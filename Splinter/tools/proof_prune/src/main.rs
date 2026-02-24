// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use std::collections::VecDeque;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

#[derive(Debug, Clone)]
enum Mode {
    Single { file: PathBuf, module: String },
    AllFiles,
}

#[derive(Debug, Clone)]
struct Config {
    mode: Mode,
    verus: String,
    entry: String,
    workdir: PathBuf,
    label: String,
    function_filters: Vec<String>,
    extra_verus_args: Vec<String>,
    jobs: usize,
    wave_size: usize,
    _global_verify_cmd: Option<String>,
    snapshot_cmd: Option<String>,
    stream_verus: bool,
}

#[derive(Debug, Clone)]
struct FunctionSpan {
    name: String,
    start_line: usize,
    end_line: usize,
}

#[derive(Debug, Clone)]
struct FileTask {
    rel_from_repo: PathBuf,
    rel_from_workdir: PathBuf,
    module: String,
}

#[derive(Debug, Clone)]
struct FileProcessResult {
    task: FileTask,
    skipped: bool,
    message: String,
}

#[derive(Debug, Default, Clone)]
struct RunStats {
    total_files: usize,
    completed_files: usize,
    durable_files: usize,
    removed: usize,
    kept: usize,
}

fn usage() -> String {
    [
        "Usage:",
        "  proof_prune --file <path> --module <module> --verus <path> [options] [-- <extra verus args>]",
        "  proof_prune --all-files --verus <path> [options] [-- <extra verus args>]",
        "",
        "Mode options:",
        "  --file <path>          Single-file mode target",
        "  --module <module>      Single-file mode module path",
        "  --all-files            Batch mode: enumerate all .rs files under --workdir",
        "",
        "Common options:",
        "  --verus <path>         Verus binary path",
        "  --entry <path>         Verus entry file (default: main.rs)",
        "  --workdir <path>       Working directory for verus (default: .)",
        "  --label <label>        Label for required asserts (default: trigger)",
        "  --function <substr>    Restrict to function names containing substring; repeatable",
        "  --stream-verus         Stream verus stdout/stderr instead of capturing",
        "",
        "Batch options:",
        "  --jobs <n>             Parallel file workers (default: 1)",
        "  --wave-size <n>        Files per wave before drain/merge/global verify (default: jobs)",
        "  --global-verify-cmd <cmd>",
        "                        Command run after each wave merge (default: '<verus> [extra] <entry>')",
        "  --snapshot-cmd <cmd>   Command run after successful wave global verify",
        "",
        "Example (single file):",
        "  proof_prune --file marshalling/KeyFormat_v.rs --module marshalling::KeyFormat_v \\",
        "    --verus ~/work/verus/source/target-verus/release/verus --entry main.rs \\",
        "    --workdir Splinter/src -- --triggers-mode silent",
        "",
        "Example (batch):",
        "  proof_prune --all-files --verus ~/work/verus/source/target-verus/release/verus \\",
        "    --workdir Splinter/src --jobs 4 --wave-size 8 \\",
        "    --global-verify-cmd '~/work/verus/source/target-verus/release/verus --triggers-mode silent main.rs' \\",
        "    --snapshot-cmd 'git commit -am \"proof_prune wave\"'",
    ]
    .join("\n")
}

fn parse_args() -> Result<Config, String> {
    let mut args: VecDeque<String> = env::args().skip(1).collect();

    let mut file: Option<PathBuf> = None;
    let mut module: Option<String> = None;
    let mut all_files = false;
    let mut verus: Option<String> = None;
    let mut entry = "main.rs".to_string();
    let mut workdir = env::current_dir().map_err(|e| format!("failed to get cwd: {e}"))?;
    let mut label = "trigger".to_string();
    let mut function_filters = Vec::new();
    let mut extra_verus_args = Vec::new();
    let mut jobs: usize = 1;
    let mut wave_size: Option<usize> = None;
    let mut global_verify_cmd: Option<String> = None;
    let mut snapshot_cmd: Option<String> = None;
    let mut stream_verus = false;

    while let Some(arg) = args.pop_front() {
        if arg == "--" {
            extra_verus_args.extend(args.into_iter());
            break;
        }

        match arg.as_str() {
            "--file" => {
                file = Some(PathBuf::from(
                    args.pop_front()
                        .ok_or_else(|| "missing value for --file".to_string())?,
                ));
            }
            "--module" => {
                module = Some(
                    args.pop_front()
                        .ok_or_else(|| "missing value for --module".to_string())?,
                );
            }
            "--all-files" => {
                all_files = true;
            }
            "--verus" => {
                verus = Some(
                    args.pop_front()
                        .ok_or_else(|| "missing value for --verus".to_string())?,
                );
            }
            "--entry" => {
                entry = args
                    .pop_front()
                    .ok_or_else(|| "missing value for --entry".to_string())?;
            }
            "--workdir" => {
                workdir = PathBuf::from(
                    args.pop_front()
                        .ok_or_else(|| "missing value for --workdir".to_string())?,
                );
            }
            "--label" => {
                label = args
                    .pop_front()
                    .ok_or_else(|| "missing value for --label".to_string())?;
            }
            "--function" => {
                function_filters.push(
                    args.pop_front()
                        .ok_or_else(|| "missing value for --function".to_string())?,
                );
            }
            "--jobs" => {
                let v = args
                    .pop_front()
                    .ok_or_else(|| "missing value for --jobs".to_string())?;
                jobs = v
                    .parse::<usize>()
                    .map_err(|e| format!("invalid --jobs value '{v}': {e}"))?;
                if jobs == 0 {
                    return Err("--jobs must be >= 1".to_string());
                }
            }
            "--wave-size" => {
                let v = args
                    .pop_front()
                    .ok_or_else(|| "missing value for --wave-size".to_string())?;
                let parsed = v
                    .parse::<usize>()
                    .map_err(|e| format!("invalid --wave-size value '{v}': {e}"))?;
                if parsed == 0 {
                    return Err("--wave-size must be >= 1".to_string());
                }
                wave_size = Some(parsed);
            }
            "--global-verify-cmd" => {
                global_verify_cmd = Some(
                    args.pop_front()
                        .ok_or_else(|| "missing value for --global-verify-cmd".to_string())?,
                );
            }
            "--snapshot-cmd" => {
                snapshot_cmd = Some(
                    args.pop_front()
                        .ok_or_else(|| "missing value for --snapshot-cmd".to_string())?,
                );
            }
            "--stream-verus" => {
                stream_verus = true;
            }
            "-h" | "--help" => {
                return Err(usage());
            }
            other => {
                return Err(format!("unknown argument: {other}\n\n{}", usage()));
            }
        }
    }

    let verus = verus.ok_or_else(|| format!("missing --verus\n\n{}", usage()))?;

    let mode = if all_files {
        if file.is_some() || module.is_some() {
            return Err("--all-files cannot be combined with --file/--module".to_string());
        }
        Mode::AllFiles
    } else {
        let file = file.ok_or_else(|| format!("missing --file\n\n{}", usage()))?;
        let module = module.ok_or_else(|| format!("missing --module\n\n{}", usage()))?;
        Mode::Single { file, module }
    };

    let wave_size = wave_size.unwrap_or(jobs);

    Ok(Config {
        mode,
        verus,
        entry,
        workdir,
        label,
        function_filters,
        extra_verus_args,
        jobs,
        wave_size,
        _global_verify_cmd: global_verify_cmd,
        snapshot_cmd,
        stream_verus,
    })
}

fn run_shell(cmd: &str, cwd: &Path) -> Result<bool, String> {
    let status = Command::new("bash")
        .arg("-lc")
        .arg(cmd)
        .current_dir(cwd)
        .status()
        .map_err(|e| format!("failed to run shell command '{cmd}': {e}"))?;
    Ok(status.success())
}

fn find_repo_root(from_dir: &Path) -> Result<PathBuf, String> {
    let output = Command::new("git")
        .arg("rev-parse")
        .arg("--show-toplevel")
        .current_dir(from_dir)
        .output()
        .map_err(|e| format!("failed to run git rev-parse: {e}"))?;

    if !output.status.success() {
        return Err(format!(
            "git rev-parse failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }

    Ok(PathBuf::from(
        String::from_utf8_lossy(&output.stdout).trim().to_string(),
    ))
}

fn strip_line_comment(line: &str) -> &str {
    match line.find("//") {
        Some(i) => &line[..i],
        None => line,
    }
}

fn is_ident_char(c: char) -> bool {
    c == '_' || c.is_ascii_alphanumeric()
}

fn find_fn_name(line: &str) -> Option<String> {
    let s = strip_line_comment(line);
    let bytes = s.as_bytes();

    let mut i = 0;
    while i + 1 < bytes.len() {
        if bytes[i] == b'f' && bytes[i + 1] == b'n' {
            let prev_ok = if i == 0 {
                true
            } else {
                !is_ident_char(s[..i].chars().next_back().unwrap_or(' '))
            };
            let after = s[i + 2..].chars().next().unwrap_or(' ');
            if prev_ok && after.is_whitespace() {
                let mut j = i + 2;
                while j < bytes.len() && s.as_bytes()[j].is_ascii_whitespace() {
                    j += 1;
                }
                let mut k = j;
                while k < bytes.len() {
                    let ch = s[k..].chars().next().unwrap();
                    if !is_ident_char(ch) {
                        break;
                    }
                    k += ch.len_utf8();
                }
                if k > j {
                    return Some(s[j..k].to_string());
                }
            }
        }
        i += 1;
    }

    None
}

fn find_header_delim(lines: &[String], start_line: usize) -> Option<(char, usize, usize)> {
    for (li, line) in lines.iter().enumerate().skip(start_line) {
        let s = strip_line_comment(line);
        for (ci, ch) in s.char_indices() {
            if ch == '{' || ch == ';' {
                return Some((ch, li, ci));
            }
        }
    }
    None
}

fn find_fn_end(lines: &[String], brace_line: usize, brace_col: usize) -> Option<usize> {
    let mut depth = 0isize;

    for (li, line) in lines.iter().enumerate().skip(brace_line) {
        let s = strip_line_comment(line);
        for (ci, ch) in s.char_indices() {
            if li == brace_line && ci < brace_col {
                continue;
            }
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(li);
                    }
                }
                _ => {}
            }
        }
    }

    None
}

fn discover_functions(lines: &[String]) -> Vec<FunctionSpan> {
    let mut out = Vec::new();
    let mut i = 0usize;

    while i < lines.len() {
        let line = &lines[i];
        let trimmed = line.trim_start();
        if trimmed.starts_with("//") {
            i += 1;
            continue;
        }

        if let Some(name) = find_fn_name(line) {
            let Some((delim, delim_line, delim_col)) = find_header_delim(lines, i) else {
                i += 1;
                continue;
            };

            if delim == ';' {
                i = delim_line + 1;
                continue;
            }

            if let Some(end_line) = find_fn_end(lines, delim_line, delim_col) {
                out.push(FunctionSpan {
                    name,
                    start_line: i,
                    end_line,
                });
                i = end_line + 1;
                continue;
            }
        }

        i += 1;
    }

    out
}

fn comment_has_label(comment_text: &str) -> bool {
    let lower = comment_text.to_ascii_lowercase();
    lower.contains("trigger") || lower.contains("witness") || lower.contains("keep")
}

fn line_has_label(line: &str) -> bool {
    if let Some(i) = line.find("//") {
        return comment_has_label(&line[i + 2..]);
    }
    false
}

fn previous_comment_has_label(lines: &[String], fn_start: usize, line_idx: usize) -> bool {
    if line_idx == 0 || line_idx <= fn_start {
        return false;
    }

    let mut i = line_idx - 1;
    loop {
        let t = lines[i].trim();
        if t.is_empty() {
            if i == 0 || i <= fn_start {
                return false;
            }
            i -= 1;
            continue;
        }

        if t.starts_with("//") {
            return comment_has_label(t.trim_start_matches('/').trim());
        }

        return false;
    }
}

fn is_assert_candidate(lines: &[String], f: &FunctionSpan, idx: usize) -> bool {
    if idx >= lines.len() {
        return false;
    }
    if idx < f.start_line || idx > f.end_line {
        return false;
    }

    let t = lines[idx].trim_start();
    if !t.starts_with("assert(") {
        return false;
    }
    if !t.contains(';') {
        return false;
    }
    if t.starts_with("assert forall") || t.starts_with("assert exists") {
        return false;
    }
    if line_has_label(&lines[idx]) {
        return false;
    }
    if previous_comment_has_label(lines, f.start_line, idx) {
        return false;
    }

    true
}

fn find_candidates(lines: &[String], f: &FunctionSpan) -> Vec<usize> {
    let mut out = Vec::new();
    if lines.is_empty() || f.start_line >= lines.len() {
        return out;
    }
    let end = f.end_line.min(lines.len() - 1);
    for idx in f.start_line..=end {
        if is_assert_candidate(lines, f, idx) {
            out.push(idx);
        }
    }
    out
}

fn add_label_to_assert_line(line: &str, label: &str) -> String {
    if line_has_label(line) {
        return line.to_string();
    }

    if line.ends_with('\n') {
        let mut s = line.trim_end_matches('\n').to_string();
        s.push_str(" // ");
        s.push_str(label);
        s.push('\n');
        s
    } else {
        format!("{} // {}", line, label)
    }
}

fn write_lines(path: &Path, lines: &[String]) -> Result<(), String> {
    let text: String = lines.concat();
    fs::write(path, text).map_err(|e| format!("failed to write {}: {e}", path.display()))
}

fn run_verify_function(
    verus: &str,
    workdir: &Path,
    entry: &str,
    module: &str,
    fn_name: &str,
    extra_verus_args: &[String],
    stream: bool,
) -> Result<(bool, String), String> {
    fn run_once(
        verus: &str,
        workdir: &Path,
        entry: &str,
        module: &str,
        fn_name: &str,
        extra_verus_args: &[String],
        stream: bool,
    ) -> Result<(bool, String, String), String> {
        let selector = format!("*{}*", fn_name);

        let mut cmd = Command::new(verus);
        cmd.current_dir(workdir);

        for a in extra_verus_args {
            cmd.arg(a);
        }

        cmd.arg("--verify-only-module")
            .arg(module)
            .arg("--verify-function")
            .arg(&selector)
            .arg(entry);

        let output = cmd
            .output()
            .map_err(|e| format!("failed to run verus for {fn_name}: {e}"))?;

        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();

        if stream {
            if !stdout.is_empty() {
                print!("{stdout}");
            }
            if !stderr.is_empty() {
                eprint!("{stderr}");
            }
        }

        Ok((output.status.success(), stdout, stderr))
    }

    fn parse_child_modules(stderr: &str, module: &str) -> Vec<String> {
        let needle = "could not find module";
        if !stderr.contains(needle) {
            return Vec::new();
        }
        let prefix = format!("{module}::");
        let mut out = Vec::new();
        for line in stderr.lines() {
            let t = line.trim_start();
            if let Some(rest) = t.strip_prefix("- ") {
                let m = rest.trim();
                if m.starts_with(&prefix) {
                    out.push(m.to_string());
                }
            }
        }
        out.sort();
        out.dedup();
        out
    }

    let selector = format!("*{}*", fn_name);
    let _ = selector; // keep local behavior explicit and avoid accidental API drift

    let (ok, _stdout, stderr) = run_once(
        verus,
        workdir,
        entry,
        module,
        fn_name,
        extra_verus_args,
        stream,
    )?;
    if ok {
        return Ok((true, module.to_string()));
    }

    let children = parse_child_modules(&stderr, module);
    if children.is_empty() {
        return Ok((false, module.to_string()));
    }

    for child in children {
        let (ok_child, _out_child, _err_child) = run_once(
            verus,
            workdir,
            entry,
            &child,
            fn_name,
            extra_verus_args,
            stream,
        )?;
        if ok_child {
            return Ok((true, child));
        }
    }

    Ok((false, module.to_string()))
}

fn process_one_file(
    abs_file: &Path,
    display_file: &str,
    module: &str,
    verus: &str,
    workdir: &Path,
    entry: &str,
    label: &str,
    function_filters: &[String],
    extra_verus_args: &[String],
    stream_verus: bool,
    worker_id: usize,
) -> Result<(bool, usize, usize, usize, usize, String), String> {
    let original = fs::read_to_string(abs_file)
        .map_err(|e| format!("failed to read {}: {e}", abs_file.display()))?;

    let mut lines: Vec<String> = original
        .split_inclusive('\n')
        .map(|s| s.to_string())
        .collect();
    if !original.ends_with('\n') {
        lines.push("\n".to_string());
    }

    let functions = discover_functions(&lines);
    if functions.is_empty() {
        return Ok((
            false,
            0,
            0,
            0,
            0,
            "no functions discovered".to_string(),
        ));
    }

    let mut total_removed = 0usize;
    let mut total_kept = 0usize;
    let mut total_unlabeled = 0usize;
    let mut total_candidate_fns = 0usize;
    let mut any_change = false;
    let mut module_for_verify = module.to_string();

    // Process bottom-up so line deletions in one function never invalidate spans
    // for functions that remain to be processed.
    for f in functions.into_iter().rev() {
        if !function_filters.is_empty()
            && !function_filters.iter().any(|needle| f.name.contains(needle))
        {
            continue;
        }

        let candidates = find_candidates(&lines, &f);
        if candidates.is_empty() {
            continue;
        }
        total_unlabeled += candidates.len();
        total_candidate_fns += 1;

        println!(
            "[{}] running control for {}:{}",
            worker_id, display_file, f.name
        );
        let (ok_control, resolved) = run_verify_function(
            verus,
            workdir,
            entry,
            &module_for_verify,
            &f.name,
            extra_verus_args,
            stream_verus,
        )?;
        module_for_verify = resolved;
        if !ok_control {
            continue;
        }

        println!(
            "[{}] found {} assert candidate(s) for {}:{}",
            worker_id,
            candidates.len(),
            display_file,
            f.name
        );
        let total_candidates = candidates.len();

        for (k, idx) in candidates.into_iter().rev().enumerate() {
            if idx >= lines.len() {
                continue;
            }

            let original_line = lines[idx].clone();
            println!(
                "[{}] trying assert {}/{} for {}:{} (line {})",
                worker_id,
                k + 1,
                total_candidates,
                display_file,
                f.name,
                idx + 1
            );
            println!(
                "[{}] deleting assert {}/{} for {}:{}",
                worker_id,
                k + 1,
                total_candidates,
                display_file,
                f.name
            );
            lines.remove(idx);
            write_lines(abs_file, &lines)?;

            let (keep_removed, resolved) = run_verify_function(
                verus,
                workdir,
                entry,
                &module_for_verify,
                &f.name,
                extra_verus_args,
                stream_verus,
            )?;
            module_for_verify = resolved;

            if keep_removed {
                total_removed += 1;
                any_change = true;
                println!(
                    "[{}] assert {}/{} removed for {}:{}",
                    worker_id,
                    k + 1,
                    total_candidates,
                    display_file,
                    f.name
                );
            } else {
                let relabeled = add_label_to_assert_line(&original_line, label);
                lines.insert(idx, relabeled);
                write_lines(abs_file, &lines)?;
                total_kept += 1;
                any_change = true;
                println!(
                    "[{}] marking assert {}/{} as {} for {}:{}",
                    worker_id,
                    k + 1,
                    total_candidates,
                    label,
                    display_file,
                    f.name
                );
            }
            let remaining = total_candidates - (k + 1);
            println!(
                "[{}] progress for {}:{}: {}/{} done, {} to go (fn removed={}, fn kept={})",
                worker_id,
                display_file,
                f.name,
                k + 1,
                total_candidates,
                remaining,
                total_removed,
                total_kept
            );
        }

        println!(
            "[{}] post-check for {}:{}",
            worker_id, display_file, f.name
        );
        let (ok, resolved) = run_verify_function(
            verus,
            workdir,
            entry,
            &module_for_verify,
            &f.name,
            extra_verus_args,
            stream_verus,
        )?;
        module_for_verify = resolved;
        if !ok {
            return Err(format!("function {} failed post-check", f.name));
        }
    }

    write_lines(abs_file, &lines)?;
    let message = format!("removed {total_removed}, kept+labelled {total_kept}");
    Ok((
        any_change,
        total_removed,
        total_kept,
        total_unlabeled,
        total_candidate_fns,
        message,
    ))
}

fn derive_module_from_rel(rel_from_workdir: &Path) -> Option<String> {
    if rel_from_workdir.extension().and_then(|e| e.to_str()) != Some("rs") {
        return None;
    }

    let mut comps: Vec<String> = rel_from_workdir
        .components()
        .filter_map(|c| c.as_os_str().to_str().map(|s| s.to_string()))
        .collect();

    if comps.is_empty() {
        return None;
    }

    let last = comps.last()?.clone();
    if last == "mod.rs" {
        comps.pop();
    } else if let Some(stripped) = last.strip_suffix(".rs") {
        *comps.last_mut().unwrap() = stripped.to_string();
    } else {
        return None;
    }

    if comps.is_empty() {
        return None;
    }

    Some(comps.join("::"))
}

fn walk_rs_files(root: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries = fs::read_dir(root)
        .map_err(|e| format!("failed to read dir {}: {e}", root.display()))?;

    for entry in entries {
        let entry = entry.map_err(|e| format!("failed to read dir entry: {e}"))?;
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();

        if path.is_dir() {
            if name == "target" || name == ".git" {
                continue;
            }
            walk_rs_files(&path, out)?;
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
            out.push(path);
        }
    }

    Ok(())
}

fn run_single(cfg: &Config) -> Result<(), String> {
    let (file, module) = match &cfg.mode {
        Mode::Single { file, module } => (file, module),
        Mode::AllFiles => return Err("internal mode error".to_string()),
    };

    let changed = process_one_file(
        file,
        &file.display().to_string(),
        module,
        &cfg.verus,
        &cfg.workdir,
        &cfg.entry,
        &cfg.label,
        &cfg.function_filters,
        &cfg.extra_verus_args,
        cfg.stream_verus,
        0,
    )?;

    println!("done: {}", changed.5);
    Ok(())
}

fn create_worker_worktree(repo_root: &Path, worker_id: usize) -> Result<PathBuf, String> {
    let mut last_err = String::new();
    for attempt in 0..5 {
        let dir = PathBuf::from(format!(
            "/tmp/proof_prune_worker_{}_{}_{}",
            std::process::id(),
            worker_id,
            attempt
        ));

        if dir.exists() {
            let _ = fs::remove_dir_all(&dir);
        }

        let output = Command::new("git")
            .current_dir(repo_root)
            .arg("worktree")
            .arg("add")
            .arg("--detach")
            .arg(&dir)
            .arg("HEAD")
            .output()
            .map_err(|e| format!("failed to create worktree {}: {e}", dir.display()))?;

        if output.status.success() {
            return Ok(dir);
        }

        last_err = format!(
            "git worktree add failed for {} (attempt {}): {}",
            dir.display(),
            attempt + 1,
            String::from_utf8_lossy(&output.stderr).trim()
        );
        thread::sleep(Duration::from_millis(200));
    }

    Err(last_err)
}

fn remove_worker_worktree(repo_root: &Path, dir: &Path) {
    let _ = Command::new("git")
        .current_dir(repo_root)
        .arg("worktree")
        .arg("remove")
        .arg("--force")
        .arg(dir)
        .status();

    let _ = fs::remove_dir_all(dir);
}

fn run_batch(cfg: &Config) -> Result<(), String> {
    let repo_root = find_repo_root(&cfg.workdir)?;
    let workdir_abs = fs::canonicalize(&cfg.workdir)
        .map_err(|e| format!("failed to canonicalize workdir {}: {e}", cfg.workdir.display()))?;
    let workdir_rel_from_repo = workdir_abs
        .strip_prefix(&repo_root)
        .map_err(|_| {
            format!(
                "workdir {} is not inside git repo root {}",
                workdir_abs.display(),
                repo_root.display()
            )
        })?
        .to_path_buf();

    let mut files = Vec::new();
    walk_rs_files(&workdir_abs, &mut files)?;
    files.sort();

    let entry_abs = workdir_abs.join(&cfg.entry);

    let mut tasks = Vec::new();
    for abs in files {
        if abs == entry_abs {
            continue;
        }

        let rel_from_workdir = abs
            .strip_prefix(&workdir_abs)
            .map_err(|_| format!("path {} not under workdir", abs.display()))?
            .to_path_buf();

        let Some(module) = derive_module_from_rel(&rel_from_workdir) else {
            continue;
        };

        let rel_from_repo = abs
            .strip_prefix(&repo_root)
            .map_err(|_| format!("path {} not under repo root", abs.display()))?
            .to_path_buf();

        tasks.push(FileTask {
            rel_from_repo,
            rel_from_workdir,
            module,
        });
    }

    if tasks.is_empty() {
        println!("no tasks found");
        return Ok(());
    }

    println!(
        "discovered {} file tasks under {}",
        tasks.len(),
        workdir_abs.display()
    );

    let stats = Arc::new(Mutex::new(RunStats {
        total_files: tasks.len(),
        ..RunStats::default()
    }));
    let heartbeat_stop = Arc::new(AtomicBool::new(false));
    let hb_stats = Arc::clone(&stats);
    let hb_stop = Arc::clone(&heartbeat_stop);
    let heartbeat = thread::spawn(move || {
        while !hb_stop.load(Ordering::Relaxed) {
            thread::sleep(Duration::from_secs(30));
            if hb_stop.load(Ordering::Relaxed) {
                break;
            }
            let s = hb_stats.lock().unwrap().clone();
            let remaining = s.total_files.saturating_sub(s.completed_files);
            println!(
                "[heartbeat] completed {}/{} files, {} to go; durable files={}, removed={}, kept+labelled={}",
                s.completed_files, s.total_files, remaining, s.durable_files, s.removed, s.kept
            );
        }
    });

    let mut wave_num = 0usize;
    let mut total_removed = 0usize;
    let mut total_kept = 0usize;
    let mut cursor = 0usize;

    while cursor < tasks.len() {
        wave_num += 1;
        let end = (cursor + cfg.wave_size).min(tasks.len());
        let wave_tasks = tasks[cursor..end].to_vec();
        let expected_wave_claims = wave_tasks.len();
        cursor = end;

        println!(
            "\\n=== wave {}: {} file(s), jobs={} ===",
            wave_num,
            wave_tasks.len(),
            cfg.jobs
        );

        let queue = Arc::new(Mutex::new(VecDeque::from(wave_tasks)));
        let results: Arc<Mutex<Vec<FileProcessResult>>> = Arc::new(Mutex::new(Vec::new()));
        let errors: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
        let merge_lock: Arc<Mutex<()>> = Arc::new(Mutex::new(()));
        let wave_claimed = Arc::new(AtomicUsize::new(0));

        let mut handles = Vec::new();
        for worker_id in 0..cfg.jobs {
            let queue = Arc::clone(&queue);
            let results = Arc::clone(&results);
            let errors = Arc::clone(&errors);
            let stats = Arc::clone(&stats);
            let merge_lock = Arc::clone(&merge_lock);
            let wave_claimed = Arc::clone(&wave_claimed);
            let repo_root = repo_root.clone();
            let cfg = cfg.clone();
            let workdir_rel_from_repo = workdir_rel_from_repo.clone();

            let h = thread::spawn(move || {
                let worktree = match create_worker_worktree(&repo_root, worker_id) {
                    Ok(p) => p,
                    Err(e) => {
                        errors.lock().unwrap().push(e);
                        return;
                    }
                };

                let worker_workdir = worktree.join(&workdir_rel_from_repo);

                let mut thread_removed = 0usize;
                let mut thread_unlabeled = 0usize;
                let mut thread_fns = 0usize;
                let mut thread_claimed = 0usize;

                loop {
                    let (task, remaining) = {
                        let mut q = queue.lock().unwrap();
                        let t = q.pop_front();
                        let rem = q.len();
                        (t, rem)
                    };

                    let Some(task) = task else { break; };
                    thread_claimed += 1;
                    let global_claim = wave_claimed.fetch_add(1, Ordering::Relaxed) + 1;

                    let worker_file = worktree.join(&task.rel_from_repo);
                    println!(
                        "[{}] Thread {} starts, owns {} ({})",
                        worker_id,
                        worker_id,
                        task.rel_from_workdir.display(),
                        task.module
                    );
                    println!(
                        "[{}] claimed file {} in wave; queue remaining {}",
                        worker_id, global_claim, remaining
                    );

                    let processed = process_one_file(
                        &worker_file,
                        &task.rel_from_workdir.display().to_string(),
                        &task.module,
                        &cfg.verus,
                        &worker_workdir,
                        &cfg.entry,
                        &cfg.label,
                        &cfg.function_filters,
                        &cfg.extra_verus_args,
                        cfg.stream_verus,
                        worker_id,
                    );

                    match processed {
                        Ok((changed, removed, kept, unlabeled, fns, msg)) => {
                            thread_removed += removed;
                            thread_unlabeled += unlabeled;
                            thread_fns += fns;
                            let content = if changed {
                                match fs::read_to_string(&worker_file) {
                                    Ok(s) => Some(s),
                                    Err(e) => {
                                        errors.lock().unwrap().push(format!(
                                            "failed reading worker output {}: {e}",
                                            worker_file.display()
                                        ));
                                        None
                                    }
                                }
                            } else {
                                None
                            };

                            if changed {
                                if let Some(c) = &content {
                                    let _g = merge_lock.lock().unwrap();
                                    let main_path = repo_root.join(&task.rel_from_repo);
                                    if let Err(e) = fs::write(&main_path, c) {
                                        errors.lock().unwrap().push(format!(
                                            "failed to durable-merge {}: {e}",
                                            main_path.display()
                                        ));
                                    } else {
                                        let mut s = stats.lock().unwrap();
                                        s.durable_files += 1;
                                        s.removed += removed;
                                        s.kept += kept;
                                        println!(
                                            "[{}] durable merge complete for {} (removed {}, kept {})",
                                            worker_id,
                                            task.rel_from_workdir.display(),
                                            removed,
                                            kept
                                        );
                                    }
                                }
                            }

                            {
                                let mut s = stats.lock().unwrap();
                                s.completed_files += 1;
                            }

                            let result = FileProcessResult {
                                task,
                                skipped: false,
                                message: msg,
                            };
                            results.lock().unwrap().push(result);
                        }
                        Err(e) => {
                            {
                                let mut s = stats.lock().unwrap();
                                s.completed_files += 1;
                            }
                            let result = FileProcessResult {
                                task,
                                skipped: true,
                                message: format!("error: {e}"),
                            };
                            results.lock().unwrap().push(result);
                        }
                    }
                }

                println!(
                    "[{}] claimed {} files; removed {} asserts from {} unlabeled asserts across {} fns",
                    worker_id, thread_claimed, thread_removed, thread_unlabeled, thread_fns
                );
                remove_worker_worktree(&repo_root, &worktree);
            });
            handles.push(h);
        }

        for h in handles {
            let _ = h.join();
        }

        let observed_claims = wave_claimed.load(Ordering::Relaxed);
        println!(
            "[wave {}] claim accounting: observed={}, expected={}",
            wave_num, observed_claims, expected_wave_claims
        );
        if observed_claims != expected_wave_claims {
            heartbeat_stop.store(true, Ordering::Relaxed);
            let _ = heartbeat.join();
            return Err(format!(
                "wave {} claim mismatch: observed {} != expected {}",
                wave_num, observed_claims, expected_wave_claims
            ));
        }

        if !errors.lock().unwrap().is_empty() {
            let msgs = errors.lock().unwrap().clone();
            heartbeat_stop.store(true, Ordering::Relaxed);
            let _ = heartbeat.join();
            return Err(format!("worker setup/runtime errors:\n{}", msgs.join("\n")));
        }

        let mut wave_results = results.lock().unwrap().clone();
        wave_results.sort_by_key(|r| r.task.rel_from_repo.clone());

        for r in &wave_results {
            if r.skipped {
                println!(
                    "[skip] {}: {}",
                    r.task.rel_from_workdir.display(),
                    r.message
                );
                continue;
            }
            println!(
                "[done] {}: {}",
                r.task.rel_from_workdir.display(),
                r.message
            );
        }

        {
            let s = stats.lock().unwrap().clone();
            total_removed = s.removed;
            total_kept = s.kept;
        }

        println!(
            "[wave {}] drained; durable merges already applied (global verify disabled)",
            wave_num
        );

        if let Some(cmd) = &cfg.snapshot_cmd {
            println!("[wave {}] running snapshot command", wave_num);
            let ok = run_shell(cmd, &repo_root)?;
            if !ok {
                heartbeat_stop.store(true, Ordering::Relaxed);
                let _ = heartbeat.join();
                return Err(format!("snapshot command failed after wave {}: {}", wave_num, cmd));
            }
        }

        println!("[wave {}] complete", wave_num);
    }

    println!(
        "\\nall waves complete: removed {}, kept+labelled {}",
        total_removed, total_kept
    );
    heartbeat_stop.store(true, Ordering::Relaxed);
    let _ = heartbeat.join();
    Ok(())
}


fn main() {
    let cfg = match parse_args() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(2);
        }
    };

    let result = match cfg.mode {
        Mode::Single { .. } => run_single(&cfg),
        Mode::AllFiles => run_batch(&cfg),
    };

    if let Err(e) = result {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}
