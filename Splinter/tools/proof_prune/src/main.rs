// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use std::collections::VecDeque;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Debug, Clone)]
struct Config {
    file: PathBuf,
    module: String,
    verus: String,
    entry: String,
    workdir: PathBuf,
    label: String,
    function_filters: Vec<String>,
    extra_verus_args: Vec<String>,
}

#[derive(Debug, Clone)]
struct FunctionSpan {
    name: String,
    start_line: usize,
    end_line: usize,
}

fn usage() -> String {
    [
        "Usage:",
        "  proof_prune --file <path> --module <module> --verus <path> [options] [-- <extra verus args>]",
        "",
        "Options:",
        "  --entry <path>         Verus entry file (default: main.rs)",
        "  --workdir <path>       Working directory for verus invocations (default: .)",
        "  --label <label>        Label to append to needed asserts (default: trigger)",
        "  --function <substr>    Restrict to function names containing this substring; repeatable",
        "",
        "Example:",
        "  proof_prune \\",
        "    --file marshalling/ResizableUniformSizedSeq_v.rs \\",
        "    --module marshalling::ResizableUniformSizedSeq_v \\",
        "    --verus ~/work/verus/source/target-verus/release/verus \\",
        "    --entry main.rs \\",
        "    --workdir ../../src \\",
        "    -- --triggers-mode silent --multiple-errors 2",
    ]
    .join("\n")
}

fn parse_args() -> Result<Config, String> {
    let mut args: VecDeque<String> = env::args().skip(1).collect();

    let mut file: Option<PathBuf> = None;
    let mut module: Option<String> = None;
    let mut verus: Option<String> = None;
    let mut entry = "main.rs".to_string();
    let mut workdir = env::current_dir().map_err(|e| format!("failed to get cwd: {e}"))?;
    let mut label = "trigger".to_string();
    let mut function_filters = Vec::new();
    let mut extra_verus_args = Vec::new();

    while let Some(arg) = args.pop_front() {
        if arg == "--" {
            extra_verus_args.extend(args.into_iter());
            break;
        }

        match arg.as_str() {
            "--file" => {
                let v = args
                    .pop_front()
                    .ok_or_else(|| "missing value for --file".to_string())?;
                file = Some(PathBuf::from(v));
            }
            "--module" => {
                let v = args
                    .pop_front()
                    .ok_or_else(|| "missing value for --module".to_string())?;
                module = Some(v);
            }
            "--verus" => {
                let v = args
                    .pop_front()
                    .ok_or_else(|| "missing value for --verus".to_string())?;
                verus = Some(v);
            }
            "--entry" => {
                entry = args
                    .pop_front()
                    .ok_or_else(|| "missing value for --entry".to_string())?;
            }
            "--workdir" => {
                let v = args
                    .pop_front()
                    .ok_or_else(|| "missing value for --workdir".to_string())?;
                workdir = PathBuf::from(v);
            }
            "--label" => {
                label = args
                    .pop_front()
                    .ok_or_else(|| "missing value for --label".to_string())?;
            }
            "--function" => {
                let v = args
                    .pop_front()
                    .ok_or_else(|| "missing value for --function".to_string())?;
                function_filters.push(v);
            }
            "-h" | "--help" => {
                return Err(usage());
            }
            other => {
                return Err(format!("unknown argument: {other}\n\n{}", usage()));
            }
        }
    }

    let file = file.ok_or_else(|| format!("missing --file\n\n{}", usage()))?;
    let module = module.ok_or_else(|| format!("missing --module\n\n{}", usage()))?;
    let verus = verus.ok_or_else(|| format!("missing --verus\n\n{}", usage()))?;

    Ok(Config {
        file,
        module,
        verus,
        entry,
        workdir,
        label,
        function_filters,
        extra_verus_args,
    })
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
    for idx in f.start_line..=f.end_line {
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

    if let Some(comment_idx) = line.find("//") {
        let (before, comment) = line.split_at(comment_idx);
        if before.trim_end().is_empty() {
            return line.to_string();
        }
        format!("{}{} {}\n", before.trim_end(), comment, label)
    } else {
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
}

fn write_lines(path: &Path, lines: &[String]) -> Result<(), String> {
    let text: String = lines.concat();
    fs::write(path, text).map_err(|e| format!("failed to write {}: {e}", path.display()))
}

fn run_verify_function(cfg: &Config, fn_name: &str) -> Result<bool, String> {
    let selector = format!("*{}*", fn_name);

    let mut cmd = Command::new(&cfg.verus);
    cmd.current_dir(&cfg.workdir);

    for a in &cfg.extra_verus_args {
        cmd.arg(a);
    }

    cmd.arg("--verify-only-module")
        .arg(&cfg.module)
        .arg("--verify-function")
        .arg(&selector)
        .arg(&cfg.entry);

    let output = cmd
        .output()
        .map_err(|e| format!("failed to run verus for {fn_name}: {e}"))?;

    if output.status.success() {
        Ok(true)
    } else {
        Ok(false)
    }
}

fn main() {
    let cfg = match parse_args() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(2);
        }
    };

    let original = match fs::read_to_string(&cfg.file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("failed to read {}: {e}", cfg.file.display());
            std::process::exit(1);
        }
    };

    let mut lines: Vec<String> = original
        .split_inclusive('\n')
        .map(|s| s.to_string())
        .collect();
    if !original.ends_with('\n') {
        lines.push("\n".to_string());
    }

    let functions = discover_functions(&lines);
    if functions.is_empty() {
        eprintln!("no functions discovered in {}", cfg.file.display());
        std::process::exit(1);
    }

    let mut total_removed = 0usize;
    let mut total_kept = 0usize;

    for f in functions {
        if !cfg.function_filters.is_empty()
            && !cfg
                .function_filters
                .iter()
                .any(|needle| f.name.contains(needle))
        {
            continue;
        }

        match run_verify_function(&cfg, &f.name) {
            Ok(true) => {}
            Ok(false) => {
                eprintln!("[skip] {}: control verify failed", f.name);
                continue;
            }
            Err(e) => {
                eprintln!("[skip] {}: {e}", f.name);
                continue;
            }
        }

        let candidates = find_candidates(&lines, &f);
        if candidates.is_empty() {
            continue;
        }

        println!("[{}] candidates: {}", f.name, candidates.len());

        for idx in candidates.into_iter().rev() {
            if idx >= lines.len() {
                continue;
            }

            let original_line = lines[idx].clone();
            lines.remove(idx);

            if let Err(e) = write_lines(&cfg.file, &lines) {
                eprintln!("write failed while pruning {}:{}: {e}", f.name, idx + 1);
                std::process::exit(1);
            }

            let keep_removed = match run_verify_function(&cfg, &f.name) {
                Ok(v) => v,
                Err(e) => {
                    eprintln!("verify failed while pruning {}:{}: {e}", f.name, idx + 1);
                    std::process::exit(1);
                }
            };

            if keep_removed {
                total_removed += 1;
                println!("  - removed line {}", idx + 1);
            } else {
                let relabeled = add_label_to_assert_line(&original_line, &cfg.label);
                lines.insert(idx, relabeled);
                if let Err(e) = write_lines(&cfg.file, &lines) {
                    eprintln!("write failed while restoring {}:{}: {e}", f.name, idx + 1);
                    std::process::exit(1);
                }
                total_kept += 1;
                println!("  - kept+labelled line {}", idx + 1);
            }
        }

        match run_verify_function(&cfg, &f.name) {
            Ok(true) => {}
            Ok(false) => {
                eprintln!("function {} does not verify after pruning", f.name);
                std::process::exit(1);
            }
            Err(e) => {
                eprintln!("post-check failed for {}: {e}", f.name);
                std::process::exit(1);
            }
        }
    }

    if let Err(e) = write_lines(&cfg.file, &lines) {
        eprintln!("failed final write {}: {e}", cfg.file.display());
        std::process::exit(1);
    }

    println!("done: removed {total_removed}, kept+labelled {total_kept}");
}
