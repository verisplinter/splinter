#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path


def is_executable(path: Path) -> bool:
    return path.is_file() and os.access(path, os.X_OK)


def run(cmd: list[str], *, cwd: Path | None = None, env: dict[str, str] | None = None) -> None:
    pretty = " ".join(cmd)
    print(f"+ {pretty}")
    subprocess.run(cmd, cwd=str(cwd) if cwd else None, env=env, check=True)


def run_bash(cmd: str, *, cwd: Path | None = None, env: dict[str, str] | None = None) -> None:
    print(f"+ bash -lc {cmd}")
    subprocess.run(["bash", "-lc", cmd], cwd=str(cwd) if cwd else None, env=env, check=True)


def load_ci_config(repo_root: Path) -> dict[str, str]:
    config_path = repo_root / "verus-version.toml"
    with config_path.open("rb") as f:
        c = tomllib.load(f)
    required = ("verus_repo", "verus_commit", "rust_toolchain")
    for key in required:
        if key not in c:
            raise RuntimeError(f"Missing key {key} in {config_path}")
    return {k: str(c[k]) for k in required}


def verus_build_is_usable(
    verus_checkout: Path, verus_commit: str
) -> tuple[bool, Path, Path, Path]:
    marker = verus_checkout / ".splinter_ci_verus_commit"
    verus_bin = verus_checkout / "source" / "target-verus" / "release" / "verus"
    cargo_verus_bin = verus_checkout / "source" / "target-verus" / "release" / "cargo-verus"
    z3_bin = verus_checkout / "source" / "z3"
    if not marker.is_file():
        return False, marker, verus_bin, cargo_verus_bin
    if marker.read_text().strip() != verus_commit:
        return False, marker, verus_bin, cargo_verus_bin
    if not is_executable(verus_bin):
        return False, marker, verus_bin, cargo_verus_bin
    if not is_executable(cargo_verus_bin):
        return False, marker, verus_bin, cargo_verus_bin
    if not is_executable(z3_bin):
        return False, marker, verus_bin, cargo_verus_bin
    return True, marker, verus_bin, cargo_verus_bin


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run local equivalent of .github/workflows/verify.yml verify job."
    )
    parser.add_argument(
        "--phase",
        choices=["all", "verify-build", "scripted-test"],
        default="all",
        help="Which CI phase to run (default: all).",
    )
    parser.add_argument(
        "--fresh-verus",
        action="store_true",
        help="Delete and rebuild ./_verus from scratch (default is reuse).",
    )
    args = parser.parse_args()

    script_path = Path(__file__).resolve()
    # Script lives at <repo>/Splinter/tools/ci.py
    repo_root = script_path.parents[2]
    splinter_dir = repo_root / "Splinter"
    verus_checkout = repo_root / "_verus"

    cfg = load_ci_config(repo_root)
    verus_repo = cfg["verus_repo"]
    verus_commit = cfg["verus_commit"]
    rust_toolchain = cfg["rust_toolchain"]

    env = os.environ.copy()
    env["RUSTUP_TOOLCHAIN"] = rust_toolchain

    do_verify_build = args.phase in ("all", "verify-build")
    do_scripted_test = args.phase in ("all", "scripted-test")

    if do_verify_build:
        print("== local CI config ==")
        print(f"verus_repo:     {verus_repo}")
        print(f"verus_commit:   {verus_commit}")
        print(f"rust_toolchain: {rust_toolchain}")

        print("== rust toolchain ==")
        run(["rustup", "toolchain", "install", rust_toolchain])
        run(["rustup", "component", "add", "--toolchain", rust_toolchain, "rust-src"])
        run(["rustup", "component", "add", "--toolchain", rust_toolchain, "rustc-dev"])
        run(["rustup", "component", "add", "--toolchain", rust_toolchain, "llvm-tools-preview"])

        if args.fresh_verus and verus_checkout.exists():
            print("== reset _verus ==")
            shutil.rmtree(verus_checkout)

        cache_hit, marker, verus_bin, cargo_verus = verus_build_is_usable(verus_checkout, verus_commit)
        if cache_hit:
            print("== verus cache hit: using prebuilt pinned toolchain ==")
        else:
            if not (verus_checkout / ".git").exists():
                print("== clone verus ==")
                run(["git", "clone", verus_repo, str(verus_checkout)])

            print("== checkout pinned verus commit ==")
            run(["git", "-C", str(verus_checkout), "fetch", "--all", "--tags"])
            run(["git", "-C", str(verus_checkout), "checkout", verus_commit])

            print("== build verus ==")
            z3_bin = verus_checkout / "source" / "z3"
            if is_executable(z3_bin):
                print("== z3 cache hit: using existing _verus/source/z3 ==")
            else:
                print("== z3 cache miss: fetching z3 ==")
                run_bash("cd source && bash tools/get-z3.sh", cwd=verus_checkout, env=env)
            run_bash(
                "source tools/activate && cd source && vargo build --release",
                cwd=verus_checkout,
                env=env,
            )
            marker.parent.mkdir(parents=True, exist_ok=True)
            marker.write_text(f"{verus_commit}\n")

            cache_hit, _, verus_bin, cargo_verus = verus_build_is_usable(verus_checkout, verus_commit)
            if not cache_hit:
                raise RuntimeError("Verus build completed but cache marker/artifacts are unusable")

        cargo_verus_dir = cargo_verus.parent
        env2 = env.copy()
        env2["PATH"] = f"{cargo_verus_dir}:{env2.get('PATH', '')}"

        print("== verify splinter ==")
        run(
            [
                str(verus_bin),
                "src/main.rs",
                "--expand-errors",
                "--multiple-errors",
                "5",
            ],
            cwd=splinter_dir,
            env=env,
        )

        print("== cargo verus build ==")
        run(["cargo", "verus", "build"], cwd=splinter_dir, env=env2)

    if do_scripted_test:
        cache_hit, _, _, cargo_verus = verus_build_is_usable(verus_checkout, verus_commit)
        if cache_hit:
            cargo_verus_dir = cargo_verus.parent
            env2 = env.copy()
            env2["PATH"] = f"{cargo_verus_dir}:{env2.get('PATH', '')}"
        else:
            env2 = env.copy()

        print("== run crash-recovery scripted regression ==")
        (splinter_dir / "storage.bin").touch()
        log_path = Path("/tmp/verisplinter-script.log")
        with log_path.open("w") as log:
            try:
                proc = subprocess.run(
                    ["./target/debug/verisplinter"],
                    cwd=str(splinter_dir),
                    env=env2,
                    stdout=log,
                    stderr=subprocess.STDOUT,
                    timeout=120,
                )
            except subprocess.TimeoutExpired:
                print("scripted regression timed out")
                print(log_path.read_text()[-6000:])
                raise SystemExit(1)
        if proc.returncode != 0:
            print(f"scripted regression failed with status {proc.returncode}")
            print(log_path.read_text()[-6000:])
            raise SystemExit(proc.returncode)
        print(log_path.read_text()[-4000:])

    print("== done ==")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except subprocess.CalledProcessError as e:
        print(f"Command failed with exit code {e.returncode}", file=sys.stderr)
        raise
