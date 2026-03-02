#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path


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


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run local equivalent of .github/workflows/verify.yml verify job."
    )
    parser.add_argument(
        "--fresh-verus",
        action="store_true",
        help="Delete and rebuild ./_verus from scratch (default is reuse).",
    )
    args = parser.parse_args()

    script_path = Path(__file__).resolve()
    # Script lives at <repo>/Splinter/tools/ci-local.sh
    repo_root = script_path.parents[2]
    splinter_dir = repo_root / "Splinter"
    verus_checkout = repo_root / "_verus"

    cfg = load_ci_config(repo_root)
    verus_repo = cfg["verus_repo"]
    verus_commit = cfg["verus_commit"]
    rust_toolchain = cfg["rust_toolchain"]

    print("== local CI config ==")
    print(f"verus_repo:     {verus_repo}")
    print(f"verus_commit:   {verus_commit}")
    print(f"rust_toolchain: {rust_toolchain}")

    print("== rust toolchain ==")
    run(["rustup", "toolchain", "install", rust_toolchain])

    if args.fresh_verus and verus_checkout.exists():
        print("== reset _verus ==")
        shutil.rmtree(verus_checkout)

    if not (verus_checkout / ".git").exists():
        print("== clone verus ==")
        run(["git", "clone", verus_repo, str(verus_checkout)])

    print("== checkout pinned verus commit ==")
    run(["git", "-C", str(verus_checkout), "fetch", "--all", "--tags"])
    run(["git", "-C", str(verus_checkout), "checkout", verus_commit])

    print("== build verus ==")
    env = os.environ.copy()
    env["RUSTUP_TOOLCHAIN"] = rust_toolchain
    run_bash(
        "source tools/activate && cd source && bash tools/get-z3.sh && vargo build --release",
        cwd=verus_checkout,
        env=env,
    )

    verus_bin = verus_checkout / "source" / "target-verus" / "release" / "verus"
    cargo_verus_bin = verus_checkout / "source" / "target-verus" / "release"

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
    env2 = env.copy()
    env2["PATH"] = f"{cargo_verus_bin}:{env2.get('PATH', '')}"
    run(["cargo", "verus", "build"], cwd=splinter_dir, env=env2)

    print("== done ==")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except subprocess.CalledProcessError as e:
        print(f"Command failed with exit code {e.returncode}", file=sys.stderr)
        raise
