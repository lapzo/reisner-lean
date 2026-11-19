#!/usr/bin/env python3
"""Run leanblueprint, forwarding Nix's Python package paths to plastex.

The Nix leanblueprint entry point adds its dependencies to sys.path, but
does not export them to its plastex subprocess. Ordinary installations
need no adjustment. No system packages or files are modified.
"""

import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys


def main() -> int:
    binary = shutil.which("leanblueprint")
    if binary is None:
        sys.exit("leanblueprint is required; see README.md")
    env = os.environ.copy()
    if sys.argv[1:] == ["web"]:
        # plasTeX copies Nix theme assets with their read-only store modes.
        # Make the previously generated files replaceable on repeated builds.
        for path in Path("blueprint/web").rglob("*"):
            if path.is_file() and not path.is_symlink():
                path.chmod(path.stat().st_mode | stat.S_IWUSR)
    wrapped = Path(binary).resolve().with_name(".leanblueprint-wrapped")
    if wrapped.is_file():
        paths = re.findall(
            r"['\"](/nix/store/[^'\"\n]+/site-packages)['\"]",
            wrapped.read_text(),
        )
        if paths:
            paths = list(dict.fromkeys(paths))
            if env.get("PYTHONPATH"):
                paths.append(env["PYTHONPATH"])
            env["PYTHONPATH"] = os.pathsep.join(paths)
    return subprocess.run([binary, *sys.argv[1:]], env=env, check=False).returncode


if __name__ == "__main__":
    sys.exit(main())
