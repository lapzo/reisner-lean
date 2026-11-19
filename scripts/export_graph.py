#!/usr/bin/env python3
"""Export the leanblueprint graph as DOT, SVG and PDF on a white background."""

from pathlib import Path
import re
import subprocess


def main() -> None:
    html = Path("blueprint/web/dep_graph_document.html").read_text()
    match = re.search(r"\.renderDot\(`(.*?)`\)", html, re.DOTALL)
    if match is None:
        raise SystemExit("No generated dependency graph; build the web blueprint first")
    output = Path("blueprint/dep_graph.dot")
    output.write_text(match[1].replace("bgcolor=transparent", "bgcolor=white", 1) + "\n")
    for kind in ("svg", "pdf"):
        subprocess.run(
            ["dot", f"-T{kind}", str(output), "-o", f"blueprint/dep_graph.{kind}"],
            check=True,
        )


if __name__ == "__main__":
    main()
