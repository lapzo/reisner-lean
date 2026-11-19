#!/usr/bin/env python3
"""Make one local source page with file-local anchors for all blueprint Lean."""

from html import escape
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from lean_sources import SOURCE_FILES, resolve_declaration  # noqa: E402


def main() -> None:
    names = (ROOT / "blueprint/lean_decls").read_text().splitlines()
    linked = {name: resolve_declaration(name, ROOT) for name in names}
    linked_at = {(decl.source.key, decl.line): name for name, decl in linked.items()}
    if len(linked_at) != len(linked):
        raise SystemExit("Multiple blueprint declarations resolve to the same source line")
    source_sections = []
    for source in SOURCE_FILES:
        lines = (ROOT / source.relative_path).read_text().splitlines()
        rows = []
        for number, line in enumerate(lines, 1):
            declaration = linked_at.get((source.key, number))
            doc_anchor = (f'<a id="doc/{escape(declaration)}" '
                          f'data-source="{escape(source.relative_path)}" '
                          f'data-line="{number}"></a>'
                          if declaration else "")
            if source.key == "stanley":
                row_id = f"L{number}"
            else:
                row_id = f"{source.key.capitalize()}-L{number}"
            rows.append(
                f'{doc_anchor}<span id="{row_id}" data-source="{escape(source.relative_path)}" '
                f'data-line="{number}">{number:3}  {escape(line)}</span>'
            )
        source_sections.append(
            f'<h2 id="source-{escape(source.key)}">{escape(source.relative_path)}</h2>'
            '<pre><code>' + "\n".join(rows) + '</code></pre>'
        )

    output = ROOT / "blueprint/web/lean/find/index.html"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        '<!doctype html><html lang="en"><meta charset="utf-8">'
        '<title>Reisner Lean source</title>'
        '<style>body{max-width:1100px;margin:2em auto;padding:0 1em;'
        'font-family:system-ui}pre{overflow:auto;padding:1em;background:#f4f5f7;'
        'line-height:1.5}a{scroll-margin-top:1em}span:target{background:#fff0a0}</style>'
        '<h1>Reisner Lean source</h1><p><a href="../../index.html">Blueprint</a>'
        ' · <a href="../../dep_graph_document.html">Dependency graph</a></p>'
        '<p>Each source keeps its own line numbers. Declaration names are validated '
        'by <code>leanblueprint checkdecls</code>.</p>'
        + "\n".join(source_sections) + '</html>\n'
    )


if __name__ == "__main__":
    main()
