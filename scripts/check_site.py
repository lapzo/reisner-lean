#!/usr/bin/env python3
"""Check generated local pages, declaration anchors, and source snapshots."""

from collections import Counter
import json
from pathlib import Path
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "site"))
from build import Document, Element, node_metadata  # noqa: E402
sys.path.insert(0, str(ROOT / "scripts"))
from lean_sources import SOURCE_FILES, resolve_declaration  # noqa: E402


def elements(node):
    if isinstance(node, Element):
        yield node
        for child in node.children:
            yield from elements(child)


def main():
    out = ROOT / "site/dist"
    source_lines = {
        source.key: (ROOT / source.relative_path).read_text().splitlines()
        for source in SOURCE_FILES
    }
    source_by_path = {source.relative_path: source for source in SOURCE_FILES}
    cache = {}

    def read_page(path):
        if path not in cache:
            nodes = list(elements(Document(path.read_text()).root))
            ids = Counter(node.attrs["id"] for node in nodes if node.attrs.get("id"))
            assert all(count == 1 for count in ids.values()), f"Duplicate IDs in {path}"
            cache[path] = (nodes, ids)
        return cache[path]

    links = rows = 0
    for path in [out / "index.html", out / "blueprint.html"]:
        nodes, _ = read_page(path)
        for node in nodes:
            if "code-line" in node.classes:
                number = int(node.find(lambda n: "line-no" in n.classes).text())
                displayed = node.find(lambda n: "source-line" in n.classes).text()
                source_path = node.attrs.get("data-source", SOURCE_FILES[0].relative_path)
                assert source_path in source_by_path, f"Unknown source file: {source_path}"
                source = source_by_path[source_path]
                assert 1 <= number <= len(source_lines[source.key]), (
                    f"Source line out of bounds: {path}:{source_path}:{number}"
                )
                assert displayed == source_lines[source.key][number - 1], (
                    f"Source row mismatch: {path}:{source_path}:{number}"
                )
                row_id = node.attrs.get("id")
                if row_id:
                    assert row_id == f"{source.anchor_prefix}{number}", (
                        f"Incorrect source anchor: {path}:{source_path}:{number}"
                    )
                rows += 1
            for attr in ["href", "src", "xlink:href"]:
                value = node.attrs.get(attr)
                if not value:
                    continue
                ref = urlsplit(value)
                if ref.scheme or ref.netloc:
                    asset = attr == "src" or node.tag in {"link", "use", "image", "script"}
                    assert not asset or ref.scheme == "data", f"Remote asset: {value}"
                    continue
                target = (path.parent / unquote(ref.path)).resolve() if ref.path else path
                assert target.is_file(), f"Missing local target: {path}: {value}"
                if ref.fragment and target.suffix == ".html":
                    assert unquote(ref.fragment) in read_page(target)[1], (
                        f"Missing anchor: {path}: {value}"
                    )
                links += 1

    metadata = node_metadata()
    visiting, visited = set(), set()

    def visit(label):
        assert label in metadata, f"Missing blueprint dependency: {label}"
        assert label not in visiting, f"Cyclic blueprint dependency: {label}"
        if label in visited:
            return
        visiting.add(label)
        for dep in metadata[label]["deps"]:
            visit(dep)
        visiting.remove(label)
        visited.add(label)

    for label in metadata:
        visit(label)
    blueprint_nodes, blueprint_ids = read_page(out / "blueprint.html")
    articles = [node for node in blueprint_nodes if "blueprint-node" in node.classes]
    assert {node.attrs["id"] for node in articles} == set(metadata)
    for node in articles:
        assert node.attrs["data-status"] == metadata[node.attrs["id"]]["status"]
    declared = (ROOT / "blueprint/lean_decls").read_text().splitlines()
    source_page = ROOT / "blueprint/web/lean/find/index.html"
    source_nodes, source_ids = read_page(source_page)
    by_source = {source.key: source for source in SOURCE_FILES}
    source_line_rows = {}
    declaration_rows = {}
    for node in source_nodes:
        if node.tag == "span" and node.attrs.get("data-source"):
            source_path = node.attrs["data-source"]
            number = int(node.attrs["data-line"])
            assert source_path in source_by_path, f"Unknown source-page file: {source_path}"
            source = source_by_path[source_path]
            assert node.attrs.get("id") == (
                f"L{number}" if source.key == "stanley" else f"{source.key.capitalize()}-L{number}"
            ), f"Wrong source-page line anchor: {source_path}:{number}"
            assert 1 <= number <= len(source_lines[source.key])
            assert node.text() == f"{number:3}  {source_lines[source.key][number - 1]}", (
                f"Source-page row mismatch: {source_path}:{number}"
            )
            source_line_rows[(source.key, number)] = node
        elif node.tag == "a" and node.attrs.get("id", "").startswith("doc/"):
            declaration_rows[node.attrs["id"][4:]] = node
    for source in SOURCE_FILES:
        assert any(node.tag == "h2" and node.attrs.get("id") == f"source-{source.key}"
                   for node in source_nodes), f"Missing source section: {source.relative_path}"
        for number in range(1, len(source_lines[source.key]) + 1):
            assert (source.key, number) in source_line_rows, (
                f"Missing source row anchor: {source.relative_path}:{number}"
            )
    for name in declared:
        assert "doc/" + name in source_ids, f"Missing Lean source anchor: {name}"
        declaration = resolve_declaration(name, ROOT)
        assert declaration.source.key in by_source
        anchor = declaration_rows.get(name)
        assert anchor is not None, f"Missing declaration source anchor: {name}"
        assert anchor.attrs.get("data-source") == declaration.source.relative_path
        assert int(anchor.attrs.get("data-line", "0")) == declaration.line

    snapshots = [(ROOT / item.relative_path, item.relative_path.rsplit("/", 1)[-1])
                 for item in SOURCE_FILES] + [
        (ROOT / "Checks/Axioms.lean", "Axioms.lean"),
        (ROOT / "Checks/LocalizationKernelAudit.lean", "LocalizationKernelAudit.lean"),
        (ROOT / "Checks/Cech.lean", "Checks-Cech.lean"),
        (ROOT / "Checks/SimplicialCochain.lean", "Checks-SimplicialCochain.lean"),
        (ROOT / "AUDIT.md", "AUDIT.md"), (ROOT / "STATUS.md", "STATUS.md"),
        (ROOT / "lake-manifest.json", "lake-manifest.json"),
        (ROOT / "lakefile.lean", "lakefile.lean"), (ROOT / "lean-toolchain", "lean-toolchain")]
    for original, snapshot_name in snapshots:
        assert original.read_bytes() == (out / "source" / snapshot_name).read_bytes(), (
            f"Stale source snapshot: {original}"
        )
    for original, name in [(ROOT / "blueprint/print/print.pdf", "blueprint.pdf"),
                           (ROOT / "blueprint/dep_graph.svg", "dependency-graph.svg")]:
        assert original.read_bytes() == (out / name).read_bytes(), f"Stale artifact: {name}"
    print(json.dumps({"blueprint_nodes": len(metadata),
                      "checked_nodes": sum(n["status"] == "checked" for n in metadata.values()),
                      "linked_declarations": len(declared), "local_links": links,
                      "displayed_source_rows": rows,
                      "source_files": {source.relative_path: len(source_lines[source.key])
                                       for source in SOURCE_FILES},
                      "linked_source_files": len({resolve_declaration(name, ROOT).source.key
                                                   for name in declared}),
                      "unique_ids": True, "acyclic_dependencies": True,
                      "remote_assets": 0, "matching_snapshots": True}, indent=2))


if __name__ == "__main__":
    main()
