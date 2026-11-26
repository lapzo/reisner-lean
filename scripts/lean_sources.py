"""Shared source-file and declaration index for the local Lean site tools."""

from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
import re


@dataclass(frozen=True)
class SourceFile:
    key: str
    relative_path: str
    anchor_prefix: str


@dataclass(frozen=True)
class Declaration:
    full_name: str
    short_name: str
    source: SourceFile
    line: int

    @property
    def site_anchor(self) -> str:
        return f"{self.source.anchor_prefix}{self.line}"

    @property
    def source_page_anchor(self) -> str:
        if self.source.key == "stanley":
            return f"L{self.line}"
        return f"{self.source.key.capitalize()}-L{self.line}"


SOURCE_FILES = (
    SourceFile("stanley", "Reisner/StanleyReisner.lean", "lean-L"),
    SourceFile("cech-core", "Reisner/Cech/Core.lean", "lean-Cech-core-L"),
    SourceFile("cech-grading", "Reisner/Cech/Grading.lean", "lean-Cech-grading-L"),
    SourceFile("cech-contraction", "Reisner/Cech/Contraction.lean", "lean-Cech-contraction-L"),
    SourceFile("cech-indices", "Reisner/Cech/Indices.lean", "lean-Cech-indices-L"),
    SourceFile("cech-link", "Reisner/Cech/LinkComparison.lean", "lean-Cech-link-L"),
    SourceFile("cech-shifted", "Reisner/Cech/ShiftedLink.lean", "lean-Cech-shifted-L"),
    SourceFile("cech-uniform-link", "Reisner/Cech/UniformLink.lean", "lean-Cech-uniform-link-L"),
    SourceFile("cech-link-homology", "Reisner/Cech/LinkHomology.lean", "lean-Cech-link-homology-L"),
    SourceFile("cech-degree-zero", "Reisner/Cech/DegreeZero.lean", "lean-Cech-degree-zero-L"),
    SourceFile("cech-ext-comparison", "Reisner/Cech/ExtComparison.lean", "lean-Cech-ext-comparison-L"),
    SourceFile("cech-localized-ext", "Reisner/Cech/LocalizedExt.lean", "lean-Cech-localized-ext-L"),
    SourceFile("cech-face-ring-linear", "Reisner/Cech/FaceRingLinear.lean", "lean-Cech-face-ring-linear-L"),
    SourceFile("local-cohomology", "Reisner/LocalCohomology.lean", "lean-Local-cohomology-L"),
    SourceFile("local-cm", "Reisner/LocalCohenMacaulay.lean", "lean-Local-cm-L"),
    SourceFile("graded-local", "Reisner/GradedLocalTest.lean", "lean-Graded-local-L"),
    SourceFile("reisner-criterion", "Reisner/ReisnerCriterion.lean", "lean-Reisner-criterion-L"),
    SourceFile("simplicial", "Reisner/SimplicialCochain.lean", "lean-Simplicial-L"),
    SourceFile("simplicial-chain", "Reisner/SimplicialChain.lean", "lean-Simplicial-chain-L"),
    SourceFile("simplicial-duality", "Reisner/SimplicialDuality.lean", "lean-Simplicial-duality-L"),
    SourceFile("dual-homology", "Reisner/DualHomology.lean", "lean-Dual-homology-L"),
    SourceFile("link-calculus", "Reisner/LinkCalculus.lean", "lean-Link-calculus-L"),
    SourceFile("cech-purity", "Reisner/Cech/Purity.lean", "lean-Cech-purity-L"),
)

DECLARATION = re.compile(
    r"^(?:@\[[^\]]+\]\s*)?(?:(?:public|noncomputable|protected|private|unsafe|partial)\s+)*"
    r"(?:structure|theorem|lemma|def|abbrev|instance)\s+"
    # Include the Greek pi used in the mathlib homologyπ compatibility API.
    r"([A-Za-z_][A-Za-z0-9_']*π?)\b"
)
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$")
END = re.compile(r"^end(?:\s+([A-Za-z_][A-Za-z0-9_.']*))?\s*(?:--.*)?$")


def read_source_files(root: Path) -> dict[str, list[str]]:
    """Read the configured Lean files, keyed by their stable source key."""
    return {
        source.key: (root / source.relative_path).read_text().splitlines()
        for source in SOURCE_FILES
    }


@lru_cache(maxsize=None)
def _declarations_for(root_string: str) -> tuple[Declaration, ...]:
    root = Path(root_string)
    declarations: list[Declaration] = []
    for source in SOURCE_FILES:
        path = root / source.relative_path
        if not path.is_file():
            raise FileNotFoundError(f"Configured Lean source is missing: {path}")
        namespaces: list[str] = []
        for number, line in enumerate(path.read_text().splitlines(), 1):
            stripped = line.strip()
            if match := NAMESPACE.match(stripped):
                namespaces.append(match[1])
                continue
            if match := END.match(stripped):
                ending = match[1]
                if ending is None:
                    if namespaces:
                        namespaces.pop()
                else:
                    match_index = next(
                        (i for i in range(len(namespaces) - 1, -1, -1)
                         if namespaces[i] == ending or namespaces[i].endswith("." + ending)),
                        None,
                    )
                    if match_index is not None:
                        del namespaces[match_index:]
                continue
            if match := DECLARATION.match(stripped):
                short_name = match[1]
                full_name = ".".join([*namespaces, short_name])
                declarations.append(Declaration(full_name, short_name, source, number))
    return tuple(declarations)


def declarations(root: Path) -> tuple[Declaration, ...]:
    return _declarations_for(str(root.resolve()))


def declaration_index(root: Path) -> tuple[dict[str, Declaration], dict[str, list[Declaration]]]:
    by_full: dict[str, Declaration] = {}
    by_short: dict[str, list[Declaration]] = {}
    for declaration in declarations(root):
        if declaration.full_name in by_full:
            raise RuntimeError(f"Duplicate Lean declaration source: {declaration.full_name}")
        by_full[declaration.full_name] = declaration
        by_short.setdefault(declaration.short_name, []).append(declaration)
    return by_full, by_short


def resolve_declaration(name: str, root: Path) -> Declaration:
    """Resolve a blueprint/full or unique short declaration name."""
    by_full, by_short = declaration_index(root)
    if name in by_full:
        return by_full[name]
    short = name.rsplit(".", 1)[-1]
    matches = by_short.get(short, [])
    if len(matches) == 1:
        return matches[0]
    if not matches:
        raise RuntimeError(f"Declaration source not found: {name}")
    choices = ", ".join(declaration.full_name for declaration in matches)
    raise RuntimeError(f"Ambiguous short Lean declaration {name}: {choices}")
