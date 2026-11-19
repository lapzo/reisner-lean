#!/usr/bin/env python3
"""Build a local, offline mathematical site from checked Lean and the blueprint."""

from dataclasses import dataclass, field
from html import escape
from html.parser import HTMLParser
from pathlib import Path
import re
import shutil
import subprocess
import sys
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parent.parent
SITE = ROOT / "site"
OUT = SITE / "dist"
SOURCE = ROOT / "Reisner/StanleyReisner.lean"
sys.path.insert(0, str(ROOT / "scripts"))
from lean_sources import (  # noqa: E402
    SOURCE_FILES,
    declaration_index,
    resolve_declaration,
)

SOURCE_PATHS = {source.key: ROOT / source.relative_path for source in SOURCE_FILES}


@dataclass
class Element:
    tag: str
    attrs: dict = field(default_factory=dict)
    children: list = field(default_factory=list)

    @property
    def classes(self):
        return self.attrs.get("class", "").split()

    def text(self):
        return "".join(child if isinstance(child, str) else child.text() for child in self.children)

    def find(self, predicate):
        if predicate(self):
            return self
        for child in self.children:
            if isinstance(child, Element):
                found = child.find(predicate)
                if found is not None:
                    return found
        return None


VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr"}


class Document(HTMLParser):
    def __init__(self, text):
        super().__init__(convert_charrefs=True)
        self.root = Element("root")
        self.stack = [self.root]
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        node = Element(tag, dict(attrs))
        self.stack[-1].children.append(node)
        if tag not in VOID:
            self.stack.append(node)

    def handle_startendtag(self, tag, attrs):
        self.stack[-1].children.append(Element(tag, dict(attrs)))

    def handle_endtag(self, tag):
        for index in range(len(self.stack) - 1, 0, -1):
            if self.stack[index].tag == tag:
                del self.stack[index:]
                return

    def handle_data(self, text):
        self.stack[-1].children.append(text)


def render(node):
    if isinstance(node, str):
        return escape(node, quote=False)
    body = "".join(render(child) for child in node.children)
    if node.tag == "root":
        return body
    attrs = "".join(f' {key}="{escape(value or "", quote=True)}"' for key, value in node.attrs.items())
    start = f"<{node.tag}{attrs}>"
    return start if node.tag in VOID else start + body + f"</{node.tag}>"


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"Command failed: {' '.join(command)}\n{result.stdout}\n{result.stderr}")
    return result.stdout + result.stderr


def math_html(text, source_format):
    # These have the same textual meaning; texmath supports the AMS form.
    text = text.replace(r"\hbox{", r"\text{")
    result = subprocess.run(
        ["pandoc", "-f", source_format, "-t", "html5", "--mathml", "--wrap=none"],
        input=text, text=True, capture_output=True, cwd=ROOT,
    )
    if result.returncode or "Could not convert" in result.stderr or "Could not parse" in result.stderr:
        raise RuntimeError("Math conversion failed:\n" + result.stderr)
    if result.stderr:
        print(result.stderr, file=sys.stderr)
    return re.sub(
        r'(<math\b[^>]*display="block"[^>]*>.*?</math>)',
        r'<div class="math-display">\1</div>', result.stdout, flags=re.DOTALL,
    )


def node_metadata():
    text = (ROOT / "blueprint/src/content.tex").read_text()
    pattern = re.compile(
        r"\\begin\{(definition|lemma|theorem|proposition|corollary)\}"
        r"\[([^\]]+)\]\\label\{([^}]+)\}"
    )
    matches = list(pattern.finditer(text))
    nodes = {}
    for i, match in enumerate(matches):
        block = text[match.start():matches[i + 1].start() if i + 1 < len(matches) else len(text)]
        statement = block.split("\\end{" + match[1] + "}", 1)[0]
        checked = "\\leanok" in statement
        label = match[3]
        nodes[label] = {
            "kind": match[1].capitalize(),
            "title": match[2].replace("--", "–"),
            "label": label,
            "status": "checked" if checked else "external" if label.startswith("found:") else "planned",
            "deps": list(dict.fromkeys(dep.strip() for group in re.findall(r"\\uses\{([^}]+)\}", block) for dep in group.split(","))),
            "lean": [name.strip() for group in re.findall(r"\\lean\{([^}]+)\}", statement) for name in group.split(",")],
        }
    if len(nodes) != len(matches):
        raise RuntimeError("Duplicate blueprint labels")
    return nodes


def badge(status):
    title = {"checked": "Checked in Lean", "planned": "Not yet formalized", "external": "External foundation"}[status]
    return f'<span class="status-badge {status}">{title}</span>'


EXCERPTS = {
    "complex": ["Complex"], "indicator-definition": ["squarefreeExponent"],
    "ideal": ["nonfaceExponents", "stanleyReisnerIdeal"],
    "quotient": ["FaceRing"], "comparison": ["squarefreeExponent_le_iff"],
    "main-proof": ["monomial_mem_stanleyReisnerIdeal_iff"],
    "polynomial-membership": ["mem_stanleyReisnerIdeal_iff"],
    "complex-helpers": ["face_of_subset", "nonface_of_subset"],
    "product": ["monomial_squarefreeExponent_eq_prod"],
    "span": ["stanleyReisnerIdeal_eq_span"],
    "basis": ["faceExponents", "stanleyReisnerIdeal_restrictScalars_eq_restrictSupport",
              "isCompl_stanleyReisnerIdeal_faceSupport", "faceRingBasis", "faceRingBasis_apply"],
    "consequences": ["faceRing_algebraMap_injective", "faceRing_nontrivial"],
    "homogeneous": ["stanleyReisnerIdeal_isHomogeneous",
                    "weightedHomogeneousComponent_mem_stanleyReisnerIdeal",
                    "weight_fine_eq", "weight_one_eq_sum"],
    "grading-core": ["weightedFaceRingComponent", "weightedFaceRingComponent_eq_span",
                     "monomial_nonface_eq_zero", "weightedFaceRingComponent_eq_polynomial_image",
                     "weightedFaceRingComponent_mul", "weightedFaceRing_isInternal",
                     "weightedFaceRingGradedAlgebra"],
    "grading-specializations": ["faceRingFineComponent", "faceRingTotalComponent",
                                "faceRingFineGradedAlgebra", "faceRingTotalGradedAlgebra",
                                "faceRingFineComponent_eq_span_monomial",
                                "faceRingFineComponent_eq_bot_of_nonface",
                                "faceRingTotalComponent_eq_span",
                                "faceRingTotalComponent_eq_iSup_fine"],
    "degree-zero": ["faceRingFineComponent_zero", "faceRingTotalComponent_zero",
                    "faceRingDegreeZeroSubalgebra", "faceRingDegreeZeroEquiv",
                    "faceRingDegreeZeroEquiv_apply"],
    "augmentation-map": ["faceRingConstantCoeffHom", "faceRingConstantCoeff_vanishes_on_ideal",
                         "faceRingAugmentation", "faceRingAugmentation_mk",
                         "faceRingAugmentation_algebraMap", "faceRingAugmentation_surjective"],
    "augmentation-kernel": ["faceRingAugmentationIdeal", "faceRingPositiveIdeal",
                             "idealOfVars_eq_ker_constantCoeff",
                             "faceRingAugmentationIdeal_eq_map_idealOfVars",
                             "faceRingAugmentation_ker", "faceRingResidueEquiv",
                             "faceRingResidueEquiv_mk", "faceRingAugmentationIdeal_eq_positive",
                             "faceRingAugmentationIdeal_isHomogeneous"],
    "augmentation-algebra": ["faceRing_finiteType", "faceRing_isNoetherianRing",
                              "faceRingAugmentationIdeal_isMaximal"],
    "augmentation-edge-cases": ["faceRing_variable_eq_zero_of_ghost",
                                 "faceRingAugmentationIdeal_eq_span_vertices",
                                 "faceRingAugmentationIdeal_eq_bot_of_no_vertices",
                                 "faceRingAugmentationEquivOfNoVertices",
                                 "faceRingAugmentationEquivOfNoVertices_apply"],
    "coordinate-membership": ["coordinateIdeal", "mem_coordinateIdeal_iff"],
    "coordinate-quotient": ["coordinateRestriction", "coordinateRestriction_ker",
                            "coordinateRestriction_surjective", "coordinateQuotientEquiv",
                            "coordinateQuotientEquiv_mk", "coordinateRestriction_X_inside",
                            "coordinateRestriction_X_outside", "coordinateIdeal_isPrime",
                            "coordinateQuotient_ringKrullDim"],
    "facet-decomposition": ["facets", "facets_finite", "exists_facet_superset",
                            "facets_nonempty", "stanleyReisnerIdeal_eq_iInf_coordinateIdeal",
                            "exists_facet_coordinateIdeal_le"],
    "facet-edge-cases": ["ghost_not_mem_facet",
                         "facets_eq_singleton_empty_of_no_vertices"],
    "dimension-objects": ["vertices", "maxFaceCard", "card_le_maxFaceCard",
                          "exists_face_card_eq_maxFaceCard", "exists_facet_card_eq_maxFaceCard",
                          "dimension", "maxFaceCard_eq_zero_iff_no_vertices",
                          "dimension_eq_neg_one_iff_no_vertices"],
    "coordinate-chain": ["X_mem_coordinateIdeal_iff", "coordinateIdeal_le_iff",
                         "coordinateIdeal_empty", "exists_coordinatePrimeChain"],
    "dimension-upper": ["stanleyReisnerIdeal_le_coordinateIdeal", "faceRing_ringKrullDim_le"],
    "dimension-lower": ["exists_faceRingPrimeChain", "card_le_faceRingAugmentationIdeal_height",
                        "maxFaceCard_le_faceRingAugmentationIdeal_height"],
    "dimension-result": ["faceRingAugmentationIdeal_isPrime", "faceRing_ringKrullDim",
                         "faceRingAugmentationIdeal_height", "faceRing_atAugmentation_ringKrullDim"],
    "localization-objects": ["faceRingFaceProduct", "faceRingFaceProduct_eq_monomial",
                             "faceRingFaceProduct_empty", "faceRingFaceProduct_dvd",
                             "faceRingFaceProduct_sdiff", "FaceRingLocalization",
                             "faceRingLocalizationFraction", "faceRingLocalizationFraction_zero_power",
                             "faceRingLocalizationFraction_surjective"],
    "localization-kernel": ["monomial_mul_mem_stanleyReisnerIdeal_iff",
                            "faceRingFaceProduct_pow_mul_mk", "faceRingFaceProduct_mul_mk_eq_zero_iff",
                            "faceRingLocalization_algebraMap_mk_eq_zero_iff",
                            "faceRingLocalization_algebraMap_eq_zero_iff",
                            "faceRingLocalizationFraction_eq_zero_iff"],
    "localization-nonzero": ["faceRingLocalization_monomialFraction_ne_zero_iff",
                             "faceRingLocalization_nontrivial_iff",
                             "faceRingLocalization_subsingleton_of_nonface",
                             "faceRingLocalization_scalarMap_injective"],
    "localization-maps": ["faceRingLocalizationEmptyEquiv", "faceRingLocalizationEmptyEquiv_apply",
                          "faceRingLocalizationMap", "faceRingLocalizationMap_algebraMap",
                          "faceRingLocalizationMap_fraction", "faceRingLocalizationMap_self",
                          "faceRingLocalizationMap_comp"],
    "laurent-monomials": ["natExponent", "natExponent_apply", "positiveSupport", "LocalizationAdmissible",
                          "fractionDegree", "fractionDegree_apply", "localizationMonomial",
                          "localizationMonomial_fraction", "localizationMonomial_eq_zero_of_not_admissible",
                          "localizationDegrees", "localizationMonomialBasis", "localizationMonomialBasis_apply",
                          "localizationMonomial_ne_zero_iff", "localizationMonomial_natExponent"],
    "laurent-grading": ["faceRingLocalizationComponent", "faceRingLocalizationComponent_eq_bot",
                        "faceRingLocalizationComponent_finrank", "faceRingLocalization_isInternal",
                        "faceRingLocalizationGradedAlgebra", "faceRingLocalizationFraction_mem_component",
                        "faceRingLocalizationComponentBasis", "faceRingLocalizationComponentBasis_apply",
                        "faceRingFineComponent_map_localization"],
    "laurent-transitions": ["faceRingLocalizationMap_monomial", "faceRingLocalizationMap_component",
                            "faceRingLocalizationMap_basis", "faceRingLocalizationMap_basis_eq_zero"],
    "cech-complex": ["CechIndex", "CechCochain", "CechCochainDirectSum",
                      "cechCochainDirectSumEquiv", "cechDifferentialComponent",
                      "cechDifferential", "cechDifferential_apply",
                      "cechDifferential_comp_eq_zero", "cechComplex",
                      "cechComplex_X", "cechComplex_d", "cechDegreeSubmodule",
                      "cechDifferential_maps_degree", "cechDifferentialDegree"],
    "cech-basis-action": ["cechInsertIndex", "cechMonomialCochain",
                           "cechMonomialCochain_apply_self",
                           "cechMonomialCochain_apply_of_ne",
                           "cechDifferential_monomialCochain"],
    "cech-termwise-decomposition": ["cechCochainMonomialBasis",
                                     "cechDegreeSubmodule",
                                     "cechDegreeSubmodule_isInternal"],
}


def code_block(start, end, anchors=False, source_key="stanley"):
    source_file = next(source for source in SOURCE_FILES if source.key == source_key)
    lines = (ROOT / source_file.relative_path).read_text().splitlines()
    keywords = r"\b(module|public|import|namespace|universe|structure|where|theorem|noncomputable|def|abbrev|variable|by|classical|constructor|intro|have|simpa|using|exact|by_cases|simp|only|rw|rintro|end|fun|if|then|else)\b"
    rows = []
    for number in range(start, end + 1):
        line = escape(lines[number - 1])
        line = re.sub(keywords, r'<span class="kw">\1</span>', line)
        ident = f' id="{source_file.anchor_prefix}{number}"' if anchors else ""
        rows.append(f'<span class="code-line" data-source="{source_file.relative_path}"{ident}><span class="line-no" aria-hidden="true">{number}</span><span class="source-line">{line}</span></span>')
    return (f'<div class="code-wrap"><div class="code-header"><span>{escape(source_file.relative_path)}'
            f' · lines {start}–{end}</span><button type="button" class="copy-button" aria-label="Copy Lean code">Copy</button>'
            '</div><pre><code>' + "".join(rows) + '</code></pre></div>')


def code_for(key):
    if key == "full-source":
        return code_block(1, len(SOURCE.read_text().splitlines()), anchors=True)
    if key == "full-cech-source":
        lines = SOURCE_PATHS["cech"].read_text().splitlines()
        return code_block(1, len(lines), anchors=True, source_key="cech")
    ranges = []
    for name in EXCERPTS[key]:
        declaration = resolve_declaration(name, ROOT)
        source_key = declaration.source.key
        lines = SOURCE_PATHS[source_key].read_text().splitlines()
        starts = sorted(
            candidate.line for candidate in declaration_index(ROOT)[0].values()
            if candidate.source.key == source_key
        )
        start = declaration.line
        boundary = re.compile(r'^(?:/--|/-!|@\[|namespace\b|end\b|variable\b|section\b|private\s)')
        next_boundary = next((number for number in range(start + 1, len(lines) + 1)
                              if boundary.match(lines[number - 1])), len(lines) + 1)
        next_declaration = min((candidate for candidate in starts if candidate > start), default=len(lines) + 1)
        end = min(next_boundary, next_declaration) - 1
        while end >= start and not lines[end - 1].strip():
            end -= 1
        ranges.append((source_key, start, end))
    return ''.join(code_block(start, end, source_key=source_key)
                   for source_key, start, end in ranges)


def status_panel(nodes, linked):
    count = sum(node["status"] == "checked" for node in nodes.values())
    return (f'<div class="evidence"><div><strong>{count} / {len(nodes)}</strong>blueprint nodes checked</div>'
            f'<div><strong>{linked}</strong>linked Lean declarations</div><div><strong>0</strong>custom project axioms</div></div>'
            '<p>Checked: augmented complex and face-ring definitions, indicator comparison, '
            'monomial membership, the standard monomial quotient basis, weighted polynomial '
            'ideal homogeneity, and the quotient fine/total grading with its degree-zero scalar '
            'equivalence, augmentation/residue foundations, finite type and Noetherianity, '
            'coordinate-prime/facet structure, simplicial dimension, and the global and '
            'augmentation-local face-ring dimension equalities, and concrete localizations '
            'with exact fraction kernels, transition maps, and an integer grading with '
            'a Laurent monomial basis. The finite extended Čech cochain complex, its signed '
            'localization differential, square-zero law, and fine-degree restrictions are '
            'also checked, together with its signed action on localization monomial cochains '
            'and the internal direct-sum decomposition of each cochain module by fine degree. '
            'The cohomology decomposition remains future work. The count includes definitions; '
            'implemented proof blocks carry proof markers.</p>')


def route(nodes):
    steps = [
        ("thm:membership", "Nonfaces → monomial membership", "Squarefree generators are detected by exponent support. This is the checked entry point."),
        ("prop:basis", "Surviving monomials → a quotient basis", "Separate face-supported and nonface-supported terms to construct the standard monomial basis."),
        ("lem:homogeneous", "Weighted homogeneous components → ideal", "Every nonface monomial generator is homogeneous for every additive-monoid weight; the generated polynomial ideal is homogeneous."),
        ("prop:grading", "Weighted fibers → quotient graded algebra", "Standard-basis coordinate fibers give the fine and total quotient gradings; degree zero is exactly the scalar subalgebra."),
        ("prop:augmentation", "Evaluation at zero → residue algebra", "The augmentation kernel is the variable ideal and the ideal generated by positive-degree pieces; finite type and Noetherianity follow under their stated hypotheses."),
        ("prop:facet-primes", "Coordinate quotients → facet primes", "Restrict variables to a facet, identify the quotient, intersect the coordinate ideals, and place every prime over the Stanley–Reisner ideal above one facet ideal."),
        ("prop:dimension", "Facet primes → face-ring dimension", "Bound all prime chains using a facet quotient; construct a coordinate-prime chain ending at the augmentation ideal and identify localized dimension with its height."),
        ("lem:localization-kernel", "Variable-product fractions → exact kernels", "Construct the actual localizations, detect fraction vanishing term by term, and build coherent transition maps for nested inverted sets."),
        ("lem:localized", "Integer-graded pieces → Laurent monomials", "Clear denominators to prove the Laurent monomial basis, then identify each degree component and the maps between them."),
        ("lem:cech-complex", "Localized terms → a finite Čech complex", "Assemble every subset localization into a signed cochain complex, prove the differential squares to zero, and restrict it to each fine degree."),
        ("lem:cech-basis-action", "Monomial cochains → signed insertion formula", "Evaluate at each target coordinate and identify the unique inserted vertex; inadmissible target monomials vanish."),
        ("lem:cech-termwise-decomposition", "Fine degrees → a termwise cochain decomposition", "Use the product of localization monomial bases and disjoint degree fibers to identify each cochain module with the direct sum of its degree submodules."),
        ("cor:cm-lc", "Algebraic depth → local cohomology", "Use the graded local test and depth detection to translate Cohen–Macaulayness into vanishing below the dimension."),
        ("thm:lc-link", "Graded Čech pieces → link cohomology", "Compute localized monomials, contract positive degrees, and identify the remaining complexes with augmented link cochains."),
        ("thm:reisner", "Purity and vanishing → the criterion", "Prove purity from linkwise vanishing, match the dimension bounds, and deduce both implications."),
    ]
    return '<ol class="route-list">' + "".join(
        f'<li><span class="route-number">{i}</span><div><a href="blueprint.html#{label}">{escape(title)}</a>'
        + badge(nodes[label]["status"]) + f'<p>{escape(description)}</p></div></li>'
        for i, (label, title, description) in enumerate(steps, 1)
    ) + '</ol>'


def page(title, content, toc, active):
    style = (SITE / "style.css").read_text()
    script = (SITE / "site.js").read_text()
    nav = ''.join(f'<a href="{href}"' + (' aria-current="page"' if key == active else '') + f'>{name}</a>'
                  for key, href, name in [("paper", "index.html", "Proof & Lean"), ("blueprint", "blueprint.html", "Blueprint")])
    sidebar = ''.join(f'<li><a href="#{escape(ident)}">{escape(label)}</a></li>' for ident, label in toc)
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="description" content="Reisner's criterion: mathematical proof route, checked Lean code, and an honest formalization blueprint.">
<title>{escape(title)} · Reisner formalization</title><style>{style}</style></head>
<body class="{active}-page"><a class="skip" href="#main">Skip to the mathematics</a>
<header class="topbar"><div class="topbar-inner"><a class="brand" href="index.html">Reisner’s criterion</a><nav aria-label="Main navigation">{nav}</nav></div></header>
<div class="page-shell"><aside class="toc" aria-label="On this page"><div class="toc-label">On this page</div><ol>{sidebar}</ol>
<div class="toc-extra"><a href="source/StanleyReisner.lean">Lean source ↗</a><a href="blueprint.pdf">Blueprint PDF ↗</a><small>Lean 4.35.0<br>Localization kernels and grading</small></div></aside>
<main id="main"><p class="eyebrow">Combinatorial commutative algebra · Lean 4</p><h1>{escape(title)}</h1>{content}</main></div>
<footer class="site-footer">The Reisner formalization project · Checked code and future work are labelled separately · Built from local project sources</footer>
<script>{script}</script></body></html>'''


def clean_blueprint(node):
    if isinstance(node, str):
        return node
    if any(c in node.classes for c in ("titlepage", "thm_header_extras", "thm_header_hidden_extras")):
        return None
    if node.tag in {"script", "button"}:
        return None
    if "href" in node.attrs and node.attrs["href"].startswith("index.html#"):
        node.attrs["href"] = node.attrs["href"][len("index.html"):]
    if node.tag == "a" and "name" in node.attrs:
        node.attrs["id"] = node.attrs.pop("name")
    node.children = [result for child in node.children if (result := clean_blueprint(child)) is not None]
    return node


def graph_svg(nodes):
    ns = "http://www.w3.org/2000/svg"
    ET.register_namespace("", ns)
    graph = ET.fromstring((ROOT / "blueprint/dep_graph.svg").read_text())
    graph.attrib.pop("width", None); graph.attrib.pop("height", None)
    graph.set("aria-label", "Dependency graph: activate a node to read its statement and proof")
    graph.set("role", "group")
    for group in graph.iter(f"{{{ns}}}g"):
        if group.get("class") != "node":
            continue
        title = group.find(f"{{{ns}}}title")
        if title is None or title.text not in nodes:
            continue
        node = nodes[title.text]
        link = ET.Element(f"{{{ns}}}a", {"href": '#' + node['label'], "tabindex": "0", "aria-label": node['title']})
        for child in list(group):
            if child is not title:
                group.remove(child); link.append(child)
        title.text = node['title'] + ' — ' + node['status']
        group.append(link)
    return ET.tostring(graph, encoding="unicode")


NODE_CODE = {
    "def:complex": ["complex", "complex-helpers"],
    "def:dimension": ["dimension-objects", "facet-decomposition"],
    "def:ring": ["indicator-definition", "product", "ideal", "span", "quotient"],
    "lem:indicator": ["comparison"],
    "thm:membership": ["polynomial-membership", "main-proof"],
    "prop:basis": ["basis"],
    "lem:homogeneous": ["homogeneous"],
    "prop:grading": ["grading-core", "grading-specializations", "degree-zero"],
    "prop:augmentation": ["augmentation-map", "augmentation-kernel",
                           "augmentation-algebra", "augmentation-edge-cases"],
    "prop:facet-primes": ["coordinate-membership", "coordinate-quotient",
                           "facet-decomposition", "facet-edge-cases"],
    "prop:dimension": ["coordinate-chain", "dimension-upper", "dimension-lower", "dimension-result"],
    "lem:localized": ["laurent-monomials", "laurent-grading", "laurent-transitions"],
    "lem:cech-complex": ["cech-complex"],
    "lem:cech-basis-action": ["cech-basis-action"],
    "lem:cech-termwise-decomposition": ["cech-termwise-decomposition"],
    "lem:localization-kernel": ["localization-objects", "localization-kernel",
                                "localization-nonzero", "localization-maps"],
}


def blueprint_content(nodes, linked):
    document = Document((ROOT / "blueprint/web/index.html").read_text())
    main = document.root.find(lambda n: "main-text" in n.classes)
    if main is None:
        raise RuntimeError("Generated blueprint has no main-text container")
    clean_blueprint(main)
    converted = math_html(render(main), "html+tex_math_single_backslash")
    content = Document(converted).root.find(lambda n: "main-text" in n.classes)
    if content is None:
        raise RuntimeError("Math conversion lost the blueprint container")
    sections, toc = [], []
    current_section = None
    current_article = None
    encountered = set()
    for element in content.children:
        if isinstance(element, str) and not element.strip():
            continue
        if isinstance(element, Element) and element.tag == "h1":
            current_article = None
            ident = element.attrs.get("id", f"section-{len(sections) + 1}")
            name = element.text().strip()
            element.tag = "h2"
            current_section = {"head": render(element), "body": [], "has_nodes": False}
            sections.append(current_section)
            toc.append((ident, re.sub(r"^\d+\s+", "", name)))
        elif isinstance(element, Element) and element.attrs.get("id") in nodes:
            metadata = nodes[element.attrs['id']]
            encountered.add(metadata['label'])
            statement = element.find(lambda n: any(c.endswith("_thmcontent") for c in n.classes))
            if statement is None:
                raise RuntimeError("Missing statement: " + metadata['label'])
            heading = (f'<div class="node-top"><div><span class="node-label">{metadata["label"]}</span>'
                       f'<h3>{metadata["kind"]}. {escape(metadata["title"])}</h3></div>{badge(metadata["status"])}</div>')
            deps = '<div class="node-dependencies">Uses: ' + (' '.join(
                f'<a href="#{label}">{escape(nodes[label]["title"])}</a>' for label in metadata['deps']
            ) if metadata['deps'] else 'base definitions') + '</div>'
            current_article = {'metadata': metadata, 'parts': [heading, '<div class="statement">' + render(statement) + '</div>', deps]}
            if metadata['lean']:
                links = ''.join(f'<li><a class="source-link" href="index.html#{source_anchor(name)}">{escape(name)}</a></li>' for name in metadata['lean'])
                code = ''.join(code_for(key) for key in NODE_CODE[metadata['label']])
                current_article['parts'].append('<details><summary>Checked Lean declarations and source</summary><ul>' + links + '</ul>' + code + '</details>')
            current_section['body'].append(current_article)
            current_section['has_nodes'] = True
        else:
            text = render(element)
            if isinstance(element, Element) and 'proof_wrapper' in element.classes:
                text = '<details class="mathematical-proof"><summary>Mathematical proof</summary>' + text + '</details>'
            if current_article is not None:
                current_article['parts'].append(text)
            elif current_section is not None:
                current_section['body'].append(text)
    if encountered != set(nodes):
        raise RuntimeError(f"Blueprint nodes missing from the site: {set(nodes) - encountered}")
    body = []
    for section in sections:
        rendered = []
        for part in section['body']:
            if isinstance(part, str):
                rendered.append(part)
            else:
                meta = part['metadata']
                rendered.append(f'<article class="blueprint-node" id="{meta["label"]}" data-status="{meta["status"]}">' + ''.join(part['parts']) + '</article>')
        body.append(f'<section class="blueprint-section" data-node-section="{str(section["has_nodes"]).lower()}">' + section['head'] + ''.join(rendered) + '</section>')
    intro = ('<p class="lead">The full mathematical route, with statements, proofs, dependencies, and the Lean declarations that have been checked.</p>'
             + status_panel(nodes, linked)
             + '<p class="blueprint-intro">Green marks a checked node. Unmarked results remain future Lean work. '
             'External foundations are cited mathematical results with missing formal comparisons; they are not new Lean axioms.</p>'
             '<p class="link-row"><a href="#dependency-graph">Dependency graph</a> · <a href="#node-search">Find a node</a> · '
             '<a href="blueprint.pdf">Download the original blueprint PDF</a></p>'
             '<h2 id="dependency-graph">Dependency graph</h2><p class="muted">Follow an arrow from a prerequisite to the result that uses it. Select a node to read its statement.</p>'
             '<div class="graph-viewport">' + graph_svg(nodes) + '</div>'
             '<div class="graph-toolbar"><span>Green: checked · Blue: prerequisites ready · White: future work</span><div class="buttons">'
             '<button class="small-button" id="zoom-out" type="button" aria-label="Zoom out">−</button>'
             '<span id="zoom-level" aria-live="polite">100%</span>'
             '<button class="small-button" id="zoom-in" type="button" aria-label="Zoom in">+</button>'
             '<button class="small-button" id="zoom-fit" type="button">Fit</button></div></div>'
             '<h2 id="nodes">Statements and proofs</h2><div class="blueprint-controls">'
             '<input id="node-search" type="search" aria-label="Search blueprint statements and proofs" placeholder="Find a statement, proof, or declaration…">'
             '<select id="node-status" aria-label="Filter by formalization status"><option value="all">All nodes</option>'
             '<option value="checked">Checked in Lean</option><option value="planned">Not yet formalized</option><option value="external">External foundations</option></select>'
             '<button type="button" class="small-button" id="reset-filters">Reset</button></div>'
             f'<p class="filter-label" id="filter-count" aria-live="polite">{len(nodes)} of {len(nodes)} nodes shown</p>'
             '<p class="empty-state" id="empty-state" hidden>No matching nodes. Try a different term or reset the filters.</p>')
    return intro + ''.join(body), [('dependency-graph', 'Dependency graph'), ('nodes', 'Statements and proofs')] + toc


def source_line(name):
    declaration = resolve_declaration(name, ROOT)
    if declaration.source.key != "stanley":
        raise RuntimeError(
            f"{name} is in {declaration.source.relative_path}; use @@ANCHOR:{name}@@ "
            "instead of the legacy line-number placeholder"
        )
    return declaration.line


def source_anchor(name):
    return resolve_declaration(name, ROOT).site_anchor


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    validation = (run(['lake', 'build'])
                  + run(['lake', 'env', 'lean', 'Checks/Axioms.lean'])
                  + run(['lake', 'env', 'lean', 'Checks/LocalizationKernelAudit.lean'])
                  + run(['lake', 'env', 'lean', 'Checks/Cech.lean']))
    if 'sorryAx' in validation:
        raise RuntimeError('Axiom inspection contains a proof placeholder')
    allowed_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
    for group in re.findall(r'depends on axioms: \[([^]]*)\]', validation):
        dependencies = set(re.sub(r'\s+', '', group).split(','))
        if not dependencies <= allowed_axioms:
            raise RuntimeError('Unexpected axiom dependencies: ' + group)
    print('Lean build, axiom inspection, localization regressions, and Cech checks passed.')
    for args in [['pdf'], ['web'], ['checkdecls']]:
        run([sys.executable, 'scripts/blueprint.py', *args])
    run([sys.executable, 'scripts/lean_source.py'])
    run([sys.executable, 'scripts/export_graph.py'])
    print('Blueprint HTML, multi-file declaration source, and graph regenerated.')
    nodes = node_metadata()
    linked = (ROOT / 'blueprint/lean_decls').read_text().splitlines()
    referenced = [name for node in nodes.values() for name in node['lean']]
    if set(linked) != set(referenced):
        raise RuntimeError('Blueprint declaration lists disagree')
    markdown = (SITE / 'content/index.md').read_text().replace('@@TOTAL@@', str(len(nodes))).replace('@@CHECKED@@', str(sum(n['status'] == 'checked' for n in nodes.values())))
    markdown = re.sub(r'@@LINE:([A-Za-z_][A-Za-z0-9_]*)@@', lambda match: str(source_line(match[1])), markdown)
    markdown = re.sub(r'@@ANCHOR:([A-Za-z_][A-Za-z0-9_.]*)@@', lambda match: source_anchor(match[1]), markdown)
    paper = math_html(markdown, 'markdown+tex_math_dollars+raw_html')
    paper = re.sub(r'<!-- LEAN:([a-z-]+) -->', lambda match: code_for(match[1]), paper)
    paper = paper.replace('<!-- ROUTE -->', route(nodes)).replace('<!-- STATUS -->', status_panel(nodes, len(linked)))
    if '<!-- LEAN:' in paper or '@@' in paper:
        raise RuntimeError('Unexpanded content placeholder')
    toc = [('target', 'The target'), ('membership', 'Monomial membership'), ('basis', 'The quotient basis'), ('homogeneity', 'Weighted homogeneity'), ('grading', 'The quotient grading'), ('augmentation', 'Augmentation and residue'), ('facet-primes', 'Coordinate primes and facets'), ('dimension', 'Global and localized dimension'), ('localizations', 'Localization kernels and maps'), ('localized-grading', 'Integer grading of localizations'), ('cech-complex', 'The finite Čech complex'), ('cech-basis-action', 'Monomial cochain action'), ('cech-termwise-decomposition', 'Termwise fine-degree decomposition'), ('objects', 'Objects in Lean'), ('proof', 'The proof, in both languages'), ('route', 'The complete proof route'), ('checked', 'What is checked'), ('reproduce', 'Build and sources')]
    (OUT / 'index.html').write_text(page('Reisner’s criterion', paper, toc, 'paper'))
    content, blueprint_toc = blueprint_content(nodes, len(linked))
    (OUT / 'blueprint.html').write_text(page('The blueprint', content, blueprint_toc, 'blueprint'))
    (OUT / 'validation.txt').write_text(validation)
    (OUT / 'source').mkdir(exist_ok=True)
    for source in [*(ROOT / item.relative_path for item in SOURCE_FILES), ROOT / 'Checks/Axioms.lean', ROOT / 'Checks/LocalizationKernelAudit.lean', ROOT / 'Checks/Cech.lean', ROOT / 'AUDIT.md', ROOT / 'STATUS.md', ROOT / 'lake-manifest.json', ROOT / 'lakefile.lean', ROOT / 'lean-toolchain']:
        destination_name = 'Checks-Cech.lean' if source == ROOT / 'Checks/Cech.lean' else source.name
        shutil.copyfile(source, OUT / 'source' / destination_name)
    shutil.copyfile(ROOT / 'blueprint/print/print.pdf', OUT / 'blueprint.pdf')
    shutil.copyfile(ROOT / 'blueprint/dep_graph.svg', OUT / 'dependency-graph.svg')
    print(f'Built {OUT / "index.html"} and {OUT / "blueprint.html"}.')
    print(f'{len(nodes)} blueprint nodes; {len(linked)} validated declarations. Mathematics is native MathML, with no CDN.')


if __name__ == '__main__':
    main()
