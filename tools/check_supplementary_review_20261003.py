"""Check the review sources/PDFs and prepare page images for visual review."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

import pdfplumber
from pypdf import PdfReader
from PIL import Image, ImageDraw

ROOT = Path(__file__).resolve().parents[1]
REVIEW = ROOT / "documents/20261003/revisions/si-review-20261003"
BUILD = ROOT / "tmp/pdfs/supplementary-review-20261003"
QA = BUILD / "visual"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ledger = json.loads((REVIEW / "revision-ledger.json").read_text())
    assert sha(ROOT / "documents/20261003/main.tex") == ledger["baseline_main_sha256"]
    assert sha(ROOT / "documents/20261003/supplementary.tex") == ledger["baseline_supplementary_sha256"]
    clean = (REVIEW / "supplementary-revised.tex").read_text(encoding="utf-8")
    uncommented = re.sub(r"(?m)(?<!\\)%.*$", "", clean)
    labels = re.findall(r"\\label\{([^}]+)\}", uncommented)
    assert len(labels) == len(set(labels)), "Duplicate clean-source labels"
    main_source = (ROOT / "documents/20261003/main.tex").read_text(encoding="utf-8")
    main_labels = re.findall(r"\\label\{([^}]+)\}", re.sub(r"(?m)(?<!\\)%.*$", "", main_source))
    refs = re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", uncommented)
    missing = sorted(set(refs) - set(labels) - {"main-" + s for s in main_labels})
    assert not missing, missing
    assert "author-approved" not in clean
    assert "For the remaining four classes" not in clean
    assert r"\input{orbit3_enumerator_section.tex}" not in uncommented
    assert r"\label{eq:main-result-III-W23}" in clean
    assert r"\label{eq:supp-result-III-union}" in clean

    prior_round = ledger.get("revision_round", 1) - 1
    previous_source = REVIEW / f"archive/round{prior_round}/supplementary-revised.tex"
    style_review = {}
    if previous_source.is_file() and ledger.get("revision_round") in (2, 3):
        previous = re.sub(r"(?m)(?<!\\)%.*$", "",
                          previous_source.read_text(encoding="utf-8"))
        display_pattern = (r"\\begin\{(equation\*?|align\*?|gather\*?|multline\*?)\}"
                           r".*?\\end\{\1\}|\\\[.*?\\\]")
        def display_blocks(source):
            return [m.group(0) for m in re.finditer(display_pattern, source, re.S)]
        before, after = display_blocks(previous), display_blocks(uncommented)
        assert before == after, "A display formula changed during the prose revision"
        style_review = {"round": ledger["revision_round"],
                        "previous_round_sha256": sha(previous_source),
                        "display_math_blocks_preserved": len(after)}

    terms = [
        "Setting and proof outline", "Shared bit, Pauli",
        "Proof dependencies.", "From an encoder to the finite certificate.",
        "Restatement of main-text Result III",
        "Supplementary refinement of Result III",
        "Added certificate packages and repository entry points",
        "Lean declarations and verification records",
        "The auxiliary orbit-2 characteristic",
        "The six rational dual certificates in",
        "640 unsigned classes", "To eliminate the residual",
    ]
    QA.mkdir(parents=True, exist_ok=True)
    report = {"schema": 1, "main_unchanged": True, "original_supplementary_unchanged": True,
              "changes": len(ledger["changes"]), "clean_label_count": len(labels),
              "unresolved_clean_source_references": missing,
              "style_review": style_review, "documents": {}}
    for stem in ("supplementary", "supplementary-marked"):
        log = (BUILD / (stem + ".log")).read_text(encoding="utf-8", errors="replace")
        problems = [s for s in log.splitlines() if
            "undefined" in s.lower() or "multiply defined" in s.lower()
            or "LaTeX Error" in s or "Missing character" in s]
        assert not problems, (stem, problems)
        boxes = re.findall(r"Overfull \\hbox \(([^)]+)\).*", log)
        assert not boxes, (stem, boxes)
        source = BUILD / (stem + ".pdf")
        reader = PdfReader(source)
        pdf = pdfplumber.open(source)
        texts = [p.extract_text() or "" for p in pdf.pages]
        anchors = {term: [i + 1 for i, s in enumerate(texts) if term in s] for term in terms}
        # Body occurrences, excluding the table of contents. Inspect each
        # relevant page and its continuation for long newly inserted tables.
        selected = {1}
        for term, matches in anchors.items():
            if matches:
                page = matches[-1]
                selected.add(page)
                selected.add(min(page + 1, len(pdf.pages)))
        selected.add(len(pdf.pages))
        red = blue = 0
        outside = []
        for n, page in enumerate(pdf.pages, 1):
            for c in page.chars:
                color = c.get("non_stroking_color")
                red += color == (1, 0, 0)
                blue += color == (0, 0, 1)
                # A page-edge check, separate from the stricter TeX margin warnings.
                if c["x0"] < 8 or c["x1"] > page.width - 8:
                    outside.append(n)
        pdf.close()
        if stem.endswith("marked"):
            assert red > 200 and blue > 2000, (red, blue)
            assert "Deleted text" in texts[0] and "Added text" in texts[0]
            assert "Supplementary Materials" in texts[0], "Detached markup legend"
        assert not outside, (stem, sorted(set(outside)))
        images = []
        for n in sorted(selected):
            prefix = QA / f"{stem}-{n:03d}"
            subprocess.run(["pdftoppm", "-f", str(n), "-l", str(n), "-singlefile",
                            "-scale-to", "1250", "-png", str(source), str(prefix)],
                           stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, check=True)
            images.append((n, prefix.with_suffix(".png")))
        # Contact sheets let the reviewer see section transitions together;
        # the full-resolution page PNGs remain available for close inspection.
        for start in range(0, len(images), 6):
            group = images[start:start + 6]
            sheet = Image.new("RGB", (1530, 1380), "#dadada")
            draw = ImageDraw.Draw(sheet)
            for k, (n, filename) in enumerate(group):
                im = Image.open(filename).convert("RGB")
                im.thumbnail((490, 635))
                x, y = 10 + (k % 3) * 510, 25 + (k // 3) * 690
                sheet.paste(im, (x, y))
                draw.text((x, y - 18), f"{stem}, page {n}", fill="black")
            sheet.save(QA / f"{stem}-sheet-{start // 6 + 1}.png")
        report["documents"][stem] = {
            "pages": len(reader.pages), "sha256": sha(source), "anchors": anchors,
            "overfull_boxes": boxes, "characters_at_page_edge": sorted(set(outside)),
            "red_characters": red, "blue_characters": blue,
            "rendered_review_pages": sorted(selected),
            "reference_or_glyph_errors": problems,
        }
    (BUILD / "review-checks.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
