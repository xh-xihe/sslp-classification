"""Package the source-bound, visually checked current SI review revision."""
import hashlib
import json
from pathlib import Path
import shutil
from zipfile import ZipFile,ZIP_DEFLATED

ROOT=Path(__file__).resolve().parents[2]
review=ROOT/'documents/20261003/revisions/si-review-20261003'
build=ROOT/'tmp/pdfs/supplementary-review-20261003'
output=ROOT/'output/pdf'
checks=json.loads((build/'review-checks.json').read_text(encoding='utf8'))
ledger=json.loads((review/'revision-ledger.json').read_text(encoding='utf8'))
assert checks['style_review']['round']==ledger['revision_round']==3
assert checks['changes']==len(ledger['changes'])
for stem,item in checks['documents'].items():
    assert hashlib.sha256((build/(stem+'.pdf')).read_bytes()).hexdigest()==item['sha256']
    assert not item['overfull_boxes'] and not item['reference_or_glyph_errors']
    assert not item['characters_at_page_edge']
archive=review/'archive/round2/pdf'
archive.mkdir(parents=True,exist_ok=True)
for filename in ('supplementary-20261003-revised.pdf','supplementary-20261003-marked.pdf',
                 'supplementary-20261003-review-package.zip'):
    old=output/filename
    saved=archive/filename
    if old.exists() and not saved.exists():
        shutil.copy2(old,saved)
output.mkdir(parents=True,exist_ok=True)
shutil.copy2(build/'supplementary.pdf',output/'supplementary-20261003-revised.pdf')
shutil.copy2(build/'supplementary-marked.pdf',output/'supplementary-20261003-marked.pdf')
shutil.copy2(build/'review-checks.json',review/'review-checks.json')
files={p.name:p for p in review.iterdir() if p.is_file()}
for name in ('main.tex','supplementary.tex','references.bib'):
    files['baseline/'+name]=ROOT/'documents/20261003'/name
for name in ('main.pdf','supplementary.pdf','supplementary-marked.pdf'):
    files[name]=build/name
with ZipFile(output/'supplementary-20261003-review-package.zip','w',ZIP_DEFLATED) as z:
    for name,path in sorted(files.items()):
        z.write(path,name)
print('PASS round-three review package:',checks['changes'],'changes,',
      checks['style_review']['display_math_blocks_preserved'],'display formulas preserved')
