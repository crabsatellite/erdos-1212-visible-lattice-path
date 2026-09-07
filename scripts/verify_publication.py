"""Verify this public package's recorded bytes, without running a proof."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
manifest=json.loads((root/'certificate/manifest.json').read_text(encoding='utf-8'))
for item in manifest['files']:
    p=(root/item['path']).resolve()
    if not p.is_relative_to(root):raise SystemExit('unsafe manifest path')
    with p.open('rb') as f: actual=hashlib.file_digest(f,'sha256').hexdigest()
    if actual!=item['sha256']:raise SystemExit('hash mismatch: '+item['path'])
actual_sources={p.relative_to(root).as_posix() for p in (root/'kernel').rglob('*.lean')}
expected={x['path'] for x in manifest['files'] if x['path'].endswith('.lean')}
if actual_sources!=expected:raise SystemExit('Lean source inventory differs')
print('Public artifact inventory passed; no proof command was executed.')
