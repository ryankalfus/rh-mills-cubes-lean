#!/usr/bin/env python3
"""Copy the transitive local import cone of the given modules from SRC repo into DST dir (preserving paths).
Usage: vendor_cone.py SRC DST Module [Module...]   Prints local module list and external imports."""
import sys, re, os, shutil
src, dst, roots = sys.argv[1], sys.argv[2], sys.argv[3:]
imp = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.«»]+)', re.M)
def path(base, m): return os.path.join(base, m.replace('.', '/') + '.lean')
seen, ext, stack = set(), set(), list(roots)
while stack:
    m = stack.pop()
    if m in seen or m in ext: continue
    p = path(src, m)
    if not os.path.exists(p):
        ext.add(m); continue
    seen.add(m)
    stack.extend(imp.findall(open(p, encoding='utf-8').read()))
for m in sorted(seen):
    d = path(dst, m)
    os.makedirs(os.path.dirname(d), exist_ok=True)
    shutil.copyfile(path(src, m), d)
open(os.path.join(dst, 'MODULES.txt'), 'w').write('\n'.join(sorted(seen)) + '\n')
open(os.path.join(dst, 'EXTERNAL_IMPORTS.txt'), 'w').write('\n'.join(sorted(ext)) + '\n')
print(len(seen), 'local modules copied;', len(ext), 'external imports')
