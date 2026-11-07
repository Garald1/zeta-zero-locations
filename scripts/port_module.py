"""Port Lean files to the module system (required by Palomar for every .lean file in the
repository), following zeta-lab's pattern: a `module` header after the leading comments,
`import X` -> `public import X`, and `@[expose] public section` after the imports, so that
declarations and definition bodies stay visible to importing modules (needed by `decide +kernel`
on checkers defined elsewhere). Idempotent: files that already start with `module` are skipped.
Usage: python3 scripts/port_module.py FILE...
"""
import sys, re


def port(src):
    lines = src.split('\n')
    i = 0
    # leading ordinary comments (`/- ... -/`, `--`) and blank lines; not doc comments `/-!`, `/--`
    while i < len(lines):
        s = lines[i].strip()
        if s == '' or s.startswith('--'):
            i += 1
        elif s.startswith('/-') and not s.startswith('/-!') and not s.startswith('/--'):
            while '-/' not in lines[i]:
                i += 1
            i += 1
        else:
            break
    if i < len(lines) and lines[i].strip() == 'module':
        return None
    head, rest = lines[:i], lines[i:]
    # imports (possibly with blank lines between them)
    j = 0
    last = -1
    while j < len(rest):
        s = rest[j].strip()
        if s.startswith('import '):
            rest[j] = 'public ' + rest[j].lstrip()
            last = j
        elif s.startswith('public import ') or s.startswith('meta import '):
            last = j
        elif s != '':
            break
        j += 1
    if last >= 0:
        body = rest[:last + 1] + ['', '@[expose] public section'] + rest[last + 1:]
    else:
        body = ['@[expose] public section', ''] + rest
    return '\n'.join(head + ['module', ''] + body)


def port_files(fns):
    for fn in fns:
        src = open(fn).read()
        out = port(src)
        if out is not None:
            open(fn, 'w').write(out)


if __name__ == "__main__":
    port_files(sys.argv[1:])
