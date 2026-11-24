"""Check the whole project: no unproved statement, a clean build, the axioms used, and the calculator's answers.

Run from the project folder: python tools/check.py. Needs lake (elan) on PATH; the first build takes about two
minutes, later ones seconds.
"""
import pathlib, re, shutil, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ALLOWED_AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}
# input line, expected output line of the artax calculator
GOLDEN = [
    ('G;2025;e;40000000;-;0;0', 'mni=4507505.52;cargas=0.00;especial=21636026.50;doceava=2178627.67;'
     'deducciones=28322159.69;imponible=11677840.31;impuesto=1571326.12'),
    ('G;2025;e;100000000;4507505.52;0;0', 'mni=4507505.52;cargas=4245166.13;especial=21636026.50;doceava=2532391.51;'
     'deducciones=32921089.66;imponible=67078910.34;impuesto=17711693.35'),
    ('M;202608;s;81924660.37;0', 'categoria=H;limite=81924660.37;cuota=522706.68;anual=6272480.16'),
    ('M;202608;s;81924660.38;0', 'categoria=I;limite=91699761.90;cuota=963747.86;anual=11564974.32'),
    ('M;202608;v;126610838.76;0', 'categoria=excluido'),
    ('B;2025;1346548155.99;384728044.57', 'mni=384728044.57;casaExenta=1346548155.99;gravados=384728044.57;base=0.00;'
     'impuesto=0.00'),
    ('B;2025;1346548156.00;384728044.57', 'mni=384728044.57;casaExenta=1346548155.99;gravados=1731276200.57;'
     'base=1346548156.00;impuesto=13048555.97'),
    ('X;1', 'ERR;X;1'),
]


def strip_comments(text):
    text = re.sub(r'(?s)/-.*?-/', '', text)
    return re.sub(r'--.*', '', text)


def forbidden(text):
    """The words in a Lean source, outside comments, that would mean a statement is not proved by the kernel."""
    pattern = r'\b(?:sorry|native_decide|axiom|unsafe|implemented_by|opaque|skipKernelTC|ofReduceBool)\b|\+native'
    return sorted(set(re.findall(pattern, strip_comments(text))))


def theorem_names(text):
    """The full names of the theorems stated in a Lean source."""
    spaces, names = [], []
    for line in strip_comments(text).splitlines():
        m = re.match(r'\s*namespace\s+(\S+)', line)
        if m:
            spaces.append(m.group(1))
            continue
        m = re.match(r'\s*end\s+(\S+)', line)
        if m and spaces and spaces[-1] == m.group(1):
            spaces.pop()
            continue
        m = re.match(r'\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?theorem\s+(\S+)', line)
        if m:
            names.append('.'.join(spaces + [m.group(1)]))
    return names


def lean_files():
    return sorted(p for d in ('ArTax', 'ArLegal') for p in (ROOT / d).rglob('*.lean')) + \
        [ROOT / 'ArTax.lean', ROOT / 'ArLegal.lean']


def axioms_used(output):
    """The axiom names in the output of #print axioms."""
    names = set()
    for block in re.findall(r'depends on axioms: \[([^\]]*)\]', output):
        names.update(n.strip() for n in block.split(',') if n.strip())
    return names


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, encoding='utf-8', errors='replace', **kw)


def main():
    bad = {str(p.relative_to(ROOT)): forbidden(p.read_text(encoding='utf-8')) for p in lean_files()}
    bad = {k: v for k, v in bad.items() if v}
    if bad:
        print('unproved or unchecked statements:', bad)
        return 1
    if not shutil.which('lake'):
        print('lake not found: install elan to build the proofs')
        return 1
    build = run(['lake', 'build'], timeout=1500)
    if build.returncode:
        print(build.stdout[-4000:], build.stderr[-2000:])
        return 1
    names = [n for p in lean_files() for n in theorem_names(p.read_text(encoding='utf-8'))]
    listing = ROOT / 'tools' / 'out' / 'AllAxioms.lean'
    listing.parent.mkdir(exist_ok=True)
    listing.write_text('import ArTax\nimport ArLegal\n' + ''.join(f'#print axioms {n}\n' for n in names), encoding='utf-8')
    out = run(['lake', 'env', 'lean', 'tools/out/AllAxioms.lean'], timeout=900)
    text = out.stdout + out.stderr
    extra = axioms_used(text) - ALLOWED_AXIOMS
    answered = len(re.findall(r'depends on axioms|does not depend on any axioms', text))
    if out.returncode or extra or answered != len(names):
        print(f'axioms: {answered} of {len(names)} theorems answered, outside the standard three: {sorted(extra)}', text[-3000:])
        return 1
    exe = ROOT / '.lake' / 'build' / 'bin' / ('artax.exe' if sys.platform == 'win32' else 'artax')
    got = subprocess.run([str(exe)], input='\n'.join(i for i, _ in GOLDEN) + '\n', capture_output=True, text=True,
                         encoding='utf-8', timeout=60).stdout.split('\n')
    wrong = [(i, e, g) for (i, e), g in zip(GOLDEN, got) if e != g.strip()]
    if wrong or len(got) < len(GOLDEN):
        print('artax answers differ:', wrong)
        return 1
    print(f'{len(lean_files())} Lean files, build clean, {len(names)} theorems on standard axioms, {len(GOLDEN)} calculator cases')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
