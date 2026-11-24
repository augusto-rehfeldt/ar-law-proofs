"""Read the official tables in sources/ and write data/tables.json.

Sources: ARCA's published PDFs of the art. 30 deductions and the art. 94 scale (Ley de Impuesto a las
Ganancias), ARCA's Monotributo category tables, and INDEC's national CPI (IPC, base December 2016) as served
by datos.gob.ar. Amounts are kept as integer centavos. Needs pdftotext (poppler) on PATH.
"""
import html, json, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ARCA = ROOT / 'sources' / 'arca'
NUM = r'\d{1,3}(?:\.\d{3})*,\d{2}'


def centavos(s):
    return int(s.replace('.', '').replace(',', ''))


def pdf_text(name, mode='-layout'):
    out = subprocess.run(['pdftotext', mode, str(ARCA / name), '-'], capture_output=True, check=True)
    return out.stdout.decode('latin-1')


def scale_rows(text):
    """Rows (from, to, fixed, rate) of an art. 94 table, in order; to is None for the last band."""
    rows = []
    # one printed line per band: from, to, fixed sum, rate, "sobre el excedente de" (which repeats from)
    for m in re.finditer(rf'(?m)^({NUM}) ({NUM}|en adelante) ({NUM}) (\d{{1,2}}) ({NUM})\s*$', text):
        lo, hi, fixed, rate, excess = m.groups()
        if excess != lo:
            raise ValueError(f'excess {excess} is not the lower limit {lo}')
        rows.append([centavos(lo), None if hi.startswith('en') else centavos(hi), centavos(fixed), int(rate)])
    return rows


def check_scales(name, rows):
    if not rows or len(rows) % 9:
        raise ValueError(f'{name}: {len(rows)} rows is not a multiple of 9')
    tables = [rows[i:i + 9] for i in range(0, len(rows), 9)]
    for t in tables:
        if [r[3] for r in t] != [5, 9, 12, 15, 19, 23, 27, 31, 35] or t[0][0] != 0 or t[-1][1] is not None:
            raise ValueError(f'{name}: malformed scale {t}')
        if any(a[1] != b[0] for a, b in zip(t, t[1:])):
            raise ValueError(f'{name}: bands do not join {t}')
    return tables


def scale_tables(name):
    """The headline scale of a PDF, then the monthly cumulative scales that follow it (9 rows each)."""
    return check_scales(name, scale_rows(pdf_text(name, '-raw')))


def pj_rows(name, text):
    """The three rows (from, to, fixed, rate) of ARCA's art. 73 company scale."""
    text = re.sub(r'\$[ \t]*', '', text)
    text = re.sub(r',[ \t]+(\d{2})(?!\d)', r',\1', text)  # "102.375.393, 08" as printed in the 2024 table
    rows = []
    for m in re.finditer(rf'(?m)^({NUM}) ({NUM}|En adelante) ({NUM}) (\d{{2}})%? ({NUM})\s*$', text):
        lo, hi, fixed, rate, excess = m.groups()
        if excess != lo:
            raise ValueError(f'{name}: excess {excess} is not the lower limit {lo}')
        rows.append([centavos(lo), None if hi.startswith('En') else centavos(hi), centavos(fixed), int(rate)])
    if [r[3] for r in rows] != [25, 30, 35] or rows[0][0] != 0 or any(a[1] != b[0] for a, b in zip(rows, rows[1:])):
        raise ValueError(f'{name}: malformed company scale {rows}')
    return rows


DED_KEYS = ['mni', 'conyuge', 'hijo', 'hijoIncapacitado', 'especial1', 'especial1Nuevos', 'especial2']


def deductions_text(name, text):
    """The seven headline amounts of an art. 30 table (first page), in the order ARCA prints them."""
    nums = [centavos(x) for x in re.findall(NUM, text.split('\f')[0])]
    if len(nums) != 7:
        raise ValueError(f'{name}: expected 7 amounts, found {len(nums)}')
    d = dict(zip(DED_KEYS, nums))
    if not d['hijo'] < d['conyuge'] < d['mni'] < d['especial1'] < d['especial1Nuevos'] < d['especial2']:
        raise ValueError(f'{name}: amounts out of order {d}')
    return d


def deductions(name):
    return deductions_text(name, pdf_text(name, '-raw'))


# a peso amount whose decimal mark may be misprinted as a point ("2.474.358.32")
NUM2 = r'\d{1,3}(?:\.\d{3})*[.,]\d{2}'


def jubilados(name):
    return jubilados_text(name, pdf_text(name, '-raw'))


def jubilados_text(name, text):
    """The monthly rows of ARCA's table of the specific deduction for pensions (art. 30, eighth paragraph):
    the haber mínimo garantizado, eight times it as printed, and the printed running total."""
    rows = []
    for m in re.finditer(rf'(?m)^(\d+/\d{{4}}) \S+ .*?({NUM2}) 8 1 ({NUM2}) \S+ ({NUM2})\s*$', text):
        res, hmg, prod, acc = m.groups()
        rows.append({'resolucion': res, 'hmg': int(re.sub(r'\D', '', hmg)), 'producto': int(re.sub(r'\D', '', prod)),
                     'acumulado': int(re.sub(r'\D', '', acc))})
    if not rows:
        raise ValueError(f'{name}: no rows')
    return rows


MONO_KEYS = ['ingresos', 'alquileres', 'precioUnitario', 'impServicios', 'impVenta', 'sipa', 'obraSocial',
             'totalServicios', 'totalVenta']
MONO_ROW = re.compile(r'(?m)^[ \t|]*([A-K])[ \t|]+\$')


def mono_rows(text):
    """One row per category A to K: the nine peso amounts that follow the letter, up to the next row."""
    rows = {}
    starts = list(MONO_ROW.finditer(text))
    for m, nxt in zip(starts, starts[1:] + [None]):
        end = nxt.start() if nxt else text.find('Referencias', m.end())
        nums = [centavos(x) for x in re.findall(rf'\$\s*({NUM})', text[m.start():end if end > 0 else len(text)])]
        if len(nums) != 9:
            raise ValueError(f'category {m.group(1)}: {len(nums)} amounts')
        rows[m.group(1)] = dict(zip(MONO_KEYS, nums))
    if list(rows) != list('ABCDEFGHIJK'):
        raise ValueError(f'categories found: {list(rows)}')
    return rows


def html_rows(s):
    """An HTML table as text, one line per table row, cells separated by a bar."""
    s = re.sub(r'(?is)<(script|style).*?</\1>|<!--.*?-->', '', s)
    s = re.sub(r'(?is)<tr\b[^>]*>', '\x00', s)
    s = re.sub(r'(?i)</t[dh]>', ' | ', s)
    s = html.unescape(re.sub(r'(?s)<[^>]+>', '', s)).replace('\xa0', ' ')
    return '\n'.join(' '.join(r.split()) for r in s.split('\x00'))


def main():
    out = {
        'art94': {
            '2025-S1': scale_tables('Tabla-Art-94-LIG-enero-junio-2025.pdf'),
            '2025-S2': scale_tables('Tabla-Art-94-LIG-periodo-julio-diciembre-2025.pdf'),
            '2025': scale_tables('Tabla-Art-94-LIG-liquidacion-anual-y-final-2025.pdf'),
            '2026-S1': scale_tables('Tabla-Art-94-LIG-per-ene-a-jun-2026.pdf'),
            '2026-S2': scale_tables('Tabla-Art-94-LIG-per-jul-a-dic-2026.pdf'),
            '2026': scale_tables('Tabla-Art-94-LIG-liquidacion-anual-y-final-2026.pdf'),
        },
        'art30': {
            '2025-S1': deductions('Deducciones-personales-art-30-enero-junio-2025.pdf'),
            '2025-S2': deductions('Deducciones-personales-art-30-julio-diciembre-2025.pdf'),
            '2025': deductions('Deducciones-personales-art-30-liq-anual-2025.pdf'),
            '2026-S1': deductions('Deducciones-personales-art-30-ene-a-jun-2026.pdf'),
            '2026-S2': deductions('Deducciones-personales-art-30-jul-dic-2026.pdf'),
            '2026': deductions('Deducciones-personales-art-30-liq-anual-2026.pdf'),
        },
        'monotributo': {
            '2025-02': mono_rows(pdf_text('monotributo-categorias-febrero-julio-2025.pdf', '-raw')),
            '2025-08': mono_rows(pdf_text('monotributo-categorias-agosto-2025-enero-2026.pdf', '-raw')),
            '2026-02': mono_rows(pdf_text('monotributo-categorias-febrero-julio-2026.pdf', '-raw')),
            '2026-08': mono_rows(html_rows((ARCA / 'monotributo-categorias-agosto-2026.html').read_text(encoding='utf-8'))),
        },
    }
    out['jubilados'] = {'2025': jubilados('Deducciones-art-30-2025-Jubilados-HMG-2025.pdf'),
                        '2026': jubilados('Deducciones-art-30-2025-Jubilados-HMG-2026.pdf')}
    out['art73'] = {str(y): pj_rows(str(y), pdf_text(f'Ganancias-Escala-PJ-{y}.pdf', '-raw')) for y in range(2022, 2027)}
    ipc = json.loads((ROOT / 'sources' / 'indec' / 'ipc_nacional_nivel_general.json').read_text())['data']
    out['ipc'] = {d[:7]: round(v * 10000) for d, v in ipc}  # index values with four decimals, as integers
    (ROOT / 'data').mkdir(exist_ok=True)
    (ROOT / 'data' / 'tables.json').write_text(json.dumps(out, indent=1, sort_keys=True), encoding='utf-8')
    print({k: ({p: len(v) for p, v in out[k].items()} if k != 'ipc' else len(out[k])) for k in sorted(out)})


if __name__ == '__main__':
    main()
