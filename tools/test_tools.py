"""Offline tests of the table extractor, the Lean generator and the source list. No PDF tool, no network."""
import json, pathlib, unittest

import check, extract, fetch, gen_lean

ROOT = pathlib.Path(__file__).resolve().parent.parent
RATES = [5, 9, 12, 15, 19, 23, 27, 31, 35]


def scale_text(step=100):
    lines = []
    for i, rate in enumerate(RATES):
        lo = f'{i * step},00'
        hi = 'en adelante' if i == 8 else f'{(i + 1) * step},00'
        lines.append(f'{lo} {hi} {i},50 {rate} {lo}')
    return '\n'.join(lines) + '\n'


class Extract(unittest.TestCase):
    def test_centavos(self):
        self.assertEqual(extract.centavos('1.749.901,45'), 174990145)
        self.assertEqual(extract.centavos('0,00'), 0)

    def test_scale_rows(self):
        rows = extract.scale_rows('ENERO\n0,00 126.697,64 0,00 5 0,00\n126.697,64 en adelante 6.334,88 9 126.697,64\n')
        self.assertEqual(rows, [[0, 12669764, 0, 5], [12669764, None, 633488, 9]])

    def test_scale_row_excess_must_repeat_lower_limit(self):
        with self.assertRaises(ValueError):
            extract.scale_rows('0,00 126.697,64 0,00 5 1,00\n')

    def test_check_scales(self):
        tables = extract.check_scales('t', extract.scale_rows(scale_text() + scale_text(50)))
        self.assertEqual(len(tables), 2)
        self.assertEqual([r[3] for r in tables[1]], RATES)
        with self.assertRaises(ValueError):
            extract.check_scales('t', extract.scale_rows(scale_text())[:8])

    def test_check_scales_rejects_bands_that_do_not_join(self):
        rows = extract.scale_rows(scale_text())
        rows[3][0] += 1
        with self.assertRaises(ValueError):
            extract.check_scales('t', rows)

    def test_deductions(self):
        text = 'a) 4.507.505,52\n1. 4.245.166,13\n2. 2.140.852,77\n2.1 4.281.705,53\n15.776.269,32\n18.030.022,08\n21.636.026,50\n\fmonthly 1,00'
        d = extract.deductions_text('t', text)
        self.assertEqual(d['mni'], 450750552)
        self.assertEqual(d['hijoIncapacitado'], 428170553)
        self.assertEqual(d['especial2'], 2163602650)
        with self.assertRaises(ValueError):
            extract.deductions_text('t', '1,00 2,00')

    def test_mono_rows(self):
        text = '\n'.join(f'{c} $ {i + 1},00 Hasta 30 m2 Hasta 3330 Kw $ 2,00 $ 3,00 $ 4,00 $ 5,00 $ 6,00 $ 7,00 $ 17,00 $ 18,00'
                         for i, c in enumerate('ABCDEFGHIJK')) + '\nReferencias $ 9,00'
        rows = extract.mono_rows(text)
        self.assertEqual(list(rows), list('ABCDEFGHIJK'))
        self.assertEqual(rows['K']['ingresos'], 1100)
        self.assertEqual(rows['A']['totalVenta'], 1800)
        with self.assertRaises(ValueError):
            extract.mono_rows(text.replace('K $ 11,00', 'K 11,00'))

    def test_html_rows(self):
        page = '<table><tr><td> A </td><!-- <td>x</td> --><td>$12.009.410,45</td></tr><tr><td>B</td><td>$1,00</td></tr></table>'
        self.assertEqual(extract.html_rows(page).split('\n')[1:], ['A | $12.009.410,45 |', 'B | $1,00 |'])

    def test_pj_rows(self):
        text = ('Pagarán $\n$ 0,00 $ 34.703.523,08 $ 0,00 25% $ 0,00\n$ 34.703.523,08 $ 347.035.230,79 $ 8.675.880,77 30% $ 34.703.523,08\n'
                '$ 347.035.230,79 En adelante $102.375.393, 08 35% $ 347.035.230,79\n')
        rows = extract.pj_rows('t', text)
        self.assertEqual(rows[2], [34703523079, None, 10237539308, 35])
        self.assertEqual(rows[0], [0, 3470352308, 0, 25])
        with self.assertRaises(ValueError):
            extract.pj_rows('t', text.replace('30%', '31%'))

    def test_jubilados(self):
        text = ('251/2025 27/6/2025 Jul-25 309.294,79 8 1 2.474.358.32 Julio 16.115.490.48\n'
                '359/2025 27/11/2025 dic 25 340.879,59 8 1 2.727.036,72 Diciembre 29.194.257,68\n')
        rows = extract.jubilados_text('t', text)
        self.assertEqual(rows[0], {'resolucion': '251/2025', 'hmg': 30929479, 'producto': 247435832, 'acumulado': 1611549048})
        self.assertEqual(rows[1]['acumulado'], 2919425768)
        with self.assertRaises(ValueError):
            extract.jubilados_text('t', 'nothing here')


class Generate(unittest.TestCase):
    def test_scale(self):
        self.assertEqual(gen_lean.scale([[0, 10, 0, 5], [10, None, 1, 9]]), '[⟨0, 0, 5⟩, ⟨10, 1, 9⟩]')

    def test_ipc(self):
        text = gen_lean.ipc_lean({'2024-12': 76940075, '2016-12': 1000000})
        self.assertIn('  | 201612 => 1000000\n  | 202412 => 76940075\n  | _ => 0', text)
        self.assertIn('def ipcLast : Nat := 202412', text)

    def test_generated_files_are_current(self):
        tables = ROOT / 'data' / 'tables.json'
        if not tables.exists():
            self.skipTest('data/tables.json not built')
        d = json.loads(tables.read_text(encoding='utf-8'))
        for name, text in [('Ipc.lean', gen_lean.ipc_lean(d['ipc'])), ('Ganancias.lean', gen_lean.ganancias_lean(d)),
                           ('Jubilados.lean', gen_lean.jubilados_lean(d['jubilados'])),
                           ('Sociedades.lean', gen_lean.sociedades_lean(d['art73'])),
                           ('Monotributo.lean', gen_lean.monotributo_lean(d['monotributo']))]:
            self.assertEqual((ROOT / 'ArTax' / 'Data' / name).read_text(encoding='utf-8'), text, name)


class Check(unittest.TestCase):
    def test_forbidden_ignores_comments(self):
        self.assertEqual(check.forbidden('/-! no sorry here -/\ntheorem t : True := trivial -- sorry\n'), [])
        self.assertEqual(check.forbidden('theorem t : False := by sorry\naxiom a : False'), ['axiom', 'sorry'])
        self.assertEqual(check.forbidden('theorem t : 1 = 1 := by native_decide'), ['native_decide'])
        self.assertEqual(check.forbidden('theorem t : 1 = 1 := by decide +native\nopaque x : Nat'), ['+native', 'opaque'])
        self.assertEqual(check.forbidden('set_option debug.skipKernelTC true'), ['skipKernelTC'])

    def test_theorem_names(self):
        text = 'namespace A.B\n/-- theorem fake -/\ntheorem t1 : True := trivial\ntheorem C.t2 : True := trivial\nend A.B\n@[simp] protected theorem t3 : True := trivial\n'
        self.assertEqual(check.theorem_names(text), ['A.B.t1', 'A.B.C.t2', 't3'])

    def test_axioms_used(self):
        out = "'A.b' depends on axioms: [propext, Quot.sound]\n'A.c' does not depend on any axioms\n'A.d' depends on axioms: [sorryAx]"
        self.assertEqual(check.axioms_used(out), {'propext', 'Quot.sound', 'sorryAx'})


class Sources(unittest.TestCase):
    def test_list(self):
        paths = [p for p, _u, _d in fetch.SOURCES]
        self.assertEqual(len(paths), len(set(paths)))
        self.assertTrue(all(u.startswith('https://') for _p, u, _d in fetch.SOURCES))

    def test_sources_md(self):
        text = fetch.sources_md([('a/b.pdf', 'https://x/b.pdf', 'A table', 'ff')])
        self.assertIn('| sources/a/b.pdf | ff | <https://x/b.pdf> | A table |', text)


if __name__ == '__main__':
    unittest.main()
