"""Offline tests for gen_refs.py, built on small inline fixtures.

They do not read sources/: each test feeds a few lines shaped like the InfoLEG pages and checks one step of the
pipeline (HTML to lines, article splitting, repeal notes, dates, citation resolution, flag finding, Lean emission).

Run from tools/: python -B -m unittest -q test_gen_refs
"""
import unittest

import gen_refs as g


HTML = (
    "<html><head><script>var x = 1;</script></head><body>"
    "<p>ARTICULO 1&ordm; &mdash; Texto\n uno.</p><p>a) inciso <b>a</b>.</p>"
    "<br>ARTICULO 2 &mdash; (Art&iacute;culo derogado por art. 3 de la Ley N&deg; 27.000 B.O. 5/1/2020)</body></html>"
)


class HtmlTest(unittest.TestCase):
    def test_lines(self):
        lines = g.html_to_lines(HTML)
        self.assertEqual(lines[0], "ARTICULO 1º — Texto uno.")
        self.assertEqual(lines[1], "a) inciso a.")
        self.assertTrue(lines[2].startswith("ARTICULO 2 — (Artículo derogado"))
        self.assertNotIn("var x", " ".join(lines))


class DateTest(unittest.TestCase):
    def test_parse(self):
        self.assertEqual(g.parse_date("08/07/2024"), 20240708)
        self.assertEqual(g.parse_date("1/12/2022"), 20221201)
        self.assertEqual(g.parse_date("19/1/2004"), 20040119)
        self.assertEqual(g.parse_date("29/12/98"), 19981229)

    def test_invalid(self):
        self.assertIsNone(g.parse_date("31/02/2020"))
        self.assertIsNone(g.parse_date("12/13/2020"))

    def test_next_day(self):
        self.assertEqual(g.next_day(20191231), 20200101)
        self.assertEqual(g.next_day(20240228), 20240229)
        self.assertEqual(g.next_day(20230228), 20230301)


class NoteTest(unittest.TestCase):
    def test_article_repeal(self):
        n = g.parse_notes("ARTÍCULO 27.- (Artículo derogado por art. 70 inciso b) de la Ley N° 27.743 B.O. 08/07/2024. "
                          "Vigencia: a partir del día de su publicación en el Boletín Ofical y surtirá efecto a partir del "
                          "año fiscal 2024)")
        self.assertEqual(len(n), 1)
        self.assertEqual(n[0]["unit"], "artículo")
        self.assertEqual(n[0]["action"], "derogado")
        self.assertEqual(n[0]["norm"], "Ley 27.743")
        self.assertEqual(n[0]["bo"], 20240708)
        self.assertEqual(n[0]["from"], 20240708)

    def test_next_day_vigencia_and_decree(self):
        n = g.parse_notes("Texto. (Inciso sustituido por art. 1° del Decreto N° 1334/98 B.O. 16/11/1998. Vigencia: "
                          "el día siguiente al de su publicación en el Boletín Oficial)")
        self.assertEqual(n[0]["unit"], "inciso")
        self.assertEqual(n[0]["action"], "sustituido")
        self.assertEqual(n[0]["norm"], "Decreto 1334/98")
        self.assertEqual(n[0]["from"], 19981117)

    def test_no_vigencia_keeps_publication_and_says_so(self):
        n = g.parse_notes("(Título V derogado por art. 1°, inciso a), punto 4 de la Ley N° 25.865 B.O. 19/1/2004.)")
        self.assertEqual(n[0]["unit"], "título")
        self.assertEqual(n[0]["bo"], 20040119)
        self.assertEqual(n[0]["date_basis"], "B.O.")

    def test_deferred_effects_take_the_cap(self):
        n = g.parse_notes("(Título V derogado por art. 1°, inciso a), punto 4 de la Ley N° 25.865 B.O. 19/1/2004. "
                          "Vigencia: a partir del día de su publicación en el Boletín Oficial. Las disposiciones contenidas "
                          "en el Título I de la norma de referencia surtirán efectos a partir de la fecha que disponga el "
                          "Poder Ejecutivo nacional, la que no podrá superar los ciento ochenta (180) días contados desde "
                          "la fecha de publicación oficial.)")
        self.assertEqual(n[0]["from"], 20040718)

    def test_nota_infoleg_is_not_an_amendment(self):
        self.assertEqual(g.parse_notes("(Nota Infoleg: por art. 2° de la Ley N° 27.432 B.O. 29/12/2017 se prorroga)"), [])


ARTS = [
    "TITULO I",
    "ARTICULO 1º — Rige el artículo 3 y el inciso b) del artículo 2.",
    "ARTÍCULO 2.- Son sujetos:",
    "a) uno;",
    "b) (Inciso derogado por art. 5 de la Ley N° 26.000 B.O. 2/1/2010)",
    "c) los del inciso b) de este artículo.",
    "Artículo...: Sin número, según el artículo 4 de la ley 11.683.",
    "TITULO II",
    "ARTICULO 3 — (Artículo derogado por art. 9 de la Ley N° 25.000 B.O. 3/3/2003)",
    "ARTICULO 4 bis — Texto con \"Artículo 9. — citado\" en otra línea.",
    "\"Artículo 9. — cita del artículo 3 dentro de una cita\"",
]


class SplitTest(unittest.TestCase):
    def test_split(self):
        arts = g.split_articles(ARTS)
        self.assertEqual([a.num for a in arts], ["1", "2", "2 s/n 1", "3", "4 bis"])
        self.assertEqual(arts[1].lines[2], "b) (Inciso derogado por art. 5 de la Ley N° 26.000 B.O. 2/1/2010)")
        self.assertEqual(arts[3].title, "II")

    def test_titled_numbering(self):
        arts = g.split_articles(["TITULO III", "ARTICULO 1 — a", "TITULO VI", "ARTICULO 1 — b"], titled=True)
        self.assertEqual([a.key for a in arts], ["III:1", "VI:1"])

    def test_repeals(self):
        arts = g.split_articles(ARTS)
        self.assertIsNone(g.article_repeal(arts[0]))
        self.assertEqual(g.article_repeal(arts[3])["bo"], 20030303)
        self.assertEqual(set(g.inciso_repeals(arts[1])), {"b"})

    def test_title_repeal(self):
        reps = g.title_repeals(["TITULO V", "RESPONSABLES", "(Título V derogado por art. 1 de la Ley N° 25.865 "
                                "B.O. 19/1/2004.)", "TITULO VI"])
        self.assertEqual(reps["V"]["bo"], 20040119)


class CiteTest(unittest.TestCase):
    def kinds(self, text, own="lig"):
        return [(c["kind"], c.get("statute"), c["article"], c.get("inciso")) for c in g.find_citations(text, own)]

    def test_same_statute(self):
        self.assertEqual(self.kinds("previsto en el artículo 32 de esta ley."), [("same", "lig", "32", None)])
        self.assertEqual(self.kinds("según el tercer párrafo del artículo 32."), [("same", "lig", "32", None)])

    def test_list(self):
        self.assertEqual(self.kinds("los artículos 27, 32 y 110 de la presente ley"),
                         [("same", "lig", "27", None), ("same", "lig", "32", None), ("same", "lig", "110", None)])

    def test_list_comma_y(self):
        self.assertEqual([c["article"] for c in g.find_citations("a que se refieren los artículos 13, 32, y 35.", "iva")],
                         ["13", "32", "35"])

    def test_inciso(self):
        self.assertEqual(self.kinds("los incisos x) e y) del artículo 26"),
                         [("same", "lig", "26", "x"), ("same", "lig", "26", "y")])

    def test_other_act(self):
        self.assertEqual(self.kinds("en los términos del artículo 2° de la ley 24.467 y sus modificatorias"),
                         [("other", None, "2", None)])
        self.assertEqual(self.kinds("comprendidos en los artículos 726, 727 del Código Alimentario Argentino"),
                         [("other", None, "726", None), ("other", None, "727", None)])
        self.assertEqual(self.kinds("del artículo 49 de la Ley de Impuesto a las Ganancias, texto según decreto 649"),
                         [("ambiguous", None, "49", None)])

    def test_cross_statute(self):
        self.assertEqual(self.kinds("conforme el artículo 45 de la ley 11.683, texto ordenado en 1998", own="iva"),
                         [("cross", "ley11683", "45", None)])
        self.assertEqual(self.kinds("el artículo 26 de la Ley de Impuesto a las Ganancias, texto ordenado en 2019",
                                    own="iva"), [("cross", "lig", "26", None)])

    def test_siguientes(self):
        self.assertEqual(self.kinds("previstas en los artículos 33 y siguientes de la Ley Nº 11.683, texto ordenado en 1998",
                                    own="iva"), [("cross", "ley11683", "33", None)])

    def test_heading_not_body(self):
        arts = g.split_articles(["ARTÍCULO 32.- (Artículo derogado por art. 70 inciso c) de la Ley N° 27.743 "
                                 "B.O. 08/07/2024.)", "CONCEPTO DE RESIDENCIA", "ARTÍCULO 33.- Texto."])
        self.assertEqual(g.article_repeal(arts[0])["bo"], 20240708)

    def test_old_ordering_is_ambiguous(self):
        self.assertEqual(self.kinds("los artículos 35 y 36 de la Ley Nº 11.683 texto ordenado en 1978 y sus modif",
                                    own="iva"), [("ambiguous", None, "35", None), ("ambiguous", None, "36", None)])

    def test_bare_ley_is_ambiguous(self):
        self.assertEqual(self.kinds("los valores del artículo 98 de la ley, no comprendidos"),
                         [("ambiguous", None, "98", None)])

    def test_unnumbered_and_reglamentacion(self):
        self.assertEqual(self.kinds("el artículo sin número a continuación del artículo 28"), [])
        self.assertEqual(self.kinds("el artículo 176 de la reglamentación"), [("other", None, "176", None)])


class AmendingTest(unittest.TestCase):
    def test_amending_clause_is_ambiguous(self):
        cs = g.find_citations("Sustitúyese el artículo 5 por el siguiente:", "x")
        self.assertEqual([c["kind"] for c in cs], ["ambiguous"])


    def test_plural_and_embedded(self):
        self.assertEqual([c["kind"] for c in g.find_citations("Deróganse los artículos 7, 8 y 9.", "x")],
                         ["ambiguous"] * 3)
        self.assertEqual([n for n, _ in g.own_lines(["Sustitúyese el artículo 5 por el siguiente:",
                                                     "Artículo 5: según el artículo 9."])], [0])

    def test_list_interrupted_by_inciso(self):
        cs = g.find_citations("permanecerán vigentes los artículos 27, 28 inc. 1, 585 y 590 de la Ley 2372 y sus", "x")
        self.assertEqual({c["kind"] for c in cs}, {"other"})

    def test_number_already_tied_to_other_act(self):
        cs = g.find_citations("los artículos 97 o 98 de la Constitución Nacional o si se han producido las "
                              "circunstancias del artículo 98 o si", "x")
        self.assertEqual([c["kind"] for c in cs], ["other", "other", "ambiguous"])


    def test_bare_citation_right_after_other_act(self):
        cs = g.find_citations("la mayoría prevista en el artículo 97 de la Constitución Nacional o si se han producido "
                              "las circunstancias del artículo 98 o si", "x")
        self.assertEqual([c["kind"] for c in cs], ["other", "ambiguous"])

    def test_list_introduced_by_other_act(self):
        cs = g.find_citations("las siguientes disposiciones del CODIGO PROCESAL CIVIL: artículo 3, artículos 7 y 8", "x")
        self.assertEqual({c["kind"] for c in cs}, {"ambiguous"})


class CorpusTest(unittest.TestCase):
    LOG = ("@@aaa\nLaw: Ley 2\nKind: law\nIn-force: 2020-05-01\n\n##\nD\tact/art-003.md\nM\tact/art-001.md\n"
           "@@bbb\nLaw: Ley 1\nKind: law\nIn-force: 2000-01-01\n\n##\nA\tact/art-001.md\nA\tact/art-003.md\n"
           "A\tact/README.md\n")

    def test_events(self):
        ev = g.corpus_events(self.LOG)
        self.assertEqual(ev["act/art-003.md"], [(20200501, "D", "Ley 2", "law"), (20000101, "A", "Ley 1", "law")])
        self.assertNotIn("act/README.md", ev)

    def test_flags(self):
        ev = g.corpus_events(self.LOG)
        texts = {"act/art-001.md": "# Art. 1\nSegún el artículo 3 y el artículo 2 de la ley 1.234.\n"}
        flags, amb = g.corpus_flags(None, texts, ev)
        self.assertEqual([(f["citing"], f["target"]) for f in flags], [("act/art-001.md", "act/art-003.md")])
        self.assertEqual(flags[0]["target_hist"], [(20200501, False), (20000101, True)])
        self.assertEqual(flags[0]["citing_hist"], [(20200501, True), (20000101, True)])

    def test_unit_key(self):
        self.assertEqual(g.unit_key("5"), "art-005")
        self.assertEqual(g.unit_key("245 bis"), "art-245-bis")
        self.assertEqual(g.unit_key("2671"), "art-2671")


class FlagTest(unittest.TestCase):
    def test_flags(self):
        st = g.Statute("tst", "Ley de prueba", ARTS, base=19900101)
        flags, ambiguous = g.find_flags({"tst": st})
        got = sorted((f["citing"], f["target"]) for f in flags)
        self.assertEqual(got, [("tst art. 1", "tst art. 2 inc. b)"), ("tst art. 1", "tst art. 3"),
                               ("tst art. 2", "tst art. 2 inc. b)")])
        self.assertEqual(sorted((f["target"], f["repeal"]["bo"]) for f in flags),
                         [("tst art. 2 inc. b)", 20100102), ("tst art. 2 inc. b)", 20100102), ("tst art. 3", 20030303)])

    def test_title_citation(self):
        lines = ["TITULO V", "(Título V derogado por art. 1 de la Ley N° 25.865 B.O. 19/1/2004.)", "TITULO VI",
                 "ARTICULO 36 — salvo los responsables comprendidos en el Título V, que usen la opción."]
        flags, _ = g.find_flags({"t": g.Statute("t", "x", lines, base=19970101)})
        self.assertEqual([(f["citing"], f["target"]) for f in flags], [("t art. 36", "t tít. V")])

    def test_epigraph_not_body(self):
        arts = g.split_articles(["ARTICULO 10 — (Artículo derogado por art. 245 de la Ley N° 27.430 B.O. 29/12/2017)",
                                 "Declaración jurada y liquidación administrativa del tributo", "ARTICULO 11 — Texto."])
        self.assertIsNotNone(g.article_repeal(arts[0]))

    def test_quoted_lines_ignored(self):
        st = g.Statute("tst", "Ley de prueba", ARTS, base=19900101)
        flags, _ = g.find_flags({"tst": st})
        self.assertFalse(any(f["citing"].startswith("tst art. 4") for f in flags))


class LeanTest(unittest.TestCase):
    def test_emit(self):
        flags = [{"id": "F1", "citing": "x art. 1", "target": "x art. 3", "quote": "artículo 3",
                  "citing_since": 19900101, "target_since": 19900101, "repeal": {"from": 20030303}}]
        src = g.emit_lean(flags, 20261124, "Tax", "test")
        self.assertIn("namespace ArLegal.Generated.Tax", src)
        self.assertIn("⟨[(19900101, true)], [(20030303, false), (19900101, true)]⟩", src)
        self.assertIn("theorem certified : flags.map (·.certified 20261124) = [true] := by decide", src)
        self.assertNotIn("sorry", src)


if __name__ == "__main__":
    unittest.main()
