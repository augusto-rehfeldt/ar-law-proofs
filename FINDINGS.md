# Findings to flag

Each item is a statement the Lean kernel checked (theorem named in brackets, under ArTax/) about the statute's
text or an official table. They are arithmetic facts about the rules as written and published. Whether a given
one is a defect, a policy choice or an opening for planning is a legal judgement this file does not make.
Amounts in pesos. Dead cross-references between statutes are listed separately in ArLegal/FINDINGS.md.

## 1. Cliffs: one centavo changes the tax by a large amount

| Where | What happens | Size | Theorem |
|---|---|---|---|
| Ganancias, art. 30 b) | A spouse whose net income of the year passes the art. 30 a) amount by one centavo stops being a deductible dependant | $ 1.609.625,49 more tax in 2025 for a taxpayer in the top band | Ganancias.spouse_cliff_2025, spouse_cliff_2026 |
| Ganancias, art. 30, pensions | A pensioner's other income passing the art. 30 a) amount by one centavo, or becoming liable to bienes personales for anything but a single home, swaps the specific deduction (8 haberes mínimos) for a) + c) 2 and its twelfth | $ 872.097,99 of deduction lost in 2025 (no dependants) | Ganancias.jubilado_cliffs |
| Bienes personales, art. 24 | The home is outside the tax up to the home threshold and wholly inside it one centavo above | $ 4.061.300,53 (2023), $ 11.899.406,06 (2024), $ 13.048.555,97 (2025) for someone whose other assets equal the general threshold | BienesPersonales.home_cliff, home_cliff_alone |
| Monotributo, Anexo art. 8 | One centavo of gross income over a category limit moves the whole monthly payment to the next category | Aug 2026, services, twelve months in the higher category: H to I $ 5.292.494,16, J to K $ 5.365.755,36, G to H $ 3.508.724,88. Categories are revised each semester (art. 9), so this is the cost of a year spent there | Monotributo.saltos_202608, cliff_H_I |
| Monotributo, exclusion | Above category K's limit the taxpayer leaves the regime altogether | above $ 126.610.838,75 (Aug 2026) | Monotributo.exclusion |

The art. 94 scale itself, the art. 73 scale and the bienes personales scale have no cliff on their bands: one more
peso never costs more than the scale's top rate (Ganancias.art94_no_cliff, Sociedades.no_cliff,
BienesPersonales.escala_no_cliff, tops).

## 2. Openings in the text

* **Let homes are exempt one by one, with no ceiling** (Ley 23.966 art. 21 l). For homes let "con contratos
  debidamente registrados" the test is the value "de cada uno de ellos". Any number of let homes each at the home
  threshold is untaxed; ten of them in 2025 are $ 13.465.481.559,90 outside the tax (on the home threshold computed
  here, see section 3), while a single let home of twice the threshold is taxed in full, and the
  owner's own home one centavo over the threshold is taxed in full. [BienesPersonales.alquiler_sin_tope,
  alquiler_2025]
* **Fraud put right early is fined less than an omission left to the end** (Ley 11.683 arts. 45, 46, 49). A first
  offender who defrauded and regularises between the inspection order and the vista previa pays a quarter of the
  minimum of two times the tax, that is half the tax; a first offender who merely omitted and waits for the
  assessment pays the whole tax. Before an inspection order there is no fine even for fraud.
  [Procedimiento.fraude_temprano, espontanea]
* **A recidivist loses every reduction at once** (art. 49): $ 250.000 against $ 2.000.000 on $ 1.000.000 of tax
  in the same stage. [Procedimiento.reincidencia]

## 3. The administration's tables against the statute's words

* **January 2025 was adjusted by four months, not by the calendar semester the statute names.** Art. 30 and
  art. 94 are adjusted "por el coeficiente que surja de la variación" of the IPC of the calendar semester. July to
  December 2024 gives an art. 30 a) amount of $ 4.244.114,41 for the first half of 2025; ARCA published
  $ 3.916.268,37, which is the September 2024 amounts times the index of December over August 2024 (ARCA cites the
  article after art. 102 of the regulations). The reason is visible: Ley 27.743 art. 74 had already adjusted the
  amounts in September 2024 by June to August, and the full semester would have counted July and August twice.
  The statute's text does not say so; the regulations do. [Ganancias.enero_2025_semester, art94_2025S1, art30_2025S1]
* **The September 2024 coefficient was built from rounded monthly rates.** 1,1335 is 4,6 %, 4,0 % and 4,2 %
  compounded; the index ratio is 1,133316, which would put the art. 30 a) amount of the first half of 2025
  $ 635,09 lower. [Ganancias.sept_2024_rounded, coeficiente_sept_2024, indice_sept_2024]
* **"Incrementar en 3,8 veces" is a wording with two readings.** Art. 30 c) increases the art. 30 a) amount "en"
  3,8 times (2,5 for the self-employed); ARCA's special deduction is 4,8 times the amount, the natural reading of
  "increase by". Read as "multiply by 3,8", the deduction would be one art. 30 a) amount smaller. ARCA's reading is
  consistent across both apartados; the point is only that the text bears both.
  [Ganancias.especial_2025, especial_other_reading]
* **Art. 73 company scale, 2022.** ARCA's scales for 2023 to 2026 are the statute's 2021 amounts times the index of
  the previous October over October 2020, to the centavo. The 2022 scale is not: its first limit, $ 7.604.948,57,
  is $ 633,97 under the index figure, because that year the two October indices were taken rounded to one decimal
  (547,1 over 359,7), which reproduces the whole 2022 table. [Sociedades.arca_2023_2026, arca_2022,
  arca_2022_un_decimal]
* **The home threshold after 2023 is not printed by ARCA** on the pages read here; by the statute's rule it is
  $ 1.025.482.377,13 for 2024 and $ 1.346.548.155,99 for 2025. These two figures are computed, not compared with
  an official one. [BienesPersonales.home_thresholds]

Everything else checked reproduces to the centavo from INDEC's index: the art. 94 limits for 2025 and 2026
(Ganancias.art94_2025, art94_2026S1, art94_2026), the art. 30 amounts but for one-centavo cells
(art30_2025, art30_2026), the Monotributo tables of August 2025, February 2026 and August 2026, 66 cells each
(Monotributo.indexado_202508, indexado_202602, indexado_202608), and the bienes personales tables of 2024 and
2025, each from the statute's 2023 amounts (BienesPersonales.ajuste_2024, ajuste_2025). ARCA compounds on the
statute's amounts, not on its own rounded table of the year before; chaining the rounded tables lands a centavo
away (BienesPersonales.ajuste_2025_encadenado).

## 4. Printed tables that disagree with themselves

* **ARCA's pension table for 2025, September row**: it repeats August's haber mínimo, $ 314.305,37, beside a
  product of $ 2.562.217,36, which is eight times $ 320.277,17. The running totals follow the products, so the
  annual figure is unaffected. [Ganancias.septiembre_2025, acumulados]
* **Printed tables that step down by a centavo at a limit**, because a fixed sum sits a fraction of a centavo
  (0,31 and 0,55 in Ganancias, 1,19 in bienes personales) under the tax on the bands below it: art. 94 annual 2025 at $ 7.874.556,52 and first half 2025 at $ 46.181.289,52
  [Ganancias.printed_step_2025, printed_step_2025S1, fixed_sums_within_a_centavo]; bienes personales 2025 at
  $ 114.105.948,16 [BienesPersonales.escala2025_step]. The cause is that limits and fixed sums are indexed and
  rounded separately.
* **Monthly art. 94 tables**: of the 384 limit cells checked, 339 follow the twelfth-part rule exactly and 45 are
  one centavo off. [Ganancias.monthly_cells]
* **Monotributo, SIPA column**: the one column that does not index exactly, by up to 5 centavos.
  [Monotributo.sipa_centavos]
* **Art. 73 company scales**: fixed sums within half a centavo of the bands in every year. [Sociedades.gaps]

## 5. Amounts a reform left behind

* **Ley 27.799 (B.O. 2/1/2026) multiplied the art. 38 fines by 1 100 and left the appeal thresholds.** The Tribunal
  Fiscal hears fines over $ 25.000 (art. 159 b, amount of 2012) and a court claim needs more than $ 200 (arts. 82
  and 86, amount of 2003). No art. 38 fine reached the first before 2026; the smallest one now, $ 110.000 (art. 38
  second paragraph, paid within fifteen days), is 4,4 times it and 550 times the second. [Procedimiento.umbrales_sin_actualizar]
* **The funeral deduction reads "PESOS CUATRO CENTAVOS ($ 0,04)"** (Ganancias art. 29, a 1985 amount), and the one
  article that tied it to an update, art. 184, points at art. 32, repealed in 2024. Updates of that kind were
  already frozen by Ley 23.928 in 1991, so the 2024 repeal removed the mechanism, not a working update; the amount
  applied in practice was not checked here. [ArLegal: LigArt32.sepelio_frozen]
* **Bienes personales: the scale of each later year is printed with 2023 amounts**, to be adjusted by the article
  after art. 24; the 2024 statute table is the 2023 one less its last band. [BienesPersonales.ajuste_2024]

## Not covered

Valuation rules, exemptions other than those named, provincial taxes, the corporate tax base, VAT's list of
goods per rate, interest (art. 37, set by resolution), and the 2024 ARCA tables, whose PDFs have a broken font
map and cannot be read by machine.
