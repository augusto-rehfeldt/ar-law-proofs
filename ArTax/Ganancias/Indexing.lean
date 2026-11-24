import ArTax.Indice
import ArTax.Data.Ganancias

/-!
# ARCA's tables against the statute and INDEC's index

Arts. 30 and 94 fix amounts (Ley 27.743, in force from fiscal year 2024) and say how they move:

* Ley 27.743 art. 74: "se ajustarán excepcionalmente en septiembre de 2024 por el coeficiente que surja de la
  variación del [IPC] correspondiente a los meses junio a agosto de 2024, inclusive";
* last paragraph of each article: "se ajustarán semestralmente, a partir del año fiscal 2025, inclusive, en los
  meses de enero y julio, por el coeficiente que surja de la variación del [IPC] correspondiente al semestre
  calendario que finalice el mes inmediato anterior al de la actualización que se realice."

The theorems below recompute ARCA's published amounts from the statute's own figures and INDEC's index and say,
to the centavo, where they agree and where they do not. The index is the series "IPC, nivel general, nacional,
base diciembre 2016" as served by datos.gob.ar (ArTax/Data/Ipc.lean).
-/

namespace ArTax.Ganancias
open ArTax

/-! ## 2025 and 2026: each table is the one before it times the index ratio -/

/-- **July 2025.** Every limit of the annual scale for 2025 is the limit of the first-half scale times the index
of June 2025 over December 2024, to the centavo. -/
theorem art94_2025 : s2025S1.limits.map (idx 202506 202412) = s2025.limits := by decide

/-- **January 2026**: the annual scale for 2025 times the index of December 2025 over June 2025. -/
theorem art94_2026S1 : s2025.limits.map (idx 202512 202506) = s2026S1.limits := by decide

/-- **July 2026**: the first-half scale times the index of June 2026 over December 2025. -/
theorem art94_2026 : s2026S1.limits.map (idx 202606 202512) = s2026.limits := by decide

/-- The three amounts art. 30 fixes: a), b) 1, b) 2. -/
def tres (d : Deductions) : List Int := [d.mni, d.conyuge, d.hijo]

theorem art30_2025 : (tres d2025S1).map (idx 202506 202412) = tres d2025 := by decide

theorem art30_2026S1 : (tres d2025).map (idx 202512 202506) = tres d2026S1 := by decide

/-- July 2026: inciso a) and the spouse to the centavo; ARCA's child deduction, $ 2.859.060,31, is one centavo
above the recomputed one. -/
theorem art30_2026 : (tres d2026S1).map (idx 202606 202512) = [d2026.mni, d2026.conyuge, d2026.hijo - 1] := by
  decide

/-! ## The second-half tables are the mean of the first half and the annual table -/

/-- Twice each limit of the second-half scale, less the first-half limit and the annual one, in centavos: the
second-half table is the mean of the other two within one centavo, rounded up in 2025 and both ways in 2026. -/
theorem art94_second_half :
    (s2025S2.limits.zip (s2025S1.limits.zip s2025.limits)).map (fun x => 2 * x.1 - x.2.1 - x.2.2) =
      [0, 1, 1, 0, 0, 0, 0, 0] ∧
    (s2026S2.limits.zip (s2026S1.limits.zip s2026.limits)).map (fun x => 2 * x.1 - x.2.1 - x.2.2) =
      [0, 1, -1, -1, 0, -1, 0, -1] := by decide

/-! ## The monthly tables

Each half-year PDF prints, for every month of the year, the cumulative scale the employer applies that month.
Expected limit of month m: m twelfths of the first-half limit up to June, then six twelfths of it plus (m - 6)
twelfths of the annual limit. -/

def mensual (h1 ha : List Int) (m : Int) : List Int :=
  if m ≤ 6 then h1.map fun x => rnd (x * m) 12 else (h1.zip ha).map fun x => rnd (x.1 * 6 + x.2 * (m - 6)) 12

/-- Printed limit less expected limit, for every month and band of a monthly table. -/
def desvios (tabs : List Scale) (h1 ha : List Int) : List Int :=
  ((tabs.zip (List.range tabs.length)).map fun x => (x.1.limits.zip (mensual h1 ha (x.2 + 1))).map fun y => y.1 - y.2).flatten

/-- **All 384 monthly limits are within one centavo of that rule; 45 are one centavo off** (5 and 4 in the two
tables for 2025, 15 and 21 in those for 2026). The first-half tables project the first-half amounts over the
whole year. -/
theorem monthly_cells :
    [desvios m2025S1 s2025S1.limits s2025S1.limits, desvios m2025S2 s2025S1.limits s2025.limits,
     desvios m2026S1 s2026S1.limits s2026S1.limits, desvios m2026S2 s2026S1.limits s2026.limits].map
      (fun l => (l.length, (l.filter (· != 0)).length, l.all fun x => decide (-1 ≤ x ∧ x ≤ 1))) =
    [(96, 5, true), (96, 4, true), (96, 15, true), (96, 21, true)] := by decide

/-! ## September 2024 and January 2025: from the statute's figures -/

/-- INDEC's monthly rises for June, July and August 2024, to one decimal: 4.6 %, 4.0 %, 4.2 %. -/
theorem variaciones_2024 :
    [variacion 202406 202405, variacion 202407 202406, variacion 202408 202407] = [46, 40, 42] := by decide

/-- Compounded and rounded to four decimals they give 1.1335. -/
theorem coeficiente_sept_2024 : rnd ((1000 + 46) * (1000 + 40) * (1000 + 42)) 100000 = 11335 := by decide

/-- The index itself rose by a factor of 1.133316 from May to August 2024. -/
theorem indice_sept_2024 : rnd (ipc 202408 * 1000000) (ipc 202405) = 1133316 := by decide

/-- The amounts from September 2024: the statute's figure times 1.1335. -/
def sept2024 (x : Int) : Int := rnd (x * 11335) 10000

/-- The amounts from January 2025 as ARCA computed them: the statute's figure times 1.1335, times the index of
December 2024 over August 2024. -/
def ene2025 (x : Int) : Int := rnd (x * 11335 * ipc 202412) (10000 * ipc 202408)

/-- **January 2025, the scale.** Every limit of ARCA's first-half scale for 2025 is the statute's limit times
1.1335 times the index of December over August 2024, to the centavo. -/
theorem art94_2025S1 : baseScale.limits.map ene2025 = s2025S1.limits := by decide

/-- January 2025, the deductions: inciso a) and the spouse to the centavo, the child one centavo above. -/
theorem art30_2025S1 :
    [baseMni, baseConyuge, baseHijo].map ene2025 = [d2025S1.mni, d2025S1.conyuge, d2025S1.hijo - 1] := by decide

/-- **The September 2024 coefficient was 1.1335, not the index ratio.** With the index of May and August 2024
(a factor of 1.133316) the inciso a) amount for the first half of 2025 would be $ 3.915.633,28, which is
$ 635,09 less than ARCA's $ 3.916.268,37. The difference is carried into every later table. -/
theorem sept_2024_rounded : rnd (baseMni * ipc 202412) (ipc 202405) = 391563328 ∧
    d2025S1.mni - 391563328 = 63509 := by decide

/-- **January 2025 did not use the calendar semester.** Art. 30 says January's adjustment is by the index of
"el semestre calendario que finalice el mes inmediato anterior": July to December 2024. Applied to the September
amount ($ 3.503.688,17) that gives $ 4.244.114,41. ARCA's amount is $ 3.916.268,37, the September amount times
the index of September to December only, so that July and August, already counted in September, are not counted
twice. ARCA's tables cite for it "el artículo sin número a continuación del artículo 102 de la Reglamentación". -/
theorem enero_2025_semester : sept2024 baseMni = 350368817 ∧
    idx 202412 202406 (sept2024 baseMni) = 424411441 ∧
    idx 202412 202408 (sept2024 baseMni) = d2025S1.mni := by decide

end ArTax.Ganancias
