import ArTax.Data.Ganancias

/-!
# Impuesto a las ganancias: theorems

General theorems hold for every income (no sorry, no native_decide). Concrete ones are evaluated by the kernel on
the figures ARCA printed for 2025 and 2026.
-/

namespace ArTax.Ganancias
open ArTax

/-- Annual assessment 2025 and 2026, ARCA's tables. -/
def p2025 : Periodo := ⟨d2025, s2025⟩
def p2026 : Periodo := ⟨d2026, s2026⟩

/-- The six headline scales ARCA published for 2025 and 2026. -/
def published : List Scale := [s2025S1, s2025S2, s2025, s2026S1, s2026S2, s2026]

/-! ## The scale of art. 94 has no cliff -/

theorem scales_progressive : (baseScale :: published).all Scale.progressive = true := by decide

theorem scales_top : (baseScale :: published).all (fun s => s.top == 35) = true := by decide

/-- **Art. 94 never lowers the tax when the taxable income rises**: the statute's scale and each published one. -/
theorem art94_mono {s : Scale} (h : s ∈ baseScale :: published) {x y : Int} (hxy : x ≤ y) :
    s.ticks x ≤ s.ticks y :=
  s.ticks_mono (List.all_eq_true.mp scales_progressive s h) hxy

/-- **No more than 35 % of any extra peso**: for the statute's scale and each published one, the tax on y - x more
centavos of taxable income is at most 35 % of them (exact amounts, in hundredths of a centavo). -/
theorem art94_no_cliff {s : Scale} (h : s ∈ baseScale :: published) {x y : Int} (hxy : x ≤ y) :
    s.ticks y - s.ticks x ≤ 35 * (y - x) := by
  have h1 := s.ticks_lipschitz (List.all_eq_true.mp scales_progressive s h) hxy
  have h2 : s.top = 35 := by simpa using List.all_eq_true.mp scales_top s h
  rwa [h2] at h1

/-! ## The printed fixed sums -/

/-- In the statute, every "pagarán" sum is exactly the tax on the bands below it. -/
theorem baseScale_exact : baseScale.fixedGaps = [0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide

/-- In ARCA's tables the fixed sums are rounded to the centavo. Printed sum less exact sum, in hundredths of a
centavo, for the six headline tables (first half 2025, second half 2025, annual 2025, then the same for 2026). -/
theorem published_gaps : published.map Scale.fixedGaps = [
    [0, -35, -38, -42, -7, 5, 9, 3, -55],
    [0, 20, 16, 44, -16, -4, 0, -6, -14],
    [0, -25, -21, 39, -31, -19, -15, -21, 21],
    [0, -45, -17, -25, -35, 5, -15, 15, -31],
    [0, -45, -37, 7, 47, -3, -30, -5, 48],
    [0, -45, 52, 24, 14, -7, 36, -17, 4]] := by decide

/-- Every printed fixed sum, in the six headline tables and the 48 monthly ones, is within one centavo of the
exact sum of the bands below it. -/
theorem fixed_sums_within_a_centavo :
    (published ++ m2025S1 ++ m2025S2 ++ m2026S1 ++ m2026S2).all
      (fun s => s.fixedGaps.all fun g => decide (-100 < g ∧ g < 100)) = true := by decide

/-- **A rounding step in the printed annual scale for 2025.** At a taxable income of exactly $ 7.874.556,52 (the
upper limit of the fourth band) the printed table gives one centavo more than at $ 7.874.556,53: the next row's
fixed sum, $ 848.702,20, is 0.31 centavo below the exact sum of the bands. -/
theorem printed_step_2025 : s2025.tax 787455653 = s2025.tax 787455652 - 1 := by decide

/-- The same in the table for the first half of 2025, at the top limit $ 46.181.289,52. -/
theorem printed_step_2025S1 : s2025S1.tax 4618128953 = s2025S1.tax 4618128952 - 1 := by decide

/-- On the bands alone the tax never falls at those points. -/
theorem exact_no_step : s2025.exactTax 787455652 ≤ s2025.exactTax 787455653 ∧
    s2025S1.exactTax 4618128952 ≤ s2025S1.exactTax 4618128953 := by decide

/-! ## Art. 30 c): "incrementar en 3,8 veces" -/

/-- ARCA's special deductions for 2025 are the inciso a) amount increased by 2.5, 3 and 3.8 times: 3.5, 4 and 4.8
times that amount. -/
theorem especial_2025 : d2025.especial1 = incrementar d2025.mni 25 ∧
    d2025.especial1Nuevos = incrementar d2025.mni 30 ∧ d2025.especial2 = incrementar d2025.mni 38 := by decide

/-- Read as a plain multiple ("3,8 veces el monto"), the employee's special deduction for 2025 would be
$ 17.128.520,98 instead of $ 21.636.026,50: the two readings differ by exactly the inciso a) amount. -/
theorem especial_other_reading : veces d2025.mni 38 = 1712852098 ∧
    d2025.especial2 - veces d2025.mni 38 = d2025.mni := by decide

/-- In the other five tables the printed special deductions are a few centavos above those multiples of the
printed inciso a) amount, and the deduction for a child unable to work is up to two centavos below twice the
child deduction. Columns: c) 1, c) 1 "nuevos", c) 2, child unable to work. -/
theorem especial_centavos : [d2025S1, d2025S2, d2025, d2026S1, d2026S2, d2026].map (fun d =>
      [d.especial1 - incrementar d.mni 25, d.especial1Nuevos - incrementar d.mni 30,
       d.especial2 - incrementar d.mni 38, d.hijoIncapacitado - 2 * d.hijo]) =
    [[1, 2, 2, -1], [2, 3, 4, 0], [0, 0, 0, -1], [1, 1, 2, 0], [1, 2, 3, -2], [2, 2, 3, -2]] := by decide

/-! ## The spouse deduction is lost at once -/

/-- **One centavo of the spouse's income costs the taxpayer $ 1.609.625,49 (2025).** An employee with a ganancia
neta of $ 100 million deducts $ 4.245.166,13 for a spouse whose net income of the year is $ 4.507.505,52, the
inciso a) amount. One centavo more and the whole deduction goes, with the twelfth added to it by art. 30 c). -/
theorem spouse_cliff_2025 :
    impuesto p2025 { neta := 10000000000, conyuge := some d2025.mni } = 1771169335 ∧
    impuesto p2025 { neta := 10000000000, conyuge := some (d2025.mni + 1) } = 1932131884 ∧
    (1932131884 : Int) - 1771169335 = 160962549 := by decide

/-- The same for 2026: $ 2.149.618,33 at a ganancia neta of $ 150 million. -/
theorem spouse_cliff_2026 :
    impuesto p2026 { neta := 15000000000, conyuge := some d2026.mni } = 2941185866 ∧
    impuesto p2026 { neta := 15000000000, conyuge := some (d2026.mni + 1) } = 3156147699 := by decide

/-- A spouse with income above the limit is the same as no spouse. -/
theorem spouse_over_limit (d : Deductions) (i : Int) (h : d.mni < i) : conyugeDed d (some i) = conyugeDed d none := by
  unfold conyugeDed
  have : ¬ i ≤ d.mni := by omega
  simp [this]

/-! ## The taxpayer's own income -/

/-- **More income never lowers the taxable income**, family and kind of income unchanged, whenever inciso a) plus
the family deductions is not negative. The special deduction grows with the income up to its ceiling, and the
twelfth with it, but never past the income itself. -/
theorem imponible_mono (d : Deductions) (p q : Persona) (hr : p.renta = q.renta) (hc : cargas d p = cargas d q)
    (h0 : 0 ≤ d.mni + cargas d q) (h : p.neta ≤ q.neta) : imponible d p ≤ imponible d q := by
  unfold imponible deducciones doceava especial
  rw [hr, hc]
  generalize cargas d q = c at *
  generalize topeEspecial d q.renta = t
  cases q.renta <;> simp only [rnd, pos] <;> omega

/-- **On the bands, more income never lowers the tax.** -/
theorem impuesto_mono (per : Periodo) (hs : per.scale.progressive = true) (p q : Persona) (hr : p.renta = q.renta)
    (hc : cargas per.ded p = cargas per.ded q) (h0 : 0 ≤ per.ded.mni + cargas per.ded q) (h : p.neta ≤ q.neta) :
    per.scale.exactTax (imponible per.ded p) ≤ per.scale.exactTax (imponible per.ded q) :=
  rnd_mono (by omega) (per.scale.ticks_mono hs (imponible_mono per.ded p q hr hc h0 h))

/-- A worked case for 2025: an employee with a ganancia neta of $ 40 million and no dependants deducts
$ 28.322.159,69, is taxed on $ 11.677.840,31 and owes $ 1.571.326,12. -/
theorem ejemplo_2025 : deducciones d2025 { neta := 4000000000 } = 2832215969 ∧
    imponible d2025 { neta := 4000000000 } = 1167784031 ∧
    impuesto p2025 { neta := 4000000000 } = 157132612 := by decide

end ArTax.Ganancias
