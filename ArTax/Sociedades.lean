import ArTax.Scale
import ArTax.Indice
import ArTax.Data.Sociedades

/-!
# Impuesto a las ganancias of companies: the scale of art. 73

Ley de Impuesto a las Ganancias art. 73 a), scale introduced by Ley 27.630 (B.O. 16/6/2021). InfoLEG prints the
scale as an image (sources/infoleg/ley27630.jpg): up to $ 5.000.000, 25 %; from $ 5.000.000 to $ 50.000.000,
$ 1.250.000 plus 30 % of the excess over $ 5.000.000; above $ 50.000.000, $ 14.750.000 plus 35 % of the excess
over $ 50.000.000.

Same article: "Los montos previstos en la escala [...] se ajustarán anualmente, a partir del 1° de enero de 2022,
considerando la variación anual del [IPC] correspondiente al mes de octubre del año anterior al del ajuste,
respecto del mismo mes del año anterior. Los montos determinados por aplicación del mecanismo descripto resultarán
de aplicación para los ejercicios fiscales que se inicien con posterioridad a cada actualización."

ARCA publishes the scale for each year (sources/arca/Ganancias-Escala-PJ-*.pdf, in ArTax/Data/Sociedades.lean).
-/

namespace ArTax.Sociedades
open ArTax

/-- Art. 73 a) as enacted, for fiscal years starting in 2021. -/
def escala2021 : Scale := [⟨0, 0, 25⟩, ⟨500000000, 125000000, 30⟩, ⟨5000000000, 1475000000, 35⟩]

/-- The statute's amounts, limits and fixed sums alike, times the index of month m over October 2020. -/
def escalaLey (m : Nat) : Scale := escala2021.map fun r => ⟨idx m 202010 r.lo, idx m 202010 r.fixed, r.rate⟩

/-- ARCA's published scales, 2022 to 2026. -/
def publicadas : List Scale := [arca2022, arca2023, arca2024, arca2025, arca2026]

/-- In the statute the fixed sums are exactly the tax on the bands below. -/
theorem escala2021_exact : escala2021.fixedGaps = [0, 0, 0] := by decide

theorem progressive : (escala2021 :: publicadas).all (fun s => s.progressive && s.top == 35) = true := by decide

/-- **No cliff between the three rates**: on the bands, one more peso of profit never costs more than 35 centavos,
in the statute's scale and in each published one. -/
theorem no_cliff {s : Scale} (h : s ∈ escala2021 :: publicadas) {x y : Int} (hxy : x ≤ y) :
    s.ticks x ≤ s.ticks y ∧ s.ticks y - s.ticks x ≤ 35 * (y - x) := by
  have hp := List.all_eq_true.mp progressive s h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have h1 := s.ticks_lipschitz hp.1 hxy
  rw [hp.2] at h1
  exact ⟨s.ticks_mono hp.1 hxy, h1⟩

/-- **2023 to 2026.** ARCA's scale is the 2021 statute scale, every limit and every fixed sum, times the index of
the previous October over October 2020, to the centavo. The yearly variations are compounded on the statute's
amounts, not on the rounded table of the year before. -/
theorem arca_2023_2026 : [arca2023, arca2024, arca2025, arca2026] =
    [202210, 202310, 202410, 202510].map escalaLey := by decide

/-- **2022 is the exception.** By the index of October 2021 over October 2020 the first limit is $ 7.605.582,54;
ARCA published $ 7.604.948,57, which is $ 633,97 less. -/
theorem arca_2022 : (escalaLey 202110).map (·.lo) = [0, 760558254, 7605582541] ∧
    arca2022.map (·.lo) = [0, 760494857, 7604948568] ∧ 760558254 - 760494857 = 63397 := by decide

/-- **Why.** The 2022 scale is the statute's amounts times 547,1 over 359,7: the two October indices rounded to one
decimal (INDEC's four-decimal values are 547,0802 and 359,6570). Every limit and fixed sum of ARCA's table follows. -/
theorem arca_2022_un_decimal : arca2022 = escala2021.map (fun r => ⟨rnd (r.lo * 5471) 3597, rnd (r.fixed * 5471) 3597, r.rate⟩) ∧
    ipc 202110 = 5470802 ∧ ipc 202010 = 3596570 := by decide

/-- Adjusted that way, each printed fixed sum stays within half a centavo of the tax on the bands below: printed
less exact, in hundredths of a centavo, 2021 to 2026. -/
theorem gaps : (escala2021 :: publicadas).map Scale.fixedGaps =
    [[0, 0, 0], [0, -25, 45], [0, -25, -35], [0, 0, -30], [0, 50, -30], [0, -50, 30]] := by decide

end ArTax.Sociedades
