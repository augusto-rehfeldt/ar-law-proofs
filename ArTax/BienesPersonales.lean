import ArTax.Scale
import ArTax.Indice

/-!
# Impuesto sobre los bienes personales

Ley 23.966, Título VI, as amended by Ley 27.743 art. 63 (InfoLEG texto actualizado,
sources/infoleg/ley23966_texact.htm).

* Art. 24: "No estarán alcanzados por el impuesto los bienes gravados [...] cuando su valor en conjunto [...] resulten
  iguales o inferiores a cien millones de pesos ($ 100.000.000). De tratarse de inmuebles destinados a
  casa-habitación del contribuyente [...] no estarán alcanzados por el impuesto cuando su valor [...] resulten iguales
  o inferiores a trescientos cincuenta millones de pesos ($ 350.000.000)."
* Article added after art. 24: "Los montos previstos en el artículo 24 y en el artículo 25, se ajustarán anualmente
  por el coeficiente que surja de la variación anual del [IPC] correspondiente al mes de octubre del año anterior al
  del ajuste respecto al mismo mes del año anterior."
* Art. 25: the tax is the scale applied to "el valor total de los bienes [...] que exceda del establecido en el
  artículo 24"; one scale per fiscal period 2023 to 2026, each printed with the amounts of 2023, and for 2027 "cero
  coma veinticinco por ciento (0,25%)" flat.

Amounts in centavos; rates in hundredths of a per cent (50 is 0.50 %).

The model takes the value of the home and the value of everything else, both already valued under the Ley. Not
covered: valuation, shares taxed through the company (article after art. 25), the reduced rates for "contribuyentes
cumplidores", the REIBP of Ley 27.743, and taxpayers abroad.
-/

namespace ArTax.BienesPersonales
open ArTax

/-- The rates are out of 10 000. -/
def unit : Int := 10000

/-- One fiscal period: the general threshold, the home threshold, the scale. -/
structure Periodo where
  mni : Int
  casa : Int
  scale : Scale

/-- Art. 25 a., fiscal period 2023, as printed in the statute. -/
def escala2023 : Scale := [⟨0, 0, 50⟩, ⟨1368870413, 6844352, 75⟩, ⟨2965885897, 18821968, 100⟩,
  ⟨8213222482, 71295334, 125⟩, ⟨45629013784, 538992725, 150⟩]

/-- ARCA, "Tabla general período 2024" (sources/arca/bienes-personales-alicuotas.html). -/
def escala2024 : Scale := [⟨0, 0, 50⟩, ⟨4010721386, 20053607, 75⟩, ⟨8689896343, 55147419, 100⟩,
  ⟨24064328328, 208891739, 125⟩]

/-- ARCA, "Tabla general período 2025". -/
def escala2025 : Scale := [⟨0, 0, 50⟩, ⟨5266428373, 26332142, 75⟩, ⟨11410594816, 72413389, 100⟩]

/-- Art. 24: $ 100.000.000 and $ 350.000.000 (fiscal period 2023). -/
def p2023 : Periodo := ⟨10000000000, 35000000000, escala2023⟩

/-- 2024: ARCA's threshold, $ 292.994.964,89; the home threshold is the statute's rule applied to $ 350.000.000. -/
def p2024 : Periodo := ⟨29299496489, idx 202410 202310 35000000000, escala2024⟩

/-- 2025: ARCA's threshold, $ 384.728.044,57; the home threshold by the same rule, from the 2023 amount. -/
def p2025 : Periodo := ⟨38472804457, idx 202510 202310 35000000000, escala2025⟩

/-- A taxpayer's assets at 31 December: the home, and everything else that is taxable. -/
structure Bienes where
  casa : Int
  otros : Int

/-- Art. 24, second paragraph: the home is outside the tax only while its value does not exceed the home
threshold; above it the whole value counts. -/
def gravados (p : Periodo) (b : Bienes) : Int := b.otros + (if b.casa ≤ p.casa then 0 else b.casa)

/-- Art. 25: the value "que exceda" the threshold of art. 24. -/
def base (p : Periodo) (b : Bienes) : Int := pos (gravados p b - p.mni)

/-- The tax on the printed scale, in centavos. -/
def impuesto (p : Periodo) (b : Bienes) : Int := p.scale.taxU unit (base p b)

/-! ## The statute's scale -/

/-- The fixed sums the statute prints for 2023 are the tax on the bands below, to the centavo: printed less exact,
in ten-thousandths of a centavo, each under half a centavo. -/
theorem escala2023_gaps : escala2023.fixedGapsU unit = [0, -650, -1950, -450, -3200] := by decide

theorem escalas_progressive : [escala2023, escala2024, escala2025].all Scale.progressive = true := by decide

/-- **No cliff at the general threshold or inside the scale**: on the bands, more taxable assets never lower the
tax, in any of the three periods. -/
theorem escala_mono {s : Scale} (h : s ∈ [escala2023, escala2024, escala2025]) {x y : Int} (hxy : x ≤ y) :
    s.exactTaxU unit x ≤ s.exactTaxU unit y :=
  rnd_mono (by decide) (s.ticks_mono (List.all_eq_true.mp escalas_progressive s h) hxy)

/-- **No cliff, with the bound**: on the bands, one more peso of taxable assets never costs more than the scale's
top rate: 1.50 % in 2023, 1.25 % in 2024, 1.00 % in 2025. -/
theorem escala_no_cliff {s : Scale} (h : s ∈ [escala2023, escala2024, escala2025]) {x y : Int} (hxy : x ≤ y) :
    s.ticks y - s.ticks x ≤ s.top * (y - x) :=
  s.ticks_lipschitz (List.all_eq_true.mp escalas_progressive s h) hxy

theorem tops : [escala2023, escala2024, escala2025].map Scale.top = [150, 125, 100] := by decide

/-- Other assets one centavo over the threshold cost nothing yet; the tax starts at 0.50 % of the excess. -/
theorem no_cliff_at_threshold : [p2023, p2024, p2025].all (fun p =>
    impuesto p ⟨0, p.mni⟩ == 0 && impuesto p ⟨0, p.mni + 1⟩ == 0) = true := by decide

/-! ## ARCA's amounts for 2024 and 2025 against the statute's rule -/

/-- **2024.** ARCA's threshold, every limit and every fixed sum of its table are the statute's 2023 figures times
the index of October 2024 over October 2023, to the centavo. The statute's own table for 2024 (art. 25 b.) is the
2023 one without its last band. -/
theorem ajuste_2024 : idx 202410 202310 p2023.mni = p2024.mni ∧
    (escala2023.take 4).map (fun b => (idx 202410 202310 b.lo, idx 202410 202310 b.fixed, b.rate)) =
      escala2024.map (fun b => (b.lo, b.fixed, b.rate)) := by decide

/-- **2025.** Art. 25 prints every period's scale with the 2023 amounts, so the adjustment starts from them:
ARCA's threshold, limits and fixed sums are the statute's 2023 figures times the index of October 2025 over October
2023, to the centavo. -/
theorem ajuste_2025 : idx 202510 202310 p2023.mni = p2025.mni ∧
    (escala2023.take 3).map (fun b => (idx 202510 202310 b.lo, idx 202510 202310 b.fixed, b.rate)) =
      escala2025.map (fun b => (b.lo, b.fixed, b.rate)) := by decide

/-- Adjusting ARCA's rounded 2024 figures by one more year instead lands a centavo away twice (threshold and last
fixed sum): ARCA does not chain its own tables. -/
theorem ajuste_2025_encadenado : idx 202510 202410 p2024.mni = p2025.mni - 1 ∧
    (escala2024.take 3).map (fun b => idx 202510 202410 b.fixed) = [0, 26332142, 72413389 + 1] := by decide

/-- That fixed sum is also 1.19 centavos below the tax on the bands under it, so in the 2025 table one centavo
more of assets over $ 114.105.948,16 lowers the tax by a centavo. -/
theorem escala2025_step : escala2025.fixedGapsU unit = [0, 1350, -11875] ∧
    escala2025.taxU unit 11410594817 = escala2025.taxU unit 11410594816 - 1 := by decide

/-! ## The home: all or nothing -/

/-- **One centavo over the home threshold.** A taxpayer whose other assets equal the general threshold owes
nothing while the home is worth the home threshold or less. One centavo more and the whole home is taxed:
$ 4.061.300,53 in 2023, $ 11.899.406,06 in 2024, $ 13.048.555,97 in 2025. -/
theorem home_cliff : [p2023, p2024, p2025].map (fun p =>
    (impuesto p ⟨p.casa, p.mni⟩, impuesto p ⟨p.casa + 1, p.mni⟩)) =
    [(0, 406130053), (0, 1189940606), (0, 1304855597)] := by decide

/-- The home thresholds by the statute's rule: $ 1.025.482.377,13 for 2024 and $ 1.346.548.155,99 for 2025. -/
theorem home_thresholds : p2024.casa = 102548237713 ∧ p2025.casa = 134654815599 := by decide

/-- With no other assets at all, a home one centavo over the threshold is taxed on its value above the general
threshold. -/
theorem home_cliff_alone : [p2023, p2024, p2025].map (fun p => impuesto p ⟨p.casa + 1, 0⟩) =
    [281130053, 823696900, 920127552] := by decide

/-- Below the threshold the home never counts, whatever else is owned. -/
theorem home_exempt (p : Periodo) (b : Bienes) (h : b.casa ≤ p.casa) : gravados p b = b.otros := by
  simp [gravados, h]

/-! ## Homes let to tenants: an exemption per property, with no ceiling -/

/-- Art. 21 l) (Ley 27.737): exempt are "los inmuebles destinados a locación para casa-habitación, con contratos
debidamente registrados, cuando el valor de cada uno de ellos sea igual o inferior al monto establecido en el
segundo párrafo del artículo 24". What the let homes add to the taxable assets. -/
def alquilerGravado (p : Periodo) : List Int → Int
  | [] => 0
  | v :: t => (if v ≤ p.casa then 0 else v) + alquilerGravado p t

/-- **The test is on each property, not on their sum**: any number of let homes, each worth exactly the home
threshold, adds nothing to the taxable assets. -/
theorem alquiler_sin_tope (p : Periodo) (n : Nat) : alquilerGravado p (List.replicate n p.casa) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate, alquilerGravado, ih]

/-- Ten let homes at the 2025 threshold, $ 13.465.481.559,90 in all, are outside the tax; one let home worth a
fifth of that is taxed on its whole value. -/
theorem alquiler_2025 : alquilerGravado p2025 (List.replicate 10 p2025.casa) = 0 ∧
    10 * p2025.casa = 1346548155990 ∧ alquilerGravado p2025 [2 * p2025.casa] = 269309631198 := by decide

end ArTax.BienesPersonales
