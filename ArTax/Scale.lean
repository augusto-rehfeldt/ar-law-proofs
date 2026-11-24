import ArTax.Basic

/-!
# Progressive scales

Argentine tax statutes print a scale as rows "más de A, a B, pagarán F, más el r %, sobre el excedente de A"
(Ley de Impuesto a las Ganancias art. 94 and art. 73; Ley 23.966 art. 25). A `Band` is one such row.

Two readings of a scale are defined, because the printed fixed sums `F` are redundant: they should equal the tax
on the bands below.

* `ticks`: the sum over the bands, written with the increases of the rate (`Σ (rᵢ − rᵢ₋₁) · max 0 (x − Aᵢ)`), in
  hundredths of a centavo and exact. It ignores the printed fixed sums.
* `printedTicks`: the row `x` falls in, as printed: `F + r · (x − A)`.

The general theorems are about `ticks`: it never falls when income rises and never rises faster than the top
rate. `fixedGaps` measures, for a given table, how far each printed fixed sum is from the exact one.
-/

namespace ArTax

/-- One printed row: lower limit and fixed sum in centavos, rate in per cent. -/
structure Band where
  lo : Int
  fixed : Int
  rate : Int
deriving Repr, DecidableEq

abbrev Scale := List Band

namespace Scale

/-- Exact tax in hundredths of a centavo, band by band, given the rate `prev` of the band below. -/
def ticksFrom (prev : Int) : Scale → Int → Int
  | [], _ => 0
  | b :: t, x => (b.rate - prev) * pos (x - b.lo) + ticksFrom b.rate t x

/-- Exact tax on `x` centavos, in hundredths of a centavo. -/
def ticks (s : Scale) (x : Int) : Int := ticksFrom 0 s x

/-- The rates never fall from one band to the next. -/
def progressiveFrom (prev : Int) : Scale → Bool
  | [] => true
  | b :: t => decide (prev ≤ b.rate) && progressiveFrom b.rate t

def progressive (s : Scale) : Bool := progressiveFrom 0 s

/-- The rate of the last band. -/
def topFrom (prev : Int) : Scale → Int
  | [] => prev
  | b :: t => topFrom b.rate t

def top (s : Scale) : Int := topFrom 0 s

theorem ticksFrom_mono : ∀ (s : Scale) (prev : Int), progressiveFrom prev s = true →
    ∀ x y : Int, x ≤ y → ticksFrom prev s x ≤ ticksFrom prev s y
  | [], _, _, _, _, _ => Int.le_refl _
  | b :: t, prev, hp, x, y, hxy => by
    simp only [progressiveFrom, Bool.and_eq_true, decide_eq_true_eq] at hp
    have h1 : (b.rate - prev) * pos (x - b.lo) ≤ (b.rate - prev) * pos (y - b.lo) :=
      Int.mul_le_mul_of_nonneg_left (pos_mono (by omega)) (by omega)
    have h2 := ticksFrom_mono t b.rate hp.2 x y hxy
    simp only [ticksFrom]
    omega

theorem ticksFrom_lipschitz : ∀ (s : Scale) (prev : Int), progressiveFrom prev s = true →
    ∀ x y : Int, x ≤ y → ticksFrom prev s y - ticksFrom prev s x ≤ (topFrom prev s - prev) * (y - x)
  | [], prev, _, x, y, _ => by simp [ticksFrom, topFrom]
  | b :: t, prev, hp, x, y, hxy => by
    simp only [progressiveFrom, Bool.and_eq_true, decide_eq_true_eq] at hp
    have h1 : (b.rate - prev) * (pos (y - b.lo) - pos (x - b.lo)) ≤ (b.rate - prev) * (y - x) :=
      Int.mul_le_mul_of_nonneg_left (by have := pos_step (x := x - b.lo) (y := y - b.lo) (by omega); omega) (by omega)
    have h2 := ticksFrom_lipschitz t b.rate hp.2 x y hxy
    have h3 : (topFrom b.rate t - prev) * (y - x) = (b.rate - prev) * (y - x) + (topFrom b.rate t - b.rate) * (y - x) := by
      rw [← Int.add_mul]; congr 1; omega
    rw [Int.mul_sub] at h1
    simp only [ticksFrom, topFrom]
    omega

/-- **A progressive scale never lowers the tax when income rises**, whatever its limits and rates. -/
theorem ticks_mono (s : Scale) (h : s.progressive = true) {x y : Int} (hxy : x ≤ y) : s.ticks x ≤ s.ticks y :=
  ticksFrom_mono s 0 h x y hxy

/-- **No cliff inside a progressive scale**: the tax on `y - x` more centavos is at most the top rate on them. -/
theorem ticks_lipschitz (s : Scale) (h : s.progressive = true) {x y : Int} (hxy : x ≤ y) :
    s.ticks y - s.ticks x ≤ s.top * (y - x) := by
  have := ticksFrom_lipschitz s 0 h x y hxy
  simpa [ticks, top] using this

/-- The row `x` falls in, read as the statute prints it ("más de A, a B"): the last row whose lower limit is
below `x`. -/
def pick (cur : Band) : Scale → Int → Band
  | [], _ => cur
  | b :: t, x => if b.lo < x then pick b t x else cur

/-- Tax on `x` as printed: the row's fixed sum plus its rate on the excess, in `1 / unit` of a centavo, where
`unit` is what the rates are out of (100 for whole per cents, 10 000 for hundredths of a per cent). -/
def printedTicksU (unit : Int) (s : Scale) (x : Int) : Int :=
  match s with
  | [] => 0
  | b :: t => let r := pick b t x; r.fixed * unit + r.rate * pos (x - r.lo)

/-- Tax on `x` centavos as printed, in centavos, for rates out of `unit`. -/
def taxU (unit : Int) (s : Scale) (x : Int) : Int := rnd (printedTicksU unit s x) unit

/-- Tax on `x` centavos from the bands alone, in centavos, for rates out of `unit`. -/
def exactTaxU (unit : Int) (s : Scale) (x : Int) : Int := rnd (ticks s x) unit

/-- For each row, the printed fixed sum less the exact tax at the row's lower limit, in `1 / unit` of a
centavo. All zeros means the printed column is exactly the sum of the bands below. -/
def fixedGapsU (unit : Int) (s : Scale) : List Int := s.map fun b => b.fixed * unit - ticks s b.lo

/-- Tax on `x` as printed, in hundredths of a centavo (rates in whole per cents). -/
def printedTicks (s : Scale) (x : Int) : Int := printedTicksU 100 s x

/-- Tax on `x` centavos as printed, in centavos. -/
def tax (s : Scale) (x : Int) : Int := taxU 100 s x

/-- Tax on `x` centavos from the bands alone, in centavos. -/
def exactTax (s : Scale) (x : Int) : Int := exactTaxU 100 s x

/-- Printed fixed sums less exact ones, in hundredths of a centavo. -/
def fixedGaps (s : Scale) : List Int := fixedGapsU 100 s

/-- The lower limits of the rows after the first. -/
def limits (s : Scale) : List Int := (s.drop 1).map (·.lo)

end Scale
end ArTax
