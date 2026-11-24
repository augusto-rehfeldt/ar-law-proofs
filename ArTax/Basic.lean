/-!
# Basic arithmetic for the Argentine tax models

Every amount is a whole number of centavos (`Int`): the statutes and ARCA's tables print pesos with two decimals.
Rates are whole per cents or, where a statute uses fractions of a per cent, hundredths of a per cent.

`rnd n d` is the exact quotient `n / d` (with `d > 0`) rounded to the nearest unit, a half counted up. It is the
rounding that reproduces ARCA's published tables from INDEC's index (see `ArTax/Ganancias/Indexing.lean`); no
statute states it.
-/

namespace ArTax

/-- `n / d` rounded to the nearest unit, a half counted up. Requires `d > 0`. -/
def rnd (n d : Int) : Int := (2 * n + d) / (2 * d)

/-- The positive part, `max 0 x`. -/
def pos (x : Int) : Int := max 0 x

/-- `p` per cent of `x`, rounded (`p` in hundredths of a per cent: `pct 1050 x` is 10.5 %). -/
def pct (p x : Int) : Int := rnd (p * x) 10000

theorem rnd_exact (k d : Int) (hd : 0 < d) : rnd (k * d) d = k := by
  unfold rnd
  have h : 2 * (k * d) + d = (2 * d) * k + d := by
    rw [Int.mul_comm k d, ← Int.mul_assoc]
  rw [h, Int.add_comm, Int.add_mul_ediv_left _ _ (by omega)]
  have : d / (2 * d) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  omega

theorem rnd_mono {a b d : Int} (hd : 0 < d) (h : a ≤ b) : rnd a d ≤ rnd b d := by
  unfold rnd
  exact Int.ediv_le_ediv (by omega) (by omega)

theorem rnd_nonneg {a d : Int} (hd : 0 < d) (h : 0 ≤ a) : 0 ≤ rnd a d := by
  unfold rnd
  exact Int.ediv_nonneg (by omega) (by omega)

theorem pos_nonneg (x : Int) : 0 ≤ pos x := by unfold pos; omega

theorem pos_mono {x y : Int} (h : x ≤ y) : pos x ≤ pos y := by unfold pos; omega

/-- The positive part grows no faster than its argument. -/
theorem pos_step {x y : Int} (h : x ≤ y) : pos y - pos x ≤ y - x := by unfold pos; omega

end ArTax
