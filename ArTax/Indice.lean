import ArTax.Basic
import ArTax.Data.Ipc

/-!
# Adjusting an amount by INDEC's index

The statutes adjust their amounts "por el coeficiente que surja de la variación del Índice de Precios al Consumidor
(IPC) que suministre el INDEC" over a stated period. Read as the ratio of the index at the end of the period to the
index at its start, applied to the amount and rounded to the centavo, this reproduces ARCA's tables
(ArTax/Ganancias/Indexing.lean, ArTax/Monotributo/Theorems.lean).
-/

namespace ArTax

/-- An amount adjusted by the index of month a over the index of month b, to the nearest centavo. -/
def idx (a b : Nat) (x : Int) : Int := rnd (x * ipc a) (ipc b)

/-- The rise of the index in month m over the month before, in tenths of a per cent: the monthly figure as INDEC
announces it, to one decimal. -/
def variacion (m prev : Nat) : Int := rnd ((ipc m - ipc prev) * 1000) (ipc prev)

end ArTax
