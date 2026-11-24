import ArTax.Basic

/-!
# Régimen Simplificado para Pequeños Contribuyentes (Monotributo)

Anexo of Ley 24.977 as amended by Ley 27.743; the amounts in force are ARCA's "Cuadro de categorías y valores del
monotributo" (ArTax/Data/Monotributo.lean), one table per half-year starting 1 February and 1 August.

A taxpayer falls in the first category whose limits they do not exceed and pays that category's monthly amount:
the impuesto integrado (lower for sales of goods than for services from category C up), the contribution to the
SIPA and the contribution to an obra social. Above the limits of category K the regime no longer applies.

The model categorises by gross receipts and by rents accrued in the year. The other parameters of the table (floor
area, electricity used, maximum unit price) are not modelled.
-/

namespace ArTax.Monotributo

/-- One category of ARCA's table, in centavos: the annual limits, then the monthly amounts. -/
structure Row where
  ingresos : Int
  alquileres : Int
  precioUnitario : Int
  impServicios : Int
  impVenta : Int
  sipa : Int
  obraSocial : Int
  totalServicios : Int
  totalVenta : Int
deriving Repr, DecidableEq

/-- Categories A to K, in order. -/
abbrev Table := List Row

inductive Actividad where
  | servicios
  | venta
deriving Repr, DecidableEq

/-- The monthly amount of a category as the table totals it. -/
def Row.cuota (r : Row) : Actividad → Int
  | .servicios => r.totalServicios
  | .venta => r.totalVenta

/-- The monthly amount rebuilt from its three parts. -/
def Row.partes (r : Row) : Actividad → Int
  | .servicios => r.impServicios + r.sipa + r.obraSocial
  | .venta => r.impVenta + r.sipa + r.obraSocial

/-- The category of a taxpayer with these gross receipts and rents of the last twelve months: the first row
whose limits are not exceeded; none above category K (excluded from the regime). -/
def categoria (t : Table) (ingresos alquileres : Int) : Option Row :=
  t.find? fun r => decide (ingresos ≤ r.ingresos) && decide (alquileres ≤ r.alquileres)

/-- The category by gross receipts alone. -/
def porIngresos (t : Table) (ingresos : Int) : Option Row := t.find? fun r => decide (ingresos ≤ r.ingresos)

/-- What the regime costs in a year at these receipts: twelve monthly amounts of the category. -/
def costoAnual (t : Table) (a : Actividad) (ingresos : Int) : Option Int :=
  (porIngresos t ingresos).map fun r => 12 * r.cuota a

/-- For each limit between two categories: what one centavo over it costs in a year, twelve times the difference
of the monthly amounts. -/
def saltos (t : Table) (a : Actividad) : List Int :=
  (t.zip (t.drop 1)).map fun (r, s) => 12 * (s.cuota a - r.cuota a)

/-- The annual limits of gross receipts. -/
def limites (t : Table) : List Int := t.map (·.ingresos)

end ArTax.Monotributo
