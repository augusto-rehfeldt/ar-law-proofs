import ArTax.Data.Ganancias
import ArTax.Data.Jubilados

/-!
# The specific deduction for pensions

Art. 30, eighth and ninth paragraphs: "Respecto de las rentas mencionadas en el inciso c) del artículo 82 de la
presente, las deducciones previstas en los incisos a) y c) de este artículo, serán reemplazadas por una deducción
específica equivalente a ocho (8) veces la suma de los haberes mínimos garantizados, definidos en el artículo 125 de
la ley 24.241 [...], siempre que esta última suma resulte superior a la suma de las deducciones antedichas. Lo
dispuesto en el párrafo anterior no será de aplicación respecto de aquellos sujetos que perciban y/u obtengan
ingresos de distinta naturaleza a los allí previstos superiores al monto previsto en el inciso a) de este artículo.
Tampoco corresponderá esa deducción para quienes se encuentren obligados a tributar el Impuesto sobre los Bienes
Personales, siempre y cuando esta obligación no surja exclusivamente de la tenencia de un inmueble para vivienda
única."

ARCA publishes the deduction month by month from ANSES's resolutions (ArTax/Data/Jubilados.lean).
-/

namespace ArTax.Ganancias
open ArTax

/-- The months of a table whose printed product is not eight times the printed haber (January is 0). -/
def filasMal (t : List Haber) : List Nat :=
  (t.zip (List.range t.length)).filterMap fun x => if 8 * x.1.hmg = x.1.producto then none else some x.2

/-- The running totals rebuilt from the printed products. -/
def acumular : Int → List Haber → List Int
  | _, [] => []
  | acc, h :: t => (acc + h.producto) :: acumular (acc + h.producto) t

/-- **A misprint in ARCA's table for 2025.** In eleven months the printed product is eight times the printed haber
mínimo. In September it is not: the table repeats August's haber, $ 314.305,37, next to a product of
$ 2.562.217,36, which is eight times $ 320.277,17. -/
theorem septiembre_2025 : filasMal h2025 = [8] ∧ (h2025.map (·.hmg))[8]? = (h2025.map (·.hmg))[7]? ∧
    (h2025.map (·.producto))[8]? = some (8 * 32027717) := by decide

/-- The table for 2026 (January to October) has no such row. -/
theorem productos_2026 : filasMal h2026 = [] := by decide

/-- Every printed running total is the sum of the printed products so far, in both tables. -/
theorem acumulados : acumular 0 h2025 = h2025.map (·.acumulado) ∧ acumular 0 h2026 = h2026.map (·.acumulado) := by
  decide

/-- The specific deduction for the whole of 2025: $ 29.194.257,68. -/
def especifica2025 : Int := 2919425768

theorem especifica2025_es : (h2025.map (·.acumulado)).getLast? = some especifica2025 := by decide

/-- Incisos a) and c) 2 for a pensioner with no dependants, with the twelfth that art. 30 c) adds wherever
apartado 2 applies. -/
def comunes (d : Deductions) : Int := d.mni + d.especial2 + rnd (d.mni + d.especial2) 12

/-- What a pensioner with no dependants deducts under incisos a) and c): the specific deduction if it is the
larger, unless other income exceeds the inciso a) amount or the pensioner must pay bienes personales for more than
a single home. -/
def deduccionJubilado (d : Deductions) (especifica otrosIngresos : Int) (obligadoBienes : Bool) : Int :=
  if d.mni < otrosIngresos || obligadoBienes then comunes d else max especifica (comunes d)

/-- **For 2025 the specific deduction is the larger one**: $ 29.194.257,68 against $ 28.322.159,69. -/
theorem especifica_mayor : comunes d2025 = 2832215969 ∧ especifica2025 - comunes d2025 = 87209799 := by decide

/-- **Two cliffs for a pensioner (2025).** Other income of exactly the inciso a) amount keeps the specific
deduction; one centavo more loses $ 872.097,99 of deduction. So does becoming liable to bienes personales for
anything but a single home. -/
theorem jubilado_cliffs :
    deduccionJubilado d2025 especifica2025 d2025.mni false = 2919425768 ∧
    deduccionJubilado d2025 especifica2025 (d2025.mni + 1) false = 2832215969 ∧
    deduccionJubilado d2025 especifica2025 0 true = 2832215969 := by decide

end ArTax.Ganancias
