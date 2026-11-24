import ArTax.Indice
import ArTax.Data.Monotributo

/-!
# Monotributo: theorems

Anexo of Ley 24.977, art. 52 (texto Ley 27.743 art. 94): the limits and the amounts "se actualizarán semestralmente
a partir del año fiscal 2025, inclusive, en los meses de enero y julio, por el coeficiente que surja de la variación
anual del Índice de Precios al Consumidor (IPC) que suministre el [INDEC], correspondiente al semestre calendario que
finalice el mes inmediato anterior al de la actualización que se realice. La Administración Federal de Ingresos
Públicos será la encargada de publicar semestralmente los nuevos montos". ARCA's tables apply from 1 February and
1 August.
-/

namespace ArTax.Monotributo
open ArTax

/-- ARCA's four tables from February 2025 to August 2026. -/
def tablas : List Table := [t202502, t202508, t202602, t202608]

/-! ## The tables add up -/

/-- In every category of every table, the printed total is the impuesto integrado plus the SIPA contribution plus
the obra social contribution, for services and for sales. -/
theorem totales : tablas.all (fun t => t.length == 11 && t.all fun r =>
    r.cuota .servicios == r.partes .servicios && r.cuota .venta == r.partes .venta) = true := by decide

/-! ## Each table is the one before it times the index ratio -/

/-- The amounts that follow the index: the three limits, the two impuestos integrados and the obra social. -/
def campos (r : Row) : List Int :=
  [r.ingresos, r.alquileres, r.precioUnitario, r.impServicios, r.impVenta, r.obraSocial]

/-- **August 2025**: all 66 such amounts are those of February 2025 times the index of June 2025 over December
2024, to the centavo. -/
theorem indexado_202508 : t202502.map (fun r => (campos r).map (idx 202506 202412)) = t202508.map campos := by
  decide

/-- **February 2026**: times the index of December 2025 over June 2025. -/
theorem indexado_202602 : t202508.map (fun r => (campos r).map (idx 202512 202506)) = t202602.map campos := by
  decide

/-- **August 2026**: times the index of June 2026 over December 2025. -/
theorem indexado_202608 : t202602.map (fun r => (campos r).map (idx 202606 202512)) = t202608.map campos := by
  decide

/-- The SIPA contribution does not follow the same arithmetic to the centavo. Printed amount less the previous
amount times the index ratio, categories A to K, for the three updates: up to 5 centavos. -/
theorem sipa_centavos :
    (t202502.zip t202508).map (fun x => x.2.sipa - idx 202506 202412 x.1.sipa) = [0, 0, 1, -1, 0, 0, 0, 0, -1, -1, -2] ∧
    (t202508.zip t202602).map (fun x => x.2.sipa - idx 202512 202506 x.1.sipa) = [0, 0, 0, 1, 1, 1, 1, 1, 2, 3, 5] ∧
    (t202602.zip t202608).map (fun x => x.2.sipa - idx 202606 202512 x.1.sipa) = [0, 0, 1, 0, 1, 1, 1, 1, 2, 2, 2] := by
  decide

/-! ## Cliffs between categories -/

/-- What one centavo over each limit costs in a year under the table in force from August 2026, in centavos:
from A to B, B to C, and so on to J to K. For services the worst are G to H ($ 3.508.724,88), H to I
($ 5.292.494,16) and J to K ($ 5.365.755,36). -/
theorem saltos_202608 :
    saltos t202608 .servicios = [8222280, 11569248, 22311372, 42238224, 37167312, 95434476, 350872488, 529249416,
      244262280, 536575536] ∧
    saltos t202608 .venta = [8222280, 9781800, 21641076, 30843240, 25995768, 34661280, 190895952, 188517324,
      126961092, 145571460] := by decide

/-- Receipts less the year's monthly amounts. -/
def neto (t : Table) (a : Actividad) (ingresos : Int) : Option Int :=
  (costoAnual t a ingresos).map fun c => ingresos - c

/-- **A service provider at the top of category H (August 2026 table).** With receipts of $ 81.924.660,37 the
year costs $ 6.272.480,16 at twelve monthly amounts. One centavo more and twelve months in category I cost
$ 11.564.974,32. Receipts $ 5.292.494,15 above the limit still leave one centavo less than stopping at the limit.
Categories are revised each semester (Anexo art. 9), so the twelve-month figure is the cost of staying there a year. -/
theorem cliff_H_I : costoAnual t202608 .servicios 8192466037 = some 627248016 ∧
    costoAnual t202608 .servicios 8192466038 = some 1156497432 ∧
    neto t202608 .servicios (8192466037 + 529249415) = some (8192466037 - 627248016 - 1) := by decide

/-- Above category K the regime ends: $ 126.610.838,75 of receipts is in, one centavo more is out. -/
theorem exclusion : (porIngresos t202608 12661083875).isSome = true ∧ porIngresos t202608 12661083876 = none := by
  decide

/-- Limits and monthly amounts both rise from each category to every later one. -/
def Ordenada (t : Table) (a : Actividad) : Prop :=
  t.Pairwise fun r s => r.ingresos ≤ s.ingresos ∧ r.cuota a ≤ s.cuota a

theorem ordenadas : ∀ t ∈ tablas, ∀ a, Ordenada t a := by
  intro t ht a
  simp only [tablas, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> cases a <;> unfold Ordenada <;> decide

/-- **Within the regime the monthly amount never falls when receipts rise**, for any table whose limits and
amounts are in order. -/
theorem cuota_mono : ∀ (t : Table) (a : Actividad), Ordenada t a → ∀ (x y : Int) (r s : Row), x ≤ y →
    porIngresos t x = some r → porIngresos t y = some s → r.cuota a ≤ s.cuota a
  | [], _, _, _, _, _, _, _, hx, _ => by simp [porIngresos] at hx
  | r0 :: t, a, hp, x, y, r, s, hxy, hx, hy => by
    unfold Ordenada at hp
    rw [List.pairwise_cons] at hp
    simp only [porIngresos, List.find?_cons] at hx hy
    by_cases h1 : y ≤ r0.ingresos
    · have h2 : x ≤ r0.ingresos := by omega
      simp [h1] at hy
      simp [h2] at hx
      subst hx; subst hy
      exact Int.le_refl _
    · simp [h1] at hy
      by_cases h2 : x ≤ r0.ingresos
      · simp [h2] at hx
        subst hx
        exact (hp.1 s (List.mem_of_find?_eq_some hy)).2
      · simp [h2] at hx
        exact cuota_mono t a hp.2 x y r s hxy hx hy

end ArTax.Monotributo
