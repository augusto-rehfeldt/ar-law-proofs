import ArLegal.Basic

/-!
# Ganancias: articles 31 and 184 still point at article 32, repealed in 2024

Source: InfoLEG, Ley de Impuesto a las Ganancias, texto ordenado por Decreto 824/2019 (`sources/infoleg/lig_texact.htm`).
The ordering decree took effect "el día siguiente al de su publicación en el Boletín Oficial" (its art. 2); the page
shows publication on 06/12/2019 ("e. 06/12/2019"), so the ordered text is modelled from 7 December 2019.

* Art. 31, third paragraph (no amendment note): "Los importes mensuales a computar, serán los que se determinen
  aplicando el procedimiento a que se refiere el tercer párrafo del artículo 32."
* Art. 184 (no amendment note): "A los fines de la actualización prevista en el artículo 32, el importe establecido en
  el artículo 29 se considerará vigente al 31 de diciembre de 1985."
* Art. 32 is now only the note "(Artículo derogado por art. 70 inciso c) de la Ley N° 27.743 B.O. 08/07/2024.
  Vigencia: a partir del día de su publicación en el Boletín Ofical y surtirá efecto a partir del año fiscal 2024)".
  Its former text is not on the page, so it is not quoted or modelled here: only its existence matters.
* Art. 29 still reads "... se podrán deducir los gastos de sepelio ... hasta la suma de PESOS CUATRO CENTAVOS ($ 0,04)
  ...". Art. 184 is the only provision of the ordered text that ties that amount to the update in art. 32.
* Art. 30 was substituted by art. 71 of the same Ley 27.743 (same B.O.) and now carries its own update rule: "Los
  montos previstos en este artículo se ajustarán semestralmente, a partir del año fiscal 2025, inclusive, en los meses
  de enero y julio, por el coeficiente que surja de la variación del Índice de Precios al Consumidor (IPC) ...".

The repeal "surtirá efecto a partir del año fiscal 2024", that is from 1 January 2024, earlier than publication. The
model uses the publication date, the later of the two, so every "from 8 July 2024" statement below also holds under the
retroactive reading.
-/

namespace ArLegal.LigArt32

def ordered : Date := 20191207
def repealedOn : Date := 20240708
def today : Date := 20261124

/-- Art. 31, third paragraph. -/
def art31_3 : Provision := fun d =>
  if ordered ≤ d then some "Los importes mensuales a computar, serán los que se determinen aplicando el procedimiento a que se refiere el tercer párrafo del artículo 32." else none

/-- Art. 184. -/
def art184 : Provision := fun d =>
  if ordered ≤ d then some "A los fines de la actualización prevista en el artículo 32, el importe establecido en el artículo 29 se considerará vigente al 31 de diciembre de 1985." else none

/-- Art. 32: in the ordered text until its repeal; its words are not modelled. -/
def art32 : Provision := fun d => if ordered ≤ d ∧ d < repealedOn then some "(texto del artículo 32, t.o. 2019)" else none

/-- Art. 29, the amount art. 184 refers to. -/
def art29 : Provision := fun d =>
  if ordered ≤ d then some "hasta la suma de PESOS CUATRO CENTAVOS ($ 0,04)" else none

/-- Art. 30, last paragraph, as substituted by Ley 27.743 art. 71. -/
def art30_update : Provision := fun d =>
  if repealedOn ≤ d then some "Los montos previstos en este artículo se ajustarán semestralmente, a partir del año fiscal 2025, inclusive, en los meses de enero y julio, por el coeficiente que surja de la variación del Índice de Precios al Consumidor (IPC)" else none

def monthly : Remission := { citing := art31_3, target := art32 }
def update184 : Remission := { citing := art184, target := art32 }

theorem art32_repealed : repealedFrom art32 repealedOn := by
  intro d hd
  have : ¬ d < repealedOn := Nat.not_lt.mpr hd
  simp [art32, this]

/-- **Art. 31, third paragraph, is a dead remission** from 8 July 2024 on. -/
theorem monthly_dead : ∀ d, repealedOn ≤ d → monthly.operative d = false :=
  dead_remission monthly repealedOn art32_repealed

/-- **Art. 184 is a dead remission** from 8 July 2024 on. -/
theorem update184_dead : ∀ d, repealedOn ≤ d → update184.operative d = false :=
  dead_remission update184 repealedOn art32_repealed

/-- Both citing provisions are still in the ordered text today. -/
theorem citing_in_force_today : inForce art31_3 today = true ∧ inForce art184 today = true := by decide

/-- Sanity check: both remissions worked the day before the repeal was published. -/
theorem worked_before : monthly.operative 20240707 = true ∧ update184.operative 20240707 = true := by decide

/-- Today art. 29 still names four centavos, and the remission that tied it to an update cannot operate. -/
theorem sepelio_frozen : art29 today = some "hasta la suma de PESOS CUATRO CENTAVOS ($ 0,04)" ∧
    update184.operative today = false :=
  ⟨by decide, update184_dead today (by decide)⟩

/-! ## The counter-reading

Art. 31 is not a charging rule but a computation rule for deductions, so the ban on analogy in Ley 11.683 art. 1 does
not obviously bar reading "el tercer párrafo del artículo 32" as the update rule that replaced it in art. 30. Read that
way the remission operates again; Lean shows the defect is exactly the literal reading plus the repeal. The words of
the old third paragraph cannot be compared with the new art. 30 from the source, so whether the reading is faithful is
not something this file can settle. Art. 184 has no such successor: art. 30's new rule updates "los montos previstos en
este artículo", and art. 29 is not among them. -/

theorem monthly_read_as_art30 : ∀ d, repealedOn ≤ d → (monthly.readAs art30_update).operative d = true := by
  intro d hd
  have h1 : ordered ≤ d := Nat.le_trans (by decide) hd
  exact readAs_operative monthly art30_update d (by simp [monthly, inForce, art31_3, h1])
    (by simp [inForce, art30_update, hd])

end ArLegal.LigArt32
