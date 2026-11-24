import ArLegal.Basic

/-!
# IVA: three articles still point at Título V (responsables no inscriptos), repealed in 2004

Source: InfoLEG, Ley de Impuesto al Valor Agregado, texto ordenado por Decreto 280/97 (`sources/infoleg/iva_texact.htm`).
The decree is dated 26/3/97 on the page (its B.O. date is not on the page), so the ordered text is modelled from that
day; nothing below depends on it beyond "before 2004".

* Título V "RESPONSABLES NO INSCRIPTOS" is now only the note "(Título V derogado por art. 1°, inciso a), punto 4 de la
  Ley N° 25.865 B.O. 19/1/2004. Vigencia: a partir del día de su publicación en el Boletín Oficial. Las disposiciones
  contenidas en el Título I de la norma de referencia surtirán efectos a partir de la fecha que disponga el Poder
  Ejecutivo nacional, la que no podrá superar los ciento ochenta (180) días contados desde la fecha de publicación
  oficial.)" No article of the title is left in the text: the last article before it is art. 28 (Título IV) and the
  first after it is art. 36 (Título VI). The page itself places art. 32 in Título V (art. 12: "el segundo párrafo del
  artículo 32 del referido Título") and art. 29 too (Antecedentes: "Título V, artículo 29 sustituido por art. 2º de la
  Ley N° 24.977"); arts. 30 to 35 are placed there by the numbering gap.
* Art. 12, inciso a), last paragraph: "En ningún caso dará lugar a cómputo de crédito fiscal alguno el gravamen que se
  hubiere liquidado a los adquirentes de acuerdo con lo dispuesto en el Título V, salvo cuando se trate del caso
  previsto en el segundo párrafo del artículo 32 del referido Título."
* Art. 36, first paragraph: "Los sujetos pasivos del impuesto mencionados en el artículo 4º deberán inscribirse en la
  DIRECCION GENERAL IMPOSITIVA en la forma y tiempo que la misma establezca, salvo cuando, tratándose de responsables
  comprendidos en el Título V, hagan uso de la opción que el mismo autoriza."
* Art. 47, third paragraph: "... a que se refieren los artículos 13, 32, y 35."

## When did the repeal take effect

The note defers the effects of "el Título I de la norma de referencia" to a date the Executive sets, at most 180 days
after 19 January 2004. The page does not say which date was set, nor (outside the note) that art. 1 belongs to Título I
of Ley 25.865. So the effect date `e` is a parameter: every theorem holds for any `e`, and the headline uses only the
statutory ceiling. 19 January 2004 plus 180 days is 17 July 2004 (2004 is a leap year: 12 + 29 + 31 + 30 + 31 + 30 + 17);
the model takes 18 July 2004 to allow for either counting convention.
-/

namespace ArLegal.IvaTituloV

def ordered : Date := 19970326
def published : Date := 20040119
def ceiling : Date := 20040718
def today : Date := 20261124

/-- Título V (and each of its articles), in force until the repeal takes effect on `e`. -/
def tituloV (e : Date) : Provision := fun d => if ordered ≤ d ∧ d < e then some "RESPONSABLES NO INSCRIPTOS" else none

/-- The exception at the end of art. 36, first paragraph. -/
def art36_exception : Provision := fun d =>
  if ordered ≤ d then some "salvo cuando, tratándose de responsables comprendidos en el Título V, hagan uso de la opción que el mismo autoriza" else none

/-- The exception at the end of art. 12, inciso a). -/
def art12_exception : Provision := fun d =>
  if ordered ≤ d then some "salvo cuando se trate del caso previsto en el segundo párrafo del artículo 32 del referido Título" else none

def registration (e : Date) : Remission := { citing := art36_exception, target := tituloV e }
def creditException (e : Date) : Remission := { citing := art12_exception, target := tituloV e }

theorem tituloV_repealed (e : Date) : repealedFrom (tituloV e) e := by
  intro d hd
  have : ¬ d < e := Nat.not_lt.mpr hd
  simp [tituloV, this]

/-- Whatever date the repeal took effect, both exceptions are dead from that date on. -/
theorem dead_from_effect (e : Date) :
    ∀ d, e ≤ d → (registration e).operative d = false ∧ (creditException e).operative d = false :=
  fun d hd => ⟨dead_remission (registration e) e (tituloV_repealed e) d hd,
               dead_remission (creditException e) e (tituloV_repealed e) d hd⟩

/-- **Headline.** For any effect date the note allows (on or before the 180-day ceiling), the exceptions in arts. 12
and 36 have been dead since 18 July 2004 at the latest, and both are still in the text today. -/
theorem dead_since_ceiling (e : Date) (he : e ≤ ceiling) :
    (∀ d, ceiling ≤ d → (registration e).operative d = false ∧ (creditException e).operative d = false) ∧
    inForce art36_exception today = true ∧ inForce art12_exception today = true :=
  ⟨fun d hd => dead_from_effect e d (Nat.le_trans he hd), by decide, by decide⟩

/-! ## The counter-theorem: the defect rests on the effect date

Before the effect date the title was still law and the exception in art. 36 could be invoked. So the dead window
starts at `e`, not at publication: on any day between publication and `e` the remission operates. -/

theorem operative_before_effect (e d : Date) (h1 : published ≤ d) (h2 : d < e) :
    (registration e).operative d = true := by
  have h0 : ordered ≤ d := Nat.le_trans (by decide) h1
  simp [Remission.operative, registration, inForce, art36_exception, tituloV, h0, h2]

end ArLegal.IvaTituloV
