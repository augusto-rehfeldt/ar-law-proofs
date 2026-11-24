import ArTax.Basic

/-!
# Ley 11.683 de Procedimiento Tributario: fines

Texto ordenado 1998 with its amendments up to Ley 27.826 (B.O. 9/10/2026), InfoLEG texto actualizado
(sources/infoleg/ley11683_texact.htm).

* Art. 38: failing to file a return on time "será sancionada, sin necesidad de requerimiento previo, con una multa
  de pesos doscientos veinte mil ($220.000), la que se elevará a pesos cuatrocientos cuarenta mil ($440.000) si se
  tratare de sociedades, asociaciones o entidades de cualquier clase" (amounts set by Ley 27.799 art. 15, B.O.
  2/1/2026, in place of $ 200 and $ 400). Second paragraph: "Si dentro del plazo de QUINCE (15) días a partir de
  la notificación el infractor pagare voluntariamente la multa y presentare la declaración jurada omitida, los
  importes señalados en el párrafo primero de este artículo, se reducirán de pleno derecho a la mitad".
* Art. 49 bis (Ley 27.826 art. 2°): for a MiPyME, an individual, an estate or a non-profit that is not a "Gran
  Contribuyente Nacional", the fines of arts. 38 and 39 "se reducirán de pleno derecho en un veinticinco por
  ciento (25%)".
* Art. 45: omission, "una multa del ciento por ciento (100%) del gravamen dejado de pagar"; 200 % where the
  omission involves transactions with persons abroad; on recidivism 200 % and 300 %.
* Art. 46: fraud, "multa de dos (2) hasta seis (6) veces el importe del tributo evadido".
* Art. 49: a taxpayer who is not a recidivist and puts things right before an inspection order "quedará exento de
  responsabilidad infraccional"; between the order and the "vista previa" the fines of arts. 45 and 46 "se reducirán
  a un cuarto (1/4) de su mínimo legal"; before the vista of art. 17, "a la mitad (1/2)"; within fifteen days of it,
  "a tres cuartos (3/4)"; if the assessment is consented, "al mínimo legal".

Amounts in centavos. A fraction of a centavo in a fine is dropped (integer division); the worked figures divide
exactly. The interest of art. 37 is not modelled: its rate is set by resolution, not by the Ley.
-/

namespace ArTax.Procedimiento

/-! ## Art. 38: not filing on time -/

/-- Art. 38: $ 220.000 for an individual, $ 440.000 for an entity. -/
def multaFormal (entidad : Bool) : Int := if entidad then 44000000 else 22000000

/-- Art. 49 bis: a quarter off for those it covers. -/
def multaFormalReducida (entidad beneficiario : Bool) : Int :=
  if beneficiario then multaFormal entidad * 75 / 100 else multaFormal entidad

/-- Art. 38, second paragraph: half for paying and filing within fifteen days of the notice. -/
def multaFormalVoluntaria (entidad : Bool) : Int := multaFormal entidad / 2

/-- An individual covered by art. 49 bis pays $ 165.000; an entity covered, $ 330.000. Ley 27.799 multiplied the
old amounts by 1 100. -/
theorem art38 : multaFormalReducida false true = 16500000 ∧ multaFormalReducida true true = 33000000 ∧
    multaFormal false = 1100 * 20000 ∧ multaFormal true = 1100 * 40000 := by decide

/-! ## Thresholds the 2026 reform left behind -/

/-- Art. 159 b): the Tribunal Fiscal de la Nación hears appeals against "multas superiores a PESOS VEINTICINCO MIL
($ 25.000)" (amount set by Ley 26.784, B.O. 5/11/2012). -/
def umbralTribunal : Int := 2500000

/-- Arts. 82 and 86: a court claim needs "una suma mayor de DOSCIENTOS PESOS ($ 200)" (Ley 25.795, B.O.
17/11/2003). -/
def umbralDemanda : Int := 20000

/-- **Ley 27.799 multiplied the fines and left the thresholds.** Until 2026 no art. 38 fine ($ 200 or $ 400)
reached the Tribunal Fiscal's threshold. Now the smallest one, $ 110.000 for an individual who pays within fifteen
days, is 4.4 times that threshold and 550 times the court threshold: both filters let everything through. (Were the
art. 49 bis quarter taken off as well, $ 82.500, the same holds.) -/
theorem umbrales_sin_actualizar : 40000 ≤ umbralTribunal ∧
    10 * multaFormalVoluntaria false = 44 * umbralTribunal ∧
    multaFormalVoluntaria false = 550 * umbralDemanda ∧
    umbralTribunal < multaFormalVoluntaria false * 75 / 100 := by decide

/-! ## Arts. 45, 46 and 49: omission, fraud and putting things right -/

/-- When the taxpayer puts things right, in the order of art. 49. -/
inductive Etapa where
  /-- Before an inspection order is notified. -/
  | antesDeOrden
  /-- Between the inspection order and the "vista previa". -/
  | antesDeVistaPrevia
  /-- Before the vista of art. 17. -/
  | antesDeVista
  /-- Accepted within fifteen days of the vista. -/
  | quinceDias
  /-- The assessment is consented. -/
  | consentida
  /-- None of the above. -/
  | ninguna
deriving Repr, DecidableEq

/-- Position in time. -/
def Etapa.orden : Etapa → Nat
  | .antesDeOrden => 0 | .antesDeVistaPrevia => 1 | .antesDeVista => 2
  | .quinceDias => 3 | .consentida => 4 | .ninguna => 5

/-- The fine of art. 45 before any reduction, in per cent of the tax omitted. -/
def omisionPct (exterior reincidente : Bool) : Int :=
  match exterior, reincidente with
  | false, false => 100 | true, false => 200 | false, true => 200 | true, true => 300

/-- Art. 49 applied to a fine whose legal minimum is `minimo` and whose amount without reduction is `plena`
(both in per cent of the tax). A recidivist gets no reduction. -/
def reducida (minimo plena : Int) (reincidente : Bool) (e : Etapa) : Int :=
  if reincidente then plena else
  match e with
  | .antesDeOrden => 0
  | .antesDeVistaPrevia => minimo / 4
  | .antesDeVista => minimo / 2
  | .quinceDias => minimo * 3 / 4
  | .consentida => minimo
  | .ninguna => plena

/-- The fine for omission (art. 45), in centavos, on `impuesto` centavos of tax left unpaid. -/
def multaOmision (impuesto : Int) (exterior reincidente : Bool) (e : Etapa) : Int :=
  impuesto * reducida (omisionPct exterior reincidente) (omisionPct exterior reincidente) reincidente e / 100

/-- The fine for fraud (art. 46): between 2 and 6 times the tax; `veces` is what the judge sets. -/
def multaDefraudacion (impuesto veces : Int) (reincidente : Bool) (e : Etapa) : Int :=
  impuesto * reducida 200 (100 * (max 2 (min 6 veces))) reincidente e / 100

/-- **Putting things right earlier never costs more** (art. 49), for omission and for fraud, whatever the tax
and whatever multiple the fraud fine is set at. -/
theorem antes_es_menos (impuesto veces : Int) (h : 0 ≤ impuesto) (ext rein : Bool) (e f : Etapa)
    (hef : e.orden ≤ f.orden) :
    multaOmision impuesto ext rein e ≤ multaOmision impuesto ext rein f ∧
    multaDefraudacion impuesto veces rein e ≤ multaDefraudacion impuesto veces rein f := by
  have key : ∀ a b : Int, a ≤ b → impuesto * a / 100 ≤ impuesto * b / 100 := fun a b hab =>
    Int.ediv_le_ediv (by decide) (Int.mul_le_mul_of_nonneg_left hab h)
  constructor
  · apply key
    cases ext <;> cases rein <;> cases e <;> cases f <;> simp [Etapa.orden] at hef <;> decide
  · apply key
    cases rein <;> cases e <;> cases f <;> simp [Etapa.orden] at hef <;> simp [reducida] <;> omega

/-- **Before an inspection order there is no fine at all**, even for fraud, unless the taxpayer is a recidivist. -/
theorem espontanea (impuesto veces : Int) (ext : Bool) :
    multaOmision impuesto ext false .antesDeOrden = 0 ∧
    multaDefraudacion impuesto veces false .antesDeOrden = 0 := by
  simp [multaOmision, multaDefraudacion, reducida]

/-- **A recidivist loses every reduction at once.** On $ 1.000.000 of tax omitted and put right between the
inspection order and the vista previa: $ 250.000 of fine for a first offender, $ 2.000.000 for a recidivist. -/
theorem reincidencia : multaOmision 100000000 false false .antesDeVistaPrevia = 25000000 ∧
    multaOmision 100000000 false true .antesDeVistaPrevia = 200000000 := by decide

/-- **Fraud put right early is fined less than an omission left to the end.** A first offender who defrauded and
regularises before the vista previa pays half the tax as fine (a quarter of the minimum of two times); one who
merely omitted and waits for the final assessment pays the whole tax. -/
theorem fraude_temprano (impuesto veces : Int) (h : 0 ≤ impuesto) :
    multaDefraudacion impuesto veces false .antesDeVistaPrevia ≤ multaOmision impuesto false false .ninguna := by
  simp only [multaDefraudacion, multaOmision, reducida, omisionPct]
  exact Int.ediv_le_ediv (by decide) (Int.mul_le_mul_of_nonneg_left (by simp <;> omega) h)

end ArTax.Procedimiento
