/-!
# The model: provisions over time and provisions that apply by reference

A small model of statute law over time, enough to state "this provision points at a provision that is gone" as a
theorem that Lean checks.

* A **date** is a natural number written `YYYYMMDD` (`20240708` is 8 July 2024). For real calendar dates numeric order
  is calendar order, so `20240708 ≤ d` reads "on or after 8 July 2024".
* A **provision** (artículo, inciso, título) is its text as a function of the date: `some text` while it is in force,
  `none` before it exists and after it is repealed ("derogado"). InfoLEG keeps only a note in place of a repealed
  provision; that note is `none` here.
* A **remission** ("norma de remisión") is a provision that applies by pointing at another one: "el procedimiento a
  que se refiere el tercer párrafo del artículo 32". The rule it relies on is stated once, as a definition: it can be
  applied on a date only if both it and the provision it names are in force that day. Ley 11.683, art. 1, second
  paragraph (t.o. 1998) is why the reference is read as written in tax matters: "No se admitirá la analogía para
  ampliar el alcance del hecho imponible, de las exenciones o de los ilícitos tributarios." Each case says where a
  court could read the reference differently, and proves what would follow.
-/

namespace ArLegal

/-- A date written as `YYYYMMDD`. -/
abbrev Date := Nat

/-- A provision: its text on each date; `none` when it does not exist (not yet enacted, repealed, never enacted). -/
abbrev Provision := Date → Option String

/-- In force on `d`: it has text on `d`. -/
def inForce (p : Provision) (d : Date) : Bool := (p d).isSome

/-- Repealed from `r`: no text on any date from `r` on. -/
def repealedFrom (p : Provision) (r : Date) : Prop := ∀ d, r ≤ d → p d = none

/-- Never enacted: no text on any date (a number nobody ever filled). -/
def neverEnacted (p : Provision) : Prop := ∀ d, p d = none

/-- A provision that applies by reference to another. -/
structure Remission where
  citing : Provision  -- the provision that refers
  target : Provision  -- the provision it names

/-- **The rule.** A remission operates on `d` only if it and the provision it names are both in force on `d`. -/
def Remission.operative (x : Remission) (d : Date) : Bool := inForce x.citing d && inForce x.target d

/-- **Dead remission.** If the provision named is repealed from `r`, the remission cannot operate on any date from
`r` on, whatever its own text says and however long it stays on the statute book. -/
theorem dead_remission (x : Remission) (r : Date) (h : repealedFrom x.target r) :
    ∀ d, r ≤ d → x.operative d = false := by
  intro d hd
  simp [Remission.operative, inForce, h d hd]

/-- **Phantom remission.** If the provision named was never enacted, the remission never operates. -/
theorem phantom_remission (x : Remission) (h : neverEnacted x.target) : ∀ d, x.operative d = false := by
  intro d
  simp [Remission.operative, inForce, h d]

/-- The same citing words read as pointing at another provision (a successor article, say). -/
def Remission.readAs (x : Remission) (q : Provision) : Remission := { citing := x.citing, target := q }

/-- **The counter-reading.** Read as pointing at a provision in force, the remission operates whenever the citing
provision is in force too. A defect certified here is the literal reading plus the repeal, nothing more. -/
theorem readAs_operative (x : Remission) (q : Provision) (d : Date)
    (hc : inForce x.citing d = true) (hq : inForce q d = true) : (x.readAs q).operative d = true := by
  simp [Remission.readAs, Remission.operative, hc, hq]

/-! ## Histories and certificates

A generated flag does not carry text, only a dated record of whether each provision existed: newest entry first,
`(from, true)` for "in force from", `(from, false)` for "gone from". The generator (`tools/gen_refs.py`) writes these
records from the InfoLEG notes; Lean evaluates each certificate, and the soundness theorem below says once for all
what a certificate that evaluates to `true` proves. -/

/-- A provision's dated record, newest first. -/
abbrev History := List (Date × Bool)

/-- Whether the record says the provision exists on `d`: the newest entry dated on or before `d` decides. -/
def History.holds : History → Date → Bool
  | [], _ => false
  | (t, v) :: older, d => if t ≤ d then v else History.holds older d

/-- The provision a record describes (text is not needed here, only existence). -/
def History.toProvision (h : History) : Provision := fun d => if h.holds d then some "" else none

theorem History.gone_from (r : Date) (older : History) :
    repealedFrom (History.toProvision ((r, false) :: older)) r := by
  intro d hd
  simp [History.toProvision, History.holds, hd]

/-- A flag: the record of the citing provision and of the provision it names. -/
structure RefFlag where
  citing : History
  target : History

def RefFlag.remission (f : RefFlag) : Remission :=
  { citing := f.citing.toProvision, target := f.target.toProvision }

/-- Certified on `today`: the target's newest entry is "gone from r" with `r ≤ today`, and the citing provision is in
force on `today`. Computable, so `decide` checks it. -/
def RefFlag.certified (f : RefFlag) (today : Date) : Bool :=
  match f.target with
  | (r, false) :: _ => decide (r ≤ today) && f.citing.holds today
  | _ => false

/-- The citing provision was rewritten (substituted or inserted) after its target was gone: the legislature touched
it and kept the dead reference. -/
def RefFlag.reenacted (f : RefFlag) : Bool :=
  match f.target, f.citing with
  | (r, false) :: _, (t, true) :: _ => decide (r < t)
  | _, _ => false

/-- **Soundness of certificates.** A certified flag names a date `r`, not after `today`, from which the citing
provision cannot operate, although it is still in force on `today`. -/
theorem RefFlag.certified_sound (f : RefFlag) (today : Date) (h : f.certified today = true) :
    ∃ r, r ≤ today ∧ f.citing.holds today = true ∧ ∀ d, r ≤ d → f.remission.operative d = false := by
  unfold RefFlag.certified at h
  split at h
  · rename_i r older heq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨r, h.1, h.2, ?_⟩
    have hg : repealedFrom f.target.toProvision r := by rw [heq]; exact History.gone_from r older
    exact dead_remission f.remission r hg
  · simp at h

/-- Soundness for a whole list at once: if every flag is certified, every flag is a dead remission. -/
theorem RefFlag.all_sound (fs : List RefFlag) (today : Date) (h : fs.all (·.certified today) = true) :
    ∀ f ∈ fs, ∃ r, r ≤ today ∧ f.citing.holds today = true ∧ ∀ d, r ≤ d → f.remission.operative d = false := by
  intro f hf
  exact RefFlag.certified_sound f today (List.all_eq_true.mp h f hf)

end ArLegal
