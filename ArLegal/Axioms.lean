import ArLegal.Basic
import ArLegal.Cases.LigArt32
import ArLegal.Cases.IvaTituloV
import ArLegal.Generated.Tax
import ArLegal.Generated.Corpus000

/-! Which axioms the headline theorems rest on. Expected: none beyond Lean's core
(`propext`, `Quot.sound`, `Classical.choice` at most); no `sorryAx`, no `Lean.ofReduceBool`. -/

#print axioms ArLegal.dead_remission
#print axioms ArLegal.phantom_remission
#print axioms ArLegal.RefFlag.certified_sound
#print axioms ArLegal.LigArt32.monthly_dead
#print axioms ArLegal.LigArt32.sepelio_frozen
#print axioms ArLegal.LigArt32.monthly_read_as_art30
#print axioms ArLegal.IvaTituloV.dead_since_ceiling
#print axioms ArLegal.IvaTituloV.operative_before_effect
#print axioms ArLegal.Generated.Tax.certified
#print axioms ArLegal.Generated.Tax.all_dead
#print axioms ArLegal.Generated.Corpus000.certified
#print axioms ArLegal.Generated.Corpus000.all_dead
