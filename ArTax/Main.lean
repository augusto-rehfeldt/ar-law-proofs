import ArTax.Ganancias.Theorems
import ArTax.Monotributo.Theorems
import ArTax.BienesPersonales

/-!
# artax: the models from the command line

One case per line on standard input, fields separated by semicolons, amounts in pesos (1234567.89):

* G;year;renta;neta;conyuge;hijos;incapacitados : impuesto a las ganancias, annual assessment. year is 2025 or
  2026; renta is e (employee, art. 82 a to c), a (self-employed) or n (new professional); conyuge is - for none or
  the spouse's net income of the year.
* M;tabla;actividad;ingresos;alquileres : Monotributo. tabla is 202502, 202508, 202602 or 202608; actividad is s
  (services) or v (sales).
* B;year;casa;otros : bienes personales, year 2023, 2024 or 2025; the home and all other taxable assets.

One line of key=value pairs comes back for each case, or ERR and the line.
-/

open ArTax

/-- Pesos with up to two decimals, to centavos. -/
def parsePesos (s : String) : Option Int := do
  let s := s.trimAscii.toString
  let (neg, s) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  let c : Nat ← match s.splitOn "." with
    | [w] => (· * 100) <$> w.toNat?
    | [w, f] =>
      let f := if f.length == 1 then f ++ "0" else f
      if f.length != 2 then none else (fun a b => a * 100 + b) <$> w.toNat? <*> f.toNat?
    | _ => none
  pure (if neg then -(c : Int) else c)

/-- Centavos as pesos with two decimals. -/
def fmt (c : Int) : String :=
  let a := c.natAbs
  let f := a % 100
  (if c < 0 then "-" else "") ++ toString (a / 100) ++ "." ++ (if f < 10 then "0" else "") ++ toString f

def runGanancias (y r neta cony hijos inc : String) : Option String := do
  let per ← match y with
    | "2025" => some Ganancias.p2025
    | "2026" => some Ganancias.p2026
    | _ => none
  let renta ← match r with
    | "e" => some Ganancias.Renta.empleado
    | "a" => some Ganancias.Renta.autonomo
    | "n" => some Ganancias.Renta.nuevo
    | _ => none
  let conyuge ← if cony == "-" then some none else some <$> parsePesos cony
  let p : Ganancias.Persona :=
    { renta, neta := ← parsePesos neta, conyuge, hijos := ← hijos.toNat?, hijosIncapacitados := ← inc.toNat? }
  let d := per.ded
  pure s!"mni={fmt d.mni};cargas={fmt (Ganancias.cargas d p)};especial={fmt (Ganancias.especial d p)};doceava={fmt (Ganancias.doceava d p)};deducciones={fmt (Ganancias.deducciones d p)};imponible={fmt (Ganancias.imponible d p)};impuesto={fmt (Ganancias.impuesto per p)}"

def runMonotributo (tab act ing alq : String) : Option String := do
  let t ← match tab with
    | "202502" => some Monotributo.t202502
    | "202508" => some Monotributo.t202508
    | "202602" => some Monotributo.t202602
    | "202608" => some Monotributo.t202608
    | _ => none
  let a ← match act with
    | "s" => some Monotributo.Actividad.servicios
    | "v" => some Monotributo.Actividad.venta
    | _ => none
  let i ← parsePesos ing
  let q ← parsePesos alq
  match Monotributo.categoria t i q with
  | none => pure "categoria=excluido"
  | some r =>
    let k := (t.findIdx? (· == r)).getD 0
    pure s!"categoria={("ABCDEFGHIJK".toList.getD k '?')};limite={fmt r.ingresos};cuota={fmt (r.cuota a)};anual={fmt (12 * r.cuota a)}"

def runBienes (y casa otros : String) : Option String := do
  let p ← match y with
    | "2023" => some BienesPersonales.p2023
    | "2024" => some BienesPersonales.p2024
    | "2025" => some BienesPersonales.p2025
    | _ => none
  let b : BienesPersonales.Bienes := ⟨← parsePesos casa, ← parsePesos otros⟩
  pure s!"mni={fmt p.mni};casaExenta={fmt p.casa};gravados={fmt (BienesPersonales.gravados p b)};base={fmt (BienesPersonales.base p b)};impuesto={fmt (BienesPersonales.impuesto p b)}"

def runLine (line : String) : Option String :=
  match (line.splitOn ";").map (·.trimAscii.toString) with
  | ["G", y, r, neta, cony, hijos, inc] => runGanancias y r neta cony hijos inc
  | ["M", tab, act, ing, alq] => runMonotributo tab act ing alq
  | ["B", y, casa, otros] => runBienes y casa otros
  | _ => none

partial def loop (i o : IO.FS.Stream) : IO Unit := do
  let line ← i.getLine
  if line.isEmpty then return
  let line := line.trimAscii.toString
  if !line.isEmpty then
    o.putStrLn ((runLine line).getD s!"ERR;{line}")
  loop i o

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
