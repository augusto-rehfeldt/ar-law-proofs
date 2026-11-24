import ArTax.Scale

/-!
# Impuesto a las ganancias of a resident individual: the statute and the model

Ley de Impuesto a las Ganancias, texto ordenado por Decreto 824/2019, as amended by Ley 27.743 (B.O. 08/07/2024),
InfoLEG texto actualizado (sources/infoleg/lig_texact.htm).

* Art. 30: "Las personas humanas tendrán derecho a deducir de sus ganancias netas: a) En concepto de ganancias no
  imponibles, la suma de pesos tres millones noventa y un mil treinta y cinco ($ 3.091.035) [...]; b) En concepto de
  cargas de familia, siempre que las personas que se indican sean residentes en el país, estén a cargo del
  contribuyente y no tengan en el año ingresos netos superiores a pesos tres millones noventa y un mil treinta y
  cinco ($ 3.091.035) [...]: 1. Pesos dos millones novecientos once mil ciento treinta y cinco ($ 2.911.135) por el
  cónyuge. [...] 2. Pesos un millón cuatrocientos sesenta y ocho mil noventa y seis ($ 1.468.096) por cada hijo,
  hija, hijastro o hijastra menor de dieciocho (18) años o incapacitado para el trabajo. La deducción de este inciso
  [...] se incrementará, para el caso de la del apartado 2, en una (1) vez por cada hijo [...] incapacitado para el
  trabajo. c) En concepto de deducción especial, hasta una suma equivalente al importe que resulte de incrementar el
  monto a que hace referencia el inciso a) del presente artículo en: 1. Dos coma cinco (2,5) veces, cuando se trate
  de ganancias netas comprendidas en el artículo 53 [...] y de ganancias netas incluidas en el artículo 82, excepto
  que queden incluidas en el apartado siguiente. En esos supuestos, el incremento será de tres (3) veces [...] cuando
  se trate de 'nuevos profesionales' o 'nuevos emprendedores' [...]. 2. Tres coma ocho (3,8) veces, cuando se trate
  de ganancias netas comprendidas en los incisos a), b) y c) del artículo 82 citado. Cuando corresponda la aplicación
  de la deducción especial indicada en el inciso c), apartado 2, de este artículo, se añadirá como deducción especial
  la doceava parte del total de deducciones resultantes de la suma de los incisos a), b) y c), apartado 2".
* Art. 94: the scale, nine bands from 5 % to 35 % (baseScale below).
* Both articles end: "Los montos previstos en este artículo se ajustarán semestralmente, a partir del año fiscal
  2025, inclusive, en los meses de enero y julio, por el coeficiente que surja de la variación del Índice de Precios
  al Consumidor (IPC) que suministre el [INDEC], correspondiente al semestre calendario que finalice el mes inmediato
  anterior al de la actualización que se realice."

The amounts of a given period are ARCA's published tables (ArTax/Data/Ganancias.lean); how they follow from the
statute and the index is checked in Indexing.lean.

## What the model covers

One resident individual for one fiscal year: the ganancia neta before personal deductions is an input (wages net
of social-security contributions, or the net result of self-employment), then the art. 30 deductions and the art. 94
scale. Not covered: the general deductions of art. 85 (they are taken before the input), the impuesto cedular (arts. 95 to 99), the 15 % rate of art. 94, third
paragraph, foreign-source income, and the monthly withholding procedure of Resolución General 4003. The specific
deduction for pensions (art. 30, eighth paragraph) is in ArTax/Ganancias/Jubilados.lean.
-/

namespace ArTax.Ganancias

/-- The amounts of art. 30 for one period, in centavos, as ARCA prints them: a), b) 1, b) 2, b) 2 for a child
unable to work, c) 1, c) 1 for "nuevos profesionales/emprendedores", c) 2. -/
structure Deductions where
  mni : Int
  conyuge : Int
  hijo : Int
  hijoIncapacitado : Int
  especial1 : Int
  especial1Nuevos : Int
  especial2 : Int
deriving Repr, DecidableEq

/-! ## The statute's own amounts (Ley 27.743 arts. 71 and 73) -/

/-- Art. 30 a): $ 3.091.035. -/
def baseMni : Int := 309103500
/-- Art. 30 b) 1: $ 2.911.135. -/
def baseConyuge : Int := 291113500
/-- Art. 30 b) 2: $ 1.468.096. -/
def baseHijo : Int := 146809600

/-- Art. 30 c): "el importe que resulte de incrementar el monto [del inciso a)] en" tenths / 10 "veces", read
as ARCA applies it: the amount plus that many times the amount. -/
def incrementar (mni tenths : Int) : Int := rnd (mni * (10 + tenths)) 10

/-- The same words read as a plain multiple: tenths / 10 times the amount. -/
def veces (mni tenths : Int) : Int := rnd (mni * tenths) 10

/-- Art. 94, first paragraph, as printed in the statute. -/
def baseScale : Scale := [
  ⟨0, 0, 5⟩, ⟨120000000, 6000000, 9⟩, ⟨240000000, 16800000, 12⟩, ⟨360000000, 31200000, 15⟩,
  ⟨540000000, 58200000, 19⟩, ⟨1080000000, 160800000, 23⟩, ⟨1620000000, 285000000, 27⟩,
  ⟨2430000000, 503700000, 31⟩, ⟨3645000000, 880350000, 35⟩]

/-! ## The model -/

/-- A fiscal period: ARCA's deductions and scale for the annual assessment. -/
structure Periodo where
  ded : Deductions
  scale : Scale

/-- Which apartado of art. 30 c) the income falls under. -/
inductive Renta where
  /-- Art. 82 a), b), c): public office, employment, pensions. Apartado 2. -/
  | empleado
  /-- Art. 53 worked personally, or other art. 82 income. Apartado 1. -/
  | autonomo
  /-- Apartado 1, "nuevos profesionales" or "nuevos emprendedores". -/
  | nuevo
deriving Repr, DecidableEq

/-- One taxpayer for one year, in centavos. -/
structure Persona where
  renta : Renta := .empleado
  /-- Ganancia neta of the year before the personal deductions of art. 30. -/
  neta : Int
  /-- A spouse (or partner, art. 30 b) 1) resident and dependent: their own net income of the year. -/
  conyuge : Option Int := none
  /-- Children under 18 deducted by this taxpayer. -/
  hijos : Nat := 0
  /-- Children unable to work deducted by this taxpayer. -/
  hijosIncapacitados : Nat := 0

/-- Art. 30 b) 1: the spouse counts only while their net income of the year is not above the inciso a) amount. -/
def conyugeDed (d : Deductions) : Option Int → Int
  | some i => if i ≤ d.mni then d.conyuge else 0
  | none => 0

/-- Art. 30 b): cargas de familia. -/
def cargas (d : Deductions) (p : Persona) : Int :=
  conyugeDed d p.conyuge + d.hijo * p.hijos + d.hijoIncapacitado * p.hijosIncapacitados

/-- The ceiling of the special deduction of art. 30 c) for each kind of income. -/
def topeEspecial (d : Deductions) : Renta → Int
  | .empleado => d.especial2
  | .autonomo => d.especial1
  | .nuevo => d.especial1Nuevos

/-- Art. 30 c): "hasta una suma equivalente": the special deduction cannot exceed the income it is given for. -/
def especial (d : Deductions) (p : Persona) : Int := min (pos p.neta) (topeEspecial d p.renta)

/-- Art. 30 c), second paragraph: a twelfth of a) + b) + c) 2, only where apartado 2 applies. -/
def doceava (d : Deductions) (p : Persona) : Int :=
  match p.renta with
  | .empleado => rnd (d.mni + cargas d p + especial d p) 12
  | _ => 0

/-- All personal deductions of art. 30. -/
def deducciones (d : Deductions) (p : Persona) : Int :=
  d.mni + cargas d p + especial d p + doceava d p

/-- Ganancia neta sujeta a impuesto. -/
def imponible (d : Deductions) (p : Persona) : Int := pos (p.neta - deducciones d p)

/-- The tax of art. 94 on the printed scale, in centavos. -/
def impuesto (per : Periodo) (p : Persona) : Int := per.scale.tax (imponible per.ded p)

end ArTax.Ganancias
