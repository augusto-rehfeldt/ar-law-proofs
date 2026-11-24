import ArTax.Basic

/-!
# Impuesto al valor agregado

Ley de Impuesto al Valor Agregado, texto ordenado 1997 (sources/infoleg/iva_texact.htm), art. 28: "La alícuota del
impuesto será del veintiuno por ciento (21%). [...] Esta alícuota se incrementará al veintisiete por ciento (27%)
para las ventas de gas, energía eléctrica y aguas reguladas por medidor [...] Estarán alcanzados por una alícuota
equivalente al cincuenta por ciento (50%) de la establecida en el primer párrafo [...]".

Rates in hundredths of a per cent. The model is the tax on one sale and the settlement of one taxpayer (débito
fiscal less crédito fiscal, arts. 11 and 12); which goods and services fall under each rate is not modelled. A
negative settlement is counted as such, where art. 24 carries it forward to later periods instead of refunding it.
-/

namespace ArTax.IVA

/-- Art. 28, first paragraph: 21 %. -/
def general : Int := 2100
/-- Art. 28, second paragraph: 27 %. -/
def incrementada : Int := 2700
/-- Art. 28, fourth paragraph: half of the first paragraph's rate. -/
def reducida : Int := general / 2

theorem reducida_es : reducida = 1050 := by decide

/-- The tax on a net price, in ten-thousandths of a centavo (exact). -/
def debito (rate neto : Int) : Int := rate * neto

/-- What one taxpayer settles for a period: tax on its sales less tax charged on its purchases. -/
def saldo (rate ventas compras : Int) : Int := debito rate ventas - debito rate compras

/-- The sum of the settlements along a chain of sales at net prices p₀, p₁, ..., each stage buying at the price
before it and selling at the next. -/
def cadena (rate : Int) : Int → List Int → Int
  | _, [] => 0
  | prev, p :: t => saldo rate p prev + cadena rate p t

/-- The last price of the chain. -/
def final : Int → List Int → Int
  | prev, [] => prev
  | _, p :: t => final p t

/-- **However many stages a good passes through, the tax collected along the chain is the rate on the last net
price** (less the tax on what the first stage bought). The crédito fiscal makes the tax one on final
consumption. -/
theorem cadena_total (rate : Int) : ∀ (prev : Int) (ps : List Int),
    cadena rate prev ps = debito rate (final prev ps) - debito rate prev
  | _, [] => by simp [cadena, final]
  | prev, p :: t => by
    have ih := cadena_total rate p t
    simp only [cadena, final, saldo]
    omega

/-- A sale at $ 100 net at each rate: $ 21, $ 27 and $ 10,50 of tax. -/
theorem ejemplo : [general, incrementada, reducida].map (fun r => rnd (debito r 10000) 10000) = [2100, 2700, 1050] := by
  decide

end ArTax.IVA
