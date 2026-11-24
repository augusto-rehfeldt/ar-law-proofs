# ar-law-proofs

Machine-checked models of Argentine national tax law, in Lean 4 (core library only: no Mathlib, no sorry, no
native_decide). An Argentine counterpart of the lean-proofs folder of lexifina/global-law.

* **ArTax**: executable models written from the statutes, checked against the tables ARCA publishes and INDEC's
  price index, with theorems about them. What they flag is in [FINDINGS.md](FINDINGS.md).
* **ArLegal**: provisions over time and certified dead references between tax statutes; see ArLegal/FINDINGS.md.

| Module | Law | Proved |
|---|---|---|
| ArTax/Ganancias | Ley de Impuesto a las Ganancias arts. 30 and 94, individuals, 2025 and 2026 | no cliff on the scale, monotone tax, spouse and pensioner cliffs, ARCA's tables rebuilt from the index, the January 2025 and September 2024 adjustments, a misprint |
| ArTax/Sociedades | same Ley, art. 73 company scale, 2021 to 2026 | no cliff, ARCA's 2023 to 2026 scales from the statute's rule, the 2022 exception |
| ArTax/Monotributo | Ley 24.977 Anexo, tables Feb 2025 to Aug 2026 | exact indexation, category cliffs, exclusion |
| ArTax/BienesPersonales | Ley 23.966 Título VI, 2023 to 2025 | ARCA's 2024 and 2025 amounts from the statute's rule, the home cliff, the per-property rental exemption |
| ArTax/IVA | Ley de IVA art. 28 | the tax along a chain is the rate on the last price |
| ArTax/Procedimiento | Ley 11.683 arts. 38, 45, 46, 49, 49 bis, 159 | earlier is never dearer, fraud early against omission late, stale thresholds |

Amounts are integer centavos throughout. Rounding is explicit: half up in the tax and index computations; the
fines of Ley 11.683 drop any fraction of a centavo.

## Run

    python tools/fetch.py        # official sources into sources/ (git-ignored), hashes into SOURCES.md
    python tools/extract.py      # sources -> data/tables.json (needs pdftotext)
    python tools/gen_lean.py     # data/tables.json -> ArTax/Data/*.lean
    python tools/gen_refs.py     # statutes -> data/refs.json and ArLegal/Generated/Tax.lean (see its --help)
    lake build                   # checks every theorem; needs elan
    echo "B;2025;1346548156.00;384728044.57" | .lake/build/bin/artax

artax reads one case per line (formats in ArTax/Main.lean) and prints the computed tax.

## Check

    python -B -m unittest -q test_tools test_gen_refs    # from tools/: offline, no Lean needed
    python tools/check.py                                # no unproved statement, clean build, axioms of every theorem, calculator

## Limits

The models cover what each module's header says and nothing else: no valuation rules, no provincial taxes, no
corporate tax base. ARCA's 2024 PDFs cannot be read by machine (broken font map), so 2024 figures are derived from
the statute. The bienes personales home thresholds after 2023 are the statute's rule applied to the index, not compared with
a published figure. Nothing here is legal or tax advice.
