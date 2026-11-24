# Findings: references to repealed provisions

Certified means the certificate evaluates true in ArLegal/Generated/*.lean; RefFlag.certified_sound then proves that
from the repeal date on the citing provision cannot operate by its reference, though it is in force on 24/11/2026.
The rule is the literal reading; each hand-written case also proves what a successor reading would give.

## Counts

| | found | certified | rejected by hand | ambiguous, not certified |
|---|---|---|---|---|
| Six tax statutes (InfoLEG) | 7 | 7 | 0 | 61 |
| Corpus clone lexifina/argentina-law, same-act references | 22 | 19 | 3 | |

## Tax statutes

* **T006, T007. Ganancias arts. 31 and 184 point at art. 32**, repealed by art. 70 inc. c) of Ley 27.743 (B.O.
  08/07/2024, effect from fiscal year 2024; the model uses the later date). Art. 31, third paragraph: "...el
  procedimiento a que se refiere el tercer párrafo del artículo 32." Art. 184: "A los fines de la actualización
  prevista en el artículo 32, el importe establecido en el artículo 29 se considerará vigente al 31 de diciembre de
  1985." Art. 184 is the only provision tying the funeral deduction of art. 29, which still reads "PESOS CUATRO
  CENTAVOS ($ 0,04)", to an update, so that amount has no update rule left (LigArt32.sepelio_frozen). For art. 31,
  reading the reference as art. 30's new update rule makes it operate again (LigArt32.monthly_read_as_art30). The
  former text of art. 32 is not on the page, so whether that reading is faithful is not established.
* **T001 to T005. IVA arts. 12, 36 and 47 point at Título V and its arts. 32 and 35**, repealed by art. 1 inc. a)
  pto. 4 of Ley 25.865 (B.O. 19/1/2004). The repeal's effect was deferred to a date set by the Executive, at most
  180 days later; that date is not in the source, so the certificate uses the ceiling, 18/07/2004, and the case
  file proves the result for any effect date up to it. Art. 35 is placed in Título V from the numbering gap.
  Leftovers of an abolished regime.
* **Ambiguous, 61, not certified**: 12 cite the 1997 numbering of Ganancias (one the 1978 numbering of Ley 11.683);
  14 are a bare "de la ley"; 35 are "dicha ley", possessives or non-unique numbers.
* **Not detected**: repeals of a paragraph, punto or apartado (Ganancias arts. 82 and 94; IVA arts. 4, 7, 12, 19,
  36, 39; Ley 11.683 arts. 35 and 101). Example of a reference left unchecked: Ganancias art. 158, "último párrafo
  del artículo 82".

## Corpus (repeal date is the clone's in-force date, not cross-checked against InfoLEG)

| Flag | Citing | Target | Repealed | Note |
|---|---|---|---|---|
| C0001 | Código Penal art. 23 | art. 213 ter | 06/01/2012, Ley 26.734 | art. 23 amended again 05/01/2013 and kept the reference |
| C0002 | Ley 18.345 art. 52 | art. 15 | 01/04/1998, Ley 24.946 | |
| C0003 | Ley 19.945 art. 100 | art. 74 | 20/06/2012, Ley 26.744 | harmless |
| C0004 to C0006 | LCT art. 191 | arts. 174, 175, 176 | 06/03/2026, Ley 27.802 | art. 191 is a pure remission, now empty |
| C0007, C0008 | Ley 23.298 arts. 74, 77 | art. 46 | 10/10/2002, Ley 25.600 | |
| C0009 | Ley 23.737 art. 29 bis | art. 25 | 19/05/2000, Ley 25.246 | conspiracy still lists the repealed offence |
| C0010 to C0012 | Ley 24.013 arts. 85, 97, 108 | arts. 46, 34, 43 | 03/10/1998, Ley 25.013 | leftovers |
| C0013, C0014 | Ley 24.467 art. 6 | arts. 13, 16 | 20/05/2025, Decreto 339/2025 | |
| C0015 | Ley 26.522 art. 156 | art. 16 | 04/01/2016, DNU 267/2015 | spent |
| C0016 | Ley 26.682 art. 7 | art. 6 | 30/12/2023, DNU 70/2023 | |
| C0017 | Ley 26.993 art. 45 | art. 39 | 03/02/2025, Decreto 55/2025 | |
| C0018 | Ley 27.078 art. 91 | art. 21 | 06/01/2025, Decreto 6/2025 | |
| C0019 | Ley 27.149 art. 84 | art. 75 | 07/01/2016, DNU 257/2015 | |

Rejected: Ley 19.550 art. 386 to art. 371 (the cited words do not match the deleted text); Ley 24.013 art. 119 to
art. 12 and Ley 26.844 art. 73 to art. 50 (repealed by the labour title of DNU 70/2023, suspended by the courts, so
no repeal date can be established).

Not done: references between different acts in the corpus, numbers never enacted, and a cross-check of the corpus
dates against InfoLEG.
