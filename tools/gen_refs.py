"""Find references to repealed provisions in six Argentine national tax statutes and write Lean certificates.

The inputs are the InfoLEG "texto actualizado" pages in ../sources/infoleg (read offline, never fetched). Each page is
reduced to one line per paragraph, cut to the statute body, and split into articles. InfoLEG writes every amendment as
a parenthesised note after the text it touches, for example "(Artículo derogado por art. 70 inciso b) de la Ley N°
27.743 B.O. 08/07/2024. Vigencia: ...)". From those notes the script learns which articles, incisos and titles were
repealed, by which norm and on which date. It then reads every provision still in force and resolves each citation
("artículo 32", "inciso x) del artículo 26", "artículo 45 de la ley 11.683"): a citation of the same statute, or of one
of the other five by number or name, that lands on a repealed unit is a flag. A citation whose words point at some
other act ("de la ley 24.467", "del Código ...", "de la reglamentación") is never flagged; one whose act cannot be told
("de la ley", "de dicha ley", the old numbering of a statute) goes to the ambiguous list instead.

Outputs: ../data/refs.json (flags, ambiguous hits, repeal inventory) and ../ArLegal/Generated/Tax.lean (one RefFlag
certificate per flag, ending in a theorem that states which flags Lean certifies). The run is deterministic.

    python -B tools/gen_refs.py [--today 20261124]
"""
from __future__ import annotations

import argparse
import calendar
import datetime
import html
import json
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SRC = ROOT / "sources" / "infoleg"

# ---------------------------------------------------------------- text

def html_to_lines(raw: str) -> list[str]:
    """One line per HTML paragraph, tags removed, entities decoded, whitespace collapsed."""
    t = re.sub(r"(?is)<(script|style)\b.*?</\1>", " ", raw)
    t = re.sub(r"(?s)<!--.*?-->", " ", t)
    t = re.sub(r"\s+", " ", t)
    t = re.sub(r"(?i)<br\s*/?>|</?p\b[^>]*>|</?div\b[^>]*>|</?h\d\b[^>]*>|</?tr\b[^>]*>|</?li\b[^>]*>", "\n", t)
    t = re.sub(r"<[^>]+>", "", t)
    t = html.unescape(t).replace("\xa0", " ")
    out = []
    for line in t.split("\n"):
        line = re.sub(r"[ \t]+", " ", line).strip()
        if line:
            out.append(line)
    return out


def norm(s: str) -> str:
    """Lowercase without accents, for matching only."""
    return s.lower().translate(str.maketrans("áéíóúü", "aeiouu"))


# ---------------------------------------------------------------- dates

def parse_date(s: str) -> int | None:
    """'08/07/2024' -> 20240708; two-digit years read as 19xx from 50 up, else 20xx. None if not a real date."""
    m = re.fullmatch(r"\s*(\d{1,2})/(\d{1,2})/(\d{2}|\d{4})\s*", s)
    if not m:
        return None
    d, mo, y = int(m.group(1)), int(m.group(2)), int(m.group(3))
    if len(m.group(3)) == 2:
        y += 1900 if y >= 50 else 2000
    if not (1 <= mo <= 12 and 1 <= d <= calendar.monthrange(y, mo)[1]):
        return None
    return y * 10000 + mo * 100 + d


def add_days(d: int, n: int) -> int:
    x = datetime.date(d // 10000, d // 100 % 100, d % 100) + datetime.timedelta(days=n)
    return x.year * 10000 + x.month * 100 + x.day


def next_day(d: int) -> int:
    y, m, dd = d // 10000, d // 100 % 100, d % 100
    if dd < calendar.monthrange(y, m)[1]:
        return d + 1
    if m < 12:
        return y * 10000 + (m + 1) * 100 + 1
    return (y + 1) * 10000 + 101


# ---------------------------------------------------------------- amendment notes

NOTE = re.compile(
    r"\((?P<head>(?!Nota)[^(]{0,160}?)\b(?P<action>derogad[oa]s?|sustituid[oa]s?|incorporad[oa]s?|modificad[oa]s?|"
    r"vetad[oa]s?|observad[oa]s?)\s+por\s+(?P<by>[^(]{0,200}?)\bB\.\s?O\.?\s*(?P<date>\d{1,2}/\d{1,2}/\d{2,4})",
    re.I)
NORM = re.compile(r"(Ley|Decreto(?:-Ley)?|Resoluci[oó]n General|Decreto de Necesidad y Urgencia)\s*(?:N[°º.o]*\s*)?(\d[\d.]*(?:/\d+)?)",
                  re.I)
UNITS = {"articulo": "artículo", "articulos": "artículo", "inciso": "inciso", "incisos": "inciso", "titulo": "título",
         "capitulo": "capítulo", "apartado": "apartado", "apartados": "apartado", "punto": "punto", "puntos": "punto",
         "parrafo": "párrafo", "parrafos": "párrafo", "anexo": "anexo", "subinciso": "subinciso"}


def parse_notes(text: str) -> list[dict]:
    """Every amendment note in a line: what unit, what was done, by which norm, published and in force when."""
    out = []
    for m in NOTE.finditer(text):
        head = m.group("head").strip()
        first = norm(head.split()[0]) if head.split() else ""
        unit = UNITS.get(first, norm(head) or "?")
        bo = parse_date(m.group("date"))
        if bo is None:
            continue
        nm = NORM.search(m.group("by"))
        nxt = NOTE.search(text, m.end())
        rest = text[m.end():min(m.end() + 400, nxt.start() if nxt else len(text))]
        cut = rest.find("(Nota")
        rest = rest if cut < 0 else rest[:cut]
        r = norm(rest)
        cap = re.search(r"no podra superar (?:los |el )?[^()]{0,40}\((\d+)\)\s*dias", r)
        if cap:
            # effects deferred to a date set later, capped at N days from publication: take the cap (one day of
            # slack for the counting convention), the latest date the repeal can have taken effect
            frm, basis = add_days(bo, int(cap.group(1)) + 1), f"latest date allowed: {cap.group(1)} days after B.O., +1"
        elif "dia siguiente" in r and "publicacion" in r:
            frm, basis = next_day(bo), "día siguiente a la publicación"
        elif re.search(r"(a partir del dia de su publicacion|a partir de su publicacion|desde su publicacion|"
                       r"el dia de su publicacion|a partir de la fecha de su publicacion)", r):
            frm, basis = bo, "publicación"
        else:
            frm, basis = bo, "B.O."
        out.append({"unit": unit, "head": head, "action": norm(m.group("action")).rstrip("s").replace("da", "do"),
                    "by": m.group("by").strip(), "norm": f"{nm.group(1).title()} {nm.group(2).rstrip('.')}" if nm else None,
                    "bo": bo, "from": frm, "date_basis": basis, "vigencia": rest.strip()[:300],
                    "note": text[m.start():m.end()] + rest[:200]})
    return out


# ---------------------------------------------------------------- articles

HEADER = re.compile(r"^ART[IÍ]CULO\.?\s*(?P<num>\d+)\s*(?P<suf>bis|ter|quater|quinquies|sexies|septies|octies)?\s*[°º]?"
                    r"(?=\s|[.\-—–:]|$)", re.I)
UNNUMBERED = re.compile(r"^ART[IÍ]CULO\.?\s*(?:\.{2,}|…+|s/n|sin n[uú]mero)", re.I)
TITLE = re.compile(r"^T[IÍ]TULO\s+([IVXL]+)\b")
QUOTE_START = ('"', "“", "«", "'")
INC_LINE = re.compile(r"^(?P<l>[a-zñ])\s*\)\s*(?P<rest>.*)$")


@dataclass
class Article:
    num: str
    title: str | None
    lines: list[str] = field(default_factory=list)
    titled: bool = False

    @property
    def key(self) -> str:
        return f"{self.title}:{self.num}" if self.titled else self.num

    @property
    def unnumbered(self) -> bool:
        return " s/n " in self.num


def is_heading(line: str) -> bool:
    """A section heading inside a statute (no lowercase letters, e.g. 'CONCEPTO DE RESIDENCIA', 'CAPÍTULO II')."""
    return not re.search(r"[a-zñáéíóú]", line) or bool(re.match(r"^CAP[IÍ]TULO\b", line))


def is_epigraph(line: str, nxt: str) -> bool:
    """A short caption standing right before an article or heading ('Domicilio Fiscal', 'Responsabilidad del ...')."""
    if len(line) > 90 or re.search(r"[.:;,)]$", line) or INC_LINE.match(line) or re.match(r"^\d", line):
        return False
    if line.startswith(QUOTE_START) or line.startswith("(") or HEADER.match(line) or UNNUMBERED.match(line):
        return False
    return bool(HEADER.match(nxt) or UNNUMBERED.match(nxt) or TITLE.match(nxt) or (nxt and is_heading(nxt)))


def split_articles(lines: list[str], titled: bool = False) -> list[Article]:
    """Split a statute body into articles. Unnumbered articles are named '<previous> s/n <k>'."""
    arts: list[Article] = []
    title = None
    last_num, sn = "0", 0
    for k, line in enumerate(lines):
        t = TITLE.match(line)
        if t:
            title = t.group(1)
            if titled:
                last_num = "0"
            continue
        nxt = lines[k + 1] if k + 1 < len(lines) else ""
        if is_epigraph(line, nxt):
            continue
        h = HEADER.match(line)
        if h:
            num = h.group("num") + (f" {h.group('suf').lower()}" if h.group("suf") else "")
            arts.append(Article(num, title, [line], titled))
            last_num, sn = num, 0
            continue
        if UNNUMBERED.match(line):
            sn += 1
            arts.append(Article(f"{last_num} s/n {sn}", title, [line], titled))
            continue
        if arts and not is_heading(line):
            arts[-1].lines.append(line)
    return arts


def strip_notes(text: str) -> str:
    """The provision's own words: amendment notes and 'Nota Infoleg' remarks removed."""
    t = text
    for m in reversed(list(NOTE.finditer(t))):
        end = m.end()
        depth = 1
        i = end
        while i < len(t) and depth:      # extend to the note's closing parenthesis
            depth += {"(": 1, ")": -1}.get(t[i], 0)
            i += 1
        t = t[:m.start()] + " " + t[i:]
    t = re.sub(r"\(Nota Infoleg:.*", " ", t, flags=re.I)
    return t


def article_body(a: Article) -> str:
    first = HEADER.sub("", a.lines[0], count=1) if HEADER.match(a.lines[0]) else UNNUMBERED.sub("", a.lines[0], count=1)
    body = " ".join([first] + a.lines[1:])
    return strip_notes(body)


def article_repeal(a: Article) -> dict | None:
    """The repeal note of an article whose text InfoLEG has replaced by that note; None while it has text."""
    notes = [n for line in a.lines for n in parse_notes(line) if n["unit"] == "artículo" and n["action"] == "derogado"]
    if not notes:
        return None
    if re.sub(r"[\s.\-—–:°º…]+", "", article_body(a)):
        return None
    return notes[-1]




def inciso_repeals(a: Article) -> dict[str, dict]:
    """Lettered incisos of an article whose text is only a repeal note."""
    out = {}
    for line in a.lines[1:]:
        m = INC_LINE.match(line)
        if not m:
            continue
        notes = [n for n in parse_notes(line) if n["action"] == "derogado" and n["unit"] in ("inciso", "subinciso")]
        if notes and not re.sub(r"[\s.\-—–:;,…]+", "", strip_notes(m.group("rest"))):
            out[m.group("l")] = notes[-1]
    return out


def title_repeals(lines: list[str]) -> dict[str, dict]:
    """Titles whose heading is followed by a 'Título ... derogado' note."""
    out = {}
    for i, line in enumerate(lines):
        t = TITLE.match(line)
        if not t:
            continue
        for nxt in lines[i + 1:i + 4]:
            if TITLE.match(nxt) or HEADER.match(nxt):
                break
            for n in parse_notes(nxt):
                if n["unit"] == "título" and n["action"] == "derogado":
                    out[t.group(1)] = n
    return out


# ---------------------------------------------------------------- statutes

@dataclass
class Statute:
    key: str
    name: str
    lines: list[str]
    base: int                     # date from which the consolidated text is taken to exist
    titled: bool = False
    base_basis: str = ""

    def __post_init__(self):
        self.articles = split_articles(self.lines, self.titled)
        self.by_key = {}
        for a in self.articles:
            self.by_key.setdefault(a.key, a)
        self.title_rep = title_repeals(self.lines)
        self.gap = self._title_gaps()

    def _title_gaps(self) -> dict[str, dict]:
        """Article numbers missing from the text exactly where a repealed title (with no articles left) sits."""
        out = {}
        order = []                                   # (title, first, last) of numbered articles per title, in order
        seen_titles = []
        for line in self.lines:
            t = TITLE.match(line)
            if t:
                seen_titles.append(t.group(1))
        for tt in seen_titles:
            nums = [int(a.num) for a in self.articles if a.title == tt and a.num.isdigit()]
            order.append((tt, min(nums) if nums else None, max(nums) if nums else None))
        for i, (tt, lo, hi) in enumerate(order):
            if tt not in self.title_rep or lo is not None:
                continue
            prev = next((h for _, _, h in reversed(order[:i]) if h is not None), None)
            nxt = next((l for _, l, _ in order[i + 1:] if l is not None), None)
            if prev is None or nxt is None or nxt - prev < 2 or nxt - prev > 30:
                continue
            for n in range(prev + 1, nxt):
                k = f"{tt}:{n}" if self.titled else str(n)
                if k not in self.by_key:
                    out[k] = dict(self.title_rep[tt], gap_title=tt)
        return out

    def label(self, key: str, inciso: str | None = None) -> str:
        if self.titled and ":" in key:
            t, n = key.split(":", 1)
            s = f"{self.key} tít. {t} art. {n}"
        else:
            s = f"{self.key} art. {key}"
        return s + (f" inc. {inciso})" if inciso else "")


# How each statute is cited from elsewhere. A name alone (no version) is accepted only where the numbering has not
# changed; for Ganancias the 2019 ordering must be named, because the 1997 ordering numbers the articles differently.
REGISTRY = {
    "lig": {"numbers": ("20.628",), "need_version": True, "to": "2019",
            "names": (r"ley de impuesto a las ganancias",), "version": r"(2019|824)"},
    "ley11683": {"numbers": ("11.683",), "to": "1998", "names": (r"ley de procedimiento (tributario|fiscal)",
                                                   r"ley de procedimientos? fiscal(es)?")},
    "iva": {"numbers": ("23.349",), "need_version": True, "to": "1997", "names": (r"ley de impuesto al valor agregado",),
            "version": r"1997"},
    "ley23966": {"numbers": ("23.966",), "names": ()},
    "ley24977": {"numbers": ("24.977",), "names": ()},
    "ley25413": {"numbers": ("25.413",), "names": ()},
}

NUM = r"\d+(?:\s*[°º])?(?:\s+(?:bis|ter|quater|quinquies|sexies))?"
INC = r"[a-zñ]\)"
SEP = r"(?:\s*[,;]\s*(?:(?:y|e|o|u)\s+)?|\s+(?:y|e|o|u)\s+)"
CITE = re.compile(
    rf"(?:(?P<incs>incisos?\s+{INC}(?:{SEP}{INC})*)\s*,?\s*(?:del|de\s+los)\s+)?"
    rf"(?P<word>art[ií]culos?|arts?\.)\s+(?P<nums>{NUM}(?:{SEP}{NUM})*)"
    rf"(?P<tail>\s*,\s*incisos?\s+(?P<tincs>{INC}(?:{SEP}{INC})*))?", re.I)
OWN_INC = re.compile(rf"\bincisos?\s+(?P<incs>{INC}(?:{SEP}{INC})*)\s*,?\s*(?:de\s+este|del\s+presente)\s+art[ií]culo",
                     re.I)
SAME = re.compile(r"^[\s,]*(?:de|del)\s+(?:esta\s+ley|la\s+presente\s+ley|la\s+presente\b|presente\s+ley|"
                  r"(?:el\s+)?presente\s+(?:titulo|capitulo|regimen|anexo)|este\s+(?:titulo|capitulo|regimen|anexo|texto)|"
                  r"la\s+ley\s+del\s+gravamen|esta\s+norma)")
ACT_NUM = re.compile(r"^[\s,]*(?:de|del)\s+(?:la\s+)?ley\s*(?:n[°º.ro]*\s*)?(\d{1,2}\.\d{3}|\d{3,5})\b")
VAGUE = re.compile(r"^[\s,]*(?:de|del)\s+(?:la\s+ley\b(?!\s+de\b)|dicha|dicho|la\s+citada|el\s+citado|la\s+mencionada|"
                   r"el\s+mencionado|la\s+referida|el\s+referido|aquella|aquel|esa|ese|las?\s+leyes?\s+(?:respectivas?|citadas?))")
OTHER = re.compile(r"^[\s,]*(?:de|del|de\s+los|de\s+las)\s+(?:la\s+|el\s+|los\s+|las\s+)?(?:ley|leyes|decreto|codigo|"
                   r"resolucion|reglament|texto\s+ordenado|convenio|constitucion|regimen|anexo|acuerdo|tratado|estatuto|"
                   r"norma|disposicion|cap|titulo|libro|parte|apartado|estatuto|ordenanza|protocolo|carta|"
                   r"impuesto|reforma|presupuesto)")
TITLE_CITE = re.compile(r"\bT[ií]tulo\s+([IVXL]+)\b(?!\s*,?\s*(?:cap[ií]tulo|del?\s+la\s+ley))")
AMENDING = re.compile(r"\b(?:sustit[uú]y|der[oó]g|incorp[oó]r|modif[ií]c|reempl[aá]z|agr[eé]g|supr[ií]m|intercal|"
                      r"sustit[uú]y)[aeáé]n?se\b", re.I)
EMBEDDED_HEAD = re.compile(r"^(?:art[ií]culo|art\.)\s*\d+", re.I)


def own_lines(lines: list[str]) -> list[tuple[int, str]]:
    """The paragraphs that are the provision's own words: stops at an amending clause that introduces new text
    ('Sustitúyese el artículo 5 por el siguiente:'), whose following paragraphs belong to another provision."""
    out = []
    for i, line in enumerate(lines):
        if line.startswith(QUOTE_START):
            continue
        out.append((i, line))
        if AMENDING.search(line) and re.search(r"(:\s*$|por el siguiente|el siguiente texto|los siguientes)", line):
            break
    return out
INTRO_OTHER = re.compile(r"\b(?:del|de la)\s+(?:c[oó]digo|ley\s+(?:n[°º.]*\s*)?\d|decreto|constituci[oó]n)[^:;.]*:", re.I)
POSSESSIVE = re.compile(r"\b(su|sus|dicho|dicha|cuyo|cuya|cuyos|cuyas)\s+$", re.I)


def _nums(s: str) -> list[str]:
    out = []
    for m in re.finditer(NUM, s):
        n = re.sub(r"\s*[°º]", "", m.group(0))
        out.append(re.sub(r"\s+", " ", n).lower())
    return out


def _incs(s: str | None) -> list[str]:
    return re.findall(r"([a-zñ])\)", s) if s else []


def _other_ordering(w: str, r: dict) -> bool:
    """The words name a 'texto ordenado' of a year other than the one on disk (a different article numbering)."""
    years = re.findall(r"(?:texto ordenado|t\.\s?o\.?)\s*(?:en\s*|de\s*)?(\d{4})", w)
    return bool(years) and any(y != r.get("to") for y in years)


def classify(after: str, own: str) -> tuple[str, str | None]:
    """Which act the words right after a citation point at: ('same'|'cross'|'other'|'ambiguous', statute)."""
    w = norm(after)
    w = re.split(r";|:|(?<!\binc)(?<!\bap)(?<!\barts)(?<!\bart)\.\s", w, maxsplit=1)[0]
    w = re.sub(r"^(?:[\s,]+|(?:y|e|o|u)\s+|a\s+(?=\d)|(?:incs?|aps?|arts?|pto|ptos)\.\s*|(?:incisos?|apartados?|puntos?|"
               r"parrafos?|primero|segundo|tercero|cuarto|quinto|sexto|ultimo|penultimo|bis|ter|quater|siguientes|ss|concordantes)\b|\d+\s*[°º]?|"
               r"[a-zñ]\))+", " ", w)
    w = re.sub(r"^[\s,]*(?:(?:y|e)\s+(?:siguientes|ss\.?|concordantes|sus\s+modificaciones|sus\s+modificatorias|"
               r"modificatorias|complementarias)\b[\s,]*)+", " ", w)
    m = re.match(r"^[\s,]*del\s+titulo\s+[ivxl]+\b", w)
    if m:
        w = w[m.end():]
    if SAME.match(w):
        return "same", own
    m = ACT_NUM.match(w)
    if m:
        for k, r in REGISTRY.items():
            if m.group(1).replace(".", "") in {n.replace(".", "") for n in r["numbers"]}:
                if (r.get("need_version") and not re.search(r.get("version", "$^"), w)) or _other_ordering(w, r):
                    return "ambiguous", None
                return ("same" if k == own else "cross"), k
        return "other", None
    for k, r in REGISTRY.items():
        for name in r["names"]:
            if re.match(r"^[\s,]*(?:de|del)\s+(?:la\s+)?" + name, w):
                if (r.get("need_version") and not re.search(r["version"], w)) or _other_ordering(w, r):
                    return "ambiguous", None
                return ("same" if k == own else "cross"), k
    if VAGUE.match(w):
        return "ambiguous", None
    if OTHER.match(w):
        return "other", None
    if re.match(r"^[\s,]*(?:de|del)\s+(?:la\s+)?ley\s+de\b", w):
        return "other", None
    return "same", own


def find_citations(text: str, own: str, current: str | None = None) -> list[dict]:
    """Citations of articles (and lettered incisos) in one paragraph of provision text."""
    out = []
    elsewhere = set()                                 # numbers already cited here as another act's articles
    last_other = -10_000                              # where the last citation of another act ended
    for m in CITE.finditer(text):
        before = text[max(0, m.start() - 40):m.start()]
        if re.search(r"a\s+continuaci[oó]n\s+del?\s+$", before, re.I):
            continue                                  # names an unnumbered article, not the one cited
        kind, st = classify(text[m.end():m.end() + 120], own)
        if AMENDING.search(text[:m.start()]):
            kind, st = "ambiguous", None              # an amending clause: its act is whatever it amends
        if POSSESSIVE.search(before):
            kind, st = "ambiguous", None
        incs = _incs(m.group("incs")) + _incs(m.group("tincs"))
        nums = _nums(m.group("nums"))
        explicit = bool(SAME.match(norm(text[m.end():m.end() + 60])))
        if kind == "same" and not explicit:
            gap = text[last_other:m.start()] if last_other >= 0 else ""
            if set(nums) & elsewhere or (0 <= m.start() - last_other < 80 and not re.search(r"[.;]", gap)):
                kind, st = "ambiguous", None          # 'el artículo 98' right after 'el artículo 97 de la CN'
            elif INTRO_OTHER.search(text[:m.start()]):
                kind, st = "ambiguous", None          # 'las siguientes disposiciones del CÓDIGO ...: artículo 3, ...'
        if kind in ("other", "ambiguous"):
            elsewhere.update(nums)
            last_other = m.end()
        quote = text[max(0, m.start() - 60):m.end() + 60].strip()
        for n in nums:
            for i in (incs if len(nums) == 1 and incs else [None]):
                c = {"kind": kind, "article": n, "inciso": i, "span": m.group(0).strip(), "quote": quote}
                if st:
                    c["statute"] = st
                out.append(c)
    for m in TITLE_CITE.finditer(text):
        kind, st = classify(text[m.end():m.end() + 120], own)
        if kind == "same":
            out.append({"kind": "same", "statute": own, "article": None, "title": m.group(1), "inciso": None,
                        "span": m.group(0), "quote": text[max(0, m.start() - 60):m.end() + 60].strip()})
    if current:
        for m in OWN_INC.finditer(text):
            for i in _incs(m.group("incs")):
                out.append({"kind": "same", "statute": own, "article": current, "inciso": i, "span": m.group(0),
                            "quote": text[max(0, m.start() - 60):m.end() + 60].strip()})
    return out


def _line_since(line: str, nxt: str = "", units: tuple = ()) -> int | None:
    """Latest substitution/insertion date noted on this paragraph, or in a note paragraph right after it."""
    notes = parse_notes(line)
    if nxt.startswith("(") and not re.sub(r"[\s.)]+", "", strip_notes(nxt)):
        notes += parse_notes(nxt)
    ds = [n["bo"] for n in notes if n["action"] in ("sustituido", "incorporado") and (not units or n["unit"] in units)]
    return max(ds) if ds else None


def _ambiguous(st, a, c) -> dict:
    """An unresolved citation; 'if_same' names the repealed unit it would hit if read as this statute's own."""
    out = {"citing": st.label(a.key), "span": c["span"], "quote": c["quote"], "article": c["article"],
           "inciso": c.get("inciso")}
    key = f"{a.title}:{c['article']}" if st.titled else c["article"]
    t = st.by_key.get(key)
    rep = (article_repeal(t) or (inciso_repeals(t).get(c.get("inciso")) if c.get("inciso") else None)) if t else st.gap.get(key)
    if rep:
        out["if_same"] = {"target": st.label(key, c.get("inciso") if t and not article_repeal(t) else None),
                          "norm": rep["norm"], "bo": rep["bo"]}
    return out


def _flag(st, a, tst, tkey, inc, c, line, rep, citing_since, basis) -> dict:
    target = f"{tst.key} {tkey}" if tkey.startswith("tít.") else tst.label(tkey, inc)
    return {"statute": st.key, "citing": st.label(a.key), "citing_key": a.key, "target": target,
            "target_statute": tst.key, "target_key": tkey, "target_inciso": inc, "kind": c["kind"], "span": c["span"],
            "quote": c["quote"], "line": line[:600], "repeal": rep, "basis": basis, "citing_since": citing_since,
            "target_since": tst.base}


def find_flags(statutes: dict[str, Statute]) -> tuple[list[dict], list[dict]]:
    """Citations from provisions in force that land on a repealed article, inciso or title-gap article."""
    flags, ambiguous = [], []
    for sk in sorted(statutes):
        st = statutes[sk]
        for a in st.articles:
            if article_repeal(a):
                continue
            art_since = max([d for d in (_line_since(l, units=("artículo",)) for l in a.lines) if d] or [0])
            own_incs = inciso_repeals(a)
            for li, line in own_lines(a.lines):
                inc_m = INC_LINE.match(line)
                if inc_m and inc_m.group("l") in own_incs:
                    continue
                text = strip_notes(HEADER.sub("", line, count=1) if li == 0 else line)
                text = re.sub(r"[\"“«][^\"”»]{0,2000}[\"”»]", " ", text)
                cur = None if a.unnumbered else a.num
                line_since = _line_since(line, a.lines[li + 1] if li + 1 < len(a.lines) else "")
                for c in find_citations(text, sk, cur):
                    if c["kind"] in ("ambiguous", "other"):
                        if c["kind"] == "ambiguous":
                            ambiguous.append(_ambiguous(st, a, c))
                        continue
                    tst = statutes.get(c.get("statute"))
                    if tst is None:
                        continue
                    if c.get("title"):
                        rep = tst.title_rep.get(c["title"])
                        if rep and not (st.titled and a.title == c["title"]):
                            flags.append(_flag(st, a, tst, f"tít. {c['title']}", None, c, line, rep,
                                               line_since or art_since or st.base, "title"))
                        continue
                    if tst.titled:
                        cand = [k for k in tst.by_key if k.split(":", 1)[1] == c["article"]]
                        if tst is st and f"{a.title}:{c['article']}" in tst.by_key:
                            tkey = f"{a.title}:{c['article']}"
                        elif tst is st and f"{a.title}:{c['article']}" in tst.gap:
                            tkey = f"{a.title}:{c['article']}"
                        elif tst is not st and len(cand) == 1:
                            tkey = cand[0]
                        else:
                            if tst is not st:
                                ambiguous.append(dict(_ambiguous(st, a, c), why="article number not unique across titles"))
                            continue
                    else:
                        tkey = c["article"]
                    if tkey == a.key and tst is st and not c["inciso"]:
                        continue
                    target = tst.by_key.get(tkey)
                    rep, inc = None, None
                    if target is not None:
                        rep = article_repeal(target)
                        if rep is None and c["inciso"]:
                            rep = inciso_repeals(target).get(c["inciso"])
                            inc = c["inciso"] if rep else None
                    elif tkey in tst.gap:
                        rep = tst.gap[tkey]
                    if not rep:
                        continue
                    flags.append(_flag(st, a, tst, tkey, inc, c, line, rep, line_since or art_since or st.base,
                                       "title gap" if "gap_title" in rep else "note"))
    seen, amb = set(), []
    for x in ambiguous:
        k = (x["citing"], x["span"], x["quote"])
        if k not in seen:
            seen.add(k)
            amb.append(x)
    ambiguous = amb
    # one flag per (citing, target)
    seen, uniq = set(), []
    for f in flags:
        k = (f["citing"], f["target"])
        if k not in seen:
            seen.add(k)
            uniq.append(f)
    for i, f in enumerate(uniq, 1):
        f["id"] = f"T{i:03d}"
    return uniq, ambiguous


# ---------------------------------------------------------------- Lean

def histories(f: dict) -> tuple[list[tuple[int, bool]], list[tuple[int, bool]]]:
    r = f["repeal"]["from"]
    citing = [(f["citing_since"], True)]
    target = [(r, False)] + ([(f["target_since"], True)] if f["target_since"] < r else [])
    return citing, target


def at(h: list[tuple[int, bool]], d: int) -> bool:
    for t, v in h:
        if t <= d:
            return v
    return False


def verdict(f: dict, today: int) -> bool:
    c, t = histories(f)
    return (not t[0][1]) and t[0][0] <= today and at(c, today)


def reenacted(f: dict) -> bool:
    c, t = histories(f)
    return (not t[0][1]) and c[0][1] and t[0][0] < c[0][0]


def lean_hist(h) -> str:
    return "[" + ", ".join(f"({d}, {'true' if v else 'false'})" for d, v in h) + "]"


def emit_lean(flags: list[dict], today: int, module: str, source: str) -> str:
    return _emit(flags, [histories(f) for f in flags], today, module, source)


def _emit(flags: list[dict], hists: list, today: int, module: str, source: str, data: str = "data/refs.json") -> str:
    items = []
    verdicts, reens = [], []
    for f, (c, t) in zip(flags, hists):
        verdicts.append((not t[0][1]) and t[0][0] <= today and at(c, today))
        reens.append((not t[0][1]) and c[0][1] and t[0][0] < c[0][0])
        cm = f"{f['id']}: {f['citing']} -> {f['target']}".replace("-/", "- /")
        items.append(f"  -- {cm}\n  ⟨{lean_hist(c)}, {lean_hist(t)}⟩")
    body = ",\n".join(items)
    cert = ", ".join("true" if v else "false" for v in verdicts)
    reen = ", ".join("true" if v else "false" for v in reens)
    return (f"import ArLegal.Basic\n\n-- Generated by tools/gen_refs.py from {source}. Do not edit.\n"
            f"namespace ArLegal.Generated.{module}\n\n"
            f"/-- One certificate per flag, in the order of {data}. -/\n"
            f"def flags : List RefFlag := [\n{body}\n]\n\n"
            f"/-- Lean evaluates every certificate on {today}; the right-hand side is the generator's verdict. -/\n"
            f"theorem certified : flags.map (·.certified {today}) = [{cert}] := by decide\n\n"
            + (f"/-- Every flag in this file is a dead remission (`RefFlag.all_sound`). -/\n"
               f"theorem all_dead : ∀ f ∈ flags, ∃ r, r ≤ {today} ∧ f.citing.holds {today} = true ∧\n"
               f"    ∀ d, r ≤ d → f.remission.operative d = false :=\n"
               f"  RefFlag.all_sound flags {today} (by decide)\n\n" if verdicts and all(verdicts) else "")
            + f"/-- Which citing provisions were rewritten after their target was repealed. -/\n"
            f"theorem reenacted : flags.map (·.reenacted) = [{reen}] := by decide\n\n"
            f"end ArLegal.Generated.{module}\n")


# ---------------------------------------------------------------- corpus (git history, read only)

ART_FILE = re.compile(r"^(?P<act>[a-z0-9-]+)/art-(?P<n>\d+)(?:-(?P<suf>[a-z]+))?\.md$")
TRAILER = re.compile(r"^(In-force|Law|Kind):\s*(.*)$", re.M)


def unit_key(article: str) -> str:
    """'245 bis' -> 'art-245-bis' (the corpus's zero-padded file names)."""
    m = re.fullmatch(r"(\d+)(?: ([a-z]+))?", article)
    return f"art-{int(m.group(1)):03d}" + (f"-{m.group(2)}" if m.group(2) else "") if m else ""


def corpus_events(log: str) -> dict[str, list[tuple[int, str, str, str]]]:
    """Per file, its dated events (date, status A/M/D, law, kind), newest first, from
    'git log --no-renames --name-status' output whose commits start with an '@@<sha>' line followed by the body."""
    ev: dict[str, list] = {}
    for block in log.split("\n@@")[0:]:
        block = block.lstrip("@")
        head, _, rest = block.partition("\n")
        body, _, files = rest.partition("\n##\n")
        tr = {k: v.strip() for k, v in TRAILER.findall(body)}
        date = tr.get("In-force", "")
        if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", date):
            continue
        d = int(date.replace("-", ""))
        for line in files.splitlines():
            parts = line.split("\t")
            if len(parts) == 2 and parts[0] in ("A", "M", "D") and ART_FILE.match(parts[1]):
                ev.setdefault(parts[1], []).append((d, parts[0], tr.get("Law", ""), tr.get("Kind", "")))
    for p in ev:
        ev[p].sort(key=lambda e: -e[0])         # stable: commit order kept within a day
    return ev


def history_of(events: list[tuple[int, str, str, str]]) -> list[tuple[int, bool]]:
    return [(d, s != "D") for d, s, _, _ in events]


def corpus_flags(root: Path, texts: dict[str, str], events: dict[str, list]) -> tuple[list[dict], list[dict]]:
    """Intra-act citations from articles present at HEAD to article files the history deleted and never restored."""
    flags, ambiguous = [], []
    for path in sorted(texts):
        act = path.split("/", 1)[0]
        lines = texts[path].splitlines()
        lines = lines[1:] if lines and lines[0].startswith("#") else lines
        for _, line in own_lines(lines):
            if EMBEDDED_HEAD.match(line):
                break                                 # text of another provision copied into this one
            text = re.sub(r"[\"“«][^\"”»]{0,2000}[\"”»]", " ", line)
            for c in find_citations(text, act):
                if c["kind"] != "same" or c.get("title") or not c["article"]:
                    continue
                tpath = f"{act}/{unit_key(c['article'])}.md"
                if tpath == path or tpath in texts or tpath not in events:
                    continue
                tev = events[tpath]
                if tev[0][1] != "D":
                    continue
                rec = {"act": act, "citing": path, "target": tpath, "span": c["span"], "quote": c["quote"],
                       "repeal": {"from": tev[0][0], "law": tev[0][2], "kind": tev[0][3]},
                       "citing_hist": history_of(events.get(path, [])), "target_hist": history_of(tev)}
                if tev[0][3] not in ("law", "decree") or not rec["citing_hist"]:
                    ambiguous.append(dict(rec, why="deletion not credited to a norm" if rec["citing_hist"]
                                          else "citing file has no dated history"))
                else:
                    flags.append(rec)
    seen, uniq = set(), []
    for f in flags:
        why = CORPUS_REJECTED.get((f["citing"], f["target"]))
        if why:
            if (f["citing"], f["target"]) not in seen:
                ambiguous.append(dict(f, why="rejected by hand: " + why))
                seen.add((f["citing"], f["target"]))
            continue
        if (f["citing"], f["target"]) not in seen:
            seen.add((f["citing"], f["target"]))
            uniq.append(f)
    for i, f in enumerate(uniq, 1):
        f["id"] = f"C{i:04d}"
        f["citing_label"], f["target_label"] = f["citing"], f["target"]
    return uniq, ambiguous


# Flags read by hand and not certified, with the reason. Keyed by (citing file, target file).
CORPUS_REJECTED = {
    ("ley-19550/art-386.md", "ley-19550/art-371.md"):
        "referent mismatch: art. 386 o) speaks of 'leyes previstas en el artículo 371, reglamentarias de los "
        "registros', but the deleted art. 371 was 'Dirección y administración' of a joint venture; the citation "
        "follows an older numbering or another act, so the dead target is not the one cited",
    ("ley-24013/art-119.md", "ley-24013/art-012.md"):
        "repeal credited to DNU 70/2023, whose labour title was suspended by the courts; the record names no later "
        "statutory repeal, so the date the article ceased cannot be established from it",
    ("ley-26844/art-073.md", "ley-26844/art-050.md"):
        "repeal credited to DNU 70/2023, whose labour title was suspended by the courts; the record names no later "
        "statutory repeal, so the date the article ceased cannot be established from it",
}


def load_corpus(root: Path) -> tuple[dict[str, str], dict[str, list]]:
    """Article texts at HEAD and the dated history of every article file, read with git (no code from the clone runs)."""
    def git(*args: str) -> str:
        return subprocess.run(["git", "-C", str(root), *args], capture_output=True, check=True,
                              encoding="utf-8").stdout
    names = [n for n in git("ls-tree", "-r", "HEAD", "--name-only").splitlines() if ART_FILE.match(n)]
    texts = {}
    for n in names:
        texts[n] = (root / n).read_text(encoding="utf-8")       # working tree checked clean against HEAD
    if git("status", "--porcelain", "--untracked-files=no").strip():
        raise SystemExit("corpus clone has local changes; refusing to read it")
    log = git("log", "HEAD", "--no-renames", "--name-status", "--format=@@%H%n%B%n##")
    return texts, corpus_events(log)


def emit_corpus_lean(flags: list[dict], today: int, chunk: int) -> dict[str, str]:
    files = {}
    for k in range(0, max(len(flags), 1), chunk):
        part = flags[k:k + chunk]
        mod = f"Corpus{k // chunk:03d}"
        items = [{"id": f["id"], "citing": f["citing"], "target": f["target"]} for f in part]
        hist = [(f["citing_hist"], f["target_hist"]) for f in part]
        files[mod] = _emit(items, hist, today, mod, "the argentina-law corpus clone (git history)",
                           "data/corpus_refs.json")
    return files


# ---------------------------------------------------------------- sources

# start: first line of the statute body; stop: first line after it. base: date the consolidated text is taken to
# exist from, with the evidence for it, all read from the page itself.
SOURCES = {
    "lig": dict(file="lig_texact.htm", name="Ley de Impuesto a las Ganancias, t.o. Decreto 824/2019",
                start=r"^ANEXO I$", stop=r"^(Hoja Adicional de Firmas|ANEXO II$|Antecedentes Normativos$)",
                base=20191207, basis="Decreto 824/2019 art. 2: in force the day after publication (e. 06/12/2019)"),
    "ley11683": dict(file="ley11683_texact.htm", name="Ley 11.683 de Procedimiento Tributario, t.o. 1998",
                     start=r"^TITULO I$", stop=r"^(ANEXO II\b|INDICE\b|Antecedentes Normativos$)",
                     base=19980713, basis="Decreto 821/98 dated 13/7/98 (B.O. date not on the page)"),
    "iva": dict(file="iva_texact.htm", name="Ley de Impuesto al Valor Agregado, t.o. 1997",
                start=r"^ANEXO I$", stop=r"^(ANEXO II\b|Antecedentes Normativos$)",
                base=19970326, basis="Decreto 280/97 dated 26/3/97 (B.O. date not on the page)"),
    "ley23966": dict(file="ley23966_texact.htm", name="Ley 23.966 (Título VI: Impuesto sobre los Bienes Personales)",
                     start=r"^TITULO I$", stop=r"^Antecedentes Normativos$", titled=True,
                     base=19910815, basis="promulgated 15/8/1991 (B.O. date not on the page)"),
    "ley24977": dict(file="ley24977_texact.htm", name="Ley 24.977, Anexo (Régimen Simplificado, Monotributo)",
                     start=r"^ANEXO$", stop=r"^Antecedentes Normativos$",
                     base=20091221, basis="Anexo substituted by Ley 26.565 art. 1, B.O. 21/12/2009"),
    "ley25413": dict(file="ley25413_texact.htm", name="Ley 25.413 (impuesto sobre créditos y débitos)",
                     start=r"sancionan con fuerza de Ley", stop=r"^Antecedentes Normativos$", skip_start=True,
                     base=20010324, basis="promulgated 24/3/2001 (B.O. date not on the page)"),
}


def body(lines: list[str], start: str, stop: str, skip_start: bool = False) -> list[str]:
    i = next(i for i, l in enumerate(lines) if re.search(start, l))
    if skip_start:
        i += 1
    j = next((k for k in range(i + 1, len(lines)) if re.search(stop, lines[k])), len(lines))
    return lines[i:j]


def load_statutes(src: Path = SRC) -> dict[str, Statute]:
    out = {}
    for k, s in SOURCES.items():
        raw = (src / s["file"]).read_bytes().decode("cp1252", errors="replace")
        lines = body(html_to_lines(raw), s["start"], s["stop"], s.get("skip_start", False))
        out[k] = Statute(k, s["name"], lines, s["base"], s.get("titled", False), s["basis"])
    return out


def inventory(statutes: dict[str, Statute]) -> dict:
    inv = {}
    for k, st in statutes.items():
        arts = {a.key: article_repeal(a) for a in st.articles}
        inv[k] = {
            "articles": len(st.articles),
            "repealed_articles": {a: {"norm": r["norm"], "bo": r["bo"], "from": r["from"]} for a, r in arts.items() if r},
            "repealed_incisos": {f"{a.key} {i})": {"norm": r["norm"], "bo": r["bo"], "from": r["from"]}
                                 for a in st.articles for i, r in inciso_repeals(a).items()},
            "repealed_titles": {t: {"norm": r["norm"], "bo": r["bo"], "from": r["from"]} for t, r in st.title_rep.items()},
            "title_gap_articles": sorted(st.gap),
        }
    return inv


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--today", type=int, default=20261124)
    ap.add_argument("--corpus", type=Path, help="local clone of the argentina-law corpus (optional, read only)")
    ap.add_argument("--chunk", type=int, default=100)
    a = ap.parse_args()
    statutes = load_statutes()
    flags, ambiguous = find_flags(statutes)
    for f in flags:
        f["certified"] = verdict(f, a.today)
        f["reenacted"] = reenacted(f)
    data = {"today": a.today, "sources": {k: {"file": s["file"], "name": s["name"], "base": s["base"],
                                               "base_basis": s["basis"]} for k, s in SOURCES.items()},
            "inventory": inventory(statutes), "flags": flags, "ambiguous": ambiguous}
    (ROOT / "data").mkdir(exist_ok=True)
    (ROOT / "data" / "refs.json").write_text(json.dumps(data, ensure_ascii=False, indent=1, sort_keys=True) + "\n",
                                             encoding="utf-8")
    gen = ROOT / "ArLegal" / "Generated"
    gen.mkdir(parents=True, exist_ok=True)
    (gen / "Tax.lean").write_text(emit_lean(flags, a.today, "Tax", "sources/infoleg (six tax statutes)"),
                                  encoding="utf-8", newline="\n")
    print(f"flags {len(flags)}, certified {sum(f['certified'] for f in flags)}, ambiguous {len(ambiguous)}")
    if a.corpus:
        texts, events = load_corpus(a.corpus)
        cflags, camb = corpus_flags(a.corpus, texts, events)
        for f in cflags:
            f["certified"] = at(f["citing_hist"], a.today) and not f["target_hist"][0][1] and f["target_hist"][0][0] <= a.today
            f["reenacted"] = f["citing_hist"][0][1] and f["target_hist"][0][0] < f["citing_hist"][0][0]
        head = subprocess.run(["git", "-C", str(a.corpus), "rev-parse", "HEAD"], capture_output=True,
                              encoding="utf-8").stdout.strip()
        (ROOT / "data" / "corpus_refs.json").write_text(
            json.dumps({"today": a.today, "corpus_head": head, "articles": len(texts), "flags": cflags,
                        "ambiguous": camb}, ensure_ascii=False, indent=1, sort_keys=True) + "\n", encoding="utf-8")
        for old in gen.glob("Corpus*.lean"):
            old.unlink()
        for mod, src in emit_corpus_lean(cflags, a.today, a.chunk).items():
            (gen / f"{mod}.lean").write_text(src, encoding="utf-8", newline="\n")
        print(f"corpus: articles {len(texts)}, flags {len(cflags)}, certified {sum(f['certified'] for f in cflags)}, "
              f"ambiguous {len(camb)}")


if __name__ == "__main__":
    main()
