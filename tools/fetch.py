"""Download the official sources the build reads into sources/, and write SOURCES.md with their SHA-256.

A file already on disk is not downloaded again, so the hashes in SOURCES.md are those of the copies the build was
made from. InfoLEG's robots.txt asks for ten seconds between requests; this script waits that long after each
InfoLEG download and one second after the others.
"""
import hashlib, pathlib, sys, time, urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
AGENT = 'Mozilla/5.0 (compatible; ar-law-proofs)'
# (path under sources/, address, what it is)
SOURCES = [
    ("infoleg/lig_texact.htm", "https://servicios.infoleg.gob.ar/infolegInternet/anexos/330000-334999/332890/texact.htm",
     "Ley de Impuesto a las Ganancias, t.o. Decreto 824/2019, texto actualizado"),
    ("infoleg/ley27630.jpg", "https://servicios.infoleg.gob.ar/infolegInternet/anexos/330000-334999/332890/ley27630.jpg",
     "The scale of art. 73 (Ley 27.630), printed by InfoLEG as an image"),
    ("infoleg/ley11683_texact.htm", "https://servicios.infoleg.gob.ar/infolegInternet/anexos/15000-19999/18771/texact.htm",
     "Ley 11.683 de Procedimiento Tributario, t.o. 1998, texto actualizado"),
    ("infoleg/iva_texact.htm", "https://servicios.infoleg.gob.ar/infolegInternet/anexos/40000-44999/42701/texact.htm",
     "Ley de Impuesto al Valor Agregado, t.o. 1997, texto actualizado"),
    ("infoleg/ley23966_texact.htm", "https://servicios.infoleg.gob.ar/infolegInternet/anexos/0-4999/365/texact.htm",
     "Ley 23.966 (Título VI: bienes personales), texto actualizado"),
    ("infoleg/ley24977_texact.htm", "https://servicios.infoleg.gob.ar/infolegInternet/anexos/50000-54999/51609/texact.htm",
     "Ley 24.977 (Monotributo), texto actualizado"),
    ("infoleg/ley25413_texact.htm", "https://servicios.infoleg.gob.ar/infolegInternet/anexos/65000-69999/66533/texact.htm",
     "Ley 25.413 (créditos y débitos bancarios), texto actualizado"),
    ("indec/ipc_nacional_nivel_general.json", "https://apis.datos.gob.ar/series/api/series/?ids=148.3_INIVELNAL_DICI_M_26&limit=1000&format=json&start_date=2016-12-01",
     "INDEC, IPC nacional, nivel general, base diciembre 2016 (datos.gob.ar series API)"),
    ("arca/monotributo-categorias-agosto-2026.html", "https://www.arca.gob.ar/monotributo/categorias.asp",
     "ARCA, Monotributo: montos y categorías vigentes (from 1/08/2026)"),
    ("arca/bienes-personales-alicuotas.html", "https://www.arca.gob.ar/gananciasYBienes/bienes-personales/conceptos-basicos/alicuotas.asp",
     "ARCA, Bienes personales: alícuotas 2023 to 2025"),
    ("arca/bienes-personales-exentos.html", "https://www.arca.gob.ar/gananciasYBienes/bienes-personales/conceptos-basicos/bienes-exentos.asp",
     "ARCA, Bienes personales: bienes exentos"),
    ("arca/Tabla-Art-94-LIG-enero-junio-2025.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-humanas-sucesiones-indivisas/declaracion-jurada/documentos/Tabla-Art-94-LIG-enero-junio-2025.pdf",
     "ARCA, published table"),
    ("arca/Tabla-Art-94-LIG-periodo-julio-diciembre-2025.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-humanas-sucesiones-indivisas/declaracion-jurada/documentos/Tabla-Art-94-LIG-periodo-julio-diciembre-2025.pdf",
     "ARCA, published table"),
    ("arca/Tabla-Art-94-LIG-liquidacion-anual-y-final-2025.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-humanas-sucesiones-indivisas/declaracion-jurada/documentos/Tabla-Art-94-LIG-liquidacion-anual-y-final-2025.pdf",
     "ARCA, published table"),
    ("arca/Tabla-Art-94-LIG-per-ene-a-jun-2026.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-humanas-sucesiones-indivisas/declaracion-jurada/documentos/Tabla-Art-94-LIG-per-ene-a-jun-2026.pdf",
     "ARCA, published table"),
    ("arca/Tabla-Art-94-LIG-per-jul-a-dic-2026.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-humanas-sucesiones-indivisas/declaracion-jurada/documentos/Tabla-Art-94-LIG-per-jul-a-dic-2026.pdf",
     "ARCA, published table"),
    ("arca/Tabla-Art-94-LIG-liquidacion-anual-y-final-2026.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-humanas-sucesiones-indivisas/declaracion-jurada/documentos/Tabla-Art-94-LIG-liquidacion-anual-y-final-2026.pdf",
     "ARCA, published table"),
    ("arca/Deducciones-personales-art-30-enero-junio-2025.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-humanas-sucesiones-indivisas/deducciones/documentos/Deducciones-personales-art-30-enero-junio-2025.pdf",
     "ARCA, published table"),
    ("arca/Deducciones-personales-art-30-julio-diciembre-2025.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-humanas-sucesiones-indivisas/deducciones/documentos/Deducciones-personales-art-30-julio-diciembre-2025.pdf",
     "ARCA, published table"),
    ("arca/Deducciones-personales-art-30-liq-anual-2025.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-humanas-sucesiones-indivisas/deducciones/documentos/Deducciones-personales-art-30-liq-anual-2025.pdf",
     "ARCA, published table"),
    ("arca/Deducciones-personales-art-30-ene-a-jun-2026.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-humanas-sucesiones-indivisas/deducciones/documentos/Deducciones-personales-art-30-ene-a-jun-2026.pdf",
     "ARCA, published table"),
    ("arca/Deducciones-personales-art-30-jul-dic-2026.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-humanas-sucesiones-indivisas/deducciones/documentos/Deducciones-personales-art-30-jul-dic-2026.pdf",
     "ARCA, published table"),
    ("arca/Deducciones-personales-art-30-liq-anual-2026.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-humanas-sucesiones-indivisas/deducciones/documentos/Deducciones-personales-art-30-liq-anual-2026.pdf",
     "ARCA, published table"),
    ("arca/Deducciones-art-30-2025-Jubilados-HMG-2025.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-humanas-sucesiones-indivisas/deducciones/documentos/Deducciones-art-30-2025-Jubilados-HMG-2025.pdf",
     "ARCA, published table"),
    ("arca/Deducciones-art-30-2025-Jubilados-HMG-2026.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-humanas-sucesiones-indivisas/deducciones/documentos/Deducciones-art-30-2025-Jubilados-HMG-2026.pdf",
     "ARCA, published table"),
    ("arca/monotributo-categorias-febrero-julio-2025.pdf", "https://www.arca.gob.ar/monotributo/documentos/categorias/monotributo-categorias-febrero-julio-2025.pdf",
     "ARCA, published table"),
    ("arca/monotributo-categorias-agosto-2025-enero-2026.pdf", "https://www.arca.gob.ar/monotributo/documentos/categorias/monotributo-categorias-agosto-2025-enero-2026.pdf",
     "ARCA, published table"),
    ("arca/monotributo-categorias-febrero-julio-2026.pdf", "https://www.arca.gob.ar/monotributo/documentos/categorias/monotributo-categorias-febrero-julio-2026.pdf",
     "ARCA, published table"),
    ("arca/Ganancias-Escala-PJ-2022.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-juridicas/determinacion/documentos/Ganancias-Escala-PJ-2022.pdf",
     "ARCA, escala del art. 73, 2022"),
    ("arca/Ganancias-Escala-PJ-2023.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-juridicas/determinacion/documentos/Ganancias-Escala-PJ-2023.pdf",
     "ARCA, escala del art. 73, 2023"),
    ("arca/Ganancias-Escala-PJ-2024.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-juridicas/determinacion/documentos/Ganancias-Escala-PJ-2024.pdf",
     "ARCA, escala del art. 73, 2024"),
    ("arca/Ganancias-Escala-PJ-2025.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-juridicas/determinacion/documentos/Ganancias-Escala-PJ-2025.pdf",
     "ARCA, escala del art. 73, 2025"),
    ("arca/Ganancias-Escala-PJ-2026.pdf", "https://www.arca.gob.ar/gananciasYBienes/ganancias/personas-juridicas/determinacion/documentos/Ganancias-Escala-PJ-2026.pdf",
     "ARCA, escala del art. 73, 2026"),
]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources_md(rows):
    """The table of SOURCES.md from (path, address, description, hash) rows."""
    lines = ['# Sources', '',
             'Official texts and tables the build reads. They are not redistributed here: run python tools/fetch.py to',
             'download them into sources/ (git-ignored). The hashes are those of the copies this build was made from;',
             'a publisher may have replaced a file since.', '',
             '| File | SHA-256 | Address | What it is |', '|---|---|---|---|']
    lines += [f'| sources/{p} | {h} | <{u}> | {d} |' for p, u, d, h in rows]
    return '\n'.join(lines) + '\n'


def main():
    rows = []
    for path, url, what in SOURCES:
        target = ROOT / 'sources' / path
        if not target.exists():
            target.parent.mkdir(parents=True, exist_ok=True)
            request = urllib.request.Request(url, headers={'User-Agent': AGENT})
            with urllib.request.urlopen(request, timeout=60) as response:
                target.write_bytes(response.read())
            print('downloaded', path, file=sys.stderr)
            time.sleep(10 if 'infoleg' in url else 1)
        rows.append((path, url, what, sha256(target)))
    (ROOT / 'SOURCES.md').write_text(sources_md(rows), encoding='utf-8', newline='\n')
    print(f'{len(rows)} sources, SOURCES.md written')


if __name__ == '__main__':
    main()
