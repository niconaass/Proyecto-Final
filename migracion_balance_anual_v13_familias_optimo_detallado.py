from __future__ import annotations
"""
Trabajo Integrador - Planta híbrida FV + Eólico + BESS
Migración del balance anual desde Excel a Python.

Esta versión reproduce la lógica actual acordada antes de optimizar:
- año bisiesto: 8784 h;
- SOC horario secuencial;
- SOC inicial = 100 % de la capacidad disponible del año;
- FV degradado año a año;
- BESS degradado linealmente por ciclos equivalentes;
- peak shaving obligatorio por potencia contratada/T1;
- carga con excedente renovable y posibilidad de carga desde red;
- despacho económico LP y planificación multianual opcionales;
- exportación de excedentes hasta el límite de T1, sin remuneración;
- CAPEX/OPEX/potencia contratada/energía de red a 20 años;
- evaluación automática de configuraciones;
- búsqueda por grilla sobre cuatro variables de diseño, con P contratada fija en 15 MW;
- restricción espacial del parque eólico para el polígono disponible;
- reporte explícito del BESS en MW / MWh / horas;
- CAPEX BESS separado en componente de energía y componente de potencia;
- filtro espacial de screening para FV + containers BESS dentro del terreno;
- pitch FV calculado por criterio geométrico de no sombreado (6,5 m), con GCR derivado automáticamente.

BASE V11:
- despacho económico anual con límite de ciclos;
- planificación multianual de degradación: calcula el SOH técnico mínimo de cada año,
  reserva los ciclos mínimos futuros y evita que el arbitraje temprano deje al BESS sin
  capacidad para cumplir la demanda en años posteriores.

BASE V12:
- P_FV y P_BESS son variables continuas; N_aeros y N_containers son enteras.
- Differential Evolution mixto: no usa valores discretos prefijados de potencia.
- SOC anual cíclico: SOC final = SOC inicial, evitando energía gratis cada 1 de enero.
- degradación BESS conservadora también dentro del último año del horizonte.
- modo de optimización liviano: no exporta ni conserva detalle horario de candidatos.
- screening espacial conjunto: eólico reserva área y FV+BESS deben caber en el residual.

NOVEDAD V13:
- enumera todas las familias discretas (N_aeros, N_containers) del dominio pedido;
- para CADA familia explora P_FV y P_BESS sobre el dominio continuo completo, sin rangos heredados de V12;
- cada familia factible recibe al menos una validación EXACTA de 20 años;
- las mejores familias se refinan con evaluaciones exactas adicionales, sin cambiar el dominio global;
- al encontrar el óptimo genera un análisis anual completo de degradación, compras de red, BESS y costos.

NO implementa todavía:
- reemplazo automático del BESS al llegar a EOL;
- layout geométrico conjunto exacto FV + aerogeneradores + BESS dentro del KMZ.

IMPORTANTE SOBRE ESPACIO:
Para el predimensionamiento FV se adopta pitch entre filas = 6,5 m para tracker 1P N-S,
correspondiente al criterio acordado de evitar sombreado entre filas entre 9:00 y 15:00
hora solar en el solsticio de invierno. Con ancho rotante 2,384 m, el GCR se deriva como
GCR = 2,384 / pitch ≈ 0,367. El pitch puede modificarse con --pitch-fv-m.
El filtro FV+BESS es un screening; la comprobación final debe hacerse con layout georreferenciado.

Instalación:
    pip install pandas numpy openpyxl

Uso básico:
    python migracion_balance_anual_v13_familias_optimo_detallado.py --excel Balance_anual-v3.xlsm

Simulación de 20 años:
    python migracion_balance_anual_v13_familias_optimo_detallado.py --excel Balance_anual-v3.xlsm --simular-20

Si se omite --excel, busca automáticamente un archivo Balance_anual-v3*.xlsm/.xlsx
en la carpeta del script, la carpeta actual o ~/Documents/Facultad/Taller integrador.
"""


import argparse
import math
import re
import unicodedata
import warnings
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal
from itertools import product
import time
import sys
import json
import subprocess
import tempfile

import numpy as np
import pandas as pd
from scipy.optimize import linprog, differential_evolution, minimize
from scipy.sparse import coo_matrix


# =============================================================================
# CONSTANTES
# =============================================================================

HORAS_ANIO = 8784
DT_H = 1.0

# Red / pliego
LIMITE_T1_MW = 15.0
P_CONTRATADA_MIN_MW = 6.0
P_CONTRATADA_MAX_MW = 15.0
P_CONTRATADA_FIJA_MW = 15.0  # recomendación docente: potencia contratada fija
COSTO_PC_USD_MW_MES = 4_500.0
ESCALAMIENTO_COSTOS = 0.025
WACC = 0.08

# BESS
ETA_CARGA_DEFAULT = 0.95
ETA_DESCARGA_DEFAULT = 0.95
SOC_MIN_DEFAULT = 0.10
SOC_MAX_DEFAULT = 1.00
SOC_INICIAL_DEFAULT = 1.00
SOH_EOL = 0.70
DOD_CICLO_REFERENCIA = 0.90
DEGRADACION_POR_CICLO_EQ = 0.000025  # 0,0025 puntos porcentuales/ciclo
P_RATE_MAX = 0.50                    # 0,5 C: P_BESS <= 0,5 * E_BESS
E_CONTAINER_MWH_DEFAULT = 5.015

# Aerogeneradores
P_NOMINAL_AERO_MW = {
    "GE3.4": 3.43,
    "GE3.8": 3.83,
}

# Restricción espacial derivada del KMZ del proyecto.
# Ambos aerogeneradores tienen rotor D = 130 m. Se adopta, de manera
# provisional, un espaciamiento mínimo centro-centro de 5D = 650 m.
# Para el polígono disponible (~0,804 km²; envolvente ~1,68 x 0,75 km),
# el máximo hallado que cumple 5D es 5 aerogeneradores.
# Esta restricción NO agrega pérdidas de estela: esas pérdidas ya están
# incorporadas en el perfil energético utilizado.
ROTOR_DIAMETRO_M = 130.0
DISTANCIA_MIN_AEROS_D = 5.0
DISTANCIA_MIN_AEROS_M = ROTOR_DIAMETRO_M * DISTANCIA_MIN_AEROS_D
AREA_DISPONIBLE_KM2 = 0.8041640744
AREA_DISPONIBLE_M2 = AREA_DISPONIBLE_KM2 * 1_000_000.0
N_AEROS_MAX_ESPACIO = 5

# Screening de ocupación eólica para responder cuánto terreno queda disponible
# para FV+BESS. Se reserva, de forma conservadora y explícita, el disco de radio
# D/2 alrededor de cada torre (área equivalente al rotor). La separación 5D entre
# centros se verifica aparte. Esto NO reemplaza el layout georreferenciado final.
AREA_RESERVADA_EOLICA_POR_AERO_M2 = math.pi * (ROTOR_DIAMETRO_M / 2.0) ** 2

# FV / ocupación de terreno.
# Trina Vertex NEG21C.20 y Jinko 66HL5-BDV: 2384 x 1303 mm.
# Para el screening se usa 700 W por defecto (conservador en superficie).
# Tracker supuesto: 1P, eje N-S. El ancho que rota perpendicular al eje es 2,384 m.
# Criterio de predimensionamiento acordado: pitch = 6,5 m, obtenido para evitar
# sombreado entre filas entre 9:00 y 15:00 hora solar en el solsticio de invierno.
# Por lo tanto, GCR = ancho_rotante / pitch.
MODULO_FV_LARGO_M = 2.384
MODULO_FV_ANCHO_M = 1.303
ANCHO_ROTANTE_TRACKER_1P_M = MODULO_FV_LARGO_M
PITCH_FV_DEFAULT_M = 6.5
POTENCIA_MODULO_FV_W_DEFAULT = 700.0

# BESS Gotion GRID5015: 6058 x 2438 mm.
# Screening conservador: 4 m entre containers en ambas direcciones.
BESS_CONTAINER_LARGO_M = 6.058
BESS_CONTAINER_ANCHO_M = 2.438
BESS_SEPARACION_SCREENING_M = 4.0

# CAPEX
CAPEX_FV_USD_MW = 614_000.0
CAPEX_EOL_USD_MW = 950_000.0
CAPEX_BESS_ENERGIA_USD_MWH = 190_000.0
CAPEX_BESS_POTENCIA_USD_MW = 239_000.0
CAPEX_FIJO_USD = 400_000.0

# OPEX: criterio adoptado en el Excel
OPEX_FV_PCT = 0.012
OPEX_EOL_PCT = 0.022
OPEX_BESS_PCT = 0.017


# =============================================================================
# ESTRUCTURAS
# =============================================================================

@dataclass(frozen=True)
class Configuracion:
    n_aeros: int
    p_fv_mw: float
    p_contratada_mw: float
    limite_t1_mw: float
    p_bess_mw: float
    e_bess_mwh: float
    eta_carga: float
    eta_descarga: float
    soc_min: float
    soc_max: float
    soc_inicial_frac: float
    n_containers: int
    e_container_mwh: float


@dataclass(frozen=True)
class Capex:
    fv_usd: float
    eolico_usd: float
    bess_usd: float
    fijo_usd: float
    total_usd: float


# =============================================================================
# UTILIDADES
# =============================================================================

def factor_degradacion_fv(anio: int) -> float:
    """Año 1 = 0,990; luego disminuye 0,004 por año hasta año 20 = 0,914."""
    if not 1 <= anio <= 20:
        raise ValueError("El año debe estar entre 1 y 20.")
    return 0.99 - 0.004 * (anio - 1)


def calcular_metricas_bess_diseno(
    p_bess_mw: float,
    n_containers: int,
    e_container_mwh: float = E_CONTAINER_MWH_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
) -> dict:
    """Potencia, energía, horas y CAPEX BESS con P y E tratadas por separado."""
    if n_containers < 0 or int(n_containers) != n_containers:
        raise ValueError("n_containers debe ser un entero >= 0.")
    if p_bess_mw < 0:
        raise ValueError("P_BESS debe ser >= 0.")
    e_bess_mwh = float(n_containers) * float(e_container_mwh)
    if n_containers == 0:
        if p_bess_mw > 1e-12:
            raise ValueError("No puede haber P_BESS > 0 sin containers/energía.")
        horas_nominales = 0.0
        horas_utiles_bol = 0.0
    else:
        if p_bess_mw <= 1e-12:
            raise ValueError("No tiene sentido instalar containers BESS con P_BESS = 0.")
        if p_bess_mw > P_RATE_MAX * e_bess_mwh + 1e-9:
            raise ValueError("P_BESS supera el máximo 0,5P del BESS.")
        horas_nominales = e_bess_mwh / p_bess_mw
        horas_utiles_bol = e_bess_mwh * (soc_max - soc_min) / p_bess_mw
    capex_energia = e_bess_mwh * CAPEX_BESS_ENERGIA_USD_MWH
    capex_potencia = p_bess_mw * CAPEX_BESS_POTENCIA_USD_MW
    return {
        "n_containers": int(n_containers),
        "e_bess_mwh": float(e_bess_mwh),
        "p_bess_mw": float(p_bess_mw),
        "horas_nominales": float(horas_nominales),
        "horas_utiles_bol": float(horas_utiles_bol),
        "capex_bess_energia_usd": float(capex_energia),
        "capex_bess_potencia_usd": float(capex_potencia),
        "capex_bess_total_usd": float(capex_energia + capex_potencia),
    }


def calcular_area_bess_screening(n_containers: int) -> dict:
    """Grilla compacta de containers, usando 4 m de separación en ambos ejes."""
    if n_containers < 0 or int(n_containers) != n_containers:
        raise ValueError("n_containers debe ser un entero >= 0.")
    n_containers = int(n_containers)
    if n_containers == 0:
        return {"area_bess_m2": 0.0, "area_bess_huella_pura_m2": 0.0,
                "bess_filas": 0, "bess_columnas": 0}
    huella_pura = n_containers * BESS_CONTAINER_LARGO_M * BESS_CONTAINER_ANCHO_M
    mejor = None
    for filas in range(1, n_containers + 1):
        columnas = math.ceil(n_containers / filas)
        largo = columnas * BESS_CONTAINER_LARGO_M + (columnas - 1) * BESS_SEPARACION_SCREENING_M
        ancho = filas * BESS_CONTAINER_ANCHO_M + (filas - 1) * BESS_SEPARACION_SCREENING_M
        candidato = (largo * ancho, filas, columnas)
        if mejor is None or candidato[0] < mejor[0]:
            mejor = candidato
    area, filas, columnas = mejor
    return {"area_bess_m2": float(area), "area_bess_huella_pura_m2": float(huella_pura),
            "bess_filas": int(filas), "bess_columnas": int(columnas)}


def calcular_area_fv_screening(
    p_fv_mw: float,
    *,
    potencia_modulo_w: float,
    pitch_fv_m: float = PITCH_FV_DEFAULT_M,
) -> dict:
    """
    Screening de superficie FV para tracker 1P N-S.

    GCR = ancho_rotante / pitch
    A_FV = A_módulos / GCR

    El pitch por defecto (6,5 m) es el criterio geométrico acordado de
    predimensionamiento para evitar sombreado entre filas entre 9:00 y 15:00
    hora solar en el solsticio de invierno.
    """
    if p_fv_mw < 0 or potencia_modulo_w <= 0:
        raise ValueError("P_FV debe ser >=0 y potencia del módulo >0.")
    if pitch_fv_m <= ANCHO_ROTANTE_TRACKER_1P_M:
        raise ValueError(
            f"pitch_fv_m debe ser mayor que el ancho rotante ({ANCHO_ROTANTE_TRACKER_1P_M:.3f} m)."
        )
    gcr_fv = ANCHO_ROTANTE_TRACKER_1P_M / pitch_fv_m
    n_modulos = 0 if p_fv_mw <= 1e-12 else math.ceil(p_fv_mw * 1_000_000.0 / potencia_modulo_w)
    area_modulo = MODULO_FV_LARGO_M * MODULO_FV_ANCHO_M
    area_modulos = n_modulos * area_modulo
    area_terreno = area_modulos / gcr_fv if n_modulos else 0.0
    return {
        "n_modulos_fv": int(n_modulos),
        "potencia_fv_real_por_modulos_mwp": float(n_modulos * potencia_modulo_w / 1_000_000.0),
        "pitch_fv_m": float(pitch_fv_m),
        "gcr_fv": float(gcr_fv),
        "area_modulos_fv_m2": float(area_modulos),
        "area_fv_terreno_m2": float(area_terreno),
    }


def calcular_screening_espacial(*, p_fv_mw: float, n_aeros: int, n_containers: int,
                                 potencia_modulo_w: float, pitch_fv_m: float = PITCH_FV_DEFAULT_M) -> dict:
    """
    Screening espacial V12.

    1) exige n_aeros <= 5 y mantiene la separación mínima 5D como restricción de layout;
    2) reserva dentro del predio un área equivalente al disco de radio D/2 por aerogenerador;
    3) FV+BESS deben caber en el área residual.

    La reserva eólica es deliberadamente un screening: no representa caminos, fundaciones
    ni micrositing final, pero evita reportar erróneamente que FV+BESS disponen del 100 %
    del terreno cuando hay aerogeneradores instalados.
    """
    fv = calcular_area_fv_screening(
        p_fv_mw, potencia_modulo_w=potencia_modulo_w, pitch_fv_m=pitch_fv_m
    )
    bess = calcular_area_bess_screening(n_containers)
    area_fv_bess = fv["area_fv_terreno_m2"] + bess["area_bess_m2"]
    area_eolica_reservada = int(n_aeros) * AREA_RESERVADA_EOLICA_POR_AERO_M2
    area_residual = max(0.0, AREA_DISPONIBLE_M2 - area_eolica_reservada)
    area_total_screening = area_fv_bess + area_eolica_reservada

    cumple_aeros = 0 <= int(n_aeros) <= N_AEROS_MAX_ESPACIO
    cumple_area = area_fv_bess <= area_residual + 1e-9
    return {
        **fv, **bess,
        "area_eolica_reservada_m2": float(area_eolica_reservada),
        "area_residual_tras_eolica_m2": float(area_residual),
        "area_fv_mas_bess_m2": float(area_fv_bess),
        "area_total_screening_m2": float(area_total_screening),
        "uso_area_fv_bess_pct": float(100.0 * area_fv_bess / AREA_DISPONIBLE_M2),
        "uso_area_eolica_pct": float(100.0 * area_eolica_reservada / AREA_DISPONIBLE_M2),
        "uso_area_total_screening_pct": float(100.0 * area_total_screening / AREA_DISPONIBLE_M2),
        "cumple_espacio_aeros": bool(cumple_aeros),
        "cumple_area_fv_bess": bool(cumple_area),
        "cumple_screening_espacial": bool(cumple_aeros and cumple_area),
    }


def _normalizar_texto(x: object) -> str:
    s = unicodedata.normalize("NFKD", str(x))
    s = "".join(c for c in s if not unicodedata.combining(c))
    s = s.casefold()
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return " ".join(s.split())


def _buscar_columna(df: pd.DataFrame, *terminos: str) -> str:
    """
    Busca una columna que contenga todos los términos indicados como TOKENS,
    ignorando mayúsculas, acentos, saltos de línea y signos.

    Importante: se compara por palabras completas y no por subcadenas.
    Así, por ejemplo, "carga" NO coincide con "descarga".
    """
    tokens_objetivo: set[str] = set()
    for termino in terminos:
        tokens_objetivo.update(_normalizar_texto(termino).split())

    coincidencias: list[str] = []

    for c in df.columns:
        tokens_columna = set(_normalizar_texto(c).split())
        if tokens_objetivo.issubset(tokens_columna):
            coincidencias.append(c)

    if not coincidencias:
        raise KeyError(
            f"No encontré una columna con los términos {terminos}.\n"
            f"Columnas disponibles:\n{list(df.columns)}"
        )
    if len(coincidencias) > 1:
        raise KeyError(
            f"La búsqueda {terminos} es ambigua. Coincidencias: {coincidencias}"
        )
    return coincidencias[0]


def _valor_fila(r: pd.Series, *terminos: str) -> float:
    df_aux = pd.DataFrame(columns=r.index)
    col = _buscar_columna(df_aux, *terminos)
    return float(r[col])


def _valor_fila_exacta(r: pd.Series, nombre_columna: str) -> float:
    """
    Busca primero una columna por nombre normalizado EXACTO.

    Sirve para distinguir, por ejemplo:
      - "Capacidad BESS [MWh]" (capacidad nominal instalada)
      - "Capacidad BESS disponible [MWh]" (capacidad degradada del año)
    """
    objetivo = _normalizar_texto(nombre_columna)
    coincidencias = [c for c in r.index if _normalizar_texto(c) == objetivo]

    if len(coincidencias) == 1:
        return float(r[coincidencias[0]])
    if len(coincidencias) > 1:
        raise KeyError(
            f"Hay más de una columna equivalente a {nombre_columna!r}: {coincidencias}"
        )
    raise KeyError(
        f"No encontré la columna exacta {nombre_columna!r}.\n"
        f"Columnas disponibles:\n{list(r.index)}"
    )


def validar_configuracion(cfg: Configuracion) -> None:
    if cfg.n_aeros < 0 or int(cfg.n_aeros) != cfg.n_aeros:
        raise ValueError("n_aeros debe ser un entero >= 0.")
    if cfg.p_fv_mw < 0:
        raise ValueError("P_FV no puede ser negativa.")

    if not (P_CONTRATADA_MIN_MW <= cfg.p_contratada_mw <= P_CONTRATADA_MAX_MW):
        raise ValueError(
            f"P_contratada debe quedar entre {P_CONTRATADA_MIN_MW:g} y "
            f"{P_CONTRATADA_MAX_MW:g} MW."
        )
    if cfg.p_contratada_mw > cfg.limite_t1_mw + 1e-9:
        raise ValueError("P_contratada no puede superar el límite de T1.")
    if cfg.limite_t1_mw > LIMITE_T1_MW + 1e-9:
        raise ValueError(f"El límite de T1 no puede superar {LIMITE_T1_MW:g} MW.")

    if cfg.p_bess_mw < 0 or cfg.e_bess_mwh < 0:
        raise ValueError("P_BESS y E_BESS deben ser >= 0.")
    if cfg.e_bess_mwh == 0 and cfg.p_bess_mw > 0:
        raise ValueError("No puede existir P_BESS > 0 con E_BESS = 0.")
    if cfg.e_bess_mwh > 0 and cfg.p_bess_mw > P_RATE_MAX * cfg.e_bess_mwh + 1e-9:
        raise ValueError(
            f"P_BESS={cfg.p_bess_mw:.6f} MW supera el máximo 0,5C para "
            f"E_BESS={cfg.e_bess_mwh:.6f} MWh "
            f"(máximo {P_RATE_MAX * cfg.e_bess_mwh:.6f} MW)."
        )

    if not (0 < cfg.eta_carga <= 1 and 0 < cfg.eta_descarga <= 1):
        raise ValueError("Los rendimientos deben quedar en (0,1].")
    if not (0 <= cfg.soc_min < cfg.soc_max <= 1):
        raise ValueError("Debe cumplirse 0 <= SOC_min < SOC_max <= 1.")
    if not (cfg.soc_min <= cfg.soc_inicial_frac <= cfg.soc_max):
        raise ValueError("SOC inicial debe estar entre SOC_min y SOC_max.")

    if cfg.n_containers > 0:
        e_cont = cfg.n_containers * cfg.e_container_mwh
        if not math.isclose(cfg.e_bess_mwh, e_cont, rel_tol=0, abs_tol=1e-6):
            warnings.warn(
                "E_BESS no coincide exactamente con n_containers * energía/container. "
                f"E_BESS={cfg.e_bess_mwh:.6f} MWh; containers={e_cont:.6f} MWh.",
                RuntimeWarning,
            )

    if not math.isclose(cfg.p_contratada_mw, round(cfg.p_contratada_mw), abs_tol=1e-9):
        warnings.warn(
            "El pliego presenta escalones enteros de potencia contratada (6..15 MW). "
            "El simulador admite un valor continuo, pero en la optimización final "
            "conviene tratarlo como variable discreta.",
            RuntimeWarning,
        )


def buscar_excel_por_defecto() -> Path:
    """Busca automáticamente el Excel del proyecto en ubicaciones habituales.

    Orden de búsqueda:
    1) carpeta del script;
    2) carpeta desde la que se ejecuta Python;
    3) ~/Documents/Facultad/Taller integrador.

    Si hay más de un Balance_anual-v3* en una misma ubicación, pide --excel
    para evitar elegir silenciosamente el archivo equivocado.
    """
    carpetas = [
        Path(__file__).resolve().parent,
        Path.cwd(),
        Path.home() / "Documents" / "Facultad" / "Taller integrador",
    ]

    # Eliminar duplicados conservando el orden.
    carpetas_unicas = []
    for carpeta in carpetas:
        carpeta = carpeta.resolve()
        if carpeta not in carpetas_unicas:
            carpetas_unicas.append(carpeta)

    for carpeta in carpetas_unicas:
        if not carpeta.exists():
            continue

        exactos = [
            carpeta / "Balance_anual-v3.xlsm",
            carpeta / "Balance_anual-v3.xlsx",
        ]
        for p in exactos:
            if p.exists():
                return p

        encontrados = sorted(
            p for p in carpeta.glob("Balance_anual-v3*")
            if p.suffix.lower() in {".xlsm", ".xlsx"}
        )
        if len(encontrados) == 1:
            return encontrados[0]
        if len(encontrados) > 1:
            raise FileNotFoundError(
                f"Encontré varios Excel Balance_anual-v3* en {carpeta}. "
                "Usá --excel para indicar cuál:\n  "
                + "\n  ".join(str(p) for p in encontrados)
            )

    lugares = "\n  ".join(str(p) for p in carpetas_unicas)
    raise FileNotFoundError(
        "No encontré Balance_anual-v3*.xlsm/.xlsx automáticamente. "
        "Busqué en:\n  " + lugares +
        "\nUsá --excel RUTA_AL_ARCHIVO para indicarlo explícitamente."
    )


# =============================================================================
# LECTURA DEL EXCEL
# =============================================================================

def leer_configuracion_excel(ruta_excel: str | Path) -> Configuracion:
    """Lee la fila de parámetros actualmente guardada en la hoja 'Parametros'."""
    df = pd.read_excel(ruta_excel, sheet_name="Parametros", nrows=1)
    if df.empty:
        raise ValueError("La hoja 'Parametros' no contiene la fila esperada.")
    r = df.iloc[0]

    # En Parametros usamos nombres exactos normalizados. Es más seguro que
    # búsquedas parciales porque la hoja contiene pares como carga/descarga y
    # capacidad nominal/capacidad disponible.
    cfg = Configuracion(
        n_aeros=int(_valor_fila_exacta(r, "Cantidad aerogeneradores GE")),
        p_fv_mw=_valor_fila_exacta(r, "Potencia FV instalada [MW]"),
        p_contratada_mw=_valor_fila_exacta(r, "P contratada de la red [MW]"),
        limite_t1_mw=_valor_fila_exacta(r, "Límite T1 [MW]"),
        p_bess_mw=_valor_fila_exacta(r, "Potencia BESS [MW]"),
        # Capacidad NOMINAL instalada. No usar "Capacidad BESS disponible".
        e_bess_mwh=_valor_fila_exacta(r, "Capacidad BESS [MWh]"),
        eta_carga=_valor_fila_exacta(r, "Rendimiento carga"),
        eta_descarga=_valor_fila_exacta(r, "Rendimiento descarga"),
        soc_min=_valor_fila_exacta(r, "SOC mínimo"),
        soc_max=_valor_fila_exacta(r, "SOC máximo"),
        soc_inicial_frac=_valor_fila_exacta(r, "SOC inicial"),
        n_containers=int(_valor_fila_exacta(r, "Cantidad containers BESS")),
        e_container_mwh=_valor_fila_exacta(r, "Energía/container [MWh]"),
    )
    validar_configuracion(cfg)
    return cfg


def cargar_perfiles(ruta_excel: str | Path, p_fv_referencia_mw: float) -> pd.DataFrame:
    """
    Reutiliza perfiles ya calculados/validados en el Excel.

    Demanda:
      Las 24 filas de la hoja 'Demanda' se interpretan por ORDEN:
      fila 1 -> hora 00:00, ..., fila 24 -> hora 23:00.
      Esto reproduce el Balance anual, aunque la columna original esté rotulada 1..24.

    FV:
      Usa 'P módulo final [W]' antes del límite de 15 MW y lo normaliza con la
      potencia FV de referencia del Excel. Luego, al simular, se escala por P_FV,
      se limita a 15 MW y finalmente se aplica degradación anual.

    Eólico:
      Usa potencia horaria por aerogenerador para GE 3.4 y GE 3.8.

    Los años de las fuentes no se cruzan por fecha: se conserva el orden de las
    8784 horas tal como se hizo en el Excel.
    """
    if p_fv_referencia_mw <= 0:
        raise ValueError("La potencia FV de referencia debe ser > 0.")

    demanda = pd.read_excel(ruta_excel, sheet_name="Demanda", nrows=24)
    solar = pd.read_excel(ruta_excel, sheet_name="solar", header=1, nrows=HORAS_ANIO)
    eolico = pd.read_excel(ruta_excel, sheet_name="Eolico 2008", nrows=HORAS_ANIO)

    if len(demanda) < 24:
        raise ValueError(f"Demanda tiene {len(demanda)} filas; se esperaban 24.")
    demanda = demanda.iloc[:24].copy()
    if len(solar) != HORAS_ANIO:
        raise ValueError(f"solar tiene {len(solar)} filas; se esperaban {HORAS_ANIO}.")
    if len(eolico) != HORAS_ANIO:
        raise ValueError(f"Eolico 2008 tiene {len(eolico)} filas; se esperaban {HORAS_ANIO}.")

    col_dem_ver = _buscar_columna(demanda, "demanda", "verano")
    col_dem_inv = _buscar_columna(demanda, "demanda", "invierno")
    col_banda = _buscar_columna(demanda, "banda", "horaria")
    col_precio = _buscar_columna(demanda, "precio", "red")

    col_solar_final = _buscar_columna(solar, "p", "modulo", "final")
    col_eol_34 = _buscar_columna(eolico, "p", "ge", "3 4", "aerogenerador")
    col_eol_38 = _buscar_columna(eolico, "p", "ge", "3 8", "aerogenerador")

    fechas = pd.date_range("2020-01-01 00:00:00", periods=HORAS_ANIO, freq="h")
    horas = fechas.hour.to_numpy(dtype=int)

    dem_ver_24 = pd.to_numeric(demanda[col_dem_ver], errors="raise").to_numpy(dtype=float)
    dem_inv_24 = pd.to_numeric(demanda[col_dem_inv], errors="raise").to_numpy(dtype=float)
    banda_24 = demanda[col_banda].astype(str).str.strip().to_numpy(dtype=object)
    precio_24 = pd.to_numeric(demanda[col_precio], errors="raise").to_numpy(dtype=float)

    # El Excel considera Verano de noviembre a abril e Invierno de mayo a octubre.
    es_verano = (fechas.month >= 11) | (fechas.month <= 4)
    demanda_mw = np.where(es_verano, dem_ver_24[horas], dem_inv_24[horas])
    banda = banda_24[horas]
    tarifa_base = precio_24[horas]

    solar_final_w = pd.to_numeric(solar[col_solar_final], errors="raise").to_numpy(dtype=float)
    fv_pu_sin_limite = solar_final_w / (p_fv_referencia_mw * 1e6)

    e34 = pd.to_numeric(eolico[col_eol_34], errors="raise").to_numpy(dtype=float) / 1000.0
    e38 = pd.to_numeric(eolico[col_eol_38], errors="raise").to_numpy(dtype=float) / 1000.0

    for nombre, arr in {
        "demanda_mw": demanda_mw,
        "tarifa_base": tarifa_base,
        "fv_pu_sin_limite": fv_pu_sin_limite,
        "eolico_34": e34,
        "eolico_38": e38,
    }.items():
        if len(arr) != HORAS_ANIO or not np.isfinite(arr).all():
            raise ValueError(f"El perfil {nombre} tiene NaN/inf o longitud incorrecta.")

    bandas_validas = {"Valle", "Resto", "Pico"}
    bandas_encontradas = set(map(str, banda))
    if not bandas_encontradas.issubset(bandas_validas):
        raise ValueError(f"Bandas no reconocidas en Demanda: {bandas_encontradas}")

    return pd.DataFrame(
        {
            "fecha_hora": fechas,
            "hora": horas,
            "estacion": np.where(es_verano, "Verano", "Invierno"),
            "demanda_mw": demanda_mw,
            "banda": banda,
            "tarifa_base_usd_mwh": tarifa_base,
            "fv_pu_sin_limite": fv_pu_sin_limite,
            "eolico_34_por_aero_mw": e34,
            "eolico_38_por_aero_mw": e38,
        }
    )


# =============================================================================
# SIMULACIÓN HORARIA
# =============================================================================

def simular_anio(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    p_contratada_mw: float,
    anio: int,
    soh_inicial: float,
    ciclos_acum_inicial: float = 0.0,
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    exportar_excedente: bool = True,
    escalamiento_costos: float = ESCALAMIENTO_COSTOS,
) -> tuple[pd.DataFrame, dict]:
    """
    Simula las 8784 horas de un año.

    Estrategia actual, ANTES de optimizar el despacho económico:
      1) FV + eólico abastecen demanda.
      2) Excedente renovable carga BESS.
      3) Si déficit > P_contratada/T1, BESS descarga obligatoriamente.
      4) La red cubre el déficit remanente hasta el límite contratado.
      5) En Valle, la red puede cargar BESS usando el margen contratado disponible.
      6) Descarga económica adicional = 0.
      7) Excedente remanente se exporta hasta 15 MW; lo que supere T1 se recorta.

    SOC:
      SOC_inicio(h) = SOC_fin(h-1), siempre secuencial.
      Al comienzo de cada año, SOC = soc_inicial_frac de la capacidad disponible.
    """
    if len(perfiles) != HORAS_ANIO:
        raise ValueError(f"Se esperaban {HORAS_ANIO} horas.")
    if tipo_aero not in P_NOMINAL_AERO_MW:
        raise ValueError("tipo_aero debe ser 'GE3.4' o 'GE3.8'.")
    if not 1 <= anio <= 20:
        raise ValueError("anio debe estar entre 1 y 20.")
    if not (SOH_EOL <= soh_inicial <= 1.0):
        raise ValueError(f"SOH inicial debe estar entre {SOH_EOL:.2f} y 1,00.")
    if p_fv_mw < 0 or n_aeros < 0 or int(n_aeros) != n_aeros:
        raise ValueError("P_FV debe ser >= 0 y n_aeros un entero >= 0.")
    if p_bess_mw < 0 or e_bess_mwh < 0:
        raise ValueError("P_BESS y E_BESS deben ser >= 0.")
    if e_bess_mwh == 0 and p_bess_mw > 0:
        raise ValueError("P_BESS debe ser 0 si E_BESS es 0.")
    if e_bess_mwh > 0 and p_bess_mw > P_RATE_MAX * e_bess_mwh + 1e-9:
        raise ValueError("P_BESS supera el límite 0,5C del BESS.")
    if not (P_CONTRATADA_MIN_MW <= p_contratada_mw <= P_CONTRATADA_MAX_MW):
        raise ValueError("P_contratada debe estar entre 6 y 15 MW.")
    if p_contratada_mw > limite_t1_mw + 1e-9:
        raise ValueError("P_contratada no puede superar T1.")

    banda = perfiles["banda"].to_numpy(dtype=object)
    tarifa_base = perfiles["tarifa_base_usd_mwh"].to_numpy(dtype=float)
    tarifa_anio = tarifa_base * (1.0 + escalamiento_costos) ** (anio - 1)

    factor_fv = factor_degradacion_fv(anio)

    # Misma convención que el Excel: escala P_FV -> limita a 15 MW -> degrada.
    p_fv_sin_degradar = np.minimum(
        p_fv_mw * perfiles["fv_pu_sin_limite"].to_numpy(dtype=float),
        limite_t1_mw,
    )
    p_fv = p_fv_sin_degradar * factor_fv

    if tipo_aero == "GE3.4":
        p_eolico = n_aeros * perfiles["eolico_34_por_aero_mw"].to_numpy(dtype=float)
    else:
        p_eolico = n_aeros * perfiles["eolico_38_por_aero_mw"].to_numpy(dtype=float)

    demanda = perfiles["demanda_mw"].to_numpy(dtype=float)
    renovable = p_fv + p_eolico
    p_neta = demanda - renovable
    deficit = np.maximum(p_neta, 0.0)
    excedente = np.maximum(-p_neta, 0.0)

    p_red_max = min(p_contratada_mw, limite_t1_mw)

    capacidad_disponible = e_bess_mwh * soh_inicial
    e_soc_min = capacidad_disponible * soc_min
    e_soc_max = capacidad_disponible * soc_max
    soc0 = capacidad_disponible * soc_inicial_frac if e_bess_mwh > 0 else 0.0

    n = HORAS_ANIO
    soc_inicio_arr = np.zeros(n)
    carga_ren_arr = np.zeros(n)
    descarga_obl_arr = np.zeros(n)
    carga_red_arr = np.zeros(n)
    descarga_econ_arr = np.zeros(n)  # se activa en una etapa posterior
    soc_fin_arr = np.zeros(n)
    red_consumo_arr = np.zeros(n)
    red_import_arr = np.zeros(n)
    export_arr = np.zeros(n)
    curtail_arr = np.zeros(n)
    no_abast_arr = np.zeros(n)
    costo_arr = np.zeros(n)
    p_t1_arr = np.zeros(n)
    error_balance_arr = np.zeros(n)

    soc_anterior = soc0

    for h in range(n):
        soc_ini = soc_anterior
        soc_inicio_arr[h] = soc_ini

        # 1) CARGA DESDE RENOVABLE
        if e_bess_mwh > 0 and p_bess_mw > 0:
            margen_soc_carga = max(0.0, (e_soc_max - soc_ini) / (eta_carga * DT_H))
            carga_ren = min(excedente[h], p_bess_mw, margen_soc_carga)
        else:
            carga_ren = 0.0

        soc_1 = soc_ini + carga_ren * eta_carga * DT_H

        # 2) DESCARGA OBLIGATORIA PARA PEAK SHAVING
        descarga_necesaria = max(deficit[h] - p_red_max, 0.0)
        if e_bess_mwh > 0 and p_bess_mw > 0:
            max_descarga_soc = max(0.0, (soc_1 - e_soc_min) * eta_descarga / DT_H)
            descarga_obl = min(descarga_necesaria, p_bess_mw, max_descarga_soc)
        else:
            descarga_obl = 0.0

        soc_2 = soc_1 - descarga_obl / eta_descarga * DT_H

        # 3) RED PARA CONSUMO
        red_consumo = min(max(deficit[h] - descarga_obl, 0.0), p_red_max)

        # 4) CARGA DESDE RED EN VALLE
        carga_red = 0.0
        if banda[h] == "Valle" and e_bess_mwh > 0 and p_bess_mw > 0:
            margen_p_bess = max(0.0, p_bess_mw - carga_ren)
            margen_red = max(0.0, p_red_max - red_consumo)
            margen_soc = max(0.0, (e_soc_max - soc_2) / (eta_carga * DT_H))
            carga_red = min(margen_p_bess, margen_red, margen_soc)

        # 5) DESCARGA ECONÓMICA ADICIONAL: todavía apagada
        descarga_econ = 0.0

        soc_fin = (
            soc_2
            + carga_red * eta_carga * DT_H
            - descarga_econ / eta_descarga * DT_H
        )

        # 6) RED, EXPORTACIÓN Y VERTIDO/CURTAILMENT
        red_import = red_consumo + carga_red
        excedente_remanente = max(excedente[h] - carga_ren, 0.0)

        if exportar_excedente:
            export = min(excedente_remanente, limite_t1_mw)
            curtail = max(excedente_remanente - export, 0.0)
        else:
            export = 0.0
            curtail = excedente_remanente

        no_abast = max(deficit[h] - descarga_obl - descarga_econ - red_consumo, 0.0)
        p_t1 = red_import - export  # + importa / - exporta

        # El excedente exportado no genera ingresos; sólo se paga importación.
        costo = red_import * tarifa_anio[h] * DT_H

        # Balance completo incluyendo demanda no abastecida como déficit explícito.
        error_balance = (
            renovable[h]
            + descarga_obl
            + descarga_econ
            + red_import
            + no_abast
            - demanda[h]
            - carga_ren
            - carga_red
            - export
            - curtail
        )

        carga_ren_arr[h] = carga_ren
        descarga_obl_arr[h] = descarga_obl
        carga_red_arr[h] = carga_red
        descarga_econ_arr[h] = descarga_econ
        soc_fin_arr[h] = soc_fin
        red_consumo_arr[h] = red_consumo
        red_import_arr[h] = red_import
        export_arr[h] = export
        curtail_arr[h] = curtail
        no_abast_arr[h] = no_abast
        costo_arr[h] = costo
        p_t1_arr[h] = p_t1
        error_balance_arr[h] = error_balance

        soc_anterior = soc_fin

    # Chequeos físicos que deben cumplirse incluso si la configuración es inviable.
    tol = 1e-8
    if np.max(np.abs(error_balance_arr)) > tol:
        raise RuntimeError(
            f"El balance horario no cierra. Error máximo = "
            f"{np.max(np.abs(error_balance_arr)):.3e} MW."
        )
    if np.max(red_import_arr) > p_red_max + tol:
        raise RuntimeError("La importación de red superó P_contratada/T1.")
    if np.max(np.abs(p_t1_arr)) > limite_t1_mw + tol:
        raise RuntimeError("El flujo neto por T1 superó 15 MW.")
    if e_bess_mwh > 0:
        if np.min(soc_fin_arr) < e_soc_min - tol or np.max(soc_fin_arr) > e_soc_max + tol:
            raise RuntimeError("El SOC salió de sus límites.")
    if np.max(carga_ren_arr + carga_red_arr) > p_bess_mw + tol:
        raise RuntimeError("La potencia total de carga superó P_BESS.")
    if np.max(descarga_obl_arr + descarga_econ_arr) > p_bess_mw + tol:
        raise RuntimeError("La potencia total de descarga superó P_BESS.")

    # Ciclos equivalentes
    energia_desc_terminal = float((descarga_obl_arr + descarga_econ_arr).sum() * DT_H)
    if e_bess_mwh > 0:
        energia_desc_interna = energia_desc_terminal / eta_descarga
        ciclos_eq = energia_desc_interna / (DOD_CICLO_REFERENCIA * e_bess_mwh)
    else:
        energia_desc_interna = 0.0
        ciclos_eq = 0.0

    ciclos_acum_final = ciclos_acum_inicial + ciclos_eq
    soh_teorico_final = 1.0 - DEGRADACION_POR_CICLO_EQ * ciclos_acum_final
    soh_final = max(SOH_EOL, soh_teorico_final)
    capacidad_final = e_bess_mwh * soh_final

    resultado = pd.DataFrame(
        {
            "Fecha/hora": perfiles["fecha_hora"].to_numpy(),
            "Hora": perfiles["hora"].to_numpy(),
            "Estación": perfiles["estacion"].to_numpy(),
            "Banda": banda,
            "Tarifa base [USD/MWh]": tarifa_base,
            "Tarifa año [USD/MWh]": tarifa_anio,
            "Demanda [MW]": demanda,
            "FV [MW]": p_fv,
            "Eólico [MW]": p_eolico,
            "Renovable [MW]": renovable,
            "P neta [MW]": p_neta,
            "Déficit [MW]": deficit,
            "Excedente renovable [MW]": excedente,
            "SOC inicio [MWh]": soc_inicio_arr,
            "Carga desde renovable [MW]": carga_ren_arr,
            "Descarga obligatoria [MW]": descarga_obl_arr,
            "Carga desde red en Valle [MW]": carga_red_arr,
            "Descarga económica [MW]": descarga_econ_arr,
            "SOC fin [MWh]": soc_fin_arr,
            "P red para consumo [MW]": red_consumo_arr,
            "P red importada total [MW]": red_import_arr,
            "P exportada [MW]": export_arr,
            "Curtailment / vertido [MW]": curtail_arr,
            "P T1 neta (+import/-export) [MW]": p_t1_arr,
            "Demanda no abastecida [MW]": no_abast_arr,
            "Costo red horario [USD]": costo_arr,
            "Error balance [MW]": error_balance_arr,
        }
    )

    energia_red_banda: dict[str, float] = {}
    costo_red_banda: dict[str, float] = {}
    for b in ("Valle", "Resto", "Pico"):
        mask = banda == b
        energia_red_banda[b] = float(red_import_arr[mask].sum() * DT_H)
        costo_red_banda[b] = float(costo_arr[mask].sum())

    resumen = {
        "anio": anio,
        "factor_fv": factor_fv,
        "soh_inicial": soh_inicial,
        "soh_final": soh_final,
        "eol_alcanzado": bool(soh_teorico_final <= SOH_EOL),
        "capacidad_bess_inicio_mwh": capacidad_disponible,
        "capacidad_bess_final_mwh": capacidad_final,
        "soc_inicial_mwh": soc0,
        "soc_final_mwh": float(soc_fin_arr[-1]),
        "soc_minimo_observado_mwh": float(soc_fin_arr.min()),
        "soc_maximo_observado_mwh": float(soc_fin_arr.max()),
        "energia_demanda_mwh": float(demanda.sum() * DT_H),
        "energia_fv_mwh": float(p_fv.sum() * DT_H),
        "energia_eolica_mwh": float(p_eolico.sum() * DT_H),
        "energia_red_total_mwh": float(red_import_arr.sum() * DT_H),
        "energia_red_valle_mwh": energia_red_banda["Valle"],
        "energia_red_resto_mwh": energia_red_banda["Resto"],
        "energia_red_pico_mwh": energia_red_banda["Pico"],
        "carga_renovable_mwh": float(carga_ren_arr.sum() * DT_H),
        "carga_red_valle_mwh": float(carga_red_arr.sum() * DT_H),
        "descarga_obligatoria_mwh": float(descarga_obl_arr.sum() * DT_H),
        "descarga_economica_mwh": float(descarga_econ_arr.sum() * DT_H),
        "energia_exportada_mwh": float(export_arr.sum() * DT_H),
        "curtailment_mwh": float(curtail_arr.sum() * DT_H),
        "demanda_no_abastecida_mwh": float(no_abast_arr.sum() * DT_H),
        "horas_no_cumple": int(np.count_nonzero(no_abast_arr > 1e-9)),
        "max_deficit_no_abastecido_mw": float(no_abast_arr.max()),
        "cumple_demanda": bool(np.max(no_abast_arr) <= 1e-9),
        "max_importacion_red_mw": float(red_import_arr.max()),
        "max_abs_flujo_t1_mw": float(np.max(np.abs(p_t1_arr))),
        "energia_descargada_interna_mwh": energia_desc_interna,
        "ciclos_equivalentes": float(ciclos_eq),
        "ciclos_acumulados_final": float(ciclos_acum_final),
        "costo_valle_usd": costo_red_banda["Valle"],
        "costo_resto_usd": costo_red_banda["Resto"],
        "costo_pico_usd": costo_red_banda["Pico"],
        "costo_red_total_usd": float(costo_arr.sum()),
        "max_error_balance_mw": float(np.max(np.abs(error_balance_arr))),
    }

    return resultado, resumen

def simular_anio_economico(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    p_contratada_mw: float,
    anio: int,
    soh_inicial: float,
    ciclos_acum_inicial: float = 0.0,
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    exportar_excedente: bool = True,
    escalamiento_costos: float = ESCALAMIENTO_COSTOS,
    exigir_soc_final_igual_inicial: bool = False,
    max_ciclos_anio: float | None = None,
    objetivo_lp: Literal["costo", "min_descarga"] = "costo",
    devolver_detalle: bool = True,
) -> tuple[pd.DataFrame | None, dict]:
    """
    Despacho anual del BESS por programación lineal.

    objetivo_lp="costo": minimiza el costo horario de compra a red.
    objetivo_lp="min_descarga": minimiza throughput de descarga y se usa para
    estimar la reserva técnica mínima del BESS.

    max_ciclos_anio permite imponer un presupuesto anual de degradación.
    """
    if len(perfiles) != HORAS_ANIO:
        raise ValueError(f"Se esperaban {HORAS_ANIO} horas.")
    if tipo_aero not in P_NOMINAL_AERO_MW:
        raise ValueError("tipo_aero debe ser 'GE3.4' o 'GE3.8'.")
    if not 1 <= anio <= 20:
        raise ValueError("anio debe estar entre 1 y 20.")

    banda = perfiles["banda"].to_numpy(dtype=object)
    tarifa_base = perfiles["tarifa_base_usd_mwh"].to_numpy(dtype=float)
    tarifa_anio = tarifa_base * (1.0 + escalamiento_costos) ** (anio - 1)
    factor_fv = factor_degradacion_fv(anio)

    p_fv_sin_degradar = np.minimum(
        p_fv_mw * perfiles["fv_pu_sin_limite"].to_numpy(dtype=float), limite_t1_mw
    )
    p_fv = p_fv_sin_degradar * factor_fv
    if tipo_aero == "GE3.4":
        p_eolico = n_aeros * perfiles["eolico_34_por_aero_mw"].to_numpy(dtype=float)
    else:
        p_eolico = n_aeros * perfiles["eolico_38_por_aero_mw"].to_numpy(dtype=float)

    demanda = perfiles["demanda_mw"].to_numpy(dtype=float)
    renovable = p_fv + p_eolico
    p_neta = demanda - renovable
    deficit = np.maximum(p_neta, 0.0)
    excedente = np.maximum(-p_neta, 0.0)
    p_red_max = min(p_contratada_mw, limite_t1_mw)

    capacidad_disponible = e_bess_mwh * soh_inicial
    e_soc_min = capacidad_disponible * soc_min
    e_soc_max = capacidad_disponible * soc_max
    soc0 = capacidad_disponible * soc_inicial_frac if e_bess_mwh > 0 else 0.0

    if e_bess_mwh <= 1e-12 or p_bess_mw <= 1e-12:
        red_import = np.minimum(deficit, p_red_max)
        no_abast = np.maximum(deficit - p_red_max, 0.0)
        export = np.minimum(excedente, limite_t1_mw) if exportar_excedente else np.zeros(HORAS_ANIO)
        curtail = excedente - export
        costo = red_import * tarifa_anio * DT_H
        soc = np.zeros(HORAS_ANIO)
        carga_ren = np.zeros(HORAS_ANIO)
        carga_red = np.zeros(HORAS_ANIO)
        descarga = np.zeros(HORAS_ANIO)
    else:
        n = HORAS_ANIO
        i_cr, i_cg, i_d, i_s = 0, n, 2*n, 3*n
        nv = 4*n

        c = np.zeros(nv)
        if objetivo_lp == "costo":
            # El término tarifa*deficit es constante. Sólo optimizamos carga de red - descarga.
            c[i_cg:i_cg+n] = tarifa_anio * DT_H
            c[i_d:i_d+n] = -tarifa_anio * DT_H
        elif objetivo_lp == "min_descarga":
            # Objetivo técnico: usar la menor descarga posible. Un término muy pequeño
            # sobre carga de red evita soluciones degeneradas sin alterar el throughput.
            c[i_d:i_d+n] = DT_H
            c[i_cg:i_cg+n] = 1e-8 * tarifa_anio * DT_H
        else:
            raise ValueError("objetivo_lp debe ser 'costo' o 'min_descarga'.")

        bounds = []
        bounds += [(0.0, min(float(excedente[h]), p_bess_mw)) for h in range(n)]
        bounds += [(0.0, p_bess_mw) for _ in range(n)]
        bounds += [(0.0, min(float(deficit[h]), p_bess_mw)) for h in range(n)]
        bounds += [(e_soc_min, e_soc_max) for _ in range(n)]

        rows, cols, data, b_eq = [], [], [], []
        for h in range(n):
            r = len(b_eq)
            rows += [r, r, r, r]
            cols += [i_cr+h, i_cg+h, i_d+h, i_s+h]
            data += [-eta_carga*DT_H, -eta_carga*DT_H, DT_H/eta_descarga, 1.0]
            if h > 0:
                rows.append(r); cols.append(i_s+h-1); data.append(-1.0)
                b_eq.append(0.0)
            else:
                b_eq.append(soc0)
        if exigir_soc_final_igual_inicial:
            r = len(b_eq)
            rows.append(r); cols.append(i_s+n-1); data.append(1.0)
            b_eq.append(soc0)
        A_eq = coo_matrix((data, (rows, cols)), shape=(len(b_eq), nv)).tocsr()
        b_eq = np.asarray(b_eq, dtype=float)

        rows, cols, data, b_ub = [], [], [], []
        for h in range(n):
            # carga_ren + carga_red <= P_BESS
            r = len(b_ub)
            rows += [r, r]; cols += [i_cr+h, i_cg+h]; data += [1.0, 1.0]
            b_ub.append(p_bess_mw)
            # importación = deficit - descarga + carga_red <= P_red_max
            r = len(b_ub)
            rows += [r, r]; cols += [i_cg+h, i_d+h]; data += [1.0, -1.0]
            b_ub.append(p_red_max - deficit[h])

        if max_ciclos_anio is not None:
            if max_ciclos_anio < -1e-12:
                raise ValueError("max_ciclos_anio debe ser >= 0.")
            # N_eq = E_desc_terminal / (eta_desc * DOD_ref * E_nom)
            e_desc_terminal_max = max(0.0, float(max_ciclos_anio)) * (
                eta_descarga * DOD_CICLO_REFERENCIA * e_bess_mwh
            )
            r = len(b_ub)
            for h in range(n):
                rows.append(r); cols.append(i_d+h); data.append(DT_H)
            b_ub.append(e_desc_terminal_max)

        A_ub = coo_matrix((data, (rows, cols)), shape=(len(b_ub), nv)).tocsr()
        b_ub = np.asarray(b_ub, dtype=float)

        sol = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                      bounds=bounds, method="highs")
        if not sol.success:
            raise RuntimeError(f"Despacho económico LP falló en año {anio}: {sol.message}")

        x = sol.x
        carga_ren = x[i_cr:i_cr+n]
        carga_red = x[i_cg:i_cg+n]
        descarga = x[i_d:i_d+n]
        soc = x[i_s:i_s+n]
        red_import = np.maximum(deficit - descarga + carga_red, 0.0)
        no_abast = np.zeros(n)
        excedente_rem = np.maximum(excedente - carga_ren, 0.0)
        export = np.minimum(excedente_rem, limite_t1_mw) if exportar_excedente else np.zeros(n)
        curtail = excedente_rem - export
        costo = red_import * tarifa_anio * DT_H

    descarga_necesaria = np.maximum(deficit - p_red_max, 0.0)
    descarga_obl = np.minimum(descarga, descarga_necesaria)
    descarga_econ = np.maximum(descarga - descarga_obl, 0.0)
    red_consumo = np.maximum(deficit - descarga, 0.0)
    p_t1 = red_import - export
    soc_inicio = np.empty(HORAS_ANIO)
    soc_inicio[0] = soc0
    if HORAS_ANIO > 1:
        soc_inicio[1:] = soc[:-1]

    error_balance = (
        renovable + descarga + red_import + no_abast
        - demanda - carga_ren - carga_red - export - curtail
    )
    tol = 2e-6
    if np.max(np.abs(error_balance)) > tol:
        raise RuntimeError(f"Balance LP no cierra. Error máximo={np.max(np.abs(error_balance)):.3e} MW")
    if np.max(red_import) > p_red_max + tol:
        raise RuntimeError("Despacho LP superó P contratada/T1.")
    if np.max(np.abs(p_t1)) > limite_t1_mw + tol:
        raise RuntimeError("Despacho LP superó el límite neto T1.")

    energia_desc_terminal = float(descarga.sum() * DT_H)
    if e_bess_mwh > 0:
        energia_desc_interna = energia_desc_terminal / eta_descarga
        ciclos_eq = energia_desc_interna / (DOD_CICLO_REFERENCIA * e_bess_mwh)
    else:
        energia_desc_interna = 0.0
        ciclos_eq = 0.0
    ciclos_acum_final = ciclos_acum_inicial + ciclos_eq
    soh_teorico_final = 1.0 - DEGRADACION_POR_CICLO_EQ * ciclos_acum_final
    soh_final = max(SOH_EOL, soh_teorico_final)
    capacidad_final = e_bess_mwh * soh_final

    resultado = None
    if devolver_detalle:
        resultado = pd.DataFrame({
            "Fecha/hora": perfiles["fecha_hora"].to_numpy(),
            "Hora": perfiles["hora"].to_numpy(),
            "Estación": perfiles["estacion"].to_numpy(),
            "Banda": banda,
            "Tarifa base [USD/MWh]": tarifa_base,
            "Tarifa año [USD/MWh]": tarifa_anio,
            "Demanda [MW]": demanda,
            "FV [MW]": p_fv,
            "Eólico [MW]": p_eolico,
            "Renovable [MW]": renovable,
            "P neta [MW]": p_neta,
            "Déficit [MW]": deficit,
            "Excedente renovable [MW]": excedente,
            "SOC inicio [MWh]": soc_inicio,
            "Carga desde renovable [MW]": carga_ren,
            "Descarga obligatoria [MW]": descarga_obl,
            "Carga desde red [MW]": carga_red,
            "Descarga económica [MW]": descarga_econ,
            "Descarga total [MW]": descarga,
            "SOC fin [MWh]": soc,
            "P red para consumo [MW]": red_consumo,
            "P red importada total [MW]": red_import,
            "P exportada [MW]": export,
            "Curtailment / vertido [MW]": curtail,
            "P T1 neta (+import/-export) [MW]": p_t1,
            "Demanda no abastecida [MW]": no_abast,
            "Costo red horario [USD]": costo,
            "Error balance [MW]": error_balance,
        })

    energia_red_banda, costo_red_banda = {}, {}
    for b in ("Valle", "Resto", "Pico"):
        mask = banda == b
        energia_red_banda[b] = float(red_import[mask].sum() * DT_H)
        costo_red_banda[b] = float(costo[mask].sum())

    resumen = {
        "anio": anio,
        "factor_fv": factor_fv,
        "soh_inicial": soh_inicial,
        "soh_final": soh_final,
        "eol_alcanzado": bool(soh_teorico_final <= SOH_EOL),
        "capacidad_bess_inicio_mwh": capacidad_disponible,
        "capacidad_bess_final_mwh": capacidad_final,
        "soc_inicial_mwh": soc0,
        "soc_final_mwh": float(soc[-1]),
        "soc_minimo_observado_mwh": float(np.min(soc)),
        "soc_maximo_observado_mwh": float(np.max(soc)),
        "energia_demanda_mwh": float(demanda.sum() * DT_H),
        "energia_fv_mwh": float(p_fv.sum() * DT_H),
        "energia_eolica_mwh": float(p_eolico.sum() * DT_H),
        "energia_red_total_mwh": float(red_import.sum() * DT_H),
        "energia_red_valle_mwh": energia_red_banda["Valle"],
        "energia_red_resto_mwh": energia_red_banda["Resto"],
        "energia_red_pico_mwh": energia_red_banda["Pico"],
        "carga_renovable_mwh": float(carga_ren.sum() * DT_H),
        "carga_red_valle_mwh": float(carga_red[banda == "Valle"].sum() * DT_H),
        "carga_red_total_mwh": float(carga_red.sum() * DT_H),
        "descarga_obligatoria_mwh": float(descarga_obl.sum() * DT_H),
        "descarga_economica_mwh": float(descarga_econ.sum() * DT_H),
        "descarga_total_mwh": float(descarga.sum() * DT_H),
        "energia_exportada_mwh": float(export.sum() * DT_H),
        "curtailment_mwh": float(curtail.sum() * DT_H),
        "demanda_no_abastecida_mwh": float(no_abast.sum() * DT_H),
        "horas_no_cumple": int(np.count_nonzero(no_abast > 1e-9)),
        "max_deficit_no_abastecido_mw": float(no_abast.max()),
        "cumple_demanda": bool(np.max(no_abast) <= 1e-9),
        "max_importacion_red_mw": float(red_import.max()),
        "max_abs_flujo_t1_mw": float(np.max(np.abs(p_t1))),
        "energia_descargada_interna_mwh": energia_desc_interna,
        "ciclos_equivalentes": float(ciclos_eq),
        "ciclos_acumulados_final": float(ciclos_acum_final),
        "costo_valle_usd": costo_red_banda["Valle"],
        "costo_resto_usd": costo_red_banda["Resto"],
        "costo_pico_usd": costo_red_banda["Pico"],
        "costo_red_total_usd": float(costo.sum()),
        "max_error_balance_mw": float(np.max(np.abs(error_balance))),
        "despacho": (
            "económico LP anual" if objetivo_lp == "costo" else "LP técnico mínima descarga"
        ),
        "max_ciclos_anio": None if max_ciclos_anio is None else float(max_ciclos_anio),
    }
    return resultado, resumen


# =============================================================================
# ECONOMÍA
# =============================================================================

def calcular_capex(
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
) -> Capex:
    if tipo_aero not in P_NOMINAL_AERO_MW:
        raise ValueError("Tipo de aerogenerador no válido.")

    p_eol_instalada = n_aeros * P_NOMINAL_AERO_MW[tipo_aero]
    fv = CAPEX_FV_USD_MW * p_fv_mw
    eol = CAPEX_EOL_USD_MW * p_eol_instalada
    bess = (
        CAPEX_BESS_ENERGIA_USD_MWH * e_bess_mwh
        + CAPEX_BESS_POTENCIA_USD_MW * p_bess_mw
    )
    total = fv + eol + bess + CAPEX_FIJO_USD
    return Capex(fv, eol, bess, CAPEX_FIJO_USD, total)


def calcular_opex_anual(
    capex: Capex,
    anio: int,
    *,
    incluir_capex_fijo_en_cada_opex: bool = True,
) -> dict[str, float]:
    """
    Reproduce el criterio actual del Excel: a la base de OPEX de FV, eólico y BESS
    se le suma el CAPEX fijo de 400.000 USD a cada tecnología.
    """
    fijo = capex.fijo_usd if incluir_capex_fijo_en_cada_opex else 0.0
    esc = (1.0 + ESCALAMIENTO_COSTOS) ** (anio - 1)

    fv = (capex.fv_usd + fijo) * OPEX_FV_PCT * esc
    eol = (capex.eolico_usd + fijo) * OPEX_EOL_PCT * esc
    bess = (capex.bess_usd + fijo) * OPEX_BESS_PCT * esc
    return {
        "fv_usd": fv,
        "eolico_usd": eol,
        "bess_usd": bess,
        "total_usd": fv + eol + bess,
    }


def costo_potencia_contratada_anual(p_contratada_mw: float, anio: int) -> float:
    """
    Criterio adoptado con el docente/Excel:
    4500 USD/(MW·mes) * 12 meses, escalado 2,5 % anual.
    """
    return (
        p_contratada_mw
        * COSTO_PC_USD_MW_MES
        * 12.0
        * (1.0 + ESCALAMIENTO_COSTOS) ** (anio - 1)
    )



def buscar_soh_minimo_tecnico_anio(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    p_contratada_mw: float,
    anio: int,
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    exportar_excedente: bool = True,
    tol_soh: float = 5e-4,
) -> tuple[float, float]:
    """
    Busca por bisección el SOH mínimo que permite abastecer completamente el año
    usando el despacho técnico conservador (sin arbitraje económico).

    Devuelve (SOH mínimo técnico, ciclos mínimos técnicos aproximados en ese SOH).
    El resultado se usa sólo para reservar vida útil futura; no reemplaza el despacho
    económico LP que se ejecuta luego.
    """
    if e_bess_mwh <= 1e-12 or p_bess_mw <= 1e-12:
        # Sin BESS no hay estado de salud que planificar.
        _, r = simular_anio(
            perfiles,
            p_fv_mw=p_fv_mw, n_aeros=n_aeros, p_bess_mw=0.0, e_bess_mwh=0.0,
            p_contratada_mw=p_contratada_mw, anio=anio, soh_inicial=1.0,
            eta_carga=eta_carga, eta_descarga=eta_descarga,
            soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw, tipo_aero=tipo_aero,
            exportar_excedente=exportar_excedente,
        )
        if not r["cumple_demanda"]:
            raise RuntimeError(f"La configuración no abastece el año {anio} aun con SOH=1.")
        return 1.0, 0.0

    def evaluar(soh: float) -> tuple[bool, dict]:
        _, rr = simular_anio(
            perfiles,
            p_fv_mw=p_fv_mw, n_aeros=n_aeros,
            p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw, anio=anio, soh_inicial=soh,
            ciclos_acum_inicial=0.0,
            eta_carga=eta_carga, eta_descarga=eta_descarga,
            soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw, tipo_aero=tipo_aero,
            exportar_excedente=exportar_excedente,
        )
        return bool(rr["cumple_demanda"]), rr

    ok_hi, r_hi = evaluar(1.0)
    if not ok_hi:
        raise RuntimeError(f"La configuración no abastece el año {anio} ni con SOH=1.")

    ok_lo, r_lo = evaluar(SOH_EOL)
    if ok_lo:
        return SOH_EOL, float(r_lo["ciclos_equivalentes"])

    lo, hi = SOH_EOL, 1.0
    r_factible = r_hi
    while hi - lo > tol_soh:
        mid = 0.5 * (lo + hi)
        ok, rr = evaluar(mid)
        if ok:
            hi = mid
            r_factible = rr
        else:
            lo = mid

    # Recalcular exactamente en el extremo factible final.
    ok, r_factible = evaluar(hi)
    if not ok:
        raise RuntimeError(f"Error numérico buscando SOH técnico del año {anio}.")
    return float(hi), float(r_factible["ciclos_equivalentes"])


def preparar_plan_degradacion_multianual(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    p_contratada_mw: float,
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    exportar_excedente: bool = True,
    tol_soh: float = 5e-4,
) -> pd.DataFrame:
    """
    Construye una envolvente de ciclos acumulados para 20 años.

    Idea:
      - cada año tiene un SOH mínimo técnico para poder cumplir la demanda;
      - cada año necesita una cantidad mínima de ciclos por peak shaving;
      - hacia atrás se reserva esa vida útil mínima futura;
      - el resto de los ciclos queda disponible para arbitraje económico.

    Es una aproximación multianual de look-ahead mucho más liviana que resolver un LP
    horario único de 175.680 h. No inventa costo de degradación ni reemplazo.
    """
    if e_bess_mwh <= 1e-12 or p_bess_mw <= 1e-12:
        return pd.DataFrame({
            "Año": np.arange(1, 21),
            "SOH mínimo técnico": np.ones(20),
            "Ciclos mínimos técnicos": np.zeros(20),
            "Máx ciclos acumulados por SOH técnico": np.zeros(20),
            "Envolvente ciclos acumulados al inicio": np.zeros(20),
            "Envolvente ciclos acumulados siguiente inicio": np.zeros(20),
        })

    soh_min = np.zeros(20)
    ciclos_min = np.zeros(20)

    for i, anio in enumerate(range(1, 21)):
        soh_i, ciclos_i = buscar_soh_minimo_tecnico_anio(
            perfiles,
            p_fv_mw=p_fv_mw, n_aeros=n_aeros,
            p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw, anio=anio,
            eta_carga=eta_carga, eta_descarga=eta_descarga,
            soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw, tipo_aero=tipo_aero,
            exportar_excedente=exportar_excedente, tol_soh=tol_soh,
        )
        soh_min[i] = soh_i
        ciclos_min[i] = ciclos_i

    # SOH = 1 - degradación_por_ciclo * ciclos_acumulados.
    ciclos_max_por_soh = np.maximum(
        0.0,
        np.minimum(
            (1.0 - soh_min) / DEGRADACION_POR_CICLO_EQ,
            (1.0 - SOH_EOL) / DEGRADACION_POR_CICLO_EQ,
        ),
    )
    ciclos_eol = (1.0 - SOH_EOL) / DEGRADACION_POR_CICLO_EQ

    # V12: envolvente conservadora. Ya no permitimos que el último año "gaste"
    # degradación por debajo del SOH técnico del propio año. Para cada año se calcula:
    #   B_fin[y]    = máximo acumulado al FINAL del año y;
    #   B_inicio[y] = máximo acumulado al INICIO, reservando los ciclos técnicos.
    # Además B_fin[y] no puede superar lo admisible al inicio del año siguiente.
    B_inicio = np.zeros(20)
    B_fin = np.zeros(20)
    limite_inicio_siguiente = ciclos_eol
    for y in range(19, -1, -1):
        B_fin[y] = min(ciclos_max_por_soh[y], limite_inicio_siguiente)
        B_inicio[y] = B_fin[y] - ciclos_min[y]
        limite_inicio_siguiente = B_inicio[y]

    if B_inicio[0] < -1e-6:
        raise RuntimeError(
            "Ni reservando exclusivamente los ciclos técnicos mínimos el BESS alcanza "
            "para cumplir los 20 años con degradación conservadora dentro de cada año."
        )
    B_inicio = np.maximum(B_inicio, 0.0)
    B_fin = np.maximum(B_fin, 0.0)

    return pd.DataFrame({
        "Año": np.arange(1, 21),
        "SOH mínimo técnico": soh_min,
        "Ciclos mínimos técnicos": ciclos_min,
        "Máx ciclos acumulados por SOH técnico": ciclos_max_por_soh,
        "Envolvente ciclos acumulados al inicio": B_inicio,
        "Envolvente ciclos acumulados al final": B_fin,
        # alias conservado para compatibilidad con reportes previos
        "Envolvente ciclos acumulados siguiente inicio": B_fin,
    })


def simular_20_anios_consciente_degradacion(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    p_contratada_mw: float,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    exportar_excedente: bool = True,
    incluir_capex_fijo_en_cada_opex: bool = True,
    wacc: float = WACC,
    tol_soh_plan: float = 5e-4,
    devolver_detalle_anio1: bool = True,
) -> tuple[pd.DataFrame, float, pd.DataFrame | None, dict | None, pd.DataFrame]:
    """
    Despacho económico con look-ahead de degradación para los 20 años.

    No optimiza los 175.680 pasos en un único LP (demasiado pesado para evaluar muchos
    diseños). En cambio, calcula primero una reserva técnica futura de vida útil y luego
    resuelve 20 LP anuales, limitando los ciclos de cada año para no comprometer los años
    restantes. De esta forma la batería no puede 'comerse' el SOC/SOH futuro por arbitraje.

    Devuelve:
      detalle_20, costo_total_20, detalle_horario_anio1, resumen_anio1, plan_degradacion
    """
    capex = calcular_capex(p_fv_mw, n_aeros, p_bess_mw, e_bess_mwh, tipo_aero)

    if e_bess_mwh <= 1e-12 or p_bess_mw <= 1e-12:
        detalle, costo = simular_20_anios(
            perfiles,
            p_fv_mw=p_fv_mw, n_aeros=n_aeros,
            p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw, tipo_aero=tipo_aero,
            eta_carga=eta_carga, eta_descarga=eta_descarga,
            soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw, exportar_excedente=exportar_excedente,
            incluir_capex_fijo_en_cada_opex=incluir_capex_fijo_en_cada_opex,
            wacc=wacc, despacho_economico=False,
        )
        r1, s1 = simular_anio(
            perfiles,
            p_fv_mw=p_fv_mw, n_aeros=n_aeros,
            p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw, anio=1, soh_inicial=1.0,
            eta_carga=eta_carga, eta_descarga=eta_descarga,
            soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw, tipo_aero=tipo_aero,
            exportar_excedente=exportar_excedente,
        )
        plan = preparar_plan_degradacion_multianual(
            perfiles, p_fv_mw=p_fv_mw, n_aeros=n_aeros,
            p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw,
        )
        return detalle, costo, r1, s1, plan

    plan = preparar_plan_degradacion_multianual(
        perfiles,
        p_fv_mw=p_fv_mw, n_aeros=n_aeros,
        p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
        p_contratada_mw=p_contratada_mw,
        eta_carga=eta_carga, eta_descarga=eta_descarga,
        soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
        limite_t1_mw=limite_t1_mw, tipo_aero=tipo_aero,
        exportar_excedente=exportar_excedente, tol_soh=tol_soh_plan,
    )

    soh = 1.0
    ciclos_acum = 0.0
    filas: list[dict] = []
    detalle_anio1: pd.DataFrame | None = None
    resumen_anio1: dict | None = None

    for i, anio in enumerate(range(1, 21)):
        soh_min_tecnico = float(plan.iloc[i]["SOH mínimo técnico"])
        if soh + 2e-4 < soh_min_tecnico:
            raise RuntimeError(
                f"Año {anio}: SOH disponible={soh:.5f} < SOH técnico mínimo={soh_min_tecnico:.5f}."
            )

        max_acum_siguiente = float(
            plan.iloc[i]["Envolvente ciclos acumulados siguiente inicio"]
        )
        max_ciclos_anio = max(0.0, max_acum_siguiente - ciclos_acum)

        resultado, resumen = simular_anio_economico(
            perfiles,
            p_fv_mw=p_fv_mw, n_aeros=n_aeros,
            p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw, anio=anio,
            soh_inicial=soh, ciclos_acum_inicial=ciclos_acum,
            eta_carga=eta_carga, eta_descarga=eta_descarga,
            soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw, tipo_aero=tipo_aero,
            exportar_excedente=exportar_excedente,
            max_ciclos_anio=max_ciclos_anio,
            objetivo_lp="costo",
            exigir_soc_final_igual_inicial=True,
            devolver_detalle=(devolver_detalle_anio1 and i == 0),
        )

        if i == 0 and devolver_detalle_anio1:
            detalle_anio1 = resultado.copy() if resultado is not None else None
            resumen_anio1 = resumen.copy()

        opex = calcular_opex_anual(
            capex, anio,
            incluir_capex_fijo_en_cada_opex=incluir_capex_fijo_en_cada_opex,
        )
        costo_pc = costo_potencia_contratada_anual(p_contratada_mw, anio)
        costo_red = resumen["costo_red_total_usd"]
        costo_reemplazo = 0.0
        flujo_nominal = opex["total_usd"] + costo_pc + costo_red + costo_reemplazo
        vp = flujo_nominal / (1.0 + wacc) ** anio

        filas.append({
            "Año": anio,
            "Factor FV": resumen["factor_fv"],
            "SOH inicio": resumen["soh_inicial"],
            "SOH mínimo técnico": soh_min_tecnico,
            "SOH final": resumen["soh_final"],
            "Capacidad BESS inicio [MWh]": resumen["capacidad_bess_inicio_mwh"],
            "Capacidad BESS final [MWh]": resumen["capacidad_bess_final_mwh"],
            "Ciclos mínimos técnicos": float(plan.iloc[i]["Ciclos mínimos técnicos"]),
            "Ciclos máximos permitidos año": max_ciclos_anio,
            "Ciclos equivalentes año": resumen["ciclos_equivalentes"],
            "Ciclos equivalentes acumulados": resumen["ciclos_acumulados_final"],
            "EOL alcanzado": resumen["eol_alcanzado"],
            "Energía demanda [MWh]": resumen["energia_demanda_mwh"],
            "Energía FV [MWh]": resumen["energia_fv_mwh"],
            "Energía eólica [MWh]": resumen["energia_eolica_mwh"],
            "Energía red Valle [MWh]": resumen["energia_red_valle_mwh"],
            "Energía red Resto [MWh]": resumen["energia_red_resto_mwh"],
            "Energía red Pico [MWh]": resumen["energia_red_pico_mwh"],
            "Carga renovable BESS [MWh]": resumen.get("carga_renovable_mwh", 0.0),
            "Carga red total [MWh]": resumen.get("carga_red_total_mwh", resumen["carga_red_valle_mwh"]),
            "Descarga obligatoria [MWh]": resumen["descarga_obligatoria_mwh"],
            "Descarga económica [MWh]": resumen["descarga_economica_mwh"],
            "Descarga total BESS [MWh]": resumen.get("descarga_total_mwh", resumen["descarga_obligatoria_mwh"] + resumen["descarga_economica_mwh"]),
            "SOC mínimo observado [MWh]": resumen.get("soc_minimo_observado_mwh", float("nan")),
            "Costo red Valle [USD]": resumen["costo_valle_usd"],
            "Costo red Resto [USD]": resumen["costo_resto_usd"],
            "Costo red Pico [USD]": resumen["costo_pico_usd"],
            "Costo energía red [USD]": costo_red,
            "OPEX FV [USD]": opex["fv_usd"],
            "OPEX eólico [USD]": opex["eolico_usd"],
            "OPEX BESS [USD]": opex["bess_usd"],
            "OPEX total [USD]": opex["total_usd"],
            "Costo potencia contratada [USD]": costo_pc,
            "Costo reemplazo BESS [USD]": costo_reemplazo,
            "Flujo anual nominal [USD]": flujo_nominal,
            "VP flujo anual [USD]": vp,
            "Demanda no abastecida [MWh]": resumen["demanda_no_abastecida_mwh"],
            "Horas no cumple": resumen["horas_no_cumple"],
            "Cumple demanda": resumen["cumple_demanda"],
            "Exportación [MWh]": resumen["energia_exportada_mwh"],
            "Curtailment [MWh]": resumen["curtailment_mwh"],
            "Modo despacho": "económico LP + reserva multianual de degradación",
        })

        ciclos_acum = resumen["ciclos_acumulados_final"]
        soh = resumen["soh_final"]

    detalle = pd.DataFrame(filas)
    costo_total_20 = capex.total_usd + float(detalle["VP flujo anual [USD]"].sum())
    return detalle, costo_total_20, detalle_anio1, resumen_anio1, plan


def simular_20_anios(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    p_contratada_mw: float,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    exportar_excedente: bool = True,
    incluir_capex_fijo_en_cada_opex: bool = True,
    wacc: float = WACC,
    despacho_economico: bool = False,
) -> tuple[pd.DataFrame, float]:
    """
    Simula años 1..20 secuencialmente.

    Importante: reproduce el criterio adoptado en el Excel para el comienzo de cada
    año: SOC inicial = 1 (100 % de la CAPACIDAD DISPONIBLE de ese año).
    El SOH sí se hereda del año anterior.

    No hay reemplazo automático del BESS. Si SOH llega a 70 %, se marca EOL y se
    mantiene el piso de 70 % para no extrapolar la degradación más allá del dato.
    """
    capex = calcular_capex(p_fv_mw, n_aeros, p_bess_mw, e_bess_mwh, tipo_aero)

    soh = 1.0
    ciclos_acum = 0.0
    filas: list[dict] = []

    for anio in range(1, 21):
        simulador_anual = simular_anio_economico if despacho_economico else simular_anio
        _, resumen = simulador_anual(
            perfiles,
            p_fv_mw=p_fv_mw,
            n_aeros=n_aeros,
            p_bess_mw=p_bess_mw,
            e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw,
            anio=anio,
            soh_inicial=soh,
            ciclos_acum_inicial=ciclos_acum,
            eta_carga=eta_carga,
            eta_descarga=eta_descarga,
            soc_min=soc_min,
            soc_max=soc_max,
            soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw,
            tipo_aero=tipo_aero,
            exportar_excedente=exportar_excedente,
        )

        opex = calcular_opex_anual(
            capex,
            anio,
            incluir_capex_fijo_en_cada_opex=incluir_capex_fijo_en_cada_opex,
        )
        costo_pc = costo_potencia_contratada_anual(p_contratada_mw, anio)
        costo_red = resumen["costo_red_total_usd"]

        # Reemplazo BESS pendiente de definición: por ahora 0.
        costo_reemplazo = 0.0

        flujo_nominal = opex["total_usd"] + costo_pc + costo_red + costo_reemplazo
        vp = flujo_nominal / (1.0 + wacc) ** anio

        filas.append(
            {
                "Año": anio,
                "Factor FV": resumen["factor_fv"],
                "SOH inicio": resumen["soh_inicial"],
                "SOH final": resumen["soh_final"],
                "Capacidad BESS inicio [MWh]": resumen["capacidad_bess_inicio_mwh"],
                "Capacidad BESS final [MWh]": resumen["capacidad_bess_final_mwh"],
                "Ciclos equivalentes año": resumen["ciclos_equivalentes"],
                "Ciclos equivalentes acumulados": resumen["ciclos_acumulados_final"],
                "EOL alcanzado": resumen["eol_alcanzado"],
                "Energía red Valle [MWh]": resumen["energia_red_valle_mwh"],
                "Energía red Resto [MWh]": resumen["energia_red_resto_mwh"],
                "Energía red Pico [MWh]": resumen["energia_red_pico_mwh"],
                "Costo red Valle [USD]": resumen["costo_valle_usd"],
                "Costo red Resto [USD]": resumen["costo_resto_usd"],
                "Costo red Pico [USD]": resumen["costo_pico_usd"],
                "Costo energía red [USD]": costo_red,
                "OPEX FV [USD]": opex["fv_usd"],
                "OPEX eólico [USD]": opex["eolico_usd"],
                "OPEX BESS [USD]": opex["bess_usd"],
                "OPEX total [USD]": opex["total_usd"],
                "Costo potencia contratada [USD]": costo_pc,
                "Costo reemplazo BESS [USD]": costo_reemplazo,
                "Flujo anual nominal [USD]": flujo_nominal,
                "VP flujo anual [USD]": vp,
                "Demanda no abastecida [MWh]": resumen["demanda_no_abastecida_mwh"],
                "Horas no cumple": resumen["horas_no_cumple"],
                "Cumple demanda": resumen["cumple_demanda"],
                "Exportación [MWh]": resumen["energia_exportada_mwh"],
                "Curtailment [MWh]": resumen["curtailment_mwh"],
            }
        )

        ciclos_acum = resumen["ciclos_acumulados_final"]
        soh = resumen["soh_final"]

    detalle = pd.DataFrame(filas)
    costo_total_20 = capex.total_usd + float(detalle["VP flujo anual [USD]"].sum())
    return detalle, costo_total_20



# =============================================================================
# EVALUACIÓN Y OPTIMIZACIÓN DE DISEÑO
# =============================================================================

def evaluar_configuracion(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    p_contratada_mw: float,
    n_containers: int | None = None,
    e_container_mwh: float = E_CONTAINER_MWH_DEFAULT,
    potencia_modulo_fv_w: float = POTENCIA_MODULO_FV_W_DEFAULT,
    pitch_fv_m: float = PITCH_FV_DEFAULT_M,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    exportar_excedente: bool = True,
    wacc: float = WACC,
    despacho_economico: bool = False,
    despacho_multianual: bool = False,
) -> tuple[dict, pd.DataFrame | None]:
    """
    Evalúa UNA configuración de diseño durante 20 años.

    Si no abastece toda la demanda en cualquiera de los 20 años, se marca como
    no factible y el costo objetivo se devuelve como infinito.

    Esta es la función que usa el optimizador de diseño.
    """
    # Validaciones físicas básicas de la configuración candidata.
    if p_fv_mw < 0:
        raise ValueError("P_FV debe ser >= 0.")
    if n_aeros < 0 or int(n_aeros) != n_aeros:
        raise ValueError("n_aeros debe ser un entero >= 0.")
    if not (P_CONTRATADA_MIN_MW <= p_contratada_mw <= min(P_CONTRATADA_MAX_MW, limite_t1_mw)):
        raise ValueError("P_contratada debe estar entre 6 MW y el límite de T1.")
    if p_bess_mw < 0 or e_bess_mwh < 0:
        raise ValueError("P_BESS y E_BESS deben ser >= 0.")
    if e_bess_mwh == 0 and p_bess_mw > 1e-12:
        raise ValueError("No puede haber potencia BESS con E_BESS = 0.")
    if e_bess_mwh > 1e-12 and p_bess_mw <= 1e-12:
        raise ValueError("No tiene sentido instalar energía BESS con P_BESS = 0.")
    if e_bess_mwh > 0 and p_bess_mw > P_RATE_MAX * e_bess_mwh + 1e-9:
        raise ValueError("P_BESS supera 0,5C para la capacidad BESS propuesta.")
    if n_containers is None:
        n_containers = 0 if e_bess_mwh <= 1e-12 else int(round(e_bess_mwh / e_container_mwh))
    if not math.isclose(e_bess_mwh, n_containers * e_container_mwh, rel_tol=0, abs_tol=1e-6):
        raise ValueError("E_BESS debe coincidir con n_containers * energía/container.")
    bess_diseno = calcular_metricas_bess_diseno(p_bess_mw, int(n_containers), e_container_mwh, soc_min, soc_max)
    espacio = calcular_screening_espacial(
        p_fv_mw=p_fv_mw, n_aeros=n_aeros, n_containers=int(n_containers),
        potencia_modulo_w=potencia_modulo_fv_w, pitch_fv_m=pitch_fv_m
    )
    if not espacio["cumple_screening_espacial"]:
        raise ValueError("La configuración no cumple el screening espacial.")

    if despacho_multianual:
        detalle_20, costo_total_20, _, _, _ = simular_20_anios_consciente_degradacion(
            perfiles,
            p_fv_mw=p_fv_mw, n_aeros=n_aeros,
            p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw, tipo_aero=tipo_aero,
            eta_carga=eta_carga, eta_descarga=eta_descarga,
            soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw, exportar_excedente=exportar_excedente,
            wacc=wacc,
        )
    else:
        detalle_20, costo_total_20 = simular_20_anios(
            perfiles,
            p_fv_mw=p_fv_mw,
            n_aeros=n_aeros,
            p_bess_mw=p_bess_mw,
            e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw,
            tipo_aero=tipo_aero,
            eta_carga=eta_carga,
            eta_descarga=eta_descarga,
            soc_min=soc_min,
            soc_max=soc_max,
            soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw,
            exportar_excedente=exportar_excedente,
            wacc=wacc,
            despacho_economico=despacho_economico,
        )

    factible = bool(detalle_20["Cumple demanda"].all())
    horas_no_cumple = int(detalle_20["Horas no cumple"].sum())
    energia_no_abast = float(detalle_20["Demanda no abastecida [MWh]"].sum())
    costo_objetivo = float(costo_total_20) if factible else math.inf

    capex = calcular_capex(p_fv_mw, n_aeros, p_bess_mw, e_bess_mwh, tipo_aero)
    p_eol_mw = n_aeros * P_NOMINAL_AERO_MW[tipo_aero]

    resumen = {
        "P_FV [MW]": float(p_fv_mw),
        "N aeros": int(n_aeros),
        "P_EOL instalada [MW]": float(p_eol_mw),
        "P_BESS [MW]": float(p_bess_mw),
        "N containers BESS": int(n_containers),
        "E_BESS [MWh]": float(e_bess_mwh),
        "Duración BESS nominal [h]": bess_diseno["horas_nominales"],
        "Duración BESS útil BOL [h]": bess_diseno["horas_utiles_bol"],
        "CAPEX BESS energía [USD]": bess_diseno["capex_bess_energia_usd"],
        "CAPEX BESS potencia [USD]": bess_diseno["capex_bess_potencia_usd"],
        "CAPEX BESS total [USD]": bess_diseno["capex_bess_total_usd"],
        "P contratada [MW]": float(p_contratada_mw),
        "Factible": factible,
        "Horas no cumple 20a": horas_no_cumple,
        "Energía no abastecida 20a [MWh]": energia_no_abast,
        "CAPEX [USD]": float(capex.total_usd),
        "VP operación 20a [USD]": float(detalle_20["VP flujo anual [USD]"].sum()),
        "Costo total 20a [USD]": float(costo_objetivo),
        "Ciclos acumulados año 20": float(detalle_20.iloc[-1]["Ciclos equivalentes acumulados"]),
        "SOH final año 20": float(detalle_20.iloc[-1]["SOH final"]),
        "EOL alcanzado": bool(detalle_20["EOL alcanzado"].any()),
        "Modo despacho": (
            "económico con reserva multianual" if despacho_multianual
            else ("económico LP anual" if despacho_economico else "técnico heurístico")
        ),
    }
    if espacio is not None:
        resumen.update({
            "Potencia módulo FV [W]": float(potencia_modulo_fv_w),
            "Pitch FV [m]": float(espacio["pitch_fv_m"]),
            "GCR FV": float(espacio["gcr_fv"]),
            "N módulos FV": int(espacio["n_modulos_fv"]),
            "Área módulos FV [m2]": float(espacio["area_modulos_fv_m2"]),
            "Área FV terreno [m2]": float(espacio["area_fv_terreno_m2"]),
            "Área BESS screening [m2]": float(espacio["area_bess_m2"]),
            "Área FV+BESS screening [m2]": float(espacio["area_fv_mas_bess_m2"]),
            "Área eólica reservada screening [m2]": float(espacio["area_eolica_reservada_m2"]),
            "Área residual tras eólica [m2]": float(espacio["area_residual_tras_eolica_m2"]),
            "Área total screening [m2]": float(espacio["area_total_screening_m2"]),
            "Uso terreno FV+BESS [%]": float(espacio["uso_area_fv_bess_pct"]),
            "Uso terreno eólico [%]": float(espacio["uso_area_eolica_pct"]),
            "Uso terreno total screening [%]": float(espacio["uso_area_total_screening_pct"]),
            "Cumple screening espacial": bool(espacio["cumple_screening_espacial"]),
        })
    return resumen, detalle_20


def _parsear_lista_numerica(texto: str, *, enteros: bool = False) -> list[float] | list[int]:
    """Convierte '0,1,2.5' en una lista numérica, sin duplicados."""
    if texto is None or not str(texto).strip():
        raise ValueError("La lista de candidatos no puede estar vacía.")
    partes = [x.strip() for x in str(texto).split(",") if x.strip()]
    if enteros:
        vals = [int(float(x)) for x in partes]
        if any(abs(float(x) - int(float(x))) > 1e-9 for x in partes):
            raise ValueError(f"Se esperaban enteros en: {texto}")
    else:
        vals = [float(x) for x in partes]
    # preserva orden, elimina duplicados
    return list(dict.fromkeys(vals))


def optimizar_grilla(
    perfiles: pd.DataFrame,
    *,
    valores_fv: list[float],
    valores_aeros: list[int],
    valores_pbess: list[float],
    valores_containers: list[int],
    p_contratada_mw: float = P_CONTRATADA_FIJA_MW,
    e_container_mwh: float = E_CONTAINER_MWH_DEFAULT,
    potencia_modulo_fv_w: float = POTENCIA_MODULO_FV_W_DEFAULT,
    pitch_fv_m: float = PITCH_FV_DEFAULT_M,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    exportar_excedente: bool = True,
    wacc: float = WACC,
    despacho_economico: bool = False,
) -> tuple[pd.DataFrame, dict | None]:
    """
    Recorre una grilla explícita de las cuatro variables de diseño:
      1) P_FV
      2) cantidad de aerogeneradores (P_EOL queda determinada)
      3) P_BESS
      4) cantidad de containers (E_BESS = containers * 5,015 MWh)
  
    Las configuraciones físicamente imposibles (por ejemplo P_BESS > 0,5C)
    se descartan antes de simular.

    IMPORTANTE: esta optimización usa el despacho operativo ACTUAL. Todavía no
    optimiza hora a hora la descarga económica del BESS.
    """
    combinaciones = list(product(
        valores_fv,
        valores_aeros,
        valores_pbess,
        valores_containers,
    ))
    total = len(combinaciones)
    if total == 0:
        raise ValueError("El espacio de búsqueda está vacío.")
    if pitch_fv_m <= ANCHO_ROTANTE_TRACKER_1P_M:
        raise ValueError(
            f"--pitch-fv-m debe ser mayor que {ANCHO_ROTANTE_TRACKER_1P_M:.3f} m."
        )
    if potencia_modulo_fv_w <= 0:
        raise ValueError("--pot-modulo-fv-w debe ser > 0.")
    gcr_fv = ANCHO_ROTANTE_TRACKER_1P_M / pitch_fv_m

    print("\n" + "=" * 80)
    print("OPTIMIZACIÓN POR GRILLA")
    print("=" * 80)
    print(f"Combinaciones brutas: {total:,}")
    print(f"P contratada fija: {p_contratada_mw:.1f} MW")
    print(f"Restricción eólica: n_aeros <= {N_AEROS_MAX_ESPACIO} | D={ROTOR_DIAMETRO_M:.0f} m | separación mínima={DISTANCIA_MIN_AEROS_M:.0f} m ({DISTANCIA_MIN_AEROS_D:.1f}D)")
    print(f"Área del polígono: {AREA_DISPONIBLE_M2/10_000:.2f} ha")
    print(f"FV screening: módulo={potencia_modulo_fv_w:g} W | pitch={pitch_fv_m:.2f} m | GCR={gcr_fv:.3f}")
    print(f"BESS screening: {BESS_CONTAINER_LARGO_M:.3f} x {BESS_CONTAINER_ANCHO_M:.3f} m | separación={BESS_SEPARACION_SCREENING_M:g} m")

    resultados: list[dict] = []
    mejor: dict | None = None
    t0 = time.time()
    evaluadas = 0
    descartadas_fisicas = 0

    for idx, (p_fv, n_aeros, p_bess, n_cont) in enumerate(combinaciones, start=1):
        p_cont = float(p_contratada_mw)
        e_bess = float(n_cont) * float(e_container_mwh)

        # Filtros físicos baratos, antes de las 20 simulaciones anuales.
        if p_fv < 0 or n_aeros < 0 or n_cont < 0:
            descartadas_fisicas += 1
            continue
        if n_aeros > N_AEROS_MAX_ESPACIO:
            descartadas_fisicas += 1
            continue
        if abs(p_cont - P_CONTRATADA_FIJA_MW) > 1e-9:
            raise ValueError("La optimización debe usar P contratada fija en 15 MW.")
        if p_cont > limite_t1_mw + 1e-9:
            raise ValueError("P contratada fija supera el límite de T1.")
        if e_bess <= 1e-12 and p_bess > 1e-12:
            descartadas_fisicas += 1
            continue
        if e_bess > 1e-12 and p_bess <= 1e-12:
            descartadas_fisicas += 1
            continue
        if e_bess > 0 and p_bess > P_RATE_MAX * e_bess + 1e-9:
            descartadas_fisicas += 1
            continue
        espacio = calcular_screening_espacial(
            p_fv_mw=float(p_fv), n_aeros=int(n_aeros), n_containers=int(n_cont),
            potencia_modulo_w=float(potencia_modulo_fv_w), pitch_fv_m=float(pitch_fv_m))
        if not espacio["cumple_screening_espacial"]:
            descartadas_fisicas += 1
            continue

        try:
            resumen, _ = evaluar_configuracion(
                perfiles,
                p_fv_mw=float(p_fv),
                n_aeros=int(n_aeros),
                p_bess_mw=float(p_bess),
                e_bess_mwh=e_bess,
                p_contratada_mw=float(p_cont),
                n_containers=int(n_cont),
                e_container_mwh=float(e_container_mwh),
                potencia_modulo_fv_w=float(potencia_modulo_fv_w),
                pitch_fv_m=float(pitch_fv_m),
                tipo_aero=tipo_aero,
                eta_carga=eta_carga,
                eta_descarga=eta_descarga,
                soc_min=soc_min,
                soc_max=soc_max,
                soc_inicial_frac=soc_inicial_frac,
                limite_t1_mw=limite_t1_mw,
                exportar_excedente=exportar_excedente,
                wacc=wacc,
                despacho_economico=despacho_economico,
            )
        except ValueError:
            descartadas_fisicas += 1
            continue

        evaluadas += 1
        resultados.append(resumen)

        if resumen["Factible"]:
            if mejor is None or resumen["Costo total 20a [USD]"] < mejor["Costo total 20a [USD]"]:
                mejor = resumen.copy()
                print(
                    f"  Nuevo mejor -> Costo=${mejor['Costo total 20a [USD]']:,.0f} | "
                    f"FV={mejor['P_FV [MW]']:g} MW | aeros={mejor['N aeros']} | "
                    f"PBESS={mejor['P_BESS [MW]']:g} MW | EBESS={mejor['E_BESS [MWh]']:g} MWh | "
                    f"t={mejor['Duración BESS nominal [h]']:.2f} h | "
                    f"FV+BESS={mejor['Uso terreno FV+BESS [%]']:.1f}% terreno | "
                    f"Pcont={mejor['P contratada [MW]']:g} MW"
                )

        if idx % max(1, total // 20) == 0 or idx == total:
            elapsed = time.time() - t0
            print(
                f"Progreso {idx:,}/{total:,} ({100*idx/total:5.1f} %) | "
                f"simuladas={evaluadas:,} | descartadas={descartadas_fisicas:,} | "
                f"{elapsed:,.1f} s"
            )

    df = pd.DataFrame(resultados)
    if not df.empty:
        # Factibles primero y luego costo creciente. Los inf quedan al final.
        df = df.sort_values(
            by=["Factible", "Costo total 20a [USD]"],
            ascending=[False, True],
            ignore_index=True,
        )

    return df, mejor

# =============================================================================
# SALIDA
# =============================================================================

def imprimir_resumen_anio(resumen: dict) -> None:
    print("\n" + "=" * 80)
    print(f"RESUMEN AÑO {resumen['anio']}")
    print("=" * 80)
    claves = [
        "factor_fv",
        "soh_inicial",
        "soh_final",
        "capacidad_bess_inicio_mwh",
        "capacidad_bess_final_mwh",
        "energia_demanda_mwh",
        "energia_fv_mwh",
        "energia_eolica_mwh",
        "energia_red_total_mwh",
        "energia_red_valle_mwh",
        "energia_red_resto_mwh",
        "energia_red_pico_mwh",
        "carga_renovable_mwh",
        "carga_red_valle_mwh",
        "descarga_obligatoria_mwh",
        "descarga_economica_mwh",
        "energia_exportada_mwh",
        "curtailment_mwh",
        "demanda_no_abastecida_mwh",
        "horas_no_cumple",
        "max_deficit_no_abastecido_mw",
        "ciclos_equivalentes",
        "ciclos_acumulados_final",
        "costo_valle_usd",
        "costo_resto_usd",
        "costo_pico_usd",
        "costo_red_total_usd",
        "max_abs_flujo_t1_mw",
        "max_error_balance_mw",
    ]
    for k in claves:
        v = resumen[k]
        if isinstance(v, (float, np.floating)):
            print(f"{k:42s}: {float(v):,.9f}")
        else:
            print(f"{k:42s}: {v}")


# =============================================================================
# MAIN
# =============================================================================

def main_v11_legacy() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--excel",
        type=Path,
        default=None,
        help="Ruta al Excel actual (.xlsm o .xlsx).",
    )
    parser.add_argument(
        "--tipo-aero",
        choices=["GE3.4", "GE3.8"],
        default="GE3.4",
        help="Tecnología eólica a simular.",
    )
    parser.add_argument(
        "--simular-20",
        action="store_true",
        help="Además del año 1, simula los 20 años y calcula el costo total.",
    )
    parser.add_argument(
        "--despacho-economico",
        action="store_true",
        help="Optimiza cada año por separado. Puede ser miope respecto de la degradación futura.",
    )
    parser.add_argument(
        "--despacho-multianual",
        action="store_true",
        help=(
            "V11 recomendada: despacho económico con reserva multianual de degradación. "
            "Calcula SOH técnico mínimo futuro y limita ciclos para asegurar los 20 años."
        ),
    )
    parser.add_argument(
        "--sin-exportar",
        action="store_true",
        help="Recorta todo excedente en vez de exportarlo hasta T1.",
    )
    parser.add_argument(
        "--optimizar",
        action="store_true",
        help="Ejecuta búsqueda por grilla de las cuatro variables de diseño.",
    )
    parser.add_argument("--fv-valores", type=str, default=None, help="Ej.: 0,10,15,17,20")
    parser.add_argument("--aeros-valores", type=str, default=None, help="Ej.: 0,1,2,3")
    parser.add_argument("--pbess-valores", type=str, default=None, help="Ej.: 0,2.5,5,7.5")
    parser.add_argument("--containers-valores", type=str, default=None, help="Ej.: 0,1,2,3,4")
    parser.add_argument("--pot-modulo-fv-w", type=float, default=POTENCIA_MODULO_FV_W_DEFAULT,
                        help="Potencia STC del módulo para área. Default 700 W (conservador dentro de 700-725 W).")
    parser.add_argument(
        "--pitch-fv-m", type=float, default=PITCH_FV_DEFAULT_M,
        help=(
            "Pitch entre filas FV [m]. Default 6.5 m, criterio geométrico de no sombreado "
            "9-15 h solares en solsticio de invierno. El GCR se calcula automáticamente."
        ),
    )
    args = parser.parse_args()
    if args.despacho_multianual:
        # El modo multianual necesariamente evalúa los 20 años.
        args.simular_20 = True
    if args.optimizar and args.despacho_multianual:
        raise ValueError(
            "V11 usa el despacho multianual para validar configuraciones. "
            "No lo combines todavía con --optimizar: el optimizador continuo/mixto será la etapa siguiente."
        )

    ruta = args.excel.resolve() if args.excel is not None else buscar_excel_por_defecto()
    if not ruta.exists():
        raise FileNotFoundError(f"No encontré el Excel: {ruta}")

    print(f"Excel utilizado: {ruta}")
    cfg = leer_configuracion_excel(ruta)
    perfiles = cargar_perfiles(ruta, cfg.p_fv_mw)

    print("\nConfiguración leída:")
    for k, v in asdict(cfg).items():
        print(f"  {k:24s} = {v}")

    try:
        bess_base = calcular_metricas_bess_diseno(cfg.p_bess_mw, cfg.n_containers,
                                                  cfg.e_container_mwh, cfg.soc_min, cfg.soc_max)
        print("\nBESS actual (diseño):")
        print(f"  P instalada                 = {bess_base['p_bess_mw']:.6f} MW")
        print(f"  E instalada                 = {bess_base['e_bess_mwh']:.6f} MWh")
        print(f"  Duración nominal E/P        = {bess_base['horas_nominales']:.3f} h")
        print(f"  Duración útil BOL por SOC   = {bess_base['horas_utiles_bol']:.3f} h")
        print(f"  CAPEX energía BESS          = ${bess_base['capex_bess_energia_usd']:,.0f}")
        print(f"  CAPEX potencia BESS         = ${bess_base['capex_bess_potencia_usd']:,.0f}")
    except ValueError as exc:
        print(f"\nAVISO BESS actual: {exc}")

    if abs(cfg.p_contratada_mw - P_CONTRATADA_FIJA_MW) > 1e-9:
        print(f"\nAVISO: el Excel tiene P contratada={cfg.p_contratada_mw} MW, pero la optimización usará {P_CONTRATADA_FIJA_MW} MW por criterio docente.")

    # -------------------------------------------------------------------------
    # ETAPAS 1 y 2: año 1 + horizonte de 20 años
    # -------------------------------------------------------------------------
    carpeta_salida = ruta.parent
    detalle_20_precalculado = None
    costo_total_20_precalculado = None
    plan_degradacion_v11 = None

    if args.despacho_multianual:
        print("\nPreparando V11: reserva técnica de degradación para los 20 años...")
        (
            detalle_20_precalculado,
            costo_total_20_precalculado,
            resultado_1,
            resumen_1,
            plan_degradacion_v11,
        ) = simular_20_anios_consciente_degradacion(
            perfiles,
            p_fv_mw=cfg.p_fv_mw,
            n_aeros=cfg.n_aeros,
            p_bess_mw=cfg.p_bess_mw,
            e_bess_mwh=cfg.e_bess_mwh,
            p_contratada_mw=cfg.p_contratada_mw,
            tipo_aero=args.tipo_aero,
            eta_carga=cfg.eta_carga,
            eta_descarga=cfg.eta_descarga,
            soc_min=cfg.soc_min,
            soc_max=cfg.soc_max,
            soc_inicial_frac=cfg.soc_inicial_frac,
            limite_t1_mw=cfg.limite_t1_mw,
            exportar_excedente=not args.sin_exportar,
        )
        resumen_1["soh_minimo_tecnico"] = float(plan_degradacion_v11.iloc[0]["SOH mínimo técnico"])
        resumen_1["ciclos_maximos_permitidos_anio"] = float(
            detalle_20_precalculado.iloc[0]["Ciclos máximos permitidos año"]
        )
        resumen_1["despacho"] = "económico LP + reserva multianual de degradación"
    else:
        simulador_anio_1 = simular_anio_economico if args.despacho_economico else simular_anio
        resultado_1, resumen_1 = simulador_anio_1(
            perfiles,
            p_fv_mw=cfg.p_fv_mw,
            n_aeros=cfg.n_aeros,
            p_bess_mw=cfg.p_bess_mw,
            e_bess_mwh=cfg.e_bess_mwh,
            p_contratada_mw=cfg.p_contratada_mw,
            anio=1,
            soh_inicial=1.0,
            ciclos_acum_inicial=0.0,
            eta_carga=cfg.eta_carga,
            eta_descarga=cfg.eta_descarga,
            soc_min=cfg.soc_min,
            soc_max=cfg.soc_max,
            soc_inicial_frac=cfg.soc_inicial_frac,
            limite_t1_mw=cfg.limite_t1_mw,
            tipo_aero=args.tipo_aero,
            exportar_excedente=not args.sin_exportar,
        )

    imprimir_resumen_anio(resumen_1)
    if args.despacho_multianual:
        print(f"{'SOH mínimo técnico año 1':42s}: {resumen_1['soh_minimo_tecnico']:.6f}")
        print(f"{'Ciclos máximos permitidos año 1':42s}: {resumen_1['ciclos_maximos_permitidos_anio']:.6f}")
        print(f"{'Modo despacho':42s}: {resumen_1['despacho']}")

    salida_anio1 = carpeta_salida / "resultado_anio1_python.csv"
    resultado_1.to_csv(salida_anio1, index=False, decimal=".")
    print(f"\nDetalle horario año 1 guardado en:\n  {salida_anio1}")

    if plan_degradacion_v11 is not None:
        salida_plan = carpeta_salida / "plan_degradacion_multianual_v11.csv"
        plan_degradacion_v11.to_csv(salida_plan, index=False, decimal=".")
        print(f"Plan de degradación V11 guardado en:\n  {salida_plan}")

    # -------------------------------------------------------------------------
    # ETAPA 2: 20 años
    # -------------------------------------------------------------------------
    if args.simular_20:
        if args.despacho_multianual:
            detalle_20 = detalle_20_precalculado
            costo_total_20 = costo_total_20_precalculado
        else:
            detalle_20, costo_total_20 = simular_20_anios(
                perfiles,
                p_fv_mw=cfg.p_fv_mw,
                n_aeros=cfg.n_aeros,
                p_bess_mw=cfg.p_bess_mw,
                e_bess_mwh=cfg.e_bess_mwh,
                p_contratada_mw=cfg.p_contratada_mw,
                tipo_aero=args.tipo_aero,
                eta_carga=cfg.eta_carga,
                eta_descarga=cfg.eta_descarga,
                soc_min=cfg.soc_min,
                soc_max=cfg.soc_max,
                soc_inicial_frac=cfg.soc_inicial_frac,
                limite_t1_mw=cfg.limite_t1_mw,
                exportar_excedente=not args.sin_exportar,
                despacho_economico=args.despacho_economico,
            )

        salida_20 = carpeta_salida / "resumen_20_anios_python.csv"
        detalle_20.to_csv(salida_20, index=False, decimal=".")

        capex = calcular_capex(
            cfg.p_fv_mw,
            cfg.n_aeros,
            cfg.p_bess_mw,
            cfg.e_bess_mwh,
            args.tipo_aero,
        )

        print("\n" + "=" * 80)
        print("RESUMEN ECONÓMICO 20 AÑOS")
        print("=" * 80)
        if args.despacho_multianual:
            print("Modo                               : económico + reserva multianual de degradación")
        elif args.despacho_economico:
            print("Modo                               : económico LP anual (miope)")
        else:
            print("Modo                               : técnico heurístico")
        print(f"CAPEX total [USD]                 : {capex.total_usd:,.2f}")
        print(f"VP costos años 1-20 [USD]         : {detalle_20['VP flujo anual [USD]'].sum():,.2f}")
        print(f"COSTO TOTAL 20 AÑOS [USD]         : {costo_total_20:,.2f}")
        print(f"Ciclos equivalentes acumulados    : {detalle_20.iloc[-1]['Ciclos equivalentes acumulados']:,.6f}")
        print(f"SOH final año 20                  : {detalle_20.iloc[-1]['SOH final']:.6f}")
        print(f"Horas totales sin abastecer       : {int(detalle_20['Horas no cumple'].sum())}")
        print(f"Todos los años cumplen demanda    : {bool(detalle_20['Cumple demanda'].all())}")
        if args.despacho_multianual:
            print(f"SOH técnico mínimo año 20         : {detalle_20.iloc[-1]['SOH mínimo técnico']:.6f}")
        print(f"\nResumen anual guardado en:\n  {salida_20}")

    # -------------------------------------------------------------------------
    # ETAPA 3: optimización de cuatro variables por grilla; P contratada fija
    # -------------------------------------------------------------------------
    if args.optimizar:
        faltantes = []
        if args.fv_valores is None:
            faltantes.append("--fv-valores")
        if args.aeros_valores is None:
            faltantes.append("--aeros-valores")
        if args.pbess_valores is None:
            faltantes.append("--pbess-valores")
        if args.containers_valores is None:
            faltantes.append("--containers-valores")
        if faltantes:
            raise ValueError(
                "Para --optimizar tenés que indicar la grilla de las cuatro variables. "
                "Faltan: " + ", ".join(faltantes)
            )

        valores_fv = _parsear_lista_numerica(args.fv_valores)
        valores_aeros = _parsear_lista_numerica(args.aeros_valores, enteros=True)
        valores_pbess = _parsear_lista_numerica(args.pbess_valores)
        valores_containers = _parsear_lista_numerica(args.containers_valores, enteros=True)

        tabla_opt, mejor = optimizar_grilla(
            perfiles,
            valores_fv=valores_fv,
            valores_aeros=valores_aeros,
            valores_pbess=valores_pbess,
            valores_containers=valores_containers,
            p_contratada_mw=P_CONTRATADA_FIJA_MW,
            e_container_mwh=cfg.e_container_mwh,
            potencia_modulo_fv_w=args.pot_modulo_fv_w,
            pitch_fv_m=args.pitch_fv_m,
            tipo_aero=args.tipo_aero,
            eta_carga=cfg.eta_carga,
            eta_descarga=cfg.eta_descarga,
            soc_min=cfg.soc_min,
            soc_max=cfg.soc_max,
            soc_inicial_frac=cfg.soc_inicial_frac,
            limite_t1_mw=cfg.limite_t1_mw,
            exportar_excedente=not args.sin_exportar,
            despacho_economico=args.despacho_economico,
        )

        salida_opt = carpeta_salida / "resultados_optimizacion_grilla_v11.csv"
        tabla_opt.to_csv(salida_opt, index=False, decimal=".")
        print(f"\nResultados de la grilla guardados en:\n  {salida_opt}")

        if mejor is None:
            print("\nNo apareció ninguna configuración factible en la grilla indicada.")
        else:
            print("\n" + "=" * 80)
            print("MEJOR CONFIGURACIÓN DE LA GRILLA")
            print("=" * 80)
            for k, v in mejor.items():
                if isinstance(v, float):
                    print(f"{k:38s}: {v:,.6f}")
                else:
                    print(f"{k:38s}: {v}")


# =============================================================================
# V12 - OPTIMIZACIÓN CONTINUA/MIXTA
# =============================================================================

def _screening_potencia_rapido(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    limite_t1_mw: float,
    tipo_aero: Literal["GE3.4", "GE3.8"],
) -> bool:
    """Condición necesaria barata usando el año 20 (FV más degradado)."""
    factor_fv = factor_degradacion_fv(20)
    fv = np.minimum(p_fv_mw * perfiles["fv_pu_sin_limite"].to_numpy(float), limite_t1_mw) * factor_fv
    if tipo_aero == "GE3.4":
        eol = n_aeros * perfiles["eolico_34_por_aero_mw"].to_numpy(float)
    else:
        eol = n_aeros * perfiles["eolico_38_por_aero_mw"].to_numpy(float)
    deficit = np.maximum(perfiles["demanda_mw"].to_numpy(float) - fv - eol, 0.0)
    requerida = np.maximum(deficit - min(P_CONTRATADA_FIJA_MW, limite_t1_mw), 0.0)
    return bool(np.max(requerida) <= p_bess_mw + 1e-9)


def evaluar_configuracion_v12(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    n_containers: int,
    cfg_base: Configuracion,
    potencia_modulo_fv_w: float,
    pitch_fv_m: float,
    tipo_aero: Literal["GE3.4", "GE3.8"],
    exportar_excedente: bool,
    devolver_detalle_anio1: bool = False,
) -> tuple[dict, pd.DataFrame, pd.DataFrame | None, pd.DataFrame]:
    """Evaluación exacta V12 de un diseño candidato."""
    p_fv_mw = float(p_fv_mw)
    p_bess_mw = float(p_bess_mw)
    n_aeros = int(n_aeros)
    n_containers = int(n_containers)
    e_bess_mwh = n_containers * cfg_base.e_container_mwh

    if p_fv_mw < 0 or p_bess_mw < 0 or n_aeros < 0 or n_containers < 0:
        raise ValueError("Variables de diseño negativas.")
    if n_aeros > N_AEROS_MAX_ESPACIO:
        raise ValueError("Cantidad de aerogeneradores supera el máximo espacial de screening.")

    # Caso sin BESS: P_BESS se fuerza a cero; no se inventa energía/capacidad.
    if n_containers == 0:
        p_bess_mw = 0.0
        e_bess_mwh = 0.0
    else:
        if p_bess_mw <= 1e-6:
            raise ValueError("Hay containers BESS pero P_BESS es prácticamente cero.")
        if p_bess_mw > P_RATE_MAX * e_bess_mwh + 1e-9:
            raise ValueError("P_BESS supera el límite 0,5C.")

    espacio = calcular_screening_espacial(
        p_fv_mw=p_fv_mw,
        n_aeros=n_aeros,
        n_containers=n_containers,
        potencia_modulo_w=potencia_modulo_fv_w,
        pitch_fv_m=pitch_fv_m,
    )
    if not espacio["cumple_screening_espacial"]:
        raise ValueError("No cumple screening espacial conjunto eólico + FV + BESS.")

    # Screening de potencia necesario antes de resolver 20 LP horarios.
    if not _screening_potencia_rapido(
        perfiles,
        p_fv_mw=p_fv_mw,
        n_aeros=n_aeros,
        p_bess_mw=p_bess_mw,
        limite_t1_mw=cfg_base.limite_t1_mw,
        tipo_aero=tipo_aero,
    ):
        raise ValueError("No alcanza la potencia instantánea para abastecer el año 20.")

    detalle_20, costo_total, detalle_h1, resumen_h1, plan = simular_20_anios_consciente_degradacion(
        perfiles,
        p_fv_mw=p_fv_mw,
        n_aeros=n_aeros,
        p_bess_mw=p_bess_mw,
        e_bess_mwh=e_bess_mwh,
        p_contratada_mw=P_CONTRATADA_FIJA_MW,
        tipo_aero=tipo_aero,
        eta_carga=cfg_base.eta_carga,
        eta_descarga=cfg_base.eta_descarga,
        soc_min=cfg_base.soc_min,
        soc_max=cfg_base.soc_max,
        soc_inicial_frac=cfg_base.soc_inicial_frac,
        limite_t1_mw=cfg_base.limite_t1_mw,
        exportar_excedente=exportar_excedente,
        wacc=WACC,
        devolver_detalle_anio1=devolver_detalle_anio1,
    )

    if not bool(detalle_20["Cumple demanda"].all()):
        raise ValueError("La configuración no abastece toda la demanda en 20 años.")

    bess = calcular_metricas_bess_diseno(
        p_bess_mw, n_containers, cfg_base.e_container_mwh, cfg_base.soc_min, cfg_base.soc_max
    ) if n_containers > 0 else calcular_metricas_bess_diseno(
        0.0, 0, cfg_base.e_container_mwh, cfg_base.soc_min, cfg_base.soc_max
    )
    capex = calcular_capex(p_fv_mw, n_aeros, p_bess_mw, e_bess_mwh, tipo_aero)

    resumen = {
        "P_FV [MW]": p_fv_mw,
        "N aeros": n_aeros,
        "P_EOL instalada [MW]": n_aeros * P_NOMINAL_AERO_MW[tipo_aero],
        "P_BESS [MW]": p_bess_mw,
        "N containers BESS": n_containers,
        "E_BESS [MWh]": e_bess_mwh,
        "Duración BESS nominal [h]": bess["horas_nominales"],
        "Duración BESS útil BOL [h]": bess["horas_utiles_bol"],
        "CAPEX FV [USD]": capex.fv_usd,
        "CAPEX eólico [USD]": capex.eolico_usd,
        "CAPEX BESS energía [USD]": bess["capex_bess_energia_usd"],
        "CAPEX BESS potencia [USD]": bess["capex_bess_potencia_usd"],
        "CAPEX BESS total [USD]": bess["capex_bess_total_usd"],
        "CAPEX total [USD]": capex.total_usd,
        "VP operación 20a [USD]": float(detalle_20["VP flujo anual [USD]"].sum()),
        "Costo total 20a [USD]": float(costo_total),
        "Horas no cumple 20a": int(detalle_20["Horas no cumple"].sum()),
        "Energía no abastecida 20a [MWh]": float(detalle_20["Demanda no abastecida [MWh]"].sum()),
        "Ciclos acumulados año 20": float(detalle_20.iloc[-1]["Ciclos equivalentes acumulados"]),
        "SOH final año 20": float(detalle_20.iloc[-1]["SOH final"]),
        "EOL alcanzado": bool(detalle_20["EOL alcanzado"].any()),
        "Exportación 20a [MWh]": float(detalle_20["Exportación [MWh]"].sum()),
        "Potencia módulo FV [W]": potencia_modulo_fv_w,
        "Pitch FV [m]": espacio["pitch_fv_m"],
        "GCR FV": espacio["gcr_fv"],
        "N módulos FV": espacio["n_modulos_fv"],
        "Área FV terreno [m2]": espacio["area_fv_terreno_m2"],
        "Área BESS screening [m2]": espacio["area_bess_m2"],
        "Área eólica reservada screening [m2]": espacio["area_eolica_reservada_m2"],
        "Área residual tras eólica [m2]": espacio["area_residual_tras_eolica_m2"],
        "Área total screening [m2]": espacio["area_total_screening_m2"],
        "Uso terreno total screening [%]": espacio["uso_area_total_screening_pct"],
        "Factible": True,
    }
    return resumen, detalle_20, detalle_h1, plan




def _credito_arbitraje_surrogate_v12(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    soh: float,
    anio: int,
    cfg_base: Configuracion,
    tipo_aero: Literal["GE3.4", "GE3.8"],
) -> tuple[float,float]:
    """
    Potencial económico diario de desplazar energía hacia Pico y luego Resto.
    Es sólo un crédito de ranking para la exploración: el despacho final se resuelve
    con LP en procesos exactos independientes.
    """
    if e_bess_mwh<=1e-12 or p_bess_mw<=1e-12:
        return 0.0,0.0
    demanda=perfiles["demanda_mw"].to_numpy(float)
    banda=perfiles["banda"].to_numpy(object)
    fv=np.minimum(p_fv_mw*perfiles["fv_pu_sin_limite"].to_numpy(float),cfg_base.limite_t1_mw)*factor_degradacion_fv(anio)
    if tipo_aero=="GE3.4":
        eol=n_aeros*perfiles["eolico_34_por_aero_mw"].to_numpy(float)
    else:
        eol=n_aeros*perfiles["eolico_38_por_aero_mw"].to_numpy(float)
    net=demanda-fv-eol
    deficit=np.maximum(net,0.0); excedente=np.maximum(-net,0.0)
    req_obl=np.maximum(deficit-P_CONTRATADA_FIJA_MW,0.0)
    p_econ_disp=np.maximum(p_bess_mw-req_obl,0.0)
    necesidad_econ=np.minimum(np.minimum(deficit,P_CONTRATADA_FIJA_MW),p_econ_disp)
    headroom=np.maximum(P_CONTRATADA_FIJA_MW-deficit,0.0)
    carga_red_cap=np.minimum(headroom,p_bess_mw)
    carga_ren_cap=np.minimum(excedente,p_bess_mw)
    usable_terminal=e_bess_mwh*soh*(cfg_base.soc_max-cfg_base.soc_min)*cfg_base.eta_descarga
    esc=(1.0+ESCALAMIENTO_COSTOS)**(anio-1)
    tval,tres,tpico=32.0*esc,65.0*esc,125.0*esc
    ahorro=0.0; salida=0.0
    for dia in range(366):
        sl=slice(dia*24,(dia+1)*24)
        b=banda[sl]
        ren_term=float(carga_ren_cap[sl].sum())*cfg_base.eta_carga*cfg_base.eta_descarga
        val_term=float(carga_red_cap[sl][b=="Valle"].sum())*cfg_base.eta_carga*cfg_base.eta_descarga
        energia=min(usable_terminal,ren_term+val_term)
        need_pico=float(necesidad_econ[sl][b=="Pico"].sum())
        need_resto=float(necesidad_econ[sl][b=="Resto"].sum())
        q_pico=min(energia,need_pico)
        q_resto=min(max(0.0,energia-q_pico),need_resto)
        q=q_pico+q_resto
        libre=min(q,ren_term)
        pagada=max(0.0,q-libre)
        evitado=q_pico*tpico+q_resto*tres
        costo_carga=pagada/(cfg_base.eta_carga*cfg_base.eta_descarga)*tval
        ahorro+=max(0.0,evitado-costo_carga)
        salida+=q
    ciclos=(salida/cfg_base.eta_descarga)/(DOD_CICLO_REFERENCIA*e_bess_mwh)
    return float(ahorro),float(ciclos)


def evaluar_surrogado_v12(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    n_containers: int,
    cfg_base: Configuracion,
    potencia_modulo_fv_w: float,
    pitch_fv_m: float,
    tipo_aero: Literal["GE3.4", "GE3.8"],
    exportar_excedente: bool,
) -> tuple[float, dict]:
    """
    Surrogate V12 SIN LP, para que Differential Evolution sea rápido y para no dejar
    estado de HiGHS antes de la validación exacta.

    Base: simulación técnica de los 20 años + un crédito conservador (35 %) del
    potencial de arbitraje Valle -> Pico/Resto. El 35 % evita adjudicar a la batería
    todo el arbitraje teórico, ya que el modelo exacto debe reservar ciclos/SOH futuro.

    El surrogate sólo ORDENA candidatos. El costo que se reporta como resultado final
    siempre proviene del modelo exacto multianual V12.
    """
    p_fv_mw=float(p_fv_mw); p_bess_mw=float(p_bess_mw)
    n_aeros=int(n_aeros); n_containers=int(n_containers)
    e_bess_mwh=n_containers*cfg_base.e_container_mwh
    if n_containers==0:
        p_bess_mw=0.0;e_bess_mwh=0.0
    elif p_bess_mw<=1e-6 or p_bess_mw>P_RATE_MAX*e_bess_mwh+1e-9:
        raise ValueError("BESS fuera de límites físicos.")
    espacio=calcular_screening_espacial(
        p_fv_mw=p_fv_mw,n_aeros=n_aeros,n_containers=n_containers,
        potencia_modulo_w=potencia_modulo_fv_w,pitch_fv_m=pitch_fv_m)
    if not espacio["cumple_screening_espacial"]:
        raise ValueError("No cumple screening espacial.")
    if not _screening_potencia_rapido(
        perfiles,p_fv_mw=p_fv_mw,n_aeros=n_aeros,p_bess_mw=p_bess_mw,
        limite_t1_mw=cfg_base.limite_t1_mw,tipo_aero=tipo_aero):
        raise ValueError("No alcanza potencia instantánea en año 20.")

    detalle,costo_tecnico=simular_20_anios(
        perfiles,p_fv_mw=p_fv_mw,n_aeros=n_aeros,p_bess_mw=p_bess_mw,
        e_bess_mwh=e_bess_mwh,p_contratada_mw=P_CONTRATADA_FIJA_MW,
        tipo_aero=tipo_aero,eta_carga=cfg_base.eta_carga,eta_descarga=cfg_base.eta_descarga,
        soc_min=cfg_base.soc_min,soc_max=cfg_base.soc_max,soc_inicial_frac=cfg_base.soc_inicial_frac,
        limite_t1_mw=cfg_base.limite_t1_mw,exportar_excedente=exportar_excedente,
        wacc=WACC,despacho_economico=False)
    if not bool(detalle["Cumple demanda"].all()):
        raise ValueError("No abastece 20 años en screening técnico.")

    credito_vp=0.0;ciclos_pot=0.0
    if n_containers>0:
        for _,row in detalle.iterrows():
            y=int(row["Año"]);soh=float(row["SOH inicio"])
            ah,cy=_credito_arbitraje_surrogate_v12(
                perfiles,p_fv_mw=p_fv_mw,n_aeros=n_aeros,p_bess_mw=p_bess_mw,
                e_bess_mwh=e_bess_mwh,soh=soh,anio=y,cfg_base=cfg_base,tipo_aero=tipo_aero)
            credito_vp+=ah/(1.0+WACC)**y;ciclos_pot+=cy
    FRACCION_CREDITO=0.35
    costo_sur=float(costo_tecnico-FRACCION_CREDITO*credito_vp)
    return costo_sur,{
        "P_FV [MW]":p_fv_mw,"N aeros":n_aeros,"P_BESS [MW]":p_bess_mw,
        "N containers BESS":n_containers,"E_BESS [MWh]":e_bess_mwh,
        "Costo surrogate 20a [USD]":costo_sur,"Costo técnico 20a [USD]":float(costo_tecnico),
        "Crédito arbitraje potencial VP [USD]":float(credito_vp),
        "Ciclos económicos potenciales 20a":float(ciclos_pot),
        "Uso terreno total screening [%]":float(espacio["uso_area_total_screening_pct"]),
    }


def optimizar_mixto_v12(
    perfiles: pd.DataFrame,
    *,
    cfg_base: Configuracion,
    ruta_excel: Path,
    fv_min: float,
    fv_max: float,
    pbess_min: float,
    pbess_max: float,
    aeros_min: int,
    aeros_max: int,
    containers_min: int,
    containers_max: int,
    potencia_modulo_fv_w: float,
    pitch_fv_m: float,
    tipo_aero: Literal["GE3.4", "GE3.8"],
    exportar_excedente: bool,
    maxiter: int,
    popsize: int,
    seed: int,
    tol: float,
    refinar: bool,
    n_finalistas: int = 6,
    objetivo_exacto_directo: bool = False,
) -> tuple[dict, pd.DataFrame, object]:
    """
    V12 en dos etapas por defecto:
      A) Differential Evolution mixto sobre un surrogate económico rápido;
      B) reevaluación EXACTA multianual V12 de los mejores finalistas.

    Con objetivo_exacto_directo=True, Differential Evolution llama al modelo exacto en
    cada candidato (mucho más lento, útil sólo para una corrida final exhaustiva).
    """
    if fv_max <= fv_min or pbess_max < pbess_min:
        raise ValueError("Intervalos continuos inválidos.")
    if not (0 <= aeros_min <= aeros_max <= N_AEROS_MAX_ESPACIO):
        raise ValueError(f"aeros debe quedar entre 0 y {N_AEROS_MAX_ESPACIO}.")
    if not (0 <= containers_min <= containers_max):
        raise ValueError("Rango de containers inválido.")

    bounds=[(float(fv_min),float(fv_max)),(float(aeros_min),float(aeros_max)),
            (float(pbess_min),float(pbess_max)),(float(containers_min),float(containers_max))]
    integrality=[False,True,False,True]
    cache:dict[tuple,float]={}
    explorados:list[dict]=[]
    mejor_sur=math.inf
    t0=time.time(); contador=0

    def key(pfv,na,pb,nc): return (round(float(pfv),4),int(na),round(float(pb),4),int(nc))

    def objetivo(x):
        nonlocal contador,mejor_sur
        contador+=1
        pfv=float(x[0]); na=int(round(x[1])); pb=float(x[2]); nc=int(round(x[3]))
        if nc==0: pb=0.0
        k=key(pfv,na,pb,nc)
        if k in cache: return cache[k]
        e=nc*cfg_base.e_container_mwh
        if nc>0 and (pb<=1e-6 or pb>P_RATE_MAX*e+1e-9):
            val=1e11+1e8*max(0,pb-P_RATE_MAX*e)
            cache[k]=val; return val
        try:
            if objetivo_exacto_directo:
                rr,_,_,_=evaluar_configuracion_v12(
                    perfiles,p_fv_mw=pfv,n_aeros=na,p_bess_mw=pb,n_containers=nc,
                    cfg_base=cfg_base,potencia_modulo_fv_w=potencia_modulo_fv_w,
                    pitch_fv_m=pitch_fv_m,tipo_aero=tipo_aero,
                    exportar_excedente=exportar_excedente,devolver_detalle_anio1=False)
                val=float(rr["Costo total 20a [USD]"])
                row={"P_FV [MW]":pfv,"N aeros":na,"P_BESS [MW]":pb,
                     "N containers BESS":nc,"Costo surrogate 20a [USD]":val}
            else:
                val,row=evaluar_surrogado_v12(
                    perfiles,p_fv_mw=pfv,n_aeros=na,p_bess_mw=pb,n_containers=nc,
                    cfg_base=cfg_base,potencia_modulo_fv_w=potencia_modulo_fv_w,
                    pitch_fv_m=pitch_fv_m,tipo_aero=tipo_aero,
                    exportar_excedente=exportar_excedente)
            cache[k]=val
            row=dict(row); row["Evaluación"]=contador; row["Tiempo acumulado [min]"]=(time.time()-t0)/60
            explorados.append(row)
            if val<mejor_sur:
                mejor_sur=val
                print(f"  nuevo mejor exploración #{contador}: ${val:,.0f} | FV={pfv:.4f} | aeros={na} | BESS={pb:.4f} MW / {e:.3f} MWh")
            return val
        except (ValueError,RuntimeError):
            cache[k]=1e11; return 1e11

    print("\n"+"="*80)
    print("V12 - OPTIMIZACIÓN CONTINUA/MIXTA DEL DISEÑO")
    print("="*80)
    print(f"P_FV continua       : [{fv_min:g}, {fv_max:g}] MW")
    print(f"N aeros entero      : [{aeros_min}, {aeros_max}]")
    print(f"P_BESS continua     : [{pbess_min:g}, {pbess_max:g}] MW")
    print(f"N containers entero : [{containers_min}, {containers_max}]")
    print(f"P contratada fija   : {P_CONTRATADA_FIJA_MW:g} MW")
    print("SOC anual           : cíclico (SOC final = SOC inicial)")
    print("Degradación         : FV anual + BESS por ciclos")
    print("Objetivo             : mínimo costo total descontado a 20 años")
    print("Vector inicial       : población automática; NO usa la configuración del Excel")
    print("Modo                 : "+("EXACTO directo (lento)" if objetivo_exacto_directo else f"2 etapas; {n_finalistas} finalistas exactos"))

    res=differential_evolution(objetivo,bounds=bounds,integrality=integrality,
        maxiter=int(maxiter),popsize=int(popsize),tol=float(tol),seed=int(seed),
        polish=False,updating="immediate",workers=1,disp=True)

    # Opcional: pulido sobre surrogate con enteras fijas (rápido). La validación final sigue siendo exacta.
    if refinar and explorados:
        best_sur=min(explorados,key=lambda r:r["Costo surrogate 20a [USD]"])
        na=int(best_sur["N aeros"]); nc=int(best_sur["N containers BESS"])
        maxpb=0.0 if nc==0 else min(pbess_max,P_RATE_MAX*nc*cfg_base.e_container_mwh)
        if nc==0:
            pb0=0.0
        else:
            pb0=min(max(float(best_sur["P_BESS [MW]"]),max(pbess_min,1e-4)),maxpb)
        def o2(z): return objetivo([z[0],na,z[1],nc])
        if nc==0:
            # sólo P_FV tiene sentido
            from scipy.optimize import minimize_scalar
            rr=minimize_scalar(lambda z:objetivo([z,na,0.0,nc]),bounds=(fv_min,fv_max),method="bounded",options={"maxiter":12,"xatol":0.01})
        elif maxpb>=max(pbess_min,1e-4):
            minimize(o2,[best_sur["P_FV [MW]"],pb0],method="Powell",
                     bounds=[(fv_min,fv_max),(max(pbess_min,1e-4),maxpb)],
                     options={"maxiter":8,"xtol":0.01,"ftol":5e-4,"disp":False})

    if not explorados:
        raise RuntimeError("No apareció ningún candidato factible durante la exploración.")

    # Seleccionar finalistas DIVERSOS. Primero toma el mejor global y luego, cuando
    # existen, el mejor de cada cantidad de aerogeneradores. Así el surrogate no puede
    # hacer que todos los finalistas sean clones con el mismo N_aeros.
    exp=pd.DataFrame(explorados).sort_values("Costo surrogate 20a [USD]").reset_index(drop=True)
    finalistas=[]; vistos=set(); aeros_cubiertos=set()
    def agregar(r):
        k=(round(float(r["P_FV [MW]"]),3),int(r["N aeros"]),round(float(r["P_BESS [MW]"]),3),int(r["N containers BESS"]))
        if k in vistos:return False
        vistos.add(k);finalistas.append(r);aeros_cubiertos.add(int(r["N aeros"]));return True
    agregar(exp.iloc[0])
    for na in sorted(exp["N aeros"].astype(int).unique()):
        if len(finalistas)>=max(1,int(n_finalistas)):break
        if na in aeros_cubiertos:continue
        sub=exp[exp["N aeros"].astype(int)==na]
        if not sub.empty:agregar(sub.iloc[0])
    # Completar con los siguientes mejores, priorizando combinaciones (aeros,containers) nuevas.
    pares={(int(r["N aeros"]),int(r["N containers BESS"])) for r in finalistas}
    for _,r in exp.iterrows():
        if len(finalistas)>=max(1,int(n_finalistas)):break
        par=(int(r["N aeros"]),int(r["N containers BESS"]))
        if par in pares:continue
        if agregar(r):pares.add(par)
    for _,r in exp.iterrows():
        if len(finalistas)>=max(1,int(n_finalistas)):break
        agregar(r)

    print(f"\nEtapa exacta: reevaluando {len(finalistas)} finalistas con los 20 años completos...")
    # IMPORTANTE: las evaluaciones exactas se ejecutan en procesos Python limpios.
    # Tras muchas llamadas a HiGHS durante Differential Evolution, algunos entornos
    # pueden degradar mucho su rendimiento. El subproceso evita ese problema y hace
    # reproducible el tiempo de cada finalista.
    exactos=[]; extras={}
    with tempfile.TemporaryDirectory(prefix="v12_finalistas_") as td:
        td=Path(td)
        for j,r in enumerate(finalistas,1):
            pfv=float(r["P_FV [MW]"]); na=int(r["N aeros"]); pb=float(r["P_BESS [MW]"]); nc=int(r["N containers BESS"])
            if nc==0: pb=0.0
            pref=td/f"cand_{j}"
            cmd=[
                sys.executable,str(Path(__file__).resolve()),
                "--excel",str(ruta_excel),
                "--tipo-aero",tipo_aero,
                "--pot-modulo-fv-w",str(potencia_modulo_fv_w),
                "--pitch-fv-m",str(pitch_fv_m),
                "--evaluar-candidato-interno",
                "--cand-pfv",str(pfv),"--cand-aeros",str(na),
                "--cand-pbess",str(pb),"--cand-containers",str(nc),
                "--cand-prefix",str(pref),
            ]
            if not exportar_excedente:
                cmd.append("--sin-exportar")
            proc=subprocess.run(cmd,capture_output=True,text=True)
            if proc.returncode!=0:
                msg=(proc.stderr or proc.stdout or "error desconocido").strip().splitlines()[-1]
                print(f"  finalista {j}: descartado en validación exacta ({msg})")
                continue
            try:
                rr=json.loads((Path(str(pref)+"_resumen.json")).read_text(encoding="utf-8"))
                d20=pd.read_csv(Path(str(pref)+"_20a.csv"))
                dh1=pd.read_csv(Path(str(pref)+"_anio1.csv"))
                plan=pd.read_csv(Path(str(pref)+"_plan.csv"))
            except Exception as exc:
                print(f"  finalista {j}: no pude leer salida exacta ({exc})")
                continue
            rr["Costo surrogate 20a [USD]"]=float(r["Costo surrogate 20a [USD]"])
            rr["_extra_id"]=len(exactos)
            extras[len(exactos)]=(d20,dh1,plan)
            exactos.append(rr)
            print(f"  finalista {j}: EXACTO=${rr['Costo total 20a [USD]']:,.0f} | FV={pfv:.4f} | aeros={na} | BESS={pb:.4f}/{nc*cfg_base.e_container_mwh:.3f}")
    if not exactos:
        raise RuntimeError("Ningún finalista superó la validación exacta V12. Aumentá --maxiter/--popsize.")

    tex=pd.DataFrame(exactos).sort_values("Costo total 20a [USD]").reset_index(drop=True)
    extra_id=int(tex.iloc[0]["_extra_id"])
    mejor_det=dict(tex.iloc[0])
    mejor_det.pop("_extra_id",None)
    detalle20,detalle_h1,plan=extras[extra_id]
    tex=tex.drop(columns=["_extra_id"])
    return mejor_det,tex,(res,detalle20,detalle_h1,plan,exp)



# =============================================================================
# V13 - OPTIMIZACIÓN POR FAMILIAS DISCRETAS + INFORME FINAL DETALLADO
# =============================================================================

def _json_safe_v13(v):
    if isinstance(v, (np.floating, np.integer)):
        return v.item()
    if isinstance(v, np.bool_):
        return bool(v)
    if isinstance(v, float) and (math.isnan(v) or math.isinf(v)):
        return None
    return v


def _evaluar_exacto_subproceso_v13(
    *,
    ruta_excel: Path,
    pfv: float,
    na: int,
    pbess: float,
    nc: int,
    tipo_aero: Literal["GE3.4", "GE3.8"],
    potencia_modulo_fv_w: float,
    pitch_fv_m: float,
    exportar_excedente: bool,
    carpeta_tmp: Path,
    etiqueta: str,
) -> tuple[dict, pd.DataFrame, pd.DataFrame | None, pd.DataFrame] | None:
    """Evalúa un candidato exacto en un proceso limpio (HiGHS/LP estable)."""
    pref = carpeta_tmp / etiqueta
    cmd = [
        sys.executable, str(Path(__file__).resolve()),
        "--excel", str(ruta_excel),
        "--tipo-aero", tipo_aero,
        "--pot-modulo-fv-w", str(potencia_modulo_fv_w),
        "--pitch-fv-m", str(pitch_fv_m),
        "--evaluar-candidato-interno",
        "--cand-pfv", str(float(pfv)),
        "--cand-aeros", str(int(na)),
        "--cand-pbess", str(float(pbess)),
        "--cand-containers", str(int(nc)),
        "--cand-prefix", str(pref),
    ]
    if not exportar_excedente:
        cmd.append("--sin-exportar")
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode != 0:
        return None
    try:
        rr = json.loads(Path(str(pref) + "_resumen.json").read_text(encoding="utf-8"))
        d20 = pd.read_csv(Path(str(pref) + "_20a.csv"))
        plan = pd.read_csv(Path(str(pref) + "_plan.csv"))
        h1_path = Path(str(pref) + "_anio1.csv")
        dh1 = pd.read_csv(h1_path) if h1_path.exists() else None
    except Exception:
        return None
    return rr, d20, dh1, plan


def _candidatos_diversos_familia_v13(explorados: list[dict], cantidad: int = 3) -> list[dict]:
    """Toma los mejores surrogate de una familia evitando candidatos prácticamente clonados."""
    if not explorados:
        return []
    df = pd.DataFrame(explorados).sort_values("Costo surrogate 20a [USD]")
    elegidos: list[dict] = []
    for _, r in df.iterrows():
        cand = dict(r)
        if not elegidos:
            elegidos.append(cand)
        else:
            separado = all(
                abs(float(cand["P_FV [MW]"]) - float(e["P_FV [MW]"])) >= 0.35
                or abs(float(cand["P_BESS [MW]"]) - float(e["P_BESS [MW]"])) >= 0.25
                for e in elegidos
            )
            if separado:
                elegidos.append(cand)
        if len(elegidos) >= max(1, int(cantidad)):
            break
    return elegidos


def _explorar_familia_surrogate_v13(
    perfiles: pd.DataFrame,
    *,
    na: int,
    nc: int,
    cfg_base: Configuracion,
    fv_min: float,
    fv_max: float,
    pbess_min: float,
    pbess_max: float,
    potencia_modulo_fv_w: float,
    pitch_fv_m: float,
    tipo_aero: Literal["GE3.4", "GE3.8"],
    exportar_excedente: bool,
    maxiter: int,
    popsize: int,
    seed: int,
    tol: float,
    candidatos_guardar: int,
) -> tuple[list[dict], object | None]:
    """
    Explora P_FV/P_BESS sobre TODO el dominio continuo de una familia discreta fija.
    V13 no usa los rangos encontrados por V12 como límites.
    """
    na, nc = int(na), int(nc)
    e_bess = nc * cfg_base.e_container_mwh
    explorados: list[dict] = []
    cache: dict[tuple, float] = {}

    if nc == 0:
        max_pb = 0.0
        min_pb = 0.0
        bounds = [(float(fv_min), float(fv_max))]
    else:
        max_pb = min(float(pbess_max), P_RATE_MAX * e_bess)
        min_pb = max(float(pbess_min), 1e-3)
        if max_pb < min_pb - 1e-12:
            return [], None
        bounds = [(float(fv_min), float(fv_max)), (min_pb, max_pb)]

    def objetivo(z):
        pfv = float(z[0])
        pb = 0.0 if nc == 0 else float(z[1])
        k = (round(pfv, 4), round(pb, 4))
        if k in cache:
            return cache[k]
        try:
            val, row = evaluar_surrogado_v12(
                perfiles,
                p_fv_mw=pfv, n_aeros=na, p_bess_mw=pb, n_containers=nc,
                cfg_base=cfg_base,
                potencia_modulo_fv_w=potencia_modulo_fv_w,
                pitch_fv_m=pitch_fv_m,
                tipo_aero=tipo_aero,
                exportar_excedente=exportar_excedente,
            )
            row = dict(row)
            explorados.append(row)
            cache[k] = float(val)
            return float(val)
        except (ValueError, RuntimeError):
            cache[k] = 1e11
            return 1e11

    res = differential_evolution(
        objetivo,
        bounds=bounds,
        maxiter=int(maxiter), popsize=int(popsize), tol=float(tol),
        seed=int(seed), polish=False, updating="immediate", workers=1, disp=False,
    )
    return _candidatos_diversos_familia_v13(explorados, candidatos_guardar), res


def _refinar_familia_exacto_v13(
    *,
    mejor_inicial: dict,
    na: int,
    nc: int,
    cfg_base: Configuracion,
    ruta_excel: Path,
    fv_min: float,
    fv_max: float,
    pbess_min: float,
    pbess_max: float,
    tipo_aero: Literal["GE3.4", "GE3.8"],
    potencia_modulo_fv_w: float,
    pitch_fv_m: float,
    exportar_excedente: bool,
    carpeta_tmp: Path,
    rondas: int,
    paso_fv_inicial: float,
    paso_pbess_inicial: float,
    contador_inicio: int,
) -> tuple[dict, pd.DataFrame, pd.DataFrame | None, pd.DataFrame, list[dict], int]:
    """
    Refinamiento EXACTO local sólo después de haber explorado globalmente toda la familia.
    Usa búsqueda por coordenadas y reduce el paso en cada ronda. No impone un subdominio fijo.
    """
    actual = mejor_inicial
    d20_actual = actual.pop("_d20")
    dh1_actual = actual.pop("_dh1")
    plan_actual = actual.pop("_plan")
    hist: list[dict] = []
    contador = contador_inicio
    step_fv = float(paso_fv_inicial)
    step_pb = float(paso_pbess_inicial)
    max_pb_fis = 0.0 if nc == 0 else min(float(pbess_max), P_RATE_MAX * nc * cfg_base.e_container_mwh)
    min_pb_fis = 0.0 if nc == 0 else max(float(pbess_min), 1e-3)

    for ronda in range(max(0, int(rondas))):
        pf0 = float(actual["P_FV [MW]"])
        pb0 = float(actual["P_BESS [MW]"])
        puntos = [(pf0 - step_fv, pb0), (pf0 + step_fv, pb0)]
        if nc > 0:
            puntos += [(pf0, pb0 - step_pb), (pf0, pb0 + step_pb)]
        hubo_mejora = False
        for pfv, pb in puntos:
            pfv = min(max(float(pfv), float(fv_min)), float(fv_max))
            if nc == 0:
                pb = 0.0
            else:
                pb = min(max(float(pb), min_pb_fis), max_pb_fis)
            if abs(pfv - pf0) < 1e-9 and abs(pb - pb0) < 1e-9:
                continue
            contador += 1
            ev = _evaluar_exacto_subproceso_v13(
                ruta_excel=ruta_excel, pfv=pfv, na=na, pbess=pb, nc=nc,
                tipo_aero=tipo_aero, potencia_modulo_fv_w=potencia_modulo_fv_w,
                pitch_fv_m=pitch_fv_m, exportar_excedente=exportar_excedente,
                carpeta_tmp=carpeta_tmp, etiqueta=f"ref_{na}_{nc}_{contador}",
            )
            if ev is None:
                continue
            rr, d20, dh1, plan = ev
            rr["Etapa V13"] = f"refinamiento ronda {ronda+1}"
            hist.append(dict(rr))
            if float(rr["Costo total 20a [USD]"]) + 1e-6 < float(actual["Costo total 20a [USD]"]):
                actual = dict(rr)
                d20_actual, dh1_actual, plan_actual = d20, dh1, plan
                hubo_mejora = True
        step_fv *= 0.35
        step_pb *= 0.35
        # Aunque no haya mejora, una segunda escala más fina puede encontrar el mínimo cerca del centro.
    actual["_d20"] = d20_actual
    actual["_dh1"] = dh1_actual
    actual["_plan"] = plan_actual
    return actual, d20_actual, dh1_actual, plan_actual, hist, contador


def optimizar_por_familias_v13(
    perfiles: pd.DataFrame,
    *,
    cfg_base: Configuracion,
    ruta_excel: Path,
    fv_min: float,
    fv_max: float,
    pbess_min: float,
    pbess_max: float,
    aeros_min: int,
    aeros_max: int,
    containers_min: int,
    containers_max: int,
    potencia_modulo_fv_w: float,
    pitch_fv_m: float,
    tipo_aero: Literal["GE3.4", "GE3.8"],
    exportar_excedente: bool,
    maxiter_familia: int,
    popsize_familia: int,
    seed: int,
    tol: float,
    candidatos_surrogate_por_familia: int,
    exactos_por_familia: int,
    top_familias_refinar: int,
    rondas_refinamiento: int,
    paso_fv_refinar: float,
    paso_pbess_refinar: float,
) -> tuple[dict, pd.DataFrame, pd.DataFrame, pd.DataFrame, pd.DataFrame | None, pd.DataFrame]:
    """
    Estrategia V13:
      1) enumera TODAS las familias discretas (aeros, containers);
      2) en cada familia explora P_FV y P_BESS sobre el dominio continuo COMPLETO;
      3) valida exactamente al menos el mejor candidato de cada familia que el surrogate considera factible;
      4) refina exactamente las mejores familias globales.
    """
    if fv_max <= fv_min or pbess_max < pbess_min:
        raise ValueError("Intervalos continuos inválidos.")
    if not (0 <= aeros_min <= aeros_max <= N_AEROS_MAX_ESPACIO):
        raise ValueError(f"aeros debe quedar entre 0 y {N_AEROS_MAX_ESPACIO}.")
    if not (0 <= containers_min <= containers_max):
        raise ValueError("Rango de containers inválido.")

    familias = list(product(range(aeros_min, aeros_max + 1), range(containers_min, containers_max + 1)))
    print("\n" + "=" * 80)
    print("V13 - OPTIMIZACIÓN POR FAMILIAS DISCRETAS")
    print("=" * 80)
    print(f"Familias (N_aeros, N_containers): {len(familias)}")
    print(f"P_FV continua por familia        : [{fv_min:g}, {fv_max:g}] MW")
    print(f"P_BESS continua por familia      : [{pbess_min:g}, {pbess_max:g}] MW, limitada además por 0,5C")
    print("Dominio de refinamiento          : NO se recorta con resultados de V12")
    print("Validación                       : modelo exacto 20 años por familia factible")
    print("Objetivo                         : mínimo costo total descontado a 20 años")

    filas_familias: list[dict] = []
    hist_exacto: list[dict] = []
    exactos_familia: list[dict] = []
    contador_exacto = 0
    t0 = time.time()

    with tempfile.TemporaryDirectory(prefix="v13_familias_") as td:
        td = Path(td)
        for idx, (na, nc) in enumerate(familias, 1):
            print(f"\nFamilia {idx}/{len(familias)}: aeros={na}, containers={nc} (E={nc*cfg_base.e_container_mwh:.3f} MWh)")
            cands, _ = _explorar_familia_surrogate_v13(
                perfiles, na=na, nc=nc, cfg_base=cfg_base,
                fv_min=fv_min, fv_max=fv_max, pbess_min=pbess_min, pbess_max=pbess_max,
                potencia_modulo_fv_w=potencia_modulo_fv_w, pitch_fv_m=pitch_fv_m,
                tipo_aero=tipo_aero, exportar_excedente=exportar_excedente,
                maxiter=maxiter_familia, popsize=popsize_familia,
                seed=seed + 101*na + 17*nc, tol=tol,
                candidatos_guardar=max(candidatos_surrogate_por_familia, exactos_por_familia),
            )
            if not cands:
                filas_familias.append({
                    "N aeros": na, "N containers BESS": nc, "E_BESS [MWh]": nc*cfg_base.e_container_mwh,
                    "Factible surrogate": False, "Factible exacto": False,
                })
                print("  sin candidato factible en exploración global")
                continue

            best_sur = cands[0]
            exactos_local: list[tuple[dict, pd.DataFrame, pd.DataFrame | None, pd.DataFrame]] = []
            for j, cand in enumerate(cands[:max(1, int(exactos_por_familia))], 1):
                contador_exacto += 1
                pfv = float(cand["P_FV [MW]"])
                pb = 0.0 if nc == 0 else float(cand["P_BESS [MW]"])
                ev = _evaluar_exacto_subproceso_v13(
                    ruta_excel=ruta_excel, pfv=pfv, na=na, pbess=pb, nc=nc,
                    tipo_aero=tipo_aero, potencia_modulo_fv_w=potencia_modulo_fv_w,
                    pitch_fv_m=pitch_fv_m, exportar_excedente=exportar_excedente,
                    carpeta_tmp=td, etiqueta=f"fam_{na}_{nc}_{j}_{contador_exacto}",
                )
                if ev is None:
                    continue
                rr, d20, dh1, plan = ev
                rr["Costo surrogate 20a [USD]"] = float(cand["Costo surrogate 20a [USD]"])
                rr["Etapa V13"] = "validación familia"
                hist_exacto.append(dict(rr))
                exactos_local.append((rr, d20, dh1, plan))

            if not exactos_local:
                filas_familias.append({
                    "N aeros": na, "N containers BESS": nc, "E_BESS [MWh]": nc*cfg_base.e_container_mwh,
                    "Factible surrogate": True, "Factible exacto": False,
                    "P_FV mejor surrogate [MW]": float(best_sur["P_FV [MW]"]),
                    "P_BESS mejor surrogate [MW]": float(best_sur["P_BESS [MW]"]),
                    "Costo surrogate mejor [USD]": float(best_sur["Costo surrogate 20a [USD]"]),
                })
                print("  candidato surrogate no superó validación exacta")
                continue

            exactos_local.sort(key=lambda x: float(x[0]["Costo total 20a [USD]"]))
            rr, d20, dh1, plan = exactos_local[0]
            guardado = dict(rr)
            guardado["_d20"] = d20
            guardado["_dh1"] = dh1
            guardado["_plan"] = plan
            exactos_familia.append(guardado)
            filas_familias.append({
                "N aeros": na,
                "N containers BESS": nc,
                "E_BESS [MWh]": nc*cfg_base.e_container_mwh,
                "Factible surrogate": True,
                "Factible exacto": True,
                "P_FV mejor surrogate [MW]": float(best_sur["P_FV [MW]"]),
                "P_BESS mejor surrogate [MW]": float(best_sur["P_BESS [MW]"]),
                "Costo surrogate mejor [USD]": float(best_sur["Costo surrogate 20a [USD]"]),
                "P_FV exacto inicial [MW]": float(rr["P_FV [MW]"]),
                "P_BESS exacto inicial [MW]": float(rr["P_BESS [MW]"]),
                "Costo exacto inicial [USD]": float(rr["Costo total 20a [USD]"]),
                "Tiempo acumulado [min]": (time.time()-t0)/60.0,
            })
            print(f"  EXACTO=${float(rr['Costo total 20a [USD]']):,.0f} | FV={float(rr['P_FV [MW]']):.4f} MW | BESS={float(rr['P_BESS [MW]']):.4f} MW")

        if not exactos_familia:
            raise RuntimeError("Ninguna familia resultó factible en validación exacta V13.")

        # Refinar las mejores familias según COSTO EXACTO, no según surrogate.
        exactos_familia.sort(key=lambda r: float(r["Costo total 20a [USD]"]))
        top = exactos_familia[:max(0, min(int(top_familias_refinar), len(exactos_familia)))]
        if top and rondas_refinamiento > 0:
            print("\n" + "-"*80)
            print(f"Refinamiento EXACTO de las {len(top)} mejores familias por costo exacto")
            print("-"*80)
        refinados_por_par: dict[tuple[int,int], dict] = {}
        for k, ini in enumerate(top, 1):
            na = int(ini["N aeros"]); nc = int(ini["N containers BESS"])
            print(f"  refinando {k}/{len(top)}: aeros={na}, containers={nc}, costo inicial=${float(ini['Costo total 20a [USD]']):,.0f}")
            actual, d20, dh1, plan, hist, contador_exacto = _refinar_familia_exacto_v13(
                mejor_inicial=dict(ini), na=na, nc=nc, cfg_base=cfg_base,
                ruta_excel=ruta_excel, fv_min=fv_min, fv_max=fv_max,
                pbess_min=pbess_min, pbess_max=pbess_max,
                tipo_aero=tipo_aero, potencia_modulo_fv_w=potencia_modulo_fv_w,
                pitch_fv_m=pitch_fv_m, exportar_excedente=exportar_excedente,
                carpeta_tmp=td, rondas=rondas_refinamiento,
                paso_fv_inicial=paso_fv_refinar, paso_pbess_inicial=paso_pbess_refinar,
                contador_inicio=contador_exacto,
            )
            hist_exacto.extend(hist)
            refinados_por_par[(na,nc)] = actual
            print(f"    -> costo refinado=${float(actual['Costo total 20a [USD]']):,.0f} | FV={float(actual['P_FV [MW]']):.4f} | BESS={float(actual['P_BESS [MW]']):.4f}")

        # Sustituir candidatos iniciales por refinados donde corresponda.
        finales: list[dict] = []
        for ini in exactos_familia:
            par = (int(ini["N aeros"]), int(ini["N containers BESS"]))
            finales.append(refinados_por_par.get(par, ini))
        finales.sort(key=lambda r: float(r["Costo total 20a [USD]"]))
        mejor = finales[0]
        detalle20 = mejor.pop("_d20")
        detalle_h1 = mejor.pop("_dh1")
        plan = mejor.pop("_plan")

    # Completar tabla de familias con el resultado refinado, si existió.
    df_fam = pd.DataFrame(filas_familias)
    if not df_fam.empty:
        for par, rr in refinados_por_par.items():
            m = (df_fam["N aeros"].astype(int)==par[0]) & (df_fam["N containers BESS"].astype(int)==par[1])
            df_fam.loc[m, "P_FV refinado [MW]"] = float(rr["P_FV [MW]"])
            df_fam.loc[m, "P_BESS refinado [MW]"] = float(rr["P_BESS [MW]"])
            df_fam.loc[m, "Costo exacto refinado [USD]"] = float(rr["Costo total 20a [USD]"])
        # costo representativo final por familia
        if "Costo exacto refinado [USD]" in df_fam.columns:
            df_fam["Costo final familia [USD]"] = pd.to_numeric(df_fam["Costo exacto refinado [USD]"], errors="coerce")
        else:
            df_fam["Costo final familia [USD]"] = np.nan
        if "Costo exacto inicial [USD]" in df_fam.columns:
            base_cost = pd.to_numeric(df_fam["Costo exacto inicial [USD]"], errors="coerce")
            df_fam["Costo final familia [USD]"] = df_fam["Costo final familia [USD]"].where(df_fam["Costo final familia [USD]"].notna(), base_cost)
        df_fam = df_fam.sort_values("Costo final familia [USD]", na_position="last").reset_index(drop=True)

    df_hist = pd.DataFrame(hist_exacto)
    return dict(mejor), df_fam, df_hist, detalle20, detalle_h1, plan


def construir_evolucion_anual_v13(detalle20: pd.DataFrame, mejor: dict) -> pd.DataFrame:
    """Agrega indicadores de evolución para explicar degradación y compras de red del óptimo."""
    d = detalle20.copy()
    d["Energía red total [MWh]"] = d[["Energía red Valle [MWh]", "Energía red Resto [MWh]", "Energía red Pico [MWh]"]].sum(axis=1)
    red1 = float(d.iloc[0]["Energía red total [MWh]"])
    fv1 = float(d.iloc[0].get("Energía FV [MWh]", np.nan))
    d["Aumento red vs año 1 [MWh]"] = d["Energía red total [MWh]"] - red1
    d["Aumento red vs año 1 [%]"] = np.where(red1 > 1e-12, 100.0*d["Aumento red vs año 1 [MWh]"]/red1, np.nan)
    if "Energía FV [MWh]" in d.columns and math.isfinite(fv1):
        d["Pérdida FV vs año 1 [MWh]"] = fv1 - d["Energía FV [MWh]"]
        d["Variación FV vs año 1 [%]"] = 100.0*(d["Energía FV [MWh]"]/fv1 - 1.0)
    d["SOH BESS inicio [%]"] = 100.0*d["SOH inicio"]
    d["SOH BESS final [%]"] = 100.0*d["SOH final"]
    e_nom = float(mejor["E_BESS [MWh]"])
    d["Pérdida capacidad BESS vs nominal [MWh]"] = e_nom - d["Capacidad BESS final [MWh]"]
    d["Costo energía red a precios año 1 [USD]"] = d["Costo energía red [USD]"] / ((1.0+ESCALAMIENTO_COSTOS)**(d["Año"]-1))
    d["VP costo energía red [USD]"] = d["Costo energía red [USD]"] / ((1.0+WACC)**d["Año"])
    if "Energía demanda [MWh]" in d.columns:
        d["Demanda cubierta por red [%]"] = 100.0*d["Energía red total [MWh]"]/d["Energía demanda [MWh]"]
    return d


def construir_resumen_economico_v13(detalle20: pd.DataFrame, mejor: dict) -> pd.DataFrame:
    """Desglose del costo total a valor presente para el óptimo."""
    anios = detalle20["Año"].to_numpy(float)
    desc = (1.0 + WACC) ** anios
    componentes = [
        ("CAPEX FV", float(mejor["CAPEX FV [USD]"])),
        ("CAPEX eólico", float(mejor["CAPEX eólico [USD]"])),
        ("CAPEX BESS energía", float(mejor["CAPEX BESS energía [USD]"])),
        ("CAPEX BESS potencia", float(mejor["CAPEX BESS potencia [USD]"])),
        ("CAPEX fijo proyecto", float(CAPEX_FIJO_USD)),
        ("VP OPEX FV", float(np.sum(detalle20["OPEX FV [USD]"].to_numpy(float)/desc))),
        ("VP OPEX eólico", float(np.sum(detalle20["OPEX eólico [USD]"].to_numpy(float)/desc))),
        ("VP OPEX BESS", float(np.sum(detalle20["OPEX BESS [USD]"].to_numpy(float)/desc))),
        ("VP potencia contratada", float(np.sum(detalle20["Costo potencia contratada [USD]"].to_numpy(float)/desc))),
        ("VP red Valle", float(np.sum(detalle20["Costo red Valle [USD]"].to_numpy(float)/desc))),
        ("VP red Resto", float(np.sum(detalle20["Costo red Resto [USD]"].to_numpy(float)/desc))),
        ("VP red Pico", float(np.sum(detalle20["Costo red Pico [USD]"].to_numpy(float)/desc))),
        ("VP reemplazo BESS", float(np.sum(detalle20["Costo reemplazo BESS [USD]"].to_numpy(float)/desc))),
    ]
    total = sum(v for _,v in componentes)
    df = pd.DataFrame(componentes, columns=["Componente", "Valor presente [USD]"])
    df["Participación costo total [%]"] = 100.0*df["Valor presente [USD]"]/total if total else np.nan
    return df


def generar_analisis_final_v13(mejor: dict, evolucion: pd.DataFrame, economico: pd.DataFrame) -> str:
    y1, y20 = evolucion.iloc[0], evolucion.iloc[-1]
    red1 = float(y1["Energía red total [MWh]"]); red20 = float(y20["Energía red total [MWh]"])
    fv1 = float(y1.get("Energía FV [MWh]", np.nan)); fv20 = float(y20.get("Energía FV [MWh]", np.nan))
    lines = [
        "TRABAJO INTEGRADOR - ANÁLISIS FINAL DEL ÓPTIMO V13",
        "="*72,
        "",
        "DISEÑO ÓPTIMO",
        f"P_FV                         : {float(mejor['P_FV [MW]']):.4f} MW",
        f"Aerogeneradores              : {int(mejor['N aeros'])} ({float(mejor['P_EOL instalada [MW]']):.3f} MW instalados)",
        f"BESS potencia                 : {float(mejor['P_BESS [MW]']):.4f} MW",
        f"BESS energía                  : {float(mejor['E_BESS [MWh]']):.3f} MWh ({int(mejor['N containers BESS'])} containers)",
        f"Duración nominal BESS         : {float(mejor['Duración BESS nominal [h]']):.3f} h",
        f"Potencia contratada           : {P_CONTRATADA_FIJA_MW:.1f} MW",
        "",
        "RESULTADO ECONÓMICO",
        f"CAPEX total                   : USD {float(mejor['CAPEX total [USD]']):,.0f}",
        f"VP operación 20 años          : USD {float(mejor['VP operación 20a [USD]']):,.0f}",
        f"COSTO TOTAL 20 AÑOS           : USD {float(mejor['Costo total 20a [USD]']):,.0f}",
        "",
        "EVOLUCIÓN AÑO 1 -> AÑO 20",
    ]
    if math.isfinite(fv1) and fv1 > 0:
        lines += [
            f"Generación FV año 1           : {fv1:,.1f} MWh",
            f"Generación FV año 20          : {fv20:,.1f} MWh",
            f"Variación generación FV       : {(fv20/fv1-1)*100:.2f} %",
        ]
    lines += [
        f"Factor FV año 1 / año 20      : {float(y1['Factor FV']):.3f} / {float(y20['Factor FV']):.3f}",
        f"SOH BESS inicio               : {float(y1['SOH inicio'])*100:.2f} %",
        f"SOH BESS final año 20         : {float(y20['SOH final'])*100:.2f} %",
        f"Capacidad BESS final año 20   : {float(y20['Capacidad BESS final [MWh]']):.3f} MWh",
        f"Ciclos acumulados             : {float(y20['Ciclos equivalentes acumulados']):,.1f}",
        f"Compra red año 1              : {red1:,.1f} MWh",
        f"Compra red año 20             : {red20:,.1f} MWh",
        f"Aumento compra red            : {red20-red1:+,.1f} MWh ({((red20/red1)-1)*100 if red1 else float('nan'):+.2f} %)",
        f"Costo red año 1               : USD {float(y1['Costo energía red [USD]']):,.0f}",
        f"Costo red año 20 nominal      : USD {float(y20['Costo energía red [USD]']):,.0f}",
        f"Costo red año 20 a precios A1 : USD {float(y20['Costo energía red a precios año 1 [USD]']):,.0f}",
        "",
        "BALANCE 20 AÑOS",
        f"Exportación acumulada         : {float(mejor['Exportación 20a [MWh]']):,.1f} MWh (sin remuneración)",
        f"Demanda no abastecida         : {float(mejor['Energía no abastecida 20a [MWh]']):,.6f} MWh",
        f"Horas sin abastecer           : {int(mejor['Horas no cumple 20a'])}",
        f"Uso terreno screening         : {float(mejor['Uso terreno total screening [%]']):.2f} %",
        "",
        "NOTA:",
        "El aumento de compra de red respecto del año 1 refleja la evolución conjunta del",
        "sistema bajo los mismos perfiles base: degradación FV, pérdida de capacidad BESS",
        "por ciclos y cambios del despacho económico. No se atribuye exclusivamente a una",
        "única tecnología. El layout espacial sigue siendo un screening y no un micrositing final.",
        "",
        "DESGLOSE DEL COSTO TOTAL A VALOR PRESENTE",
    ]
    for _, r in economico.iterrows():
        lines.append(
            f"{str(r['Componente']):28s}: USD {float(r['Valor presente [USD]']):>13,.0f} "
            f"({float(r['Participación costo total [%]']):5.2f} %)"
        )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="V13: optimización por familias discretas con P_FV/P_BESS continuas e informe final detallado a 20 años."
    )
    parser.add_argument("--excel", type=Path, default=None)
    parser.add_argument("--tipo-aero", choices=["GE3.4", "GE3.8"], default="GE3.4")
    parser.add_argument("--sin-exportar", action="store_true")
    parser.add_argument("--pot-modulo-fv-w", type=float, default=POTENCIA_MODULO_FV_W_DEFAULT)
    parser.add_argument("--pitch-fv-m", type=float, default=PITCH_FV_DEFAULT_M)

    parser.add_argument("--optimizar", action="store_true", help="Ejecuta V13 y busca el mínimo global por familias discretas.")
    parser.add_argument("--fv-min", type=float, default=0.0)
    parser.add_argument("--fv-max", type=float, default=30.0)
    parser.add_argument("--pbess-min", type=float, default=0.0)
    parser.add_argument("--pbess-max", type=float, default=12.0)
    parser.add_argument("--aeros-min", type=int, default=0)
    parser.add_argument("--aeros-max", type=int, default=N_AEROS_MAX_ESPACIO)
    parser.add_argument("--containers-min", type=int, default=0)
    parser.add_argument("--containers-max", type=int, default=8)
    parser.add_argument("--maxiter-familia", type=int, default=6, help="Generaciones surrogate DE POR familia.")
    parser.add_argument("--popsize-familia", type=int, default=4, help="Población surrogate DE POR familia.")
    parser.add_argument("--tol", type=float, default=0.01)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--candidatos-surrogate-familia", type=int, default=3, help="Candidatos diversos retenidos por familia.")
    parser.add_argument("--exactos-por-familia", type=int, default=1, help="Validaciones exactas iniciales por familia factible.")
    parser.add_argument("--top-familias-refinar", type=int, default=6, help="Cantidad de mejores familias exactas a refinar.")
    parser.add_argument("--rondas-refinamiento", type=int, default=2, help="Rondas de refinamiento exacto por coordenadas.")
    parser.add_argument("--paso-fv-refinar", type=float, default=0.75, help="Paso FV inicial del refinamiento exacto [MW].")
    parser.add_argument("--paso-pbess-refinar", type=float, default=0.50, help="Paso BESS inicial del refinamiento exacto [MW].")

    # Modo interno para subprocess exacto.
    parser.add_argument("--evaluar-candidato-interno", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--cand-pfv", type=float, default=None, help=argparse.SUPPRESS)
    parser.add_argument("--cand-aeros", type=int, default=None, help=argparse.SUPPRESS)
    parser.add_argument("--cand-pbess", type=float, default=None, help=argparse.SUPPRESS)
    parser.add_argument("--cand-containers", type=int, default=None, help=argparse.SUPPRESS)
    parser.add_argument("--cand-prefix", type=Path, default=None, help=argparse.SUPPRESS)

    args = parser.parse_args()
    ruta = args.excel.resolve() if args.excel is not None else buscar_excel_por_defecto()
    if not ruta.exists():
        raise FileNotFoundError(f"No encontré el Excel: {ruta}")

    cfg = leer_configuracion_excel(ruta)
    perfiles = cargar_perfiles(ruta, cfg.p_fv_mw)
    carpeta = ruta.parent
    print(f"Excel utilizado: {ruta}")

    if args.evaluar_candidato_interno:
        requeridos = [args.cand_pfv, args.cand_aeros, args.cand_pbess, args.cand_containers, args.cand_prefix]
        if any(v is None for v in requeridos):
            raise ValueError("Faltan parámetros internos del candidato.")
        rr, d20, dh1, plan = evaluar_configuracion_v12(
            perfiles,
            p_fv_mw=args.cand_pfv, n_aeros=args.cand_aeros,
            p_bess_mw=args.cand_pbess, n_containers=args.cand_containers,
            cfg_base=cfg, potencia_modulo_fv_w=args.pot_modulo_fv_w,
            pitch_fv_m=args.pitch_fv_m, tipo_aero=args.tipo_aero,
            exportar_excedente=not args.sin_exportar, devolver_detalle_anio1=True,
        )
        pref = args.cand_prefix
        Path(str(pref)+"_resumen.json").write_text(
            json.dumps({k:_json_safe_v13(v) for k,v in rr.items()}, ensure_ascii=False, indent=2), encoding="utf-8"
        )
        d20.to_csv(Path(str(pref)+"_20a.csv"), index=False, decimal=".")
        plan.to_csv(Path(str(pref)+"_plan.csv"), index=False, decimal=".")
        if dh1 is not None:
            dh1.to_csv(Path(str(pref)+"_anio1.csv"), index=False, decimal=".")
        return

    if not args.optimizar:
        print("\nV13 está pensada para buscar el óptimo. Ejecutá el archivo con --optimizar.")
        print("No se evalúa automáticamente la configuración del Excel para no perder tiempo.")
        return

    mejor, familias, hist, detalle20, detalle_h1, plan = optimizar_por_familias_v13(
        perfiles,
        cfg_base=cfg, ruta_excel=ruta,
        fv_min=args.fv_min, fv_max=args.fv_max,
        pbess_min=args.pbess_min, pbess_max=args.pbess_max,
        aeros_min=args.aeros_min, aeros_max=args.aeros_max,
        containers_min=args.containers_min, containers_max=args.containers_max,
        potencia_modulo_fv_w=args.pot_modulo_fv_w, pitch_fv_m=args.pitch_fv_m,
        tipo_aero=args.tipo_aero, exportar_excedente=not args.sin_exportar,
        maxiter_familia=args.maxiter_familia, popsize_familia=args.popsize_familia,
        seed=args.seed, tol=args.tol,
        candidatos_surrogate_por_familia=args.candidatos_surrogate_familia,
        exactos_por_familia=args.exactos_por_familia,
        top_familias_refinar=args.top_familias_refinar,
        rondas_refinamiento=args.rondas_refinamiento,
        paso_fv_refinar=args.paso_fv_refinar,
        paso_pbess_refinar=args.paso_pbess_refinar,
    )

    evolucion = construir_evolucion_anual_v13(detalle20, mejor)
    economico = construir_resumen_economico_v13(detalle20, mejor)
    analisis = generar_analisis_final_v13(mejor, evolucion, economico)

    print("\n" + "="*80)
    print("ÓPTIMO ECONÓMICO GLOBAL V13")
    print("="*80)
    for k, v in mejor.items():
        if isinstance(v, (float, np.floating)):
            print(f"{k:42s}: {float(v):,.6f}")
        else:
            print(f"{k:42s}: {v}")

    y1, y20 = evolucion.iloc[0], evolucion.iloc[-1]
    print("\n" + "="*80)
    print("EVOLUCIÓN DEL ÓPTIMO - AÑO 1 vs AÑO 20")
    print("="*80)
    if "Energía FV [MWh]" in evolucion.columns:
        print(f"FV año 1 [MWh]                         : {float(y1['Energía FV [MWh]']):,.3f}")
        print(f"FV año 20 [MWh]                        : {float(y20['Energía FV [MWh]']):,.3f}")
    print(f"Factor FV año 1 -> 20                  : {float(y1['Factor FV']):.3f} -> {float(y20['Factor FV']):.3f}")
    print(f"SOH BESS inicio -> final 20            : {float(y1['SOH inicio'])*100:.2f}% -> {float(y20['SOH final'])*100:.2f}%")
    print(f"Ciclos acumulados                      : {float(y20['Ciclos equivalentes acumulados']):,.3f}")
    print(f"Compra red año 1 [MWh]                 : {float(y1['Energía red total [MWh]']):,.3f}")
    print(f"Compra red año 20 [MWh]                : {float(y20['Energía red total [MWh]']):,.3f}")
    print(f"Aumento compra red año 20 vs año 1     : {float(y20['Aumento red vs año 1 [MWh]']):+,.3f} MWh ({float(y20['Aumento red vs año 1 [%]']):+.2f}%)")
    print(f"Exportación acumulada 20a [MWh]        : {float(mejor['Exportación 20a [MWh]']):,.3f}")
    print(f"Demanda no abastecida 20a [MWh]        : {float(mejor['Energía no abastecida 20a [MWh]']):,.6f}")

    # Archivos finales V13.
    f_fam = carpeta / "v13_mejor_por_familia.csv"
    f_hist = carpeta / "v13_evaluaciones_exactas.csv"
    f_evol = carpeta / "optimo_v13_evolucion_20_anios.csv"
    f_eco = carpeta / "optimo_v13_desglose_economico.csv"
    f_plan = carpeta / "optimo_v13_plan_degradacion.csv"
    f_h1 = carpeta / "optimo_v13_anio1_horario.csv"
    f_txt = carpeta / "optimo_v13_analisis_final.txt"
    f_json = carpeta / "optimo_v13_resumen.json"

    familias.to_csv(f_fam, index=False, decimal=".")
    if not hist.empty:
        hist.to_csv(f_hist, index=False, decimal=".")
    evolucion.to_csv(f_evol, index=False, decimal=".")
    economico.to_csv(f_eco, index=False, decimal=".")
    plan.to_csv(f_plan, index=False, decimal=".")
    if detalle_h1 is not None:
        detalle_h1.to_csv(f_h1, index=False, decimal=".")
    f_txt.write_text(analisis, encoding="utf-8")
    f_json.write_text(json.dumps({k:_json_safe_v13(v) for k,v in mejor.items()}, ensure_ascii=False, indent=2), encoding="utf-8")

    print("\nArchivos finales V13:")
    print(f"  {f_fam}")
    if not hist.empty: print(f"  {f_hist}")
    print(f"  {f_evol}")
    print(f"  {f_eco}")
    print(f"  {f_plan}")
    if detalle_h1 is not None: print(f"  {f_h1}")
    print(f"  {f_txt}")
    print(f"  {f_json}")


if __name__ == "__main__":
    main()
"""
Trabajo Integrador - Planta híbrida FV + Eólico + BESS
Migración del balance anual desde Excel a Python.

Esta versión reproduce la lógica actual acordada antes de optimizar:
- año bisiesto: 8784 h;
- SOC horario secuencial;
- SOC inicial = 100 % de la capacidad disponible del año;
- FV degradado año a año;
- BESS degradado linealmente por ciclos equivalentes;
- peak shaving obligatorio por potencia contratada/T1;
- carga con excedente renovable y posibilidad de carga desde red;
- despacho económico LP y planificación multianual opcionales;
- exportación de excedentes hasta el límite de T1, sin remuneración;
- CAPEX/OPEX/potencia contratada/energía de red a 20 años;
- evaluación automática de configuraciones;
- búsqueda por grilla sobre cuatro variables de diseño, con P contratada fija en 15 MW;
- restricción espacial del parque eólico para el polígono disponible;
- reporte explícito del BESS en MW / MWh / horas;
- CAPEX BESS separado en componente de energía y componente de potencia;
- filtro espacial de screening para FV + containers BESS dentro del terreno;
- pitch FV calculado por criterio geométrico de no sombreado (6,5 m), con GCR derivado automáticamente.

BASE V11:
- despacho económico anual con límite de ciclos;
- planificación multianual de degradación: calcula el SOH técnico mínimo de cada año,
  reserva los ciclos mínimos futuros y evita que el arbitraje temprano deje al BESS sin
  capacidad para cumplir la demanda en años posteriores.

BASE V12:
- P_FV y P_BESS son variables continuas; N_aeros y N_containers son enteras.
- Differential Evolution mixto: no usa valores discretos prefijados de potencia.
- SOC anual cíclico: SOC final = SOC inicial, evitando energía gratis cada 1 de enero.
- degradación BESS conservadora también dentro del último año del horizonte.
- modo de optimización liviano: no exporta ni conserva detalle horario de candidatos.
- screening espacial conjunto: eólico reserva área y FV+BESS deben caber en el residual.

NOVEDAD V13:
- enumera todas las familias discretas (N_aeros, N_containers) del dominio pedido;
- para CADA familia explora P_FV y P_BESS sobre el dominio continuo completo, sin rangos heredados de V12;
- cada familia factible recibe al menos una validación EXACTA de 20 años;
- las mejores familias se refinan con evaluaciones exactas adicionales, sin cambiar el dominio global;
- al encontrar el óptimo genera un análisis anual completo de degradación, compras de red, BESS y costos.

NO implementa todavía:
- reemplazo automático del BESS al llegar a EOL;
- layout geométrico conjunto exacto FV + aerogeneradores + BESS dentro del KMZ.

IMPORTANTE SOBRE ESPACIO:
Para el predimensionamiento FV se adopta pitch entre filas = 6,5 m para tracker 1P N-S,
correspondiente al criterio acordado de evitar sombreado entre filas entre 9:00 y 15:00
hora solar en el solsticio de invierno. Con ancho rotante 2,384 m, el GCR se deriva como
GCR = 2,384 / pitch ≈ 0,367. El pitch puede modificarse con --pitch-fv-m.
El filtro FV+BESS es un screening; la comprobación final debe hacerse con layout georreferenciado.

Instalación:
    pip install pandas numpy openpyxl

Uso básico:
    python migracion_balance_anual_v13_familias_optimo_detallado.py --excel Balance_anual-v3.xlsm

Simulación de 20 años:
    python migracion_balance_anual_v13_familias_optimo_detallado.py --excel Balance_anual-v3.xlsm --simular-20

Si se omite --excel, busca automáticamente un archivo Balance_anual-v3*.xlsm/.xlsx
en la carpeta del script, la carpeta actual o ~/Documents/Facultad/Taller integrador.
"""


import argparse
import math
import re
import unicodedata
import warnings
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal
from itertools import product
import time
import sys
import json
import subprocess
import tempfile

import numpy as np
import pandas as pd
from scipy.optimize import linprog, differential_evolution, minimize
from scipy.sparse import coo_matrix


# =============================================================================
# CONSTANTES
# =============================================================================

HORAS_ANIO = 8784
DT_H = 1.0

# Red / pliego
LIMITE_T1_MW = 15.0
P_CONTRATADA_MIN_MW = 6.0
P_CONTRATADA_MAX_MW = 15.0
P_CONTRATADA_FIJA_MW = 15.0  # recomendación docente: potencia contratada fija
COSTO_PC_USD_MW_MES = 4_500.0
ESCALAMIENTO_COSTOS = 0.025
WACC = 0.08

# BESS
ETA_CARGA_DEFAULT = 0.95
ETA_DESCARGA_DEFAULT = 0.95
SOC_MIN_DEFAULT = 0.10
SOC_MAX_DEFAULT = 1.00
SOC_INICIAL_DEFAULT = 1.00
SOH_EOL = 0.70
DOD_CICLO_REFERENCIA = 0.90
DEGRADACION_POR_CICLO_EQ = 0.000025  # 0,0025 puntos porcentuales/ciclo
P_RATE_MAX = 0.50                    # 0,5 C: P_BESS <= 0,5 * E_BESS
E_CONTAINER_MWH_DEFAULT = 5.015

# Aerogeneradores
P_NOMINAL_AERO_MW = {
    "GE3.4": 3.43,
    "GE3.8": 3.83,
}

# Restricción espacial derivada del KMZ del proyecto.
# Ambos aerogeneradores tienen rotor D = 130 m. Se adopta, de manera
# provisional, un espaciamiento mínimo centro-centro de 5D = 650 m.
# Para el polígono disponible (~0,804 km²; envolvente ~1,68 x 0,75 km),
# el máximo hallado que cumple 5D es 5 aerogeneradores.
# Esta restricción NO agrega pérdidas de estela: esas pérdidas ya están
# incorporadas en el perfil energético utilizado.
ROTOR_DIAMETRO_M = 130.0
DISTANCIA_MIN_AEROS_D = 5.0
DISTANCIA_MIN_AEROS_M = ROTOR_DIAMETRO_M * DISTANCIA_MIN_AEROS_D
AREA_DISPONIBLE_KM2 = 0.8041640744
AREA_DISPONIBLE_M2 = AREA_DISPONIBLE_KM2 * 1_000_000.0
N_AEROS_MAX_ESPACIO = 5

# Screening de ocupación eólica para responder cuánto terreno queda disponible
# para FV+BESS. Se reserva, de forma conservadora y explícita, el disco de radio
# D/2 alrededor de cada torre (área equivalente al rotor). La separación 5D entre
# centros se verifica aparte. Esto NO reemplaza el layout georreferenciado final.
AREA_RESERVADA_EOLICA_POR_AERO_M2 = math.pi * (ROTOR_DIAMETRO_M / 2.0) ** 2

# FV / ocupación de terreno.
# Trina Vertex NEG21C.20 y Jinko 66HL5-BDV: 2384 x 1303 mm.
# Para el screening se usa 700 W por defecto (conservador en superficie).
# Tracker supuesto: 1P, eje N-S. El ancho que rota perpendicular al eje es 2,384 m.
# Criterio de predimensionamiento acordado: pitch = 6,5 m, obtenido para evitar
# sombreado entre filas entre 9:00 y 15:00 hora solar en el solsticio de invierno.
# Por lo tanto, GCR = ancho_rotante / pitch.
MODULO_FV_LARGO_M = 2.384
MODULO_FV_ANCHO_M = 1.303
ANCHO_ROTANTE_TRACKER_1P_M = MODULO_FV_LARGO_M
PITCH_FV_DEFAULT_M = 6.5
POTENCIA_MODULO_FV_W_DEFAULT = 700.0

# BESS Gotion GRID5015: 6058 x 2438 mm.
# Screening conservador: 4 m entre containers en ambas direcciones.
BESS_CONTAINER_LARGO_M = 6.058
BESS_CONTAINER_ANCHO_M = 2.438
BESS_SEPARACION_SCREENING_M = 4.0

# CAPEX
CAPEX_FV_USD_MW = 614_000.0
CAPEX_EOL_USD_MW = 950_000.0
CAPEX_BESS_ENERGIA_USD_MWH = 190_000.0
CAPEX_BESS_POTENCIA_USD_MW = 239_000.0
CAPEX_FIJO_USD = 400_000.0

# OPEX: criterio adoptado en el Excel
OPEX_FV_PCT = 0.012
OPEX_EOL_PCT = 0.022
OPEX_BESS_PCT = 0.017


# =============================================================================
# ESTRUCTURAS
# =============================================================================

@dataclass(frozen=True)
class Configuracion:
    n_aeros: int
    p_fv_mw: float
    p_contratada_mw: float
    limite_t1_mw: float
    p_bess_mw: float
    e_bess_mwh: float
    eta_carga: float
    eta_descarga: float
    soc_min: float
    soc_max: float
    soc_inicial_frac: float
    n_containers: int
    e_container_mwh: float


@dataclass(frozen=True)
class Capex:
    fv_usd: float
    eolico_usd: float
    bess_usd: float
    fijo_usd: float
    total_usd: float


# =============================================================================
# UTILIDADES
# =============================================================================

def factor_degradacion_fv(anio: int) -> float:
    """Año 1 = 0,990; luego disminuye 0,004 por año hasta año 20 = 0,914."""
    if not 1 <= anio <= 20:
        raise ValueError("El año debe estar entre 1 y 20.")
    return 0.99 - 0.004 * (anio - 1)


def calcular_metricas_bess_diseno(
    p_bess_mw: float,
    n_containers: int,
    e_container_mwh: float = E_CONTAINER_MWH_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
) -> dict:
    """Potencia, energía, horas y CAPEX BESS con P y E tratadas por separado."""
    if n_containers < 0 or int(n_containers) != n_containers:
        raise ValueError("n_containers debe ser un entero >= 0.")
    if p_bess_mw < 0:
        raise ValueError("P_BESS debe ser >= 0.")
    e_bess_mwh = float(n_containers) * float(e_container_mwh)
    if n_containers == 0:
        if p_bess_mw > 1e-12:
            raise ValueError("No puede haber P_BESS > 0 sin containers/energía.")
        horas_nominales = 0.0
        horas_utiles_bol = 0.0
    else:
        if p_bess_mw <= 1e-12:
            raise ValueError("No tiene sentido instalar containers BESS con P_BESS = 0.")
        if p_bess_mw > P_RATE_MAX * e_bess_mwh + 1e-9:
            raise ValueError("P_BESS supera el máximo 0,5P del BESS.")
        horas_nominales = e_bess_mwh / p_bess_mw
        horas_utiles_bol = e_bess_mwh * (soc_max - soc_min) / p_bess_mw
    capex_energia = e_bess_mwh * CAPEX_BESS_ENERGIA_USD_MWH
    capex_potencia = p_bess_mw * CAPEX_BESS_POTENCIA_USD_MW
    return {
        "n_containers": int(n_containers),
        "e_bess_mwh": float(e_bess_mwh),
        "p_bess_mw": float(p_bess_mw),
        "horas_nominales": float(horas_nominales),
        "horas_utiles_bol": float(horas_utiles_bol),
        "capex_bess_energia_usd": float(capex_energia),
        "capex_bess_potencia_usd": float(capex_potencia),
        "capex_bess_total_usd": float(capex_energia + capex_potencia),
    }


def calcular_area_bess_screening(n_containers: int) -> dict:
    """Grilla compacta de containers, usando 4 m de separación en ambos ejes."""
    if n_containers < 0 or int(n_containers) != n_containers:
        raise ValueError("n_containers debe ser un entero >= 0.")
    n_containers = int(n_containers)
    if n_containers == 0:
        return {"area_bess_m2": 0.0, "area_bess_huella_pura_m2": 0.0,
                "bess_filas": 0, "bess_columnas": 0}
    huella_pura = n_containers * BESS_CONTAINER_LARGO_M * BESS_CONTAINER_ANCHO_M
    mejor = None
    for filas in range(1, n_containers + 1):
        columnas = math.ceil(n_containers / filas)
        largo = columnas * BESS_CONTAINER_LARGO_M + (columnas - 1) * BESS_SEPARACION_SCREENING_M
        ancho = filas * BESS_CONTAINER_ANCHO_M + (filas - 1) * BESS_SEPARACION_SCREENING_M
        candidato = (largo * ancho, filas, columnas)
        if mejor is None or candidato[0] < mejor[0]:
            mejor = candidato
    area, filas, columnas = mejor
    return {"area_bess_m2": float(area), "area_bess_huella_pura_m2": float(huella_pura),
            "bess_filas": int(filas), "bess_columnas": int(columnas)}


def calcular_area_fv_screening(
    p_fv_mw: float,
    *,
    potencia_modulo_w: float,
    pitch_fv_m: float = PITCH_FV_DEFAULT_M,
) -> dict:
    """
    Screening de superficie FV para tracker 1P N-S.

    GCR = ancho_rotante / pitch
    A_FV = A_módulos / GCR

    El pitch por defecto (6,5 m) es el criterio geométrico acordado de
    predimensionamiento para evitar sombreado entre filas entre 9:00 y 15:00
    hora solar en el solsticio de invierno.
    """
    if p_fv_mw < 0 or potencia_modulo_w <= 0:
        raise ValueError("P_FV debe ser >=0 y potencia del módulo >0.")
    if pitch_fv_m <= ANCHO_ROTANTE_TRACKER_1P_M:
        raise ValueError(
            f"pitch_fv_m debe ser mayor que el ancho rotante ({ANCHO_ROTANTE_TRACKER_1P_M:.3f} m)."
        )
    gcr_fv = ANCHO_ROTANTE_TRACKER_1P_M / pitch_fv_m
    n_modulos = 0 if p_fv_mw <= 1e-12 else math.ceil(p_fv_mw * 1_000_000.0 / potencia_modulo_w)
    area_modulo = MODULO_FV_LARGO_M * MODULO_FV_ANCHO_M
    area_modulos = n_modulos * area_modulo
    area_terreno = area_modulos / gcr_fv if n_modulos else 0.0
    return {
        "n_modulos_fv": int(n_modulos),
        "potencia_fv_real_por_modulos_mwp": float(n_modulos * potencia_modulo_w / 1_000_000.0),
        "pitch_fv_m": float(pitch_fv_m),
        "gcr_fv": float(gcr_fv),
        "area_modulos_fv_m2": float(area_modulos),
        "area_fv_terreno_m2": float(area_terreno),
    }


def calcular_screening_espacial(*, p_fv_mw: float, n_aeros: int, n_containers: int,
                                 potencia_modulo_w: float, pitch_fv_m: float = PITCH_FV_DEFAULT_M) -> dict:
    """
    Screening espacial V12.

    1) exige n_aeros <= 5 y mantiene la separación mínima 5D como restricción de layout;
    2) reserva dentro del predio un área equivalente al disco de radio D/2 por aerogenerador;
    3) FV+BESS deben caber en el área residual.

    La reserva eólica es deliberadamente un screening: no representa caminos, fundaciones
    ni micrositing final, pero evita reportar erróneamente que FV+BESS disponen del 100 %
    del terreno cuando hay aerogeneradores instalados.
    """
    fv = calcular_area_fv_screening(
        p_fv_mw, potencia_modulo_w=potencia_modulo_w, pitch_fv_m=pitch_fv_m
    )
    bess = calcular_area_bess_screening(n_containers)
    area_fv_bess = fv["area_fv_terreno_m2"] + bess["area_bess_m2"]
    area_eolica_reservada = int(n_aeros) * AREA_RESERVADA_EOLICA_POR_AERO_M2
    area_residual = max(0.0, AREA_DISPONIBLE_M2 - area_eolica_reservada)
    area_total_screening = area_fv_bess + area_eolica_reservada

    cumple_aeros = 0 <= int(n_aeros) <= N_AEROS_MAX_ESPACIO
    cumple_area = area_fv_bess <= area_residual + 1e-9
    return {
        **fv, **bess,
        "area_eolica_reservada_m2": float(area_eolica_reservada),
        "area_residual_tras_eolica_m2": float(area_residual),
        "area_fv_mas_bess_m2": float(area_fv_bess),
        "area_total_screening_m2": float(area_total_screening),
        "uso_area_fv_bess_pct": float(100.0 * area_fv_bess / AREA_DISPONIBLE_M2),
        "uso_area_eolica_pct": float(100.0 * area_eolica_reservada / AREA_DISPONIBLE_M2),
        "uso_area_total_screening_pct": float(100.0 * area_total_screening / AREA_DISPONIBLE_M2),
        "cumple_espacio_aeros": bool(cumple_aeros),
        "cumple_area_fv_bess": bool(cumple_area),
        "cumple_screening_espacial": bool(cumple_aeros and cumple_area),
    }


def _normalizar_texto(x: object) -> str:
    s = unicodedata.normalize("NFKD", str(x))
    s = "".join(c for c in s if not unicodedata.combining(c))
    s = s.casefold()
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return " ".join(s.split())


def _buscar_columna(df: pd.DataFrame, *terminos: str) -> str:
    """
    Busca una columna que contenga todos los términos indicados como TOKENS,
    ignorando mayúsculas, acentos, saltos de línea y signos.

    Importante: se compara por palabras completas y no por subcadenas.
    Así, por ejemplo, "carga" NO coincide con "descarga".
    """
    tokens_objetivo: set[str] = set()
    for termino in terminos:
        tokens_objetivo.update(_normalizar_texto(termino).split())

    coincidencias: list[str] = []

    for c in df.columns:
        tokens_columna = set(_normalizar_texto(c).split())
        if tokens_objetivo.issubset(tokens_columna):
            coincidencias.append(c)

    if not coincidencias:
        raise KeyError(
            f"No encontré una columna con los términos {terminos}.\n"
            f"Columnas disponibles:\n{list(df.columns)}"
        )
    if len(coincidencias) > 1:
        raise KeyError(
            f"La búsqueda {terminos} es ambigua. Coincidencias: {coincidencias}"
        )
    return coincidencias[0]


def _valor_fila(r: pd.Series, *terminos: str) -> float:
    df_aux = pd.DataFrame(columns=r.index)
    col = _buscar_columna(df_aux, *terminos)
    return float(r[col])


def _valor_fila_exacta(r: pd.Series, nombre_columna: str) -> float:
    """
    Busca primero una columna por nombre normalizado EXACTO.

    Sirve para distinguir, por ejemplo:
      - "Capacidad BESS [MWh]" (capacidad nominal instalada)
      - "Capacidad BESS disponible [MWh]" (capacidad degradada del año)
    """
    objetivo = _normalizar_texto(nombre_columna)
    coincidencias = [c for c in r.index if _normalizar_texto(c) == objetivo]

    if len(coincidencias) == 1:
        return float(r[coincidencias[0]])
    if len(coincidencias) > 1:
        raise KeyError(
            f"Hay más de una columna equivalente a {nombre_columna!r}: {coincidencias}"
        )
    raise KeyError(
        f"No encontré la columna exacta {nombre_columna!r}.\n"
        f"Columnas disponibles:\n{list(r.index)}"
    )


def validar_configuracion(cfg: Configuracion) -> None:
    if cfg.n_aeros < 0 or int(cfg.n_aeros) != cfg.n_aeros:
        raise ValueError("n_aeros debe ser un entero >= 0.")
    if cfg.p_fv_mw < 0:
        raise ValueError("P_FV no puede ser negativa.")

    if not (P_CONTRATADA_MIN_MW <= cfg.p_contratada_mw <= P_CONTRATADA_MAX_MW):
        raise ValueError(
            f"P_contratada debe quedar entre {P_CONTRATADA_MIN_MW:g} y "
            f"{P_CONTRATADA_MAX_MW:g} MW."
        )
    if cfg.p_contratada_mw > cfg.limite_t1_mw + 1e-9:
        raise ValueError("P_contratada no puede superar el límite de T1.")
    if cfg.limite_t1_mw > LIMITE_T1_MW + 1e-9:
        raise ValueError(f"El límite de T1 no puede superar {LIMITE_T1_MW:g} MW.")

    if cfg.p_bess_mw < 0 or cfg.e_bess_mwh < 0:
        raise ValueError("P_BESS y E_BESS deben ser >= 0.")
    if cfg.e_bess_mwh == 0 and cfg.p_bess_mw > 0:
        raise ValueError("No puede existir P_BESS > 0 con E_BESS = 0.")
    if cfg.e_bess_mwh > 0 and cfg.p_bess_mw > P_RATE_MAX * cfg.e_bess_mwh + 1e-9:
        raise ValueError(
            f"P_BESS={cfg.p_bess_mw:.6f} MW supera el máximo 0,5C para "
            f"E_BESS={cfg.e_bess_mwh:.6f} MWh "
            f"(máximo {P_RATE_MAX * cfg.e_bess_mwh:.6f} MW)."
        )

    if not (0 < cfg.eta_carga <= 1 and 0 < cfg.eta_descarga <= 1):
        raise ValueError("Los rendimientos deben quedar en (0,1].")
    if not (0 <= cfg.soc_min < cfg.soc_max <= 1):
        raise ValueError("Debe cumplirse 0 <= SOC_min < SOC_max <= 1.")
    if not (cfg.soc_min <= cfg.soc_inicial_frac <= cfg.soc_max):
        raise ValueError("SOC inicial debe estar entre SOC_min y SOC_max.")

    if cfg.n_containers > 0:
        e_cont = cfg.n_containers * cfg.e_container_mwh
        if not math.isclose(cfg.e_bess_mwh, e_cont, rel_tol=0, abs_tol=1e-6):
            warnings.warn(
                "E_BESS no coincide exactamente con n_containers * energía/container. "
                f"E_BESS={cfg.e_bess_mwh:.6f} MWh; containers={e_cont:.6f} MWh.",
                RuntimeWarning,
            )

    if not math.isclose(cfg.p_contratada_mw, round(cfg.p_contratada_mw), abs_tol=1e-9):
        warnings.warn(
            "El pliego presenta escalones enteros de potencia contratada (6..15 MW). "
            "El simulador admite un valor continuo, pero en la optimización final "
            "conviene tratarlo como variable discreta.",
            RuntimeWarning,
        )


def buscar_excel_por_defecto() -> Path:
    """Busca automáticamente el Excel del proyecto en ubicaciones habituales.

    Orden de búsqueda:
    1) carpeta del script;
    2) carpeta desde la que se ejecuta Python;
    3) ~/Documents/Facultad/Taller integrador.

    Si hay más de un Balance_anual-v3* en una misma ubicación, pide --excel
    para evitar elegir silenciosamente el archivo equivocado.
    """
    carpetas = [
        Path(__file__).resolve().parent,
        Path.cwd(),
        Path.home() / "Documents" / "Facultad" / "Taller integrador",
    ]

    # Eliminar duplicados conservando el orden.
    carpetas_unicas = []
    for carpeta in carpetas:
        carpeta = carpeta.resolve()
        if carpeta not in carpetas_unicas:
            carpetas_unicas.append(carpeta)

    for carpeta in carpetas_unicas:
        if not carpeta.exists():
            continue

        exactos = [
            carpeta / "Balance_anual-v3.xlsm",
            carpeta / "Balance_anual-v3.xlsx",
        ]
        for p in exactos:
            if p.exists():
                return p

        encontrados = sorted(
            p for p in carpeta.glob("Balance_anual-v3*")
            if p.suffix.lower() in {".xlsm", ".xlsx"}
        )
        if len(encontrados) == 1:
            return encontrados[0]
        if len(encontrados) > 1:
            raise FileNotFoundError(
                f"Encontré varios Excel Balance_anual-v3* en {carpeta}. "
                "Usá --excel para indicar cuál:\n  "
                + "\n  ".join(str(p) for p in encontrados)
            )

    lugares = "\n  ".join(str(p) for p in carpetas_unicas)
    raise FileNotFoundError(
        "No encontré Balance_anual-v3*.xlsm/.xlsx automáticamente. "
        "Busqué en:\n  " + lugares +
        "\nUsá --excel RUTA_AL_ARCHIVO para indicarlo explícitamente."
    )


# =============================================================================
# LECTURA DEL EXCEL
# =============================================================================

def leer_configuracion_excel(ruta_excel: str | Path) -> Configuracion:
    """Lee la fila de parámetros actualmente guardada en la hoja 'Parametros'."""
    df = pd.read_excel(ruta_excel, sheet_name="Parametros", nrows=1)
    if df.empty:
        raise ValueError("La hoja 'Parametros' no contiene la fila esperada.")
    r = df.iloc[0]

    # En Parametros usamos nombres exactos normalizados. Es más seguro que
    # búsquedas parciales porque la hoja contiene pares como carga/descarga y
    # capacidad nominal/capacidad disponible.
    cfg = Configuracion(
        n_aeros=int(_valor_fila_exacta(r, "Cantidad aerogeneradores GE")),
        p_fv_mw=_valor_fila_exacta(r, "Potencia FV instalada [MW]"),
        p_contratada_mw=_valor_fila_exacta(r, "P contratada de la red [MW]"),
        limite_t1_mw=_valor_fila_exacta(r, "Límite T1 [MW]"),
        p_bess_mw=_valor_fila_exacta(r, "Potencia BESS [MW]"),
        # Capacidad NOMINAL instalada. No usar "Capacidad BESS disponible".
        e_bess_mwh=_valor_fila_exacta(r, "Capacidad BESS [MWh]"),
        eta_carga=_valor_fila_exacta(r, "Rendimiento carga"),
        eta_descarga=_valor_fila_exacta(r, "Rendimiento descarga"),
        soc_min=_valor_fila_exacta(r, "SOC mínimo"),
        soc_max=_valor_fila_exacta(r, "SOC máximo"),
        soc_inicial_frac=_valor_fila_exacta(r, "SOC inicial"),
        n_containers=int(_valor_fila_exacta(r, "Cantidad containers BESS")),
        e_container_mwh=_valor_fila_exacta(r, "Energía/container [MWh]"),
    )
    validar_configuracion(cfg)
    return cfg


def cargar_perfiles(ruta_excel: str | Path, p_fv_referencia_mw: float) -> pd.DataFrame:
    """
    Reutiliza perfiles ya calculados/validados en el Excel.

    Demanda:
      Las 24 filas de la hoja 'Demanda' se interpretan por ORDEN:
      fila 1 -> hora 00:00, ..., fila 24 -> hora 23:00.
      Esto reproduce el Balance anual, aunque la columna original esté rotulada 1..24.

    FV:
      Usa 'P módulo final [W]' antes del límite de 15 MW y lo normaliza con la
      potencia FV de referencia del Excel. Luego, al simular, se escala por P_FV,
      se limita a 15 MW y finalmente se aplica degradación anual.

    Eólico:
      Usa potencia horaria por aerogenerador para GE 3.4 y GE 3.8.

    Los años de las fuentes no se cruzan por fecha: se conserva el orden de las
    8784 horas tal como se hizo en el Excel.
    """
    if p_fv_referencia_mw <= 0:
        raise ValueError("La potencia FV de referencia debe ser > 0.")

    demanda = pd.read_excel(ruta_excel, sheet_name="Demanda", nrows=24)
    solar = pd.read_excel(ruta_excel, sheet_name="solar", header=1, nrows=HORAS_ANIO)
    eolico = pd.read_excel(ruta_excel, sheet_name="Eolico 2008", nrows=HORAS_ANIO)

    if len(demanda) < 24:
        raise ValueError(f"Demanda tiene {len(demanda)} filas; se esperaban 24.")
    demanda = demanda.iloc[:24].copy()
    if len(solar) != HORAS_ANIO:
        raise ValueError(f"solar tiene {len(solar)} filas; se esperaban {HORAS_ANIO}.")
    if len(eolico) != HORAS_ANIO:
        raise ValueError(f"Eolico 2008 tiene {len(eolico)} filas; se esperaban {HORAS_ANIO}.")

    col_dem_ver = _buscar_columna(demanda, "demanda", "verano")
    col_dem_inv = _buscar_columna(demanda, "demanda", "invierno")
    col_banda = _buscar_columna(demanda, "banda", "horaria")
    col_precio = _buscar_columna(demanda, "precio", "red")

    col_solar_final = _buscar_columna(solar, "p", "modulo", "final")
    col_eol_34 = _buscar_columna(eolico, "p", "ge", "3 4", "aerogenerador")
    col_eol_38 = _buscar_columna(eolico, "p", "ge", "3 8", "aerogenerador")

    fechas = pd.date_range("2020-01-01 00:00:00", periods=HORAS_ANIO, freq="h")
    horas = fechas.hour.to_numpy(dtype=int)

    dem_ver_24 = pd.to_numeric(demanda[col_dem_ver], errors="raise").to_numpy(dtype=float)
    dem_inv_24 = pd.to_numeric(demanda[col_dem_inv], errors="raise").to_numpy(dtype=float)
    banda_24 = demanda[col_banda].astype(str).str.strip().to_numpy(dtype=object)
    precio_24 = pd.to_numeric(demanda[col_precio], errors="raise").to_numpy(dtype=float)

    # El Excel considera Verano de noviembre a abril e Invierno de mayo a octubre.
    es_verano = (fechas.month >= 11) | (fechas.month <= 4)
    demanda_mw = np.where(es_verano, dem_ver_24[horas], dem_inv_24[horas])
    banda = banda_24[horas]
    tarifa_base = precio_24[horas]

    solar_final_w = pd.to_numeric(solar[col_solar_final], errors="raise").to_numpy(dtype=float)
    fv_pu_sin_limite = solar_final_w / (p_fv_referencia_mw * 1e6)

    e34 = pd.to_numeric(eolico[col_eol_34], errors="raise").to_numpy(dtype=float) / 1000.0
    e38 = pd.to_numeric(eolico[col_eol_38], errors="raise").to_numpy(dtype=float) / 1000.0

    for nombre, arr in {
        "demanda_mw": demanda_mw,
        "tarifa_base": tarifa_base,
        "fv_pu_sin_limite": fv_pu_sin_limite,
        "eolico_34": e34,
        "eolico_38": e38,
    }.items():
        if len(arr) != HORAS_ANIO or not np.isfinite(arr).all():
            raise ValueError(f"El perfil {nombre} tiene NaN/inf o longitud incorrecta.")

    bandas_validas = {"Valle", "Resto", "Pico"}
    bandas_encontradas = set(map(str, banda))
    if not bandas_encontradas.issubset(bandas_validas):
        raise ValueError(f"Bandas no reconocidas en Demanda: {bandas_encontradas}")

    return pd.DataFrame(
        {
            "fecha_hora": fechas,
            "hora": horas,
            "estacion": np.where(es_verano, "Verano", "Invierno"),
            "demanda_mw": demanda_mw,
            "banda": banda,
            "tarifa_base_usd_mwh": tarifa_base,
            "fv_pu_sin_limite": fv_pu_sin_limite,
            "eolico_34_por_aero_mw": e34,
            "eolico_38_por_aero_mw": e38,
        }
    )


# =============================================================================
# SIMULACIÓN HORARIA
# =============================================================================

def simular_anio(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    p_contratada_mw: float,
    anio: int,
    soh_inicial: float,
    ciclos_acum_inicial: float = 0.0,
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    exportar_excedente: bool = True,
    escalamiento_costos: float = ESCALAMIENTO_COSTOS,
) -> tuple[pd.DataFrame, dict]:
    """
    Simula las 8784 horas de un año.

    Estrategia actual, ANTES de optimizar el despacho económico:
      1) FV + eólico abastecen demanda.
      2) Excedente renovable carga BESS.
      3) Si déficit > P_contratada/T1, BESS descarga obligatoriamente.
      4) La red cubre el déficit remanente hasta el límite contratado.
      5) En Valle, la red puede cargar BESS usando el margen contratado disponible.
      6) Descarga económica adicional = 0.
      7) Excedente remanente se exporta hasta 15 MW; lo que supere T1 se recorta.

    SOC:
      SOC_inicio(h) = SOC_fin(h-1), siempre secuencial.
      Al comienzo de cada año, SOC = soc_inicial_frac de la capacidad disponible.
    """
    if len(perfiles) != HORAS_ANIO:
        raise ValueError(f"Se esperaban {HORAS_ANIO} horas.")
    if tipo_aero not in P_NOMINAL_AERO_MW:
        raise ValueError("tipo_aero debe ser 'GE3.4' o 'GE3.8'.")
    if not 1 <= anio <= 20:
        raise ValueError("anio debe estar entre 1 y 20.")
    if not (SOH_EOL <= soh_inicial <= 1.0):
        raise ValueError(f"SOH inicial debe estar entre {SOH_EOL:.2f} y 1,00.")
    if p_fv_mw < 0 or n_aeros < 0 or int(n_aeros) != n_aeros:
        raise ValueError("P_FV debe ser >= 0 y n_aeros un entero >= 0.")
    if p_bess_mw < 0 or e_bess_mwh < 0:
        raise ValueError("P_BESS y E_BESS deben ser >= 0.")
    if e_bess_mwh == 0 and p_bess_mw > 0:
        raise ValueError("P_BESS debe ser 0 si E_BESS es 0.")
    if e_bess_mwh > 0 and p_bess_mw > P_RATE_MAX * e_bess_mwh + 1e-9:
        raise ValueError("P_BESS supera el límite 0,5C del BESS.")
    if not (P_CONTRATADA_MIN_MW <= p_contratada_mw <= P_CONTRATADA_MAX_MW):
        raise ValueError("P_contratada debe estar entre 6 y 15 MW.")
    if p_contratada_mw > limite_t1_mw + 1e-9:
        raise ValueError("P_contratada no puede superar T1.")

    banda = perfiles["banda"].to_numpy(dtype=object)
    tarifa_base = perfiles["tarifa_base_usd_mwh"].to_numpy(dtype=float)
    tarifa_anio = tarifa_base * (1.0 + escalamiento_costos) ** (anio - 1)

    factor_fv = factor_degradacion_fv(anio)

    # Misma convención que el Excel: escala P_FV -> limita a 15 MW -> degrada.
    p_fv_sin_degradar = np.minimum(
        p_fv_mw * perfiles["fv_pu_sin_limite"].to_numpy(dtype=float),
        limite_t1_mw,
    )
    p_fv = p_fv_sin_degradar * factor_fv

    if tipo_aero == "GE3.4":
        p_eolico = n_aeros * perfiles["eolico_34_por_aero_mw"].to_numpy(dtype=float)
    else:
        p_eolico = n_aeros * perfiles["eolico_38_por_aero_mw"].to_numpy(dtype=float)

    demanda = perfiles["demanda_mw"].to_numpy(dtype=float)
    renovable = p_fv + p_eolico
    p_neta = demanda - renovable
    deficit = np.maximum(p_neta, 0.0)
    excedente = np.maximum(-p_neta, 0.0)

    p_red_max = min(p_contratada_mw, limite_t1_mw)

    capacidad_disponible = e_bess_mwh * soh_inicial
    e_soc_min = capacidad_disponible * soc_min
    e_soc_max = capacidad_disponible * soc_max
    soc0 = capacidad_disponible * soc_inicial_frac if e_bess_mwh > 0 else 0.0

    n = HORAS_ANIO
    soc_inicio_arr = np.zeros(n)
    carga_ren_arr = np.zeros(n)
    descarga_obl_arr = np.zeros(n)
    carga_red_arr = np.zeros(n)
    descarga_econ_arr = np.zeros(n)  # se activa en una etapa posterior
    soc_fin_arr = np.zeros(n)
    red_consumo_arr = np.zeros(n)
    red_import_arr = np.zeros(n)
    export_arr = np.zeros(n)
    curtail_arr = np.zeros(n)
    no_abast_arr = np.zeros(n)
    costo_arr = np.zeros(n)
    p_t1_arr = np.zeros(n)
    error_balance_arr = np.zeros(n)

    soc_anterior = soc0

    for h in range(n):
        soc_ini = soc_anterior
        soc_inicio_arr[h] = soc_ini

        # 1) CARGA DESDE RENOVABLE
        if e_bess_mwh > 0 and p_bess_mw > 0:
            margen_soc_carga = max(0.0, (e_soc_max - soc_ini) / (eta_carga * DT_H))
            carga_ren = min(excedente[h], p_bess_mw, margen_soc_carga)
        else:
            carga_ren = 0.0

        soc_1 = soc_ini + carga_ren * eta_carga * DT_H

        # 2) DESCARGA OBLIGATORIA PARA PEAK SHAVING
        descarga_necesaria = max(deficit[h] - p_red_max, 0.0)
        if e_bess_mwh > 0 and p_bess_mw > 0:
            max_descarga_soc = max(0.0, (soc_1 - e_soc_min) * eta_descarga / DT_H)
            descarga_obl = min(descarga_necesaria, p_bess_mw, max_descarga_soc)
        else:
            descarga_obl = 0.0

        soc_2 = soc_1 - descarga_obl / eta_descarga * DT_H

        # 3) RED PARA CONSUMO
        red_consumo = min(max(deficit[h] - descarga_obl, 0.0), p_red_max)

        # 4) CARGA DESDE RED EN VALLE
        carga_red = 0.0
        if banda[h] == "Valle" and e_bess_mwh > 0 and p_bess_mw > 0:
            margen_p_bess = max(0.0, p_bess_mw - carga_ren)
            margen_red = max(0.0, p_red_max - red_consumo)
            margen_soc = max(0.0, (e_soc_max - soc_2) / (eta_carga * DT_H))
            carga_red = min(margen_p_bess, margen_red, margen_soc)

        # 5) DESCARGA ECONÓMICA ADICIONAL: todavía apagada
        descarga_econ = 0.0

        soc_fin = (
            soc_2
            + carga_red * eta_carga * DT_H
            - descarga_econ / eta_descarga * DT_H
        )

        # 6) RED, EXPORTACIÓN Y VERTIDO/CURTAILMENT
        red_import = red_consumo + carga_red
        excedente_remanente = max(excedente[h] - carga_ren, 0.0)

        if exportar_excedente:
            export = min(excedente_remanente, limite_t1_mw)
            curtail = max(excedente_remanente - export, 0.0)
        else:
            export = 0.0
            curtail = excedente_remanente

        no_abast = max(deficit[h] - descarga_obl - descarga_econ - red_consumo, 0.0)
        p_t1 = red_import - export  # + importa / - exporta

        # El excedente exportado no genera ingresos; sólo se paga importación.
        costo = red_import * tarifa_anio[h] * DT_H

        # Balance completo incluyendo demanda no abastecida como déficit explícito.
        error_balance = (
            renovable[h]
            + descarga_obl
            + descarga_econ
            + red_import
            + no_abast
            - demanda[h]
            - carga_ren
            - carga_red
            - export
            - curtail
        )

        carga_ren_arr[h] = carga_ren
        descarga_obl_arr[h] = descarga_obl
        carga_red_arr[h] = carga_red
        descarga_econ_arr[h] = descarga_econ
        soc_fin_arr[h] = soc_fin
        red_consumo_arr[h] = red_consumo
        red_import_arr[h] = red_import
        export_arr[h] = export
        curtail_arr[h] = curtail
        no_abast_arr[h] = no_abast
        costo_arr[h] = costo
        p_t1_arr[h] = p_t1
        error_balance_arr[h] = error_balance

        soc_anterior = soc_fin

    # Chequeos físicos que deben cumplirse incluso si la configuración es inviable.
    tol = 1e-8
    if np.max(np.abs(error_balance_arr)) > tol:
        raise RuntimeError(
            f"El balance horario no cierra. Error máximo = "
            f"{np.max(np.abs(error_balance_arr)):.3e} MW."
        )
    if np.max(red_import_arr) > p_red_max + tol:
        raise RuntimeError("La importación de red superó P_contratada/T1.")
    if np.max(np.abs(p_t1_arr)) > limite_t1_mw + tol:
        raise RuntimeError("El flujo neto por T1 superó 15 MW.")
    if e_bess_mwh > 0:
        if np.min(soc_fin_arr) < e_soc_min - tol or np.max(soc_fin_arr) > e_soc_max + tol:
            raise RuntimeError("El SOC salió de sus límites.")
    if np.max(carga_ren_arr + carga_red_arr) > p_bess_mw + tol:
        raise RuntimeError("La potencia total de carga superó P_BESS.")
    if np.max(descarga_obl_arr + descarga_econ_arr) > p_bess_mw + tol:
        raise RuntimeError("La potencia total de descarga superó P_BESS.")

    # Ciclos equivalentes
    energia_desc_terminal = float((descarga_obl_arr + descarga_econ_arr).sum() * DT_H)
    if e_bess_mwh > 0:
        energia_desc_interna = energia_desc_terminal / eta_descarga
        ciclos_eq = energia_desc_interna / (DOD_CICLO_REFERENCIA * e_bess_mwh)
    else:
        energia_desc_interna = 0.0
        ciclos_eq = 0.0

    ciclos_acum_final = ciclos_acum_inicial + ciclos_eq
    soh_teorico_final = 1.0 - DEGRADACION_POR_CICLO_EQ * ciclos_acum_final
    soh_final = max(SOH_EOL, soh_teorico_final)
    capacidad_final = e_bess_mwh * soh_final

    resultado = pd.DataFrame(
        {
            "Fecha/hora": perfiles["fecha_hora"].to_numpy(),
            "Hora": perfiles["hora"].to_numpy(),
            "Estación": perfiles["estacion"].to_numpy(),
            "Banda": banda,
            "Tarifa base [USD/MWh]": tarifa_base,
            "Tarifa año [USD/MWh]": tarifa_anio,
            "Demanda [MW]": demanda,
            "FV [MW]": p_fv,
            "Eólico [MW]": p_eolico,
            "Renovable [MW]": renovable,
            "P neta [MW]": p_neta,
            "Déficit [MW]": deficit,
            "Excedente renovable [MW]": excedente,
            "SOC inicio [MWh]": soc_inicio_arr,
            "Carga desde renovable [MW]": carga_ren_arr,
            "Descarga obligatoria [MW]": descarga_obl_arr,
            "Carga desde red en Valle [MW]": carga_red_arr,
            "Descarga económica [MW]": descarga_econ_arr,
            "SOC fin [MWh]": soc_fin_arr,
            "P red para consumo [MW]": red_consumo_arr,
            "P red importada total [MW]": red_import_arr,
            "P exportada [MW]": export_arr,
            "Curtailment / vertido [MW]": curtail_arr,
            "P T1 neta (+import/-export) [MW]": p_t1_arr,
            "Demanda no abastecida [MW]": no_abast_arr,
            "Costo red horario [USD]": costo_arr,
            "Error balance [MW]": error_balance_arr,
        }
    )

    energia_red_banda: dict[str, float] = {}
    costo_red_banda: dict[str, float] = {}
    for b in ("Valle", "Resto", "Pico"):
        mask = banda == b
        energia_red_banda[b] = float(red_import_arr[mask].sum() * DT_H)
        costo_red_banda[b] = float(costo_arr[mask].sum())

    resumen = {
        "anio": anio,
        "factor_fv": factor_fv,
        "soh_inicial": soh_inicial,
        "soh_final": soh_final,
        "eol_alcanzado": bool(soh_teorico_final <= SOH_EOL),
        "capacidad_bess_inicio_mwh": capacidad_disponible,
        "capacidad_bess_final_mwh": capacidad_final,
        "soc_inicial_mwh": soc0,
        "soc_final_mwh": float(soc_fin_arr[-1]),
        "soc_minimo_observado_mwh": float(soc_fin_arr.min()),
        "soc_maximo_observado_mwh": float(soc_fin_arr.max()),
        "energia_demanda_mwh": float(demanda.sum() * DT_H),
        "energia_fv_mwh": float(p_fv.sum() * DT_H),
        "energia_eolica_mwh": float(p_eolico.sum() * DT_H),
        "energia_red_total_mwh": float(red_import_arr.sum() * DT_H),
        "energia_red_valle_mwh": energia_red_banda["Valle"],
        "energia_red_resto_mwh": energia_red_banda["Resto"],
        "energia_red_pico_mwh": energia_red_banda["Pico"],
        "carga_renovable_mwh": float(carga_ren_arr.sum() * DT_H),
        "carga_red_valle_mwh": float(carga_red_arr.sum() * DT_H),
        "descarga_obligatoria_mwh": float(descarga_obl_arr.sum() * DT_H),
        "descarga_economica_mwh": float(descarga_econ_arr.sum() * DT_H),
        "energia_exportada_mwh": float(export_arr.sum() * DT_H),
        "curtailment_mwh": float(curtail_arr.sum() * DT_H),
        "demanda_no_abastecida_mwh": float(no_abast_arr.sum() * DT_H),
        "horas_no_cumple": int(np.count_nonzero(no_abast_arr > 1e-9)),
        "max_deficit_no_abastecido_mw": float(no_abast_arr.max()),
        "cumple_demanda": bool(np.max(no_abast_arr) <= 1e-9),
        "max_importacion_red_mw": float(red_import_arr.max()),
        "max_abs_flujo_t1_mw": float(np.max(np.abs(p_t1_arr))),
        "energia_descargada_interna_mwh": energia_desc_interna,
        "ciclos_equivalentes": float(ciclos_eq),
        "ciclos_acumulados_final": float(ciclos_acum_final),
        "costo_valle_usd": costo_red_banda["Valle"],
        "costo_resto_usd": costo_red_banda["Resto"],
        "costo_pico_usd": costo_red_banda["Pico"],
        "costo_red_total_usd": float(costo_arr.sum()),
        "max_error_balance_mw": float(np.max(np.abs(error_balance_arr))),
    }

    return resultado, resumen

def simular_anio_economico(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    p_contratada_mw: float,
    anio: int,
    soh_inicial: float,
    ciclos_acum_inicial: float = 0.0,
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    exportar_excedente: bool = True,
    escalamiento_costos: float = ESCALAMIENTO_COSTOS,
    exigir_soc_final_igual_inicial: bool = False,
    max_ciclos_anio: float | None = None,
    objetivo_lp: Literal["costo", "min_descarga"] = "costo",
    devolver_detalle: bool = True,
) -> tuple[pd.DataFrame | None, dict]:
    """
    Despacho anual del BESS por programación lineal.

    objetivo_lp="costo": minimiza el costo horario de compra a red.
    objetivo_lp="min_descarga": minimiza throughput de descarga y se usa para
    estimar la reserva técnica mínima del BESS.

    max_ciclos_anio permite imponer un presupuesto anual de degradación.
    """
    if len(perfiles) != HORAS_ANIO:
        raise ValueError(f"Se esperaban {HORAS_ANIO} horas.")
    if tipo_aero not in P_NOMINAL_AERO_MW:
        raise ValueError("tipo_aero debe ser 'GE3.4' o 'GE3.8'.")
    if not 1 <= anio <= 20:
        raise ValueError("anio debe estar entre 1 y 20.")

    banda = perfiles["banda"].to_numpy(dtype=object)
    tarifa_base = perfiles["tarifa_base_usd_mwh"].to_numpy(dtype=float)
    tarifa_anio = tarifa_base * (1.0 + escalamiento_costos) ** (anio - 1)
    factor_fv = factor_degradacion_fv(anio)

    p_fv_sin_degradar = np.minimum(
        p_fv_mw * perfiles["fv_pu_sin_limite"].to_numpy(dtype=float), limite_t1_mw
    )
    p_fv = p_fv_sin_degradar * factor_fv
    if tipo_aero == "GE3.4":
        p_eolico = n_aeros * perfiles["eolico_34_por_aero_mw"].to_numpy(dtype=float)
    else:
        p_eolico = n_aeros * perfiles["eolico_38_por_aero_mw"].to_numpy(dtype=float)

    demanda = perfiles["demanda_mw"].to_numpy(dtype=float)
    renovable = p_fv + p_eolico
    p_neta = demanda - renovable
    deficit = np.maximum(p_neta, 0.0)
    excedente = np.maximum(-p_neta, 0.0)
    p_red_max = min(p_contratada_mw, limite_t1_mw)

    capacidad_disponible = e_bess_mwh * soh_inicial
    e_soc_min = capacidad_disponible * soc_min
    e_soc_max = capacidad_disponible * soc_max
    soc0 = capacidad_disponible * soc_inicial_frac if e_bess_mwh > 0 else 0.0

    if e_bess_mwh <= 1e-12 or p_bess_mw <= 1e-12:
        red_import = np.minimum(deficit, p_red_max)
        no_abast = np.maximum(deficit - p_red_max, 0.0)
        export = np.minimum(excedente, limite_t1_mw) if exportar_excedente else np.zeros(HORAS_ANIO)
        curtail = excedente - export
        costo = red_import * tarifa_anio * DT_H
        soc = np.zeros(HORAS_ANIO)
        carga_ren = np.zeros(HORAS_ANIO)
        carga_red = np.zeros(HORAS_ANIO)
        descarga = np.zeros(HORAS_ANIO)
    else:
        n = HORAS_ANIO
        i_cr, i_cg, i_d, i_s = 0, n, 2*n, 3*n
        nv = 4*n

        c = np.zeros(nv)
        if objetivo_lp == "costo":
            # El término tarifa*deficit es constante. Sólo optimizamos carga de red - descarga.
            c[i_cg:i_cg+n] = tarifa_anio * DT_H
            c[i_d:i_d+n] = -tarifa_anio * DT_H
        elif objetivo_lp == "min_descarga":
            # Objetivo técnico: usar la menor descarga posible. Un término muy pequeño
            # sobre carga de red evita soluciones degeneradas sin alterar el throughput.
            c[i_d:i_d+n] = DT_H
            c[i_cg:i_cg+n] = 1e-8 * tarifa_anio * DT_H
        else:
            raise ValueError("objetivo_lp debe ser 'costo' o 'min_descarga'.")

        bounds = []
        bounds += [(0.0, min(float(excedente[h]), p_bess_mw)) for h in range(n)]
        bounds += [(0.0, p_bess_mw) for _ in range(n)]
        bounds += [(0.0, min(float(deficit[h]), p_bess_mw)) for h in range(n)]
        bounds += [(e_soc_min, e_soc_max) for _ in range(n)]

        rows, cols, data, b_eq = [], [], [], []
        for h in range(n):
            r = len(b_eq)
            rows += [r, r, r, r]
            cols += [i_cr+h, i_cg+h, i_d+h, i_s+h]
            data += [-eta_carga*DT_H, -eta_carga*DT_H, DT_H/eta_descarga, 1.0]
            if h > 0:
                rows.append(r); cols.append(i_s+h-1); data.append(-1.0)
                b_eq.append(0.0)
            else:
                b_eq.append(soc0)
        if exigir_soc_final_igual_inicial:
            r = len(b_eq)
            rows.append(r); cols.append(i_s+n-1); data.append(1.0)
            b_eq.append(soc0)
        A_eq = coo_matrix((data, (rows, cols)), shape=(len(b_eq), nv)).tocsr()
        b_eq = np.asarray(b_eq, dtype=float)

        rows, cols, data, b_ub = [], [], [], []
        for h in range(n):
            # carga_ren + carga_red <= P_BESS
            r = len(b_ub)
            rows += [r, r]; cols += [i_cr+h, i_cg+h]; data += [1.0, 1.0]
            b_ub.append(p_bess_mw)
            # importación = deficit - descarga + carga_red <= P_red_max
            r = len(b_ub)
            rows += [r, r]; cols += [i_cg+h, i_d+h]; data += [1.0, -1.0]
            b_ub.append(p_red_max - deficit[h])

        if max_ciclos_anio is not None:
            if max_ciclos_anio < -1e-12:
                raise ValueError("max_ciclos_anio debe ser >= 0.")
            # N_eq = E_desc_terminal / (eta_desc * DOD_ref * E_nom)
            e_desc_terminal_max = max(0.0, float(max_ciclos_anio)) * (
                eta_descarga * DOD_CICLO_REFERENCIA * e_bess_mwh
            )
            r = len(b_ub)
            for h in range(n):
                rows.append(r); cols.append(i_d+h); data.append(DT_H)
            b_ub.append(e_desc_terminal_max)

        A_ub = coo_matrix((data, (rows, cols)), shape=(len(b_ub), nv)).tocsr()
        b_ub = np.asarray(b_ub, dtype=float)

        sol = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                      bounds=bounds, method="highs")
        if not sol.success:
            raise RuntimeError(f"Despacho económico LP falló en año {anio}: {sol.message}")

        x = sol.x
        carga_ren = x[i_cr:i_cr+n]
        carga_red = x[i_cg:i_cg+n]
        descarga = x[i_d:i_d+n]
        soc = x[i_s:i_s+n]
        red_import = np.maximum(deficit - descarga + carga_red, 0.0)
        no_abast = np.zeros(n)
        excedente_rem = np.maximum(excedente - carga_ren, 0.0)
        export = np.minimum(excedente_rem, limite_t1_mw) if exportar_excedente else np.zeros(n)
        curtail = excedente_rem - export
        costo = red_import * tarifa_anio * DT_H

    descarga_necesaria = np.maximum(deficit - p_red_max, 0.0)
    descarga_obl = np.minimum(descarga, descarga_necesaria)
    descarga_econ = np.maximum(descarga - descarga_obl, 0.0)
    red_consumo = np.maximum(deficit - descarga, 0.0)
    p_t1 = red_import - export
    soc_inicio = np.empty(HORAS_ANIO)
    soc_inicio[0] = soc0
    if HORAS_ANIO > 1:
        soc_inicio[1:] = soc[:-1]

    error_balance = (
        renovable + descarga + red_import + no_abast
        - demanda - carga_ren - carga_red - export - curtail
    )
    tol = 2e-6
    if np.max(np.abs(error_balance)) > tol:
        raise RuntimeError(f"Balance LP no cierra. Error máximo={np.max(np.abs(error_balance)):.3e} MW")
    if np.max(red_import) > p_red_max + tol:
        raise RuntimeError("Despacho LP superó P contratada/T1.")
    if np.max(np.abs(p_t1)) > limite_t1_mw + tol:
        raise RuntimeError("Despacho LP superó el límite neto T1.")

    energia_desc_terminal = float(descarga.sum() * DT_H)
    if e_bess_mwh > 0:
        energia_desc_interna = energia_desc_terminal / eta_descarga
        ciclos_eq = energia_desc_interna / (DOD_CICLO_REFERENCIA * e_bess_mwh)
    else:
        energia_desc_interna = 0.0
        ciclos_eq = 0.0
    ciclos_acum_final = ciclos_acum_inicial + ciclos_eq
    soh_teorico_final = 1.0 - DEGRADACION_POR_CICLO_EQ * ciclos_acum_final
    soh_final = max(SOH_EOL, soh_teorico_final)
    capacidad_final = e_bess_mwh * soh_final

    resultado = None
    if devolver_detalle:
        resultado = pd.DataFrame({
            "Fecha/hora": perfiles["fecha_hora"].to_numpy(),
            "Hora": perfiles["hora"].to_numpy(),
            "Estación": perfiles["estacion"].to_numpy(),
            "Banda": banda,
            "Tarifa base [USD/MWh]": tarifa_base,
            "Tarifa año [USD/MWh]": tarifa_anio,
            "Demanda [MW]": demanda,
            "FV [MW]": p_fv,
            "Eólico [MW]": p_eolico,
            "Renovable [MW]": renovable,
            "P neta [MW]": p_neta,
            "Déficit [MW]": deficit,
            "Excedente renovable [MW]": excedente,
            "SOC inicio [MWh]": soc_inicio,
            "Carga desde renovable [MW]": carga_ren,
            "Descarga obligatoria [MW]": descarga_obl,
            "Carga desde red [MW]": carga_red,
            "Descarga económica [MW]": descarga_econ,
            "Descarga total [MW]": descarga,
            "SOC fin [MWh]": soc,
            "P red para consumo [MW]": red_consumo,
            "P red importada total [MW]": red_import,
            "P exportada [MW]": export,
            "Curtailment / vertido [MW]": curtail,
            "P T1 neta (+import/-export) [MW]": p_t1,
            "Demanda no abastecida [MW]": no_abast,
            "Costo red horario [USD]": costo,
            "Error balance [MW]": error_balance,
        })

    energia_red_banda, costo_red_banda = {}, {}
    for b in ("Valle", "Resto", "Pico"):
        mask = banda == b
        energia_red_banda[b] = float(red_import[mask].sum() * DT_H)
        costo_red_banda[b] = float(costo[mask].sum())

    resumen = {
        "anio": anio,
        "factor_fv": factor_fv,
        "soh_inicial": soh_inicial,
        "soh_final": soh_final,
        "eol_alcanzado": bool(soh_teorico_final <= SOH_EOL),
        "capacidad_bess_inicio_mwh": capacidad_disponible,
        "capacidad_bess_final_mwh": capacidad_final,
        "soc_inicial_mwh": soc0,
        "soc_final_mwh": float(soc[-1]),
        "soc_minimo_observado_mwh": float(np.min(soc)),
        "soc_maximo_observado_mwh": float(np.max(soc)),
        "energia_demanda_mwh": float(demanda.sum() * DT_H),
        "energia_fv_mwh": float(p_fv.sum() * DT_H),
        "energia_eolica_mwh": float(p_eolico.sum() * DT_H),
        "energia_red_total_mwh": float(red_import.sum() * DT_H),
        "energia_red_valle_mwh": energia_red_banda["Valle"],
        "energia_red_resto_mwh": energia_red_banda["Resto"],
        "energia_red_pico_mwh": energia_red_banda["Pico"],
        "carga_renovable_mwh": float(carga_ren.sum() * DT_H),
        "carga_red_valle_mwh": float(carga_red[banda == "Valle"].sum() * DT_H),
        "carga_red_total_mwh": float(carga_red.sum() * DT_H),
        "descarga_obligatoria_mwh": float(descarga_obl.sum() * DT_H),
        "descarga_economica_mwh": float(descarga_econ.sum() * DT_H),
        "descarga_total_mwh": float(descarga.sum() * DT_H),
        "energia_exportada_mwh": float(export.sum() * DT_H),
        "curtailment_mwh": float(curtail.sum() * DT_H),
        "demanda_no_abastecida_mwh": float(no_abast.sum() * DT_H),
        "horas_no_cumple": int(np.count_nonzero(no_abast > 1e-9)),
        "max_deficit_no_abastecido_mw": float(no_abast.max()),
        "cumple_demanda": bool(np.max(no_abast) <= 1e-9),
        "max_importacion_red_mw": float(red_import.max()),
        "max_abs_flujo_t1_mw": float(np.max(np.abs(p_t1))),
        "energia_descargada_interna_mwh": energia_desc_interna,
        "ciclos_equivalentes": float(ciclos_eq),
        "ciclos_acumulados_final": float(ciclos_acum_final),
        "costo_valle_usd": costo_red_banda["Valle"],
        "costo_resto_usd": costo_red_banda["Resto"],
        "costo_pico_usd": costo_red_banda["Pico"],
        "costo_red_total_usd": float(costo.sum()),
        "max_error_balance_mw": float(np.max(np.abs(error_balance))),
        "despacho": (
            "económico LP anual" if objetivo_lp == "costo" else "LP técnico mínima descarga"
        ),
        "max_ciclos_anio": None if max_ciclos_anio is None else float(max_ciclos_anio),
    }
    return resultado, resumen


# =============================================================================
# ECONOMÍA
# =============================================================================

def calcular_capex(
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
) -> Capex:
    if tipo_aero not in P_NOMINAL_AERO_MW:
        raise ValueError("Tipo de aerogenerador no válido.")

    p_eol_instalada = n_aeros * P_NOMINAL_AERO_MW[tipo_aero]
    fv = CAPEX_FV_USD_MW * p_fv_mw
    eol = CAPEX_EOL_USD_MW * p_eol_instalada
    bess = (
        CAPEX_BESS_ENERGIA_USD_MWH * e_bess_mwh
        + CAPEX_BESS_POTENCIA_USD_MW * p_bess_mw
    )
    total = fv + eol + bess + CAPEX_FIJO_USD
    return Capex(fv, eol, bess, CAPEX_FIJO_USD, total)


def calcular_opex_anual(
    capex: Capex,
    anio: int,
    *,
    incluir_capex_fijo_en_cada_opex: bool = True,
) -> dict[str, float]:
    """
    Reproduce el criterio actual del Excel: a la base de OPEX de FV, eólico y BESS
    se le suma el CAPEX fijo de 400.000 USD a cada tecnología.
    """
    fijo = capex.fijo_usd if incluir_capex_fijo_en_cada_opex else 0.0
    esc = (1.0 + ESCALAMIENTO_COSTOS) ** (anio - 1)

    fv = (capex.fv_usd + fijo) * OPEX_FV_PCT * esc
    eol = (capex.eolico_usd + fijo) * OPEX_EOL_PCT * esc
    bess = (capex.bess_usd + fijo) * OPEX_BESS_PCT * esc
    return {
        "fv_usd": fv,
        "eolico_usd": eol,
        "bess_usd": bess,
        "total_usd": fv + eol + bess,
    }


def costo_potencia_contratada_anual(p_contratada_mw: float, anio: int) -> float:
    """
    Criterio adoptado con el docente/Excel:
    4500 USD/(MW·mes) * 12 meses, escalado 2,5 % anual.
    """
    return (
        p_contratada_mw
        * COSTO_PC_USD_MW_MES
        * 12.0
        * (1.0 + ESCALAMIENTO_COSTOS) ** (anio - 1)
    )



def buscar_soh_minimo_tecnico_anio(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    p_contratada_mw: float,
    anio: int,
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    exportar_excedente: bool = True,
    tol_soh: float = 5e-4,
) -> tuple[float, float]:
    """
    Busca por bisección el SOH mínimo que permite abastecer completamente el año
    usando el despacho técnico conservador (sin arbitraje económico).

    Devuelve (SOH mínimo técnico, ciclos mínimos técnicos aproximados en ese SOH).
    El resultado se usa sólo para reservar vida útil futura; no reemplaza el despacho
    económico LP que se ejecuta luego.
    """
    if e_bess_mwh <= 1e-12 or p_bess_mw <= 1e-12:
        # Sin BESS no hay estado de salud que planificar.
        _, r = simular_anio(
            perfiles,
            p_fv_mw=p_fv_mw, n_aeros=n_aeros, p_bess_mw=0.0, e_bess_mwh=0.0,
            p_contratada_mw=p_contratada_mw, anio=anio, soh_inicial=1.0,
            eta_carga=eta_carga, eta_descarga=eta_descarga,
            soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw, tipo_aero=tipo_aero,
            exportar_excedente=exportar_excedente,
        )
        if not r["cumple_demanda"]:
            raise RuntimeError(f"La configuración no abastece el año {anio} aun con SOH=1.")
        return 1.0, 0.0

    def evaluar(soh: float) -> tuple[bool, dict]:
        _, rr = simular_anio(
            perfiles,
            p_fv_mw=p_fv_mw, n_aeros=n_aeros,
            p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw, anio=anio, soh_inicial=soh,
            ciclos_acum_inicial=0.0,
            eta_carga=eta_carga, eta_descarga=eta_descarga,
            soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw, tipo_aero=tipo_aero,
            exportar_excedente=exportar_excedente,
        )
        return bool(rr["cumple_demanda"]), rr

    ok_hi, r_hi = evaluar(1.0)
    if not ok_hi:
        raise RuntimeError(f"La configuración no abastece el año {anio} ni con SOH=1.")

    ok_lo, r_lo = evaluar(SOH_EOL)
    if ok_lo:
        return SOH_EOL, float(r_lo["ciclos_equivalentes"])

    lo, hi = SOH_EOL, 1.0
    r_factible = r_hi
    while hi - lo > tol_soh:
        mid = 0.5 * (lo + hi)
        ok, rr = evaluar(mid)
        if ok:
            hi = mid
            r_factible = rr
        else:
            lo = mid

    # Recalcular exactamente en el extremo factible final.
    ok, r_factible = evaluar(hi)
    if not ok:
        raise RuntimeError(f"Error numérico buscando SOH técnico del año {anio}.")
    return float(hi), float(r_factible["ciclos_equivalentes"])


def preparar_plan_degradacion_multianual(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    p_contratada_mw: float,
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    exportar_excedente: bool = True,
    tol_soh: float = 5e-4,
) -> pd.DataFrame:
    """
    Construye una envolvente de ciclos acumulados para 20 años.

    Idea:
      - cada año tiene un SOH mínimo técnico para poder cumplir la demanda;
      - cada año necesita una cantidad mínima de ciclos por peak shaving;
      - hacia atrás se reserva esa vida útil mínima futura;
      - el resto de los ciclos queda disponible para arbitraje económico.

    Es una aproximación multianual de look-ahead mucho más liviana que resolver un LP
    horario único de 175.680 h. No inventa costo de degradación ni reemplazo.
    """
    if e_bess_mwh <= 1e-12 or p_bess_mw <= 1e-12:
        return pd.DataFrame({
            "Año": np.arange(1, 21),
            "SOH mínimo técnico": np.ones(20),
            "Ciclos mínimos técnicos": np.zeros(20),
            "Máx ciclos acumulados por SOH técnico": np.zeros(20),
            "Envolvente ciclos acumulados al inicio": np.zeros(20),
            "Envolvente ciclos acumulados siguiente inicio": np.zeros(20),
        })

    soh_min = np.zeros(20)
    ciclos_min = np.zeros(20)

    for i, anio in enumerate(range(1, 21)):
        soh_i, ciclos_i = buscar_soh_minimo_tecnico_anio(
            perfiles,
            p_fv_mw=p_fv_mw, n_aeros=n_aeros,
            p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw, anio=anio,
            eta_carga=eta_carga, eta_descarga=eta_descarga,
            soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw, tipo_aero=tipo_aero,
            exportar_excedente=exportar_excedente, tol_soh=tol_soh,
        )
        soh_min[i] = soh_i
        ciclos_min[i] = ciclos_i

    # SOH = 1 - degradación_por_ciclo * ciclos_acumulados.
    ciclos_max_por_soh = np.maximum(
        0.0,
        np.minimum(
            (1.0 - soh_min) / DEGRADACION_POR_CICLO_EQ,
            (1.0 - SOH_EOL) / DEGRADACION_POR_CICLO_EQ,
        ),
    )
    ciclos_eol = (1.0 - SOH_EOL) / DEGRADACION_POR_CICLO_EQ

    # V12: envolvente conservadora. Ya no permitimos que el último año "gaste"
    # degradación por debajo del SOH técnico del propio año. Para cada año se calcula:
    #   B_fin[y]    = máximo acumulado al FINAL del año y;
    #   B_inicio[y] = máximo acumulado al INICIO, reservando los ciclos técnicos.
    # Además B_fin[y] no puede superar lo admisible al inicio del año siguiente.
    B_inicio = np.zeros(20)
    B_fin = np.zeros(20)
    limite_inicio_siguiente = ciclos_eol
    for y in range(19, -1, -1):
        B_fin[y] = min(ciclos_max_por_soh[y], limite_inicio_siguiente)
        B_inicio[y] = B_fin[y] - ciclos_min[y]
        limite_inicio_siguiente = B_inicio[y]

    if B_inicio[0] < -1e-6:
        raise RuntimeError(
            "Ni reservando exclusivamente los ciclos técnicos mínimos el BESS alcanza "
            "para cumplir los 20 años con degradación conservadora dentro de cada año."
        )
    B_inicio = np.maximum(B_inicio, 0.0)
    B_fin = np.maximum(B_fin, 0.0)

    return pd.DataFrame({
        "Año": np.arange(1, 21),
        "SOH mínimo técnico": soh_min,
        "Ciclos mínimos técnicos": ciclos_min,
        "Máx ciclos acumulados por SOH técnico": ciclos_max_por_soh,
        "Envolvente ciclos acumulados al inicio": B_inicio,
        "Envolvente ciclos acumulados al final": B_fin,
        # alias conservado para compatibilidad con reportes previos
        "Envolvente ciclos acumulados siguiente inicio": B_fin,
    })


def simular_20_anios_consciente_degradacion(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    p_contratada_mw: float,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    exportar_excedente: bool = True,
    incluir_capex_fijo_en_cada_opex: bool = True,
    wacc: float = WACC,
    tol_soh_plan: float = 5e-4,
    devolver_detalle_anio1: bool = True,
) -> tuple[pd.DataFrame, float, pd.DataFrame | None, dict | None, pd.DataFrame]:
    """
    Despacho económico con look-ahead de degradación para los 20 años.

    No optimiza los 175.680 pasos en un único LP (demasiado pesado para evaluar muchos
    diseños). En cambio, calcula primero una reserva técnica futura de vida útil y luego
    resuelve 20 LP anuales, limitando los ciclos de cada año para no comprometer los años
    restantes. De esta forma la batería no puede 'comerse' el SOC/SOH futuro por arbitraje.

    Devuelve:
      detalle_20, costo_total_20, detalle_horario_anio1, resumen_anio1, plan_degradacion
    """
    capex = calcular_capex(p_fv_mw, n_aeros, p_bess_mw, e_bess_mwh, tipo_aero)

    if e_bess_mwh <= 1e-12 or p_bess_mw <= 1e-12:
        detalle, costo = simular_20_anios(
            perfiles,
            p_fv_mw=p_fv_mw, n_aeros=n_aeros,
            p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw, tipo_aero=tipo_aero,
            eta_carga=eta_carga, eta_descarga=eta_descarga,
            soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw, exportar_excedente=exportar_excedente,
            incluir_capex_fijo_en_cada_opex=incluir_capex_fijo_en_cada_opex,
            wacc=wacc, despacho_economico=False,
        )
        r1, s1 = simular_anio(
            perfiles,
            p_fv_mw=p_fv_mw, n_aeros=n_aeros,
            p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw, anio=1, soh_inicial=1.0,
            eta_carga=eta_carga, eta_descarga=eta_descarga,
            soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw, tipo_aero=tipo_aero,
            exportar_excedente=exportar_excedente,
        )
        plan = preparar_plan_degradacion_multianual(
            perfiles, p_fv_mw=p_fv_mw, n_aeros=n_aeros,
            p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw,
        )
        return detalle, costo, r1, s1, plan

    plan = preparar_plan_degradacion_multianual(
        perfiles,
        p_fv_mw=p_fv_mw, n_aeros=n_aeros,
        p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
        p_contratada_mw=p_contratada_mw,
        eta_carga=eta_carga, eta_descarga=eta_descarga,
        soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
        limite_t1_mw=limite_t1_mw, tipo_aero=tipo_aero,
        exportar_excedente=exportar_excedente, tol_soh=tol_soh_plan,
    )

    soh = 1.0
    ciclos_acum = 0.0
    filas: list[dict] = []
    detalle_anio1: pd.DataFrame | None = None
    resumen_anio1: dict | None = None

    for i, anio in enumerate(range(1, 21)):
        soh_min_tecnico = float(plan.iloc[i]["SOH mínimo técnico"])
        if soh + 2e-4 < soh_min_tecnico:
            raise RuntimeError(
                f"Año {anio}: SOH disponible={soh:.5f} < SOH técnico mínimo={soh_min_tecnico:.5f}."
            )

        max_acum_siguiente = float(
            plan.iloc[i]["Envolvente ciclos acumulados siguiente inicio"]
        )
        max_ciclos_anio = max(0.0, max_acum_siguiente - ciclos_acum)

        resultado, resumen = simular_anio_economico(
            perfiles,
            p_fv_mw=p_fv_mw, n_aeros=n_aeros,
            p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw, anio=anio,
            soh_inicial=soh, ciclos_acum_inicial=ciclos_acum,
            eta_carga=eta_carga, eta_descarga=eta_descarga,
            soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw, tipo_aero=tipo_aero,
            exportar_excedente=exportar_excedente,
            max_ciclos_anio=max_ciclos_anio,
            objetivo_lp="costo",
            exigir_soc_final_igual_inicial=True,
            devolver_detalle=(devolver_detalle_anio1 and i == 0),
        )

        if i == 0 and devolver_detalle_anio1:
            detalle_anio1 = resultado.copy() if resultado is not None else None
            resumen_anio1 = resumen.copy()

        opex = calcular_opex_anual(
            capex, anio,
            incluir_capex_fijo_en_cada_opex=incluir_capex_fijo_en_cada_opex,
        )
        costo_pc = costo_potencia_contratada_anual(p_contratada_mw, anio)
        costo_red = resumen["costo_red_total_usd"]
        costo_reemplazo = 0.0
        flujo_nominal = opex["total_usd"] + costo_pc + costo_red + costo_reemplazo
        vp = flujo_nominal / (1.0 + wacc) ** anio

        filas.append({
            "Año": anio,
            "Factor FV": resumen["factor_fv"],
            "SOH inicio": resumen["soh_inicial"],
            "SOH mínimo técnico": soh_min_tecnico,
            "SOH final": resumen["soh_final"],
            "Capacidad BESS inicio [MWh]": resumen["capacidad_bess_inicio_mwh"],
            "Capacidad BESS final [MWh]": resumen["capacidad_bess_final_mwh"],
            "Ciclos mínimos técnicos": float(plan.iloc[i]["Ciclos mínimos técnicos"]),
            "Ciclos máximos permitidos año": max_ciclos_anio,
            "Ciclos equivalentes año": resumen["ciclos_equivalentes"],
            "Ciclos equivalentes acumulados": resumen["ciclos_acumulados_final"],
            "EOL alcanzado": resumen["eol_alcanzado"],
            "Energía demanda [MWh]": resumen["energia_demanda_mwh"],
            "Energía FV [MWh]": resumen["energia_fv_mwh"],
            "Energía eólica [MWh]": resumen["energia_eolica_mwh"],
            "Energía red Valle [MWh]": resumen["energia_red_valle_mwh"],
            "Energía red Resto [MWh]": resumen["energia_red_resto_mwh"],
            "Energía red Pico [MWh]": resumen["energia_red_pico_mwh"],
            "Carga renovable BESS [MWh]": resumen.get("carga_renovable_mwh", 0.0),
            "Carga red total [MWh]": resumen.get("carga_red_total_mwh", resumen["carga_red_valle_mwh"]),
            "Descarga obligatoria [MWh]": resumen["descarga_obligatoria_mwh"],
            "Descarga económica [MWh]": resumen["descarga_economica_mwh"],
            "Descarga total BESS [MWh]": resumen.get("descarga_total_mwh", resumen["descarga_obligatoria_mwh"] + resumen["descarga_economica_mwh"]),
            "SOC mínimo observado [MWh]": resumen.get("soc_minimo_observado_mwh", float("nan")),
            "Costo red Valle [USD]": resumen["costo_valle_usd"],
            "Costo red Resto [USD]": resumen["costo_resto_usd"],
            "Costo red Pico [USD]": resumen["costo_pico_usd"],
            "Costo energía red [USD]": costo_red,
            "OPEX FV [USD]": opex["fv_usd"],
            "OPEX eólico [USD]": opex["eolico_usd"],
            "OPEX BESS [USD]": opex["bess_usd"],
            "OPEX total [USD]": opex["total_usd"],
            "Costo potencia contratada [USD]": costo_pc,
            "Costo reemplazo BESS [USD]": costo_reemplazo,
            "Flujo anual nominal [USD]": flujo_nominal,
            "VP flujo anual [USD]": vp,
            "Demanda no abastecida [MWh]": resumen["demanda_no_abastecida_mwh"],
            "Horas no cumple": resumen["horas_no_cumple"],
            "Cumple demanda": resumen["cumple_demanda"],
            "Exportación [MWh]": resumen["energia_exportada_mwh"],
            "Curtailment [MWh]": resumen["curtailment_mwh"],
            "Modo despacho": "económico LP + reserva multianual de degradación",
        })

        ciclos_acum = resumen["ciclos_acumulados_final"]
        soh = resumen["soh_final"]

    detalle = pd.DataFrame(filas)
    costo_total_20 = capex.total_usd + float(detalle["VP flujo anual [USD]"].sum())
    return detalle, costo_total_20, detalle_anio1, resumen_anio1, plan


def simular_20_anios(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    p_contratada_mw: float,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    exportar_excedente: bool = True,
    incluir_capex_fijo_en_cada_opex: bool = True,
    wacc: float = WACC,
    despacho_economico: bool = False,
) -> tuple[pd.DataFrame, float]:
    """
    Simula años 1..20 secuencialmente.

    Importante: reproduce el criterio adoptado en el Excel para el comienzo de cada
    año: SOC inicial = 1 (100 % de la CAPACIDAD DISPONIBLE de ese año).
    El SOH sí se hereda del año anterior.

    No hay reemplazo automático del BESS. Si SOH llega a 70 %, se marca EOL y se
    mantiene el piso de 70 % para no extrapolar la degradación más allá del dato.
    """
    capex = calcular_capex(p_fv_mw, n_aeros, p_bess_mw, e_bess_mwh, tipo_aero)

    soh = 1.0
    ciclos_acum = 0.0
    filas: list[dict] = []

    for anio in range(1, 21):
        simulador_anual = simular_anio_economico if despacho_economico else simular_anio
        _, resumen = simulador_anual(
            perfiles,
            p_fv_mw=p_fv_mw,
            n_aeros=n_aeros,
            p_bess_mw=p_bess_mw,
            e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw,
            anio=anio,
            soh_inicial=soh,
            ciclos_acum_inicial=ciclos_acum,
            eta_carga=eta_carga,
            eta_descarga=eta_descarga,
            soc_min=soc_min,
            soc_max=soc_max,
            soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw,
            tipo_aero=tipo_aero,
            exportar_excedente=exportar_excedente,
        )

        opex = calcular_opex_anual(
            capex,
            anio,
            incluir_capex_fijo_en_cada_opex=incluir_capex_fijo_en_cada_opex,
        )
        costo_pc = costo_potencia_contratada_anual(p_contratada_mw, anio)
        costo_red = resumen["costo_red_total_usd"]

        # Reemplazo BESS pendiente de definición: por ahora 0.
        costo_reemplazo = 0.0

        flujo_nominal = opex["total_usd"] + costo_pc + costo_red + costo_reemplazo
        vp = flujo_nominal / (1.0 + wacc) ** anio

        filas.append(
            {
                "Año": anio,
                "Factor FV": resumen["factor_fv"],
                "SOH inicio": resumen["soh_inicial"],
                "SOH final": resumen["soh_final"],
                "Capacidad BESS inicio [MWh]": resumen["capacidad_bess_inicio_mwh"],
                "Capacidad BESS final [MWh]": resumen["capacidad_bess_final_mwh"],
                "Ciclos equivalentes año": resumen["ciclos_equivalentes"],
                "Ciclos equivalentes acumulados": resumen["ciclos_acumulados_final"],
                "EOL alcanzado": resumen["eol_alcanzado"],
                "Energía red Valle [MWh]": resumen["energia_red_valle_mwh"],
                "Energía red Resto [MWh]": resumen["energia_red_resto_mwh"],
                "Energía red Pico [MWh]": resumen["energia_red_pico_mwh"],
                "Costo red Valle [USD]": resumen["costo_valle_usd"],
                "Costo red Resto [USD]": resumen["costo_resto_usd"],
                "Costo red Pico [USD]": resumen["costo_pico_usd"],
                "Costo energía red [USD]": costo_red,
                "OPEX FV [USD]": opex["fv_usd"],
                "OPEX eólico [USD]": opex["eolico_usd"],
                "OPEX BESS [USD]": opex["bess_usd"],
                "OPEX total [USD]": opex["total_usd"],
                "Costo potencia contratada [USD]": costo_pc,
                "Costo reemplazo BESS [USD]": costo_reemplazo,
                "Flujo anual nominal [USD]": flujo_nominal,
                "VP flujo anual [USD]": vp,
                "Demanda no abastecida [MWh]": resumen["demanda_no_abastecida_mwh"],
                "Horas no cumple": resumen["horas_no_cumple"],
                "Cumple demanda": resumen["cumple_demanda"],
                "Exportación [MWh]": resumen["energia_exportada_mwh"],
                "Curtailment [MWh]": resumen["curtailment_mwh"],
            }
        )

        ciclos_acum = resumen["ciclos_acumulados_final"]
        soh = resumen["soh_final"]

    detalle = pd.DataFrame(filas)
    costo_total_20 = capex.total_usd + float(detalle["VP flujo anual [USD]"].sum())
    return detalle, costo_total_20



# =============================================================================
# EVALUACIÓN Y OPTIMIZACIÓN DE DISEÑO
# =============================================================================

def evaluar_configuracion(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    p_contratada_mw: float,
    n_containers: int | None = None,
    e_container_mwh: float = E_CONTAINER_MWH_DEFAULT,
    potencia_modulo_fv_w: float = POTENCIA_MODULO_FV_W_DEFAULT,
    pitch_fv_m: float = PITCH_FV_DEFAULT_M,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    exportar_excedente: bool = True,
    wacc: float = WACC,
    despacho_economico: bool = False,
    despacho_multianual: bool = False,
) -> tuple[dict, pd.DataFrame | None]:
    """
    Evalúa UNA configuración de diseño durante 20 años.

    Si no abastece toda la demanda en cualquiera de los 20 años, se marca como
    no factible y el costo objetivo se devuelve como infinito.

    Esta es la función que usa el optimizador de diseño.
    """
    # Validaciones físicas básicas de la configuración candidata.
    if p_fv_mw < 0:
        raise ValueError("P_FV debe ser >= 0.")
    if n_aeros < 0 or int(n_aeros) != n_aeros:
        raise ValueError("n_aeros debe ser un entero >= 0.")
    if not (P_CONTRATADA_MIN_MW <= p_contratada_mw <= min(P_CONTRATADA_MAX_MW, limite_t1_mw)):
        raise ValueError("P_contratada debe estar entre 6 MW y el límite de T1.")
    if p_bess_mw < 0 or e_bess_mwh < 0:
        raise ValueError("P_BESS y E_BESS deben ser >= 0.")
    if e_bess_mwh == 0 and p_bess_mw > 1e-12:
        raise ValueError("No puede haber potencia BESS con E_BESS = 0.")
    if e_bess_mwh > 1e-12 and p_bess_mw <= 1e-12:
        raise ValueError("No tiene sentido instalar energía BESS con P_BESS = 0.")
    if e_bess_mwh > 0 and p_bess_mw > P_RATE_MAX * e_bess_mwh + 1e-9:
        raise ValueError("P_BESS supera 0,5C para la capacidad BESS propuesta.")
    if n_containers is None:
        n_containers = 0 if e_bess_mwh <= 1e-12 else int(round(e_bess_mwh / e_container_mwh))
    if not math.isclose(e_bess_mwh, n_containers * e_container_mwh, rel_tol=0, abs_tol=1e-6):
        raise ValueError("E_BESS debe coincidir con n_containers * energía/container.")
    bess_diseno = calcular_metricas_bess_diseno(p_bess_mw, int(n_containers), e_container_mwh, soc_min, soc_max)
    espacio = calcular_screening_espacial(
        p_fv_mw=p_fv_mw, n_aeros=n_aeros, n_containers=int(n_containers),
        potencia_modulo_w=potencia_modulo_fv_w, pitch_fv_m=pitch_fv_m
    )
    if not espacio["cumple_screening_espacial"]:
        raise ValueError("La configuración no cumple el screening espacial.")

    if despacho_multianual:
        detalle_20, costo_total_20, _, _, _ = simular_20_anios_consciente_degradacion(
            perfiles,
            p_fv_mw=p_fv_mw, n_aeros=n_aeros,
            p_bess_mw=p_bess_mw, e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw, tipo_aero=tipo_aero,
            eta_carga=eta_carga, eta_descarga=eta_descarga,
            soc_min=soc_min, soc_max=soc_max, soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw, exportar_excedente=exportar_excedente,
            wacc=wacc,
        )
    else:
        detalle_20, costo_total_20 = simular_20_anios(
            perfiles,
            p_fv_mw=p_fv_mw,
            n_aeros=n_aeros,
            p_bess_mw=p_bess_mw,
            e_bess_mwh=e_bess_mwh,
            p_contratada_mw=p_contratada_mw,
            tipo_aero=tipo_aero,
            eta_carga=eta_carga,
            eta_descarga=eta_descarga,
            soc_min=soc_min,
            soc_max=soc_max,
            soc_inicial_frac=soc_inicial_frac,
            limite_t1_mw=limite_t1_mw,
            exportar_excedente=exportar_excedente,
            wacc=wacc,
            despacho_economico=despacho_economico,
        )

    factible = bool(detalle_20["Cumple demanda"].all())
    horas_no_cumple = int(detalle_20["Horas no cumple"].sum())
    energia_no_abast = float(detalle_20["Demanda no abastecida [MWh]"].sum())
    costo_objetivo = float(costo_total_20) if factible else math.inf

    capex = calcular_capex(p_fv_mw, n_aeros, p_bess_mw, e_bess_mwh, tipo_aero)
    p_eol_mw = n_aeros * P_NOMINAL_AERO_MW[tipo_aero]

    resumen = {
        "P_FV [MW]": float(p_fv_mw),
        "N aeros": int(n_aeros),
        "P_EOL instalada [MW]": float(p_eol_mw),
        "P_BESS [MW]": float(p_bess_mw),
        "N containers BESS": int(n_containers),
        "E_BESS [MWh]": float(e_bess_mwh),
        "Duración BESS nominal [h]": bess_diseno["horas_nominales"],
        "Duración BESS útil BOL [h]": bess_diseno["horas_utiles_bol"],
        "CAPEX BESS energía [USD]": bess_diseno["capex_bess_energia_usd"],
        "CAPEX BESS potencia [USD]": bess_diseno["capex_bess_potencia_usd"],
        "CAPEX BESS total [USD]": bess_diseno["capex_bess_total_usd"],
        "P contratada [MW]": float(p_contratada_mw),
        "Factible": factible,
        "Horas no cumple 20a": horas_no_cumple,
        "Energía no abastecida 20a [MWh]": energia_no_abast,
        "CAPEX [USD]": float(capex.total_usd),
        "VP operación 20a [USD]": float(detalle_20["VP flujo anual [USD]"].sum()),
        "Costo total 20a [USD]": float(costo_objetivo),
        "Ciclos acumulados año 20": float(detalle_20.iloc[-1]["Ciclos equivalentes acumulados"]),
        "SOH final año 20": float(detalle_20.iloc[-1]["SOH final"]),
        "EOL alcanzado": bool(detalle_20["EOL alcanzado"].any()),
        "Modo despacho": (
            "económico con reserva multianual" if despacho_multianual
            else ("económico LP anual" if despacho_economico else "técnico heurístico")
        ),
    }
    if espacio is not None:
        resumen.update({
            "Potencia módulo FV [W]": float(potencia_modulo_fv_w),
            "Pitch FV [m]": float(espacio["pitch_fv_m"]),
            "GCR FV": float(espacio["gcr_fv"]),
            "N módulos FV": int(espacio["n_modulos_fv"]),
            "Área módulos FV [m2]": float(espacio["area_modulos_fv_m2"]),
            "Área FV terreno [m2]": float(espacio["area_fv_terreno_m2"]),
            "Área BESS screening [m2]": float(espacio["area_bess_m2"]),
            "Área FV+BESS screening [m2]": float(espacio["area_fv_mas_bess_m2"]),
            "Área eólica reservada screening [m2]": float(espacio["area_eolica_reservada_m2"]),
            "Área residual tras eólica [m2]": float(espacio["area_residual_tras_eolica_m2"]),
            "Área total screening [m2]": float(espacio["area_total_screening_m2"]),
            "Uso terreno FV+BESS [%]": float(espacio["uso_area_fv_bess_pct"]),
            "Uso terreno eólico [%]": float(espacio["uso_area_eolica_pct"]),
            "Uso terreno total screening [%]": float(espacio["uso_area_total_screening_pct"]),
            "Cumple screening espacial": bool(espacio["cumple_screening_espacial"]),
        })
    return resumen, detalle_20


def _parsear_lista_numerica(texto: str, *, enteros: bool = False) -> list[float] | list[int]:
    """Convierte '0,1,2.5' en una lista numérica, sin duplicados."""
    if texto is None or not str(texto).strip():
        raise ValueError("La lista de candidatos no puede estar vacía.")
    partes = [x.strip() for x in str(texto).split(",") if x.strip()]
    if enteros:
        vals = [int(float(x)) for x in partes]
        if any(abs(float(x) - int(float(x))) > 1e-9 for x in partes):
            raise ValueError(f"Se esperaban enteros en: {texto}")
    else:
        vals = [float(x) for x in partes]
    # preserva orden, elimina duplicados
    return list(dict.fromkeys(vals))


def optimizar_grilla(
    perfiles: pd.DataFrame,
    *,
    valores_fv: list[float],
    valores_aeros: list[int],
    valores_pbess: list[float],
    valores_containers: list[int],
    p_contratada_mw: float = P_CONTRATADA_FIJA_MW,
    e_container_mwh: float = E_CONTAINER_MWH_DEFAULT,
    potencia_modulo_fv_w: float = POTENCIA_MODULO_FV_W_DEFAULT,
    pitch_fv_m: float = PITCH_FV_DEFAULT_M,
    tipo_aero: Literal["GE3.4", "GE3.8"] = "GE3.4",
    eta_carga: float = ETA_CARGA_DEFAULT,
    eta_descarga: float = ETA_DESCARGA_DEFAULT,
    soc_min: float = SOC_MIN_DEFAULT,
    soc_max: float = SOC_MAX_DEFAULT,
    soc_inicial_frac: float = SOC_INICIAL_DEFAULT,
    limite_t1_mw: float = LIMITE_T1_MW,
    exportar_excedente: bool = True,
    wacc: float = WACC,
    despacho_economico: bool = False,
) -> tuple[pd.DataFrame, dict | None]:
    """
    Recorre una grilla explícita de las cuatro variables de diseño:
      1) P_FV
      2) cantidad de aerogeneradores (P_EOL queda determinada)
      3) P_BESS
      4) cantidad de containers (E_BESS = containers * 5,015 MWh)
  
    Las configuraciones físicamente imposibles (por ejemplo P_BESS > 0,5C)
    se descartan antes de simular.

    IMPORTANTE: esta optimización usa el despacho operativo ACTUAL. Todavía no
    optimiza hora a hora la descarga económica del BESS.
    """
    combinaciones = list(product(
        valores_fv,
        valores_aeros,
        valores_pbess,
        valores_containers,
    ))
    total = len(combinaciones)
    if total == 0:
        raise ValueError("El espacio de búsqueda está vacío.")
    if pitch_fv_m <= ANCHO_ROTANTE_TRACKER_1P_M:
        raise ValueError(
            f"--pitch-fv-m debe ser mayor que {ANCHO_ROTANTE_TRACKER_1P_M:.3f} m."
        )
    if potencia_modulo_fv_w <= 0:
        raise ValueError("--pot-modulo-fv-w debe ser > 0.")
    gcr_fv = ANCHO_ROTANTE_TRACKER_1P_M / pitch_fv_m

    print("\n" + "=" * 80)
    print("OPTIMIZACIÓN POR GRILLA")
    print("=" * 80)
    print(f"Combinaciones brutas: {total:,}")
    print(f"P contratada fija: {p_contratada_mw:.1f} MW")
    print(f"Restricción eólica: n_aeros <= {N_AEROS_MAX_ESPACIO} | D={ROTOR_DIAMETRO_M:.0f} m | separación mínima={DISTANCIA_MIN_AEROS_M:.0f} m ({DISTANCIA_MIN_AEROS_D:.1f}D)")
    print(f"Área del polígono: {AREA_DISPONIBLE_M2/10_000:.2f} ha")
    print(f"FV screening: módulo={potencia_modulo_fv_w:g} W | pitch={pitch_fv_m:.2f} m | GCR={gcr_fv:.3f}")
    print(f"BESS screening: {BESS_CONTAINER_LARGO_M:.3f} x {BESS_CONTAINER_ANCHO_M:.3f} m | separación={BESS_SEPARACION_SCREENING_M:g} m")

    resultados: list[dict] = []
    mejor: dict | None = None
    t0 = time.time()
    evaluadas = 0
    descartadas_fisicas = 0

    for idx, (p_fv, n_aeros, p_bess, n_cont) in enumerate(combinaciones, start=1):
        p_cont = float(p_contratada_mw)
        e_bess = float(n_cont) * float(e_container_mwh)

        # Filtros físicos baratos, antes de las 20 simulaciones anuales.
        if p_fv < 0 or n_aeros < 0 or n_cont < 0:
            descartadas_fisicas += 1
            continue
        if n_aeros > N_AEROS_MAX_ESPACIO:
            descartadas_fisicas += 1
            continue
        if abs(p_cont - P_CONTRATADA_FIJA_MW) > 1e-9:
            raise ValueError("La optimización debe usar P contratada fija en 15 MW.")
        if p_cont > limite_t1_mw + 1e-9:
            raise ValueError("P contratada fija supera el límite de T1.")
        if e_bess <= 1e-12 and p_bess > 1e-12:
            descartadas_fisicas += 1
            continue
        if e_bess > 1e-12 and p_bess <= 1e-12:
            descartadas_fisicas += 1
            continue
        if e_bess > 0 and p_bess > P_RATE_MAX * e_bess + 1e-9:
            descartadas_fisicas += 1
            continue
        espacio = calcular_screening_espacial(
            p_fv_mw=float(p_fv), n_aeros=int(n_aeros), n_containers=int(n_cont),
            potencia_modulo_w=float(potencia_modulo_fv_w), pitch_fv_m=float(pitch_fv_m))
        if not espacio["cumple_screening_espacial"]:
            descartadas_fisicas += 1
            continue

        try:
            resumen, _ = evaluar_configuracion(
                perfiles,
                p_fv_mw=float(p_fv),
                n_aeros=int(n_aeros),
                p_bess_mw=float(p_bess),
                e_bess_mwh=e_bess,
                p_contratada_mw=float(p_cont),
                n_containers=int(n_cont),
                e_container_mwh=float(e_container_mwh),
                potencia_modulo_fv_w=float(potencia_modulo_fv_w),
                pitch_fv_m=float(pitch_fv_m),
                tipo_aero=tipo_aero,
                eta_carga=eta_carga,
                eta_descarga=eta_descarga,
                soc_min=soc_min,
                soc_max=soc_max,
                soc_inicial_frac=soc_inicial_frac,
                limite_t1_mw=limite_t1_mw,
                exportar_excedente=exportar_excedente,
                wacc=wacc,
                despacho_economico=despacho_economico,
            )
        except ValueError:
            descartadas_fisicas += 1
            continue

        evaluadas += 1
        resultados.append(resumen)

        if resumen["Factible"]:
            if mejor is None or resumen["Costo total 20a [USD]"] < mejor["Costo total 20a [USD]"]:
                mejor = resumen.copy()
                print(
                    f"  Nuevo mejor -> Costo=${mejor['Costo total 20a [USD]']:,.0f} | "
                    f"FV={mejor['P_FV [MW]']:g} MW | aeros={mejor['N aeros']} | "
                    f"PBESS={mejor['P_BESS [MW]']:g} MW | EBESS={mejor['E_BESS [MWh]']:g} MWh | "
                    f"t={mejor['Duración BESS nominal [h]']:.2f} h | "
                    f"FV+BESS={mejor['Uso terreno FV+BESS [%]']:.1f}% terreno | "
                    f"Pcont={mejor['P contratada [MW]']:g} MW"
                )

        if idx % max(1, total // 20) == 0 or idx == total:
            elapsed = time.time() - t0
            print(
                f"Progreso {idx:,}/{total:,} ({100*idx/total:5.1f} %) | "
                f"simuladas={evaluadas:,} | descartadas={descartadas_fisicas:,} | "
                f"{elapsed:,.1f} s"
            )

    df = pd.DataFrame(resultados)
    if not df.empty:
        # Factibles primero y luego costo creciente. Los inf quedan al final.
        df = df.sort_values(
            by=["Factible", "Costo total 20a [USD]"],
            ascending=[False, True],
            ignore_index=True,
        )

    return df, mejor

# =============================================================================
# SALIDA
# =============================================================================

def imprimir_resumen_anio(resumen: dict) -> None:
    print("\n" + "=" * 80)
    print(f"RESUMEN AÑO {resumen['anio']}")
    print("=" * 80)
    claves = [
        "factor_fv",
        "soh_inicial",
        "soh_final",
        "capacidad_bess_inicio_mwh",
        "capacidad_bess_final_mwh",
        "energia_demanda_mwh",
        "energia_fv_mwh",
        "energia_eolica_mwh",
        "energia_red_total_mwh",
        "energia_red_valle_mwh",
        "energia_red_resto_mwh",
        "energia_red_pico_mwh",
        "carga_renovable_mwh",
        "carga_red_valle_mwh",
        "descarga_obligatoria_mwh",
        "descarga_economica_mwh",
        "energia_exportada_mwh",
        "curtailment_mwh",
        "demanda_no_abastecida_mwh",
        "horas_no_cumple",
        "max_deficit_no_abastecido_mw",
        "ciclos_equivalentes",
        "ciclos_acumulados_final",
        "costo_valle_usd",
        "costo_resto_usd",
        "costo_pico_usd",
        "costo_red_total_usd",
        "max_abs_flujo_t1_mw",
        "max_error_balance_mw",
    ]
    for k in claves:
        v = resumen[k]
        if isinstance(v, (float, np.floating)):
            print(f"{k:42s}: {float(v):,.9f}")
        else:
            print(f"{k:42s}: {v}")


# =============================================================================
# MAIN
# =============================================================================

def main_v11_legacy() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--excel",
        type=Path,
        default=None,
        help="Ruta al Excel actual (.xlsm o .xlsx).",
    )
    parser.add_argument(
        "--tipo-aero",
        choices=["GE3.4", "GE3.8"],
        default="GE3.4",
        help="Tecnología eólica a simular.",
    )
    parser.add_argument(
        "--simular-20",
        action="store_true",
        help="Además del año 1, simula los 20 años y calcula el costo total.",
    )
    parser.add_argument(
        "--despacho-economico",
        action="store_true",
        help="Optimiza cada año por separado. Puede ser miope respecto de la degradación futura.",
    )
    parser.add_argument(
        "--despacho-multianual",
        action="store_true",
        help=(
            "V11 recomendada: despacho económico con reserva multianual de degradación. "
            "Calcula SOH técnico mínimo futuro y limita ciclos para asegurar los 20 años."
        ),
    )
    parser.add_argument(
        "--sin-exportar",
        action="store_true",
        help="Recorta todo excedente en vez de exportarlo hasta T1.",
    )
    parser.add_argument(
        "--optimizar",
        action="store_true",
        help="Ejecuta búsqueda por grilla de las cuatro variables de diseño.",
    )
    parser.add_argument("--fv-valores", type=str, default=None, help="Ej.: 0,10,15,17,20")
    parser.add_argument("--aeros-valores", type=str, default=None, help="Ej.: 0,1,2,3")
    parser.add_argument("--pbess-valores", type=str, default=None, help="Ej.: 0,2.5,5,7.5")
    parser.add_argument("--containers-valores", type=str, default=None, help="Ej.: 0,1,2,3,4")
    parser.add_argument("--pot-modulo-fv-w", type=float, default=POTENCIA_MODULO_FV_W_DEFAULT,
                        help="Potencia STC del módulo para área. Default 700 W (conservador dentro de 700-725 W).")
    parser.add_argument(
        "--pitch-fv-m", type=float, default=PITCH_FV_DEFAULT_M,
        help=(
            "Pitch entre filas FV [m]. Default 6.5 m, criterio geométrico de no sombreado "
            "9-15 h solares en solsticio de invierno. El GCR se calcula automáticamente."
        ),
    )
    args = parser.parse_args()
    if args.despacho_multianual:
        # El modo multianual necesariamente evalúa los 20 años.
        args.simular_20 = True
    if args.optimizar and args.despacho_multianual:
        raise ValueError(
            "V11 usa el despacho multianual para validar configuraciones. "
            "No lo combines todavía con --optimizar: el optimizador continuo/mixto será la etapa siguiente."
        )

    ruta = args.excel.resolve() if args.excel is not None else buscar_excel_por_defecto()
    if not ruta.exists():
        raise FileNotFoundError(f"No encontré el Excel: {ruta}")

    print(f"Excel utilizado: {ruta}")
    cfg = leer_configuracion_excel(ruta)
    perfiles = cargar_perfiles(ruta, cfg.p_fv_mw)

    print("\nConfiguración leída:")
    for k, v in asdict(cfg).items():
        print(f"  {k:24s} = {v}")

    try:
        bess_base = calcular_metricas_bess_diseno(cfg.p_bess_mw, cfg.n_containers,
                                                  cfg.e_container_mwh, cfg.soc_min, cfg.soc_max)
        print("\nBESS actual (diseño):")
        print(f"  P instalada                 = {bess_base['p_bess_mw']:.6f} MW")
        print(f"  E instalada                 = {bess_base['e_bess_mwh']:.6f} MWh")
        print(f"  Duración nominal E/P        = {bess_base['horas_nominales']:.3f} h")
        print(f"  Duración útil BOL por SOC   = {bess_base['horas_utiles_bol']:.3f} h")
        print(f"  CAPEX energía BESS          = ${bess_base['capex_bess_energia_usd']:,.0f}")
        print(f"  CAPEX potencia BESS         = ${bess_base['capex_bess_potencia_usd']:,.0f}")
    except ValueError as exc:
        print(f"\nAVISO BESS actual: {exc}")

    if abs(cfg.p_contratada_mw - P_CONTRATADA_FIJA_MW) > 1e-9:
        print(f"\nAVISO: el Excel tiene P contratada={cfg.p_contratada_mw} MW, pero la optimización usará {P_CONTRATADA_FIJA_MW} MW por criterio docente.")

    # -------------------------------------------------------------------------
    # ETAPAS 1 y 2: año 1 + horizonte de 20 años
    # -------------------------------------------------------------------------
    carpeta_salida = ruta.parent
    detalle_20_precalculado = None
    costo_total_20_precalculado = None
    plan_degradacion_v11 = None

    if args.despacho_multianual:
        print("\nPreparando V11: reserva técnica de degradación para los 20 años...")
        (
            detalle_20_precalculado,
            costo_total_20_precalculado,
            resultado_1,
            resumen_1,
            plan_degradacion_v11,
        ) = simular_20_anios_consciente_degradacion(
            perfiles,
            p_fv_mw=cfg.p_fv_mw,
            n_aeros=cfg.n_aeros,
            p_bess_mw=cfg.p_bess_mw,
            e_bess_mwh=cfg.e_bess_mwh,
            p_contratada_mw=cfg.p_contratada_mw,
            tipo_aero=args.tipo_aero,
            eta_carga=cfg.eta_carga,
            eta_descarga=cfg.eta_descarga,
            soc_min=cfg.soc_min,
            soc_max=cfg.soc_max,
            soc_inicial_frac=cfg.soc_inicial_frac,
            limite_t1_mw=cfg.limite_t1_mw,
            exportar_excedente=not args.sin_exportar,
        )
        resumen_1["soh_minimo_tecnico"] = float(plan_degradacion_v11.iloc[0]["SOH mínimo técnico"])
        resumen_1["ciclos_maximos_permitidos_anio"] = float(
            detalle_20_precalculado.iloc[0]["Ciclos máximos permitidos año"]
        )
        resumen_1["despacho"] = "económico LP + reserva multianual de degradación"
    else:
        simulador_anio_1 = simular_anio_economico if args.despacho_economico else simular_anio
        resultado_1, resumen_1 = simulador_anio_1(
            perfiles,
            p_fv_mw=cfg.p_fv_mw,
            n_aeros=cfg.n_aeros,
            p_bess_mw=cfg.p_bess_mw,
            e_bess_mwh=cfg.e_bess_mwh,
            p_contratada_mw=cfg.p_contratada_mw,
            anio=1,
            soh_inicial=1.0,
            ciclos_acum_inicial=0.0,
            eta_carga=cfg.eta_carga,
            eta_descarga=cfg.eta_descarga,
            soc_min=cfg.soc_min,
            soc_max=cfg.soc_max,
            soc_inicial_frac=cfg.soc_inicial_frac,
            limite_t1_mw=cfg.limite_t1_mw,
            tipo_aero=args.tipo_aero,
            exportar_excedente=not args.sin_exportar,
        )

    imprimir_resumen_anio(resumen_1)
    if args.despacho_multianual:
        print(f"{'SOH mínimo técnico año 1':42s}: {resumen_1['soh_minimo_tecnico']:.6f}")
        print(f"{'Ciclos máximos permitidos año 1':42s}: {resumen_1['ciclos_maximos_permitidos_anio']:.6f}")
        print(f"{'Modo despacho':42s}: {resumen_1['despacho']}")

    salida_anio1 = carpeta_salida / "resultado_anio1_python.csv"
    resultado_1.to_csv(salida_anio1, index=False, decimal=".")
    print(f"\nDetalle horario año 1 guardado en:\n  {salida_anio1}")

    if plan_degradacion_v11 is not None:
        salida_plan = carpeta_salida / "plan_degradacion_multianual_v11.csv"
        plan_degradacion_v11.to_csv(salida_plan, index=False, decimal=".")
        print(f"Plan de degradación V11 guardado en:\n  {salida_plan}")

    # -------------------------------------------------------------------------
    # ETAPA 2: 20 años
    # -------------------------------------------------------------------------
    if args.simular_20:
        if args.despacho_multianual:
            detalle_20 = detalle_20_precalculado
            costo_total_20 = costo_total_20_precalculado
        else:
            detalle_20, costo_total_20 = simular_20_anios(
                perfiles,
                p_fv_mw=cfg.p_fv_mw,
                n_aeros=cfg.n_aeros,
                p_bess_mw=cfg.p_bess_mw,
                e_bess_mwh=cfg.e_bess_mwh,
                p_contratada_mw=cfg.p_contratada_mw,
                tipo_aero=args.tipo_aero,
                eta_carga=cfg.eta_carga,
                eta_descarga=cfg.eta_descarga,
                soc_min=cfg.soc_min,
                soc_max=cfg.soc_max,
                soc_inicial_frac=cfg.soc_inicial_frac,
                limite_t1_mw=cfg.limite_t1_mw,
                exportar_excedente=not args.sin_exportar,
                despacho_economico=args.despacho_economico,
            )

        salida_20 = carpeta_salida / "resumen_20_anios_python.csv"
        detalle_20.to_csv(salida_20, index=False, decimal=".")

        capex = calcular_capex(
            cfg.p_fv_mw,
            cfg.n_aeros,
            cfg.p_bess_mw,
            cfg.e_bess_mwh,
            args.tipo_aero,
        )

        print("\n" + "=" * 80)
        print("RESUMEN ECONÓMICO 20 AÑOS")
        print("=" * 80)
        if args.despacho_multianual:
            print("Modo                               : económico + reserva multianual de degradación")
        elif args.despacho_economico:
            print("Modo                               : económico LP anual (miope)")
        else:
            print("Modo                               : técnico heurístico")
        print(f"CAPEX total [USD]                 : {capex.total_usd:,.2f}")
        print(f"VP costos años 1-20 [USD]         : {detalle_20['VP flujo anual [USD]'].sum():,.2f}")
        print(f"COSTO TOTAL 20 AÑOS [USD]         : {costo_total_20:,.2f}")
        print(f"Ciclos equivalentes acumulados    : {detalle_20.iloc[-1]['Ciclos equivalentes acumulados']:,.6f}")
        print(f"SOH final año 20                  : {detalle_20.iloc[-1]['SOH final']:.6f}")
        print(f"Horas totales sin abastecer       : {int(detalle_20['Horas no cumple'].sum())}")
        print(f"Todos los años cumplen demanda    : {bool(detalle_20['Cumple demanda'].all())}")
        if args.despacho_multianual:
            print(f"SOH técnico mínimo año 20         : {detalle_20.iloc[-1]['SOH mínimo técnico']:.6f}")
        print(f"\nResumen anual guardado en:\n  {salida_20}")

    # -------------------------------------------------------------------------
    # ETAPA 3: optimización de cuatro variables por grilla; P contratada fija
    # -------------------------------------------------------------------------
    if args.optimizar:
        faltantes = []
        if args.fv_valores is None:
            faltantes.append("--fv-valores")
        if args.aeros_valores is None:
            faltantes.append("--aeros-valores")
        if args.pbess_valores is None:
            faltantes.append("--pbess-valores")
        if args.containers_valores is None:
            faltantes.append("--containers-valores")
        if faltantes:
            raise ValueError(
                "Para --optimizar tenés que indicar la grilla de las cuatro variables. "
                "Faltan: " + ", ".join(faltantes)
            )

        valores_fv = _parsear_lista_numerica(args.fv_valores)
        valores_aeros = _parsear_lista_numerica(args.aeros_valores, enteros=True)
        valores_pbess = _parsear_lista_numerica(args.pbess_valores)
        valores_containers = _parsear_lista_numerica(args.containers_valores, enteros=True)

        tabla_opt, mejor = optimizar_grilla(
            perfiles,
            valores_fv=valores_fv,
            valores_aeros=valores_aeros,
            valores_pbess=valores_pbess,
            valores_containers=valores_containers,
            p_contratada_mw=P_CONTRATADA_FIJA_MW,
            e_container_mwh=cfg.e_container_mwh,
            potencia_modulo_fv_w=args.pot_modulo_fv_w,
            pitch_fv_m=args.pitch_fv_m,
            tipo_aero=args.tipo_aero,
            eta_carga=cfg.eta_carga,
            eta_descarga=cfg.eta_descarga,
            soc_min=cfg.soc_min,
            soc_max=cfg.soc_max,
            soc_inicial_frac=cfg.soc_inicial_frac,
            limite_t1_mw=cfg.limite_t1_mw,
            exportar_excedente=not args.sin_exportar,
            despacho_economico=args.despacho_economico,
        )

        salida_opt = carpeta_salida / "resultados_optimizacion_grilla_v11.csv"
        tabla_opt.to_csv(salida_opt, index=False, decimal=".")
        print(f"\nResultados de la grilla guardados en:\n  {salida_opt}")

        if mejor is None:
            print("\nNo apareció ninguna configuración factible en la grilla indicada.")
        else:
            print("\n" + "=" * 80)
            print("MEJOR CONFIGURACIÓN DE LA GRILLA")
            print("=" * 80)
            for k, v in mejor.items():
                if isinstance(v, float):
                    print(f"{k:38s}: {v:,.6f}")
                else:
                    print(f"{k:38s}: {v}")


# =============================================================================
# V12 - OPTIMIZACIÓN CONTINUA/MIXTA
# =============================================================================

def _screening_potencia_rapido(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    limite_t1_mw: float,
    tipo_aero: Literal["GE3.4", "GE3.8"],
) -> bool:
    """Condición necesaria barata usando el año 20 (FV más degradado)."""
    factor_fv = factor_degradacion_fv(20)
    fv = np.minimum(p_fv_mw * perfiles["fv_pu_sin_limite"].to_numpy(float), limite_t1_mw) * factor_fv
    if tipo_aero == "GE3.4":
        eol = n_aeros * perfiles["eolico_34_por_aero_mw"].to_numpy(float)
    else:
        eol = n_aeros * perfiles["eolico_38_por_aero_mw"].to_numpy(float)
    deficit = np.maximum(perfiles["demanda_mw"].to_numpy(float) - fv - eol, 0.0)
    requerida = np.maximum(deficit - min(P_CONTRATADA_FIJA_MW, limite_t1_mw), 0.0)
    return bool(np.max(requerida) <= p_bess_mw + 1e-9)


def evaluar_configuracion_v12(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    n_containers: int,
    cfg_base: Configuracion,
    potencia_modulo_fv_w: float,
    pitch_fv_m: float,
    tipo_aero: Literal["GE3.4", "GE3.8"],
    exportar_excedente: bool,
    devolver_detalle_anio1: bool = False,
) -> tuple[dict, pd.DataFrame, pd.DataFrame | None, pd.DataFrame]:
    """Evaluación exacta V12 de un diseño candidato."""
    p_fv_mw = float(p_fv_mw)
    p_bess_mw = float(p_bess_mw)
    n_aeros = int(n_aeros)
    n_containers = int(n_containers)
    e_bess_mwh = n_containers * cfg_base.e_container_mwh

    if p_fv_mw < 0 or p_bess_mw < 0 or n_aeros < 0 or n_containers < 0:
        raise ValueError("Variables de diseño negativas.")
    if n_aeros > N_AEROS_MAX_ESPACIO:
        raise ValueError("Cantidad de aerogeneradores supera el máximo espacial de screening.")

    # Caso sin BESS: P_BESS se fuerza a cero; no se inventa energía/capacidad.
    if n_containers == 0:
        p_bess_mw = 0.0
        e_bess_mwh = 0.0
    else:
        if p_bess_mw <= 1e-6:
            raise ValueError("Hay containers BESS pero P_BESS es prácticamente cero.")
        if p_bess_mw > P_RATE_MAX * e_bess_mwh + 1e-9:
            raise ValueError("P_BESS supera el límite 0,5C.")

    espacio = calcular_screening_espacial(
        p_fv_mw=p_fv_mw,
        n_aeros=n_aeros,
        n_containers=n_containers,
        potencia_modulo_w=potencia_modulo_fv_w,
        pitch_fv_m=pitch_fv_m,
    )
    if not espacio["cumple_screening_espacial"]:
        raise ValueError("No cumple screening espacial conjunto eólico + FV + BESS.")

    # Screening de potencia necesario antes de resolver 20 LP horarios.
    if not _screening_potencia_rapido(
        perfiles,
        p_fv_mw=p_fv_mw,
        n_aeros=n_aeros,
        p_bess_mw=p_bess_mw,
        limite_t1_mw=cfg_base.limite_t1_mw,
        tipo_aero=tipo_aero,
    ):
        raise ValueError("No alcanza la potencia instantánea para abastecer el año 20.")

    detalle_20, costo_total, detalle_h1, resumen_h1, plan = simular_20_anios_consciente_degradacion(
        perfiles,
        p_fv_mw=p_fv_mw,
        n_aeros=n_aeros,
        p_bess_mw=p_bess_mw,
        e_bess_mwh=e_bess_mwh,
        p_contratada_mw=P_CONTRATADA_FIJA_MW,
        tipo_aero=tipo_aero,
        eta_carga=cfg_base.eta_carga,
        eta_descarga=cfg_base.eta_descarga,
        soc_min=cfg_base.soc_min,
        soc_max=cfg_base.soc_max,
        soc_inicial_frac=cfg_base.soc_inicial_frac,
        limite_t1_mw=cfg_base.limite_t1_mw,
        exportar_excedente=exportar_excedente,
        wacc=WACC,
        devolver_detalle_anio1=devolver_detalle_anio1,
    )

    if not bool(detalle_20["Cumple demanda"].all()):
        raise ValueError("La configuración no abastece toda la demanda en 20 años.")

    bess = calcular_metricas_bess_diseno(
        p_bess_mw, n_containers, cfg_base.e_container_mwh, cfg_base.soc_min, cfg_base.soc_max
    ) if n_containers > 0 else calcular_metricas_bess_diseno(
        0.0, 0, cfg_base.e_container_mwh, cfg_base.soc_min, cfg_base.soc_max
    )
    capex = calcular_capex(p_fv_mw, n_aeros, p_bess_mw, e_bess_mwh, tipo_aero)

    resumen = {
        "P_FV [MW]": p_fv_mw,
        "N aeros": n_aeros,
        "P_EOL instalada [MW]": n_aeros * P_NOMINAL_AERO_MW[tipo_aero],
        "P_BESS [MW]": p_bess_mw,
        "N containers BESS": n_containers,
        "E_BESS [MWh]": e_bess_mwh,
        "Duración BESS nominal [h]": bess["horas_nominales"],
        "Duración BESS útil BOL [h]": bess["horas_utiles_bol"],
        "CAPEX FV [USD]": capex.fv_usd,
        "CAPEX eólico [USD]": capex.eolico_usd,
        "CAPEX BESS energía [USD]": bess["capex_bess_energia_usd"],
        "CAPEX BESS potencia [USD]": bess["capex_bess_potencia_usd"],
        "CAPEX BESS total [USD]": bess["capex_bess_total_usd"],
        "CAPEX total [USD]": capex.total_usd,
        "VP operación 20a [USD]": float(detalle_20["VP flujo anual [USD]"].sum()),
        "Costo total 20a [USD]": float(costo_total),
        "Horas no cumple 20a": int(detalle_20["Horas no cumple"].sum()),
        "Energía no abastecida 20a [MWh]": float(detalle_20["Demanda no abastecida [MWh]"].sum()),
        "Ciclos acumulados año 20": float(detalle_20.iloc[-1]["Ciclos equivalentes acumulados"]),
        "SOH final año 20": float(detalle_20.iloc[-1]["SOH final"]),
        "EOL alcanzado": bool(detalle_20["EOL alcanzado"].any()),
        "Exportación 20a [MWh]": float(detalle_20["Exportación [MWh]"].sum()),
        "Potencia módulo FV [W]": potencia_modulo_fv_w,
        "Pitch FV [m]": espacio["pitch_fv_m"],
        "GCR FV": espacio["gcr_fv"],
        "N módulos FV": espacio["n_modulos_fv"],
        "Área FV terreno [m2]": espacio["area_fv_terreno_m2"],
        "Área BESS screening [m2]": espacio["area_bess_m2"],
        "Área eólica reservada screening [m2]": espacio["area_eolica_reservada_m2"],
        "Área residual tras eólica [m2]": espacio["area_residual_tras_eolica_m2"],
        "Área total screening [m2]": espacio["area_total_screening_m2"],
        "Uso terreno total screening [%]": espacio["uso_area_total_screening_pct"],
        "Factible": True,
    }
    return resumen, detalle_20, detalle_h1, plan




def _credito_arbitraje_surrogate_v12(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    e_bess_mwh: float,
    soh: float,
    anio: int,
    cfg_base: Configuracion,
    tipo_aero: Literal["GE3.4", "GE3.8"],
) -> tuple[float,float]:
    """
    Potencial económico diario de desplazar energía hacia Pico y luego Resto.
    Es sólo un crédito de ranking para la exploración: el despacho final se resuelve
    con LP en procesos exactos independientes.
    """
    if e_bess_mwh<=1e-12 or p_bess_mw<=1e-12:
        return 0.0,0.0
    demanda=perfiles["demanda_mw"].to_numpy(float)
    banda=perfiles["banda"].to_numpy(object)
    fv=np.minimum(p_fv_mw*perfiles["fv_pu_sin_limite"].to_numpy(float),cfg_base.limite_t1_mw)*factor_degradacion_fv(anio)
    if tipo_aero=="GE3.4":
        eol=n_aeros*perfiles["eolico_34_por_aero_mw"].to_numpy(float)
    else:
        eol=n_aeros*perfiles["eolico_38_por_aero_mw"].to_numpy(float)
    net=demanda-fv-eol
    deficit=np.maximum(net,0.0); excedente=np.maximum(-net,0.0)
    req_obl=np.maximum(deficit-P_CONTRATADA_FIJA_MW,0.0)
    p_econ_disp=np.maximum(p_bess_mw-req_obl,0.0)
    necesidad_econ=np.minimum(np.minimum(deficit,P_CONTRATADA_FIJA_MW),p_econ_disp)
    headroom=np.maximum(P_CONTRATADA_FIJA_MW-deficit,0.0)
    carga_red_cap=np.minimum(headroom,p_bess_mw)
    carga_ren_cap=np.minimum(excedente,p_bess_mw)
    usable_terminal=e_bess_mwh*soh*(cfg_base.soc_max-cfg_base.soc_min)*cfg_base.eta_descarga
    esc=(1.0+ESCALAMIENTO_COSTOS)**(anio-1)
    tval,tres,tpico=32.0*esc,65.0*esc,125.0*esc
    ahorro=0.0; salida=0.0
    for dia in range(366):
        sl=slice(dia*24,(dia+1)*24)
        b=banda[sl]
        ren_term=float(carga_ren_cap[sl].sum())*cfg_base.eta_carga*cfg_base.eta_descarga
        val_term=float(carga_red_cap[sl][b=="Valle"].sum())*cfg_base.eta_carga*cfg_base.eta_descarga
        energia=min(usable_terminal,ren_term+val_term)
        need_pico=float(necesidad_econ[sl][b=="Pico"].sum())
        need_resto=float(necesidad_econ[sl][b=="Resto"].sum())
        q_pico=min(energia,need_pico)
        q_resto=min(max(0.0,energia-q_pico),need_resto)
        q=q_pico+q_resto
        libre=min(q,ren_term)
        pagada=max(0.0,q-libre)
        evitado=q_pico*tpico+q_resto*tres
        costo_carga=pagada/(cfg_base.eta_carga*cfg_base.eta_descarga)*tval
        ahorro+=max(0.0,evitado-costo_carga)
        salida+=q
    ciclos=(salida/cfg_base.eta_descarga)/(DOD_CICLO_REFERENCIA*e_bess_mwh)
    return float(ahorro),float(ciclos)


def evaluar_surrogado_v12(
    perfiles: pd.DataFrame,
    *,
    p_fv_mw: float,
    n_aeros: int,
    p_bess_mw: float,
    n_containers: int,
    cfg_base: Configuracion,
    potencia_modulo_fv_w: float,
    pitch_fv_m: float,
    tipo_aero: Literal["GE3.4", "GE3.8"],
    exportar_excedente: bool,
) -> tuple[float, dict]:
    """
    Surrogate V12 SIN LP, para que Differential Evolution sea rápido y para no dejar
    estado de HiGHS antes de la validación exacta.

    Base: simulación técnica de los 20 años + un crédito conservador (35 %) del
    potencial de arbitraje Valle -> Pico/Resto. El 35 % evita adjudicar a la batería
    todo el arbitraje teórico, ya que el modelo exacto debe reservar ciclos/SOH futuro.

    El surrogate sólo ORDENA candidatos. El costo que se reporta como resultado final
    siempre proviene del modelo exacto multianual V12.
    """
    p_fv_mw=float(p_fv_mw); p_bess_mw=float(p_bess_mw)
    n_aeros=int(n_aeros); n_containers=int(n_containers)
    e_bess_mwh=n_containers*cfg_base.e_container_mwh
    if n_containers==0:
        p_bess_mw=0.0;e_bess_mwh=0.0
    elif p_bess_mw<=1e-6 or p_bess_mw>P_RATE_MAX*e_bess_mwh+1e-9:
        raise ValueError("BESS fuera de límites físicos.")
    espacio=calcular_screening_espacial(
        p_fv_mw=p_fv_mw,n_aeros=n_aeros,n_containers=n_containers,
        potencia_modulo_w=potencia_modulo_fv_w,pitch_fv_m=pitch_fv_m)
    if not espacio["cumple_screening_espacial"]:
        raise ValueError("No cumple screening espacial.")
    if not _screening_potencia_rapido(
        perfiles,p_fv_mw=p_fv_mw,n_aeros=n_aeros,p_bess_mw=p_bess_mw,
        limite_t1_mw=cfg_base.limite_t1_mw,tipo_aero=tipo_aero):
        raise ValueError("No alcanza potencia instantánea en año 20.")

    detalle,costo_tecnico=simular_20_anios(
        perfiles,p_fv_mw=p_fv_mw,n_aeros=n_aeros,p_bess_mw=p_bess_mw,
        e_bess_mwh=e_bess_mwh,p_contratada_mw=P_CONTRATADA_FIJA_MW,
        tipo_aero=tipo_aero,eta_carga=cfg_base.eta_carga,eta_descarga=cfg_base.eta_descarga,
        soc_min=cfg_base.soc_min,soc_max=cfg_base.soc_max,soc_inicial_frac=cfg_base.soc_inicial_frac,
        limite_t1_mw=cfg_base.limite_t1_mw,exportar_excedente=exportar_excedente,
        wacc=WACC,despacho_economico=False)
    if not bool(detalle["Cumple demanda"].all()):
        raise ValueError("No abastece 20 años en screening técnico.")

    credito_vp=0.0;ciclos_pot=0.0
    if n_containers>0:
        for _,row in detalle.iterrows():
            y=int(row["Año"]);soh=float(row["SOH inicio"])
            ah,cy=_credito_arbitraje_surrogate_v12(
                perfiles,p_fv_mw=p_fv_mw,n_aeros=n_aeros,p_bess_mw=p_bess_mw,
                e_bess_mwh=e_bess_mwh,soh=soh,anio=y,cfg_base=cfg_base,tipo_aero=tipo_aero)
            credito_vp+=ah/(1.0+WACC)**y;ciclos_pot+=cy
    FRACCION_CREDITO=0.35
    costo_sur=float(costo_tecnico-FRACCION_CREDITO*credito_vp)
    return costo_sur,{
        "P_FV [MW]":p_fv_mw,"N aeros":n_aeros,"P_BESS [MW]":p_bess_mw,
        "N containers BESS":n_containers,"E_BESS [MWh]":e_bess_mwh,
        "Costo surrogate 20a [USD]":costo_sur,"Costo técnico 20a [USD]":float(costo_tecnico),
        "Crédito arbitraje potencial VP [USD]":float(credito_vp),
        "Ciclos económicos potenciales 20a":float(ciclos_pot),
        "Uso terreno total screening [%]":float(espacio["uso_area_total_screening_pct"]),
    }


def optimizar_mixto_v12(
    perfiles: pd.DataFrame,
    *,
    cfg_base: Configuracion,
    ruta_excel: Path,
    fv_min: float,
    fv_max: float,
    pbess_min: float,
    pbess_max: float,
    aeros_min: int,
    aeros_max: int,
    containers_min: int,
    containers_max: int,
    potencia_modulo_fv_w: float,
    pitch_fv_m: float,
    tipo_aero: Literal["GE3.4", "GE3.8"],
    exportar_excedente: bool,
    maxiter: int,
    popsize: int,
    seed: int,
    tol: float,
    refinar: bool,
    n_finalistas: int = 6,
    objetivo_exacto_directo: bool = False,
) -> tuple[dict, pd.DataFrame, object]:
    """
    V12 en dos etapas por defecto:
      A) Differential Evolution mixto sobre un surrogate económico rápido;
      B) reevaluación EXACTA multianual V12 de los mejores finalistas.

    Con objetivo_exacto_directo=True, Differential Evolution llama al modelo exacto en
    cada candidato (mucho más lento, útil sólo para una corrida final exhaustiva).
    """
    if fv_max <= fv_min or pbess_max < pbess_min:
        raise ValueError("Intervalos continuos inválidos.")
    if not (0 <= aeros_min <= aeros_max <= N_AEROS_MAX_ESPACIO):
        raise ValueError(f"aeros debe quedar entre 0 y {N_AEROS_MAX_ESPACIO}.")
    if not (0 <= containers_min <= containers_max):
        raise ValueError("Rango de containers inválido.")

    bounds=[(float(fv_min),float(fv_max)),(float(aeros_min),float(aeros_max)),
            (float(pbess_min),float(pbess_max)),(float(containers_min),float(containers_max))]
    integrality=[False,True,False,True]
    cache:dict[tuple,float]={}
    explorados:list[dict]=[]
    mejor_sur=math.inf
    t0=time.time(); contador=0

    def key(pfv,na,pb,nc): return (round(float(pfv),4),int(na),round(float(pb),4),int(nc))

    def objetivo(x):
        nonlocal contador,mejor_sur
        contador+=1
        pfv=float(x[0]); na=int(round(x[1])); pb=float(x[2]); nc=int(round(x[3]))
        if nc==0: pb=0.0
        k=key(pfv,na,pb,nc)
        if k in cache: return cache[k]
        e=nc*cfg_base.e_container_mwh
        if nc>0 and (pb<=1e-6 or pb>P_RATE_MAX*e+1e-9):
            val=1e11+1e8*max(0,pb-P_RATE_MAX*e)
            cache[k]=val; return val
        try:
            if objetivo_exacto_directo:
                rr,_,_,_=evaluar_configuracion_v12(
                    perfiles,p_fv_mw=pfv,n_aeros=na,p_bess_mw=pb,n_containers=nc,
                    cfg_base=cfg_base,potencia_modulo_fv_w=potencia_modulo_fv_w,
                    pitch_fv_m=pitch_fv_m,tipo_aero=tipo_aero,
                    exportar_excedente=exportar_excedente,devolver_detalle_anio1=False)
                val=float(rr["Costo total 20a [USD]"])
                row={"P_FV [MW]":pfv,"N aeros":na,"P_BESS [MW]":pb,
                     "N containers BESS":nc,"Costo surrogate 20a [USD]":val}
            else:
                val,row=evaluar_surrogado_v12(
                    perfiles,p_fv_mw=pfv,n_aeros=na,p_bess_mw=pb,n_containers=nc,
                    cfg_base=cfg_base,potencia_modulo_fv_w=potencia_modulo_fv_w,
                    pitch_fv_m=pitch_fv_m,tipo_aero=tipo_aero,
                    exportar_excedente=exportar_excedente)
            cache[k]=val
            row=dict(row); row["Evaluación"]=contador; row["Tiempo acumulado [min]"]=(time.time()-t0)/60
            explorados.append(row)
            if val<mejor_sur:
                mejor_sur=val
                print(f"  nuevo mejor exploración #{contador}: ${val:,.0f} | FV={pfv:.4f} | aeros={na} | BESS={pb:.4f} MW / {e:.3f} MWh")
            return val
        except (ValueError,RuntimeError):
            cache[k]=1e11; return 1e11

    print("\n"+"="*80)
    print("V12 - OPTIMIZACIÓN CONTINUA/MIXTA DEL DISEÑO")
    print("="*80)
    print(f"P_FV continua       : [{fv_min:g}, {fv_max:g}] MW")
    print(f"N aeros entero      : [{aeros_min}, {aeros_max}]")
    print(f"P_BESS continua     : [{pbess_min:g}, {pbess_max:g}] MW")
    print(f"N containers entero : [{containers_min}, {containers_max}]")
    print(f"P contratada fija   : {P_CONTRATADA_FIJA_MW:g} MW")
    print("SOC anual           : cíclico (SOC final = SOC inicial)")
    print("Degradación         : FV anual + BESS por ciclos")
    print("Objetivo             : mínimo costo total descontado a 20 años")
    print("Vector inicial       : población automática; NO usa la configuración del Excel")
    print("Modo                 : "+("EXACTO directo (lento)" if objetivo_exacto_directo else f"2 etapas; {n_finalistas} finalistas exactos"))

    res=differential_evolution(objetivo,bounds=bounds,integrality=integrality,
        maxiter=int(maxiter),popsize=int(popsize),tol=float(tol),seed=int(seed),
        polish=False,updating="immediate",workers=1,disp=True)

    # Opcional: pulido sobre surrogate con enteras fijas (rápido). La validación final sigue siendo exacta.
    if refinar and explorados:
        best_sur=min(explorados,key=lambda r:r["Costo surrogate 20a [USD]"])
        na=int(best_sur["N aeros"]); nc=int(best_sur["N containers BESS"])
        maxpb=0.0 if nc==0 else min(pbess_max,P_RATE_MAX*nc*cfg_base.e_container_mwh)
        if nc==0:
            pb0=0.0
        else:
            pb0=min(max(float(best_sur["P_BESS [MW]"]),max(pbess_min,1e-4)),maxpb)
        def o2(z): return objetivo([z[0],na,z[1],nc])
        if nc==0:
            # sólo P_FV tiene sentido
            from scipy.optimize import minimize_scalar
            rr=minimize_scalar(lambda z:objetivo([z,na,0.0,nc]),bounds=(fv_min,fv_max),method="bounded",options={"maxiter":12,"xatol":0.01})
        elif maxpb>=max(pbess_min,1e-4):
            minimize(o2,[best_sur["P_FV [MW]"],pb0],method="Powell",
                     bounds=[(fv_min,fv_max),(max(pbess_min,1e-4),maxpb)],
                     options={"maxiter":8,"xtol":0.01,"ftol":5e-4,"disp":False})

    if not explorados:
        raise RuntimeError("No apareció ningún candidato factible durante la exploración.")

    # Seleccionar finalistas DIVERSOS. Primero toma el mejor global y luego, cuando
    # existen, el mejor de cada cantidad de aerogeneradores. Así el surrogate no puede
    # hacer que todos los finalistas sean clones con el mismo N_aeros.
    exp=pd.DataFrame(explorados).sort_values("Costo surrogate 20a [USD]").reset_index(drop=True)
    finalistas=[]; vistos=set(); aeros_cubiertos=set()
    def agregar(r):
        k=(round(float(r["P_FV [MW]"]),3),int(r["N aeros"]),round(float(r["P_BESS [MW]"]),3),int(r["N containers BESS"]))
        if k in vistos:return False
        vistos.add(k);finalistas.append(r);aeros_cubiertos.add(int(r["N aeros"]));return True
    agregar(exp.iloc[0])
    for na in sorted(exp["N aeros"].astype(int).unique()):
        if len(finalistas)>=max(1,int(n_finalistas)):break
        if na in aeros_cubiertos:continue
        sub=exp[exp["N aeros"].astype(int)==na]
        if not sub.empty:agregar(sub.iloc[0])
    # Completar con los siguientes mejores, priorizando combinaciones (aeros,containers) nuevas.
    pares={(int(r["N aeros"]),int(r["N containers BESS"])) for r in finalistas}
    for _,r in exp.iterrows():
        if len(finalistas)>=max(1,int(n_finalistas)):break
        par=(int(r["N aeros"]),int(r["N containers BESS"]))
        if par in pares:continue
        if agregar(r):pares.add(par)
    for _,r in exp.iterrows():
        if len(finalistas)>=max(1,int(n_finalistas)):break
        agregar(r)

    print(f"\nEtapa exacta: reevaluando {len(finalistas)} finalistas con los 20 años completos...")
    # IMPORTANTE: las evaluaciones exactas se ejecutan en procesos Python limpios.
    # Tras muchas llamadas a HiGHS durante Differential Evolution, algunos entornos
    # pueden degradar mucho su rendimiento. El subproceso evita ese problema y hace
    # reproducible el tiempo de cada finalista.
    exactos=[]; extras={}
    with tempfile.TemporaryDirectory(prefix="v12_finalistas_") as td:
        td=Path(td)
        for j,r in enumerate(finalistas,1):
            pfv=float(r["P_FV [MW]"]); na=int(r["N aeros"]); pb=float(r["P_BESS [MW]"]); nc=int(r["N containers BESS"])
            if nc==0: pb=0.0
            pref=td/f"cand_{j}"
            cmd=[
                sys.executable,str(Path(__file__).resolve()),
                "--excel",str(ruta_excel),
                "--tipo-aero",tipo_aero,
                "--pot-modulo-fv-w",str(potencia_modulo_fv_w),
                "--pitch-fv-m",str(pitch_fv_m),
                "--evaluar-candidato-interno",
                "--cand-pfv",str(pfv),"--cand-aeros",str(na),
                "--cand-pbess",str(pb),"--cand-containers",str(nc),
                "--cand-prefix",str(pref),
            ]
            if not exportar_excedente:
                cmd.append("--sin-exportar")
            proc=subprocess.run(cmd,capture_output=True,text=True)
            if proc.returncode!=0:
                msg=(proc.stderr or proc.stdout or "error desconocido").strip().splitlines()[-1]
                print(f"  finalista {j}: descartado en validación exacta ({msg})")
                continue
            try:
                rr=json.loads((Path(str(pref)+"_resumen.json")).read_text(encoding="utf-8"))
                d20=pd.read_csv(Path(str(pref)+"_20a.csv"))
                dh1=pd.read_csv(Path(str(pref)+"_anio1.csv"))
                plan=pd.read_csv(Path(str(pref)+"_plan.csv"))
            except Exception as exc:
                print(f"  finalista {j}: no pude leer salida exacta ({exc})")
                continue
            rr["Costo surrogate 20a [USD]"]=float(r["Costo surrogate 20a [USD]"])
            rr["_extra_id"]=len(exactos)
            extras[len(exactos)]=(d20,dh1,plan)
            exactos.append(rr)
            print(f"  finalista {j}: EXACTO=${rr['Costo total 20a [USD]']:,.0f} | FV={pfv:.4f} | aeros={na} | BESS={pb:.4f}/{nc*cfg_base.e_container_mwh:.3f}")
    if not exactos:
        raise RuntimeError("Ningún finalista superó la validación exacta V12. Aumentá --maxiter/--popsize.")

    tex=pd.DataFrame(exactos).sort_values("Costo total 20a [USD]").reset_index(drop=True)
    extra_id=int(tex.iloc[0]["_extra_id"])
    mejor_det=dict(tex.iloc[0])
    mejor_det.pop("_extra_id",None)
    detalle20,detalle_h1,plan=extras[extra_id]
    tex=tex.drop(columns=["_extra_id"])
    return mejor_det,tex,(res,detalle20,detalle_h1,plan,exp)



# =============================================================================
# V13 - OPTIMIZACIÓN POR FAMILIAS DISCRETAS + INFORME FINAL DETALLADO
# =============================================================================

def _json_safe_v13(v):
    if isinstance(v, (np.floating, np.integer)):
        return v.item()
    if isinstance(v, np.bool_):
        return bool(v)
    if isinstance(v, float) and (math.isnan(v) or math.isinf(v)):
        return None
    return v


def _evaluar_exacto_subproceso_v13(
    *,
    ruta_excel: Path,
    pfv: float,
    na: int,
    pbess: float,
    nc: int,
    tipo_aero: Literal["GE3.4", "GE3.8"],
    potencia_modulo_fv_w: float,
    pitch_fv_m: float,
    exportar_excedente: bool,
    carpeta_tmp: Path,
    etiqueta: str,
) -> tuple[dict, pd.DataFrame, pd.DataFrame | None, pd.DataFrame] | None:
    """Evalúa un candidato exacto en un proceso limpio (HiGHS/LP estable)."""
    pref = carpeta_tmp / etiqueta
    cmd = [
        sys.executable, str(Path(__file__).resolve()),
        "--excel", str(ruta_excel),
        "--tipo-aero", tipo_aero,
        "--pot-modulo-fv-w", str(potencia_modulo_fv_w),
        "--pitch-fv-m", str(pitch_fv_m),
        "--evaluar-candidato-interno",
        "--cand-pfv", str(float(pfv)),
        "--cand-aeros", str(int(na)),
        "--cand-pbess", str(float(pbess)),
        "--cand-containers", str(int(nc)),
        "--cand-prefix", str(pref),
    ]
    if not exportar_excedente:
        cmd.append("--sin-exportar")
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode != 0:
        return None
    try:
        rr = json.loads(Path(str(pref) + "_resumen.json").read_text(encoding="utf-8"))
        d20 = pd.read_csv(Path(str(pref) + "_20a.csv"))
        plan = pd.read_csv(Path(str(pref) + "_plan.csv"))
        h1_path = Path(str(pref) + "_anio1.csv")
        dh1 = pd.read_csv(h1_path) if h1_path.exists() else None
    except Exception:
        return None
    return rr, d20, dh1, plan


def _candidatos_diversos_familia_v13(explorados: list[dict], cantidad: int = 3) -> list[dict]:
    """Toma los mejores surrogate de una familia evitando candidatos prácticamente clonados."""
    if not explorados:
        return []
    df = pd.DataFrame(explorados).sort_values("Costo surrogate 20a [USD]")
    elegidos: list[dict] = []
    for _, r in df.iterrows():
        cand = dict(r)
        if not elegidos:
            elegidos.append(cand)
        else:
            separado = all(
                abs(float(cand["P_FV [MW]"]) - float(e["P_FV [MW]"])) >= 0.35
                or abs(float(cand["P_BESS [MW]"]) - float(e["P_BESS [MW]"])) >= 0.25
                for e in elegidos
            )
            if separado:
                elegidos.append(cand)
        if len(elegidos) >= max(1, int(cantidad)):
            break
    return elegidos


def _explorar_familia_surrogate_v13(
    perfiles: pd.DataFrame,
    *,
    na: int,
    nc: int,
    cfg_base: Configuracion,
    fv_min: float,
    fv_max: float,
    pbess_min: float,
    pbess_max: float,
    potencia_modulo_fv_w: float,
    pitch_fv_m: float,
    tipo_aero: Literal["GE3.4", "GE3.8"],
    exportar_excedente: bool,
    maxiter: int,
    popsize: int,
    seed: int,
    tol: float,
    candidatos_guardar: int,
) -> tuple[list[dict], object | None]:
    """
    Explora P_FV/P_BESS sobre TODO el dominio continuo de una familia discreta fija.
    V13 no usa los rangos encontrados por V12 como límites.
    """
    na, nc = int(na), int(nc)
    e_bess = nc * cfg_base.e_container_mwh
    explorados: list[dict] = []
    cache: dict[tuple, float] = {}

    if nc == 0:
        max_pb = 0.0
        min_pb = 0.0
        bounds = [(float(fv_min), float(fv_max))]
    else:
        max_pb = min(float(pbess_max), P_RATE_MAX * e_bess)
        min_pb = max(float(pbess_min), 1e-3)
        if max_pb < min_pb - 1e-12:
            return [], None
        bounds = [(float(fv_min), float(fv_max)), (min_pb, max_pb)]

    def objetivo(z):
        pfv = float(z[0])
        pb = 0.0 if nc == 0 else float(z[1])
        k = (round(pfv, 4), round(pb, 4))
        if k in cache:
            return cache[k]
        try:
            val, row = evaluar_surrogado_v12(
                perfiles,
                p_fv_mw=pfv, n_aeros=na, p_bess_mw=pb, n_containers=nc,
                cfg_base=cfg_base,
                potencia_modulo_fv_w=potencia_modulo_fv_w,
                pitch_fv_m=pitch_fv_m,
                tipo_aero=tipo_aero,
                exportar_excedente=exportar_excedente,
            )
            row = dict(row)
            explorados.append(row)
            cache[k] = float(val)
            return float(val)
        except (ValueError, RuntimeError):
            cache[k] = 1e11
            return 1e11

    res = differential_evolution(
        objetivo,
        bounds=bounds,
        maxiter=int(maxiter), popsize=int(popsize), tol=float(tol),
        seed=int(seed), polish=False, updating="immediate", workers=1, disp=False,
    )
    return _candidatos_diversos_familia_v13(explorados, candidatos_guardar), res


def _refinar_familia_exacto_v13(
    *,
    mejor_inicial: dict,
    na: int,
    nc: int,
    cfg_base: Configuracion,
    ruta_excel: Path,
    fv_min: float,
    fv_max: float,
    pbess_min: float,
    pbess_max: float,
    tipo_aero: Literal["GE3.4", "GE3.8"],
    potencia_modulo_fv_w: float,
    pitch_fv_m: float,
    exportar_excedente: bool,
    carpeta_tmp: Path,
    rondas: int,
    paso_fv_inicial: float,
    paso_pbess_inicial: float,
    contador_inicio: int,
) -> tuple[dict, pd.DataFrame, pd.DataFrame | None, pd.DataFrame, list[dict], int]:
    """
    Refinamiento EXACTO local sólo después de haber explorado globalmente toda la familia.
    Usa búsqueda por coordenadas y reduce el paso en cada ronda. No impone un subdominio fijo.
    """
    actual = mejor_inicial
    d20_actual = actual.pop("_d20")
    dh1_actual = actual.pop("_dh1")
    plan_actual = actual.pop("_plan")
    hist: list[dict] = []
    contador = contador_inicio
    step_fv = float(paso_fv_inicial)
    step_pb = float(paso_pbess_inicial)
    max_pb_fis = 0.0 if nc == 0 else min(float(pbess_max), P_RATE_MAX * nc * cfg_base.e_container_mwh)
    min_pb_fis = 0.0 if nc == 0 else max(float(pbess_min), 1e-3)

    for ronda in range(max(0, int(rondas))):
        pf0 = float(actual["P_FV [MW]"])
        pb0 = float(actual["P_BESS [MW]"])
        puntos = [(pf0 - step_fv, pb0), (pf0 + step_fv, pb0)]
        if nc > 0:
            puntos += [(pf0, pb0 - step_pb), (pf0, pb0 + step_pb)]
        hubo_mejora = False
        for pfv, pb in puntos:
            pfv = min(max(float(pfv), float(fv_min)), float(fv_max))
            if nc == 0:
                pb = 0.0
            else:
                pb = min(max(float(pb), min_pb_fis), max_pb_fis)
            if abs(pfv - pf0) < 1e-9 and abs(pb - pb0) < 1e-9:
                continue
            contador += 1
            ev = _evaluar_exacto_subproceso_v13(
                ruta_excel=ruta_excel, pfv=pfv, na=na, pbess=pb, nc=nc,
                tipo_aero=tipo_aero, potencia_modulo_fv_w=potencia_modulo_fv_w,
                pitch_fv_m=pitch_fv_m, exportar_excedente=exportar_excedente,
                carpeta_tmp=carpeta_tmp, etiqueta=f"ref_{na}_{nc}_{contador}",
            )
            if ev is None:
                continue
            rr, d20, dh1, plan = ev
            rr["Etapa V13"] = f"refinamiento ronda {ronda+1}"
            hist.append(dict(rr))
            if float(rr["Costo total 20a [USD]"]) + 1e-6 < float(actual["Costo total 20a [USD]"]):
                actual = dict(rr)
                d20_actual, dh1_actual, plan_actual = d20, dh1, plan
                hubo_mejora = True
        step_fv *= 0.35
        step_pb *= 0.35
        # Aunque no haya mejora, una segunda escala más fina puede encontrar el mínimo cerca del centro.
    actual["_d20"] = d20_actual
    actual["_dh1"] = dh1_actual
    actual["_plan"] = plan_actual
    return actual, d20_actual, dh1_actual, plan_actual, hist, contador


def optimizar_por_familias_v13(
    perfiles: pd.DataFrame,
    *,
    cfg_base: Configuracion,
    ruta_excel: Path,
    fv_min: float,
    fv_max: float,
    pbess_min: float,
    pbess_max: float,
    aeros_min: int,
    aeros_max: int,
    containers_min: int,
    containers_max: int,
    potencia_modulo_fv_w: float,
    pitch_fv_m: float,
    tipo_aero: Literal["GE3.4", "GE3.8"],
    exportar_excedente: bool,
    maxiter_familia: int,
    popsize_familia: int,
    seed: int,
    tol: float,
    candidatos_surrogate_por_familia: int,
    exactos_por_familia: int,
    top_familias_refinar: int,
    rondas_refinamiento: int,
    paso_fv_refinar: float,
    paso_pbess_refinar: float,
) -> tuple[dict, pd.DataFrame, pd.DataFrame, pd.DataFrame, pd.DataFrame | None, pd.DataFrame]:
    """
    Estrategia V13:
      1) enumera TODAS las familias discretas (aeros, containers);
      2) en cada familia explora P_FV y P_BESS sobre el dominio continuo COMPLETO;
      3) valida exactamente al menos el mejor candidato de cada familia que el surrogate considera factible;
      4) refina exactamente las mejores familias globales.
    """
    if fv_max <= fv_min or pbess_max < pbess_min:
        raise ValueError("Intervalos continuos inválidos.")
    if not (0 <= aeros_min <= aeros_max <= N_AEROS_MAX_ESPACIO):
        raise ValueError(f"aeros debe quedar entre 0 y {N_AEROS_MAX_ESPACIO}.")
    if not (0 <= containers_min <= containers_max):
        raise ValueError("Rango de containers inválido.")

    familias = list(product(range(aeros_min, aeros_max + 1), range(containers_min, containers_max + 1)))
    print("\n" + "=" * 80)
    print("V13 - OPTIMIZACIÓN POR FAMILIAS DISCRETAS")
    print("=" * 80)
    print(f"Familias (N_aeros, N_containers): {len(familias)}")
    print(f"P_FV continua por familia        : [{fv_min:g}, {fv_max:g}] MW")
    print(f"P_BESS continua por familia      : [{pbess_min:g}, {pbess_max:g}] MW, limitada además por 0,5C")
    print("Dominio de refinamiento          : NO se recorta con resultados de V12")
    print("Validación                       : modelo exacto 20 años por familia factible")
    print("Objetivo                         : mínimo costo total descontado a 20 años")

    filas_familias: list[dict] = []
    hist_exacto: list[dict] = []
    exactos_familia: list[dict] = []
    contador_exacto = 0
    t0 = time.time()

    with tempfile.TemporaryDirectory(prefix="v13_familias_") as td:
        td = Path(td)
        for idx, (na, nc) in enumerate(familias, 1):
            print(f"\nFamilia {idx}/{len(familias)}: aeros={na}, containers={nc} (E={nc*cfg_base.e_container_mwh:.3f} MWh)")
            cands, _ = _explorar_familia_surrogate_v13(
                perfiles, na=na, nc=nc, cfg_base=cfg_base,
                fv_min=fv_min, fv_max=fv_max, pbess_min=pbess_min, pbess_max=pbess_max,
                potencia_modulo_fv_w=potencia_modulo_fv_w, pitch_fv_m=pitch_fv_m,
                tipo_aero=tipo_aero, exportar_excedente=exportar_excedente,
                maxiter=maxiter_familia, popsize=popsize_familia,
                seed=seed + 101*na + 17*nc, tol=tol,
                candidatos_guardar=max(candidatos_surrogate_por_familia, exactos_por_familia),
            )
            if not cands:
                filas_familias.append({
                    "N aeros": na, "N containers BESS": nc, "E_BESS [MWh]": nc*cfg_base.e_container_mwh,
                    "Factible surrogate": False, "Factible exacto": False,
                })
                print("  sin candidato factible en exploración global")
                continue

            best_sur = cands[0]
            exactos_local: list[tuple[dict, pd.DataFrame, pd.DataFrame | None, pd.DataFrame]] = []
            for j, cand in enumerate(cands[:max(1, int(exactos_por_familia))], 1):
                contador_exacto += 1
                pfv = float(cand["P_FV [MW]"])
                pb = 0.0 if nc == 0 else float(cand["P_BESS [MW]"])
                ev = _evaluar_exacto_subproceso_v13(
                    ruta_excel=ruta_excel, pfv=pfv, na=na, pbess=pb, nc=nc,
                    tipo_aero=tipo_aero, potencia_modulo_fv_w=potencia_modulo_fv_w,
                    pitch_fv_m=pitch_fv_m, exportar_excedente=exportar_excedente,
                    carpeta_tmp=td, etiqueta=f"fam_{na}_{nc}_{j}_{contador_exacto}",
                )
                if ev is None:
                    continue
                rr, d20, dh1, plan = ev
                rr["Costo surrogate 20a [USD]"] = float(cand["Costo surrogate 20a [USD]"])
                rr["Etapa V13"] = "validación familia"
                hist_exacto.append(dict(rr))
                exactos_local.append((rr, d20, dh1, plan))

            if not exactos_local:
                filas_familias.append({
                    "N aeros": na, "N containers BESS": nc, "E_BESS [MWh]": nc*cfg_base.e_container_mwh,
                    "Factible surrogate": True, "Factible exacto": False,
                    "P_FV mejor surrogate [MW]": float(best_sur["P_FV [MW]"]),
                    "P_BESS mejor surrogate [MW]": float(best_sur["P_BESS [MW]"]),
                    "Costo surrogate mejor [USD]": float(best_sur["Costo surrogate 20a [USD]"]),
                })
                print("  candidato surrogate no superó validación exacta")
                continue

            exactos_local.sort(key=lambda x: float(x[0]["Costo total 20a [USD]"]))
            rr, d20, dh1, plan = exactos_local[0]
            guardado = dict(rr)
            guardado["_d20"] = d20
            guardado["_dh1"] = dh1
            guardado["_plan"] = plan
            exactos_familia.append(guardado)
            filas_familias.append({
                "N aeros": na,
                "N containers BESS": nc,
                "E_BESS [MWh]": nc*cfg_base.e_container_mwh,
                "Factible surrogate": True,
                "Factible exacto": True,
                "P_FV mejor surrogate [MW]": float(best_sur["P_FV [MW]"]),
                "P_BESS mejor surrogate [MW]": float(best_sur["P_BESS [MW]"]),
                "Costo surrogate mejor [USD]": float(best_sur["Costo surrogate 20a [USD]"]),
                "P_FV exacto inicial [MW]": float(rr["P_FV [MW]"]),
                "P_BESS exacto inicial [MW]": float(rr["P_BESS [MW]"]),
                "Costo exacto inicial [USD]": float(rr["Costo total 20a [USD]"]),
                "Tiempo acumulado [min]": (time.time()-t0)/60.0,
            })
            print(f"  EXACTO=${float(rr['Costo total 20a [USD]']):,.0f} | FV={float(rr['P_FV [MW]']):.4f} MW | BESS={float(rr['P_BESS [MW]']):.4f} MW")

        if not exactos_familia:
            raise RuntimeError("Ninguna familia resultó factible en validación exacta V13.")

        # Refinar las mejores familias según COSTO EXACTO, no según surrogate.
        exactos_familia.sort(key=lambda r: float(r["Costo total 20a [USD]"]))
        top = exactos_familia[:max(0, min(int(top_familias_refinar), len(exactos_familia)))]
        if top and rondas_refinamiento > 0:
            print("\n" + "-"*80)
            print(f"Refinamiento EXACTO de las {len(top)} mejores familias por costo exacto")
            print("-"*80)
        refinados_por_par: dict[tuple[int,int], dict] = {}
        for k, ini in enumerate(top, 1):
            na = int(ini["N aeros"]); nc = int(ini["N containers BESS"])
            print(f"  refinando {k}/{len(top)}: aeros={na}, containers={nc}, costo inicial=${float(ini['Costo total 20a [USD]']):,.0f}")
            actual, d20, dh1, plan, hist, contador_exacto = _refinar_familia_exacto_v13(
                mejor_inicial=dict(ini), na=na, nc=nc, cfg_base=cfg_base,
                ruta_excel=ruta_excel, fv_min=fv_min, fv_max=fv_max,
                pbess_min=pbess_min, pbess_max=pbess_max,
                tipo_aero=tipo_aero, potencia_modulo_fv_w=potencia_modulo_fv_w,
                pitch_fv_m=pitch_fv_m, exportar_excedente=exportar_excedente,
                carpeta_tmp=td, rondas=rondas_refinamiento,
                paso_fv_inicial=paso_fv_refinar, paso_pbess_inicial=paso_pbess_refinar,
                contador_inicio=contador_exacto,
            )
            hist_exacto.extend(hist)
            refinados_por_par[(na,nc)] = actual
            print(f"    -> costo refinado=${float(actual['Costo total 20a [USD]']):,.0f} | FV={float(actual['P_FV [MW]']):.4f} | BESS={float(actual['P_BESS [MW]']):.4f}")

        # Sustituir candidatos iniciales por refinados donde corresponda.
        finales: list[dict] = []
        for ini in exactos_familia:
            par = (int(ini["N aeros"]), int(ini["N containers BESS"]))
            finales.append(refinados_por_par.get(par, ini))
        finales.sort(key=lambda r: float(r["Costo total 20a [USD]"]))
        mejor = finales[0]
        detalle20 = mejor.pop("_d20")
        detalle_h1 = mejor.pop("_dh1")
        plan = mejor.pop("_plan")

    # Completar tabla de familias con el resultado refinado, si existió.
    df_fam = pd.DataFrame(filas_familias)
    if not df_fam.empty:
        for par, rr in refinados_por_par.items():
            m = (df_fam["N aeros"].astype(int)==par[0]) & (df_fam["N containers BESS"].astype(int)==par[1])
            df_fam.loc[m, "P_FV refinado [MW]"] = float(rr["P_FV [MW]"])
            df_fam.loc[m, "P_BESS refinado [MW]"] = float(rr["P_BESS [MW]"])
            df_fam.loc[m, "Costo exacto refinado [USD]"] = float(rr["Costo total 20a [USD]"])
        # costo representativo final por familia
        if "Costo exacto refinado [USD]" in df_fam.columns:
            df_fam["Costo final familia [USD]"] = pd.to_numeric(df_fam["Costo exacto refinado [USD]"], errors="coerce")
        else:
            df_fam["Costo final familia [USD]"] = np.nan
        if "Costo exacto inicial [USD]" in df_fam.columns:
            base_cost = pd.to_numeric(df_fam["Costo exacto inicial [USD]"], errors="coerce")
            df_fam["Costo final familia [USD]"] = df_fam["Costo final familia [USD]"].where(df_fam["Costo final familia [USD]"].notna(), base_cost)
        df_fam = df_fam.sort_values("Costo final familia [USD]", na_position="last").reset_index(drop=True)

    df_hist = pd.DataFrame(hist_exacto)
    return dict(mejor), df_fam, df_hist, detalle20, detalle_h1, plan


def construir_evolucion_anual_v13(detalle20: pd.DataFrame, mejor: dict) -> pd.DataFrame:
    """Agrega indicadores de evolución para explicar degradación y compras de red del óptimo."""
    d = detalle20.copy()
    d["Energía red total [MWh]"] = d[["Energía red Valle [MWh]", "Energía red Resto [MWh]", "Energía red Pico [MWh]"]].sum(axis=1)
    red1 = float(d.iloc[0]["Energía red total [MWh]"])
    fv1 = float(d.iloc[0].get("Energía FV [MWh]", np.nan))
    d["Aumento red vs año 1 [MWh]"] = d["Energía red total [MWh]"] - red1
    d["Aumento red vs año 1 [%]"] = np.where(red1 > 1e-12, 100.0*d["Aumento red vs año 1 [MWh]"]/red1, np.nan)
    if "Energía FV [MWh]" in d.columns and math.isfinite(fv1):
        d["Pérdida FV vs año 1 [MWh]"] = fv1 - d["Energía FV [MWh]"]
        d["Variación FV vs año 1 [%]"] = 100.0*(d["Energía FV [MWh]"]/fv1 - 1.0)
    d["SOH BESS inicio [%]"] = 100.0*d["SOH inicio"]
    d["SOH BESS final [%]"] = 100.0*d["SOH final"]
    e_nom = float(mejor["E_BESS [MWh]"])
    d["Pérdida capacidad BESS vs nominal [MWh]"] = e_nom - d["Capacidad BESS final [MWh]"]
    d["Costo energía red a precios año 1 [USD]"] = d["Costo energía red [USD]"] / ((1.0+ESCALAMIENTO_COSTOS)**(d["Año"]-1))
    d["VP costo energía red [USD]"] = d["Costo energía red [USD]"] / ((1.0+WACC)**d["Año"])
    if "Energía demanda [MWh]" in d.columns:
        d["Demanda cubierta por red [%]"] = 100.0*d["Energía red total [MWh]"]/d["Energía demanda [MWh]"]
    return d


def construir_resumen_economico_v13(detalle20: pd.DataFrame, mejor: dict) -> pd.DataFrame:
    """Desglose del costo total a valor presente para el óptimo."""
    anios = detalle20["Año"].to_numpy(float)
    desc = (1.0 + WACC) ** anios
    componentes = [
        ("CAPEX FV", float(mejor["CAPEX FV [USD]"])),
        ("CAPEX eólico", float(mejor["CAPEX eólico [USD]"])),
        ("CAPEX BESS energía", float(mejor["CAPEX BESS energía [USD]"])),
        ("CAPEX BESS potencia", float(mejor["CAPEX BESS potencia [USD]"])),
        ("CAPEX fijo proyecto", float(CAPEX_FIJO_USD)),
        ("VP OPEX FV", float(np.sum(detalle20["OPEX FV [USD]"].to_numpy(float)/desc))),
        ("VP OPEX eólico", float(np.sum(detalle20["OPEX eólico [USD]"].to_numpy(float)/desc))),
        ("VP OPEX BESS", float(np.sum(detalle20["OPEX BESS [USD]"].to_numpy(float)/desc))),
        ("VP potencia contratada", float(np.sum(detalle20["Costo potencia contratada [USD]"].to_numpy(float)/desc))),
        ("VP red Valle", float(np.sum(detalle20["Costo red Valle [USD]"].to_numpy(float)/desc))),
        ("VP red Resto", float(np.sum(detalle20["Costo red Resto [USD]"].to_numpy(float)/desc))),
        ("VP red Pico", float(np.sum(detalle20["Costo red Pico [USD]"].to_numpy(float)/desc))),
        ("VP reemplazo BESS", float(np.sum(detalle20["Costo reemplazo BESS [USD]"].to_numpy(float)/desc))),
    ]
    total = sum(v for _,v in componentes)
    df = pd.DataFrame(componentes, columns=["Componente", "Valor presente [USD]"])
    df["Participación costo total [%]"] = 100.0*df["Valor presente [USD]"]/total if total else np.nan
    return df


def generar_analisis_final_v13(mejor: dict, evolucion: pd.DataFrame, economico: pd.DataFrame) -> str:
    y1, y20 = evolucion.iloc[0], evolucion.iloc[-1]
    red1 = float(y1["Energía red total [MWh]"]); red20 = float(y20["Energía red total [MWh]"])
    fv1 = float(y1.get("Energía FV [MWh]", np.nan)); fv20 = float(y20.get("Energía FV [MWh]", np.nan))
    lines = [
        "TRABAJO INTEGRADOR - ANÁLISIS FINAL DEL ÓPTIMO V13",
        "="*72,
        "",
        "DISEÑO ÓPTIMO",
        f"P_FV                         : {float(mejor['P_FV [MW]']):.4f} MW",
        f"Aerogeneradores              : {int(mejor['N aeros'])} ({float(mejor['P_EOL instalada [MW]']):.3f} MW instalados)",
        f"BESS potencia                 : {float(mejor['P_BESS [MW]']):.4f} MW",
        f"BESS energía                  : {float(mejor['E_BESS [MWh]']):.3f} MWh ({int(mejor['N containers BESS'])} containers)",
        f"Duración nominal BESS         : {float(mejor['Duración BESS nominal [h]']):.3f} h",
        f"Potencia contratada           : {P_CONTRATADA_FIJA_MW:.1f} MW",
        "",
        "RESULTADO ECONÓMICO",
        f"CAPEX total                   : USD {float(mejor['CAPEX total [USD]']):,.0f}",
        f"VP operación 20 años          : USD {float(mejor['VP operación 20a [USD]']):,.0f}",
        f"COSTO TOTAL 20 AÑOS           : USD {float(mejor['Costo total 20a [USD]']):,.0f}",
        "",
        "EVOLUCIÓN AÑO 1 -> AÑO 20",
    ]
    if math.isfinite(fv1) and fv1 > 0:
        lines += [
            f"Generación FV año 1           : {fv1:,.1f} MWh",
            f"Generación FV año 20          : {fv20:,.1f} MWh",
            f"Variación generación FV       : {(fv20/fv1-1)*100:.2f} %",
        ]
    lines += [
        f"Factor FV año 1 / año 20      : {float(y1['Factor FV']):.3f} / {float(y20['Factor FV']):.3f}",
        f"SOH BESS inicio               : {float(y1['SOH inicio'])*100:.2f} %",
        f"SOH BESS final año 20         : {float(y20['SOH final'])*100:.2f} %",
        f"Capacidad BESS final año 20   : {float(y20['Capacidad BESS final [MWh]']):.3f} MWh",
        f"Ciclos acumulados             : {float(y20['Ciclos equivalentes acumulados']):,.1f}",
        f"Compra red año 1              : {red1:,.1f} MWh",
        f"Compra red año 20             : {red20:,.1f} MWh",
        f"Aumento compra red            : {red20-red1:+,.1f} MWh ({((red20/red1)-1)*100 if red1 else float('nan'):+.2f} %)",
        f"Costo red año 1               : USD {float(y1['Costo energía red [USD]']):,.0f}",
        f"Costo red año 20 nominal      : USD {float(y20['Costo energía red [USD]']):,.0f}",
        f"Costo red año 20 a precios A1 : USD {float(y20['Costo energía red a precios año 1 [USD]']):,.0f}",
        "",
        "BALANCE 20 AÑOS",
        f"Exportación acumulada         : {float(mejor['Exportación 20a [MWh]']):,.1f} MWh (sin remuneración)",
        f"Demanda no abastecida         : {float(mejor['Energía no abastecida 20a [MWh]']):,.6f} MWh",
        f"Horas sin abastecer           : {int(mejor['Horas no cumple 20a'])}",
        f"Uso terreno screening         : {float(mejor['Uso terreno total screening [%]']):.2f} %",
        "",
        "NOTA:",
        "El aumento de compra de red respecto del año 1 refleja la evolución conjunta del",
        "sistema bajo los mismos perfiles base: degradación FV, pérdida de capacidad BESS",
        "por ciclos y cambios del despacho económico. No se atribuye exclusivamente a una",
        "única tecnología. El layout espacial sigue siendo un screening y no un micrositing final.",
        "",
        "DESGLOSE DEL COSTO TOTAL A VALOR PRESENTE",
    ]
    for _, r in economico.iterrows():
        lines.append(
            f"{str(r['Componente']):28s}: USD {float(r['Valor presente [USD]']):>13,.0f} "
            f"({float(r['Participación costo total [%]']):5.2f} %)"
        )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="V13: optimización por familias discretas con P_FV/P_BESS continuas e informe final detallado a 20 años."
    )
    parser.add_argument("--excel", type=Path, default=None)
    parser.add_argument("--tipo-aero", choices=["GE3.4", "GE3.8"], default="GE3.4")
    parser.add_argument("--sin-exportar", action="store_true")
    parser.add_argument("--pot-modulo-fv-w", type=float, default=POTENCIA_MODULO_FV_W_DEFAULT)
    parser.add_argument("--pitch-fv-m", type=float, default=PITCH_FV_DEFAULT_M)

    parser.add_argument("--optimizar", action="store_true", help="Ejecuta V13 y busca el mínimo global por familias discretas.")
    parser.add_argument("--fv-min", type=float, default=0.0)
    parser.add_argument("--fv-max", type=float, default=30.0)
    parser.add_argument("--pbess-min", type=float, default=0.0)
    parser.add_argument("--pbess-max", type=float, default=12.0)
    parser.add_argument("--aeros-min", type=int, default=0)
    parser.add_argument("--aeros-max", type=int, default=N_AEROS_MAX_ESPACIO)
    parser.add_argument("--containers-min", type=int, default=0)
    parser.add_argument("--containers-max", type=int, default=8)
    parser.add_argument("--maxiter-familia", type=int, default=6, help="Generaciones surrogate DE POR familia.")
    parser.add_argument("--popsize-familia", type=int, default=4, help="Población surrogate DE POR familia.")
    parser.add_argument("--tol", type=float, default=0.01)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--candidatos-surrogate-familia", type=int, default=3, help="Candidatos diversos retenidos por familia.")
    parser.add_argument("--exactos-por-familia", type=int, default=1, help="Validaciones exactas iniciales por familia factible.")
    parser.add_argument("--top-familias-refinar", type=int, default=6, help="Cantidad de mejores familias exactas a refinar.")
    parser.add_argument("--rondas-refinamiento", type=int, default=2, help="Rondas de refinamiento exacto por coordenadas.")
    parser.add_argument("--paso-fv-refinar", type=float, default=0.75, help="Paso FV inicial del refinamiento exacto [MW].")
    parser.add_argument("--paso-pbess-refinar", type=float, default=0.50, help="Paso BESS inicial del refinamiento exacto [MW].")

    # Modo interno para subprocess exacto.
    parser.add_argument("--evaluar-candidato-interno", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--cand-pfv", type=float, default=None, help=argparse.SUPPRESS)
    parser.add_argument("--cand-aeros", type=int, default=None, help=argparse.SUPPRESS)
    parser.add_argument("--cand-pbess", type=float, default=None, help=argparse.SUPPRESS)
    parser.add_argument("--cand-containers", type=int, default=None, help=argparse.SUPPRESS)
    parser.add_argument("--cand-prefix", type=Path, default=None, help=argparse.SUPPRESS)

    args = parser.parse_args()
    ruta = args.excel.resolve() if args.excel is not None else buscar_excel_por_defecto()
    if not ruta.exists():
        raise FileNotFoundError(f"No encontré el Excel: {ruta}")

    cfg = leer_configuracion_excel(ruta)
    perfiles = cargar_perfiles(ruta, cfg.p_fv_mw)
    carpeta = ruta.parent
    print(f"Excel utilizado: {ruta}")

    if args.evaluar_candidato_interno:
        requeridos = [args.cand_pfv, args.cand_aeros, args.cand_pbess, args.cand_containers, args.cand_prefix]
        if any(v is None for v in requeridos):
            raise ValueError("Faltan parámetros internos del candidato.")
        rr, d20, dh1, plan = evaluar_configuracion_v12(
            perfiles,
            p_fv_mw=args.cand_pfv, n_aeros=args.cand_aeros,
            p_bess_mw=args.cand_pbess, n_containers=args.cand_containers,
            cfg_base=cfg, potencia_modulo_fv_w=args.pot_modulo_fv_w,
            pitch_fv_m=args.pitch_fv_m, tipo_aero=args.tipo_aero,
            exportar_excedente=not args.sin_exportar, devolver_detalle_anio1=True,
        )
        pref = args.cand_prefix
        Path(str(pref)+"_resumen.json").write_text(
            json.dumps({k:_json_safe_v13(v) for k,v in rr.items()}, ensure_ascii=False, indent=2), encoding="utf-8"
        )
        d20.to_csv(Path(str(pref)+"_20a.csv"), index=False, decimal=".")
        plan.to_csv(Path(str(pref)+"_plan.csv"), index=False, decimal=".")
        if dh1 is not None:
            dh1.to_csv(Path(str(pref)+"_anio1.csv"), index=False, decimal=".")
        return

    if not args.optimizar:
        print("\nV13 está pensada para buscar el óptimo. Ejecutá el archivo con --optimizar.")
        print("No se evalúa automáticamente la configuración del Excel para no perder tiempo.")
        return

    mejor, familias, hist, detalle20, detalle_h1, plan = optimizar_por_familias_v13(
        perfiles,
        cfg_base=cfg, ruta_excel=ruta,
        fv_min=args.fv_min, fv_max=args.fv_max,
        pbess_min=args.pbess_min, pbess_max=args.pbess_max,
        aeros_min=args.aeros_min, aeros_max=args.aeros_max,
        containers_min=args.containers_min, containers_max=args.containers_max,
        potencia_modulo_fv_w=args.pot_modulo_fv_w, pitch_fv_m=args.pitch_fv_m,
        tipo_aero=args.tipo_aero, exportar_excedente=not args.sin_exportar,
        maxiter_familia=args.maxiter_familia, popsize_familia=args.popsize_familia,
        seed=args.seed, tol=args.tol,
        candidatos_surrogate_por_familia=args.candidatos_surrogate_familia,
        exactos_por_familia=args.exactos_por_familia,
        top_familias_refinar=args.top_familias_refinar,
        rondas_refinamiento=args.rondas_refinamiento,
        paso_fv_refinar=args.paso_fv_refinar,
        paso_pbess_refinar=args.paso_pbess_refinar,
    )

    evolucion = construir_evolucion_anual_v13(detalle20, mejor)
    economico = construir_resumen_economico_v13(detalle20, mejor)
    analisis = generar_analisis_final_v13(mejor, evolucion, economico)

    print("\n" + "="*80)
    print("ÓPTIMO ECONÓMICO GLOBAL V13")
    print("="*80)
    for k, v in mejor.items():
        if isinstance(v, (float, np.floating)):
            print(f"{k:42s}: {float(v):,.6f}")
        else:
            print(f"{k:42s}: {v}")

    y1, y20 = evolucion.iloc[0], evolucion.iloc[-1]
    print("\n" + "="*80)
    print("EVOLUCIÓN DEL ÓPTIMO - AÑO 1 vs AÑO 20")
    print("="*80)
    if "Energía FV [MWh]" in evolucion.columns:
        print(f"FV año 1 [MWh]                         : {float(y1['Energía FV [MWh]']):,.3f}")
        print(f"FV año 20 [MWh]                        : {float(y20['Energía FV [MWh]']):,.3f}")
    print(f"Factor FV año 1 -> 20                  : {float(y1['Factor FV']):.3f} -> {float(y20['Factor FV']):.3f}")
    print(f"SOH BESS inicio -> final 20            : {float(y1['SOH inicio'])*100:.2f}% -> {float(y20['SOH final'])*100:.2f}%")
    print(f"Ciclos acumulados                      : {float(y20['Ciclos equivalentes acumulados']):,.3f}")
    print(f"Compra red año 1 [MWh]                 : {float(y1['Energía red total [MWh]']):,.3f}")
    print(f"Compra red año 20 [MWh]                : {float(y20['Energía red total [MWh]']):,.3f}")
    print(f"Aumento compra red año 20 vs año 1     : {float(y20['Aumento red vs año 1 [MWh]']):+,.3f} MWh ({float(y20['Aumento red vs año 1 [%]']):+.2f}%)")
    print(f"Exportación acumulada 20a [MWh]        : {float(mejor['Exportación 20a [MWh]']):,.3f}")
    print(f"Demanda no abastecida 20a [MWh]        : {float(mejor['Energía no abastecida 20a [MWh]']):,.6f}")

    # Archivos finales V13.
    f_fam = carpeta / "v13_mejor_por_familia.csv"
    f_hist = carpeta / "v13_evaluaciones_exactas.csv"
    f_evol = carpeta / "optimo_v13_evolucion_20_anios.csv"
    f_eco = carpeta / "optimo_v13_desglose_economico.csv"
    f_plan = carpeta / "optimo_v13_plan_degradacion.csv"
    f_h1 = carpeta / "optimo_v13_anio1_horario.csv"
    f_txt = carpeta / "optimo_v13_analisis_final.txt"
    f_json = carpeta / "optimo_v13_resumen.json"

    familias.to_csv(f_fam, index=False, decimal=".")
    if not hist.empty:
        hist.to_csv(f_hist, index=False, decimal=".")
    evolucion.to_csv(f_evol, index=False, decimal=".")
    economico.to_csv(f_eco, index=False, decimal=".")
    plan.to_csv(f_plan, index=False, decimal=".")
    if detalle_h1 is not None:
        detalle_h1.to_csv(f_h1, index=False, decimal=".")
    f_txt.write_text(analisis, encoding="utf-8")
    f_json.write_text(json.dumps({k:_json_safe_v13(v) for k,v in mejor.items()}, ensure_ascii=False, indent=2), encoding="utf-8")

    print("\nArchivos finales V13:")
    print(f"  {f_fam}")
    if not hist.empty: print(f"  {f_hist}")
    print(f"  {f_evol}")
    print(f"  {f_eco}")
    print(f"  {f_plan}")
    if detalle_h1 is not None: print(f"  {f_h1}")
    print(f"  {f_txt}")
    print(f"  {f_json}")


if __name__ == "__main__":
    main()



