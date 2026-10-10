"""Catalog of requirements for a purported P vs NP resolution.

Source: laboratory claim-gate specification (Camino A / Camino B).
"""

from __future__ import annotations

from enum import Enum
from typing import Any


class ClaimSide(str, Enum):
    """Exactly one side may be asserted by a resolution candidate."""

    A_P_EQ_NP = "A_P_eq_NP"
    B_P_NE_NP = "B_P_ne_NP"


PROBLEM_MODES: list[dict[str, Any]] = [
    {
        "id": "decision",
        "name": "Decision",
        "requirement": (
            "Correct yes/no for every input; terminates; worst-case poly-time if claiming P=NP."
        ),
    },
    {
        "id": "search",
        "name": "Search (certificate recovery)",
        "requirement": (
            "A poly-time decision algorithm must lift to search via self-reducibility "
            "(SAT assignment, clique vertices, Hamiltonian cycle, Subset-Sum subset, …) "
            "with polynomially many decision calls and verifiable certificates."
        ),
    },
    {
        "id": "optimization",
        "name": "Optimization",
        "requirement": (
            "Decision (cost ≤ K) lifts to optimum via binary search / related queries: "
            "search range has polynomial bit-length; query count polynomial; "
            "each query instance has polynomial size."
        ),
    },
    {
        "id": "yes_and_no",
        "name": "YES and NO instances",
        "requirement": (
            "Correct on satisfiable AND unsatisfiable / no-certificate instances. "
            "Fast YES heuristics without efficient NO certificates are insufficient."
        ),
    },
]


NPC_FAMILIES: list[dict[str, Any]] = [
    # Logic / satisfiability
    {"id": "sat", "group": "logic", "name": "SAT", "role": "NPC"},
    {"id": "cnf_sat", "group": "logic", "name": "CNF-SAT", "role": "NPC"},
    {"id": "3sat", "group": "logic", "name": "3-SAT", "role": "NPC"},
    {"id": "circuit_sat", "group": "logic", "name": "Circuit-SAT", "role": "NPC"},
    {"id": "nae_3sat", "group": "logic", "name": "NAE-3-SAT", "role": "NPC"},
    {"id": "exact_sat", "group": "logic", "name": "Exact SAT", "role": "NPC"},
    {"id": "unsat", "group": "logic", "name": "UNSAT", "role": "coNPC_related"},
    {"id": "taut", "group": "logic", "name": "TAUT", "role": "coNPC"},
    # Graphs
    {"id": "clique", "group": "graphs", "name": "Clique", "role": "NPC"},
    {"id": "independent_set", "group": "graphs", "name": "Independent Set", "role": "NPC"},
    {"id": "vertex_cover", "group": "graphs", "name": "Vertex Cover", "role": "NPC"},
    {"id": "3coloring", "group": "graphs", "name": "3-Coloring", "role": "NPC"},
    {"id": "ham_cycle", "group": "graphs", "name": "Hamiltonian Cycle", "role": "NPC"},
    {"id": "ham_path", "group": "graphs", "name": "Hamiltonian Path", "role": "NPC"},
    {"id": "longest_path", "group": "graphs", "name": "Longest Path (decision)", "role": "NPC"},
    {"id": "steiner_tree", "group": "graphs", "name": "Steiner Tree (decision)", "role": "NPC"},
    {"id": "dominating_set", "group": "graphs", "name": "Dominating Set", "role": "NPC"},
    {"id": "subgraph_iso", "group": "graphs", "name": "Subgraph Isomorphism", "role": "NPC"},
    # Numbers / combinatorics
    {"id": "subset_sum", "group": "numbers", "name": "Subset Sum", "role": "NPC"},
    {"id": "partition", "group": "numbers", "name": "Partition", "role": "NPC"},
    {"id": "knapsack", "group": "numbers", "name": "Knapsack (decision)", "role": "NPC"},
    {"id": "bin_packing", "group": "numbers", "name": "Bin Packing (decision)", "role": "NPC"},
    {"id": "exact_cover", "group": "numbers", "name": "Exact Cover", "role": "NPC"},
    {"id": "x3c", "group": "numbers", "name": "Exact Cover by 3-Sets (X3C)", "role": "NPC"},
    {"id": "set_cover", "group": "numbers", "name": "Set Cover", "role": "NPC"},
    {"id": "ilp_01", "group": "numbers", "name": "0-1 ILP feasibility", "role": "NPC"},
    # Routing / scheduling
    {"id": "tsp_decision", "group": "routing", "name": "TSP (decision)", "role": "NPC"},
    {"id": "vrp", "group": "routing", "name": "Vehicle Routing (NPC variants)", "role": "NPC"},
    {"id": "job_shop", "group": "routing", "name": "Job-Shop Scheduling (decision)", "role": "NPC"},
    {"id": "timetabling", "group": "routing", "name": "Timetabling", "role": "NPC"},
    {"id": "multiprocessor", "group": "routing", "name": "Multiprocessor Scheduling", "role": "NPC"},
    {
        "id": "rcpsp",
        "group": "routing",
        "name": "Resource-Constrained Project Scheduling",
        "role": "NPC",
    },
]


# Negative answers required: each must be discarded (status PASS means "discarded / not used").
ERROR_DISCARDS: list[dict[str, Any]] = [
    {"id": "brute_2n", "question": "¿Usa fuerza bruta 2^n, aunque esté optimizada?"},
    {
        "id": "input_dependent_exponent",
        "question": "¿Tiene una constante o exponente que depende del tamaño de la entrada?",
    },
    {"id": "exp_precompute", "question": "¿Precalcula una tabla exponencial?"},
    {"id": "exp_memory", "question": "¿Usa memoria exponencial?"},
    {"id": "exp_parallel_branches", "question": "¿Ejecuta ramas exponenciales en paralelo?"},
    {"id": "exp_processors", "question": "¿Supone una cantidad exponencial de procesadores?"},
    {
        "id": "exp_bit_integers",
        "question": "¿Opera con enteros que contienen exponencialmente muchos bits?",
    },
    {
        "id": "unary_vs_binary",
        "question": "¿Mide la complejidad respecto del valor numérico y no de su longitud binaria?",
    },
    {"id": "pseudo_poly", "question": "¿Es pseudo-polinómico en vez de polinómico?"},
    {
        "id": "bounded_treewidth_only",
        "question": "¿Solo funciona para grafos de treewidth pequeño?",
    },
    {
        "id": "clause_ratio_only",
        "question": "¿Solo funciona para una proporción determinada de cláusulas?",
    },
    {"id": "almost_always", "question": "¿Solo funciona «casi siempre»?"},
    {
        "id": "distribution_dependent",
        "question": "¿Depende de una distribución probabilística de las entradas?",
    },
    {
        "id": "error_prob_unremoved",
        "question": "¿Tiene una probabilidad de error sin demostrar cómo eliminarla?",
    },
    {
        "id": "neural_no_proof",
        "question": "¿Usa una red neuronal sin prueba universal de corrección?",
    },
    {
        "id": "ai_strategy_exp",
        "question": "¿La IA elige una estrategia, pero esa selección puede tardar exponencialmente?",
    },
    {"id": "non_terminating", "question": "¿El algoritmo puede quedar ejecutándose indefinidamente?"},
    {"id": "small_n_only", "question": "¿Los experimentos solo alcanzan tamaños pequeños?"},
    {
        "id": "curve_fitting",
        "question": "¿Se infiere un crecimiento polinómico mediante ajuste de curvas?",
    },
    {
        "id": "practice_vs_asymptotic",
        "question": "¿Se confunde rapidez práctica con tiempo polinómico asintótico?",
    },
]


BARRIER_ITEMS: list[dict[str, Any]] = [
    {
        "id": "relativization",
        "name": "Relativización (Baker–Gill–Solovay)",
        "requirement": (
            "Identificar el paso concreto que NO relativiza. "
            "Una técnica válida relativo a todo oráculo no basta."
        ),
    },
    {
        "id": "natural_proofs",
        "name": "Natural proofs (Razborov–Rudich)",
        "requirement": (
            "Si usa cotas de circuitos: ¿la propiedad es constructiva, amplia y útil? "
            "Mostrar por qué no es una natural proof (o por qué los supuestos cripto no aplican)."
        ),
    },
    {
        "id": "algebrization",
        "name": "Algebrización (Aaronson–Wigderson)",
        "requirement": "Identificar el paso concreto que NO algebriza.",
    },
    {
        "id": "restricted_model",
        "name": "Modelo restringido vs general",
        "requirement": (
            "Cotas para circuitos monótonos, AC⁰, profundidad fija, resolución tree-like/"
            "regular, DPLL, CDCL, greedy, etc. NO bastan solos. "
            "Una ruta suficiente (más fuerte): cota superpolinómica para circuitos booleanos "
            "generales sobre un problema NP-completo (p.ej. 3-SAT)."
        ),
    },
]


CONSEQUENCE_ITEMS_A: list[dict[str, Any]] = [
    {"id": "all_npc_in_p", "text": "SAT y todos los NP-completos caerían en P."},
    {"id": "search_in_p", "text": "Los problemas de búsqueda asociados serían polinomiales."},
    {"id": "p_eq_np_eq_conp", "text": "P = NP = coNP."},
    {"id": "taut_unsat_in_p", "text": "TAUT y UNSAT caerían en P."},
    {
        "id": "exact_opt_poly",
        "text": "Muchos problemas exactos de optimización tendrían algoritmos polinomiales.",
    },
    {
        "id": "no_owf",
        "text": "No existirían funciones unidireccionales clásicas con la dureza esperada.",
    },
    {
        "id": "crypto_collapse",
        "text": "Muchas bases clásicas de seguridad criptográfica quedarían invalidadas.",
    },
    {
        "id": "impractical_ok",
        "text": "O(n^1000) bastaría formalmente aunque fuese impráctico.",
    },
]


CONSEQUENCE_ITEMS_B: list[dict[str, Any]] = [
    {
        "id": "not_all_exp",
        "text": "NO implica automáticamente que todo NP-completo requiera tiempo exponencial.",
    },
    {"id": "not_factoring", "text": "NO implica que la factorización sea difícil."},
    {"id": "not_crypto_safe", "text": "NO implica que la criptografía actual sea segura."},
    {"id": "not_np_ne_conp", "text": "NO implica NP ≠ coNP."},
    {"id": "not_avg_hard", "text": "NO implica dureza en promedio."},
    {"id": "not_no_approx", "text": "NO implica ausencia de buenos algoritmos aproximados."},
    {"id": "not_no_heuristics", "text": "NO implica ausencia de heurísticas rápidas."},
    {
        "id": "not_quantum",
        "text": "NO implica que una computadora cuántica tampoco pueda resolverlos.",
    },
    {
        "id": "only_worst_case_det",
        "text": (
            "Solo establece: no existe algoritmo determinista polinomial que resuelva "
            "correctamente todas las instancias de todos los problemas de NP."
        ),
    },
]


APPROVAL_CHECKLIST: list[dict[str, Any]] = [
    {"id": "exact_claim", "text": "Afirmación exacta: P=NP o P≠NP (un solo Camino)."},
    {"id": "formal_defs", "text": "Definiciones formales de P, NP y reducción."},
    {"id": "machine_model", "text": "Modelo computacional especificado."},
    {"id": "input_bits", "text": "Tamaño de entrada definido en bits."},
    {"id": "correctness_all", "text": "Corrección demostrada para todas las entradas."},
    {"id": "subroutine_complexity", "text": "Complejidad de cada subrutina."},
    {"id": "worst_case_time", "text": "Tiempo de peor caso."},
    {"id": "memory", "text": "Memoria utilizada."},
    {"id": "no_exp_preprocess", "text": "Ausencia de preprocesamiento exponencial."},
    {"id": "no_exp_parallel", "text": "Ausencia de paralelismo exponencial oculto."},
    {"id": "no_hidden_params", "text": "Ausencia de parámetros fijos ocultos."},
    {"id": "yes_no_cases", "text": "Tratamiento de casos YES y NO."},
    {"id": "decision_to_search", "text": "Conversión entre decisión y búsqueda."},
    {"id": "reductions_formal", "text": "Reducciones verificadas formalmente."},
    {"id": "relativization_review", "text": "Revisión de relativización."},
    {"id": "natural_proofs_review", "text": "Revisión de natural proofs."},
    {"id": "algebrization_review", "text": "Revisión de algebrización."},
    {"id": "literature_compare", "text": "Comparación con teoremas existentes."},
    {"id": "adversarial_search", "text": "Búsqueda adversarial de contraejemplos."},
    {"id": "formal_lemmas", "text": "Verificación formal de los lemas críticos."},
    {"id": "independent_review", "text": "Revisión por especialistas independientes."},
]


# Path A / B mechanical requirements (beyond checklists)
PATH_A_REQUIREMENTS: list[dict[str, str]] = [
    {
        "id": "a_npc_problem",
        "text": "Existe algoritmo determinista que resuelve un problema NP-completo.",
    },
    {"id": "a_correct_all", "text": "Correcto para todas las entradas."},
    {"id": "a_terminates", "text": "Termina siempre."},
    {
        "id": "a_poly_time",
        "text": "Tiempo O(n^k) para alguna constante fija k (n = bits de la entrada).",
    },
    {
        "id": "a_no_hidden_exp",
        "text": (
            "No esconde trabajo exponencial en preprocesamiento, memoria, "
            "paralelismo o números gigantes."
        ),
    },
]


PATH_B_REQUIREMENTS: list[dict[str, str]] = [
    {
        "id": "b_some_np_hard",
        "text": "Existe al menos un problema de NP sin algoritmo determinista polinomial para todas las entradas.",
    },
    {
        "id": "b_future_algorithms",
        "text": "La afirmación cubre algoritmos aún no inventados.",
    },
    {
        "id": "b_asymptotic",
        "text": "La cota es asintótica y válida para tamaños arbitrariamente grandes.",
    },
    {
        "id": "b_not_method_specific",
        "text": (
            "No se limita a DPLL, CDCL, fuerza bruta, redes neuronales "
            "ni una familia particular de métodos."
        ),
    },
]
