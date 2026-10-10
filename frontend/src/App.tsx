import { EvidenceBadge, HelpTip } from "./components/EvidenceBadge";
import { BarCompare, DualAxisChart } from "./components/Charts";
import { ReductionGraph, type GraphPayload } from "./components/ReductionGraph";
import { useEffect, useMemo, useState } from "react";

const API = import.meta.env.VITE_API_URL ?? "http://localhost:8000";

type Tab =
  | "home"
  | "complexity"
  | "solvers"
  | "generator"
  | "reductions"
  | "conjectures"
  | "auditor"
  | "barriers"
  | "formalization"
  | "ayuda";

const TABS: { id: Tab; label: string }[] = [
  { id: "home", label: "Inicio" },
  { id: "complexity", label: "Complejidad" },
  { id: "solvers", label: "Solvers" },
  { id: "generator", label: "Generador" },
  { id: "reductions", label: "Reducciones" },
  { id: "conjectures", label: "Conjeturas" },
  { id: "auditor", label: "Auditor" },
  { id: "barriers", label: "Barreras" },
  { id: "formalization", label: "Lean" },
  { id: "ayuda", label: "Ayuda" },
];

type PhasePoint = {
  ratio: number;
  sat_rate: number | null;
  median_decisions: number | null;
};

export default function App() {
  const [tab, setTab] = useState<Tab>("home");
  const [health, setHealth] = useState("…");
  const [summary, setSummary] = useState<Record<string, unknown> | null>(null);
  const [dimacs, setDimacs] = useState(
    "c ejemplo 3-CNF\np cnf 3 3\n1 2 3 0\n-1 2 -3 0\n1 -2 3 0\n"
  );
  const [solver, setSolver] = useState("meta");
  const [out, setOut] = useState("");
  const [ratio, setRatio] = useState(4.2);
  const [nVars, setNVars] = useState(10);
  const [seed, setSeed] = useState(12345);
  const [family, setFamily] = useState("pigeonhole");
  const [advSize, setAdvSize] = useState(4);
  const [auditText, setAuditText] = useState(
    "Theorem. In practice our heuristic always finds solutions in polynomial time, therefore P = NP."
  );
  const [barriers, setBarriers] = useState<Array<Record<string, unknown>>>([]);
  const [formalization, setFormalization] = useState<Record<string, unknown> | null>(
    null
  );
  const [helpTopics, setHelpTopics] = useState<Array<{ id: string; title: string; body: string }>>(
    []
  );
  const [phase, setPhase] = useState<PhasePoint[]>([]);
  const [phaseNote, setPhaseNote] = useState("");
  const [phaseLoading, setPhaseLoading] = useState(false);
  const [graph, setGraph] = useState<GraphPayload | null>(null);
  const [compareRows, setCompareRows] = useState<
    { solver: string; wall_time_seconds: number; decisions: number; satisfiable: boolean | null }[]
  >([]);

  useEffect(() => {
    fetch(`${API}/health`)
      .then((r) => r.json())
      .then((j) => setHealth(j.status))
      .catch(() => setHealth("unreachable"));
    fetch(`${API}/dashboard/summary`)
      .then((r) => r.json())
      .then(setSummary)
      .catch(() => setSummary(null));
    fetch(`${API}/barriers`)
      .then((r) => r.json())
      .then(setBarriers)
      .catch(() => setBarriers([]));
    fetch(`${API}/formalization`)
      .then((r) => r.json())
      .then(setFormalization)
      .catch(() => setFormalization(null));
    fetch(`${API}/help/topics`)
      .then((r) => r.json())
      .then(setHelpTopics)
      .catch(() => setHelpTopics([]));
    fetch(`${API}/visual/phase-latest`)
      .then((r) => r.json())
      .then((j) => {
        if (Array.isArray(j.series) && j.series.length) {
          setPhase(j.series);
          setPhaseNote(String(j.disclaimer ?? ""));
        }
      })
      .catch(() => undefined);
  }, []);

  const alerts = useMemo(() => {
    const a = summary?.alerts;
    return Array.isArray(a) ? (a as string[]) : [];
  }, [summary]);

  async function post(path: string, body: unknown) {
    setOut("running…");
    const r = await fetch(`${API}${path}`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(body),
    });
    const j = await r.json();
    setOut(JSON.stringify(j, null, 2));
    return j;
  }

  async function runPhaseSnapshot() {
    setPhaseLoading(true);
    try {
      const j = await post("/visual/phase-snapshot", {
        num_variables: 12,
        instances_per_ratio: 8,
        seed: 42,
      });
      setPhase(j.series ?? []);
      setPhaseNote(String(j.disclaimer ?? ""));
    } finally {
      setPhaseLoading(false);
    }
  }

  async function visualizeReduction() {
    const j = await post("/visual/reduction-graph", {
      dimacs,
      reduction: "3sat_to_clique",
    });
    setGraph(j);
  }

  async function compareSolvers() {
    const j = await post("/solve/compare", { dimacs, solver: "meta" });
    setCompareRows(j.rows ?? []);
  }

  return (
    <div className="page">
      <header className="hero">
        <p className="brand">PNP Research Laboratory</p>
        <h1>Complejidad computacional, con lupa visual.</h1>
        <p className="lede">
          Experimentos, reducciones y auditorías con etiquetas de evidencia. Lo que ves
          aquí es apoyo visual (≤ E2): nunca una resolución de P vs NP.
        </p>
        <div className="hero-actions">
          <EvidenceBadge level="E2 max. experimental" claim="observation" />
          <p className="meta">API: {health}</p>
        </div>
      </header>

      <nav className="tabs" aria-label="Secciones">
        {TABS.map((t) => (
          <button
            key={t.id}
            type="button"
            className={tab === t.id ? "tab active" : "tab"}
            onClick={() => setTab(t.id)}
          >
            {t.label}
          </button>
        ))}
      </nav>

      {tab === "home" && (
        <section className="panel">
          <h2>Inicio</h2>
          <div className="home-grid">
            <div>
              <p className="muted">{String(summary?.evidence_policy ?? "…")}</p>
              <ul className="list">
                {alerts.map((a) => (
                  <li key={a}>{a}</li>
                ))}
              </ul>
              <HelpTip title="¿Por dónde empezar?">
                1) Abre <strong>Complejidad</strong> y genera un snapshot del gráfico α.
                2) En <strong>Reducciones</strong>, visualiza 3-SAT → Clique paso a paso.
                3) Usa <strong>Ayuda</strong> si un resultado te parece “demasiado fuerte”.
              </HelpTip>
            </div>
            <div className="mini-chart-wrap">
              <DualAxisChart
                points={phase}
                y1Label="tasa SAT"
                y2Label="decisiones"
                title="Vista rápida (último snapshot / experimento)"
              />
              <button type="button" className="ghost" onClick={() => setTab("complexity")}>
                Ir al explorador
              </button>
            </div>
          </div>
        </section>
      )}

      {tab === "complexity" && (
        <section className="panel">
          <h2>Explorador de complejidad</h2>
          <EvidenceBadge level="E2" claim="observation_experimental" />
          <HelpTip title="Cómo leer este gráfico">
            La curva dorada es la tasa empírica de satisfacibilidad; la verde punteada es el
            esfuerzo mediano de DPLL. Un valle o pico cerca de α≈4 es una pista de la
            literatura, no un teorema demostrado aquí.
          </HelpTip>
          <div className="row">
            <button type="button" onClick={runPhaseSnapshot} disabled={phaseLoading}>
              {phaseLoading ? "Calculando…" : "Generar snapshot visual (n=12)"}
            </button>
          </div>
          <DualAxisChart
            points={phase}
            y1Label="tasa SAT (pysat)"
            y2Label="median decisiones (dpll)"
            title="Transición empírica en random 3-SAT"
          />
          <p className="warn-inline">{phaseNote}</p>
          <pre className="compact">{out}</pre>
        </section>
      )}

      {tab === "solvers" && (
        <section className="panel">
          <h2>Solvers</h2>
          <HelpTip title="Comparar sin sobreinterpretar">
            Barras más cortas ≠ algoritmo en P. Solo comparan tiempos en esta instancia
            concreta.
          </HelpTip>
          <label className="field">
            Solver
            <select value={solver} onChange={(e) => setSolver(e.target.value)}>
              <option value="meta">meta</option>
              <option value="dpll">dpll</option>
              <option value="pysat">pysat</option>
              <option value="bruteforce">bruteforce</option>
            </select>
          </label>
          <textarea value={dimacs} onChange={(e) => setDimacs(e.target.value)} rows={8} />
          <div className="row">
            <button type="button" onClick={() => post("/solve", { dimacs, solver })}>
              Ejecutar
            </button>
            <button type="button" className="ghost" onClick={compareSolvers}>
              Comparar (barras)
            </button>
          </div>
          {compareRows.length > 0 && <BarCompare rows={compareRows} />}
          <pre>{out}</pre>
        </section>
      )}

      {tab === "generator" && (
        <section className="panel">
          <h2>Generadores</h2>
          <h3>Random k-SAT</h3>
          <div className="row">
            <label className="field">
              n
              <input
                type="number"
                value={nVars}
                onChange={(e) => setNVars(Number(e.target.value))}
              />
            </label>
            <label className="field">
              α
              <input
                type="number"
                step="0.1"
                value={ratio}
                onChange={(e) => setRatio(Number(e.target.value))}
              />
            </label>
            <label className="field">
              seed
              <input
                type="number"
                value={seed}
                onChange={(e) => setSeed(Number(e.target.value))}
              />
            </label>
          </div>
          <button
            type="button"
            onClick={() =>
              post("/generate/random-ksat", {
                num_variables: nVars,
                ratio,
                seed,
                k: 3,
              })
            }
          >
            Generar random
          </button>
          <h3>Adversariales / estructurados</h3>
          <div className="row">
            <label className="field">
              familia
              <select value={family} onChange={(e) => setFamily(e.target.value)}>
                <option value="pigeonhole">pigeonhole (PHP)</option>
                <option value="tseitin">tseitin</option>
                <option value="hard_subset_sum">hard subset sum</option>
                <option value="crafted_hamiltonian">crafted hamiltonian</option>
              </select>
            </label>
            <label className="field">
              size
              <input
                type="number"
                value={advSize}
                onChange={(e) => setAdvSize(Number(e.target.value))}
              />
            </label>
          </div>
          <button
            type="button"
            onClick={() =>
              post("/generate/adversarial", {
                family,
                size: advSize,
                seed,
                unsat: true,
              })
            }
          >
            Generar adversarial
          </button>
          <pre>{out}</pre>
        </section>
      )}

      {tab === "reductions" && (
        <section className="panel">
          <h2>Reducciones visuales</h2>
          <EvidenceBadge level="E2 + known_result (Karp)" claim="visual didactic" />
          <HelpTip title="Guía rápida">
            Los nodos del mismo color pertenecen a la misma cláusula. Avanza los pasos 1→4
            para ver aristas y el parámetro k.
          </HelpTip>
          <textarea value={dimacs} onChange={(e) => setDimacs(e.target.value)} rows={6} />
          <div className="row">
            <button type="button" onClick={visualizeReduction}>
              Visualizar 3-SAT → Clique
            </button>
            <button
              type="button"
              className="ghost"
              onClick={() => post("/reductions/apply", { dimacs, reduction: "3sat_to_clique" })}
            >
              Solo JSON
            </button>
          </div>
          <ReductionGraph data={graph} />
          <pre className="compact">{out}</pre>
        </section>
      )}

      {tab === "conjectures" && (
        <section className="panel">
          <h2>Conjeturas / refutación</h2>
          <div className="row">
            <button
              type="button"
              onClick={() => post("/conjectures/refute/demo-always-sat", {})}
            >
              Refutar “siempre SAT @ α=4.2”
            </button>
            <button
              type="button"
              className="ghost"
              onClick={() => post("/conjectures/refute/solvers-agree", {})}
            >
              Desacuerdo solvers
            </button>
          </div>
          <pre>{out}</pre>
        </section>
      )}

      {tab === "auditor" && (
        <section className="panel">
          <h2>Auditor de demostraciones</h2>
          <EvidenceBadge level="E1 (heurístico)" claim="never certification" />
          <textarea value={auditText} onChange={(e) => setAuditText(e.target.value)} rows={8} />
          <button type="button" onClick={() => post("/audit/proof", { text: auditText })}>
            Auditar
          </button>
          <pre>{out}</pre>
        </section>
      )}

      {tab === "barriers" && (
        <section className="panel">
          <h2>Barreras conocidas</h2>
          <div className="cards">
            {barriers.map((b) => (
              <article key={String(b.id)} className="barrier">
                <h3>{String(b.name)}</h3>
                <p>{String(b.summary)}</p>
              </article>
            ))}
          </div>
        </section>
      )}

      {tab === "formalization" && (
        <section className="panel">
          <h2>Formalización Lean</h2>
          <EvidenceBadge level="E5-parcial" claim="certificate lemmas only" />
          <pre className="compact">{JSON.stringify(formalization, null, 2)}</pre>
        </section>
      )}

      {tab === "ayuda" && (
        <section className="panel">
          <h2>Centro de ayuda visual</h2>
          <p className="muted">
            Tarjetas metodológicas para no confundir gráficos con demostraciones.
          </p>
          <div className="help-grid">
            {helpTopics.map((t) => (
              <article key={t.id} className="help-card">
                <h3>{t.title}</h3>
                <p>{t.body}</p>
              </article>
            ))}
          </div>
        </section>
      )}

      <section className="panel warn">
        <h2>Alerta metodológica permanente</h2>
        <p>
          Toda visualización de esta interfaz es apoyo interpretativo. Evidencia
          experimental ≤ E2. No resuelve P vs NP.
        </p>
      </section>
    </div>
  );
}
