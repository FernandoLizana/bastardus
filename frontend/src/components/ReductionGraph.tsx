import { useEffect, useMemo, useState } from "react";

type Node = { id: number; label: string; clause: number; literal: number; group: number };
type Link = { source: number; target: number };

export type GraphPayload = {
  nodes: Node[];
  links: Link[];
  k: number;
  steps: { title: string; detail: string }[];
  source_size: Record<string, number>;
  target_size: Record<string, number>;
  caveat: string;
};

function layout(nodes: Node[], width: number, height: number) {
  const groups = [...new Set(nodes.map((n) => n.group))].sort((a, b) => a - b);
  const byGroup = new Map<number, Node[]>();
  for (const n of nodes) {
    const arr = byGroup.get(n.group) ?? [];
    arr.push(n);
    byGroup.set(n.group, arr);
  }
  const pos = new Map<number, { x: number; y: number }>();
  groups.forEach((g, gi) => {
    const col = byGroup.get(g) ?? [];
    const x = (width * (gi + 1)) / (groups.length + 1);
    col.forEach((n, ni) => {
      const y = (height * (ni + 1)) / (col.length + 1);
      pos.set(n.id, { x, y });
    });
  });
  return pos;
}

const PALETTE = ["#c4a35a", "#6ec6a8", "#d27b5a", "#7aa2d4", "#b08dcf"];

export function ReductionGraph({ data }: { data: GraphPayload | null }) {
  const [step, setStep] = useState(0);
  const w = 720;
  const h = 360;
  const positions = useMemo(
    () => (data ? layout(data.nodes, w, h) : new Map<number, { x: number; y: number }>()),
    [data]
  );

  useEffect(() => setStep(0), [data]);

  if (!data) {
    return <p className="muted">Carga un 3-CNF y pulsa “Visualizar reducción”.</p>;
  }

  const color = (g: number) => PALETTE[g % PALETTE.length];
  const showEdges = step >= 1;
  const highlightK = step >= 2;

  return (
    <div className="reduction-viz">
      <div className="stepper">
        {data.steps.map((s, i) => (
          <button
            key={s.title}
            type="button"
            className={i === step ? "step active" : "step"}
            onClick={() => setStep(i)}
          >
            {i + 1}
          </button>
        ))}
      </div>
      <div className="step-detail">
        <h3>{data.steps[step]?.title}</h3>
        <p>{data.steps[step]?.detail}</p>
      </div>
      <svg
        viewBox={`0 0 ${w} ${h}`}
        className="graph-svg"
        role="img"
        aria-label="Grafo de reducción"
      >
        {showEdges &&
          data.links.map((l) => {
            const a = positions.get(l.source);
            const b = positions.get(l.target);
            if (!a || !b) return null;
            return (
              <line
                key={`${l.source}-${l.target}`}
                x1={a.x}
                y1={a.y}
                x2={b.x}
                y2={b.y}
                stroke="rgba(158,176,168,0.35)"
                strokeWidth="1"
              />
            );
          })}
        {data.nodes.map((n) => {
          const p = positions.get(n.id);
          if (!p) return null;
          return (
            <g key={n.id} transform={`translate(${p.x},${p.y})`}>
              <circle
                r={highlightK ? 14 : 12}
                fill={color(n.group)}
                stroke={highlightK ? "#fff" : "transparent"}
                strokeWidth={highlightK ? 1.5 : 0}
                opacity={0.95}
              >
                <title>{n.label}</title>
              </circle>
              <text dy="0.35em" textAnchor="middle" className="node-label">
                {n.literal}
              </text>
            </g>
          );
        })}
      </svg>
      <div className="size-strip">
        <span>
          origen: n={data.source_size.variables}, m={data.source_size.clauses}
        </span>
        <span className="arrow">→</span>
        <span>
          clique: |V|={data.target_size.vertices}, |E|={data.target_size.edges}, k=
          {data.k}
        </span>
      </div>
      <p className="muted tiny">{data.caveat}</p>
    </div>
  );
}
