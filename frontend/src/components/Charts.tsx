export function DualAxisChart({
  points,
  y1Label,
  y2Label,
  title,
}: {
  points: { ratio: number; sat_rate: number | null; median_decisions: number | null }[];
  y1Label: string;
  y2Label: string;
  title: string;
}) {
  const w = 640;
  const h = 280;
  const pad = { t: 28, r: 48, b: 40, l: 48 };
  const innerW = w - pad.l - pad.r;
  const innerH = h - pad.t - pad.b;
  if (!points.length) {
    return <p className="muted">Sin datos aún. Genera un snapshot.</p>;
  }
  const xs = points.map((p) => p.ratio);
  const minX = Math.min(...xs);
  const maxX = Math.max(...xs);
  const maxDec = Math.max(
    1,
    ...points.map((p) => p.median_decisions ?? 0)
  );
  const xScale = (x: number) =>
    pad.l + ((x - minX) / Math.max(maxX - minX, 1e-6)) * innerW;
  const ySat = (y: number) => pad.t + (1 - y) * innerH;
  const yDec = (y: number) => pad.t + (1 - y / maxDec) * innerH;

  const satPath = points
    .filter((p) => p.sat_rate != null)
    .map((p, i) => {
      const x = xScale(p.ratio);
      const y = ySat(p.sat_rate as number);
      return `${i === 0 ? "M" : "L"}${x},${y}`;
    })
    .join(" ");
  const decPath = points
    .filter((p) => p.median_decisions != null)
    .map((p, i) => {
      const x = xScale(p.ratio);
      const y = yDec(p.median_decisions as number);
      return `${i === 0 ? "M" : "L"}${x},${y}`;
    })
    .join(" ");

  return (
    <figure className="chart-card">
      <figcaption>{title}</figcaption>
      <svg viewBox={`0 0 ${w} ${h}`} role="img" aria-label={title} className="chart-svg">
        <defs>
          <linearGradient id="satFill" x1="0" y1="0" x2="0" y2="1">
            <stop offset="0%" stopColor="#c4a35a" stopOpacity="0.35" />
            <stop offset="100%" stopColor="#c4a35a" stopOpacity="0" />
          </linearGradient>
        </defs>
        {/* grid */}
        {[0, 0.25, 0.5, 0.75, 1].map((t) => (
          <line
            key={t}
            x1={pad.l}
            x2={w - pad.r}
            y1={ySat(t)}
            y2={ySat(t)}
            stroke="rgba(155,176,168,0.2)"
          />
        ))}
        <path d={satPath} fill="none" stroke="#c4a35a" strokeWidth="2.5" />
        <path d={decPath} fill="none" stroke="#6ec6a8" strokeWidth="2" strokeDasharray="5 4" />
        {points.map((p) =>
          p.sat_rate == null ? null : (
            <circle
              key={`s-${p.ratio}`}
              cx={xScale(p.ratio)}
              cy={ySat(p.sat_rate)}
              r="4"
              fill="#c4a35a"
            />
          )
        )}
        {points.map((p) =>
          p.median_decisions == null ? null : (
            <circle
              key={`d-${p.ratio}`}
              cx={xScale(p.ratio)}
              cy={yDec(p.median_decisions)}
              r="3.5"
              fill="#6ec6a8"
            />
          )
        )}
        {points.map((p) => (
          <text
            key={`x-${p.ratio}`}
            x={xScale(p.ratio)}
            y={h - 14}
            textAnchor="middle"
            className="chart-axis"
          >
            {p.ratio}
          </text>
        ))}
        <text x={pad.l} y={16} className="chart-legend gold">
          {y1Label}
        </text>
        <text x={w - pad.r} y={16} textAnchor="end" className="chart-legend mint">
          {y2Label}
        </text>
        <text x={w / 2} y={h - 2} textAnchor="middle" className="chart-axis">
          α = m/n
        </text>
      </svg>
    </figure>
  );
}

export function BarCompare({
  rows,
}: {
  rows: { solver: string; wall_time_seconds: number; decisions: number; satisfiable: boolean | null }[];
}) {
  const maxT = Math.max(1e-6, ...rows.map((r) => r.wall_time_seconds));
  return (
    <div className="bar-compare">
      {rows.map((r) => (
        <div key={r.solver} className="bar-row">
          <div className="bar-label">
            <strong>{r.solver}</strong>
            <span>
              {r.satisfiable === null ? "?" : r.satisfiable ? "SAT" : "UNSAT"} ·{" "}
              {r.wall_time_seconds.toFixed(4)}s · {r.decisions} decid.
            </span>
          </div>
          <div className="bar-track">
            <div
              className="bar-fill"
              style={{ width: `${(r.wall_time_seconds / maxT) * 100}%` }}
            />
          </div>
        </div>
      ))}
    </div>
  );
}
