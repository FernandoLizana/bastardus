import type { ReactNode } from "react";

export function EvidenceBadge({ level, claim }: { level: string; claim?: string }) {
  return (
    <div className="evidence-badge" title="Nivel de evidencia científica">
      <span className="eb-level">{level}</span>
      {claim ? <span className="eb-claim">{claim}</span> : null}
    </div>
  );
}

export function HelpTip({ title, children }: { title: string; children: ReactNode }) {
  return (
    <details className="help-tip">
      <summary>{title}</summary>
      <div className="help-tip-body">{children}</div>
    </details>
  );
}
