import {
  Callout,
  Card,
  CardBody,
  CardHeader,
  CollapsibleSection,
  Divider,
  Grid,
  H1,
  H2,
  H3,
  Pill,
  Row,
  Stack,
  Stat,
  Table,
  Text,
  UsageBar,
  useHostTheme,
} from "cursor/canvas";

const BUILD_EVENTS = [
  { date: "2026-07-30 13:08", label: "Build GREEN (1368 jobs)", tone: "success" as const },
  { date: "2026-07-30 16:32–23:02", label: "Build paralelo fallido / atascado (~6.5 h)", tone: "danger" as const },
  { date: "2026-07-31 18:41", label: "Build GREEN verificado (1368 jobs, ~2h47m)", tone: "success" as const },
];

const PIPELINE = [
  { step: "461 emit discharge", status: "OK", detail: "ParametricDischargePart1/2/3 + All" },
  { step: "E2 projection mass", status: "OK", detail: "461/461 parametricProjOK (Python + Lean)" },
  { step: "Perm hash completo", status: "OK", detail: "topologyPermForEndpoints 461/461" },
  { step: "Perm (n,toArcs)", status: "Parcial", detail: "83/461 arc shape unique" },
  { step: "Perm (n,toArcs,p0)", status: "OK", detail: "461/461 clave mínima parcial" },
  { step: "Prop bridge", status: "OK", detail: "closureFromSaturated, parametricProjHolds, FreshG0" },
  { step: "Combinatorial gap", status: "Parcial", detail: "Witnesses⇔Discharge; sin ∀e sin emit" },
  { step: "Mathlib IsOuterplanar", status: "Blocked", detail: "Scaffold PNPLab; upstream ausente v4.32.0" },
  { step: "lake build PNPLab", status: "OK", detail: "31 jul 2026 18:41 local" },
];

const METRICS = [
  { metric: "Discharge emit", value: "461/461", pct: 100 },
  { metric: "Projection mass E2", value: "461/461", pct: 100 },
  { metric: "Perm endpoint hash", value: "461/461", pct: 100 },
  { metric: "Perm (n,toArcs) único", value: "83/461", pct: Math.round((83 / 461) * 100) },
  { metric: "Perm (n,toArcs,p0)", value: "461/461", pct: 100 },
  { metric: "Perm (n,toArcs,Vres)", value: "459/461", pct: Math.round((459 / 461) * 100) },
  { metric: "Smoke combinatorial", value: "7/461", pct: Math.round((7 / 461) * 100) },
];

const CEILINGS = [
  {
    id: "E5-1",
    title: "Discharge combinatorial ∀e sin emit",
    provable: "ForAll↔Witnesses; subclasses (fixedN, massWindow, arcP0, arcUnique); perm rename; sufficient bundles",
    impossible: "461 flags saturate + topology + arc_p0 como Prop sin emit/native_decide por instancia",
    status: "Ceiling documentado",
  },
  {
    id: "E5-2",
    title: "Perm sin forma cerrada combinatoria",
    provable: "Lookup 461/461; clave mínima (n,toArcs,p0); colisión Vres documentada (c6 idx 10 vs 18)",
    impossible: "Una sola fórmula de papel sin tabulación; 126/209 formas multi-perm",
    status: "Cerrado (honesto, catálogo)",
  },
  {
    id: "E5-3",
    title: "Mathlib SimpleGraph.IsOuterplanar",
    provable: "OuterplanarExportCert, local ≃ IsFacialOuterplanar, peel hooks, 7 smoke certs",
    impossible: "Reemplazar hook upstream hasta que Mathlib publique API",
    status: "Upstream blocked",
  },
];

const DISCOVERIES = [
  {
    title: "c8EndpointsEven corregido",
    body: "Se documentó projOK=false pero native_decide da true. Contraejemplo honesto: misma ventana de masa y mismo hop que c8Endpoints0123, pero discharge solo en semilla canónica.",
  },
  {
    title: "Nunca builds paralelos",
    body: "Varios lake build PNPLab simultáneos causaron OOM, .olean corruptos y rebuilds de 3–5 h. Regla: un solo build con LEAN_NUM_THREADS=2.",
  },
  {
    title: "Colisión Vres n=6",
    body: "arcs=(1,0,0,1): c6Endpoints0234 vs c6Endpoints1345 comparten forma pero distinto perm (idx 10 vs 18). (n,toArcs,Vres) no es clave universal (459/461).",
  },
  {
    title: "Monitor falsos WARN",
    body: "Durante Part2/Part3 el log no crece hasta terminar la fase; CPU alta + sin cambio olean ≠ atasco. Build 31 jul SUCCESS detectado 18:45.",
  },
  {
    title: "P vs NP no es el camino",
    body: "Category C completa infra de Width vs Δ / crossing law paramétrica. may_present=False; proximidad ~0 a P≠NP directo.",
  },
];

const ARTIFACTS = [
  { path: "lean/PNPLab/ParametricDischargePart*.lean", role: "461 emit discharge" },
  { path: "lean/PNPLab/CrossingTopologyPermLookup.lean", role: "Perm lookup + análisis 461" },
  { path: "lean/PNPLab/ParametricCombinatorialDischarge.lean", role: "Gap combinatorial + techos" },
  { path: "lean/PNPLab/MathlibBridge.lean", role: "Puente outerplanar local" },
  { path: "papers/REMAINING_CHECKLIST.md", role: "Checklist maestro" },
  { path: "papers/E5_GAPS_CHECKLIST.md", role: "Gaps G1–G8 + evidencia" },
  { path: "papers/MATHLIB_IS_OUTERPLANAR_MIGRATION.md", role: "Migración upstream" },
  { path: "scripts/resume_pnplab_build.ps1", role: "Build resumible + lock" },
  { path: "scripts/monitor_pnplab_build.ps1", role: "Monitor cada 10 min" },
  { path: "lean/build-resume.log", role: "Log build" },
  { path: "lean/build-monitor.log", role: "Log monitor" },
];

function toneForStatus(status: string): "success" | "warning" | "danger" | "neutral" {
  if (status === "OK") return "success";
  if (status === "Blocked") return "danger";
  if (status === "Parcial") return "warning";
  return "neutral";
}

export default function CategoryCE5Hallazgos() {
  const { tokens } = useHostTheme();

  return (
    <Stack gap={24} style={{ padding: 24, maxWidth: 960, color: tokens.text.primary }}>
      <Stack gap={8}>
        <Pill tone="success">Category C — infra cerrada</Pill>
        <H1>Hallazgos y descubrimientos — Width vs Δ / E5</H1>
        <Text style={{ color: tokens.text.secondary, lineHeight: 1.5 }}>
          Síntesis de todo lo construido, verificado y limitado en el repo bastardus (crossing law paramétrica,
          proyección G→R, perm topology, puente Mathlib). Actualizado tras build GREEN del 31 jul 2026 18:41.
        </Text>
      </Stack>

      <Grid columns={3} gap={12}>
        <Stat label="Discharge emit" value="461/461" tone="success" />
        <Stat label="Build PNPLab" value="GREEN" tone="success" sub="31 jul 2026 · 1368 jobs" />
        <Stat label="Techos abiertos" value="3" tone="warning" sub="límites, no bugs" />
      </Grid>

      <Callout tone="info" title="Veredicto en una frase">
        La tubería técnica está hecha y compila. Lo que queda son tres techos matemáticos documentados — no trabajo
        de implementación pendiente salvo pulido opcional.
      </Callout>

      <Divider />

      <Stack gap={12}>
        <H2>Pipeline Category C</H2>
        <Table
          columns={[
            { key: "step", header: "Componente", width: "28%" },
            { key: "status", header: "Estado", width: "14%" },
            { key: "detail", header: "Detalle" },
          ]}
          rows={PIPELINE.map((r) => ({
            step: r.step,
            status: <Pill tone={toneForStatus(r.status)}>{r.status}</Pill>,
            detail: r.detail,
          }))}
        />
      </Stack>

      <Stack gap={12}>
        <H2>Cobertura numérica</H2>
        <Text style={{ color: tokens.text.secondary, fontSize: 12 }}>
          Fuente: emit Python + Lean native_decide + análisis perm catalog
        </Text>
        {METRICS.map((m) => (
          <Stack key={m.metric} gap={4}>
            <Row style={{ justifyContent: "space-between" }}>
              <Text weight="medium">{m.metric}</Text>
              <Text style={{ color: tokens.text.secondary }}>{m.value}</Text>
            </Row>
            <UsageBar
              segments={[{ value: m.pct, label: m.value, color: m.pct === 100 ? "green" : m.pct >= 80 ? "blue" : "amber" }]}
              max={100}
            />
          </Stack>
        ))}
      </Stack>

      <Divider />

      <Stack gap={12}>
        <H2>Historial de builds (jul 2026)</H2>
        {BUILD_EVENTS.map((e) => (
          <Row key={e.date} gap={12} style={{ alignItems: "flex-start" }}>
            <Pill tone={e.tone}>{e.tone === "success" ? "OK" : "Issue"}</Pill>
            <Stack gap={2}>
              <Text weight="medium">{e.label}</Text>
              <Text style={{ color: tokens.text.secondary, fontSize: 12 }}>{e.date}</Text>
            </Stack>
          </Row>
        ))}
      </Stack>

      <Divider />

      <Stack gap={12}>
        <H2>Los 3 techos E5 (honestos)</H2>
        {CEILINGS.map((c) => (
          <CollapsibleSection
            key={c.id}
            header={
              <Row gap={8} style={{ alignItems: "center" }}>
                <Pill tone={c.status.includes("blocked") ? "danger" : "warning"}>{c.id}</Pill>
                <Text weight="medium">{c.title}</Text>
                <Pill tone="neutral">{c.status}</Pill>
              </Row>
            }
          >
            <Stack gap={8} style={{ paddingTop: 8 }}>
              <Stack gap={4}>
                <H3>Provable (sin emit / upstream)</H3>
                <Text style={{ color: tokens.text.secondary, lineHeight: 1.5 }}>{c.provable}</Text>
              </Stack>
              <Stack gap={4}>
                <H3>Techo / imposible ahora</H3>
                <Text style={{ color: tokens.text.secondary, lineHeight: 1.5 }}>{c.impossible}</Text>
              </Stack>
            </Stack>
          </CollapsibleSection>
        ))}
      </Stack>

      <Divider />

      <Stack gap={12}>
        <H2>Descubrimientos y correcciones</H2>
        <Grid columns={1} gap={8}>
          {DISCOVERIES.map((d) => (
            <Card key={d.title} variant="outline">
              <CardHeader title={d.title} />
              <CardBody>
                <Text style={{ color: tokens.text.secondary, lineHeight: 1.5 }}>{d.body}</Text>
              </CardBody>
            </Card>
          ))}
        </Grid>
      </Stack>

      <Divider />

      <Stack gap={12}>
        <H2>Artefactos clave en el repo</H2>
        <Table
          columns={[
            { key: "path", header: "Ruta", width: "45%" },
            { key: "role", header: "Rol" },
          ]}
          rows={ARTIFACTS}
        />
      </Stack>

      <Callout tone="warning" title="Fuera de alcance">
        Camino A/B P vs NP — claim-gate may_present=False. Completar Category C no desbloquea una prueba P≠NP.
      </Callout>

      <Text style={{ color: tokens.text.muted, fontSize: 11 }}>
        Canvas generado 2026-08-02 · repo bastardus · Lean 4.32.0 + Mathlib v4.32.0
      </Text>
    </Stack>
  );
}
