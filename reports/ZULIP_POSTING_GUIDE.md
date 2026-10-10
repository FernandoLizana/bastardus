# Zulip posting guide — ChordWidth community outreach

**Purpose:** Step-by-step instructions for posting to Lean Zulip (and optionally MathOverflow).  
**Draft content:** [COMMUNITY_QUESTION_DRAFT.md](COMMUNITY_QUESTION_DRAFT.md)  
**You post manually** — do not share secrets, `.env` files, or private repo URLs.

---

## English

### 1. Open Lean Zulip

Go to: **https://leanprover.zulipchat.com/**

Log in with your Lean community account (GitHub or email signup).

### 2. Choose a stream

| Stream | When to use |
|--------|-------------|
| **#mathlib4** | Best for Question A (Mathlib treewidth API, PR #38334) and Question B (proof strategy). |
| **#new members** | Broader visibility; good if you want general feedback or collaborators (Question C). |

**Recommendation:** Post **Question A + B** in `#mathlib4`. Post **Question C** separately in `#new members` only if you want collaboration outreach — or fold C into the same thread as a short closing paragraph.

### 3. Copy-paste from COMMUNITY_QUESTION_DRAFT

Open [COMMUNITY_QUESTION_DRAFT.md](COMMUNITY_QUESTION_DRAFT.md) and paste in this order:

| Section | Paste? | Notes |
|---------|--------|-------|
| **§1 Context (paste first)** | ✅ Yes | One message — sets up the project. |
| **Question A** | ✅ Yes | Mathlib treewidth / PR #38334. |
| **Question B** | ✅ Yes | tw(L(G)) proof strategy from K₄/C₄ core. |
| **Question C** | Optional | Collaboration pointer; trim if `#mathlib4`-only. |
| **§2 MathOverflow** | ❌ No on Zulip | Use only for MathOverflow (see §5 below). |

**Formatting tips:**
- Zulip supports `$...$` and `$$...$$` for LaTeX in many streams — preview before sending.
- Keep each question as its own message or a clearly separated block so replies stay threaded.
- Mention evidence numbers briefly (2870/2870 exact n≤14, 383/383 representative n≤100) but label them **computational evidence, not proof**.

### 4. What to expect / how to link PNPLab

**What to expect:**
- Replies may point to existing Mathlib lemmas, suggest upgrading the pin, or recommend waiting for PR #38334.
- Reviewers may ask whether you need pathwidth before treeWidth — have [FASE5_ROADMAP.md](FASE5_ROADMAP.md) handy for context.
- Turnaround: hours to days depending on stream activity.

**How to link the repo (no secrets):**
- If the repo is **public on GitHub**, share the public URL and point to:
  - `papers/CHORD_DIAGRAM_TSEITIN_WIDTH.md` — paper skeleton
  - `reports/LITERATURE_TSEITIN_WIDTH.md` — literature audit
  - `reports/CHORD_WIDTH_LEAN_STATUS.md` — Lean build status
  - `reports/CHORD_TREewidth_EXACT_N5_N14.md` — exact Python validation
- If the repo is **private**, do **not** paste tokens or invite links in Zulip. Instead:
  - Offer to paste relevant Lean snippets inline.
  - Attach or link **public** artifacts only (e.g. a gist of the audit summary, or CSV summary tables).
  - Say you can share read access on request via DM.

**Do not share:**
- API keys, `.env`, credentials, or internal deployment URLs.
- Claims that 2870/2870 or 383/383 constitute a mathematical proof.

### 5. Optional — MathOverflow

1. Go to **https://mathoverflow.net/** (requires reputation or signup).
2. Click **Ask Question**.
3. Copy from [COMMUNITY_QUESTION_DRAFT.md](COMMUNITY_QUESTION_DRAFT.md) §2:
   - **Title** (use as-is or shorten slightly)
   - **Context**, **Precise question**, **What we've verified**, **What we need**
4. Add tags: `graph-theory`, `treewidth`, `line-graph`, `resolution`, `propositional-proof-complexity`.
5. Cite Galesi et al. 2020 and Harvey–Wood 2019 in the references block.
6. Clearly label Python sweeps as **computational evidence** with exact vs heuristic caveats.

MathOverflow is slower but reaches graph theorists outside the Lean community.

---

## Español

### 1. Abrir Lean Zulip

Ir a: **https://leanprover.zulipchat.com/**

Iniciar sesión con tu cuenta de la comunidad Lean (GitHub o registro por email).

### 2. Elegir un stream

| Stream | Cuándo usarlo |
|--------|---------------|
| **#mathlib4** | Ideal para Pregunta A (API de treewidth en Mathlib, PR #38334) y Pregunta B (estrategia de prueba). |
| **#new members** | Mayor visibilidad; útil para colaboradores (Pregunta C). |

**Recomendación:** Publicar **Pregunta A + B** en `#mathlib4`. Publicar **Pregunta C** en `#new members` solo si buscas colaboración — o añadirla al final del mismo hilo.

### 3. Copiar-pegar desde COMMUNITY_QUESTION_DRAFT

Abrir [COMMUNITY_QUESTION_DRAFT.md](COMMUNITY_QUESTION_DRAFT.md) y pegar en este orden:

| Sección | ¿Pegar? | Notas |
|---------|---------|-------|
| **§1 Context (paste first)** | ✅ Sí | Un mensaje — presenta el proyecto. |
| **Pregunta A** | ✅ Sí | Treewidth en Mathlib / PR #38334. |
| **Pregunta B** | ✅ Sí | Estrategia tw(L(G)) desde núcleo K₄/C₄. |
| **Pregunta C** | Opcional | Colaboración; recortar si solo `#mathlib4`. |
| **§2 MathOverflow** | ❌ No en Zulip | Solo para MathOverflow (ver §5). |

**Consejos de formato:**
- Zulip suele soportar LaTeX con `$...$` y `$$...$$` — previsualizar antes de enviar.
- Cada pregunta en un mensaje separado o bloque claro para mantener el hilo ordenado.
- Mencionar cifras (2870/2870 exacto n≤14, 383/383 representativo n≤100) como **evidencia computacional, no prueba**.

### 4. Qué esperar / cómo enlazar PNPLab

**Qué esperar:**
- Respuestas pueden señalar lemas ya en Mathlib, sugerir actualizar el pin, o recomendar esperar al PR #38334.
- Pueden preguntar si conviene pathwidth antes que treeWidth — tener [FASE5_ROADMAP.md](FASE5_ROADMAP.md) a mano.
- Plazo de respuesta: horas o días según actividad del stream.

**Cómo enlazar el repo (sin secretos):**
- Si el repo es **público en GitHub**, compartir la URL pública y apuntar a:
  - `papers/CHORD_DIAGRAM_TSEITIN_WIDTH.md`
  - `reports/LITERATURE_TSEITIN_WIDTH.md`
  - `reports/CHORD_WIDTH_LEAN_STATUS.md`
  - `reports/CHORD_TREewidth_EXACT_N5_N14.md`
- Si el repo es **privado**, **no** pegar tokens ni enlaces de invitación en Zulip. En su lugar:
  - Ofrecer pegar fragmentos Lean relevantes en el hilo.
  - Adjuntar solo artefactos **públicos** (gist del audit, tablas resumen).
  - Indicar que puedes dar acceso de lectura bajo solicitud por DM.

**No compartir:**
- Claves API, `.env`, credenciales, URLs internas de despliegue.
- Afirmaciones de que 2870/2870 o 383/383 son prueba matemática.

### 5. Opcional — MathOverflow

1. Ir a **https://mathoverflow.net/** (requiere reputación o registro).
2. Clic en **Ask Question**.
3. Copiar de [COMMUNITY_QUESTION_DRAFT.md](COMMUNITY_QUESTION_DRAFT.md) §2: título, contexto, pregunta precisa, verificación, lo que necesitamos.
4. Tags sugeridos: `graph-theory`, `treewidth`, `line-graph`, `resolution`, `propositional-proof-complexity`.
5. Citar Galesi et al. 2020 y Harvey–Wood 2019.
6. Etiquetar los barridos Python claramente como **evidencia computacional** con las salvedades exacto vs heurístico.

MathOverflow es más lento pero llega a teóricos de grafos fuera de Lean.

---

## Quick checklist / Lista rápida

- [ ] Elegido stream / stream chosen
- [ ] Context pegado / Context pasted
- [ ] Preguntas A–B (y C si aplica) / Questions A–B (and C if applicable)
- [ ] Evidencia etiquetada como computacional / Evidence labeled as computational
- [ ] Sin secretos en el post / No secrets in post
- [ ] (Opcional) MathOverflow / (Optional) MathOverflow
