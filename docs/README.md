# docs

Two self-contained HTML pages. Open them in a browser; there is no build step and no
external asset — a strict CSP forbids one, so all CSS and JS is inline.

| File | What it is |
|------|------------|
| `functoriality-talk.html` | The talk: *Functoriality is a correctness condition on economic definitions*. Written for an audience of **category theorists**. The economics and the category theory run in parallel columns; the Lean sits between them as the arbiter. |
| `dependency-graph.html` | The dependency graph of every declaration on `surplus-order`: what rests on what, the IC ⟹ envelope bridge in red, the category-theory region hatched, and the *storyline* — the backward cone of the two corollaries — as a green corridor. |

## These are frozen

**Do not update them as a matter of course.** Unlike `README.md`, `TODO.md`, `PLAN.md` and
`DECISIONS.md` — which the working agreement in `CLAUDE.md` requires you to keep current — these
two are updated **only when explicitly asked**. They are finished arguments, not living
documents, and a well-meant edit that drifts away from the version being presented is worse than
a stale one.

If the Lean changes in a way that falsifies something they say, note it in `TODO.md` and leave
the pages alone until asked.

## One thing to know before editing the graph

The two SVG figures in `functoriality-talk.html` share a single arrowhead definition
(`<marker id="ar">`), declared in the first figure. Delete or reorder the figures and the
arrowheads in the other one vanish silently — the page still renders, just without arrows.
