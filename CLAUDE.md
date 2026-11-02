# CLAUDE.md — working agreement for this project

A Lean 4 / Mathlib formalisation arguing that Myerson's Revenue Equivalence and the
Mirrlees Taxation Principle are one theorem. Read `README.md` for the three-move arc,
`PLAN.md` for what is being built next, `DECISIONS.md` for why the design is what it is.

## Project files you must keep current

| File | What it holds | When to touch it |
|------|---------------|------------------|
| `TODO.md` | Living task list | **Every** commit that changes task status |
| `PLAN.md` | The phased plan and acceptance criteria | When a phase starts, changes shape, or completes |
| `DECISIONS.md` | Append-only decision log | Whenever a design choice is made *or reversed* |
| `README.md` | The arc, the design rationale, proof status | When the architecture or proof status changes |
| `docs/*.html` | The talk and the dependency graph | **Only when explicitly asked.** See below. |

`docs/` is the exception to everything above. The two HTML pages there — the category-theory
talk and the dependency graph — are **finished arguments, not living documents**. Do not
regenerate, refresh or "bring them up to date" on your own initiative; a well-meant edit that
drifts from the version being presented is worse than a stale one. If the Lean changes in a way
that falsifies something they claim, put it in `TODO.md` and leave the pages alone.

## Obligations

These are not suggestions. A phase is not done until all four hold.

1. **Update `TODO.md` in the same commit as the work.** Tick what closed, add what the work
   uncovered. A stale TODO is worse than none — it will be trusted.
2. **Log every decision in `DECISIONS.md`**, with the *alternative rejected and why*. A
   decision without its discarded alternative is just a description, and the next session
   will re-litigate it. Record a decision **before** implementing it, not after.
3. **Update project memory** (`/memories`) when something is learned that is not
   reconstructible from the code or git history — a dead end, a mathlib gap, a hypothesis
   that turned out false. Not for things the code already says.
4. **`git commit` at the end of every phase.** Never mid-phase with a broken build. The
   commit message states what changed *and what it cost*.

## Quality gate — every commit

- `lake build` clean.
- **Zero sorries.** This project has none; it stays that way. If a proof needs a `sorry`,
  the statement is wrong — fix the statement, or stop and say so.
- Axioms are exactly `[propext, Classical.choice, Quot.sound]`. Check with `#print axioms`
  on anything new. A custom axiom is never acceptable without explicit approval.
- Never weaken a theorem to make it compile without saying so, in the commit message and in
  `DECISIONS.md`.

## Verifying claims about this codebase

Two techniques have already produced **wrong answers** here. Do not repeat them.

- **`ConstantInfo.value?` returns `none` for theorems** in this Lean version. Walking proof
  terms to compute dependencies therefore silently returns nothing and every probe comes
  back `false`. It looks like a clean result. It is not.
- **A token scan misses real uses.** Anonymous constructors (`{ h := f.hAlloc }`), field
  projections (`f.h`), and instance resolution (`allocHom_subsingleton`) never name the
  declaration. A grep-built dependency graph showed `AllocHom` as an unused leaf when it is
  in fact the sole premise of `T.map`.

**The reliable test is deletion:** comment the declaration out, run `lake build`, see what
breaks. It cannot lie. Use it before claiming anything is unused, load-bearing, or vacuous.

## Lean version and module system

- Lean and Mathlib `v4.35.0`, since the port merged on 2026-11-01. Evidence and steps: `docs/PLAN_lean_module_and_version_port.md` in the workspace repo.
- Every Lean file here is a `module`. A new file starts with `module`, imports with `public import`, and puts its declarations in `@[expose] public section`. A `module` file cannot import a non-`module` file.
- `.lake/packages` is a symlink to the shared Mathlib, `~/claude_projects/lake-shared/mathlib-v4.35.0/packages`. Do not run two builds at the same time and do not delete that folder. The old v4.30 packages are kept as `.lake/packages-v4.30`.
- To roll back, see `.local/lean-4.35-port-rollback.md` in the workspace repo.

## Lean conventions

- 100-character lines (mathlib style), not 80.
- Docstrings are **prose, not statements** — Lean does not check them. One already claimed
  `V(θ_min) = 0` while the definition said `≥ 0` (see D4). When you change a definition,
  read its docstring.
- Thin categories: functor laws, naturality, and triangle identities all discharge with
  `@Subsingleton.elim _ mechHom_subsingleton _ _` / `allocHom_subsingleton`.
- The IDE's diagnostics go stale after a structure changes. Trust
  `lake env lean <file>` over the editor squiggles.
- Prefer the `/lean4:*` workflow: `/lean4:prove` to work, `/lean4:checkpoint` to land.

## Key proof patterns (checked on Lean and Mathlib v4.35.0, 2026-11-02)

Moved here from the old outer `declarative-only-proofs/mechdesign-adjoint-functor/CLAUDE.md`, which is not in git. Each was rechecked against
the v4.35 sources and a small test file:

- **FTC domain**: all FTC arguments restrict to `Set.Ici θ_min` (not `Set.univ`), so `θ_min > 0` is available and no `sorry` is needed for
  non-physical types. Still the rule (47 uses).
- **`hvθ`**: the relevant partial derivative is `deriv (v (y θ)) θ`, not the total derivative `deriv (fun s => v (y s) s) θ`.
  Still the hypothesis form in `MirrleesSetting.lean`.
- **Thin category laws**: morphism uniqueness (`MechHom`, `AllocHom`) is discharged by `Subsingleton.elim` (28 uses).
- **`le_or_gt`**: case split with this lemma. In v4.35 `le_or_lt` no longer exists at all (`Unknown identifier`).
- **`intervalIntegrable_const`**: use it from the root namespace; `intervalIntegral.intervalIntegrable_const` is an unknown constant in v4.35.
- **`integral_symm a b`**: `∫ x in b..a, f x = -∫ x in a..b, f x`; needed when swapping interval endpoints. Unchanged.
- **`HasDerivAt.sub`**: the code uses the explicit non-dot form (5 uses). The old warning was that dot notation resolved to
  `HasFDerivAtFilter.sub`; in a simple test on v4.35 `hf.sub hg` worked, so this is a habit now, not a necessity. Untested on the larger proofs.

Removed from the old list: the `h_spread` field. `MechHom` and `AllocHom` no longer carry it (see the *Design note* in `Framework.lean`),
so the thin-category proofs no longer need it.

## Status (was: standing warning)

**The IC ⟹ envelope bridge is closed.** `hEnv` is no longer assumed anywhere in the
master-theorem chain: `surplus_hasDerivWithinAt` derives it from `hIC` via the Milgrom–Segal
squeeze, and `surplus_lipschitzOn` derives continuity of the surplus from the IC sandwich. The
theorems *are* now about IC mechanisms — you may describe them that way.

What survives as a hypothesis is `hW`: continuity of `(s, u) ↦ ∂_θ v(q s, u)` at the diagonal
from the upper right. It is stated on the composite because `A` carries no topology. In the
Myerson setting it is exactly right-continuity of `q`, and the posted price satisfies it.

Two things worth remembering, because they are counter-intuitive:

- **Revenue equivalence needs neither single crossing nor IR.** SC makes `T` a functor; IR
  orients the adjunction `T ⊣ Q`. Neither is used by `masterTheorem_transferInvariance`.
- **`adj_T_Q` has no consumer, and that is correct.** An adjunction is *structure*, not a
  lemma. Do not contrive a dependency on it to make the dependency graph look better.
