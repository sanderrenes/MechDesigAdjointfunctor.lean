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
