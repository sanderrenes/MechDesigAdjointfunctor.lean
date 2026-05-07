# MechDesigAdjointfunctor — Lean 4 Formalization

Formal proof in Lean 4 / Mathlib that Myerson's (1981) Revenue Equivalence Theorem and the Mirrlees (1971) Taxation Principle are both instances of a single categorical theorem: the allocation functor **Q : Mech → Alloc** has a right adjoint **T**, and every IC mechanism with a given allocation rule is isomorphic to T(q).

See `MechDesigAdjointfunctor/Unification.md` for the mathematical write-up.

## File structure

| File | Contents |
|------|----------|
| `Framework.lean` | Abstract categories Mech and Alloc, functor Q, IC_implies_monotone |
| `MasterTheorem.lean` | Transfer functor T, T_wellDefined, adj_Q_T, Master Theorem |
| `MyersonSetting.lean` | Myerson auction instantiation, Revenue Equivalence |
| `MirrleesSetting.lean` | Mirrlees taxation instantiation, Taxation Principle |
| `Corollaries.lean` | Corollaries 5.1 and 5.2 as instances of the Master Theorem |

## Proof status (as of 2026-05-07)

Build: `lake build` — completes successfully (2652 jobs, only `sorry` warnings).

### Completed ✓

| Lemma | File | Notes |
|-------|------|-------|
| `IC_implies_monotone` | Framework | MON from IC + SC via mimicry argument |
| Category laws (8 stubs) | Framework | `apply MechHom.ext/AllocHom.ext; funext; rfl` |
| `myerson_singleCrossing` | MyersonSetting | `nlinarith` |
| `myerson_vDiff` | MyersonSetting | `unfold myersonValue; fun_prop` |
| `mirrlees_vDiff` | MirrleesSetting | `DifferentiableOn.sub` + `DifferentiableOn.div`; domain `Set.Ioi 0` |
| `T_wellDefined` (IR branch) | MasterTheorem | `integral_same` + `sub_zero` + `linarith` |
| `T_wellDefined` (IC branch, physical) | MasterTheorem | FTC + SC + `HasDerivAt.nonneg_of_monotone` + `integral_mono_on` |
| `myerson_IC_of_monotone_transfer` | MyersonSetting | `integral_add_adjacent_intervals` + `integral_mono_on` + case split |
| `mirrlees_IC_of_envelope` | MirrleesSetting | Mirrors T_wellDefined; `hvθ` corrected to partial derivative |

### Remaining sorry stubs

| Lemma | File | Obstacle |
|-------|------|----------|
| `mirrlees_singleCrossing` | MirrleesSetting | Differentiability of SC-M condition |
| `myerson_transfer_unique` | MyersonSetting | Envelope theorem (convex analysis) |
| `mirrlees_unique_from_IC` | MirrleesSetting | Envelope theorem (convex analysis) |
| `taxation_principle` (local) | MirrleesSetting | Depends on only-if direction |
| `T_wellDefined` (non-physical case) | MasterTheorem | `hdiff` restricted to `Set.Ioi 0`; FTC unavailable for θ ≤ 0 |
| `mirrlees_IC_of_envelope` (non-physical) | MirrleesSetting | Same `Set.Ioi 0` restriction |
| `alloc_hasLimits` | Framework | **Architectural**: current `AllocHom` (reparametrizations) doesn't give a complete category; see below |
| `Q_preservesLimits` | Framework | Depends on `alloc_hasLimits` |
| `adj_Q_T` | MasterTheorem | Depends on uniqueness of envelope formula (sorry) |
| `T_terminal` | MasterTheorem | Depends on `adj_Q_T` |
| `masterTheorem_existence/isomorphism/transferInvariance` | MasterTheorem | Depend on `T_terminal` |
| `revenueEquivalence` | Corollaries | Uses `masterTheorem_transferInvariance` (sorry); also θ_min = 0 boundary |
| `taxationPrinciple` (corollary) | Corollaries | Uses `masterTheorem_transferInvariance` (sorry) |

### Architectural issue: `AllocHom` morphism convention

`alloc_hasLimits` is not provable under the current `AllocHom` definition (type-space reparametrizations φ : ℝ → ℝ with `r'.q ∘ φ = r.q`). Even a terminal object fails: uniqueness breaks for constant allocations.

The `Unification.md` proof sketch assumes a *different* morphism convention — pointwise value comparison `∀ θ, r.q θ ≤ r'.q θ`. Under that convention, `MonotoneAlloc A` is a poset and limits are immediate from `Pi.completeLattice`.

This does not block the main economic results: `adj_Q_T` and `masterTheorem_transferInvariance` do not take `alloc_hasLimits` as a hypothesis.

**Possible fix:** Redefine `AllocHom r r' : Prop := ∀ θ, r.q θ ≤ r'.q θ` (requires refactoring Q functor and category laws).

## Key proof patterns

- **`HasDerivAt.sub`**: always use explicit form, not dot notation (dot resolves to `HasFDerivAtFilter.sub`)
- **`intervalIntegrable_const`**: root namespace, not `intervalIntegral.`
- **`le_or_gt`**: case split in this Mathlib version (not `le_or_lt`)
- **`integral_symm θ θ'`**: gives `∫ in θ'..θ = -∫ in θ..θ'`
- **Non-physical sorry**: IC proofs leave `¬(0 < θ' ∧ 0 < θ)` as sorry — `DifferentiableOn (Set.Ioi 0)` makes FTC unavailable outside positive reals
- **`hvθ` correction**: partial derivative `deriv (v (y θ)) θ`, not total `deriv (fun s => v (y s) s) θ`

## Build

```bash
cd /path/to/MechDesigAdjointfunctor.lean
lake build
```
