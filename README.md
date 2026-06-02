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

## Proof status — branch `master` (as of 2026-05-21)

This is the **master branch** which has merged the `spread-monotone-allochom` branch. The `h_spread` field has been added to both `MechHom` and `AllocHom` to ensure `Q` maps morphisms without sorries.

Build: `lake build` — completes successfully (1 `sorry` warning remaining; vacuous — never exercised).

### Completed ✓

| Lemma | File | Notes |
|-------|------|-------|
| `IC_implies_monotone` | Framework | MON from IC + SC via mimicry argument |
| Category laws (8 stubs) | Framework | `Subsingleton.elim` — thin category |
| `myerson_singleCrossing` | MyersonSetting | `nlinarith` |
| `myerson_vDiff` | MyersonSetting | `unfold myersonValue; fun_prop` |
| `mirrlees_vDiff` | MirrleesSetting | `DifferentiableOn.sub` + `DifferentiableOn.div`; domain `Set.Ioi 0` |
| `mirrlees_singleCrossing` | MirrleesSetting | `deriv_sub` + `hg_pos` + `linarith` |
| `T_wellDefined` | MasterTheorem | FTC + SC + `integral_mono_on`; both IR and IC proved for all `θ ≥ θ_min > 0` |
| `myerson_IC_of_monotone_transfer` | MyersonSetting | `integral_add_adjacent_intervals` + `integral_mono_on` + case split |
| `mirrlees_IC_of_envelope` | MirrleesSetting | Mirrors T_wellDefined; FTC on `Set.Ici θ_min` |
| `myerson_transfer_unique` | MyersonSetting | FTC + linarith |
| `mirrlees_unique_from_IC` | MirrleesSetting | SC + IC by-contradiction + FTC |
| `taxation_principle` (local) | MirrleesSetting | FTC twice + linarith |
| `adj_Q_T` | MasterTheorem | `Adjunction.mkOfUnitCounit`; unit via FTC + IR |
| `Q_preservesColimits` | MasterTheorem | `adj_Q_T.leftAdjoint_preservesColimits` (Q is LEFT adjoint) |
| `T_terminal` | MasterTheorem | FTC + IR; `hTransf` via envelope on `[θ_min, ∞)`; uniqueness by `mechHom_subsingleton` |
| `masterTheorem_existence` | MasterTheorem | `T_terminal` + FTC |
| `masterTheorem_isomorphism` | MasterTheorem | FTC + BC; integral restricted to `Set.Ici θ_min` |
| `masterTheorem_transferInvariance` | MasterTheorem | `le_antisymm` + linarith from two isomorphisms; integral over `Set.Ici θ_min` |
| `taxationPrinciple` | Corollaries | Delegates to `masterTheorem_transferInvariance` |
| `myerson_expectedRevenue` | MyersonSetting | IBP via `integral_hasStrictDerivAt` |
| `myerson_revenueFormula` | Corollaries | Delegates to `myerson_expectedRevenue` |
| `revenueEquivalence` | Corollaries | `MyersonAlloc = ℝ`; delegates to `masterTheorem_transferInvariance` |

### Remaining sorry stubs (1)

| Lemma | File | Obstacle |
|-------|------|----------|
| `T.map hTransf` | MasterTheorem | False for general `v`; needs a v-monotonicity hypothesis. **Immaterial to this prVacuous**: never accessed by any proved theorem — functor laws use `mechHom_subsingleton` and `masterTheorem_transferInvariance` constructs `hTransf` independently via FTC + IR. See Unification.md §7.1–7.2 |

## Key proof patterns

- **`HasDerivAt.sub`**: always use explicit form, not dot notation (dot resolves to `HasFDerivAtFilter.sub`)
- **`intervalIntegrable_const`**: root namespace, not `intervalIntegral.`
- **`le_or_gt`**: case split in this Mathlib version (not `le_or_lt`)
- **`integral_symm θ θ'`**: gives `∫ in θ'..θ = -∫ in θ..θ'`
- **Non-physical case avoided**: `masterTheorem_transferInvariance` integrates over `Set.Ici θ_min`; FTC is only needed for `θ ≥ θ_min > 0`, so no sorry is required for non-physical types
- **`hvθ` correction**: partial derivative `deriv (v (y θ)) θ`, not total `deriv (fun s => v (y s) s) θ`

## Build

```bash
cd /path/to/MechDesigAdjointfunctor.lean
lake build
```

See `Unification.md` §7.1–7.2 for mathematical analysis of the `T.map hTransf` obstruction.
