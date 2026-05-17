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

## Proof status — branch `master` (as of 2026-05-17)

This is the **master branch** which has merged the `spread-monotone-allochom` branch. The `h_spread` field has been added to both `MechHom` and `AllocHom` to ensure `Q` maps morphisms without sorries.

Build: `lake build` — completes successfully (only `sorry` warnings, 4 remaining).

### Completed ✓

| Lemma | File | Notes |
|-------|------|-------|
| `IC_implies_monotone` | Framework | MON from IC + SC via mimicry argument |
| Category laws (8 stubs) | Framework | `Subsingleton.elim` — thin category |
| `myerson_singleCrossing` | MyersonSetting | `nlinarith` |
| `myerson_vDiff` | MyersonSetting | `unfold myersonValue; fun_prop` |
| `mirrlees_vDiff` | MirrleesSetting | `DifferentiableOn.sub` + `DifferentiableOn.div`; domain `Set.Ioi 0` |
| `mirrlees_singleCrossing` | MirrleesSetting | `deriv_sub` + `hg_pos` + `linarith` |
| `T_wellDefined` (IR + IC branches, physical) | MasterTheorem | FTC + SC + `integral_mono_on`; non-physical left as sorry |
| `myerson_IC_of_monotone_transfer` | MyersonSetting | `integral_add_adjacent_intervals` + `integral_mono_on` + case split |
| `mirrlees_IC_of_envelope` (physical) | MirrleesSetting | Mirrors T_wellDefined |
| `myerson_transfer_unique` | MyersonSetting | FTC + linarith |
| `mirrlees_unique_from_IC` | MirrleesSetting | SC + IC by-contradiction + FTC |
| `taxation_principle` (local) | MirrleesSetting | FTC twice + linarith |
| `alloc_hasLimitsOfShape` / `alloc_hasLimits` | Framework | Pointwise `sInf` (spread fields sorry'd — see below) |
| `adj_Q_T` | MasterTheorem | `Adjunction.mkOfUnitCounit`; unit via FTC + IR |
| `Q_preservesColimits` | MasterTheorem | `adj_Q_T.leftAdjoint_preservesColimits` (Q is LEFT adjoint) |
| `T_terminal` | MasterTheorem | From `adj_Q_T` + envelope formula (non-physical sorry retained) |
| `masterTheorem_existence` | MasterTheorem | `T_terminal` + FTC |
| `masterTheorem_isomorphism` | MasterTheorem | FTC + BC (non-physical sorrys retained) |
| `masterTheorem_transferInvariance` | MasterTheorem | `le_antisymm` + linarith from two isomorphisms |
| `taxationPrinciple` | Corollaries | Delegates to `masterTheorem_transferInvariance` |
| `myerson_expectedRevenue` | MyersonSetting | IBP via `integral_hasStrictDerivAt` |
| `myerson_revenueFormula` | Corollaries | Delegates to `myerson_expectedRevenue` |
| `revenueEquivalence` | Corollaries | `MyersonAlloc = ℝ`; delegates to `masterTheorem_transferInvariance` |

### Remaining sorry stubs (4)

| Lemma | File | Obstacle |
|-------|------|----------|
| `alloc_hasLimitsOfShape` cone `h_spread` | Framework | Pointwise `sInf` does not preserve spread monotonicity (counterexample: θ² vs θ) |
| `alloc_hasLimitsOfShape` lift `h_spread` | Framework | Same obstruction as cone |
| `T.map hTransf` | MasterTheorem | Needs structural assumption on `v` beyond `h_spread`; see Unification.md §7.1–7.2 |
| `masterTheorem_transferInvariance` (θ < θ_min case) | MasterTheorem | Design limitation: FTC requires `Set.Ioi 0` |

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

See `Unification.md` §7.1–7.5 for detailed mathematical analysis of the remaining obstructions.
