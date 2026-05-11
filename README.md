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

## Proof status (as of 2026-05-11)

Build: `lake build` — completes successfully (only `sorry` warnings, 9 remaining).

### Completed ✓

| Lemma | File | Notes |
|-------|------|-------|
| `IC_implies_monotone` | Framework | MON from IC + SC via mimicry argument |
| Category laws (8 stubs) | Framework | `Subsingleton.elim` — thin category |
| `alloc_hasLimitsOfShape` / `alloc_hasLimits` | Framework | Pointwise `sInf`; `alloc_hasLimitsOfSize` bridges to `HasLimitsOfSize` |
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
| `alloc_hasLimits` | Framework | Complete; `alloc_hasLimitsOfSize` bridges |
| `adj_Q_T` | MasterTheorem | `Adjunction.mkOfUnitCounit`; unit via FTC + IR |
| `Q_preservesColimits` | MasterTheorem | `adj_Q_T.leftAdjoint_preservesColimits` (Q is LEFT adjoint) |
| `T_terminal` | MasterTheorem | From `adj_Q_T` + envelope formula |
| `masterTheorem_existence` | MasterTheorem | `T_terminal` + FTC |
| `masterTheorem_isomorphism` | MasterTheorem | FTC + BC (non-physical sorry retained) |
| `masterTheorem_transferInvariance` | MasterTheorem | `le_antisymm` + linarith from two isomorphisms |
| `taxationPrinciple` | Corollaries | Delegates to `masterTheorem_transferInvariance` |
| `myerson_expectedRevenue` | MyersonSetting | IBP via `integral_hasStrictDerivAt` |
| `myerson_revenueFormula` | Corollaries | Delegates to `myerson_expectedRevenue` |

### Remaining sorry stubs

| Lemma | File | Obstacle |
|-------|------|----------|
| `T_wellDefined` (θ ≤ 0 case) | MasterTheorem | Design limitation: FTC requires `Set.Ioi 0` |
| `T.map hTransf` | MasterTheorem | **Mathematically false** for general AllocHoms; see Unification.md §7.1 |
| `adj_Q_T` unit (θ ≤ 0 case) | MasterTheorem | Design limitation |
| `T_terminal` (θ ≤ 0 case) | MasterTheorem | Design limitation |
| `masterTheorem_isomorphism` (θ ≤ 0 case) | MasterTheorem | Design limitation |
| `mirrlees_IC_of_envelope` (θ ≤ 0 case) | MirrleesSetting | Design limitation |
| `revenueEquivalence` | Corollaries | `MyersonAlloc = Set.Icc 0 1` is not `AddCommGroup`; see Unification.md §7.5 |

### Branch: spread-monotone-allochom

The branch `spread-monotone-allochom` experiments with enriching `AllocHom` with a spread-monotonicity condition `h_spread : Monotone (fun θ => r'.q θ - r.q θ)`, which is necessary to prove `T.map.hTransf`. See `Unification.md` §7.1–7.5 for a detailed analysis of findings, including the terminal object structure and the incompatibility with `alloc_hasLimitsOfShape`.

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
