# MechDesigAdjointfunctor — Lean 4 Formalization

Formal proof in Lean 4 / Mathlib that Myerson's (1981) Revenue Equivalence Theorem and the Mirrlees (1971) Taxation Principle are both instances of a single categorical theorem about the transfer functor **T : Alloc → Mech** and the allocation functor **Q : Mech → Alloc**.

See `MechDesigAdjointfunctor/Unification.md` for the mathematical write-up.

## Incentive compatibility is load-bearing (the envelope bridge)

The envelope condition is **derived from IC**, not assumed. This was the project's largest
gap and it is now closed:

1. **`surplus_ic_sandwich`** — pure `hIC`, no analysis at all. Each type declining to mimic
   the other bounds the surplus change on both sides by increments of `v(a, ·)` along a
   *fixed* allocation:
   ```
   v(q θ₁, θ₂) − v(q θ₁, θ₁)  ≤  V(θ₂) − V(θ₁)  ≤  v(q θ₂, θ₂) − v(q θ₂, θ₁)
   ```
2. **`surplus_lipschitzOn` → `surplus_continuousOn`** — the sandwich plus a Lipschitz-in-the-
   type condition on `v` gives continuity of the surplus. Discharged in both settings
   (`myerson_lipschitz`, `mirrlees_lipschitz`).
3. **`surplus_hasDerivWithinAt`** — Milgrom–Segal. Divide the sandwich by `y − θ > 0`; the
   lower bound is a slope of `v(q θ, ·)`; the upper bound the mean value theorem turns into
   `∂_θ v(q y, ξ)` for `ξ ∈ (θ, y)`. Squeeze.

**The envelope hypothesis is one-sided, and it has to be.** A two-sided `HasDerivAt` is not
merely strong — it is **false** for the canonical optimal auction. A posted price with reserve
`p` has surplus `max(θ − p, 0)`, a kink at `p`, no derivative
(`PostedPrice.postedPrice_not_hasDerivAt`). The old formulation therefore *excluded every
auction with a reserve price*. The right derivative survives the kink, and the posted price
now satisfies every hypothesis the framework asks: `postedPrice_hasEnvelope`,
`postedPrice_lipschitz`, `postedPrice_hW`.

**What revenue equivalence does *not* need:** single crossing or IR. SC makes `T` a functor;
IR orients the adjunction. Neither is used by `masterTheorem_transferInvariance`, and the
corollaries no longer pretend otherwise.

## The paper's arc, in three moves

The categorical content is organised as a reflection followed by its normalisation. Each move is fully proved; nothing below rests on a `sorry`.

### Move 1 — the general case: `T ⊣ Q`

**Mech** fibers over **Alloc** via `Q`. The fiber coordinate is the *boundary rent* `V(θ_min) ≥ 0` — the surplus conceded to the lowest type. This is the content of `surplus_split`, the envelope theorem in surplus form:

```
V_m(θ)  =  V_m(θ_min)  +  ∫_{θ_min}^{θ} (∂v/∂s)(r.q s, s) ds
```

Every BIC-IR mechanism over an allocation `r` is the envelope mechanism displaced by a single constant. `T(r)` is the member with rent `0` — the rent-extracting mechanism — so it sits at the *bottom* of its fiber. Hence:

- `adj_T_Q` : **`T ⊣ Q`**, with `T` the **left** adjoint (not `Q ⊣ T`).
- `T_initial` : `T(r)` is **initial** in `Mech_r`, not terminal. Individual rationality is what pins the direction — it is used essentially in the counit.
- `T_full`, `T_faithful` : `T` is **fully faithful**, exhibiting **Alloc** as a coreflective subcategory of **Mech**.
- `T_preservesColimits`, `Q_preservesLimits` : the usual consequences, with the corrected variance.

### Move 2 — the comonad: `T ∘ Q` strips the rent

`zeroRent_TQ` : `T(Q(m))` always has zero rent, whatever rent `m` had. So the counit `ε_m : T(Q(m)) ⟶ m` is literally the operation *"remove the lowest type's rent"*, and `T ∘ Q` is the idempotent comonad that performs it. `ε_m` is an isomorphism **exactly** on the zero-rent objects.

This is where revenue equivalence lives: two mechanisms over the same allocation with the same rent have the same image under the comonad and the same offset from it, hence are isomorphic (`mechIso_of_sameAlloc_sameRent`). And `transfer_eq_of_iso` shows an isomorphism in **Mech** *forces equal transfers* — so the category is genuinely load-bearing, not decorative.

### Move 3 — the normalized case: `Alloc ≌ Mech₀`

Restrict to `Mech₀`, the full subcategory of zero-rent mechanisms (`ZeroRent`). There the counit is an isomorphism, so `T ⊣ Q` upgrades to an **adjoint equivalence**:

```
equivAllocMech₀ :  MonotoneAlloc A  ≌  Mech₀ A v θ_min
```

`T₀ ⊣ Q₀` **and** `Q₀ ⊣ T₀` — adjoint in both directions. This is the **Taxation Principle**: normalized mechanisms *are* allocations, up to natural isomorphism.

**Where the content actually is.** Move 3 is cheap, as equivalences always are. The work is in Move 1 (that `T` exists at all — `T_wellDefined`) and Move 2 (that the counit is iso *precisely* at zero rent). A reader should be pointed at those, not at the equivalence.

## Why morphisms are ordered by surplus, not by transfer

`MechHom` carries `hSurp : ∀ θ ≥ θ_min, V_m θ ≤ V_m' θ`, where `V(θ) = v(q θ, θ) − t θ`. It does **not** carry a transfer condition. This is forced:

- Ordering by `t` makes `T` **not a functor**. `t*(r) ≤ t*(r')` does not follow from `r.q ≤ r'.q` for general `v`; it needs *convexity of `v` in the allocation*, which `mirrleesValue y θ = θ·h(y) − g(y/θ)` fails in the standard regime (`h` concave, `g` convex). A transfer field therefore breaks the Mirrlees instantiation and destroys the unification.
- Ordering by `V` makes `T.map` follow from **single crossing alone** (`Tmech_surplus_mono`) — an assumption both settings already make. Quasilinearity (the numeraire enters utility linearly) means `t` is recoverable as `t θ = v(q θ) θ − V θ`, so **no information about transfers is lost**; the allocation simply stops contaminating the comparison.

`h_spread` (spread monotonicity) existed only to prop up the transfer-ordered `T.map`. It is no longer needed and has been dropped from both `AllocHom` and `MechHom`, leaving **Alloc** as the plain pointwise order that Definition 1.5 intends.

## Boundary condition: equal rent, not zero rent

`masterTheorem_transferInvariance` requires `V₁(θ_min) = V₂(θ_min)` (`hV₀`), **not** `V(θ_min) = 0`. Revenue equivalence needs *equal* rent, never *zero* rent — `envelope_transfer_shift` (`m.t θ = t*(θ) − V_m(θ_min)`) makes this exact. This matches `mirrlees_unique_from_IC`, which already quantified over a common `V₀`; the abstract layer previously proved something narrower than its own instantiation.

Note also that transfer invariance uses **neither single crossing nor IR** — only IC's envelope condition. SC is needed to build `T` (functoriality) and for `IC_implies_monotone`; IR is needed to orient the adjunction. Neither is needed for revenue equivalence itself.

## File structure

| File | Contents |
|------|----------|
| `Framework.lean` | Categories Mech (surplus-ordered) and Alloc, `surplus`, functor Q, `IC_implies_monotone` |
| `MasterTheorem.lean` | `T`, `T_wellDefined`, `adj_T_Q`, `T_initial`, Master Theorem, `Mech₀`, `equivAllocMech₀` |
| `MyersonSetting.lean` | Myerson auction instantiation, Revenue Equivalence |
| `MirrleesSetting.lean` | Mirrlees taxation instantiation, Taxation Principle |
| `Corollaries.lean` | Corollaries 5.1 and 5.2 as instances of the Master Theorem |

## Proof status — branch `surplus-order`

Build: `lake build` — completes successfully. **Zero sorries.** All results depend only on the standard axioms `[propext, Classical.choice, Quot.sound]`.

### Key declarations

| Declaration | File | Notes |
|-------------|------|-------|
| `IC_implies_monotone` | Framework | MON from IC + SC via mimicry argument |
| `surplus` | Framework | `V(θ) = v(q θ, θ) − t θ`; the quasilinear coordinate |
| `mechCategory`, `allocCategory` | Framework | Thin categories; laws by `Subsingleton.elim` |
| `T_wellDefined` | MasterTheorem | FTC + SC + `integral_mono_on`; IC and IR for all `θ ≥ θ_min > 0` |
| `typeDeriv_mono_of_alloc_le` | MasterTheorem | The SC step, lifted out; the only ingredient `T.map` needs |
| `Tmech_surplus_mono` | MasterTheorem | **`T.map`** — from single crossing alone |
| `T_full`, `T_faithful` | MasterTheorem | `T` fully faithful; Alloc coreflective in Mech |
| `surplus_split` | MasterTheorem | Envelope theorem in surplus form; the fiber structure |
| `adj_T_Q` | MasterTheorem | `Adjunction.mkOfUnitCounit`; counit via `surplus_split` + IR |
| `T_initial` | MasterTheorem | `T(r)` initial in its fiber (replaces `T_terminal`) |
| `envelope_transfer_shift` | MasterTheorem | `m.t θ = t*(θ) − V_m(θ_min)`; no boundary condition |
| `transfer_eq_of_iso` | MasterTheorem | Iso in Mech ⟹ equal transfers (makes the category load-bearing) |
| `masterTheorem_transferInvariance` | MasterTheorem | Via the iso; relaxed `hV₀` (equal rent) |
| `Mech₀`, `equivAllocMech₀` | MasterTheorem | **Move 3**: `Alloc ≌ Mech₀`, the Taxation Principle |
| `revenueEquivalence` | Corollaries | Instance of the Master Theorem at `myersonValue` |
| `taxationPrinciple` | Corollaries | Instance of the Master Theorem at `mirrleesValue` |
| `myerson_expectedRevenue` | MyersonSetting | IBP via `integral_hasStrictDerivAt` |

### Honest notes for a referee

* **`adj_T_Q` has no consumer.** The adjunction is proved structure *about* the framework;
  the corollaries do not use it. What they *do* use is the isomorphism in **Mech**
  (`transfer_eq_of_iso`: an iso forces equal transfers), which is real categorical content.
  `transferInvariance_via_T` shows the route through `T` is available. We say this rather
  than contriving a dependency.
* **Move 3 is cheap.** `Alloc ≌ Mech₀` is an equivalence, and equivalences are always cheap.
  The content is in Moves 1 and 2 — that `T` exists at all (`T_wellDefined`), and that the
  counit is invertible *precisely* at zero rent.
* **`myersonTransfer ≠ transferFormula`.** They differ by the rent conceded below `θ_min`
  (`myerson_transferFormula_eq_myersonTransfer`); they coincide only at `θ_min = 0`, which
  the master theorem forbids.

### Open modelling question

`IsIR` asserts `V(θ_min) ≥ 0` while its docstring describes `V(θ_min) = 0`. The branch keeps the **inequality**, which is what makes Move 1 substantive (the fiber is a genuine one-parameter family) and Move 3 a real restriction rather than a definition. Tightening `IsIR` to an equality would collapse **Mech** onto **Mech₀** and make revenue equivalence true by construction of the objects — a cleaner headline, a weaker theorem.

## Key proof patterns

- **`HasDerivAt.sub`**: use the explicit form, not dot notation (dot resolves to `HasFDerivAtFilter.sub`)
- **`intervalIntegrable_const`**: root namespace, not `intervalIntegral.`
- **`integral_symm θ θ'`**: gives `∫ in θ'..θ = -∫ in θ..θ'`
- **Physical domain**: integrals run over `Set.Ici θ_min`; FTC is only needed for `θ ≥ θ_min > 0`
- **`hvθ`**: partial derivative `deriv (v (y θ)) θ`, not total `deriv (fun s => v (y s) s) θ`
- **Thin categories**: naturality, triangle identities and functor laws all discharge by `@Subsingleton.elim _ mechHom_subsingleton` / `allocHom_subsingleton`

## Build

```bash
cd /path/to/MechDesigAdjointfunctor.lean
lake build
```
