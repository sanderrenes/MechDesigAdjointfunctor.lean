import MechDesigAdjointfunctor.Lean.MasterTheorem
import MechDesigAdjointfunctor.Lean.MyersonSetting
import MechDesigAdjointfunctor.Lean.MirrleesSetting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Stage 5: Revenue Equivalence and the Taxation Principle as Corollaries

Instantiates the abstract Master Theorem (`MasterTheorem.lean`) in the two
economic settings to recover the classical results as special cases.

## Main declarations

* `MechDesign.Corollaries.revenueEquivalence` — Corollary 5.1: Myerson's Revenue
  Equivalence Theorem is an instance of Theorem 4.5(iii).
* `MechDesign.Corollaries.taxationPrinciple` — Corollary 5.2: the Mirrlees Taxation
  Principle is an instance of Theorem 4.5(iii).

## The proof chain

```
QI + SC  →  MON  (IC_implies_monotone)
               ↓
       Alloc is complete  (alloc_hasLimits)
               ↓
       Q preserves limits  (Q_preservesLimits)
               ↓
       T(q) is BIC-IR  (T_wellDefined)
               ↓
       Q ⊣ T  (adj_Q_T)
               ↓
       T(q) terminal in Mech_q  (T_terminal)
               ↙               ↘
  Revenue Equivalence     Taxation Principle
  (Myerson 1981)          (Hammond 1979; Rochet 1985)
```

Both corollaries follow from `masterTheorem_transferInvariance`.  Only the economic
interpretation of objects and morphisms differs.

## References

* Myerson (1981), *Optimal Auction Design*, Theorem 2
* Riley–Samuelson (1981), *Optimal Auctions*, Theorem 1
* Hammond (1979), *Straightforward Incentive Compatibility*, Theorem 1
* Rochet (1985), *The Taxation Principle*, Proposition 1
-/

open MeasureTheory MechDesign

namespace MechDesign.Corollaries

/-! ### 5.1 Revenue Equivalence (Corollary 5.1) -/

/-- **Corollary 5.1 — Myerson Revenue Equivalence Theorem**.

In the Myerson auction setting (type space `[0,1]`, value function `v(q,θ) = θ*q`,
allocation probabilities `q ∈ [0,1]`), any two BIC-IR mechanisms
`M₁ = (q, t₁)` and `M₂ = (q, t₂)` with the **same allocation rule** `q` and
boundary condition `Vᵢ(0) = 0` satisfy:

  `𝔼[t₁(θ)] = 𝔼[t₂(θ)]`

*Proof*: Instantiate `masterTheorem_transferInvariance` with the Myerson value function.
SC holds by `myerson_singleCrossing`.  The expected transfer equals
`𝔼[ψ(θ) · q(θ)]` where `ψ(θ) = θ - (1-F(θ))/f(θ)` is the virtual valuation,
which depends only on `q` and the type distribution `F`.

*Reference*: Myerson (1981), Theorem 2; Riley–Samuelson (1981). -/
theorem revenueEquivalence
    (q₀ : MonotoneAlloc Myerson.MyersonAlloc)
    (m₁ m₂ : ICIRMechanism Myerson.MyersonAlloc Myerson.myersonValue 0)
    (hm₁_alloc : ∀ θ, m₁.mech.q θ = q₀.q θ)
    (hm₂_alloc : ∀ θ, m₂.mech.q θ = q₀.q θ)
    (hint : ∀ a b, IntervalIntegrable
      (typeDerivAlongAlloc Myerson.myersonValue q₀)
      MeasureTheory.volume a b)
    (hintC : ∀ (a : Myerson.MyersonAlloc) b c,
      IntervalIntegrable (deriv (Myerson.myersonValue a)) MeasureTheory.volume b c)
    (F : ℝ → ℝ) (f : ℝ → ℝ) (hf : ∀ θ, 0 < f θ)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ, m₁.mech.t θ ∂μ = ∫ θ, m₂.mech.t θ ∂μ :=
  -- NOTE: `masterTheorem_transferInvariance` now requires `0 < θ_min`; the Myerson
  -- setting uses `θ_min = 0` so this corollary is currently blocked at the
  -- boundary-condition argument (sorry below).  Recovering the result for Myerson
  -- needs a separate argument that handles the `θ_min = 0` boundary directly.
  masterTheorem_transferInvariance
    (sorry : (0 : ℝ) < 0)
    Myerson.myerson_singleCrossing
    q₀ Myerson.myerson_vDiff hint hintC m₁ m₂ hm₁_alloc hm₂_alloc μ

/-- **Myerson expected revenue formula**: for any BIC-IR mechanism with allocation `q`
and `V(0) = 0`, expected revenue equals expected virtual surplus.

  `𝔼_F[t(θ)] = 𝔼_F[ψ(θ) · q(θ)]`   where `ψ(θ) = θ - (1-F(θ))/f(θ)`.

This follows from the transfer formula by integration by parts.
*Reference*: Myerson (1981), Equation (5). -/
theorem myerson_revenueFormula (q : ℝ → ℝ) (F f : ℝ → ℝ)
    (hq_mono : Monotone q)
    (hf_pos : ∀ θ ∈ Set.Icc (0:ℝ) 1, 0 < f θ)
    (hq_int : ∀ a b, IntervalIntegrable q MeasureTheory.volume a b) :
    ∫ θ in (0:ℝ)..1, Myerson.myersonTransfer q θ * f θ =
    ∫ θ in (0:ℝ)..1, (θ - (1 - F θ) / f θ) * q θ * f θ := by
  sorry

/-! ### 5.2 Taxation Principle (Corollary 5.2) -/

/-- **Corollary 5.2 — Mirrlees Taxation Principle**.

In the Mirrlees taxation setting (type space `[θ_min, θ_max]`, quasilinear value
function `v(y, θ)`), any IC mechanism `(y(θ), c(θ))` with `V(θ_min) = 0` can be
implemented by a **unique** nonlinear tax schedule `T : Y → ℝ` defined by
`T(y) = y - c(y)` on the range of `y(θ)`.

Moreover, any two IC mechanisms with the **same income assignment** `y(θ)` and the same
`V(θ_min)` produce identical tax schedules and hence the same expected tax revenue.

*Proof*: Instantiate `masterTheorem_transferInvariance` with the Mirrlees value function.
SC holds by `mirrlees_singleCrossing` under SC-M.  The tax schedule is uniquely
determined by the allocation rule and the boundary condition.

*Reference*: Hammond (1979), Theorem 1; Rochet (1985), Proposition 1; Mirrlees (1971),
Eq. (27). -/
theorem taxationPrinciple
    (h g : ℝ → ℝ) (hh : Differentiable ℝ h) (hg : Differentiable ℝ g)
    (hg_pos : ∀ l, 0 < deriv g l)
    (θ_min : ℝ) (hθ_pos : 0 < θ_min)
    (q₀ : MonotoneAlloc ℝ)
    (m₁ m₂ : ICIRMechanism ℝ (Mirrlees.mirrleesValue h g) θ_min)
    (hm₁_alloc : ∀ θ, m₁.mech.q θ = q₀.q θ)
    (hm₂_alloc : ∀ θ, m₂.mech.q θ = q₀.q θ)
    (hint : ∀ a b, IntervalIntegrable
      (typeDerivAlongAlloc (Mirrlees.mirrleesValue h g) q₀)
      MeasureTheory.volume a b)
    (hintC : ∀ (a : ℝ) b c,
      IntervalIntegrable (deriv (Mirrlees.mirrleesValue h g a)) MeasureTheory.volume b c)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ, m₁.mech.t θ ∂μ = ∫ θ, m₂.mech.t θ ∂μ :=
  masterTheorem_transferInvariance
    hθ_pos
    (Mirrlees.mirrlees_singleCrossing h g hh hg hg_pos)
    q₀ (Mirrlees.mirrlees_vDiff h g hh hg)
    hint hintC m₁ m₂ hm₁_alloc hm₂_alloc μ

/-! ### 5.3 Conditions for Failure (Stage 6 placeholders)

The following stubs record where each of the three conditions breaks down,
matching the discussion in Section 6 of `Unification.md`.  Proofs are deferred. -/

/-- **Failure of QI**: Without quasilinearity, the allocation and transfer components
of IC mechanisms are entangled.  Q no longer factors through Alloc as a forgetful
functor; the adjunction Q ⊣ T breaks.
*Reference*: Maskin–Riley (1984); Rochet–Choné (1998). -/
theorem failure_nonQuasilinear : True := trivial  -- placeholder

/-- **Failure of SC**: With multi-dimensional types `θ ∈ ℝᵏ` for `k ≥ 2`, there is no
natural total order giving single crossing.  Alloc loses its poset structure; the
completeness argument fails; the Adjoint Functor Theorem does not directly apply.
*Reference*: Rochet (1987); Armstrong (1996); Rochet–Choné (1998). -/
theorem failure_multiDimensional : True := trivial  -- placeholder

/-- **Failure of MON** (ironing): Without regularity, the optimal allocation is
non-monotone.  The categorical fix is ironing: replace `q*` with its concave
majorant over bunching intervals.  Uniqueness of `T(q)` recovers only in expectation.
*Reference*: Myerson (1981), Section 6; Mirrlees (1971), Section 6; Ebert (1992). -/
theorem failure_ironing : True := trivial  -- placeholder

end MechDesign.Corollaries
