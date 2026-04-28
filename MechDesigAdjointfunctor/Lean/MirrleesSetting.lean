import MechDesigAdjointfunctor.Lean.Framework
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Stage 3: The Mirrlees Taxation Setting

Instantiates the abstract framework of `Framework.lean` to Mirrlees's (1971)
optimal nonlinear income taxation model, recovering the **Taxation Principle**
(Hammond 1979; Rochet 1985).

## Summary

* Allocation space `A = ℝ≥0` — gross income `y`.
* Value function: quasilinear approximation `v(y, θ) = θ * h(y) - g(y/θ)` where
  `h` is the value of income and `g` is the disutility of effort.
* SC-M (Spence-Mirrlees condition): MRS between income and consumption decreasing in `θ`.
* IC characterises the net-income schedule via the envelope formula (Lemma 3.1):
  `V(θ) = V(θ_min) + ∫_{θ_min}^θ ∂v/∂s (y(s), s) ds`.
* The **Taxation Principle**: any IC mechanism can be implemented by a unique
  nonlinear tax schedule `T(y) = y - c(y)`.

## References

* Mirrlees (1971), *Optimal Income Taxation*, Sections 2–6, Eqs. (26)–(27)
* Hammond (1979), *Straightforward Individual Incentive Compatibility*, Theorem 1
* Rochet (1985), *The Taxation Principle and Multi-Time HJE*, Proposition 1
* Seade (1977), *On the Shape of Optimal Tax Schedules*
-/

open MeasureTheory intervalIntegral

namespace MechDesign.Mirrlees

/-! ### 3.1 The Mirrlees Environment -/

/-- The value function for the Mirrlees model, as a quasilinear approximation.
`v(y, θ) = θ * h y - g (y / θ)` where `h : ℝ → ℝ` values income and
`g : ℝ → ℝ` is the disutility of labour effort `l = y / θ`. -/
noncomputable def mirrleesValue (h g : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun y θ => θ * h y - g (y / θ)

/-- **Condition SC-M** (Spence-Mirrlees Single Crossing): the marginal rate of
substitution `MRS(y, c, θ) = -∂U/∂y / ∂U/∂c` is strictly decreasing in `θ`.
Equivalently, higher-productivity types have flatter indifference curves in `(y, c)` space.
Formalised here as: `∂/∂θ [v(y, θ) - v(y', θ)] > 0` for all `y > y'`, which is the
abstract SC condition applied to the income-consumption allocation space.
*Reference*: Mirrlees (1971) Assumption 3; Seade (1977). -/
def SpenceMirrlees (v : ℝ → ℝ → ℝ) : Prop :=
  SingleCrossing (A := ℝ) v

/-- SC-M implies the abstract SC condition for the income-consumption allocation space.

The Spence-Mirrlees condition `SpenceMirrlees v = SingleCrossing v` (by definition),
so this lemma establishes SC from differentiability assumptions on `h` and `g`.
*Reference*: Mirrlees (1971), Lemma 1; Fudenberg–Tirole (1991), Ch. 7. -/
lemma mirrlees_singleCrossing (h g : ℝ → ℝ) (hh : Differentiable ℝ h)
    (hg : Differentiable ℝ g) (hg_pos : ∀ l, 0 < deriv g l) :
    SingleCrossing (A := ℝ) (mirrleesValue h g) := by
  sorry

/-! ### 3.2 IC Characterisation and the Taxation Principle (Lemma 3.1) -/

/-- The **Mirrlees envelope transfer formula**: the unique consumption rule `c(θ)` that,
paired with a monotone income assignment `y(θ)`, yields an IC mechanism with
`V(θ_min) = V₀`.

  `V(θ) = V₀ + ∫_{θ_min}^θ (∂v/∂s)(y(s), s) ds`
  `c(θ) = v(y(θ), θ) - V(θ)` -/
noncomputable def mirrleesRent (vθ_partial : ℝ → ℝ) (V₀ θ_min θ : ℝ) : ℝ :=
  V₀ + ∫ s in θ_min..θ, vθ_partial s

/-- The tax schedule induced by income assignment `y(θ)` and consumption `c(θ)`:
`T(y) = y - c` on the range of `y`. -/
noncomputable def taxSchedule (y c : ℝ → ℝ) (θ : ℝ) : ℝ := y θ - c θ

/-- **Lemma 3.1 (Taxation Principle — if direction)**: if `y(θ)` is monotone and `V`
satisfies the envelope formula, then the mechanism `(y, c)` is IC.

Proof sketch: for a misreport `r`, the payoff difference is
`V(θ) - U(θ,r) = ∫ᵣ^θ [∂v/∂s(y(s),s) - ∂v/∂s(y(r),s)] ds ≥ 0`
by SC-M and monotonicity of `y`. -/
lemma mirrlees_IC_of_envelope (v : ℝ → ℝ → ℝ) (vθ_partial : ℝ → ℝ) (V₀ θ_min : ℝ)
    (y : ℝ → ℝ) (hySC : SingleCrossing v)
    (hy_mono : Monotone y)
    (hvθ : ∀ θ, vθ_partial θ = deriv (fun s => v (y s) s) θ)
    (hint : ∀ a b, IntervalIntegrable vθ_partial MeasureTheory.volume a b) :
    IsIC v ⟨y, fun θ => v (y θ) θ - mirrleesRent vθ_partial V₀ θ_min θ⟩ := by
  sorry

/-- **Lemma 3.1 (Taxation Principle — only-if direction)**: if `(y(θ), c(θ))` is IC
with `V(θ_min) = V₀`, then `y` is monotone and the rent `V(θ)` satisfies the envelope
formula.  Moreover, the tax schedule `T(y) = y - c(y)` is uniquely determined by
`y(θ)` and `V₀`.

Proof sketch: `V(θ) = max_r U(θ,r)` is convex (max of functions with the Spence-Mirrlees
property), so `y` is non-decreasing (MON).  The envelope theorem gives
`V'(θ) = (∂v/∂θ)(y(θ), θ)` a.e.; integrating from `θ_min` yields the formula.
*Reference*: Mirrlees (1971), Eqs. (26)–(27); Hammond (1979), Thm. 1; Rochet (1985), Prop. 1. -/
lemma mirrlees_unique_from_IC (v : ℝ → ℝ → ℝ) (vθ_partial : ℝ → ℝ)
    (V₀ θ_min : ℝ) (y t : ℝ → ℝ)
    (hIC : IsIC v ⟨y, t⟩)
    (hIR : v (y θ_min) θ_min - t θ_min = V₀) :
    Monotone y ∧ ∀ θ, t θ = v (y θ) θ - mirrleesRent vθ_partial V₀ θ_min θ := by
  sorry

/-- **Remark (Taxation Principle)**: any IC direct mechanism `(y(θ), c(θ))` can be
implemented by a unique nonlinear tax schedule `T : Y → ℝ` defined by `T(y) = y - c`
on the range of `y`.  Two IC mechanisms with the same `y(θ)` and the same `V(θ_min)`
produce identical tax schedules.
*Reference*: Hammond (1979); Rochet (1985). -/
theorem taxation_principle (v : ℝ → ℝ → ℝ) (vθ_partial : ℝ → ℝ)
    (V₀ θ_min : ℝ) (y₁ y₂ t₁ t₂ : ℝ → ℝ)
    (hIC₁ : IsIC v ⟨y₁, t₁⟩) (hIR₁ : v (y₁ θ_min) θ_min - t₁ θ_min = V₀)
    (hIC₂ : IsIC v ⟨y₂, t₂⟩) (hIR₂ : v (y₂ θ_min) θ_min - t₂ θ_min = V₀)
    (hy_eq : y₁ = y₂) :
    t₁ = t₂ := by
  sorry

end MechDesign.Mirrlees
