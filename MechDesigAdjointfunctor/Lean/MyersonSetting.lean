import MechDesigAdjointfunctor.Lean.Framework
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Stage 2: The Myerson Auction Setting

Instantiates the abstract framework of `Framework.lean` to Myerson's (1981)
single-object auction with one-dimensional types.

## Summary

* Allocation space `A = Set.Icc 0 1` — probability of receiving the object.
* Value function `v q θ = θ * q`.
* SC holds: `v q θ - v q' θ = θ * (q - q')` is strictly increasing in `θ` for `q > q'`.
* IC characterises payment uniquely via the envelope formula (Lemma 2.1):
  `t(θ) = θ * q(θ) - ∫₀^θ q(s) ds`.
* Revenue equivalence follows as a special case of the Master Theorem.

## References

* Myerson (1981), *Optimal Auction Design*, Theorem 2, Lemma 2
* Klemperer (1999), *Auction Theory: A Guide to the Literature*, Theorem 1
-/

open MeasureTheory intervalIntegral

namespace MechDesign.Myerson

/-! ### 2.1 The Myerson Environment -/

/-- The Myerson allocation space: probabilities of receiving the object. -/
abbrev MyersonAlloc := Set.Icc (0 : ℝ) 1

/-- The Myerson value function: `v(q, θ) = θ * q`.  Linear in both arguments. -/
noncomputable def myersonValue : MyersonAlloc → ℝ → ℝ :=
  fun q θ => θ * q.val

/-- **Condition REG** (Regularity, Myerson): the virtual valuation
`ψ(θ) = θ - (1 - F(θ)) / f(θ)` is non-decreasing.  Required for the optimal
allocation to be monotone without ironing. -/
def IsRegular (F f : ℝ → ℝ) (Θ : Set ℝ) : Prop :=
  ∀ θ ∈ Θ, 0 < f θ ∧ MonotoneOn (fun θ => θ - (1 - F θ) / f θ) Θ

/-! ### 2.2 Single Crossing in the Myerson Setting (Section 2.2) -/

/-- SC holds for the Myerson value function: `v q θ - v q' θ = θ * (q - q')`,
which is strictly increasing in `θ` whenever `q > q'`. -/
lemma myerson_singleCrossing : SingleCrossing myersonValue := by
  intro q q' hq θ θ' hθ
  simp only [myersonValue]
  have hqq : q'.val < q.val := hq
  nlinarith [hq, hθ]

/-! ### 2.3 Differentiability of the Myerson Value Function -/

/-- The Myerson value function `v(q, θ) = θ * q.val` is differentiable (in fact
polynomial) in the type argument `θ`, for any fixed allocation `q`. -/
lemma myerson_vDiff : ∀ (q : MyersonAlloc), DifferentiableOn ℝ (myersonValue q) (Set.Ioi 0) := by
  intro q
  unfold myersonValue
  fun_prop

/-! ### 2.4 IC Characterisation in the Myerson Setting (Lemma 2.1) -/

/-- The **Myerson envelope transfer formula**: the unique transfer rule that, paired
with a monotone allocation rule `q`, yields a BIC mechanism with `V(0) = 0`.

  `t*(θ) = θ * q(θ) - ∫₀^θ q(s) ds`

*Reference*: Myerson (1981), Theorem 2. -/
noncomputable def myersonTransfer (q : ℝ → ℝ) (θ : ℝ) : ℝ :=
  θ * q θ - ∫ s in (0 : ℝ)..θ, q s

/-- The equilibrium payoff under the Myerson transfer equals the information rent:
`V(θ) = ∫₀^θ q(s) ds`. -/
noncomputable def myersonRent (q : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..θ, q s

/-- **Lemma 2.1 (if direction)**: If `q` is monotone and `t = myersonTransfer q`, then
the mechanism `(q, t)` is BIC with `V(0) = 0`.

Proof sketch: for any misreport `r`, the payoff difference is
`V(θ) - U(θ, r) = ∫ᵣ^θ [q(θ) - q(s)] ds ≥ 0` since `q` is non-decreasing. -/
lemma myerson_IC_of_monotone_transfer (q : ℝ → ℝ) (hq : Monotone q)
    (hq_int : ∀ a b, IntervalIntegrable q MeasureTheory.volume a b) :
    IsIC myersonValue ⟨fun θ => ⟨q θ, sorry, sorry⟩, myersonTransfer q⟩ := by
  sorry

/-- **Lemma 2.1 (only-if direction)**: If `(q, t)` is BIC with `V(0) = 0`,
then `q` is monotone and `t = myersonTransfer q`.

Proof sketch: `V(θ) = max_r U(θ, r)` is convex (max of affine functions), so `q`
is non-decreasing.  The envelope theorem gives `V'(θ) = q(θ)` a.e.; integrating
with `V(0) = 0` and substituting yields the formula. -/
lemma myerson_transfer_unique {q : ℝ → ℝ} {t : ℝ → ℝ}
    (hIC : IsIC myersonValue ⟨fun θ => ⟨q θ, sorry, sorry⟩, t⟩)
    (hIR : t 0 ≤ 0 * q 0) :
    ∀ θ, t θ = myersonTransfer q θ := by
  sorry

/-- **Expected revenue formula**: for any BIC-IR mechanism with allocation `q` and
`V(0) = 0`, the expected payment equals the expected virtual surplus.

  `𝔼[t(θ)] = 𝔼[ψ(θ) * q(θ)]`  where `ψ(θ) = θ - (1-F(θ))/f(θ)`.

Derived from the Myerson transfer formula by integration by parts.
*Reference*: Myerson (1981), Equation (5); Riley–Samuelson (1981). -/
theorem myerson_expectedRevenue (q : ℝ → ℝ) (F f : ℝ → ℝ)
    (hf : ∀ θ, 0 < f θ)
    (hq_int : ∀ a b, IntervalIntegrable q MeasureTheory.volume a b) :
    ∫ θ in (0 : ℝ)..1, myersonTransfer q θ * f θ =
    ∫ θ in (0 : ℝ)..1, (θ - (1 - F θ) / f θ) * q θ * f θ := by
  sorry

end MechDesign.Myerson
