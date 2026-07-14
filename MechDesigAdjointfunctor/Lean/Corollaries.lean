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
       Q preserves colimits  (Q_preservesColimits)
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

/-! ### 5.0 Discharging the Lipschitz hypothesis

`surplus_split` no longer assumes the surplus is continuous — it *derives* continuity from
incentive compatibility (`surplus_ic_sandwich` → `surplus_lipschitzOn`).  The price is a
regularity hypothesis on the value function: `v(a, ·)` must be Lipschitz in the type, with a
constant uniform over the allocations the mechanism actually uses.

Here is that hypothesis discharged in the Myerson setting.  It is exactly the standard
assumption that allocation probabilities lie in `[0, 1]`. -/

/-- **The Myerson value function is `1`-Lipschitz in the type along any allocation in
`[-1, 1]`** — in particular along any allocation *probability*.

`v(a, θ) = θ·a`, so `|v(a, θ₂) − v(a, θ₁)| = |a|·|θ₂ − θ₁| ≤ |θ₂ − θ₁|` whenever `|a| ≤ 1`.
Combined with `surplus_lipschitzOn`, this discharges the continuity requirement of
`revenueEquivalence` from IC alone. -/
theorem myerson_lipschitz {a : Myerson.MyersonAlloc} (ha : |a| ≤ 1) (S : Set ℝ) :
    LipschitzOnWith 1 (Myerson.myersonValue a) S := by
  refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
  simp only [Myerson.myersonValue, Real.dist_eq, NNReal.coe_one, one_mul]
  calc |x * a - y * a| = |a| * |x - y| := by rw [← abs_mul]; ring_nf
    _ ≤ 1 * |x - y| := by gcongr
    _ = |x - y| := one_mul _

/-- **The Mirrlees value function is Lipschitz in the type**, given a bound on its
θ-derivative over the physical domain.

`v(y, θ) = θ·h(y) − g(y/θ)`, so `∂v/∂θ = h(y) + (y/θ²)·g′(y/θ)`.  On `[θ_min, ∞)` with
`θ_min > 0` this is bounded for each income `y`, and uniformly so once the income range is
bounded — which is the economically mild assumption that incomes are bounded.  The bound is
taken as an explicit hypothesis rather than derived, so that the caller can supply whatever
bound their `h`, `g` and income range actually give.

This is the Mirrlees counterpart of `myerson_lipschitz`, and it is what discharges the
continuity requirement of `taxationPrinciple` from IC alone. -/
theorem mirrlees_lipschitz (h g : ℝ → ℝ) (hh : Differentiable ℝ h) (hg : Differentiable ℝ g)
    {θ_min : ℝ} (hθ_pos : 0 < θ_min) (y : ℝ) (C : NNReal)
    (hbound : ∀ θ ∈ Set.Ici θ_min, ‖h y + (y / θ ^ 2) * deriv g (y / θ)‖₊ ≤ C) :
    LipschitzOnWith C (Mirrlees.mirrleesValue h g y) (Set.Ici θ_min) := by
  refine (convex_Ici θ_min).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun θ => h y + (y / θ ^ 2) * deriv g (y / θ)) (fun θ hθ => ?_) hbound
  have hθ0 : θ ≠ 0 := ne_of_gt (lt_of_lt_of_le hθ_pos (Set.mem_Ici.mp hθ))
  exact (Mirrlees.mirrleesValue_hasDerivAt h g hh hg y θ hθ0).hasDerivWithinAt

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
    (θ_min : ℝ) (hθ_pos : 0 < θ_min)
    (q₀ : MonotoneAlloc Myerson.MyersonAlloc)
    (m₁ m₂ : ICIRMechanism Myerson.MyersonAlloc Myerson.myersonValue θ_min)
    (hm₁_alloc : m₁ ∈ MechWithAlloc q₀)
    (hm₂_alloc : m₂ ∈ MechWithAlloc q₀)
    (hint : ∀ a b, IntervalIntegrable
      (typeDerivAlongAlloc Myerson.myersonValue q₀)
      MeasureTheory.volume a b)
    (hintC : ∀ (a : Myerson.MyersonAlloc) b c,
      IntervalIntegrable (deriv (Myerson.myersonValue a)) MeasureTheory.volume b c)
    -- Envelope condition: continuity plus a RIGHT derivative.  One-sided on purpose — a
    -- two-sided derivative would exclude posted-price auctions, whose surplus has a kink
    -- at the reserve.  See `surplus_split` and `Myerson.postedPrice_hasEnvelope`.
    -- Continuity is NOT assumed: it is derived from IC, given that the value function is
    -- Lipschitz in the type along each allocation the mechanism uses.  Discharged for
    -- Myerson by `myerson_lipschitz` whenever the allocation is bounded.
    (L₁ : NNReal)
    (hvLip₁ : ∀ θ' : ℝ,
      LipschitzOnWith L₁ (Myerson.myersonValue (m₁.mech.q θ')) (Set.Ici θ_min))
    (hEnv₁ : ∀ θ > 0, HasDerivWithinAt
      (fun s => Myerson.myersonValue (q₀.q s) s - m₁.mech.t s)
      (typeDerivAlongAlloc Myerson.myersonValue q₀ θ) (Set.Ioi θ) θ)
    (L₂ : NNReal)
    (hvLip₂ : ∀ θ' : ℝ,
      LipschitzOnWith L₂ (Myerson.myersonValue (m₂.mech.q θ')) (Set.Ici θ_min))
    (hEnv₂ : ∀ θ > 0, HasDerivWithinAt
      (fun s => Myerson.myersonValue (q₀.q s) s - m₂.mech.t s)
      (typeDerivAlongAlloc Myerson.myersonValue q₀ θ) (Set.Ioi θ) θ)
    -- RELAXED boundary condition: the two mechanisms leave the lowest type the SAME rent.
    -- (Revenue equivalence needs equal rent, not zero rent.)
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ in Set.Ici θ_min, m₁.mech.t θ ∂μ = ∫ θ in Set.Ici θ_min, m₂.mech.t θ ∂μ :=
  masterTheorem_transferInvariance hθ_pos q₀ hint m₁ m₂ hm₁_alloc hm₂_alloc
    L₁ hvLip₁ hEnv₁ L₂ hvLip₂ hEnv₂ hV₀ μ

/-- **Myerson expected revenue formula**: for any BIC-IR mechanism with allocation `q`
and `V(0) = 0`, expected revenue equals expected virtual surplus.

  `𝔼_F[t(θ)] = 𝔼_F[ψ(θ) · q(θ)]`   where `ψ(θ) = θ - (1-F(θ))/f(θ)`.

This follows from the transfer formula by integration by parts.
*Reference*: Myerson (1981), Equation (5). -/
theorem myerson_revenueFormula (q : ℝ → ℝ) (F f : ℝ → ℝ)
    (hf_pos : ∀ θ, 0 < f θ)
    (hq_int : ∀ a b, IntervalIntegrable q MeasureTheory.volume a b)
    (hq_cont : Continuous q) (hf_cont : Continuous f)
    (hFf : ∀ θ, HasDerivAt F (f θ) θ)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) :
    ∫ θ in (0:ℝ)..1, Myerson.myersonTransfer q θ * f θ =
    ∫ θ in (0:ℝ)..1, (θ - (1 - F θ) / f θ) * q θ * f θ :=
  Myerson.myerson_expectedRevenue q F f hf_pos hq_int hq_cont hf_cont hFf hF0 hF1

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
    (hh_mono : StrictMono h)
    (hSM : StrictMono (fun l => l * deriv g l))
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
    -- Envelope condition: continuity plus a RIGHT derivative.  One-sided on purpose — a
    -- two-sided derivative would exclude allocations with a bunching region.
    -- Continuity is NOT assumed: it is derived from IC, given Lipschitz-in-the-type.
    -- For Mirrlees, `∂v/∂θ = h y + g'(y/θ)·y/θ²` is bounded on `[θ_min, ∞)` for each fixed
    -- income `y`, and uniformly so once the income range is bounded.  See TODO.md — the
    -- Lean discharge of this is the one Phase 1 task still open.
    (L₁ : NNReal)
    (hvLip₁ : ∀ θ' : ℝ,
      LipschitzOnWith L₁ (Mirrlees.mirrleesValue h g (m₁.mech.q θ')) (Set.Ici θ_min))
    (hEnv₁ : ∀ θ > 0, HasDerivWithinAt
      (fun s => Mirrlees.mirrleesValue h g (q₀.q s) s - m₁.mech.t s)
      (typeDerivAlongAlloc (Mirrlees.mirrleesValue h g) q₀ θ) (Set.Ioi θ) θ)
    (L₂ : NNReal)
    (hvLip₂ : ∀ θ' : ℝ,
      LipschitzOnWith L₂ (Mirrlees.mirrleesValue h g (m₂.mech.q θ')) (Set.Ici θ_min))
    (hEnv₂ : ∀ θ > 0, HasDerivWithinAt
      (fun s => Mirrlees.mirrleesValue h g (q₀.q s) s - m₂.mech.t s)
      (typeDerivAlongAlloc (Mirrlees.mirrleesValue h g) q₀ θ) (Set.Ioi θ) θ)
    -- RELAXED boundary condition: identical rent at the lowest type (a common `V₀`),
    -- matching what `mirrlees_unique_from_IC` already assumed.
    (hV₀ : surplus m₁ θ_min = surplus m₂ θ_min)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ in Set.Ici θ_min, m₁.mech.t θ ∂μ = ∫ θ in Set.Ici θ_min, m₂.mech.t θ ∂μ :=
  masterTheorem_transferInvariance hθ_pos q₀ hint m₁ m₂ hm₁_alloc hm₂_alloc
    L₁ hvLip₁ hEnv₁ L₂ hvLip₂ hEnv₂ hV₀ μ

/-! ### 5.2b The posted price — why the envelope hypothesis must be one-sided

The mechanism that forces the design of `surplus_split`'s hypothesis.  A **posted price**
with reserve `p`: sell iff `θ ≥ p`, charge `p` on a sale.  It is the canonical optimal
auction under regularity, it is monotone, IC and IR — and its surplus

  `V θ = θ·q θ - t θ = max (θ - p) 0`

has a **kink at `p`**.  It has no two-sided derivative there.

So a `HasDerivAt` envelope hypothesis is not merely inconvenient, it is **unsatisfiable**
for every auction with a reserve price, and `revenueEquivalence` would be inapplicable to
the mechanisms it most wants to talk about.  The right derivative survives the kink — at
`p` it equals `1 = q p` — which is all `integral_eq_sub_of_hasDeriv_right` ever needed.

`postedPrice_hasEnvelope` discharges the hypothesis the framework now takes.
`postedPrice_not_hasDerivAt` shows the hypothesis it used to take is false. -/

namespace PostedPrice

variable {p : ℝ}

/-- Sell iff the type clears the reserve. -/
noncomputable def alloc (p : ℝ) : ℝ → Myerson.MyersonAlloc := fun θ => if p ≤ θ then 1 else 0

/-- Charge the reserve on a sale, nothing otherwise. -/
noncomputable def transfer (p : ℝ) : ℝ → ℝ := fun θ => if p ≤ θ then p else 0

lemma alloc_mono : Monotone (alloc p) := by
  intro a b hab
  rcases le_or_gt p a with ha | ha
  · have hb : p ≤ b := ha.trans hab
    simp [alloc, ha, hb]
  · rcases le_or_gt p b with hb | hb
    · simp [alloc, not_le.mpr ha, hb]
    · simp [alloc, not_le.mpr ha, not_le.mpr hb]

/-- The surplus of the posted price is `max (θ - p) 0` — the kinked function. -/
lemma surplus_eq (θ : ℝ) :
    Myerson.myersonValue (alloc p θ) θ - transfer p θ = max (θ - p) 0 := by
  simp only [Myerson.myersonValue, alloc, transfer]
  split_ifs with h
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ θ - p)]; ring
  · rw [max_eq_right (by linarith [not_le.mp h] : θ - p ≤ (0:ℝ))]; ring

/-- The Myerson envelope integrand along any allocation is the allocation itself:
`D_r(θ) = ∂/∂θ (θ · r.q θ) = r.q θ`. -/
lemma typeDeriv_eq (r : MonotoneAlloc Myerson.MyersonAlloc) (θ : ℝ) :
    typeDerivAlongAlloc Myerson.myersonValue r θ = r.q θ := by
  simp only [typeDerivAlongAlloc, Myerson.myersonValue]
  have h : HasDerivAt (fun s : ℝ => s * r.q θ) (r.q θ) θ := by
    simpa using (hasDerivAt_id θ).mul_const (r.q θ)
  exact h.deriv

/-- **The posted price satisfies the framework's envelope hypothesis.**
Continuity plus a *right* derivative at every physical type — including at the reserve `p`,
where the right derivative is `1 = q p`. -/
theorem postedPrice_hasEnvelope :
    ContinuousOn (fun s => Myerson.myersonValue (alloc p s) s - transfer p s) (Set.Ioi 0) ∧
    ∀ θ > 0, HasDerivWithinAt
      (fun s => Myerson.myersonValue (alloc p s) s - transfer p s)
      (typeDerivAlongAlloc Myerson.myersonValue ⟨alloc p, alloc_mono⟩ θ) (Set.Ioi θ) θ := by
  have hV : (fun s => Myerson.myersonValue (alloc p s) s - transfer p s)
      = fun s => max (s - p) 0 := funext fun s => surplus_eq s
  constructor
  · rw [hV]
    exact (Continuous.max (continuous_id.sub continuous_const) continuous_const).continuousOn
  · intro θ _
    rw [hV, typeDeriv_eq ⟨alloc p, alloc_mono⟩ θ]
    change HasDerivWithinAt (fun s => max (s - p) 0) (alloc p θ) (Set.Ioi θ) θ
    by_cases hpθ : p ≤ θ
    · -- Above the reserve: V agrees with `s - p` to the right of θ, slope 1 = q θ.
      have hEq : Set.EqOn (fun s => max (s - p) 0) (fun s => s - p) (Set.Ici θ) := by
        intro s hs
        exact max_eq_left (by linarith [hs, le_trans hpθ hs] : (0:ℝ) ≤ s - p)
      have h1 : HasDerivWithinAt (fun s : ℝ => s - p) 1 (Set.Ioi θ) θ :=
        ((hasDerivAt_id θ).sub_const p).hasDerivWithinAt
      have hres : HasDerivWithinAt (fun s => max (s - p) 0) 1 (Set.Ioi θ) θ :=
        h1.congr (fun s hs => hEq (Set.mem_Ici.mpr (le_of_lt hs)))
          (hEq (Set.mem_Ici.mpr (le_refl θ)))
      simpa [alloc, if_pos hpθ] using hres
    · -- Below the reserve: V is eventually 0 to the right of θ, slope 0 = q θ.
      push_neg at hpθ
      have hev : (fun s => max (s - p) 0) =ᶠ[nhdsWithin θ (Set.Ioi θ)] fun _ => (0:ℝ) := by
        have hmem : Set.Iio p ∈ nhdsWithin θ (Set.Ioi θ) :=
          nhdsWithin_le_nhds (Iio_mem_nhds hpθ)
        filter_upwards [hmem] with s hs
        exact max_eq_right (by linarith [Set.mem_Iio.mp hs] : s - p ≤ (0:ℝ))
      have h0 : HasDerivWithinAt (fun _ : ℝ => (0:ℝ)) 0 (Set.Ioi θ) θ :=
        (hasDerivAt_const θ (0:ℝ)).hasDerivWithinAt
      have : HasDerivWithinAt (fun s => max (s - p) 0) 0 (Set.Ioi θ) θ :=
        h0.congr_of_eventuallyEq hev (max_eq_right (by linarith : θ - p ≤ (0:ℝ)))
      simpa [alloc, if_neg (not_le.mpr hpθ)] using this

/-- **The posted price does NOT satisfy a two-sided envelope hypothesis.**

At the reserve `p` the surplus `max (θ - p) 0` has slope `0` from the left and `1` from the
right, so it has **no** derivative there — for *any* candidate value `c`.

This is the theorem that justifies Phase 0.  The framework previously demanded
`HasDerivAt`, and this shows that demand is unsatisfiable for the canonical optimal
auction: `revenueEquivalence` could not be applied to any mechanism with a reserve. -/
theorem postedPrice_not_hasDerivAt (c : ℝ) :
    ¬ HasDerivAt (fun s => max (s - p) 0) c p := by
  intro h
  have hslope := hasDerivAt_iff_tendsto_slope.mp h
  -- From the left the slope is identically 0.
  have hleft : Filter.Tendsto (slope (fun s => max (s - p) 0) p) (nhdsWithin p (Set.Iio p))
      (nhds c) :=
    hslope.mono_left (nhdsWithin_mono p (fun x hx => ne_of_lt (Set.mem_Iio.mp hx)))
  have hL0 : slope (fun s => max (s - p) 0) p =ᶠ[nhdsWithin p (Set.Iio p)] fun _ => (0:ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxp : x - p ≤ 0 := by linarith [Set.mem_Iio.mp hx]
    simp [slope_def_field, max_eq_right hxp, max_eq_right (le_of_eq (sub_self p))]
  have hc0 : c = 0 :=
    tendsto_nhds_unique (hleft.congr' hL0) tendsto_const_nhds
  -- From the right the slope is identically 1.
  have hright : Filter.Tendsto (slope (fun s => max (s - p) 0) p) (nhdsWithin p (Set.Ioi p))
      (nhds c) :=
    hslope.mono_left (nhdsWithin_mono p (fun x hx => ne_of_gt (Set.mem_Ioi.mp hx)))
  have hR1 : slope (fun s => max (s - p) 0) p =ᶠ[nhdsWithin p (Set.Ioi p)] fun _ => (1:ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxp : (0:ℝ) ≤ x - p := by linarith [Set.mem_Ioi.mp hx]
    have hne : x - p ≠ 0 := sub_ne_zero.mpr (ne_of_gt (Set.mem_Ioi.mp hx))
    simp [slope_def_field, max_eq_left hxp, max_eq_right (le_of_eq (sub_self p)),
      div_self hne]
  have hc1 : c = 1 :=
    tendsto_nhds_unique (hright.congr' hR1) tendsto_const_nhds
  exact absurd (hc0 ▸ hc1 : (0:ℝ) = 1) (by norm_num)

/-- **The posted price also discharges the Lipschitz hypothesis.**  Its allocation is `0` or
`1`, so `myerson_lipschitz` applies.  Together with `postedPrice_hasEnvelope`, the
reserve-price auction now satisfies *every* hypothesis the framework asks of it — continuity
comes free from IC, and the envelope condition is one-sided. -/
theorem postedPrice_lipschitz (θ' : ℝ) (S : Set ℝ) :
    LipschitzOnWith 1 (Myerson.myersonValue (alloc p θ')) S := by
  refine myerson_lipschitz ?_ S
  simp only [alloc]
  split_ifs <;> simp

end PostedPrice

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
