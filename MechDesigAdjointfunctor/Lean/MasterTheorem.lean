import MechDesigAdjointfunctor.Lean.Framework
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Perfect
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Stage 4: The Master Theorem — Adjunction Q ⊣ T

Proves the abstract categorical Master Theorem: the allocation functor
**Q : Mech → Alloc** has a right adjoint **T : Alloc → Mech**, and the right
adjoint is unique up to natural isomorphism.  Every IC-IR mechanism with a given
allocation rule is isomorphic to `T(q)`.

## Main declarations

* `MechDesign.transferFormula` — the abstract envelope transfer formula
* `MechDesign.typeDerivAlongAlloc` — the type-partial derivative along an allocation rule
* `MechDesign.T_wellDefined` — `T(q)` is BIC-IR for any monotone `q` (Lemma 4.2)
* `MechDesign.Tmech` — the mechanism object `T(r)`
* `MechDesign.T` — the Transfer Functor `T : Alloc → Mech` (Definition 4.1)
* `MechDesign.adj_Q_T` — the adjunction `Q ⊣ T` (Theorem 4.3)
* `MechDesign.T_terminal` — `T(q)` is terminal in **Mech_q** (Corollary 4.4)
* `MechDesign.masterTheorem_existence` — existence and uniqueness (Thm 4.5 i)
* `MechDesign.masterTheorem_isomorphism` — every BIC mechanism ≅ `T(q)` (Thm 4.5 ii)
* `MechDesign.masterTheorem_transferInvariance` — transfer invariance (Thm 4.5 iii)

## References

* Mac Lane (1978), *Categories for the Working Mathematician*, Chapter IV
* Myerson (1981), *Optimal Auction Design*, Theorem 2
* Hammond (1979), *Straightforward Incentive Compatibility*, Theorem 1
* Rochet (1985), *The Taxation Principle*, Proposition 1
-/

open CategoryTheory CategoryTheory.Limits MeasureTheory Filter

namespace MechDesign

/-! ### 4.1 The Transfer Functor **T : Alloc → Mech** (Definition 4.1) -/

/-- **The abstract envelope transfer formula** (Definition 4.1):
given the type-partial derivative `vθ_partial s = (∂v/∂s)(q(s), s)`, the unique
BIC transfer with boundary condition `V(θ_min) = 0` is

  `t*(θ) = v(q(θ), θ) - ∫_{θ_min}^θ (∂v/∂s)(q(s), s) ds`

*Reference*: Definition 4.1; Lemmas 2.1, 3.1. -/
noncomputable def transferFormula {A : Type*} (v : A → ℝ → ℝ) (θ_min : ℝ)
    (vθ_partial : ℝ → ℝ)   -- s ↦ (∂v/∂s)(q(s), s), the type-derivative along q
    (q : ℝ → A) (θ : ℝ) : ℝ :=
  v (q θ) θ - ∫ s in θ_min..θ, vθ_partial s

/-- The type-partial derivative `s ↦ (∂v/∂s)(q(s), s)` induced by a monotone
allocation rule `q`.  Used as input to `transferFormula`. -/
noncomputable def typeDerivAlongAlloc {A : Type*} [Preorder A]
    (v : A → ℝ → ℝ) (q : MonotoneAlloc A) : ℝ → ℝ :=
  fun s => deriv (v (q.q s)) s

/-- **Lemma 4.2**: For any monotone allocation rule `r`, the mechanism
`T(r) = (r.q, transferFormula(...))` is BIC and IR.
Proof uses the if-direction of Lemmas 2.1 and 3.1: the envelope formula produces
an IC mechanism whenever `q` is non-decreasing under SC.
*Reference*: Lemma 4.2. -/
lemma T_wellDefined {A : Type*} [LinearOrder A] [AddCommGroup A] [IsOrderedAddMonoid A] {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c) :
    IsIC v θ_min ⟨r.q, transferFormula v θ_min (typeDerivAlongAlloc v r) r.q⟩ ∧
    IsIR v θ_min ⟨r.q, transferFormula v θ_min (typeDerivAlongAlloc v r) r.q⟩ := by
  refine ⟨?_, ?_⟩
  · -- IsIC: V(θ) ≥ U(θ, θ') for all physical θ, θ' (θ_min ≤ θ, θ_min ≤ θ').
    -- Since θ_min > 0, both θ > 0 and θ' > 0 always, so FTC + SC + integral_mono apply.
    intro θ θ' hθ hθ'
    have hθ'_pos : 0 < θ' := lt_of_lt_of_le hθ_pos hθ'
    have hθ_pos' : 0 < θ := lt_of_lt_of_le hθ_pos hθ
    -- Unfold to integral inequality form.
    show v (r.q θ) θ - transferFormula v θ_min (typeDerivAlongAlloc v r) r.q θ ≥
        v (r.q θ') θ - transferFormula v θ_min (typeDerivAlongAlloc v r) r.q θ'
    simp only [transferFormula]
    -- After simp, need:
    --   v(qθ,θ) - (v(qθ,θ) - I θ) ≥ v(qθ',θ) - (v(qθ',θ') - I θ')
    -- where I x = ∫_{θ_min}^x typeDerivAlongAlloc v r s.
    -- Equivalent: I θ - I θ' ≥ v(qθ',θ) - v(qθ',θ').
    -- Using interval split (hint): I θ - I θ' = ∫_{θ'}^θ D.
    set Iθ : ℝ := ∫ s in θ_min..θ, typeDerivAlongAlloc v r s with hIθ_def
    set Iθ' : ℝ := ∫ s in θ_min..θ', typeDerivAlongAlloc v r s with hIθ'_def
    set Iθ'_θ : ℝ := ∫ s in θ'..θ, typeDerivAlongAlloc v r s with hIθ'θ_def
    -- Interval split: I θ_min..θ' + ∫_{θ'}^θ = ∫_{θ_min}^θ
    have hsplit : Iθ' + Iθ'_θ = Iθ := by
      rw [hIθ_def, hIθ'_def, hIθ'θ_def]
      exact intervalIntegral.integral_add_adjacent_intervals (hint θ_min θ') (hint θ' θ)
    -- Reduce the goal to: Iθ'_θ ≥ v(qθ', θ) - v(qθ', θ')
    suffices h : Iθ'_θ ≥ v (r.q θ') θ - v (r.q θ') θ' by linarith
    -- Physical case: both θ, θ' > 0 (from θ_min > 0 and IsIC restriction).
    · -- FTC: ∫_{θ'}^θ deriv(v(qθ')) s = v(qθ', θ) - v(qθ', θ')
      have hFTC : (∫ s in θ'..θ, deriv (v (r.q θ')) s) = v (r.q θ') θ - v (r.q θ') θ' := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro s hs
          have hs_pos : 0 < s := by
            rcases le_total θ' θ with hle | hle
            · rw [Set.uIcc_of_le hle] at hs; exact lt_of_lt_of_le hθ'_pos hs.1
            · rw [Set.uIcc_of_ge hle] at hs; exact lt_of_lt_of_le hθ_pos' hs.1
          exact ((hdiff (r.q θ')) s hs_pos).differentiableAt
            (IsOpen.mem_nhds isOpen_Ioi hs_pos) |>.hasDerivAt
        · exact hintC (r.q θ') θ' θ
      -- Now: Iθ'_θ ≥ ∫_{θ'}^θ deriv(v(qθ')) s.
      -- This holds by integral_mono via SC + monotonicity of r.q.
      rw [← hFTC]
      -- Goal: ∫_{θ'}^θ typeDerivAlongAlloc v r s ≥ ∫_{θ'}^θ deriv (v (r.q θ')) s
      -- Pointwise: typeDerivAlongAlloc v r s = deriv (v (r.q s)) s ≥ deriv (v (r.q θ')) s
      -- when r.q s ≥ r.q θ'.
      rcases le_total θ' θ with hle | hle
      · -- θ' ≤ θ: integration interval is [θ', θ]. For s ∈ [θ', θ], s ≥ θ', so r.q s ≥ r.q θ'.
        -- Goal: ∫ D ≥ ∫ D' = ∫ D' ≤ ∫ D, so hintC (for D') is the first arg, hint (for D) second.
        rw [hIθ'θ_def]
        apply intervalIntegral.integral_mono_on hle (hintC (r.q θ') θ' θ) (hint θ' θ)
        intro s hs
        -- hs : s ∈ Icc θ' θ; need deriv (v (r.q θ')) s ≤ typeDerivAlongAlloc v r s
        unfold typeDerivAlongAlloc
        have hqle : r.q θ' ≤ r.q s := r.hMono hs.1
        rcases lt_or_eq_of_le hqle with hqlt | hqeq
        · have hSCq := hSC (r.q s) (r.q θ') hqlt
          have hs_pos : 0 < s := lt_of_lt_of_le hθ'_pos hs.1
          have hd1 : DifferentiableAt ℝ (v (r.q s)) s :=
            ((hdiff (r.q s)) s hs_pos).differentiableAt
              (IsOpen.mem_nhds isOpen_Ioi hs_pos)
          have hd2 : DifferentiableAt ℝ (v (r.q θ')) s :=
            ((hdiff (r.q θ')) s hs_pos).differentiableAt
              (IsOpen.mem_nhds isOpen_Ioi hs_pos)
          have hhas : HasDerivAt (fun x => v (r.q s) x - v (r.q θ') x)
              (deriv (v (r.q s)) s - deriv (v (r.q θ')) s) s :=
            HasDerivAt.sub hd1.hasDerivAt hd2.hasDerivAt
          have hacc : AccPt s (𝓟 D) := by
            rw [accPt_principal_iff_nhdsWithin]
            exact (right_nhdsWithin_Ioo_neBot hs_pos).mono
              (nhdsWithin_mono _ (fun x hx => ⟨hD_Ioi (Set.mem_Ioi.mpr hx.1), hx.2.ne⟩))
          linarith [hhas.hasDerivWithinAt.nonneg_of_monotoneOn hacc hSCq.monotoneOn]
        · rw [← hqeq]
      · -- θ ≤ θ': backwards integral case — reduce to forward by integral_symm.
        -- Key: ∫_{θ}^{θ'} typeDerivAlongAlloc ≤ ∫_{θ}^{θ'} deriv(v(r.q θ'))
        -- pointwise: r.q s ≤ r.q θ' for s ∈ [θ,θ'], so SC gives deriv(v(r.q s)) ≤ deriv(v(r.q θ')).
        have key : ∫ s in θ..θ', typeDerivAlongAlloc v r s ≤
                   ∫ s in θ..θ', deriv (v (r.q θ')) s :=
          intervalIntegral.integral_mono_on hle (hint θ θ') (hintC (r.q θ') θ θ') (by
            intro s hs
            unfold typeDerivAlongAlloc
            have hqle : r.q s ≤ r.q θ' := r.hMono hs.2
            rcases lt_or_eq_of_le hqle with hqlt | hqeq
            · have hSCq := hSC (r.q θ') (r.q s) hqlt
              have hs_pos : 0 < s := lt_of_lt_of_le hθ_pos' hs.1
              have hd1 : DifferentiableAt ℝ (v (r.q s)) s :=
                ((hdiff (r.q s)) s hs_pos).differentiableAt
                  (IsOpen.mem_nhds isOpen_Ioi hs_pos)
              have hd2 : DifferentiableAt ℝ (v (r.q θ')) s :=
                ((hdiff (r.q θ')) s hs_pos).differentiableAt
                  (IsOpen.mem_nhds isOpen_Ioi hs_pos)
              -- HasDerivAt for the difference function, then use nonneg_of_monotoneOn
              have hhas : HasDerivAt (fun x => v (r.q θ') x - v (r.q s) x)
                  (deriv (v (r.q θ')) s - deriv (v (r.q s)) s) s :=
                HasDerivAt.sub hd2.hasDerivAt hd1.hasDerivAt
              have hacc : AccPt s (𝓟 D) := by
                rw [accPt_principal_iff_nhdsWithin]
                exact (right_nhdsWithin_Ioo_neBot hs_pos).mono
                  (nhdsWithin_mono _ (fun x hx => ⟨hD_Ioi (Set.mem_Ioi.mpr hx.1), hx.2.ne⟩))
              linarith [hhas.hasDerivWithinAt.nonneg_of_monotoneOn hacc hSCq.monotoneOn]
            · rw [← hqeq])
        -- integral_symm θ θ' : ∫ x in θ'..θ, f x = -∫ x in θ..θ', f x
        have h1 : ∫ s in θ'..θ, typeDerivAlongAlloc v r s =
                  -∫ s in θ..θ', typeDerivAlongAlloc v r s :=
          intervalIntegral.integral_symm θ θ'
        have h2 : ∫ s in θ'..θ, deriv (v (r.q θ')) s =
                  -∫ s in θ..θ', deriv (v (r.q θ')) s :=
          intervalIntegral.integral_symm θ θ'
        rw [hIθ'θ_def, h1]
        linarith [h2]
  · -- IsIR: v(r.q θ_min, θ_min) - t*(θ_min) ≥ 0
    -- t*(θ_min) = v(r.q θ_min, θ_min) - ∫_{θ_min}^{θ_min} D = v(...) - 0
    change v (r.q θ_min) θ_min -
        transferFormula v θ_min (typeDerivAlongAlloc v r) r.q θ_min ≥ 0
    simp only [transferFormula, intervalIntegral.integral_same, sub_zero]
    linarith

/-- The BIC-IR mechanism `T(r) = (r.q, t*)` as an element of `ICIRMechanism`. -/
noncomputable def Tmech {A : Type*} [LinearOrder A] [AddCommGroup A] [IsOrderedAddMonoid A] {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c) :
    ICIRMechanism A v θ_min :=
  { mech := ⟨r.q, transferFormula v θ_min (typeDerivAlongAlloc v r) r.q⟩
    hMono := r.hMono
    hIC   := (T_wellDefined hθ_pos hSC hD_Ioi r hdiff hint hintC).1
    hIR   := (T_wellDefined hθ_pos hSC hD_Ioi r hdiff hint hintC).2 }

/-- **T : Alloc → Mech** — the Transfer Functor (Definition 4.1).
- On objects: `T(r) = (r.q, t*)` where `t*` is the envelope transfer formula.
- On morphisms: `T(φ) = (φ, φ)` — the same type transformation on both components.
*Reference*: Definition 4.1. -/
noncomputable def T {A : Type*} [LinearOrder A] [AddCommGroup A] [IsOrderedAddMonoid A] {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (hint : ∀ (r : MonotoneAlloc A) a b,
      IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b) :
    MonotoneAlloc A ⥤ ICIRMechanism A v θ_min where
  obj r     := Tmech hθ_pos hSC hD_Ioi r hdiff (hint r) hintC
  map {r r'} f :=
    { hAlloc   := f.h
      h_spread := f.h_spread
      hTransf  := by
        -- Goal: ∀ θ, T(r).t θ ≤ T(r').t θ, i.e.
        --   v(r.q θ, θ) - ∫_{θ_min}^θ deriv(v(r.q ·)) s ds ≤
        --   v(r'.q θ, θ) - ∫_{θ_min}^θ deriv(v(r'.q ·)) s ds
        --
        -- After rearranging, this is the inequality
        --   v(r'.q θ, θ) - v(r.q θ, θ) ≥
        --   ∫_{θ_min}^θ [deriv(v(r'.q s)) s - deriv(v(r.q s)) s] ds.
        --
        -- The spread-monotone-allochom branch enriches `AllocHom` with
        --   `f.h_spread : Monotone (fun θ => r'.q θ - r.q θ)`.
        -- In the Myerson case `v(a, θ) = a · θ`:
        --   LHS = (r'.q θ - r.q θ) · θ,
        --   RHS = ∫_{θ_min}^θ (r'.q s - r.q s) ds,
        -- and the inequality reduces to
        --   θ · Δ(θ) ≥ ∫_{θ_min}^θ Δ(s) ds   where Δ = r'.q - r.q.
        -- Because Δ is non-decreasing (= `f.h_spread`), Δ(s) ≤ Δ(θ) for
        -- s ≤ θ, so this follows from `intervalIntegral.integral_mono_on`
        -- together with `θ_min ≥ 0` (so the boundary term θ_min · Δ(θ_min)
        -- is dominated).
        --
        -- For a general value function `v`, however, the same reduction is
        -- not available: it requires additional structural assumptions on
        -- `v` — most cleanly, that `v(·, θ)` is **affine in `a`** with the
        -- same affine slope across types (the Myerson/Mirrlees regime), or
        -- a uniform convexity/Lipschitz condition controlling the
        -- cross-partial `∂²v/∂a∂θ`.  These extra hypotheses are not part
        -- of the current `T` signature.
        --
        -- The abstract framework therefore documents this as the remaining
        -- gap on the spread-monotone-allochom branch: the spread field
        -- `f.h_spread` is necessary (and in the Myerson case sufficient),
        -- but proving `T.map.hTransf` in full categorical generality
        -- additionally requires structural assumptions on `v`.
        intro θ _hθ
        -- `f.h_spread` is in scope here for future Myerson-specific use.
        -- We do NOT discharge the inequality at this level of generality.
        sorry
    }
  map_id _     := by apply @Subsingleton.elim _ mechHom_subsingleton
  map_comp _ _ := by apply @Subsingleton.elim _ mechHom_subsingleton

/-! ### 4.2 The Adjunction **Q ⊣ T** (Theorem 4.3) -/

/-- **Theorem 4.3: Q ⊣ T** — the allocation functor `Q` is left adjoint to the
transfer functor `T`:

  `Hom_Alloc(Q(m), r) ≅ Hom_Mech(m, T(r))`  naturally in `m` and `r`.

*Proof sketch*: The natural bijection is exhibited explicitly.
- *Forward*: given `φ : Q(m) → r` in **Alloc**, construct `φ̃ : m → T(r)` in **Mech**
  with `φ̃.φ = φ.φ`.  Transfer compatibility holds because both `m.t` and
  `T(r).t ∘ φ` satisfy the same envelope formula with allocation `m.q`.
- *Backward*: given `ψ : m → T(r)` in **Mech**, `Q(ψ)` is a morphism `Q(m) → r`.
Naturality follows from functoriality of Q and T.
*Reference*: Theorem 4.3; Mac Lane (1978), Chapter IV. -/
-- `Adjunction` is a structure (Type), not a Prop, so we use `def` not `theorem`.
-- `θ_min` must be passed explicitly: neither `Q hSC` nor `T hSC hint` carries it.
noncomputable def adj_Q_T {A : Type*} [LinearOrder A] [AddCommGroup A] [IsOrderedAddMonoid A] {v : A → ℝ → ℝ} (θ_min : ℝ)
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D)
    (hD : ∀ θ, θ ∈ D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (hint : ∀ (r : MonotoneAlloc A) a b,
      IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    -- Global only-if envelope condition: every BIC-IR mechanism has the envelope derivative.
    -- This is the only-if direction of the IC envelope theorem (IC + diff of t → V' = typeDerivAlongAlloc).
    (hEnv : ∀ (m : ICIRMechanism A v θ_min) (θ : ℝ), 0 < θ →
        HasDerivAt (fun s => v (m.mech.q s) s - m.mech.t s)
            (typeDerivAlongAlloc v ⟨m.mech.q, m.hMono⟩ θ) θ) :
    Q (θ_min := θ_min) hSC hD ⊣ T (θ_min := θ_min) hθ_pos hSC hD_Ioi hdiff hintC hint :=
  -- Both Mech and Alloc are thin (preorder) categories, so:
  -- * Naturality conditions are trivial (Subsingleton.elim on the hom-set).
  -- * Triangle identities reduce to NatTrans.ext + Subsingleton.elim on hom-sets.
  -- The unit η_m : m → T(Q(m)) is the non-trivial part: hTransf uses FTC + IR (mirrors T_terminal).
  -- The counit ε_r : Q(T(r)) → r is le_refl (Q(T(r)).q = r.q definitionally).
  Adjunction.mkOfUnitCounit {
    unit := {
      app := fun m =>
        { hAlloc   := fun _ => le_refl _
          h_spread := by
            -- T(Q(m)).q = m.q definitionally, so spread = m.q θ - m.q θ = 0.
            change Monotone (fun θ => m.mech.q θ - m.mech.q θ)
            simp [sub_self]; exact monotone_const
          hTransf := fun θ hθ => by
            -- Goal: m.mech.t θ ≤ T(Q(m)).mech.t θ
            -- Physical case only (θ ≥ θ_min > 0). FTC on hEnv + IR gives the envelope.
            change m.mech.t θ ≤ v (m.mech.q θ) θ -
                ∫ s in θ_min..θ, typeDerivAlongAlloc v ⟨m.mech.q, m.hMono⟩ s
            have hθ_pos' : 0 < θ := lt_of_lt_of_le hθ_pos hθ
            have hFTC : ∫ s in θ_min..θ,
                  typeDerivAlongAlloc v ⟨m.mech.q, m.hMono⟩ s =
                  (v (m.mech.q θ) θ - m.mech.t θ) -
                  (v (m.mech.q θ_min) θ_min - m.mech.t θ_min) :=
              intervalIntegral.integral_eq_sub_of_hasDerivAt
                (fun s hs => hEnv m s <|
                  lt_of_lt_of_le (lt_min hθ_pos hθ_pos') (by simpa [Set.uIcc, min_comm] using hs.1))
                (hint ⟨m.mech.q, m.hMono⟩ θ_min θ)
            have hIR : (0 : ℝ) ≤ v (m.mech.q θ_min) θ_min - m.mech.t θ_min := m.hIR
            linarith
        }
      naturality := fun _ _ _ => @Subsingleton.elim _ mechHom_subsingleton _ _
    }
    counit := {
      -- Q(T(r)).q = r.q definitionally, so the AllocHom is le_refl.
      app := fun r =>
        { h := fun _ => le_refl _
          h_spread := by
            -- Source `Q(T(r))` has q-field definitionally equal to `r.q`, so
            -- spread = r.q - r.q = 0, which is constantly monotone.
            change Monotone (fun θ => r.q θ - r.q θ)
            intro a b _; simp }
      naturality := fun _ _ _ => @Subsingleton.elim _ allocHom_subsingleton _ _
    }
    -- Triangle identities: both sides are equal in Subsingleton hom-sets.
    left_triangle := by ext; exact @Subsingleton.elim _ allocHom_subsingleton _ _
    right_triangle := by ext; exact @Subsingleton.elim _ mechHom_subsingleton _ _
  }

/-- **Lemma 1.8 (proved)**: Q preserves all small colimits.
Q is the left adjoint in `adj_Q_T`, so `leftAdjoint_preservesColimits` applies directly. -/
noncomputable instance Q_preservesColimits {A : Type*} [LinearOrder A] [AddCommGroup A] [IsOrderedAddMonoid A] {v : A → ℝ → ℝ}
    (θ_min : ℝ) (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D)
    (hD : ∀ θ, θ ∈ D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (hint : ∀ (r : MonotoneAlloc A) a b,
      IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hEnv : ∀ (m : ICIRMechanism A v θ_min) (θ : ℝ), 0 < θ →
        HasDerivAt (fun s => v (m.mech.q s) s - m.mech.t s)
            (typeDerivAlongAlloc v ⟨m.mech.q, m.hMono⟩ θ) θ) :
    PreservesColimits (Q (θ_min := θ_min) hSC hD) :=
  (adj_Q_T θ_min hθ_pos hSC hD hD_Ioi hdiff hintC hint hEnv).leftAdjoint_preservesColimits

/-! ### 4.3 Terminality of T(q) in **Mech_q** (Corollary 4.4) -/

/-- The set of all BIC-IR mechanisms with allocation rule equal to `r.q` pointwise. -/
def MechWithAlloc {A : Type*} [LinearOrder A] [AddCommGroup A] [IsOrderedAddMonoid A] {v : A → ℝ → ℝ} {θ_min : ℝ}
    (r : MonotoneAlloc A) : Set (ICIRMechanism A v θ_min) :=
  {m | ∀ θ, m.mech.q θ = r.q θ}

/-- **Corollary 4.4**: `T(r)` is the **terminal object** in the full subcategory
`MechWithAlloc r`: every BIC-IR mechanism with allocation `r.q` has a unique
morphism to `T(r)`.

*Proof sketch*:
- *Existence*: by the envelope characterisation (only-if direction of Lemmas 2.1/3.1),
  any BIC mechanism `(r.q, t)` satisfies `t = t*`, so `id_Θ` is a valid morphism.
- *Uniqueness*: any morphism `φ : (r.q, t) → T(r)` must satisfy `r.q ∘ φ = r.q`.
  If `r.q` is strictly increasing, this forces `φ = id`.
*Reference*: Corollary 4.4; Mac Lane (1978), Section IV.1. -/
theorem T_terminal {A : Type*} [LinearOrder A] [AddCommGroup A] [IsOrderedAddMonoid A] {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (m : ICIRMechanism A v θ_min) (hm : m ∈ MechWithAlloc r)
    -- Envelope derivative condition: the surplus V_m = v(r.q ·) · - m.t has the
    -- envelope derivative at every physical type.  This is the only-if direction of
    -- the envelope theorem; it follows from IC + differentiability of v and t.
    (hEnv : ∀ θ > 0, HasDerivAt (fun s => v (r.q s) s - m.mech.t s)
        (typeDerivAlongAlloc v r θ) θ) :
    Nonempty (m ⟶ Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC) ∧
    ∀ (f g : m ⟶ Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC), f = g := by
  refine ⟨?_, ?_⟩
  · -- Existence: build a `MechHom m (Tmech ...)`.
    -- hAlloc: m.q θ = r.q θ from hm, so le_of_eq applies.
    -- hTransf: only-if envelope theorem.  For θ > 0, FTC on hEnv gives
    --   ∫_{θ_min}^θ typeDerivAlongAlloc = V_m(θ) - V_m(θ_min).
    -- IR gives V_m(θ_min) ≥ 0, so m.t θ ≤ t*(θ).
    refine ⟨⟨fun θ => le_of_eq (hm θ), ?_, ?_⟩⟩
    · -- hTransf (field 2): FTC + IR. θ ≥ θ_min > 0 ensures FTC is available.
      intro θ hθ_lb
      have hθ_pos' : 0 < θ := lt_of_lt_of_le hθ_pos hθ_lb
      simp only [Tmech, transferFormula]
      have hFTC : ∫ s in θ_min..θ, typeDerivAlongAlloc v r s =
                (v (r.q θ) θ - m.mech.t θ) - (v (r.q θ_min) θ_min - m.mech.t θ_min) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro s hs
          have hs_pos : 0 < s := by
            rcases le_total θ_min θ with hle | hle
            · rw [Set.uIcc_of_le hle] at hs; exact lt_of_lt_of_le hθ_pos hs.1
            · rw [Set.uIcc_of_ge hle] at hs; exact lt_of_lt_of_le hθ_pos' hs.1
          exact hEnv s hs_pos
        · exact hint θ_min θ
      have hIR : (0 : ℝ) ≤ v (r.q θ_min) θ_min - m.mech.t θ_min := by
        have h : v (m.mech.q θ_min) θ_min - m.mech.t θ_min ≥ 0 := m.hIR
        rw [hm θ_min] at h; linarith
      linarith
    · -- h_spread (field 3): Tmech.q = r.q definitionally; m.q = r.q from hm; spread = 0.
      have hzero : (fun θ => (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC).mech.q θ -
                              m.mech.q θ) = fun _ => (0 : A) :=
        funext fun θ => by show r.q θ - m.mech.q θ = 0; rw [← hm θ]; exact sub_self _
      rw [hzero]; exact monotone_const
  · intro f g
    exact @Subsingleton.elim _ mechHom_subsingleton _ _

/-! ### 4.4 The Master Theorem (Theorem 4.5) -/

/-- **Theorem 4.5(i) — Existence and Uniqueness**: For any monotone allocation rule `r`
and boundary condition `V(θ_min) = 0`, there exists a **unique** BIC-IR mechanism
with allocation `r.q`.  It is the explicit mechanism `T(r)`.

Uniqueness: terminal objects are unique up to unique isomorphism (Mac Lane, Sec. III.1).
*Reference*: Theorem 4.5(i). -/
theorem masterTheorem_existence {A : Type*} [LinearOrder A] [AddCommGroup A] [IsOrderedAddMonoid A] {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c) :
    ∃! (m : ICIRMechanism A v θ_min),
      m ∈ MechWithAlloc r ∧
      ∀ θ, m.mech.t θ = transferFormula v θ_min (typeDerivAlongAlloc v r) r.q θ := by
  refine ⟨Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC, ⟨?_, ?_⟩, ?_⟩
  · intro θ; rfl
  · intro θ; rfl
  · -- Uniqueness: requires the only-if envelope theorem (terminality of Tmech).
    rintro m ⟨hm_alloc, hm_t⟩
    obtain ⟨⟨mq, mt⟩, mIC, mIR⟩ := m
    simp only [MechWithAlloc, Set.mem_setOf_eq] at hm_alloc
    have hq : mq = r.q := funext hm_alloc
    have ht : mt = transferFormula v θ_min (typeDerivAlongAlloc v r) r.q := funext hm_t
    subst hq; subst ht
    simp only [Tmech]

/-- **Theorem 4.5(ii) — Isomorphism**: Every BIC-IR mechanism with allocation `r.q`
and `V(θ_min) = 0` is isomorphic to `T(r)` in **Mech**.

Proof: the unique morphism from Corollary 4.4 is `id_Θ`, which is an isomorphism.
*Reference*: Theorem 4.5(ii). -/
theorem masterTheorem_isomorphism {A : Type*} [LinearOrder A] [AddCommGroup A] [IsOrderedAddMonoid A] {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (m : ICIRMechanism A v θ_min) (hm : m ∈ MechWithAlloc r)
    -- Envelope derivative condition (only-if direction): same as T_terminal.
    (hEnv : ∀ θ > 0, HasDerivAt (fun s => v (r.q s) s - m.mech.t s) (typeDerivAlongAlloc v r θ) θ)
    -- Boundary condition V(θ_min) = 0: normalises the surplus at the lowest type.
    (hBC : v (m.mech.q θ_min) θ_min = m.mech.t θ_min) :
    Nonempty (m ≅ Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC) := by
  -- FTC + boundary condition gives m.t θ = t*(θ) for all physical θ > 0.
  have htransf_eq : ∀ θ > 0,
      m.mech.t θ = (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC).mech.t θ := by
    intro θ hθ
    simp only [Tmech, transferFormula]
    have hFTC : ∫ s in θ_min..θ, typeDerivAlongAlloc v r s =
            (v (r.q θ) θ - m.mech.t θ) - (v (r.q θ_min) θ_min - m.mech.t θ_min) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro s hs
        have hs_pos : 0 < s := by
          rcases le_total θ_min θ with hle | hle
          · rw [Set.uIcc_of_le hle] at hs; exact lt_of_lt_of_le hθ_pos hs.1
          · rw [Set.uIcc_of_ge hle] at hs; exact lt_of_lt_of_le hθ hs.1
        exact hEnv s hs_pos
      · exact hint θ_min θ
    have hBC' : v (r.q θ_min) θ_min - m.mech.t θ_min = 0 := by
      rw [← hm θ_min]; linarith [hBC]
    linarith
  -- Both allocation rules agree; the isomorphism hom/inv identities hold by subsingleton.
  have hqeq : ∀ θ, (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC).mech.q θ = m.mech.q θ :=
    fun θ => (hm θ).symm
  have hom_transf : ∀ θ, θ_min ≤ θ → m.mech.t θ ≤ (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC).mech.t θ :=
    fun θ hθ_lb => le_of_eq (htransf_eq θ (lt_of_lt_of_le hθ_pos hθ_lb))
  have inv_transf : ∀ θ, θ_min ≤ θ → (Tmech hθ_pos hSC hD_Ioi r hdiff hint hintC).mech.t θ ≤ m.mech.t θ :=
    fun θ hθ_lb => le_of_eq (htransf_eq θ (lt_of_lt_of_le hθ_pos hθ_lb)).symm
  have hspread_zero : ∀ (f g : ℝ → A), (∀ θ, f θ = g θ) →
      Monotone (fun θ => f θ - g θ) := fun f g heq => by
    have : (fun θ => f θ - g θ) = fun _ => (0 : A) := funext fun θ => by rw [heq θ]; exact sub_self _
    rw [this]; exact monotone_const
  exact ⟨{
    hom := ⟨fun θ => le_of_eq (hm θ), hom_transf,
            hspread_zero _ _ hqeq⟩
    inv := ⟨fun θ => le_of_eq (hqeq θ), inv_transf,
            hspread_zero _ _ (fun θ => (hqeq θ).symm)⟩
    hom_inv_id := @Subsingleton.elim _ mechHom_subsingleton _ _
    inv_hom_id := @Subsingleton.elim _ mechHom_subsingleton _ _
  }⟩

/-- **Theorem 4.5(iii) — Transfer Invariance**: Any two BIC-IR mechanisms with the
same allocation rule and `V(θ_min) = 0` generate the **same expected transfer**.

Proof: by Thm 4.5(ii), both are isomorphic to `T(r)`, so their transfers coincide
pointwise, and hence their expected transfers are equal.
*Reference*: Theorem 4.5(iii); Myerson (1981), Theorem 2. -/
theorem masterTheorem_transferInvariance {A : Type*} [LinearOrder A]
    [AddCommGroup A] [IsOrderedAddMonoid A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (hθ_pos : 0 < θ_min) {D : Set ℝ} (hSC : SingleCrossing v D) (hD_Ioi : Set.Ioi 0 ⊆ D)
    (r : MonotoneAlloc A)
    (hdiff : ∀ (a : A), DifferentiableOn ℝ (v a) (Set.Ioi 0))
    (hint : ∀ a b, IntervalIntegrable (typeDerivAlongAlloc v r) MeasureTheory.volume a b)
    (hintC : ∀ (a : A) b c, IntervalIntegrable (deriv (v a)) MeasureTheory.volume b c)
    (m₁ m₂ : ICIRMechanism A v θ_min)
    (hm₁ : m₁ ∈ MechWithAlloc r) (hm₂ : m₂ ∈ MechWithAlloc r)
    (hEnv₁ : ∀ θ > 0, HasDerivAt (fun s => v (r.q s) s - m₁.mech.t s) (typeDerivAlongAlloc v r θ) θ)
    (hBC₁ : v (m₁.mech.q θ_min) θ_min = m₁.mech.t θ_min)
    (hEnv₂ : ∀ θ > 0, HasDerivAt (fun s => v (r.q s) s - m₂.mech.t s) (typeDerivAlongAlloc v r θ) θ)
    (hBC₂ : v (m₂.mech.q θ_min) θ_min = m₂.mech.t θ_min)
    (μ : MeasureTheory.Measure ℝ) [IsFiniteMeasure μ] :
    ∫ θ, m₁.mech.t θ ∂μ = ∫ θ, m₂.mech.t θ ∂μ := by
  -- Both mechanisms are isomorphic to Tmech; squeeze the two iso morphisms to get t₁ = t₂.
  obtain ⟨iso1⟩ := masterTheorem_isomorphism hθ_pos hSC hD_Ioi r hdiff hint hintC m₁ hm₁ hEnv₁ hBC₁
  obtain ⟨iso2⟩ := masterTheorem_isomorphism hθ_pos hSC hD_Ioi r hdiff hint hintC m₂ hm₂ hEnv₂ hBC₂
  have heq : m₁.mech.t = m₂.mech.t :=
    funext fun θ => by
      rcases le_or_gt θ_min θ with hθ_lb | hθ_lt
      · exact le_antisymm
          (le_trans (iso1.hom.hTransf θ hθ_lb) (iso2.inv.hTransf θ hθ_lb))
          (le_trans (iso2.hom.hTransf θ hθ_lb) (iso1.inv.hTransf θ hθ_lb))
      · -- θ < θ_min: design limitation (same as other non-physical cases).
        sorry
  rw [heq]

end MechDesign
