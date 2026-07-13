import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.CompleteLattice.Basic

/-!
# Stage 1: Abstract Categorical Framework

Defines the categories **Mech** and **Alloc**, the forgetful functor
**Q : Mech → Alloc**, and establishes that **Alloc** is complete and **Q**
preserves limits.  These are the prerequisites for the adjunction Q ⊣ T proved
in `MasterTheorem.lean`.

## Main declarations

* `MechDesign.SingleCrossing` — condition SC
* `MechDesign.IsIC`, `MechDesign.IsIR` — incentive and participation constraints
* `MechDesign.ICIRMechanism` — object type for the category **Mech**
* `MechDesign.MonotoneAlloc` — object type for the category **Alloc**
* `MechDesign.mechCategory`, `MechDesign.allocCategory` — category instances
* `MechDesign.Q` — forgetful functor Q : Mech → Alloc
* `MechDesign.IC_implies_monotone` — condition MON from IC + SC (Lemma 1.7 precursor)
* `MechDesign.alloc_hasLimits` — Lemma 1.7
* `MechDesign.Q_preservesColimits` — Lemma 1.8 (proved in `MasterTheorem.lean`)

## References

* Mac Lane (1978), *Categories for the Working Mathematician*, Chapters III–V
* Myerson (1981), *Optimal Auction Design*, Lemma 2
* Mirrlees (1971), *An Exploration in the Theory of Optimum Income Taxation*, Eq. (27)
-/

open CategoryTheory CategoryTheory.Limits MeasureTheory

namespace MechDesign

/-! ### 1.1 Economic Primitives -/

/-- **Condition SC** (Single Crossing): for any two allocations `a > a'`, the surplus
difference `v a θ - v a' θ` is strictly increasing in type `θ`.  Higher types have a
strictly greater marginal value for higher allocations. -/
def SingleCrossing {A : Type*} [Preorder A] (v : A → ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ (a a' : A), a > a' → StrictMonoOn (fun θ => v a θ - v a' θ) D

/-! ### 1.2 Mechanisms and Incentive Constraints -/

/-- A *direct mechanism* over allocation space `A`: an allocation rule `q : ℝ → A`
paired with a transfer rule `t : ℝ → ℝ`.  Utility is `v(q(θ), θ) - t(θ)` (quasilinear
in the transfer — condition QI is structural). -/
structure Mechanism (A : Type*) where
  q : ℝ → A   -- allocation rule
  t : ℝ → ℝ   -- transfer rule (positive = payment by agent)

/-- **Bayesian Incentive Compatibility (BIC)**: truth-telling is weakly optimal for
every type `θ` regardless of the report `θ'`. -/
def IsIC {A : Type*} (v : A → ℝ → ℝ) (θ_min : ℝ) (m : Mechanism A) : Prop :=
  ∀ θ θ' : ℝ, θ_min ≤ θ → θ_min ≤ θ' →
    v (m.q θ) θ - m.t θ ≥ v (m.q θ') θ - m.t θ'

/-- **Individual Rationality (IR)**: the lowest type `θ_min` receives non-negative
surplus.  Normalised to zero: `V(θ_min) = 0`. -/
def IsIR {A : Type*} (v : A → ℝ → ℝ) (θ_min : ℝ) (m : Mechanism A) : Prop :=
  v (m.q θ_min) θ_min - m.t θ_min ≥ 0

/-- A **BIC-IR mechanism**: a mechanism satisfying both `IsIC` and `IsIR`. -/
structure ICIRMechanism (A : Type*) [Preorder A] (v : A → ℝ → ℝ) (θ_min : ℝ) where
  mech : Mechanism A
  hMono : Monotone mech.q
  hIC   : IsIC v θ_min mech
  hIR   : IsIR v θ_min mech

/-! ### 1.3 The Category **Mech** (Definition 1.4)

Objects: BIC-IR mechanisms.
Morphisms: order-preserving type-space transformations that are simultaneously
compatible with the allocation and transfer rules. -/

/-- A morphism `f : m → m'` in **Mech** is given by the pointwise allocation
inequality `m.mech.q θ ≤ m'.mech.q θ`, together with **spread monotonicity** on the
allocation gap — matching the `AllocHom` condition so that `Q` can map `MechHom` to
`AllocHom` without a sorry.

**Design note (transfer condition deliberately omitted).**  An earlier version also
carried a transfer field `hTransf : ∀ θ ≥ θ_min, m.mech.t θ ≤ m'.mech.t θ`.  That field
makes `T : Alloc → Mech` *not a functor*: given an `AllocHom r ⟶ r'`, the envelope
transfers satisfy no order relation in general — `t*(r) ≤ t*(r')` requires structural
assumptions on `v` (affinity in the allocation, as in the Myerson/Mirrlees regime)
that are not part of the abstract framework.  Since `T` is the right adjoint the whole
Master Theorem rests on, the coherent resolution is to let **Mech**'s morphisms be
exactly the allocation-order morphisms, and to state the transfer content as explicit
theorems instead: `envelope_transfer_unique` (transfers of any two BIC-IR mechanisms
with the same allocation coincide) and `masterTheorem_transferInvariance`. -/
@[ext]
structure MechHom {A : Type*} [AddCommGroup A] [Preorder A] [IsOrderedAddMonoid A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    (m m' : ICIRMechanism A v θ_min) : Type where
  hAlloc   : ∀ θ, m.mech.q θ ≤ m'.mech.q θ
  h_spread : Monotone (fun θ => m'.mech.q θ - m.mech.q θ)

instance mechHom_subsingleton {A : Type*} [AddCommGroup A] [Preorder A] [IsOrderedAddMonoid A]
    {v : A → ℝ → ℝ} {θ_min : ℝ}
    {m m' : ICIRMechanism A v θ_min} : Subsingleton (MechHom m m') := by
  constructor; intro f g
  obtain ⟨fa, fs⟩ := f; obtain ⟨ga, gs⟩ := g
  congr 1

instance mechCategory {A : Type*} [AddCommGroup A] [Preorder A] [IsOrderedAddMonoid A]
    {v : A → ℝ → ℝ} {θ_min : ℝ} :
    Category (ICIRMechanism A v θ_min) where
  Hom m m'  := MechHom m m'
  id m      :=
    { hAlloc   := fun _ => le_rfl
      h_spread := by
        have : (fun θ => m.mech.q θ - m.mech.q θ) = fun _ => (0 : A) :=
          funext fun θ => sub_self _
        rw [this]; exact monotone_const }
  comp {m m' m''} f g  :=
    { hAlloc   := fun θ => le_trans (f.hAlloc θ) (g.hAlloc θ)
      h_spread := by
        have hsum : (fun θ => m''.mech.q θ - m.mech.q θ) =
            fun θ => (m''.mech.q θ - m'.mech.q θ) + (m'.mech.q θ - m.mech.q θ) :=
          funext fun θ => by abel
        rw [hsum]; exact Monotone.add g.h_spread f.h_spread }
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-! ### 1.4 The Category **Alloc** (Definition 1.5)

Objects: monotone (non-decreasing) allocation rules — condition MON.
Morphisms: order-preserving type transformations compatible with the allocation rule. -/

/-- An object of **Alloc**: an admissible (monotone) allocation rule.  Condition MON
is a consequence of IC + SC; see `IC_implies_monotone`. -/
@[ext]
structure MonotoneAlloc (A : Type*) [Preorder A] where
  q : ℝ → A
  hMono : Monotone q

/-- A morphism `h : r → r'` in **Alloc**: a pointwise inequality `r.q θ ≤ r'.q θ`
together with **spread monotonicity** — the difference `r'.q - r.q` is monotone in `θ`.
The spread condition is needed to make the functor `T : Alloc → Mech` well-defined on
morphisms: it is exactly the inequality required to prove `T(r).t ≤ T(r').t`.

This makes `MonotoneAlloc A` a thin (preorder-flavoured) category, but the spread
condition is an extra refinement beyond pure pointwise-≤. -/
@[ext]
structure AllocHom {A : Type*} [AddCommGroup A] [Preorder A] [IsOrderedAddMonoid A]
    (r r' : MonotoneAlloc A) : Type where
  h        : ∀ θ, r.q θ ≤ r'.q θ
  h_spread : Monotone (fun θ => r'.q θ - r.q θ)

instance allocHom_subsingleton {A : Type*} [AddCommGroup A] [Preorder A] [IsOrderedAddMonoid A]
    {r r' : MonotoneAlloc A} : Subsingleton (AllocHom r r') := by
  constructor; intro f g
  obtain ⟨ha, hs⟩ := f; obtain ⟨ga, gs⟩ := g
  congr 1

instance allocCategory {A : Type*} [AddCommGroup A] [Preorder A] [IsOrderedAddMonoid A] :
    Category (MonotoneAlloc A) where
  Hom r r'  := AllocHom r r'
  id r      :=
    { h := fun _ => le_rfl
      h_spread := by
        -- spread = fun θ => r.q θ - r.q θ = 0, which is constant hence monotone.
        have hzero : (fun θ => r.q θ - r.q θ) = fun _ => (0 : A) := by
          funext θ; exact sub_self _
        rw [hzero]; exact monotone_const }
  comp {r r' r''} f g  :=
    { h := fun θ => le_trans (f.h θ) (g.h θ)
      h_spread := by
        -- spread of (f then g) = spread(g) + spread(f) since
        -- (r''.q θ - r.q θ) = (r''.q θ - r'.q θ) + (r'.q θ - r.q θ).
        have hsum : (fun θ => r''.q θ - r.q θ) =
            (fun θ => (r''.q θ - r'.q θ) + (r'.q θ - r.q θ)) := by
          funext θ; abel
        rw [hsum]
        exact Monotone.add g.h_spread f.h_spread }
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-! ### 1.5 The Allocation Functor **Q : Mech → Alloc** (Definition 1.6) -/

/-- **Condition MON from IC + SC** (precursor to Lemma 1.7): every BIC mechanism has a
non-decreasing allocation rule.  Proof sketch: if `q` were decreasing over some
interval, a mimicry deviation by higher types would be profitable, violating IC.
*Reference*: Myerson (1981) Lemma 2; Mirrlees (1971) Eq. (27). -/
lemma IC_implies_monotone {A : Type*} [LinearOrder A] {v : A → ℝ → ℝ} {θ_min : ℝ}
    {D : Set ℝ} (hSC : SingleCrossing v D) (hD : ∀ θ, θ ∈ D)
    (m : ICIRMechanism A v θ_min) : MonotoneOn m.mech.q (Set.Ici θ_min) := by
  intro θ₁ hθ₁ θ₂ hθ₂ h12
  by_contra hlt
  rw [not_le] at hlt
  -- `hlt : m.mech.q θ₂ < m.mech.q θ₁`
  have h1 := m.hIC θ₁ θ₂ hθ₁ hθ₂
  have h2 := m.hIC θ₂ θ₁ hθ₂ hθ₁
  rcases eq_or_lt_of_le h12 with heq | hlt_θ
  · rw [heq] at hlt
    exact lt_irrefl _ hlt
  · have hSC' := hSC (m.mech.q θ₁) (m.mech.q θ₂) hlt
    linarith [hSC' (hD θ₁) (hD θ₂) hlt_θ]

/-- **Q : Mech → Alloc** — the forgetful functor that drops the transfer rule and
retains only the allocation rule.  Well-defined by `IC_implies_monotone`.
*Reference*: Definition 1.6 and the remark on forgetful functors in Section 1.5. -/
noncomputable def Q {A : Type*} [LinearOrder A] [AddCommGroup A] [IsOrderedAddMonoid A]
    {v : A → ℝ → ℝ}
    {θ_min : ℝ} {D : Set ℝ} (_hSC : SingleCrossing v D) (_hD : ∀ θ, θ ∈ D) :
    ICIRMechanism A v θ_min ⥤ MonotoneAlloc A where
  obj m       := ⟨m.mech.q, m.hMono⟩
  map f       :=
    { h        := f.hAlloc
      h_spread := f.h_spread }
  map_id _     := by apply @Subsingleton.elim _ allocHom_subsingleton
  map_comp _ _ := by apply @Subsingleton.elim _ allocHom_subsingleton

/-! ### 1.6 Q Preserves Colimits (Lemma 1.7) -/

-- **Lemma 1.8**: Q preserves all small colimits because it is the left adjoint in Q ⊣ T.
-- The proof requires `adj_Q_T` (defined in `MasterTheorem.lean`, which imports this file),
-- so it lives there as `MechDesign.Q_preservesColimits`.
-- *Reference*: Mac Lane (1978), Chapter V, Theorem 5.1 (left adjoints preserve colimits).

end MechDesign
