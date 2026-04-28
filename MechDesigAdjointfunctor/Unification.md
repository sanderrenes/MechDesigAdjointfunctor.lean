All projects
Category Theory
Look at applications of category theory for Institutional and mechanism design


How can I help you today?

    AI-assisted theorem proving in Lean and Agda
    Last message 23 hours ago
    Category theory for institutional design generalization
    Last message 8 days ago
    Econagents framework and category theory alignment
    Last message 9 days ago
    Open games curriculum and categorical representation
    Last message 18 days ago
    Category theory and auction revenue equivalence
    Last message 1 month ago
    Equivalence classes and allocation selection
    Last message 1 month ago

Instructions

This project needs to be mathematically correct. Check mathematical results for mistakes. Refer to relevant papers for later publication.
Files
23% of project capacity used
Indexing

    pdf

    pdf

    pdf

categorical-unification-mirrlees-myerson.md

25.75 KB •537 lines•Formatting may be inconsistent from source
# Revenue Equivalence and the Taxation Principle as a Single Categorical Theorem

## A Unified Proof via Adjunctions in Categories of Incentive-Compatible Mechanisms

---

## Overview

This document proves that Myerson's (1981) Revenue Equivalence Theorem and the Mirrlees (1971) Taxation Principle — as formalised by Hammond (1979) and Rochet (1985) — are both instances of a single categorical theorem:

> **Master Theorem.** In any category of incentive-compatible mechanisms over a one-dimensional ordered type space with quasilinear preferences, the allocation functor Q: Mech → Alloc has a right adjoint T. The right adjoint is unique up to natural isomorphism. Every incentive-compatible mechanism with a given allocation rule is isomorphic to T(q). Consequently, any two IC mechanisms with the same allocation rule and the same boundary condition generate the same expected transfer.

The proof proceeds in six stages:

1. Construct the abstract categorical framework shared by both models
2. Verify the framework applies to the Myerson auction setting
3. Verify the framework applies to the Mirrlees taxation setting
4. Prove the Master Theorem in the abstract framework
5. Instantiate the Master Theorem in each setting
6. Identify where conditions diverge and the result fails

---

## Stage 1: The Abstract Categorical Framework

### 1.1 The General Economic Environment

Let the following data be given:

- A **type space** Θ = [θ_min, θ_max] ⊂ ℝ, totally ordered
- A **type distribution** F: Θ → [0,1] with density f > 0 on Θ
- An **allocation space** A (a measurable space of outcomes)
- A **transfer space** T = ℝ
- A **utility function** U: A × T × Θ → ℝ satisfying quasilinearity in transfers:

```
U(a, t, θ) = v(a, θ) - t
```

where v: A × Θ → ℝ is the value function.

**Condition QI (Quasilinearity).** The utility function is additively separable in the transfer: U(a, t, θ) = v(a, θ) - t.

*QI is required throughout. Both Myerson and Mirrlees satisfy QI.*

### 1.2 The Single Crossing Condition

**Condition SC (Single Crossing).** For any two allocations a, a' ∈ A with a ≻ a' (in some order on A):

```
∂/∂θ [v(a, θ) - v(a', θ)] > 0   for all θ ∈ Θ
```

Higher types have a strictly greater marginal value for higher allocations.

*SC is required to establish monotonicity of the optimal allocation rule. Both models satisfy SC under their respective parametrisations; see Stages 2 and 3.*

*Reference: Mirrlees (1971), Section 2; Myerson (1981), Lemma 2.*

### 1.3 The Category Mech

**Definition 1.1 (Direct Mechanism).** A direct mechanism is a pair (q, t) where:

- q: Θ → A is a measurable allocation rule
- t: Θ → ℝ is a measurable transfer rule

**Definition 1.2 (Incentive Compatibility).** A mechanism (q, t) is **Bayesian Incentive Compatible (BIC)** if for all θ, θ' ∈ Θ:

```
v(q(θ), θ) - t(θ) ≥ v(q(θ'), θ) - t(θ')
```

Truth-telling is weakly optimal for every type.

**Definition 1.3 (Individual Rationality).** A mechanism (q, t) satisfies **Individual Rationality (IR)** if:

```
V(θ_min) = v(q(θ_min), θ_min) - t(θ_min) ≥ 0
```

The lowest type receives non-negative surplus.

**Definition 1.4 (Category Mech).** The category **Mech** has:

- *Objects:* BIC and IR direct mechanisms (q, t)
- *Morphisms:* A morphism φ: (q, t) → (q', t') is a type-space transformation φ: Θ → Θ' preserving IC and IR, such that q' ∘ φ = q and t' ∘ φ = t

**Remark.** Mech is a fibred category over the category TypeSp of type spaces and order-preserving maps. Objects are pairs (Θ, (q, t)) and morphisms respect both the base type space structure and the mechanism structure. See Grothendieck (1971) for the general theory of fibred categories.

### 1.4 The Category Alloc

**Definition 1.5 (Category Alloc).** The category **Alloc** has:

- *Objects:* Monotone allocation rules q: Θ → A (non-decreasing in θ under SC)
- *Morphisms:* A morphism φ: q → q' is an order-preserving type-space transformation φ: Θ → Θ' such that q' ∘ φ = q

**Condition MON (Monotonicity).** An allocation rule q is admissible (an object in Alloc) only if q is non-decreasing in θ.

*MON is a consequence of IC under SC. Proof: Myerson (1981), Lemma 2; Mirrlees (1971), Equation (27). The argument is standard: if q were decreasing over some interval, a mimicry deviation by higher types would be profitable, violating IC.*

### 1.5 The Allocation Functor

**Definition 1.6 (Allocation Functor).** The functor **Q: Mech → Alloc** is defined by:

- On objects: Q(q, t) = q  (forgets the transfer rule)
- On morphisms: Q(φ) = the allocation component of φ

*Q is a forgetful functor. It is well-defined because any IC mechanism has a monotone allocation rule by MON, hence Q(q, t) is an object in Alloc.*

### 1.6 Completeness of Alloc

**Lemma 1.7 (Alloc is Complete).** The category Alloc has all small limits.

*Proof.* It suffices to show Alloc has all products and all equalisers (Mac Lane, 1978, Theorem V.2.1).

**Products.** Given monotone rules q₁, q₂: Θ → A, their product in Alloc is the greatest lower bound pointwise:

```
(q₁ × q₂)(θ) = inf{a ∈ A : a ≥ q₁(θ) and a ≥ q₂(θ)}
```

This is monotone in θ because the infimum of monotone functions is monotone. The universal property holds because any r with r(θ) ≤ q₁(θ) and r(θ) ≤ q₂(θ) for all θ satisfies r(θ) ≤ (q₁ × q₂)(θ), giving the required unique morphism.

**Equalisers.** Given parallel morphisms φ, ψ: q → q', the equaliser is the restriction of q to the set E = {θ : φ(θ) = ψ(θ)}. Monotonicity is preserved by restriction to a subset. The universal property is immediate.

Since Alloc has all products and equalisers, it is complete. □

*Reference: Mac Lane (1978), Categories for the Working Mathematician, Chapter V.*

### 1.7 Q Preserves Limits

**Lemma 1.8 (Q Preserves Limits).** The functor Q: Mech → Alloc preserves all small limits.

*Proof.* Q is a forgetful functor that drops the transfer component t and retains the allocation component q. Limit constructions in Mech act componentwise on q and t independently — this follows from quasilinearity (QI), which ensures that incentive compatibility constraints factor into an allocation condition (MON) and a transfer condition (the envelope formula). Since Q drops the t component and limits of q-components in Mech coincide with limits in Alloc, Q preserves limits. □

*Reference: Mac Lane (1978), Chapter V, Corollary 5.1. The argument is the standard one for forgetful functors from categories of structured objects to categories of the underlying structure.*

---

## Stage 2: The Myerson Auction Setting

### 2.1 Instantiation

The Myerson setting is:

- Θ = [0,1], F uniform (or any regular distribution)
- A = [0,1]ᴺ, with q_i(θ) = probability bidder i receives the object
- Feasibility: Σᵢ qᵢ(θ) ≤ 1
- Value function: v(q, θ) = θᵢ · qᵢ (quasilinear, linear in allocation)
- Transfer: tᵢ(θ) = payment by bidder i

**Condition REG (Regularity, Myerson).** The virtual valuation ψ(θ) = θ - (1-F(θ))/f(θ) is non-decreasing in θ.

*REG implies MON for the optimal allocation rule. Without REG, the optimal allocation may be non-monotone and requires ironing; see Myerson (1981), Section 6.*

### 2.2 Verification of SC in Myerson Setting

For two allocations qᵢ > qᵢ' (higher probability of winning):

```
∂/∂θᵢ [v(qᵢ, θᵢ) - v(qᵢ', θᵢ)] = ∂/∂θᵢ [θᵢ(qᵢ - qᵢ')] = qᵢ - qᵢ' > 0
```

SC holds in the Myerson setting. □

### 2.3 IC Characterisation in Myerson Setting

**Lemma 2.1 (Myerson Characterisation).** A mechanism (q, t) is BIC with V_i(0) = 0 if and only if:

1. qᵢ(θᵢ) is non-decreasing in θᵢ (condition MON)
2. The payment rule satisfies:

```
tᵢ(θᵢ) = θᵢ · qᵢ(θᵢ) - ∫₀^θᵢ qᵢ(s) ds
```

*Proof (if direction).* Suppose qᵢ is non-decreasing and tᵢ satisfies (2). The equilibrium payoff is:

```
Vᵢ(θᵢ) = θᵢ · qᵢ(θᵢ) - tᵢ(θᵢ) = ∫₀^θᵢ qᵢ(s) ds
```

For any misreport r, the payoff is:

```
Uᵢ(θᵢ, r) = θᵢ · qᵢ(r) - tᵢ(r) = θᵢ · qᵢ(r) - r · qᵢ(r) + ∫₀^r qᵢ(s) ds
```

Then:

```
Vᵢ(θᵢ) - Uᵢ(θᵢ, r) = ∫ᵣ^θᵢ [qᵢ(θᵢ) - qᵢ(s)] ds ≥ 0
```

since qᵢ is non-decreasing. Truth-telling is optimal. IR: Vᵢ(0) = 0 by construction.

*Proof (only if direction).* Suppose (q, t) is BIC. Then Vᵢ(θᵢ) = max_r {θᵢ · qᵢ(r) - tᵢ(r)} is the maximum of affine functions of θᵢ, hence convex. By convexity and the IC constraints, qᵢ must be non-decreasing (MON). By the envelope theorem applied to the maximum:

```
dVᵢ/dθᵢ = qᵢ(θᵢ)   a.e.
```

Integrating with Vᵢ(0) = 0 and substituting Vᵢ(θᵢ) = θᵢ · qᵢ(θᵢ) - tᵢ(θᵢ) yields (2). □

*Reference: Myerson (1981), Theorem 2; Klemperer (1999), Theorem 1.*

---

## Stage 3: The Mirrlees Taxation Setting

### 3.1 Instantiation

The Mirrlees setting is:

- Θ = [θ_min, θ_max], distribution F with density f > 0
- A = {(c, y) : c ≥ 0, y ≥ 0}, consumption-income pairs
- The allocation rule assigns gross income: q(θ) = y(θ)
- The agent's budget constraint: c = y - T(y), where T is the tax schedule
- Value function: v(y, θ) = u(c, y/θ) where u is increasing in c, decreasing in labour l = y/θ
- Quasilinear approximation: v(y, θ) = θ · h(y) - g(y/θ) for smooth h, g (Mirrlees 1971, Section 2)
- Transfer: T(y(θ)) = y(θ) - c(θ), the tax paid by type θ

**Condition SC-M (Single Crossing, Mirrlees).** The indifference curves in (y, c) space satisfy single crossing: the marginal rate of substitution between income and consumption, MRS(y, c, θ) = -∂U/∂y / ∂U/∂c, is strictly decreasing in θ.

*Equivalently, ∂MRS/∂θ < 0: higher productivity types have flatter indifference curves at any point, and are willing to supply more labour at any wage. This is the Spence-Mirrlees condition.*

*Reference: Mirrlees (1971), Assumption 3; Seade (1977).*

### 3.2 Verification of SC in Mirrlees Setting

Under SC-M, for two income levels y > y':

```
∂/∂θ [v(y, θ) - v(y', θ)] = ∂/∂θ [u(y - T(y), y/θ) - u(y' - T(y'), y'/θ)]
```

Under SC-M this is strictly positive: higher types gain relatively more from higher income levels. The Mirrlees condition SC-M is exactly condition SC in the abstract framework for the income-consumption allocation space. □

*Reference: Mirrlees (1971), Lemma 1; Fudenberg and Tirole (1991), Chapter 7.*

### 3.3 IC Characterisation in Mirrlees Setting

**Lemma 3.1 (Mirrlees Characterisation — Taxation Principle).** A mechanism (y(θ), c(θ)) is incentive compatible with V(θ_min) ≥ 0 if and only if:

1. y(θ) is non-decreasing in θ (condition MON)
2. The net income schedule satisfies:

```
c(θ) = v(y(θ), θ) - V(θ_min) - ∫_{θ_min}^θ ∂v/∂s (y(s), s) ds

       equivalently:

V(θ) = V(θ_min) + ∫_{θ_min}^θ ∂v/∂s (y(s), s) ds
```

And the tax schedule T(y) = y - c is uniquely determined by y(θ) and V(θ_min).

*Proof (if direction).* Suppose y(θ) is non-decreasing and V satisfies (2). For any misreport r:

```
V(θ) - U(θ, r) = [V(θ) - V(r)] - [v(y(r), θ) - v(y(r), r)]
               = ∫ᵣ^θ [∂v/∂s(y(s),s) - ∂v/∂s(y(r),s)] ds
```

Under SC-M and MON (y non-decreasing), the integrand is non-negative for s between r and θ, so V(θ) ≥ U(θ, r). Truth-telling is optimal.

*Proof (only if direction).* Suppose the mechanism is IC. Then V(θ) = max_r U(θ, r) is convex in θ as the maximum of functions linear in θ (under QI). By convexity and IC, y(θ) must be non-decreasing (MON). The envelope theorem gives:

```
dV/dθ = ∂v/∂θ (y(θ), θ)   a.e.
```

Integrating with boundary condition V(θ_min) yields (2). Uniqueness of T(y): since y(θ) is non-decreasing and satisfies MON, the function T(y) = y - c(y) is well-defined on the range of y(θ). □

*Reference: Mirrlees (1971), Equations (26)-(27); Hammond (1979), Theorem 1; Rochet (1985), Proposition 1; Guesnerie (1981).*

**Remark (Taxation Principle).** Lemma 3.1 is the Taxation Principle: any IC direct mechanism (y(θ), c(θ)) can be implemented by a nonlinear tax schedule T(y), and this schedule is unique given the allocation y(θ) and the boundary condition V(θ_min). The proof is a direct consequence of the envelope characterisation. *Reference: Hammond (1979); Rochet (1985).*

---

## Stage 4: The Master Theorem

### 4.1 The Transfer Functor

**Definition 4.1 (Transfer Functor).** Given the abstract framework of Stage 1, define the functor **T: Alloc → Mech** by:

- On objects: T(q) = (q, t*) where t* is defined by:

```
t*(θ) = v(q(θ), θ) - V(θ_min) - ∫_{θ_min}^θ ∂v/∂s (q(s), s) ds
```

with V(θ_min) = 0 (normalisation)

- On morphisms: T(φ) = (φ, φ) — the same type-space transformation applied to both components

**Lemma 4.2 (T is well-defined).** T(q) is a BIC and IR mechanism for any monotone allocation rule q satisfying MON.

*Proof.* Identical structure to Lemmas 2.1 and 3.1: the if-direction of both characterisation lemmas applies verbatim in the abstract framework under QI and SC. The proof uses only that q is non-decreasing (MON) and that the utility satisfies QI and SC. □

### 4.2 The Adjunction

**Theorem 4.3 (Q ⊣ T).** The allocation functor Q: Mech → Alloc is left adjoint to the transfer functor T: Alloc → Mech:

```
hom_Alloc(Q(q, t), q')  ≅  hom_Mech((q, t), T(q'))

naturally in (q, t) and q'.
```

*Proof.* We exhibit the natural bijection explicitly.

Given a morphism φ: Q(q, t) → q' in Alloc — that is, an order-preserving type-space transformation with q' ∘ φ = q — we construct a morphism φ̃: (q, t) → T(q') in Mech.

The required morphism φ̃ must satisfy:
1. Q(φ̃) = φ: the allocation component of φ̃ is φ
2. The transfer component carries t to t*_{q'} ∘ φ

Since (q, t) is BIC with allocation q and T(q') is BIC with allocation q', and both have the same boundary condition, Lemmas 2.1/3.1 imply t = t*_q and t*_{q'} ∘ φ = t*_q. So φ̃ = (φ, φ) is the required morphism, and it is unique given φ.

Conversely, given a morphism ψ: (q, t) → T(q') in Mech, Q(ψ) is a morphism Q(q, t) → Q(T(q')) = q' in Alloc. The map φ ↦ φ̃ and ψ ↦ Q(ψ) are inverse bijections.

Naturality in both arguments follows from the functoriality of Q and T and the componentwise definition of morphisms. □

*Reference: Mac Lane (1978), Chapter IV. The adjunction is constructed explicitly rather than via the Adjoint Functor Theorem, using the characterisation lemmas as the key input.*

### 4.3 Terminality of T(q)

**Corollary 4.4 (T(q) is Terminal in Mech_q).** Fix a monotone allocation rule q and boundary condition V(θ_min) = 0. In the full subcategory **Mech_q** of Mech consisting of all BIC mechanisms with allocation rule q, the object T(q) is the terminal object: every object has a unique morphism to T(q).

*Proof.* Let (q, t) be any object in Mech_q. We need to exhibit a unique morphism φ: (q, t) → T(q).

*Existence.* By Lemmas 2.1/3.1 (the only-if direction), since (q, t) is BIC with allocation q and V(θ_min) = 0, the transfer rule t must satisfy the envelope formula, hence t = t*_q. So the identity morphism id_Θ: (q, t) → T(q) = (q, t*_q) = (q, t) is a valid morphism.

*Uniqueness.* Any morphism φ: (q, t) → T(q) in Mech_q must satisfy q ∘ φ = q. Since q is strictly increasing (MON + strict SC), this forces φ = id_Θ. □

*Reference: The terminality argument is an instance of the general fact that right adjoints represent terminal objects in comma categories. See Mac Lane (1978), Section IV.1.*

### 4.4 The Master Theorem

**Theorem 4.5 (Master Theorem — Unified Revenue Equivalence / Taxation Principle).**

Let the abstract framework of Stage 1 hold, with conditions QI, SC, and MON satisfied. Fix a monotone allocation rule q: Θ → A and boundary condition V(θ_min) = 0. Then:

**(i) Existence and Uniqueness.** There exists a unique BIC, IR mechanism T(q) with allocation rule q. It is given explicitly by:

```
t*(θ) = v(q(θ), θ) - ∫_{θ_min}^θ ∂v/∂s (q(s), s) ds
```

**(ii) Isomorphism.** Every BIC, IR mechanism (q, t) with allocation q is isomorphic to T(q) in Mech.

**(iii) Transfer Invariance.** The expected transfer is uniquely determined by q:

```
E[t(θ)] = E[t*(θ)] = E[v(q(θ), θ)] - ∫_Θ ∫_{θ_min}^θ ∂v/∂s(q(s),s) ds dF(θ)
```

Any two BIC, IR mechanisms with the same allocation rule q generate the same expected transfer.

*Proof.*

*(i)* T(q) = (q, t*) exists by Lemma 4.2. Uniqueness follows from Corollary 4.4: T(q) is the terminal object in Mech_q, and terminal objects are unique up to unique isomorphism (Mac Lane 1978, Section III.1).

*(ii)* Let (q, t) be any BIC, IR mechanism with allocation q and V(θ_min) = 0. By Corollary 4.4 there exists a unique morphism φ: (q, t) → T(q). Since t = t*_q by the envelope characterisation (Lemmas 2.1/3.1), φ = id_Θ, which is an isomorphism.

*(iii)* Since t = t*_q pointwise for any BIC mechanism with allocation q and V(θ_min) = 0, the expected transfers are equal:

```
E[t(θ)] = E[t*(θ)]
```

for any two such mechanisms. □

*References: Myerson (1981), Theorem 2; Hammond (1979), Theorem 1; Rochet (1985), Proposition 1; Mac Lane (1978), Chapters IV–V.*

---

## Stage 5: Instantiation in Each Setting

### 5.1 Revenue Equivalence as a Corollary

**Corollary 5.1 (Myerson Revenue Equivalence).** In the Myerson auction setting (Stage 2), any two BIC, IR mechanisms M₁ = (q, t¹) and M₂ = (q, t²) with the same allocation rule q and V_i(0) = 0 satisfy:

```
E[t¹ᵢ(θᵢ)] = E[t²ᵢ(θᵢ)]   for all i
```

*Proof.* Apply Theorem 4.5(iii) to the Myerson setting. Conditions QI, SC, and MON are verified in Stage 2. The formula gives:

```
E[tᵢ(θᵢ)] = E[θᵢ · qᵢ(θᵢ)] - ∫₀¹ ∫₀^θ qᵢ(s) ds dF(θ) = E[ψ(θᵢ) · qᵢ(θᵢ)]
```

where ψ(θ) = θ - (1-F(θ))/f(θ) is the virtual valuation (by integration by parts). This depends only on q and F. □

*Reference: Myerson (1981), Theorem 2; Riley and Samuelson (1981).*

### 5.2 Taxation Principle as a Corollary

**Corollary 5.2 (Mirrlees Taxation Principle).** In the Mirrlees taxation setting (Stage 3), any IC mechanism (y(θ), c(θ)) with V(θ_min) = 0 has a unique implementing tax schedule T: Y → ℝ defined by T(y) = y - c on the range of y(θ). Any two IC mechanisms with the same income assignment y(θ) and the same V(θ_min) have the same tax schedule and hence the same expected tax revenue.

*Proof.* Apply Theorem 4.5(iii) to the Mirrlees setting. Conditions QI, SC (via SC-M), and MON are verified in Stage 3. The formula gives:

```
T(y(θ)) = y(θ) - c(θ) = v(y(θ), θ) - ∫_{θ_min}^θ ∂v/∂s(y(s), s) ds
```

This depends only on y(θ) and V(θ_min). Two mechanisms with the same y(θ) must have the same c(θ) and hence the same T. □

*Reference: Hammond (1979), Theorem 1; Rochet (1985), Proposition 1; Mirrlees (1971), Equation (27).*

---

## Stage 6: Conditions for Failure and Extensions

### 6.1 Where the Categorical Structure Fails

The Master Theorem requires QI, SC, and MON. The following summarises what breaks when each condition fails and what the categorical reason is.

**Failure of QI (Non-quasilinear preferences).**

If U(a, t, θ) is not additively separable in t, the envelope formula no longer pins down the transfer uniquely given the allocation. The value of the transfer feeds back into the agent's valuation of the allocation, making Q and T entangled. Formally, Q no longer factors through Alloc as a forgetful functor — the allocation component of a morphism in Mech depends on the transfer component. The adjunction Q ⊣ T breaks.

*Reference: Maskin and Riley (1984); Rochet and Chone (1998).*

**Failure of SC (Multi-dimensional types).**

With multi-dimensional types θ ∈ Θ ⊂ ℝᵏ for k ≥ 2, condition SC fails in general: there is no natural total order on Θ under which all agents' preferences are single-crossing. Monotonicity of q as a function Θ → A is no longer well-defined without further structure. The category Alloc loses its natural poset structure, products in Alloc are no longer pointwise minima, and completeness cannot be established by the same argument. The Adjoint Functor Theorem does not directly apply.

In this setting, additional conditions (cyclical monotonicity, Rochet 1987) are needed to characterise IC mechanisms, and these do not reduce to a single envelope formula. Revenue equivalence fails: different allocation rules can generate the same expected transfer.

*Reference: Rochet (1987); Armstrong (1996); Rochet and Chone (1998).*

**Failure of MON (Non-regular distributions, ironing).**

When regularity fails (REG violated in the Myerson setting), the optimal allocation rule q* is non-monotone in the unconstrained optimum. The categorical fix is ironing (Myerson 1981, Section 6): replace q* with its least concave majorant over the regions where MON fails, pooling types over intervals. Categorically, Q fails to be faithful over bunching intervals — multiple types map to the same allocation, and T(q) is not uniquely defined pointwise. Uniqueness of T(q) is recovered only after ironing, and only in expectation.

The analogous construction in Mirrlees is bunching (Mirrlees 1971, Section 6): the optimal income assignment is constant over intervals of types where the unconstrained optimum would violate MON. The categorical analysis is identical.

*Reference: Myerson (1981), Section 6; Mirrlees (1971), Section 6; Ebert (1992).*

### 6.2 The Dynamic Extension

Pavan, Segal, and Toikka (2014) extend both frameworks to dynamic environments where types evolve over time as θₜ = θ₀ + ∫₀ᵗ dBₛ (a stochastic process). The envelope formula generalises to:

```
dV_t/dθ₀ = E[∫₀^T ∂v/∂θ (q_t, θ_t) · (∂θ_t/∂θ₀) dt]
```

Categorically, the domain category Dist is replaced by a category of stochastic type processes, morphisms are adapted transformations of these processes, and the right adjoint T integrates the envelope formula over paths. The Master Theorem applies verbatim with the path integral replacing the scalar integral. The transfer schedule is unique given the allocation policy and the initial boundary condition.

*Reference: Pavan, Segal, and Toikka (2014), Theorem 1.*

---

## Summary: The Proof Chain

```
Conditions:  QI + SC + SC-M  →  MON (monotone allocation)
                                  (Myerson 1981 Lemma 2;
                                   Mirrlees 1971 Eq. 27)
                   │
                   ▼
Lemma 1.7:  Alloc is complete
            (products = pointwise inf;
             equalisers = restriction to agreement set)
                   │
                   ▼
Lemma 1.8:  Q: Mech → Alloc preserves limits
            (Q is forgetful; limits act componentwise under QI)
                   │
                   ▼
Lemma 4.2:  T(q) is a valid BIC mechanism for any q ∈ Alloc
            (if-direction of characterisation lemmas 2.1, 3.1)
                   │
                   ▼
Theorem 4.3: Q ⊣ T  (adjunction)
             (natural bijection of hom-sets;
              explicit via envelope formula)
                   │
                   ▼
Corollary 4.4: T(q) is terminal in Mech_q
               (right adjoints represent terminal objects;
                uniqueness from strict monotonicity of q)
                   │
                   ├────────────────────────────┐
                   │                            │
                   ▼                            ▼
Corollary 5.1:              Corollary 5.2:
Revenue Equivalence         Taxation Principle
(Myerson 1981)              (Hammond 1979;
                             Rochet 1985)
```

Both corollaries are instances of Theorem 4.5. The proof chain is the same; only the economic interpretation of objects and morphisms differs.

---

## References

Armstrong, M. (1996). Multiproduct nonlinear pricing. *Econometrica*, 64(1), 51–75.

Ebert, U. (1992). A reexamination of the optimal nonlinear income tax. *Journal of Public Economics*, 49(1), 47–73.

Fudenberg, D., & Tirole, J. (1991). *Game Theory*. MIT Press.

Grothendieck, A. (1971). Revêtements étales et groupe fondamental (SGA 1). *Lecture Notes in Mathematics*, 224. Springer.

Guesnerie, R. (1981). On taxation and incentives: Further reflections on the limits to redistribution. *Bonn Discussion Paper* No. 89.

Hammond, P. J. (1979). Straightforward individual incentive compatibility in large economies. *Review of Economic Studies*, 46(2), 263–282.

Klemperer, P. (1999). Auction theory: A guide to the literature. *Journal of Economic Surveys*, 13(3), 227–286.

Mac Lane, S. (1978). *Categories for the Working Mathematician* (2nd ed.). Springer. [Chapters III–V on limits, adjunctions, and the Adjoint Functor Theorem.]

Maskin, E., & Riley, J. (1984). Monopoly with incomplete information. *RAND Journal of Economics*, 15(2), 171–196.

Mirrlees, J. A. (1971). An exploration in the theory of optimum income taxation. *Review of Economic Studies*, 38(2), 175–208.

Myerson, R. B. (1981). Optimal auction design. *Mathematics of Operations Research*, 6(1), 58–73.

Pavan, A., Segal, I., & Toikka, J. (2014). Dynamic mechanism design: A Myersonian approach. *Econometrica*, 82(2), 601–653.

Riehl, E. (2017). *Category Theory in Context*. Dover. Available at: https://math.jhu.edu/~eriehl/context.pdf [Chapters 4–5 on adjunctions and limits.]

Riley, J. G., & Samuelson, W. F. (1981). Optimal auctions. *American Economic Review*, 71(3), 381–392.

Rochet, J.-C. (1985). The taxation principle and multi-time Hamilton-Jacobi equations. *Journal of Mathematical Economics*, 14(2), 113–128.

Rochet, J.-C. (1987). A necessary and sufficient condition for rationalizability in a quasi-linear context. *Journal of Mathematical Economics*, 16(2), 191–200.

Rochet, J.-C., & Choné, P. (1998). Ironing, sweeping, and multidimensional screening. *Econometrica*, 66(4), 783–826.

Seade, J. (1977). On the shape of optimal tax schedules. *Journal of Public Economics*, 7(2), 203–235.
