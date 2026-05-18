

# Monotonicity in Optimal Auctions and Taxation: Formal Proofs for Lean 4

This document extracts and structures the proofs of **monotonicity** in two foundational economic models:
1. **Optimal Auctions (Myerson 1981)**: Monotonicity of the probability of winning in the bidder's type.
2. **Optimal Income Taxation (Mirrlees Model)**: Monotonicity of consumption and income in the agent's type.

The proofs are organized for implementation in **Lean 4**, with clear assumptions and logical steps.



## 1. Monotonicity in Optimal Auctions (Myerson 1981)

### Context
Myerson (1981) proves that in optimal auctions, the probability of a bidder winning the object is **monotonically increasing** in their type (willingness to pay). This result is derived under the **Revelation Principle** and **incentive compatibility constraints**.

---

### Key Assumptions
1. **Independent Private Values (IPV)**:
   - Bidders' value estimates \( t_i \) are stochastically independent.
   - Each \( t_i \) is drawn from a continuous distribution \( F_i \) with density \( f_i > 0 \) on \([a_i, b_i]\).

2. **Risk Neutrality**:
   - Bidders and the seller are risk-neutral.

3. **Regularity Condition**:
   - The function \( c_i(t_i) = t_i - e_i(t_i) - \frac{1 - F_i(t_i)}{f_i(t_i)} \) is **strictly increasing** in \( t_i \).
   - Here, \( e_i(t_i) \) captures revision effects (e.g., quality uncertainty).

4. **Incentive Compatibility (IC)**:
   - Bidders report their types truthfully in equilibrium.
   - Formally: \( U_i(p, x, t_i) \geq U_i(p, x, s_i) + (t_i - s_i) Q_i(p, s_i) \) for all \( s_i < t_i \).

5. **Individual Rationality (IR)**:
   - Bidders' expected utility is non-negative: \( U_i(p, x, t_i) \geq 0 \).

---

### Monotonicity of Winning Probability
**Statement**:
For any feasible direct revelation mechanism \((p, x)\), the conditional probability \( Q_i(p, t_i) \) that bidder \( i \) wins the object, given their type \( t_i \), is **strictly increasing** in \( t_i \).

---

### Proof (from Lemma 2, §4 of Myerson 1981)
1. **Incentive Compatibility (IC) Constraint**:
   For any \( s_i < t_i \), the IC constraint (4.6) requires:
   \[
   U_i(p, x, t_i) \geq U_i(p, x, s_i) + (t_i - s_i) Q_i(p, s_i).
   \]
   Symmetrically, swapping \( s_i \) and \( t_i \):
   \[
   U_i(p, x, s_i) \geq U_i(p, x, t_i) + (s_i - t_i) Q_i(p, t_i).
   \]
   Combining these inequalities:
   \[
   (t_i - s_i) Q_i(p, s_i) \leq U_i(p, x, t_i) - U_i(p, x, s_i) \leq (t_i - s_i) Q_i(p, t_i).
   \]
   For \( s_i < t_i \), this simplifies to:
   \[
   Q_i(p, s_i) \leq Q_i(p, t_i).
   \]
   Thus, \( Q_i(p, \cdot) \) is **non-decreasing** in \( t_i \).

2. **Strict Monotonicity under Regularity**:
   If the problem is **regular** (i.e., \( c_i(t_i) \) is strictly increasing), then the optimal allocation \( p \) assigns the object to the bidder with the highest \( c_i(t_i) \). Since \( c_i \) is strictly increasing, \( p_i(t) > 0 \) implies \( c_i(t_i) \) is maximal, and thus \( Q_i(p, t_i) \) is **strictly increasing** in \( t_i \).

---

### Lean 4 Structure
```lean4
-- Assumptions
variable {n : ℕ} {i : Fin n}  -- n bidders, indexed by Fin n
variable (F : Fin n → ℝ → ℝ)  -- CDFs for each bidder
variable (f : Fin n → ℝ → ℝ)  -- PDFs for each bidder
variable (a b : Fin n → ℝ)   -- Lower/upper bounds for types
variable (p : (Fin n → ℝ) → Fin n → ℝ)  -- Allocation function (probability of winning)
variable (x : (Fin n → ℝ) → Fin n → ℝ)  -- Payment function

-- Regularity condition: c_i(t_i) is strictly increasing
def c (i : Fin n) (t_i : ℝ) : ℝ := t_i - (1 - F i t_i) / (f i t_i)
axiom regularity : ∀ i t_i s_i, a i ≤ s_i → s_i < t_i → t_i ≤ b i → c i s_i < c i t_i

-- Monotonicity of Q_i (conditional probability of winning)
def Q (i : Fin n) (p : (Fin n → ℝ) → Fin n → ℝ) (t_i : ℝ) : ℝ :=
  ∫ t_{-i} in setOf (fun t => ∀ j ≠ i, a j ≤ t j ∧ t j ≤ b j), p (Function.update t_i i t_{-i}) i * (∏ j ≠ i, f j (t_{-i} j))

-- Theorem: Q_i is strictly increasing in t_i under regularity
theorem monotonicity_Q (i : Fin n) (p : (Fin n → ℝ) → Fin n → ℝ) (h_regular : regularity)
    (h_IC : IncentiveCompatible p x) (h_IR : IndividualRational p x) :
    StrictMono (Q i p) := by
  -- Proof steps:
  -- 1. Use IC to show Q_i is non-decreasing (from Lemma 2).
  -- 2. Use regularity to show strict monotonicity.
  sorry
```

---

---

## 2. Monotonicity in Mirrlees Taxation (Optimal Income Taxation)

### Context
In the **Mirrlees model** of optimal income taxation, the **Spence-Mirrlees condition** (single-crossing) and **incentive compatibility** imply that optimal allocations \( c(n) \) (consumption) and \( z(n) \) (income) are **monotonically increasing** in the agent’s type \( n \) (ability).

---

### Key Assumptions
1. **Utility Function**:
   - \( u(c, l) = c - v(l) \), where \( v \) is strictly convex (\( v'' \geq 0 \)) and increasing (\( v' > 0 \)).

2. **Single-Crossing Condition (Spence-Mirrlees)**:
   The marginal rate of substitution \( \text{MRS}_{c,z} = \frac{v'(l)}{n} \) is **decreasing** in \( n \).
   Formally:
   \[
   \frac{\partial}{\partial n} \left( \frac{v'(z(n)/n)}{n} \right) \leq 0.
   \]

3. **Incentive Compatibility (IC)**:
   Agents truthfully report their type \( n \), so the allocation must satisfy:
   \[
   c(n) - v\left(\frac{z(n)}{n}\right) \geq c(n') - v\left(\frac{z(n')}{n}\right) \quad \forall n, n'.
   \]

4. **Local IC (First-Order Approach)**:
   The derivative of utility with respect to \( n \) is:
   \[
   \frac{du(n)}{dn} = \frac{z(n)}{n^2} v'\left(\frac{z(n)}{n}\right) > 0.
   \]
   This implies \( u(n) \) is strictly increasing in \( n \).

---

### Monotonicity of Allocations
**Statement**:
Under the Spence-Mirrlees condition and incentive compatibility, the optimal consumption \( c(n) \) and income \( z(n) \) are **strictly increasing** in \( n \).

---

### Proof (from §1 of *Economics 2450A: Public Economics*)
1. **Single-Crossing + IC ⇒ Monotonicity**:
   - The Spence-Mirrlees condition ensures that the indifference curves of higher-type agents are "flatter" in the \( (c, z) \) space.
   - Combined with IC, this implies that higher types must receive weakly higher consumption and income. Strict convexity of \( v \) ensures **strict monotonicity**.

2. **Formal Argument**:
   - Suppose \( n_1 < n_2 \). If \( z(n_1) \geq z(n_2) \), then by single-crossing, agent \( n_2 \) would prefer \( (c(n_1), z(n_1)) \) over \( (c(n_2), z(n_2)) \), violating IC.
   - Thus, \( z(n) \) must be strictly increasing in \( n \).
   - From the budget constraint \( c(n) = z(n) - T(z(n)) \), and since \( T \) is designed to preserve incentives, \( c(n) \) is also strictly increasing.

---
### Lean 4 Structure
```lean4
-- Assumptions
variable (v : ℝ → ℝ)  -- Disutility of labor
variable (u : ℝ → ℝ → ℝ)  -- Utility function: u(c, l) = c - v(l)
variable (n : ℝ)      -- Type (ability)
variable (c z : ℝ → ℝ)  -- Consumption and income as functions of type

-- Spence-Mirrlees condition: MRS is decreasing in n
axiom spence_mirrlees : ∀ n1 n2 l, n1 < n2 → (v' l / n1) > (v' l / n2)

-- Incentive Compatibility (local)
axiom local_IC : ∀ n, deriv (fun n => u (c n) (z n / n)) n = (z n / n^2) * v' (z n / n)

-- Monotonicity of z(n) and c(n)
theorem monotonicity_allocations (h_v_convex : Convex ℝ v (Set.Ici 0))
    (h_v_increasing : StrictMonoOn v' (Set.Ici 0))
    (h_spence_mirrlees : spence_mirrlees) (h_IC : local_IC) :
    StrictMono z ∧ StrictMono c := by
  -- Proof steps:
  -- 1. Use Spence-Mirrlees + IC to show z(n) is strictly increasing.
  -- 2. Use budget constraint to show c(n) is strictly increasing.
  sorry
```

---
---
## Summary of Assumptions for Lean 4

| **Context**               | **Assumptions**                                                                                     | **Monotonicity Result**                          |
|---------------------------|---------------------------------------------------------------------------------------------------|-------------------------------------------------|
| **Myerson (Auctions)**    | IPV, risk neutrality, regularity (\( c_i \) strictly increasing), IC, IR                          | \( Q_i(p, t_i) \) strictly increasing in \( t_i \) |
| **Mirrlees (Taxation)**  | \( u(c, l) = c - v(l) \), \( v \) convex, Spence-Mirrlees condition, local IC                     | \( c(n) \), \( z(n) \) strictly increasing in \( n \) |

---
## Implementation Notes for Lean 4
1. **For Myerson’s Auction Model**:
   - Define `Q_i` as an integral over other bidders’ types.
   - Use the `IncentiveCompatible` axiom to derive non-decreasing \( Q_i \).
   - Use the `regularity` axiom to strengthen to strict monotonicity.

2. **For Mirrlees Taxation**:
   - Define the Spence-Mirrlees condition as a derivative inequality.
   - Use `Convex` and `StrictMonoOn` for \( v \).
   - Prove \( z(n) \) is strictly increasing first, then \( c(n) \).

3. **Required Lean Libraries**:
   - `Mathlib.Analysis.Convex` (for convexity of \( v \))
   - `Mathlib.MeasureTheory.Integral` (for \( Q_i \) in auctions)
   - `Mathlib.Order.Monotone` (for monotonicity proofs)

---
## References
- Myerson, R. B. (1981). *Optimal Auction Design*. Mathematics of Operations Research, 6(1), 58–73.
- Mirrlees, J. A. (1971). *An Exploration in the Theory of Optimum Income Taxation*. Review of Economic Studies, 38(2), 175–208.
- Stantcheva, S. (2024). *Economics 2450A: Public Economics, Section 3-4: Mirrlees Taxation*. Harvard University.
```

---
