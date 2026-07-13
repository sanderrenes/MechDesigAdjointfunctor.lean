# Decisions

Append-only. One entry per decision that a reader of the code could not reconstruct from
the code itself. Newest last. Record the **alternative rejected** and **why** — a decision
without its discarded alternative is just a description.

---

## D1 — Order **Mech**'s morphisms by *surplus*, not by *transfer*
**Date:** 2026-07-13 · **Branch:** `surplus-order` · **Commit:** `d064a7b`

`MechHom` carries `hSurp : ∀ θ ≥ θ_min, V_m θ ≤ V_m' θ` where `V(θ) = v(q θ, θ) − t θ`.
It carries **no** transfer condition.

**Rejected: order by the transfer** (`hTransf : m.t θ ≤ m'.t θ`), which is what the original
formulation used. That field makes `T : Alloc → Mech` **not a functor**: `t*(r) ≤ t*(r')`
does not follow from `r.q ≤ r'.q` for general `v`. It requires *convexity of `v` in the
allocation*, and `mirrleesValue y θ = θ·h(y) − g(y/θ)` is **concave** in `y` in the standard
regime (`h` concave, `g` convex). A transfer order therefore breaks the Mirrlees
instantiation and destroys the unification claim, which is the point of the paper. This was
the source of the long-standing `sorry` on `T.map`.

**Why surplus works:** quasilinearity. The numeraire enters utility linearly, so `t` is
recoverable from `(q, V)` as `t θ = v(q θ) θ − V θ` — no information about transfers is lost.
But `V_{T(r)}(θ) = ∫ D_r` collapses to the bare envelope integral, so `V_{T(r)} ≤ V_{T(r')}`
reduces to a pointwise inequality between integrands, which is exactly **single crossing** —
an assumption both settings already make. See `Tmech_surplus_mono`.

**Also rejected: require convexity of `v` in the allocation.** It would restore the transfer
order and give a genuine adjunction — for Myerson only. Mirrlees fails it. Buying the
categorical story at the cost of the unification is a bad trade.

---

## D2 — Drop `h_spread` from `AllocHom` and `MechHom`
**Date:** 2026-07-13 · **Commit:** `d064a7b`

Spread monotonicity (`Monotone (fun θ => r'.q θ − r.q θ)`) existed *only* to prop up the
transfer-ordered `T.map`. Under D1, `T.map` follows from single crossing alone and never
uses it. Dropping it leaves **Alloc** as the plain pointwise order on monotone allocation
rules, which is what Definition 1.5 always intended.

---

## D3 — The adjunction is `T ⊣ Q`, not `Q ⊣ T`; `T(r)` is **initial**, not terminal
**Date:** 2026-07-13 · **Commit:** `d064a7b`

Under the surplus order, IR (`V(θ_min) ≥ 0`) makes `T(r)` the *minimal-rent* mechanism in
its fiber, so arrows run **out** of it. `T` is the left adjoint; `T` preserves colimits and
`Q` preserves limits. `T_terminal` became `T_initial`.

**Rejected: keep `Q ⊣ T` by normalising `IsIR` to `V(θ_min) = 0`.** That collapses each
fiber to a single object and makes `Mech ≃ Alloc` outright — see D4.

---

## D4 — `IsIR` stays an **inequality** (`V(θ_min) ≥ 0`); the normalisation lives in `Mech₀`
**Date:** 2026-07-13 · **Commit:** `095fccb`

**Rejected: define `IsIR` as `V(θ_min) = 0`.** It would give the cleaner headline
(`Mech ≃ Alloc` directly) but a *weaker theorem*: revenue equivalence would become true by
construction of the objects, migrating the content into the well-definedness of `Mech` rather
than being a claim proved about it.

Keeping the inequality means the fiber over an allocation is a genuine one-parameter family
indexed by boundary rent (`surplus_split`), which is what makes Move 1 substantive and Move 3
a real restriction. The docstring previously *described* the normalisation while the
definition asserted the inequality; corrected in `095fccb`.

---

## D5 — The boundary condition is **equal rent**, not **zero rent**
**Date:** 2026-07-13 · **Commit:** `d064a7b`

`masterTheorem_transferInvariance` requires `V₁(θ_min) = V₂(θ_min)` (`hV₀`), not
`V(θ_min) = 0`. `envelope_transfer_shift` (`m.t θ = t*(θ) − V_m(θ_min)`) makes this exact:
revenue equivalence needs *equal* rent, never *zero* rent.

This matches `mirrlees_unique_from_IC`, which already quantified over a common `V₀`. The
abstract layer had been proving something **narrower than its own instantiation**.

Side effect: transfer invariance uses neither single crossing nor IR — only IC's envelope
condition. SC is needed to build `T`; IR to orient the adjunction; neither for revenue
equivalence itself.

---

## D6 — The paper's arc is three moves
**Date:** 2026-07-13 · **Commit:** `0225ed4`

1. **General:** `T ⊣ Q` on all of **Mech**; `T` fully faithful; `T(r)` initial; fiber
   coordinate is the boundary rent.
2. **Comonad:** `T ∘ Q` strips the rent (`zeroRent_TQ`); the counit is invertible exactly on
   zero-rent objects.
3. **Normalised:** `Alloc ≌ Mech₀` (`equivAllocMech₀`) — adjoint in both directions. The
   Taxation Principle.

The content is in Moves 1 and 2. **Move 3 is cheap, as equivalences always are** — say so in
the paper rather than letting a referee say it.

---

## D7 — The envelope hypothesis is **one-sided**: continuity + a right derivative
**Date:** 2026-07-13 · **Branch:** `surplus-order` · **Phase 0**

`hEnv` now reads

```lean
hVcont : ContinuousOn (fun s => v (r.q s) s - m.mech.t s) (Set.Ioi 0)
hEnv   : ∀ θ > 0, HasDerivWithinAt (fun s => v (r.q s) s - m.mech.t s)
                    (typeDerivAlongAlloc v r θ) (Set.Ioi θ) θ
```

**Rejected: the two-sided `HasDerivAt` we had.** It is not merely stronger than needed — it
is **false** for the canonical optimal auction. A posted price with reserve `p`
(`q θ = 1{p ≤ θ}`) is monotone, IC and IR, and has surplus `V θ = max (θ - p) 0`, which has
slope `0` from the left and `1` from the right at `p`. It has *no* derivative there, for any
candidate value — proved as `PostedPrice.postedPrice_not_hasDerivAt`.

So the old hypothesis was **unsatisfiable** for every auction with a reserve price and every
allocation with a bunching region: `revenueEquivalence` could not be applied to the
mechanisms it most wants to talk about. This was a scope hole, not a stylistic choice.

**Why one-sided works:** the right derivative survives the kink — at `p` it is `1 = q p` —
and mathlib's `integral_eq_sub_of_hasDeriv_right` only ever needed
`ContinuousOn` + `HasDerivWithinAt … (Set.Ioi x) x` on the open interval. The envelope
identity holds; only two-sidedness fails. Discharged for the posted price in
`PostedPrice.postedPrice_hasEnvelope`.

Every previous caller still typechecks: `HasDerivAt.hasDerivWithinAt` makes this a strict
weakening. Cost: one extra hypothesis (`hVcont`) at each site.

---

## D8 — Continuity of the surplus is **derived from IC**, not assumed
**Date:** 2026-07-13 · **Branch:** `surplus-order` · **Phase 1**

`surplus_split` no longer takes a `ContinuousOn` hypothesis. It takes a regularity
hypothesis on the *value function* —

```lean
L : NNReal
hvLip : ∀ θ' : ℝ, LipschitzOnWith L (v (m.mech.q θ')) (Set.Ici θ_min)
```

— and derives continuity of the surplus from `m.hIC` via `surplus_ic_sandwich`:

```
v(q θ₁, θ₂) − v(q θ₁, θ₁)  ≤  V(θ₂) − V(θ₁)  ≤  v(q θ₂, θ₂) − v(q θ₂, θ₁)
```

Both bounds move the *type* while holding the *allocation* fixed, so each is bounded by
`L·|Δθ|`, giving `surplus_lipschitzOn` and hence `surplus_continuousOn`.

**This is what finally makes `hIC` load-bearing.** Verified the only way that can be
trusted here (see `CLAUDE.md`): commenting out `surplus_ic_sandwich` **breaks the build**.
The chain `revenueEquivalence → masterTheorem_transferInvariance → mechIso_… →
surplus_split → surplus_continuousOn → surplus_lipschitzOn → surplus_ic_sandwich → m.hIC`
is real.

**Rejected: keep assuming `ContinuousOn`.** It compiles, but it leaves incentive
compatibility unused — the theorems would remain *about mechanisms that happen to have a
continuous surplus*, not about IC mechanisms.

**Note on the hypothesis shape.** `hvLip` quantifies over the allocations the mechanism
*actually uses* (`v (m.mech.q θ')`), not over all of `A`. A bound uniform over all of `A`
would be **false** for `MyersonAlloc = ℝ` (take `a → ∞`). Discharged for Myerson by
`myerson_lipschitz` (allocation probabilities in `[-1,1]` give `L = 1`), and for the posted
price by `PostedPrice.postedPrice_lipschitz`. The Mirrlees discharge is on paper but not yet
in Lean — see `TODO.md`.

---

## D9 — The envelope family lives on `[θ_min, ∞)`, not `(0, ∞)`
**Date:** 2026-07-13 · **Phase 1**

`surplus_split`, `envelope_transfer_shift` and `envelope_transfer_unique` now conclude for
`θ_min ≤ θ` rather than `0 < θ`.

**Forced by D8.** `IsIC` only constrains reports and types `≥ θ_min`, so the IC sandwich —
and therefore continuity of the surplus — is available only on `[θ_min, ∞)`. Nothing below
`θ_min` is derivable from IC, so claiming it there was never honest. The model has no
economic content below `θ_min` anyway, and every caller already worked on `[θ_min, ∞)`.

---

## Pending — record before implementing

* **Phase 2:** right-continuity of `q` — a field of `MonotoneAlloc`, or a hypothesis?
* **Phase 2:** whether to drop `hMono` as a field of `ICIRMechanism` once `hIC` is
  load-bearing (it is derivable from `hIC` + SC via `IC_implies_monotone`).
