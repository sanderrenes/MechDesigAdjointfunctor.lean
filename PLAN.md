# Plan — closing the IC ⟹ envelope bridge

Status: **Phase 0 done. Phase 1 done** (abstract layer + Myerson; the Mirrlees Lipschitz discharge remains — see TODO.md). **Phase 2 open.** Branch: `surplus-order`.

## Why

Every theorem in the development takes `hEnv` as a *hypothesis*:

```lean
hEnv : ∀ θ > 0, HasDerivAt (fun s => v (r.q s) s - m.mech.t s) (typeDerivAlongAlloc v r θ) θ
```

Two problems follow from this, and they are the largest open issues in the project.

**1. `hEnv` is too strong — it is false for the mechanisms that matter.** It demands a
two-sided derivative at *every* physical type. Take a posted price with reserve `p`, the
canonical optimal auction: `q θ = 1{θ ≥ p}` is monotone, IC and IR, and its surplus
`V(θ) = max(θ − p, 0)` has a **kink at `p`**. No derivative there. So `hEnv` is
unsatisfiable and `revenueEquivalence` **cannot be applied to any auction with a reserve
price**, nor `taxationPrinciple` to any allocation with a bunching region.

**2. Incentive compatibility is never used.** `ICIRMechanism.hIC` is consumed by exactly
one lemma, `IC_implies_monotone`, and nothing consumes that lemma (verified: the project
builds with it deleted). IC enters the development *only* through the assumed `hEnv`. The
missing link — IC ⟹ envelope condition, the only-if direction of the envelope theorem
(Milgrom–Segal) — is precisely what would make `hIC` load-bearing.

Closing this bridge fixes both at once.

---

## Phase 0 — weaken `hEnv` to the right-derivative form ✅ **DONE**

Landed. `hEnv` is now `ContinuousOn` + `HasDerivWithinAt … (Set.Ioi θ) θ`; `surplus_split`
uses `integral_eq_sub_of_hasDeriv_right`; the posted price is proved to satisfy the new
hypothesis (`PostedPrice.postedPrice_hasEnvelope`) and to **violate** the old one
(`PostedPrice.postedPrice_not_hasDerivAt`). See `DECISIONS.md` D7. Original write-up follows.

**Do this regardless of the rest.** It is an independent correctness-of-scope fix.

Mathlib's FTC-2 does not need two-sided derivatives.
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` asks only for

* `ContinuousOn V (Icc a b)`, and
* `HasDerivWithinAt V (D x) (Ioi x) x` for `x ∈ Ioo a b` — a **right** derivative.

The right derivative survives a kink: at the posted price, `V`'s right-derivative at `p`
is `1 = q(p) = D(p)`. The envelope identity holds; only two-sidedness fails.

**Tasks**
- [ ] Swap the FTC call inside `surplus_split` (the only place `hEnv` is consumed) to
      `integral_eq_sub_of_hasDeriv_right_of_le`.
- [ ] Weaken the `hEnv` hypothesis to `HasDerivWithinAt … (Set.Ioi θ) θ` + `ContinuousOn`
      throughout `MasterTheorem.lean` and `Corollaries.lean`.
- [ ] Confirm existing callers still typecheck (`HasDerivAt.hasDerivWithinAt` is a strict
      weakening, so they should).
- [ ] Add a regression example: the posted-price mechanism `q θ = if p ≤ θ then 1 else 0`
      satisfies the new hypothesis and the old one it does not. **This is the acceptance
      test for the phase** — without it we have not demonstrated the fix.

**Acceptance:** `lake build` clean, zero sorries, standard axioms; posted-price example
compiles; `git commit`.

**Estimate:** ~half a day. Low risk.

---

## Phase 1 — `V` is Lipschitz, hence continuous, *from IC* ✅ **DONE (abstract + Myerson)**

Landed: `surplus_ic_sandwich` (pure IC) → `surplus_lipschitzOn` → `surplus_continuousOn`.
`surplus_split` derives continuity instead of assuming it, so **`hIC` is now load-bearing** —
confirmed by deletion (removing the sandwich breaks the build). Myerson discharged via
`myerson_lipschitz`. See `DECISIONS.md` D8, D9. Remaining: the Mirrlees Lipschitz discharge
(`TODO.md`). Original write-up follows.

IC gives the sandwich directly, with no analysis — for `θ₁ < θ₂`, using each type's report
as the other's deviation:

```
v(q θ₁, θ₂) − v(q θ₁, θ₁)  ≤  V(θ₂) − V(θ₁)  ≤  v(q θ₂, θ₂) − v(q θ₂, θ₁)
```

Both bounds integrate `∂_θ v` along a *fixed* allocation, so a local bound on `∂_θ v(a, s)`
uniform in `a` over the range of `q` yields `|ΔV| ≤ L·|Δθ|` — `LipschitzOnWith`, hence
`ContinuousOn`, which is Phase 0's first hypothesis, now **derived from `hIC`**.

**Tasks**
- [ ] State the new regularity hypothesis: `∂_θ v` locally bounded, uniformly in the
      allocation. Verify it discharges for `myersonValue` (`∂_θ v = a`) **and**
      `mirrleesValue` (`∂_θ v = h y + g′(y/θ)·y/θ²`) *before* touching the abstract layer.
- [ ] `surplus_ic_sandwich`: the two-sided bound, straight from `m.hIC`.
- [ ] `surplus_lipschitzOn` → `surplus_continuousOn`.

**Acceptance:** `ContinuousOn` is discharged from IC, not assumed. Build clean. `git commit`.

**Estimate:** ~1 day.

---

## Phase 2 — the right-derivative equals `D θ` (Milgrom–Segal)

Divide the same sandwich by `h > 0`:

```
(v(q θ, θ+h) − v(q θ, θ))/h  ≤  (V(θ+h) − V(θ))/h  ≤  (v(q(θ+h), θ+h) − v(q(θ+h), θ))/h
```

The **lower** bound → `∂_θ v(q θ, θ) = D θ` by differentiability of `v(a, ·)`. The **upper**
bound → the same limit provided `q(θ+h) → q θ` — i.e. **`q` right-continuous at `θ`** — plus
joint continuity of `∂_θ v` in `(a, s)`. Squeeze via `hasDerivWithinAt_iff_tendsto_slope`
and `tendsto_of_tendsto_of_tendsto_of_le_of_le`.

Right-continuity of `q` is a new assumption but economically free: a monotone `q` has
countably many jumps and the mechanism is unchanged a.e. by taking the right-continuous
representative. The posted price with `q p = 1` is already right-continuous.

**Tasks**
- [ ] Add right-continuity of `q` (as a field of `MonotoneAlloc`, or a hypothesis — decide
      and record in `DECISIONS.md`).
- [ ] Add joint continuity of `∂_θ v`; verify for both value functions first.
- [ ] `surplus_hasDerivWithinAt`: the squeeze.
- [ ] Delete `hEnv` from every signature; `surplus_split` becomes a theorem about IC
      mechanisms.
- [ ] Now that `hIC` is load-bearing: give `IC_implies_monotone` a consumer, and consider
      dropping `hMono` as a field of `ICIRMechanism` (it is derivable from `hIC` + SC).

**Acceptance:** `hEnv` appears nowhere. `hIC` is reachable from `revenueEquivalence` and
`taxationPrinciple` in the dependency graph. Build clean. `git commit`.

**Estimate:** 1–2 days. Most of it is hypothesis bookkeeping, not hard analysis.

**Main risk:** the uniformity hypotheses in Phases 1–2 must be stated so that *both* value
functions discharge them. Instantiate both **before** refactoring the abstract layer. This
is exactly the failure mode that killed the convexity route (see `DECISIONS.md`, D1).

---

## Out of scope here, but open

* **Bridge 2 — `myersonTransfer` is unlinked.** `myerson_expectedRevenue` is proved about
  `myersonTransfer`, a definition written independently of `transferFormula`. They coincide
  mathematically (at `v = θ·q` the envelope integrand is just `q`), but no lemma says so,
  and `myersonTransfer` hard-codes `θ_min = 0` while the master theorem needs `θ_min > 0`.
  So the virtual-valuation result floats free of the categorical machinery.
* **Bridge 3 — the corollaries never use the adjunction.** `revenueEquivalence` and
  `taxationPrinciple` reach `masterTheorem_transferInvariance` and stop; `adj_T_Q` is proved
  structure nothing consumes (verified by deletion). Optional fix: route transfer invariance
  through initiality of `T(r)`.
