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

## D10 — The envelope condition is **derived from IC** (Milgrom–Segal). `hEnv` is gone.
**Date:** 2026-07-13 · **Branch:** `surplus-order` · **Phase 2**

`surplus_hasDerivWithinAt` proves what `hEnv` used to assume: the surplus has a right
derivative equal to the envelope integrand, at every physical type. Divide the IC sandwich
by `y − θ > 0`; the lower bound is a slope of `v(q θ, ·)` and tends to `D θ`; the upper bound
is a slope of `v(q y, ·)`, which the **mean value theorem** turns into `∂_θ v(q y, ξ)` for
`ξ ∈ (θ, y)`; as `y ↓ θ` both collapse to `θ`. Squeeze.

`hEnv` no longer appears anywhere in `MasterTheorem.lean` or `Corollaries.lean`.

**The one surviving hypothesis, and why it is shaped oddly.** `A` carries **no topology** in
this framework, so "`q` is right-continuous" is not even *statable*. Instead:

```lean
hW : ∀ θ, θ_min ≤ θ → ContinuousWithinAt (fun p : ℝ × ℝ => deriv (v (r.q p.1)) p.2)
                        (Set.Ici θ ×ˢ Set.Ici θ) (θ, θ)
```

**Rejected: add `[TopologicalSpace A]` to the framework** and assume right-continuity of `q`
plus joint continuity of `∂_θ v`. That would have touched every declaration in the project,
and it is *stronger* than what the squeeze needs. `hW` asks only for what is actually used:
the composite `(s, u) ↦ ∂_θ v(q s, u)` continuous at the diagonal from the upper-right.

In the Myerson setting `∂_θ v(a, u) = a`, so `hW` **is** precisely right-continuity of `q` —
and the posted price satisfies it (`PostedPrice.postedPrice_hW`): `q` jumps *up* at the
reserve, and `q p = 1`. The reserve-price auction, which the original two-sided `HasDerivAt`
excluded outright, now sails through the derivation.

---

## D11 — `hMono` stays a field of `ICIRMechanism`
**Date:** 2026-07-13 · **Phase 2**

**Rejected: drop `hMono` and derive it from `hIC` + SC via `IC_implies_monotone`.**
`IC_implies_monotone` concludes `MonotoneOn m.mech.q (Set.Ici θ_min)` — monotone on the
*physical domain only*. The field `hMono : Monotone mech.q` is monotonicity on **all of ℝ**,
which IC cannot give, because `IsIC` says nothing about types below `θ_min`. The two are not
interchangeable, so the field stays.

`IC_implies_monotone` therefore remains without a consumer. It is retained as a documented
consistency check: it shows the `hMono` field is not an *extra* economic assumption on the
domain where the model has content. Recorded rather than silently deleted.

---

## D12 — Drop the hypotheses the corollaries do not use; make the categorical route explicit
**Date:** 2026-07-13 · **Branch:** `surplus-order`

`taxationPrinciple` no longer takes `hg_pos`, `hh_mono`, `hSM` (the Spence–Mirrlees
conditions) or `hintC`; `revenueEquivalence` no longer takes `hintC`.

**Rejected: keep them to document the setting.** They were *unused*, and carrying an unused
hypothesis overstates what a theorem needs — a reader (or referee) reasonably assumes every
hypothesis is load-bearing. Transfer invariance needs **neither single crossing nor IR**: SC
is what makes `T` a functor, IR is what orients the adjunction, and revenue equivalence needs
neither. Dropping them *strengthens* the statements.

Separately, `transferInvariance_via_T` derives Theorem 4.5(iii) for normalised mechanisms by
going `m₁ ≅ T(r) ≅ m₂` and applying `transfer_eq_of_iso`, giving `masterTheorem_isomorphism`
a consumer and demonstrating that the route through `T` is genuinely available.

`adj_T_Q` still has no consumer. **That is correct and should not be "fixed":** an adjunction
is *structure*, not a lemma. Contriving a dependency on it would be dishonest. The module
docstring says so plainly.

---

## D13 — `myersonTransfer` and `transferFormula` differ by the rent below `θ_min`
**Date:** 2026-07-13 · **Branch:** `surplus-order`

`myerson_transferFormula_eq_myersonTransfer`:

```
transferFormula(θ_min)(θ)  =  myersonTransfer(θ)  +  ∫₀^{θ_min} q
```

**Rejected: prove them equal.** They are *not* equal. `myersonTransfer` hard-codes
`θ_min = 0`, while the Master Theorem requires `θ_min > 0`, and the two differ by exactly the
rent conceded below `θ_min`. Asserting an equality would have required either weakening the
master theorem to `θ_min = 0` (destroying the FTC arguments, which need `θ_min > 0`) or
silently changing `myersonTransfer`. The shift *is* the bridge, and it is consistent with D5:
the abstract theory deliberately leaves the boundary rent free.

---

## D14 — Delete the `True := trivial` "failure" theorems
**Date:** 2026-07-13 · **Branch:** `surplus-order`

`failure_nonQuasilinear`, `failure_multiDimensional`, `failure_ironing` were each
`theorem … : True := trivial`.

**Rejected: keep them as placeholders.** A theorem whose statement is `True` proves nothing,
but it *looks* like a result — it appears in the declaration list, it type-checks, and it
makes the development seem to cover the failure cases when it does not. That is worse than
absence. They are now prose in §5.3 of `Corollaries.lean`, which is what they always were,
and the prose is sharper for being written against the current design (e.g. failure of SC
breaks `T`'s functoriality but *not* revenue equivalence).

---

## D15 — The transfer order was a **default**, not a belief. State its provenance honestly.
**Date:** 2026-07-14 · **Branch:** `surplus-order` · **Artifact:** the category-theory talk

D1 records *that* the transfer order fails and *why* (Mirrlees is concave in `y`). This entry
records where that order **came from**, because the exposition kept getting it wrong and the
next session will get it wrong again.

**The provenance is: a mechanism *is* the pair `⟨q, t⟩`, and a pair invites a componentwise
order.** Nobody chose `hTransf`. Nobody defended it. It is the order you write when the object
presents itself as two coordinates and nothing has ever asked which coordinate is the state
variable.

**Rejected: "economists believe that allocating more means charging more."** This was the
framing in the first draft of the talk, and it is **false as stated** — it would not survive a
question from the floor. Pointwise comparison of transfers *across two mechanisms* is not a
standard order in mechanism design at all; economists compare mechanisms by expected revenue,
or by Pareto dominance in utilities. The bundle-costs-more intuition is a fact about **one
agent facing one price schedule**, and the draft silently transplanted it to a comparison
**between mechanisms**. Do not reinstate this framing, however well it plays.

**Why the honest version is stronger.** "Economists believe a false thing" invites an argument
about what economists believe, and loses it — they do not believe it, they have never
considered it. "Here is a definition that constrains a literature and has never once been made
to justify itself" is unarguable, and it is what the development actually demonstrates. It also
explains why the error survived: **a componentwise order on a pair states no theorem, so it is
never checked.** It sits in a structure and silently constrains everything downstream. The only
reason it was ever read aloud is that a functor demanded to know what it said.

**How this was caught.** Not by Lean — by the user pressing on a sentence that *sounded* right.
Which is the same failure mode the project is about: plausibility is exactly what the kernel
refuses and prose accepts. Prose has no kernel. The docstring rule (D4) is the same lesson;
this is its second instance, and it now applies to the **paper**, not just the code.

---

## D16 — `A` needs only an order. Drop `AddCommGroup` and `IsOrderedAddMonoid`.
**Date:** 2026-07-17 · **Branch:** `surplus-order` · **Verified by:** deletion + `lake build`

Every declaration touching `A` carried `[AddCommGroup A]` and `[IsOrderedAddMonoid A]`. **Not
one proof used them.** Removed from all 27 binders across `Framework.lean` and
`MasterTheorem.lean`; `lake build` completes (2683 jobs), zero sorries, zero warnings, and
`revenueEquivalence`, `taxationPrinciple`, `allocCategory`, `mechCategory`, `T` and `adj_T_Q`
still rest on exactly `[propext, Classical.choice, Quot.sound]`.

**Where the binders came from.** The *spread monotonicity* field on `AllocHom`,
`Monotone (fun θ => r'.q θ - r.q θ)`, was the only consumer — it subtracts in `A`, so it needed
the group. That field was dropped when **Mech** moved to the surplus order (D1, D2), because
`T.map` then follows from single crossing alone. **The subtraction went away and the binder
stayed.** `AllocHom`'s sole field is now `∀ θ, r.q θ ≤ r'.q θ`, and `MechHom`'s two fields are
an inequality in `A` and an inequality in `ℝ`. A `Preorder` suffices. The surplus subtraction
`v (q θ) θ - t θ` is in `ℝ`, which is where the group instance was silently coming from all
along — never from `A`.

**Rejected: keep them as future-proofing / "they cost nothing".** They cost something specific
and they had already charged it. `MyersonSetting.lean` read: *"Using `ℝ` rather than
`Set.Icc 0 1` gives the `AddCommGroup` instance required by `AllocHom`."* So an **unused
typeclass dictated the modelling choice** — the Myerson allocation space is the reals because a
binder asked, and `[0,1]` is therefore enforced by hypothesis at call sites (`|a| ≤ 1` in
`myerson_lipschitz`) rather than by the type. A probability is not an abelian group; `[0,1]`
is not closed under addition. The requirement that forced ℝ was vacuous. Docstring corrected.

**Also rejected: infer it from the absence of `+` or `-` on `A` in the source.** That is the
token scan the project has already been burned by (`CLAUDE.md`), and it cannot see instance
resolution. The claim here rests on deletion and rebuild, and on nothing else.

**How this was caught.** Not by Lean — Lean was perfectly happy to carry a vacuous binder
forever. By the user asking, of a sentence in the talk, *"how is the probability of winning an
abelian group?"* The formalisation had been quietly answering *"it isn't — so I'll use ℝ"* for
months, and no build ever complained. **This is D15's lesson again, from the other side:** D15
was prose flattering a definition, this is a definition flattered by an unexamined constraint.
Both survived because nothing was ever obliged to state them out loud.

**Left open.** Whether `MyersonAlloc` should now *become* `Set.Icc 0 1` — only `Preorder` is
demanded, so it is newly possible, but `myersonValue` would need `θ * a.val` and every call
site shifts. **Untested. Do not assume it works.** See `TODO.md`.

---

## D17 — Two linters for statements that say nothing. Both advisory, neither a gate.
**Date:** 2026-07-17 · **Branch:** `surplus-order` · **File:** `Lean/Linters.lean`

D14 deleted three `theorem … : True := trivial` declarations that had made `Corollaries.lean`
look as though it covered the failure cases. **Nothing in the toolchain would have caught them.**
Tested: all 16 default `#lint` linters pass a `True` theorem in silence; `synTaut` fires only on
literal `e = e`. So the project's own worst empty statement was invisible to every check it had.

Two linters, deliberately of different kinds:

* **`linter.trueStatement`** — a real **compiler warning**, at elaboration, on any declaration
  whose conclusion is `True` (all leading `∀` stripped). Decidable and exact. Live on the whole
  library: `lake build` is clean, 2684 jobs, **zero false positives across 132 declarations**.
  Opt out with `set_option linter.trueStatement false in`.
* **`witnessless`** — an `@[env_linter]`, so it surfaces only under `lake exe runLinter`. Reports
  any theorem tagged `@[needs_witness]` with no `@[witness_for]` aimed at it.

**Rejected: make either one a hard gate (an error, or a `lake build` failure).** The `True` check
could be — it is exact. But a `True` statement is occasionally the honest placeholder, and a rule
that cannot be obeyed gets disabled wholesale, taking the useful signal with it. A warning is
read; an error in the way is silenced. The gate that already exists (zero sorries) is enforceable
because it is never *right* to leave a `sorry`. It is sometimes right to write `True`.

**Rejected: a linter that detects vacuity.** This is what one actually wants and it **cannot be
built**: satisfiability of a hypothesis set is undecidable. Anything claiming to do it is lying.
`witnessless` therefore checks a **weaker, honest thing** — that you *said* the hypotheses
deserved an instance and have not produced one. It is a checklist, not a proof.

**Rejected: fire `witnessless` on every theorem with hypotheses, no tagging needed.** That is the
version with no opt-in, and it would report essentially every lemma in the library. A linter that
fires on everything conveys nothing, and would be turned off within a day. Opt-in keeps the
signal where it was deliberately asked for — the headline theorems.

**The limit, stated so nobody mistakes these for safety.** Neither linter can tell you a statement
is *wrong*, only that it is shaped like nothing. D1 (a definition that was false), D7 (a
hypothesis false for every reserve-price auction) and D16 (a vacuous binder) would all pass both
in silence. The only test that found those was a human reading the statement, or deletion. **The
real defence against vacuity is instantiation** — `postedPrice_hasEnvelope`,
`postedPrice_lipschitz`, `postedPrice_hW` are what D7 was caught by, and `witnessless` only nags
you to write more of them.

**Cost.** `Framework.lean` now imports `Lean/Linters.lean`, so the whole chain depends on it — a
linter only runs in files that import it. That is a real coupling: the linter file must stay
cheap and must never fail to compile, or the entire library stops building.

---

## Pending

*Nothing pending.* All phases of `PLAN.md` are complete; `TODO.md` lists only
non-committal ideas.