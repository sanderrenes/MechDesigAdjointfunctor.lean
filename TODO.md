# TODO

Living list. Update it in the same commit as the work — see `CLAUDE.md`.
Legend: `[ ]` open · `[~]` in progress · `[x]` done · `[-]` dropped (say why)

## Now — Phase 1: `V` Lipschitz from IC
- [ ] Check the "`∂_θ v` locally bounded, uniformly in the allocation" hypothesis discharges
      for `myersonValue` **and** `mirrleesValue` *before* touching the abstract layer
- [ ] `surplus_ic_sandwich` from `m.hIC`
- [ ] `surplus_lipschitzOn` → `surplus_continuousOn`
- [ ] Commit

## Then — Phase 2: right-derivative = `D θ` (Milgrom–Segal)
- [ ] Decide: right-continuity of `q` as a `MonotoneAlloc` field, or a hypothesis? Record in `DECISIONS.md`
- [ ] Joint continuity of `∂_θ v`; verify for both value functions first
- [ ] `surplus_hasDerivWithinAt` (squeeze)
- [ ] Delete `hEnv` from every signature
- [ ] Give `IC_implies_monotone` a consumer; consider dropping `hMono` as a field
- [ ] Commit

## Open questions (not scheduled)
- [ ] `myersonTransfer` is never linked to `transferFormula`; it hard-codes `θ_min = 0`
      while the master theorem needs `θ_min > 0`. The Myerson revenue formula therefore
      floats free of the categorical machinery. (`PLAN.md` § Out of scope, Bridge 2)
- [ ] The corollaries never touch `adj_T_Q` (verified by deletion). Optionally route
      transfer invariance through initiality of `T(r)`. (Bridge 3)
- [ ] `myerson_singleCrossing` / `mirrlees_singleCrossing` have no consumers since the
      boundary condition was relaxed to equal-rent. Expected, but confirm it stays that way.
- [ ] Decide whether `Corollaries.taxationPrinciple` should keep its now-unused setting
      hypotheses (`hh`, `hg`, `hg_pos`, `hh_mono`, `hSM`) or drop them.
- [ ] `failure_nonQuasilinear`, `failure_multiDimensional`, `failure_ironing` are `True`
      placeholders in `Corollaries.lean`. Either state them or delete them.

## Done
- [x] **Phase 0** — `hEnv` weakened to `ContinuousOn` + `HasDerivWithinAt … (Set.Ioi θ) θ`
      throughout (D7). `surplus_split` now uses
      `intervalIntegral.integral_eq_sub_of_hasDeriv_right`. Acceptance test landed:
      `PostedPrice.postedPrice_hasEnvelope` (the reserve-price auction *does* satisfy the new
      hypothesis) and `PostedPrice.postedPrice_not_hasDerivAt` (it does **not** satisfy the
      old one — no derivative at the reserve, for any candidate value).
- [x] Order `MechHom` by surplus rather than transfer; `T` becomes a functor (D1, D2)
- [x] `adj_T_Q` : `T ⊣ Q`; `T(r)` initial, not terminal (D3)
- [x] Relax the boundary condition to equal rent, `hV₀` (D5)
- [x] `Mech₀` + `equivAllocMech₀` : `Alloc ≌ Mech₀` — Move 3 (D6)
- [x] Correct the `IsIR` docstring (it described the normalisation, not the inequality)
