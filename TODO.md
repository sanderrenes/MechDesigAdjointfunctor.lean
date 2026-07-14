# TODO

Living list. Update it in the same commit as the work — see `CLAUDE.md`.
Legend: `[ ]` open · `[~]` in progress · `[x]` done · `[-]` dropped (say why)

## Open

*Nothing scheduled.* The IC ⟹ envelope bridge is closed and all three missing bridges are
resolved. `lake build` is clean with **zero sorries, zero warnings**, and every result rests
on `[propext, Classical.choice, Quot.sound]`.

- [ ] **Carry D15 into the paper.** The presentation (`docs/functoriality-talk.html`) already
      states the transfer order's provenance honestly: it was a **componentwise default on the
      pair `⟨q,t⟩`**, not a belief economists hold. The *paper* has yet to be written, and the
      seductive-but-false framing ("economists think allocating more means charging more") will
      present itself again the moment it is. It does not survive a referee. Use D15's version:
      a componentwise order on a pair **states no theorem, so it is never checked** — which is
      why the error survived, and why a functor was needed to make it speak.

Ideas, not commitments:
- [ ] Prove the failure cases in §5.3 of `Corollaries.lean` rather than documenting them
      (they are currently prose, having been fake `True := trivial` theorems — see D14).
- [ ] `mirrlees_lipschitz` takes the derivative bound as a hypothesis. It could be *derived*
      from bounded incomes plus continuity of `h` and `g'` on the relevant compact.
- [ ] `hW` could be specialised: in the Myerson setting it is literally right-continuity of
      `q`, and a helper lemma `myerson_hW_of_rightContinuous` would make that visible to
      callers rather than leaving them to unfold the composite.

## Done

- [x] **Bridge 2 — `myersonTransfer` linked to `transferFormula`** (D13).
      `myerson_transferFormula`: the abstract formula at `v = θ·a` is `θ·q θ − ∫_{θ_min}^θ q`.
      `myerson_transferFormula_eq_myersonTransfer`: the two differ by **exactly** the rent
      conceded below `θ_min`, `∫₀^{θ_min} q`. They coincide iff `θ_min = 0`, which the master
      theorem forbids — so the honest bridge is the shift, not an equality.
- [x] **Bridge 3 — the categorical route made explicit** (D12). `transferInvariance_via_T`
      derives Theorem 4.5(iii) for normalised mechanisms by going `m₁ ≅ T(r) ≅ m₂` and
      applying `transfer_eq_of_iso`. This gives `masterTheorem_isomorphism` a consumer and
      shows `T` is not decorative. `adj_T_Q` still has no consumer, and that is correct: an
      adjunction is *structure*, not a lemma. Documented in the module docstring.
- [x] **Unused hypotheses dropped** (D12). `taxationPrinciple` no longer takes `hg_pos`,
      `hh_mono`, `hSM` (the Spence–Mirrlees conditions) or `hintC`; `revenueEquivalence` no
      longer takes `hintC`. Transfer invariance needs **neither SC nor IR** — SC makes `T` a
      functor, IR orients the adjunction, and revenue equivalence needs neither. Carrying
      them overstated the theorem's requirements.
- [x] **Fake theorems deleted** (D14). `failure_nonQuasilinear`, `failure_multiDimensional`
      and `failure_ironing` were `theorem … : True := trivial`. A theorem stating `True`
      proves nothing and made the file look as though it covered the failure cases. They are
      now prose in §5.3, which is what they always were.
- [x] **`myerson_singleCrossing` / `mirrlees_singleCrossing` have no consumers** — confirmed
      expected and correct. Once the boundary condition was relaxed to equal-rent (D5),
      transfer invariance stopped needing SC. SC remains load-bearing for `T`'s functoriality
      (`typeDeriv_mono_of_alloc_le` → `Tmech_surplus_mono`), just not for the corollaries.
- [x] **Phase 2 — THE BRIDGE IS CLOSED** (D10, D11). `surplus_hasDerivWithinAt` proves the
      envelope condition from IC via the Milgrom–Segal squeeze (IC sandwich + mean value
      theorem). **`hEnv` no longer appears in `MasterTheorem.lean` or `Corollaries.lean`.**
      The surviving hypothesis is `hW` — continuity of `(s,u) ↦ ∂_θ v(q s, u)` at the diagonal
      from the upper right — stated on the composite because `A` has no topology. In the
      Myerson setting it *is* right-continuity of `q`, and the posted price satisfies it
      (`PostedPrice.postedPrice_hW`). `hMono` stays a field (D11): IC gives only `MonotoneOn`
      on `[θ_min, ∞)`, not `Monotone` on ℝ.
- [x] **Phase 1 (complete)** — `hIC` is **load-bearing** (D8, D9). `surplus_ic_sandwich`
      (pure IC) → `surplus_lipschitzOn` → `surplus_continuousOn`; `surplus_split` derives
      continuity instead of assuming it. Verified by deletion. Discharged in both settings
      (`myerson_lipschitz`, `mirrlees_lipschitz`, `PostedPrice.postedPrice_lipschitz`).
      Envelope family moved from `(0, ∞)` to `[θ_min, ∞)`.
- [x] **Phase 0** — `hEnv` weakened to a **right** derivative (D7). The old two-sided
      `HasDerivAt` was not merely strong but **false** for the posted price
      (`PostedPrice.postedPrice_not_hasDerivAt`), so reserve-price auctions were excluded
      outright. Now they satisfy every hypothesis (`postedPrice_hasEnvelope`,
      `postedPrice_lipschitz`, `postedPrice_hW`).
- [x] Order `MechHom` by surplus rather than transfer; `T` becomes a functor (D1, D2)
- [x] `adj_T_Q` : `T ⊣ Q`; `T(r)` initial, not terminal (D3)
- [x] Relax the boundary condition to equal rent, `hV₀` (D5)
- [x] `Mech₀` + `equivAllocMech₀` : `Alloc ≌ Mech₀` — Move 3 (D6)
- [x] Correct the `IsIR` docstring (it described the normalisation, not the inequality) (D4)
