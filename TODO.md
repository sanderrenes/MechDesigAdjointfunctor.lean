# TODO

Living list. Update it in the same commit as the work — see `CLAUDE.md`.
Legend: `[ ]` open · `[~]` in progress · `[x]` done · `[-]` dropped (say why)

## Open

*No proof work scheduled.* The IC ⟹ envelope bridge is closed and all three missing bridges are
resolved. `lake build` is clean with **zero sorries, zero warnings**, and every result rests
on `[propext, Classical.choice, Quot.sound]`. What is open below is exposition, tooling and
one untested refactor — not mathematics.

- [ ] **Confirm `lean_action_ci.yml` goes green with the new Jekyll homepage (D18).** `docs/`
      gained `Gemfile` / `_config.yml` / `index.md` so `docgen-action`'s `bundle exec jekyll
      build` step has a real site to build, fixing a "Could not locate Gemfile" CI failure.
      `bundle install && jekyll build` now builds clean **locally** (2026-07-17) and
      `docs/Gemfile.lock` is committed from that run — what's still unconfirmed is the GitHub
      Actions runner itself and the `deploy-pages` step. Push and watch the Action.

- [ ] **Carry D15 into the paper.** The presentation (`docs/functoriality-talk.html`) already
      states the transfer order's provenance honestly: it was a **componentwise default on the
      pair `⟨q,t⟩`**, not a belief economists hold. The *paper* has yet to be written, and the
      seductive-but-false framing ("economists think allocating more means charging more") will
      present itself again the moment it is. It does not survive a referee. Use D15's version:
      a componentwise order on a pair **states no theorem, so it is never checked** — which is
      why the error survived, and why a functor was needed to make it speak.

- [ ] **Make `MyersonAlloc` actually be `Set.Icc 0 1`?** Newly *possible* after D16 — `A` needs
      only a `Preorder`, and the `AddCommGroup` requirement that forced `ℝ` turned out to be
      vacuous. **Untested, and not obviously worth it:** `myersonValue` becomes `θ * a.val`,
      every call site shifts, and `myerson_lipschitz`'s `|a| ≤ 1` hypothesis would become free.
      The win is honesty — "probability of winning" would be true of the type rather than of a
      hypothesis carried beside it. Decide by trying it, not by reasoning about it.

- [ ] **Add `lake exe runLinter` to the quality gate.** `lake exe runLinter MechDesigAdjointfunctor.Lean`
      runs 16 environment linters over the library. It ships with Batteries via Mathlib, it works
      on this project today, and **it has never been run**. Add it to `CLAUDE.md`'s per-commit gate
      beside `lake build` and `#print axioms`.
      **Triage the 9 current findings first** — a gate that starts red is a gate nobody obeys:
      - `unusedArguments` on `T_preservesColimits` / `Q_preservesLimits`: both carry a long list of
        unused hypotheses (`hD`, `hdiff`, `hintC`, `hint`, `hvLip`, `hW`). This is D12's finding
        again — hypotheses that overstate what a result needs. **Most likely to be real.**
      - `structureInType` on `MechHom` / `AllocHom`: "all fields are propositional but the structure
        isn't." *Probably* a forced false positive, since `CategoryTheory.Category` demands
        `Type`-valued homs — **unverified, check before dismissing.**
      - `unusedArguments` on `Q` (`_hSC`, `_hD`): already underscored, i.e. deliberate. Silence it
        or justify it in the docstring.
      - `docBlame`: `Mechanism.q`, `Mechanism.t`, `ICIRMechanism.mech`, `MonotoneAlloc.q` carry `--`
        line comments where docstrings were meant. D4's lesson: a comment Lean does not attach is a
        comment nobody reads.
      **What the linter cannot do, so the gate must keep saying so (D16):** it catches vacuous
      instance binders on `def`s only — never on `structure`s, `instance`s or `theorem`s, which is
      where definitions live. It caught 1 of our 27 binders. And a *chain* of vacuous binders hides
      itself: `AddCommGroup` was never flagged because `IsOrderedAddMonoid` needed it, and only the
      last link in the chain is visible. **Deletion remains the only test that cannot lie.**

- [ ] **complete `HARNESS.md` with code on desktop, post completed version to GitHub and send it to Benedikt.** The document is written (D17 commit)
      and is self-contained — it assumes no knowledge of this project and can be copied into the
      next one. What remains is publishing it somewhere readable and asking if he sees rules that break anything.  
      Ship `Lean/Linters.lean` alongside it; the document tells you to copy both.

Ideas, not commitments:
- [ ] Prove the failure cases in §5.3 of `Corollaries.lean` rather than documenting them
      (they are currently prose, having been fake `True := trivial` theorems — see D14).
- [ ] `mirrlees_lipschitz` takes the derivative bound as a hypothesis. It could be *derived*
      from bounded incomes plus continuity of `h` and `g'` on the relevant compact.
- [ ] `hW` could be specialised: in the Myerson setting it is literally right-continuity of
      `q`, and a helper lemma `myerson_hW_of_rightContinuous` would make that visible to
      callers rather than leaving them to unfold the composite.

## Done

- [x] **Two linters for statements that say nothing** (D17). `Lean/Linters.lean`.
      `linter.trueStatement` warns on any conclusion that is `True` — D14's exact failure, which
      **all 16 default linters pass in silence** (tested). Live on the library: clean build, zero
      false positives over 132 declarations. `witnessless` reports `@[needs_witness]` theorems with
      no `@[witness_for]`. Both advisory, neither a gate — see D17 for why an error would be worse.
      **Neither detects vacuity; that is undecidable.** The defence remains instantiation (D7).
- [x] **`A` needs only an order** (D16). `[AddCommGroup A]` and `[IsOrderedAddMonoid A]` were
      carried by all 27 declarations touching `A` and used by **none**. They were the residue of
      the *spread monotonicity* field (deleted in D1/D2), which was the only thing that ever
      subtracted in `A`. Removed; `lake build` clean, zero sorries, axioms unchanged —
      **verified by deletion**, not by grep. The cost was real while it lasted: the binder is
      why `MyersonAlloc := ℝ` rather than `Set.Icc 0 1`, i.e. **an unused typeclass had dictated
      a modelling choice**. Found by the user asking how a probability could be an abelian group.
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
