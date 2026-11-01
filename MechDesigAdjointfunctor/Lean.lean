module

public import MechDesigAdjointfunctor.Lean.Basic

@[expose] public section

/-!
# MechDesigAdjointfunctor — Root Import

A Lean 4 formalisation of the categorical unification of Myerson's Revenue
Equivalence Theorem and the Mirrlees Taxation Principle as instances of a single
Master Theorem about the adjunction T ⊣ Q: the transfer functor T is the left adjoint of the
allocation functor Q (see `DECISIONS.md` D3 for why it is not the other way round).

## Module structure

| File | Contents |
|------|----------|
| `Framework` | Stage 1 — categories Mech, Alloc; functor Q; Lemma 1.7 |
| `MyersonSetting` | Stage 2 — Myerson auction; SC; Lemma 2.1 |
| `MirrleesSetting` | Stage 3 — Mirrlees taxation; SC-M; Lemma 3.1 |
| `MasterTheorem` | Stage 4 — Transfer Functor T; adjunction T ⊣ Q; Lemma 1.8; Theorem 4.5 |
| `Corollaries` | Stage 5 — Revenue Equivalence; Taxation Principle |
-/
