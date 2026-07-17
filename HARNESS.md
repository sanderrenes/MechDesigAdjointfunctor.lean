# HARNESS.md — the working agreement for an LLM-driven Lean 4 project

**Copy this file into the next project and follow it.** It is self-contained: it assumes no
knowledge of the project it came from. Where it cites evidence, the citation is to
`DECISIONS.md` of the *originating* project (a formalisation arguing that Myerson's Revenue
Equivalence and the Mirrlees Taxation Principle are one theorem) — the entries are named so you
can ask for them, but you do not need them to follow the rules.

---

## 0. What this is for, and why it is not a style guide

An LLM can write Lean far better than it can judge Lean. It knows the Mathlib lemma names, the
tactic idiom, the difference between `HasDerivAt` and `HasDerivWithinAt`. What it will not
reliably do is **let a failure speak**. Asked about an unprovable obligation, the first instinct
on offer is to make the obligation disappear — comment out the block, weaken the statement until
it compiles, report a dependency analysis that silently returned nothing.

Every one of those *destroys the finding*. In the originating project the single most valuable
object in the repository was a `sorry` that would not close, and the path of least resistance was
to delete it. It turned out not to be a proof gap: it was the category refusing an incorrect
definition, and it is the whole result.

**So the architecture is three parts, and it fails if you remove any one:**

| Part | Job | Fails how |
|---|---|---|
| The **model** | Translator. Writes the Lean. | Fluent and unreliable. Will make failures go away. |
| The **kernel** | Adjudicator. Decides if the proof proves the statement. | Cannot tell you the statement is the one you meant. |
| The **harness** | Keeps the cheap escape unavailable. | Is this document. |

The kernel is incorruptible *about the question it is asked*, and the author chooses the
question. **That seam is what this harness closes.** It is not a style guide, and none of it is
about making the Lean pretty.

---

## 1. The quality gate — every commit, no exceptions

1. **`lake build` clean.** No errors, no warnings.
2. **Zero sorries.** If a proof needs a `sorry`, **the statement is wrong** — fix the statement,
   or stop and say so. Do not "come back to it".
3. **Axioms are exactly `[propext, Classical.choice, Quot.sound]`.** Check with `#print axioms`
   on anything new. A custom axiom is a `sorry` wearing a hat, and is never acceptable without
   explicit human approval.
4. **Never weaken a theorem to make it compile without saying so** — in the commit message *and*
   in `DECISIONS.md`.

Rule 2 is the load-bearing one and it is worth being precise about why. A `sorry` typechecks. A
theorem quietly weakened until it goes through typechecks *perfectly*, and looks greener than the
honest one. Neither is visible in a build log. **Zero sorries is what converts "I could not prove
this" into "this statement is false" — which is the only way a formalisation ever tells you
something you did not already believe.** In the originating project that single rule turned a
proof gap into a refuted definition (D1, D2).

---

## 2. Verification: what is allowed to count as evidence

Two techniques produced **confidently wrong answers** in the originating project. Both looked
like clean results. Do not repeat them.

- **`ConstantInfo.value?` returns `none` for theorems** in some Lean versions. Walking proof
  terms to compute dependencies therefore silently returns nothing, and every probe comes back
  `false`. It does not error. It reports a tidy, complete, wrong answer.
- **A token scan misses real uses.** Anonymous constructors (`{ h := f.hAlloc }`), field
  projections (`m.hIC`) and instance resolution never name the declaration. A grep-built
  dependency graph showed a structure as an unused leaf when it was in fact the sole premise of
  the main functor.

**The reliable test is deletion.** Comment the declaration out, run `lake build`, see what
breaks. It cannot lie. Use it before claiming anything is unused, load-bearing, or vacuous.

> **The general rule: never report a property of the codebase you have not tested.** The failure
> mode is not that the model lies. It is that a plausible method returns a clean answer and
> nobody asks whether the method works. If you cannot test a claim, say you have not tested it.

---

## 3. Tooling — what it catches, and precisely what it does not

Run these. Then do not trust them.

```
lake build                                  # errors + elaboration warnings
lake exe runLinter <YourLib>                # 16 environment linters, whole library
#print axioms <decl>                        # axiom hygiene
#list_linters                               # what is available
```

`lake exe runLinter` ships with Batteries via Mathlib and works out of the box. It never gates
the build, so everything it says is advisory. **Triage its findings before adopting it as a
gate: a gate that starts red is a gate nobody obeys.**

### The measured blind spots

These are test results from the originating project, not impressions.

**Vacuous instance binders.** `unusedArguments` catches them on `def`s only — **never on
`structure`s, `instance`s or `theorem`s**, which is where definitions live. Of 27 vacuous
binders, it caught **1**. Worse, a *chain* of vacuous binders conceals itself: `[AddCommGroup A]`
was never flagged because `[IsOrderedAddMonoid A]` needed it — it was load-bearing for a binder
that was load-bearing for nothing. Only the last link is visible; removing it exposes the next
(D16).

**Statements that say nothing.** Of five planted failures, the 16 default linters caught **one**:

| Planted | Caught |
|---|---|
| `theorem foo (n : ℕ) : n = n := rfl` | yes — `synTaut` |
| `theorem foo : True := trivial` | **no** |
| Vacuous: `(h1 : n < 3) (h2 : 5 < n) : n = 42` | **no** |
| A theorem carrying a hypothesis it never uses | **no** |
| `(h : 0 < n) : n = n ∨ n ≠ n` | **no** |

`synTaut` fires only on literal `e = e`, which is far narrower than the name suggests.

### The conclusion to draw

**Every one of these checks syntax. Every real failure is semantic.** In the originating project:
a definition that was false (D1) — invisible. A hypothesis false for every reserve-price auction
(D7) — invisible. Theorems stating `True` (D14) — invisible. A vacuous binder (D16) — 1 of 27
visible. The machinery caught roughly one twenty-seventh of one of four findings. **Everything
else came from a human reading a statement and asking what it said, or from deleting something
and watching.**

The kernel checks the proof against the statement. The linters check the statement's *shape*.
**Nothing checks the statement's meaning.** That gap is the work.

---

## 4. Two linters worth copying

`Lean/Linters.lean` in the originating project is self-contained (~100 lines, imports only `Lean`
and `Batteries.Tactic.Lint`). Copy it. Both are **advisory by design** (D17):

- **`linter.trueStatement`** — a compiler **warning** on any declaration whose conclusion is
  `True`, after stripping `∀`s. Exact, decidable, zero false positives over 132 declarations.
  Opt out per-declaration with `set_option linter.trueStatement false in`.
- **`witnessless`** — an `@[env_linter]` reporting theorems tagged `@[needs_witness]` with no
  `@[witness_for]` aimed at them.

**Neither is a gate, and that is deliberate.** A `True` statement is occasionally an honest
placeholder; a rule that cannot be obeyed gets disabled wholesale, taking the signal with it.
"Zero sorries" is enforceable because it is never *right* to leave a `sorry`.

**Do not mistake `witnessless` for a vacuity checker.** Satisfiability of a hypothesis set is
undecidable; anything claiming otherwise is lying to you. It checks the weaker honest thing: that
you *said* an instance was owed and have not produced one.

To wire the warning into a library, the base file must `import` the linter module — a linter only
runs in files that import it. That couples the whole library to it, so keep it cheap and never
let it fail to compile.

---

## 5. The real defence against vacuity: instantiate

There is no tool. There is a practice, and it is the one that produced the best finding in the
originating project.

**Take the headline theorem and instantiate it at the object the field actually cares about.
Prove that object satisfies every hypothesis.**

That project's envelope theorem was originally stated with a two-sided derivative hypothesis, as
the literature states it. Instantiating it at a **posted price with reserve `p`** — the canonical
optimal auction — showed the surplus is `max(θ − p, 0)`: a kink, no derivative. The hypothesis
was not merely strong. It was **false for every auction with a reserve price**, so the theorem as
stated excluded the entire case of interest. `postedPrice_not_hasDerivAt` is now a theorem in
that repository (D7).

Nobody is *forced* to check that canonical examples satisfy their hypotheses, which is why this
survives in published work. **Force it.** A hypothesis set with no witness has never been shown
to be satisfiable, and a theorem about an empty set of objects is not a theorem about anything.

---

## 6. Documents you must keep current

A stale document is worse than none, because it will be trusted.

| File | Holds | Touch it |
|---|---|---|
| `TODO.md` | Living task list | **Every** commit that changes task status |
| `DECISIONS.md` | Append-only decision log | Whenever a choice is made **or reversed** |
| `PLAN.md` | Phases and acceptance criteria | When a phase starts, changes shape, or completes |
| `README.md` | The arc and proof status | When architecture or proof status changes |

### The `DECISIONS.md` rule, which is the one that gets skipped

**Log the alternative you rejected, and why.** A decision without its discarded alternative is
just a description, and the next session — human or model — will re-litigate it. Record the
decision **before** implementing, not after; a log written afterwards is a rationalisation.

Design decisions compound. Later ones must be consistent with earlier ones or they create
problems that take a long time to surface.

### Presentation artefacts are frozen

If the project has finished outputs — a talk, a paper, a diagram — they are **arguments, not
living documents**. Do not regenerate or "bring them up to date" on your own initiative. A
well-meant edit that drifts from the version being presented is worse than a stale one. If the
Lean changes in a way that falsifies something they claim, **put it in `TODO.md` and leave them
alone**.

---

## 7. Docstrings are prose. Lean does not check them.

When you change a definition, **read its docstring**. In the originating project one claimed
`V(θ_min) = 0` while the definition said `≥ 0` (D4). Another justified a modelling choice by
citing a typeclass requirement that had become vacuous two decisions earlier — so an unused
binder silently dictated the shape of the model, and the docstring kept explaining why (D16).

A comment the compiler does not attach is a comment nobody reads. Prose has no kernel.

---

## 8. The division of labour — state it honestly

It is easy to overclaim in both directions.

In the originating project the model did **not** discover that the definition was wrong. It
**could not close the obligation**, and the harness forbade it from pretending otherwise or
quietly deleting it. *Then* the human worked out why, and the "why" was a domain insight the
model did not have. **The machine supplied the obstruction. The human supplied the diagnosis.
Neither could have done both.**

Say it that way. The interesting claim is never "the AI proved a theorem". It is that a
formalisation **refused a definition nobody had ever been asked to justify** — and that requires
both parties.

---

## 9. Standing instructions to the agent

- **When a proof will not close, the first hypothesis is that the statement is wrong.** Not that
  you lack the tactic. Say so, and stop, before trying to engineer around it.
- **Never delete or comment out an obligation to make a build green.** That obligation is the
  most valuable object in the repository until proven otherwise.
- **Never report a codebase property you have not tested.** Prefer deletion-and-rebuild.
- **Never silently weaken.** If the statement had to shrink, that is the headline of the commit
  message, not a footnote.
- **Commit at the end of every phase, never mid-phase with a broken build.** The message states
  what changed *and what it cost*.
- **When you are uncertain, say which part you did not test.** "I have not verified this" is
  always an acceptable answer and is the one thing the model is systematically bad at offering.

---

## 10. Bootstrapping a new project

1. Copy `HARNESS.md` (this file) and `Lean/Linters.lean`.
2. Create `CLAUDE.md` pointing at this file, plus whatever is specific to the new domain.
3. Create empty `TODO.md`, `DECISIONS.md`, `PLAN.md`.
4. `import <YourLib>.Linters` from the base module so `linter.trueStatement` runs.
5. Confirm the gate is green *before* any real work: `lake build` clean, `#print axioms` on a
   trivial declaration, `lake exe runLinter <YourLib>` triaged to zero or a written list of
   known-and-accepted findings.
6. Then, and only then, start formalising.

The point of step 5 is that a gate adopted after the mess exists is a gate that gets waived.
