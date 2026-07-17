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

### CI: the one gate that runs without being asked

`lake new`/`lake init` scaffolds three GitHub Actions workflows under `.github/workflows/`.
Keep them; they are the only check in this list that fires on a machine you do not control.

- **`lean_action_ci.yml`** — `leanprover/lean-action` on every `push` and `pull_request`. This is
  `lake build` (Rule 1) enforced server-side: a red run means the gate was violated, full stop,
  no "it built locally." It also runs `docgen-action`, which needs nothing from you but a clean
  build.
- **`update.yml`** — `workflow_dispatch`-only Mathlib-update bot. It opens a PR when a new
  Mathlib tag builds clean, an issue when it does not. Leave the `schedule:` trigger commented
  out unless you want unattended dependency bumps; this project runs it by hand.
- **`create-release.yml`** — tags a release whenever `lean-toolchain` changes on `main`/`master`.
  Harmless, no action needed.

None of these substitute for local verification — a green CI run only reconfirms Rule 1, it does
not check Rules 2–4 (sorries, axioms, silent weakening), which have no automated gate at all and
depend entirely on the discipline in this document.

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

## 6a. Session lifecycle — Start / Run / End

The documents in §6 are *what* to keep current. This is *when*. It is the workspace-standard
loop (see the `lean-econ-workflow` skill, if your environment has it) — copy the discipline even
if that skill is not installed where this project lands.

**Naming note.** The standard convention is `CLAUDE.md` plus four control files: `memory.md`
(live state — current phase, completed declarations, open sorries, blockers), `progress.md`
(append-only commit log), `plan.md` (phase-by-phase steps), and `decisions.md` (append-only
decision log — §6's `DECISIONS.md` rule applies to it verbatim: log the rejected alternative,
record before implementing). **Use this split in a new project** — it is the convention the rest
of the workspace already uses. `README.md` is not part of this list: it belongs to the repo, not
the workflow — every project has one regardless of which control-file convention it follows, and
it is written for a human reader, not maintained as session state.

### Start (every session)

1. Read `memory.md` **first**. If it is missing, warn and offer to reconstruct from git log and
   the `.lean` files; do not write Lean until it is restored.
2. Read `CLAUDE.md`. Confirm the project goal and the active phase.
3. Check tools: toolchain version against `lean-toolchain`, `lake build` resolves, key imports
   are available. If Lean is unavailable, say so — plan and doc work can continue, proofs cannot
   be verified.
4. Report current phase, last completed declaration, open blockers/sorries.
5. **Ask before writing Lean**: continue from where the project left off, or change
   assumptions/goals? Wait for confirmation.

New-project setup, one time only: `git init` and commit the scaffolding, `lake update` to
resolve path dependencies, `lake build` to confirm a green zero-sorry baseline **before** Phase 1
— see §10.

### Run (during a phase)

- One declaration at a time — definition or theorem, smallest viable step.
- Compiler-guided: drive proofs with the LSP / `lake build` / `lake env lean <File>`; search
  Mathlib (`leansearch`/`loogle`/`leanfinder`) before reinventing.
- Update `memory.md` **immediately** after each completed proof: move it to Completed, note the
  proof pattern if non-obvious.
- Never mark something done with a `sorry` — that is Rule 2 in §1, not a separate rule.
- Log design choices to `decisions.md` as they are made, not at phase end — see §6's rule,
  which applies here unchanged.
- **Track assumptions explicitly.** Quasilinearity, single-crossing, positive welfare weights,
  full support, finiteness, equilibrium existence — carry them as named hypotheses, list them
  under "Assumptions in Force," never silently strengthen.
- **Honesty constraint.** Never let a statement that is false or `sorry`'d in generality become
  load-bearing. If a clean theorem only holds under a model restriction, state and use the
  restricted version, and document the false general form rather than asserting it.
- If the project is declarative, results may be `noncomputable` and use classical choice — do
  not add `Decidable`/enumeration machinery for its own sake.
- Resolve ambiguities against existing decisions, not in isolation: consult a shared
  `DESIGN_*.md` if one exists (precedence: headline decisions > structural > resolved questions
  > local convenience); a choice that contradicts a higher tier must be reopened with the human,
  not overridden.

### End (phase complete, build green, 0 new sorries)

1. Update `memory.md`: move the phase's results into Completed, confirm 0 sorries or record each
   placeholder with a reason, note new proof patterns and assumptions invoked, set the next
   phase.
2. Append to `progress.md`: a summary row (`phase | date | tokens | cumulative | sorry-count`)
   and a structured commit block (fields: Phase, Completed, Sorries, Tokens, notes). Confirm
   every decision made this phase is in `decisions.md` — a decision made but not logged is the
   failure §6 calls "the one that gets skipped."
3. Commit, per §9's rule (end of phase, never mid-phase with a broken build):
   ```
   phase(N): <one-line summary, imperative, ≤72 chars>

   Phase: <N>
   Completed: <theorems/definitions>
   Sorries: <count> open (<names>)
   Tokens: ~<N>

   <approach notes / blocked items / hypotheses carried>
   ```
4. If the project keeps a dependency-graph snapshot, refresh it.
5. Confirm next-phase prerequisites (upstream names proved, dependencies built) before starting.

A session that ends mid-phase still updates the live-state and log files with partial state; the
full End sequence and the `phase(N)` commit happen only at phase completion.

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

This is the complete list — everything else in this document explains *why* one of these steps
exists. A next agent doing a cold instantiation should be able to execute this section alone.

1. **Scaffold the Lake project** (`lake new <pkg> math` or `lake init`, if not done already).
   This generates `lakefile.toml`, `lean-toolchain`, and `.github/workflows/` —
   `lean_action_ci.yml`, `update.yml`, `create-release.yml` — as-is; see §3's CI subsection for
   what each does. Do not hand-write these unless you have a specific reason to deviate.
2. **Pin the toolchain and Mathlib together.** `lean-toolchain` and the `[[require]] mathlib`
   `rev` in `lakefile.toml` must name the *same* release (e.g. both `v4.30.0`, not one `-rc`
   ahead of the other) — a mismatch is invisible until a build breaks on a machine that resolves
   dependencies fresh.
3. **Copy `HARNESS.md`** (this file — it is self-contained, see the header) **and
   `Lean/Linters.lean`** (§4). `import <YourLib>.Linters` from the library's base module so
   `linter.trueStatement` actually runs — a linter only fires in files that import it.
4. **Create `CLAUDE.md`** pointing at `HARNESS.md`, plus whatever is domain-specific (the
   framework being formalised, key Mathlib gaps already known, house conventions like line
   length). Use this project's `CLAUDE.md` as a template for shape, not content.
5. **Create the control files** from §6a: `memory.md`, `progress.md`, `plan.md`, `decisions.md`.
   `README.md` is separate — it is a repo file, not a workflow file, and every project has one
   regardless. Empty control files are fine; the discipline is populating them from the first
   commit, not what they start with.
6. **Confirm the gate is green *before* any real work**:
   - `lake build` clean — zero errors, zero warnings.
   - `#print axioms` on a trivial declaration — confirms the axiom set is the expected
     `[propext, Classical.choice, Quot.sound]` baseline before anything project-specific is
     added.
   - `lake exe runLinter <YourLib>` triaged to zero, or a written list of known-and-accepted
     findings — do not adopt it as a gate while it starts red (§3: "a gate that starts red is a
     gate nobody obeys").
   - Push once and confirm `lean_action_ci.yml` goes green on GitHub — this is the only check in
     the whole document that runs somewhere you do not control; confirm it *works*, not just
     that it exists.
7. **Run the Start sequence from §6a** on the first real session, even though `memory.md` will be
   near-empty — it is the same muscle you will need every session after.
8. Then, and only then, start formalising.

The point of step 6 is that a gate adopted after the mess exists is a gate that gets waived.
