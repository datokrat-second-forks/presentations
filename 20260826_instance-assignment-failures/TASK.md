# Handoff: Instance Assignment Failures slides

## Goal

Create a standalone Verso deck about the Mathlib RT/EIT experiment.

The deck is for Lean core developers who understand the old behavior. It must show one example for each diagnosis category.

Each example must reproduce the failure. Use selective traces to show the mechanism. Use original Mathlib definitions unless a smaller example is necessary.

The deck title is **Instance Assignment Failures**. The author is Paul Reichert. The date is 2026-08-26.

## Project paths

- Slides project: `/root/presentations/20260826_instance-assignment-failures`
- Lean worktree: `/root/lean4/julia-minimal`
- Mathlib worktree: `/root/mathlib4/julia-minimal`
- Rendered deck: `/root/presentations/20260826_instance-assignment-failures/_slides/index.html`
- Original investigation report: `/root/static/rt-eit-failure-modes.html`
- Experiment notes: `/root/lean4/julia-minimal/.claude/rt-eit-task/TASK.md`

The project `lean-toolchain` points to `/root/lean4/julia-minimal/build/release/stage1`.

The project requires Mathlib from `/root/mathlib4/julia-minimal`.

## User decisions

- Make a standalone deck.
- Use all ten diagnosis categories, with frequent categories first.
- Put the quantitative breakdown near the start.
- Do not add a diagnosis summary at the end.
- Always show the failure case.
- Disable all new adjustments when that gives the clearest failure.
- State explicitly when an example keeps an adjustment enabled.
- Keep traces small, but preserve the failure mechanism.
- Use exact predecessor imports or isolated modules when later imports can change tactic sets.
- Preserve hover information in the rendered slides.
- Remove the proof-shape slide from the current proofreading version.
- Discuss uncertain presentation changes before implementation.

## Diagnosis counts

The audit started with 53 declarations.

- RT annotation debt: 18
- Initial EIT regressions: 35
- Default-instance exemption: 17
- Abandoned goals: 7
  - blocked searches: 5
  - real value mismatches: 2
- Dependent assignment order: 4
- Types unified too late: 2
- Fallback timeout: 2
- Inference-order flip: 1
- Proof-shape coupling: 1
- Ordinary-unification stuck: 1

The three Lean adjustments resolve 26 of the 35 initial EIT regressions. Nine declarations still need local EIT exemptions.

## Lean options added for the deck

The Lean worktree contains three uncommitted, default-on options:

```text
backward.isDefEq.respectTransparency.elabInstanceTypes.exemptDefaultInstances
backward.isDefEq.respectTransparency.elabInstanceTypes.unmarkAbandoned
backward.isDefEq.respectTransparency.elabInstanceTypes.unifyTypesFirst
```

Files:

- `src/Lean/Elab/SyntheticMVars.lean`
- `src/Lean/Meta/ExprDefEq.lean`
- `tests/elab/elabInstanceTypeAdjustments.lean`

The options gate these three behavior changes:

1. Exempt assignments from the default-instance pass.
2. Unmark abandoned typeclass metavariables.
3. Unify assignment types before the strict instance check.

The Lean build completed successfully after these changes.

These focused tests passed:

```bash
tests/with_stage1_test_env.sh tests/elab/run_test.sh elabInstanceTypeAdjustments.lean
tests/with_stage1_test_env.sh tests/elab/run_test.sh elabInstanceTypes.lean
```

## Current deck structure

`Deck.lean` contains the title, the quantitative breakdown, the option overview, category slides, and the final residual count.

The current proofreading version omits the proof-shape slide. The breakdown and final residual count still include that category.

Live isolated examples exist for these categories:

1. RT annotation debt
2. Abandoned blocked search
3. Dependent assignment order
4. Types unified too late
5. Fallback timeout
6. Inference-order flip
7. Ordinary-unification stuck

The default-instance and abandoned-value categories currently use focused static excerpts. Their original Mathlib examples are large.

Each live example uses `leanModules` with a local Lake package. This keeps Mathlib imports isolated between examples.

## Performance work

The first rendered HTML file was 45 MB. It contained approximately 215,000 hover payloads.

The proof-shape slide contributed approximately 35.9 MB. Its filter retained large `isDefEq` subtrees.

After removal of that slide and tighter trace scopes, the rendered file decreased to approximately 234 KB. Hover support remained enabled.

The next RT correction increased the last rendered file to approximately 1.24 MB. The increase comes from the `SupHomClass` synthesis trace.

Do not disable server mode. The user wants hover information.

## Current unresolved issue: RT trace display

The RT example originally used the wrong namespace. That version failed because `mixedSpace` and `normAtPlace` were unknown.

The correct namespace is:

```lean
namespace NumberField.mixedEmbedding
```

A standalone probe at `/tmp/RTProbe.lean` verified the intended failure.

The failure occurs at `map_finset_sup'` in the `rw` list. The trace contains a failed synthesis request:

```text
SupHomClass ?m.46 ?m.47 ?m.48
```

The trailing `simp` is not relevant.

The current source traces only the `rw` tactic:

```lean
(set_option trace.Meta.synthInstance true in
  rw [← coe_nnnorm, nnnorm_eq_sup_normAtPlace, ← sup'_eq_sup univ_nonempty,
    ← NNReal.val_eq_coe, ← OrderHom.Subtype.val_coe, map_finset_sup',
    OrderHom.Subtype.val_coe])
```

The direct `postprocess_traces` command filters for `SupHomClass` and uses `hoist`.

Verso attached the trace message to an early token in the `rw` list. The user could not see the trace in the slide infoview.

A `store_traces_as` prototype moved the trace to an explicit command. The user rejected this direction before review.

The source no longer contains `store_traces_as` or `#postprocess_traces`.

Do not split the rewrite list without discussion. The user asked to discuss that approach first.

The source now uses `end mixedEmbedding`. The previous rendered HTML still contains an unintended full-name `end` error.

## Build state

The last complete deck build succeeded before the final direct-trace restoration.

The final source restoration has not completed a full deck build. Two later builds were stopped for discussion.

The current rendered HTML is stale. It does not exactly match `Deck.lean`.

Before presenting a new proofreading version, run:

```bash
cd /root/presentations/20260826_instance-assignment-failures
lake build
lake exe slides
```

Then make sure that the RT slide has these properties:

- No unknown-identifier error for `mixedSpace`.
- No unknown-identifier error for `normAtPlace`.
- No scope-name error at `end`.
- The error points to the rewrite near `map_finset_sup'`.
- The trace contains the failed `SupHomClass` search.
- The trace is accessible in the slide infoview.

Do not report completion until all properties are confirmed from the rendered HTML.

## Verso compatibility patches

Current Verso main does not build unchanged with this experimental Lean worktree.

The project records two patches:

- `patches/verso-z85.patch`
- `patches/verso-slides-module-path.patch`

The first patch avoids a `grind` error in the Z85 encoder.

The second patch preserves dependency paths when Verso extracts isolated modules. It includes fixed local Lean and Mathlib paths.

Apply the patches after `lake update`:

```bash
./prepare-dependencies.sh
```

The `.lake/packages/verso` and `.lake/packages/verso-slides` repositories are intentionally dirty because these patches are applied.

## Repository state and cautions

The presentation repository root is `/root/presentations`. It already contains unrelated changes in `fro-template`.

Do not modify or commit those unrelated changes.

The Lean worktree also contains unrelated local files:

- `.claude/CLAUDE.md`
- `.claude/rt-eit-task/`

Do not modify or commit them as part of the slides task.

The Mathlib worktree contains at least these local changes:

- `Mathlib/CategoryTheory/Preadditive/CommGrp_.lean`
- `lean-toolchain`

Treat all current filesystem changes as authoritative.

## Recommended next discussion

First, agree on the intended interaction for trace messages in a slide code block.

Questions:

1. Which visible token must open the `SupHomClass` trace?
2. Must the trace appear automatically in the panel, or only after token selection?
3. Can the original `rw` list be split if the proof state and failure mechanism remain unchanged?

After this discussion, implement only the agreed trace-anchor design. Then rebuild and inspect the rendered HTML.
