import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Worked example: an upper bound for the partial sums of `∑ 1/k²`

The Basel problem says `∑_{k ≥ 1} 1/k² = π²/6 ≈ 1.645`. This file proves elementary upper bounds
for the partial sums `S n = ∑_{k=1}^n 1/k²` and then tightens them twice:

| version   | statement                     | limit as `n → ∞` |
|-----------|-------------------------------|------------------|
| version 0 | `S n ≤ 2 - 1/n` for `n ≥ 1`       | `2`              |
| version 1 | `S n ≤ 7/4 - 1/n` for `n ≥ 2`     | `1.75`           |
| version 2 | `S n ≤ 5/3 - 1/(n+½)` for `n ≥ 1` | `1.666…`         |

Every version is proved by induction on `n`, and every inductive step uses a telescoping estimate
for the new summand. Each tightening breaks a *different* part of the proof:

* version 0 → version 1 breaks only the **base case**. The induction step and the telescoping
  lemma `step` stay valid without change.
* version 1 → version 2 breaks only the **induction step**. The base case still holds, and the
  fix is a sharper telescoping lemma `step'`.

This illustrates how one iterates on a Lean proof: after an edit, Lean marks exactly the parts of
the argument that no longer hold, and the rest needs no rechecking.

The failed attempts are recorded below with `#guard_msgs`, which checks that Lean really reports
the documented error. In a live demo, edit the theorem in place instead.
-/

namespace BaselBound

/-! ## Version 0: `S n ≤ 2 - 1/n`

Paper proof. For `n = 1` both sides equal `1`. For the induction step it is sufficient to show
`1/(n+1)² ≤ 1/n - 1/(n+1)`, because then
`S (n+1) = S n + 1/(n+1)² ≤ (2 - 1/n) + (1/n - 1/(n+1)) = 2 - 1/(n+1)`.
The estimate holds because `1/n - 1/(n+1) = 1/(n(n+1))` and `n(n+1) ≤ (n+1)²`.
-/

/-- The telescoping estimate `1/(n+1)² ≤ 1/n - 1/(n+1)`. -/
theorem step (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / n - 1 / (n + 1) := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_sub_div _ _ (by positivity) (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Version 0. Things to look at in the infoview:

* After `induction`, there are two goals, `base` and `succ`. In the `succ` goal, the induction
  hypothesis appears as `ih`.
* After `rw [Finset.sum_Icc_succ_top …]`, the last summand is split off the sum.
* `linarith [step n hn]` combines `ih` with the telescoping estimate, as in the paper proof.

The cast `(n : ℝ)` in the statement is necessary: without it, Lean reads `1 / n` as division
of natural numbers, where `1 / n = 0` for `n ≥ 2`. -/
theorem sum_le_two (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linarith [step n hn]

/-! ## Version 1: `S n ≤ 7/4 - 1/n`

First attempt: replace `2` with `7/4` and change nothing else. Lean reports an error only in the
base case. The goal there is `S 1 ≤ 7/4 - 1/1`, that is `1 ≤ 3/4`, and `norm_num` reduces it to
`False`. Thus the proof is not merely incomplete: the statement is false for `n = 1`.
The induction step shows no error.
-/

/--
error: unsolved goals
case base
n : ℕ
⊢ False
-/
#guard_msgs in
theorem sum_le_seven_fourths_attempt (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 ≤ 7 / 4 - 1 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linarith [step n hn]

/-- Version 1. The fix: start the induction at `n = 2`, where `S 2 = 1 + 1/4 = 7/4 - 1/2` holds
with equality. The induction step and the lemma `step` are not changed. Only the call
`step n hn` needs the new proof `by omega` of `1 ≤ n` from `2 ≤ n`. -/
theorem sum_le_seven_fourths (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 ≤ 7 / 4 - 1 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Finset.sum_Icc_succ_top]
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linarith [step n (by omega)]

/-! ## Version 2: `S n ≤ 5/3 - 1/(n + ½)`

First attempt: change the statement and keep the proof of version 0. Now the base case is
correct (`1 ≤ 5/3 - 2/3` holds with equality), but `linarith` fails in the induction step.
The error message shows the induction hypothesis `ih` and the negated goal `a✝`. The old
telescoping estimate `1/n - 1/(n+1)` is too weak to get from `ih` to the new goal.
-/

/--
error: linarith failed to find a contradiction
case succ
n✝ n : ℕ
hn : 1 ≤ n
ih : ∑ k ∈ Finset.Icc 1 n, 1 / ↑k ^ 2 ≤ 5 / 3 - 1 / (↑n + 1 / 2)
a✝ : 5 / 3 - 1 / (↑n + 1 + 1 / 2) < ∑ k ∈ Finset.Icc 1 n, 1 / ↑k ^ 2 + 1 / (↑n + 1) ^ 2
⊢ False
failed
-/
#guard_msgs in
theorem sum_le_five_thirds_attempt (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 ≤ 5 / 3 - 1 / ((n : ℝ) + 1 / 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linarith [step n hn]

/-- The sharper telescoping estimate `1/(n+1)² ≤ 1/(n+½) - 1/(n+1+½)`. The right-hand side
equals `1/((n+1)² - ¼)`. The proof is the same as the proof of `step`.

The right-hand side is written as `n + 1 + 1/2`, not as `n + 3/2`, because this is the form in
which the term occurs in the goal. `linarith` does not identify the two forms. -/
theorem step' (n : ℕ) :
    1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n + 1 / 2) - 1 / (n + 1 + 1 / 2) := by
  rw [div_sub_div _ _ (by positivity) (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Version 2. The fix: use `step'` instead of `step`. The base case is not changed. The old
lemma `step` is still correct; it is no longer used. -/
theorem sum_le_five_thirds (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 ≤ 5 / 3 - 1 / ((n : ℝ) + 1 / 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linarith [step' n]

end BaselBound
