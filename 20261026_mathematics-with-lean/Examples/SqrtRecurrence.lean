import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Worked example: the recurrence `a (n+1) = a n + 1 / a n`

Let `a 0 = 1` and `a (n+1) = a n + 1 / a n`. Then `a n ~ √(2n)`. Squaring the recurrence gives

  `a (n+1)² = a n² + 2 + 1 / a n²`,

and the elementary bounds follow by induction:

| version   | statement                                          |
|-----------|----------------------------------------------------|
| version 0 | `2n + 1 ≤ a n² ≤ 3n + 1`                           |
| version 1 | `2n + 1 ≤ a n² ≤ (7n + 5)/3` (upper bound for `n ≥ 1`) |

For the upper bound in version 0 it is sufficient that `1 / a n² ≤ 1`, which follows from
`a n ≥ 1`. The sharper upper bound in version 1 needs `1 / a n² ≤ 1/3`, which follows from the
*lower* bound: `a n² ≥ 2n + 1 ≥ 3` for `n ≥ 1`.

When the upper bound is tightened, Lean reports an error only in the induction step of the upper
bound. The lemmas `one_le_a`, `a_succ_sq` and the lower bound stay valid. The fix uses the lower
bound, which was already proved, so it needs no further thought.

The failed attempt is recorded below with `#guard_msgs`, which checks that Lean really reports
the documented error. In a live demo, edit the theorem in place instead.
-/

namespace SqrtRecurrence

/-- The sequence `a 0 = 1`, `a (n+1) = a n + 1 / a n`. -/
noncomputable def a : ℕ → ℝ
  | 0 => 1
  | n + 1 => a n + 1 / a n

/-- All terms are at least `1`. In particular, `a n ≠ 0`, so the division is harmless. -/
theorem one_le_a (n : ℕ) : 1 ≤ a n := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    have : 0 < 1 / a n := one_div_pos.2 (by linarith)
    rw [a]
    linarith

/-- The squared recurrence `a (n+1)² = a n² + 2 + 1 / a n²`. -/
theorem a_succ_sq (n : ℕ) : a (n + 1) ^ 2 = a n ^ 2 + 2 + 1 / a n ^ 2 := by
  have : a n ≠ 0 := by linarith [one_le_a n]
  rw [a]
  field_simp
  ring

/-! ## Version 0: `2n + 1 ≤ a n² ≤ 3n + 1` -/

/-- The lower bound. It uses only `1 / a n² ≥ 0`. -/
theorem lower (n : ℕ) : 2 * n + 1 ≤ a n ^ 2 := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    have : 0 ≤ 1 / a n ^ 2 := by positivity
    rw [a_succ_sq]
    push_cast
    linarith

/-- The upper bound. It uses `1 / a n² ≤ 1`, which follows from `a n ≥ 1`. -/
theorem upper (n : ℕ) : a n ^ 2 ≤ 3 * n + 1 := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    have : 1 / a n ^ 2 ≤ 1 := by
      rw [div_le_one (by nlinarith [one_le_a n])]
      nlinarith [one_le_a n]
    rw [a_succ_sq]
    push_cast
    linarith

/-! ## Version 1: `a n² ≤ (7n + 5)/3` for `n ≥ 1`

The new bound is sharp for `n = 1`, where `a 1 = 2`. Because `a 0² = 1 > 5/3`, it does not hold
for `n = 0`, so the induction starts at `n = 1`.

First attempt: change the statement and the base case and keep the induction step. The base
case is correct. In the induction step, `linarith` fails. The error message shows the hypothesis
`this : 1 / a n ^ 2 ≤ 1`, which is now too weak: the step needs `1 / a n² ≤ 1/3`.
-/

/--
error: linarith failed to find a contradiction
case succ
n✝ n : ℕ
hn : 1 ≤ n
ih : a n ^ 2 ≤ (7 * ↑n + 5) / 3
this : 1 / a n ^ 2 ≤ 1
a✝ : (7 * (↑n + 1) + 5) / 3 < a n ^ 2 + 2 + 1 / a n ^ 2
⊢ False
failed
-/
#guard_msgs in
theorem upper_seven_thirds_attempt (n : ℕ) (hn : 1 ≤ n) : a n ^ 2 ≤ (7 * n + 5) / 3 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [a]
  | succ n hn ih =>
    have : 1 / a n ^ 2 ≤ 1 := by
      rw [div_le_one (by nlinarith [one_le_a n])]
      nlinarith [one_le_a n]
    rw [a_succ_sq]
    push_cast
    linarith

/-- Version 1. The fix: prove `1 / a n² ≤ 1/3` from the lower bound `lower n`. The rest of the
induction step is not changed. -/
theorem upper_seven_thirds (n : ℕ) (hn : 1 ≤ n) : a n ^ 2 ≤ (7 * n + 5) / 3 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [a]
  | succ n hn ih =>
    have : 1 / a n ^ 2 ≤ 1 / 3 := by
      have h₁ := lower n
      have h₂ : (1 : ℝ) ≤ n := by exact_mod_cast hn
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    rw [a_succ_sq]
    push_cast
    linarith

end SqrtRecurrence
