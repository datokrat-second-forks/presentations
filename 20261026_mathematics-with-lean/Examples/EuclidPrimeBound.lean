import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Worked example: Euclid's bound on the `n`-th prime

Let `p n` be the `n`-th prime, counted from `p 0 = 2`. Euclid's argument gives
`p (n+1) ≤ p 0 * ⋯ * p n + 1`: the smallest prime factor of the right-hand side divides none of
`p 0, …, p n`, so it is a prime that is larger than `p n`. With induction this gives a doubly
exponential bound.

| version   | statement           |
|-----------|---------------------|
| version 0 | `p n ≤ 4 ^ 2 ^ n`   |
| version 1 | `p n ≤ 2 ^ 2 ^ n`   |

The constant `2` is optimal for bounds of the form `c ^ 2 ^ n`, because `p 0 = 2`.

The proof has two independent parts:

* the number theory: the lemma `euclid`, which does not mention the bound;
* the arithmetic: the lemma `prod_lt`, `∏_{i<n} c ^ 2 ^ i < c ^ 2 ^ n`.

When the bound changes from `4` to `2`, Lean reports an error only at the single line of the main
proof that uses the arithmetic lemma. The number theory needs no rechecking.

The failed attempt is recorded below with `#guard_msgs`, which checks that Lean really reports
the documented error. In a live demo, edit the theorem in place instead.

The bound is very weak (Bertrand's postulate gives `p n ≤ 2 ^ (n + 1)`). The point here is the
structure of the argument, not the strength of the bound.
-/

namespace EuclidPrimeBound

/-- The `n`-th prime, counted from `p 0 = 2`. -/
noncomputable abbrev p (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- Euclid's argument: `p (n+1) ≤ p 0 * ⋯ * p n + 1`.

Let `P = p 0 * ⋯ * p n` and let `q` be the smallest prime factor of `P + 1`. If `q` divides `P`,
then `q` divides `1`, which is false. Thus `q` is not one of `p 0, …, p n`. Because `q` is the
`k`-th prime for `k = Nat.count Nat.Prime q`, this gives `n + 1 ≤ k` and thus
`p (n+1) ≤ p k = q ≤ P + 1`. -/
theorem euclid (n : ℕ) : p (n + 1) ≤ (∏ i ∈ Finset.range (n + 1), p i) + 1 := by
  set P := ∏ i ∈ Finset.range (n + 1), p i
  have hP : 0 < P := Finset.prod_pos fun i _ =>
    (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i).pos
  set q := (P + 1).minFac
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqP : ¬ q ∣ P := by
    intro h
    have : q ∣ 1 := (Nat.dvd_add_right h).1 (Nat.minFac_dvd (P + 1))
    exact hq.one_lt.ne' (Nat.dvd_one.1 this)
  have hk : n + 1 ≤ Nat.count Nat.Prime q := by
    by_contra h
    apply hqP
    rw [← Nat.nth_count hq]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega))
  calc p (n + 1) ≤ p (Nat.count Nat.Prime q) := Nat.nth_monotone Nat.infinite_setOfPred_prime hk
    _ = q := Nat.nth_count hq
    _ ≤ P + 1 := Nat.minFac_le (by omega)

/-! ## Version 0: `p n ≤ 4 ^ 2 ^ n` -/

/-- The arithmetic lemma for base `4`: `∏_{i<n} 4 ^ 2 ^ i < 4 ^ 2 ^ n`.
The induction step uses `4 ^ 2 ^ (n+1) = 4 ^ 2 ^ n * 4 ^ 2 ^ n`. -/
theorem prod_lt (n : ℕ) : ∏ i ∈ Finset.range n, 4 ^ 2 ^ i < 4 ^ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_range_succ, pow_succ, pow_mul, sq]
    exact Nat.mul_lt_mul_of_pos_right ih (by positivity)

/-- Version 0. The proof is a chain of inequalities (`calc`), one line for each step of the paper
proof: Euclid's argument, the induction hypothesis for every factor (`gcongr`), and the
arithmetic lemma. Here strong induction is necessary, because the induction hypothesis is used
for all `i ≤ n`. -/
theorem p_le_four (n : ℕ) : p n ≤ 4 ^ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      calc p (n + 1) ≤ (∏ i ∈ Finset.range (n + 1), p i) + 1 := euclid n
        _ ≤ (∏ i ∈ Finset.range (n + 1), 4 ^ 2 ^ i) + 1 := by
          gcongr with i hi
          exact ih i (by simp at hi; omega)
        _ ≤ 4 ^ 2 ^ (n + 1) := prod_lt (n + 1)

/-! ## Version 1: `p n ≤ 2 ^ 2 ^ n`

First attempt: replace `4` with `2` in the statement and in the `calc` chain. The base case,
Euclid's argument and the `gcongr` step are still correct. Lean reports an error only in the last
line: `prod_lt` is a statement about base `4`, not about base `2`.
-/

/--
error: Type mismatch
  prod_lt (n + 1)
has type
  ∏ i ∈ Finset.range (n + 1), 4 ^ 2 ^ i < 4 ^ 2 ^ (n + 1)
but is expected to have type
  ∏ i ∈ Finset.range (n + 1), 2 ^ 2 ^ i + 1 ≤ 2 ^ 2 ^ (n + 1)
-/
#guard_msgs in
theorem p_le_two_attempt (n : ℕ) : p n ≤ 2 ^ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      calc p (n + 1) ≤ (∏ i ∈ Finset.range (n + 1), p i) + 1 := euclid n
        _ ≤ (∏ i ∈ Finset.range (n + 1), 2 ^ 2 ^ i) + 1 := by
          gcongr with i hi
          exact ih i (by simp at hi; omega)
        _ ≤ 2 ^ 2 ^ (n + 1) := prod_lt (n + 1)

/-- The arithmetic lemma for every base `c ≥ 2`. Only the base case of the proof changes: it now
needs `1 < c`. The induction step is the same as in `prod_lt`. -/
theorem prod_lt' (c : ℕ) (hc : 2 ≤ c) (n : ℕ) :
    ∏ i ∈ Finset.range n, c ^ 2 ^ i < c ^ 2 ^ n := by
  induction n with
  | zero => simp; omega
  | succ n ih =>
    rw [Finset.prod_range_succ, pow_succ, pow_mul, sq]
    exact Nat.mul_lt_mul_of_pos_right ih (by positivity)

/-- Version 1. The fix: use the general lemma `prod_lt'` in the last line. Nothing else changes. -/
theorem p_le_two (n : ℕ) : p n ≤ 2 ^ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      calc p (n + 1) ≤ (∏ i ∈ Finset.range (n + 1), p i) + 1 := euclid n
        _ ≤ (∏ i ∈ Finset.range (n + 1), 2 ^ 2 ^ i) + 1 := by
          gcongr with i hi
          exact ih i (by simp at hi; omega)
        _ ≤ 2 ^ 2 ^ (n + 1) := prod_lt' 2 le_rfl (n + 1)

end EuclidPrimeBound
