import VersoSlides
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open VersoSlides

set_option verso.code.warnLineLength 100

#doc (Slides) "Mathematics with Lean" =>

# Mathematics with Lean

Paul Reichert

# Can a Computer Check a Proof?

December 2020, Peter Scholze:

> I spent much of 2019 obsessed with the proof of this theorem, almost getting crazy over it. In
> the end, we were able to get an argument pinned down on paper, but I think nobody else has dared
> to look at the details of this, and so I still have some small lingering doubts.

* The challenge: formalize the main theorem of liquid vector spaces (Clausen–Scholze)
* The *Liquid Tensor Experiment*: a community effort with the proof assistant Lean

:::notes
Alternative openings from the outline: "Can a computer check mathematical proofs?" as an open
question, or recent AI news.
TODO: Verify the quote against the "Liquid Tensor Experiment" post on the Xena blog.
:::

# About This Talk

1. What is Lean?
2. Timeline
3. Projects and benefits of mechanization
4. What does a Lean proof prove?
5. First steps with Lean

# Lean: A Short History

* 2013: Leonardo de Moura starts Lean at Microsoft Research
* 2017: Lean 3; the community starts *Mathlib*
* 2021: Lean 4, also a general-purpose programming language
* 2023: Mathlib is ported to Lean 4; the Lean FRO is founded
* Today: Mathlib has more than two million lines

:::notes
TODO: Check dates and the current size of Mathlib.
:::

# How Lean Works

* You write *definitions*, *statements* and *proofs*
* Foundation: dependent type theory; a statement is a type, a proof is a term of that type
* *Tactics* construct proof terms step by step, from small steps (`rw`) to automation
  (`simp`, `linarith`, `grind`)
* A small *kernel* checks the finished proof term: you only need to trust the kernel
* *Mathlib* supplies the definitions and theorems of everyday mathematics

# A First Proof: Euclid

```lean
-- !hide
namespace Euclid
-- !end hide
/-- The `n`-th prime, counted from `p 0 = 2`. -/
noncomputable abbrev p (n : ℕ) : ℕ := Nat.nth Nat.Prime n

-- !fragment
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
-- !hide
end Euclid
-- !end hide
```

:::notes
The smallest prime factor `q` of `P + 1` divides none of `p 0, …, p n`, so it is a prime larger
than `p n`. Show the goal state in the info panel. Worked example: `Examples/EuclidPrimeBound.lean`.
:::

# Timeline

* 2019: perfectoid spaces are defined in Lean
* 2020–2022: Liquid Tensor Experiment
* 2023: Polynomial Freiman–Ruzsa conjecture, formalized within weeks of the preprint
* 2024: Equational Theories Project; start of the Fermat's Last Theorem project
* 2024–2025: AI systems solve olympiad problems with proofs checked by Lean

:::notes
TODO: Check dates; add current events.
:::

# Projects and Benefits

*Hypothesis:* If you can quickly become confident that a result is correct, you can rely on it
without the risk that a mistake invalidates your work.

# Confidence in a Subtle Argument

* Lean checks every step, so only the *statement* needs human review
* Liquid Tensor Experiment:
  * June 2021: the key technical part is verified
  * July 2022: the full challenge is complete

:::notes
TODO: Scholze quote from "Half a year of the Liquid Tensor Experiment".
:::

# Deciding Whether a Disputed Proof Deserves Attention

* Refereeing a long proof by an unknown author is expensive
* A mechanized proof shifts the burden: check that the statement says what it should
* Definitions and statements stay human-readable; the proof can be arbitrarily long

:::notes
TODO: Pick an example.
:::

# Modifying a Proof: A Bound on the Primes

From Euclid's argument by strong induction: $`p_n \le 4^{2^n}`.

```lean
-- !hide
namespace Euclid
theorem prod_lt (n : ℕ) : ∏ i ∈ Finset.range n, 4 ^ 2 ^ i < 4 ^ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_range_succ, pow_succ, pow_mul, sq]
    exact Nat.mul_lt_mul_of_pos_right ih (by positivity)
-- !end hide
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
-- !hide
end Euclid
-- !end hide
```

:::notes
`prod_lt` is the arithmetic lemma `∏_{i<n} 4^(2^i) < 4^(2^n)`. It is hidden on the slide.
:::

# Tightening the Bound

Replace $`4` with $`2`:

```lean +error
-- !hide
namespace Euclid.Attempt
-- !end hide
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
        _ ≤ 2 ^ 2 ^ (n + 1) := prod_lt (n + 1)
-- !hide
end Euclid.Attempt
-- !end hide
```

:::fragment
Lean marks only the last line. Euclid's argument and the induction need no rechecking.
:::

# The Fix

Generalize the arithmetic lemma; nothing else changes.

```lean
-- !hide
namespace Euclid
-- !end hide
theorem prod_lt' (c : ℕ) (hc : 2 ≤ c) (n : ℕ) :
    ∏ i ∈ Finset.range n, c ^ 2 ^ i < c ^ 2 ^ n := by
  induction n with
  | zero => simp; omega
  | succ n ih =>
    rw [Finset.prod_range_succ, pow_succ, pow_mul, sq]
    exact Nat.mul_lt_mul_of_pos_right ih (by positivity)

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
-- !hide
end Euclid
-- !end hide
```

:::notes
More worked examples with tightened bounds: `Examples/BaselBound.lean` (breaks the base case, then
the induction step) and `Examples/SqrtRecurrence.lean`.
:::

# Clarification and Simplification

* Formalization forces you to make every hidden assumption explicit
* Dependencies become explicit: you see exactly which lemmas a result uses
* Abstractions that make the formal proof easier often make the informal proof clearer too
* Example: the Liquid Tensor Experiment led to simplifications of the original argument

:::notes
TODO: Concrete examples of simplifications from LTE.
:::

# Collaboration

* Clear interfaces: a Lean statement means the same thing to everyone, so there are no mismatches
  between contributors
* No high barriers of entry: Lean checks the contributions, so you can accept work from people
  you do not know
* The infrastructure:
  * a GitHub repository
  * a Zulip chat for discussion
  * tasks that people claim
  * pull requests
  * automated CI checks

# Blueprints

A *blueprint* pairs a human-readable outline of the proof with the Lean mechanization.

* People without Lean experience write the blueprint
* Lean users formalize the individual statements
* The core team sets up skeletons for the targets
* The dependency graph shows what is done and what is ready to be worked on

:::notes
TODO: Show a blueprint live (for example the Fermat's Last Theorem or PFR blueprint) and explain
what working with it looks like.
:::

# What Does a Lean Proof Prove?

_Image: puzzle with one near-fitting piece_

* A near-fitting puzzle piece is easy to miss
* It is not easy to miss when you try to fill out the whole puzzle

# Where the Analogy Fails

_Image: one informal and one formal puzzle piece_

* Lean does tell us when two pieces fit together
* It does not tell us whether together they say what we expect
* So one piece is the informal mathematics, the other is the formal statement:
  humans check that these fit

# Comparator

* Given: a challenge file with the statements, and a solution file with the proofs
* Comparator checks that the solution proves exactly the challenge statements, with only the
  standard axioms
* So the human review is limited to the challenge file

:::notes
TODO: Check the details of `leanprover/comparator` before the talk.
:::

# First Steps with Lean

* *Natural Number Game*: learn the basics in the browser
* `live.lean-lang.org`: try Lean in the browser without installing anything
* VS Code with the Lean 4 extension
* *Mathematics in Lean*: an introduction to formalization with Mathlib
* The Lean Zulip chat: ask questions, find projects
* AI?

# AI and Lean

* Lean gives an automatic, reliable check of a proof
* This makes it a good target for AI systems that generate proofs
* What does this mean for the mathematical community?

:::notes
Optional section, depending on the interest of the audience.
:::

# Thank You

Questions?
