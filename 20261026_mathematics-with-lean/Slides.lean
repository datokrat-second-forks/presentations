import VersoSlides
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

open VersoSlides

set_option verso.code.warnLineLength 100

#doc (Slides) "Mathematics with Lean" =>

# Mathematics with Lean

Paul Reichert

# About This Talk

* For mathematicians who are curious about proof mechanization but have never tried it
* Plan:
  1. What is Lean?
  2. Why mechanize proofs?
     * Confidence in subtle arguments
     * Triage of disputed proofs
     * Clarification and simplification
  3. How to get started
  4. (On request) AI and Lean

# What Is Lean?

* A programming language and an interactive proof assistant
* You write definitions, statements and proofs; Lean checks every step
* A small trusted kernel: you only need to trust the kernel, not the tactics that produced the proof
* Mathlib: a community library of more than two million lines of formalized mathematics

:::notes
TODO: Check the current size of Mathlib before the talk.
:::

# A First Proof

```lean
-- !hide
open Finset
-- !end hide
#eval ∑ i ∈ range 101, i

-- !fragment
theorem gauss (n : ℕ) : 2 * ∑ i ∈ range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    ring
```

:::notes
Show the goal state in the info panel after each step. `sum_range_succ` is a Mathlib lemma;
`ring` proves identities in commutative (semi)rings.
:::

# The Computer Says No

```lean +error
-- !hide
open Finset
-- !end hide
theorem wrong (n : ℕ) : 2 * ∑ i ∈ range (n + 1), i = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    ring
```

:::notes
Lean does not accept a proof attempt of a false statement. The error message shows where the
argument breaks down.
:::

# Why Mechanize? Confidence

* Some arguments are too long or too subtle to check with full confidence by hand
* Lean checks every step, so only the *statement* needs human review
* Example: the Liquid Tensor Experiment
  * December 2020: Peter Scholze challenges the community to formalize a central theorem of
    liquid vector spaces (joint work with Dustin Clausen)
  * June 2021: the key technical part is verified
  * July 2022: the full challenge is complete

:::notes
TODO: Add the Scholze quote from "Half a year of the Liquid Tensor Experiment" (Xena blog).
:::

# Why Mechanize? Triage of Disputed Proofs

* Refereeing a long proof by an unknown author is expensive
* A mechanized proof shifts the burden: check that the statement says what it should
* Definitions and statements stay human-readable; the proof can be arbitrarily long

:::notes
TODO: Pick an example.
:::

# Why Mechanize? Clarification and Simplification

* Formalization forces you to make every hidden assumption explicit
* Abstractions that make the formal proof easier often make the informal proof clearer too
* Example: the Liquid Tensor Experiment led to simplifications of the original argument

:::notes
TODO: Concrete examples of simplifications from LTE.
:::

# Community Projects

* Liquid Tensor Experiment (2020–2022)
* Polynomial Freiman–Ruzsa conjecture (2023): formalized within weeks of the preprint
* Equational Theories Project (2024)
* Fermat's Last Theorem (ongoing)
* Blueprints: a dependency graph of informal statements makes it possible to split the work
  between many contributors

:::notes
TODO: Check dates and current status before the talk.
:::

# How to Get Started

* *Natural Number Game*: learn the basics in the browser
* *Mathematics in Lean*: an introduction to formalization with Mathlib
* *Theorem Proving in Lean 4*: the foundations
* The Lean Zulip chat: ask questions, find projects
* Formalize something you know well, in a small scope

# AI and Lean

* Lean gives an automatic, reliable check of a proof
* This makes it a good target for AI systems that generate proofs
* What does this mean for the mathematical community?

:::notes
Optional section, depending on the interest of the audience.
:::

# Thank You

Questions?
