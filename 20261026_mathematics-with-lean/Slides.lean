import VersoSlides
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open VersoSlides

/-
# Intro

Proof assistants are software tools that verify a proof in a formal system.

In this talk, I will show you why and how to use a proof assistant called Lean.

# How Lean Works

* You write *definitions*, *statements* and *proofs*
* Foundation: dependent type theory; a statement is a type, a proof is a term of that type
* *Tactics* construct proof terms step by step, from small steps (`rw`) to automation
  (`simp`, `linarith`, `grind`)
* A small *kernel* checks the finished proof term: you only need to trust the kernel
* *Mathlib* supplies the definitions and theorems of everyday mathematics


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
* A formalized proof shifts the burden: check that the statement says what it should
* Definitions and statements stay human-readable; the proof can be arbitrarily long

:::notes
TODO: Pick an example.
:::

# PFR: From 12 to 11

* November 2023: Gowers, Green, Manners and Tao prove PFR over $`\mathbb{F}_2^n` with $`2K^{12}` cosets.
  The Lean formalization takes three weeks.
* December 2023: in a blog comment, Jyun-Jie Liao proposes a refinement that gives $`2K^{11}`.
* Tao's first step: the proof fixed $`\eta = 1/9`. He made $`\eta` a parameter (6 files, about 85 lines):

```code diff
-noncomputable def η := (9:ℝ)⁻¹
 structure refPackage :=
   …
+  η : ℝ
+  hη: 0 < η
+  hη': 8 * η < 1

-      · apply (mul_le_mul_left (by norm_num [η])).mpr lem611c
+      · apply (mul_le_mul_left p.hη).mpr lem611c

-theorem tau_strictly_decreases_aux : d[X₁ # X₂] = 0 := by
-  have hη : η = 1/9 := by rw [η, one_div]
+theorem tau_strictly_decreases_aux (hpη: p.η = 1/9): d[X₁ # X₂] = 0 := by
```

:::fragment
Lean finds every use of the value. Most steps only need $`0 < \eta`; the step that really needs
$`\eta = 1/9` now says so in its statement.
:::

:::notes
Commit 29a4d44 in `teorth/pfr` (9 December 2023): "Refactor proof to allow for variable eta". Tao on
Zulip that evening: "I have refactored the proofs accordingly and it looks like everything compiles."
Liao's comment is on Tao's blog post "On a conjecture of Marton" (13 November 2023).
:::

# PFR: Splitting the Work

* Same day: Tao writes the new argument into the blueprint and adds Lean stubs, "a dozen or so
  additional tasks outstanding"
* 11–17 December: Sébastien Gouëzel writes most of the new proof (about 1,600 lines). It reuses the
  existing estimates, which now hold for every $`\eta < 1/8`.
* The limit case $`\eta = 1/8` needs a new argument: a compactness argument for a limit of minimizers
* 19 December: the consequences switch to the new theorem, and their constants improve too:

```code diff
-  obtain ⟨H, c, hcS, hHA, hAcH⟩ := PFR_conjecture hA_nonempty hA_le
+  obtain ⟨H, c, hcS, hHA, hAcH⟩ := PFR_conjecture_improv hA_nonempty hA_le

-  ∃ (φ : G →+ G') (T : Set G'), Nat.card T ≤ 4 * (Nat.card S:ℝ)^(24:ℝ) ∧ ∀ x : G, (f x) - (φ x) ∈ T
+  ∃ (φ : G →+ G') (T : Set G'), Nat.card T ≤ 4 * (Nat.card S:ℝ)^(22:ℝ) ∧ ∀ x : G, (f x) - (φ x) ∈ T
```

:::notes
Sources: `teorth/pfr`, file `PFR/ImprovedPFR.lean`: stubs in commit 5a2fed7 (9 December), Gouëzel's
branches `SG_improved1`–`3`, and the switch of `HomPFR` in commit d751ff4 (19 December). The
homomorphism form of PFR goes from $`4K^{24}` to $`4K^{22}`. Later, Liao lowered the exponent to 9
(arXiv:2404.09639, April 2024); formalizing that version was still in progress at the time of the
README.
:::

# Alt. A: Partial Sums of $`\sum 1/k^2`

The Basel sum is $`\pi^2/6 \approx 1.645`. By induction, with a telescoping estimate:
$`\sum_{k=1}^n 1/k^2 \le 2 - 1/n`.

```lean
-- !hide
namespace Basel
-- !end hide
theorem step (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / n - 1 / (n + 1) := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_sub_div _ _ (by positivity) (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem sum_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linarith [step n hn]
-- !hide
end Basel
-- !end hide
```

:::notes
Alternative to the Euclid example (from `Examples/BaselBound.lean`); keep one of them.
:::

# Alt. A: Tightening the Bound

Replace $`2` with $`7/4`:

```lean +error
-- !hide
namespace Basel.Attempt
-- !end hide
theorem step (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / n - 1 / (n + 1) := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_sub_div _ _ (by positivity) (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem sum_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 ≤ /- !fragment changed -/7 / 4/- !end fragment -/ - 1 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linarith [step n hn]
-- !hide
end Basel.Attempt
-- !end hide
```

:::fragment
Lean marks only the base case: for $`n = 1`, the claim is $`1 \le 3/4`. The induction step needs
no rechecking.
:::

# Alt. A: The Fix

Start the induction at $`n = 2`; the induction step and `step` stay the same.

```lean
-- !hide
namespace Basel.Fix
-- !end hide
theorem step (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / n - 1 / (n + 1) := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_sub_div _ _ (by positivity) (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem sum_le (n : ℕ) (hn : /- !fragment changed -/2/- !end fragment -/ ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 ≤ 7 / 4 - 1 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Finset.sum_Icc_succ_top]
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linarith [step n (by omega)]
-- !hide
end Basel.Fix
-- !end hide
```

# Alt. A: Tightening Further

Back to $`n \ge 1`, with the bound $`5/3 - 1/(n + 1/2)`:

```lean +error
-- !hide
namespace Basel.Attempt2
-- !end hide
theorem step (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / n - 1 / (n + 1) := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_sub_div _ _ (by positivity) (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem sum_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 ≤ /- !fragment changed -/5 / 3 - 1 / ((n : ℝ) + 1 / 2)/- !end fragment -/ := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linarith [step n hn]
-- !hide
end Basel.Attempt2
-- !end hide
```

:::fragment
Now the base case holds, and Lean marks the induction step: the telescoping estimate is too weak.
:::

# Alt. A: The Fix

A sharper telescoping estimate; the base case stays the same.

```lean
-- !hide
namespace Basel.Fix2
-- !end hide
theorem step (n : ℕ) :
    1 / ((n : ℝ) + 1) ^ 2 ≤ /- !fragment changed -/1 / (n + 1 / 2) - 1 / (n + 1 + 1 / 2)/- !end fragment -/ := by
  rw [div_sub_div _ _ (by positivity) (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem sum_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 ≤ 5 / 3 - 1 / ((n : ℝ) + 1 / 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linarith [/- !fragment changed -/step n/- !end fragment -/]
-- !hide
end Basel.Fix2
-- !end hide
```

# Alt. B: The Recurrence $`a_{n+1} = a_n + 1/a_n`

Squaring gives $`a_{n+1}^2 = a_n^2 + 2 + 1/a_n^2`, so by induction $`a_n^2 \le 3n + 1`:

```lean
-- !hide
namespace Recurrence
-- !end hide
noncomputable def a : ℕ → ℝ
  | 0 => 1
  | n + 1 => a n + 1 / a n

theorem one_le_a (n : ℕ) : 1 ≤ a n := by /- !replace … -/
  induction n with
  | zero => simp [a]
  | succ n ih =>
    have : 0 < 1 / a n := one_div_pos.2 (by linarith)
    rw [a]
    linarith
/- !end replace -/
theorem a_succ_sq (n : ℕ) : a (n + 1) ^ 2 = a n ^ 2 + 2 + 1 / a n ^ 2 := by /- !replace … -/
  have : a n ≠ 0 := by linarith [one_le_a n]
  rw [a]
  field_simp
  ring
/- !end replace -/

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
-- !hide
end Recurrence
-- !end hide
```

:::notes
Alternative to the Euclid example (from `Examples/SqrtRecurrence.lean`); keep one of them.
:::

# Alt. B: Tightening the Bound

Replace $`3n + 1` with $`(7n + 5)/3`, which holds for $`n \ge 1`:

```lean +error
-- !hide
namespace Recurrence.Attempt
-- !end hide
theorem one_le_a (n : ℕ) : 1 ≤ a n := by /- !replace … -/
  induction n with
  | zero => simp [a]
  | succ n ih =>
    have : 0 < 1 / a n := one_div_pos.2 (by linarith)
    rw [a]
    linarith
/- !end replace -/
theorem a_succ_sq (n : ℕ) : a (n + 1) ^ 2 = a n ^ 2 + 2 + 1 / a n ^ 2 := by /- !replace … -/
  have : a n ≠ 0 := by linarith [one_le_a n]
  rw [a]
  field_simp
  ring
/- !end replace -/

theorem upper' (n : ℕ) /- !fragment changed -/(hn : 1 ≤ n)/- !end fragment -/ :
    a n ^ 2 ≤ /- !fragment changed -/(7 * n + 5) / 3/- !end fragment -/ := by
  induction /- !fragment changed -/n, hn using Nat.le_induction/- !end fragment -/ with
  | /- !fragment changed -/base => norm_num [a]/- !end fragment -/
  | succ n /- !fragment changed -/hn/- !end fragment -/ ih =>
    have : 1 / a n ^ 2 ≤ 1 := by
      rw [div_le_one (by nlinarith [one_le_a n])]
      nlinarith [one_le_a n]
    rw [a_succ_sq]
    push_cast
    linarith
-- !hide
end Recurrence.Attempt
-- !end hide
```

:::fragment
Lean marks only the induction step: $`1/a_n^2 \le 1` is too weak, it needs $`1/a_n^2 \le 1/3`.
:::

# Alt. B: The Fix

Use the lower bound $`a_n^2 \ge 2n + 1`, which is already proved:

```lean
-- !hide
namespace Recurrence
-- !end hide
theorem lower (n : ℕ) : 2 * n + 1 ≤ a n ^ 2 := by /- !replace … -/
  induction n with
  | zero => simp [a]
  | succ n ih =>
    have : 0 ≤ 1 / a n ^ 2 := by positivity
    rw [a_succ_sq]
    push_cast
    linarith
/- !end replace -/

theorem upper' (n : ℕ) (hn : 1 ≤ n) :
    a n ^ 2 ≤ (7 * n + 5) / 3 := by
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
-- !hide
end Recurrence
-- !end hide
```

# Clarification and Simplification

* Formalization forces you to make every hidden assumption explicit
* Dependencies become explicit: you see exactly which lemmas a result uses
* Abstractions that make the formal proof easier often make the informal proof clearer too
* Example: the Liquid Tensor Experiment led to simplifications of the original argument

:::notes
TODO: Concrete examples of simplifications from LTE. One follows on the next slide (Commelin's
complex).
:::

# Commelin's Complex

* Clausen–Scholze compute Ext groups with a *Breen–Deligne resolution*. It is not explicit, and
  its existence needs stable homotopy theory.
* The LTE team formalized only the properties of the resolution that the proof actually uses.
* Johan Commelin wrote down an explicit object with these properties:
  * terms $`\mathbb{Z}[A^{2^i}]`
  * differentials defined recursively from sums and projections
  * the required homotopies are identity maps
  * about 100 lines of Lean
* Lean forced the abstraction. Scholze then saw that the explicit complex suffices for the whole
  proof, so the formal proof avoids Breen–Deligne resolutions and stable homotopy theory.

:::fragment
> "What Johan realized is that one can actually give a nice and completely explicit object satisfying those axioms, and this is good enough for all the intended applications." — Peter Scholze, June 2021
:::

:::notes
Details and sources: `lte-commelin-complex.md`. The complex is in `src/breen_deligne/eg.lean` of
`lean-liquid` (first version on 11 December 2020, six days after the challenge). In 2022 a
comparison lemma replaced exactness by a condition that the explicit complex satisfies; the
complex is then used as Mac Lane's $`Q'`-construction. The quote is from Scholze's "Half a year
of the Liquid Tensor Experiment", checked only through Avigad's "Mathematics and the formal turn".

Commelin on Zulip (#general › Community blog), when Buzzard suggested emphasizing that formalizing
made them abstract the properties they needed, as de Jong did for resolution of singularities:
"it's been a subtle interplay between me abstracting the properties we needed, and Scholze
immediately recognizing that all the pieces fit together. … Lean forced me to do the
abstraction, but it didn't help us with connecting the existing puzzle pieces when it comes to
this Breen-Deligne lemma." And: "Where I see genuine help from Lean is in untangling the rest of
the proof. … I wasn't able to find that path without Lean."
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


# What Does a Lean Proof Prove?
%%%
autoAnimate := true
%%%

A near-fitting puzzle piece is easy to miss…

```html
<div class="puzzle-stage">
  <img class="puzzle-pieces big" data-id="puzzle-pieces"
       src="images/puzzle-1-in-isolation.webp" alt="Two puzzle pieces that seem to fit">
</div>
```

# What Does a Lean Proof Prove?
%%%
autoAnimate := true
%%%

:::fragment (index := 1)
…but not when you try to fill out the whole puzzle.
:::

```html
<div class="puzzle-stage">
  <img class="puzzle-full fragment" data-fragment-index="1"
       src="images/puzzle-2-in-the-bigger-picture.webp" alt="The two pieces in the whole puzzle">
  <img class="puzzle-pieces small" data-id="puzzle-pieces"
       src="images/puzzle-1-in-isolation.webp" alt="Two puzzle pieces that seem to fit">
  <img class="puzzle-full fragment" data-fragment-index="2"
       src="images/puzzle-3-where-it-belongs.webp" alt="Where the piece belongs">
</div>
```

:::notes
The pieces shrink to their place in the puzzle (auto-animate). Next step: the whole puzzle fades in
around them; the pieces stay on top. Last step: where the piece belongs.
:::

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
Recent examples: the quasi-Riemann hypothesis formalization was checked with Comparator
(CoolRmal/quasi-riemann-seven-eighths). Counterpoint: "Navier-Stokes lost in translation"
(Bastounis, Circelli, Hansen, October 2026) argues that a verified Lean proof of an
autoformalized statement does not guarantee the correctness of the natural-language proof.
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
-/

-- The limit counts the inline `/- !fragment … -/` markers, which are not shown on the slides.
set_option verso.code.warnLineLength 130

#doc (Slides) "Mathematics with Lean" =>

# Mathematics with Lean

Paul Reichert

# A First Proof: Euclid

```lean
-- !hide
namespace Euclid
-- !end hide
/-- The `n`-th prime, counted from `p 0 = 2`. -/
noncomputable abbrev p (n : ℕ) : ℕ := Nat.nth Nat.Prime n

-- !fragment
theorem euclid (n : ℕ) : p n ≤ (∏ i ∈ Finset.range n, p i) + 1 := by
  set P := ∏ i ∈ Finset.range n, p i
  have hP : 0 < P := Finset.prod_pos fun i _ =>
    (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i).pos
  set q := (P + 1).minFac
  have hq : q.Prime := Nat.minFac_prime (by grind)
  have hqP : ¬ q ∣ P := by
    intro h
    have : q ∣ 1 := (Nat.dvd_add_right h).1 (Nat.minFac_dvd (P + 1))
    exact hq.one_lt.ne' (Nat.dvd_one.1 this)
  have hk : n ≤ Nat.count Nat.Prime q := by
    by_contra h
    apply hqP
    rw [← Nat.nth_count hq]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by grind))
  calc p n ≤ p (Nat.count Nat.Prime q) := Nat.nth_monotone Nat.infinite_setOfPred_prime hk
    _ = q := Nat.nth_count hq
    _ ≤ P + 1 := Nat.minFac_le (by grind)
-- !hide
end Euclid
-- !end hide
```

:::notes
The smallest prime factor `q` of `P + 1` divides none of `p 0, …, p (n - 1)`, so it is a prime that is at least
`p n`. Show the goal state in the info panel. Worked example: `Examples/EuclidPrimeBound.lean`.
:::

# A Recent History of Proof Formalization

{image "static/images/math-timeline.svg" (class := "timeline")}[Lean in mathematics]

:::notes
Generated by `scripts/math-timeline.py`; edit the events there. The style and the milestones up
to 2023 follow the timeline in Leo de Moura's Marktoberdorf 2026 lectures. The Mathlib curve is
counted from the git histories (all lines of .lean files, monthly): Mathlib 3 until July 2023,
then Mathlib 4. The step in August 2023 is real: at the end of the port, Mathlib 3 had 1.09M
lines and Mathlib 4 had 1.26M, because the same mathematics takes more lines in Lean 4 syntax.
TODO: Check the dates (in particular Equational Theories, Carleson).
2026 results, both AI-generated with Lean formalizations and not yet independently refereed:
Navier–Stokes (OpenAI, 8 September 2026): finite-time blowup for the *forced* 3D equations; the
unforced Clay problem is still open. Quasi-Riemann hypothesis (OpenAI, 6 October 2026): no zeros
of zeta with real part greater than 7/8; community checks with Comparator.
FLT (AI): Anthropic, announced early September 2026. Claude formalized FLT in about 11 days
(about 13M lines of Lean, following Darmon–Diamond–Taylor, a classical route). Kevin Buzzard compiled it
and ran Comparator: "it checks out". The human FLT project (Imperial, 2024–2029) continues: its
goal is a modern, maintainable route and Mathlib-quality infrastructure, not only the final
theorem. Say so explicitly, since the two boxes invite the reading that one ended the other.
:::

# Liquid Tensor Experiment

December 2020, Peter Scholze (on the XENA Project blog):

> I want to propose a challenge: Formalize the proof of the following theorem.

*Theorem 1.1 (Clausen–S.)* Let $`0<p'<p\leq 1` be real numbers, let $`S` be a profinite set, and let $`V` be a $`p`-Banach space. Let $`\mathcal M_{p'}(S)` be the space of $`p'`-measures on $`S`. Then $`\mathrm{Ext}^i_{\mathrm{Cond}(\mathrm{Ab})}(\mathcal M_{p'}(S),V)=0` for $`i\geq 1`.

> I spent much of 2019 obsessed with the proof of this theorem, almost getting crazy over it.
In the end, we were able to get an argument pinned down on paper,
but I think nobody else has dared to look at the details of this,
and so I still have some small lingering doubts.

> I think the theorem is of utmost foundational importance, so being 99.9% sure is not
enough. As it will be used as a black box, a mistake in this proof could remain
uncaught.

* The challenge: formalize the main theorem of liquid vector spaces (Clausen–Scholze)
* The *Liquid Tensor Experiment*: a community effort with Lean, led by Johan Commelin

# A Recent History of Proof Formalization

{image "static/images/math-timeline.svg" (class := "timeline")}[Lean in mathematics]

# Liquid Tensor Experiment

After a year of work, the proof had been fully formalized and verified.

> One day I was sweating a little bit. The proof walks a fine line, so if some argument needs
constants that are quite a bit different from what I claimed, it might have collapsed.

In the course of the formalization, the proof also got significantly simpler.

# Confidence in the Proof

> \[I\]t was exactly the interactions via the Zulip chat that convinced me that
a proper verification was going on. To me the computers didn’t matter at all,
it could also have been Ofer Gabber. If I simply got a blanket “This is all correct” stamp,
I would have been extremely suspicious, as I was completely sure that I made /some/ slips.

> Actually, there would be a very clear thing that might have gone wrong in this:
Namely, that the formalized theorem statement isn’t quite what you think it is.
The confidence that \[Theorem 9.4\] is correct comes from looking at this in some detail,
but also very much from seeing that during the process, they seemed to run
into all the little nasty details that I expected (and sometimes not).
When it is later proved that Theorem 9.4 implies the result of the challenge,
these problems will also become less important, as the statement of the main theorem is less technical,
so it should be somewhat easier to verify that all definitions are correct.

# What Does a Lean Proof Prove?
%%%
autoAnimate := true
%%%

A subtly incorrect definition is easy to miss…

```html
<div class="puzzle-stage">
  <img class="puzzle-pieces big" data-id="puzzle-pieces"
       src="images/puzzle-1-in-isolation.webp" alt="Two puzzle pieces that seem to fit">
</div>
```

# What Does a Lean Proof Prove?
%%%
autoAnimate := true
%%%

:::fragment (index := 1)
…but not when you try to build the whole theory around it.
:::

```html
<div class="puzzle-stage">
  <img class="puzzle-full fragment" data-fragment-index="1"
       src="images/puzzle-2-in-the-bigger-picture.webp" alt="The two pieces in the whole puzzle">
  <img class="puzzle-pieces small" data-id="puzzle-pieces"
       src="images/puzzle-1-in-isolation.webp" alt="Two puzzle pieces that seem to fit">
  <img class="puzzle-full fragment" data-fragment-index="2"
       src="images/puzzle-3-where-it-belongs.webp" alt="Where the piece belongs">
</div>
```

:::notes
The pieces shrink to their place in the puzzle (auto-animate). Next step: the whole puzzle fades in
around them; the pieces stay on top. Last step: where the piece belongs.
:::

# Liquid Tensor Experiment

Scholze's original proof relied on a complex object from stable homotopy theory, the Breen-Deligne complex.

During the formalization, Johan Commelin axiomatized the exact properties of this complex that
the proof relied on.

Then he noticed that it could be replaced with something much simpler.
It no longer required stable homotopy theory.

# Modifying a Proof: A Bound on the Primes

```lean
-- !hide
namespace Euclid
-- !end hide
theorem prod_lt (n : ℕ) : ∏ i ∈ Finset.range n, 4 ^ 2 ^ i < 4 ^ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_range_succ, pow_succ, pow_mul, sq]
    exact Nat.mul_lt_mul_of_pos_right ih (by positivity)

theorem p_le_four (n : ℕ) : p n ≤ 4 ^ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    calc p n ≤ (∏ i ∈ Finset.range n, p i) + 1 := euclid n
      _ ≤ (∏ i ∈ Finset.range n, 4 ^ 2 ^ i) + 1 := by
        gcongr with i hi
        exact ih i (by simp at hi; grind)
      _ ≤ 4 ^ 2 ^ n := prod_lt n
-- !hide
end Euclid
-- !end hide
```

:::notes
`prod_lt` is the arithmetic lemma `∏_{i<n} 4^(2^i) < 4^(2^n)`; `p_le_four` uses it in the last step.
:::

# Modifying a Proof: A Bound on the Primes

```lean +error
-- !hide
namespace Euclid.Attempt
-- !end hide
theorem prod_lt (n : ℕ) : ∏ i ∈ Finset.range n, 4 ^ 2 ^ i < 4 ^ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_range_succ, pow_succ, pow_mul, sq]
    exact Nat.mul_lt_mul_of_pos_right ih (by positivity)

theorem p_le_two (n : ℕ) : p n ≤ /- !fragment changed -/2/- !end fragment -/ ^ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    calc p n ≤ (∏ i ∈ Finset.range n, p i) + 1 := euclid n
      _ ≤ (∏ i ∈ Finset.range n, /- !fragment changed -/2/- !end fragment -/ ^ 2 ^ i) + 1 := by
        gcongr with i hi
        exact ih i (by simp at hi; grind)
      _ ≤ /- !fragment changed -/2/- !end fragment -/ ^ 2 ^ n := prod_lt n
-- !hide
end Euclid.Attempt
-- !end hide
```

# Modifying a Proof: A Bound on the Primes

```lean
-- !hide
namespace Euclid.Fixed
-- !end hide
theorem prod_lt /- !fragment changed -/(c : ℕ) (hc : 2 ≤ c)/- !end fragment -/ (n : ℕ) :
    ∏ i ∈ Finset.range n, /- !fragment changed -/c/- !end fragment -/ ^ 2 ^ i < /- !fragment changed -/c/- !end fragment -/ ^ 2 ^ n := by
  induction n with
  | zero => /- !fragment changed -/simp; grind/- !end fragment -/
  | succ n ih =>
    rw [Finset.prod_range_succ, pow_succ, pow_mul, sq]
    exact Nat.mul_lt_mul_of_pos_right ih (by positivity)

theorem p_le_two (n : ℕ) : p n ≤ 2 ^ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    calc p n ≤ (∏ i ∈ Finset.range n, p i) + 1 := euclid n
      _ ≤ (∏ i ∈ Finset.range n, 2 ^ 2 ^ i) + 1 := by
        gcongr with i hi
        exact ih i (by simp at hi; grind)
      _ ≤ 2 ^ 2 ^ n := prod_lt /- !fragment changed -/2 le_rfl/- !end fragment -/ n
-- !hide
end Euclid.Fixed
-- !end hide
```

:::notes
More worked examples with tightened bounds: `Examples/BaselBound.lean` (breaks the base case, then
the induction step) and `Examples/SqrtRecurrence.lean`.
:::

# Unused Hypotheses

```lean
-- !hide
namespace AmGm
-- !end hide
theorem am_gm_three (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    3 * (a * b * c) ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

theorem am_gm_four (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    4 * (a * b * c * d) ≤ a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (c ^ 2 - d ^ 2), sq_nonneg (a * b - c * d)]
-- !hide
end AmGm
-- !end hide
```

:::notes
`nlinarith` multiplies hypotheses with each other, so in the three-number case it uses `ha`, `hb`
and `hc`; without them it fails. In the four-number case, the three squares already give
$`a^4 + b^4 + c^4 + d^4 \ge 2a^2b^2 + 2c^2d^2 \ge 4abcd`. Dropping the hypotheses gives a stronger
theorem, but it has ripple effects: every proof that passes `ha hb hc hd` to `am_gm_four` breaks,
and Lean lists all of them.
:::

# Community Formalizations With Blueprints

A Lean _blueprint_ connects a human-readable outline of the proof with the Lean formalization.

* Experts without Lean experience write the blueprint.
* The core team translates the main theorems into Lean without proving them.
* Lean users pick single lemmas or definitions of the blueprint and formalize them.
* The dependency graph gives an overview over the progress of the project.

# Getting Started with Lean

* Join the Lean online community: [https://leanprover.zulipchat.com/](https://leanprover.zulipchat.com/)
* Play the Natural Number Game: [https://adam.math.hhu.de/#/g/leanprover-community/nng4](https://adam.math.hhu.de/#/g/leanprover-community/nng4)
* Write and check Lean code in the web: [https://live.lean-lang.org](https://live.lean-lang.org)
* Install a local development environment: [https://lean-lang.org/install/](https://lean-lang.org/install/)
* Read /Theorem Proving in Lean/: [https://lean-lang.org/theorem\_proving\_in\_lean4/](https://lean-lang.org/theorem_proving_in_lean4/)
* Check out `leanblueprint` by Patrick Massot: [https://github.com/PatrickMassot/leanblueprint](https://github.com/PatrickMassot/leanblueprint)
