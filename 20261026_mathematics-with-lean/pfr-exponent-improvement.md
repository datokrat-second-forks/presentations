# PFR: The Exponent Improvement from 12 to 11

Background notes for the slides "PFR: From 12 to 11" and "PFR: Splitting the Work". Collected on
2026-10-26 from the `teorth/pfr` git history, the PFR Zulip channel, Tao's blog and arXiv.

## The mathematics

* **PFR over $\mathbb{F}_2^n$** (Gowers, Green, Manners, Tao; arXiv:2311.05762, 13 November 2023):
  If $A \subseteq G = \mathbb{F}_2^n$ is non-empty and $|A+A| \le K|A|$, then $A$ is covered by at most
  $2K^{C}$ cosets of a subgroup $H$ with $|H| \le |A|$. The original proof gives $C = 12$.
* **Liao's refinement to $C = 11$:** Jyun-Jie Liao posted it as a
  [comment on Tao's blog post "On a conjecture of Marton"](https://terrytao.wordpress.com/2023/11/13/on-a-conjecture-of-marton/#comment-682353).
  It is not a separate preprint. The published GGMT paper credits Liao with the improvement of
  $C = 12$ in Theorem 1.2 to $C = 11$.
* **Later, $C = 9$:** Liao, "Improved Exponent for Marton's Conjecture in $\mathbb{F}_2^n$",
  arXiv:2404.09639 (15 April 2024, one version). The README of `teorth/pfr` says that the
  formalization of this refinement is in progress. Its current state is not checked.

### The role of $\eta$

The proof minimizes the functional

$$\tau[X_1; X_2] = d[X_1; X_2] + \eta\, d[X^0_1; X_1] + \eta\, d[X^0_2; X_2]$$

over pairs of $G$-valued random variables. The main step shows that minimizers have Ruzsa distance
$k = d[X_1; X_2] = 0$.

* **Original argument:** $\eta = 1/9$ was fixed, and it gives the entropic constant
  $2 + 1/\eta = 11$ and the exponent 12.
* **Improved argument** (`tau_strictly_decreases'`, needs $0 < \eta < 1/8$): with the new estimates
  (`averaged_construct_good`, `dist_diff_bound`) one gets

  $$k \le 8\eta k - \frac{(1 - 5\eta - \tfrac46\eta)(2\eta k - I_1)}{1-\eta},$$

  and the subtracted term is nonnegative by the old `first_estimate` ($I_1 \le 2\eta k$). For
  $\eta < 1/8$ this forces $k = 0$.
* **Why $\eta = 1/8$ needs a separate argument:** at $\eta = 1/8$ the inequality only says
  $k \le k$, so it gives no information.
* **Constants as a function of $\eta$:** for any $\eta < 1/8$ the argument proves the entropic
  form with constant $2 + 1/\eta$ and PFR with exponent $3 + 1/\eta$. This is stated in the
  blueprint: "one can obtain the claim with 11 replaced by $3 + \frac{1}{\eta}$ for any
  $0 < \eta < 1/8$". Examples:
  * $\eta = 1/9$: exponent 12. This is the old result.
  * $\eta = 0.124$: exponent about 11.06.
  * $\eta = 1/8 - \varepsilon$: exponent about $11 + 64\varepsilon$.

  The statement allows real exponents. So without a limit argument one gets
  $2K^{11+\delta}$ for every $\delta > 0$. The limit is needed only to reach exactly 11.
  At $\eta = 1/8$ the entropic constant is $2 + 8 = 10$ (`entropic_PFR_conjecture_improv`).

### The limit argument

Two different arguments were used.

1. **Tao's blueprint (9 December 2023):** "send $\eta$ to $1/8$ and use the fact that there are
   only finitely many possible choices for the subspace $H$ to conclude."
2. **The formalized argument** (Gouëzel; blueprint commit 476be40 "cleanup blueprint",
   15 December 2023; Lean lemma `tau_minimizer_exists_rdist_eq_zero`):
   1. Choose $u_n \nearrow 1/8$. For each $n$, take $\tau$-minimizers for $\eta = u_n$. By
      `tau_strictly_decreases'` they have Ruzsa distance 0.
   2. $G$ is finite, so the space of pairs of probability measures on $G$ is compact. Extract a
      convergent subsequence of the distributions (`IsCompact.tendsto_subseq`).
   3. $\tau$ and $d$ are continuous in the measures and in $\eta$. So the limit is a pair of
      $\tau$-minimizers for $\eta = 1/8$ with distance 0.

   Blueprint wording: "By compactness of the space of probability measures on $G$, one may
   extract a converging subsequence of the distributions of $X_1^\eta$ and $X_2^\eta$ as
   $\eta \to 1/8$. By continuity of all the involved quantities, the limit is a pair of
   tau-minimizers for $1/8$ satisfying additionally $d[X_1;X_2] = 0$."

   After this lemma, the rest of the PFR proof runs unchanged with $\eta = 1/8$.

So the person doing the mechanization replaced the limit argument with one that was easier to
formalize.

## Timeline of the formalization

All commits are in [`teorth/pfr`](https://github.com/teorth/pfr). Tao's timestamps are Pacific
time; Gouëzel's are CET.

| Date (2023) | Event | Reference |
|---|---|---|
| 13 Nov | GGMT preprint; Tao starts the Lean project in the same week | arXiv:2311.05762 |
| 18 Nov | Tao's blog post on the blueprint workflow (written before the 12 → 11 change, which it does not mention) | [blog](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/) |
| early Dec | The formalization of PFR with exponent 12 is complete: "succeeded after three weeks" | [Mathstodon](https://mathstodon.xyz/@tao/111526765350663641) |
| 8 Dec 21:09 | Blueprint chapter for the exponent-11 argument | commit 6f80356 "Added blueprint for exponent 11 argument" |
| 9 Dec 00:57 | Zulip announcement of the two extensions, including Liao's refinement | Zulip, "PFR extensions" |
| 9 Dec 12:43 | **$\eta$ refactor**: $\eta$ becomes a parameter | commit 29a4d44 "Refactor proof to allow for variable eta" |
| 9 Dec 14:38 | Stubs: new file `PFR/ImprovedPFR.lean` (139 lines, `proof_wanted` and `sorry`) | commit 5a2fed7 "added improvedPFR stubs" |
| 9 Dec 15:02 | `examples.lean` updated with the 11 statement | commit eb815bd |
| 9 Dec 23:04 | Zulip: the argument "is now fully written up in the blueprint, and stubs to code are in the lean files" | Zulip, "PFR extensions" |
| 11 Dec 17:47 | Gouëzel starts | commit 1bb22e4 "start on improved PFR" (branch `SG_improved1`) |
| 15 Dec | "complete proof of improved exponent"; blueprint changed to the compactness argument | commits d7b6033, 476be40 |
| 17 Dec 17:05 | Gouëzel's final cleanup | commit 1d55f0c (branch `SG_improved3`, PR #149) |
| 19 Dec 13:31 | Consequences switch to the improved theorem | commit d751ff4 "Add examples, reroute PFR to PFR_improv" |

The exact completion date is not important for the talk. The README says only that this "second
stage has also been completed."

### Who wrote what in `PFR/ImprovedPFR.lean` (9–19 December, from `git log --numstat`)

| Author | Commits | Lines added |
|---|---|---|
| Sébastien Gouëzel (`sgouezel`) | 16 | about 1,590 |
| Terence Tao (`teorth`) | 8 | about 195 |
| Yaël Dillies | 2 | about 10 |

At commit d751ff4 the file has 1,037 lines and no `sorry`. The added lines include rewrites, so
they add up to more than the final size.

### Size compared to the whole project

Line counts of all `.lean` files, including comments and docstrings:

| State | All `.lean` files | Without `PFR/ForMathlib` and `PFR/Mathlib` |
|---|---|---|
| 5 December (7b00fc6, first phase complete, exponent 12) | 11,094 | 6,230 |
| 8 December (6f80356, just before the extension) | 10,911 | 6,147 |
| 19 December (d751ff4) | 13,735 | not counted |

The growth to 19 December also includes other extensions: approximate homomorphisms, weak PFR over
$\mathbb{Z}$, and Paul Lezeau's additive-energy work.

So the final `ImprovedPFR.lean` (1,037 lines) is about a tenth of the whole project as of
5 December, or about a sixth of its PFR-specific part. The roughly 1,600 added lines include
rewrites. The $\eta$ refactor before it changed only 85 lines.

Tao worked on an unrelated refactor (`entropy_refactor`, removing finiteness assumptions, PR #148)
in parallel during the same week.

## Commit excerpts

### The $\eta$ refactor (29a4d44, 9 December)

The commit changes 7 files, +85/−82. Of these, 6 are Lean files: `Endgame`, `EntropyPFR`,
`FirstEstimate`, `Main`, `SecondEstimate`, `TauFunctional`. The 7th is the blueprint.

The definition becomes a parameter of the reference package:

```diff
-/-- The constant eta that will be fixed once and for all in the rest of the argument.
-Taking `η = 1/9` works fine for the final computations. -/
-noncomputable def η := (9:ℝ)⁻¹
 structure refPackage :=
   …
+  η : ℝ
+  hη: 0 < η
+  hη': 8 * η < 1
```

Most proofs only needed positivity. Lean flags every place where the value was used:

```diff
-      · apply (mul_le_mul_left (by norm_num [η])).mpr lem611c
+      · apply (mul_le_mul_left p.hη).mpr lem611c
```

```diff
-  refine' mul_le_mul_of_nonneg_left _ (by rw [η]; positivity)
+  refine' mul_le_mul_of_nonneg_left _ (by linarith [p.hη])
```

The step that really needs the value now states it as a hypothesis. The hypothesis propagates to
`tau_strictly_decreases` and to `entropic_PFR_conjecture`:

```diff
-theorem tau_strictly_decreases_aux : d[X₁ # X₂] = 0 := by
-  have hη : η = 1/9 := by rw [η, one_div]
+theorem tau_strictly_decreases_aux (hpη: p.η = 1/9): d[X₁ # X₂] = 0 := by
```

At the use site in `Main.lean`:

```diff
-  let p : refPackage Ω₀ Ω₀ G := ⟨UA, UA, UAmeas, UAmeas⟩
+  let p : refPackage Ω₀ Ω₀ G := ⟨UA, UA, UAmeas, UAmeas, 1/9, (by norm_num), (by norm_num)⟩
```

Tao on Zulip, 9 December 20:46: "in the previous build, η was hardcoded to be 1/9. In preparation
for the extension in which we lower the PFR constant from 12 to 11, I have moved η into the
reference package p and it is now permitted to range between 0 and 1/8 exclusive, though some key
steps in our previous argument only apply when η = 1/9. I have refactored the proofs accordingly
and it looks like everything compiles."

### The stubs (5a2fed7, 9 December)

These are statements with blueprint docstrings. Some statements were not yet formalized and use
the placeholder `proof_wanted … : 0 = 1`:

```lean
proof_wanted construct_good_prelim' : 0 = 1
proof_wanted construct_good' : 0 = 1
proof_wanted averaged_construct_good : 0 = 1
proof_wanted gen_ineq: 0 = 1
proof_wanted dist_diff_bound : 0 = 1

theorem tau_strictly_decreases' : d[X₁ # X₂] = 0 := sorry

theorem PFR_conjecture' (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
     ∃ (H : AddSubgroup G) (c : Set G),
      Nat.card c < 2 * K ^ 11 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  sorry
```

The Zulip task list "Outstanding tasks, version 6.0" (9 December) contains these items:

* **Proof tasks:** "Constructing good variables, I′/II′/III′", "General inequality", "Bound on
  distance differences", "Improved tau decrement", "Entropy form of PFR′", and "Improved PFR". The
  last one is described as a "Straightforward modification of PFR, with one additional limiting
  argument needed to send eta to 1/8."
* **Statement and documentation tasks**, among them "Here the sum involves 12 terms, one may need to
  think about the cleanest way to express this formula."

### The final step reuses the old estimates (d751ff4)

`tau_strictly_decreases_aux'` combines new lemmas with `first_estimate`, which is unchanged apart
from the refactor and now holds for every $\eta$, and with `second_estimate_aux`:

```lean
theorem tau_strictly_decreases_aux' (hp : 8 * p.η < 1) : d[X₁ # X₂] = 0 := by
  have : 0 < p.η := p.hη
  have : k ≤ 8 * p.η * k := by calc
    k ≤ (6 * p.η * k - (1 - 5 * p.η) / (1 - p.η) * (2 * p.η * k - I₁))
        + p.η / 6 * (8 * k + 2 * (d[X₁ # X₁] + d[X₂ # X₂])) :=
      averaged_final p hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
    _ ≤ 6 * p.η * k - (1 - 5 * p.η) / (1 - p.η) * (2 * p.η * k - I₁) +
        p.η / 6 * (8 * k + 2 * (2 * (k + (2 * p.η * k - I₁) / (1 - p.η)))) := by
      gcongr
      exact second_estimate_aux p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂
        h_indep.reindex_four_abdc h_min
    _ = 8 * p.η * k - (1 - 5 * p.η - 4/6 * p.η) * (2 * p.η * k - I₁) / (1 - p.η) := by ring
    _ ≤ 8 * p.η * k := by
      simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
      apply div_nonneg _ (by linarith)
      apply mul_nonneg (by linarith) _
      linarith [first_estimate p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min]
  apply le_antisymm _ (rdist_nonneg hX₁ hX₂)
  nlinarith
```

Not everything was reused verbatim:

* `second_estimate` was split, and `second_estimate_aux` was factored out of it.
* Between 29a4d44 and d751ff4, `SecondEstimate.lean` and `Endgame.lean` changed by +53/−114 lines
  in total, partly through mathlib bumps and Tao's parallel refactor.
* `first_estimate` and `sum_condMutual_le` (Endgame) are used as they are.

### The consequences switch over (d751ff4, 19 December)

In `PFR/HomPFR.lean`:

```diff
-import PFR.Main
+import PFR.ImprovedPFR
 …
-  ∃ (φ : G →+ G') (T : Set G'), Nat.card T ≤ 4 * (Nat.card S:ℝ)^(24:ℝ) ∧ ∀ x : G, (f x) - (φ x) ∈ T := by
+  ∃ (φ : G →+ G') (T : Set G'), Nat.card T ≤ 4 * (Nat.card S:ℝ)^(22:ℝ) ∧ ∀ x : G, (f x) - (φ x) ∈ T := by
 …
-  obtain ⟨H, c, hcS, hHA, hAcH⟩ := PFR_conjecture hA_nonempty hA_le
+  obtain ⟨H, c, hcS, hHA, hAcH⟩ := PFR_conjecture_improv hA_nonempty hA_le
 …
-  have hG_card_le : Nat.card G ≤ 2*(Nat.card S:ℝ)^(12:ℝ) * Nat.card H₀
+  have hG_card_le : Nat.card G ≤ 2*(Nat.card S:ℝ)^(11:ℝ) * Nat.card H₀
```

The commit changes 7 files, +68/−56. The changed statements:

* **Homomorphism form:** $4K^{24} \to 4K^{22}$. This one is proved.
* **Approximate homomorphism form:** constants $C_1^{25} C_3^{24} K^{50C_4+48C_2} \to
  C_1^{21} C_3^{20} K^{46C_4+44C_2}$. It was still `sorry` at that point.
* **Weak PFR over $\mathbb{Z}$:** $K^{-48} \to K^{-44}$. Also still `sorry` or `proof_wanted` at
  that point.

`examples.lean` gains `#print axioms PFR_conjecture_improv`.

## Claims that are not verified or were retracted

* **Retracted:** a quote attributed to Tao's 18 November blog post ("one can simply replace 12 with
  11 in the theorem, and the compiler will then dutifully point out the dozen or so lines that now
  do not compile properly"). It came from a web-search summary. The blog post does not contain it,
  and it predates the 12 → 11 change. Do not use it.
* **Also not found:** "hundreds of lines of downstream code then had to be refactored". The source
  is unknown, so do not use it.
* **Lex Fridman Podcast #472** (June 2025): Tao recalls that a few weeks after a formalization,
  "someone said, oh, we can actually improve this 12 to an 11 by reworking some of these steps".
  He adds that with pen and paper, changing a parameter means rechecking every line. Only search
  snippets of this are available, because the transcript page was blocked by the proxy. Paraphrase
  it rather than quote it.
* **Three weeks and about 20 people:** "three weeks" is from Tao's Mathstodon post. "About 20
  people" is from his spoken account and is not checked against a written source.

## References

* GGMT, "On a conjecture of Marton", [arXiv:2311.05762](https://arxiv.org/abs/2311.05762)
* J.-J. Liao, "Improved Exponent for Marton's Conjecture in $\mathbb{F}_2^n$",
  [arXiv:2404.09639](https://arxiv.org/abs/2404.09639)
* Liao's blog comment:
  <https://terrytao.wordpress.com/2023/11/13/on-a-conjecture-of-marton/#comment-682353>
* Tao, "Formalizing the proof of PFR in Lean4 using Blueprint: a short tour" (18 November 2023):
  <https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/>
* Tao on Mathstodon, project completion: <https://mathstodon.xyz/@tao/111526765350663641>
* Repository: <https://github.com/teorth/pfr>. Local clone:
  `/root/downstream/mathematics-with-lean/pfr`. The key commits are 6f80356, 29a4d44, 5a2fed7,
  1bb22e4, d7b6033, 476be40, 1d55f0c and d751ff4. Files: `PFR/TauFunctional.lean`,
  `PFR/ImprovedPFR.lean`, `PFR/HomPFR.lean` and `blueprint/src/chapter/improved_exponent.tex`.
* Project page and blueprint: <https://teorth.github.io/pfr/>
* Zulip, PFR channel:
  * "PFR extensions":
    <https://leanprover-community.github.io/archive/stream/412902-Polynomial-Freiman-Ruzsa-conjecture/topic/PFR.20extensions.html>
  * "Outstanding tasks, version 8.0":
    <https://leanprover-community.github.io/archive/stream/412902-Polynomial-Freiman-Ruzsa-conjecture/topic/Outstanding.20tasks.2C.20version.208.2E0.html>
* Lex Fridman Podcast #472 with Terence Tao: <https://lexfridman.com/terence-tao>
