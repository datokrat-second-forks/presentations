# LTE: Commelin's Complex

Background notes for the slide "Commelin's Complex". Collected on 2026-10-27 from the
`leanprover-community/lean-liquid` git history and secondary sources. Scholze's blog post itself
was blocked by the proxy.

## The problem

* **The challenge:** Scholze posed the Liquid Tensor Experiment (LTE) on the Xena blog on
  5 December 2020. The target is Theorem 1.1 of Clausen–Scholze: for $0 < p' < p \le 1$, a
  profinite set $S$ and a $p$-Banach space $V$, $\mathrm{Ext}^i(\mathcal{M}_{p'}(S), V) = 0$ for
  $i \ge 1$.
* **The Ext computation:** Clausen–Scholze compute these Ext groups with a *Breen–Deligne
  resolution*. That is a functorial resolution of every abelian group $A$ by sums of free groups
  $\mathbb{Z}[A^n]$.
* **Why this is a problem for formalization:** the resolution is not explicit. Its existence uses
  stable homotopy theory, namely the homology of Eilenberg–MacLane spaces. Formalizing that would
  have been a large detour.

## Step 1: formalize only the properties the proof uses

The project formalized just the structure the argument uses, as "Breen–Deligne data" and
"Breen–Deligne packages" in `src/breen_deligne/`:

* **Universal maps:** finite $\mathbb{Z}$-linear combinations of integer matrices. They act
  functorially as $\mathbb{Z}[A^m] \to \mathbb{Z}[A^n]$ (`universal_map.lean`; the correspondence
  with functorial families of homomorphisms is in `functorial_map.lean`).
* **A package:** a complex of such maps, together with a homotopy between the two maps
  "sum" ($\sigma$) and "projections" ($\pi$) on the doubled complex.

The first half of the project (Theorem 9.4/9.5, "the part Scholze was unsure about") needs no
exactness. In Lean it is stated for an arbitrary package that satisfies suitability conditions on
the constants (`first_target` in `src/liquid.lean`). The README of the folder notes: "this
directory does _not_ contain a proof of the Breen-Deligne theorem".

## Step 2: Commelin's explicit complex

File `src/breen_deligne/eg.lean` (124 lines in the final version), "An explicit nontrivial example
of Breen-Deligne data". In Lean 3 notation:

```lean
/-- The `i`-th rank of this BD package is `2^i`. -/
def rank (i : ℕ) : FreeMat := 2 ^ i

/-- `σπ n` is an abreviation for `proj n 2 - sum n 2`. -/
def σπ (n : ℕ) := universal_map.proj n 2 - universal_map.sum n 2

/-- The `i`-th map of this BD package is inductively defined
as the simplest solution to the homotopy condition,
so that the homotopy will consist of identity maps. -/
def map : Π n, rank (n+1) ⟶ rank n
| 0     := σπ 1
| (n+1) := σπ (rank (n+1)) - mul 2 (map n)

/-- The `n`-th homotopy map for the example BD package is the identity. -/
def hmap : Π (j i : ℕ) (h : j + 1 = i), (((data.mul 2).obj BD).X j) ⟶ (BD.X i)
| j i rfl := 𝟙 _
```

In words:

* **Terms:** the $i$-th term is $\mathbb{Z}[A^{2^i}]$.
* **Differentials:** they are defined recursively as $d_0 = \pi - \sigma$ and
  $d_{n+1} = (\pi - \sigma) - 2 \cdot d_n$, where "$2\cdot$" is the doubling of a universal map
  (block diagonal).
* **The choice:** the differentials are chosen so that the required homotopy consists of identity
  maps.
* **Proofs:** that this is a complex (`is_complex_zero` and `is_complex_succ`) and that the
  homotopy works are a few lines each.

### History

* 30 November 2020: initial commit of `lean-liquid` by Johan Commelin. The repository predates the
  public challenge.
* 11 December 2020: commit 87cde79a "finish breen--deligne example complex" (Commelin). It is
  already the same construction: `rank n = 2 ^ n`, `map (n+1) := σ_diff (rank (n+1)) - (map n).double`,
  homotopy `hmap n := universal_map.id _`.
* 23 March 2021: moved to its own file `eg.lean`, commit e97a0003.

## Step 3: no Breen–Deligne resolution at all (2022)

The second half computes Ext groups, and there exactness seems to be needed. The team proved a
comparison lemma that avoids it:

* **The comparison lemma** (`main_lemma` / `main_lemma_general` in `src/breen_deligne/main.lean`;
  stated by Commelin on 22 March 2022, commit db1dd0a5 "statement of BD lemma"). It compares
  "$f - g$ induces isomorphisms on $\mathrm{Ext}^i(A, B)$" with the same statement for the
  evaluated complex. It does **not** require the evaluated complex to be exact. It only requires
  its homology in negative degrees to be of the form $T(A')$ for a functor $T$ that preserves
  short exact sequences and coproducts (hypothesis `hTA`).
* **The explicit complex satisfies this.** In `src/condensed/bd_lemma.lean`:
  * $T$ is a tensor-product functor.
  * $A'$ = `HQ'Z (-n)`, defined as the homology of `eg` evaluated at $\mathbb{Z}$:

    ```lean
    def HQ'Z (n : ℤ) : Ab :=
    ((eg.eval $ category_theory.forget AddCommGroup ⋙ AddCommGroup.free).obj
      (AddCommGroup.free.obj punit)).val.as.homology n
    ```

  * The lemma is applied via `eg.main_lemma_general' _ A B f g tensor_functor tensor_punit (λ n, HQ'Z (-n))`.
* **The names.** The evaluation of the complex on condensed abelian groups is called `QprimeFP`
  (`src/pseudo_normed_group/QprimeFP.lean`, first commit 4570eff6, 16 May 2022). So the explicit
  complex is used as Mac Lane's $Q'$-construction: a cubical complex with terms
  $\mathbb{Z}[A^{2^n}]$.
* **The final theorem.** The project was completed on 14 July 2022, as announced on the Lean
  community blog. The final theorem instantiates `breen_deligne.eg`: `ExtQprime.Tinv2 r r'
  breen_deligne.eg.data …` in `src/Lbar/ext.lean`.
* **The later blueprint.** Commelin and coauthors' "Blueprint for the reduction to Theorem 9.4"
  says that the argument "avoids the use of stable homotopy theory by replacing abstract
  Breen–Deligne resolutions with the explicit Q′-construction of MacLane".

So the completed formalization uses neither Breen–Deligne resolutions nor stable homotopy theory.

## Scholze's view (June 2021)

The following comes from "Half a year of the Liquid Tensor Experiment: Amazing developments",
Xena blog, 5 June 2021. It is quoted through Avigad, "Mathematics and the formal turn"
(arXiv:2311.00007), and search summaries:

* The computation of the Ext groups "is done via a certain non-explicit resolution known as a
  Breen-Deligne resolution", which "has certain beautiful structural properties, but is not
  explicit, and the existence relies on some facts from stable homotopy theory".
* The Breen–Deligne resolution was axiomatized, formalizing only the key structural properties.
  "What Johan realized is that one can actually give a nice and completely explicit object
  satisfying those axioms, and this is good enough for all the intended applications."
* On the project: "Reid Barton did some critical early work, but then Johan Commelin has taken the
  leading role in this."

## Why the properties were factored out

The history and the blueprint give these answers.

1. **30 November 2020: the original plan.** The plan was to state the Breen–Deligne theorem
   itself, with direct sums $\bigoplus \mathbb{Z}[A^{k_i}]$ in each degree, and to leave the proof
   as `sorry` (commit 2324a4b2, "statement of Breen--Deligne, modulo some sorries"):
   `theorem breen_deligne : ∃ BD : breen_deligne_data, BD.is_complex := sorry`. The direct sums
   immediately caused trouble: "fail, we don't know how to do maps into direct sums".
2. **10–11 December 2020: the redesign** (commits cc594c9d, 1e8019ea, 426ce07f):
   * `data` has a single $\mathbb{Z}[A^{\mathrm{rank}\,n}]$ in each degree.
   * `homotopy` is a homotopy between sum and projections.
   * `package` combines the two.
   * The comments show the design was still open: "do we want/need this?", "is this what we want
     for index 0 of a homotopy?".
   * A field `rank_zero : rank 0 = 1 -- this "hardcodes" that the complex end in ℤ[A] → A` was
     added and then commented out. This dropped the augmentation, and with it the idea of a
     resolution.
   * The example `eg` was finished the same afternoon.
3. **The blueprint, Section 1.1 "Breen–Deligne data"** (source on the `gh-pages` branch of
   `leanprover-community/liquid`): "This variant is not actually a resolution, but it is
   sufficient for our purposes, and is much easier to state and prove."
4. **The blueprint, Section 2.3 "The MacLane $Q'$-construction"**, on the key homology property:
   "As the proof shows, we do not really need the $Q'$-construction here: Any Breen–Deligne
   package will do."

The following is an inference, not stated in the sources:

* **Why no resolution was needed:** Theorem 9.4 uses only the form $\mathbb{Z}[A^n]$ of the
  terms, the universality of the maps, and the homotopy. So the existence theorem, with its stable
  homotopy theory, was not needed for the first goal.
* **Why the example came so soon:** once the abstraction was in place, the target theorem
  quantified over all packages. Without an example it could have been vacuous.

## Commelin's account of who did what

The exchange is on Zulip, `#general` › "Community blog":
<https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Community.20blog/near/266544598>
(the link points to Commelin's message). The date is not checked.

> **Kevin Buzzard:** @Johan Commelin You're not tempted to say far more explicitly "look we
> simplified the argument because we formalised it and it made us abstract the properties we
> needed"? People like de Jong proved great theorems in maths because they thought about what
> people were actually using when they were relying on resolution of singularities and then made a
> weaker construction which sufficed -- this was his big breakthrough. To say that a computer is
> helping us to do this is something which I think should be emphasized
>
> **Johan Commelin:** @Kevin Buzzard You are right. But it's been a subtle interplay between me
> abstracting the properties we needed, and Scholze immediately recognizing that all the pieces
> fit together. Without his input, I don't think I would have connected the dots.
> Lean forced me to do the abstraction, but it didn't help us with connecting the existing puzzle
> pieces when it comes to this Breen-Deligne lemma.
>
> **Johan Commelin:** Where I see genuine help from Lean is in untangling the rest of the proof.
> That was one complicated tangle, and with Lean we managed to find a precise path through the
> maze. I wasn't able to find that path without Lean.
>
> **Johan Commelin:** At some point in time, we should write down these findings in a careful way.
> Probably when we write a paper about the whole journey.

How I read it:

* **Buzzard's analogy:** de Jong's alterations (1996). People relied on resolution of
  singularities, which is unknown in characteristic $p$. De Jong asked which properties were
  actually used and built a weaker construction that suffices. Buzzard sees the same pattern in
  replacing Breen–Deligne resolutions by packages.
* **Commelin divides the credit three ways:**
  1. **Lean forced the abstraction**, the Breen–Deligne package. This matches the December 2020
     history above.
  2. **Scholze recognized that the pieces fit together.** "This Breen-Deligne lemma" is presumably
     the comparison lemma (`main_lemma`; blueprint Proposition 2.3.3). It shows that the explicit
     complex suffices even for the Ext computation of the second half. Lean did not help with this
     connection.
  3. **Lean helped in "untangling the rest of the proof"**: the maze of constants and normed
     homological algebra, mainly around Theorem 9.4. This matches Scholze's June 2021 remark that
     he did not understand why the argument worked until it was formalized.
* **In terms of discovery and justification:** Lean contributed to discovery by posing the right
  question, the abstraction. The conceptual answer came from Scholze. The clearest gain from Lean
  is that it made a tangled proof surveyable.

The slide follows this account: "Lean forced the abstraction. Scholze then saw that the explicit
complex suffices for the whole proof".

## Open questions

* **Exact wording:** Scholze's sentences above are checked only through secondary sources.
* **"Standard tool":** a search summary attributes "I expect that Commelin's complex may become a
  standard tool in the coming years" to "one commentator". It may be Scholze in the same post. The
  author is not confirmed, so don't attribute it yet.
* **Mac Lane's $Q'$:** it is unclear whether the 2020 complex was recognized as Mac Lane's $Q'$
  from the start or only later. The Lean names `Qprime…` only appear in 2022.
* **Which homology facts are used:** the details of which facts about $H_*(Q'(\mathbb{Z}))$ are
  needed (for example torsion-freeness conditions) are not checked here.

## References

* Scholze, "Liquid tensor experiment" (5 December 2020):
  <https://xenaproject.wordpress.com/2020/12/05/liquid-tensor-experiment/>
* Scholze, "Half a year of the Liquid Tensor Experiment: Amazing developments" (5 June 2021):
  <https://xenaproject.wordpress.com/2021/06/05/half-a-year-of-the-liquid-tensor-experiment-amazing-developments/>
* "Completion of the Liquid Tensor Experiment" (Lean community blog, July 2022):
  <https://leanprover-community.github.io/blog/posts/lte-final/>
* Commelin et al., "Liquid Tensor Experiment: Blueprint for the reduction to Theorem 9.4":
  <https://math.commelin.net/files/LTE.pdf>
* J. Avigad, "Mathematics and the formal turn", Bull. AMS 61 (2024),
  [arXiv:2311.00007](https://arxiv.org/abs/2311.00007)
* J. Commelin, "Liquid Tensor Experiment", Nieuw Archief voor Wiskunde 5/22 nr. 4 (December 2021):
  <https://www.nieuwarchief.nl/serie5/pdf/naw5-2021-22-4-231.pdf>
* J. Commelin, "Liquid Tensor Experiment: a case study in epistemology of proof" (slides, PAT 2023):
  <https://pat2023.icube.unistra.fr/slides/slides-pat2023-commelin-talk2.pdf>
* Repository: <https://github.com/leanprover-community/lean-liquid>. Local clone:
  `/root/downstream/mathematics-with-lean/lean-liquid`. Files: `src/breen_deligne/eg.lean`,
  `src/breen_deligne/main.lean`, `src/condensed/bd_lemma.lean`,
  `src/pseudo_normed_group/QprimeFP.lean`, `src/Lbar/ext.lean`, `src/liquid.lean`,
  `src/challenge.lean`. Commits: 87cde79a, e97a0003, db1dd0a5, 4570eff6.
