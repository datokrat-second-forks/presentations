import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

set_option verso.code.warnLineLength 100

#doc (Slides) "Instance Assignment Failures" =>

# Instance Assignment Failures

Paul Reichert

2026-08-26

```lean -show
set_option linter.unusedVariables false
set_option verso.code.warnLineLength 100
```

# Quantitative breakdown

The audit started with **53 declarations**. Old transparency debt explains 18 declarations.
The strict check initially regressed the remaining 35 declarations.

{html}`<div class="count-grid">
  <div><strong>18</strong>RT annotation debt</div>
  <div><strong>17</strong>default-instance bypass</div>
  <div><strong>7</strong>abandoned goals</div>
  <div><strong>4</strong>dependent assignment order</div>
  <div><strong>2</strong>types unified too late</div>
  <div><strong>2</strong>fallback timeout</div>
  <div><strong>1</strong>inference-order flip</div>
  <div><strong>1</strong>proof-shape coupling</div>
  <div><strong>1</strong>ordinary-unification stuck</div>
</div>`

The abandoned-goal count contains five blocked searches and two real value mismatches.

# Reproducing the failures

The local Lean build contains three default-on adjustments to the strict EIT check.

```code text
backward.isDefEq.respectTransparency.elabInstanceTypes.exemptDefaultInstances
backward.isDefEq.respectTransparency.elabInstanceTypes.unmarkAbandoned
backward.isDefEq.respectTransparency.elabInstanceTypes.unifyTypesFirst
```

Most slides disable all three adjustments. A slide states when it enables an adjustment to
isolate a later failure mode.

The traces keep only failed assignment checks, fallback searches, and the first relevant
unification branch.

# 1. RT annotation debt — 18 declarations

The old declaration disabled respect-transparency behavior. Removing that override exposes
definitions that the proof needs at implicit transparency.

:::leanModules +error (moduleRoot := RTDebt)
```leanModule +lakefile -show
import Lake
open Lake DSL
require mathlib from "/root/mathlib4/julia-minimal"
package p where
  version := v!"0.1.0"
lean_lib RTDebt
```
```leanModule (moduleName := RTDebt) -stretch +error
module
meta import Lean.PostprocessTraces
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

open Lean.PostprocessTraces
-- !hide
postprocess_traces
  hoist (fun x => do
    (ofClass `Meta.synthInstance x) <&&> (containsString "SupHomClass" x))
in
set_option backward.isDefEq.respectTransparency.elabInstanceTypes false in
-- !end hide
namespace NumberField.mixedEmbedding
open scoped Classical
open NumberField.InfinitePlace Module Finset
variable (K : Type*) [Field K] [NumberField K]
example (x : mixedSpace K) :
    ‖x‖ = univ.sup' univ_nonempty fun w ↦ normAtPlace w x := by
  (set_option trace.Meta.synthInstance true in
   rw [← coe_nnnorm, nnnorm_eq_sup_normAtPlace, ← sup'_eq_sup univ_nonempty,
     ← NNReal.val_eq_coe, ← OrderHom.Subtype.val_coe, map_finset_sup',
     OrderHom.Subtype.val_coe])
  simp
end mixedEmbedding
```
:::

Local `implicit_reducible` marks fix this case. EIT does not cause the failure.

<div class="source">CanonicalEmbedding/Basic.lean:404</div>

# 2. Default-instance bypass — 17 declarations

The old deferred check does not revisit an instance metavariable assigned by the default-instance
pass. The strict check originally rejected that assignment too early.

```code text
-- Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean
let f₁ := Limits.Pi.map (fun j ↦ (T j).mor₁)
obtain ⟨Z, f₂, f₃, hT'⟩ := distinguished_cocone_triangle f₁
…
-- Diagram arithmetic creates a default HAdd metavariable.
```

```code text
[Meta.synthInstance] HAdd (A ⟶ Z) (?m ⟶ T'.obj₃) …
[Meta.isDefEq.assign.checkTypes] ❌
  (?h : HAdd (A ⟶ Z) (?m ⟶ T'.obj₃) (A ⟶ T'.obj₃)) := instHAdd
[Meta.synthInstance] ❌ HAdd (A ⟶ Z) (A ⟶ T'.obj₃) …
```

```code text
set_option ….exemptDefaultInstances false -- reproduce the failure
set_option ….unmarkAbandoned false
set_option ….unifyTypesFirst false
```

<div class="source">Pretriangulated.lean:617</div>

# 3. Abandoned goals — 5 blocked searches

`convert` can create a typeclass goal and later abandon it. The caller does not use the rejected
assignment, but strict checking can block elaboration before the goal is disarmed.

:::leanModules +error (moduleRoot := AbandonedSearch)
```leanModule +lakefile -show
import Lake
open Lake DSL
require mathlib from "/root/mathlib4/julia-minimal"
package p where
  version := v!"0.1.0"
lean_lib AbandonedSearch
```
```leanModule (moduleName := AbandonedSearch) -stretch +error
module
meta import Lean.PostprocessTraces
import Mathlib.AlgebraicGeometry.FunctionField

open Lean.PostprocessTraces
-- !hide
postprocess_traces
  filterSubtrees (fun x => do
    (ofClass `Meta.isDefEq x) <&&> (containsString "Monad.Algebra" x))
in
set_option backward.isDefEq.respectTransparency.elabInstanceTypes true in
set_option backward.isDefEq.respectTransparency.elabInstanceTypes.exemptDefaultInstances false in
set_option backward.isDefEq.respectTransparency.elabInstanceTypes.unmarkAbandoned false in
set_option backward.isDefEq.respectTransparency.elabInstanceTypes.unifyTypesFirst false in
-- !end hide
namespace AlgebraicGeometry
attribute [local implicit_reducible] Spec Spec.sheafedSpaceObj Spec.topObj
  Spec.locallyRingedSpaceObj Scheme.Opens.toScheme Scheme.restrict
  LocallyRingedSpace.restrict PresheafedSpace.restrict SheafedSpace.restrict
  SetLike.coe Set Opens.toTopCat in
example {X : Scheme} [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) [h : Nonempty U] :
    hU.primeIdealOf
        ⟨genericPoint X,
          ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h)⟩ =
      genericPoint (Spec Γ(X, U)) := by
  delta IsAffineOpen.primeIdealOf
  convert! genericPoint_eq_of_isOpenImmersion
    (U.toScheme.isoSpec.hom ≫ Spec.map
      (X.presheaf.map (eqToHom U.isOpenEmbedding_obj_top).op))
  (set_option trace.Meta.isDefEq true in
   apply Subtype.ext)
  exact (genericPoint_eq_of_isOpenImmersion U.ι).symm
end AlgebraicGeometry
```
:::

The failure uses `unmarkAbandoned := false`. The other two adjustments stay disabled.

<div class="source">FunctionField.lean:131</div>

# 4. Abandoned goals — 2 real mismatches

Some abandoned goals contain a genuine value mismatch. The synthesized concrete `MonObj` and the
abstract `grp` field have equal types but different operations.

```code text
-- Mathlib/CategoryTheory/Preadditive/CommGrp_.lean
convert! (MonObj.lift_comp_one_right _ 0).symm
· simp
· infer_instance
```

```code text
candidate:   X.grp.toMonObj.one
synthesized: MonObj.one from the constructed monoid object
comparison:  ❌ at reducible, instances, semireducible, and all
```

Unmarking the abandoned metavariable restores old behavior. It also accepts this mismatch because
the elaborator discards the goal.

<div class="source">CommGrp&#95;.lean:62</div>

# 5. Dependent assignment order — 4 declarations

The visible function types already agree. Assigning the instance value first is what determines
the dependent index and family metavariables.

:::leanModules +error (moduleRoot := DependentOrder)
```leanModule +lakefile -show
import Lake
open Lake DSL
require mathlib from "/root/mathlib4/julia-minimal"
package p where
  version := v!"0.1.0"
lean_lib DependentOrder
```
```leanModule (moduleName := DependentOrder) -stretch +error
module
meta import Lean.PostprocessTraces
import Mathlib.MeasureTheory.Constructions.Cylinders

open Lean.PostprocessTraces
-- !hide
postprocess_traces
  filterSubtrees (ofClass `Meta.isDefEq.assign.checkTypes)
in
set_option backward.isDefEq.respectTransparency.elabInstanceTypes true in
set_option backward.isDefEq.respectTransparency.elabInstanceTypes.exemptDefaultInstances false in
set_option backward.isDefEq.respectTransparency.elabInstanceTypes.unmarkAbandoned false in
set_option backward.isDefEq.respectTransparency.elabInstanceTypes.unifyTypesFirst false in
-- !end hide
open Function Set MeasurableSpace in
open MeasureTheory in
variable {I : Type} {A : I → Type} in
example [∀ i, TopologicalSpace (A i)] (s : Finset I) {S : Set (∀ i : s, A i)}
    (hs : IsClosed S) : IsClosed (cylinder s S) := by
  (set_option trace.Meta.isDefEq true in
   set_option trace.Meta.isDefEq.printTransparency true in
   exact hs.preimage (continuous_pi fun _ ↦ continuous_apply _))
```
:::

All three adjustments are disabled. Types-first cannot fix this category.

<div class="source">Cylinders.lean:249</div>

# 6. Types unified too late — 2 declarations

The first strict implementation checked the values before ordinary unification settled type
metavariables. Compatible quotient views then appeared heterogeneous.

:::leanModules +error (moduleRoot := TypesFirst)
```leanModule +lakefile -show
import Lake
open Lake DSL
require mathlib from "/root/mathlib4/julia-minimal"
package p where
  version := v!"0.1.0"
lean_lib TypesFirst
```
```leanModule (moduleName := TypesFirst) -stretch +error
module
meta import Lean.PostprocessTraces
import Mathlib.Analysis.InnerProductSpace.ProdL2

open Lean.PostprocessTraces
-- !hide
postprocess_traces
  filterSubtrees (fun x => do
    (ofClass `Meta.isDefEq.assign.checkTypes x) <&&>
      (containsString "Submodule" x))
in
set_option backward.isDefEq.respectTransparency.elabInstanceTypes true in
set_option backward.isDefEq.respectTransparency.elabInstanceTypes.exemptDefaultInstances false in
set_option backward.isDefEq.respectTransparency.elabInstanceTypes.unmarkAbandoned false in
set_option backward.isDefEq.respectTransparency.elabInstanceTypes.unifyTypesFirst false in
-- !end hide
namespace Submodule
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
variable (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
example : (E ⨸ K) ≃ₗᵢ[𝕜] ↥Kᵾ where
  __ := K.quotientEquivOfIsCompl Kᵾ K.isCompl_orthogonal
  norm_map' y := by
    set f := K.quotientEquivOfIsCompl Kᵾ K.isCompl_orthogonal
    rw [coe_norm, ← norm_orthogonalProjectionOnto_apply Kᵾ (f y).2,
      orthogonalProjectionOnto_orthogonal, coe_norm, starProjection_minimal, eq_comm]
    have h : ‖Quotient.mk (f y).val‖ =
        sInf ((fun (x : E) ↦ ‖(f y).val + x‖) '' K.toAddSubgroup) :=
      quotient_norm_mk_eq K.toAddSubgroup (f y).1
    (set_option trace.Meta.isDefEq true in
     convert! h using 2)
    · simp [f]
    · rw [sInf_image', ← Equiv.iInf_comp (Equiv.neg K)]
      simp
end Submodule
```
:::

This failure sets `unifyTypesFirst := false`. Enabling that adjustment resolves it.

<div class="source">ProdL2.lean:142</div>

# 7. Fallback timeout — 2 declarations

Fallback synthesis finds a valid instance. Its final comparison unfolds repeated `Additive` and
`Multiplicative` wrappers until it exhausts the heartbeat limit.

:::leanModules +error (moduleRoot := FallbackTimeout)
```leanModule +lakefile -show
import Lake
open Lake DSL
require mathlib from "/root/mathlib4/julia-minimal"
package p where
  version := v!"0.1.0"
lean_lib FallbackTimeout
```
```leanModule (moduleName := FallbackTimeout) -stretch +error
module
meta import Lean.PostprocessTraces
import Mathlib.Algebra.Order.Monoid.LocallyFiniteOrder

open Lean.PostprocessTraces
-- !hide
postprocess_traces
  filterSubtrees (ofClass `Meta.isDefEq.assign.checkTypes)
in
set_option maxHeartbeats 200000 in
-- All three adjustments remain enabled: this is the residual failure.
-- !end hide
example {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    [LocallyFiniteOrder G] : StrictMono (LocallyFiniteOrder.orderMonoidHom G) :=
  let : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  set_option trace.Meta.isDefEq true in
  fun _ _ h ↦ LocallyFiniteOrder.orderAddMonoidHom_strictMono h
```
:::

<div class="source">LocallyFiniteOrder.lean:183</div>

# 8. Inference-order flip — 1 declaration

The strict check fixes shared metavariables earlier. The inverse map then receives a prime-spectrum
index where it needs a maximal-spectrum index.

:::leanModules +error (moduleRoot := InferenceFlip)
```leanModule +lakefile -show
import Lake
open Lake DSL
require mathlib from "/root/mathlib4/julia-minimal"
package p where
  version := v!"0.1.0"
lean_lib InferenceFlip
```
```leanModule (moduleName := InferenceFlip) -stretch +error
module
meta import Lean.PostprocessTraces
import Mathlib.RingTheory.Spectrum.Maximal.Localization

open Lean.PostprocessTraces
-- !hide
postprocess_traces
  filterSubtrees (ofClass `Meta.isDefEq.assign.checkTypes)
in
-- All three adjustments remain enabled: this is the residual failure.
-- !end hide
noncomputable example {R : Type*} [CommRing R] [IsDomain R]
    (h : ∀ I : Ideal R, I.IsPrime → I.IsMaximal) :
    PrimeSpectrum.PiLocalization R ≃+* MaximalSpectrum.PiLocalization R where
  __ := PrimeSpectrum.piLocalizationToMaximal R
  invFun := set_option trace.Meta.isDefEq true in
    RingHom.pi fun I ↦ Pi.evalRingHom _ (⟨_, h _ I.2⟩ : MaximalSpectrum R)
```
:::

<div class="source">Maximal/Localization.lean:187</div>

# 10. Ordinary-unification stuck — 1 declaration

This stuck term does not pass through the abandoned synthetic-metavariable path. Therefore,
unmark-on-abandon cannot affect it.

:::leanModules +error (moduleRoot := OrdinaryStuck)
```leanModule +lakefile -show
import Lake
open Lake DSL
require mathlib from "/root/mathlib4/julia-minimal"
package p where
  version := v!"0.1.0"
lean_lib OrdinaryStuck
```
```leanModule (moduleName := OrdinaryStuck) -stretch +error
module
meta import Lean.PostprocessTraces
import Mathlib.RingTheory.Etale.StandardEtale

open Lean.PostprocessTraces
-- !hide
postprocess_traces
  filterSubtrees (fun x => do
    (ofClass `Meta.isDefEq.assign.checkTypes x) <||>
      ((ofClass `Meta.isDefEq x) <&&> (containsString "StandardEtalePair.Ring" x)))
in
-- All three adjustments remain enabled: this is the residual failure.
-- !end hide
open Polynomial in
variable {R : Type*} [CommRing R] (P : StandardEtalePair R) in
example : aeval P.X P.g * Ideal.Quotient.mk _ .X = 1 := by
  have : aeval (R := R) P.X =
      (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext
    simp [StandardEtalePair.Ring, StandardEtalePair.X]
  (set_option trace.Meta.isDefEq true in
   set_option trace.Meta.isDefEq.printTransparency true in
   rw [this])
```
:::

<div class="source">StandardEtale.lean:107</div>

# What remains

The three adjustments resolve 26 of the 35 initial EIT regressions.

Nine declarations still need local EIT exemptions:

* four dependent-assignment cases;
* two fallback timeouts;
* one inference-order change;
* one proof-shape dependency;
* one ordinary-unification stuck term.

The policy keeps the check early. It does not assign an instance first and validate it after later
elaboration has already used that assignment.
