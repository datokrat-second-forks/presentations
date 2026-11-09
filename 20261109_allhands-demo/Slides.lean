import VersoSlides
import Lean.PostprocessTraces

open VersoSlides
open Lean.PostprocessTraces

#doc (Slides) "Coherence of Type Classes in Lean" =>
%%%
transition := "none"
%%%

# Coherence of Type Classes in Lean

Paul Reichert, Lean FRO

Lean FRO All-Hands, November 9, 2026

# Coherence

Wish: "If users follow a simple rule, they don't get into situations where two terms are
definitionally equal except inside instances (coherence of instances)."

Rule: If `α = β` at _instance_ transparency, then if the user provides instances of types `α` and `β`,
they must be definitionally equal at _implicit_ transparency.
instances of types `α` and `β` provided by the user must be definitionally equal at implicit transparency.
Violations are called diamonds. Otherwise, the instances are called _canonical_.

We would like to promise users following that rule will not encounter instance incoherences.

# Challenge 1: Lean Introduces Non-Canonical Instances

```lean +error -keep
class X where x : Nat
class Y (α : Type) extends X where y : Nat

instance : Y Nat := { x := 0, y := 0 }
instance [inst : Y Nat] : X := inst.toX

def f [Y Nat] (_ : X.x = 0) : Nat := Y.y Nat

-- Later...

def N := Nat
instance : Y N := { x := 0, y := 1 }
-- not a diamond, defeq to the earlier `X` instance:
instance [inst : Y N] : X := inst.toX

postprocess_traces (filterSubtrees (containsString "Y.toX Nat =?= instYN.toX N")) >=> (exposeSubtrees (containsString "Y.toX Nat =?= instYN.toX N")) in
set_option trace.Meta.isDefEq true in
def bla := fun (h : X.x = 0) => f h -- `(?i : Y Nat).toX =?= instYN.toX`
```

Diagnosis: The type check for instances happens at implicit transparency,
even though instances' types are expected to match at instance transparency.

Similarly, using (d)simp with a `rfl` equality that does not hold at instance transparency invalidates instances.

# Approaches

1. get rid of the distinction between `instance_reducible` and `implicit_reducible` (very breaking, topic of my last demo)
2. enforce the invariant that types of instances must be as expected up to instance transparency

Second approach also breaks many proofs and makes working with unbundled things less convenient:
`dsimp` works less often. It's only the negative side of the solution.

# Working With Stricter Instance-Type Checks

TODO: Insert toy example inspired by category theory stuff

# Challenge 2: `if` and `Decidable`

It is very difficult to avoid `Decidable` diamonds.

```lean -keep
def f (a b : Array Nat) : Nat :=
  if a < b then 0 else 1
def g (a b : Array Nat) : Nat :=
  if a.toList < b.toList then 0 else 1

example : f a b = g a b := by
  dsimp only [f, g, LT.lt]
  fail_if_success rfl
  simp
```

* There are many non-canonical `Decidable` instances
* In order to make rewriting `if`'s possible despite the dependency, `simp` has special handling for "subsingleton instances" like `Decidable`.
  But this only adds more non-canonical instances.
* Can we make `if` less dependent? Or do we just need to accept the problems with `Decidable`?

# How Isabelle Handles If-Then-Else

```
fun contains :: "'a ⇒ 'a list ⇒ bool" where
  "contains x [] = False"
| "contains x (y # ys) = (x = y ∨ contains x ys)"

export_code contains in SML
```

Generates:

```
type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;
fun eq A_ a b = equal A_ a b;

fun contains A_ x [] = false
  | contains A_ x (y :: ys) = eq A_ x y orelse contains A_ x ys;
```

# How Rocq Handles If-Then-Else

* `Decision` type class works like Lean's `Decidable`
* Boolean reflection?
* `sumbool`: `if Nat.dec_eq x y ...` where `Nat.dec_eq x y : Decidable P`
