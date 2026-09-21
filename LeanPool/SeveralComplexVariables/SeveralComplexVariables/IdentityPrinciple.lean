/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity

/-!
# The identity theorem for holomorphic functions in several variables

Holomorphic maps on a preconnected open subset of a finite-dimensional complex normed space
agree everywhere if they agree near one point, equivalently on a nonempty open subset. The
target may be a complex Banach space. The proofs use the project's holomorphic–analytic
equivalence and Mathlib's analytic identity principle.

`DifferentiableOn.eqOn_of_preconnected_of_eqOn` is
[Fritzsche–Grauert][FritzscheGrauert2002] (2002), I.4.10, p. 22,
with Banach-valued targets. Finite coordinate spaces `ι → ℂ` are covered as finite-dimensional
spaces, including empty coordinate types. The agreement set must be nonempty; agreement merely on a
set with a cluster point does not suffice in several variables.

## Main results

* `DifferentiableOn.eqOn_of_preconnected_of_eqOn`: **Identity theorem
  ([Fritzsche–Grauert][FritzscheGrauert2002] I.4.10).** Two holomorphic maps on an open,
  preconnected set agree everywhere if they agree on a nonempty open subset.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
-/

public section

open Set Filter
open scoped Topology

namespace DifferentiableOn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The holomorphic identity principle from equality near one point of an open, preconnected set.
The target may be any complex Banach space. -/
theorem eqOn_of_preconnected_of_eventuallyEq {U : Set E} (hU : IsOpen U)
    (hconn : IsPreconnected U) {f g : E → F}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {a : E} (ha : a ∈ U) (heq : f =ᶠ[𝓝 a] g) : EqOn f g U :=
  (hf.analyticOnNhd_of_finiteDimensional hU).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd_of_finiteDimensional hU) hconn ha heq

/-- **Identity theorem ([Fritzsche–Grauert][FritzscheGrauert2002] I.4.10).** Two holomorphic maps on
an open, preconnected set agree everywhere if they agree on a nonempty open subset. -/
theorem eqOn_of_preconnected_of_eqOn {U V : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {f g : E → F} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) (heq : EqOn f g V) :
    EqOn f g U := by
  obtain ⟨a, ha⟩ := hne
  exact hf.eqOn_of_preconnected_of_eventuallyEq hU hconn hg (hVU ha)
    (Filter.mem_of_superset (hV.mem_nhds ha) (fun _ hx => heq hx))

/-- A holomorphic map vanishing on a nonempty open subset vanishes throughout the open, preconnected
domain. -/
theorem eqOn_zero_of_preconnected_of_eqOn_zero {U V : Set E} (hU : IsOpen U)
    (hconn : IsPreconnected U)
    {f : E → F} (hf : DifferentiableOn ℂ f U)
    (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) (heq : EqOn f 0 V) :
    EqOn f 0 U :=
  hf.eqOn_of_preconnected_of_eqOn hU hconn (differentiableOn_const 0) hV hne hVU heq

end DifferentiableOn

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
