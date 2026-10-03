/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Stability.HalfRelaxedLimits.Semijets

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Half-relaxed stability theorems

This file contains the main viscosity stability theorems for upper and lower
half-relaxed limits.

The main declarations are `ViscositySubsolution.upperHalfRelaxedLimit` and
`ViscositySupersolution.lowerHalfRelaxedLimit`.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat} {ι : Type*}

/--
Abstract half-relaxed stability for subsolutions.

Let `upperLimit x = upperHalfRelaxedLimit uᵢ l C x`. If the set of indices `i` for
which `uᵢ i` is a viscosity subsolution of `F = 0` on `C` belongs to `l`,
and if for every `x ∈ C` and every `J ∈ Superjet C upperLimit x` the graph point
`((x, upperLimit x), J)` belongs to `TailClosureSuperjetGraph C uᵢ l`, then `upperLimit`
is a viscosity subsolution of `F = 0` on `C`. The other hypotheses are the
operator continuity and boundedness assumptions used to prove upper
semicontinuity of `upperLimit`.
-/
theorem ViscositySubsolution.upperHalfRelaxedLimit_of_eventually_tailClosureSuperjetGraph
    {C : Set (Point n)} {F : Operator n} {uᵢ : ι -> Point n -> Real}
    {l : Filter ι}
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (happrox : ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
      J ∈ Superjet C (upperHalfRelaxedLimit uᵢ l C) x ->
        ((x, upperHalfRelaxedLimit uᵢ l C x), J) ∈
          TailClosureSuperjetGraph C uᵢ l) :
    ViscositySubsolution C F (upperHalfRelaxedLimit uᵢ l C) :=
  ViscositySubsolution.of_eventually_tailClosureSuperjetGraph
    (upperSemicontinuousOn_upperHalfRelaxedLimit uᵢ l C hbddAbove hcobddBelow)
    hF hsub happrox

/--
Abstract half-relaxed stability for supersolutions.

Let `lowerLimit x = lowerHalfRelaxedLimit uᵢ l C x`. If the set of indices `i` for
which `uᵢ i` is a viscosity supersolution of `F = 0` on `C` belongs to `l`,
and if for every `x ∈ C` and every `J ∈ Subjet C lowerLimit x` the graph point
`((x, lowerLimit x), J)` belongs to `TailClosureSubjetGraph C uᵢ l`, then `lowerLimit` is a
viscosity supersolution of `F = 0` on `C`. The other hypotheses are the
operator continuity and boundedness assumptions used to prove lower
semicontinuity of `lowerLimit`.
-/
theorem ViscositySupersolution.lowerHalfRelaxedLimit_of_eventually_tailClosureSubjetGraph
    {C : Set (Point n)} {F : Operator n} {uᵢ : ι -> Point n -> Real}
    {l : Filter ι}
    (hF : OperatorContinuous F)
    (hsuper : ∀ᶠ i in l, ViscositySupersolution C F (uᵢ i))
    (hbddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hcobddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (happrox : ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
      J ∈ Subjet C (lowerHalfRelaxedLimit uᵢ l C) x ->
        ((x, lowerHalfRelaxedLimit uᵢ l C x), J) ∈
          TailClosureSubjetGraph C uᵢ l) :
    ViscositySupersolution C F (lowerHalfRelaxedLimit uᵢ l C) :=
  ViscositySupersolution.of_eventually_tailClosureSubjetGraph
    (lowerSemicontinuousOn_lowerHalfRelaxedLimit uᵢ l C hbddBelow hcobddAbove)
    hF hsuper happrox

/--
Half-relaxed stability for subsolutions.

Let `upperLimit x = upperHalfRelaxedLimit uᵢ l C x`. If the set of indices `i` for
which `uᵢ i` is a viscosity subsolution of `F = 0` on `C` belongs to `l`,
then `upperLimit` is a viscosity subsolution of `F = 0` on `C`, under the operator
continuity, local compactness, and boundedness hypotheses stated below.
-/
theorem ViscositySubsolution.upperHalfRelaxedLimit
    {C : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ)) :
    ViscositySubsolution C F (upperHalfRelaxedLimit uᵢ l C) := by
  refine ViscositySubsolution.upperHalfRelaxedLimit_of_eventually_tailClosureSuperjetGraph
    hF hsub hbddAbove hcobddBelow ?_
  intro x hxC J hJ
  exact tailClosureSuperjetGraph_upperHalfRelaxedLimit_superjet
    (uᵢ := uᵢ) (l := l) (C := C) (x := x) (J := J)
    hxC hbddAbove hcobddBelow (hsub.mono fun _ hi => hi.1) hJ

/--
Half-relaxed stability for supersolutions.

Let `lowerLimit x = lowerHalfRelaxedLimit uᵢ l C x`. If the set of indices `i` for
which `uᵢ i` is a viscosity supersolution of `F = 0` on `C` belongs to `l`,
then `lowerLimit` is a viscosity supersolution of `F = 0` on `C`, under the operator
continuity, local compactness, and boundedness hypotheses stated below.
-/
theorem ViscositySupersolution.lowerHalfRelaxedLimit
    {C : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (hF : OperatorContinuous F)
    (hsuper : ∀ᶠ i in l, ViscositySupersolution C F (uᵢ i))
    (hbddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hcobddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ)) :
    ViscositySupersolution C F (lowerHalfRelaxedLimit uᵢ l C) := by
  refine ViscositySupersolution.lowerHalfRelaxedLimit_of_eventually_tailClosureSubjetGraph
    hF hsuper hbddBelow hcobddAbove ?_
  intro x hxC J hJ
  exact tailClosureSubjetGraph_lowerHalfRelaxedLimit_subjet
    (uᵢ := uᵢ) (l := l) (C := C) (x := x) (J := J)
    hxC hbddBelow hcobddAbove (hsuper.mono fun _ hi => hi.1) hJ

/--
Locally uniform convergence identifies the upper half-relaxed limit with the
ordinary limit.
-/
theorem upperHalfRelaxedLimit_eq_of_locallyUniform
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real} {l : Filter ι}
    {C : Set (Point n)} {x : Point n}
    [NeBot (halfRelaxedFilter l C x)]
    (hlu : LocallyUniformTendstoOn uᵢ u l C)
    (hu : ContinuousWithinAt u C x) (hxC : x ∈ C) :
    upperHalfRelaxedLimit uᵢ l C x = u x := by
  have hg : Tendsto (fun q : ι × Point n => q.2)
      (halfRelaxedFilter l C x) (nhdsWithin x C) :=
    tendsto_snd
  have htendsto : Tendsto (halfRelaxedValue uᵢ)
      (halfRelaxedFilter l C x) (nhds (u x)) := by
    refine tendsto_comp_of_locally_uniform_limit_within
      (F := fun q : ι × Point n => uᵢ q.1) hu hg ?_
    intro V hV
    rcases hlu V hV x hxC with ⟨t, ht, hlocal⟩
    exact ⟨t, ht, hlocal.prod_inl (nhdsWithin x C)⟩
  exact htendsto.limsup_eq

/--
Locally uniform convergence identifies the lower half-relaxed limit with the
ordinary limit.
-/
theorem lowerHalfRelaxedLimit_eq_of_locallyUniform
    {uᵢ : ι -> Point n -> Real} {u : Point n -> Real} {l : Filter ι}
    {C : Set (Point n)} {x : Point n}
    [NeBot (halfRelaxedFilter l C x)]
    (hlu : LocallyUniformTendstoOn uᵢ u l C)
    (hu : ContinuousWithinAt u C x) (hxC : x ∈ C) :
    lowerHalfRelaxedLimit uᵢ l C x = u x := by
  have hg : Tendsto (fun q : ι × Point n => q.2)
      (halfRelaxedFilter l C x) (nhdsWithin x C) :=
    tendsto_snd
  have htendsto : Tendsto (halfRelaxedValue uᵢ)
      (halfRelaxedFilter l C x) (nhds (u x)) := by
    refine tendsto_comp_of_locally_uniform_limit_within
      (F := fun q : ι × Point n => uᵢ q.1) hu hg ?_
    intro V hV
    rcases hlu V hV x hxC with ⟨t, ht, hlocal⟩
    exact ⟨t, ht, hlocal.prod_inl (nhdsWithin x C)⟩
  exact htendsto.liminf_eq

end ViscositySolns
