/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherFunctionSpace

/-!
# Fixed-coefficient linear second-order parabolic operators

This file packages the coordinate operator produced by a connection
Laplacian in a local bundle frame.  Its coefficients act on the spatial
Hessian, spatial gradient, and value of a genuine `ParabolicSecondJet`:

`L u = A(D²u) + B(Du) + C(u)`.

The main estimates prove directly that `L` maps parabolic
`C^{2+α,1+α/2}` control to `C^{0,α}` control and that the fixed
coefficient operator is Lipschitz on differences.  The latter is the exact
input for the frozen-coefficient Duhamel contraction used in a manifold
parametrix.
-/

@[expose] public noncomputable section
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Break the nested continuous-linear-map instance-search cycle explicitly.
local instance hessianMapNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] (X →L[ℝ] E)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance hessianMapNormedSpace :
    NormedSpace ℝ (X →L[ℝ] (X →L[ℝ] E)) :=
  ContinuousLinearMap.toNormedSpace

/-- The bounded bilinear evaluation map `(T, v) ↦ T v`. -/
def operatorEvaluation (V W : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] :
    (V →L[ℝ] W) →L[ℝ] V →L[ℝ] W :=
  ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ W)

@[simp]
theorem operatorEvaluation_apply {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : V →L[ℝ] W) (v : V) :
    operatorEvaluation V W T v = T v :=
  rfl

/-- A local fixed-coefficient linear second-order operator evaluated using a
chosen genuine parabolic second jet. -/
def parabolicLinearSecondOrder
    (A : ℝ × X → (X →L[ℝ] (X →L[ℝ] E)) →L[ℝ] E)
    (B : ℝ × X → (X →L[ℝ] E) →L[ℝ] E)
    (C : ℝ × X → E →L[ℝ] E)
    (u : ℝ × X → E) {s : Set (ℝ × X)} (J : ParabolicSecondJet u s) :
    ℝ × X → E :=
  fun z => A z (J.spaceSecondDeriv z) + B z (J.spaceDeriv z) + C z (u z)

/-- Explicit `C^{0,α}` radius for a fixed-coefficient second-order
operator acting on a function with higher radius `N`. -/
def parabolicLinearSecondOrderRadius (NA NB NC N : ℝ) : ℝ :=
  ‖operatorEvaluation (X →L[ℝ] (X →L[ℝ] E)) E‖ * NA * N +
    ‖operatorEvaluation (X →L[ℝ] E) E‖ * NB * N +
      ‖operatorEvaluation E E‖ * NC * N

/-- A fixed-coefficient linear second-order operator maps a genuine
parabolic second jet with `C^{2+α,1+α/2}` radius `N` to a
`C^{0,α}` function, with a fully explicit coefficient radius. -/
theorem parabolicC0AlphaNormLe_parabolicLinearSecondOrder
    {A : ℝ × X → (X →L[ℝ] (X →L[ℝ] E)) →L[ℝ] E}
    {B : ℝ × X → (X →L[ℝ] E) →L[ℝ] E}
    {C : ℝ × X → E →L[ℝ] E}
    {u : ℝ × X → E} {s : Set (ℝ × X)}
    {NA NB NC N α : ℝ}
    (hA : ParabolicC0AlphaNormLe NA α A s)
    (hB : ParabolicC0AlphaNormLe NB α B s)
    (hC : ParabolicC0AlphaNormLe NC α C s)
    (hu : ParabolicC2AlphaNormLe N α u s)
    (J : ParabolicSecondJet u s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    ParabolicC0AlphaNormLe
      (parabolicLinearSecondOrderRadius (X := X) (E := E) NA NB NC N) α
      (parabolicLinearSecondOrder A B C u J) s := by
  rcases hu.secondJet_c0AlphaNormLe_self_of_unique J htime hspace with
    ⟨hu0, hu1, hu2, _hut⟩
  have hprincipal := hA.continuousLinearMap₂
    (operatorEvaluation (X →L[ℝ] (X →L[ℝ] E)) E) hu2
  have hfirst := hB.continuousLinearMap₂
    (operatorEvaluation (X →L[ℝ] E) E) hu1
  have hzero := hC.continuousLinearMap₂ (operatorEvaluation E E) hu0
  convert hprincipal.add hfirst |>.add hzero using 1 <;> rfl

/-- The fixed-coefficient operator estimate on a difference of two functions.
All derivative differences come from the genuine jets of the two functions;
uniqueness of derivatives on the slices identifies them with the jet of the
pointwise difference. -/
theorem parabolicC0AlphaNormLe_parabolicLinearSecondOrder_sub
    {A : ℝ × X → (X →L[ℝ] (X →L[ℝ] E)) →L[ℝ] E}
    {B : ℝ × X → (X →L[ℝ] E) →L[ℝ] E}
    {C : ℝ × X → E →L[ℝ] E}
    {u v : ℝ × X → E} {s : Set (ℝ × X)}
    {NA NB NC N α : ℝ}
    (hA : ParabolicC0AlphaNormLe NA α A s)
    (hB : ParabolicC0AlphaNormLe NB α B s)
    (hC : ParabolicC0AlphaNormLe NC α C s)
    (huv : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    (Ju : ParabolicSecondJet u s) (Jv : ParabolicSecondJet v s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    ParabolicC0AlphaNormLe
      (parabolicLinearSecondOrderRadius (X := X) (E := E) NA NB NC N) α
      (fun z => parabolicLinearSecondOrder A B C u Ju z -
        parabolicLinearSecondOrder A B C v Jv z) s := by
  rcases huv.secondJet_sub_c0AlphaNormLe_self_of_unique Ju Jv htime hspace with
    ⟨hu0, hu1, hu2, _hut⟩
  have hprincipal := hA.continuousLinearMap₂
    (operatorEvaluation (X →L[ℝ] (X →L[ℝ] E)) E) hu2
  have hfirst := hB.continuousLinearMap₂
    (operatorEvaluation (X →L[ℝ] E) E) hu1
  have hzero := hC.continuousLinearMap₂ (operatorEvaluation E E) hu0
  have hsum := hprincipal.add hfirst |>.add hzero
  convert hsum using 1
  · rfl
  · funext z
    simp only [parabolicLinearSecondOrder, operatorEvaluation_apply, map_sub]
    module

/-- The residual `∂ₜu - Lu` of a fixed-coefficient operator is
`C^{0,α}` whenever `u` has a controlled genuine parabolic second jet. -/
theorem parabolicC0AlphaNormLe_timeDeriv_sub_parabolicLinearSecondOrder
    {A : ℝ × X → (X →L[ℝ] (X →L[ℝ] E)) →L[ℝ] E}
    {B : ℝ × X → (X →L[ℝ] E) →L[ℝ] E}
    {C : ℝ × X → E →L[ℝ] E}
    {u : ℝ × X → E} {s : Set (ℝ × X)}
    {NA NB NC N α : ℝ}
    (hA : ParabolicC0AlphaNormLe NA α A s)
    (hB : ParabolicC0AlphaNormLe NB α B s)
    (hC : ParabolicC0AlphaNormLe NC α C s)
    (hu : ParabolicC2AlphaNormLe N α u s)
    (J : ParabolicSecondJet u s)
    (htime : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (timeSliceDomain s z.2) z.1)
    (hspace : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      UniqueDiffWithinAt ℝ (spaceSliceDomain s z.1) z.2) :
    ParabolicC0AlphaNormLe
      (N + parabolicLinearSecondOrderRadius (X := X) (E := E) NA NB NC N) α
      (fun z => J.timeDeriv z - parabolicLinearSecondOrder A B C u J z) s := by
  have ht := (hu.secondJet_c0AlphaNormLe_self_of_unique J htime hspace).2.2.2
  exact ht.sub (parabolicC0AlphaNormLe_parabolicLinearSecondOrder
    hA hB hC hu J htime hspace)

end AnalyticPDE
end RicciFlow
