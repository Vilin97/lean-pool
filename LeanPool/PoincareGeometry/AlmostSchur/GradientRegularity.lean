/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.Gradient
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Regularity of the intrinsic Riemannian gradient

The gradient is the Riesz representative defined in `AlmostSchur.Gradient`.
The proof uses the smooth metric bundle map and inversion in local coordinates.

On a smooth finite-dimensional manifold, a Cⁿ metric and a Cⁿ⁺¹ function give
a Cⁿ gradient for every finite n. In particular a C¹ metric and a C² function
give a differentiable gradient, and smooth metric/function data give a smooth
gradient. The model-with-corners framework is retained throughout.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "DM" => (fun x : M => TM x →L[ℝ] ℝ)

local instance gradientRegularityFiniteDimensionalTangentSpace (x : M) :
    FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

omit [FiniteDimensional ℝ E] [RiemannianBundle TM] in
/-- A scalar differential is a section of the cotangent bundle, with one derivative lost. -/
theorem contMDiffAt_differential (n : ℕ) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) (n + 1) f x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) y (mvfderiv (I := I) f y)) x := by
  apply (contMDiffAt_hom_bundle _).2
  refine ⟨contMDiffAt_id, ?_⟩
  have h := hf.mfderiv_const (m := (n : ℕ∞ω)) (by rfl)
  convert h using 1
  funext y
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates, mvfderiv]
  ext v
  rfl

/-- The inverse Riesz map is a smooth bundle morphism whenever the metric is smooth
to the same order. This does not assume any smoothness of the gradient. -/
theorem contMDiffAt_rieszInverse (n : ℕ)
    [IsContMDiffRiemannianBundle I n E TM] (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E)) n
      (fun y => TotalSpace.mk' ((E →L[ℝ] ℝ) →L[ℝ] E)
        (E := fun y => DM y →L[ℝ] TM y) y
        ((InnerProductSpace.toDual ℝ (TM y)).symm.toContinuousLinearEquiv :
          DM y ≃L[ℝ] TM y).toContinuousLinearMap) x := by
  let R (y : M) : TM y ≃L[ℝ] DM y :=
    (InnerProductSpace.toDual ℝ (TM y)).toContinuousLinearEquiv
  have hR : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TM y →L[ℝ] DM y) y (R y).toContinuousLinearMap) := by
    obtain ⟨g, hg, heq⟩ :=
      (inferInstance : IsContMDiffRiemannianBundle I n E TM).exists_contMDiff
    convert hg using 1
    funext y
    congr 1
    ext u v
    exact heq y u v
  let A (y : M) := ContinuousLinearMap.inCoordinates E TM (E →L[ℝ] ℝ) DM
    x y x y (R y).toContinuousLinearMap
  have hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)) n A x :=
    ((contMDiffAt_hom_bundle _).1 (hR x)).2
  have hAx : (A x).IsInvertible := by
    dsimp [A]
    rw [ContinuousLinearMap.inCoordinates_eq
      (mem_baseSet_trivializationAt E TM x)
      (mem_baseSet_trivializationAt (E →L[ℝ] ℝ) DM x)]
    exact ContinuousLinearMap.isInvertible_equiv.comp
      (ContinuousLinearMap.isInvertible_equiv.comp ContinuousLinearMap.isInvertible_equiv)
  have hinv : ContMDiffAt I 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E) n
      (fun y => ContinuousLinearMap.inverse (A y)) x :=
    hAx.contDiffAt_map_inverse.contMDiffAt.comp x hA
  apply (contMDiffAt_hom_bundle _).2
  refine ⟨contMDiffAt_id, ?_⟩
  apply hinv.congr_of_eventuallyEq
  have hT := (trivializationAt E TM x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E TM x)
  have hD := (trivializationAt (E →L[ℝ] ℝ) DM x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt (E →L[ℝ] ℝ) DM x)
  filter_upwards [hT, hD] with y hy hdy
  dsimp [A]
  rw [ContinuousLinearMap.inCoordinates_eq hy hdy,
    ContinuousLinearMap.inCoordinates_eq hdy hy]
  simp only [ContinuousLinearMap.inverse_equiv_comp, ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.symm_symm]
  rfl

/-- Finite regularity of the actual Riesz gradient at a point: a Cⁿ metric and
a Cⁿ⁺¹ scalar function give a Cⁿ tangent section. -/
theorem contMDiffAt_gradient (n : ℕ)
    [IsContMDiffRiemannianBundle I n E TM] {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) (n + 1) f x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (T% (gradient (I := I) f)) x := by
  exact ContMDiffAt.clm_bundle_apply (F₁ := E →L[ℝ] ℝ) (E₁ := DM)
    (F₂ := E) (E₂ := TM) (contMDiffAt_rieszInverse (I := I) n x)
    (contMDiffAt_differential n hf)

/-- Global finite regularity, with the one-derivative loss on the scalar function explicit. -/
theorem contMDiff_gradient (n : ℕ)
    [IsContMDiffRiemannianBundle I n E TM] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (n + 1) f) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) n (T% (gradient (I := I) f)) :=
  fun x => contMDiffAt_gradient n (hf x)

/-- A C² function has a differentiable gradient under a C¹ Riemannian metric. -/
theorem mdifferentiableAt_gradient
    [IsContMDiffRiemannianBundle I 1 E TM] {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (gradient (I := I) f)) x := by
  let gradientRegularityMetricOne : IsContMDiffRiemannianBundle I (↑(1 : ℕ)) E TM :=
    IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
  exact (contMDiffAt_gradient 1 hf).mdifferentiableAt (by norm_num)

/-- The actual gradient of a globally C² function is a differentiable tangent section. -/
theorem mdifferentiable_gradient
    [IsContMDiffRiemannianBundle I 1 E TM] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) :
    MDifferentiable I (I.prod 𝓘(ℝ, E)) (T% (gradient (I := I) f)) :=
  fun x => mdifferentiableAt_gradient (hf x)

/-- A smooth function on a smooth Riemannian manifold has a smooth intrinsic gradient. -/
theorem contMDiff_gradient_infty
    [IsContMDiffRiemannianBundle I ∞ E TM] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (gradient (I := I) f)) := by
  rw [contMDiff_infty]
  intro n
  exact contMDiff_gradient n (hf.of_le
    (WithTop.coe_le_coe.2 (le_top : (n : ℕ∞) + 1 ≤ ⊤)))

end AlmostSchur
