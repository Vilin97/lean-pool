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

public import LeanPool.PoincareGeometry.AlmostSchur.ChartTestLift
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyPairingCoefficients
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Actual inverse-Gram formula for the coordinate Riemannian gradient

The cometric formula follows from the Riesz characterization and the tangent
trivialization. No coordinate-gradient identification is assumed.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology BigOperators

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gram matrix sends the actual gradient coordinates to the scalar differential. -/
theorem coordinateMetric_mulVec_gradient (b : OrthonormalBasis ι ℝ E) (c : M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    {z : E} (hz : z ∈ (extChartAt I c).target) :
    (coordinateMetric (I := I) b.toBasis c z).mulVec
      (b.repr (coordinateVectorField (I := I) c (gradient (I := I) f) z)) =
      fun i => fderiv ℝ (f ∘ (extChartAt I c).symm) z (b i) := by
  let χ := extChartAt I c
  let x := χ.symm z
  let e := trivializationAt E (TangentSpace I) c
  have hx : x ∈ (chartAt H c).source := by simpa only [x, χ, extChartAt_source] using χ.map_target hz
  have he : x ∈ e.baseSet := hx
  let q := coordinateVectorField (I := I) c (gradient (I := I) f) z
  have hrec : e.symmL ℝ x q = gradient (I := I) f x :=
    e.symmL_continuousLinearMapAt he _
  ext i
  have hd := fderiv_chart_comp f c x hx (hf.mdifferentiableAt (by norm_num)) (b i)
  have hz' : χ x = z := χ.right_inv hz
  change fderiv ℝ (f ∘ χ.symm) (χ x) (b i) = _ at hd
  rw [hz'] at hd
  rw [hd, ← inner_gradient, real_inner_comm, ← hrec, ← b.sum_repr q]
  simp only [map_sum, map_smul, inner_sum, real_inner_smul_right]
  change (∑ j, coordinateMetric (I := I) b.toBasis c z i j * b.repr q j) = _
  apply Finset.sum_congr rfl
  intro j _
  simp only [coordinateMetric, tangentChartGram, tangentTrivializationGram, Matrix.gram_apply,
    OrthonormalBasis.coe_toBasis, x, χ, e]
  ring

/-- The actual coordinate gradient is obtained by applying the inverse Gram matrix. -/
theorem coordinateGradient_eq_invMetric_mulVec (b : OrthonormalBasis ι ℝ E) (c : M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    {z : E} (hz : z ∈ (extChartAt I c).target) :
    b.repr (coordinateVectorField (I := I) c (gradient (I := I) f) z) =
      (coordinateMetric (I := I) b.toBasis c z)⁻¹.mulVec
        (fun j => fderiv ℝ (f ∘ (extChartAt I c).symm) z (b j)) := by
  rw [← coordinateMetric_mulVec_gradient b c f hf hz, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (coordinateMetric_posDef b.toBasis c z hz).det_pos.ne'), Matrix.one_mulVec]

/-- Component form, directly usable in divergence-form energy integrals. -/
theorem coordinateGradient_component_eq_sum (b : OrthonormalBasis ι ℝ E) (c : M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    {z : E} (hz : z ∈ (extChartAt I c).target) (i : ι) :
    inner ℝ (b i) (coordinateVectorField (I := I) c (gradient (I := I) f) z) =
      ∑ j, (coordinateMetric (I := I) b.toBasis c z)⁻¹ i j *
        fderiv ℝ (f ∘ (extChartAt I c).symm) z (b j) := by
  have h := congrFun (coordinateGradient_eq_invMetric_mulVec b c f hf hz) i
  simpa only [OrthonormalBasis.repr_apply_apply, Matrix.mulVec, dotProduct] using h

end AlmostSchur
