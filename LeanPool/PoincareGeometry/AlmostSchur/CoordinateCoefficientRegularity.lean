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

public import LeanPool.PoincareGeometry.AlmostSchur.CoordinateEllipticity
public import LeanPool.PoincareGeometry.AlmostSchur.MatrixInverseRegularity
public import LeanPool.PoincareGeometry.AlmostSchur.DivergenceRegularity
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Regularity and compact derivative bounds for elliptic coefficients

The actual density-weighted inverse metric is C¹ on its chart domain. Compact
subsets have bounded derivatives, giving the coefficient estimate required
for difference-quotient commutators on convex interior neighborhoods.
-/

@[expose] public noncomputable section
open Bundle Set
open scoped ContDiff Manifold Matrix.Norms.Elementwise

namespace AlmostSchur

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Density weighting and inversion preserve any available differentiability order. -/
theorem contDiffOn_densityWeightedInverse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : WithTop ℕ∞} {U : Set V} (A : V → Matrix ι ι ℝ)
    (hA : ContDiffOn ℝ n A U) (hp : ∀ x ∈ U, 0 < (A x).det) :
    ContDiffOn ℝ n (fun x => matrixDensity (A x) • (A x)⁻¹) U := by
  have hd : ContDiffOn ℝ n (fun x => matrixDensity (A x)) U :=
    ((determinantMultilinear (ι := ι)).contDiff.comp_contDiffOn hA).sqrt
      (fun x hx => (hp x hx).ne')
  exact hd.smul (contDiffOn_matrix_inverse A hA (fun x hx => (hp x hx).ne'))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M]

/-- C¹ regularity of the actual elliptic coefficients, not a separate coefficient assumption. -/
theorem contDiffOn_coordinateEllipticMatrix (b : Module.Basis ι ℝ E) (c : M) :
    ContDiffOn ℝ 1 (coordinateEllipticMatrix (I := I) b c) (extChartAt I c).target :=
  contDiffOn_densityWeightedInverse _ (contDiffOn_coordinateMetric b c)
    (fun z hz => (coordinateMetric_posDef b c z hz).det_pos)

/-- All entries of the actual coefficient matrix have one finite compact bound. -/
theorem exists_coordinateEllipticMatrix_entry_bound (b : Module.Basis ι ℝ E) (c : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ i j : ι,
      |coordinateEllipticMatrix (I := I) b c z i j| ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((contDiffOn_coordinateEllipticMatrix (I := I) b c).continuousOn.mono hKt)
  refine ⟨max C 0, le_max_right _ _, fun z hz i j => ?_⟩
  exact (Matrix.norm_entry_le_entrywise_sup_norm _).trans
    ((hC z hz).trans (le_max_left _ _))

/-- Coordinate coefficient derivatives have a finite uniform bound on compact chart subsets. -/
theorem exists_coordinateEllipticMatrix_derivative_bound (b : Module.Basis ι ℝ E) (c : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ i j : ι,
      ‖fderiv ℝ (fun y => coordinateEllipticMatrix (I := I) b c y i j) z‖ ≤ C := by
  classical
  have hb (i j : ι) : ∃ C : ℝ, ∀ z ∈ K,
      ‖fderiv ℝ (fun y => coordinateEllipticMatrix (I := I) b c y i j) z‖ ≤ C := by
    have hd := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_coordinateEllipticMatrix (I := I) b c) i) j
    have hc := hd.continuousOn_fderiv_of_isOpen (isOpen_extChartAt_target c) (by norm_num)
    exact hK.exists_bound_of_continuousOn (hc.mono hKt)
  choose C hC using hb
  refine ⟨∑ i, ∑ j, max (C i j) 0, ?_, fun z hz i j => ?_⟩
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => le_max_right _ _
  · calc
      _ ≤ C i j := hC i j z hz
      _ ≤ max (C i j) 0 := le_max_left _ _
      _ ≤ ∑ j, max (C i j) 0 := Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ j)
      _ ≤ ∑ i, ∑ j, max (C i j) 0 := Finset.single_le_sum
        (fun i _ => Finset.sum_nonneg fun j _ => le_max_right _ _) (Finset.mem_univ i)

/-- On convex compact chart subsets, actual coefficients obey a uniform difference estimate. -/
theorem exists_coordinateEllipticMatrix_difference_bound (b : Module.Basis ι ℝ E) (c : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    (hconv : Convex ℝ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖coordinateEllipticMatrix (I := I) b c y - coordinateEllipticMatrix (I := I) b c x‖ ≤
        C * ‖y - x‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_coordinateEllipticMatrix_derivative_bound b c hK hKt
  refine ⟨C, hC0, fun x hx y hy => ?_⟩
  apply (Matrix.norm_le_iff (mul_nonneg hC0 (norm_nonneg _))).mpr
  intro i j
  have hd := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_coordinateEllipticMatrix (I := I) b c) i) j
  exact hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hd.contDiffAt ((isOpen_extChartAt_target c).mem_nhds (hKt hz))).differentiableAt
      (by norm_num))
    (fun z hz => hC z hz i j) hx hy

/-- The coefficient commutator has a uniform directional difference-quotient bound. -/
theorem exists_coordinateEllipticMatrix_quotient_bound (b : Module.Basis ι ℝ E) (c : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    (hconv : Convex ℝ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x v : E) (h : ℝ), h ≠ 0 → x ∈ K → x + h • v ∈ K →
      ‖h⁻¹ • (coordinateEllipticMatrix (I := I) b c (x + h • v) -
        coordinateEllipticMatrix (I := I) b c x)‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_coordinateEllipticMatrix_difference_bound b c hK hKt hconv
  refine ⟨C, hC0, fun x v h hh hx hxh => ?_⟩
  have hb := hC x hx (x + h • v) hxh
  rw [add_sub_cancel_left, norm_smul] at hb
  rw [norm_smul]
  calc
    _ ≤ ‖h⁻¹‖ * (C * (‖h‖ * ‖v‖)) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = C * ‖v‖ := by
      rw [norm_inv]
      field_simp

end AlmostSchur
