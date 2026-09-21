/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectionWeightedTail
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionScalarFiniteP
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.Cube

/-!
# Square-weighted tails of reflected scalars

Scalar odd reflection preserves square-weighted level tails up to the exact
`3^d` parent-volume factor.  The proof embeds the scalar into one coordinate
of the existing reflected-vector API; the zero-dimensional case is direct.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

private theorem norm_cubeCoordinateFoldSign_scalarWeightedTail
    {d : ℕ} (Q : TriadicCube d) (x : Vec d) (i : Fin d) :
    ‖cubeCoordinateFoldSign Q x i‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [Real.norm_eq_abs, sq_abs, one_pow, pow_two,
    cubeCoordinateFoldSign_mul_self]

private theorem aestronglyMeasurable_hilbertVec_single
    {α : Type*} [MeasurableSpace α] {d : ℕ} (i : Fin d)
    {F : α → ℝ} {μ : Measure α} (hF : AEStronglyMeasurable F μ) :
    AEStronglyMeasurable
      (fun x ↦ HilbertVec.ofVec (Pi.single i (F x))) μ := by
  let L : ℝ →L[ℝ] HilbertVec d :=
    (HilbertVec.ofVecL d).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin d ↦ ℝ) i)
  have hL := L.continuous.comp_aestronglyMeasurable hF
  simpa only [L, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.single_apply, HilbertVec.ofVecL_apply] using hL

private theorem norm_hilbertVec_single_eq
    {d : ℕ} (i : Fin d) (t : ℝ) :
    ‖HilbertVec.ofVec (Pi.single i t)‖ = ‖t‖ := by
  exact PiLp.norm_single 2 (fun _ : Fin d ↦ ℝ) i t

private theorem
    norm_hilbertVec_cubeDirichletOddReflectionVectorField_single_eq_scalar
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (F : Vec d → ℝ)
    (x : Vec d) :
    ‖HilbertVec.ofVec
        (cubeDirichletOddReflectionVectorField Q
          (fun y ↦ Pi.single i (F y)) x)‖ =
      ‖cubeDirichletOddReflectionScalar Q F x‖ := by
  have hvector :
      cubeDirichletOddReflectionVectorField Q
          (fun y ↦ Pi.single i (F y)) x =
        Pi.single i
          (cubeCoordinateFoldSign Q x i *
            cubeDirichletOddReflectionScalar Q F x) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp only [cubeDirichletOddReflectionVectorField_apply,
        cubeCoordinateFoldReflectedVectorField, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_same, cubeDirichletOddReflectionScalar_apply]
      ring
    · simp only [cubeDirichletOddReflectionVectorField_apply,
        cubeCoordinateFoldReflectedVectorField, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_of_ne hji, mul_zero]
  rw [hvector, norm_hilbertVec_single_eq, norm_mul,
    norm_cubeCoordinateFoldSign_scalarWeightedTail, one_mul]

private theorem openCubeSet_originCube_zero_eq_univ (m : ℤ) :
    openCubeSet (originCube 0 m) = Set.univ := by
  ext x
  simp only [openCubeSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact fun i ↦ Fin.elim0 i

private theorem scaledOpenCubeSet_originCube_zero_eq_univ
    (m : ℤ) (r : ℝ) :
    scaledOpenCubeSet (originCube 0 m) r = Set.univ := by
  ext x
  simp only [scaledOpenCubeSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact fun i ↦ Fin.elim0 i

private theorem cubeDirichletOddReflectionScalar_originCube_zero
    (m : ℤ) (F : Vec 0 → ℝ) :
    cubeDirichletOddReflectionScalar (originCube 0 m) F = F := by
  funext x
  rw [cubeDirichletOddReflectionScalar_apply]
  have hfold : cubeCoordinateFold (originCube 0 m) x = x :=
    Subsingleton.elim _ _
  rw [hfold]
  have hsign : cubeDirichletOddReflectionSign (originCube 0 m) x = 1 := by
    unfold cubeDirichletOddReflectionSign
    apply Finset.prod_eq_one
    intro i _
    exact Fin.elim0 i
  rw [hsign, one_mul]

/-- A square-weighted norm tail of the scalar Dirichlet odd reflection on a
centered parent cube is exactly `3^d` copies of its source-cube tail. -/
theorem
    sqWeightedMeasure_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar_tail
    {d : ℕ} {m : ℤ} (F : Vec d → ℝ) {a : ℝ}
    (hF : AEStronglyMeasurable F
      (volume.restrict (openCubeSet (originCube d m)))) :
    sqWeightedMeasure
        (cubeDirichletOddReflectionScalar (originCube d m) F) volume
        ({x | a < ‖cubeDirichletOddReflectionScalar
          (originCube d m) F x‖} ∩ openCubeSet (originCube d (m + 1))) =
      ((3 : ℝ≥0∞) ^ d) *
        sqWeightedMeasure F volume
          ({x | a < ‖F x‖} ∩ openCubeSet (originCube d m)) := by
  classical
  by_cases hd : d = 0
  · subst d
    simp only [cubeDirichletOddReflectionScalar_originCube_zero,
      openCubeSet_originCube_zero_eq_univ, Set.inter_univ, pow_zero, one_mul]
  · let i : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    let G : Vec d → Vec d := fun x ↦ Pi.single i (F x)
    let Sref : Vec d → ℝ :=
      cubeDirichletOddReflectionScalar (originCube d m) F
    let Vref : Vec d → HilbertVec d := fun x ↦
      HilbertVec.ofVec
        (cubeDirichletOddReflectionVectorField (originCube d m) G x)
    let Vsource : Vec d → HilbertVec d :=
      fun x ↦ HilbertVec.ofVec (G x)
    have hG : AEStronglyMeasurable Vsource
        (volume.restrict (openCubeSet (originCube d m))) := by
      simpa only [Vsource, G] using
        aestronglyMeasurable_hilbertVec_single i hF
    have hsourceNorm : ∀ x, ‖Vsource x‖ = ‖F x‖ := by
      intro x
      exact norm_hilbertVec_single_eq i (F x)
    have hreflectedNorm : ∀ x, ‖Vref x‖ = ‖Sref x‖ := by
      intro x
      exact
        norm_hilbertVec_cubeDirichletOddReflectionVectorField_single_eq_scalar
          (originCube d m) i F x
    have hsourceMeasure :
        sqWeightedMeasure Vsource volume = sqWeightedMeasure F volume := by
      apply MeasureTheory.withDensity_congr_ae
      filter_upwards with x
      rw [hsourceNorm x]
    have hreflectedMeasure :
        sqWeightedMeasure Vref volume = sqWeightedMeasure Sref volume := by
      apply MeasureTheory.withDensity_congr_ae
      filter_upwards with x
      rw [hreflectedNorm x]
    have hsourceTail :
        {x | a < ‖Vsource x‖} = {x | a < ‖F x‖} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [hsourceNorm x]
    have hreflectedTail :
        {x | a < ‖Vref x‖} = {x | a < ‖Sref x‖} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [hreflectedNorm x]
    have hvector :=
      sqWeightedMeasure_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_tail
        G hG (a := a)
    change sqWeightedMeasure Sref volume
        ({x | a < ‖Sref x‖} ∩ openCubeSet (originCube d (m + 1))) = _
    rw [← hreflectedMeasure, ← hreflectedTail,
      ← hsourceMeasure, ← hsourceTail]
    exact hvector

/-- The square-weighted scalar-reflection tail on the half-scaled parent is
bounded by the exact `3^d` source-cube tail. -/
theorem
    sqWeightedMeasure_innerHalf_succ_originCube_cubeDirichletOddReflectionScalar_tail_le
    {d : ℕ} {m : ℤ} (F : Vec d → ℝ) {a : ℝ}
    (hF : AEStronglyMeasurable F
      (volume.restrict (openCubeSet (originCube d m)))) :
    sqWeightedMeasure
        (cubeDirichletOddReflectionScalar (originCube d m) F) volume
        ({x | a < ‖cubeDirichletOddReflectionScalar
          (originCube d m) F x‖} ∩
          scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)) ≤
      ((3 : ℝ≥0∞) ^ d) *
        sqWeightedMeasure F volume
          ({x | a < ‖F x‖} ∩ openCubeSet (originCube d m)) := by
  let Qp : TriadicCube d := originCube d (m + 1)
  let Sref : Vec d → ℝ :=
    cubeDirichletOddReflectionScalar (originCube d m) F
  have hhalf : scaledOpenCubeSet Qp (1 / 2 : ℝ) ⊆ openCubeSet Qp := by
    intro x hx
    rw [← ball_cubeCenter_eq_openCubeSet]
    have hxclosed :
        x ∈ Metric.closedBall (cubeCenter Qp)
          ((1 / 2 : ℝ) * cubeRadius Qp) :=
      scaledClosedCubeSet_subset_metricClosedBall Qp
        (by norm_num : 0 ≤ (1 / 2 : ℝ)) (fun i ↦ le_of_lt (hx i))
    exact Metric.closedBall_subset_ball (by
      nlinarith [cubeRadius_pos Qp]) hxclosed
  calc
    sqWeightedMeasure Sref volume
        ({x | a < ‖Sref x‖} ∩ scaledOpenCubeSet Qp (1 / 2 : ℝ)) ≤
        sqWeightedMeasure Sref volume
          ({x | a < ‖Sref x‖} ∩ openCubeSet Qp) := by
          exact measure_mono (Set.inter_subset_inter_right _ hhalf)
    _ = ((3 : ℝ≥0∞) ^ d) *
        sqWeightedMeasure F volume
          ({x | a < ‖F x‖} ∩ openCubeSet (originCube d m)) := by
          simpa only [Sref, Qp] using
            sqWeightedMeasure_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar_tail
              F hF (a := a)

end CubeCalderonZygmund

end

end Homogenization
