/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.Coordinates
public import LeanPool.Odlyzko.Theta.TorusPeriodization

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Module

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A coordinate gaussian used in the Odlyzko-bound argument. -/
noncomputable def coordinateGaussian
    (b : Basis ι ℤ L) (a : ℝ) (x : ι → ℝ) : ℂ :=
  latticeGaussian a ((b.ofZLatticeBasis ℝ L).equivFun.symm x)

/-- A coordinate basis map used in the Odlyzko-bound argument. -/
noncomputable def coordinateBasisMap (b : Basis ι ℤ L) :
    C(ι → ℝ, E) :=
  let e := LinearEquiv.toContinuousLinearEquiv
    (b.ofZLatticeBasis ℝ L).equivFun.symm
  ⟨e, e.continuous⟩

omit [DecidableEq ι] in
theorem continuous_coordinateGaussian
    (b : Basis ι ℤ L) (a : ℝ) :
    Continuous (coordinateGaussian L b a) := by
  unfold coordinateGaussian latticeGaussian
  have hlin : Continuous fun x : ι → ℝ ↦
      (b.ofZLatticeBasis ℝ L).equivFun.symm x :=
    (LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm).continuous
  fun_prop

omit [DecidableEq ι] in
theorem ofZLatticeBasis_equivFun_symm_intCast
    (b : Basis ι ℤ L) (n : ι → ℤ) :
    (b.ofZLatticeBasis ℝ L).equivFun.symm (fun i ↦ (n i : ℝ)) =
      latticePoint L b n := by
  rw [Basis.equivFun_symm_apply, latticePoint,
    Basis.equivFun_symm_apply]
  have hcoe :
      ((↑(∑ i, n i • b i) : L) : E) =
        ∑ i, n i • (b i : E) := by simp
  rw [hcoe]
  apply Finset.sum_congr rfl
  intro i _
  rw [Basis.ofZLatticeBasis_apply]
  exact Int.cast_smul_eq_zsmul ℝ (n i) (b i : E)

/-- A coordinate gaussian translate used in the Odlyzko-bound argument. -/
noncomputable def coordinateGaussianTranslate
    (b : Basis ι ℤ L) (a : ℝ) (n : ι → ℤ) :
    C(ι → ℝ, ℂ) :=
  ⟨fun x ↦ coordinateGaussian L b a
      (x + fun i ↦ (n i : ℝ)),
    (continuous_coordinateGaussian L b a).comp
      (continuous_id.add (continuous_pi fun _ ↦ continuous_const))⟩

omit [IsZLattice ℝ L] [DecidableEq ι] in
theorem summable_norm_latticeGaussian_latticePoint
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ι → ℤ ↦
      ‖latticeGaussian a (latticePoint L b n)‖) := by
  have hs := (Equiv.summable_iff
    (e := b.equivFun.toEquiv.symm)).mpr
      (summable_norm_latticeGaussian L ha)
  simpa [Function.comp_def, latticePoint] using hs

omit [DecidableEq ι] in
theorem norm_coordinateGaussianTranslate_apply_le
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a)
    (x : ι → ℝ) (n : ι → ℤ) :
    ‖coordinateGaussianTranslate L b a n x‖ ≤
      Real.exp (a * ‖coordinateBasisMap L b x‖ ^ 2) *
        ‖latticeGaussian (a / 2) (latticePoint L b n)‖ := by
  change ‖coordinateGaussian L b a
      (x + fun i ↦ (n i : ℝ))‖ ≤ _
  have hsplit :
      (b.ofZLatticeBasis ℝ L).equivFun.symm
          (x + fun i ↦ (n i : ℝ)) =
        coordinateBasisMap L b x + latticePoint L b n := by
    rw [map_add, ofZLatticeBasis_equivFun_symm_intCast]
    rfl
  rw [coordinateGaussian, hsplit]
  exact norm_latticeGaussian_add_le ha.le _ _

omit [DecidableEq ι] in
theorem norm_restrict_coordinateGaussianTranslate_le
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a)
    (K : TopologicalSpace.Compacts (ι → ℝ)) (n : ι → ℤ) :
    ‖(coordinateGaussianTranslate L b a n).restrict K‖ ≤
      Real.exp (a * ‖(coordinateBasisMap L b).restrict K‖ ^ 2) *
        ‖latticeGaussian (a / 2) (latticePoint L b n)‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.exp_pos _).le
    (norm_nonneg _))).2
  intro x
  refine (norm_coordinateGaussianTranslate_apply_le
    L b ha x n).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ ha.le
  have hx := ContinuousMap.norm_coe_le_norm
    ((coordinateBasisMap L b).restrict K) x
  change ‖coordinateBasisMap L b (x : ι → ℝ)‖ ≤
    ‖(coordinateBasisMap L b).restrict K‖ at hx
  nlinarith [norm_nonneg (coordinateBasisMap L b x),
    norm_nonneg ((coordinateBasisMap L b).restrict K)]

omit [DecidableEq ι] in
theorem summable_norm_restrict_coordinateGaussianTranslate
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a)
    (K : TopologicalSpace.Compacts (ι → ℝ)) :
    Summable (fun n : ι → ℤ ↦
      ‖(coordinateGaussianTranslate L b a n).restrict K‖) := by
  let C := Real.exp
    (a * ‖(coordinateBasisMap L b).restrict K‖ ^ 2)
  have hbase := summable_norm_latticeGaussian_latticePoint
    L b (half_pos ha)
  apply (hbase.mul_left C).of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_restrict_coordinateGaussianTranslate_le L b ha K n

omit [DecidableEq ι] in
private theorem summable_coordinateGaussianTranslate
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    Summable (coordinateGaussianTranslate L b a) := by
  classical
  apply ContinuousMap.summable_of_locally_summable_norm
  intro K
  exact summable_norm_restrict_coordinateGaussianTranslate L b ha K

omit [DecidableEq ι] in
theorem continuous_intPeriodization_coordinateGaussian
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    Continuous (intPeriodization (coordinateGaussian L b a)) := by
  classical
  let F := coordinateGaussianTranslate L b a
  have hF : Summable F :=
    summable_coordinateGaussianTranslate L b ha
  have hcontinuous : Continuous fun x : ι → ℝ ↦ (∑' n, F n) x :=
    (∑' n, F n).continuous
  have heval (x : ι → ℝ) :
      (∑' n, F n) x =
        intPeriodization (coordinateGaussian L b a) x := by
    calc
      (∑' n, F n) x = ∑' n, (F n) x :=
        (ContinuousMap.tsum_apply hF x).symm
      _ = intPeriodization (coordinateGaussian L b a) x := rfl
  simp_all

/-- A gaussian torus periodization used in the Odlyzko-bound argument. -/
noncomputable def gaussianTorusPeriodization
    (b : Basis ι ℤ L) (a : ℝ) (ha : 0 < a) :
    C(UnitAddTorus ι, ℂ) :=
  torusPeriodization (coordinateGaussian L b a)
    (continuous_intPeriodization_coordinateGaussian L b ha)

omit [DecidableEq ι] in
theorem gaussianTorusPeriodization_zero
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    gaussianTorusPeriodization L b a ha 0 = latticeTheta L a := by
  classical
  rw [show (0 : UnitAddTorus ι) =
      torusQuotientMap (0 : ι → ℝ) by rfl]
  rw [gaussianTorusPeriodization,
    torusPeriodization_apply_quotient]
  unfold intPeriodization coordinateGaussian
  simp_rw [zero_add,
    ofZLatticeBasis_equivFun_symm_intCast]
  exact (latticeTheta_eq_tsum_coordinates L b a).symm

end NumberField.Odlyzko
