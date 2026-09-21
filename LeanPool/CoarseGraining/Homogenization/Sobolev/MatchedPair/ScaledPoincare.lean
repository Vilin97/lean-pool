/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.AxisCube
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1Dilation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1Translation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareMeanZero
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareZeroTrace
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.MeanZero
import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.Basic

/-! # Scaled Poincare -/

namespace Homogenization

open MeasureTheory Homogenization
open scoped ENNReal NNReal BigOperators Pointwise

/-!
# Scaled Poincaré inequalities on axis cubes

Two scaled Poincaré inequalities on axis cubes `U = axisCube z L`:

* `scaled_meanZero_poincare` — the mean-zero Poincaré inequality with the
  explicit `C_d · L` scaling;
* `scaled_dirichlet_poincare` — the zero-trace (Dirichlet) Poincaré inequality
  for `MemH10` functions, with the explicit `C_d · L` scaling.

Both are obtained from the corresponding existential Poincaré constant on the
fixed unit corner cube `axisCube 0 1` (whose constant is therefore an absolute
`C_d`), transported to `axisCube z L` along the affine dilation-plus-translation
`axisCube z L = translateSet z (L • axisCube 0 1)`.  The `H¹` weak-gradient
transport and constant bookkeeping are supplied by the reusable bridges
`H1CoerciveEstimate.dilate` / `.translate`, `H1Function.unscale`,
`H10Function.unscale`, `H10Function.untranslate`.
-/

noncomputable section

variable {d : ℕ}

/-! ## Geometry of axis cubes under dilation and translation -/

/-- The corner unit cube dilates to the corner cube of side `L`. -/
theorem smul_axisCube_zero_one (L : ℝ) (hL : 0 < L) :
    L • axisCube (0 : Homogenization.Vec d) 1 = axisCube (0 : Homogenization.Vec d) L := by
  have hL_ne : L ≠ 0 := hL.ne'
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hL_ne]
  simp only [axisCube, Set.mem_pi, Set.mem_univ, forall_true_left, zero_add,
    Set.mem_Ioo, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  have hinv : 0 < L⁻¹ := inv_pos.mpr hL
  constructor
  · intro h j
    have hj := h j
    constructor
    · have h1 := mul_pos hL hj.1
      rwa [mul_inv_cancel_left₀ hL_ne] at h1
    · have h2 := mul_lt_mul_of_pos_left hj.2 hL
      rwa [mul_inv_cancel_left₀ hL_ne, mul_one] at h2
  · intro h j
    have hj := h j
    constructor
    · exact mul_pos hinv hj.1
    · have hmul := mul_lt_mul_of_pos_left hj.2 hinv
      rwa [inv_mul_cancel₀ hL_ne] at hmul

/-- Translating the corner cube of side `L` by `z` gives `axisCube z L`. -/
theorem translateSet_axisCube_zero (z : Homogenization.Vec d) (L : ℝ) :
    translateSet z (axisCube (0 : Homogenization.Vec d) L) = axisCube z L := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  simp only [axisCube, Set.mem_pi, Set.mem_univ, forall_true_left, zero_add,
    Set.mem_Ioo, Pi.sub_apply, Pi.zero_apply]
  constructor
  · intro h j
    have hj := h j
    constructor
    · linarith [hj.1]
    · linarith [hj.2]
  · intro h j
    have hj := h j
    constructor
    · linarith [hj.1]
    · linarith [hj.2]

/-- The affine identification `axisCube z L = translateSet z (L • axisCube 0 1)`. -/
theorem axisCube_eq_translateSet_smul (z : Homogenization.Vec d) (L : ℝ) (hL : 0 < L) :
    axisCube z L = translateSet z (L • axisCube (0 : Homogenization.Vec d) 1) := by
  rw [smul_axisCube_zero_one L hL, translateSet_axisCube_zero]

/-! ## Finite-measure instances -/

instance isFiniteMeasure_volumeMeasureOn_axisCube
    (z : Homogenization.Vec d) (L : ℝ) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (axisCube z L)) := by
  simpa [volumeMeasureOn] using
    (isOpenBoundedConvexDomain_axisCube z L).isFiniteMeasure_restrict_volume

/-! ## The mean-zero coercive estimate, transported to axis cubes -/

/-- The absolute mean-zero Poincaré constant of the *fixed* unit corner cube
`axisCube 0 1`.  It depends only on the dimension `d`. -/
noncomputable def unitMeanZeroPoincareConst (d : ℕ) : ℝ :=
  (h1CoerciveEstimate_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_axisCube (0 : Homogenization.Vec d) 1)).fixedValue

theorem unitMeanZeroPoincareConst_nonneg (d : ℕ) :
    0 ≤ unitMeanZeroPoincareConst d :=
  (h1CoerciveEstimate_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_axisCube (0 : Homogenization.Vec d) 1)).constant_nonneg

private theorem coercive_constant_eqRec {V U : Set (Homogenization.Vec d)}
    (h : V = U) (hC : H1CoerciveEstimate V) :
    (h ▸ hC).fixedValue = hC.fixedValue := by cases h; rfl

/-- The mean-zero coercive `H¹` estimate on `axisCube z L`, obtained by dilating
the unit corner-cube estimate by `L` and translating by `z`.  Its constant is the
scale-correct `L · C_d`. -/
noncomputable def axisCubeMeanZeroCoerciveEstimate
    (z : Homogenization.Vec d) {L : ℝ} (hL : 0 < L) :
    H1CoerciveEstimate (axisCube z L) :=
  letI : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (L • axisCube (0 : Homogenization.Vec d) 1)) := by
    rw [smul_axisCube_zero_one L hL]
    exact isFiniteMeasure_volumeMeasureOn_axisCube 0 L
  (axisCube_eq_translateSet_smul z L hL).symm ▸
    (((h1CoerciveEstimate_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_axisCube (0 : Homogenization.Vec d) 1)).dilate hL).translate z)

theorem axisCubeMeanZeroCoerciveEstimate_constant
    (z : Homogenization.Vec d) {L : ℝ} (hL : 0 < L) :
    (axisCubeMeanZeroCoerciveEstimate z hL).fixedValue = L * unitMeanZeroPoincareConst d := by
  let : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (L • axisCube (0 : Homogenization.Vec d) 1)) := by
    rw [smul_axisCube_zero_one L hL]
    exact isFiniteMeasure_volumeMeasureOn_axisCube 0 L
  rw [axisCubeMeanZeroCoerciveEstimate, coercive_constant_eqRec,
    H1CoerciveEstimate.translate_constant, H1CoerciveEstimate.dilate_constant]
  rfl

/-! ## Bridges between the library's `L²` realizations and `eLpNorm` -/

/-- The `L²` realization norm of an `H¹` value is the `toReal` of its `eLpNorm`. -/
theorem norm_toScalarL2_eq {U : Set (Homogenization.Vec d)} (h : H1Function U) :
    ‖h.toScalarL2‖ = (eLpNorm h.toFun 2 (volumeMeasureOn U)).toReal := by
  simp only [H1Function.toScalarL2, Homogenization.toScalarL2]
  rw [MeasureTheory.Lp.norm_toLp]

/-- The `L²` realization norm of a gradient coordinate is the `toReal` of its
`eLpNorm`. -/
theorem norm_gradCoordToScalarL2_eq {U : Set (Homogenization.Vec d)}
    (h : H1Function U) (i : Fin d) :
    ‖h.gradCoordToScalarL2 i‖ =
      (eLpNorm (fun x => h.grad x i) 2 (volumeMeasureOn U)).toReal := by
  simp only [H1Function.gradCoordToScalarL2, Homogenization.toScalarL2]
  rw [MeasureTheory.Lp.norm_toLp]

/-! ## F0(i): scaled mean-zero Poincaré -/

/-- **Scaled mean-zero Poincaré on axis cubes.**

For `u ∈ H¹(axisCube z L)`, the `L²` norm of the mean-subtracted `u − ⨍u` is
controlled by `C_d · L` times the coordinate-sum `L²` norm of `∇u`. -/
theorem scaled_meanZero_poincare (z : Homogenization.Vec d) {L : ℝ} (hL : 0 < L)
    (u : H1Function (axisCube z L)) :
    (eLpNorm u.subAverage.toFun 2 (volumeMeasureOn (axisCube z L))).toReal
      ≤ unitMeanZeroPoincareConst d * L *
          ∑ i : Fin d,
            (eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal := by
  have hconst : (axisCubeMeanZeroCoerciveEstimate z hL).fixedValue =
      L * unitMeanZeroPoincareConst d :=
    axisCubeMeanZeroCoerciveEstimate_constant z hL
  have hb := (axisCubeMeanZeroCoerciveEstimate z hL).bound u.toMeanZero
  have hconst_nonneg : 0 ≤ (axisCubeMeanZeroCoerciveEstimate z hL).fixedValue :=
    (axisCubeMeanZeroCoerciveEstimate z hL).constant_nonneg
  -- Identify the value norm with the target left-hand side.
  have hval : (u.toMeanZero).valueL2Norm =
      (eLpNorm u.subAverage.toFun 2 (volumeMeasureOn (axisCube z L))).toReal := by
    unfold H1MeanZeroFunction.valueL2Norm H1MeanZeroFunction.toScalarL2
    rw [H1Function.toMeanZero_toH1Function, norm_toScalarL2_eq]
  -- The gradient norm is bounded by the coordinate-sum of the eLpNorms of ∇u.
  have hgrad_le : (u.toMeanZero).gradientL2Norm ≤
      ∑ i : Fin d, (eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal := by
    have hstep1 : (u.toMeanZero).gradientL2Norm ≤ u.subAverage.gradientCoordL2NormSum := by
      unfold H1MeanZeroFunction.gradientL2Norm H1MeanZeroFunction.gradToVectorL2
      rw [H1Function.toMeanZero_toH1Function]
      exact u.subAverage.norm_gradToVectorL2_le_gradientCoordL2NormSum
    have hstep2 : u.subAverage.gradientCoordL2NormSum =
        ∑ i : Fin d,
          (eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal := by
      unfold H1Function.gradientCoordL2NormSum
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [norm_gradCoordToScalarL2_eq]
      have hfun : (fun x => u.subAverage.grad x i) = (fun x => u.grad x i) := by
        funext x
        rw [H1Function.grad_subAverage]
      rw [hfun]
    exact hstep1.trans_eq hstep2
  -- Assemble.
  calc
    (eLpNorm u.subAverage.toFun 2 (volumeMeasureOn (axisCube z L))).toReal
        = (u.toMeanZero).valueL2Norm := hval.symm
    _ ≤ (axisCubeMeanZeroCoerciveEstimate z hL).fixedValue * (u.toMeanZero).gradientL2Norm := hb
    _ ≤ (axisCubeMeanZeroCoerciveEstimate z hL).fixedValue *
          ∑ i : Fin d,
            (eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal :=
          mul_le_mul_of_nonneg_left hgrad_le hconst_nonneg
    _ = unitMeanZeroPoincareConst d * L *
          ∑ i : Fin d,
            (eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal := by
          rw [hconst]; ring

/-! ## Translation- and cast-invariance of the `L²` realizations -/

/-- Translation preserves the `L²` value norm of an `H¹` witness. -/
theorem norm_toScalarL2_untranslate_eq {U : Set (Homogenization.Vec d)} (z : Homogenization.Vec d)
    (u : H1Function (translateSet z U)) :
    ‖(H1Function.untranslate z u).toScalarL2‖ = ‖u.toScalarL2‖ := by
  rw [norm_toScalarL2_eq, norm_toScalarL2_eq]
  congr 1
  have hμ := measurePreserving_addRight_restrict_translateSet (d := d) z U
  have hcomp := MeasureTheory.eLpNorm_comp_measurePreserving
    (g := u.toFun) (p := (2 : ℝ≥0∞)) u.memL2.aestronglyMeasurable hμ
  simpa [H1Function.untranslate_toFun, Function.comp, volumeMeasureOn] using! hcomp

/-- Translation preserves the coordinate-sum gradient `L²` norm. -/
theorem gradientCoordL2NormSum_untranslate_eq {U : Set (Homogenization.Vec d)}
    (z : Homogenization.Vec d) (u : H1Function (translateSet z U)) :
    (H1Function.untranslate z u).gradientCoordL2NormSum = u.gradientCoordL2NormSum := by
  unfold H1Function.gradientCoordL2NormSum
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [norm_gradCoordToScalarL2_eq, norm_gradCoordToScalarL2_eq]
  congr 1
  have hμ := measurePreserving_addRight_restrict_translateSet (d := d) z U
  have hcomp := MeasureTheory.eLpNorm_comp_measurePreserving
    (g := fun x => u.grad x i) (p := (2 : ℝ≥0∞))
    (u.gradMemL2 i).aestronglyMeasurable hμ
  simpa [H1Function.untranslate_grad, Function.comp, volumeMeasureOn] using! hcomp

/-- Rewriting the domain along a set equality preserves the `L²` value norm. -/
theorem norm_toScalarL2_h10_congr {U V : Set (Homogenization.Vec d)}
    (h : U = V) (w : H10Function U) :
    ‖(h ▸ w).toH1Function.toScalarL2‖ = ‖w.toH1Function.toScalarL2‖ := by
  cases h; rfl

/-- Rewriting the domain along a set equality preserves the coordinate-sum
gradient norm. -/
theorem gradientCoordL2NormSum_h10_congr {U V : Set (Homogenization.Vec d)}
    (h : U = V) (w : H10Function U) :
    (h ▸ w).toH1Function.gradientCoordL2NormSum = w.toH1Function.gradientCoordL2NormSum := by
  cases h; rfl

/-! ## F0(ii): scaled Dirichlet (zero-trace) Poincaré -/

/-- The absolute zero-trace Poincaré constant of the fixed unit corner cube. -/
noncomputable def unitDirichletPoincareConst (d : ℕ) [NeZero d] : ℝ :=
  (H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_axisCube (0 : Homogenization.Vec d) 1)).choose

theorem unitDirichletPoincareConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ unitDirichletPoincareConst d :=
  (H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_axisCube (0 : Homogenization.Vec d) 1)).choose_spec.1

theorem unitDirichletPoincareConst_bound {d : ℕ} [NeZero d]
    (w : H10Function (axisCube (0 : Homogenization.Vec d) 1)) :
    ‖w.toH1Function.toScalarL2‖ ≤
      unitDirichletPoincareConst d * w.toH1Function.gradientCoordL2NormSum :=
  (H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_axisCube (0 : Homogenization.Vec d) 1)).choose_spec.2 w

/-- **Scaled Dirichlet Poincaré on axis cubes (norm form).**

For `w ∈ H¹₀(axisCube z L)`, the `L²` realization norm of `w` is controlled by
`C_d · L` times the coordinate-sum gradient norm of `∇w`. -/
theorem scaled_dirichlet_poincare_norm {d : ℕ} [NeZero d] (z : Homogenization.Vec d) {L : ℝ}
    (hL : 0 < L) (w : H10Function (axisCube z L)) :
    ‖w.toH1Function.toScalarL2‖ ≤
      unitDirichletPoincareConst d * L * w.toH1Function.gradientCoordL2NormSum := by
  have heq1 : axisCube z L = translateSet z (axisCube (0 : Homogenization.Vec d) L) :=
    (translateSet_axisCube_zero z L).symm
  have heq2 : axisCube (0 : Homogenization.Vec d) L = L • axisCube (0 : Homogenization.Vec d) 1 :=
    (smul_axisCube_zero_one L hL).symm
  -- Transport `w` to the fixed unit corner cube.
  let w1 : H10Function (translateSet z (axisCube (0 : Homogenization.Vec d) L)) := heq1 ▸ w
  let w2 : H10Function (axisCube (0 : Homogenization.Vec d) L) := H10Function.untranslate z w1
  let w3 : H10Function (L • axisCube (0 : Homogenization.Vec d) 1) := heq2 ▸ w2
  let w4 : H10Function (axisCube (0 : Homogenization.Vec d) 1) := H10Function.unscale hL w3
  have hFpos : 0 < dilationL2Factor d L := dilationL2Factor_pos (d := d) hL
  -- Value-norm transport chain.
  have hvalNorm : ‖w4.toH1Function.toScalarL2‖ =
      dilationL2Factor d L * ‖w.toH1Function.toScalarL2‖ := by
    have e1 : ‖w4.toH1Function.toScalarL2‖ =
        dilationL2Factor d L * ‖w3.toH1Function.toScalarL2‖ := by
      show ‖(H10Function.unscale hL w3).toH1Function.toScalarL2‖ = _
      rw [H10Function.unscale_toH1Function]
      exact H1Function.norm_toScalarL2_unscale_eq hL w3.toH1Function
    have e2 : ‖w3.toH1Function.toScalarL2‖ = ‖w2.toH1Function.toScalarL2‖ :=
      norm_toScalarL2_h10_congr heq2 w2
    have e3 : ‖w2.toH1Function.toScalarL2‖ = ‖w1.toH1Function.toScalarL2‖ := by
      show ‖(H10Function.untranslate z w1).toH1Function.toScalarL2‖ = _
      rw [H10Function.untranslate_toH1Function]
      exact norm_toScalarL2_untranslate_eq z w1.toH1Function
    have e4 : ‖w1.toH1Function.toScalarL2‖ = ‖w.toH1Function.toScalarL2‖ :=
      norm_toScalarL2_h10_congr heq1 w
    rw [e1, e2, e3, e4]
  -- Gradient-norm transport chain.
  have hgradNorm : w4.toH1Function.gradientCoordL2NormSum =
      L * dilationL2Factor d L * w.toH1Function.gradientCoordL2NormSum := by
    have e1 : w4.toH1Function.gradientCoordL2NormSum =
        L * dilationL2Factor d L * w3.toH1Function.gradientCoordL2NormSum := by
      show (H10Function.unscale hL w3).toH1Function.gradientCoordL2NormSum = _
      rw [H10Function.unscale_toH1Function]
      exact H1Function.gradientCoordL2NormSum_unscale_eq hL w3.toH1Function
    have e2 : w3.toH1Function.gradientCoordL2NormSum =
        w2.toH1Function.gradientCoordL2NormSum :=
      gradientCoordL2NormSum_h10_congr heq2 w2
    have e3 : w2.toH1Function.gradientCoordL2NormSum =
        w1.toH1Function.gradientCoordL2NormSum := by
      show (H10Function.untranslate z w1).toH1Function.gradientCoordL2NormSum = _
      rw [H10Function.untranslate_toH1Function]
      exact gradientCoordL2NormSum_untranslate_eq z w1.toH1Function
    have e4 : w1.toH1Function.gradientCoordL2NormSum =
        w.toH1Function.gradientCoordL2NormSum :=
      gradientCoordL2NormSum_h10_congr heq1 w
    rw [e1, e2, e3, e4]
  -- Unit-cube Dirichlet Poincaré, rescaled.
  have hunit := unitDirichletPoincareConst_bound (d := d) w4
  rw [hvalNorm, hgradNorm] at hunit
  -- Cancel the common positive dilation factor.
  have hcancel : dilationL2Factor d L * ‖w.toH1Function.toScalarL2‖ ≤
      dilationL2Factor d L *
        (unitDirichletPoincareConst d * L * w.toH1Function.gradientCoordL2NormSum) := by
    calc
      dilationL2Factor d L * ‖w.toH1Function.toScalarL2‖
          ≤ unitDirichletPoincareConst d *
              (L * dilationL2Factor d L * w.toH1Function.gradientCoordL2NormSum) := hunit
      _ = dilationL2Factor d L *
            (unitDirichletPoincareConst d * L * w.toH1Function.gradientCoordL2NormSum) := by ring
  exact (mul_le_mul_iff_right₀ hFpos).1 hcancel

/-- The coordinate-sum gradient norm as a sum of `eLpNorm` `toReal`s. -/
theorem gradientCoordL2NormSum_eq_sum_eLpNorm {U : Set (Homogenization.Vec d)}
    (h : H1Function U) :
    h.gradientCoordL2NormSum =
      ∑ i : Fin d, (eLpNorm (fun x => h.grad x i) 2 (volumeMeasureOn U)).toReal := by
  unfold H1Function.gradientCoordL2NormSum
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [norm_gradCoordToScalarL2_eq]

/-- **Scaled Dirichlet Poincaré on axis cubes (`eLpNorm` form).** -/
theorem scaled_dirichlet_poincare {d : ℕ} [NeZero d] (z : Homogenization.Vec d) {L : ℝ}
    (hL : 0 < L) (w : H10Function (axisCube z L)) :
    (eLpNorm w.toH1Function.toFun 2 (volumeMeasureOn (axisCube z L))).toReal
      ≤ unitDirichletPoincareConst d * L *
          ∑ i : Fin d,
            (eLpNorm (fun x => w.toH1Function.grad x i) 2
              (volumeMeasureOn (axisCube z L))).toReal := by
  have h := scaled_dirichlet_poincare_norm z hL w
  rwa [norm_toScalarL2_eq,
    gradientCoordL2NormSum_eq_sum_eLpNorm] at h

end

end Homogenization
