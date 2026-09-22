/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH10

/-! # Coercive Mean Zero -/

namespace Homogenization

/-!
# Mean-zero coercive helpers

This file starts the quantitative helper layer for the future mean-zero `H¹`
coercive estimate on bounded open convex domains.

The current pass records the first bound we will need later: an `L²` control of
the affine correction coming from `averageGradient`.
-/

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

/-- Finite-measure `L²` control constant for the componentwise average
gradient. -/
noncomputable def averageGradientL2ControlConst : ℝ :=
  (MeasureTheory.volume U).toReal⁻¹ *
    ((MeasureTheory.volume U) ^ ((1 : ℝ) - 1 / 2)).toReal

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
/-- Nonnegativity of `averageGradientL2ControlConst`. -/
theorem averageGradientL2ControlConst_nonneg :
    0 ≤ H1Function.averageGradientL2ControlConst (U := U) := by
  unfold H1Function.averageGradientL2ControlConst
  positivity

/-- Domain-side `L²` control constant for affine functions on a Sobolev-regular
domain. -/
noncomputable def affineValueL2ControlConst (hU : IsSobolevRegularDomain U) : ℝ := by
  classical
  let R : ℝ := Classical.choose hU.isBoundedDomain
  exact ((MeasureTheory.volume U) ^ ((1 : ℝ) / 2)).toReal * (d : ℝ) * R

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
theorem affineValueL2ControlConst_nonneg (hU : IsSobolevRegularDomain U) :
    0 ≤ H1Function.affineValueL2ControlConst hU := by
  unfold H1Function.affineValueL2ControlConst
  have hR_nonneg : 0 ≤ Classical.choose hU.isBoundedDomain :=
    le_of_lt (Classical.choose_spec hU.isBoundedDomain).1
  have hleft : 0 ≤ ((MeasureTheory.volume U ^ ((1 : ℝ) / 2)).toReal * (d : ℝ)) := by
    positivity
  exact mul_nonneg hleft hR_nonneg

/-- The affine function with gradient `p` has `L²` norm controlled by a
domain-dependent constant times `‖p‖`. -/
theorem norm_toScalarL2_affineOnIsSobolevRegularDomain_le
    (hU : IsSobolevRegularDomain U) (p : Vec d) :
    ‖(H1Function.affineOnIsSobolevRegularDomain hU p).toScalarL2‖ ≤
      H1Function.affineValueL2ControlConst hU * ‖p‖ := by
  classical
  let R : ℝ := Classical.choose hU.isBoundedDomain
  have hR : ∀ x ∈ U, ∀ i, |x i| ≤ R := (Classical.choose_spec hU.isBoundedDomain).2
  have hR_nonneg : 0 ≤ R := le_of_lt (Classical.choose_spec hU.isBoundedDomain).1
  let C : ℝ := (d : ℝ) * R * ‖p‖
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbound :
      ∀ᵐ x ∂volumeMeasureOn U,
        ‖(H1Function.affineOnIsSobolevRegularDomain hU p) x‖ ≤ C := by
    rw [MeasureTheory.ae_restrict_iff' hU.measurableSet]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    calc
      ‖(H1Function.affineOnIsSobolevRegularDomain hU p) x‖
          = ‖∑ i : Fin d, p i * x i‖ := by
              simp [H1Function.affineOnIsSobolevRegularDomain_apply]
      _ ≤ ∑ i : Fin d, ‖p i * x i‖ := norm_sum_le _ _
      _ = ∑ i : Fin d, ‖p i‖ * ‖x i‖ := by
            simp [norm_mul]
      _ ≤ ∑ i : Fin d, ‖p‖ * R := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hxi : ‖x i‖ ≤ R := by
              simpa [Real.norm_eq_abs] using hR x hx i
            calc
              ‖p i‖ * ‖x i‖ ≤ ‖p i‖ * R := by
                exact mul_le_mul_of_nonneg_left hxi (norm_nonneg _)
              _ ≤ ‖p‖ * R := by
                exact mul_le_mul_of_nonneg_right (norm_le_pi_norm p i) hR_nonneg
      _ = (d : ℝ) * R * ‖p‖ := by
            simp [mul_left_comm, mul_comm]
  have hnorm :
      MeasureTheory.eLpNorm
          (fun x => (H1Function.affineOnIsSobolevRegularDomain hU p) x)
          (2 : ENNReal) (volumeMeasureOn U) ≤
        (volumeMeasureOn U) Set.univ ^ ((2 : ENNReal).toReal⁻¹) * ENNReal.ofReal C :=
    MeasureTheory.eLpNorm_le_of_ae_bound (μ := volumeMeasureOn U) (p := (2 : ENNReal))
      (H1Function.affineOnIsSobolevRegularDomain hU p).memL2.aestronglyMeasurable hbound
  have hpow_ne_top :
      (volumeMeasureOn U) Set.univ ^ ((2 : ENNReal).toReal⁻¹) ≠ ⊤ := by
    refine (ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_).ne
    simpa [volumeMeasureOn] using (MeasureTheory.measure_lt_top (volumeMeasureOn U) Set.univ).ne
  have hmul_ne_top :
      (volumeMeasureOn U) Set.univ ^ ((2 : ENNReal).toReal⁻¹) * ENNReal.ofReal C ≠ ⊤ :=
    ENNReal.mul_ne_top hpow_ne_top ENNReal.ofReal_ne_top
  calc
    ‖(H1Function.affineOnIsSobolevRegularDomain hU p).toScalarL2‖
        = ENNReal.toReal
            (MeasureTheory.eLpNorm
              (fun x => (H1Function.affineOnIsSobolevRegularDomain hU p) x)
              (2 : ENNReal) (volumeMeasureOn U)) := by
              rw [H1Function.toScalarL2, Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp]
    _ ≤ ENNReal.toReal
          ((volumeMeasureOn U) Set.univ ^ ((2 : ENNReal).toReal⁻¹) * ENNReal.ofReal C) := by
            exact ENNReal.toReal_mono hmul_ne_top hnorm
    _ = ((MeasureTheory.volume U) ^ ((1 : ℝ) / 2)).toReal * C := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_nonneg]
          simp [volumeMeasureOn]
    _ = H1Function.affineValueL2ControlConst hU * ‖p‖ := by
          unfold H1Function.affineValueL2ControlConst
          simp [R, C, mul_assoc, mul_left_comm, mul_comm]

/-- Specialization of the affine `L²` bound to the affine correction with
gradient `u.averageGradient`. -/
theorem norm_toScalarL2_averageGradientAffineOnIsSobolevRegularDomain_le
    (hU : IsSobolevRegularDomain U) (u : H1Function U) :
    ‖(u.averageGradientAffineOnIsSobolevRegularDomain hU).toScalarL2‖ ≤
      H1Function.affineValueL2ControlConst hU * ‖u.averageGradient‖ := by
  simpa [H1Function.averageGradientAffineOnIsSobolevRegularDomain] using
    H1Function.norm_toScalarL2_affineOnIsSobolevRegularDomain_le
      (hU := hU) (p := u.averageGradient)

/-- On a finite-measure domain, the componentwise average gradient is
controlled by the vector `L²` norm of the weak gradient. -/
theorem norm_averageGradient_le_averageGradientL2ControlConst_mul
    (u : H1Function U) :
    ‖u.averageGradient‖ ≤
      H1Function.averageGradientL2ControlConst (U := U) * ‖u.gradToVectorL2‖ := by
  let μ := volumeMeasureOn U
  have hnonneg :
      0 ≤ H1Function.averageGradientL2ControlConst (U := U) * ‖u.gradToVectorL2‖ := by
    exact mul_nonneg (H1Function.averageGradientL2ControlConst_nonneg (U := U)) (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hnonneg).2 ?_
  intro i
  have hgrad_int : MeasureTheory.Integrable (fun x => u.grad x i) μ := by
    simpa [μ] using (u.grad_memL2 i).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hgrad_norm :
      ∫ x, |u.grad x i| ∂μ =
        ENNReal.toReal (MeasureTheory.eLpNorm (fun x => u.grad x i) 1 μ) := by
    calc
      ∫ x, |u.grad x i| ∂μ = ∫ x, ‖u.grad x i‖ ∂μ := by
        simp
      _ = (∫⁻ x, ‖u.grad x i‖ₑ ∂μ).toReal := by
        exact MeasureTheory.integral_norm_eq_lintegral_enorm hgrad_int.aestronglyMeasurable
      _ = ENNReal.toReal (MeasureTheory.eLpNorm (fun x => u.grad x i) 1 μ) := by
        rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm hgrad_int.aestronglyMeasurable]
  have hL1_bound :
      MeasureTheory.eLpNorm (fun x => u.grad x i) 1 μ ≤
        MeasureTheory.eLpNorm (fun x => u.grad x i) 2 μ *
          μ Set.univ ^ ((1 : ℝ) - 1 / 2) := by
    simpa using
      (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := μ)
        (f := fun x => u.grad x i)
        (p := (1 : ENNReal))
        (q := (2 : ENNReal))
        (by norm_num)
        (u.grad_memL2 i).aestronglyMeasurable)
  have hConst_ne_top : μ Set.univ ^ ((1 : ℝ) - 1 / 2) ≠ ⊤ := by
    refine (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_).ne
    simpa [μ] using (MeasureTheory.measure_lt_top μ Set.univ).ne
  have hMul_ne_top :
      MeasureTheory.eLpNorm (fun x => u.grad x i) 2 μ * μ Set.univ ^ ((1 : ℝ) - 1 / 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (u.grad_memL2 i).eLpNorm_lt_top.ne hConst_ne_top
  have hL1_toReal :
      ENNReal.toReal (MeasureTheory.eLpNorm (fun x => u.grad x i) 1 μ) ≤
        ENNReal.toReal
          (MeasureTheory.eLpNorm (fun x => u.grad x i) 2 μ *
            μ Set.univ ^ ((1 : ℝ) - 1 / 2)) :=
    ENNReal.toReal_mono hMul_ne_top hL1_bound
  have hcoord_int_bound :
      |∫ x in U, u.grad x i ∂MeasureTheory.volume| ≤
        ((MeasureTheory.volume U) ^ ((1 : ℝ) - 1 / 2)).toReal * ‖u.gradToVectorL2‖ := by
    have habs :
        |∫ x, u.grad x i ∂μ| ≤ ∫ x, |u.grad x i| ∂μ := by
      simpa using MeasureTheory.abs_integral_le_integral_abs (f := fun x => u.grad x i) (μ := μ)
    calc
      |∫ x in U, u.grad x i ∂MeasureTheory.volume|
          = |∫ x, u.grad x i ∂μ| := by
              simp [μ]
      _ ≤ ∫ x, |u.grad x i| ∂μ := habs
      _ = ENNReal.toReal (MeasureTheory.eLpNorm (fun x => u.grad x i) 1 μ) := hgrad_norm
      _ ≤ ENNReal.toReal
            (MeasureTheory.eLpNorm (fun x => u.grad x i) 2 μ *
              μ Set.univ ^ ((1 : ℝ) - 1 / 2)) := hL1_toReal
      _ = ENNReal.toReal (MeasureTheory.eLpNorm (fun x => u.grad x i) 2 μ) *
            (μ Set.univ ^ ((1 : ℝ) - 1 / 2)).toReal := by
            rw [ENNReal.toReal_mul]
      _ = ‖u.gradCoordToScalarL2 i‖ * ((MeasureTheory.volume U) ^ ((1 : ℝ) - 1 / 2)).toReal := by
            rw [H1Function.gradCoordToScalarL2, Homogenization.toScalarL2,
              MeasureTheory.Lp.norm_toLp]
            simp [μ]
      _ = ((MeasureTheory.volume U) ^ ((1 : ℝ) - 1 / 2)).toReal * ‖u.gradCoordToScalarL2 i‖ := by
            ring
      _ ≤ ((MeasureTheory.volume U) ^ ((1 : ℝ) - 1 / 2)).toReal * ‖u.gradToVectorL2‖ := by
            refine mul_le_mul_of_nonneg_left (u.norm_gradCoordToScalarL2_le i) ?_
            positivity
  have hvolinv_nonneg : 0 ≤ (MeasureTheory.volume U).toReal⁻¹ := by
    positivity
  have hcoord :
      |u.averageGradient i| ≤
        H1Function.averageGradientL2ControlConst (U := U) * ‖u.gradToVectorL2‖ := by
    calc
      |u.averageGradient i|
          = |(MeasureTheory.volume U).toReal⁻¹ *
              ∫ x in U, u.grad x i ∂MeasureTheory.volume| := by
                unfold H1Function.averageGradient integralAverage
                rfl
      _ = (MeasureTheory.volume U).toReal⁻¹ *
            |∫ x in U, u.grad x i ∂MeasureTheory.volume| := by
              rw [abs_mul, abs_of_nonneg hvolinv_nonneg]
      _ ≤ (MeasureTheory.volume U).toReal⁻¹ *
            (((MeasureTheory.volume U) ^ ((1 : ℝ) - 1 / 2)).toReal * ‖u.gradToVectorL2‖) := by
              exact mul_le_mul_of_nonneg_left hcoord_int_bound hvolinv_nonneg
      _ = H1Function.averageGradientL2ControlConst (U := U) * ‖u.gradToVectorL2‖ := by
            unfold H1Function.averageGradientL2ControlConst
            ring
  simpa [Real.norm_eq_abs] using hcoord

private theorem norm_toVectorL2_const (p : Vec d) :
    ‖Homogenization.toVectorL2
        (U := U)
        (show MemVectorL2 U (fun _ : Vec d => p) from
          MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) p)‖ =
      ((MeasureTheory.volume U) ^ ((1 : ℝ) / 2)).toReal * ‖p‖ := by
  rw [Homogenization.toVectorL2, MeasureTheory.Lp.norm_toLp]
  rw [MeasureTheory.eLpNorm_const']
  · simp [volumeMeasureOn, mul_comm]
  · norm_num
  · norm_num

private theorem averageGradientAffineOnIsSobolevRegularDomain_gradToVectorL2_eq
    (hU : IsSobolevRegularDomain U) (u : H1Function U) :
    (u.averageGradientAffineOnIsSobolevRegularDomain hU).gradToVectorL2 =
      Homogenization.toVectorL2
        (U := U)
        (show MemVectorL2 U (fun _ : Vec d => u.averageGradient) from
          MeasureTheory.memLp_const
            (μ := volumeMeasureOn U) (p := (2 : ENNReal)) u.averageGradient) := by
  let hconst_mem : MemVectorL2 U (fun _ : Vec d => u.averageGradient) :=
    MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) u.averageGradient
  apply
    (Homogenization.toVectorL2_eq_toVectorL2_iff
      ((u.averageGradientAffineOnIsSobolevRegularDomain hU).grad_memVectorL2) hconst_mem).2
  filter_upwards
      [H1Function.coeFn_gradToVectorL2 (u.averageGradientAffineOnIsSobolevRegularDomain hU),
        Homogenization.coeFn_toVectorL2 (U := U) (f := fun _ : Vec d => u.averageGradient) hconst_mem]
    with x hgrad hconst
  simp [H1Function.averageGradientAffineOnIsSobolevRegularDomain]

/-- The affine correction with gradient `u.averageGradient` has gradient `L²`
norm equal to the finite-measure `L²` norm of the constant vector field
`u.averageGradient`. -/
theorem norm_gradToVectorL2_averageGradientAffineOnIsSobolevRegularDomain
    (hU : IsSobolevRegularDomain U) (u : H1Function U) :
    ‖(u.averageGradientAffineOnIsSobolevRegularDomain hU).gradToVectorL2‖ =
      ((MeasureTheory.volume U) ^ ((1 : ℝ) / 2)).toReal * ‖u.averageGradient‖ := by
  rw [averageGradientAffineOnIsSobolevRegularDomain_gradToVectorL2_eq]
  exact norm_toVectorL2_const (U := U) u.averageGradient

/-- On a finite-measure Sobolev-regular domain, the gradient `L²` norm of the
affine correction is controlled by the gradient `L²` norm of `u`. -/
theorem norm_gradToVectorL2_averageGradientAffineOnIsSobolevRegularDomain_le
    (hU : IsSobolevRegularDomain U) (u : H1Function U) :
    ‖(u.averageGradientAffineOnIsSobolevRegularDomain hU).gradToVectorL2‖ ≤
      (((MeasureTheory.volume U) ^ ((1 : ℝ) / 2)).toReal *
        H1Function.averageGradientL2ControlConst (U := U)) * ‖u.gradToVectorL2‖ := by
  calc
    ‖(u.averageGradientAffineOnIsSobolevRegularDomain hU).gradToVectorL2‖
        = ((MeasureTheory.volume U) ^ ((1 : ℝ) / 2)).toReal * ‖u.averageGradient‖ := by
            exact H1Function.norm_gradToVectorL2_averageGradientAffineOnIsSobolevRegularDomain
              (hU := hU) (u := u)
    _ ≤ ((MeasureTheory.volume U) ^ ((1 : ℝ) / 2)).toReal *
          (H1Function.averageGradientL2ControlConst (U := U) * ‖u.gradToVectorL2‖) := by
            refine mul_le_mul_of_nonneg_left
              (H1Function.norm_averageGradient_le_averageGradientL2ControlConst_mul (U := U) u) ?_
            positivity
    _ = (((MeasureTheory.volume U) ^ ((1 : ℝ) / 2)).toReal *
          H1Function.averageGradientL2ControlConst (U := U)) * ‖u.gradToVectorL2‖ := by
            ring

/-- The gradient `L²` norm of the affine-corrected `H¹` function is controlled
by the gradient `L²` norm of `u`. -/
theorem norm_gradToVectorL2_sub_averageGradientAffineOnIsSobolevRegularDomain_le
    (hU : IsSobolevRegularDomain U) (u : H1Function U) :
    ‖(u - u.averageGradientAffineOnIsSobolevRegularDomain hU).gradToVectorL2‖ ≤
      (1 + ((MeasureTheory.volume U) ^ ((1 : ℝ) / 2)).toReal *
          H1Function.averageGradientL2ControlConst (U := U)) * ‖u.gradToVectorL2‖ := by
  let a := u.averageGradientAffineOnIsSobolevRegularDomain hU
  have hsub :
      (u - a).gradToVectorL2 = u.gradToVectorL2 - a.gradToVectorL2 := by
    calc
      (u - a).gradToVectorL2 = (u + (-1 : ℝ) • a).gradToVectorL2 := by rfl
      _ = u.gradToVectorL2 + (-1 : ℝ) • a.gradToVectorL2 := by
            rw [H1Function.gradToVectorL2_add, H1Function.gradToVectorL2_smul]
      _ = u.gradToVectorL2 - a.gradToVectorL2 := by
            simp [sub_eq_add_neg]
  have ha :
      ‖a.gradToVectorL2‖ ≤
        (((MeasureTheory.volume U) ^ ((1 : ℝ) / 2)).toReal *
          H1Function.averageGradientL2ControlConst (U := U)) * ‖u.gradToVectorL2‖ := by
    simpa [a] using
      H1Function.norm_gradToVectorL2_averageGradientAffineOnIsSobolevRegularDomain_le
        (hU := hU) (u := u)
  calc
    ‖(u - a).gradToVectorL2‖ = ‖u.gradToVectorL2 - a.gradToVectorL2‖ := by
      rw [hsub]
    _ ≤ ‖u.gradToVectorL2‖ + ‖a.gradToVectorL2‖ := norm_sub_le _ _
    _ ≤ ‖u.gradToVectorL2‖ +
          ((((MeasureTheory.volume U) ^ ((1 : ℝ) / 2)).toReal *
            H1Function.averageGradientL2ControlConst (U := U)) * ‖u.gradToVectorL2‖) := by
            simpa [add_comm] using add_le_add_right ha ‖u.gradToVectorL2‖
    _ = (1 + ((MeasureTheory.volume U) ^ ((1 : ℝ) / 2)).toReal *
          H1Function.averageGradientL2ControlConst (U := U)) * ‖u.gradToVectorL2‖ := by
            ring

/-- The `L²` norm of `u` is bounded by the `L²` norm of the affine-corrected
remainder plus the `L²` norm of the affine correction. -/
theorem norm_toScalarL2_le_norm_toScalarL2_sub_averageGradientAffineOnIsSobolevRegularDomain_add
    (hU : IsSobolevRegularDomain U) (u : H1Function U) :
    ‖u.toScalarL2‖ ≤
      ‖(u - u.averageGradientAffineOnIsSobolevRegularDomain hU).toScalarL2‖ +
        ‖(u.averageGradientAffineOnIsSobolevRegularDomain hU).toScalarL2‖ := by
  let a := u.averageGradientAffineOnIsSobolevRegularDomain hU
  have hsum : (u - a).toScalarL2 + a.toScalarL2 = u.toScalarL2 := by
    calc
      (u - a).toScalarL2 + a.toScalarL2
          = (u.toScalarL2 + (-1 : ℝ) • a.toScalarL2) + a.toScalarL2 := by
              rw [show u - a = u + (-1 : ℝ) • a by rfl, H1Function.toScalarL2_add,
                H1Function.toScalarL2_smul]
      _ = u.toScalarL2 + (((-1 : ℝ) • a.toScalarL2) + a.toScalarL2) := by
            abel_nf
      _ = u.toScalarL2 := by
            simp
  calc
    ‖u.toScalarL2‖ = ‖(u - a).toScalarL2 + a.toScalarL2‖ := by
      rw [← hsum]
    _ ≤ ‖(u - a).toScalarL2‖ + ‖a.toScalarL2‖ := norm_add_le _ _

/-- The affine-correction part of `‖u.toScalarL2‖` is controlled by
`‖u.gradToVectorL2‖`, leaving only the `L²` norm of the affine-corrected
remainder as the future zero-trace coercive input. -/
theorem norm_toScalarL2_le_norm_toScalarL2_sub_averageGradientAffineOnIsSobolevRegularDomain_add_mul
    (hU : IsSobolevRegularDomain U) (u : H1Function U) :
    ‖u.toScalarL2‖ ≤
      ‖(u - u.averageGradientAffineOnIsSobolevRegularDomain hU).toScalarL2‖ +
        (H1Function.affineValueL2ControlConst hU *
          H1Function.averageGradientL2ControlConst (U := U)) * ‖u.gradToVectorL2‖ := by
  have haffine :=
    H1Function.norm_toScalarL2_averageGradientAffineOnIsSobolevRegularDomain_le
      (hU := hU) (u := u)
  have havg :=
    H1Function.norm_averageGradient_le_averageGradientL2ControlConst_mul (U := U) u
  calc
    ‖u.toScalarL2‖ ≤
        ‖(u - u.averageGradientAffineOnIsSobolevRegularDomain hU).toScalarL2‖ +
          ‖(u.averageGradientAffineOnIsSobolevRegularDomain hU).toScalarL2‖ := by
            exact
              H1Function.norm_toScalarL2_le_norm_toScalarL2_sub_averageGradientAffineOnIsSobolevRegularDomain_add
                (hU := hU) (u := u)
    _ ≤ ‖(u - u.averageGradientAffineOnIsSobolevRegularDomain hU).toScalarL2‖ +
          (H1Function.affineValueL2ControlConst hU * ‖u.averageGradient‖) := by
            have hsum :=
              add_le_add_right haffine
                ‖(u - u.averageGradientAffineOnIsSobolevRegularDomain hU).toScalarL2‖
            simpa [add_comm] using hsum
    _ ≤ ‖(u - u.averageGradientAffineOnIsSobolevRegularDomain hU).toScalarL2‖ +
          (H1Function.affineValueL2ControlConst hU *
            (H1Function.averageGradientL2ControlConst (U := U) * ‖u.gradToVectorL2‖)) := by
            have hmul :
                H1Function.affineValueL2ControlConst hU * ‖u.averageGradient‖ ≤
                  H1Function.affineValueL2ControlConst hU *
                    (H1Function.averageGradientL2ControlConst (U := U) * ‖u.gradToVectorL2‖) := by
              exact mul_le_mul_of_nonneg_left havg
                (H1Function.affineValueL2ControlConst_nonneg hU)
            have hsum :=
              add_le_add_right hmul
                ‖(u - u.averageGradientAffineOnIsSobolevRegularDomain hU).toScalarL2‖
            simpa [add_comm] using hsum
    _ = ‖(u - u.averageGradientAffineOnIsSobolevRegularDomain hU).toScalarL2‖ +
          ((H1Function.affineValueL2ControlConst hU *
            H1Function.averageGradientL2ControlConst (U := U)) * ‖u.gradToVectorL2‖) := by
            ring

end H1Function

end Homogenization
