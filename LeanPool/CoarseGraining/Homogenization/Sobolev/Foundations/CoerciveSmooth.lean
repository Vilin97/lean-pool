/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1
public import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.LinearAlgebra.Pi

/-! # Coercive Smooth -/

@[expose] public section

namespace Homogenization

/-!
# Smooth coercive core

This file records the derivative-side smooth compact-support estimate that
compares the full `L²` norm of the Fréchet derivative with the coordinate
gradient sum already packaged in `gradientCoordL2NormSum`.
-/

open scoped ENNReal

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

private theorem norm_fderiv_le_sum_basisVec_apply
    (L : Vec d →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i : Fin d, ‖L (basisVec i)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) ?_
  intro x
  have hx :
      L x = ∑ i : Fin d, x i * L (basisVec i) := by
    calc
      L x = ∑ i : Fin d, x i • L (fun j => if i = j then 1 else 0) := by
        simpa using (LinearMap.pi_apply_eq_sum_univ (f := L.toLinearMap) x)
      _ = ∑ i : Fin d, x i • L (basisVec i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hfun : (fun j => if i = j then 1 else 0) = basisVec i := by
            funext j
            simp [basisVec_apply, eq_comm]
          rw [hfun]
      _ = ∑ i : Fin d, x i * L (basisVec i) := by
          simp [smul_eq_mul]
  calc
    ‖L x‖ = ‖∑ i : Fin d, x i * L (basisVec i)‖ := by rw [hx]
    _ ≤ ∑ i : Fin d, ‖x i * L (basisVec i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin d, ‖x i‖ * ‖L (basisVec i)‖ := by
          simp [norm_mul]
    _ ≤ ∑ i : Fin d, ‖x‖ * ‖L (basisVec i)‖ := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (norm_nonneg _)
    _ = (∑ i : Fin d, ‖L (basisVec i)‖) * ‖x‖ := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (Finset.mul_sum (s := Finset.univ) (f := fun i : Fin d => ‖L (basisVec i)‖) ‖x‖).symm

private theorem support_fderiv_apply_basisVec_subset_of_tsupport_subset
    {f : Vec d → ℝ} (i : Fin d) (hsub : tsupport f ⊆ U) :
    Function.support (fun x => (fderiv ℝ f x) (basisVec i)) ⊆ U := by
  intro x hx
  exact hsub <|
    (support_fderiv_subset (𝕜 := ℝ) (f := f)) <| by
      change fderiv ℝ f x ≠ 0
      intro hzero
      apply hx
      simp [hzero]

private theorem support_sum_basisVec_apply_subset_tsupport
    {f : Vec d → ℝ} :
    Function.support (fun x => ∑ i : Fin d, ‖(fderiv ℝ f x) (basisVec i)‖) ⊆ tsupport f := by
  intro x hx
  by_contra hxt
  have hzero :
      ∀ i : Fin d, (fderiv ℝ f x) (basisVec i) = 0 := by
    intro i
    have hi : x ∉ Function.support (fderiv ℝ f) := by
      exact fun hx' => hxt ((support_fderiv_subset (𝕜 := ℝ) (f := f)) hx')
    have hfx : fderiv ℝ f x = 0 := by
      simpa [Function.notMem_support] using hi
    simp [hfx]
  apply hx
  simp [hzero]

private theorem eLpNorm_basisVec_apply_eq_gradCoordToScalarL2_norm
    (hU : IsOpen U) {f : Vec d → ℝ} (hf1 : ContDiff ℝ 1 f)
    (hf_supp : HasCompactSupport f) (hf_sub : tsupport f ⊆ U) (i : Fin d) :
    ENNReal.toReal
        (MeasureTheory.eLpNorm (fun x => ‖(fderiv ℝ f x) (basisVec i)‖) 2 MeasureTheory.volume) =
      ‖(H1Function.ofContDiff hU hf1 hf_supp).gradCoordToScalarL2 i‖ := by
  let u : H1Function U := H1Function.ofContDiff hU hf1 hf_supp
  let dg : Vec d → ℝ := fun x => (fderiv ℝ f x) (basisVec i)
  have hsupport : Function.support dg ⊆ U :=
    support_fderiv_apply_basisVec_subset_of_tsupport_subset (U := U) i hf_sub
  calc
    ENNReal.toReal (MeasureTheory.eLpNorm (fun x => ‖(fderiv ℝ f x) (basisVec i)‖)
        2 MeasureTheory.volume)
      = ENNReal.toReal (MeasureTheory.eLpNorm dg 2 MeasureTheory.volume) := by
          rw [MeasureTheory.eLpNorm_norm _
            ((hf1.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable]
    _ = ENNReal.toReal (MeasureTheory.eLpNorm dg 2 (volumeMeasureOn U)) := by
          rw [← MeasureTheory.eLpNorm_restrict_eq_of_support_subset
            ((hf1.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable hsupport]
    _ = ENNReal.toReal (MeasureTheory.eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn U)) := by
          simp [u, dg, H1Function.ofContDiff]
    _ = ‖u.gradCoordToScalarL2 i‖ := by
          rw [H1Function.gradCoordToScalarL2, Homogenization.toScalarL2,
            MeasureTheory.Lp.norm_toLp]

/-- Smooth compactly supported functions supported in `U` have full Fréchet
derivative `L²` norm controlled by the coordinate-gradient sum in the project's
`H¹` API. -/
theorem fderivL2Norm_le_gradientCoordL2NormSum_ofContDiff
    (hU : IsOpen U) {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : HasCompactSupport f) (hf_sub : tsupport f ⊆ U) :
    let u : H1Function U := H1Function.ofContDiff hU (hf.of_le (by simp)) hf_supp
    ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) 2 MeasureTheory.volume) ≤
      u.gradientCoordL2NormSum := by
  let hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  let u : H1Function U := H1Function.ofContDiff hU hf1 hf_supp
  let dg : Fin d → Vec d → ℝ := fun i x => (fderiv ℝ f x) (basisVec i)
  let D : Vec d → ℝ := fun x => ∑ i : Fin d, ‖dg i x‖
  let dLp : MeasureTheory.Lp (Vec d →L[ℝ] ℝ) 2 MeasureTheory.volume :=
    ((hf1.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hf_supp.fderiv (𝕜 := ℝ))).toLp
      (fderiv ℝ f)
  have hd_cont : Continuous D := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((hf1.continuous_fderiv (by simp)).clm_apply continuous_const).norm
  have hd_mem : MeasureTheory.MemLp D 2 MeasureTheory.volume :=
    hd_cont.memLp_of_hasCompactSupport <|
      HasCompactSupport.of_support_subset_isCompact
        hf_supp.isCompact (support_sum_basisVec_apply_subset_tsupport (f := f))
  let dCoordLp : MeasureTheory.Lp ℝ 2 MeasureTheory.volume := hd_mem.toLp D
  have hderiv_le_sum :
      ‖dLp‖ ≤ ‖dCoordLp‖ := by
    refine MeasureTheory.Lp.norm_le_norm_of_ae_le ?_
    filter_upwards
      [MeasureTheory.MemLp.coeFn_toLp
        ((hf1.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hf_supp.fderiv (𝕜 := ℝ))),
        MeasureTheory.MemLp.coeFn_toLp hd_mem]
      with x hxD hxCoord
    rw [hxD, hxCoord]
    have hnonneg : 0 ≤ D x := Finset.sum_nonneg fun i _ => norm_nonneg _
    calc
      ‖fderiv ℝ f x‖ ≤ D x := norm_fderiv_le_sum_basisVec_apply (fderiv ℝ f x)
      _ = ‖D x‖ := by simp [abs_of_nonneg hnonneg]
  have hsum_le :
      ‖dCoordLp‖ ≤ ∑ i : Fin d, ‖u.gradCoordToScalarL2 i‖ := by
    let di : Fin d → Vec d → ℝ := fun i x => ‖dg i x‖
    have hdi_mem :
        ∀ i : Fin d, MeasureTheory.MemLp (di i) 2 MeasureTheory.volume := by
      intro i
      have hcont : Continuous (di i) := by
        exact ((hf1.continuous_fderiv (by simp)).clm_apply continuous_const).norm
      exact hcont.memLp_of_hasCompactSupport
        ((hf_supp.fderiv_apply (𝕜 := ℝ) (basisVec i)).norm)
    have hsum_eLp :
        MeasureTheory.eLpNorm D 2 MeasureTheory.volume ≤
          ∑ i : Fin d, MeasureTheory.eLpNorm (di i) 2 MeasureTheory.volume := by
      have hD : D = ∑ i : Fin d, di i := by
        funext x
        simp [D, di]
      rw [hD]
      simpa using
        (MeasureTheory.eLpNorm_sum_le
          (μ := MeasureTheory.volume)
          (s := Finset.univ)
          (f := di)

          (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    calc
      ‖dCoordLp‖ = ENNReal.toReal (MeasureTheory.eLpNorm D 2 MeasureTheory.volume) := by
            simp [dCoordLp]
      _ ≤ ENNReal.toReal (∑ i : Fin d, MeasureTheory.eLpNorm (di i) 2 MeasureTheory.volume) := by
            refine ENNReal.toReal_mono ?_ hsum_eLp
            exact ENNReal.sum_ne_top.2 fun i _ => (hdi_mem i).eLpNorm_lt_top.ne
      _ = ∑ i : Fin d, ‖u.gradCoordToScalarL2 i‖ := by
            rw [ENNReal.toReal_sum (fun i hi => (hdi_mem i).eLpNorm_lt_top.ne)]
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa [di, hf1] using
              eLpNorm_basisVec_apply_eq_gradCoordToScalarL2_norm
                (U := U) hU hf1 hf_supp hf_sub i
  have hfderiv_eq :
      ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) 2 MeasureTheory.volume) = ‖dLp‖ := by
    simp [dLp]
  calc
    ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) 2 MeasureTheory.volume)
        = ‖dLp‖ := hfderiv_eq
    _ ≤ ‖dCoordLp‖ := hderiv_le_sum
    _ ≤ u.gradientCoordL2NormSum := hsum_le

/-- In dimensions `d ≥ 3`, smooth compactly supported functions supported in a
bounded domain satisfy the coercive `L²` estimate with the coordinate-gradient
sum on the right. -/
theorem valueL2Norm_le_sobolevConst_mul_gradientCoordL2NormSum_ofContDiff
    (hU : IsOpen U) (hBounded : IsBoundedDomain U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : HasCompactSupport f) (hf_sub : tsupport f ⊆ U) (hd : 2 < d) :
    let u : H1Function U := H1Function.ofContDiff hU (hf.of_le (by simp)) hf_supp
    ‖u.toScalarL2‖ ≤
      (MeasureTheory.eLpNormLESNormFDerivOfLeConst
        (F := ℝ) (μ := MeasureTheory.volume) (s := U) (p := 2) (q := 2) : ℝ) *
        u.gradientCoordL2NormSum := by
  let hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  let u : H1Function U := H1Function.ofContDiff hU hf1 hf_supp
  let C := MeasureTheory.eLpNormLESNormFDerivOfLeConst
    (F := ℝ) (μ := MeasureTheory.volume) (s := U) (p := 2) (q := 2)
  have hsupp : Function.support f ⊆ U := by
    intro x hx
    exact hf_sub (subset_tsupport _ hx)
  have hfderiv_mem : MeasureTheory.MemLp (fderiv ℝ f) 2 MeasureTheory.volume :=
    (hf1.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hf_supp.fderiv (𝕜 := ℝ))
  have hsob :
      MeasureTheory.eLpNorm f 2 MeasureTheory.volume ≤
        (C : ℝ≥0∞) * MeasureTheory.eLpNorm (fderiv ℝ f) 2 MeasureTheory.volume := by
    simpa [C] using
      (MeasureTheory.eLpNorm_le_eLpNorm_fderiv
        (μ := MeasureTheory.volume)
        (F := ℝ)
        (u := f)
        (s := U)
        hf1 hsupp (by norm_num : (1 : NNReal) ≤ 2)
        (by
          have hd' : (2 : NNReal) < d := by
            exact_mod_cast hd
          simpa [Homogenization.Vec, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hd')
        hBounded.isBounded)
  have hvalue :
      ‖u.toScalarL2‖ = ENNReal.toReal (MeasureTheory.eLpNorm f 2 MeasureTheory.volume) := by
    calc
      ‖u.toScalarL2‖ = ENNReal.toReal (MeasureTheory.eLpNorm u 2 (volumeMeasureOn U)) := by
        rw [H1Function.toScalarL2, Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp]
      _ = ENNReal.toReal (MeasureTheory.eLpNorm f 2 (volumeMeasureOn U)) := by
        simp [u, H1Function.ofContDiff]
      _ = ENNReal.toReal (MeasureTheory.eLpNorm f 2 MeasureTheory.volume) := by
        rw [MeasureTheory.eLpNorm_restrict_eq_of_support_subset hf.continuous.aestronglyMeasurable hsupp]
  calc
    ‖u.toScalarL2‖ = ENNReal.toReal (MeasureTheory.eLpNorm f 2 MeasureTheory.volume) := hvalue
    _ ≤ ENNReal.toReal ((C : ℝ≥0∞) * MeasureTheory.eLpNorm (fderiv ℝ f) 2 MeasureTheory.volume) := by
          exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfderiv_mem.eLpNorm_lt_top.ne) hsob
    _ = (C : ℝ) * ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) 2 MeasureTheory.volume) := by
          rw [ENNReal.toReal_mul]
          simp
    _ ≤ (C : ℝ) * u.gradientCoordL2NormSum := by
          exact mul_le_mul_of_nonneg_left
            (fderivL2Norm_le_gradientCoordL2NormSum_ofContDiff
              (U := U) hU hf hf_supp hf_sub)
            (show 0 ≤ (C : ℝ) by exact_mod_cast C.2)

end H1Function

end Homogenization
