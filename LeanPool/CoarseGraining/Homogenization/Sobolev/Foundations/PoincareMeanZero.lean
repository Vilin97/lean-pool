/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareLp
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing
public import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain

/-! # Poincare Mean Zero -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

/-- File-level typeclass cache for `Nontrivial (Vec d)` and
`NoncompactSpace (Vec d)` under `[NeZero d]`. See `PoincareZeroTrace.lean`. -/
private instance instNontrivialVecPMZ (d : ℕ) [NeZero d] :
    Nontrivial (Vec d) := inferInstance
private instance instNoncompactSpaceVecPMZ (d : ℕ) [NeZero d] :
    NoncompactSpace (Vec d) := inferInstance

/-!
# Mean-zero `L²` Poincare on bounded open convex domains

This file packages the bounded-open-convex Poincare development on the
mean-zero `H¹` layer.

The proof combines the smooth convex-domain Poincare theorem, convex smoothing
of rough `H¹` witnesses, and the closed-graph continuity lemmas for subtracting
averages. The public output is the bundled coercive estimate consumed by the
Hodge layer.
-/

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
            (Finset.mul_sum (s := Finset.univ)
              (f := fun i : Fin d => ‖L (basisVec i)‖) ‖x‖).symm

private theorem eLpNorm_basisVec_apply_eq_gradCoordToScalarL2_norm
    (hU : IsOpenBoundedConvexDomain U) {f : Vec d → ℝ}
    (hf1 : ContDiff ℝ 1 f) (i : Fin d) :
    ENNReal.toReal
        (MeasureTheory.eLpNorm (fun x => ‖(fderiv ℝ f x) (basisVec i)‖) 2
          (volumeMeasureOn U)) =
      ‖(H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU hf1).gradCoordToScalarL2 i‖ := by
  let u : H1Function U := H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU hf1
  let dg : Vec d → ℝ := fun x => (fderiv ℝ f x) (basisVec i)
  calc
    ENNReal.toReal
        (MeasureTheory.eLpNorm (fun x => ‖(fderiv ℝ f x) (basisVec i)‖) 2
          (volumeMeasureOn U))
      = ENNReal.toReal (MeasureTheory.eLpNorm dg 2 (volumeMeasureOn U)) := by
          rw [MeasureTheory.eLpNorm_norm _
            ((hf1.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable]
    _ = ENNReal.toReal (MeasureTheory.eLpNorm (fun x => u.grad x i) 2
          (volumeMeasureOn U)) := by
          simp [u, dg, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
            H1Function.ofContDiffOnIsSobolevRegularDomain]
    _ = ‖u.gradCoordToScalarL2 i‖ := by
          rw [H1Function.gradCoordToScalarL2, Homogenization.toScalarL2,
            MeasureTheory.Lp.norm_toLp]

private theorem memLp_fderiv_of_contDiffOnIsOpenBoundedConvexDomain
    (hU : IsOpenBoundedConvexDomain U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) :
    MeasureTheory.MemLp (fderiv ℝ f) 2 (volumeMeasureOn U) := by
  have hfderiv_cont : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hclosure_compact : IsCompact (closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  let CD : ℝ :=
    Classical.choose (hclosure_compact.exists_bound_of_continuousOn hfderiv_cont.continuousOn)
  have hCD : ∀ x ∈ closure U, ‖fderiv ℝ f x‖ ≤ CD :=
    Classical.choose_spec
      (hclosure_compact.exists_bound_of_continuousOn hfderiv_cont.continuousOn)
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  refine MeasureTheory.MemLp.of_bound
    (μ := volumeMeasureOn U) hfderiv_cont.aestronglyMeasurable CD ?_
  rw [MeasureTheory.ae_restrict_iff' hU.isOpen.measurableSet]
  exact Filter.Eventually.of_forall fun x hx => hCD x (subset_closure hx)

private theorem toReal_eLpNorm_two_sq_eq_integral_rpow_norm
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] {μ : MeasureTheory.Measure α} {f : α → E}
    (hf : MeasureTheory.MemLp f 2 μ) :
    (ENNReal.toReal (MeasureTheory.eLpNorm f 2 μ)) ^ 2 =
      ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := by
  have hpow : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
  have h :=
    hf.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ENNReal) ≠ 0)
      (by simp : (2 : ENNReal) ≠ ⊤)
  rw [h, hpow]
  have hint_nonneg : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := by
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
  rw [ENNReal.toReal_ofReal]
  · rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hint_nonneg
  · exact Real.rpow_nonneg hint_nonneg _

private theorem norm_toScalarL2_sq_eq_integral_rpow_norm
    (u : H1Function U) :
    ‖u.toScalarL2‖ ^ 2 = ∫ x in U, ‖u x‖ ^ (2 : ℝ) ∂MeasureTheory.volume := by
  rw [H1Function.toScalarL2, Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp]
  exact toReal_eLpNorm_two_sq_eq_integral_rpow_norm u.memL2

theorem fderivL2Norm_le_gradientCoordL2NormSum_ofContDiffOnIsOpenBoundedConvexDomain
    (hU : IsOpenBoundedConvexDomain U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    let u : H1Function U :=
      H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU (hf.of_le (by simp))
    ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) 2 (volumeMeasureOn U)) ≤
      u.gradientCoordL2NormSum := by
  let hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn U
  let : MeasureTheory.IsFiniteMeasure μ := by
    dsimp [μ, volumeMeasureOn]
    exact hU.isFiniteMeasure_restrict_volume
  let u : H1Function U := H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU hf1
  let dg : Fin d → Vec d → ℝ := fun i x => (fderiv ℝ f x) (basisVec i)
  let D : Vec d → ℝ := fun x => ∑ i : Fin d, ‖dg i x‖
  have hfderiv_cont : Continuous (fderiv ℝ f) := hf1.continuous_fderiv (by simp)
  have hclosure_compact : IsCompact (closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  let CD : ℝ :=
    Classical.choose (hclosure_compact.exists_bound_of_continuousOn hfderiv_cont.continuousOn)
  have hCD : ∀ x ∈ closure U, ‖fderiv ℝ f x‖ ≤ CD :=
    Classical.choose_spec
      (hclosure_compact.exists_bound_of_continuousOn hfderiv_cont.continuousOn)
  have hfderiv_mem :
      MeasureTheory.MemLp (fderiv ℝ f) 2 μ := by
    refine MeasureTheory.MemLp.of_bound (μ := μ) hfderiv_cont.aestronglyMeasurable CD ?_
    rw [MeasureTheory.ae_restrict_iff' hU.isOpen.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => hCD x (subset_closure hx)
  let dLp : MeasureTheory.Lp (Vec d →L[ℝ] ℝ) 2 μ :=
    hfderiv_mem.toLp (fderiv ℝ f)
  have hdi_mem :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => ‖dg i x‖) 2 μ := by
    intro i
    simpa [u, dg, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
      H1Function.ofContDiffOnIsSobolevRegularDomain] using (u.grad_memL2 i).norm
  have hD_mem : MeasureTheory.MemLp D 2 μ := by
    have hsum :=
      MeasureTheory.memLp_finsetSum (μ := μ) (p := (2 : ENNReal))
        (s := Finset.univ) (f := fun i : Fin d => fun x : Vec d => ‖dg i x‖)
        (fun i hi => hdi_mem i)
    simpa [D] using hsum
  let dCoordLp : MeasureTheory.Lp ℝ 2 μ := hD_mem.toLp D
  have hderiv_le_sum :
      ‖dLp‖ ≤ ‖dCoordLp‖ := by
    refine MeasureTheory.Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp hfderiv_mem,
      MeasureTheory.MemLp.coeFn_toLp hD_mem] with x hxD hxCoord
    rw [hxD, hxCoord]
    have hnonneg : 0 ≤ D x := Finset.sum_nonneg fun i _ => norm_nonneg _
    calc
      ‖fderiv ℝ f x‖ ≤ D x := norm_fderiv_le_sum_basisVec_apply (fderiv ℝ f x)
      _ = ‖D x‖ := by simp [abs_of_nonneg hnonneg]
  have hsum_le :
      ‖dCoordLp‖ ≤ ∑ i : Fin d, ‖u.gradCoordToScalarL2 i‖ := by
    let di : Fin d → Vec d → ℝ := fun i x => ‖dg i x‖
    have hsum_eLp :
        MeasureTheory.eLpNorm D 2 μ ≤
          ∑ i : Fin d, MeasureTheory.eLpNorm (di i) 2 μ := by
      have hD : D = ∑ i : Fin d, di i := by
        funext x
        simp [D, di]
      rw [hD]
      simpa using
        (MeasureTheory.eLpNorm_sum_le
          (μ := μ)
          (s := Finset.univ)
          (f := di)

          (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    calc
      ‖dCoordLp‖ = ENNReal.toReal (MeasureTheory.eLpNorm D 2 μ) := by
            simp [dCoordLp]
      _ ≤ ENNReal.toReal (∑ i : Fin d, MeasureTheory.eLpNorm (di i) 2 μ) := by
            refine ENNReal.toReal_mono ?_ hsum_eLp
            exact ENNReal.sum_ne_top.2 fun i _ => (hdi_mem i).eLpNorm_lt_top.ne
      _ = ∑ i : Fin d, ‖u.gradCoordToScalarL2 i‖ := by
            rw [ENNReal.toReal_sum (fun i hi => (hdi_mem i).eLpNorm_lt_top.ne)]
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa [di, hf1, μ] using
              eLpNorm_basisVec_apply_eq_gradCoordToScalarL2_norm
                (U := U) hU hf1 i
  have hfderiv_eq :
      ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) 2 μ) = ‖dLp‖ := by
    simp [dLp]
  change ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) 2 μ) ≤
    u.gradientCoordL2NormSum
  calc
    ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) 2 μ)
        = ‖dLp‖ := hfderiv_eq
    _ ≤ ‖dCoordLp‖ := hderiv_le_sum
    _ ≤ u.gradientCoordL2NormSum := hsum_le

private noncomputable def smoothPoincareSqConst
    (hU : IsOpenBoundedConvexDomain U) : ℝ :=
  (((MeasureTheory.volume U).toReal⁻¹ *
      (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ))) ^ (2 : ℝ)) *
    ((((d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
        (4 * Classical.choose hU.isBoundedDomain)) ^ (2 : ℝ)))

private theorem smoothPoincareSqConst_nonneg
    (hU : IsOpenBoundedConvexDomain U) :
    0 ≤ smoothPoincareSqConst (d := d) (U := U) hU := by
  have hR : 0 ≤ Classical.choose hU.isBoundedDomain :=
    le_of_lt (Classical.choose_spec hU.isBoundedDomain).1
  have hbase₁ :
      0 ≤ (MeasureTheory.volume U).toReal⁻¹ *
        (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ)) := by
    exact mul_nonneg
      (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (div_nonneg (pow_nonneg (mul_nonneg (by norm_num) hR) d) (Nat.cast_nonneg d))
  have hbase₂ :
      0 ≤ (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
        (4 * Classical.choose hU.isBoundedDomain) := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg d) ENNReal.toReal_nonneg)
      (mul_nonneg (by norm_num) hR)
  exact mul_nonneg
    (Real.rpow_nonneg hbase₁ _)
    (Real.rpow_nonneg hbase₂ _)

private noncomputable def smoothPoincareConst
    (hU : IsOpenBoundedConvexDomain U) : ℝ :=
  Real.sqrt (smoothPoincareSqConst (d := d) (U := U) hU)

private theorem smoothPoincareConst_nonneg
    (hU : IsOpenBoundedConvexDomain U) :
    0 ≤ smoothPoincareConst (d := d) (U := U) hU := by
  exact Real.sqrt_nonneg _

private theorem smoothPoincareSqConst_le_const_sq
    (hU : IsOpenBoundedConvexDomain U) :
    smoothPoincareSqConst (d := d) (U := U) hU ≤
      (smoothPoincareConst (d := d) (U := U) hU) ^ 2 := by
  rw [smoothPoincareConst, Real.sq_sqrt (smoothPoincareSqConst_nonneg (d := d) (U := U) hU)]

/-- Public formula bounding the chosen coercive constant in
`h1CoerciveEstimate_of_isOpenBoundedConvexDomain`.

The formula is intentionally the square root of the smooth squared Poincare
constant times the coordinate-to-vector comparison factor. It exposes the
geometric scale of the chosen proof without exposing the private smooth proof
names. -/
noncomputable def h1CoerciveEstimateChosenBound
    (hU : IsOpenBoundedConvexDomain U) : ℝ :=
  Real.sqrt
    ((((MeasureTheory.volume U).toReal⁻¹ *
      (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ))) ^ (2 : ℝ)) *
    ((((d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
        (4 * Classical.choose hU.isBoundedDomain)) ^ (2 : ℝ)))) *
      (d : ℝ)

theorem h1CoerciveEstimateChosenBound_nonneg
    (hU : IsOpenBoundedConvexDomain U) :
    0 ≤ h1CoerciveEstimateChosenBound (d := d) (U := U) hU := by
  exact mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg d)

private theorem norm_toScalarL2_subAverage_le_smoothPoincareConst_mul_gradientCoordL2NormSum_ofContDiff
    [NeZero d] [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    let u : H1Function U :=
      H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU (hf.of_le (by simp))
    ‖u.subAverage.toScalarL2‖ ≤
      smoothPoincareConst (d := d) (U := U) hU * u.gradientCoordL2NormSum := by
  let hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  let u : H1Function U := H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU hf1
  let C : ℝ := smoothPoincareConst (d := d) (U := U) hU
  let Csq : ℝ := smoothPoincareSqConst (d := d) (U := U) hU
  have huInt : MeasureTheory.IntegrableOn f U := by
    simpa [u, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
      H1Function.ofContDiffOnIsSobolevRegularDomain] using u.integrableOn
  have hu_toFun : (u : Vec d → ℝ) = f := by
    funext x
    simp [u, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
      H1Function.ofContDiffOnIsSobolevRegularDomain]
  have hu_avg : integralAverage U u = integralAverage U f := by
    rw [hu_toFun]
  have hpoinc :
      ∫ x in U, ‖f x - integralAverage U f‖ ^ (2 : ℝ) ∂MeasureTheory.volume ≤
        (((MeasureTheory.volume U).toReal⁻¹ *
            (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ))) ^ (2 : ℝ)) *
          ((((d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
              (4 * Classical.choose hU.isBoundedDomain)) ^ (2 : ℝ)) *
            ∫ y in U, ‖fderiv ℝ f y‖ ^ (2 : ℝ) ∂MeasureTheory.volume) := by
    simpa using
      (integral_rpow_norm_sub_integralAverage_le_bound_of_isOpenBoundedConvexDomain
        (d := d) (U := U) hU huInt hf (p := (2 : ℝ)) (by norm_num) hvol)
  have hfderiv_mem :
      MeasureTheory.MemLp (fderiv ℝ f) 2 (volumeMeasureOn U) :=
    memLp_fderiv_of_contDiffOnIsOpenBoundedConvexDomain hU hf1
  have hleft_sq :
      ‖u.subAverage.toScalarL2‖ ^ 2 =
        ∫ x in U, ‖f x - integralAverage U f‖ ^ (2 : ℝ) ∂MeasureTheory.volume := by
    calc
      ‖u.subAverage.toScalarL2‖ ^ 2
          = ∫ x in U, ‖u.subAverage x‖ ^ (2 : ℝ) ∂MeasureTheory.volume :=
              norm_toScalarL2_sq_eq_integral_rpow_norm (U := U) u.subAverage
      _ = ∫ x in U, ‖f x - integralAverage U f‖ ^ (2 : ℝ)
            ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun hU.isOpen.measurableSet ?_
          intro x hx
          change ‖u x - integralAverage U u‖ ^ (2 : ℝ) =
            ‖f x - integralAverage U f‖ ^ (2 : ℝ)
          rw [hu_avg, show u x = f x by rw [hu_toFun]]
  have hderiv_sq :
      (ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) 2 (volumeMeasureOn U))) ^ 2 =
        ∫ y in U, ‖fderiv ℝ f y‖ ^ (2 : ℝ) ∂MeasureTheory.volume :=
    toReal_eLpNorm_two_sq_eq_integral_rpow_norm hfderiv_mem
  have hbase_sq :
      ‖u.subAverage.toScalarL2‖ ^ 2 ≤
        Csq *
          (ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) 2 (volumeMeasureOn U))) ^ 2 := by
    calc
      ‖u.subAverage.toScalarL2‖ ^ 2
          = ∫ x in U, ‖f x - integralAverage U f‖ ^ (2 : ℝ) ∂MeasureTheory.volume :=
              hleft_sq
      _ ≤ Csq * ∫ y in U, ‖fderiv ℝ f y‖ ^ (2 : ℝ) ∂MeasureTheory.volume := by
          calc
            ∫ x in U, ‖f x - integralAverage U f‖ ^ (2 : ℝ) ∂MeasureTheory.volume
                ≤ (((MeasureTheory.volume U).toReal⁻¹ *
                    (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ))) ^
                      (2 : ℝ)) *
                  ((((d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
                      (4 * Classical.choose hU.isBoundedDomain)) ^ (2 : ℝ)) *
                    ∫ y in U, ‖fderiv ℝ f y‖ ^ (2 : ℝ) ∂MeasureTheory.volume) := hpoinc
            _ = Csq * ∫ y in U, ‖fderiv ℝ f y‖ ^ (2 : ℝ)
                  ∂MeasureTheory.volume := by
                dsimp [Csq, smoothPoincareSqConst]
                ring
      _ = Csq *
          (ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) 2 (volumeMeasureOn U))) ^ 2 := by
            rw [hderiv_sq]
  have hderiv_le_grad :
      ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) 2 (volumeMeasureOn U)) ≤
        u.gradientCoordL2NormSum := by
    simpa [u, hf1] using
      fderivL2Norm_le_gradientCoordL2NormSum_ofContDiffOnIsOpenBoundedConvexDomain
        (U := U) hU hf
  have htarget_sq :
      ‖u.subAverage.toScalarL2‖ ^ 2 ≤
        (C * u.gradientCoordL2NormSum) ^ 2 := by
    have hCsq_le : Csq ≤ C ^ 2 := by
      simpa [C, Csq] using
        smoothPoincareSqConst_le_const_sq (d := d) (U := U) hU
    have hderiv_nonneg :
        0 ≤ ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) 2 (volumeMeasureOn U)) :=
      ENNReal.toReal_nonneg
    have hgrad_nonneg : 0 ≤ u.gradientCoordL2NormSum :=
      u.gradientCoordL2NormSum_nonneg
    calc
      ‖u.subAverage.toScalarL2‖ ^ 2
          ≤ Csq *
              (ENNReal.toReal
                (MeasureTheory.eLpNorm (fderiv ℝ f) 2 (volumeMeasureOn U))) ^ 2 :=
            hbase_sq
      _ ≤ C ^ 2 *
              (ENNReal.toReal
                (MeasureTheory.eLpNorm (fderiv ℝ f) 2 (volumeMeasureOn U))) ^ 2 := by
            exact mul_le_mul_of_nonneg_right hCsq_le (sq_nonneg _)
      _ ≤ C ^ 2 * u.gradientCoordL2NormSum ^ 2 := by
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ hderiv_nonneg hderiv_le_grad 2) (sq_nonneg C)
      _ = (C * u.gradientCoordL2NormSum) ^ 2 := by ring
  have hright_nonneg : 0 ≤ C * u.gradientCoordL2NormSum := by
    exact mul_nonneg (by simpa [C] using smoothPoincareConst_nonneg (d := d) (U := U) hU)
      u.gradientCoordL2NormSum_nonneg
  change ‖u.subAverage.toScalarL2‖ ≤ C * u.gradientCoordL2NormSum
  exact le_of_sq_le_sq htarget_sq hright_nonneg

private theorem unitConvexApproxScale_pos (n : ℕ) :
    0 < unitConvexApproxScale n := by
  dsimp [unitConvexApproxScale]
  positivity

noncomputable def convexApproxSmoothH1
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ) : H1Function U :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
    ((contDiff_convexApproxSmoothRepresentative
      (U := U) (ρ := unitConvexApproxKernel (d := d)) (u := u.toFun)
      (p := (2 : ENNReal)) (x0 := x0) (r := r) (ε := unitConvexApproxScale n)
      hU.isOpen.measurableSet (isConvexApproxKernel_unitConvexApproxKernel (d := d))
      (by norm_num : (1 : ENNReal) ≤ 2) u.memL2 hr (unitConvexApproxScale_pos n)).of_le
      (by simp))

theorem convexApproxSmoothH1_toFun
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (convexApproxSmoothH1 (U := U) hU u x0 hr n : Vec d → ℝ) =
      convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d)) u x0 r
        (unitConvexApproxScale n) := by
  funext x
  simp [convexApproxSmoothH1, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain]

theorem convexApproxSmoothH1_grad
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (convexApproxSmoothH1 (U := U) hU u x0 hr n).grad =
      fun x i =>
        (fderiv ℝ
          (convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d)) u x0 r
            (unitConvexApproxScale n)) x) (basisVec i) := by
  funext x i
  simp [convexApproxSmoothH1, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain]

theorem tendsto_convexApproxSmoothH1_toScalarL2
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Filter.Tendsto
      (fun n => (convexApproxSmoothH1 (U := U) hU u x0 hr n).toScalarL2)
      Filter.atTop (nhds u.toScalarL2) := by
  let ρ : Vec d → ℝ := unitConvexApproxKernel (d := d)
  let ψ : ℕ → H1Function U := convexApproxSmoothH1 (U := U) hU u x0 hr
  have hρ : IsConvexApproxKernel ρ := by
    simpa [ρ] using isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hevent_lt_one : ∀ᶠ n : ℕ in Filter.atTop, unitConvexApproxScale n < 1 :=
    (((tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one).mono
      (fun _ hn => hn))
  have hraw :
      Filter.Tendsto
        (fun n : ℕ =>
          MeasureTheory.eLpNorm
            (fun x => convexApproxSmoothing ρ u x0 r (unitConvexApproxScale n) x - u x)
            2 (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    simpa [ρ, volumeMeasureOn] using
      (tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
        (U := U) hU hρ (by norm_num : (1 : ENNReal) ≤ 2) (by simp : (2 : ENNReal) ≠ ⊤)
        u.memL2 hball hr tendsto_unitConvexApproxScale_zero
        (Filter.Eventually.of_forall unitConvexApproxScale_pos) hevent_lt_one)
  have hrep :
      Filter.Tendsto
        (fun n : ℕ =>
          MeasureTheory.eLpNorm
            (fun x =>
              convexApproxSmoothRepresentative U ρ u x0 r (unitConvexApproxScale n) x -
                u x)
            2 (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    refine hraw.congr' ?_
    filter_upwards [hevent_lt_one] with n hε_lt_one
    apply MeasureTheory.eLpNorm_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem hU.isOpen.measurableSet] with x hx
    rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := u.toFun) hU hρ hx hball hr (unitConvexApproxScale_pos n) hε_lt_one]
  rw [tendsto_iff_dist_tendsto_zero]
  have hdist :
      (fun n => dist (ψ n).toScalarL2 u.toScalarL2) =
        fun n =>
          ENNReal.toReal
            (MeasureTheory.eLpNorm
              (fun x =>
                convexApproxSmoothRepresentative U ρ u x0 r (unitConvexApproxScale n) x -
                  u x)
              2 (volumeMeasureOn U)) := by
    funext n
    have hψ_toFun := convexApproxSmoothH1_toFun (U := U) hU u x0 hr n
    have hedist0 :
        edist (ψ n).toScalarL2 u.toScalarL2 =
          MeasureTheory.eLpNorm ((ψ n).toFun - u.toFun) 2 (volumeMeasureOn U) := by
      simp [ψ, H1Function.toScalarL2, Homogenization.toScalarL2]
    have hedist :
        edist (ψ n).toScalarL2 u.toScalarL2 =
          MeasureTheory.eLpNorm
            (fun x =>
              convexApproxSmoothRepresentative U ρ u x0 r (unitConvexApproxScale n) x -
                u x)
            2 (volumeMeasureOn U) := by
      calc
        edist (ψ n).toScalarL2 u.toScalarL2
            = MeasureTheory.eLpNorm ((ψ n).toFun - u.toFun) 2 (volumeMeasureOn U) :=
                hedist0
        _ = MeasureTheory.eLpNorm
            (fun x =>
              convexApproxSmoothRepresentative U ρ u x0 r (unitConvexApproxScale n) x -
                u x)
            2 (volumeMeasureOn U) := by
              congr 1
    rw [MeasureTheory.Lp.dist_edist, hedist]
  rw [hdist]
  have hmem :
      ∀ n : ℕ,
        MeasureTheory.MemLp
          (fun x =>
            convexApproxSmoothRepresentative U ρ u x0 r (unitConvexApproxScale n) x -
              u x)
          2 (volumeMeasureOn U) := by
    intro n
    have hψ_toFun := convexApproxSmoothH1_toFun (U := U) hU u x0 hr n
    have hsub : MeasureTheory.MemLp (fun x => (ψ n).toFun x - u x) 2 (volumeMeasureOn U) :=
      (ψ n).memL2.sub u.memL2
    refine MeasureTheory.MemLp.ae_eq ?_ hsub
    filter_upwards with x
    rw [show (ψ n).toFun x =
      convexApproxSmoothRepresentative U ρ u x0 r (unitConvexApproxScale n) x by
        simpa [ρ] using congrFun hψ_toFun x]
  exact (ENNReal.tendsto_toReal_zero_iff (fun n => (hmem n).eLpNorm_lt_top.ne)).2 hrep

theorem tendsto_convexApproxSmoothH1_gradCoordToScalarL2
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (i : Fin d) :
    Filter.Tendsto
      (fun n => (convexApproxSmoothH1 (U := U) hU u x0 hr n).gradCoordToScalarL2 i)
      Filter.atTop (nhds (u.gradCoordToScalarL2 i)) := by
  let ρ : Vec d → ℝ := unitConvexApproxKernel (d := d)
  let ψ : ℕ → H1Function U := convexApproxSmoothH1 (U := U) hU u x0 hr
  have hρ : IsConvexApproxKernel ρ := by
    simpa [ρ] using isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hevent_lt_one : ∀ᶠ n : ℕ in Filter.atTop, unitConvexApproxScale n < 1 :=
    (((tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one).mono
      (fun _ hn => hn))
  have hraw :
      Filter.Tendsto
        (fun n : ℕ =>
          MeasureTheory.eLpNorm
            (fun x =>
              (1 - unitConvexApproxScale n) *
                  convexApproxSmoothing ρ (fun y => u.grad y i) x0 r
                    (unitConvexApproxScale n) x -
                u.grad x i)
            2 (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    simpa [ρ, volumeMeasureOn] using
      (tendsto_eLpNorm_sub_zero_one_sub_mul_convexApproxSmoothing_of_memLpOn
        (U := U) hU hρ (by norm_num : (1 : ENNReal) ≤ 2) (by simp : (2 : ENNReal) ≠ ⊤)
        (u.grad_memL2 i) hball hr tendsto_unitConvexApproxScale_zero
        (Filter.Eventually.of_forall unitConvexApproxScale_pos) hevent_lt_one)
  have hrep :
      Filter.Tendsto
        (fun n : ℕ =>
          MeasureTheory.eLpNorm
            (fun x =>
              (fderiv ℝ
                (convexApproxSmoothRepresentative U ρ u x0 r (unitConvexApproxScale n)) x)
                  (basisVec i) -
                u.grad x i)
            2 (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    refine hraw.congr' ?_
    filter_upwards [hevent_lt_one] with n hε_lt_one
    apply MeasureTheory.eLpNorm_congr_ae
    have hbridge :=
      ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
        (U := U) (ρ := ρ) (u := u.toFun) (gi := fun y => u.grad y i)
        (i := i) (p := (2 : ENNReal)) hU hρ (by norm_num : (1 : ENNReal) ≤ 2)
        u.memL2 (u.grad_memL2 i) (u.hasWeakPartialDerivOn i)
        hball hr (unitConvexApproxScale_pos n) hε_lt_one
    filter_upwards [hbridge, MeasureTheory.ae_restrict_mem hU.isOpen.measurableSet] with x hxbridge hxU
    rw [hxbridge]
    rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := fun y => u.grad y i) hU hρ hxU hball hr (unitConvexApproxScale_pos n)
        hε_lt_one]
  rw [tendsto_iff_dist_tendsto_zero]
  have hdist :
      (fun n => dist ((ψ n).gradCoordToScalarL2 i) (u.gradCoordToScalarL2 i)) =
        fun n =>
          ENNReal.toReal
            (MeasureTheory.eLpNorm
              (fun x =>
                (fderiv ℝ
                  (convexApproxSmoothRepresentative U ρ u x0 r (unitConvexApproxScale n)) x)
                    (basisVec i) -
                  u.grad x i)
              2 (volumeMeasureOn U)) := by
    funext n
    have hψ_grad := convexApproxSmoothH1_grad (U := U) hU u x0 hr n
    have hedist0 :
        edist ((ψ n).gradCoordToScalarL2 i) (u.gradCoordToScalarL2 i) =
          MeasureTheory.eLpNorm
            (((fun x => (ψ n).grad x i) - fun x => u.grad x i))
            2 (volumeMeasureOn U) := by
      simp [ψ, H1Function.gradCoordToScalarL2, Homogenization.toScalarL2]
    have hedist :
        edist ((ψ n).gradCoordToScalarL2 i) (u.gradCoordToScalarL2 i) =
          MeasureTheory.eLpNorm
            (fun x =>
              (fderiv ℝ
                (convexApproxSmoothRepresentative U ρ u x0 r (unitConvexApproxScale n)) x)
                  (basisVec i) -
                u.grad x i)
            2 (volumeMeasureOn U) := by
      calc
        edist ((ψ n).gradCoordToScalarL2 i) (u.gradCoordToScalarL2 i)
            = MeasureTheory.eLpNorm
                (((fun x => (ψ n).grad x i) - fun x => u.grad x i))
                2 (volumeMeasureOn U) := hedist0
        _ = MeasureTheory.eLpNorm
            (fun x =>
              (fderiv ℝ
                (convexApproxSmoothRepresentative U ρ u x0 r (unitConvexApproxScale n)) x)
                  (basisVec i) -
                u.grad x i)
            2 (volumeMeasureOn U) := by
              congr 1
    rw [MeasureTheory.Lp.dist_edist, hedist]
  rw [hdist]
  have hmem :
      ∀ n : ℕ,
        MeasureTheory.MemLp
          (fun x =>
            (fderiv ℝ
              (convexApproxSmoothRepresentative U ρ u x0 r (unitConvexApproxScale n)) x)
                (basisVec i) -
              u.grad x i)
          2 (volumeMeasureOn U) := by
    intro n
    have hψ_grad := convexApproxSmoothH1_grad (U := U) hU u x0 hr n
    have hsub : MeasureTheory.MemLp (fun x => (ψ n).grad x i - u.grad x i)
        2 (volumeMeasureOn U) :=
      ((ψ n).grad_memL2 i).sub (u.grad_memL2 i)
    refine MeasureTheory.MemLp.ae_eq ?_ hsub
    filter_upwards with x
    rw [show (ψ n).grad x i =
      (fderiv ℝ
        (convexApproxSmoothRepresentative U ρ u x0 r (unitConvexApproxScale n)) x)
          (basisVec i) by
        simpa [ρ] using congrFun (congrFun hψ_grad x) i]
  exact (ENNReal.tendsto_toReal_zero_iff (fun n => (hmem n).eLpNorm_lt_top.ne)).2 hrep

/-- The smooth Poincare estimate passes to arbitrary `H¹` functions by the
convex smoothing approximation. -/
private theorem norm_toScalarL2_subAverage_le_smoothPoincareConst_mul_gradientCoordL2NormSum
    [NeZero d] [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (u : H1Function U) :
    ‖u.subAverage.toScalarL2‖ ≤
      smoothPoincareConst (d := d) (U := U) hU * u.gradientCoordL2NormSum := by
  have hnonempty : U.Nonempty := by
    by_contra hne
    have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst U
    simp at hvol
  rcases hnonempty with ⟨x0, hx0⟩
  rcases Metric.mem_nhds_iff.1 (hU.isOpen.mem_nhds hx0) with ⟨δ, hδpos, hδsub⟩
  let r : ℝ := δ / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hball : Metric.closedBall x0 r ⊆ U := by
    intro y hy
    apply hδsub
    have hy' : dist y x0 ≤ r := by
      simpa [Metric.mem_closedBall] using hy
    have hlt : dist y x0 < δ := by
      have hrδ : r < δ := by
        dsimp [r]
        linarith
      exact lt_of_le_of_lt hy' hrδ
    simpa [Metric.mem_ball] using hlt
  let ψ : ℕ → H1Function U := fun n => convexApproxSmoothH1 (U := U) hU u x0 hr n
  have hψ_bound :
      ∀ n, ‖(ψ n).subAverage.toScalarL2‖ ≤
        smoothPoincareConst (d := d) (U := U) hU * (ψ n).gradientCoordL2NormSum := by
    intro n
    let f : Vec d → ℝ :=
      convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d)) u x0 r
        (unitConvexApproxScale n)
    have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
      contDiff_convexApproxSmoothRepresentative
        (U := U) (ρ := unitConvexApproxKernel (d := d)) (u := u.toFun)
        (p := (2 : ENNReal)) (x0 := x0) (r := r) (ε := unitConvexApproxScale n)
        hU.isOpen.measurableSet (isConvexApproxKernel_unitConvexApproxKernel (d := d))
        (by norm_num : (1 : ENNReal) ≤ 2) u.memL2 hr (unitConvexApproxScale_pos n)
    simpa [ψ, convexApproxSmoothH1, f] using
      (norm_toScalarL2_subAverage_le_smoothPoincareConst_mul_gradientCoordL2NormSum_ofContDiff
        (U := U) hU (f := f) hf hvol)
  have hleft :
      Filter.Tendsto (fun n => ‖(ψ n).subAverage.toScalarL2‖) Filter.atTop
        (nhds ‖u.subAverage.toScalarL2‖) := by
    have hval :
        Filter.Tendsto (fun n => (ψ n).toScalarL2) Filter.atTop
          (nhds u.toScalarL2) := by
      simpa [ψ] using
        (tendsto_convexApproxSmoothH1_toScalarL2 (U := U) hU u hball hr)
    exact (continuous_norm.tendsto _).comp
      (H1Function.tendsto_toScalarL2_subAverage_of_tendsto_toScalarL2 hval)
  have hright_grad :
      Filter.Tendsto (fun n => (ψ n).gradientCoordL2NormSum) Filter.atTop
        (nhds u.gradientCoordL2NormSum) := by
    have hgrad :
        ∀ i : Fin d,
          Filter.Tendsto (fun n => (ψ n).gradCoordToScalarL2 i) Filter.atTop
            (nhds (u.gradCoordToScalarL2 i)) := by
      intro i
      simpa [ψ] using
        (tendsto_convexApproxSmoothH1_gradCoordToScalarL2 (U := U) hU u hball hr i)
    simpa [H1Function.gradientCoordL2NormSum] using
      tendsto_finsetSum Finset.univ
        (fun i _ => (continuous_norm.tendsto _).comp (hgrad i))
  have hright :
      Filter.Tendsto
        (fun n =>
          smoothPoincareConst (d := d) (U := U) hU * (ψ n).gradientCoordL2NormSum)
        Filter.atTop
        (nhds (smoothPoincareConst (d := d) (U := U) hU * u.gradientCoordL2NormSum)) :=
    tendsto_const_nhds.mul hright_grad
  exact le_of_tendsto_of_tendsto' hleft hright hψ_bound

/-- Positive-dimensional, positive-volume bounded open convex domains satisfy
the mean-zero `L²` Poincare estimate. -/
private theorem h1MeanZero_valueL2Norm_le_smoothPoincareConst_mul_gradientL2Norm
    [NeZero d] [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (u : H1MeanZeroFunction U) :
    u.valueL2Norm ≤
      (smoothPoincareConst (d := d) (U := U) hU * d) * u.gradientL2Norm := by
  let C : ℝ := smoothPoincareConst (d := d) (U := U) hU
  have hC_nonneg : 0 ≤ C := by
    simpa [C] using smoothPoincareConst_nonneg (d := d) (U := U) hU
  have havg : integralAverage U u.toH1Function = 0 := by
    unfold integralAverage
    rw [u.meanZero]
    simp
  have hsub : u.toH1Function.subAverage = u.toH1Function := by
    apply H1Function.ext
    · funext x
      simp [havg]
    · funext x
      ext i
      simp
  have hbase :=
    norm_toScalarL2_subAverage_le_smoothPoincareConst_mul_gradientCoordL2NormSum
      (U := U) hU hvol u.toH1Function
  have hcoord := u.toH1Function.gradientCoordL2NormSum_le
  calc
    u.valueL2Norm = ‖u.toH1Function.subAverage.toScalarL2‖ := by
      rw [hsub]
      rfl
    _ ≤ C * u.toH1Function.gradientCoordL2NormSum := by
      simpa [C] using hbase
    _ ≤ C * (d * u.gradientL2Norm) := by
      simpa [H1MeanZeroFunction.gradientL2Norm, H1MeanZeroFunction.gradToVectorL2] using
        mul_le_mul_of_nonneg_left hcoord hC_nonneg
    _ = (C * d) * u.gradientL2Norm := by
      ring

private theorem h1MeanZero_valueL2Norm_eq_zero_of_volume_toReal_eq_zero
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hvol : (MeasureTheory.volume U).toReal = 0) (u : H1MeanZeroFunction U) :
    u.valueL2Norm = 0 := by
  have hfinite : MeasureTheory.volume U < ⊤ := by
    simpa [volumeMeasureOn] using
      (MeasureTheory.measure_lt_top (volumeMeasureOn U) Set.univ)
  have hvol0 : MeasureTheory.volume U = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff (MeasureTheory.volume U)).mp hvol with hzero | htop
    · exact hzero
    · exact (hfinite.ne htop).elim
  have hμ0 : volumeMeasureOn U = 0 := by
    simpa [volumeMeasureOn] using
      (MeasureTheory.Measure.restrict_eq_zero.2 hvol0 :
        MeasureTheory.volume.restrict U = 0)
  dsimp [H1MeanZeroFunction.valueL2Norm, H1MeanZeroFunction.toScalarL2,
    H1Function.toScalarL2, Homogenization.toScalarL2]
  rw [MeasureTheory.Lp.norm_toLp]
  rw [hμ0, MeasureTheory.eLpNorm_measure_zero]
  rfl

private theorem h1MeanZero_valueL2Norm_eq_zero_of_dim_zero
    {U : Set (Vec 0)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hvol : 0 < (MeasureTheory.volume U).toReal) (u : H1MeanZeroFunction U) :
    u.valueL2Norm = 0 := by
  let c : ℝ := u.toH1Function.toFun 0
  have hconst : u.toH1Function.toFun = fun _ : Vec 0 => c := by
    funext x
    exact congrArg u.toH1Function.toFun (Subsingleton.elim x (0 : Vec 0))
  have hmean_const : ∫ x in U, (fun _ : Vec 0 => c) x ∂MeasureTheory.volume = 0 := by
    change MeanZeroOn U (fun _ : Vec 0 => c)
    rw [← hconst]
    exact u.meanZero
  have hμ :
      (MeasureTheory.volume.restrict U).real Set.univ = MeasureTheory.volume.real U := by
    exact MeasureTheory.measureReal_restrict_apply_univ (μ := MeasureTheory.volume) U
  have hmean_mul : (MeasureTheory.volume U).toReal * c = 0 := by
    rw [MeasureTheory.integral_const] at hmean_const
    rw [hμ, smul_eq_mul] at hmean_const
    exact hmean_const
  have hc0 : c = 0 := by
    nlinarith
  have hzeroFun : u.toH1Function.toFun = 0 := by
    rw [hconst]
    funext x
    simp [hc0]
  have hL2 : u.toScalarL2 = 0 := by
    apply MeasureTheory.Lp.ext
    filter_upwards
        [H1Function.coeFn_toScalarL2 u.toH1Function,
          MeasureTheory.Lp.coeFn_zero ℝ (2 : ENNReal) (volumeMeasureOn U)]
      with x hx h0
    change u.toH1Function.toScalarL2 x = (0 : ScalarL2 U) x
    rw [hx, h0]
    exact congrFun hzeroFun x
  simp [H1MeanZeroFunction.valueL2Norm, hL2]

end H1Function

/-- Bounded open convex domains satisfy the mean-zero `L²` Poincare inequality,
packaged as an `H1CoerciveEstimate`.

Equivalently, there exists `C ≥ 0` such that every `u : H1MeanZeroFunction U`
satisfies `u.valueL2Norm ≤ C * u.gradientL2Norm`. -/
noncomputable def h1CoerciveEstimate_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) :
    H1CoerciveEstimate U := by
  classical
  by_cases hvol0 : (MeasureTheory.volume U).toReal = 0
  · exact
      { fixedValue := 0
        constant_nonneg := le_rfl
        bound := by
          intro u
          have hzero :=
            H1Function.h1MeanZero_valueL2Norm_eq_zero_of_volume_toReal_eq_zero
              (U := U) hvol0 u
          simp [hzero] }
  · have hvol : 0 < (MeasureTheory.volume U).toReal := by
      exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hvol0)
    by_cases hd0 : d = 0
    · subst d
      exact
        { fixedValue := 0
          constant_nonneg := le_rfl
          bound := by
            intro u
            have hzero :=
              H1Function.h1MeanZero_valueL2Norm_eq_zero_of_dim_zero
                (U := U) hvol u
            simp [hzero] }
    · letI : NeZero d := ⟨hd0⟩
      exact
        { fixedValue := H1Function.smoothPoincareConst (d := d) (U := U) hU * d
          constant_nonneg := by
            exact mul_nonneg
              (H1Function.smoothPoincareConst_nonneg (d := d) (U := U) hU)
              (Nat.cast_nonneg d)
          bound := by
            intro u
            exact
              H1Function.h1MeanZero_valueL2Norm_le_smoothPoincareConst_mul_gradientL2Norm
                (U := U) hU hvol u }

theorem h1CoerciveEstimate_of_isOpenBoundedConvexDomain_constant_le_chosenBound
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) :
    (h1CoerciveEstimate_of_isOpenBoundedConvexDomain (U := U) hU).fixedValue ≤
      H1Function.h1CoerciveEstimateChosenBound (d := d) (U := U) hU := by
  classical
  unfold h1CoerciveEstimate_of_isOpenBoundedConvexDomain
  by_cases hvol0 : (MeasureTheory.volume U).toReal = 0
  · simp [hvol0,
      H1Function.h1CoerciveEstimateChosenBound_nonneg (d := d) (U := U) hU]
  · by_cases hd0 : d = 0
    · subst d
      simp [hvol0,
        H1Function.h1CoerciveEstimateChosenBound_nonneg (d := 0) (U := U) hU]
    · let : NeZero d := ⟨hd0⟩
      simp [hvol0, hd0, H1Function.h1CoerciveEstimateChosenBound,
        H1Function.smoothPoincareConst, H1Function.smoothPoincareSqConst]

/-- Unbundled existential form of
`h1CoerciveEstimate_of_isOpenBoundedConvexDomain`. -/
theorem exists_poincare_constant_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : H1MeanZeroFunction U, u.valueL2Norm ≤ C * u.gradientL2Norm := by
  refine
    ⟨
      (h1CoerciveEstimate_of_isOpenBoundedConvexDomain (U := U) hU).fixedValue,
      (h1CoerciveEstimate_of_isOpenBoundedConvexDomain (U := U) hU).constant_nonneg,
      ?_
    ⟩
  intro u
  exact (h1CoerciveEstimate_of_isOpenBoundedConvexDomain (U := U) hU).bound u

end Homogenization
