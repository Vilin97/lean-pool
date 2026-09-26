/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareLp
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing

/-! # Seminorms -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

/-!
# Mean-zero `W^{1,p}` Poincare scaffolding

This file is the public landing zone for the finite-`p` extension of the
bounded-open-convex mean-zero Poincare theorem.

The completed `p = 2` endpoint in `PoincareMeanZero.lean` is bundled as an
`H1CoerciveEstimate`, because it feeds the Hilbert/Hodge layer.  The finite-`p`
surface here stays in terms of `eLpNorm` seminorms attached to the witness-based
`W1pFunction` API.
-/

/-- For a finite positive real exponent, the real value of the `eLpNorm` is the
usual integral power expression. -/
theorem toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : MeasureTheory.Measure α}
    {f : α → E} {p : ℝ} (hp : 0 < p)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p) μ) :
    ENNReal.toReal (MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ) =
      (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p : ℝ) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    intro hzero
    exact (not_le_of_gt hp) (ENNReal.ofReal_eq_zero.mp hzero)
  have hp_real : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal hp.le
  have h :=
    hf.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top
  rw [h]
  have hnonneg :
      0 ≤
        (∫ x, ‖f x‖ ^ (ENNReal.ofReal p).toReal ∂μ) ^
          ((ENNReal.ofReal p).toReal)⁻¹ := by
    positivity
  rw [ENNReal.toReal_ofReal hnonneg, hp_real]
  simp [one_div]

/-- Powered form of `toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv`. -/
theorem toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : MeasureTheory.Measure α}
    {f : α → E} {p : ℝ} (hp : 0 < p)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p) μ) :
    (ENNReal.toReal (MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ)) ^ p =
      ∫ x, ‖f x‖ ^ p ∂μ := by
  rw [toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv hp hf]
  have hint_nonneg : 0 ≤ ∫ x, ‖f x‖ ^ p ∂μ := by
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
  rw [← Real.rpow_mul hint_nonneg]
  have hp_ne : p ≠ 0 := ne_of_gt hp
  rw [show (1 / p : ℝ) * p = 1 by field_simp [hp_ne]]
  simp

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}

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

theorem memLp_fderiv_of_contDiffOnIsOpenBoundedConvexDomain
    (hU : IsOpenBoundedConvexDomain U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) :
    MeasureTheory.MemLp (fderiv ℝ f) p (volumeMeasureOn U) := by
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

/-- The scalar `L^p(U)` seminorm of a `W^{1,p}` witness, as a real number. -/
noncomputable def valueLpSeminorm (u : W1pFunction U p) : ℝ :=
  ENNReal.toReal (MeasureTheory.eLpNorm u.toFun p (volumeMeasureOn U))

/-- The scalar `L^p(U)` seminorm after subtracting the integral average. -/
noncomputable def subAverageLpSeminorm (u : W1pFunction U p) : ℝ :=
  ENNReal.toReal
    (MeasureTheory.eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) p
      (volumeMeasureOn U))

/-- The `i`th coordinate `L^p(U)` seminorm of the weak gradient. -/
noncomputable def gradCoordLpSeminorm (u : W1pFunction U p) (i : Fin d) : ℝ :=
  ENNReal.toReal (MeasureTheory.eLpNorm (fun x => u.grad x i) p (volumeMeasureOn U))

/-- Coordinate-sum gradient seminorm used by the finite-`p` Poincare API.

This avoids introducing a vector-valued `Lp` wrapper for every exponent at this
stage, while matching the data already stored in `W1pFunction.gradMemLp`. -/
noncomputable def gradientCoordLpSeminormSum (u : W1pFunction U p) : ℝ :=
  ∑ i : Fin d, u.gradCoordLpSeminorm i

theorem valueLpSeminorm_nonneg (u : W1pFunction U p) :
    0 ≤ u.valueLpSeminorm :=
  ENNReal.toReal_nonneg

theorem subAverageLpSeminorm_nonneg (u : W1pFunction U p) :
    0 ≤ u.subAverageLpSeminorm :=
  ENNReal.toReal_nonneg

theorem gradCoordLpSeminorm_nonneg (u : W1pFunction U p) (i : Fin d) :
    0 ≤ u.gradCoordLpSeminorm i :=
  ENNReal.toReal_nonneg

theorem gradientCoordLpSeminormSum_nonneg (u : W1pFunction U p) :
    0 ≤ u.gradientCoordLpSeminormSum := by
  exact Finset.sum_nonneg fun i _ => u.gradCoordLpSeminorm_nonneg i

private theorem eLpNorm_basisVec_apply_eq_gradCoordLpSeminorm
    (hU : IsOpenBoundedConvexDomain U) {f : Vec d → ℝ}
    (hf1 : ContDiff ℝ 1 f) (i : Fin d) :
    ENNReal.toReal
        (MeasureTheory.eLpNorm (fun x => ‖(fderiv ℝ f x) (basisVec i)‖) p
          (volumeMeasureOn U)) =
      (W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
        (U := U) (p := p) hU hf1).gradCoordLpSeminorm i := by
  let u : W1pFunction U p :=
    W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU hf1
  let dg : Vec d → ℝ := fun x => (fderiv ℝ f x) (basisVec i)
  calc
    ENNReal.toReal
        (MeasureTheory.eLpNorm (fun x => ‖(fderiv ℝ f x) (basisVec i)‖) p
          (volumeMeasureOn U))
      = ENNReal.toReal (MeasureTheory.eLpNorm dg p (volumeMeasureOn U)) := by
          rw [MeasureTheory.eLpNorm_norm _
            ((hf1.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable]
    _ = ENNReal.toReal (MeasureTheory.eLpNorm (fun x => u.grad x i) p
          (volumeMeasureOn U)) := by
          simp [u, dg, W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
            W1pFunction.ofContDiffOnIsSobolevRegularDomain]
    _ = u.gradCoordLpSeminorm i := rfl

theorem fderivLpNorm_le_gradientCoordLpSeminormSum_ofContDiffOnIsOpenBoundedConvexDomain
    (hU : IsOpenBoundedConvexDomain U) (hp1 : 1 ≤ p) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    let u : W1pFunction U p :=
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU (hf.of_le (by simp))
    ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) p (volumeMeasureOn U)) ≤
      u.gradientCoordLpSeminormSum := by
  let hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn U
  let : MeasureTheory.IsFiniteMeasure μ := by
    dsimp [μ, volumeMeasureOn]
    exact hU.isFiniteMeasure_restrict_volume
  let u : W1pFunction U p := W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU hf1
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
      MeasureTheory.MemLp (fderiv ℝ f) p μ := by
    refine MeasureTheory.MemLp.of_bound (μ := μ) hfderiv_cont.aestronglyMeasurable CD ?_
    rw [MeasureTheory.ae_restrict_iff' hU.isOpen.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => hCD x (subset_closure hx)
  let dLp : MeasureTheory.Lp (Vec d →L[ℝ] ℝ) p μ :=
    hfderiv_mem.toLp (fderiv ℝ f)
  have hdi_mem :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => ‖dg i x‖) p μ := by
    intro i
    simpa [u, dg, W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain] using (u.grad_memLp i).norm
  have hD_mem : MeasureTheory.MemLp D p μ := by
    have hsum :=
      MeasureTheory.memLp_finsetSum (μ := μ) (p := p)
        (s := Finset.univ) (f := fun i : Fin d => fun x : Vec d => ‖dg i x‖)
        (fun i hi => hdi_mem i)
    simpa [D] using hsum
  let dCoordLp : MeasureTheory.Lp ℝ p μ := hD_mem.toLp D
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
      ‖dCoordLp‖ ≤ ∑ i : Fin d, u.gradCoordLpSeminorm i := by
    let di : Fin d → Vec d → ℝ := fun i x => ‖dg i x‖
    have hsum_eLp :
        MeasureTheory.eLpNorm D p μ ≤
          ∑ i : Fin d, MeasureTheory.eLpNorm (di i) p μ := by
      have hD : D = ∑ i : Fin d, di i := by
        funext x
        simp [D, di]
      rw [hD]
      simpa using
        (MeasureTheory.eLpNorm_sum_le
          (μ := μ)
          (s := Finset.univ)
          (f := di)

          hp1)
    calc
      ‖dCoordLp‖ = ENNReal.toReal (MeasureTheory.eLpNorm D p μ) := by
            simp [dCoordLp]
      _ ≤ ENNReal.toReal (∑ i : Fin d, MeasureTheory.eLpNorm (di i) p μ) := by
            refine ENNReal.toReal_mono ?_ hsum_eLp
            exact ENNReal.sum_ne_top.2 fun i _ => (hdi_mem i).eLpNorm_lt_top.ne
      _ = ∑ i : Fin d, u.gradCoordLpSeminorm i := by
            rw [ENNReal.toReal_sum (fun i hi => (hdi_mem i).eLpNorm_lt_top.ne)]
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa [di, hf1, μ] using
              eLpNorm_basisVec_apply_eq_gradCoordLpSeminorm
                (U := U) (p := p) hU hf1 i
  have hfderiv_eq :
      ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) p μ) = ‖dLp‖ := by
    simp [dLp]
  change ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) p μ) ≤
    u.gradientCoordLpSeminormSum
  calc
    ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) p μ)
        = ‖dLp‖ := hfderiv_eq
    _ ≤ ‖dCoordLp‖ := hderiv_le_sum
    _ ≤ u.gradientCoordLpSeminormSum := hsum_le


end W1pFunction

end Homogenization
