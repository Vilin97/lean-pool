/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH10
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.Definitions
public import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain

/-! # Poincare Zero Trace -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

/-- File-level typeclass cache: `Nontrivial (Vec d)` under `[NeZero d]`.
Short-circuits the `NeZero → Nonempty → Nontrivial` instance-search chain
file-wide and propagates to downstream importers via the serialized
instance database. Controlled A/B on this file: cumulative
`typeclass inference` drops ~2.2s, `simp` ~1.2s (~4.4s total). -/
private instance instNontrivialVecPZT (d : ℕ) [NeZero d] :
    Nontrivial (Vec d) := inferInstance

/-- File-level typeclass cache for `NoncompactSpace (Vec d)` under
`[NeZero d]`; paired with the `Nontrivial` cache above. -/
private instance instNoncompactSpaceVecPZT (d : ℕ) [NeZero d] :
    NoncompactSpace (Vec d) := inferInstance

/-!
# Zero-trace Poincare on bounded open convex domains

This file is the public theorem wrapper for the bounded-open-convex
zero-trace Poincare development.

We freeze the general finite-`p` theorem surface on `W^{1,p}_0` here so
downstream PDE files can target the correct statement while the Sobolev proof
is completed separately. The existing `L²` estimate from `CoerciveH10` is then
repackaged in the same style as the mean-zero wrapper file.
-/

private theorem fderiv_coord_apply_basisVec_self {d : ℕ} (i : Fin d) (x : Vec d) :
    (fderiv ℝ (fun y : Vec d => y i) x) (basisVec i) = 1 := by
  have h :
      fderiv ℝ (fun y : Vec d => y i) x =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) := by
    exact ContinuousLinearMap.fderiv (𝕜 := ℝ)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)
  rw [h]
  simp [basisVec]

private theorem integral_eq_neg_integral_fderiv_mul_coord
    {d : ℕ} {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : HasCompactSupport f) (i : Fin d) :
    ∫ x, f x ∂MeasureTheory.volume =
      -∫ x, (fderiv ℝ f x) (basisVec i) * x i ∂MeasureTheory.volume := by
  let coord : Vec d → ℝ := fun x => x i
  let v : Vec d := basisVec i
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hf_diff : Differentiable ℝ f := hf1.differentiable (by simp)
  have hcoord_diff : Differentiable ℝ coord := by
    dsimp [coord]
    fun_prop
  have hf_cont : Continuous f := hf_diff.continuous
  have hcoord_cont : Continuous coord := by
    dsimp [coord]
    fun_prop
  have hfderiv_cont : Continuous (fun x => (fderiv ℝ f x) v) := by
    simpa [v] using (hf1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfderiv_supp : HasCompactSupport (fun x => (fderiv ℝ f x) v) := by
    simpa [v] using hf_supp.fderiv_apply (𝕜 := ℝ) v
  have h1 :
      MeasureTheory.Integrable (fun x => (fderiv ℝ f x) v * coord x)
        MeasureTheory.volume := by
    exact (hfderiv_cont.mul hcoord_cont).integrable_of_hasCompactSupport
      hfderiv_supp.mul_right
  have h2 :
      MeasureTheory.Integrable (fun x => f x * (fderiv ℝ coord x) v)
        MeasureTheory.volume := by
    have hf_int : MeasureTheory.Integrable f MeasureTheory.volume :=
      hf_cont.integrable_of_hasCompactSupport hf_supp
    simpa [coord, v, fderiv_coord_apply_basisVec_self] using hf_int
  have h3 : MeasureTheory.Integrable (fun x => f x * coord x) MeasureTheory.volume := by
    exact (hf_cont.mul hcoord_cont).integrable_of_hasCompactSupport hf_supp.mul_right
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := MeasureTheory.volume) (f := f) (g := coord) (v := v)
    h1 h2 h3 (fun x _ => hf_diff x) (fun x _ => hcoord_diff x)
  simpa [coord, v, fderiv_coord_apply_basisVec_self] using h

private theorem support_fderiv_apply_basisVec_subset_of_tsupport_subset
    {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ} (i : Fin d)
    (hsub : tsupport f ⊆ U) :
    Function.support (fun x => (fderiv ℝ f x) (basisVec i)) ⊆ U := by
  intro x hx
  exact hsub <|
    (support_fderiv_subset (𝕜 := ℝ) (f := f)) <| by
      change fderiv ℝ f x ≠ 0
      intro hzero
      apply hx
      simp [hzero]

private theorem setIntegral_eq_neg_setIntegral_fderiv_mul_coord
    {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f)
    (hf_sub : tsupport f ⊆ U) (i : Fin d) :
    ∫ x in U, f x ∂MeasureTheory.volume =
      -∫ x in U, (fderiv ℝ f x) (basisVec i) * x i ∂MeasureTheory.volume := by
  have hzero_f : ∀ x, x ∉ U → f x = 0 := by
    intro x hxU
    exact image_eq_zero_of_notMem_tsupport (fun hxt => hxU (hf_sub hxt))
  have hzero_d : ∀ x, x ∉ U → (fderiv ℝ f x) (basisVec i) * x i = 0 := by
    intro x hxU
    have hxnot : x ∉ Function.support (fun x => (fderiv ℝ f x) (basisVec i)) :=
      fun hx => hxU (support_fderiv_apply_basisVec_subset_of_tsupport_subset (U := U) i
        hf_sub hx)
    have hderiv : (fderiv ℝ f x) (basisVec i) = 0 := by
      simpa [Function.notMem_support] using hxnot
    simp [hderiv]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero_f,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero_d,
    integral_eq_neg_integral_fderiv_mul_coord hf hf_supp i]

private theorem abs_setIntegral_le_bound_mul_integral_abs_fderiv_coord
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f)
    (hf_sub : tsupport f ⊆ U) (i : Fin d) :
    |∫ x in U, f x ∂MeasureTheory.volume| ≤
      Classical.choose hU.isBoundedDomain *
        ∫ x in U, |(fderiv ℝ f x) (basisVec i)| ∂MeasureTheory.volume := by
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn U
  let dg : Vec d → ℝ := fun x => (fderiv ℝ f x) (basisVec i)
  let R : ℝ := Classical.choose hU.isBoundedDomain
  let : MeasureTheory.IsFiniteMeasure μ := by
    simpa [μ, volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  have hR_nonneg : 0 ≤ R := le_of_lt (Classical.choose_spec hU.isBoundedDomain).1
  have hgrad_int : MeasureTheory.Integrable (fun x => |dg x|) μ := by
    let w : W1pFunction U (1 : ENNReal) :=
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU (hf.of_le (by simp))
    have hw : MeasureTheory.Integrable (fun x => w.grad x i) μ := by
      exact (w.grad_memLp i).integrable (by norm_num : (1 : ENNReal) ≤ 1)
    simpa [w, dg, μ, W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain, Real.norm_eq_abs] using hw.norm
  have hprod_int : MeasureTheory.Integrable (fun x => |dg x * x i|) μ := by
    refine (hgrad_int.const_mul R).mono' ?_ ?_
    · exact ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul
        (by fun_prop) |>.norm.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem hU.isOpen.measurableSet] with x hxU
      have hcoord : |x i| ≤ R := (Classical.choose_spec hU.isBoundedDomain).2 x hxU i
      calc
        ‖|dg x * x i|‖ = |dg x * x i| := by simp
        _ = |dg x| * |x i| := abs_mul _ _
        _ ≤ |dg x| * R := mul_le_mul_of_nonneg_left hcoord (abs_nonneg _)
        _ = R * |dg x| := by ring
  have hmono :
      (fun x => |dg x * x i|) ≤ᵐ[μ] fun x => R * |dg x| := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU.isOpen.measurableSet] with x hxU
    have hcoord : |x i| ≤ R := (Classical.choose_spec hU.isBoundedDomain).2 x hxU i
    calc
      |dg x * x i| = |dg x| * |x i| := abs_mul _ _
      _ ≤ |dg x| * R := mul_le_mul_of_nonneg_left hcoord (abs_nonneg _)
      _ = R * |dg x| := by ring
  calc
    |∫ x in U, f x ∂MeasureTheory.volume|
        = |-(∫ x in U, dg x * x i ∂MeasureTheory.volume)| := by
          rw [setIntegral_eq_neg_setIntegral_fderiv_mul_coord hf hf_supp hf_sub i]
    _ = |∫ x in U, dg x * x i ∂MeasureTheory.volume| := abs_neg _
    _ ≤ ∫ x in U, |dg x * x i| ∂MeasureTheory.volume := by
          simpa [μ, volumeMeasureOn, dg] using
            (MeasureTheory.abs_integral_le_integral_abs
              (μ := μ) (f := fun x => dg x * x i))
    _ ≤ ∫ x in U, R * |dg x| ∂MeasureTheory.volume := by
          simpa [μ, volumeMeasureOn, dg, R] using
            (MeasureTheory.integral_mono_ae hprod_int (hgrad_int.const_mul R) hmono)
    _ = R * ∫ x in U, |dg x| ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_const_mul]

private theorem integral_abs_fderiv_coord_le_eLpNorm_mul_measure
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {q : ℝ} (hq : 1 < q) {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin d) :
    ∫ x in U, |(fderiv ℝ f x) (basisVec i)| ∂MeasureTheory.volume ≤
      ENNReal.toReal
        (MeasureTheory.eLpNorm (fun x => (fderiv ℝ f x) (basisVec i)) (ENNReal.ofReal q)
          (volumeMeasureOn U)) *
        ENNReal.toReal ((volumeMeasureOn U) Set.univ ^ (1 - 1 / q : ℝ)) := by
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn U
  let dg : Vec d → ℝ := fun x => (fderiv ℝ f x) (basisVec i)
  let pE : ENNReal := ENNReal.ofReal q
  let : MeasureTheory.IsFiniteMeasure μ := by
    simpa [μ, volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hpE_one : (1 : ENNReal) ≤ pE := by
    dsimp [pE]
    rw [ENNReal.one_le_ofReal]
    exact hq.le
  have hmem1 : MeasureTheory.MemLp dg 1 μ := by
    let w : W1pFunction U (1 : ENNReal) :=
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU (hf.of_le (by simp))
    simpa [w, dg, μ, W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain] using (w.grad_memLp i)
  have hmemp : MeasureTheory.MemLp dg pE μ := by
    let w : W1pFunction U pE :=
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU (hf.of_le (by simp))
    simpa [w, dg, pE, μ, W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain] using (w.grad_memLp i)
  have hL1_eq :
      ∫ x in U, |(fderiv ℝ f x) (basisVec i)| ∂MeasureTheory.volume =
        ENNReal.toReal (MeasureTheory.eLpNorm dg 1 μ) := by
    have hnorm :
        ENNReal.toReal (MeasureTheory.eLpNorm dg (ENNReal.ofReal (1 : ℝ)) μ) =
          (∫ x, ‖dg x‖ ^ (1 : ℝ) ∂μ) ^ (1 / (1 : ℝ) : ℝ) := by
      exact toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv
        (μ := μ) (f := dg) (p := (1 : ℝ)) zero_lt_one (by simpa using hmem1)
    have hpow :
        (∫ x, ‖dg x‖ ^ (1 : ℝ) ∂μ) ^ (1 / (1 : ℝ) : ℝ) =
          ∫ x, |dg x| ∂μ := by
      simp [Real.norm_eq_abs]
    calc
      ∫ x in U, |(fderiv ℝ f x) (basisVec i)| ∂MeasureTheory.volume
          = ∫ x, |dg x| ∂μ := by rfl
      _ = ENNReal.toReal (MeasureTheory.eLpNorm dg 1 μ) := by
          rw [show (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) by norm_num]
          rw [hnorm, hpow]
  have hle_en :
      MeasureTheory.eLpNorm dg 1 μ ≤
        MeasureTheory.eLpNorm dg pE μ * μ Set.univ ^ (1 - 1 / q : ℝ) := by
    simpa [μ, pE, ENNReal.toReal_ofReal hq_pos.le] using
      (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := μ) (f := dg) (p := (1 : ENNReal)) (q := pE) hpE_one
        hmemp.aestronglyMeasurable)
  have hexp_nonneg : 0 ≤ (1 - 1 / q : ℝ) := by
    have hinv_le : 1 / q ≤ 1 := (div_le_one hq_pos).2 hq.le
    linarith
  have hmeasure_pow_ne_top : μ Set.univ ^ (1 - 1 / q : ℝ) ≠ ⊤ := by
    refine (ENNReal.rpow_lt_top_of_nonneg hexp_nonneg ?_).ne
    exact (MeasureTheory.measure_lt_top μ Set.univ).ne
  have hprod_ne_top : MeasureTheory.eLpNorm dg pE μ *
      μ Set.univ ^ (1 - 1 / q : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top hmemp.eLpNorm_lt_top.ne hmeasure_pow_ne_top
  calc
    ∫ x in U, |(fderiv ℝ f x) (basisVec i)| ∂MeasureTheory.volume
        = ENNReal.toReal (MeasureTheory.eLpNorm dg 1 μ) := hL1_eq
    _ ≤ ENNReal.toReal (MeasureTheory.eLpNorm dg pE μ *
          μ Set.univ ^ (1 - 1 / q : ℝ)) :=
        ENNReal.toReal_mono hprod_ne_top hle_en
    _ = ENNReal.toReal (MeasureTheory.eLpNorm dg pE μ) *
        ENNReal.toReal (μ Set.univ ^ (1 - 1 / q : ℝ)) := by
          rw [ENNReal.toReal_mul]

private theorem eLpNorm_const_toReal_ofReal
    {d : ℕ} {U : Set (Vec d)} {q : ℝ} (hq : 1 < q) (c : ℝ) :
    let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn U
    ENNReal.toReal (MeasureTheory.eLpNorm (fun _ : Vec d => c) (ENNReal.ofReal q) μ) =
      |c| * ENNReal.toReal (μ Set.univ ^ (1 / q : ℝ)) := by
  intro μ
  let pE : ENNReal := ENNReal.ofReal q
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hp0 : pE ≠ 0 := by
    dsimp [pE]
    intro hzero
    exact (not_le_of_gt hq_pos) (ENNReal.ofReal_eq_zero.mp hzero)
  have hp_top : pE ≠ ⊤ := by
    dsimp [pE]
    exact ENNReal.ofReal_ne_top
  have hconst := MeasureTheory.eLpNorm_const'
    (μ := μ) (p := pE) (c := c) hp0 hp_top
  calc
    ENNReal.toReal (MeasureTheory.eLpNorm (fun _ : Vec d => c) (ENNReal.ofReal q) μ)
        = ENNReal.toReal (‖c‖ₑ * μ Set.univ ^ (1 / q : ℝ)) := by
          simpa [pE, ENNReal.toReal_ofReal hq_pos.le] using congrArg ENNReal.toReal hconst
    _ = ENNReal.toReal ‖c‖ₑ * ENNReal.toReal (μ Set.univ ^ (1 / q : ℝ)) := by
          rw [ENNReal.toReal_mul]
    _ = |c| * ENNReal.toReal (μ Set.univ ^ (1 / q : ℝ)) := by
          simp [Real.norm_eq_abs]

private theorem const_average_lpSeminorm_le_bound_mul_gradCoord
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {q : ℝ} (hq : 1 < q) (_hvol : 0 < (MeasureTheory.volume U).toReal)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f)
    (hf_sub : tsupport f ⊆ U) (i : Fin d) :
    ENNReal.toReal
        (MeasureTheory.eLpNorm (fun _ : Vec d => integralAverage U f) (ENNReal.ofReal q)
          (volumeMeasureOn U)) ≤
      (((MeasureTheory.volume U).toReal⁻¹ * Classical.choose hU.isBoundedDomain) *
          ENNReal.toReal ((volumeMeasureOn U) Set.univ ^ (1 - 1 / q : ℝ)) *
        ENNReal.toReal ((volumeMeasureOn U) Set.univ ^ (1 / q : ℝ))) *
      ENNReal.toReal
        (MeasureTheory.eLpNorm (fun x => (fderiv ℝ f x) (basisVec i)) (ENNReal.ofReal q)
          (volumeMeasureOn U)) := by
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn U
  let gradNorm : ℝ := ENNReal.toReal
        (MeasureTheory.eLpNorm (fun x => (fderiv ℝ f x) (basisVec i)) (ENNReal.ofReal q) μ)
  let μpow1 : ℝ := ENNReal.toReal (μ Set.univ ^ (1 - 1 / q : ℝ))
  let μpow2 : ℝ := ENNReal.toReal (μ Set.univ ^ (1 / q : ℝ))
  let R : ℝ := Classical.choose hU.isBoundedDomain
  have hR_nonneg : 0 ≤ R := le_of_lt (Classical.choose_spec hU.isBoundedDomain).1
  have hμinv_nonneg : 0 ≤ (MeasureTheory.volume U).toReal⁻¹ := by positivity
  have hμpow2_nonneg : 0 ≤ μpow2 := ENNReal.toReal_nonneg
  have hset := abs_setIntegral_le_bound_mul_integral_abs_fderiv_coord
    (U := U) hU hf hf_supp hf_sub i
  have hl1 := integral_abs_fderiv_coord_le_eLpNorm_mul_measure
    (U := U) hU hq hf i
  have havg : |integralAverage U f| ≤
      (MeasureTheory.volume U).toReal⁻¹ * (R * (gradNorm * μpow1)) := by
    unfold integralAverage
    calc
      |(MeasureTheory.volume U).toReal⁻¹ * ∫ x in U, f x ∂MeasureTheory.volume|
          = (MeasureTheory.volume U).toReal⁻¹ *
              |∫ x in U, f x ∂MeasureTheory.volume| := by
            rw [abs_mul, abs_of_nonneg hμinv_nonneg]
      _ ≤ (MeasureTheory.volume U).toReal⁻¹ *
          (R * ∫ x in U, |(fderiv ℝ f x) (basisVec i)| ∂MeasureTheory.volume) := by
            exact mul_le_mul_of_nonneg_left hset hμinv_nonneg
      _ ≤ (MeasureTheory.volume U).toReal⁻¹ * (R * (gradNorm * μpow1)) := by
            refine mul_le_mul_of_nonneg_left ?_ hμinv_nonneg
            exact mul_le_mul_of_nonneg_left (by simpa [gradNorm, μpow1, μ] using hl1)
              hR_nonneg
  calc
    ENNReal.toReal
        (MeasureTheory.eLpNorm (fun _ : Vec d => integralAverage U f) (ENNReal.ofReal q)
          (volumeMeasureOn U))
        = |integralAverage U f| * μpow2 := by
          simpa [μ, μpow2] using
            (eLpNorm_const_toReal_ofReal (U := U) hq (integralAverage U f))
    _ ≤ ((MeasureTheory.volume U).toReal⁻¹ * (R * (gradNorm * μpow1))) * μpow2 := by
          exact mul_le_mul_of_nonneg_right havg hμpow2_nonneg
    _ = (((MeasureTheory.volume U).toReal⁻¹ * R) * μpow1 * μpow2) * gradNorm := by
          ring

private theorem valueLpSeminorm_le_subAverage_add_constLpSeminorm_ofContDiff
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {q : ℝ} (hq : 1 < q) {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    let u : W1pFunction U (ENNReal.ofReal q) :=
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU (hf.of_le (by simp))
    u.valueLpSeminorm ≤ u.subAverageLpSeminorm +
      ENNReal.toReal
        (MeasureTheory.eLpNorm (fun _ : Vec d => integralAverage U f) (ENNReal.ofReal q)
          (volumeMeasureOn U)) := by
  intro u
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn U
  let pE : ENNReal := ENNReal.ofReal q
  let avg : ℝ := integralAverage U f
  let : MeasureTheory.IsFiniteMeasure μ := by
    simpa [μ, volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  have hp1 : (1 : ENNReal) ≤ pE := by
    dsimp [pE]
    rw [ENNReal.one_le_ofReal]
    exact hq.le
  have hconst_mem : MeasureTheory.MemLp (fun _ : Vec d => avg) pE μ :=
    MeasureTheory.memLp_const avg
  have hsub_mem : MeasureTheory.MemLp (fun x => f x - avg) pE μ := by
    have hf_mem : MeasureTheory.MemLp f pE μ := by
      simpa [u, pE, μ, W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
        W1pFunction.ofContDiffOnIsSobolevRegularDomain] using u.memLp
    simpa [Pi.sub_apply] using! hf_mem.sub hconst_mem
  have htri :
      MeasureTheory.eLpNorm f pE μ ≤
        MeasureTheory.eLpNorm (fun x => f x - avg) pE μ +
          MeasureTheory.eLpNorm (fun _ : Vec d => avg) pE μ := by
    calc
      MeasureTheory.eLpNorm f pE μ
          = MeasureTheory.eLpNorm ((fun x => f x - avg) + fun _ : Vec d => avg)
              pE μ := by
              apply MeasureTheory.eLpNorm_congr_ae
              filter_upwards with x
              simp [avg]
      _ ≤ MeasureTheory.eLpNorm (fun x => f x - avg) pE μ +
            MeasureTheory.eLpNorm (fun _ : Vec d => avg) pE μ :=
          MeasureTheory.eLpNorm_add_le hp1
  have hsum_ne_top :
      MeasureTheory.eLpNorm (fun x => f x - avg) pE μ +
          MeasureTheory.eLpNorm (fun _ : Vec d => avg) pE μ ≠ ⊤ := by
    exact ENNReal.add_ne_top.2 ⟨hsub_mem.eLpNorm_lt_top.ne, hconst_mem.eLpNorm_lt_top.ne⟩
  calc
    u.valueLpSeminorm = ENNReal.toReal (MeasureTheory.eLpNorm f pE μ) := by
      simp [W1pFunction.valueLpSeminorm, u, pE, μ,
        W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
        W1pFunction.ofContDiffOnIsSobolevRegularDomain]
    _ ≤ ENNReal.toReal
          (MeasureTheory.eLpNorm (fun x => f x - avg) pE μ +
            MeasureTheory.eLpNorm (fun _ : Vec d => avg) pE μ) :=
        ENNReal.toReal_mono hsum_ne_top htri
    _ = ENNReal.toReal (MeasureTheory.eLpNorm (fun x => f x - avg) pE μ) +
          ENNReal.toReal (MeasureTheory.eLpNorm (fun _ : Vec d => avg) pE μ) := by
        rw [ENNReal.toReal_add hsub_mem.eLpNorm_lt_top.ne hconst_mem.eLpNorm_lt_top.ne]
    _ = u.subAverageLpSeminorm +
          ENNReal.toReal
            (MeasureTheory.eLpNorm (fun _ : Vec d => integralAverage U f) (ENNReal.ofReal q)
              (volumeMeasureOn U)) := by
        simp [W1pFunction.subAverageLpSeminorm, u, pE, μ, avg,
          W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
          W1pFunction.ofContDiffOnIsSobolevRegularDomain]

private theorem exists_smooth_zeroTrace_poincare_constant_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {q : ℝ} (hq : 1 < q)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f),
        HasCompactSupport f → tsupport f ⊆ U →
        let u : W1pFunction U (ENNReal.ofReal q) :=
          W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU (hf.of_le (by simp))
        u.valueLpSeminorm ≤ C * u.gradientCoordLpSeminormSum := by
  classical
  rcases W1pFunction.exists_subAverage_poincare_constant_of_isOpenBoundedConvexDomain
      (U := U) hU hq with ⟨Csub, hCsub, hsub⟩
  let i0 : Fin d := 0
  let Cavg : ℝ :=
    ((MeasureTheory.volume U).toReal⁻¹ * Classical.choose hU.isBoundedDomain) *
      ENNReal.toReal ((volumeMeasureOn U) Set.univ ^ (1 - 1 / q : ℝ)) *
        ENNReal.toReal ((volumeMeasureOn U) Set.univ ^ (1 / q : ℝ))
  have hCavg : 0 ≤ Cavg := by
    dsimp [Cavg]
    have hμinv : 0 ≤ (MeasureTheory.volume U).toReal⁻¹ := by positivity
    have hR : 0 ≤ Classical.choose hU.isBoundedDomain :=
      le_of_lt (Classical.choose_spec hU.isBoundedDomain).1
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hμinv hR) ENNReal.toReal_nonneg)
      ENNReal.toReal_nonneg
  refine ⟨Csub + Cavg, add_nonneg hCsub hCavg, ?_⟩
  intro f hf hf_supp hf_sub
  let u : W1pFunction U (ENNReal.ofReal q) :=
    W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU (hf.of_le (by simp))
  have htri := valueLpSeminorm_le_subAverage_add_constLpSeminorm_ofContDiff
    (U := U) hU hq (f := f) hf
  have hconst := const_average_lpSeminorm_le_bound_mul_gradCoord
    (U := U) hU hq hvol hf hf_supp hf_sub i0
  have hgrad_i_le_sum : u.gradCoordLpSeminorm i0 ≤ u.gradientCoordLpSeminormSum := by
    simpa [W1pFunction.gradientCoordLpSeminormSum] using
      (Finset.single_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun j => u.gradCoordLpSeminorm j)
        (fun j _ => u.gradCoordLpSeminorm_nonneg j)
        (by simp : i0 ∈ (Finset.univ : Finset (Fin d))))
  have hconst_u :
      ENNReal.toReal
          (MeasureTheory.eLpNorm (fun _ : Vec d => integralAverage U f) (ENNReal.ofReal q)
            (volumeMeasureOn U)) ≤
        Cavg * u.gradientCoordLpSeminormSum := by
    calc
      ENNReal.toReal
          (MeasureTheory.eLpNorm (fun _ : Vec d => integralAverage U f) (ENNReal.ofReal q)
            (volumeMeasureOn U))
          ≤ Cavg * u.gradCoordLpSeminorm i0 := by
            simpa [Cavg, u, i0, W1pFunction.gradCoordLpSeminorm,
              W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
              W1pFunction.ofContDiffOnIsSobolevRegularDomain] using hconst
      _ ≤ Cavg * u.gradientCoordLpSeminormSum :=
            mul_le_mul_of_nonneg_left hgrad_i_le_sum hCavg
  calc
    u.valueLpSeminorm
        ≤ u.subAverageLpSeminorm +
          ENNReal.toReal
            (MeasureTheory.eLpNorm (fun _ : Vec d => integralAverage U f) (ENNReal.ofReal q)
              (volumeMeasureOn U)) := by
            simpa [u] using htri
    _ ≤ Csub * u.gradientCoordLpSeminormSum + Cavg * u.gradientCoordLpSeminormSum :=
          add_le_add (hsub u) hconst_u
    _ = (Csub + Cavg) * u.gradientCoordLpSeminormSum := by ring

namespace W10pFunction

private theorem tendsto_toReal_eLpNorm_of_tendsto_eLpNorm_sub
    {d : ℕ} {p : ENNReal} {μ : MeasureTheory.Measure (Vec d)} (hp1 : 1 ≤ p)
    {F : ℕ → Vec d → ℝ} {f : Vec d → ℝ}
    (hF_mem : ∀ n, MeasureTheory.MemLp (F n) p μ)
    (hf_mem : MeasureTheory.MemLp f p μ)
    (hLp :
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun x => F n x - f x) p μ)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ENNReal.toReal (MeasureTheory.eLpNorm (F n) p μ))
      Filter.atTop (nhds (ENNReal.toReal (MeasureTheory.eLpNorm f p μ))) := by
  let : Fact (1 ≤ p) := ⟨hp1⟩
  have hLpSpace :
      Filter.Tendsto (fun n => (hF_mem n).toLp (F n))
        Filter.atTop (nhds (hf_mem.toLp f)) := by
    exact
      (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (μ := μ) (p := p) F hF_mem f hf_mem).2
        (by simpa [Pi.sub_apply] using! hLp)
  have hnorm :
      Filter.Tendsto (fun n => ‖(hF_mem n).toLp (F n)‖)
        Filter.atTop (nhds ‖hf_mem.toLp f‖) :=
    hLpSpace.norm
  simpa [MeasureTheory.Lp.norm_toLp] using hnorm

/-- Bounded open convex domains satisfy the zero-trace `W^{1,p}` Poincare
inequality.

Equivalently, there exists `C ≥ 0` such that every `u : W10pFunction U p`
satisfies an `L^p` bound of the function by the sum of the `L^p` norms of its
weak gradient coordinates. Lean keeps the exponent on the `W^{1,p}` layer as an
`ENNReal`. -/
theorem exists_poincare_constant_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)} {p : ENNReal}
    (hp : (1 : ENNReal) < p) (hp_top : p ≠ ⊤)
    (hU : IsOpenBoundedConvexDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : W10pFunction U p,
        ENNReal.toReal (MeasureTheory.eLpNorm u p (volumeMeasureOn U)) ≤
          C * ∑ i : Fin d,
            ENNReal.toReal
              (MeasureTheory.eLpNorm (fun x => u.toW1pFunction.grad x i) p (volumeMeasureOn U)) := by
  classical
  let q : ℝ := p.toReal
  have hq : 1 < q := by
    have htmp : (1 : ENNReal).toReal < p.toReal :=
      (ENNReal.toReal_lt_toReal (by simp : (1 : ENNReal) ≠ ⊤) hp_top).2 hp
    simpa [q] using htmp
  have hp_eq : ENNReal.ofReal q = p := ENNReal.ofReal_toReal hp_top
  rw [← hp_eq]
  let pE : ENNReal := ENNReal.ofReal q
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn U
  let : MeasureTheory.IsFiniteMeasure μ := by
    simpa [μ, volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  by_cases hvol0 : (MeasureTheory.volume U).toReal = 0
  · refine ⟨0, le_rfl, ?_⟩
    intro u
    have hfinite : MeasureTheory.volume U < ⊤ := by
      simpa [volumeMeasureOn] using
        (MeasureTheory.measure_lt_top (volumeMeasureOn U) Set.univ)
    have hvol0' : MeasureTheory.volume U = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (MeasureTheory.volume U)).mp hvol0 with hzero | htop
      · exact hzero
      · exact (hfinite.ne htop).elim
    have hμ0 : volumeMeasureOn U = 0 := by
      simpa [volumeMeasureOn] using
        (MeasureTheory.Measure.restrict_eq_zero.2 hvol0' :
          MeasureTheory.volume.restrict U = 0)
    simp [hμ0, MeasureTheory.eLpNorm_measure_zero]
  · have hvol : 0 < (MeasureTheory.volume U).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hvol0)
    rcases exists_smooth_zeroTrace_poincare_constant_of_isOpenBoundedConvexDomain
        (U := U) hU hq hvol with ⟨C, hC, hSmooth⟩
    refine ⟨C, hC, ?_⟩
    intro u
    let ψ : ℕ → W1pFunction U pE := fun n =>
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU
        ((u.approx_smooth n).of_le (by simp))
    have hp1 : (1 : ENNReal) ≤ pE := by
      dsimp [pE]
      rw [ENNReal.one_le_ofReal]
      exact hq.le
    have hψ_bound :
        ∀ n, (ψ n).valueLpSeminorm ≤ C * (ψ n).gradientCoordLpSeminormSum := by
      intro n
      simpa [ψ, pE] using
        (hSmooth (f := u.approx n) (u.approx_smooth n)
          (u.approx_hasCompactSupport n) (u.approx_support_subset n))
    have hleft :
        Filter.Tendsto (fun n => (ψ n).valueLpSeminorm) Filter.atTop
          (nhds u.toW1pFunction.valueLpSeminorm) := by
      have hnorm :=
        tendsto_toReal_eLpNorm_of_tendsto_eLpNorm_sub
          (μ := μ) (p := pE) hp1
          (F := fun n => (ψ n).toFun) (f := u.toW1pFunction.toFun)
          (fun n => (ψ n).memLp) u.toW1pFunction.memLp
          (by simpa [ψ, pE, μ, W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
              W1pFunction.ofContDiffOnIsSobolevRegularDomain] using u.tendsto_approx)
      simpa [W1pFunction.valueLpSeminorm, ψ, pE, μ] using hnorm
    have hgrad :
        ∀ i : Fin d,
          Filter.Tendsto (fun n => (ψ n).gradCoordLpSeminorm i) Filter.atTop
            (nhds (u.toW1pFunction.gradCoordLpSeminorm i)) := by
      intro i
      have hnorm :=
        tendsto_toReal_eLpNorm_of_tendsto_eLpNorm_sub
          (μ := μ) (p := pE) hp1
          (F := fun n => fun x => (ψ n).grad x i)
          (f := fun x => u.toW1pFunction.grad x i)
          (fun n => (ψ n).grad_memLp i) (u.toW1pFunction.grad_memLp i)
          (by simpa [ψ, pE, μ, W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
              W1pFunction.ofContDiffOnIsSobolevRegularDomain] using
              (u.tendsto_approx_grad i))
      simpa [W1pFunction.gradCoordLpSeminorm, ψ, pE, μ] using hnorm
    have hright_grad :
        Filter.Tendsto (fun n => (ψ n).gradientCoordLpSeminormSum) Filter.atTop
          (nhds u.toW1pFunction.gradientCoordLpSeminormSum) := by
      simpa [W1pFunction.gradientCoordLpSeminormSum] using
        tendsto_finsetSum Finset.univ (fun i _ => hgrad i)
    have hright :
        Filter.Tendsto (fun n => C * (ψ n).gradientCoordLpSeminormSum) Filter.atTop
          (nhds (C * u.toW1pFunction.gradientCoordLpSeminormSum)) :=
      tendsto_const_nhds.mul hright_grad
    have hlimit :
        u.toW1pFunction.valueLpSeminorm ≤
          C * u.toW1pFunction.gradientCoordLpSeminormSum :=
      le_of_tendsto_of_tendsto' hleft hright hψ_bound
    simpa [W1pFunction.valueLpSeminorm, W1pFunction.gradientCoordLpSeminormSum,
      W1pFunction.gradCoordLpSeminorm, pE, μ] using hlimit

end W10pFunction

namespace H10Function

noncomputable def toW10pFunction {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) : W10pFunction U (2 : ENNReal) :=
  { toW1pFunction :=
      { toFun := u.toH1Function.toFun
        grad := u.toH1Function.grad
        memLp := u.toH1Function.memL2
        gradMemLp := u.toH1Function.gradMemL2
        hasWeakGradient := u.toH1Function.hasWeakGradient }
    approx := u.approx
    approx_smooth := u.approx_smooth
    approx_hasCompactSupport := u.approx_hasCompactSupport
    approx_support_subset := u.approx_support_subset
    tendsto_approx := u.tendsto_approx
    tendsto_approx_grad := u.tendsto_approx_grad }

/-- Existential constant form of the bounded-open-convex zero-trace `L²`
Poincare inequality. This is the `H¹₀` wrapper parallel to the mean-zero
public theorem file. -/
theorem exists_poincare_constant_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : H10Function U,
        ‖u.toH1Function.toScalarL2‖ ≤ C * u.toH1Function.gradientCoordL2NormSum := by
  rcases W10pFunction.exists_poincare_constant_of_isOpenBoundedConvexDomain
      (U := U) (p := (2 : ENNReal)) (by norm_num) (by norm_num) hU with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro u
  have h := hbound u.toW10pFunction
  simpa [toW10pFunction, H1Function.toScalarL2, Homogenization.toScalarL2,
    MeasureTheory.Lp.norm_toLp, H1Function.gradientCoordL2NormSum,
    H1Function.gradCoordToScalarL2] using h

/-- Any zero-trace coercive estimate implies that an `H¹₀` function with zero
gradient `L²` class has zero value `L²` class. This isolates the only use of
the scalar Poincare inequality needed in the current RHS Dirichlet theory. -/
theorem toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_exists_poincare_constant
    {d : ℕ} {U : Set (Vec d)}
    (hP : ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : H10Function U,
        ‖u.toH1Function.toScalarL2‖ ≤ C * u.toH1Function.gradientCoordL2NormSum)
    (u : H10Function U) (hgrad : u.toH1Function.gradToVectorL2 = 0) :
    u.toH1Function.toScalarL2 = 0 := by
  rcases hP with ⟨C, _hC, hbound⟩
  have hgradCoordLeZero : u.toH1Function.gradientCoordL2NormSum ≤ 0 := by
    calc
      u.toH1Function.gradientCoordL2NormSum ≤ d * ‖u.toH1Function.gradToVectorL2‖ :=
        u.toH1Function.gradientCoordL2NormSum_le
      _ = 0 := by
        rw [hgrad, norm_zero, mul_zero]
  have hgradCoordZero : u.toH1Function.gradientCoordL2NormSum = 0 := by
    exact le_antisymm hgradCoordLeZero u.toH1Function.gradientCoordL2NormSum_nonneg
  have hvalueLeZero : ‖u.toH1Function.toScalarL2‖ ≤ 0 := by
    calc
      ‖u.toH1Function.toScalarL2‖ ≤ C * u.toH1Function.gradientCoordL2NormSum := hbound u
      _ = 0 := by rw [hgradCoordZero, mul_zero]
  exact norm_eq_zero.mp (le_antisymm hvalueLeZero (norm_nonneg _))

end H10Function

end Homogenization
