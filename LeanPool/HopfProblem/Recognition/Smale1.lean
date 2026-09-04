/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.TriangleRegularBaseFundamentalGroup
import all LeanPool.HopfProblem.Foundations.LineBundleTransport
import all LeanPool.HopfProblem.Foundations.TriangleRegularBaseFundamentalGroup
import all Mathlib.Analysis.Calculus.Implicit
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Hopf problem: recognition · smale 1

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private abbrev Smale.MorseHandle.UnitDisk (V : Type*) [NormedAddCommGroup V] :=
  Metric.closedBall (0 : V) 1

private def Smale.MorseHandle.modelMap {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (z : UnitDisk N × UnitDisk P) : N × P :=
  ((ρ * Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2)) • (z.1 : N), ρ • (z.2 : P))

private theorem Smale.MorseHandle.continuous_modelMap {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) :
    Continuous (modelMap (N := N) (P := P) ρ) := by
  have hu : Continuous (fun z : UnitDisk N × UnitDisk P => (z.1 : N)) :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous (fun z : UnitDisk N × UnitDisk P => (z.2 : P)) :=
    continuous_subtype_val.comp continuous_snd
  exact
    ((continuous_const.mul
              (Real.continuous_sqrt.comp (continuous_const.add (hv.norm.pow 2)))).smul
          hu).prodMk
      (continuous_const.smul hv)

private theorem Smale.MorseHandle.negative_scale_pos {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] {ρ : ℝ} (hρ : 0 < ρ) (z : UnitDisk N × UnitDisk P) :
    0 < ρ * Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2) :=
  mul_pos hρ (Real.sqrt_pos.mpr (by positivity))

private theorem Smale.MorseHandle.modelMap_injective {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) :
    Function.Injective (modelMap (N := N) (P := P) ρ) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have hv : (v : P) = (v' : P) := by
    have hh := congrArg (fun z : N × P => ρ⁻¹ • z.2) h
    simpa only [modelMap, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul] using hh
  have hv' : v = v' := Subtype.ext hv
  subst v'
  have hu : (u : N) = (u' : N) := by
    have hh := congrArg (fun z : N × P => (ρ * Real.sqrt (1 + ‖(v : P)‖ ^ 2))⁻¹ • z.1) h
    simpa only [modelMap, smul_smul, inv_mul_cancel₀ (negative_scale_pos hρ (u, v)).ne',
      one_smul] using hh
  exact Prod.ext (Subtype.ext hu) rfl

private theorem Smale.MorseHandle.modelMap_mem_product {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ)
    (z : UnitDisk N × UnitDisk P) :
    modelMap ρ z ∈ Metric.closedBall (0 : N) (2 * ρ) ×ˢ Metric.closedBall (0 : P) (2 * ρ) := by
  have hu : ‖(z.1 : N)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.1.2
  have hv : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.2
  have hv₂ : ‖(z.2 : P)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z.2 : P)]
  have hs : Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2) ≤ 2 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith⟩
  constructor
  · rw [mem_closedBall_zero_iff]
    change ‖(ρ * Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2)) • (z.1 : N)‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (negative_scale_pos hρ z)]
    calc
      _ ≤ ρ * Real.sqrt (1 + ‖(z.2 : P)‖ ^ 2) :=
        mul_le_of_le_one_right (negative_scale_pos hρ z).le hu
      _ ≤ ρ * 2 := (mul_le_mul_of_nonneg_left hs hρ.le)
      _ = _ := mul_comm _ _
  · rw [mem_closedBall_zero_iff]
    change ‖ρ • (z.2 : P)‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    have hh := mul_le_mul_of_nonneg_left hv hρ.le
    linarith

private theorem
    Smale.MorseHandle.modelMap_height {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : UnitDisk N × UnitDisk P) :
    -‖(modelMap ρ z).1‖ ^ 2 + ‖(modelMap ρ z).2‖ ^ 2 =
      ρ ^ 2 * ((1 + ‖(z.2 : P)‖ ^ 2) * (1 - ‖(z.1 : N)‖ ^ 2) - 1) := by
  simp only [modelMap, norm_smul, Real.norm_eq_abs, abs_of_pos (negative_scale_pos hρ z),
    abs_of_pos hρ, mul_pow, Real.sq_sqrt (show 0 ≤ 1 + ‖(z.2 : P)‖ ^ 2 by positivity)]
  ring

private theorem Smale.MorseHandle.modelMap_lower_iff {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ)
    (z : UnitDisk N × UnitDisk P) :
    -‖(modelMap ρ z).1‖ ^ 2 + ‖(modelMap ρ z).2‖ ^ 2 ≤ -(ρ ^ 2) ↔ ‖(z.1 : N)‖ = 1 := by
  rw [modelMap_height hρ z]
  have hu : ‖(z.1 : N)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.1.2
  have hu₀ := norm_nonneg (z.1 : N)
  have hpos : 0 < ρ ^ 2 * (1 + ‖(z.2 : P)‖ ^ 2) := mul_pos (sq_pos_of_pos hρ) (by positivity)
  constructor
  · intro h
    have hp : (ρ ^ 2 * (1 + ‖(z.2 : P)‖ ^ 2)) * (1 - ‖(z.1 : N)‖ ^ 2) ≤ 0 := by
      calc
        _ = ρ ^ 2 * ((1 + ‖(z.2 : P)‖ ^ 2) * (1 - ‖(z.1 : N)‖ ^ 2) - 1) + ρ ^ 2 := by ring
        _ ≤ 0 := by linarith
    have hm : 1 - ‖(z.1 : N)‖ ^ 2 ≤ 0 :=
      (mul_le_mul_iff_right₀ hpos).mp (by simpa only [MulZeroClass.mul_zero] using hp)
    nlinarith
  · intro h
    simp only [h, one_pow, sub_self, MulZeroClass.mul_zero, zero_sub, mul_neg, mul_one, le_refl]

private theorem
    Smale.MorseHandle.modelMap_upper {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : UnitDisk N × UnitDisk P) :
    -‖(modelMap ρ z).1‖ ^ 2 + ‖(modelMap ρ z).2‖ ^ 2 ≤ ρ ^ 2 := by
  rw [modelMap_height hρ z]
  have hv : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.2
  have hv₂ : ‖(z.2 : P)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z.2 : P)]
  have hu₂ : 0 ≤ ‖(z.1 : N)‖ ^ 2 := sq_nonneg _
  have hfactor : 0 ≤ 1 + ‖(z.2 : P)‖ ^ 2 := by positivity
  have hsmall : (1 + ‖(z.2 : P)‖ ^ 2) * (1 - ‖(z.1 : N)‖ ^ 2) - 1 ≤ 1 := by
    nlinarith [mul_nonneg hfactor hu₂]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall (sq_nonneg ρ)

private def Smale.MorseHandle.beltFaceScale (r : ℝ) : ℝ :=
  Real.sqrt (1 + r ^ 2) / Real.sqrt 2

private theorem Smale.MorseHandle.beltFaceScale_pos (r : ℝ) : 0 < beltFaceScale r :=
  div_pos (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by norm_num))

private theorem Smale.MorseHandle.continuous_beltFaceScale : Continuous beltFaceScale :=
  (Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))).div_const _

private theorem Smale.MorseHandle.beltFaceScale_one : beltFaceScale 1 = 1 := by
  simp only [beltFaceScale, one_pow, one_add_one_eq_two]
  exact div_self (Real.sqrt_pos.mpr (by norm_num)).ne'

private theorem
    Smale.MorseHandle.beltFaceScale_monotone : MonotoneOn beltFaceScale (Set.Ici 0) := by
  intro r hr s hs hrs
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg 2)
  apply Real.sqrt_le_sqrt
  have hsq : r ^ 2 ≤ s ^ 2 := (sq_le_sq₀ hr hs).mpr hrs
  linarith

private theorem Smale.MorseHandle.beltFaceRadius_strictMono :
    StrictMonoOn (fun r => beltFaceScale r * r) (Set.Ici 0) := by
  intro r hr s hs hrs
  exact
    (mul_lt_mul_of_pos_left hrs (beltFaceScale_pos r)).trans_le
      (mul_le_mul_of_nonneg_right (beltFaceScale_monotone hr hs hrs.le) hs)

private def
    Smale.MorseHandle.beltFaceMap {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] (u : N) :
    N :=
  beltFaceScale ‖u‖ • u

private theorem Smale.MorseHandle.continuous_beltFaceMap {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] : Continuous (beltFaceMap (N := N)) :=
  (continuous_beltFaceScale.comp continuous_norm).smul continuous_id

private theorem
    Smale.MorseHandle.norm_beltFaceMap {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (u : N) : ‖beltFaceMap u‖ = beltFaceScale ‖u‖ * ‖u‖ := by
  rw [beltFaceMap, norm_smul, Real.norm_eq_abs, abs_of_pos (beltFaceScale_pos _)]

private theorem
    Smale.MorseHandle.beltFaceMap_zero {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] :
    beltFaceMap (0 : N) = 0 := by simp only [beltFaceMap, smul_zero]

private theorem Smale.MorseHandle.norm_beltFaceMap_lt_one_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (u : N) : ‖beltFaceMap u‖ < 1 ↔ ‖u‖ < 1 := by
  have hh := beltFaceRadius_strictMono.lt_iff_lt (norm_nonneg u) (show 0 ≤ (1 : ℝ) by norm_num)
  simpa only [beltFaceScale_one, mul_one, norm_beltFaceMap] using hh

private theorem Smale.MorseHandle.beltFaceMap_mem_disk {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] {u : N} (hu : ‖u‖ ≤ 1) : ‖beltFaceMap u‖ ≤ 1 := by
  rw [norm_beltFaceMap]
  have hs : beltFaceScale ‖u‖ ≤ 1 := by
    rw [← beltFaceScale_one]
    exact beltFaceScale_monotone (norm_nonneg u) (by norm_num) hu
  exact (mul_le_mul_of_nonneg_right hs (norm_nonneg u)).trans (by simpa only [one_mul])

private theorem Smale.MorseHandle.beltFaceMap_injective {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] : Function.Injective (beltFaceMap (N := N)) := by
  intro u v huv
  have hn : ‖u‖ = ‖v‖ := by
    apply beltFaceRadius_strictMono.injOn (norm_nonneg u) (norm_nonneg v)
    simpa only [norm_beltFaceMap] using congrArg Norm.norm huv
  change beltFaceScale ‖u‖ • u = beltFaceScale ‖v‖ • v at huv
  rw [hn] at huv
  exact (smul_right_injective N (beltFaceScale_pos ‖v‖).ne') huv

private theorem Smale.MorseHandle.beltFaceMap_surjOn_disk {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] :
    Set.SurjOn (beltFaceMap (N := N)) (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
  intro v hv
  by_cases hvzero : v = 0
  · subst v
    exact ⟨0, mem_closedBall_zero_iff.mpr (by norm_num), beltFaceMap_zero⟩
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvzero
  have hvrange : ‖v‖ ∈ Set.Icc (beltFaceScale 0 * 0) (beltFaceScale 1 * 1) := by
    simpa only [MulZeroClass.mul_zero, beltFaceScale_one, mul_one, Set.mem_Icc] using
      And.intro hvpos.le (mem_closedBall_zero_iff.mp hv)
  obtain ⟨r, hr, hrv⟩ :=
    intermediate_value_Icc (a := (0 : ℝ)) (b := 1) (by norm_num)
      (continuous_beltFaceScale.mul continuous_id).continuousOn hvrange
  change beltFaceScale r * r = ‖v‖ at hrv
  let u : N := (r / ‖v‖) • v
  have hnorm : ‖u‖ = r := by
    change ‖(r / ‖v‖) • v‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr.1 hvpos.le),
      div_mul_cancel₀ _ hvpos.ne']
  refine ⟨u, mem_closedBall_zero_iff.mpr (hnorm ▸ hr.2), ?_⟩
  change beltFaceScale ‖u‖ • ((r / ‖v‖) • v) = v
  rw [hnorm, smul_smul, ← mul_div_assoc, hrv, div_self hvpos.ne', one_smul]

private def Smale.MorseHandle.beltFaceDiskMap {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] :
    UnitDisk N → UnitDisk N := fun u =>
  ⟨beltFaceMap u.val,
    mem_closedBall_zero_iff.mpr (beltFaceMap_mem_disk (mem_closedBall_zero_iff.mp u.property))⟩

private theorem Smale.MorseHandle.continuous_beltFaceDiskMap {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] : Continuous (beltFaceDiskMap (N := N)) :=
  (continuous_beltFaceMap.comp continuous_subtype_val).subtype_mk _

private theorem Smale.MorseHandle.beltFaceDiskMap_bijective {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] : Function.Bijective (beltFaceDiskMap (N := N)) := by
  constructor
  · intro u v huv
    exact Subtype.ext (beltFaceMap_injective (congrArg Subtype.val huv))
  · intro v
    obtain ⟨u, hu, huv⟩ := beltFaceMap_surjOn_disk v.property
    exact ⟨⟨u, hu⟩, Subtype.ext huv⟩

private def
    Smale.MorseHandle.beltFaceDiskHomeomorph {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] : UnitDisk N ≃ₜ UnitDisk N :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective beltFaceDiskMap beltFaceDiskMap_bijective) continuous_beltFaceDiskMap

private def Smale.MorseHandle.ambientMap {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (z : N × P) : N × P :=
  ((ρ * Real.sqrt (1 + ‖z.2‖ ^ 2)) • z.1, ρ • z.2)

private def Smale.MorseHandle.ambientInverse {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (z : N × P) : N × P :=
  ((ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2))⁻¹ • z.1, ρ⁻¹ • z.2)

private theorem Smale.MorseHandle.ambientInverse_ambientMap {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    ambientInverse ρ (ambientMap ρ z) = z := by
  have hscale : 0 < ρ * Real.sqrt (1 + ‖z.2‖ ^ 2) :=
    mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  apply Prod.ext
  · simp only [ambientInverse, ambientMap, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul,
      inv_mul_cancel₀ hscale.ne']
  · simp only [ambientInverse, ambientMap, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]

private theorem Smale.MorseHandle.ambientMap_ambientInverse {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    ambientMap ρ (ambientInverse ρ z) = z := by
  have hscale : 0 < ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2) :=
    mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  apply Prod.ext
  · simp only [ambientInverse, ambientMap, smul_smul, mul_inv_cancel₀ hscale.ne', one_smul]
  · simp only [ambientInverse, ambientMap, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]

private def
    Smale.MorseHandle.ambientHomeomorph {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (hρ : 0 < ρ) : (N × P) ≃ₜ (N × P) := by
  have hscale (v : P) : 0 < ρ * Real.sqrt (1 + ‖v‖ ^ 2) :=
    mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  refine
    { toFun := ambientMap ρ
      invFun := ambientInverse ρ
      left_inv := ambientInverse_ambientMap hρ
      right_inv := ambientMap_ambientInverse hρ
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · exact
      ((continuous_const.mul
                (Real.continuous_sqrt.comp
                  (continuous_const.add (continuous_snd.norm.pow 2)))).smul
            continuous_fst).prodMk
        (continuous_const.smul continuous_snd)
  · have hv : Continuous (fun z : N × P => ρ⁻¹ • z.2) := continuous_const.smul continuous_snd
    have hc : Continuous (fun z : N × P => ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2)) :=
      continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.add (hv.norm.pow 2)))
    exact ((hc.inv₀ (fun z => (hscale (ρ⁻¹ • z.2)).ne')).smul continuous_fst).prodMk hv

@[simp]
private theorem Smale.MorseHandle.ambientHomeomorph_zero {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (hρ : 0 < ρ) :
    ambientHomeomorph (N := N) (P := P) ρ hρ 0 = 0 := by
  change ambientMap ρ (0 : N × P) = 0
  simp only [ambientMap, Prod.fst_zero, Prod.snd_zero, smul_zero, Prod.mk_zero_zero]

private theorem Smale.MorseHandle.range_modelMap_mem_nhds_zero {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) :
    Set.range (modelMap (N := N) (P := P) ρ) ∈ 𝓝 (0 : N × P) := by
  let e := ambientHomeomorph (N := N) (P := P) ρ hρ
  let O := Metric.ball (0 : N) 1 ×ˢ Metric.ball (0 : P) 1
  have hO : IsOpen (e '' O) := e.isOpenMap O (Metric.isOpen_ball.prod Metric.isOpen_ball)
  have hzero : (0 : N × P) ∈ e '' O := by
    refine ⟨0, ?_, ambientHomeomorph_zero ρ hρ⟩
    exact ⟨by simp, by simp⟩
  have hsub : e '' O ⊆ Set.range (modelMap (N := N) (P := P) ρ) := by
    rintro _ ⟨z, hz, rfl⟩
    exact
      ⟨(⟨z.1, Metric.ball_subset_closedBall hz.1⟩, ⟨z.2, Metric.ball_subset_closedBall hz.2⟩),
        rfl⟩
  exact Filter.mem_of_superset (hO.mem_nhds hzero) hsub

private theorem
    Smale.MorseHandle.inverse_scale_sq {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {ρ : ℝ} (hρ : 0 < ρ) (v : P) : (ρ * Real.sqrt (1 + ‖ρ⁻¹ • v‖ ^ 2)) ^ 2 = ρ ^ 2 + ‖v‖ ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (by positivity), norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hρ)]
  field_simp

private theorem Smale.MorseHandle.mem_range_modelMap_iff {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    z ∈ Set.range (modelMap ρ) ↔ ‖z.2‖ ≤ ρ ∧ -(ρ ^ 2) ≤ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  let A := ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2)
  have hA : 0 < A := mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  have hA₂ : A ^ 2 = ρ ^ 2 + ‖z.2‖ ^ 2 := inverse_scale_sq hρ z.2
  have hneg : ‖A⁻¹ • z.1‖ ≤ 1 ↔ -(ρ ^ 2) ≤ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA), inv_mul_le_one₀ hA, ←
      sq_le_sq₀ (norm_nonneg z.1) hA.le, hA₂]
    constructor <;> intro h <;> linarith
  have hpos : ‖ρ⁻¹ • z.2‖ ≤ 1 ↔ ‖z.2‖ ≤ ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), inv_mul_le_one₀ hρ]
  constructor
  · rintro ⟨w, hw⟩
    have hi : ambientInverse ρ z = ((w.1 : N), (w.2 : P)) := by
      rw [← hw]
      exact ambientInverse_ambientMap hρ ((w.1 : N), (w.2 : P))
    have h₁ : A⁻¹ • z.1 = (w.1 : N) := congrArg Prod.fst hi
    have h₂ : ρ⁻¹ • z.2 = (w.2 : P) := congrArg Prod.snd hi
    exact
      ⟨hpos.mp (by rw [h₂]; exact mem_closedBall_zero_iff.mp w.2.2),
        hneg.mp (by rw [h₁]; exact mem_closedBall_zero_iff.mp w.1.2)⟩
  · intro hz
    refine
      ⟨(⟨A⁻¹ • z.1, mem_closedBall_zero_iff.mpr (hneg.mpr hz.2)⟩,
          ⟨ρ⁻¹ • z.2, mem_closedBall_zero_iff.mpr (hpos.mpr hz.1)⟩),
        ?_⟩
    exact ambientMap_ambientInverse hρ z

private def Smale.MorseHandle.quadratic {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    (z : N × P) : ℝ :=
  -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2

private def Smale.MorseHandle.descent {N P : Type*} [NormedAddCommGroup P] (z : N × P) : N × P :=
  (z.1, -z.2)

private theorem Smale.MorseHandle.contDiff_descent {N P : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [NormedAddCommGroup P] [InnerProductSpace ℝ P] :
    ContDiff ℝ ∞ (descent (N := N) (P := P)) :=
  contDiff_fst.prodMk contDiff_snd.neg

private theorem Smale.MorseHandle.fderiv_quadratic_descent {N P : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [NormedAddCommGroup P] [InnerProductSpace ℝ P] (z : N × P) :
    fderiv ℝ quadratic z (descent z) = -2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) := by
  have hd :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).norm_sq.neg.add
      (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).norm_sq
  have hd' := hd.fderiv
  change fderiv ℝ quadratic z = _ at hd'
  rw [hd']
  simp only [descent, add_apply, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', innerSL_apply_apply,
    inner_neg_right, real_inner_self_eq_norm_sq, two_smul]
  ring

private theorem Smale.MorseHandle.fderiv_quadratic_descent_neg {N P : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [NormedAddCommGroup P] [InnerProductSpace ℝ P] {z : N × P}
    (hz : z ≠ 0) : fderiv ℝ quadratic z (descent z) < 0 := by
  rw [fderiv_quadratic_descent]
  have hsum : 0 < ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
    by_contra! h
    have hu : ‖z.1‖ = 0 := by nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
    have hv : ‖z.2‖ = 0 := by nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
    exact hz (Prod.ext (norm_eq_zero.mp hu) (norm_eq_zero.mp hv))
  nlinarith

private def Smale.MorseHandle.descentFlow {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] : Flow ℝ (N × P)
    where
  toFun t z := (Real.exp t • z.1, Real.exp (-t) • z.2)
  cont' :=
    ((Real.continuous_exp.comp continuous_fst).smul continuous_snd.fst).prodMk
      ((Real.continuous_exp.comp continuous_fst.neg).smul continuous_snd.snd)
  map_add' s t z := by simp only [Real.exp_add, neg_add, smul_smul]
  map_zero' z := by simp

private theorem Smale.MorseHandle.hasDerivAt_descentFlow {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (z : N × P) (t : ℝ) :
    HasDerivAt (fun s => descentFlow s z) (descent (descentFlow t z)) t := by
  have h₁ := (Real.hasDerivAt_exp t).smul_const z.1
  have h₂ := ((hasDerivAt_id t).neg.exp).smul_const z.2
  simpa only [descentFlow, descent, id_eq, Pi.neg_apply, mul_neg, mul_one, neg_smul] using
    h₁.prodMk h₂

private theorem Smale.MorseHandle.norm_descentFlow_fst {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (t : ℝ) (z : N × P) :
    ‖(descentFlow t z).1‖ = Real.exp t * ‖z.1‖ := by
  change ‖Real.exp t • z.1‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]

private theorem Smale.MorseHandle.norm_descentFlow_snd {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (t : ℝ) (z : N × P) :
    ‖(descentFlow t z).2‖ = Real.exp (-t) * ‖z.2‖ := by
  change ‖Real.exp (-t) • z.2‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-t))]

private theorem Smale.MorseHandle.norm_fst_le_descentFlow {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {t : ℝ} (ht : 0 ≤ t) (z : N × P) :
    ‖z.1‖ ≤ ‖(descentFlow t z).1‖ := by
  rw [norm_descentFlow_fst]
  exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp_iff.mpr ht)

private theorem Smale.MorseHandle.norm_snd_descentFlow_le {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {t : ℝ} (ht : 0 ≤ t) (z : N × P) :
    ‖(descentFlow t z).2‖ ≤ ‖z.2‖ := by
  rw [norm_descentFlow_snd]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))

private theorem Smale.MorseHandle.mem_lower_union_handle_iff {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    z ∈ {w | quadratic w ≤ -(ρ ^ 2)} ∪ Set.range (modelMap ρ) ↔
      quadratic z ≤ -(ρ ^ 2) ∨ ‖z.2‖ ≤ ρ := by
  rw [Set.mem_union, Set.mem_ofPred_eq, mem_range_modelMap_iff hρ]
  change quadratic z ≤ -(ρ ^ 2) ∨ (‖z.2‖ ≤ ρ ∧ -(ρ ^ 2) ≤ quadratic z) ↔ _
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h.1
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hq : quadratic z ≤ -(ρ ^ 2)
      · exact Or.inl hq
      · exact Or.inr ⟨h, le_of_not_ge hq⟩

private def Smale.MorseHandle.beltFaceTime (r : ℝ) : ℝ :=
  Real.log (Real.sqrt (1 + r ^ 2))

private theorem Smale.MorseHandle.beltFaceTime_nonneg (r : ℝ) : 0 ≤ beltFaceTime r :=
  Real.log_nonneg (Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg r]))

private theorem Smale.MorseHandle.exp_beltFaceTime (r : ℝ) :
    Real.exp (beltFaceTime r) = Real.sqrt (1 + r ^ 2) :=
  Real.exp_log (Real.sqrt_pos.mpr (by positivity))

private def Smale.MorseHandle.beltLevelModel {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (u : N) (v : P) : N × P :=
  (ρ • u, (ρ * Real.sqrt (1 + ‖u‖ ^ 2)) • v)

private theorem Smale.MorseHandle.beltLevelModel_height {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (u : N)
    {v : P} (hv : ‖v‖ = 1) : quadratic (beltLevelModel ρ u v) = ρ ^ 2 := by
  have hs : 0 < Real.sqrt (1 + ‖u‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  simp only [quadratic, beltLevelModel, norm_smul, Real.norm_eq_abs, abs_of_pos hρ,
    abs_of_pos (mul_pos hρ hs), hv, mul_one, mul_pow,
    Real.sq_sqrt (show 0 ≤ 1 + ‖u‖ ^ 2 by positivity)]
  ring

private theorem Smale.MorseHandle.descentFlow_beltFaceTime {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (u : UnitDisk N)
    (v : UnitDisk P) (hv : ‖v.val‖ = 1) :
    descentFlow (beltFaceTime ‖u.val‖) (beltLevelModel ρ u.val v.val) =
      modelMap ρ (beltFaceDiskMap u, v) := by
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hu : Real.sqrt (1 + ‖u.val‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  apply Prod.ext
  · change
      Real.exp (beltFaceTime ‖u.val‖) • (ρ • u.val) =
        (ρ * Real.sqrt (1 + ‖v.val‖ ^ 2)) • (beltFaceScale ‖u.val‖ • u.val)
    rw [exp_beltFaceTime, hv, one_pow, one_add_one_eq_two, smul_smul, smul_smul]
    congr 1
    unfold beltFaceScale
    field_simp
  · change
      Real.exp (-beltFaceTime ‖u.val‖) • ((ρ * Real.sqrt (1 + ‖u.val‖ ^ 2)) • v.val) = ρ • v.val
    rw [Real.exp_neg, exp_beltFaceTime, smul_smul]
    congr 1
    field_simp

private theorem Smale.MorseHandle.descentFlow_beltLevelModel_mem_block {N P : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ}
    (hρ : 0 < ρ) (u : UnitDisk N) {v : P} (hv : ‖v‖ = 1) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (beltFaceTime ‖u.val‖)) :
    descentFlow t (beltLevelModel ρ u.val v) ∈
      Metric.closedBall (0 : N) (2 * ρ) ×ˢ Metric.closedBall (0 : P) (2 * ρ) := by
  have hu : ‖u.val‖ ≤ 1 := mem_closedBall_zero_iff.mp u.property
  have hspos : 0 < Real.sqrt (1 + ‖u.val‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs : Real.sqrt (1 + ‖u.val‖ ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [norm_nonneg u.val]⟩
  have he : Real.exp t ≤ Real.sqrt (1 + ‖u.val‖ ^ 2) := by
    rw [← exp_beltFaceTime]
    exact Real.exp_le_exp.mpr ht.2
  have hen : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.1)
  constructor
  · rw [mem_closedBall_zero_iff, norm_descentFlow_fst]
    change Real.exp t * ‖ρ • u.val‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    calc
      _ ≤ Real.exp t * ρ :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hρ.le hu) (Real.exp_pos t).le
      _ ≤ 2 * ρ := mul_le_mul_of_nonneg_right (he.trans hs) hρ.le
  · rw [mem_closedBall_zero_iff, norm_descentFlow_snd]
    change Real.exp (-t) * ‖(ρ * Real.sqrt (1 + ‖u.val‖ ^ 2)) • v‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hρ hspos), hv, mul_one]
    calc
      _ ≤ ρ * Real.sqrt (1 + ‖u.val‖ ^ 2) := mul_le_of_le_one_left (mul_pos hρ hspos).le hen
      _ ≤ ρ * 2 := (mul_le_mul_of_nonneg_left hs hρ.le)
      _ = 2 * ρ := mul_comm _ _

private theorem Smale.MorseHandle.descentFlow_neg_beltFaceTime {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (u : UnitDisk N)
    (v : UnitDisk P) (hv : ‖v.val‖ = 1) :
    descentFlow (-beltFaceTime ‖u.val‖) (modelMap ρ (beltFaceDiskMap u, v)) =
      beltLevelModel ρ u.val v.val := by
  rw [← descentFlow_beltFaceTime ρ u v hv, ← descentFlow.map_add, neg_add_cancel,
    descentFlow.map_zero_apply]

private theorem
    Smale.MorseHandle.descentFlow_positiveFace_mem_block {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ)
    (u : UnitDisk N) (v : UnitDisk P) (hv : ‖v.val‖ = 1) {t : ℝ}
    (ht : t ∈ Set.uIcc 0 (-beltFaceTime ‖u.val‖)) :
    descentFlow t (modelMap ρ (beltFaceDiskMap u, v)) ∈
      Metric.closedBall (0 : N) (2 * ρ) ×ˢ Metric.closedBall (0 : P) (2 * ρ) := by
  rw [Set.uIcc_of_ge (neg_nonpos.mpr (beltFaceTime_nonneg ‖u.val‖))] at ht
  rw [← descentFlow_beltFaceTime ρ u v hv, ← descentFlow.map_add]
  apply descentFlow_beltLevelModel_mem_block hρ u hv
  constructor <;> linarith [ht.1, ht.2]

private def Degree.BeltPassage.time (s : ℝ) : ℝ :=
  Real.log (Real.sqrt (1 + s ^ 2) / s)

private theorem Degree.BeltPassage.time_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ time s := by
  have hroot := Real.sqrt_nonneg (1 + s ^ 2)
  have hsquare := Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)
  apply Real.log_nonneg
  apply (le_div_iff₀ hs).mpr
  nlinarith

private theorem Degree.BeltPassage.exp_time {s : ℝ} (hs : 0 < s) :
    Real.exp (time s) = Real.sqrt (1 + s ^ 2) / s :=
  Real.exp_log (div_pos (Real.sqrt_pos.mpr (by positivity)) hs)

private def Degree.BeltPassage.upper {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ s : ℝ) (u : N) (v : P) : N × P :=
  ((ρ * s) • u, (ρ * Real.sqrt (1 + s ^ 2)) • v)

private def Degree.BeltPassage.lower {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ s : ℝ) (u : N) (v : P) : N × P :=
  ((ρ * Real.sqrt (1 + s ^ 2)) • u, (ρ * s) • v)

private theorem
    Degree.BeltPassage.descentFlow_time {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) {s : ℝ} (hs : 0 < s) (u : N) (v : P) :
    Smale.MorseHandle.descentFlow (time s) (Degree.BeltPassage.upper ρ s u v) =
      Degree.BeltPassage.lower ρ s u v := by
  have hr : Real.sqrt (1 + s ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  apply Prod.ext
  · change Real.exp (time s) • ((ρ * s) • u) = (ρ * Real.sqrt (1 + s ^ 2)) • u
    rw [exp_time hs, smul_smul]
    congr 1
    field_simp
  · change Real.exp (-time s) • ((ρ * Real.sqrt (1 + s ^ 2)) • v) = (ρ * s) • v
    rw [Real.exp_neg, exp_time hs, smul_smul]
    congr 1
    field_simp

private theorem Degree.BeltPassage.descentFlow_mem_block {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s)
    (hs₁ : s ≤ 1) {u : N} (hu : ‖u‖ = 1) {v : P} (hv : ‖v‖ = 1) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (time s)) :
    Smale.MorseHandle.descentFlow t (Degree.BeltPassage.upper ρ s u v) ∈
      Metric.closedBall (0 : N) (2 * ρ) ×ˢ Metric.closedBall (0 : P) (2 * ρ) := by
  have hrpos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hr : Real.sqrt (1 + s ^ 2) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hpos : 0 ≤ ρ * s := (mul_pos hρ hs).le
  constructor
  · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_fst]
    change Real.exp t * ‖(ρ * s) • u‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos, hu, mul_one]
    calc
      _ ≤ Real.exp (time s) * (ρ * s) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht.2) hpos
      _ = ρ * Real.sqrt (1 + s ^ 2) := by rw [exp_time hs]; field_simp
      _ ≤ ρ * 2 := (mul_le_mul_of_nonneg_left hr hρ.le)
      _ = 2 * ρ := mul_comm _ _
  · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_snd]
    change Real.exp (-t) * ‖(ρ * Real.sqrt (1 + s ^ 2)) • v‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hρ hrpos), hv, mul_one]
    calc
      _ ≤ ρ * Real.sqrt (1 + s ^ 2) :=
        mul_le_of_le_one_left (mul_pos hρ hrpos).le
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.1))
      _ ≤ ρ * 2 := (mul_le_mul_of_nonneg_left hr hρ.le)
      _ = 2 * ρ := mul_comm _ _

private theorem
    Degree.BeltPassage.contDiff_lower {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (u : N) (v : P) :
    ContDiff ℝ ∞ (fun s => Degree.BeltPassage.lower ρ s u v) :=
  ((contDiff_const.mul
            ((contDiff_const.add (contDiff_id.pow 2)).sqrt (fun _ => by positivity))).smul
        contDiff_const).prodMk
    ((contDiff_const.mul contDiff_id).smul contDiff_const)

private theorem Degree.BeltPassage.lower_zero {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (u : N) (v : P) :
    Degree.BeltPassage.lower ρ 0 u v = (ρ • u, 0) := by
  simp only [Degree.BeltPassage.lower, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_one,
    mul_one, MulZeroClass.mul_zero, zero_smul]

private theorem Degree.BeltPassage.upper_neg {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ s : ℝ) (u : N) (v : P) :
    Degree.BeltPassage.upper ρ (-s) u v = Degree.BeltPassage.upper ρ s (-u) v := by
  simp only [Degree.BeltPassage.upper, neg_sq, mul_neg, neg_smul, smul_neg]

private theorem
    Degree.BeltPassage.upper_height {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ s : ℝ) {u : N} (hu : ‖u‖ = 1) {v : P}
    (hv : ‖v‖ = 1) : Smale.MorseHandle.quadratic (Degree.BeltPassage.upper ρ s u v) = ρ ^ 2 := by
  simp only [Smale.MorseHandle.quadratic, Degree.BeltPassage.upper, norm_smul, Real.norm_eq_abs,
    hu, hv, mul_one, sq_abs, mul_pow, Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)]
  ring

private theorem
    Degree.BeltPassage.contDiff_upper {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (u : N) (v : P) :
    ContDiff ℝ ∞ (fun s => Degree.BeltPassage.upper ρ s u v) :=
  ((contDiff_const.mul contDiff_id).smul contDiff_const).prodMk
    ((contDiff_const.mul
          ((contDiff_const.add (contDiff_id.pow 2)).sqrt (fun _ => by positivity))).smul
      contDiff_const)

private theorem Degree.BeltPassage.upper_zero {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) (u : N) (v : P) :
    Degree.BeltPassage.upper ρ 0 u v = (0, ρ • v) := by
  simp only [Degree.BeltPassage.upper, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_one,
    mul_one, MulZeroClass.mul_zero, zero_smul]

private theorem
    Degree.BeltPassage.upper_mem_block {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ s : ℝ} (hρ : 0 < ρ) (hs : |s| ≤ 1) {u : N}
    (hu : ‖u‖ = 1) {v : P} (hv : ‖v‖ = 1) :
    Degree.BeltPassage.upper ρ s u v ∈
      Metric.closedBall (0 : N) (2 * ρ) ×ˢ Metric.closedBall (0 : P) (2 * ρ) := by
  have hrpos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hr : Real.sqrt (1 + s ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [sq_abs s, abs_nonneg s]⟩
  constructor
  · rw [mem_closedBall_zero_iff]
    change ‖(ρ * s) • u‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_mul, abs_of_pos hρ]
    have hh := mul_le_mul_of_nonneg_left hs hρ.le
    linarith
  · rw [mem_closedBall_zero_iff]
    change ‖(ρ * Real.sqrt (1 + s ^ 2)) • v‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hρ hrpos), hv, mul_one]
    exact (mul_le_mul_of_nonneg_left hr hρ.le).trans_eq (mul_comm _ _)

private def Smale.RegularValues.singularPoints {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) : Set E :=
  {x | (fderiv ℝ f x).det = 0}

private def Smale.RegularValues.regularValues {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) : Set E :=
  (f '' singularPoints f)ᶜ

private theorem Smale.RegularValues.mem_regularValues_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → E) (y : E) :
    y ∈ regularValues f ↔ ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0 := by
  constructor
  · intro hy x hx hdet
    exact hy ⟨x, hdet, hx⟩
  · intro hy ⟨x, hx, hxy⟩
    exact hy x hxy hx

private theorem Smale.RegularValues.bijective_iff_det_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (A : E →L[ℝ] E) :
    Function.Bijective A ↔ A.det ≠ 0 := by
  constructor
  · intro h hdet
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet) (LinearMap.ker_eq_bot.mpr h.1)
  · intro hdet
    have hker : A.toLinearMap.ker = ⊥ := by
      by_contra hn
      exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn)
    have hi := LinearMap.ker_eq_bot.mp hker
    exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

private theorem Smale.RegularValues.bijective_fderiv_of_mem_regularValues {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → E} {y : E}
    (hy : y ∈ regularValues f) {x : E} (hx : f x = y) : Function.Bijective (fderiv ℝ f x) := by
  have hdet := (mem_regularValues_iff f y).mp hy x hx
  exact (bijective_iff_det_ne_zero _).mpr hdet

private theorem
    Smale.RegularValues.measure_singularValues_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → E}
    (hf : Differentiable ℝ f) : μ (f '' singularPoints f) = 0 :=
  MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (fun x _ => (hf x).hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx)

private theorem Smale.RegularValues.dense_regularValues {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → E}
    (hf : Differentiable ℝ f) : Dense (regularValues f) := by
  have he : ∀ᵐ y ∂μ, y ∉ f '' singularPoints f := by
    rw [MeasureTheory.ae_iff]
    have hs : {y : E | ¬y ∉ f '' singularPoints f} = f '' singularPoints f := by
      ext y
      simp
    rw [hs]
    exact measure_singularValues_eq_zero μ hf
  exact μ.dense_of_ae he

private def Smale.MorsePerturbation.dualEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : E ≃L[ℝ] (E →L[ℝ] ℝ) := by
  classical
    exact
    ((Module.Basis.ofVectorSpace ℝ E).toDualEquiv.trans
        LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

private def Smale.MorsePerturbation.coordinateGradient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : E → ℝ) (x : E) : E :=
  dualEquiv.symm (fderiv ℝ f x)

private def Smale.MorsePerturbation.linearPerturbation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : E → ℝ) (a : E) (x : E) : ℝ :=
  f x - dualEquiv a x

private def Smale.MorsePerturbation.IsMorse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) : Prop :=
  ∀ x, fderiv ℝ f x = 0 → Function.Bijective (fderiv ℝ (fderiv ℝ f) x)

private theorem Smale.MorsePerturbation.contDiff_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fderiv ℝ f) :=
  hf.fderiv_right (by simp)

private theorem
    Smale.MorsePerturbation.contDiff_coordinateGradient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (coordinateGradient f) :=
  dualEquiv.symm.contDiff.comp (contDiff_fderiv hf)

private theorem Smale.MorsePerturbation.fderiv_linearPerturbation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a x : E) :
    fderiv ℝ (linearPerturbation f a) x = fderiv ℝ f x - dualEquiv a := by
  unfold linearPerturbation
  rw [fderiv_fun_sub (hf.differentiable (by simp) x) (dualEquiv a).differentiableAt,
    ContinuousLinearMap.fderiv]

private theorem
    Smale.MorsePerturbation.hessian_linearPerturbation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a x : E) :
    fderiv ℝ (fderiv ℝ (linearPerturbation f a)) x = fderiv ℝ (fderiv ℝ f) x := by
  have heq : fderiv ℝ (linearPerturbation f a) = fun y => fderiv ℝ f y - dualEquiv a :=
    funext (fderiv_linearPerturbation hf a)
  rw [heq, fderiv_sub_const]

private theorem Smale.MorsePerturbation.fderiv_coordinateGradient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    fderiv ℝ (coordinateGradient f) x =
      dualEquiv.symm.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) x) := by
  exact
    (dualEquiv.symm.hasFDerivAt.comp x
        ((contDiff_fderiv hf).differentiable (by simp) x).hasFDerivAt).fderiv

private theorem Smale.MorsePerturbation.isMorse_of_regularValue {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {a : E}
    (ha : a ∈ Smale.RegularValues.regularValues (coordinateGradient f)) :
    IsMorse (linearPerturbation f a) := by
  intro x hx
  rw [fderiv_linearPerturbation hf a x, sub_eq_zero] at hx
  have hxa : coordinateGradient f x = a := by simp [coordinateGradient, hx]
  have hbij := Smale.RegularValues.bijective_fderiv_of_mem_regularValues ha hxa
  rw [hessian_linearPerturbation hf a x]
  have heq :
    (fun v : E => dualEquiv (fderiv ℝ (coordinateGradient f) x v)) = fderiv ℝ (fderiv ℝ f) x := by
    funext v
    rw [fderiv_coordinateGradient hf x]
    exact dualEquiv.apply_symm_apply _
  rw [← heq]
  exact dualEquiv.bijective.comp hbij

public
theorem Smale.MorsePerturbation.isOpen_forall_mem_compact {P X : Type*} [TopologicalSpace P]
    [TopologicalSpace X] {K : Set X} (hK : IsCompact K) {U : Set (P × X)} (hU : IsOpen U) :
    IsOpen {p : P | ∀ x ∈ K, (p, x) ∈ U} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let B : Set (P × K) := {q | (q.1, (q.2 : X)) ∉ U}
  have hB : IsClosed B :=
    hU.isClosed_compl.preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hproj : IsClosed ((Prod.fst : P × K → P) '' B) := isClosedMap_fst_of_compactSpace B hB
  have heq : {p : P | ∀ x ∈ K, (p, x) ∈ U} = ((Prod.fst : P × K → P) '' B)ᶜ := by
    ext p
    constructor
    · intro hp ⟨⟨q, x⟩, hbad, hq⟩
      change q = p at hq
      subst q
      exact hbad (hp x x.property)
    · intro hp x hx
      by_contra hbad
      exact hp ⟨(p, ⟨x, hx⟩), hbad, rfl⟩
  rw [heq]
  exact hproj.isOpen_compl

private theorem
    Smale.MorsePerturbation.contDiff_spatialDerivative {P E F : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : P → E → F} (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (fun q : P × E => fderiv ℝ (f q.1) q.2) := by
  let g : (P × E) → E → F := fun q x => f q.1 x
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hg.fderiv contDiff_snd (by simp)

private theorem Smale.MorsePerturbation.bijective_hessian_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (A : E →L[ℝ] (E →L[ℝ] ℝ)) :
    Function.Bijective A ↔ (dualEquiv.symm.toContinuousLinearMap.comp A).det ≠ 0 := by
  rw [← Smale.RegularValues.bijective_iff_det_ne_zero]
  constructor
  · intro hA
    exact dualEquiv.symm.bijective.comp hA
  · intro hA
    have heq : (fun x : E => dualEquiv ((dualEquiv.symm.toContinuousLinearMap.comp A) x)) = A := by
      funext x
      exact dualEquiv.apply_symm_apply _
    rw [← heq]
    exact dualEquiv.bijective.comp hA

private theorem Smale.MorsePerturbation.contDiffAt_spatialDerivative {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : P → E → F} {q : P × E}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) q) :
    ContDiffAt ℝ ∞ (fun r : P × E => fderiv ℝ (f r.1) r.2) q := by
  let g : (P × E) → E → F := fun r x => f r.1 x
  have hg : ContDiffAt ℝ ∞ (Function.uncurry g) (q, q.2) :=
    hf.comp (q, q.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact hg.fderiv contDiffAt_snd (by simp)

private theorem Smale.MorsePerturbation.contDiffOn_spatialDerivative {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : P → E → F} {U : Set (P × E)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) U) :
    ContDiffOn ℝ ∞ (fun q : P × E => fderiv ℝ (f q.1) q.2) U := by
  intro q hq
  exact (contDiffAt_spatialDerivative (hf.contDiffAt (hU.mem_nhds hq))).contDiffWithinAt

private theorem Smale.MorsePerturbation.isOpen_goodJetOn {P E : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : P → E → ℝ} {U : Set (P × E)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) U) :
    IsOpen
      {q : P × E |
        q ∈ U ∧
          (fderiv ℝ (f q.1) q.2 ≠ 0 ∨ Function.Bijective (fderiv ℝ (fderiv ℝ (f q.1)) q.2))} := by
  have h₁ := contDiffOn_spatialDerivative hU hf
  have h₂ := contDiffOn_spatialDerivative (f := fun p x => fderiv ℝ (f p) x) hU h₁
  have hd :
    ContinuousOn
      (fun q : P × E =>
        (dualEquiv.symm.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ (f q.1)) q.2)).det)
      U :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_const.clm_comp h₂.continuousOn)
  have ha :=
    h₁.continuousOn.isOpen_inter_preimage hU
      (isClosed_singleton (x := (0 : E →L[ℝ] ℝ))).isOpen_compl
  have hb := hd.isOpen_inter_preimage hU (isClosed_singleton (x := (0 : ℝ))).isOpen_compl
  have heq :
    {q : P × E |
        q ∈ U ∧
          (fderiv ℝ (f q.1) q.2 ≠ 0 ∨ Function.Bijective (fderiv ℝ (fderiv ℝ (f q.1)) q.2))} =
      (U ∩ (fun q : P × E => fderiv ℝ (f q.1) q.2) ⁻¹' {0}ᶜ) ∪
        (U ∩
          (fun q : P × E =>
              (dualEquiv.symm.toContinuousLinearMap.comp
                  (fderiv ℝ (fderiv ℝ (f q.1)) q.2)).det) ⁻¹'
            {0}ᶜ) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_singleton_iff, bijective_hessian_iff]
    exact and_or_left
  rw [heq]
  exact ha.union hb

private def Smale.ManifoldPerturbation.coordinateVector {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {p : M}
    (φ : SmoothBumpFunction 𝓘(ℝ, E) p) (x : M) : E :=
  φ x • extChartAt 𝓘(ℝ, E) p x

private theorem
    Smale.ManifoldPerturbation.contMDiff_coordinateVector {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {p : M} (φ : SmoothBumpFunction 𝓘(ℝ, E) p) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (coordinateVector φ) :=
  φ.contMDiff_smul contMDiffOn_extChartAt

private def
    Smale.ManifoldPerturbation.perturb {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {p : M}
    (φ : SmoothBumpFunction 𝓘(ℝ, E) p) (f : M → ℝ) (a : E) (x : M) : ℝ :=
  f x - Smale.MorsePerturbation.dualEquiv a (coordinateVector φ x)

private theorem Smale.ManifoldPerturbation.contMDiff_perturb {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {p : M} (φ : SmoothBumpFunction 𝓘(ℝ, E) p) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (fun q : E × M => perturb φ f q.1 q.2) :=
  (hf.comp contMDiff_snd).sub
    ((Smale.MorsePerturbation.dualEquiv.contDiff.contMDiff.comp contMDiff_fst).clm_apply
      ((contMDiff_coordinateVector φ).comp contMDiff_snd))

@[simp]
private theorem Smale.ManifoldPerturbation.perturb_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {p : M}
    (φ : SmoothBumpFunction 𝓘(ℝ, E) p) (f : M → ℝ) : perturb φ f 0 = f := by
  funext x
  simp [perturb]

private def
    Smale.ManifoldMorse.IsMorseAt (E : Type*) {M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (x : M) : Prop :=
  ∃ e : OpenPartialHomeomorph M E,
    e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      x ∈ e.source ∧
        (fderiv ℝ (f ∘ e.symm) (e x) ≠ 0 ∨
          Function.Bijective (fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e x)))

private def
    Smale.ManifoldMorse.IsMorseOn (E : Type*) {M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (K : Set M) : Prop :=
  ∀ x ∈ K, IsMorseAt E f x

private def
    Smale.ManifoldMorse.IsMorse (E : Type*) {M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) : Prop :=
  ∀ x, IsMorseAt E f x

private theorem Smale.ManifoldMorse.IsMorseOn.union {E : Type*} {M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {K L : Set M}
    (hK : Smale.ManifoldMorse.IsMorseOn E f K) (hL : Smale.ManifoldMorse.IsMorseOn E f L) :
    Smale.ManifoldMorse.IsMorseOn E f (K ∪ L) := by
  intro x hx
  rcases hx with hx | hx
  · exact hK x hx
  · exact hL x hx

private theorem Smale.ManifoldMorse.contDiffOn_chartExpression {E : Type*} {M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) : ContDiffOn ℝ ∞ (f ∘ e.symm) e.target :=
  (hf.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn

private theorem Smale.ManifoldMorse.isMorseAt_of_chart_eventuallyEq {E : Type*} {M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {g : E → ℝ} {x : M} {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hx : x ∈ e.source)
    (hg : Smale.MorsePerturbation.IsMorse g) (heq : f ∘ e.symm =ᶠ[𝓝 (e x)] g) : IsMorseAt E f x :=
  by
  refine ⟨e, he, hx, ?_⟩
  by_cases hc : fderiv ℝ (f ∘ e.symm) (e x) = 0
  · right
    rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq]
    exact hg (e x) ((heq.fderiv_eq (𝕜 := ℝ)).symm.trans hc)
  · exact Or.inl hc

private theorem
    Smale.ManifoldMorse.contDiffOn_inChart {E : Type*} {M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f))
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    ContDiffOn ℝ ∞ (fun q : P × E => f q.1 (e.symm q.2)) {q : P × E | q.2 ∈ e.target} := by
  intro q hq
  have hi := contMDiffAt_symm_of_mem_maximalAtlas he hq
  have hmap :
    ContMDiffAt 𝓘(ℝ, P × E) (𝓘(ℝ, P).prod 𝓘(ℝ, E)) ∞ (fun r : P × E => (r.1, e.symm r.2)) q :=
    contDiffAt_fst.contMDiffAt.prodMk (hi.comp q contDiffAt_snd.contMDiffAt)
  exact (hf.contMDiffAt.comp q hmap).contDiffAt.contDiffWithinAt

private theorem
    Smale.ManifoldMorse.isOpen_morseInChart {E : Type*} {M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f))
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    IsOpen
      {q : P × M |
        q.2 ∈ e.source ∧
          (fderiv ℝ (f q.1 ∘ e.symm) (e q.2) ≠ 0 ∨
            Function.Bijective (fderiv ℝ (fderiv ℝ (f q.1 ∘ e.symm)) (e q.2)))} := by
  have hg :=
    Smale.MorsePerturbation.isOpen_goodJetOn (f := fun a y => f a (e.symm y))
      (e.open_target.preimage (continuous_snd : Continuous (Prod.snd : P × E → E)))
      (contDiffOn_inChart hf he)
  let S : Set (P × M) := {q | q.2 ∈ e.source}
  have hS : IsOpen S := e.open_source.preimage continuous_snd
  have hm : ContinuousOn (fun q : P × M => (q.1, e q.2)) S :=
    continuous_fst.continuousOn.prodMk
      (e.continuousOn.comp continuous_snd.continuousOn (fun _ hq => hq))
  convert hm.isOpen_inter_preimage hS hg using 1
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, S]
  constructor
  · rintro ⟨hq, hg⟩
    exact ⟨hq, e.map_source hq, hg⟩
  · rintro ⟨hq, -, hg⟩
    exact ⟨hq, hg⟩

private theorem Smale.ManifoldMorse.isOpen_isMorseAt {E : Type*} {M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) :
    IsOpen {q : P × M | IsMorseAt E (f q.1) q.2} := by
  have heq :
    {q : P × M | IsMorseAt E (f q.1) q.2} =
      ⋃ (e : OpenPartialHomeomorph M E) (_ : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M),
        {q : P × M |
          q.2 ∈ e.source ∧
            (fderiv ℝ (f q.1 ∘ e.symm) (e q.2) ≠ 0 ∨
              Function.Bijective (fderiv ℝ (fderiv ℝ (f q.1 ∘ e.symm)) (e q.2)))} := by
    ext q
    simp only [Set.mem_ofPred_eq, IsMorseAt, Set.mem_iUnion, exists_prop]
  rw [heq]
  exact isOpen_iUnion fun e => isOpen_iUnion fun he => isOpen_morseInChart hf he

private theorem Smale.ManifoldMorse.isOpen_isMorseOn {E : Type*} {M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) {K : Set M}
    (hK : IsCompact K) : IsOpen {p : P | IsMorseOn E (f p) K} :=
  Smale.MorsePerturbation.isOpen_forall_mem_compact hK (isOpen_isMorseAt hf)

private def
    Smale.MorsePerturbation.hessianEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (x : E)
    (h : Function.Bijective (fderiv ℝ (fderiv ℝ f) x)) : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
  (LinearEquiv.ofBijective (fderiv ℝ (fderiv ℝ f) x).toLinearMap h).toContinuousLinearEquiv

@[simp]
private theorem Smale.MorsePerturbation.hessianEquiv_toContinuousLinearMap {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : E → ℝ) (x : E)
    (h : Function.Bijective (fderiv ℝ (fderiv ℝ f) x)) :
    (hessianEquiv f x h).toContinuousLinearMap = fderiv ℝ (fderiv ℝ f) x := by
  ext v w
  rfl

private def Smale.ManifoldMorse.criticalPoints {M : Type*} [TopologicalSpace M] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E M] (f : M → ℝ) : Set M :=
  {x | mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0}

private theorem Smale.ManifoldMorse.mem_criticalPoints_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : M} (hx : x ∈ e.source) :
    x ∈ criticalPoints E f ↔ fderiv ℝ (f ∘ e.symm) (e x) = 0 := by
  have he' : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  have hcomp :
    fderiv ℝ (f ∘ e.symm) (e x) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)) := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp (e x) (hf.mdifferentiableAt (by simp))
        (he'.mdifferentiableAt_symm (e.map_source hx))]
    rw [e.left_inv hx]
  rw [hcomp]
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0 ↔ _
  constructor
  · intro h
    rw [h]
    ext v
    rfl
  · intro h
    ext v
    obtain ⟨w, hw⟩ := he'.symm.mfderiv_surjective (e.map_source hx) v
    have hh := congrArg (fun A : E →L[ℝ] ℝ => A w) h
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)) w) = 0 at hh
    rw [hw] at hh
    exact hh

private theorem Smale.ManifoldMorse.criticalPoints_isClosed {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) : IsClosed (criticalPoints E f) := by
  apply isOpen_compl_iff.mp
  rw [isOpen_iff_mem_nhds]
  intro x hx
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hxS : x ∈ e.source := mem_chart_source E x
  have hd := (contDiffOn_chartExpression hf he).fderiv_of_isOpen e.open_target (m := ∞) (by simp)
  let V : Set E := e.target ∩ (fderiv ℝ (f ∘ e.symm)) ⁻¹' {0}ᶜ
  have hV : IsOpen V :=
    hd.continuousOn.isOpen_inter_preimage e.open_target
      (isClosed_singleton (x := (0 : E →L[ℝ] ℝ))).isOpen_compl
  have hU := e.continuousOn.isOpen_inter_preimage e.open_source hV
  have hxU : x ∈ e.source ∩ e ⁻¹' V :=
    ⟨hxS, e.map_source hxS, fun h => hx ((mem_criticalPoints_iff hf he hxS).mpr h)⟩
  apply Filter.mem_of_superset (hU.mem_nhds hxU)
  intro y hy hc
  exact hy.2.2 ((mem_criticalPoints_iff hf he hy.1).mp hc)

private theorem Smale.ManifoldMorse.criticalPoints_isDiscrete {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) : IsDiscrete (criticalPoints E f) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨e, he, hxS, hreg | hH⟩ := hm x
  · exact False.elim (hreg ((mem_criticalPoints_iff hf he hxS).mp hx))
  · have hc : fderiv ℝ (f ∘ e.symm) (e x) = 0 := (mem_criticalPoints_iff hf he hxS).mp hx
    have hloc :=
      (contDiffOn_chartExpression hf he).contDiffAt (e.open_target.mem_nhds (e.map_source hxS))
    have hdf := hloc.fderiv_right (m := ∞) (by simp)
    let L := Smale.MorsePerturbation.hessianEquiv (f ∘ e.symm) (e x) hH
    have hL : HasFDerivAt (fderiv ℝ (f ∘ e.symm)) L.toContinuousLinearMap (e x) := by
      rw [show L.toContinuousLinearMap = fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e x) from
          Smale.MorsePerturbation.hessianEquiv_toContinuousLinearMap _ _ hH]
      exact (hdf.differentiableAt (by simp)).hasFDerivAt
    let d := hdf.toOpenPartialHomeomorph (fderiv ℝ (f ∘ e.symm)) hL (by simp)
    have hd : e x ∈ d.source := hdf.mem_toOpenPartialHomeomorph_source hL (by simp)
    let U := e.source ∩ e ⁻¹' d.source
    have hU : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source d.open_source
    refine ⟨U, hU, ?_⟩
    ext y
    constructor
    · rintro ⟨hy, hyc⟩
      apply Set.mem_singleton_iff.mpr
      apply e.injOn hy.1 hxS
      apply d.injOn hy.2 hd
      exact ((mem_criticalPoints_iff hf he hy.1).mp hyc).trans hc.symm
    · intro hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact ⟨⟨hxS, hd⟩, hx⟩

private theorem Smale.ManifoldMorse.finite_criticalPoints {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) : (criticalPoints E f).Finite :=
  (criticalPoints_isClosed hf).isCompact.finite (criticalPoints_isDiscrete hf hm)

private def
    Smale.FlowConstruction.chartDirection {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (e : OpenPartialHomeomorph M E) (w : E) :
    (x : M) → TangentSpace 𝓘(ℝ, E) x :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e (fun y => (NormedSpace.fromTangentSpace y).symm w)

private theorem
    Smale.FlowConstruction.contMDiffOn_chartDirection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (w : E) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, chartDirection e w x⟩ : TangentBundle 𝓘(ℝ, E) M)) e.source := by
  have hW :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun y : E => (⟨y, (NormedSpace.fromTangentSpace y).symm w⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have he' : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  intro x hx
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x).IsInvertible := ⟨he'.mfderiv hx, rfl⟩
  exact
    ((hW (e x)).mpullback_vectorField_preimage (contMDiffAt_of_mem_maximalAtlas he hx) hinv
        (by simp)).contMDiffWithinAt

private theorem Smale.FlowConstruction.mvfderiv_chartDirection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (w : E) {x : M} (hx : x ∈ e.source) :
    mvfderiv 𝓘(ℝ, E) f x (chartDirection e w x) = fderiv ℝ (f ∘ e.symm) (e x) w := by
  have he' : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  have h₁ := he'.comp_symm_deriv (e.map_source hx)
  rw [e.left_inv hx] at h₁
  have hi := ContinuousLinearMap.inverse_eq h₁ (he'.symm_comp_deriv hx)
  have hc :
    fderiv ℝ (f ∘ e.symm) (e x) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)) := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp (e x) (hf.mdifferentiableAt (by simp))
        (he'.mdifferentiableAt_symm (e.map_source hx))]
    rw [e.left_inv hx]
  unfold chartDirection
  rw [VectorField.mpullback_apply, hi]
  exact (congrArg (fun A : E →L[ℝ] ℝ => A w) hc).symm

private theorem Smale.FlowConstruction.exists_unitSpeedField_near_regular {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {p : M} (hp : p ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ U : Set M,
      IsOpen U ∧
        p ∈ U ∧
          ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
            ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) U ∧
              ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) f x (V x) = 1 := by
  classical
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hpS : p ∈ e.source := mem_chart_source E p
  have hdf : fderiv ℝ (f ∘ e.symm) (e p) ≠ 0 := fun h =>
    hp ((Smale.ManifoldMorse.mem_criticalPoints_iff hf he hpS).mpr h)
  have hw : ∃ w : E, fderiv ℝ (f ∘ e.symm) (e p) w ≠ 0 := by
    by_contra! h
    exact hdf (ContinuousLinearMap.ext h)
  obtain ⟨w, hw⟩ := hw
  let D : M → ℝ := fun x => fderiv ℝ (f ∘ e.symm) (e x) w
  have hder :=
    (Smale.ManifoldMorse.contDiffOn_chartExpression hf he).fderiv_of_isOpen e.open_target (m := ∞)
      (by simp)
  have hD : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ D e.source :=
    (hder.clm_apply contDiffOn_const).contMDiffOn.comp (contMDiffOn_of_mem_maximalAtlas he)
      (fun _ hx => e.map_source hx)
  let U : Set M := e.source ∩ D ⁻¹' {0}ᶜ
  have hU : IsOpen U :=
    hD.continuousOn.isOpen_inter_preimage e.open_source
      (isClosed_singleton (x := (0 : ℝ))).isOpen_compl
  let V : (x : M) → TangentSpace 𝓘(ℝ, E) x := fun x => (D x)⁻¹ • chartDirection e w x
  refine ⟨U, hU, ⟨hpS, hw⟩, V, ?_, ?_⟩
  · exact
      ((hD.mono Set.inter_subset_left).inv₀ (fun _ hx => hx.2)).smul_section
        ((contMDiffOn_chartDirection he w).mono Set.inter_subset_left)
  · intro x hx
    change mvfderiv 𝓘(ℝ, E) f x ((D x)⁻¹ • chartDirection e w x) = 1
    rw [map_smul, smul_eq_mul, mvfderiv_chartDirection hf he w hx.1]
    exact inv_mul_cancel₀ hx.2

private theorem Smale.FlowConstruction.exists_prescribedDerivativeField {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M] {f χ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ)
    (hsupp : tsupport χ ⊆ (Smale.ManifoldMorse.criticalPoints E f)ᶜ) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        ∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) = χ x := by
  let C : (x : M) → Set (TangentSpace 𝓘(ℝ, E) x) := fun x => {w | mvfderiv 𝓘(ℝ, E) f x w = χ x}
  have hC (x : M) : Convex ℝ (C x) :=
    (convex_singleton (χ x)).linear_preimage (mvfderiv 𝓘(ℝ, E) f x).toLinearMap
  have hlocal :
    ∀ p : M,
      ∃ U ∈ 𝓝 p,
        ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
          ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))
              U ∧
            ∀ x ∈ U, V x ∈ C x := by
    intro p
    by_cases hp : p ∉ Smale.ManifoldMorse.criticalPoints E f
    · obtain ⟨U, hU, hpU, V, hV, hVunit⟩ := exists_unitSpeedField_near_regular hf hp
      refine ⟨U, hU.mem_nhds hpU, (fun x => χ x • V x), hχ.contMDiffOn.smul_section hV, ?_⟩
      intro x hx
      change mvfderiv 𝓘(ℝ, E) f x (χ x • V x) = χ x
      rw [map_smul, hVunit x hx, smul_eq_mul, mul_one]
    · have hps : p ∉ tsupport χ := fun h => hp (hsupp h)
      refine
        ⟨(tsupport χ)ᶜ, (isClosed_tsupport χ).isOpen_compl.mem_nhds hps, (fun _ => 0),
          (Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, E))).contMDiffOn, ?_⟩
      intro x hx
      change mvfderiv 𝓘(ℝ, E) f x 0 = χ x
      rw [map_zero, image_eq_zero_of_notMem_tsupport hx]
  obtain ⟨V, hV⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local (n := ⊤) 𝓘(ℝ, E)
      (TangentSpace 𝓘(ℝ, E) (M := M)) C hC hlocal
  exact ⟨V, V.contMDiff, hV⟩

private theorem Smale.FlowConstruction.exists_gluedDescentField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {ι : Type*} [Finite ι] (U K : ι → Set M)
    (hU : ∀ i, IsOpen (U i)) (hK : ∀ i, IsClosed (K i)) (hKU : ∀ i, K i ⊆ U i)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcover : Smale.ManifoldMorse.criticalPoints E f ⊆ ⋃ i, K i)
    (Vloc : ι → (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hVloc :
      ∀ i,
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, Vloc i x⟩ : TangentBundle 𝓘(ℝ, E) M)) (U i))
    (hdesc :
      ∀ i x,
        x ∈ U i →
          x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (Vloc i x) < 0) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
          ∀ i x, x ∈ K i → V x = Vloc i x := by
  let C : (x : M) → Set (TangentSpace 𝓘(ℝ, E) x) := fun x =>
    {w |
      (x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x w < 0) ∧
        ∀ i, x ∈ K i → w = Vloc i x}
  have hC (x : M) : Convex ℝ (C x) := by
    intro u hu v hv a b ha hb hab
    refine ⟨?_, ?_⟩
    · intro hreg
      have h := (convex_Iio (0 : ℝ)) (hu.1 hreg) (hv.1 hreg) ha hb hab
      simpa only [map_add, map_smul, smul_eq_mul, Set.mem_Iio] using h
    · intro i hxi
      rw [hu.2 i hxi, hv.2 i hxi, ← add_smul, hab, one_smul]
  have hclosed : IsClosed (⋃ i, K i) := isClosed_iUnion_of_finite hK
  have hlocal :
    ∀ p : M,
      ∃ W ∈ 𝓝 p,
        ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
          ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))
              W ∧
            ∀ x ∈ W, V x ∈ C x := by
    intro p
    by_cases hp : p ∈ ⋃ i, K i
    · obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
      refine ⟨U i, (hU i).mem_nhds (hKU i hpi), Vloc i, hVloc i, ?_⟩
      intro x hx
      refine ⟨hdesc i x hx, ?_⟩
      intro j hxj
      by_cases hij : i = j
      · subst j
        rfl
      · exact False.elim (Set.disjoint_left.mp (hdisj hij) hx (hKU j hxj))
    · have hpreg : p ∉ Smale.ManifoldMorse.criticalPoints E f := fun h => hp (hcover h)
      obtain ⟨W, hW, hpW, V, hV, hVf⟩ := exists_unitSpeedField_near_regular hf hpreg
      refine
        ⟨W ∩ (⋃ i, K i)ᶜ, (hW.inter hclosed.isOpen_compl).mem_nhds ⟨hpW, hp⟩, (fun x => -(V x)),
          hV.neg_section.mono Set.inter_subset_left, ?_⟩
      intro x hx
      refine ⟨?_, ?_⟩
      · intro _
        change mvfderiv 𝓘(ℝ, E) f x (-V x) < 0
        rw [map_neg, hVf x hx.1]
        norm_num
      · intro i hxi
        exact False.elim (hx.2 (Set.mem_iUnion.mpr ⟨i, hxi⟩))
  obtain ⟨V, hV⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local (n := ⊤) 𝓘(ℝ, E)
      (TangentSpace 𝓘(ℝ, E) (M := M)) C hC hlocal
  exact ⟨V, V.contMDiff, fun x => (hV x).1, fun i x hx => (hV x).2 i hx⟩

private theorem MorseCancel.exists_closed_patch_descent_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M] {f : M → ℝ}
    (V₀ : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV₀ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V₀ x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero₀ : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V₀ x = 0)
    (hdesc₀ : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V₀ x) < 0)
    {ι : Type*} [Finite ι] (K U : ι → Set M) (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i) (hdisj : Pairwise (fun i j => Disjoint (K i) (K j)))
    (Vloc : ι → (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hVloc :
      ∀ i,
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, Vloc i x⟩ : TangentBundle 𝓘(ℝ, E) M)) (U i))
    (hzero : ∀ i x, x ∈ U i → x ∈ Smale.ManifoldMorse.criticalPoints E f → Vloc i x = 0)
    (hdesc :
      ∀ i x,
        x ∈ U i →
          x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (Vloc i x) < 0) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0) ∧
          (∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
            ∀ i x, x ∈ K i → V x = Vloc i x := by
  classical
  let C : (x : M) → Set (TangentSpace 𝓘(ℝ, E) x) := fun x =>
    {w |
      (x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x w < 0) ∧
        (x ∈ Smale.ManifoldMorse.criticalPoints E f → w = 0) ∧ ∀ i, x ∈ K i → w = Vloc i x}
  have hC (x : M) : Convex ℝ (C x) := by
    intro u hu v hv a b ha hb hab
    refine ⟨?_, ?_, ?_⟩
    · intro hreg
      have h := (convex_Iio (0 : ℝ)) (hu.1 hreg) (hv.1 hreg) ha hb hab
      simpa only [map_add, map_smul, smul_eq_mul, Set.mem_Iio] using h
    · intro hcrit
      rw [hu.2.1 hcrit, hv.2.1 hcrit, smul_zero, smul_zero, add_zero]
    · intro i hxi
      rw [hu.2.2 i hxi, hv.2.2 i hxi, ← add_smul, hab, one_smul]
  have hclosed : IsClosed (⋃ i, K i) := isClosed_iUnion_of_finite hK
  have hlocal :
    ∀ p : M,
      ∃ O ∈ 𝓝 p,
        ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
          ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))
              O ∧
            ∀ x ∈ O, V x ∈ C x := by
    intro p
    by_cases hp : p ∈ ⋃ i, K i
    · obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
      let R := ⋃ j : { j : ι // j ≠ i }, K j
      have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hK j)
      have hpR : p ∉ R := by
        intro hpR
        obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hpR
        exact Set.disjoint_left.mp (hdisj (fun h => j.property h.symm)) hpi hpj
      refine
        ⟨U i ∩ Rᶜ, ((hU i).inter hR.isOpen_compl).mem_nhds ⟨hKU i hpi, hpR⟩, Vloc i,
          (hVloc i).mono Set.inter_subset_left, ?_⟩
      intro x hx
      refine ⟨hdesc i x hx.1, hzero i x hx.1, ?_⟩
      intro j hxj
      by_cases hij : i = j
      · subst j
        rfl
      · exact False.elim (hx.2 (Set.mem_iUnion.mpr ⟨⟨j, fun h => hij h.symm⟩, hxj⟩))
    · refine ⟨(⋃ i, K i)ᶜ, hclosed.isOpen_compl.mem_nhds hp, V₀, hV₀.contMDiffOn, ?_⟩
      intro x hx
      refine ⟨hdesc₀ x, hzero₀ x, ?_⟩
      intro i hxi
      exact False.elim (hx (Set.mem_iUnion.mpr ⟨i, hxi⟩))
  obtain ⟨V, hV⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local (n := ⊤) 𝓘(ℝ, E)
      (TangentSpace 𝓘(ℝ, E) (M := M)) C hC hlocal
  exact ⟨V, V.contMDiff, fun x => (hV x).2.1, fun x => (hV x).1, fun i x hx => (hV x).2.2 i hx⟩

private def Smale.FlowConstruction.partialChartField {E F M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞) (W : F → F) :
    (x : M) → TangentSpace 𝓘(ℝ, E) x :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F) e (fun y => (NormedSpace.fromTangentSpace y).symm (W y))

private theorem Smale.FlowConstruction.contMDiffOn_partialChartField {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [CompleteSpace E] [IsManifold 𝓘(ℝ, E) ∞ M]
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞) {W : F → F} (hW : ContDiff ℝ ∞ W) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, partialChartField e W x⟩ : TangentBundle 𝓘(ℝ, E) M)) e.source := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hW' :
    ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, F).tangent) ∞
      (fun y : F =>
        (⟨y, (NormedSpace.fromTangentSpace y).symm (W y)⟩ : TangentBundle 𝓘(ℝ, F) F)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hW
  intro x hx
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x).IsInvertible := ⟨he.mfderiv hx, rfl⟩
  exact
    ((hW' (e x)).mpullback_vectorField_preimage
        ((e.contMDiffOn x hx).contMDiffAt (e.open_source.mem_nhds hx)) hinv
        (by simp)).contMDiffWithinAt

private theorem
    Smale.FlowConstruction.mvfderiv_partialChartField {E F M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞) (W : F → F) {x : M} (hx : x ∈ e.source) :
    mvfderiv 𝓘(ℝ, E) f x (partialChartField e W x) = fderiv ℝ (f ∘ e.symm) (e x) (W (e x)) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have h₁ := he.comp_symm_deriv (e'.map_source hx)
  rw [e'.left_inv hx] at h₁
  have hi := ContinuousLinearMap.inverse_eq h₁ (he.symm_comp_deriv hx)
  have hc :
    fderiv ℝ (f ∘ e'.symm) (e' x) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x).comp (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e'.symm (e' x)) := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp (e' x) (hf.mdifferentiableAt (by simp))
        (he.mdifferentiableAt_symm (e'.map_source hx))]
    rw [e'.left_inv hx]
  unfold partialChartField
  rw [VectorField.mpullback_apply]
  change
    mvfderiv 𝓘(ℝ, E) f x
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e' x).inverse
          ((NormedSpace.fromTangentSpace (e' x)).symm (W (e' x)))) =
      _
  rw [hi]
  exact (congrArg (fun A : F →L[ℝ] ℝ => A (W (e' x))) hc).symm

private theorem Smale.ManifoldMorse.exists_compact_plateau {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] (p : M) :
    ∃ (φ : SmoothBumpFunction 𝓘(ℝ, E) p) (U L : Set M),
      IsOpen U ∧
        U ⊆ (chartAt E p).source ∧ Set.EqOn φ (fun _ => 1) U ∧ IsCompact L ∧ L ∈ 𝓝 p ∧ L ⊆ U := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let φ : SmoothBumpFunction 𝓘(ℝ, E) p := Classical.choice inferInstance
  have hN : {x : M | φ x = 1} ∩ (chartAt E p).source ∈ 𝓝 p :=
    Filter.inter_mem φ.eventuallyEq_one
      ((chartAt E p).open_source.mem_nhds (mem_chart_source E p))
  obtain ⟨U, hUN, hU, hpU⟩ := mem_nhds_iff.mp hN
  obtain ⟨L, hpL, hLU, hL⟩ := local_compact_nhds (hU.mem_nhds hpU)
  exact ⟨φ, U, L, hU, fun x hx => (hUN hx).2, fun x hx => (hUN hx).1, hL, hpL, hLU⟩

private theorem
    Smale.ManifoldMorse.perturb_inChart_eventuallyEq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {p : M}
    (φ : SmoothBumpFunction 𝓘(ℝ, E) p) {f : M → ℝ} {G : E → ℝ} {U : Set M} {V : Set E}
    (hU : IsOpen U) (hUs : U ⊆ (chartAt E p).source) (hφ : Set.EqOn φ (fun _ => 1) U)
    (hV : IsOpen V) (hG : Set.EqOn G (f ∘ (chartAt E p).symm) V) (a : E) {x : M} (hx : x ∈ U)
    (hxV : chartAt E p x ∈ V) :
    Smale.ManifoldPerturbation.perturb φ f a ∘ (chartAt E p).symm =ᶠ[𝓝 (chartAt E p x)]
      Smale.MorsePerturbation.linearPerturbation G a := by
  let e := chartAt E p
  have hxt : e x ∈ e.target := e.map_source (hUs hx)
  have hi : ContinuousAt e.symm (e x) := e.symm.continuousAt hxt
  have hpre : e.symm ⁻¹' U ∈ 𝓝 (e x) := by
    apply hi.preimage_mem_nhds
    simpa only [e.left_inv (hUs hx)] using hU.mem_nhds hx
  filter_upwards [hpre, e.open_target.mem_nhds hxt, hV.mem_nhds hxV] with y hyU hyt hyV
  have hφy := hφ hyU
  have hGy := hG hyV
  change G y = f (e.symm y) at hGy
  change
    f (e.symm y) -
        Smale.MorsePerturbation.dualEquiv a (φ (e.symm y) • extChartAt 𝓘(ℝ, E) p (e.symm y)) =
      G y - Smale.MorsePerturbation.dualEquiv a y
  rw [hφy, one_smul, ← hGy]
  congr 2
  simpa only [extChartAt_coe, Function.comp_apply, modelWithCornersSelf_coe, id_eq] using
    e.right_inv hyt

private theorem Smale.ManifoldMorse.exists_morse_extension {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {p : M} (φ : SmoothBumpFunction 𝓘(ℝ, E) p)
    {U L K : Set M} (hU : IsOpen U) (hUs : U ⊆ (chartAt E p).source)
    (hφ : Set.EqOn φ (fun _ => 1) U) (hL : IsCompact L) (hLU : L ⊆ U) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hK : IsCompact K) (hfK : IsMorseOn E f K) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ a : E,
      ‖a‖ < ε ∧
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (Smale.ManifoldPerturbation.perturb φ f a) ∧
          IsMorseOn E (Smale.ManifoldPerturbation.perturb φ f a) (L ∪ K) := by
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hLc : IsCompact (e '' L) := hL.image_of_continuousOn (e.continuousOn.mono (hLU.trans hUs))
  have hLt : e '' L ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hUs (hLU hx))
  obtain ⟨G, hG, V, hV, hLV, -, hGV⟩ :=
    LineBundleTransport.exists_smooth_extension_near_closed hLc.isClosed e.open_target hLt
      (contDiffOn_chartExpression hf he)
  have hfamily := Smale.ManifoldPerturbation.contMDiff_perturb φ hf
  let A : Set E := {a | IsMorseOn E (Smale.ManifoldPerturbation.perturb φ f a) K}
  have hA : IsOpen A := isOpen_isMorseOn (f := Smale.ManifoldPerturbation.perturb φ f) hfamily hK
  have hA₀ : (0 : E) ∈ A := by simpa [A] using hfK
  have hd :=
    Smale.RegularValues.dense_regularValues μ
      ((Smale.MorsePerturbation.contDiff_coordinateGradient hG).differentiable (by simp))
  obtain ⟨a, ha, haA, haε⟩ :=
    hd.exists_mem_open (hA.inter Metric.isOpen_ball) ⟨0, hA₀, Metric.mem_ball_self hε⟩
  refine ⟨a, mem_ball_zero_iff.mp haε, ?_, ?_⟩
  · exact hfamily.comp (contMDiff_const.prodMk contMDiff_id)
  · refine IsMorseOn.union ?_ haA
    intro x hx
    apply
      isMorseAt_of_chart_eventuallyEq he (hUs (hLU hx))
        (Smale.MorsePerturbation.isMorse_of_regularValue hG ha)
    exact
      perturb_inChart_eventuallyEq φ hU hUs hφ hV hGV a (hLU hx) (hLV (Set.mem_image_of_mem e hx))

private theorem
    Smale.ManifoldMorse.exists_morse_function_of_haar {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ] :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f := by
  classical
  choose φ U L hU hUs hφ hL hn hLU using exists_compact_plateau (E := E) (M := M)
  obtain ⟨s, hs⟩ := finite_cover_nhds hn
  have hfinite :
    ∀ t : Finset M, ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorseOn E f (⋃ p ∈ t, L p) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => 0, contMDiff_const, ?_⟩
      intro x hx
      simp at hx
    | @insert p t hp ih =>
      obtain ⟨f, hf, hm⟩ := ih
      have hK : IsCompact (⋃ q ∈ t, L q) := t.isCompact_biUnion (fun q _ => hL q)
      obtain ⟨a, -, hfa, hma⟩ :=
        exists_morse_extension μ (φ p) (hU p) (hUs p) (hφ p) (hL p) (hLU p) hf hK hm (ε := 1)
          zero_lt_one
      refine ⟨Smale.ManifoldPerturbation.perturb (φ p) f a, hfa, ?_⟩
      have heq : (⋃ q ∈ Insert.insert p t, L q) = L p ∪ ⋃ q ∈ t, L q := by
        ext x
        simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
        constructor
        · rintro ⟨q, hq | hq, hx⟩
          · subst q
            exact Or.inl hx
          · exact Or.inr ⟨q, hq, hx⟩
        · rintro (hx | ⟨q, hq, hx⟩)
          · exact ⟨p, Or.inl rfl, hx⟩
          · exact ⟨q, Or.inr hq, hx⟩
      rw [heq]
      exact hma
  obtain ⟨f, hf, hm⟩ := hfinite s
  refine ⟨f, hf, fun x => hm x ?_⟩
  rw [hs]
  exact Set.mem_univ x

private theorem
    Smale.ManifoldMorse.exists_morse_function (E : Type*) (M : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  exact exists_morse_function_of_haar (E := E) (M := M) MeasureTheory.Measure.addHaar

private theorem SmoothMorseLemma.contDiff_parametric_intervalIntegral_of_le {P F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : P × ℝ → F) (hG : ContDiff ℝ ∞ G) (a b : ℝ) (hab : a ≤ b) :
    ContDiff ℝ ∞ (fun p => ∫ t in a..b, G (p, t)) := by
  obtain ⟨χ, hχ, hχc, hχone⟩ := LineBundleTransport.exists_interval_cutoff a b
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.MeasureSpace.volume.restrict (Set.Ioc a b)
  let L : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ
  let g : P → ℝ → F := fun p t => χ (-t) • G (p, -t)
  have hg : ContDiff ℝ ∞ (fun q : P × ℝ => g q.1 q.2) :=
    (hχ.comp contDiff_snd.neg).smul (hG.comp (contDiff_fst.prodMk contDiff_snd.neg))
  have hk : IsCompact (-tsupport χ) := hχc.isCompact.neg
  have hgs : ∀ p t, p ∈ (Set.univ : Set P) → t ∉ -tsupport χ → g p t = 0 := by
    intro p t _ ht
    have ht' : -t ∉ tsupport χ := by simpa using ht
    change χ (-t) • G (p, -t) = 0
    rw [image_eq_zero_of_notMem_tsupport ht', zero_smul]
  have hf : MeasureTheory.LocallyIntegrable (fun _ : ℝ => (1 : ℝ)) μ :=
    MeasureTheory.locallyIntegrable_const _
  have hc :=
    MeasureTheory.contDiffOn_convolution_right_with_param_comp (μ := μ) (n := (⊤ : ℕ∞)) L (v :=
      fun _ : P => (0 : ℝ)) contDiffOn_const isOpen_univ hk hgs hf hg.contDiffOn
  have heq (p : P) : ((fun _ : ℝ => (1 : ℝ)) ⋆[L, μ] g p) 0 = ∫ t in a..b, G (p, t) := by
    rw [intervalIntegral.integral_of_le hab]
    change (∫ t, (1 : ℝ) • (χ (-(0 - t)) • G (p, -(0 - t))) ∂μ) = ∫ t in Set.Ioc a b, G (p, t)
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have hχt : χ t = 1 := hχone (Set.mem_uIcc_of_le ht.1.le ht.2)
    simp only [zero_sub, neg_neg, hχt, one_smul]
  have hfun :
    (fun p => ((fun _ : ℝ => (1 : ℝ)) ⋆[L, μ] g p) 0) = (fun p => ∫ t in a..b, G (p, t)) :=
    funext heq
  rw [← hfun]
  exact contDiffOn_univ.mp hc

private theorem
    SmoothMorseLemma.contDiff_parametric_intervalIntegral {P F : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F] (G : P × ℝ → F)
    (hG : ContDiff ℝ ∞ G) (a b : ℝ) : ContDiff ℝ ∞ (fun p => ∫ t in a..b, G (p, t)) := by
  rcases le_total a b with hab | hba
  · exact contDiff_parametric_intervalIntegral_of_le G hG a b hab
  · have he : (fun p => ∫ t in a..b, G (p, t)) = (fun p => -(∫ t in b..a, G (p, t))) :=
      funext fun _ => intervalIntegral.integral_symm b a
    rw [he]
    exact (contDiff_parametric_intervalIntegral_of_le G hG b a hba).neg

private def
    SmoothMorseLemma.taylorHessianIntegrand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (q : E × ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (1 - q.2) • fderiv ℝ (fderiv ℝ f) (q.2 • q.1)

private def SmoothMorseLemma.secondTaylorFactor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (2 : ℝ) • ∫ t in (0 : ℝ)..1, taylorHessianIntegrand f (x, t)

private theorem SmoothMorseLemma.contDiff_taylorHessianIntegrand {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (taylorHessianIntegrand f) := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) := .of_norm_smul_le (fun c B => norm_smul_le c B)
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  have hH : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := (contDiff_infty_iff_fderiv.mp hdf).2
  exact (contDiff_const.sub contDiff_snd).smul (hH.comp (contDiff_snd.smul contDiff_fst))

private theorem SmoothMorseLemma.contDiff_secondTaylorFactor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (secondTaylorFactor f) :=
  (contDiff_parametric_intervalIntegral (taylorHessianIntegrand f)
        (contDiff_taylorHessianIntegrand hf) 0 1).const_smul
    (2 : ℝ)

private theorem SmoothMorseLemma.secondTaylorFactor_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x u v : E) :
    secondTaylorFactor f x u v =
      2 * ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) u v := by
  have hc : Continuous (fun t : ℝ => taylorHessianIntegrand f (x, t)) :=
    (contDiff_taylorHessianIntegrand hf).continuous.comp (continuous_const.prodMk continuous_id)
  have hi :
    IntervalIntegrable (fun t : ℝ => taylorHessianIntegrand f (x, t))
      MeasureTheory.MeasureSpace.volume 0 1 :=
    hc.intervalIntegrable 0 1
  have hiu :
    IntervalIntegrable (fun t : ℝ => taylorHessianIntegrand f (x, t) u)
      MeasureTheory.MeasureSpace.volume 0 1 :=
    (hc.clm_apply continuous_const).intervalIntegrable 0 1
  simp only [secondTaylorFactor, smul_apply]
  rw [ContinuousLinearMap.intervalIntegral_apply hi u,
    ContinuousLinearMap.intervalIntegral_apply hiu v]
  simp only [taylorHessianIntegrand, smul_apply, smul_eq_mul]

private theorem SmoothMorseLemma.secondTaylorFactor_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) : secondTaylorFactor f 0 = fderiv ℝ (fderiv ℝ f) 0 := by
  have hw : (∫ t in (0 : ℝ)..1, (1 - t)) = (1 / 2 : ℝ) := by
    calc
      (∫ t in (0 : ℝ)..1, (1 - t)) = (∫ _t in (0 : ℝ)..1, (1 : ℝ)) - ∫ t in (0 : ℝ)..1, t :=
        intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
          intervalIntegrable_const (continuous_id.intervalIntegrable 0 1)
      _ = 1 / 2 := by norm_num [integral_id]
  have hz :
    (∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ f) 0) =
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) 0 :=
    (intervalIntegral.integral_smul_const (fun t : ℝ => 1 - t) (fderiv ℝ (fderiv ℝ f) 0)).trans
      (congrArg (fun c : ℝ => c • fderiv ℝ (fderiv ℝ f) 0) hw)
  simp only [secondTaylorFactor, taylorHessianIntegrand, smul_zero]
  exact (congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => (2 : ℝ) • B) hz).trans (by norm_num [smul_smul])

private theorem SmoothMorseLemma.secondTaylorFactor_symmetric {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x u v : E) :
    secondTaylorFactor f x u v = secondTaylorFactor f x v u := by
  rw [secondTaylorFactor_apply hf, secondTaylorFactor_apply hf]
  apply congrArg (fun r : ℝ => 2 * r)
  apply intervalIntegral.integral_congr
  intro t _
  have hs : IsSymmSndFDerivAt ℝ f (t • x) :=
    hf.contDiffAt.isSymmSndFDerivAt
      (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  exact congrArg (fun r : ℝ => (1 - t) * r) (hs u v)

private theorem SmoothMorseLemma.map_eq_add_linear_add_secondTaylorFactor {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    f x = f 0 + fderiv ℝ f 0 x + (1 / 2 : ℝ) * secondTaylorFactor f x x x := by
  have ht :=
    map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := 0) (y := x) (n := 1)
      (fun t _ => hf.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have ht' :
    f x = f 0 + fderiv ℝ f 0 x + ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x :=
    by simpa [Finset.sum_range_succ, iteratedFDeriv_two_apply, smul_eq_mul] using ht
  rw [secondTaylorFactor_apply hf]
  calc
    f x = f 0 + fderiv ℝ f 0 x + ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x :=
      ht'
    _ =
        f 0 + fderiv ℝ f 0 x +
          (1 / 2 : ℝ) * (2 * ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x) := by
      ring

private abbrev SmoothMorseLemma.Bilinear (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ

private def SmoothMorseLemma.symmetricForms (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Submodule ℝ (Bilinear E)
    where
  carrier := {B | ∀ u v, B u v = B v u}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro B C hB hC u v
    change B u v + C u v = B v u + C v u
    rw [hB u v, hC u v]
  smul_mem' := by
    intro c B hB u v
    change c * B u v = c * B v u
    rw [hB u v]

private abbrev
    SmoothMorseLemma.SymmetricForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  symmetricForms E

@[ext]
private theorem
    SmoothMorseLemma.symmetricForm_ext (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S T : SymmetricForm E} (h : ∀ u v, S.val u v = T.val u v) : S = T :=
  Subtype.ext (ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => h u v)

private def SmoothMorseLemma.flipBilinear (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Bilinear E →L[ℝ] Bilinear E :=
  (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap

private def SmoothMorseLemma.symmetrize (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Bilinear E →L[ℝ] SymmetricForm E :=
  (((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (Bilinear E) + flipBilinear E)).codRestrict
    (symmetricForms E)
    (fun B u v => by
      change (2 : ℝ)⁻¹ * (B u v + B v u) = (2 : ℝ)⁻¹ * (B v u + B u v)
      ring)

@[simp]
private theorem
    SmoothMorseLemma.symmetrize_apply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Bilinear E) (u v : E) : (symmetrize E B).val u v = (2 : ℝ)⁻¹ * (B u v + B v u) :=
  rfl

private def SmoothMorseLemma.congruence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Bilinear E) (L : E →L[ℝ] E) : Bilinear E :=
  B.bilinearComp L L

@[simp]
private theorem
    SmoothMorseLemma.congruence_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Bilinear E) (L : E →L[ℝ] E) (u v : E) : congruence B L u v = B (L u) (L v) :=
  rfl

@[simp]
private theorem
    SmoothMorseLemma.congruence_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Bilinear E) : congruence B (0 : E →L[ℝ] E) = 0 := by
  ext u v
  simp [congruence]

private theorem
    SmoothMorseLemma.contDiff_congruence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Bilinear E) : ContDiff ℝ ∞ (congruence B) := by
  have h₁ : ContDiff ℝ ∞ (fun L : E →L[ℝ] E => B.comp L) := contDiff_const.clm_comp contDiff_id
  have h₂ : ContDiff ℝ ∞ (fun L : E →L[ℝ] E => (B.comp L).flip) :=
    (flipBilinear E).contDiff.comp h₁
  exact (flipBilinear E).contDiff.comp (h₂.clm_comp contDiff_id)

private def SmoothMorseLemma.raiseIndex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) : Bilinear E →L[ℝ] (E →L[ℝ] E) :=
  ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E H.symm.toContinuousLinearMap

private def
    SmoothMorseLemma.symmetricTaylorFactor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) : SymmetricForm E :=
  symmetrize E (secondTaylorFactor f x)

private theorem SmoothMorseLemma.contDiff_symmetricTaylorFactor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (symmetricTaylorFactor f) :=
  (symmetrize E).contDiff.comp (contDiff_secondTaylorFactor hf)

private theorem SmoothMorseLemma.symmetricTaylorFactor_coe {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    (symmetricTaylorFactor f x).val = secondTaylorFactor f x := by
  ext u v
  change
    (2 : ℝ)⁻¹ * (secondTaylorFactor f x u v + secondTaylorFactor f x v u) =
      secondTaylorFactor f x u v
  rw [secondTaylorFactor_symmetric hf x v u]
  ring

private theorem SmoothMorseLemma.symmetricTaylorFactor_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    (symmetricTaylorFactor f 0).val = fderiv ℝ (fderiv ℝ f) 0 := by
  rw [symmetricTaylorFactor_coe hf, secondTaylorFactor_zero]

private theorem SmoothMorseLemma.map_eq_add_symmetricTaylorFactor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : fderiv ℝ f 0 = 0) (x : E) :
    f x = f 0 + (1 / 2 : ℝ) * (symmetricTaylorFactor f x).val x x := by
  rw [symmetricTaylorFactor_coe hf]
  simpa only [hc, zero_apply, add_zero] using map_eq_add_linear_add_secondTaylorFactor hf x

private theorem SmoothMorseLemma.exists_partialDiffeomorph_of_contDiffOn {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (a : E)
    (ha : a ∈ U) (f' : E ≃L[ℝ] F) (hderiv : HasFDerivAt f (f' : E →L[ℝ] F) a) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞,
      a ∈ e.source ∧ e.source ⊆ U ∧ ∀ x : E, e x = f x := by
  have hfa : ContDiffAt ℝ ∞ f a := hf.contDiffAt (hU.mem_nhds ha)
  have hdc : ContinuousAt (fderiv ℝ f) a :=
    (hf.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds ha)
  have hinv : {x : E | ∃ l : E ≃L[ℝ] F, (l : E →L[ℝ] F) = fderiv ℝ f x} ∈ 𝓝 a := by
    have hn := f'.nhds
    rw [← hderiv.fderiv] at hn
    exact hdc.preimage_mem_nhds hn
  obtain ⟨W, hWsub, hWopen, haW⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds ha) hinv)
  let e : OpenPartialHomeomorph E F := (hfa.toOpenPartialHomeomorph f hderiv (by simp)).restr W
  have heW : e.source ⊆ W := by
    intro x hx
    change x ∈ ((hfa.toOpenPartialHomeomorph f hderiv (by simp)).restr W).source at hx
    rw [OpenPartialHomeomorph.restr_source' _ _ hWopen] at hx
    exact hx.2
  have heU : e.source ⊆ U := fun x hx => (hWsub (heW hx)).1
  have hae : a ∈ e.source := by
    change a ∈ ((hfa.toOpenPartialHomeomorph f hderiv (by simp)).restr W).source
    rw [OpenPartialHomeomorph.restr_source' _ _ hWopen]
    exact ⟨hfa.mem_toOpenPartialHomeomorph_source hderiv (by simp), haW⟩
  refine
    ⟨{  toPartialEquiv := e.toPartialEquiv
        open_source := e.open_source
        open_target := e.open_target
        contMDiffOn_toFun := ?_
        contMDiffOn_invFun := ?_ }, hae, heU, fun _ => rfl⟩
  · change ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f e.source
    exact (hf.mono heU).contMDiffOn
  · apply ContDiffOn.contMDiffOn
    intro y hy
    have hxW := heW (e.map_target hy)
    obtain ⟨hxU, l, hl⟩ := hWsub hxW
    have hfx : ContDiffAt ℝ ∞ f (e.symm y) := hf.contDiffAt (hU.mem_nhds hxU)
    have hdx : HasFDerivAt f (l : E →L[ℝ] F) (e.symm y) := by
      rw [hl]
      exact (hfx.differentiableAt (by simp)).hasFDerivAt
    exact (e.contDiffAt_symm hy hdx hfx).contDiffWithinAt

private theorem SmoothMorseLemma.exists_partialDiffeomorph_of_contDiff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ ∞ f) (a : E) (f' : E ≃L[ℝ] F)
    (hderiv : HasFDerivAt f (f' : E →L[ℝ] F) a) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞, a ∈ e.source ∧ ∀ x : E, e x = f x := by
  obtain ⟨e, ha, _, he⟩ :=
    exists_partialDiffeomorph_of_contDiffOn isOpen_univ hf.contDiffOn a (Set.mem_univ a) f' hderiv
  exact ⟨e, ha, he⟩

private theorem SmoothMorseLemma.exists_quadratic_chart_of_smooth_congruence {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (A : E → SymmetricForm E) (hA : ContDiff ℝ ∞ A) (H : SymmetricForm E) (hA0 : A 0 = H)
    (hfactor : ∀ x, f x = f 0 + (1 / 2 : ℝ) * (A x).val x x) (V : Set (SymmetricForm E))
    (hV : IsOpen V) (hHV : H ∈ V) (L : SymmetricForm E → E →L[ℝ] E) (hL : ContDiffOn ℝ ∞ L V)
    (hL0 : L H = ContinuousLinearMap.id ℝ E) (hcong : ∀ B ∈ V, congruence H.val (L B) = B.val) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (0 : E) ∈ e.source ∧
        e 0 = 0 ∧
          HasFDerivAt e (ContinuousLinearMap.id ℝ E) 0 ∧
            (∀ x ∈ e.source, f x = f 0 + (1 / 2 : ℝ) * H.val (e x) (e x)) ∧
              (∀ y ∈ e.target, f (e.symm y) = f 0 + (1 / 2 : ℝ) * H.val y y) := by
  let U : Set E := A ⁻¹' V
  have hU : IsOpen U := hV.preimage hA.continuous
  have h0 : (0 : E) ∈ U := by
    change A 0 ∈ V
    rw [hA0]
    exact hHV
  have hLA : ContDiffOn ℝ ∞ (fun x => L (A x)) U := hL.comp hA.contDiffOn (fun _ hx => hx)
  let φ : E → E := fun x => L (A x) x
  have hφ : ContDiffOn ℝ ∞ φ U := hLA.clm_apply contDiffOn_id
  have hLA0 : L (A 0) = ContinuousLinearMap.id ℝ E := by rw [hA0, hL0]
  have hd : HasFDerivAt φ (ContinuousLinearMap.id ℝ E) 0 := by
    have h := ((hLA.contDiffAt (hU.mem_nhds h0)).differentiableAt (by simp)).hasFDerivAt
    simpa only [id_eq, hLA0, ContinuousLinearMap.comp_id, map_zero, add_zero] using
      h.clm_apply (hasFDerivAt_id (0 : E))
  obtain ⟨e, he0, heU, he⟩ :=
    exists_partialDiffeomorph_of_contDiffOn hU hφ 0 h0 (ContinuousLinearEquiv.refl ℝ E) hd
  have heφ : (e : E → E) = φ := funext he
  have hezero : e 0 = 0 := by
    rw [he]
    exact map_zero (L (A 0))
  have hnormal (x : E) (hx : x ∈ e.source) : f x = f 0 + (1 / 2 : ℝ) * H.val (e x) (e x) := by
    have hquad := congrArg (fun B : Bilinear E => B x x) (hcong (A x) (heU hx))
    change H.val (L (A x) x) (L (A x) x) = (A x).val x x at hquad
    rw [he]
    change f x = f 0 + (1 / 2 : ℝ) * H.val (L (A x) x) (L (A x) x)
    rw [hquad]
    exact hfactor x
  refine ⟨e, he0, hezero, ?_, hnormal, ?_⟩
  · rw [heφ]
    exact hd
  · intro y hy
    have hr : e (e.symm y) = y := e.right_inv hy
    simpa only [hr] using hnormal (e.symm y) (e.map_target hy)

private def
    SmoothMorseLemma.raiseSymmetricIndex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) : SymmetricForm E →L[ℝ] (E →L[ℝ] E) :=
  (raiseIndex H).comp (symmetricForms E).subtypeL

@[simp]
private theorem SmoothMorseLemma.raiseSymmetricIndex_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) (S : SymmetricForm E) (u : E) :
    raiseSymmetricIndex H S u = H.symm (S.val u) :=
  rfl

private theorem SmoothMorseLemma.hasFDerivAt_congruence_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B : Bilinear E) :
    HasFDerivAt (congruence B) (0 : (E →L[ℝ] E) →L[ℝ] Bilinear E) 0 := by
  have h₁ := (hasFDerivAt_const B (0 : E →L[ℝ] E)).clm_comp (hasFDerivAt_id (0 : E →L[ℝ] E))
  have h₂ := (flipBilinear E).hasFDerivAt.comp 0 h₁
  have h₃ := h₂.clm_comp (hasFDerivAt_id (0 : E →L[ℝ] E))
  have h₄ := (flipBilinear E).hasFDerivAt.comp 0 h₃
  convert h₄ using 1 <;>
    first
    | rfl
    | simp

private def
    SmoothMorseLemma.congruencePolynomial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) (S : SymmetricForm E) : SymmetricForm E :=
  (2 : ℝ) • S + symmetrize E (congruence H.toContinuousLinearMap (raiseSymmetricIndex H S))

@[simp]
private theorem SmoothMorseLemma.congruencePolynomial_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) : congruencePolynomial H 0 = 0 := by
  simp [congruencePolynomial]

private theorem SmoothMorseLemma.contDiff_congruencePolynomial {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) : ContDiff ℝ ∞ (congruencePolynomial H) :=
  (contDiff_id.const_smul (2 : ℝ)).add
    ((symmetrize E).contDiff.comp
      ((contDiff_congruence H.toContinuousLinearMap).comp (raiseSymmetricIndex H).contDiff))

private theorem
    SmoothMorseLemma.hasFDerivAt_congruencePolynomial_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    HasFDerivAt (congruencePolynomial H) ((2 : ℝ) • ContinuousLinearMap.id ℝ (SymmetricForm E))
      0 := by
  have hc :
    HasFDerivAt (congruence H.toContinuousLinearMap) (0 : (E →L[ℝ] E) →L[ℝ] Bilinear E)
      (raiseSymmetricIndex H (0 : SymmetricForm E)) := by
    simpa only [map_zero] using hasFDerivAt_congruence_zero H.toContinuousLinearMap
  have hq := hc.comp (0 : SymmetricForm E) (raiseSymmetricIndex H).hasFDerivAt
  have hs := (symmetrize E).hasFDerivAt.comp (0 : SymmetricForm E) hq
  have h := ((hasFDerivAt_id (0 : SymmetricForm E)).const_smul (2 : ℝ)).add hs
  convert h using 1 <;>
    first
    | rfl
    | simp

private def
    SmoothMorseLemma.referenceSymmetricForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hH : ∀ u v, H u v = H v u) : SymmetricForm E :=
  ⟨H.toContinuousLinearMap, hH⟩

@[simp]
private theorem SmoothMorseLemma.referenceSymmetricForm_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hH : ∀ u v, H u v = H v u) (u v : E) :
    (referenceSymmetricForm H hH).val u v = H u v :=
  rfl

private theorem
    SmoothMorseLemma.congruencePolynomial_add_reference {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hH : ∀ u v, H u v = H v u)
    (S : SymmetricForm E) :
    (congruencePolynomial H S + referenceSymmetricForm H hH).val =
      congruence H.toContinuousLinearMap (ContinuousLinearMap.id ℝ E + raiseSymmetricIndex H S) :=
  by
  ext u v
  have hcross : H u (H.symm (S.val v)) = S.val u v := by
    rw [hH, H.apply_symm_apply, S.property v u]
  have hquad :
    H (H.symm (S.val v)) (H.symm (S.val u)) = H (H.symm (S.val u)) (H.symm (S.val v)) := hH _ _
  have hquad' : S.val v (H.symm (S.val u)) = S.val u (H.symm (S.val v)) := by
    simpa only [H.apply_symm_apply] using hquad
  simp only [congruencePolynomial, Submodule.coe_add, Submodule.coe_smul, add_apply, smul_apply,
    smul_eq_mul, symmetrize_apply, congruence_apply, raiseSymmetricIndex_apply,
    referenceSymmetricForm_apply, ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
    map_add, hcross, H.apply_symm_apply, hquad']
  ring

private def
    SmoothMorseLemma.congruenceDoubleEquiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    SymmetricForm E ≃L[ℝ] SymmetricForm E :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := SymmetricForm E)
    (Units.mk0 (2 : ℝ) (by norm_num))

private theorem SmoothMorseLemma.congruenceDoubleEquiv_toContinuousLinearMap {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (congruenceDoubleEquiv E).toContinuousLinearMap =
      (2 : ℝ) • ContinuousLinearMap.id ℝ (SymmetricForm E) := by
  ext S
  rfl

private theorem SmoothMorseLemma.exists_congruencePolynomial_partialDiffeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) :
    ∃ e :
      PartialDiffeomorph 𝓘(ℝ, SymmetricForm E) 𝓘(ℝ, SymmetricForm E) (SymmetricForm E)
        (SymmetricForm E) ∞,
      (0 : SymmetricForm E) ∈ e.source ∧ ∀ S, e S = congruencePolynomial H S := by
  apply
    exists_partialDiffeomorph_of_contDiff (contDiff_congruencePolynomial H) 0
      (congruenceDoubleEquiv E)
  rw [congruenceDoubleEquiv_toContinuousLinearMap]
  exact hasFDerivAt_congruencePolynomial_zero H

private theorem SmoothMorseLemma.exists_smooth_congruence_factor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (hH : ∀ u v, H u v = H v u) :
    ∃ U : Set (SymmetricForm E),
      IsOpen U ∧
        referenceSymmetricForm H hH ∈ U ∧
          ∃ L : SymmetricForm E → (E →L[ℝ] E),
            ContDiffOn ℝ ∞ L U ∧
              L (referenceSymmetricForm H hH) = ContinuousLinearMap.id ℝ E ∧
                ∀ A ∈ U, congruence H.toContinuousLinearMap (L A) = A.val := by
  obtain ⟨e, he0, he⟩ := exists_congruencePolynomial_partialDiffeomorph H
  have he_zero : e (0 : SymmetricForm E) = 0 := by rw [he, congruencePolynomial_zero]
  have hzero_target : (0 : SymmetricForm E) ∈ e.target := by
    simpa only [he_zero] using e.toPartialEquiv.map_source he0
  have he_symm_zero : e.invFun (0 : SymmetricForm E) = 0 := by
    have h := e.toPartialEquiv.left_inv he0
    change e.invFun (e.toFun 0) = 0 at h
    change e.toFun 0 = 0 at he_zero
    rwa [he_zero] at h
  let U : Set (SymmetricForm E) := (fun A => A - referenceSymmetricForm H hH) ⁻¹' e.target
  let L : SymmetricForm E → (E →L[ℝ] E) := fun A =>
    ContinuousLinearMap.id ℝ E +
      raiseSymmetricIndex H (e.invFun (A - referenceSymmetricForm H hH))
  have hU : IsOpen U := e.open_target.preimage (continuous_id.sub continuous_const)
  have hHU : referenceSymmetricForm H hH ∈ U := by
    simpa only [U, Set.mem_preimage, sub_self] using hzero_target
  have hinv : ContDiffOn ℝ ∞ (fun A => e.invFun (A - referenceSymmetricForm H hH)) U :=
    e.contMDiffOn_invFun.contDiffOn.comp (contDiff_id.sub contDiff_const).contDiffOn
      (fun _ hA => hA)
  refine ⟨U, hU, hHU, L, ?_, ?_, ?_⟩
  · exact contDiffOn_const.add ((raiseSymmetricIndex H).contDiff.comp_contDiffOn hinv)
  · simp only [L, sub_self, he_symm_zero, map_zero, add_zero]
  · intro A hA
    have hq :
      congruencePolynomial H (e.invFun (A - referenceSymmetricForm H hH)) =
        A - referenceSymmetricForm H hH := by
      rw [← he]
      exact e.toPartialEquiv.right_inv hA
    change
      congruence H.toContinuousLinearMap
          (ContinuousLinearMap.id ℝ E +
            raiseSymmetricIndex H (e.invFun (A - referenceSymmetricForm H hH))) =
        A.val
    rw [← congruencePolynomial_add_reference H hH, hq, sub_add_cancel]

private def SmoothMorseLemma.hessianEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (a : E)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
  (LinearEquiv.ofBijective (fderiv ℝ (fderiv ℝ f) a).toLinearMap hn).toContinuousLinearEquiv

private theorem SmoothMorseLemma.exists_morse_chart_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : fderiv ℝ f 0 = 0) (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) 0)) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (0 : E) ∈ e.source ∧
        e 0 = 0 ∧
          HasFDerivAt e (ContinuousLinearMap.id ℝ E) 0 ∧
            (∀ x ∈ e.source, f x = f 0 + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 (e x) (e x)) ∧
              (∀ y ∈ e.target, f (e.symm y) = f 0 + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 y y) := by
  let H := hessianEquiv f 0 hn
  have hH : ∀ u v, H u v = H v u := by
    intro u v
    have hs := (symmetricTaylorFactor f 0).property u v
    rw [symmetricTaylorFactor_zero hf] at hs
    exact hs
  obtain ⟨V, hV, hHV, L, hL, hL0, hcong⟩ := exists_smooth_congruence_factor H hH
  have hA0 : symmetricTaylorFactor f 0 = referenceSymmetricForm H hH := by
    apply Subtype.ext
    exact symmetricTaylorFactor_zero hf
  obtain ⟨e, he0, hezero, hederiv, hnormal, hinverse⟩ :=
    exists_quadratic_chart_of_smooth_congruence f (symmetricTaylorFactor f)
      (contDiff_symmetricTaylorFactor hf) (referenceSymmetricForm H hH) hA0
      (map_eq_add_symmetricTaylorFactor hf hc) V hV hHV L hL hL0 hcong
  exact ⟨e, he0, hezero, hederiv, hnormal, hinverse⟩

private theorem SmoothMorseLemma.exists_contDiff_compactlySupported_eqOn_closedBall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E}
    {a : E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ g : E → ℝ,
      ContDiff ℝ ∞ g ∧
        HasCompactSupport g ∧
          tsupport g ⊆ U ∧
            ∃ r : ℝ, 0 < r ∧ Metric.closedBall a r ⊆ U ∧ Set.EqOn g f (Metric.closedBall a r) := by
  obtain ⟨r, hr, hrU⟩ : ∃ r : ℝ, 0 < r ∧ Metric.closedBall a r ⊆ U :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds ha)
  let β : ContDiffBump a :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  have hβU : tsupport (β : E → ℝ) ⊆ U := by
    rw [β.tsupport_eq]
    exact hrU
  have hg : ContDiff ℝ ∞ (fun x => β x * f x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport (β : E → ℝ)
    · exact β.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds (hβU hx)))
    · have hzero : (β : E → ℝ) =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
      have hconst : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℝ)) x := contDiffAt_const
      apply hconst.congr_of_eventuallyEq
      filter_upwards [hzero] with y hy
      simp only [hy, Pi.zero_apply, MulZeroClass.zero_mul]
  refine
    ⟨fun x => β x * f x, hg, β.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans hβU,
      β.rIn, β.rIn_pos, ?_, ?_⟩
  · exact (Metric.closedBall_subset_closedBall β.rIn_lt_rOut.le).trans hrU
  · intro x hx
    change β x * f x = f x
    rw [β.one_of_mem_closedBall hx, one_mul]

private theorem SmoothMorseLemma.exists_contDiff_extension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E} {a : E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 a] f := by
  obtain ⟨g, hg, _, _, r, hr, _, he⟩ :=
    exists_contDiff_compactlySupported_eqOn_closedBall hf hU ha
  refine ⟨g, hg, ?_⟩
  filter_upwards [Metric.ball_mem_nhds a hr] with x hx
  exact he (Metric.ball_subset_closedBall hx)

private theorem SmoothMorseLemma.exists_contDiff_extension_preserving_derivatives {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E}
    {a : E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ g : E → ℝ,
      ContDiff ℝ ∞ g ∧
        g =ᶠ[𝓝 a] f ∧
          g a = f a ∧
            fderiv ℝ g a = fderiv ℝ f a ∧
              fderiv ℝ (fderiv ℝ g) a = fderiv ℝ (fderiv ℝ f) a ∧
                ∀ n : ℕ, iteratedFDeriv ℝ n g =ᶠ[𝓝 a] iteratedFDeriv ℝ n f := by
  obtain ⟨g, hg, he⟩ := exists_contDiff_extension hf hU ha
  exact
    ⟨g, hg, he, he.self_of_nhds, he.fderiv_eq, he.fderiv.fderiv_eq, fun n =>
      he.iteratedFDeriv ℝ n⟩

private def SmoothMorseLemma.restrictChart {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    (U : Set E) (hU : IsOpen U) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞
    where
  __ := e.toOpenPartialHomeomorph.restrOpen U hU
  contMDiffOn_toFun := e.contMDiffOn_toFun.mono Set.inter_subset_left
  contMDiffOn_invFun := e.contMDiffOn_invFun.mono Set.inter_subset_left

@[simp]
private theorem SmoothMorseLemma.restrictChart_apply {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) (U : Set E) (hU : IsOpen U) (x : E) :
    restrictChart e U hU x = e x :=
  rfl

private def SmoothMorseLemma.translationToZero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞
    where
  toFun x := x - a
  invFun x := a + x
  left_inv x := by simp [sub_eq_add_neg]
  right_inv x := by simp [sub_eq_add_neg, add_assoc]
  contMDiff_toFun :=
    (show ContDiff ℝ ∞ (fun x : E => x - a) from contDiff_id.sub contDiff_const).contMDiff
  contMDiff_invFun :=
    (show ContDiff ℝ ∞ (fun x : E => a + x) from contDiff_const.add contDiff_id).contMDiff

private def SmoothMorseLemma.translateChart {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞ :=
  (translationToZero a).toPartialDiffeomorph.trans e

@[simp]
private theorem SmoothMorseLemma.translateChart_apply {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) (x : E) : translateChart a e x = e (x - a) :=
  rfl

@[simp]
private theorem SmoothMorseLemma.mem_translateChart_source {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) (x : E) :
    x ∈ (translateChart a e).source ↔ x - a ∈ e.source := by
  change (x ∈ Set.univ ∧ x - a ∈ e.source) ↔ x - a ∈ e.source
  simp only [Set.mem_univ, true_and]

private theorem SmoothMorseLemma.hessian_comp_add_left {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (a x : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (a + y))) x = fderiv ℝ (fderiv ℝ f) (a + x) := by
  have h : fderiv ℝ (fun y => f (a + y)) = fun y => fderiv ℝ f (a + y) :=
    funext fun y => fderiv_comp_add_left a
  rw [h, fderiv_comp_add_left]

private theorem
    SmoothMorseLemma.exists_morse_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a : E) (hc : fderiv ℝ f a = 0)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      a ∈ e.source ∧
        e a = 0 ∧
          HasFDerivAt e (ContinuousLinearMap.id ℝ E) a ∧
            (∀ x ∈ e.source, f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (e x) (e x)) ∧
              (∀ y ∈ e.target, f (e.symm y) = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a y y) := by
  let g : E → ℝ := fun x => f (a + x)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  have hgc : fderiv ℝ g 0 = 0 := by simpa only [g, fderiv_comp_add_left, add_zero] using hc
  have hgn : Function.Bijective (fderiv ℝ (fderiv ℝ g) 0) := by
    simpa only [g, hessian_comp_add_left, add_zero] using hn
  obtain ⟨e, he0, hezero, hederiv, hnormal, _⟩ := exists_morse_chart_zero hg hgc hgn
  let φ := translateChart a e
  have haφ : a ∈ φ.source := by
    change a ∈ (translateChart a e).source
    rw [mem_translateChart_source, sub_self]
    exact he0
  have hφzero : φ a = 0 := by
    change e (a - a) = 0
    rw [sub_self, hezero]
  have hφderiv : HasFDerivAt φ (ContinuousLinearMap.id ℝ E) a := by
    have hφfun : (φ : E → E) = fun x => e (x - a) := funext (translateChart_apply a e)
    rw [hφfun]
    have hdshift : HasFDerivAt (fun x : E => x - a) (ContinuousLinearMap.id ℝ E) a :=
      (hasFDerivAt_id a).sub_const a
    have hdouter : HasFDerivAt e (ContinuousLinearMap.id ℝ E) (a - a) := by
      simpa only [sub_self] using hederiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      hdouter.comp (f := fun x : E => x - a) a hdshift
  have hφnormal (x : E) (hx : x ∈ φ.source) :
    f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (φ x) (φ x) := by
    have hx' : x - a ∈ e.source := (mem_translateChart_source a e x).mp hx
    have hpoint : a + (x - a) = x := by simp [sub_eq_add_neg]
    simpa only [g, hessian_comp_add_left, add_zero, hpoint, φ, translateChart_apply] using
      hnormal (x - a) hx'
  refine ⟨φ, haφ, hφzero, hφderiv, hφnormal, ?_⟩
  intro y hy
  have hr : φ (φ.symm y) = y := φ.right_inv hy
  simpa only [hr] using hφnormal (φ.symm y) (φ.map_target hy)

private theorem SmoothMorseLemma.exists_morse_chart_of_contDiffOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E} (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) (a : E) (ha : a ∈ U) (hc : fderiv ℝ f a = 0)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      a ∈ e.source ∧
        e.source ⊆ U ∧
          e a = 0 ∧
            HasFDerivAt e (ContinuousLinearMap.id ℝ E) a ∧
              (∀ x ∈ e.source, f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (e x) (e x)) ∧
                (∀ y ∈ e.target,
                  f (e.symm y) = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a y y) := by
  obtain ⟨g, hg, heq, hga, hdf, hH, _⟩ :=
    exists_contDiff_extension_preserving_derivatives hf hU ha
  have hgc : fderiv ℝ g a = 0 := hdf.trans hc
  have hgn : Function.Bijective (fderiv ℝ (fderiv ℝ g) a) := by
    rw [hH]
    exact hn
  obtain ⟨e, hea, hezero, hederiv, hnormal, _⟩ := exists_morse_chart hg a hgc hgn
  obtain ⟨W, hWsub, hWopen, haW⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds ha) heq)
  let φ := restrictChart e W hWopen
  have haφ : a ∈ φ.source := ⟨hea, haW⟩
  have hφU : φ.source ⊆ U := fun _ hx => (hWsub hx.2).1
  have hφnormal (x : E) (hx : x ∈ φ.source) :
    f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (φ x) (φ x) := by
    have hxeq : g x = f x := (hWsub hx.2).2
    simpa only [φ, restrictChart_apply, hxeq, hga, hH] using hnormal x hx.1
  refine ⟨φ, haφ, hφU, hezero, hederiv, hφnormal, ?_⟩
  intro y hy
  have hr : φ (φ.symm y) = y := φ.right_inv hy
  simpa only [hr] using hφnormal (φ.symm y) (φ.map_target hy)

private def
    SmoothMorseLemma.halfHessianQuadratic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Bilinear E) : QuadraticForm ℝ E :=
  LinearMap.BilinMap.toQuadraticMap ((1 / 2 : ℝ) • H.toLinearMap₁₂)

@[simp]
private theorem SmoothMorseLemma.halfHessianQuadratic_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : Bilinear E) (x : E) : halfHessianQuadratic H x = (1 / 2 : ℝ) * H x x :=
  rfl

private theorem SmoothMorseLemma.halfHessianQuadratic_associated {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : Bilinear E) (hH : ∀ x y, H x y = H y x) :
    QuadraticMap.associated (halfHessianQuadratic H) = (1 / 2 : ℝ) • H.toLinearMap₁₂ := by
  apply QuadraticMap.associated_left_inverse ℝ (B₁ := (1 / 2 : ℝ) • H.toLinearMap₁₂)
  intro x y
  change (1 / 2 : ℝ) * H x y = (1 / 2 : ℝ) * H y x
  rw [hH]

private theorem
    SmoothMorseLemma.halfHessianQuadratic_separatingLeft {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : Bilinear E) (hH : ∀ x y, H x y = H y x)
    (hHinj : Function.Injective H) :
    (QuadraticMap.associated (halfHessianQuadratic H)).SeparatingLeft := by
  rw [halfHessianQuadratic_associated H hH]
  intro x hx
  apply hHinj
  ext y
  have hxy := hx y
  change (1 / 2 : ℝ) * H x y = 0 at hxy
  simpa using (mul_eq_zero.mp hxy).resolve_left (by norm_num)

private theorem SmoothMorseLemma.exists_signed_coordinates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : Bilinear E) (hH : ∀ x y, H x y = H y x)
    (hHbij : Function.Bijective H) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        ∃ C : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ),
          ∀ x, (1 / 2 : ℝ) * H x x = ∑ i, w i * (C x i) ^ 2 := by
  obtain ⟨w, hw, ⟨C⟩⟩ :=
    (halfHessianQuadratic H).equivalent_one_neg_one_weighted_sum_squared
      (halfHessianQuadratic_separatingLeft H hH hHbij.1)
  refine ⟨w, hw, C.toLinearEquiv.toContinuousLinearEquiv, ?_⟩
  intro x
  change (1 / 2 : ℝ) * H x x = ∑ i, w i * (C x i) ^ 2
  simpa only [QuadraticMap.weightedSumSquares_apply, halfHessianQuadratic_apply, smul_eq_mul,
    pow_two] using (C.map_app x).symm

private theorem SmoothMorseLemma.exists_signed_diffeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : Bilinear E) (hH : ∀ x y, H x y = H y x)
    (hHbij : Function.Bijective H) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        ∃ C : E ≃ₘ[ℝ] (Fin (Module.finrank ℝ E) → ℝ),
          C 0 = 0 ∧ ∀ x, (1 / 2 : ℝ) * H x x = ∑ i, w i * (C x i) ^ 2 := by
  obtain ⟨w, hw, C, hC⟩ := exists_signed_coordinates H hH hHbij
  exact ⟨w, hw, C.toDiffeomorph, C.map_zero, hC⟩

private theorem SmoothMorseLemma.hessian_symmetric_of_contDiffOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {U : Set E} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {a : E}
    (ha : a ∈ U) (u v : E) : fderiv ℝ (fderiv ℝ f) a u v = fderiv ℝ (fderiv ℝ f) a v u := by
  have hs :=
    (hf.contDiffAt (hU.mem_nhds ha)).isSymmSndFDerivAt
      (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  exact hs u v

private theorem SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (a : E) (ha : a ∈ U) (hc : fderiv ℝ f a = 0)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        ∃ e :
          PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) E
            (Fin (Module.finrank ℝ E) → ℝ) ∞,
          a ∈ e.source ∧
            e.source ⊆ U ∧
              e a = 0 ∧
                (∀ x ∈ e.source, f x = f a + ∑ i, w i * (e x i) ^ 2) ∧
                  (∀ y ∈ e.target, f (e.symm y) = f a + ∑ i, w i * y i ^ 2) := by
  obtain ⟨e, hea, heU, hezero, _, hnormal, _⟩ := exists_morse_chart_of_contDiffOn hf hU a ha hc hn
  obtain ⟨w, hw, C, hCzero, hC⟩ :=
    exists_signed_diffeomorph (fderiv ℝ (fderiv ℝ f) a) (hessian_symmetric_of_contDiffOn hf hU ha)
      hn
  let φ := e.trans C.toPartialDiffeomorph
  have hsource : φ.source = e.source := by
    ext x
    change (x ∈ e.source ∧ e x ∈ (Set.univ : Set E)) ↔ x ∈ e.source
    simp only [Set.mem_univ, and_true]
  have haφ : a ∈ φ.source := hsource ▸ hea
  have hφU : φ.source ⊆ U := hsource ▸ heU
  have hφzero : φ a = 0 := by
    change C (e a) = 0
    rw [hezero, hCzero]
  have hφnormal (x : E) (hx : x ∈ φ.source) : f x = f a + ∑ i, w i * (φ x i) ^ 2 := by
    have hx' : x ∈ e.source := hsource ▸ hx
    calc
      f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (e x) (e x) := hnormal x hx'
      _ = f a + ∑ i, w i * (C (e x) i) ^ 2 := by rw [hC]
      _ = f a + ∑ i, w i * (φ x i) ^ 2 := rfl
  refine ⟨w, hw, φ, haφ, hφU, hφzero, hφnormal, ?_⟩
  intro y hy
  have hr : φ (φ.symm y) = y := φ.right_inv hy
  simpa only [hr] using hφnormal (φ.symm y) (φ.map_target hy)

private def Smale.ManifoldMorse.chartPartialDiffeomorph {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (e : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞
    where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he

private structure Smale.ManifoldMorse.SignedMorseChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (x : M) where
  weights : Fin (Module.finrank ℝ E) → ℝ
  signs : ∀ i, weights i = -1 ∨ weights i = 1
  chart :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) M (Fin (Module.finrank ℝ E) → ℝ)
      ∞
  mem_source : x ∈ chart.source
  center : chart x = 0
  equation : ∀ y ∈ chart.source, f y = f x + ∑ i, weights i * (chart y i) ^ 2
  inverse_equation : ∀ y ∈ chart.target, f (chart.symm y) = f x + ∑ i, weights i * y i ^ 2

private theorem Smale.ManifoldMorse.nonempty_signedMorseChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) (x : M)
    (hx : x ∈ criticalPoints E f) : Nonempty (SignedMorseChart (E := E) f x) := by
  obtain ⟨e, he, hxS, hreg | hH⟩ := hm x
  · exact False.elim (hreg ((mem_criticalPoints_iff hf he hxS).mp hx))
  · have hc := (mem_criticalPoints_iff hf he hxS).mp hx
    obtain ⟨w, hw, d, hdx, -, hd₀, hdeq, hdinv⟩ :=
      SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn (contDiffOn_chartExpression hf he)
        e.open_target (e x) (e.map_source hxS) hc hH
    let c := (chartPartialDiffeomorph e he).trans d
    refine ⟨⟨w, hw, c, ⟨hxS, hdx⟩, hd₀, ?_, ?_⟩⟩
    · intro y hy
      have hyS : y ∈ e.source := hy.1
      have hyd : e y ∈ d.source := hy.2
      change f y = f x + ∑ i, w i * (d (e y) i) ^ 2
      simpa only [Function.comp_apply, e.left_inv hyS, e.left_inv hxS] using hdeq (e y) hyd
    · intro y hy
      have hyd : y ∈ d.target := hy.1
      change f (e.symm (d.symm y)) = f x + ∑ i, w i * y i ^ 2
      simpa only [Function.comp_apply, e.left_inv hxS] using hdinv y hyd

private abbrev Smale.MorseHandle.Negative {ι : Type*} (w : ι → ℝ) :=
  { i // w i = -1 }

private abbrev Smale.MorseHandle.Positive {ι : Type*} (w : ι → ℝ) :=
  { i // w i ≠ -1 }

private abbrev Smale.MorseHandle.NegativeSpace {ι : Type*} (w : ι → ℝ) :=
  EuclideanSpace ℝ (Negative w)

private abbrev Smale.MorseHandle.PositiveSpace {ι : Type*} (w : ι → ℝ) :=
  EuclideanSpace ℝ (Positive w)

attribute [local instance 100] Classical.propDecidable in
private def Smale.MorseHandle.splitLinearEquiv {ι : Type*} (w : ι → ℝ) :
    (ι → ℝ) ≃ₗ[ℝ] (NegativeSpace w × PositiveSpace w) := by
  let e : (ι → ℝ) ≃ₗ[ℝ] ((Negative w → ℝ) × (Positive w → ℝ)) :=
    { toEquiv := Equiv.piEquivPiSubtypeProd (fun i => w i = -1) (fun _ => ℝ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact
    e.trans
      (LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (Negative w → ℝ)).symm
        (WithLp.linearEquiv 2 ℝ (Positive w → ℝ)).symm)

attribute [local instance 100] Classical.propDecidable in
private def Smale.MorseHandle.splitCoordinates {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    (ι → ℝ) ≃L[ℝ] (NegativeSpace w × PositiveSpace w) :=
  (splitLinearEquiv w).toContinuousLinearEquiv

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.MorseHandle.signedSum_eq_norms {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (z : ι → ℝ) :
    ∑ i, w i * (z i) ^ 2 = -‖(splitCoordinates w z).1‖ ^ 2 + ‖(splitCoordinates w z).2‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have hneg : (∑ i : Negative w, w i.1 * (z i.1) ^ 2) = -∑ i : Negative w, (z i.1) ^ 2 := by
    calc
      _ = ∑ i : Negative w, -(z i.1) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [i.2, neg_one_mul]
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hpos : (∑ i : Positive w, w i.1 * (z i.1) ^ 2) = ∑ i : Positive w, (z i.1) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(hw i.1).resolve_left i.2, one_mul]
  calc
    ∑ i, w i * (z i) ^ 2 =
        (∑ i : Negative w, w i.1 * (z i.1) ^ 2) + ∑ i : Positive w, w i.1 * (z i.1) ^ 2 :=
      (Fintype.sum_subtype_add_sum_subtype (fun i => w i = -1) (fun i => w i * (z i) ^ 2)).symm
    _ = _ := by rw [hneg, hpos]; rfl

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.MorseHandle.signedSum_symm_eq_norms {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (z : NegativeSpace w × PositiveSpace w) :
    ∑ i, w i * ((splitCoordinates w).symm z i) ^ 2 = -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    signedSum_eq_norms w hw ((splitCoordinates w).symm z)

private abbrev Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) :=
  Smale.MorseHandle.NegativeSpace c.weights

private abbrev Smale.ManifoldMorse.SignedMorseChart.PositiveCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) :=
  Smale.MorseHandle.PositiveSpace c.weights

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.finrank_negative_add_positive {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) :
    Module.finrank ℝ c.NegativeCoordinates + Module.finrank ℝ c.PositiveCoordinates =
      Module.finrank ℝ E := by
  have h := (Smale.MorseHandle.splitLinearEquiv c.weights).finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_fin_fun] using h.symm

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.splitChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) M
      (c.NegativeCoordinates × c.PositiveCoordinates) ∞ :=
  c.chart.trans (Smale.MorseHandle.splitCoordinates c.weights).toDiffeomorph.toPartialDiffeomorph

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.splitChart_mem_source {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) : x ∈ c.splitChart.source :=
  ⟨c.mem_source, Set.mem_univ _⟩

attribute [local instance 100] Classical.propDecidable in
@[simp]
private theorem Smale.ManifoldMorse.SignedMorseChart.splitChart_center {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) : c.splitChart x = 0 := by
  change Smale.MorseHandle.splitCoordinates c.weights (c.chart x) = 0
  rw [c.center, map_zero]

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.splitChart_equation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {y : M}
    (hy : y ∈ c.splitChart.source) :
    f y = f x - ‖(c.splitChart y).1‖ ^ 2 + ‖(c.splitChart y).2‖ ^ 2 := by
  rw [c.equation y hy.1, Smale.MorseHandle.signedSum_eq_norms c.weights c.signs]
  change f x + (-‖(c.splitChart y).1‖ ^ 2 + ‖(c.splitChart y).2‖ ^ 2) = _
  ring

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.splitChart_inverse_equation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x)
    {y : c.NegativeCoordinates × c.PositiveCoordinates} (hy : y ∈ c.splitChart.target) :
    f (c.splitChart.symm y) = f x - ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
  change f (c.chart.symm ((Smale.MorseHandle.splitCoordinates c.weights).symm y)) = _
  rw [c.inverse_equation ((Smale.MorseHandle.splitCoordinates c.weights).symm y) hy.2,
    Smale.MorseHandle.signedSum_symm_eq_norms c.weights c.signs]
  ring

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.exists_closed_productBlock {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) :
    ∃ r > (0 : ℝ),
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target := by
  have hzero : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target := by
    rw [← c.splitChart_center]
    exact c.splitChart.toOpenPartialHomeomorph.map_source c.splitChart_mem_source
  obtain ⟨r, hr, hsub⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (c.splitChart.open_target.mem_nhds hzero)
  refine ⟨r, hr, ?_⟩
  rw [closedBall_prod_same]
  exact hsub

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.descentField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) : (x : M) → TangentSpace 𝓘(ℝ, E) x :=
  Smale.FlowConstruction.partialChartField c.splitChart Smale.MorseHandle.descent

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.contMDiffOn_descentField {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [CompleteSpace E]
    [IsManifold 𝓘(ℝ, E) ∞ M] :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, c.descentField x⟩ : TangentBundle 𝓘(ℝ, E) M)) c.splitChart.source :=
  Smale.FlowConstruction.contMDiffOn_partialChartField c.splitChart
    Smale.MorseHandle.contDiff_descent

attribute [local instance 100] Classical.propDecidable in
@[simp]
private theorem Smale.ManifoldMorse.SignedMorseChart.descentField_center {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) : c.descentField p = 0 := by
  have hzero : Smale.MorseHandle.descent (c.splitChart p) = 0 := by
    rw [c.splitChart_center]
    simp [Smale.MorseHandle.descent]
  unfold descentField Smale.FlowConstruction.partialChartField
  rw [VectorField.mpullback_apply, hzero, map_zero, map_zero]

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.mvfderiv_descentField {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : x ∈ c.splitChart.source) :
    mvfderiv 𝓘(ℝ, E) f x (c.descentField x) =
      -2 * (‖(c.splitChart x).1‖ ^ 2 + ‖(c.splitChart x).2‖ ^ 2) := by
  rw [descentField, Smale.FlowConstruction.mvfderiv_partialChartField hf c.splitChart _ hx]
  have hcoord :
    (f ∘ c.splitChart.symm) =ᶠ[𝓝 (c.splitChart x)]
      (fun z => f p + Smale.MorseHandle.quadratic z) := by
    filter_upwards [c.splitChart.open_target.mem_nhds
        (c.splitChart.toOpenPartialHomeomorph.map_source hx)] with
      z hz
    change f (c.splitChart.symm z) = f p + (-‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
    rw [c.splitChart_inverse_equation hz]
    ring
  rw [hcoord.fderiv_eq, fderiv_const_add]
  exact Smale.MorseHandle.fderiv_quadratic_descent _

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.mvfderiv_descentField_neg {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : x ∈ c.splitChart.source) (hxp : x ≠ p) :
    mvfderiv 𝓘(ℝ, E) f x (c.descentField x) < 0 := by
  have hcoord : c.splitChart x ≠ 0 := by
    intro h
    apply hxp
    exact
      c.splitChart.toOpenPartialHomeomorph.injOn hx c.splitChart_mem_source
        (h.trans c.splitChart_center.symm)
  rw [c.mvfderiv_descentField hf hx]
  simpa only [Smale.MorseHandle.fderiv_quadratic_descent] using
    Smale.MorseHandle.fderiv_quadratic_descent_neg hcoord

private theorem Smale.ManifoldMorse.exists_adaptedDescentField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x ∈ criticalPoints E f, V x = 0) ∧
          (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
            ∀ p ∈ criticalPoints E f,
              ∃ c : SignedMorseChart (E := E) f p, ∀ᶠ x in 𝓝 p, V x = c.descentField x := by
  classical
  let S := criticalPoints E f
  have hS : S.Finite := finite_criticalPoints hf hm
  let : Fintype S := hS.fintype
  let c (p : S) : SignedMorseChart (E := E) f (p : M) :=
    Classical.choice (nonempty_signedMorseChart hf hm p.1 p.2)
  obtain ⟨U₀, hU₀, hdisj₀⟩ := hS.t2_separation
  let U (p : S) : Set M := U₀ p ∩ (c p).splitChart.source
  have hU (p : S) : IsOpen (U p) := (hU₀ p).2.inter (c p).splitChart.open_source
  have hpU (p : S) : (p : M) ∈ U p := ⟨(hU₀ p).1, (c p).splitChart_mem_source⟩
  have hdisj : Pairwise (fun p q : S => Disjoint (U p) (U q)) := by
    intro p q hpq
    exact
      (hdisj₀ p.2 q.2 (fun h => hpq (Subtype.ext h))).mono Set.inter_subset_left
        Set.inter_subset_left
  choose K hKnhds hKclosed hKU using
    (fun p : S => exists_mem_nhds_isClosed_subset ((hU p).mem_nhds (hpU p)))
  have hcover : criticalPoints E f ⊆ ⋃ p : S, K p := by
    intro p hp
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, mem_of_mem_nhds (hKnhds ⟨p, hp⟩)⟩
  have hVloc (p : S) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, (c p).descentField x⟩ : TangentBundle 𝓘(ℝ, E) M)) (U p) :=
    (c p).contMDiffOn_descentField.mono Set.inter_subset_right
  have hdesc (p : S) (x : M) (hx : x ∈ U p) (hreg : x ∉ criticalPoints E f) :
    mvfderiv 𝓘(ℝ, E) f x ((c p).descentField x) < 0 :=
    (c p).mvfderiv_descentField_neg hf hx.2 (fun h => hreg (h.symm ▸ p.2))
  obtain ⟨V, hV, hstrict, hmatch⟩ :=
    Smale.FlowConstruction.exists_gluedDescentField hf U K hU hKclosed hKU hdisj hcover
      (fun p => (c p).descentField) hVloc hdesc
  refine ⟨V, hV, ?_, hstrict, ?_⟩
  · intro p hp
    rw [hmatch ⟨p, hp⟩ p (mem_of_mem_nhds (hKnhds ⟨p, hp⟩))]
    exact (c ⟨p, hp⟩).descentField_center
  · intro p hp
    refine ⟨c ⟨p, hp⟩, ?_⟩
    filter_upwards [hKnhds ⟨p, hp⟩] with x hx
    exact hmatch ⟨p, hp⟩ x hx

private theorem MorseCancel.morse_descentField_zero_at_critical {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
      {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ c.splitChart.source) (hcrit : x ∈ Smale.ManifoldMorse.criticalPoints E f) :
    c.descentField x = 0 := by
  by_cases hxp : x = p
  · subst x
    exact c.descentField_center
  · have hneg := c.mvfderiv_descentField_neg hf hx hxp
    have hc : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0 := hcrit
    have hz : mvfderiv 𝓘(ℝ, E) f x (c.descentField x) = 0 := by
      unfold mvfderiv
      rw [hc]
      rfl
    rw [hz] at hneg
    exact False.elim (lt_irrefl (0 : ℝ) hneg)

private theorem MorseCancel.exists_prescribed_morse_patch_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f) {ι : Type*}
    [Finite ι] (p : ι → M) (hp : ∀ i, p i ∈ Smale.ManifoldMorse.criticalPoints E f)
    (c : ∀ i, Smale.ManifoldMorse.SignedMorseChart (E := E) f (p i)) (K : ι → Set M)
    (hK : ∀ i, IsClosed (K i)) (hKchart : ∀ i, K i ⊆ (c i).splitChart.source)
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0) ∧
          (∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
            ∀ i x, x ∈ K i → V x = (c i).descentField x := by
  obtain ⟨V₀, hV₀, hzero₀, hdesc₀, -⟩ := Smale.ManifoldMorse.exists_adaptedDescentField hf hm
  apply
    exists_closed_patch_descent_field V₀ hV₀ hzero₀ hdesc₀ K (fun i => (c i).splitChart.source) hK
      (fun i => (c i).splitChart.open_source) hKchart hdisj (fun i => (c i).descentField)
      (fun i => (c i).contMDiffOn_descentField)
  · exact fun i x hx hc => morse_descentField_zero_at_critical (c i) hf hx hc
  · intro i x hx hreg
    exact (c i).mvfderiv_descentField_neg hf hx (fun h => hreg (h.symm ▸ hp i))

attribute [local instance 100] Classical.propDecidable in
private def MorseCancel.morseClosedBlock {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ) : Set M :=
  c.splitChart.symm ''
    (Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
      Metric.closedBall (0 : c.PositiveCoordinates) R)

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.morseClosedBlock_subset_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) R ⊆
        c.splitChart.target) :
    morseClosedBlock c R ⊆ c.splitChart.source := by
  rintro x ⟨z, hz, rfl⟩
  exact c.splitChart.map_target' (hblock hz)

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.morseClosedBlock_height {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) R ⊆
        c.splitChart.target) :
    morseClosedBlock c R ⊆ f ⁻¹' Set.Icc (f p - R ^ 2) (f p + R ^ 2) := by
  rintro x ⟨z, hz, rfl⟩
  have hn : ‖z.1‖ ≤ R := mem_closedBall_zero_iff.mp hz.1
  have hp : ‖z.2‖ ≤ R := mem_closedBall_zero_iff.mp hz.2
  have hn2 : ‖z.1‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hp2 : ‖z.2‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  change f (c.splitChart.symm z) ∈ Set.Icc (f p - R ^ 2) (f p + R ^ 2)
  rw [c.splitChart_inverse_equation (hblock hz)]
  constructor <;> nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.morseClosedBlock_mem_nhds {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) R ⊆
        c.splitChart.target)
    {z : c.NegativeCoordinates × c.PositiveCoordinates} (hn : ‖z.1‖ < R) (hp : ‖z.2‖ < R) :
    morseClosedBlock c R ∈ 𝓝 (c.splitChart.symm z) := by
  have hz : z ∈ c.splitChart.target :=
    hblock ⟨mem_closedBall_zero_iff.mpr hn.le, mem_closedBall_zero_iff.mpr hp.le⟩
  have hx : c.splitChart.symm z ∈ c.splitChart.source := c.splitChart.map_target' hz
  have hc : c.splitChart (c.splitChart.symm z) = z := c.splitChart.right_inv' hz
  have ho :
    Metric.ball (0 : c.NegativeCoordinates) R ×ˢ Metric.ball (0 : c.PositiveCoordinates) R ∈
      𝓝 (c.splitChart (c.splitChart.symm z)) := by
    rw [hc]
    exact
      (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
        ⟨mem_ball_zero_iff.mpr hn, mem_ball_zero_iff.mpr hp⟩
  have hnear := (c.splitChart.toOpenPartialHomeomorph.continuousAt hx) ho
  filter_upwards [c.splitChart.open_source.mem_nhds hx, hnear] with y hy hcy
  exact
    ⟨c.splitChart y, ⟨Metric.ball_subset_closedBall hcy.1, Metric.ball_subset_closedBall hcy.2⟩,
      c.splitChart.left_inv' hy⟩

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.isCompact_morseClosedBlock {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
     (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) R ⊆
        c.splitChart.target) :
    IsCompact (morseClosedBlock c R) :=
  (ProperSpace.isCompact_closedBall (0 : c.NegativeCoordinates) R).prod
      (ProperSpace.isCompact_closedBall (0 : c.PositiveCoordinates) R) |>.image_of_continuousOn
    (c.splitChart.symm.contMDiffOn_toFun.continuousOn.mono hblock)

private theorem Smale.FlowConstruction.exists_localFlow_in_open {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {v : E → E} {x₀ : E} (hv : ContDiffAt ℝ 1 v x₀)
    {U : Set E} (hU : IsOpen U) (hxU : x₀ ∈ U) :
    ∃ r > (0 : ℝ),
      ∃ ε > (0 : ℝ),
        ∃ α : E × ℝ → E,
          ContinuousOn α (Metric.ball x₀ r ×ˢ Set.Ioo (-ε) ε) ∧
            ∀ x ∈ Metric.ball x₀ r,
              α (x, 0) = x ∧
                ∀ t ∈ Set.Ioo (-ε) ε,
                  α (x, t) ∈ U ∧ HasDerivAt (fun s => α (x, s)) (v (α (x, t))) t := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hv
  obtain ⟨α, hα, hc⟩ := (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  simp only [zero_sub, zero_add] at hα hc
  have hr' : (0 : ℝ) < r := hr
  have hc₀ : ContinuousAt α (x₀, 0) :=
    hc.continuousAt
      (prod_mem_nhds (Metric.closedBall_mem_nhds x₀ hr') (Icc_mem_nhds (neg_lt_zero.mpr hε) hε))
  have hα₀ : α (x₀, 0) = x₀ := (hα x₀ (Metric.mem_closedBall_self hr'.le)).1
  have hpre : α ⁻¹' U ∈ 𝓝 (x₀, 0) := hc₀.preimage_mem_nhds (hU.mem_nhds (hα₀.symm ▸ hxU))
  have hD : Metric.ball x₀ (r : ℝ) ×ˢ Set.Ioo (-ε) ε ∈ 𝓝 (x₀, 0) :=
    prod_mem_nhds (Metric.ball_mem_nhds x₀ hr') (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hD hpre)
  have hs :
    Metric.ball x₀ δ ×ˢ Set.Ioo (-δ) δ ⊆ (Metric.ball x₀ (r : ℝ) ×ˢ Set.Ioo (-ε) ε) ∩ α ⁻¹' U := by
    intro q hq
    apply hδsub
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hq.1, by simpa only [dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr hq.2⟩
  refine ⟨δ, hδ, δ, hδ, α, hc.mono ?_, ?_⟩
  · intro q hq
    exact ⟨Metric.ball_subset_closedBall (hs hq).1.1, Set.Ioo_subset_Icc_self (hs hq).1.2⟩
  · intro x hx
    have hx₀ : (x, (0 : ℝ)) ∈ Metric.ball x₀ δ ×ˢ Set.Ioo (-δ) δ := ⟨hx, neg_lt_zero.mpr hδ, hδ⟩
    have hx' : x ∈ Metric.closedBall x₀ (r : ℝ) := Metric.ball_subset_closedBall (hs hx₀).1.1
    refine ⟨(hα x hx').1, ?_⟩
    intro t ht
    have hq : (x, t) ∈ Metric.ball x₀ δ ×ˢ Set.Ioo (-δ) δ := ⟨hx, ht⟩
    refine ⟨(hs hq).2, ?_⟩
    have ht' := (hs hq).1.2
    exact ((hα x hx').2 t (Set.Ioo_subset_Icc_self ht')).hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)

private def
    Smale.FlowConstruction.coordinateField {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (v : (x : M) → TangentSpace 𝓘(ℝ, E) x) (p : M) (y : E) : E :=
  tangentCoordChange 𝓘(ℝ, E) ((chartAt E p).symm y) p ((chartAt E p).symm y)
    (v ((chartAt E p).symm y))

private theorem
    Smale.FlowConstruction.contDiffAt_coordinateField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p : M}
    (hv :
      ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)) p) :
    ContDiffAt ℝ 1 (coordinateField v p) (chartAt E p p) := by
  rw [contMDiffAt_iff] at hv
  have h :=
    hv.2.contDiffAt
      (range_mem_nhds_isInteriorPoint (I := 𝓘(ℝ, E))
        (BoundarylessManifold.isInteriorPoint (x := p)))
  convert h.snd using 1 <;> rfl

private theorem
    Smale.FlowConstruction.coordinateField_eq_mfderiv {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (v : (x : M) → TangentSpace 𝓘(ℝ, E) x) (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    coordinateField v p y =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p) ((chartAt E p).symm y) (v ((chartAt E p).symm y)) := by
  rw [mfderiv_chartAt_eq_tangentCoordChange ((chartAt E p).map_target hy)]
  rfl

private theorem
    Smale.FlowConstruction.mfderiv_symm_coordinateField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (v : (x : M) → TangentSpace 𝓘(ℝ, E) x) (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y
        ((NormedSpace.fromTangentSpace y).symm (coordinateField v p y)) =
      v ((chartAt E p).symm y) := by
  let e := chartAt E p
  have he := (mdifferentiable_chart (I := 𝓘(ℝ, E)) p).symm_comp_deriv (e.map_target hy)
  rw [e.right_inv hy] at he
  rw [coordinateField_eq_mfderiv v p hy]
  exact congrArg (fun A : E →L[ℝ] E => A (v (e.symm y))) he

private theorem Smale.FlowConstruction.hasMFDerivAt_lift_coordinateCurve {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p : M} {α : ℝ → E} {t : ℝ}
    (hα : HasDerivAt α (coordinateField v p (α t)) t) (ht : α t ∈ (chartAt E p).target) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((chartAt E p).symm ∘ α) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v ((chartAt E p).symm (α t)))) := by
  have hi := ((mdifferentiable_chart (I := 𝓘(ℝ, E)) p).mdifferentiableAt_symm ht).hasMFDerivAt
  have h := hi.comp t hα.hasFDerivAt.hasMFDerivAt
  apply h.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm (α t))
        ((NormedSpace.fromTangentSpace t a) •
          (NormedSpace.fromTangentSpace (α t)).symm (coordinateField v p (α t))) =
      (NormedSpace.fromTangentSpace t a) • v ((chartAt E p).symm (α t))
  rw [map_smul, mfderiv_symm_coordinateField v p ht]

private theorem Smale.FlowConstruction.exists_manifoldLocalFlow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} (p : M)
    (hv :
      ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)) p) :
    ∃ U : Set M,
      IsOpen U ∧
        p ∈ U ∧
          ∃ ε > (0 : ℝ),
            ∃ F : M × ℝ → M,
              ContinuousOn F (U ×ˢ Set.Ioo (-ε) ε) ∧
                ∀ x ∈ U,
                  F (x, 0) = x ∧ IsMIntegralCurveOn (fun t => F (x, t)) v (Set.Ioo (-ε) ε) := by
  let e := chartAt E p
  obtain ⟨r, hr, ε, hε, α, hαc, hα⟩ :=
    exists_localFlow_in_open (contDiffAt_coordinateField hv) e.open_target
      (e.map_source (mem_chart_source E p))
  let U : Set M := e.source ∩ e ⁻¹' Metric.ball (e p) r
  have hU : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
  have hpU : p ∈ U := ⟨mem_chart_source E p, Metric.mem_ball_self hr⟩
  let F : M × ℝ → M := fun q => e.symm (α (e q.1, q.2))
  have hc : ContinuousOn (fun q : M × ℝ => (e q.1, q.2)) (U ×ˢ Set.Ioo (-ε) ε) :=
    (e.continuousOn.comp continuous_fst.continuousOn (fun _ hq => hq.1.1)).prodMk
      continuous_snd.continuousOn
  have hd :
    Set.MapsTo (fun q : M × ℝ => (e q.1, q.2)) (U ×ˢ Set.Ioo (-ε) ε)
      (Metric.ball (e p) r ×ˢ Set.Ioo (-ε) ε) :=
    fun _ hq => ⟨hq.1.2, hq.2⟩
  have hFc : ContinuousOn F (U ×ˢ Set.Ioo (-ε) ε) :=
    e.symm.continuousOn.comp (hαc.comp hc hd) (fun q hq => ((hα (e q.1) hq.1.2).2 q.2 hq.2).1)
  refine ⟨U, hU, hpU, ε, hε, F, hFc, ?_⟩
  intro x hx
  refine ⟨?_, ?_⟩
  · change e.symm (α (e x, 0)) = x
    rw [(hα (e x) hx.2).1, e.left_inv hx.1]
  · intro t ht
    have hcurve := (hα (e x) hx.2).2 t ht
    exact (hasMFDerivAt_lift_coordinateCurve hcurve.2 hcurve.1).hasMFDerivWithinAt

private theorem
    Smale.FlowConstruction.exists_uniformIntegralCurves {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ∃ ε > (0 : ℝ), ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) := by
  classical
  choose U hU hp ε hε F hFc hF using fun p : M => exists_manifoldLocalFlow p (hv p)
  obtain ⟨s, hs⟩ :=
    isCompact_univ.elim_finite_subcover U hU (fun x _ => Set.mem_iUnion.mpr ⟨x, hp x⟩)
  have hN : (⋂ p ∈ s, Set.Ioo (-(ε p)) (ε p)) ∈ 𝓝 (0 : ℝ) :=
    (Filter.biInter_finset_mem s).mpr fun p _ => Ioo_mem_nhds (neg_lt_zero.mpr (hε p)) (hε p)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨δ, hδ, ?_⟩
  intro x
  obtain ⟨p, hps, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  refine ⟨fun t => F p (x, t), (hF p x hx).1, (hF p x hx).2.mono ?_⟩
  intro t ht
  apply Set.mem_iInter₂.mp (hδsub ?_) p hps
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht

private theorem
    Smale.FlowConstruction.exists_globalIntegralCurve {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : M) : ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨ε, hε, h⟩ := exists_uniformIntegralCurves hv
  exact exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε h x

private def Smale.FlowConstruction.flow {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (t : ℝ) (x : M) : M :=
  (exists_globalIntegralCurve hv x).choose t

@[simp]
private theorem
    Smale.FlowConstruction.flow_zero {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : M) : flow hv 0 x = x :=
  (exists_globalIntegralCurve hv x).choose_spec.1

private theorem Smale.FlowConstruction.isMIntegralCurve_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : M) : IsMIntegralCurve (fun t => flow hv t x) v :=
  (exists_globalIntegralCurve hv x).choose_spec.2

private theorem
    Smale.FlowConstruction.flow_add {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (s t : ℝ) (x : M) : flow hv (s + t) x = flow hv s (flow hv t x) := by
  have h₁ := (isMIntegralCurve_flow hv x).comp_add t
  have h₂ := isMIntegralCurve_flow hv (flow hv t x)
  have heq :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv h₁ h₂ (t₀ := 0)
      (by simp only [Function.comp_apply, zero_add, flow_zero])
  exact congrFun heq s

private theorem Smale.FlowConstruction.flow_eq_local {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {U : Set M} {ε : ℝ} (hε : 0 < ε) {F : M × ℝ → M}
    (hF : ∀ x ∈ U, F (x, 0) = x ∧ IsMIntegralCurveOn (fun t => F (x, t)) v (Set.Ioo (-ε) ε))
    {x : M} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo (-ε) ε) : flow hv t x = F (x, t) :=
  isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := 0) ⟨neg_lt_zero.mpr hε, hε⟩ hv
    ((isMIntegralCurve_flow hv x).isMIntegralCurveOn _) (hF x hx).2
    ((flow_zero hv x).trans (hF x hx).1.symm) ht

private theorem Smale.FlowConstruction.exists_continuousOn_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (p : M) :
    ∃ U : Set M,
      IsOpen U ∧
        p ∈ U ∧ ∃ ε > (0 : ℝ), ContinuousOn (Function.uncurry (flow hv)) (Set.Ioo (-ε) ε ×ˢ U) := by
  obtain ⟨U, hU, hp, ε, hε, F, hFc, hF⟩ := exists_manifoldLocalFlow p (hv p)
  refine ⟨U, hU, hp, ε, hε, ?_⟩
  have hc : ContinuousOn (fun q : ℝ × M => F (q.2, q.1)) (Set.Ioo (-ε) ε ×ˢ U) :=
    hFc.comp continuous_swap.continuousOn (fun _ hq => ⟨hq.2, hq.1⟩)
  exact hc.congr (fun q hq => flow_eq_local hv hε hF hq.2 hq.1)

private theorem
    Smale.FlowConstruction.exists_smalltime_continuous {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ∃ ε > (0 : ℝ), ∀ t ∈ Set.Ioo (-ε) ε, Continuous (flow hv t) := by
  classical
  choose U hU hp ε hε hF using exists_continuousOn_flow hv
  obtain ⟨s, hs⟩ :=
    isCompact_univ.elim_finite_subcover U hU (fun x _ => Set.mem_iUnion.mpr ⟨x, hp x⟩)
  have hN : (⋂ p ∈ s, Set.Ioo (-(ε p)) (ε p)) ∈ 𝓝 (0 : ℝ) :=
    (Filter.biInter_finset_mem s).mpr fun p _ => Ioo_mem_nhds (neg_lt_zero.mpr (hε p)) (hε p)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have htall : t ∈ ⋂ p ∈ s, Set.Ioo (-(ε p)) (ε p) :=
    hδsub (by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht)
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨p, hps, hxp⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  have htp := Set.mem_iInter₂.mp htall p hps
  exact
    ((hF p).continuousAt (prod_mem_nhds (Ioo_mem_nhds htp.1 htp.2) ((hU p).mem_nhds hxp))).comp
      (continuousAt_const.prodMk continuousAt_id)

private theorem Smale.FlowConstruction.continuous_flow_time {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (t : ℝ) : Continuous (flow hv t) := by
  obtain ⟨ε, hε, hsmall⟩ := exists_smalltime_continuous hv
  let S : Set ℝ := {s | Continuous (flow hv s)}
  have hstep {s u : ℝ} (hs : s ∈ S) (hu : Dist.dist u s < ε) : u ∈ S := by
    have hus : u - s ∈ Set.Ioo (-ε) ε := by
      exact abs_lt.mp (by simpa only [Real.dist_eq] using hu)
    have hc := (hsmall (u - s) hus).comp hs
    have heq : (fun x => flow hv (u - s) (flow hv s x)) = flow hv u := by
      funext x
      rw [← flow_add, sub_add_cancel]
    change Continuous (flow hv u)
    rw [← heq]
    exact hc
  have hS : IsOpen S :=
    isOpen_iff_mem_nhds.mpr fun s hs =>
      Filter.mem_of_superset (Metric.ball_mem_nhds s hε) (fun u hu => hstep hs hu)
  have hSc : IsOpen Sᶜ :=
    isOpen_iff_mem_nhds.mpr fun s hs =>
      Filter.mem_of_superset (Metric.ball_mem_nhds s hε)
        (fun u hu h =>
          hs
            (hstep h
              (by
                change Dist.dist u s < ε at hu
                rwa [dist_comm])))
  have hzero : (0 : ℝ) ∈ S := by
    change Continuous (flow hv 0)
    have heq : flow hv 0 = id := funext (flow_zero hv)
    rw [heq]
    exact continuous_id
  have hSuniv : S = Set.univ :=
    (show IsClopen S from ⟨isOpen_compl_iff.mp hSc, hS⟩).eq_univ ⟨0, hzero⟩
  change t ∈ S
  rw [hSuniv]
  exact Set.mem_univ t

private theorem Smale.FlowConstruction.continuous_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    Continuous (Function.uncurry (flow hv)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨U, hU, hp, ε, hε, hF⟩ := exists_continuousOn_flow hv (flow hv q.1 q.2)
  have hzero :=
    hF.continuousAt (prod_mem_nhds (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε) (hU.mem_nhds hp))
  have hmap : ContinuousAt (fun r : ℝ × M => (r.1 - q.1, flow hv q.1 r.2)) q :=
    (continuousAt_fst.sub continuousAt_const).prodMk
      ((continuous_flow_time hv q.1).continuousAt.comp continuousAt_snd)
  have hzero' :
    ContinuousAt (Function.uncurry (flow hv))
      ((fun r : ℝ × M => (r.1 - q.1, flow hv q.1 r.2)) q) := by simpa only [sub_self] using hzero
  have hcomp := hzero'.comp (f := fun r : ℝ × M => (r.1 - q.1, flow hv q.1 r.2)) hmap
  have heq :
    (fun r : ℝ × M => flow hv (r.1 - q.1) (flow hv q.1 r.2)) = Function.uncurry (flow hv) := by
    funext r
    rw [← flow_add, sub_add_cancel]
    rfl
  exact heq ▸ hcomp

private def
    Smale.FlowConstruction.compactFlow {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
    [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    Flow ℝ M where
  toFun := flow hv
  cont' := continuous_flow hv
  map_add' := flow_add hv
  map_zero' := flow_zero hv

private theorem
    Smale.FlowConstruction.isMIntegralCurve_compactFlow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [CompactSpace M] {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : M) : IsMIntegralCurve (fun t => compactFlow hv t x) v :=
  isMIntegralCurve_flow hv x

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_disjoint_morse_block_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f) {ι : Type*}
    [Finite ι] (p : ι → M) (hp : ∀ i, p i ∈ Smale.ManifoldMorse.criticalPoints E f)
    (c : ∀ i, Smale.ManifoldMorse.SignedMorseChart (E := E) f (p i)) (R : ι → ℝ)
    (hblock :
      ∀ i,
        Metric.closedBall (0 : (c i).NegativeCoordinates) (R i) ×ˢ
            Metric.closedBall (0 : (c i).PositiveCoordinates) (R i) ⊆
          (c i).splitChart.target)
    (hintervals :
      Pairwise
        (fun i j =>
          Disjoint (Set.Icc (f (p i) - R i ^ 2) (f (p i) + R i ^ 2))
            (Set.Icc (f (p j) - R j ^ 2) (f (p j) + R j ^ 2)))) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (F : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, IsMIntegralCurve (fun t => F t x) V) ∧
          (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0) ∧
            (∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
              ∀ i (z : (c i).NegativeCoordinates × (c i).PositiveCoordinates),
                ‖z.1‖ < R i →
                  ‖z.2‖ < R i → ∀ᶠ y in 𝓝 ((c i).splitChart.symm z), V y = (c i).descentField y :=
  by
  let K := fun i => morseClosedBlock (c i) (R i)
  have hK (i : ι) : IsClosed (K i) := (isCompact_morseClosedBlock (c i) (R i) (hblock i)).isClosed
  have hKsource (i : ι) : K i ⊆ (c i).splitChart.source :=
    morseClosedBlock_subset_source (c i) (R i) (hblock i)
  have hdisj : Pairwise (fun i j => Disjoint (K i) (K j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact
      Set.disjoint_left.mp (hintervals hij) (morseClosedBlock_height (c i) (R i) (hblock i) hxi)
        (morseClosedBlock_height (c j) (R j) (hblock j) hxj)
  obtain ⟨V, hV, hzero, hdesc, hmatch⟩ :=
    exists_prescribed_morse_patch_field hf hm p hp c K hK hKsource hdisj
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  let F := Smale.FlowConstruction.compactFlow hV₁
  refine ⟨V, F, hV, Smale.FlowConstruction.isMIntegralCurve_compactFlow hV₁, hzero, hdesc, ?_⟩
  intro i z hn hp
  filter_upwards [morseClosedBlock_mem_nhds (c i) (R i) (hblock i) hn hp] with y hy
  exact hmatch i y hy

private theorem MorseCancel.exists_larger_closedBall_inside_open {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [ProperSpace A] {U : Set A} (hU : IsOpen U) {R B : ℝ} (hR : 0 ≤ R)
    (hRB : R < B) (hsub : Metric.closedBall (0 : A) R ⊆ U) :
    ∃ S, R < S ∧ S < B ∧ Metric.closedBall (0 : A) S ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ :=
    (ProperSpace.isCompact_closedBall (0 : A) R).exists_cthickening_subset_open hU hsub
  rw [cthickening_closedBall hδ.le hR] at hδU
  obtain ⟨S, hRS, hSm⟩ := exists_between (lt_min (by linarith : R < δ + R) hRB)
  exact
    ⟨S, hRS, hSm.trans_le (min_le_right _ _),
      (Metric.closedBall_subset_closedBall (hSm.le.trans (min_le_left _ _))).trans hδU⟩

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_morse_block_enlargement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {r : ℝ} (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target) :
    ∃ R,
      2 * r < R ∧
        R < 3 * r ∧
          Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
              Metric.closedBall (0 : c.PositiveCoordinates) R ⊆
            c.splitChart.target := by
  have hb :
    Metric.closedBall (0 : c.NegativeCoordinates × c.PositiveCoordinates) (2 * r) ⊆
      c.splitChart.target := by simpa only [closedBall_prod_same, Prod.mk_zero_zero] using hblock
  obtain ⟨R, hR, hR', hsub⟩ :=
    exists_larger_closedBall_inside_open c.splitChart.open_target (by positivity : 0 ≤ 2 * r)
      (by linarith : 2 * r < 3 * r) hb
  refine ⟨R, hR, hR', ?_⟩
  simpa only [closedBall_prod_same, Prod.mk_zero_zero] using hsub

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_disjoint_surgery_block_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f) {ι : Type*}
    [Finite ι] (p : ι → M) (hp : ∀ i, p i ∈ Smale.ManifoldMorse.criticalPoints E f)
    (c : ∀ i, Smale.ManifoldMorse.SignedMorseChart (E := E) f (p i)) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i)
    (hblock :
      ∀ i,
        Metric.closedBall (0 : (c i).NegativeCoordinates) (2 * r i) ×ˢ
            Metric.closedBall (0 : (c i).PositiveCoordinates) (2 * r i) ⊆
          (c i).splitChart.target)
    (hintervals :
      Pairwise
        (fun i j =>
          Disjoint (Set.Icc (f (p i) - 9 * r i ^ 2) (f (p i) + 9 * r i ^ 2))
            (Set.Icc (f (p j) - 9 * r j ^ 2) (f (p j) + 9 * r j ^ 2)))) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (F : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, IsMIntegralCurve (fun t => F t x) V) ∧
          (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0) ∧
            (∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
              ∀ i z,
                z ∈
                    Metric.closedBall (0 : (c i).NegativeCoordinates) (2 * r i) ×ˢ
                      Metric.closedBall (0 : (c i).PositiveCoordinates) (2 * r i) →
                  ∀ᶠ y in 𝓝 ((c i).splitChart.symm z), V y = (c i).descentField y := by
  choose R hR hR' hlarge using fun i => exists_morse_block_enlargement (c i) (hr i) (hblock i)
  have hRpos (i : ι) : 0 < R i := (mul_pos (show (0 : ℝ) < 2 by norm_num) (hr i)).trans (hR i)
  have hsq (i : ι) : R i ^ 2 < 9 * r i ^ 2 := by
    have hh :=
      mul_pos (sub_pos.mpr (hR' i))
        (add_pos (mul_pos (show (0 : ℝ) < 3 by norm_num) (hr i)) (hRpos i))
    nlinarith
  have hsub (i : ι) :
    Set.Icc (f (p i) - R i ^ 2) (f (p i) + R i ^ 2) ⊆
      Set.Icc (f (p i) - 9 * r i ^ 2) (f (p i) + 9 * r i ^ 2) := by
    intro v hv
    constructor <;> linarith [hv.1, hv.2, hsq i]
  obtain ⟨V, F, hV, hF, hzero, hdesc, hmatch⟩ :=
    exists_disjoint_morse_block_field hf hm p hp c R hlarge
      (fun i j hij => (hintervals hij).mono (hsub i) (hsub j))
  refine ⟨V, F, hV, hF, hzero, hdesc, ?_⟩
  intro i z hz
  exact
    hmatch i z ((mem_closedBall_zero_iff.mp hz.1).trans_lt (hR i))
      ((mem_closedBall_zero_iff.mp hz.2).trans_lt (hR i))

private theorem
    NoExotic.exists_partialDiffeomorph_of_contDiffOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {U : Set E} {x : E} (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hinv : (fderiv ℝ f x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ (Φ : E → F) = f := by
  have hfx := hf.contDiffAt (hU.mem_nhds hx)
  obtain ⟨A, hA⟩ := hinv
  have hfd : HasFDerivAt f (A : E →L[ℝ] F) x := by
    rw [hA]
    exact (hfx.differentiableAt (by simp)).hasFDerivAt
  let g := hfx.toOpenPartialHomeomorph f hfd (by simp)
  let W := U ∩ interior {y | (fderiv ℝ f y).IsInvertible}
  have hW : IsOpen W := hU.inter isOpen_interior
  have hxW : x ∈ W := by
    refine ⟨hx, mem_interior_iff_mem_nhds.mpr ?_⟩
    have ho : IsOpen {L : E →L[ℝ] F | L.IsInvertible} := ContinuousLinearEquiv.isOpen
    exact (hfx.continuousAt_fderiv (by simp)) (ho.mem_nhds ⟨A, hA⟩)
  let r := g.restrOpen W hW
  have hsource : r.source ⊆ U := fun _ h ↦ h.2.1
  have hto : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ r r.source := (hf.mono hsource).contMDiffOn
  have hsymm : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r.symm r.target := by
    intro y hy
    have hys := r.map_target hy
    have hiy : (fderiv ℝ f (r.symm y)).IsInvertible :=
      interior_subset (s := {z : E | (fderiv ℝ f z).IsInvertible}) hys.2.2
    obtain ⟨Ay, hAy⟩ := hiy
    have hfy : ContDiffAt ℝ ∞ f (r.symm y) := hf.contDiffAt (hU.mem_nhds hys.2.1)
    have hfdy : HasFDerivAt r (Ay : E →L[ℝ] F) (r.symm y) := by
      change HasFDerivAt f (Ay : E →L[ℝ] F) (r.symm y)
      rw [hAy]
      exact (hfy.differentiableAt (by simp)).hasFDerivAt
    exact (r.contDiffAt_symm hy hfdy hfy).contMDiffAt.contMDiffWithinAt
  refine
    ⟨{ r.toPartialEquiv with
        open_source := r.open_source
        open_target := r.open_target
        contMDiffOn_toFun := hto
        contMDiffOn_invFun := hsymm },
      ?_, hsource, rfl⟩
  exact ⟨hfx.mem_toOpenPartialHomeomorph_source hfd (by simp), hxW⟩

private def
    NoExotic.tangentModelEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H M : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (x : M) : TangentSpace I x ≃L[ℝ] E where
  toFun v := v
  invFun v := v
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

private noncomputable def NoExotic.modelChartPartialDiffeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] (x : M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E ∞
    where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using (contMDiffOn_extChartAt (I := I) (x := x) (n := ∞))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

private theorem
    NoExotic.isLocalDiffeomorphAt_of_invertible_mvfderiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {H M : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] {f : M → F} {x : M} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f)
    (hinv : (mvfderiv I f x).IsInvertible) : IsLocalDiffeomorphAt I 𝓘(ℝ, F) ∞ f x := by
  let c := modelChartPartialDiffeomorph (I := I) x
  let fc : E → F := f ∘ c.symm
  have hfc : ContDiffOn ℝ ∞ fc c.target := (hf.comp_contMDiffOn c.contMDiffOn_invFun).contDiffOn
  have hc : x ∈ c.source := mem_extChartAt_source x
  have hderiv : mvfderiv I f x = fderiv ℝ fc (c x) := by
    simpa [fc, c, modelChartPartialDiffeomorph, writtenInExtChartAt, extChartAt_self_eq,
      chartAt_self_eq, ModelWithCorners.range_eq_univ] using
      (hf.mdifferentiable (by simp) x).mvfderiv
  have hfcinv : (fderiv ℝ fc (c x)).IsInvertible := by
    obtain ⟨A, hA⟩ := hinv
    refine ⟨(tangentModelEquiv (I := I) x).symm.trans A, ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L : TangentSpace I x →L[ℝ] F ↦ L v) (hA.trans hderiv)
  obtain ⟨d, hd, _, hdf⟩ :=
    exists_partialDiffeomorph_of_contDiffOn c.open_target (c.map_source' hc) hfc hfcinv
  refine ⟨c.trans d, ⟨hc, hd⟩, ?_⟩
  intro y hy
  change f y = d (c y)
  rw [hdf]
  change f y = f (c.symm (c y))
  exact (congrArg f (c.left_inv' hy.1)).symm

private theorem Smale.RegularLevel.surjective_of_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {L : E →L[ℝ] ℝ} (hL : L ≠ 0) : Function.Surjective L := by
  have hex : ∃ v, L v ≠ 0 := by
    by_contra! h
    exact hL (ContinuousLinearMap.ext h)
  obtain ⟨v, hv⟩ := hex
  intro r
  refine ⟨(r / L v) • v, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]

private theorem Smale.RegularLevel.finrank_kernel_add_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {L : E →L[ℝ] ℝ} (hL : L ≠ 0) :
    Module.finrank ℝ L.ker + 1 = Module.finrank ℝ E := by
  have hr : L.range = ⊤ := LinearMap.range_eq_top.mpr (surjective_of_ne_zero hL)
  have hdim := L.toLinearMap.finrank_range_add_finrank_ker
  change Module.finrank ℝ L.range + Module.finrank ℝ L.ker = Module.finrank ℝ E at hdim
  rw [hr, finrank_top, Module.finrank_self] at hdim
  omega

private theorem
    Smale.RegularLevel.exists_height_partialDiffeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {U : Set E} {x : E} (hU : IsOpen U)
    (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U) (hreg : fderiv ℝ f x ≠ 0) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × (fderiv ℝ f x).ker) E (ℝ × (fderiv ℝ f x).ker) ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ (∀ y, (Φ y).1 = f y) ∧ Φ x = (f x, 0) := by
  let L := fderiv ℝ f x
  have hs : HasStrictFDerivAt f L x :=
    (hf.contDiffAt (hU.mem_nhds hx)).hasStrictFDerivAt (by simp)
  have hr : L.range = ⊤ := LinearMap.range_eq_top.mpr (surjective_of_ne_zero hreg)
  have hk : L.ker.ClosedComplemented := L.ker_closedComplemented_of_finiteDimensional_range
  let φ := hs.implicitFunctionDataOfComplemented f L hr hk
  have hg : ContDiffOn ℝ ∞ φ.prodFun U := by
    apply hf.prodMk
    change ContDiffOn ℝ ∞ (fun y => Classical.choose hk (y - x)) U
    exact (Classical.choose hk).contDiff.comp_contDiffOn (contDiffOn_id.sub contDiffOn_const)
  obtain ⟨Φ, hΦ, hΦU, hΦf⟩ :=
    NoExotic.exists_partialDiffeomorph_of_contDiffOn hU hx hg φ.isInvertible_fderiv_prodFun
  refine ⟨Φ, hΦ, hΦU, ?_, ?_⟩
  · intro y
    rw [hΦf]
    rfl
  · rw [hΦf]
    change (f x, Classical.choose hk (x - x)) = (f x, 0)
    simp

private abbrev Smale.RegularLevel.Model (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))

private theorem Smale.RegularLevel.exists_native_height_chart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × Model E) M (ℝ × Model E) ∞,
      x ∈ Φ.source ∧ (∀ y ∈ Φ.source, (Φ y).1 = f y) ∧ Φ x = (f x, 0) := by
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hxe : x ∈ e.source := mem_chart_source E x
  let c : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞ :=
    { e.toPartialEquiv with
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
  have hreg : fderiv ℝ (f ∘ e.symm) (e x) ≠ 0 := fun h =>
    hx ((Smale.ManifoldMorse.mem_criticalPoints_iff hf he hxe).mpr h)
  obtain ⟨d, hd, -, hfirst, hcenter⟩ :=
    exists_height_partialDiffeomorph e.open_target (e.map_source hxe)
      (Smale.ManifoldMorse.contDiffOn_chartExpression hf he) hreg
  let L := fderiv ℝ (f ∘ e.symm) (e x)
  have hdim : Module.finrank ℝ L.ker = Module.finrank ℝ (Model E) := by
    have hh := finrank_kernel_add_one hreg
    change Module.finrank ℝ L.ker + 1 = Module.finrank ℝ E at hh
    rw [finrank_euclideanSpace_fin]
    omega
  let j : L.ker ≃L[ℝ] Model E := ContinuousLinearEquiv.ofFinrankEq hdim
  let J : (ℝ × L.ker) ≃L[ℝ] (ℝ × Model E) := (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr j
  let τ := J.toDiffeomorph.toPartialDiffeomorph
  refine ⟨(c.trans d).trans τ, ⟨⟨hxe, hd⟩, Set.mem_univ _⟩, ?_, ?_⟩
  · intro y hy
    change (d (e y)).1 = f y
    rw [hfirst]
    exact congrArg f (e.left_inv hy.1.1)
  · change J (d (e x)) = (f x, 0)
    rw [hcenter]
    change (f (e.symm (e x)), j 0) = (f x, 0)
    rw [e.left_inv hxe, map_zero]

private theorem
    Smale.RegularLevel.inverse_height {M D : Type*} [TopologicalSpace M] [TopologicalSpace D]
    {f : M → ℝ} {b : ℝ} (e : OpenPartialHomeomorph M (ℝ × D)) (he : ∀ y ∈ e.source, (e y).1 = f y)
    {v : D} (hv : (b, v) ∈ e.target) : f (e.symm (b, v)) = b := by
  have h := he (e.symm (b, v)) (e.map_target hv)
  rw [e.right_inv hv] at h
  exact h.symm

attribute [local instance 100] Classical.propDecidable in
private def Smale.RegularLevel.sliceInverse {M D : Type*} [TopologicalSpace M] [TopologicalSpace D]
    {f : M → ℝ} {b : ℝ} (e : OpenPartialHomeomorph M (ℝ × D)) (he : ∀ y ∈ e.source, (e y).1 = f y)
    (base : { x : M // f x = b }) (v : D) : { x : M // f x = b } :=
  if hv : (b, v) ∈ e.target then ⟨e.symm (b, v), inverse_height e he hv⟩ else base

attribute [local instance 100] Classical.propDecidable in
private def Smale.RegularLevel.sliceChart {M D : Type*} [TopologicalSpace M] [TopologicalSpace D]
    {f : M → ℝ} {b : ℝ} (e : OpenPartialHomeomorph M (ℝ × D)) (he : ∀ y ∈ e.source, (e y).1 = f y)
    (base : { x : M // f x = b }) : OpenPartialHomeomorph { x : M // f x = b } D
    where
  toFun x := (e x).2
  invFun := sliceInverse e he base
  source := {x | (x : M) ∈ e.source}
  target := {v | (b, v) ∈ e.target}
  map_source' := by
    intro x hx
    have hp : (b, (e x).2) = e x := Prod.ext ((he x hx).trans x.property).symm rfl
    change (b, (e x).2) ∈ e.target
    rw [hp]
    exact e.map_source hx
  map_target' := by
    intro v hv
    change (b, v) ∈ e.target at hv
    change (sliceInverse e he base v : M) ∈ e.source
    simp only [sliceInverse, dite_eq_left hv]
    exact e.map_target hv
  left_inv' := by
    intro x hx
    have hp : (b, (e x).2) = e x := Prod.ext ((he x hx).trans x.property).symm rfl
    have ht : (b, (e x).2) ∈ e.target := hp ▸ e.map_source hx
    simp only [sliceInverse, dite_eq_left ht]
    apply Subtype.ext
    change e.symm (b, (e x).2) = x
    rw [hp]
    exact e.left_inv hx
  right_inv' := by
    intro v hv
    change (b, v) ∈ e.target at hv
    simp only [sliceInverse, dite_eq_left hv]
    rw [e.right_inv hv]
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun :=
    continuous_snd.comp_continuousOn
      (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx))
  continuousOn_invFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply
      (e.symm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun _ hv => hv)).congr
    intro v hv
    change (b, v) ∈ e.target at hv
    simp only [Function.comp_apply, sliceInverse, dite_eq_left hv]
    rfl

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.RegularLevel.sliceChart_symm_coe {M D : Type*} [TopologicalSpace M]
    [TopologicalSpace D] {f : M → ℝ} {b : ℝ} (e : OpenPartialHomeomorph M (ℝ × D))
    (he : ∀ y ∈ e.source, (e y).1 = f y) (base : { x : M // f x = b }) {v : D}
    (hv : v ∈ (sliceChart e he base).target) :
    ((sliceChart e he base).symm v : M) = e.symm (b, v) := by
  change (b, v) ∈ e.target at hv
  change (sliceInverse e he base v : M) = _
  simp only [sliceInverse, dite_eq_left hv]

private theorem
    Smale.RegularLevel.contDiffOn_slice_transition {E D M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace M]
    [ChartedSpace E M] {f : M → ℝ} {b : ℝ}
    (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × D) M (ℝ × D) ∞)
    (hΦ : ∀ y ∈ Φ.source, (Φ y).1 = f y) (hΨ : ∀ y ∈ Ψ.source, (Ψ y).1 = f y)
    (x y : { z : M // f z = b }) :
    let c := sliceChart Φ.toOpenPartialHomeomorph hΦ x
    let d := sliceChart Ψ.toOpenPartialHomeomorph hΨ y
    ContDiffOn ℝ ∞ (c.symm.trans d) (c.symm.trans d).source := by
  let c := sliceChart Φ.toOpenPartialHomeomorph hΦ x
  let d := sliceChart Ψ.toOpenPartialHomeomorph hΨ y
  let S := (c.symm.trans d).source
  have hS (v : D) (hv : v ∈ S) : (b, v) ∈ Φ.target ∧ Φ.symm (b, v) ∈ Ψ.source := by
    refine ⟨hv.1, ?_⟩
    have hh : (c.symm v : M) ∈ Ψ.source := hv.2
    rwa [sliceChart_symm_coe Φ.toOpenPartialHomeomorph hΦ x hv.1] at hh
  have hfirst : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (fun v => Φ.symm (b, v)) S :=
    Φ.contMDiffOn_invFun.comp ((contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn)
      (fun v hv => (hS v hv).1)
  have hsecond := Ψ.contMDiffOn_toFun.comp hfirst (fun v hv => (hS v hv).2)
  have hfull : ContDiffOn ℝ ∞ (fun v => (Ψ (Φ.symm (b, v))).2) S :=
    (contDiff_snd.contMDiff.comp_contMDiffOn hsecond).contDiffOn
  apply hfull.congr
  intro v hv
  change (Ψ (c.symm v : M)).2 = (Ψ (Φ.symm (b, v))).2
  rw [sliceChart_symm_coe Φ.toOpenPartialHomeomorph hΦ x hv.1]
  rfl

private def Smale.RegularLevel.heightChart {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (x : { x : M // f x = b }) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × Model E) M (ℝ × Model E) ∞ :=
  Classical.choose (exists_native_height_chart hf (hreg x x.property))

private theorem Smale.RegularLevel.heightChart_mem_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (x : { x : M // f x = b }) : (x : M) ∈ (heightChart hf hreg x).source :=
  (Classical.choose_spec (exists_native_height_chart hf (hreg x x.property))).1

private theorem Smale.RegularLevel.heightChart_height {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (x : { x : M // f x = b }) :
    ∀ y ∈ (heightChart hf hreg x).source, (heightChart hf hreg x y).1 = f y :=
  (Classical.choose_spec (exists_native_height_chart hf (hreg x x.property))).2.1

private def Smale.RegularLevel.levelChart {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (x : { x : M // f x = b }) : OpenPartialHomeomorph { x : M // f x = b } (Model E) :=
  sliceChart (heightChart hf hreg x).toOpenPartialHomeomorph (heightChart_height hf hreg x) x

@[instance_reducible]
private def Smale.RegularLevel.chartedSpace {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ChartedSpace (Model E) { x : M // f x = b }
    where
  atlas := Set.range (levelChart hf hreg)
  chartAt := levelChart hf hreg
  mem_chart_source := heightChart_mem_source hf hreg
  chart_mem_atlas := fun x => ⟨x, rfl⟩

private theorem Smale.RegularLevel.isManifold {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    letI := chartedSpace hf hreg
    IsManifold 𝓘(ℝ, Model E) ∞ { x : M // f x = b } := by
  let _ := chartedSpace hf hreg
  apply isManifold_of_contDiffOn
  intro c d hc hd
  obtain ⟨x, rfl⟩ := hc
  obtain ⟨y, rfl⟩ := hd
  simpa only [mfld_simps, levelChart] using
    contDiffOn_slice_transition (heightChart hf hreg x) (heightChart hf hreg y)
      (heightChart_height hf hreg x) (heightChart_height hf hreg y) x y

private theorem Smale.RegularLevel.contMDiff_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    letI := chartedSpace hf hreg
    ContMDiff 𝓘(ℝ, Model E) 𝓘(ℝ, E) ∞ (Subtype.val : { x : M // f x = b } → M) := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  intro x
  let Φ := heightChart hf hreg x
  let c := levelChart hf hreg x
  have hx : x ∈ c.source := heightChart_mem_source hf hreg x
  have hc : ContMDiffAt 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ∞ c x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hx
  have ht : (b, c x) ∈ Φ.target := c.map_source hx
  have hslice : ContMDiffAt 𝓘(ℝ, Model E) 𝓘(ℝ, E) ∞ (fun v => Φ.symm (b, v)) (c x) :=
    (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds ht)).comp (c x)
      (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt
  have hcomp := hslice.comp x hc
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hx] with y hy
  change (y : M) = Φ.symm (b, c y)
  have heq : (b, c y) = Φ y :=
    Prod.ext ((heightChart_height hf hreg x y hy).trans y.property).symm rfl
  rw [heq]
  exact (Φ.left_inv' hy).symm

private theorem Smale.RegularLevel.contMDiffAt_iff_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) {G H X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
    [TopologicalSpace X] [ChartedSpace H X] (g : X → { x : M // f x = b }) (x : X) :
    letI := chartedSpace hf hreg
    ContMDiffAt I 𝓘(ℝ, Model E) ∞ g x ↔ ContMDiffAt I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) x := by
  let _ := chartedSpace hf hreg
  constructor
  · intro hg
    exact (Smale.RegularLevel.contMDiff_inclusion hf hreg).contMDiffAt.comp x hg
  · intro hg
    apply contMDiffAt_iff_target.mpr
    refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hg.continuousAt, ?_⟩
    let Φ := heightChart hf hreg (g x)
    have hΦ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × Model E) ∞ Φ (g x) :=
      Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (heightChart_mem_source hf hreg (g x)))
    have hcomp := hΦ.comp x hg
    change ContMDiffAt I 𝓘(ℝ, Model E) ∞ (fun y => (Φ (g y)).2) x
    exact contDiff_snd.contMDiff.contMDiffAt.comp x hcomp

private theorem Smale.RegularLevel.contMDiff_iff_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) {G H X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
    [TopologicalSpace X] [ChartedSpace H X] (g : X → { x : M // f x = b }) :
    letI := chartedSpace hf hreg
    ContMDiff I 𝓘(ℝ, Model E) ∞ g ↔ ContMDiff I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) := by
  let _ := chartedSpace hf hreg
  exact forall_congr' (contMDiffAt_iff_inclusion hf hreg I g)

private theorem
    Smale.RegularLevel.injective_mfderiv_of_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) {G H X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
    [TopologicalSpace X] [ChartedSpace H X] (g : X → { x : M // f x = b }) (x : X)
    (hg : ContMDiffAt I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) x)
    (hi : Function.Injective (mfderiv I 𝓘(ℝ, E) (Subtype.val ∘ g) x)) :
    letI := chartedSpace hf hreg
    Function.Injective (mfderiv I 𝓘(ℝ, Model E) g x) := by
  let _ := chartedSpace hf hreg
  have hgl := (contMDiffAt_iff_inclusion hf hreg I g x).mpr hg
  have hv := (Smale.RegularLevel.contMDiff_inclusion hf hreg).contMDiffAt (x := g x)
  rw [mfderiv_comp x (hv.mdifferentiableAt (by simp)) (hgl.mdifferentiableAt (by simp))] at hi
  exact fun v w hvw =>
    hi
      (congrArg (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) (g x))
        hvw)

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.SignedMorseChart.attachingHandleMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    C(Smale.MorseHandle.UnitDisk c.NegativeCoordinates ×
        Smale.MorseHandle.UnitDisk c.PositiveCoordinates,
      M)
    where
  toFun z := c.splitChart.symm (Smale.MorseHandle.modelMap ρ z)
  continuous_toFun :=
    c.splitChart.toOpenPartialHomeomorph.symm.continuousOn.comp_continuous
      (Smale.MorseHandle.continuous_modelMap ρ)
      (fun z => hblock (Smale.MorseHandle.modelMap_mem_product hρ z))

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.attachingHandleMap_injective {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Function.Injective (c.attachingHandleMap ρ hρ hblock) := by
  intro z w h
  apply Smale.MorseHandle.modelMap_injective hρ
  exact
    c.splitChart.toOpenPartialHomeomorph.symm.injOn
      (hblock (Smale.MorseHandle.modelMap_mem_product hρ z))
      (hblock (Smale.MorseHandle.modelMap_mem_product hρ w)) h

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.attachingHandleMap_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) [T2Space M] (ρ : ℝ)
    (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Topology.IsClosedEmbedding (c.attachingHandleMap ρ hρ hblock) :=
  (c.attachingHandleMap ρ hρ hblock).continuous.isClosedEmbedding
    (c.attachingHandleMap_injective ρ hρ hblock)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.attachingHandleMap_quadratic {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (z :
      Smale.MorseHandle.UnitDisk c.NegativeCoordinates ×
        Smale.MorseHandle.UnitDisk c.PositiveCoordinates) :
    f (c.attachingHandleMap ρ hρ hblock z) =
      f x +
        (-‖(Smale.MorseHandle.modelMap ρ z).1‖ ^ 2 + ‖(Smale.MorseHandle.modelMap ρ z).2‖ ^ 2) := by
  change f (c.splitChart.symm (Smale.MorseHandle.modelMap ρ z)) = _
  rw [c.splitChart_inverse_equation (hblock (Smale.MorseHandle.modelMap_mem_product hρ z))]
  ring

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.attachingHandleMap_lower_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (z :
      Smale.MorseHandle.UnitDisk c.NegativeCoordinates ×
        Smale.MorseHandle.UnitDisk c.PositiveCoordinates) :
    f (c.attachingHandleMap ρ hρ hblock z) ≤ f x - ρ ^ 2 ↔ ‖(z.1 : c.NegativeCoordinates)‖ = 1 := by
  rw [c.attachingHandleMap_quadratic, sub_eq_add_neg, add_le_add_iff_left]
  exact Smale.MorseHandle.modelMap_lower_iff hρ z

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.attachingHandleMap_upper {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (z :
      Smale.MorseHandle.UnitDisk c.NegativeCoordinates ×
        Smale.MorseHandle.UnitDisk c.PositiveCoordinates) :
    f (c.attachingHandleMap ρ hρ hblock z) ≤ f x + ρ ^ 2 := by
  rw [c.attachingHandleMap_quadratic]
  exact add_le_add le_rfl (Smale.MorseHandle.modelMap_upper hρ z)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.range_attachingHandleMap_mem_nhds {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Set.range (c.attachingHandleMap ρ hρ hblock) ∈ 𝓝 p := by
  let e := c.splitChart.toOpenPartialHomeomorph
  have hzero : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ e.target := by
    rw [← c.splitChart_center]
    exact e.map_source c.splitChart_mem_source
  have hinv : e.symm 0 = p := by
    rw [← c.splitChart_center]
    exact e.left_inv c.splitChart_mem_source
  have hnhds :=
    e.symm.image_mem_nhds hzero
      (Smale.MorseHandle.range_modelMap_mem_nhds_zero (N := c.NegativeCoordinates) (P :=
        c.PositiveCoordinates) hρ)
  rw [hinv] at hnhds
  apply Filter.mem_of_superset hnhds
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  exact ⟨z, rfl⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.mem_interior_range_attachingHandleMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    p ∈ interior (Set.range (c.attachingHandleMap ρ hρ hblock)) :=
  mem_interior_iff_mem_nhds.mpr (c.range_attachingHandleMap_mem_nhds ρ hρ hblock)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.mem_range_attachingHandleMap_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ Set.range (c.attachingHandleMap ρ hρ hblock) ↔
      c.splitChart y ∈ Set.range (Smale.MorseHandle.modelMap ρ) := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    exact
      (c.splitChart.toOpenPartialHomeomorph.right_inv
          (hblock (Smale.MorseHandle.modelMap_mem_product hρ z))).symm
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change c.splitChart.symm (Smale.MorseHandle.modelMap ρ z) = y
    rw [hz]
    exact c.splitChart.toOpenPartialHomeomorph.left_inv hy

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.mem_range_attachingHandleMap_iff_inequalities
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ Set.range (c.attachingHandleMap ρ hρ hblock) ↔
      ‖(c.splitChart y).2‖ ≤ ρ ∧ f p - ρ ^ 2 ≤ f y := by
  rw [c.mem_range_attachingHandleMap_iff ρ hρ hblock hy,
    Smale.MorseHandle.mem_range_modelMap_iff hρ]
  apply and_congr_right
  intro _
  rw [c.splitChart_equation hy]
  constructor <;> intro h <;> linarith

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.mem_attachingUnion_iff_model {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ {z | f z ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock) ↔
      c.splitChart y ∈
        {z | Smale.MorseHandle.quadratic z ≤ -(ρ ^ 2)} ∪
          Set.range (Smale.MorseHandle.modelMap ρ) := by
  change
    (f y ≤ f p - ρ ^ 2 ∨ y ∈ Set.range (c.attachingHandleMap ρ hρ hblock)) ↔
      (Smale.MorseHandle.quadratic (c.splitChart y) ≤ -(ρ ^ 2) ∨
        c.splitChart y ∈ Set.range (Smale.MorseHandle.modelMap ρ))
  rw [c.mem_range_attachingHandleMap_iff ρ hρ hblock hy]
  apply or_congr_left
  rw [c.splitChart_equation hy]
  unfold Smale.MorseHandle.quadratic
  constructor <;> intro h <;> linarith

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.mem_interior_attachingUnion_of_model {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source)
    (hi :
      c.splitChart y ∈
        interior
          ({z | Smale.MorseHandle.quadratic z ≤ -(ρ ^ 2)} ∪
            Set.range (Smale.MorseHandle.modelMap ρ))) :
    y ∈ interior ({z | f z ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hp :=
    (c.splitChart.toOpenPartialHomeomorph.continuousAt hy).preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hi)
  apply Filter.mem_of_superset (Filter.inter_mem (c.splitChart.open_source.mem_nhds hy) hp)
  intro z hz
  exact (c.mem_attachingUnion_iff_model ρ hρ hblock hz.1).mpr hz.2

private def
    Smale.MorseHandle.attachmentRegion {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (ρ : ℝ) : Set (N × P) :=
  {z | quadratic z ≤ -(ρ ^ 2)} ∪ Set.range (modelMap ρ)

private theorem Smale.MorseHandle.continuous_quadratic {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] : Continuous (quadratic (N := N) (P := P)) := by
  unfold quadratic
  fun_prop

private theorem Smale.MorseHandle.isClosed_attachmentRegion {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) :
    IsClosed (attachmentRegion (N := N) (P := P) ρ) := by
  have heq :
    attachmentRegion (N := N) (P := P) ρ = {z | quadratic z ≤ -(ρ ^ 2)} ∪ {z | ‖z.2‖ ≤ ρ} := by
    ext z
    exact mem_lower_union_handle_iff hρ z
  rw [heq]
  exact
    (isClosed_le continuous_quadratic continuous_const).union
      (isClosed_le continuous_snd.norm continuous_const)

private theorem Smale.MorseHandle.notMem_interior_attachmentRegion_of_bounds {N P : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ}
    (hρ : 0 < ρ) (z : N × P) (hq : -(ρ ^ 2) ≤ quadratic z) (hv : ρ ≤ ‖z.2‖) :
    z ∉ interior (attachmentRegion ρ) := by
  intro hi
  have hpath : ContinuousAt (fun r : ℝ => (z.1, r • z.2)) 1 := by fun_prop
  have hnear : ∀ᶠ r : ℝ in 𝓝 1, (z.1, r • z.2) ∈ attachmentRegion ρ := by
    apply hpath.preimage_mem_nhds
    simpa only [one_smul, Prod.eta] using mem_interior_iff_mem_nhds.mp hi
  obtain ⟨r, hr, hmem⟩ := hnear.exists_gt
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hvpos : 0 < ‖z.2‖ := hρ.trans_le hv
  have hnorm : ‖r • z.2‖ = r * ‖z.2‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
  have hnormlt : ‖z.2‖ < ‖r • z.2‖ := by
    rw [hnorm]
    nlinarith
  have hquadlt : quadratic z < quadratic (z.1, r • z.2) := by
    unfold quadratic
    nlinarith [norm_nonneg (r • z.2), norm_nonneg z.2]
  rcases (mem_lower_union_handle_iff hρ (z.1, r • z.2)).mp hmem with h | h
  · exact (not_lt_of_ge h) (hq.trans_lt hquadlt)
  · exact (not_lt_of_ge h) (hv.trans_lt hnormlt)

private theorem
    Smale.MorseHandle.mem_interior_attachmentRegion_iff {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    z ∈ interior (attachmentRegion ρ) ↔ quadratic z < -(ρ ^ 2) ∨ ‖z.2‖ < ρ := by
  constructor
  · intro hi
    by_cases hq : quadratic z < -(ρ ^ 2)
    · exact Or.inl hq
    by_cases hv : ‖z.2‖ < ρ
    · exact Or.inr hv
    exact
      (notMem_interior_attachmentRegion_of_bounds hρ z (le_of_not_gt hq) (le_of_not_gt hv)
          hi).elim
  · rintro (hq | hv)
    · apply
        interior_maximal (t := {w | quadratic w < -(ρ ^ 2)}) _
          (isOpen_lt continuous_quadratic continuous_const) hq
      intro w hw
      exact (mem_lower_union_handle_iff hρ w).mpr (Or.inl hw.le)
    · apply
        interior_maximal (t := {w : N × P | ‖w.2‖ < ρ}) _
          (isOpen_lt continuous_snd.norm continuous_const) hv
      intro w hw
      exact (mem_lower_union_handle_iff hρ w).mpr (Or.inr hw.le)

private theorem
    Smale.MorseHandle.mem_frontier_attachmentRegion_iff {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    z ∈ frontier (attachmentRegion ρ) ↔
      (quadratic z = -(ρ ^ 2) ∧ ρ ≤ ‖z.2‖) ∨ (‖z.2‖ = ρ ∧ -(ρ ^ 2) ≤ quadratic z) := by
  rw [frontier, (isClosed_attachmentRegion hρ).closure_eq]
  change (z ∈ attachmentRegion ρ ∧ z ∉ interior (attachmentRegion ρ)) ↔ _
  rw [mem_interior_attachmentRegion_iff hρ]
  rw [show z ∈ attachmentRegion ρ ↔ quadratic z ≤ -(ρ ^ 2) ∨ ‖z.2‖ ≤ ρ from
      mem_lower_union_handle_iff hρ z]
  constructor
  · rintro ⟨hmem, hnot⟩
    have hq : -(ρ ^ 2) ≤ quadratic z := le_of_not_gt (fun h => hnot (Or.inl h))
    have hv : ρ ≤ ‖z.2‖ := le_of_not_gt (fun h => hnot (Or.inr h))
    rcases hmem with h | h
    · exact Or.inl ⟨le_antisymm h hq, hv⟩
    · exact Or.inr ⟨le_antisymm h hv, hq⟩
  · rintro (⟨hq, hv⟩ | ⟨hv, hq⟩)
    · refine ⟨Or.inl hq.le, ?_⟩
      rintro (h | h)
      · exact hq.not_lt h
      · exact (not_lt_of_ge hv) h
    · refine ⟨Or.inr hv.le, ?_⟩
      rintro (h | h)
      · exact (not_lt_of_ge hq) h
      · exact hv.not_lt h

private theorem Smale.MorseHandle.modelMap_mem_frontier_attachmentRegion_iff {N P : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ : ℝ}
    (hρ : 0 < ρ) (z : UnitDisk N × UnitDisk P) :
    modelMap ρ z ∈ frontier (attachmentRegion ρ) ↔ ‖(z.2 : P)‖ = 1 := by
  have hv : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.property
  have hnorm : ‖(modelMap ρ z).2‖ = ρ * ‖(z.2 : P)‖ := by
    change ‖ρ • (z.2 : P)‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  rw [mem_frontier_attachmentRegion_iff hρ]
  constructor
  · intro hz
    have hlo : ρ ≤ ‖(modelMap ρ z).2‖ := by
      rcases hz with hz | hz
      · exact hz.2
      · exact hz.1.ge
    rw [hnorm] at hlo
    nlinarith
  · intro hz
    refine Or.inr ⟨?_, ?_⟩
    · rw [hnorm, hz, mul_one]
    · exact ((mem_range_modelMap_iff hρ (modelMap ρ z)).mp ⟨z, rfl⟩).2

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.mem_interior_attachingUnion_iff_model {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ interior ({z | f z ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ↔
      c.splitChart y ∈ interior (Smale.MorseHandle.attachmentRegion ρ) := by
  constructor
  · intro hi
    apply mem_interior_iff_mem_nhds.mpr
    have ht : c.splitChart y ∈ c.splitChart.target := c.splitChart.map_source' hy
    have hc : ContinuousAt c.splitChart.symm (c.splitChart y) :=
      c.splitChart.toOpenPartialHomeomorph.symm.continuousAt ht
    have hleft : c.splitChart.symm (c.splitChart y) = y := c.splitChart.left_inv' hy
    have hnear :
      c.splitChart.symm ⁻¹'
          interior ({z | f z ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ∈
        𝓝 (c.splitChart y) :=
      hc.preimage_mem_nhds
        (by
          rw [hleft]
          exact isOpen_interior.mem_nhds hi)
    apply Filter.mem_of_superset (Filter.inter_mem (c.splitChart.open_target.mem_nhds ht) hnear)
    intro z hz
    have hmem :=
      (c.mem_attachingUnion_iff_model ρ hρ hblock (c.splitChart.map_target' hz.1)).mp
        (interior_subset hz.2)
    rwa [c.splitChart.right_inv' hz.1] at hmem
  · exact c.mem_interior_attachingUnion_of_model ρ hρ hblock hy

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.mem_frontier_attachingUnion_iff_model {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M]
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {y : M} (hy : y ∈ c.splitChart.source) :
    y ∈ frontier ({z | f z ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ↔
      c.splitChart y ∈ frontier (Smale.MorseHandle.attachmentRegion ρ) := by
  have hA : IsClosed ({z | f z ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) :=
    (isClosed_le hf continuous_const).union
      (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range
  rw [frontier, frontier, hA.closure_eq,
    (Smale.MorseHandle.isClosed_attachmentRegion hρ).closure_eq]
  exact
    and_congr (c.mem_attachingUnion_iff_model ρ hρ hblock hy)
      (not_congr (c.mem_interior_attachingUnion_iff_model ρ hρ hblock hy))

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.attachingHandleMap_mem_frontier_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M]
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (z :
      Smale.MorseHandle.UnitDisk c.NegativeCoordinates ×
        Smale.MorseHandle.UnitDisk c.PositiveCoordinates) :
    c.attachingHandleMap ρ hρ hblock z ∈
        frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ↔
      ‖(z.2 : c.PositiveCoordinates)‖ = 1 := by
  have ht := hblock (Smale.MorseHandle.modelMap_mem_product hρ z)
  have hy : c.attachingHandleMap ρ hρ hblock z ∈ c.splitChart.source :=
    c.splitChart.map_target' ht
  rw [c.mem_frontier_attachingUnion_iff_model hf ρ hρ hblock hy]
  have heq : c.splitChart (c.attachingHandleMap ρ hρ hblock z) = Smale.MorseHandle.modelMap ρ z :=
    c.splitChart.right_inv' ht
  rw [heq, Smale.MorseHandle.modelMap_mem_frontier_attachmentRegion_iff hρ]

private def
    Smale.ClosedAttachment.Rel {K M : Type*} [TopologicalSpace K] [TopologicalSpace M] (A : Set M)
    (B : Set K) (h : C(K, M)) : A ⊕ K → A ⊕ K → Prop
  | .inl a, .inr k => k ∈ B ∧ (a : M) = h k
  | _, _ => False

private abbrev Smale.ClosedAttachment.Space {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (B : Set K) (h : C(K, M)) :=
  Quot (Smale.ClosedAttachment.Rel A B h)

private def Smale.ClosedAttachment.sumMap {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (h : C(K, M)) : A ⊕ K → ↥(A ∪ Set.range h)
  | .inl a => ⟨a, Or.inl a.2⟩
  | .inr k => ⟨h k, Or.inr ⟨k, rfl⟩⟩

private theorem Smale.ClosedAttachment.continuous_sumMap {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (h : C(K, M)) : Continuous (sumMap A h) :=
  continuous_sum_dom.mpr ⟨continuous_subtype_val.subtype_mk _, h.continuous.subtype_mk _⟩

private theorem Smale.ClosedAttachment.sumMap_respects {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (B : Set K) (h : C(K, M)) (x y : A ⊕ K)
    (hxy : Smale.ClosedAttachment.Rel A B h x y) : sumMap A h x = sumMap A h y := by
  cases x with
  | inl a =>
    cases y with
    | inl a' => exact hxy.elim
    | inr k => exact Subtype.ext hxy.2
  | inr k => cases y <;> exact hxy.elim

private def
    Smale.ClosedAttachment.quotientMap {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (B : Set K) (h : C(K, M)) : Space A B h → ↥(A ∪ Set.range h) :=
  Quot.lift (sumMap A h) (sumMap_respects A B h)

private theorem Smale.ClosedAttachment.continuous_quotientMap {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (B : Set K) (h : C(K, M)) : Continuous (quotientMap A B h) :=
  continuous_quot_lift (sumMap_respects A B h) (Smale.ClosedAttachment.continuous_sumMap A h)

private theorem Smale.ClosedAttachment.quotientMap_injective {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (B : Set K) (h : C(K, M)) (hinj : Function.Injective h)
    (hface : ∀ k, h k ∈ A ↔ k ∈ B) : Function.Injective (quotientMap A B h) := by
  intro q r
  induction q using Quot.inductionOn with
  | _ x =>
    induction r using Quot.inductionOn with
    | _ y =>
      intro heq
      have heq' := congrArg Subtype.val heq
      cases x with
      | inl a =>
        cases y with
        | inl a' =>
          have haa : a = a' := Subtype.ext heq'
          subst a'
          rfl
        | inr k =>
          change (a : M) = h k at heq'
          have hk : h k ∈ A := by rw [← heq']; exact a.2
          exact Quot.sound ⟨(hface k).mp hk, heq'⟩
      | inr k =>
        cases y with
        | inl a =>
          change h k = (a : M) at heq'
          have hk : h k ∈ A := by rw [heq']; exact a.2
          exact
            (Quot.sound (r := Smale.ClosedAttachment.Rel A B h) (a := .inl a) (b := .inr k)
                ⟨(hface k).mp hk, heq'.symm⟩).symm
        | inr k' =>
          have hkk : k = k' := hinj heq'
          subst k'
          rfl

private theorem Smale.ClosedAttachment.quotientMap_surjective {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (B : Set K) (h : C(K, M)) :
    Function.Surjective (quotientMap A B h) := by
  rintro ⟨x, hx | ⟨k, rfl⟩⟩
  · exact ⟨Quot.mk _ (.inl ⟨x, hx⟩), rfl⟩
  · exact ⟨Quot.mk _ (.inr k), rfl⟩

private def
    Smale.ClosedAttachment.unionHomeomorph {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (B : Set K) (h : C(K, M)) [CompactSpace K] [T2Space M] (hA : IsCompact A)
    (hinj : Function.Injective h) (hface : ∀ k, h k ∈ A ↔ k ∈ B) :
    Space A B h ≃ₜ ↥(A ∪ Set.range h) := by
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  exact
    Continuous.homeoOfEquivCompactToT2 (f :=
      Equiv.ofBijective (quotientMap A B h)
        ⟨quotientMap_injective A B h hinj hface, quotientMap_surjective A B h⟩)
      (continuous_quotientMap A B h)

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.attachingHandleMap_boundary_height {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (z :
      Smale.MorseHandle.UnitDisk c.NegativeCoordinates ×
        Smale.MorseHandle.UnitDisk c.PositiveCoordinates)
    (hz : ‖(z.1 : c.NegativeCoordinates)‖ = 1) :
    f (c.attachingHandleMap ρ hρ hblock z) = f x - ρ ^ 2 := by
  rw [c.attachingHandleMap_quadratic, Smale.MorseHandle.modelMap_height hρ z, hz]
  ring

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.SignedMorseChart.attachingBoundaryMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    C(Metric.sphere (0 : c.NegativeCoordinates) 1 ×
        Smale.MorseHandle.UnitDisk c.PositiveCoordinates,
      { y : M // f y = f x - ρ ^ 2 })
    where
  toFun
    z :=
    ⟨c.attachingHandleMap ρ hρ hblock (⟨z.1, Metric.sphere_subset_closedBall z.1.2⟩, z.2),
      c.attachingHandleMap_boundary_height ρ hρ hblock _
        (by simpa only [Metric.mem_sphere, dist_zero_right] using z.1.2)⟩
  continuous_toFun :=
    ((c.attachingHandleMap ρ hρ hblock).continuous.comp
          (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk
            continuous_snd)).subtype_mk
      _

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.attachingHandleUnionHomeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) [T2Space M] [CompactSpace M]
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Smale.ClosedAttachment.Space {y : M | f y ≤ f x - ρ ^ 2}
        {z | ‖(z.1 : c.NegativeCoordinates)‖ = 1} (c.attachingHandleMap ρ hρ hblock) ≃ₜ
      ↥({y : M | f y ≤ f x - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) :=
  Smale.ClosedAttachment.unionHomeomorph _ _ _ (isClosed_le hf continuous_const).isCompact
    (c.attachingHandleMap_injective ρ hρ hblock)
    (fun z => c.attachingHandleMap_lower_iff ρ hρ hblock z)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.attachingHandleUnion_subset_upper {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    {y : M | f y ≤ f x - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock) ⊆
      {y : M | f y ≤ f x + ρ ^ 2} := by
  rintro y (hy | ⟨z, rfl⟩)
  · change f y ≤ f x + ρ ^ 2
    change f y ≤ f x - ρ ^ 2 at hy
    nlinarith [sq_nonneg ρ]
  · exact c.attachingHandleMap_upper ρ hρ hblock z

private def
    Smale.RadialExtension.direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E)
    (hx : x ≠ 0) : Metric.sphere (0 : E) 1 :=
  ⟨‖x‖⁻¹ • x, by simp [norm_smul, hx]⟩

attribute [local instance 100] Classical.propDecidable in
private def Smale.RadialExtension.radial {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) (x : E) : F :=
  if hx : x = 0 then 0 else ‖x‖ • (f (direction x hx) : F)

@[simp]
private theorem
    Smale.RadialExtension.radial_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) : radial f 0 = 0 := by simp [radial]

private theorem Smale.RadialExtension.radial_of_ne_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) {x : E} (hx : x ≠ 0) :
    radial f x = ‖x‖ • (f (direction x hx) : F) := by simp [radial, hx]

@[simp]
private theorem
    Smale.RadialExtension.norm_radial {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) (x : E) : ‖radial f x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp
  rw [radial_of_ne_zero f hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x),
    mem_sphere_zero_iff_norm.mp (f (direction x hx)).property, mul_one]

@[simp]
private theorem Smale.RadialExtension.radial_eq_zero_iff {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) (x : E) : radial f x = 0 ↔ x = 0 := by
  rw [← norm_eq_zero, norm_radial, norm_eq_zero]

private theorem Smale.RadialExtension.direction_radial {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) {x : E} (hx : x ≠ 0) :
    direction (radial f x) (fun h => hx ((radial_eq_zero_iff f x).mp h)) = f (direction x hx) := by
  apply Subtype.ext
  change ‖radial f x‖⁻¹ • radial f x = (f (direction x hx) : F)
  rw [norm_radial, radial_of_ne_zero f hx, inv_smul_smul₀ (norm_ne_zero_iff.mpr hx)]

@[simp]
private theorem Smale.RadialExtension.radial_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) : radial id x = x := by
  by_cases hx : x = 0
  · subst x
    simp
  rw [radial_of_ne_zero id hx]
  exact smul_inv_smul₀ (norm_ne_zero_iff.mpr hx) x

private theorem
    Smale.RadialExtension.radial_comp {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : Metric.sphere (0 : F) 1 → Metric.sphere (0 : G) 1)
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) (x : E) :
    radial g (radial f x) = radial (g ∘ f) x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hy : radial f x ≠ 0 := fun h => hx ((radial_eq_zero_iff f x).mp h)
  rw [radial_of_ne_zero g hy, norm_radial, direction_radial f hx, radial_of_ne_zero (g ∘ f) hx]
  rfl

@[simp]
private theorem Smale.RadialExtension.radial_on_sphere {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) (x : Metric.sphere (0 : E) 1) :
    radial f x = (f x : F) := by
  have hn : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have hx : (x : E) ≠ 0 := by
    intro h
    simp [h] at hn
  have hd : direction (x : E) hx = x := by
    apply Subtype.ext
    simp [direction, hn]
  rw [radial_of_ne_zero f hx, hn, hd, one_smul]

private theorem Smale.RadialExtension.continuous_radial {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1} (hf : Continuous f) :
    Continuous (radial f) := by
  have haway : ContinuousOn (radial f) ({0}ᶜ : Set E) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq :
      ({0}ᶜ : Set E).domRestrict (radial f) = fun (x : ({0}ᶜ : Set E)) =>
        ‖(x : E)‖ • (f ((homeomorphUnitSphereProd E x).1) : F) := by
      funext x
      rw [Set.domRestrict_apply, radial_of_ne_zero f x.property]
      have hd : direction (x : E) x.property = (homeomorphUnitSphereProd E x).1 := by
        apply Subtype.ext
        simp [direction]
      rw [hd]
    rw [heq]
    exact
      continuous_subtype_val.norm.smul
        (continuous_subtype_val.comp (hf.comp (homeomorphUnitSphereProd E).continuous.fst))
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro y hy
    simpa only [radial_zero, dist_zero_right, norm_radial] using hy
  exact (haway x hx).continuousAt (isOpen_compl_singleton.mem_nhds hx)

private def Smale.RadialExtension.homeomorph {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1) : E ≃ₜ F
    where
  toFun := radial e
  invFun := radial e.symm
  left_inv
    x := by
    rw [radial_comp]
    have h : (e.symm : Metric.sphere (0 : F) 1 → Metric.sphere (0 : E) 1) ∘ e = id := by
      funext y
      exact e.symm_apply_apply y
    rw [h, radial_id]
  right_inv
    x := by
    rw [radial_comp]
    have h : (e : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1) ∘ e.symm = id := by
      funext y
      exact e.apply_symm_apply y
    rw [h, radial_id]
  continuous_toFun := continuous_radial e.continuous
  continuous_invFun := continuous_radial e.symm.continuous

private def Smale.RadialExtension.closedBallHomeomorph {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1) :
    Metric.closedBall (0 : E) 1 ≃ₜ Metric.closedBall (0 : F) 1 :=
  (homeomorph e).sets
    (by
      ext x
      simp [homeomorph])

@[simp]
private theorem
    Smale.RadialExtension.closedBallHomeomorph_on_sphere {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1) (x : Metric.sphere (0 : E) 1) :
    closedBallHomeomorph e ⟨x, Metric.sphere_subset_closedBall x.property⟩ =
      ⟨e x, Metric.sphere_subset_closedBall (e x).property⟩ := by
  apply Subtype.ext
  exact radial_on_sphere e x

private abbrev Smale.PuncturedHandle.Radius :=
  Set.Ioc (0 : ℝ) 1

private abbrev Smale.PuncturedHandle.UnitSphere (E : Type*) [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) 1

private abbrev Smale.PuncturedHandle.PuncturedBall (E : Type*) [NormedAddCommGroup E] :=
  { x : E // x ≠ 0 ∧ ‖x‖ ≤ 1 }

private def Smale.PuncturedHandle.point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : UnitSphere E) (r : Radius) : PuncturedBall E := by
  have hn : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  have hnorm : ‖(r : ℝ) • (u : E)‖ = (r : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.property.1, hn, mul_one]
  refine ⟨(r : ℝ) • (u : E), ?_, ?_⟩
  · exact norm_pos_iff.mp (by rw [hnorm]; exact r.property.1)
  · rw [hnorm]
    exact r.property.2

private theorem
    Smale.PuncturedHandle.norm_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : UnitSphere E) (r : Radius) : ‖(point u r : E)‖ = (r : ℝ) := by
  change ‖(r : ℝ) • (u : E)‖ = (r : ℝ)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.property.1,
    mem_sphere_zero_iff_norm.mp u.property, mul_one]

private def Smale.PuncturedHandle.polar (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    PuncturedBall E ≃ₜ (UnitSphere E × Radius)
    where
  toFun
    x :=
    (Smale.RadialExtension.direction (x : E) x.property.1,
      ⟨‖(x : E)‖, norm_pos_iff.mpr x.property.1, x.property.2⟩)
  invFun p := point p.1 p.2
  left_inv := by
    intro x
    apply Subtype.ext
    change ‖(x : E)‖ • (‖(x : E)‖⁻¹ • (x : E)) = (x : E)
    exact smul_inv_smul₀ (norm_ne_zero_iff.mpr x.property.1) (x : E)
  right_inv := by
    rintro ⟨u, r⟩
    apply Prod.ext
    · apply Subtype.ext
      change ‖(point u r : E)‖⁻¹ • ((r : ℝ) • (u : E)) = (u : E)
      rw [norm_point, inv_smul_smul₀ r.property.1.ne']
    · apply Subtype.ext
      exact norm_point u r
  continuous_toFun := by
    have hdir :
      Continuous
        (fun x : PuncturedBall E => Smale.RadialExtension.direction (x : E) x.property.1) :=
      ((continuous_subtype_val.norm.inv₀ (fun x => norm_ne_zero_iff.mpr x.property.1)).smul
            continuous_subtype_val).subtype_mk
        _
    exact hdir.prodMk (continuous_subtype_val.norm.subtype_mk _)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_snd).smul
          (continuous_subtype_val.comp continuous_fst)).subtype_mk
      _

private def Smale.PuncturedHandle.exchange (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (UnitSphere E × PuncturedBall F) ≃ₜ (PuncturedBall E × UnitSphere F) :=
  ((Homeomorph.refl (UnitSphere E)).prodCongr (polar F)).trans
    (((Homeomorph.refl (UnitSphere E)).prodCongr
          (Homeomorph.prodComm (UnitSphere F) Radius)).trans
      ((Homeomorph.prodAssoc (UnitSphere E) Radius (UnitSphere F)).symm.trans
        ((polar E).symm.prodCongr (Homeomorph.refl (UnitSphere F)))))

private theorem Smale.PuncturedHandle.exchange_apply {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (u : UnitSphere E)
    (v : PuncturedBall F) :
    exchange E F (u, v) =
      (point u ⟨‖(v : F)‖, norm_pos_iff.mpr v.property.1, v.property.2⟩,
        Smale.RadialExtension.direction (v : F) v.property.1) :=
  rfl

private def
    Smale.PuncturedHandle.boundaryPoint {E : Type*} [NormedAddCommGroup E] (u : UnitSphere E) :
    PuncturedBall E :=
  ⟨u, Metric.ne_of_mem_sphere u.property one_ne_zero, (mem_sphere_zero_iff_norm.mp u.property).le⟩

private theorem Smale.PuncturedHandle.exchange_boundary {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (u : UnitSphere E)
    (v : UnitSphere F) : exchange E F (u, boundaryPoint v) = (boundaryPoint u, v) := by
  rw [exchange_apply]
  have hv : ‖(v : F)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  apply Prod.ext
  · apply Subtype.ext
    change ‖(v : F)‖ • (u : E) = (u : E)
    rw [hv, one_smul]
  · apply Subtype.ext
    change ‖(v : F)‖⁻¹ • (v : F) = (v : F)
    rw [hv, inv_one, one_smul]

private abbrev Smale.PuncturedHandle.UnitBall (E : Type*) [NormedAddCommGroup E] :=
  { x : E // ‖x‖ ≤ 1 }

private def Smale.PuncturedHandle.ballZero {E : Type*} [NormedAddCommGroup E] : UnitBall E :=
  ⟨0, by simp⟩

private def
    Smale.PuncturedHandle.sphereToBall {E : Type*} [NormedAddCommGroup E] (u : UnitSphere E) :
    UnitBall E :=
  ⟨u, (mem_sphere_zero_iff_norm.mp u.property).le⟩

private def Smale.PuncturedHandle.puncturedToBall {E : Type*} [NormedAddCommGroup E]
    (u : PuncturedBall E) : UnitBall E :=
  ⟨u, u.property.2⟩

private theorem Smale.PuncturedHandle.puncturedToBall_injective {E : Type*} [NormedAddCommGroup E] :
    Function.Injective (puncturedToBall (E := E)) := fun _ _ h =>
  Subtype.ext (congrArg (fun z : UnitBall E => (z : E)) h)

private def
    Smale.PuncturedHandle.oldBoundary {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (q : UnitSphere E × UnitSphere F) : UnitSphere E × UnitBall F :=
  (q.1, sphereToBall q.2)

private def
    Smale.PuncturedHandle.newBoundary {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (q : UnitSphere E × UnitSphere F) : UnitBall E × UnitSphere F :=
  (sphereToBall q.1, q.2)

private def
    Smale.PuncturedHandle.oldPunctured {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (p : UnitSphere E × PuncturedBall F) : UnitSphere E × UnitBall F :=
  (p.1, puncturedToBall p.2)

private def
    Smale.PuncturedHandle.newPunctured {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (p : PuncturedBall E × UnitSphere F) : UnitBall E × UnitSphere F :=
  (puncturedToBall p.1, p.2)

private theorem Smale.PuncturedHandle.oldPunctured_injective {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] : Function.Injective (oldPunctured (E := E) (F := F)) := by
  intro p q h
  exact
    Prod.ext (congrArg (fun z : UnitSphere E × UnitBall F => z.1) h)
      (puncturedToBall_injective (congrArg (fun z : UnitSphere E × UnitBall F => z.2) h))

private theorem Smale.PuncturedHandle.newPunctured_injective {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] : Function.Injective (newPunctured (E := E) (F := F)) := by
  intro p q h
  exact
    Prod.ext (puncturedToBall_injective (congrArg (fun z : UnitBall E × UnitSphere F => z.1) h))
      (congrArg (fun z : UnitBall E × UnitSphere F => z.2) h)

private def Smale.PuncturedHandle.oldPuncturedDomain (E F : Type*) [NormedAddCommGroup E]
    [NormedAddCommGroup F] :
    (UnitSphere E × PuncturedBall F) ≃ₜ { p : UnitSphere E × UnitBall F // (p.2 : F) ≠ 0 }
    where
  toFun p := ⟨oldPunctured p, p.2.property.1⟩
  invFun p := (p.val.1, ⟨p.val.2, p.property, p.val.2.property⟩)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    change
      Continuous
        (fun p : UnitSphere E × PuncturedBall F =>
          (p.1, (⟨(p.2 : F), p.2.property.2⟩ : UnitBall F)))
    exact continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · exact
        (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _

private def Smale.PuncturedHandle.newPuncturedDomain (E F : Type*) [NormedAddCommGroup E]
    [NormedAddCommGroup F] :
    (PuncturedBall E × UnitSphere F) ≃ₜ { p : UnitBall E × UnitSphere F // (p.1 : E) ≠ 0 }
    where
  toFun p := ⟨newPunctured p, p.1.property.1⟩
  invFun p := (⟨p.val.1, p.property, p.val.1.property⟩, p.val.2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    change
      Continuous
        (fun p : PuncturedBall E × UnitSphere F =>
          ((⟨(p.1 : E), p.1.property.2⟩ : UnitBall E), p.2))
    exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
  continuous_invFun := by
    apply Continuous.prodMk
    · exact
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _
    · exact continuous_snd.comp continuous_subtype_val

private theorem Smale.PuncturedHandle.oldPunctured_boundary {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] (q : UnitSphere E × UnitSphere F) :
    oldPunctured (q.1, boundaryPoint q.2) = oldBoundary q :=
  rfl

private theorem Smale.PuncturedHandle.newPunctured_boundary {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] (q : UnitSphere E × UnitSphere F) :
    newPunctured (boundaryPoint q.1, q.2) = newBoundary q :=
  rfl

private def
    Smale.ClosedCover.glue {X Y : Type*} {A B : Set X} (hcover : A ∪ B = Set.univ) (f : A → Y)
    (g : B → Y) : X → Y := by
  classical
    exact fun x =>
    if hx : x ∈ A then f ⟨x, hx⟩
    else g ⟨x, (show x ∈ A ∪ B by rw [hcover]; trivial).resolve_left hx⟩

private theorem Smale.ClosedCover.glue_left {X Y : Type*} {A B : Set X} (hcover : A ∪ B = Set.univ)
    (f : A → Y) (g : B → Y) (x : A) : glue hcover f g x = f x := by
  classical simp only [glue, dite_eq_left x.property]

private theorem Smale.ClosedCover.glue_right {X Y : Type*} {A B : Set X} (hcover : A ∪ B = Set.univ)
    (f : A → Y) (g : B → Y) (hagree : ∀ a : A, ∀ b : B, (a : X) = b → f a = g b) (x : B) :
    glue hcover f g x = g x := by
  classical
  by_cases hx : (x : X) ∈ A
  · rw [glue, dite_eq_left hx]
    exact hagree ⟨x, hx⟩ x rfl
  · rw [glue, dite_eq_right hx]

private theorem
    Smale.ClosedCover.continuous_glue {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} (hcover : A ∪ B = Set.univ) (hA : IsClosed A) (hB : IsClosed B) (f : A → Y)
    (g : B → Y) (hf : Continuous f) (hg : Continuous g)
    (hagree : ∀ a : A, ∀ b : B, (a : X) = b → f a = g b) : Continuous (glue hcover f g) := by
  have hleft : ContinuousOn (glue hcover f g) A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : A.domRestrict (glue hcover f g) = f := funext (fun x => glue_left hcover f g x)
    rw [heq]
    exact hf
  have hright : ContinuousOn (glue hcover f g) B := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : B.domRestrict (glue hcover f g) = g :=
      funext (fun x => glue_right hcover f g hagree x)
    rw [heq]
    exact hg
  apply continuousOn_univ.mp
  rw [← hcover]
  exact hleft.union_of_isClosed hright hA hB

private def Smale.ClosedCover.homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} {C D : Set Y} (hcover : A ∪ B = Set.univ) (hcover' : C ∪ D = Set.univ)
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C) (hD : IsClosed D) (e : A ≃ₜ C)
    (f : B ≃ₜ D) (hcross : ∀ a : A, ∀ b : B, ((e a : C) : Y) = f b ↔ (a : X) = b) : X ≃ₜ Y := by
  let e₀ : A → Y := fun x => e x
  let f₀ : B → Y := fun x => f x
  let e₁ : C → X := fun y => e.symm y
  let f₁ : D → X := fun y => f.symm y
  have hagree : ∀ a : A, ∀ b : B, (a : X) = b → e₀ a = f₀ b := fun a b h => (hcross a b).mpr h
  have hagreeInv : ∀ c : C, ∀ d : D, (c : Y) = d → e₁ c = f₁ d := by
    intro c d h
    apply (hcross (e.symm c) (f.symm d)).mp
    simpa only [e.apply_symm_apply, f.apply_symm_apply] using h
  let F := glue hcover e₀ f₀
  let G := glue hcover' e₁ f₁
  have hleft : Function.LeftInverse G F := by
    intro x
    have hx : x ∈ A ∪ B := by rw [hcover]; trivial
    rcases hx with hx | hx
    · calc
        G (F x) = G (e₀ ⟨x, hx⟩) := congrArg G (glue_left hcover e₀ f₀ ⟨x, hx⟩)
        _ = e₁ (e ⟨x, hx⟩) := (glue_left hcover' e₁ f₁ (e ⟨x, hx⟩))
        _ = x := congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
    · calc
        G (F x) = G (f₀ ⟨x, hx⟩) := congrArg G (glue_right hcover e₀ f₀ hagree ⟨x, hx⟩)
        _ = f₁ (f ⟨x, hx⟩) := (glue_right hcover' e₁ f₁ hagreeInv (f ⟨x, hx⟩))
        _ = x := congrArg Subtype.val (f.symm_apply_apply ⟨x, hx⟩)
  have hright : Function.RightInverse G F := by
    intro y
    have hy : y ∈ C ∪ D := by rw [hcover']; trivial
    rcases hy with hy | hy
    · calc
        F (G y) = F (e₁ ⟨y, hy⟩) := congrArg F (glue_left hcover' e₁ f₁ ⟨y, hy⟩)
        _ = e₀ (e.symm ⟨y, hy⟩) := (glue_left hcover e₀ f₀ (e.symm ⟨y, hy⟩))
        _ = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
    · calc
        F (G y) = F (f₁ ⟨y, hy⟩) := congrArg F (glue_right hcover' e₁ f₁ hagreeInv ⟨y, hy⟩)
        _ = f₀ (f.symm ⟨y, hy⟩) := (glue_right hcover e₀ f₀ hagree (f.symm ⟨y, hy⟩))
        _ = y := congrArg Subtype.val (f.apply_symm_apply ⟨y, hy⟩)
  exact
    { toEquiv := { toFun := F, invFun := G, left_inv := hleft, right_inv := hright }
      continuous_toFun :=
        continuous_glue hcover hA hB e₀ f₀ (continuous_subtype_val.comp e.continuous)
          (continuous_subtype_val.comp f.continuous) hagree
      continuous_invFun :=
        continuous_glue hcover' hC hD e₁ f₁ (continuous_subtype_val.comp e.symm.continuous)
          (continuous_subtype_val.comp f.symm.continuous) hagreeInv }

private def Smale.ClosedCover.homeomorphOfClosedPieces {R P Q X Y : Type*} [TopologicalSpace R]
    [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace X] [TopologicalSpace Y]
    (r₀ : R → X) (r₁ : R → Y) (p₀ : P → X) (p₁ : Q → Y) (hr₀ : Topology.IsClosedEmbedding r₀)
    (hr₁ : Topology.IsClosedEmbedding r₁) (hp₀ : Topology.IsClosedEmbedding p₀)
    (hp₁ : Topology.IsClosedEmbedding p₁) (hcover₀ : Set.range r₀ ∪ Set.range p₀ = Set.univ)
    (hcover₁ : Set.range r₁ ∪ Set.range p₁ = Set.univ) (e : P ≃ₜ Q)
    (hincidence : ∀ r p, r₀ r = p₀ p ↔ r₁ r = p₁ (e p)) : X ≃ₜ Y := by
  let a₀ := hr₀.isEmbedding.toHomeomorph
  let a₁ := hr₁.isEmbedding.toHomeomorph
  let b₀ := hp₀.isEmbedding.toHomeomorph
  let b₁ := hp₁.isEmbedding.toHomeomorph
  let a : Set.range r₀ ≃ₜ Set.range r₁ := a₀.symm.trans a₁
  let b : Set.range p₀ ≃ₜ Set.range p₁ := b₀.symm.trans (e.trans b₁)
  apply
    homeomorph hcover₀ hcover₁ hr₀.isClosed_range hp₀.isClosed_range hr₁.isClosed_range
      hp₁.isClosed_range a b
  intro x y
  have hx : r₀ (a₀.symm x) = (x : X) := by exact congrArg Subtype.val (a₀.apply_symm_apply x)
  have hy : p₀ (b₀.symm y) = (y : X) := by exact congrArg Subtype.val (b₀.apply_symm_apply y)
  change r₁ (a₀.symm x) = p₁ (e (b₀.symm y)) ↔ (x : X) = (y : X)
  rw [← hincidence, hx, hy]

private structure Smale.SurgeryBoundaryPair (E F R X Y : Type*) [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y] where
  oldExterior : R → X
  newExterior : R → Y
  oldPiece : PuncturedHandle.UnitSphere E × PuncturedHandle.UnitBall F → X
  newPiece : PuncturedHandle.UnitBall E × PuncturedHandle.UnitSphere F → Y
  oldExterior_closed : Topology.IsClosedEmbedding oldExterior
  newExterior_closed : Topology.IsClosedEmbedding newExterior
  oldPiece_closed : Topology.IsClosedEmbedding oldPiece
  newPiece_closed : Topology.IsClosedEmbedding newPiece
  old_cover : Set.range oldExterior ∪ Set.range oldPiece = Set.univ
  new_cover : Set.range newExterior ∪ Set.range newPiece = Set.univ
  boundary : PuncturedHandle.UnitSphere E × PuncturedHandle.UnitSphere F → R
  old_overlap :
    ∀ r p, oldExterior r = oldPiece p ↔ ∃ q, r = boundary q ∧ p = PuncturedHandle.oldBoundary q
  new_overlap :
    ∀ r p, newExterior r = newPiece p ↔ ∃ q, r = boundary q ∧ p = PuncturedHandle.newBoundary q

private def Smale.SurgeryBoundaryPair.attachingSphere {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) : C(Smale.PuncturedHandle.UnitSphere E, X) :=
  ⟨fun u => d.oldPiece (u, Smale.PuncturedHandle.ballZero),
    d.oldPiece_closed.continuous.comp (continuous_id.prodMk continuous_const)⟩

private def Smale.SurgeryBoundaryPair.beltSphere {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) : C(Smale.PuncturedHandle.UnitSphere F, Y) :=
  ⟨fun v => d.newPiece (Smale.PuncturedHandle.ballZero, v),
    d.newPiece_closed.continuous.comp (continuous_const.prodMk continuous_id)⟩

private abbrev Smale.SurgeryBoundaryPair.OldComplement {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) :=
  (Set.range d.attachingSphere)ᶜ

private abbrev Smale.SurgeryBoundaryPair.NewComplement {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) :=
  (Set.range d.beltSphere)ᶜ

private theorem
    Smale.SurgeryBoundaryPair.oldPiece_mem_core_iff {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y)
    (p : Smale.PuncturedHandle.UnitSphere E × Smale.PuncturedHandle.UnitBall F) :
    d.oldPiece p ∈ Set.range d.attachingSphere ↔ (p.2 : F) = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    have hp : (u, (Smale.PuncturedHandle.ballZero : Smale.PuncturedHandle.UnitBall F)) = p :=
      d.oldPiece_closed.injective hu
    exact
      (congrArg
          (fun z : Smale.PuncturedHandle.UnitSphere E × Smale.PuncturedHandle.UnitBall F =>
            (z.2 : F))
          hp).symm
  · intro hp
    refine ⟨p.1, ?_⟩
    apply congrArg d.oldPiece
    exact Prod.ext rfl (Subtype.ext hp.symm)

private theorem
    Smale.SurgeryBoundaryPair.newPiece_mem_belt_iff {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y)
    (p : Smale.PuncturedHandle.UnitBall E × Smale.PuncturedHandle.UnitSphere F) :
    d.newPiece p ∈ Set.range d.beltSphere ↔ (p.1 : E) = 0 := by
  constructor
  · rintro ⟨v, hv⟩
    have hp : ((Smale.PuncturedHandle.ballZero : Smale.PuncturedHandle.UnitBall E), v) = p :=
      d.newPiece_closed.injective hv
    exact
      (congrArg
          (fun z : Smale.PuncturedHandle.UnitBall E × Smale.PuncturedHandle.UnitSphere F =>
            (z.1 : E))
          hp).symm
  · intro hp
    refine ⟨p.2, ?_⟩
    apply congrArg d.newPiece
    exact Prod.ext (Subtype.ext hp.symm) rfl

private theorem
    Smale.SurgeryBoundaryPair.oldExterior_avoids {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) (r : R) : d.oldExterior r ∈ d.OldComplement := by
  rintro ⟨u, hu⟩
  obtain ⟨q, -, hq⟩ := (d.old_overlap r (u, Smale.PuncturedHandle.ballZero)).mp hu.symm
  have hz : (q.2 : F) = 0 :=
    (congrArg
        (fun z : Smale.PuncturedHandle.UnitSphere E × Smale.PuncturedHandle.UnitBall F =>
          (z.2 : F))
        hq).symm
  exact (Metric.ne_of_mem_sphere q.2.property one_ne_zero) hz

private theorem
    Smale.SurgeryBoundaryPair.newExterior_avoids {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) (r : R) : d.newExterior r ∈ d.NewComplement := by
  rintro ⟨v, hv⟩
  obtain ⟨q, -, hq⟩ := (d.new_overlap r (Smale.PuncturedHandle.ballZero, v)).mp hv.symm
  have hz : (q.1 : E) = 0 :=
    (congrArg
        (fun z : Smale.PuncturedHandle.UnitBall E × Smale.PuncturedHandle.UnitSphere F =>
          (z.1 : E))
        hq).symm
  exact (Metric.ne_of_mem_sphere q.1.property one_ne_zero) hz

private theorem Smale.ClosedCover.isClosedEmbedding_codRestrict {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hf : Topology.IsClosedEmbedding f) {s : Set B}
    (hs : ∀ x, f x ∈ s) : Topology.IsClosedEmbedding (s.codRestrict f hs) :=
  ⟨hf.isEmbedding.codRestrict s hs, (hf.isClosedMap.codRestrict hs).isClosed_range⟩

private def Smale.SurgeryBoundaryPair.oldExteriorMap {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) : R → d.OldComplement :=
  d.OldComplement.codRestrict d.oldExterior d.oldExterior_avoids

private def Smale.SurgeryBoundaryPair.newExteriorMap {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) : R → d.NewComplement :=
  d.NewComplement.codRestrict d.newExterior d.newExterior_avoids

private def
    Smale.SurgeryBoundaryPair.oldParameterComplement {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) :
    (Smale.PuncturedHandle.UnitSphere E × Smale.PuncturedHandle.PuncturedBall F) ≃ₜ
      (d.oldPiece ⁻¹' d.OldComplement) :=
  (Smale.PuncturedHandle.oldPuncturedDomain E F).trans
    (Homeomorph.setCongr
      (by
        ext p
        exact (not_congr (d.oldPiece_mem_core_iff p)).symm))

private def
    Smale.SurgeryBoundaryPair.newParameterComplement {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) :
    (Smale.PuncturedHandle.PuncturedBall E × Smale.PuncturedHandle.UnitSphere F) ≃ₜ
      (d.newPiece ⁻¹' d.NewComplement) :=
  (Smale.PuncturedHandle.newPuncturedDomain E F).trans
    (Homeomorph.setCongr
      (by
        ext p
        exact (not_congr (d.newPiece_mem_belt_iff p)).symm))

private def Smale.SurgeryBoundaryPair.oldPuncturedMap {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) :
    Smale.PuncturedHandle.UnitSphere E × Smale.PuncturedHandle.PuncturedBall F →
      d.OldComplement :=
  d.OldComplement.restrictPreimage d.oldPiece ∘ d.oldParameterComplement

private def Smale.SurgeryBoundaryPair.newPuncturedMap {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) :
    Smale.PuncturedHandle.PuncturedBall E × Smale.PuncturedHandle.UnitSphere F →
      d.NewComplement :=
  d.NewComplement.restrictPreimage d.newPiece ∘ d.newParameterComplement

private theorem Smale.SurgeryBoundaryPair.isClosedEmbedding_oldExteriorMap {E F R X Y : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : Smale.SurgeryBoundaryPair E F R X Y) :
    Topology.IsClosedEmbedding d.oldExteriorMap :=
  Smale.ClosedCover.isClosedEmbedding_codRestrict d.oldExterior_closed d.oldExterior_avoids

private theorem Smale.SurgeryBoundaryPair.isClosedEmbedding_newExteriorMap {E F R X Y : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : Smale.SurgeryBoundaryPair E F R X Y) :
    Topology.IsClosedEmbedding d.newExteriorMap :=
  Smale.ClosedCover.isClosedEmbedding_codRestrict d.newExterior_closed d.newExterior_avoids

private theorem Smale.SurgeryBoundaryPair.isClosedEmbedding_oldPuncturedMap {E F R X Y : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : Smale.SurgeryBoundaryPair E F R X Y) :
    Topology.IsClosedEmbedding d.oldPuncturedMap :=
  (d.oldPiece_closed.restrictPreimage d.OldComplement).comp
    d.oldParameterComplement.isClosedEmbedding

private theorem Smale.SurgeryBoundaryPair.isClosedEmbedding_newPuncturedMap {E F R X Y : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : Smale.SurgeryBoundaryPair E F R X Y) :
    Topology.IsClosedEmbedding d.newPuncturedMap :=
  (d.newPiece_closed.restrictPreimage d.NewComplement).comp
    d.newParameterComplement.isClosedEmbedding

private theorem
    Smale.SurgeryBoundaryPair.oldComplement_cover {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) :
    Set.range d.oldExteriorMap ∪ Set.range d.oldPuncturedMap = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro z
  have hz : (z : X) ∈ Set.range d.oldExterior ∪ Set.range d.oldPiece := by
    rw [d.old_cover]
    trivial
  rcases hz with ⟨r, hr⟩ | ⟨p, hp⟩
  · exact Or.inl ⟨r, Subtype.ext hr⟩
  · have hpavoid : d.oldPiece p ∈ d.OldComplement := hp.symm ▸ z.property
    have hpne : (p.2 : F) ≠ 0 := fun h => hpavoid ((d.oldPiece_mem_core_iff p).mpr h)
    refine Or.inr ⟨(p.1, ⟨p.2, hpne, p.2.property⟩), Subtype.ext ?_⟩
    exact hp

private theorem
    Smale.SurgeryBoundaryPair.newComplement_cover {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) :
    Set.range d.newExteriorMap ∪ Set.range d.newPuncturedMap = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro z
  have hz : (z : Y) ∈ Set.range d.newExterior ∪ Set.range d.newPiece := by
    rw [d.new_cover]
    trivial
  rcases hz with ⟨r, hr⟩ | ⟨p, hp⟩
  · exact Or.inl ⟨r, Subtype.ext hr⟩
  · have hpavoid : d.newPiece p ∈ d.NewComplement := hp.symm ▸ z.property
    have hpne : (p.1 : E) ≠ 0 := fun h => hpavoid ((d.newPiece_mem_belt_iff p).mpr h)
    refine Or.inr ⟨(⟨p.1, hpne, p.1.property⟩, p.2), Subtype.ext ?_⟩
    exact hp

private theorem
    Smale.SurgeryBoundaryPair.oldPunctured_overlap {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) (r : R)
    (p : Smale.PuncturedHandle.UnitSphere E × Smale.PuncturedHandle.PuncturedBall F) :
    d.oldExteriorMap r = d.oldPuncturedMap p ↔
      ∃ q, r = d.boundary q ∧ p = (q.1, Smale.PuncturedHandle.boundaryPoint q.2) := by
  rw [Subtype.ext_iff]
  change d.oldExterior r = d.oldPiece (Smale.PuncturedHandle.oldPunctured p) ↔ _
  rw [d.old_overlap]
  constructor
  · rintro ⟨q, hr, hp⟩
    exact
      ⟨q, hr,
        Smale.PuncturedHandle.oldPunctured_injective
          (hp.trans (Smale.PuncturedHandle.oldPunctured_boundary q).symm)⟩
  · rintro ⟨q, hr, rfl⟩
    exact ⟨q, hr, Smale.PuncturedHandle.oldPunctured_boundary q⟩

private theorem
    Smale.SurgeryBoundaryPair.newPunctured_overlap {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) (r : R)
    (p : Smale.PuncturedHandle.PuncturedBall E × Smale.PuncturedHandle.UnitSphere F) :
    d.newExteriorMap r = d.newPuncturedMap p ↔
      ∃ q, r = d.boundary q ∧ p = (Smale.PuncturedHandle.boundaryPoint q.1, q.2) := by
  rw [Subtype.ext_iff]
  change d.newExterior r = d.newPiece (Smale.PuncturedHandle.newPunctured p) ↔ _
  rw [d.new_overlap]
  constructor
  · rintro ⟨q, hr, hp⟩
    exact
      ⟨q, hr,
        Smale.PuncturedHandle.newPunctured_injective
          (hp.trans (Smale.PuncturedHandle.newPunctured_boundary q).symm)⟩
  · rintro ⟨q, hr, rfl⟩
    exact ⟨q, hr, Smale.PuncturedHandle.newPunctured_boundary q⟩

private structure Smale.AttachmentBoundaryData (N P M : Type*) [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] (f : M → ℝ) (a : ℝ) where
  handle : PuncturedHandle.UnitBall N × PuncturedHandle.UnitBall P → M
  handle_closed : Topology.IsClosedEmbedding handle
  height_continuous : Continuous f
  lower_frontier : frontier {x | f x ≤ a} = {x | f x = a}
  lower_face : ∀ z, f (handle z) = a ↔ ‖(z.1 : N)‖ = 1
  upper_face : ∀ z, handle z ∈ frontier ({x | f x ≤ a} ∪ Set.range handle) ↔ ‖(z.2 : P)‖ = 1

private abbrev Smale.AttachmentBoundaryData.Level {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (_ : Smale.AttachmentBoundaryData N P M f a) :=
  { x : M // f x = a }

private abbrev Smale.AttachmentBoundaryData.region {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a) : Set M :=
  {x | f x ≤ a} ∪ Set.range d.handle

private abbrev Smale.AttachmentBoundaryData.Boundary {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a) :=
  frontier d.region

private abbrev Smale.AttachmentBoundaryData.Exterior {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a) :=
  { x : M // f x = a ∧ x ∈ d.Boundary }

private def Smale.AttachmentBoundaryData.oldExterior {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a) : d.Exterior → d.Level := fun x =>
  ⟨x, x.property.1⟩

private def Smale.AttachmentBoundaryData.newExterior {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a) : d.Exterior → d.Boundary := fun x =>
  ⟨x, x.property.2⟩

private def Smale.AttachmentBoundaryData.oldPiece {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a)
    (z : Smale.PuncturedHandle.UnitSphere N × Smale.PuncturedHandle.UnitBall P) : d.Level :=
  ⟨d.handle (Smale.PuncturedHandle.sphereToBall z.1, z.2),
    (d.lower_face _).mpr (mem_sphere_zero_iff_norm.mp z.1.property)⟩

private def Smale.AttachmentBoundaryData.newPiece {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a)
    (z : Smale.PuncturedHandle.UnitBall N × Smale.PuncturedHandle.UnitSphere P) : d.Boundary :=
  ⟨d.handle (z.1, Smale.PuncturedHandle.sphereToBall z.2),
    (d.upper_face _).mpr (mem_sphere_zero_iff_norm.mp z.2.property)⟩

private def Smale.AttachmentBoundaryData.boundary {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a)
    (q : Smale.PuncturedHandle.UnitSphere N × Smale.PuncturedHandle.UnitSphere P) : d.Exterior :=
  ⟨d.handle (Smale.PuncturedHandle.sphereToBall q.1, Smale.PuncturedHandle.sphereToBall q.2),
    (d.lower_face _).mpr (mem_sphere_zero_iff_norm.mp q.1.property),
    (d.upper_face _).mpr (mem_sphere_zero_iff_norm.mp q.2.property)⟩

private theorem
    Smale.AttachmentBoundaryData.oldExterior_closed {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a) : Topology.IsClosedEmbedding d.oldExterior :=
  Smale.ClosedCover.isClosedEmbedding_codRestrict
    ((isClosed_eq d.height_continuous continuous_const).inter
        isClosed_frontier).isClosedEmbedding_subtypeVal
    (fun x => x.property.1)

private theorem
    Smale.AttachmentBoundaryData.newExterior_closed {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a) : Topology.IsClosedEmbedding d.newExterior :=
  Smale.ClosedCover.isClosedEmbedding_codRestrict
    ((isClosed_eq d.height_continuous continuous_const).inter
        isClosed_frontier).isClosedEmbedding_subtypeVal
    (fun x => x.property.2)

private theorem
    Smale.AttachmentBoundaryData.sphereToBall_closed {N : Type*} [NormedAddCommGroup N] :
    Topology.IsClosedEmbedding (Smale.PuncturedHandle.sphereToBall (E := N)) :=
  Smale.ClosedCover.isClosedEmbedding_codRestrict
    Metric.isClosed_sphere.isClosedEmbedding_subtypeVal
    (fun u => (mem_sphere_zero_iff_norm.mp u.property).le)

private theorem Smale.AttachmentBoundaryData.oldPiece_closed {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a) : Topology.IsClosedEmbedding d.oldPiece := by
  exact
    Smale.ClosedCover.isClosedEmbedding_codRestrict
      (d.handle_closed.comp (sphereToBall_closed.prodMap Topology.IsClosedEmbedding.id))
      (fun z => (d.lower_face _).mpr (mem_sphere_zero_iff_norm.mp z.1.property))

private theorem Smale.AttachmentBoundaryData.newPiece_closed {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a) : Topology.IsClosedEmbedding d.newPiece := by
  apply Smale.ClosedCover.isClosedEmbedding_codRestrict
  exact d.handle_closed.comp (Topology.IsClosedEmbedding.id.prodMap sphereToBall_closed)

private theorem Smale.AttachmentBoundaryData.old_cover {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a) :
    Set.range d.oldExterior ∪ Set.range d.oldPiece = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : (x : M) ∈ Set.range d.handle
  · obtain ⟨z, hz⟩ := hx
    have hnorm : ‖(z.1 : N)‖ = 1 := (d.lower_face z).mp (hz ▸ x.property)
    refine Or.inr ⟨(⟨z.1, mem_sphere_zero_iff_norm.mpr hnorm⟩, z.2), ?_⟩
    exact Subtype.ext hz
  · have hfront : (x : M) ∈ d.Boundary := by
      have hlow : (x : M) ∈ frontier {y | f y ≤ a} := by
        rw [d.lower_frontier]
        exact x.property
      change (x : M) ∈ frontier d.region
      rw [frontier] at hlow ⊢
      refine ⟨closure_mono Set.subset_union_left hlow.1, ?_⟩
      intro hi
      apply hlow.2
      apply mem_interior_iff_mem_nhds.mpr
      have hnear := mem_interior_iff_mem_nhds.mp hi
      have hout := d.handle_closed.isClosed_range.isOpen_compl.mem_nhds hx
      apply Filter.mem_of_superset (Filter.inter_mem hnear hout)
      intro y hy
      exact hy.1.resolve_right hy.2
    exact Or.inl ⟨⟨x, x.property, hfront⟩, rfl⟩

private theorem Smale.AttachmentBoundaryData.new_cover {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a) :
    Set.range d.newExterior ∪ Set.range d.newPiece = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hclosed : IsClosed d.region :=
    (isClosed_le d.height_continuous continuous_const).union d.handle_closed.isClosed_range
  have hx : (x : M) ∈ d.region := by
    have hc := frontier_subset_closure x.property
    rwa [hclosed.closure_eq] at hc
  rcases hx with hx | ⟨z, hz⟩
  · have heq : f x = a := by
      apply le_antisymm hx
      by_contra hn
      have hlt : f x < a := lt_of_not_ge hn
      have hi : (x : M) ∈ interior d.region :=
        interior_maximal (fun y (hy : f y < a) => Or.inl hy.le)
          (isOpen_lt d.height_continuous continuous_const) hlt
      exact x.property.2 hi
    exact Or.inl ⟨⟨x, heq, x.property⟩, rfl⟩
  · have hnorm : ‖(z.2 : P)‖ = 1 := (d.upper_face z).mp (hz ▸ x.property)
    refine Or.inr ⟨(z.1, ⟨z.2, mem_sphere_zero_iff_norm.mpr hnorm⟩), ?_⟩
    exact Subtype.ext hz

private theorem Smale.AttachmentBoundaryData.old_overlap {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a) (r : d.Exterior)
    (z : Smale.PuncturedHandle.UnitSphere N × Smale.PuncturedHandle.UnitBall P) :
    d.oldExterior r = d.oldPiece z ↔
      ∃ q, r = d.boundary q ∧ z = Smale.PuncturedHandle.oldBoundary q := by
  constructor
  · intro h
    have hr : (r : M) = d.handle (Smale.PuncturedHandle.sphereToBall z.1, z.2) :=
      congrArg Subtype.val h
    have hnorm : ‖(z.2 : P)‖ = 1 := (d.upper_face _).mp (hr ▸ r.property.2)
    refine ⟨(z.1, ⟨z.2, mem_sphere_zero_iff_norm.mpr hnorm⟩), Subtype.ext hr, rfl⟩
  · rintro ⟨q, rfl, rfl⟩
    rfl

private theorem Smale.AttachmentBoundaryData.new_overlap {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a) (r : d.Exterior)
    (z : Smale.PuncturedHandle.UnitBall N × Smale.PuncturedHandle.UnitSphere P) :
    d.newExterior r = d.newPiece z ↔
      ∃ q, r = d.boundary q ∧ z = Smale.PuncturedHandle.newBoundary q := by
  constructor
  · intro h
    have hr : (r : M) = d.handle (z.1, Smale.PuncturedHandle.sphereToBall z.2) :=
      congrArg Subtype.val h
    have hnorm : ‖(z.1 : N)‖ = 1 := (d.lower_face _).mp (hr ▸ r.property.1)
    refine ⟨(⟨z.1, mem_sphere_zero_iff_norm.mpr hnorm⟩, z.2), Subtype.ext hr, rfl⟩
  · rintro ⟨q, rfl, rfl⟩
    rfl

private def Smale.AttachmentBoundaryData.surgeryBoundaryPair {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.AttachmentBoundaryData N P M f a) :
    Smale.SurgeryBoundaryPair N P d.Exterior d.Level d.Boundary
    where
  oldExterior := d.oldExterior
  newExterior := d.newExterior
  oldPiece := d.oldPiece
  newPiece := d.newPiece
  oldExterior_closed := d.oldExterior_closed
  newExterior_closed := d.newExterior_closed
  oldPiece_closed := d.oldPiece_closed
  newPiece_closed := d.newPiece_closed
  old_cover := d.old_cover
  new_cover := d.new_cover
  boundary := d.boundary
  old_overlap := d.old_overlap
  new_overlap := d.new_overlap

private def Smale.MorseHandle.unitBallHomeomorph (N : Type*) [NormedAddCommGroup N] :
    Smale.PuncturedHandle.UnitBall N ≃ₜ UnitDisk N
    where
  toFun z := ⟨z, mem_closedBall_zero_iff.mpr z.property⟩
  invFun z := ⟨z, mem_closedBall_zero_iff.mp z.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.handleBallCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    (Smale.PuncturedHandle.UnitBall c.NegativeCoordinates ×
        Smale.PuncturedHandle.UnitBall c.PositiveCoordinates) ≃ₜ
      (Smale.MorseHandle.UnitDisk c.NegativeCoordinates ×
        Smale.MorseHandle.UnitDisk c.PositiveCoordinates) :=
  (Smale.MorseHandle.unitBallHomeomorph c.NegativeCoordinates).prodCongr
    (Smale.MorseHandle.unitBallHomeomorph c.PositiveCoordinates)

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.normHandleMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    C(Smale.PuncturedHandle.UnitBall c.NegativeCoordinates ×
        Smale.PuncturedHandle.UnitBall c.PositiveCoordinates,
      M) :=
  ⟨fun z => c.attachingHandleMap ρ hρ hblock (c.handleBallCoordinates z),
    (c.attachingHandleMap ρ hρ hblock).continuous.comp c.handleBallCoordinates.continuous⟩

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.range_normHandleMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Set.range (c.normHandleMap ρ hρ hblock) = Set.range (c.attachingHandleMap ρ hρ hblock) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨c.handleBallCoordinates z, rfl⟩
  · rintro ⟨z, rfl⟩
    refine ⟨c.handleBallCoordinates.symm z, ?_⟩
    change
      c.attachingHandleMap ρ hρ hblock
          (c.handleBallCoordinates (c.handleBallCoordinates.symm z)) =
        _
    rw [c.handleBallCoordinates.apply_symm_apply]

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.attachmentBoundaryData {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M]
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hlevel : frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2}) :
    Smale.AttachmentBoundaryData c.NegativeCoordinates c.PositiveCoordinates M f (f p - ρ ^ 2)
    where
  handle := c.normHandleMap ρ hρ hblock
  handle_closed :=
    (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).comp
      c.handleBallCoordinates.isClosedEmbedding
  height_continuous := hf
  lower_frontier := hlevel
  lower_face := fun z => by
    constructor
    · intro hz
      exact (c.attachingHandleMap_lower_iff ρ hρ hblock (c.handleBallCoordinates z)).mp hz.le
    · intro hz
      exact c.attachingHandleMap_boundary_height ρ hρ hblock (c.handleBallCoordinates z) hz
  upper_face := fun z => by
    rw [c.range_normHandleMap ρ hρ hblock]
    exact c.attachingHandleMap_mem_frontier_iff hf ρ hρ hblock (c.handleBallCoordinates z)

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.SignedMorseChart.attachingCoreMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    C(Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates, { y : M // f y = f p - ρ ^ 2 }) :=
  (c.attachingBoundaryMap ρ hρ hblock).comp
    ⟨fun u => (u, ⟨0, by simp⟩), continuous_id.prodMk continuous_const⟩

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.attachingCoreMap_coe {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (u : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates) :
    (c.attachingCoreMap ρ hρ hblock u : M) =
      c.splitChart.symm (ρ • (u : c.NegativeCoordinates), 0) := by
  change
    c.splitChart.symm
        ((ρ * Real.sqrt (1 + ‖(0 : c.PositiveCoordinates)‖ ^ 2)) • (u : c.NegativeCoordinates),
          ρ • (0 : c.PositiveCoordinates)) =
      _
  simp

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.contMDiff_attachingCoreMap_ambient {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)] (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val ∘ c.attachingCoreMap ρ hρ hblock) := by
  have heq :
    Subtype.val ∘ c.attachingCoreMap ρ hρ hblock =
      fun u : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates =>
      c.splitChart.symm (ρ • (u : c.NegativeCoordinates), 0) :=
    funext (c.attachingCoreMap_coe ρ hρ hblock)
  rw [heq]
  have hcoe :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates) ∞
      (Subtype.val :
        Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates → c.NegativeCoordinates) :=
    contMDiff_coe_sphere (E := c.NegativeCoordinates) (n := n)
  have hscalar :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun _ : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates => ρ) :=
    contMDiff_const
  have hnegative :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates) ∞
      (fun u : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates =>
        ρ • (u : c.NegativeCoordinates)) :=
    hscalar.smul hcoe
  have hcoords :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) ∞
      (fun u : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates =>
        (ρ • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates))) :=
    hnegative.prodMk_space contMDiff_const
  apply c.splitChart.contMDiffOn_invFun.comp_contMDiff hcoords
  intro u
  have hh :=
    hblock
      (Smale.MorseHandle.modelMap_mem_product hρ
        (⟨(u : c.NegativeCoordinates), Metric.sphere_subset_closedBall u.property⟩,
          (⟨0, by simp⟩ : Smale.MorseHandle.UnitDisk c.PositiveCoordinates)))
  simpa [Smale.MorseHandle.modelMap] using hh

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.contMDiff_attachingCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (n : ℕ) [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    letI := Smale.RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (c.attachingCoreMap ρ hρ hblock) := by
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  exact
    (Smale.RegularLevel.contMDiff_iff_inclusion hf hreg (𝓡 n)
          (c.attachingCoreMap ρ hρ hblock)).mpr
      (c.contMDiff_attachingCoreMap_ambient n ρ hρ hblock)

private theorem Smale.MorseHandle.quadratic_descentFlow_lt {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {t : ℝ} (ht : 0 < t) {z : N × P}
    (hz : z ≠ 0) : quadratic (descentFlow t z) < quadratic z := by
  have h₁ :=
    (sq_le_sq₀ (norm_nonneg z.1) (norm_nonneg (descentFlow t z).1)).mpr
      (norm_fst_le_descentFlow ht.le z)
  have h₂ :=
    (sq_le_sq₀ (norm_nonneg (descentFlow t z).2) (norm_nonneg z.2)).mpr
      (norm_snd_descentFlow_le ht.le z)
  by_cases hu : z.1 = 0
  · have hv : z.2 ≠ 0 := fun hv => hz (Prod.ext hu hv)
    have hvnorm : ‖(descentFlow t z).2‖ < ‖z.2‖ := by
      rw [norm_descentFlow_snd]
      exact
        mul_lt_of_lt_one_left (norm_pos_iff.mpr hv) (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
    have hv₂ := (sq_lt_sq₀ (norm_nonneg (descentFlow t z).2) (norm_nonneg z.2)).mpr hvnorm
    exact add_lt_add_of_le_of_lt (neg_le_neg h₁) hv₂
  · have hunorm : ‖z.1‖ < ‖(descentFlow t z).1‖ := by
      rw [norm_descentFlow_fst]
      exact lt_mul_of_one_lt_left (norm_pos_iff.mpr hu) (Real.one_lt_exp_iff.mpr ht)
    have hu₂ := (sq_lt_sq₀ (norm_nonneg z.1) (norm_nonneg (descentFlow t z).1)).mpr hunorm
    exact add_lt_add_of_lt_of_le (neg_lt_neg hu₂) h₂

private theorem Smale.MorseHandle.descentFlow_mem_interior_lower_union_handle {N P : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {ρ t : ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) {z : N × P}
    (hz : z ∈ {w | quadratic w ≤ -(ρ ^ 2)} ∪ Set.range (modelMap ρ)) :
    descentFlow t z ∈ interior ({w | quadratic w ≤ -(ρ ^ 2)} ∪ Set.range (modelMap ρ)) := by
  have hc : Continuous (quadratic (N := N) (P := P)) :=
    (continuous_fst.norm.pow 2).neg.add (continuous_snd.norm.pow 2)
  rw [mem_lower_union_handle_iff hρ] at hz
  rcases hz with hq | hv
  · have hne : z ≠ 0 := by
      intro h
      have hq' : (0 : ℝ) ≤ -(ρ ^ 2) := by simpa [h, quadratic] using hq
      nlinarith [sq_pos_of_pos hρ]
    have hlt : quadratic (descentFlow t z) < -(ρ ^ 2) :=
      (quadratic_descentFlow_lt ht hne).trans_le hq
    apply mem_interior.mpr
    refine ⟨{w | quadratic w < -(ρ ^ 2)}, ?_, isOpen_lt hc continuous_const, hlt⟩
    intro w hw
    exact Or.inl (show quadratic w ≤ -(ρ ^ 2) from le_of_lt hw)
  · have hlt : ‖(descentFlow t z).2‖ < ρ := by
      rw [norm_descentFlow_snd]
      calc
        _ ≤ Real.exp (-t) * ρ := mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
        _ < ρ := mul_lt_of_lt_one_left hρ (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
    apply mem_interior.mpr
    refine ⟨{w : N × P | ‖w.2‖ < ρ}, ?_, isOpen_lt continuous_snd.norm continuous_const, hlt⟩
    intro w hw
    exact (mem_lower_union_handle_iff hρ w).mpr (Or.inr hw.le)

private theorem Smale.FlowConstruction.partialChartField_eq_mfderiv_symm {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞)
    (W : F → F) {x : M} (hx : x ∈ e.source) :
    partialChartField e W x =
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e.symm (e x)
        ((NormedSpace.fromTangentSpace (e x)).symm (W (e x))) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have h₁ := he.comp_symm_deriv (e'.map_source hx)
  rw [e'.left_inv hx] at h₁
  have hi := ContinuousLinearMap.inverse_eq h₁ (he.symm_comp_deriv hx)
  unfold partialChartField
  rw [VectorField.mpullback_apply]
  change
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e' x).inverse
        ((NormedSpace.fromTangentSpace (e' x)).symm (W (e' x))) =
      _
  rw [hi]
  rfl

private theorem Smale.FlowConstruction.hasMFDerivAt_lift_partialChartCurve {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞)
    (W : F → F) {α : ℝ → F} {t : ℝ} (hα : HasDerivAt α (W (α t)) t) (ht : α t ∈ e.target) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (e.symm ∘ α) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (partialChartField e W (e.symm (α t)))) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hi := (he.mdifferentiableAt_symm ht).hasMFDerivAt
  have hd := hi.comp t hα.hasFDerivAt.hasMFDerivAt
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e'.symm (α t))
        ((NormedSpace.fromTangentSpace t a) •
          (NormedSpace.fromTangentSpace (α t)).symm (W (α t))) =
      (NormedSpace.fromTangentSpace t a) • partialChartField e W (e'.symm (α t))
  rw [map_smul, partialChartField_eq_mfderiv_symm e W (e'.map_target ht)]
  rw [show e (e'.symm (α t)) = α t from e'.right_inv ht]
  rfl

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.eventually_flow_eq_descentModel {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M}
    (hx : x ∈ c.splitChart.source) (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      F t x = c.splitChart.symm (Smale.MorseHandle.descentFlow t (c.splitChart x)) := by
  let e := c.splitChart.toOpenPartialHomeomorph
  let α : ℝ → c.NegativeCoordinates × c.PositiveCoordinates := fun t =>
    Smale.MorseHandle.descentFlow t (c.splitChart x)
  let γ : ℝ → M := e.symm ∘ α
  have hα : Continuous α :=
    Smale.MorseHandle.descentFlow.continuous continuous_id continuous_const
  have hα₀ : α 0 = e x := Smale.MorseHandle.descentFlow.map_zero_apply _
  have htarget : ∀ᶠ t in 𝓝 (0 : ℝ), α t ∈ e.target :=
    hα.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds (hα₀ ▸ e.map_source hx))
  have hγ₀ : γ 0 = x := by
    change e.symm (α 0) = x
    rw [hα₀, e.left_inv hx]
  have hγc : ContinuousAt γ 0 :=
    (e.continuousAt_symm (hα₀ ▸ e.map_source hx)).comp hα.continuousAt
  have hγt : Filter.Tendsto γ (𝓝 (0 : ℝ)) (𝓝 x) := by simpa only [ContinuousAt, hγ₀] using hγc
  have hγ : IsMIntegralCurveAt γ V 0 := by
    filter_upwards [htarget, hγt.eventually heq] with t ht heqt
    change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ t)))
    rw [heqt]
    exact
      Smale.FlowConstruction.hasMFDerivAt_lift_partialChartCurve c.splitChart
        Smale.MorseHandle.descent (Smale.MorseHandle.hasDerivAt_descentFlow (c.splitChart x) t) ht
  have h₀ : F 0 x = γ 0 := (F.map_zero_apply x).trans hγ₀.symm
  exact
    isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless (hV.contMDiffAt)
      ((hcurve x).isMIntegralCurveAt 0) hγ h₀

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.flow_eqOn_descentModel {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M}
    (hx : x ∈ c.splitChart.source) {S : Set ℝ} (hS : IsPreconnected S) (hzero : 0 ∈ S)
    (htarget : ∀ t ∈ S, Smale.MorseHandle.descentFlow t (c.splitChart x) ∈ c.splitChart.target)
    (heq :
      ∀ t ∈ S,
        ∀ᶠ y in 𝓝 (c.splitChart.symm (Smale.MorseHandle.descentFlow t (c.splitChart x))),
          V y = c.descentField y) :
    Set.EqOn (fun t => F t x)
      (fun t => c.splitChart.symm (Smale.MorseHandle.descentFlow t (c.splitChart x))) S := by
  let α : ℝ → c.NegativeCoordinates × c.PositiveCoordinates := fun t =>
    Smale.MorseHandle.descentFlow t (c.splitChart x)
  let γ : ℝ → M := c.splitChart.symm ∘ α
  have hα : Continuous α :=
    Smale.MorseHandle.descentFlow.continuous continuous_id continuous_const
  have hγ : ∀ t ∈ S, IsMIntegralCurveAt γ V t := by
    intro t ht
    have hlocal : ∀ᶠ s in 𝓝 t, α s ∈ c.splitChart.target :=
      hα.continuousAt.preimage_mem_nhds (c.splitChart.open_target.mem_nhds (htarget t ht))
    have hc : ContinuousAt c.splitChart.toOpenPartialHomeomorph.symm (α t) :=
      c.splitChart.toOpenPartialHomeomorph.continuousAt_symm (htarget t ht)
    have hγc : ContinuousAt γ t := hc.comp (f := α) hα.continuousAt
    filter_upwards [hlocal, hγc.eventually (heq t ht)] with s hs heqs
    change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ s)))
    rw [heqs]
    exact
      Smale.FlowConstruction.hasMFDerivAt_lift_partialChartCurve c.splitChart
        Smale.MorseHandle.descent (Smale.MorseHandle.hasDerivAt_descentFlow (c.splitChart x) s) hs
  have hγc : Continuous (fun t : S => γ t.val) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hγ t.val t.property).continuousAt).comp continuousAt_subtype_val
  let U : Set S := {t | F t.val x = γ t.val}
  have hclosed : IsClosed U :=
    isClosed_eq (F.continuous continuous_subtype_val continuous_const) hγc
  have hopen : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hlocal :=
      isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless hV.contMDiffAt
        ((hcurve x).isMIntegralCurveAt t.val) (hγ t.val t.property) ht
    exact continuousAt_subtype_val.eventually hlocal
  have hγzero : γ 0 = x := by
    change c.splitChart.symm (Smale.MorseHandle.descentFlow 0 (c.splitChart x)) = x
    rw [Smale.MorseHandle.descentFlow.map_zero_apply]
    exact c.splitChart.left_inv' hx
  have hnonempty : U.Nonempty := ⟨⟨0, hzero⟩, (F.map_zero_apply x).trans hγzero.symm⟩
  let : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have huniv : U = Set.univ := (show IsClopen U from ⟨hclosed, hopen⟩).eq_univ hnonempty
  intro t ht
  have hmem : (⟨t, ht⟩ : S) ∈ U := huniv ▸ Set.mem_univ _
  exact hmem

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.flow_eq_descentModel_of_mem_uIcc {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M}
    (hx : x ∈ c.splitChart.source) {t : ℝ}
    (htarget :
      ∀ s ∈ Set.uIcc 0 t, Smale.MorseHandle.descentFlow s (c.splitChart x) ∈ c.splitChart.target)
    (heq :
      ∀ s ∈ Set.uIcc 0 t,
        ∀ᶠ y in 𝓝 (c.splitChart.symm (Smale.MorseHandle.descentFlow s (c.splitChart x))),
          V y = c.descentField y) :
    F t x = c.splitChart.symm (Smale.MorseHandle.descentFlow t (c.splitChart x)) :=
  c.flow_eqOn_descentModel hV F hcurve hx isPreconnected_uIcc Set.left_mem_uIcc htarget heq
    Set.right_mem_uIcc

end Mathoverflow1973

end
