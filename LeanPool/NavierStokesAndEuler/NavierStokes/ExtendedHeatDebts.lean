/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatProfileExtension
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricTerminalCompensation
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Literal heat debts on an open physical parameter domain

Negative diffusion uses the constructed smooth heat-profile extension. The
three debts remain the actual improper integrals of the edited outgoing
profile. All differentiated kernels and their integrable majorants are
derived from that extension.
-/

@[expose] public section


noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.ExtendedHeatDebts

open HeatTailEdit OutgoingTail
open ParametricHeatTail (jetProduct jetProduct_nonneg jetProduct_continuousOn
  jetProduct_bound tailWeight tailDecay tailSize tailSize_nonneg tailWeight_continuousOn
  tailWeight_bound diffusion diffusion_contDiff diffusion_hasDerivAt)

/-! ## Dominated derivative chains on the entire real parameter line -/

section IntegralChain

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {J : ℕ → ℝ → α → ℝ}

/-- Chain dominated, given by `∀ n L, 0 < L → ∃ b : α → ℝ, Integrable b μ ∧ ∀ᵐ t ∂μ, ∀ ν : ℝ,
|ν| ≤ L → ‖J n ν t‖ ≤ b t`. -/
noncomputable def ChainDominated (J : ℕ → ℝ → α → ℝ) (μ : Measure α) : Prop :=
  ∀ n L, 0 < L → ∃ b : α → ℝ, Integrable b μ ∧
    ∀ᵐ t ∂μ, ∀ ν : ℝ, |ν| ≤ L → ‖J n ν t‖ ≤ b t

variable
  (hJ : ∀ᵐ t ∂μ, ∀ n ν, HasDerivAt (fun u => J n u t) (J (n + 1) ν t) ν)
  (hm : ∀ n ν, AEStronglyMeasurable (J n ν) μ)
  (hb : ChainDominated J μ)

include hm hb

theorem chain_integrable (n : ℕ) (ν : ℝ) : Integrable (J n ν) μ := by
  obtain ⟨b, hi, hbound⟩ := hb n (|ν| + 1) (by positivity)
  exact hi.mono' (hm n ν) (hbound.mono fun t ht => ht ν (by linarith))

include hJ

theorem integral_chain_hasDerivAt (n : ℕ) (ν : ℝ) :
    HasDerivAt (fun u => ∫ t, J n u t ∂μ) (∫ t, J (n + 1) ν t ∂μ) ν := by
  obtain ⟨b, hi, hbound⟩ := hb (n + 1) (|ν| + 1) (by positivity)
  have hball {u : ℝ} (hu : u ∈ Metric.ball ν 1) : |u| ≤ |ν| + 1 := by
    have hdist : |u - ν| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hu
    calc
      |u| = |(u - ν) + ν| := by congr 1; ring
      _ ≤ |u - ν| + |ν| := abs_add_le _ _
      _ ≤ |ν| + 1 := by linarith
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u t => J n u t) (F' := fun u t => J (n + 1) u t)
    (bound := b) (μ := μ) (Metric.ball_mem_nhds ν (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (hm n)) (chain_integrable hm hb n ν) (hm (n + 1) ν)
    (hbound.mono fun t ht u hu => ht u (hball hu)) hi
    (hJ.mono fun t ht u _ => ht n u)).2

theorem iteratedDeriv_integral_chain (n : ℕ) (ν : ℝ) :
    iteratedDeriv n (fun u => ∫ t, J 0 u t ∂μ) ν = ∫ t, J n ν t ∂μ := by
  induction n generalizing ν with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, funext ih]
      exact (integral_chain_hasDerivAt hJ hm hb n ν).deriv

theorem contDiff_integral_chain : ContDiff ℝ ∞ (fun u => ∫ t, J 0 u t ∂μ) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [funext (iteratedDeriv_integral_chain hJ hm hb n)]
  exact fun ν => (integral_chain_hasDerivAt hJ hm hb n ν).differentiableAt

end IntegralChain

/-! ## The actual extended edit and all its diffusion derivatives -/

/-- Correction, given by `switch K X * (HeatProfileExtension.scaledProfile (1 + h) X ν - 1)`. -/
noncomputable def correction (h K ν X : ℝ) : ℝ :=
  switch K X * (HeatProfileExtension.scaledProfile (1 + h) X ν - 1)

/-- Multiplier, given by `1 + correction h K ν X`. -/
noncomputable def multiplier (h ν K X : ℝ) : ℝ := 1 + correction h K ν X

/-- Edit, given by `E X * multiplier h ν K X`. -/
noncomputable def edit (E : ℝ → ℝ) (h ν K X : ℝ) : ℝ := E X * multiplier h ν K X

/-- Change, given by `edit E h ν K X - E X`. -/
noncomputable def change (E : ℝ → ℝ) (h ν K X : ℝ) : ℝ := edit E h ν K X - E X

/-- Square change, given by `edit E h ν K X ^ 2 - E X ^ 2`. -/
noncomputable def squareChange (E : ℝ → ℝ) (h ν K X : ℝ) : ℝ :=
  edit E h ν K X ^ 2 - E X ^ 2

/-- Correction jet, given by `iteratedDeriv n (fun u => correction h K u X) ν`. -/
noncomputable def correctionJet (h K : ℝ) (n : ℕ) (ν X : ℝ) : ℝ :=
  iteratedDeriv n (fun u => correction h K u X) ν

/-- Correction bound, with branches according to `n = 0`. -/
noncomputable def correctionBound (h L : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 2 * HeatProfileExtension.derivativeBound (1 + h) 1 * L
  else 2 ^ n * HeatProfileExtension.derivativeBound (1 + h) n

theorem correctionBound_zero (h L : ℝ) :
    correctionBound h L 0 = 2 * HeatProfileExtension.derivativeBound (1 + h) 1 * L := by
  simp only [correctionBound, ↓reduceIte]

theorem correctionBound_succ (h L : ℝ) (n : ℕ) :
    correctionBound h L (n + 1) =
      2 ^ (n + 1) * HeatProfileExtension.derivativeBound (1 + h) (n + 1) := by
  simp only [correctionBound, Nat.add_one_ne_zero, ite_false]

theorem correction_contDiff {h : ℝ} (hh : 0 < h) (K X : ℝ) :
    ContDiff ℝ ∞ (fun ν => correction h K ν X) :=
  contDiff_const.mul (((HeatProfileExtension.extension_contDiff (a := 1 + h) (by linarith)).comp
    ((contDiff_const.mul contDiff_id).div_const X)).sub contDiff_const)

theorem correctionJet_hasDerivAt {h : ℝ} (hh : 0 < h) (K X : ℝ) (n : ℕ) (ν : ℝ) :
    HasDerivAt (fun u => correctionJet h K n u X) (correctionJet h K (n + 1) ν X) ν := by
  have hd := (correction_contDiff hh K X).differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n) ν
  simpa only [correctionJet, iteratedDeriv_succ] using hd.hasDerivAt

theorem correctionJet_zero (h K ν X : ℝ) : correctionJet h K 0 ν X = correction h K ν X := rfl

theorem correctionJet_succ {h : ℝ} (hh : 0 < h) (K X ν : ℝ) (n : ℕ) :
    correctionJet h K (n + 1) ν X = switch K X * (2 / X) ^ (n + 1) *
      iteratedDeriv (n + 1) (HeatProfileExtension.extension (1 + h)) (2 * ν / X) := by
  have hc : ContDiff ℝ ∞ (HeatProfileExtension.scaledProfile (1 + h) X) :=
    (HeatProfileExtension.extension_contDiff (a := 1 + h) (by linarith)).comp
      ((contDiff_const.mul contDiff_id).div_const X)
  unfold correctionJet correction
  rw [iteratedDeriv_const_mul _ ((hc.sub contDiff_const).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl (n + 1))).contDiffAt]
  rw [show (fun x => HeatProfileExtension.scaledProfile (1 + h) X x - 1) =
    (fun x => (-1 : ℝ) + HeatProfileExtension.scaledProfile (1 + h) X x) by funext x; ring,
    iteratedDeriv_const_add (Nat.succ_pos n),
    HeatProfileExtension.iteratedDeriv_scaledProfile (a := 1 + h) (by linarith)]
  simp only [Nat.succ_eq_add_one, mul_assoc]

theorem correctionBound_nonneg (h : ℝ) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    0 ≤ correctionBound h L n := by
  cases n with
  | zero =>
      rw [correctionBound_zero]
      exact mul_nonneg (mul_nonneg (by norm_num)
        (HeatProfileExtension.derivativeBound_nonneg _ _)) hL
  | succ n =>
      rw [correctionBound_succ]
      exact mul_nonneg (by positivity) (HeatProfileExtension.derivativeBound_nonneg _ _)

theorem correctionJet_continuousOn_X {h K : ℝ} (hh : 0 < h) (hK : 0 < K)
    (n : ℕ) (ν : ℝ) : ContinuousOn (fun X => correctionJet h K n ν X) (Ioi 0) := by
  have hr : ContinuousOn (fun X : ℝ => 2 * ν / X) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun X hX => (show 0 < X from hX).ne')
  have hH := HeatProfileExtension.extension_contDiff (a := 1 + h) (by linarith)
  cases n with
  | zero =>
      exact (switch_contDiffOn hK).continuousOn.mul
        ((hH.continuous.comp_continuousOn hr).sub continuousOn_const)
  | succ n =>
      simp_rw [correctionJet_succ hh]
      have hratio : ContinuousOn (fun X : ℝ => (2 : ℝ) / X) (Ioi 0) :=
        continuousOn_const.div continuousOn_id (fun X hX => (show 0 < X from hX).ne')
      exact ((switch_contDiffOn hK).continuousOn.mul
        (hratio.pow (n + 1))).mul
        ((hH.continuous_iteratedDeriv (n + 1)
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)).comp_continuousOn hr)

theorem correctionJet_bound {h K L ν X : ℝ} (hh : 0 < h) (hX : 1 ≤ X)
    (hν : |ν| ≤ L) (n : ℕ) : |correctionJet h K n ν X| ≤ correctionBound h L n / X := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hsw := switch_bounds K X
  cases n with
  | zero =>
      change |switch K X * (HeatProfileExtension.scaledProfile (1 + h) X ν - 1)| ≤ _
      rw [abs_mul, abs_of_nonneg hsw.1]
      calc
        _ ≤ 1 * |HeatProfileExtension.scaledProfile (1 + h) X ν - 1| :=
          mul_le_mul_of_nonneg_right hsw.2 (abs_nonneg _)
        _ ≤ 2 * HeatProfileExtension.derivativeBound (1 + h) 1 * |ν| / X := by
          simpa only [one_mul] using HeatProfileExtension.scaledProfile_sub_one_bound
            (a := 1 + h) (by linarith) hXp ν
        _ ≤ correctionBound h L 0 / X := by
          change 2 * HeatProfileExtension.derivativeBound (1 + h) 1 * |ν| / X ≤
            (2 * HeatProfileExtension.derivativeBound (1 + h) 1 * L) / X
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hν (mul_nonneg (by norm_num)
              (HeatProfileExtension.derivativeBound_nonneg _ _))) hXp.le
  | succ n =>
      have hp : (2 / X) ^ (n + 1) ≤ 2 ^ (n + 1) / X := by
        rw [div_pow]
        exact div_le_div_of_nonneg_left (by positivity) hXp (le_self_pow₀ hX (by omega))
      rw [correctionJet_succ hh, abs_mul, abs_mul, abs_of_nonneg hsw.1,
        abs_of_nonneg (pow_nonneg (div_nonneg (by norm_num) hXp.le) _)]
      have hj := HeatProfileExtension.extension_derivative_bound (a := 1 + h)
        (by linarith) (n + 1) (2 * ν / X)
      rw [Real.norm_eq_abs] at hj
      calc
        _ ≤ 1 * (2 ^ (n + 1) / X) * HeatProfileExtension.derivativeBound (1 + h) (n + 1) := by
          gcongr
          exact hsw.2
        _ = correctionBound h L (n + 1) / X := by rw [correctionBound_succ]; ring

/-- Square correction jet, given by `2 * correctionJet h K n ν X + jetProduct (fun i =>
correctionJet h K i ν X) (fun i => correctionJet h K i ν X) n`. -/
noncomputable def squareCorrectionJet (h K : ℝ) (n : ℕ) (ν X : ℝ) : ℝ :=
  2 * correctionJet h K n ν X +
    jetProduct (fun i => correctionJet h K i ν X) (fun i => correctionJet h K i ν X) n

/-- Square correction bound, given by `2 * correctionBound h L n + jetProduct (correctionBound h
L) (correctionBound h L) n`. -/
noncomputable def squareCorrectionBound (h L : ℝ) (n : ℕ) : ℝ :=
  2 * correctionBound h L n + jetProduct (correctionBound h L) (correctionBound h L) n

theorem squareCorrectionJet_zero (h K ν X : ℝ) :
    squareCorrectionJet h K 0 ν X = multiplier h ν K X ^ 2 - 1 := by
  simp only [squareCorrectionJet, jetProduct, correctionJet_zero, multiplier]
  ring

theorem squareCorrectionJet_hasDerivAt {h : ℝ} (hh : 0 < h) (K X : ℝ) (n : ℕ) (ν : ℝ) :
    HasDerivAt (fun u => squareCorrectionJet h K n u X)
      (squareCorrectionJet h K (n + 1) ν X) ν := by
  have hp := ParametricHeatTail.jetProduct_hasDerivWithinAt (s := univ)
    (fun i => (correctionJet_hasDerivAt hh K X i ν).hasDerivWithinAt)
    (fun i => (correctionJet_hasDerivAt hh K X i ν).hasDerivWithinAt) n
  exact ((correctionJet_hasDerivAt hh K X n ν).const_mul 2).add
    (by simpa only [hasDerivWithinAt_univ] using hp)

theorem squareCorrectionJet_continuousOn_X {h K : ℝ} (hh : 0 < h) (hK : 0 < K)
    (n : ℕ) (ν : ℝ) : ContinuousOn (fun X => squareCorrectionJet h K n ν X) (Ioi 0) :=
  (continuousOn_const.mul (correctionJet_continuousOn_X hh hK n ν)).add
    (jetProduct_continuousOn (fun i => correctionJet_continuousOn_X hh hK i ν)
      (fun i => correctionJet_continuousOn_X hh hK i ν) n)

theorem squareCorrectionBound_nonneg (h : ℝ) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    0 ≤ squareCorrectionBound h L n :=
  add_nonneg (mul_nonneg (by norm_num) (correctionBound_nonneg h hL n))
    (jetProduct_nonneg (correctionBound_nonneg h hL) (correctionBound_nonneg h hL) n)

theorem squareCorrectionJet_bound {h K L ν X : ℝ} (hh : 0 < h) (hX : 1 ≤ X)
    (hν : |ν| ≤ L) (n : ℕ) :
    |squareCorrectionJet h K n ν X| ≤ squareCorrectionBound h L n / X := by
  have hL : 0 ≤ L := (abs_nonneg ν).trans hν
  calc
    _ ≤ |2 * correctionJet h K n ν X| +
        |jetProduct (fun i => correctionJet h K i ν X) (fun i => correctionJet h K i ν X) n| :=
      abs_add_le _ _
    _ ≤ 2 * (correctionBound h L n / X) +
        jetProduct (correctionBound h L) (correctionBound h L) n / X := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left (correctionJet_bound hh hX hν n) (by norm_num))
        (jetProduct_bound hX (correctionBound_nonneg h hL) (correctionBound_nonneg h hL)
          (fun i => correctionJet_bound hh hX hν i) (fun i => correctionJet_bound hh hX hν i) n)
    _ = _ := by unfold squareCorrectionBound; ring

/-- Edit jet, with branches according to `square`. -/
noncomputable def editJet (square : Bool) (h K : ℝ) (n : ℕ) (ν X : ℝ) : ℝ :=
  if square then squareCorrectionJet h K n ν X else correctionJet h K n ν X

/-- Edit bound, with branches according to `square`. -/
noncomputable def editBound (square : Bool) (h L : ℝ) (n : ℕ) : ℝ :=
  if square then squareCorrectionBound h L n else correctionBound h L n

theorem editJet_hasDerivAt {h : ℝ} (hh : 0 < h) (K X : ℝ) (square : Bool) (n : ℕ) (ν : ℝ) :
    HasDerivAt (fun u => editJet square h K n u X) (editJet square h K (n + 1) ν X) ν := by
  cases square
  · exact correctionJet_hasDerivAt hh K X n ν
  · exact squareCorrectionJet_hasDerivAt hh K X n ν

theorem editJet_continuousOn_X {h K : ℝ} (hh : 0 < h) (hK : 0 < K)
    (square : Bool) (n : ℕ) (ν : ℝ) : ContinuousOn (fun X => editJet square h K n ν X) (Ioi 0) := by
  cases square
  · exact correctionJet_continuousOn_X hh hK n ν
  · exact squareCorrectionJet_continuousOn_X hh hK n ν

theorem editBound_nonneg (square : Bool) (h : ℝ) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    0 ≤ editBound square h L n := by
  cases square
  · exact correctionBound_nonneg h hL n
  · exact squareCorrectionBound_nonneg h hL n

theorem editJet_bound {h K L ν X : ℝ} (hh : 0 < h) (hX : 1 ≤ X)
    (hν : |ν| ≤ L) (square : Bool) (n : ℕ) :
    |editJet square h K n ν X| ≤ editBound square h L n / X := by
  cases square
  · exact correctionJet_bound hh hX hν n
  · exact squareCorrectionJet_bound hh hX hν n

/-! ## Literal weighted improper integrals -/

/-- Weighted jet, given by `X ^ q * W X * editJet square h K n ν X`. -/
noncomputable def weightedJet (W : ℝ → ℝ) (square : Bool) (h K q : ℝ)
    (n : ℕ) (ν X : ℝ) : ℝ := X ^ q * W X * editJet square h K n ν X

/-- Weighted debt jet, given by `∫ X in Ioi K, weightedJet W square h K q n ν X`. -/
noncomputable def weightedDebtJet (W : ℝ → ℝ) (square : Bool) (h K q : ℝ)
    (n : ℕ) (ν : ℝ) : ℝ := ∫ X in Ioi K, weightedJet W square h K q n ν X

section Weighted

variable {W : ℝ → ℝ} {h K p q B : ℝ}
  (hh : 0 < h) (hK : 1 ≤ K) (hW : ContinuousOn W (Ioi K))
  (hB : 0 ≤ B) (hweight : ∀ X ∈ Ioi K, |W X| ≤ B * (X / K) ^ p)
  (hpq : p + q < 0)

include hh

theorem weightedJet_derivative (square : Bool) :
    ∀ᵐ X ∂volume.restrict (Ioi K), ∀ n ν,
      HasDerivAt (fun u => weightedJet W square h K q n u X)
        (weightedJet W square h K q (n + 1) ν X) ν := by
  exact Eventually.of_forall fun X n ν =>
    (editJet_hasDerivAt hh K X square n ν).const_mul (X ^ q * W X)

include hK hW

theorem weightedJet_continuousOn (square : Bool) (n : ℕ) (ν : ℝ) :
    ContinuousOn (weightedJet W square h K q n ν) (Ioi K) := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  exact ((continuousOn_id.rpow_const (fun X hX => Or.inl (hKp.trans hX).ne')).mul hW).mul
    ((editJet_continuousOn_X hh hKp square n ν).mono (Ioi_subset_Ioi hKp.le))

theorem weightedJet_measurable (square : Bool) (n : ℕ) (ν : ℝ) :
    AEStronglyMeasurable (weightedJet W square h K q n ν) (volume.restrict (Ioi K)) :=
  (weightedJet_continuousOn hh hK hW square n ν).aestronglyMeasurable measurableSet_Ioi

include hB hweight

omit hW in
theorem weightedJet_bound (square : Bool) (n : ℕ) {L ν X : ℝ}
    (hν : |ν| ≤ L) (hX : X ∈ Ioi K) :
    ‖weightedJet W square h K q n ν X‖ ≤
      (B * editBound square h L n) * weightedKernel K p q X := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one (hK.trans hX.le)
  rw [weightedJet, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hXp q)]
  calc
    _ ≤ X ^ q * (B * (X / K) ^ p) * (editBound square h L n / X) := by
      gcongr
      · exact hweight X hX
      · exact editJet_bound hh (hK.trans hX.le) hν square n
    _ = _ := by unfold weightedKernel; ring

include hpq

omit hW in
theorem weightedJet_dominated (square : Bool) :
    ChainDominated (weightedJet W square h K q) (volume.restrict (Ioi K)) := by
  intro n L hL
  refine ⟨fun X => (B * editBound square h L n) * weightedKernel K p q X,
    (weightedKernel_integrable (lt_of_lt_of_le zero_lt_one hK) hpq).const_mul _, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  intro ν hν
  exact weightedJet_bound hh hK hB hweight square n hν hX

omit hW in
theorem weightedDebtJet_bound (square : Bool) (n : ℕ) {L ν : ℝ}
    (hν : |ν| ≤ L) :
    |weightedDebtJet W square h K q n ν| ≤
      B * editBound square h L n * K ^ q / (-p - q) := by
  have hi := (weightedKernel_integrable (lt_of_lt_of_le zero_lt_one hK) hpq).const_mul
    (B * editBound square h L n)
  have hb' := norm_integral_le_of_norm_le hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    exact weightedJet_bound hh hK hB hweight square n hν hX)
  simpa only [weightedDebtJet, Real.norm_eq_abs, integral_const_mul,
    integral_weightedKernel (lt_of_lt_of_le zero_lt_one hK) hpq, mul_div_assoc] using hb'

theorem weightedJet_integrable (square : Bool) (n : ℕ) (ν : ℝ) :
    IntegrableOn (weightedJet W square h K q n ν) (Ioi K) :=
  chain_integrable (weightedJet_measurable hh hK hW square)
    (weightedJet_dominated hh hK hB hweight hpq square) n ν

theorem weightedDebtJet_hasDerivAt (square : Bool) (n : ℕ) (ν : ℝ) :
    HasDerivAt (weightedDebtJet W square h K q n)
      (weightedDebtJet W square h K q (n + 1) ν) ν :=
  integral_chain_hasDerivAt (weightedJet_derivative hh square)
    (weightedJet_measurable hh hK hW square)
    (weightedJet_dominated hh hK hB hweight hpq square) n ν

theorem weightedDebtJet_eq_iteratedDeriv (square : Bool) (n : ℕ) (ν : ℝ) :
    iteratedDeriv n (weightedDebtJet W square h K q 0) ν =
      weightedDebtJet W square h K q n ν :=
  iteratedDeriv_integral_chain (weightedJet_derivative hh square)
    (weightedJet_measurable hh hK hW square)
    (weightedJet_dominated hh hK hB hweight hpq square) n ν

theorem weightedDebt_contDiff (square : Bool) :
    ContDiff ℝ ∞ (weightedDebtJet W square h K q 0) :=
  contDiff_integral_chain (weightedJet_derivative hh square)
    (weightedJet_measurable hh hK hW square)
    (weightedJet_dominated hh hK hB hweight hpq square)

end Weighted

/-! ## Specialization to the actual outgoing profile -/

/-- Nu debt jet, given by `weightedDebtJet (tailWeight d K square) square d.h K q n ν`. -/
noncomputable def nuDebtJet (d : TailData) (K : ℝ) (square : Bool) (q : ℝ)
    (n : ℕ) (ν : ℝ) : ℝ := weightedDebtJet (tailWeight d K square) square d.h K q n ν

/-- Nu constant, given by `tailSize d square * editBound square d.h L n / (-tailDecay d square -
q)`. -/
noncomputable def nuConstant (d : TailData) (L : ℝ) (square : Bool) (q : ℝ) (n : ℕ) : ℝ :=
  tailSize d square * editBound square d.h L n / (-tailDecay d square - q)

theorem nuConstant_nonneg (d : TailData) {L : ℝ} (hL : 0 ≤ L) (square : Bool) {q : ℝ}
    (hq : tailDecay d square + q < 0) (n : ℕ) : 0 ≤ nuConstant d L square q n := by
  exact div_nonneg (mul_nonneg (tailSize_nonneg d square)
    (editBound_nonneg square d.h hL n)) (by linarith)

theorem nuDebtJet_hasDerivAt (d : TailData) {K : ℝ} (hK : 1 ≤ K) (square : Bool)
    {q : ℝ} (hq : tailDecay d square + q < 0) (n : ℕ) (ν : ℝ) :
    HasDerivAt (nuDebtJet d K square q n) (nuDebtJet d K square q (n + 1) ν) ν :=
  weightedDebtJet_hasDerivAt d.h_pos hK
    (tailWeight_continuousOn d (lt_of_lt_of_le zero_lt_one hK) square)
    (tailSize_nonneg d square) (tailWeight_bound d (lt_of_lt_of_le zero_lt_one hK) square)
    hq square n ν

theorem nuDebt_contDiff (d : TailData) {K : ℝ} (hK : 1 ≤ K) (square : Bool)
    {q : ℝ} (hq : tailDecay d square + q < 0) : ContDiff ℝ ∞ (nuDebtJet d K square q 0) :=
  weightedDebt_contDiff d.h_pos hK
    (tailWeight_continuousOn d (lt_of_lt_of_le zero_lt_one hK) square)
    (tailSize_nonneg d square) (tailWeight_bound d (lt_of_lt_of_le zero_lt_one hK) square)
    hq square

theorem nuDebtJet_eq_iteratedDeriv (d : TailData) {K : ℝ} (hK : 1 ≤ K) (square : Bool)
    {q : ℝ} (hq : tailDecay d square + q < 0) (n : ℕ) (ν : ℝ) :
    iteratedDeriv n (nuDebtJet d K square q 0) ν = nuDebtJet d K square q n ν :=
  weightedDebtJet_eq_iteratedDeriv d.h_pos hK
    (tailWeight_continuousOn d (lt_of_lt_of_le zero_lt_one hK) square)
    (tailSize_nonneg d square) (tailWeight_bound d (lt_of_lt_of_le zero_lt_one hK) square)
    hq square n ν

theorem nuDebtJet_bound (d : TailData) {K : ℝ} (hK : 1 ≤ K) (square : Bool)
    {q : ℝ} (hq : tailDecay d square + q < 0) (n : ℕ) {L ν : ℝ} (hν : |ν| ≤ L) :
    |nuDebtJet d K square q n ν| ≤ nuConstant d L square q n * K ^ q := by
  have hb' := weightedDebtJet_bound d.h_pos hK
    (tailSize_nonneg d square) (tailWeight_bound d (lt_of_lt_of_le zero_lt_one hK) square)
    hq square n hν
  convert! hb' using 1
  unfold nuConstant
  ring

/-- The literal extended outgoing edit. -/
noncomputable def physicalEdit (d : TailData) (K η X : ℝ) : ℝ :=
  edit (outgoingProfile d K η) d.h (diffusion η) K X

/-- Physical pressure, given by `∫ X in Ioi K, squareChange (outgoingProfile d K η) d.h
(diffusion η) K X / X`. -/
noncomputable def physicalPressure (d : TailData) (K η : ℝ) : ℝ :=
  ∫ X in Ioi K, squareChange (outgoingProfile d K η) d.h (diffusion η) K X / X

/-- Physical energy, given by `∫ X in Ioi K, squareChange (outgoingProfile d K η) d.h (diffusion
η) K X`. -/
noncomputable def physicalEnergy (d : TailData) (K η : ℝ) : ℝ :=
  ∫ X in Ioi K, squareChange (outgoingProfile d K η) d.h (diffusion η) K X

/-- Physical angular, given by `∫ X in Ioi K, Real.sqrt (2 * X) * change (outgoingProfile d K η)
d.h (diffusion η) K X`. -/
noncomputable def physicalAngular (d : TailData) (K η : ℝ) : ℝ :=
  ∫ X in Ioi K, Real.sqrt (2 * X) * change (outgoingProfile d K η) d.h (diffusion η) K X

theorem physicalPressure_eq (d : TailData) {K : ℝ} (hK : 0 < K) (η : ℝ) :
    physicalPressure d K η = nuDebtJet d K true (-1) 0 (diffusion η) := by
  unfold physicalPressure nuDebtJet weightedDebtJet
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  simp only [weightedJet, tailWeight, editJet, ite_true]
  rw [squareCorrectionJet_zero]
  unfold squareChange edit
  rw [outgoingProfile_eq_powerTail d hK hX.le η, Real.rpow_neg_one]
  ring

theorem physicalEnergy_eq (d : TailData) {K : ℝ} (hK : 0 < K) (η : ℝ) :
    physicalEnergy d K η = nuDebtJet d K true 0 0 (diffusion η) := by
  unfold physicalEnergy nuDebtJet weightedDebtJet
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  simp only [weightedJet, tailWeight, editJet, ite_true]
  rw [squareCorrectionJet_zero, Real.rpow_zero]
  unfold squareChange edit
  rw [outgoingProfile_eq_powerTail d hK hX.le η]
  ring

theorem physicalAngular_eq (d : TailData) {K : ℝ} (hK : 0 < K) (η : ℝ) :
    physicalAngular d K η = Real.sqrt 2 * nuDebtJet d K false (1 / 2) 0 (diffusion η) := by
  unfold physicalAngular nuDebtJet weightedDebtJet
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  simp only [weightedJet, tailWeight, editJet, Bool.false_eq_true, ite_false, correctionJet_zero]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [Real.sqrt_eq_rpow]
  unfold change edit multiplier
  rw [outgoingProfile_eq_powerTail d hK hX.le η]
  ring

theorem multiplier_eq_original (h : ℝ) {ν K X : ℝ} (hν : 0 ≤ ν) (hX : 0 < X) :
    multiplier h ν K X = HeatTailEdit.multiplier h ν K X := by
  unfold multiplier correction
  rw [HeatProfileExtension.scaledProfile_eq_profile (1 + h) hX hν]
  rfl

theorem edit_eq_original (E : ℝ → ℝ) (h : ℝ) {ν K X : ℝ} (hν : 0 ≤ ν) (hX : 0 < X) :
    edit E h ν K X = HeatTailEdit.edit E h ν K X := by
  rw [edit, multiplier_eq_original h hν hX]
  rfl

theorem physicalPressure_eq_original (d : TailData) {K η : ℝ} (hK : 0 < K)
    (hη : η ∈ Icc (-1 : ℝ) 1) :
    physicalPressure d K η = ParametricHeatTail.physicalPressure d K η := by
  unfold physicalPressure ParametricHeatTail.physicalPressure pressureDebt
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  unfold squareChange HeatTailEdit.squareChange
  dsimp only
  rw [edit_eq_original _ _ (ParametricHeatTail.diffusion_mem hη).1 (hK.trans hX)]

theorem physicalEnergy_eq_original (d : TailData) {K η : ℝ} (hK : 0 < K)
    (hη : η ∈ Icc (-1 : ℝ) 1) :
    physicalEnergy d K η = ParametricHeatTail.physicalEnergy d K η := by
  unfold physicalEnergy ParametricHeatTail.physicalEnergy energyDebt
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  unfold squareChange HeatTailEdit.squareChange
  rw [edit_eq_original _ _ (ParametricHeatTail.diffusion_mem hη).1 (hK.trans hX)]

theorem physicalAngular_eq_original (d : TailData) {K η : ℝ} (hK : 0 < K)
    (hη : η ∈ Icc (-1 : ℝ) 1) :
    physicalAngular d K η = ParametricHeatTail.physicalAngular d K η := by
  unfold physicalAngular ParametricHeatTail.physicalAngular angularDebt
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  unfold change HeatTailEdit.change
  dsimp only
  rw [edit_eq_original _ _ (ParametricHeatTail.diffusion_mem hη).1 (hK.trans hX)]

/-! ## Exact radius rescaling and joint smoothness -/

theorem correction_scale (h ν : ℝ) {K : ℝ} (hK : K ≠ 0) (X : ℝ) :
    correction h K ν (K * X) = correction h 1 (ν / K) X := by
  unfold correction switch HeatProfileExtension.scaledProfile
  simp only [mul_div_cancel_left₀ X hK, div_one]
  congr 2
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring_nf

theorem tailWeight_scale (d : TailData) {K : ℝ} (hK : K ≠ 0) (square : Bool) (X : ℝ) :
    tailWeight d K square (K * X) = tailWeight d 1 square X := by
  cases square <;> simp only [tailWeight, Bool.false_eq_true, ite_false, ite_true,
    powerTail, mul_div_cancel_left₀ X hK, div_one]

theorem editJet_scale_zero (h ν : ℝ) {K : ℝ} (hK : K ≠ 0) (square : Bool) (X : ℝ) :
    editJet square h K 0 ν (K * X) = editJet square h 1 0 (ν / K) X := by
  cases square
  · exact correction_scale h ν hK X
  · simp only [editJet, ite_true, squareCorrectionJet_zero, multiplier, correction_scale h ν hK X]

theorem weightedJet_scale_zero (d : TailData) {K : ℝ} (hK : 0 < K)
    (square : Bool) (q ν : ℝ) {X : ℝ} (hX : 0 ≤ X) :
    weightedJet (tailWeight d K square) square d.h K q 0 ν (K * X) =
      K ^ q * weightedJet (tailWeight d 1 square) square d.h 1 q 0 (ν / K) X := by
  unfold weightedJet
  rw [Real.mul_rpow hK.le hX, tailWeight_scale d hK.ne', editJet_scale_zero d.h ν hK.ne']
  ring

/-- A genuine change of variables in the improper integral gives all radius
dependence through an explicit power and the rescaled diffusion. -/
theorem nuDebt_scale (d : TailData) {K : ℝ} (hK : 0 < K)
    (square : Bool) (q ν : ℝ) :
    nuDebtJet d K square q 0 ν = K ^ (q + 1) * nuDebtJet d 1 square q 0 (ν / K) := by
  let g : ℝ → ℝ := weightedJet (tailWeight d K square) square d.h K q 0 ν
  have hcv := integral_comp_mul_left_Ioi g 1 hK
  simp only [mul_one, smul_eq_mul] at hcv
  have hcv' : nuDebtJet d K square q 0 ν = K * ∫ X in Ioi 1, g (K * X) := by
    rw [hcv, ← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
    rfl
  rw [hcv']
  have heq : (∫ X in Ioi (1 : ℝ), g (K * X)) =
      K ^ q * nuDebtJet d 1 square q 0 (ν / K) := by
    unfold nuDebtJet weightedDebtJet
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro X hX
    exact weightedJet_scale_zero d hK square q ν (zero_le_one.trans hX.le)
  rw [heq, Real.rpow_add_one hK.ne']
  ring

theorem nuDebt_joint_contDiffOn (d : TailData) (square : Bool) {q : ℝ}
    (hq : tailDecay d square + q < 0) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => nuDebtJet d p.1 square q 0 p.2)
      (Ioi 0 ×ˢ (univ : Set ℝ)) := by
  have hp : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.1 ^ (q + 1))
      (Ioi 0 ×ˢ (univ : Set ℝ)) :=
    contDiffOn_fst.rpow_const_of_ne (fun p hp => (show 0 < p.1 from hp.1).ne')
  have hr : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2 / p.1)
      (Ioi 0 ×ˢ (univ : Set ℝ)) :=
    contDiffOn_snd.div contDiffOn_fst (fun p hp => (show 0 < p.1 from hp.1).ne')
  have hout := hp.mul ((nuDebt_contDiff d (K := 1) le_rfl square hq).comp_contDiffOn hr)
  exact hout.congr (fun p hp => nuDebt_scale d hp.1 square q p.2)

/-- Eta debt, given by `nuDebtJet d K square q 0 (diffusion η)`. -/
noncomputable def etaDebt (d : TailData) (K : ℝ) (square : Bool) (q η : ℝ) : ℝ :=
  nuDebtJet d K square q 0 (diffusion η)

theorem etaDebt_contDiff (d : TailData) {K : ℝ} (hK : 1 ≤ K) (square : Bool)
    {q : ℝ} (hq : tailDecay d square + q < 0) : ContDiff ℝ ∞ (etaDebt d K square q) :=
  (nuDebt_contDiff d hK square hq).comp diffusion_contDiff

theorem etaDebt_hasDerivAt (d : TailData) {K : ℝ} (hK : 1 ≤ K) (square : Bool)
    {q : ℝ} (hq : tailDecay d square + q < 0) (η : ℝ) :
    HasDerivAt (etaDebt d K square q)
      (nuDebtJet d K square q 1 (diffusion η) * (-2 * η)) η :=
  (nuDebtJet_hasDerivAt d hK square hq 0 (diffusion η)).comp η (diffusion_hasDerivAt η)

theorem etaDebt_joint_contDiffOn (d : TailData) (square : Bool) {q : ℝ}
    (hq : tailDecay d square + q < 0) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => etaDebt d p.1 square q p.2)
      (Ioi 0 ×ˢ (univ : Set ℝ)) := by
  exact (nuDebt_joint_contDiffOn d square hq).comp
    (contDiffOn_fst.prodMk (diffusion_contDiff.comp_contDiffOn contDiffOn_snd))
    (fun p hp => ⟨hp.1, mem_univ _⟩)

theorem physicalPressure_joint_contDiffOn (d : TailData) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => physicalPressure d p.1 p.2)
      (Ioi 0 ×ˢ (univ : Set ℝ)) :=
  (etaDebt_joint_contDiffOn d true (ParametricHeatTail.pressure_decay d)).congr
    (fun p hp => physicalPressure_eq d hp.1 p.2)

theorem physicalEnergy_joint_contDiffOn (d : TailData) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => physicalEnergy d p.1 p.2)
      (Ioi 0 ×ˢ (univ : Set ℝ)) :=
  (etaDebt_joint_contDiffOn d true (ParametricHeatTail.energy_decay d)).congr
    (fun p hp => physicalEnergy_eq d hp.1 p.2)

theorem physicalAngular_joint_contDiffOn (d : TailData) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => physicalAngular d p.1 p.2)
      (Ioi 0 ×ˢ (univ : Set ℝ)) :=
  (contDiffOn_const.mul (etaDebt_joint_contDiffOn d false (ParametricHeatTail.angular_decay
      d))).congr
    (fun p hp => physicalAngular_eq d hp.1 p.2)

/-! ## Uniform estimates on a fixed enlarged physical band -/

/-- Enlarged band, given by `Icc (-(3 / 2 : ℝ)) (3 / 2)`. -/
noncomputable def enlargedBand : Set ℝ := Icc (-(3 / 2 : ℝ)) (3 / 2)

theorem physicalBand_subset_enlargedBand : Icc (-1 : ℝ) 1 ⊆ enlargedBand := by
  intro η hη
  change -(3 / 2 : ℝ) ≤ η ∧ η ≤ 3 / 2
  constructor <;> linarith [hη.1, hη.2]

theorem enlargedBand_diffusion_bound {η : ℝ} (hη : η ∈ enlargedBand) : |diffusion η| ≤ 3 := by
  have hη' : -(3 / 2 : ℝ) ≤ η ∧ η ≤ 3 / 2 := hη
  have hp : 0 ≤ (3 / 2 - η) * (3 / 2 + η) :=
    mul_nonneg (by linarith) (by linarith)
  rw [abs_le]
  dsimp [diffusion]
  constructor <;> linarith [sq_nonneg η]

theorem enlargedBand_diffusion_derivative_bound {η : ℝ} (hη : η ∈ enlargedBand)
    (n : ℕ) (hn : 1 ≤ n) : ‖iteratedFDeriv ℝ n diffusion η‖ ≤ (3 : ℝ) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hη' : -(3 / 2 : ℝ) ≤ η ∧ η ≤ 3 / 2 := hη
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · rw [iteratedDeriv_one, ParametricHeatTail.diffusion_deriv, Real.norm_eq_abs]
    norm_num only [Nat.zero_add, pow_one]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rcases n with _ | n
  · rw [ParametricHeatTail.diffusion_second]
    norm_num
  · rw [show n + 1 + 1 + 1 = n + 3 by omega, ParametricHeatTail.diffusion_higher]
    simp only [norm_zero]
    positivity

/-- Eta constant, given by `(n.factorial : ℝ) * (∑ i ∈ Finset.range (n + 1), nuConstant d 3
square q i) * 3 ^ n`. -/
noncomputable def etaConstant (d : TailData) (square : Bool) (q : ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * (∑ i ∈ Finset.range (n + 1), nuConstant d 3 square q i) * 3 ^ n

theorem etaConstant_nonneg (d : TailData) (square : Bool) {q : ℝ}
    (hq : tailDecay d square + q < 0) (n : ℕ) : 0 ≤ etaConstant d square q n := by
  unfold etaConstant
  exact mul_nonneg (mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => nuConstant_nonneg d (by norm_num) square hq i)) (by positivity)

theorem etaDebt_jet_bound (d : TailData) {K : ℝ} (hK : 1 ≤ K) (square : Bool)
    {q : ℝ} (hq : tailDecay d square + q < 0) (n : ℕ) {η : ℝ} (hη : η ∈ enlargedBand) :
    |iteratedDeriv n (etaDebt d K square q) η| ≤ etaConstant d square q n * K ^ q := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hb' := norm_iteratedFDeriv_comp_le (nuDebt_contDiff d hK square hq) diffusion_contDiff
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) η
    (C := (∑ i ∈ Finset.range (n + 1), nuConstant d 3 square q i) * K ^ q)
    (D := 3) (n := n) ?_ ?_
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hb'
    change |iteratedDeriv n (etaDebt d K square q) η| ≤ _ at hb'
    convert! hb' using 1
    unfold etaConstant
    ring
  · intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      nuDebtJet_eq_iteratedDeriv d hK square hq i (diffusion η)]
    apply (nuDebtJet_bound d hK square hq i (enlargedBand_diffusion_bound hη)).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hKp.le q)
    exact Finset.single_le_sum (fun j _ => nuConstant_nonneg d (by norm_num) square hq j)
      (Finset.mem_range.mpr (by omega))
  · intro i hi _
    exact enlargedBand_diffusion_derivative_bound hη i hi

theorem physicalPressure_contDiff (d : TailData) {K : ℝ} (hK : 1 ≤ K) :
    ContDiff ℝ ∞ (physicalPressure d K) := by
  rw [show physicalPressure d K = etaDebt d K true (-1) from
    funext (physicalPressure_eq d (lt_of_lt_of_le zero_lt_one hK))]
  exact etaDebt_contDiff d hK true (ParametricHeatTail.pressure_decay d)

theorem physicalEnergy_contDiff (d : TailData) {K : ℝ} (hK : 1 ≤ K) :
    ContDiff ℝ ∞ (physicalEnergy d K) := by
  rw [show physicalEnergy d K = etaDebt d K true 0 from
    funext (physicalEnergy_eq d (lt_of_lt_of_le zero_lt_one hK))]
  exact etaDebt_contDiff d hK true (ParametricHeatTail.energy_decay d)

theorem physicalAngular_contDiff (d : TailData) {K : ℝ} (hK : 1 ≤ K) :
    ContDiff ℝ ∞ (physicalAngular d K) := by
  rw [show physicalAngular d K = (fun η => Real.sqrt 2 * etaDebt d K false (1 / 2) η) from
    funext (physicalAngular_eq d (lt_of_lt_of_le zero_lt_one hK))]
  exact contDiff_const.mul (etaDebt_contDiff d hK false (ParametricHeatTail.angular_decay d))

theorem physicalPressure_jet_bound (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    (n : ℕ) {η : ℝ} (hη : η ∈ enlargedBand) :
    |iteratedDeriv n (physicalPressure d K) η| ≤ etaConstant d true (-1) n / K := by
  rw [show physicalPressure d K = etaDebt d K true (-1) from
    funext (physicalPressure_eq d (lt_of_lt_of_le zero_lt_one hK))]
  simpa only [Real.rpow_neg_one, div_eq_mul_inv] using
    etaDebt_jet_bound d hK true (ParametricHeatTail.pressure_decay d) n hη

theorem physicalEnergy_jet_bound (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    (n : ℕ) {η : ℝ} (hη : η ∈ enlargedBand) :
    |iteratedDeriv n (physicalEnergy d K) η| ≤ etaConstant d true 0 n := by
  rw [show physicalEnergy d K = etaDebt d K true 0 from
    funext (physicalEnergy_eq d (lt_of_lt_of_le zero_lt_one hK))]
  simpa only [Real.rpow_zero, mul_one] using
    etaDebt_jet_bound d hK true (ParametricHeatTail.energy_decay d) n hη

theorem physicalAngular_jet_bound (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    (n : ℕ) {η : ℝ} (hη : η ∈ enlargedBand) :
    |iteratedDeriv n (physicalAngular d K) η| ≤
      (Real.sqrt 2 * etaConstant d false (1 / 2) n) * Real.sqrt K := by
  rw [show physicalAngular d K = (fun η => Real.sqrt 2 * etaDebt d K false (1 / 2) η) from
    funext (physicalAngular_eq d (lt_of_lt_of_le zero_lt_one hK))]
  rw [iteratedDeriv_const_mul _ ((etaDebt_contDiff d hK false (ParametricHeatTail.angular_decay
      d)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt,
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hb' := mul_le_mul_of_nonneg_left
    (etaDebt_jet_bound d hK false (ParametricHeatTail.angular_decay d) n hη) (Real.sqrt_nonneg 2)
  simpa only [← Real.sqrt_eq_rpow K, mul_assoc] using hb'

theorem exists_physical_debt_jet_bounds (d : TailData) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∀ η ∈ enlargedBand,
      |iteratedDeriv n (physicalPressure d K) η| ≤ C / K ∧
      |iteratedDeriv n (physicalEnergy d K) η| ≤ C ∧
      |iteratedDeriv n (physicalAngular d K) η| ≤ C * Real.sqrt K := by
  let CP := etaConstant d true (-1) n
  let CS := etaConstant d true 0 n
  let CI := Real.sqrt 2 * etaConstant d false (1 / 2) n
  have hp : 0 ≤ CP := etaConstant_nonneg d true (ParametricHeatTail.pressure_decay d) n
  have hs : 0 ≤ CS := etaConstant_nonneg d true (ParametricHeatTail.energy_decay d) n
  have hi : 0 ≤ CI := mul_nonneg (Real.sqrt_nonneg 2)
    (etaConstant_nonneg d false (ParametricHeatTail.angular_decay d) n)
  refine ⟨1 + CP + CS + CI, by linarith, ?_⟩
  intro K hK η hη
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨(physicalPressure_jet_bound d hK n hη).trans ?_,
    (physicalEnergy_jet_bound d hK n hη).trans ?_,
    (physicalAngular_jet_bound d hK n hη).trans ?_⟩
  · exact div_le_div_of_nonneg_right (show CP ≤ 1 + CP + CS + CI by linarith) hKp.le
  · change CS ≤ 1 + CP + CS + CI
    linarith
  · exact mul_le_mul_of_nonneg_right (show CI ≤ 1 + CP + CS + CI by linarith)
      (Real.sqrt_nonneg K)

theorem exists_physical_debt_C1_bounds (d : TailData) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∀ η ∈ enlargedBand,
      |physicalPressure d K η| ≤ C / K ∧ |deriv (physicalPressure d K) η| ≤ C / K ∧
      |physicalEnergy d K η| ≤ C ∧ |deriv (physicalEnergy d K) η| ≤ C ∧
      |physicalAngular d K η| ≤ C * Real.sqrt K ∧
      |deriv (physicalAngular d K) η| ≤ C * Real.sqrt K := by
  obtain ⟨C0, hC0, hb0⟩ := exists_physical_debt_jet_bounds d 0
  obtain ⟨C1, hC1, hb1⟩ := exists_physical_debt_jet_bounds d 1
  refine ⟨C0 + C1, by linarith, ?_⟩
  intro K hK η hη
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  rcases hb0 K hK η hη with ⟨hp0, hs0, hi0⟩
  rcases hb1 K hK η hη with ⟨hp1, hs1, hi1⟩
  simp only [iteratedDeriv_zero, iteratedDeriv_one] at hp0 hs0 hi0 hp1 hs1 hi1
  refine ⟨hp0.trans ?_, hp1.trans ?_, hs0.trans ?_, hs1.trans ?_, hi0.trans ?_, hi1.trans ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) hKp.le
  · exact div_le_div_of_nonneg_right (by linarith) hKp.le
  · linarith
  · linarith
  · exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg K)
  · exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg K)

/-- Physical debt, given by `![physicalPressure d K η, physicalEnergy d K η, physicalAngular d K
η]`. -/
noncomputable def physicalDebt (d : TailData) (K η : ℝ) : TerminalCompensation.Coeff :=
  ![physicalPressure d K η, physicalEnergy d K η, physicalAngular d K η]

/-- Normalized debt, given by `TerminalCompensation.scaledDebt K (physicalDebt d K η)`. -/
noncomputable def normalizedDebt (d : TailData) (K η : ℝ) : TerminalCompensation.Coeff :=
  TerminalCompensation.scaledDebt K (physicalDebt d K η)

theorem normalizedDebt_contDiff (d : TailData) {K : ℝ} (hK : 1 ≤ K) :
    ContDiff ℝ ∞ (normalizedDebt d K) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact physicalPressure_contDiff d hK
  · exact (physicalEnergy_contDiff d hK).div_const K
  · exact (physicalAngular_contDiff d hK).div_const (K * Real.sqrt (2 * K))

theorem normalizedDebt_deriv (d : TailData) {K : ℝ} (hK : 1 ≤ K) (η : ℝ) :
    deriv (normalizedDebt d K) η = TerminalCompensation.scaledDebt K
      ![deriv (physicalPressure d K) η, deriv (physicalEnergy d K) η,
        deriv (physicalAngular d K) η] := by
  apply HasDerivAt.deriv
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j
  · exact ((physicalPressure_contDiff d hK).differentiable (by simp) η).hasDerivAt
  · exact (((physicalEnergy_contDiff d hK).differentiable (by simp) η).hasDerivAt).div_const K
  · exact (((physicalAngular_contDiff d hK).differentiable (by simp) η).hasDerivAt).div_const
      (K * Real.sqrt (2 * K))

/-- The exact normalized vector has the same uniform `C1` inverse-radius
cost on the enlarged compact band, using ordinary derivatives everywhere. -/
theorem exists_normalized_C1_bounds (d : TailData) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∀ η ∈ enlargedBand,
      ‖normalizedDebt d K η‖ ≤ C / K ∧ ‖deriv (normalizedDebt d K) η‖ ≤ C / K := by
  obtain ⟨C, hC, hb⟩ := exists_physical_debt_C1_bounds d
  refine ⟨C, hC, fun K hK η hη => ?_⟩
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  rcases hb K hK η hη with ⟨hp0, hp1, he0, he1, hi0, hi1⟩
  refine ⟨ParametricTerminalCompensation.scaled_triple_norm_bound hKp hC.le hp0 he0 hi0, ?_⟩
  rw [normalizedDebt_deriv d hK]
  exact ParametricTerminalCompensation.scaled_triple_norm_bound hKp hC.le hp1 he1 hi1

/-- The extended physical edit remains strictly positive throughout the
enlarged band once the switch radius is sufficiently large. -/
theorem eventually_physicalEdit_pos (d : TailData) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ η ∈ enlargedBand,
      ∀ X : ℝ, 0 < X → 0 < physicalEdit d K η X := by
  let C := correctionBound d.h 3 0
  have hC : 0 ≤ C := correctionBound_nonneg d.h (by norm_num) 0
  refine ⟨1 + 2 * C, by linarith, fun K hK η hη X hX => ?_⟩
  have hKone : 1 ≤ K := by linarith
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hKone
  apply mul_pos (outgoingProfile_pos d K η X)
  change 0 < 1 + correction d.h K (diffusion η) X
  by_cases hXK : X ≤ K
  · rw [correction, switch_zero hKp hX hXK, zero_mul, add_zero]
    norm_num
  · have hKX : K < X := lt_of_not_ge hXK
    have hb := correctionJet_bound (K := K) d.h_pos (hKone.trans hKX.le)
      (enlargedBand_diffusion_bound hη) 0
    rw [correctionJet_zero] at hb
    have hhalf : C / X < 1 / 2 := (div_lt_iff₀ hX).mpr (by dsimp [C] at *; linarith)
    have hsmall : |correction d.h K (diffusion η) X| < 1 / 2 := hb.trans_lt hhalf
    have hl := (abs_lt.mp hsmall).1
    linarith

/-! ## Every actual physical-parameter derivative passes under the integral -/

theorem partial_iteratedDeriv_contDiffOn {F : ℝ × ℝ → ℝ} {K : ℝ}
    (hF : ContDiffOn ℝ ∞ F ((univ : Set ℝ) ×ˢ Ioi K)) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv n (fun η => F (η, p.2)) p.1)
      ((univ : Set ℝ) ×ˢ Ioi K) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
      intro p hp
      have hc := ih.contDiffAt ((isOpen_univ.prod isOpen_Ioi).mem_nhds hp)
      have hf : ContDiffAt ℝ ∞
          (Function.uncurry (fun q : ℝ × ℝ => fun η : ℝ =>
            iteratedDeriv n (fun u => F (u, q.2)) η)) (p, p.1) :=
        hc.comp (p, p.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
      have hd : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ =>
          fderiv ℝ (fun η => iteratedDeriv n (fun u => F (u, q.2)) η) q.1) p :=
        hf.fderiv (g := fun q : ℝ × ℝ => q.1) contDiffAt_fst (by simp)
      have hda : ContDiffAt ℝ ∞
          (fun q : ℝ × ℝ => deriv (fun η => iteratedDeriv n (fun u => F (u, q.2)) η) q.1) p :=
        hd.clm_apply contDiffAt_const
      simpa only [iteratedDeriv_succ] using hda.contDiffWithinAt

theorem editJet_zero_contDiff {h : ℝ} (hh : 0 < h) (K X : ℝ) (square : Bool) :
    ContDiff ℝ ∞ (fun ν => editJet square h K 0 ν X) := by
  cases square
  · exact correction_contDiff hh K X
  · exact (contDiff_const.mul (correction_contDiff hh K X)).add
      ((correction_contDiff hh K X).mul (correction_contDiff hh K X))

theorem iteratedDeriv_weightedJet {h : ℝ} (hh : 0 < h) (W : ℝ → ℝ)
    (K q X : ℝ) (square : Bool) (n : ℕ) (ν : ℝ) :
    iteratedDeriv n (fun u => weightedJet W square h K q 0 u X) ν =
      weightedJet W square h K q n ν X := by
  induction n generalizing ν with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, funext ih]
      exact ((editJet_hasDerivAt hh K X square n ν).const_mul (X ^ q * W X)).deriv

theorem weightedJet_zero_contDiff {h : ℝ} (hh : 0 < h) (W : ℝ → ℝ)
    (K q X : ℝ) (square : Bool) :
    ContDiff ℝ ∞ (fun ν => weightedJet W square h K q 0 ν X) :=
  contDiff_const.mul (editJet_zero_contDiff hh K X square)

theorem actualIntegrand_joint_contDiffOn (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    (square : Bool) (q : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      weightedJet (tailWeight d K square) square d.h K q 0 (diffusion p.1) p.2)
      ((univ : Set ℝ) ×ˢ Ioi K) := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hW : ContDiffOn ℝ ∞ (tailWeight d K square) (Ioi 0) := by
    have hw := powerTail_contDiffOn hKp d.h (outgoingAmplitude d) (outgoingShape_contDiff d)
    cases square
    · exact hw
    · exact hw.pow 2
  have hs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => switch K p.2)
      ((univ : Set ℝ) ×ˢ Ioi K) :=
    (switch_contDiffOn hKp).comp contDiffOn_snd (fun p hp => hKp.trans hp.2)
  have hh : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      HeatProfileExtension.scaledProfile (1 + d.h) p.2 p.1)
      ((univ : Set ℝ) ×ˢ Ioi K) :=
    (HeatProfileExtension.scaledProfile_contDiffOn (a := 1 + d.h) (by linarith [d.h_pos])).comp
      (contDiffOn_snd.prodMk contDiffOn_fst) (fun p hp => ⟨hKp.trans hp.2, mem_univ _⟩)
  have hc : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => correction d.h K p.1 p.2)
      ((univ : Set ℝ) ×ˢ Ioi K) := hs.mul (hh.sub contDiffOn_const)
  have he : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => editJet square d.h K 0 p.1 p.2)
      ((univ : Set ℝ) ×ˢ Ioi K) := by
    cases square
    · exact hc
    · exact (contDiffOn_const.mul hc).add (hc.mul hc)
  have hn : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      weightedJet (tailWeight d K square) square d.h K q 0 p.1 p.2)
      ((univ : Set ℝ) ×ˢ Ioi K) :=
    ((contDiffOn_snd.rpow_const_of_ne (fun p hp => (hKp.trans hp.2).ne')).mul
      (hW.comp contDiffOn_snd (fun p hp => hKp.trans hp.2))).mul he
  exact hn.comp ((diffusion_contDiff.comp_contDiffOn contDiffOn_fst).prodMk contDiffOn_snd)
    (fun p hp => ⟨mem_univ _, hp.2⟩)

/-- Eta integrand jet, given by `iteratedDeriv n (fun θ => weightedJet (tailWeight d K square)
square d.h K q 0 (diffusion θ) X) η`. -/
noncomputable def etaIntegrandJet (d : TailData) (K : ℝ) (square : Bool) (q : ℝ)
    (n : ℕ) (η X : ℝ) : ℝ :=
  iteratedDeriv n (fun θ => weightedJet (tailWeight d K square) square d.h K q 0 (diffusion θ) X) η

theorem etaIntegrandJet_measurable (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    (square : Bool) (q : ℝ) (n : ℕ) (η : ℝ) :
    AEStronglyMeasurable (etaIntegrandJet d K square q n η) (volume.restrict (Ioi K)) := by
  have hc := (partial_iteratedDeriv_contDiffOn (actualIntegrand_joint_contDiffOn d hK square q)
      n).continuousOn
  have hi : ContinuousOn (fun X : ℝ => (η, X)) (Ioi K) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hcx := hc.comp hi (fun X (hX : X ∈ Ioi K) =>
    (show (η, X) ∈ (univ : Set ℝ) ×ˢ Ioi K from ⟨mem_univ _, hX⟩))
  unfold etaIntegrandJet
  simpa only [Function.comp_def] using hcx.aestronglyMeasurable measurableSet_Ioi

theorem diffusion_abs_bound {L η : ℝ} (hη : |η| ≤ L) : |diffusion η| ≤ 1 + L ^ 2 := by
  have hp : 0 ≤ (L - η) * (L + η) :=
    mul_nonneg (by linarith [(abs_le.mp hη).2]) (by linarith [(abs_le.mp hη).1])
  rw [abs_le]
  dsimp [diffusion]
  constructor <;> linarith [sq_nonneg η, sq_nonneg L]

theorem diffusion_iterated_bound {L η : ℝ} (hL : 0 ≤ L) (hη : |η| ≤ L)
    (n : ℕ) (hn : 1 ≤ n) : ‖iteratedFDeriv ℝ n diffusion η‖ ≤ (2 * (L + 1)) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · rw [iteratedDeriv_one, ParametricHeatTail.diffusion_deriv, Real.norm_eq_abs]
    norm_num only [Nat.zero_add, pow_one]
    exact abs_le.mpr ⟨by linarith [(abs_le.mp hη).2], by linarith [(abs_le.mp hη).1]⟩
  rcases n with _ | n
  · rw [ParametricHeatTail.diffusion_second]
    norm_num
    nlinarith
  · rw [show n + 1 + 1 + 1 = n + 3 by omega, ParametricHeatTail.diffusion_higher]
    simp only [norm_zero]
    positivity

theorem etaIntegrandJet_dominated (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    (square : Bool) {q : ℝ} (hq : tailDecay d square + q < 0) :
    ChainDominated (etaIntegrandJet d K square q) (volume.restrict (Ioi K)) := by
  intro n L hL
  let S := ∑ i ∈ Finset.range (n + 1), editBound square d.h (1 + L ^ 2) i
  let C := (n.factorial : ℝ) * (tailSize d square * S) * (2 * (L + 1)) ^ n
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨fun X => C * weightedKernel K (tailDecay d square) q X,
    (weightedKernel_integrable hKp hq).const_mul C, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  intro η hη
  have hXp : 0 < X := hKp.trans hX
  have hw : 0 ≤ weightedKernel K (tailDecay d square) q X := by
    unfold weightedKernel
    positivity
  have hc := norm_iteratedFDeriv_comp_le
    (weightedJet_zero_contDiff d.h_pos (tailWeight d K square) K q X square)
    diffusion_contDiff (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) η
    (C := (tailSize d square * S) * weightedKernel K (tailDecay d square) q X)
    (D := 2 * (L + 1)) (n := n) ?_ ?_
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hc
    change ‖etaIntegrandJet d K square q n η X‖ ≤ _ at hc
    convert! hc using 1
    dsimp [C]
    ring
  · intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_weightedJet d.h_pos (tailWeight d K square) K q X square i (diffusion η)]
    apply (weightedJet_bound d.h_pos hK (tailSize_nonneg d square)
      (tailWeight_bound d hKp square) square i (diffusion_abs_bound hη) hX).trans
    apply mul_le_mul_of_nonneg_right _ hw
    apply mul_le_mul_of_nonneg_left _ (tailSize_nonneg d square)
    exact Finset.single_le_sum (fun j _ => editBound_nonneg square d.h (by positivity) j)
      (Finset.mem_range.mpr (by omega))
  · intro i hi _
    exact diffusion_iterated_bound hL.le hη i hi

theorem etaIntegrandJet_derivative (d : TailData) (K : ℝ) (square : Bool) (q : ℝ) :
    ∀ᵐ X ∂volume.restrict (Ioi K), ∀ n η,
      HasDerivAt (fun θ => etaIntegrandJet d K square q n θ X)
        (etaIntegrandJet d K square q (n + 1) η X) η := by
  apply Eventually.of_forall
  intro X n η
  have hc := (weightedJet_zero_contDiff d.h_pos (tailWeight d K square) K q X square).comp
    diffusion_contDiff
  have hd := hc.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n) η
  simpa only [etaIntegrandJet, iteratedDeriv_succ, Function.comp_def] using hd.hasDerivAt

theorem etaIntegrandJet_integrable (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    (square : Bool) {q : ℝ} (hq : tailDecay d square + q < 0) (n : ℕ) (η : ℝ) :
    IntegrableOn (etaIntegrandJet d K square q n η) (Ioi K) :=
  chain_integrable (etaIntegrandJet_measurable d hK square q)
    (etaIntegrandJet_dominated d hK square hq) n η

/-- Every genuine eta derivative of the improper debt is the integral of
the same genuine derivative of its integrand. -/
theorem etaDebt_derivative_integral (d : TailData) {K : ℝ} (hK : 1 ≤ K)
    (square : Bool) {q : ℝ} (hq : tailDecay d square + q < 0) (n : ℕ) (η : ℝ) :
    iteratedDeriv n (etaDebt d K square q) η =
      ∫ X in Ioi K, etaIntegrandJet d K square q n η X :=
  iteratedDeriv_integral_chain (etaIntegrandJet_derivative d K square q)
    (etaIntegrandJet_measurable d hK square q)
    (etaIntegrandJet_dominated d hK square hq) n η

theorem pressure_integrand_eq (d : TailData) {K X : ℝ} (hK : 0 < K) (hX : K < X) (η : ℝ) :
    squareChange (outgoingProfile d K η) d.h (diffusion η) K X / X =
      weightedJet (tailWeight d K true) true d.h K (-1) 0 (diffusion η) X := by
  simp only [weightedJet, tailWeight, editJet, ite_true]
  rw [squareCorrectionJet_zero]
  unfold squareChange edit
  rw [outgoingProfile_eq_powerTail d hK hX.le η, Real.rpow_neg_one]
  ring

theorem energy_integrand_eq (d : TailData) {K X : ℝ} (hK : 0 < K) (hX : K < X) (η : ℝ) :
    squareChange (outgoingProfile d K η) d.h (diffusion η) K X =
      weightedJet (tailWeight d K true) true d.h K 0 0 (diffusion η) X := by
  simp only [weightedJet, tailWeight, editJet, ite_true]
  rw [squareCorrectionJet_zero, Real.rpow_zero]
  unfold squareChange edit
  rw [outgoingProfile_eq_powerTail d hK hX.le η]
  ring

theorem angular_integrand_eq (d : TailData) {K X : ℝ} (hK : 0 < K) (hX : K < X) (η : ℝ) :
    Real.sqrt (2 * X) * change (outgoingProfile d K η) d.h (diffusion η) K X =
      Real.sqrt 2 * weightedJet (tailWeight d K false) false d.h K (1 / 2) 0 (diffusion η) X := by
  simp only [weightedJet, tailWeight, editJet, Bool.false_eq_true, ite_false, correctionJet_zero]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [Real.sqrt_eq_rpow]
  unfold change edit multiplier
  rw [outgoingProfile_eq_powerTail d hK hX.le η]
  ring

theorem physical_debts_integrable (d : TailData) {K : ℝ} (hK : 1 ≤ K) (η : ℝ) :
    IntegrableOn (fun X => squareChange (outgoingProfile d K η) d.h (diffusion η) K X / X) (Ioi K) ∧
    IntegrableOn (squareChange (outgoingProfile d K η) d.h (diffusion η) K) (Ioi K) ∧
    IntegrableOn (fun X => Real.sqrt (2 * X) *
      change (outgoingProfile d K η) d.h (diffusion η) K X) (Ioi K) := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  constructor
  · apply (etaIntegrandJet_integrable d hK true (ParametricHeatTail.pressure_decay d) 0 η).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    exact (pressure_integrand_eq d hKp hX η).symm
  constructor
  · apply (etaIntegrandJet_integrable d hK true (ParametricHeatTail.energy_decay d) 0 η).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    exact (energy_integrand_eq d hKp hX η).symm
  · apply ((etaIntegrandJet_integrable d hK false (ParametricHeatTail.angular_decay d) 0
      η).const_mul
      (Real.sqrt 2)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    exact (angular_integrand_eq d hKp hX η).symm

/-- Differentiation under the literal pressure-debt improper integral. -/
theorem physicalPressure_derivative_integral (d : TailData) {K : ℝ} (hK : 1 ≤ K) (n : ℕ) (η : ℝ) :
    iteratedDeriv n (physicalPressure d K) η =
      ∫ X in Ioi K, iteratedDeriv n
        (fun θ => squareChange (outgoingProfile d K θ) d.h (diffusion θ) K X / X) η := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  rw [show physicalPressure d K = etaDebt d K true (-1) from funext (physicalPressure_eq d hKp),
    etaDebt_derivative_integral d hK true (ParametricHeatTail.pressure_decay d)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  dsimp only
  rw [show (fun θ => squareChange (outgoingProfile d K θ) d.h (diffusion θ) K X / X) =
    (fun θ => weightedJet (tailWeight d K true) true d.h K (-1) 0 (diffusion θ) X) from
      funext (pressure_integrand_eq d hKp hX)]
  rfl

/-- Differentiation under the literal energy-debt improper integral. -/
theorem physicalEnergy_derivative_integral (d : TailData) {K : ℝ} (hK : 1 ≤ K) (n : ℕ) (η : ℝ) :
    iteratedDeriv n (physicalEnergy d K) η =
      ∫ X in Ioi K, iteratedDeriv n
        (fun θ => squareChange (outgoingProfile d K θ) d.h (diffusion θ) K X) η := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  rw [show physicalEnergy d K = etaDebt d K true 0 from funext (physicalEnergy_eq d hKp),
    etaDebt_derivative_integral d hK true (ParametricHeatTail.energy_decay d)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  dsimp only
  rw [show (fun θ => squareChange (outgoingProfile d K θ) d.h (diffusion θ) K X) =
    (fun θ => weightedJet (tailWeight d K true) true d.h K 0 0 (diffusion θ) X) from
      funext (energy_integrand_eq d hKp hX)]
  rfl

/-- Differentiation under the literal angular-debt improper integral. -/
theorem physicalAngular_derivative_integral (d : TailData) {K : ℝ} (hK : 1 ≤ K) (n : ℕ) (η : ℝ) :
    iteratedDeriv n (physicalAngular d K) η =
      ∫ X in Ioi K, iteratedDeriv n
        (fun θ => Real.sqrt (2 * X) * change (outgoingProfile d K θ) d.h (diffusion θ) K X) η := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  rw [show physicalAngular d K = (fun θ => Real.sqrt 2 * etaDebt d K false (1 / 2) θ) from
      funext (physicalAngular_eq d hKp),
    iteratedDeriv_const_mul _ ((etaDebt_contDiff d hK false (ParametricHeatTail.angular_decay
        d)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt,
    etaDebt_derivative_integral d hK false (ParametricHeatTail.angular_decay d), ←
        integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  dsimp only
  rw [show (fun θ => Real.sqrt (2 * X) * change (outgoingProfile d K θ) d.h (diffusion θ) K X) =
    (fun θ => Real.sqrt 2 * weightedJet (tailWeight d K false) false d.h K (1 / 2) 0 (diffusion θ)
        X) from
      funext (angular_integrand_eq d hKp hX)]
  have hc := (weightedJet_zero_contDiff d.h_pos (tailWeight d K false) K (1 / 2) X false).comp
    diffusion_contDiff
  simpa only [Function.comp_def, etaIntegrandJet] using
    (iteratedDeriv_const_mul (Real.sqrt 2) (hc.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt).symm

theorem physicalDebt_eq_original (d : TailData) {K η : ℝ} (hK : 0 < K)
    (hη : η ∈ Icc (-1 : ℝ) 1) :
    physicalDebt d K η = ParametricTerminalCompensation.physicalDebt d K η := by
  simp only [physicalDebt, ParametricTerminalCompensation.physicalDebt,
    physicalPressure_eq_original d hK hη, physicalEnergy_eq_original d hK hη,
    physicalAngular_eq_original d hK hη]

theorem normalizedDebt_eq_original (d : TailData) {K η : ℝ} (hK : 0 < K)
    (hη : η ∈ Icc (-1 : ℝ) 1) :
    normalizedDebt d K η =
      TerminalCompensation.scaledDebt K (ParametricTerminalCompensation.physicalDebt d K η) := by
  rw [normalizedDebt, physicalDebt_eq_original d hK hη]

theorem enlargedBand_isCompact : IsCompact enlargedBand := isCompact_Icc

theorem enlargedBand_uniqueDiffOn : UniqueDiffOn ℝ enlargedBand :=
  uniqueDiffOn_Icc (by norm_num)

theorem physicalBand_subset_openNeighborhood :
    Icc (-1 : ℝ) 1 ⊆ Ioo (-(3 / 2 : ℝ)) (3 / 2) := by
  intro η hη
  constructor <;> linarith [hη.1, hη.2]

theorem normalizedDebt_derivWithin (d : TailData) {K η : ℝ} (hK : 1 ≤ K)
    (hη : η ∈ enlargedBand) :
    derivWithin (normalizedDebt d K) enlargedBand η = deriv (normalizedDebt d K) η :=
  (((normalizedDebt_contDiff d hK).differentiable (by
      simp) η).hasDerivAt.hasDerivWithinAt).derivWithin
    (enlargedBand_uniqueDiffOn η hη)

/-- Direct input to the existing compact-parameter compensation solver. The
functions are already globally smooth; the within derivative is only the
solver's compact-domain convention. -/
theorem exists_normalized_C1_within_bounds (d : TailData) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∀ η ∈ enlargedBand,
      ‖normalizedDebt d K η‖ ≤ C / K ∧
      ‖derivWithin (normalizedDebt d K) enlargedBand η‖ ≤ C / K := by
  obtain ⟨C, hC, hb⟩ := exists_normalized_C1_bounds d
  refine ⟨C, hC, fun K hK η hη => ?_⟩
  rw [normalizedDebt_derivWithin d hK hη]
  exact hb K hK η hη

theorem physicalEdit_joint_contDiffOn (d : TailData) {K : ℝ} (hK : 0 < K) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => physicalEdit d K p.2 p.1)
      (Ioi 0 ×ˢ (univ : Set ℝ)) := by
  have hs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => switch K p.1)
      (Ioi 0 ×ˢ (univ : Set ℝ)) :=
    (switch_contDiffOn hK).comp contDiffOn_fst (fun _ hp => hp.1)
  have hH : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      HeatProfileExtension.scaledProfile (1 + d.h) p.1 (diffusion p.2))
      (Ioi 0 ×ˢ (univ : Set ℝ)) :=
    HeatProfileExtension.physicalProfile_contDiffOn (a := 1 + d.h) (by linarith [d.h_pos])
  exact (outgoingProfile_joint_contDiffOn d hK).mul
    (contDiffOn_const.add (hs.mul (hH.sub contDiffOn_const)))

theorem physicalEdit_eq_original (d : TailData) (K : ℝ) {η X : ℝ}
    (hη : η ∈ Icc (-1 : ℝ) 1) (hX : 0 < X) :
    physicalEdit d K η X = ParametricHeatTail.physicalEdit d K η X :=
  edit_eq_original (outgoingProfile d K η) d.h (ParametricHeatTail.diffusion_mem hη).1 hX

theorem normalizedDebt_joint_contDiffOn (d : TailData) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => normalizedDebt d p.1 p.2)
      (Ioi 0 ×ˢ (univ : Set ℝ)) := by
  have hroot : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Real.sqrt (2 * p.1))
      (Ioi 0 ×ˢ (univ : Set ℝ)) :=
    (contDiffOn_const.mul contDiffOn_fst).sqrt
      (fun p hp => (mul_pos (by norm_num) (show 0 < p.1 from hp.1)).ne')
  apply contDiffOn_pi.mpr
  intro j
  fin_cases j
  · exact physicalPressure_joint_contDiffOn d
  · exact (physicalEnergy_joint_contDiffOn d).div contDiffOn_fst
      (fun p hp => (show 0 < p.1 from hp.1).ne')
  · exact (physicalAngular_joint_contDiffOn d).div (contDiffOn_fst.mul hroot)
      (fun p hp => mul_ne_zero (show p.1 ≠ 0 from (show 0 < p.1 from hp.1).ne')
        (Real.sqrt_pos.mpr (mul_pos (by norm_num) (show 0 < p.1 from hp.1))).ne')

end NavierStokes.ExtendedHeatDebts
