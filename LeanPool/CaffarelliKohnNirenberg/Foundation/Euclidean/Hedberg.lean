/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.Maximal.StrongType
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The order-one Euclidean Riesz potential
This file supplies the geometric part of Hedberg's proof in the native
three-dimensional model `Vec3`.  The maximal majorant is the uncentred
maximal function from `Maximal.HardyLittlewood`.
-/

public section

open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic
/-- A maximal majorant for the absolute value of a real function. -/
@[expose]
def IsMaximalMajorant (f : Vec3 → ℝ) (M : Vec3 → ℝ≥0∞) : Prop :=
  ∀ z : Vec3, ∀ R : ℝ, 0 < R →
    (∫⁻ w in Metric.ball z R, ENNReal.ofReal |f w|) ≤
      M z * volume (Metric.ball z R)

/-- The maximal majorant associated with the Euclidean maximal function. -/
@[expose]
def maximalMajorant (f : Vec3 → ℝ) : Vec3 → ℝ≥0∞ :=
  maximalFunction (fun z ↦ ENNReal.ofReal |f z|)
theorem isMaximalMajorant_maximalMajorant (f : Vec3 → ℝ) :
    IsMaximalMajorant f (maximalMajorant f) := by
  intro z R hR
  have haverage := maximalFunction_average_le
    (f := fun w ↦ ENNReal.ofReal |f w|) (c := z) (z := z) (r := R)
    (Metric.mem_ball_self hR)
  rw [setLAverage_eq] at haverage
  have hvol0 : volume (Metric.ball z R) ≠ 0 := by
    rw [volume_metricBall_eq (x := z) hR]
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hvoltop : volume (Metric.ball z R) ≠ ∞ := by
    rw [volume_metricBall_eq (x := z) hR]
    exact ENNReal.ofReal_ne_top
  exact (ENNReal.div_le_iff hvol0
    hvoltop).mp haverage
/-- The order-one Riesz kernel and its nonnegative potential. -/
@[expose] def rieszKernelOne (z w : Vec3) : ℝ≥0∞ :=
  (ENNReal.ofReal (dist z w)) ^ (-2 : ℝ)
/-- Order-one Riesz potential of the absolute value of a scalar source. -/
@[expose]
def rieszPotentialOne (f : Vec3 → ℝ) (z : Vec3) : ℝ≥0∞ :=
  ∫⁻ w, rieszKernelOne z w * ENNReal.ofReal |f w|
/-- Dyadic shell inside the reference radius for the near-field potential estimate. -/
def nearShell (R : ℝ) (n : ℕ) (z : Vec3) : Set Vec3 :=
  {w | (2 : ℝ) ^ (Int.negSucc n : ℝ) * R ≤ dist z w ∧
    dist z w < (2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) * R}
/-- Dyadic shell outside the reference radius for the far-field potential estimate. -/
def farShell (R : ℝ) (n : ℕ) (z : Vec3) : Set Vec3 :=
  {w | (2 : ℝ) ^ (n : ℝ) * R ≤ dist z w ∧
    dist z w < (2 : ℝ) ^ ((n : ℝ) + 1) * R}
private lemma nearShell_measurable (R : ℝ) (n : ℕ) (z : Vec3) :
    MeasurableSet (nearShell R n z) := by
  have hdist : Measurable (fun w : Vec3 => dist z w) :=
    measurable_dist.comp (measurable_const.prodMk measurable_id)
  exact (hdist measurableSet_Ici).inter (hdist measurableSet_Iio)
private lemma farShell_measurable (R : ℝ) (n : ℕ) (z : Vec3) :
    MeasurableSet (farShell R n z) := by
  have hdist : Measurable (fun w : Vec3 => dist z w) :=
    measurable_dist.comp (measurable_const.prodMk measurable_id)
  exact (hdist measurableSet_Ici).inter (hdist measurableSet_Iio)
private lemma nearShell_pairwise {R : ℝ} (hR : 0 < R) (z : Vec3) :
    Pairwise (Function.onFun Disjoint (fun n ↦ nearShell R n z)) := by
  intro n m hnm
  change Disjoint (nearShell R n z) (nearShell R m z)
  rw [Set.disjoint_left]
  intro w hwn hwm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hindex : Int.negSucc m + 1 ≤ Int.negSucc n := by omega
    have hexp : ((Int.negSucc m : ℝ) + 1) ≤ (Int.negSucc n : ℝ) := by
      exact_mod_cast hindex
    have hpow : (2 : ℝ) ^ ((Int.negSucc m : ℝ) + 1) ≤
        (2 : ℝ) ^ (Int.negSucc n : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hrad := mul_le_mul_of_nonneg_right hpow hR.le
    exact (not_lt_of_ge (hrad.trans hwn.1)) hwm.2
  · have hindex : Int.negSucc n + 1 ≤ Int.negSucc m := by omega
    have hexp : ((Int.negSucc n : ℝ) + 1) ≤ (Int.negSucc m : ℝ) := by
      exact_mod_cast hindex
    have hpow : (2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) ≤
        (2 : ℝ) ^ (Int.negSucc m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hrad := mul_le_mul_of_nonneg_right hpow hR.le
    exact (not_lt_of_ge (hrad.trans hwm.1)) hwn.2
private lemma farShell_pairwise {R : ℝ} (hR : 0 < R) (z : Vec3) :
    Pairwise (Function.onFun Disjoint (fun n ↦ farShell R n z)) := by
  intro n m hnm
  change Disjoint (farShell R n z) (farShell R m z)
  rw [Set.disjoint_left]
  intro w hwn hwm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hexp : ((n : ℝ) + 1) ≤ (m : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hlt)
    have hpow : (2 : ℝ) ^ ((n : ℝ) + 1) ≤ (2 : ℝ) ^ (m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hrad := mul_le_mul_of_nonneg_right hpow hR.le
    exact (not_lt_of_ge (hrad.trans hwm.1)) hwn.2
  · have hexp : ((m : ℝ) + 1) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hgt)
    have hpow : (2 : ℝ) ^ ((m : ℝ) + 1) ≤ (2 : ℝ) ^ (n : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hrad := mul_le_mul_of_nonneg_right hpow hR.le
    exact (not_lt_of_ge (hrad.trans hwn.1)) hwm.2
private lemma zero_set_volume (z : Vec3) :
    volume ({w | dist z w = 0} : Set Vec3) = 0 := by
  apply measure_mono_null
    (show {w | dist z w = 0} ⊆ ({z} : Set Vec3) by
      intro w hw
      exact (dist_eq_zero.mp hw) ▸ mem_singleton z)
  simp
private lemma nearShell_cover {z : Vec3} {R : ℝ} (hR : 0 < R) :
    {w | dist z w < R} ⊆
      {w | dist z w = 0} ∪ ⋃ n : ℕ, nearShell R n z := by
  intro w hw
  by_cases hzero : dist z w = 0
  · exact Or.inl hzero
  · have hne : z ≠ w := by
      intro h
      exact hzero (by simp [h])
    have hpos : 0 < dist z w := dist_pos.mpr hne
    let x : ℝ := dist z w / R
    let L : ℝ := Real.log 2
    let k : ℤ := ⌊Real.log x / L⌋
    have hL : 0 < L := Real.log_pos (by norm_num)
    have hx : 0 < x := div_pos hpos hR
    have hx1 : x < 1 := (div_lt_one hR).2 hw
    have hkneg : k < 0 := by
      apply (Int.floor_lt).2
      have hlogx : Real.log x < 0 := Real.log_neg hx hx1
      simpa using (div_neg_of_neg_of_pos hlogx hL)
    have hklo : (k : ℝ) ≤ Real.log x / L := Int.floor_le _
    have hkhi : Real.log x / L < (k : ℝ) + 1 := Int.lt_floor_add_one _
    have hpowlo : (2 : ℝ) ^ (k : ℝ) ≤ x := by
      apply (Real.strictMonoOn_log.le_iff_le
        (Real.rpow_pos_of_pos (by norm_num) _) hx).mp
      rw [Real.log_rpow (by norm_num)]
      calc
        (k : ℝ) * Real.log 2 ≤ (Real.log x / L) * L :=
          mul_le_mul_of_nonneg_right hklo hL.le
        _ = Real.log x := by field_simp [hL.ne']
    have hpowhi : x < (2 : ℝ) ^ ((k : ℝ) + 1) := by
      apply (Real.strictMonoOn_log.lt_iff_lt
        hx (Real.rpow_pos_of_pos (by norm_num) _)).mp
      rw [Real.log_rpow (by norm_num)]
      calc
        Real.log x = (Real.log x / L) * L := by field_simp [hL.ne']
        _ < ((k : ℝ) + 1) * L := mul_lt_mul_of_pos_right hkhi hL
    have hinner : (2 : ℝ) ^ (k : ℝ) * R ≤ dist z w := by
      simpa [x] using (le_div_iff₀ hR).mp hpowlo
    have houter : dist z w < (2 : ℝ) ^ ((k : ℝ) + 1) * R := by
      simpa [x] using (div_lt_iff₀ hR).mp hpowhi
    obtain ⟨n, hn⟩ := Int.eq_negSucc_of_lt_zero hkneg
    rw [hn] at hinner houter
    exact Or.inr (mem_iUnion.mpr ⟨n, ⟨hinner, houter⟩⟩)
private lemma farShell_cover {z : Vec3} {R : ℝ} (hR : 0 < R) :
    {w | R ≤ dist z w} ⊆ ⋃ n : ℕ, farShell R n z := by
  intro w hw
  let x : ℝ := dist z w / R
  let L : ℝ := Real.log 2
  let k : ℤ := ⌊Real.log x / L⌋
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hx : 1 ≤ x := (one_le_div hR).2 hw
  have hk : 0 ≤ k := by
    apply (Int.floor_nonneg).2
    exact div_nonneg (Real.log_nonneg hx) hL.le
  have hklo : (k : ℝ) ≤ Real.log x / L := Int.floor_le _
  have hkhi : Real.log x / L < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hpowlo : (2 : ℝ) ^ (k : ℝ) ≤ x := by
    apply (Real.strictMonoOn_log.le_iff_le
      (Real.rpow_pos_of_pos (by norm_num) _) (by positivity : 0 < x)).mp
    rw [Real.log_rpow (by norm_num)]
    calc
      (k : ℝ) * Real.log 2 ≤ (Real.log x / L) * L :=
        mul_le_mul_of_nonneg_right hklo hL.le
      _ = Real.log x := by field_simp [hL.ne']
  have hpowhi : x < (2 : ℝ) ^ ((k : ℝ) + 1) := by
    apply (Real.strictMonoOn_log.lt_iff_lt
      (by positivity : 0 < x) (Real.rpow_pos_of_pos (by norm_num) _)).mp
    rw [Real.log_rpow (by norm_num)]
    calc
      Real.log x = (Real.log x / L) * L := by field_simp [hL.ne']
      _ < ((k : ℝ) + 1) * L := mul_lt_mul_of_pos_right hkhi hL
  have hinner : (2 : ℝ) ^ (k : ℝ) * R ≤ dist z w := by
    simpa [x] using (le_div_iff₀ hR).mp hpowlo
  have houter : dist z w < (2 : ℝ) ^ ((k : ℝ) + 1) * R := by
    simpa [x] using (div_lt_iff₀ hR).mp hpowhi
  have hinner' : (2 : ℝ) ^ (k.toNat : ℝ) * R ≤ dist z w := by
    have hcast : (k.toNat : ℝ) = (k : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hk
    rw [hcast]
    exact hinner
  have houter' : dist z w < (2 : ℝ) ^ ((k.toNat : ℝ) + 1) * R := by
    have hcast : (k.toNat : ℝ) = (k : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hk
    rw [hcast]
    exact houter
  exact mem_iUnion.mpr ⟨k.toNat, ⟨hinner', houter'⟩⟩
private lemma shell_ball_subset {R : ℝ} {n : ℕ} {z : Vec3} :
    nearShell R n z ⊆ Metric.ball z ((2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) * R) := by
  intro w hw
  change dist w z < _
  simpa only [dist_comm] using hw.2
private lemma far_shell_ball_subset {R : ℝ} {n : ℕ} {z : Vec3} :
    farShell R n z ⊆ Metric.ball z ((2 : ℝ) ^ ((n : ℝ) + 1) * R) := by
  intro w hw
  change dist w z < _
  simpa only [dist_comm] using hw.2
private lemma volume_nearShell_le {R : ℝ} {n : ℕ} {z : Vec3} (hR : 0 < R) :
    volume (nearShell R n z) ≤
      ENNReal.ofReal ((2 * ((2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) * R)) ^ 3) := by
  calc
    volume (nearShell R n z) ≤
        volume (Metric.ball z ((2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) * R)) :=
      measure_mono shell_ball_subset
    _ = _ := volume_metricBall_eq (x := z) (by positivity)
private lemma volume_farShell_le {R : ℝ} {n : ℕ} {z : Vec3} (hR : 0 < R) :
    volume (farShell R n z) ≤
      ENNReal.ofReal ((2 * ((2 : ℝ) ^ ((n : ℝ) + 1) * R)) ^ 3) := by
  calc
    volume (farShell R n z) ≤
        volume (Metric.ball z ((2 : ℝ) ^ ((n : ℝ) + 1) * R)) :=
      measure_mono far_shell_ball_subset
    _ = _ := volume_metricBall_eq (x := z) (by positivity)
private lemma ennreal_mul_rpow_of_ne_zero_of_ne_top
    {x y : ℝ≥0∞} {e : ℝ} (hx0 : x ≠ 0) (hxtop : x ≠ ∞)
    (hy0 : y ≠ 0) (hytop : y ≠ ∞) :
    (x * y) ^ e = x ^ e * y ^ e := by
  by_cases he : 0 ≤ e
  · exact ENNReal.mul_rpow_of_nonneg x y he
  · have he' : 0 ≤ -e := le_of_lt (neg_pos.mpr (lt_of_not_ge he))
    have hxpow : x ^ e = (x ^ (-e))⁻¹ := by
      simpa using (ENNReal.rpow_neg x (-e))
    have hypow : y ^ e = (y ^ (-e))⁻¹ := by
      simpa using (ENNReal.rpow_neg y (-e))
    calc
      (x * y) ^ e = ((x * y) ^ (-e))⁻¹ := by
        simpa using (ENNReal.rpow_neg (x * y) (-e))
      _ = (x ^ (-e) * y ^ (-e))⁻¹ := by
        rw [ENNReal.mul_rpow_of_nonneg x y he']
      _ = (x ^ (-e))⁻¹ * (y ^ (-e))⁻¹ := by
        have hxr0 : x ^ (-e) ≠ 0 :=
          (ENNReal.rpow_pos (lt_of_le_of_ne bot_le (Ne.symm hx0)) hxtop).ne'
        have hxrtop : x ^ (-e) ≠ ∞ :=
          ENNReal.rpow_ne_top_of_nonneg he' hxtop
        have hyr0 : y ^ (-e) ≠ 0 :=
          (ENNReal.rpow_pos (lt_of_le_of_ne bot_le (Ne.symm hy0)) hytop).ne'
        have hyrtop : y ^ (-e) ≠ ∞ :=
          ENNReal.rpow_ne_top_of_nonneg he' hytop
        exact ENNReal.mul_inv (Or.inl hxr0) (Or.inl hxrtop)
      _ = x ^ e * y ^ e := by rw [hxpow, hypow]
/-- Geometric-series term controlling the near-field order-one potential. -/
def nearTerm (n : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal ((2 : ℝ) ^ (Int.negSucc n : ℝ))) ^ (-2 : ℝ) *
    ENNReal.ofReal ((4 * ((2 : ℝ) ^ (Int.negSucc n : ℝ))) ^ 3)
/-- The geometric constant in the near-field estimate. -/
@[expose]
def hedbergNearConstant : ℝ≥0∞ := ∑' n : ℕ, nearTerm n

private lemma near_shell_integral_le
    {R : ℝ} (hR : 0 < R) {f : Vec3 → ℝ} (hf : AEMeasurable f volume)
    {M : Vec3 → ℝ≥0∞} (hM : IsMaximalMajorant f M)
    (n : ℕ) (z : Vec3) :
    (∫⁻ w in nearShell R n z,
      rieszKernelOne z w * ENNReal.ofReal |f w|) ≤
      nearTerm n * ENNReal.ofReal R * M z := by
  let a : ℝ := (2 : ℝ) ^ (Int.negSucc n : ℝ) * R
  let b : ℝ := (2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) * R
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hkernel : ∀ w ∈ nearShell R n z,
      rieszKernelOne z w ≤ (ENNReal.ofReal a) ^ (-2 : ℝ) := by
    intro w hw
    have hinner : a ≤ dist z w := by
      simpa [a] using hw.1
    rw [rieszKernelOne, ENNReal.rpow_neg, ENNReal.rpow_neg,
      ENNReal.inv_le_inv]
    apply ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hinner)
    norm_num
  have hball :
      (∫⁻ w in nearShell R n z, ENNReal.ofReal |f w|) ≤
        M z * volume (Metric.ball z b) := by
    calc
      (∫⁻ w in nearShell R n z, ENNReal.ofReal |f w|) ≤
          ∫⁻ w in Metric.ball z b, ENNReal.ofReal |f w| :=
        lintegral_mono_set (shell_ball_subset (R := R) (n := n) (z := z))
      _ ≤ M z * volume (Metric.ball z b) := hM z b hb
  have hprod :
      (∫⁻ w in nearShell R n z,
        rieszKernelOne z w * ENNReal.ofReal |f w|) ≤
        (ENNReal.ofReal a) ^ (-2 : ℝ) *
          (∫⁻ w in nearShell R n z, ENNReal.ofReal |f w|) := by
    calc
      (∫⁻ w in nearShell R n z,
          rieszKernelOne z w * ENNReal.ofReal |f w|) ≤
          ∫⁻ w in nearShell R n z,
            (ENNReal.ofReal a) ^ (-2 : ℝ) * ENNReal.ofReal |f w| := by
        apply setLIntegral_mono_ae
          ((hf.norm.ennreal_ofReal.restrict).const_mul
            ((ENNReal.ofReal a) ^ (-2 : ℝ)))
        filter_upwards [] with w hw
        exact mul_le_mul (hkernel w hw) (le_refl _)
          (by positivity) (by positivity)
      _ = (ENNReal.ofReal a) ^ (-2 : ℝ) *
          (∫⁻ w in nearShell R n z, ENNReal.ofReal |f w|) := by
        apply lintegral_const_mul'
        rw [ENNReal.rpow_neg]
        exact ENNReal.inv_ne_top.mpr
          (ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr ha)
            (by norm_num)))
  have hscale :
      (ENNReal.ofReal a) ^ (-2 : ℝ) *
          ENNReal.ofReal ((2 * b) ^ 3) =
        nearTerm n * ENNReal.ofReal R := by
    have hc : 0 < (2 : ℝ) ^ (Int.negSucc n : ℝ) := by positivity
    have hc0 : (2 : ℝ) ^ (Int.negSucc n : ℝ) ≠ 0 := ne_of_gt hc
    have hR0 : R ≠ 0 := ne_of_gt hR
    have hcR0 : (2 : ℝ) ^ (Int.negSucc n : ℝ) * R ≠ 0 :=
      mul_ne_zero hc0 hR0
    have hfourc : 4 * (2 : ℝ) ^ (Int.negSucc n : ℝ) > 0 := by positivity
    have hfourc0 : 4 * (2 : ℝ) ^ (Int.negSucc n : ℝ) ≠ 0 :=
      ne_of_gt hfourc
    have hleft : a = (2 : ℝ) ^ (Int.negSucc n : ℝ) * R := rfl
    have hright : 2 * b = (4 * (2 : ℝ) ^ (Int.negSucc n : ℝ)) * R := by
      dsimp [b]
      rw [Real.rpow_add (by positivity)]
      ring
    rw [hleft, hright, ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_mul hfourc.le, ENNReal.ofReal_mul hc.le]
    rw [ennreal_mul_rpow_of_ne_zero_of_ne_top
      (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top
      (ENNReal.ofReal_pos.mpr hR).ne' ENNReal.ofReal_ne_top]
    rw [← ENNReal.rpow_natCast]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    calc
      _ = ((ENNReal.ofReal ((2 : ℝ) ^ (Int.negSucc n : ℝ))) ^ (-2 : ℝ) *
          ENNReal.ofReal ((4 * ((2 : ℝ) ^ (Int.negSucc n : ℝ))) ^ 3)) *
          (ENNReal.ofReal R ^ (-2 : ℝ) * ENNReal.ofReal R ^ (3 : ℝ)) := by
        rw [ENNReal.ofReal_pow (by positivity)]
        norm_num
        ac_rfl
      _ = nearTerm n * ENNReal.ofReal R := by
        rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hR).ne'
          ENNReal.ofReal_ne_top]
        norm_num [nearTerm]
  calc
    (∫⁻ w in nearShell R n z,
        rieszKernelOne z w * ENNReal.ofReal |f w|) ≤
        (ENNReal.ofReal a) ^ (-2 : ℝ) *
          (M z * volume (Metric.ball z b)) := by
      exact hprod.trans (mul_le_mul_of_nonneg_left hball (by positivity))
    _ ≤ (ENNReal.ofReal a) ^ (-2 : ℝ) *
          (M z * ENNReal.ofReal ((2 * b) ^ 3)) := by
      gcongr
      rw [volume_metricBall_eq (x := z) hb]
    _ = nearTerm n * ENNReal.ofReal R * M z := by
      calc
        (ENNReal.ofReal a) ^ (-2 : ℝ) *
            (M z * ENNReal.ofReal ((2 * b) ^ 3)) =
            ((ENNReal.ofReal a) ^ (-2 : ℝ) *
              ENNReal.ofReal ((2 * b) ^ 3)) * M z := by ac_rfl
        _ = nearTerm n * ENNReal.ofReal R * M z := by rw [hscale]

theorem rieszPotentialOne_near_le
    {R : ℝ} (hR : 0 < R) {f : Vec3 → ℝ}
    (hf : AEMeasurable f volume) {M : Vec3 → ℝ≥0∞}
    (hM : IsMaximalMajorant f M) (z : Vec3) :
    (∫⁻ w in {w | dist z w < R},
      rieszKernelOne z w * ENNReal.ofReal |f w|) ≤
      hedbergNearConstant * ENNReal.ofReal R * M z := by
  let s₀ : Set Vec3 := {w | dist z w = 0}
  let s : ℕ → Set Vec3 := fun n ↦ nearShell R n z
  let g : Vec3 → ℝ≥0∞ := fun w ↦
    rieszKernelOne z w * ENNReal.ofReal |f w|
  have hs₀ : MeasurableSet s₀ := by
    have hdist : Measurable (fun w : Vec3 => dist z w) :=
      measurable_dist.comp (measurable_const.prodMk measurable_id)
    exact hdist (measurableSet_singleton (0 : ℝ))
  have hs : ∀ n, MeasurableSet (s n) := by
    intro n
    simpa [s] using nearShell_measurable R n z
  have hspair : Pairwise (Function.onFun Disjoint s) := by
    simpa [s] using nearShell_pairwise hR z
  have hzdisj : Disjoint s₀ (⋃ n, s n) := by
    rw [Set.disjoint_iUnion_right]
    intro n
    rw [Set.disjoint_left]
    intro w hwzero hwshell
    have hinner : 0 < (2 : ℝ) ^ (Int.negSucc n : ℝ) * R := by
      positivity
    exact (not_lt_of_ge (hwshell.1.trans_eq hwzero)) hinner
  have hzero : volume s₀ = 0 := by
    change volume ({w | dist z w = 0} : Set Vec3) = 0
    exact zero_set_volume z
  have hzero_int : (∫⁻ w in s₀, g w) = 0 := by
    rw [show (∫⁻ w in s₀, g w) = ∫⁻ w, g w ∂volume.restrict s₀ by rfl,
      Measure.restrict_eq_zero.mpr hzero, lintegral_zero_measure]
  have hcover : {w | dist z w < R} ⊆ s₀ ∪ ⋃ n, s n := by
    simpa [s₀, s] using nearShell_cover hR
  have hsum :
      (∫⁻ w in ⋃ n, s n, g w) = ∑' n, ∫⁻ w in s n, g w := by
    exact lintegral_iUnion hs hspair g
  have hterm : ∀ n : ℕ,
      (∫⁻ w in s n, g w) ≤ nearTerm n * ENNReal.ofReal R * M z := by
    intro n
    simpa [s, g] using near_shell_integral_le hR hf hM n z
  calc
    (∫⁻ w in {w | dist z w < R},
        rieszKernelOne z w * ENNReal.ofReal |f w|) ≤
        ∫⁻ w in s₀ ∪ ⋃ n, s n, g w :=
      lintegral_mono_set hcover
    _ = (∫⁻ w in s₀, g w) + ∫⁻ w in ⋃ n, s n, g w :=
      lintegral_union (MeasurableSet.iUnion hs) hzdisj
    _ = ∑' n, ∫⁻ w in s n, g w := by rw [hzero_int, zero_add, hsum]
    _ ≤ ∑' n, nearTerm n * ENNReal.ofReal R * M z :=
      ENNReal.tsum_le_tsum hterm
    _ = hedbergNearConstant * ENNReal.ofReal R * M z := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
      rfl

private lemma rieszKernelOne_measurable (z : Vec3) :
    Measurable (rieszKernelOne z) := by
  have hdist : Measurable (fun w : Vec3 => dist z w) :=
    measurable_dist.comp (measurable_const.prodMk measurable_id)
  exact ENNReal.continuous_rpow_const.measurable.comp
    (ENNReal.measurable_ofReal.comp hdist)

private lemma far_kernel_shell_bound
    {R : ℝ} (hR : 0 < R) (n : ℕ) (z : Vec3) :
    (∫⁻ w in farShell R n z, rieszKernelOne z w ^ (5 / 3 : ℝ)) ≤
      (ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ) * R)) ^ (-(10 / 3 : ℝ)) *
        ENNReal.ofReal ((2 * ((2 : ℝ) ^ ((n : ℝ) + 1) * R)) ^ 3) := by
  let a : ℝ := (2 : ℝ) ^ (n : ℝ) * R
  let b : ℝ := (2 : ℝ) ^ ((n : ℝ) + 1) * R
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hkernel : ∀ w ∈ farShell R n z,
      rieszKernelOne z w ^ (5 / 3 : ℝ) ≤
        (ENNReal.ofReal a) ^ (-(10 / 3 : ℝ)) := by
    intro w hw
    have hinner : a ≤ dist z w := by
      simpa [a] using hw.1
    have hbase : rieszKernelOne z w ≤ (ENNReal.ofReal a) ^ (-2 : ℝ) := by
      rw [rieszKernelOne, ENNReal.rpow_neg, ENNReal.rpow_neg,
        ENNReal.inv_le_inv]
      apply ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hinner)
      norm_num
    calc
      rieszKernelOne z w ^ (5 / 3 : ℝ) ≤
          ((ENNReal.ofReal a) ^ (-2 : ℝ)) ^ (5 / 3 : ℝ) :=
        ENNReal.rpow_le_rpow hbase (by norm_num)
      _ = (ENNReal.ofReal a) ^ (-(10 / 3 : ℝ)) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        ring
  have hmono :
      (∫⁻ w in farShell R n z, rieszKernelOne z w ^ (5 / 3 : ℝ)) ≤
        ∫⁻ w in farShell R n z,
          (ENNReal.ofReal a) ^ (-(10 / 3 : ℝ)) := by
    have hmeaspow : Measurable
        (fun w : Vec3 => rieszKernelOne z w ^ (5 / 3 : ℝ)) :=
      ENNReal.continuous_rpow_const.measurable.comp (rieszKernelOne_measurable z)
    apply setLIntegral_mono_ae
      (aemeasurable_const :
        AEMeasurable (fun _ : Vec3 =>
          (ENNReal.ofReal a) ^ (-(10 / 3 : ℝ)))
          (volume.restrict (farShell R n z)))
    filter_upwards [] with w hw
    exact hkernel w hw
  calc
    (∫⁻ w in farShell R n z, rieszKernelOne z w ^ (5 / 3 : ℝ)) ≤
        ∫⁻ w in farShell R n z,
          (ENNReal.ofReal a) ^ (-(10 / 3 : ℝ)) := hmono
    _ = (ENNReal.ofReal a) ^ (-(10 / 3 : ℝ)) *
        volume (farShell R n z) := setLIntegral_const _ _
    _ ≤ (ENNReal.ofReal a) ^ (-(10 / 3 : ℝ)) *
        ENNReal.ofReal ((2 * b) ^ 3) := by
      gcongr
      exact volume_farShell_le hR
    _ = _ := by rfl

private lemma far_shell_integral_le
    {R : ℝ} (hR : 0 < R) {f : Vec3 → ℝ} (hf : AEMeasurable f volume)
    (n : ℕ) (z : Vec3) :
    (∫⁻ w in farShell R n z,
      rieszKernelOne z w * ENNReal.ofReal |f w|) ≤
      ((ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ) * R)) ^ (-(10 / 3 : ℝ)) *
        ENNReal.ofReal ((2 * ((2 : ℝ) ^ ((n : ℝ) + 1) * R)) ^ 3)) ^
          (3 / 5 : ℝ) *
        (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
  let s : Set Vec3 := farShell R n z
  have hs : MeasurableSet s := by
    simpa [s] using farShell_measurable R n z
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict s)
    (p := (5 / 3 : ℝ)) (q := (5 / 2 : ℝ))
    (by
      rw [Real.holderConjugate_iff]
      constructor <;> norm_num)
    ((rieszKernelOne_measurable z).aemeasurable.restrict)
    (hf.norm.ennreal_ofReal.restrict)
  have hleft :
      (∫⁻ w in s, rieszKernelOne z w * ENNReal.ofReal |f w|) ≤
        (∫⁻ w in s, rieszKernelOne z w ^ (5 / 3 : ℝ)) ^ (3 / 5 : ℝ) *
          (∫⁻ w in s, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
    simpa [one_div, Real.norm_eq_abs] using hholder
  have hK := far_kernel_shell_bound hR n z
  have hF :
      (∫⁻ w in s, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ≤
        ∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ) := by
    refine MeasureTheory.lintegral_mono'
      (μ := volume.restrict s) (ν := volume)
      (f := fun w : Vec3 => ENNReal.ofReal |f w| ^ (5 / 2 : ℝ))
      (g := fun w : Vec3 => ENNReal.ofReal |f w| ^ (5 / 2 : ℝ))
      ((Measure.restrict_mono_set volume (Set.subset_univ s)).trans_eq
        Measure.restrict_univ) ?_
    intro w
    exact le_rfl
  calc
    (∫⁻ w in farShell R n z,
        rieszKernelOne z w * ENNReal.ofReal |f w|) =
        ∫⁻ w in s, rieszKernelOne z w * ENNReal.ofReal |f w| := by rfl
    _ ≤ (∫⁻ w in s, rieszKernelOne z w ^ (5 / 3 : ℝ)) ^ (3 / 5 : ℝ) *
          (∫⁻ w in s, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := hleft
    _ ≤ ((ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ) * R)) ^ (-(10 / 3 : ℝ)) *
        ENNReal.ofReal ((2 * ((2 : ℝ) ^ ((n : ℝ) + 1) * R)) ^ 3)) ^
          (3 / 5 : ℝ) *
        (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
      gcongr

/-- Geometric-series term controlling the far-field order-one potential. -/
def farTerm (n : ℕ) : ℝ≥0∞ :=
  ((ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ))) ^ (-(10 / 3 : ℝ)) *
    ENNReal.ofReal ((4 * ((2 : ℝ) ^ (n : ℝ))) ^ 3)) ^ (3 / 5 : ℝ)

private lemma far_shell_scale_identity {R : ℝ} (hR : 0 < R) (n : ℕ) :
    ((ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ) * R)) ^ (-(10 / 3 : ℝ)) *
      ENNReal.ofReal ((2 * ((2 : ℝ) ^ ((n : ℝ) + 1) * R)) ^ 3)) ^
        (3 / 5 : ℝ) =
      farTerm n * (ENNReal.ofReal R) ^ (-(1 / 5 : ℝ)) := by
  let c : ℝ := (2 : ℝ) ^ (n : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hfour : 0 < 4 * c := by positivity
  have hleft : c * R = (2 : ℝ) ^ (n : ℝ) * R := by rfl
  have hright : 2 * ((2 : ℝ) ^ ((n : ℝ) + 1) * R) = (4 * c) * R := by
    dsimp [c]
    rw [Real.rpow_add (by positivity)]
    ring
  have hscale :
      ENNReal.ofReal (c * R) ^ (-(10 / 3 : ℝ)) *
          ENNReal.ofReal ((4 * c * R) ^ 3) =
        (ENNReal.ofReal c) ^ (-(10 / 3 : ℝ)) *
          ENNReal.ofReal ((4 * c) ^ 3) *
            (ENNReal.ofReal R) ^ (-(1 / 3 : ℝ)) := by
    rw [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_mul hfour.le]
    have hp4 : ENNReal.ofReal ((4 * c) ^ 3) =
        ENNReal.ofReal (4 * c) ^ (3 : ℕ) :=
      ENNReal.ofReal_pow (by positivity) 3
    rw [hp4]
    rw [ennreal_mul_rpow_of_ne_zero_of_ne_top
      (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top
      (ENNReal.ofReal_pos.mpr hR).ne' ENNReal.ofReal_ne_top]
    rw [← ENNReal.rpow_natCast,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    calc
      _ = ((ENNReal.ofReal c) ^ (-(10 / 3 : ℝ)) *
          ENNReal.ofReal (4 * c) ^ (3 : ℕ)) *
          ((ENNReal.ofReal R) ^ (-(10 / 3 : ℝ)) *
            (ENNReal.ofReal R) ^ (3 : ℝ)) := by
        norm_num
        ac_rfl
      _ = _ := by
        rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hR).ne'
          ENNReal.ofReal_ne_top]
        congr 2
        · ring_nf
  rw [hleft, hright, hscale, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [← ENNReal.rpow_mul]
  dsimp [farTerm]
  rw [ENNReal.ofReal_pow (by positivity)]
  congr 1
  ring_nf

/-- Summed coefficient in the far-field Hedberg estimate. -/
@[expose]
def hedbergFarConstant : ℝ≥0∞ := ∑' n : ℕ, farTerm n

private lemma far_integral_le_shell_sum {R : ℝ} (hR : 0 < R)
    {f : Vec3 → ℝ} (_hf : AEMeasurable f volume) (z : Vec3) :
    (∫⁻ w in {w | R ≤ dist z w},
      rieszKernelOne z w * ENNReal.ofReal |f w|) ≤
      ∑' n : ℕ, ∫⁻ w in farShell R n z,
        rieszKernelOne z w * ENNReal.ofReal |f w| := by
  let s : ℕ → Set Vec3 := fun n ↦ farShell R n z
  have hs : ∀ n, MeasurableSet (s n) := by
    intro n
    simpa [s] using farShell_measurable R n z
  have hspair : Pairwise (Function.onFun Disjoint s) := by
    simpa [s] using farShell_pairwise hR z
  have hunion :
      ∫⁻ w in ⋃ n, s n,
          rieszKernelOne z w * ENNReal.ofReal |f w| =
        ∑' n, ∫⁻ w in s n,
          rieszKernelOne z w * ENNReal.ofReal |f w| :=
    lintegral_iUnion hs hspair _
  have hcover : {w | R ≤ dist z w} ⊆ ⋃ n, s n := by
    simpa [s] using farShell_cover hR
  calc
    (∫⁻ w in {w | R ≤ dist z w},
        rieszKernelOne z w * ENNReal.ofReal |f w|) ≤
        ∫⁻ w in ⋃ n, s n,
          rieszKernelOne z w * ENNReal.ofReal |f w| :=
      lintegral_mono_set hcover
    _ = ∑' n, ∫⁻ w in s n,
          rieszKernelOne z w * ENNReal.ofReal |f w| := hunion
    _ = ∑' n, ∫⁻ w in farShell R n z,
          rieszKernelOne z w * ENNReal.ofReal |f w| := by rfl

theorem rieszPotentialOne_far_le
    {R : ℝ} (hR : 0 < R) {f : Vec3 → ℝ}
    (hf : AEMeasurable f volume) (z : Vec3) :
    (∫⁻ w in {w | R ≤ dist z w},
      rieszKernelOne z w * ENNReal.ofReal |f w|) ≤
      hedbergFarConstant * (ENNReal.ofReal R) ^ (-(1 / 5 : ℝ)) *
        (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
  let B : ℝ≥0∞ :=
    (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ)
  have hsum := far_integral_le_shell_sum hR hf z
  have hterm : ∀ n : ℕ,
      (∫⁻ w in farShell R n z,
          rieszKernelOne z w * ENNReal.ofReal |f w|) ≤
        farTerm n * (ENNReal.ofReal R) ^ (-(1 / 5 : ℝ)) * B := by
    intro n
    have hs := far_shell_integral_le hR hf n z
    calc
      (∫⁻ w in farShell R n z,
          rieszKernelOne z w * ENNReal.ofReal |f w|) ≤
          ((ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ) * R)) ^ (-(10 / 3 : ℝ)) *
            ENNReal.ofReal ((2 * ((2 : ℝ) ^ ((n : ℝ) + 1) * R)) ^ 3)) ^
              (3 / 5 : ℝ) * B := by simpa [B] using hs
      _ = farTerm n * (ENNReal.ofReal R) ^ (-(1 / 5 : ℝ)) * B := by
        rw [far_shell_scale_identity hR n]
  calc
    (∫⁻ w in {w | R ≤ dist z w},
        rieszKernelOne z w * ENNReal.ofReal |f w|) ≤
        ∑' n, ∫⁻ w in farShell R n z,
          rieszKernelOne z w * ENNReal.ofReal |f w| := hsum
    _ ≤ ∑' n, farTerm n * (ENNReal.ofReal R) ^ (-(1 / 5 : ℝ)) * B :=
      ENNReal.tsum_le_tsum hterm
    _ = hedbergFarConstant * (ENNReal.ofReal R) ^ (-(1 / 5 : ℝ)) * B := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
      rfl
    _ = hedbergFarConstant * (ENNReal.ofReal R) ^ (-(1 / 5 : ℝ)) *
        (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
      rfl

theorem rieszPotentialOne_scale_le
    {R : ℝ} (hR : 0 < R) {f : Vec3 → ℝ}
    (hf : AEMeasurable f volume) {M : Vec3 → ℝ≥0∞}
    (hM : IsMaximalMajorant f M) (z : Vec3) :
    rieszPotentialOne f z ≤
      hedbergNearConstant * ENNReal.ofReal R * M z +
        hedbergFarConstant * (ENNReal.ofReal R) ^ (-(1 / 5 : ℝ)) *
          (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
  let s : Set Vec3 := {w | dist z w < R}
  let t : Set Vec3 := {w | R ≤ dist z w}
  have hs : MeasurableSet s := by
    have hdist : Measurable (fun w : Vec3 => dist z w) :=
      measurable_dist.comp (measurable_const.prodMk measurable_id)
    exact hdist measurableSet_Iio
  have ht : MeasurableSet t := by
    have hdist : Measurable (fun w : Vec3 => dist z w) :=
      measurable_dist.comp (measurable_const.prodMk measurable_id)
    exact hdist measurableSet_Ici
  have hdisj : Disjoint s t := by
    rw [Set.disjoint_left]
    intro w hws hwt
    change dist z w < R at hws
    change R ≤ dist z w at hwt
    exact (not_lt_of_ge hwt) hws
  have hunion : s ∪ t = Set.univ := by
    ext w
    change (dist z w < R ∨ R ≤ dist z w) ↔ True
    simp only [iff_true]
    exact lt_or_ge (dist z w) R
  calc
    rieszPotentialOne f z = ∫⁻ w in Set.univ,
        rieszKernelOne z w * ENNReal.ofReal |f w| := by
      simp [rieszPotentialOne]
    _ = ∫⁻ w in s ∪ t,
        rieszKernelOne z w * ENNReal.ofReal |f w| := by rw [hunion]
    _ = (∫⁻ w in s, rieszKernelOne z w * ENNReal.ofReal |f w|) +
        ∫⁻ w in t, rieszKernelOne z w * ENNReal.ofReal |f w| :=
      lintegral_union ht hdisj
    _ ≤ hedbergNearConstant * ENNReal.ofReal R * M z +
        hedbergFarConstant * (ENNReal.ofReal R) ^ (-(1 / 5 : ℝ)) *
          (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
      exact add_le_add
        (rieszPotentialOne_near_le hR hf hM z)
        (rieszPotentialOne_far_le hR hf z)

theorem rieszPotentialOne_hedberg
    {f : Vec3 → ℝ} (hf : AEMeasurable f volume)
    {M : Vec3 → ℝ≥0∞} (hM : IsMaximalMajorant f M) (z : Vec3)
    (hM0 : M z ≠ 0) (hMtop : M z ≠ ∞)
    (hB0 : (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) ≠ 0)
    (hBtop : (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) ≠ ∞) :
    rieszPotentialOne f z ≤
      (hedbergNearConstant + hedbergFarConstant) *
        M z ^ (1 / 6 : ℝ) *
        (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (1 / 3 : ℝ) := by
  let B : ℝ≥0∞ :=
    (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ)
  have hB0' : B ≠ 0 := hB0
  have hBtop' : B ≠ ∞ := hBtop
  have hmpos : 0 < (M z).toReal := ENNReal.toReal_pos hM0 hMtop
  have hbpos : 0 < B.toReal := ENNReal.toReal_pos hB0' hBtop'
  let R : ℝ := (B.toReal / (M z).toReal) ^ (5 / 6 : ℝ)
  have hR : 0 < R := by
    dsimp [R]
    exact Real.rpow_pos_of_pos (div_pos hbpos hmpos) _
  have hbalance : (ENNReal.ofReal R) ^ (6 / 5 : ℝ) * M z = B := by
    have hratio : 0 ≤ B.toReal / (M z).toReal :=
      (div_nonneg hbpos.le hmpos.le)
    have hratioE : ENNReal.ofReal (B.toReal / (M z).toReal) = B / M z := by
      rw [ENNReal.ofReal_div_of_pos hmpos,
        ENNReal.ofReal_toReal hBtop', ENNReal.ofReal_toReal hMtop]
    have hpow : ENNReal.ofReal R =
        (ENNReal.ofReal (B.toReal / (M z).toReal)) ^ (5 / 6 : ℝ) := by
      dsimp [R]
      exact (ENNReal.ofReal_rpow_of_nonneg hratio (by norm_num)).symm
    rw [hpow, ← ENNReal.rpow_mul]
    have hexp : (5 / 6 : ℝ) * (6 / 5 : ℝ) = 1 := by norm_num
    rw [hexp, ENNReal.rpow_one, hratioE]
    exact ENNReal.div_mul_cancel hM0 hMtop
  have hscale := rieszPotentialOne_scale_le hR hf hM z
  rw [← show B = (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) by rfl]
    at hscale
  have hX0 : ENNReal.ofReal R ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hR).ne'
  have hXtop : ENNReal.ofReal R ≠ ∞ := ENNReal.ofReal_ne_top
  have hMpow : (M z) ^ (1 / 6 : ℝ) * B ^ (5 / 6 : ℝ) =
      ENNReal.ofReal R * M z := by
    rw [← hbalance]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    rw [← ENNReal.rpow_mul]
    norm_num
    calc
      M z ^ (1 / 6 : ℝ) *
          (ENNReal.ofReal R * M z ^ (5 / 6 : ℝ)) =
          ENNReal.ofReal R * (M z ^ (1 / 6 : ℝ) * M z ^ (5 / 6 : ℝ)) := by
        ac_rfl
      _ = ENNReal.ofReal R * M z := by
        rw [← ENNReal.rpow_add _ _ hM0 hMtop]
        norm_num
  have hfarcollapse :
      (ENNReal.ofReal R) ^ (-(1 / 5 : ℝ)) * B =
        ENNReal.ofReal R * M z := by
    rw [← hbalance]
    calc
      (ENNReal.ofReal R) ^ (-(1 / 5 : ℝ)) *
          ((ENNReal.ofReal R) ^ (6 / 5 : ℝ) * M z) =
          ((ENNReal.ofReal R) ^ (-(1 / 5 : ℝ)) *
            (ENNReal.ofReal R) ^ (6 / 5 : ℝ)) * M z := by ac_rfl
      _ = ENNReal.ofReal R * M z := by
        rw [← ENNReal.rpow_add _ _ hX0 hXtop]
        congr 1
        norm_num
  calc
    rieszPotentialOne f z ≤
        hedbergNearConstant * ENNReal.ofReal R * M z +
          hedbergFarConstant *
            ((ENNReal.ofReal R) ^ (-(1 / 5 : ℝ)) * B) := by
      simpa [B, mul_assoc] using hscale
    _ = (hedbergNearConstant + hedbergFarConstant) *
        (ENNReal.ofReal R * M z) := by
      rw [hfarcollapse]
      rw [add_mul]
      ac_rfl
    _ = (hedbergNearConstant + hedbergFarConstant) *
        M z ^ (1 / 6 : ℝ) * B ^ (5 / 6 : ℝ) := by
      calc
        (hedbergNearConstant + hedbergFarConstant) *
              (ENNReal.ofReal R * M z) =
            (hedbergNearConstant + hedbergFarConstant) *
              (M z ^ (1 / 6 : ℝ) * B ^ (5 / 6 : ℝ)) := by
          rw [hMpow]
        _ = (hedbergNearConstant + hedbergFarConstant) *
              M z ^ (1 / 6 : ℝ) * B ^ (5 / 6 : ℝ) := by
          rw [mul_assoc]
    _ = _ := by
      dsimp [B]
      rw [← ENNReal.rpow_mul]
      congr 1
      norm_num

end CKN.Foundation.Euclidean
