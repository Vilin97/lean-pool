/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.SingletonNull

/-!
# Parabolic Riesz kernels

The definitions in this module use the parabolic gauge appearing in the
potential estimates and expose the dyadic shell geometry used by later
integral estimates.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology


noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The parabolic gauge used by the order-`β` Riesz kernel. -/
def parabolicRho₂ (z w : ParabolicPoint) : ℝ :=
  Real.sqrt |z.2 - w.2| + vec3EuclideanNorm (z.1 - w.1)

/-- The order-`β` parabolic Riesz kernel as an extended nonnegative function. -/
def parabolicRieszKernel (β : ℝ) (z w : ParabolicPoint) : ℝ≥0∞ :=
  (ENNReal.ofReal (parabolicRho₂ z w)) ^ (-(5 - β))

/-- The nonnegative parabolic Riesz potential. -/
def parabolicRieszPotential (β : ℝ) (f : ParabolicPoint → ℝ)
    (z : ParabolicPoint) : ℝ≥0∞ :=
  ∫⁻ w, parabolicRieszKernel β z w * ENNReal.ofReal |f w|

/-- The shell with inner radius `2^k R` and outer radius `2^(k+1) R`. -/
def parabolicRieszShell (R : ℝ) (k : ℤ) (z : ParabolicPoint) : Set ParabolicPoint :=
  {w | (2 : ℝ) ^ (k : ℝ) * R ≤ parabolicRho₂ z w ∧
    parabolicRho₂ z w < (2 : ℝ) ^ ((k : ℝ) + 1) * R}

private lemma continuous_vec3EuclideanNorm_prod :
    Continuous (fun p : Vec3 × ℝ => vec3EuclideanNorm p.1) := by
  rw [show (fun p : Vec3 × ℝ => vec3EuclideanNorm p.1) =
      fun p => ‖WithLp.toLp 2 p.1‖ by
        funext p
        exact vec3EuclideanNorm_eq_l2 _]
  exact continuous_norm.comp ((PiLp.continuous_toLp 2 _).comp continuous_fst)

theorem measurable_parabolicRho₂ (z : ParabolicPoint) :
    Measurable (fun w : ParabolicPoint => parabolicRho₂ z w) := by
  have hnorm : Measurable (fun v : Vec3 => vec3EuclideanNorm v) := by
    rw [show (fun v : Vec3 => vec3EuclideanNorm v) =
        fun v => ‖WithLp.toLp 2 v‖ by
          funext v
          exact vec3EuclideanNorm_eq_l2 _]
    exact (continuous_norm.comp (PiLp.continuous_toLp 2 _)).measurable
  have hspace : Measurable (fun w : ParabolicPoint => z.1 - w.1) := by
    exact measurable_const.sub measurable_fst
  have htime : Measurable (fun w : ParabolicPoint => z.2 - w.2) := by
    exact measurable_const.sub measurable_snd
  have habs : Measurable (fun x : ℝ => |x|) := continuous_abs.measurable
  have hsqrt : Measurable (fun x : ℝ => Real.sqrt |x|) :=
    Real.continuous_sqrt.measurable.comp habs
  unfold parabolicRho₂
  have hsum := (hnorm.comp hspace).add (hsqrt.comp htime)
  change Measurable (fun w : ParabolicPoint =>
    vec3EuclideanNorm (z.1 - w.1) + Real.sqrt |z.2 - w.2|) at hsum
  have hsum' : Measurable (fun w : ParabolicPoint =>
      vec3EuclideanNorm (z.1 - w.1) + Real.sqrt |z.2 - w.2|) := hsum
  simpa only [add_comm] using hsum'

theorem measurableSet_parabolicRieszShell (R : ℝ) (k : ℤ) (z : ParabolicPoint) :
    MeasurableSet (parabolicRieszShell R k z) := by
  have hρ := measurable_parabolicRho₂ z
  unfold parabolicRieszShell
  exact (hρ measurableSet_Ici).inter (hρ measurableSet_Iio)

theorem parabolicRho₂_nonneg (z w : ParabolicPoint) : 0 ≤ parabolicRho₂ z w := by
  unfold parabolicRho₂
  exact add_nonneg (Real.sqrt_nonneg _) (vec3EuclideanNorm_nonneg _)

theorem parabolicDist_le_parabolicRho₂ (z w : ParabolicPoint) :
    parabolicDist z w ≤ parabolicRho₂ z w := by
  unfold parabolicDist parabolicRho₂
  exact max_le (le_add_of_nonneg_left (Real.sqrt_nonneg _))
    (le_add_of_nonneg_right (vec3EuclideanNorm_nonneg _))

theorem parabolicRho₂_lt_subset_metricBall {z : ParabolicPoint} {R : ℝ} :
    {w | parabolicRho₂ z w < R} ⊆
      @Metric.ball ParabolicPoint parabolicPseudoMetricSpace z R := by
  intro w hw
  change dist w z < R
  rw [dist_comm, dist_eq_parabolicDist]
  exact (parabolicDist_le_parabolicRho₂ z w).trans_lt hw

theorem volume_parabolicRho₂_lt_le {z : ParabolicPoint} {R : ℝ} (hR : 0 < R) :
    volume {w | parabolicRho₂ z w < R} ≤
      ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (R ^ 5) *
        volume (parabolicCylinder 0 0 1) := by
  let T : ℝ := z.2 + (2 * R) ^ 2 / 2
  have hball := metricBall_subset_parabolicCylinder (x := z.1) (t := T)
    (r := 2 * R) (by positivity)
  have hcenter : (z.1, T - (2 * R) ^ 2 / 2) = z := by
    dsimp [T]
    congr 1
    ring
  have hradius : (2 * R) / 2 = R := by ring
  rw [hcenter, hradius] at hball
  have hsubset : {w | parabolicRho₂ z w < R} ⊆
      parabolicCylinder z.1 T (2 * R) :=
    (parabolicRho₂_lt_subset_metricBall).trans hball
  have hscale₂ := volume_parabolicCylinder_radius_scale
    (x := z.1) (t := T) (r := R) (a := 2) (by norm_num)
  have hscaleR := volume_parabolicCylinder_radius_scale
    (x := z.1) (t := T) (r := 1) (a := R) hR
  have hscaleR' : volume (parabolicCylinder z.1 T R) =
      ENNReal.ofReal (R ^ 5) * volume (parabolicCylinder z.1 T 1) := by
    simpa using hscaleR
  have hunit : volume (parabolicCylinder z.1 T 1) =
      volume (parabolicCylinder 0 0 1) := by
    rw [volume_parabolicCylinder_zero, volume_parabolicCylinder_zero]
  calc
    volume {w | parabolicRho₂ z w < R} ≤
        volume (parabolicCylinder z.1 T (2 * R)) := measure_mono hsubset
    _ = ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder z.1 T R) := by
      simpa using hscale₂
    _ = ENNReal.ofReal (2 ^ 5) *
          (ENNReal.ofReal (R ^ 5) * volume (parabolicCylinder z.1 T 1)) := by
      rw [hscaleR']
    _ = ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (R ^ 5) *
          volume (parabolicCylinder 0 0 1) := by
      rw [hunit]
      ring

theorem volume_parabolicRieszShell_le {z : ParabolicPoint} {R : ℝ} {k : ℤ}
    (hR : 0 < R) :
    volume (parabolicRieszShell R k z) ≤
      ENNReal.ofReal (2 ^ 5) *
          ENNReal.ofReal (((2 : ℝ) ^ ((k : ℝ) + 1) * R) ^ 5) *
        volume (parabolicCylinder 0 0 1) := by
  have houter : 0 < (2 : ℝ) ^ ((k : ℝ) + 1) * R :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hR
  have hsubset : parabolicRieszShell R k z ⊆
      {w | parabolicRho₂ z w < (2 : ℝ) ^ ((k : ℝ) + 1) * R} := by
    intro w hw
    exact hw.2
  exact (measure_mono hsubset).trans (volume_parabolicRho₂_lt_le houter)

theorem parabolicRieszKernel_nonneg (β : ℝ) (z w : ParabolicPoint) :
    0 ≤ parabolicRieszKernel β z w := by
  exact bot_le

theorem mem_parabolicRieszShell {R : ℝ} {k : ℤ} {z w : ParabolicPoint}
    (hinner : (2 : ℝ) ^ (k : ℝ) * R ≤ parabolicRho₂ z w)
    (houter : parabolicRho₂ z w < (2 : ℝ) ^ ((k : ℝ) + 1) * R) :
    w ∈ parabolicRieszShell R k z := by
  exact ⟨hinner, houter⟩

theorem parabolicRieszShell_subset_tail {R : ℝ} {k : ℤ} {z : ParabolicPoint}
    (hR : 0 < R) (hk : 0 ≤ k) :
    parabolicRieszShell R k z ⊆ {w | R ≤ parabolicRho₂ z w} := by
  intro w hw
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
    apply Real.one_le_rpow (by norm_num)
    exact_mod_cast hk
  calc
    R = 1 * R := by ring
    _ ≤ (2 : ℝ) ^ (k : ℝ) * R := mul_le_mul_of_nonneg_right hpow hR.le
    _ ≤ parabolicRho₂ z w := hw.1

/-- A positive point below a radius belongs to a negative dyadic shell. -/
theorem exists_shell_of_pos_lt {z w : ParabolicPoint} {R : ℝ}
    (hR : 0 < R) (hρ : 0 < parabolicRho₂ z w)
    (hρR : parabolicRho₂ z w < R) :
    ∃ k : ℤ, k < 0 ∧ w ∈ parabolicRieszShell R k z := by
  let x : ℝ := parabolicRho₂ z w / R
  let L : ℝ := Real.log 2
  let k : ℤ := ⌊Real.log x / L⌋
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hx : 0 < x := div_pos hρ hR
  have hx1 : x < 1 := by
    dsimp [x]
    exact (div_lt_one hR).2 hρR
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
      (k : ℝ) * Real.log 2 ≤ (Real.log x / L) * L := by
        exact mul_le_mul_of_nonneg_right hklo hL.le
      _ = Real.log x := by field_simp [hL.ne']
  have hpowhi : x < (2 : ℝ) ^ ((k : ℝ) + 1) := by
    apply (Real.strictMonoOn_log.lt_iff_lt
      hx (Real.rpow_pos_of_pos (by norm_num) _)).mp
    rw [Real.log_rpow (by norm_num)]
    calc
      Real.log x = (Real.log x / L) * L := by field_simp [hL.ne']
      _ < ((k : ℝ) + 1) * L := mul_lt_mul_of_pos_right hkhi hL
  have hinner : (2 : ℝ) ^ (k : ℝ) * R ≤ parabolicRho₂ z w := by
    simpa [x] using (le_div_iff₀ hR).mp hpowlo
  have houter : parabolicRho₂ z w < (2 : ℝ) ^ ((k : ℝ) + 1) * R := by
    simpa [x] using (div_lt_iff₀ hR).mp hpowhi
  exact ⟨k, hkneg, mem_parabolicRieszShell hinner houter⟩

private lemma pairwise_disjoint_parabolicRieszShells {R : ℝ} (hR : 0 < R)
    (z : ParabolicPoint) :
    Pairwise (Function.onFun Disjoint (fun k : {k : ℤ // k < 0} =>
      parabolicRieszShell R k.1 z)) := by
  intro k l hkl
  change Disjoint (parabolicRieszShell R k.1 z) (parabolicRieszShell R l.1 z)
  rw [Set.disjoint_left]
  intro w hwk hwl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hpow : (2 : ℝ) ^ ((k.1 : ℝ) + 1) ≤ (2 : ℝ) ^ (l.1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact_mod_cast (Int.add_one_le_iff.mpr hlt)
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hpow hR.le).trans
      hwl.1)) hwk.2
  · have hpow : (2 : ℝ) ^ ((l.1 : ℝ) + 1) ≤ (2 : ℝ) ^ (k.1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact_mod_cast (Int.add_one_le_iff.mpr hgt)
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hpow hR.le).trans
      hwk.1)) hwl.2

/-- The zero set of the gauge is contained in its center. -/
theorem parabolicRho₂_zero_subset_singleton (z : ParabolicPoint) :
    {w | parabolicRho₂ z w = 0} ⊆ ({z} : Set ParabolicPoint) := by
  intro w hw
  change parabolicRho₂ z w = 0 at hw
  have hspace_nonneg : 0 ≤ vec3EuclideanNorm (z.1 - w.1) :=
    vec3EuclideanNorm_nonneg _
  have htime_nonneg : 0 ≤ Real.sqrt |z.2 - w.2| := Real.sqrt_nonneg _
  have hspace : vec3EuclideanNorm (z.1 - w.1) = 0 := by
    unfold parabolicRho₂ at hw
    nlinarith only [hw, hspace_nonneg, htime_nonneg]
  have htime : Real.sqrt |z.2 - w.2| = 0 := by
    unfold parabolicRho₂ at hw
    nlinarith only [hw, hspace_nonneg, htime_nonneg]
  have hspace_zero : z.1 - w.1 = 0 := by
    rw [vec3EuclideanNorm_eq_l2] at hspace
    exact (WithLp.toLp_eq_zero 2).mp (norm_eq_zero.mp hspace)
  have htime_zero : z.2 - w.2 = 0 := by
    have habs : |z.2 - w.2| = 0 :=
      le_antisymm (Real.sqrt_eq_zero'.mp htime) (abs_nonneg _)
    simpa using abs_eq_zero.mp habs
  have hEq : w = z := Prod.ext (sub_eq_zero.mp hspace_zero).symm
    (sub_eq_zero.mp htime_zero).symm
  exact hEq ▸ mem_singleton z

private lemma local_shell_cover {z : ParabolicPoint} {R : ℝ} (hR : 0 < R) :
    {w | parabolicRho₂ z w < R} ⊆
      {w | parabolicRho₂ z w = 0} ∪
        ⋃ k : {k : ℤ // k < 0}, parabolicRieszShell R k.1 z := by
  intro w hw
  by_cases hzero : parabolicRho₂ z w = 0
  · exact Or.inl hzero
  · have hpos : 0 < parabolicRho₂ z w :=
      lt_of_le_of_ne (parabolicRho₂_nonneg z w) (Ne.symm hzero)
    obtain ⟨k, hk, hmem⟩ := exists_shell_of_pos_lt hR hpos hw
    exact Or.inr (mem_iUnion.mpr ⟨⟨k, hk⟩, hmem⟩)

/-- The kernel-volume scaling identity on a dyadic shell. -/
theorem shell_power_identity {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β)
    (_ : β ≤ 5) :
    (ENNReal.ofReal a) ^ (-(5 - β)) * ENNReal.ofReal ((2 * a) ^ 5) =
      ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (a ^ β) := by
  have hx0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
  have hxtop : ENNReal.ofReal a ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    (ENNReal.ofReal a) ^ (-(5 - β)) * ENNReal.ofReal ((2 * a) ^ 5) =
        (ENNReal.ofReal a) ^ (-(5 - β)) *
          (ENNReal.ofReal 2 * ENNReal.ofReal a) ^ 5 := by
      rw [ENNReal.ofReal_pow (by positivity) 5,
        ENNReal.ofReal_mul (by positivity)]
    _ = (ENNReal.ofReal 2) ^ 5 *
          ((ENNReal.ofReal a) ^ (-(5 - β)) * (ENNReal.ofReal a) ^ 5) := by
      rw [mul_pow]
      ac_rfl
    _ = (ENNReal.ofReal 2) ^ 5 * (ENNReal.ofReal a) ^ β := by
      have hcombine :
          (ENNReal.ofReal a) ^ (-(5 - β)) *
              (ENNReal.ofReal a) ^ (5 : ℝ) =
            (ENNReal.ofReal a) ^ β := by
        rw [← ENNReal.rpow_add _ _ hx0 hxtop]
        congr 1
        ring
      have hnat : (ENNReal.ofReal a) ^ (5 : ℕ) =
          (ENNReal.ofReal a) ^ (5 : ℝ) := ENNReal.rpow_natCast _ _ |>.symm
      rw [hnat, hcombine]
    _ = ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (a ^ β) := by
      rw [← ENNReal.ofReal_pow (by positivity) 5,
        ENNReal.ofReal_rpow_of_nonneg ha.le hβ]

private lemma shell_kernel_integral_le {β : ℝ} (hβ : 0 < β) (hβ5 : β < 5)
    {R : ℝ} (hR : 0 < R) (k : ℤ) (z : ParabolicPoint) :
    (∫⁻ w in parabolicRieszShell R k z,
      parabolicRieszKernel β z w) ≤
      ENNReal.ofReal (2 ^ 5) *
          ENNReal.ofReal (((2 : ℝ) ^ (k : ℝ) * R) ^ β) *
          (ENNReal.ofReal (2 ^ 5) *
        volume (parabolicCylinder 0 0 1)) := by
  let a : ℝ := (2 : ℝ) ^ (k : ℝ) * R
  let b : ℝ := (2 : ℝ) ^ ((k : ℝ) + 1) * R
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hpoint : ∀ w ∈ parabolicRieszShell R k z,
      parabolicRieszKernel β z w ≤
        (ENNReal.ofReal a) ^ (-(5 - β)) := by
    intro w hw
    have hrho : a ≤ parabolicRho₂ z w := hw.1
    rw [parabolicRieszKernel, ENNReal.rpow_neg, ENNReal.rpow_neg,
      ENNReal.inv_le_inv]
    apply ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hrho)
    exact sub_nonneg.mpr hβ5.le
  have hupper :
      (∫⁻ w in parabolicRieszShell R k z,
        parabolicRieszKernel β z w) ≤
      (ENNReal.ofReal a) ^ (-(5 - β)) *
        volume (parabolicRieszShell R k z) := by
    calc
      (∫⁻ w in parabolicRieszShell R k z,
          parabolicRieszKernel β z w) ≤
          ∫⁻ w in parabolicRieszShell R k z,
            (ENNReal.ofReal a) ^ (-(5 - β)) := by
        apply setLIntegral_mono measurable_const
        exact hpoint
      _ = (ENNReal.ofReal a) ^ (-(5 - β)) *
          volume (parabolicRieszShell R k z) := by
        rw [setLIntegral_const]
  calc
    (∫⁻ w in parabolicRieszShell R k z,
        parabolicRieszKernel β z w) ≤
        (ENNReal.ofReal a) ^ (-(5 - β)) *
          (ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (b ^ 5) *
            volume (parabolicCylinder 0 0 1)) := by
      exact hupper.trans (by
        simpa [a, b, mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_left (volume_parabolicRieszShell_le
              (z := z) (R := R) (k := k) hR)
            ((ENNReal.ofReal a) ^ (-(5 - β)))))
    _ = ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (a ^ β) *
          (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1)) := by
      have hbrel : b = 2 * a := by
        dsimp [a, b]
        rw [Real.rpow_add (by positivity)]
        ring
      rw [hbrel]
      calc
        (ENNReal.ofReal a) ^ (-(5 - β)) *
              (ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal ((2 * a) ^ 5) *
                volume (parabolicCylinder 0 0 1)) =
            (ENNReal.ofReal a) ^ (-(5 - β)) *
                ENNReal.ofReal ((2 * a) ^ 5) *
              (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1)) := by
          ac_rfl
        _ = ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (a ^ β) *
              (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1)) := by
          rw [shell_power_identity ha hβ.le hβ5.le]

/-- Dyadic parabolic shell strictly below the reference scale. -/
def negativeShell (R : ℝ) (n : ℕ) (z : ParabolicPoint) : Set ParabolicPoint :=
  parabolicRieszShell R (Int.negSucc n) z

private lemma negativeShell_measurable (R : ℝ) (n : ℕ) (z : ParabolicPoint) :
    MeasurableSet (negativeShell R n z) := by
  exact measurableSet_parabolicRieszShell R (Int.negSucc n) z

private lemma negativeShell_pairwise {R : ℝ} (hR : 0 < R) (z : ParabolicPoint) :
    Pairwise (Function.onFun Disjoint (fun n => negativeShell R n z)) := by
  intro n m hnm
  change Disjoint (negativeShell R n z) (negativeShell R m z)
  rw [Set.disjoint_left]
  intro w hwn hwm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hindex : Int.negSucc m + 1 ≤ Int.negSucc n := by omega
    have hexp : ((Int.negSucc m : ℝ) + 1) ≤ (Int.negSucc n : ℝ) := by
      exact_mod_cast hindex
    have hpow : (2 : ℝ) ^ ((Int.negSucc m : ℝ) + 1) ≤
        (2 : ℝ) ^ (Int.negSucc n : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hrad := mul_le_mul_of_nonneg_right hpow hR.le
    exact (not_lt_of_ge (hrad.trans hwn.1)) hwm.2
  · have hindex : Int.negSucc n + 1 ≤ Int.negSucc m := by omega
    have hexp : ((Int.negSucc n : ℝ) + 1) ≤ (Int.negSucc m : ℝ) := by
      exact_mod_cast hindex
    have hpow : (2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) ≤
        (2 : ℝ) ^ (Int.negSucc m : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hrad := mul_le_mul_of_nonneg_right hpow hR.le
    exact (not_lt_of_ge (hrad.trans hwm.1)) hwn.2

private lemma zeroSet_disjoint_negativeShells {R : ℝ} (hR : 0 < R)
    (z : ParabolicPoint) (n : ℕ) :
    Disjoint {w | parabolicRho₂ z w = 0} (negativeShell R n z) := by
  rw [Set.disjoint_left]
  intro w hwzero hwshell
  have hinner : 0 < (2 : ℝ) ^ (Int.negSucc n : ℝ) * R := by
    positivity
  exact (not_lt_of_ge (hwshell.1.trans_eq hwzero)) hinner

private lemma local_shell_cover_nat {z : ParabolicPoint} {R : ℝ} (hR : 0 < R) :
    {w | parabolicRho₂ z w < R} ⊆
      {w | parabolicRho₂ z w = 0} ∪ ⋃ n : ℕ, negativeShell R n z := by
  intro w hw
  by_cases hzero : parabolicRho₂ z w = 0
  · exact Or.inl hzero
  · have hpos : 0 < parabolicRho₂ z w :=
      lt_of_le_of_ne (parabolicRho₂_nonneg z w) (Ne.symm hzero)
    obtain ⟨k, hk, hmem⟩ := exists_shell_of_pos_lt hR hpos hw
    obtain ⟨n, hn⟩ := Int.eq_negSucc_of_lt_zero hk
    subst k
    exact Or.inr (mem_iUnion.mpr ⟨n, hmem⟩)

private lemma local_kernel_integral_le_shell_sum {β : ℝ} (_ : 0 < β)
    (_ : β < 5) {R : ℝ} (hR : 0 < R) (z : ParabolicPoint) :
    (∫⁻ w in {w | parabolicRho₂ z w < R},
      parabolicRieszKernel β z w) ≤
      ∑' n : ℕ, ∫⁻ w in negativeShell R n z,
        parabolicRieszKernel β z w := by
  let s₀ : Set ParabolicPoint := {w | parabolicRho₂ z w = 0}
  let s : ℕ → Set ParabolicPoint := fun n => negativeShell R n z
  have hs0 : MeasurableSet s₀ := by
    exact (measurable_parabolicRho₂ z) (measurableSet_singleton 0)
  have hs : ∀ n, MeasurableSet (s n) := by
    intro n
    simpa [s] using negativeShell_measurable R n z
  have hspair : Pairwise (Function.onFun Disjoint s) := by
    simpa [s] using negativeShell_pairwise hR z
  have hzero : volume s₀ = 0 := by
    apply measure_mono_null (parabolicRho₂_zero_subset_singleton z)
    exact CKN.Foundation.Parabolic.Integration.volume_singleton_parabolicPoint z
  have hzdisj : Disjoint s₀ (⋃ n, s n) := by
    rw [Set.disjoint_iUnion_right]
    intro n
    simpa [s₀, s] using zeroSet_disjoint_negativeShells hR z n
  have hunion :
      ∫⁻ w in s₀ ∪ ⋃ n, s n, parabolicRieszKernel β z w =
        (∫⁻ w in s₀, parabolicRieszKernel β z w) +
          ∫⁻ w in ⋃ n, s n, parabolicRieszKernel β z w := by
    exact lintegral_union (MeasurableSet.iUnion hs) hzdisj
  have hzero_int : ∫⁻ w in s₀, parabolicRieszKernel β z w = 0 := by
    have hrestrict : volume.restrict s₀ = 0 :=
      Measure.restrict_eq_zero.mpr hzero
    rw [show (∫⁻ w in s₀, parabolicRieszKernel β z w) =
        ∫⁻ w, parabolicRieszKernel β z w ∂volume.restrict s₀ by rfl,
      hrestrict, lintegral_zero_measure]
  have hshells :
      ∫⁻ w in ⋃ n, s n, parabolicRieszKernel β z w =
        ∑' n, ∫⁻ w in s n, parabolicRieszKernel β z w :=
    lintegral_iUnion hs hspair _
  have hcover : {w | parabolicRho₂ z w < R} ⊆ s₀ ∪ ⋃ n, s n := by
    simpa [s₀, s] using local_shell_cover_nat hR
  calc
    (∫⁻ w in {w | parabolicRho₂ z w < R},
        parabolicRieszKernel β z w) ≤
        ∫⁻ w in s₀ ∪ ⋃ n, s n, parabolicRieszKernel β z w :=
      lintegral_mono_set hcover
    _ = (∫⁻ w in s₀, parabolicRieszKernel β z w) +
          ∫⁻ w in ⋃ n, s n, parabolicRieszKernel β z w := hunion
    _ = ∑' n : ℕ, ∫⁻ w in s n, parabolicRieszKernel β z w := by
      rw [hzero_int, zero_add, hshells]
    _ = ∑' n : ℕ, ∫⁻ w in negativeShell R n z,
          parabolicRieszKernel β z w := by
      rfl

/-- The geometric constant used by the local kernel estimate. -/
def parabolicLocalKernelConstant (β : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (2 ^ 5) *
      (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
    ∑' n : ℕ, ENNReal.ofReal
      (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)

theorem parabolicRieszKernel_local_le {β : ℝ} (hβ : 0 < β) (hβ5 : β < 5)
    {R : ℝ} (hR : 0 < R) (z : ParabolicPoint) :
    (∫⁻ w in {w | parabolicRho₂ z w < R},
      parabolicRieszKernel β z w) ≤
      parabolicLocalKernelConstant β * ENNReal.ofReal (R ^ β) := by
  let A : ℝ≥0∞ := ENNReal.ofReal (2 ^ 5) *
      (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))
  let B : ℝ≥0∞ := ENNReal.ofReal (R ^ β)
  have hsum := local_kernel_integral_le_shell_sum hβ hβ5 hR z
  have hterm : ∀ n : ℕ,
      (∫⁻ w in negativeShell R n z, parabolicRieszKernel β z w) ≤
        A * (ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) * B) := by
    intro n
    have hs := shell_kernel_integral_le hβ hβ5 hR (Int.negSucc n) z
    have hbase : 0 ≤ ((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β := by
      positivity
    have hpow : (((2 : ℝ) ^ (Int.negSucc n : ℝ) * R) ^ β) =
        ((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β * R ^ β := by
      rw [Real.mul_rpow (by positivity) hR.le]
    calc
      (∫⁻ w in negativeShell R n z, parabolicRieszKernel β z w) ≤
          ENNReal.ofReal (2 ^ 5) *
            ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ) * R) ^ β) *
              (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1)) := by
        simpa [negativeShell] using hs
      _ = A * (ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) * B) := by
        rw [hpow, ENNReal.ofReal_mul hbase]
        simp [A, B, mul_assoc, mul_left_comm, mul_comm]
  calc
    (∫⁻ w in {w | parabolicRho₂ z w < R},
        parabolicRieszKernel β z w) ≤
        ∑' n : ℕ, ∫⁻ w in negativeShell R n z,
          parabolicRieszKernel β z w := hsum
    _ ≤ ∑' n : ℕ,
          A * (ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) * B) :=
      ENNReal.tsum_le_tsum hterm
    _ = (A * ∑' n : ℕ, ENNReal.ofReal
          (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)) * B := by
      have hfun : (fun n : ℕ => A *
          (ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) * B)) =
          (fun n : ℕ => (A * ENNReal.ofReal
            (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)) * B) := by
        funext n
        ac_rfl
      rw [hfun]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
    _ = parabolicLocalKernelConstant β * ENNReal.ofReal (R ^ β) := by
      rfl

theorem parabolicRieszPotential_mono {β : ℝ} {f g : ParabolicPoint → ℝ}
    (hfg : ∀ w, |f w| ≤ |g w|) (z : ParabolicPoint) :
    parabolicRieszPotential β f z ≤ parabolicRieszPotential β g z := by
  unfold parabolicRieszPotential
  apply lintegral_mono
  intro w
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hfg w)) _

end CKN.Foundation.Parabolic.Morrey
