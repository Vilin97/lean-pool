/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Maximal.StrongType
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Hedberg
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Inclusions
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Kernel

/-!
# Hedberg and Adams estimates

This module connects the parabolic Riesz potential with the exported maximal
function estimates and the cylinder Morrey seminorm.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology


noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The maximal function applied to the absolute value of a real function. -/
def parabolicMaximalMajorant (f : ParabolicPoint → ℝ) : ParabolicPoint → ℝ≥0∞ :=
  parabolicMaximalFunction (fun w ↦ ENNReal.ofReal |f w|)

/-- The maximal majorant property of the exported parabolic maximal function. -/
theorem isParabolicMaximalMajorant_parabolicMaximalMajorant
    (f : ParabolicPoint → ℝ) :
    IsParabolicMaximalMajorant f (parabolicMaximalMajorant f) := by
  intro z R hR
  have haverage := parabolicMaximalFunction_average_le
    (f := fun w ↦ ENNReal.ofReal |f w|) (c := z) (z := z) (r := R)
    (Metric.mem_ball_self hR)
  rw [setLAverage_eq] at haverage
  exact (ENNReal.div_le_iff (volume_parabolicBall_pos hR).ne'
    (volume_parabolicBall_lt_top hR).ne).mp haverage

private lemma volume_metricBall_le {z : ParabolicPoint} {R : ℝ} (hR : 0 < R) :
    volume (Metric.ball z R) ≤
      ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (R ^ 5) *
        volume (parabolicCylinder 0 0 1) := by
  let T : ℝ := z.2 + (2 * R) ^ 2 / 2
  have hball := metricBall_subset_parabolicCylinder (x := z.1) (t := T)
    (r := 2 * R) (by positivity)
  have hcenter : (z.1, T - (2 * R) ^ 2 / 2) = z := by
    dsimp [T]
    congr 1
    ring_nf
  have hradius : (2 * R) / 2 = R := by ring_nf
  rw [hcenter, hradius] at hball
  have hscale := volume_parabolicCylinder_radius_scale
    (x := z.1) (t := T) (r := 1) (a := 2 * R) (by positivity)
  have hunit : volume (parabolicCylinder z.1 T 1) =
      volume (parabolicCylinder 0 0 1) := by
    rw [volume_parabolicCylinder_zero, volume_parabolicCylinder_zero]
  calc
    volume (Metric.ball z R) ≤ volume (parabolicCylinder z.1 T (2 * R)) :=
      measure_mono hball
    _ = ENNReal.ofReal ((2 * R) ^ 5) * volume (parabolicCylinder z.1 T 1) := by
      simpa using hscale
    _ = ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (R ^ 5) *
        volume (parabolicCylinder 0 0 1) := by
      rw [hunit, show (2 * R) ^ 5 = 2 ^ 5 * R ^ 5 by ring_nf,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 5),
        ENNReal.ofReal_pow (by positivity : 0 ≤ R) 5]

def nearShell (R : ℝ) (n : ℕ) (z : ParabolicPoint) : Set ParabolicPoint :=
  parabolicRieszShell R (Int.negSucc n) z

private lemma nearShell_measurable (R : ℝ) (n : ℕ) (z : ParabolicPoint) :
    MeasurableSet (nearShell R n z) := by
  exact measurableSet_parabolicRieszShell R (Int.negSucc n) z

private lemma nearShell_pairwise {R : ℝ} (hR : 0 < R) (z : ParabolicPoint) :
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

private lemma zero_set_volume (z : ParabolicPoint) :
    volume ({w | parabolicRho₂ z w = 0} : Set ParabolicPoint) = 0 := by
  apply measure_mono_null (parabolicRho₂_zero_subset_singleton z)
  rcases z with ⟨x, t⟩
  change (volume : Measure (Vec3 × ℝ)) ({(x, t)} : Set (Vec3 × ℝ)) = 0
  have hset : ({(x, t)} : Set (Vec3 × ℝ)) = {x} ×ˢ {t} := by
    ext p
    rcases p with ⟨y, s⟩
    simp only [mem_singleton_iff]
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · rintro ⟨hy, hs⟩
      exact Prod.ext hy hs
  rw [hset]
  change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
    ({x} ×ˢ {t}) = 0
  rw [Measure.prod_prod]
  simp

private lemma near_shell_cover {z : ParabolicPoint} {R : ℝ} (hR : 0 < R) :
    {w | parabolicRho₂ z w < R} ⊆
      {w | parabolicRho₂ z w = 0} ∪ ⋃ n : ℕ, nearShell R n z := by
  intro w hw
  by_cases hzero : parabolicRho₂ z w = 0
  · exact Or.inl hzero
  · have hpos : 0 < parabolicRho₂ z w :=
      lt_of_le_of_ne (parabolicRho₂_nonneg z w) (Ne.symm hzero)
    obtain ⟨k, hk, hmem⟩ := by
      exact exists_shell_of_pos_lt hR hpos hw
    obtain ⟨n, hn⟩ := Int.eq_negSucc_of_lt_zero hk
    subst k
    exact Or.inr (mem_iUnion.mpr ⟨n, hmem⟩)

private lemma near_shell_integral_le
    {β q : ℝ} (hβ : 0 < β) (hβ5 : β < 5) (_ : 1 ≤ q)
    (_ : β * q < 5) {R : ℝ} (hR : 0 < R)
    {f : ParabolicPoint → ℝ} {M : ParabolicPoint → ℝ≥0∞}
    (hf : AEMeasurable f volume) (hM : IsParabolicMaximalMajorant f M)
    (n : ℕ) (z : ParabolicPoint) :
    (∫⁻ w in nearShell R n z,
      parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
      (ENNReal.ofReal (2 ^ 5) *
        (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
        (ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) *
          ENNReal.ofReal (R ^ β)) * M z := by
  let a : ℝ := (2 : ℝ) ^ (Int.negSucc n : ℝ) * R
  let b : ℝ := (2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) * R
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hkernel : ∀ w ∈ nearShell R n z,
      parabolicRieszKernel β z w ≤ (ENNReal.ofReal a) ^ (-(5 - β)) := by
    intro w hw
    have hinner : a ≤ parabolicRho₂ z w := by
      simpa [a, nearShell] using hw.1
    rw [parabolicRieszKernel, ENNReal.rpow_neg, ENNReal.rpow_neg,
      ENNReal.inv_le_inv]
    apply ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hinner)
    exact sub_nonneg.mpr hβ5.le
  have hsubset : nearShell R n z ⊆ Metric.ball z b := by
    intro w hw
    apply parabolicRho₂_lt_subset_metricBall
    simpa [b, nearShell] using hw.2
  have hball :
      (∫⁻ w in nearShell R n z, ENNReal.ofReal |f w|) ≤
        M z * volume (Metric.ball z b) := by
    calc
      (∫⁻ w in nearShell R n z, ENNReal.ofReal |f w|) ≤
          ∫⁻ w in Metric.ball z b, ENNReal.ofReal |f w| :=
        lintegral_mono_set hsubset
      _ ≤ M z * volume (Metric.ball z b) := hM z b hb
  have hball' :
      (∫⁻ w in nearShell R n z, ENNReal.ofReal |f w|) ≤
        M z * (ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (b ^ 5) *
          volume (parabolicCylinder 0 0 1)) :=
    hball.trans (by
      simpa [mul_comm] using (mul_le_mul_left (volume_metricBall_le hb) (M z)))
  have hprod :
      (∫⁻ w in nearShell R n z,
        parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
        (ENNReal.ofReal a) ^ (-(5 - β)) *
          (∫⁻ w in nearShell R n z, ENNReal.ofReal |f w|) := by
    calc
      (∫⁻ w in nearShell R n z,
          parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
          ∫⁻ w in nearShell R n z,
            (ENNReal.ofReal a) ^ (-(5 - β)) * ENNReal.ofReal |f w| := by
        apply setLIntegral_mono_ae
          ((hf.norm.ennreal_ofReal.restrict).const_mul
            ((ENNReal.ofReal a) ^ (-(5 - β))))
        filter_upwards [] with w hw
        simpa only [Real.norm_eq_abs] using
          (mul_le_mul (hkernel w hw) (le_refl _) (by positivity) (by positivity))
      _ = (ENNReal.ofReal a) ^ (-(5 - β)) *
          (∫⁻ w in nearShell R n z, ENNReal.ofReal |f w|) := by
        rw [lintegral_const_mul' _ _ (by
          rw [ENNReal.rpow_neg]
          exact ENNReal.inv_ne_top.mpr
            (ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr ha)
              ENNReal.ofReal_ne_top)))]
  calc
    (∫⁻ w in nearShell R n z,
        parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
        (ENNReal.ofReal a) ^ (-(5 - β)) *
          (M z * (ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (b ^ 5) *
            volume (parabolicCylinder 0 0 1))) :=
      hprod.trans (by
        simpa [mul_comm] using
          (mul_le_mul_right hball' ((ENNReal.ofReal a) ^ (-(5 - β)))))
    _ = (ENNReal.ofReal (2 ^ 5) *
        (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
        (ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) *
          ENNReal.ofReal (R ^ β)) * M z := by
      have hba : b = 2 * a := by
        dsimp [a, b]
        rw [Real.rpow_add (by positivity)]
        ring_nf
      have hscale :
          (ENNReal.ofReal a) ^ (-(5 - β)) * ENNReal.ofReal (b ^ 5) =
            ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (a ^ β) := by
        rw [hba]
        exact shell_power_identity ha hβ.le hβ5.le
      calc
        (ENNReal.ofReal a) ^ (-(5 - β)) *
            (M z * (ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (b ^ 5) *
              volume (parabolicCylinder 0 0 1))) =
            M z * ((ENNReal.ofReal a) ^ (-(5 - β)) *
              ENNReal.ofReal (b ^ 5)) *
              (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1)) := by
                ac_rfl
        _ = M z * (ENNReal.ofReal (2 ^ 5) * ENNReal.ofReal (a ^ β)) *
              (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1)) := by
                rw [hscale]
        _ = (ENNReal.ofReal (2 ^ 5) *
            (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
            (ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) *
              ENNReal.ofReal (R ^ β)) * M z := by
          rw [Real.mul_rpow (by positivity) hR.le,
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤
              ((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)]
          ac_rfl

/-- The geometric constant in the local Hedberg estimate. -/
def parabolicHedbergNearConstant (β : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (2 ^ 5) *
      (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
    ∑' n : ℕ, ENNReal.ofReal
      (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)

/-- The local part of the potential is bounded by the maximal majorant. -/
theorem parabolicRieszPotential_near_le
    {β q : ℝ} (hβ : 0 < β) (hβ5 : β < 5) (hq : 1 ≤ q)
    (hβq : β * q < 5) {R : ℝ} (hR : 0 < R)
    {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    {M : ParabolicPoint → ℝ≥0∞}
    (hM : IsParabolicMaximalMajorant f M) (z : ParabolicPoint) :
    (∫⁻ w in {w | parabolicRho₂ z w < R},
      parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
      parabolicHedbergNearConstant β * ENNReal.ofReal (R ^ β) * M z := by
  let s₀ : Set ParabolicPoint := {w | parabolicRho₂ z w = 0}
  let s : ℕ → Set ParabolicPoint := fun n ↦ nearShell R n z
  let g : ParabolicPoint → ℝ≥0∞ := fun w ↦
    parabolicRieszKernel β z w * ENNReal.ofReal |f w|
  have hs₀ : MeasurableSet s₀ := by
    change MeasurableSet ((fun w : ParabolicPoint => parabolicRho₂ z w) ⁻¹' {0})
    exact (measurable_parabolicRho₂ z) (measurableSet_singleton (0 : ℝ))
  have hs : ∀ n, MeasurableSet (s n) := by
    intro n
    simpa [s] using nearShell_measurable R n z
  have hspair : Pairwise (Function.onFun Disjoint s) := by
    simpa [s] using nearShell_pairwise hR z
  have hzdisj : Disjoint s₀ (⋃ n, s n) := by
    rw [Set.disjoint_iUnion_right]
    intro n
    change Disjoint {w | parabolicRho₂ z w = 0} (nearShell R n z)
    rw [Set.disjoint_left]
    intro w hwzero hwshell
    have hinner : 0 < (2 : ℝ) ^ (Int.negSucc n : ℝ) * R := by
      positivity
    exact (not_lt_of_ge (hwshell.1.trans_eq hwzero)) hinner
  have hzero : volume s₀ = 0 := by
    simpa [s₀] using zero_set_volume z
  have hzero_int : (∫⁻ w in s₀, g w) = 0 := by
    have hrestrict : volume.restrict s₀ = 0 := Measure.restrict_eq_zero.mpr hzero
    rw [show (∫⁻ w in s₀, g w) = ∫⁻ w, g w ∂volume.restrict s₀ by rfl,
      hrestrict, lintegral_zero_measure]
  have hcover : {w | parabolicRho₂ z w < R} ⊆ s₀ ∪ ⋃ n, s n := by
    simpa [s₀, s] using near_shell_cover hR
  have hsum :
      (∫⁻ w in ⋃ n, s n, g w) = ∑' n, ∫⁻ w in s n, g w := by
    exact lintegral_iUnion hs hspair g
  have hterm : ∀ n : ℕ,
      (∫⁻ w in s n, g w) ≤
        (ENNReal.ofReal (2 ^ 5) *
          (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
          (ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) *
            ENNReal.ofReal (R ^ β)) * M z := by
    intro n
    simpa [s, g] using near_shell_integral_le hβ hβ5 hq hβq hR hf hM n z
  calc
    (∫⁻ w in {w | parabolicRho₂ z w < R},
        parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
        ∫⁻ w in s₀ ∪ ⋃ n, s n, g w := by
      exact lintegral_mono_set hcover
    _ = (∫⁻ w in s₀, g w) + ∫⁻ w in ⋃ n, s n, g w :=
      lintegral_union (MeasurableSet.iUnion hs) hzdisj
    _ = ∑' n, ∫⁻ w in s n, g w := by rw [hzero_int, zero_add, hsum]
    _ ≤ ∑' n, ((ENNReal.ofReal (2 ^ 5) *
          (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
          (ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) *
            ENNReal.ofReal (R ^ β)) * M z) := ENNReal.tsum_le_tsum hterm
    _ = parabolicHedbergNearConstant β * ENNReal.ofReal (R ^ β) * M z := by
      rw [ENNReal.tsum_mul_right]
      have hfun : (fun n : ℕ =>
          (ENNReal.ofReal (2 ^ 5) *
            (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
            (ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) *
              ENNReal.ofReal (R ^ β))) =
          (fun n : ℕ =>
            ((ENNReal.ofReal (2 ^ 5) *
              (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) *
              ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)) *
              ENNReal.ofReal (R ^ β)) := by
        funext n
        ac_rfl
      rw [hfun, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
      rfl

/-- The two-scale Hedberg estimate before optimization. -/
theorem parabolicRieszPotential_scale_le
    {β q : ℝ} (hβ : 0 < β) (hβ5 : β < 5) (hq : 1 ≤ q)
    (hβq : β * q < 5) {R : ℝ} (hR : 0 < R)
    {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    {M : ParabolicPoint → ℝ≥0∞}
    (hM : IsParabolicMaximalMajorant f M) (z : ParabolicPoint) :
    parabolicRieszPotential β f z ≤
      parabolicHedbergNearConstant β * ENNReal.ofReal (R ^ β) * M z +
      parabolicTailKernelConstant β q *
        ENNReal.ofReal R ^ (β - 5 / q) * morreyNorm 1 q f := by
  apply parabolicRieszPotential_split_le z
  · exact parabolicRieszPotential_near_le hβ hβ5 hq hβq hR hf hM z
  · exact parabolicRieszKernel_tail_le hβ hβ5 hq hβq hR hf z

/-- Hedberg's pointwise estimate at a scale satisfying the balancing identity. -/
theorem parabolicRieszPotential_hedberg_of_balance
    {β q : ℝ} (hβ : 0 < β) (hβ5 : β < 5) (hq : 1 ≤ q)
    (hβq : β * q < 5) {R : ℝ} (hR : 0 < R)
    {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    {M : ParabolicPoint → ℝ≥0∞}
    (hM : IsParabolicMaximalMajorant f M) {N : ℝ≥0∞}
    (hN : N = morreyNorm 1 q f) (z : ParabolicPoint) (hM0 : M z ≠ 0)
    (hMtop : M z ≠ ∞) (_ : N ≠ 0) (_ : N ≠ ∞)
    (hbalance : ENNReal.ofReal R ^ (5 / q) * M z = N) :
    parabolicRieszPotential β f z ≤
      (parabolicHedbergNearConstant β + parabolicTailKernelConstant β q) *
        M z ^ (1 - β * q / 5) * N ^ (β * q / 5) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let θ : ℝ := β * q / 5
  let lam : ℝ := 1 - θ
  let X : ℝ≥0∞ := ENNReal.ofReal R
  have hX0 : X ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have hXtop : X ≠ ∞ := ENNReal.ofReal_ne_top
  have hXp0 : X ^ (5 / q) ≠ 0 := by
    exact (ENNReal.rpow_pos (lt_of_le_of_ne bot_le (Ne.symm hX0)) hXtop).ne'
  have hXptop : X ^ (5 / q) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    positivity
    exact hXtop
  have hNθ : N ^ θ = X ^ β * (M z) ^ θ := by
    rw [← hbalance, ENNReal.mul_rpow_of_ne_top hXptop hMtop,
      ← ENNReal.rpow_mul]
    congr 1
    dsimp [θ]
    field_simp [hq0.ne']
  have hcollapse : X ^ β * M z = M z ^ lam * N ^ θ := by
    have hpow : M z ^ lam * M z ^ θ = M z := by
      rw [← ENNReal.rpow_add _ _ hM0 hMtop]
      have hsum : lam + θ = 1 := by
        dsimp [lam]
        ring_nf
      rw [hsum, ENNReal.rpow_one]
    calc
      X ^ β * M z = X ^ β * (M z ^ lam * M z ^ θ) :=
        congrArg (fun u ↦ X ^ β * u) hpow.symm
      _ = M z ^ lam * (X ^ β * M z ^ θ) := by ac_rfl
      _ = M z ^ lam * N ^ θ :=
        (congrArg (fun u ↦ M z ^ lam * u) hNθ).symm
  have htailcollapse : X ^ (β - 5 / q) * N = X ^ β * M z := by
    have hbalanceX : X ^ (5 / q) * M z = N := by
      simpa [X] using hbalance
    rw [← hbalanceX]
    calc
      X ^ (β - 5 / q) * (X ^ (5 / q) * M z) =
          (X ^ (β - 5 / q) * X ^ (5 / q)) * M z := by ac_rfl
      _ = X ^ β * M z := by
        rw [← ENNReal.rpow_add _ _ hX0 hXtop]
        congr 1
        ring_nf
  have hscale := parabolicRieszPotential_scale_le hβ hβ5 hq hβq hR hf hM z
  rw [← hN] at hscale
  change parabolicRieszPotential β f z ≤ _ at hscale
  have hnear : ENNReal.ofReal (R ^ β) * M z = X ^ β * M z := by
    rw [show ENNReal.ofReal (R ^ β) = X ^ β by
      dsimp [X]
      exact (ENNReal.ofReal_rpow_of_nonneg hR.le hβ.le).symm]
  have hfar : ENNReal.ofReal R ^ (β - 5 / q) * N =
      X ^ (β - 5 / q) * N := by rfl
  calc
    parabolicRieszPotential β f z ≤
        parabolicHedbergNearConstant β *
            (ENNReal.ofReal (R ^ β) * M z) +
          parabolicTailKernelConstant β q *
            (ENNReal.ofReal R ^ (β - 5 / q) * N) := by
      simpa only [mul_assoc] using hscale
    _ = parabolicHedbergNearConstant β *
            (X ^ β * M z) +
          parabolicTailKernelConstant β q *
            (X ^ (β - 5 / q) * N) := by
      rw [hnear, hfar]
    _ = parabolicHedbergNearConstant β *
            (M z ^ lam * N ^ θ) +
          parabolicTailKernelConstant β q *
            (M z ^ lam * N ^ θ) := by
      rw [htailcollapse, hcollapse]
    _ = parabolicHedbergNearConstant β *
            (M z ^ lam * N ^ θ) +
          parabolicTailKernelConstant β q *
            (M z ^ lam * N ^ θ) := by rfl
    _ = (parabolicHedbergNearConstant β + parabolicTailKernelConstant β q) *
        M z ^ (1 - β * q / 5) * N ^ (β * q / 5) := by
      dsimp [lam, θ]
      ring_nf

/-- Hedberg's pointwise estimate for positive finite maximal and Morrey data. -/
theorem parabolicRieszPotential_hedberg
    {β q : ℝ} (hβ : 0 < β) (hβ5 : β < 5) (hq : 1 ≤ q)
    (hβq : β * q < 5) {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) {M : ParabolicPoint → ℝ≥0∞}
    (hM : IsParabolicMaximalMajorant f M) (z : ParabolicPoint)
    (hM0 : M z ≠ 0) (hMtop : M z ≠ ∞)
    (hN : morreyNorm 1 q f ≠ 0) (hNtop : morreyNorm 1 q f ≠ ∞) :
    parabolicRieszPotential β f z ≤
      (parabolicHedbergNearConstant β + parabolicTailKernelConstant β q) *
        M z ^ (1 - β * q / 5) * (morreyNorm 1 q f) ^ (β * q / 5) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmpos : 0 < (M z).toReal := ENNReal.toReal_pos hM0 hMtop
  have hnpos : 0 < (morreyNorm 1 q f).toReal :=
    ENNReal.toReal_pos hN hNtop
  let R : ℝ :=
    ((morreyNorm 1 q f).toReal / (M z).toReal) ^ (q / 5)
  have hR : 0 < R := by
    dsimp [R]
    exact Real.rpow_pos_of_pos (div_pos hnpos hmpos) _
  have hbalance : ENNReal.ofReal R ^ (5 / q) * M z = morreyNorm 1 q f := by
    have hratio : 0 ≤ (morreyNorm 1 q f).toReal / (M z).toReal :=
      (div_nonneg hnpos.le hmpos.le)
    have hratioE : ENNReal.ofReal
        ((morreyNorm 1 q f).toReal / (M z).toReal) =
        morreyNorm 1 q f / M z := by
      rw [ENNReal.ofReal_div_of_pos hmpos,
        ENNReal.ofReal_toReal hNtop, ENNReal.ofReal_toReal hMtop]
    have hpow : ENNReal.ofReal R =
        (ENNReal.ofReal
          ((morreyNorm 1 q f).toReal / (M z).toReal)) ^ (q / 5) := by
      dsimp [R]
      exact (ENNReal.ofReal_rpow_of_nonneg hratio (div_nonneg hq0.le (by norm_num))).symm
    rw [hpow, ← ENNReal.rpow_mul]
    have hexp : q / 5 * (5 / q) = 1 := by
      field_simp [hq0.ne']
    rw [hexp, ENNReal.rpow_one, hratioE]
    exact ENNReal.div_mul_cancel hM0 hMtop
  exact parabolicRieszPotential_hedberg_of_balance hβ hβ5 hq hβq hR hf hM
    rfl z hM0 hMtop hN hNtop hbalance
