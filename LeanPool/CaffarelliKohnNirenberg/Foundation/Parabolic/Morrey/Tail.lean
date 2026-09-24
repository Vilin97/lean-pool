/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Kernel

/-!
# Tail

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology


noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The absolute integral on a positive cylinder is controlled by its Morrey norm. -/
theorem cylinderAbsIntegral_le_morreyNorm {q : ℝ} (hq : 1 ≤ q)
    {f : ParabolicPoint → ℝ} (_ : AEMeasurable f volume)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |f w|) ≤
      (ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) * morreyNorm 1 q f := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hcell : morreyCell 1 q f z r ≤ morreyNorm 1 q f := by
    unfold morreyNorm
    exact le_iSup_of_le z (le_iSup_of_le ⟨r, hr⟩ le_rfl)
  have hcell' : (ENNReal.ofReal r) ^ (-(5 * (1 - 1 / q))) *
      cylinderPowerIntegral 1 f z r ≤ morreyNorm 1 q f := by
    simpa [morreyCell, one_div, hq0.ne'] using hcell
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrtop : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hinv : (ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) *
      (ENNReal.ofReal r) ^ (-(5 * (1 - 1 / q))) = 1 := by
    rw [← ENNReal.rpow_add _ _ hr0 hrtop, add_neg_cancel, ENNReal.rpow_zero]
  calc
    (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |f w|) =
        cylinderPowerIntegral 1 f z r := by
      unfold cylinderPowerIntegral
      apply lintegral_congr
      intro w
      simp
    _ = (ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) *
          ((ENNReal.ofReal r) ^ (-(5 * (1 - 1 / q))) *
            cylinderPowerIntegral 1 f z r) := by
      calc
        cylinderPowerIntegral 1 f z r =
            1 * cylinderPowerIntegral 1 f z r := by rw [one_mul]
        _ = ((ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) *
              (ENNReal.ofReal r) ^ (-(5 * (1 - 1 / q)))) *
            cylinderPowerIntegral 1 f z r := by rw [hinv]
        _ = _ := by ac_rfl
    _ ≤ (ENNReal.ofReal r) ^ (5 * (1 - 1 / q)) * morreyNorm 1 q f :=
      by
        simpa [mul_comm] using
          (mul_le_mul_left hcell' ((ENNReal.ofReal r) ^
            (5 * (1 - 1 / q))))

private lemma positive_shell_cylinder_subset {R : ℝ} (hR : 0 < R)
    (k : ℕ) (z : ParabolicPoint) :
    parabolicRieszShell R (k : ℤ) z ⊆
      parabolicCylinder z.1
        (z.2 + (2 * ((2 : ℝ) ^ ((k : ℝ) + 1) * R)) ^ 2 / 2)
        (2 * ((2 : ℝ) ^ ((k : ℝ) + 1) * R)) := by
  let b : ℝ := (2 : ℝ) ^ ((k : ℝ) + 1) * R
  have hb : 0 < b := by
    dsimp [b]
    positivity
  let T : ℝ := z.2 + (2 * b) ^ 2 / 2
  have hball := metricBall_subset_parabolicCylinder (x := z.1) (t := T)
    (r := 2 * b) (by positivity)
  have hcenter : (z.1, T - (2 * b) ^ 2 / 2) = z := by
    dsimp [T]
    congr 1
    ring
  have hradius : (2 * b) / 2 = b := by ring
  rw [hcenter, hradius] at hball
  have hshell_ball : parabolicRieszShell R (k : ℤ) z ⊆
      @Metric.ball ParabolicPoint parabolicPseudoMetricSpace z b := by
    intro w hw
    exact parabolicRho₂_lt_subset_metricBall hw.2
  have hresult := hshell_ball.trans hball
  simpa [b] using hresult

lemma exists_positive_shell {z w : ParabolicPoint} {R : ℝ}
    (hR : 0 < R) (hRρ : R ≤ parabolicRho₂ z w) :
    ∃ k : ℕ, w ∈ parabolicRieszShell R (k : ℤ) z := by
  let x : ℝ := parabolicRho₂ z w / R
  let L : ℝ := Real.log 2
  let k : ℤ := ⌊Real.log x / L⌋
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact (one_le_div hR).2 hRρ
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
  have hinner : (2 : ℝ) ^ (k : ℝ) * R ≤ parabolicRho₂ z w := by
    simpa [x] using (le_div_iff₀ hR).mp hpowlo
  have houter : parabolicRho₂ z w < (2 : ℝ) ^ ((k : ℝ) + 1) * R := by
    simpa [x] using (div_lt_iff₀ hR).mp hpowhi
  have hmem : w ∈ parabolicRieszShell R k z := mem_parabolicRieszShell hinner houter
  exact ⟨k.toNat, by simpa [Int.toNat_of_nonneg hk] using hmem⟩

/-- Nonnegative-index parabolic shell for the far-field Morrey estimate. -/
def positiveShell (R : ℝ) (n : ℕ) (z : ParabolicPoint) : Set ParabolicPoint :=
  parabolicRieszShell R (n : ℤ) z

private lemma positiveShell_measurable (R : ℝ) (n : ℕ) (z : ParabolicPoint) :
    MeasurableSet (positiveShell R n z) := by
  exact measurableSet_parabolicRieszShell R (n : ℤ) z

private lemma positiveShell_pairwise {R : ℝ} (hR : 0 < R) (z : ParabolicPoint) :
    Pairwise (Function.onFun Disjoint (fun n => positiveShell R n z)) := by
  intro n m hnm
  change Disjoint (positiveShell R n z) (positiveShell R m z)
  rw [Set.disjoint_left]
  intro w hwn hwm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hindex : (n : ℤ) + 1 ≤ (m : ℤ) := by
      exact_mod_cast (Nat.succ_le_of_lt hlt)
    have hexp : ((n : ℝ) + 1) ≤ (m : ℝ) := by
      exact_mod_cast hindex
    have hpow : (2 : ℝ) ^ ((n : ℝ) + 1) ≤ (2 : ℝ) ^ (m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hrad := mul_le_mul_of_nonneg_right hpow hR.le
    exact (not_lt_of_ge (hrad.trans hwm.1)) hwn.2
  · have hindex : (m : ℤ) + 1 ≤ (n : ℤ) := by
      exact_mod_cast (Nat.succ_le_of_lt hgt)
    have hexp : ((m : ℝ) + 1) ≤ (n : ℝ) := by
      exact_mod_cast hindex
    have hpow : (2 : ℝ) ^ ((m : ℝ) + 1) ≤ (2 : ℝ) ^ (n : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hrad := mul_le_mul_of_nonneg_right hpow hR.le
    exact (not_lt_of_ge (hrad.trans hwn.1)) hwm.2

private lemma positive_shell_cover {z : ParabolicPoint} {R : ℝ} (hR : 0 < R) :
    {w | R ≤ parabolicRho₂ z w} ⊆ ⋃ n : ℕ, positiveShell R n z := by
  intro w hw
  obtain ⟨n, hmem⟩ := exists_positive_shell hR hw
  exact mem_iUnion.mpr ⟨n, hmem⟩

private lemma ennreal_mul_rpow {x y : ℝ≥0∞} {e : ℝ} (hx0 : x ≠ 0) (hxtop : x ≠ ∞)
    (_ : y ≠ 0) (_ : y ≠ ∞) :
    (x * y) ^ e = x ^ e * y ^ e := by
  by_cases he : 0 ≤ e
  · exact ENNReal.mul_rpow_of_nonneg x y he
  · have he' : 0 ≤ -e := le_of_lt (neg_pos.mpr (lt_of_not_ge he))
    have heq : e = -(-e) := by ring
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
        exact ENNReal.mul_inv (Or.inl hxr0) (Or.inl hxrtop)
      _ = x ^ e * y ^ e := by rw [hxpow, hypow]

private lemma positive_shell_integral_le {β q : ℝ} (_ : 0 < β)
    (hβ5 : β < 5) (hq : 1 ≤ q) (_ : β * q < 5)
    {R : ℝ} (hR : 0 < R) {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) (n : ℕ) (z : ParabolicPoint) :
    (∫⁻ w in positiveShell R n z,
      parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
      (ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ) * R)) ^ (-(5 - β)) *
        (ENNReal.ofReal (2 * ((2 : ℝ) ^ ((n : ℝ) + 1) * R))) ^
          (5 * (1 - 1 / q)) * morreyNorm 1 q f := by
  let a : ℝ := (2 : ℝ) ^ (n : ℝ) * R
  let b : ℝ := (2 : ℝ) ^ ((n : ℝ) + 1) * R
  let s : Set ParabolicPoint := positiveShell R n z
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hkernel : ∀ w ∈ s,
      parabolicRieszKernel β z w ≤
        (ENNReal.ofReal a) ^ (-(5 - β)) := by
    intro w hw
    have hrho : a ≤ parabolicRho₂ z w := by
      simpa [a, s, positiveShell] using hw.1
    rw [parabolicRieszKernel, ENNReal.rpow_neg, ENNReal.rpow_neg,
      ENNReal.inv_le_inv]
    apply ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hrho)
    exact sub_nonneg.mpr hβ5.le
  have hprod :
      (∫⁻ w in s, parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
        ∫⁻ w in s, (ENNReal.ofReal a) ^ (-(5 - β)) *
          ENNReal.ofReal |f w| := by
    apply setLIntegral_mono_ae
      ((hf.norm.ennreal_ofReal.restrict).const_mul
        ((ENNReal.ofReal a) ^ (-(5 - β))))
    filter_upwards [] with w hw
    simpa [mul_comm] using
      (mul_le_mul_right (hkernel w hw) (ENNReal.ofReal |f w|))
  have hshell_cyl : s ⊆
      parabolicCylinder z.1
        (z.2 + (2 * b) ^ 2 / 2) (2 * b) := by
    simpa [s, b, positiveShell] using positive_shell_cylinder_subset hR n z
  have hF : (∫⁻ w in s, ENNReal.ofReal |f w|) ≤
      (ENNReal.ofReal (2 * b)) ^ (5 * (1 - 1 / q)) * morreyNorm 1 q f := by
    calc
      (∫⁻ w in s, ENNReal.ofReal |f w|) ≤
          ∫⁻ w in parabolicCylinder z.1
            (z.2 + (2 * b) ^ 2 / 2) (2 * b), ENNReal.ofReal |f w| :=
        lintegral_mono_set hshell_cyl
      _ ≤ (ENNReal.ofReal (2 * b)) ^ (5 * (1 - 1 / q)) *
            morreyNorm 1 q f := by
        exact cylinderAbsIntegral_le_morreyNorm hq hf
          (z.1, z.2 + (2 * b) ^ 2 / 2) (by positivity)
  calc
    (∫⁻ w in positiveShell R n z,
        parabolicRieszKernel β z w * ENNReal.ofReal |f w|) =
        ∫⁻ w in s, parabolicRieszKernel β z w * ENNReal.ofReal |f w| := by
      rfl
    _ ≤ ∫⁻ w in s, (ENNReal.ofReal a) ^ (-(5 - β)) *
          ENNReal.ofReal |f w| := hprod
    _ = (ENNReal.ofReal a) ^ (-(5 - β)) *
          (∫⁻ w in s, ENNReal.ofReal |f w|) := by
      have hconst := lintegral_const_mul'' (μ := volume.restrict s)
        ((ENNReal.ofReal a) ^ (-(5 - β)))
        (hf.norm.ennreal_ofReal.restrict)
      change (∫⁻ w, (ENNReal.ofReal a) ^ (-(5 - β)) *
          ENNReal.ofReal |f w| ∂volume.restrict s) =
        (ENNReal.ofReal a) ^ (-(5 - β)) *
          (∫⁻ w, ENNReal.ofReal |f w| ∂volume.restrict s)
      simpa [Real.norm_eq_abs] using hconst
    _ ≤ (ENNReal.ofReal a) ^ (-(5 - β)) *
          ((ENNReal.ofReal (2 * b)) ^ (5 * (1 - 1 / q)) *
            morreyNorm 1 q f) :=
      by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_le_mul_left hF ((ENNReal.ofReal a) ^ (-(5 - β))))
    _ = _ := by
      simp [a, b, mul_assoc]

private lemma positive_shell_scale_identity {β q : ℝ} (hq : 1 ≤ q)
    (_ : β * q < 5) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    (ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ) * R)) ^ (-(5 - β)) *
        (ENNReal.ofReal (2 * ((2 : ℝ) ^ ((n : ℝ) + 1) * R))) ^
          (5 * (1 - 1 / q)) =
      (ENNReal.ofReal (2 : ℝ)) ^
          ((n : ℝ) * (β - 5 / q) + 2 * (5 * (1 - 1 / q))) *
        (ENNReal.ofReal R) ^ (β - 5 / q) := by
  let S : ℝ≥0∞ := ENNReal.ofReal (2 : ℝ)
  let T : ℝ≥0∞ := ENNReal.ofReal R
  let α : ℝ := 5 * (1 - 1 / q)
  let δ : ℝ := β - 5 / q
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hα : 0 ≤ α := by
    dsimp [α]
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr (by
        simpa using (one_div_le_one_div_of_le zero_lt_one hq)))
  have hS0 : S ≠ 0 := by
    dsimp [S]
    exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  have hSTop : S ≠ ∞ := by
    dsimp [S]
    exact ENNReal.ofReal_ne_top
  have hT0 : T ≠ 0 := by
    dsimp [T]
    exact (ENNReal.ofReal_pos.mpr hR).ne'
  have hTTop : T ≠ ∞ := by
    dsimp [T]
    exact ENNReal.ofReal_ne_top
  have hSn0 : S ^ (n : ℝ) ≠ 0 :=
    (ENNReal.rpow_pos (lt_of_le_of_ne bot_le (Ne.symm hS0)) hSTop).ne'
  have hSnTop : S ^ (n : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hSTop
  have hSn2_0 : S ^ ((n : ℝ) + 2) ≠ 0 :=
    (ENNReal.rpow_pos (lt_of_le_of_ne bot_le (Ne.symm hS0)) hSTop).ne'
  have hSn2_Top : S ^ ((n : ℝ) + 2) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hSTop
  have ha : ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ) * R) =
      S ^ (n : ℝ) * T := by
    dsimp [S, T]
    rw [ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  have hbreal : 2 * ((2 : ℝ) ^ ((n : ℝ) + 1) * R) =
      (2 : ℝ) ^ ((n : ℝ) + 2) * R := by
    calc
      2 * ((2 : ℝ) ^ ((n : ℝ) + 1) * R) =
          (2 * (2 : ℝ) ^ ((n : ℝ) + 1)) * R := by ring
      _ = ((2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ ((n : ℝ) + 1)) * R := by
        norm_num
      _ = (2 : ℝ) ^ (1 + ((n : ℝ) + 1)) * R := by
        rw [Real.rpow_add (x := (2 : ℝ)) (by positivity) 1 ((n : ℝ) + 1)]
      _ = (2 : ℝ) ^ ((n : ℝ) + 2) * R := by
        congr 2
        ring
  have hb : ENNReal.ofReal (2 * ((2 : ℝ) ^ ((n : ℝ) + 1) * R)) =
      S ^ ((n : ℝ) + 2) * T := by
    rw [hbreal, ENNReal.ofReal_mul (by positivity)]
    dsimp [S, T]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  have hfirst := ennreal_mul_rpow hSn0 hSnTop hT0 hTTop
    (e := -(5 - β))
  have hsecond := ennreal_mul_rpow hSn2_0 hSn2_Top hT0 hTTop (e := α)
  rw [ha, hb, hfirst, hsecond]
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  calc
    S ^ ((n : ℝ) * -(5 - β)) * T ^ (-(5 - β)) *
          (S ^ (((n : ℝ) + 2) * α) * T ^ α) =
        (S ^ ((n : ℝ) * -(5 - β)) *
            S ^ (((n : ℝ) + 2) * α)) *
          (T ^ (-(5 - β)) * T ^ α) := by ac_rfl
    _ = S ^ ((n : ℝ) * -(5 - β) + ((n : ℝ) + 2) * α) *
          T ^ (-(5 - β) + α) := by
      rw [← ENNReal.rpow_add _ _ hS0 hSTop,
        ← ENNReal.rpow_add _ _ hT0 hTTop]
    _ = _ := by
      dsimp [S, T, α, δ]
      congr 2 <;> ring

private lemma tail_integral_le_shell_sum {β : ℝ} {R : ℝ} (hR : 0 < R)
    {f : ParabolicPoint → ℝ} (_ : AEMeasurable f volume) (z : ParabolicPoint) :
    (∫⁻ w in {w | R ≤ parabolicRho₂ z w},
      parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
      ∑' n : ℕ, ∫⁻ w in positiveShell R n z,
        parabolicRieszKernel β z w * ENNReal.ofReal |f w| := by
  let s : ℕ → Set ParabolicPoint := fun n => positiveShell R n z
  have hs : ∀ n, MeasurableSet (s n) := by
    intro n
    simpa [s] using positiveShell_measurable R n z
  have hspair : Pairwise (Function.onFun Disjoint s) := by
    simpa [s] using positiveShell_pairwise hR z
  have hunion :
      ∫⁻ w in ⋃ n, s n,
          parabolicRieszKernel β z w * ENNReal.ofReal |f w| =
        ∑' n, ∫⁻ w in s n,
          parabolicRieszKernel β z w * ENNReal.ofReal |f w| :=
    lintegral_iUnion hs hspair _
  have hcover : {w | R ≤ parabolicRho₂ z w} ⊆ ⋃ n, s n := by
    simpa [s] using positive_shell_cover hR
  calc
    (∫⁻ w in {w | R ≤ parabolicRho₂ z w},
        parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
        ∫⁻ w in ⋃ n, s n,
          parabolicRieszKernel β z w * ENNReal.ofReal |f w| :=
      lintegral_mono_set hcover
    _ = ∑' n : ℕ, ∫⁻ w in s n,
          parabolicRieszKernel β z w * ENNReal.ofReal |f w| := hunion
    _ = ∑' n : ℕ, ∫⁻ w in positiveShell R n z,
          parabolicRieszKernel β z w * ENNReal.ofReal |f w| := by
      rfl

/-- The dyadic constant used by the Morrey tail estimate. -/
def parabolicTailKernelConstant (β q : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, (ENNReal.ofReal (2 : ℝ)) ^
    ((n : ℝ) * (β - 5 / q) + 2 * (5 * (1 - 1 / q)))

theorem parabolicRieszKernel_tail_le {β q : ℝ} (hβ : 0 < β) (hβ5 : β < 5)
    (hq : 1 ≤ q) (hβq : β * q < 5) {R : ℝ} (hR : 0 < R)
    {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume) (z : ParabolicPoint) :
    (∫⁻ w in {w | R ≤ parabolicRho₂ z w},
      parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
      parabolicTailKernelConstant β q *
        (ENNReal.ofReal R) ^ (β - 5 / q) * morreyNorm 1 q f := by
  let T : ℝ≥0∞ := (ENNReal.ofReal R) ^ (β - 5 / q)
  let N : ℝ≥0∞ := morreyNorm 1 q f
  have hsum := tail_integral_le_shell_sum (β := β) (R := R) hR hf z
  have hterm : ∀ n : ℕ,
      (∫⁻ w in positiveShell R n z,
        parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
        (ENNReal.ofReal (2 : ℝ)) ^
            ((n : ℝ) * (β - 5 / q) + 2 * (5 * (1 - 1 / q))) * T * N := by
    intro n
    have hs := positive_shell_integral_le hβ hβ5 hq hβq hR hf n z
    calc
      (∫⁻ w in positiveShell R n z,
          parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
          (ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ) * R)) ^ (-(5 - β)) *
            (ENNReal.ofReal (2 * ((2 : ℝ) ^ ((n : ℝ) + 1) * R))) ^
              (5 * (1 - 1 / q)) * morreyNorm 1 q f := hs
      _ = (ENNReal.ofReal (2 : ℝ)) ^
            ((n : ℝ) * (β - 5 / q) + 2 * (5 * (1 - 1 / q))) * T * N := by
        rw [positive_shell_scale_identity hq hβq hR n]
  calc
    (∫⁻ w in {w | R ≤ parabolicRho₂ z w},
        parabolicRieszKernel β z w * ENNReal.ofReal |f w|) ≤
        ∑' n : ℕ, ∫⁻ w in positiveShell R n z,
          parabolicRieszKernel β z w * ENNReal.ofReal |f w| := hsum
    _ ≤ ∑' n : ℕ, (ENNReal.ofReal (2 : ℝ)) ^
          ((n : ℝ) * (β - 5 / q) + 2 * (5 * (1 - 1 / q))) * T * N :=
      ENNReal.tsum_le_tsum hterm
    _ = parabolicTailKernelConstant β q * T * N := by
      have hfun : (fun n : ℕ =>
          (ENNReal.ofReal (2 : ℝ)) ^
            ((n : ℝ) * (β - 5 / q) + 2 * (5 * (1 - 1 / q))) * T * N) =
          (fun n : ℕ =>
            ((ENNReal.ofReal (2 : ℝ)) ^
              ((n : ℝ) * (β - 5 / q) + 2 * (5 * (1 - 1 / q)))) * T * N) := by
        funext n
        rfl
      rw [hfun, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
      rfl
    _ = parabolicTailKernelConstant β q *
          (ENNReal.ofReal R) ^ (β - 5 / q) * morreyNorm 1 q f := by
      rfl



end CKN.Foundation.Parabolic.Morrey
