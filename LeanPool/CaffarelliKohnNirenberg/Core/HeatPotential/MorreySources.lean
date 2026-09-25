/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Near
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsBridge
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Kernel

/-!
# Morrey Sources

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric


noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

private lemma heatPotentialShell_subset_cylinder
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) (k : ℤ) :
    parabolicRieszShell r k z ⊆
      parabolicCylinder z.1
        (z.2 + (2 * ((2 : ℝ) ^ ((k : ℝ) + 1) * r)) ^ 2 / 2)
        (2 * ((2 : ℝ) ^ ((k : ℝ) + 1) * r)) := by
  let b : ℝ := (2 : ℝ) ^ ((k : ℝ) + 1) * r
  have hb : 0 < b := by
    dsimp [b]
    positivity
  let T : ℝ := z.2 + (2 * b) ^ 2 / 2
  have hball := metricBall_subset_parabolicCylinder
    (x := z.1) (t := T) (r := 2 * b) (by positivity)
  have hcenter : (z.1, T - (2 * b) ^ 2 / 2) = z := by
    dsimp [T]
    congr 1
    ring
  have hrad : (2 * b) / 2 = b := by ring
  rw [hcenter, hrad] at hball
  intro w hw
  exact hball (parabolicRho₂_lt_subset_metricBall hw.2)

/- The first-index Morrey norm gives the absolute source mass on every shell. -/
theorem heatPotential_shell_source_l1_bound
    {F : ParabolicPoint → ℝ} {z : ParabolicPoint} {r P θ : ℝ}
    (hr : 0 < r) (hP : 1 ≤ P) (hPθ : P ≤ θ)
    (hF : AEMeasurable F volume) (k : ℤ) :
    (∫⁻ w in parabolicRieszShell r k z, ENNReal.ofReal |F w|) ≤
      (ENNReal.ofReal
          (2 * ((2 : ℝ) ^ ((k : ℝ) + 1) * r))) ^
          (5 * (1 - 1 / θ)) *
        (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
        morreyNorm P θ F := by
  let b : ℝ := (2 : ℝ) ^ ((k : ℝ) + 1) * r
  let c : ParabolicPoint := (z.1, z.2 + (2 * b) ^ 2 / 2)
  have hsubset : parabolicRieszShell r k z ⊆
      parabolicCylinder c.1 c.2 (2 * b) := by
    simpa [c, b] using heatPotentialShell_subset_cylinder hr k
  have hmono :
      (∫⁻ w in parabolicRieszShell r k z, ENNReal.ofReal |F w|) ≤
      ∫⁻ w in parabolicCylinder c.1 c.2 (2 * b),
        ENNReal.ofReal |F w| :=
    lintegral_mono_set hsubset
  have hcy := cylinderAbsIntegral_le_morreyNorm
    (q := θ) (hP.trans hPθ) hF c (r := 2 * b) (by positivity)
  have hlow := morreyNorm_lower_p (p' := 1) (p := P) (q := θ)
    (by norm_num) hP hPθ hF
  have hlow' : morreyNorm 1 θ F ≤
      (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
        morreyNorm P θ F := by
    simpa using hlow
  calc
    (∫⁻ w in parabolicRieszShell r k z, ENNReal.ofReal |F w|) ≤
        (ENNReal.ofReal (2 * b)) ^ (5 * (1 - 1 / θ)) *
          morreyNorm 1 θ F := hmono.trans hcy
    _ ≤ (ENNReal.ofReal (2 * b)) ^ (5 * (1 - 1 / θ)) *
        ((volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
          morreyNorm P θ F) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_left hlow'
          ((ENNReal.ofReal (2 * b)) ^ (5 * (1 - 1 / θ))))
    _ = (ENNReal.ofReal
          (2 * ((2 : ℝ) ^ ((k : ℝ) + 1) * r))) ^
          (5 * (1 - 1 / θ)) *
        (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
        morreyNorm P θ F := by
      simp only [b]
      ac_rfl

theorem heatPotential_near_riesz_shell_term_bound
    {F : ParabolicPoint → ℝ} {z : ParabolicPoint} {r P θ β : ℝ}
    (hr : 0 < r) (hP : 1 ≤ P) (hPθ : P ≤ θ)
    (hβ5 : β < 5) (hF : AEMeasurable F volume)
    (n : ℕ) :
    (∫⁻ w in parabolicRieszShell r (Int.negSucc n) z,
      parabolicRieszKernel β z w * ENNReal.ofReal |F w|) ≤
      (ENNReal.ofReal ((2 : ℝ) ^ (Int.negSucc n : ℝ) * r)) ^
          (-(5 - β)) *
        (ENNReal.ofReal
          (2 * ((2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) * r))) ^
          (5 * (1 - 1 / θ)) *
        (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
        morreyNorm P θ F := by
  let a : ℝ := (2 : ℝ) ^ (Int.negSucc n : ℝ) * r
  let s : Set ParabolicPoint := parabolicRieszShell r (Int.negSucc n) z
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hkernel : ∀ w ∈ s,
      parabolicRieszKernel β z w ≤
        (ENNReal.ofReal a) ^ (-(5 - β)) := by
    intro w hw
    have hinner : a ≤ parabolicRho₂ z w := by
      simpa [a, s] using hw.1
    rw [parabolicRieszKernel, ENNReal.rpow_neg, ENNReal.rpow_neg,
      ENNReal.inv_le_inv]
    apply ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hinner)
    exact sub_nonneg.mpr hβ5.le
  have hprod :
      (∫⁻ w in s,
        parabolicRieszKernel β z w * ENNReal.ofReal |F w|) ≤
      (ENNReal.ofReal a) ^ (-(5 - β)) *
        (∫⁻ w in s, ENNReal.ofReal |F w|) := by
    calc
      (∫⁻ w in s,
          parabolicRieszKernel β z w * ENNReal.ofReal |F w|) ≤
          ∫⁻ w in s,
            (ENNReal.ofReal a) ^ (-(5 - β)) * ENNReal.ofReal |F w| := by
        apply setLIntegral_mono_ae
          ((hF.norm.ennreal_ofReal.restrict).const_mul
            ((ENNReal.ofReal a) ^ (-(5 - β))))
        filter_upwards [] with w hw
        exact mul_le_mul (hkernel w hw) (le_refl _)
          (by positivity) (by positivity)
      _ = (ENNReal.ofReal a) ^ (-(5 - β)) *
          (∫⁻ w in s, ENNReal.ofReal |F w|) := by
        rw [lintegral_const_mul' _ _ (by
          rw [ENNReal.rpow_neg]
          exact ENNReal.inv_ne_top.mpr
            (ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr ha)
              ENNReal.ofReal_ne_top)))]
  have hsource := heatPotential_shell_source_l1_bound
    (z := z) (r := r) hr hP hPθ hF (Int.negSucc n)
  calc
    (∫⁻ w in parabolicRieszShell r (Int.negSucc n) z,
        parabolicRieszKernel β z w * ENNReal.ofReal |F w|) ≤
        (ENNReal.ofReal a) ^ (-(5 - β)) *
          (∫⁻ w in s, ENNReal.ofReal |F w|) := hprod
    _ ≤ (ENNReal.ofReal a) ^ (-(5 - β)) *
        ((ENNReal.ofReal
          (2 * ((2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) * r))) ^
            (5 * (1 - 1 / θ)) *
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
          morreyNorm P θ F) := by
      exact mul_le_mul_of_nonneg_left hsource (by positivity)
    _ = (ENNReal.ofReal ((2 : ℝ) ^ (Int.negSucc n : ℝ) * r)) ^
          (-(5 - β)) *
        (ENNReal.ofReal
          (2 * ((2 : ℝ) ^ ((Int.negSucc n : ℝ) + 1) * r))) ^
          (5 * (1 - 1 / θ)) *
        (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
        morreyNorm P θ F := by
      simp only [a]
      ac_rfl

theorem integrableOn_abs_of_lintegral_lt_top
    {F : ParabolicPoint → ℝ} {S : Set ParabolicPoint}
    (hF : AEMeasurable F volume)
    (hfinite : (∫⁻ w in S, ENNReal.ofReal |F w|) < ∞) :
    IntegrableOn (fun w => |F w|) S volume := by
  have hmeas : AEStronglyMeasurable (fun w => |F w|)
      (volume.restrict S) := hF.norm.aestronglyMeasurable.restrict
  have hnonneg : 0 ≤ᵐ[(volume.restrict S)] (fun w => |F w|) :=
    Filter.Eventually.of_forall (fun w => abs_nonneg (F w))
  have hiff := lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg
  exact hiff.mp (ne_of_lt hfinite)

theorem integrableOn_of_abs_integrable
    {F : ParabolicPoint → ℝ} {S : Set ParabolicPoint}
    (hF : AEMeasurable F volume)
    (hfinite : (∫⁻ w in S, ENNReal.ofReal |F w|) < ∞) :
    IntegrableOn F S volume := by
  have habs := integrableOn_abs_of_lintegral_lt_top hF hfinite
  apply habs.mono'
  · exact hF.aestronglyMeasurable.restrict
  · filter_upwards [] with w
    simp only [Real.norm_eq_abs]
    exact le_rfl




theorem integrableOn_mul_of_abs_integrable_of_bound
    {F K : ParabolicPoint → ℝ} {S : Set ParabolicPoint} {C : ℝ}
    (hS : MeasurableSet S) (hF : AEMeasurable F volume)
    (hK : AEMeasurable K volume)
    (hfinite : (∫⁻ w in S, ENNReal.ofReal |F w|) < ∞)
    (_ : 0 ≤ C)
    (hbound : ∀ w ∈ S, |K w| ≤ C) :
    IntegrableOn (fun w => K w * F w) S volume := by
  have hsource := integrableOn_abs_of_lintegral_lt_top hF hfinite
  have hmajor : IntegrableOn (fun w => C * |F w|) S volume :=
    hsource.const_mul C
  apply hmajor.mono'
  · exact (hK.mul hF).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem hS] with w hw
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hbound w hw) (abs_nonneg _)

theorem real_integral_abs_le_of_lintegral_le
    {F : ParabolicPoint → ℝ} {S : Set ParabolicPoint} {M : ℝ≥0∞}
    (hF : AEMeasurable F volume)
    (hfinite : (∫⁻ w in S, ENNReal.ofReal |F w|) < ∞)
    (hMtop : M ≠ ∞)
    (hM : (∫⁻ w in S, ENNReal.ofReal |F w|) ≤ M) :
    ∫ w in S, |F w| ≤ M.toReal := by
  have hsource := integrableOn_abs_of_lintegral_lt_top hF hfinite
  have hEq : ENNReal.ofReal (∫ w in S, |F w|) =
      ∫⁻ w in S, ENNReal.ofReal |F w| := by
    exact ofReal_integral_eq_lintegral_ofReal hsource
      (Filter.Eventually.of_forall fun w => abs_nonneg (F w))
  have hI : 0 ≤ ∫ w in S, |F w| :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun w => abs_nonneg (F w))
  have hle : (ENNReal.ofReal (∫ w in S, |F w|)).toReal ≤ M.toReal := by
    apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hMtop).mpr
    rw [hEq]
    exact hM
  simpa only [ENNReal.toReal_ofReal hI] using hle



theorem heatPotential_near_shell_geometric_sum
    {A : ℕ → ℝ≥0∞} {C q : ℝ≥0∞}
    (_ : q < 1) (hA : ∀ n : ℕ, A n ≤ C * q ^ n) :
    ∑' n : ℕ, A n ≤ C * (1 - q)⁻¹ := by
  calc
    ∑' n : ℕ, A n ≤ ∑' n : ℕ, C * q ^ n :=
      ENNReal.tsum_le_tsum hA
    _ = C * ∑' n : ℕ, q ^ n := ENNReal.tsum_mul_left
    _ = C * (1 - q)⁻¹ := by rw [ENNReal.tsum_geometric q]


end CKN.Core.HeatPotential
