/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRemainderMajorantQuantitative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsRemainder

/-!
# Pressure Gradient Origin KPHarmonic Moment

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4
private theorem integral_power_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) (a : ℝ) :
    (∫⁻ y, g y ^ a ∂μ) ^ (3/2 : ℝ) ≤
      μ Set.univ ^ (1/2 : ℝ) * ∫⁻ y, g y ^ (a * (3/2)) ∂μ := by
  have hpq : (3/2 : ℝ).HolderConjugate 3 := by constructor <;> norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (hg.pow_const a) (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [← ENNReal.rpow_mul, ENNReal.one_rpow, lintegral_const, one_mul] at h
  norm_num at h
  have ht := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 3/2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at ht
  norm_num at ht
  simpa only [mul_comm] using ht

private theorem slice_integral_power_bound {B : Set Vec3} {J : Set ℝ}
    {F : Vec3 × ℝ → ℝ≥0∞}
    (hF : AEMeasurable F ((volume.restrict B).prod (volume.restrict J))) (a : ℝ) :
    AEMeasurable (fun s => ∫⁻ y in B, F (y,s) ^ a) (volume.restrict J) ∧
    (∫⁻ s in J, (∫⁻ y in B, F (y,s) ^ a) ^ (3/2 : ℝ)) ≤
      volume B ^ (1/2 : ℝ) * ∫⁻ w in B ×ˢ J, F w ^ (a * (3/2)) := by
  refine ⟨(hF.pow_const a).lintegral_prod_left', ?_⟩
  calc
    _ ≤ ∫⁻ s in J, volume B ^ (1/2 : ℝ) *
        ∫⁻ y in B, F (y,s) ^ (a * (3/2)) := by
      apply lintegral_mono_ae
      filter_upwards [hF.aestronglyMeasurable.prodMk_right] with s hs
      simpa only [Measure.restrict_apply_univ] using integral_power_le (volume.restrict B)
        hs.aemeasurable a
    _ = _ := by
      rw [lintegral_const_mul'' _ ((hF.pow_const _).lintegral_prod_left'),
        ← lintegral_prod_symm _ (hF.pow_const _), Measure.prod_restrict]
      rfl

private theorem three_terms_power_bound (a b c : ℝ≥0∞) :
    (a + b + c) ^ (3/2 : ℝ) ≤
      16 * (a ^ (3/2 : ℝ) + b ^ (3/2 : ℝ) + c ^ (3/2 : ℝ)) := by
  have htwo : (2 : ℝ≥0∞) ^ (3/2 : ℝ) ≤ 4 := by
    calc
      _ ≤ (2 : ℝ≥0∞) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have h (x y : ℝ≥0∞) : (x+y) ^ (3/2 : ℝ) ≤ 4 *
      (x ^ (3/2 : ℝ) + y ^ (3/2 : ℝ)) :=
    (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow x y (by norm_num)).trans
      (mul_le_mul' htwo le_rfl)
  calc
    _ ≤ 4 * ((a+b) ^ (3/2 : ℝ) + c ^ (3/2 : ℝ)) := h _ _
    _ ≤ 4 * (4 * (a ^ (3/2 : ℝ) + b ^ (3/2 : ℝ)) + 4 * c ^ (3/2 : ℝ)) :=
      mul_le_mul' le_rfl (add_le_add (h _ _) (le_mul_of_one_le_left' (by norm_num)))
    _ = _ := by ring

private theorem three_slice_mass_bound {B : Set Vec3} {J : Set ℝ}
    {U P F : Vec3 × ℝ → ℝ≥0∞}
    (hU : AEMeasurable U ((volume.restrict B).prod (volume.restrict J)))
    (hP : AEMeasurable P ((volume.restrict B).prod (volume.restrict J)))
    (hF : AEMeasurable F ((volume.restrict B).prod (volume.restrict J)))
    (a b c D : ℝ≥0∞)
    (hUD : (∫⁻ w in B ×ˢ J, U w ^ (3 : ℝ)) ≤ D)
    (hPD : (∫⁻ w in B ×ˢ J, P w ^ (3 / 2 : ℝ)) ≤ D)
    (hFD : (∫⁻ w in B ×ˢ J, F w ^ (3 / 2 : ℝ)) ≤ D) :
    let M := fun s => a * (∫⁻ y in B, U (y,s) ^ (2 : ℝ)) +
      b * (∫⁻ y in B, P (y,s)) + c * (∫⁻ y in B, F (y,s))
    AEMeasurable M (volume.restrict J) ∧
    (∫⁻ s in J, M s ^ (3/2 : ℝ)) ≤
      16 * volume B ^ (1/2 : ℝ) *
        (a ^ (3/2 : ℝ) + b ^ (3/2 : ℝ) + c ^ (3/2 : ℝ)) * D := by
  have hu := slice_integral_power_bound hU 2
  have hp := slice_integral_power_bound hP 1
  have hf := slice_integral_power_bound hF 1
  norm_num only [one_mul, ENNReal.rpow_one, show (2 : ℝ) * (3/2) = 3 by norm_num] at hu hp hf
  refine ⟨((aemeasurable_const.mul hu.1).add (aemeasurable_const.mul hp.1)).add
    (aemeasurable_const.mul hf.1), ?_⟩
  dsimp only
  calc
    _ ≤ ∫⁻ s in J, 16 *
        ((a * (∫⁻ y in B, U (y,s) ^ (2 : ℝ))) ^ (3/2 : ℝ) +
          (b * (∫⁻ y in B, P (y,s))) ^ (3/2 : ℝ) +
          (c * (∫⁻ y in B, F (y,s))) ^ (3/2 : ℝ)) :=
      lintegral_mono (fun _ => three_terms_power_bound _ _ _)
    _ = 16 * (a ^ (3/2 : ℝ) * (∫⁻ s in J, (∫⁻ y in B, U (y,s) ^ (2 : ℝ)) ^ (3/2 : ℝ)) +
        b ^ (3/2 : ℝ) * (∫⁻ s in J, (∫⁻ y in B, P (y,s)) ^ (3/2 : ℝ)) +
        c ^ (3/2 : ℝ) * (∫⁻ s in J, (∫⁻ y in B, F (y,s)) ^ (3/2 : ℝ))) := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3/2)]
      have ha : AEMeasurable (fun s => a ^ (3/2 : ℝ) *
          (∫⁻ y in B, U (y,s) ^ (2 : ℝ)) ^ (3/2 : ℝ)) (volume.restrict J) :=
        aemeasurable_const.mul (hu.1.pow_const _)
      have hb : AEMeasurable (fun s => b ^ (3/2 : ℝ) *
          (∫⁻ y in B, P (y,s)) ^ (3/2 : ℝ)) (volume.restrict J) :=
        aemeasurable_const.mul (hp.1.pow_const _)
      simp only [ENNReal.rpow_ofNat] at ha hb ⊢
      have hab : AEMeasurable (fun s =>
          a ^ (3/2 : ℝ) * (∫⁻ y in B, U (y,s) ^ (2 : ℕ)) ^ (3/2 : ℝ) +
          b ^ (3/2 : ℝ) * (∫⁻ y in B, P (y,s)) ^ (3/2 : ℝ)) (volume.restrict J) := ha.add hb
      have hum : AEMeasurable (fun s => (∫⁻ y in B, U (y,s) ^ (2 : ℕ)) ^ (3/2 : ℝ))
          (volume.restrict J) := by simpa only [ENNReal.rpow_ofNat] using hu.1.pow_const (3/2 : ℝ)
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left' hab,
        lintegral_add_left' ha, lintegral_const_mul'' _ hum,
        lintegral_const_mul'' _ (hp.1.pow_const (3/2 : ℝ)), lintegral_const_mul'' _
          (hf.1.pow_const (3/2 : ℝ))]
    _ ≤ 16 * (a ^ (3/2 : ℝ) * (volume B ^ (1/2 : ℝ) * D) +
        b ^ (3/2 : ℝ) * (volume B ^ (1/2 : ℝ) * D) +
        c ^ (3/2 : ℝ) * (volume B ^ (1/2 : ℝ) * D)) := by
      gcongr
      · exact hu.2.trans (mul_le_mul' le_rfl hUD)
      · exact hp.2.trans (mul_le_mul' le_rfl hPD)
      · exact hf.2.trans (mul_le_mul' le_rfl hFD)
    _ = _ := by ring


/-- The harmonic slice majorant keeps only kinetic energy and pressure mass. -/
def originHarmonicSliceMajorant (C ρ : ℝ) (x : Vec3)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (s : ℝ) : ℝ≥0∞ :=
  fixedRemainderCoefficients C ρ 0 *
      (∫⁻ y in vec3Ball x ρ, ENNReal.ofReal (vec3EuclideanNorm (u (y,s))) ^ (2 : ℝ)) +
    fixedRemainderCoefficients C ρ 1 *
      (∫⁻ y in vec3Ball x ρ, ENNReal.ofReal |p (y,s)|)

/-- The explicit coefficient of the harmonic majorant's time moment. -/
def originHarmonicMomentConstant (C ρ : ℝ) (x : Vec3) : ℝ≥0∞ :=
  16 * volume (vec3Ball x ρ) ^ (1/2 : ℝ) *
    (fixedRemainderCoefficients C ρ 0 ^ (3/2 : ℝ) +
      fixedRemainderCoefficients C ρ 1 ^ (3/2 : ℝ))

/-- The harmonic time moment is linear in the unit data size and vanishes
with it; no additive constant is needed for the pressure and energy terms. -/
theorem origin_harmonic_majorant_moment_of_sws
    (C ε : ℝ) {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε)
    {z : ParabolicPoint} {ρ : ℝ}
    (hQ : parabolicCylinder z.1 z.2 ρ ⊆ parabolicCylinder (0 : Vec3) 0 1) :
    AEMeasurable (originHarmonicSliceMajorant C ρ z.1 u p)
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) ∧
    (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2,
      originHarmonicSliceMajorant C ρ z.1 u p s ^ (3/2 : ℝ)) ≤
      originHarmonicMomentConstant C ρ z.1 * ENNReal.ofReal ε := by
  let B := vec3Ball z.1 ρ
  let J := Ioc (z.2 - ρ ^ 2) z.2
  let U := fun w : Vec3 × ℝ => ENNReal.ofReal (vec3EuclideanNorm (u w))
  let P := fun w : Vec3 × ℝ => ENNReal.ofReal |p w|
  obtain ⟨Ω', J', hbox, hsub⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 (by norm_num : (0 : ℝ) < 1) hdom
  have hd := hsol.2.2.2.2.2.1 Ω' J' hbox
  have hlocal : B ×ˢ J ⊆ spaceTimeSet Ω' J' := hQ.trans hsub
  have hU : AEMeasurable U ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact ((continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      hd.1).aemeasurable.ennreal_ofReal).mono_measure
      (Measure.restrict_mono_set volume hlocal)
  have hP : AEMeasurable P ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact ((continuous_abs.comp_aestronglyMeasurable
      hd.2.2.1).aemeasurable.ennreal_ofReal).mono_measure
      (Measure.restrict_mono_set volume hlocal)
  have hUε : (∫⁻ w in B ×ˢ J, U w ^ (3 : ℝ)) ≤ ENNReal.ofReal ε :=
    (lintegral_mono_set hQ).trans ((lintegral_mono (fun _ =>
      (le_add_right le_rfl).trans (le_add_right le_rfl))).trans hsmall)
  have hPε : (∫⁻ w in B ×ˢ J, P w ^ (3/2 : ℝ)) ≤ ENNReal.ofReal ε :=
    (lintegral_mono_set hQ).trans ((lintegral_mono (fun _ =>
      (le_add_left le_rfl).trans (le_add_right le_rfl))).trans hsmall)
  have hh := three_slice_mass_bound hU hP
    (aemeasurable_const (b := (0 : ℝ≥0∞)))
    (fixedRemainderCoefficients C ρ 0) (fixedRemainderCoefficients C ρ 1)
    0 (ENNReal.ofReal ε) hUε hPε (by simp)
  have hm : AEMeasurable (fun s =>
      fixedRemainderCoefficients C ρ 0 * (∫⁻ y in B, U (y,s)^(2 : ℝ)) +
      fixedRemainderCoefficients C ρ 1 * (∫⁻ y in B, P (y,s))) (volume.restrict J) := by
    simpa only [zero_mul, add_zero] using hh.1
  refine ⟨hm, ?_⟩
  simpa only [originHarmonicSliceMajorant, originHarmonicMomentConstant,
    zero_mul, add_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 3/2)] using hh.2

private theorem ofReal_integral_le_mass (B : Set Vec3) (g : Vec3 → ℝ) :
    ENNReal.ofReal (∫ y in B, g y) ≤ ∫⁻ y in B, ENNReal.ofReal |g y| := by
  have h := enorm_integral_le_lintegral_enorm (μ := volume.restrict B) g
  simp only [Real.enorm_eq_ofReal_abs] at h
  exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans h

/-- One absolute harmonic coefficient controls every component of the
actual harmonic gradient by its slice-energy majorant. -/
theorem exists_origin_harmonic_gradient_majorant :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ}, IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ/2),
            ‖classicalGradient
              (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                (sourceSliceCentredMean z.1 ρ u) p s) x i‖ₑ ≤
              originHarmonicSliceMajorant C ρ z.1 u p s := by
  obtain ⟨C, hC, hbound⟩ := exists_harmonicPressurePart_Ck_slice_energy_of_sws 1
  refine ⟨C, hC, ?_⟩
  intro Ω I q u f Du p hsol z ρ hρ hsub
  filter_upwards [hbound hsol hρ hsub] with s hhs
  intro i x hx
  let B := vec3Ball z.1 ρ
  let η := mollifiedBallCutoff z.1 hρ
  let h := harmonicPressurePart η u (sourceSliceCentredMean z.1 ρ u) p s
  let Ch := C * ρ ^ (-3 : ℝ)
  let kp := (Real.pi * 4 / 3) ^ (1/3 : ℝ) * ρ
  have hCh : 0 ≤ Ch := by dsimp [Ch]; positivity
  have hkp : 0 < kp := by dsimp [kp]; positivity
  have hE : 0 ≤ ∫ y in B, vec3EuclideanNorm (u (y,s)) ^ (2 : ℕ) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hP : 0 ≤ ∫ y in B, |p (y,s)| := integral_nonneg (fun _ => abs_nonneg _)
  change ‖classicalGradient h x i‖ₑ ≤ _
  have hh := hhs x hx
  rw [norm_iteratedFDeriv_one] at hh
  norm_num only [Nat.cast_one, show -(2 + (1 : ℝ)) = -3 by norm_num] at hh
  have hi : ‖classicalGradient h x i‖ ≤ ‖fderiv ℝ h x‖ :=
    ((fderiv ℝ h x).le_opNorm (basisVec i)).trans
      (mul_le_of_le_one_right (norm_nonneg _) (norm_basisVec_le_one i))
  have hb : ‖classicalGradient h x i‖ ≤
      (Ch/ρ) * (∫ y in B, vec3EuclideanNorm (u (y,s)) ^ (2 : ℕ)) +
      (Ch/kp) * (∫ y in B, |p (y,s)|) := by
    apply (hi.trans hh).trans_eq
    dsimp only [Ch, kp, B]
    ring
  rw [← ofReal_norm]
  apply (ENNReal.ofReal_le_ofReal hb).trans
  rw [ENNReal.ofReal_add (mul_nonneg (div_nonneg hCh hρ.le) hE)
    (mul_nonneg (div_nonneg hCh hkp.le) hP),
    ENNReal.ofReal_mul (div_nonneg hCh hρ.le), ENNReal.ofReal_mul (div_nonneg hCh hkp.le)]
  apply add_le_add (mul_le_mul' le_rfl _) (mul_le_mul' le_rfl _)
  · apply (ofReal_integral_le_mass B (fun y => vec3EuclideanNorm (u (y,s)) ^ (2 : ℕ))).trans_eq
    apply lintegral_congr
    intro y
    rw [abs_of_nonneg (sq_nonneg _), ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _),
      ENNReal.rpow_ofNat]
  · simpa only [abs_abs] using ofReal_integral_le_mass B (fun y => |p (y,s)|)

private theorem clipped_time_power_le {J : Set ℝ} {P : ℝ → ℝ≥0∞}
    {E : ℝ≥0∞} (hJ : MeasurableSet J) (hP : AEMeasurable P (volume.restrict J))
    (hmassJ : (∫⁻ s in J, P s ^ (3 / 2 : ℝ)) ≤ E) {t r : ℝ} (hr : 0 < r) :
    (∫⁻ s in Ioc (t-r^2) t ∩ J, P s^(6/5 : ℝ)) ≤
      E^(4/5 : ℝ) * ENNReal.ofReal r^(2/5 : ℝ) := by
  have hH : AEMeasurable (J.indicator P) volume :=
    (aemeasurable_indicator_iff hJ).mpr hP
  have hmass : (∫⁻ s, J.indicator P s ^ (3/2 : ℝ)) ≤ E := by
    have heq : (fun s => J.indicator P s ^ (3/2 : ℝ)) =
        J.indicator (fun s => P s ^ (3/2 : ℝ)) := by
      funext s
      by_cases hs : s ∈ J
      · simp only [indicator_of_mem hs]
      · simp only [indicator_of_notMem hs, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 3/2)]
    rw [heq, lintegral_indicator hJ]
    exact hmassJ
  have hh := pressure_remainder_time_power_bound hH (t := t) hr
  have heq : (fun s => J.indicator P s ^ (6/5 : ℝ)) =
      J.indicator (fun s => P s ^ (6/5 : ℝ)) := by
    funext s
    by_cases hs : s ∈ J
    · simp only [indicator_of_mem hs]
    · simp only [indicator_of_notMem hs, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 6/5)]
  rw [heq, lintegral_indicator hJ,
    Measure.restrict_restrict hJ, inter_comm J] at hh
  exact hh.trans (mul_le_mul' (ENNReal.rpow_le_rpow hmass (by norm_num)) le_rfl)


/-- Temporal Hölder gives the small-cell power with its vanishing data-size
factor retained explicitly. The source collar and the tested cell are separate. -/
theorem origin_harmonic_majorant_clipped_time_of_sws
    (C ε t r : ℝ) (hr : 0 < r)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε)
    {z : ParabolicPoint} {ρ : ℝ}
    (hQ : parabolicCylinder z.1 z.2 ρ ⊆ parabolicCylinder (0 : Vec3) 0 1) :
    (∫⁻ s in Ioc (t-r^2) t ∩ Ioc (z.2-ρ^2) z.2,
      originHarmonicSliceMajorant C ρ z.1 u p s ^ (6/5 : ℝ)) ≤
      originHarmonicMomentConstant C ρ z.1 ^ (4/5 : ℝ) *
        ENNReal.ofReal ε ^ (4/5 : ℝ) * ENNReal.ofReal r ^ (2/5 : ℝ) := by
  obtain ⟨hm, hb⟩ := origin_harmonic_majorant_moment_of_sws C ε hsol hdom hsmall hQ
  have hh := clipped_time_power_le (t := t) measurableSet_Ioc hm hb hr
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4/5)] using hh

/-- A collar-independent moment coefficient for source radii between `1/8`
and `1`. It is an explicit function of the absolute harmonic coefficient. -/
def originHarmonicAbsoluteMomentConstant (C : ℝ) : ℝ≥0∞ :=
  16 * ENNReal.ofReal (Real.pi*4/3)^(1/2 : ℝ) *
    ((ENNReal.ofReal (4096*C))^(3/2 : ℝ) +
      (ENNReal.ofReal (4096*C / (Real.pi*4/3)^(1/3 : ℝ)))^(3/2 : ℝ))

/-- The harmonic moment coefficient is uniform on the admissible fixed collars. -/
theorem origin_harmonic_moment_constant_le_absolute
    (C ρ : ℝ) (x : Vec3) (hC : 0 ≤ C) (hρlo : 1 / 8 ≤ ρ) (hρhi : ρ ≤ 1) :
    originHarmonicMomentConstant C ρ x ≤ originHarmonicAbsoluteMomentConstant C := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by norm_num) hρlo
  have hpow : ρ^(-4 : ℝ) ≤ 4096 := by
    have hh := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1/8) hρlo
      (by norm_num : (-4 : ℝ) ≤ 0)
    exact hh.trans_eq (by norm_num)
  have he : C*ρ^(-3 : ℝ)/ρ = C*ρ^(-4 : ℝ) := by
    norm_num [Real.rpow_neg, Real.rpow_natCast]
    field_simp
  have hfirst : C*ρ^(-3 : ℝ)/ρ ≤ 4096*C := by
    rw [he]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hpow hC
  have hsecond : C*ρ^(-3 : ℝ)/((Real.pi*4/3)^(1/3 : ℝ)*ρ) ≤
      4096*C/(Real.pi*4/3)^(1/3 : ℝ) := by
    have hh := div_le_div_of_nonneg_right hfirst
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi*4/3) (1/3 : ℝ))
    convert hh using 1
    ring
  have hv : volume (vec3Ball x ρ) ≤ ENNReal.ofReal (Real.pi*4/3) := by
    rw [volume_vec3Ball_eq]
    have hh : ENNReal.ofReal ρ ≤ 1 := by
      exact (ENNReal.ofReal_le_ofReal hρhi).trans_eq (by simp)
    exact (mul_le_mul' (pow_le_one₀ (by positivity) hh) le_rfl).trans_eq (one_mul _)
  unfold originHarmonicMomentConstant originHarmonicAbsoluteMomentConstant
  apply mul_le_mul'
  · exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hv (by norm_num))
  · apply add_le_add
    · apply ENNReal.rpow_le_rpow _ (by norm_num)
      change ENNReal.ofReal (C*ρ^(-3 : ℝ)/ρ) ≤ _
      exact ENNReal.ofReal_le_ofReal hfirst
    · apply ENNReal.rpow_le_rpow _ (by norm_num)
      change ENNReal.ofReal (C*ρ^(-3 : ℝ)/((Real.pi*4/3)^(1/3 : ℝ)*ρ)) ≤ _
      exact ENNReal.ofReal_le_ofReal hsecond

private theorem slice_norm_power_le_majorant
    {S : Set Vec3} {g : Vec3 → ℝ} {M : ℝ≥0∞}
    (hg : AEStronglyMeasurable g (volume.restrict S))
    (hb : ∀ᵐ y ∂volume.restrict S, ‖g y‖ₑ ≤ M) :
    eLpNorm g (ENNReal.ofReal (6/5 : ℝ)) (volume.restrict S)^(6/5 : ℝ) ≤
      volume S * M^(6/5 : ℝ) := by
  have hh := eLpNorm_le_of_ae_enorm_bound (p := ENNReal.ofReal (6/5 : ℝ)) hg hb
  simp only [smul_eq_mul, Measure.restrict_apply_univ] at hh
  norm_num only [ENNReal.toReal_ofReal, show (0 : ℝ) ≤ 6/5 by norm_num] at hh
  have hp := ENNReal.rpow_le_rpow hh (by norm_num : (0 : ℝ) ≤ 6/5)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul] at hp
  norm_num at hp
  simpa only [mul_comm] using hp

/-- A spatial majorant with the harmonic time bound controls the literal
clipped slice norm; spatial clipping contributes only its volume. -/
theorem origin_harmonic_clipped_slice_norm_bound
    (C ε : ℝ) (S : Set Vec3) (J : Set ℝ) (t r : ℝ) (hr : 0 < r)
    {M : ℝ → ℝ≥0∞} {F : Vec3 × ℝ → ℝ}
    (hJ : MeasurableSet J) (hm : AEMeasurable M (volume.restrict J))
    (hMass : (∫⁻ s in J, M s ^ (3 / 2 : ℝ)) ≤ CKN.Core.Step4.originHarmonicAbsoluteMomentConstant
      C *
      ENNReal.ofReal ε)
    (hf : ∀ᵐ s ∂volume.restrict J, AEStronglyMeasurable (fun y => F (y, s)) (volume.restrict S))
    (hb : ∀ᵐ s ∂volume.restrict J, ∀ᵐ y ∂volume.restrict S, ‖F (y, s)‖ₑ ≤ M s) :
    (∫⁻ s in Ioc (t-r^2) t ∩ J,
      eLpNorm (fun y => F (y,s)) (ENNReal.ofReal (6/5 : ℝ)) (volume.restrict S)^(6/5 : ℝ)) ≤
      volume S * originHarmonicAbsoluteMomentConstant C^(4/5 : ℝ) *
        ENNReal.ofReal ε^(4/5 : ℝ) * ENNReal.ofReal r^(2/5 : ℝ) := by
  have hw : Ioc (t-r^2) t ∩ J ⊆ J := inter_subset_right
  have hpoint : ∀ᵐ s ∂volume.restrict (Ioc (t-r^2) t ∩ J),
      eLpNorm (fun y => F (y,s)) (ENNReal.ofReal (6/5 : ℝ)) (volume.restrict S)^(6/5 : ℝ) ≤
        volume S * M s^(6/5 : ℝ) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hw hf,
      ae_restrict_of_ae_restrict_of_subset hw hb] with s hs hsB
    exact slice_norm_power_le_majorant hs hsB
  have htime := clipped_time_power_le (t := t) hJ hm hMass hr
  have hMm := hm.mono_measure (Measure.restrict_mono_set volume hw)
  calc
    _ ≤ ∫⁻ s in Ioc (t-r^2) t ∩ J, volume S*M s^(6/5 : ℝ) := lintegral_mono_ae hpoint
    _ = volume S * ∫⁻ s in Ioc (t-r^2) t ∩ J, M s^(6/5 : ℝ) :=
      lintegral_const_mul'' _ (hMm.pow_const _)
    _ ≤ _ := by
      have hh := mul_le_mul' (le_refl (volume S)) htime
      simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4/5), mul_assoc] using hh

end CKN.Core.Step4
