/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothCovariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatCovariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.GaussianEnvelope
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

/-!
# Concentration of actual pulse covariance columns

We use `r = sqrt L`, so that a slot has length `r^2`.  Pointwise Gaussian
bounds on the fundamental component and an actual compactly supported cutoff
give mass of order `r` and first centered moment of order `r^2`.  Division by
the mass then gives a direction error of order `1/r`.
-/

noncomputable section

namespace NavierStokes.PulseCovariance

open Set MeasureTheory Filter
open scoped Topology

private theorem inverse_length_mass (r u v : ℝ) (hr : r ≠ 0) :
    (u / r ^ 2) * (v * r) = u * v / r := by
  field_simp

private theorem normalize_mass_product (u k r : ℝ) (hk : k ≠ 0) :
    u * r ^ 2 = (u / k) * r * (k * r) := by
  field_simp

private theorem sub_normalized_mass (u m v : ℝ) (hm : m ≠ 0) :
    u / m - v = (u - m * v) / m := by
  field_simp

private theorem normalize_direction_product (r ε K C m : ℝ) (hr : r ≠ 0) :
    ε * m + (K / r ^ 2) * (C * r * m) = (ε + K * C / r) * m := by
  field_simp

noncomputable def gaussian (b m r v : ℝ) : ℝ :=
  Real.exp (-b * ((v - m) / r) ^ 2)

noncomputable def firstGaussianMoment (b : ℝ) : ℝ :=
  ∫ v : ℝ, |v| * Real.exp (-b * v ^ 2)

theorem gaussian_pos (b m r v : ℝ) : 0 < gaussian b m r v := Real.exp_pos _

theorem gaussian_eq_length (b m r v : ℝ) :
    gaussian b m r v = Real.exp (-b * (v - m) ^ 2 / r ^ 2) := by
  unfold gaussian
  congr 1
  ring

/-- The reference ODE envelope already constructed in `GaussianEnvelope`
supplies the pointwise Gaussian hypotheses with constants independent of slot
length. -/
theorem reference_envelope_gaussian_bounds {lam u : ℝ} (hlam : 0 < lam) (hu : 0 < u) :
    ∃ b B : ℝ, 0 < b ∧ 0 < B ∧ ∀ r : ℝ, 0 < r → ∀ v ∈ Icc 0 (r ^ 2),
      gaussian B (r ^ 2 / 2) r v ≤
        GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u (r ^ 2))
          (r ^ 2 / 2) v ∧
      GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u (r ^ 2))
          (r ^ 2 / 2) v ≤ gaussian b (r ^ 2 / 2) r v := by
  obtain ⟨b, B, hb, hB, hbounds⟩ :=
    GaussianEnvelope.reference_uniform_gaussian_bounds hlam hu
  refine ⟨b, B, hb, hB, ?_⟩
  intro r hr v hv
  simpa only [gaussian_eq_length] using hbounds (r ^ 2) (sq_pos_of_pos hr) v hv

theorem integrable_gaussian {b r : ℝ} (hb : 0 < b) (hr : 0 < r) (m : ℝ) :
    Integrable (gaussian b m r) := by
  exact ((integrable_exp_neg_mul_sq hb).comp_div hr.ne').comp_sub_right m

theorem integral_gaussian_scaled (b m r : ℝ) (hr : 0 < r) :
    (∫ v : ℝ, gaussian b m r v) = r * Real.sqrt (Real.pi / b) := by
  unfold gaussian
  rw [integral_sub_right_eq_self (fun v : ℝ => Real.exp (-b * (v / r) ^ 2)) m]
  rw [Measure.integral_comp_div (fun u : ℝ => Real.exp (-b * u ^ 2)) r,
    integral_gaussian, abs_of_pos hr, smul_eq_mul]

theorem integrable_first_gaussian {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : ℝ => |v| * Real.exp (-b * v ^ 2)) := by
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
    (integrable_mul_exp_neg_mul_sq hb).norm

theorem firstGaussianMoment_nonneg (b : ℝ) : 0 ≤ firstGaussianMoment b := by
  apply integral_nonneg
  intro v
  exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

theorem abs_sub_scaled {r : ℝ} (hr : 0 < r) (v m : ℝ) :
    |v - m| = r * |(v - m) / r| := by
  rw [abs_div, abs_of_pos hr]
  field_simp

theorem integrable_first_gaussian_scaled {b r : ℝ} (hb : 0 < b) (hr : 0 < r)
    (m : ℝ) : Integrable (fun v : ℝ => |v - m| * gaussian b m r v) := by
  have hi := (((integrable_first_gaussian hb).comp_div hr.ne').comp_sub_right m).const_mul r
  convert! hi using 1
  ext v
  rw [abs_sub_scaled hr v m]
  simp only [gaussian]
  ring

theorem integral_first_gaussian_scaled (b m r : ℝ) (hr : 0 < r) :
    (∫ v : ℝ, |v - m| * gaussian b m r v) = r ^ 2 * firstGaussianMoment b := by
  have heq : (fun v : ℝ => |v - m| * gaussian b m r v) =
      (fun v : ℝ => r * (|(v - m) / r| * Real.exp (-b * ((v - m) / r) ^ 2))) := by
    ext v
    rw [abs_sub_scaled hr v m]
    simp only [gaussian]
    ring
  rw [heq, integral_const_mul]
  rw [integral_sub_right_eq_self
    (fun v : ℝ => |v / r| * Real.exp (-b * (v / r) ^ 2)) m]
  rw [Measure.integral_comp_div (fun u : ℝ => |u| * Real.exp (-b * u ^ 2)) r,
    abs_of_pos hr, smul_eq_mul]
  simp only [firstGaussianMoment]
  ring

noncomputable def weight (ψ x : ℝ → ℝ) (v : ℝ) : ℝ := ψ v ^ 2 * x v ^ 2

noncomputable def mass (ψ x : ℝ → ℝ) : ℝ := ∫ v : ℝ, weight ψ x v

noncomputable def centeredMoment (ψ x : ℝ → ℝ) (m : ℝ) : ℝ :=
  ∫ v : ℝ, |v - m| * weight ψ x v

/-- All assumptions concern actual pointwise functions on the slot.  No
integrated covariance bound is an input. -/
structure PulseBounds (r a A b B : ℝ) (ψ x : ℝ → ℝ) : Prop where
  radius_one_le : 1 ≤ r
  lower_pos : 0 < a
  upper_pos : 0 < A
  decay_pos : 0 < b
  lower_decay_pos : 0 < B
  cutoff_continuous : Continuous ψ
  component_continuous : Continuous x
  cutoff_abs_le : ∀ v, |ψ v| ≤ 1
  cutoff_zero : ∀ v, v ∉ Icc (r ^ 2 / 6) (5 * r ^ 2 / 6) → ψ v = 0
  cutoff_one : ∀ v ∈ Icc (r ^ 2 / 3) (2 * r ^ 2 / 3), ψ v = 1
  component_lower : ∀ v ∈ Icc 0 (r ^ 2), a * gaussian B (r ^ 2 / 2) r v ≤ x v
  component_upper : ∀ v ∈ Icc 0 (r ^ 2), x v ≤ A * gaussian b (r ^ 2 / 2) r v

/-- The cutoff conditions, separated from the ODE envelope for the adapter. -/
structure CutoffBounds (r : ℝ) (ψ : ℝ → ℝ) : Prop where
  continuous : Continuous ψ
  abs_le : ∀ v, |ψ v| ≤ 1
  zero_outside : ∀ v, v ∉ Icc (r ^ 2 / 6) (5 * r ^ 2 / 6) → ψ v = 0
  one_inside : ∀ v ∈ Icc (r ^ 2 / 3) (2 * r ^ 2 / 3), ψ v = 1

/-- Direct adapter from the growing-mode comparison `a P ≤ x ≤ A P` and
two-sided Gaussian estimates on the actual reference envelope `P`. -/
theorem pulseBounds_of_envelope {r a A b B : ℝ} {ψ x P : ℝ → ℝ}
    (hr : 1 ≤ r) (ha : 0 < a) (hA : 0 < A) (hb : 0 < b) (hB : 0 < B)
    (hψ : CutoffBounds r ψ) (hx : Continuous x)
    (hP : ∀ v ∈ Icc 0 (r ^ 2),
      gaussian B (r ^ 2 / 2) r v ≤ P v ∧ P v ≤ gaussian b (r ^ 2 / 2) r v)
    (hcompare : ∀ v ∈ Icc 0 (r ^ 2), a * P v ≤ x v ∧ x v ≤ A * P v) :
    PulseBounds r a A b B ψ x := by
  refine ⟨hr, ha, hA, hb, hB, hψ.continuous, hx,
    hψ.abs_le, hψ.zero_outside, hψ.one_inside, ?_, ?_⟩
  · intro v hv
    exact (mul_le_mul_of_nonneg_left (hP v hv).1 ha.le).trans (hcompare v hv).1
  · intro v hv
    exact (hcompare v hv).2.trans (mul_le_mul_of_nonneg_left (hP v hv).2 hA.le)

namespace PulseBounds

variable {r a A b B : ℝ} {ψ x : ℝ → ℝ} (h : PulseBounds r a A b B ψ x)

include h

theorem radius_pos : 0 < r := lt_of_lt_of_le zero_lt_one h.radius_one_le

theorem component_pos {v : ℝ} (hv : v ∈ Icc 0 (r ^ 2)) : 0 < x v :=
  lt_of_lt_of_le (mul_pos h.lower_pos (gaussian_pos _ _ _ _)) (h.component_lower v hv)

omit h in
theorem weight_nonneg (v : ℝ) : 0 ≤ weight ψ x v := mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem weight_continuous : Continuous (weight ψ x) :=
  (h.cutoff_continuous.pow 2).mul (h.component_continuous.pow 2)

theorem weight_gaussian_upper (v : ℝ) :
    weight ψ x v ≤ A ^ 2 * gaussian (2 * b) (r ^ 2 / 2) r v := by
  by_cases hv : v ∈ Icc (r ^ 2 / 6) (5 * r ^ 2 / 6)
  · have hslot : v ∈ Icc 0 (r ^ 2) := by
      constructor <;> nlinarith [hv.1, hv.2, sq_nonneg r]
    have hx := h.component_upper v hslot
    have hx0 := (h.component_pos hslot).le
    have hg := (gaussian_pos b (r ^ 2 / 2) r v).le
    have hψ : ψ v ^ 2 ≤ 1 := by
      have hp := h.cutoff_abs_le v
      have hab := abs_le.mp hp
      nlinarith [sq_nonneg (ψ v), hab.1, hab.2]
    have he : gaussian b (r ^ 2 / 2) r v ^ 2 =
        gaussian (2 * b) (r ^ 2 / 2) r v := by
      simp only [gaussian, sq, ← Real.exp_add]
      congr 1
      ring
    calc
      weight ψ x v ≤ x v ^ 2 := by
        unfold weight
        nlinarith [mul_le_mul_of_nonneg_right hψ (sq_nonneg (x v))]
      _ ≤ (A * gaussian b (r ^ 2 / 2) r v) ^ 2 :=
        pow_le_pow_left₀ hx0 hx 2
      _ = A ^ 2 * gaussian (2 * b) (r ^ 2 / 2) r v := by rw [mul_pow, he]
  · rw [weight, h.cutoff_zero v hv]
    simpa using mul_nonneg (sq_nonneg A) (gaussian_pos (2 * b) (r ^ 2 / 2) r v).le

theorem weight_integrable : Integrable (weight ψ x) := by
  apply ((integrable_gaussian (b := 2 * b) (by linarith [h.decay_pos]) h.radius_pos
    (r ^ 2 / 2)).const_mul (A ^ 2)).mono' h.weight_continuous.aestronglyMeasurable
  filter_upwards [] with v
  simpa only [Real.norm_eq_abs, abs_of_nonneg (weight_nonneg v)] using
    h.weight_gaussian_upper v

theorem moment_integrable :
    Integrable (fun v : ℝ => |v - r ^ 2 / 2| * weight ψ x v) := by
  apply ((integrable_first_gaussian_scaled (b := 2 * b) (by linarith [h.decay_pos]) h.radius_pos
    (r ^ 2 / 2)).const_mul (A ^ 2)).mono'
      (((continuous_id.fun_sub continuous_const).abs.fun_mul
        h.weight_continuous).aestronglyMeasurable)
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (abs_nonneg _) (weight_nonneg v))]
  simp only [id_eq]
  nlinarith [mul_le_mul_of_nonneg_left (h.weight_gaussian_upper v) (abs_nonneg (v - r ^ 2 / 2))]

theorem mass_upper : mass ψ x ≤ A ^ 2 * Real.sqrt (Real.pi / (2 * b)) * r := by
  have hi := integral_mono h.weight_integrable
    ((integrable_gaussian (b := 2 * b) (by linarith [h.decay_pos]) h.radius_pos (r ^ 2 /
      2)).const_mul
      (A ^ 2)) h.weight_gaussian_upper
  rw [integral_const_mul, integral_gaussian_scaled _ _ _ h.radius_pos] at hi
  exact hi.trans_eq (by ring)

theorem moment_upper :
    centeredMoment ψ x (r ^ 2 / 2) ≤ A ^ 2 * firstGaussianMoment (2 * b) * r ^ 2 := by
  have hi := integral_mono h.moment_integrable
    ((integrable_first_gaussian_scaled (b := 2 * b) (by linarith [h.decay_pos]) h.radius_pos
      (r ^ 2 / 2)).const_mul (A ^ 2)) (fun v => ?_)
  · rw [integral_const_mul, integral_first_gaussian_scaled _ _ _ h.radius_pos] at hi
    exact hi.trans_eq (by ring)
  · nlinarith [mul_le_mul_of_nonneg_left (h.weight_gaussian_upper v)
      (abs_nonneg (v - r ^ 2 / 2))]

theorem core_mem_middle {v : ℝ}
    (hv : v ∈ Icc (r ^ 2 / 2 - r / 6) (r ^ 2 / 2 + r / 6)) :
    v ∈ Icc (r ^ 2 / 3) (2 * r ^ 2 / 3) := by
  have hr := h.radius_one_le
  have hrr : r ≤ r ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) h.radius_pos.le]
  constructor <;> nlinarith [hv.1, hv.2]

theorem core_scaled_sq {v : ℝ}
    (hv : v ∈ Icc (r ^ 2 / 2 - r / 6) (r ^ 2 / 2 + r / 6)) :
    ((v - r ^ 2 / 2) / r) ^ 2 ≤ 1 / 36 := by
  have hlo : -(1 / 6 : ℝ) ≤ (v - r ^ 2 / 2) / r := by
    apply (le_div_iff₀ h.radius_pos).mpr
    linarith [hv.1]
  have hhi : (v - r ^ 2 / 2) / r ≤ (1 / 6 : ℝ) := by
    apply (div_le_iff₀ h.radius_pos).mpr
    linarith [hv.2]
  nlinarith

theorem core_weight_lower {v : ℝ}
    (hv : v ∈ Icc (r ^ 2 / 2 - r / 6) (r ^ 2 / 2 + r / 6)) :
    a ^ 2 * Real.exp (-B / 18) ≤ weight ψ x v := by
  have hmid := h.core_mem_middle hv
  have hslot : v ∈ Icc 0 (r ^ 2) := by
    constructor <;> nlinarith [hmid.1, hmid.2, sq_nonneg r]
  have hx := h.component_lower v hslot
  have he : Real.exp (-B / 18) ≤ gaussian B (r ^ 2 / 2) r v ^ 2 := by
    unfold gaussian
    rw [pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (h.core_scaled_sq hv) h.lower_decay_pos.le]
  rw [weight, h.cutoff_one v hmid]
  simp only [one_pow, one_mul]
  calc
    a ^ 2 * Real.exp (-B / 18) ≤ a ^ 2 * gaussian B (r ^ 2 / 2) r v ^ 2 :=
      mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = (a * gaussian B (r ^ 2 / 2) r v) ^ 2 := by ring
    _ ≤ x v ^ 2 := pow_le_pow_left₀
      (mul_pos h.lower_pos (gaussian_pos _ _ _ _)).le hx 2

noncomputable def lowerMassConstant (a B : ℝ) : ℝ := a ^ 2 * Real.exp (-B / 18) / 3

theorem lowerMassConstant_pos : 0 < lowerMassConstant a B := by
  unfold lowerMassConstant
  have := h.lower_pos
  positivity

theorem mass_lower : lowerMassConstant a B * r ≤ mass ψ x := by
  have hv : (volume : Measure ℝ) (Icc (r ^ 2 / 2 - r / 6) (r ^ 2 / 2 + r / 6)) ≠ ⊤ :=
    ne_of_lt (isCompact_Icc.measure_lt_top)
  have hi := setIntegral_ge_of_const_le measurableSet_Icc hv
    (fun v hv => h.core_weight_lower hv) h.weight_integrable.integrableOn
  rw [Real.volume_real_Icc_of_le (by linarith [h.radius_pos])] at hi
  have hj := setIntegral_le_integral (s := Icc (r ^ 2 / 2 - r / 6) (r ^ 2 / 2 + r / 6))
    h.weight_integrable (ae_of_all _ weight_nonneg)
  change _ ≤ mass ψ x at hj
  calc
    lowerMassConstant a B * r =
        (a ^ 2 * Real.exp (-B / 18)) *
          (r ^ 2 / 2 + r / 6 - (r ^ 2 / 2 - r / 6)) := by
      unfold lowerMassConstant
      ring
    _ ≤ _ := by simpa only [smul_eq_mul, mul_comm] using hi
    _ ≤ mass ψ x := hj

theorem mass_pos : 0 < mass ψ x :=
  lt_of_lt_of_le (mul_pos h.lowerMassConstant_pos h.radius_pos) h.mass_lower

theorem cutoff_compact : HasCompactSupport ψ :=
  HasCompactSupport.intro isCompact_Icc h.cutoff_zero

theorem weight_compact : HasCompactSupport (weight ψ x) := by
  apply HasCompactSupport.intro (K := Icc (r ^ 2 / 6) (5 * r ^ 2 / 6)) isCompact_Icc
  intro v hv
  simp [weight, h.cutoff_zero v hv]

theorem weight_direction_integrable {q : ℝ → ℝ}
    (hq : ContinuousOn q (Icc 0 (r ^ 2))) :
    Integrable (fun v => weight ψ x v * q v) := by
  have hs : Function.support (fun v => weight ψ x v * q v) ⊆ Icc 0 (r ^ 2) := by
    intro v hv
    by_contra hv'
    have hout : v ∉ Icc (r ^ 2 / 6) (5 * r ^ 2 / 6) := by
      intro hin
      apply hv'
      constructor <;> nlinarith [hin.1, hin.2, sq_nonneg r]
    exact hv (by simp [weight, h.cutoff_zero v hout])
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  exact (h.weight_continuous.continuousOn.mul hq).integrableOn_Icc

/-- The positive scalar prefactor has precisely the required reciprocal-square-
root size when the column coefficient has reciprocal-slot-length size. -/
theorem scalar_size_bounds {ci clo chi : ℝ} (hclo : 0 < clo) (hchi : 0 < chi)
    (hci_lower : clo / r ^ 2 ≤ ci) (hci_upper : ci ≤ chi / r ^ 2) :
    0 < ci * mass ψ x ∧
      clo * lowerMassConstant a B / r ≤ ci * mass ψ x ∧
      ci * mass ψ x ≤ chi * (A ^ 2 * Real.sqrt (Real.pi / (2 * b))) / r := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos h.radius_pos
  have hci : 0 < ci := lt_of_lt_of_le (div_pos hclo hr2) hci_lower
  refine ⟨mul_pos hci h.mass_pos, ?_, ?_⟩
  · calc
      clo * lowerMassConstant a B / r =
          (clo / r ^ 2) * (lowerMassConstant a B * r) :=
        (inverse_length_mass _ _ _ h.radius_pos.ne').symm
      _ ≤ ci * mass ψ x :=
        mul_le_mul hci_lower h.mass_lower
          (mul_pos h.lowerMassConstant_pos h.radius_pos).le hci.le
  · calc
      ci * mass ψ x ≤ (chi / r ^ 2) *
          (A ^ 2 * Real.sqrt (Real.pi / (2 * b)) * r) :=
        mul_le_mul hci_upper h.mass_upper h.mass_pos.le (div_pos hchi hr2).le
      _ = chi * (A ^ 2 * Real.sqrt (Real.pi / (2 * b))) / r :=
        inverse_length_mass _ _ _ h.radius_pos.ne'

end PulseBounds

noncomputable def averagedDirection (ψ x q : ℝ → ℝ) : ℝ :=
  (∫ v : ℝ, weight ψ x v * q v) / mass ψ x

noncomputable def concentrationConstant (a A b B : ℝ) : ℝ :=
  A ^ 2 * firstGaussianMoment (2 * b) / PulseBounds.lowerMassConstant a B

namespace PulseBounds

variable {r a A b B : ℝ} {ψ x : ℝ → ℝ} (h : PulseBounds r a A b B ψ x)

include h

theorem concentrationConstant_nonneg : 0 ≤ concentrationConstant a A b B := by
  exact div_nonneg (mul_nonneg (sq_nonneg _) (firstGaussianMoment_nonneg _))
    h.lowerMassConstant_pos.le

theorem normalized_moment_bound :
    centeredMoment ψ x (r ^ 2 / 2) / mass ψ x ≤ concentrationConstant a A b B * r := by
  apply (div_le_iff₀ h.mass_pos).mpr
  calc
    centeredMoment ψ x (r ^ 2 / 2) ≤
        A ^ 2 * firstGaussianMoment (2 * b) * r ^ 2 := h.moment_upper
    _ = concentrationConstant a A b B * r * (lowerMassConstant a B * r) :=
      normalize_mass_product _ _ _ h.lowerMassConstant_pos.ne'
    _ ≤ concentrationConstant a A b B * r * mass ψ x :=
      mul_le_mul_of_nonneg_left h.mass_lower
        (mul_nonneg h.concentrationConstant_nonneg h.radius_pos.le)

theorem averagedDirection_sub {q : ℝ → ℝ} (hq : ContinuousOn q (Icc 0 (r ^ 2))) (q₀ : ℝ) :
    averagedDirection ψ x q - q₀ =
      (∫ v : ℝ, weight ψ x v * (q v - q₀)) / mass ψ x := by
  have he : (fun v => weight ψ x v * (q v - q₀)) =
      (fun v => weight ψ x v * q v - weight ψ x v * q₀) := by
    ext v
    ring
  rw [he, integral_sub (h.weight_direction_integrable hq)
    (h.weight_integrable.mul_const q₀), integral_mul_const]
  change (∫ v : ℝ, weight ψ x v * q v) / mass ψ x - q₀ =
    ((∫ v : ℝ, weight ψ x v * q v) - mass ψ x * q₀) / mass ψ x
  exact sub_normalized_mass _ _ _ h.mass_pos.ne'

/-- A pointwise directional error plus a pointwise linear drift gives an actual
integrated error.  The moment bounds used below are derived above, not assumed. -/
theorem averagedDirection_error {q : ℝ → ℝ} (hq : ContinuousOn q (Icc 0 (r ^ 2)))
    {q₀ ε K : ℝ} (hK : 0 ≤ K)
    (hqbound : ∀ v ∈ Icc 0 (r ^ 2),
      |q v - q₀| ≤ ε + K * |v - r ^ 2 / 2| / r ^ 2) :
    |averagedDirection ψ x q - q₀| ≤
      ε + K * concentrationConstant a A b B / r := by
  have hgi : Integrable (fun v => ε * weight ψ x v +
      (K / r ^ 2) * (|v - r ^ 2 / 2| * weight ψ x v)) :=
    (h.weight_integrable.const_mul ε).add (h.moment_integrable.const_mul (K / r ^ 2))
  have hpoint (v : ℝ) : |weight ψ x v * (q v - q₀)| ≤
      ε * weight ψ x v + (K / r ^ 2) * (|v - r ^ 2 / 2| * weight ψ x v) := by
    by_cases hv : v ∈ Icc (r ^ 2 / 6) (5 * r ^ 2 / 6)
    · have hslot : v ∈ Icc 0 (r ^ 2) := by
        constructor <;> nlinarith [hv.1, hv.2, sq_nonneg r]
      rw [abs_mul, abs_of_nonneg (weight_nonneg v)]
      convert! mul_le_mul_of_nonneg_left (hqbound v hslot) (weight_nonneg v) using 1
      ring
    · simp [weight, h.cutoff_zero v hv]
  have hi := norm_integral_le_of_norm_le (f := fun v => weight ψ x v * (q v - q₀))
    hgi (ae_of_all _ (fun v => by simpa only [Real.norm_eq_abs] using hpoint v))
  simp only [Real.norm_eq_abs] at hi
  rw [integral_add (h.weight_integrable.const_mul ε)
    (h.moment_integrable.const_mul (K / r ^ 2)), integral_const_mul, integral_const_mul] at hi
  change |∫ v : ℝ, weight ψ x v * (q v - q₀)| ≤
    ε * mass ψ x + (K / r ^ 2) * centeredMoment ψ x (r ^ 2 / 2) at hi
  rw [h.averagedDirection_sub hq q₀, abs_div, abs_of_pos h.mass_pos]
  apply (div_le_iff₀ h.mass_pos).mpr
  calc
    |∫ v : ℝ, weight ψ x v * (q v - q₀)| ≤
        ε * mass ψ x + (K / r ^ 2) * centeredMoment ψ x (r ^ 2 / 2) := hi
    _ ≤ ε * mass ψ x + (K / r ^ 2) *
        (concentrationConstant a A b B * r * mass ψ x) := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hK (sq_nonneg r))
      exact (div_le_iff₀ h.mass_pos).mp h.normalized_moment_bound
    _ = (ε + K * concentrationConstant a A b B / r) * mass ψ x :=
      normalize_direction_product _ _ _ _ _ h.radius_pos.ne'

/-- The ODE directional error `E/L` is smaller than the Gaussian concentration
error `1/sqrt L`. -/
theorem averagedDirection_error_order {q : ℝ → ℝ}
    (hq : ContinuousOn q (Icc 0 (r ^ 2))) {q₀ E K : ℝ}
    (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hqbound : ∀ v ∈ Icc 0 (r ^ 2),
      |q v - q₀| ≤ E / r ^ 2 + K * |v - r ^ 2 / 2| / r ^ 2) :
    |averagedDirection ψ x q - q₀| ≤
      (E + K * concentrationConstant a A b B) / r := by
  have hi := h.averagedDirection_error hq hK hqbound
  have hEr : E / r ^ 2 ≤ E / r := by
    apply div_le_div_of_nonneg_left hE h.radius_pos
    nlinarith [mul_nonneg (sub_nonneg.mpr h.radius_one_le) h.radius_pos.le]
  apply hi.trans
  rw [add_div]
  exact add_le_add_left hEr _

end PulseBounds

abbrev Vec2 := SmoothCovariance.Vec2
abbrev Mat2 := SmoothCovariance.Mat2

noncomputable def radiusProfile (s : ℝ) : ℝ := Real.sqrt (1 + s ^ 2)

theorem radiusProfile_pos (s : ℝ) : 0 < radiusProfile s := by
  apply Real.sqrt_pos.mpr
  positivity

theorem radiusProfile_sq (s : ℝ) : radiusProfile s ^ 2 = 1 + s ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem abs_le_radiusProfile (s : ℝ) : |s| ≤ radiusProfile s := by
  have hp := (radiusProfile_pos s).le
  have hs := radiusProfile_sq s
  nlinarith [sq_abs s, abs_nonneg s]

/-- The square-root profile used in the actual tangent model is globally
one-Lipschitz; smoothness of a normalized direction is not assumed here. -/
theorem radiusProfile_lipschitz (s t : ℝ) :
    |radiusProfile s - radiusProfile t| ≤ |s - t| := by
  have hp : 0 < radiusProfile s + radiusProfile t :=
    add_pos (radiusProfile_pos s) (radiusProfile_pos t)
  have he : (radiusProfile s - radiusProfile t) * (radiusProfile s + radiusProfile t) =
      (s - t) * (s + t) := by
    nlinarith [radiusProfile_sq s, radiusProfile_sq t]
  have ha := congrArg abs he
  rw [abs_mul, abs_mul, abs_of_pos hp] at ha
  have hst : |s + t| ≤ radiusProfile s + radiusProfile t :=
    (abs_add_le s t).trans (add_le_add (abs_le_radiusProfile s) (abs_le_radiusProfile t))
  exact (mul_le_mul_iff_left₀ hp).mp (by
    nlinarith [mul_le_mul_of_nonneg_left hst (abs_nonneg (s - t))])

/-- Coordinates in the fixed tangent frame `(N,K)` of `h N - s K`, where
`h = c₀ sqrt(1+s²)`. -/
noncomputable def modelDirection (c₀ s : ℝ) : Vec2 := ![c₀ * radiusProfile s, -s]

theorem modelDirection_lipschitz (c₀ s t : ℝ) (i : Fin 2) :
    |modelDirection c₀ s i - modelDirection c₀ t i| ≤ (|c₀| + 1) * |s - t| := by
  fin_cases i
  · change |c₀ * radiusProfile s - c₀ * radiusProfile t| ≤ _
    rw [← mul_sub, abs_mul]
    calc
      |c₀| * |radiusProfile s - radiusProfile t| ≤ |c₀| * |s - t| :=
        mul_le_mul_of_nonneg_left (radiusProfile_lipschitz s t) (abs_nonneg _)
      _ ≤ (|c₀| + 1) * |s - t| := by nlinarith [abs_nonneg (s - t)]
  · change |(-s) - (-t)| ≤ _
    have he : |(-s) - (-t)| = |s - t| := by
      calc
        |(-s) - (-t)| = |-(s - t)| := congrArg abs (by ring)
        _ = |s - t| := abs_neg _
    rw [he]
    nlinarith [mul_nonneg (abs_nonneg c₀) (abs_nonneg (s - t))]

noncomputable def affineSlope (s₀ slope r v : ℝ) : ℝ :=
  s₀ + slope * (v - r ^ 2 / 2) / r ^ 2

theorem affineSlope_midpoint (s₀ slope r : ℝ) : affineSlope s₀ slope r (r ^ 2 / 2) = s₀ := by
  simp [affineSlope]

theorem hasDerivAt_affineSlope (s₀ slope r v : ℝ) :
    HasDerivAt (affineSlope s₀ slope r) (slope / r ^ 2) v := by
  unfold affineSlope
  simpa only [id_eq, mul_one] using
    (((hasDerivAt_id v).sub_const (r ^ 2 / 2)).const_mul slope).div_const (r ^ 2) |>.const_add s₀

theorem affineSlope_deriv_bound (s₀ slope r v : ℝ) {C : ℝ} (hC : |slope| ≤ C) :
    |deriv (affineSlope s₀ slope r) v| ≤ C / r ^ 2 := by
  rw [(hasDerivAt_affineSlope s₀ slope r v).deriv, abs_div, abs_of_nonneg (sq_nonneg r)]
  exact div_le_div_of_nonneg_right hC (sq_nonneg r)

theorem affineSlope_distance (s₀ slope r v : ℝ) :
    |affineSlope s₀ slope r v - s₀| = |slope| * |v - r ^ 2 / 2| / r ^ 2 := by
  simp only [affineSlope, add_sub_cancel_left, abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg r)]

theorem modelDirection_affine_drift (c₀ s₀ slope r v : ℝ) (i : Fin 2) :
    |modelDirection c₀ (affineSlope s₀ slope r v) i - modelDirection c₀ s₀ i| ≤
      ((|c₀| + 1) * |slope|) * |v - r ^ 2 / 2| / r ^ 2 := by
  have hi := modelDirection_lipschitz c₀ (affineSlope s₀ slope r v) s₀ i
  rw [affineSlope_distance] at hi
  exact hi.trans_eq (by ring)

noncomputable def actualColumn (ci : ℝ) (ψ x : ℝ → ℝ) (t : ℝ → Vec2) : Vec2 :=
  fun i => ci * ∫ v : ℝ, ψ v ^ 2 * x v * t v i

noncomputable def normalizedColumn (ψ x : ℝ → ℝ) (t : ℝ → Vec2) : Vec2 :=
  fun i => averagedDirection ψ x (fun v => t v i / x v)

namespace PulseBounds

variable {r a A b B : ℝ} {ψ x : ℝ → ℝ} (h : PulseBounds r a A b B ψ x)

include h

theorem raw_integrand_eq {t : ℝ → Vec2} (v : ℝ) (i : Fin 2) :
    ψ v ^ 2 * x v * t v i = weight ψ x v * (t v i / x v) := by
  by_cases hv : v ∈ Icc 0 (r ^ 2)
  · have hx := (h.component_pos hv).ne'
    unfold weight
    field_simp
  · have hout : v ∉ Icc (r ^ 2 / 6) (5 * r ^ 2 / 6) := by
      intro hin
      apply hv
      constructor <;> nlinarith [hin.1, hin.2, sq_nonneg r]
    simp [weight, h.cutoff_zero v hout]

/-- Exact factorization of the actual covariance integral into its positive
mass and normalized direction. -/
theorem actualColumn_factorization (ci : ℝ) (t : ℝ → Vec2) :
    actualColumn ci ψ x t = fun i => (ci * mass ψ x) * normalizedColumn ψ x t i := by
  ext i
  unfold actualColumn normalizedColumn averagedDirection
  simp_rw [h.raw_integrand_eq]
  exact (mul_div_cancel_right₀
    (ci * (∫ v : ℝ, weight ψ x v * (t v i / x v))) h.mass_pos.ne').symm.trans (by ring)

theorem actualColumn_eq_intervalIntegral (ci : ℝ) (t : ℝ → Vec2) (i : Fin 2) :
    actualColumn ci ψ x t i = ci * ∫ v in (0 : ℝ)..r ^ 2, ψ v ^ 2 * x v * t v i := by
  unfold actualColumn
  congr 1
  rw [intervalIntegral.integral_of_le (sq_nonneg r)]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  have hout : v ∉ Icc (r ^ 2 / 6) (5 * r ^ 2 / 6) := by
    intro hin
    apply hv
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos h.radius_pos
    constructor <;> nlinarith [hin.1, hin.2]
  simp [h.cutoff_zero v hout]

theorem ratio_continuousOn {t : ℝ → Vec2}
    (ht : ∀ i, ContinuousOn (fun v => t v i) (Icc 0 (r ^ 2))) (i : Fin 2) :
    ContinuousOn (fun v => t v i / x v) (Icc 0 (r ^ 2)) :=
  (ht i).div h.component_continuous.continuousOn (fun _ hv => (h.component_pos hv).ne')

/-- Directional concentration for actual fundamental tangent components.
The sole tangent estimate assumed is the pointwise ODE approximation to
`h(v)N-s(v)K`, with affine `s` and the exact square-root profile `h`. -/
theorem normalizedColumn_error {t : ℝ → Vec2}
    (ht : ∀ i, ContinuousOn (fun v => t v i) (Icc 0 (r ^ 2)))
    {E c₀ s₀ slope : ℝ} (hE : 0 ≤ E)
    (htmodel : ∀ v ∈ Icc 0 (r ^ 2), ∀ i,
      |t v i / x v - modelDirection c₀ (affineSlope s₀ slope r v) i| ≤ E / r ^ 2)
    (i : Fin 2) :
    |normalizedColumn ψ x t i - modelDirection c₀ s₀ i| ≤
      (E + ((|c₀| + 1) * |slope|) * concentrationConstant a A b B) / r := by
  apply h.averagedDirection_error_order (h.ratio_continuousOn ht i) hE
    (mul_nonneg (by positivity) (abs_nonneg _))
  intro v hv
  exact (abs_sub_le (t v i / x v)
    (modelDirection c₀ (affineSlope s₀ slope r v) i) (modelDirection c₀ s₀ i)).trans
      (add_le_add (htmodel v hv i) (modelDirection_affine_drift c₀ s₀ slope r v i))

/-- The ODE error may instead be supplied as `E/S` on a slot with `L ≤ κ S`.
This converts it to the preceding concentration estimate. -/
theorem normalizedColumn_error_of_outer_scale {t : ℝ → Vec2}
    (ht : ∀ i, ContinuousOn (fun v => t v i) (Icc 0 (r ^ 2)))
    {E S κ c₀ s₀ slope : ℝ} (hE : 0 ≤ E) (hS : 0 < S) (hκ : 0 ≤ κ)
    (hL : r ^ 2 ≤ κ * S)
    (htmodel : ∀ v ∈ Icc 0 (r ^ 2), ∀ i,
      |t v i / x v - modelDirection c₀ (affineSlope s₀ slope r v) i| ≤ E / S)
    (i : Fin 2) :
    |normalizedColumn ψ x t i - modelDirection c₀ s₀ i| ≤
      (E * κ + ((|c₀| + 1) * |slope|) * concentrationConstant a A b B) / r := by
  apply h.normalizedColumn_error ht (mul_nonneg hE hκ) _ i
  intro v hv j
  apply (htmodel v hv j).trans
  apply (div_le_div_iff₀ hS (sq_pos_of_pos h.radius_pos)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hL hE]

end PulseBounds

/-- A single actual pulse.  Every estimate in this record is pointwise;
neither its covariance integral nor its average direction is assumed. -/
structure TangentPulse (r a A b B c₀ s₀ slope E : ℝ) where
  cutoff : ℝ → ℝ
  component : ℝ → ℝ
  tangent : ℝ → Vec2
  bounds : PulseBounds r a A b B cutoff component
  tangent_continuous : ∀ i, ContinuousOn (fun v => tangent v i) (Icc 0 (r ^ 2))
  tangent_model : ∀ v ∈ Icc 0 (r ^ 2), ∀ i,
    |tangent v i / component v - modelDirection c₀ (affineSlope s₀ slope r v) i| ≤
      E / r ^ 2

noncomputable def signedSlopes (u : ℝ) : Vec2 := ![u, -u]

noncomputable def signedModel (c₀ u : ℝ) : Mat2 :=
  fun i j => modelDirection c₀ (signedSlopes u j) i

theorem signedModel_eq_covariance (c₀ u : ℝ) :
    signedModel c₀ u = Covariance.signedMatrix (Covariance.normalMagnitude c₀ u) u 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [signedModel, modelDirection, signedSlopes, Covariance.signedMatrix,
      Covariance.normalMagnitude, radiusProfile]

theorem signedModel_strictCone {c₀ u m t : ℝ} (hc₀ : c₀ < 0) (hu : 0 < u)
    (hcone : |Covariance.normalMagnitude c₀ u * t| < u * m) :
    SmoothCovariance.StrictCone (signedModel c₀ u) (Covariance.target m t) := by
  rw [signedModel_eq_covariance]
  exact SmoothCovariance.signed_model_strictCone (Covariance.normalMagnitude_pos hc₀)
    hu zero_lt_one zero_lt_one hcone

theorem signedModel_continuousOn {X : Type*} [TopologicalSpace X] {K : Set X}
    {c₀ u : X → ℝ} (hc₀ : ContinuousOn c₀ K) (hu : ContinuousOn u K) (i j : Fin 2) :
    ContinuousOn (fun p => signedModel (c₀ p) (u p) i j) K := by
  have hn : ContinuousOn (fun p => c₀ p * Real.sqrt (1 + u p ^ 2)) K :=
    hc₀.mul (Real.continuous_sqrt.comp_continuousOn (continuousOn_const.add (hu.pow 2)))
  fin_cases i <;> fin_cases j
  · simpa [signedModel, modelDirection, signedSlopes, radiusProfile] using hn
  · simpa [signedModel, modelDirection, signedSlopes, radiusProfile] using hn
  · simpa [signedModel, modelDirection, signedSlopes] using hu.fun_neg
  · simpa [signedModel, modelDirection, signedSlopes] using hu

abbrev SignedPulsePair (r a A b B c₀ u E : ℝ) :=
  (j : Fin 2) → TangentPulse r a A b B c₀ (signedSlopes u j) (signedSlopes u j) E

noncomputable def actualMatrix {r a A b B c₀ u E : ℝ}
    (pulses : SignedPulsePair r a A b B c₀ u E) (ci : Vec2) : Mat2 :=
  fun i j => actualColumn (ci j) (pulses j).cutoff (pulses j).component (pulses j).tangent i

noncomputable def normalizedMatrix {r a A b B c₀ u E : ℝ}
    (pulses : SignedPulsePair r a A b B c₀ u E) : Mat2 :=
  fun i j => normalizedColumn (pulses j).cutoff (pulses j).component (pulses j).tangent i

noncomputable def columnScales {r a A b B c₀ u E : ℝ}
    (pulses : SignedPulsePair r a A b B c₀ u E) (ci : Vec2) : Vec2 :=
  fun j => ci j * mass (pulses j).cutoff (pulses j).component

theorem signedSlopes_abs (u : ℝ) (j : Fin 2) : |signedSlopes u j| = |u| := by
  fin_cases j <;> simp [signedSlopes]

theorem actualMatrix_factorization {r a A b B c₀ u E : ℝ}
    (pulses : SignedPulsePair r a A b B c₀ u E) (ci : Vec2) :
    actualMatrix pulses ci = FlatCovariance.columns (normalizedMatrix pulses) (columnScales pulses
      ci) := by
  ext i j
  exact congrFun ((pulses j).bounds.actualColumn_factorization (ci j) (pulses j).tangent) i

theorem columnScales_pos {r a A b B c₀ u E : ℝ}
    (pulses : SignedPulsePair r a A b B c₀ u E) {ci : Vec2} (hci : ∀ j, 0 < ci j)
    (j : Fin 2) : 0 < columnScales pulses ci j :=
  mul_pos (hci j) (pulses j).bounds.mass_pos

theorem normalizedMatrix_entry_error {r a A b B c₀ u E : ℝ}
    (pulses : SignedPulsePair r a A b B c₀ u E) (hE : 0 ≤ E) (i j : Fin 2) :
    |normalizedMatrix pulses i j - signedModel c₀ u i j| ≤
      (E + ((|c₀| + 1) * |u|) * concentrationConstant a A b B) / r := by
  have hi := (pulses j).bounds.normalizedColumn_error
    (pulses j).tangent_continuous hE (pulses j).tangent_model i
  unfold normalizedMatrix signedModel
  simpa only [signedSlopes_abs] using hi

theorem actualMatrix_positive_of_normalized {r a A b B c₀ u E : ℝ}
    (pulses : SignedPulsePair r a A b B c₀ u E) {ci : Vec2} (hci : ∀ j, 0 < ci j)
    (T : Vec2) (hdet : (normalizedMatrix pulses).det ≠ 0)
    (hw : ∀ i, 0 < SmoothCovariance.weights (normalizedMatrix pulses) T i) :
    (actualMatrix pulses ci).det ≠ 0 ∧
      (∀ i, 0 < SmoothCovariance.weights (actualMatrix pulses ci) T i) ∧
      (∀ i, 0 < SmoothCovariance.amplitudes (actualMatrix pulses ci) T i) := by
  have hs : ∀ j, 0 < columnScales pulses ci j := columnScales_pos pulses hci
  have hsn : ∀ j, columnScales pulses ci j ≠ 0 := fun j => (hs j).ne'
  have hT : FlatCovariance.scaledTarget 1 T = T := by
    ext i
    simp [FlatCovariance.scaledTarget]
  rw [actualMatrix_factorization]
  have hweight : ∀ i, 0 < SmoothCovariance.weights
      (FlatCovariance.columns (normalizedMatrix pulses) (columnScales pulses ci)) T i := by
    intro i
    rw [← hT, FlatCovariance.weights_columns _ _ _ _ hdet hsn]
    exact mul_pos (div_pos zero_lt_one (hs i)) (hw i)
  exact ⟨FlatCovariance.columns_det_ne_zero hdet hsn, hweight,
    fun i => Real.sqrt_pos.mpr (hweight i)⟩

/- This is the same entrywise norm used by SmoothCovariance's compact
perturbation theorem. -/
local instance : NormedAddCommGroup Mat2 :=
  inferInstanceAs (NormedAddCommGroup (Fin 2 → Fin 2 → ℝ))

local instance : NormedSpace ℝ Mat2 :=
  inferInstanceAs (NormedSpace ℝ (Fin 2 → Fin 2 → ℝ))

/-- A uniform slot threshold for the actual signed pulse pair over a compact
strict-cone family.  Its matrix approximation is a conclusion of the Gaussian
moment and pointwise tangent estimates in `TangentPulse`, not a hypothesis. -/
theorem compact_actual_positive_inverse
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {c₀ u : X → ℝ} {T : X → Vec2}
    (hmodel : ∀ i j, ContinuousOn (fun p => signedModel (c₀ p) (u p) i j) K)
    (hT : ∀ i, ContinuousOn (fun p => T p i) K)
    (hcone : ∀ p ∈ K, SmoothCovariance.StrictCone (signedModel (c₀ p) (u p)) (T p))
    {a A b B E C U : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hc₀ : ∀ p ∈ K, |c₀ p| ≤ C) (hu : ∀ p ∈ K, |u p| ≤ U) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ p ∈ K, ∀ r : ℝ, R ≤ r →
      ∀ pulses : SignedPulsePair r a A b B (c₀ p) (u p) E,
      ∀ ci : Vec2, (∀ j, 0 < ci j) →
        (actualMatrix pulses ci).det ≠ 0 ∧
        (∀ i, 0 < SmoothCovariance.weights (actualMatrix pulses ci) (T p) i) ∧
        (∀ i, 0 < SmoothCovariance.amplitudes (actualMatrix pulses ci) (T p) i) := by
  obtain ⟨ρ, hρ, hstable⟩ := SmoothCovariance.compact_family_perturbation_stability
    hK hmodel hT hcone
  let Q : ℝ := E + ((C + 1) * U) * |concentrationConstant a A b B|
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  refine ⟨max 1 (Q / ρ), le_max_left _ _, ?_⟩
  intro p hp r hr pulses ci hci
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hsmall : Q / r ≤ ρ := by
    apply (div_le_iff₀ hrp).mpr
    have hR : Q / ρ ≤ r := (le_max_right _ _).trans hr
    nlinarith [(div_le_iff₀ hρ).mp hR]
  have hentry (i j : Fin 2) :
      |normalizedMatrix pulses i j - signedModel (c₀ p) (u p) i j| ≤ ρ := by
    apply (normalizedMatrix_entry_error pulses hE i j).trans
    apply le_trans _ hsmall
    apply div_le_div_of_nonneg_right _ hrp.le
    dsimp [Q]
    apply add_le_add_right
    have hf : (|c₀ p| + 1) * |u p| ≤ (C + 1) * U :=
      mul_le_mul (add_le_add_left (hc₀ p hp) 1) (hu p hp)
        (abs_nonneg _) (by linarith)
    exact mul_le_mul hf (le_abs_self _)
      (pulses j).bounds.concentrationConstant_nonneg
      (mul_nonneg (by linarith) hU)
  have hdist : dist (normalizedMatrix pulses, T p) (signedModel (c₀ p) (u p), T p) ≤ ρ := by
    rw [dist_prod_same_right]
    apply (dist_pi_le_iff hρ.le).mpr
    intro i
    apply (dist_pi_le_iff hρ.le).mpr
    intro j
    simpa only [Real.dist_eq] using hentry i j
  obtain ⟨hd, hw, _⟩ := hstable p hp (normalizedMatrix pulses) (T p) hdist
  exact actualMatrix_positive_of_normalized pulses hci (T p) hd hw

/-- Scalar cone inequalities and continuity of the four scalar model data
suffice.  Compactness supplies both the uniform cone tolerance and the uniform
bounds on `c₀,u`, hence one slot threshold for every actual pulse pair. -/
theorem compact_actual_positive_inverse_of_scalar_cone
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {c₀ u m t : X → ℝ} (hc₀ : ContinuousOn c₀ K) (hu : ContinuousOn u K)
    (hm : ContinuousOn m K) (ht : ContinuousOn t K)
    (hc₀neg : ∀ p ∈ K, c₀ p < 0) (hupos : ∀ p ∈ K, 0 < u p)
    (hcone : ∀ p ∈ K, |Covariance.normalMagnitude (c₀ p) (u p) * t p| < u p * m p)
    {a A b B E : ℝ} (hE : 0 ≤ E) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ p ∈ K, ∀ r : ℝ, R ≤ r →
      ∀ pulses : SignedPulsePair r a A b B (c₀ p) (u p) E,
      ∀ ci : Vec2, (∀ j, 0 < ci j) →
        (actualMatrix pulses ci).det ≠ 0 ∧
        (∀ i, 0 < SmoothCovariance.weights (actualMatrix pulses ci) (Covariance.target (m p) (t p))
          i) ∧
        (∀ i, 0 < SmoothCovariance.amplitudes (actualMatrix pulses ci) (Covariance.target (m p) (t
          p)) i) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc₀
  obtain ⟨U, hU⟩ := hK.exists_bound_of_continuousOn hu
  have htarget : ∀ i, ContinuousOn (fun p => Covariance.target (m p) (t p) i) K := by
    intro i
    fin_cases i
    · simpa [Covariance.target] using hm.fun_neg
    · simpa [Covariance.target] using ht
  apply compact_actual_positive_inverse hK (signedModel_continuousOn hc₀ hu) htarget
    (fun p hp => signedModel_strictCone (hc₀neg p hp) (hupos p hp) (hcone p hp)) hE
    (le_max_left 0 C) (le_max_left 0 U)
  · intro p hp
    exact (show |c₀ p| ≤ C by simpa only [Real.norm_eq_abs] using hC p hp).trans (le_max_right _ _)
  · intro p hp
    exact (show |u p| ≤ U by simpa only [Real.norm_eq_abs] using hU p hp).trans (le_max_right _ _)

end NavierStokes.PulseCovariance
