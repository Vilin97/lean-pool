/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.KernelSegment
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Kernel Time

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

namespace CKN

open MeasureTheory Metric
open scoped ENNReal NNReal Pointwise

/-- File-level instance providing `Nontrivial (Vec d)` under `[NeZero d]`. -/
instance instNontrivialVecTimeCollapse (d : ℕ) [NeZero d] :
    Nontrivial (Vec d) := inferInstance

/-!
# Time-collapse estimates for the Riesz-kernel Poincare integrand

Collects the `intervalIntegral`-level lemmas that bound the time-averaged
segment-blend integrand against `rieszKernel`.
-/

section TimeCollapse

variable {d : ℕ} [NeZero d]

private theorem inv_natPow_eq_rpow_neg_nat {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    (a ^ n)⁻¹ = a ^ (-((n : ℕ) : ℝ)) := by
  rw [← Real.rpow_natCast, Real.rpow_neg ha]

private theorem intervalIntegral_inv_pow_if_le_mul_le_rieszAux
    {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 < R) :
    ∫ t in (0 : ℝ)..1,
      ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ρ ≤ (1 - t) * R then ρ else 0) ≤
      ((R ^ d) / (d : ℝ)) * ρ ^ (1 - (d : ℝ)) := by
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (NeZero.ne d)
  have hd_ne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne d)
  by_cases hρ_zero : ρ = 0
  · have hleft :
        ∫ t in (0 : ℝ)..1,
          ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ρ ≤ (1 - t) * R then ρ else 0) = 0 := by
      simp [hρ_zero]
    rw [hleft, hρ_zero]
    exact mul_nonneg
      (div_nonneg (pow_nonneg hR.le _) hd_pos.le)
      (Real.rpow_nonneg (by positivity) _)
  · have hρ_pos : 0 < ρ := lt_of_le_of_ne hρ (by simpa [eq_comm] using hρ_zero)
    by_cases hρ_ltR : ρ < R
    · let a : ℝ := 1 - ρ / R
      have ha_nonneg : 0 ≤ a := by
        dsimp [a]
        have hdiv_lt : ρ / R < 1 := by
          rw [div_lt_iff₀ hR]
          simpa using hρ_ltR
        linarith only [hdiv_lt]
      have ha_le_one : a ≤ 1 := by
        dsimp [a]
        have hdiv_nonneg : 0 ≤ ρ / R := by
          positivity
        linarith only [hdiv_nonneg]
      have ha_mem : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha_nonneg, ha_le_one⟩
      have hiff (t : ℝ) : ρ ≤ (1 - t) * R ↔ t ≤ a := by
        dsimp [a]
        constructor
        · intro htρ
          have hdiv : ρ / R ≤ 1 - t := by
            rw [div_le_iff₀ hR]
            simpa [mul_comm, mul_left_comm, mul_assoc] using htρ
          linarith only [hdiv]
        · intro htρ
          have hdiv : ρ / R ≤ 1 - t := by
            linarith only [htρ]
          rw [div_le_iff₀ hR] at hdiv
          simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv
      have hcongr :
          ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc (0 : ℝ) 1 →
            ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ρ ≤ (1 - t) * R then ρ else 0) =
              Set.indicator {t : ℝ | t ≤ a}
                (fun t => ((1 - t) ^ (d + 1 : ℕ))⁻¹ * ρ) t := by
        exact Filter.Eventually.of_forall fun t ht => by
          simp [Set.indicator, hiff t]
      have hrexp :
          ∫ t in (0 : ℝ)..a, ((1 - t) ^ (d + 1 : ℕ))⁻¹ =
            ∫ t in (0 : ℝ)..a, (1 - t) ^ (-((d + 1 : ℕ) : ℝ)) := by
        refine intervalIntegral.integral_congr_ae ?_
        exact Filter.Eventually.of_forall fun t ht => by
          rw [Set.uIoc_of_le ha_nonneg] at ht
          have hbase_nonneg : 0 ≤ 1 - t := by
            linarith only [ht.2, ha_le_one]
          rw [inv_natPow_eq_rpow_neg_nat hbase_nonneg]
      have hsub :
          ∫ t in (0 : ℝ)..a, (1 - t) ^ (-((d + 1 : ℕ) : ℝ)) =
            ∫ s in 1 - a..1, s ^ (-((d + 1 : ℕ) : ℝ)) := by
        simpa using
          (intervalIntegral.integral_comp_sub_left
            (f := fun s : ℝ => s ^ (-((d + 1 : ℕ) : ℝ))) (a := 0) (b := a) 1)
      have hone_sub_a_eq : 1 - a = ρ / R := by
        dsimp [a]
        ring
      have hone_sub_a_pos : 0 < 1 - a := by
        rw [hone_sub_a_eq]
        exact div_pos hρ_pos hR
      have hzero_not_mem : (0 : ℝ) ∉ Set.uIcc (1 - a) (1 : ℝ) := by
        rw [Set.uIcc_of_le (by linarith only [ha_nonneg] : 1 - a ≤ (1 : ℝ))]
        simp [not_le.mpr hone_sub_a_pos]
      have hexp_ne : (-((d + 1 : ℕ) : ℝ)) ≠ -1 := by
        intro h
        have h_cast : ((d + 1 : ℕ) : ℝ) = 1 := by
          linarith only [h]
        have h_nat : d + 1 = 1 := by
          exact_mod_cast h_cast
        have hdzero_nat : d = 0 := by
          omega
        have hdzero : (d : ℝ) = 0 := by
          exact_mod_cast hdzero_nat
        exact hd_ne hdzero
      have hpow_formula :
          ∫ s in 1 - a..1, s ^ (-((d + 1 : ℕ) : ℝ)) =
            ((1 - a) ^ (-(d : ℝ)) - 1) / (d : ℝ) := by
        calc
          ∫ s in 1 - a..1, s ^ (-((d + 1 : ℕ) : ℝ))
              = (1 ^ (-(d : ℝ)) - (1 - a) ^ (-(d : ℝ))) / (-(d : ℝ)) := by
                  simpa using
                    (integral_rpow (a := 1 - a) (b := (1 : ℝ))
                      (r := -((d + 1 : ℕ) : ℝ)) (Or.inr ⟨hexp_ne, hzero_not_mem⟩))
          _ = ((1 - a) ^ (-(d : ℝ)) - 1) / (d : ℝ) := by
                have h_one : (1 : ℝ) ^ (-(d : ℝ)) = 1 := by simp
                rw [h_one]
                field_simp [hd_ne]
                ring
      have hratio :
          (ρ / R) ^ (-(d : ℝ)) = (R ^ d : ℝ) / (ρ ^ d : ℝ) := by
        calc
          (ρ / R) ^ (-(d : ℝ)) = ((ρ / R) ^ (d : ℝ))⁻¹ := by
            rw [Real.rpow_neg (by positivity : 0 ≤ ρ / R)]
          _ = ((ρ ^ d : ℝ) / (R ^ d : ℝ))⁻¹ := by
                rw [Real.div_rpow hρ hR.le, Real.rpow_natCast, Real.rpow_natCast]
          _ = (R ^ d : ℝ) / (ρ ^ d : ℝ) := by
                field_simp [hρ_pos.ne', hR.ne']
      have hρ_rpow :
          ρ ^ (1 - (d : ℝ)) = ρ / (ρ ^ d : ℝ) := by
        calc
          ρ ^ (1 - (d : ℝ)) = ρ ^ (1 : ℝ) * ρ ^ (-(d : ℝ)) := by
            rw [show (1 - (d : ℝ)) = (1 : ℝ) + (-(d : ℝ)) by ring, Real.rpow_add hρ_pos]
          _ = ρ * ((ρ ^ d : ℝ)⁻¹) := by
                rw [Real.rpow_one, Real.rpow_neg hρ, Real.rpow_natCast]
          _ = ρ / (ρ ^ d : ℝ) := by
                ring
      calc
        ∫ t in (0 : ℝ)..1,
            ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ρ ≤ (1 - t) * R then ρ else 0)
            = ∫ t in (0 : ℝ)..a, ((1 - t) ^ (d + 1 : ℕ))⁻¹ * ρ := by
                rw [intervalIntegral.integral_congr_ae hcongr]
                simpa using
                  (intervalIntegral.integral_indicator
                    (μ := MeasureTheory.volume)
                    (f := fun t => ((1 - t) ^ (d + 1 : ℕ))⁻¹ * ρ) ha_mem)
        _ = ρ * ∫ t in (0 : ℝ)..a, ((1 - t) ^ (d + 1 : ℕ))⁻¹ := by
              rw [intervalIntegral.integral_mul_const, mul_comm]
        _ = ρ * ∫ t in (0 : ℝ)..a, (1 - t) ^ (-((d + 1 : ℕ) : ℝ)) := by
              rw [hrexp]
        _ = ρ * ∫ s in 1 - a..1, s ^ (-((d + 1 : ℕ) : ℝ)) := by
              rw [hsub]
        _ = ρ * (((1 - a) ^ (-(d : ℝ)) - 1) / (d : ℝ)) := by
              rw [hpow_formula]
        _ ≤ ρ * (((1 - a) ^ (-(d : ℝ))) / (d : ℝ)) := by
              refine mul_le_mul_of_nonneg_left ?_ hρ
              have hrpow_nonneg : 0 ≤ (1 - a) ^ (-(d : ℝ)) :=
                Real.rpow_nonneg (le_of_lt hone_sub_a_pos) _
              have hsub_le : (1 - a) ^ (-(d : ℝ)) - 1 ≤ (1 - a) ^ (-(d : ℝ)) := by
                linarith only [hrpow_nonneg]
              exact div_le_div_of_nonneg_right hsub_le hd_pos.le
        _ = ρ * (((ρ / R) ^ (-(d : ℝ))) / (d : ℝ)) := by
              rw [hone_sub_a_eq]
        _ = ρ * ((((R ^ d : ℝ) / (ρ ^ d : ℝ))) / (d : ℝ)) := by
              rw [hratio]
        _ = ((R ^ d) / (d : ℝ)) * (ρ / (ρ ^ d : ℝ)) := by
              rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
              ring
        _ = ((R ^ d) / (d : ℝ)) * ρ ^ (1 - (d : ℝ)) := by
              rw [hρ_rpow]
    · have hR_le_ρ : R ≤ ρ := le_of_not_gt hρ_ltR
      have hleft_zero :
          ∫ t in (0 : ℝ)..1,
            ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ρ ≤ (1 - t) * R then ρ else 0) = 0 := by
        refine intervalIntegral.integral_zero_ae ?_
        exact Filter.Eventually.of_forall fun t ht => by
          rw [Set.uIoc_of_le zero_le_one] at ht
          have hrad_lt : (1 - t) * R < R := by
            nlinarith only [ht.1, hR]
          have hnot : ¬ ρ ≤ (1 - t) * R := by
            intro hle
            exact not_le_of_gt hrad_lt (le_trans hR_le_ρ hle)
          simp [hnot]
      rw [hleft_zero]
      exact mul_nonneg
        (div_nonneg (pow_nonneg hR.le _) hd_pos.le)
        (Real.rpow_nonneg hρ _)

omit [NeZero d] in
private theorem intervalIntegrable_inv_pow_if_le_mul
    {ρ R c : ℝ} (_ : 0 ≤ c) (hρ : 0 ≤ ρ) (hR : 0 < R) :
    IntervalIntegrable
      (fun t : ℝ =>
        ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ρ ≤ (1 - t) * R then c * ρ else 0))
      MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  by_cases hρ_zero : ρ = 0
  · simp [hρ_zero]
  · have hρ_pos : 0 < ρ := lt_of_le_of_ne hρ (by simpa [eq_comm] using hρ_zero)
    by_cases hρ_ltR : ρ < R
    · let a : ℝ := 1 - ρ / R
      let g : ℝ → ℝ := fun t => ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (c * ρ)
      have ha_nonneg : 0 ≤ a := by
        dsimp [a]
        have hdiv_lt : ρ / R < 1 := by
          rw [div_lt_iff₀ hR]
          simpa using hρ_ltR
        linarith only [hdiv_lt]
      have ha_lt_one : a < 1 := by
        dsimp [a]
        have hdiv_pos : 0 < ρ / R := div_pos hρ_pos hR
        linarith only [hdiv_pos]
      have ha_le_one : a ≤ 1 := ha_lt_one.le
      have hiff (t : ℝ) : ρ ≤ (1 - t) * R ↔ t ≤ a := by
        dsimp [a]
        constructor
        · intro htρ
          have hdiv : ρ / R ≤ 1 - t := by
            rw [div_le_iff₀ hR]
            simpa [mul_comm, mul_left_comm, mul_assoc] using htρ
          linarith only [hdiv]
        · intro htρ
          have hdiv : ρ / R ≤ 1 - t := by
            linarith only [htρ]
          rw [div_le_iff₀ hR] at hdiv
          simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv
      have hg_cont_pow :
          ContinuousOn (fun t : ℝ => ((1 - t) ^ (d + 1 : ℕ) : ℝ)) (Set.Icc (0 : ℝ) a) := by
        fun_prop
      have hg_cont_inv :
          ContinuousOn (fun t : ℝ => (((1 - t) ^ (d + 1 : ℕ) : ℝ)⁻¹) ) (Set.Icc (0 : ℝ) a) := by
        refine hg_cont_pow.inv₀ ?_
        intro t ht
        have hbase_pos : 0 < 1 - t := by
          linarith only [ht.2, ha_lt_one]
        exact pow_ne_zero _ (ne_of_gt hbase_pos)
      have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) a) := by
        exact hg_cont_inv.mul continuousOn_const
      have hg_int_Icc : MeasureTheory.IntegrableOn g (Set.Icc (0 : ℝ) a) MeasureTheory.volume :=
        hg_cont.integrableOn_compact isCompact_Icc
      have hg_int : MeasureTheory.IntegrableOn g (Set.Ioc (0 : ℝ) a) MeasureTheory.volume :=
        hg_int_Icc.mono_set (by
          intro t ht
          exact ⟨ht.1.le, ht.2⟩)
      have hleft_eq :
          Set.EqOn
            (fun t : ℝ =>
              ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ρ ≤ (1 - t) * R then c * ρ else 0))
            g
            (Set.Ioc (0 : ℝ) a) := by
        intro t ht
        have hcond : ρ ≤ (1 - t) * R := (hiff t).2 ht.2
        simp [g, hcond]
      have hleft_int :
          MeasureTheory.IntegrableOn
            (fun t : ℝ =>
              ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ρ ≤ (1 - t) * R then c * ρ else 0))
            (Set.Ioc (0 : ℝ) a) MeasureTheory.volume :=
        hg_int.congr_fun hleft_eq.symm measurableSet_Ioc
      have hright_zero :
          Set.EqOn
            (fun t : ℝ =>
              ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ρ ≤ (1 - t) * R then c * ρ else 0))
            (fun _ : ℝ => 0)
            (Set.Ioc a 1) := by
        intro t ht
        have hnot : ¬ ρ ≤ (1 - t) * R := by
          intro hle
          exact not_le_of_gt ht.1 ((hiff t).1 hle)
        simp [hnot]
      have hright_int :
          MeasureTheory.IntegrableOn
            (fun t : ℝ =>
              ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ρ ≤ (1 - t) * R then c * ρ else 0))
            (Set.Ioc a 1) MeasureTheory.volume := by
        exact
          (MeasureTheory.integrableOn_const (s := Set.Ioc a 1) (C := (0 : ℝ))
            (hs := measure_Ioc_lt_top.ne)).congr_fun
            hright_zero.symm measurableSet_Ioc
      have hunion : Set.Ioc (0 : ℝ) a ∪ Set.Ioc a 1 = Set.Ioc (0 : ℝ) 1 := by
        ext t
        constructor
        · intro ht
          rcases ht with ht | ht
          on_goal 1 => exact ⟨ht.1, le_trans ht.2 ha_le_one⟩
          exact ⟨lt_of_le_of_lt ha_nonneg ht.1, ht.2⟩
        · intro ht
          by_cases hta : t ≤ a
          · exact Or.inl ⟨ht.1, hta⟩
          · exact Or.inr ⟨lt_of_not_ge hta, ht.2⟩
      simpa [hunion] using hleft_int.union hright_int
    · have hR_le_ρ : R ≤ ρ := le_of_not_gt hρ_ltR
      have hzero :
          Set.EqOn
            (fun t : ℝ =>
              ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ρ ≤ (1 - t) * R then c * ρ else 0))
            (fun _ : ℝ => 0)
            (Set.Ioc (0 : ℝ) 1) := by
        intro t ht
        have hrad_lt : (1 - t) * R < R := by
          nlinarith only [ht.1, hR]
        have hnot : ¬ ρ ≤ (1 - t) * R := by
          intro hle
          exact not_le_of_gt hrad_lt (le_trans hR_le_ρ hle)
        simp [hnot]
      exact (MeasureTheory.integrableOn_const (s := Set.Ioc (0 : ℝ) 1) (C := (0 : ℝ))
        (hs := measure_Ioc_lt_top.ne)).congr_fun
        hzero.symm measurableSet_Ioc

theorem intervalIntegral_inv_pow_if_norm_sub_le_mul_le_rieszKernel
    {x z : Vec d} {R : ℝ} (hR : 0 < R) :
    ∫ t in (0 : ℝ)..1,
      ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ‖x - z‖ ≤ (1 - t) * R then ‖x - z‖ else 0) ≤
      ((R ^ d) / (d : ℝ)) * rieszKernel x z := by
  simpa [rieszKernel] using
    intervalIntegral_inv_pow_if_le_mul_le_rieszAux (d := d)
      (ρ := ‖x - z‖) (R := R) (norm_nonneg _) hR

private theorem setIntegral_inv_pow_if_norm_sub_le_mul_le_rieszKernel
    {x z : Vec d} {R : ℝ} (hR : 0 < R) :
    ∫ t in Set.Ioc (0 : ℝ) 1,
      ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ‖x - z‖ ≤ (1 - t) * R then ‖x - z‖ else 0)
        ∂MeasureTheory.volume ≤
      ((R ^ d) / (d : ℝ)) * rieszKernel x z := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  exact intervalIntegral_inv_pow_if_norm_sub_le_mul_le_rieszKernel (d := d) (x := x) (z := z) hR

omit [NeZero d] in
private theorem integrable_restrict_Ioc_inv_pow_if_norm_sub_le_mul
    {x z : Vec d} {R : ℝ} (hR : 0 < R) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ‖x - z‖ ≤ (1 - t) * R then ‖x - z‖ else 0))
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  change MeasureTheory.IntegrableOn
    (fun t : ℝ =>
      ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ‖x - z‖ ≤ (1 - t) * R then ‖x - z‖ else 0))
    (Set.Ioc (0 : ℝ) 1) MeasureTheory.volume
  have htmp :
      IntervalIntegrable
        (fun t : ℝ =>
          ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ‖x - z‖ ≤ (1 - t) * R then ‖x - z‖ else 0))
        MeasureTheory.volume 0 1 := by
    simpa using
      (intervalIntegrable_inv_pow_if_le_mul (d := d) (ρ := ‖x - z‖) (R := R) (c := (1 : ℝ))
        zero_le_one (norm_nonneg _) hR)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 htmp

omit [NeZero d] in
private theorem integrable_rieszKernel_withDensity_of_integrableOn_mul_rieszKernel
    {U : Set (Vec d)} {x : Vec d} {φ : Vec d → ℝ}
    (hφ_nonneg : ∀ z, 0 ≤ φ z)
    (hφ_meas : AEMeasurable φ (MeasureTheory.volume.restrict U))
    (hφK_int :
      MeasureTheory.IntegrableOn
        (fun z => φ z * rieszKernel x z) U MeasureTheory.volume) :
    let μU : MeasureTheory.Measure (Vec d) :=
      (MeasureTheory.volume.restrict U).withDensity (fun z => ENNReal.ofReal (φ z))
    MeasureTheory.Integrable (fun z => rieszKernel x z) μU := by
  dsimp
  rw [MeasureTheory.integrable_withDensity_iff_integrable_smul₀'
    (μ := MeasureTheory.volume.restrict U)
    (f := fun z => ENNReal.ofReal (φ z))
    (g := fun z => rieszKernel x z)]
  · simpa [MeasureTheory.IntegrableOn, smul_eq_mul, hφ_nonneg] using hφK_int
  · simpa using hφ_meas.ennreal_ofReal
  · exact Filter.Eventually.of_forall (fun z => by simp)

omit [NeZero d] in
private theorem measurable_timeCollapseKernel
    {x : Vec d} {R : ℝ} :
    Measurable (fun p : Vec d × ℝ =>
      ((1 - p.2) ^ (d + 1 : ℕ))⁻¹ *
        (if ‖x - p.1‖ ≤ (1 - p.2) * R then ‖x - p.1‖ else 0)) := by
  let s : Set (Vec d × ℝ) := {p : Vec d × ℝ | ‖x - p.1‖ ≤ (1 - p.2) * R}
  have hs : MeasurableSet s := by
    dsimp [s]
    exact (isClosed_le ((continuous_const.sub continuous_fst).norm)
      ((continuous_const.sub continuous_snd).mul continuous_const)).measurableSet
  have hg : Measurable (fun p : Vec d × ℝ =>
      ((1 - p.2) ^ (d + 1 : ℕ))⁻¹ * ‖x - p.1‖) := by
    fun_prop
  simpa [s, Set.indicator, Pi.zero_apply] using! hg.indicator hs

private theorem integrable_timeCollapseKernel_withDensity
    {U : Set (Vec d)} {x : Vec d} {R : ℝ} (hR : 0 < R)
    {φ : Vec d → ℝ}
    (hφ_nonneg : ∀ z, 0 ≤ φ z)
    (hφ_meas : AEMeasurable φ (MeasureTheory.volume.restrict U))
    (hφK_int :
      MeasureTheory.IntegrableOn
        (fun z => φ z * rieszKernel x z) U MeasureTheory.volume) :
    let μU : MeasureTheory.Measure (Vec d) :=
      (MeasureTheory.volume.restrict U).withDensity (fun z => ENNReal.ofReal (φ z))
    let μI : MeasureTheory.Measure ℝ :=
      MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)
    MeasureTheory.Integrable
      (fun p : Vec d × ℝ =>
        ((1 - p.2) ^ (d + 1 : ℕ))⁻¹ *
          (if ‖x - p.1‖ ≤ (1 - p.2) * R then ‖x - p.1‖ else 0))
      (μU.prod μI) := by
  dsimp
  let F : Vec d × ℝ → ℝ := fun p =>
    ((1 - p.2) ^ (d + 1 : ℕ))⁻¹ *
      (if ‖x - p.1‖ ≤ (1 - p.2) * R then ‖x - p.1‖ else 0)
  have hF_meas : Measurable F := measurable_timeCollapseKernel (d := d) (x := x) (R := R)
  have hsections :
      ∀ᵐ z ∂(MeasureTheory.volume.restrict U).withDensity (fun z => ENNReal.ofReal (φ z)),
        MeasureTheory.Integrable
          (fun t => F (z, t))
          (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine Filter.Eventually.of_forall ?_
    intro z
    simpa [F] using
      integrable_restrict_Ioc_inv_pow_if_norm_sub_le_mul (d := d) (x := x) (z := z) hR
  have hkernel_int :
      MeasureTheory.Integrable
        (fun z => rieszKernel x z)
        ((MeasureTheory.volume.restrict U).withDensity (fun z => ENNReal.ofReal (φ z))) :=
    integrable_rieszKernel_withDensity_of_integrableOn_mul_rieszKernel
      (hφ_nonneg := hφ_nonneg) (hφ_meas := hφ_meas) (hφK_int := hφK_int)
  have hright :
      MeasureTheory.Integrable
        (fun z => ((R ^ d) / (d : ℝ)) * rieszKernel x z)
        ((MeasureTheory.volume.restrict U).withDensity (fun z => ENNReal.ofReal (φ z))) := by
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hkernel_int.const_mul ((R ^ d) / (d : ℝ))
  have hpointwise :
      (fun z =>
        ∫ t, ‖F (z, t)‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))) ≤ᵐ[
          (MeasureTheory.volume.restrict U).withDensity (fun z => ENNReal.ofReal (φ z))]
        (fun z => ((R ^ d) / (d : ℝ)) * rieszKernel x z) := by
    refine Filter.Eventually.of_forall ?_
    intro z
    change
      ∫ t in Set.Ioc (0 : ℝ) 1, ‖F (z, t)‖ ∂MeasureTheory.volume ≤
        ((R ^ d) / (d : ℝ)) * rieszKernel x z
    have hnorm_eq :
        Set.EqOn
          (fun t : ℝ => ‖F (z, t)‖)
          (fun t : ℝ =>
            ((1 - t) ^ (d + 1 : ℕ))⁻¹ * (if ‖x - z‖ ≤ (1 - t) * R then ‖x - z‖ else 0))
          (Set.Ioc (0 : ℝ) 1) := by
      intro t ht
      by_cases hcond : ‖x - z‖ ≤ (1 - t) * R
      · have hnonneg :
            0 ≤ ((1 - t) ^ (d + 1 : ℕ))⁻¹ * ‖x - z‖ := by
          have hbase_nonneg : 0 ≤ 1 - t := by
            linarith only [ht.2]
          exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hbase_nonneg _)) (norm_nonneg _)
        simp [F, hcond, Real.norm_of_nonneg hnonneg]
      · simp [F, hcond]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hnorm_eq]
    exact setIntegral_inv_pow_if_norm_sub_le_mul_le_rieszKernel (d := d) (x := x) (z := z) hR
  have hleft_aestronglyMeasurable :
      AEStronglyMeasurable
        (fun z =>
          ∫ t, ‖F (z, t)‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
        ((MeasureTheory.volume.restrict U).withDensity (fun z => ENNReal.ofReal (φ z))) := by
    exact hF_meas.norm.aemeasurable.aestronglyMeasurable.integral_prod_right'
  have hleft_bound :
      ∀ᵐ z ∂((MeasureTheory.volume.restrict U).withDensity (fun z => ENNReal.ofReal (φ z))),
        ‖∫ t, ‖F (z, t)‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))‖ ≤
          ((R ^ d) / (d : ℝ)) * rieszKernel x z := by
    filter_upwards [hpointwise] with z hz
    have hnonneg :
        0 ≤ ∫ t, ‖F (z, t)‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      exact MeasureTheory.integral_nonneg (fun t => norm_nonneg _)
    calc
      ‖∫ t, ‖F (z, t)‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))‖
          = ∫ t, ‖F (z, t)‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
              rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      _ ≤ ((R ^ d) / (d : ℝ)) * rieszKernel x z := hz
  have houter :
      MeasureTheory.Integrable
        (fun z =>
          ∫ t, ‖F (z, t)‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
        ((MeasureTheory.volume.restrict U).withDensity (fun z => ENNReal.ofReal (φ z))) :=
    hright.mono' hleft_aestronglyMeasurable hleft_bound
  exact (MeasureTheory.integrable_prod_iff (μ := (MeasureTheory.volume.restrict U).withDensity
      (fun z => ENNReal.ofReal (φ z)))
      (ν := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))
      hF_meas.aestronglyMeasurable).2 ⟨hsections, houter⟩

omit [NeZero d] in
private theorem setIntegral_indicator_closedBall_eq_setIntegral_inter_closedBall
    {U : Set (Vec d)} {x : Vec d} {r : ℝ} {ψ : Vec d → ℝ} :
    ∫ z in U, (Metric.closedBall x r).indicator (fun z => ψ z * ‖x - z‖) z
      ∂MeasureTheory.volume =
      ∫ z in U ∩ Metric.closedBall x r, ψ z * ‖x - z‖ ∂MeasureTheory.volume := by
  simpa using
    (MeasureTheory.setIntegral_indicator (μ := MeasureTheory.volume) (s := U)
      (t := Metric.closedBall x r) (f := fun z => ψ z * ‖x - z‖) measurableSet_closedBall)

theorem setIntegral_inv_pow_setIntegral_inter_closedBall_le_rieszKernel
    {U : Set (Vec d)} (hU_meas : MeasurableSet U)
    {x : Vec d} {R : ℝ} (hR : 0 < R) {φ : Vec d → ℝ}
    (hφ_nonneg : ∀ z, 0 ≤ φ z)
    (hφ_meas : AEMeasurable φ (MeasureTheory.volume.restrict U))
    (hφK_int :
      MeasureTheory.IntegrableOn
        (fun z => φ z * rieszKernel x z) U MeasureTheory.volume) :
    ∫ t in Set.Ioc (0 : ℝ) 1,
      ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
        ∫ z in U ∩ Metric.closedBall x ((1 - t) * R), φ z * ‖x - z‖
          ∂MeasureTheory.volume
      ≤
      ((R ^ d) / (d : ℝ)) *
        ∫ z in U, φ z * rieszKernel x z ∂MeasureTheory.volume := by
  let μU : MeasureTheory.Measure (Vec d) :=
    (MeasureTheory.volume.restrict U).withDensity (fun z => ENNReal.ofReal (φ z))
  let μI : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)
  let C : ℝ := (R ^ d) / (d : ℝ)
  let F : Vec d × ℝ → ℝ := fun p =>
    ((1 - p.2) ^ (d + 1 : ℕ))⁻¹ *
      (if ‖x - p.1‖ ≤ (1 - p.2) * R then ‖x - p.1‖ else 0)
  have hprod_int : MeasureTheory.Integrable F (μU.prod μI) := by
    simpa [μU, μI, F] using
      integrable_timeCollapseKernel_withDensity (d := d) (x := x) (R := R) hR
        (hφ_nonneg := hφ_nonneg) (hφ_meas := hφ_meas) (hφK_int := hφK_int)
  have hkernel_int : MeasureTheory.Integrable (fun z => rieszKernel x z) μU := by
    simpa [μU] using
      integrable_rieszKernel_withDensity_of_integrableOn_mul_rieszKernel
        (hφ_nonneg := hφ_nonneg) (hφ_meas := hφ_meas) (hφK_int := hφK_int)
  have hright_int : MeasureTheory.Integrable (fun z => C * rieszKernel x z) μU := by
    simpa [C, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hkernel_int.const_mul C
  have hinner_bound :
      (fun z => ∫ t, F (z, t) ∂μI) ≤ᵐ[μU]
        (fun z => C * rieszKernel x z) := by
    refine Filter.Eventually.of_forall ?_
    intro z
    change
      ∫ t in Set.Ioc (0 : ℝ) 1,
        ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
          (if ‖x - z‖ ≤ (1 - t) * R then ‖x - z‖ else 0)
        ∂MeasureTheory.volume ≤
        C * rieszKernel x z
    simpa [C] using
      setIntegral_inv_pow_if_norm_sub_le_mul_le_rieszKernel (d := d) (x := x) (z := z) hR
  have hleft_int : MeasureTheory.Integrable (fun z => ∫ t, F (z, t) ∂μI) μU :=
    hprod_int.integral_prod_left
  have hcollapse :
      ∫ z, ∫ t, F (z, t) ∂μI ∂μU ≤ ∫ z, C * rieszKernel x z ∂μU := by
    exact MeasureTheory.integral_mono_ae hleft_int hright_int hinner_bound
  have hinner_eq (t : ℝ) :
      ∫ z, F (z, t) ∂μU =
        ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
          ∫ z in U ∩ Metric.closedBall x ((1 - t) * R), φ z * ‖x - z‖
            ∂MeasureTheory.volume := by
    have htop :
        ∀ᵐ z ∂(MeasureTheory.volume.restrict U), ENNReal.ofReal (φ z) < ∞ := by
      exact Filter.Eventually.of_forall (fun z => by simp)
    calc
      ∫ z, F (z, t) ∂μU
          = ∫ z in U, φ z * F (z, t) ∂MeasureTheory.volume := by
              simpa [μU, smul_eq_mul, hφ_nonneg] using
                (integral_withDensity_eq_integral_toReal_smul₀
                  (μ := MeasureTheory.volume.restrict U)
                  (f_meas := hφ_meas.ennreal_ofReal)
                  (hf_lt_top := htop)
                  (g := fun z => F (z, t)))
      _ = ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
            ∫ z in U, (Metric.closedBall x ((1 - t) * R)).indicator
              (fun z => φ z * ‖x - z‖) z ∂MeasureTheory.volume := by
              have hEq :
                  Set.EqOn
                    (fun z => φ z * F (z, t))
                    (fun z =>
                      ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
                        (Metric.closedBall x ((1 - t) * R)).indicator
                          (fun z => φ z * ‖x - z‖) z)
                    U := by
                  intro z hz
                  by_cases hcond : ‖x - z‖ ≤ (1 - t) * R
                  · have hball : z ∈ Metric.closedBall x ((1 - t) * R) := by
                      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hcond
                    simp [F, hcond, hball]
                    ring
                  · have hball : z ∉ Metric.closedBall x ((1 - t) * R) := by
                      intro hzball
                      exact hcond (by
                        simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hzball)
                    simp [F, hcond, hball]
              simpa [MeasureTheory.integral_const_mul] using
                (MeasureTheory.setIntegral_congr_fun hU_meas hEq)
      _ = ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
            ∫ z in U ∩ Metric.closedBall x ((1 - t) * R), φ z * ‖x - z‖
              ∂MeasureTheory.volume := by
              rw [setIntegral_indicator_closedBall_eq_setIntegral_inter_closedBall]
  have houter_eq :
      ∫ t, ∫ z, F (z, t) ∂μU ∂μI =
        ∫ t in Set.Ioc (0 : ℝ) 1,
          ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
            ∫ z in U ∩ Metric.closedBall x ((1 - t) * R), φ z * ‖x - z‖
              ∂MeasureTheory.volume ∂MeasureTheory.volume := by
    simpa [μI] using
      (MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => hinner_eq t))
  have hright_eq :
      ∫ z, C * rieszKernel x z ∂μU =
        C * ∫ z in U, φ z * rieszKernel x z ∂MeasureTheory.volume := by
    have htop :
        ∀ᵐ z ∂(MeasureTheory.volume.restrict U), ENNReal.ofReal (φ z) < ∞ := by
      exact Filter.Eventually.of_forall (fun z => by simp)
    calc
      ∫ z, C * rieszKernel x z ∂μU
          = ∫ z in U, φ z * (C * rieszKernel x z) ∂MeasureTheory.volume := by
              simpa [μU, smul_eq_mul, hφ_nonneg] using
                (integral_withDensity_eq_integral_toReal_smul₀
                  (μ := MeasureTheory.volume.restrict U)
                  (f_meas := hφ_meas.ennreal_ofReal)
                  (hf_lt_top := htop)
                  (g := fun z => C * rieszKernel x z))
      _ = ∫ z in U, C * (φ z * rieszKernel x z) ∂MeasureTheory.volume := by
            refine MeasureTheory.setIntegral_congr_fun hU_meas ?_
            intro z hz
            ring
      _ = C * ∫ z in U, φ z * rieszKernel x z ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
  calc
    ∫ t in Set.Ioc (0 : ℝ) 1,
        ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
          ∫ z in U ∩ Metric.closedBall x ((1 - t) * R), φ z * ‖x - z‖
            ∂MeasureTheory.volume ∂MeasureTheory.volume
        = ∫ t, ∫ z, F (z, t) ∂μU ∂μI := by
            rw [houter_eq]
    _ = ∫ z, ∫ t, F (z, t) ∂μI ∂μU := by
          exact (MeasureTheory.integral_integral_swap hprod_int).symm
    _ ≤ ∫ z, C * rieszKernel x z ∂μU := hcollapse
    _ = C * ∫ z in U, φ z * rieszKernel x z ∂MeasureTheory.volume := hright_eq
    _ = ((R ^ d) / (d : ℝ)) *
          ∫ z in U, φ z * rieszKernel x z ∂MeasureTheory.volume := by
            simp [C]

theorem intervalIntegrable_inv_pow_setIntegral_inter_closedBall
    {U : Set (Vec d)} (hU_meas : MeasurableSet U)
    {x : Vec d} {R : ℝ} (hR : 0 < R) {φ : Vec d → ℝ}
    (hφ_nonneg : ∀ z, 0 ≤ φ z)
    (hφ_meas : AEMeasurable φ (MeasureTheory.volume.restrict U))
    (hφK_int :
      MeasureTheory.IntegrableOn
        (fun z => φ z * rieszKernel x z) U MeasureTheory.volume) :
    IntervalIntegrable
      (fun t =>
        ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
          ∫ z in U ∩ Metric.closedBall x ((1 - t) * R), φ z * ‖x - z‖
            ∂MeasureTheory.volume)
      MeasureTheory.volume 0 1 := by
  let μU : MeasureTheory.Measure (Vec d) :=
    (MeasureTheory.volume.restrict U).withDensity (fun z => ENNReal.ofReal (φ z))
  let μI : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)
  let F : Vec d × ℝ → ℝ := fun p =>
    ((1 - p.2) ^ (d + 1 : ℕ))⁻¹ *
      (if ‖x - p.1‖ ≤ (1 - p.2) * R then ‖x - p.1‖ else 0)
  have hprod_int : MeasureTheory.Integrable F (μU.prod μI) := by
    simpa [μU, μI, F] using
      integrable_timeCollapseKernel_withDensity (d := d) (x := x) (R := R) hR
        (hφ_nonneg := hφ_nonneg) (hφ_meas := hφ_meas) (hφK_int := hφK_int)
  have houter_int : MeasureTheory.Integrable (fun t => ∫ z, F (z, t) ∂μU) μI :=
    hprod_int.integral_prod_right
  have hinner_eq (t : ℝ) :
      ∫ z, F (z, t) ∂μU =
        ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
          ∫ z in U ∩ Metric.closedBall x ((1 - t) * R), φ z * ‖x - z‖
            ∂MeasureTheory.volume := by
    have htop :
        ∀ᵐ z ∂(MeasureTheory.volume.restrict U), ENNReal.ofReal (φ z) < ∞ := by
      exact Filter.Eventually.of_forall (fun z => by simp)
    calc
      ∫ z, F (z, t) ∂μU
          = ∫ z in U, φ z * F (z, t) ∂MeasureTheory.volume := by
              simpa [μU, smul_eq_mul, hφ_nonneg] using
                (integral_withDensity_eq_integral_toReal_smul₀
                  (μ := MeasureTheory.volume.restrict U)
                  (f_meas := hφ_meas.ennreal_ofReal)
                  (hf_lt_top := htop)
                  (g := fun z => F (z, t)))
      _ = ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
            ∫ z in U, (Metric.closedBall x ((1 - t) * R)).indicator
              (fun z => φ z * ‖x - z‖) z ∂MeasureTheory.volume := by
              have hEq :
                  Set.EqOn
                    (fun z => φ z * F (z, t))
                    (fun z =>
                      ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
                        (Metric.closedBall x ((1 - t) * R)).indicator
                          (fun z => φ z * ‖x - z‖) z)
                    U := by
                  intro z hz
                  by_cases hcond : ‖x - z‖ ≤ (1 - t) * R
                  · have hball : z ∈ Metric.closedBall x ((1 - t) * R) := by
                      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hcond
                    simp [F, hcond, hball]
                    ring
                  · have hball : z ∉ Metric.closedBall x ((1 - t) * R) := by
                      intro hzball
                      exact hcond (by
                        simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hzball)
                    simp [F, hcond, hball]
              simpa [MeasureTheory.integral_const_mul] using
                (MeasureTheory.setIntegral_congr_fun hU_meas hEq)
      _ = ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
            ∫ z in U ∩ Metric.closedBall x ((1 - t) * R), φ z * ‖x - z‖
              ∂MeasureTheory.volume := by
              rw [setIntegral_indicator_closedBall_eq_setIntegral_inter_closedBall]
  have houter_int' :
      MeasureTheory.Integrable
        (fun t =>
          ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
            ∫ z in U ∩ Metric.closedBall x ((1 - t) * R), φ z * ‖x - z‖
              ∂MeasureTheory.volume)
        μI := by
    refine houter_int.congr ?_
    exact Filter.Eventually.of_forall hinner_eq
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  simpa [MeasureTheory.IntegrableOn, μI] using houter_int'

theorem intervalIntegral_inv_pow_setIntegral_inter_closedBall_le_rieszKernel
    {U : Set (Vec d)} (hU_meas : MeasurableSet U)
    {x : Vec d} {R : ℝ} (hR : 0 < R) {φ : Vec d → ℝ}
    (hφ_nonneg : ∀ z, 0 ≤ φ z)
    (hφ_meas : AEMeasurable φ (MeasureTheory.volume.restrict U))
    (hφK_int :
      MeasureTheory.IntegrableOn
        (fun z => φ z * rieszKernel x z) U MeasureTheory.volume) :
    ∫ t in (0 : ℝ)..1,
      ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
        ∫ z in U ∩ Metric.closedBall x ((1 - t) * R), φ z * ‖x - z‖
          ∂MeasureTheory.volume
      ≤
      ((R ^ d) / (d : ℝ)) *
        ∫ z in U, φ z * rieszKernel x z ∂MeasureTheory.volume := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact setIntegral_inv_pow_setIntegral_inter_closedBall_le_rieszKernel
    (d := d) hU_meas hR hφ_nonneg hφ_meas hφK_int

end TimeCollapse

end CKN
