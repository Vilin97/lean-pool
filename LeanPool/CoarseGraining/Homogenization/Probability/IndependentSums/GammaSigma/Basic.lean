/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Gamma
import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.Triangle

/-! # Basic -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- The Chapter 4 indicator scale attached to an event of probability `p`:
for `0 < p < 1` this is the quantity `|log p|^{-1/σ}` written as
`(-log p)^(-1/σ)`. -/
noncomputable def gammaIndicatorScale (σ p : ℝ) : ℝ :=
  (-Real.log p) ^ (-σ⁻¹)

/-- An explicit Chapter 4 moment-growth constant for the stretched-exponential
class `Γ_σ`. It is chosen large enough to absorb the elementary gamma-integral
bound used in the tail-to-moment direction. -/
noncomputable def gammaMomentConst (σ : ℝ) : ℝ :=
  (2 * Real.exp 1) * max 1 ((2 / (σ * Real.exp 1)) ^ σ⁻¹)

/-- Absolute `p^{1/σ}` moment growth with witness `M` for the stretched-
exponential Chapter 4 class. -/
def HasGammaMomentGrowthWith (μ : Measure Ω) (σ : ℝ) (X : Ω → ℝ) (M : ℝ) : Prop :=
  ∀ ⦃p : ℝ⦄, 1 ≤ p →
    Integrable (fun ω => |X ω| ^ p) μ ∧
      ∫ ω, |X ω| ^ p ∂μ ≤ (M * p ^ σ⁻¹) ^ p

/-- Existential absolute `Γ_σ` moment growth. -/
def HasGammaMomentGrowth (μ : Measure Ω) (σ : ℝ) (X : Ω → ℝ) : Prop :=
  ∃ M > 0, HasGammaMomentGrowthWith μ σ X M

lemma gammaMomentConst_pos {σ : ℝ} (_hσ : 0 < σ) : 0 < gammaMomentConst σ := by
  dsimp [gammaMomentConst]
  positivity

theorem hasGammaMomentGrowthWith_iff_of_nonneg {σ M : ℝ} {Y : Ω → ℝ}
    (hY_nonneg : ∀ ω, 0 ≤ Y ω) :
    HasGammaMomentGrowthWith μ σ Y M ↔
      ∀ ⦃p : ℝ⦄, 1 ≤ p →
        Integrable (fun ω => Y ω ^ p) μ ∧
          ∫ ω, Y ω ^ p ∂μ ≤ (M * p ^ σ⁻¹) ^ p := by
  constructor
  · intro h p hp
    rcases h hp with ⟨h_int, h_bound⟩
    have hpow : (fun ω => |Y ω| ^ p) = fun ω => Y ω ^ p := by
      funext ω
      rw [abs_of_nonneg (hY_nonneg ω)]
    refine ⟨hpow ▸ h_int, ?_⟩
    simpa [hpow] using h_bound
  · intro h p hp
    rcases h hp with ⟨h_int, h_bound⟩
    have hpow : (fun ω => |Y ω| ^ p) = fun ω => Y ω ^ p := by
      funext ω
      rw [abs_of_nonneg (hY_nonneg ω)]
    refine ⟨hpow.symm ▸ h_int, ?_⟩
    simpa [hpow] using h_bound

lemma rpow_mul_exp_neg_half_le {r u : ℝ} (hr : 0 < r) (hu : 0 < u) :
    u ^ r * Real.exp (-u / 2) ≤ ((2 * r) / Real.exp 1) ^ r := by
  have hx : 0 < u / (2 * r) := by positivity
  have hlog : Real.log (u / (2 * r)) ≤ u / (2 * r) - 1 :=
    Real.log_le_sub_one_of_pos hx
  have hmul' : Real.log (u / (2 * r)) * r ≤ (u / (2 * r) - 1) * r :=
    mul_le_mul_of_nonneg_right hlog hr.le
  have hmul : Real.log (u / (2 * r)) * r ≤ u / 2 - r := by
    calc
      Real.log (u / (2 * r)) * r ≤ (u / (2 * r) - 1) * r := hmul'
      _ = u / 2 - r := by
        field_simp [hr.ne']
  have hexp : Real.exp (Real.log (u / (2 * r)) * r) ≤ Real.exp (u / 2 - r) :=
    Real.exp_le_exp.2 hmul
  have hpow :
      (u / (2 * r)) ^ r ≤ Real.exp (u / 2 - r) := by
    simpa [Real.rpow_def_of_pos hx] using hexp
  have hmul'' :
      (2 * r) ^ r * ((u / (2 * r)) ^ r) ≤
        (2 * r) ^ r * Real.exp (u / 2 - r) := by
    exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by positivity) _)
  have hleft : (2 * r) ^ r * ((u / (2 * r)) ^ r) = u ^ r := by
    rw [← Real.mul_rpow (show 0 ≤ 2 * r by positivity) (show 0 ≤ u / (2 * r) by positivity)]
    congr 1
    field_simp [hr.ne']
  have hconst :
      (2 * r) ^ r * Real.exp (-r) = ((2 * r) / Real.exp 1) ^ r := by
    calc
      (2 * r) ^ r * Real.exp (-r) = (2 * r) ^ r * (Real.exp 1) ^ (-r) := by
        rw [← Real.exp_one_rpow (-r)]
      _ = (2 * r) ^ r * ((Real.exp 1)⁻¹) ^ r := by
        rw [Real.rpow_neg_eq_inv_rpow]
      _ = ((2 * r) * (Real.exp 1)⁻¹) ^ r := by
        rw [← Real.mul_rpow (show 0 ≤ 2 * r by positivity) (show 0 ≤ (Real.exp 1)⁻¹ by positivity)]
      _ = ((2 * r) / Real.exp 1) ^ r := by
        rw [div_eq_mul_inv]
  have hright :
      (2 * r) ^ r * Real.exp (u / 2 - r) =
        (((2 * r) / Real.exp 1) ^ r) * Real.exp (u / 2) := by
    calc
      (2 * r) ^ r * Real.exp (u / 2 - r)
        = (2 * r) ^ r * (Real.exp (u / 2) * Real.exp (-r)) := by
            rw [sub_eq_add_neg, Real.exp_add]
      _ = ((2 * r) ^ r * Real.exp (-r)) * Real.exp (u / 2) := by
            ac_rfl
      _ = (((2 * r) / Real.exp 1) ^ r) * Real.exp (u / 2) := by
            rw [hconst]
  have hupper : u ^ r ≤ (((2 * r) / Real.exp 1) ^ r) * Real.exp (u / 2) := by
    exact (hleft ▸ hmul'').trans_eq hright
  have hcancel := mul_le_mul_of_nonneg_right hupper (by positivity : 0 ≤ Real.exp (-u / 2))
  calc
    u ^ r * Real.exp (-u / 2)
      ≤ ((((2 * r) / Real.exp 1) ^ r) * Real.exp (u / 2)) * Real.exp (-u / 2) := hcancel
    _ = (((2 * r) / Real.exp 1) ^ r) * (Real.exp (u / 2) * Real.exp (-u / 2)) := by
          ac_rfl
    _ = (((2 * r) / Real.exp 1) ^ r) * 1 := by
          rw [← Real.exp_add, show u / 2 + -u / 2 = 0 by ring, Real.exp_zero]
    _ = ((2 * r) / Real.exp 1) ^ r := by ring

lemma gamma_add_one_le_two_mul_rpow_div_exp {r : ℝ} (hr : 0 < r) :
    Real.Gamma (r + 1) ≤ 2 * ((2 * r) / Real.exp 1) ^ r := by
  calc
    Real.Gamma (r + 1) = ∫ u in Set.Ioi (0 : ℝ), u ^ r * Real.exp (-u) := by
      rw [Real.Gamma_eq_integral (by linarith)]
      congr with u
      rw [show (r + 1) - 1 = r by ring]
      ac_rfl
    _ = ∫ u in Set.Ioi (0 : ℝ), (u ^ r * Real.exp (-u / 2)) * Real.exp (-u / 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      rw [show Real.exp (-u) = Real.exp (-u / 2) * Real.exp (-u / 2) by
        rw [← Real.exp_add]
        ring_nf]
      ac_rfl
    _ ≤ ∫ u in Set.Ioi (0 : ℝ), (((2 * r) / Real.exp 1) ^ r) * Real.exp (-u / 2) := by
      let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
      have hν_nonneg : 0 ≤ᵐ[ν] fun u => u ^ r * Real.exp (-u / 2) * Real.exp (-u / 2) := by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
        exact mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hu.le _) (by positivity))
          (by positivity)
      have hν_int :
          Integrable (fun u => (((2 * r) / Real.exp 1) ^ r) * Real.exp (-u / 2)) ν := by
        simpa [ν, IntegrableOn, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          (integrableOn_exp_mul_Ioi (a := -((1 : ℝ) / 2)) (by norm_num) 0).const_mul
            (((2 * r) / Real.exp 1) ^ r)
      have hmono :
          ∀ᵐ u ∂ν,
            u ^ r * Real.exp (-u / 2) * Real.exp (-u / 2) ≤
              (((2 * r) / Real.exp 1) ^ r) * Real.exp (-u / 2) := by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
        have h := rpow_mul_exp_neg_half_le hr hu
        have h' := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ Real.exp (-u / 2))
        simpa [mul_assoc, mul_left_comm, mul_comm] using h'
      simpa [ν] using integral_mono_of_nonneg hν_nonneg hν_int hmono
    _ = (((2 * r) / Real.exp 1) ^ r) * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u / 2) := by
      rw [integral_const_mul]
    _ = 2 * ((2 * r) / Real.exp 1) ^ r := by
      have hI :
          ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u / 2) = 2 := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          integral_exp_mul_Ioi (a := -((1 : ℝ) / 2)) (by norm_num) 0
      rw [hI]
      ring

lemma integrableOn_rpow_mul_exp_neg_rpow_of_pos {σ p : ℝ}
    (hσ : 0 < σ) (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => t ^ (p - 1) * Real.exp (-(t ^ σ))) (Set.Ioi 0) := by
  let f : ℝ → ℝ := fun u => u ^ (p / σ - 1) * Real.exp (-u)
  have hf : IntegrableOn f (Set.Ioi 0) := by
    simpa [f, mul_comm] using (Real.GammaIntegral_convergent (div_pos hp hσ))
  have hcomp :
      IntegrableOn (fun t : ℝ => t ^ (σ - 1) * f (t ^ σ)) (Set.Ioi 0) := by
    simpa [f, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      (integrableOn_Ioi_comp_rpow_iff' (E := ℝ) f hσ.ne').2 hf
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).1 hcomp
  intro t ht
  calc
    t ^ (σ - 1) * f (t ^ σ)
      = t ^ (σ - 1) * ((t ^ σ) ^ (p / σ - 1) * Real.exp (-(t ^ σ))) := by
          rfl
    _ = (t ^ (σ - 1) * (t ^ σ) ^ (p / σ - 1)) * Real.exp (-(t ^ σ)) := by
          ring
    _ = (t ^ (σ - 1) * t ^ (σ * (p / σ - 1))) * Real.exp (-(t ^ σ)) := by
          rw [← Real.rpow_mul (le_of_lt ht)]
    _ = t ^ ((σ - 1) + σ * (p / σ - 1)) * Real.exp (-(t ^ σ)) := by
          rw [← Real.rpow_add ht]
    _ = t ^ (-1 + σ * (p / σ)) * Real.exp (-(t ^ σ)) := by
          congr 1
          ring_nf
    _ = t ^ (p - 1) * Real.exp (-(t ^ σ)) := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (by congr 1; field_simp [hσ.ne'] : t ^ (-1 + σ * (p / σ)) = t ^ (-1 + p))

lemma gamma_moment_kernel_bound {σ p : ℝ}
    (hσ : 0 < σ) (hp : 1 ≤ p) :
    Real.exp 1 * p * ((1 / σ) * Real.Gamma (p / σ)) ≤
      (gammaMomentConst σ * p ^ σ⁻¹) ^ p := by
  let c : ℝ := (2 / (σ * Real.exp 1)) ^ σ⁻¹
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact Real.rpow_nonneg (by positivity) _
  have hppow_nonneg : 0 ≤ p ^ σ⁻¹ := Real.rpow_nonneg hp_nonneg _
  have hmuldiv : (1 / σ) * p = p / σ := by
    field_simp [hσ.ne']
  have hGamma :
      Real.exp 1 * p * ((1 / σ) * Real.Gamma (p / σ)) =
        Real.exp 1 * Real.Gamma (p / σ + 1) := by
    calc
      Real.exp 1 * p * ((1 / σ) * Real.Gamma (p / σ))
          = Real.exp 1 * (((1 / σ) * p) * Real.Gamma (p / σ)) := by ring
      _ = Real.exp 1 * ((p / σ) * Real.Gamma (p / σ)) := by rw [hmuldiv]
      _ = Real.exp 1 * Real.Gamma (p / σ + 1) := by
            rw [Real.Gamma_add_one (div_ne_zero hp_pos.ne' hσ.ne')]
  have hGammaBound :
      Real.exp 1 * Real.Gamma (p / σ + 1) ≤
        Real.exp 1 * (2 * ((2 * (p / σ)) / Real.exp 1) ^ (p / σ)) := by
    exact mul_le_mul_of_nonneg_left
      (gamma_add_one_le_two_mul_rpow_div_exp (r := p / σ) (div_pos hp_pos hσ))
      (by positivity)
  have hpow_eq :
      ((2 * (p / σ)) / Real.exp 1) ^ (p / σ) = (c * p ^ σ⁻¹) ^ p := by
    dsimp [c]
    calc
      ((2 * (p / σ)) / Real.exp 1) ^ (p / σ)
          = (((2 / (σ * Real.exp 1)) * p) ^ σ⁻¹) ^ p := by
              have hbase :
                  ((2 * (p / σ)) / Real.exp 1) = ((2 / (σ * Real.exp 1)) * p) := by
                field_simp [hσ.ne']
              rw [hbase, ← Real.rpow_mul (by positivity : 0 ≤ (2 / (σ * Real.exp 1)) * p)]
              congr 1
              field_simp [hσ.ne']
      _ = (((2 / (σ * Real.exp 1)) ^ σ⁻¹) * p ^ σ⁻¹) ^ p := by
            congr 1
            rw [Real.mul_rpow (by positivity : 0 ≤ 2 / (σ * Real.exp 1)) hp_nonneg]
  have hinner :
      (c * p ^ σ⁻¹) ^ p ≤ (max 1 c * p ^ σ⁻¹) ^ p := by
    refine Real.rpow_le_rpow ?_ ?_ hp_nonneg
    · exact mul_nonneg hc_nonneg hppow_nonneg
    · gcongr
      exact le_max_right 1 c
  have htwoe_one : 1 ≤ 2 * Real.exp 1 := by
    have hexp_one : 1 ≤ Real.exp 1 := by
      exact Real.one_le_exp (by positivity : 0 ≤ (1 : ℝ))
    nlinarith
  have htwoe :
      2 * Real.exp 1 ≤ (2 * Real.exp 1) ^ p := by
    exact Real.self_le_rpow_of_one_le htwoe_one hp
  have hmul :
      (2 * Real.exp 1) * (c * p ^ σ⁻¹) ^ p ≤
        (2 * Real.exp 1) ^ p * (max 1 c * p ^ σ⁻¹) ^ p := by
    exact mul_le_mul htwoe hinner (by positivity) (by positivity)
  calc
    Real.exp 1 * p * ((1 / σ) * Real.Gamma (p / σ))
      = Real.exp 1 * Real.Gamma (p / σ + 1) := hGamma
    _ ≤ Real.exp 1 * (2 * ((2 * (p / σ)) / Real.exp 1) ^ (p / σ)) := hGammaBound
    _ = (2 * Real.exp 1) * (c * p ^ σ⁻¹) ^ p := by
          rw [hpow_eq]
          ring
    _ ≤ (2 * Real.exp 1) ^ p * (max 1 c * p ^ σ⁻¹) ^ p := hmul
    _ = ((2 * Real.exp 1) * (max 1 c * p ^ σ⁻¹)) ^ p := by
          rw [← Real.mul_rpow (by positivity : 0 ≤ 2 * Real.exp 1)
            (mul_nonneg (le_trans zero_le_one (le_max_left 1 c)) hppow_nonneg)]
    _ = (gammaMomentConst σ * p ^ σ⁻¹) ^ p := by
          dsimp [gammaMomentConst, c]
          congr 1
          ring

/-- Reverse `Γ_σ` moment estimate at unit scale: stretched-exponential upper
tails imply `p^{1/σ}` moment growth for every `p ≥ 1`. -/
theorem lintegral_rpow_le_of_isBigOWith_gammaSigma_unit
    {Y : Ω → ℝ} {σ p : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hp : 1 ≤ p) (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (hYm : AEMeasurable Y μ) (hY : IsBigOWith μ (gammaSigma σ) Y 1) :
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ p) ∂μ ≤
      ENNReal.ofReal ((gammaMomentConst σ * p ^ σ⁻¹) ^ p) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hY_nonneg_ae : 0 ≤ᵐ[μ] Y := Filter.Eventually.of_forall hY_nonneg
  have hY_tail := (isBigOWith_gammaSigma_iff (μ := μ) (X := Y) (A := 1) (σ := σ)).1 hY
  have hLayer :=
    MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul (μ := μ) hY_nonneg_ae hYm hp_pos
  have hTail :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Ioi (0 : ℝ) →
        μ {ω | t < Y ω} ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-(t ^ σ))) := by
    intro t ht
    let s : Set Ω := upperTailEvent Y t
    change μ s ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-(t ^ σ)))
    by_cases ht1 : 1 ≤ t
    · have hreal :
        μ.real s ≤ Real.exp (-(t ^ σ)) := by
          simpa [s, upperTailEvent] using hY_tail ht1
      have hmul :
          Real.exp (-(t ^ σ)) ≤ Real.exp 1 * Real.exp (-(t ^ σ)) := by
        calc
          Real.exp (-(t ^ σ)) = 1 * Real.exp (-(t ^ σ)) := by ring
          _ ≤ Real.exp 1 * Real.exp (-(t ^ σ)) := by
                gcongr
                exact Real.one_le_exp (by positivity : 0 ≤ (1 : ℝ))
      have hfinite := measure_lt_top μ s
      have hmeasure_eq :
          μ s = ENNReal.ofReal (μ.real s) := by
        simp [Measure.real, hfinite.ne]
      rw [hmeasure_eq]
      exact ENNReal.ofReal_le_ofReal (hreal.trans hmul)
    · have hprob :
        μ s ≤ 1 := by
          calc
            μ s ≤ μ Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := by simp
      have hpow_le_one : t ^ σ ≤ 1 := by
        have ht_lt_one : t < 1 := lt_of_not_ge ht1
        simpa using Real.rpow_le_rpow (le_of_lt ht) ht_lt_one.le hσ.le
      have hexp :
          (1 : ENNReal) ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-(t ^ σ))) := by
        have hreal : 1 ≤ Real.exp (1 - t ^ σ) := by
          exact Real.one_le_exp (sub_nonneg.mpr hpow_le_one)
        simpa [sub_eq_add_neg, Real.exp_add] using (ENNReal.ofReal_le_ofReal hreal)
      exact hprob.trans hexp
  have hdom :
      ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (p - 1)) ≤
          ENNReal.ofReal (Real.exp 1 * (t ^ (p - 1) * Real.exp (-(t ^ σ)))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hpow_nonneg : 0 ≤ t ^ (p - 1) := Real.rpow_nonneg ht.le _
    have hmul :
        μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (p - 1)) ≤
          ENNReal.ofReal (Real.exp 1 * Real.exp (-(t ^ σ))) *
            ENNReal.ofReal (t ^ (p - 1)) := by
      exact mul_le_mul_of_nonneg_right (hTail ht)
        (by positivity : 0 ≤ ENNReal.ofReal (t ^ (p - 1)))
    calc
      μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-(t ^ σ))) *
            ENNReal.ofReal (t ^ (p - 1)) := hmul
      _ = ENNReal.ofReal (Real.exp 1 * (t ^ (p - 1) * Real.exp (-(t ^ σ)))) := by
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp 1 * Real.exp (-(t ^ σ)))]
            congr 1
            ring
  have hDomInt :
      IntegrableOn (fun t : ℝ => Real.exp 1 * (t ^ (p - 1) * Real.exp (-(t ^ σ))))
        (Set.Ioi 0) := by
    show Integrable (fun t : ℝ => Real.exp 1 * (t ^ (p - 1) * Real.exp (-(t ^ σ))))
      (volume.restrict (Set.Ioi 0))
    have hraw :=
      (integrableOn_rpow_mul_exp_neg_rpow_of_pos (σ := σ) (p := p) hσ hp_pos).const_mul
        (Real.exp 1)
    simp only [mul_assoc, mul_comm] at hraw ⊢
    exact hraw
  have hDomNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun t : ℝ => Real.exp 1 * (t ^ (p - 1) * Real.exp (-(t ^ σ))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hpow_nonneg : 0 ≤ t ^ (p - 1) := Real.rpow_nonneg ht.le _
    exact mul_nonneg (by positivity) (mul_nonneg hpow_nonneg (by positivity))
  have hDomLin :
      ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp 1 * (t ^ (p - 1) * Real.exp (-(t ^ σ)))) =
        ENNReal.ofReal (Real.exp 1 * ((1 / σ) * Real.Gamma (p / σ))) := by
    have hEq :
        ENNReal.ofReal
            (∫ t in Set.Ioi (0 : ℝ), Real.exp 1 * (t ^ (p - 1) * Real.exp (-(t ^ σ)))) =
          ∫⁻ t in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (Real.exp 1 * (t ^ (p - 1) * Real.exp (-(t ^ σ)))) := by
      simpa [IntegrableOn] using
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (μ := volume.restrict (Set.Ioi (0 : ℝ))) hDomInt hDomNonneg)
    rw [← hEq]
    rw [integral_const_mul, integral_rpow_mul_exp_neg_rpow hσ (by linarith : -1 < p - 1)]
    have harg : (p - 1 + 1) / σ = p / σ := by ring
    rw [harg]
  have hmono :
      ∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (p - 1)) ≤
        ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp 1 * (t ^ (p - 1) * Real.exp (-(t ^ σ)))) := by
    exact lintegral_mono_ae hdom
  calc
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ p) ∂μ
      = ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (p - 1)) := hLayer
    _ ≤ ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (Real.exp 1 * (t ^ (p - 1) * Real.exp (-(t ^ σ)))) := by
          gcongr
    _ = ENNReal.ofReal (Real.exp 1 * p * ((1 / σ) * Real.Gamma (p / σ))) := by
          rw [hDomLin, ← ENNReal.ofReal_mul (le_trans zero_le_one hp)]
          ring_nf
    _ ≤ ENNReal.ofReal ((gammaMomentConst σ * p ^ σ⁻¹) ^ p) := by
          exact ENNReal.ofReal_le_ofReal (gamma_moment_kernel_bound hσ hp)

/-- Stretched-exponential upper tails imply `p^{1/σ}` moment growth at an
arbitrary scale. -/
theorem lintegral_rpow_le_of_isBigOWith_gammaSigma
    {Y : Ω → ℝ} {K σ p : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hK : 0 < K) (hp : 1 ≤ p) (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (hYm : AEMeasurable Y μ) (hY : IsBigOWith μ (gammaSigma σ) Y K) :
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ p) ∂μ ≤
      ENNReal.ofReal ((gammaMomentConst σ * p ^ σ⁻¹ * K) ^ p) := by
  let Z : Ω → ℝ := fun ω => Y ω / K
  have hZ_nonneg : ∀ ω, 0 ≤ Z ω := by
    intro ω
    dsimp [Z]
    exact div_nonneg (hY_nonneg ω) hK.le
  have hZm : AEMeasurable Z μ := by
    simpa [Z, div_eq_mul_inv, mul_comm] using hYm.const_mul K⁻¹
  have hZ : IsBigOWith μ (gammaSigma σ) Z 1 := by
    rw [isBigOWith_gammaSigma_iff] at hY ⊢
    intro t ht
    have hset : upperTailEvent Z t = upperTailEvent Y (K * t) := by
      ext ω
      dsimp [Z, upperTailEvent]
      rw [lt_div_iff₀ hK, mul_comm]
    simpa [hset] using hY ht
  have hunit :=
    lintegral_rpow_le_of_isBigOWith_gammaSigma_unit
      (μ := μ) (Y := Z) (σ := σ) (p := p) hσ hp hZ_nonneg hZm hZ
  have hZpowm : AEMeasurable (fun ω => Z ω ^ p) μ :=
    hZm.pow measurable_const.aemeasurable
  calc
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ p) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (K ^ p) * ENNReal.ofReal (Z ω ^ p) ∂μ := by
          apply lintegral_congr_ae
          refine Filter.Eventually.of_forall ?_
          intro ω
          dsimp [Z]
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hK.le _)]
          congr 1
          calc
            Y ω ^ p = (K * (Y ω / K)) ^ p := by
              congr 1
              symm
              field_simp [hK.ne']
            _ = K ^ p * (Y ω / K) ^ p := by
              rw [Real.mul_rpow hK.le (hZ_nonneg ω)]
    _ = ENNReal.ofReal (K ^ p) * ∫⁻ ω, ENNReal.ofReal (Z ω ^ p) ∂μ := by
          simpa using
            (MeasureTheory.lintegral_const_mul'' (μ := μ) (r := ENNReal.ofReal (K ^ p))
              (f := fun ω => ENNReal.ofReal (Z ω ^ p))
              (measurable_id.ennreal_ofReal.comp_aemeasurable hZpowm))
    _ ≤ ENNReal.ofReal (K ^ p) * ENNReal.ofReal ((gammaMomentConst σ * p ^ σ⁻¹) ^ p) := by
          gcongr
    _ = ENNReal.ofReal ((gammaMomentConst σ * p ^ σ⁻¹ * K) ^ p) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hK.le _)]
          congr 1
          have hscale_nonneg : 0 ≤ gammaMomentConst σ * p ^ σ⁻¹ := by
            exact mul_nonneg (gammaMomentConst_pos hσ).le (Real.rpow_nonneg (le_trans zero_le_one hp) _)
          rw [Real.mul_rpow hscale_nonneg hK.le]
          ring

/-- Real-integral version of `lintegral_rpow_le_of_isBigOWith_gammaSigma`. -/
theorem integral_rpow_le_of_isBigOWith_gammaSigma
    {Y : Ω → ℝ} {K σ p : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hK : 0 < K) (hp : 1 ≤ p) (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (hYm : AEMeasurable Y μ) (hY : IsBigOWith μ (gammaSigma σ) Y K) :
    ∫ ω, Y ω ^ p ∂μ ≤ (gammaMomentConst σ * p ^ σ⁻¹ * K) ^ p := by
  have hlin :=
    lintegral_rpow_le_of_isBigOWith_gammaSigma
      (μ := μ) (Y := Y) (K := K) (σ := σ) (p := p) hσ hK hp hY_nonneg hYm hY
  have hpow_nonneg : 0 ≤ᵐ[μ] fun ω => Y ω ^ p := by
    exact Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hY_nonneg ω) _
  have hbound_nonneg : 0 ≤ (gammaMomentConst σ * p ^ σ⁻¹ * K) ^ p := by
    have hscale_nonneg : 0 ≤ gammaMomentConst σ * p ^ σ⁻¹ * K := by
      exact mul_nonneg
        (mul_nonneg (gammaMomentConst_pos hσ).le (Real.rpow_nonneg (le_trans zero_le_one hp) _))
        hK.le
    exact Real.rpow_nonneg hscale_nonneg _
  have hfin := lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hpow_nonneg
    (hYm.pow measurable_const.aemeasurable).aestronglyMeasurable]
  have htoReal :
      (∫⁻ ω, ENNReal.ofReal (Y ω ^ p) ∂μ).toReal ≤
        (ENNReal.ofReal ((gammaMomentConst σ * p ^ σ⁻¹ * K) ^ p)).toReal :=
    (ENNReal.toReal_le_toReal hfin.ne ENNReal.ofReal_ne_top).2 hlin
  simpa [hbound_nonneg] using htoReal

/-- Integrability consequence of stretched-exponential upper-tail control. -/
theorem integrable_rpow_of_isBigOWith_gammaSigma
    {Y : Ω → ℝ} {K σ p : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hK : 0 < K) (hp : 1 ≤ p) (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (hYm : AEMeasurable Y μ) (hY : IsBigOWith μ (gammaSigma σ) Y K) :
    Integrable (fun ω => Y ω ^ p) μ := by
  have hlin :=
    lintegral_rpow_le_of_isBigOWith_gammaSigma
      (μ := μ) (Y := Y) (K := K) (σ := σ) (p := p) hσ hK hp hY_nonneg hYm hY
  have hpow_nonneg : 0 ≤ᵐ[μ] fun ω => Y ω ^ p := by
    exact Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hY_nonneg ω) _
  have hpow_aesm :
      AEStronglyMeasurable (fun ω => Y ω ^ p) μ :=
    (hYm.pow measurable_const.aemeasurable).aestronglyMeasurable
  refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    (μ := μ) hpow_aesm hpow_nonneg).1 ?_
  exact ne_of_lt (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)

/-- Symmetric moment estimate for the stretched-exponential class. -/
theorem integral_abs_rpow_le_of_isBigO_gammaSigma
    {X : Ω → ℝ} {K σ p : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hK : 0 < K) (hp : 1 ≤ p)
    (hXm : AEMeasurable X μ) (hX : IsBigO μ (gammaSigma σ) X K) :
    ∫ ω, |X ω| ^ p ∂μ ≤ (gammaMomentConst σ * p ^ σ⁻¹ * K) ^ p := by
  rw [IsBigO] at hX
  exact integral_rpow_le_of_isBigOWith_gammaSigma
    (μ := μ) (Y := fun ω => |X ω|) (K := K) (σ := σ) (p := p)
    hσ hK hp (fun ω => abs_nonneg (X ω)) (continuous_abs.measurable.comp_aemeasurable hXm) hX

/-- Power rule for the stretched-exponential class on nonnegative random
variables. -/
theorem isBigOWith_gammaSigma_rpow
    {X : Ω → ℝ} {A σ p : ℝ}
    [IsFiniteMeasure μ]
    (hp : 0 < p) (hA : 0 ≤ A) (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hX : IsBigOWith μ (gammaSigma σ) X A) :
    IsBigOWith μ (gammaSigma (σ / p)) (fun ω => X ω ^ p) (A ^ p) := by
  rw [isBigOWith_gammaSigma_iff] at hX ⊢
  intro t ht
  let s : ℝ := t ^ p⁻¹
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hs_nonneg : 0 ≤ s := by
    exact Real.rpow_nonneg ht0 _
  have hs_one : 1 ≤ s := by
    dsimp [s]
    exact Real.one_le_rpow ht (inv_nonneg.mpr hp.le)
  have hsubset :
      upperTailEvent (fun ω => X ω ^ p) (A ^ p * t) ⊆
        upperTailEvent X (A * s) := by
    intro ω hω
    have hAs_pow : (A * s) ^ p = A ^ p * t := by
      calc
        (A * s) ^ p = A ^ p * s ^ p := by
          rw [Real.mul_rpow hA hs_nonneg]
        _ = A ^ p * t := by
          rw [show s ^ p = t by
            dsimp [s]
            rw [Real.rpow_inv_rpow ht0 hp.ne']]
    have hω' : (A * s) ^ p < X ω ^ p := by
      simpa [hAs_pow] using hω
    exact (Real.rpow_lt_rpow_iff (mul_nonneg hA hs_nonneg) (hX_nonneg ω) hp).1 hω'
  refine (measureReal_mono hsubset).trans ?_
  have hs_pow : s ^ σ = t ^ (σ / p) := by
    dsimp [s]
    calc
      (t ^ p⁻¹) ^ σ = t ^ (p⁻¹ * σ) := by
        rw [← Real.rpow_mul ht0]
      _ = t ^ (σ / p) := by
        simp [div_eq_mul_inv, mul_comm]
  simpa [s, hs_pow, div_eq_mul_inv] using hX hs_one

/-- Reversible power rule for stretched-exponential upper-tail bounds on
nonnegative random variables. -/
theorem isBigOWith_gammaSigma_rpow_iff
    {X : Ω → ℝ} {A σ p : ℝ}
    [IsFiniteMeasure μ]
    (hp : 0 < p) (hA : 0 ≤ A) (hX_nonneg : ∀ ω, 0 ≤ X ω) :
    IsBigOWith μ (gammaSigma σ) X A ↔
      IsBigOWith μ (gammaSigma (σ / p)) (fun ω => X ω ^ p) (A ^ p) := by
  constructor
  · exact isBigOWith_gammaSigma_rpow (μ := μ) hp hA hX_nonneg
  · intro hXp
    have hp_inv : 0 < p⁻¹ := inv_pos.mpr hp
    have hApow_nonneg : 0 ≤ A ^ p := Real.rpow_nonneg hA _
    have hXpow_nonneg : ∀ ω, 0 ≤ X ω ^ p := fun ω => Real.rpow_nonneg (hX_nonneg ω) _
    have hback :=
      isBigOWith_gammaSigma_rpow (μ := μ) (X := fun ω => X ω ^ p)
        (A := A ^ p) (σ := σ / p) (p := p⁻¹)
        hp_inv hApow_nonneg hXpow_nonneg hXp
    have hsigma : (σ / p) / p⁻¹ = σ := by
      field_simp [div_eq_mul_inv, hp.ne']
    have hX_id : (fun ω => (X ω ^ p) ^ p⁻¹) = X := by
      funext ω
      calc
        (X ω ^ p) ^ p⁻¹ = X ω ^ (p * p⁻¹) := by
          rw [← Real.rpow_mul (hX_nonneg ω)]
        _ = X ω := by
          rw [mul_inv_cancel₀ hp.ne', Real.rpow_one]
    have hA_id : (A ^ p) ^ p⁻¹ = A := by
      calc
        (A ^ p) ^ p⁻¹ = A ^ (p * p⁻¹) := by
          rw [← Real.rpow_mul hA]
        _ = A := by
          rw [mul_inv_cancel₀ hp.ne', Real.rpow_one]
    simpa [hsigma, hX_id, hA_id] using hback

/-- Symmetric reversible power rule for the stretched-exponential class,
expressed through the note-level quantity `|X|^p`. -/
theorem isBigO_gammaSigma_rpow_iff
    {X : Ω → ℝ} {A σ p : ℝ}
    [IsFiniteMeasure μ]
    (hp : 0 < p) (hA : 0 ≤ A) :
    IsBigO μ (gammaSigma σ) X A ↔
      IsBigO μ (gammaSigma (σ / p)) (fun ω => |X ω| ^ p) (A ^ p) := by
  have habs :
      (fun ω => |(|X ω| ^ p)|) = (fun ω => |X ω| ^ p) := by
    funext ω
    rw [abs_of_nonneg]
    exact Real.rpow_nonneg (abs_nonneg (X ω)) _
  rw [IsBigO, IsBigO, habs]
  simpa [abs_abs] using
    isBigOWith_gammaSigma_rpow_iff (μ := μ) (X := fun ω => |X ω|) (A := A) (σ := σ) (p := p)
      hp hA (fun ω => abs_nonneg (X ω))

/-- Moment growth of order `p^{1/σ}` implies stretched-exponential upper tails
with the Chapter 4 constant `e M`. -/
theorem isBigOWith_gammaSigma_of_moment_growth
    {Y : Ω → ℝ} {M σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hM : 0 < M) (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (hY :
      ∀ ⦃p : ℝ⦄, 1 ≤ p →
        Integrable (fun ω => Y ω ^ p) μ ∧
          ∫ ω, Y ω ^ p ∂μ ≤ (M * p ^ σ⁻¹) ^ p) :
    IsBigOWith μ (gammaSigma σ) Y (Real.exp 1 * M) := by
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  let p : ℝ := t ^ σ
  have hp_one : 1 ≤ p := by
    dsimp [p]
    exact Real.one_le_rpow ht hσ.le
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp_one
  rcases hY hp_one with ⟨hp_int, hp_bound⟩
  have hbase_pos : 0 < (Real.exp 1 * M) * t := by positivity
  have hYpow_nonneg : 0 ≤ᵐ[μ] fun ω => Y ω ^ p :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hY_nonneg ω) _
  have hsubset :
      upperTailEvent Y ((Real.exp 1 * M) * t) ⊆
        {ω | (((Real.exp 1 * M) * t) ^ p) ≤ Y ω ^ p} := by
    intro ω hω
    have hωpow :
        (((Real.exp 1 * M) * t) ^ p) < Y ω ^ p := by
      exact (Real.rpow_lt_rpow_iff hbase_pos.le (hY_nonneg ω) hp_pos).2 hω
    exact le_of_lt hωpow
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := fun ω => Y ω ^ p)
      hYpow_nonneg hp_int (((Real.exp 1 * M) * t) ^ p)
  have htail_aux :
      μ.real {ω | (((Real.exp 1 * M) * t) ^ p) ≤ Y ω ^ p} ≤
        ((M * p ^ σ⁻¹) ^ p) / (((Real.exp 1 * M) * t) ^ p) := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hbase_pos _)]
    simpa [mul_comm] using (hmarkov.trans hp_bound)
  have hp_root : p ^ σ⁻¹ = t := by
    dsimp [p]
    calc
      (t ^ σ) ^ σ⁻¹ = t ^ (σ * σ⁻¹) := by
        rw [← Real.rpow_mul (le_trans zero_le_one ht)]
      _ = t := by
        rw [mul_inv_cancel₀ hσ.ne', Real.rpow_one]
  have hMt_pos : 0 < M * t := by positivity
  calc
    μ.real (upperTailEvent Y ((Real.exp 1 * M) * t))
      ≤ μ.real {ω | (((Real.exp 1 * M) * t) ^ p) ≤ Y ω ^ p} :=
        measureReal_mono hsubset
    _ ≤ ((M * p ^ σ⁻¹) ^ p) / (((Real.exp 1 * M) * t) ^ p) := htail_aux
    _ = ((M * t) ^ p) / (((Real.exp 1) ^ p) * ((M * t) ^ p)) := by
      rw [hp_root]
      congr 1
      calc
        (((Real.exp 1 * M) * t) ^ p) = ((Real.exp 1) * (M * t)) ^ p := by ring_nf
        _ = (Real.exp 1) ^ p * (M * t) ^ p := by
          rw [Real.mul_rpow (by positivity) hMt_pos.le]
    _ = ((M * t) ^ p * ((M * t) ^ p)⁻¹) * ((Real.exp 1) ^ p)⁻¹ := by
      rw [div_eq_mul_inv, mul_inv_rev]
      ac_rfl
    _ = ((Real.exp 1) ^ p)⁻¹ := by
      rw [mul_inv_cancel₀ (Real.rpow_pos_of_pos hMt_pos _).ne', one_mul]
    _ = Real.exp (-p) := by
      rw [Real.exp_one_rpow, ← Real.exp_neg]
    _ = Real.exp (-(t ^ σ)) := by
      simp [p]

/-- Symmetric moment-growth criterion for the stretched-exponential class. -/
theorem isBigO_gammaSigma_of_moment_growth
    {X : Ω → ℝ} {M σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hM : 0 < M)
    (hX :
      ∀ ⦃p : ℝ⦄, 1 ≤ p →
        Integrable (fun ω => |X ω| ^ p) μ ∧
          ∫ ω, |X ω| ^ p ∂μ ≤ (M * p ^ σ⁻¹) ^ p) :
    IsBigO μ (gammaSigma σ) X (Real.exp 1 * M) := by
  rw [IsBigO]
  exact isBigOWith_gammaSigma_of_moment_growth
    (μ := μ) (Y := fun ω => |X ω|) (M := M) (σ := σ) hσ hM
    (fun ω => abs_nonneg (X ω)) hX

/-- Tail control with witness `K` yields `p^{1/σ}` absolute moment growth with
the explicit Chapter 4 witness `gammaMomentConst σ * K`. -/
theorem hasGammaMomentGrowthWith_of_isBigOWith_gammaSigma
    {Y : Ω → ℝ} {K σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hK : 0 < K) (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (hYm : AEMeasurable Y μ) (hY : IsBigOWith μ (gammaSigma σ) Y K) :
    HasGammaMomentGrowthWith μ σ Y (gammaMomentConst σ * K) := by
  rw [hasGammaMomentGrowthWith_iff_of_nonneg (μ := μ) (σ := σ)
    (M := gammaMomentConst σ * K) (Y := Y) hY_nonneg]
  intro p hp
  refine ⟨?_, ?_⟩
  · exact integrable_rpow_of_isBigOWith_gammaSigma
      (μ := μ) (Y := Y) (K := K) (σ := σ) (p := p)
      hσ hK hp hY_nonneg hYm hY
  · have hbound :=
      integral_rpow_le_of_isBigOWith_gammaSigma
        (μ := μ) (Y := Y) (K := K) (σ := σ) (p := p)
        hσ hK hp hY_nonneg hYm hY
    have hscale :
        gammaMomentConst σ * p ^ σ⁻¹ * K =
          (gammaMomentConst σ * K) * p ^ σ⁻¹ := by
      ring
    simpa [hscale] using hbound

/-- Absolute `p^{1/σ}` moment growth implies stretched-exponential upper tails
with the Chapter 4 constant `e M`, provided the random variable is
nonnegative. -/
theorem isBigOWith_gammaSigma_of_hasGammaMomentGrowthWith_of_nonneg
    {Y : Ω → ℝ} {M σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hM : 0 < M) (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (hY : HasGammaMomentGrowthWith μ σ Y M) :
    IsBigOWith μ (gammaSigma σ) Y (Real.exp 1 * M) := by
  rw [hasGammaMomentGrowthWith_iff_of_nonneg (μ := μ) (σ := σ)
    (M := M) (Y := Y) hY_nonneg] at hY
  exact isBigOWith_gammaSigma_of_moment_growth
    (μ := μ) (Y := Y) (M := M) (σ := σ) hσ hM hY_nonneg hY

/-- Symmetric tail control with witness `K` yields witness-level absolute
moment growth with the explicit Chapter 4 constant `gammaMomentConst σ * K`. -/
theorem hasGammaMomentGrowthWith_of_isBigO_gammaSigma
    {X : Ω → ℝ} {K σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hK : 0 < K)
    (hXm : AEMeasurable X μ) (hX : IsBigO μ (gammaSigma σ) X K) :
    HasGammaMomentGrowthWith μ σ X (gammaMomentConst σ * K) := by
  intro p hp
  refine ⟨?_, ?_⟩
  · have hX_abs : IsBigOWith μ (gammaSigma σ) (fun ω => |X ω|) K := by
      simpa [IsBigO] using hX
    exact integrable_rpow_of_isBigOWith_gammaSigma
      (μ := μ) (Y := fun ω => |X ω|) (K := K) (σ := σ) (p := p)
      hσ hK hp (fun ω => abs_nonneg (X ω))
      (continuous_abs.measurable.comp_aemeasurable hXm) hX_abs
  · have hbound :=
      integral_abs_rpow_le_of_isBigO_gammaSigma
        (μ := μ) (X := X) (K := K) (σ := σ) (p := p) hσ hK hp hXm hX
    have hscale :
        gammaMomentConst σ * p ^ σ⁻¹ * K =
          (gammaMomentConst σ * K) * p ^ σ⁻¹ := by
      ring
    simpa [hscale] using hbound

/-- Tail control in the symmetric `O_{Γ_σ}` sense yields existential absolute
moment growth. -/
theorem hasGammaMomentGrowth_of_isBigO_gammaSigma
    {X : Ω → ℝ} {K σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hK : 0 < K)
    (hXm : AEMeasurable X μ) (hX : IsBigO μ (gammaSigma σ) X K) :
    HasGammaMomentGrowth μ σ X := by
  refine ⟨gammaMomentConst σ * K, mul_pos (gammaMomentConst_pos hσ) hK, ?_⟩
  exact hasGammaMomentGrowthWith_of_isBigO_gammaSigma
    (μ := μ) (X := X) (K := K) (σ := σ) hσ hK hXm hX

/-- Witness-level absolute moment growth directly upgrades to the symmetric
`O_{Γ_σ}` relation. -/
theorem isBigO_gammaSigma_of_hasGammaMomentGrowthWith
    {X : Ω → ℝ} {M σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hM : 0 < M)
    (hX : HasGammaMomentGrowthWith μ σ X M) :
    IsBigO μ (gammaSigma σ) X (Real.exp 1 * M) := by
  exact isBigO_gammaSigma_of_moment_growth
    (μ := μ) (X := X) (M := M) (σ := σ) hσ hM hX

/-- For nonnegative random variables, existential `Γ_σ` moment growth is
equivalent to an upper-tail `O_{Γ_σ}` witness. -/
theorem hasGammaMomentGrowth_iff_exists_isBigOWith_gammaSigma_of_nonneg
    {Y : Ω → ℝ} {σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hY_nonneg : ∀ ω, 0 ≤ Y ω) (hYm : AEMeasurable Y μ) :
    HasGammaMomentGrowth μ σ Y ↔
      ∃ K > 0, IsBigOWith μ (gammaSigma σ) Y K := by
  constructor
  · rintro ⟨M, hM, hY_growth⟩
    refine ⟨Real.exp 1 * M, by positivity, ?_⟩
    exact isBigOWith_gammaSigma_of_hasGammaMomentGrowthWith_of_nonneg
      (μ := μ) (Y := Y) (M := M) (σ := σ) hσ hM hY_nonneg hY_growth
  · rintro ⟨K, hK, hY_tail⟩
    refine ⟨gammaMomentConst σ * K, mul_pos (gammaMomentConst_pos hσ) hK, ?_⟩
    exact hasGammaMomentGrowthWith_of_isBigOWith_gammaSigma
      (μ := μ) (Y := Y) (K := K) (σ := σ) hσ hK hY_nonneg hYm hY_tail

/-- Existential `Γ_σ` moment growth is equivalent to the symmetric
stretched-exponential `O_{Γ_σ}` relation. -/
theorem hasGammaMomentGrowth_iff_exists_isBigO_gammaSigma
    {X : Ω → ℝ} {σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hXm : AEMeasurable X μ) :
    HasGammaMomentGrowth μ σ X ↔
      ∃ K > 0, IsBigO μ (gammaSigma σ) X K := by
  constructor
  · rintro ⟨M, hM, hX_growth⟩
    refine ⟨Real.exp 1 * M, by positivity, ?_⟩
    exact isBigO_gammaSigma_of_hasGammaMomentGrowthWith
      (μ := μ) (X := X) (M := M) (σ := σ) hσ hM hX_growth
  · rintro ⟨K, hK, hX_tail⟩
    exact hasGammaMomentGrowth_of_isBigO_gammaSigma
      (μ := μ) (X := X) (K := K) (σ := σ) hσ hK hXm hX_tail


end

end IndependentSums

end Homogenization
