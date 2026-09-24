/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliEnergyTerms
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliEnergy

/-! Integrability estimates used by the local energy lower bound. -/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat


noncomputable section

namespace CKN

lemma caccioppoli_gradient_integrable_on_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I) :
    IntegrableOn (fun z => spatialGradientSq u Du z)
      (parabolicCylinder x₀ t₀ ρ) volume := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ
  have hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).2.1
  have hDumeas : AEMeasurable (fun z : ParabolicPoint =>
      spatialGradientSq u Du z) (volume.restrict Q) := by
    have hcont : Continuous (fun v : Fin 3 → Vec3 =>
        ∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ (2 : ℕ)) := by
      fun_prop
    have h := hcont.comp_aestronglyMeasurable hDu
    exact h.aemeasurable.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have henergy : (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) ≠ ∞ := by
    have h := (hsol.2.2.2.2.2.1 Ω' J hbox).2.2.2.2.2.1
    have hle : (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) ≤
        ∫⁻ z in spaceTimeSet Ω' J, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) := by
      calc
        (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) ≤
            ∫⁻ z in Q, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) := by
          apply lintegral_mono
          intro z
          exact le_add_left le_rfl
        _ ≤ ∫⁻ z in spaceTimeSet Ω' J,
            ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) :=
          lintegral_mono_set hcyl
    exact ne_of_lt (hle.trans_lt h)
  have hpoint : ∀ z : ParabolicPoint,
      ENNReal.ofReal (spatialGradientSq u Du z) ≤
        9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
    intro z
    have hterm : ∀ i : Fin 3, ∀ j : Fin 3,
        (Du z i j) ^ (2 : ℕ) ≤ ‖Du z‖ ^ (2 : ℕ) := by
      intro i j
      rw [← sq_abs]
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact le_trans (norm_le_pi_norm (Du z i) j) (norm_le_pi_norm (Du z) i)
    have hsum : spatialGradientSq u Du z ≤
        ∑ i : Fin 3, ∑ j : Fin 3, ‖Du z‖ ^ (2 : ℕ) := by
      unfold spatialGradientSq
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    have hsum' : spatialGradientSq u Du z ≤ 9 * ‖Du z‖ ^ (2 : ℕ) := by
      calc
        spatialGradientSq u Du z ≤
            ∑ i : Fin 3, ∑ j : Fin 3, ‖Du z‖ ^ (2 : ℕ) := hsum
        _ = 9 * ‖Du z‖ ^ (2 : ℕ) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
    calc
      ENNReal.ofReal (spatialGradientSq u Du z) ≤
          ENNReal.ofReal (9 * ‖Du z‖ ^ (2 : ℕ)) :=
        ENNReal.ofReal_le_ofReal hsum'
      _ = 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
          show ENNReal.ofReal (9 : ℝ) = 9 by norm_num]
        congr 1
        rw [← ofReal_norm]
        rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
        norm_num [Real.rpow_natCast]
  have hlin : (∫⁻ z in Q, ENNReal.ofReal (spatialGradientSq u Du z)) ≠ ∞ := by
    have hle := lintegral_mono (μ := volume.restrict Q) hpoint
    have htop : (∫⁻ z in Q, 9 * ‖Du z‖ₑ ^ (2 : ℝ)) < ∞ := by
      apply lt_top_iff_ne_top.mpr
      rw [lintegral_const_mul' 9 _ (by norm_num)]
      exact ENNReal.mul_ne_top (by norm_num) henergy
    exact ne_of_lt (hle.trans_lt htop)
  have hnonneg : ∀ z : ParabolicPoint, 0 ≤ spatialGradientSq u Du z := by
    intro z
    unfold spatialGradientSq
    positivity
  exact caccioppoli_integrable_of_lintegral_abs_ne_top hDumeas (by
    simpa only [Q, abs_of_nonneg (hnonneg _)] using hlin)

lemma caccioppoli_u_sq_integrable_of_memLp
    {B : Set Vec3} {v : Vec3 → Vec3}
    (hv : MemLp v 2 (volume.restrict B)) :
    IntegrableOn (fun x => (vec3EuclideanNorm (v x)) ^ (2 : ℕ)) B volume := by
  have hnorm : AEStronglyMeasurable (fun x => vec3EuclideanNorm (v x))
      (volume.restrict B) :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hv.aestronglyMeasurable
  have hsq : AEStronglyMeasurable
      (fun x => (vec3EuclideanNorm (v x)) ^ (2 : ℕ))
      (volume.restrict B) := hnorm.pow 2
  have hbound : ∀ᵐ x ∂(volume.restrict B),
      ‖(vec3EuclideanNorm (v x)) ^ (2 : ℕ)‖ ≤ 3 * ‖v x‖ ^ (2 : ℕ) := by
    filter_upwards [] with x
    have hx := native_euclidean_norm_le_sqrt_three_norm (v x)
    have hsqx := (sq_le_sq₀ (vec3EuclideanNorm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).2 hx
    calc
      ‖(vec3EuclideanNorm (v x)) ^ (2 : ℕ)‖ =
          (vec3EuclideanNorm (v x)) ^ (2 : ℕ) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ (Real.sqrt 3 * ‖v x‖) ^ (2 : ℕ) := hsqx
      _ = 3 * ‖v x‖ ^ (2 : ℕ) := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
  exact Integrable.mono' ((hv.integrable_norm_pow (by norm_num)).const_mul (3 : ℝ))
    hsq hbound

lemma caccioppoli_gradient_sq_integrable_of_memLp
    {B : Set Vec3} {v : Vec3 → Fin 3 → Vec3}
    (hv : MemLp v 2 (volume.restrict B)) :
    IntegrableOn (fun x => ∑ i : Fin 3, ∑ j : Fin 3, (v x i j) ^ (2 : ℕ))
      B volume := by
  have hmeas : AEStronglyMeasurable v (volume.restrict B) :=
    hv.aestronglyMeasurable
  have hsq : AEStronglyMeasurable
      (fun x => ∑ i : Fin 3, ∑ j : Fin 3, (v x i j) ^ (2 : ℕ))
      (volume.restrict B) := by
    have hcont : Continuous (fun w : Fin 3 → Vec3 =>
        ∑ i : Fin 3, ∑ j : Fin 3, (w i j) ^ (2 : ℕ)) := by fun_prop
    simpa only [spatialGradientSq] using hcont.comp_aestronglyMeasurable hmeas
  have hbound : ∀ᵐ x ∂(volume.restrict B),
      ‖∑ i : Fin 3, ∑ j : Fin 3, (v x i j) ^ (2 : ℕ)‖ ≤
        9 * ‖v x‖ ^ (2 : ℕ) := by
    filter_upwards [] with x
    have hterm : ∀ i : Fin 3, ∀ j : Fin 3,
        (v x i j) ^ (2 : ℕ) ≤ ‖v x‖ ^ (2 : ℕ) := by
      intro i j
      rw [← sq_abs]
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact le_trans (norm_le_pi_norm (v x i) j) (norm_le_pi_norm (v x) i)
    have hsum : (∑ i : Fin 3, ∑ j : Fin 3, (v x i j) ^ (2 : ℕ)) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, ‖v x‖ ^ (2 : ℕ) := by
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    calc
      ‖∑ i : Fin 3, ∑ j : Fin 3, (v x i j) ^ (2 : ℕ)‖ =
          ∑ i : Fin 3, ∑ j : Fin 3, (v x i j) ^ (2 : ℕ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        positivity
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖v x‖ ^ (2 : ℕ) := hsum
      _ = 9 * ‖v x‖ ^ (2 : ℕ) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  exact Integrable.mono' ((hv.integrable_norm_pow (by norm_num)).const_mul (9 : ℝ))
    hsq hbound

end CKN
