/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteCoarseBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteAssemblyBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteSumBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds

/-! Initial high and mean estimates retain their distinct small factors.
The only truncation-dependent quantity is the already controlled tail base. -/

@[expose] public section


noncomputable section


namespace EulerPacketCylinderField.Field

open Set Finset EulerPacketProfileRecursion EulerPacketPointJets EulerFiniteGrades

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} {G : Field P T raw}
  {q d : ℕ} {R A γ : ℝ}

theorem WordBound.normalize_amplitude (hG : G.WordBound q R (γ * A) d) (hγ : 0 < γ) :
    (G.smul γ⁻¹).WordBound q R A d := by
  have h := hG.smul γ⁻¹
  simpa only [abs_of_pos (inv_pos.mpr hγ),← mul_assoc,inv_mul_cancel₀ hγ.ne',one_mul] using h

theorem WordBound.restore_amplitude (hG : (G.smul γ⁻¹).WordBound q R A d) (hγ : 0 < γ) :
    G.WordBound q R (γ*A) d := by
  have h := hG.smul γ
  rw [abs_of_pos hγ] at h
  apply h.ofRawEq G
  intro t x θ
  change raw (t,(x,θ)) = γ • (γ⁻¹ • raw (t,(x,θ)))
  rw [smul_smul,mul_inv_cancel₀ hγ.ne',one_smul]

theorem wordBound_evaluate_low_high_scaled (N : ℕ) (hN : 1 ≤ N) (κ B C₁ C₂ γ : ℝ)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hγ : 0 < γ) (hsmall : κ * B ≤ 1 / 2)
    (f : ℕ → VectorField) (H : ∀ i, Field P T (f i)) (q : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hzero : ∀ (t : Icc (0 : ℝ) T) x θ, f 0 (t, (x, θ)) = 0)
    (hone : (H 1).WordBound q R (γ * C₁) 0) (htwo : (H 2).WordBound q R (γ * C₂) 0)
    (htail : ∀ n, 3 ≤ n → n ≤ N + 1 → (H n).WordBound q R (γ * B ^ (n + 1)) 0) :
    (evaluateFamily (N+1) κ f H).WordBound q R
      (γ*(κ*C₁+κ^2*C₂+2*B*(κ*B)^3)) 0 := by
  let J (i : ℕ) := (H i).smul γ⁻¹
  have h := wordBound_evaluate_low_high N hN κ B C₁ C₂ hκ hB hsmall
    (fun i => γ⁻¹ • f i) J q R hR
    (fun t x θ => by change γ⁻¹ • f 0 (t,(x,θ)) = 0; rw [hzero t x θ,smul_zero])
    (hone.normalize_amplitude hγ) (htwo.normalize_amplitude hγ)
    (fun n hn hNn => (htail n hn hNn).normalize_amplitude hγ)
  have hs := h.smul γ
  rw [abs_of_pos hγ] at hs
  apply hs.ofRawEq
  intro t x θ
  change (∑ i ∈ range (N+1+1), κ^i • f i (t,(x,θ))) =
    γ • (∑ i ∈ range (N+1+1), κ^i • (γ⁻¹ • f i (t,(x,θ))))
  rw [smul_sum]
  apply sum_congr rfl
  intro i _
  rw [smul_smul,smul_smul]
  congr 1
  field_simp

end EulerPacketCylinderField.Field

namespace EulerPacketInitial

open Set Finset EulerSmoothLimit EulerPacketProfileRecursion EulerPacketPointJets
  EulerPacketCylinderField EulerPacketTimeProfile EulerPacketShiftArithmetic EulerFiniteGrades
  EulerPacketCoarseMajorant

variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {N : ℕ}
  {a : ℕ → Profile} {support : Set Space}
  (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
  (S : Scales (Icc (0 : ℝ) T)) (R : ℝ)
  (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
  (hR : 1 ≤ R) (ha : a 0 = 0) (t : Icc (0 : ℝ) T)

include hG hR ha

theorem highGrade_bound (n : ℕ) :
    (highGradeField G t n).WordBound 6 R (S.growth t*(3*S.H0^(2*n))) (highShift n) := by
  have hH := S.H0_pos.le
  have hγ := (S.growth_pos t).le
  have hf (i : ℕ) (hi : i ≤ N) :
      ((G i hi).high.freeze t).WordBound 6 R (S.growth t*S.H0^(2*i)) (highShift i) := by
    by_cases hi0 : i=0
    · subst i
      exact (Field.wordBound_of_zero _ (fun _ _ _ => by
          rw [ha]; rfl) 6 R (highShift 0)).mono_amplitude
        (zero_le_one.trans hR) (by positivity)
    · apply ((hG i hi (by omega)).high_freeze t).mono_amplitude (zero_le_one.trans hR)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ S.H0_one_le (by omega : 2*i-2 ≤ 2*i)) hγ
  have hc (i : ℕ) (hi : i ≤ N) :
      ((G i hi).corrector.freeze t).WordBound 6 R (S.growth t*S.H0^(2*i)) (highShift i) := by
    by_cases hi0 : i=0
    · subst i
      exact (Field.wordBound_of_zero _ (fun _ _ _ => by
          rw [ha]; rfl) 6 R (highShift 0)).mono_amplitude
        (zero_le_one.trans hR) (by positivity)
    · apply ((hG i hi (by omega)).corrector_freeze t).mono_amplitude (zero_le_one.trans hR)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ S.H0_one_le (by omega : 2*i-2 ≤ 2*i)) hγ
  have hf' := Field.wordBound_truncateFamily N _ (fun i hi => (G i hi).high.freeze t)
    6 R (fun i => S.growth t*S.H0^(2*i)) highShift (zero_le_one.trans hR)
    (fun i => mul_nonneg hγ (pow_nonneg hH _)) hf
  have hc' := Field.wordBound_truncateFamily N _ (fun i hi => (G i hi).corrector.freeze t)
    6 R (fun i => S.growth t*S.H0^(2*i)) highShift (zero_le_one.trans hR)
    (fun i => mul_nonneg hγ (pow_nonneg hH _)) hc
  cases n with
  | zero => exact (hf' 0).mono_amplitude (zero_le_one.trans hR) (by norm_num; linarith)
  | succ n =>
    have hh := (hc' n).mono_shift hR (mul_nonneg hγ (pow_nonneg hH _))
      (show highShift n ≤ highShift (n+1) by unfold highShift; omega)
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ S.H0_one_le (by
        omega : 2*n ≤ 2*(n+1))) hγ
    exact ((hf' (n+1)).add hh).mono_amplitude (zero_le_one.trans hR) (by
      have := mul_nonneg hγ (pow_nonneg hH (2*(n+1)))
      nlinarith)

theorem meanGrade_bound (n : ℕ) :
    (meanGradeField G t n).WordBound 6 R (3*S.H0^(2*n)) (highShift n) := by
  apply Field.wordBound_truncateFamily N _ _ 6 R (fun i => 3*S.H0^(2*i)) highShift
    (zero_le_one.trans hR) (fun i => mul_nonneg (by norm_num) (pow_nonneg S.H0_pos.le _))
  intro i hi
  by_cases hi0 : i=0
  · subst i
    exact (Field.wordBound_of_zero _ (fun _ _ _ => by
        rw [ha]; rfl) 6 R (highShift 0)).mono_amplitude
      (zero_le_one.trans hR) (by norm_num)
  · have h := ((hG i hi (by omega)).mean_freeze t).mono_shift hR (S.mean_pos i t).le
      (show meanShift i ≤ highShift i by unfold meanShift highShift; omega)
    apply h.mono_amplitude (zero_le_one.trans hR)
    have hp := S.mean_le_coarse i t
    have hH := pow_nonneg S.H0_pos.le (2*i)
    nlinarith

theorem high_bound (hN : 1 ≤ N) (C κ : ℝ) (hC : 1 ≤ C) (hκ : 0 ≤ κ)
    (hsmall : κ * tailBase R S.H0 C N ≤ 1 / 2) :
    (highField G t κ).WordBound 6 (4*R)
      (S.growth t*(κ*fixedVelocityGradeCost R S.H0 1+κ^2*fixedVelocityGradeCost R S.H0 2 +
        2*tailBase R S.H0 C N*(κ*tailBase R S.H0 C N)^3)) 0 := by
  apply Field.wordBound_evaluate_low_high_scaled N hN κ (tailBase R S.H0 C N)
    (fixedVelocityGradeCost R S.H0 1) (fixedVelocityGradeCost R S.H0 2) (S.growth t)
    hκ (tailBase_nonneg R S.H0 C (zero_le_one.trans hC) N) (S.growth_pos t) hsmall
    _ _ 6 (4*R) (by linarith)
  · intro s x θ
    have hz : timeSlice t (a 0).high = 0 := by rw [ha]; rfl
    rw [highGrade,assemble_zero N _ _ hz]
    rfl
  · exact (((highGrade_bound G S R hG hR ha t 1).normalize_amplitude (S.growth_pos
      t)).fixed_velocity_grade
      (zero_le_one.trans hR) S.H0_pos.le).restore_amplitude (S.growth_pos t)
  · exact (((highGrade_bound G S R hG hR ha t 2).normalize_amplitude (S.growth_pos
      t)).fixed_velocity_grade
      (zero_le_one.trans hR) S.H0_pos.le).restore_amplitude (S.growth_pos t)
  · intro n _ hn
    exact (((highGrade_bound G S R hG hR ha t n).normalize_amplitude (S.growth_pos
        t)).coarse_velocity_grade
      hR S.H0_one_le C hC N hN (by omega)).restore_amplitude (S.growth_pos t)

theorem mean_bound (hN : 1 ≤ N) (ha1 : (a 1).mean = 0) (C κ : ℝ) (hC : 1 ≤ C) (hκ : 0 ≤ κ)
    (hsmall : κ * tailBase R S.H0 C N ≤ 1 / 2) :
    (meanField G t κ).WordBound 6 (4*R)
      (κ^2*fixedVelocityGradeCost R S.H0 2 +
        2*tailBase R S.H0 C N*(κ*tailBase R S.H0 C N)^3) 0 := by
  have h := Field.wordBound_evaluate_low_high N hN κ (tailBase R S.H0 C N)
    0 (fixedVelocityGradeCost R S.H0 2) hκ
    (tailBase_nonneg R S.H0 C (zero_le_one.trans hC) N) hsmall
    (meanGrade N t a) (meanGradeField G t) 6 (4*R) (by linarith)
    (by intro s x θ; simp only [meanGrade,truncate_of_le N 0 _ (Nat.zero_le N)]; rw [ha]; rfl)
    (Field.wordBound_of_zero _
      (by intro s x θ; simp only [meanGrade,truncate_of_le N 1 _ hN]; rw [ha1]; rfl) 6 (4*R) 0)
    ((meanGrade_bound G S R hG hR ha t 2).fixed_velocity_grade (zero_le_one.trans hR) S.H0_pos.le)
    (fun n _ hn => (meanGrade_bound G S R hG hR ha t n).coarse_velocity_grade
      hR S.H0_one_le C hC N hN (by omega))
  simpa only [meanField,mean,mul_zero,zero_add] using h

end EulerPacketInitial
