/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedPressureBudgets
public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureCovector
public import LeanPool.NavierStokesAndEuler.Euler.PacketRemainderBounds

@[expose] public section

/-! The finite pressure covector differs from the leading angular
primary by an actual O(k⁻²) cylinder field, uniformly in the truncation
length selected by the source frequency guard. -/

noncomputable section

namespace EulerPacketPressure

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketCylinderField EulerPacketTimeProfile EulerPacketShiftArithmetic
  EulerPacketCoarseMajorant EulerPacketFiniteFrequency EulerFiniteGrades

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile} {support : Set Space}
  (hT : 0 < T) (m : Space)
  (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le support (a i))
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (K : ∀ i, i ≤ N → PressureBudget P T hT.le m (a i) S R i)

def covectorGradeField (i : ℕ) : Field P T (covectorGrades N m a i) :=
  Field.assembleFamily N
    (fun j => pressureGradient (a j).meanPressure+angularPressure m (a j).highPressure)
    (fun j => pressureGradient (a j).highPressure)
    (fun j hj => (K j hj).mean.add (K j hj).angular) (fun j hj => (G j hj).pressure) i

variable (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
  (hR : 1 ≤ R) (ha : a 0=0)

include hG hR ha in
theorem covectorGrade_bound (i : ℕ) :
    (covectorGradeField hT m G K i).WordBound 6 R (3*S.H0^(2*i)) (highShift i) := by
  apply Field.wordBound_assembleFamily N _ _ _ _ R S.H0 hR S.H0_one_le
  · intro j hj
    by_cases hj0 : j=0
    · subst j
      have hz : ∀ (t : Icc (0 : ℝ) T) x θ,
          (pressureGradient (a 0).meanPressure+angularPressure m (a 0).highPressure) (t,(x,θ))=0 :=
            by
        intro t x θ
        rw [ha]
        simp [pressureGradient,angularPressure,pressureJet_zero]
      exact (Field.wordBound_of_zero ((K 0 hj).mean.add (K 0 hj).angular) hz 6 R (highShift
        0)).mono_amplitude
        (zero_le_one.trans hR) (by norm_num)
    · have hm := (K j hj).mean_bound.remove_profile hT.le (S.mean j) (S.mean_pos j)
        (S.H0^(2*j)) (pow_nonneg S.H0_pos.le _) (S.mean_le_coarse j)
      have hq := (K j hj).angular_bound.remove_profile hT.le (S.high j) (S.high_pos j)
        (S.H0^(2*j)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse j (by omega))
      simp only [mul_one] at hm hq
      have hm' := hm.mono_shift hR (pow_nonneg S.H0_pos.le _)
        (show meanShift j ≤ highShift j by unfold meanShift highShift; omega)
      change ((K j hj).mean.add (K j hj).angular).WordBound 6 R (2*S.H0^(2*j)) (highShift j)
      rw [two_mul (S.H0^(2*j))]
      exact hm'.add hq
  · intro j hj
    by_cases hj0 : j=0
    · subst j
      exact (Field.wordBound_of_zero (G 0 hj).pressure
        (fun _ _ _ => by rw [ha]; simp [pressureGradient,pressureJet_zero])
        6 R (highShift 0)).mono_amplitude (zero_le_one.trans hR) (by norm_num)
    · exact (hG j hj (by omega)).pressure_unnormalized (by omega)

include ha in
theorem covectorGrades_zero : covectorGrades N m a 0=0 := by
  apply assemble_zero
  rw [ha]
  funext z
  simp [pressureGradient,angularPressure,pressureJet_zero]

include ha in
theorem covectorGrades_one (hN : 1 ≤ N) (hm : (a 1).meanPressure=0) :
    covectorGrades N m a 1=angularPressure m (a 1).highPressure := by
  rw [covectorGrades,assemble_interior N 1 le_rfl hN]
  simp only [Nat.sub_self,hm,ha]
  funext z
  simp [pressureGradient,angularPressure,pressureJet_zero]

def covectorRemainder (κ : ℝ) : VectorField :=
  fieldSum (N+1) κ (covectorGrades N m a)-κ • angularPressure m (a 1).highPressure

def covectorRemainderField (hN : 1 ≤ N) (hm : (a 1).meanPressure=0) (κ : ℝ) :
    Field P T (covectorRemainder (N := N) (a := a) m κ) :=
  (Field.evaluateRemainder (N+1) (by omega) κ (covectorGrades N m a)
    (covectorGradeField hT m G K)).congr
      (fun _ _ _ => by rw [covectorGrades_one m ha hN hm]; rfl)

include hG hR in
theorem covectorRemainder_bound (hN : 1 ≤ N) (hm : (a 1).meanPressure=0)
    {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)
    (k : ℝ) (hk : 4 ≤ k) (hbase : tailBase R S.H0 BC.termCost N ≤ k^(1/100 : ℝ)) :
    (covectorRemainderField hT m G K ha hN hm k⁻¹).WordBound 6 (4*R)
      ((fixedVelocityGradeCost R S.H0 2+2)/k^2) 0 := by
  have hk0 : 0 < k := by linarith
  let B := tailBase R S.H0 BC.termCost N
  have hB : 0 ≤ B := tailBase_nonneg R S.H0 BC.termCost BC.termCost_nonneg N
  have hsmall : k⁻¹*B ≤ 1/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using EulerPacketTailBound.grade_ratio_le_half k B hk hbase
  have hz := covectorGrades_zero (N := N) m ha
  have h := Field.wordBound_evaluateRemainder N hN k⁻¹ B (fixedVelocityGradeCost R S.H0 2)
    (inv_nonneg.mpr hk0.le) hB hsmall (covectorGrades N m a) (covectorGradeField hT m G K)
    6 (4*R) (by linarith) (fun _ _ _ => by rw [hz]; rfl)
    ((covectorGrade_bound hT m G K hG hR ha 2).fixed_velocity_grade (zero_le_one.trans hR)
      S.H0_pos.le)
    (fun n _ hn => (covectorGrade_bound hT m G K hG hR ha n).coarse_velocity_grade
      hR S.H0_one_le BC.termCost BC.one_le_termCost N hN (by omega))
  exact (h.mono_amplitude (by linarith)
    (remainder_low_high_le k B (fixedVelocityGradeCost R S.H0 2) hk0
      (fourth_power_le_frequency k B (by linarith) hB hbase))).of_path_eq _ rfl

end EulerPacketPressure
