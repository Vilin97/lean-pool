/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerLimit

/-! The packet-sequence form of ordinary Euler compactness: a common
H³ bound, uniform initial Sobolev bounds, and initial L² Cauchy data
produce an actual smooth Euler limit on the same positive interval. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerSmoothSobolev Finset
open scoped ContDiff Topology

theorem wordEnergy_le_tensorNorm (A : SmoothL2Field Space) (m : ℕ) :
    wordEnergy m A ≤ wordCount m*(tensorNorm m A)^2 := by
  calc
    _ ≤ ∑ n ∈ range (m+1), ∑ _w : Fin n → Fin 3, (tensorNorm m A)^2 := by
      apply sum_le_sum
      intro n hn
      apply sum_le_sum
      intro w _
      exact pow_le_pow_left₀ (norm_nonneg _) (wordBound_tensorNorm m A n
        (by have := mem_range.mp hn; omega) w) 2
    _ = _ := by
      simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_pow,Nat.cast_ofNat]
      rw [← sum_mul]
      rfl

namespace Evolution

variable {T : ℝ} {hT : 0 ≤ T}

theorem fieldPath_eq_velocityPath (U : Evolution T hT) :
    fieldPath U.velocity U.velocity_continuous=U.velocityPath := by
  apply ContinuousMap.ext
  intro t
  exact (U.velocityPath_apply t).symm

theorem gradient_le_h3 (U : Evolution T hT) (M : ℝ)
    (hM : ∀ t, tensorNorm 3 (U.velocity t) ≤ M) (t : Icc (0 : ℝ) T) (x : Space) :
    ‖fderiv ℝ (U.velocity t).field x‖ ≤ (9*smoothEmbeddingConstant)*M := by
  have h := real_smooth_fderiv_le_H3 3 (U.velocity t).field (U.velocity t).smooth
    (fun j _ => (U.velocity t).integrable j) x
  rw [← tensorNorm_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hM t)
    (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg))

theorem cauchyPath_of_initial (V : ℕ → Evolution T hT) (M : ℝ)
    (hM : ∀ k t, tensorNorm 3 ((V k).velocity t) ≤ M)
    (hinit : CauchySeq (fun k => ((V k).velocity ⟨0, le_rfl, hT⟩).toLp)) :
    CauchySeq (fun k => fieldPath (V k).velocity (V k).velocity_continuous) := by
  let K := (9*smoothEmbeddingConstant)*M
  have hM0 : 0 ≤ M := (tensorNorm_nonneg 3 ((V 0).velocity ⟨0,le_rfl,hT⟩)).trans (hM 0 _)
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) hM0
  have hK (k : ℕ) (t : Icc (0 : ℝ) T) (x : Space) :
      ‖fderiv ℝ ((V k).velocity t).field x‖ ≤ K := (V k).gradient_le_h3 M (hM k) t x
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hinit (ε/Real.exp (K*T)) (div_pos hε (Real.exp_pos _))
  refine ⟨N,fun j hj k hk => ?_⟩
  have hb := (V k).velocityPath_norm_sub_le (V j) K hK0 (hK k)
  have hi := mul_lt_mul_of_pos_right (hN j hj k hk) (Real.exp_pos (K*T))
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.exp_pos (K*T)))] at hi
  rw [dist_eq_norm,fieldPath_eq_velocityPath,fieldPath_eq_velocityPath]
  apply hb.trans_lt
  simpa only [dist_eq_norm,velocityPath_apply] using hi

theorem all_order_bounds_of_h3 (V : ℕ → Evolution T hT) (M : ℝ)
    (hM : ∀ k t, tensorNorm 3 ((V k).velocity t) ≤ M)
    (hinit : ∀ q, ∃ R : ℝ, ∀ k, tensorNorm q ((V k).velocity ⟨0, le_rfl, hT⟩) ≤ R) :
    ∀ q, ∃ C : ℝ, ∀ k t, tensorNorm q ((V k).velocity t) ≤ C := by
  intro q
  by_cases hq : 3 ≤ q
  · obtain ⟨R,hR⟩ := hinit q
    have hR0 : 0 ≤ R := (tensorNorm_nonneg q ((V 0).velocity ⟨0,le_rfl,hT⟩)).trans (hR 0)
    refine ⟨wordCount q*Real.sqrt (wordCount q*R^2*Real.exp (tameEnergyConstant q*M*T)),?_⟩
    intro k t
    apply (tensorNorm_le_energy ((V k).velocity t) q).trans
    apply mul_le_mul_of_nonneg_left _ (wordCount_nonneg q)
    apply Real.sqrt_le_sqrt
    apply ((V k).higher_energy_of_h3 q hq M (hM k) t).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact (wordEnergy_le_tensorNorm _ q).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (tensorNorm_nonneg q _) (hR k) 2) (wordCount_nonneg q))
  · refine ⟨wordCount q*M,?_⟩
    intro k t
    apply tensorNorm_le_wordCount
    intro n hn w
    exact (wordBound_tensorNorm 3 ((V k).velocity t) n (by omega) w).trans (hM k t)

end Evolution

variable {T : ℝ} {hT : 0 ≤ T}

/-- Limit evolution of H3, given by `limitEvolution V hpos (Evolution.all_order_bounds_of_h3 V M
hM hinit) (Evolution.cauchyPath_of_initial V M hM hcauchy)`. -/
def limitEvolutionOfH3 (V : ℕ → Evolution T hT) (hpos : 0 < T) (M : ℝ)
    (hM : ∀ k t, tensorNorm 3 ((V k).velocity t) ≤ M)
    (hinit : ∀ q, ∃ R : ℝ, ∀ k, tensorNorm q ((V k).velocity ⟨0, le_rfl, hT⟩) ≤ R)
    (hcauchy : CauchySeq (fun k => ((V k).velocity ⟨0, le_rfl, hT⟩).toLp)) : Evolution T hT :=
  limitEvolution V hpos (Evolution.all_order_bounds_of_h3 V M hM hinit)
    (Evolution.cauchyPath_of_initial V M hM hcauchy)

theorem limitEvolutionOfH3_convergence (V : ℕ → Evolution T hT) (hpos : 0 < T) (M : ℝ)
    (hM : ∀ k t, tensorNorm 3 ((V k).velocity t) ≤ M)
    (hinit : ∀ q, ∃ R : ℝ, ∀ k, tensorNorm q ((V k).velocity ⟨0, le_rfl, hT⟩) ≤ R)
    (hcauchy : CauchySeq (fun k => ((V k).velocity ⟨0, le_rfl, hT⟩).toLp)) (q : ℕ) :
    Tendsto (fun k => jetPath (V k).velocity (V k).velocity_continuous q) atTop
      (𝓝 (jetPath (limitEvolutionOfH3 V hpos M hM hinit hcauchy).velocity
        (limitEvolutionOfH3 V hpos M hM hinit hcauchy).velocity_continuous q)) :=
  limitEvolution_jet_convergence V hpos (Evolution.all_order_bounds_of_h3 V M hM hinit)
    (Evolution.cauchyPath_of_initial V M hM hcauchy) q

theorem limitEvolutionOfH3_initial (V : ℕ → Evolution T hT) (hpos : 0 < T) (M : ℝ)
    (hM : ∀ k t, tensorNorm 3 ((V k).velocity t) ≤ M)
    (hinit : ∀ q, ∃ R : ℝ, ∀ k, tensorNorm q ((V k).velocity ⟨0, le_rfl, hT⟩) ≤ R)
    (hcauchy : CauchySeq (fun k => ((V k).velocity ⟨0, le_rfl, hT⟩).toLp)) (u0 : L2)
    (hu0 : Tendsto (fun k => ((V k).velocity ⟨0, le_rfl, hT⟩).toLp) atTop (𝓝 u0)) :
    ((limitEvolutionOfH3 V hpos M hM hinit hcauchy).velocity ⟨0,le_rfl,hT⟩).toLp=u0 :=
  limitEvolution_initial V hpos (Evolution.all_order_bounds_of_h3 V M hM hinit)
    (Evolution.cauchyPath_of_initial V M hM hcauchy) u0 hu0

end EulerOrdinarySobolev
