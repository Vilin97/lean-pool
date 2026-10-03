/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyStreamDiff

/-! # Weak dissipation versus classical dissipation

From the stream-difference estimate
`stream_difference_energy` with `η/κ ≤ 1/10` and the squared triangle inequality, a weak solution
for the limit drift dissipates at least `49/100` of the classical dissipation for the smooth stream
`Ψ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance

theorem spaceTimeGradNormSq_nonneg' (D : ℝ → Vec 2 → Vec 2) : 0 ≤ spaceTimeGradNormSq D :=
  integral_nonneg fun p => by
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

theorem spaceTimeGrad_integrable {D : ℝ → Vec 2 → Vec 2}
    (hD : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => D p.1 p.2 i) 2 (volume.restrict timeCube)) :
    Integrable (fun p : ℝ × Vec 2 => vecNormSq (D p.1 p.2)) (volume.restrict timeCube) := by
  have hi : ∀ i : Fin 2, Integrable (fun p : ℝ × Vec 2 => D p.1 p.2 i ^ 2)
      (volume.restrict timeCube) := by
    intro i
    have h := (hD i).integrable_norm_rpow (by norm_num) (by norm_num)
    rw [show (2 : ENNReal).toReal = 2 by norm_num] at h
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using h
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hi i)
  simpa only [vecNormSq, vecDot, ← pow_two] using hsum

theorem AssemblyGradient.square_triangle' (u v : ℝ) : v ^ 2 ≤ 2 * u ^ 2 + 2 * (u - v) ^ 2 := by
  nlinarith only [sq_nonneg (2 * u - v)]

/-- Squared triangle inequality for the spacetime gradient norm. -/
theorem spaceTimeGrad_triangle {D E : ℝ → Vec 2 → Vec 2}
    (hD : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => D p.1 p.2 i) 2 (volume.restrict timeCube))
    (hE : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => E p.1 p.2 i) 2 (volume.restrict timeCube)) :
    spaceTimeGradNormSq E ≤ 2 * spaceTimeGradNormSq D +
      2 * spaceTimeGradNormSq (fun t x => D t x - E t x) := by
  have hdiff := spaceTimeGrad_integrable (D := fun t x => D t x - E t x)
    (fun i => (hD i).sub (hE i))
  have hInt := ((spaceTimeGrad_integrable hD).const_mul 2).add (hdiff.const_mul 2)
  have hp : ∀ p : ℝ × Vec 2, vecNormSq (E p.1 p.2) ≤
      2 * vecNormSq (D p.1 p.2) + 2 * vecNormSq (D p.1 p.2 - E p.1 p.2) := by
    intro p
    simp only [vecNormSq, vecDot, ← pow_two, Finset.mul_sum, ← Finset.sum_add_distrib,
      Pi.sub_apply]
    exact Finset.sum_le_sum (fun i _ => AssemblyGradient.square_triangle' _ _)
  have h := integral_mono (spaceTimeGrad_integrable hE) hInt hp
  simpa only [Pi.add_apply,
    integral_add ((spaceTimeGrad_integrable hD).const_mul 2) (hdiff.const_mul 2),
    integral_const_mul, spaceTimeGradNormSq] using h

/-- Abstract form: `d ≤ a/10` in the `√κ`-weighted norms gives `49/100 · κ S₂ ≤ κ S_D`. -/
theorem weighted_triangle_real {κ S1 S2 SD : ℝ} (hκ : 0 < κ) (h1 : 0 ≤ S1) (h2 : 0 ≤ S2)
    (htri : S2 ≤ 2 * SD + 2 * S1)
    (hd : Real.sqrt κ * Real.sqrt S1 ≤ 1 / 10 * (Real.sqrt κ * Real.sqrt S2)) :
    49 / 100 * (κ * S2) ≤ κ * SD := by
  have ha : 0 ≤ Real.sqrt κ * Real.sqrt S1 := by positivity
  have hsq := pow_le_pow_left₀ ha hd 2
  have e1 : (Real.sqrt κ * Real.sqrt S1) ^ 2 = κ * S1 := by
    rw [mul_pow, Real.sq_sqrt hκ.le, Real.sq_sqrt h1]
  have e2 : (1 / 10 * (Real.sqrt κ * Real.sqrt S2)) ^ 2 = 1 / 100 * (κ * S2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hκ.le, Real.sq_sqrt h2]
    ring
  rw [e1, e2] at hsq
  have := mul_le_mul_of_nonneg_left htri hκ.le
  nlinarith only [hsq, this]

/-- Weak dissipation for the limit drift dominates `49/100` of the classical dissipation for a
smooth stream `Ψ` uniformly `η`-close to `φ`, provided `η/κ ≤ 1/10`. -/
theorem weak_dissipation_ge_classical {b : ℝ → Vec 2 → Vec 2}
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t))
    (hdiv : IsDivFree b)
    {φ : ℝ → Vec 2 → ℝ}
    (hφ_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => φ p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hφ_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (φ t))
    (hφ_diff : ∀ t ∈ Set.Icc (0 : ℝ) 1, Differentiable ℝ (φ t))
    (hbφ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, b t x = streamVel φ t x)
    {Ψ : ℝ → Vec 2 → ℝ} (hΨ : IsAdmissibleStream Ψ) {κ : ℝ} (hκ : 0 < κ)
    {g : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgp : IsZ2Periodic g)
    {θM : ℝ → Vec 2 → ℝ}
    (hθM : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) g θM)
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hθ : IsWeakSolutionGrad b κ g θ Dθ)
    {η : ℝ} (hη : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, |φ t x - Ψ t x| ≤ η)
    (hηκ : η / κ ≤ 1 / 10) :
    49 / 100 * (κ * spaceTimeGradNormSq (fun t x => spaceGrad (θM t) x)) ≤
      κ * spaceTimeGradNormSq Dθ := by
  have hdiff := stream_difference_energy hb_meas hb_bdd hb_per hdiv hφ_meas hφ_per hφ_diff hbφ
    hΨ hκ hg hgp hθM hθ hη
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη 0 ⟨le_rfl, zero_le_one⟩ 0)
  have hbM : Continuous (fun p : ℝ × Vec 2 => streamVel Ψ p.1 p.2) :=
    (Infra.Classical.streamVel_smoothPeriodic Ψ hΨ).smooth.continuous
  have hM := classical_isWeakSolutionGrad hbM hθM
  have htri := spaceTimeGrad_triangle (D := Dθ) (E := fun t x => spaceGrad (θM t) x) hθ.2.2.2.1
    hM.2.2.2.1
  have hS := spaceTimeGradNormSq_nonneg' (fun t x => spaceGrad (θM t) x)
  have hsqrt : 0 ≤ Real.sqrt κ * Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (θM t) x)) :=
    by positivity
  have hdiff' : Real.sqrt κ * Real.sqrt (spaceTimeGradNormSq
        (fun t x => Dθ t x - spaceGrad (θM t) x)) ≤
      1 / 10 * (Real.sqrt κ * Real.sqrt (spaceTimeGradNormSq
        (fun t x => spaceGrad (θM t) x))) :=
    hdiff.trans (mul_le_mul_of_nonneg_right hηκ hsqrt)
  exact weighted_triangle_real hκ (spaceTimeGradNormSq_nonneg' _) hS htri hdiff'

end AVenhance.Infra.Section5.RelativeError

end
