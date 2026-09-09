/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocitySystem
public import LeanPool.NavierStokesAndEuler.Euler.ClosedIntervalDerivativeExtension

@[expose] public section

/-!
The actual closed-interval packet equations feed the checked scalar
amplification theorem.  Endpoint derivatives are extended explicitly; only
the first two physical transport rows enter the comparison.
-/

noncomputable section


namespace EulerPacketMovingFrame

open Set EulerPacketRay EulerPacketStage EulerPacketPerturbation
  EulerClosedIntervalDerivativeExtension

/-- Relative amplification for paths with their genuine within-interval
equations.  The ideal reference solutions are constructed by the scalar ODE
existence theorem, not supplied as extra assumptions. -/
theorem controlled_stage_references_within
    {σ Θ T e ε lam : ℝ} {U V P Q N : ℝ → ℝ} {R A C : ℝ → Fin 3 → Fin 3 → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 < T) (hT : T ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hlam : 0 ≤ lam) (hsmall : 1000000 * stabilityConstant * e * Θ ^ 40 ≤ 1)
    (hRc : ∀ i j, ContinuousOn (fun t => R t i j) (Icc 0 T))
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hCc : ∀ i j, ContinuousOn (fun t => C t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivWithinAt P
      (R t 0 0 * P t + R t 0 1 * Q t + R t 0 2 * N t) (Icc 0 T) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q
      (R t 1 0 * P t + R t 1 1 * Q t + R t 1 2 * N t) (Icc 0 T) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivWithinAt N
      (R t 2 0 * P t + R t 2 1 * Q t + R t 2 2 * N t) (Icc 0 T) t)
    (hU : ∀ t ∈ Icc 0 T, HasDerivWithinAt U
      (velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) (Icc 0 T) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivWithinAt V
      (velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) (Icc 0 T) t)
    (hRclose : ∀ t ∈ Icc 0 T, ∀ i j, |R t i j - idealRayEntry (σ ^ 2) i j| ≤ 4 * e)
    (hAclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e)
    (hCclose : ∀ t ∈ Icc 0 T, ∀ j,
      |C t 0 j - idealUnprojectedEntry 0 j| ≤ 5 * e ∧
      |C t 1 j - idealUnprojectedEntry 1 j| ≤ 5 * e)
    (hrayInitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e)
    (hU0 : U 0 = -lam) (hV0 : V 0 = 1) :
    ∃ F F₁ Z Z₁ : ℝ → ℝ,
      F 0 = 1 ∧ F₁ 0 = 0 ∧ Z 0 = 1 ∧ Z₁ 0 = lam ∧
      (∀ t, HasDerivAt F (F₁ t) t) ∧ (∀ t, HasDerivAt Z (Z₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t) ∧
      (∀ t ∈ Icc 0 T, |V t - Z t| + |U t + Z₁ t| ≤
        160000000 * e * Θ ^ 29 * (1 + lam) * F t) ∧
      (∀ t ∈ Icc 1 T, 0 < V t ∧
        |V t / Z t - 1| ≤ stabilityConstant * e * Θ ^ 29 ∧
        |U t / V t + Z₁ t / Z t| ≤ 10 * (stabilityConstant * e * Θ ^ 29)) := by
  obtain ⟨P', hPeq, hP'⟩ := exists_extension hT0 hP
  obtain ⟨Q', hQeq, hQ'⟩ := exists_extension hT0 hQ
  obtain ⟨N', hNeq, hN'⟩ := exists_extension hT0 hN
  obtain ⟨U', hUeq, hU'⟩ := exists_extension hT0 hU
  obtain ⟨V', hVeq, hV'⟩ := exists_extension hT0 hV
  have h0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  have hC'c : ∀ i j, ContinuousOn (fun t => firstTwoRows (C t) i j) (Icc 0 T) := by
    intro i j
    by_cases hi : i = 0
    · simpa only [firstTwoRows, hi, ite_true] using hCc 0 j
    · simpa only [firstTwoRows, hi, ite_false] using hCc 1 j
  have hC'close : ∀ t ∈ Icc 0 T, ∀ i j,
      |firstTwoRows (C t) i j - idealUnprojectedEntry i j| ≤ 5*e := by
    intro t ht i j
    fin_cases i
    · simpa [firstTwoRows] using (hCclose t ht j).1
    · simpa [firstTwoRows] using (hCclose t ht j).2
    · simpa [firstTwoRows, idealUnprojectedEntry] using (hCclose t ht j).2
  have hPe : ∀ t ∈ Icc 0 T, HasDerivAt P'
      (R t 0 0*P' t+R t 0 1*Q' t+R t 0 2*N' t) t := by
    intro t ht
    simpa only [hPeq ht, hQeq ht, hNeq ht] using hP' t ht
  have hQe : ∀ t ∈ Icc 0 T, HasDerivAt Q'
      (R t 1 0*P' t+R t 1 1*Q' t+R t 1 2*N' t) t := by
    intro t ht
    simpa only [hPeq ht, hQeq ht, hNeq ht] using hQ' t ht
  have hNe : ∀ t ∈ Icc 0 T, HasDerivAt N'
      (R t 2 0*P' t+R t 2 1*Q' t+R t 2 2*N' t) t := by
    intro t ht
    simpa only [hPeq ht, hQeq ht, hNeq ht] using hN' t ht
  have hUe : ∀ t ∈ Icc 0 T, HasDerivAt U'
      (velocityFirstRhs (A t) (firstTwoRows (C t)) ε (P' t) (Q' t) (N' t) (U' t) (V' t)) t := by
    intro t ht
    simpa only [velocityFirstRhs_firstTwoRows, hPeq ht, hQeq ht, hNeq ht, hUeq ht, hVeq ht] using
      hU' t ht
  have hVe : ∀ t ∈ Icc 0 T, HasDerivAt V'
      (velocitySecondRhs (A t) (firstTwoRows (C t)) ε (P' t) (Q' t) (N' t) (U' t) (V' t)) t := by
    intro t ht
    simpa only [velocitySecondRhs_firstTwoRows, hPeq ht, hQeq ht, hNeq ht, hUeq ht, hVeq ht] using
      hV' t ht
  have hri : norm3 (P' 0) (Q' 0) (N' 0-1) ≤ e := by
    simpa only [hPeq h0, hQeq h0, hNeq h0] using hrayInitial
  have hui : U' 0 = -lam := (hUeq h0).trans hU0
  have hvi : V' 0 = 1 := (hVeq h0).trans hV0
  obtain ⟨F, F₁, Z, Z₁, hF0, hF₁0, hZ0, hZ₁0, hF, hZ, hfF, hfZ, herr, hrel⟩ :=
    controlled_stage_references hσ hσsmall hΘ hT0.le hT he hε hεe hlam hsmall
      hRc hAc hC'c hPe hQe hNe hUe hVe hRclose hAclose hC'close hri hui hvi
  refine ⟨F, F₁, Z, Z₁, hF0, hF₁0, hZ0, hZ₁0, hF, hZ, hfF, hfZ, ?_, ?_⟩
  · intro t ht
    simpa only [hUeq ht, hVeq ht] using herr t ht
  · intro t ht
    have ht' : t ∈ Icc 0 T := ⟨le_trans (by norm_num) ht.1, ht.2⟩
    simpa only [hUeq ht', hVeq ht'] using hrel t ht

end EulerPacketMovingFrame
