/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerCauchy
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerRestriction

@[expose] public section

/-! A common short interval for an Euler family with Cauchy initial H3
data. A fixed tail member supplies the reference solution; the actual
stability theorem supplies the uniform H3 bound needed by the limit. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter Real MeasureTheory Finset EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
open scoped Topology

theorem tensorNorm_le_sub_add (A B : SmoothL2Field Space) (s : ℕ) :
    tensorNorm s A ≤ tensorNorm s (fieldSub A B)+tensorNorm s B := by
  unfold tensorNorm
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro n _
  rw [jetLp_fieldSub]
  have h := norm_add_le (A.jetLp n-B.jetLp n) (B.jetLp n)
  simpa only [sub_add_cancel] using h

namespace Evolution

variable {T : ℝ} {hT : 0 ≤ T}

theorem short_uniform_h3 (V : ℕ → Evolution T hT) (hpos : 0 < T)
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i, N ≤ i → ∀ j, N ≤ j →
      tensorNorm 3 (fieldSub ((V i).velocity ⟨0,le_rfl,hT⟩) ((V j).velocity ⟨0,le_rfl,hT⟩)) ≤ ε) :
    ∃ L : ℝ, ∃ hL : 0 < L, ∃ hLT : L ≤ T, ∃ N : ℕ, ∃ M : ℝ,
      ∀ n t, tensorNorm 3 (((V (n+N)).restrictTime L hL.le hLT).velocity t) ≤ M := by
  obtain ⟨N,hN⟩ := hCauchy (1/2560) (by norm_num)
  let U := V N
  let C := stabilityConstant U.referenceSize
  have hC : 0 < C := stabilityConstant_pos U.referenceSize_nonneg
  let L := min T (log 2/(3*C))
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have hL : 0 < L := lt_min hpos (div_pos hlog (by positivity))
  have hLT : L ≤ T := min_le_left _ _
  have hLe : 3*C*L ≤ log 2 := by
    have h := (le_div_iff₀ (show 0 < 3*C by positivity)).mp (min_le_right T (log 2/(3*C)))
    nlinarith only [h]
  have hexp : exp (3*C*L) ≤ 2 := by
    have h := exp_le_exp.mpr hLe
    rwa [exp_log (by norm_num : (0 : ℝ) < 2)] at h
  have hsmall : 640*(1/2560 : ℝ)*exp (3*C*L) ≤ 1/2 := by linarith only [hexp]
  let R := U.restrictTime L hL.le hLT
  refine ⟨L,hL,hLT,N,1/2+40*U.referenceSize,?_⟩
  intro n t
  let W := (V (n+N)).restrictTime L hL.le hLT
  have hi : tensorNorm 3 (R.difference W ⟨0,le_rfl,hL.le⟩) ≤ 1/2560 :=
    hN (n+N) (by omega) N le_rfl
  have hd : tensorNorm 3 (R.difference W t) ≤ 1/2 :=
    (R.h3_stability W U.referenceSize (1/2560)
      (U.restrictTime_referenceWordBound L hL.le hLT) (by norm_num) hi hsmall t).trans hsmall
  have hu : tensorNorm 3 (R.velocity t) ≤ 40*U.referenceSize :=
    tensorNorm_three_le _ _ (wordBound_mono (U.restrictTime_referenceWordBound L hL.le hLT t) (by
      omega))
  exact (tensorNorm_le_sub_add (W.velocity t) (R.velocity t) 3).trans (add_le_add hd hu)

end Evolution

theorem exists_local_evolution_of_cauchy {T : ℝ} {hT : 0 ≤ T}
    (V : ℕ → Evolution T hT) (hpos : 0 < T)
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i, N ≤ i → ∀ j, N ≤ j →
      tensorNorm 3 (fieldSub ((V i).velocity ⟨0,le_rfl,hT⟩) ((V j).velocity ⟨0,le_rfl,hT⟩)) ≤ ε)
    (hinit : ∀ q, ∃ R : ℝ, ∀ n, tensorNorm q ((V n).velocity ⟨0,le_rfl,hT⟩) ≤ R)
    (u0 : L2) (hu0 : Tendsto (fun n => ((V n).velocity ⟨0,le_rfl,hT⟩).toLp) atTop (𝓝 u0)) :
    ∃ L : ℝ, ∃ hL : 0 < L, L ≤ T ∧
      ∃ E : Evolution L hL.le, (E.velocity ⟨0,le_rfl,hL.le⟩).toLp=u0 := by
  obtain ⟨L,hL,hLT,N,M,hM⟩ := Evolution.short_uniform_h3 V hpos hCauchy
  let W := fun n => (V (n+N)).restrictTime L hL.le hLT
  have hb : ∀ q, ∃ R : ℝ, ∀ n, tensorNorm q ((W n).velocity ⟨0,le_rfl,hL.le⟩) ≤ R := by
    intro q
    obtain ⟨R,hR⟩ := hinit q
    exact ⟨R,fun n => hR (n+N)⟩
  have hc : Tendsto (fun n => ((W n).velocity ⟨0,le_rfl,hL.le⟩).toLp) atTop (𝓝 u0) := by
    exact hu0.comp (tendsto_add_atTop_nat N)
  refine ⟨L,hL,hLT,limitEvolutionOfH3 W hL M hM hb hc.cauchySeq,?_⟩
  exact limitEvolutionOfH3_initial W hL M hM hb hc.cauchySeq u0 hc

end EulerOrdinarySobolev
