/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBound

/-! Relative residual assembly. The ten named quantitative leaves remain
explicit inputs; continuity supplies measurability and slice L2 membership.
In particular the tenth leaf is `R46`, not omitted from the residual. -/

@[expose] public section

noncomputable section
open scoped ENNReal
open MeasureTheory Homogenization AVenhance AVenhance.Infra.Section5
open AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.RelativeError

/-- Relative residual assembly in the centered ten-term family. Only the
three grouped slots are centered; their common mean-zero identity restores
the actual source residual sum. -/
theorem relative_residual_of_centered_term_bounds {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e b : ℝ → Vec 2 → Vec 2) (C ε δ S : ℝ)
    (hResidual : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x,
      residualIdentity I hΦ m κm T d e b t x)
    (hContinuous : ∀ i, i < 10 → ContinuousOn
      (fun p : ℝ × Vec 2 => section5Term I hΦ m κm T d e i p.1 p.2)
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ))
    (hgroup : ∀ t ∈ Set.Ioo (0 : ℝ) 1, MeanZeroOn unitCube (fun x =>
      twistie4 I hΦ m κm T t x + twistie5 I hΦ m κm T t x + normie3 I hΦ m κm T t x))
    (hterms : ∀ i, i < 10 → timeHMinusOneNorm
      (section5CenteredTerm I hΦ m κm T d e i) ≤
      ENNReal.ofReal (C * Real.sqrt κm * ε ^ δ * S)) :
    timeHMinusOneNorm (fun t x => advDiffOp b κm (I.ansatz hΦ m κm T) t x) ≤
      ENNReal.ofReal ((10 * C) * Real.sqrt κm * ε ^ δ * S) := by
  have hc : ∀ i, i < 10 → ContinuousOn
      (fun p : ℝ × Vec 2 => section5CenteredTerm I hΦ m κm T d e i p.1 p.2)
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ) := by
    intro i hi
    interval_cases i
    · exact hContinuous 0 (by norm_num)
    · exact hContinuous 1 (by norm_num)
    · exact hContinuous 2 (by norm_num)
    · exact continuousOn_centerCell (hContinuous 3 (by norm_num))
    · exact continuousOn_centerCell (hContinuous 4 (by norm_num))
    · exact hContinuous 5 (by norm_num)
    · exact hContinuous 6 (by norm_num)
    · exact hContinuous 7 (by norm_num)
    · exact continuousOn_centerCell (hContinuous 8 (by norm_num))
    · exact hContinuous 9 (by norm_num)
  have heq : timeHMinusOneNorm
      (fun t x => advDiffOp b κm (I.ansatz hΦ m κm T) t x) =
      timeHMinusOneNorm (fun t x => ∑ i ∈ Finset.range 10,
        section5CenteredTerm I hΦ m κm T d e i t x) := by
    unfold timeHMinusOneNorm
    congr 1
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have hf : (fun x => advDiffOp b κm (I.ansatz hΦ m κm T) t x) =
        fun x => ∑ i ∈ Finset.range 10, section5CenteredTerm I hΦ m κm T d e i t x := by
      funext x
      rw [sum_section5CenteredTerm_eq I hΦ m κm T d e t
        (fun i hi => memL2On_of_continuousOn_slice (hContinuous i hi) ht) (hgroup t ht) x]
      rw [hResidual t ht x]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, section5Term, nineTerms]
      ring
    change hMinusOneNorm (fun x => advDiffOp b κm (I.ansatz hΦ m κm T) t x) ^ 2 = _
    rw [hf]
  rw [heq]
  have hb := timeHMinusOneNorm_sum_range_le (by norm_num : 1 ≤ 10) hc
  apply (hb.trans (Finset.sum_le_sum fun i hi => hterms i (Finset.mem_range.mp hi))).trans_eq
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [show ((10 : ℕ) : ENNReal) = ENNReal.ofReal 10 by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]
  congr 1
  ring

theorem relative_residual_of_term_bounds {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (d e b : ℝ → Vec 2 → Vec 2) (C ε δ S : ℝ)
    (hResidual : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x,
      residualIdentity I hΦ m κm T d e b t x)
    (hContinuous : ∀ i, i < 10 → ContinuousOn
      (fun p : ℝ × Vec 2 => section5Term I hΦ m κm T d e i p.1 p.2)
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ))
    (hgroup : ∀ t ∈ Set.Ioo (0 : ℝ) 1, MeanZeroOn unitCube (fun x =>
      twistie4 I hΦ m κm T t x + twistie5 I hΦ m κm T t x + normie3 I hΦ m κm T t x))
    (hcutoff1 : timeHMinusOneNorm (cutoff1 I hΦ m κm T) ≤
      ENNReal.ofReal (C * Real.sqrt κm * ε ^ δ * S))
    (htwistie1 : timeHMinusOneNorm (twistie1 I hΦ m κm T) ≤
      ENNReal.ofReal (C * Real.sqrt κm * ε ^ δ * S))
    (htwistie3 : timeHMinusOneNorm (twistie3 I hΦ m κm T) ≤
      ENNReal.ofReal (C * Real.sqrt κm * ε ^ δ * S))
    (htwistie4 : timeHMinusOneNorm (fun t => centerCell (twistie4 I hΦ m κm T t)) ≤
      ENNReal.ofReal (C * Real.sqrt κm * ε ^ δ * S))
    (htwistie5 : timeHMinusOneNorm (fun t => centerCell (twistie5 I hΦ m κm T t)) ≤
      ENNReal.ofReal (C * Real.sqrt κm * ε ^ δ * S))
    (hnormie1 : timeHMinusOneNorm (normie1 I hΦ m κm T) ≤
      ENNReal.ofReal (C * Real.sqrt κm * ε ^ δ * S))
    (hnormie2 : timeHMinusOneNorm (normie2 I hΦ m κm T) ≤
      ENNReal.ofReal (C * Real.sqrt κm * ε ^ δ * S))
    (htiny : timeHMinusOneNorm (tiny I hΦ m κm d e) ≤
      ENNReal.ofReal (C * Real.sqrt κm * ε ^ δ * S))
    (hnormie3 : timeHMinusOneNorm (fun t => centerCell (normie3 I hΦ m κm T t)) ≤
      ENNReal.ofReal (C * Real.sqrt κm * ε ^ δ * S))
    (hR46 : timeHMinusOneNorm (R46 I hΦ m κm T) ≤
      ENNReal.ofReal (C * Real.sqrt κm * ε ^ δ * S)) :
    timeHMinusOneNorm (fun t x => advDiffOp b κm (I.ansatz hΦ m κm T) t x) ≤
      ENNReal.ofReal ((10 * C) * Real.sqrt κm * ε ^ δ * S) := by
  have hterms : ∀ i, i < 10 → timeHMinusOneNorm (section5CenteredTerm I hΦ m κm T d e i) ≤
      ENNReal.ofReal (C * Real.sqrt κm * ε ^ δ * S) := by
    intro i hi
    interval_cases i
    · exact hcutoff1
    · exact htwistie1
    · exact htwistie3
    · exact htwistie4
    · exact htwistie5
    · exact hnormie1
    · exact hnormie2
    · exact htiny
    · exact hnormie3
    · exact hR46
  exact relative_residual_of_centered_term_bounds I hΦ m κm T d e b C ε δ S
    hResidual hContinuous hgroup hterms

/-- A relative finite ENNReal bound supplies both finiteness and the normalized
real bound; `toReal` is never used on an infinite residual. -/
theorem relative_residual_finite_and_normalized {κ C ε δ S : ℝ} {F : ENNReal}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hε : 0 < ε) (hS : 0 ≤ S)
    (hF : F ≤ ENNReal.ofReal (C * Real.sqrt κ * ε ^ δ * S)) :
    F ≠ ⊤ ∧ F.toReal / Real.sqrt κ ≤ C * ε ^ δ * S := by
  have hfin : F ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hF
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hF
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  refine ⟨hfin, (div_le_iff₀ (Real.sqrt_pos.2 hκ)).2 ?_⟩
  exact hreal.trans_eq (by ring)

end AVenhance.Infra.Section5.RelativeError
