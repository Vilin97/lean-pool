/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import Mathlib.Topology.Connected.PathConnected

/-!
# LeanPool.DirectedTopologyLean4.UnitIntervalAux
-/

/-
  This file contains lemmas about
  * elements being contained in the unit interval.
  * relations between elements in the unit interval.
-/

open scoped unitInterval

namespace unitIAux

lemma zero_le (T : I) : ⟨0, unitInterval.zero_mem⟩ ≤ T := Subtype.coe_le_coe.mp T.2.1
lemma le_one (T : I) : T ≤ ⟨1, unitInterval.one_mem⟩:= Subtype.coe_le_coe.mp T.2.2

lemma double_pos_of_pos {T : I} (hT₀ : 0 < T) : 0 < (2 * T : ℝ) :=
  mul_pos two_pos hT₀
lemma double_sigma_pos_of_lt_one {T : I} (hT₁ : T < 1) : 0 < (2 * (1 - T) : ℝ) :=
  mul_pos two_pos (by simpa using hT₁)

lemma double_mem_I {t : I} (ht : ↑t ≤ (2⁻¹ : ℝ)) : 2 * (t : ℝ) ∈ I := by
  refine ⟨mul_nonneg zero_le_two t.2.1, ?_⟩
  calc 2 * (t : ℝ)
      _ ≤ 2 * 2⁻¹ := (mul_le_mul_iff_of_pos_left two_pos).mpr ht
      _ = 1 := by norm_num

lemma double_sub_one_mem_I {t : I} (ht : (2⁻¹ : ℝ) ≤ ↑t) : 2 * (t : ℝ) - 1 ∈ I := by
  refine ⟨?_, ?_⟩
  · calc (0 : ℝ) = 2 * (2⁻¹ : ℝ) - 1 := by norm_num
      _ ≤ 2 * ↑t - 1 :=
        sub_le_sub_right ((mul_le_mul_iff_of_pos_left (by norm_num)).mpr ht) 1
  · calc 2 * (t : ℝ) - 1
      _ ≤ 2 * 1 - 1 :=
        sub_le_sub_right ((mul_le_mul_iff_of_pos_left (by norm_num)).mpr t.2.2) 1
      _ = 1         := by norm_num

lemma interp_left_le_of_le (T : I) {a b : I} (hab : a ≤ b) :
    (σ T : ℝ) * ↑a + ↑T ≤ (σ T : ℝ) * ↑b + ↑T := by
  have hσT : (0 : ℝ) ≤ σ T := (σ T).2.1
  have hab' : (a : ℝ) ≤ b := hab
  nlinarith

section

noncomputable section

lemma half_mem_I : (2⁻¹ : ℝ) ∈ I :=
⟨inv_nonneg.mpr zero_le_two, inv_le_one_of_one_le₀ one_le_two⟩

/-- The midpoint `1/2` of the unit interval. -/
abbrev halfI : I := ⟨(2⁻¹ : ℝ), half_mem_I⟩

lemma has_T_half {t₀ t₁ : I} (γ : Path t₀ t₁) (ht₀ : ↑t₀ < (2⁻¹ : ℝ)) (ht₁ : ↑t₁ > (2⁻¹ : ℝ)) :
  ∃ (T : I),  0 < T ∧ T < 1 ∧ (γ T) = halfI := by
  have : γ.toFun 0 ≤ halfI := by rw [γ.source']; exact Subtype.coe_le_coe.mp (le_of_lt ht₀)
  have h₀ : ∃ (t : I), γ t ≤ halfI := ⟨0, this⟩
  have : halfI ≤ γ.toFun 1 := by rw [γ.target']; exact Subtype.coe_le_coe.mp (le_of_lt ht₁)
  have h₁ : ∃ (t : I), halfI ≤ γ t := ⟨1, this⟩
  have hy := Set.mem_range.mp (mem_range_of_exists_le_of_exists_ge γ.continuous_toFun h₀ h₁)
  obtain ⟨T, hT⟩ := hy
  use T
  have hT₀ : 0 ≠ T := by
    rintro ⟨rfl⟩
    apply lt_irrefl (t₀ : ℝ)
    calc (t₀ : ℝ)
        _ < 2⁻¹       := ht₀
        _ = (γ 0 : ℝ) := Subtype.coe_inj.mpr hT.symm
        _ = ↑t₀       := Subtype.coe_inj.mpr γ.source'
  have hT₁ : T ≠ 1 := by
    rintro ⟨rfl⟩
    apply lt_irrefl (t₁ : ℝ)
    calc (t₁ : ℝ)
      _ = (γ 1 : ℝ) := Subtype.coe_inj.mpr γ.target'.symm
      _ = halfI    := Subtype.coe_inj.mpr hT
      _ < ↑t₁       := ht₁
  exact ⟨lt_iff_le_and_ne.mpr ⟨T.2.1, hT₀⟩, lt_iff_le_and_ne.mpr ⟨T.2.2, hT₁⟩, hT⟩
end

end

end unitIAux
