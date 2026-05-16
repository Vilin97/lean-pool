/-
Copyright (c) 2026 Command Master. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Command Master
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import LeanPool.LeanBourgain.Additive.Constants

/-!
# Quantitative constants for incidence and sum-product estimates

Defines numeric constants `SG_C₅`, `SG_C₄`, ..., `ST_C`, and the epsilon
schedules `SG_eps_i` and `ST_prime_field_eps_i` that parameterize the
Szemerédi-Trotter and sum-product steps of the Bourgain extractor proof,
along with the structural inequalities used to compare them.
-/

namespace LeanPool.LeanBourgain

/-- `SG_C₅ = 2 ^ 49`. -/
def SG_C₅ : NNReal := 2 ^ 49

/-- `SG_C₄ = 4 + 16 * (SG_C₅ + 2)`. -/
noncomputable def SG_C₄ : NNReal := 4 + 16 * (SG_C₅ + 2)

/-- `SG_C₃ = 4 * sqrt (SG_C₄ + 1)`. -/
noncomputable def SG_C₃ : NNReal := 4 * NNReal.sqrt (SG_C₄ + 1)

/-- `SG_C₂ = SG_C₃ + 16`. -/
noncomputable def SG_C₂ : NNReal := SG_C₃ + 16

/-- `SG_C = SG_C₂ + 1`. -/
noncomputable def SG_C : NNReal := SG_C₂ + 1

/-- `ST_C₄ = SG_C + 2`. -/
noncomputable def ST_C₄ : NNReal := SG_C + 2

/-- `ST_C₃ = (ST_C₄ + 73) ^ (1/4)`. -/
noncomputable def ST_C₃ : NNReal := (ST_C₄ + 73 : NNReal) ^ (1 / 4 : ℝ)

/-- `ST_C₂ = sqrt (2 * (ST_C₃ + sqrt 2 / 4))`. -/
noncomputable def ST_C₂ : NNReal := NNReal.sqrt (2 * (ST_C₃ + NNReal.sqrt 2 / 4))

/-- `ST_C = ST_C₂ + 1`. -/
noncomputable def ST_C : NNReal := ST_C₂ + 1

/-- Innermost epsilon constant for the sum-product schedule. -/
noncomputable def SG_eps₃ (α : ℝ) : ℝ :=
  min (min (11 / 439) (15 / 136 * α)) ((α / 4) / (full_C (α / 4) * 9212 / 45))

/-- Middle epsilon constant for the sum-product schedule. -/
noncomputable def SG_eps₂ (α : ℝ) : ℝ := 2 / 3 * (SG_eps₃ α)

/-- Outermost epsilon constant for the sum-product schedule. -/
noncomputable def SG_eps (α : ℝ) : ℝ := 13 / 30 * (SG_eps₂ α)

/-- Innermost epsilon constant for the prime-field Szemerédi-Trotter schedule. -/
noncomputable def ST_prime_field_eps₃ (α : ℝ) : ℝ := 12 / 13 * (SG_eps α)

/-- Middle epsilon constant for the prime-field Szemerédi-Trotter schedule. -/
noncomputable def ST_prime_field_eps₂ (α : ℝ) : ℝ := (ST_prime_field_eps₃ α) / 4

/-- Outermost epsilon constant for the prime-field Szemerédi-Trotter schedule. -/
noncomputable def ST_prime_field_eps (α : ℝ) : ℝ := (ST_prime_field_eps₂ α) / 3

lemma ntlSGeps (β : ℝ) : SG_eps₃ β < 45 / 1756 :=
  calc SG_eps₃ β
    _ ≤ 11 / 439 := by unfold SG_eps₃; simp
    _ < 45 / 1756 := by norm_num

lemma ntlSGeps' (β : ℝ) : SG_eps₃ β ≤ 15 / 136 * β := by
  unfold SG_eps₃
  simp

theorem full_C_neq_zero (x : ℝ) : full_C x ≠ 0 := by
  unfold full_C full_C₂
  simp

lemma pos_SGeps₃ (β : ℝ) (h : 0 < β) :
    0 < SG_eps₃ β := by
  unfold SG_eps₃
  have hne : (full_C (β / 4) : ℝ) ≠ 0 := by exact_mod_cast full_C_neq_zero (β / 4)
  have hpos : (0 : ℝ) < full_C (β / 4) := by
    have := full_C_neq_zero (β / 4)
    positivity
  refine lt_min ?_ ?_
  · refine lt_min (by norm_num) ?_
    positivity
  · positivity

lemma pos_ST_prime_field_eps (α : ℝ) (h : 0 < α) : 0 < ST_prime_field_eps α := by
  unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
  simp [pos_SGeps₃ α h]

lemma one_le_SG_C₃ : 1 ≤ SG_C₃ := calc
  1 = NNReal.sqrt 1 := by simp
  _ ≤ NNReal.sqrt (SG_C₄ + 1) := by simp
  _ ≤ 4 * NNReal.sqrt (SG_C₄ + 1) := by simp
  _ = SG_C₃ := rfl

lemma SG_C₃_pos : 0 < SG_C₃ := calc
  0 < 1 := zero_lt_one
  _ ≤ SG_C₃ := one_le_SG_C₃

lemma one_le_ST_C₃ : 1 ≤ ST_C₃ := calc
  1 ≤ (1 : NNReal) ^ (1 / 4 : ℝ) := by simp
  _ ≤ (ST_C₄ + 73 : NNReal) ^ (1 / 4 : ℝ) := by
        gcongr
        have : ST_C₄ + 73 = 1 + (ST_C₄ + 72) := by ring
        rw [this]
        simp
  _ = ST_C₃ := rfl

lemma ST_C₃_pos : 0 < ST_C₃ := calc
  0 < 1 := zero_lt_one
  _ ≤ ST_C₃ := one_le_ST_C₃

lemma ST_C_pos : 0 < ST_C := calc
  0 < 1 := zero_lt_one
  _ ≤ 1 + ST_C₂ := by simp
  _ = ST_C := add_comm ..

lemma lemma1 (β : ℝ) :
    1 / 2 + 2 * ST_prime_field_eps β ≤ 1 - 4 * ST_prime_field_eps₂ β := by
  unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma2 (β : ℝ) :
    4 * ST_prime_field_eps₂ β ≤ 1 := by
  unfold ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma3 (β : ℝ) :
    ST_prime_field_eps₂ β + 6 * ST_prime_field_eps β ≤ 1 - 4 * ST_prime_field_eps₂ β := by
  unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma4 (β : ℝ) :
    1 ≤ 3 / 2 - SG_eps β := by
  unfold SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma5 (β : ℝ) :
    1 + (2⁻¹ - SG_eps β) ≠ 0 := by
  have := lemma4 β
  ring_nf
  linarith

lemma lemma6 (β : ℝ) :
    1 + 4 * ST_prime_field_eps β ≤ 3 / 2 - SG_eps β := by
  unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma7 (β : ℝ) :
    1 / 2 + SG_eps β ≤ 1 + (-(SG_eps β * 2) - ST_prime_field_eps β * 4) := by
  unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma8 (β : ℝ) :
    0 ≤ 1 / 2 - SG_eps₂ β - SG_eps β - 4 * ST_prime_field_eps β := by
  unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma9 (β : ℝ) (h : 0 < β) :
    0 ≤ ST_prime_field_eps β := by
  unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
  have := pos_SGeps₃ β h
  linarith

lemma lemma10 (β : ℝ) (h : 0 < β) :
    0 ≤ SG_eps₃ β :=
  le_of_lt <| pos_SGeps₃ β h

lemma lemma11 (β : ℝ) (h : 0 < β) :
    β / 4 < β / 2 - 439 / 45 * β * SG_eps₃ β := by
  have := ntlSGeps β
  have hbeta : β * (1 / 4) < β * (1 / 2 - 439 / 45 * SG_eps₃ β) := by
    apply mul_lt_mul_of_pos_left _ h
    linarith
  linarith

lemma lemma12 (β : ℝ) (h : 0 < β) :
    0 < β / 2 - 439 / 45 * β * SG_eps₃ β := calc
  0 < β / 4 := by simp [h]
  _ < β / 2 - 439 / 45 * β * SG_eps₃ β := lemma11 β h

lemma lemma13 (β : ℝ) :
    ST_prime_field_eps β * 6 + SG_eps₂ β + SG_eps β ≤ 1 / 2 - 439 / 45 * SG_eps₃ β := by
  unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
  have := ntlSGeps β
  linarith

lemma lemma14 (β : ℝ) :
    0 ≤ 1 / 2 - 439 / 45 * SG_eps₃ β := by
  have := ntlSGeps β
  linarith

lemma lemma15 (β : ℝ) (h : 0 < β) :
    0 ≤ 1 / 2 + 8 * ST_prime_field_eps β + SG_eps₂ β + SG_eps β := by
  unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
  have := pos_SGeps₃ β h
  linarith

lemma lemma16 (β : ℝ) :
    0 ≤ 1 / 2 - 113 / 30 * SG_eps₃ β := by
  have := ntlSGeps β
  linarith

end LeanPool.LeanBourgain
