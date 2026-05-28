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

/-- The master quantitative estimate combining the constants and epsilon
schedules: the bound driving the sum-product iteration is strictly below
`p ^ (…)/ 2` for every prime `p` and admissible doubling parameter `β`. -/
theorem final_theorem (β : ℝ) (h : 0 < β) (n : ℕ+) (p : ℕ) [instpprime : Fact p.Prime]
    (h₁ : n ≤ (p ^ (2 - β) : ℝ))
    (h₂ : SG_C₅ * (1 / 4) ≤ n ^ (ST_prime_field_eps β * 6 + SG_eps₂ β + SG_eps β)) :
    (2 ^ 110 * (256 * n ^ (8 * ST_prime_field_eps β + 2 * SG_eps₃ β)) ^ 42) ^
      full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) <
    (p ^ min (β / 2 - 17 / 15 * (2 - β) * SG_eps₃ β) (β / 2 - 113 / 30 * β * SG_eps₃ β) : ℝ) / 2 :=
  calc
    ((2 ^ 110 * (256 * n ^ (8 * ST_prime_field_eps β + 2 * SG_eps₃ β)) ^ 42) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) : ℝ) =
        (2 ^ 110 * 256 ^ 42 * (n ^ (8 * ST_prime_field_eps β + 2 * SG_eps₃ β)) ^ 42) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) := by
      rw [mul_pow (256 : ℝ), ← mul_assoc]
    _ = (2 ^ 110 * 256 ^ 42 * n ^ (1372 / 15 * SG_eps₃ β)) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) := by
      have hexp : (8 * ST_prime_field_eps β + 2 * SG_eps₃ β) * (42 : ℕ) =
          1372 / 15 * SG_eps₃ β := by
        unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
        push_cast
        ring
      rw [← Real.rpow_mul_natCast (by positivity), hexp]
    _ = (2 * (2 ^ 110 * 256 ^ 42) * n ^ (1372 / 15 * SG_eps₃ β) / 2) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) := by
      ring_nf
    _ = (2 * (2 ^ 110 * 256 ^ 42) * n ^ (1372 / 15 * SG_eps₃ β)) ^
          full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) /
        2 ^ full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) := by
      rw [div_pow]
    _ ≤ (2 * (2 ^ 110 * 256 ^ 42) * n ^ (1372 / 15 * SG_eps₃ β)) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) / 2 := by
      gcongr
      apply le_self_pow₀
      · norm_num
      · apply full_C_neq_zero
    _ ≤ ((SG_C₅ * (1 / 4)) ^ 10 * n ^ (1372 / 15 * SG_eps₃ β)) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) / 2 := by
      gcongr
      unfold SG_C₅
      norm_num
    _ ≤ ((n ^ (ST_prime_field_eps β * 6 + SG_eps₂ β + SG_eps β)) ^ 10 *
          n ^ (1372 / 15 * SG_eps₃ β)) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) / 2 := by
      gcongr
      exact h₂
    _ = (n ^ (4606 / 45 * SG_eps₃ β)) ^
        full_C (β / 2 - 439 / 45 * β * SG_eps₃ β) / 2 := by
      have hexp : (ST_prime_field_eps β * 6 + SG_eps₂ β + SG_eps β) * (10 : ℕ) +
          1372 / 15 * SG_eps₃ β = 4606 / 45 * SG_eps₃ β := by
        unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ SG_eps SG_eps₂
        push_cast
        ring
      rw [← Real.rpow_mul_natCast (by positivity), ← Real.rpow_add (by positivity), hexp]
    _ ≤ (n ^ (4606 / 45 * SG_eps₃ β)) ^
        full_C (β / 4) / 2 := by
      have hbase : (1 : ℝ) ≤ (n : ℝ) ^ (4606 / 45 * SG_eps₃ β) := by
        apply Real.one_le_rpow
        · norm_cast
          simp
        · have := lemma10 β h
          linarith
      have harg : (1 : ℝ) / (β / 2 - 439 / 45 * β * SG_eps₃ β) ≤ 1 / (β / 4) := by
        apply one_div_le_one_div_of_le (by linarith)
        exact le_of_lt <| lemma11 β h
      unfold full_C full_C₂
      gcongr
      · norm_num
      · norm_num
      · have := lemma12 β h
        positivity
    _ ≤ ((p ^ (2 - β)) ^ (4606 / 45 * SG_eps₃ β)) ^
        full_C (β / 4) / 2 := by
      gcongr
      simp [lemma10 β h]
    _ ≤ ((p ^ 2) ^ (4606 / 45 * SG_eps₃ β)) ^
        full_C (β / 4) / 2 := by
      conv =>
        rhs
        lhs
        lhs
        rw [← Real.rpow_natCast]
      gcongr
      · have := lemma10 β h
        linarith
      · exact_mod_cast instpprime.out.one_le
      · push_cast
        linarith
    _ = p ^ (full_C (β / 4) * 9212 / 45 * SG_eps₃ β) / 2 := by
      rw [← Real.rpow_natCast_mul (by positivity), ← Real.rpow_mul_natCast (by positivity)]
      congr 2
      push_cast
      ring
    _ ≤ p ^ (full_C (β / 4) * 9212 / 45 * (β * 45 / (4 * (full_C (β / 4) * 9212)))) / 2 := by
      gcongr
      · exact_mod_cast instpprime.out.one_le
      · unfold SG_eps₃
        refine (min_le_right _ _).trans (le_of_eq ?_)
        ring
    _ = p ^ (β / 4) / 2 := by
      congr 2
      unfold full_C full_C₂
      field_simp
    _ < (p ^ min (β / 2 - 17 / 15 * (2 - β) * SG_eps₃ β)
          (β / 2 - 113 / 30 * β * SG_eps₃ β) : ℝ) / 2 := by
      gcongr
      apply Real.rpow_lt_rpow_of_exponent_lt
      · have := instpprime.out.two_le
        norm_cast
      · simp only [lt_min_iff]
        refine ⟨?_, ?_⟩
        · suffices 17 / 15 * (2 - β) * SG_eps₃ β < β / 4 by linarith
          calc
            17 / 15 * (2 - β) * SG_eps₃ β < 17 / 15 * (2 - 0) * SG_eps₃ β := by
                gcongr
                exact pos_SGeps₃ β h
            _ = 34 / 15 * SG_eps₃ β := by ring_nf
            _ ≤ 34 / 15 * (15 / 136 * β) := by
                gcongr
                exact ntlSGeps' β
            _ = β / 4 := by ring
        · have := lemma11 β h
          apply this.trans_le
          gcongr _ - ?_ * _ * _
          · exact lemma10 β h
          · norm_num

end LeanPool.LeanBourgain
