/-
Copyright (c) 2026 Command Master. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Command Master
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import LeanPool.LeanBourgain.Additive.Constants

/-!
# Quantitative constants for incidence and sum-product estimates

Defines numeric constants `sgC₅`, `sgC₄`, ..., `stC`, and the epsilon
schedules `SG_eps_i` and `ST_prime_field_eps_i` that parameterize the
Szemerédi-Trotter and sum-product steps of the Bourgain extractor proof,
along with the structural inequalities used to compare them.
-/

namespace LeanPool.LeanBourgain

/-- `sgC₅ = 2 ^ 49`. -/
def sgC₅ : NNReal := 2 ^ 49

/-- `sgC₄ = 4 + 16 * (sgC₅ + 2)`. -/
noncomputable def sgC₄ : NNReal := 4 + 16 * (sgC₅ + 2)

/-- `sgC₃ = 4 * sqrt (sgC₄ + 1)`. -/
noncomputable def sgC₃ : NNReal := 4 * NNReal.sqrt (sgC₄ + 1)

/-- `sgC₂ = sgC₃ + 16`. -/
noncomputable def sgC₂ : NNReal := sgC₃ + 16

/-- `sgC = sgC₂ + 1`. -/
noncomputable def sgC : NNReal := sgC₂ + 1

/-- `stC₄ = sgC + 2`. -/
noncomputable def stC₄ : NNReal := sgC + 2

/-- `stC₃ = (stC₄ + 73) ^ (1/4)`. -/
noncomputable def stC₃ : NNReal := (stC₄ + 73 : NNReal) ^ (1 / 4 : ℝ)

/-- `stC₂ = sqrt (2 * (stC₃ + sqrt 2 / 4))`. -/
noncomputable def stC₂ : NNReal := NNReal.sqrt (2 * (stC₃ + NNReal.sqrt 2 / 4))

/-- `stC = stC₂ + 1`. -/
noncomputable def stC : NNReal := stC₂ + 1

/-- Innermost epsilon constant for the sum-product schedule. -/
noncomputable def sgEps₃ (α : ℝ) : ℝ :=
  min (min (11 / 439) (15 / 136 * α)) ((α / 4) / (fullC (α / 4) * 9212 / 45))

/-- Middle epsilon constant for the sum-product schedule. -/
noncomputable def sgEps₂ (α : ℝ) : ℝ := 2 / 3 * (sgEps₃ α)

/-- Outermost epsilon constant for the sum-product schedule. -/
noncomputable def sgEps (α : ℝ) : ℝ := 13 / 30 * (sgEps₂ α)

/-- Innermost epsilon constant for the prime-field Szemerédi-Trotter schedule. -/
noncomputable def stPrimeFieldEps₃ (α : ℝ) : ℝ := 12 / 13 * (sgEps α)

/-- Middle epsilon constant for the prime-field Szemerédi-Trotter schedule. -/
noncomputable def stPrimeFieldEps₂ (α : ℝ) : ℝ := (stPrimeFieldEps₃ α) / 4

/-- Outermost epsilon constant for the prime-field Szemerédi-Trotter schedule. -/
noncomputable def stPrimeFieldEps (α : ℝ) : ℝ := (stPrimeFieldEps₂ α) / 3

lemma ntlSGeps (β : ℝ) : sgEps₃ β < 45 / 1756 :=
  calc sgEps₃ β
    _ ≤ 11 / 439 := by unfold sgEps₃; simp
    _ < 45 / 1756 := by norm_num

lemma ntlSGeps' (β : ℝ) : sgEps₃ β ≤ 15 / 136 * β := by
  unfold sgEps₃
  simp

theorem full_C_neq_zero (x : ℝ) : fullC x ≠ 0 := by
  unfold fullC fullC₂
  simp

lemma pos_SGeps₃ (β : ℝ) (h : 0 < β) :
    0 < sgEps₃ β := by
  unfold sgEps₃
  have hne : (fullC (β / 4) : ℝ) ≠ 0 := by exact_mod_cast full_C_neq_zero (β / 4)
  have hpos : (0 : ℝ) < fullC (β / 4) := by
    have := full_C_neq_zero (β / 4)
    positivity
  refine lt_min ?_ ?_
  · refine lt_min (by norm_num) ?_
    positivity
  · positivity

lemma pos_ST_prime_field_eps (α : ℝ) (h : 0 < α) : 0 < stPrimeFieldEps α := by
  unfold stPrimeFieldEps stPrimeFieldEps₂ stPrimeFieldEps₃ sgEps sgEps₂
  simp [pos_SGeps₃ α h]

lemma one_le_SG_C₃ : 1 ≤ sgC₃ := calc
  1 = NNReal.sqrt 1 := by simp
  _ ≤ NNReal.sqrt (sgC₄ + 1) := by simp
  _ ≤ 4 * NNReal.sqrt (sgC₄ + 1) := by simp
  _ = sgC₃ := rfl

lemma SG_C₃_pos : 0 < sgC₃ := calc
  0 < 1 := zero_lt_one
  _ ≤ sgC₃ := one_le_SG_C₃

lemma one_le_ST_C₃ : 1 ≤ stC₃ := calc
  1 ≤ (1 : NNReal) ^ (1 / 4 : ℝ) := by simp
  _ ≤ (stC₄ + 73 : NNReal) ^ (1 / 4 : ℝ) := by
        gcongr
        have : stC₄ + 73 = 1 + (stC₄ + 72) := by ring
        rw [this]
        simp
  _ = stC₃ := rfl

lemma ST_C₃_pos : 0 < stC₃ := calc
  0 < 1 := zero_lt_one
  _ ≤ stC₃ := one_le_ST_C₃

lemma ST_C_pos : 0 < stC := calc
  0 < 1 := zero_lt_one
  _ ≤ 1 + stC₂ := by simp
  _ = stC := add_comm ..

lemma lemma1 (β : ℝ) :
    1 / 2 + 2 * stPrimeFieldEps β ≤ 1 - 4 * stPrimeFieldEps₂ β := by
  unfold stPrimeFieldEps stPrimeFieldEps₂ stPrimeFieldEps₃ sgEps sgEps₂
  have := ntlSGeps β
  linarith

lemma lemma2 (β : ℝ) :
    4 * stPrimeFieldEps₂ β ≤ 1 := by
  unfold stPrimeFieldEps₂ stPrimeFieldEps₃ sgEps sgEps₂
  have := ntlSGeps β
  linarith

lemma lemma3 (β : ℝ) :
    stPrimeFieldEps₂ β + 6 * stPrimeFieldEps β ≤ 1 - 4 * stPrimeFieldEps₂ β := by
  unfold stPrimeFieldEps stPrimeFieldEps₂ stPrimeFieldEps₃ sgEps sgEps₂
  have := ntlSGeps β
  linarith

lemma lemma4 (β : ℝ) :
    1 ≤ 3 / 2 - sgEps β := by
  unfold sgEps sgEps₂
  have := ntlSGeps β
  linarith

lemma lemma5 (β : ℝ) :
    1 + (2⁻¹ - sgEps β) ≠ 0 := by
  have := lemma4 β
  ring_nf
  linarith

lemma lemma6 (β : ℝ) :
    1 + 4 * stPrimeFieldEps β ≤ 3 / 2 - sgEps β := by
  unfold stPrimeFieldEps stPrimeFieldEps₂ stPrimeFieldEps₃ sgEps sgEps₂
  have := ntlSGeps β
  linarith

lemma lemma7 (β : ℝ) :
    1 / 2 + sgEps β ≤ 1 + (-(sgEps β * 2) - stPrimeFieldEps β * 4) := by
  unfold stPrimeFieldEps stPrimeFieldEps₂ stPrimeFieldEps₃ sgEps sgEps₂
  have := ntlSGeps β
  linarith

lemma lemma8 (β : ℝ) :
    0 ≤ 1 / 2 - sgEps₂ β - sgEps β - 4 * stPrimeFieldEps β := by
  unfold stPrimeFieldEps stPrimeFieldEps₂ stPrimeFieldEps₃ sgEps sgEps₂
  have := ntlSGeps β
  linarith

lemma lemma9 (β : ℝ) (h : 0 < β) :
    0 ≤ stPrimeFieldEps β := by
  unfold stPrimeFieldEps stPrimeFieldEps₂ stPrimeFieldEps₃ sgEps sgEps₂
  have := pos_SGeps₃ β h
  linarith

lemma lemma10 (β : ℝ) (h : 0 < β) :
    0 ≤ sgEps₃ β :=
  le_of_lt <| pos_SGeps₃ β h

lemma lemma11 (β : ℝ) (h : 0 < β) :
    β / 4 < β / 2 - 439 / 45 * β * sgEps₃ β := by
  have := ntlSGeps β
  have hbeta : β * (1 / 4) < β * (1 / 2 - 439 / 45 * sgEps₃ β) := by
    apply mul_lt_mul_of_pos_left _ h
    linarith
  linarith

lemma lemma12 (β : ℝ) (h : 0 < β) :
    0 < β / 2 - 439 / 45 * β * sgEps₃ β := calc
  0 < β / 4 := by simp [h]
  _ < β / 2 - 439 / 45 * β * sgEps₃ β := lemma11 β h

lemma lemma13 (β : ℝ) :
    stPrimeFieldEps β * 6 + sgEps₂ β + sgEps β ≤ 1 / 2 - 439 / 45 * sgEps₃ β := by
  unfold stPrimeFieldEps stPrimeFieldEps₂ stPrimeFieldEps₃ sgEps sgEps₂
  have := ntlSGeps β
  linarith

lemma lemma14 (β : ℝ) :
    0 ≤ 1 / 2 - 439 / 45 * sgEps₃ β := by
  have := ntlSGeps β
  linarith

lemma lemma15 (β : ℝ) (h : 0 < β) :
    0 ≤ 1 / 2 + 8 * stPrimeFieldEps β + sgEps₂ β + sgEps β := by
  unfold stPrimeFieldEps stPrimeFieldEps₂ stPrimeFieldEps₃ sgEps sgEps₂
  have := pos_SGeps₃ β h
  linarith

lemma lemma16 (β : ℝ) :
    0 ≤ 1 / 2 - 113 / 30 * sgEps₃ β := by
  have := ntlSGeps β
  linarith

/-- The master quantitative estimate combining the constants and epsilon
schedules: the bound driving the sum-product iteration is strictly below
`p ^ (…)/ 2` for every prime `p` and admissible doubling parameter `β`. -/
theorem final_theorem (β : ℝ) (h : 0 < β) (n : ℕ+) (p : ℕ) [instpprime : Fact p.Prime]
    (h₁ : n ≤ (p ^ (2 - β) : ℝ))
    (h₂ : sgC₅ * (1 / 4) ≤ n ^ (stPrimeFieldEps β * 6 + sgEps₂ β + sgEps β)) :
    (2 ^ 110 * (256 * n ^ (8 * stPrimeFieldEps β + 2 * sgEps₃ β)) ^ 42) ^
      fullC (β / 2 - 439 / 45 * β * sgEps₃ β) <
    (p ^ min (β / 2 - 17 / 15 * (2 - β) * sgEps₃ β) (β / 2 - 113 / 30 * β * sgEps₃ β) : ℝ) / 2 :=
  calc
    ((2 ^ 110 * (256 * n ^ (8 * stPrimeFieldEps β + 2 * sgEps₃ β)) ^ 42) ^
        fullC (β / 2 - 439 / 45 * β * sgEps₃ β) : ℝ) =
        (2 ^ 110 * 256 ^ 42 * (n ^ (8 * stPrimeFieldEps β + 2 * sgEps₃ β)) ^ 42) ^
        fullC (β / 2 - 439 / 45 * β * sgEps₃ β) := by
      rw [mul_pow (256 : ℝ), ← mul_assoc]
    _ = (2 ^ 110 * 256 ^ 42 * n ^ (1372 / 15 * sgEps₃ β)) ^
        fullC (β / 2 - 439 / 45 * β * sgEps₃ β) := by
      have hexp : (8 * stPrimeFieldEps β + 2 * sgEps₃ β) * (42 : ℕ) =
          1372 / 15 * sgEps₃ β := by
        unfold stPrimeFieldEps stPrimeFieldEps₂ stPrimeFieldEps₃ sgEps sgEps₂
        push_cast
        ring
      rw [← Real.rpow_mul_natCast (by positivity), hexp]
    _ = (2 * (2 ^ 110 * 256 ^ 42) * n ^ (1372 / 15 * sgEps₃ β) / 2) ^
        fullC (β / 2 - 439 / 45 * β * sgEps₃ β) := by
      ring_nf
    _ = (2 * (2 ^ 110 * 256 ^ 42) * n ^ (1372 / 15 * sgEps₃ β)) ^
          fullC (β / 2 - 439 / 45 * β * sgEps₃ β) /
        2 ^ fullC (β / 2 - 439 / 45 * β * sgEps₃ β) := by
      rw [div_pow]
    _ ≤ (2 * (2 ^ 110 * 256 ^ 42) * n ^ (1372 / 15 * sgEps₃ β)) ^
        fullC (β / 2 - 439 / 45 * β * sgEps₃ β) / 2 := by
      gcongr
      apply le_self_pow₀
      · norm_num
      · apply full_C_neq_zero
    _ ≤ ((sgC₅ * (1 / 4)) ^ 10 * n ^ (1372 / 15 * sgEps₃ β)) ^
        fullC (β / 2 - 439 / 45 * β * sgEps₃ β) / 2 := by
      gcongr
      unfold sgC₅
      norm_num
    _ ≤ ((n ^ (stPrimeFieldEps β * 6 + sgEps₂ β + sgEps β)) ^ 10 *
          n ^ (1372 / 15 * sgEps₃ β)) ^
        fullC (β / 2 - 439 / 45 * β * sgEps₃ β) / 2 := by
      gcongr
      exact h₂
    _ = (n ^ (4606 / 45 * sgEps₃ β)) ^
        fullC (β / 2 - 439 / 45 * β * sgEps₃ β) / 2 := by
      have hexp : (stPrimeFieldEps β * 6 + sgEps₂ β + sgEps β) * (10 : ℕ) +
          1372 / 15 * sgEps₃ β = 4606 / 45 * sgEps₃ β := by
        unfold stPrimeFieldEps stPrimeFieldEps₂ stPrimeFieldEps₃ sgEps sgEps₂
        push_cast
        ring
      rw [← Real.rpow_mul_natCast (by positivity), ← Real.rpow_add (by positivity), hexp]
    _ ≤ (n ^ (4606 / 45 * sgEps₃ β)) ^
        fullC (β / 4) / 2 := by
      have hbase : (1 : ℝ) ≤ (n : ℝ) ^ (4606 / 45 * sgEps₃ β) := by
        apply Real.one_le_rpow
        · norm_cast
          simp
        · have := lemma10 β h
          linarith
      have harg : (1 : ℝ) / (β / 2 - 439 / 45 * β * sgEps₃ β) ≤ 1 / (β / 4) := by
        apply one_div_le_one_div_of_le (by linarith)
        exact le_of_lt <| lemma11 β h
      unfold fullC fullC₂
      gcongr
      · norm_num
      · norm_num
      · have := lemma12 β h
        positivity
    _ ≤ ((p ^ (2 - β)) ^ (4606 / 45 * sgEps₃ β)) ^
        fullC (β / 4) / 2 := by
      gcongr
      simp [lemma10 β h]
    _ ≤ ((p ^ 2) ^ (4606 / 45 * sgEps₃ β)) ^
        fullC (β / 4) / 2 := by
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
    _ = p ^ (fullC (β / 4) * 9212 / 45 * sgEps₃ β) / 2 := by
      rw [← Real.rpow_natCast_mul (by positivity), ← Real.rpow_mul_natCast (by positivity)]
      congr 2
      push_cast
      ring
    _ ≤ p ^ (fullC (β / 4) * 9212 / 45 * (β * 45 / (4 * (fullC (β / 4) * 9212)))) / 2 := by
      gcongr
      · exact_mod_cast instpprime.out.one_le
      · unfold sgEps₃
        refine (min_le_right _ _).trans (le_of_eq ?_)
        ring
    _ = p ^ (β / 4) / 2 := by
      congr 2
      unfold fullC fullC₂
      field_simp
    _ < (p ^ min (β / 2 - 17 / 15 * (2 - β) * sgEps₃ β)
          (β / 2 - 113 / 30 * β * sgEps₃ β) : ℝ) / 2 := by
      gcongr
      apply Real.rpow_lt_rpow_of_exponent_lt
      · have := instpprime.out.two_le
        norm_cast
      · simp only [lt_min_iff]
        refine ⟨?_, ?_⟩
        · suffices 17 / 15 * (2 - β) * sgEps₃ β < β / 4 by linarith
          calc
            17 / 15 * (2 - β) * sgEps₃ β < 17 / 15 * (2 - 0) * sgEps₃ β := by
                gcongr
                exact pos_SGeps₃ β h
            _ = 34 / 15 * sgEps₃ β := by ring_nf
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
