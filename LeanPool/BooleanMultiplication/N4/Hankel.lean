/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N3Certificate

/-!
# Four-term Hankel target geometry

This file starts the `n = 4` proof with the coordinate geometry of the seven-dimensional
target of four-term multiplication.  All classifications are expressed as
polynomial identities over `F₂`; no circuit or truth-table enumeration is used.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Coefficient vectors for the seven Hankel target directions of `Mul 4`. -/
abbrev TargetCoeff := Fin 7 → F₂

/-- The coefficient vector supported at one target coordinate. -/
@[expose] def targetBasis (s : Fin 7) : TargetCoeff :=
  (Pi.basisFun F₂ (Fin 7)) s

/-- The rational place at zero. -/
@[expose] def rZeroCoeff : TargetCoeff := ![1, 0, 0, 0, 0, 0, 0]

/-- The rational place at one. -/
@[expose] def rOneCoeff : TargetCoeff := ![1, 1, 1, 1, 1, 1, 1]

/-- The rational place at infinity. -/
@[expose] def rInfinityCoeff : TargetCoeff := ![0, 0, 0, 0, 0, 0, 1]

/-- The three-dimensional space spanned by the rational places. -/
@[expose] def rationalCoeffSpace : Submodule F₂ TargetCoeff :=
  Submodule.span F₂ {rZeroCoeff, rOneCoeff, rInfinityCoeff}

/-- Interpret a target coefficient vector as an ANF in the `Mul 4` target. -/
@[expose] def targetANF (c : TargetCoeff) : ANF 8 :=
  ∑ s : Fin 7, c s • Mul 4 s

/-- The `4 × 4` Hankel matrix attached to a target coefficient vector. -/
@[expose] def hankelMatrix (c : TargetCoeff) : Matrix (Fin 4) (Fin 4) F₂ :=
  fun i j => c ⟨i.val + j.val, by omega⟩

/-- Algebraic rank-at-most-one condition: every `2 × 2` minor vanishes. -/
@[expose] def HankelRankLEOne (c : TargetCoeff) : Prop :=
  ∀ i k j l : Fin 4,
    hankelMatrix c i j * hankelMatrix c k l =
      hankelMatrix c i l * hankelMatrix c k j

theorem targetBasis_apply (s t : Fin 7) :
    targetBasis s t = if s = t then 1 else 0 := by
  classical
  by_cases h : s = t
  · subst t
    simp [targetBasis, Pi.basisFun]
  · simp [targetBasis, Pi.basisFun, h]

@[simp] theorem rZeroCoeff_apply (i : Fin 7) :
    rZeroCoeff i = if i = 0 then 1 else 0 := by
  fin_cases i <;> simp [rZeroCoeff]

@[simp] theorem rInfinityCoeff_apply (i : Fin 7) :
    rInfinityCoeff i = if i = 6 then 1 else 0 := by
  fin_cases i <;> simp [rInfinityCoeff]

@[simp] theorem rOneCoeff_apply (i : Fin 7) : rOneCoeff i = 1 := by
  fin_cases i <;> rfl

private theorem rankOne_minor {c : TargetCoeff} (h : HankelRankLEOne c)
    (i k j l : Fin 4) :
    c ⟨i.val + j.val, by omega⟩ * c ⟨k.val + l.val, by omega⟩ =
      c ⟨i.val + l.val, by omega⟩ * c ⟨k.val + j.val, by omega⟩ := by
  simpa [HankelRankLEOne, hankelMatrix] using h i k j l

/-- The nonzero rank-one Hankel coefficient vectors are precisely the three
`F₂`-rational places.  The proof follows the manuscript's recurrence argument
and uses only vanishing minors and field algebra. -/
theorem rankOne_target_classification {c : TargetCoeff}
    (h : HankelRankLEOne c) (hc : c ≠ 0) :
    c = rZeroCoeff ∨ c = rOneCoeff ∨ c = rInfinityCoeff := by
  rcases f2_eq_zero_or_one (c 0) with hc0 | hc0
  · have hc1 : c 1 = 0 := by
      have hm := rankOne_minor h (0 : Fin 4) 1 1 0
      simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod, zero_add,
        Fin.mk_one, add_zero, N3Certificate.mul_self_f2, Fin.zero_eta, hc0, Nat.reduceAdd,
        Fin.reduceFinMk, zero_mul] at hm
      exact hm
    have hc2 : c 2 = 0 := by
      have hm := rankOne_minor h (0 : Fin 4) 2 2 0
      simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.reduceMod, zero_add,
        Fin.reduceFinMk, add_zero, N3Certificate.mul_self_f2, Fin.zero_eta, hc0,
        Nat.reduceAdd, zero_mul] at hm
      exact hm
    have hc3 : c 3 = 0 := by
      have hm := rankOne_minor h (0 : Fin 4) 3 3 0
      simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.mod_succ, zero_add,
        Fin.reduceFinMk, add_zero, N3Certificate.mul_self_f2, Fin.zero_eta, hc0,
        Nat.reduceAdd, zero_mul] at hm
      exact hm
    have hc4 : c 4 = 0 := by
      have hm := rankOne_minor h (1 : Fin 4) 3 3 1
      simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.mod_succ, Nat.reduceAdd,
        Fin.reduceFinMk, N3Certificate.mul_self_f2, hc2, zero_mul] at hm
      exact hm
    have hc5 : c 5 = 0 := by
      have hm := rankOne_minor h (2 : Fin 4) 3 3 2
      simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.mod_succ,
        Nat.reduceAdd, Fin.reduceFinMk, N3Certificate.mul_self_f2, hc4, zero_mul] at hm
      exact hm
    have hc6 : c 6 = 1 := by
      rcases f2_eq_zero_or_one (c 6) with hc6 | hc6
      · apply False.elim
        apply hc
        funext i
        fin_cases i <;> assumption
      · exact hc6
    exact Or.inr (Or.inr (by
      funext i
      fin_cases i <;> simp [rInfinityCoeff, hc0, hc1, hc2, hc3, hc4, hc5, hc6]))
  · have hc2 : c 2 = c 1 := by
      have hm := rankOne_minor h (0 : Fin 4) 1 0 1
      simpa [hc0, N3Certificate.mul_self_f2] using hm
    have hc3 : c 3 = c 1 := by
      have hm := rankOne_minor h (0 : Fin 4) 1 0 2
      simpa [hc0, hc2, N3Certificate.mul_self_f2] using hm
    have hc4 : c 4 = c 1 := by
      have hm := rankOne_minor h (0 : Fin 4) 2 0 2
      simpa [hc0, hc2, N3Certificate.mul_self_f2] using hm
    have hc5 : c 5 = c 1 := by
      have hm := rankOne_minor h (0 : Fin 4) 2 0 3
      simpa [hc0, hc2, hc3, N3Certificate.mul_self_f2] using hm
    have hc6 : c 6 = c 1 := by
      have hm := rankOne_minor h (0 : Fin 4) 3 0 3
      simpa [hc0, hc3, N3Certificate.mul_self_f2] using hm
    rcases f2_eq_zero_or_one (c 1) with hc1 | hc1
    · exact Or.inl (by
        funext i
        fin_cases i <;> simp [rZeroCoeff, hc0, hc1, hc2, hc3, hc4, hc5, hc6])
    · exact Or.inr (Or.inl (by
        funext i
        fin_cases i <;> simp [rOneCoeff, hc0, hc1, hc2, hc3, hc4, hc5, hc6]))

@[simp] theorem rankOne_rZero : HankelRankLEOne rZeroCoeff := by
  intro i k j l
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    decide

@[simp] theorem rankOne_rOne : HankelRankLEOne rOneCoeff := by
  intro i k j l
  simp [hankelMatrix]

@[simp] theorem rankOne_rInfinity : HankelRankLEOne rInfinityCoeff := by
  intro i k j l
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    decide

end

end N4
end UnrestrictedBooleanMul
