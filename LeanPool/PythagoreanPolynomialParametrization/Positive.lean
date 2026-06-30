/-
Copyright (c) 2026 Lazar Milikic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lazar Milikic
-/

import LeanPool.PythagoreanPolynomialParametrization.IntegerValued

/-! # Positive Pythagorean triples and 16-parameter variant

This file contains the positive-triple remark and the unrestricted 16-parameter
substitution obtained from the four-square theorem.
-/

namespace LeanPool.PythagoreanPolynomialParametrization

open MvPolynomial



/-- a_pos = y + (1+w)·z -/
noncomputable def aPosParam : RatPoly 4 := yVar + (C (1 : ℚ) + wVar) * zVar

/-- b_pos = y -/
noncomputable def bPosParam : RatPoly 4 := yVar

/-- c_pos = x + (1-w)²·x -/
noncomputable def cPosParam : RatPoly 4 := xVar + (C (1 : ℚ) - wVar) ^ 2 * xVar

/-- f_pos = c_pos·(a_pos² - b_pos²)/2

In the paper: ((x+(1-w)²x)((y+(1+w)z)²-y²))/2 -/
noncomputable def fPosParam : RatPoly 4 :=
  C (1 / 2 : ℚ) * cPosParam * (aPosParam ^ 2 - bPosParam ^ 2)

/-- g_pos = c_pos·a_pos·b_pos

In the paper: (x+(1-w)²x)(y+(1+w)z)y -/
noncomputable def gPosParam : RatPoly 4 := cPosParam * aPosParam * bPosParam

/-- h_pos = c_pos·(a_pos² + b_pos²)/2

In the paper: ((x+(1-w)²x)((y+(1+w)z)²+y²))/2 -/
noncomputable def hPosParam : RatPoly 4 :=
  C (1 / 2 : ℚ) * cPosParam * (aPosParam ^ 2 + bPosParam ^ 2)

/-- The first coordinate polynomial in the positive parametrization is integer-valued. -/
theorem f_pos_param_intValued : IsIntValued fPosParam := by
  intro v
  let x : ℤ := v (0 : Fin 4)
  let y : ℤ := v (1 : Fin 4)
  let z : ℤ := v (2 : Fin 4)
  let w : ℤ := v (3 : Fin 4)
  let A : ℤ := y + ((1 : ℤ) + w) * z
  let B : ℤ := y
  let Cc : ℤ := x + ((1 : ℤ) - w) ^ 2 * x
  have hpar : PaperParityCondition A B Cc := by
    rcases Int.even_or_odd w with hw | hw
    · left
      rcases hw with ⟨t, ht⟩
      refine ⟨x * (1 - 2 * t + 2 * t ^ 2), ?_⟩
      dsimp [Cc]
      rw [ht]
      ring
    · right
      rcases hw with ⟨t, ht⟩
      refine ⟨z * (t + 1), ?_⟩
      dsimp [A, B]
      rw [ht]
      ring
  rcases (TMap_integral_iff_parity A B Cc).mpr hpar with ⟨fx, gy, hz, hT⟩
  refine ⟨fx, ?_⟩
  have hfcoord : (Cc : ℚ) * ((A : ℚ) ^ 2 - (B : ℚ) ^ 2) / 2 = (fx : ℚ) := by
    simpa [TMap] using congrArg Prod.fst hT
  rw [← hfcoord]
  simp [fPosParam, cPosParam, aPosParam, bPosParam, xVar, yVar, zVar, wVar,
    A, B, Cc]
  ring

/-- The second coordinate polynomial in the positive parametrization is integer-valued. -/
theorem g_pos_param_intValued : IsIntValued gPosParam := by
  intro v
  let x : ℤ := v (0 : Fin 4)
  let y : ℤ := v (1 : Fin 4)
  let z : ℤ := v (2 : Fin 4)
  let w : ℤ := v (3 : Fin 4)
  let A : ℤ := y + ((1 : ℤ) + w) * z
  let B : ℤ := y
  let Cc : ℤ := x + ((1 : ℤ) - w) ^ 2 * x
  refine ⟨Cc * A * B, ?_⟩
  simp [gPosParam, cPosParam, aPosParam, bPosParam, xVar, yVar, zVar, wVar,
    A, B, Cc]
  ring

/-- The third coordinate polynomial in the positive parametrization is integer-valued. -/
theorem h_pos_param_intValued : IsIntValued hPosParam := by
  intro v
  let x : ℤ := v (0 : Fin 4)
  let y : ℤ := v (1 : Fin 4)
  let z : ℤ := v (2 : Fin 4)
  let w : ℤ := v (3 : Fin 4)
  let A : ℤ := y + ((1 : ℤ) + w) * z
  let B : ℤ := y
  let Cc : ℤ := x + ((1 : ℤ) - w) ^ 2 * x
  have hpar : PaperParityCondition A B Cc := by
    rcases Int.even_or_odd w with hw | hw
    · left
      rcases hw with ⟨t, ht⟩
      refine ⟨x * (1 - 2 * t + 2 * t ^ 2), ?_⟩
      dsimp [Cc]
      rw [ht]
      ring
    · right
      rcases hw with ⟨t, ht⟩
      refine ⟨z * (t + 1), ?_⟩
      dsimp [A, B]
      rw [ht]
      ring
  rcases (TMap_integral_iff_parity A B Cc).mpr hpar with ⟨fx, gy, hz, hT⟩
  refine ⟨hz, ?_⟩
  have hhcoord : (Cc : ℚ) * ((A : ℚ) ^ 2 + (B : ℚ) ^ 2) / 2 = (hz : ℚ) := by
    simpa [TMap] using congrArg (fun p : ℚ × ℚ × ℚ => p.2.2) hT
  rw [← hhcoord]
  simp [hPosParam, cPosParam, aPosParam, bPosParam, xVar, yVar, zVar, wVar,
    A, B, Cc]
  ring

/-- Construct a 4-tuple input for polynomial evaluation from individual components. -/
def mkRatPolyInput4 (x' y' z' w' : ℤ) : Fin 4 → ℤ := fun i =>
  if i = 0 then x' else if i = 1 then y' else if i = 2 then z' else w'

/-- Frisch--Vaserstein's positive Pythagorean-triple parametrization, with positive
parameters `x`, `y`, `z` and nonnegative parameter `w`. -/
theorem positive_triples_parametrization :
    IsIntValued fPosParam ∧ IsIntValued gPosParam ∧ IsIntValued hPosParam ∧
    positivePythagoreanTriples =
      {(x, y, z) | ∃ (x' y' z' w' : ℤ),
        0 < x' ∧ 0 < y' ∧ 0 < z' ∧ 0 ≤ w' ∧
        ratPolyEval fPosParam (mkRatPolyInput4 x' y' z' w') = (x : ℚ) ∧
        ratPolyEval gPosParam (mkRatPolyInput4 x' y' z' w') = (y : ℚ) ∧
        ratPolyEval hPosParam (mkRatPolyInput4 x' y' z' w') = (z : ℚ)} := by
  have hPositiveRange (x y z : ℤ) :
      (0 < x ∧ 0 < y ∧ 0 < z ∧ IsPythagoreanTriple x y z) ↔
        ∃ a b c : ℤ, PositiveTParameters a b c ∧
          TMap a b c = ((x : ℚ), (y : ℚ), (z : ℚ)) := by
    constructor
    · rintro ⟨hxpos, hypos, hzpos, hpy⟩
      rcases (pythagorean_iff_mem_TMap_range x y z).mp hpy with ⟨a, b, c, hT⟩
      have hxcoord : (c : ℚ) * ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) / 2 = (x : ℚ) := by
        simpa [TMap] using congrArg Prod.fst hT
      have hycoord : (c : ℚ) * (a : ℚ) * (b : ℚ) = (y : ℚ) := by
        simpa [TMap] using congrArg (fun p : ℚ × ℚ × ℚ => p.2.1) hT
      have hzcoord : (c : ℚ) * ((a : ℚ) ^ 2 + (b : ℚ) ^ 2) / 2 = (z : ℚ) := by
        simpa [TMap] using congrArg (fun p : ℚ × ℚ × ℚ => p.2.2) hT
      have hzqpos : (0 : ℚ) < (z : ℚ) := by exact_mod_cast hzpos
      have hyqpos : (0 : ℚ) < (y : ℚ) := by exact_mod_cast hypos
      have hxqpos : (0 : ℚ) < (x : ℚ) := by exact_mod_cast hxpos
      have hsum_nonneg : (0 : ℚ) ≤ (a : ℚ) ^ 2 + (b : ℚ) ^ 2 := by
        nlinarith [sq_nonneg (a : ℚ), sq_nonneg (b : ℚ)]
      have hczprod_pos : (0 : ℚ) < (c : ℚ) * ((a : ℚ) ^ 2 + (b : ℚ) ^ 2) := by
        nlinarith [hzcoord, hzqpos]
      have hcqpos : (0 : ℚ) < (c : ℚ) :=
        pos_of_mul_pos_right (by simpa [mul_comm] using hczprod_pos) hsum_nonneg
      have hcpos : 0 < c := by exact_mod_cast hcqpos
      have hycoord' : (c : ℚ) * ((a : ℚ) * (b : ℚ)) = (y : ℚ) := by
        simpa [mul_assoc] using hycoord
      have hcabprod_pos : (0 : ℚ) < (c : ℚ) * ((a : ℚ) * (b : ℚ)) := by
        nlinarith [hycoord', hyqpos]
      have habqpos : (0 : ℚ) < (a : ℚ) * (b : ℚ) :=
        pos_of_mul_pos_right hcabprod_pos (le_of_lt hcqpos)
      have habpos : 0 < a * b := by exact_mod_cast habqpos
      have ha_ne : a ≠ 0 := by
        intro ha
        subst a
        norm_num at habpos
      have hb_ne : b ≠ 0 := by
        intro hb
        subst b
        norm_num at habpos
      have hapos : 0 < |a| := abs_pos.mpr ha_ne
      have hbpos : 0 < |b| := abs_pos.mpr hb_ne
      have hcxprod_pos : (0 : ℚ) < (c : ℚ) * ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) := by
        nlinarith [hxcoord, hxqpos]
      have hdiffqpos : (0 : ℚ) < (a : ℚ) ^ 2 - (b : ℚ) ^ 2 :=
        pos_of_mul_pos_right hcxprod_pos (le_of_lt hcqpos)
      have hsq_lt_q : (b : ℚ) ^ 2 < (a : ℚ) ^ 2 := by nlinarith
      have hsq_lt_int : b ^ 2 < a ^ 2 := by exact_mod_cast hsq_lt_q
      have hblta : |b| < |a| := by
        rwa [abs_lt_iff_mul_self_lt, ← pow_two, ← pow_two]
      have hprod_abs_int : |a| * |b| = a * b := by
        rw [← abs_mul, abs_of_nonneg (le_of_lt habpos)]
      have hprod_abs_q : ((|a| : ℤ) : ℚ) * ((|b| : ℤ) : ℚ) = (a : ℚ) * (b : ℚ) := by
        exact_mod_cast hprod_abs_int
      have hprod_abs_q' : |(a : ℚ)| * |(b : ℚ)| = (a : ℚ) * (b : ℚ) := by
        simpa [Int.cast_abs] using hprod_abs_q
      have hTabs : TMap (|a|) (|b|) c = ((x : ℚ), (y : ℚ), (z : ℚ)) := by
        rw [← hT]
        ext
        · simp [TMap, Int.cast_abs]
        · simp only [TMap, Int.cast_abs]
          rw [mul_assoc, hprod_abs_q', ← mul_assoc]
        · simp [TMap, Int.cast_abs]
      have hpar : PaperParityCondition (|a|) (|b|) c := by
        exact (TMap_integral_iff_parity (|a|) (|b|) c).mp ⟨x, y, z, hTabs⟩
      refine ⟨|a|, |b|, c, ?_, hTabs⟩
      exact ⟨hapos, hbpos, hcpos, hblta, hpar⟩
    · rintro ⟨a, b, c, hpos, hT⟩
      rcases hpos with ⟨hapos, hbpos, hcpos, hblta, hpar⟩
      have hxcoord : (c : ℚ) * ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) / 2 = (x : ℚ) := by
        simpa [TMap] using congrArg Prod.fst hT
      have hycoord : (c : ℚ) * (a : ℚ) * (b : ℚ) = (y : ℚ) := by
        simpa [TMap] using congrArg (fun p : ℚ × ℚ × ℚ => p.2.1) hT
      have hzcoord : (c : ℚ) * ((a : ℚ) ^ 2 + (b : ℚ) ^ 2) / 2 = (z : ℚ) := by
        simpa [TMap] using congrArg (fun p : ℚ × ℚ × ℚ => p.2.2) hT
      have hcqpos : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hcpos
      have haqpos : (0 : ℚ) < (a : ℚ) := by exact_mod_cast hapos
      have hbqpos : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hbpos
      have hbaq : (b : ℚ) < (a : ℚ) := by exact_mod_cast hblta
      have hdiffqpos : (0 : ℚ) < (a : ℚ) ^ 2 - (b : ℚ) ^ 2 := by
        nlinarith
      have hxqpos : (0 : ℚ) < (x : ℚ) := by
        rw [← hxcoord]
        positivity
      have hyqpos : (0 : ℚ) < (y : ℚ) := by
        rw [← hycoord]
        positivity
      have hzqpos : (0 : ℚ) < (z : ℚ) := by
        rw [← hzcoord]
        positivity
      have hxpos : 0 < x := by exact_mod_cast hxqpos
      have hypos : 0 < y := by exact_mod_cast hyqpos
      have hzpos : 0 < z := by exact_mod_cast hzqpos
      have hpy : IsPythagoreanTriple x y z := by
        exact (pythagorean_iff_mem_TMap_range x y z).mpr ⟨a, b, c, hT⟩
      exact ⟨hxpos, hypos, hzpos, hpy⟩
  refine ⟨f_pos_param_intValued, g_pos_param_intValued, h_pos_param_intValued, ?_⟩
  ext p
  rcases p with ⟨x, y, z⟩
  simp only [positivePythagoreanTriples, exists_and_left, Set.mem_setOf_eq]
  rw [hPositiveRange x y z]
  constructor
  · rintro ⟨a, b, c, hpos, hT⟩
    rcases (positive_T_parameters_parametrized a b c).mp hpos with
      ⟨x', y', z', w', hxpos, hypos, hzpos, hwnonneg, ha, hb, hc⟩
    refine ⟨x', hxpos, y', hypos, z', hzpos, w', hwnonneg, ?_, ?_, ?_⟩
    · have hxcoord : (c : ℚ) * ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) / 2 = (x : ℚ) := by
        simpa [TMap] using congrArg Prod.fst hT
      rw [← hxcoord]
      rw [ha, hb, hc]
      simp [ratPolyEval, fPosParam, cPosParam, aPosParam, bPosParam, xVar, yVar,
        zVar, wVar, mkRatPolyInput4]
      ring_nf
    · have hycoord : (c : ℚ) * (a : ℚ) * (b : ℚ) = (y : ℚ) := by
        simpa [TMap] using congrArg (fun p : ℚ × ℚ × ℚ => p.2.1) hT
      rw [← hycoord]
      rw [ha, hb, hc]
      simp [ratPolyEval, gPosParam, cPosParam, aPosParam, bPosParam, xVar, yVar,
        zVar, wVar, mkRatPolyInput4]
    · have hzcoord : (c : ℚ) * ((a : ℚ) ^ 2 + (b : ℚ) ^ 2) / 2 = (z : ℚ) := by
        simpa [TMap] using congrArg (fun p : ℚ × ℚ × ℚ => p.2.2) hT
      rw [← hzcoord]
      rw [ha, hb, hc]
      simp [ratPolyEval, hPosParam, cPosParam, aPosParam, bPosParam, xVar, yVar,
        zVar, wVar, mkRatPolyInput4]
      ring_nf
  · rintro ⟨x', hxpos, y', hypos, z', hzpos, w', hwnonneg, hf, hg, hh⟩
    let a : ℤ := y' + ((1 : ℤ) + w') * z'
    let b : ℤ := y'
    let c : ℤ := x' + ((1 : ℤ) - w') ^ 2 * x'
    have hpos : PositiveTParameters a b c := by
      exact (positive_T_parameters_parametrized a b c).mpr
        ⟨x', y', z', w', hxpos, hypos, hzpos, hwnonneg, rfl, rfl, rfl⟩
    have hxcoord : (c : ℚ) * ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) / 2 = (x : ℚ) := by
      rw [← hf]
      simp [ratPolyEval, fPosParam, cPosParam, aPosParam, bPosParam, xVar, yVar,
        zVar, wVar, mkRatPolyInput4, a, b, c]
      ring_nf
    have hycoord : (c : ℚ) * (a : ℚ) * (b : ℚ) = (y : ℚ) := by
      rw [← hg]
      simp [ratPolyEval, gPosParam, cPosParam, aPosParam, bPosParam, xVar, yVar,
        zVar, wVar, mkRatPolyInput4, a, b, c]
    have hzcoord : (c : ℚ) * ((a : ℚ) ^ 2 + (b : ℚ) ^ 2) / 2 = (z : ℚ) := by
      rw [← hh]
      simp [ratPolyEval, hPosParam, cPosParam, aPosParam, bPosParam, xVar, yVar,
        zVar, wVar, mkRatPolyInput4, a, b, c]
      ring_nf
    have hT : TMap a b c = ((x : ℚ), (y : ℚ), (z : ℚ)) := by
      ext
      · simpa [TMap] using hxcoord
      · simpa [TMap] using hycoord
      · simpa [TMap] using hzcoord
    exact ⟨a, b, c, hpos, hT⟩

/-! ## 16-parameter parametrization via four-square theorem -/

/-- xSub = x₁² + x₂² + x₃² + x₄² + 1 -/
noncomputable def xSub : RatPoly 16 :=
  (X 0)^2 + (X 1)^2 + (X 2)^2 + (X 3)^2 + C (1 : ℚ)

/-- ySub = y₁² + y₂² + y₃² + y₄² + 1 -/
noncomputable def ySub : RatPoly 16 :=
  (X 4)^2 + (X 5)^2 + (X 6)^2 + (X 7)^2 + C (1 : ℚ)

/-- zSub = z₁² + z₂² + z₃² + z₄² + 1 -/
noncomputable def zSub : RatPoly 16 :=
  (X 8)^2 + (X 9)^2 + (X 10)^2 + (X 11)^2 + C (1 : ℚ)

/-- wSub = w₁² + w₂² + w₃² + w₄² -/
noncomputable def wSub : RatPoly 16 :=
  (X 12)^2 + (X 13)^2 + (X 14)^2 + (X 15)^2

/-- a_16 = ySub + (1 + wSub) * zSub -/
noncomputable def a16Param : RatPoly 16 := ySub + (C (1 : ℚ) + wSub) * zSub

/-- b_16 = ySub -/
noncomputable def b16Param : RatPoly 16 := ySub

/-- c_16 = xSub + (1 - wSub)² * xSub -/
noncomputable def c16Param : RatPoly 16 := xSub + (C (1 : ℚ) - wSub) ^ 2 * xSub

/-- f_16 = c_16·(a_16² - b_16²)/2

In the paper: ((xSub+(1-wSub)²xSub)((ySub+(1+wSub)zSub)²-ySub²))/2 -/
noncomputable def f16Param : RatPoly 16 :=
  C (1 / 2 : ℚ) * c16Param * (a16Param ^ 2 - b16Param ^ 2)

/-- g_16 = c_16·a_16·b_16

In the paper: (xSub+(1-wSub)²xSub)(ySub+(1+wSub)zSub)ySub -/
noncomputable def g16Param : RatPoly 16 := c16Param * a16Param * b16Param

/-- h_16 = c_16·(a_16² + b_16²)/2

In the paper: ((xSub+(1-wSub)²xSub)((ySub+(1+wSub)zSub)²+ySub²))/2 -/
noncomputable def h16Param : RatPoly 16 :=
  C (1 / 2 : ℚ) * c16Param * (a16Param ^ 2 + b16Param ^ 2)

/-- The positive-triple parametrization with unrestricted integer parameters, obtained
from the four-variable positive parametrization by replacing the positive/nonnegative
parameters with four-square expressions. -/
theorem exists_16_param_parametrization :
    IsIntValued f16Param ∧ IsIntValued g16Param ∧ IsIntValued h16Param ∧
    positivePythagoreanTriples =
      {(x, y, z) | ∃ (a : Fin 16 → ℤ),
        ratPolyEval f16Param a = (x : ℚ) ∧
        ratPolyEval g16Param a = (y : ℚ) ∧
        ratPolyEval h16Param a = (z : ℚ)} := by
  let lift16ToPosInput : (Fin 16 → ℤ) → Fin 4 → ℤ := fun a =>
    mkRatPolyInput4
      (a (0 : Fin 16) ^ 2 + a (1 : Fin 16) ^ 2 + a (2 : Fin 16) ^ 2 +
        a (3 : Fin 16) ^ 2 + 1)
      (a (4 : Fin 16) ^ 2 + a (5 : Fin 16) ^ 2 + a (6 : Fin 16) ^ 2 +
        a (7 : Fin 16) ^ 2 + 1)
      (a (8 : Fin 16) ^ 2 + a (9 : Fin 16) ^ 2 + a (10 : Fin 16) ^ 2 +
        a (11 : Fin 16) ^ 2 + 1)
      (a (12 : Fin 16) ^ 2 + a (13 : Fin 16) ^ 2 + a (14 : Fin 16) ^ 2 +
        a (15 : Fin 16) ^ 2)
  have hf_eval (a : Fin 16 → ℤ) :
      ratPolyEval f16Param a = ratPolyEval fPosParam (lift16ToPosInput a) := by
    simp [ratPolyEval, f16Param, fPosParam, c16Param, a16Param, b16Param,
      xSub, ySub, zSub, wSub, cPosParam, aPosParam, bPosParam, xVar, yVar,
      zVar, wVar, lift16ToPosInput, mkRatPolyInput4]
  have hg_eval (a : Fin 16 → ℤ) :
      ratPolyEval g16Param a = ratPolyEval gPosParam (lift16ToPosInput a) := by
    simp [ratPolyEval, g16Param, gPosParam, c16Param, a16Param, b16Param,
      xSub, ySub, zSub, wSub, cPosParam, aPosParam, bPosParam, xVar, yVar,
      zVar, wVar, lift16ToPosInput, mkRatPolyInput4]
  have hh_eval (a : Fin 16 → ℤ) :
      ratPolyEval h16Param a = ratPolyEval hPosParam (lift16ToPosInput a) := by
    simp [ratPolyEval, h16Param, hPosParam, c16Param, a16Param, b16Param,
      xSub, ySub, zSub, wSub, cPosParam, aPosParam, bPosParam, xVar, yVar,
      zVar, wVar, lift16ToPosInput, mkRatPolyInput4]
  have hf16 : IsIntValued f16Param := by
    intro a
    rcases f_pos_param_intValued (lift16ToPosInput a) with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    change ratPolyEval f16Param a = (k : ℚ)
    have hk' : ratPolyEval fPosParam (lift16ToPosInput a) = (k : ℚ) := by
      simpa [ratPolyEval] using hk
    exact (hf_eval a).trans hk'
  have hg16 : IsIntValued g16Param := by
    intro a
    rcases g_pos_param_intValued (lift16ToPosInput a) with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    change ratPolyEval g16Param a = (k : ℚ)
    have hk' : ratPolyEval gPosParam (lift16ToPosInput a) = (k : ℚ) := by
      simpa [ratPolyEval] using hk
    exact (hg_eval a).trans hk'
  have hh16 : IsIntValued h16Param := by
    intro a
    rcases h_pos_param_intValued (lift16ToPosInput a) with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    change ratPolyEval h16Param a = (k : ℚ)
    have hk' : ratPolyEval hPosParam (lift16ToPosInput a) = (k : ℚ) := by
      simpa [ratPolyEval] using hk
    exact (hh_eval a).trans hk'
  rcases positive_triples_parametrization with ⟨_, _, _, hpos4⟩
  refine ⟨hf16, hg16, hh16, ?_⟩
  rw [hpos4]
  ext p
  rcases p with ⟨x, y, z⟩
  constructor
  · rintro ⟨x', y', z', w', hxpos, hypos, hzpos, hwnonneg, hf, hg, hh⟩
    rcases (int_positive_iff_four_squares_add_one x').mp hxpos with
      ⟨x0, x1, x2, x3, hxsum⟩
    rcases (int_positive_iff_four_squares_add_one y').mp hypos with
      ⟨y0, y1, y2, y3, hysum⟩
    rcases (int_positive_iff_four_squares_add_one z').mp hzpos with
      ⟨z0, z1, z2, z3, hzsum⟩
    rcases (int_nonneg_iff_four_squares w').mp hwnonneg with
      ⟨w0, w1, w2, w3, hwsum⟩
    let a : Fin 16 → ℤ := fun i =>
      if i = (0 : Fin 16) then x0 else
      if i = (1 : Fin 16) then x1 else
      if i = (2 : Fin 16) then x2 else
      if i = (3 : Fin 16) then x3 else
      if i = (4 : Fin 16) then y0 else
      if i = (5 : Fin 16) then y1 else
      if i = (6 : Fin 16) then y2 else
      if i = (7 : Fin 16) then y3 else
      if i = (8 : Fin 16) then z0 else
      if i = (9 : Fin 16) then z1 else
      if i = (10 : Fin 16) then z2 else
      if i = (11 : Fin 16) then z3 else
      if i = (12 : Fin 16) then w0 else
      if i = (13 : Fin 16) then w1 else
      if i = (14 : Fin 16) then w2 else w3
    have hinput : lift16ToPosInput a = mkRatPolyInput4 x' y' z' w' := by
      funext i
      fin_cases i <;> simp [lift16ToPosInput, mkRatPolyInput4, a, hxsum, hysum, hzsum,
        hwsum]
    refine ⟨a, ?_, ?_, ?_⟩
    · calc
        ratPolyEval f16Param a = ratPolyEval fPosParam (lift16ToPosInput a) :=
          hf_eval a
        _ = ratPolyEval fPosParam (mkRatPolyInput4 x' y' z' w') := by rw [hinput]
        _ = (x : ℚ) := hf
    · calc
        ratPolyEval g16Param a = ratPolyEval gPosParam (lift16ToPosInput a) :=
          hg_eval a
        _ = ratPolyEval gPosParam (mkRatPolyInput4 x' y' z' w') := by rw [hinput]
        _ = (y : ℚ) := hg
    · calc
        ratPolyEval h16Param a = ratPolyEval hPosParam (lift16ToPosInput a) :=
          hh_eval a
        _ = ratPolyEval hPosParam (mkRatPolyInput4 x' y' z' w') := by rw [hinput]
        _ = (z : ℚ) := hh
  · rintro ⟨a, hf, hg, hh⟩
    let x' : ℤ := a (0 : Fin 16) ^ 2 + a (1 : Fin 16) ^ 2 + a (2 : Fin 16) ^ 2 +
      a (3 : Fin 16) ^ 2 + 1
    let y' : ℤ := a (4 : Fin 16) ^ 2 + a (5 : Fin 16) ^ 2 + a (6 : Fin 16) ^ 2 +
      a (7 : Fin 16) ^ 2 + 1
    let z' : ℤ := a (8 : Fin 16) ^ 2 + a (9 : Fin 16) ^ 2 + a (10 : Fin 16) ^ 2 +
      a (11 : Fin 16) ^ 2 + 1
    let w' : ℤ := a (12 : Fin 16) ^ 2 + a (13 : Fin 16) ^ 2 + a (14 : Fin 16) ^ 2 +
      a (15 : Fin 16) ^ 2
    have hxpos : 0 < x' := by
      dsimp [x']
      nlinarith [sq_nonneg (a (0 : Fin 16)), sq_nonneg (a (1 : Fin 16)),
        sq_nonneg (a (2 : Fin 16)), sq_nonneg (a (3 : Fin 16))]
    have hypos : 0 < y' := by
      dsimp [y']
      nlinarith [sq_nonneg (a (4 : Fin 16)), sq_nonneg (a (5 : Fin 16)),
        sq_nonneg (a (6 : Fin 16)), sq_nonneg (a (7 : Fin 16))]
    have hzpos : 0 < z' := by
      dsimp [z']
      nlinarith [sq_nonneg (a (8 : Fin 16)), sq_nonneg (a (9 : Fin 16)),
        sq_nonneg (a (10 : Fin 16)), sq_nonneg (a (11 : Fin 16))]
    have hwnonneg : 0 ≤ w' := by
      dsimp [w']
      nlinarith [sq_nonneg (a (12 : Fin 16)), sq_nonneg (a (13 : Fin 16)),
        sq_nonneg (a (14 : Fin 16)), sq_nonneg (a (15 : Fin 16))]
    have hinput : lift16ToPosInput a = mkRatPolyInput4 x' y' z' w' := by
      funext i
      fin_cases i <;> simp [lift16ToPosInput, mkRatPolyInput4, x', y', z', w']
    refine ⟨x', y', z', w', hxpos, hypos, hzpos, hwnonneg, ?_, ?_, ?_⟩
    · calc
        ratPolyEval fPosParam (mkRatPolyInput4 x' y' z' w') =
            ratPolyEval fPosParam (lift16ToPosInput a) := by rw [hinput]
        _ = ratPolyEval f16Param a := (hf_eval a).symm
        _ = (x : ℚ) := hf
    · calc
        ratPolyEval gPosParam (mkRatPolyInput4 x' y' z' w') =
            ratPolyEval gPosParam (lift16ToPosInput a) := by rw [hinput]
        _ = ratPolyEval g16Param a := (hg_eval a).symm
        _ = (y : ℚ) := hg
    · calc
        ratPolyEval hPosParam (mkRatPolyInput4 x' y' z' w') =
            ratPolyEval hPosParam (lift16ToPosInput a) := by rw [hinput]
        _ = ratPolyEval h16Param a := (hh_eval a).symm
        _ = (z : ℚ) := hh

end LeanPool.PythagoreanPolynomialParametrization
