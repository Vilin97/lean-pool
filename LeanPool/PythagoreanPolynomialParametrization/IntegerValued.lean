/-
Copyright (c) 2026 Lazar Milikic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lazar Milikic
-/

import LeanPool.PythagoreanPolynomialParametrization.SourceLemmas

/-! # Integer-valued parametrization of all Pythagorean triples

This file contains the explicit four-variable integer-valued polynomial triple from
Frisch and Vaserstein's main theorem.
-/

namespace LeanPool.PythagoreanPolynomialParametrization

open MvPolynomial



/-- Variable x (index 0) in the 4-variable rational polynomial ring. -/
noncomputable def xVar : RatPoly 4 := X 0

/-- Variable y (index 1) in the 4-variable rational polynomial ring. -/
noncomputable def yVar : RatPoly 4 := X 1

/-- Variable z (index 2) in the 4-variable rational polynomial ring. -/
noncomputable def zVar : RatPoly 4 := X 2

/-- Variable w (index 3) in the 4-variable rational polynomial ring. -/
noncomputable def wVar : RatPoly 4 := X 3

/-- a = y + z·w -/
noncomputable def aParam : RatPoly 4 := yVar + zVar * wVar

/-- b = z - y·w -/
noncomputable def bParam : RatPoly 4 := zVar - yVar * wVar

/-- c = 2x - x·w -/
noncomputable def cParam : RatPoly 4 := C (2 : ℚ) * xVar - xVar * wVar

/-- f = c·(a² - b²)/2

In the paper: ((2x-xw)((y+zw)²-(z-yw)²))/2 -/
noncomputable def fParam : RatPoly 4 := C (1 / 2 : ℚ) * cParam * (aParam ^ 2 - bParam ^ 2)

/-- g = c·a·b

In the paper: (2x-xw)(y+zw)(z-yw) -/
noncomputable def gParam : RatPoly 4 := cParam * aParam * bParam

/-- h = c·(a² + b²)/2

In the paper: ((2x-xw)((y+zw)²+(z-yw)²))/2 -/
noncomputable def hParam : RatPoly 4 := C (1 / 2 : ℚ) * cParam * (aParam ^ 2 + bParam ^ 2)

/-- The first coordinate polynomial in the four-variable parametrization is integer-valued. -/
theorem f_param_intValued : IsIntValued fParam := by
  intro v
  let x : ℤ := v (0 : Fin 4)
  let y : ℤ := v (1 : Fin 4)
  let z : ℤ := v (2 : Fin 4)
  let w : ℤ := v (3 : Fin 4)
  let A : ℤ := y + z * w
  let B : ℤ := z - y * w
  let Cc : ℤ := (2 : ℤ) * x - x * w
  have hpar : PaperParityCondition A B Cc := by
    exact (parity_condition_parametrized A B Cc).mpr ⟨x, y, z, w, rfl, rfl, rfl⟩
  rcases (TMap_integral_iff_parity A B Cc).mpr hpar with ⟨fx, gy, hz, hT⟩
  refine ⟨fx, ?_⟩
  have hfcoord : (Cc : ℚ) * ((A : ℚ) ^ 2 - (B : ℚ) ^ 2) / 2 = (fx : ℚ) := by
    simpa [TMap] using congrArg Prod.fst hT
  rw [← hfcoord]
  simp [fParam, cParam, aParam, bParam, xVar, yVar, zVar, wVar, A, B, Cc]
  ring

/-- The second coordinate polynomial in the four-variable parametrization is integer-valued. -/
theorem g_param_intValued : IsIntValued gParam := by
  intro v
  let x : ℤ := v (0 : Fin 4)
  let y : ℤ := v (1 : Fin 4)
  let z : ℤ := v (2 : Fin 4)
  let w : ℤ := v (3 : Fin 4)
  let A : ℤ := y + z * w
  let B : ℤ := z - y * w
  let Cc : ℤ := (2 : ℤ) * x - x * w
  refine ⟨Cc * A * B, ?_⟩
  simp [gParam, cParam, aParam, bParam, xVar, yVar, zVar, wVar, A, B, Cc]
  ring

/-- The third coordinate polynomial in the four-variable parametrization is integer-valued. -/
theorem h_param_intValued : IsIntValued hParam := by
  intro v
  let x : ℤ := v (0 : Fin 4)
  let y : ℤ := v (1 : Fin 4)
  let z : ℤ := v (2 : Fin 4)
  let w : ℤ := v (3 : Fin 4)
  let A : ℤ := y + z * w
  let B : ℤ := z - y * w
  let Cc : ℤ := (2 : ℤ) * x - x * w
  have hpar : PaperParityCondition A B Cc := by
    exact (parity_condition_parametrized A B Cc).mpr ⟨x, y, z, w, rfl, rfl, rfl⟩
  rcases (TMap_integral_iff_parity A B Cc).mpr hpar with ⟨fx, gy, hz, hT⟩
  refine ⟨hz, ?_⟩
  have hhcoord : (Cc : ℚ) * ((A : ℚ) ^ 2 + (B : ℚ) ^ 2) / 2 = (hz : ℚ) := by
    simpa [TMap] using congrArg (fun p : ℚ × ℚ × ℚ => p.2.2) hT
  rw [← hhcoord]
  simp [hParam, cParam, aParam, bParam, xVar, yVar, zVar, wVar, A, B, Cc]
  ring

/-- Frisch--Vaserstein's four-variable integer-valued polynomial parametrization of all
Pythagorean triples. -/
theorem exists_int_valued_parametrization :
    IntValuedParametrizes fParam gParam hParam pythagoreanTriples := by
  refine ⟨f_param_intValued, g_param_intValued, h_param_intValued, ?_⟩
  ext p
  rcases p with ⟨x, y, z⟩
  constructor
  · intro hp
    have hpy : IsPythagoreanTriple x y z := by
      simpa [pythagoreanTriples] using hp
    rcases (pythagorean_iff_mem_TMap_range x y z).mp hpy with ⟨a, b, c, hT⟩
    have hIntegral : IsIntegralTValue a b c := ⟨x, y, z, hT⟩
    have hpar : PaperParityCondition a b c := (TMap_integral_iff_parity a b c).mp hIntegral
    rcases (parity_condition_parametrized a b c).mp hpar with
      ⟨x0, y0, z0, w0, ha, hb, hc⟩
    let v : Fin 4 → ℤ := fun i =>
      if i = (0 : Fin 4) then x0 else
      if i = (1 : Fin 4) then y0 else
      if i = (2 : Fin 4) then z0 else w0
    refine ⟨v, ?_, ?_, ?_⟩
    · have hfcoord : (c : ℚ) * ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) / 2 = (x : ℚ) := by
        simpa [TMap] using congrArg Prod.fst hT
      rw [← hfcoord]
      rw [ha, hb, hc]
      simp [ratPolyEval, fParam, cParam, aParam, bParam, xVar, yVar, zVar, wVar, v]
      ring
    · have hgcoord : (c : ℚ) * (a : ℚ) * (b : ℚ) = (y : ℚ) := by
        simpa [TMap] using congrArg (fun p : ℚ × ℚ × ℚ => p.2.1) hT
      rw [← hgcoord]
      rw [ha, hb, hc]
      simp [ratPolyEval, gParam, cParam, aParam, bParam, xVar, yVar, zVar, wVar, v]
    · have hhcoord : (c : ℚ) * ((a : ℚ) ^ 2 + (b : ℚ) ^ 2) / 2 = (z : ℚ) := by
        simpa [TMap] using congrArg (fun p : ℚ × ℚ × ℚ => p.2.2) hT
      rw [← hhcoord]
      rw [ha, hb, hc]
      simp [ratPolyEval, hParam, cParam, aParam, bParam, xVar, yVar, zVar, wVar, v]
      ring
  · rintro ⟨v, hf, hg, hh⟩
    let x0 : ℤ := v (0 : Fin 4)
    let y0 : ℤ := v (1 : Fin 4)
    let z0 : ℤ := v (2 : Fin 4)
    let w0 : ℤ := v (3 : Fin 4)
    let A : ℤ := y0 + z0 * w0
    let B : ℤ := z0 - y0 * w0
    let Cc : ℤ := (2 : ℤ) * x0 - x0 * w0
    have hfcoord : (Cc : ℚ) * ((A : ℚ) ^ 2 - (B : ℚ) ^ 2) / 2 = (x : ℚ) := by
      rw [← hf]
      simp [ratPolyEval, fParam, cParam, aParam, bParam,
        xVar, yVar, zVar, wVar, A, B, Cc, x0, y0, z0, w0]
      ring
    have hgcoord : (Cc : ℚ) * (A : ℚ) * (B : ℚ) = (y : ℚ) := by
      rw [← hg]
      simp [ratPolyEval, gParam, cParam, aParam, bParam,
        xVar, yVar, zVar, wVar, A, B, Cc, x0, y0, z0, w0]
    have hhcoord : (Cc : ℚ) * ((A : ℚ) ^ 2 + (B : ℚ) ^ 2) / 2 = (z : ℚ) := by
      rw [← hh]
      simp [ratPolyEval, hParam, cParam, aParam, bParam,
        xVar, yVar, zVar, wVar, A, B, Cc, x0, y0, z0, w0]
      ring
    have hT : ∃ a b c : ℤ, TMap a b c = ((x : ℚ), (y : ℚ), (z : ℚ)) := by
      refine ⟨A, B, Cc, ?_⟩
      ext
      · simpa [TMap] using hfcoord
      · simpa [TMap] using hgcoord
      · simpa [TMap] using hhcoord
    have hpy : IsPythagoreanTriple x y z := (pythagorean_iff_mem_TMap_range x y z).mpr hT
    simpa [pythagoreanTriples] using hpy

end LeanPool.PythagoreanPolynomialParametrization
