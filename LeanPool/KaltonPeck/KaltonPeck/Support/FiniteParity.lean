/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
import LeanPool.KaltonPeck.KaltonPeck.Support.Definitions
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Finite-dimensional parity

This file proves the parity results for finite-dimensional alternating forms and complex
structures that underlie the later rank-parity arguments.
-/

namespace KaltonPeck.Support.FiniteParity

noncomputable
section

/-- A finite-dimensional real alternating bilinear form has even rank, and its radical has the
same parity as the ambient space.

Blueprint: `lem:finite-alt-even`; audit: `LEM-FINITE-ALT-RANK-EVEN`. -/
theorem finiteAlternatingRankEven {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (c : LinearMap.BilinForm ℝ V) (hc : c.IsAlt) :
    Even (Module.finrank ℝ c.range) ∧
      Nat.ModEq 2 (Module.finrank ℝ c.ker) (Module.finrank ℝ V) := by
  classical
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl c.ker
  let b : LinearMap.BilinForm ℝ W := c.restrict W
  have hbAlt : b.IsAlt := by
    intro x
    exact hc x
  have hbND : b.Nondegenerate := by
    rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    apply Subtype.ext
    have hxall : ∀ y : V, c (x : V) y = 0 := by
      intro y
      obtain ⟨k, w, hk, hw, rfl⟩ :=
        Submodule.codisjoint_iff_exists_add_eq.mp hW.codisjoint y
      have hk0 : c k = 0 := LinearMap.mem_ker.mp hk
      have hkx : c k (x : V) = 0 := by rw [hk0]; rfl
      have hxk : c (x : V) k = 0 := hc.isRefl k (x : V) hkx
      have hx0 : b x = 0 := LinearMap.mem_ker.mp hx
      have hxw : c (x : V) w = 0 := by
        exact LinearMap.congr_fun hx0 ⟨w, hw⟩
      simp only [map_add, hxk, hxw, add_zero]
    have hxker : (x : V) ∈ c.ker := by
      rw [LinearMap.mem_ker]
      ext y
      exact hxall y
    have hxbot : (x : V) ∈ (⊥ : Submodule ℝ V) :=
      hW.disjoint.le_bot ⟨hxker, x.property⟩
    simpa using hxbot
  have hWEven : Even (Module.finrank ℝ W) := by
    let e := Module.finBasis ℝ W
    let A := LinearMap.BilinForm.toMatrix e b
    have hskew : Matrix.transpose A = -A := by
      ext i j
      simp only [Matrix.transpose_apply, Matrix.neg_apply, A,
        LinearMap.BilinForm.toMatrix_apply]
      exact (hbAlt.neg_eq (e i) (e j)).symm
    have hdet : A.det ≠ 0 :=
      (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero e).mp hbND
    by_contra hEven
    have hOdd : Odd (Module.finrank ℝ W) := Nat.not_even_iff_odd.mp hEven
    have hdetEq := congrArg Matrix.det hskew
    rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin, hOdd.neg_one_pow] at hdetEq
    apply hdet
    linarith
  have hrank := LinearMap.finrank_range_add_finrank_ker c
  have hdim := Submodule.finrank_add_eq_of_isCompl hW
  have hwrank : Module.finrank ℝ W = Module.finrank ℝ c.range := by omega
  rw [hwrank] at hWEven
  constructor
  · exact hWEven
  · have hrmod : Nat.ModEq 2 (Module.finrank ℝ c.range) 0 :=
      hWEven.two_dvd.modEq_zero_nat
    have hsumMod := hrmod.add_right (Module.finrank ℝ c.ker)
    rw [hrank] at hsumMod
    simpa using hsumMod.symm

/-- Continuous finite-dimensional wrapper for even rank of an alternating form.

Blueprint: `lem:finite-alt-even`; audit: `LEM-FINITE-ALT-RANK-EVEN`. -/
theorem finiteContinuousAlternatingRankEven {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (c : ContinuousAlternatingForm V) :
    Even (Module.finrank ℝ c.toDual.toLinearMap.range) ∧
      Nat.ModEq 2 (Module.finrank ℝ c.radical) (Module.finrank ℝ V) := by
  let e : StrongDual ℝ V ≃ₗ[ℝ] Module.Dual ℝ V :=
    (LinearMap.toContinuousLinearMap :
      (Module.Dual ℝ V) ≃ₗ[ℝ] StrongDual ℝ V).symm
  let b : LinearMap.BilinForm ℝ V := e.toLinearMap.comp c.toDual.toLinearMap
  have hbAlt : b.IsAlt := by
    intro x
    exact c.alternating x
  obtain ⟨hrEven, hkerMod⟩ := finiteAlternatingRankEven b hbAlt
  have hker : b.ker = c.toDual.toLinearMap.ker := by
    ext x
    simp [b, e]
  have hrank : Module.finrank ℝ b.range =
      Module.finrank ℝ c.toDual.toLinearMap.range := by
    have hbRN := LinearMap.finrank_range_add_finrank_ker b
    have hcRN := LinearMap.finrank_range_add_finrank_ker c.toDual.toLinearMap
    rw [hker] at hbRN
    omega
  constructor
  · simpa [← hrank] using hrEven
  · rw [hker] at hkerMod
    rw [c.radical_eq_ker]
    exact hkerMod

/-- A finite-dimensional real vector space carrying an endomorphism squaring to `-I` has even
dimension.

Blueprint: `lem:finite-complex-even`; audit: `LEM-COMPLEX-STRUCTURE-EVEN-DIM`. -/
theorem finiteComplexDimensionEven {V : Type*} [AddCommGroup V] [Module ℝ V]
     (J : Module.End ℝ V) (hJ : J ^ 2 = -1) :
    Even (Module.finrank ℝ V) := by
  by_contra h
  have hOdd : Odd (Module.finrank ℝ V) := Nat.not_even_iff_odd.mp h
  have hneg : (-1 : Module.End ℝ V) = (-1 : ℝ) • LinearMap.id := by
    ext x
    simp
  have hdet := congrArg LinearMap.det hJ
  rw [map_pow, hneg, LinearMap.det_smul, LinearMap.det_id, mul_one,
    hOdd.neg_one_pow] at hdet
  nlinarith [sq_nonneg (LinearMap.det J)]

/-- Continuous-linear wrapper for finite complex structures.

Blueprint: `lem:finite-complex-even`; audit: `LEM-COMPLEX-STRUCTURE-EVEN-DIM`. -/
theorem finiteContinuousComplexDimensionEven {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (J : V →L[ℝ] V)
    (hJ : IsComplexStructure J) : Even (Module.finrank ℝ V) := by
  apply finiteComplexDimensionEven J.toLinearMap
  exact congrArg ContinuousLinearMap.toLinearMap hJ

/-- A finite-dimensional invariant subspace of a real complex structure has even dimension.

Blueprint: `lem:finite-complex-even`; audit: `LEM-COMPLEX-STRUCTURE-EVEN-DIM`. -/
theorem finiteInvariantSubmoduleComplexDimensionEven {V : Type*} [AddCommGroup V]
    [Module ℝ V] (J : Module.End ℝ V) (W : Submodule ℝ V)
    (hW : ∀ x : W, J x ∈ W) (hJ : ∀ x : W, J (J x) = -(x : V)) :
    Even (Module.finrank ℝ W) := by
  let JW : Module.End ℝ W :=
    J.restrict (fun x hx => hW ⟨x, hx⟩)
  apply finiteComplexDimensionEven JW
  ext x
  simpa [JW, pow_two] using hJ x

end

end KaltonPeck.Support.FiniteParity

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
