/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.BalancedCombination
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Rational approximation within rational affine constraints

A generalized inverse over the rationals gives an affine projection onto
any consistent rational system. Its real extension allows approximation
by rational solutions while retaining open inequalities.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace EGZ.BalancedCombination

/-- Every rational matrix admits a generalized inverse, including rectangular
and rank-deficient matrices. -/
theorem exists_matrix_generalized_inverse {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℚ) : ∃ B : Matrix J I ℚ, A * B * A = A := by
  classical
  let f := Matrix.toLin' A
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨g, hg⟩ := s.exists_extend
  have hfgf : (f.comp g).comp f = f := by
    apply LinearMap.ext
    intro x
    have h₁ := LinearMap.congr_fun hg (f.rangeRestrict x)
    have h₂ := LinearMap.congr_fun hs (f.rangeRestrict x)
    have h₂' := congrArg Subtype.val h₂
    exact (congrArg f h₁).trans h₂'
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', f] using
    congrArg LinearMap.toMatrix' hfgf

/-- Rational solutions of a rational linear system are dense in its real
solution set. In particular, any open inequalities valid at a real solution
remain valid at some rational solution. -/
theorem exists_rational_solution_mem_open {I J : Type*} [Finite I] [Fintype J]
    (A : Matrix I J ℚ) (b : I → ℚ) (x : J → ℝ)
    (hx : (A.map (Rat.castHom ℝ)) *ᵥ x = fun i ↦ (b i : ℝ))
    (U : Set (J → ℝ)) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ y : J → ℚ, A *ᵥ y = b ∧ (fun j ↦ (y j : ℝ)) ∈ U := by
  let := Fintype.ofFinite I
  classical
  obtain ⟨B, hB⟩ := exists_matrix_generalized_inverse A
  let AR : Matrix I J ℝ := A.map (Rat.castHom ℝ)
  let BR : Matrix J I ℝ := B.map (Rat.castHom ℝ)
  let bR : I → ℝ := fun i ↦ b i
  have hxR : AR *ᵥ x = bR := hx
  have hBR : AR * BR * AR = AR := by
    simpa only [Matrix.map_mul] using congrArg (fun M : Matrix I J ℚ ↦ M.map (Rat.castHom ℝ)) hB
  have hAbR : AR *ᵥ (BR *ᵥ bR) = bR := by
    rw [← hxR]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBR]
  have hAb : A *ᵥ (B *ᵥ b) = b := by
    ext i
    have h := congrFun hAbR i
    dsimp [AR, BR, bR, Matrix.mulVec, dotProduct, Matrix.map] at h
    exact_mod_cast h
  let P : (J → ℝ) → J → ℝ := fun y ↦ y + BR *ᵥ (bR - AR *ᵥ y)
  have hP : Continuous P := by
    apply continuous_pi
    intro j
    dsimp [P, Matrix.mulVec, dotProduct]
    fun_prop
  have hPx : P x = x := by
    simp only [P, show AR *ᵥ x = bR from hx, sub_self, Matrix.mulVec_zero, add_zero]
  have hdense : DenseRange (fun y : J → ℚ ↦ fun j ↦ (y j : ℝ)) :=
    DenseRange.piMap (fun _ ↦ Rat.denseRange_cast)
  obtain ⟨y, hy⟩ := hdense.exists_mem_open (hU.preimage hP)
    ⟨x, by simpa only [Set.mem_preimage, hPx] using hxU⟩
  let z : J → ℚ := y + B *ᵥ (b - A *ᵥ y)
  have hz : A *ᵥ z = b := by
    dsimp only [z]
    rw [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_sub,
      hAb, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB]
    abel
  refine ⟨z, hz, ?_⟩
  have hcast : (fun j ↦ (z j : ℝ)) = P (fun j ↦ (y j : ℝ)) := by
    ext j
    simp [z, P, BR, bR, AR, Matrix.mulVec, dotProduct]
  rw [hcast]
  exact hy

end EGZ.BalancedCombination
