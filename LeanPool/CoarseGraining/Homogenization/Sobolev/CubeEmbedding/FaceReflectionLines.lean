/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Reflections
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Derivatives
public import LeanPool.CoarseGraining.Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! # Face Reflection Lines -/

@[expose] public section

namespace Homogenization

open Homogenization
open scoped BigOperators

/-!
# Single-face even reflection: definitions and per-line calculus

Global (on all of `ℝ^d`) even reflection of a function across the face
`{x_i = a}`, its candidate gradient (sign-flipped in direction `i` on the
reflected side), the geometric fact that the reflection commutes with coordinate
insertion, and the one-dimensional derivatives of the direct and reflected line
functions.  These feed the Fubini assembly in `FaceReflection`.
-/

noncomputable section

variable {d : ℕ}

/-- Even reflection of `v` across the face `{x_i = a}`: unchanged where
`a ≤ x i`, reflected otherwise. -/
def faceReflect (v : Vec d → ℝ) (a : ℝ) (i : Fin d) : Vec d → ℝ :=
  fun x => if a ≤ x i then v x else v (coordFaceReflection a i x)

/-- Candidate gradient of `faceReflect v a i`: the reflected-side gradient carries
a sign flip in direction `i` (and no flip in the other directions). -/
def faceGrad (v : Vec d → ℝ) (a : ℝ) (i : Fin d) : Vec d → Vec d :=
  fun x j =>
    if a ≤ x i then (fderiv ℝ v x) (basisVec j)
    else (if j = i then (-1 : ℝ) else 1) *
      (fderiv ℝ v (coordFaceReflection a i x)) (basisVec j)

/-- The face reflection commutes with coordinate insertion at the reflected axis:
inserting `t` at `i` then reflecting is inserting `2a − t`. -/
theorem coordFaceReflection_insertNth {n : ℕ} (a : ℝ) (i : Fin (n + 1))
    (t : ℝ) (z : Vec n) :
    coordFaceReflection a i (i.insertNth t z) = i.insertNth (2 * a - t) z := by
  funext j
  rw [coordFaceReflection_apply]
  rcases eq_or_ne j i with h | h
  · subst h; simp
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
    simp [Fin.insertNth_apply_succAbove, h]

/-- The insertion line `t ↦ i.insertNth t z` is affine with velocity `basisVec i`. -/
theorem hasDerivAt_insertNth {n : ℕ} (i : Fin (n + 1)) (z : Vec n) (t₀ : ℝ) :
    HasDerivAt (fun t => (i.insertNth t z : Vec (n + 1))) (basisVec i) t₀ := by
  have hfun : (fun t : ℝ => (i.insertNth t z : Vec (n + 1)))
      = fun t => t • (basisVec i) + i.insertNth 0 z := by
    funext t
    funext j
    rcases eq_or_ne j i with h | h
    · subst h
      simp [Fin.insertNth_apply_same, basisVec]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
      simp [Fin.insertNth_apply_succAbove, basisVec, Fin.succAbove_ne]
  rw [hfun]
  simpa using ((hasDerivAt_id t₀).smul_const (basisVec i)).add_const (i.insertNth 0 z)

/-- The reflected insertion line `t ↦ i.insertNth (2a − t) z` has velocity
`-basisVec i`. -/
theorem hasDerivAt_insertNth_reflect {n : ℕ} (a : ℝ) (i : Fin (n + 1))
    (z : Vec n) (t₀ : ℝ) :
    HasDerivAt (fun t => (i.insertNth (2 * a - t) z : Vec (n + 1)))
      (-basisVec i) t₀ := by
  have hinner : HasDerivAt (fun t : ℝ => 2 * a - t) (-1) t₀ := by
    simpa using (hasDerivAt_id t₀).const_sub (2 * a)
  have hcomp := (hasDerivAt_insertNth i z (2 * a - t₀)).scomp t₀ hinner
  simpa using! hcomp

/-- Directional derivative of `v` along the insertion line in direction `i`. -/
theorem hasDerivAt_comp_insertNth {n : ℕ} {v : Vec (n + 1) → ℝ}
    (hv : Differentiable ℝ v) (i : Fin (n + 1)) (z : Vec n) (t₀ : ℝ) :
    HasDerivAt (fun t => v (i.insertNth t z))
      ((fderiv ℝ v (i.insertNth t₀ z)) (basisVec i)) t₀ :=
  (hv (i.insertNth t₀ z)).hasFDerivAt.comp_hasDerivAt t₀ (hasDerivAt_insertNth i z t₀)

/-- Directional derivative of `v` along the reflected insertion line. -/
theorem hasDerivAt_comp_insertNth_reflect {n : ℕ} {v : Vec (n + 1) → ℝ}
    (hv : Differentiable ℝ v) (a : ℝ) (i : Fin (n + 1)) (z : Vec n) (t₀ : ℝ) :
    HasDerivAt (fun t => v (i.insertNth (2 * a - t) z))
      ((fderiv ℝ v (i.insertNth (2 * a - t₀) z)) (-basisVec i)) t₀ :=
  (hv (i.insertNth (2 * a - t₀) z)).hasFDerivAt.comp_hasDerivAt t₀
    (hasDerivAt_insertNth_reflect a i z t₀)

/-- Velocity of the reflected insertion line in a *tangential* coordinate `j ≠ i`:
inserting `t` at `j` then reflecting across `{x_i = a}` moves with velocity
`basisVec j` (the reflection fixes tangential directions). -/
theorem hasDerivAt_coordFaceReflection_insertNth {n : ℕ}
    (a : ℝ) {i j : Fin (n + 1)} (hji : j ≠ i) (z : Vec n) (t₀ : ℝ) :
    HasDerivAt (fun t => coordFaceReflection a i (j.insertNth t z))
      (basisVec j) t₀ := by
  have hline : HasDerivAt (fun t : ℝ => (j.insertNth t z : Vec (n + 1)))
      (basisVec j) t₀ := hasDerivAt_insertNth j z t₀
  have hA : HasDerivAt
      (fun t => coordReflectionLinear i (j.insertNth t z))
      (coordReflectionLinear i (basisVec j)) t₀ :=
    (coordReflectionLinear i).hasFDerivAt.comp_hasDerivAt t₀ hline
  have hvel : coordReflectionLinear i (basisVec j) = basisVec j := by
    rw [coordReflectionLinear_basisVec, if_neg hji, one_smul]
  rw [hvel] at hA
  exact hA.add_const (coordFaceReflectionOffset a i)

/-- Directional derivative of `v` along the reflected insertion line in a
tangential coordinate `j ≠ i`. -/
theorem hasDerivAt_comp_coordFaceReflection_insertNth {n : ℕ} {v : Vec (n + 1) → ℝ}
    (hv : Differentiable ℝ v) (a : ℝ) {i j : Fin (n + 1)} (hji : j ≠ i)
    (z : Vec n) (t₀ : ℝ) :
    HasDerivAt (fun t => v (coordFaceReflection a i (j.insertNth t z)))
      ((fderiv ℝ v (coordFaceReflection a i (j.insertNth t₀ z))) (basisVec j)) t₀ :=
  (hv (coordFaceReflection a i (j.insertNth t₀ z))).hasFDerivAt.comp_hasDerivAt t₀
    (hasDerivAt_coordFaceReflection_insertNth a hji z t₀)

end

end Homogenization
