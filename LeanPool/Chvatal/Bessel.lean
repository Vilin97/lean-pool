/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvátal formalization contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

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

/-!
# Normalized finite-dimensional Hilbert spaces

Theorem 2.1 uses the uniform probability inner product, rather than the counting
inner product on Euclidean space. This file transfers mathlib's Bessel inequality
and Gram–Schmidt theorem through the explicit normalization by `√|Ω|`.
-/

@[expose] public section

namespace Chvatal

noncomputable section

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- The uniform probability inner product in Section 2, generalized to any nonempty
finite sample space. -/
def uniformInner (f g : Ω → ℝ) : ℝ := (∑ x, f x * g x) / Fintype.card Ω

/-- The normalization which identifies the paper's probability inner product with
mathlib's Euclidean inner product. -/
noncomputable def uniformEuclidean : (Ω → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ Ω :=
  (LinearEquiv.smulOfNeZero ℝ (Ω → ℝ) (Real.sqrt (Fintype.card Ω))⁻¹
    (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by exact_mod_cast Fintype.card_pos)))).trans
      (WithLp.linearEquiv 2 ℝ (Ω → ℝ)).symm

/-- Coordinate formula for the normalization used in Theorem 2.1. -/
@[simp] theorem uniformEuclidean_apply (f : Ω → ℝ) (x : Ω) :
    uniformEuclidean f x = (Real.sqrt (Fintype.card Ω))⁻¹ * f x := rfl

/-- The normalization preserves exactly the probability inner product of Section 2. -/
theorem inner_uniformEuclidean (f g : Ω → ℝ) :
    inner ℝ (uniformEuclidean f) (uniformEuclidean g) = uniformInner f g := by
  rw [PiLp.inner_apply, uniformInner, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Real.inner_apply, uniformEuclidean_apply]
  have hpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hs := Real.sq_sqrt hpos.le
  have hne : Real.sqrt (Fintype.card Ω) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  field_simp
  rw [hs]
  ring

/-- Orthonormality with respect to uniform probability, as in Theorem 2.1 and
Corollary 3.2. The index type may be empty. -/
def UniformOrthonormal {κ : Type*} (u : κ → Ω → ℝ) : Prop := by
  classical
  exact ∀ i j, uniformInner (u i) (u j) = if i = j then 1 else 0

/-- Uniform orthonormality is ordinary orthonormality after normalization. -/
theorem uniformOrthonormal_iff {κ : Type*} (u : κ → Ω → ℝ) :
    UniformOrthonormal u ↔ Orthonormal ℝ (fun i => uniformEuclidean (u i)) := by
  classical
  rw [orthonormal_iff_ite]
  simp only [UniformOrthonormal, inner_uniformEuclidean]

/-- Theorem 2.1 (Bessel's inequality), with the paper's normalized inner product. -/
theorem bessel_inequality {κ : Type*} [Fintype κ] (u : κ → Ω → ℝ)
    (hu : UniformOrthonormal u) (h : Ω → ℝ) :
    ∑ i, (uniformInner (u i) h) ^ 2 ≤ uniformInner h h := by
  classical
  have hB := ((uniformOrthonormal_iff u).mp hu).sum_inner_products_le
    (s := Finset.univ) (uniformEuclidean h)
  simpa only [inner_uniformEuclidean, ← real_inner_self_eq_norm_sq,
    inner_uniformEuclidean, Real.norm_eq_abs, sq_abs] using hB

/-- The linear algebra step in Corollary 3.2: a finite independent family contained
in a subspace can be orthonormalized inside that same subspace. Thus simultaneous
physical and Fourier support restrictions, which define subspaces, are preserved. -/
theorem exists_uniformOrthonormal_in_submodule {κ : Type*} [Finite κ]
    (W : Submodule ℝ (Ω → ℝ)) (f : κ → Ω → ℝ)
    (hli : LinearIndependent ℝ f) (hf : ∀ i, f i ∈ W) :
    ∃ u : κ → Ω → ℝ, UniformOrthonormal u ∧ ∀ i, u i ∈ W := by
  classical
  let _ := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  let v : Fin (Fintype.card κ) → EuclideanSpace ℝ Ω :=
    fun i => uniformEuclidean (f (e.symm i))
  have hv : LinearIndependent ℝ v :=
    (hli.comp e.symm e.symm.injective).map'
      uniformEuclidean.toLinearMap (LinearMap.ker_eq_bot.mpr uniformEuclidean.injective)
  let w := InnerProductSpace.gramSchmidtNormed ℝ v
  have hw : Orthonormal ℝ w := InnerProductSpace.gramSchmidtNormed_orthonormal hv
  let L := W.map uniformEuclidean.toLinearMap
  have hspan : Submodule.span ℝ (Set.range v) ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_map.mpr ⟨f (e.symm i), hf _, rfl⟩
  have hwmem (i) : w i ∈ L := by
    apply hspan
    rw [← InnerProductSpace.span_gramSchmidt ℝ v,
      ← InnerProductSpace.span_gramSchmidtNormed_range]
    exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨fun i => uniformEuclidean.symm (w (e i)), ?_, ?_⟩
  · rw [uniformOrthonormal_iff]
    simpa only [LinearEquiv.apply_symm_apply, Function.comp_def] using hw.comp e e.injective
  · intro i
    obtain ⟨g, hg, hgeq⟩ := Submodule.mem_map.mp (hwmem (e i))
    change uniformEuclidean.symm (w (e i)) ∈ W
    rw [← hgeq]
    simpa using hg

end

end Chvatal
