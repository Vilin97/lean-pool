/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Archimedean.Real.Hom


/-!
# `CencovPetz.Simplex`

The strictly positive probability simplex on a finite type, together with its canonical tangent
submodule (sum-zero functions) and the classical Fisher information bilinear form.

This is groundwork for the finite/discrete Čencov (Chentsov) uniqueness story.

## Main definitions

- `CencovPetz.Simplex α`: strictly positive distributions `p : α → ℝ` with `∑ p = 1`.
- `CencovPetz.tangentSpace α`: the submodule `{u : α → ℝ | ∑ u = 0}`.
- `CencovPetz.fisherBilin p`: the Fisher bilinear form on `tangentSpace α`,
  `∑ uᵢ vᵢ / pᵢ`.

## Main results

- `CencovPetz.fisherBilin_comm`: symmetry of the Fisher bilinear form.
- `CencovPetz.fisherBilin_pos`: positive-definiteness on nonzero tangent vectors.
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- The strictly positive probability simplex on a finite type `α`. -/
structure Simplex (α : Type*) [Fintype α] : Type _ where
  /-- Coordinate representation `p : α → ℝ`. -/
  p : α → ℝ
  /-- Strict positivity of each coordinate. -/
  pos : ∀ a, 0 < p a
  /-- Normalization. -/
  sum_eq_one : (∑ a, p a) = 1

namespace Simplex

variable (p : Simplex α)

@[ext] lemma ext {p q : Simplex α} (h : p.p = q.p) : p = q := by
  cases p
  simp_all

lemma p_ne_zero (a : α) : p.p a ≠ 0 :=
  ne_of_gt (p.pos a)

end Simplex

/-- The linear functional `u ↦ ∑ a, u a` on `α → ℝ`. -/
noncomputable def sumLinearMap (α : Type*) [Fintype α] : (α → ℝ) →ₗ[ℝ] ℝ := by
  classical
  refine
    { toFun := fun u => ∑ a, u a
      map_add' := ?_
      map_smul' := ?_ }
  · intro u v
    -- `∑ (u+v) = ∑ u + ∑ v`.
    simpa [Pi.add_apply] using
      (Finset.sum_add_distrib (s := (Finset.univ : Finset α)) (f := u) (g := v))
  · intro c u
    -- `∑ (c • u) = c • ∑ u`.
    simpa [Pi.smul_apply, smul_eq_mul] using
      (Finset.mul_sum (s := (Finset.univ : Finset α)) (a := c) (f := u)).symm

/-- Tangent space to the simplex, modeled as the sum-zero submodule of `α → ℝ`. -/
noncomputable abbrev tangentSpace (α : Type*) [Fintype α] : Submodule ℝ (α → ℝ) :=
  LinearMap.ker (sumLinearMap α)

namespace tangentSpace

variable (α)

lemma mem_iff {u : α → ℝ} :
    u ∈ tangentSpace (α := α) ↔ (∑ a, u a) = 0 := by
  simp [tangentSpace, sumLinearMap]

end tangentSpace

/-- The Fisher bilinear form on the simplex tangent space:
`⟪u,v⟫_p = ∑ a, u a * v a / p a`. -/
noncomputable def fisherBilin (p : Simplex α) : LinearMap.BilinForm ℝ (tangentSpace (α := α)) := by
  classical
  refine LinearMap.mk₂ ℝ
    (fun u v => ∑ a, ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a) ?_ ?_ ?_ ?_
  · intro u₁ u₂ v
    -- Additivity in the first argument.
    simp [add_mul, add_div, Finset.sum_add_distrib]
  · intro c u v
    -- Homogeneity in the first argument.
    -- Factor `c` out of the finite sum.
    simpa [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
      (Finset.mul_sum (s := (Finset.univ : Finset α)) (a := c)
        (f := fun a => ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a)).symm
  · intro u v₁ v₂
    -- Additivity in the second argument.
    simp [mul_add, add_div, Finset.sum_add_distrib]
  · intro c u v
    -- Homogeneity in the second argument.
    simpa [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
      (Finset.mul_sum (s := (Finset.univ : Finset α)) (a := c)
        (f := fun a => ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a)).symm

namespace fisherBilin

variable (p : Simplex α)

@[simp] lemma apply (u v : tangentSpace (α := α)) :
    fisherBilin p u v = ∑ a, ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a := by
  rfl

lemma comm (u v : tangentSpace (α := α)) :
    fisherBilin p u v = fisherBilin p v u := by
  classical
  simp [fisherBilin.apply, mul_comm]

lemma pos (u : tangentSpace (α := α)) (hu : u ≠ 0) :
    0 < fisherBilin p u u := by
  classical
  -- Pick an index where `u` is nonzero.
  have hu_fun : (u : α → ℝ) ≠ (0 : α → ℝ) := by
    simp_all
  have h_not_forall : ¬ ∀ a : α, ((u : α → ℝ) a) = 0 := by
    intro hforall
    apply hu_fun
    funext a
    exact hforall a
  obtain ⟨a0, ha0⟩ : ∃ a0 : α, ((u : α → ℝ) a0) ≠ 0 :=
    (Classical.not_forall).1 h_not_forall
  have hterm_pos : 0 < (((u : α → ℝ) a0) * ((u : α → ℝ) a0)) / p.p a0 := by
    -- `(u a0)^2 / p a0` is positive since `u a0 ≠ 0` and `p a0 > 0`.
    have : 0 < ((u : α → ℝ) a0) * ((u : α → ℝ) a0) := mul_self_pos.2 ha0
    have hp_pos : 0 < p.p a0 := p.pos a0
    -- `x / y = x * (1/y)`.
    simpa [div_eq_mul_inv, mul_assoc] using mul_pos this (inv_pos.2 hp_pos)
  -- All terms are nonnegative, and the `a0` term is positive.
  have h_nonneg : ∀ a : α, 0 ≤ (((u : α → ℝ) a) * ((u : α → ℝ) a)) / p.p a := by
    intro a
    have hp_pos : 0 < p.p a := p.pos a
    have : 0 ≤ ((u : α → ℝ) a) * ((u : α → ℝ) a) := mul_self_nonneg ((u : α → ℝ) a)
    -- divide by a positive number
    exact div_nonneg this (le_of_lt hp_pos)
  -- Use `Finset.sum_pos'` on `Finset.univ`.
  have : 0 < ∑ a : α, (((u : α → ℝ) a) * ((u : α → ℝ) a)) / p.p a := by
    -- Convert `Fintype`-sum to `Finset`-sum and apply positivity.
    simpa using
      (Finset.sum_pos' (s := (Finset.univ : Finset α))
        (f := fun a => (((u : α → ℝ) a) * ((u : α → ℝ) a)) / p.p a)
        (h := fun a _ => h_nonneg a)
        (hs := ⟨a0, by simp, hterm_pos⟩))
  simpa [fisherBilin.apply] using this

end fisherBilin
end LeanPool.CencovPetz
