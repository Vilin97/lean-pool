/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic

/-!
# Diameter shrinking for iterated barycentric subdivision

This file proves the geometric *metric shrinking* facts for affine barycentric
subdivision of the standard topological simplex `Δⁿ` and its iterates. These are
the metric inputs needed by the later small-simplices theorem.

The mathematical content is the classical estimate: one barycentric subdivision
of a simplex contracts diameters by the factor `n/(n+1) < 1`, and therefore the
`N`-fold subdivision contracts by `(n/(n+1))^N → 0`.

## Design

Rather than route through the singular-chain subdivision operator, we work
directly with the affine layer. A simplex is described by its tuple of `n+1`
vertices `V : Fin (n+1) → E` in a real normed space `E`. One barycentric
subdivision step, for a permutation `π` of the vertices, produces the new vertex
tuple

```text
(stepVertices V π) k = barycenter {V (π 0), …, V (π k)}
 = (k+1)⁻¹ • Σ_{j ≤ k} V (π j).
```

The geometric simplex is the convex hull of the vertex tuple, and
`Metric.diam (convexHull ℝ (Set.range V)) = Metric.diam (Set.range V)`
(`convexHull_diam`), so it suffices to bound `Metric.diam (Set.range V)`.

## Main results

* `contractionFactor n = n/(n+1)`, with `contractionFactor_nonneg` and
 `contractionFactor_lt_one`.
* `stepVertices_diam_le` — one-step contraction:
 `diam (range (stepVertices V π)) ≤ contractionFactor n * diam (range V)`.
* `iterVertices` — the vertex tuple of an affine sub-simplex of `sdᴺ`.
* `iterVertices_diam_le` — `diam (range (iterVertices …)) ≤ (contractionFactor n)^N * diam
  (range V)`.
* `exists_iteratedSubdivision_affine_diameter_lt` — for every `ε > 0` there is `N`
 such that *every* affine sub-simplex appearing in the `N`-fold barycentric
 subdivision of `Δⁿ` has diameter `< ε`.
-/

@[expose] public section

open scoped BigOperators
open Finset Metric

namespace SphereOddDegree
namespace BarycentricSubdivisionDiameter

/-! ## The contraction factor -/

/-- The dimension-dependent contraction factor `n/(n+1)`. It is `< 1` for every
`n` (in particular `0` for `n = 0`). -/
noncomputable def contractionFactor (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

theorem contractionFactor_nonneg (n : ℕ) : 0 ≤ contractionFactor n := by
  unfold contractionFactor
  positivity

theorem contractionFactor_lt_one (n : ℕ) : contractionFactor n < 1 := by
  unfold contractionFactor
  rw [div_lt_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-
Monotonicity helper: `l/(l+1) ≤ n/(n+1)` whenever `l ≤ n`.
-/
theorem ratio_le_contractionFactor {l n : ℕ} (h : l ≤ n) :
    (l : ℝ) / (l + 1) ≤ contractionFactor n := by
  rw [ contractionFactor, div_le_div_iff₀ ] <;> norm_cast <;> nlinarith

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## One barycentric subdivision step on a vertex tuple -/

/-- One barycentric subdivision step applied to a vertex tuple `V`, ordered by the
permutation `π`. The `k`-th new vertex is the barycenter of the first `k+1`
old vertices in the order `π`. -/
noncomputable def stepVertices (n : ℕ) (V : Fin (n + 1) → E)
    (π : Equiv.Perm (Fin (n + 1))) : Fin (n + 1) → E :=
  fun k => ((k.val + 1 : ℝ))⁻¹ • ∑ j ∈ Finset.Iic k, V (π j)

omit [NormedSpace ℝ E] in
/-- The range of any vertex tuple over `Fin (n+1)` is bounded. -/
theorem isBounded_range (n : ℕ) (V : Fin (n + 1) → E) :
    Bornology.IsBounded (Set.range V) :=
  (Set.finite_range V).isBounded

theorem dist_vertex_step_le (n : ℕ) (V : Fin (n + 1) → E)
    (π : Equiv.Perm (Fin (n + 1))) (l i : Fin (n + 1)) (hi : i ≤ l) :
    dist (V (π i)) (stepVertices n V π l)
      ≤ (l.val : ℝ) / (l.val + 1) * Metric.diam (Set.range V) := by
  have h_step : V (π i) - (stepVertices n V π l) = (l.val + 1 : ℝ)⁻¹ • ∑ j ∈ Finset.Iic l, (V (π
    i) - V (π j)) := by
    simp? [stepVertices]
    simp [smul_sub, ← Nat.cast_smul_eq_nsmul ℝ]
    rw [inv_smul_smul₀ (Nat.cast_add_one_ne_zero _)]
  have h_norm : ‖∑ j ∈ Finset.Iic l, (V (π i) - V (π j))‖ ≤ l.val * Metric.diam (Set.range V) := by
    have h_bound : ∀ j ∈ (Finset.Iic l).erase i, ‖V (π i) - V (π j)‖ ≤ Metric.diam (Set.range V)
      := by
      intro j _
      rw [← dist_eq_norm]
      exact Metric.dist_le_diam_of_mem (isBounded_range n V) (Set.mem_range_self (π i))
        (Set.mem_range_self (π j))
    have h_sum := norm_sum_le (Finset.Iic l) (fun j => V (π i) - V (π j))
    have h_zero : ‖V (π i) - V (π i)‖ = 0 := by simp
    have h_split : ∑ j ∈ Finset.Iic l, ‖V (π i) - V (π j)‖ = ∑ j ∈ (Finset.Iic l).erase i, ‖V (π
      i) - V (π j)‖ := by
      rw [← Finset.sum_erase (Finset.Iic l) h_zero]
    have h_card : ((Finset.Iic l).erase i).card = l.val := by
      rw [Finset.card_erase_of_mem (Finset.mem_Iic.mpr hi), Fin.card_Iic, Nat.add_sub_cancel]
    have h_sum_le : ∑ j ∈ (Finset.Iic l).erase i, ‖V (π i) - V (π j)‖ ≤ l.val * Metric.diam
      (Set.range V) := by
      have := Finset.sum_le_card_nsmul ((Finset.Iic l).erase i) (fun j => ‖V (π i) - V (π j)‖)
        (Metric.diam (Set.range V)) (fun j hj => h_bound j hj)
      rwa [h_card, nsmul_eq_mul] at this
    linarith
  rw [dist_eq_norm, h_step, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hl_pos : 0 ≤ (l.val + 1 : ℝ)⁻¹ := by positivity
  have h_le := mul_le_mul_of_nonneg_left h_norm hl_pos
  have h_eq : (l.val + 1 : ℝ)⁻¹ * (l.val * Metric.diam (Set.range V)) = (l.val : ℝ) / (l.val +
    1) * Metric.diam (Set.range V) := by
    ring
  linarith

theorem dist_step_step_le_aux (n : ℕ) (V : Fin (n + 1) → E)
    (π : Equiv.Perm (Fin (n + 1))) (l l' : Fin (n + 1)) (hll : l ≤ l') :
    dist (stepVertices n V π l) (stepVertices n V π l')
      ≤ (l'.val : ℝ) / (l'.val + 1) * Metric.diam (Set.range V) := by
  set D := Metric.diam (Set.range V)
  set s := Finset.Iic l
  have hs : s.card = l.val + 1 := by
    simp [s]
  have h_step : stepVertices n V π l - stepVertices n V π l' = (l.val + 1 : ℝ)⁻¹ • ∑ i ∈ s, (V
    (π i) - stepVertices n V π l') := by
    rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, hs, ← Nat.cast_smul_eq_nsmul ℝ,
      Nat.cast_add, Nat.cast_one, inv_smul_smul₀ (by positivity : (l.val : ℝ) + 1 ≠ 0)]
    rfl
  have h_dist : ∀ i ∈ s, ‖V (π i) - stepVertices n V π l'‖ ≤ (l'.val : ℝ) / (l'.val + 1) * D := by
    intro i hi
    have := dist_vertex_step_le n V π l' i (le_trans (Finset.mem_Iic.mp hi) hll)
    simpa [dist_eq_norm] using this
  rw [dist_eq_norm, h_step, norm_smul, Real.norm_of_nonneg (by positivity)]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)) ?_
  have h_sum_le := mul_le_mul_of_nonneg_left (Finset.sum_le_sum h_dist) (by
    positivity : 0 ≤ (l.val + 1 : ℝ)⁻¹)
  refine le_trans h_sum_le ?_
  simp only [Finset.sum_const, nsmul_eq_mul, hs]
  push_cast
  have : (l.val + 1 : ℝ) ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ this, one_mul]

theorem dist_step_step_le (n : ℕ) (V : Fin (n + 1) → E)
    (π : Equiv.Perm (Fin (n + 1))) (l l' : Fin (n + 1)) :
    dist (stepVertices n V π l) (stepVertices n V π l')
      ≤ contractionFactor n * Metric.diam (Set.range V) := by
  by_cases h : l ≤ l'
  · refine le_trans (dist_step_step_le_aux _ _ _ _ _ h) ?_
    exact mul_le_mul_of_nonneg_right (ratio_le_contractionFactor (Nat.le_of_lt_succ (Fin.is_lt
      l'))) (Metric.diam_nonneg)
  · rw [dist_comm]
    have h' : l' ≤ l := le_of_not_ge h
    refine le_trans (dist_step_step_le_aux n V π l' l h') ?_
    exact mul_le_mul_of_nonneg_right (ratio_le_contractionFactor (Nat.le_of_lt_succ l.isLt))
      Metric.diam_nonneg

theorem stepVertices_diam_le (n : ℕ) (V : Fin (n + 1) → E)
    (π : Equiv.Perm (Fin (n + 1))) :
    Metric.diam (Set.range (stepVertices n V π))
      ≤ contractionFactor n * Metric.diam (Set.range V) := by
  refine Metric.diam_le_of_forall_dist_le
    (mul_nonneg (contractionFactor_nonneg n) (Metric.diam_nonneg)) ?_
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact dist_step_step_le n V π a b

/-- Iterate barycentric subdivision of a vertex family along a permutation word. -/
noncomputable def iterVertices (n : ℕ) : (N : ℕ) → (Fin N → Equiv.Perm (Fin (n + 1))) →
    (Fin (n + 1) → E) → (Fin (n + 1) → E)
  | 0, _, V => V
  | N + 1, πs, V =>
      stepVertices n (iterVertices n N (fun i => πs i.castSucc) V) (πs (Fin.last N))

@[simp] theorem iterVertices_zero (n : ℕ)
    (πs : Fin 0 → Equiv.Perm (Fin (n + 1))) (V : Fin (n + 1) → E) :
    iterVertices n 0 πs V = V := rfl

theorem iterVertices_succ (n N : ℕ)
    (πs : Fin (N + 1) → Equiv.Perm (Fin (n + 1))) (V : Fin (n + 1) → E) :
    iterVertices n (N + 1) πs V
      = stepVertices n (iterVertices n N (fun i => πs i.castSucc) V) (πs (Fin.last N)) :=
  rfl

theorem iterVertices_diam_le (n N : ℕ)
    (πs : Fin N → Equiv.Perm (Fin (n + 1))) (V : Fin (n + 1) → E) :
    Metric.diam (Set.range (iterVertices n N πs V))
      ≤ (contractionFactor n) ^ N * Metric.diam (Set.range V) := by
  induction N with
  | zero =>
    simp [iterVertices]
  | succ N ih =>
    rw [iterVertices_succ]
    refine le_trans (stepVertices_diam_le n (iterVertices n N (fun i => πs i.castSucc) V) (πs
      (Fin.last N))) ?_
    have h_ih := ih (fun i => πs i.castSucc)
    have h_mul := mul_le_mul_of_nonneg_left h_ih (contractionFactor_nonneg n)
    rw [pow_succ', mul_assoc]
    exact h_mul

end Normed

/-! ## The standard simplex and the main existence theorem -/

/-- The tuple of `n+1` standard basis vertices of `Δⁿ`, as points of
`Fin (n+1) → ℝ`. -/
noncomputable def stdVerts (n : ℕ) : Fin (n + 1) → (Fin (n + 1) → ℝ) :=
  fun k => Pi.single k 1

/-
The standard vertex set has diameter at most `1`.
-/
theorem diam_range_stdVerts_le_one (n : ℕ) :
    Metric.diam (Set.range (stdVerts n)) ≤ 1 := by
  apply Metric.diam_le_of_forall_dist_le zero_le_one
  rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
  apply (dist_pi_le_iff zero_le_one).2
  intro k
  simp only [stdVerts, Pi.single_apply, Real.dist_eq]
  split_ifs <;> norm_num

/-
**Main theorem.** For every `ε > 0` there is a number `N` of barycentric
subdivisions such that *every* affine sub-simplex appearing in the `N`-fold
barycentric subdivision of `Δⁿ` — i.e. for every choice of the `N` permutations
`πs` — has vertex-set diameter `< ε`.
-/
theorem exists_iteratedSubdivision_affine_diameter_lt (n : ℕ) (eps : ℝ)
    (heps : 0 < eps) :
    ∃ N : ℕ, ∀ (πs : Fin N → Equiv.Perm (Fin (n + 1))),
      Metric.diam (Set.range (iterVertices n N πs (stdVerts n))) < eps := by
  have := exists_pow_lt_of_lt_one heps ( contractionFactor_lt_one n );
  exact ⟨ this.choose, fun πs => lt_of_le_of_lt ( iterVertices_diam_le n _ _ _ ) (
    lt_of_le_of_lt ( mul_le_of_le_one_right ( pow_nonneg ( contractionFactor_nonneg n ) _ ) (
    diam_range_stdVerts_le_one n ) ) this.choose_spec ) ⟩

/-- Convex-hull form of the theorem: the *geometric* affine sub-simplex (the
convex hull of the vertex tuple) has diameter `< ε` after enough subdivisions. -/
theorem exists_iteratedSubdivision_affine_convexHull_diameter_lt (n : ℕ) (eps : ℝ)
    (heps : 0 < eps) :
    ∃ N : ℕ, ∀ (πs : Fin N → Equiv.Perm (Fin (n + 1))),
      Metric.diam (convexHull ℝ (Set.range (iterVertices n N πs (stdVerts n)))) < eps := by
  obtain ⟨N, hN⟩ := exists_iteratedSubdivision_affine_diameter_lt n eps heps
  exact ⟨N, fun πs => by rw [convexHull_diam]; exact hN πs⟩

end BarycentricSubdivisionDiameter
end SphereOddDegree
