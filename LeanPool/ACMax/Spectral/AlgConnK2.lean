/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import LeanPool.ACMax.Spectral.AlgConn
import LeanPool.ACMax.Spectral.RayleighUpper
import LeanPool.ACMax.Spectral.RayleighLower

/-!
# Algebraic connectivity of `K_{2,n-2}` equals `2`

`algConn_completeBipartite_two`: the equality clause of the ACMAX conjecture.
The Laplacian spectrum of `K_{2,n-2}` is `0, 2^(n-3), (n-2), n`, so its
second-smallest eigenvalue is `2`.
-/

namespace ACMax

open Classical in
theorem algConn_completeBipartite_two (n : ℕ) (hn : 4 ≤ n) :
    algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 := by
  classical
  set m := n - 2 with hm
  let : DecidableEq (Fin 2 ⊕ Fin m) := fun a b => Classical.propDecidable (a = b)
  have : Nontrivial (Fin 2 ⊕ Fin m) := ⟨Sum.inl 0, Sum.inl 1, by simp⟩
  set G : SimpleGraph (Fin 2 ⊕ Fin m) := completeBipartiteGraph (Fin 2) (Fin m) with hG
  -- adjacency description
  have hadj : ∀ i j : Fin 2 ⊕ Fin m, G.Adj i j ↔
      (i.isLeft ∧ j.isRight) ∨ (i.isRight ∧ j.isLeft) := by
    intro i j; rw [hG]; rfl
  -- splitting lemmas over the sum type
  have hsplit : ∀ y : Fin 2 ⊕ Fin m → ℝ,
      ∑ w, y w = y (Sum.inl 0) + y (Sum.inl 1) + ∑ k : Fin m, y (Sum.inr k) := by
    intro y; rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  have hsq : ∀ y : Fin 2 ⊕ Fin m → ℝ,
      ∑ w, (y w) ^ 2
        = (y (Sum.inl 0)) ^ 2 + (y (Sum.inl 1)) ^ 2 + ∑ k : Fin m, (y (Sum.inr k)) ^ 2 := by
    intro y; rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  -- the Laplacian quadratic form as a clean leaf sum
  have hQ : ∀ y : Fin 2 ⊕ Fin m → ℝ,
      dotProduct y ((G.lapMatrix ℝ).mulVec y)
        = ∑ k : Fin m,
            ((y (Sum.inl 0) - y (Sum.inr k)) ^ 2 + (y (Sum.inl 1) - y (Sum.inr k)) ^ 2) := by
    intro y
    rw [← Matrix.toLinearMap₂'_apply' (G.lapMatrix ℝ) y y, SimpleGraph.lapMatrix_toLinearMap₂']
    simp only [hadj, Fintype.sum_sum_type, Fin.sum_univ_two, Sum.isLeft_inl, Sum.isRight_inl,
      Sum.isLeft_inr, Sum.isRight_inr, Bool.false_eq_true, and_true, and_false, or_false,
      false_or, ite_true, ite_false, Finset.sum_const_zero, add_zero, zero_add]
    rw [div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  -- ===== Upper bound: algConn ≤ 2 =====
  have hupper : algConn G ≤ 2 := by
    have hm0 : 0 < m := by omega
    have hm1 : 1 < m := by omega
    set i0 : Fin m := ⟨0, hm0⟩ with hi0
    set i1 : Fin m := ⟨1, hm1⟩ with hi1
    have hne : i0 ≠ i1 := by
      rw [hi0, hi1]; intro h; exact absurd (Fin.mk.inj_iff.mp h) (by norm_num)
    set g : Fin m → ℝ := fun k => (if k = i0 then (1 : ℝ) else 0) - (if k = i1 then 1 else 0)
      with hgdef
    set x : Fin 2 ⊕ Fin m → ℝ := Sum.elim (fun _ => (0 : ℝ)) g with hxdef
    -- ∑ g = 0
    have hg_sum : ∑ k : Fin m, g k = 0 := by
      simp only [hgdef, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    have hg_i0 : g i0 = 1 := by
      simp [hgdef, hne]
    have hS2pos : 0 < ∑ k : Fin m, (g k) ^ 2 := by
      apply Finset.sum_pos' (fun k _ => sq_nonneg _)
      exact ⟨i0, Finset.mem_univ _, by rw [hg_i0]; norm_num⟩
    -- ∑ x = 0
    have hx0 : ∑ w, x w = 0 := by
      rw [hsplit x, hxdef]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hg_sum]; ring
    -- ∑ x² = S2
    have hsumsq : ∑ w, (x w) ^ 2 = ∑ k : Fin m, (g k) ^ 2 := by
      rw [hsq x, hxdef]
      simp only [Sum.elim_inl, Sum.elim_inr]
      ring
    -- Q x = 2 * S2
    have hQval : (∑ k : Fin m,
        ((x (Sum.inl 0) - x (Sum.inr k)) ^ 2 + (x (Sum.inl 1) - x (Sum.inr k)) ^ 2))
        = 2 * ∑ k : Fin m, (g k) ^ 2 := by
      rw [hxdef]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _; ring
    have key := algConn_mul_sq_le G x hx0
    have hbound : algConn G * (∑ i, x i ^ 2) ≤ 2 * ∑ k : Fin m, (g k) ^ 2 :=
      calc algConn G * (∑ i, x i ^ 2)
          ≤ dotProduct x ((G.lapMatrix ℝ).mulVec x) := key
        _ = 2 * ∑ k : Fin m, (g k) ^ 2 := by rw [hQ x, hQval]
    rw [hsumsq] at hbound
    exact le_of_mul_le_mul_right hbound hS2pos
  -- ===== Lower bound: 2 ≤ algConn =====
  have hlower : 2 ≤ algConn G := by
    apply le_algConn_of_forall G 2
    intro x hx0
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by
      have h2m : 2 ≤ m := by omega
      exact_mod_cast h2m
    -- constraint from orthogonality to the all-ones vector
    have hsum : x (Sum.inl 0) + x (Sum.inl 1) + ∑ k : Fin m, x (Sum.inr k) = 0 := by
      rw [← hsplit x]; exact hx0
    -- expansion of a shifted sum of squares
    have e1 : ∀ t : ℝ, ∑ k : Fin m, (t - x (Sum.inr k)) ^ 2
        = (m : ℝ) * t ^ 2 - 2 * t * (∑ k : Fin m, x (Sum.inr k))
          + ∑ k : Fin m, (x (Sum.inr k)) ^ 2 := by
      intro t
      have hterm : ∀ k : Fin m,
          (t - x (Sum.inr k)) ^ 2 = t ^ 2 - 2 * t * (x (Sum.inr k)) + (x (Sum.inr k)) ^ 2 :=
        fun k => by ring
      simp only [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    have hQval : (∑ k : Fin m,
        ((x (Sum.inl 0) - x (Sum.inr k)) ^ 2 + (x (Sum.inl 1) - x (Sum.inr k)) ^ 2))
        = (m : ℝ) * ((x (Sum.inl 0)) ^ 2 + (x (Sum.inl 1)) ^ 2)
          - 2 * ((x (Sum.inl 0)) + (x (Sum.inl 1))) * (∑ k : Fin m, x (Sum.inr k))
          + 2 * (∑ k : Fin m, (x (Sum.inr k)) ^ 2) := by
      rw [Finset.sum_add_distrib, e1 (x (Sum.inl 0)), e1 (x (Sum.inl 1))]; ring
    have hSc : (∑ k : Fin m, x (Sum.inr k)) = -((x (Sum.inl 0)) + (x (Sum.inl 1))) := by
      linarith
    rw [hsq x]
    calc 2 * ((x (Sum.inl 0)) ^ 2 + (x (Sum.inl 1)) ^ 2 + ∑ k : Fin m, (x (Sum.inr k)) ^ 2)
        ≤ ∑ k : Fin m,
            ((x (Sum.inl 0) - x (Sum.inr k)) ^ 2 + (x (Sum.inl 1) - x (Sum.inr k)) ^ 2) := by
          rw [hQval, hSc]
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 2)
            (add_nonneg (sq_nonneg (x (Sum.inl 0))) (sq_nonneg (x (Sum.inl 1)))),
            sq_nonneg ((x (Sum.inl 0)) + (x (Sum.inl 1)))]
      _ = dotProduct x ((G.lapMatrix ℝ).mulVec x) := (hQ x).symm
  exact le_antisymm hupper hlower

end ACMax
