/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

/-! Walsh sign families. -/

open scoped BigOperators
open Finset

noncomputable section

namespace NonMRR

/-- The sum of the first `j` coordinates of a finite real vector. -/
def vectorPrefix {L : ℕ} (v : Fin L → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ univ.filter (fun i : Fin L => i.val < j), v i

private def sign (b : Bool) : ℝ := if b then 1 else -1

private lemma sign_sq (b : Bool) : sign b ^ 2 = 1 := by cases b <;> norm_num [sign]
private lemma sign_not (b : Bool) : sign (!b) = - sign b := by cases b <;> norm_num [sign]

private def flipCoord {m : ℕ} (k : Fin m) : (Fin m → Bool) ≃ (Fin m → Bool) :=
  Function.Involutive.toPerm (fun x => Function.update x k (!(x k))) (by
    intro x
    ext l
    by_cases h : l = k
    · subst l; simp
    · simp [Function.update_of_ne h])

private lemma sign_sum_zero {m : ℕ} (k : Fin m) :
    ∑ x : Fin m → Bool, sign (x k) = 0 := by
  have h := (flipCoord k).sum_comp (fun x : Fin m → Bool => sign (x k))
  have hf : ∀ x, sign ((flipCoord k x) k) = - sign (x k) := by
    intro x
    simp [flipCoord, Function.Involutive.toPerm, sign_not]
  simp_rw [hf, sum_neg_distrib] at h
  linarith

private lemma sign_pair_sum_zero {m : ℕ} {k l : Fin m} (hkl : k ≠ l) :
    ∑ x : Fin m → Bool, sign (x k) * sign (x l) = 0 := by
  have h := (flipCoord k).sum_comp (fun x : Fin m → Bool => sign (x k) * sign (x l))
  have hf : ∀ x, sign ((flipCoord k x) k) * sign ((flipCoord k x) l) =
      -(sign (x k) * sign (x l)) := by
    intro x
    simp [flipCoord, Function.Involutive.toPerm, sign_not, Function.update_of_ne hkl.symm]
  simp_rw [hf, sum_neg_distrib] at h
  linarith

private def cubeSize (m : ℕ) : ℕ := Fintype.card (Fin m → Bool)

private lemma cubeSize_pos (m : ℕ) : 0 < cubeSize m := Fintype.card_pos

private def character {m : ℕ} (k : Fin m) : EuclideanSpace ℝ (Fin m → Bool) :=
  WithLp.toLp 2 (fun x => sign (x k) / Real.sqrt (cubeSize m))

private lemma character_orthonormal (m : ℕ) :
    Orthonormal ℝ (character (m := m)) := by
  classical
  have hL : (0 : ℝ) < cubeSize m := by exact_mod_cast cubeSize_pos m
  rw [orthonormal_iff_ite]
  intro k l
  simp only [PiLp.inner_apply, character, RCLike.inner_apply,
    conj_trivial]
  simp_rw [div_mul_div_comm]
  rw [← sum_div]
  by_cases h : k = l
  · subst l
    simp_rw [← pow_two, sign_sq]
    simp [cubeSize]
  · rw [sign_pair_sum_zero (Ne.symm h)]
    simp [h]

private def cubeVector {m : ℕ} (k : Fin m) (x : Fin m → Bool) : ℝ :=
  sign (x k) / cubeSize m

private lemma cubeVector_subset_sq_le (m : ℕ) (s : Finset (Fin m → Bool)) :
    ∑ k : Fin m, (∑ x ∈ s, cubeVector k x) ^ 2 ≤ 1 := by
  classical
  have hL : (0 : ℝ) < cubeSize m := by exact_mod_cast cubeSize_pos m
  have hs : Real.sqrt (cubeSize m) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hL)
  let b : EuclideanSpace ℝ (Fin m → Bool) := WithLp.toLp 2
    (fun x => if x ∈ s then 1 / Real.sqrt (cubeSize m) else 0)
  have hb (k : Fin m) : inner ℝ (character k) b = ∑ x ∈ s, cubeVector k x := by
    simp only [PiLp.inner_apply, character, b, RCLike.inner_apply,
      conj_trivial]
    simp_rw [ite_mul, zero_mul, div_mul_div_comm, one_mul,
      ← pow_two, Real.sq_sqrt hL.le]
    simp [cubeVector, sum_ite_mem]
  have hn : ‖b‖ ^ 2 ≤ 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [b, ite_pow, zero_pow (by decide : 2 ≠ 0),
      div_pow, one_pow, Real.sq_sqrt hL.le]
    simp only [sum_ite_mem, sum_const, nsmul_eq_mul]
    simp only [univ_inter, mul_one_div]
    rw [div_le_one hL]
    exact_mod_cast (card_le_card (subset_univ s))
  have h := (character_orthonormal m).sum_inner_products_le (s := univ) b
  simp_rw [hb, Real.norm_eq_abs, sq_abs] at h
  exact h.trans hn

/-- Walsh sign vectors are balanced and satisfy Bessel's bound on every subset
of coordinates. The length is the cardinality of the Boolean cube. -/
theorem exists_walsh_subset_vectors (m : ℕ) :
    ∃ L : ℕ, 0 < L ∧ ∃ v : Fin m → Fin L → ℝ,
      (∀ k, ∑ i, v k i = 0) ∧
      (∀ k i, |v k i| = 1 / (L : ℝ)) ∧
      (∀ s : Finset (Fin L), ∑ k, (∑ i ∈ s, v k i) ^ 2 ≤ 1) := by
  classical
  let e : Fin (cubeSize m) ≃ (Fin m → Bool) := (Fintype.equivFin _).symm
  let v : Fin m → Fin (cubeSize m) → ℝ := fun k i => cubeVector k (e i)
  refine ⟨cubeSize m, cubeSize_pos m, v, ?_, ?_, ?_⟩
  · intro k
    change ∑ i, cubeVector k (e i) = 0
    rw [e.sum_comp]
    simp [cubeVector, ← sum_div, sign_sum_zero]
  · intro k i
    have habs : |sign ((e i) k)| = 1 := by cases (e i) k <;> norm_num [sign]
    simp [v, cubeVector, abs_div, habs]
  · intro s
    have h := cubeVector_subset_sq_le m (s.image e)
    simpa only [sum_image (fun _ _ _ _ h => e.injective h), v] using h

/-- The Walsh vectors satisfy the prefix-square estimate in every ordering. -/
theorem exists_walsh_vectors (m : ℕ) :
    ∃ L : ℕ, 0 < L ∧ ∃ v : Fin m → Fin L → ℝ,
      (∀ k, ∑ i, v k i = 0) ∧
      (∀ k i, |v k i| = 1 / (L : ℝ)) ∧
      (∀ (σ : Equiv.Perm (Fin L)) (j : ℕ),
        ∑ k, (vectorPrefix (v k ∘ σ) j) ^ 2 ≤ 1) := by
  classical
  obtain ⟨L, hL, v, hv0, hvabs, hvsubset⟩ := exists_walsh_subset_vectors m
  refine ⟨L, hL, v, hv0, hvabs, ?_⟩
  intro σ j
  have h := hvsubset ((univ.filter (fun i : Fin L => i.val < j)).image σ)
  simpa only [sum_image (fun _ _ _ _ h => σ.injective h), vectorPrefix,
    Function.comp_apply] using h

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
