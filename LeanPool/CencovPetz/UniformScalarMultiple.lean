/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.PermutationInvariantBilinForm


/-!
# `CencovPetz.UniformScalarMultiple`

At the uniform point on a finite simplex, a monotone metric family's bilinear form is a scalar
multiple of the Fisher bilinear form.

This is an algebraic step in the finite Čencov/Chentsov uniqueness proof: permutation invariance
plus the `dij` relations imply that (at the uniform point) the metric is determined by a single
scalar.
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

namespace TangentFin

namespace Bilin

open _root_.LeanPool.CencovPetz.TangentFin.Basis

variable {n : ℕ} (G : MonotoneMetricFamily) [Nonempty (Fin n)]

omit [Nonempty (Fin n)] in
private lemma sum_smul_dij_eq (u : V n) (i0 : Fin n) :
    (∑ i : Fin n, ((u : Fin n → ℝ) i) • dij (n := n) i i0) = u := by
  classical
  ext k
  have hu_sum : (∑ i : Fin n, (u : Fin n → ℝ) i) = 0 :=
    (tangentSpace.mem_iff (α := Fin n) (u := (u : Fin n → ℝ))).1 u.property
  have h_pick :
      (∑ i : Fin n, (u : Fin n → ℝ) i * e (n := n) i k) = (u : Fin n → ℝ) k := by
    have :
        (∑ i : Fin n, (u : Fin n → ℝ) i * e (n := n) i k) =
          (u : Fin n → ℝ) k * e (n := n) k k := by
      refine
        (Fintype.sum_eq_single k
          (f := fun i : Fin n => (u : Fin n → ℝ) i * e (n := n) i k) ?_)
      intro i hi
      have hk : k ≠ i := by simpa [eq_comm] using hi
      have : e (n := n) i k = 0 := by
        simp [e, Pi.single_eq_of_ne hk]
      simp [this]
    simpa [e] using this
  have h_const :
      (∑ i : Fin n, (u : Fin n → ℝ) i * e (n := n) i0 k) =
        (∑ i : Fin n, (u : Fin n → ℝ) i) * e (n := n) i0 k := by
    simpa using
      (Finset.sum_mul (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => (u : Fin n → ℝ) i) (a := e (n := n) i0 k)).symm
  have h :
      (∑ i : Fin n, (u : Fin n → ℝ) i * (e (n := n) i k - e (n := n) i0 k))
        = (u : Fin n → ℝ) k := by
    calc
      (∑ i : Fin n, (u : Fin n → ℝ) i * (e (n := n) i k - e (n := n) i0 k))
          = (∑ i : Fin n, (u : Fin n → ℝ) i * e (n := n) i k)
              - (∑ i : Fin n, (u : Fin n → ℝ) i * e (n := n) i0 k) := by
                simp [sub_eq_add_neg, mul_add, Finset.sum_add_distrib]
      _ = (u : Fin n → ℝ) k - ((∑ i : Fin n, (u : Fin n → ℝ) i) * e (n := n) i0 k) := by
            simp [h_pick, h_const]
      _ = (u : Fin n → ℝ) k := by
            simp [hu_sum]
  simpa [Basis.dij_coe, sub_eq_add_neg, mul_add, Finset.sum_add_distrib] using h
private lemma B_sum_dij_eq (u : V n) (i0 : Fin n) :
    B (G := G) (n := n) u u =
      ∑ i : Fin n, ∑ j : Fin n,
        (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
          B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) := by
  classical
  have hu_repr : (∑ i : Fin n, ((u : Fin n → ℝ) i) • dij (n := n) i i0) = u :=
    sum_smul_dij_eq (n := n) (u := u) (i0 := i0)
  calc
    B (G := G) (n := n) u u =
        B (G := G) (n := n)
          (∑ i : Fin n, ((u : Fin n → ℝ) i) • dij (n := n) i i0)
          (∑ j : Fin n, ((u : Fin n → ℝ) j) • dij (n := n) j i0) := by
            simp [hu_repr]
    _ = ∑ i : Fin n, ∑ j : Fin n,
          ((u : Fin n → ℝ) i) * ((u : Fin n → ℝ) j) *
            B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) := by
              have h :
                  B (G := G) (n := n)
                      (∑ i : Fin n, ((u : Fin n → ℝ) i) • dij (n := n) i i0)
                      (∑ j : Fin n, ((u : Fin n → ℝ) j) • dij (n := n) j i0)
                    =
                    ∑ x : Fin n, ∑ i : Fin n,
                      ((u : Fin n → ℝ) x) *
                        (((u : Fin n → ℝ) i) *
                          B (G := G) (n := n) (dij (n := n) x i0) (dij (n := n) i i0)) := by
                simp [Finset.mul_sum, B_symm (G := G) (n := n)]
              have h' :
                  (∑ x : Fin n, ∑ i : Fin n,
                        ((u : Fin n → ℝ) x) *
                          (((u : Fin n → ℝ) i) *
                            B (G := G) (n := n) (dij (n := n) x i0) (dij (n := n) i i0)))
                    =
                    ∑ i : Fin n, ∑ j : Fin n,
                      ((u : Fin n → ℝ) i) * ((u : Fin n → ℝ) j) *
                        B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) := by
                calc
                  (∑ x : Fin n, ∑ i : Fin n,
                        ((u : Fin n → ℝ) x) *
                          (((u : Fin n → ℝ) i) *
                            B (G := G) (n := n) (dij (n := n) x i0) (dij (n := n) i i0)))
                      =
                      (∑ i : Fin n, ∑ x : Fin n,
                        ((u : Fin n → ℝ) x) *
                          (((u : Fin n → ℝ) i) *
                            B (G := G) (n := n)
                              (dij (n := n) x i0)
                              (dij (n := n) i i0))) := by
                        exact
                          (Finset.sum_comm :
                            (∑ x : Fin n, ∑ i : Fin n,
                              ((u : Fin n → ℝ) x) *
                                (((u : Fin n → ℝ) i) *
                                  B (G := G) (n := n)
                                    (dij (n := n) x i0)
                                    (dij (n := n) i i0)))
                              = _)
                  _ =
                      ∑ i : Fin n, ∑ j : Fin n,
                        ((u : Fin n → ℝ) i) * ((u : Fin n → ℝ) j) *
                          B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) := by
                        simp [mul_assoc, mul_left_comm, B_symm (G := G) (n := n)]
              exact h.trans h'

private lemma B_dij_anchor_self_eq (i0 i1 i : Fin n) (hi01 : i0 ≠ i1) (hi : i ≠ i0) :
    B (G := G) (n := n) (dij (n := n) i0 i) (dij (n := n) i0 i) =
      B (G := G) (n := n) (dij (n := n) i0 i1) (dij (n := n) i0 i1) := by
  classical
  by_cases hi1 : i = i1
  · simp_all
  · have hi0i : i0 ≠ i := by
      intro h
      exact hi h.symm
    have hperm :=
      B_dij_dij_eq_of_perm (G := G) (n := n) (σ := Equiv.swap i1 i)
        (i := i0) (j := i1) (k := i0) (l := i1)
    have hσi0 : (Equiv.swap i1 i) i0 = i0 := by
      simp [Equiv.swap_apply_of_ne_of_ne hi01 hi0i]
    simp_all

private lemma B_dij_i_i0_pair (i0 i1 : Fin n) (hi01 : i0 ≠ i1) (c : ℝ)
    (hc : c = B (G := G) (n := n) (dij (n := n) i0 i1) (dij (n := n) i0 i1)) :
    ∀ i j : Fin n,
      B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) =
        if i = i0 ∨ j = i0 then 0 else if i = j then c else (1 / 2 : ℝ) * c := by
  intro i j
  by_cases hi : i = i0
  · simp_all
  by_cases hj : j = i0
  · simp_all
  have hneg_i : dij (n := n) i i0 = -dij (n := n) i0 i := by
    simpa using (Basis.dij_neg (n := n) i i0)
  have hneg_j : dij (n := n) j i0 = -dij (n := n) i0 j := by
    simpa using (Basis.dij_neg (n := n) j i0)
  by_cases hij : i = j
  · subst hij
    have hself0 :
        B (G := G) (n := n) (dij (n := n) i0 i) (dij (n := n) i0 i) = c := by
      simpa [hc] using
        (B_dij_anchor_self_eq (G := G) (n := n) (i0 := i0) (i1 := i1) (i := i) hi01 hi)
    simp_all
  · have hi0i : i0 ≠ i := by
      intro h
      exact hi h.symm
    have hi0j : i0 ≠ j := by
      intro h
      exact hj h.symm
    have hij' : i ≠ j := hij
    have hhalf :
        B (G := G) (n := n) (dij (n := n) i0 i) (dij (n := n) i0 j)
          = (1 / 2 : ℝ) *
            B (G := G) (n := n) (dij (n := n) i0 i) (dij (n := n) i0 i) := by
      simpa using
        (B_dij_dij_eq_half_self (G := G) (n := n) (i := i0) (j := i) (k := j) hi0i hij' hi0j)
    have hself :
        B (G := G) (n := n) (dij (n := n) i0 i) (dij (n := n) i0 i) = c := by
      simpa [hc] using
        (B_dij_anchor_self_eq (G := G) (n := n) (i0 := i0) (i1 := i1) (i := i) hi01 hi)
    simp_all

private lemma B_double_sum_erase (u : V n) (i0 : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n,
        (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
          B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0))
      =
      ∑ i ∈ (Finset.univ : Finset (Fin n)).erase i0,
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i0,
          (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
            B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) := by
  simp_all

omit G [Nonempty (Fin n)] in
private lemma kernel_sum_expand (u : V n) (S : Finset (Fin n)) (c : ℝ) :
    (∑ i ∈ S, ∑ j ∈ S,
        (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
          (if i = j then c else (1 / 2 : ℝ) * c))
      =
      (c / 2) *
        (((∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j))
          + (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i)) := by
  have hsplit (i j : Fin n) :
      (if i = j then c else (1 / 2 : ℝ) * c) = (c / 2) + (if i = j then c / 2 else 0) := by
    by_cases h : i = j
    · simp_all
    · simp [h]
      ring
  have hsumSq_factor :
      (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i * (c / 2)) =
        (c / 2) * (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) := by
    have h :
        (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i * (c / 2)) =
          (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) * (c / 2) := by
      exact
        (Finset.sum_mul (s := S)
            (f := fun i : Fin n => (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) (a := c / 2)).symm
    calc
      (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i * (c / 2)) =
          (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) * (c / 2) := h
      _ = (c / 2) * (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) := by
            ring
  have hconst :
      (∑ i ∈ S, ∑ j ∈ S,
          (u : Fin n → ℝ) i * (u : Fin n → ℝ) j * (c / 2))
        =
        (c / 2) * ((∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j)) := by
    have hprod :
        (∑ i ∈ S, ∑ j ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) j) =
          (∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j) := by
      exact
        (Finset.sum_mul_sum (s := S) (t := S) (f := fun i : Fin n => (u : Fin n → ℝ) i)
            (g := fun j : Fin n => (u : Fin n → ℝ) j)).symm
    calc
      (∑ i ∈ S, ∑ j ∈ S,
          (u : Fin n → ℝ) i * (u : Fin n → ℝ) j * (c / 2))
          = (∑ i ∈ S, ∑ j ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) j) * (c / 2) := by
                simp [Finset.sum_mul, mul_assoc]
      _ = (c / 2) * (∑ i ∈ S, ∑ j ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) j) := by
                ring
      _ = (c / 2) * ((∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j)) := by
                rw [hprod]
  have hdiag :
      (∑ i ∈ S, ∑ j ∈ S,
          (u : Fin n → ℝ) i * (u : Fin n → ℝ) j * (if i = j then c / 2 else 0))
        =
        (c / 2) * (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) := by
    simp_all
  calc
    (∑ i ∈ S, ∑ j ∈ S,
        (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
          (if i = j then c else (1 / 2 : ℝ) * c))
        =
        ∑ i ∈ S, ∑ j ∈ S,
          (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
            ((c / 2) + (if i = j then c / 2 else 0)) := by
              simp_all
    _ =
        (∑ i ∈ S, ∑ j ∈ S,
            (u : Fin n → ℝ) i * (u : Fin n → ℝ) j * (c / 2))
          +
          (∑ i ∈ S, ∑ j ∈ S,
            (u : Fin n → ℝ) i * (u : Fin n → ℝ) j * (if i = j then c / 2 else 0)) := by
              simp [mul_add, Finset.sum_add_distrib]
    _ =
        (c / 2) * ((∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j))
          + (c / 2) * (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) := by
              simp_all
    _ =
        (c / 2) *
          (((∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j))
            + (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i)) := by
              ring

private lemma B_quadratic_dij_sum (i0 i1 : Fin n) (hi01 : i0 ≠ i1) (c : ℝ)
    (hc : c = B (G := G) (n := n) (dij (n := n) i0 i1) (dij (n := n) i0 i1))
    (u : V n) :
    B (G := G) (n := n) u u =
      (c / 2) * (∑ k : Fin n, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) := by
  classical
  have hB_sum := B_sum_dij_eq (G := G) (n := n) (u := u) (i0 := i0)
  have h_pair := B_dij_i_i0_pair (G := G) (n := n) (i0 := i0) (i1 := i1) hi01 c hc
  have hu_sum : (∑ i : Fin n, (u : Fin n → ℝ) i) = 0 :=
    (tangentSpace.mem_iff (α := Fin n) (u := (u : Fin n → ℝ))).1 u.property
  let S : Finset (Fin n) := (Finset.univ : Finset (Fin n)).erase i0
  have hsum_erase : (∑ i ∈ S, (u : Fin n → ℝ) i) = -(u : Fin n → ℝ) i0 := by
    have h :
        (∑ i : Fin n, (u : Fin n → ℝ) i) =
          (∑ i ∈ S, (u : Fin n → ℝ) i) + (u : Fin n → ℝ) i0 := by
      exact
        (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => (u : Fin n → ℝ) i) (a := i0) (Finset.mem_univ i0)).symm
    have hu' := hu_sum
    rw [h] at hu'
    linarith
  have h_erase :
      (∑ i : Fin n, ∑ j : Fin n,
          (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
            B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0))
        =
        ∑ i ∈ S, ∑ j ∈ S,
          (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
            B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) := by
    exact B_double_sum_erase (G := G) (n := n) (u := u) (i0 := i0)
  have h_pairS (i : Fin n) (hiS : i ∈ S) : i ≠ i0 :=
    (Finset.mem_erase.1 hiS).1
  have hkernel :
      (∑ i ∈ S, ∑ j ∈ S,
          (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
            B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0))
        =
        ∑ i ∈ S, ∑ j ∈ S,
          (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
            (if i = j then c else (1 / 2 : ℝ) * c) := by
    refine Finset.sum_congr rfl (fun i hiS => ?_)
    refine Finset.sum_congr rfl (fun j hjS => ?_)
    have hi0 : i ≠ i0 := h_pairS i hiS
    have hj0 : j ≠ i0 := h_pairS j hjS
    simp_all
  have h_expandS := kernel_sum_expand (n := n) (u := u) (S := S) (c := c)
  have hSsq :
      (∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j) =
        (u : Fin n → ℝ) i0 * (u : Fin n → ℝ) i0 := by
    simp_all
  have hsq_split :
      (∑ k : Fin n, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) =
        (u : Fin n → ℝ) i0 * (u : Fin n → ℝ) i0 +
          ∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i := by
    have h :
        (∑ k : Fin n, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) =
          (∑ k ∈ S, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) +
            (u : Fin n → ℝ) i0 * (u : Fin n → ℝ) i0 := by
      exact
        (Finset.sum_erase_add
            (s := (Finset.univ : Finset (Fin n)))
            (f := fun k : Fin n =>
              (u : Fin n → ℝ) k * (u : Fin n → ℝ) k)
            (a := i0) (Finset.mem_univ i0)).symm
    calc
      (∑ k : Fin n, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) =
          (∑ k ∈ S, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) +
            (u : Fin n → ℝ) i0 * (u : Fin n → ℝ) i0 := h
      _ =
          (u : Fin n → ℝ) i0 * (u : Fin n → ℝ) i0 +
            ∑ k ∈ S, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k := by
            ac_rfl
  simp_all

lemma B_eq_smul_fisherBilin_uniform (i0 i1 : Fin n) (hi01 : i0 ≠ i1) :
  B (G := G) (n := n)
    =
      (B (G := G) (n := n) (dij (n := n) i0 i1) (dij (n := n) i0 i1) /
          (2 * (Fintype.card (Fin n) : ℝ))) • fisherBilin (Simplex.uniform (α := Fin n)) := by
  classical
  have : Nonempty (Fin n) := ⟨i0⟩
  set c : ℝ := B (G := G) (n := n) (dij (n := n) i0 i1) (dij (n := n) i0 i1) with hc
  have hcard_ne : (Fintype.card (Fin n) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  have hSymm₁ : (B (G := G) (n := n)).IsSymm := by
    refine ⟨fun u v => ?_⟩
    simpa using (B_symm (G := G) (n := n) u v)
  have hSymm₂ :
      (((c / (2 * (Fintype.card (Fin n) : ℝ))) •
        fisherBilin (Simplex.uniform (α := Fin n)))).IsSymm := by
    refine ⟨fun u v => ?_⟩
    simp [fisherBilin.comm (p := Simplex.uniform (α := Fin n))]
  have hdiag : ∀ u : V n,
      B (G := G) (n := n) u u =
        ((c / (2 * (Fintype.card (Fin n) : ℝ))) •
          fisherBilin (Simplex.uniform (α := Fin n))) u u := by
    intro u
    have hB_quadratic :=
      B_quadratic_dij_sum (G := G) (n := n) (i0 := i0) (i1 := i1) hi01 c hc u
    have hfisher :
        (fisherBilin (Simplex.uniform (α := Fin n)) u u) =
          (Fintype.card (Fin n) : ℝ) * (∑ k : Fin n, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) := by
      simp only [fisherBilin.apply, Simplex.uniform_apply, Fintype.card_fin, one_div,
        div_inv_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      ring
    have hscaled_fisher :
        (c / (2 * (Fintype.card (Fin n) : ℝ))) * fisherBilin (Simplex.uniform (α := Fin n)) u u =
          (c / 2) * (∑ k : Fin n, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) := by
      rw [hfisher]
      have hscale :
          (c / (2 * (Fintype.card (Fin n) : ℝ))) * (Fintype.card (Fin n) : ℝ) = c / 2 := by
        have hm : (Fintype.card (Fin n) : ℝ) ≠ 0 := hcard_ne
        rw [div_mul_eq_mul_div]
        exact mul_div_mul_right (a := c) (b := (2 : ℝ)) (c := (Fintype.card (Fin n) : ℝ)) hm
      rw [← mul_assoc]
      rw [hscale]
    simp_all
  have hEq :=
    LinearMap.BilinForm.ext_of_isSymm hSymm₁ hSymm₂ hdiag
  simpa [c, hc] using hEq

end Bilin
end TangentFin
end LeanPool.CencovPetz
