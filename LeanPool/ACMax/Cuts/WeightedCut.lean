/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import LeanPool.ACMax.Spectral.AlgConn
public import LeanPool.ACMax.Spectral.RayleighUpper
public import LeanPool.ACMax.Spectral.TestVector

/-!
# Weighted (unbalanced) cut certificate

Generalizes `algConn_le_two_of_balanced_cut` to an arbitrary bipartition `A ⊔ Aᶜ`.
With `p = |A|`, `q = |Aᶜ|`, the vector `x = q·𝟙_A − p·𝟙_{Aᶜ}` is orthogonal to `𝟙`,
has squared norm `p·q·n`, and Laplacian quadratic form `n²·cut`, so
`xᵀ L x = n²·cut ≤ 2·p·q·n = 2‖x‖²` whenever `n·cut ≤ 2·p·q`.  This handles odd `n`
and unbalanced near-regular graphs where a balanced cut is unavailable.
-/

public section

namespace ACMax

open Matrix

open Classical in
/-- A bipartition `A ⊔ Aᶜ` with `|V|·cut ≤ 2·|A|·|Aᶜ|` certifies `algConn G ≤ 2`
(`cut = ∑_{a ∈ A} |N(a) \ A|`).  Both parts must be nonempty. -/
theorem algConn_le_two_of_weighted_cut {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (A : Finset V) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hcut : Fintype.card V * (∑ a ∈ A, (G.neighborFinset a \ A).card)
            ≤ 2 * (A.card * Aᶜ.card)) :
    algConn G ≤ 2 := by
  classical
  set N : ℕ := Fintype.card V with hN
  set p : ℕ := A.card with hp
  set q : ℕ := Aᶜ.card with hq
  set cut : ℕ := ∑ a ∈ A, (G.neighborFinset a \ A).card with hcutdef
  have hpq : p + q = N := by rw [hp, hq, hN]; exact Finset.card_add_card_compl A
  have hpqR : (p : ℝ) + (q : ℝ) = (N : ℝ) := by exact_mod_cast hpq
  set x : V → ℝ := fun v => if v ∈ A then (q : ℝ) else (-(p : ℝ)) with hx
  -- Obligation 1: `x` is orthogonal to the all-ones vector.
  have hsum0 : ∑ i, x i = 0 := by
    have hval : ∀ i, x i = (N : ℝ) * (if i ∈ A then (1 : ℝ) else 0) - (p : ℝ) := by
      intro i
      simp only [hx]
      by_cases h : i ∈ A <;> simp only [h, ite_true, ite_false, mul_one, mul_zero] <;>
        linarith [hpqR]
    simp_rw [hval, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
      Finset.filter_univ_mem]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN, ← hp]
    ring
  -- Obligation 2: `x` is nonzero.
  have hne : ∃ i, x i ≠ 0 := by
    obtain ⟨a, ha⟩ := hA
    refine ⟨a, ?_⟩
    simp only [hx, ha, ite_true]
    have hq0 : 0 < q := by rw [hq]; exact Finset.card_pos.mpr hAc
    exact_mod_cast hq0.ne'
  -- Norm: `∑ (x i)^2 = p·q·N`.
  have hnorm : ∑ i, (x i) ^ 2 = (p : ℝ) * (q : ℝ) * (N : ℝ) := by
    have hsq : ∀ i, (x i) ^ 2 =
        (if i ∈ A then (1 : ℝ) else 0) * ((q : ℝ) ^ 2 - (p : ℝ) ^ 2) + (p : ℝ) ^ 2 := by
      intro i
      simp only [hx]
      by_cases h : i ∈ A <;> simp only [h, ite_true, ite_false] <;> ring
    simp_rw [hsq, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_boole,
      Finset.filter_univ_mem, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hN, ← hp, ← hpqR]
    ring
  -- Count lemma: ordered adjacent pairs `(i ∈ A, j ∉ A)` total `cut`.
  have hcount1 :
      (∑ i, ∑ j, if (G.Adj i j ∧ i ∈ A ∧ j ∉ A) then (1 : ℝ) else 0) = (cut : ℝ) := by
    have hinner : ∀ i, (∑ j, if (G.Adj i j ∧ i ∈ A ∧ j ∉ A) then (1 : ℝ) else 0) =
        if i ∈ A then ((G.neighborFinset i \ A).card : ℝ) else 0 := by
      intro i
      by_cases hi : i ∈ A
      · simp only [hi, true_and, ite_true]
        have hfilt : (Finset.univ.filter fun j => G.Adj i j ∧ j ∉ A) =
            G.neighborFinset i \ A := by
          ext j; simp [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff]
        rw [Finset.sum_boole, hfilt]
      · simp [hi]
    simp_rw [hinner]
    rw [Finset.sum_ite_mem, Finset.univ_inter, hcutdef]
    push_cast
    rfl
  -- Count lemma: ordered adjacent pairs `(i ∉ A, j ∈ A)` also total `cut`.
  have hcount2 :
      (∑ i, ∑ j, if (G.Adj i j ∧ i ∉ A ∧ j ∈ A) then (1 : ℝ) else 0) = (cut : ℝ) := by
    rw [← hcount1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
    tauto
  -- Quadratic form equals `(p+q)² · cut = N² · cut`.
  have hquad : dotProduct x ((G.lapMatrix ℝ).mulVec x) =
      ((p : ℝ) + (q : ℝ)) ^ 2 * (cut : ℝ) := by
    rw [← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂']
    have hterm : ∀ i j, (if G.Adj i j then (x i - x j) ^ 2 else 0) =
        ((p : ℝ) + (q : ℝ)) ^ 2 * (if (G.Adj i j ∧ i ∈ A ∧ j ∉ A) then (1 : ℝ) else 0) +
        ((p : ℝ) + (q : ℝ)) ^ 2 * (if (G.Adj i j ∧ i ∉ A ∧ j ∈ A) then (1 : ℝ) else 0) := by
      intro i j
      simp only [hx]
      by_cases hadj : G.Adj i j <;> by_cases hiA : i ∈ A <;> by_cases hjA : j ∈ A <;>
        simp [hadj, hiA, hjA] <;> ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcount1, hcount2]
    ring
  -- Conclude via the universal test-vector certificate.
  apply algConn_le_two_of_testvector G x hsum0 hne
  rw [hquad, hnorm, hpqR]
  have hcR : (N : ℝ) * (cut : ℝ) ≤ 2 * ((p : ℝ) * (q : ℝ)) := by exact_mod_cast hcut
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [hcR, hNnn]

end ACMax
