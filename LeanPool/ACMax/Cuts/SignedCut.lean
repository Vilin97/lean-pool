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
# Signed (three-valued) certificate — the unifying general method

Every `n ≤ 8` upper-bound proof, and the `n = 9` extremal graphs where the `±1` cut
method *provably* fails, are all captured by a single **`{-1,0,1}` test vector**
`x = 𝟙_P − 𝟙_N` with a third "neutral" set `Z = (P ∪ N)ᶜ`.  Orthogonality to `𝟙`
requires `|P| = |N|`; the squared norm is `2|P|`; and the Laplacian quadratic form is
`xᵀ L x = 4·e(P,N) + e(P,Z) + e(N,Z)` (cross edges between `P` and `N` cost `4`, edges
to the neutral set cost `1`, edges inside a block cost `0`).  Hence the certificate
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4|P|` gives `algConn G ≤ 2`.

This **subsumes**:
* `algConn_le_two_of_balanced_cut` (`Z = ∅`, `N = Pᶜ`): `4·cut ≤ 4|P| ↔ cut ≤ |P| = n/2`;
* `algConn_le_two_of_nonadj_pair` (`P = {u}`, `N = {v}`): `deg u + deg v + 2[u∼v] ≤ 4`;

and, unlike any bipartition cut, it certifies the `λ₂ = 2` Fiedler-eigenvector graphs at
`n = 9` (the eigenvectors are `{-1,0,1}`-valued, with the high-degree vertices in `Z`).
-/

public section

namespace ACMax

open Matrix

open Classical in
/-- Three-valued (`{-1,0,1}`) certificate: disjoint equal-size `P, N` with
`4·e(P,N) + e(P, neutral) + e(N, neutral) ≤ 4|P|` forces `algConn G ≤ 2`, where the
neutral set is `(P ∪ N)ᶜ`. -/
theorem algConn_le_two_of_signed {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (P N : Finset V) (hd : Disjoint P N)
    (hc : P.card = N.card) (hpos : 0 < P.card)
    (hcond : 4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
             + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
             + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
             ≤ 4 * P.card) :
    algConn G ≤ 2 := by
  classical
  set ePN : ℕ := ∑ p ∈ P, (G.neighborFinset p ∩ N).card with hePNdef
  set ePZ : ℕ := ∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card with hePZdef
  set eNZ : ℕ := ∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card with heNZdef
  set x : V → ℝ :=
    fun v => (if v ∈ P then (1 : ℝ) else 0) - (if v ∈ N then (1 : ℝ) else 0) with hx
  -- Obligation 1: `x` is orthogonal to the all-ones vector.
  have hsum0 : ∑ i, x i = 0 := by
    simp only [hx]
    rw [Finset.sum_sub_distrib]
    simp_rw [Finset.sum_boole, Finset.filter_univ_mem]
    rw [hc]
    ring
  -- Obligation 2: `x` is nonzero.
  have hne : ∃ i, x i ≠ 0 := by
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    refine ⟨p, ?_⟩
    have hpN : p ∉ N := Finset.disjoint_left.mp hd hp
    simp only [hx, hp, hpN, ite_true, ite_false]
    norm_num
  -- Norm: each `p ∈ P`, `q ∈ N` contributes `1`, neutral contributes `0`.
  have hnorm : ∑ i, (x i) ^ 2 = (P.card : ℝ) + (N.card : ℝ) := by
    have hsq : ∀ i,
        (x i) ^ 2 = (if i ∈ P then (1 : ℝ) else 0) + (if i ∈ N then (1 : ℝ) else 0) := by
      intro i
      simp only [hx]
      by_cases hiP : i ∈ P
      · have hiN : i ∉ N := Finset.disjoint_left.mp hd hiP
        simp [hiP, hiN]
      · by_cases hiN : i ∈ N <;> simp [hiP, hiN]
    simp_rw [hsq, Finset.sum_add_distrib, Finset.sum_boole, Finset.filter_univ_mem]
  -- Count lemma `P → N`: ordered adjacent pairs `(i ∈ P, j ∈ N)` total `ePN`.
  have hPN : (∑ i, ∑ j, if (G.Adj i j ∧ i ∈ P ∧ j ∈ N) then (1 : ℝ) else 0) = (ePN : ℝ) := by
    have hinner : ∀ i, (∑ j, if (G.Adj i j ∧ i ∈ P ∧ j ∈ N) then (1 : ℝ) else 0) =
        if i ∈ P then ((G.neighborFinset i ∩ N).card : ℝ) else 0 := by
      intro i
      by_cases hi : i ∈ P
      · simp only [hi, true_and, ite_true]
        have hfilt : (Finset.univ.filter fun j => G.Adj i j ∧ j ∈ N) =
            G.neighborFinset i ∩ N := by
          ext j; simp [SimpleGraph.mem_neighborFinset, Finset.mem_inter]
        rw [Finset.sum_boole, hfilt]
      · simp [hi]
    simp_rw [hinner]
    rw [Finset.sum_ite_mem, Finset.univ_inter, hePNdef]
    push_cast
    rfl
  -- Count lemma `N → P`: equal to `ePN` by symmetry.
  have hNP : (∑ i, ∑ j, if (G.Adj i j ∧ i ∈ N ∧ j ∈ P) then (1 : ℝ) else 0) = (ePN : ℝ) := by
    rw [← hPN, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
    tauto
  -- Count lemma `P → Z`: ordered adjacent pairs `(i ∈ P, j ∉ P ∪ N)` total `ePZ`.
  have hPZ :
      (∑ i, ∑ j, if (G.Adj i j ∧ i ∈ P ∧ j ∉ P ∪ N) then (1 : ℝ) else 0) = (ePZ : ℝ) := by
    have hinner : ∀ i, (∑ j, if (G.Adj i j ∧ i ∈ P ∧ j ∉ P ∪ N) then (1 : ℝ) else 0) =
        if i ∈ P then ((G.neighborFinset i \ (P ∪ N)).card : ℝ) else 0 := by
      intro i
      by_cases hi : i ∈ P
      · simp only [hi, true_and, ite_true]
        have hfilt : (Finset.univ.filter fun j => G.Adj i j ∧ j ∉ P ∪ N) =
            G.neighborFinset i \ (P ∪ N) := by
          ext j; simp [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff]
        rw [Finset.sum_boole, hfilt]
      · simp [hi]
    simp_rw [hinner]
    rw [Finset.sum_ite_mem, Finset.univ_inter, hePZdef]
    push_cast
    rfl
  -- Count lemma `Z → P`: equal to `ePZ` by symmetry.
  have hZP :
      (∑ i, ∑ j, if (G.Adj i j ∧ i ∉ P ∪ N ∧ j ∈ P) then (1 : ℝ) else 0) = (ePZ : ℝ) := by
    rw [← hPZ, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
    tauto
  -- Count lemma `N → Z`: ordered adjacent pairs `(i ∈ N, j ∉ P ∪ N)` total `eNZ`.
  have hNZ :
      (∑ i, ∑ j, if (G.Adj i j ∧ i ∈ N ∧ j ∉ P ∪ N) then (1 : ℝ) else 0) = (eNZ : ℝ) := by
    have hinner : ∀ i, (∑ j, if (G.Adj i j ∧ i ∈ N ∧ j ∉ P ∪ N) then (1 : ℝ) else 0) =
        if i ∈ N then ((G.neighborFinset i \ (P ∪ N)).card : ℝ) else 0 := by
      intro i
      by_cases hi : i ∈ N
      · simp only [hi, true_and, ite_true]
        have hfilt : (Finset.univ.filter fun j => G.Adj i j ∧ j ∉ P ∪ N) =
            G.neighborFinset i \ (P ∪ N) := by
          ext j; simp [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff]
        rw [Finset.sum_boole, hfilt]
      · simp [hi]
    simp_rw [hinner]
    rw [Finset.sum_ite_mem, Finset.univ_inter, heNZdef]
    push_cast
    rfl
  -- Count lemma `Z → N`: equal to `eNZ` by symmetry.
  have hZN :
      (∑ i, ∑ j, if (G.Adj i j ∧ i ∉ P ∪ N ∧ j ∈ N) then (1 : ℝ) else 0) = (eNZ : ℝ) := by
    rw [← hNZ, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    refine if_congr ?_ rfl rfl
    rw [SimpleGraph.adj_comm]
    tauto
  -- Quadratic form equals `4·ePN + ePZ + eNZ`.
  have hquad : dotProduct x ((G.lapMatrix ℝ).mulVec x) =
      4 * (ePN : ℝ) + (ePZ : ℝ) + (eNZ : ℝ) := by
    rw [← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂']
    have hiPN : ∀ i, i ∈ P → i ∉ N := fun i h => Finset.disjoint_left.mp hd h
    have hterm : ∀ i j, (if G.Adj i j then (x i - x j) ^ 2 else 0) =
        4 * (if (G.Adj i j ∧ i ∈ P ∧ j ∈ N) then (1 : ℝ) else 0) +
        4 * (if (G.Adj i j ∧ i ∈ N ∧ j ∈ P) then (1 : ℝ) else 0) +
        (if (G.Adj i j ∧ i ∈ P ∧ j ∉ P ∪ N) then (1 : ℝ) else 0) +
        (if (G.Adj i j ∧ i ∉ P ∪ N ∧ j ∈ P) then (1 : ℝ) else 0) +
        (if (G.Adj i j ∧ i ∈ N ∧ j ∉ P ∪ N) then (1 : ℝ) else 0) +
        (if (G.Adj i j ∧ i ∉ P ∪ N ∧ j ∈ N) then (1 : ℝ) else 0) := by
      intro i j
      simp only [hx]
      by_cases hadj : G.Adj i j
      · by_cases hiP : i ∈ P <;> by_cases hiN : i ∈ N <;> by_cases hjP : j ∈ P <;>
          by_cases hjN : j ∈ N <;>
          first
          | exact absurd hiN (hiPN i hiP)
          | exact absurd hjN (hiPN j hjP)
          | (simp [hadj, hiP, hiN, hjP, hjN, Finset.mem_union] <;> norm_num)
      · simp [hadj]
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hPN, hNP, hPZ, hZP, hNZ, hZN]
    ring
  -- Conclude via the universal test-vector certificate.
  apply algConn_le_two_of_testvector G x hsum0 hne
  rw [hquad, hnorm]
  have hcondR : 4 * (ePN : ℝ) + (ePZ : ℝ) + (eNZ : ℝ) ≤ 4 * (P.card : ℝ) := by
    exact_mod_cast hcond
  have hcR : (N.card : ℝ) = (P.card : ℝ) := by exact_mod_cast hc.symm
  rw [hcR]
  linarith

end ACMax
