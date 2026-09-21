/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperSeries

/-!
# Hook vanishing for Jacobi–Trudi determinants

If the complete homogeneous sequence attached to a scalar sequence
`t` satisfies the alternating binomial recurrence of order `p`
beyond degree `q` — the coefficient statement of
`(1 − X)^p · Σ h_n Xⁿ = polynomial of degree ≤ q` — then the Schur
specialisation `diagramSchur λ t` vanishes for every diagram `λ`
containing the cell `(p, q)`.

Route: a unipotent column operation turns each column `≥ p` of the
Jacobi–Trudi matrix into the recurrence sums; in the first `p + 1`
rows the recurrence applies and the transformed entries vanish, so
those rows live in a `p`-dimensional coordinate subspace, are
linearly dependent, and the determinant is zero.
-/

namespace RS

open Matrix Finset

/-- The unipotent column-operation matrix: columns `< p` are left
alone, and column `j ≥ p` becomes the alternating binomial
combination of columns `j, j − 1, …, j − p`. -/
noncomputable def hookColOp (p ℓ : ℕ) : Matrix (Fin ℓ) (Fin ℓ) ℂ :=
  Matrix.of fun k j =>
    if (j : ℕ) < p then (if k = j then 1 else 0)
    else if (k : ℕ) ≤ (j : ℕ) then
      (-1 : ℂ) ^ ((j : ℕ) - (k : ℕ)) *
        ((p.choose ((j : ℕ) - (k : ℕ))) : ℂ)
    else 0

/-- The column operation is upper triangular. -/
theorem hookColOp_blockTriangular (p ℓ : ℕ) :
    (hookColOp p ℓ).BlockTriangular id := by
  intro k j hjk
  have h : (j : ℕ) < (k : ℕ) := hjk
  simp only [hookColOp, Matrix.of_apply]
  split_ifs with h1 h2 h3
  · exact absurd (congrArg Fin.val h2) (by omega)
  · rfl
  · omega
  · rfl

/-- The column operation has determinant one. -/
theorem det_hookColOp (p ℓ : ℕ) : (hookColOp p ℓ).det = 1 := by
  rw [Matrix.det_of_upperTriangular (hookColOp_blockTriangular p ℓ)]
  apply Finset.prod_eq_one
  intro j _
  simp only [hookColOp, Matrix.of_apply]
  split_ifs with h1 h2
  · rfl
  · simp
  · omega

/-- The Jacobi–Trudi matrix of a row-length list. -/
noncomputable def jtMatrix (t : ℕ → ℂ) (rows : List ℕ) :
    Matrix (Fin rows.length) (Fin rows.length) ℂ :=
  Matrix.of fun i j : Fin rows.length =>
    newtonHZ t ((rows.get i : ℤ) + (j : ℤ) - (i : ℤ))

/-- `schurDet` is the determinant of the Jacobi–Trudi matrix. -/
theorem schurDet_eq_det_jtMatrix (t : ℕ → ℂ) (rows : List ℕ) :
    schurDet t rows = (jtMatrix t rows).det :=
  rfl

/-- Columns `≥ p` of the transformed Jacobi–Trudi matrix carry the
alternating binomial recurrence sums. -/
theorem jtMatrix_mul_hookColOp (t : ℕ → ℂ) (rows : List ℕ) (p : ℕ)
    (i j : Fin rows.length) (hj : p ≤ (j : ℕ)) :
    (jtMatrix t rows * hookColOp p rows.length) i j =
      ∑ d ∈ Finset.range (p + 1), (-1 : ℂ) ^ d * (p.choose d : ℂ) *
        newtonHZ t ((rows.get i : ℤ) + (j : ℤ) - (i : ℤ) - (d : ℤ)) := by
  rw [Matrix.mul_apply]
  have hnotlt : ¬ (j : ℕ) < p := not_lt.mpr hj
  -- Extend the recurrence sum to `range (j + 1)`: the extra terms
  -- carry a vanishing binomial coefficient.
  have hext :
      (∑ d ∈ Finset.range (p + 1), (-1 : ℂ) ^ d * (p.choose d : ℂ) *
        newtonHZ t ((rows.get i : ℤ) + (j : ℤ) - (i : ℤ) - (d : ℤ))) =
      ∑ d ∈ Finset.range ((j : ℕ) + 1),
        (-1 : ℂ) ^ d * (p.choose d : ℂ) *
        newtonHZ t ((rows.get i : ℤ) + (j : ℤ) - (i : ℤ) - (d : ℤ)) := by
    refine Finset.sum_subset (fun x hx => ?_) ?_
    · rw [Finset.mem_range] at hx ⊢
      omega
    intro d hd hnd
    rw [Finset.mem_range] at hd
    rw [Finset.mem_range, not_lt] at hnd
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    ring
  rw [hext]
  -- Indices `k > j` do not contribute on the left.
  rw [show (∑ k, jtMatrix t rows i k * hookColOp p rows.length k j) =
      ∑ k ∈ Finset.univ.filter
        (fun k : Fin rows.length => (k : ℕ) ≤ (j : ℕ)),
        jtMatrix t rows i k * hookColOp p rows.length k j from
    (Finset.sum_subset (Finset.filter_subset _ _) (by
      intro k _ hk
      rw [Finset.mem_filter, not_and] at hk
      have hkj : ¬ (k : ℕ) ≤ (j : ℕ) := hk (Finset.mem_univ k)
      simp only [hookColOp, Matrix.of_apply, if_neg hnotlt,
        if_neg hkj, mul_zero])).symm]
  -- Reindex by `d = j − k`.
  refine Finset.sum_bij'
    (i := fun k _ => (j : ℕ) - (k : ℕ))
    (j := fun d hd => (⟨(j : ℕ) - d,
      lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ : Fin rows.length))
    ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range]
    omega
  · intro d _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Nat.sub_le _ _⟩
  · intro k hk
    rw [Finset.mem_filter] at hk
    refine Fin.ext ?_
    show (j : ℕ) - ((j : ℕ) - (k : ℕ)) = (k : ℕ)
    omega
  · intro d hd
    rw [Finset.mem_range] at hd
    show (j : ℕ) - ((j : ℕ) - d) = d
    omega
  · intro k hk
    rw [Finset.mem_filter] at hk
    have hkj : (k : ℕ) ≤ (j : ℕ) := hk.2
    simp only [jtMatrix, hookColOp, Matrix.of_apply, if_neg hnotlt,
      if_pos hkj]
    have hcast : (((j : ℕ) - (k : ℕ) : ℕ) : ℤ) =
        (j : ℤ) - (k : ℤ) := by omega
    rw [hcast]
    have harg : (rows.get i : ℤ) + (k : ℤ) - (i : ℤ) =
        (rows.get i : ℤ) + (j : ℤ) - (i : ℤ) -
          ((j : ℤ) - (k : ℤ)) := by ring
    rw [harg]
    ring

/-- In the first `p + 1` rows, the transformed entries in columns
`≥ p` vanish by the recurrence: the diagram contains the cell
`(p, q)`, so those rows are long enough to push the argument past
degree `q`. -/
theorem jtMatrix_mul_hookColOp_eq_zero (t : ℕ → ℂ) {p q : ℕ}
    (hrec : ∀ m : ℤ, (q : ℤ) < m →
      ∑ d ∈ Finset.range (p + 1), (-1 : ℂ) ^ d * (p.choose d : ℂ) *
        newtonHZ t (m - (d : ℤ)) = 0)
    (lam : YoungDiagram) (hcell : (p, q) ∈ lam)
    (i j : Fin lam.rowLens.length)
    (hi : (i : ℕ) ≤ p) (hj : p ≤ (j : ℕ)) :
    (jtMatrix t lam.rowLens * hookColOp p lam.rowLens.length) i j
      = 0 := by
  rw [jtMatrix_mul_hookColOp t lam.rowLens p i j hj]
  have hget : lam.rowLens.get i = lam.rowLen (i : ℕ) := by
    rw [List.get_eq_getElem, YoungDiagram.get_rowLens]
  have hq : q < lam.rowLen (i : ℕ) :=
    lt_of_lt_of_le (YoungDiagram.mem_iff_lt_rowLen.mp hcell)
      (lam.rowLen_anti _ _ hi)
  have hij : (i : ℕ) ≤ (j : ℕ) := le_trans hi hj
  have hm : (q : ℤ) <
      (lam.rowLens.get i : ℤ) + (j : ℤ) - (i : ℤ) := by
    rw [hget]
    omega
  exact hrec _ hm

/-- **Hook vanishing** (the combinatorial engine behind Deligne
1.9): if the complete homogeneous sequence of `t` satisfies the
alternating binomial recurrence of order `p` beyond degree `q`,
the Schur specialisation vanishes on every diagram containing the
cell `(p, q)`. -/
theorem diagramSchur_eq_zero_of_hook (t : ℕ → ℂ) {p q : ℕ}
    (hrec : ∀ m : ℤ, (q : ℤ) < m →
      ∑ d ∈ Finset.range (p + 1), (-1 : ℂ) ^ d * (p.choose d : ℂ) *
        newtonHZ t (m - (d : ℤ)) = 0)
    (lam : YoungDiagram) (hcell : (p, q) ∈ lam) :
    diagramSchur lam t = 0 := by
  -- Notation and the size bound `p < ℓ`.
  set ℓ := lam.rowLens.length with hℓ
  have hpl : p < ℓ := by
    rw [hℓ, YoungDiagram.length_rowLens]
    rw [← YoungDiagram.mem_iff_lt_colLen]
    exact lam.up_left_mem le_rfl (Nat.zero_le q) hcell
  set M := jtMatrix t lam.rowLens * hookColOp p ℓ with hM
  -- The first `p + 1` rows, restricted to the first `p` columns.
  set v : Fin (p + 1) → (Fin p → ℂ) := fun a b =>
    M ⟨(a : ℕ), lt_of_lt_of_le a.isLt hpl⟩
      ⟨(b : ℕ), lt_of_le_of_lt (Nat.le_of_lt b.isLt) hpl⟩ with hv
  -- Too many vectors for the ambient dimension: dependence.
  have hdep : ¬ LinearIndependent ℂ v := by
    intro hLI
    have hcard := hLI.fintype_card_le_finrank
    rw [Module.finrank_pi] at hcard
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨f, g, hfg, i₀, hne⟩ :=
    Fintype.not_linearIndependent_iffₛ.mp hdep
  set c : Fin (p + 1) → ℂ := fun a => f a - g a with hc
  have hcsum : ∑ a, c a • v a = 0 := by
    simp only [hc, sub_smul]
    rw [Finset.sum_sub_distrib, hfg, sub_self]
  have hc₀ : c i₀ ≠ 0 := sub_ne_zero.mpr hne
  -- The dependence vector, extended by zero.
  set w : Fin ℓ → ℂ := fun k =>
    if h : (k : ℕ) < p + 1 then c ⟨(k : ℕ), h⟩ else 0 with hw
  have hwne : w ≠ 0 := by
    intro h0
    apply hc₀
    calc c i₀ = w ⟨(i₀ : ℕ), lt_of_lt_of_le i₀.isLt hpl⟩ := by
          rw [hw]
          show c i₀ =
            if h : (i₀ : ℕ) < p + 1 then c ⟨(i₀ : ℕ), h⟩ else 0
          rw [dif_pos i₀.isLt]
      _ = 0 := by rw [h0]; rfl
  -- The extended vector annihilates the transformed matrix.
  have hvm : Matrix.vecMul w M = 0 := by
    funext j
    show ∑ k, w k * M k j = 0
    -- Only the first `p + 1` rows contribute.
    rw [show (∑ k, w k * M k j) =
        ∑ a : Fin (p + 1), c a *
          M ⟨(a : ℕ), lt_of_lt_of_le a.isLt hpl⟩ j from ?_]
    · rcases lt_or_ge (j : ℕ) p with hjp | hjp
      · -- Columns `< p`: the chosen dependence relation.
        have := congrFun hcsum ⟨(j : ℕ), hjp⟩
        rw [Finset.sum_apply] at this
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
        rw [← this]
      · -- Columns `≥ p`: the recurrence zeroes.
        refine Finset.sum_eq_zero fun a _ => ?_
        have hz := jtMatrix_mul_hookColOp_eq_zero t hrec lam hcell
          ⟨(a : ℕ), lt_of_lt_of_le a.isLt hpl⟩ j
          (Nat.lt_succ_iff.mp a.isLt) hjp
        show c a * (jtMatrix t lam.rowLens *
          hookColOp p lam.rowLens.length)
            ⟨(a : ℕ), lt_of_lt_of_le a.isLt hpl⟩ j = 0
        rw [hz, mul_zero]
    · -- Collapse the zero-extended sum onto `Fin (p + 1)`.
      rw [show (∑ k, w k * M k j) =
          ∑ k ∈ Finset.univ.filter
            (fun k : Fin ℓ => (k : ℕ) < p + 1), w k * M k j from
        (Finset.sum_subset (Finset.filter_subset _ _) (by
          intro k _ hk
          rw [Finset.mem_filter, not_and] at hk
          have : ¬ (k : ℕ) < p + 1 := hk (Finset.mem_univ k)
          rw [hw]
          simp only [dif_neg this, zero_mul])).symm]
      refine Finset.sum_bij'
        (i := fun k hk => (⟨(k : ℕ),
          (Finset.mem_filter.mp hk).2⟩ : Fin (p + 1)))
        (j := fun a _ => (⟨(a : ℕ),
          lt_of_lt_of_le a.isLt hpl⟩ : Fin ℓ))
        ?_ ?_ ?_ ?_ ?_
      · intro k _
        exact Finset.mem_univ _
      · intro a _
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, a.isLt⟩
      · intro k _
        exact Fin.ext rfl
      · intro a _
        exact Fin.ext rfl
      · intro k hk
        have hklt : (k : ℕ) < p + 1 := (Finset.mem_filter.mp hk).2
        rw [hw]
        simp only [dif_pos hklt]
        rfl
  -- Conclude through the determinant.
  have hdet0 : M.det = 0 :=
    Matrix.exists_vecMul_eq_zero_iff.mp ⟨w, hwne, hvm⟩
  have hdetM : (jtMatrix t lam.rowLens).det = 0 := by
    have := Matrix.det_mul (jtMatrix t lam.rowLens) (hookColOp p ℓ)
    rw [← hM, hdet0, det_hookColOp, mul_one] at this
    exact this.symm
  rw [diagramSchur, schurDet_eq_det_jtMatrix, hdetM]

/-- The super-power-sum sequences satisfy the recurrence slot of
`diagramSchur_eq_zero_of_hook`, in its integer-indexed form. -/
theorem superPS_rec_int (p q : ℕ) {m : ℤ} (hm : (q : ℤ) < m) :
    ∑ d ∈ Finset.range (p + 1), (-1 : ℂ) ^ d * (p.choose d : ℂ) *
      newtonHZ (superPS p q) (m - (d : ℤ)) = 0 := by
  have hm0 : 0 ≤ m := le_trans (Int.natCast_nonneg q) (le_of_lt hm)
  set n := m.toNat with hn
  have hmn : m = (n : ℤ) := (Int.toNat_of_nonneg hm0).symm
  have hqn : q < n := by omega
  have hanti := newtonH_superPS_rec_antidiagonal p q hqn
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hanti
  -- Both sums agree with the common extension to `range (M + 1)`.
  set M := max p n with hM
  have hleft :
      (∑ d ∈ Finset.range (p + 1), (-1 : ℂ) ^ d * (p.choose d : ℂ) *
        newtonHZ (superPS p q) (m - (d : ℤ))) =
      ∑ d ∈ Finset.range (M + 1), (-1 : ℂ) ^ d * (p.choose d : ℂ) *
        newtonHZ (superPS p q) (m - (d : ℤ)) := by
    refine Finset.sum_subset (fun x hx => ?_) (fun d _ hd => ?_)
    · rw [Finset.mem_range] at hx ⊢
      omega
    · rw [Finset.mem_range, not_lt] at hd
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      ring
  have hswap :
      (∑ d ∈ Finset.range (M + 1), (-1 : ℂ) ^ d * (p.choose d : ℂ) *
        newtonHZ (superPS p q) (m - (d : ℤ))) =
      ∑ d ∈ Finset.range (n + 1), (-1 : ℂ) ^ d * (p.choose d : ℂ) *
        newtonHZ (superPS p q) (m - (d : ℤ)) := by
    refine (Finset.sum_subset (fun x hx => ?_) (fun d _ hd => ?_)).symm
    · rw [Finset.mem_range] at hx ⊢
      omega
    · rw [Finset.mem_range, not_lt] at hd
      have hneg : m - (d : ℤ) < 0 := by omega
      rw [newtonHZ, if_neg (not_le.mpr hneg), mul_zero]
  have hconv :
      (∑ d ∈ Finset.range (n + 1), (-1 : ℂ) ^ d * (p.choose d : ℂ) *
        newtonHZ (superPS p q) (m - (d : ℤ))) =
      ∑ d ∈ Finset.range (n + 1), (-1 : ℂ) ^ d * (p.choose d : ℂ) *
        newtonH (superPS p q) (n - d) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_range] at hd
    congr 1
    rw [show m - (d : ℤ) = ((n - d : ℕ) : ℤ) by omega,
      newtonHZ_natCast]
  rw [hleft, hswap, hconv]
  exact hanti

/-- **Deligne 1.9, vanishing direction, character side**: the Schur
specialisation at the super power sums of dimension `(p, q)`
vanishes on every diagram containing the cell `(p, q)`. -/
theorem diagramSchur_superPS_eq_zero {p q : ℕ} (lam : YoungDiagram)
    (hcell : (p, q) ∈ lam) :
    diagramSchur lam (superPS p q) = 0 :=
  diagramSchur_eq_zero_of_hook (superPS p q)
    (fun _ hm => superPS_rec_int p q hm) lam hcell

/-- One `h`-variable: the Schur specialisation at `superPS 1 0` is
the indicator of single-row diagrams. -/
theorem diagramSchur_superPS_row (ν : YoungDiagram) :
    diagramSchur ν (superPS 1 0) =
      if ν.colLen 0 ≤ 1 then 1 else 0 := by
  by_cases h : ν.colLen 0 ≤ 1
  · rw [if_pos h]
    have hlen : ν.rowLens.length ≤ 1 := by
      rw [YoungDiagram.length_rowLens]; exact h
    rw [diagramSchur, schurDet_eq_det_jtMatrix,
      Matrix.det_of_upperTriangular
        (by
          intro i j hji
          have hji' : (j : ℕ) < (i : ℕ) := hji
          have hi := i.isLt
          omega)]
    refine Finset.prod_eq_one fun i _ => ?_
    show newtonHZ (superPS 1 0)
      ((ν.rowLens.get i : ℤ) + (i : ℤ) - (i : ℤ)) = 1
    rw [show ((ν.rowLens.get i : ℤ) + (i : ℤ) - (i : ℤ)) =
      ((ν.rowLens.get i : ℕ) : ℤ) by ring, newtonHZ_natCast,
      newtonH_superPS_zero_q 1 _ Nat.one_pos]
    simp
  · rw [if_neg h]
    exact diagramSchur_superPS_eq_zero ν
      (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))

/-- One `e`-variable: the Schur specialisation at `superPS 0 1` is
the indicator of single-column diagrams. -/
theorem diagramSchur_superPS_col (ν : YoungDiagram) :
    diagramSchur ν (superPS 0 1) =
      if ν.rowLen 0 ≤ 1 then 1 else 0 := by
  by_cases h : ν.rowLen 0 ≤ 1
  · rw [if_pos h]
    have hone : ∀ i : Fin ν.rowLens.length,
        ν.rowLens.get i = 1 := by
      intro i
      have hpos : 0 < ν.rowLens.get i :=
        ν.pos_of_mem_rowLens _ (ν.rowLens.get_mem i)
      have hle : ν.rowLens.get i ≤ ν.rowLen 0 := by
        rw [List.get_eq_getElem, YoungDiagram.get_rowLens]
        exact ν.rowLen_anti 0 (i : ℕ) (Nat.zero_le _)
      omega
    have hval : ∀ n : ℕ,
        newtonH (superPS 0 1) n = ((1 : ℕ).choose n : ℂ) :=
      newtonH_superPS_zero_p 1
    rw [diagramSchur, schurDet_eq_det_jtMatrix,
      Matrix.det_of_lowerTriangular _ (by
        intro i j hij
        have hij' : (i : ℕ) < (j : ℕ) := hij
        show newtonHZ (superPS 0 1)
          ((ν.rowLens.get i : ℤ) + (j : ℤ) - (i : ℤ)) = 0
        rw [hone i, show ((1 : ℕ) : ℤ) + (j : ℤ) - (i : ℤ) =
          ((1 + (j : ℕ) - (i : ℕ) : ℕ) : ℤ) by omega,
          newtonHZ_natCast, hval]
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp)]
    refine Finset.prod_eq_one fun i _ => ?_
    show newtonHZ (superPS 0 1)
      ((ν.rowLens.get i : ℤ) + (i : ℤ) - (i : ℤ)) = 1
    rw [hone i, show ((1 : ℕ) : ℤ) + (i : ℤ) - (i : ℤ) =
      ((1 : ℕ) : ℤ) by ring, newtonHZ_natCast, hval]
    simp
  · rw [if_neg h]
    exact diagramSchur_superPS_eq_zero ν
      (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))

end RS
