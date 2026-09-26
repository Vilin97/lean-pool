/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.Permanent
public import LeanPool.BeyondBethe.BeyondBethe.Stable
public import Mathlib.Tactic

/-! # Paired Certificate -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

open MvPolynomial

/-- A partition of the row set into named clusters.  The equivalence labels
each row by its cluster and its position inside that cluster.  Pair
certificates use the special case in which every size is one or two, but the
coefficient identity below holds for arbitrary cluster sizes. -/
structure RowClustering (n : ℕ) where
  /-- The type indexing the row clusters. -/
  Cluster : Type
  clusterFintype : Fintype Cluster
  clusterDecidableEq : DecidableEq Cluster
  /-- The number of local row positions assigned to each cluster. -/
  size : Cluster → ℕ
  /-- An equivalence identifying all cluster-local row positions with the original matrix rows. -/
  rows : (Σ c, Fin (size c)) ≃ Fin n

attribute [instance] RowClustering.clusterFintype
attribute [instance] RowClustering.clusterDecidableEq

namespace RowClustering

variable {n : ℕ} (C : RowClustering n)

/-- The cluster containing a row. -/
noncomputable def clusterOfRow (i : Fin n) : C.Cluster :=
  (C.rows.symm i).1

/-- The cluster selected at each column by a permutation in Mathlib's
column-to-row orientation. -/
noncomputable def clusterAssignment (σ : Equiv.Perm (Fin n)) :
    Fin n → C.Cluster :=
  fun j ↦ C.clusterOfRow (σ j)

end RowClustering

/-- Squarefree exponent vector selecting one cluster variable for each
column. -/
noncomputable def selectorExponent
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (h : ι → κ) : κ × ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v ↦ if v.1 = h v.2 then 1 else 0

@[simp]
theorem selectorExponent_apply
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (h : ι → κ) (c : κ) (j : ι) :
    selectorExponent h (c, j) = if c = h j then 1 else 0 := by
  simp [selectorExponent]

theorem selectorExponent_injective
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    [DecidableEq ι] :
    Function.Injective (selectorExponent : (ι → κ) → κ × ι →₀ ℕ) := by
  intro h h' heq
  funext j
  have hj := congrArg (fun d : κ × ι →₀ ℕ ↦ d (h j, j)) heq
  simp only [selectorExponent_apply, ite_eq_left rfl] at hj
  by_contra hne
  simp [hne] at hj

theorem selectorExponent_eq_sum_single
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (h : ι → κ) :
    selectorExponent h =
      ∑ j, Finsupp.single (h j, j) 1 := by
  classical
  ext ⟨c, j⟩
  simp [selectorExponent_apply, Finsupp.single_apply]
  by_cases hc : c = h j
  · subst c
    have hs : ({x : ι | h x = h j ∧ x = j} : Finset ι) = {j} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hx
        simpa using hx.2
      · intro hx
        have hxj : x = j := by simpa using hx
        subst x
        simp
    rw [hs]
    simp
  · have hs : ({x : ι | h x = c ∧ x = j} : Finset ι) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hx
        have hxj : x = j := hx.2
        subst x
        exact (hc hx.1.symm).elim
      · simp
    rw [hs]
    simp [hc]

theorem selectorExponent_degree
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (h : ι → κ) :
    Finsupp.degree (selectorExponent h) = Fintype.card ι := by
  rw [selectorExponent_eq_sum_single, map_sum]
  simp [Finsupp.degree_single]

theorem monomial_selectorExponent
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (h : ι → κ) :
    (monomial (selectorExponent h) 1 : MvPolynomial (κ × ι) ℝ) =
      ∏ j, X (h j, j) := by
  rw [selectorExponent_eq_sum_single, monomial_sum_one]
  simp [← X_pow_eq_monomial]

/-- The column-selector polynomial written in its monomial expansion.  It is
the expansion of `prod_j (sum_C z_{Cj})`. -/
noncomputable def columnSelector
    (κ ι : Type*) [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] : MvPolynomial (κ × ι) ℝ :=
  ∑ h : ι → κ, monomial (selectorExponent h) 1

/-- The factored form of the column selector used for its stability proof. -/
noncomputable def columnSelectorProduct
    (κ ι : Type*) [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] : MvPolynomial (κ × ι) ℝ :=
  ∏ j : ι, ∑ c : κ, X (c, j)

theorem columnSelector_eq_product
    (κ ι : Type*) [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] :
    columnSelector κ ι = columnSelectorProduct κ ι := by
  rw [columnSelectorProduct, Fintype.prod_sum, columnSelector]
  apply Finset.sum_congr rfl
  intro h _
  exact monomial_selectorExponent h

/-- The column selector is real stable: at an upper-half-plane input, each
column factor has strictly positive imaginary part. -/
theorem columnSelector_isRealStable
    (κ ι : Type*) [Fintype κ] [DecidableEq κ] [Nonempty κ]
    [Fintype ι] [DecidableEq ι] :
    IsRealStable (columnSelector κ ι) := by
  rw [columnSelector_eq_product]
  intro z hz
  rw [columnSelectorProduct, MvPolynomial.eval₂_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  rw [MvPolynomial.eval₂_sum]
  simp only [MvPolynomial.eval₂_X]
  have him : 0 < ∑ c : κ, (z (c, j)).im :=
    Finset.sum_pos (fun c _ ↦ hz (c, j)) Finset.univ_nonempty
  intro heq
  have hzero := congrArg Complex.im heq
  simp at hzero
  linarith

theorem columnSelector_nonnegativeCoefficients
    (κ ι : Type*) [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] :
    HasNonnegativeCoefficients (columnSelector κ ι) := by
  intro d
  rw [columnSelector, coeff_sum]
  apply Finset.sum_nonneg
  intro h _
  rw [coeff_monomial]
  split <;> norm_num

theorem columnSelector_isHomogeneous
    (κ ι : Type*) [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] :
    (columnSelector κ ι).IsHomogeneous (Fintype.card ι) := by
  rw [columnSelector]
  apply MvPolynomial.IsHomogeneous.sum
  intro h _
  exact isHomogeneous_monomial 1 (selectorExponent_degree h)

theorem columnSelector_isMultiaffine
    (κ ι : Type*) [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] :
    IsMultiaffine (columnSelector κ ι) := by
  intro v
  rw [columnSelector]
  refine (degreeOf_sum_le v _ _).trans (Finset.sup_le ?_)
  intro h _
  rw [degreeOf_monomial_eq _ _ one_ne_zero]
  rcases v with ⟨c, j⟩
  rw [selectorExponent_apply]
  split <;> simp

theorem columnSelector_coeff_selectorExponent
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (h : ι → κ) :
    (columnSelector κ ι).coeff (selectorExponent h) = 1 := by
  rw [columnSelector, coeff_sum]
  simp only [coeff_monomial]
  have heq : ∀ h' : ι → κ,
      (selectorExponent h' = selectorExponent h) ↔ h' = h := fun h' ↦
    (selectorExponent_injective.eq_iff)
  simp_rw [heq]
  rw [Finset.sum_ite_eq' Finset.univ h]
  simp

theorem columnSelector_support
    (κ ι : Type*) [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] :
    (columnSelector κ ι).support =
      Finset.univ.image (selectorExponent : (ι → κ) → κ × ι →₀ ℕ) := by
  ext d
  constructor
  · intro hd
    rw [mem_support_iff, columnSelector, coeff_sum] at hd
    simp only [coeff_monomial] at hd
    obtain ⟨h, _, hh⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
    by_cases heq : selectorExponent h = d
    · exact Finset.mem_image.mpr ⟨h, Finset.mem_univ h, heq⟩
    · simp [heq] at hh
  · intro hd
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hd
    rw [mem_support_iff, columnSelector_coeff_selectorExponent h]
    norm_num
theorem coefficientInnerProduct_eq_sum_right_support_of_coeff_one
    {σ : Type*}
    (p q : MvPolynomial σ ℝ)
    (hq : ∀ d ∈ q.support, q.coeff d = 1) :
    coefficientInnerProduct p q = ∑ d ∈ q.support, p.coeff d := by
  classical
  rw [coefficientInnerProduct]
  calc
    (∑ d ∈ p.support.filter (· ∈ q.support),
        p.coeff d * q.coeff d) =
        ∑ d ∈ p.support.filter (· ∈ q.support), p.coeff d := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [hq d (Finset.mem_filter.mp hd).2, mul_one]
    _ = ∑ d ∈ q.support, p.coeff d := by
          apply Finset.sum_subset
          · intro d hd
            exact (Finset.mem_filter.mp hd).2
          · intro d hdq hdnot
            by_contra hne
            apply hdnot
            exact Finset.mem_filter.mpr ⟨by
              rwa [mem_support_iff], hdq⟩

/- Pairing with the column selector extracts exactly the coefficients whose
exponents choose one cluster for each column. -/
theorem coefficientInnerProduct_columnSelector
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial (κ × ι) ℝ) :
    coefficientInnerProduct p (columnSelector κ ι) =
      ∑ h : ι → κ, p.coeff (selectorExponent h) := by
  rw [coefficientInnerProduct_eq_sum_right_support_of_coeff_one]
  · rw [columnSelector_support,
      Finset.sum_image selectorExponent_injective.injOn]
  · intro d hd
    rw [columnSelector_support] at hd
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hd
    exact columnSelector_coeff_selectorExponent h

/-- The cluster polynomial in expanded form.  Permutations that differ only
inside a cluster contribute to the same monomial, so their weights add in its
coefficient exactly as in the paper's pair polynomial. -/
noncomputable def expandedClusterPolynomial
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n) :
    MvPolynomial (C.Cluster × Fin n) ℝ :=
  ∑ σ : Equiv.Perm (Fin n),
    monomial (selectorExponent (C.clusterAssignment σ))
      (∏ j, A (σ j) j)

theorem expandedClusterPolynomial_support
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    {d : C.Cluster × Fin n →₀ ℕ}
    (hd : d ∈ (expandedClusterPolynomial A C).support) :
    ∃ σ : Equiv.Perm (Fin n),
      d = selectorExponent (C.clusterAssignment σ) := by
  rw [mem_support_iff] at hd
  rw [expandedClusterPolynomial, coeff_sum] at hd
  simp only [coeff_monomial] at hd
  obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  by_cases heq : selectorExponent (C.clusterAssignment σ) = d
  · exact ⟨σ, heq.symm⟩
  · simp [heq] at hσ

theorem columnSelector_coeff_of_mem_expandedClusterPolynomial
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    {d : C.Cluster × Fin n →₀ ℕ}
    (hd : d ∈ (expandedClusterPolynomial A C).support) :
    (columnSelector C.Cluster (Fin n)).coeff d = 1 := by
  obtain ⟨σ, rfl⟩ := expandedClusterPolynomial_support A C hd
  exact columnSelector_coeff_selectorExponent (C.clusterAssignment σ)

theorem sum_coeff_expandedClusterPolynomial_eq_permanent
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n) :
    (∑ d ∈ (expandedClusterPolynomial A C).support,
        (expandedClusterPolynomial A C).coeff d) = Matrix.permanent A := by
  let one : C.Cluster × Fin n → ℝ := fun _ ↦ 1
  have hevalCoeffs :
      (expandedClusterPolynomial A C).eval one =
        ∑ d ∈ (expandedClusterPolynomial A C).support,
          (expandedClusterPolynomial A C).coeff d := by
    rw [eval_eq]
    simp [one]
  have hevalPerm :
      (expandedClusterPolynomial A C).eval one = Matrix.permanent A := by
    rw [expandedClusterPolynomial, eval_sum]
    simp [eval_monomial, one, Matrix.permanent]
  exact hevalCoeffs.symm.trans hevalPerm

/- Paper equation (12): the same-monomial coefficient pairing of the
expanded cluster polynomial and the column selector is exactly the
permanent.  This proof is purely finite and does not use real stability. -/
theorem coefficientInnerProduct_cluster_selector_eq_permanent
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n) :
    coefficientInnerProduct (expandedClusterPolynomial A C)
      (columnSelector C.Cluster (Fin n)) = Matrix.permanent A := by
  let p := expandedClusterPolynomial A C
  let q := columnSelector C.Cluster (Fin n)
  change coefficientInnerProduct p q = Matrix.permanent A
  rw [coefficientInnerProduct, Finset.sum_filter]
  have hsum : (∑ d ∈ p.support, p.coeff d) = Matrix.permanent A := by
    simpa only [p] using sum_coeff_expandedClusterPolynomial_eq_permanent A C
  apply Eq.trans ?_ hsum
  apply Finset.sum_congr rfl
  intro d hd
  have hcoeff : q.coeff d = 1 :=
    columnSelector_coeff_of_mem_expandedClusterPolynomial A C hd
  have hmem : d ∈ q.support := by
    rw [mem_support_iff, hcoeff]
    norm_num
  simp [hmem, hcoeff]

/-- The two-row polynomial `Q_{rs}` from paper (9), written as a sum over
ordered off-diagonal pairs.  The two orientations of `{j,k}` contribute the
two terms in its coefficient. -/
noncomputable def pairPolynomial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ e ∈ (Finset.univ : Finset ι).offDiag,
    monomial (Finsupp.single e.1 1 + Finsupp.single e.2 1)
      (u e.1 * v e.2)

theorem single_add_single_one_eq_iff
    {ι : Type*} [DecidableEq ι]
    {a b j k : ι} (hab : a ≠ b) (hjk : j ≠ k) :
    Finsupp.single a 1 + Finsupp.single b 1 =
        Finsupp.single j 1 + Finsupp.single k 1 ↔
      (a = j ∧ b = k) ∨ (a = k ∧ b = j) := by
  rw [Finsupp.single_add_single_eq_single_add_single
    (one_ne_zero : (1 : ℕ) ≠ 0) (one_ne_zero : (1 : ℕ) ≠ 0)]
  simp [hab, hjk]

/-- The coefficient of `z_j z_k` is the combined weight of the two internal
assignments, exactly as stated below paper (9). -/
theorem pairPolynomial_coeff_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → ℝ) {j k : ι} (hjk : j ≠ k) :
    (pairPolynomial u v).coeff
      (Finsupp.single j 1 + Finsupp.single k 1) =
        u j * v k + u k * v j := by
  classical
  rw [pairPolynomial, coeff_sum]
  simp only [coeff_monomial]
  have hjkMem : (j, k) ∈ (Finset.univ : Finset ι).offDiag := by
    simp [hjk]
  have hkjMem : (k, j) ∈ (Finset.univ : Finset ι).offDiag := by
    simp [Ne.symm hjk]
  calc
    (∑ e ∈ (Finset.univ : Finset ι).offDiag,
        if Finsupp.single e.1 1 + Finsupp.single e.2 1 =
            Finsupp.single j 1 + Finsupp.single k 1 then
          u e.1 * v e.2 else 0) =
        ∑ e ∈ (Finset.univ : Finset ι).offDiag,
          if e = (j, k) ∨ e = (k, j) then u e.1 * v e.2 else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      have heNe : e.1 ≠ e.2 := (Finset.mem_offDiag.mp he).2.2
      have hiff :
          (Finsupp.single e.1 1 + Finsupp.single e.2 1 =
              Finsupp.single j 1 + Finsupp.single k 1) ↔
            e = (j, k) ∨ e = (k, j) := by
        rw [single_add_single_one_eq_iff heNe hjk]
        simp only [Prod.ext_iff]
      by_cases h : Finsupp.single e.1 1 + Finsupp.single e.2 1 =
          Finsupp.single j 1 + Finsupp.single k 1
      · simp [h, hiff.mp h]
      · have hnot : ¬(e = (j, k) ∨ e = (k, j)) := fun heq ↦ h (hiff.mpr heq)
        simp [h, hnot]
    _ = u j * v k + u k * v j := by
      rw [← Finset.sum_filter, Finset.filter_or,
        Finset.filter_eq' _ (j, k), Finset.filter_eq' _ (k, j)]
      simp [hjkMem, hkjMem, hjk]

/-- Evaluation of the pair polynomial in the ordered-pair form. -/
theorem pairPolynomial_eval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v z : ι → ℝ) :
    (pairPolynomial u v).eval z =
      ∑ e ∈ (Finset.univ : Finset ι).offDiag,
        u e.1 * v e.2 * z e.1 * z e.2 := by
  rw [pairPolynomial, eval_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [eval_monomial]
  rw [Finsupp.prod_add_index]
  · simp [Finsupp.prod_single_index, mul_assoc, mul_left_comm, mul_comm]
  · simp
  · intro a _ b c
    exact pow_add (z a) b c

theorem pairPolynomial_nonnegativeCoefficients
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u v : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    HasNonnegativeCoefficients (pairPolynomial u v) := by
  intro d
  rw [pairPolynomial, coeff_sum]
  apply Finset.sum_nonneg
  intro e _
  rw [coeff_monomial]
  split
  · exact mul_nonneg (hu e.1) (hv e.2)
  · exact le_rfl

theorem pairPolynomial_isHomogeneous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → ℝ) :
    (pairPolynomial u v).IsHomogeneous 2 := by
  rw [pairPolynomial]
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  apply isHomogeneous_monomial
  simp [map_add, Finsupp.degree_single]

theorem pairPolynomial_isMultiaffine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → ℝ) :
    IsMultiaffine (pairPolynomial u v) := by
  intro i
  rw [pairPolynomial]
  refine (degreeOf_sum_le i _ _).trans (Finset.sup_le ?_)
  intro e he
  have hne : e.1 ≠ e.2 := (Finset.mem_offDiag.mp he).2.2
  by_cases hc : u e.1 * v e.2 = 0
  · simp [hc]
  · rw [degreeOf_monomial_eq _ _ hc]
    by_cases hi : i = e.1
    · subst i
      simp [Finsupp.single_apply, hne]
    · by_cases hi' : i = e.2
      · subst i
        simp [Finsupp.single_apply, hne, Ne.symm hne]
      · simp [Finsupp.single_apply, hi, hi']

/-- The formal Hessian matrix of `Q(u,v)`: diagonal entries vanish because
the polynomial is multiaffine, while off-diagonal entries are the paired
coefficients. -/
def pairHessian
    {ι : Type*} [DecidableEq ι] (u v : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ if i = j then 0 else u i * v j + v i * u j

/-- Paper equation (11), the exact rank-two-minus-diagonal Hessian identity. -/
theorem pairHessian_eq
    {ι : Type*} [DecidableEq ι] (u v : ι → ℝ) :
    pairHessian u v =
      Matrix.vecMulVec u v + Matrix.vecMulVec v u -
        2 • Matrix.diagonal (fun i ↦ u i * v i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [pairHessian, Matrix.vecMulVec]
    ring
  · simp [pairHessian, Matrix.vecMulVec, Matrix.diagonal_apply, hij]

end BeyondBethe
