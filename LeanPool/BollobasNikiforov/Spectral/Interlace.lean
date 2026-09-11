/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.BollobasNikiforov.Basic.Spectrum
import LeanPool.BollobasNikiforov.Definition
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Noncomplete graphs and the two largest adjacency eigenvalues

A missing edge gives a vanishing 2x2 principal submatrix of the adjacency
matrix. Courant-Fischer on that coordinate plane yields `lambda2 G ≥ 0` when `G`
is not complete, and therefore `F(A_G) = lambda1 G ^ 2 + lambda2 G ^ 2`. The
largest eigenvalue is nonnegative for every finite graph, complete or not.
-/

namespace BollobasNikiforov

open Matrix Module WithLp


variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### SP13 — A nonedge gives a zero principal 2x2 -/

omit [Fintype V] in
/-- The principal 2x2 submatrix of the adjacency matrix on a nonedge is
identically zero. -/
lemma adjMatrix_eq_zero_on_nonedge_pair {i j : V} (hij : i ≠ j) (hna : ¬ G.Adj i j)
    {a b : V} (ha : a ∈ ({i, j} : Finset V)) (hb : b ∈ ({i, j} : Finset V)) :
    G.adjMatrix ℝ a b = 0 := by
  rw [SimpleGraph.adjMatrix_apply]
  split_ifs with hab
  · exfalso
    have habne : a ≠ b := hab.ne
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact habne rfl
    · exact hna hab
    · exact hna hab.symm
    · exact habne rfl
  · rfl

/-- The adjacency quadratic form vanishes on vectors supported on a nonedge. -/
lemma dotProduct_mulVec_adjMatrix_eq_zero_of_supported_on_nonedge
    {i j : V} (hij : i ≠ j) (hna : ¬ G.Adj i j) {x : V → ℝ}
    (hx : ∀ v, v ∉ ({i, j} : Finset V) → x v = 0) :
    x ⬝ᵥ G.adjMatrix ℝ *ᵥ x = 0 := by
  rw [dot_mulVec_eq_sum_sum]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  by_cases ha : a ∈ ({i, j} : Finset V)
  · by_cases hb : b ∈ ({i, j} : Finset V)
    · rw [adjMatrix_eq_zero_on_nonedge_pair G hij hna hb ha]
      simp
    · simp [hx b hb]
  · simp [hx a ha]

/-! ### SP14 — Rayleigh on a 2-dimensional coordinate subspace -/

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ}

/-- Euclidean inner product on coordinate space. Avoids the `BollobasNikiforov.inner` name clash. -/
noncomputable def euclInner (x y : EuclideanSpace ℝ n) : ℝ :=
  Inner.inner (𝕜 := ℝ) x y

omit [DecidableEq n] in
lemma euclInner_smul_right (x y : EuclideanSpace ℝ n) (c : ℝ) :
    euclInner x (c • y) = c * euclInner x y :=
  real_inner_smul_right x y c

/-- The Euclidean quadratic form expands in the ordered eigenbasis. -/
lemma dotProduct_mulVec_eq_sum_eigenvalues₀ (hA : A.IsHermitian) (x : n → ℝ) :
    x ⬝ᵥ A *ᵥ x =
      ∑ i, hA.eigenvalues₀ i *
        euclInner ((isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis
          finrank_euclideanSpace i) (toLp 2 x) ^ 2 := by
  let hT := (isSymmetric_toEuclideanLin_iff (A := A)).mpr hA
  let b := hT.eigenvectorBasis finrank_euclideanSpace
  let xE : EuclideanSpace ℝ n := toLp 2 x
  have hinter : euclInner xE (A.toEuclideanLin xE) = x ⬝ᵥ A *ᵥ x := by
    simp only [euclInner, xE]
    change Inner.inner (𝕜 := ℝ) (toLp 2 x) (toLp 2 (A *ᵥ x)) = _
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct_comm]
  have hTx : A.toEuclideanLin xE =
      ∑ i, (hA.eigenvalues₀ i * Inner.inner (𝕜 := ℝ) (b i) xE) • b i := by
    conv_lhs => rw [← b.sum_repr' xE]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hT.apply_eigenvectorBasis, smul_smul, mul_comm]
    rfl
  simp only [euclInner] at hinter ⊢
  rw [← hinter, hTx, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right xE (b i), real_inner_comm xE]
  ring

/-- On the orthogonal complement of a top eigenvector, the Rayleigh form is at
most `lambdaSecond`. -/
lemma dotProduct_mulVec_le_lambdaSecond_of_orthogonal (hA : A.IsHermitian)
    [Nontrivial n] {x : n → ℝ} (hx : ∑ k, x k ^ 2 = 1)
    (horth :
      euclInner ((isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace
          ⟨0, Fintype.card_pos⟩)
        (toLp 2 x) = 0) :
    x ⬝ᵥ A *ᵥ x ≤ lambdaSecond hA := by
  rw [dotProduct_mulVec_eq_sum_eigenvalues₀ hA]
  let b := (isSymmetric_toEuclideanLin_iff (A := A)).mpr hA |>.eigenvectorBasis
    finrank_euclideanSpace
  let i0 : Fin (Fintype.card n) := ⟨0, Fintype.card_pos⟩
  let i1 : Fin (Fintype.card n) := ⟨1, Fintype.one_lt_card⟩
  have hsumc : ∑ i, euclInner (b i) (toLp 2 x) ^ 2 = 1 := by
    have hnorm : ‖b.repr (toLp 2 x)‖ = ‖toLp 2 x‖ := b.repr.norm_map _
    have hE : ‖toLp 2 x‖ ^ 2 = ∑ k, x k ^ 2 :=
      EuclideanSpace.real_norm_sq_eq (toLp 2 x)
    have hrepr : ‖b.repr (toLp 2 x)‖ ^ 2 = ∑ i, euclInner (b i) (toLp 2 x) ^ 2 := by
      simpa [euclInner, OrthonormalBasis.repr_apply_apply] using
        EuclideanSpace.real_norm_sq_eq (b.repr (toLp 2 x))
    rw [← hrepr, hnorm, hE, hx]
  have hz : euclInner (b i0) (toLp 2 x) ^ 2 = 0 :=
    sq_eq_zero_iff.mpr (by simpa [i0, b] using horth)
  have hrest : ∑ i ∈ Finset.univ.erase i0, euclInner (b i) (toLp 2 x) ^ 2 = 1 := by
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun i => euclInner (b i) (toLp 2 x) ^ 2) (Finset.mem_univ i0)
    rw [hsumc, hz, add_zero] at hsplit
    exact hsplit
  have hle : ∀ i ∈ Finset.univ.erase i0,
      hA.eigenvalues₀ i * euclInner (b i) (toLp 2 x) ^ 2 ≤
        lambdaSecond hA * euclInner (b i) (toLp 2 x) ^ 2 := by
    intro i hi
    have hi0 : i ≠ i0 := Finset.ne_of_mem_erase hi
    have h01 : i1 ≤ i := by
      refine Fin.le_iff_val_le_val.mpr ?_
      have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero this)
    exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone h01) (sq_nonneg _)
  calc
    ∑ i, hA.eigenvalues₀ i * euclInner (b i) (toLp 2 x) ^ 2
        = hA.eigenvalues₀ i0 * euclInner (b i0) (toLp 2 x) ^ 2 +
            ∑ i ∈ Finset.univ.erase i0,
              hA.eigenvalues₀ i * euclInner (b i) (toLp 2 x) ^ 2 := by
          rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i0)]
    _ = ∑ i ∈ Finset.univ.erase i0,
          hA.eigenvalues₀ i * euclInner (b i) (toLp 2 x) ^ 2 := by
          simp [hz]
    _ ≤ ∑ i ∈ Finset.univ.erase i0,
          lambdaSecond hA * euclInner (b i) (toLp 2 x) ^ 2 :=
          Finset.sum_le_sum hle
    _ = lambdaSecond hA * ∑ i ∈ Finset.univ.erase i0,
          euclInner (b i) (toLp 2 x) ^ 2 := by
          rw [Finset.mul_sum]
    _ = lambdaSecond hA := by simp [hrest]

/-- A unit vector in `span {e i, e j}` orthogonal to a top eigenvector. -/
lemma exists_l2_mem_span_single_pair_orthogonal (hA : A.IsHermitian)
    [Nontrivial n] {i j : n} (hij : i ≠ j) :
    ∃ x : n → ℝ,
      x ∈ Submodule.span ℝ ({Pi.single i (1 : ℝ), Pi.single j 1} : Set (n → ℝ)) ∧
        ∑ k, x k ^ 2 = 1 ∧
        euclInner ((isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace
            ⟨0, Fintype.card_pos⟩)
          (toLp 2 x) = 0 := by
  let b := (isSymmetric_toEuclideanLin_iff (A := A)).mpr hA |>.eigenvectorBasis
    finrank_euclideanSpace
  let u := ofLp (b ⟨0, Fintype.card_pos⟩)
  let y : n → ℝ :=
    if u i = 0 ∧ u j = 0 then Pi.single i (1 : ℝ)
    else u j • Pi.single i (1 : ℝ) + (-u i) • Pi.single j (1 : ℝ)
  have hyW : y ∈ Submodule.span ℝ
      ({Pi.single i (1 : ℝ), Pi.single j 1} : Set (n → ℝ)) := by
    dsimp [y]
    split_ifs
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hy0 : y ≠ 0 := by
    dsimp [y]
    split_ifs with hu
    · intro hy
      simpa using congrFun hy i
    · intro hy
      have hi := congrFun hy i
      have hj := congrFun hy j
      simp only [neg_smul, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
        Pi.neg_apply, Pi.single_eq_of_ne hij, mul_zero, neg_zero, add_zero, Pi.zero_apply,
        Pi.single_eq_of_ne hij.symm, zero_add, neg_eq_zero] at hi hj
      exact hu ⟨hj, hi⟩
  have hysum : ∑ k, y k ^ 2 ≠ 0 := by
    intro h
    apply hy0
    ext k
    have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h k
      (Finset.mem_univ _)
    exact sq_eq_zero_iff.mp hk
  have hysum0 : 0 < ∑ k, y k ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) hysum.symm
  let s := Real.sqrt (∑ k, y k ^ 2)
  let x : n → ℝ := s⁻¹ • y
  refine ⟨x, Submodule.smul_mem _ _ hyW, ?_, ?_⟩
  · change ∑ k, (s⁻¹ * y k) ^ 2 = 1
    simp_rw [mul_pow, ← Finset.mul_sum]
    rw [inv_pow, Real.sq_sqrt (le_of_lt hysum0), inv_mul_cancel₀ hysum]
  · have hyorth : euclInner (b ⟨0, Fintype.card_pos⟩) (toLp 2 y) = 0 := by
      have huE : toLp 2 u = b ⟨0, Fintype.card_pos⟩ := by
        simp [u]
      have hinner : euclInner (toLp 2 u) (toLp 2 y) = y ⬝ᵥ u :=
        EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) u y
      rw [← huE, hinner]
      dsimp [y]
      split_ifs with hu
      · simp [dotProduct, Pi.single_apply, hu.1]
      · simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul]
        rw [Finset.sum_add_distrib]
        simp [Pi.single_apply, mul_ite]
        ring
    have hxE : toLp 2 x = s⁻¹ • toLp 2 y := by
      simp [x]
    rw [hxE, euclInner_smul_right, hyorth, mul_zero]

/-- Rayleigh values of unit vectors in `span {e i, e j}`. -/
def rayleighOnSpanPair (A : Matrix n n ℝ) (i j : n) : Set ℝ :=
  { t | ∃ x : n → ℝ,
      x ∈ Submodule.span ℝ ({Pi.single i (1 : ℝ), Pi.single j 1} : Set (n → ℝ)) ∧
        ∑ k, x k ^ 2 = 1 ∧ t = x ⬝ᵥ A *ᵥ x }

lemma nonempty_rayleighOnSpanPair {i j : n} :
    (rayleighOnSpanPair A i j).Nonempty := by
  refine ⟨Pi.single i (1 : ℝ) ⬝ᵥ A *ᵥ Pi.single i 1,
    Pi.single i (1 : ℝ), Submodule.subset_span (Set.mem_insert _ _), ?_, rfl⟩
  rw [Fintype.sum_eq_single i]
  · simp
  · intro k hk
    simp [hk]

lemma bddBelow_rayleighOnSpanPair {i j : n} :
    BddBelow (rayleighOnSpanPair A i j) := by
  refine ⟨-∑ a, ∑ b, |A a b|, ?_⟩
  rintro _ ⟨x, -, hx, rfl⟩
  have hx1 : ∀ k, |x k| ≤ 1 := fun k => by
    have : x k ^ 2 ≤ 1 :=
      (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ k)).trans_eq hx
    exact (sq_le_one_iff_abs_le_one (a := x k)).1 this
  have habs : |x ⬝ᵥ A *ᵥ x| ≤ ∑ a, ∑ b, |A a b| := by
    rw [dot_mulVec_eq_sum_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun a _ => ?_
    rw [abs_mul, abs_mul]
    calc
      |x a| * |A a b| * |x b| ≤ 1 * |A a b| * 1 := by gcongr <;> apply hx1
      _ = |A a b| := by simp
  exact neg_le_of_abs_le habs

/-- **SP14.** Courant-Fischer comparison on a coordinate 2-plane:
`lambdaSecond` is at least the infimum of the Rayleigh form on `span {e i, e j}`. -/
lemma lambdaSecond_ge_sInf_span_single_pair (hA : A.IsHermitian)
    [Nontrivial n] {i j : n} (hij : i ≠ j) :
    sInf (rayleighOnSpanPair A i j) ≤ lambdaSecond hA := by
  obtain ⟨x, hxW, hx1, horth⟩ := exists_l2_mem_span_single_pair_orthogonal hA hij
  have hxle := dotProduct_mulVec_le_lambdaSecond_of_orthogonal hA hx1 horth
  have hmem : x ⬝ᵥ A *ᵥ x ∈ rayleighOnSpanPair A i j := ⟨x, hxW, hx1, rfl⟩
  exact (csInf_le bddBelow_rayleighOnSpanPair hmem).trans hxle

/-- If the Rayleigh form is nonnegative on the coordinate 2-plane, then
`0 ≤ lambdaSecond`. -/
lemma lambdaSecond_nonneg_of_rayleighOnSpanPair_nonneg (hA : A.IsHermitian)
    [Nontrivial n] {i j : n} (hij : i ≠ j)
    (hnn : ∀ t ∈ rayleighOnSpanPair A i j, 0 ≤ t) :
    0 ≤ lambdaSecond hA :=
  (le_csInf nonempty_rayleighOnSpanPair hnn).trans
    (lambdaSecond_ge_sInf_span_single_pair hA hij)

/-- If the quadratic form vanishes on `span {e i, e j}`, then `0 ≤ lambdaSecond`. -/
lemma lambdaSecond_nonneg_of_quadForm_eq_zero_on_span (hA : A.IsHermitian)
    [Nontrivial n] {i j : n} (hij : i ≠ j)
    (h0 : ∀ x : n → ℝ,
      x ∈ Submodule.span ℝ ({Pi.single i (1 : ℝ), Pi.single j 1} : Set (n → ℝ)) →
        x ⬝ᵥ A *ᵥ x = 0) :
    0 ≤ lambdaSecond hA := by
  refine lambdaSecond_nonneg_of_rayleighOnSpanPair_nonneg hA hij ?_
  rintro _ ⟨x, hxW, -, rfl⟩
  simp [h0 x hxW]

omit [Fintype n] in
lemma mem_span_single_pair_support {i j : n} {x : n → ℝ}
    (hx : x ∈ Submodule.span ℝ ({Pi.single i (1 : ℝ), Pi.single j 1} : Set (n → ℝ)))
    {v : n} (hvi : v ≠ i) (hvj : v ≠ j) : x v = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  simp [hvi, hvj]

/-! ### SP15 — `lambda2 G ≥ 0` if `G` is not complete -/

lemma lambda2_eq_lambdaSecond [Nontrivial V] :
    lambda2 G = lambdaSecond (G.isHermitian_adjMatrix ℝ) :=
  rfl

lemma lambda1_eq_lambdaMax [Nonempty V] :
    lambda1 G = lambdaMax (G.isHermitian_adjMatrix ℝ) :=
  rfl

/-- **SP15.** A noncomplete graph on at least two vertices has `lambda2 ≥ 0`. -/
lemma lambda2_nonneg [Nontrivial V] (hG : G ≠ ⊤) : 0 ≤ lambda2 G := by
  obtain ⟨i, j, hij, hna⟩ := SimpleGraph.ne_top_iff_exists_not_adj.mp hG
  rw [lambda2_eq_lambdaSecond]
  refine lambdaSecond_nonneg_of_quadForm_eq_zero_on_span
    (G.isHermitian_adjMatrix ℝ) hij fun x hx => ?_
  refine dotProduct_mulVec_adjMatrix_eq_zero_of_supported_on_nonedge G hij hna ?_
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  exact mem_span_single_pair_support hx hv.1 hv.2

/-! ### SP17 — `lambda1 G ≥ 0` -/

/-- **SP17.** The largest adjacency eigenvalue is nonnegative. -/
lemma lambda1_nonneg [Nonempty V] : 0 ≤ lambda1 G := by
  let hA := G.isHermitian_adjMatrix ℝ
  have hsum : ∑ i, hA.eigenvalues i = 0 := by
    have htr : (G.adjMatrix ℝ).trace = ∑ i, (hA.eigenvalues i : ℝ) :=
      hA.trace_eq_sum_eigenvalues
    have hz : (G.adjMatrix ℝ).trace = 0 := G.trace_adjMatrix ℝ
    simpa [hz] using htr.symm
  have hle : ∀ i : V, hA.eigenvalues i ≤ lambda1 G := fun i => by
    simpa [lambda1, adjacencyEigenvalues₀, IsHermitian.eigenvalues] using
      hA.eigenvalues₀_antitone (Fin.zero_le _)
  have hbound : ∑ i, hA.eigenvalues i ≤ ∑ _i : V, lambda1 G :=
    Finset.sum_le_sum fun i _ => hle i
  rw [hsum, Finset.sum_const, nsmul_eq_mul] at hbound
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  exact (mul_nonneg_iff_of_pos_left hn).1 hbound

/-! ### SP16 — `F(A_G) = lambda1^2 + lambda2^2` for noncomplete `G` -/

lemma lambdaSecond_le_lambdaMax (hA : A.IsHermitian) [Nontrivial n] :
    lambdaSecond hA ≤ lambdaMax hA :=
  hA.eigenvalues₀_antitone (Fin.zero_le _)

/-- **SP16.** On a noncomplete graph the positive-part squares in `F` are
`lambda1 ^ 2` and `lambda2 ^ 2`. -/
lemma F_adjMatrix_eq [Nontrivial V] (hG : G ≠ ⊤) :
    F (G.isHermitian_adjMatrix ℝ) = lambda1 G ^ 2 + lambda2 G ^ 2 := by
  let hA := G.isHermitian_adjMatrix ℝ
  have h2 : 0 ≤ lambdaSecond hA := by
    simpa [lambda2_eq_lambdaSecond] using lambda2_nonneg G hG
  have h1 : lambdaSecond hA ≤ lambdaMax hA := lambdaSecond_le_lambdaMax hA
  rw [F_eq, lambda1_eq_lambdaMax, lambda2_eq_lambdaSecond, max_eq_left (h2.trans h1),
    max_eq_left h2]

end BollobasNikiforov
