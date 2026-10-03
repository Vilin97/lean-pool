/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Spectral.GramClass

/-!
# The Spectral Lemma

Section 11.3 of `bs_lambda.txt`: `lambda(f)^2 ≤ c + 2 √((c-1) A B)` for a certificate family.

Write `G = gram F.ind` for the positive-side Gram matrix of a certificate family.
Section 11.2 (in `BSLambda/Spectral/GramClass.lean`) shows that every off-diagonal entry
of `G` is `0` or `1`, and that a nonzero entry `G x y` is *oriented*: exactly one of
`x, y` lies at distance one from the other's certificate.

Splitting `G` accordingly as `G = D + R + Rᵀ`, where `D` is the diagonal and `R` keeps
only the oriented entries, we get

* `‖D‖ ≤ c` because every diagonal entry is a sensitivity, bounded by the codimension;
* every row of `R` has at most `A (c-1)` nonzero entries — at most `A` certificates lie
  at distance one from `x`, and for each the partner `y` is a single flip of the
  projection `π_{C_j}(x)` at one of the `c` coordinates fixed by `C_i`, minus the flip
  that returns `x` itself;
* every column of `R` has at most `B` nonzero entries — at most `B` certificates lie at
  distance at most two from `y`, and each determines `x = π_{C_i}(y)`.

The Schur test (`BSLambda/Spectral/SchurTest.lean`) then gives `‖R‖ ≤ √(A(c-1)·B)`, and
`lam f ^ 2 ≤ ‖G‖ ≤ ‖D‖ + 2‖R‖`.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

public section

/-- A finite sum of reals that are each at most one is at most the number of nonzero terms.
This is a general `Finset` fact, stated here because Mathlib does not have it. -/
theorem Finset.sum_le_card_filter_ne_zero {α : Type*} (s : Finset α) {f : α → ℝ}
    (hf : ∀ a ∈ s, f a ≤ 1) : ∑ a ∈ s, f a ≤ ((s.filter fun a ↦ f a ≠ 0).card : ℝ) := by
  rw [← Finset.sum_filter_ne_zero]
  simpa using Finset.sum_le_card_nsmul _ _ 1 fun a ha ↦ hf a (Finset.mem_filter.1 ha).1

namespace BSLambda

namespace CertFamily

open scoped Matrix Matrix.Norms.L2Operator

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)

/-! ### The splitting `G = D + R + Rᵀ` -/

/-- The diagonal part `D` of the Gram matrix (Section 11.3). -/
noncomputable def diagMat : Matrix (Ones F.ind) (Ones F.ind) ℝ :=
  Matrix.diagonal (gram F.ind).diag

/-- The oriented off-diagonal part `R` of the Gram matrix: the entry `G x y` is kept only
when `x` lies at distance one from `y`'s certificate (Section 11.3). -/
@[expose]
noncomputable def offMat : Matrix (Ones F.ind) (Ones F.ind) ℝ := Matrix.of fun x y =>
  if F.owner x ≠ F.owner y ∧ (F.P (F.owner y)).dist x.1 = 1 then gram F.ind x y else 0

/-- The Schur-test bound `√(A (c-1) B)` on the oriented part (Section 11.3). -/
@[expose]
noncomputable def offBound : ℝ :=
  Real.sqrt (((F.A * (F.c - 1) : ℕ) : ℝ) * (F.B : ℝ))

/-- The defining formula for an entry of the diagonal part (Section 11.3). -/
theorem diagMat_apply (x y : Ones F.ind) :
    F.diagMat x y = if x = y then gram F.ind x x else 0 :=
  Matrix.diagonal_apply _ _ _

/-- The defining formula for an entry of the oriented part (Section 11.3). -/
theorem offMat_apply (x y : Ones F.ind) :
    F.offMat x y =
      if F.owner x ≠ F.owner y ∧ (F.P (F.owner y)).dist x.1 = 1 then gram F.ind x y else 0 :=
  rfl

/-- The entries of `R` are Gram entries or zero, hence nonnegative — one of the two
hypotheses of the Schur test (Section 11.3). -/
theorem offMat_nonneg (x y : Ones F.ind) : 0 ≤ F.offMat x y := by
  rw [F.offMat_apply]
  split_ifs
  exacts [gram_nonneg F.ind x y, le_rfl]

/-- The diagonal of `R` vanishes, since a point owns itself: this is what makes `D` in the
splitting `G = D + R + Rᵀ` carry the whole diagonal (Section 11.3). -/
theorem offMat_diag (x : Ones F.ind) : F.offMat x x = 0 := by
  rw [F.offMat_apply, ite_eq_right]
  exact fun h ↦ h.1 rfl

/-- The entries of `R` are at most one, by `gram_le_one`; this is what turns the row and
column *counts* of Section 11.3 into bounds on the row and column *sums*. -/
theorem offMat_le_one (x y : Ones F.ind) : F.offMat x y ≤ 1 := by
  rw [F.offMat_apply]
  split_ifs with h
  · exact F.gram_le_one (ne_of_apply_ne F.owner h.1)
  · exact zero_le_one

/-- Orientation is one-way: if `x` is a single flip away from `y`'s certificate, then `y`
is not a single flip away from `x`'s, because it is two flips away (Section 11.2). -/
private theorem dist_ne_one_of_dist_eq_one {x y : Ones F.ind} (hg : gram F.ind x y ≠ 0)
    (hd : (F.P (F.owner y)).dist x.1 = 1) : (F.P (F.owner x)).dist y.1 ≠ 1 := by
  rw [(F.dist_eq_two_of_dist_eq_one hg hd).1]
  omega

/-- Off the diagonal, `dist_eq_one_or_dist_eq_one` and `dist_ne_one_of_dist_eq_one` say that a
Gram entry is oriented in exactly one of the two directions, so it is picked up by exactly one
of `R` and `Rᵀ` (Section 11.3). -/
private theorem gram_eq_offMat_add_offMat {x y : Ones F.ind} (hxy : x ≠ y) :
    gram F.ind x y = F.offMat x y + F.offMat y x := by
  rw [F.offMat_apply, F.offMat_apply]
  by_cases hgram : gram F.ind x y = 0
  · rw [hgram, ← gram_comm x y, hgram, ite_self, ite_self, add_zero]
  have hown : F.owner x ≠ F.owner y := F.owner_ne_of_gram_ne_zero hxy hgram
  rcases F.dist_eq_one_or_dist_eq_one hxy hgram with hd | hd
  · rw [ite_eq_left ⟨hown, hd⟩, ite_eq_right fun h ↦ F.dist_ne_one_of_dist_eq_one hgram hd h.2,
      add_zero]
  · have hgram' : gram F.ind y x ≠ 0 := gram_comm x y ▸ hgram
    rw [ite_eq_right fun h ↦ F.dist_ne_one_of_dist_eq_one hgram' hd h.2,
      ite_eq_left ⟨hown.symm, hd⟩,
      zero_add, gram_comm]

/-- The splitting `G = D + R + Rᵀ` of the Gram matrix (Section 11.3). -/
theorem gram_eq_add : gram F.ind = F.diagMat + F.offMat + F.offMatᵀ := by
  ext x y
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.transpose_apply, F.diagMat_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [ite_eq_left rfl, F.offMat_diag, add_zero, add_zero]
  · rw [ite_eq_right hxy, zero_add]
    exact F.gram_eq_offMat_add_offMat hxy

/-! ### Counting the nonzero entries of `R` -/

/-- Reading off the three conditions hidden behind a nonzero entry of the oriented part
(Section 11.3). -/
theorem offMat_ne_zero_iff {x y : Ones F.ind} :
    F.offMat x y ≠ 0 ↔
      F.owner x ≠ F.owner y ∧ (F.P (F.owner y)).dist x.1 = 1 ∧ gram F.ind x y ≠ 0 := by
  rw [F.offMat_apply]
  split_ifs with h
  · exact ⟨fun hg ↦ ⟨h.1, h.2, hg⟩, fun hg ↦ hg.2.2⟩
  · exact ⟨fun hg ↦ absurd rfl hg, fun hg ↦ absurd ⟨hg.1, hg.2.1⟩ h⟩

/-- A nonzero oriented entry `R x y` identifies `x` as the projection of `y` onto `x`'s own
certificate; so within the column of `y` the owner determines the row (Section 11.3). -/
private theorem eq_proj_of_offMat_ne_zero {x y : Ones F.ind} (h : F.offMat x y ≠ 0) :
    x.1 = (F.P (F.owner x)).proj y.1 := by
  obtain ⟨-, hdist, hgram⟩ := F.offMat_ne_zero_iff.1 h
  exact (F.dist_eq_two_of_dist_eq_one hgram hdist).2

/-- For a fixed second owner `j`, at most `c - 1` inputs `y` give a nonzero oriented
entry in the row of `x`: each such `y` is a single flip of `π_{C_j}(x)` at a coordinate
fixed by `C_i`, and the flip that returns `x` itself is excluded
(Section 11.3, row bound). -/
theorem card_offMat_row_slice_le {x : Ones F.ind} {j : ι} (hj : j ≠ F.owner x)
    (hd : (F.P j).dist x.1 = 1) :
    (Finset.univ.filter fun y : Ones F.ind =>
      F.offMat x y ≠ 0 ∧ F.owner y = j).card ≤ F.c - 1 := by
  obtain ⟨p₀, hp₀mem, hp₀eq⟩ := F.exists_flip_proj_self (Ne.symm hj) (F.owner_sat x) hd
  have hmaps : ∀ y ∈ (Finset.univ.filter fun y : Ones F.ind ↦
        F.offMat x y ≠ 0 ∧ F.owner y = j), y.1 ∈
      ((F.P (F.owner x)).fixedSet.erase p₀).image fun p ↦ flipSet ((F.P j).proj x.1) {p} := by
    intro y hy
    rw [Finset.mem_filter_univ] at hy
    obtain ⟨hown, hdist, hgram⟩ := F.offMat_ne_zero_iff.1 hy.1
    have hxy : x ≠ y := ne_of_apply_ne F.owner hown
    obtain ⟨p, hpmem, hpeq⟩ := F.exists_flip_proj hgram hdist
    rw [hy.2] at hpeq
    refine Finset.mem_image.2 ⟨p, Finset.mem_erase.2 ⟨?_, hpmem⟩, hpeq.symm⟩
    rintro rfl
    exact hxy (Subtype.ext (hp₀eq.trans hpeq.symm))
  refine (Finset.card_le_card_of_injOn Subtype.val hmaps
    Subtype.coe_injective.injOn).trans (Finset.card_image_le.trans (le_of_eq ?_))
  rw [Finset.card_erase_of_mem hp₀mem, ← PartialAssign.codim_eq_card_fixedSet,
    F.codim_eq (F.owner x)]

/-- Every row of the oriented part has at most `A (c - 1)` nonzero entries: the row splits
into at most `A` slices, one per certificate at distance one from `x`, and
`card_offMat_row_slice_le` bounds each slice (Section 11.3, row bound). -/
theorem card_offMat_row_le (x : Ones F.ind) :
    (Finset.univ.filter fun y : Ones F.ind => F.offMat x y ≠ 0).card
      ≤ F.A * (F.c - 1) := by
  have hmaps : ∀ y ∈ (Finset.univ.filter fun y : Ones F.ind ↦ F.offMat x y ≠ 0),
      F.owner y ∈ Finset.univ.filter fun j ↦ j ≠ F.owner x ∧ (F.P j).dist x.1 = 1 := by
    intro y hy
    rw [Finset.mem_filter_univ] at hy ⊢
    obtain ⟨hown, hdist, -⟩ := F.offMat_ne_zero_iff.1 hy
    exact ⟨Ne.symm hown, hdist⟩
  have hslice : ∀ j ∈ Finset.univ.filter fun j ↦ j ≠ F.owner x ∧ (F.P j).dist x.1 = 1,
      ((Finset.univ.filter fun y : Ones F.ind ↦ F.offMat x y ≠ 0).filter
        fun y ↦ F.owner y = j).card ≤ F.c - 1 := by
    intro j hj
    rw [Finset.mem_filter_univ] at hj
    rw [Finset.filter_filter]
    exact F.card_offMat_row_slice_le hj.1 hj.2
  refine (Finset.card_le_mul_card_image_of_maps_to hmaps _ hslice).trans ?_
  rw [mul_comm]
  exact Nat.mul_le_mul_right _ (F.listOne (F.owner x) x.1 (F.owner_sat x))

/-- Every column of the oriented part has at most `B` nonzero entries: every row index `x`
of the column of `y` has a distinct owner, at distance two from `y`, and `listTwo` bounds the
number of those (Section 11.3, column bound). -/
theorem card_offMat_col_le (y : Ones F.ind) :
    (Finset.univ.filter fun x : Ones F.ind => F.offMat x y ≠ 0).card ≤ F.B := by
  refine (Finset.card_le_card_of_injOn F.owner ?_ ?_).trans
    (F.listTwo (F.owner y) y.1 (F.owner_sat y))
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter_univ] at hx ⊢
    obtain ⟨hown, hdist, hgram⟩ := F.offMat_ne_zero_iff.1 hx
    exact ⟨hown, (F.dist_eq_two_of_dist_eq_one hgram hdist).1.le⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter_univ] at hx₁ hx₂
    refine Subtype.ext ?_
    rw [F.eq_proj_of_offMat_ne_zero hx₁, heq, ← F.eq_proj_of_offMat_ne_zero hx₂]

/-! ### The Schur test and the Spectral Lemma -/

/-- Every row sum of the oriented part is at most `A (c - 1)`: the entries are at most one,
so the sum is at most the count of `card_offMat_row_le` (Section 11.3). -/
theorem offMat_row_sum_le (x : Ones F.ind) :
    ∑ y, F.offMat x y ≤ ((F.A * (F.c - 1) : ℕ) : ℝ) :=
  (Finset.sum_le_card_filter_ne_zero _ fun y _ ↦ F.offMat_le_one x y).trans
    (by exact_mod_cast F.card_offMat_row_le x)

/-- Every column sum of the oriented part is at most `B`: the entries are at most one, so
the sum is at most the count of `card_offMat_col_le` (Section 11.3). -/
theorem offMat_col_sum_le (y : Ones F.ind) :
    ∑ x, F.offMat x y ≤ (F.B : ℝ) :=
  (Finset.sum_le_card_filter_ne_zero _ fun x _ ↦ F.offMat_le_one x y).trans
    (by exact_mod_cast F.card_offMat_col_le y)

/-- The diagonal part has operator norm at most the codimension `c`: the L2 operator norm of
a diagonal matrix is the supremum norm of its diagonal, and `gram_diag_le` bounds every Gram
diagonal entry by `c` (Section 11.3). -/
theorem l2_opNorm_diagMat_le : ‖F.diagMat‖ ≤ (F.c : ℝ) := by
  rw [diagMat, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun x ↦ ?_
  rw [Matrix.diag_apply, Real.norm_eq_abs, abs_of_nonneg (gram_nonneg F.ind x x)]
  exact F.gram_diag_le x

/-- The Schur test applied to `R`, with the row bound `A (c-1)` and the column bound `B`
(Section 11.3). -/
theorem l2_opNorm_offMat_le : ‖F.offMat‖ ≤ F.offBound :=
  Matrix.l2_opNorm_le_sqrt_of_row_col_sums F.offMat F.offMat_nonneg F.offMat_row_sum_le
    F.offMat_col_sum_le

/-- The transpose of `R` obeys the same bound, since transposition preserves the L2 operator
norm (Section 11.3). -/
theorem l2_opNorm_offMat_transpose_le : ‖F.offMatᵀ‖ ≤ F.offBound :=
  F.offMat.l2_opNorm_transpose.trans_le F.l2_opNorm_offMat_le

/-- The triangle inequality on the splitting `G = D + R + Rᵀ` (Section 11.3). -/
theorem l2_opNorm_gram_le : ‖gram F.ind‖ ≤ (F.c : ℝ) + 2 * F.offBound := by
  rw [F.gram_eq_add, two_mul, ← add_assoc]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add F.l2_opNorm_diagMat_le F.l2_opNorm_offMat_le))
    F.l2_opNorm_offMat_transpose_le)

/-- **The Spectral Lemma** (Section 11.3): `lambda(f)^2 ≤ c + 2 √(A (c-1) B)`.  Combining
`lam_sq_le_l2_opNorm_gram` with the norm bound on `G`. -/
theorem lam_sq_le : lam F.ind ^ 2 ≤ (F.c : ℝ) + 2 * F.offBound :=
  le_trans (lam_sq_le_l2_opNorm_gram F.ind) F.l2_opNorm_gram_le

/-- The Spectral Lemma with `offBound` unfolded and the subtraction taken in `ℝ` rather than
in `ℕ`, which is how Section 11.3 displays it. Nothing downstream needs this form — `lam_sq_le`
is the one the development uses — but it is the statement free of a truncated subtraction. -/
theorem lam_sq_le_sqrt (hc : 1 ≤ F.c) :
    lam F.ind ^ 2 ≤ (F.c : ℝ) + 2 * Real.sqrt (((F.c : ℝ) - 1) * F.A * F.B) := by
  refine F.lam_sq_le.trans_eq ?_
  rw [offBound, Nat.cast_mul, Nat.cast_sub hc, Nat.cast_one]
  ring_nf

end CertFamily

end BSLambda
