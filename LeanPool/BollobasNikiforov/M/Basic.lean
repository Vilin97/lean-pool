/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.BollobasNikiforov.Basic.Inner
import LeanPool.BollobasNikiforov.CP.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Lattice

/-!
# The matrix `M(X)` of `eq:matrix`

For a real matrix `X`,
`M X = X ⊙ X + ∑_{i<j} (if X i j < 0 then (X i j)² else 0) • vecMulVec (e i - e j) (e i - e j)`.
When `X` is positive semidefinite this is PSD and entrywise nonnegative.
-/

namespace BollobasNikiforov

open Matrix Finset
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

noncomputable section

/-! ### MX01 — definition of `M` -/

/-- The correction weight on the pair `{i,j}`: `(X i j)²` when `i < j` and the
entry is negative, and `0` otherwise. -/
def laplacianCoeff (X : Matrix n n ℝ) (i j : n) : ℝ :=
  if i < j ∧ X i j < 0 then (X i j) ^ 2 else 0

/-- The map of `docs/sol.tex` (eq:matrix). -/
def M (X : Matrix n n ℝ) : Matrix n n ℝ :=
  X ⊙ X + ∑ i, ∑ j, laplacianCoeff X i j • vecMulVec (e i - e j) (e i - e j)

/-- The all-ones matrix, used as the Frobenius partner of `M`. -/
def ones : Matrix n n ℝ :=
  of fun _ _ => 1

omit [Fintype n] [DecidableEq n] in
lemma laplacianCoeff_nonneg (X : Matrix n n ℝ) (i j : n) :
    0 ≤ laplacianCoeff X i j := by
  unfold laplacianCoeff
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

lemma M_apply (X : Matrix n n ℝ) (a b : n) :
    M X a b =
      X a b * X a b +
        ∑ i, ∑ j, laplacianCoeff X i j *
          vecMulVec (e i - e j) (e i - e j) a b := by
  simp [M, hadamard_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply]

/-! ### Helpers for the rank-one Laplacian -/

omit [Fintype n] [LinearOrder n] in
/-- Off-diagonal entries of `vecMulVec (e p - e q) (e p - e q)`. -/
lemma vecMulVec_sub_single_offDiag {p q i j : n} (hij : i ≠ j) :
    vecMulVec (e p - e q) (e p - e q) i j =
      if p = i ∧ q = j then (-1 : ℝ)
      else if p = j ∧ q = i then -1
      else 0 := by
  rcases eq_or_ne p q with hpq | hpq
  · subst hpq
    simp only [sub_self, vecMulVec_apply, Pi.zero_apply, mul_zero]
    have hii : ¬ (p = i ∧ p = j) := fun h ↦ hij (h.1.symm.trans h.2)
    have hjj : ¬ (p = j ∧ p = i) := fun h ↦ hij (h.2.symm.trans h.1)
    simp [hii, hjj]
  · rw [vecMulVec_sub_single_apply hpq]
    have hii : ¬ (i = p ∧ j = p) := fun h ↦ hij (h.1.trans h.2.symm)
    have hjj : ¬ (i = q ∧ j = q) := fun h ↦ hij (h.1.trans h.2.symm)
    simp only [hii, hjj, ite_false]
    have hA : (i = p ∧ j = q) ↔ (p = i ∧ q = j) :=
      ⟨fun ⟨hp, hq⟩ ↦ ⟨hp.symm, hq.symm⟩, fun ⟨hp, hq⟩ ↦ ⟨hp.symm, hq.symm⟩⟩
    have hB : (i = q ∧ j = p) ↔ (p = j ∧ q = i) :=
      ⟨fun ⟨hp, hq⟩ ↦ ⟨hq.symm, hp.symm⟩, fun ⟨hp, hq⟩ ↦ ⟨hq.symm, hp.symm⟩⟩
    simp only [hA, hB]

omit [LinearOrder n] in
lemma sum_sum_ite_eq_pair (f : n → n → ℝ) (i j : n) :
    ∑ p, ∑ q, (if p = i ∧ q = j then f p q else 0) = f i j := by
  simp [ite_and, sum_ite_eq']

lemma laplacianCoeff_correction_offDiag (X : Matrix n n ℝ) {i j : n} (hij : i ≠ j) :
    ∑ p, ∑ q, laplacianCoeff X p q * vecMulVec (e p - e q) (e p - e q) i j =
      - laplacianCoeff X i j - laplacianCoeff X j i := by
  simp_rw [vecMulVec_sub_single_offDiag hij]
  have hdecomp (p q : n) :
      laplacianCoeff X p q *
          (if p = i ∧ q = j then (-1 : ℝ) else if p = j ∧ q = i then -1 else 0) =
        (if p = i ∧ q = j then -laplacianCoeff X i j else 0) +
          (if p = j ∧ q = i then -laplacianCoeff X j i else 0) := by
    by_cases h1 : p = i ∧ q = j
    · simp only [h1, and_self, ↓reduceIte, mul_neg, mul_one, left_eq_add, ite_eq_right_iff,
      neg_eq_zero, and_imp]
      exact fun h_eq _ ↦ (hij h_eq).elim
    · by_cases h2 : p = j ∧ q = i
      · simp only [h2, and_self, ↓reduceIte, ite_self, mul_neg, mul_one, right_eq_add,
        ite_eq_right_iff, neg_eq_zero, and_imp]
        exact fun h_eq _ ↦ (hij h_eq.symm).elim
      · simp [h1, h2]
  simp_rw [hdecomp, sum_add_distrib]
  rw [sum_sum_ite_eq_pair, sum_sum_ite_eq_pair]
  ring

/-! ### MX03 — off-diagonal formula -/

/-- For `i ≠ j` and symmetric `X`, `M X i j = (max (X i j) 0)²`. -/
lemma M_apply_of_ne (X : Matrix n n ℝ) (hX : X.IsSymm) {i j : n} (hij : i ≠ j) :
    M X i j = posPart X i j ^ 2 := by
  rw [M_apply, laplacianCoeff_correction_offDiag X hij]
  rcases lt_or_gt_of_ne hij with hij | hji
  · have : ¬ j < i := not_lt.mpr hij.le
    simp only [laplacianCoeff, hij, true_and, this, false_and, ↓reduceIte, sub_zero, posPart_apply]
    split_ifs with hneg
    · rw [max_eq_right hneg.le]; ring
    · rw [max_eq_left (not_lt.mp hneg)]; ring
  · have : ¬ i < j := not_lt.mpr hji.le
    have hsym : X j i = X i j := hX.apply i j
    simp only [laplacianCoeff, this, false_and, ↓reduceIte, neg_zero, hji, true_and, zero_sub,
      posPart_apply]
    rw [hsym]
    split_ifs with hneg
    · rw [max_eq_right hneg.le]; ring
    · rw [max_eq_left (not_lt.mp hneg)]; ring

/-! ### MX02 — PSD and entrywise nonnegativity -/

lemma M_posSemidef {X : Matrix n n ℝ} (hX : X.PosSemidef) : (M X).PosSemidef := by
  unfold M
  refine (posSemidef_hadamard_self hX).add ?_
  exact posSemidef_sum _ fun i _ ↦ posSemidef_sum _ fun j _ ↦
    (posSemidef_vecMulVec_self (e i - e j)).smul (laplacianCoeff_nonneg X i j)

lemma M_nonneg {X : Matrix n n ℝ} (hX : X.PosSemidef) (i j : n) : 0 ≤ M X i j := by
  rcases eq_or_ne i j with rfl | hij
  · rw [M_apply]
    refine add_nonneg (mul_self_nonneg _) (sum_nonneg fun p _ ↦ sum_nonneg fun q _ ↦ ?_)
    exact mul_nonneg (laplacianCoeff_nonneg X p q)
      (by simpa [vecMulVec_apply] using mul_self_nonneg ((e p - e q) i))
  · have hS : X.IsSymm := isHermitian_iff_isSymm.mp hX.isHermitian
    rw [M_apply_of_ne X hS hij]
    exact sq_nonneg _

/-! ### MX04 — all-ones identities -/

omit [DecidableEq n] [LinearOrder n] in
lemma inner_sum_right {ι : Type*} (B : Matrix n n ℝ) (s : Finset ι)
    (f : ι → Matrix n n ℝ) :
    inner B (∑ i ∈ s, f i) = ∑ i ∈ s, inner B (f i) := by
  simp [inner, mul_sum, trace_sum]

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
lemma isSymm_ones : (ones : Matrix n n ℝ).IsSymm := by
  ext
  simp [ones]

omit [LinearOrder n] in
lemma sub_single_dotProduct_one (i j : n) :
    (e i - e j) ⬝ᵥ (1 : n → ℝ) = 0 := by
  simp [e, Pi.sub_apply, dotProduct, Pi.single_apply]

omit [LinearOrder n] in
lemma vecMulVec_sub_single_mulVec_one (i j : n) :
    vecMulVec (e i - e j) (e i - e j) *ᵥ (1 : n → ℝ) = 0 := by
  rw [vecMulVec_mulVec, sub_single_dotProduct_one]
  simp

omit [LinearOrder n] in
lemma inner_ones_vecMulVec_sub_single (i j : n) :
    inner (ones : Matrix n n ℝ) (vecMulVec (e i - e j) (e i - e j)) = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · simp [sub_self, inner]
  · rw [inner_vecMulVec_sub_single isSymm_ones hij]
    simp [ones]; norm_num

omit [DecidableEq n] [LinearOrder n] in
lemma inner_ones_hadamard_self (X : Matrix n n ℝ) :
    inner (ones : Matrix n n ℝ) (X ⊙ X) = inner X X := by
  rw [inner_eq_sum, inner_self]
  simp [ones, hadamard_apply, pow_two]

/-- Each Laplacian annihilates the all-ones vector, so `M X` and `X ⊙ X` have
the same row sums. -/
lemma M_mulVec_one (X : Matrix n n ℝ) :
    M X *ᵥ (1 : n → ℝ) = (X ⊙ X) *ᵥ (1 : n → ℝ) := by
  simp only [M, add_mulVec, sum_mulVec, smul_mulVec]
  refine add_eq_left.mpr ?_
  refine Fintype.sum_eq_zero _ fun i ↦ Fintype.sum_eq_zero _ fun j ↦ ?_
  rw [vecMulVec_sub_single_mulVec_one, smul_zero]

lemma inner_ones_M (X : Matrix n n ℝ) :
    inner (ones : Matrix n n ℝ) (M X) = inner X X := by
  unfold M
  rw [inner_add_right, inner_ones_hadamard_self, inner_sum_right]
  refine add_eq_left.mpr (Fintype.sum_eq_zero _ fun i ↦ ?_)
  rw [inner_sum_right]
  refine Fintype.sum_eq_zero _ fun j ↦ ?_
  rw [inner_smul_right, inner_ones_vecMulVec_sub_single, mul_zero]

/-! ### MX05 — continuity and scaling -/

lemma ite_neg_sq_eq_min_sq (x : ℝ) :
    (if x < 0 then x ^ 2 else 0) = (min x 0) ^ 2 := by
  rcases lt_trichotomy x 0 with h | h | h
  · simp [h, min_eq_left h.le]
  · simp [h]
  · simp [h.not_gt, min_eq_right h.le]

omit [Fintype n] [DecidableEq n] in
lemma laplacianCoeff_eq_min (X : Matrix n n ℝ) (i j : n) :
    laplacianCoeff X i j = if i < j then (min (X i j) 0) ^ 2 else 0 := by
  unfold laplacianCoeff
  by_cases hij : i < j <;> simp [hij, ite_neg_sq_eq_min_sq]

omit [Fintype n] [DecidableEq n] in
lemma continuous_laplacianCoeff (i j : n) :
    Continuous fun X : Matrix n n ℝ => laplacianCoeff X i j := by
  simp_rw [laplacianCoeff_eq_min]
  by_cases hij : i < j
  · simp only [hij, ↓reduceIte]
    exact ((continuous_apply_apply i j).min continuous_const).pow 2
  · simp only [hij, ↓reduceIte]
    exact continuous_const

lemma continuous_M : Continuous (fun X : Matrix n n ℝ => M X) := by
  unfold M
  refine Continuous.add ?hadamard ?sum
  · refine continuous_matrix fun i j ↦
      (continuous_apply_apply i j).mul (continuous_apply_apply i j)
  · refine continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦ ?_
    exact (continuous_laplacianCoeff i j).smul continuous_const

omit [Fintype n] [DecidableEq n] in
lemma laplacianCoeff_smul_sq (c : ℝ) (hc : 0 ≤ c) (X : Matrix n n ℝ) (i j : n) :
    laplacianCoeff ((c ^ 2) • X) i j = c ^ 4 * laplacianCoeff X i j := by
  unfold laplacianCoeff
  by_cases hij : i < j
  · simp only [hij, true_and]
    have hxij : ((c ^ 2) • X) i j = c * c * X i j := by
      rw [Matrix.smul_apply, smul_eq_mul, pow_two]
    rw [hxij]
    rcases eq_or_lt_of_le hc with rfl | hpos
    · simp
    · have hc2 : 0 < c * c := mul_pos hpos hpos
      by_cases hneg : X i j < 0
      · have : c * c * X i j < 0 := mul_neg_of_pos_of_neg hc2 hneg
        simp [hneg, this]
        ring
      · have : ¬ c * c * X i j < 0 := by
          rw [not_lt] at hneg ⊢
          exact mul_nonneg (mul_nonneg hpos.le hpos.le) hneg
        simp [hneg, this]
  · simp [hij]

/-- `M (c² • X) = c⁴ • M X` for `c ≥ 0`. -/
lemma M_smul_sq {c : ℝ} (hc : 0 ≤ c) (X : Matrix n n ℝ) :
    M ((c ^ 2) • X) = (c ^ 4) • M X := by
  unfold M
  have hHad : ((c ^ 2) • X) ⊙ ((c ^ 2) • X) = (c ^ 4) • (X ⊙ X) := by
    rw [smul_hadamard, hadamard_smul, smul_smul]
    ring_nf
  rw [hHad]
  have hsum :
      ∑ i, ∑ j, laplacianCoeff ((c ^ 2) • X) i j • vecMulVec (e i - e j) (e i - e j) =
        (c ^ 4) • ∑ i, ∑ j, laplacianCoeff X i j • vecMulVec (e i - e j) (e i - e j) := by
    simp_rw [laplacianCoeff_smul_sq c hc, mul_smul]
    rw [smul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [smul_sum]
  rw [hsum, ← smul_add]

end

end BollobasNikiforov
