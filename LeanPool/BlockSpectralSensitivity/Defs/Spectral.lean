/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Defs.Sensitivity
public import LeanPool.BlockSpectralSensitivity.Spectral.Hermitian

/-!
# The sensitivity graph and `lambda(f)`

`adj f` is the adjacency matrix (over `ℝ`) of the sensitivity graph `G_f`: vertices are
all inputs, and `x ~ y` when `x` and `y` are Hamming neighbours with `f x ≠ f y`.

`lam f` is defined as the largest eigenvalue of `adj f`, matching the definition
`lambda(f) = largest eigenvalue of A_f` of Section 1.2 of `bs_lambda.txt`.

The `L2` operator norm on matrices is a scoped instance; we `open scoped
Matrix.Norms.L2Operator` throughout the spectral development.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

public section

namespace BSLambda

open scoped Matrix Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V]

/-- The adjacency matrix `A_f` of the sensitivity graph `G_f`. -/
@[expose] noncomputable def adj (f : Input V → Bool) : Matrix (Input V) (Input V) ℝ :=
  Matrix.of fun x y => if hammingDist x y = 1 ∧ f x ≠ f y then (1 : ℝ) else 0

lemma adj_apply (f : Input V → Bool) (x y : Input V) :
    adj f x y = if hammingDist x y = 1 ∧ f x ≠ f y then (1 : ℝ) else 0 := rfl

/-- The sensitivity adjacency matrix has nonnegative entries. -/
lemma adj_nonneg (f : Input V → Bool) (x y : Input V) : 0 ≤ adj f x y := by
  rw [adj_apply]
  positivity

lemma adj_apply_eq_one_iff {f : Input V → Bool} {x y : Input V} :
    adj f x y = 1 ↔ hammingDist x y = 1 ∧ f x ≠ f y := by
  simp [adj_apply]

/-- Two inputs on the same side of `f` are never adjacent in the sensitivity graph. -/
lemma adj_eq_zero_of_apply_eq (f : Input V → Bool) {x y : Input V} (h : f x = f y) :
    adj f x y = 0 := by
  simp [adj_apply, h]

/-- Adjacent inputs take different `f`-values. -/
lemma apply_ne_of_adj_ne_zero (f : Input V → Bool) {x y : Input V} (h : adj f x y ≠ 0) :
    f x ≠ f y :=
  fun hf ↦ h (adj_eq_zero_of_apply_eq f hf)

/-- The adjacency matrix of the sensitivity graph is symmetric. -/
lemma adj_comm (f : Input V → Bool) (x y : Input V) : adj f x y = adj f y x := by
  simp [adj_apply, hammingDist_comm y x, ne_comm]

lemma transpose_adj (f : Input V → Bool) : (adj f)ᵀ = adj f :=
  Matrix.ext fun x y ↦ adj_comm f y x

lemma isHermitian_adj (f : Input V → Bool) : (adj f).IsHermitian :=
  (Matrix.conjTranspose_eq_transpose_of_trivial (adj f)).trans (transpose_adj f)

section DecEq
variable [DecidableEq V]

/-- The neighbours of `x` in the sensitivity graph. -/
def nbrs (f : Input V → Bool) (x : Input V) : Finset (Input V) :=
  Finset.univ.filter fun y => hammingDist x y = 1 ∧ f x ≠ f y

/-- `y` is a neighbour of `x` exactly when they are Hamming neighbours separated by `f`. -/
lemma mem_nbrs {f : Input V → Bool} {x y : Input V} :
    y ∈ nbrs f x ↔ hammingDist x y = 1 ∧ f x ≠ f y := by
  simp [nbrs]

/-- The neighbours of `x` are exactly the one-coordinate flips at sensitive coordinates. -/
lemma nbrs_eq_image (f : Input V → Bool) (x : Input V) :
    nbrs f x = (sensCoords f x).image fun v => flipSet x {v} := by
  ext y
  simp only [mem_nbrs, Finset.mem_image, mem_sensCoords, SensitiveCoord]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨v, rfl⟩ := exists_eq_flipSet_singleton_of_hammingDist_eq_one h1
    exact ⟨v, h2.symm, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hammingDist_flipSet_singleton x v, hv.symm⟩

/-- The degree of `x` in `G_f` is `s(f,x)`. -/
@[simp] lemma card_nbrs (f : Input V → Bool) (x : Input V) : (nbrs f x).card = sensAt f x := by
  rw [nbrs_eq_image, Finset.card_image_of_injective _ (flipSet_singleton_injective x), sensAt]

/-- `adj f x y` is the indicator of `y` being a neighbour of `x` in `G_f`. -/
lemma adj_apply_eq_ite_mem_nbrs (f : Input V → Bool) (x y : Input V) :
    adj f x y = if y ∈ nbrs f x then 1 else 0 := by
  simp [adj_apply, mem_nbrs]

/-- Every row of `adj f` sums to the sensitivity at that point. -/
@[simp] lemma sum_adj_row (f : Input V → Bool) (x : Input V) :
    ∑ y, adj f x y = (sensAt f x : ℝ) := by
  simp [adj_apply_eq_ite_mem_nbrs, Finset.sum_ite_mem]

/-- Column sums of the sensitivity adjacency matrix: it is symmetric (`adj_comm`), so they
agree with the row sums of `sum_adj_row`. -/
lemma sum_adj_col (f : Input V → Bool) (y : Input V) : ∑ x, adj f x y = (sensAt f y : ℝ) := by
  simpa [adj_comm f y] using sum_adj_row f y

/-- The trace of the sensitivity adjacency matrix vanishes: no input is its own neighbour. -/
lemma trace_adj (f : Input V → Bool) : (adj f).trace = 0 := by
  refine Finset.sum_eq_zero fun x _ ↦ ?_
  simp [Matrix.diag_apply, adj_apply]

/-- `lambda(f)`: the largest eigenvalue of the sensitivity-graph adjacency matrix. -/
@[expose]
noncomputable def lam (f : Input V → Bool) : ℝ := ⨆ i, (isHermitian_adj f).eigenvalues i

/-- `lambda(f) ≥ 0`: the eigenvalues of `adj f` sum to `trace (adj f) = 0`, so at least one of
them, hence their supremum, is nonnegative (Section 11.1 of `bs_lambda.txt`). -/
theorem lam_nonneg (f : Input V → Bool) : 0 ≤ lam f := by
  have htr : ∑ i, (isHermitian_adj f).eigenvalues i = 0 := by
    simpa [trace_adj] using (isHermitian_adj f).trace_eq_sum_eigenvalues.symm
  have hle : ∑ _i : Input V, (0 : ℝ) ≤ ∑ i, (isHermitian_adj f).eigenvalues i := by
    rw [htr, Finset.sum_const_zero]
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hle
  exact hi.trans (le_ciSup (Finite.bddAbove_range _) i)

/-- `lambda(f)` is at most the L2 operator norm of the adjacency matrix (Section 11.1). -/
theorem lam_le_l2_opNorm_adj (f : Input V → Bool) : lam f ≤ ‖adj f‖ :=
  (isHermitian_adj f).ciSup_eigenvalues_le_l2_opNorm

end DecEq

end BSLambda
