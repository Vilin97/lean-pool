/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Defs.Spectral
public import LeanPool.BlockSpectralSensitivity.Spectral.SchurTest

/-!
# Boundary incidence and the positive-side Gram matrix

Section 11.1 of `bs_lambda.txt` splits the vertex set of the sensitivity graph `G_f` into the
positive inputs `S = f⁻¹(1)` and the negative inputs `T = f⁻¹(0)`.  The graph is bipartite
between `S` and `T`, with biadjacency matrix `M` (`BSLambda.biadj`), so that in the vertex
order `S, T`

```
A_f = [ 0    M   ]
      [ Mᵀ   0   ]
```

and `lambda(f)^2 = rho(K)` for the positive-side Gram matrix `K = M Mᵀ` (`BSLambda.gram`).

We prove the inequality half of that identity, which is all the later sections need:

`BSLambda.lam_sq_le_l2_opNorm_gram : lam f ^ 2 ≤ ‖gram f‖`.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

public section

namespace BSLambda

open scoped Matrix Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The two sides and the biadjacency matrix -/

/-- The inputs on which `f` is `1`: the positive side `S = f⁻¹(1)`
(Section 11.1 of `bs_lambda.txt`). -/
abbrev Ones (f : Input V → Bool) : Type _ := {x : Input V // f x = true}

/-- The inputs on which `f` is `0`: the negative side `T = f⁻¹(0)`
(Section 11.1 of `bs_lambda.txt`). -/
abbrev Zeros (f : Input V → Bool) : Type _ := {x : Input V // f x = false}

/-- The biadjacency matrix `M` of the sensitivity graph, rows indexed by `S`,
columns by `T` (Section 11.1). -/
@[expose]
noncomputable def biadj (f : Input V → Bool) : Matrix (Ones f) (Zeros f) ℝ :=
  Matrix.of fun x z => if hammingDist x.1 z.1 = 1 then (1 : ℝ) else 0

/-- The positive-side Gram matrix `K = M Mᵀ` (Section 11.1). -/
noncomputable def gram (f : Input V → Bool) : Matrix (Ones f) (Ones f) ℝ :=
  biadj f * (biadj f)ᵀ

omit [DecidableEq V] in
/-- Entries of the biadjacency matrix of Section 11.1. -/
lemma biadj_apply (f : Input V → Bool) (x : Ones f) (z : Zeros f) :
    biadj f x z = if hammingDist x.1 z.1 = 1 then (1 : ℝ) else 0 := rfl

omit [DecidableEq V] in
/-- The biadjacency matrix of Section 11.1 has nonnegative entries. -/
lemma biadj_nonneg (f : Input V → Bool) (x : Ones f) (z : Zeros f) : 0 ≤ biadj f x z := by
  rw [biadj_apply]
  positivity

omit [DecidableEq V] in
/-- The biadjacency matrix is the restriction of the adjacency matrix to `S × T`: the
condition `f x ≠ f z` of `BSLambda.adj` is automatic there (Section 11.1). -/
lemma biadj_eq_adj (f : Input V → Bool) (x : Ones f) (z : Zeros f) :
    biadj f x z = adj f x.1 z.1 := by
  rw [biadj_apply, adj_apply]
  simp [x.2, z.2]

/-- A weighted sum of the row `adj f a ·` over the inputs lying on the same side of `f` as `a`
vanishes, since no two same-side inputs are adjacent. -/
private lemma sum_adj_mul_eq_zero_of_apply_eq (f : Input V → Bool) (v : Input V → ℝ) {b : Bool}
    {a : Input V} (ha : f a = b) : ∑ y : {y : Input V // f y = b}, adj f a y.1 * v y.1 = 0 := by
  refine Finset.sum_eq_zero fun y _ ↦ ?_
  rw [adj_eq_zero_of_apply_eq f (ha.trans y.2.symm), zero_mul]

/-- Splitting a sum over all inputs into its positive and its negative part (Section 11.1). -/
theorem sum_ones_add_sum_zeros (f : Input V → Bool) (g : Input V → ℝ) :
    ∑ x : Ones f, g x.1 + ∑ z : Zeros f, g z.1 = ∑ y : Input V, g y := by
  have h2 : ∑ z : Zeros f, g z.1 = ∑ z : {x : Input V // ¬ f x = true}, g z.1 :=
    Fintype.sum_equiv (Equiv.subtypeEquivRight fun _ ↦ by simp) _ _ fun _ ↦ rfl
  rw [h2]
  exact Fintype.sum_subtype_add_sum_subtype (fun x ↦ f x = true) g

/-! ### The positive-side Gram matrix -/

/-- **Counting form of the Gram entries.**  For `x, y ∈ S`, the entry `K_{x,y}` counts the
negative inputs adjacent to both `x` and `y` (Section 11.1 of `bs_lambda.txt`). -/
theorem gram_apply (f : Input V → Bool) (x y : Ones f) :
    gram f x y =
      ((Finset.univ.filter fun z : Zeros f =>
          hammingDist x.1 z.1 = 1 ∧ hammingDist y.1 z.1 = 1).card : ℝ) := by
  simp only [gram, Matrix.mul_apply, Matrix.transpose_apply, biadj_apply, Finset.card_filter,
    Nat.cast_sum, ite_and, ite_mul, one_mul, zero_mul, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- A Gram entry is nonzero exactly when the two positive inputs have a common negative
Hamming neighbour: `gram_apply` with the cardinality turned into an existential
(Section 11.1). -/
theorem gram_ne_zero_iff {f : Input V → Bool} {x y : Ones f} :
    gram f x y ≠ 0 ↔ ∃ z : Zeros f, hammingDist x.1 z.1 = 1 ∧ hammingDist y.1 z.1 = 1 := by
  rw [gram_apply, Nat.cast_ne_zero, Finset.card_ne_zero, Finset.filter_nonempty_iff]
  simp

/-- The Gram matrix of Section 11.1 is symmetric, entrywise. -/
theorem gram_comm {f : Input V → Bool} (x y : Ones f) : gram f x y = gram f y x := by
  rw [gram_apply, gram_apply]
  exact congrArg _ (congrArg Finset.card (Finset.filter_congr fun _ _ ↦ and_comm))

/-- The Gram matrix of Section 11.1 has nonnegative entries. -/
lemma gram_nonneg (f : Input V → Bool) (x y : Ones f) : 0 ≤ gram f x y := by
  rw [gram_apply]
  positivity

/-- On the diagonal, `K_{x,x} = s(f,x)` (Section 11.1 of `bs_lambda.txt`). -/
theorem gram_diag (f : Input V → Bool) (x : Ones f) : gram f x x = (sensAt f x.1 : ℝ) := by
  rw [gram_apply, ← card_nbrs]
  norm_cast
  refine Finset.card_bij (fun z _ ↦ (z : Input V)) ?_ (fun _ _ _ _ hab ↦ Subtype.ext hab) ?_
  · intro z hz
    rw [Finset.mem_filter_univ] at hz
    refine mem_nbrs.mpr ⟨hz.1, ?_⟩
    simp [x.2, z.2]
  · intro y hy
    rw [mem_nbrs] at hy
    refine ⟨⟨y, ?_⟩, ?_, rfl⟩
    · simpa [x.2] using hy.2
    · simpa using hy.1

/-- The Gram matrix `K = M Mᵀ` of Section 11.1 is symmetric. -/
theorem gram_isHermitian (f : Input V → Bool) : (gram f).IsHermitian := by
  rw [gram, ← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact Matrix.isHermitian_mul_conjTranspose_self _

/-! ### The block decomposition of the adjacency matrix -/

/-- The `Ones f` rows of the block decomposition of `A_f`: at a positive input, `A_f *ᵥ v` sees
only the negative coordinates of `v`, and there it is governed by `M` (Section 11.1). -/
lemma mulVec_adj_ones (f : Input V → Bool) (v : Input V → ℝ) (x : Ones f) :
    (adj f *ᵥ v) x.1 = (biadj f *ᵥ fun z : Zeros f ↦ v z.1) x := by
  change ∑ y : Input V, adj f x.1 y * v y = ∑ z : Zeros f, biadj f x z * v z.1
  rw [← sum_ones_add_sum_zeros f fun y ↦ adj f x.1 y * v y,
    sum_adj_mul_eq_zero_of_apply_eq f v x.2, zero_add]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [biadj_eq_adj]

/-- The `Zeros f` rows of the block decomposition of `A_f`: at a negative input, `A_f *ᵥ v` sees
only the positive coordinates of `v`, and there it is governed by `Mᵀ` (Section 11.1). -/
lemma mulVec_adj_zeros (f : Input V → Bool) (v : Input V → ℝ) (z : Zeros f) :
    (adj f *ᵥ v) z.1 = ((biadj f)ᵀ *ᵥ fun x : Ones f ↦ v x.1) z := by
  change ∑ y : Input V, adj f z.1 y * v y = ∑ x : Ones f, (biadj f)ᵀ z x * v x.1
  rw [← sum_ones_add_sum_zeros f fun y ↦ adj f z.1 y * v y,
    sum_adj_mul_eq_zero_of_apply_eq f v z.2, add_zero]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Matrix.transpose_apply, biadj_eq_adj, adj_comm]

/-- The L2 operator norm of `A_f` is bounded by that of its off-diagonal block `M`
(Section 11.1 of `bs_lambda.txt`). -/
theorem l2_opNorm_adj_le (f : Input V → Bool) : ‖adj f‖ ≤ ‖biadj f‖ := by
  refine Matrix.l2_opNorm_le_of_sum_sq_mulVec_le (adj f) (norm_nonneg _) fun v ↦ ?_
  rw [← sum_ones_add_sum_zeros f fun y ↦ (adj f *ᵥ v) y ^ 2,
    ← sum_ones_add_sum_zeros f fun y ↦ v y ^ 2]
  have h1 : ∑ x : Ones f, (adj f *ᵥ v) x.1 ^ 2 ≤ ‖biadj f‖ ^ 2 * ∑ z : Zeros f, v z.1 ^ 2 := by
    simpa [mulVec_adj_ones] using Matrix.sum_sq_mulVec_le (biadj f) fun z : Zeros f ↦ v z.1
  have h2 : ∑ z : Zeros f, (adj f *ᵥ v) z.1 ^ 2 ≤ ‖biadj f‖ ^ 2 * ∑ x : Ones f, v x.1 ^ 2 := by
    simpa [mulVec_adj_zeros, Matrix.l2_opNorm_transpose] using
      Matrix.sum_sq_mulVec_le ((biadj f)ᵀ) fun x : Ones f ↦ v x.1
  calc ∑ x : Ones f, (adj f *ᵥ v) x.1 ^ 2 + ∑ z : Zeros f, (adj f *ᵥ v) z.1 ^ 2
      ≤ ‖biadj f‖ ^ 2 * ∑ z : Zeros f, v z.1 ^ 2 + ‖biadj f‖ ^ 2 * ∑ x : Ones f, v x.1 ^ 2 :=
        add_le_add h1 h2
    _ = ‖biadj f‖ ^ 2 * (∑ x : Ones f, v x.1 ^ 2 + ∑ z : Zeros f, v z.1 ^ 2) := by ring

/-- The norm of the Gram matrix `K = M Mᵀ` is the square of the norm of `M` (Section 11.1). -/
theorem l2_opNorm_gram (f : Input V → Bool) : ‖gram f‖ = ‖biadj f‖ * ‖biadj f‖ := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self ((biadj f)ᵀ)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at h
  rw [gram, h, Matrix.l2_opNorm_transpose]

/-- `lambda(f)^2 <= ‖K‖`, where `K = M Mᵀ` is the positive-side Gram matrix
(Section 11.1 of `bs_lambda.txt`). -/
theorem lam_sq_le_l2_opNorm_gram (f : Input V → Bool) : lam f ^ 2 ≤ ‖gram f‖ := by
  rw [l2_opNorm_gram, ← sq]
  calc lam f ^ 2 ≤ ‖adj f‖ ^ 2 := pow_le_pow_left₀ (lam_nonneg f) (lam_le_l2_opNorm_adj f) 2
    _ ≤ ‖biadj f‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_adj_le f) 2

end BSLambda
