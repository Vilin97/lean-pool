/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Spectral.Bipartite

/-!
# `‖A_f‖ = lambda(f)`

Conjugating an eigenvector by the sign pattern `x ↦ (-1)^{f x}` turns an eigenvector for `μ`
into an eigenvector for `-μ` (`BSLambda.exists_neg_eigenvector`), because every edge of the
sensitivity graph flips the sign.  Hence `|μ| ≤ lambda(f)` for every eigenvalue `μ`
(`BSLambda.abs_eigenvalues_adj_le_lam`) and therefore `‖A_f‖ = lambda(f)`
(`BSLambda.l2_opNorm_adj_eq_lam`).  This upgrades the inequality
`BSLambda.lam_le_l2_opNorm_adj` of Section 11.1 of `bs_lambda.txt` to an equality, which is
what the composition theorem of Section 14 needs.

The consequences used later are the operator bound
`BSLambda.sum_sq_adj_mulVec_le : ∑ x, (A_f *ᵥ v) x ^ 2 ≤ lambda(f)^2 * ∑ x, v x ^ 2`
and the existence of a top eigenvector `BSLambda.exists_top_eigenvector`.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

@[expose] public section

namespace BSLambda

open scoped Matrix Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An eigenvalue of `A_f` is at most `lambda(f)`. -/
theorem le_lam_of_eigenvector (f : Input V → Bool) {μ : ℝ} {v : Input V → ℝ} (hv : v ≠ 0)
    (hev : adj f *ᵥ v = μ • v) : μ ≤ lam f :=
  (isHermitian_adj f).le_ciSup_eigenvalues hv hev

/-- The sign pattern `(-1)^{f x}`: it is `1` on `f⁻¹(true)` and `-1` on `f⁻¹(false)`. -/
def signPattern (f : Input V → Bool) (x : Input V) : ℝ := if f x then 1 else -1

omit [Fintype V] [DecidableEq V] in
/-- The sign pattern takes the values `±1`, so it never vanishes. -/
private theorem signPattern_ne_zero (f : Input V → Bool) (x : Input V) : signPattern f x ≠ 0 := by
  rw [signPattern]
  split <;> norm_num

omit [DecidableEq V] in
/-- The sign pattern flips across every edge of the sensitivity graph, so scaling coordinate `y`
by `signPattern f y` is the same as scaling the whole `x`-row by `-signPattern f x`. -/
private theorem adj_mul_signPattern (f : Input V → Bool) (v : Input V → ℝ) (x y : Input V) :
    adj f x y * (signPattern f y * v y) = -signPattern f x * (adj f x y * v y) := by
  by_cases h : hammingDist x y = 1 ∧ f x ≠ f y
  · have hfy : f y = !f x := by
      revert h
      cases f x <;> cases f y <;> simp
    rw [adj_apply, ite_eq_left h, signPattern, signPattern, hfy]
    cases f x <;> simp
  · rw [adj_apply, ite_eq_right h]
    ring

/-- The sign flip `x ↦ (-1)^{f x}` conjugates an eigenvector for `μ` into one for `-μ`: every
edge of the sensitivity graph joins inputs with different `f`-values. -/
theorem exists_neg_eigenvector (f : Input V → Bool) {μ : ℝ} {v : Input V → ℝ} (hv : v ≠ 0)
    (hev : adj f *ᵥ v = μ • v) : ∃ w : Input V → ℝ, w ≠ 0 ∧ adj f *ᵥ w = (-μ) • w := by
  refine ⟨fun x ↦ signPattern f x * v x, ?_, ?_⟩
  · intro hw
    refine hv (funext fun x ↦ ?_)
    exact (mul_eq_zero.1 (congrFun hw x)).resolve_left (signPattern_ne_zero f x)
  · funext x
    have hvx : ∑ y : Input V, adj f x y * v y = μ * v x := by
      simpa [Matrix.mulVec, dotProduct] using congrFun hev x
    calc (adj f *ᵥ fun y ↦ signPattern f y * v y) x
        = ∑ y : Input V, adj f x y * (signPattern f y * v y) := rfl
      _ = ∑ y : Input V, -signPattern f x * (adj f x y * v y) :=
          Finset.sum_congr rfl fun y _ ↦ adj_mul_signPattern f v x y
      _ = -signPattern f x * ∑ y : Input V, adj f x y * v y := (Finset.mul_sum _ _ _).symm
      _ = -signPattern f x * (μ * v x) := by rw [hvx]
      _ = ((-μ) • fun y ↦ signPattern f y * v y) x := by
          simp only [Pi.smul_apply, smul_eq_mul]
          ring

/-- Every eigenvalue of `A_f` is at most `lambda(f)` in absolute value. -/
theorem abs_eigenvalues_adj_le_lam (f : Input V → Bool) (i : Input V) :
    |(isHermitian_adj f).eigenvalues i| ≤ lam f := by
  have hne : (⇑((isHermitian_adj f).eigenvectorBasis i) : Input V → ℝ) ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 <|
      (isHermitian_adj f).eigenvectorBasis.orthonormal.ne_zero i
  have hev : adj f *ᵥ ⇑((isHermitian_adj f).eigenvectorBasis i)
      = (isHermitian_adj f).eigenvalues i • ⇑((isHermitian_adj f).eigenvectorBasis i) :=
    (isHermitian_adj f).mulVec_eigenvectorBasis i
  refine abs_le.2 ⟨?_, le_ciSup (Finite.bddAbove_range _) i⟩
  obtain ⟨w, hw, hwev⟩ := exists_neg_eigenvector f hne hev
  exact neg_le.2 (le_lam_of_eigenvector f hw hwev)

/-- The L2 operator norm of the sensitivity adjacency matrix is at most `lambda(f)`. -/
theorem l2_opNorm_adj_le_lam (f : Input V → Bool) : ‖adj f‖ ≤ lam f :=
  (isHermitian_adj f).l2_opNorm_le_of_abs_eigenvalues_le (abs_eigenvalues_adj_le_lam f)

/-- **`lambda(f)` is the L2 operator norm of `A_f`.**  The sensitivity graph is bipartite, so
its spectrum is symmetric about `0` and the largest eigenvalue is the spectral radius. -/
theorem l2_opNorm_adj_eq_lam (f : Input V → Bool) : ‖adj f‖ = lam f :=
  le_antisymm (l2_opNorm_adj_le_lam f) (lam_le_l2_opNorm_adj f)

/-- The operator bound defining `lambda(f)`, in sum-of-squares form. -/
theorem sum_sq_adj_mulVec_le (f : Input V → Bool) (v : Input V → ℝ) :
    ∑ x, (adj f *ᵥ v) x ^ 2 ≤ lam f ^ 2 * ∑ x, v x ^ 2 := by
  simpa [l2_opNorm_adj_eq_lam] using Matrix.sum_sq_mulVec_le (adj f) v

/-- The operator bound restricted to one side of the bipartition: `A_f *ᵥ v` reads `v` only on
the other side, so only the other side's coordinates appear on the right. -/
theorem sum_sq_adj_mulVec_side_le (f : Input V → Bool) (v : Input V → ℝ) (β : Bool) :
    ∑ x, (if f x = β then (adj f *ᵥ v) x else 0) ^ 2
      ≤ lam f ^ 2 * ∑ x, (if f x = β then 0 else v x) ^ 2 := by
  refine (Finset.sum_le_sum fun x _ ↦ ?_).trans
    (sum_sq_adj_mulVec_le f fun z ↦ if f z = β then 0 else v z)
  rcases eq_or_ne (f x) β with hx | hx
  · rw [ite_eq_left hx]
    refine le_of_eq (congrArg (· ^ 2) (Finset.sum_congr rfl fun z _ ↦ ?_))
    rcases eq_or_ne (f z) β with hz | hz
    · simp [adj_eq_zero_of_apply_eq f (hx.trans hz.symm)]
    · simp [hz]
  · rw [ite_eq_right hx, zero_pow two_ne_zero]
    positivity

/-- The largest eigenvalue of `A_f` is attained by an eigenvector. -/
theorem exists_top_eigenvector (f : Input V → Bool) :
    ∃ u : Input V → ℝ, u ≠ 0 ∧ adj f *ᵥ u = lam f • u :=
  (isHermitian_adj f).exists_eigenvector_ciSup_eigenvalues

/-- `A_f *ᵥ v` written as a sum over coordinate flips. -/
theorem adj_mulVec_apply (f : Input V → Bool) (ν : Input V → ℝ) (x : Input V) :
    (adj f *ᵥ ν) x = ∑ i : V, adj f x (flipSet x {i}) * ν (flipSet x {i}) := by
  classical
  have himg : ∑ y ∈ Finset.univ.image fun i : V ↦ flipSet x {i}, adj f x y * ν y
      = ∑ i : V, adj f x (flipSet x {i}) * ν (flipSet x {i}) :=
    Finset.sum_image fun a _ b _ hab ↦ flipSet_singleton_injective x hab
  rw [← himg]
  change ∑ y : Input V, adj f x y * ν y = _
  refine (Finset.sum_subset (Finset.subset_univ _) fun y _ hy ↦ ?_).symm
  suffices h0 : adj f x y = 0 by rw [h0, zero_mul]
  rw [adj_apply]
  refine ite_eq_right fun h ↦ hy ?_
  obtain ⟨w, rfl⟩ := exists_eq_flipSet_singleton_of_hammingDist_eq_one h.1
  exact Finset.mem_image.2 ⟨w, Finset.mem_univ w, rfl⟩

/-- A bound on the sensitivity of `f` bounds `lambda(f)`: the adjacency matrix has nonnegative
entries and all its row sums are at most `k`. -/
theorem lam_le_of_sensAt_le {f : Input V → Bool} {k : ℝ} (hk : 0 ≤ k)
    (hs : ∀ x, (sensAt f x : ℝ) ≤ k) : lam f ≤ k := by
  refine (lam_le_l2_opNorm_adj f).trans ?_
  rw [← Real.sqrt_mul_self hk]
  exact Matrix.l2_opNorm_le_sqrt_of_row_col_sums (adj f) (adj_nonneg f)
    (fun x ↦ (sum_adj_row f x).trans_le (hs x)) fun y ↦ (sum_adj_col f y).trans_le (hs y)

/-- A sensitivity graph all of whose vertices have degree `k` has `lambda = k`: the row sums
give `lam f ≤ k`, and the all-ones vector is an eigenvector for `k`. -/
theorem lam_eq_of_sensAt_eq {f : Input V → Bool} {k : ℝ} (hk : 0 ≤ k)
    (hs : ∀ x, (sensAt f x : ℝ) = k) : lam f = k :=
  le_antisymm (lam_le_of_sensAt_le hk fun x ↦ (hs x).le) <|
    le_lam_of_eigenvector f (v := fun _ ↦ (1 : ℝ))
      (fun h ↦ one_ne_zero (congrFun h (zeroInput V)))
      (funext fun x ↦ by simpa [Matrix.mulVec, dotProduct] using hs x)

end BSLambda
