/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Sign averaging and two little-Grothendieck bounds

This file contains an elementary but very useful principle and its two standard
consequences for operators with an `ℓ_∞` domain or an `ℓ₁` codomain.

## Sign averaging

For finitely many vectors `w j` (`j ∈ J`) in an inner product space, the average
of `‖∑_j ε_j w_j‖²` over all sign patterns `ε ∈ {±1}^J` equals `∑_j ‖w_j‖²`
(the cross terms cancel). Consequently, if *every* signed sum has norm at most
`M`, then

  `∑_{j ∈ J} ‖w_j‖² ≤ M²`.

A sign pattern is encoded by a subset `S ⊆ J` (`ε_j = +1` iff `j ∈ S`); the
corresponding signed sum is `signedSum w S J`. The averaging identity is
`sum_powerset_norm_signedSum_sq`, proved by induction on `J` using the
parallelogram law, and the resulting inequality is
`sum_norm_sq_le_sq_of_signedSum_le`.

## The two consequences

* `sum_norm_sq_apply_single_le` — for `B : ℓ_∞ → H` with `H` a Hilbert space,
  `∑_j ‖B e_j‖² ≤ ‖B‖²`. This is the **little Grothendieck inequality** in the
  form needed here (with constant `1`): only the `±1`-vectors of `ℓ_∞`, which
  all have norm `1`, enter the sign-averaging argument. In Hilbert–Schmidt
  language: `B` restricted to the unit vectors is Hilbert–Schmidt with
  `‖B‖_HS ≤ ‖B‖`.
* `sum_norm_sq_row_le` — dually, for `A : H → ℓ₁` with *rows* `w j`, i.e.
  `⟪w j, x⟫ = (A x) j`, one has `∑_j ‖w_j‖² ≤ ‖A‖²`. Here the signed sums are
  bounded using `∑_{j ∈ J} |y_j| ≤ ‖y‖₁`; this is the little Grothendieck bound
  for the adjoint `A' : ℓ_∞ = ℓ₁' → H`, but stated without ever forming the
  adjoint.

Both are stated as bounds on *finite* partial sums. For the index set `ℕ` this
makes `∑_j ‖w_j‖²` summable (`summable_norm_sq_row`), recorded at the end
together with the `ℓ₂`-norm identity `norm_sq_eq_tsum_norm_sq`.
-/

@[expose] public section

open scoped ENNReal

namespace SNumbers

/-! ## Signed sums -/

section SignedSum

variable {G : Type*} [AddCommGroup G] {ι : Type*} [DecidableEq ι]

/-- `signedSum w S J = ∑_{j ∈ J} ε_j w_j`, where the sign pattern is given by
the subset `S`: `ε_j = +1` for `j ∈ S` and `ε_j = -1` for `j ∉ S`. -/
def signedSum (w : ι → G) (S J : Finset ι) : G :=
  ∑ j ∈ J, if j ∈ S then w j else -w j

/-- The signed sum over the empty index set is `0`. -/
@[simp] lemma signedSum_empty (w : ι → G) (S : Finset ι) : signedSum w S ∅ = 0 := by
  simp [signedSum]

/-- Adding a new index `a ∉ J` outside the sign pattern subtracts `w a`. -/
lemma signedSum_insert_of_notMem {w : ι → G} {a : ι} {S J : Finset ι}
    (ha : a ∉ J) (haS : a ∉ S) :
    signedSum w S (insert a J) = signedSum w S J - w a := by
  rw [signedSum, signedSum, Finset.sum_insert ha, ite_eq_right haS]
  abel

/-- Adding a new index `a ∉ J` inside the sign pattern adds `w a`. -/
lemma signedSum_insert_insert {w : ι → G} {a : ι} {S J : Finset ι} (ha : a ∉ J) :
    signedSum w (insert a S) (insert a J) = signedSum w S J + w a := by
  rw [signedSum, signedSum, Finset.sum_insert ha, ite_eq_left (Finset.mem_insert_self a S)]
  have hcongr : ∀ j ∈ J, (if j ∈ insert a S then w j else -w j)
      = if j ∈ S then w j else -w j := by
    intro j hj
    have hja : j ≠ a := fun h => ha (h ▸ hj)
    simp [Finset.mem_insert, hja]
  rw [Finset.sum_congr rfl hcongr]
  abel

end SignedSum

/-! ## The averaging identity and the sign-averaging bound -/

section Averaging

variable {ι : Type*} [DecidableEq ι]

/-- **Sign averaging (identity form).** Summing `‖∑_j ε_j w_j‖²` over all `2^|J|`
sign patterns gives `2^|J| · ∑_{j ∈ J} ‖w_j‖²`: the cross terms cancel. The proof
is induction on `J`, where the two extensions of a sign pattern to a new index
are paired by the parallelogram law.

The scalar field `𝕜` is an explicit argument because it does not occur in the
statement (only the norm does, while the proof uses the inner product). -/
lemma sum_powerset_norm_signedSum_sq (𝕜 : Type*) [RCLike 𝕜] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (w : ι → H) (J : Finset ι) :
    ∑ S ∈ J.powerset, ‖signedSum w S J‖ ^ 2 = 2 ^ J.card * ∑ j ∈ J, ‖w j‖ ^ 2 := by
  induction J using Finset.induction_on with
  | empty => simp
  | insert a J ha ih =>
      -- The two sign patterns extending `S ⊆ J` differ by `± w a`.
      have key : ∀ S ∈ J.powerset,
          ‖signedSum w S (insert a J)‖ ^ 2
              + ‖signedSum w (insert a S) (insert a J)‖ ^ 2
            = 2 * (‖signedSum w S J‖ ^ 2 + ‖w a‖ ^ 2) := by
        intro S hS
        have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
        rw [signedSum_insert_of_notMem ha haS, signedSum_insert_insert ha]
        linarith [parallelogram_law_with_norm (𝕜 := 𝕜) (signedSum w S J) (w a)]
      have hsplit : ∑ S ∈ (insert a J).powerset, ‖signedSum w S (insert a J)‖ ^ 2
          = ∑ S ∈ J.powerset, (‖signedSum w S (insert a J)‖ ^ 2
              + ‖signedSum w (insert a S) (insert a J)‖ ^ 2) := by
        rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
      rw [hsplit, Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_add_distrib, ih,
        Finset.sum_const, Finset.card_powerset, Finset.card_insert_of_notMem ha,
        Finset.sum_insert ha, nsmul_eq_mul]
      push_cast
      ring

/-- **Sign averaging (inequality form).** If every signed sum `∑_j ε_j w_j`
(`j ∈ J`) has norm at most `M`, then `∑_{j ∈ J} ‖w_j‖² ≤ M²`. As above, `𝕜` is
explicit since it does not occur in the statement. -/
lemma sum_norm_sq_le_sq_of_signedSum_le (𝕜 : Type*) [RCLike 𝕜] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {w : ι → H} {J : Finset ι} {M : ℝ}
    (hM : ∀ S ⊆ J, ‖signedSum w S J‖ ≤ M) :
    ∑ j ∈ J, ‖w j‖ ^ 2 ≤ M ^ 2 := by
  have hpow : (0 : ℝ) < 2 ^ J.card := by positivity
  have hle : 2 ^ J.card * ∑ j ∈ J, ‖w j‖ ^ 2 ≤ 2 ^ J.card * M ^ 2 := by
    rw [← sum_powerset_norm_signedSum_sq 𝕜 w J]
    calc ∑ S ∈ J.powerset, ‖signedSum w S J‖ ^ 2
        ≤ ∑ _S ∈ J.powerset, M ^ 2 :=
          Finset.sum_le_sum fun S hS =>
            pow_le_pow_left₀ (norm_nonneg _) (hM S (Finset.mem_powerset.mp hS)) 2
      _ = 2 ^ J.card * M ^ 2 := by
          rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
          push_cast
          ring
  exact le_of_mul_le_mul_left hle hpow

end Averaging

/-! ## Little Grothendieck for an `ℓ_∞` domain -/

section Linfty

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι : Type*} [DecidableEq ι]

/-- The coordinates of a signed sum of unit vectors of `ℓ_∞` are `0` and `±1`. -/
lemma signedSum_single_coord (S J : Finset ι) (i : ι) :
    (signedSum (fun j => lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)) S J) i
      = if i ∈ J then (if i ∈ S then (1 : 𝕜) else -1) else 0 := by
  have hterm : ∀ j : ι,
      ((if j ∈ S then lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)
          else -lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)) : lp (fun _ : ι => 𝕜) ∞) i
        = if i = j then (if j ∈ S then (1 : 𝕜) else -1) else 0 := by
    intro j
    by_cases hj : j ∈ S <;>
      by_cases hij : i = j <;>
        simp [hj, hij, lp.single_apply]
  rw [signedSum, lp.coeFn_sum, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  simp

/-- Signed sums of the unit vectors of `ℓ_∞` are contained in the unit ball. -/
lemma norm_signedSum_single_le_one (S J : Finset ι) :
    ‖signedSum (fun j => lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)) S J‖ ≤ 1 := by
  refine lp.norm_le_of_forall_le zero_le_one fun i => ?_
  rw [signedSum_single_coord]
  by_cases hiJ : i ∈ J <;> by_cases hiS : i ∈ S <;> simp [hiJ, hiS]

/-- **Little Grothendieck inequality for `ℓ_∞ → H`.** For every bounded operator
`B` from `ℓ_∞` into a Hilbert space and every finite set `J` of indices,
`∑_{j ∈ J} ‖B e_j‖² ≤ ‖B‖²`; that is, `B` is Hilbert–Schmidt on the unit vectors
with `‖B‖_HS ≤ ‖B‖`. -/
theorem sum_norm_sq_apply_single_le (B : lp (fun _ : ι => 𝕜) ∞ →L[𝕜] H) (J : Finset ι) :
    ∑ j ∈ J, ‖B (lp.single ∞ j (1 : 𝕜))‖ ^ 2 ≤ ‖B‖ ^ 2 := by
  refine sum_norm_sq_le_sq_of_signedSum_le 𝕜 fun S _ => ?_
  have hmap : signedSum (fun j => B (lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜))) S J
      = B (signedSum (fun j => lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)) S J) := by
    rw [signedSum, signedSum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ S <;> simp [hj]
  rw [hmap]
  calc ‖B (signedSum (fun j => lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)) S J)‖
      ≤ ‖B‖ * ‖signedSum (fun j => lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)) S J‖ :=
        B.le_opNorm _
    _ ≤ ‖B‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_signedSum_single_le_one S J) (norm_nonneg B)
    _ = ‖B‖ := mul_one _

end Linfty

/-! ## The dual bound for an `ℓ₁` codomain -/

section L1

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- Finite partial sums of the absolute values of the coordinates of an
`ℓ₁`-vector are bounded by its norm. -/
lemma sum_norm_apply_le_norm_l1 (f : lp (fun _ : ι => 𝕜) 1) (J : Finset ι) :
    ∑ j ∈ J, ‖f j‖ ≤ ‖f‖ := by
  have h := lp.sum_rpow_le_norm_rpow (p := 1)
    (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal) f J
  simpa using h

omit [DecidableEq ι] in
/-- **Little Grothendieck inequality for `H → ℓ₁`.** If `w j` are the *rows* of
`A : H → ℓ₁`, i.e. `⟪w j, x⟫ = (A x) j` for all `x`, then
`∑_{j ∈ J} ‖w j‖² ≤ ‖A‖²` for every finite `J`.

This is the little Grothendieck bound applied to the adjoint of `A`, which maps
`ℓ_∞ = ℓ₁'` into `H`; formulating it via the rows avoids constructing the
adjoint. The signed sums are bounded here by
`re ⟪z, z⟫ = re (∑_j ε_j (A z)_j) ≤ ‖A z‖₁ ≤ ‖A‖ ‖z‖`. -/
theorem sum_norm_sq_row_le (A : H →L[𝕜] lp (fun _ : ι => 𝕜) 1) {w : ι → H}
    (hw : ∀ (j : ι) (x : H), (inner 𝕜 (w j) x : 𝕜) = A x j) (J : Finset ι) :
    ∑ j ∈ J, ‖w j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  classical
  refine sum_norm_sq_le_sq_of_signedSum_le 𝕜 fun S _ => ?_
  set z := signedSum w S J with hz
  -- Expand `⟪z, z⟫` using the rows: the signs reappear on the coordinates of `A z`.
  have hinner : (inner 𝕜 z z : 𝕜)
      = ∑ j ∈ J, (if j ∈ S then (A z) j else -((A z) j)) := by
    rw [hz, signedSum, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ S
    · rw [ite_eq_left hj, ite_eq_left hj, hw]
    · rw [ite_eq_right hj, ite_eq_right hj, inner_neg_left, hw]
  have hle : ‖z‖ ^ 2 ≤ ‖A‖ * ‖z‖ :=
    calc ‖z‖ ^ 2 = RCLike.re (inner 𝕜 z z : 𝕜) := (inner_self_eq_norm_sq z).symm
      _ ≤ ‖(inner 𝕜 z z : 𝕜)‖ := RCLike.re_le_norm _
      _ = ‖∑ j ∈ J, (if j ∈ S then (A z) j else -((A z) j))‖ := by rw [hinner]
      _ ≤ ∑ j ∈ J, ‖(A z) j‖ := by
          refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun j _ => ?_)
          by_cases hj : j ∈ S <;> simp [hj]
      _ ≤ ‖A z‖ := sum_norm_apply_le_norm_l1 _ J
      _ ≤ ‖A‖ * ‖z‖ := A.le_opNorm z
  rcases (norm_nonneg z).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg A
  · nlinarith [hle, hpos]

end L1

/-! ## Summability and the `ℓ₂`-norm as a sum of squares -/

section Tsum

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Over the index set `ℕ`, the row bound makes `∑_j ‖w_j‖²` a convergent
series (its partial sums are nonnegative and bounded by `‖A‖²`). -/
lemma summable_norm_sq_row (A : H →L[𝕜] lp (fun _ : ℕ => 𝕜) 1) {w : ℕ → H}
    (hw : ∀ (j : ℕ) (x : H), (inner 𝕜 (w j) x : 𝕜) = A x j) :
    Summable fun j => ‖w j‖ ^ 2 :=
  summable_of_sum_range_le (fun _ => by positivity) fun n =>
    sum_norm_sq_row_le A hw (Finset.range n)

/-- The squared `ℓ₂`-norm is the sum of the squared coordinate norms. -/
lemma norm_sq_eq_tsum_norm_sq {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (f : lp E 2) : ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) f
  rw [show ((2 : ℝ≥0∞)).toReal = (2 : ℝ) by norm_num] at h
  simpa using h

end Tsum

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
