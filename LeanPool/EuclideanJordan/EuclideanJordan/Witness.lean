/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.EuclideanJordan.EuclideanJordan.FormallyReal
public import LeanPool.EuclideanJordan.EuclideanJordan.Block
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Jordan
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Inner



/-!
# Non-vacuity of the Peirce layer, on the Hermitian-matrix carrier

`EuclideanJordan/Peirce.lean` and `EuclideanJordan/PeirceMul.lean` are stated over an abstract
    real commutative
Jordan algebra and are *conditional* throughout: every theorem assumes `c ∘ c = c`, and the
sharper ones assume an element with `c ∘ y = ½ y`. Conditional theorems are worth exactly
as much as their hypotheses are satisfiable. This file is the check that they are.

Four things are verified, and they are different claims.

**1. The instance stack resolves on `H₂(ℂ)`.** The four typeclass hypotheses of the Peirce
layer — `NonUnitalNonAssocCommRing`, `IsCommJordan`, `Module ℝ`, `IsScalarTower ℝ` — are all
satisfied by `HermitianMat (Fin 2) ℂ` under the scoped Jordan instances of
`EuclideanJordan/Vendor/HermitianMat/Jordan.lean` (namespace `HermMul`). Nothing had to be
built for this: the vendored file carries `IsCommJordan (HermitianMat d 𝕜)` already.
★ This is also why the layer assumes `IsScalarTower ℝ J J` rather than `SMulCommClass`:
they are interchangeable for a commutative product, and `IsScalarTower` is the one the
carrier supplies.

**2. The `1/2`-eigenspace is not zero.** This is the part that could have gone wrong
silently. Every rule in `EuclideanJordan/PeirceMul.lean` mentioning `J_{1/2}` would be
    *vacuously true*
on a carrier where the half-space is trivial — and the half-space **is** trivial for the two
idempotents one reaches for first, `0` and `1`. So a witness is exhibited: `cWit` is the
rank-one projection `diag(1,0)`, `xWit` is the off-diagonal `[[0,1],[1,0]]`, and
`cWit_mul_xWit` proves `cWit ∘ xWit = ½ · xWit` with `xWit ≠ 0`.

**3. `HermitianMat` is formally real** (§4 below), so `EuclideanJordan/FormallyReal.lean`'s
    no-nilpotents
theorem is live rather than conditional on an uninhabited hypothesis.

**4. The diagonal matrix units are a complete Jordan frame** (§5 below), witnessing
`IsOrthIdemFamily` — which had **no** carrier here until then, leaving every theorem of
`EuclideanJordan/Frame.lean` and `EuclideanJordan/Block.lean` conditional on a structure nothing
    was known to satisfy.

★ **Scope.** This is non-vacuity, not coverage: it shows the Peirce hypotheses have a model
with all three components nonzero, and nothing more. The rank-two carrier is used because it
is the smallest place where a `1/2`-eigenvector exists, not because rank two matters here.
-/

@[expose] public section

open HermMul EuclideanJordan

namespace EuclideanJordan.Witness

/-- The rank-two carrier. -/
abbrev H2 := HermitianMat (Fin 2) ℂ

/-! ### 1. The instance stack -/

noncomputable example : NonUnitalNonAssocCommRing H2 := inferInstance
noncomputable example : IsCommJordan H2 := inferInstance
noncomputable example : Module ℝ H2 := inferInstance
noncomputable example : IsScalarTower ℝ H2 H2 := inferInstance

/-! ### 2. An idempotent with a nonzero `1/2`-eigenspace -/

/-- The rank-one projection `diag(1,0)`. -/
noncomputable def cWit : H2 := HermitianMat.diagonal ℂ ![1, 0]

/-- The off-diagonal Hermitian matrix `[[0,1],[1,0]]`. -/
def xWit : H2 :=
  ⟨!![0, 1; 1, 0], by
    simp only [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

theorem cWit_mat : cWit.mat = Matrix.diagonal (fun i => ((![1, 0] : Fin 2 → ℝ) i : ℂ)) := rfl

theorem xWit_mat : xWit.mat = !![0, 1; 1, 0] := rfl

theorem xWit_ne_zero : xWit ≠ 0 := by
  intro h
  have h2 : xWit.mat 0 1 = (0 : H2).mat 0 1 := by rw [h]
  rw [xWit_mat] at h2
  simp at h2

/-- `cWit` is an idempotent for the Jordan product. -/
theorem cWit_idem : cWit * cWit = cWit := by
  apply HermitianMat.ext
  rw [mul_eq_symmMul, HermitianMat.symmMul_toMat, cWit_mat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  norm_num

/-- **The half-space is inhabited by a nonzero element**, so every `J_{1/2}` rule in
`EuclideanJordan/PeirceMul.lean` has content on this carrier. -/
theorem cWit_mul_xWit : cWit * xWit = (2 : ℝ)⁻¹ • xWit := by
  apply HermitianMat.ext
  rw [mul_eq_symmMul, HermitianMat.symmMul_toMat, cWit_mat, xWit_mat]
  change _ = (2 : ℝ)⁻¹ • xWit.mat
  rw [xWit_mat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMul_diagonal]

/-! ### 3. The layer, exercised

Three theorems of the abstract layer instantiated at the witness. They are corollaries with
no new content — the point is that the hypotheses discharge against a real carrier rather
than remaining hypothetical. -/

/-- `eigen_half_mul_half` at the witness: `xWit ∘ xWit` has no `1/2`-component. -/
theorem witness_half_mul_half : cWit * (cWit * (xWit * xWit)) = cWit * (xWit * xWit) :=
  eigen_half_mul_half cWit_idem cWit_mul_xWit cWit_mul_xWit

/-- `peirceHalf_mul_half_eq_zero` at the witness. -/
theorem witness_peirceHalf_eq_zero : peirceHalf cWit (xWit * xWit) = 0 :=
  peirceHalf_mul_half_eq_zero cWit_idem cWit_mul_xWit cWit_mul_xWit

/-- `exists_peirce_decomposition` at the witness: `xWit` itself splits. -/
theorem witness_decomposition :
    ∃ y₁ yₕ y₀ : H2, cWit * y₁ = y₁ ∧ cWit * yₕ = (2 : ℝ)⁻¹ • yₕ ∧ cWit * y₀ = 0
      ∧ xWit = y₁ + yₕ + y₀ :=
  exists_peirce_decomposition cWit_idem xWit

/-- **The middle branch of `eigenvalue_trichotomy` is attained.**  Without this the
trichotomy would still be true with an empty `1/2` case, and every `J_{1/2}` rule with it.

★ This statement replaced a genuinely vacuous one, and the replacement is the finding.  The
first version here read `(2:ℝ)⁻¹ = 0 ∨ (2:ℝ)⁻¹ = (2:ℝ)⁻¹ ∨ (2:ℝ)⁻¹ = 1`, discharged by
`eigenvalue_trichotomy` at the witness — a disjunction whose middle disjunct is `rfl`, so it
is provable with no witness, no carrier and no Jordan identity.  A vacuous statement inside
the very file written to rule out vacuity. -/
theorem witness_half_attained : ∃ y : H2, y ≠ 0 ∧ cWit * y = (2 : ℝ)⁻¹ • y :=
  ⟨xWit, xWit_ne_zero, cWit_mul_xWit⟩

/-! ### 4. Formal reality on the Hermitian-matrix carrier

★★★ **This section closes the exposure `EuclideanJordan/FormallyReal.lean` declares in its own
    docstring**:
that `IsFormallyReal` had no carrier here, so every theorem depending on it was conditional on
an uninhabited hypothesis.

`HermitianMat d 𝕜` is formally real, and the proof is the classical one: the Jordan square of
a Hermitian matrix is its matrix square, whose trace is the squared Frobenius norm, so a
vanishing sum of squares is a vanishing sum of non-negative reals.

★ Nothing new is built here — `inner_self_nonneg` and `InnerProductCore.definite` are vendored
(`EuclideanJordan/Vendor/HermitianMat/Inner.lean`) and the Jordan-square identity is
`symmMul_self`. What was
missing was, once again, the *application*. -/

section FormallyReal

variable {d : Type*} [Fintype d] [DecidableEq d] {𝕜 : Type*} [RCLike 𝕜]

/-- The trace functional is additive along a `Finset` sum. -/
private theorem inner_sum_left_one {ι : Type*} (t : Finset ι) (g : ι → HermitianMat d 𝕜) :
    inner ℝ (∑ j ∈ t, g j) (1 : HermitianMat d 𝕜)
      = ∑ j ∈ t, inner ℝ (g j) (1 : HermitianMat d 𝕜) := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih => rw [Finset.sum_cons, HermitianMat.inner_add_left, ih, Finset.sum_cons]

/-- The Jordan square has the same trace as the matrix square: `Tr[(A ∘ A)·1] = Tr[A·A]`. -/
private theorem inner_mul_self_one (A : HermitianMat d 𝕜) :
    inner ℝ (A * A) (1 : HermitianMat d 𝕜) = inner ℝ A A := by
  rw [HermitianMat.inner_def, HermitianMat.inner_def, mul_eq_symmMul, HermitianMat.symmMul_self]
  simp

omit [DecidableEq d] in
/-- **`H_d(𝕜)` is formally real.** -/
instance instIsFormallyReal : EuclideanJordan.IsFormallyReal (HermitianMat d 𝕜) where
  eq_zero_of_sum_mul_self := by
    let : DecidableEq d := Classical.decEq d
    intro ι s f hsum i hi
    have h0 : ∑ j ∈ s, inner ℝ (f j * f j) (1 : HermitianMat d 𝕜) = 0 := by
      rw [← inner_sum_left_one, hsum]
      simp
    have h1 : ∑ j ∈ s, inner ℝ (f j) (f j) = 0 := by
      rw [← h0]
      exact Finset.sum_congr rfl fun j _ => (inner_mul_self_one (f j)).symm
    have h2 : inner ℝ (f i) (f i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => HermitianMat.inner_self_nonneg (f j))).mp h1 i hi
    exact HermitianMat.InnerProductCore.definite (f i) h2

/-- The nilpotence theorem, live on the carrier: a Hermitian matrix with a vanishing
Jordan power is zero. -/
theorem hermitian_eq_zero_of_jpow_eq_zero {A : HermitianMat d 𝕜} {n : ℕ}
    (h : EuclideanJordan.jpow A n = 0) : A = 0 :=
  EuclideanJordan.eq_zero_of_jpow_eq_zero n h

/-- Albert's theorem, live on the carrier. -/
theorem hermitian_jpow_mul_jpow (A : HermitianMat d 𝕜) (m n : ℕ) :
    EuclideanJordan.jpow A m * EuclideanJordan.jpow A n
      = EuclideanJordan.jpow A (m + n + 1) :=
  EuclideanJordan.jpow_mul_jpow A m n

end FormallyReal

/-! ### 5. A Jordan frame on the carrier

★★ **This closes the last vacuity exposure in the EJA layer.** `IsOrthIdemFamily`
(`EuclideanJordan/Frame.lean`) had **no witness**, so every theorem of
    `EuclideanJordan/Frame.lean` and
`EuclideanJordan/Block.lean` was conditional on a structure nothing was known to satisfy — the same
exposure that section 4 closed for `IsFormallyReal`. The diagonal matrix units supply it.

★ Completeness (`∑ i, p i = 1`) is proved here even though **no theorem in the abstract layer
assumes it** — deliberately, per `EuclideanJordan/Frame.lean`'s docstring, since completeness is
    what the
spectral theorem produces rather than what the Peirce theory needs. Having it on the carrier
shows the abstract results are not being kept general by weakening past what the intended
model satisfies. -/

section JordanFrame

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The diagonal matrix units `E_ii`, as Hermitian matrices. -/
noncomputable def diagFrame (i : d) : HermitianMat d ℂ :=
  HermitianMat.diagonal ℂ (fun j => if j = i then 1 else 0)

omit [Fintype d] in
theorem diagFrame_mat (i : d) :
    (diagFrame i).mat = Matrix.diagonal (fun j => ((if j = i then (1 : ℝ) else 0 : ℝ) : ℂ)) :=
  rfl

/-- **The diagonal matrix units are a family of orthogonal idempotents.** -/
theorem diagFrame_orthIdem :
    EuclideanJordan.IsOrthIdemFamily (diagFrame (d := d)) where
  idem i := by
    apply HermitianMat.ext
    rw [mul_eq_symmMul, HermitianMat.symmMul_toMat, diagFrame_mat,
      Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases h : a = b <;> simp [Matrix.smul_apply, h]
    split_ifs <;> norm_num
  orth i j hij := by
    apply HermitianMat.ext
    rw [mul_eq_symmMul, HermitianMat.symmMul_toMat, diagFrame_mat, diagFrame_mat,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases h : a = b <;> simp [Matrix.smul_apply, h]
    split_ifs with h1 h2 <;> simp_all

/-- The frame is **complete**: the matrix units sum to the identity. -/
theorem diagFrame_sum : (∑ i, diagFrame (d := d) i) = 1 := by
  have hsum : (∑ i, diagFrame (d := d) i).mat = ∑ i, (diagFrame (d := d) i).mat := by simp
  apply HermitianMat.ext
  rw [hsum]
  ext a b
  simp only [Matrix.sum_apply, diagFrame_mat, Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; simp [apply_ite ((↑) : ℝ → ℂ)]
  · simp [h]

end JordanFrame

end EuclideanJordan.Witness
