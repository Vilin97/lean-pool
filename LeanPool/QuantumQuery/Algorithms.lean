/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Finite quantum algorithms, query oracles, and simulation

Ported from the corresponding upstream modules listed by the source sections below.
References beginning with `Source` name these retained sections.
-/

public section

section SourceQuantumFiniteHilbert

/-!
# Finite-dimensional complex Hilbert space for the query model

A quantum state on a finite basis type `H` is a function `ψ : H → ℂ`, an operator
is a `Matrix H H ℂ`, and the action of an operator on a state is `U *ᵥ ψ`.  We
keep this *raw*, in the same spirit as the adversary side of the project: the
inner product is a plain finite sum

  `qInner ψ φ = ∑ h, star (ψ h) * φ h`,

conjugate-linear in the first argument, and the squared norm is
`qNormSq ψ = ∑ h, ‖ψ h‖²`.

Why not `EuclideanSpace ℂ H`?  Because most arguments downstream — the query
decomposition of a state by its index register, the progress measure of the
adversary lower bound, the oracle's action on a product basis — are
manipulations of finite sums over the basis, and `WithLp`/`PiLp` coercions get
in the way of exactly those.  So the raw form is the default.

It is not a quarantine, though: `qInner_eq_euclidean` and `qNormSq_eq_euclidean`
below are **public**, and `SourceQuantumProjector` crosses by them deliberately,
building subspaces and orthogonal projectors in `EuclideanSpace` where Mathlib's
theory lives and carrying the results back as matrices.  Raw by default, Euclidean
where Mathlib is stronger.

## Main definitions

* `qInner`, `qNormSq`, `IsQState` (a unit vector).
* `qBasis h` — the computational basis state `|h⟩`.
* `Matrix.unitaryGroup H ℂ` is Mathlib's; `qPerm e` is the unitary that sends
  `|b⟩` to `|e b⟩`, which is how every permutation oracle enters.
* `IsQProjector P` and the reflection `qRefl P = 2P - 1`.

## Main results

* `qInner_mulVec_mulVec`, `qNormSq_mulVec`, `IsQState.mulVec` — a unitary
  preserves inner products, squared norms, and unit states.
* `qInner_norm_le` — Cauchy–Schwarz.
* `qInner_mulVec_left` — moving an operator across the inner product.
* `qPerm_mem_unitaryGroup`, `qPerm_mulVec`, `qPerm_involutive`.
* `qRefl_mem_unitaryGroup`, `qRefl_mul_self`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type*} [Fintype H] [DecidableEq H]

/-! ## The inner product -/

/-- The Hermitian inner product on `H → ℂ`, conjugate-linear in the **first**
argument (the physicists' convention, and Mathlib's). -/
@[expose]
def qInner (ψ φ : H → ℂ) : ℂ := star ψ ⬝ᵥ φ

omit [DecidableEq H] in
lemma qInner_def (ψ φ : H → ℂ) : qInner ψ φ = ∑ h, star (ψ h) * φ h := rfl

/-- The squared norm of a state, as a real number. -/
@[expose]
def qNormSq (ψ : H → ℂ) : ℝ := ∑ h, Complex.normSq (ψ h)

omit [DecidableEq H] in
lemma qNormSq_def (ψ : H → ℂ) : qNormSq ψ = ∑ h, Complex.normSq (ψ h) := rfl

/-- A (pure) quantum state: a unit vector. -/
@[expose]
def IsQState (ψ : H → ℂ) : Prop := qNormSq ψ = 1

omit [DecidableEq H] in
lemma qNormSq_nonneg (ψ : H → ℂ) : 0 ≤ qNormSq ψ :=
  Finset.sum_nonneg fun h _ => Complex.normSq_nonneg (ψ h)

omit [DecidableEq H] in
@[simp] lemma qInner_self (ψ : H → ℂ) : qInner ψ ψ = (qNormSq ψ : ℂ) := by
  classical
  rw [qInner_def, qNormSq_def]
  push_cast
  exact Finset.sum_congr rfl fun h _ => Complex.normSq_eq_conj_mul_self.symm

omit [DecidableEq H] in
lemma qInner_conj (ψ φ : H → ℂ) : star (qInner ψ φ) = qInner φ ψ := by
  classical
  rw [qInner_def, qInner_def, star_sum]
  exact Finset.sum_congr rfl fun h _ => by rw [star_mul, star_star, mul_comm]

omit [DecidableEq H] in
@[simp] lemma qInner_zero_left (φ : H → ℂ) : qInner (0 : H → ℂ) φ = 0 := by
  simp [qInner_def]

omit [DecidableEq H] in
@[simp] lemma qInner_zero_right (ψ : H → ℂ) : qInner ψ (0 : H → ℂ) = 0 := by
  simp [qInner_def]

omit [DecidableEq H] in
lemma qInner_add_right (ψ φ χ : H → ℂ) :
    qInner ψ (φ + χ) = qInner ψ φ + qInner ψ χ := by
  simp only [qInner_def, Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

omit [DecidableEq H] in
lemma qInner_add_left (ψ φ χ : H → ℂ) :
    qInner (ψ + φ) χ = qInner ψ χ + qInner φ χ := by
  simp only [qInner_def, Pi.add_apply, star_add, add_mul]
  exact Finset.sum_add_distrib

omit [DecidableEq H] in
lemma qInner_sub_left (ψ φ χ : H → ℂ) :
    qInner (ψ - φ) χ = qInner ψ χ - qInner φ χ := by
  simp only [qInner_def, Pi.sub_apply, star_sub, sub_mul]
  rw [Finset.sum_sub_distrib]

omit [DecidableEq H] in
lemma qInner_sub_right (ψ φ χ : H → ℂ) :
    qInner ψ (φ - χ) = qInner ψ φ - qInner ψ χ := by
  simp only [qInner_def, Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]

omit [DecidableEq H] in
lemma qInner_smul_right (c : ℂ) (ψ φ : H → ℂ) :
    qInner ψ (c • φ) = c * qInner ψ φ := by
  simp only [qInner_def, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => by ring

omit [DecidableEq H] in
lemma qInner_smul_left (c : ℂ) (ψ φ : H → ℂ) :
    qInner (c • ψ) φ = star c * qInner ψ φ := by
  simp only [qInner_def, Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => by ring

omit [DecidableEq H] in
lemma qInner_sum_right {α : Type*} (ψ : H → ℂ) (s : Finset α) (F : α → (H → ℂ)) :
    qInner ψ (∑ i ∈ s, F i) = ∑ i ∈ s, qInner ψ (F i) := by
  simp only [qInner_def]
  rw [show (∑ h, star (ψ h) * (∑ i ∈ s, F i) h) = ∑ h, ∑ i ∈ s, star (ψ h) * F i h from
    Finset.sum_congr rfl fun h _ => by rw [Finset.sum_apply, Finset.mul_sum]]
  exact Finset.sum_comm

omit [DecidableEq H] in
lemma qInner_sum_left {α : Type*} (s : Finset α) (F : α → (H → ℂ)) (φ : H → ℂ) :
    qInner (∑ i ∈ s, F i) φ = ∑ i ∈ s, qInner (F i) φ := by
  simp only [qInner_def]
  rw [show (∑ h, star ((∑ i ∈ s, F i) h) * φ h) = ∑ h, ∑ i ∈ s, star (F i h) * φ h from
    Finset.sum_congr rfl fun h _ => by
      rw [Finset.sum_apply, star_sum, Finset.sum_mul]]
  exact Finset.sum_comm

omit [DecidableEq H] in
@[simp] lemma qNormSq_zero : qNormSq (0 : H → ℂ) = 0 := by simp [qNormSq_def]

omit [DecidableEq H] in
lemma qNormSq_smul (c : ℂ) (ψ : H → ℂ) :
    qNormSq (c • ψ) = Complex.normSq c * qNormSq ψ := by
  classical
  rw [qNormSq_def, qNormSq_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => by
    rw [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]

omit [DecidableEq H] in
/-- The parallelogram expansion. -/
lemma qNormSq_add (ψ φ : H → ℂ) :
    qNormSq (ψ + φ) = qNormSq ψ + qNormSq φ + 2 * (qInner ψ φ).re := by
  classical
  have h : qInner (ψ + φ) (ψ + φ)
      = qInner ψ ψ + qInner φ φ + (qInner ψ φ + qInner φ ψ) := by
    rw [qInner_add_left, qInner_add_right, qInner_add_right]
    ring
  have h2 : (qInner φ ψ).re = (qInner ψ φ).re := by
    rw [← qInner_conj ψ φ]
    simp
  have h3 := congrArg Complex.re h
  rw [qInner_self, qInner_self, qInner_self] at h3
  simp only [Complex.add_re, Complex.ofReal_re] at h3
  rw [h3, h2]
  ring

omit [DecidableEq H] in
lemma qNormSq_eq_zero_iff {ψ : H → ℂ} : qNormSq ψ = 0 ↔ ψ = 0 := by
  classical
  constructor
  · intro h
    funext k
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun h _ => Complex.normSq_nonneg (ψ h))).mp h k (Finset.mem_univ k)
    simpa using Complex.normSq_eq_zero.mp this
  · rintro rfl
    simp

/-! ## The Euclidean bridge

The sanctioned crossing between the raw representation used everywhere here and
Mathlib's inner-product-space library.  These two lemmas are **public on
purpose**: the reflection constructors of the upper bound build a subspace in
`EuclideanSpace ℂ H`, take Mathlib's `Submodule.starProjection`, transport it
back through `WithLp.linearEquiv`, and turn it into a matrix with
`LinearMap.toMatrix'`.  That route needs to state its correctness in raw terms,
and these are the lemmas that let it.

Everything *else* in this section stays raw: the bridge is a door, not a move.
-/

omit [DecidableEq H] in
lemma qInner_eq_euclidean (ψ φ : H → ℂ) :
    qInner ψ φ = inner ℂ (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) (WithLp.toLp 2 φ) := by
  classical
  rw [EuclideanSpace.inner_toLp_toLp, qInner_def, dotProduct]
  exact Finset.sum_congr rfl fun h _ => by rw [mul_comm]; rfl

omit [DecidableEq H] in
lemma qNormSq_eq_euclidean (ψ : H → ℂ) :
    qNormSq ψ = ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ H)‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun h _ => by positivity)]
  exact Finset.sum_congr rfl fun h _ => Complex.normSq_eq_norm_sq (ψ h)

omit [DecidableEq H] in
/-- **Cauchy–Schwarz.** -/
theorem qInner_norm_le (ψ φ : H → ℂ) :
    ‖qInner ψ φ‖ ≤ Real.sqrt (qNormSq ψ) * Real.sqrt (qNormSq φ) := by
  classical
  rw [qInner_eq_euclidean, qNormSq_eq_euclidean, qNormSq_eq_euclidean,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact norm_inner_le_norm _ _

omit [DecidableEq H] in
/-- The triangle inequality, in squared-norm form. -/
theorem sqrt_qNormSq_add_le (ψ φ : H → ℂ) :
    Real.sqrt (qNormSq (ψ + φ)) ≤ Real.sqrt (qNormSq ψ) + Real.sqrt (qNormSq φ) := by
  classical
  rw [qNormSq_eq_euclidean, qNormSq_eq_euclidean, qNormSq_eq_euclidean,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]
  exact norm_add_le _ _

/-! ## Basis states -/

/-- The computational basis state `|h⟩`. -/
def qBasis (h : H) : H → ℂ := Pi.single h 1

omit [Fintype H] in
@[simp] lemma qBasis_apply (h k : H) : qBasis h k = if k = h then 1 else 0 := by
  rw [qBasis, Pi.single_apply]

@[simp] lemma qNormSq_qBasis (h : H) : qNormSq (qBasis h) = 1 := by
  rw [qNormSq_def, Finset.sum_eq_single h]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

lemma isQState_qBasis (h : H) : IsQState (qBasis h) := qNormSq_qBasis h

/-! ## Unitaries -/

lemma one_mem_qUnitary : (1 : Matrix H H ℂ) ∈ Matrix.unitaryGroup H ℂ :=
  one_mem _

lemma mul_mem_qUnitary {U V : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hV : V ∈ Matrix.unitaryGroup H ℂ) : U * V ∈ Matrix.unitaryGroup H ℂ :=
  mul_mem hU hV

lemma conjTranspose_mul_self_of_unitary {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) : Uᴴ * U = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp hU
  rwa [Matrix.star_eq_conjTranspose] at this

omit [DecidableEq H] in
/-- **Moving an operator across the inner product.** -/
lemma qInner_mulVec_left (M : Matrix H H ℂ) (ψ φ : H → ℂ) :
    qInner (M *ᵥ ψ) φ = qInner ψ (Mᴴ *ᵥ φ) := by
  rw [qInner, qInner, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]

/-- **A unitary preserves the inner product.** -/
theorem qInner_mulVec_mulVec {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (ψ φ : H → ℂ) : qInner (U *ᵥ ψ) (U *ᵥ φ) = qInner ψ φ := by
  rw [qInner, qInner, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, conjTranspose_mul_self_of_unitary hU, Matrix.vecMul_one]

/-- **A unitary preserves the squared norm.** -/
theorem qNormSq_mulVec {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (ψ : H → ℂ) : qNormSq (U *ᵥ ψ) = qNormSq ψ := by
  have h := qInner_mulVec_mulVec hU ψ ψ
  rw [qInner_self, qInner_self] at h
  exact_mod_cast h

/-- **A unitary maps states to states.** -/
theorem IsQState.mulVec {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    {ψ : H → ℂ} (hψ : IsQState ψ) : IsQState (U *ᵥ ψ) := by
  rw [IsQState, qNormSq_mulVec hU]
  exact hψ

/-! ## Permutation unitaries

Every oracle in this development is a permutation of the computational basis, so
this is the workhorse.  Note the inverse in the definition: Mathlib's
`Equiv.Perm.permMatrix σ` acts on *coordinates* by `v ∘ σ`, i.e. it sends the
basis state `|b⟩` to `|σ⁻¹ b⟩`; `qPerm e` is normalized so that it sends `|b⟩` to
`|e b⟩`. -/

/-- The unitary that sends the basis state `|b⟩` to `|e b⟩`. -/
def qPerm (e : Equiv.Perm H) : Matrix H H ℂ := (e⁻¹).permMatrix ℂ

lemma qPerm_mulVec (e : Equiv.Perm H) (ψ : H → ℂ) : qPerm e *ᵥ ψ = ψ ∘ ⇑(e⁻¹) := by
  rw [qPerm, Matrix.permMatrix_mulVec]

lemma qPerm_mulVec_apply (e : Equiv.Perm H) (ψ : H → ℂ) (h : H) :
    (qPerm e *ᵥ ψ) h = ψ (e.symm h) := by
  rw [qPerm_mulVec]
  rfl

/-- **A permutation unitary sends basis states to basis states.** -/
lemma qPerm_mulVec_qBasis (e : Equiv.Perm H) (p : H) :
    qPerm e *ᵥ qBasis p = qBasis (e p) := by
  funext k
  rw [qPerm_mulVec_apply, qBasis_apply, qBasis_apply]
  by_cases h : k = e p
  · simp [h]
  · have h' : ¬ (e.symm k = p) := fun hk => h (by rw [← hk, Equiv.apply_symm_apply])
    simp [h, h']

omit [Fintype H] in
@[simp] lemma qPerm_one : qPerm (1 : Equiv.Perm H) = 1 := by
  simp [qPerm]

lemma qPerm_mul (e f : Equiv.Perm H) : qPerm (e * f) = qPerm e * qPerm f := by
  rw [qPerm, qPerm, qPerm, _root_.mul_inv_rev, Matrix.permMatrix_mul]

lemma qPerm_mem_unitaryGroup (e : Equiv.Perm H) :
    qPerm e ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, qPerm,
    Matrix.conjTranspose_permMatrix, inv_inv, ← Matrix.permMatrix_mul]
  simp

/-- An involutive permutation gives a self-inverse unitary: query = unquery. -/
lemma qPerm_mul_self_of_involutive {e : Equiv.Perm H} (he : Function.Involutive e) :
    qPerm e * qPerm e = 1 := by
  rw [← qPerm_mul]
  have : e * e = 1 := Equiv.ext fun h => he h
  rw [this, qPerm_one]

/-! ## Projectors and reflections -/

/-- An orthogonal projector. -/
@[expose]
def IsQProjector (P : Matrix H H ℂ) : Prop := Pᴴ = P ∧ P * P = P

/-- The reflection about the range of a projector, `2P - 1`. -/
@[expose]
def qRefl (P : Matrix H H ℂ) : Matrix H H ℂ := (2 : ℂ) • P - 1

lemma qRefl_conjTranspose {P : Matrix H H ℂ} (hP : IsQProjector P) :
    (qRefl P)ᴴ = qRefl P := by
  rw [qRefl, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP.1,
    Matrix.conjTranspose_one]
  norm_num

/-- **A reflection is involutive.** -/
lemma qRefl_mul_self {P : Matrix H H ℂ} (hP : IsQProjector P) :
    qRefl P * qRefl P = 1 := by
  rw [qRefl, sub_mul, mul_sub, mul_sub, Matrix.smul_mul, Matrix.mul_smul, hP.2,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
  match_scalars <;> ring

omit [DecidableEq H] in
/-- **A projector shrinks**: `‖Pψ‖ ≤ ‖ψ‖`. -/
theorem IsQProjector.qNormSq_mulVec_le {P : Matrix H H ℂ} (hP : IsQProjector P)
    (ψ : H → ℂ) : qNormSq (P *ᵥ ψ) ≤ qNormSq ψ := by
  classical
  have horth : (qInner (P *ᵥ ψ) (ψ - P *ᵥ ψ)).re = 0 := by
    rw [qInner_mulVec_left, hP.1, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hP.2,
      sub_self, qInner_zero_right, Complex.zero_re]
  have hsplit : P *ᵥ ψ + (ψ - P *ᵥ ψ) = ψ := by abel
  have hexp := qNormSq_add (P *ᵥ ψ) (ψ - P *ᵥ ψ)
  rw [hsplit, horth] at hexp
  have := qNormSq_nonneg (ψ - P *ᵥ ψ)
  linarith

/-- **Conjugating a projector by a unitary gives a projector.** -/
lemma IsQProjector.conj {P U : Matrix H H ℂ} (hP : IsQProjector P)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) : IsQProjector (U * P * Uᴴ) := by
  have h : Uᴴ * U = 1 := conjTranspose_mul_self_of_unitary hU
  constructor
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP.1,
      Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, h, Matrix.one_mul, ← Matrix.mul_assoc P P, hP.2]

/-- **A reflection is unitary.** -/
lemma qRefl_mem_unitaryGroup {P : Matrix H H ℂ} (hP : IsQProjector P) :
    qRefl P ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    qRefl_conjTranspose hP]
  exact qRefl_mul_self hP

end QuantumQueryComplexity

end SourceQuantumFiniteHilbert

section SourceQuantumTail

/-!
# The two counting bounds of the independent-run analysis

Pure finite probability, stated over an arbitrary weight; no quantum imports.

* `sum_filter_ne_le_sum_coord` — **the union bound over coordinates**: any
  weight of the patterns different from a target is at most the sum over
  coordinates of the weight of the patterns wrong at that coordinate.
  (A standalone utility, currently unused: the tuple join ended up using
  Weierstrass on the diagonal instead, and plurality amplification
  (`SourceQuantumPlurality`) uses the sharper exponential-moment
  argument `sum_prod_tail_le` rather than a union bound.)
* `sum_prod_majority_le` — **the majority tail**: if each coordinate's wrong
  value carries probability at most `ε ≤ 1`, the product weight of the
  patterns with at least `t` wrong coordinates is at most `2^k·εᵗ`.  With
  per-run error `1/16` and `t = ⌈k/2⌉` this is `≤ 2^{-k}` — no Chernoff
  bound and no independence formalism: the product structure is supplied
  exactly by the bank-swap compiler, and the tail is one count over
  patterns.
* `sum_prod_tail_le` — **the exponential-moment tail** (moved here from `SourceQuantumPlurality`, so
  that circuit utilities can use it without the lower-bound development): the weight of the
  records with at least `t` wrong coordinates is at most `(1 + ε)^k / 2^t`.  Unlike the
  majority tail it decays at base error `1/3`: `(4/3)^k / 2^{k/2} = (8/9)^{k/2}`.
-/

namespace QuantumQueryComplexity

/-- **The union bound over coordinates**: every pattern different from `b` is
wrong somewhere, so its weight is charged to some coordinate. -/
lemma sum_filter_ne_le_sum_coord {k : ℕ} (w : (Fin k → Bool) → ℝ)
    (hw : ∀ y, 0 ≤ w y) (b : Fin k → Bool) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin k → Bool => y ≠ b), w y)
      ≤ ∑ j : Fin k, ∑ y ∈ Finset.univ.filter
          (fun y : Fin k → Bool => y j ≠ b j), w y := by
  have hite : ∀ (y : Fin k → Bool) (j : Fin k),
      (0 : ℝ) ≤ if y j ≠ b j then w y else 0 := by
    intro y j
    by_cases h : y j ≠ b j <;> simp [h, hw y]
  have hle : ∀ y ∈ Finset.univ.filter (fun y : Fin k → Bool => y ≠ b),
      w y ≤ ∑ j : Fin k, (if y j ≠ b j then w y else 0) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ b j := by
      by_contra hcon
      rw [not_exists] at hcon
      exact hy (funext fun j => not_not.mp (hcon j))
    calc w y = ∑ l ∈ ({j} : Finset (Fin k)),
          (if y l ≠ b l then w y else 0) := by simp [hj]
      _ ≤ ∑ l : Fin k, (if y l ≠ b l then w y else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun l _ _ => hite y l
  calc (∑ y ∈ Finset.univ.filter (fun y : Fin k → Bool => y ≠ b), w y)
      ≤ ∑ y ∈ Finset.univ.filter (fun y : Fin k → Bool => y ≠ b),
          ∑ j : Fin k, (if y j ≠ b j then w y else 0) :=
        Finset.sum_le_sum hle
    _ ≤ ∑ y : Fin k → Bool, ∑ j : Fin k, (if y j ≠ b j then w y else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun y _ _ => Finset.sum_nonneg fun j _ => hite y j
    _ = ∑ j : Fin k, ∑ y : Fin k → Bool, (if y j ≠ b j then w y else 0) :=
        Finset.sum_comm
    _ = ∑ j : Fin k, ∑ y ∈ Finset.univ.filter
          (fun y : Fin k → Bool => y j ≠ b j), w y := by
        exact Finset.sum_congr rfl fun j _ => (Finset.sum_filter _ _).symm

/-- **The majority tail**: patterns with at least `t` wrong coordinates carry
product weight at most `2^k·εᵗ`. -/
lemma sum_prod_majority_le {k t : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (p : Fin k → Bool → ℝ) (b : Fin k → Bool)
    (hp0 : ∀ j y, 0 ≤ p j y) (hp1 : ∀ j y, p j y ≤ 1)
    (hpe : ∀ j, p j (!(b j)) ≤ ε) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin k → Bool =>
        t ≤ (Finset.univ.filter (fun j => y j ≠ b j)).card),
      ∏ j, p j (y j))
      ≤ 2 ^ k * ε ^ t := by
  have hterm : ∀ y : Fin k → Bool,
      t ≤ (Finset.univ.filter (fun j => y j ≠ b j)).card →
      (∏ j, p j (y j)) ≤ ε ^ t := by
    intro y hy
    set S := Finset.univ.filter (fun j : Fin k => y j ≠ b j) with hS
    have hsplit : (∏ j, p j (y j))
        = (∏ j ∈ S, p j (y j)) * ∏ j ∈ Sᶜ, p j (y j) :=
      (Finset.prod_mul_prod_compl S _).symm
    have h1 : (∏ j ∈ S, p j (y j)) ≤ ε ^ S.card := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod₀ (fun j _ => hp0 j _) fun j hj => ?_
      have hne : y j ≠ b j := by
        simpa [hS] using (Finset.mem_filter.mp hj).2
      have hval : y j = !(b j) := by
        cases hb : b j <;> cases hyj : y j <;> simp_all
      rw [hval]
      exact hpe j
    have h2 : (∏ j ∈ Sᶜ, p j (y j)) ≤ 1 :=
      Finset.prod_le_one₀ (fun j _ => hp0 j _) (fun j _ => hp1 j _)
    have h3 : ε ^ S.card ≤ ε ^ t := pow_le_pow_of_le_one hε0 hε1 hy
    have hS0 : (0 : ℝ) ≤ ε ^ S.card := pow_nonneg hε0 _
    calc (∏ j, p j (y j))
        = (∏ j ∈ S, p j (y j)) * ∏ j ∈ Sᶜ, p j (y j) := hsplit
      _ ≤ ε ^ S.card * 1 := by
          refine mul_le_mul h1 h2 ?_ hS0
          exact Finset.prod_nonneg fun j _ => hp0 j _
      _ ≤ ε ^ t := by rw [mul_one]; exact h3
  calc (∑ y ∈ Finset.univ.filter (fun y : Fin k → Bool =>
          t ≤ (Finset.univ.filter (fun j => y j ≠ b j)).card),
        ∏ j, p j (y j))
      ≤ ∑ _y ∈ Finset.univ.filter (fun y : Fin k → Bool =>
          t ≤ (Finset.univ.filter (fun j => y j ≠ b j)).card), ε ^ t := by
        refine Finset.sum_le_sum fun y hy => ?_
        exact hterm y (by simpa using (Finset.mem_filter.mp hy).2)
    _ ≤ ∑ _y : Fin k → Bool, ε ^ t := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => pow_nonneg hε0 t
    _ = 2 ^ k * ε ^ t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

section ExpMoment

variable {O : Type} [Fintype O] [DecidableEq O]

/-! ## The exponential-moment tail -/

/-- The number of coordinates at which the record `y` differs from `b`. -/
@[expose]
def wrongCount {k : ℕ} (y b : Fin k → O) : ℕ :=
  (Finset.univ.filter (fun j => y j ≠ b j)).card

omit [Fintype O] in
lemma prod_ite_eq_two_pow_wrongCount {k : ℕ} (y b : Fin k → O) :
    (∏ j, (if y j ≠ b j then (2 : ℝ) else 1)) = 2 ^ wrongCount y b := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  rfl

/-- **The exponential-moment tail.**  If each coordinate's wrong values carry
probability at most `ε`, the product weight of the records with at least `t`
wrong coordinates, times `2^t`, is at most `(1 + ε)^k`: the weight of
`2^{wrong}` factorizes coordinatewise as `∏ (1 + Pr[wrong]) ≤ (1 + ε)^k`,
and `2^t ≤ 2^{wrong}` on the tail. -/
theorem sum_prod_tail_le {k t : ℕ} {ε : ℝ}
    (p : Fin k → O → ℝ) (b : Fin k → O)
    (hp0 : ∀ j o, 0 ≤ p j o) (hp1 : ∀ j, ∑ o, p j o ≤ 1)
    (hpe : ∀ j, ∑ o ∈ Finset.univ.filter (fun o => o ≠ b j), p j o ≤ ε) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin k → O => t ≤ wrongCount y b),
        ∏ j, p j (y j)) * 2 ^ t
      ≤ (1 + ε) ^ k := by
  have hm0 : ∀ (j : Fin k) (o : O), (0 : ℝ) ≤ if o ≠ b j then 2 else 1 := by
    intro j o
    split_ifs <;> norm_num
  have hfactor : ∀ j : Fin k,
      (∑ o, p j o * (if o ≠ b j then (2 : ℝ) else 1)) ≤ 1 + ε := by
    intro j
    have hsplit : ∀ o, p j o * (if o ≠ b j then (2 : ℝ) else 1)
        = p j o + (if o ≠ b j then p j o else 0) := by
      intro o
      split_ifs <;> ring
    simp only [hsplit]
    rw [Finset.sum_add_distrib, ← Finset.sum_filter]
    exact add_le_add (hp1 j) (hpe j)
  have hstep : ∀ y ∈ Finset.univ.filter (fun y : Fin k → O => t ≤ wrongCount y b),
      (∏ j, p j (y j)) * 2 ^ t
        ≤ ∏ j, p j (y j) * (if y j ≠ b j then (2 : ℝ) else 1) := by
    intro y hy
    have hy' : t ≤ wrongCount y b := (Finset.mem_filter.mp hy).2
    rw [Finset.prod_mul_distrib, prod_ite_eq_two_pow_wrongCount]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hy')
      (Finset.prod_nonneg fun j _ => hp0 j _)
  calc (∑ y ∈ Finset.univ.filter (fun y : Fin k → O => t ≤ wrongCount y b),
          ∏ j, p j (y j)) * 2 ^ t
      = ∑ y ∈ Finset.univ.filter (fun y : Fin k → O => t ≤ wrongCount y b),
          (∏ j, p j (y j)) * 2 ^ t := Finset.sum_mul _ _ _
    _ ≤ ∑ y ∈ Finset.univ.filter (fun y : Fin k → O => t ≤ wrongCount y b),
          ∏ j, p j (y j) * (if y j ≠ b j then (2 : ℝ) else 1) :=
        Finset.sum_le_sum hstep
    _ ≤ ∑ y : Fin k → O, ∏ j, p j (y j) * (if y j ≠ b j then (2 : ℝ) else 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun y _ _ => Finset.prod_nonneg fun j _ => mul_nonneg (hp0 j _) (hm0 j _)
    _ = ∏ j, ∑ o, p j o * (if o ≠ b j then (2 : ℝ) else 1) :=
        (Fintype.prod_sum fun j o => p j o * (if o ≠ b j then (2 : ℝ) else 1)).symm
    _ ≤ ∏ _j : Fin k, (1 + ε) :=
        Finset.prod_le_prod₀
          (fun j _ => Finset.sum_nonneg fun o _ => mul_nonneg (hp0 j o) (hm0 j o))
          (fun j _ => hfactor j)
    _ = (1 + ε) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end ExpMoment

end QuantumQueryComplexity

end SourceQuantumTail

section SourceQuantumFidelity

/-!
# Fidelity bounds for a unitary, against a fixed vector and against a far pair

The two generic Hilbert-space estimates behind the state-conversion
measurement.  The quantity a Hadamard test reads out is `Re⟪ψ, Uψ⟫`, and the
detector `U` of `SourceQuantumInputDetector` is designed to make it large on one kind
of input and small on the other.  This section proves the two sides in the
abstract, for an arbitrary unitary `U` on an arbitrary finite space:

* **the positive side** (`le_mul_re_qInner_mulVec_of_fixed`): if `U` fixes
  `φ`, then `Re⟪ψ, Uψ⟫ ≥ 2|⟪φ,ψ⟫|²/‖φ‖² − ‖ψ‖²` — stated multiplied out by
  `‖φ‖⁴`, so `φ = 0` needs no special case and no division appears;
* **the negative side** (`re_qInner_mulVec_le_of_perp`): if `ψ = ψN + ψF`
  orthogonally and `‖UψF + ψF‖` is small — `U` is close to `−1` on the far
  part — then `Re⟪ψ, Uψ⟫ ≤ ‖ψ‖‖ψN‖ + ‖ψ‖‖UψF + ψF‖ − ‖ψF‖²`.

No spectral decomposition of `U` occurs.  The positive bound is one
Cauchy–Schwarz application to the auxiliary vector `χ = ‖φ‖²ψ − ⟪φ,ψ⟫φ`, the
component of `‖φ‖²ψ` orthogonal to `φ`: since `U` and `Uᴴ` both fix `φ`, the
plane spanned by `φ` and the pair `χ, Uχ` splits the form `⟪ψ, Uψ⟫` exactly,
and Cauchy–Schwarz on the `χ`-part is the only estimate.  The negative bound
is Cauchy–Schwarz three times, with the orthogonality supplying the exact
`−‖ψF‖²` term.

Also here: `qInner_mulVec_one_sub_mulVec`, the orthogonality of a projector's
range and its complement's range on the same vector — the form in which the
chord windows enter the negative side downstream.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

/-- A unitary that fixes a vector: so does its adjoint. -/
lemma conjTranspose_mulVec_of_fixed {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) {φ : H → ℂ} (hφ : U *ᵥ φ = φ) :
    Uᴴ *ᵥ φ = φ := by
  conv_lhs => rw [← hφ]
  rw [Matrix.mulVec_mulVec, conjTranspose_mul_self_of_unitary hU,
    Matrix.one_mulVec]

private lemma star_ofReal (r : ℝ) : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
  rw [RCLike.star_def, Complex.conj_ofReal]

private lemma star_mul_self_eq (b : ℂ) :
    star b * b = ((Complex.normSq b : ℝ) : ℂ) := by
  rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self]

private lemma mul_star_self_eq (b : ℂ) :
    b * star b = ((Complex.normSq b : ℝ) : ℂ) := by
  rw [mul_comm]; exact star_mul_self_eq b

omit [DecidableEq H] in
/-- `Re z ≥ −‖ψ‖‖φ‖` for an inner product `z = ⟪ψ, φ⟫`. -/
private lemma neg_le_re_qInner (ψ φ : H → ℂ) :
    -(Real.sqrt (qNormSq ψ) * Real.sqrt (qNormSq φ)) ≤ (qInner ψ φ).re := by
  classical
  have h1 := Complex.abs_re_le_norm (qInner ψ φ)
  have h2 := qInner_norm_le ψ φ
  have := abs_le.mp (h1.trans h2)
  linarith [this.1]

omit [DecidableEq H] in
/-- `Re z ≤ ‖ψ‖‖φ‖` for an inner product `z = ⟪ψ, φ⟫`. -/
private lemma re_qInner_le (ψ φ : H → ℂ) :
    (qInner ψ φ).re ≤ Real.sqrt (qNormSq ψ) * Real.sqrt (qNormSq φ) := by
  classical
  have h1 := Complex.abs_re_le_norm (qInner ψ φ)
  have h2 := qInner_norm_le ψ φ
  have := abs_le.mp (h1.trans h2)
  linarith [this.2]

/-- **The fidelity lower bound.**  A unitary that fixes `φ` satisfies, on every
`ψ`, `Re⟪ψ, Uψ⟫ ≥ 2|⟪φ,ψ⟫|²/‖φ‖² − ‖ψ‖²` — multiplied out by `‖φ‖⁴`, so no
positivity of `‖φ‖` is assumed and no division appears. -/
theorem le_mul_re_qInner_mulVec_of_fixed {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) {φ : H → ℂ} (hφ : U *ᵥ φ = φ)
    (ψ : H → ℂ) :
    2 * Complex.normSq (qInner φ ψ) * qNormSq φ - qNormSq φ ^ 2 * qNormSq ψ
      ≤ qNormSq φ ^ 2 * (qInner ψ (U *ᵥ ψ)).re := by
  set b : ℂ := qInner φ ψ with hb
  set χ : H → ℂ := ((qNormSq φ : ℝ) : ℂ) • ψ + (-b) • φ with hχ
  -- the orthogonality facts: `φ ⊥ χ` and `φ ⊥ Uχ`
  have hφχ : qInner φ χ = 0 := by
    rw [hχ, qInner_add_right, qInner_smul_right, qInner_smul_right,
      qInner_self, ← hb]
    ring
  have hχφ : qInner χ φ = 0 := by
    have h := congrArg star hφχ
    rwa [qInner_conj, star_zero] at h
  have hUχ : U *ᵥ χ = ((qNormSq φ : ℝ) : ℂ) • (U *ᵥ ψ) + (-b) • φ := by
    rw [hχ, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hφ]
  have hφUχ : qInner φ (U *ᵥ χ) = 0 := by
    have h1 : qInner (U *ᵥ χ) φ = qInner χ φ := by
      rw [qInner_mulVec_left, conjTranspose_mulVec_of_fixed hU hφ]
    have h := congrArg star (h1.trans hχφ)
    rwa [qInner_conj, star_zero] at h
  -- the split of `‖φ‖²ψ` along `φ` and its complement
  have hdec : ((qNormSq φ : ℝ) : ℂ) • ψ = χ + b • φ := by
    rw [hχ]; module
  have hUdec : ((qNormSq φ : ℝ) : ℂ) • (U *ᵥ ψ) = U *ᵥ χ + b • φ := by
    rw [hUχ]; module
  have hψφ : qInner ψ φ = star b := by rw [hb, qInner_conj]
  -- the exact complex identity: `‖φ‖⁴⟪ψ,Uψ⟫ = ⟪χ,Uχ⟫ + |⟪φ,ψ⟫|²‖φ‖²`
  have hmain : ((qNormSq φ : ℝ) : ℂ) ^ 2 * qInner ψ (U *ᵥ ψ)
      = qInner χ (U *ᵥ χ)
        + ((Complex.normSq b : ℝ) : ℂ) * ((qNormSq φ : ℝ) : ℂ) := by
    have hL : qInner (((qNormSq φ : ℝ) : ℂ) • ψ)
          (((qNormSq φ : ℝ) : ℂ) • (U *ᵥ ψ))
        = ((qNormSq φ : ℝ) : ℂ) ^ 2 * qInner ψ (U *ᵥ ψ) := by
      rw [qInner_smul_left, qInner_smul_right, star_ofReal]
      ring
    have hR : qInner (χ + b • φ) (U *ᵥ χ + b • φ)
        = qInner χ (U *ᵥ χ)
          + ((Complex.normSq b : ℝ) : ℂ) * ((qNormSq φ : ℝ) : ℂ) := by
      simp only [qInner_add_left, qInner_add_right, qInner_smul_left,
        qInner_smul_right, qInner_self]
      rw [hχφ, hφUχ]
      linear_combination ((qNormSq φ : ℝ) : ℂ) * mul_star_self_eq b
    rw [← hL, hdec, hUdec, hR]
  -- extract real parts
  have hre : qNormSq φ ^ 2 * (qInner ψ (U *ᵥ ψ)).re
      = (qInner χ (U *ᵥ χ)).re + Complex.normSq b * qNormSq φ := by
    have h := congrArg Complex.re hmain
    rwa [Complex.add_re,
      show (((qNormSq φ : ℝ) : ℂ) ^ 2 * qInner ψ (U *ᵥ ψ)).re
          = qNormSq φ ^ 2 * (qInner ψ (U *ᵥ ψ)).re from by
        rw [← Complex.ofReal_pow, Complex.re_ofReal_mul],
      show (((Complex.normSq b : ℝ) : ℂ) * ((qNormSq φ : ℝ) : ℂ)).re
          = Complex.normSq b * qNormSq φ from by
        rw [← Complex.ofReal_mul, Complex.ofReal_re]] at h
  -- Cauchy–Schwarz on the `χ`-part
  have hCS : -(qNormSq χ) ≤ (qInner χ (U *ᵥ χ)).re := by
    have h := neg_le_re_qInner χ (U *ᵥ χ)
    rwa [qNormSq_mulVec hU, Real.mul_self_sqrt (qNormSq_nonneg χ)] at h
  -- the norm of `χ`, exactly
  have hχnorm : qNormSq χ
      = qNormSq φ ^ 2 * qNormSq ψ - Complex.normSq b * qNormSq φ := by
    have hcross : qInner (((qNormSq φ : ℝ) : ℂ) • ψ) ((-b) • φ)
        = ((-(qNormSq φ * Complex.normSq b) : ℝ) : ℂ) := by
      rw [qInner_smul_left, qInner_smul_right, star_ofReal, hψφ]
      push_cast
      linear_combination (-((qNormSq φ : ℝ) : ℂ)) * mul_star_self_eq b
    rw [hχ, qNormSq_add, qNormSq_smul, qNormSq_smul, Complex.normSq_ofReal,
      Complex.normSq_neg, hcross, Complex.ofReal_re]
    ring
  rw [hχnorm] at hCS
  linarith [hre, hCS]

/-- **The fidelity upper bound.**  If `ψ` splits orthogonally into a near part
`ψN` and a far part `ψF` on which the unitary is close to `−1`, then
`Re⟪ψ, Uψ⟫ ≤ ‖ψ‖‖ψN‖ + ‖ψ‖‖UψF + ψF‖ − ‖ψF‖²`. -/
theorem re_qInner_mulVec_le_of_perp {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) {ψN ψF : H → ℂ}
    (horth : qInner ψN ψF = 0) :
    (qInner (ψN + ψF) (U *ᵥ (ψN + ψF))).re
      ≤ Real.sqrt (qNormSq (ψN + ψF)) * Real.sqrt (qNormSq ψN)
        + Real.sqrt (qNormSq (ψN + ψF)) * Real.sqrt (qNormSq (U *ᵥ ψF + ψF))
        - qNormSq ψF := by
  have hsplit : qInner (ψN + ψF) (U *ᵥ (ψN + ψF))
      = qInner (ψN + ψF) (U *ᵥ ψN) + qInner (ψN + ψF) (U *ᵥ ψF + ψF)
        - qInner (ψN + ψF) ψF := by
    rw [Matrix.mulVec_add, qInner_add_right, qInner_add_right]
    ring
  have hlast : qInner (ψN + ψF) ψF = ((qNormSq ψF : ℝ) : ℂ) := by
    rw [qInner_add_left, horth, zero_add, qInner_self]
  have h1 : (qInner (ψN + ψF) (U *ᵥ ψN)).re
      ≤ Real.sqrt (qNormSq (ψN + ψF)) * Real.sqrt (qNormSq ψN) := by
    have h := re_qInner_le (ψN + ψF) (U *ᵥ ψN)
    rwa [qNormSq_mulVec hU] at h
  have h2 : (qInner (ψN + ψF) (U *ᵥ ψF + ψF)).re
      ≤ Real.sqrt (qNormSq (ψN + ψF)) * Real.sqrt (qNormSq (U *ᵥ ψF + ψF)) :=
    re_qInner_le _ _
  have hre := congrArg Complex.re hsplit
  rw [hlast] at hre
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at hre
  linarith

/-- **A projector's range is orthogonal to its complement's range**, on the
same vector.  The form in which the chord-window decomposition enters the
fidelity bound. -/
lemma qInner_mulVec_one_sub_mulVec {P : Matrix H H ℂ} (hP : IsQProjector P)
    (x : H → ℂ) : qInner (P *ᵥ x) ((1 - P) *ᵥ x) = 0 := by
  rw [qInner_mulVec_left, Matrix.mulVec_mulVec, hP.1]
  rw [show P * (1 - P) = 0 from by rw [Matrix.mul_sub, Matrix.mul_one, hP.2,
    sub_self], Matrix.zero_mulVec, qInner_zero_right]

end QuantumQueryComplexity

end SourceQuantumFidelity

section SourceQuantumMeasurement

/-!
# Computational-basis measurement

A measurement of the final state of a query algorithm is a projective
measurement in the computational basis, coarse-grained by a **readout map**
`p : H → O` that says which output each basis state announces.  So the only
definition needed is

  `qProb p ψ o = ∑ h with p h = o, ‖ψ h‖²`,

the probability of announcing `o`.  Deferring all measurements to the end is
without loss of generality in the query model, and general POVMs are not needed
for the characterization (see the plan, §"Design Decisions").

The companion definition `qRestrict p o ψ` is the unnormalized post-measurement
state; it is what turns statements about probabilities into statements about
inner products, which is how the adversary lower bound consumes the output
condition (`∑ o, qRestrict p o ψ = ψ`, and distinct outcomes are orthogonal).
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type*} [Fintype H] [DecidableEq H]
variable {O : Type*} [DecidableEq O]

/-- The unnormalized part of `ψ` that announces the outcome `o`. -/
@[expose]
def qRestrict (p : H → O) (o : O) (ψ : H → ℂ) : H → ℂ :=
  fun h => if p h = o then ψ h else 0

/-- **The probability that measuring `ψ` announces the outcome `o`.** -/
@[expose]
def qProb (p : H → O) (ψ : H → ℂ) (o : O) : ℝ :=
  ∑ h, if p h = o then Complex.normSq (ψ h) else 0

omit [DecidableEq H] in
lemma qProb_eq_qNormSq_qRestrict (p : H → O) (ψ : H → ℂ) (o : O) :
    qProb p ψ o = qNormSq (qRestrict p o ψ) := by
  classical
  rw [qProb, qNormSq_def]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [qRestrict]
  by_cases hh : p h = o <;> simp [hh]

omit [DecidableEq H] in
lemma qProb_nonneg (p : H → O) (ψ : H → ℂ) (o : O) : 0 ≤ qProb p ψ o := by
  classical
  rw [qProb_eq_qNormSq_qRestrict]
  exact qNormSq_nonneg _

/-- Measuring a basis state announces its readout with certainty. -/
@[simp] lemma qProb_qBasis (p : H → O) (h : H) (o : O) :
    qProb p (qBasis h) o = if p h = o then 1 else 0 := by
  rw [qProb, Finset.sum_eq_single h]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-! ## The distance-to-success bridge

None of this needs `[Fintype O]` — the sums range over `H` alone — and the
cardinality-free extraction depends on exactly that: the bridge from a
conversion-distance bound to a success probability must not reintroduce an
output-cardinality assumption. -/

omit [DecidableEq H] in
/-- The part of `ψ` that does **not** announce `o`. -/
lemma qNormSq_sub_qRestrict (p : H → O) (o : O) (ψ : H → ℂ) :
    qNormSq (ψ - qRestrict p o ψ) = qNormSq ψ - qProb p ψ o := by
  classical
  rw [qNormSq_def, qNormSq_def, qProb, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Pi.sub_apply, qRestrict]
  by_cases hh : p h = o <;> simp [hh]

omit [DecidableEq H] in
/-- **Restriction is the best sector approximation**: against any `φ`
supported on the `o`-sector, the unannounced mass of `ψ` is dominated. -/
lemma qNormSq_sub_qRestrict_le (p : H → O) (o : O) (ψ : H → ℂ)
    {φ : H → ℂ} (hφ : qRestrict p o φ = φ) :
    qNormSq (ψ - qRestrict p o ψ) ≤ qNormSq (ψ - φ) := by
  classical
  rw [qNormSq_def, qNormSq_def]
  refine Finset.sum_le_sum fun h _ => ?_
  by_cases hh : p h = o
  · simp only [Pi.sub_apply, qRestrict, hh, ite_eq_left]
    simp only [sub_self, Complex.normSq_zero]
    exact Complex.normSq_nonneg _
  · have hφh : φ h = 0 := by rw [← hφ, qRestrict, ite_eq_right hh]
    simp [Pi.sub_apply, qRestrict, hh, hφh]

omit [DecidableEq H] in
/-- **The distance-to-success bridge**, output-cardinality-free: a state
within squared distance `δ` of one supported on the `o`-sector announces
`o` with probability at least `qNormSq ψ − δ`. -/
lemma le_qProb_of_qNormSq_sub_le (p : H → O) (o : O) {ψ φ : H → ℂ}
    (hφ : qRestrict p o φ = φ) {δ : ℝ} (h : qNormSq (ψ - φ) ≤ δ) :
    qNormSq ψ - δ ≤ qProb p ψ o := by
  classical
  have h1 := qNormSq_sub_qRestrict p o ψ
  have h2 := qNormSq_sub_qRestrict_le p o ψ hφ
  linarith

/-! ## The outcomes partition the norm -/

variable [Fintype O]

omit [DecidableEq H] in
lemma sum_qProb (p : H → O) (ψ : H → ℂ) : ∑ o, qProb p ψ o = qNormSq ψ := by
  simp only [qProb, qNormSq_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp

omit [DecidableEq H] in
/-- On a state the outcome probabilities sum to one. -/
lemma sum_qProb_eq_one {ψ : H → ℂ} (hψ : IsQState ψ) (p : H → O) :
    ∑ o, qProb p ψ o = 1 := by
  classical
  rw [sum_qProb]
  exact hψ

omit [DecidableEq H] [Fintype O] in
lemma qProb_le_qNormSq (p : H → O) (ψ : H → ℂ) (o : O) :
    qProb p ψ o ≤ qNormSq ψ := by
  classical
  rw [qProb, qNormSq_def]
  exact Finset.sum_le_sum fun h _ => by
    split_ifs
    · exact le_rfl
    · exact Complex.normSq_nonneg _

omit [DecidableEq H] [Fintype O] in
lemma qProb_le_one {ψ : H → ℂ} (hψ : IsQState ψ) (p : H → O) (o : O) :
    qProb p ψ o ≤ 1 := by
  classical
  rw [← hψ]
  exact qProb_le_qNormSq p ψ o

omit [DecidableEq H] [Fintype O] in
/-- **Two distinct outcomes cannot both be likely.**  This is what forbids a
single state from answering two different questions, and hence what makes the
query model unable to compute an unobservable distinction. -/
lemma qProb_add_qProb_le_qNormSq (p : H → O) (ψ : H → ℂ) {a b : O} (hab : a ≠ b) :
    qProb p ψ a + qProb p ψ b ≤ qNormSq ψ := by
  classical
  simp only [qProb, qNormSq_def, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun h _ => ?_
  by_cases ha : p h = a
  · simp [ha, hab]
  · by_cases hb : p h = b
    · simp [hb, Ne.symm hab]
    · simp [ha, hb, Complex.normSq_nonneg]

omit [DecidableEq H] [Fintype O] in
lemma qProb_add_qProb_le_one {ψ : H → ℂ} (hψ : IsQState ψ) (p : H → O) {a b : O}
    (hab : a ≠ b) : qProb p ψ a + qProb p ψ b ≤ 1 := by
  classical
  rw [← hψ]
  exact qProb_add_qProb_le_qNormSq p ψ hab

omit [DecidableEq H] in
/-- The probability of announcing anything other than `o` is `1 - qProb p ψ o`. -/
lemma sum_qProb_ne {ψ : H → ℂ} (hψ : IsQState ψ) (p : H → O) (o : O) :
    ∑ o' ∈ Finset.univ.erase o, qProb p ψ o' = 1 - qProb p ψ o := by
  classical
  have h := sum_qProb_eq_one hψ p
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o)] at h
  linarith

/-! ## The post-measurement decomposition -/

omit [DecidableEq H] [Fintype H] in
lemma sum_qRestrict (p : H → O) (ψ : H → ℂ) : ∑ o, qRestrict p o ψ = ψ := by
  funext h
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single (p h)]
  · simp [qRestrict]
  · intro b _ hb
    simp [qRestrict, Ne.symm hb]
  · simp

omit [DecidableEq H] in
/-- **The inner product decomposes over the outcomes.**  This is the form the
adversary lower bound uses, with the readout map taken to be the query-index
register: it splits a state into the sectors the oracle acts on independently. -/
lemma qInner_eq_sum_qRestrict (p : H → O) (ψ φ : H → ℂ) :
    qInner ψ φ = ∑ o, qInner (qRestrict p o ψ) (qRestrict p o φ) := by
  classical
  have key : ∀ (o : O) (h : H),
      star (qRestrict p o ψ h) * qRestrict p o φ h
        = if p h = o then star (ψ h) * φ h else 0 := by
    intro o h
    rw [qRestrict, qRestrict]
    by_cases hh : p h = o <;> simp [hh]
  calc qInner ψ φ = ∑ h, star (ψ h) * φ h := qInner_def ψ φ
    _ = ∑ h, ∑ o, (if p h = o then star (ψ h) * φ h else 0) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.sum_ite_eq Finset.univ (p h) (fun _ => star (ψ h) * φ h),
          ite_eq_left (Finset.mem_univ _)]
    _ = ∑ o, ∑ h, (if p h = o then star (ψ h) * φ h else 0) := Finset.sum_comm
    _ = ∑ o, qInner (qRestrict p o ψ) (qRestrict p o φ) := by
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [qInner_def]
        exact Finset.sum_congr rfl fun h _ => (key o h).symm

omit [DecidableEq H] [Fintype O] in
/-- Distinct outcomes are orthogonal. -/
lemma qInner_qRestrict_of_ne (p : H → O) {a b : O} (hab : a ≠ b) (ψ φ : H → ℂ) :
    qInner (qRestrict p a ψ) (qRestrict p b φ) = 0 := by
  classical
  rw [qInner_def]
  refine Finset.sum_eq_zero fun h _ => ?_
  rw [qRestrict, qRestrict]
  by_cases ha : p h = a
  · have hb : ¬ p h = b := by rw [ha]; exact hab
    simp [hb]
  · simp [ha]

end QuantumQueryComplexity

end SourceQuantumMeasurement

section SourceQuantumOracle

/-!
# The value oracle

The basis of a query algorithm is

  `QBasis ι σ W = Option ι × Option σ × W`

— a query-index register (`none` = *idle*, no query is made), an answer register
(`none` = *blank*), and a workspace.  On input `a : ι → σ` the oracle acts as the
identity on the idle sector and, on the index `some i`, **swaps the blank answer
with the answer `some (a i)`**:

  `|i⟩|⊥⟩|w⟩ ↦ |i⟩|a i⟩|w⟩`,  `|i⟩|a i⟩|w⟩ ↦ |i⟩|⊥⟩|w⟩`,

leaving `|i⟩|s⟩|w⟩` alone for every other answer `s`.

Why this oracle rather than `|i⟩|s⟩ ↦ |i⟩|s ⊕ a i⟩`:

* it is defined for **any** finite alphabet, with no group structure on `σ`;
* it is a permutation of the basis, hence unitary for free, and an
  **involution**, so query and unquery are literally the same matrix;
* the idle index gives controlled queries at no extra cost, which is what the
  phase-detection circuit of the upper bound will need;
* on a blank answer register it returns the value coherently, which is all the
  lower bound's query decomposition uses.

It is equivalent to the Boolean XOR oracle at two queries per query, in both
directions: `SourceQuantumXorOracle` defines that oracle (with explicit idle-index
and blank-answer sectors) and `SourceQuantumSimulation` proves the equivalence.

The two lemmas that carry the whole development are `oracleMap_none` and
`oracleMap_some`: the oracle's action at a basis state with index `some i`
depends on the input **only through `a i`**.  That is the source of the
adversary lower bound's query decomposition.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

/-- The basis of a query algorithm: query index (`none` = idle), answer register
(`none` = blank), and workspace. -/
abbrev QBasis (ι σ W : Type*) : Type _ := Option ι × Option σ × W

-- Named instances keep nested query registers from expanding instance-search terms.
instance instQBasisDecidableEq {ι σ W : Type*} [DecidableEq ι] [DecidableEq σ]
    [DecidableEq W] : DecidableEq (QBasis ι σ W) :=
  inferInstanceAs (DecidableEq (Option ι × Option σ × W))

instance instQBasisFintype {ι σ W : Type*} [Fintype ι] [Fintype σ] [Fintype W] :
    Fintype (QBasis ι σ W) :=
  inferInstanceAs (Fintype (Option ι × Option σ × W))

variable {ι σ W : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- The oracle's action on the computational basis. -/
@[expose]
def oracleMap (a : ι → σ) : QBasis ι σ W → QBasis ι σ W
  | (none, t, w) => (none, t, w)
  | (some i, t, w) => (some i, Equiv.swap none (some (a i)) t, w)

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] [Fintype σ] in
@[simp] lemma oracleMap_none (a : ι → σ) (t : Option σ) (w : W) :
    oracleMap a ((none, t, w) : QBasis ι σ W) = (none, t, w) := rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] [Fintype σ] in
/-- **The oracle reads the input only at the queried index.** -/
@[simp] lemma oracleMap_some (a : ι → σ) (i : ι) (t : Option σ) (w : W) :
    oracleMap a ((some i, t, w) : QBasis ι σ W)
      = (some i, Equiv.swap none (some (a i)) t, w) := rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] [Fintype σ] in
/-- The oracle never moves the index register. -/
lemma oracleMap_fst (a : ι → σ) (p : QBasis ι σ W) : (oracleMap a p).1 = p.1 := by
  obtain ⟨(_ | i), t, w⟩ := p <;> rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] [Fintype σ] in
lemma oracleMap_snd_of_fst_none {a : ι → σ} {p : QBasis ι σ W}
    (h : p.1 = none) : (oracleMap a p).2.1 = p.2.1 := by
  obtain ⟨(_ | i), t, w⟩ := p
  · rfl
  · exact absurd h (by simp)

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] [Fintype σ] in
lemma oracleMap_snd_of_fst_some {a : ι → σ} {p : QBasis ι σ W} {i : ι}
    (h : p.1 = some i) :
    (oracleMap a p).2.1 = Equiv.swap none (some (a i)) p.2.1 := by
  obtain ⟨(_ | j), t, w⟩ := p
  · exact absurd h (by simp)
  · have hj : j = i := Option.some_injective _ h
    subst hj
    rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] [Fintype σ] in
lemma oracleMap_blank (a : ι → σ) (i : ι) (w : W) :
    oracleMap a ((some i, none, w) : QBasis ι σ W) = (some i, some (a i), w) := by
  simp

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] [Fintype σ] in
lemma oracleMap_involutive (a : ι → σ) :
    Function.Involutive (oracleMap (W := W) a) := by
  rintro ⟨(_ | i), t, w⟩
  · rfl
  · simp

/-- The oracle as a permutation of the basis. -/
@[expose]
def oraclePerm (a : ι → σ) : Equiv.Perm (QBasis ι σ W) :=
  Function.Involutive.toPerm _ (oracleMap_involutive a)

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] [Fintype σ] in
@[simp] lemma oraclePerm_apply (a : ι → σ) (p : QBasis ι σ W) :
    oraclePerm a p = oracleMap a p := rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] [Fintype σ] in
lemma oraclePerm_involutive (a : ι → σ) :
    Function.Involutive (oraclePerm (W := W) a) := oracleMap_involutive a

/-- **The oracle unitary.** -/
@[expose]
def oracleMat (a : ι → σ) : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ :=
  qPerm (oraclePerm a)

theorem oracleMat_mem_unitaryGroup (a : ι → σ) :
    oracleMat (W := W) a ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ :=
  qPerm_mem_unitaryGroup _

/-- **Query = unquery.** -/
theorem oracleMat_mul_self (a : ι → σ) :
    oracleMat (W := W) a * oracleMat a = 1 :=
  qPerm_mul_self_of_involutive (oraclePerm_involutive a)

lemma oracleMat_mulVec_apply (a : ι → σ) (ψ : QBasis ι σ W → ℂ) (p : QBasis ι σ W) :
    (oracleMat a *ᵥ ψ) p = ψ (oracleMap a p) := by
  rw [oracleMat, qPerm_mulVec_apply]
  -- `(oraclePerm a).symm` is the same function as `oracleMap a`, by construction
  rfl

/-- On the idle sector the oracle does nothing: this is what makes a query
*controlled*. -/
@[simp] lemma oracleMat_mulVec_apply_none (a : ι → σ) (ψ : QBasis ι σ W → ℂ)
    (t : Option σ) (w : W) :
    (oracleMat a *ᵥ ψ) ((none, t, w) : QBasis ι σ W) = ψ (none, t, w) := by
  rw [oracleMat_mulVec_apply, oracleMap_none]

/-- **The query decomposition.**  At a basis state with query index `some i` the
queried state depends on the input only through `a i`. -/
@[simp] lemma oracleMat_mulVec_apply_some (a : ι → σ) (ψ : QBasis ι σ W → ℂ)
    (i : ι) (t : Option σ) (w : W) :
    (oracleMat a *ᵥ ψ) ((some i, t, w) : QBasis ι σ W)
      = ψ (some i, Equiv.swap none (some (a i)) t, w) := by
  rw [oracleMat_mulVec_apply, oracleMap_some]

/-- Two inputs that agree at the index `i` give the same amplitude at every
basis state querying `i`; two inputs always agree on the idle sector. -/
theorem oracleMat_mulVec_congr {a b : ι → σ} (ψ : QBasis ι σ W → ℂ)
    {p : QBasis ι σ W} (hp : ∀ i, p.1 = some i → a i = b i) :
    (oracleMat a *ᵥ ψ) p = (oracleMat b *ᵥ ψ) p := by
  obtain ⟨(_ | i), t, w⟩ := p
  · simp
  · rw [oracleMat_mulVec_apply_some, oracleMat_mulVec_apply_some, hp i rfl]

lemma oracleMat_mulVec_qBasis (a : ι → σ) (p : QBasis ι σ W) :
    oracleMat a *ᵥ qBasis p = qBasis (oracleMap a p) := by
  rw [oracleMat, qPerm_mulVec_qBasis]
  rfl

end QuantumQueryComplexity

end SourceQuantumOracle

section SourceQuantumAlgorithm

/-!
# Quantum query algorithms

A **quantum query algorithm** is an initial unit state on `QBasis ι σ Work`, a
sequence of input-independent unitaries, and a readout map for the final
computational-basis measurement.  On input `a : ι → σ` it evolves as

  `ψ₀ = U₀ |init⟩`,   `ψ_{t+1} = U_{t+1} O_a ψ_t`,

so `A.state a t` is the state after **`t` queries**; `A.prob a t o` is the
probability that measuring it announces `o`.  This is the standard
deferred-measurement form of the model.

## Design notes

* The unitaries are indexed by all of `ℕ`.  An algorithm is not tied to a query
  count: the query count is the time `t` at which one reads off the answer.
  This removes every `Fin (q+1)` cast from the development, and makes "the same
  algorithm run longer" a statement about `t`, not a new structure.
* The workspace `W` is a **parameter**, not a field.  Bundling it inside the
  structure makes `A.Work` appear in the index type of every matrix, and then
  `rw` and instance search fail on goals that are true by `rfl` (the type
  `QBasis ι σ A.Work` is only *definitionally* the concrete workspace a
  construction used).  Quantifying over `W` is deferred to `QueryCounts` in
  `SourceQuantumComplexity`, which is the one place it costs anything.  Everything lives
  in `Type` (universe 0): every index type, alphabet and workspace in this
  project is concrete.
* Correctness is stated **promise-natively**, through `read : X → ι → σ`.  The
  total case is `X = (ι → σ)` with `read = id`.

## Main results

* `QAlg.state_isQState` — the algorithm's state is a unit vector at all times.
* `computesWithErrorOn_const` — a constant function needs no queries.
* `computesWithErrorOn_proj` — one query reads one coordinate exactly.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {W : Type} [Fintype W] [DecidableEq W]
variable {X : Type} [Fintype X]

/-- **A quantum query algorithm** with output type `O` and workspace `W`. -/
structure QAlg (ι σ O W : Type) [Fintype ι] [DecidableEq ι] [Fintype σ]
    [DecidableEq σ] [Fintype W] [DecidableEq W] where
  /-- The initial state. -/
  init : QBasis ι σ W → ℂ
  /-- The initial state is a unit vector. -/
  init_isQState : IsQState init
  /-- The input-independent unitaries; `step t` is applied after the `t`-th
  query (and `step 0` before the first). -/
  step : ℕ → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ
  /-- Each step is unitary. -/
  step_unitary : ∀ t, step t ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ
  /-- The final measurement's readout map. -/
  readout : QBasis ι σ W → O

namespace QAlg

/-- **The state of `A` on input `a` after `t` queries.** -/
@[expose]
def state (A : QAlg ι σ O W) (a : ι → σ) : ℕ → (QBasis ι σ W → ℂ)
  | 0 => A.step 0 *ᵥ A.init
  | t + 1 => A.step (t + 1) *ᵥ (oracleMat a *ᵥ A.state a t)

@[simp] lemma state_zero (A : QAlg ι σ O W) (a : ι → σ) :
    A.state a 0 = A.step 0 *ᵥ A.init := rfl

@[simp] lemma state_succ (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) :
    A.state a (t + 1) = A.step (t + 1) *ᵥ (oracleMat a *ᵥ A.state a t) := rfl

/-- **The state stays a unit vector.** -/
theorem state_isQState (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) :
    IsQState (A.state a t) := by
  induction t with
  | zero => exact IsQState.mulVec (A.step_unitary 0) A.init_isQState
  | succ t ih =>
      rw [state_succ]
      exact IsQState.mulVec (A.step_unitary (t + 1))
        (IsQState.mulVec (oracleMat_mem_unitaryGroup a) ih)

variable [DecidableEq O]

/-- The probability that `A`, run for `t` queries on input `a`, announces `o`. -/
@[expose]
def prob (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) (o : O) : ℝ :=
  qProb A.readout (A.state a t) o

lemma prob_nonneg (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) (o : O) :
    0 ≤ A.prob a t o := qProb_nonneg _ _ _

lemma prob_le_one (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) (o : O) :
    A.prob a t o ≤ 1 := by
  classical
  exact qProb_le_one (A.state_isQState a t) _ _

end QAlg

/-! ## Bounded-error correctness -/

variable [DecidableEq O]

/-- **`A` computes `f` on the promise `read` with error at most `ε` in `q`
queries.** -/
@[expose]
def ComputesWithErrorOn (A : QAlg ι σ O W) (q : ℕ) (read : X → ι → σ) (f : X → O)
    (ε : ℝ) : Prop :=
  ∀ x : X, 1 - ε ≤ A.prob (read x) q (f x)

omit [Fintype X] in
lemma ComputesWithErrorOn.mono {A : QAlg ι σ O W} {q : ℕ} {read : X → ι → σ}
    {f : X → O} {ε ε' : ℝ} (h : ComputesWithErrorOn A q read f ε) (hε : ε ≤ ε') :
    ComputesWithErrorOn A q read f ε' :=
  fun x => le_trans (by linarith) (h x)

/-! ## Two sanity constructions

These are the smallest end-to-end uses of the model: they exercise the oracle's
action on a basis state and the measurement rule, and they are the base cases of
every later construction. -/

/-- The zero-query algorithm that always announces `c`. -/
def constAlg (ι σ : Type) [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (c : O) : QAlg ι σ O Unit where
  init := qBasis (none, none, ())
  init_isQState := isQState_qBasis _
  step := fun _ => 1
  step_unitary := fun _ => one_mem_qUnitary
  readout := fun _ => c

omit [Fintype X] in
/-- **A constant function needs no queries.** -/
theorem computesWithErrorOn_const (read : X → ι → σ) (c : O) {f : X → O}
    (hf : ∀ x, f x = c) {ε : ℝ} (hε : 0 ≤ ε) :
    ComputesWithErrorOn (constAlg ι σ c) 0 read f ε := by
  intro x
  have h : (constAlg ι σ c).prob (read x) 0 (f x) = 1 := by
    simp [QAlg.prob, constAlg, hf x]
  rw [h]
  linarith

/-- The one-query algorithm that queries the coordinate `i` and announces the
answer register. -/
def projAlg (σ : Type) [Fintype σ] [DecidableEq σ] {ι : Type} [Fintype ι]
    [DecidableEq ι] (i : ι) : QAlg ι σ (Option σ) Unit where
  init := qBasis (some i, none, ())
  init_isQState := isQState_qBasis _
  step := fun _ => 1
  step_unitary := fun _ => one_mem_qUnitary
  readout := fun p => p.2.1

omit [Fintype X] in
/-- **One query reads one coordinate, exactly.** -/
theorem computesWithErrorOn_proj (read : X → ι → σ) (i : ι) {ε : ℝ} (hε : 0 ≤ ε) :
    ComputesWithErrorOn (projAlg σ i) 1 read (fun x => some (read x i)) ε := by
  intro x
  have h : (projAlg σ i).prob (read x) 1 (some (read x i)) = 1 := by
    simp [QAlg.prob, projAlg, oracleMat_mulVec_qBasis]
  rw [h]
  linarith

end QuantumQueryComplexity

end SourceQuantumAlgorithm

section SourceQuantumBlocks

/-!
# Workspace extension and register-indexed families

Extending a workspace by a register `V` and acting **block-diagonally** on it is
the single primitive behind two things the circuit layer needs: *lifting* an
operator to a larger workspace (a constant family) and *controlling* it on a
register value (a family that is the identity elsewhere).

  `blockFam fam` applies `fam v` on the sector where the extra register holds `v`.

It is defined as Mathlib's `Matrix.blockDiagonal` read through the reindexing
`regEquiv : QBasis ι σ (V × W) ≃ QBasis ι σ W × V`, so the algebra —
multiplicativity, unit, adjoint — is inherited rather than re-proved.

## Acceptance contracts

* `blockFam_mul`, `blockFam_one`, `blockFam_conjTranspose`,
  `blockFam_mem_unitaryGroup` — it is a monoid map into the unitaries.
* `blockFam_mulVec_embed` — its action on the **encoded subspace**
  `embedReg v ψ`, the sector where the register holds `v`.  This is the only
  form in which `blockFam` gets used: statements about a controlled operator are
  statements about encoded states, never global matrix identities.
* `blockFam_oracle` — the oracle ignores the workspace, so on an extended
  workspace it *is* a constant block family.  This is what lets a query pass
  through a workspace extension unchanged.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ V W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Two matrices agreeing on every basis vector are equal. -/
lemma matrix_ext_of_mulVec_qBasis {H : Type} [Fintype H] [DecidableEq H]
    {M N : Matrix H H ℂ} (h : ∀ r, M *ᵥ qBasis r = N *ᵥ qBasis r) : M = N := by
  ext p q
  have hpq := congrFun (h q) p
  simpa [Matrix.mulVec, dotProduct, qBasis_apply, Finset.sum_ite_eq'] using hpq

/-- The extended basis, split as (rest, extra register). -/
@[expose]
def regEquiv : QBasis ι σ (V × W) ≃ QBasis ι σ W × V where
  toFun p := ((p.1, p.2.1, p.2.2.2), p.2.2.1)
  invFun x := (x.1.1, x.1.2.1, (x.2, x.1.2.2))
  left_inv := by rintro ⟨k, t, v, w⟩; rfl
  right_inv := by rintro ⟨⟨k, t, w⟩, v⟩; rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype V] [Fintype W]
    [Fintype ι] [Fintype σ] in
@[simp] lemma regEquiv_apply (p : QBasis ι σ (V × W)) :
    regEquiv p = ((p.1, p.2.1, p.2.2.2), p.2.2.1) := by
  classical
  exact rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype V] [Fintype W]
    [Fintype ι] [Fintype σ] in
@[simp] lemma regEquiv_symm_apply (x : QBasis ι σ W × V) :
    (regEquiv (ι := ι) (σ := σ) (V := V) (W := W)).symm x
      = (x.1.1, x.1.2.1, (x.2, x.1.2.2)) := by
  classical
  exact rfl

/-- **A register-indexed family of operators**, acting block-diagonally on the
extra register. -/
def blockFam (fam : V → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    Matrix (QBasis ι σ (V × W)) (QBasis ι σ (V × W)) ℂ :=
  (Matrix.blockDiagonal fam).submatrix regEquiv regEquiv

/-- Lift an operator to an extended workspace: the constant family. -/
def liftReg (V : Type) [DecidableEq V]
    (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    Matrix (QBasis ι σ (V × W)) (QBasis ι σ (V × W)) ℂ :=
  blockFam (fun _ : V => U)

/-! ## The algebra -/

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] in
theorem blockFam_mul (f g : V → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    blockFam f * blockFam g = blockFam (fun v => f v * g v) := by
  rw [blockFam, blockFam, blockFam, Matrix.submatrix_mul_equiv, Matrix.blockDiagonal_mul]

omit [Fintype V] [Fintype W] [Fintype ι] [Fintype σ] in
theorem blockFam_one :
    blockFam (fun _ : V => (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)) = 1 := by
  rw [blockFam, show (fun _ : V => (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ))
    = (1 : V → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) from rfl,
    Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype V] [Fintype W] [Fintype ι]
    [Fintype σ] in
theorem blockFam_conjTranspose (f : V → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    (blockFam f)ᴴ = blockFam (fun v => (f v)ᴴ) := by
  rw [blockFam, blockFam, Matrix.conjTranspose_submatrix, Matrix.blockDiagonal_conjTranspose]

theorem blockFam_mem_unitaryGroup {f : V → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hf : ∀ v, f v ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) :
    blockFam f ∈ Matrix.unitaryGroup (QBasis ι σ (V × W)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    blockFam_conjTranspose, blockFam_mul]
  rw [show (fun v => (f v)ᴴ * f v) = (fun _ : V => (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ))
    from funext fun v => conjTranspose_mul_self_of_unitary (hf v)]
  exact blockFam_one

lemma liftReg_mem_unitaryGroup {U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) :
    liftReg V U ∈ Matrix.unitaryGroup (QBasis ι σ (V × W)) ℂ :=
  blockFam_mem_unitaryGroup fun _ => hU

/-! ## The encoded subspace -/

/-- **The encoded subspace**: `ψ`, placed in the sector where the extra register
holds `v`. -/
@[expose]
def embedReg (v : V) (ψ : QBasis ι σ W → ℂ) : QBasis ι σ (V × W) → ℂ :=
  fun p => if p.2.2.1 = v then ψ (p.1, p.2.1, p.2.2.2) else 0

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype V] [Fintype W] [Fintype ι]
    [Fintype σ] in
lemma embedReg_apply (v : V) (ψ : QBasis ι σ W → ℂ) (p : QBasis ι σ (V × W)) :
    embedReg v ψ p = if p.2.2.1 = v then ψ (p.1, p.2.1, p.2.2.2) else 0 := rfl

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] in
private lemma blockDiagonal_mulVec_embed
    (fam : V → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (v : V)
    (ψ : QBasis ι σ W → ℂ) :
    Matrix.blockDiagonal fam *ᵥ (fun x : QBasis ι σ W × V => if x.2 = v then ψ x.1 else 0)
      = fun x : QBasis ι σ W × V => if x.2 = v then (fam v *ᵥ ψ) x.1 else 0 := by
  funext x
  obtain ⟨s', u'⟩ := x
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  have hterm : ∀ (s : QBasis ι σ W) (u : V),
      Matrix.blockDiagonal fam (s', u') (s, u) * (if u = v then ψ s else 0)
        = if u = u' then (if u' = v then fam u' s' s * ψ s else 0) else 0 := by
    intro s u
    rw [Matrix.blockDiagonal_apply]
    by_cases h : u' = u
    · subst h
      by_cases h2 : u' = v <;> simp [h2]
    · simp [h, Ne.symm h]
  simp only [hterm]
  rw [show (∑ s : QBasis ι σ W, ∑ u : V,
      (if u = u' then (if u' = v then fam u' s' s * ψ s else 0) else 0))
      = ∑ s : QBasis ι σ W, (if u' = v then fam u' s' s * ψ s else 0) from
    Finset.sum_congr rfl fun s _ => by
      rw [Finset.sum_ite_eq' Finset.univ u' (fun _ => (if u' = v then fam u' s' s * ψ s else 0))]
      simp]
  by_cases h : u' = v
  · subst h
    simp [Matrix.mulVec, dotProduct]
  · simp [h]

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] in
/-- **The action on the encoded subspace.** -/
theorem blockFam_mulVec_embed (fam : V → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (v : V) (ψ : QBasis ι σ W → ℂ) :
    blockFam fam *ᵥ embedReg v ψ = embedReg v (fam v *ᵥ ψ) := by
  classical
  rw [blockFam, Matrix.submatrix_mulVec_equiv]
  have hcomp : embedReg v ψ ∘ (regEquiv (ι := ι) (σ := σ) (V := V) (W := W)).symm
      = fun x : QBasis ι σ W × V => if x.2 = v then ψ x.1 else 0 := by
    funext x
    obtain ⟨⟨k, t, w⟩, u⟩ := x
    rfl
  rw [hcomp, blockDiagonal_mulVec_embed]
  funext p
  rfl

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] in
lemma liftReg_mul (U U' : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    liftReg V U * liftReg V U' = liftReg V (U * U') := by
  classical
  exact blockFam_mul _ _

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] in
lemma liftReg_mulVec_embed (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (v : V)
    (ψ : QBasis ι σ W → ℂ) :
    liftReg V U *ᵥ embedReg v ψ = embedReg v (U *ᵥ ψ) := by
  classical
  exact blockFam_mulVec_embed _ v ψ

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
omit [Fintype V] in
lemma liftReg_conjTranspose (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    (liftReg V U)ᴴ = liftReg V Uᴴ := by
  classical
  exact blockFam_conjTranspose _

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] in
lemma isQProjector_liftReg {P : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hP : IsQProjector P) : IsQProjector (liftReg V P) := by
  classical
  exact ⟨by rw [liftReg_conjTranspose, hP.1], by rw [liftReg_mul, hP.2]⟩

/-! ## The sectors are orthogonal

The embedding is linear and isometric onto its own sector, and distinct register
values give orthogonal sectors.  Everything a superposition over the register
needs — Pythagoras for a packed family, in particular — comes from these. -/

omit [DecidableEq V] [DecidableEq W] [DecidableEq ι] [DecidableEq σ] in
/-- Split a sum over the extended basis as (rest, extra register). -/
lemma sum_reg {M : Type*} [AddCommMonoid M] (F : QBasis ι σ (V × W) → M) :
    ∑ r, F r = ∑ s : QBasis ι σ W, ∑ u : V, F (regEquiv.symm (s, u)) := by
  rw [← Equiv.sum_comp (regEquiv (ι := ι) (σ := σ) (V := V) (W := W)).symm F,
    Fintype.sum_prod_type]

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype V] [Fintype W] [Fintype ι]
    [Fintype σ] in
lemma embedReg_regEquiv_symm (v : V) (ψ : QBasis ι σ W → ℂ)
    (s : QBasis ι σ W) (u : V) :
    embedReg v ψ (regEquiv.symm (s, u)) = if u = v then ψ s else 0 := rfl

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype V] [Fintype W] [Fintype ι]
    [Fintype σ] in
lemma embedReg_smul (v : V) (a : ℂ) (ψ : QBasis ι σ W → ℂ) :
    embedReg v (a • ψ) = a • embedReg v ψ := by
  funext p
  by_cases h : p.2.2.1 = v <;> simp [embedReg_apply, h]

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype V] [Fintype W] [Fintype ι]
    [Fintype σ] in
lemma embedReg_sum {α : Type*} (v : V) (s : Finset α)
    (f : α → (QBasis ι σ W → ℂ)) :
    embedReg v (∑ i ∈ s, f i) = ∑ i ∈ s, embedReg v (f i) := by
  classical
  funext p
  rw [embedReg_apply, Finset.sum_apply, Finset.sum_apply]
  by_cases h : p.2.2.1 = v
  · simp only [ite_eq_left h]
    exact Finset.sum_congr rfl fun i _ => by rw [embedReg_apply, ite_eq_left h]
  · simp [h, embedReg_apply]

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] in
/-- **Distinct register values give orthogonal sectors**, and the embedding
preserves the inner product on its own. -/
theorem qInner_embedReg (v v' : V) (ψ φ : QBasis ι σ W → ℂ) :
    qInner (embedReg v ψ) (embedReg v' φ) = if v = v' then qInner ψ φ else 0 := by
  classical
  rw [qInner_def, sum_reg]
  by_cases h : v = v'
  · subst h
    rw [ite_eq_left rfl, qInner_def]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single v]
    · rw [embedReg_regEquiv_symm, embedReg_regEquiv_symm, ite_eq_left rfl, ite_eq_left rfl]
    · intro u _ hu
      rw [embedReg_regEquiv_symm, ite_eq_right hu, star_zero, zero_mul]
    · simp
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun u _ => ?_
    rw [embedReg_regEquiv_symm, embedReg_regEquiv_symm]
    by_cases hu : u = v'
    · rw [ite_eq_right fun hc => h (hc.symm.trans hu), star_zero, zero_mul]
    · rw [ite_eq_right hu, mul_zero]

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] in
lemma qNormSq_embedReg (v : V) (ψ : QBasis ι σ W → ℂ) :
    qNormSq (embedReg v ψ) = qNormSq ψ := by
  classical
  have h := qInner_embedReg v v ψ ψ
  rw [ite_eq_left rfl, qInner_self, qInner_self] at h
  exact_mod_cast h

/-! ## Operators on the extra register itself

`blockFam` acts on the *workspace*, indexed by the register.  Its transpose —
acting on the **register**, trivially on the workspace — is the other primitive a
clocked construction needs, and it is Mathlib's Kronecker product with the
identity, so again the algebra is inherited rather than re-proved. -/

/-- An operator acting on the **extra register alone**, as the identity
elsewhere. -/
def regOp (A : Matrix V V ℂ) :
    Matrix (QBasis ι σ (V × W)) (QBasis ι σ (V × W)) ℂ :=
  Matrix.kroneckerMap (· * ·) (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) A
    |>.submatrix regEquiv regEquiv

omit [DecidableEq V] in
theorem regOp_mul (A B : Matrix V V ℂ) :
    regOp (ι := ι) (σ := σ) (W := W) A * regOp B = regOp (A * B) := by
  rw [regOp, regOp, regOp, Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, one_mul]

omit [Fintype V] [Fintype W] [Fintype ι] [Fintype σ] in
theorem regOp_one :
    regOp (ι := ι) (σ := σ) (W := W) (1 : Matrix V V ℂ) = 1 := by
  rw [regOp, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

omit [DecidableEq V] [Fintype V] [Fintype W] [Fintype ι] [Fintype σ] in
theorem regOp_conjTranspose (A : Matrix V V ℂ) :
    (regOp (ι := ι) (σ := σ) (W := W) A)ᴴ = regOp Aᴴ := by
  rw [regOp, regOp, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]

omit [DecidableEq V] in
theorem isQProjector_regOp {A : Matrix V V ℂ} (hA : IsQProjector A) :
    IsQProjector (regOp (ι := ι) (σ := σ) (W := W) A) := by
  classical
  exact ⟨by rw [regOp_conjTranspose, hA.1], by rw [regOp_mul, hA.2]⟩

/-- **The action on the encoded subspace**: `A` moves the register, leaving the
workspace vector alone. -/
theorem regOp_mulVec_embedReg (A : Matrix V V ℂ) (v : V) (ψ : QBasis ι σ W → ℂ) :
    regOp A *ᵥ embedReg v ψ = ∑ v' : V, A v' v • embedReg v' ψ := by
  have key : ∀ (s' : QBasis ι σ W) (u : V),
      (Matrix.kroneckerMap (· * ·) (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) A
          *ᵥ (embedReg v ψ ∘ (regEquiv (ι := ι) (σ := σ) (V := V) (W := W)).symm))
          (s', u) = A u v * ψ s' := by
    intro s' u
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    have hterm : ∀ (s : QBasis ι σ W) (u' : V),
        Matrix.kroneckerMap (· * ·) (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) A
            (s', u) (s, u')
          * (embedReg v ψ ∘ (regEquiv (ι := ι) (σ := σ) (V := V) (W := W)).symm) (s, u')
        = if u' = v then (if s = s' then A u v * ψ s else 0) else 0 := by
      intro s u'
      rw [Function.comp_apply, embedReg_regEquiv_symm]
      by_cases h : u' = v
      · subst h
        rw [ite_eq_left rfl, ite_eq_left rfl]
        -- the Kronecker entry, unfolded: `(1 ⊗ₖ A) (s',u) (s,u') = 1 s' s * A u u'`
        change ((1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) s' s * A u u') * ψ s
          = if s = s' then A u u' * ψ s else 0
        rw [Matrix.one_apply]
        by_cases hs : s' = s
        · rw [ite_eq_left hs, ite_eq_left hs.symm, one_mul]
        · rw [ite_eq_right hs, ite_eq_right fun hc => hs hc.symm, zero_mul, zero_mul]
      · rw [ite_eq_right h, ite_eq_right h, mul_zero]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [regOp, Matrix.submatrix_mulVec_equiv]
  funext p
  rw [Function.comp_apply,
    show (regEquiv (ι := ι) (σ := σ) (V := V) (W := W)) p
      = ((p.1, p.2.1, p.2.2.2), p.2.2.1) from rfl, key, Finset.sum_apply,
    Finset.sum_eq_single p.2.2.1]
  · rw [Pi.smul_apply, embedReg_apply, ite_eq_left rfl, smul_eq_mul]
  · intro v' _ hv'
    rw [Pi.smul_apply, embedReg_apply, ite_eq_right fun hc => hv' hc.symm, smul_zero]
  · simp

/-! ## The oracle passes through a workspace extension -/

omit [DecidableEq V] [DecidableEq W] [DecidableEq ι] [Fintype V] [Fintype W] [Fintype ι]
    [Fintype σ] in
/-- The oracle leaves the extra register alone. -/
lemma oracleMap_reg_fst (a : ι → σ) (p : QBasis ι σ (V × W)) :
    (oracleMap a p).2.2.1 = p.2.2.1 := by
  obtain ⟨k, t, v, w⟩ := p
  cases k <;> rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq ι] [Fintype V] [Fintype W] [Fintype ι]
    [Fintype σ] in
/-- The oracle commutes with dropping the extra register. -/
lemma oracleMap_reg_drop (a : ι → σ) (p : QBasis ι σ (V × W)) :
    ((oracleMap a p).1, (oracleMap a p).2.1, (oracleMap a p).2.2.2)
      = oracleMap a (p.1, p.2.1, p.2.2.2) := by
  obtain ⟨k, t, v, w⟩ := p
  cases k <;> rfl

omit [Fintype V] [Fintype W] [Fintype ι] [Fintype σ] in
lemma qBasis_eq_embedReg (r : QBasis ι σ (V × W)) :
    qBasis r = embedReg r.2.2.1 (qBasis (r.1, r.2.1, r.2.2.2)) := by
  classical
  funext p
  obtain ⟨k, t, v, w⟩ := p
  obtain ⟨k', t', v', w'⟩ := r
  simp only [qBasis_apply, embedReg_apply, Prod.mk.injEq]
  by_cases h : v = v'
  · subst h
    by_cases hk : k = k' <;> by_cases ht : t = t' <;> by_cases hw : w = w' <;>
      simp [hk, ht, hw]
  · simp [h]

omit [Fintype W] [Fintype ι] [Fintype σ] in
omit [Fintype V] in
/-- **The oracle ignores the workspace**, so on an extended workspace it is a
constant block family. -/
theorem blockFam_oracle (a : ι → σ) [Finite W] [Finite ι] [Finite σ] [Finite V] :
    oracleMat (W := V × W) a = liftReg V (oracleMat a) := by
  classical
  let := Fintype.ofFinite V
  classical
  let := Fintype.ofFinite W
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  refine matrix_ext_of_mulVec_qBasis fun r => ?_
  rw [oracleMat_mulVec_qBasis, qBasis_eq_embedReg r, liftReg_mulVec_embed,
    oracleMat_mulVec_qBasis, qBasis_eq_embedReg (oracleMap a r), oracleMap_reg_fst,
    oracleMap_reg_drop]

end QuantumQueryComplexity

end SourceQuantumBlocks

section SourceQuantumComplexity

/-!
# Bounded-error quantum query complexity

`qQueryOn read f ε` is the least number of queries with which some algorithm
computes `f` on the promise `read` with error at most `ε`, and
`boundedErrorQQueryOn` fixes the conventional `ε = 1/3`.

Two API shapes matter downstream and they are not symmetric:

* **Upper bounds** (`qQueryOn_le`) are unconditional: exhibiting one algorithm
  bounds the infimum.
* **Lower bounds** (`le_qQueryOn`) need the achievable set to be *nonempty*,
  because `sInf ∅ = 0` in `ℕ`.  The hypothesis is discharged once and for all by
  an exact algorithm for every observationally determined problem; until that is
  in place every lower bound carries `hne` explicitly rather than hiding the
  gap.
-/

namespace QuantumQueryComplexity

variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [DecidableEq O]
variable {X : Type} [Fintype X]

/-- The set of query counts at which `f` is computable with error `≤ ε`.  The
workspace is existentially quantified here — this is the one place where that
costs anything, and it keeps `QAlg` free of a bundled type field. -/
@[expose]
def QueryCounts (read : X → ι → σ) (f : X → O) (ε : ℝ) : Set ℕ :=
  {q | ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
    ComputesWithErrorOn A q read f ε}

/-- **Bounded-error quantum query complexity on a promise.** -/
@[expose]
noncomputable def qQueryOn (read : X → ι → σ) (f : X → O) (ε : ℝ) : ℕ :=
  sInf (QueryCounts read f ε)

/-- The conventional error convention. -/
noncomputable abbrev boundedErrorQQueryOn (read : X → ι → σ) (f : X → O) : ℕ :=
  qQueryOn read f (1 / 3)

/-- Quantum query complexity of a total function. -/
noncomputable abbrev qQuery (f : (ι → σ) → O) (ε : ℝ) : ℕ :=
  qQueryOn (X := ι → σ) id f ε

/-- The conventional error convention, for a total function. -/
noncomputable abbrev boundedErrorQQuery (f : (ι → σ) → O) : ℕ :=
  qQuery f (1 / 3)

/-! ## Upper bounds

Trap: in the existential above the two instance components **must** be supplied
with `inferInstance`.  Writing `⟨W, _, _, A, h⟩` and letting unification solve
them from `A`'s type sends `isDefEq` into a loop (it does not terminate even at
2·10⁶ heartbeats). -/

omit [Fintype X] in
theorem mem_queryCounts {read : X → ι → σ} {f : X → O} {ε : ℝ} {q : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {A : QAlg ι σ O W}
    (h : ComputesWithErrorOn A q read f ε) :
    q ∈ QueryCounts read f ε :=
  ⟨W, inferInstance, inferInstance, A, h⟩

omit [Fintype X] in
/-- **One algorithm bounds the complexity.** -/
theorem qQueryOn_le {read : X → ι → σ} {f : X → O} {ε : ℝ} {q : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {A : QAlg ι σ O W}
    (h : ComputesWithErrorOn A q read f ε) :
    qQueryOn read f ε ≤ q := by
  classical
  exact Nat.sInf_le (mem_queryCounts h)

/-! ## Lower bounds and the optimal witness -/

omit [Fintype X] in
/-- **The infimum is attained**: an optimal algorithm exists as soon as any
algorithm does. -/
theorem exists_computes_qQueryOn {read : X → ι → σ} {f : X → O} {ε : ℝ}
    (hne : (QueryCounts read f ε).Nonempty) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
      ComputesWithErrorOn A (qQueryOn read f ε) read f ε :=
  Nat.sInf_mem hne

omit [Fintype X] in
/-- **A bound valid for every algorithm bounds the complexity from below.** -/
theorem le_qQueryOn {read : X → ι → σ} {f : X → O} {ε : ℝ} {c : ℕ}
    (hne : (QueryCounts read f ε).Nonempty)
    (h : ∀ (q : ℕ) (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
      ComputesWithErrorOn A q read f ε → c ≤ q) :
    c ≤ qQueryOn read f ε := by
  classical
  obtain ⟨W, hW, hW', A, hA⟩ := exists_computes_qQueryOn hne
  exact h _ W hW hW' A hA

omit [Fintype X] in
/-- The real-valued form, which is what the adversary lower bound produces. -/
theorem le_qQueryOn_real {read : X → ι → σ} {f : X → O} {ε : ℝ} {c : ℝ}
    (hne : (QueryCounts read f ε).Nonempty)
    (h : ∀ (q : ℕ) (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
      ComputesWithErrorOn A q read f ε → c ≤ (q : ℝ)) :
    c ≤ (qQueryOn read f ε : ℝ) := by
  classical
  obtain ⟨W, hW, hW', A, hA⟩ := exists_computes_qQueryOn hne
  exact h _ W hW hW' A hA

/-! ## Monotonicity in the error -/

omit [Fintype X] in
theorem queryCounts_mono {read : X → ι → σ} {f : X → O} {ε ε' : ℝ} (hε : ε ≤ ε') :
    QueryCounts read f ε ⊆ QueryCounts read f ε' := by
  classical
  rintro q ⟨W, hW, hW', A, hA⟩
  exact ⟨W, hW, hW', A, hA.mono hε⟩

omit [Fintype X] in
theorem qQueryOn_mono {read : X → ι → σ} {f : X → O} {ε ε' : ℝ} (hε : ε ≤ ε')
    (hne : (QueryCounts read f ε).Nonempty) :
    qQueryOn read f ε' ≤ qQueryOn read f ε := by
  classical
  exact Nat.sInf_le (queryCounts_mono hε (Nat.sInf_mem hne))

/-! ## Restriction to a promise

A promise problem whose output is a function *of the observations* is no
harder than the total problem: run the total algorithm on the promised
observations.  No injectivity and no structure on `read` are needed. -/

omit [Fintype X] in
/-- A total algorithm, run on the promised observations. -/
theorem computesWithErrorOn_comp_read {W : Type} [Fintype W] [DecidableEq W]
    {A : QAlg ι σ O W} {q : ℕ} {f : (ι → σ) → O} {ε : ℝ}
    (h : ComputesWithErrorOn A q (id : (ι → σ) → ι → σ) f ε)
    (read : X → ι → σ) :
    ComputesWithErrorOn A q read (fun x => f (read x)) ε :=
  fun x => h (read x)

omit [Fintype X] in
theorem queryCounts_subset_of_read (read : X → ι → σ) (f : (ι → σ) → O)
    (ε : ℝ) :
    QueryCounts (X := ι → σ) id f ε
      ⊆ QueryCounts read (fun x => f (read x)) ε := by
  classical
  rintro q ⟨W, hW, hW', A, hA⟩
  exact ⟨W, hW, hW', A, computesWithErrorOn_comp_read hA read⟩

omit [Fintype X] in
/-- **The restriction bound**: `Q_ε(f ∘ read on the promise) ≤ Q_ε(f)`.  This
is what turns a promise lower bound into a lower bound on the honest total
function. -/
theorem qQueryOn_comp_read_le_qQuery (read : X → ι → σ) (f : (ι → σ) → O)
    {ε : ℝ} (hne : (QueryCounts (X := ι → σ) id f ε).Nonempty) :
    qQueryOn read (fun x => f (read x)) ε ≤ qQuery f ε := by
  classical
  exact Nat.sInf_le (queryCounts_subset_of_read read f ε (Nat.sInf_mem hne))

/-! ## The constant case -/

omit [Fintype X] in
/-- A constant function has quantum query complexity zero. -/
theorem qQueryOn_const_eq_zero (read : X → ι → σ) {f : X → O} {c : O}
    (hf : ∀ x, f x = c) {ε : ℝ} (hε : 0 ≤ ε) : qQueryOn read f ε = 0 := by
  classical
  exact Nat.le_zero.mp (qQueryOn_le (computesWithErrorOn_const read c hf hε))

end QuantumQueryComplexity

end SourceQuantumComplexity

section SourceQuantumRoutine

/-!
# Query routines: a composable layer above `QAlg`

`QAlg` is a whole algorithm — an initial state, a schedule, and a readout — and
its schedule has an exact length.  Circuit constructions need something smaller
and composable: an **operator** built from queries, which can be sequenced,
inverted, and controlled, and whose query count is tracked exactly.  That is a
`QRoutine`:

  `R.run a = U_len · O_a · U_{len-1} · ⋯ · O_a · U_0`,   exactly `R.len` queries.

A routine carries no initial state and no readout, so it composes; `R.toAlg`
turns one into a `QAlg` at the end, and `toAlg_state` says the algorithm's state
after `R.len` queries is `R.run a` applied to the initial state.  So everything
proved about `QAlg` — in particular the operational lower bound — applies to
whatever the routine layer builds, with no change to the pinned statements.

## Main results

* `run_mem_unitaryGroup` — a routine is a unitary for every input.
* `toAlg_state` — the bridge to `QAlg`.
* `comp_run` — **sequencing**: `(R.comp S).run a = S.run a * R.run a` with
  `(R.comp S).len = R.len + S.len`.  Query counts add exactly; the boundary
  unitaries `S.step 0` and `R.step R.len` are merged into one, which is why no
  query is wasted at the junction.
* `exists_inv` — **inversion**: every routine has an inverse routine of the
  *same* length.  This is where the oracle being an involution pays: `Oᴴ = O`,
  so reversing a schedule costs no extra queries.
* `runUpto_congr` — routines agreeing on steps `0 … len` have the same run,
  which is what lets constructions specify a schedule only where it matters.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ O W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- **A query routine**: `len` oracle calls interleaved with input-independent
unitaries. -/
structure QRoutine (ι σ W : Type) [Fintype ι] [DecidableEq ι] [Fintype σ]
    [DecidableEq σ] [Fintype W] [DecidableEq W] where
  /-- The number of queries. -/
  len : ℕ
  /-- The input-independent unitaries; `step t` is applied after the `t`-th
  query, and `step 0` before the first. -/
  step : ℕ → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ
  /-- Each step is unitary. -/
  step_unitary : ∀ t, step t ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ

/-- The adjoint of a unitary is unitary. -/
lemma conjTranspose_mem_qUnitary {H : Type} [Fintype H] [DecidableEq H]
    {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    Uᴴ ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  have h := Matrix.mem_unitaryGroup_iff.mp hU
  rwa [Matrix.star_eq_conjTranspose] at h

namespace QRoutine

section GeneralOracle

variable (Q : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)

/-- The operator implemented by the first `t` queries of `R`, with the opaque
oracle matrix `Q` in place of the transposition oracle. -/
@[expose]
def runWith (R : QRoutine ι σ W) : ℕ → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ
  | 0 => R.step 0
  | t + 1 => R.step (t + 1) * (Q * R.runWith t)

@[simp] lemma runWith_zero (R : QRoutine ι σ W) : R.runWith Q 0 = R.step 0 := rfl

@[simp] lemma runWith_succ (R : QRoutine ι σ W) (t : ℕ) :
    R.runWith Q (t + 1) = R.step (t + 1) * (Q * R.runWith Q t) := rfl

lemma runWith_mem_unitaryGroup (R : QRoutine ι σ W)
    (hQ : Q ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) (t : ℕ) :
    R.runWith Q t ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ := by
  induction t with
  | zero => exact R.step_unitary 0
  | succ t ih => exact mul_mem (R.step_unitary (t + 1)) (mul_mem hQ ih)

/-- Only the steps up to `t` matter. -/
lemma runWith_congr {R S : QRoutine ι σ W} {t : ℕ}
    (h : ∀ k, k ≤ t → R.step k = S.step k) : R.runWith Q t = S.runWith Q t := by
  induction t with
  | zero => exact h 0 le_rfl
  | succ t ih =>
      rw [runWith_succ, runWith_succ, h (t + 1) le_rfl,
        ih (fun k hk => h k (le_trans hk (Nat.le_succ t)))]

end GeneralOracle

/-- The operator implemented by the first `t` queries of `R`. -/
@[expose]
def runUpto (R : QRoutine ι σ W) (a : ι → σ) :
    ℕ → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ := R.runWith (oracleMat a)


@[simp] lemma runUpto_zero (R : QRoutine ι σ W) (a : ι → σ) :
    R.runUpto a 0 = R.step 0 := rfl

@[simp] lemma runUpto_succ (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ) :
    R.runUpto a (t + 1) = R.step (t + 1) * (oracleMat a * R.runUpto a t) := rfl

/-- **The operator implemented by `R`**, using exactly `R.len` queries. -/
@[expose]
def run (R : QRoutine ι σ W) (a : ι → σ) : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ :=
  R.runUpto a R.len

lemma runUpto_mem_unitaryGroup (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ) :
    R.runUpto a t ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ :=
  R.runWith_mem_unitaryGroup _ (oracleMat_mem_unitaryGroup a) t

lemma run_mem_unitaryGroup (R : QRoutine ι σ W) (a : ι → σ) :
    R.run a ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ :=
  R.runUpto_mem_unitaryGroup a R.len

/-- Only the steps up to `t` matter for the first `t` queries. -/
lemma runUpto_congr {R S : QRoutine ι σ W} (a : ι → σ) {t : ℕ}
    (h : ∀ k, k ≤ t → R.step k = S.step k) : R.runUpto a t = S.runUpto a t := runWith_congr _ h

/-! ## The bridge to `QAlg` -/

/-- Turn a routine into an algorithm by supplying an initial state and a
readout. -/
@[expose]
def toAlg (R : QRoutine ι σ W) (init : QBasis ι σ W → ℂ) (hinit : IsQState init)
    (readout : QBasis ι σ W → O) : QAlg ι σ O W where
  init := init
  init_isQState := hinit
  step := R.step
  step_unitary := R.step_unitary
  readout := readout

/-- **The bridge.**  The algorithm's state after `t` queries is the routine's
operator applied to the initial state. -/
lemma toAlg_state (R : QRoutine ι σ W) (init : QBasis ι σ W → ℂ)
    (hinit : IsQState init) (readout : QBasis ι σ W → O) (a : ι → σ) (t : ℕ) :
    (R.toAlg init hinit readout).state a t = R.runUpto a t *ᵥ init := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [QAlg.state_succ, ih, runUpto_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rfl

lemma toAlg_state_len (R : QRoutine ι σ W) (init : QBasis ι σ W → ℂ)
    (hinit : IsQState init) (readout : QBasis ι σ W → O) (a : ι → σ) :
    (R.toAlg init hinit readout).state a R.len = R.run a *ᵥ init :=
  R.toAlg_state init hinit readout a R.len

/-! ## Sequencing -/

/-- **Sequencing**: run `R`, then `S`.  The two boundary unitaries are merged,
so the query count is exactly `R.len + S.len`. -/
@[expose]
def comp (R S : QRoutine ι σ W) : QRoutine ι σ W where
  len := R.len + S.len
  step := fun t =>
    if t < R.len then R.step t
    else if t = R.len then S.step 0 * R.step R.len
    else S.step (t - R.len)
  step_unitary := by
    intro t
    split_ifs
    · exact R.step_unitary _
    · exact mul_mem (S.step_unitary 0) (R.step_unitary _)
    · exact S.step_unitary _

@[simp] lemma comp_len (R S : QRoutine ι σ W) : (R.comp S).len = R.len + S.len := rfl

lemma comp_step_of_lt (R S : QRoutine ι σ W) {t : ℕ} (h : t < R.len) :
    (R.comp S).step t = R.step t := by
  change (if t < R.len then _ else _) = _
  rw [ite_eq_left h]

lemma comp_step_self (R S : QRoutine ι σ W) :
    (R.comp S).step R.len = S.step 0 * R.step R.len := by
  change (if R.len < R.len then _ else if R.len = R.len then _ else _) = _
  rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]

lemma comp_step_of_gt (R S : QRoutine ι σ W) {t : ℕ} (h : R.len < t) :
    (R.comp S).step t = S.step (t - R.len) := by
  change (if t < R.len then _ else if t = R.len then _ else _) = _
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

section GeneralOracleComposition
variable (Q : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)

/-- The standard semantics is the transposition-oracle instance. -/
lemma runUpto_eq_runWith (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ) :
    R.runUpto a t = R.runWith (oracleMat a) t := rfl

lemma run_eq_runWith (R : QRoutine ι σ W) (a : ι → σ) :
    R.run a = R.runWith (oracleMat a) R.len :=
  runUpto_eq_runWith R a R.len

/-! ## Sequencing, parametrically -/

lemma comp_runWith_of_lt (R S : QRoutine ι σ W) {t : ℕ}
    (ht : t < R.len) : (R.comp S).runWith Q t = R.runWith Q t :=
  runWith_congr Q fun _ hk => comp_step_of_lt R S (lt_of_le_of_lt hk ht)

lemma comp_runWith_len (R S : QRoutine ι σ W) :
    (R.comp S).runWith Q R.len = S.step 0 * R.runWith Q R.len := by
  rcases Nat.eq_zero_or_pos R.len with h0 | hpos
  · calc (R.comp S).runWith Q R.len
        = (R.comp S).step R.len := by rw [h0]; rfl
      _ = S.step 0 * R.step R.len := comp_step_self R S
      _ = S.step 0 * R.runWith Q R.len := by rw [h0]; rfl
  · obtain ⟨m, hm⟩ : ∃ m, R.len = m + 1 := ⟨R.len - 1, by omega⟩
    have hlt : m < R.len := by omega
    calc (R.comp S).runWith Q R.len
        = (R.comp S).step R.len * (Q * (R.comp S).runWith Q m) := by
          rw [hm]
          rfl
      _ = (S.step 0 * R.step R.len) * (Q * R.runWith Q m) := by
          rw [comp_step_self, comp_runWith_of_lt Q R S hlt]
      _ = S.step 0 * (R.step R.len * (Q * R.runWith Q m)) := by
          rw [Matrix.mul_assoc]
      _ = S.step 0 * R.runWith Q R.len := by
          rw [hm]
          rfl

lemma comp_runWith_add (R S : QRoutine ι σ W) (k : ℕ) :
    (R.comp S).runWith Q (R.len + k)
      = S.runWith Q k * R.runWith Q R.len := by
  induction k with
  | zero => simpa using comp_runWith_len Q R S
  | succ k ih =>
      have hgt : R.len < R.len + (k + 1) := by omega
      have hsub : R.len + (k + 1) - R.len = k + 1 := by omega
      calc (R.comp S).runWith Q (R.len + (k + 1))
          = (R.comp S).step (R.len + (k + 1))
              * (Q * (R.comp S).runWith Q (R.len + k)) := by
            rw [show R.len + (k + 1) = (R.len + k) + 1 from by omega]
            rfl
        _ = S.step (k + 1) * (Q * (S.runWith Q k * R.runWith Q R.len)) := by
            rw [comp_step_of_gt R S hgt, hsub, ih]
        _ = (S.step (k + 1) * (Q * S.runWith Q k)) * R.runWith Q R.len := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = S.runWith Q (k + 1) * R.runWith Q R.len := by rw [runWith_succ]

/-- **Sequencing against any oracle**: the mirror of `comp_run`. -/
theorem comp_runWith_full (R S : QRoutine ι σ W) :
    (R.comp S).runWith Q (R.len + S.len)
      = S.runWith Q S.len * R.runWith Q R.len :=
  comp_runWith_add Q R S S.len


end GeneralOracleComposition

lemma comp_runUpto_of_lt (R S : QRoutine ι σ W) (a : ι → σ) {t : ℕ}
    (ht : t < R.len) : (R.comp S).runUpto a t = R.runUpto a t :=
  comp_runWith_of_lt (oracleMat a) R S ht

lemma comp_runUpto_len (R S : QRoutine ι σ W) (a : ι → σ) :
    (R.comp S).runUpto a R.len = S.step 0 * R.runUpto a R.len := comp_runWith_len (oracleMat a) R S

lemma comp_runUpto_add (R S : QRoutine ι σ W) (a : ι → σ) (k : ℕ) :
    (R.comp S).runUpto a (R.len + k) = S.runUpto a k * R.run a :=
  comp_runWith_add (oracleMat a) R S k

/-- **Sequencing, at the level of operators.** -/
theorem comp_run (R S : QRoutine ι σ W) (a : ι → σ) :
    (R.comp S).run a = S.run a * R.run a :=
  comp_runUpto_add R S a S.len

/-! ## Padding by two

Padding by an *even* number of queries is free and needs no extra workspace: the
oracle is an involution, so a query immediately followed by a query is the
identity.  Padding by *one* is a different matter — it needs somewhere to park
the query index so that the extra query idles — and lives in `SourceQuantumControl`. -/

/-- Append two queries that cancel. -/
@[expose]
def padTwo (R : QRoutine ι σ W) : QRoutine ι σ W where
  len := R.len + 2
  step := fun t => if t ≤ R.len then R.step t else 1
  step_unitary := by
    intro t
    split_ifs
    · exact R.step_unitary _
    · exact one_mem_qUnitary

@[simp] lemma padTwo_len (R : QRoutine ι σ W) : R.padTwo.len = R.len + 2 := rfl

/-- **Padding by two changes nothing.** -/
theorem padTwo_run (R : QRoutine ι σ W) (a : ι → σ) : R.padTwo.run a = R.run a := by
  have hbase : R.padTwo.runUpto a R.len = R.runUpto a R.len :=
    runUpto_congr a fun k hk => by
      change (if k ≤ R.len then _ else _) = _
      rw [ite_eq_left hk]
  have h1 : R.padTwo.step (R.len + 1) = 1 := by
    change (if R.len + 1 ≤ R.len then _ else _) = _
    rw [ite_eq_right (by omega)]
  have h2 : R.padTwo.step (R.len + 2) = 1 := by
    change (if R.len + 2 ≤ R.len then _ else _) = _
    rw [ite_eq_right (by omega)]
  calc R.padTwo.run a
      = R.padTwo.step (R.len + 2)
          * (oracleMat a * (R.padTwo.step (R.len + 1)
            * (oracleMat a * R.padTwo.runUpto a R.len))) := rfl
    _ = oracleMat a * (oracleMat a * R.runUpto a R.len) := by
        rw [h1, h2, hbase, Matrix.one_mul, Matrix.one_mul]
    _ = (oracleMat a * oracleMat a) * R.runUpto a R.len := by rw [Matrix.mul_assoc]
    _ = R.run a := by rw [oracleMat_mul_self, Matrix.one_mul]; rfl

/-! ## Inversion

The oracle is an involution with real entries, so it is self-adjoint; reversing
a schedule therefore costs no extra queries.  That is the content of the
`Oᴴ = O` step below, and it is the reason the value oracle was chosen to be a
transposition in the first place. -/

omit [Fintype W] [Fintype ι] [Fintype σ] in
lemma oracleMat_conjTranspose (a : ι → σ) [Finite W] [Finite ι] [Finite σ] :
    (oracleMat (W := W) a)ᴴ = oracleMat a := by
  classical
  let := Fintype.ofFinite W
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  have h1 : (oracleMat (W := W) a)ᴴ * oracleMat a = 1 :=
    conjTranspose_mul_self_of_unitary (oracleMat_mem_unitaryGroup a)
  have h2 : oracleMat (W := W) a * oracleMat a = 1 := oracleMat_mul_self a
  calc (oracleMat (W := W) a)ᴴ
      = (oracleMat a)ᴴ * 1 := by rw [Matrix.mul_one]
    _ = (oracleMat a)ᴴ * (oracleMat a * oracleMat a) := by rw [h2]
    _ = ((oracleMat a)ᴴ * oracleMat a) * oracleMat a := by rw [Matrix.mul_assoc]
    _ = oracleMat a := by rw [h1, Matrix.one_mul]

/-- A single-query routine, used to peel the last query off a schedule. -/
private def lastQuery (U V : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) : QRoutine ι σ W where
  len := 1
  step := fun t => if t = 0 then V else U
  step_unitary := by
    intro t
    split_ifs
    · exact hV
    · exact hU

private lemma lastQuery_run (U V) (hU) (hV) (a : ι → σ) :
    (lastQuery (W := W) U V hU hV).run a = U * (oracleMat a * V) := rfl

/-- **Inversion.**  Every routine has an inverse routine of the same length. -/
theorem exists_inv (R : QRoutine ι σ W) :
    ∃ R' : QRoutine ι σ W, R'.len = R.len ∧ ∀ a, R'.run a = (R.run a)ᴴ := by
  obtain ⟨n, hn⟩ : ∃ n, R.len = n := ⟨R.len, rfl⟩
  induction n generalizing R with
  | zero =>
      refine ⟨⟨0, fun _ => (R.step 0)ᴴ, fun _ => ?_⟩, hn.symm, fun a => ?_⟩
      · exact conjTranspose_mem_qUnitary (R.step_unitary 0)
      · rw [run, run, hn]
        rfl
  | succ m ih =>
      -- peel the last query: `R = P` then one query and `R.step (m+1)`
      let P : QRoutine ι σ W := ⟨m, R.step, R.step_unitary⟩
      let Q : QRoutine ι σ W :=
        lastQuery (R.step (m + 1)) 1 (R.step_unitary (m + 1)) one_mem_qUnitary
      have hP : ∀ a : ι → σ, P.run a = R.runUpto a m :=
        fun a => runUpto_congr a fun _ _ => rfl
      have hPQ : ∀ a, R.run a = Q.run a * P.run a := by
        intro a
        rw [hP, lastQuery_run, run, hn, runUpto_succ, Matrix.mul_one,
          Matrix.mul_assoc]
      obtain ⟨P', hP'len, hP'⟩ := ih P rfl
      -- the inverse of one query is one query
      let Q' : QRoutine ι σ W :=
        lastQuery 1 (R.step (m + 1))ᴴ one_mem_qUnitary
          (conjTranspose_mem_qUnitary (R.step_unitary (m + 1)))
      have hQ' : ∀ a, Q'.run a = (Q.run a)ᴴ := by
        intro a
        rw [lastQuery_run, lastQuery_run, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul, Matrix.conjTranspose_one, oracleMat_conjTranspose,
          Matrix.one_mul, Matrix.one_mul]
      refine ⟨Q'.comp P', ?_, fun a => ?_⟩
      · have hPm : P'.len = m := hP'len
        change 1 + P'.len = R.len
        rw [hPm, hn]
        omega
      · rw [comp_run, hP', hQ', hPQ a, Matrix.conjTranspose_mul]

/-! ## Zero-query constructors, and an explicit inverse -/

/-- A zero-query routine: just a unitary. -/
@[expose]
def ofUnitary (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) : QRoutine ι σ W where
  len := 0
  step := fun _ => U
  step_unitary := fun _ => hU

@[simp] lemma ofUnitary_len (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) : (ofUnitary U hU).len = 0 := rfl

@[simp] lemma ofUnitary_run (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) (a : ι → σ) :
    (ofUnitary U hU).run a = U := rfl

lemma ofUnitary_runWith (Q : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) :
    (ofUnitary U hU).runWith Q 0 = U := rfl

/-- The zero-query identity routine. -/
@[expose]
def identity : QRoutine ι σ W := ofUnitary 1 one_mem_qUnitary

@[simp] lemma identity_len : (identity : QRoutine ι σ W).len = 0 := rfl

@[simp] lemma identity_run (a : ι → σ) :
    (identity : QRoutine ι σ W).run a = 1 := rfl

/-- **The one-query routine**: a single bare oracle call. -/
@[expose]
def query : QRoutine ι σ W where
  len := 1
  step := fun _ => 1
  step_unitary := fun _ => one_mem_qUnitary

@[simp] lemma query_len : (query : QRoutine ι σ W).len = 1 := rfl

@[simp] lemma query_run (a : ι → σ) :
    (query : QRoutine ι σ W).run a = oracleMat a := by
  change (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) * (oracleMat a * 1) = oracleMat a
  rw [Matrix.one_mul, Matrix.mul_one]

/-- **An explicit inverse routine**, chosen once from `exists_inv`. -/
noncomputable def inv (R : QRoutine ι σ W) : QRoutine ι σ W := R.exists_inv.choose

@[simp] lemma inv_len (R : QRoutine ι σ W) : R.inv.len = R.len :=
  R.exists_inv.choose_spec.1

@[simp] lemma inv_run (R : QRoutine ι σ W) (a : ι → σ) :
    R.inv.run a = (R.run a)ᴴ := R.exists_inv.choose_spec.2 a

/-! ## Conjugation and iteration -/

/-- **Conjugate a fixed unitary by a routine**: run `R`, apply `U`, run `R`
backwards.  Costs `2 · R.len` queries — no more, because inversion is free. -/
noncomputable def conjFixed (R : QRoutine ι σ W)
    (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) : QRoutine ι σ W :=
  (R.comp (ofUnitary U hU)).comp R.inv

@[simp] lemma conjFixed_len (R : QRoutine ι σ W)
    (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) :
    (R.conjFixed U hU).len = 2 * R.len := by
  change R.len + 0 + R.inv.len = 2 * R.len
  rw [inv_len]
  omega

theorem conjFixed_run (R : QRoutine ι σ W)
    (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) (a : ι → σ) :
    (R.conjFixed U hU).run a = (R.run a)ᴴ * (U * R.run a) := by
  rw [conjFixed, comp_run, comp_run, ofUnitary_run, inv_run]

/-- **Run `R` `n` times in sequence.** -/
def iterate (R : QRoutine ι σ W) : ℕ → QRoutine ι σ W
  | 0 => identity
  | n + 1 => (R.iterate n).comp R

@[simp] lemma iterate_len (R : QRoutine ι σ W) (n : ℕ) :
    (R.iterate n).len = n * R.len := by
  induction n with
  | zero =>
      change (0 : ℕ) = 0 * R.len
      omega
  | succ n ih =>
      change (R.iterate n).len + R.len = (n + 1) * R.len
      rw [ih]
      ring

theorem iterate_run (R : QRoutine ι σ W) (a : ι → σ) (n : ℕ) :
    (R.iterate n).run a = (R.run a) ^ n := by
  induction n with
  | zero =>
      change (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) = (R.run a) ^ 0
      rw [pow_zero]
  | succ n ih =>
      change ((R.iterate n).comp R).run a = _
      rw [comp_run, ih, pow_succ']

end QRoutine

section
variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [DecidableEq O]

omit [DecidableEq O] in
/-- The same bridge read backwards: an algorithm's state is the run of the
routine formed from its own steps. -/
lemma state_eq_runUpto2 {W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ O W) (n : ℕ) (a : ι → σ) (t : ℕ) :
    A.state a t
      = (QRoutine.mk n A.step A.step_unitary).runUpto a t *ᵥ A.init := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [QAlg.state_succ, ih, QRoutine.runUpto_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]

end

end QuantumQueryComplexity

end SourceQuantumRoutine

section SourceQuantumControl

/-!
# The controlled query, and idling

The value oracle has an **idle index** `none`, and `SourceQuantumOracle` records that it
does nothing there.  That is only half of what a circuit needs: to *use* the
idle sector one must be able to move the query index into it and back, and
"assign `none` to the index register" is not injective, hence not unitary.

The fix is the same one `SourceQuantumReadAll` used for copying: **swap, don't assign**.
Extend the workspace with a control bit and a parking slot,

  `CtrlWork ι W = Bool × Option ι × W`,

and let `parkMat` swap the index register with the parking slot exactly when the
control bit is `false`.  Then

  `ctrlQuery a = parkMat · O_a · parkMat`

contains **exactly one** oracle factor and satisfies

* `ctrlQuery_qBasis_true`  — on control `true` it *is* the query;
* `ctrlQuery_qBasis_false` — on control `false` with a blank slot it is the
  identity: the physical query is spent on the idle index.

So one physical query implements the controlled logical query, which is what
phase detection will need, and what makes an idle query available for padding a
schedule by one (`padOne`; padding by two needs no workspace at all, see
`QRoutine.padTwo`).

`IsParked` names the sector this all happens in — control `false`, slot blank —
and `ctrlQuery_mulVec_of_parked` upgrades the basis-state statement to states
supported there, which is the form a padding argument consumes.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- The workspace of a controlled routine: a control bit, a parking slot for the
query index, and the original workspace. -/
abbrev CtrlWork (ι W : Type) : Type := Bool × Option ι × W

instance instCtrlWorkDecidableEq {ι W : Type} [DecidableEq ι] [DecidableEq W] :
    DecidableEq (CtrlWork ι W) :=
  inferInstanceAs (DecidableEq (Bool × Option ι × W))

instance instCtrlWorkFintype {ι W : Type} [Fintype ι] [Fintype W] :
    Fintype (CtrlWork ι W) :=
  inferInstanceAs (Fintype (Bool × Option ι × W))

/-! ## Parking -/

/-- Swap the query-index register with the parking slot, unless the control bit
says otherwise. -/
@[expose]
def parkMap : QBasis ι σ (CtrlWork ι W) → QBasis ι σ (CtrlWork ι W)
  | (k, t, (true, s, w)) => (k, t, (true, s, w))
  | (k, t, (false, s, w)) => (s, t, (false, k, w))

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
@[simp] lemma parkMap_true (k : Option ι) (t : Option σ) (s : Option ι) (w : W) :
    parkMap ((k, t, (true, s, w)) : QBasis ι σ (CtrlWork ι W))
      = (k, t, (true, s, w)) := rfl

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
@[simp] lemma parkMap_false (k : Option ι) (t : Option σ) (s : Option ι) (w : W) :
    parkMap ((k, t, (false, s, w)) : QBasis ι σ (CtrlWork ι W))
      = (s, t, (false, k, w)) := rfl

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
lemma parkMap_involutive :
    Function.Involutive (parkMap (ι := ι) (σ := σ) (W := W)) := by
  rintro ⟨k, t, b, s, w⟩
  cases b <;> rfl

/-- Parking, as a permutation of the basis. -/
def parkPerm : Equiv.Perm (QBasis ι σ (CtrlWork ι W)) :=
  Function.Involutive.toPerm _ parkMap_involutive

/-- Parking, as a unitary. -/
def parkMat : Matrix (QBasis ι σ (CtrlWork ι W)) (QBasis ι σ (CtrlWork ι W)) ℂ :=
  qPerm parkPerm

lemma parkMat_mem_unitaryGroup :
    parkMat (ι := ι) (σ := σ) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι σ (CtrlWork ι W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma parkMat_mulVec_apply (ψ : QBasis ι σ (CtrlWork ι W) → ℂ)
    (p : QBasis ι σ (CtrlWork ι W)) : (parkMat *ᵥ ψ) p = ψ (parkMap p) := by
  rw [parkMat, qPerm_mulVec_apply]
  rfl

/-! ## The controlled query -/

/-- **The controlled query**: park, query, unpark.  Note the single `oracleMat`
factor — this costs exactly one physical query. -/
@[expose]
def ctrlQuery (a : ι → σ) :
    Matrix (QBasis ι σ (CtrlWork ι W)) (QBasis ι σ (CtrlWork ι W)) ℂ :=
  parkMat * (oracleMat a * parkMat)

lemma ctrlQuery_mem_unitaryGroup (a : ι → σ) :
    ctrlQuery (W := W) a ∈ Matrix.unitaryGroup (QBasis ι σ (CtrlWork ι W)) ℂ :=
  mul_mem parkMat_mem_unitaryGroup
    (mul_mem (oracleMat_mem_unitaryGroup a) parkMat_mem_unitaryGroup)

/-- The basis action of the controlled query. -/
@[expose]
def ctrlMap (a : ι → σ) :
    QBasis ι σ (CtrlWork ι W) → QBasis ι σ (CtrlWork ι W) :=
  fun p => parkMap (oracleMap a (parkMap p))

lemma ctrlQuery_mulVec_apply (a : ι → σ) (ψ : QBasis ι σ (CtrlWork ι W) → ℂ)
    (p : QBasis ι σ (CtrlWork ι W)) :
    (ctrlQuery a *ᵥ ψ) p = ψ (ctrlMap a p) := by
  rw [ctrlQuery, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    parkMat_mulVec_apply, oracleMat_mulVec_apply, parkMat_mulVec_apply]
  rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] [Fintype σ] in
lemma ctrlMap_involutive (a : ι → σ) :
    Function.Involutive (ctrlMap (σ := σ) (W := W) a) := by
  classical
  intro p
  change parkMap (oracleMap a (parkMap (parkMap (oracleMap a (parkMap p))))) = p
  rw [parkMap_involutive, oracleMap_involutive, parkMap_involutive]

lemma ctrlQuery_mulVec_qBasis (a : ι → σ) (r : QBasis ι σ (CtrlWork ι W)) :
    ctrlQuery a *ᵥ qBasis r = qBasis (ctrlMap a r) := by
  funext p
  rw [ctrlQuery_mulVec_apply, qBasis_apply, qBasis_apply]
  by_cases h : ctrlMap a p = r
  · rw [ite_eq_left h, ite_eq_left (by rw [← h, ctrlMap_involutive a p])]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (by rw [hc, ctrlMap_involutive a r]))]

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] [Fintype σ] in
lemma ctrlMap_true (a : ι → σ) (k : Option ι) (t : Option σ) (s : Option ι)
    (w : W) :
    ctrlMap a ((k, t, (true, s, w)) : QBasis ι σ (CtrlWork ι W))
      = oracleMap a (k, t, (true, s, w)) := by
  cases k <;> rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] [Fintype σ] in
lemma ctrlMap_false_blank (a : ι → σ) (k : Option ι) (t : Option σ) (w : W) :
    ctrlMap a ((k, t, (false, none, w)) : QBasis ι σ (CtrlWork ι W))
      = (k, t, (false, none, w)) := rfl

/-- **On the control-true sector the controlled query is the query.** -/
theorem ctrlQuery_qBasis_true (a : ι → σ) (k : Option ι) (t : Option σ)
    (s : Option ι) (w : W) :
    ctrlQuery a *ᵥ qBasis ((k, t, (true, s, w)) : QBasis ι σ (CtrlWork ι W))
      = oracleMat a *ᵥ qBasis (k, t, (true, s, w)) := by
  rw [ctrlQuery_mulVec_qBasis, oracleMat_mulVec_qBasis, ctrlMap_true]

/-- **On the control-false sector with a blank slot the controlled query is the
identity**: the physical query is spent on the idle index. -/
theorem ctrlQuery_qBasis_false (a : ι → σ) (k : Option ι) (t : Option σ) (w : W) :
    ctrlQuery a *ᵥ qBasis ((k, t, (false, none, w)) : QBasis ι σ (CtrlWork ι W))
      = qBasis (k, t, (false, none, w)) := by
  rw [ctrlQuery_mulVec_qBasis, ctrlMap_false_blank]

/-! ## The parked sector -/

/-- A state is **parked** if it lives where the control bit is `false` and the
parking slot is blank — the sector on which a query idles. -/
def IsParked (ψ : QBasis ι σ (CtrlWork ι W) → ℂ) : Prop :=
  ∀ p, ψ p ≠ 0 → p.2.2.1 = false ∧ p.2.2.2.1 = none

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] [Fintype σ] in
lemma ctrlMap_eq_self {a : ι → σ} {p : QBasis ι σ (CtrlWork ι W)}
    (h1 : p.2.2.1 = false) (h2 : p.2.2.2.1 = none) : ctrlMap a p = p := by
  obtain ⟨k, t, b, s, w⟩ := p
  simp only at h1 h2
  subst h1
  subst h2
  rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] [Fintype σ] in
lemma ctrlMap_not_parked {a : ι → σ} {p : QBasis ι σ (CtrlWork ι W)}
    (h : ¬ (p.2.2.1 = false ∧ p.2.2.2.1 = none)) :
    ¬ ((ctrlMap a p).2.2.1 = false ∧ (ctrlMap a p).2.2.2.1 = none) := by
  classical
  intro hc
  apply h
  have hfix : ctrlMap a (ctrlMap a p) = ctrlMap a p := ctrlMap_eq_self hc.1 hc.2
  rw [ctrlMap_involutive a p] at hfix
  rw [hfix]
  exact hc

/-- **A parked state does not notice a query.**  This is the form a padding
argument consumes. -/
theorem ctrlQuery_mulVec_of_parked (a : ι → σ)
    {ψ : QBasis ι σ (CtrlWork ι W) → ℂ} (hψ : IsParked ψ) :
    ctrlQuery a *ᵥ ψ = ψ := by
  funext p
  rw [ctrlQuery_mulVec_apply]
  by_cases hp : p.2.2.1 = false ∧ p.2.2.2.1 = none
  · rw [ctrlMap_eq_self hp.1 hp.2]
  · have h1 : ψ p = 0 := by
      by_contra h
      exact hp (hψ p h)
    have h2 : ψ (ctrlMap a p) = 0 := by
      by_contra h
      exact ctrlMap_not_parked hp (hψ _ h)
    rw [h1, h2]

/-! ## Idling and padding by one -/

/-- The controlled query as a **one-query routine**. -/
@[expose]
def ctrlQueryRoutine : QRoutine ι σ (CtrlWork ι W) where
  len := 1
  step := fun _ => parkMat
  step_unitary := fun _ => parkMat_mem_unitaryGroup

@[simp] lemma ctrlQueryRoutine_len :
    (ctrlQueryRoutine (ι := ι) (σ := σ) (W := W)).len = 1 := rfl

lemma ctrlQueryRoutine_run (a : ι → σ) :
    (ctrlQueryRoutine (ι := ι) (σ := σ) (W := W)).run a = ctrlQuery a := rfl

/-- **Padding by one query.** -/
@[expose]
def padOne (R : QRoutine ι σ (CtrlWork ι W)) : QRoutine ι σ (CtrlWork ι W) :=
  R.comp ctrlQueryRoutine

@[simp] lemma padOne_len (R : QRoutine ι σ (CtrlWork ι W)) :
    (padOne R).len = R.len + 1 := rfl

lemma padOne_run (R : QRoutine ι σ (CtrlWork ι W)) (a : ι → σ) :
    (padOne R).run a = ctrlQuery a * R.run a := by
  rw [padOne, QRoutine.comp_run, ctrlQueryRoutine_run]

/-- **Padding by one is free on the parked sector.** -/
theorem padOne_run_mulVec (R : QRoutine ι σ (CtrlWork ι W)) (a : ι → σ)
    (ψ : QBasis ι σ (CtrlWork ι W) → ℂ) (h : IsParked (R.run a *ᵥ ψ)) :
    (padOne R).run a *ᵥ ψ = R.run a *ᵥ ψ := by
  rw [padOne_run, ← Matrix.mulVec_mulVec, ctrlQuery_mulVec_of_parked a h]

/-! ## Controlled execution of a whole routine

A fixed step is controlled by lifting it to the parked workspace and
conditioning on the control bit — both instances of `blockFam`.  A query is
controlled by `ctrlQuery`.  Neither adds a query, so `control_len` is an
equality.

The statements are about the **encoded subspace** `embedCtrl b ψ` — control bit
`b`, parking slot blank — and not global matrix identities, which would be
false: off that subspace `ctrlQuery` swaps a parked index back in and queries
it. -/

/-- The blank-slot embedding: `ψ` in the sector with control bit `b` and an
empty parking slot. -/
@[expose]
def embedCtrl (b : Bool) (ψ : QBasis ι σ W → ℂ) : QBasis ι σ (CtrlWork ι W) → ℂ :=
  embedReg b (embedReg none ψ)

omit [DecidableEq W] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
lemma embedCtrl_apply (b : Bool) (ψ : QBasis ι σ W → ℂ)
    (p : QBasis ι σ (CtrlWork ι W)) :
    embedCtrl b ψ p =
      if p.2.2.1 = b ∧ p.2.2.2.1 = none then ψ (p.1, p.2.1, p.2.2.2.2) else 0 := by
  classical
  rw [embedCtrl, embedReg_apply, embedReg_apply]
  by_cases h1 : p.2.2.1 = b <;> by_cases h2 : p.2.2.2.1 = none <;> simp [h1, h2]

omit [DecidableEq W] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
lemma isParked_embedCtrl_false (ψ : QBasis ι σ W → ℂ) :
    IsParked (embedCtrl false ψ) := by
  classical
  intro p hp
  by_contra h
  exact hp (by rw [embedCtrl_apply, ite_eq_right h])

/-- A fixed step, lifted to the parked workspace and conditioned on the control
bit. -/
def ctrlStep (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    Matrix (QBasis ι σ (CtrlWork ι W)) (QBasis ι σ (CtrlWork ι W)) ℂ :=
  blockFam (fun b : Bool => bif b then liftReg (Option ι) U else 1)

lemma ctrlStep_mem_unitaryGroup {U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) :
    ctrlStep U ∈ Matrix.unitaryGroup (QBasis ι σ (CtrlWork ι W)) ℂ := by
  refine blockFam_mem_unitaryGroup fun b => ?_
  cases b
  · exact one_mem_qUnitary
  · exact liftReg_mem_unitaryGroup hU

lemma ctrlStep_mulVec_embed_true (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (ψ : QBasis ι σ W → ℂ) :
    ctrlStep U *ᵥ embedCtrl true ψ = embedCtrl true (U *ᵥ ψ) := by
  rw [ctrlStep, embedCtrl, blockFam_mulVec_embed]
  change embedReg true (liftReg (Option ι) U *ᵥ embedReg none ψ) = _
  rw [liftReg_mulVec_embed]
  rfl

lemma ctrlStep_mulVec_embed_false (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (ψ : QBasis ι σ W → ℂ) :
    ctrlStep U *ᵥ embedCtrl false ψ = embedCtrl false ψ := by
  rw [ctrlStep, embedCtrl, blockFam_mulVec_embed]
  change embedReg false ((1 : Matrix (QBasis ι σ (Option ι × W))
    (QBasis ι σ (Option ι × W)) ℂ) *ᵥ embedReg none ψ) = _
  rw [Matrix.one_mulVec]

lemma parkMat_mulVec_embed_true (ψ : QBasis ι σ W → ℂ) :
    parkMat *ᵥ embedCtrl true ψ = embedCtrl true ψ := by
  funext p
  rw [parkMat_mulVec_apply]
  obtain ⟨k, t, b, s, w⟩ := p
  cases b
  · rw [parkMap_false, embedCtrl_apply, embedCtrl_apply]
    simp
  · rw [parkMap_true]

lemma oracleMat_mulVec_embedCtrl (a : ι → σ) (b : Bool) (ψ : QBasis ι σ W → ℂ) :
    oracleMat a *ᵥ embedCtrl b ψ = embedCtrl b (oracleMat a *ᵥ ψ) := by
  rw [embedCtrl, blockFam_oracle (V := Bool), liftReg_mulVec_embed,
    blockFam_oracle (V := Option ι), liftReg_mulVec_embed]
  rfl

lemma ctrlQuery_mulVec_embed_true (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    ctrlQuery a *ᵥ embedCtrl true ψ = embedCtrl true (oracleMat a *ᵥ ψ) := by
  rw [ctrlQuery, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    parkMat_mulVec_embed_true, oracleMat_mulVec_embedCtrl,
    parkMat_mulVec_embed_true]

lemma ctrlQuery_mulVec_embed_false (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    ctrlQuery a *ᵥ embedCtrl false ψ = embedCtrl false ψ :=
  ctrlQuery_mulVec_of_parked a (isParked_embedCtrl_false ψ)

/-- The controlled routine, built one query at a time. -/
def controlUpto (R : QRoutine ι σ W) : ℕ → QRoutine ι σ (CtrlWork ι W)
  | 0 => QRoutine.ofUnitary (ctrlStep (R.step 0))
      (ctrlStep_mem_unitaryGroup (R.step_unitary 0))
  | t + 1 => (controlUpto R t).comp
      (ctrlQueryRoutine.comp (QRoutine.ofUnitary (ctrlStep (R.step (t + 1)))
        (ctrlStep_mem_unitaryGroup (R.step_unitary (t + 1)))))

/-- **Controlled execution** of a routine. -/
def QRoutine.control (R : QRoutine ι σ W) : QRoutine ι σ (CtrlWork ι W) :=
  controlUpto R R.len

lemma controlUpto_len (R : QRoutine ι σ W) (t : ℕ) : (controlUpto R t).len = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change (controlUpto R t).len + (1 + 0) = t + 1
      rw [ih]

/-- **Controlling a routine costs no extra queries.** -/
theorem control_len (R : QRoutine ι σ W) : R.control.len = R.len :=
  controlUpto_len R R.len

lemma controlUpto_run_true (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ)
    (ψ : QBasis ι σ W → ℂ) :
    (controlUpto R t).run a *ᵥ embedCtrl true ψ
      = embedCtrl true (R.runUpto a t *ᵥ ψ) := by
  induction t with
  | zero =>
      change ctrlStep (R.step 0) *ᵥ embedCtrl true ψ = _
      rw [ctrlStep_mulVec_embed_true]
      rfl
  | succ t ih =>
      change ((controlUpto R t).comp _).run a *ᵥ embedCtrl true ψ = _
      rw [QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run,
        ctrlQueryRoutine_run, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        ctrlQuery_mulVec_embed_true, ctrlStep_mulVec_embed_true,
        QRoutine.runUpto_succ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]

lemma controlUpto_run_false (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ)
    (ψ : QBasis ι σ W → ℂ) :
    (controlUpto R t).run a *ᵥ embedCtrl false ψ = embedCtrl false ψ := by
  induction t with
  | zero =>
      change ctrlStep (R.step 0) *ᵥ embedCtrl false ψ = _
      rw [ctrlStep_mulVec_embed_false]
  | succ t ih =>
      change ((controlUpto R t).comp _).run a *ᵥ embedCtrl false ψ = _
      rw [QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run,
        ctrlQueryRoutine_run, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        ctrlQuery_mulVec_embed_false, ctrlStep_mulVec_embed_false]

/-- **On the control-true sector the controlled routine runs.** -/
theorem control_run_true (R : QRoutine ι σ W) (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    R.control.run a *ᵥ embedCtrl true ψ = embedCtrl true (R.run a *ᵥ ψ) :=
  controlUpto_run_true R a R.len ψ

/-- **On the control-false sector it does nothing** — and still spends exactly
`R.len` physical queries. -/
theorem control_run_false (R : QRoutine ι σ W) (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    R.control.run a *ᵥ embedCtrl false ψ = embedCtrl false ψ :=
  controlUpto_run_false R a R.len ψ

end QuantumQueryComplexity

end SourceQuantumControl

section SourceQuantumKronLift

/-!
# Lifting an operator along a factorizing equivalence

The generic tool of the independent-run compiler.  A basis equivalence
`e : β ≃ γ × δ` splits a space into a system and an environment;
`kronLift e M` is `M ⊗ 1` read through `e`, so its algebra is inherited from
Mathlib's Kronecker product exactly as `blockFam`'s came from
`blockDiagonal`.  The two working lemmas:

* `kronLift_mulVec_splitVec` — on a **split state**
  `splitVec e φ ξ = φ((e·).1)·ξ((e·).2)` the lift acts on the system factor
  alone;
* `kronLiftRoutine_runUpto_splitVec` — a routine's steps lifted along an
  **oracle-compatible** equivalence (one that carries the global query
  registers into the system factor: `e (oracleMap a p)
  = (oracleMap a (e p).1, (e p).2)`) run, against the real oracle, as the
  original routine on the system factor.  The compatibility is stated at the
  *map* level, so no matrix identity for the oracle is ever needed.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

section Generic

variable {β γ δ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
  [Fintype δ] [DecidableEq δ]

/-- `M ⊗ 1`, read through the factorizing equivalence `e`. -/
@[expose]
def kronLift (e : β ≃ γ × δ) (M : Matrix γ γ ℂ) : Matrix β β ℂ :=
  (Matrix.kroneckerMap (· * ·) M (1 : Matrix δ δ ℂ)).submatrix e e

omit [DecidableEq β] [DecidableEq γ] [Fintype δ] in
lemma kronLift_mul (e : β ≃ γ × δ) (M N : Matrix γ γ ℂ) [Finite δ] :
    kronLift e M * kronLift e N = kronLift e (M * N) := by
  classical
  let := Fintype.ofFinite δ
  rw [kronLift, kronLift, kronLift, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul, one_mul]

omit [Fintype β] [Fintype γ] [Fintype δ] in
lemma kronLift_one (e : β ≃ γ × δ) :
    kronLift e (1 : Matrix γ γ ℂ) = 1 := by
  rw [kronLift, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

omit [DecidableEq β] [DecidableEq γ] [Fintype β] [Fintype γ] [Fintype δ] in
lemma kronLift_conjTranspose (e : β ≃ γ × δ) (M : Matrix γ γ ℂ) :
    (kronLift e M)ᴴ = kronLift e Mᴴ := by
  rw [kronLift, kronLift, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

omit [Fintype δ] in
lemma kronLift_mem_unitaryGroup (e : β ≃ γ × δ) {M : Matrix γ γ ℂ}
    (hM : M ∈ Matrix.unitaryGroup γ ℂ) [Finite δ] :
    kronLift e M ∈ Matrix.unitaryGroup β ℂ := by
  classical
  let := Fintype.ofFinite δ
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    kronLift_conjTranspose, kronLift_mul,
    conjTranspose_mul_self_of_unitary hM, kronLift_one]

/-- A state of split form: `φ` on the system factor, `ξ` on the
environment. -/
@[expose]
def splitVec (e : β ≃ γ × δ) (φ : γ → ℂ) (ξ : δ → ℂ) : β → ℂ :=
  fun b => φ (e b).1 * ξ (e b).2

omit [DecidableEq β] [DecidableEq γ] [DecidableEq δ] [Fintype β] [Fintype γ] [Fintype δ] in
@[simp] lemma splitVec_apply (e : β ≃ γ × δ) (φ : γ → ℂ) (ξ : δ → ℂ)
    (b : β) : splitVec e φ ξ b = φ (e b).1 * ξ (e b).2 := rfl

omit [DecidableEq β] [DecidableEq γ] [Fintype δ] in
/-- **The lift acts on the system factor of a split state.** -/
theorem kronLift_mulVec_splitVec (e : β ≃ γ × δ) (M : Matrix γ γ ℂ)
    (φ : γ → ℂ) (ξ : δ → ℂ) [Finite δ] :
    kronLift e M *ᵥ splitVec e φ ξ = splitVec e (M *ᵥ φ) ξ := by
  classical
  let := Fintype.ofFinite δ
  funext b
  rw [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp e.symm
    (fun b' => kronLift e M b b' * splitVec e φ ξ b')]
  rw [Fintype.sum_prod_type]
  have hterm : ∀ (c : γ) (d : δ),
      kronLift e M b (e.symm (c, d)) * splitVec e φ ξ (e.symm (c, d))
        = (M (e b).1 c * φ c) * (if (e b).2 = d then ξ d else 0) := by
    intro c d
    rw [kronLift, Matrix.submatrix_apply, Equiv.apply_symm_apply,
      Matrix.kroneckerMap_apply, splitVec_apply, Equiv.apply_symm_apply]
    rw [Matrix.one_apply]
    by_cases h : (e b).2 = d
    · rw [ite_eq_left h, ite_eq_left h]
      ring
    · rw [ite_eq_right h, ite_eq_right h]
      ring
  simp only [hterm]
  have hinner : ∀ c : γ,
      (∑ d, (M (e b).1 c * φ c) * (if (e b).2 = d then ξ d else 0))
        = (M (e b).1 c * φ c) * ξ (e b).2 := by
    intro c
    rw [← Finset.mul_sum,
      Finset.sum_ite_eq Finset.univ (e b).2 ξ, ite_eq_left (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl fun c _ => hinner c, splitVec_apply,
    ← Finset.sum_mul]
  congr 1

omit [DecidableEq β] [DecidableEq γ] [DecidableEq δ] in
/-- The squared norm of a split state is the product of the factors'. -/
lemma qNormSq_splitVec (e : β ≃ γ × δ) (φ : γ → ℂ) (ξ : δ → ℂ) :
    qNormSq (splitVec e φ ξ) = qNormSq φ * qNormSq ξ := by
  classical
  rw [qNormSq_def, ← Equiv.sum_comp e.symm
    (fun b => Complex.normSq (splitVec e φ ξ b)), Fintype.sum_prod_type]
  rw [qNormSq_def, qNormSq_def, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [splitVec_apply, Equiv.apply_symm_apply, Complex.normSq_mul]

end Generic

/-! ## The lifted routine -/

section Routine

variable {ι σ W W' D : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype W] [DecidableEq W] [Fintype W'] [DecidableEq W']
  [Fintype D] [DecidableEq D]

/-- `e` is **oracle-compatible** when it carries the global query registers
into the system factor and the environment rides along. -/
def OracleCompat (e : QBasis ι σ W' ≃ QBasis ι σ W × D) : Prop :=
  ∀ (a : ι → σ) (p : QBasis ι σ W'),
    e (oracleMap a p) = (oracleMap a (e p).1, (e p).2)

omit [DecidableEq D] [Fintype D] in
/-- The oracle preserves split states along an oracle-compatible
equivalence, acting on the system factor. -/
lemma oracleMat_mulVec_splitVec {e : QBasis ι σ W' ≃ QBasis ι σ W × D}
    (he : OracleCompat e) (a : ι → σ) (φ : QBasis ι σ W → ℂ) (ξ : D → ℂ) :
    oracleMat a *ᵥ splitVec e φ ξ = splitVec e (oracleMat a *ᵥ φ) ξ := by
  classical
  funext p
  rw [oracleMat_mulVec_apply, splitVec_apply, splitVec_apply, he a p,
    oracleMat_mulVec_apply]

/-- A routine's steps, lifted along `e`. -/
@[expose]
def QRoutine.kronLift (e : QBasis ι σ W' ≃ QBasis ι σ W × D)
    (R : QRoutine ι σ W) : QRoutine ι σ W' where
  len := R.len
  step := fun t => QuantumQueryComplexity.kronLift e (R.step t)
  step_unitary := fun t => kronLift_mem_unitaryGroup e (R.step_unitary t)

@[simp] lemma QRoutine.kronLift_len (e : QBasis ι σ W' ≃ QBasis ι σ W × D)
    (R : QRoutine ι σ W) : (R.kronLift e).len = R.len := rfl

/-- **The lifted routine runs as the original on the system factor.** -/
theorem QRoutine.kronLift_runUpto_splitVec
    {e : QBasis ι σ W' ≃ QBasis ι σ W × D} (he : OracleCompat e)
    (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ) (φ : QBasis ι σ W → ℂ)
    (ξ : D → ℂ) :
    (R.kronLift e).runUpto a t *ᵥ splitVec e φ ξ
      = splitVec e (R.runUpto a t *ᵥ φ) ξ := by
  induction t with
  | zero => exact kronLift_mulVec_splitVec e (R.step 0) φ ξ
  | succ t ih =>
      change ((R.kronLift e).step (t + 1)
          * (oracleMat a * (R.kronLift e).runUpto a t)) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        oracleMat_mulVec_splitVec he]
      rw [show (R.kronLift e).step (t + 1)
          = QuantumQueryComplexity.kronLift e (R.step (t + 1)) from rfl,
        kronLift_mulVec_splitVec]
      rw [QRoutine.runUpto_succ, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]

end Routine

end QuantumQueryComplexity

end SourceQuantumKronLift

section SourceQuantumPostcomp

/-!
# Classical postprocessing of the readout

Relabelling an algorithm's measurement outcome costs nothing: `QAlg.postcomp`
changes only the `readout` field, so the state — which is built from `init`
and `step` alone — is *literally unchanged*, and the fibre sum can only grow
the correct outcome's probability (`qProb_comp_ge`).

At the complexity level this is `qQueryOn_postcomp_le : Q_ε(g ∘ f) ≤ Q_ε(f)`,
the workhorse for reading a Boolean test off a large-valued output: it is how
a lower bound proved for a Boolean postprocessing transfers to the function
itself, and it is what makes lower bounds available for outputs whose type is
too big (or infinite) for the `Fintype`-output machinery.
-/

namespace QuantumQueryComplexity

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type}

/-- Post-composing the readout can only increase the probability of the
image outcome. -/
lemma qProb_comp_ge {H O O' : Type} [Fintype H]
    [DecidableEq O] [DecidableEq O'] (g : O → O') (r : H → O) (ψ : H → ℂ)
    (o : O) :
    qProb r ψ o ≤ qProb (fun h => g (r h)) ψ (g o) := by
  rw [qProb, qProb]
  refine Finset.sum_le_sum fun h _ => ?_
  by_cases hr : r h = o
  · rw [ite_eq_left hr, ite_eq_left (by rw [hr])]
  · rw [ite_eq_right hr]
    by_cases hg : g (r h) = g o
    · rw [ite_eq_left hg]
      exact Complex.normSq_nonneg _
    · rw [ite_eq_right hg]

/-- **Relabelling the readout**: same initial state, same steps, composed
output map. -/
@[expose]
def QAlg.postcomp {O O' W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ O W) (g : O → O') : QAlg ι σ O' W :=
  { A with readout := fun p => g (A.readout p) }

@[simp] lemma QAlg.postcomp_step {O O' W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ O W) (g : O → O') : (A.postcomp g).step = A.step := rfl

@[simp] lemma QAlg.postcomp_init {O O' W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ O W) (g : O → O') : (A.postcomp g).init = A.init := rfl

@[simp] lemma QAlg.postcomp_state {O O' W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ O W) (g : O → O') (a : ι → σ) (t : ℕ) :
    (A.postcomp g).state a t = A.state a t := by
  induction t with
  | zero =>
      rw [QAlg.state_zero, QAlg.state_zero, QAlg.postcomp_step,
        QAlg.postcomp_init]
  | succ t ih =>
      rw [QAlg.state_succ, QAlg.state_succ, ih, QAlg.postcomp_step]

@[simp] lemma QAlg.postcomp_readout {O O' W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ O W) (g : O → O') :
    (A.postcomp g).readout = fun p => g (A.readout p) := rfl

/-- **Post-composition at the algorithm level**: same cost, same error, the
composed function. -/
theorem ComputesWithErrorOn.postcomp {O O' W : Type} [DecidableEq O]
    [DecidableEq O'] [Fintype W] [DecidableEq W]
    {A : QAlg ι σ O W} {q : ℕ} {read : X → ι → σ} {F : X → O} {ε : ℝ}
    (h : ComputesWithErrorOn A q read F ε) (g : O → O') :
    ComputesWithErrorOn (A.postcomp g) q read (fun x => g (F x)) ε := by
  intro x
  refine (h x).trans ?_
  rw [QAlg.prob, QAlg.prob, QAlg.postcomp_state, QAlg.postcomp_readout]
  exact qProb_comp_ge g A.readout (A.state (read x) q) (F x)

/-- The workspace-existential form, for callers that quantify it away. -/
theorem ComputesWithErrorOn.exists_postcomp {O O' W : Type} [DecidableEq O]
    [DecidableEq O'] [Fintype W] [DecidableEq W]
    {A : QAlg ι σ O W} {q : ℕ} {read : X → ι → σ} {F : X → O} {ε : ℝ}
    (h : ComputesWithErrorOn A q read F ε) (g : O → O') :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W')
      (A' : QAlg ι σ O' W'),
      ComputesWithErrorOn A' q read (fun x => g (F x)) ε :=
  ⟨W, inferInstance, inferInstance, A.postcomp g, h.postcomp g⟩

/-- Every achievable query count survives postprocessing — the mirror of
`queryCounts_subset_of_read`. -/
theorem queryCounts_postcomp {O O' : Type} [DecidableEq O]
    [DecidableEq O'] (g : O → O') (read : X → ι → σ) (f : X → O) (ε : ℝ) :
    QueryCounts read f ε ⊆ QueryCounts read (fun x => g (f x)) ε := by
  classical
  rintro q ⟨W, hW, hW', A, hA⟩
  exact ⟨W, hW, hW', A.postcomp g, hA.postcomp g⟩

/-- **Classical postprocessing of the readout is free**: post-composing the
output function can only lower the quantum query complexity. -/
theorem qQueryOn_postcomp_le {O O' : Type} [DecidableEq O]
    [DecidableEq O'] {read : X → ι → σ} {f : X → O} {ε : ℝ} (g : O → O')
    (hne : (QueryCounts read f ε).Nonempty) :
    qQueryOn read (fun x => g (f x)) ε ≤ qQueryOn read f ε := by
  classical
  exact Nat.sInf_le (queryCounts_postcomp g read f ε (Nat.sInf_mem hne))

end QuantumQueryComplexity

end SourceQuantumPostcomp

section SourceQuantumReadAll

/-!
# Reading the whole input exactly

Every observationally determined problem has an **exact** algorithm making
`|ι|` queries.  This is the theorem that makes `qQueryOn` a genuine minimum
rather than `sInf ∅ = 0`, and it is the base case of the query model: it says
the model can do at least what a classical algorithm can.

The construction records the answers in a workspace `QRec ι σ = ι → Option σ`
and never leaves the computational basis.  Two families of basis permutations
do all the work:

* `idxSwapPerm u v` — transpose the two index-register values `u` and `v`.
  Since the index register's content is *known* at each time (it is `idxAt t`),
  a transposition suffices to move it to the next index; "assign the index
  register" would not be unitary, but "transpose the value it holds with the one
  it should hold next" is.
* `slotSwapPerm j` — swap the answer register with the workspace slot `j`.
  A *swap*, not a copy: copying is not injective, but the slot is blank when the
  swap happens, so the swap has the effect of a copy and clears the answer
  register for the next query.

The step unitary at time `t` is `idxSwapPerm (prevIdx t) (idxAt t)` after
`slotSwapPerm (prevIdx t)`, and the invariant carried by the induction is

  `state a t = |idxAt t⟩ |⊥⟩ |recAt a t⟩`,

with `recAt a t` the record holding the answers of the first `t` indices.  It
holds for **every** `t`, with no side condition: past `|ι|` the index register is
idle, the oracle acts trivially and the state stops moving, so the algorithm
pads for free.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X]

/-! ## Two families of basis permutations -/

section IdxSwap

variable {W : Type} [Fintype W] [DecidableEq W]

/-- Transpose two values of the query-index register. -/
@[expose]
def idxSwapMap (u v : Option ι) : QBasis ι σ W → QBasis ι σ W :=
  fun p => (Equiv.swap u v p.1, p.2)

omit [DecidableEq W] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
lemma idxSwapMap_involutive (u v : Option ι) :
    Function.Involutive (idxSwapMap (σ := σ) (W := W) u v) := by
  rintro ⟨k, r⟩
  simp [idxSwapMap]

/-- The index-register transposition, as a permutation of the basis. -/
@[expose]
def idxSwapPerm (u v : Option ι) : Equiv.Perm (QBasis ι σ W) :=
  Function.Involutive.toPerm _ (idxSwapMap_involutive u v)

omit [DecidableEq W] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
@[simp] lemma idxSwapPerm_apply (u v : Option ι) (p : QBasis ι σ W) :
    idxSwapPerm u v p = (Equiv.swap u v p.1, p.2) := rfl

end IdxSwap

/-- The workspace of the exact algorithm: a record of the answers seen so far. -/
abbrev QRec (ι σ : Type) : Type := ι → Option σ

/-- Swap the answer register with the workspace slot `j`. -/
@[expose]
def slotSwapMap (j : ι) : QBasis ι σ (QRec ι σ) → QBasis ι σ (QRec ι σ) :=
  fun p => (p.1, p.2.2 j, Function.update p.2.2 j p.2.1)

omit [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma slotSwapMap_involutive (j : ι) :
    Function.Involutive (slotSwapMap (ι := ι) (σ := σ) j) := by
  rintro ⟨k, t, w⟩
  simp [slotSwapMap, Function.update_idem]

/-- The slot swap at an *optional* index: at `none` there is nothing to store, so
the algorithm idles.  This is what lets one formula describe every step. -/
@[expose]
def slotSwapPerm : Option ι → Equiv.Perm (QBasis ι σ (QRec ι σ))
  | none => 1
  | some j => Function.Involutive.toPerm _ (slotSwapMap_involutive j)

omit [DecidableEq σ] [Fintype ι] [Fintype σ] in
@[simp] lemma slotSwapPerm_none :
    slotSwapPerm (ι := ι) (σ := σ) none = 1 := rfl

omit [DecidableEq σ] [Fintype ι] [Fintype σ] in
@[simp] lemma slotSwapPerm_some (j : ι) (p : QBasis ι σ (QRec ι σ)) :
    slotSwapPerm (some j) p = (p.1, p.2.2 j, Function.update p.2.2 j p.2.1) := rfl

/-! ## The schedule -/

/-- The index queried at time `t`; `none` once every index has been read. -/
noncomputable def idxAt (ι : Type) [Fintype ι] (t : ℕ) : Option ι :=
  if h : t < Fintype.card ι then some ((Fintype.equivFin ι).symm ⟨t, h⟩) else none

/-- The index queried at time `t - 1`, i.e. the one whose answer the step at time
`t` has to store. -/
noncomputable def prevIdx (ι : Type) [Fintype ι] : ℕ → Option ι
  | 0 => none
  | t + 1 => idxAt ι t

omit [DecidableEq ι] in
lemma idxAt_of_lt {t : ℕ} (h : t < Fintype.card ι) :
    idxAt ι t = some ((Fintype.equivFin ι).symm ⟨t, h⟩) := dite_eq_left h

omit [DecidableEq ι] in
lemma idxAt_eq_none_iff (t : ℕ) : idxAt ι t = none ↔ Fintype.card ι ≤ t := by
  unfold idxAt
  by_cases h : t < Fintype.card ι
  · simp only [h, dite_eq_left, reduceCtorEq, false_iff, not_le]
  · simp only [h, dite_eq_right, not_false_iff, true_iff]
    omega

omit [DecidableEq ι] in
lemma equivFin_of_idxAt {t : ℕ} {j : ι} (h : idxAt ι t = some j) :
    (Fintype.equivFin ι j : ℕ) = t := by
  classical
  by_cases ht : t < Fintype.card ι
  · rw [idxAt_of_lt ht] at h
    have hj : j = (Fintype.equivFin ι).symm ⟨t, ht⟩ := (Option.some_injective _ h).symm
    rw [hj, Equiv.apply_symm_apply]
  · rw [idxAt, dite_eq_right ht] at h
    exact absurd h (by simp)

/-! ## The record -/

/-- The workspace after `t` queries: the answers at the first `t` indices. -/
@[expose]
noncomputable def recAt (a : ι → σ) (t : ℕ) : QRec ι σ :=
  fun i => if (Fintype.equivFin ι i : ℕ) < t then some (a i) else none

omit [DecidableEq ι] [DecidableEq σ] [Fintype σ] in
lemma recAt_apply (a : ι → σ) (t : ℕ) (i : ι) :
    recAt a t i = if (Fintype.equivFin ι i : ℕ) < t then some (a i) else none := rfl

omit [DecidableEq ι] [DecidableEq σ] [Fintype σ] in
lemma recAt_zero (a : ι → σ) : recAt a 0 = fun _ => none := by
  funext i
  simp [recAt_apply]

omit [DecidableEq ι] [DecidableEq σ] [Fintype σ] in
/-- Once every index has been read the record is complete. -/
lemma recAt_of_card_le (a : ι → σ) {t : ℕ} (h : Fintype.card ι ≤ t) :
    recAt a t = fun i => some (a i) := by
  classical
  funext i
  rw [recAt_apply, ite_eq_left]
  exact lt_of_lt_of_le (Fintype.equivFin ι i).isLt h

omit [DecidableEq σ] [Fintype σ] in
/-- Storing the answer at the index read at time `t` advances the record. -/
lemma update_recAt (a : ι → σ) {t : ℕ} {j : ι} (hj : (Fintype.equivFin ι j : ℕ) = t) :
    Function.update (recAt a t) j (some (a j)) = recAt a (t + 1) := by
  classical
  funext i
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self, recAt_apply, ite_eq_left (by omega)]
  · rw [Function.update_of_ne hij, recAt_apply, recAt_apply]
    have hne : (Fintype.equivFin ι i : ℕ) ≠ t := by
      intro hc
      exact hij ((Fintype.equivFin ι).injective (Fin.ext (by rw [hc, hj])))
    by_cases hlt : (Fintype.equivFin ι i : ℕ) < t
    · rw [ite_eq_left hlt, ite_eq_left (by omega)]
    · rw [ite_eq_right hlt, ite_eq_right (by omega)]

omit [DecidableEq ι] [DecidableEq σ] [Fintype σ] in
/-- The slot the algorithm is about to write to is blank. -/
lemma recAt_self_eq_none (a : ι → σ) {t : ℕ} {j : ι}
    (hj : (Fintype.equivFin ι j : ℕ) = t) : recAt a t j = none := by
  classical
  rw [recAt_apply, ite_eq_right (by omega)]

/-! ## The algorithm -/

/-- **The algorithm that reads every coordinate**, announcing `dec` of the
completed record. -/
@[expose]
noncomputable def readAllAlg (dec : QRec ι σ → O) : QAlg ι σ O (QRec ι σ) where
  init := qBasis (none, none, fun _ => none)
  init_isQState := isQState_qBasis _
  step := fun t =>
    qPerm (idxSwapPerm (prevIdx ι t) (idxAt ι t)) * qPerm (slotSwapPerm (prevIdx ι t))
  step_unitary := fun _ =>
    mul_mem_qUnitary (qPerm_mem_unitaryGroup _) (qPerm_mem_unitaryGroup _)
  readout := fun p => dec p.2.2

@[simp] lemma readAllAlg_readout (dec : QRec ι σ → O) (p : QBasis ι σ (QRec ι σ)) :
    (readAllAlg dec).readout p = dec p.2.2 := rfl

lemma readAllAlg_step_qBasis (dec : QRec ι σ → O) (t : ℕ)
    (p : QBasis ι σ (QRec ι σ)) :
    (readAllAlg dec).step t *ᵥ qBasis p
      = qBasis (idxSwapPerm (prevIdx ι t) (idxAt ι t) (slotSwapPerm (prevIdx ι t) p)) := by
  change (qPerm (idxSwapPerm (prevIdx ι t) (idxAt ι t))
      * qPerm (slotSwapPerm (prevIdx ι t))) *ᵥ qBasis p = _
  rw [← Matrix.mulVec_mulVec, qPerm_mulVec_qBasis, qPerm_mulVec_qBasis]

/-- **The invariant.**  After `t` queries the algorithm holds the record of the
first `t` answers, with the index register pointing at the next index and the
answer register blank. -/
theorem readAllAlg_state (dec : QRec ι σ → O) (a : ι → σ) (t : ℕ) :
    (readAllAlg dec).state a t = qBasis (idxAt ι t, none, recAt a t) := by
  induction t with
  | zero =>
      change (readAllAlg dec).step 0 *ᵥ qBasis ((none, none, fun _ => none)) = _
      rw [readAllAlg_step_qBasis, recAt_zero]
      congr 1
  | succ t ih =>
      rw [QAlg.state_succ, ih, oracleMat_mulVec_qBasis, readAllAlg_step_qBasis]
      congr 1
      change idxSwapPerm (idxAt ι t) (idxAt ι (t + 1))
          (slotSwapPerm (idxAt ι t) (oracleMap a (idxAt ι t, none, recAt a t))) = _
      cases hidx : idxAt ι t with
      | none =>
          have hcard : Fintype.card ι ≤ t := (idxAt_eq_none_iff t).mp hidx
          have h1 : recAt a t = recAt a (t + 1) := by
            rw [recAt_of_card_le a hcard, recAt_of_card_le a (by omega)]
          rw [oracleMap_none, slotSwapPerm_none]
          change (Equiv.swap none (idxAt ι (t + 1)) none, none, recAt a t) = _
          rw [Equiv.swap_apply_left, h1]
      | some j =>
          have hj : (Fintype.equivFin ι j : ℕ) = t := equivFin_of_idxAt hidx
          rw [oracleMap_blank, slotSwapPerm_some]
          change (Equiv.swap (some j) (idxAt ι (t + 1)) (some j), recAt a t j,
            Function.update (recAt a t) j (some (a j))) = _
          rw [Equiv.swap_apply_left, recAt_self_eq_none a hj, update_recAt a hj]

/-- **The algorithm announces `dec` of the full input after `|ι|` queries.** -/
theorem readAllAlg_prob (dec : QRec ι σ → O) [DecidableEq O] (a : ι → σ) :
    (readAllAlg dec).prob a (Fintype.card ι) (dec fun i => some (a i)) = 1 := by
  rw [QAlg.prob, readAllAlg_state, recAt_of_card_le a le_rfl, qProb_qBasis]
  simp

/-! ## Every observationally determined problem is exactly solvable -/

/-- The readout: decode a completed record into the value of `f`.  Well defined
by observational determinacy — two promise inputs with the same record are
indistinguishable, hence have the same `f`-value. -/
noncomputable def recDecode [Nonempty O] (read : X → ι → σ) (f : X → O)
    (w : QRec ι σ) : O := by
  classical
  exact if h : ∃ x : X, ∀ i, w i = some (read x i) then f h.choose
    else Classical.arbitrary O

omit [DecidableEq ι] [Fintype σ] in
lemma recDecode_apply [Nonempty O] {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) (x : X) :
    recDecode read f (fun i => some (read x i)) = f x := by
  classical
  have hex : ∃ y : X, ∀ i, (fun i => some (read x i)) i = some (read y i) :=
    ⟨x, fun _ => rfl⟩
  rw [recDecode, dite_eq_left hex]
  refine (hdet x hex.choose (funext fun i => ?_)).symm
  exact Option.some_injective _ (hex.choose_spec i)

omit [Fintype X] in
/-- **Every observationally determined problem has an exact `|ι|`-query
algorithm.**  In particular the set of achievable query counts is nonempty, so
`qQueryOn` is a genuine minimum. -/
theorem exists_computesWithErrorOn [DecidableEq O] [Nonempty O] {read : X → ι → σ}
    {f : X → O} (hdet : ∀ x y, read x = read y → f x = f y) {ε : ℝ} (hε : 0 ≤ ε) [Finite X] :
    ∃ A : QAlg ι σ O (QRec ι σ),
      ComputesWithErrorOn A (Fintype.card ι) read f ε := by
  classical
  let := Fintype.ofFinite X
  refine ⟨readAllAlg (recDecode read f), fun x => ?_⟩
  have h : (readAllAlg (recDecode read f)).prob (read x) (Fintype.card ι) (f x) = 1 := by
    rw [← recDecode_apply hdet x]
    exact readAllAlg_prob _ _
  rw [h]
  linarith

omit [Fintype X] in
/-- **The achievable set is nonempty**, which is the hypothesis every lower
bound in `SourceQuantumComplexity` carries. -/
theorem queryCounts_nonempty [DecidableEq O] [Nonempty O] {read : X → ι → σ}
    {f : X → O} (hdet : ∀ x y, read x = read y → f x = f y) {ε : ℝ} (hε : 0 ≤ ε) [Finite X] :
    (QueryCounts read f ε).Nonempty := by
  classical
  let := Fintype.ofFinite X
  obtain ⟨A, hA⟩ := exists_computesWithErrorOn hdet hε
  exact ⟨Fintype.card ι, mem_queryCounts hA⟩

omit [Fintype X] in
/-- **Reading everything is enough**: `qQueryOn ≤ |ι|`. -/
theorem qQueryOn_le_card [DecidableEq O] [Nonempty O] {read : X → ι → σ}
    {f : X → O} (hdet : ∀ x y, read x = read y → f x = f y) {ε : ℝ} (hε : 0 ≤ ε) [Finite X] :
    qQueryOn read f ε ≤ Fintype.card ι := by
  classical
  let := Fintype.ofFinite X
  obtain ⟨A, hA⟩ := exists_computesWithErrorOn hdet hε
  exact qQueryOn_le hA

end QuantumQueryComplexity

end SourceQuantumReadAll

section SourceQuantumRunWith
/-!
# Running a routine against an arbitrary oracle matrix

The `QRoutine.runWith` semantics and composition laws are proved alongside
`QRoutine` in `SourceQuantumRoutine`. The standard `runUpto` semantics is their
transposition-oracle specialization. Both the standard and XOR simulation
compilers use the shared arbitrary-oracle implementation.
-/
end SourceQuantumRunWith

section SourceQuantumUniformAlphabet

/-!
# The uniform alphabet factorization

This alphabet factorization removes the `√|σ|` loss in uniform extraction.

A dual solution has to realise the *inequality indicator* `[a ≠ b]` as an
inner product of vectors attached to the two letters.  The construction used
so far copies a value onto every letter that differs, so its norms grow like
`√|σ|`.  The uniform replacement lives on `Option σ` — one extra "constant"
coordinate beside the `σ`-indexed ones.  The vectors live in an ambient space
of dimension `|σ| + 1`, but each is supported on exactly two coordinates;
they are **two-sparse independently of the alphabet size**:

    μ a = (1,  e a)          ν b = (1, − e b)

    ⟨μ a, ν b⟩ = 1 − δ_{ab} = [a ≠ b]
    ‖μ a‖² = ‖ν b‖² = 2

The constant coordinate contributes `1` to every pairing; the letter
coordinates contribute `−1` exactly when the letters agree, cancelling it.
Both **squared** norms are `2` — equivalently both norms are `√2` —
**independently of the alphabet size**, which is the whole point.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- The left vector of the factorization: `1` on the constant coordinate and
`1` at its own letter. -/
@[expose]
def uniformLeft (a : σ) : Option σ → ℝ
  | none => 1
  | some x => if x = a then 1 else 0

/-- The right vector: `1` on the constant coordinate and `−1` at its own
letter. -/
@[expose]
def uniformRight (b : σ) : Option σ → ℝ
  | none => 1
  | some x => if x = b then -1 else 0

omit [Fintype σ] in
@[simp] lemma uniformLeft_none (a : σ) : uniformLeft a none = 1 := rfl

omit [Fintype σ] in
@[simp] lemma uniformLeft_some (a x : σ) :
    uniformLeft a (some x) = if x = a then 1 else 0 := rfl

omit [Fintype σ] in
@[simp] lemma uniformRight_none (b : σ) : uniformRight b none = 1 := rfl

omit [Fintype σ] in
@[simp] lemma uniformRight_some (b x : σ) :
    uniformRight b (some x) = if x = b then -1 else 0 := rfl

/-- **The factorization**: the pairing is the inequality indicator. -/
theorem uniform_dotProduct (a b : σ) :
    uniformLeft a ⬝ᵥ uniformRight b = if a = b then 0 else 1 := by
  classical
  rw [dotProduct, Fintype.sum_option]
  have hterm : ∀ x : σ, uniformLeft a (some x) * uniformRight b (some x)
      = if a = b then (if x = a then (-1 : ℝ) else 0) else 0 := by
    intro x
    simp only [uniformLeft_some, uniformRight_some]
    by_cases hxa : x = a
    · subst hxa
      simp
    · simp [hxa]
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  by_cases hab : a = b
  · subst hab
    simp
  · simp [hab]

/-- **Both squared norms are `2`** — equivalently both norms are `√2` —
independently of the alphabet size. -/
theorem uniformLeft_normSq (a : σ) : uniformLeft a ⬝ᵥ uniformLeft a = 2 := by
  classical
  rw [dotProduct, Fintype.sum_option]
  have hterm : ∀ x : σ, uniformLeft a (some x) * uniformLeft a (some x)
      = if x = a then (1 : ℝ) else 0 := by
    intro x
    simp only [uniformLeft_some]
    by_cases hxa : x = a <;> simp [hxa]
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  simp
  norm_num

theorem uniformRight_normSq (b : σ) :
    uniformRight b ⬝ᵥ uniformRight b = 2 := by
  classical
  rw [dotProduct, Fintype.sum_option]
  have hterm : ∀ x : σ, uniformRight b (some x) * uniformRight b (some x)
      = if x = b then (1 : ℝ) else 0 := by
    intro x
    simp only [uniformRight_some]
    by_cases hxb : x = b <;> simp [hxb]
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  simp
  norm_num

/-- The factorization in the form the dual constraint consumes: the pairing
vanishes exactly when the letters agree, i.e. when the query does not
distinguish the two inputs. -/
theorem uniform_dotProduct_eq_zero_iff (a b : σ) :
    uniformLeft a ⬝ᵥ uniformRight b = 0 ↔ a = b := by
  rw [uniform_dotProduct]
  by_cases hab : a = b
  · rw [ite_eq_left hab]
    exact ⟨fun _ => hab, fun _ => rfl⟩
  · rw [ite_eq_right hab]
    exact ⟨fun h => absurd h (by norm_num), fun h => absurd h hab⟩

end QuantumQueryComplexity

end SourceQuantumUniformAlphabet

section SourceQuantumHadamardTest

/-!
# The Hadamard test, compiled

The generic measurement layer of the algorithm extraction: given a routine `R`
and a unit vector `u`, the **Hadamard test** prepares
`(|0⟩ + |1⟩)/√2 ⊗ u`, runs `R` controlled on the first qubit, applies a
Hadamard to it, and measures it.  The whole point:

    P(announce true)  = (1 + Re⟪u, R.run a · u⟫)/2
    P(announce false) = (1 − Re⟪u, R.run a · u⟫)/2

(`hadTest_prob_true` / `hadTest_prob_false`) — the test turns the real part of
the expectation `⟪u, R_a u⟫`, which the fidelity bounds of `SourceQuantumFidelity`
control, into an outcome probability, at **exactly `R.len` queries**
(`QRoutine.control` costs `R.len`, the Hadamards are free).

The compilation reuses the existing plumbing wholesale: `QRoutine.control`
for the controlled run, `regOp` for the Hadamard on the control register,
`comp`/`ofUnitary` for the final gate, and `toAlg` for the bridge to `QAlg`.
The announcement convention is `true` on control `0`: the detector this test
will be applied to is `≈ +1` on the accepting side, so acceptance is
constructive interference back onto `|0⟩`.

`hadMat` is real symmetric, and everything about it is decided entrywise over
`Bool` — no `2 × 2` matrix theory is imported.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-! ## The Hadamard gate, on the control register -/

/-- `1/√2`, as a complex scalar. -/
noncomputable def hadS : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

lemma star_hadS : star hadS = hadS := by
  rw [hadS, RCLike.star_def, Complex.conj_ofReal]

lemma hadS_mul_hadS : hadS * hadS = (2 : ℂ)⁻¹ := by
  rw [hadS, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma normSq_hadS : Complex.normSq hadS = 2⁻¹ := by
  rw [hadS, Complex.normSq_ofReal, ← mul_inv,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The Hadamard gate on one qubit: `(1/√2)·(−1)^{b·b'}`. -/
@[expose]
noncomputable def hadMat : Matrix Bool Bool ℂ :=
  Matrix.of fun b b' => if b && b' then -hadS else hadS

@[simp] lemma hadMat_apply (b b' : Bool) :
    hadMat b b' = if b && b' then -hadS else hadS := rfl

lemma hadMat_mem_unitaryGroup : hadMat ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext b b'
  rw [Matrix.mul_apply, Fintype.sum_bool]
  cases b <;> cases b' <;>
    simp only [Matrix.conjTranspose_apply, hadMat_apply, Bool.and_self,
      Bool.and_false, Bool.and_true,
      ite_true, ite_false, Bool.false_eq_true, star_neg, star_hadS,
      Matrix.one_apply, mul_neg, neg_mul, neg_neg, hadS_mul_hadS] <;>
    norm_num

/-- The Hadamard on the control register of `CtrlWork`. -/
noncomputable def ctrlHad :
    Matrix (QBasis ι σ (CtrlWork ι W)) (QBasis ι σ (CtrlWork ι W)) ℂ :=
  regOp hadMat

lemma regOp_mem_unitaryGroup {V : Type} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℂ} (hA : A ∈ Matrix.unitaryGroup V ℂ) :
    regOp (ι := ι) (σ := σ) (W := W) A
      ∈ Matrix.unitaryGroup (QBasis ι σ (V × W)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    regOp_conjTranspose, regOp_mul, conjTranspose_mul_self_of_unitary hA,
    regOp_one]

lemma ctrlHad_mem_unitaryGroup :
    ctrlHad (ι := ι) (σ := σ) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι σ (CtrlWork ι W)) ℂ :=
  regOp_mem_unitaryGroup hadMat_mem_unitaryGroup

/-- **The Hadamard acts on the control sectors** as its column says. -/
lemma ctrlHad_mulVec_embedCtrl (b : Bool) (ψ : QBasis ι σ W → ℂ) :
    ctrlHad *ᵥ embedCtrl b ψ
      = hadMat true b • embedCtrl true ψ + hadMat false b • embedCtrl false ψ := by
  rw [ctrlHad, embedCtrl, regOp_mulVec_embedReg, Fintype.sum_bool]
  rfl

/-! ## Sector algebra -/

omit [DecidableEq W] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
lemma embedCtrl_add (b : Bool) (ψ φ : QBasis ι σ W → ℂ) :
    embedCtrl b (ψ + φ) = embedCtrl b ψ + embedCtrl b φ := by
  classical
  funext p
  by_cases h : p.2.2.1 = b ∧ p.2.2.2.1 = none <;>
    simp [embedCtrl_apply, h]

omit [DecidableEq W] [DecidableEq σ] [Fintype W] [Fintype ι] [Fintype σ] in
lemma embedCtrl_sub (b : Bool) (ψ φ : QBasis ι σ W → ℂ) :
    embedCtrl b (ψ - φ) = embedCtrl b ψ - embedCtrl b φ := by
  classical
  funext p
  by_cases h : p.2.2.1 = b ∧ p.2.2.2.1 = none <;>
    simp [embedCtrl_apply, h]

omit [DecidableEq W] [DecidableEq σ] in
lemma qNormSq_embedCtrl (b : Bool) (ψ : QBasis ι σ W → ℂ) :
    qNormSq (embedCtrl b ψ) = qNormSq ψ := by
  classical
  rw [embedCtrl, qNormSq_embedReg, qNormSq_embedReg]

omit [DecidableEq W] [DecidableEq σ] in
lemma qInner_embedCtrl (b b' : Bool) (ψ φ : QBasis ι σ W → ℂ) :
    qInner (embedCtrl b ψ) (embedCtrl b' φ)
      = if b = b' then qInner ψ φ else 0 := by
  classical
  rw [embedCtrl, embedCtrl, qInner_embedReg]
  by_cases h : b = b'
  · rw [ite_eq_left h, ite_eq_left h, qInner_embedReg, ite_eq_left rfl]
  · rw [ite_eq_right h, ite_eq_right h]

/-! ## The test -/

/-- The Hadamard-test initial state: `(|0⟩ + |1⟩)/√2 ⊗ u`. -/
noncomputable def hadInit (u : QBasis ι σ W → ℂ) :
    QBasis ι σ (CtrlWork ι W) → ℂ :=
  hadS • (embedCtrl false u + embedCtrl true u)

omit [DecidableEq W] [DecidableEq σ] in
lemma isQState_hadInit {u : QBasis ι σ W → ℂ} (hu : IsQState u) :
    IsQState (hadInit u) := by
  classical
  rw [IsQState, hadInit, qNormSq_smul, normSq_hadS, qNormSq_add,
    qNormSq_embedCtrl, qNormSq_embedCtrl, qInner_embedCtrl,
    ite_eq_right (by simp : ¬(false = true)), hu]
  norm_num

/-- **The Hadamard test of `R` on `u`**: controlled-`R` between two Hadamards
on a control qubit, measuring the control.  Announces `true` on control `0`.
Costs exactly `R.len` queries. -/
@[expose]
noncomputable def hadTest (R : QRoutine ι σ W) (u : QBasis ι σ W → ℂ)
    (hu : IsQState u) : QAlg ι σ Bool (CtrlWork ι W) :=
  (R.control.comp (QRoutine.ofUnitary ctrlHad ctrlHad_mem_unitaryGroup)).toAlg
    (hadInit u) (isQState_hadInit hu) (fun p => !p.2.2.1)

lemma hadTest_readout (R : QRoutine ι σ W) (u : QBasis ι σ W → ℂ)
    (hu : IsQState u) :
    (hadTest R u hu).readout = fun p : QBasis ι σ (CtrlWork ι W) => !p.2.2.1 :=
  rfl

/-- **The final state of the test**, exactly: interference between `u` and
`R_a u`, sorted by the control bit. -/
theorem hadTest_state (R : QRoutine ι σ W) (u : QBasis ι σ W → ℂ)
    (hu : IsQState u) (a : ι → σ) :
    (hadTest R u hu).state a R.len
      = (hadS * hadS) • (embedCtrl false (u + R.run a *ᵥ u)
          + embedCtrl true (u - R.run a *ᵥ u)) := by
  have hlen : (R.control.comp
      (QRoutine.ofUnitary ctrlHad ctrlHad_mem_unitaryGroup)).len = R.len := by
    rw [QRoutine.comp_len, QRoutine.ofUnitary_len, control_len,
      Nat.add_zero]
  rw [hadTest, ← hlen, QRoutine.toAlg_state_len, QRoutine.comp_run,
    QRoutine.ofUnitary_run, ← Matrix.mulVec_mulVec, hadInit,
    Matrix.mulVec_smul, Matrix.mulVec_add, control_run_false,
    control_run_true, Matrix.mulVec_smul, Matrix.mulVec_add,
    ctrlHad_mulVec_embedCtrl, ctrlHad_mulVec_embedCtrl]
  simp only [hadMat_apply, Bool.and_false, Bool.and_true, Bool.and_self,
    ite_false, ite_true, Bool.false_eq_true]
  rw [embedCtrl_add, embedCtrl_sub]
  module

omit [DecidableEq W] [DecidableEq σ] in
/-- The measurement rule of the sorted state. -/
lemma qProb_hadReadout_true (a : ℂ) (χ₁ χ₂ : QBasis ι σ W → ℂ) :
    qProb (fun p : QBasis ι σ (CtrlWork ι W) => !p.2.2.1)
      (a • (embedCtrl false χ₁ + embedCtrl true χ₂)) true
      = Complex.normSq a * qNormSq χ₁ := by
  classical
  rw [qProb_eq_qNormSq_qRestrict]
  have hres : qRestrict (fun p : QBasis ι σ (CtrlWork ι W) => !p.2.2.1) true
      (a • (embedCtrl false χ₁ + embedCtrl true χ₂))
      = a • embedCtrl false χ₁ := by
    funext p
    rw [qRestrict]
    cases hb : p.2.2.1 with
    | false => simp [hb, embedCtrl_apply]
    | true => simp [hb, embedCtrl_apply]
  rw [hres, qNormSq_smul, qNormSq_embedCtrl]

omit [DecidableEq W] [DecidableEq σ] in
lemma qProb_hadReadout_false (a : ℂ) (χ₁ χ₂ : QBasis ι σ W → ℂ) :
    qProb (fun p : QBasis ι σ (CtrlWork ι W) => !p.2.2.1)
      (a • (embedCtrl false χ₁ + embedCtrl true χ₂)) false
      = Complex.normSq a * qNormSq χ₂ := by
  classical
  rw [qProb_eq_qNormSq_qRestrict]
  have hres : qRestrict (fun p : QBasis ι σ (CtrlWork ι W) => !p.2.2.1) false
      (a • (embedCtrl false χ₁ + embedCtrl true χ₂))
      = a • embedCtrl true χ₂ := by
    funext p
    rw [qRestrict]
    cases hb : p.2.2.1 with
    | false => simp [hb, embedCtrl_apply]
    | true => simp [hb, embedCtrl_apply]
  rw [hres, qNormSq_smul, qNormSq_embedCtrl]

private lemma normSq_hadS_sq : Complex.normSq (hadS * hadS) = 4⁻¹ := by
  rw [Complex.normSq_mul, normSq_hadS]
  norm_num

/-- **The acceptance probability of the Hadamard test.** -/
theorem hadTest_prob_true (R : QRoutine ι σ W) {u : QBasis ι σ W → ℂ}
    (hu : IsQState u) (a : ι → σ) :
    (hadTest R u hu).prob a R.len true
      = (1 + (qInner u (R.run a *ᵥ u)).re) / 2 := by
  rw [QAlg.prob, hadTest_readout, hadTest_state R u hu a,
    qProb_hadReadout_true, normSq_hadS_sq, qNormSq_add, hu,
    qNormSq_mulVec (R.run_mem_unitaryGroup a), hu]
  ring

/-- **The rejection probability of the Hadamard test.** -/
theorem hadTest_prob_false (R : QRoutine ι σ W) {u : QBasis ι σ W → ℂ}
    (hu : IsQState u) (a : ι → σ) :
    (hadTest R u hu).prob a R.len false
      = (1 - (qInner u (R.run a *ᵥ u)).re) / 2 := by
  have hsub : qNormSq (u - R.run a *ᵥ u)
      = 2 - 2 * (qInner u (R.run a *ᵥ u)).re := by
    have h : u - R.run a *ᵥ u = u + (-1 : ℂ) • (R.run a *ᵥ u) := by module
    rw [h, qNormSq_add, qNormSq_smul, qInner_smul_right, hu,
      qNormSq_mulVec (R.run_mem_unitaryGroup a), hu]
    simp only [Complex.normSq_neg, Complex.normSq_one, neg_one_mul,
      Complex.neg_re]
    ring
  rw [QAlg.prob, hadTest_readout, hadTest_state R u hu a,
    qProb_hadReadout_false, normSq_hadS_sq, hsub]
  ring

end QuantumQueryComplexity

end SourceQuantumHadamardTest

section SourceQuantumProductRun

/-!
# The independent-run compiler: exact product statistics

Two algorithms, compiled into one whose outcome distribution is the **exact
product** of theirs — the engine of amplification and of the finite-output
construction.

**Banks, not uncompute.**  The compiled workspace holds a full
`QBasis ι σ Wⱼ`-valued *bank* for each algorithm; the global initial state is
the tensor product of the two initial states parked in their banks, with
blank global query registers.  Phase `j` swaps bank `j` into the active
position (a basis permutation exchanging the global query/answer registers
with the bank's stored pair), runs algorithm `j`'s schedule lifted along the
oracle-compatible equivalence `pairEquivⱼ` (`SourceQuantumKronLift`), and swaps back.
Each phase therefore acts on a pristine tensor factor: no uncompute, no
factor two in the cost, and the final state is **literally**

    prodState blank (A₁.state a q₁) (A₂.state a q₂),

so the joint measurement factorizes exactly (`qProb_pairReadout`).

`Realizes read q P` packages "some algorithm has outcome distribution `P`
after `q` queries"; `Realizes.pair` is the compiler, `Realizes.map` reshapes
outcomes through the readout for free, and `Realizes.fold` iterates the pair
into a `k`-tuple with product statistics at cost `∑ qⱼ`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂]
  [DecidableEq W₂]

/-! ## The two factorizing equivalences and the two swaps -/

/-- Phase 1's view: system = (global registers, bank 1's workspace),
environment = (bank 1's parked registers, bank 2). -/
def pairEquiv₁ : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)
    ≃ QBasis ι σ W₁ × ((Option ι × Option σ) × QBasis ι σ W₂) where
  toFun p := ((p.1, p.2.1, p.2.2.1.2.2), ((p.2.2.1.1, p.2.2.1.2.1), p.2.2.2))
  invFun q := (q.1.1, q.1.2.1, ((q.2.1.1, q.2.1.2, q.1.2.2), q.2.2))
  left_inv := by rintro ⟨idx, ans, ⟨⟨i₁, a₁, w₁⟩, β₂⟩⟩; rfl
  right_inv := by rintro ⟨⟨idx, ans, w₁⟩, ⟨⟨i₁, a₁⟩, β₂⟩⟩; rfl

/-- Phase 2's view. -/
def pairEquiv₂ : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)
    ≃ QBasis ι σ W₂ × ((Option ι × Option σ) × QBasis ι σ W₁) where
  toFun p := ((p.1, p.2.1, p.2.2.2.2.2), ((p.2.2.2.1, p.2.2.2.2.1), p.2.2.1))
  invFun q := (q.1.1, q.1.2.1, (q.2.2, (q.2.1.1, q.2.1.2, q.1.2.2)))
  left_inv := by rintro ⟨idx, ans, ⟨β₁, ⟨i₂, a₂, w₂⟩⟩⟩; rfl
  right_inv := by rintro ⟨⟨idx, ans, w₂⟩, ⟨⟨i₂, a₂⟩, β₁⟩⟩; rfl

omit [DecidableEq W₁] [DecidableEq W₂] [DecidableEq ι] [Fintype W₁] [Fintype W₂] [Fintype ι]
    [Fintype σ] in
lemma oracleCompat_pairEquiv₁ :
    OracleCompat (pairEquiv₁ (ι := ι) (σ := σ) (W₁ := W₁) (W₂ := W₂)) := by
  classical
  rintro a ⟨(_ | i), ans, ⟨⟨i₁, a₁, w₁⟩, β₂⟩⟩ <;> rfl

omit [DecidableEq W₁] [DecidableEq W₂] [DecidableEq ι] [Fintype W₁] [Fintype W₂] [Fintype ι]
    [Fintype σ] in
lemma oracleCompat_pairEquiv₂ :
    OracleCompat (pairEquiv₂ (ι := ι) (σ := σ) (W₁ := W₁) (W₂ := W₂)) := by
  classical
  rintro a ⟨(_ | i), ans, ⟨β₁, ⟨i₂, a₂, w₂⟩⟩⟩ <;> rfl

/-- Swap the global query/answer registers with bank 1's parked pair. -/
def pairSwap₁Map : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)
    → QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)
  | (idx, ans, ((i₁, a₁, w₁), β₂)) => (i₁, a₁, ((idx, ans, w₁), β₂))

omit [DecidableEq W₁] [DecidableEq W₂] [DecidableEq ι] [DecidableEq σ] [Fintype W₁]
    [Fintype W₂] [Fintype ι] [Fintype σ] in
lemma pairSwap₁Map_involutive :
    Function.Involutive
      (pairSwap₁Map (ι := ι) (σ := σ) (W₁ := W₁) (W₂ := W₂)) := by
  classical
  rintro ⟨idx, ans, ⟨⟨i₁, a₁, w₁⟩, β₂⟩⟩
  rfl

/-- Swap the global query/answer registers with bank 2's parked pair. -/
def pairSwap₂Map : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)
    → QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)
  | (idx, ans, (β₁, (i₂, a₂, w₂))) => (i₂, a₂, (β₁, (idx, ans, w₂)))

omit [DecidableEq W₁] [DecidableEq W₂] [DecidableEq ι] [DecidableEq σ] [Fintype W₁]
    [Fintype W₂] [Fintype ι] [Fintype σ] in
lemma pairSwap₂Map_involutive :
    Function.Involutive
      (pairSwap₂Map (ι := ι) (σ := σ) (W₁ := W₁) (W₂ := W₂)) := by
  classical
  rintro ⟨idx, ans, ⟨β₁, ⟨i₂, a₂, w₂⟩⟩⟩
  rfl

/-- The swap-in unitary for bank 1. -/
def pairSwap₁Mat : Matrix (QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂))
    (QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)) ℂ :=
  qPerm (Function.Involutive.toPerm _ pairSwap₁Map_involutive)

lemma pairSwap₁Mat_mem_unitaryGroup :
    pairSwap₁Mat (ι := ι) (σ := σ) (W₁ := W₁) (W₂ := W₂)
      ∈ Matrix.unitaryGroup _ ℂ :=
  qPerm_mem_unitaryGroup _

lemma pairSwap₁Mat_mulVec_apply
    (ψ : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂) → ℂ) (p) :
    (pairSwap₁Mat *ᵥ ψ) p = ψ (pairSwap₁Map p) := by
  rw [pairSwap₁Mat, qPerm_mulVec_apply]
  rfl

/-- The swap-in unitary for bank 2. -/
def pairSwap₂Mat : Matrix (QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂))
    (QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)) ℂ :=
  qPerm (Function.Involutive.toPerm _ pairSwap₂Map_involutive)

lemma pairSwap₂Mat_mem_unitaryGroup :
    pairSwap₂Mat (ι := ι) (σ := σ) (W₁ := W₁) (W₂ := W₂)
      ∈ Matrix.unitaryGroup _ ℂ :=
  qPerm_mem_unitaryGroup _

lemma pairSwap₂Mat_mulVec_apply
    (ψ : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂) → ℂ) (p) :
    (pairSwap₂Mat *ᵥ ψ) p = ψ (pairSwap₂Map p) := by
  rw [pairSwap₂Mat, qPerm_mulVec_apply]
  rfl

/-! ## Product states -/

/-- The banked product state: `χ` on the global registers, `ψⱼ` in bank
`j`. -/
def prodState (χ : Option ι × Option σ → ℂ) (ψ₁ : QBasis ι σ W₁ → ℂ)
    (ψ₂ : QBasis ι σ W₂ → ℂ) :
    QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂) → ℂ :=
  fun p => χ (p.1, p.2.1) * ψ₁ p.2.2.1 * ψ₂ p.2.2.2

/-- Blank global registers. -/
def blankReg : Option ι × Option σ → ℂ :=
  fun q => if q = (none, none) then 1 else 0

lemma sum_normSq_blankReg :
    (∑ q : Option ι × Option σ, Complex.normSq (blankReg q)) = 1 := by
  rw [Finset.sum_eq_single ((none, none) : Option ι × Option σ)]
  · simp [blankReg]
  · intro q _ hq
    simp [blankReg, hq]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [DecidableEq W₁] [DecidableEq W₂] [DecidableEq ι] [DecidableEq σ] in
/-- The double-sum factorization used twice below. -/
private lemma sum_sum_factor (C : ℝ) (F : QBasis ι σ W₁ → ℝ)
    (G : QBasis ι σ W₂ → ℝ) :
    (∑ β₁, ∑ β₂, C * (F β₁ * G β₂))
      = C * (∑ β₁, F β₁) * ∑ β₂, G β₂ := by
  have hinner : ∀ β₁, (∑ β₂, C * (F β₁ * G β₂))
      = (C * F β₁) * ∑ β₂, G β₂ := by
    intro β₁
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun β₂ _ => by ring
  rw [Finset.sum_congr rfl fun β₁ _ => hinner β₁, ← Finset.sum_mul,
    ← Finset.mul_sum]

omit [DecidableEq W₁] [DecidableEq W₂] [DecidableEq ι] [DecidableEq σ] in
lemma qNormSq_prodState (χ : Option ι × Option σ → ℂ)
    (ψ₁ : QBasis ι σ W₁ → ℂ) (ψ₂ : QBasis ι σ W₂ → ℂ) :
    qNormSq (prodState χ ψ₁ ψ₂)
      = (∑ q, Complex.normSq (χ q)) * qNormSq ψ₁ * qNormSq ψ₂ := by
  classical
  rw [qNormSq_def, qNormSq_def, qNormSq_def]
  rw [show (∑ p : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂),
        Complex.normSq (prodState χ ψ₁ ψ₂ p))
      = ∑ i : Option ι, ∑ a : Option σ, ∑ β₁ : QBasis ι σ W₁,
          ∑ β₂ : QBasis ι σ W₂,
          Complex.normSq (χ (i, a)) * (Complex.normSq (ψ₁ β₁)
            * Complex.normSq (ψ₂ β₂)) from by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun β₁ _ => Finset.sum_congr rfl fun β₂ _ => ?_
    rw [prodState, Complex.normSq_mul, Complex.normSq_mul]
    ring]
  rw [Fintype.sum_prod_type, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact sum_sum_factor _ _ _

omit [DecidableEq W₁] [DecidableEq W₂] in
lemma isQState_prodState {ψ₁ : QBasis ι σ W₁ → ℂ} {ψ₂ : QBasis ι σ W₂ → ℂ}
    (h₁ : IsQState ψ₁) (h₂ : IsQState ψ₂) :
    IsQState (prodState blankReg ψ₁ ψ₂) := by
  classical
  rw [IsQState, qNormSq_prodState, sum_normSq_blankReg, h₁, h₂]
  norm_num

/-! ## The phase actions -/

lemma pairSwap₁_mulVec_prodState (χ : Option ι × Option σ → ℂ)
    (ψ₁ : QBasis ι σ W₁ → ℂ) (ψ₂ : QBasis ι σ W₂ → ℂ) :
    pairSwap₁Mat *ᵥ prodState χ ψ₁ ψ₂
      = splitVec pairEquiv₁ ψ₁ (fun q => χ q.1 * ψ₂ q.2) := by
  funext p
  rw [pairSwap₁Mat_mulVec_apply]
  obtain ⟨idx, ans, ⟨⟨i₁, a₁, w₁⟩, β₂⟩⟩ := p
  change χ (i₁, a₁) * ψ₁ (idx, ans, w₁) * ψ₂ β₂
    = ψ₁ (idx, ans, w₁) * (χ (i₁, a₁) * ψ₂ β₂)
  ring

lemma pairSwap₁_mulVec_splitVec (χ : Option ι × Option σ → ℂ)
    (ψ₁ : QBasis ι σ W₁ → ℂ) (ψ₂ : QBasis ι σ W₂ → ℂ) :
    pairSwap₁Mat *ᵥ splitVec pairEquiv₁ ψ₁ (fun q => χ q.1 * ψ₂ q.2)
      = prodState χ ψ₁ ψ₂ := by
  funext p
  rw [pairSwap₁Mat_mulVec_apply]
  obtain ⟨idx, ans, ⟨⟨i₁, a₁, w₁⟩, β₂⟩⟩ := p
  change ψ₁ (i₁, a₁, w₁) * (χ (idx, ans) * ψ₂ β₂)
    = χ (idx, ans) * ψ₁ (i₁, a₁, w₁) * ψ₂ β₂
  ring

lemma pairSwap₂_mulVec_prodState (χ : Option ι × Option σ → ℂ)
    (ψ₁ : QBasis ι σ W₁ → ℂ) (ψ₂ : QBasis ι σ W₂ → ℂ) :
    pairSwap₂Mat *ᵥ prodState χ ψ₁ ψ₂
      = splitVec pairEquiv₂ ψ₂ (fun q => χ q.1 * ψ₁ q.2) := by
  funext p
  rw [pairSwap₂Mat_mulVec_apply]
  obtain ⟨idx, ans, ⟨β₁, ⟨i₂, a₂, w₂⟩⟩⟩ := p
  change χ (i₂, a₂) * ψ₁ β₁ * ψ₂ (idx, ans, w₂)
    = ψ₂ (idx, ans, w₂) * (χ (i₂, a₂) * ψ₁ β₁)
  ring

lemma pairSwap₂_mulVec_splitVec (χ : Option ι × Option σ → ℂ)
    (ψ₁ : QBasis ι σ W₁ → ℂ) (ψ₂ : QBasis ι σ W₂ → ℂ) :
    pairSwap₂Mat *ᵥ splitVec pairEquiv₂ ψ₂ (fun q => χ q.1 * ψ₁ q.2)
      = prodState χ ψ₁ ψ₂ := by
  funext p
  rw [pairSwap₂Mat_mulVec_apply]
  obtain ⟨idx, ans, ⟨β₁, ⟨i₂, a₂, w₂⟩⟩⟩ := p
  change ψ₂ (i₂, a₂, w₂) * (χ (idx, ans) * ψ₁ β₁)
    = χ (idx, ans) * ψ₁ β₁ * ψ₂ (i₂, a₂, w₂)
  ring

/-! ## The compiled routine -/

/-- **The pair compiler**: swap in bank 1, run schedule 1 lifted, swap out;
swap in bank 2, run schedule 2 lifted, swap out.  `R₁.len + R₂.len`
queries. -/
def pairRoutine (R₁ : QRoutine ι σ W₁) (R₂ : QRoutine ι σ W₂) :
    QRoutine ι σ (QBasis ι σ W₁ × QBasis ι σ W₂) :=
  (QRoutine.ofUnitary pairSwap₁Mat pairSwap₁Mat_mem_unitaryGroup).comp
    ((R₁.kronLift pairEquiv₁).comp
      ((QRoutine.ofUnitary pairSwap₁Mat pairSwap₁Mat_mem_unitaryGroup).comp
        ((QRoutine.ofUnitary pairSwap₂Mat pairSwap₂Mat_mem_unitaryGroup).comp
          ((R₂.kronLift pairEquiv₂).comp
            (QRoutine.ofUnitary pairSwap₂Mat
              pairSwap₂Mat_mem_unitaryGroup)))))

@[simp] lemma pairRoutine_len (R₁ : QRoutine ι σ W₁) (R₂ : QRoutine ι σ W₂) :
    (pairRoutine R₁ R₂).len = R₁.len + R₂.len := by
  change 0 + (R₁.len + (0 + (0 + (R₂.len + 0)))) = R₁.len + R₂.len
  omega

/-- **The compiled run is the product of the runs.** -/
theorem pairRoutine_run_prodState (R₁ : QRoutine ι σ W₁)
    (R₂ : QRoutine ι σ W₂) (a : ι → σ) (χ : Option ι × Option σ → ℂ)
    (ψ₁ : QBasis ι σ W₁ → ℂ) (ψ₂ : QBasis ι σ W₂ → ℂ) :
    (pairRoutine R₁ R₂).run a *ᵥ prodState χ ψ₁ ψ₂
      = prodState χ (R₁.run a *ᵥ ψ₁) (R₂.run a *ᵥ ψ₂) := by
  have hrun : (pairRoutine R₁ R₂).run a
      = pairSwap₂Mat * ((R₂.kronLift pairEquiv₂).run a * (pairSwap₂Mat
          * (pairSwap₁Mat * ((R₁.kronLift pairEquiv₁).run a
            * pairSwap₁Mat)))) := by
    rw [pairRoutine, QRoutine.comp_run, QRoutine.comp_run, QRoutine.comp_run,
      QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run,
      QRoutine.ofUnitary_run]
    noncomm_ring
  rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    pairSwap₁_mulVec_prodState]
  rw [show (R₁.kronLift pairEquiv₁).run a
      = (R₁.kronLift pairEquiv₁).runUpto a R₁.len from rfl,
    QRoutine.kronLift_runUpto_splitVec oracleCompat_pairEquiv₁,
    show R₁.runUpto a R₁.len = R₁.run a from rfl,
    pairSwap₁_mulVec_splitVec, pairSwap₂_mulVec_prodState]
  rw [show (R₂.kronLift pairEquiv₂).run a
      = (R₂.kronLift pairEquiv₂).runUpto a R₂.len from rfl,
    QRoutine.kronLift_runUpto_splitVec oracleCompat_pairEquiv₂,
    show R₂.runUpto a R₂.len = R₂.run a from rfl,
    pairSwap₂_mulVec_splitVec]

/-! ## The joint measurement factorizes -/

variable {O₁ O₂ : Type} [DecidableEq O₁] [DecidableEq O₂]

/-- Read both banks. -/
def pairReadout (r₁ : QBasis ι σ W₁ → O₁) (r₂ : QBasis ι σ W₂ → O₂) :
    QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂) → O₁ × O₂ :=
  fun p => (r₁ p.2.2.1, r₂ p.2.2.2)

omit [DecidableEq W₁] [DecidableEq W₂] [DecidableEq ι] [DecidableEq σ] in
theorem qProb_pairReadout (r₁ : QBasis ι σ W₁ → O₁) (r₂ : QBasis ι σ W₂ → O₂)
    (χ : Option ι × Option σ → ℂ) (ψ₁ : QBasis ι σ W₁ → ℂ)
    (ψ₂ : QBasis ι σ W₂ → ℂ) (o₁ : O₁) (o₂ : O₂) :
    qProb (pairReadout r₁ r₂) (prodState χ ψ₁ ψ₂) (o₁, o₂)
      = (∑ q, Complex.normSq (χ q)) * qProb r₁ ψ₁ o₁ * qProb r₂ ψ₂ o₂ := by
  classical
  rw [qProb, qProb, qProb]
  rw [show (∑ p : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂),
        if pairReadout r₁ r₂ p = (o₁, o₂) then
          Complex.normSq (prodState χ ψ₁ ψ₂ p) else 0)
      = ∑ i : Option ι, ∑ a : Option σ, ∑ β₁ : QBasis ι σ W₁,
          ∑ β₂ : QBasis ι σ W₂,
          Complex.normSq (χ (i, a))
            * ((if r₁ β₁ = o₁ then Complex.normSq (ψ₁ β₁) else 0)
              * (if r₂ β₂ = o₂ then Complex.normSq (ψ₂ β₂) else 0)) from by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun β₁ _ => Finset.sum_congr rfl fun β₂ _ => ?_
    rw [show pairReadout r₁ r₂ ((i, a, (β₁, β₂))
        : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)) = (r₁ β₁, r₂ β₂)
      from rfl]
    rw [show prodState χ ψ₁ ψ₂ ((i, a, (β₁, β₂))
        : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂))
        = χ (i, a) * ψ₁ β₁ * ψ₂ β₂ from rfl]
    by_cases h1 : r₁ β₁ = o₁ <;> by_cases h2 : r₂ β₂ = o₂ <;>
      simp [h1, h2, Prod.ext_iff, Complex.normSq_mul]; ring]
  rw [Fintype.sum_prod_type, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact sum_sum_factor _ _ _

/-! ## `Realizes`, and the product-run calculus -/

section Realizes

variable {X : Type} [Fintype X] {O O' : Type} [DecidableEq O] [DecidableEq O']

/-- Some algorithm has outcome distribution `P` after `q` queries. -/
@[expose]
def Realizes (read : X → ι → σ) (q : ℕ) (P : X → O → ℝ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
    ∀ x o, A.prob (read x) q o = P x o

omit [Fintype X] in
lemma Realizes.congr {read : X → ι → σ} {q : ℕ} {P Q : X → O → ℝ}
    (h : Realizes read q P) (hPQ : ∀ x o, P x o = Q x o) :
    Realizes read q Q := by
  obtain ⟨W, hW, hW', A, hA⟩ := h
  exact ⟨W, hW, hW', A, fun x o => (hA x o).trans (hPQ x o)⟩

omit [Fintype X] in
/-- Every distribution an algorithm realizes is one the model measures:
values are probabilities of the final state. -/
lemma Realizes.nonneg {read : X → ι → σ} {q : ℕ} {P : X → O → ℝ}
    (h : Realizes read q P) (x : X) (o : O) : 0 ≤ P x o := by
  obtain ⟨W, hW, hW', A, hA⟩ := h
  rw [← hA x o]
  exact A.prob_nonneg _ _ _

omit [Fintype X] in
/-- **The pair compiler, packaged**: two realizable distributions have a
jointly realizable product, at the sum of the costs. -/
theorem Realizes.pair {read : X → ι → σ} {q₁ q₂ : ℕ} {P₁ : X → O → ℝ}
    {P₂ : X → O' → ℝ} (h₁ : Realizes read q₁ P₁) (h₂ : Realizes read q₂ P₂) :
    Realizes read (q₁ + q₂)
      (fun x o => P₁ x o.1 * P₂ x o.2 : X → O × O' → ℝ) := by
  classical
  obtain ⟨V₁, _, _, A₁, hA₁⟩ := h₁
  obtain ⟨V₂, _, _, A₂, hA₂⟩ := h₂
  refine ⟨QBasis ι σ V₁ × QBasis ι σ V₂, inferInstance, inferInstance,
    (pairRoutine (QRoutine.mk q₁ A₁.step A₁.step_unitary)
        (QRoutine.mk q₂ A₂.step A₂.step_unitary)).toAlg
      (prodState blankReg A₁.init A₂.init)
      (isQState_prodState A₁.init_isQState A₂.init_isQState)
      (pairReadout A₁.readout A₂.readout), ?_⟩
  intro x o
  obtain ⟨o₁, o₂⟩ := o
  have hlen : (pairRoutine (QRoutine.mk q₁ A₁.step A₁.step_unitary)
      (QRoutine.mk q₂ A₂.step A₂.step_unitary)).len = q₁ + q₂ := by
    rw [pairRoutine_len]
  have hstate : ((pairRoutine (QRoutine.mk q₁ A₁.step A₁.step_unitary)
        (QRoutine.mk q₂ A₂.step A₂.step_unitary)).toAlg
      (prodState blankReg A₁.init A₂.init)
      (isQState_prodState A₁.init_isQState A₂.init_isQState)
      (pairReadout A₁.readout A₂.readout)).state (read x) (q₁ + q₂)
      = prodState blankReg (A₁.state (read x) q₁) (A₂.state (read x) q₂) := by
    rw [← hlen, QRoutine.toAlg_state_len, pairRoutine_run_prodState]
    rw [show (QRoutine.mk q₁ A₁.step A₁.step_unitary).run (read x)
        = (QRoutine.mk q₁ A₁.step A₁.step_unitary).runUpto (read x) q₁
      from rfl, ← state_eq_runUpto2 A₁ q₁]
    rw [show (QRoutine.mk q₂ A₂.step A₂.step_unitary).run (read x)
        = (QRoutine.mk q₂ A₂.step A₂.step_unitary).runUpto (read x) q₂
      from rfl, ← state_eq_runUpto2 A₂ q₂]
  rw [QAlg.prob, hstate]
  rw [show ((pairRoutine (QRoutine.mk q₁ A₁.step A₁.step_unitary)
        (QRoutine.mk q₂ A₂.step A₂.step_unitary)).toAlg
      (prodState blankReg A₁.init A₂.init)
      (isQState_prodState A₁.init_isQState A₂.init_isQState)
      (pairReadout A₁.readout A₂.readout)).readout
      = pairReadout A₁.readout A₂.readout from rfl]
  rw [qProb_pairReadout, sum_normSq_blankReg, one_mul]
  rw [show qProb A₁.readout (A₁.state (read x) q₁) o₁
      = A₁.prob (read x) q₁ o₁ from rfl,
    show qProb A₂.readout (A₂.state (read x) q₂) o₂
      = A₂.prob (read x) q₂ o₂ from rfl, hA₁, hA₂]

omit [Fintype X] in
/-- Reshaping the outcome through the readout is free. -/
theorem Realizes.map [Fintype O] {read : X → ι → σ} {q : ℕ} {P : X → O → ℝ}
    (h : Realizes read q P) (g : O → O') :
    Realizes read q (fun x o' =>
      ∑ o ∈ Finset.univ.filter (fun o => g o = o'), P x o) := by
  obtain ⟨W, hW, hW', A, hA⟩ := h
  refine ⟨W, hW, hW',
    (QRoutine.mk q A.step A.step_unitary).toAlg A.init A.init_isQState
      (fun p => g (A.readout p)), ?_⟩
  intro x o
  rw [QAlg.prob,
    show ((QRoutine.mk q A.step A.step_unitary).toAlg A.init A.init_isQState
        (fun p => g (A.readout p))).readout
      = fun p => g (A.readout p) from rfl,
    show ((QRoutine.mk q A.step A.step_unitary).toAlg A.init A.init_isQState
        (fun p => g (A.readout p))).state (read x) q
      = (QRoutine.mk q A.step A.step_unitary).runUpto (read x) q *ᵥ A.init
      from QRoutine.toAlg_state _ _ _ _ _ q,
    ← state_eq_runUpto2 A q]
  rw [qProb]
  rw [show (∑ h, if g (A.readout h) = o then
        Complex.normSq (A.state (read x) q h) else 0)
      = ∑ h, ∑ b ∈ Finset.univ.filter (fun b => g b = o),
          if A.readout h = b then
            Complex.normSq (A.state (read x) q h) else 0 from by
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_filter]
    rw [Finset.sum_eq_single (A.readout h)]
    · by_cases hg : g (A.readout h) = o <;> simp [hg]
    · intro b _ hb
      by_cases hg : g b = o <;> simp [hg, Ne.symm hb]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← hA x b, QAlg.prob, qProb]

omit [Fintype X] in
/-- The bijective special case: relabel the outcomes. -/
theorem Realizes.map_equiv {read : X → ι → σ} {q : ℕ}
    {P : X → O → ℝ} (h : Realizes read q P) (g : O ≃ O') :
    Realizes read q (fun x o' => P x (g.symm o')) := by
  obtain ⟨W, hW, hW', A, hA⟩ := h
  refine ⟨W, hW, hW', A.postcomp g, ?_⟩
  intro x o
  change (A.postcomp g).prob (read x) q o = P x (g.symm o)
  rw [← hA x (g.symm o)]
  simp only [QAlg.prob, QAlg.postcomp_state, QAlg.postcomp_readout, qProb]
  exact Finset.sum_congr rfl fun h _ => if_congr g.eq_symm_apply.symm rfl rfl


end Realizes

end QuantumQueryComplexity

end SourceQuantumProductRun

section SourceQuantumXorOracle

/-!
# The standard Boolean XOR oracle, and its query model

The conventional oracle for Boolean inputs: on the answer register,

  `|i⟩|b⟩|w⟩ ↦ |i⟩|b ⊕ a i⟩|w⟩`,

with an **idle index** (`none`, no query) and a fixed blank answer — on this
model's basis `QBasis ι Bool W` the answer register is `Option Bool`, the XOR
acts on the `some`-part, and both `none` sectors are fixed.  Boolean
specifically: for an arbitrary alphabet there is no canonical XOR directly
on `σ` without choosing a group structure, so the simulation theorems start
here.  The upstream construction (`upstream OneHot.lean`) instead XORs an *encoding* of the letter
— its one-hot code in `Hot σ := σ → Bool` — which needs no structure on `σ`.

Like the transposition oracle it is a basis permutation and an involution, so
unitarity and query = unquery are free.

The model: `QAlg` is oracle-agnostic data (initial state, steps, readout);
only the *state semantics* names the oracle.  `xorState` is `QAlg.state` with
`xorOracleMat` in place of `oracleMat`, and `XorComputesWithErrorOn`,
`XorQueryCounts`, `xorQQueryOn` mirror the standard model's definitions
verbatim.  `SourceQuantumSimulation` proves the two models equivalent within a factor
of two in the query count.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

/-! ## The XOR on an optional Boolean -/

/-- XOR the `some`-part of `s` into the `some`-part of `t`; blank on either
side leaves `t` alone. -/
@[expose]
def optXor : Option Bool → Option Bool → Option Bool
  | some b, some c => some (xor b c)
  | t, _ => t

@[simp] lemma optXor_some_some (b c : Bool) :
    optXor (some b) (some c) = some (xor b c) := rfl

@[simp] lemma optXor_none (s : Option Bool) : optXor none s = none := by
  cases s <;> rfl

@[simp] lemma optXor_blank (t : Option Bool) : optXor t none = t := by
  cases t <;> rfl

lemma optXor_optXor (t s : Option Bool) : optXor (optXor t s) s = t := by
  cases t <;> cases s <;> simp [optXor]

/-! ## The oracle -/

variable {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

/-- The XOR oracle's action on the computational basis. -/
@[expose]
def xorOracleMap (a : ι → Bool) : QBasis ι Bool W → QBasis ι Bool W
  | (none, t, w) => (none, t, w)
  | (some i, t, w) => (some i, optXor t (some (a i)), w)

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
@[simp] lemma xorOracleMap_none (a : ι → Bool) (t : Option Bool) (w : W) :
    xorOracleMap a ((none, t, w) : QBasis ι Bool W) = (none, t, w) := rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
/-- **The XOR oracle reads the input only at the queried index.** -/
@[simp] lemma xorOracleMap_some (a : ι → Bool) (i : ι) (t : Option Bool)
    (w : W) : xorOracleMap a ((some i, t, w) : QBasis ι Bool W)
      = (some i, optXor t (some (a i)), w) := rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
/-- The blank answer is fixed: the XOR oracle, too, has an idle answer. -/
lemma xorOracleMap_blank (a : ι → Bool) (i : ι) (w : W) :
    xorOracleMap a ((some i, none, w) : QBasis ι Bool W)
      = (some i, none, w) := rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
lemma xorOracleMap_involutive (a : ι → Bool) :
    Function.Involutive (xorOracleMap (W := W) a) := by
  rintro ⟨(_ | i), t, w⟩
  · rfl
  · simp [optXor_optXor]

/-- The XOR oracle as a permutation of the basis. -/
@[expose]
def xorOraclePerm (a : ι → Bool) : Equiv.Perm (QBasis ι Bool W) :=
  Function.Involutive.toPerm _ (xorOracleMap_involutive a)

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
@[simp] lemma xorOraclePerm_apply (a : ι → Bool) (p : QBasis ι Bool W) :
    xorOraclePerm a p = xorOracleMap a p := rfl

/-- **The XOR oracle unitary.** -/
def xorOracleMat (a : ι → Bool) :
    Matrix (QBasis ι Bool W) (QBasis ι Bool W) ℂ :=
  qPerm (xorOraclePerm a)

theorem xorOracleMat_mem_unitaryGroup (a : ι → Bool) :
    xorOracleMat (W := W) a ∈ Matrix.unitaryGroup (QBasis ι Bool W) ℂ :=
  qPerm_mem_unitaryGroup _

/-- **Query = unquery**, here too. -/
theorem xorOracleMat_mul_self (a : ι → Bool) :
    xorOracleMat (W := W) a * xorOracleMat a = 1 :=
  qPerm_mul_self_of_involutive (xorOracleMap_involutive a)

lemma xorOracleMat_mulVec_apply (a : ι → Bool) (ψ : QBasis ι Bool W → ℂ)
    (p : QBasis ι Bool W) :
    (xorOracleMat a *ᵥ ψ) p = ψ (xorOracleMap a p) := by
  rw [xorOracleMat, qPerm_mulVec_apply]
  rfl

/-! ## The XOR query model

`QAlg` carries no oracle; the state semantics does.  These definitions mirror
`QAlg.state`, `ComputesWithErrorOn`, `QueryCounts`, and `qQueryOn` with the
XOR oracle substituted. -/

variable {O : Type} [DecidableEq O]
variable {X : Type} [Fintype X]

/-- **The state of `A` on input `a` after `t` XOR queries.** -/
@[expose]
def xorState (A : QAlg ι Bool O W) (a : ι → Bool) :
    ℕ → (QBasis ι Bool W → ℂ)
  | 0 => A.step 0 *ᵥ A.init
  | t + 1 => A.step (t + 1) *ᵥ (xorOracleMat a *ᵥ xorState A a t)

omit [DecidableEq O] in
@[simp] lemma xorState_zero (A : QAlg ι Bool O W) (a : ι → Bool) :
    xorState A a 0 = A.step 0 *ᵥ A.init := rfl

omit [DecidableEq O] in
@[simp] lemma xorState_succ (A : QAlg ι Bool O W) (a : ι → Bool) (t : ℕ) :
    xorState A a (t + 1)
      = A.step (t + 1) *ᵥ (xorOracleMat a *ᵥ xorState A a t) := rfl

omit [DecidableEq O] in
theorem xorState_isQState (A : QAlg ι Bool O W) (a : ι → Bool) (t : ℕ) :
    IsQState (xorState A a t) := by
  classical
  induction t with
  | zero => exact IsQState.mulVec (A.step_unitary 0) A.init_isQState
  | succ t ih =>
      rw [xorState_succ]
      exact IsQState.mulVec (A.step_unitary (t + 1))
        (IsQState.mulVec (xorOracleMat_mem_unitaryGroup a) ih)

omit [DecidableEq O] in
/-- **The bridge to the parametric run**: the XOR state is `runWith` of the
algorithm's step schedule, packaged with any length. -/
lemma xorState_eq_runWith (A : QAlg ι Bool O W) (n : ℕ) (a : ι → Bool)
    (t : ℕ) : xorState A a t
      = (QRoutine.mk n A.step A.step_unitary).runWith (xorOracleMat a) t
          *ᵥ A.init := by
  classical
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [xorState_succ, ih, QRoutine.runWith_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- `A` computes `f` on the promise `read` with error at most `ε` in `q`
**XOR queries**. -/
@[expose]
def XorComputesWithErrorOn (A : QAlg ι Bool O W) (q : ℕ)
    (read : X → ι → Bool) (f : X → O) (ε : ℝ) : Prop :=
  ∀ x : X, 1 - ε ≤ qProb A.readout (xorState A (read x) q) (f x)

/-- The achievable XOR-query counts. -/
def XorQueryCounts (read : X → ι → Bool) (f : X → O) (ε : ℝ) : Set ℕ :=
  {q | ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
    (A : QAlg ι Bool O W), XorComputesWithErrorOn A q read f ε}

/-- Quantum query complexity in the **XOR-oracle model**. -/
noncomputable def xorQQueryOn (read : X → ι → Bool) (f : X → O) (ε : ℝ) : ℕ :=
  sInf (XorQueryCounts read f ε)

omit [Fintype X] in
theorem mem_xorQueryCounts {read : X → ι → Bool} {f : X → O} {ε : ℝ} {q : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {A : QAlg ι Bool O W}
    (h : XorComputesWithErrorOn A q read f ε) :
    q ∈ XorQueryCounts read f ε :=
  ⟨W, inferInstance, inferInstance, A, h⟩

end QuantumQueryComplexity

end SourceQuantumXorOracle

section SourceQuantumAmplify

/-!
# Folding the pair compiler: tuples, majority, and joint correctness

The `k`-fold iteration of `Realizes.pair`, and its two consumers:

* **`amplify`** — majority over `k` independent runs of a Boolean algorithm.
  The record statistics are an exact product, so the failure probability is
  the pattern count `sum_prod_majority_le`: at per-run error `ε` the
  amplified error is `2^k·ε^{⌈k/2⌉}`; at the native `ε = 1/16` this is
  `≤ 2^{-k}`.
* **`exists_tuple_computes`** — `B` Boolean algorithms joined into one
  computing the tuple, with error `∑ εᵢ` (the product of the diagonal
  probabilities, bounded by Weierstrass).

Costs add exactly throughout — the bank-swap compiler has no uncompute
overhead.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X]

section GeneralRecords
variable {O : Type} [DecidableEq O]
omit [Fintype X]

/-! ## The `k`-fold product realization over any decidable output type -/

/-- Prepending a coordinate to a record. -/
def consEquiv (O : Type) (k : ℕ) : O × (Fin k → O) ≃ (Fin (k + 1) → O) where
  toFun p := Fin.cons p.1 p.2
  invFun y := (y 0, fun j => y j.succ)
  left_inv := by
    rintro ⟨b, t⟩
    refine Prod.ext (by simp) (funext fun j => ?_)
    simp
  right_inv := by
    intro y
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp


/-- The trivial realization: no runs, the constant distribution `1` on the
empty record. -/
lemma realizes_zero_rec (read : X → ι → σ) :
    Realizes read 0 (fun (_ : X) (_ : Fin 0 → O) => (1 : ℝ)) := by
  classical
  refine ⟨Unit, inferInstance, inferInstance,
    constAlg ι σ (fun j : Fin 0 => j.elim0), ?_⟩
  intro x o
  have ho : o = fun j : Fin 0 => j.elim0 := funext fun j => j.elim0
  subst ho
  simp [QAlg.prob, constAlg]


/-- **The `k`-fold product realization over any decidable output type**: costs
add, distributions multiply. -/
theorem Realizes.foldRec {read : X → ι → σ} :
    ∀ (k : ℕ) (q : Fin k → ℕ) (P : Fin k → X → O → ℝ),
    (∀ j, Realizes read (q j) (P j)) →
    Realizes read (∑ j, q j)
      (fun x (y : Fin k → O) => ∏ j, P j x (y j)) := by
  classical
  intro k
  induction k with
  | zero =>
      intro q P _
      rw [show (∑ j : Fin 0, q j) = 0 from by simp]
      exact (realizes_zero_rec read).congr fun x y => by simp
  | succ k ih =>
      intro q P h
      have hfold := ih (fun j => q j.succ) (fun j => P j.succ)
        (fun j => h j.succ)
      have hpair := (h 0).pair hfold
      have hmapped := hpair.map_equiv (consEquiv O k)
      rw [Fin.sum_univ_succ]
      refine hmapped.congr fun x y => ?_
      rw [show (consEquiv O k).symm y = (y 0, fun j => y j.succ) from rfl]
      rw [Fin.prod_univ_succ]

end GeneralRecords

/-! ## The base and the cons step -/

/-- Prepending a coordinate to a Boolean tuple. -/
def finConsEquiv (k : ℕ) : Bool × (Fin k → Bool) ≃ (Fin (k + 1) → Bool) :=
  consEquiv Bool k

omit [Fintype X] in
/-- The trivial realization: no runs, the constant distribution `1` on the
empty tuple. -/
lemma realizes_zero_tuple (read : X → ι → σ) :
    Realizes read 0 (fun (_ : X) (_ : Fin 0 → Bool) => (1 : ℝ)) := realizes_zero_rec read

omit [Fintype X] in
/-- **The `k`-fold product realization**: costs add, distributions
multiply. -/
theorem Realizes.fold {read : X → ι → σ} :
    ∀ (k : ℕ) (q : Fin k → ℕ) (P : Fin k → X → Bool → ℝ),
    (∀ j, Realizes read (q j) (P j)) →
    Realizes read (∑ j, q j)
      (fun x (y : Fin k → Bool) => ∏ j, P j x (y j)) := Realizes.foldRec

/-- Probabilities sum to one. -/
lemma QAlg.sum_prob {O W : Type} [DecidableEq O] [Fintype O] [Fintype W]
    [DecidableEq W] (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) :
    ∑ o, A.prob a t o = 1 := by
  change (∑ o, qProb A.readout (A.state a t) o) = 1
  rw [sum_qProb, A.state_isQState]

/-- The full pattern sum of a product distribution is the product of the
totals. -/
lemma sum_pattern_prod {k : ℕ} (p : Bool → ℝ) :
    (∑ y : Fin k → Bool, ∏ j, p (y j)) = (∑ b, p b) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [← Equiv.sum_comp (finConsEquiv k)
        (fun y => ∏ j, p (y j)), Fintype.sum_prod_type]
      rw [show (∑ b, ∑ t : Fin k → Bool, ∏ j, p (finConsEquiv k (b, t) j))
          = ∑ b, ∑ t : Fin k → Bool, p b * ∏ j, p (t j) from by
        refine Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun t _ => ?_
        rw [show (finConsEquiv k (b, t)) = Fin.cons b t from rfl,
          Fin.prod_univ_succ]
        simp]
      rw [show (∑ b, ∑ t : Fin k → Bool, p b * ∏ j, p (t j))
          = ∑ b, p b * ∑ t : Fin k → Bool, ∏ j, p (t j) from
        Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]]
      rw [← Finset.sum_mul, ih, pow_succ]
      ring

/-! ## Majority amplification -/

/-- The majority vote. -/
def majVote (k : ℕ) (y : Fin k → Bool) : Bool :=
  decide (k < 2 * (Finset.univ.filter (fun j => y j = true)).card)

/-- A wrong majority has at least `⌈k/2⌉` wrong votes. -/
lemma le_card_wrong_of_majVote_ne {k : ℕ} {y : Fin k → Bool} {b : Bool}
    (h : majVote k y ≠ b) :
    (k + 1) / 2 ≤ (Finset.univ.filter (fun j => y j ≠ b)).card := by
  have hsplit : (Finset.univ.filter (fun j => y j = true)).card
      + (Finset.univ.filter (fun j => ¬(y j = true))).card = k := by
    rw [Finset.card_filter_add_card_filter_not (fun j => y j = true),
      Finset.card_univ, Fintype.card_fin]
  cases b with
  | true =>
      have hmaj : ¬(k < 2 * (Finset.univ.filter
          (fun j => y j = true)).card) := by
        intro hcon
        exact h (by simp [majVote, hcon])
      have hwrong : (Finset.univ.filter (fun j => y j ≠ true)).card
          = (Finset.univ.filter (fun j => ¬(y j = true))).card := rfl
      rw [hwrong]
      omega
  | false =>
      have hmaj : k < 2 * (Finset.univ.filter
          (fun j => y j = true)).card := by
        by_contra hcon
        exact h (by simp [majVote, hcon])
      have hwrong : (Finset.univ.filter (fun j => y j ≠ false)).card
          = (Finset.univ.filter (fun j => y j = true)).card := by
        congr 1
        ext j
        simp [Finset.mem_filter]
      rw [hwrong]
      omega

omit [Fintype X] in
/-- **Majority amplification.**  `k` independent runs of a Boolean algorithm
with error `ε ≤ 1` compute the same function with error `2^k·ε^{⌈k/2⌉}`, at
`k` times the cost. -/
theorem amplify {read : X → ι → σ} {f : X → Bool} {q : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hex : ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QAlg ι σ Bool W), ComputesWithErrorOn A q read f ε) (k : ℕ) :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W')
      (A' : QAlg ι σ Bool W'),
      ComputesWithErrorOn A' (k * q) read f
        (2 ^ k * ε ^ ((k + 1) / 2)) := by
  classical
  obtain ⟨W, hW, hW', A, hA⟩ := hex
  -- the base realization
  have hbase : Realizes read q (fun x b => A.prob (read x) q b) :=
    ⟨W, hW, hW', A, fun _ _ => rfl⟩
  have hfold := Realizes.fold k (fun _ => q)
    (fun _ x b => A.prob (read x) q b) (fun _ => hbase)
  have hcost : (∑ _j : Fin k, q) = k * q := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hcost] at hfold
  have hmaj := hfold.map (majVote k)
  obtain ⟨W', hW1, hW2, A', hA'⟩ := hmaj
  refine ⟨W', hW1, hW2, A', ?_⟩
  intro x
  rw [hA' x (f x)]
  -- the correct-majority mass is the total minus the wrong-majority mass
  have htotal : (∑ y : Fin k → Bool, ∏ _j : Fin k,
      A.prob (read x) q (y _j)) = 1 := by
    rw [show (∑ y : Fin k → Bool, ∏ j : Fin k, A.prob (read x) q (y j))
        = (∑ b, A.prob (read x) q b) ^ k from
      sum_pattern_prod (fun b => A.prob (read x) q b),
      A.sum_prob, one_pow]
  have hsplitsum : (∑ y ∈ Finset.univ.filter
        (fun y : Fin k → Bool => majVote k y = f x),
      ∏ j, A.prob (read x) q (y j))
      + (∑ y ∈ Finset.univ.filter
          (fun y : Fin k → Bool => ¬(majVote k y = f x)),
        ∏ j, A.prob (read x) q (y j)) = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact htotal
  -- the wrong-majority mass is small
  have hwrongmass : (∑ y ∈ Finset.univ.filter
        (fun y : Fin k → Bool => ¬(majVote k y = f x)),
      ∏ j, A.prob (read x) q (y j))
      ≤ 2 ^ k * ε ^ ((k + 1) / 2) := by
    have hsub : Finset.univ.filter
        (fun y : Fin k → Bool => ¬(majVote k y = f x))
        ⊆ Finset.univ.filter (fun y : Fin k → Bool =>
          (k + 1) / 2 ≤ (Finset.univ.filter (fun j => y j ≠ f x)).card) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact le_card_wrong_of_majVote_ne hy
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun y _ _ => Finset.prod_nonneg fun j _ => A.prob_nonneg _ _ _) ?_
    refine sum_prod_majority_le hε0 hε1 (fun _ b => A.prob (read x) q b)
      (fun _ => f x) (fun _ b => A.prob_nonneg _ _ _)
      (fun _ b => A.prob_le_one _ _ _) fun _ => ?_
    -- the wrong value's probability is at most `ε`
    have hsum2 : A.prob (read x) q (f x)
        + A.prob (read x) q (!(f x)) = 1 := by
      have := A.sum_prob (read x) q
      rw [Fintype.sum_bool] at this
      cases hfx : f x <;> simp at this ⊢ <;> linarith
    have := hA x
    linarith
  linarith [hsplitsum, hwrongmass]

/-! ## Joining Boolean algorithms into a tuple -/

/-- Weierstrass: the product of near-one probabilities is near one. -/
lemma one_sub_sum_le_prod {k : ℕ} (p e : Fin k → ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (he0 : ∀ j, 0 ≤ e j)
    (h : ∀ j, 1 - e j ≤ p j) :
    1 - (∑ j, e j) ≤ ∏ j, p j := by
  induction k with
  | zero => simp
  | succ k ih =>
      have htail := ih (fun j => p j.succ) (fun j => e j.succ)
        (fun j => hp0 j.succ) (fun j => hp1 j.succ) (fun j => he0 j.succ)
        (fun j => h j.succ)
      have hS0 : (0 : ℝ) ≤ ∑ j : Fin k, e j.succ :=
        Finset.sum_nonneg fun j _ => he0 j.succ
      have hT0 : (0 : ℝ) ≤ ∏ j : Fin k, p j.succ :=
        Finset.prod_nonneg fun j _ => hp0 j.succ
      rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
      rcases le_or_gt (1 - ∑ j : Fin k, e j.succ) 0 with hneg | hpos
      · have h1 : 1 - (e 0 + ∑ j : Fin k, e j.succ) ≤ 0 := by
          linarith [he0 0]
        exact le_trans h1 (mul_nonneg (hp0 0) hT0)
      · have h1 : p 0 * (1 - ∑ j : Fin k, e j.succ)
            ≤ p 0 * ∏ j : Fin k, p j.succ :=
          mul_le_mul_of_nonneg_left htail (hp0 0)
        nlinarith [h 0, he0 0, hp1 0]

omit [Fintype X] in
/-- **The tuple compiler**: `B` Boolean algorithms joined into one computing
the tuple function, at the sum of the costs and the sum of the errors. -/
theorem exists_tuple_computes {read : X → ι → σ} {B : ℕ}
    {g : Fin B → X → Bool} {q : Fin B → ℕ} {ε : Fin B → ℝ}
    (hε0 : ∀ i, 0 ≤ ε i)
    (hex : ∀ i, ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QAlg ι σ Bool W), ComputesWithErrorOn A (q i) read (g i) (ε i)) :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W')
      (A' : QAlg ι σ (Fin B → Bool) W'),
      ComputesWithErrorOn A' (∑ i, q i) read (fun x i => g i x)
        (∑ i, ε i) := by
  classical
  choose W hW hW' A hA using hex
  have hbase : ∀ i, Realizes read (q i)
      (fun x b => (A i).prob (read x) (q i) b) := fun i =>
    ⟨W i, hW i, hW' i, A i, fun _ _ => rfl⟩
  have hfold := Realizes.fold B q
    (fun i x b => (A i).prob (read x) (q i) b) hbase
  obtain ⟨W', hW1, hW2, A', hA'⟩ := hfold
  refine ⟨W', hW1, hW2, A', ?_⟩
  intro x
  rw [hA' x (fun i => g i x)]
  refine le_trans ?_ (le_of_eq rfl)
  refine one_sub_sum_le_prod _ ε
    (fun i => (A i).prob_nonneg _ _ _)
    (fun i => (A i).prob_le_one _ _ _) hε0 fun i => hA i x

end QuantumQueryComplexity

end SourceQuantumAmplify

section SourceQuantumSimulation

/-!
# Oracle simulation: transposition ↔ XOR, at two queries per query

The model-equivalence theorem for Boolean input
alphabets.  Each direction is one **two-query gadget** on a clean-ancilla
encoded subspace (`embedReg` with an `Option Bool` ancilla register), compiled
over whole routines at exactly `2·R.len` queries, and exported as a
`QueryCounts` translation:

    q ∈ XorQueryCounts read f ε  →  2q ∈ QueryCounts read f ε
    q ∈ QueryCounts read f ε     →  2q ∈ XorQueryCounts read f ε

with the complexity inequalities

    qQueryOn read f ε ≤ 2 · xorQQueryOn read f ε
    xorQQueryOn read f ε ≤ 2 · qQueryOn read f ε.

**The gadgets.**  With ancilla `v`, answer `t`:

* transposition simulates XOR (`xorGadget`, clean value `⊥`):
  swap `t ↔ v`, query (`⊥ ↦ a i`), XOR the answer into the ancilla, unquery,
  swap back — `swap · O · xorInto · O · swap`;
* XOR simulates transposition (`transGadget`, clean value `some false`):
  swap, query (`some false ↦ some (a i)`), controlled-swap `⊥ ↔ some v` on
  the ancilla where `v` is the answer's value, unquery, swap back —
  `swap · Oˣ · ctrlSwap · Oˣ · swap`.

Both middle unitaries are input-independent basis permutations; the
controlled swap is additionally controlled on the index register being
active, which is what keeps the idle sector exactly fixed.  Off the clean
sector each gadget moves the ancilla away from the clean value, so the
encoded-subspace statements hold with no side condition.

The compilers are compositional (`QRoutine.comp` + `ofUnitary` of lifted
steps, exactly like `selectPowers`), with `comp_run` sequencing the standard
side and `comp_runWith`/`xorRun` (from `SourceQuantumRunWith`) the XOR side.

Boolean specifically: for an arbitrary alphabet there is no canonical XOR
directly on `σ` without choosing a group structure on `σ`; the transposition
oracle is the alphabet-free primitive, which is why it is this development's
native model.  The upstream construction (`upstream OneHotSimulation.lean`) handles arbitrary finite
alphabets by XORing the letter's one-hot *encoding* into a `Hot σ` register,
with the same two-queries-per-query gadget pattern as here.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

/-! ## The run in the XOR model, packaged -/

namespace QRoutine

/-- The operator implemented by `R` against the XOR oracle. -/
@[expose]
def xorRun (R : QRoutine ι Bool W) (a : ι → Bool) :
    Matrix (QBasis ι Bool W) (QBasis ι Bool W) ℂ :=
  R.runWith (xorOracleMat a) R.len

theorem comp_xorRun (R S : QRoutine ι Bool W) (a : ι → Bool) :
    (R.comp S).xorRun a = S.xorRun a * R.xorRun a :=
  comp_runWith_full (xorOracleMat a) R S

@[simp] lemma ofUnitary_xorRun (U : Matrix (QBasis ι Bool W) (QBasis ι Bool W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι Bool W) ℂ) (a : ι → Bool) :
    (ofUnitary U hU).xorRun a = U := rfl

end QRoutine

/-! ## The gadget permutations

All on `QBasis ι Bool (Option Bool × W)`: index, answer, ancilla,
workspace. -/

/-- Swap the answer register with the ancilla. -/
@[expose]
def swapAncMap : QBasis ι Bool (Option Bool × W) → QBasis ι Bool (Option Bool × W)
  | (idx, t, (v, w)) => (idx, v, (t, w))

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
@[simp] lemma swapAncMap_apply (idx : Option ι) (t v : Option Bool) (w : W) :
    swapAncMap ((idx, t, (v, w)) : QBasis ι Bool (Option Bool × W))
      = (idx, v, (t, w)) := rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
lemma swapAncMap_involutive :
    Function.Involutive (swapAncMap (ι := ι) (W := W)) := by
  rintro ⟨idx, t, v, w⟩
  rfl

/-- XOR the answer register's value into the ancilla. -/
@[expose]
def xorIntoMap : QBasis ι Bool (Option Bool × W) → QBasis ι Bool (Option Bool × W)
  | (idx, s, (t, w)) => (idx, s, (optXor t s, w))

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
@[simp] lemma xorIntoMap_apply (idx : Option ι) (s t : Option Bool) (w : W) :
    xorIntoMap ((idx, s, (t, w)) : QBasis ι Bool (Option Bool × W))
      = (idx, s, (optXor t s, w)) := rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
lemma xorIntoMap_involutive :
    Function.Involutive (xorIntoMap (ι := ι) (W := W)) := by
  rintro ⟨idx, s, t, w⟩
  simp [optXor_optXor]

/-- On an active index with answer `some v`: swap `⊥ ↔ some v` in the
ancilla.  Controlled on the index being active, so the idle sector is exactly
fixed. -/
@[expose]
def ctrlSwapMap : QBasis ι Bool (Option Bool × W) → QBasis ι Bool (Option Bool × W)
  | (some i, some v, (t, w)) => (some i, some v, (Equiv.swap none (some v) t, w))
  | p => p

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
@[simp] lemma ctrlSwapMap_active (i : ι) (v : Bool) (t : Option Bool) (w : W) :
    ctrlSwapMap ((some i, some v, (t, w)) : QBasis ι Bool (Option Bool × W))
      = (some i, some v, (Equiv.swap none (some v) t, w)) := rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
@[simp] lemma ctrlSwapMap_idle (s : Option Bool) (t : Option Bool) (w : W) :
    ctrlSwapMap ((none, s, (t, w)) : QBasis ι Bool (Option Bool × W))
      = (none, s, (t, w)) := by
  cases s <;> rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
@[simp] lemma ctrlSwapMap_blank (i : ι) (t : Option Bool) (w : W) :
    ctrlSwapMap ((some i, none, (t, w)) : QBasis ι Bool (Option Bool × W))
      = (some i, none, (t, w)) := rfl

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
lemma ctrlSwapMap_involutive :
    Function.Involutive (ctrlSwapMap (ι := ι) (W := W)) := by
  classical
  rintro ⟨(_ | i), (_ | v), t, w⟩ <;> simp

/-! ## The gadget unitaries -/

/-- The answer–ancilla swap. -/
def swapAncMat : Matrix (QBasis ι Bool (Option Bool × W))
    (QBasis ι Bool (Option Bool × W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ swapAncMap_involutive)

lemma swapAncMat_mem_unitaryGroup :
    swapAncMat (ι := ι) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι Bool (Option Bool × W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma swapAncMat_mulVec_apply (ψ : QBasis ι Bool (Option Bool × W) → ℂ)
    (p : QBasis ι Bool (Option Bool × W)) :
    (swapAncMat *ᵥ ψ) p = ψ (swapAncMap p) := by
  rw [swapAncMat, qPerm_mulVec_apply]
  rfl

/-- The XOR-into-the-ancilla unitary. -/
def xorIntoMat : Matrix (QBasis ι Bool (Option Bool × W))
    (QBasis ι Bool (Option Bool × W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ xorIntoMap_involutive)

lemma xorIntoMat_mem_unitaryGroup :
    xorIntoMat (ι := ι) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι Bool (Option Bool × W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma xorIntoMat_mulVec_apply (ψ : QBasis ι Bool (Option Bool × W) → ℂ)
    (p : QBasis ι Bool (Option Bool × W)) :
    (xorIntoMat *ᵥ ψ) p = ψ (xorIntoMap p) := by
  rw [xorIntoMat, qPerm_mulVec_apply]
  rfl

/-- The controlled-swap unitary. -/
def ctrlSwapMat : Matrix (QBasis ι Bool (Option Bool × W))
    (QBasis ι Bool (Option Bool × W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ ctrlSwapMap_involutive)

lemma ctrlSwapMat_mem_unitaryGroup :
    ctrlSwapMat (ι := ι) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι Bool (Option Bool × W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma ctrlSwapMat_mulVec_apply (ψ : QBasis ι Bool (Option Bool × W) → ℂ)
    (p : QBasis ι Bool (Option Bool × W)) :
    (ctrlSwapMat *ᵥ ψ) p = ψ (ctrlSwapMap p) := by
  rw [ctrlSwapMat, qPerm_mulVec_apply]
  rfl

/-! ## The two gadgets -/

/-- **Transposition simulates XOR**: two physical queries. -/
@[expose]
def xorGadget : QRoutine ι Bool (Option Bool × W) where
  len := 2
  step := fun t => if t = 1 then xorIntoMat else swapAncMat
  step_unitary := by
    intro t
    split_ifs
    · exact xorIntoMat_mem_unitaryGroup
    · exact swapAncMat_mem_unitaryGroup

@[simp] lemma xorGadget_len : (xorGadget (ι := ι) (W := W)).len = 2 := rfl

/-- **XOR simulates transposition**: two physical queries. -/
@[expose]
def transGadget : QRoutine ι Bool (Option Bool × W) where
  len := 2
  step := fun t => if t = 1 then ctrlSwapMat else swapAncMat
  step_unitary := by
    intro t
    split_ifs
    · exact ctrlSwapMat_mem_unitaryGroup
    · exact swapAncMat_mem_unitaryGroup

@[simp] lemma transGadget_len : (transGadget (ι := ι) (W := W)).len = 2 := rfl

/-- **The XOR gadget's action on the clean-ancilla sector** is exactly one
XOR query. -/
theorem xorGadget_run (a : ι → Bool) (ψ : QBasis ι Bool W → ℂ) :
    (xorGadget (ι := ι) (W := W)).run a *ᵥ embedReg none ψ
      = embedReg none (xorOracleMat a *ᵥ ψ) := by
  have hrun : (xorGadget (ι := ι) (W := W)).run a
      = swapAncMat * (oracleMat a * (xorIntoMat * (oracleMat a * swapAncMat))) :=
    rfl
  funext p
  rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    swapAncMat_mulVec_apply, oracleMat_mulVec_apply, xorIntoMat_mulVec_apply,
    oracleMat_mulVec_apply, swapAncMat_mulVec_apply]
  obtain ⟨idx, t, v, w⟩ := p
  rcases idx with _ | i
  · rcases v with _ | c <;>
      simp [embedReg_apply, xorOracleMat_mulVec_apply]
  · rcases v with _ | c
    · -- clean ancilla, active index: the simulated query
      cases hai : a i <;> rcases t with _ | tb <;>
        simp [hai, embedReg_apply, xorOracleMat_mulVec_apply,
          optXor]
    · -- dirty ancilla: the ancilla stays dirty, both sides vanish
      cases hai : a i <;> rcases c with _ | _ <;>
        simp [hai, embedReg_apply, Equiv.swap_apply_def, optXor]

/-- **The transposition gadget's action on the clean-ancilla sector** is
exactly one transposition query, under XOR semantics. -/
theorem transGadget_xorRun (a : ι → Bool) (ψ : QBasis ι Bool W → ℂ) :
    (transGadget (ι := ι) (W := W)).xorRun a *ᵥ embedReg (some false) ψ
      = embedReg (some false) (oracleMat a *ᵥ ψ) := by
  have hrun : (transGadget (ι := ι) (W := W)).xorRun a
      = swapAncMat * (xorOracleMat a
          * (ctrlSwapMat * (xorOracleMat a * swapAncMat))) := rfl
  funext p
  rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    swapAncMat_mulVec_apply, xorOracleMat_mulVec_apply,
    ctrlSwapMat_mulVec_apply, xorOracleMat_mulVec_apply,
    swapAncMat_mulVec_apply]
  obtain ⟨idx, t, v, w⟩ := p
  rcases idx with _ | i
  · rcases v with _ | c <;>
      simp [embedReg_apply, oracleMat_mulVec_apply]
  · rcases v with _ | c
    · -- blank ancilla: the XOR oracle fixes it, both sides vanish
      simp [embedReg_apply, optXor]
    · -- clean ancilla `some false`: the simulated transposition;
      -- dirty `some true`: stays dirty, both sides vanish
      cases hai : a i <;> rcases c with _ | _ <;>
        simp [hai, embedReg_apply, oracleMat_mulVec_apply,
          Equiv.swap_apply_def, optXor]

/-! ## The compilers -/

/-- Compile the first `t` XOR queries of a schedule into the transposition
model: lifted steps, one `xorGadget` per query. -/
def simXorUpto (R : QRoutine ι Bool W) : ℕ → QRoutine ι Bool (Option Bool × W)
  | 0 => QRoutine.ofUnitary (liftReg (Option Bool) (R.step 0))
      (liftReg_mem_unitaryGroup (R.step_unitary 0))
  | t + 1 => (simXorUpto R t).comp (xorGadget.comp
      (QRoutine.ofUnitary (liftReg (Option Bool) (R.step (t + 1)))
        (liftReg_mem_unitaryGroup (R.step_unitary (t + 1)))))

@[simp] lemma simXorUpto_len (R : QRoutine ι Bool W) (t : ℕ) :
    (simXorUpto R t).len = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change ((simXorUpto R t).comp _).len = _
      rw [QRoutine.comp_len, QRoutine.comp_len, ih, xorGadget_len,
        QRoutine.ofUnitary_len]
      omega

theorem simXorUpto_run (R : QRoutine ι Bool W) (a : ι → Bool) (t : ℕ)
    (ψ : QBasis ι Bool W → ℂ) :
    (simXorUpto R t).run a *ᵥ embedReg none ψ
      = embedReg none (R.runWith (xorOracleMat a) t *ᵥ ψ) := by
  induction t with
  | zero =>
      change (QRoutine.ofUnitary _ _).run a *ᵥ _ = _
      rw [QRoutine.ofUnitary_run, liftReg_mulVec_embed]
      rfl
  | succ t ih =>
      have hrun : (simXorUpto R (t + 1)).run a
          = liftReg (Option Bool) (R.step (t + 1))
              * (xorGadget.run a * (simXorUpto R t).run a) := by
        change ((simXorUpto R t).comp _).run a = _
        rw [QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run,
          Matrix.mul_assoc]
      rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        xorGadget_run, liftReg_mulVec_embed, QRoutine.runWith_succ,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- **The compiled XOR schedule**: `2·R.len` transposition queries. -/
def simXor (R : QRoutine ι Bool W) : QRoutine ι Bool (Option Bool × W) :=
  simXorUpto R R.len

@[simp] lemma simXor_len (R : QRoutine ι Bool W) :
    (simXor R).len = 2 * R.len := simXorUpto_len R R.len

theorem simXor_run (R : QRoutine ι Bool W) (a : ι → Bool)
    (ψ : QBasis ι Bool W → ℂ) :
    (simXor R).run a *ᵥ embedReg none ψ
      = embedReg none (R.runWith (xorOracleMat a) R.len *ᵥ ψ) :=
  simXorUpto_run R a R.len ψ

/-- Compile the first `t` transposition queries of a schedule into the XOR
model: lifted steps, one `transGadget` per query. -/
def simTransUpto (R : QRoutine ι Bool W) : ℕ → QRoutine ι Bool (Option Bool × W)
  | 0 => QRoutine.ofUnitary (liftReg (Option Bool) (R.step 0))
      (liftReg_mem_unitaryGroup (R.step_unitary 0))
  | t + 1 => (simTransUpto R t).comp (transGadget.comp
      (QRoutine.ofUnitary (liftReg (Option Bool) (R.step (t + 1)))
        (liftReg_mem_unitaryGroup (R.step_unitary (t + 1)))))

@[simp] lemma simTransUpto_len (R : QRoutine ι Bool W) (t : ℕ) :
    (simTransUpto R t).len = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change ((simTransUpto R t).comp _).len = _
      rw [QRoutine.comp_len, QRoutine.comp_len, ih, transGadget_len,
        QRoutine.ofUnitary_len]
      omega

theorem simTransUpto_xorRun (R : QRoutine ι Bool W) (a : ι → Bool) (t : ℕ)
    (ψ : QBasis ι Bool W → ℂ) :
    (simTransUpto R t).xorRun a *ᵥ embedReg (some false) ψ
      = embedReg (some false) (R.runUpto a t *ᵥ ψ) := by
  induction t with
  | zero =>
      change (QRoutine.ofUnitary _ _).xorRun a *ᵥ _ = _
      rw [QRoutine.ofUnitary_xorRun, liftReg_mulVec_embed]
      rfl
  | succ t ih =>
      have hrun : (simTransUpto R (t + 1)).xorRun a
          = liftReg (Option Bool) (R.step (t + 1))
              * (transGadget.xorRun a * (simTransUpto R t).xorRun a) := by
        change ((simTransUpto R t).comp _).xorRun a = _
        rw [QRoutine.comp_xorRun, QRoutine.comp_xorRun,
          QRoutine.ofUnitary_xorRun, Matrix.mul_assoc]
      rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        transGadget_xorRun, liftReg_mulVec_embed, QRoutine.runUpto_succ,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- **The compiled transposition schedule**: `2·R.len` XOR queries. -/
def simTrans (R : QRoutine ι Bool W) : QRoutine ι Bool (Option Bool × W) :=
  simTransUpto R R.len

@[simp] lemma simTrans_len (R : QRoutine ι Bool W) :
    (simTrans R).len = 2 * R.len := simTransUpto_len R R.len

theorem simTrans_xorRun (R : QRoutine ι Bool W) (a : ι → Bool)
    (ψ : QBasis ι Bool W → ℂ) :
    (simTrans R).xorRun a *ᵥ embedReg (some false) ψ
      = embedReg (some false) (R.run a *ᵥ ψ) :=
  simTransUpto_xorRun R a R.len ψ

/-! ## Transporting states, readouts, and probabilities -/

section Transport

variable {σ V O : Type} [Fintype σ] [DecidableEq σ] [Fintype V] [DecidableEq V]
  [DecidableEq O]

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] in
lemma isQState_embedReg (v : V) {ψ : QBasis ι σ W → ℂ} (hψ : IsQState ψ) :
    IsQState (embedReg v ψ) := by
  classical
  rw [IsQState, qNormSq_embedReg]
  exact hψ

/-- Read the underlying registers, ignoring the ancilla. -/
def stripReadout (r : QBasis ι σ W → O) : QBasis ι σ (V × W) → O :=
  fun p => r (p.1, p.2.1, p.2.2.2)

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] [Fintype V] [Fintype W] [Fintype ι]
    [Fintype σ] in
lemma qRestrict_stripReadout_embedReg (r : QBasis ι σ W → O) (v : V) (o : O)
    (χ : QBasis ι σ W → ℂ) :
    qRestrict (stripReadout (V := V) r) o (embedReg v χ)
      = embedReg v (qRestrict r o χ) := by
  classical
  funext p
  rw [qRestrict, embedReg_apply, embedReg_apply, qRestrict, stripReadout]
  by_cases hv : p.2.2.1 = v <;>
    by_cases hr : r (p.1, p.2.1, p.2.2.2) = o <;>
    simp [hv, hr]

omit [DecidableEq W] [DecidableEq ι] [DecidableEq σ] in
/-- **Measuring through the ancilla changes nothing.** -/
lemma qProb_stripReadout_embedReg (r : QBasis ι σ W → O) (v : V) (o : O)
    (χ : QBasis ι σ W → ℂ) :
    qProb (stripReadout (V := V) r) (embedReg v χ) o = qProb r χ o := by
  classical
  rw [qProb_eq_qNormSq_qRestrict, qProb_eq_qNormSq_qRestrict,
    qRestrict_stripReadout_embedReg, qNormSq_embedReg]

end Transport

/-! ## The state bridges -/

section Bridges

variable {O : Type} [DecidableEq O]

omit [DecidableEq O] in
/-- The standard state is the run of the algorithm's own schedule. -/
lemma state_eq_runUpto (A : QAlg ι Bool O W) (n : ℕ) (a : ι → Bool) (t : ℕ) :
    A.state a t
      = (QRoutine.mk n A.step A.step_unitary).runUpto a t *ᵥ A.init := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [QAlg.state_succ, ih, QRoutine.runUpto_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]

omit [DecidableEq O] in
/-- The XOR state of a packaged routine is its parametric run. -/
lemma xorState_toAlg (R : QRoutine ι Bool W) (init : QBasis ι Bool W → ℂ)
    (hinit : IsQState init) (r : QBasis ι Bool W → O) (a : ι → Bool) (t : ℕ) :
    xorState (R.toAlg init hinit r) a t
      = R.runWith (xorOracleMat a) t *ᵥ init := by
  classical
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [xorState_succ, ih, QRoutine.runWith_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rfl

end Bridges

/-! ## The `QueryCounts` translations -/

section Translations

variable {O : Type} [DecidableEq O] {X : Type} [Fintype X]

omit [Fintype X] in
/-- **The transposition model simulates the XOR model** at a factor of two:
every achievable XOR query count doubles into the native model. -/
theorem two_mul_mem_queryCounts_of_xor {read : X → ι → Bool} {f : X → O}
    {ε : ℝ} {q : ℕ} (hq : q ∈ XorQueryCounts read f ε) :
    2 * q ∈ QueryCounts read f ε := by
  classical
  obtain ⟨W', _, _, A, hA⟩ := hq
  refine mem_queryCounts
    (A := (simXor (QRoutine.mk q A.step A.step_unitary)).toAlg
      (embedReg none A.init) (isQState_embedReg none A.init_isQState)
      (stripReadout A.readout)) ?_
  intro x
  have hlen : (simXor (QRoutine.mk q A.step A.step_unitary)).len = 2 * q := by
    rw [simXor_len]
  have hstate : ((simXor (QRoutine.mk q A.step A.step_unitary)).toAlg
        (embedReg none A.init) (isQState_embedReg none A.init_isQState)
        (stripReadout A.readout)).state (read x) (2 * q)
      = embedReg none (xorState A (read x) q) := by
    rw [← hlen, QRoutine.toAlg_state_len, simXor_run,
      ← xorState_eq_runWith A q]
  rw [QAlg.prob, hstate,
    show ((simXor (QRoutine.mk q A.step A.step_unitary)).toAlg
        (embedReg none A.init) (isQState_embedReg none A.init_isQState)
        (stripReadout A.readout)).readout = stripReadout A.readout from rfl,
    qProb_stripReadout_embedReg]
  exact hA x

omit [Fintype X] in
/-- **The XOR model simulates the transposition model** at a factor of two. -/
theorem two_mul_mem_xorQueryCounts_of_std {read : X → ι → Bool} {f : X → O}
    {ε : ℝ} {q : ℕ} (hq : q ∈ QueryCounts read f ε) :
    2 * q ∈ XorQueryCounts read f ε := by
  classical
  obtain ⟨W', _, _, A, hA⟩ := hq
  refine mem_xorQueryCounts
    (A := (simTrans (QRoutine.mk q A.step A.step_unitary)).toAlg
      (embedReg (some false) A.init)
      (isQState_embedReg (some false) A.init_isQState)
      (stripReadout A.readout)) ?_
  intro x
  have hlen : (simTrans (QRoutine.mk q A.step A.step_unitary)).len = 2 * q := by
    rw [simTrans_len]
  have hstate : xorState ((simTrans (QRoutine.mk q A.step A.step_unitary)).toAlg
        (embedReg (some false) A.init)
        (isQState_embedReg (some false) A.init_isQState)
        (stripReadout A.readout)) (read x) (2 * q)
      = embedReg (some false) (A.state (read x) q) := by
    rw [xorState_toAlg, show (2 * q)
        = (simTrans (QRoutine.mk q A.step A.step_unitary)).len from hlen.symm]
    rw [show (simTrans (QRoutine.mk q A.step A.step_unitary)).runWith
          (xorOracleMat (read x))
          (simTrans (QRoutine.mk q A.step A.step_unitary)).len
        = (simTrans (QRoutine.mk q A.step A.step_unitary)).xorRun (read x)
        from rfl]
    rw [simTrans_xorRun,
      show (QRoutine.mk q A.step A.step_unitary).run (read x)
          = (QRoutine.mk q A.step A.step_unitary).runUpto (read x) q from rfl,
      ← state_eq_runUpto A q]
  rw [hstate,
    show ((simTrans (QRoutine.mk q A.step A.step_unitary)).toAlg
        (embedReg (some false) A.init)
        (isQState_embedReg (some false) A.init_isQState)
        (stripReadout A.readout)).readout = stripReadout A.readout from rfl,
    qProb_stripReadout_embedReg]
  exact hA x

/-! ## The complexity comparison -/

variable [Nonempty O]

omit [Fintype X] in
theorem xorQueryCounts_nonempty {read : X → ι → Bool} {f : X → O} {ε : ℝ}
    (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) [Finite X] :
    (XorQueryCounts read f ε).Nonempty := by
  classical
  let := Fintype.ofFinite X
  obtain ⟨q, hq⟩ := queryCounts_nonempty hdet hε0
  exact ⟨2 * q, two_mul_mem_xorQueryCounts_of_std hq⟩

omit [Fintype X] in
/-- **Model equivalence, one direction**: standard complexity is at most
twice the XOR complexity. -/
theorem qQueryOn_le_two_mul_xorQQueryOn {read : X → ι → Bool} {f : X → O}
    {ε : ℝ} (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) [Finite X] :
    qQueryOn read f ε ≤ 2 * xorQQueryOn read f ε := by
  classical
  let := Fintype.ofFinite X
  have hne := xorQueryCounts_nonempty hdet hε0
  have hmem : xorQQueryOn read f ε ∈ XorQueryCounts read f ε :=
    Nat.sInf_mem hne
  exact Nat.sInf_le (two_mul_mem_queryCounts_of_xor hmem)

omit [Fintype X] in
/-- **Model equivalence, the other direction**: XOR complexity is at most
twice the standard complexity. -/
theorem xorQQueryOn_le_two_mul_qQueryOn {read : X → ι → Bool} {f : X → O}
    {ε : ℝ} (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) [Finite X] :
    xorQQueryOn read f ε ≤ 2 * qQueryOn read f ε := by
  classical
  let := Fintype.ofFinite X
  have hne := queryCounts_nonempty hdet hε0
  have hmem : qQueryOn read f ε ∈ QueryCounts read f ε := Nat.sInf_mem hne
  exact Nat.sInf_le (two_mul_mem_xorQueryCounts_of_std hmem)

end Translations

end QuantumQueryComplexity

end SourceQuantumSimulation

section SourceQuantumFiniteOutput

/-!
# Finite outputs by bit encoding

A finite output type `O` with `m` values is encoded in
`B = ⌈log₂ m⌉ = Nat.clog 2 m` Boolean bits through `Fintype.equivFin`; each
bit of `f` is a post-composition of `f`, so on the adversary side it costs
nothing (`advPMOn_comp_le`).  Given a `1/16`-algorithm for each bit, the
assembly is:

* amplify each bit to error `(1/4)ᵗ` with `2t` majority rounds (`amplify`;
  the exponent arithmetic is `2^{2t}·(1/16)^t = (1/4)^t`);
* join the `B` amplified bits into the tuple (`exists_tuple_computes`),
  error `B·(1/4)ᵗ`, cost `∑ᵢ 2t·qᵢ`;
* decode by post-composing the readout with the inverse encoding
  (`ComputesWithErrorOn.postcomp` from `SourceQuantumPostcomp` — the fibre sum
  only grows the correct outcome's probability).

`exists_decode_computes` is the generic assembly; the final theorem against
`advPMOn` lives in `SourceQuantumCharacterization`, which supplies the
per-bit algorithms from the promise-Boolean characterization.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X]

/-! ## The bit encoding -/

variable (O : Type) [Fintype O] [DecidableEq O]

/-- The number of encoding bits: `⌈log₂ |O|⌉`. -/
def encBits : ℕ := Nat.clog 2 (Fintype.card O)

variable {O}

/-- Bit `i` of the encoded value. -/
noncomputable def encBit (o : O) (i : Fin (encBits O)) : Bool :=
  Nat.testBit ((Fintype.equivFin O) o).val i.val

omit [DecidableEq O] in
/-- The encoding is injective: values are below `2^B`, so the first `B` bits
determine them. -/
lemma encBit_injective {o o' : O}
    (h : ∀ i : Fin (encBits O), encBit o i = encBit o' i) : o = o' := by
  have hlt : ∀ p : O, ((Fintype.equivFin O) p).val < 2 ^ encBits O := by
    intro p
    calc ((Fintype.equivFin O) p).val < Fintype.card O :=
        ((Fintype.equivFin O) p).isLt
      _ ≤ 2 ^ encBits O := Nat.le_pow_clog (by norm_num) _
  have hval : ((Fintype.equivFin O) o).val = ((Fintype.equivFin O) o').val := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    by_cases hi : i < encBits O
    · exact h ⟨i, hi⟩
    · rw [Nat.testBit_eq_false_of_lt, Nat.testBit_eq_false_of_lt]
      · exact lt_of_lt_of_le (hlt o')
          (Nat.pow_le_pow_right (by norm_num) (le_of_not_gt hi))
      · exact lt_of_lt_of_le (hlt o)
          (Nat.pow_le_pow_right (by norm_num) (le_of_not_gt hi))
  exact (Fintype.equivFin O).injective (Fin.ext hval)

/-- The decoder: the (unique) value with the given bits, if any. -/
noncomputable def encDecode [Nonempty O] (y : Fin (encBits O) → Bool) : O :=
  if h : ∃ o : O, (fun i => encBit o i) = y then h.choose
  else Classical.arbitrary O

omit [DecidableEq O] in
lemma encDecode_encBit [Nonempty O] (o : O) :
    encDecode (fun i => encBit o i) = o := by
  classical
  rw [encDecode, dite_eq_left ⟨o, rfl⟩]
  have hspec := (⟨o, rfl⟩ : ∃ o' : O,
    (fun i => encBit o' i) = fun i => encBit o i).choose_spec
  exact encBit_injective fun i => congrFun hspec i

/-! ## The assembly -/

/-- The exponent arithmetic of the amplification: `2t` rounds at error
`1/16` give error `(1/4)ᵗ`. -/
private lemma amp_error_eq (t : ℕ) :
    (2 : ℝ) ^ (2 * t) * (1 / 16 : ℝ) ^ ((2 * t + 1) / 2) = (1 / 4) ^ t := by
  have hexp : (2 * t + 1) / 2 = t := by omega
  rw [hexp, pow_mul]
  rw [show ((2 : ℝ) ^ 2) = 4 from by norm_num, ← mul_pow]
  norm_num

omit [Fintype X] in
/-- **The finite-output assembly**: given a `1/16`-algorithm for each
encoding bit of `f`, there is an algorithm for `f` itself with error
`B·(1/4)ᵗ` at cost `∑ᵢ 2t·qᵢ`. -/
theorem exists_decode_computes {O : Type} [Fintype O] [DecidableEq O]
    [Nonempty O] {read : X → ι → σ} {f : X → O}
    {qb : Fin (encBits O) → ℕ} (t : ℕ)
    (halg : ∀ i, ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QAlg ι σ Bool W),
      ComputesWithErrorOn A (qb i) read (fun x => encBit (f x) i) (1 / 16)) :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W')
      (A' : QAlg ι σ O W'),
      ComputesWithErrorOn A' (∑ i, 2 * t * qb i) read f
        ((encBits O : ℝ) * (1 / 4) ^ t) := by
  classical
  -- amplify each bit
  have hamp : ∀ i, ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QAlg ι σ Bool W),
      ComputesWithErrorOn A (2 * t * qb i) read
        (fun x => encBit (f x) i) ((1 / 4 : ℝ) ^ t) := by
    intro i
    have h := amplify (by norm_num) (by norm_num) (halg i) (2 * t)
    rw [amp_error_eq] at h
    rw [show 2 * t * qb i = (2 * t) * qb i from rfl]
    exact h
  -- join the bits
  have htuple := exists_tuple_computes
    (ε := fun _ => ((1 / 4 : ℝ) ^ t)) (fun _ => by positivity) hamp
  -- the tuple error sums to `B·(1/4)ᵗ`
  rw [show (∑ _i : Fin (encBits O), ((1 / 4 : ℝ) ^ t))
      = (encBits O : ℝ) * (1 / 4) ^ t from by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
    at htuple
  -- decode
  obtain ⟨W', hW1, hW2, A', hA'⟩ := htuple
  have hdec := hA'.exists_postcomp (encDecode (O := O))
  refine hdec.imp fun W'' h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun A'' hA'' => ?_
  intro x
  have hx := hA'' x
  have hbeta : (fun x => encDecode fun i => encBit (f x) i) x = f x := by
    change encDecode (fun i => encBit (f x) i) = f x
    exact encDecode_encBit (f x)
  rwa [hbeta] at hx

end QuantumQueryComplexity

end SourceQuantumFiniteOutput
