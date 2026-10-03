/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Adversary matrices, semidefinite duality, and composition

Ported from the corresponding upstream modules listed by the source sections below.
References beginning with `Source` name these retained sections.
-/

public section

section SourceDefs

/-!
# The negative-weight adversary bound: definitions

We define the negative-weight adversary bound `ADV±` of Høyer–Lee–Špalek
(quant-ph/0611054, Definition 2) for a total function `f : (ι → σ) → O`, in the
division-free primal form of Belovs–Lee (arXiv:2004.06439, Definition 6):

  `advPM f = sup { ‖Γ‖ | Γ symmetric, Γ x y = 0 whenever f x = f y,
                          and ‖Γ ⊙ D i‖ ≤ 1 for every input index i }`

where `D i = advD i` is the difference matrix with `(D i) x y = 1` iff
`x i ≠ y i`, `⊙` is the Hadamard (entrywise) product, and `‖·‖` is the spectral
(L2 operator) norm.  Since `Γ = 0` is feasible, the value set is nonempty and
`advPM f ≥ 0`; no division or `Γ ≠ 0` side condition is needed.

Nothing here uses two-valuedness of the input alphabet `σ` or of the output type
`O`: `advD` needs only `DecidableEq σ` for its `if`, and `IsAdvMatrix` uses
`f x = f y` as a proposition, never as a decidable test.  The Boolean theory is
recovered at `σ = O = Bool`, which is how every downstream file uses it; the
general alphabet is what makes non-Boolean problems such as maximum finding
expressible.

We also define the classical nonnegative-weight bound `adv` (HLŠ Definition 1)
by adding the entrywise nonnegativity constraint.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*}

/-- The difference matrix `D_i` (HLŠ §2, BL Definition 6): `(advD i) x y = 1`
if `x i ≠ y i` and `0` otherwise. -/
@[expose]
def advD (i : ι) : Matrix (ι → σ) (ι → σ) ℝ :=
  Matrix.of fun x y => if x i = y i then 0 else 1

omit [DecidableEq ι] [Fintype ι] [Fintype σ] in
@[simp] lemma advD_apply (i : ι) (x y : ι → σ) :
    advD i x y = if x i = y i then 0 else 1 := rfl

omit [DecidableEq ι] [Fintype ι] [Fintype σ] in
lemma advD_isHermitian (i : ι) : (advD (σ := σ) i).IsHermitian := by
  change (advD i)ᴴ = advD i
  ext x y
  simp [Matrix.conjTranspose_apply, advD, eq_comm]

omit [DecidableEq ι] [Fintype ι] [Fintype σ] in
lemma hadamard_advD_apply (Γ : Matrix (ι → σ) (ι → σ) ℝ) (i : ι)
    (x y : ι → σ) : (Γ ⊙ advD i) x y = if x i = y i then 0 else Γ x y := by
  classical
  rw [Matrix.hadamard_apply, advD_apply]
  by_cases h : x i = y i <;> simp [h]

/-- An adversary matrix for `f` (HLŠ §2): a real symmetric matrix supported on
pairs of inputs with different `f`-values.  Taking `x = y` shows the diagonal
vanishes. -/
@[expose]
def IsAdvMatrix (f : (ι → σ) → O)
    (Γ : Matrix (ι → σ) (ι → σ) ℝ) : Prop :=
  Γ.IsHermitian ∧ ∀ x y, f x = f y → Γ x y = 0

namespace IsAdvMatrix

variable {f : (ι → σ) → O} {Γ : Matrix (ι → σ) (ι → σ) ℝ}

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma isHermitian (h : IsAdvMatrix f Γ) : Γ.IsHermitian := h.1

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma apply_eq_zero (h : IsAdvMatrix f Γ) {x y : ι → σ} (hxy : f x = f y) :
    Γ x y = 0 := h.2 x y hxy

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma diag_eq_zero (h : IsAdvMatrix f Γ) (x : ι → σ) : Γ x x = 0 :=
  h.2 x x rfl

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma smul (h : IsAdvMatrix f Γ) (c : ℝ) : IsAdvMatrix f (c • Γ) :=
  ⟨h.1.smul (star_trivial c), fun x y hxy => by
    simp [Matrix.smul_apply, h.2 x y hxy]⟩

end IsAdvMatrix

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma isAdvMatrix_zero (f : (ι → σ) → O) : IsAdvMatrix f 0 :=
  ⟨Matrix.isHermitian_zero, fun _ _ _ => rfl⟩

/-- The negative-weight adversary bound `ADV±(f)` (HLŠ Definition 2, in the
division-free form of BL Definition 6). -/
@[expose]
noncomputable def advPM (f : (ι → σ) → O) : ℝ :=
  sSup {r : ℝ | ∃ Γ, IsAdvMatrix f Γ ∧ (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) ∧ r = ‖Γ‖}

/-- The classical (nonnegative-weight) adversary bound `ADV(f)`
(HLŠ Definition 1). -/
noncomputable def adv (f : (ι → σ) → O) : ℝ :=
  sSup {r : ℝ | ∃ Γ, IsAdvMatrix f Γ ∧ (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) ∧
    (∀ x y, 0 ≤ Γ x y) ∧ r = ‖Γ‖}

end QuantumQueryComplexity

end SourceDefs

section SourceMaxDefs

/-!
# Maximum finding: the function and its level counts

`maxFun x = ⊔ᵢ x i` for `x : ι → A` with `A` a linear order and `ι` a nonempty
finite index type.  This is the non-Boolean function whose adversary bound we
study; at `A = Bool` it is exactly `orN`.

We use `Finset.sup'` over `univ` rather than `Finset.max'`: `max'` takes a
`Finset A`, so stating it would force `(Finset.univ.image x).max'`, dragging in
`[DecidableEq A]` and an `image`-nonemptiness proof.  `sup'` ranges over `ι`
directly and needs neither.

Alongside it we define `cnt p x`, the number of coordinates of `x` on which a
`Bool`-valued predicate `p` holds, and the normalised indicator `wt p x`.
Predicates are `Bool`-valued rather than `Prop`-valued throughout this
development so that no `Decidable` instance ever has to be carried, matched, or
unified.
-/


namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] {A : Type*} [LinearOrder A]

/-- The maximum of a tuple: `maxFun x = ⊔ᵢ x i`. -/
noncomputable def maxFun [Nonempty ι] (x : ι → A) : A :=
  Finset.univ.sup' Finset.univ_nonempty x

variable [Nonempty ι]

lemma le_maxFun (x : ι → A) (i : ι) : x i ≤ maxFun x :=
  Finset.le_sup' x (Finset.mem_univ i)

lemma exists_eq_maxFun (x : ι → A) : ∃ i, x i = maxFun x := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  exact ⟨i, hi.symm⟩

lemma maxFun_le {x : ι → A} {b : A} (h : ∀ i, x i ≤ b) : maxFun x ≤ b :=
  Finset.sup'_le _ _ fun i _ => h i

/-- `maxFun` is characterised by the two conditions defining a maximum. -/
lemma maxFun_eq_iff {x : ι → A} {b : A} :
    maxFun x = b ↔ (∃ i, x i = b) ∧ ∀ i, x i ≤ b := by
  constructor
  · rintro rfl
    exact ⟨exists_eq_maxFun x, le_maxFun x⟩
  · rintro ⟨⟨i, rfl⟩, h⟩
    exact le_antisymm (maxFun_le h) (le_maxFun x i)

/-! ## Level counts -/

/-- The number of coordinates of `x` on which the predicate `p` holds. -/
def cnt (p : A → Bool) (x : ι → A) : ℕ :=
  (Finset.univ.filter fun i => p (x i)).card

variable {p : A → Bool}

omit [LinearOrder A] [Nonempty ι] in
lemma cnt_eq_sum (x : ι → A) :
    (cnt p x : ℝ) = ∑ i, if p (x i) then 1 else 0 := by
  simp only [cnt]
  rw [Finset.card_filter]
  push_cast
  rfl

/-- If the cut holds at the maximum then some coordinate realises it, so the
count is positive.  This is what makes the division by `cnt` in the dual
solution harmless. -/
lemma cnt_pos_of_maxFun (x : ι → A) (h : p (maxFun x)) : 0 < cnt p x := by
  obtain ⟨i, hi⟩ := exists_eq_maxFun x
  refine Finset.card_pos.mpr ⟨i, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi]
  exact h

lemma cnt_ne_zero_of_maxFun (x : ι → A) (h : p (maxFun x)) :
    (cnt p x : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (cnt_pos_of_maxFun x h).ne'

lemma one_le_cnt_of_maxFun (x : ι → A) (h : p (maxFun x)) :
    (1 : ℝ) ≤ (cnt p x : ℝ) := by
  exact_mod_cast cnt_pos_of_maxFun x h

/-! ## The normalised indicator of a cut -/

/-- The indicator of `{i | p (x i)}`, normalised to sum to `1`. -/
noncomputable def wt (p : A → Bool) (x : ι → A) (i : ι) : ℝ :=
  (if p (x i) then 1 else 0) / (cnt p x : ℝ)

omit [LinearOrder A] [Nonempty ι] in
lemma wt_eq_zero (x : ι → A) {i : ι} (h : p (x i) = false) : wt p x i = 0 := by
  simp [wt, h]

/-- The normalised indicator sums to `1` whenever the cut holds at the
maximum. -/
lemma sum_wt (x : ι → A) (h : p (maxFun x)) : (∑ i, wt p x i) = 1 := by
  simp only [wt]
  rw [← Finset.sum_div, ← cnt_eq_sum]
  exact div_self (cnt_ne_zero_of_maxFun x h)

/-- The squared `ℓ²` mass of the normalised indicator is `1 / cnt ≤ 1`. -/
lemma sum_wt_sq_le_one (x : ι → A) (h : p (maxFun x)) :
    (∑ i, wt p x i * wt p x i) ≤ 1 := by
  have hne := cnt_ne_zero_of_maxFun (p := p) x h
  have key : (∑ i, wt p x i * wt p x i) = 1 / (cnt p x : ℝ) := by
    have hsq : ∀ i : ι, wt p x i * wt p x i
        = (if p (x i) then (1 : ℝ) else 0) / ((cnt p x : ℝ) * (cnt p x : ℝ)) := by
      intro i
      simp only [wt, div_mul_div_comm]
      by_cases hi : p (x i) <;> simp [hi]
    simp only [hsq]
    rw [← Finset.sum_div, ← cnt_eq_sum]
    field_simp
  rw [key, div_le_one (lt_of_lt_of_le zero_lt_one (one_le_cnt_of_maxFun x h))]
  exact one_le_cnt_of_maxFun x h

end QuantumQueryComplexity

end SourceMaxDefs

section SourceSpectral

/-!
# Spectral-norm infrastructure for the adversary bound

Layer-0 lemmas about the L2 operator norm of real matrices.  All
`EuclideanSpace`/`WithLp` friction is quarantined inside the proofs of this
file: every exported statement is phrased with raw `Matrix`, `*ᵥ`, `⬝ᵥ` and
`Real.sqrt (x ⬝ᵥ x)`.

Main results:
* `abs_dotProduct_mulVec_le` — the master bilinear bound
  `|x ⬝ᵥ A *ᵥ y| ≤ ‖A‖ * √(x ⬝ᵥ x) * √(y ⬝ᵥ y)`;
* `l2_opNorm_le_of_forall_dotProduct` — its converse;
* `abs_entry_le_l2_opNorm` — entries are bounded by the norm;
* `l2_opNorm_le_sum_abs` — the crude bound `‖A‖ ≤ ∑ |A x y|`;
* `abs_eigenvalue_le_norm` — eigenvalues are bounded by the norm.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix

variable {n : Type*} [Fintype n]

lemma dotProduct_self_nonneg (x : n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

lemma norm_toLp_eq (x : n → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ = Real.sqrt (x ⬝ᵥ x) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, Real.norm_eq_abs, sq]

lemma inner_toLp (x y : n → ℝ) :
    ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ n), WithLp.toLp 2 y⟫ = x ⬝ᵥ y := by
  simp [PiLp.inner_apply, RCLike.inner_apply, dotProduct, mul_comm]

lemma abs_apply_le_sqrt_dotProduct_self (x : n → ℝ) (i : n) :
    |x i| ≤ Real.sqrt (x ⬝ᵥ x) := by
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  simpa [sq, dotProduct] using
    Finset.single_le_sum (f := fun j => x j * x j)
      (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)

lemma dotProduct_mulVec_eq_sum (A : Matrix n n ℝ) (u w : n → ℝ) :
    u ⬝ᵥ A *ᵥ w = ∑ x, ∑ y, u x * A x y * w y := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

variable [DecidableEq n]

/-- Master bilinear bound for the L2 operator norm. -/
theorem abs_dotProduct_mulVec_le (A : Matrix n n ℝ) (x y : n → ℝ) :
    |x ⬝ᵥ A *ᵥ y| ≤ ‖A‖ * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
  have h := Matrix.inner_toEuclideanCLM A (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  calc |x ⬝ᵥ A *ᵥ y|
      = |⟪(WithLp.toLp 2 x : EuclideanSpace ℝ n),
          Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 y)⟫| := by rw [h]
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ *
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 y)‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ *
          (‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ *
            ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _)
          (norm_nonneg _)
    _ = ‖A‖ * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
        rw [← Matrix.cstar_norm_def, norm_toLp_eq, norm_toLp_eq]; ring

/-- Converse of the master bilinear bound. -/
theorem l2_opNorm_le_of_forall_dotProduct (A : Matrix n n ℝ) {c : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ x y, |x ⬝ᵥ A *ᵥ y| ≤ c * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) :
    ‖A‖ ≤ c := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun v => ?_
  set y : n → ℝ := WithLp.ofLp v with hy
  set w : n → ℝ := A *ᵥ y with hw
  have hval : Matrix.toEuclideanCLM (𝕜 := ℝ) A v = WithLp.toLp 2 w := by
    conv_lhs => rw [show v = WithLp.toLp 2 y from rfl]
    rw [Matrix.toEuclideanCLM_toLp]
  have hnv : ‖v‖ = Real.sqrt (y ⬝ᵥ y) := by
    rw [show v = WithLp.toLp 2 y from rfl, norm_toLp_eq]
  rw [hval, norm_toLp_eq, hnv]
  have key := h w y
  rw [← hw] at key
  have habs : |w ⬝ᵥ w| = w ⬝ᵥ w := abs_of_nonneg (dotProduct_self_nonneg w)
  have hww : w ⬝ᵥ w = Real.sqrt (w ⬝ᵥ w) * Real.sqrt (w ⬝ᵥ w) :=
    (Real.mul_self_sqrt (dotProduct_self_nonneg w)).symm
  set s := Real.sqrt (w ⬝ᵥ w) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hs0 with h0 | h0
  · rw [← h0]
    positivity
  · rw [habs, hww] at key
    nlinarith [key, h0, Real.sqrt_nonneg (y ⬝ᵥ y)]

/-- Every entry is bounded by the L2 operator norm. -/
theorem abs_entry_le_l2_opNorm (A : Matrix n n ℝ) (x y : n) : |A x y| ≤ ‖A‖ := by
  have h := abs_dotProduct_mulVec_le A (Pi.single x 1) (Pi.single y 1)
  have h1 : (Pi.single x 1 : n → ℝ) ⬝ᵥ A *ᵥ Pi.single y 1 = A x y := by
    simp [single_dotProduct]
  have h2 : (Pi.single x 1 : n → ℝ) ⬝ᵥ Pi.single x 1 = 1 := by
    simp
  have h3 : (Pi.single y 1 : n → ℝ) ⬝ᵥ Pi.single y 1 = 1 := by
    simp
  rw [h1, h2, h3, Real.sqrt_one] at h
  simpa using h

/-- Crude norm bound: the L2 operator norm is at most the sum of the absolute
values of the entries. -/
theorem l2_opNorm_le_sum_abs (A : Matrix n n ℝ) :
    ‖A‖ ≤ ∑ x, ∑ y, |A x y| := by
  refine l2_opNorm_le_of_forall_dotProduct A
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    fun u v => ?_
  rw [dotProduct_mulVec_eq_sum]
  calc |∑ a, ∑ b, u a * A a b * v b|
      ≤ ∑ a, ∑ b, |u a * A a b * v b| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a, ∑ b, |A a b| * (Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v)) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [abs_mul, abs_mul]
        have h12 : |u a| * |v b| ≤ Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) :=
          mul_le_mul (abs_apply_le_sqrt_dotProduct_self u a)
            (abs_apply_le_sqrt_dotProduct_self v b) (abs_nonneg _)
            (Real.sqrt_nonneg _)
        calc |u a| * |A a b| * |v b| = |A a b| * (|u a| * |v b|) := by ring
          _ ≤ |A a b| * (Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v)) :=
              mul_le_mul_of_nonneg_left h12 (abs_nonneg _)
    _ = (∑ x, ∑ y, |A x y|) * (Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v)) := by
        simp_rw [← Finset.sum_mul]
    _ = (∑ x, ∑ y, |A x y|) * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) :=
        (mul_assoc _ _ _).symm

/-- An eigenvalue of any square real matrix is bounded by the L2 operator
norm. -/
theorem abs_eigenvalue_le_norm {A : Matrix n n ℝ} {v : n → ℝ} {θ : ℝ}
    (hv : A *ᵥ v = θ • v) (hv0 : v ≠ 0) : |θ| ≤ ‖A‖ := by
  have h := abs_dotProduct_mulVec_le A v v
  rw [hv] at h
  have hsmul : v ⬝ᵥ (θ • v) = θ * (v ⬝ᵥ v) := by
    simp [dotProduct_smul, smul_eq_mul]
  rw [hsmul, abs_mul, abs_of_nonneg (dotProduct_self_nonneg v)] at h
  have hvv : 0 < v ⬝ᵥ v := by
    rcases (dotProduct_self_nonneg v).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (dotProduct_self_eq_zero.mp h'.symm) hv0
  have hsq : Real.sqrt (v ⬝ᵥ v) * Real.sqrt (v ⬝ᵥ v) = v ⬝ᵥ v :=
    Real.mul_self_sqrt (dotProduct_self_nonneg v)
  rw [mul_assoc, hsq] at h
  exact le_of_mul_le_mul_right h hvv

/-- Reindexing a square matrix along an injection of index types does not
increase the L2 operator norm. -/
theorem l2_opNorm_submatrix_le {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix n n ℝ) (e : m ≃ n) : ‖A.submatrix e e‖ ≤ ‖A‖ := by
  refine l2_opNorm_le_of_forall_dotProduct _ (norm_nonneg A) fun x y => ?_
  have hdot : ∀ z : m → ℝ,
      (fun a => z (e.symm a)) ⬝ᵥ (fun a => z (e.symm a)) = z ⬝ᵥ z := fun z =>
    Equiv.sum_comp e.symm fun a => z a * z a
  have hbil : x ⬝ᵥ (A.submatrix e e) *ᵥ y
      = (fun a => x (e.symm a)) ⬝ᵥ A *ᵥ (fun b => y (e.symm b)) := by
    rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum,
      ← Equiv.sum_comp e (fun a => ∑ b, x (e.symm a) * A a b * y (e.symm b))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Equiv.sum_comp e
      (fun b => x (e.symm (e p)) * A (e p) b * y (e.symm b))]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [Matrix.submatrix_apply]
  rw [hbil, ← hdot x, ← hdot y]
  exact abs_dotProduct_mulVec_le _ _ _

/-- Reindexing a square matrix by a bijection preserves the L2 operator
norm. -/
theorem l2_opNorm_submatrix_equiv {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix n n ℝ) (e : m ≃ n) : ‖A.submatrix e e‖ = ‖A‖ := by
  refine le_antisymm (l2_opNorm_submatrix_le A e) ?_
  have h := l2_opNorm_submatrix_le (A.submatrix e e) e.symm
  rwa [Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id] at h

/-! ## The eigenvalue layer -/

/-- For a real symmetric matrix, the L2 operator norm equals the sup norm of
the eigenvalue vector.  Proof: spectral theorem plus unitary invariance of the
C*-norm, plus `‖diagonal v‖ = ‖v‖`. -/
theorem norm_eq_norm_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ‖A‖ = ‖hA.eigenvalues‖ := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [CStarRing.norm_mul_mem_unitary _
      (Unitary.star_mem hA.eigenvectorUnitary.prop),
    CStarRing.norm_mem_unitary_mul _ hA.eigenvectorUnitary.prop,
    Matrix.l2_opNorm_diagonal, RCLike.ofReal_real_eq_id, Function.id_comp]

theorem abs_eigenvalues_le_norm {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (j : n) : |hA.eigenvalues j| ≤ ‖A‖ := by
  rw [norm_eq_norm_eigenvalues hA]
  simpa [Real.norm_eq_abs] using norm_le_pi_norm hA.eigenvalues j

theorem exists_abs_eigenvalues_eq_norm [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) : ∃ j, |hA.eigenvalues j| = ‖A‖ := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset n)
    Finset.univ_nonempty (fun i => ‖hA.eigenvalues i‖₊)
  refine ⟨j, ?_⟩
  rw [norm_eq_norm_eigenvalues hA, Pi.norm_def, hj]
  simp [Real.norm_eq_abs]

theorem norm_le_of_forall_abs_eigenvalues_le {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ j, |hA.eigenvalues j| ≤ B) : ‖A‖ ≤ B := by
  rw [norm_eq_norm_eigenvalues hA]
  refine (pi_norm_le_iff_of_nonneg hB).mpr fun j => ?_
  rw [Real.norm_eq_abs]
  exact h j

/-- **Spanning-eigenvector bound.**  If a family of eigenvectors of a real
symmetric matrix spans the whole space and all its eigenvalues are bounded by
`B` in absolute value, then `‖A‖ ≤ B`.  Members of the family are allowed to
be zero. -/
theorem norm_le_of_eigenvector_family {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {κ : Type*} (v : κ → n → ℝ) (μ : κ → ℝ) {B : ℝ}
    (hB : 0 ≤ B)
    (heig : ∀ k, A *ᵥ v k = μ k • v k)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (hμ : ∀ k, |μ k| ≤ B) : ‖A‖ ≤ B := by
  refine norm_le_of_forall_abs_eigenvalues_le hA hB fun j => ?_
  by_contra hlt
  push Not at hlt
  set w : n → ℝ := WithLp.ofLp (hA.eigenvectorBasis j) with hwdef
  have hw0 : w ≠ 0 := fun h0 =>
    hA.eigenvectorBasis.orthonormal.ne_zero j (by
      have hb : hA.eigenvectorBasis j = WithLp.toLp 2 w := rfl
      rw [hb, h0]
      rfl)
  have hAw : A *ᵥ w = hA.eigenvalues j • w := hA.mulVec_eigenvectorBasis j
  have hAT : Aᵀ = A := (Matrix.isHermitian_iff_isSymm.mp hA)
  have horth : ∀ k, w ⬝ᵥ v k = 0 := by
    intro k
    have hsymm : w ⬝ᵥ A *ᵥ v k = v k ⬝ᵥ A *ᵥ w := by
      conv_lhs => rw [← hAT]
      exact Matrix.dotProduct_transpose_mulVec ..
    have h1 : w ⬝ᵥ A *ᵥ v k = μ k * (w ⬝ᵥ v k) := by
      rw [heig k, dotProduct_smul, smul_eq_mul]
    have h2 : v k ⬝ᵥ A *ᵥ w = hA.eigenvalues j * (v k ⬝ᵥ w) := by
      rw [hAw, dotProduct_smul, smul_eq_mul]
    have key : hA.eigenvalues j * (w ⬝ᵥ v k) = μ k * (w ⬝ᵥ v k) := by
      calc hA.eigenvalues j * (w ⬝ᵥ v k)
          = hA.eigenvalues j * (v k ⬝ᵥ w) := by rw [dotProduct_comm]
        _ = v k ⬝ᵥ A *ᵥ w := h2.symm
        _ = w ⬝ᵥ A *ᵥ v k := hsymm.symm
        _ = μ k * (w ⬝ᵥ v k) := h1
    have hne : hA.eigenvalues j ≠ μ k := fun hEq =>
      absurd (by rw [hEq]; exact hμ k) (not_le.mpr hlt)
    have hfac : (hA.eigenvalues j - μ k) * (w ⬝ᵥ v k) = 0 := by
      linarith [key]
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact absurd (sub_eq_zero.mp h') hne
    · exact h'
  let φ : (n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun u => w ⬝ᵥ u
      map_add' := fun a b => dotProduct_add w a b
      map_smul' := fun c u => by simp [dotProduct_smul] }
  have hker : Submodule.span ℝ (Set.range v) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    exact horth k
  have hw_in : w ∈ LinearMap.ker φ :=
    hker (by rw [hspan]; exact Submodule.mem_top)
  have hww : w ⬝ᵥ w = 0 := LinearMap.mem_ker.mp hw_in
  exact hw0 (dotProduct_self_eq_zero.mp hww)

/-- Conjugation by a `±1` diagonal matrix preserves the L2 operator norm. -/
theorem l2_opNorm_conj_diagonal_sign {s : n → ℝ}
    (hs : ∀ a, s a = 1 ∨ s a = -1) (X : Matrix n n ℝ) :
    ‖Matrix.diagonal s * X * Matrix.diagonal s‖ = ‖X‖ := by
  have hDD : Matrix.diagonal s * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have hss : (fun a => s a * s a) = fun _ => (1 : ℝ) := by
      funext a
      rcases hs a with h | h <;> rw [h] <;> norm_num
    rw [hss, Matrix.diagonal_one]
  have hstar : star (Matrix.diagonal s) = Matrix.diagonal s := by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
  have hmem : Matrix.diagonal s ∈ unitary (Matrix n n ℝ) :=
    Unitary.mem_iff.mpr ⟨by rw [hstar, hDD], by rw [hstar, hDD]⟩
  rw [mul_assoc, CStarRing.norm_mem_unitary_mul _ hmem,
    CStarRing.norm_mul_mem_unitary _ hmem]

end QuantumQueryComplexity

end SourceSpectral

section SourceBasic

/-!
# Basic properties of the adversary bound

Accessor lemmas for `advPM` as a conditionally complete supremum, the a priori
bound `‖Γ‖ ≤ card²` for feasible matrices (which makes the value set bounded
above), and the un-normalized witness lemma `norm_div_le_advPM` — the workhorse
for proving lower bounds on `advPM`.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} {f : (ι → σ) → O} {Γ : Matrix (ι → σ) (ι → σ) ℝ}

lemma advPM_set_nonempty (f : (ι → σ) → O) :
    {r : ℝ | ∃ Γ, IsAdvMatrix f Γ ∧ (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) ∧
      r = ‖Γ‖}.Nonempty :=
  ⟨‖(0 : Matrix (ι → σ) (ι → σ) ℝ)‖, 0, isAdvMatrix_zero f,
    fun i => by simp, rfl⟩

/-- All entries of a feasible matrix are bounded by `1` in absolute value:
off-diagonal entries embed into some `Γ ⊙ advD i`, and entries with
`f x = f y` (in particular the diagonal) vanish. -/
lemma abs_apply_le_one_of_feasible (h1 : IsAdvMatrix f Γ)
    (h2 : ∀ i, ‖Γ ⊙ advD i‖ ≤ 1) (x y : ι → σ) : |Γ x y| ≤ 1 := by
  by_cases hf : f x = f y
  · simp [h1.apply_eq_zero hf]
  · have hxy : x ≠ y := fun h => hf (by rw [h])
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    have h3 := abs_entry_le_l2_opNorm (Γ ⊙ advD i) x y
    rw [hadamard_advD_apply, ite_eq_right hi] at h3
    exact h3.trans (h2 i)

/-- The a priori bound making the `advPM` value set bounded above. -/
lemma norm_le_of_feasible (h1 : IsAdvMatrix f Γ)
    (h2 : ∀ i, ‖Γ ⊙ advD i‖ ≤ 1) :
    ‖Γ‖ ≤ (Fintype.card (ι → σ) : ℝ) ^ 2 := by
  refine (l2_opNorm_le_sum_abs Γ).trans ?_
  calc ∑ x, ∑ y, |Γ x y| ≤ ∑ _x : ι → σ, ∑ _y : ι → σ, (1 : ℝ) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        abs_apply_le_one_of_feasible h1 h2 x y
    _ = (Fintype.card (ι → σ) : ℝ) ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, pow_two]

lemma bddAbove_advPM_set (f : (ι → σ) → O) :
    BddAbove {r : ℝ | ∃ Γ, IsAdvMatrix f Γ ∧ (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) ∧
      r = ‖Γ‖} := by
  refine ⟨(Fintype.card (ι → σ) : ℝ) ^ 2, ?_⟩
  rintro r ⟨Γ, h1, h2, rfl⟩
  exact norm_le_of_feasible h1 h2

/-- Every feasible matrix certifies a lower bound on `advPM`. -/
theorem le_advPM (h1 : IsAdvMatrix f Γ) (h2 : ∀ i, ‖Γ ⊙ advD i‖ ≤ 1) :
    ‖Γ‖ ≤ advPM f :=
  le_csSup (bddAbove_advPM_set f) ⟨Γ, h1, h2, rfl⟩

theorem advPM_nonneg (f : (ι → σ) → O) : 0 ≤ advPM f := by
  simpa using le_advPM (isAdvMatrix_zero f) fun i => by simp

theorem advPM_le {c : ℝ}
    (hc : ∀ Γ, IsAdvMatrix f Γ → (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) → ‖Γ‖ ≤ c) :
    advPM f ≤ c := by
  refine csSup_le (advPM_set_nonempty f) ?_
  rintro r ⟨Γ, h1, h2, rfl⟩
  exact hc Γ h1 h2

/-- ε-accessor: any value below `advPM f` is beaten by a feasible witness. -/
theorem exists_lt_of_lt_advPM {c : ℝ} (h : c < advPM f) :
    ∃ Γ, IsAdvMatrix f Γ ∧ (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) ∧ c < ‖Γ‖ := by
  obtain ⟨r, hr, hcr⟩ := exists_lt_of_lt_csSup (advPM_set_nonempty f) h
  obtain ⟨Γ, h1, h2, rfl⟩ := hr
  exact ⟨Γ, h1, h2, hcr⟩

/-- **Un-normalized witness lemma**: an adversary matrix all of whose Schur
norms are at most `c` certifies `‖Γ‖ / c ≤ advPM f`.  This is the paper's
ratio formulation, division-free at the point of use. -/
theorem norm_div_le_advPM (h1 : IsAdvMatrix f Γ) {c : ℝ}
    (h2 : ∀ i, ‖Γ ⊙ advD i‖ ≤ c) (hc : 0 < c) : ‖Γ‖ / c ≤ advPM f := by
  have k1 : IsAdvMatrix f (c⁻¹ • Γ) := h1.smul c⁻¹
  have k2 : ∀ i, ‖(c⁻¹ • Γ) ⊙ advD i‖ ≤ 1 := fun i => by
    rw [Matrix.smul_hadamard, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hc)]
    calc c⁻¹ * ‖Γ ⊙ advD i‖ ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left (h2 i) (inv_pos.mpr hc).le
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have h := le_advPM k1 k2
  rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc),
    inv_mul_eq_div] at h

theorem adv_le_advPM (f : (ι → σ) → O) : adv f ≤ advPM f := by
  refine csSup_le ?_ ?_
  · exact ⟨‖(0 : Matrix (ι → σ) (ι → σ) ℝ)‖, 0, isAdvMatrix_zero f,
      fun i => by simp, fun x y => le_rfl, rfl⟩
  · rintro r ⟨Γ, h1, h2, -, rfl⟩
    exact le_advPM h1 h2

theorem advPM_eq_zero_of_forall_eq (h : ∀ x y, f x = f y) : advPM f = 0 :=
  le_antisymm
    (advPM_le fun Γ hΓ _ => by
      have hΓ0 : Γ = 0 := by
        ext x y
        rw [Matrix.zero_apply]
        exact hΓ.apply_eq_zero (h x y)
      simp [hΓ0])
    (advPM_nonneg f)

/-! ## The elementary two-entry witness -/

/-- The elementary adversary matrix `e_{xy} + e_{yx}` supported on a single
symmetric pair of entries. -/
def pairMatrix (x y : ι → σ) : Matrix (ι → σ) (ι → σ) ℝ :=
  Matrix.single x y 1 + Matrix.single y x 1

omit [DecidableEq ι] [Fintype σ] in
lemma pairMatrix_isHermitian (x y : ι → σ) :
    (pairMatrix x y).IsHermitian := by
  change (pairMatrix x y)ᴴ = pairMatrix x y
  ext a b
  simp only [Matrix.conjTranspose_apply, pairMatrix, Matrix.add_apply,
    Matrix.single_apply, star_trivial]
  rw [add_comm]
  congr 1
  · exact if_congr (by tauto) rfl rfl
  · exact if_congr (by tauto) rfl rfl

lemma single_one_mulVec (a b : ι → σ) (u : (ι → σ) → ℝ) :
    Matrix.single a b (1 : ℝ) *ᵥ u = fun w => if a = w then u b else 0 := by
  funext w
  by_cases haw : a = w
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, haw]
  · simp [Matrix.mulVec, dotProduct, haw]

lemma pairMatrix_mulVec (x y : ι → σ) (u : (ι → σ) → ℝ) :
    pairMatrix x y *ᵥ u
      = fun w => (if x = w then u y else 0) + if y = w then u x else 0 := by
  rw [pairMatrix, Matrix.add_mulVec, single_one_mulVec, single_one_mulVec]
  rfl

omit [DecidableEq ι] [Fintype σ] in
lemma pairMatrix_apply_eq_zero {x y a b : ι → σ} (h1 : ¬(x = a ∧ y = b))
    (h2 : ¬(y = a ∧ x = b)) : pairMatrix x y a b = 0 := by
  simp [pairMatrix, h1, h2]

omit [DecidableEq ι] [Fintype σ] in
/-- Masking a pair matrix by a difference matrix either leaves it alone or
kills it, according to whether the pair differs in that coordinate. -/
lemma pairMatrix_hadamard_advD (x y : ι → σ) (i : ι) :
    pairMatrix x y ⊙ advD i = if x i = y i then 0 else pairMatrix x y := by
  classical
  by_cases hi : x i = y i
  · rw [ite_eq_left hi]
    ext a b
    rw [Matrix.hadamard_apply, Matrix.zero_apply, advD_apply]
    by_cases h1 : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := h1
      rw [ite_eq_left hi, mul_zero]
    · by_cases h2 : y = a ∧ x = b
      · obtain ⟨rfl, rfl⟩ := h2
        rw [ite_eq_left hi.symm, mul_zero]
      · rw [pairMatrix_apply_eq_zero h1 h2, zero_mul]
  · rw [ite_eq_right hi]
    ext a b
    rw [Matrix.hadamard_apply, advD_apply]
    by_cases h1 : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := h1
      rw [ite_eq_right hi, mul_one]
    · by_cases h2 : y = a ∧ x = b
      · obtain ⟨rfl, rfl⟩ := h2
        rw [ite_eq_right fun h => hi h.symm, mul_one]
      · rw [pairMatrix_apply_eq_zero h1 h2, zero_mul]

lemma norm_pairMatrix {x y : ι → σ} (hxy : x ≠ y) : ‖pairMatrix x y‖ = 1 := by
  classical
  -- `norm_le_of_eigenvector_family` needs `[Nonempty (ι → σ)]`; the hypothesis
  -- `x` supplies the witness, so no `[Nonempty σ]` instance is required.
  have : Nonempty (ι → σ) := ⟨x⟩
  have hmul : ∀ u : (ι → σ) → ℝ, pairMatrix x y *ᵥ u
      = fun w => (if x = w then u y else 0) + if y = w then u x else 0 := by
    intro u
    rw [pairMatrix, Matrix.add_mulVec, single_one_mulVec, single_one_mulVec]
    rfl
  refine le_antisymm ?_ ?_
  · set v : (ι → σ) → (ι → σ) → ℝ := fun z =>
      if z = x then Pi.single x 1 + Pi.single y 1
      else if z = y then Pi.single x 1 - Pi.single y 1
      else Pi.single z 1 with hv
    set μ : (ι → σ) → ℝ := fun z =>
      if z = x then 1 else if z = y then -1 else 0 with hμ
    have hvx : v x = Pi.single x 1 + Pi.single y 1 := by rw [hv]; simp
    have hvy : v y = Pi.single x 1 - Pi.single y 1 := by
      rw [hv]; simp [Ne.symm hxy]
    have hvz : ∀ z, z ≠ x → z ≠ y → v z = Pi.single z 1 := by
      intro z h1 h2; rw [hv]; simp [h1, h2]
    have hμx : μ x = 1 := by rw [hμ]; simp
    have hμy : μ y = -1 := by rw [hμ]; simp [Ne.symm hxy]
    have hμz : ∀ z, z ≠ x → z ≠ y → μ z = 0 := by
      intro z h1 h2; rw [hμ]; simp [h1, h2]
    refine norm_le_of_eigenvector_family (pairMatrix_isHermitian x y) v μ
      zero_le_one ?_ ?_ ?_
    · intro z
      by_cases hzx : z = x
      · rw [hzx, hvx, hμx, hmul]
        funext w
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, one_mul]
        by_cases hwx : w = x <;> by_cases hwy : w = y
        · exact absurd (hwx.symm.trans hwy) hxy
        · simp [hwx, hxy, Ne.symm hxy]
        · simp [hwy, hxy, Ne.symm hxy]
        · simp [hwx, hwy, Ne.symm hwx, Ne.symm hwy]
      · by_cases hzy : z = y
        · rw [hzy, hvy, hμy, hmul]
          funext w
          simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
          by_cases hwx : w = x <;> by_cases hwy : w = y
          · exact absurd (hwx.symm.trans hwy) hxy
          · simp [hwx, hxy, Ne.symm hxy]
          · simp [hwy, hxy, Ne.symm hxy]
          · simp [hwx, hwy, Ne.symm hwx, Ne.symm hwy]
        · rw [hvz z hzx hzy, hμz z hzx hzy, hmul]
          funext w
          simp [Pi.single_apply, Ne.symm hzx, Ne.symm hzy]
    · rw [eq_top_iff, ← (Pi.basisFun ℝ (ι → σ)).span_eq]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨z, rfl⟩
      rw [Pi.basisFun_apply]
      by_cases hzx : z = x
      · rw [hzx]
        have hx2 : (Pi.single x 1 : (ι → σ) → ℝ)
            = (2⁻¹ : ℝ) • (v x + v y) := by
          rw [hvx, hvy]
          funext w
          simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
          ring
        rw [hx2]
        exact Submodule.smul_mem _ _ (Submodule.add_mem _
          (Submodule.subset_span ⟨x, rfl⟩) (Submodule.subset_span ⟨y, rfl⟩))
      · by_cases hzy : z = y
        · rw [hzy]
          have hy2 : (Pi.single y 1 : (ι → σ) → ℝ)
              = (2⁻¹ : ℝ) • (v x - v y) := by
            rw [hvx, hvy]
            funext w
            simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
            ring
          rw [hy2]
          exact Submodule.smul_mem _ _ (Submodule.sub_mem _
            (Submodule.subset_span ⟨x, rfl⟩) (Submodule.subset_span ⟨y, rfl⟩))
        · rw [← hvz z hzx hzy]
          exact Submodule.subset_span ⟨z, rfl⟩
    · intro z
      simp only [hμ]
      split_ifs <;> norm_num
  · have h := abs_entry_le_l2_opNorm (pairMatrix x y) x y
    have hval : pairMatrix x y x y = 1 := by
      simp [pairMatrix, Ne.symm hxy]
    rw [hval] at h
    simpa using h

theorem one_le_advPM {x y : ι → σ} (hf : f x ≠ f y) : 1 ≤ advPM f := by
  have hxy : x ≠ y := fun h => hf (by rw [h])
  have hadv : IsAdvMatrix f (pairMatrix x y) := by
    refine ⟨pairMatrix_isHermitian x y, ?_⟩
    intro a b hab
    by_cases h1 : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := h1
      exact absurd hab hf
    · by_cases h2 : y = a ∧ x = b
      · obtain ⟨rfl, rfl⟩ := h2
        exact absurd hab.symm hf
      · simp [pairMatrix, h1, h2]
  have hfeas : ∀ i, ‖pairMatrix x y ⊙ advD i‖ ≤ 1 := by
    intro i
    by_cases hi : x i = y i
    · have h0 : pairMatrix x y ⊙ advD i = 0 := by
        ext a b
        rw [Matrix.hadamard_apply, Matrix.zero_apply, advD_apply]
        by_cases h1 : x = a ∧ y = b
        · obtain ⟨rfl, rfl⟩ := h1
          rw [ite_eq_left hi, mul_zero]
        · by_cases h2 : y = a ∧ x = b
          · obtain ⟨rfl, rfl⟩ := h2
            rw [ite_eq_left hi.symm, mul_zero]
          · have hz : pairMatrix x y a b = 0 := by
              simp [pairMatrix, h1, h2]
            rw [hz, zero_mul]
      rw [h0, norm_zero]
      exact zero_le_one
    · have h1 : pairMatrix x y ⊙ advD i = pairMatrix x y := by
        ext a b
        rw [Matrix.hadamard_apply, advD_apply]
        by_cases h1 : x = a ∧ y = b
        · obtain ⟨rfl, rfl⟩ := h1
          rw [ite_eq_right hi, mul_one]
        · by_cases h2 : y = a ∧ x = b
          · obtain ⟨rfl, rfl⟩ := h2
            rw [ite_eq_right (fun h => hi h.symm), mul_one]
          · have hz : pairMatrix x y a b = 0 := by
              simp [pairMatrix, h1, h2]
            rw [hz, zero_mul]
      rw [h1, norm_pairMatrix hxy]
  have h := le_advPM hadv hfeas
  rwa [norm_pairMatrix hxy] at h

theorem advPM_eq_zero_iff : advPM f = 0 ↔ ∀ x y, f x = f y := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨x, y, hxy⟩ := hc
    have h1 := one_le_advPM hxy
    rw [h] at h1
    norm_num at h1
  · exact advPM_eq_zero_of_forall_eq

end QuantumQueryComplexity

end SourceBasic

section SourceBipartite

/-!
# Bipartite support structure of adversary matrices

An adversary matrix `N` for `g` vanishes on same-colored pairs (`g u = g v`),
so it maps vectors supported on one color class into the other class.
Consequently an eigenvector with nonzero eigenvalue must have nonzero
restriction to *both* color classes (`brestrict_ne_zero`,
`IsAdvMatrix.exists_eigenvector_support`).  This is the nonvanishing input to
the `≥` direction of the composed-matrix norm formula (HLŠ Lemma 16).
-/


namespace QuantumQueryComplexity

open Matrix

variable {U : Type*} [Fintype U]

/-- Restriction of a vector to a color class of the coloring `χ`. -/
@[expose]
def brestrict (χ : U → Bool) (b : Bool) (w : U → ℝ) : U → ℝ :=
  fun u => if χ u = b then w u else 0

omit [Fintype U] in
@[simp] lemma brestrict_apply (χ : U → Bool) (b : Bool) (w : U → ℝ) (u : U) :
    brestrict χ b w u = if χ u = b then w u else 0 := rfl

omit [Fintype U] in
lemma brestrict_add_not (χ : U → Bool) (b : Bool) (w : U → ℝ) :
    brestrict χ b w + brestrict χ (!b) w = w := by
  funext u
  simp only [Pi.add_apply, brestrict_apply]
  cases hb : χ u <;> cases b <;> simp

/-- A matrix vanishing on same-colored pairs maps a `b`-supported vector to a
`!b`-supported one, with the values of the full product. -/
lemma mulVec_brestrict {M : Matrix U U ℝ} {χ : U → Bool}
    (hM : ∀ u v, χ u = χ v → M u v = 0) (w : U → ℝ) (b : Bool) :
    M *ᵥ brestrict χ b w = brestrict χ (!b) (M *ᵥ w) := by
  funext u
  simp only [Matrix.mulVec, dotProduct, brestrict_apply, mul_ite, mul_zero]
  by_cases hu : χ u = b
  · rw [ite_eq_right (by rw [hu]; cases b <;> simp)]
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : χ v = b
    · rw [ite_eq_left hv, hM u v (hu.trans hv.symm), zero_mul]
    · rw [ite_eq_right hv]
  · have hu' : χ u = !b := by cases hcu : χ u <;> cases b <;> simp_all
    rw [ite_eq_left hu']
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : χ v = b
    · rw [ite_eq_left hv]
    · have hv' : χ v = χ u := by
        cases hcv : χ v <;> cases hcu : χ u <;> cases b <;> simp_all
      rw [ite_eq_right hv, hM u v hv'.symm, zero_mul]

lemma mulVec_brestrict_eigen {M : Matrix U U ℝ} {χ : U → Bool}
    (hM : ∀ u v, χ u = χ v → M u v = 0) {w : U → ℝ} {θ : ℝ}
    (hw : M *ᵥ w = θ • w) (b : Bool) :
    M *ᵥ brestrict χ b w = θ • brestrict χ (!b) w := by
  rw [mulVec_brestrict hM, hw]
  funext u
  by_cases h : χ u = !b <;> simp [brestrict_apply, h]

/-- An eigenvector with nonzero eigenvalue of a color-bipartite matrix has
nonzero restriction to each color class. -/
theorem brestrict_ne_zero {M : Matrix U U ℝ} {χ : U → Bool}
    (hM : ∀ u v, χ u = χ v → M u v = 0) {w : U → ℝ} {θ : ℝ}
    (hw : M *ᵥ w = θ • w) (hθ : θ ≠ 0) (hw0 : w ≠ 0) (b : Bool) :
    brestrict χ b w ≠ 0 := by
  intro hb
  have h1 : θ • brestrict χ (!b) w = 0 := by
    rw [← mulVec_brestrict_eigen hM hw b, hb, Matrix.mulVec_zero]
  have h2 : brestrict χ (!b) w = 0 := by
    rcases smul_eq_zero.mp h1 with h | h
    · exact absurd h hθ
    · exact h
  exact hw0 (by rw [← brestrict_add_not χ b w, hb, h2, add_zero])

/-- Wrapper for the composition layer: an eigenvector with nonzero eigenvalue
of an adversary matrix for `g` has support in every color class of `g`. -/
theorem IsAdvMatrix.exists_eigenvector_support {ι : Type*} [Fintype ι]
    [DecidableEq ι] {g : (ι → Bool) → Bool}
    {N : Matrix (ι → Bool) (ι → Bool) ℝ} (hN : IsAdvMatrix g N)
    {v : (ι → Bool) → ℝ} {θ : ℝ} (hv : N *ᵥ v = θ • v) (hθ : θ ≠ 0)
    (hv0 : v ≠ 0) (a : Bool) : ∃ u, g u = a ∧ v u ≠ 0 := by
  have h := brestrict_ne_zero (fun u w' huw => hN.2 u w' huw) hv hθ hv0 a
  obtain ⟨u, hu⟩ := Function.ne_iff.mp h
  simp only [brestrict_apply, Pi.zero_apply] at hu
  by_cases hgu : g u = a
  · rw [ite_eq_left hgu] at hu
    exact ⟨u, hgu, hu⟩
  · rw [ite_eq_right hgu] at hu
    exact absurd rfl hu

end QuantumQueryComplexity

end SourceBipartite

section SourceSchurMultiplier

/-!
# The Schur-multiplier norm bound

The key estimate `‖X ⊙ P‖ ≤ d * ‖X‖` for a positive semidefinite `P` whose
diagonal entries are at most `d` (`norm_hadamard_posSemidef_le`), proved via a
Gram decomposition of `P` and Cauchy–Schwarz.  In the composition theorem this
replaces the sign-flipping analysis of HLŠ Lemma 16 (following the PSD
viewpoint of Belovs–Lee, arXiv:2004.06439 §4).

Also: small PSD facts — the all-ones matrix, the `2×2` seed
`[[R, λ], [λ, R]]` for `|λ| ≤ R`, and `M + ‖M‖ • 1 ≥ 0` for symmetric `M`
(BL Lemma 18).  The "PSD lift" fact (BL Fact 2) is mathlib's
`Matrix.PosSemidef.submatrix`, which takes an arbitrary index map.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {n : Type*} [Fintype n]

omit [Fintype n] in
/-- The all-ones matrix is positive semidefinite. -/
lemma posSemidef_allOnes [Finite n] :
    (Matrix.of fun _ _ : n => (1 : ℝ)).PosSemidef := by
  classical
  let := Fintype.ofFinite n
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · change _ᴴ = _
    ext i j
    simp [Matrix.conjTranspose_apply]
  · have hmul : (Matrix.of fun _ _ : n => (1 : ℝ)) *ᵥ x
        = fun _ => ∑ j, x j := by
      funext i
      simp [Matrix.mulVec, dotProduct]
    rw [star_trivial, hmul]
    have hdp : x ⬝ᵥ (fun _ => ∑ j, x j) = (∑ i, x i) * (∑ j, x j) := by
      simp [dotProduct, ← Finset.sum_mul]
    rw [hdp]
    exact mul_self_nonneg _

/-- The `2×2` seed: `[[R, lam], [lam, R]]` is PSD when `|lam| ≤ R`. -/
lemma posSemidef_boolPair {R lam : ℝ} (h : |lam| ≤ R) :
    (Matrix.of fun a b : Bool => if a = b then R else lam).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · change _ᴴ = _
    ext a b
    simp [Matrix.conjTranspose_apply, eq_comm]
  · rw [star_trivial]
    rcases abs_le.mp h with ⟨h1, h2⟩
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_bool, Matrix.of_apply]
    norm_num
    nlinarith [sq_nonneg (x true + x false), sq_nonneg (x true - x false)]

variable [DecidableEq n]

/-- **Schur-multiplier bound** (Belovs–Lee): if `P` is positive semidefinite
with all diagonal entries at most `d`, then `‖X ⊙ P‖ ≤ d * ‖X‖`. -/
theorem norm_hadamard_posSemidef_le (X : Matrix n n ℝ) {P : Matrix n n ℝ}
    (hP : P.PosSemidef) {d : ℝ} (hd : 0 ≤ d) (hdiag : ∀ a, P a a ≤ d) :
    ‖X ⊙ P‖ ≤ d * ‖X‖ := by
  obtain ⟨m, gv, hgv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hP
  have hPab : ∀ a b, P a b = ∑ k, gv k a * gv k b := by
    intro a b
    rw [hgv]
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
  refine l2_opNorm_le_of_forall_dotProduct _ (mul_nonneg hd (norm_nonneg X))
    fun x y => ?_
  -- Step 1: expand the bilinear form along the Gram decomposition.
  have step1 : x ⬝ᵥ (X ⊙ P) *ᵥ y
      = ∑ k, (fun a => gv k a * x a) ⬝ᵥ X *ᵥ (fun b => gv k b * y b) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.hadamard_apply, Finset.mul_sum]
    have e1 : ∀ a b, x a * (X a b * P a b * y b)
        = ∑ k, (gv k a * x a) * (X a b * (gv k b * y b)) := by
      intro a b
      rw [hPab a b]
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    calc ∑ a, ∑ b, x a * (X a b * P a b * y b)
        = ∑ a, ∑ b, ∑ k, (gv k a * x a) * (X a b * (gv k b * y b)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e1 a b
      _ = ∑ a, ∑ k, ∑ b, (gv k a * x a) * (X a b * (gv k b * y b)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ b, (gv k a * x a) * (X a b * (gv k b * y b)) :=
          Finset.sum_comm
  rw [step1]
  -- Notation for the reweighted vectors and their lengths.
  set xk : Fin m → n → ℝ := fun k a => gv k a * x a with hxk
  set yk : Fin m → n → ℝ := fun k b => gv k b * y b with hyk
  -- Step 5 (used twice): the total squared length is controlled by the
  -- diagonal of `P`.
  have hlen : ∀ (z : n → ℝ) (zk : Fin m → n → ℝ),
      (∀ k a, zk k a = gv k a * z a) →
      ∑ k, zk k ⬝ᵥ zk k ≤ d * (z ⬝ᵥ z) := by
    intro z zk hzk
    have hz : ∑ k, zk k ⬝ᵥ zk k = ∑ a, (z a * z a) * P a a := by
      simp only [dotProduct, hzk]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hPab a a, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hz]
    calc ∑ a, (z a * z a) * P a a ≤ ∑ a, (z a * z a) * d :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hdiag a) (mul_self_nonneg _)
      _ = d * (z ⬝ᵥ z) := by
        rw [← Finset.sum_mul, mul_comm]
        rfl
  -- Steps 2–4: triangle inequality, the master bound per `k`, and
  -- Cauchy–Schwarz over `k`.
  calc |∑ k, xk k ⬝ᵥ X *ᵥ yk k|
      ≤ ∑ k, |xk k ⬝ᵥ X *ᵥ yk k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ‖X‖ * (Real.sqrt (xk k ⬝ᵥ xk k) * Real.sqrt (yk k ⬝ᵥ yk k)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have := abs_dotProduct_mulVec_le X (xk k) (yk k)
        calc |xk k ⬝ᵥ X *ᵥ yk k|
            ≤ ‖X‖ * Real.sqrt (xk k ⬝ᵥ xk k) * Real.sqrt (yk k ⬝ᵥ yk k) := this
          _ = ‖X‖ * (Real.sqrt (xk k ⬝ᵥ xk k) * Real.sqrt (yk k ⬝ᵥ yk k)) :=
              mul_assoc _ _ _
    _ = ‖X‖ * ∑ k, Real.sqrt (xk k ⬝ᵥ xk k) * Real.sqrt (yk k ⬝ᵥ yk k) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ‖X‖ * (Real.sqrt (∑ k, xk k ⬝ᵥ xk k) * Real.sqrt (∑ k, yk k ⬝ᵥ yk k)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg X)
        have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun k => Real.sqrt (xk k ⬝ᵥ xk k)) (fun k => Real.sqrt (yk k ⬝ᵥ yk k))
        simpa [Real.sq_sqrt (dotProduct_self_nonneg _)] using hcs
    _ ≤ ‖X‖ * (Real.sqrt (d * (x ⬝ᵥ x)) * Real.sqrt (d * (y ⬝ᵥ y))) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg X)
        exact mul_le_mul (Real.sqrt_le_sqrt (hlen x xk fun k a => rfl))
          (Real.sqrt_le_sqrt (hlen y yk fun k a => rfl)) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = d * ‖X‖ * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
        rw [Real.sqrt_mul hd, Real.sqrt_mul hd]
        rw [show Real.sqrt d * Real.sqrt (x ⬝ᵥ x) *
            (Real.sqrt d * Real.sqrt (y ⬝ᵥ y))
            = Real.sqrt d * Real.sqrt d *
              (Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) from by ring,
          Real.mul_self_sqrt hd]
        ring

/-- `M + ‖M‖ • 1` is positive semidefinite for symmetric `M`
(BL Lemma 18). -/
theorem posSemidef_add_norm_smul_one {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    (M + ‖M‖ • (1 : Matrix n n ℝ)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hM.add (Matrix.isHermitian_one.smul (star_trivial _))) fun x => ?_
  rw [star_trivial, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul]
  have h1 := abs_dotProduct_mulVec_le M x x
  have h2 := Real.mul_self_sqrt (dotProduct_self_nonneg x)
  have h3 := neg_abs_le (x ⬝ᵥ M *ᵥ x)
  rw [smul_eq_mul]
  nlinarith [Real.sqrt_nonneg (x ⬝ᵥ x), norm_nonneg M]

end QuantumQueryComplexity

end SourceSchurMultiplier

section SourceCompositionHat

/-!
# The composed adversary matrix (hat formulation)

Following Belovs–Lee (arXiv:2004.06439, Definitions 17 and 19), the composed
adversary matrix for `h = f ∘ gᵏ` is built from an outer matrix `Γf` and inner
matrices `M i` via `hat N = N + ‖N‖ • 1`:

  `compose g Γf M x y = Γf (tilde g x) (tilde g y) * ∏ i, hat (M i) (x·ᵢ) (y·ᵢ)`

For a g-shaped `N` (symmetric, vanishing on pairs with `g u = g v`), `hat N`
agrees entrywise with the color-block convention of HLŠ Definition 6:
same-color blocks are `‖N‖·I`, different-color blocks are `N`.

## The block decomposition is abstract

The inner inputs are **not** assumed to form a Boolean cube.  Everything below
is stated for a composed input type `Z` equipped with an equivalence
`e : Z ≃ (α → Y)` onto tuples of inner inputs drawn from an arbitrary finite
type `Y`, with a colouring `g : α → Y → Bool`.

This permits composition of *promise* problems whose inner inputs range over a
subtype rather than a cube. The spectral content never sees the cube: the two
places two-valuedness is used are the colouring's **output** and the outer cube
`α → Bool`, and both survive.

The original cube statements are recovered verbatim as the instance
`e := cubeBlocks α β`, so no downstream file changes.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

lemma isHermitian_apply_symm {n : Type*} {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (a b : n) : A a b = A b a := by
  conv_lhs => rw [← hA.eq]
  simp [Matrix.conjTranspose_apply]

/-! ## The hat matrix -/

/-- BL Definition 17 in additive form: `hat N = N + ‖N‖ • 1`. -/
noncomputable def hat {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℝ) : Matrix n n ℝ :=
  N + ‖N‖ • (1 : Matrix n n ℝ)

lemma hat_apply {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n ℝ)
    (u v : n) : hat N u v = N u v + ‖N‖ * (if u = v then 1 else 0) := by
  simp [hat, Matrix.one_apply]

lemma hat_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    {N : Matrix n n ℝ} (hN : N.IsHermitian) : (hat N).IsHermitian :=
  hN.add (Matrix.isHermitian_one.smul (star_trivial _))

/-! ## Composition over an abstract block decomposition -/

section General

variable {α Y Z : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- The `i`-th block of a composed input. -/
@[expose]
def sliceE (e : Z ≃ (α → Y)) (z : Z) (i : α) : Y := e z i

/-- The vector of inner-function values of a composed input. -/
@[expose]
def tildeE (e : Z ≃ (α → Y)) (g : α → Y → Bool) (z : Z) : α → Bool :=
  fun i => g i (sliceE e z i)

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq α] [Fintype Y] [Fintype Z] [Fintype α] in
@[simp] lemma sliceE_apply (e : Z ≃ (α → Y)) (z : Z) (i : α) :
    sliceE e z i = e z i := rfl

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq α] [Fintype Y] [Fintype Z] [Fintype α] in
@[simp] lemma tildeE_apply (e : Z ≃ (α → Y)) (g : α → Y → Bool) (z : Z)
    (i : α) : tildeE e g z i = g i (sliceE e z i) := rfl

/-- BL Definition 19 over an abstract block decomposition. -/
@[expose]
noncomputable def composeE (e : Z ≃ (α → Y)) (g : α → Y → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ) (M : α → Matrix Y Y ℝ) :
    Matrix Z Z ℝ :=
  Matrix.of fun x y =>
    Γf (tildeE e g x) (tildeE e g y) * ∏ i, hat (M i) (sliceE e x i) (sliceE e y i)

omit [DecidableEq Z] [DecidableEq α] [Fintype Z] in
@[simp] lemma composeE_apply (e : Z ≃ (α → Y)) (g : α → Y → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ) (M : α → Matrix Y Y ℝ) (x y : Z) :
    composeE e g Γf M x y
      = Γf (tildeE e g x) (tildeE e g y)
        * ∏ i, hat (M i) (sliceE e x i) (sliceE e y i) := rfl

omit [DecidableEq Z] [DecidableEq α] [Fintype Z] in
lemma composeE_isHermitian (e : Z ≃ (α → Y)) (g : α → Y → Bool)
    {Γf : Matrix (α → Bool) (α → Bool) ℝ} {M : α → Matrix Y Y ℝ}
    (hΓf : Γf.IsHermitian) (hM : ∀ i, (M i).IsHermitian) :
    (composeE e g Γf M).IsHermitian := by
  change (composeE e g Γf M)ᴴ = composeE e g Γf M
  ext x y
  simp only [Matrix.conjTranspose_apply, composeE_apply, star_trivial]
  rw [isHermitian_apply_symm hΓf (tildeE e g y) (tildeE e g x)]
  congr 1
  exact Finset.prod_congr rfl fun i _ =>
    isHermitian_apply_symm (hat_isHermitian (hM i)) _ _

end General

/-! ## The cube instance

The original statements, recovered by taking the block decomposition to be the
currying equivalence. -/

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The block decomposition of a Boolean cube into `α` blocks of shape `β`. -/
@[expose]
def cubeBlocks (α β : Type*) : ((α × β) → Bool) ≃ (α → (β → Bool)) :=
  Equiv.curry α β Bool

/-- The `i`-th block of a composed input. -/
@[expose]
def slice (x : (α × β) → Bool) (i : α) : β → Bool := sliceE (cubeBlocks α β) x i

/-- The vector of inner-function values of a composed input. -/
@[expose]
def tilde (g : α → (β → Bool) → Bool) (x : (α × β) → Bool) : α → Bool :=
  tildeE (cubeBlocks α β) g x

/-- The constant family of inner functions (the uniform case). -/
abbrev constFam (g : (β → Bool) → Bool) : α → (β → Bool) → Bool := fun _ => g

omit [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] in
@[simp] lemma slice_apply (x : (α × β) → Bool) (i : α) (j : β) :
    slice x i j = x (i, j) := rfl

omit [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] in
@[simp] lemma tilde_apply (g : α → (β → Bool) → Bool) (x : (α × β) → Bool)
    (i : α) : tilde g x i = g i (slice x i) := rfl

/-- BL Definition 19, uniform-alphabet form: the composed matrix. -/
@[expose]
noncomputable def compose (g : α → (β → Bool) → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    (M : α → Matrix (β → Bool) (β → Bool) ℝ) :
    Matrix ((α × β) → Bool) ((α × β) → Bool) ℝ :=
  composeE (cubeBlocks α β) g Γf M

omit [DecidableEq α] in
@[simp] lemma compose_apply (g : α → (β → Bool) → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    (M : α → Matrix (β → Bool) (β → Bool) ℝ) (x y : (α × β) → Bool) :
    compose g Γf M x y
      = Γf (tilde g x) (tilde g y) * ∏ i, hat (M i) (slice x i) (slice y i) :=
  rfl

omit [DecidableEq α] in
lemma compose_isHermitian (g : α → (β → Bool) → Bool)
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (β → Bool) (β → Bool) ℝ}
    (hΓf : Γf.IsHermitian) (hM : ∀ i, (M i).IsHermitian) :
    (compose g Γf M).IsHermitian := by
  classical
  exact composeE_isHermitian _ g hΓf hM

end QuantumQueryComplexity

end SourceCompositionHat

section SourceDual

/-!
# The dual (minimisation) form of the adversary bound

The dual of the adversary SDP (Lee–Mittal–Reichardt–Špalek–Szegedy; stated as
Theorem 7 of Belovs–Lee, arXiv:2004.06439) asks for two families of vectors
`u x i`, `v x i` indexed by inputs `x` and query positions `i`, satisfying

  `∑_{i : x i ≠ y i} ⟪u x i, v y i⟫ = 1` if `g x ≠ g y`, and `= 0` if `g x = g y`,

with objective `max_x ∑_i ‖u x i‖²` (and the same for `v`).  The constraints
on pairs with `g x = g y` are the extra ones isolated by LMRSS; they are what
makes dual solutions *compose*.

This section defines feasible dual solutions (`DualPair`), the dual value
`advDual` as an infimum of costs, and proves **weak duality**
`advPM g ≤ advDual g` (`advPM_le_advDual`) by the same Gram-plus-Cauchy–Schwarz
argument that underlies the Schur-multiplier bound.

Strong duality is proved later in `SourceDualityMain` by Hahn–Banach separation:
`advDual_eq_advPM` identifies the two values, and `advPM_composeFun_eq` gives
unconditional exact Boolean block composition.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} [DecidableEq O]

/-- A feasible solution of the dual program for `g`, with vectors of
dimension `K`.  `DecidableEq σ` is what makes the coordinate mask
`if x i = y i` meaningful, and `DecidableEq O` the output test
`if g x = g y`; no finiteness of `σ` is needed here, since the constraint
never sums over inputs. -/
structure DualPair {ι : Type*} [Fintype ι] {σ : Type*} [DecidableEq σ]
    {O : Type*} [DecidableEq O] (K : Type*) [Fintype K]
    (g : (ι → σ) → O) where
  /-- The first vector family. -/
  u : (ι → σ) → ι → K → ℝ
  /-- The second vector family. -/
  v : (ι → σ) → ι → K → ℝ
  /-- The dual feasibility constraint, including the LMRSS constraints on
  pairs with equal `g`-value. -/
  constraint : ∀ x y : ι → σ,
    (∑ i, if x i = y i then 0 else ∑ k, u x i k * v y i k)
      = if g x = g y then 0 else 1

namespace DualPair

variable {K K' : Type*} [Fintype K] [Fintype K'] {g : (ι → σ) → O}

/-- The cost of a dual solution is bounded by `c`. -/
def IsCostLe (P : DualPair K g) (c : ℝ) : Prop :=
  (∀ x, ∑ i, ∑ k, P.u x i k * P.u x i k ≤ c) ∧
  (∀ x, ∑ i, ∑ k, P.v x i k * P.v x i k ≤ c)

omit [DecidableEq ι] [Fintype σ] in
lemma IsCostLe.mono {P : DualPair K g} {c d : ℝ} (h : P.IsCostLe c)
    (hcd : c ≤ d) : P.IsCostLe d :=
  ⟨fun x => (h.1 x).trans hcd, fun x => (h.2 x).trans hcd⟩

omit [DecidableEq ι] [Fintype σ] in
lemma isCostLe_nonneg [Nonempty σ] {P : DualPair K g} {c : ℝ}
    (h : P.IsCostLe c) : 0 ≤ c := by
  classical
  obtain ⟨x⟩ : Nonempty (ι → σ) := inferInstance
  refine le_trans ?_ (h.1 x)
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun k _ => mul_self_nonneg _

/-- Transporting a dual solution along a bijection of the dimension type. -/
def reindex (P : DualPair K g) (e : K ≃ K') : DualPair K' g where
  u x i k' := P.u x i (e.symm k')
  v x i k' := P.v x i (e.symm k')
  constraint x y := by
    rw [← P.constraint x y]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : x i = y i
    · rw [ite_eq_left hi, ite_eq_left hi]
    · rw [ite_eq_right hi, ite_eq_right hi]
      exact Fintype.sum_equiv e.symm _ _ fun k' => rfl

omit [DecidableEq ι] [Fintype σ] in
lemma reindex_isCostLe {P : DualPair K g} {c : ℝ} (h : P.IsCostLe c)
    (e : K ≃ K') : (P.reindex e).IsCostLe c := by
  constructor
  · intro x
    refine le_trans (le_of_eq ?_) (h.1 x)
    exact Finset.sum_congr rfl fun i _ =>
      Fintype.sum_equiv e.symm _ _ fun k' => rfl
  · intro x
    refine le_trans (le_of_eq ?_) (h.2 x)
    exact Finset.sum_congr rfl fun i _ =>
      Fintype.sum_equiv e.symm _ _ fun k' => rfl

end DualPair

/-! ## Weak duality -/

/-! The two estimates behind weak duality are stated for an arbitrary finite
type `X` of inputs rather than for the cube `ι → σ`.  Nothing in them uses the
product structure — only that the matrices are indexed by inputs — and the extra
generality is what lets `SourcePromiseDefs` reuse them verbatim for a
promise domain. -/

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] [DecidableEq ι] in
lemma sum_reweight_le {K : Type*} [Fintype K]
    (w : X → ℝ) (U : X → ι → K → ℝ) {c : ℝ}
    (h : ∀ x, ∑ i, ∑ k, U x i k * U x i k ≤ c) :
    (∑ p : ι × K, (fun x => w x * U x p.1 p.2) ⬝ᵥ
      (fun x => w x * U x p.1 p.2)) ≤ c * (w ⬝ᵥ w) := by
  have hstep : (∑ p : ι × K, (fun x => w x * U x p.1 p.2) ⬝ᵥ
      (fun x => w x * U x p.1 p.2))
      = ∑ x, (w x * w x) * ∑ i, ∑ k, U x i k * U x i k := by
    calc (∑ p : ι × K, (fun x => w x * U x p.1 p.2) ⬝ᵥ
          (fun x => w x * U x p.1 p.2))
        = ∑ i, ∑ k, ∑ x, (w x * w x) * (U x i k * U x i k) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
          simp only [dotProduct]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ = ∑ i, ∑ x, ∑ k, (w x * w x) * (U x i k * U x i k) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ x, ∑ i, ∑ k, (w x * w x) * (U x i k * U x i k) := Finset.sum_comm
      _ = ∑ x, (w x * w x) * ∑ i, ∑ k, U x i k * U x i k := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  rw [hstep]
  calc ∑ x, (w x * w x) * ∑ i, ∑ k, U x i k * U x i k
      ≤ ∑ x, (w x * w x) * c :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (h x) (mul_self_nonneg _)
    _ = c * (w ⬝ᵥ w) := by rw [← Finset.sum_mul, mul_comm]; rfl

omit [DecidableEq ι] in
/-- The core estimate of weak duality: a sum of bilinear forms of norm at
most one, reweighted by dual vectors of cost at most `c`, is bounded by
`c` times the product of the vector lengths. -/
lemma key_bound {K : Type*} [Fintype K]
    (M : ι → Matrix X X ℝ) (hM : ∀ i, ‖M i‖ ≤ 1)
    (a b : X → ℝ) (U V : X → ι → K → ℝ) {c : ℝ}
    (hc : 0 ≤ c)
    (hU : ∀ x, ∑ i, ∑ k, U x i k * U x i k ≤ c)
    (hV : ∀ x, ∑ i, ∑ k, V x i k * V x i k ≤ c) :
    |∑ p : ι × K, (fun x => a x * U x p.1 p.2) ⬝ᵥ
        M p.1 *ᵥ (fun y => b y * V y p.1 p.2)|
      ≤ c * Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) := by
  classical
  calc |∑ p : ι × K, (fun x => a x * U x p.1 p.2) ⬝ᵥ
          M p.1 *ᵥ (fun y => b y * V y p.1 p.2)|
      ≤ ∑ p : ι × K, |(fun x => a x * U x p.1 p.2) ⬝ᵥ
          M p.1 *ᵥ (fun y => b y * V y p.1 p.2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : ι × K,
          Real.sqrt ((fun x => a x * U x p.1 p.2) ⬝ᵥ
            (fun x => a x * U x p.1 p.2)) *
          Real.sqrt ((fun y => b y * V y p.1 p.2) ⬝ᵥ
            (fun y => b y * V y p.1 p.2)) := by
        refine Finset.sum_le_sum fun p _ => ?_
        refine (abs_dotProduct_mulVec_le _ _ _).trans ?_
        have h1 : ‖M p.1‖ * Real.sqrt ((fun x => a x * U x p.1 p.2) ⬝ᵥ
              (fun x => a x * U x p.1 p.2))
            ≤ 1 * Real.sqrt ((fun x => a x * U x p.1 p.2) ⬝ᵥ
              (fun x => a x * U x p.1 p.2)) :=
          mul_le_mul_of_nonneg_right (hM p.1) (Real.sqrt_nonneg _)
        calc ‖M p.1‖ * Real.sqrt ((fun x => a x * U x p.1 p.2) ⬝ᵥ
              (fun x => a x * U x p.1 p.2)) *
              Real.sqrt ((fun y => b y * V y p.1 p.2) ⬝ᵥ
                (fun y => b y * V y p.1 p.2))
            ≤ 1 * Real.sqrt ((fun x => a x * U x p.1 p.2) ⬝ᵥ
                (fun x => a x * U x p.1 p.2)) *
              Real.sqrt ((fun y => b y * V y p.1 p.2) ⬝ᵥ
                (fun y => b y * V y p.1 p.2)) :=
              mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
          _ = _ := by ring
    _ ≤ Real.sqrt (∑ p : ι × K, (fun x => a x * U x p.1 p.2) ⬝ᵥ
            (fun x => a x * U x p.1 p.2)) *
          Real.sqrt (∑ p : ι × K, (fun y => b y * V y p.1 p.2) ⬝ᵥ
            (fun y => b y * V y p.1 p.2)) := by
        have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun p : ι × K => Real.sqrt ((fun x => a x * U x p.1 p.2) ⬝ᵥ
            (fun x => a x * U x p.1 p.2)))
          (fun p : ι × K => Real.sqrt ((fun y => b y * V y p.1 p.2) ⬝ᵥ
            (fun y => b y * V y p.1 p.2)))
        simpa [Real.sq_sqrt (dotProduct_self_nonneg _)] using hcs
    _ ≤ Real.sqrt (c * (a ⬝ᵥ a)) * Real.sqrt (c * (b ⬝ᵥ b)) :=
        mul_le_mul (Real.sqrt_le_sqrt (sum_reweight_le a U hU))
          (Real.sqrt_le_sqrt (sum_reweight_le b V hV))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = c * Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) := by
        rw [Real.sqrt_mul hc, Real.sqrt_mul hc]
        rw [show Real.sqrt c * Real.sqrt (a ⬝ᵥ a) *
            (Real.sqrt c * Real.sqrt (b ⬝ᵥ b))
            = Real.sqrt c * Real.sqrt c *
              (Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b)) from by ring,
          Real.mul_self_sqrt hc]
        ring

/-- **Weak duality**: every feasible dual solution of cost at most `c` bounds
the adversary bound by `c`. -/
theorem advPM_le_of_dualPair {K : Type*} [Fintype K] {g : (ι → σ) → O}
    (P : DualPair K g) {c : ℝ} (hc : 0 ≤ c) (hP : P.IsCostLe c) :
    advPM g ≤ c := by
  refine advPM_le fun Γ hΓ hΓD => ?_
  refine l2_opNorm_le_of_forall_dotProduct Γ hc fun a b => ?_
  have hsplit : ∀ x y, a x * Γ x y * b y
      = ∑ p : ι × K, (a x * P.u x p.1 p.2) * (Γ ⊙ advD p.1) x y *
          (b y * P.v y p.1 p.2) := by
    intro x y
    rw [Fintype.sum_prod_type]
    change a x * Γ x y * b y
      = ∑ i, ∑ k, (a x * P.u x i k) * (Γ ⊙ advD i) x y * (b y * P.v y i k)
    have hstep : ∀ i : ι,
        (∑ k, (a x * P.u x i k) * (Γ ⊙ advD i) x y * (b y * P.v y i k))
        = (a x * b y * Γ x y) *
            (if x i = y i then 0 else ∑ k, P.u x i k * P.v y i k) := by
      intro i
      by_cases hi : x i = y i
      · rw [ite_eq_left hi, mul_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hadamard_advD_apply, ite_eq_left hi]
        ring
      · rw [ite_eq_right hi, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hadamard_advD_apply, ite_eq_right hi]
        ring
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
      ← Finset.mul_sum, P.constraint x y]
    by_cases hg : g x = g y
    · rw [ite_eq_left hg, hΓ.apply_eq_zero hg]
      ring
    · rw [ite_eq_right hg]
      ring
  have hexpand : a ⬝ᵥ Γ *ᵥ b
      = ∑ p : ι × K, (fun x => a x * P.u x p.1 p.2) ⬝ᵥ
          (fun i => Γ ⊙ advD i) p.1 *ᵥ (fun y => b y * P.v y p.1 p.2) := by
    rw [dotProduct_mulVec_eq_sum]
    have hrhs : (∑ p : ι × K, (fun x => a x * P.u x p.1 p.2) ⬝ᵥ
        (fun i => Γ ⊙ advD i) p.1 *ᵥ (fun y => b y * P.v y p.1 p.2))
        = ∑ p : ι × K, ∑ x, ∑ y, (a x * P.u x p.1 p.2) *
            (Γ ⊙ advD p.1) x y * (b y * P.v y p.1 p.2) :=
      Finset.sum_congr rfl fun p _ => dotProduct_mulVec_eq_sum _ _ _
    rw [hrhs]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => hsplit x y
  rw [hexpand]
  exact key_bound (fun i => Γ ⊙ advD i) hΓD a b P.u P.v hc hP.1 hP.2

/-! ## A feasible dual solution always exists -/

/-- The number of coordinates on which two inputs differ. -/
def diffCard (x y : ι → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card

omit [DecidableEq ι] in
lemma diffCard_ne_zero {x y : ι → Bool} (h : x ≠ y) : diffCard x y ≠ 0 := by
  rw [diffCard, Finset.card_ne_zero]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  exact ⟨i, by simp [hi]⟩

omit [DecidableEq ι] in
lemma sum_ite_diff_const (x y : ι → Bool) (C : ℝ) :
    (∑ i, if x i = y i then 0 else C) = (diffCard x y : ℝ) * C := by
  rw [show (∑ i, if x i = y i then (0:ℝ) else C)
      = ∑ i, if x i ≠ y i then C else 0 from
    Finset.sum_congr rfl fun i _ => by by_cases hi : x i = y i <;> simp [hi]]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- A dual solution of finite (very lossy) cost, showing the dual program is
always feasible: `u x i` is the standard basis vector of `x`, and the mass of
`v y i` is spread over the coordinates where the inputs differ. -/
noncomputable def trivialDual (g : (ι → Bool) → Bool) :
    DualPair (ι → Bool) g where
  u x _ k := if k = x then 1 else 0
  v y i k := if g k = g y then 0
    else (if k i = y i then 0 else (diffCard k y : ℝ)⁻¹)
  constraint x y := by
    by_cases hg : g x = g y
    · rw [ite_eq_left hg]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : x i = y i
      · rw [ite_eq_left hi]
      · rw [ite_eq_right hi]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k = x
        · subst hk
          simp [hg]
        · simp [hk]
    · rw [ite_eq_right hg]
      have hxy : x ≠ y := fun h => hg (by rw [h])
      trans (∑ i : ι, if x i = y i then (0:ℝ) else (diffCard x y : ℝ)⁻¹)
      · refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : x i = y i
        · rw [ite_eq_left hi, ite_eq_left hi]
        · rw [ite_eq_right hi, ite_eq_right hi]
          rw [Finset.sum_eq_single x]
          · simp [hg, hi]
          · intro k _ hk
            simp [hk]
          · intro h
            exact absurd (Finset.mem_univ _) h
      · rw [sum_ite_diff_const]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (diffCard_ne_zero hxy))

lemma trivialDual_isCostLe (g : (ι → Bool) → Bool) :
    (trivialDual g).IsCostLe
      ((Fintype.card ι : ℝ) + (Fintype.card (ι → Bool) : ℝ)) := by
  constructor
  · intro x
    change (∑ i : ι, ∑ k : ι → Bool,
      (if k = x then (1:ℝ) else 0) * (if k = x then (1:ℝ) else 0)) ≤ _
    have hk : ∀ i : ι, (∑ k : ι → Bool, (if k = x then (1:ℝ) else 0) *
        (if k = x then (1:ℝ) else 0)) = 1 := by
      intro i
      rw [Finset.sum_eq_single x]
      · norm_num
      · intro k _ hk
        rw [ite_eq_right hk]
        ring
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hk i,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have := Nat.cast_nonneg (α := ℝ) (Fintype.card (ι → Bool))
    linarith
  · intro y
    change (∑ i : ι, ∑ k : ι → Bool,
      (if g k = g y then (0:ℝ) else if k i = y i then 0
        else (diffCard k y : ℝ)⁻¹) *
      (if g k = g y then (0:ℝ) else if k i = y i then 0
        else (diffCard k y : ℝ)⁻¹)) ≤ _
    rw [Finset.sum_comm]
    have hbound : ∀ k : ι → Bool,
        (∑ i : ι, (if g k = g y then (0:ℝ) else if k i = y i then 0
            else (diffCard k y : ℝ)⁻¹) *
          (if g k = g y then (0:ℝ) else if k i = y i then 0
            else (diffCard k y : ℝ)⁻¹)) ≤ 1 := by
      intro k
      by_cases hgk : g k = g y
      · simp [hgk]
      · have hky : k ≠ y := fun h => hgk (by rw [h])
        have hN : (diffCard k y : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (diffCard_ne_zero hky)
        have hN1 : (1:ℝ) ≤ (diffCard k y : ℝ) := by
          have h1 := Nat.one_le_iff_ne_zero.mpr (diffCard_ne_zero hky)
          exact_mod_cast h1
        trans (∑ i : ι, if k i = y i then (0:ℝ)
            else (diffCard k y : ℝ)⁻¹ * (diffCard k y : ℝ)⁻¹)
        · refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
          by_cases hi : k i = y i <;> simp [hi, hgk]
        · rw [sum_ite_diff_const, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]
          exact inv_le_one_of_one_le₀ hN1
    calc (∑ k : ι → Bool, ∑ i : ι,
          (if g k = g y then (0:ℝ) else if k i = y i then 0
            else (diffCard k y : ℝ)⁻¹) *
          (if g k = g y then (0:ℝ) else if k i = y i then 0
            else (diffCard k y : ℝ)⁻¹))
        ≤ ∑ _k : ι → Bool, (1:ℝ) := Finset.sum_le_sum fun k _ => hbound k
      _ = (Fintype.card (ι → Bool) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      _ ≤ (Fintype.card ι : ℝ) + (Fintype.card (ι → Bool) : ℝ) := by
          have := Nat.cast_nonneg (α := ℝ) (Fintype.card ι)
          linarith

/-! ## The dual value -/

/-- The set of achievable dual costs (with dimensions normalised to `Fin n`). -/
def dualCosts (g : (ι → Bool) → Bool) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ ∃ (n : ℕ) (P : DualPair (Fin n) g), P.IsCostLe c}

/-- The value of the dual program. -/
noncomputable def advDual (g : (ι → Bool) → Bool) : ℝ := sInf (dualCosts g)

omit [DecidableEq ι] in
lemma dualCosts_nonempty (g : (ι → Bool) → Bool) : (dualCosts g).Nonempty := by
  classical
  refine ⟨(Fintype.card ι : ℝ) + (Fintype.card (ι → Bool) : ℝ), ?_, ?_⟩
  · positivity
  · exact ⟨Fintype.card (ι → Bool),
      (trivialDual g).reindex (Fintype.equivFin _),
      DualPair.reindex_isCostLe (trivialDual_isCostLe g) _⟩

omit [DecidableEq ι] in
lemma bddBelow_dualCosts (g : (ι → Bool) → Bool) : BddBelow (dualCosts g) :=
  ⟨0, fun _c hc => hc.1⟩

omit [DecidableEq ι] in
theorem advDual_nonneg (g : (ι → Bool) → Bool) : 0 ≤ advDual g := by
  classical
  exact le_csInf (dualCosts_nonempty g) fun c hc => hc.1

omit [DecidableEq ι] in
/-- Any feasible dual solution bounds the dual value. -/
theorem advDual_le_of_dualPair {K : Type*} [Fintype K]
    {g : (ι → Bool) → Bool} (P : DualPair K g) {c : ℝ} (hc : 0 ≤ c)
    (hP : P.IsCostLe c) : advDual g ≤ c := by
  classical
  refine csInf_le (bddBelow_dualCosts g) ⟨hc, Fintype.card K,
    P.reindex (Fintype.equivFin _), DualPair.reindex_isCostLe hP _⟩

/-- **Weak duality.** -/
theorem advPM_le_advDual (g : (ι → Bool) → Bool) : advPM g ≤ advDual g := by
  refine le_csInf (dualCosts_nonempty g) ?_
  rintro c ⟨hc, n, P, hP⟩
  exact advPM_le_of_dualPair P hc hP

omit [DecidableEq ι] in
/-- Any value above the dual optimum is achieved by some feasible dual
solution. -/
theorem exists_dualPair_of_lt {g : (ι → Bool) → Bool} {c : ℝ}
    (h : advDual g < c) :
    ∃ (n : ℕ) (P : DualPair (Fin n) g), P.IsCostLe c := by
  classical
  obtain ⟨a, ha, hac⟩ := exists_lt_of_csInf_lt (dualCosts_nonempty g) h
  obtain ⟨-, n, P, hP⟩ := ha
  exact ⟨n, P, hP.mono hac.le⟩

end QuantumQueryComplexity

end SourceDual

section SourceCompositionCompose

/-!
# The b-sum form of the composed matrix

The first rewriting lemma (`composeE_apply_sum`): the entry
`composeE e g Γf M x y` can be written as a sum over all outer inputs
`b : α → Bool`, with guards `if g i (sliceE e y i) = b i` making the
`b = tildeE e g y` fiber automatic.  This eliminates the non-factoring
occurrence `Γf x_tilde y_tilde` before any sum/product interchange.

As in `SourceCompositionHat` the block decomposition is abstract; the cube statement is the
instance at `cubeBlocks`.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

section General

variable {α Y Z : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

omit [DecidableEq Z] [Fintype Z] in
lemma composeE_apply_sum (e : Z ≃ (α → Y)) (g : α → Y → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ) (M : α → Matrix Y Y ℝ) (x y : Z) :
    composeE e g Γf M x y
      = ∑ b : α → Bool, Γf (tildeE e g x) b *
          ∏ i, (if g i (sliceE e y i) = b i
            then hat (M i) (sliceE e x i) (sliceE e y i) else 0) := by
  classical
  symm
  calc ∑ b : α → Bool, Γf (tildeE e g x) b *
        ∏ i, (if g i (sliceE e y i) = b i
          then hat (M i) (sliceE e x i) (sliceE e y i) else 0)
      = Γf (tildeE e g x) (tildeE e g y) *
        ∏ i, (if g i (sliceE e y i) = tildeE e g y i
          then hat (M i) (sliceE e x i) (sliceE e y i) else 0) := by
        refine Finset.sum_eq_single (tildeE e g y) ?_ ?_
        · intro b _ hb
          obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
          have hzero : (if g i (sliceE e y i) = b i
              then hat (M i) (sliceE e x i) (sliceE e y i) else 0) = 0 :=
            ite_eq_right fun h => hi (h.symm.trans (tildeE_apply e g y i).symm)
          rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
    _ = composeE e g Γf M x y := by
        rw [composeE_apply]
        congr 1
        exact Finset.prod_congr rfl fun i _ => ite_eq_left rfl

end General

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma compose_apply_sum (g : α → (β → Bool) → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    (M : α → Matrix (β → Bool) (β → Bool) ℝ) (x y : (α × β) → Bool) :
    compose g Γf M x y
      = ∑ b : α → Bool, Γf (tilde g x) b *
          ∏ i, (if g i (slice y i) = b i
            then hat (M i) (slice x i) (slice y i) else 0) :=
  composeE_apply_sum (cubeBlocks α β) g Γf M x y

end QuantumQueryComplexity

end SourceCompositionCompose

section SourceCompositionSchurPSD

/-!
# The outer auxiliary matrices `Γf ⊙ Emat` and their PSD structure

For an assignment of eigenvalues `lamv i` (with `|lamv i| ≤ R i`), the matrix

  `Emat R lamv a b = ∏ i, if a i = b i then R i else lamv i`

is positive semidefinite: it is the entrywise product over `i : α` of lifts of
the `2×2` seeds `[[R i, lamv i], [lamv i, R i]]` along the coordinate maps
`a ↦ a i` (mathlib's `Matrix.PosSemidef.submatrix` — BL Fact 2 — plus the
Schur product theorem `Matrix.PosSemidef.hadamard`).  Its diagonal is
`∏ i, R i`, so the Schur-multiplier bound gives
`‖Γf ⊙ Emat R lamv‖ ≤ (∏ i, R i) * ‖Γf‖` — replacing the sign-flipping
analysis of HLŠ Lemma 16.

At a "vertex" (`lamv i = ε i * R i` with `ε i = ±1`), `Γf ⊙ Emat` becomes a
`±1`-diagonal conjugate of `(∏ R) • Γf` (`hadamard_Emat_vertex`), which is the
witness used in the `≥` direction.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Entrywise products of PSD matrices lifted along arbitrary maps are PSD
(`Finset` induction from the Schur product theorem; BL Facts 2 and 3). -/
lemma posSemidef_prod_lift {ι E κ : Type*}
    {F : ι → Matrix κ κ ℝ} (hF : ∀ i, (F i).PosSemidef) (e : ι → E → κ)
    (s : Finset ι) [Finite E] :
    Matrix.PosSemidef (Matrix.of fun a b : E => ∏ i ∈ s, F i (e i a) (e i b)) := by
  classical
  let := Fintype.ofFinite E
  induction s using Finset.induction_on with
  | empty => simpa using posSemidef_allOnes (n := E)
  | @insert j s hj ih =>
      have heq : (Matrix.of fun a b : E => ∏ i ∈ insert j s, F i (e i a) (e i b))
          = ((F j).submatrix (e j) (e j)) ⊙
            (Matrix.of fun a b : E => ∏ i ∈ s, F i (e i a) (e i b)) := by
        ext a b
        simp [Finset.prod_insert hj, Matrix.hadamard_apply,
          Matrix.submatrix_apply]
      rw [heq]
      exact ((hF j).submatrix _).hadamard ih

omit [DecidableEq α] [Fintype α] in
/-- Entrywise products of PSD matrices lifted along coordinate evaluations
are PSD. -/
lemma posSemidef_prod_eval {F : α → Matrix Bool Bool ℝ}
    (hF : ∀ i, (F i).PosSemidef) (s : Finset α) [Finite α] :
    Matrix.PosSemidef
      (Matrix.of fun a b : α → Bool => ∏ i ∈ s, F i (a i) (b i)) := by
  classical
  let := Fintype.ofFinite α
  exact posSemidef_prod_lift hF (fun i (a : α → Bool) => a i) s

/-- The outer auxiliary matrix of HLŠ Lemma 16 (denoted `A_c` there, with
`lamv i` the eigenvalue selected in slot `i`). -/
@[expose]
noncomputable def Emat (R lamv : α → ℝ) : Matrix (α → Bool) (α → Bool) ℝ :=
  Matrix.of fun a b => ∏ i, if a i = b i then R i else lamv i

omit [DecidableEq α] in
@[simp] lemma Emat_apply (R lamv : α → ℝ) (a b : α → Bool) :
    Emat R lamv a b = ∏ i, if a i = b i then R i else lamv i := rfl

omit [DecidableEq α] in
lemma Emat_isHermitian (R lamv : α → ℝ) : (Emat R lamv).IsHermitian := by
  change (Emat R lamv)ᴴ = Emat R lamv
  ext a b
  simp only [Matrix.conjTranspose_apply, Emat_apply, star_trivial]
  exact Finset.prod_congr rfl fun i _ => if_congr eq_comm rfl rfl

omit [DecidableEq α] in
lemma Emat_posSemidef {R lamv : α → ℝ} (h : ∀ i, |lamv i| ≤ R i) :
    (Emat R lamv).PosSemidef := by
  classical
  exact posSemidef_prod_eval
      (F := fun i => Matrix.of fun s t : Bool => if s = t then R i else lamv i)
      (fun i => posSemidef_boolPair (h i)) Finset.univ

omit [DecidableEq α] in
lemma Emat_diag (R lamv : α → ℝ) (a : α → Bool) :
    Emat R lamv a a = ∏ i, R i :=
  Finset.prod_congr rfl fun _i _ => ite_eq_left rfl

/-- The Schur-multiplier estimate for the outer auxiliary matrix. -/
lemma norm_hadamard_Emat_le (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    {R lamv : α → ℝ} (hR : ∀ i, 0 ≤ R i) (h : ∀ i, |lamv i| ≤ R i) :
    ‖Γf ⊙ Emat R lamv‖ ≤ (∏ i, R i) * ‖Γf‖ :=
  norm_hadamard_posSemidef_le Γf (Emat_posSemidef h)
    (Finset.prod_nonneg fun i _ => hR i) fun a => (Emat_diag R lamv a).le

/-- The `±1` character vector attached to a sign assignment. -/
def chiSign (ε : α → ℝ) : (α → Bool) → ℝ := fun a => ∏ i, if a i then ε i else 1

omit [DecidableEq α] in
lemma chiSign_mul_self {ε : α → ℝ} (hε : ∀ i, ε i * ε i = 1) (a : α → Bool) :
    chiSign ε a * chiSign ε a = 1 := by
  rw [chiSign, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases h : a i <;> simp [h, hε i]

omit [DecidableEq α] in
lemma Emat_vertex {R ε : α → ℝ} (hε : ∀ i, ε i * ε i = 1) (a b : α → Bool) :
    Emat R (fun i => ε i * R i) a b
      = (∏ i, R i) * (chiSign ε a * chiSign ε b) := by
  simp only [Emat_apply, chiSign]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hab : a i = b i
  · rw [ite_eq_left hab, hab]
    by_cases hb : b i <;> simp [hb, hε i]
  · rw [ite_eq_right hab]
    cases ha : a i <;> cases hb : b i <;> simp_all <;> ring

lemma diagonal_chiSign_mul_self {ε : α → ℝ} (hε : ∀ i, ε i * ε i = 1) :
    Matrix.diagonal (chiSign ε) * Matrix.diagonal (chiSign ε) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun a => chiSign ε a * chiSign ε a) = fun _ => (1 : ℝ) from
    funext fun a => chiSign_mul_self hε a]
  exact Matrix.diagonal_one

lemma chiSign_diagonal_mulVec_ne_zero {ε : α → ℝ} (hε : ∀ i, ε i * ε i = 1)
    {w : (α → Bool) → ℝ} (hw0 : w ≠ 0) :
    Matrix.diagonal (chiSign ε) *ᵥ w ≠ 0 := by
  intro h0
  apply hw0
  calc w = (1 : Matrix (α → Bool) (α → Bool) ℝ) *ᵥ w :=
      (Matrix.one_mulVec w).symm
    _ = (Matrix.diagonal (chiSign ε) * Matrix.diagonal (chiSign ε)) *ᵥ w := by
        rw [diagonal_chiSign_mul_self hε]
    _ = Matrix.diagonal (chiSign ε) *ᵥ (Matrix.diagonal (chiSign ε) *ᵥ w) :=
        (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [h0, Matrix.mulVec_zero]

/-- At a sign vertex, `Γf ⊙ Emat` is a `±1`-diagonal conjugate of
`(∏ R) • Γf`. -/
lemma hadamard_Emat_vertex (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    {R ε : α → ℝ} (hε : ∀ i, ε i * ε i = 1) :
    Γf ⊙ Emat R (fun i => ε i * R i)
      = (∏ i, R i) •
        (Matrix.diagonal (chiSign ε) * Γf * Matrix.diagonal (chiSign ε)) := by
  ext a b
  rw [Matrix.hadamard_apply, Emat_vertex hε, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

end QuantumQueryComplexity

end SourceCompositionSchurPSD

section SourcePromiseDefs

/-!
# The adversary bound on a promise domain

`advPM f` is a single worst-case number attached to a *total* function on the
cube `ι → σ`.  Some bounds are genuinely instance-sensitive: the semilattice
product costs `O(√(n log|L_x|))` where `L_x` is generated by the letters of the
input `x` at hand, and that cannot be said with a free `x` on only one side of
an inequality about a total function.

The fix is to let the inputs be an arbitrary finite type `X` together with an
**observation map**

  `read : X → ι → σ`,

so that a query at `i` returns `read x i`.  Every occurrence of `x i = y i` in
the definitions becomes `read x i = read y i`, and nothing else changes:
`advPMOn`, `DualPairOn` and weak duality are the same statements with the cube
replaced by `X`.  The total case is `X = (ι → σ)` with `read x = x`.

The point of the definitions is `DualPair.restrictTo`: a dual solution for a
total function restricts to the promise **at no cost**, and the restricted cost
is the maximum of the *pointwise* masses over the promise only.  So a bound whose
per-input analysis needs a hypothesis about that input — a critical budget, say —
gives a promise bound as soon as the promise guarantees the hypothesis.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {O : Type*}

/-! ## The primal bound -/

/-- The difference matrix of a promise domain: `1` exactly when a query at `i`
distinguishes the two promise inputs. -/
@[expose]
def advDOn (read : X → ι → σ) (i : ι) : Matrix X X ℝ :=
  Matrix.of fun x y => if read x i = read y i then 0 else 1

omit [DecidableEq X] [DecidableEq ι] [Fintype X] [Fintype ι] in
@[simp] lemma advDOn_apply (read : X → ι → σ) (i : ι) (x y : X) :
    advDOn read i x y = if read x i = read y i then 0 else 1 := rfl

omit [DecidableEq X] [DecidableEq ι] [Fintype X] [Fintype ι] in
lemma advDOn_isHermitian (read : X → ι → σ) (i : ι) :
    (advDOn read i).IsHermitian := by
  change (advDOn read i)ᴴ = advDOn read i
  ext x y
  simp [Matrix.conjTranspose_apply, advDOn, eq_comm]

omit [DecidableEq X] [DecidableEq ι] [Fintype X] [Fintype ι] in
lemma hadamard_advDOn_apply (read : X → ι → σ) (Γ : Matrix X X ℝ) (i : ι)
    (x y : X) :
    (Γ ⊙ advDOn read i) x y = if read x i = read y i then 0 else Γ x y := by
  classical
  rw [Matrix.hadamard_apply, advDOn_apply]
  by_cases h : read x i = read y i <;> simp [h]

/-- An adversary matrix on a promise domain. -/
@[expose]
def IsAdvMatrixOn (f : X → O) (Γ : Matrix X X ℝ) : Prop :=
  Γ.IsHermitian ∧ ∀ x y, f x = f y → Γ x y = 0

omit [DecidableEq X] [Fintype X] in
lemma isAdvMatrixOn_zero (f : X → O) : IsAdvMatrixOn f (0 : Matrix X X ℝ) :=
  ⟨Matrix.isHermitian_zero, fun _ _ _ => rfl⟩

/-- **The adversary bound of a function on a promise domain.** -/
@[expose]
noncomputable def advPMOn (read : X → ι → σ) (f : X → O) : ℝ :=
  sSup {r : ℝ | ∃ Γ, IsAdvMatrixOn f Γ ∧ (∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) ∧ r = ‖Γ‖}

omit [DecidableEq ι] [Fintype ι] in
lemma advPMOn_set_nonempty (read : X → ι → σ) (f : X → O) :
    {r : ℝ | ∃ Γ, IsAdvMatrixOn f Γ ∧ (∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1)
      ∧ r = ‖Γ‖}.Nonempty := by
  refine ⟨0, 0, isAdvMatrixOn_zero f, fun i => ?_, ?_⟩
  · rw [Matrix.zero_hadamard]
    simp
  · simp

omit [DecidableEq ι] [Fintype ι] in
theorem advPMOn_le {read : X → ι → σ} {f : X → O} {c : ℝ}
    (hc : ∀ Γ, IsAdvMatrixOn f Γ → (∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) → ‖Γ‖ ≤ c) :
    advPMOn read f ≤ c := by
  classical
  refine csSup_le (advPMOn_set_nonempty read f) ?_
  rintro r ⟨Γ, h1, h2, rfl⟩
  exact hc Γ h1 h2

/-! ## The dual -/

variable [DecidableEq O]

/-- A feasible dual solution on a promise domain. -/
structure DualPairOn {ι : Type*} [Fintype ι] {σ : Type*} [DecidableEq σ]
    {X : Type*} [Fintype X] {O : Type*} [DecidableEq O]
    (read : X → ι → σ) (K : Type*) [Fintype K] (f : X → O) where
  /-- The first vector family. -/
  u : X → ι → K → ℝ
  /-- The second vector family. -/
  v : X → ι → K → ℝ
  /-- Feasibility, with the mask read through `read`. -/
  constraint : ∀ x y : X,
    (∑ i, if read x i = read y i then 0 else ∑ k, u x i k * v y i k)
      = if f x = f y then 0 else 1

namespace DualPairOn

variable {K : Type*} [Fintype K] {read : X → ι → σ} {f : X → O}

/-- The cost of a dual solution on a promise domain. -/
@[expose]
def IsCostLe (P : DualPairOn read K f) (c : ℝ) : Prop :=
  (∀ x, ∑ i, ∑ k, P.u x i k * P.u x i k ≤ c) ∧
  (∀ x, ∑ i, ∑ k, P.v x i k * P.v x i k ≤ c)

omit [DecidableEq X] [DecidableEq ι] in
lemma IsCostLe.mono {P : DualPairOn read K f} {c d : ℝ} (h : P.IsCostLe c)
    (hcd : c ≤ d) : P.IsCostLe d :=
  ⟨fun x => (h.1 x).trans hcd, fun x => (h.2 x).trans hcd⟩

end DualPairOn

omit [DecidableEq ι] in
/-- **Weak duality on a promise domain.**  The same Gram-plus-Cauchy–Schwarz
argument as `advPM_le_of_dualPair`; only the mask is read through `read`. -/
theorem advPMOn_le_of_dualPairOn {K : Type*} [Fintype K] {read : X → ι → σ}
    {f : X → O} (P : DualPairOn read K f) {c : ℝ} (hc : 0 ≤ c)
    (hP : P.IsCostLe c) : advPMOn read f ≤ c := by
  classical
  refine advPMOn_le fun Γ hΓ hΓD => ?_
  refine l2_opNorm_le_of_forall_dotProduct Γ hc fun a b => ?_
  have hsplit : ∀ x y, a x * Γ x y * b y
      = ∑ p : ι × K, (a x * P.u x p.1 p.2) * (Γ ⊙ advDOn read p.1) x y *
          (b y * P.v y p.1 p.2) := by
    intro x y
    rw [Fintype.sum_prod_type]
    change a x * Γ x y * b y
      = ∑ i, ∑ k, (a x * P.u x i k) * (Γ ⊙ advDOn read i) x y * (b y * P.v y i k)
    have hstep : ∀ i : ι,
        (∑ k, (a x * P.u x i k) * (Γ ⊙ advDOn read i) x y * (b y * P.v y i k))
        = (a x * b y * Γ x y) *
            (if read x i = read y i then 0 else ∑ k, P.u x i k * P.v y i k) := by
      intro i
      by_cases hi : read x i = read y i
      · rw [ite_eq_left hi, mul_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hadamard_advDOn_apply, ite_eq_left hi]
        ring
      · rw [ite_eq_right hi, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hadamard_advDOn_apply, ite_eq_right hi]
        ring
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
      ← Finset.mul_sum, P.constraint x y]
    by_cases hg : f x = f y
    · rw [ite_eq_left hg, hΓ.2 x y hg]
      ring
    · rw [ite_eq_right hg]
      ring
  have hexpand : a ⬝ᵥ Γ *ᵥ b
      = ∑ p : ι × K, (fun x => a x * P.u x p.1 p.2) ⬝ᵥ
          (fun i => Γ ⊙ advDOn read i) p.1 *ᵥ (fun y => b y * P.v y p.1 p.2) := by
    rw [dotProduct_mulVec_eq_sum]
    have hrhs : (∑ p : ι × K, (fun x => a x * P.u x p.1 p.2) ⬝ᵥ
        (fun i => Γ ⊙ advDOn read i) p.1 *ᵥ (fun y => b y * P.v y p.1 p.2))
        = ∑ p : ι × K, ∑ x, ∑ y, (a x * P.u x p.1 p.2) *
            (Γ ⊙ advDOn read p.1) x y * (b y * P.v y p.1 p.2) :=
      Finset.sum_congr rfl fun p _ => dotProduct_mulVec_eq_sum _ _ _
    rw [hrhs]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => hsplit x y
  rw [hexpand]
  exact key_bound (fun i => Γ ⊙ advDOn read i) hΓD a b P.u P.v hc hP.1 hP.2

/-! ## Restricting a total dual solution to a promise -/

namespace DualPair

variable {K : Type*} [Fintype K] [Fintype σ] {g : (ι → σ) → O}

/-- **A total dual solution restricted to a promise domain.**  The vectors are
unchanged: the promise constraint at `(x, y)` is the total constraint at
`(read x, read y)`. -/
def restrictTo (P : DualPair K g) (read : X → ι → σ) :
    DualPairOn read K (fun x => g (read x)) where
  u x := P.u (read x)
  v y := P.v (read y)
  constraint x y := P.constraint (read x) (read y)

omit [DecidableEq X] [DecidableEq ι] [Fintype σ] in
/-- The restricted cost is the maximum of the *pointwise* masses **over the
promise only** — which is the entire point of the construction. -/
theorem restrictTo_isCostLe {P : DualPair K g} {read : X → ι → σ} {c : ℝ}
    (hu : ∀ x : X, (∑ i, ∑ k, P.u (read x) i k * P.u (read x) i k) ≤ c)
    (hv : ∀ x : X, (∑ i, ∑ k, P.v (read x) i k * P.v (read x) i k) ≤ c) :
    (P.restrictTo read).IsCostLe c := ⟨hu, hv⟩

end DualPair

end QuantumQueryComplexity

end SourcePromiseDefs

section SourceDualityGramOn

/-!
# Gram encoding of the dual program, on a promise domain

The promise-domain mirror of `SourceDualityGram`: the input space is an
abstract finite `X` read through `read : X → ι → σ`, the constraint mask is
`read x i = read y i`, and the target is `[f x ≠ f y]`.  Everything else —
the convexification by passing to Gram matrices, the rank-one decomposition
back to a `DualPairOn` — is the same change of variables.

The total case is the instance `X = ι → σ`, `read = id`; it is kept as the
separate `SourceDualityGram` because its statements (`DualPair`, `advPM`) are
pinned by downstream consumers.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {O : Type*} [DecidableEq O]

/-- Index type for the Gram matrix of a promise dual solution: `(x, i, false)`
indexes the vector `u x i` and `(x, i, true)` indexes `v x i`. -/
abbrev GramIdxOn (X ι : Type*) : Type _ := X × ι × Bool

/-! ## The affine data of the promise dual program -/

/-- The right-hand side of the dual feasibility constraint on the promise
domain: `1` on pairs with distinct values, `0` otherwise. -/
@[expose]
def dualTargetOn (f : X → O) : Matrix X X ℝ :=
  Matrix.of fun x y => if f x = f y then 0 else 1

omit [DecidableEq X] [Fintype X] in
@[simp] lemma dualTargetOn_apply (f : X → O) (x y : X) :
    dualTargetOn f x y = if f x = f y then 0 else 1 := rfl

omit [DecidableEq X] [Fintype X] in
lemma dualTargetOn_comm (f : X → O) (x y : X) :
    dualTargetOn f y x = dualTargetOn f x y := by
  simp [eq_comm]

/-- The left-hand side of the dual feasibility constraint, as a function of
the Gram matrix, with the mask read through `read`. -/
@[expose]
def gramROn (read : X → ι → σ) (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) :
    Matrix X X ℝ :=
  Matrix.of fun x y =>
    ∑ i, if read x i = read y i then 0 else G (x, i, false) (y, i, true)

omit [DecidableEq X] [DecidableEq ι] [Fintype X] [Fintype σ] in
@[simp] lemma gramROn_apply (read : X → ι → σ)
    (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) (x y : X) :
    gramROn read G x y
      = ∑ i, if read x i = read y i then 0 else G (x, i, false) (y, i, true) :=
  rfl

/-- The dual objective, as a function of the Gram matrix. -/
def gramCostOn (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) (b : Bool)
    (x : X) : ℝ :=
  ∑ i, G (x, i, b) (x, i, b)

/-! ### Linearity -/

omit [DecidableEq X] [DecidableEq ι] [Fintype X] [Fintype σ] in
lemma gramROn_add (read : X → ι → σ)
    (G H : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) :
    gramROn read (G + H) = gramROn read G + gramROn read H := by
  ext x y
  simp only [gramROn_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    by_cases h : read x i = read y i <;> simp [h]

omit [DecidableEq X] [DecidableEq ι] [Fintype X] [Fintype σ] in
lemma gramROn_smul (read : X → ι → σ) (c : ℝ)
    (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) :
    gramROn read (c • G) = c • gramROn read G := by
  ext x y
  simp only [gramROn_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    by_cases h : read x i = read y i <;> simp [h]

omit [DecidableEq X] [DecidableEq ι] [Fintype X] in
lemma gramCostOn_add (G H : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ)
    (b : Bool) (x : X) :
    gramCostOn (G + H) b x = gramCostOn G b x + gramCostOn H b x := by
  simp [gramCostOn, Finset.sum_add_distrib]

omit [DecidableEq X] [DecidableEq ι] [Fintype X] in
lemma gramCostOn_smul (c : ℝ) (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ)
    (b : Bool) (x : X) : gramCostOn (c • G) b x = c * gramCostOn G b x := by
  simp [gramCostOn, Finset.mul_sum]

omit [DecidableEq X] [DecidableEq ι] [Fintype X] in
/-- A positive semidefinite Gram matrix has nonnegative costs. -/
lemma gramCostOn_nonneg {G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ}
    (hG : G.PosSemidef) (b : Bool) (x : X) : 0 ≤ gramCostOn G b x :=
  Finset.sum_nonneg fun _ _ => hG.diag_nonneg

/-! ## Rank-one Gram matrices -/

omit [DecidableEq X] [DecidableEq ι] [Fintype X] [Fintype σ] in
lemma gramROn_vecMulVec (read : X → ι → σ) (w : GramIdxOn X ι → ℝ)
    (x y : X) :
    gramROn read (vecMulVec w w) x y
      = ∑ i, if read x i = read y i then 0
          else w (x, i, false) * w (y, i, true) := by
  simp [gramROn, vecMulVec_apply]

omit [DecidableEq X] [DecidableEq ι] [Fintype X] in
@[simp] lemma gramCostOn_vecMulVec (w : GramIdxOn X ι → ℝ) (b : Bool)
    (x : X) :
    gramCostOn (vecMulVec w w) b x = ∑ i, w (x, i, b) * w (x, i, b) := by
  simp [gramCostOn, vecMulVec_apply]

omit [DecidableEq X] [DecidableEq ι] in
lemma trace_vecMulVec_on (w : GramIdxOn X ι → ℝ) :
    (vecMulVec w w).trace = ∑ z, w z * w z := by
  simp [Matrix.trace, vecMulVec_apply]

omit [DecidableEq X] [DecidableEq ι] [Fintype X] [Fintype ι] in
lemma posSemidef_vecMulVec_self_on (w : GramIdxOn X ι → ℝ) [Finite X] [Finite ι] :
    (vecMulVec w w).PosSemidef := by
  classical
  let := Fintype.ofFinite X
  let := Fintype.ofFinite ι
  have h : vecMulVec w w
      = (Matrix.of fun (z : GramIdxOn X ι) (_ : Unit) => w z) *
        (Matrix.of fun (z : GramIdxOn X ι) (_ : Unit) => w z)ᴴ := by
    ext z z'
    simp [Matrix.mul_apply, vecMulVec_apply]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-! ## From a Gram matrix to a dual solution -/

variable {read : X → ι → σ} {f : X → O}

omit [DecidableEq X] [DecidableEq ι] [Fintype σ] in
/-- Every positive semidefinite matrix satisfying the promise dual constraints
is the Gram matrix of a feasible `DualPairOn` of the same cost. -/
theorem exists_dualPairOn_of_gram
    {G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ}
    (hG : G.PosSemidef) (hR : gramROn read G = dualTargetOn f) {c : ℝ}
    (hc : ∀ b x, gramCostOn G b x ≤ c) :
    ∃ (m : ℕ) (P : DualPairOn read (Fin m) f), P.IsCostLe c := by
  obtain ⟨m, w, hw⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hG
  have hentry : ∀ z z' : GramIdxOn X ι, G z z' = ∑ k, w k z * w k z' := by
    intro z z'
    rw [hw]
    simp [Matrix.sum_apply, vecMulVec_apply]
  refine ⟨m, { u := fun x i k => w k (x, i, false)
               v := fun x i k => w k (x, i, true)
               constraint := ?_ }, ?_, ?_⟩
  · intro x y
    have := congrArg (fun M => M x y) hR
    simp only [gramROn_apply, dualTargetOn_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by
      by_cases h : read x i = read y i
      · simp [h]
      · simp only [ite_eq_right h]
        exact (hentry (x, i, false) (y, i, true)).symm
  · intro x
    refine le_trans (le_of_eq ?_) (hc false x)
    exact Finset.sum_congr rfl fun i _ =>
      (hentry (x, i, false) (x, i, false)).symm
  · intro x
    refine le_trans (le_of_eq ?_) (hc true x)
    exact Finset.sum_congr rfl fun i _ =>
      (hentry (x, i, true) (x, i, true)).symm

end QuantumQueryComplexity

end SourceDualityGramOn

section TotalDualCertificateConversion
namespace QuantumQueryComplexity
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-- A promise certificate for the identity read is a total-input certificate. -/
def DualPairOn.toTotal {O K : Type*} [DecidableEq O] [Fintype K]
    {g : (ι → σ) → O} (P : DualPairOn (fun x : ι → σ => x) K g) : DualPair K g where
  u := P.u
  v := P.v
  constraint := P.constraint

/-- The conversion preserves both vector families and hence the cost bound. -/
lemma DualPairOn.toTotal_isCostLe {O K : Type*} [DecidableEq O] [Fintype K]
    {g : (ι → σ) → O} {c : ℝ} {P : DualPairOn (fun x : ι → σ => x) K g}
    (h : P.IsCostLe c) : P.toTotal.IsCostLe c := h

end QuantumQueryComplexity
end TotalDualCertificateConversion

section SourceDualityGram

/-!
# Gram encoding of the dual program

A feasible dual solution (`DualPair`) is a pair of vector families `u x i`,
`v y i`; the dual constraints and the dual cost depend on those families only
through their inner products, i.e. only through the Gram matrix of the whole
family.  This section makes that change of variables explicit, which is what
convexifies the dual program: the set of feasible *Gram matrices* is the
intersection of the (convex) positive semidefinite cone with affine
constraints, whereas the set of feasible vector families is not convex.

Indexing the combined family by `GramIdx ι σ = (ι → σ) × ι × Bool` — `false`
tagging a `u`-vector and `true` a `v`-vector — the dictionary is

* `gramR G = dualTarget g` ↔ the `DualPair.constraint` equations,
* `gramCost G b x ≤ c` for all `b`, `x` ↔ `DualPair.IsCostLe c`.

Both directions of the translation are proved: `gramOfDual` builds the Gram
matrix of a dual solution, and `exists_dualPair_of_gram` extracts a dual
solution of dimension `Fin m` from any positive semidefinite `G` satisfying the
constraints, via the rank-one decomposition
`Matrix.posSemidef_iff_eq_sum_vecMulVec`.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} [DecidableEq O]

/-- Index type for the Gram matrix of a dual solution: `(x, i, false)` indexes
the vector `u x i` and `(x, i, true)` indexes `v x i`. -/
abbrev GramIdx (ι σ : Type*) : Type _ := GramIdxOn (ι → σ) ι

/-! ## The affine data of the dual program -/

/-- The right-hand side of the dual feasibility constraint:
`dualTarget g x y = 1` if `g x ≠ g y` and `0` otherwise. -/
@[expose]
def dualTarget (g : (ι → σ) → O) : Matrix (ι → σ) (ι → σ) ℝ := dualTargetOn g

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
@[simp] lemma dualTarget_apply (g : (ι → σ) → O) (x y : ι → σ) :
    dualTarget g x y = if g x = g y then 0 else 1 := rfl

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma dualTarget_comm (g : (ι → σ) → O) (x y : ι → σ) :
    dualTarget g y x = dualTarget g x y := dualTargetOn_comm g x y

/-- The left-hand side of the dual feasibility constraint, as a function of the
Gram matrix. -/
@[expose]
def gramR (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) :
    Matrix (ι → σ) (ι → σ) ℝ := gramROn id G

omit [DecidableEq ι] [Fintype σ] in
@[simp] lemma gramR_apply (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ)
    (x y : ι → σ) :
    gramR G x y = ∑ i, if x i = y i then 0 else G (x, i, false) (y, i, true) :=
  rfl

/-- The dual objective, as a function of the Gram matrix: `gramCost G false x`
is `∑ i, ‖u x i‖²` and `gramCost G true x` is `∑ i, ‖v x i‖²`. -/
@[expose]
def gramCost (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) (b : Bool)
    (x : ι → σ) : ℝ := gramCostOn G b x

/-! ### Linearity -/

omit [DecidableEq ι] [Fintype σ] in
lemma gramR_add (G H : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) :
    gramR (G + H) = gramR G + gramR H := gramROn_add id G H

omit [DecidableEq ι] [Fintype σ] in
lemma gramR_smul (c : ℝ) (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) :
    gramR (c • G) = c • gramR G := gramROn_smul id c G

omit [DecidableEq ι] [DecidableEq σ] [Fintype σ] in
lemma gramCost_add (G H : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) (b : Bool)
    (x : ι → σ) : gramCost (G + H) b x = gramCost G b x + gramCost H b x := gramCostOn_add G H b x

omit [DecidableEq ι] [DecidableEq σ] [Fintype σ] in
lemma gramCost_smul (c : ℝ) (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ)
    (b : Bool) (x : ι → σ) : gramCost (c • G) b x = c * gramCost G b x := gramCostOn_smul c G b x

omit [DecidableEq σ] in
/-- The trace splits as the total cost of the two sides. -/
lemma trace_eq_sum_gramCost (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) :
    G.trace = (∑ x, gramCost G false x) + ∑ x, gramCost G true x := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, gramCost, gramCost, gramCostOn, gramCostOn,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [add_comm]

omit [DecidableEq ι] [DecidableEq σ] [Fintype σ] in
/-- A positive semidefinite Gram matrix has nonnegative costs. -/
lemma gramCost_nonneg {G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ}
    (hG : G.PosSemidef) (b : Bool) (x : ι → σ) : 0 ≤ gramCost G b x := gramCostOn_nonneg hG b x

/-! ## Rank-one Gram matrices -/

omit [DecidableEq ι] [Fintype σ] in
lemma gramR_vecMulVec (w : GramIdx ι σ → ℝ) (x y : ι → σ) :
    gramR (vecMulVec w w) x y
      = ∑ i, if x i = y i then 0 else w (x, i, false) * w (y, i, true) := gramROn_vecMulVec id w x y

omit [DecidableEq ι] [DecidableEq σ] [Fintype σ] in
@[simp] lemma gramCost_vecMulVec (w : GramIdx ι σ → ℝ) (b : Bool)
    (x : ι → σ) :
    gramCost (vecMulVec w w) b x = ∑ i, w (x, i, b) * w (x, i, b) := gramCostOn_vecMulVec w b x

omit [DecidableEq σ] in
lemma trace_vecMulVec (w : GramIdx ι σ → ℝ) :
    (vecMulVec w w).trace = ∑ z, w z * w z := trace_vecMulVec_on w

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma posSemidef_vecMulVec_self (w : GramIdx ι σ → ℝ) [Finite ι] [Finite σ] :
    (vecMulVec w w).PosSemidef := posSemidef_vecMulVec_self_on w

/-! ## From a dual solution to its Gram matrix -/

variable {K : Type*} [Fintype K] {g : (ι → σ) → O}

/-- The two vector families of a dual solution, packed into a single matrix
whose rows are indexed by `GramIdx ι σ`. -/
@[expose]
def dualVec (P : DualPair K g) : Matrix (GramIdx ι σ) K ℝ :=
  Matrix.of fun z k => if z.2.2 then P.v z.1 z.2.1 k else P.u z.1 z.2.1 k

omit [DecidableEq ι] [Fintype σ] in
@[simp] lemma dualVec_false (P : DualPair K g) (x : ι → σ) (i : ι) (k : K) :
    dualVec P (x, i, false) k = P.u x i k := rfl

omit [DecidableEq ι] [Fintype σ] in
@[simp] lemma dualVec_true (P : DualPair K g) (x : ι → σ) (i : ι) (k : K) :
    dualVec P (x, i, true) k = P.v x i k := rfl

/-- The Gram matrix of a dual solution. -/
def gramOfDual (P : DualPair K g) :
    Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ := dualVec P * (dualVec P)ᴴ

omit [DecidableEq ι] [Fintype σ] in
lemma gramOfDual_apply (P : DualPair K g) (z w : GramIdx ι σ) :
    gramOfDual P z w = ∑ k, dualVec P z k * dualVec P w k := by
  simp [gramOfDual, Matrix.mul_apply]

omit [DecidableEq ι] [Fintype σ] in
lemma gramOfDual_posSemidef (P : DualPair K g) [Finite σ] : (gramOfDual P).PosSemidef := by
  classical
  let := Fintype.ofFinite σ
  exact Matrix.posSemidef_self_mul_conjTranspose _

omit [DecidableEq ι] [Fintype σ] in
lemma gramR_gramOfDual (P : DualPair K g) : gramR (gramOfDual P) = dualTarget g := by
  classical
  ext x y
  rw [gramR_apply, dualTarget_apply, ← P.constraint x y]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : x i = y i
  · simp [h]
  · simp only [ite_eq_right h]
    exact gramOfDual_apply P (x, i, false) (y, i, true)

omit [DecidableEq ι] [Fintype σ] in
lemma gramCost_gramOfDual_false (P : DualPair K g) (x : ι → σ) :
    gramCost (gramOfDual P) false x = ∑ i, ∑ k, P.u x i k * P.u x i k := by
  classical
  exact Finset.sum_congr rfl fun i _ => gramOfDual_apply P (x, i, false) (x, i, false)

omit [DecidableEq ι] [Fintype σ] in
lemma gramCost_gramOfDual_true (P : DualPair K g) (x : ι → σ) :
    gramCost (gramOfDual P) true x = ∑ i, ∑ k, P.v x i k * P.v x i k := by
  classical
  exact Finset.sum_congr rfl fun i _ => gramOfDual_apply P (x, i, true) (x, i, true)

omit [DecidableEq ι] [Fintype σ] in
lemma gramCost_gramOfDual_le {P : DualPair K g} {c : ℝ} (h : P.IsCostLe c)
    (b : Bool) (x : ι → σ) : gramCost (gramOfDual P) b x ≤ c := by
  classical
  cases b with
  | false => rw [gramCost_gramOfDual_false]; exact h.1 x
  | true => rw [gramCost_gramOfDual_true]; exact h.2 x

/-! ## From a Gram matrix back to a dual solution -/

omit [DecidableEq ι] [Fintype σ] in
/-- Every positive semidefinite matrix satisfying the dual constraints is the
Gram matrix of a feasible dual solution of the same cost.  The dimension comes
out as `Fin m`, which is the shape `advDual` normalises to. -/
theorem exists_dualPair_of_gram {G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ}
    (hG : G.PosSemidef) (hR : gramR G = dualTarget g) {c : ℝ}
    (hc : ∀ b x, gramCost G b x ≤ c) [Finite σ] :
    ∃ (m : ℕ) (P : DualPair (Fin m) g), P.IsCostLe c := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨m, P, hP⟩ := exists_dualPairOn_of_gram (read := id) hG hR hc
  exact ⟨m, P.toTotal, hP⟩

end QuantumQueryComplexity

end SourceDualityGram


section SourcePullback

/-!
# Pulling a dual solution back along an embedding of coordinates

A subproblem of a divide-and-conquer algorithm reads only a *block* of the
input.  Formally it is `pullbackFun e f x = f (x ∘ e)` for an injection
`e : κ → ι` of the block into the full coordinate set.

A dual solution for `f` transports to one for `pullbackFun e f` **at the same
cost**: place the `j`-th vector of the original solution at coordinate `e j` and
zero elsewhere.  Injectivity is what makes this work — each coordinate of `ι`
receives at most one vector, so the `ℓ²` masses simply move rather than adding
up, and the masked sum over `ι` restricts to the masked sum over `κ`.

This is how `upstream Max/Staircase.lean`'s bound for `maxFun` on a `κ`-indexed
input becomes a bound for "the maximum over a block" as a function of the whole
array, with cost governed by the block size `|κ|` and not by `|ι|`.
-/


namespace QuantumQueryComplexity

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {σ : Type*} [DecidableEq σ]
variable {O : Type*} [DecidableEq O]

/-- Restricting a function to a block of coordinates. -/
@[expose]
def pullbackFun (e : κ → ι) (f : (κ → σ) → O) : (ι → σ) → O :=
  fun x => f fun j => x (e j)

omit [DecidableEq O] [DecidableEq ι] [DecidableEq κ] [DecidableEq σ] [Fintype ι] [Fintype κ] in
@[simp] lemma pullbackFun_apply (e : κ → ι) (f : (κ → σ) → O) (x : ι → σ) :
    pullbackFun e f x = f (fun j => x (e j)) := rfl

/-! ## Spreading a `κ`-indexed family over `ι` -/

/-- The value placed at coordinate `i` by a `κ`-indexed family. -/
noncomputable def spread (e : κ → ι) (F : κ → ℝ) (i : ι) : ℝ :=
  ∑ j : κ, (if e j = i then (1 : ℝ) else 0) * F j

omit [DecidableEq κ] [Fintype ι] in
lemma spread_eq_of_mem {e : κ → ι} (he : Function.Injective e) {i : ι} {j₀ : κ}
    (hj : e j₀ = i) (F : κ → ℝ) : spread e F i = F j₀ := by
  rw [spread, Finset.sum_eq_single j₀]
  · rw [ite_eq_left hj, one_mul]
  · intro j _ hne
    rw [ite_eq_right fun h => hne (he (h.trans hj.symm)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [DecidableEq κ] [Fintype ι] in
lemma spread_eq_zero {e : κ → ι} {i : ι} (h : ∀ j, e j ≠ i) (F : κ → ℝ) :
    spread e F i = 0 :=
  Finset.sum_eq_zero fun j _ => by rw [ite_eq_right (h j), zero_mul]

omit [DecidableEq κ] [Fintype ι] in
/-- Injectivity makes `spread` multiplicative: at most one `κ`-index lands on
any given coordinate. -/
lemma spread_mul_spread {e : κ → ι} (he : Function.Injective e) (i : ι)
    (F G : κ → ℝ) :
    spread e F i * spread e G i = spread e (fun j => F j * G j) i := by
  classical
  by_cases h : ∃ j, e j = i
  · obtain ⟨j₀, hj⟩ := h
    rw [spread_eq_of_mem he hj, spread_eq_of_mem he hj, spread_eq_of_mem he hj]
  · push Not at h
    simp [spread_eq_zero h]

omit [DecidableEq κ] in
/-- Summing a spread family over `ι` recovers the sum over `κ`. -/
lemma sum_spread {e : κ → ι} (F : κ → ℝ) :
    (∑ i : ι, spread e F i) = ∑ j : κ, F j := by
  simp only [spread]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (e j)]
  · rw [ite_eq_left rfl, one_mul]
  · intro i _ hne
    rw [ite_eq_right fun h => hne h.symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

namespace DualPair

variable {K : Type*} [Fintype K] {e : κ → ι} {f : (κ → σ) → O}

/-- **A dual solution pulled back along an injection of coordinates.** -/
noncomputable def pullback (he : Function.Injective e) (P : DualPair K f) :
    DualPair K (pullbackFun e f) where
  u x i := fun k => spread e (fun j => P.u (fun j => x (e j)) j k) i
  v y i := fun k => spread e (fun j => P.v (fun j => y (e j)) j k) i
  constraint x y := by
    set T : κ → ℝ := fun j =>
      ∑ k : K, P.u (fun j => x (e j)) j k * P.v (fun j => y (e j)) j k with hT
    have hpt : ∀ i : ι,
        (∑ k : K, spread e (fun j => P.u (fun j => x (e j)) j k) i
            * spread e (fun j => P.v (fun j => y (e j)) j k) i)
        = spread e T i := by
      intro i
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        spread_mul_spread he i (fun j => P.u (fun j => x (e j)) j k)
          (fun j => P.v (fun j => y (e j)) j k)]
      simp only [spread, hT]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    simp only [hpt]
    have hmask : ∀ i : ι,
        (if x i = y i then (0 : ℝ) else spread e T i)
        = spread e (fun j => if x (e j) = y (e j) then (0 : ℝ) else T j) i := by
      intro i
      by_cases h : ∃ j, e j = i
      · obtain ⟨j₀, hj⟩ := h
        rw [spread_eq_of_mem he hj, spread_eq_of_mem he hj, hj]
      · push Not at h
        rw [spread_eq_zero h, spread_eq_zero h, ite_self]
    simp only [hmask]
    rw [sum_spread]
    exact P.constraint (fun j => x (e j)) (fun j => y (e j))

omit [DecidableEq κ] in
/-- The pullback costs exactly what the original solution costs — the `ℓ²` mass
moves from `κ` to the image of `e` without accumulating. -/
theorem pullback_isCostLe {c : ℝ} (he : Function.Injective e) (P : DualPair K f)
    (hP : P.IsCostLe c) : (P.pullback he).IsCostLe c := by
  constructor
  · intro x
    have h : ∀ i : ι, (∑ k : K, (P.pullback he).u x i k * (P.pullback he).u x i k)
        = spread e (fun j => ∑ k : K,
            P.u (fun j => x (e j)) j k * P.u (fun j => x (e j)) j k) i := by
      intro i
      change (∑ k : K, spread e (fun j => P.u (fun j => x (e j)) j k) i
          * spread e (fun j => P.u (fun j => x (e j)) j k) i) = _
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        spread_mul_spread he i (fun j => P.u (fun j => x (e j)) j k)
          (fun j => P.u (fun j => x (e j)) j k)]
      simp only [spread]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    simp only [h]
    rw [sum_spread]
    exact hP.1 _
  · intro y
    have h : ∀ i : ι, (∑ k : K, (P.pullback he).v y i k * (P.pullback he).v y i k)
        = spread e (fun j => ∑ k : K,
            P.v (fun j => y (e j)) j k * P.v (fun j => y (e j)) j k) i := by
      intro i
      change (∑ k : K, spread e (fun j => P.v (fun j => y (e j)) j k) i
          * spread e (fun j => P.v (fun j => y (e j)) j k) i) = _
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        spread_mul_spread he i (fun j => P.v (fun j => y (e j)) j k)
          (fun j => P.v (fun j => y (e j)) j k)]
      simp only [spread]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    simp only [h]
    rw [sum_spread]
    exact hP.2 _

end DualPair

/-! ## Freezing the coordinates outside a block

The dual of padding.  A function of `n` variables can be regarded as a function
of `N ≥ n` variables in which the last `N - n` are held at fixed, known values;
that is what "append `N - n` known identity matrices to the input" means, and a
dual solution for the padded problem restricts to one for the original at
unchanged cost.

Two conditions are needed, and between them they say that the adversary mask is
transported exactly.  `hin` says the embedded coordinates are read faithfully —
two inputs agree at `i` precisely when the padded inputs agree at `e i` — and
`hout` says the frozen coordinates never depend on the input, so they contribute
nothing to the mask.  Injectivity of `e` is what stops the `ℓ²` masses from
accumulating, exactly as in `pullback`.

Unlike `alphaMap`, the alphabets on the two sides need not match: padding
typically enlarges `σ` to `Option σ` in order to name the frozen letter. -/

namespace DualPair

variable {K : Type*} [Fintype K] {σ' : Type*} [DecidableEq σ']

section Restrict

variable {e : ι → κ} {Φ : (ι → σ) → κ → σ'} {F : (κ → σ') → O}

/-- **A dual solution restricted along a padding.** -/
noncomputable def restrict (he : Function.Injective e)
    (hin : ∀ (x y : ι → σ) (i : ι), Φ x (e i) = Φ y (e i) ↔ x i = y i)
    (hout : ∀ (x y : ι → σ) (j : κ), (∀ i, e i ≠ j) → Φ x j = Φ y j)
    (P : DualPair K F) : DualPair K (fun x => F (Φ x)) where
  u x i := P.u (Φ x) (e i)
  v y i := P.v (Φ y) (e i)
  constraint x y := by
    classical
    rw [← P.constraint (Φ x) (Φ y)]
    have hzero : ∀ j ∈ (Finset.univ : Finset κ), j ∉ Finset.image e Finset.univ →
        (if Φ x j = Φ y j then (0 : ℝ)
          else ∑ c, P.u (Φ x) j c * P.v (Φ y) j c) = 0 := by
      intro j _ hj
      rw [ite_eq_left (hout x y j fun i hi =>
        hj (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hi⟩))]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.image e Finset.univ)) hzero,
      Finset.sum_image fun i _ i' _ h => he h]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : x i = y i
    · rw [ite_eq_left h, ite_eq_left ((hin x y i).2 h)]
    · rw [ite_eq_right h, ite_eq_right fun hc => h ((hin x y i).1 hc)]

omit [DecidableEq ι] in
/-- The restriction costs no more than the padded solution: the `ℓ²` mass at the
frozen coordinates is simply discarded. -/
theorem restrict_isCostLe {c : ℝ} (he : Function.Injective e)
    (hin : ∀ (x y : ι → σ) (i : ι), Φ x (e i) = Φ y (e i) ↔ x i = y i)
    (hout : ∀ (x y : ι → σ) (j : κ), (∀ i, e i ≠ j) → Φ x j = Φ y j)
    (P : DualPair K F) (hP : P.IsCostLe c) :
    (P.restrict he hin hout).IsCostLe c := by
  classical
  have key : ∀ (U : (κ → σ') → κ → K → ℝ) (z : κ → σ'),
      (∑ i : ι, ∑ k : K, U z (e i) k * U z (e i) k)
        ≤ ∑ j : κ, ∑ k : K, U z j k * U z j k := by
    intro U z
    have himg : (∑ j ∈ Finset.image e Finset.univ, ∑ k : K, U z j k * U z j k)
        = ∑ i : ι, ∑ k : K, U z (e i) k * U z (e i) k :=
      Finset.sum_image fun i _ i' _ h => he h
    rw [← himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun j _ _ => Finset.sum_nonneg fun k _ => mul_self_nonneg _
  exact ⟨fun x => (key P.u (Φ x)).trans (hP.1 (Φ x)),
    fun y => (key P.v (Φ y)).trans (hP.2 (Φ y))⟩

end Restrict

end DualPair

/-! ## Recoding the alphabet -/

variable {σ' : Type*} [DecidableEq σ']

/-- Recoding the input alphabet along a map `m`. -/
@[expose]
def alphaFun (m : σ → σ') (f : (ι → σ') → O) : (ι → σ) → O :=
  fun x => f fun i => m (x i)

omit [DecidableEq O] [DecidableEq ι] [DecidableEq σ'] [DecidableEq σ] [Fintype ι] in
@[simp] lemma alphaFun_apply (m : σ → σ') (f : (ι → σ') → O) (x : ι → σ) :
    alphaFun m f x = f (fun i => m (x i)) := rfl

namespace DualPair

variable {K : Type*} [Fintype K] {m : σ → σ'} {f : (ι → σ') → O}

/-- A dual solution transports along an **injective** recoding of the alphabet,
at unchanged cost.

Injectivity is exactly what is needed and no more: it keeps the adversary mask
`x i ≠ y i` in step with `m (x i) ≠ m (y i)`, so the masked sums agree term by
term.  A non-injective recoding would merge inputs and let extra coordinates
into the sum.

The use here is order-reversing: `v ↦ M - 1 - v` is a bijection of `Fin M`, so a
solution for a maximum becomes one for a minimum without any separate
development. -/
noncomputable def alphaMap (hm : Function.Injective m) (P : DualPair K f) :
    DualPair K (alphaFun m f) where
  u x i := P.u (fun i => m (x i)) i
  v y i := P.v (fun i => m (y i)) i
  constraint x y := by
    have key : (∑ i, if x i = y i then (0 : ℝ)
          else ∑ k, P.u (fun i => m (x i)) i k * P.v (fun i => m (y i)) i k)
        = ∑ i, if m (x i) = m (y i) then (0 : ℝ)
          else ∑ k, P.u (fun i => m (x i)) i k * P.v (fun i => m (y i)) i k := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : x i = y i
      · rw [ite_eq_left h, ite_eq_left (by rw [h])]
      · rw [ite_eq_right h, ite_eq_right fun hc => h (hm hc)]
    rw [key]
    exact P.constraint (fun i => m (x i)) (fun i => m (y i))

omit [DecidableEq ι] in
theorem alphaMap_isCostLe {c : ℝ} (hm : Function.Injective m) (P : DualPair K f)
    (hP : P.IsCostLe c) : (P.alphaMap hm).IsCostLe c :=
  ⟨fun _x => hP.1 _, fun _y => hP.2 _⟩

end DualPair

/-! ## Transporting along an equality of functions -/

namespace DualPair

/-- A dual solution for `f` is one for any function equal to `f`.  The vector
families are unchanged, so all costs are too. -/
def ofEq {K : Type*} [Fintype K] {f g : (ι → σ) → O} (h : ∀ x, f x = g x)
    (P : DualPair K f) : DualPair K g where
  u := P.u
  v := P.v
  constraint x y := by
    rw [← h x, ← h y]
    exact P.constraint x y

omit [DecidableEq ι] in
theorem ofEq_isCostLe {K : Type*} [Fintype K] {f g : (ι → σ) → O} {c : ℝ}
    (h : ∀ x, f x = g x) {P : DualPair K f} (hP : P.IsCostLe c) :
    (P.ofEq h).IsCostLe c := hP

end DualPair

/-! ## Enlarging the dimension type -/

namespace DualPair

/-- Padding a dual solution with zero coordinates, along an injection of
dimension types.  Costs are unchanged.

This is what lets solutions built over *different* dimension types be fed to
`composeShared`, which needs a single type for all subproblems. -/
noncomputable def embedDim {K K' : Type*} [Fintype K]
    [Fintype K'] [DecidableEq K'] {m : K → K'} (hm : Function.Injective m)
    {f : (ι → σ) → O} (P : DualPair K f) : DualPair K' f where
  u x i := fun k' => spread m (fun k => P.u x i k) k'
  v y i := fun k' => spread m (fun k => P.v y i k) k'
  constraint x y := by
    have hpt : ∀ i : ι,
        (∑ k' : K', spread m (fun k => P.u x i k) k'
            * spread m (fun k => P.v y i k) k')
          = ∑ k : K, P.u x i k * P.v y i k := by
      intro i
      rw [Finset.sum_congr rfl fun k' (_ : k' ∈ Finset.univ) =>
        spread_mul_spread hm k' (fun k => P.u x i k) (fun k => P.v y i k)]
      exact sum_spread _
    simp only [hpt]
    exact P.constraint x y

omit [DecidableEq ι] in
theorem embedDim_isCostLe {K K' : Type*} [Fintype K]
    [Fintype K'] [DecidableEq K'] {m : K → K'} (hm : Function.Injective m)
    {f : (ι → σ) → O} {c : ℝ} (P : DualPair K f) (hP : P.IsCostLe c) :
    (P.embedDim hm).IsCostLe c := by
  classical
  have key : ∀ (U : (ι → σ) → ι → K → ℝ) (x : ι → σ) (i : ι),
      (∑ k' : K', spread m (fun k => U x i k) k' * spread m (fun k => U x i k) k')
        = ∑ k : K, U x i k * U x i k := by
    intro U x i
    rw [Finset.sum_congr rfl fun k' (_ : k' ∈ Finset.univ) =>
      spread_mul_spread hm k' (fun k => U x i k) (fun k => U x i k)]
    exact sum_spread _
  refine ⟨fun x => ?_, fun y => ?_⟩
  · change (∑ i : ι, ∑ k' : K', spread m (fun k => P.u x i k) k'
      * spread m (fun k => P.u x i k) k') ≤ c
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => key P.u x i]
    exact hP.1 x
  · change (∑ i : ι, ∑ k' : K', spread m (fun k => P.v y i k) k'
      * spread m (fun k => P.v y i k) k') ≤ c
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => key P.v y i]
    exact hP.2 y

end DualPair

end QuantumQueryComplexity

end SourcePullback

section SourceCompositionEigen

/-!
# The eigen-computation for composed matrices (HLŠ Lemma 16, Items 1–2)

The crux of the composition theorem: for eigenvectors `v i` of the inner
matrices `M i` (eigenvalues `lamv i`) and an eigenvector `w` of the outer
auxiliary matrix `Γf ⊙ Emat (‖M ·‖) lamv` (eigenvalue `μ`), the tensor
vector

  `tensorVec g v w x = w (tilde g x) * ∏ i, v i (slice x i)`

is an eigenvector of `compose g Γf M` with eigenvalue `μ`
(`compose_mulVec_tensorVec`).

The two supporting identities:
* `hat_guarded_row_sum` (K1) — the per-block action, replacing HLŠ Eq. (3)
  and all restriction-vector bookkeeping by a scalar computation;
* `sum_prod_slice` (K2) — the sum/product interchange along
  `(α × β) → Bool ≃ α → β → Bool`.

As in `SourceCompositionHat` everything is proved over an **abstract** block decomposition
`e : Z ≃ (α → Y)`; the cube statements are the `cubeBlocks` instance.
This includes promise problems whose inner inputs form a subtype. Nothing in the
spectral argument sees the difference: K1 uses only that the colouring is
`Bool`-valued, and K2 is `Fintype.prod_sum` transported along `e`.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## An adversary matrix for a colouring of an arbitrary type

`IsAdvMatrix` is tied to a cube of inputs.  The inner inputs of a composition
range over an arbitrary finite type, so the same notion is
needed there; at a cube the two are definitionally equal. -/

/-- A symmetric matrix supported on pairs of differently-coloured points. -/
def IsAdvCol {Y : Type*} (g : Y → Bool) (N : Matrix Y Y ℝ) : Prop :=
  N.IsHermitian ∧ ∀ u v, g u = g v → N u v = 0

namespace IsAdvCol
variable {Y : Type*} {g : Y → Bool} {N : Matrix Y Y ℝ}

lemma isHermitian (h : IsAdvCol g N) : N.IsHermitian := h.1

lemma apply_eq_zero (h : IsAdvCol g N) {u v : Y} (huv : g u = g v) : N u v = 0 :=
  h.2 u v huv

end IsAdvCol

/-- The bipartite-support lemma for a colouring of an arbitrary type: an
eigenvector with nonzero eigenvalue of an adversary matrix for `g` has support
in every colour class of `g`.  (`SourceBipartite` proves this over an arbitrary
index type already; only the `IsAdvMatrix` wrapper was cube-tied.) -/
theorem IsAdvCol.exists_eigenvector_support {Y : Type*} [Fintype Y]
    {g : Y → Bool} {N : Matrix Y Y ℝ} (hN : IsAdvCol g N)
    {v : Y → ℝ} {θ : ℝ} (hv : N *ᵥ v = θ • v) (hθ : θ ≠ 0) (hv0 : v ≠ 0)
    (a : Bool) : ∃ u, g u = a ∧ v u ≠ 0 := by
  have h := brestrict_ne_zero (fun u w' huw => hN.2 u w' huw) hv hθ hv0 a
  obtain ⟨u, hu⟩ := Function.ne_iff.mp h
  simp only [brestrict_apply, Pi.zero_apply] at hu
  by_cases hgu : g u = a
  · rw [ite_eq_left hgu] at hu
    exact ⟨u, hgu, hu⟩
  · rw [ite_eq_right hgu] at hu
    exact absurd rfl hu

lemma IsAdvMatrix.isAdvCol {ι σ : Type*}
     {f : (ι → σ) → Bool} {Γ : Matrix (ι → σ) (ι → σ) ℝ}
    (h : IsAdvMatrix f Γ) : IsAdvCol f Γ := h

/-! ## The spectral core over an abstract block decomposition -/

section General

variable {α Y Z : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
variable (e : Z ≃ (α → Y))

/-- **K1**: the guarded row sum of `hat N` against an eigenvector. -/
lemma hat_guarded_row_sumGen {g : (Y) → Bool}
    {N : Matrix (Y) (Y) ℝ} (hN : IsAdvCol g N)
    {v : (Y) → ℝ} {θ : ℝ} (hv : N *ᵥ v = θ • v) (u₀ : Y)
    (b : Bool) :
    ∑ u, (if g u = b then hat N u₀ u * v u else 0)
      = (if g u₀ = b then ‖N‖ else θ) * v u₀ := by
  have hsplit : ∀ u, (if g u = b then hat N u₀ u * v u else 0)
      = (if g u = b then N u₀ u * v u else 0)
      + (if g u = b then ‖N‖ * (if u₀ = u then 1 else 0) * v u else 0) := by
    intro u
    by_cases h : g u = b
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, hat_apply]
      ring
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, add_zero]
  rw [Finset.sum_congr rfl fun u _ => hsplit u, Finset.sum_add_distrib]
  have hid : ∑ u, (if g u = b then ‖N‖ * (if u₀ = u then 1 else 0) * v u else 0)
      = (if g u₀ = b then ‖N‖ else 0) * v u₀ := by
    rw [Finset.sum_eq_single u₀]
    · by_cases h : g u₀ = b <;> simp [h]
    · intro u _ hu
      have hne : u₀ ≠ u := fun hh => hu hh.symm
      by_cases h : g u = b
      · rw [ite_eq_left h, ite_eq_right hne, mul_zero, zero_mul]
      · rw [ite_eq_right h]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hNpart : ∑ u, (if g u = b then N u₀ u * v u else 0)
      = (if g u₀ = b then 0 else θ * v u₀) := by
    by_cases h0 : g u₀ = b
    · rw [ite_eq_left h0]
      refine Finset.sum_eq_zero fun u _ => ?_
      by_cases h : g u = b
      · rw [ite_eq_left h, hN.apply_eq_zero (h0.trans h.symm), zero_mul]
      · rw [ite_eq_right h]
    · rw [ite_eq_right h0]
      have hall : ∀ u, (if g u = b then N u₀ u * v u else 0) = N u₀ u * v u := by
        intro u
        by_cases h : g u = b
        · rw [ite_eq_left h]
        · rw [ite_eq_right h]
          have hgg : g u = g u₀ := by
            cases hgu : g u <;> cases hgu0 : g u₀ <;> cases b <;> simp_all
          rw [hN.apply_eq_zero hgg.symm, zero_mul]
      rw [Finset.sum_congr rfl fun u _ => hall u]
      have hcf := congrFun hv u₀
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hcf
      exact hcf
  rw [hid, hNpart]
  by_cases h : g u₀ = b <;> simp [h]

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq α] in
/-- **K2**: the sum/product interchange along slices. -/
lemma sum_prod_sliceE (F : α → (Y) → ℝ) :
    ∑ y : Z, ∏ i, F i (sliceE e y i)
      = ∏ i, ∑ u : Y, F i u := by
  classical
  rw [Fintype.prod_sum]
  exact Fintype.sum_equiv e
    (fun y => ∏ i, F i (sliceE e y i)) (fun p => ∏ i, F i (p i)) fun y => rfl

/-- The tensor eigenvector of the composed matrix. -/
@[expose]
noncomputable def tensorVecE (g : α → (Y) → Bool)
    (v : α → (Y) → ℝ) (w : (α → Bool) → ℝ) :
    (Z) → ℝ :=
  fun x => w (tildeE e g x) * ∏ i, v i (sliceE e x i)

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq α] [Fintype Y] [Fintype Z] in
@[simp] lemma tensorVecE_apply (g : α → Y → Bool) (v : α → Y → ℝ)
    (w : (α → Bool) → ℝ) (z : Z) :
    tensorVecE e g v w z = w (tildeE e g z) * ∏ i, v i (sliceE e z i) := rfl

omit [DecidableEq Z] in
/-- **K3', the crux in general form**: applying the composed matrix to a
tensor vector amounts to applying the outer auxiliary matrix `Γf ⊙ Emat` to
the outer factor.  (HLŠ Lemma 16, Items 1–2, for an arbitrary outer
vector.) -/
theorem composeE_mulVec_tensorVec' {g : α → (Y) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (Y) (Y) ℝ}
    (hM : ∀ i, IsAdvCol (g i) (M i))
    {v : α → (Y) → ℝ} {lamv : α → ℝ}
    (hv : ∀ i, M i *ᵥ v i = lamv i • v i)
    (w : (α → Bool) → ℝ) :
    composeE e g Γf M *ᵥ tensorVecE e g v w
      = tensorVecE e g v ((Γf ⊙ Emat (fun i => ‖M i‖) lamv) *ᵥ w) := by
  classical
  funext x
  calc (composeE e g Γf M *ᵥ tensorVecE e g v w) x
      = ∑ y, composeE e g Γf M x y * tensorVecE e g v w y := rfl
    _ = ∑ y, (∑ b, Γf (tildeE e g x) b *
          ∏ i, (if g i (sliceE e y i) = b i
            then hat (M i) (sliceE e x i) (sliceE e y i) else 0))
          * tensorVecE e g v w y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [composeE_apply_sum]
    _ = ∑ y, ∑ b, Γf (tildeE e g x) b * w b *
          ∏ i, ((if g i (sliceE e y i) = b i
            then hat (M i) (sliceE e x i) (sliceE e y i) else 0) * v i (sliceE e y i)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hby : tildeE e g y = b
        · subst hby
          simp only [tensorVecE]
          rw [Finset.prod_mul_distrib]
          ring
        · obtain ⟨i, hi⟩ := Function.ne_iff.mp hby
          have hzero : (if g i (sliceE e y i) = b i
              then hat (M i) (sliceE e x i) (sliceE e y i) else 0) = 0 := ite_eq_right hi
          have hzero2 : (if g i (sliceE e y i) = b i
              then hat (M i) (sliceE e x i) (sliceE e y i) else 0) * v i (sliceE e y i)
              = 0 := by
            rw [hzero, zero_mul]
          rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero,
            Finset.prod_eq_zero (Finset.mem_univ i) hzero2]
          ring
    _ = ∑ b, Γf (tildeE e g x) b * w b *
          ∏ i, ∑ u, (if g i u = b i
            then hat (M i) (sliceE e x i) u * v i u else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        have hfact : ∀ (y : Z) (i : α),
            (if g i (sliceE e y i) = b i
              then hat (M i) (sliceE e x i) (sliceE e y i) else 0) * v i (sliceE e y i)
            = (if g i (sliceE e y i) = b i
              then hat (M i) (sliceE e x i) (sliceE e y i) * v i (sliceE e y i) else 0) := by
          intro y i
          by_cases h : g i (sliceE e y i) = b i
          · rw [ite_eq_left h, ite_eq_left h]
          · rw [ite_eq_right h, ite_eq_right h, zero_mul]
        rw [Finset.sum_congr rfl fun y _ => Finset.prod_congr rfl fun i _ => hfact y i]
        exact sum_prod_sliceE e fun i u =>
          if g i u = b i then hat (M i) (sliceE e x i) u * v i u else 0
    _ = ∑ b, Γf (tildeE e g x) b * w b *
          ∏ i, ((if tildeE e g x i = b i then ‖M i‖ else lamv i) * v i (sliceE e x i)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        congr 1
        exact Finset.prod_congr rfl fun i _ =>
          hat_guarded_row_sumGen (hM i) (hv i) (sliceE e x i) (b i)
    _ = (∏ i, v i (sliceE e x i)) *
          ∑ b, (Γf (tildeE e g x) b * Emat (fun i => ‖M i‖) lamv (tildeE e g x) b) * w b := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.prod_mul_distrib, Emat_apply]
        ring
    _ = (∏ i, v i (sliceE e x i)) *
          ((Γf ⊙ Emat (fun i => ‖M i‖) lamv) *ᵥ w) (tildeE e g x) := by
        rfl
    _ = tensorVecE e g v ((Γf ⊙ Emat (fun i => ‖M i‖) lamv) *ᵥ w) x := by
        simp only [tensorVecE]
        ring

omit [DecidableEq Z] in
/-- **K3**: tensor vectors built from inner eigenvectors and an eigenvector
of the outer auxiliary matrix are eigenvectors of the composed matrix, with
the outer eigenvalue. -/
theorem composeE_mulVec_tensorVec {g : α → (Y) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (Y) (Y) ℝ}
    (hM : ∀ i, IsAdvCol (g i) (M i))
    {v : α → (Y) → ℝ} {lamv : α → ℝ}
    (hv : ∀ i, M i *ᵥ v i = lamv i • v i)
    {w : (α → Bool) → ℝ} {μ : ℝ}
    (hw : (Γf ⊙ Emat (fun i => ‖M i‖) lamv) *ᵥ w = μ • w) :
    composeE e g Γf M *ᵥ tensorVecE e g v w = μ • tensorVecE e g v w := by
  classical
  rw [composeE_mulVec_tensorVec' e hM hv, hw]
  funext x
  simp only [tensorVecE, Pi.smul_apply, smul_eq_mul]
  ring

end General

/-! ## The cube instance -/

section Cube
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma hat_guarded_row_sum {g : (β → Bool) → Bool}
    {N : Matrix (β → Bool) (β → Bool) ℝ} (hN : IsAdvMatrix g N)
    {v : (β → Bool) → ℝ} {θ : ℝ} (hv : N *ᵥ v = θ • v) (u₀ : β → Bool)
    (b : Bool) :
    ∑ u, (if g u = b then hat N u₀ u * v u else 0)
      = (if g u₀ = b then ‖N‖ else θ) * v u₀ :=
  hat_guarded_row_sumGen hN.isAdvCol hv u₀ b

lemma sum_prod_slice (F : α → (β → Bool) → ℝ) :
    ∑ y : (α × β) → Bool, ∏ i, F i (slice y i)
      = ∏ i, ∑ u : β → Bool, F i u :=
  sum_prod_sliceE (cubeBlocks α β) F

/-- The tensor eigenvector of the composed matrix. -/
@[expose]
noncomputable def tensorVec (g : α → (β → Bool) → Bool)
    (v : α → (β → Bool) → ℝ) (w : (α → Bool) → ℝ) :
    ((α × β) → Bool) → ℝ :=
  tensorVecE (cubeBlocks α β) g v w

omit [DecidableEq α] [DecidableEq β] [Fintype β] in
@[simp] lemma tensorVec_apply (g : α → (β → Bool) → Bool)
    (v : α → (β → Bool) → ℝ) (w : (α → Bool) → ℝ) (x : (α × β) → Bool) :
    tensorVec g v w x = w (tilde g x) * ∏ i, v i (slice x i) := rfl

theorem compose_mulVec_tensorVec' {g : α → (β → Bool) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (β → Bool) (β → Bool) ℝ}
    (hM : ∀ i, IsAdvMatrix (g i) (M i))
    {v : α → (β → Bool) → ℝ} {lamv : α → ℝ}
    (hv : ∀ i, M i *ᵥ v i = lamv i • v i) (w : (α → Bool) → ℝ) :
    compose g Γf M *ᵥ tensorVec g v w
      = tensorVec g v ((Γf ⊙ Emat (fun i => ‖M i‖) lamv) *ᵥ w) :=
  composeE_mulVec_tensorVec' (cubeBlocks α β) (fun i => (hM i).isAdvCol) hv w

theorem compose_mulVec_tensorVec {g : α → (β → Bool) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (β → Bool) (β → Bool) ℝ}
    (hM : ∀ i, IsAdvMatrix (g i) (M i))
    {v : α → (β → Bool) → ℝ} {lamv : α → ℝ}
    (hv : ∀ i, M i *ᵥ v i = lamv i • v i)
    {w : (α → Bool) → ℝ} {μ : ℝ}
    (hw : (Γf ⊙ Emat (fun i => ‖M i‖) lamv) *ᵥ w = μ • w) :
    compose g Γf M *ᵥ tensorVec g v w = μ • tensorVec g v w :=
  composeE_mulVec_tensorVec (cubeBlocks α β) (fun i => (hM i).isAdvCol) hv hw

end Cube

end QuantumQueryComplexity

end SourceCompositionEigen

section DualityTraceBounds
namespace QuantumQueryComplexity
open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## Positive semidefinite matrices of bounded trace -/

section PsdNorm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a positive semidefinite matrix the spectral norm is at most the trace:
the eigenvalues are nonnegative, so the largest is at most their sum. -/
lemma norm_le_trace_of_posSemidef {G : Matrix n n ℝ} (hG : G.PosSemidef) :
    ‖G‖ ≤ G.trace := by
  have htr : G.trace = ∑ i, hG.1.eigenvalues i := by
    simpa using hG.1.trace_eq_sum_eigenvalues
  refine norm_le_of_forall_abs_eigenvalues_le hG.1 ?_ fun j => ?_
  · rw [htr]
    exact Finset.sum_nonneg fun i _ => hG.eigenvalues_nonneg i
  · rw [abs_of_nonneg (hG.eigenvalues_nonneg j), htr]
    exact Finset.single_le_sum (fun i _ => hG.eigenvalues_nonneg i) (Finset.mem_univ j)

end PsdNorm

/-- The squared norm of a standard coordinate vector. -/
lemma sum_sq_single {n : Type*} [Fintype n] [DecidableEq n] (x : n) :
    (∑ y, (Pi.single x (1 : ℝ) : n → ℝ) y * (Pi.single x (1 : ℝ) : n → ℝ) y) = 1 := by
  simp [Pi.single_apply]

/-- A diagonal quadratic form evaluated on a standard coordinate vector. -/
lemma sum_weight_sq_single {n : Type*} [Fintype n] [DecidableEq n] (a : n → ℝ) (x : n) :
    (∑ y, a y * ((Pi.single x (1 : ℝ) : n → ℝ) y
      * (Pi.single x (1 : ℝ) : n → ℝ) y)) = a x := by
  simp [Pi.single_apply]

/-- A linear functional bounded on a trace ball has the corresponding homogeneous
bound in every nonzero rank-one direction. -/
lemma rankOne_lt_of_trace_bound {n : Type*} [Fintype n]
    (L : Matrix n n ℝ →ₗ[ℝ] ℝ) {T u : ℝ} (hT : 0 < T)
    (hbound : ∀ w : n → ℝ, (∑ z, w z * w z) ≤ T → L (vecMulVec w w) < u)
    (w : n → ℝ) (hw : w ≠ 0) :
    L (vecMulVec w w) < (u / T) * ∑ z, w z * w z := by
  have hS : 0 < ∑ z, w z * w z := by
    have hnn : (0 : ℝ) ≤ ∑ z, w z * w z :=
      Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.mp (by simpa [dotProduct] using h.symm)) hw
  let a : ℝ := Real.sqrt (T / ∑ z, w z * w z)
  have ha : a * a = T / ∑ z, w z * w z := Real.mul_self_sqrt (by positivity)
  have hnorm : (∑ z, (a * w z) * (a * w z)) = T := by
    calc
      _ = (a * a) * ∑ z, w z * w z := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
      _ = T := by rw [ha, div_mul_cancel₀ _ hS.ne']
  have hscale : vecMulVec (fun z => a * w z) (fun z => a * w z)
      = (a * a) • vecMulVec w w := by
    ext z z'
    simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hlt := hbound (fun z => a * w z) hnorm.le
  rw [hscale, map_smul, smul_eq_mul, ha, div_mul_eq_mul_div, div_lt_iff₀ hS] at hlt
  rw [div_mul_eq_mul_div, lt_div_iff₀ hT]
  linarith


end QuantumQueryComplexity
end DualityTraceBounds

section SourceDualityCompactOn

/-!
# The two convex sets of the separation argument, on a promise domain

The shared implementation for promise and total inputs: the ambient coordinate space is
`DualOmegaOn X → ℝ`, the compact set is the image of the truncated positive
semidefinite cone over `GramIdxOn X ι`, and the closed set is the box around
the promise dual target.  `norm_le_trace_of_posSemidef` and
`apply_eq_sum_single` are generic and imported, not re-proved.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The coordinate index of the ambient space: a pair of promise inputs for
each constraint, and an input with a side tag for each cost variable. -/
abbrev DualOmegaOn (X : Type*) : Type _ := (X × X) ⊕ (X × Bool)

/-- The affine data of the promise dual program, read off a Gram matrix. -/
@[expose]
def gramLOn (read : X → ι → σ)
    (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) : DualOmegaOn X → ℝ :=
  Sum.elim (fun q => gramROn read G q.1 q.2) (fun q => gramCostOn G q.2 q.1)

omit [DecidableEq X] [DecidableEq ι] [Fintype X] [Fintype σ] in
@[simp] lemma gramLOn_inl (read : X → ι → σ)
    (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) (x y : X) :
    gramLOn read G (Sum.inl (x, y)) = gramROn read G x y := rfl

omit [DecidableEq X] [DecidableEq ι] [Fintype X] [Fintype σ] in
@[simp] lemma gramLOn_inr (read : X → ι → σ)
    (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) (x : X) (b : Bool) :
    gramLOn read G (Sum.inr (x, b)) = gramCostOn G b x := rfl

/-- `gramLOn` as a linear map. -/
@[expose]
def gramLOnₗ (read : X → ι → σ) :
    Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ →ₗ[ℝ] (DualOmegaOn X → ℝ) where
  toFun := gramLOn read
  map_add' G H := by
    funext z
    rcases z with ⟨x, y⟩ | ⟨x, b⟩
    · simpa using congrFun₂ (gramROn_add read G H) x y
    · simpa using gramCostOn_add G H b x
  map_smul' c G := by
    funext z
    rcases z with ⟨x, y⟩ | ⟨x, b⟩
    · simpa using congrFun₂ (gramROn_smul read c G) x y
    · simpa using gramCostOn_smul c G b x

omit [DecidableEq X] [DecidableEq ι] [Fintype X] [Fintype σ] in
@[simp] lemma gramLOnₗ_apply (read : X → ι → σ)
    (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) :
    gramLOnₗ read G = gramLOn read G := rfl

private def entryOnₗ (z z' : GramIdxOn X ι) :
    Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ →ₗ[ℝ] ℝ where
  toFun G := G z z'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq X] [DecidableEq ι] [Fintype X] [Fintype ι] in
lemma continuous_matrixEntryOn (z z' : GramIdxOn X ι) [Finite X] [Finite ι] :
    Continuous fun G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ => G z z' := by
  classical
  let := Fintype.ofFinite X
  let := Fintype.ofFinite ι
  exact (entryOnₗ z z').continuous_of_finiteDimensional

private def traceOnₗ :
    Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ →ₗ[ℝ] ℝ where
  toFun G := G.trace
  map_add' := Matrix.trace_add
  map_smul' c G := by simp

omit [DecidableEq X] [DecidableEq ι] in
lemma continuous_matrixTraceOn :
    Continuous fun G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ => G.trace :=
  traceOnₗ.continuous_of_finiteDimensional

omit [DecidableEq X] [DecidableEq ι] [Fintype X] [Fintype σ] in
lemma continuous_gramLOn (read : X → ι → σ) [Finite X] :
    Continuous
      (gramLOn read :
        Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ → DualOmegaOn X → ℝ) := by
  classical
  let := Fintype.ofFinite X
  exact (gramLOnₗ read).continuous_of_finiteDimensional

/-- Positive semidefinite matrices of trace at most `T`. -/
def psdBallOn (X ι : Type*) [Fintype X] [Fintype ι]
    (T : ℝ) : Set (Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) :=
  {G | G.PosSemidef ∧ G.trace ≤ T}

omit [DecidableEq X] [DecidableEq ι] in
lemma convex_psdBallOn (T : ℝ) : Convex ℝ (psdBallOn X ι T) := by
  rintro G ⟨hG, hGT⟩ H ⟨hH, hHT⟩ a b ha hb hab
  refine ⟨(hG.smul ha).add (hH.smul hb), ?_⟩
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul,
    smul_eq_mul]
  have h1 : a * G.trace ≤ a * T := mul_le_mul_of_nonneg_left hGT ha
  have h2 : b * H.trace ≤ b * T := mul_le_mul_of_nonneg_left hHT hb
  have h3 : a * T + b * T = T := by rw [← add_mul, hab, one_mul]
  linarith

omit [DecidableEq X] [DecidableEq ι] in
lemma isClosed_psdBallOn (T : ℝ) : IsClosed (psdBallOn X ι T) := by
  have hset : psdBallOn X ι T =
      (⋂ (z : GramIdxOn X ι) (z' : GramIdxOn X ι), {G | G z' z = G z z'}) ∩
        ((⋂ v : GramIdxOn X ι → ℝ, {G | 0 ≤ v ⬝ᵥ G *ᵥ v}) ∩
          {G | G.trace ≤ T}) := by
    ext G
    simp only [psdBallOn, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hG, hT⟩
      refine ⟨fun z z' => ?_, fun v => ?_, hT⟩
      · simpa using congrFun₂ hG.1 z z'
      · simpa using hG.dotProduct_mulVec_nonneg v
    · rintro ⟨hherm, hquad, hT⟩
      have hH : G.IsHermitian := by
        change Gᴴ = G
        ext z z'
        simpa [Matrix.conjTranspose_apply] using hherm z z'
      refine ⟨Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun v => ?_, hT⟩
      · simpa using hquad v
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun z => isClosed_iInter fun z' => ?_)
    (IsClosed.inter (isClosed_iInter fun v => ?_) ?_)
  · exact isClosed_eq (continuous_matrixEntryOn z' z) (continuous_matrixEntryOn z z')
  · refine isClosed_le continuous_const ?_
    have : (fun G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ => v ⬝ᵥ G *ᵥ v)
        = fun G => ∑ z, ∑ z', v z * G z z' * v z' := by
      funext G; exact dotProduct_mulVec_eq_sum G v v
    rw [this]
    exact continuous_finsetSum _ fun z _ => continuous_finsetSum _ fun z' _ =>
      ((continuous_const.mul (continuous_matrixEntryOn z z')).mul
        continuous_const)
  · exact isClosed_le continuous_matrixTraceOn continuous_const

omit [DecidableEq X] [DecidableEq ι] in
lemma isCompact_psdBallOn (T : ℝ) : IsCompact (psdBallOn X ι T) := by
  classical
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_psdBallOn T) ?_
  have hsub : psdBallOn X ι T ⊆
      Metric.closedBall (0 : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) T := by
    rintro G ⟨hG, hGT⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_trace_of_posSemidef hG).trans hGT
  exact Metric.isBounded_closedBall.subset hsub

/-! ## The two sets -/

/-- The image of the truncated positive semidefinite cone. -/
def gramImageOn (read : X → ι → σ) (T : ℝ) : Set (DualOmegaOn X → ℝ) :=
  gramLOn read '' psdBallOn X ι T

omit [Fintype σ] in
omit [DecidableEq X] [DecidableEq ι] in
lemma convex_gramImageOn (read : X → ι → σ) (T : ℝ) :
    Convex ℝ (gramImageOn read T) := by
  classical
  exact (convex_psdBallOn T).linear_image (gramLOnₗ read)

omit [Fintype σ] in
omit [DecidableEq X] [DecidableEq ι] in
lemma isCompact_gramImageOn (read : X → ι → σ) (T : ℝ) :
    IsCompact (gramImageOn read T) := by
  classical
  exact (isCompact_psdBallOn T).image (continuous_gramLOn read)

omit [Fintype σ] in
omit [DecidableEq X] [DecidableEq ι] in
lemma zero_mem_gramImageOn {read : X → ι → σ} {T : ℝ} (hT : 0 ≤ T) :
    (0 : DualOmegaOn X → ℝ) ∈ gramImageOn read T := by
  refine ⟨0, ⟨Matrix.PosSemidef.zero, by simpa using hT⟩, ?_⟩
  funext z
  rcases z with ⟨x, y⟩ | ⟨x, b⟩
  · simp [gramROn]
  · simp [gramCostOn]

omit [Fintype σ] in
omit [DecidableEq X] [DecidableEq ι] in
lemma mem_gramImageOn_vecMulVec {read : X → ι → σ} {T : ℝ}
    (w : GramIdxOn X ι → ℝ) (hw : ∑ z, w z * w z ≤ T) :
    gramLOn read (vecMulVec w w) ∈ gramImageOn read T :=
  ⟨vecMulVec w w, ⟨posSemidef_vecMulVec_self_on w,
    by rwa [trace_vecMulVec_on]⟩, rfl⟩

/-- The target of the promise dual program: constraint block equal to
`dualTargetOn f`, cost block in `[0, c]`. -/
def dualBoxOn (f : X → Bool) (c : ℝ) : Set (DualOmegaOn X → ℝ) :=
  {z | (∀ x y, z (Sum.inl (x, y)) = dualTargetOn f x y) ∧
    ∀ q : X × Bool, 0 ≤ z (Sum.inr q) ∧ z (Sum.inr q) ≤ c}

omit [DecidableEq X] [Fintype X] in
lemma convex_dualBoxOn (f : X → Bool) (c : ℝ) : Convex ℝ (dualBoxOn f c) := by
  rintro z ⟨hz1, hz2⟩ z' ⟨hz1', hz2'⟩ a b ha hb hab
  constructor
  · intro x y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz1 x y, hz1' x y]
    rw [← add_mul, hab, one_mul]
  · intro q
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · have := (hz2 q).1
      have := (hz2' q).1
      positivity
    · nlinarith [(hz2 q).2, (hz2' q).2, (hz2 q).1, (hz2' q).1]

omit [DecidableEq X] [Fintype X] in
lemma isClosed_dualBoxOn (f : X → Bool) (c : ℝ) : IsClosed (dualBoxOn f c) := by
  have hset : dualBoxOn f c =
      (⋂ (x : X) (y : X), {z : DualOmegaOn X → ℝ |
          z (Sum.inl (x, y)) = dualTargetOn f x y}) ∩
        ⋂ q : X × Bool,
          ({z : DualOmegaOn X → ℝ | 0 ≤ z (Sum.inr q)} ∩
            {z : DualOmegaOn X → ℝ | z (Sum.inr q) ≤ c}) := by
    ext z
    simp only [dualBoxOn, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun x => isClosed_iInter fun y => ?_)
    (isClosed_iInter fun q => IsClosed.inter ?_ ?_)
  · exact isClosed_eq (continuous_apply _) continuous_const
  · exact isClosed_le continuous_const (continuous_apply _)
  · exact isClosed_le (continuous_apply _) continuous_const

/-- The corner of the box. -/
def dualCornerOn (f : X → Bool) (c : ℝ) : DualOmegaOn X → ℝ :=
  Sum.elim (fun q => dualTargetOn f q.1 q.2) (fun _ => c)

omit [DecidableEq X] [Fintype X] in
lemma dualCornerOn_mem {f : X → Bool} {c : ℝ} (hc : 0 ≤ c) :
    dualCornerOn f c ∈ dualBoxOn f c :=
  ⟨fun _ _ => rfl, fun _ => ⟨hc, le_refl c⟩⟩

end QuantumQueryComplexity

end SourceDualityCompactOn

section SourceDualityCompact

/-!
# The two convex sets of the separation argument

The dual program is separated from its target inside the finite-dimensional
coordinate space `DualOmega ι σ → ℝ`, whose coordinates are indexed by a pair
of inputs (the constraint `gramR`) or by an input together with a side tag (the
two costs `gramCost`).  The map assembling those coordinates from a Gram matrix
is `gramL`.

Two sets live there:

* `gramImage T`, the image of the positive semidefinite matrices of trace at
  most `T` — convex because the positive semidefinite cone is, and **compact**
  because that truncated cone is closed and bounded in a finite-dimensional
  space (`‖G‖ ≤ G.trace` for positive semidefinite `G`);
* `dualBox g c`, the points whose constraint block is the dual target and whose
  cost block lies in `[0, c]` — convex and closed.

Truncating the cone at a finite trace is what makes `gramImage` compact, and
hence what lets `geometric_hahn_banach_compact_closed` apply without any
closedness-of-image argument; the truncation is harmless because a dual
solution of cost at most `c` has trace at most `2 c · card (ι → σ)`.

This section also records `apply_eq_sum_single`, which reads the coefficients of a
continuous linear functional off its values on the standard basis.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The coordinate index of the ambient space of the separation argument: a
pair of inputs for each constraint, and an input with a side tag for each cost
variable. -/
abbrev DualOmega (ι σ : Type*) : Type _ := DualOmegaOn (ι → σ)

/-- The affine data of the dual program, read off a Gram matrix. -/
@[expose]
def gramL (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) : DualOmega ι σ → ℝ := gramLOn id G

omit [DecidableEq ι] [Fintype σ] in
@[simp] lemma gramL_inl (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ)
    (x y : ι → σ) : gramL G (Sum.inl (x, y)) = gramR G x y := rfl

omit [DecidableEq ι] [Fintype σ] in
@[simp] lemma gramL_inr (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ)
    (x : ι → σ) (b : Bool) : gramL G (Sum.inr (x, b)) = gramCost G b x := rfl

/-- `gramL` as a linear map. -/
@[expose]
def gramLₗ : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ →ₗ[ℝ] (DualOmega ι σ → ℝ) := gramLOnₗ id

omit [DecidableEq ι] [Fintype σ] in
@[simp] lemma gramLₗ_apply (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) :
    gramLₗ G = gramL G := rfl

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma continuous_matrixEntry (z z' : GramIdx ι σ) [Finite ι] [Finite σ] :
    Continuous fun G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ => G z z' :=
  continuous_matrixEntryOn z z'

omit [DecidableEq σ] in
lemma continuous_matrixTrace :
    Continuous fun G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ => G.trace := continuous_matrixTraceOn

omit [DecidableEq ι] [Fintype σ] in
lemma continuous_gramL [Finite σ] :
    Continuous (gramL : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ → DualOmega ι σ → ℝ) := by
  classical
  let := Fintype.ofFinite σ
  exact continuous_gramLOn id

/-- Positive semidefinite matrices of trace at most `T`. -/
def psdBall (ι σ : Type*) [Fintype ι] [DecidableEq ι] [Fintype σ]
    (T : ℝ) : Set (Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) := psdBallOn (ι → σ) ι T

omit [DecidableEq σ] in
lemma convex_psdBall (T : ℝ) : Convex ℝ (psdBall ι σ T) := convex_psdBallOn T

omit [DecidableEq σ] in
lemma isClosed_psdBall (T : ℝ) : IsClosed (psdBall ι σ T) := isClosed_psdBallOn T

omit [DecidableEq σ] in
lemma isCompact_psdBall (T : ℝ) : IsCompact (psdBall ι σ T) := isCompact_psdBallOn T

/-! ## The two sets -/

/-- The image of the truncated positive semidefinite cone: the affine data
achievable by dual solutions of total weight at most `T`. -/
def gramImage (ι σ : Type*) [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (T : ℝ) : Set (DualOmega ι σ → ℝ) := gramImageOn (id : (ι → σ) → ι → σ) T

lemma convex_gramImage (T : ℝ) : Convex ℝ (gramImage ι σ T) := convex_gramImageOn id T

lemma isCompact_gramImage (T : ℝ) : IsCompact (gramImage ι σ T) := isCompact_gramImageOn id T

lemma zero_mem_gramImage {T : ℝ} (hT : 0 ≤ T) : (0 : DualOmega ι σ → ℝ) ∈ gramImage ι σ T :=
  zero_mem_gramImageOn hT

lemma mem_gramImage_vecMulVec {T : ℝ} (w : GramIdx ι σ → ℝ)
    (hw : ∑ z, w z * w z ≤ T) : gramL (vecMulVec w w) ∈ gramImage ι σ T :=
  mem_gramImageOn_vecMulVec w hw

/-- The target of the dual program: constraint block equal to `dualTarget g`,
cost block in `[0, c]`. -/
def dualBox (g : (ι → σ) → Bool) (c : ℝ) : Set (DualOmega ι σ → ℝ) := dualBoxOn g c

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma convex_dualBox (g : (ι → σ) → Bool) (c : ℝ) : Convex ℝ (dualBox g c) := convex_dualBoxOn g c

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma isClosed_dualBox (g : (ι → σ) → Bool) (c : ℝ) : IsClosed (dualBox g c) :=
  isClosed_dualBoxOn g c

/-- The corner of the box: the dual target with every cost variable at `c`. -/
def dualCorner (g : (ι → σ) → Bool) (c : ℝ) : DualOmega ι σ → ℝ := dualCornerOn g c

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma dualCorner_mem {g : (ι → σ) → Bool} {c : ℝ} (hc : 0 ≤ c) :
    dualCorner g c ∈ dualBox g c := dualCornerOn_mem hc

/-! ## Reading off the coefficients of a functional -/

/-- A linear functional on a finite coordinate space is the pairing with its
values on the standard basis. -/
lemma apply_eq_sum_single {α : Type*} [Fintype α] [DecidableEq α]
    (φ : (α → ℝ) →L[ℝ] ℝ) (z : α → ℝ) : φ z = ∑ a, z a * φ (Pi.single a 1) := by
  have hz : z = ∑ a, z a • (Pi.single a 1 : α → ℝ) := by
    rw [← Finset.univ_sum_single z]
    exact Finset.sum_congr rfl fun a _ => by
      funext b
      by_cases h : a = b <;> simp [Pi.single_apply, h]
  conv_lhs => rw [hz]
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul]

end QuantumQueryComplexity

end SourceDualityCompact

section SourceDualityWitness

/-!
# From a positive semidefinite certificate to an adversary matrix

This section contains the elementary half of strong duality: the construction that
turns the multipliers produced by a separating hyperplane back into a feasible
*primal* witness.

The data is a symmetric matrix `Γ`, a strictly positive weight `p` on inputs,
and the inequality

  `|s ⬝ᵥ (Γ ⊙ advD i) *ᵥ t| ≤ ∑ₓ p x · s x ² + ∑ᵧ p y · t y ²`  (for every `i`),

which says exactly that the block matrix `[[diag p, (Γ ⊙ advD i)/2], [·, diag p]]`
is positive semidefinite.  Rescaling by `√p` on both sides turns it into the
adversary feasibility constraint: `Γ' x y = Γ x y / (√(p x) √(p y))` satisfies
`‖Γ' ⊙ advD i‖ ≤ 2`.  Masking off the pairs with equal `g`-value costs nothing
in norm (`l2_opNorm_hadamard_dualTarget_le`, using that a two-valued mask is an
average of the identity and a `±1` diagonal conjugation), and evaluating the
resulting adversary matrix on the unit vector `√p / ‖√p‖` returns the pairing
`⟪Γ, dualTarget g⟫ / (2 ∑ p)`.

The generic norm estimate is proved here. The total-input certificate theorem
`lt_advPM_of_certificate` is derived from the promise construction below.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## Two auxiliary norm bounds -/

section OpNorm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A bilinear form dominated by the sum of the squared lengths of its
arguments comes from a matrix of norm at most `2`.  (Optimising the scaling
`a ↦ λ a`, `b ↦ λ⁻¹ b` is what turns the arithmetic mean into the geometric
one.) -/
lemma l2_opNorm_le_two_of_quadratic (M : Matrix n n ℝ)
    (h : ∀ a b : n → ℝ, |a ⬝ᵥ M *ᵥ b| ≤ a ⬝ᵥ a + b ⬝ᵥ b) : ‖M‖ ≤ 2 := by
  refine l2_opNorm_le_of_forall_dotProduct M (by norm_num) fun a b => ?_
  have hA0 : (0 : ℝ) ≤ a ⬝ᵥ a := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hB0 : (0 : ℝ) ≤ b ⬝ᵥ b := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  rcases eq_or_ne b 0 with rfl | hb0
  · simp
  have hA1 : 0 < Real.sqrt (a ⬝ᵥ a) :=
    Real.sqrt_pos.mpr (lt_of_le_of_ne hA0 fun h =>
      ha0 (dotProduct_self_eq_zero.mp h.symm))
  have hB1 : 0 < Real.sqrt (b ⬝ᵥ b) :=
    Real.sqrt_pos.mpr (lt_of_le_of_ne hB0 fun h =>
      hb0 (dotProduct_self_eq_zero.mp h.symm))
  set A := Real.sqrt (a ⬝ᵥ a) with hA
  set B := Real.sqrt (b ⬝ᵥ b) with hB
  -- both lengths are positive: optimise the scaling
  set lam := Real.sqrt (B / A) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr (div_pos hB1 hA1)
  have hlamsq : lam ^ 2 = B / A := Real.sq_sqrt (le_of_lt (div_pos hB1 hA1))
  have hAsq : A ^ 2 = a ⬝ᵥ a := Real.sq_sqrt hA0
  have hBsq : B ^ 2 = b ⬝ᵥ b := Real.sq_sqrt hB0
  have key := h (fun x => lam * a x) (fun y => lam⁻¹ * b y)
  have e1 : ((fun x => lam * a x) : n → ℝ) ⬝ᵥ M *ᵥ (fun y => lam⁻¹ * b y)
      = a ⬝ᵥ M *ᵥ b := by
    simp only [dotProduct_mulVec_eq_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    field_simp
  have e2 : ((fun x => lam * a x) : n → ℝ) ⬝ᵥ (fun x => lam * a x)
      = lam ^ 2 * (a ⬝ᵥ a) := by
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have e3 : ((fun y => lam⁻¹ * b y) : n → ℝ) ⬝ᵥ (fun y => lam⁻¹ * b y)
      = (lam ^ 2)⁻¹ * (b ⬝ᵥ b) := by
    simp only [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    field_simp
  rw [e1, e2, e3, ← hAsq, ← hBsq, hlamsq] at key
  have hArg : (B / A) * A ^ 2 + (B / A)⁻¹ * B ^ 2 = 2 * A * B := by
    field_simp
    ring
  rw [hArg] at key
  exact key

end OpNorm

section Mask

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The `±1` sign vector of a Boolean function. -/
def boolSign (g : (ι → σ) → Bool) : (ι → σ) → ℝ := fun x => if g x then 1 else -1

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma boolSign_eq_one_or (g : (ι → σ) → Bool) (x : ι → σ) :
    boolSign g x = 1 ∨ boolSign g x = -1 := by
  by_cases h : g x = true <;> simp [boolSign, h]

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma boolSign_mul (g : (ι → σ) → Bool) (x y : ι → σ) :
    boolSign g x * boolSign g y = 1 - 2 * dualTarget g x y := by
  rcases Bool.eq_false_or_eq_true (g x) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (g y) with h2 | h2 <;>
      simp [boolSign, dualTarget, h1, h2] <;> norm_num

end Mask

/-! ## The main construction -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

end QuantumQueryComplexity

end SourceDualityWitness

section SourcePromiseBasic

/-!
# The primal witness API on a promise domain

`SourcePromiseDefs` supplies the *upper* eliminator
`advPMOn_le`; this section supplies the *introduction* rules, so that a witness
matrix certifies `‖Γ‖ ≤ advPMOn read f` directly.

There is one hypothesis here that the total case does not need.  `advPM` is a
supremum over feasible matrices, and boundedness of that set comes from the
observation that a feasible matrix vanishes wherever no query separates the two
inputs.  On a promise domain two *distinct* inputs may look identical at every
query, and then nothing constrains `Γ` there at all: the value set is unbounded
and `sSup` degenerates.  So every lemma below assumes

  `hdet : ∀ x y, read x = read y → f x = f y`,

i.e. the observations determine the output. Injectivity of `read` implies
this condition, as `separates_of_injective` records.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {O : Type*} {read : X → ι → σ} {f : X → O} {Γ : Matrix X X ℝ}

omit [DecidableEq X] [DecidableEq ι] [DecidableEq σ] [Fintype X] [Fintype ι] in
/-- An injective observation map determines the output. -/
lemma separates_of_injective (hread : Function.Injective read) (f : X → O) :
    ∀ x y, read x = read y → f x = f y := fun _ _ h => by rw [hread h]

omit [DecidableEq ι] [Fintype ι] in
/-- All entries of a feasible matrix are bounded by `1`: entries with equal
output vanish, and the rest are separated by some query. -/
lemma abs_apply_le_one_of_feasibleOn
    (hdet : ∀ x y, read x = read y → f x = f y) (h1 : IsAdvMatrixOn f Γ)
    (h2 : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) (x y : X) : |Γ x y| ≤ 1 := by
  classical
  by_cases hf : f x = f y
  · simp [h1.2 x y hf]
  · have hxy : read x ≠ read y := fun h => hf (hdet x y h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    have h3 := abs_entry_le_l2_opNorm (Γ ⊙ advDOn read i) x y
    rw [hadamard_advDOn_apply, ite_eq_right hi] at h3
    exact h3.trans (h2 i)

omit [DecidableEq ι] [Fintype ι] in
/-- The a priori bound making the `advPMOn` value set bounded above. -/
lemma norm_le_of_feasibleOn (hdet : ∀ x y, read x = read y → f x = f y)
    (h1 : IsAdvMatrixOn f Γ) (h2 : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) :
    ‖Γ‖ ≤ (Fintype.card X : ℝ) ^ 2 := by
  classical
  refine (l2_opNorm_le_sum_abs Γ).trans ?_
  calc ∑ x, ∑ y, |Γ x y| ≤ ∑ _x : X, ∑ _y : X, (1 : ℝ) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        abs_apply_le_one_of_feasibleOn hdet h1 h2 x y
    _ = (Fintype.card X : ℝ) ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, pow_two]

omit [DecidableEq ι] [Fintype ι] in
lemma bddAbove_advPMOn_set (hdet : ∀ x y, read x = read y → f x = f y) :
    BddAbove {r : ℝ | ∃ Γ, IsAdvMatrixOn f Γ ∧
      (∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) ∧ r = ‖Γ‖} := by
  classical
  refine ⟨(Fintype.card X : ℝ) ^ 2, ?_⟩
  rintro r ⟨Γ, h1, h2, rfl⟩
  exact norm_le_of_feasibleOn hdet h1 h2

omit [DecidableEq ι] [Fintype ι] in
/-- **Every feasible matrix certifies a lower bound on `advPMOn`.** -/
theorem le_advPMOn (hdet : ∀ x y, read x = read y → f x = f y)
    (h1 : IsAdvMatrixOn f Γ) (h2 : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) :
    ‖Γ‖ ≤ advPMOn read f := by
  classical
  exact le_csSup (bddAbove_advPMOn_set hdet) ⟨Γ, h1, h2, rfl⟩

omit [DecidableEq ι] [Fintype ι] in
theorem advPMOn_nonneg (hdet : ∀ x y, read x = read y → f x = f y) :
    0 ≤ advPMOn read f := by
  classical
  simpa using le_advPMOn (Γ := (0 : Matrix X X ℝ)) hdet (isAdvMatrixOn_zero f)
    fun i => by simp

omit [DecidableEq X] [Fintype X] in
lemma IsAdvMatrixOn.smul (h : IsAdvMatrixOn f Γ) (c : ℝ) :
    IsAdvMatrixOn f (c • Γ) :=
  ⟨h.1.smul (star_trivial c), fun x y hxy => by
    rw [Matrix.smul_apply, h.2 x y hxy, smul_zero]⟩

omit [DecidableEq ι] [Fintype ι] in
/-- **The un-normalized witness lemma on a promise domain.** Exhibit a matrix,
bound its masked norms by `c`, and read off `‖Γ‖ / c`. -/
theorem norm_div_le_advPMOn (hdet : ∀ x y, read x = read y → f x = f y)
    (h1 : IsAdvMatrixOn f Γ) {c : ℝ}
    (h2 : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ c) (hc : 0 < c) :
    ‖Γ‖ / c ≤ advPMOn read f := by
  classical
  have k1 : IsAdvMatrixOn f (c⁻¹ • Γ) := h1.smul c⁻¹
  have k2 : ∀ i, ‖(c⁻¹ • Γ) ⊙ advDOn read i‖ ≤ 1 := fun i => by
    rw [Matrix.smul_hadamard, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hc)]
    calc c⁻¹ * ‖Γ ⊙ advDOn read i‖ ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left (h2 i) (inv_pos.mpr hc).le
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have h := le_advPMOn hdet k1 k2
  rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc),
    inv_mul_eq_div] at h

omit [DecidableEq ι] [Fintype ι] in
/-- The ε-accessor, for arguments that need a witness beating a given value. -/
theorem exists_lt_of_lt_advPMOn {c : ℝ} (h : c < advPMOn read f) :
    ∃ Γ, IsAdvMatrixOn f Γ ∧ (∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) ∧ c < ‖Γ‖ := by
  classical
  obtain ⟨r, hr, hcr⟩ := exists_lt_of_lt_csSup (advPMOn_set_nonempty read f) h
  obtain ⟨Γ, h1, h2, rfl⟩ := hr
  exact ⟨Γ, h1, h2, hcr⟩

/-! ## The total case is a promise on the whole cube

A sanity check that the promise API really extends the total one: reading the
identity on the full cube gives back `advPM`. -/

section Total
variable [Fintype σ] [DecidableEq O]

omit [DecidableEq ι] [Fintype ι] [Fintype σ] in
@[simp] lemma advDOn_id (i : ι) :
    advDOn (fun x : ι → σ => x) i = advD i := rfl

omit [DecidableEq O] [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma isAdvMatrixOn_id_iff {g : (ι → σ) → O}
    {Γ : Matrix (ι → σ) (ι → σ) ℝ} :
    IsAdvMatrixOn g Γ ↔ IsAdvMatrix g Γ := Iff.rfl

omit [DecidableEq O] in
@[simp] theorem advPMOn_id (g : (ι → σ) → O) :
    advPMOn (fun x : ι → σ => x) g = advPM g := rfl

end Total

end QuantumQueryComplexity

end SourcePromiseBasic

section SourceCompositionSpan

/-!
# Spanning by tensor eigenvectors (HLŠ Lemma 16, Item 3)

The family of tensor vectors `tensorVecE e g (v' · (c ·)) (ofLp (W c j))` — over
all eigen-index assignments `c : α → Y` and all members `j` of an orthonormal
basis `W c` of the outer space — spans the whole composed space.

Route: pure tensors of orthonormal families are orthonormal
(`tensor_orthonormalE`, via the `sum_prod_sliceE` interchange), hence linearly
independent; their cardinality equals the dimension, so they span; and each
pure tensor lies in the span of the family because `tensorVecE` is linear in
its outer argument and `W c` is a basis.

As in `SourceCompositionHat` the block decomposition is abstract: everything is proved for
`e : Z ≃ (α → Y)` with `Y` an arbitrary finite type, and the cube statements are
the `cubeBlocks` instance.  The only cube-specific step was the dimension count
`Fintype.card ((α × β) → Bool) = Fintype.card (α → (β → Bool))`, which is now
just `Fintype.card_congr e.symm`.

This section is the second (and last) `WithLp`/`EuclideanSpace` quarantine zone.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix

/-- **S2**: transporting a spanning statement from `EuclideanSpace` to the
plain Pi module. -/
lemma span_top_of_toLp {n κ : Type*} (T : κ → (n → ℝ))
    (h : Submodule.span ℝ (Set.range fun k =>
      (WithLp.toLp 2 (T k) : EuclideanSpace ℝ n)) = ⊤) :
    Submodule.span ℝ (Set.range T) = ⊤ := by
  classical
  have himg : Set.range T
      = ⇑(WithLp.linearEquiv 2 ℝ (n → ℝ)).toLinearMap ''
        Set.range (fun k => (WithLp.toLp 2 (T k) : EuclideanSpace ℝ n)) := by
    rw [← Set.range_comp]
    rfl
  rw [himg, Submodule.span_image, h, Submodule.map_top, LinearMap.range_eq_top]
  exact (WithLp.linearEquiv 2 ℝ (n → ℝ)).surjective

/-! ## Spanning over an abstract block decomposition -/

section General

variable {α Y Z : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq α] in
/-- **S1**: pure tensors of orthonormal families are orthonormal. -/
lemma tensor_orthonormalE (e : Z ≃ (α → Y)) {v' : α → Y → Y → ℝ}
    (hON : ∀ i, Orthonormal ℝ fun d =>
      (WithLp.toLp 2 (v' i d) : EuclideanSpace ℝ Y)) :
    Orthonormal ℝ fun c : α → Y =>
      (WithLp.toLp 2 (fun x => ∏ i, v' i (c i) (sliceE e x i)) :
        EuclideanSpace ℝ Z) := by
  classical
  rw [orthonormal_iff_ite]
  intro c c'
  rw [inner_toLp]
  have hstep : (fun x : Z => ∏ i, v' i (c i) (sliceE e x i)) ⬝ᵥ
      (fun x => ∏ i, v' i (c' i) (sliceE e x i))
      = ∏ i, (v' i (c i) ⬝ᵥ v' i (c' i)) := by
    calc (fun x : Z => ∏ i, v' i (c i) (sliceE e x i)) ⬝ᵥ
        (fun x => ∏ i, v' i (c' i) (sliceE e x i))
        = ∑ x : Z,
            (∏ i, v' i (c i) (sliceE e x i)) *
              ∏ i, v' i (c' i) (sliceE e x i) := rfl
      _ = ∑ x : Z,
            ∏ i, (v' i (c i) (sliceE e x i) * v' i (c' i) (sliceE e x i)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.prod_mul_distrib]
      _ = ∏ i, ∑ u, v' i (c i) u * v' i (c' i) u :=
          sum_prod_sliceE e fun i u => v' i (c i) u * v' i (c' i) u
      _ = ∏ i, (v' i (c i) ⬝ᵥ v' i (c' i)) := rfl
  rw [hstep]
  have hij : ∀ i, v' i (c i) ⬝ᵥ v' i (c' i) = if c i = c' i then 1 else 0 := by
    intro i
    have h := orthonormal_iff_ite.mp (hON i) (c i) (c' i)
    rwa [inner_toLp] at h
  rw [Finset.prod_congr rfl fun i _ => hij i]
  by_cases hcc : c = c'
  · rw [ite_eq_left hcc, hcc]
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hcc
    rw [ite_eq_right hcc, Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)]

omit [DecidableEq Y] [DecidableEq Z] [Fintype Z] in
/-- **S3**: the tensor eigenvector family spans everything. -/
lemma span_tensorVecE_top (e : Z ≃ (α → Y)) {g : α → Y → Bool}
    (v' : α → Y → Y → ℝ)
    (hON : ∀ i, Orthonormal ℝ fun d =>
      (WithLp.toLp 2 (v' i d) : EuclideanSpace ℝ Y))
    (W : (α → Y) → OrthonormalBasis (α → Bool) ℝ
      (EuclideanSpace ℝ (α → Bool))) [Finite Z] :
    Submodule.span ℝ (Set.range fun p : (α → Y) × (α → Bool) =>
      tensorVecE e g (fun i => v' i (p.1 i)) (WithLp.ofLp (W p.1 p.2))) = ⊤ := by
  classical
  let := Fintype.ofFinite Z
  -- The eigen-index type `α → Y` can be empty when `Y` is; then so is `Z`, and
  -- the whole space is trivial.  (At a cube this branch never fires.)
  rcases isEmpty_or_nonempty (α → Y) with hE | hE
  · have : IsEmpty Z := Function.isEmpty e
    rw [eq_top_iff]
    intro v _
    rw [show v = 0 from funext fun z => isEmptyElim z]
    exact Submodule.zero_mem _
  rw [eq_top_iff]
  have hPT : Submodule.span ℝ (Set.range fun c : α → Y =>
      fun x : Z => ∏ i, v' i (c i) (sliceE e x i)) = ⊤ := by
    apply span_top_of_toLp
    refine LinearIndependent.span_eq_top_of_card_eq_finrank
      (tensor_orthonormalE e hON).linearIndependent ?_
    rw [finrank_euclideanSpace]
    exact Fintype.card_congr e.symm
  rw [← hPT]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨c, rfl⟩
  change (fun x : Z => ∏ i, v' i (c i) (sliceE e x i)) ∈ _
  let φ : ((α → Bool) → ℝ) →ₗ[ℝ] (Z → ℝ) :=
    { toFun := fun w => tensorVecE e g (fun i => v' i (c i)) w
      map_add' := fun a b => by
        funext x
        simp only [tensorVecE_apply, Pi.add_apply]
        ring
      map_smul' := fun m a => by
        funext x
        simp only [tensorVecE_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hWspan : Submodule.span ℝ
      (Set.range fun j => WithLp.ofLp (W c j)) = ⊤ := by
    apply span_top_of_toLp
    have heq : (fun j => (WithLp.toLp 2 (WithLp.ofLp (W c j)) :
        EuclideanSpace ℝ (α → Bool))) = fun j => W c j := rfl
    rw [heq]
    have hcoe : (fun j => W c j) = ⇑(W c).toBasis := by
      funext j
      rw [OrthonormalBasis.coe_toBasis]
    rw [hcoe]
    exact (W c).toBasis.span_eq
  have h1 : (fun _ : α → Bool => (1 : ℝ)) ∈
      Submodule.span ℝ (Set.range fun j => WithLp.ofLp (W c j)) := by
    rw [hWspan]
    exact Submodule.mem_top
  have h2 : φ (fun _ => 1) ∈
      Submodule.map φ (Submodule.span ℝ
        (Set.range fun j => WithLp.ofLp (W c j))) :=
    Submodule.mem_map_of_mem h1
  rw [← Submodule.span_image] at h2
  have hPTeq : (fun x : Z => ∏ i, v' i (c i) (sliceE e x i))
      = φ (fun _ => 1) := by
    funext x
    change _ = tensorVecE e g (fun i => v' i (c i)) (fun _ => 1) x
    simp [tensorVecE_apply]
  rw [hPTeq]
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  exact ⟨(c, j), rfl⟩

end General

/-! ## The cube instance -/

section Cube

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **S1**, cube form. -/
lemma tensor_orthonormal {v' : α → (β → Bool) → (β → Bool) → ℝ}
    (hON : ∀ i, Orthonormal ℝ fun d =>
      (WithLp.toLp 2 (v' i d) : EuclideanSpace ℝ (β → Bool))) :
    Orthonormal ℝ fun c : α → (β → Bool) =>
      (WithLp.toLp 2 (fun x => ∏ i, v' i (c i) (slice x i)) :
        EuclideanSpace ℝ ((α × β) → Bool)) :=
  tensor_orthonormalE (cubeBlocks α β) hON

/-- **S3**, cube form. -/
lemma span_tensorVec_top {g : α → (β → Bool) → Bool}
    (v' : α → (β → Bool) → (β → Bool) → ℝ)
    (hON : ∀ i, Orthonormal ℝ fun d =>
      (WithLp.toLp 2 (v' i d) : EuclideanSpace ℝ (β → Bool)))
    (W : (α → (β → Bool)) → OrthonormalBasis (α → Bool) ℝ
      (EuclideanSpace ℝ (α → Bool))) :
    Submodule.span ℝ (Set.range fun p : (α → (β → Bool)) × (α → Bool) =>
      tensorVec g (fun i => v' i (p.1 i)) (WithLp.ofLp (W p.1 p.2))) = ⊤ :=
  span_tensorVecE_top (cubeBlocks α β) v' hON W

end Cube

end QuantumQueryComplexity

end SourceCompositionSpan


section SourcePromisePost

/-!
# Post-composition lowers the promise adversary bound

An adversary matrix for `g ∘ f` is supported on pairs with `g (f x) ≠ g (f y)`,
hence on pairs with `f x ≠ f y` — so it is an adversary matrix for `f`, with
the same feasibility.  The suprema then compare directly:

    advPMOn read (g ∘ f) ≤ advPMOn read f.

This is the promise mirror of the `advPM_comp_le` post-processing lemma, and
it is what makes the **bit encoding** of a finite output type free on the
adversary side: each output bit is a post-composition of `f`, so its promise
adversary bound is at most that of `f`.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {O O' : Type*} [DecidableEq O] [DecidableEq O']

omit [DecidableEq O'] [DecidableEq O] [DecidableEq X] [Fintype X] in
/-- An adversary matrix for a post-composition is one for the base
function. -/
lemma IsAdvMatrixOn.of_comp {f : X → O} {g : O → O'} {Γ : Matrix X X ℝ}
    (h : IsAdvMatrixOn (fun x => g (f x)) Γ) : IsAdvMatrixOn f Γ :=
  ⟨h.1, fun x y hxy => h.2 x y (by change g (f x) = g (f y); rw [hxy])⟩

omit [DecidableEq O'] [DecidableEq O] [DecidableEq X] [DecidableEq ι] [DecidableEq σ]
    [Fintype X] [Fintype ι] [Fintype σ] in
/-- Determinacy transfers to any post-composition. -/
lemma det_comp {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) (g : O → O') :
    ∀ x y, read x = read y → g (f x) = g (f y) := by
  classical
  exact fun x y hxy => by rw [hdet x y hxy]

omit [DecidableEq O'] [DecidableEq O] [DecidableEq ι] [Fintype ι] [Fintype σ] in
/-- **Post-composition lowers the promise adversary bound.** -/
theorem advPMOn_comp_le {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) (g : O → O') :
    advPMOn read (fun x => g (f x)) ≤ advPMOn read f := by
  classical
  refine csSup_le (advPMOn_set_nonempty read _) ?_
  rintro r ⟨Γ, h1, h2, rfl⟩
  exact le_advPMOn hdet h1.of_comp h2

/-! ## Relabelling the answers

An injective relabelling of the oracle's answers changes nothing: the masks
`advDOn` only ask whether two promise inputs are distinguished at `i`. -/

variable {σ' : Type*} [DecidableEq σ']

omit [DecidableEq X] [DecidableEq ι] [Fintype X] [Fintype ι] [Fintype σ] in
lemma advDOn_comp_injective {φ : σ → σ'} (hφ : Function.Injective φ)
    (read : X → ι → σ) (i : ι) :
    advDOn (fun x j => φ (read x j)) i = advDOn read i := by
  classical
  ext x y
  rw [advDOn_apply, advDOn_apply]
  refine if_congr ?_ rfl rfl
  exact ⟨fun h => hφ h, fun h => congrArg φ h⟩

omit [DecidableEq O] [DecidableEq ι] [Fintype ι] [Fintype σ] in
/-- **The adversary bound is invariant under injective relabelling of the
answers.** -/
theorem advPMOn_comp_injective {φ : σ → σ'} (hφ : Function.Injective φ)
    (read : X → ι → σ) (f : X → O) :
    advPMOn (fun x j => φ (read x j)) f = advPMOn read f := by
  classical
  have hset : {r : ℝ | ∃ Γ, IsAdvMatrixOn f Γ
        ∧ (∀ i, ‖Γ ⊙ advDOn (fun x j => φ (read x j)) i‖ ≤ 1) ∧ r = ‖Γ‖}
      = {r : ℝ | ∃ Γ, IsAdvMatrixOn f Γ
        ∧ (∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) ∧ r = ‖Γ‖} := by
    ext r
    constructor
    · rintro ⟨Γ, h1, h2, rfl⟩
      exact ⟨Γ, h1, fun i => by rw [← advDOn_comp_injective hφ read i]; exact h2 i,
        rfl⟩
    · rintro ⟨Γ, h1, h2, rfl⟩
      exact ⟨Γ, h1, fun i => by rw [advDOn_comp_injective hφ read i]; exact h2 i,
        rfl⟩
  rw [advPMOn, advPMOn, hset]

end QuantumQueryComplexity

end SourcePromisePost

section SourceCompositionNormCompose

/-!
# The norm of a composed matrix (HLŠ Lemma 16 / BL Lemma 21)

`‖composeE e g Γf M‖ = ‖Γf‖ * ∏ i, ‖M i‖` for symmetric `Γf` and g-shaped
inner matrices `M i`.

* `≤` (`normE_compose_le`): every tensor eigenvector's eigenvalue is an
  eigenvalue of some `Γf ⊙ Emat`, bounded via the Schur-multiplier estimate;
  the tensor eigenvectors span, so the spanning-eigenvector bound applies.
  No sign-flipping analysis is needed (this replaces HLŠ's Item 4 — and
  repairs the gap in BL Lemma 21's Eq. (4), whose orthogonality claim fails
  for ±-paired eigenvalues of the dilation).
* `≥` (`le_normE_compose`): at the sign vertex `Emat` degenerates to a
  `±1`-diagonal conjugate of `(∏ ‖M i‖) • Γf`, producing an explicit tensor
  eigenvector with eigenvalue `± ‖Γf‖ * ∏ ‖M i‖`; it is nonvanishing by the
  bipartite-support lemma.

As in `SourceCompositionHat` the block decomposition is abstract, and the cube statements
`norm_compose_le` / `le_norm_compose` / `norm_compose` are the `cubeBlocks`
instance.  Two side conditions appear in the general form and are automatic at
a cube: the `≤` direction is stated for a possibly empty composed type `Z`
(the spanning-eigenvector bound wants `Nonempty`), and the `≥` direction needs
`Nonempty Y` to select an inner eigenvalue of maximal modulus.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

lemma div_self_sq {a R : ℝ} (hR : 0 < R) (h : |a| = R) :
    a / R * (a / R) = 1 := by
  have h1 : a * a = R * R := by
    have h2 := sq_abs a
    rw [h, pow_two, pow_two] at h2
    exact h2.symm
  rw [div_mul_div_comm, h1]
  exact div_self (by positivity)

/-- The vertex eigen-computation: at a sign vertex, an eigenvector of `Γf`
conjugated by the `±1` diagonal is an eigenvector of `Γf ⊙ Emat R lam` with
eigenvalue `(∏ R) * θ`. -/
lemma vertex_eigen {α : Type*} [Fintype α] [DecidableEq α]
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {R lam ε : α → ℝ}
    (hε : ∀ i, ε i * ε i = 1) (hlam_eq : ∀ i, ε i * R i = lam i)
    {θ : ℝ} {w : (α → Bool) → ℝ} (hw : Γf *ᵥ w = θ • w) :
    (Γf ⊙ Emat R lam) *ᵥ (Matrix.diagonal (chiSign ε) *ᵥ w)
      = ((∏ i, R i) * θ) • (Matrix.diagonal (chiSign ε) *ᵥ w) := by
  have hlam_fun : (fun i => ε i * R i) = lam := funext hlam_eq
  rw [← hlam_fun, hadamard_Emat_vertex Γf hε, Matrix.smul_mulVec]
  have hcore : (Matrix.diagonal (chiSign ε) * Γf * Matrix.diagonal (chiSign ε))
      *ᵥ (Matrix.diagonal (chiSign ε) *ᵥ w)
      = θ • (Matrix.diagonal (chiSign ε) *ᵥ w) := by
    rw [Matrix.mulVec_mulVec,
      mul_assoc (Matrix.diagonal (chiSign ε) * Γf),
      diagonal_chiSign_mul_self hε, mul_one,
      ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  rw [hcore, smul_smul]

/-! ## The norm formula over an abstract block decomposition -/

section General

variable {α Y Z : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
variable {g : α → Y → Bool} {Γf : Matrix (α → Bool) (α → Bool) ℝ}
  {M : α → Matrix Y Y ℝ}

/-- The `≤` direction of HLŠ Lemma 16. -/
theorem normE_compose_le (e : Z ≃ (α → Y)) (hΓf : Γf.IsHermitian)
    (hM : ∀ i, IsAdvCol (g i) (M i)) :
    ‖composeE e g Γf M‖ ≤ ‖Γf‖ * ∏ i, ‖M i‖ := by
  classical
  have hRHS : 0 ≤ ‖Γf‖ * ∏ i, ‖M i‖ :=
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · have h0 : composeE e g Γf M = 0 := by
      ext x y
      exact hZ.elim x
    rw [h0, norm_zero]
    exact hRHS
  have : Nonempty Z := hZ
  have hAH : ∀ c : α → Y,
      (Γf ⊙ Emat (fun i => ‖M i‖)
        fun i => (hM i).isHermitian.eigenvalues (c i)).IsHermitian :=
    fun c => hΓf.hadamard (Emat_isHermitian _ _)
  refine norm_le_of_eigenvector_family
    (composeE_isHermitian e g hΓf fun i => (hM i).isHermitian)
    (fun p : (α → Y) × (α → Bool) =>
      tensorVecE e g
        (fun i => WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis (p.1 i)))
        (WithLp.ofLp ((hAH p.1).eigenvectorBasis p.2)))
    (fun p => (hAH p.1).eigenvalues p.2) hRHS ?_ ?_ ?_
  · rintro ⟨c, j⟩
    exact composeE_mulVec_tensorVec e hM
      (fun i => (hM i).isHermitian.mulVec_eigenvectorBasis (c i))
      ((hAH c).mulVec_eigenvectorBasis j)
  · exact span_tensorVecE_top e
      (fun i d => WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis d))
      (fun i => (hM i).isHermitian.eigenvectorBasis.orthonormal)
      (fun c => (hAH c).eigenvectorBasis)
  · rintro ⟨c, j⟩
    calc |(hAH c).eigenvalues j|
        ≤ ‖Γf ⊙ Emat (fun i => ‖M i‖)
            fun i => (hM i).isHermitian.eigenvalues (c i)‖ :=
          abs_eigenvalues_le_norm (hAH c) j
      _ ≤ (∏ i, ‖M i‖) * ‖Γf‖ :=
          norm_hadamard_Emat_le Γf (fun i => norm_nonneg (M i))
            (fun i => abs_eigenvalues_le_norm (hM i).isHermitian (c i))
      _ = ‖Γf‖ * ∏ i, ‖M i‖ := mul_comm _ _

/-- The `≥` direction of HLŠ Lemma 16. -/
theorem le_normE_compose [Nonempty Y] (e : Z ≃ (α → Y)) (hΓf : Γf.IsHermitian)
    (hM : ∀ i, IsAdvCol (g i) (M i)) :
    ‖Γf‖ * ∏ i, ‖M i‖ ≤ ‖composeE e g Γf M‖ := by
  classical
  by_cases hz : ∃ i, ‖M i‖ = 0
  · obtain ⟨i₀, hi₀⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hi₀, mul_zero]
    exact norm_nonneg _
  push Not at hz
  have hMpos : ∀ i, 0 < ‖M i‖ := fun i =>
    (norm_nonneg (M i)).lt_of_ne (Ne.symm (hz i))
  have hpick : ∀ i, ∃ d, |(hM i).isHermitian.eigenvalues d| = ‖M i‖ := fun i =>
    exists_abs_eigenvalues_eq_norm (hM i).isHermitian
  choose d hd using hpick
  have hlam0 : ∀ i, (hM i).isHermitian.eigenvalues (d i) ≠ 0 := by
    intro i h
    have h2 := hd i
    rw [h, abs_zero] at h2
    exact (hMpos i).ne' h2.symm
  have hε : ∀ i, ((hM i).isHermitian.eigenvalues (d i) / ‖M i‖) *
      ((hM i).isHermitian.eigenvalues (d i) / ‖M i‖) = 1 := fun i =>
    div_self_sq (hMpos i) (hd i)
  have hlam_eq : ∀ i, ((hM i).isHermitian.eigenvalues (d i) / ‖M i‖) * ‖M i‖
      = (hM i).isHermitian.eigenvalues (d i) := fun i =>
    div_mul_cancel₀ _ (hMpos i).ne'
  -- the outer eigen-pair with |θ| = ‖Γf‖
  obtain ⟨j₀, hj₀⟩ := exists_abs_eigenvalues_eq_norm hΓf
  have hw : Γf *ᵥ WithLp.ofLp (hΓf.eigenvectorBasis j₀)
      = hΓf.eigenvalues j₀ • WithLp.ofLp (hΓf.eigenvectorBasis j₀) :=
    hΓf.mulVec_eigenvectorBasis j₀
  have hw0 : WithLp.ofLp (hΓf.eigenvectorBasis j₀) ≠ 0 := fun h0 =>
    hΓf.eigenvectorBasis.orthonormal.ne_zero j₀ (by
      have hb : hΓf.eigenvectorBasis j₀
          = WithLp.toLp 2 (WithLp.ofLp (hΓf.eigenvectorBasis j₀)) := rfl
      rw [hb, h0]
      rfl)
  have hvert := vertex_eigen (ε := fun i =>
      (hM i).isHermitian.eigenvalues (d i) / ‖M i‖)
    (lam := fun i => (hM i).isHermitian.eigenvalues (d i))
    (R := fun i => ‖M i‖) hε hlam_eq hw
  have hvv : ∀ i, M i *ᵥ
      WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis (d i))
      = (hM i).isHermitian.eigenvalues (d i) •
        WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis (d i)) := fun i =>
    (hM i).isHermitian.mulVec_eigenvectorBasis (d i)
  have hbig := composeE_mulVec_tensorVec e hM hvv hvert
  -- nonvanishing of the tensor witness
  have hvv0 : ∀ i,
      WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis (d i)) ≠ 0 := fun i h0 =>
    (hM i).isHermitian.eigenvectorBasis.orthonormal.ne_zero (d i) (by
      have hb : (hM i).isHermitian.eigenvectorBasis (d i)
          = WithLp.toLp 2
            (WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis (d i))) := rfl
      rw [hb, h0]
      rfl)
  have hwstar0 : Matrix.diagonal (chiSign fun i =>
      (hM i).isHermitian.eigenvalues (d i) / ‖M i‖) *ᵥ
      WithLp.ofLp (hΓf.eigenvectorBasis j₀) ≠ 0 :=
    chiSign_diagonal_mulVec_ne_zero hε hw0
  have hT0 : tensorVecE e g
      (fun i => WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis (d i)))
      (Matrix.diagonal (chiSign fun i =>
        (hM i).isHermitian.eigenvalues (d i) / ‖M i‖) *ᵥ
        WithLp.ofLp (hΓf.eigenvectorBasis j₀)) ≠ 0 := by
    obtain ⟨a₀, ha₀⟩ := Function.ne_iff.mp hwstar0
    have hsupp : ∀ i, ∃ u, g i u = a₀ i ∧
        WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis (d i)) u ≠ 0 :=
      fun i => (hM i).exists_eigenvector_support (hvv i) (hlam0 i) (hvv0 i)
        (a₀ i)
    choose u hu1 hu2 using hsupp
    have hslice : ∀ i, sliceE e (e.symm u) i = u i := fun i =>
      congrFun (e.apply_symm_apply u) i
    intro h0
    have hx := congrFun h0 (e.symm u)
    simp only [tensorVecE_apply, Pi.zero_apply] at hx
    have htilde : tildeE e g (e.symm u) = a₀ := by
      funext i
      rw [tildeE_apply, hslice i]
      exact hu1 i
    rw [htilde] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact ha₀ h
    · obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h
      rw [hslice i] at hi
      exact hu2 i hi
  have habs := abs_eigenvalue_le_norm hbig hT0
  calc ‖Γf‖ * ∏ i, ‖M i‖
      = |(∏ i, ‖M i‖) * hΓf.eigenvalues j₀| := by
        rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ =>
          norm_nonneg (M i)), hj₀]
        ring
    _ ≤ ‖composeE e g Γf M‖ := habs

/-- HLŠ Lemma 16 / BL Lemma 21, over an abstract block decomposition. -/
theorem normE_compose [Nonempty Y] (e : Z ≃ (α → Y)) (hΓf : Γf.IsHermitian)
    (hM : ∀ i, IsAdvCol (g i) (M i)) :
    ‖composeE e g Γf M‖ = ‖Γf‖ * ∏ i, ‖M i‖ :=
  le_antisymm (normE_compose_le e hΓf hM) (le_normE_compose e hΓf hM)

end General

/-! ## The cube instance -/

section Cube

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  {g : α → (β → Bool) → Bool} {Γf : Matrix (α → Bool) (α → Bool) ℝ}
  {M : α → Matrix (β → Bool) (β → Bool) ℝ}

/-- The `≤` direction of HLŠ Lemma 16. -/
theorem norm_compose_le (hΓf : Γf.IsHermitian)
    (hM : ∀ i, IsAdvMatrix (g i) (M i)) :
    ‖compose g Γf M‖ ≤ ‖Γf‖ * ∏ i, ‖M i‖ :=
  normE_compose_le (cubeBlocks α β) hΓf fun i => (hM i).isAdvCol

/-- The `≥` direction of HLŠ Lemma 16. -/
theorem le_norm_compose (hΓf : Γf.IsHermitian)
    (hM : ∀ i, IsAdvMatrix (g i) (M i)) :
    ‖Γf‖ * ∏ i, ‖M i‖ ≤ ‖compose g Γf M‖ :=
  le_normE_compose (cubeBlocks α β) hΓf fun i => (hM i).isAdvCol

/-- HLŠ Lemma 16 / BL Lemma 21: the norm of the composed matrix. -/
theorem norm_compose (hΓf : Γf.IsHermitian)
    (hM : ∀ i, IsAdvMatrix (g i) (M i)) :
    ‖compose g Γf M‖ = ‖Γf‖ * ∏ i, ‖M i‖ :=
  le_antisymm (norm_compose_le hΓf hM) (le_norm_compose hΓf hM)

end Cube

end QuantumQueryComplexity

end SourceCompositionNormCompose


section SourceDualityWitnessOn

/-!
# From a certificate to an adversary matrix, on a promise domain

The promise mirror of `SourceDualityWitness`: the multipliers of the
separating hyperplane become a feasible `IsAdvMatrixOn` witness, so the
certificate forces `c < advPMOn read f`.  The two generic norm lemmas
(`l2_opNorm_le_two_of_quadratic` and the `±1` diagonal conjugation) are
imported, not re-proved; the `±1` mask argument uses only that the *output*
is two-valued, which holds verbatim for `f : X → Bool`.

`hdet` (read-determinacy) enters exactly once, through `le_advPMOn` — the
promise adversary bound is a supremum only over a bounded set when the
promise is determined.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

section Mask

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The `±1` sign vector of a Boolean function on the promise domain. -/
def boolSignOn (f : X → Bool) : X → ℝ := fun x => if f x then 1 else -1

omit [DecidableEq X] [Fintype X] in
lemma boolSignOn_eq_one_or (f : X → Bool) (x : X) :
    boolSignOn f x = 1 ∨ boolSignOn f x = -1 := by
  by_cases h : f x = true <;> simp [boolSignOn, h]

omit [DecidableEq X] [Fintype X] in
lemma boolSignOn_mul (f : X → Bool) (x y : X) :
    boolSignOn f x * boolSignOn f y = 1 - 2 * dualTargetOn f x y := by
  rcases Bool.eq_false_or_eq_true (f x) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (f y) with h2 | h2 <;>
      simp [boolSignOn, dualTargetOn, h1, h2] <;> norm_num

/-- Masking off the pairs with equal value does not increase the spectral
norm: for a two-valued `f` the mask is an average of the identity and a `±1`
diagonal conjugation. -/
lemma l2_opNorm_hadamard_dualTargetOn_le (f : X → Bool)
    (M : Matrix X X ℝ) : ‖M ⊙ dualTargetOn f‖ ≤ ‖M‖ := by
  set s := boolSignOn f with hs
  have hsplit : M ⊙ dualTargetOn f
      = (2 : ℝ)⁻¹ • (M - Matrix.diagonal s * M * Matrix.diagonal s) := by
    ext x y
    have hmul : (Matrix.diagonal s * M * Matrix.diagonal s) x y
        = s x * M x y * s y := by
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hsxy : s x * s y = 1 - 2 * dualTargetOn f x y := boolSignOn_mul f x y
    rw [Matrix.hadamard_apply, Matrix.smul_apply, Matrix.sub_apply, hmul,
      smul_eq_mul]
    have : s x * M x y * s y = M x y * (s x * s y) := by ring
    rw [this, hsxy]
    ring
  rw [hsplit, norm_smul]
  have hconj : ‖Matrix.diagonal s * M * Matrix.diagonal s‖ = ‖M‖ :=
    l2_opNorm_conj_diagonal_sign (boolSignOn_eq_one_or f) M
  have := norm_sub_le M (Matrix.diagonal s * M * Matrix.diagonal s)
  rw [hconj] at this
  have h2 : ‖(2 : ℝ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  rw [h2]
  nlinarith [norm_nonneg M,
    norm_nonneg (M - Matrix.diagonal s * M * Matrix.diagonal s)]

end Mask

/-! ## The main construction -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq ι] [Fintype ι] [Fintype σ] in
/-- **From a dual certificate to a primal witness, on a promise domain.** -/
theorem lt_advPMOn_of_certificate {read : X → ι → σ} {f : X → Bool}
    (hdet : ∀ x y, read x = read y → f x = f y)
    {Γ : Matrix X X ℝ} {p : X → ℝ} {c : ℝ}
    (hsym : ∀ x y, Γ y x = Γ x y) (hp : ∀ x, 0 < p x)
    (hquad : ∀ (i : ι) (s t : X → ℝ),
      |s ⬝ᵥ (Γ ⊙ advDOn read i) *ᵥ t|
        ≤ (∑ x, p x * (s x * s x)) + ∑ y, p y * (t y * t y))
    (hobj : 2 * c * (∑ x, p x) < ∑ x, ∑ y, Γ x y * dualTargetOn f x y) :
    c < advPMOn read f := by
  classical
  have hsum : 0 < ∑ x, p x := by
    rcases isEmpty_or_nonempty X with he | hne
    · exact absurd hobj (by simp)
    · exact Finset.sum_pos (fun x _ => hp x) Finset.univ_nonempty
  set r : X → ℝ := fun x => Real.sqrt (p x) with hr
  have hr0 : ∀ x, 0 < r x := fun x => Real.sqrt_pos.mpr (hp x)
  have hrr : ∀ x, r x * r x = p x := fun x => Real.mul_self_sqrt (hp x).le
  set Γ' : Matrix X X ℝ := Matrix.of fun x y => Γ x y / (r x * r y) with hΓ'
  have hΓ'sym : ∀ x y, Γ' y x = Γ' x y := by
    intro x y
    change Γ y x / (r y * r x) = Γ x y / (r x * r y)
    rw [hsym x y, mul_comm (r y) (r x)]
  have hmask : ∀ (i : ι) (x y : X),
      (Γ' ⊙ advDOn read i) x y = (Γ ⊙ advDOn read i) x y / (r x * r y) := by
    intro i x y
    rw [hadamard_advDOn_apply, hadamard_advDOn_apply]
    by_cases h : read x i = read y i
    · simp [h]
    · simp [h, hΓ']
  have hnorm : ∀ i : ι, ‖Γ' ⊙ advDOn read i‖ ≤ 2 := by
    intro i
    refine l2_opNorm_le_two_of_quadratic _ fun a b => ?_
    have e1 : (fun x => a x / r x) ⬝ᵥ (Γ ⊙ advDOn read i) *ᵥ (fun y => b y / r y)
        = a ⬝ᵥ (Γ' ⊙ advDOn read i) *ᵥ b := by
      simp only [dotProduct_mulVec_eq_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [hmask i x y]
      have hx := (hr0 x).ne'
      have hy := (hr0 y).ne'
      field_simp
    have e2 : ∀ (w : X → ℝ),
        (∑ x, p x * ((w x / r x) * (w x / r x))) = w ⬝ᵥ w := by
      intro w
      rw [dotProduct]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hx := (hr0 x).ne'
      rw [← hrr x]
      field_simp
    have := hquad i (fun x => a x / r x) (fun y => b y / r y)
    rw [e1, e2 a, e2 b] at this
    exact this
  set Γ'' : Matrix X X ℝ := (2 : ℝ)⁻¹ • (Γ' ⊙ dualTargetOn f) with hΓ''
  have hadv : IsAdvMatrixOn f Γ'' := by
    constructor
    · ext x y
      change Γ'' y x = Γ'' x y
      simp only [hΓ'', Matrix.smul_apply, Matrix.hadamard_apply, smul_eq_mul,
        hΓ'sym x y, dualTargetOn_comm f x y]
    · intro x y hxy
      simp [hΓ'', Matrix.hadamard_apply, dualTargetOn, hxy]
  have hfeas : ∀ i : ι, ‖Γ'' ⊙ advDOn read i‖ ≤ 1 := by
    intro i
    have hswap : Γ'' ⊙ advDOn read i
        = (2 : ℝ)⁻¹ • ((Γ' ⊙ advDOn read i) ⊙ dualTargetOn f) := by
      ext x y
      simp only [hΓ'', Matrix.smul_apply, Matrix.hadamard_apply, smul_eq_mul]
      ring
    rw [hswap, norm_smul]
    have h1 : ‖(Γ' ⊙ advDOn read i) ⊙ dualTargetOn f‖ ≤ ‖Γ' ⊙ advDOn read i‖ :=
      l2_opNorm_hadamard_dualTargetOn_le f _
    have h2 : ‖(2 : ℝ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
    rw [h2]
    nlinarith [hnorm i, norm_nonneg ((Γ' ⊙ advDOn read i) ⊙ dualTargetOn f)]
  set R := Real.sqrt (∑ x, p x) with hR
  have hR0 : 0 < R := Real.sqrt_pos.mpr hsum
  have hRR : R * R = ∑ x, p x := Real.mul_self_sqrt hsum.le
  set a : X → ℝ := fun x => r x / R with ha
  have haa : a ⬝ᵥ a = 1 := by
    rw [dotProduct]
    have : ∀ x : X, a x * a x = p x / (R * R) := by
      intro x
      rw [ha]
      simp only []
      rw [div_mul_div_comm, hrr x]
    rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.sum_div, hRR,
      div_self hsum.ne']
  have hval : a ⬝ᵥ Γ'' *ᵥ a
      = (∑ x, ∑ y, Γ x y * dualTargetOn f x y) / (2 * ∑ x, p x) := by
    rw [dotProduct_mulVec_eq_sum, ← hRR]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hx := (hr0 x).ne'
    have hy := (hr0 y).ne'
    have hRne := hR0.ne'
    change (r x / R) * ((2 : ℝ)⁻¹ * (Γ x y / (r x * r y) * dualTargetOn f x y)) *
        (r y / R) = _
    field_simp
  have hlt : c < a ⬝ᵥ Γ'' *ᵥ a := by
    rw [hval, lt_div_iff₀ (by positivity)]
    linarith [hobj]
  have hbound : a ⬝ᵥ Γ'' *ᵥ a ≤ ‖Γ''‖ := by
    have := abs_dotProduct_mulVec_le Γ'' a a
    rw [haa, Real.sqrt_one] at this
    simpa using (le_abs_self _).trans this
  exact lt_of_lt_of_le hlt (hbound.trans (le_advPMOn hdet hadv hfeas))

end QuantumQueryComplexity

end SourceDualityWitnessOn

section TotalDualitySpecialization

/-! ## Total-input specializations of the promise witness construction -/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-- A Boolean output mask is contractive in the operator norm. -/
lemma l2_opNorm_hadamard_dualTarget_le (g : (ι → σ) → Bool)
    (M : Matrix (ι → σ) (ι → σ) ℝ) : ‖M ⊙ dualTarget g‖ ≤ ‖M‖ := by
  exact l2_opNorm_hadamard_dualTargetOn_le g M

/-- The total-input certificate construction is the identity-read promise case. -/
theorem lt_advPM_of_certificate {g : (ι → σ) → Bool}
    {Γ : Matrix (ι → σ) (ι → σ) ℝ} {p : (ι → σ) → ℝ} {c : ℝ}
    (hsym : ∀ x y, Γ y x = Γ x y) (hp : ∀ x, 0 < p x)
    (hquad : ∀ (i : ι) (s t : (ι → σ) → ℝ),
      |s ⬝ᵥ (Γ ⊙ advD i) *ᵥ t|
        ≤ (∑ x, p x * (s x * s x)) + ∑ y, p y * (t y * t y))
    (hobj : 2 * c * (∑ x, p x) < ∑ x, ∑ y, Γ x y * dualTarget g x y) :
    c < advPM g := by
  exact lt_advPMOn_of_certificate (read := id) (f := g)
    (fun _ _ h => congrArg g h) hsym hp hquad hobj


end QuantumQueryComplexity

end TotalDualitySpecialization

section SourceCompositionMask

/-!
# The Hadamard-mask identity (HLŠ p. 20 / BL Eq. (8) + Claim 23)

Masking the composed matrix by a difference matrix produces another composed
matrix: the outer matrix is masked by `advD p` and the inner matrix in slot `p`
is masked by the inner difference matrix at `q`:

  `composeE e g Γf M ⊙ advDOn (composeReadE e innerRead) (p, q)
     = composeE e g (Γf ⊙ advD p)
         (Function.update M p (M p ⊙ advDOn innerRead q))`

This is an exact entrywise identity: in every configuration where the
`‖·‖ • 1` part of a hat matrix could differ between the two sides, either the
outer factor `(Γf ⊙ advD p)` or a Kronecker delta vanishes first.

## The mask is a promise mask

The composed inputs form an arbitrary finite type `Z ≃ (α → Y)`, and a query
`(p, q)` reads coordinate `q` of the `p`-th block *through the inner
observation map* `innerRead : Y → β → σ` (`composeReadE`).  So the relevant
difference matrix is `advDOn`, evaluated on the inner observations.

Neither delicate step needs `innerRead` to be injective.  In the "queries
agree" branch the `p`-slot hat entry vanishes because the masked inner entry
vanishes *and* the two blocks have different `g`-values, hence are distinct
blocks; in the "queries differ" branch the blocks are distinct because a single
`congrArg` turns differing reads into differing blocks.

The original cube statement `compose_hadamard_advD` is recovered as the
instance `e := cubeBlocks α β` with `innerRead` the identity, since
`advDOn (fun u => u) q` is `advD q` definitionally.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

lemma IsAdvMatrix.hadamard_advD {ι : Type*}
    {f : (ι → Bool) → Bool} {Γ : Matrix (ι → Bool) (ι → Bool) ℝ}
    (h : IsAdvMatrix f Γ) (i : ι) : IsAdvMatrix f (Γ ⊙ advD i) := by
  classical
  exact ⟨h.isHermitian.hadamard (advD_isHermitian i), fun x y hxy => by
      rw [Matrix.hadamard_apply, h.apply_eq_zero hxy, zero_mul]⟩

/-! ## The mask identity over an abstract block decomposition -/

section General

variable {α β σ Y Z : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [DecidableEq σ] [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

omit [DecidableEq Y] [DecidableEq β] [Fintype Y] [Fintype β] in
lemma IsAdvCol.hadamard_advDOn {g : Y → Bool} {N : Matrix Y Y ℝ}
    (h : IsAdvCol g N) (innerRead : Y → β → σ) (q : β) :
    IsAdvCol g (N ⊙ advDOn innerRead q) := by
  classical
  exact ⟨h.isHermitian.hadamard (advDOn_isHermitian innerRead q), fun u v huv => by
      rw [Matrix.hadamard_apply, h.apply_eq_zero huv, zero_mul]⟩

/-- The observation map of a composed input: the query `(p, q)` reads
coordinate `q` of the `p`-th block, through the inner observation map. -/
def composeReadE (e : Z ≃ (α → Y)) (innerRead : Y → β → σ) :
    Z → (α × β) → σ :=
  fun z pq => innerRead (sliceE e z pq.1) pq.2

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq α] [DecidableEq β] [DecidableEq σ]
    [Fintype Y] [Fintype Z] [Fintype α] [Fintype β] in
@[simp] lemma composeReadE_apply (e : Z ≃ (α → Y)) (innerRead : Y → β → σ)
    (z : Z) (pq : α × β) :
    composeReadE e innerRead z pq = innerRead (sliceE e z pq.1) pq.2 := by
  classical
  exact rfl

omit [DecidableEq Z] [DecidableEq β] [Fintype Z] [Fintype β] in
/-- The mask identity. -/
theorem composeE_hadamard_advDOn (e : Z ≃ (α → Y)) (innerRead : Y → β → σ)
    (g : α → Y → Bool) (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    (M : α → Matrix Y Y ℝ) (hM : ∀ i, IsAdvCol (g i) (M i)) (p : α) (q : β) :
    composeE e g Γf M ⊙ advDOn (composeReadE e innerRead) (p, q)
      = composeE e g (Γf ⊙ advD p)
          (Function.update M p (M p ⊙ advDOn innerRead q)) := by
  classical
  ext x y
  rw [Matrix.hadamard_apply, composeE_apply, composeE_apply, advDOn_apply,
    composeReadE_apply, composeReadE_apply]
  by_cases hpq : innerRead (sliceE e x p) q = innerRead (sliceE e y p) q
  · rw [ite_eq_left hpq, mul_zero]
    by_cases hcol : g p (sliceE e x p) = g p (sliceE e y p)
    · rw [hadamard_advD_apply,
        ite_eq_left (show tildeE e g x p = tildeE e g y p from hcol), zero_mul]
    · have hhat : hat (Function.update M p (M p ⊙ advDOn innerRead q) p)
          (sliceE e x p) (sliceE e y p) = 0 := by
        rw [Function.update_self, hat_apply, hadamard_advDOn_apply,
          ite_eq_left hpq,
          ite_eq_right (show ¬sliceE e x p = sliceE e y p from fun hc =>
            hcol (by rw [hc]))]
        ring
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), hhat, zero_mul,
        mul_zero]
  · rw [ite_eq_right hpq, mul_one]
    have hslice_ne : sliceE e x p ≠ sliceE e y p := fun hc => hpq (by rw [hc])
    by_cases hcol : g p (sliceE e x p) = g p (sliceE e y p)
    · rw [hadamard_advD_apply,
        ite_eq_left (show tildeE e g x p = tildeE e g y p from hcol), zero_mul]
      have hhat : hat (M p) (sliceE e x p) (sliceE e y p) = 0 := by
        rw [hat_apply, (hM p).apply_eq_zero hcol, ite_eq_right hslice_ne]
        ring
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), hhat, zero_mul,
        mul_zero]
    · rw [hadamard_advD_apply,
        ite_eq_right (show ¬tildeE e g x p = tildeE e g y p from hcol),
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ p),
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
      have hp_eq : hat (Function.update M p (M p ⊙ advDOn innerRead q) p)
          (sliceE e x p) (sliceE e y p)
          = hat (M p) (sliceE e x p) (sliceE e y p) := by
        rw [Function.update_self, hat_apply, hat_apply, hadamard_advDOn_apply,
          ite_eq_right hpq, ite_eq_right hslice_ne]
        ring
      have hP : ∏ i ∈ Finset.univ.erase p,
          hat (Function.update M p (M p ⊙ advDOn innerRead q) i)
            (sliceE e x i) (sliceE e y i)
          = ∏ i ∈ Finset.univ.erase p,
              hat (M i) (sliceE e x i) (sliceE e y i) :=
        Finset.prod_congr rfl fun i hi => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [hp_eq, hP]

end General

/-! ## The cube instance -/

section Cube

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The mask identity, cube form. -/
theorem compose_hadamard_advD (g : α → (β → Bool) → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    (M : α → Matrix (β → Bool) (β → Bool) ℝ)
    (hM : ∀ i, IsAdvMatrix (g i) (M i)) (p : α) (q : β) :
    compose g Γf M ⊙ advD (p, q)
      = compose g (Γf ⊙ advD p) (Function.update M p (M p ⊙ advD q)) :=
  composeE_hadamard_advDOn (cubeBlocks α β) (fun u => u) g Γf M
    (fun i => (hM i).isAdvCol) p q

end Cube

end QuantumQueryComplexity

end SourceCompositionMask

section SourceDualityMainOn

/-!
# Strong duality for the adversary bound, on a promise domain

The promise mirror of `SourceDualityMain`: for a **read-determined Boolean**
promise problem, every value above `advPMOn read f` is achieved by a feasible
`DualPairOn`:

    exists_dualPairOn_of_advPMOn_lt :
      advPMOn read f < c → ∃ m (P : DualPairOn read (Fin m) f), P.IsCostLe c.

The argument is the same single Hahn–Banach separation, run in the coordinate
space `DualOmegaOn X → ℝ` with the truncation `T = 2c·|X|`.  Determinacy
(`hdet`) is a genuine hypothesis here: an undetermined pair
(`read x = read y`, `f x ≠ f y`) makes the dual program infeasible while the
primal supremum degenerates.  In the proof it enters through `le_advPMOn`,
and in the no-query case (`ι` empty), where it forces `f` constant so the
zero dual is feasible; the `X = ∅` case is vacuous and does not use it.
The `±1` masking trick
needs the *output* to be two-valued, which is the `f : X → Bool` hypothesis —
exactly the scope the Boolean characterization needs.

Combined with the promise-native lower bound  and extraction
(`SourceQuantumUpperBound`), this yields the **promise-Boolean characterization**; see
`SourceQuantumCharacterization`.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Rank-one test matrices concentrated on one query position -/

/-- The vector of Gram indices carrying `s` on the `u`-side and `t` on the
`v`-side of the query position `i₀`, and zero elsewhere. -/
def concVecOn (i₀ : ι) (s t : X → ℝ) : GramIdxOn X ι → ℝ :=
  fun z => if z.2.1 = i₀ then (if z.2.2 then t z.1 else s z.1) else 0

omit [DecidableEq X] [Fintype X] [Fintype σ] in
lemma gramROn_concVecOn (read : X → ι → σ) (i₀ : ι) (s t : X → ℝ) (x y : X) :
    gramROn read (vecMulVec (concVecOn i₀ s t) (concVecOn i₀ s t)) x y
      = if read x i₀ = read y i₀ then 0 else s x * t y := by
  classical
  rw [gramROn_vecMulVec, Finset.sum_eq_single i₀]
  · by_cases h : read x i₀ = read y i₀ <;> simp [h, concVecOn]
  · intro i _ hi
    by_cases h : read x i = read y i <;> simp [h, concVecOn, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

omit [DecidableEq X] [Fintype X] in
lemma gramCostOn_concVecOn_false (i₀ : ι) (s t : X → ℝ) (x : X) :
    gramCostOn (vecMulVec (concVecOn i₀ s t) (concVecOn i₀ s t)) false x
      = s x * s x := by
  classical
  rw [gramCostOn_vecMulVec, Finset.sum_eq_single i₀]
  · simp [concVecOn]
  · intro i _ hi
    simp [concVecOn, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

omit [DecidableEq X] [Fintype X] in
lemma gramCostOn_concVecOn_true (i₀ : ι) (s t : X → ℝ) (x : X) :
    gramCostOn (vecMulVec (concVecOn i₀ s t) (concVecOn i₀ s t)) true x
      = t x * t x := by
  classical
  rw [gramCostOn_vecMulVec, Finset.sum_eq_single i₀]
  · simp [concVecOn]
  · intro i _ hi
    simp [concVecOn, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

omit [DecidableEq X] in
lemma sum_sq_concVecOn (i₀ : ι) (s t : X → ℝ) :
    (∑ z, concVecOn i₀ s t z * concVecOn i₀ s t z)
      = (∑ x, s x * s x) + ∑ x, t x * t x := by
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i₀]
  · simp [concVecOn]
    ring
  · intro i _ hi
    simp [concVecOn, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

omit [DecidableEq X] [Fintype X] [Fintype ι] in
lemma concVecOn_ne_zero_left {i₀ : ι} {s t : X → ℝ} (hs : s ≠ 0) :
    concVecOn i₀ s t ≠ 0 := by
  intro h
  refine hs (funext fun x => ?_)
  have := congrFun h (x, i₀, false)
  simpa [concVecOn] using this

omit [DecidableEq X] [Fintype X] [Fintype ι] in
lemma concVecOn_ne_zero_right {i₀ : ι} {s t : X → ℝ} (ht : t ≠ 0) :
    concVecOn i₀ s t ≠ 0 := by
  intro h
  refine ht (funext fun x => ?_)
  have := congrFun h (x, i₀, true)
  simpa [concVecOn] using this

/-! ## Symmetrising a two-weight certificate -/

omit [DecidableEq ι] [Fintype ι] [Fintype σ] in
/-- The certificate with the two sides carrying different weights: averaging
reduces to the symmetric case, because `advDOn read i` and `dualTargetOn f`
are symmetric. -/
theorem lt_advPMOn_of_certificate_two {read : X → ι → σ} {f : X → Bool}
    (hdet : ∀ x y, read x = read y → f x = f y)
    {Ξ : Matrix X X ℝ} {p q : X → ℝ} {c : ℝ}
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hquad : ∀ (i : ι) (s t : X → ℝ),
      |s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t|
        ≤ (∑ x, p x * (s x * s x)) + ∑ y, q y * (t y * t y))
    (hobj : c * ((∑ x, p x) + ∑ x, q x)
      < ∑ x, ∑ y, Ξ x y * dualTargetOn f x y) :
    c < advPMOn read f := by
  classical
  set Ξ' : Matrix X X ℝ := Matrix.of fun x y => (Ξ x y + Ξ y x) / 2 with hΞ'
  set p' : X → ℝ := fun x => (p x + q x) / 2 with hp'
  have hD : ∀ (i : ι) (x y : X),
      (advDOn read i) y x = advDOn read i x y := by
    intro i x y
    simp [advDOn, eq_comm]
  have hswap : ∀ (i : ι) (s t : X → ℝ),
      s ⬝ᵥ (Ξ' ⊙ advDOn read i) *ᵥ t
        = (s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t) / 2
          + (t ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ s) / 2 := by
    intro i s t
    simp only [dotProduct_mulVec_eq_sum]
    have hcomm : (∑ x, ∑ y, t x * (Ξ ⊙ advDOn read i) x y * s y)
        = ∑ x, ∑ y, s x * ((Ξ ⊙ advDOn read i) y x) * t y := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ =>
        Finset.sum_congr rfl fun y _ => by ring
    rw [hcomm, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Matrix.hadamard_apply, hΞ', Matrix.of_apply, hD i x y]
    ring
  have hps : ∀ w : X → ℝ, (∑ x, p' x * (w x * w x))
      = (∑ x, p x * (w x * w x)) / 2 + (∑ x, q x * (w x * w x)) / 2 := by
    intro w
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hp']
    ring
  refine lt_advPMOn_of_certificate hdet (Γ := Ξ') (p := p') ?_ ?_ ?_ ?_
  · intro x y
    change (Ξ y x + Ξ x y) / 2 = (Ξ x y + Ξ y x) / 2
    ring
  · intro x
    have h1 := hp x
    have h2 := hq x
    simp only [hp']
    linarith
  · intro i s t
    rw [hswap i s t, hps s, hps t]
    have h1 := hquad i s t
    have h2 := hquad i t s
    have habs : |(s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t) / 2
          + (t ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ s) / 2|
        ≤ |s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t| / 2
          + |t ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ s| / 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_div]
      norm_num
    linarith
  · have hS : (∑ x, ∑ y, Ξ y x * dualTargetOn f x y)
        = ∑ x, ∑ y, Ξ x y * dualTargetOn f x y := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
        rw [dualTargetOn_comm]
    have hpair : (∑ x, ∑ y, Ξ' x y * dualTargetOn f x y)
        = ∑ x, ∑ y, Ξ x y * dualTargetOn f x y := by
      have hsplit : (∑ x, ∑ y, Ξ' x y * dualTargetOn f x y)
          = (∑ x, ∑ y, Ξ x y * dualTargetOn f x y) / 2
            + (∑ x, ∑ y, Ξ y x * dualTargetOn f x y) / 2 := by
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        simp only [hΞ', Matrix.of_apply]
        ring
      rw [hsplit, hS]
      ring
    rw [hpair]
    have hsum' : (∑ x, p' x) = ((∑ x, p x) + ∑ x, q x) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
    have hsump : 2 * c * (∑ x, p' x) = c * ((∑ x, p x) + ∑ x, q x) := by
      rw [hsum']
      ring
    rw [hsump]
    exact hobj

/-! ## The separation argument -/

omit [DecidableEq ι] [Fintype σ] in
/-- **Promise strong duality, existence form.**  For a read-determined
Boolean promise problem, every value above the promise adversary bound is
achieved by a feasible promise dual solution. -/
theorem exists_dualPairOn_of_advPMOn_lt {read : X → ι → σ} {f : X → Bool}
    (hdet : ∀ x y, read x = read y → f x = f y) {c : ℝ}
    (hc : advPMOn read f < c) :
    ∃ (m : ℕ) (P : DualPairOn read (Fin m) f), P.IsCostLe c := by
  classical
  have hc0 : 0 < c := lt_of_le_of_lt (advPMOn_nonneg hdet) hc
  by_contra hno
  push Not at hno
  -- with an empty promise domain the zero dual is vacuously feasible
  rcases isEmpty_or_nonempty X with hXe | hXn
  · exact hno 0 ⟨fun x _ _ => (hXe.false x).elim, fun x _ _ => (hXe.false x).elim,
      fun x _ => (hXe.false x).elim⟩
      ⟨fun x => (hXe.false x).elim, fun x => (hXe.false x).elim⟩
  -- with no query positions determinacy makes every pair equal-valued
  rcases isEmpty_or_nonempty ι with hιe | hιn
  · have hval : ∀ x y : X, f x = f y := fun x y =>
      hdet x y (funext fun i => (hιe.false i).elim)
    refine hno 0 ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun x y => ?_⟩
      ⟨fun x => ?_, fun x => ?_⟩
    · simp [hval x y]
    · simpa using hc0.le
    · simpa using hc0.le
  obtain ⟨i₀⟩ := hιn
  have hcard : 0 < (Fintype.card X : ℝ) := by
    have h : 0 < Fintype.card X := Fintype.card_pos
    exact_mod_cast h
  set T : ℝ := 2 * c * (Fintype.card X : ℝ) with hTdef
  have hT0 : 0 < T := by positivity
  -- the two sets are disjoint
  have hdisj : Disjoint (gramImageOn read T) (dualBoxOn f c) := by
    rw [Set.disjoint_left]
    rintro z ⟨G, ⟨hGpsd, _⟩, rfl⟩ ⟨hz1, hz2⟩
    have hR : gramROn read G = dualTargetOn f := by
      ext x y
      exact hz1 x y
    obtain ⟨m, Q, hQ⟩ := exists_dualPairOn_of_gram hGpsd hR
      fun b x => (hz2 (x, b)).2
    exact hno m Q hQ
  obtain ⟨φ, u, v, hgram, huv, hbox⟩ :=
    geometric_hahn_banach_compact_closed (convex_gramImageOn read T)
      (isCompact_gramImageOn read T)
      (convex_dualBoxOn f c) (isClosed_dualBoxOn f c) hdisj
  have hu0 : 0 < u := by
    have h := hgram 0 (zero_mem_gramImageOn hT0.le)
    simpa using h
  set κ : ℝ := u / T with hκdef
  have hκ0 : 0 < κ := div_pos hu0 hT0
  have hkappa : T * κ = u := by
    rw [hκdef]
    field_simp
  -- the coefficients of the separating functional
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : Matrix X X ℝ,
      ∀ x y, Ξ x y = φ (Pi.single (Sum.inl (x, y)) 1) :=
    ⟨Matrix.of fun x y => φ (Pi.single (Sum.inl (x, y)) 1), fun _ _ => rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Bool → X → ℝ,
      ∀ b x, γ b x = φ (Pi.single (Sum.inr (x, b)) 1) :=
    ⟨fun b x => φ (Pi.single (Sum.inr (x, b)) 1), fun _ _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Bool → X → ℝ, ∀ b x, P b x = κ - γ b x :=
    ⟨fun b x => κ - γ b x, fun _ _ => rfl⟩
  -- reading `φ` off a Gram matrix
  have hexpand : ∀ G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ,
      φ (gramLOn read G) = (∑ x, ∑ y, gramROn read G x y * Ξ x y)
        + ∑ x, ∑ b, gramCostOn G b x * γ b x := by
    intro G
    rw [apply_eq_sum_single]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, gramLOn_inl,
      gramLOn_inr, hΞ, hγ]
  have hQbound : ∀ w : GramIdxOn X ι → ℝ, w ≠ 0 →
      φ (gramLOn read (vecMulVec w w)) < κ * ∑ z, w z * w z :=
    rankOne_lt_of_trace_bound (φ.toLinearMap.comp (gramLOnₗ read)) hT0
      (fun w hw => hgram _ (mem_gramImageOn_vecMulVec (read := read) w hw))
  have hQle : ∀ w : GramIdxOn X ι → ℝ,
      φ (gramLOn read (vecMulVec w w)) ≤ κ * ∑ z, w z * w z := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · change (φ.toLinearMap.comp (gramLOnₗ read)) (vecMulVec (0 : GramIdxOn X ι → ℝ) 0) ≤ _
      rw [zero_vecMulVec, map_zero]
      simp
    · exact (hQbound w hw).le
  -- the value of `φ` on a rank-one matrix concentrated at one position
  have hconc : ∀ (i : ι) (s t : X → ℝ),
      φ (gramLOn read (vecMulVec (concVecOn i s t) (concVecOn i s t)))
        = s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t + ((∑ x, γ false x * (s x * s x))
          + ∑ x, γ true x * (t x * t x)) := by
    intro i s t
    rw [hexpand]
    have e1 : (∑ x, ∑ y,
          gramROn read (vecMulVec (concVecOn i s t) (concVecOn i s t)) x y
            * Ξ x y)
        = s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t := by
      rw [dotProduct_mulVec_eq_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [gramROn_concVecOn, hadamard_advDOn_apply]
      by_cases h : read x i = read y i <;> simp [h]; ring
    have e2 : (∑ x, ∑ b,
          gramCostOn (vecMulVec (concVecOn i s t) (concVecOn i s t)) b x
            * γ b x)
        = (∑ x, γ false x * (s x * s x)) + ∑ x, γ true x * (t x * t x) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Fintype.sum_bool, gramCostOn_concVecOn_false, gramCostOn_concVecOn_true]
      ring
    rw [e1, e2]
  have hPsum : ∀ (b : Bool) (w : X → ℝ),
      (∑ x, P b x * (w x * w x))
        = κ * (∑ x, w x * w x) - ∑ x, γ b x * (w x * w x) := by
    intro b w
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [hP]; ring
  -- the quadratic hypothesis of the certificate
  have hquadle : ∀ (i : ι) (s t : X → ℝ),
      s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t
        ≤ (∑ x, P false x * (s x * s x)) + ∑ x, P true x * (t x * t x) := by
    intro i s t
    have h := hQle (concVecOn i s t)
    rw [hconc i s t, sum_sq_concVecOn] at h
    rw [hPsum false s, hPsum true t]
    have hexp : κ * ((∑ x, s x * s x) + ∑ x, t x * t x)
        = κ * (∑ x, s x * s x) + κ * (∑ x, t x * t x) := by ring
    rw [hexp] at h
    linarith
  have hquadabs : ∀ (i : ι) (s t : X → ℝ),
      |s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t|
        ≤ (∑ x, P false x * (s x * s x)) + ∑ x, P true x * (t x * t x) := by
    intro i s t
    have h1 := hquadle i s t
    have h2 := hquadle i (fun x => -s x) t
    have hneg : (fun x => -s x) ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t
        = -(s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t) := by
      simp only [dotProduct_mulVec_eq_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      exact Finset.sum_congr rfl fun y _ => by ring
    have hsq : (∑ x, P false x * ((-s x) * (-s x)))
        = ∑ x, P false x * (s x * s x) :=
      Finset.sum_congr rfl fun x _ => by ring
    rw [hneg, hsq] at h2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- the weights are strictly positive
  have hsingle_ne : ∀ x : X, (Pi.single x (1 : ℝ) : X → ℝ) ≠ 0 := by
    intro x h
    have := congrFun h x
    simp at this
  have hPpos : ∀ (b : Bool) (x : X), 0 < P b x := by
    intro b x
    cases b with
    | false =>
        have h := hQbound (concVecOn i₀ (Pi.single x 1) 0)
          (concVecOn_ne_zero_left (hsingle_ne x))
        rw [hconc, sum_sq_concVecOn, sum_sq_single, sum_weight_sq_single] at h
        have hz : (Pi.single x (1 : ℝ) : X → ℝ) ⬝ᵥ (Ξ ⊙ advDOn read i₀)
            *ᵥ (0 : X → ℝ) = 0 := by simp
        simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
          hz, zero_add] at h
        rw [hP]
        linarith
    | true =>
        have h := hQbound (concVecOn i₀ 0 (Pi.single x 1))
          (concVecOn_ne_zero_right (hsingle_ne x))
        rw [hconc, sum_sq_concVecOn, sum_sq_single, sum_weight_sq_single] at h
        have hz : (0 : X → ℝ) ⬝ᵥ (Ξ ⊙ advDOn read i₀)
            *ᵥ (Pi.single x (1 : ℝ) : X → ℝ) = 0 := by simp
        simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add,
          hz] at h
        rw [hP]
        linarith
  -- the objective hypothesis of the certificate
  have hcorner := hbox _ (dualCornerOn_mem (f := f) hc0.le)
  have hcornerval : φ (dualCornerOn f c)
      = (∑ x, ∑ y, dualTargetOn f x y * Ξ x y) + ∑ x, ∑ b, c * γ b x := by
    rw [apply_eq_sum_single]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, dualCornerOn,
      Sum.elim_inl, Sum.elim_inr, hΞ, hγ]
  have hsumP : ∀ b : Bool, (∑ x, P b x)
      = κ * (Fintype.card X : ℝ) - ∑ x, γ b x := by
    intro b
    have : (∑ x, P b x) = ∑ x, (κ - γ b x) :=
      Finset.sum_congr rfl fun x _ => hP b x
    rw [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  have hcomm : (∑ x, ∑ y, dualTargetOn f x y * Ξ x y)
      = ∑ x, ∑ y, Ξ x y * dualTargetOn f x y :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => mul_comm _ _
  have hgamma : (∑ x, ∑ b, c * γ b x)
      = c * ((∑ x, γ false x) + ∑ x, γ true x) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [Fintype.sum_bool]; ring
  rw [hcornerval, hcomm, hgamma] at hcorner
  have hobj : c * ((∑ x, P false x) + ∑ x, P true x)
      < ∑ x, ∑ y, Ξ x y * dualTargetOn f x y := by
    rw [hsumP false, hsumP true]
    have hLHS : c * ((κ * (Fintype.card X : ℝ) - ∑ x, γ false x)
          + (κ * (Fintype.card X : ℝ) - ∑ x, γ true x))
        = u - c * ((∑ x, γ false x) + ∑ x, γ true x) := by
      rw [← hkappa, hTdef]
      ring
    rw [hLHS]
    linarith
  exact absurd
    (lt_advPMOn_of_certificate_two hdet (hPpos false) (hPpos true) hquadabs hobj)
    (not_lt.mpr hc.le)

/-! ## A nonconstant promise problem has `advPMOn ≥ 1/2`

The crude entrywise bound `‖M‖ ≤ ∑|M|` on the elementary pair matrix loses a
factor of two against the total case's exact `norm_pairMatrix`, which is all
the characterization's constant bookkeeping needs. -/

section Nonconstant

variable {O : Type*} [DecidableEq O]

/-- The elementary promise adversary matrix supported on one symmetric pair. -/
def pairMatrixOn (x y : X) : Matrix X X ℝ :=
  Matrix.single x y 1 + Matrix.single y x 1

omit [Fintype X] in
lemma pairMatrixOn_isHermitian (x y : X) : (pairMatrixOn x y).IsHermitian := by
  change (pairMatrixOn x y)ᴴ = pairMatrixOn x y
  ext a b
  simp only [Matrix.conjTranspose_apply, pairMatrixOn, Matrix.add_apply,
    Matrix.single_apply, star_trivial]
  rw [add_comm]
  congr 1
  · exact if_congr (by tauto) rfl rfl
  · exact if_congr (by tauto) rfl rfl

omit [Fintype X] in
lemma pairMatrixOn_apply_self {x y : X} (hxy : x ≠ y) :
    pairMatrixOn x y x y = 1 := by
  simp [pairMatrixOn, Ne.symm hxy]

lemma sum_abs_pairMatrixOn {x y : X} (hxy : x ≠ y) :
    (∑ a, ∑ b, |pairMatrixOn x y a b|) = 2 := by
  have hentry : ∀ a b, |pairMatrixOn x y a b|
      = (if x = a ∧ y = b then (1 : ℝ) else 0)
        + (if y = a ∧ x = b then (1 : ℝ) else 0) := by
    intro a b
    rw [pairMatrixOn, Matrix.add_apply, Matrix.single_apply,
      Matrix.single_apply]
    by_cases h1 : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := h1
      simp [hxy, Ne.symm hxy]
    · by_cases h2 : y = a ∧ x = b
      · obtain ⟨rfl, rfl⟩ := h2
        simp [hxy, Ne.symm hxy]
      · simp [h1, h2]
  have hone : ∀ (x' y' : X), (∑ a, ∑ b,
      (if x' = a ∧ y' = b then (1 : ℝ) else 0)) = 1 := by
    intro x' y'
    rw [Finset.sum_eq_single x']
    · rw [Finset.sum_eq_single y']
      · simp
      · intro b _ hb
        exact ite_eq_right fun hcon => hb hcon.2.symm
      · intro h
        exact absurd (Finset.mem_univ y') h
    · intro a _ ha
      exact Finset.sum_eq_zero fun b _ => ite_eq_right fun hcon => ha hcon.1.symm
    · intro h
      exact absurd (Finset.mem_univ x') h
  calc (∑ a, ∑ b, |pairMatrixOn x y a b|)
      = (∑ a, ∑ b, ((if x = a ∧ y = b then (1 : ℝ) else 0)
          + (if y = a ∧ x = b then (1 : ℝ) else 0))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          hentry a b
    _ = (∑ a, ∑ b, (if x = a ∧ y = b then (1 : ℝ) else 0))
          + ∑ a, ∑ b, (if y = a ∧ x = b then (1 : ℝ) else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_add_distrib
    _ = 2 := by rw [hone x y, hone y x]; norm_num

omit [DecidableEq O] [DecidableEq ι] [Fintype ι] [Fintype σ] in
/-- **A nonconstant promise problem has `advPMOn ≥ 1/2`**: half the
elementary pair matrix is feasible. -/
theorem half_le_advPMOn {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) {x y : X}
    (hf : f x ≠ f y) : (1 / 2 : ℝ) ≤ advPMOn read f := by
  classical
  have hxy : x ≠ y := fun h => hf (by rw [h])
  have hpair : IsAdvMatrixOn f (pairMatrixOn x y) := by
    refine ⟨pairMatrixOn_isHermitian x y, ?_⟩
    intro a b hab
    by_cases h1 : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := h1
      exact absurd hab hf
    · by_cases h2 : y = a ∧ x = b
      · obtain ⟨rfl, rfl⟩ := h2
        exact absurd hab.symm hf
      · simp [pairMatrixOn, h1, h2]
  have hadv : IsAdvMatrixOn f ((2⁻¹ : ℝ) • pairMatrixOn x y) :=
    hpair.smul (2⁻¹ : ℝ)
  have hfeas : ∀ i, ‖((2⁻¹ : ℝ) • pairMatrixOn x y) ⊙ advDOn read i‖ ≤ 1 := by
    intro i
    have hsmul : ((2⁻¹ : ℝ) • pairMatrixOn x y) ⊙ advDOn read i
        = (2⁻¹ : ℝ) • (pairMatrixOn x y ⊙ advDOn read i) := by
      ext a b
      simp only [Matrix.smul_apply, Matrix.hadamard_apply, smul_eq_mul]
      ring
    have hmasked : ‖pairMatrixOn x y ⊙ advDOn read i‖ ≤ 2 := by
      refine (l2_opNorm_le_sum_abs _).trans ?_
      rw [← sum_abs_pairMatrixOn hxy]
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
      rw [hadamard_advDOn_apply]
      by_cases h : read a i = read b i <;> simp [h]
    rw [hsmul, norm_smul]
    have h2 : ‖(2⁻¹ : ℝ)‖ = (2⁻¹ : ℝ) := by norm_num
    rw [h2]
    nlinarith [hmasked, norm_nonneg (pairMatrixOn x y ⊙ advDOn read i)]
  have hle := le_advPMOn hdet hadv hfeas
  have hentry := abs_entry_le_l2_opNorm ((2⁻¹ : ℝ) • pairMatrixOn x y) x y
  rw [Matrix.smul_apply, pairMatrixOn_apply_self hxy, smul_eq_mul,
    mul_one] at hentry
  have habs : |(2⁻¹ : ℝ)| = (2⁻¹ : ℝ) := by norm_num
  rw [habs] at hentry
  linarith

end Nonconstant

end QuantumQueryComplexity

end SourceDualityMainOn

section SourceCompositionMain

/-!
# The composition theorem for the negative-weight adversary bound

**Main result** (`advPM_mul_le_advPM_composeFun`): for total Boolean functions
`f : (α → Bool) → Bool` and `g : (β → Bool) → Bool`,

  `ADV±(f) * ADV±(g) ≤ ADV±(f ∘ gᵏ)`

— the composition lower bound of Høyer–Lee–Špalek (quant-ph/0611054,
Theorem 13, uniform unit-cost case) in the formulation of Belovs–Lee
(arXiv:2004.06439, Theorem 1, `≥` direction).  The iterated corollary
`advPM_pow_le_advPM_iterFun` gives `ADV±(f)^(d+1) ≤ ADV±(f^{∘(d+1)})`.

Proof: for feasible witnesses `Γf, Γg`, the composed matrix
`Γh = compose (constFam g) Γf (fun _ => Γg)` is an adversary matrix for `f ∘ gᵏ` with
`‖Γh‖ ≥ ‖Γf‖ ‖Γg‖^k` (Lemma 16, `≥`) and
`‖Γh ⊙ advD (p,q)‖ ≤ ‖Γg‖^(k-1)` (mask identity + Lemma 16, `≤`), so the
un-normalized witness lemma yields `advPM (f ∘ gᵏ) ≥ ‖Γf‖ ‖Γg‖`; two
supremum passes finish the proof.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The composed function `f ∘ gᵏ` on inputs indexed by `α × β`. -/
def composeFunFam (f : (α → Bool) → Bool) (g : α → (β → Bool) → Bool) :
    ((α × β) → Bool) → Bool :=
  fun x => f (tilde g x)

/-- The composed function `f ∘ gᵏ` on inputs indexed by `α × β`. -/
def composeFun (f : (α → Bool) → Bool) (g : (β → Bool) → Bool) :
    ((α × β) → Bool) → Bool :=
  composeFunFam f (constFam g)

omit [DecidableEq α] in
lemma isAdvMatrix_compose {f : (α → Bool) → Bool}
    {g : α → (β → Bool) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (β → Bool) (β → Bool) ℝ}
    (hf : IsAdvMatrix f Γf) (hM : ∀ i, IsAdvMatrix (g i) (M i)) :
    IsAdvMatrix (composeFunFam f g) (compose g Γf M) := by
  classical
  refine ⟨compose_isHermitian g hf.isHermitian fun i => (hM i).isHermitian, ?_⟩
  intro x y hxy
  rw [compose_apply, hf.apply_eq_zero hxy, zero_mul]

/-- The masked norm bound for the composed witness (T1). -/
lemma norm_compose_mask {g : (β → Bool) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {Γg : Matrix (β → Bool) (β → Bool) ℝ}
    (hf : Γf.IsHermitian) (hg : IsAdvMatrix g Γg) (p : α) (q : β) :
    ‖compose (constFam g) Γf (fun _ => Γg) ⊙ advD (p, q)‖
      ≤ ‖Γf ⊙ advD p‖ *
        (‖Γg ⊙ advD q‖ * ‖Γg‖ ^ (Fintype.card α - 1)) := by
  rw [compose_hadamard_advD (constFam g) Γf (fun _ => Γg) (fun _ => hg) p q]
  have hshape : ∀ i, IsAdvMatrix (constFam g i)
      (Function.update (fun _ : α => Γg) p (Γg ⊙ advD q) i) := by
    intro i
    by_cases hip : i = p
    · rw [hip, Function.update_self]
      exact hg.hadamard_advD q
    · rw [Function.update_of_ne hip]
      exact hg
  refine (norm_compose_le (hf.hadamard (advD_isHermitian p)) hshape).trans ?_
  have hprod : ∏ i, ‖Function.update (fun _ : α => Γg) p (Γg ⊙ advD q) i‖
      = ‖Γg ⊙ advD q‖ * ‖Γg‖ ^ (Fintype.card α - 1) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), Function.update_self]
    congr 1
    rw [Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)],
      Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ p),
      Finset.card_univ]
  rw [hprod]

/-- **The composition theorem** (HLŠ Theorem 13, uniform unit-cost case;
BL Theorem 1, `≥` direction): `ADV±(f) * ADV±(g) ≤ ADV±(f ∘ gᵏ)`. -/
theorem advPM_mul_le_advPM_composeFun (f : (α → Bool) → Bool)
    (g : (β → Bool) → Bool) :
    advPM f * advPM g ≤ advPM (composeFun f g) := by
  classical
  have hkey : ∀ Γf, IsAdvMatrix f Γf → (∀ i, ‖Γf ⊙ advD i‖ ≤ 1) →
      ∀ Γg, IsAdvMatrix g Γg → (∀ j, ‖Γg ⊙ advD j‖ ≤ 1) →
      ‖Γf‖ * ‖Γg‖ ≤ advPM (composeFun f g) := by
    intro Γf hf1 hf2 Γg hg1 hg2
    rcases eq_or_lt_of_le (norm_nonneg Γf) with hf0 | hΓfpos
    · rw [← hf0, zero_mul]
      exact advPM_nonneg _
    rcases eq_or_lt_of_le (norm_nonneg Γg) with hg0 | hΓgpos
    · rw [← hg0, mul_zero]
      exact advPM_nonneg _
    -- a nonzero adversary matrix for f forces α to be inhabited
    have hα : Nonempty α := by
      have hΓf0 : Γf ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hΓfpos
        exact lt_irrefl 0 hΓfpos
      have hentry : ∃ x y, Γf x y ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hΓf0 (Matrix.ext fun x y => by
          rw [hc x y, Matrix.zero_apply])
      obtain ⟨x, y, hxy⟩ := hentry
      have hfxy : f x ≠ f y := fun h => hxy (hf1.apply_eq_zero h)
      have hxyne : x ≠ y := fun h => hfxy (by rw [h])
      obtain ⟨i, -⟩ := Function.ne_iff.mp hxyne
      exact ⟨i⟩
    have := hα
    have hk : Fintype.card α - 1 + 1 = Fintype.card α :=
      Nat.succ_pred_eq_of_pos Fintype.card_pos
    -- the composed witness
    have hΓh_adv : IsAdvMatrix (composeFun f g)
        (compose (constFam g) Γf fun _ => Γg) :=
      isAdvMatrix_compose hf1 fun _ => hg1
    have hmask : ∀ ℓ : α × β,
        ‖compose (constFam g) Γf (fun _ => Γg) ⊙ advD ℓ‖
          ≤ ‖Γg‖ ^ (Fintype.card α - 1) := by
      rintro ⟨p, q⟩
      refine (norm_compose_mask hf1.isHermitian hg1 p q).trans ?_
      calc ‖Γf ⊙ advD p‖ * (‖Γg ⊙ advD q‖ * ‖Γg‖ ^ (Fintype.card α - 1))
          ≤ 1 * (1 * ‖Γg‖ ^ (Fintype.card α - 1)) :=
            mul_le_mul (hf2 p)
              (mul_le_mul (hg2 q) le_rfl (by positivity) zero_le_one)
              (by positivity) zero_le_one
        _ = ‖Γg‖ ^ (Fintype.card α - 1) := by ring
    have hfinal := norm_div_le_advPM hΓh_adv hmask (pow_pos hΓgpos _)
    have hlow : ‖Γf‖ * ‖Γg‖
        ≤ ‖compose (constFam g) Γf (fun _ => Γg)‖ / ‖Γg‖ ^ (Fintype.card α - 1) := by
      rw [le_div_iff₀ (pow_pos hΓgpos _)]
      calc ‖Γf‖ * ‖Γg‖ * ‖Γg‖ ^ (Fintype.card α - 1)
          = ‖Γf‖ * (‖Γg‖ * ‖Γg‖ ^ (Fintype.card α - 1)) := mul_assoc _ _ _
        _ = ‖Γf‖ * ‖Γg‖ ^ (Fintype.card α - 1 + 1) := by rw [← pow_succ']
        _ = ‖Γf‖ * ‖Γg‖ ^ (Fintype.card α) := by rw [hk]
        _ ≤ ‖compose (constFam g) Γf (fun _ => Γg)‖ := by
            have h := le_norm_compose (g := constFam g) hf1.isHermitian fun _ : α => hg1
            rw [Finset.prod_const, Finset.card_univ] at h
            exact h
    exact hlow.trans hfinal
  -- two supremum passes
  rcases eq_or_lt_of_le (advPM_nonneg g) with hg0 | hg0
  · rw [← hg0, mul_zero]
    exact advPM_nonneg _
  rw [← le_div_iff₀ hg0]
  refine advPM_le fun Γf hf1 hf2 => ?_
  rw [le_div_iff₀ hg0]
  rcases eq_or_lt_of_le (norm_nonneg Γf) with hf0 | hf0
  · rw [← hf0, zero_mul]
    exact advPM_nonneg _
  rw [mul_comm, ← le_div_iff₀ hf0]
  refine advPM_le fun Γg hg1 hg2 => ?_
  rw [le_div_iff₀ hf0, mul_comm]
  exact hkey Γf hf1 hf2 Γg hg1 hg2

/-! ## The iterated corollary -/

/-- Index types for iterated composition: `α`, `α × α`, `α × (α × α)`, … -/
@[expose]
def iterIdx (α : Type*) : ℕ → Type _
  | 0 => α
  | d + 1 => α × iterIdx α d

instance iterIdx.fintype (α : Type*) [Fintype α] :
    (d : ℕ) → Fintype (iterIdx α d)
  | 0 => ‹Fintype α›
  | d + 1 =>
      letI := iterIdx.fintype α d
      inferInstanceAs (Fintype (α × iterIdx α d))

instance iterIdx.decEq (α : Type*) [DecidableEq α] :
    (d : ℕ) → DecidableEq (iterIdx α d)
  | 0 => ‹DecidableEq α›
  | d + 1 =>
      letI := iterIdx.decEq α d
      inferInstanceAs (DecidableEq (α × iterIdx α d))

/-- Iterated composition `f^{∘(d+1)}`. -/
@[expose]
def iterFun (f : (α → Bool) → Bool) : (d : ℕ) → ((iterIdx α d → Bool) → Bool)
  | 0 => f
  | d + 1 => composeFun f (iterFun f d)

/-- Iterated composition corollary: `ADV±(f)^(d+1) ≤ ADV±(f^{∘(d+1)})`. -/
theorem advPM_pow_le_advPM_iterFun (f : (α → Bool) → Bool) (d : ℕ) :
    advPM f ^ (d + 1) ≤ advPM (iterFun f d) := by
  induction d with
  | zero =>
      change advPM f ^ 1 ≤ advPM f
      rw [pow_one]
  | succ d ih =>
      calc advPM f ^ (d + 2) = advPM f * advPM f ^ (d + 1) := by ring
        _ ≤ advPM f * advPM (iterFun f d) :=
            mul_le_mul_of_nonneg_left ih (advPM_nonneg f)
        _ ≤ advPM (iterFun f (d + 1)) :=
            advPM_mul_le_advPM_composeFun f (iterFun f d)

end QuantumQueryComplexity

end SourceCompositionMain

section SourceDualCompose

/-!
# Composition of dual solutions and the composition upper bound

Dual solutions compose multiplicatively (Belovs–Lee, arXiv:2004.06439,
Theorem 24; the construction is from LMRSS): tensoring an outer dual solution
with an inner one,

  `u_{x,(p,q)} = ψ_{x_tilde,p} ⊗ u_{x·ₚ,q}`,  `v_{x,(p,q)} = φ_{x_tilde,p} ⊗ v_{x·ₚ,q}`,

produces a feasible dual solution for `f ∘ gᵏ` of cost the product of the
costs (`DualPair.compose`).  This is exactly where the LMRSS constraints on
pairs with `g x = g y` are used: they kill the blocks where the inner
function values agree.

Consequently `advDual (f ∘ gᵏ) ≤ advDual f * advDual g`, and by weak duality

  `ADV±(f ∘ gᵏ) ≤ advDual f * advDual g`   (`advPM_composeFun_le_advDual_mul`)

unconditionally.  Combined with the lower bound
`advPM_mul_le_advPM_composeFun` this sandwiches the composed value.  The
perfect composition theorem `ADV±(f ∘ gᵏ) = ADV±(f) · ADV±(g)` follows by
applying `advPM_composeFun_eq_of_dual_eq` to the strong-duality theorem
`advDual_eq_advPM` in `SourceDualityMain`. The unconditional endpoint is
`advPM_composeFun_eq`.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-- The `c`-weighted cost of a dual solution is bounded by `V`.

Stated for a general alphabet and output type: the weighted cost is what the
outer solution of a composition must control, and in
`SourceComposeShared` the outer function is a non-Boolean maximum. -/
def DualPair.IsWeightedCostLe {ι K : Type*} [Fintype ι] [Fintype K] {σ : Type*} [DecidableEq σ]
    {O : Type*} [DecidableEq O] {f : (ι → σ) → O}
    (P : DualPair K f) (c : ι → ℝ) (V : ℝ) : Prop :=
  (∀ x, ∑ i, c i * ∑ k, P.u x i k * P.u x i k ≤ V) ∧
  (∀ x, ∑ i, c i * ∑ k, P.v x i k * P.v x i k ≤ V)

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  {f : (α → Bool) → Bool} {g : α → (β → Bool) → Bool}
  {K₁ K₂ : Type*} [Fintype K₁] [Fintype K₂]

/-- **Composition of dual solutions** (BL Theorem 24 construction). -/
def DualPair.compose (Pf : DualPair K₁ f) (Pg : ∀ i, DualPair K₂ (g i)) :
    DualPair (K₁ × K₂) (composeFunFam f g) where
  u x ℓ k := Pf.u (tilde g x) ℓ.1 k.1 * (Pg ℓ.1).u (slice x ℓ.1) ℓ.2 k.2
  v y ℓ k := Pf.v (tilde g y) ℓ.1 k.1 * (Pg ℓ.1).v (slice y ℓ.1) ℓ.2 k.2
  constraint x y := by
    -- The inner sum factorises as (outer inner product) * (inner one).
    have hinner : ∀ (p : α) (q : β),
        (∑ k : K₁ × K₂,
          (Pf.u (tilde g x) p k.1 * (Pg p).u (slice x p) q k.2) *
          (Pf.v (tilde g y) p k.1 * (Pg p).v (slice y p) q k.2))
        = (∑ k₁, Pf.u (tilde g x) p k₁ * Pf.v (tilde g y) p k₁) *
          (∑ k₂, (Pg p).u (slice x p) q k₂ * (Pg p).v (slice y p) q k₂) := by
      intro p q
      rw [Fintype.sum_prod_type]
      change (∑ k₁, ∑ k₂,
          (Pf.u (tilde g x) p k₁ * (Pg p).u (slice x p) q k₂) *
          (Pf.v (tilde g y) p k₁ * (Pg p).v (slice y p) q k₂)) = _
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k₁ _ =>
        Finset.sum_congr rfl fun k₂ _ => by ring
    -- Summing over the `p`-th block uses the inner constraint (both cases!).
    have hp : ∀ p : α,
        (∑ q : β, if slice x p q = slice y p q then (0:ℝ) else
          ∑ k : K₁ × K₂,
            (Pf.u (tilde g x) p k.1 * (Pg p).u (slice x p) q k.2) *
            (Pf.v (tilde g y) p k.1 * (Pg p).v (slice y p) q k.2))
        = if g p (slice x p) = g p (slice y p) then (0:ℝ) else
            ∑ k₁, Pf.u (tilde g x) p k₁ * Pf.v (tilde g y) p k₁ := by
      intro p
      have h1 : ∀ q : β,
          (if slice x p q = slice y p q then (0:ℝ) else
            ∑ k : K₁ × K₂,
              (Pf.u (tilde g x) p k.1 * (Pg p).u (slice x p) q k.2) *
              (Pf.v (tilde g y) p k.1 * (Pg p).v (slice y p) q k.2))
          = (∑ k₁, Pf.u (tilde g x) p k₁ * Pf.v (tilde g y) p k₁) *
            (if slice x p q = slice y p q then (0:ℝ) else
              ∑ k₂, (Pg p).u (slice x p) q k₂ * (Pg p).v (slice y p) q k₂) := by
        intro q
        by_cases hq : slice x p q = slice y p q
        · rw [ite_eq_left hq, ite_eq_left hq, mul_zero]
        · rw [ite_eq_right hq, ite_eq_right hq, hinner p q]
      rw [Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ) => h1 q,
        ← Finset.mul_sum, (Pg p).constraint (slice x p) (slice y p)]
      by_cases hgp : g p (slice x p) = g p (slice y p)
      · rw [ite_eq_left hgp, ite_eq_left hgp, mul_zero]
      · rw [ite_eq_right hgp, ite_eq_right hgp, mul_one]
    -- The outer constraint finishes the computation.
    change (∑ ℓ : α × β, if x ℓ = y ℓ then (0:ℝ) else
      ∑ k : K₁ × K₂,
        (Pf.u (tilde g x) ℓ.1 k.1 * (Pg ℓ.1).u (slice x ℓ.1) ℓ.2 k.2) *
        (Pf.v (tilde g y) ℓ.1 k.1 * (Pg ℓ.1).v (slice y ℓ.1) ℓ.2 k.2))
      = if f (tilde g x) = f (tilde g y) then (0:ℝ) else 1
    trans (∑ p : α, if g p (slice x p) = g p (slice y p) then (0:ℝ) else
        ∑ k₁, Pf.u (tilde g x) p k₁ * Pf.v (tilde g y) p k₁)
    · rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun p _ => hp p
    · exact Pf.constraint (tilde g x) (tilde g y)

omit [DecidableEq α] [DecidableEq β] in
/-- Squared mass of a block tensor factors into the two squared masses. -/
lemma sum_tensor_mass (u : α → K₁ → ℝ) (v : α → β → K₂ → ℝ) :
    (∑ ℓ : α × β, ∑ k : K₁ × K₂,
      (u ℓ.1 k.1 * v ℓ.1 ℓ.2 k.2) * (u ℓ.1 k.1 * v ℓ.1 ℓ.2 k.2)) =
      ∑ p, (∑ k₁, u p k₁ * u p k₁) * (∑ q, ∑ k₂, v p q k₂ * v p q k₂) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ => by ring

omit [DecidableEq α] [DecidableEq β] in
/-- Inner mass bounds give a weighted bound on the block tensor's mass. -/
lemma sum_tensor_mass_le (u : α → K₁ → ℝ) (v : α → β → K₂ → ℝ)
    {c : α → ℝ} {V : ℝ} (hu : ∑ p, c p * ∑ k₁, u p k₁ * u p k₁ ≤ V)
    (hv : ∀ p, ∑ q, ∑ k₂, v p q k₂ * v p q k₂ ≤ c p) :
    (∑ ℓ : α × β, ∑ k : K₁ × K₂,
      (u ℓ.1 k.1 * v ℓ.1 ℓ.2 k.2) * (u ℓ.1 k.1 * v ℓ.1 ℓ.2 k.2)) ≤ V := by
  rw [sum_tensor_mass]
  refine le_trans (Finset.sum_le_sum fun p _ => ?_) hu
  rw [mul_comm (c p)]
  exact mul_le_mul_of_nonneg_left (hv p) (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)

omit [DecidableEq α] [DecidableEq β] in
/-- **Weighted dual composition**: a `c`-weighted outer bound composes with
inner solutions of costs `c i` to an ordinary bound. -/
lemma DualPair.compose_isWeightedCostLe {Pf : DualPair K₁ f}
    {Pg : ∀ i, DualPair K₂ (g i)} {c : α → ℝ} {V : ℝ}
    (hf : Pf.IsWeightedCostLe c V) (hg : ∀ i, (Pg i).IsCostLe (c i)) :
    (Pf.compose Pg).IsCostLe V := by
  constructor
  · intro x
    exact sum_tensor_mass_le (Pf.u (tilde g x)) (fun p => (Pg p).u (slice x p))
      (hf.1 (tilde g x)) (fun p => (hg p).1 (slice x p))
  · intro x
    exact sum_tensor_mass_le (Pf.v (tilde g x)) (fun p => (Pg p).v (slice x p))
      (hf.2 (tilde g x)) (fun p => (hg p).2 (slice x p))

omit [DecidableEq α] [DecidableEq β] in
/-- The cost of a composed dual solution is the product of the costs. -/
lemma DualPair.compose_isCostLe {Pf : DualPair K₁ f} {Pg : ∀ i, DualPair K₂ (g i)}
    {c₁ c₂ : ℝ} (hf : Pf.IsCostLe c₁) (hg : ∀ i, (Pg i).IsCostLe c₂)
    (hc₂ : 0 ≤ c₂) :
    (Pf.compose Pg).IsCostLe (c₁ * c₂) := by
  apply DualPair.compose_isWeightedCostLe (c := fun _ => c₂) ?_ hg
  constructor
  · intro x
    simpa only [← Finset.mul_sum, mul_comm] using
      mul_le_mul_of_nonneg_right (hf.1 x) hc₂
  · intro x
    simpa only [← Finset.mul_sum, mul_comm] using
      mul_le_mul_of_nonneg_right (hf.2 x) hc₂

omit [DecidableEq α] [DecidableEq β] in
/-- **The dual value is submultiplicative under composition.** -/
theorem advDual_composeFun_le (f : (α → Bool) → Bool)
    (g : (β → Bool) → Bool) :
    advDual (composeFun f g) ≤ advDual f * advDual g := by
  classical
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hA : 0 ≤ advDual f := advDual_nonneg f
  have hB : 0 ≤ advDual g := advDual_nonneg g
  have hden : (0:ℝ) < advDual f + advDual g + 1 := by linarith
  set δ := min 1 (ε / (advDual f + advDual g + 1)) with hδdef
  have hδpos : 0 < δ := lt_min one_pos (div_pos hε hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (advDual f + advDual g + 1) ≤ ε := by
    have h2 : δ ≤ ε / (advDual f + advDual g + 1) := min_le_right _ _
    calc δ * (advDual f + advDual g + 1)
        ≤ (ε / (advDual f + advDual g + 1)) * (advDual f + advDual g + 1) :=
          mul_le_mul_of_nonneg_right h2 hden.le
      _ = ε := div_mul_cancel₀ _ hden.ne'
  obtain ⟨n₁, P₁, hP₁⟩ :=
    exists_dualPair_of_lt (g := f) (c := advDual f + δ) (by linarith)
  obtain ⟨n₂, P₂, hP₂⟩ :=
    exists_dualPair_of_lt (g := g) (c := advDual g + δ) (by linarith)
  have hcost : (P₁.compose (g := constFam g) (fun _ => P₂)).IsCostLe
      ((advDual f + δ) * (advDual g + δ)) :=
    DualPair.compose_isCostLe hP₁ (fun _ => hP₂) (by linarith)
  have hle := advDual_le_of_dualPair
    (P₁.compose (g := constFam g) (fun _ => P₂)) (by nlinarith) hcost
  refine hle.trans ?_
  nlinarith [mul_le_of_le_one_right hδpos.le hδ1]

/-- **The composition upper bound**, unconditional: the adversary bound of a
composed function is at most the product of the *dual* values. -/
theorem advPM_composeFun_le_advDual_mul (f : (α → Bool) → Bool)
    (g : (β → Bool) → Bool) :
    advPM (composeFun f g) ≤ advDual f * advDual g :=
  (advPM_le_advDual _).trans (advDual_composeFun_le f g)

/-- The composed adversary bound is sandwiched between the product of the
primal values and the product of the dual values. -/
theorem advPM_composeFun_sandwich (f : (α → Bool) → Bool)
    (g : (β → Bool) → Bool) :
    advPM f * advPM g ≤ advPM (composeFun f g) ∧
      advPM (composeFun f g) ≤ advDual f * advDual g :=
  ⟨advPM_mul_le_advPM_composeFun f g, advPM_composeFun_le_advDual_mul f g⟩

/-- Perfect composition from supplied duality equalities. The unconditional
`advPM_composeFun_eq` below discharges these using `advDual_eq_advPM`. -/
theorem advPM_composeFun_eq_of_dual_eq (f : (α → Bool) → Bool)
    (g : (β → Bool) → Bool) (hf : advDual f = advPM f)
    (hg : advDual g = advPM g) :
    advPM (composeFun f g) = advPM f * advPM g := by
  refine le_antisymm ?_ (advPM_mul_le_advPM_composeFun f g)
  rw [← hf, ← hg]
  exact advPM_composeFun_le_advDual_mul f g

/-! ## Functions whose adversary bound is certified on both sides -/

/-- `HasAdvValue f c` records that the adversary bound of `f` equals `c` *and*
that this value is certified by a dual solution — i.e. strong duality holds at
`f`.  This is exactly the hypothesis needed for perfect composition, and it is
established for concrete functions by exhibiting a matching primal/dual pair. -/
def HasAdvValue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) (c : ℝ) : Prop :=
  advPM f = c ∧ advDual f = c

/-- Building a `HasAdvValue` from a primal lower bound and a dual upper bound:
weak duality squeezes them together. -/
theorem hasAdvValue_of_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → Bool} {c : ℝ} (hprimal : c ≤ advPM f)
    (hdual : advDual f ≤ c) : HasAdvValue f c :=
  ⟨le_antisymm ((advPM_le_advDual f).trans hdual) hprimal,
    le_antisymm hdual (hprimal.trans (advPM_le_advDual f))⟩

/-- **Certified values compose exactly.**  If strong duality holds at `f` and
at `g`, then it holds at `f ∘ gᵏ`, with the product value. -/
theorem HasAdvValue.compose {g : (β → Bool) → Bool} {a b : ℝ}
    (hf : HasAdvValue f a) (hg : HasAdvValue g b) :
    HasAdvValue (composeFun f g) (a * b) := by
  have hprimal : a * b ≤ advPM (composeFun f g) := by
    rw [← hf.1, ← hg.1]
    exact advPM_mul_le_advPM_composeFun f g
  have hdual : advDual (composeFun f g) ≤ a * b := by
    rw [← hf.2, ← hg.2]
    exact advDual_composeFun_le f g
  exact hasAdvValue_of_le hprimal hdual

end QuantumQueryComplexity

end SourceDualCompose

section SourceWeighted

/-!
# The weighted composition lower bound

The composition machinery now allows a *different* inner function in each
block (`compose g Γf M` with `g : α → (β → Bool) → Bool`), which is what the
cost/weighted version of the adversary composition theorem needs.

`advPM_composeFunFam_ge` is the general weighted statement: if the outer
witness `Γf` satisfies

  `‖Γf ⊙ D_p‖ · V ≤ ‖Γf‖ · ‖M p‖`  for every outer coordinate `p`,

— i.e. `Γf` certifies the value `V` for `f` *with costs* `‖M p‖` — and each
inner witness `M i` is feasible, then `ADV±(f ∘ (g_1, …, g_k)) ≥ V`.

This is HLŠ Theorem 13 (`ADV±_α(h) ≥ ADV±_β(f)` with `β_i = ADV±(g_i)`) in
witness form: the cost vector enters as the norms `‖M p‖` of the inner
witnesses, so no separate `ADV±_α` definition is needed.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **The weighted composition lower bound.** -/
theorem advPM_composeFunFam_ge {f : (α → Bool) → Bool}
    {g : α → (β → Bool) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (β → Bool) (β → Bool) ℝ}
    (hf : IsAdvMatrix f Γf) (hM : ∀ i, IsAdvMatrix (g i) (M i))
    (hMfeas : ∀ i q, ‖M i ⊙ advD q‖ ≤ 1) (hMpos : ∀ i, 0 < ‖M i‖)
    {V : ℝ} (hVpos : 0 < V) (hΓfpos : 0 < ‖Γf‖)
    (hV : ∀ p, ‖Γf ⊙ advD p‖ * V ≤ ‖Γf‖ * ‖M p‖) :
    V ≤ advPM (composeFunFam f g) := by
  classical
  have hCpos : 0 < ∏ i, ‖M i‖ := Finset.prod_pos fun i _ => hMpos i
  have hcpos : 0 < ‖Γf‖ * (∏ i, ‖M i‖) / V := by positivity
  have hΓh : IsAdvMatrix (composeFunFam f g) (compose g Γf M) :=
    isAdvMatrix_compose hf hM
  have hmask : ∀ ℓ : α × β,
      ‖compose g Γf M ⊙ advD ℓ‖ ≤ ‖Γf‖ * (∏ i, ‖M i‖) / V := by
    rintro ⟨p, q⟩
    rw [compose_hadamard_advD g Γf M hM p q]
    have hshape : ∀ i, IsAdvMatrix (g i)
        (Function.update M p (M p ⊙ advD q) i) := by
      intro i
      by_cases hip : i = p
      · subst hip
        rw [Function.update_self]
        exact (hM i).hadamard_advD q
      · rw [Function.update_of_ne hip]
        exact hM i
    refine (norm_compose_le
      (hf.isHermitian.hadamard (advD_isHermitian p)) hshape).trans ?_
    -- split the product at `p`
    have hprod : ∏ i, ‖Function.update M p (M p ⊙ advD q) i‖
        = ‖M p ⊙ advD q‖ * ∏ i ∈ Finset.univ.erase p, ‖M i‖ := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), Function.update_self]
      apply congrArg (‖M p ⊙ advD q‖ * ·)
      exact Finset.prod_congr rfl fun i hi => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    have herase : (∏ i ∈ Finset.univ.erase p, ‖M i‖) * ‖M p‖
        = ∏ i, ‖M i‖ := by
      rw [mul_comm]
      exact Finset.mul_prod_erase Finset.univ (fun i => ‖M i‖)
        (Finset.mem_univ p)
    have hepos : 0 < ∏ i ∈ Finset.univ.erase p, ‖M i‖ :=
      Finset.prod_pos fun i _ => hMpos i
    rw [hprod]
    -- `‖Γf ⊙ D_p‖ * (‖M p ⊙ D_q‖ * ∏_{i≠p}) ≤ ‖Γf‖ * ∏ / V`
    rw [le_div_iff₀ hVpos]
    calc ‖Γf ⊙ advD p‖ * (‖M p ⊙ advD q‖ *
          ∏ i ∈ Finset.univ.erase p, ‖M i‖) * V
        ≤ ‖Γf ⊙ advD p‖ * (1 * ∏ i ∈ Finset.univ.erase p, ‖M i‖) * V := by
          have h1 : ‖M p ⊙ advD q‖ * ∏ i ∈ Finset.univ.erase p, ‖M i‖
              ≤ 1 * ∏ i ∈ Finset.univ.erase p, ‖M i‖ :=
            mul_le_mul_of_nonneg_right (hMfeas p q) hepos.le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) hVpos.le
      _ = (‖Γf ⊙ advD p‖ * V) * ∏ i ∈ Finset.univ.erase p, ‖M i‖ := by ring
      _ ≤ (‖Γf‖ * ‖M p‖) * ∏ i ∈ Finset.univ.erase p, ‖M i‖ :=
          mul_le_mul_of_nonneg_right (hV p) hepos.le
      _ = ‖Γf‖ * ∏ i, ‖M i‖ := by rw [← herase]; ring
  have hnorm : ‖compose g Γf M‖ = ‖Γf‖ * ∏ i, ‖M i‖ :=
    norm_compose hf.isHermitian hM
  have h := norm_div_le_advPM hΓh hmask hcpos
  rw [hnorm] at h
  have hsimp : ‖Γf‖ * (∏ i, ‖M i‖) / (‖Γf‖ * (∏ i, ‖M i‖) / V) = V := by
    field_simp
  rwa [hsimp] at h

end QuantumQueryComplexity

end SourceWeighted

section SourceAndOr

/-!
# The two-bit AND and OR functions have adversary bound `√2`

We compute `ADV±(AND₂) = ADV±(OR₂) = √2` *with a matching dual certificate*,
i.e. we establish `HasAdvValue and2 (√2)` and `HasAdvValue or2 (√2)`.  Strong
duality is therefore available at these functions unconditionally, so the
perfect composition theorem applies to them.

The primal witness is the star matrix of HLŠ §6: the adversary matrix
supported on the two edges joining `11` to its neighbours `01` and `10`.  Its
spectral norm is `√2` and each masked norm `‖Γ ⊙ D_i‖` is `1`.

The dual witness is one-dimensional (`K = Unit`), with weights
`α = 2^(-1/4)` at `11`, `β = 2^(1/4)` on the sensitive coordinate of each
neighbour, and `δ = 2^(1/4)/2` at `00`; its cost is exactly `√2`.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## Enumeration of the four two-bit inputs -/

/-- The input `00`. -/
abbrev i00 : Fin 2 → Bool := ![false, false]
/-- The input `01`. -/
abbrev i01 : Fin 2 → Bool := ![false, true]
/-- The input `10`. -/
abbrev i10 : Fin 2 → Bool := ![true, false]
/-- The input `11`. -/
abbrev i11 : Fin 2 → Bool := ![true, true]

lemma fin2Bool_cases (w : Fin 2 → Bool) :
    w = i00 ∨ w = i01 ∨ w = i10 ∨ w = i11 := by decide +revert

lemma sum_fin2Bool (f : (Fin 2 → Bool) → ℝ) :
    ∑ w : Fin 2 → Bool, f w = f i00 + f i01 + f i10 + f i11 := by
  rw [show (Finset.univ : Finset (Fin 2 → Bool)) = {i00, i01, i10, i11} from
    by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

lemma dotProduct_fin2Bool (x y : (Fin 2 → Bool) → ℝ) :
    x ⬝ᵥ y = x i00 * y i00 + x i01 * y i01 + x i10 * y i10 + x i11 * y i11 :=
  sum_fin2Bool fun w => x w * y w

/-! ## The two-bit AND function and its primal witness -/

/-- The two-bit AND function. -/
def and2 : (Fin 2 → Bool) → Bool := fun x => x 0 && x 1

/-- The star adversary matrix for `AND₂`, centred at `11`. -/
noncomputable def and2Gamma : Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℝ :=
  pairMatrix i01 i11 + pairMatrix i10 i11

lemma and2Gamma_mulVec_apply (y : (Fin 2 → Bool) → ℝ) (w : Fin 2 → Bool) :
    (and2Gamma *ᵥ y) w
      = ((if i01 = w then y i11 else 0) + (if i11 = w then y i01 else 0))
        + ((if i10 = w then y i11 else 0) + (if i11 = w then y i10 else 0)) := by
  rw [and2Gamma, Matrix.add_mulVec, pairMatrix_mulVec, pairMatrix_mulVec]
  rfl

lemma and2Gamma_bilinear (x y : (Fin 2 → Bool) → ℝ) :
    x ⬝ᵥ and2Gamma *ᵥ y
      = (x i01 + x i10) * y i11 + x i11 * (y i01 + y i10) := by
  rw [show x ⬝ᵥ and2Gamma *ᵥ y = ∑ w, x w * (and2Gamma *ᵥ y) w from rfl,
    sum_fin2Bool]
  simp only [and2Gamma_mulVec_apply]
  norm_num +decide
  ring

lemma norm_and2Gamma_le : ‖and2Gamma‖ ≤ Real.sqrt 2 := by
  refine l2_opNorm_le_of_forall_dotProduct _ (Real.sqrt_nonneg 2) fun x y => ?_
  rw [and2Gamma_bilinear]
  have hx := dotProduct_fin2Bool x x
  have hy := dotProduct_fin2Bool y y
  have hcs : ((x i01 + x i10) * y i11 + x i11 * (y i01 + y i10)) ^ 2
      ≤ ((x i01 + x i10) ^ 2 / 2 + (x i11) ^ 2) *
        (2 * (y i11) ^ 2 + (y i01 + y i10) ^ 2) := by
    nlinarith only [sq_nonneg ((x i01 + x i10) * (y i01 + y i10) - 2 * x i11 * y i11)]
  have hX : (x i01 + x i10) ^ 2 / 2 + (x i11) ^ 2 ≤ x ⬝ᵥ x := by
    rw [hx]
    nlinarith only [sq_nonneg (x i01 - x i10), sq_nonneg (x i00)]
  have hY : 2 * (y i11) ^ 2 + (y i01 + y i10) ^ 2 ≤ 2 * (y ⬝ᵥ y) := by
    rw [hy]
    nlinarith only [sq_nonneg (y i01 - y i10), sq_nonneg (y i00)]
  have hsq : ((x i01 + x i10) * y i11 + x i11 * (y i01 + y i10)) ^ 2
      ≤ 2 * (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
    calc ((x i01 + x i10) * y i11 + x i11 * (y i01 + y i10)) ^ 2
        ≤ ((x i01 + x i10) ^ 2 / 2 + (x i11) ^ 2) *
          (2 * (y i11) ^ 2 + (y i01 + y i10) ^ 2) := hcs
      _ ≤ (x ⬝ᵥ x) * (2 * (y ⬝ᵥ y)) :=
          mul_le_mul hX hY (by positivity) (dotProduct_self_nonneg x)
      _ = 2 * (x ⬝ᵥ x) * (y ⬝ᵥ y) := by ring
  calc |(x i01 + x i10) * y i11 + x i11 * (y i01 + y i10)|
      = Real.sqrt (((x i01 + x i10) * y i11 + x i11 * (y i01 + y i10)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (2 * (x ⬝ᵥ x) * (y ⬝ᵥ y)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 2 * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
        rw [Real.sqrt_mul
            (mul_nonneg (by norm_num) (dotProduct_self_nonneg x)),
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]

/-- The top eigenvector of the star matrix. -/
noncomputable def and2Vec : (Fin 2 → Bool) → ℝ :=
  fun w => if w = i01 then 1 else if w = i10 then 1
    else if w = i11 then Real.sqrt 2 else 0

lemma sqrt_two_le_norm_and2Gamma : Real.sqrt 2 ≤ ‖and2Gamma‖ := by
  have h := abs_dotProduct_mulVec_le and2Gamma and2Vec and2Vec
  rw [and2Gamma_bilinear] at h
  have e00 : and2Vec i00 = 0 := by norm_num [and2Vec]
  have e01 : and2Vec i01 = 1 := by norm_num [and2Vec]
  have e10 : and2Vec i10 = 1 := by norm_num [and2Vec]
  have e11 : and2Vec i11 = Real.sqrt 2 := by norm_num [and2Vec]
  have hdot : and2Vec ⬝ᵥ and2Vec = 4 := by
    rw [dotProduct_fin2Bool, e00, e01, e10, e11,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have h4 : Real.sqrt (4:ℝ) = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [e01, e10, e11, hdot, h4] at h
  have habs : |(1 + 1 : ℝ) * Real.sqrt 2 + Real.sqrt 2 * (1 + 1)|
      = 4 * Real.sqrt 2 := by
    rw [abs_of_nonneg (by positivity)]
    ring
  rw [habs] at h
  linarith

lemma norm_and2Gamma : ‖and2Gamma‖ = Real.sqrt 2 :=
  le_antisymm norm_and2Gamma_le sqrt_two_le_norm_and2Gamma

lemma and2Gamma_isAdvMatrix : IsAdvMatrix and2 and2Gamma := by
  refine ⟨(pairMatrix_isHermitian _ _).add (pairMatrix_isHermitian _ _), ?_⟩
  intro x y hxy
  rw [and2Gamma, Matrix.add_apply]
  have h1 : ¬(i01 = x ∧ i11 = y) := by
    rintro ⟨rfl, rfl⟩
    exact absurd hxy (by simp [and2])
  have h2 : ¬(i11 = x ∧ i01 = y) := by
    rintro ⟨rfl, rfl⟩
    exact absurd hxy (by simp [and2])
  have h3 : ¬(i10 = x ∧ i11 = y) := by
    rintro ⟨rfl, rfl⟩
    exact absurd hxy (by simp [and2])
  have h4 : ¬(i11 = x ∧ i10 = y) := by
    rintro ⟨rfl, rfl⟩
    exact absurd hxy (by simp [and2])
  rw [pairMatrix_apply_eq_zero h1 h2, pairMatrix_apply_eq_zero h3 h4, add_zero]

lemma and2Gamma_hadamard_zero : and2Gamma ⊙ advD 0 = pairMatrix i01 i11 := by
  rw [and2Gamma, Matrix.add_hadamard, pairMatrix_hadamard_advD,
    pairMatrix_hadamard_advD, ite_eq_right (by decide), ite_eq_left (by decide), add_zero]

lemma and2Gamma_hadamard_one : and2Gamma ⊙ advD 1 = pairMatrix i10 i11 := by
  rw [and2Gamma, Matrix.add_hadamard, pairMatrix_hadamard_advD,
    pairMatrix_hadamard_advD, ite_eq_left (by decide), ite_eq_right (by decide), zero_add]

lemma and2Gamma_feasible : ∀ i : Fin 2, ‖and2Gamma ⊙ advD i‖ ≤ 1 := by
  rw [Fin.forall_fin_two]
  constructor
  · rw [and2Gamma_hadamard_zero, norm_pairMatrix (by decide)]
  · rw [and2Gamma_hadamard_one, norm_pairMatrix (by decide)]

theorem sqrt_two_le_advPM_and2 : Real.sqrt 2 ≤ advPM and2 := by
  have h := le_advPM and2Gamma_isAdvMatrix and2Gamma_feasible
  rwa [norm_and2Gamma] at h

/-! ## The dual witness -/

/-- `β = 2^(1/4)`. -/
noncomputable def and2Beta : ℝ := Real.sqrt (Real.sqrt 2)
/-- `α = 2^(-1/4)`. -/
noncomputable def and2Alpha : ℝ := 1 / and2Beta
/-- `δ = 2^(1/4)/2`. -/
noncomputable def and2Delta : ℝ := and2Beta / 2

lemma and2Beta_pos : 0 < and2Beta :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by norm_num))

lemma and2Beta_ne_zero : and2Beta ≠ 0 := ne_of_gt and2Beta_pos

lemma and2Beta_sq : and2Beta * and2Beta = Real.sqrt 2 :=
  Real.mul_self_sqrt (Real.sqrt_nonneg 2)

lemma sqrt_two_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

lemma two_div_sqrt_two : 2 / Real.sqrt 2 = Real.sqrt 2 := by
  rw [eq_comm, eq_div_iff (ne_of_gt sqrt_two_pos),
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- The one-dimensional dual weights for `AND₂`. -/
noncomputable def and2DualVec (x : Fin 2 → Bool) (i : Fin 2) : ℝ :=
  if x 0 && x 1 then and2Alpha
  else if x 0 || x 1 then (if x i then 0 else and2Beta)
  else and2Delta

/-- The dual solution for `AND₂`. -/
noncomputable def and2Dual : DualPair Unit and2 where
  u x i _ := and2DualVec x i
  v x i _ := and2DualVec x i
  constraint x y := by
    have hβ : and2Beta ≠ 0 := and2Beta_ne_zero
    rw [Fin.sum_univ_two]
    rcases fin2Bool_cases x with rfl | rfl | rfl | rfl <;>
      rcases fin2Bool_cases y with rfl | rfl | rfl | rfl <;>
      simp [and2DualVec, and2, and2Alpha, and2Delta] <;>
      field_simp <;> norm_num

lemma and2Alpha_sq : and2Alpha * and2Alpha = 1 / Real.sqrt 2 := by
  rw [and2Alpha, div_mul_div_comm, one_mul, and2Beta_sq]

lemma and2Alpha_cost :
    and2Alpha * and2Alpha + and2Alpha * and2Alpha = Real.sqrt 2 := by
  rw [and2Alpha_sq, show 1 / Real.sqrt 2 + 1 / Real.sqrt 2
      = 2 / Real.sqrt 2 by ring]
  exact two_div_sqrt_two

lemma and2Delta_cost :
    and2Delta * and2Delta + and2Delta * and2Delta ≤ Real.sqrt 2 := by
  rw [and2Delta, show and2Beta / 2 * (and2Beta / 2)
      + and2Beta / 2 * (and2Beta / 2) = and2Beta * and2Beta / 2 by ring,
    and2Beta_sq]
  linarith [sqrt_two_pos]

lemma and2Dual_isCostLe : and2Dual.IsCostLe (Real.sqrt 2) := by
  have key : ∀ x : Fin 2 → Bool,
      (∑ i : Fin 2, ∑ _k : Unit, and2DualVec x i * and2DualVec x i)
        ≤ Real.sqrt 2 := by
    intro x
    rw [Fin.sum_univ_two]
    rcases fin2Bool_cases x with rfl | rfl | rfl | rfl
    · simpa [and2DualVec] using and2Delta_cost
    · simpa [and2DualVec] using le_of_eq and2Beta_sq
    · simpa [and2DualVec] using le_of_eq and2Beta_sq
    · simpa [and2DualVec] using le_of_eq and2Alpha_cost
  exact ⟨key, key⟩

theorem advDual_and2_le : advDual and2 ≤ Real.sqrt 2 :=
  advDual_le_of_dualPair and2Dual (Real.sqrt_nonneg 2) and2Dual_isCostLe

/-- **`ADV±(AND₂) = √2`, with a matching dual certificate.** -/
theorem hasAdvValue_and2 : HasAdvValue and2 (Real.sqrt 2) :=
  hasAdvValue_of_le sqrt_two_le_advPM_and2 advDual_and2_le

/-! ## Invariance of the adversary bound under relabelling

Negating the output, or negating a set of input bits, changes neither the
primal nor the dual value.  This transfers the `AND₂` computation to `OR₂`.
-/

section Invariance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] [Fintype ι] in
lemma isAdvMatrix_not {f : (ι → Bool) → Bool}
    {Γ : Matrix (ι → Bool) (ι → Bool) ℝ} :
    IsAdvMatrix (fun x => !(f x)) Γ ↔ IsAdvMatrix f Γ := by
  constructor
  · exact fun h => ⟨h.1, fun x y hxy => h.2 x y (congrArg (fun b => !b) hxy)⟩
  · exact fun h => ⟨h.1, fun x y hxy => h.2 x y (Bool.not_inj hxy)⟩

theorem advPM_not (f : (ι → Bool) → Bool) :
    advPM (fun x => !(f x)) = advPM f := by
  have key : ∀ g : (ι → Bool) → Bool,
      advPM (fun x => !(g x)) ≤ advPM g := fun g =>
    advPM_le fun Γ h1 h2 => le_advPM (isAdvMatrix_not.mp h1) h2
  refine le_antisymm (key f) ?_
  have h := key (fun x => !(f x))
  simpa using h

/-- Transport of a dual solution along output negation. -/
def DualPair.notFun {K : Type*} [Fintype K] {f : (ι → Bool) → Bool}
    (P : DualPair K f) : DualPair K (fun x => !(f x)) where
  u := P.u
  v := P.v
  constraint x y := by
    rw [P.constraint x y]
    by_cases h : f x = f y
    · rw [ite_eq_left h, ite_eq_left (by simp [h])]
    · rw [ite_eq_right h, ite_eq_right (by simpa using h)]

omit [DecidableEq ι] in
theorem advDual_not (f : (ι → Bool) → Bool) :
    advDual (fun x => !(f x)) = advDual f := by
  classical
  have key : ∀ g : (ι → Bool) → Bool,
      advDual (fun x => !(g x)) ≤ advDual g := by
    intro g
    refine le_csInf (dualCosts_nonempty g) ?_
    rintro c ⟨hc, n, P, hP⟩
    exact advDual_le_of_dualPair P.notFun hc ⟨hP.1, hP.2⟩
  refine le_antisymm (key f) ?_
  have h := key (fun x => !(f x))
  simpa using h

/-- Negating every input bit. -/
@[expose]
def flipAll : (ι → Bool) ≃ (ι → Bool) where
  toFun x := fun i => !(x i)
  invFun x := fun i => !(x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

omit [DecidableEq ι] [Fintype ι] in
lemma flipAll_apply (x : ι → Bool) (i : ι) : flipAll x i = !(x i) := rfl

omit [DecidableEq ι] [Fintype ι] in
lemma flipAll_coord_iff (x y : ι → Bool) (i : ι) :
    (flipAll x i = flipAll y i) ↔ (x i = y i) := by
  simp [flipAll_apply]

omit [DecidableEq ι] [Fintype ι] in
lemma isAdvMatrix_comp_flipAll {f : (ι → Bool) → Bool}
    {Γ : Matrix (ι → Bool) (ι → Bool) ℝ} (h : IsAdvMatrix f Γ) :
    IsAdvMatrix (fun x => f (flipAll x))
      (Γ.submatrix flipAll flipAll) := by
  refine ⟨?_, fun x y hxy => h.2 _ _ hxy⟩
  change (Γ.submatrix flipAll flipAll)ᴴ = _
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.submatrix_apply, star_trivial]
  exact (isHermitian_apply_symm h.1 _ _).symm

omit [DecidableEq ι] [Fintype ι] in
lemma submatrix_flipAll_hadamard (Γ : Matrix (ι → Bool) (ι → Bool) ℝ) (i : ι) :
    (Γ.submatrix flipAll flipAll) ⊙ advD i
      = (Γ ⊙ advD i).submatrix flipAll flipAll := by
  classical
  ext x y
  simp only [Matrix.hadamard_apply, Matrix.submatrix_apply, advD_apply]
  by_cases hi : x i = y i
  · rw [ite_eq_left hi, ite_eq_left ((flipAll_coord_iff x y i).mpr hi)]
  · rw [ite_eq_right hi, ite_eq_right (fun h => hi ((flipAll_coord_iff x y i).mp h))]

theorem advPM_comp_flipAll (f : (ι → Bool) → Bool) :
    advPM (fun x => f (flipAll x)) = advPM f := by
  have key : ∀ g : (ι → Bool) → Bool,
      advPM (fun x => g (flipAll x)) ≤ advPM g := by
    intro g
    refine advPM_le fun Γ h1 h2 => ?_
    have hsub : IsAdvMatrix g (Γ.submatrix flipAll flipAll) := by
      refine ⟨?_, fun x y hxy => ?_⟩
      · change (Γ.submatrix flipAll flipAll)ᴴ = _
        ext a b
        simp only [Matrix.conjTranspose_apply, Matrix.submatrix_apply,
          star_trivial]
        exact (isHermitian_apply_symm h1.1 _ _).symm
      · refine h1.2 _ _ ?_
        change g (flipAll (flipAll x)) = g (flipAll (flipAll y))
        simpa [flipAll] using hxy
    have hfeas : ∀ i, ‖(Γ.submatrix flipAll flipAll) ⊙ advD i‖ ≤ 1 := by
      intro i
      rw [submatrix_flipAll_hadamard, l2_opNorm_submatrix_equiv]
      exact h2 i
    have := le_advPM hsub hfeas
    rwa [l2_opNorm_submatrix_equiv] at this
  refine le_antisymm (key f) ?_
  have h := key (fun x => f (flipAll x))
  have hff : (fun x => f (flipAll (flipAll x))) = f := by
    funext x
    congr 1
    funext i
    simp [flipAll]
  rwa [hff] at h

/-- Transport of a dual solution along input negation. -/
def DualPair.compFlipAll {K : Type*} [Fintype K] {f : (ι → Bool) → Bool}
    (P : DualPair K f) : DualPair K (fun x => f (flipAll x)) where
  u x i k := P.u (flipAll x) i k
  v x i k := P.v (flipAll x) i k
  constraint x y := by
    rw [← P.constraint (flipAll x) (flipAll y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : x i = y i
    · rw [ite_eq_left hi, ite_eq_left ((flipAll_coord_iff x y i).mpr hi)]
    · rw [ite_eq_right hi, ite_eq_right (fun h => hi ((flipAll_coord_iff x y i).mp h))]

omit [DecidableEq ι] in
theorem advDual_comp_flipAll (f : (ι → Bool) → Bool) :
    advDual (fun x => f (flipAll x)) = advDual f := by
  classical
  have key : ∀ g : (ι → Bool) → Bool,
      advDual (fun x => g (flipAll x)) ≤ advDual g := by
    intro g
    refine le_csInf (dualCosts_nonempty g) ?_
    rintro c ⟨hc, n, P, hP⟩
    refine advDual_le_of_dualPair P.compFlipAll hc ⟨?_, ?_⟩
    · exact fun x => hP.1 (flipAll x)
    · exact fun x => hP.2 (flipAll x)
  refine le_antisymm (key f) ?_
  have h := key (fun x => f (flipAll x))
  have hff : (fun x => f (flipAll (flipAll x))) = f := by
    funext x
    congr 1
    funext i
    simp [flipAll]
  rwa [hff] at h

theorem HasAdvValue.not {f : (ι → Bool) → Bool} {c : ℝ} (h : HasAdvValue f c) :
    HasAdvValue (fun x => !(f x)) c :=
  ⟨by rw [advPM_not]; exact h.1, by rw [advDual_not]; exact h.2⟩

theorem HasAdvValue.compFlipAll {f : (ι → Bool) → Bool} {c : ℝ}
    (h : HasAdvValue f c) : HasAdvValue (fun x => f (flipAll x)) c :=
  ⟨by rw [advPM_comp_flipAll]; exact h.1,
    by rw [advDual_comp_flipAll]; exact h.2⟩

end Invariance

/-! ## The two-bit OR function -/

/-- The two-bit OR function. -/
def or2 : (Fin 2 → Bool) → Bool := fun x => x 0 || x 1

lemma or2_eq : or2 = fun x => !(and2 (flipAll x)) := by
  funext x
  simp [or2, and2, flipAll]

/-- **`ADV±(OR₂) = √2`, with a matching dual certificate.** -/
theorem hasAdvValue_or2 : HasAdvValue or2 (Real.sqrt 2) := by
  rw [or2_eq]
  exact hasAdvValue_and2.compFlipAll.not

end QuantumQueryComplexity

end SourceAndOr

section SourceDualityMain

/-!
# Strong duality for total-input adversary bounds

The total-input existence theorem specializes `exists_dualPairOn_of_advPMOn_lt`
at the identity read and transports the resulting certificate with
`DualPairOn.toTotal`. The Hahn–Banach separation argument is proved once, in
`SourceDualityMainOn`; the certificate and mask bounds are specialized in
`TotalDualitySpecialization`.

The total-input Gram helpers below remain available for clients of that API.
Weak duality then gives `advDual g = advPM g` for Boolean functions, followed
by the exact block-composition corollaries.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## Rank-one test matrices concentrated on one query position -/

/-- The vector of Gram indices carrying `s` on the `u`-side and `t` on the
`v`-side of the query position `i₀`, and zero elsewhere. -/
def concVec (i₀ : ι) (s t : (ι → σ) → ℝ) : GramIdx ι σ → ℝ :=
  fun z => if z.2.1 = i₀ then (if z.2.2 then t z.1 else s z.1) else 0

omit [Fintype σ] in
lemma gramR_concVec (i₀ : ι) (s t : (ι → σ) → ℝ) (x y : ι → σ) :
    gramR (vecMulVec (concVec i₀ s t) (concVec i₀ s t)) x y
      = if x i₀ = y i₀ then 0 else s x * t y := by
  classical
  rw [gramR_vecMulVec, Finset.sum_eq_single i₀]
  · by_cases h : x i₀ = y i₀ <;> simp [h, concVec]
  · intro i _ hi
    by_cases h : x i = y i <;> simp [h, concVec, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

omit [DecidableEq σ] [Fintype σ] in
lemma gramCost_concVec_false (i₀ : ι) (s t : (ι → σ) → ℝ) (x : ι → σ) :
    gramCost (vecMulVec (concVec i₀ s t) (concVec i₀ s t)) false x = s x * s x := by
  classical
  rw [gramCost_vecMulVec, Finset.sum_eq_single i₀]
  · simp [concVec]
  · intro i _ hi
    simp [concVec, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

omit [DecidableEq σ] [Fintype σ] in
lemma gramCost_concVec_true (i₀ : ι) (s t : (ι → σ) → ℝ) (x : ι → σ) :
    gramCost (vecMulVec (concVec i₀ s t) (concVec i₀ s t)) true x = t x * t x := by
  classical
  rw [gramCost_vecMulVec, Finset.sum_eq_single i₀]
  · simp [concVec]
  · intro i _ hi
    simp [concVec, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

omit [DecidableEq σ] in
lemma sum_sq_concVec (i₀ : ι) (s t : (ι → σ) → ℝ) :
    (∑ z, concVec i₀ s t z * concVec i₀ s t z)
      = (∑ x, s x * s x) + ∑ x, t x * t x := by
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i₀]
  · simp [concVec]
    ring
  · intro i _ hi
    simp [concVec, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

omit [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma concVec_ne_zero_left {i₀ : ι} {s t : (ι → σ) → ℝ} (hs : s ≠ 0) :
    concVec i₀ s t ≠ 0 := by
  intro h
  refine hs (funext fun x => ?_)
  have := congrFun h (x, i₀, false)
  simpa [concVec] using this

omit [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma concVec_ne_zero_right {i₀ : ι} {s t : (ι → σ) → ℝ} (ht : t ≠ 0) :
    concVec i₀ s t ≠ 0 := by
  intro h
  refine ht (funext fun x => ?_)
  have := congrFun h (x, i₀, true)
  simpa [concVec] using this

/-! ## Symmetrising a two-weight certificate -/

/-- The certificate of `lt_advPM_of_certificate` with the two sides carrying
different weights: averaging `Ξ` with its transpose and the two weights with
each other reduces to the symmetric case, because `advD i` and `dualTarget g`
are symmetric. -/
theorem lt_advPM_of_certificate_two {g : (ι → σ) → Bool}
    {Ξ : Matrix (ι → σ) (ι → σ) ℝ} {p q : (ι → σ) → ℝ} {c : ℝ}
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hquad : ∀ (i : ι) (s t : (ι → σ) → ℝ),
      |s ⬝ᵥ (Ξ ⊙ advD i) *ᵥ t|
        ≤ (∑ x, p x * (s x * s x)) + ∑ y, q y * (t y * t y))
    (hobj : c * ((∑ x, p x) + ∑ x, q x)
      < ∑ x, ∑ y, Ξ x y * dualTarget g x y) :
    c < advPM g := by
  exact lt_advPMOn_of_certificate_two (read := id) (f := g)
    (fun _ _ h => congrArg g h) hp hq hquad hobj

/-! ## The separation argument -/

/-- **Strong duality, existence form.**  Above the adversary bound every value
is achieved by a feasible dual solution. -/
theorem exists_dualPair_of_advPM_lt {g : (ι → σ) → Bool} {c : ℝ}
    (hc : advPM g < c) : ∃ (m : ℕ) (P : DualPair (Fin m) g), P.IsCostLe c := by
  obtain ⟨m, P, hP⟩ := exists_dualPairOn_of_advPMOn_lt (read := id) (f := g)
    (fun _ _ h => congrArg g h) hc
  exact ⟨m, P.toTotal, hP⟩

/-! ## Strong duality -/

/-- **Strong duality for the adversary bound.**  The LMRSS dual program has no
gap: its value equals `ADV±`. -/
theorem advDual_eq_advPM {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → Bool) → Bool) : advDual g = advPM g := by
  refine le_antisymm ?_ (advPM_le_advDual g)
  by_contra hlt
  push Not at hlt
  have h1 : advPM g < (advPM g + advDual g) / 2 := by linarith
  have h2 : (advPM g + advDual g) / 2 < advDual g := by linarith
  obtain ⟨m, Q, hQ⟩ := exists_dualPair_of_advPM_lt h1
  have hle : advDual g ≤ (advPM g + advDual g) / 2 :=
    advDual_le_of_dualPair Q (by linarith [advPM_nonneg g]) hQ
  linarith

/-! ## Consequences -/

section Compose

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **Perfect composition**, unconditionally: the adversary bound is exactly
multiplicative under composition. -/
theorem advPM_composeFun_eq (f : (α → Bool) → Bool) (g : (β → Bool) → Bool) :
    advPM (composeFun f g) = advPM f * advPM g :=
  advPM_composeFun_eq_of_dual_eq f g (advDual_eq_advPM f) (advDual_eq_advPM g)

/-- Every Boolean function carries a matching primal/dual pair of witnesses. -/
theorem hasAdvValue_advPM (f : (α → Bool) → Bool) : HasAdvValue f (advPM f) :=
  ⟨rfl, advDual_eq_advPM f⟩

/-- The iterated composition value is exact. -/
theorem advPM_iterFun_eq (f : (α → Bool) → Bool) (d : ℕ) :
    advPM (iterFun f d) = advPM f ^ (d + 1) := by
  induction d with
  | zero => exact (pow_one (advPM f)).symm
  | succ d ih =>
      change advPM (composeFun f (iterFun f d)) = _
      rw [advPM_composeFun_eq, ih]
      ring

end Compose

end QuantumQueryComplexity

end SourceDualityMain

section SourceStar

/-!
# Star adversary matrices

A *star matrix* with centre `c` and leaf set `S` is `∑ z ∈ S, pairMatrix z c`:
the symmetric matrix whose only nonzero entries are the unit weights joining
`c` to each leaf.  Its spectral norm is `√|S|` (`norm_starMatrix`), and
masking it by a difference matrix restricts the leaf set to those leaves
differing from the centre in that coordinate
(`starMatrix_hadamard_advD`).

These are the optimal primal witnesses for `OR` and `AND`, and specialise to
the two-bit case of `SourceAndOr`.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## Generic sum manipulations -/

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma isHermitian_sum {α : Type*} {S : Finset α}
    {M : α → Matrix (ι → σ) (ι → σ) ℝ}
    (h : ∀ a ∈ S, (M a).IsHermitian) : (∑ a ∈ S, M a).IsHermitian := by
  change (∑ a ∈ S, M a)ᴴ = _
  ext x y
  simp only [Matrix.conjTranspose_apply, Matrix.sum_apply, star_trivial]
  exact Finset.sum_congr rfl fun a ha => (isHermitian_apply_symm (h a ha) y x)

omit [DecidableEq σ] in
lemma sum_mulVec {α : Type*} (S : Finset α)
    (M : α → Matrix (ι → σ) (ι → σ) ℝ) (y : (ι → σ) → ℝ) :
    (∑ a ∈ S, M a) *ᵥ y = ∑ a ∈ S, (M a *ᵥ y) := by
  funext w
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_mul _ _ _

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma sum_hadamard {α : Type*} (S : Finset α)
    (M : α → Matrix (ι → σ) (ι → σ) ℝ)
    (D : Matrix (ι → σ) (ι → σ) ℝ) :
    (∑ a ∈ S, M a) ⊙ D = ∑ a ∈ S, (M a ⊙ D) := by
  ext x y
  simp [Matrix.hadamard_apply, Matrix.sum_apply, Finset.sum_mul]

lemma sum_ite_const {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (C : ℝ) :
    (∑ a : α, if p a then C else 0)
      = ((Finset.univ.filter p).card : ℝ) * C := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-! ## The star matrix -/

/-- The star matrix with centre `c` and leaves `S`. -/
noncomputable def starMatrix (S : Finset (ι → σ)) (c : ι → σ) :
    Matrix (ι → σ) (ι → σ) ℝ := ∑ z ∈ S, pairMatrix z c

omit [DecidableEq ι] [Fintype σ] in
lemma starMatrix_isHermitian (S : Finset (ι → σ)) (c : ι → σ) :
    (starMatrix S c).IsHermitian := by
  classical
  exact isHermitian_sum fun z _ => pairMatrix_isHermitian z c

lemma starMatrix_mulVec_apply (S : Finset (ι → σ)) (c : ι → σ)
    (y : (ι → σ) → ℝ) (w : ι → σ) :
    (starMatrix S c *ᵥ y) w
      = (if w ∈ S then y c else 0) + (if c = w then ∑ z ∈ S, y z else 0) := by
  rw [starMatrix, sum_mulVec]
  simp only [Finset.sum_apply, pairMatrix_mulVec]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' S w fun _ => y c]
  congr 1
  by_cases hc : c = w
  · simp [hc]
  · simp [hc]

lemma starMatrix_bilinear {S : Finset (ι → σ)} {c : ι → σ}
    (x y : (ι → σ) → ℝ) :
    x ⬝ᵥ starMatrix S c *ᵥ y
      = (∑ w ∈ S, x w) * y c + x c * ∑ z ∈ S, y z := by
  change (∑ w, x w * (starMatrix S c *ᵥ y) w) = _
  simp only [starMatrix_mulVec_apply, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [show (∑ w : ι → σ, x w * if w ∈ S then y c else 0)
        = ∑ w : ι → σ, if w ∈ S then x w * y c else 0 from
      Finset.sum_congr rfl fun w _ => by by_cases h : w ∈ S <;> simp [h]]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      ← Finset.sum_mul]
  · rw [show (∑ w : ι → σ, x w * if c = w then ∑ z ∈ S, y z else 0)
        = ∑ w : ι → σ, if c = w then x w * ∑ z ∈ S, y z else 0 from
      Finset.sum_congr rfl fun w _ => by by_cases h : c = w <;> simp [h]]
    rw [Finset.sum_ite_eq Finset.univ c fun w => x w * ∑ z ∈ S, y z]
    simp

omit [DecidableEq σ] in
/-- Splitting off the centre and the leaves from a sum over all inputs. -/
lemma sum_sq_ge {S : Finset (ι → σ)} {c : ι → σ} (hc : c ∉ S)
    (x : (ι → σ) → ℝ) :
    (∑ w ∈ S, x w * x w) + x c * x c ≤ x ⬝ᵥ x := by
  classical
  have hsub : (∑ w ∈ insert c S, x w * x w) ≤ ∑ w : ι → σ, x w * x w :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun w _ _ => mul_self_nonneg _
  rw [Finset.sum_insert hc] at hsub
  calc (∑ w ∈ S, x w * x w) + x c * x c
      = x c * x c + ∑ w ∈ S, x w * x w := by ring
    _ ≤ x ⬝ᵥ x := hsub

lemma norm_starMatrix_le {S : Finset (ι → σ)} {c : ι → σ} (hc : c ∉ S) :
    ‖starMatrix S c‖ ≤ Real.sqrt (S.card : ℝ) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [starMatrix]
  refine l2_opNorm_le_of_forall_dotProduct _ (Real.sqrt_nonneg _) fun x y => ?_
  rw [starMatrix_bilinear]
  have hkpos : (0:ℝ) < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have hCSx : (∑ w ∈ S, x w) ^ 2 ≤ (S.card : ℝ) * ∑ w ∈ S, x w * x w := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) x
    simpa [Finset.sum_const, sq] using h
  have hCSy : (∑ z ∈ S, y z) ^ 2 ≤ (S.card : ℝ) * ∑ z ∈ S, y z * y z := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) y
    simpa [Finset.sum_const, sq] using h
  have hx := sum_sq_ge hc x
  have hy := sum_sq_ge hc y
  have h2 : (∑ w ∈ S, x w) ^ 2 + (S.card : ℝ) * (x c) ^ 2
      ≤ (S.card : ℝ) * (x ⬝ᵥ x) := by nlinarith only [hCSx, hx, hkpos.le]
  have h3 : (S.card : ℝ) * (y c) ^ 2 + (∑ z ∈ S, y z) ^ 2
      ≤ (S.card : ℝ) * (y ⬝ᵥ y) := by nlinarith only [hCSy, hy, hkpos.le]
  have h1 : (S.card : ℝ) *
        ((∑ w ∈ S, x w) * y c + x c * ∑ z ∈ S, y z) ^ 2
      ≤ ((∑ w ∈ S, x w) ^ 2 + (S.card : ℝ) * (x c) ^ 2) *
        ((S.card : ℝ) * (y c) ^ 2 + (∑ z ∈ S, y z) ^ 2) := by
    nlinarith only [sq_nonneg ((∑ w ∈ S, x w) * (∑ z ∈ S, y z)
      - (S.card : ℝ) * (x c * y c))]
  have hprod : ((∑ w ∈ S, x w) ^ 2 + (S.card : ℝ) * (x c) ^ 2) *
        ((S.card : ℝ) * (y c) ^ 2 + (∑ z ∈ S, y z) ^ 2)
      ≤ ((S.card : ℝ) * (x ⬝ᵥ x)) * ((S.card : ℝ) * (y ⬝ᵥ y)) :=
    mul_le_mul h2 h3 (by positivity)
      (mul_nonneg hkpos.le (dotProduct_self_nonneg x))
  have hchain : (S.card : ℝ) *
        ((∑ w ∈ S, x w) * y c + x c * ∑ z ∈ S, y z) ^ 2
      ≤ (S.card : ℝ) * ((S.card : ℝ) * (x ⬝ᵥ x) * (y ⬝ᵥ y)) :=
    h1.trans (hprod.trans (le_of_eq (by ring)))
  have hsq : ((∑ w ∈ S, x w) * y c + x c * ∑ z ∈ S, y z) ^ 2
      ≤ (S.card : ℝ) * (x ⬝ᵥ x) * (y ⬝ᵥ y) :=
    le_of_mul_le_mul_left hchain hkpos
  calc |(∑ w ∈ S, x w) * y c + x c * ∑ z ∈ S, y z|
      = Real.sqrt (((∑ w ∈ S, x w) * y c + x c * ∑ z ∈ S, y z) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((S.card : ℝ) * (x ⬝ᵥ x) * (y ⬝ᵥ y)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (S.card : ℝ) * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
        rw [Real.sqrt_mul
            (mul_nonneg hkpos.le (dotProduct_self_nonneg x)),
          Real.sqrt_mul hkpos.le]

/-- The top eigenvector of a star matrix. -/
noncomputable def starVec (S : Finset (ι → σ)) (c : ι → σ) :
    (ι → σ) → ℝ :=
  fun w => if w ∈ S then 1 else if w = c then Real.sqrt (S.card : ℝ) else 0

lemma sqrt_card_le_norm_starMatrix {S : Finset (ι → σ)} {c : ι → σ}
    (hc : c ∉ S) (hS : S.Nonempty) :
    Real.sqrt (S.card : ℝ) ≤ ‖starMatrix S c‖ := by
  set k : ℝ := (S.card : ℝ) with hk
  have hkpos : 0 < k := by
    rw [hk]
    exact_mod_cast Finset.card_pos.mpr hS
  have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hkpos.le
  set v := starVec S c with hv
  have hvc : v c = Real.sqrt k := by
    rw [hv, starVec, ite_eq_right hc, ite_eq_left rfl]
  have hvS : ∀ w ∈ S, v w = 1 := fun w hw => by rw [hv, starVec, ite_eq_left hw]
  have hsum : (∑ w ∈ S, v w) = k := by
    rw [Finset.sum_congr rfl hvS, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hvv : v ⬝ᵥ v = 2 * k := by
    have hzero : ∀ w, w ∉ insert c S → v w * v w = 0 := by
      intro w hw
      rw [Finset.mem_insert] at hw
      push Not at hw
      rw [hv, starVec, ite_eq_right hw.2, ite_eq_right hw.1, mul_zero]
    have h1 : v ⬝ᵥ v = ∑ w ∈ insert c S, v w * v w :=
      (Finset.sum_subset (Finset.subset_univ _) fun w _ hw => hzero w hw).symm
    rw [h1, Finset.sum_insert hc, hvc, hsk,
      Finset.sum_congr rfl (fun w hw => by rw [hvS w hw, mul_one]),
      Finset.sum_const, nsmul_eq_mul, mul_one, ← hk]
    ring
  have h := abs_dotProduct_mulVec_le (starMatrix S c) v v
  rw [starMatrix_bilinear, hsum, hvc, hvv] at h
  have habs : |k * Real.sqrt k + Real.sqrt k * k| = 2 * k * Real.sqrt k := by
    rw [abs_of_nonneg (by positivity)]
    ring
  have h2k : Real.sqrt (2 * k) * Real.sqrt (2 * k) = 2 * k :=
    Real.mul_self_sqrt (by positivity)
  rw [habs] at h
  nlinarith [h, h2k, hkpos, Real.sqrt_nonneg k]

theorem norm_starMatrix {S : Finset (ι → σ)} {c : ι → σ} (hc : c ∉ S)
    (hS : S.Nonempty) : ‖starMatrix S c‖ = Real.sqrt (S.card : ℝ) :=
  le_antisymm (norm_starMatrix_le hc) (sqrt_card_le_norm_starMatrix hc hS)

omit [DecidableEq ι] [Fintype σ] in
lemma starMatrix_hadamard_advD (S : Finset (ι → σ)) (c : ι → σ)
    (i : ι) :
    starMatrix S c ⊙ advD i
      = starMatrix (S.filter fun z => ¬(z i = c i)) c := by
  classical
  rw [starMatrix, sum_hadamard,
    Finset.sum_congr rfl fun z (_ : z ∈ S) => pairMatrix_hadamard_advD z c i,
    starMatrix, Finset.sum_filter]
  exact Finset.sum_congr rfl fun z _ => by
    by_cases h : z i = c i <;> simp [h]

/-! ## Weighted star matrices

Giving the edges weights `w` replaces the leaf count `|S|` by the total
squared weight `∑ w²`.  This is what the *cost* version of the adversary
bound needs: for `OR_k` with costs `c`, the weighted star with `w = c`
certifies the value `√(∑ cᵢ²)` with masked norms `cᵢ`.
-/

/-- The star matrix with centre `c`, leaves `S` and edge weights `w`. -/
noncomputable def wStarMatrix (S : Finset (ι → σ)) (c : ι → σ)
    (w : (ι → σ) → ℝ) : Matrix (ι → σ) (ι → σ) ℝ :=
  ∑ z ∈ S, w z • pairMatrix z c

/-- The total squared weight of a star. -/
def starWeight (S : Finset (ι → σ)) (w : (ι → σ) → ℝ) : ℝ :=
  ∑ z ∈ S, w z * w z

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma starWeight_nonneg (S : Finset (ι → σ)) (w : (ι → σ) → ℝ) :
    0 ≤ starWeight S w :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

omit [DecidableEq ι] [Fintype σ] in
lemma wStarMatrix_isHermitian (S : Finset (ι → σ)) (c : ι → σ)
    (w : (ι → σ) → ℝ) : (wStarMatrix S c w).IsHermitian := by
  classical
  exact isHermitian_sum fun z _ =>
      (pairMatrix_isHermitian z c).smul (star_trivial (w z))

lemma wStarMatrix_mulVec_apply (S : Finset (ι → σ)) (c : ι → σ)
    (w : (ι → σ) → ℝ) (y : (ι → σ) → ℝ) (v : ι → σ) :
    (wStarMatrix S c w *ᵥ y) v
      = (if v ∈ S then w v * y c else 0)
        + (if c = v then ∑ z ∈ S, w z * y z else 0) := by
  rw [wStarMatrix, sum_mulVec]
  simp only [Finset.sum_apply, Matrix.smul_mulVec, pairMatrix_mulVec,
    Pi.smul_apply, smul_eq_mul]
  rw [show (∑ z ∈ S, w z * ((if z = v then y c else 0)
        + (if c = v then y z else 0)))
      = (∑ z ∈ S, if z = v then w z * y c else 0)
        + ∑ z ∈ S, (if c = v then w z * y z else 0) from by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by
      by_cases h1 : z = v <;> by_cases h2 : c = v <;> simp [h1, h2]; ring]
  rw [Finset.sum_ite_eq' S v fun z => w z * y c]
  congr 1
  by_cases hcv : c = v
  · simp [hcv]
  · simp [hcv]

lemma wStarMatrix_bilinear {S : Finset (ι → σ)} {c : ι → σ}
    (w : (ι → σ) → ℝ) (x y : (ι → σ) → ℝ) :
    x ⬝ᵥ wStarMatrix S c w *ᵥ y
      = (∑ z ∈ S, w z * x z) * y c + x c * ∑ z ∈ S, w z * y z := by
  change (∑ v, x v * (wStarMatrix S c w *ᵥ y) v) = _
  simp only [wStarMatrix_mulVec_apply, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [show (∑ v : ι → σ, x v * if v ∈ S then w v * y c else 0)
        = ∑ v : ι → σ, if v ∈ S then (w v * x v) * y c else 0 from
      Finset.sum_congr rfl fun v _ => by
        by_cases h : v ∈ S <;> simp [h]; ring]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      ← Finset.sum_mul]
  · rw [show (∑ v : ι → σ, x v * if c = v then ∑ z ∈ S, w z * y z else 0)
        = ∑ v : ι → σ, if c = v then x v * ∑ z ∈ S, w z * y z else 0 from
      Finset.sum_congr rfl fun v _ => by by_cases h : c = v <;> simp [h]]
    rw [Finset.sum_ite_eq Finset.univ c fun v => x v * ∑ z ∈ S, w z * y z]
    simp

lemma norm_wStarMatrix_le {S : Finset (ι → σ)} {c : ι → σ} (hc : c ∉ S)
    (w : (ι → σ) → ℝ) :
    ‖wStarMatrix S c w‖ ≤ Real.sqrt (starWeight S w) := by
  rcases eq_or_lt_of_le (starWeight_nonneg S w) with hW | hWpos
  · have hzero : ∀ z ∈ S, w z = 0 := by
      intro z hz
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (fun z _ => mul_self_nonneg (w z))).mp hW.symm z hz
      exact mul_self_eq_zero.mp h
    have h0 : wStarMatrix S c w = 0 :=
      Finset.sum_eq_zero fun z hz => by rw [hzero z hz, zero_smul]
    rw [h0, norm_zero, ← hW, Real.sqrt_zero]
  refine l2_opNorm_le_of_forall_dotProduct _ (Real.sqrt_nonneg _) fun x y => ?_
  rw [wStarMatrix_bilinear]
  have hCSx : (∑ z ∈ S, w z * x z) ^ 2
      ≤ starWeight S w * ∑ z ∈ S, x z * x z := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S w x
    simpa [starWeight, sq] using h
  have hCSy : (∑ z ∈ S, w z * y z) ^ 2
      ≤ starWeight S w * ∑ z ∈ S, y z * y z := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S w y
    simpa [starWeight, sq] using h
  have hx := sum_sq_ge hc x
  have hy := sum_sq_ge hc y
  have h2 : (∑ z ∈ S, w z * x z) ^ 2 + starWeight S w * (x c) ^ 2
      ≤ starWeight S w * (x ⬝ᵥ x) := by nlinarith only [hCSx, hx, hWpos.le]
  have h3 : starWeight S w * (y c) ^ 2 + (∑ z ∈ S, w z * y z) ^ 2
      ≤ starWeight S w * (y ⬝ᵥ y) := by nlinarith only [hCSy, hy, hWpos.le]
  have h1 : starWeight S w *
        ((∑ z ∈ S, w z * x z) * y c + x c * ∑ z ∈ S, w z * y z) ^ 2
      ≤ ((∑ z ∈ S, w z * x z) ^ 2 + starWeight S w * (x c) ^ 2) *
        (starWeight S w * (y c) ^ 2 + (∑ z ∈ S, w z * y z) ^ 2) := by
    nlinarith only [sq_nonneg ((∑ z ∈ S, w z * x z) * (∑ z ∈ S, w z * y z)
      - starWeight S w * (x c * y c))]
  have hprod : ((∑ z ∈ S, w z * x z) ^ 2 + starWeight S w * (x c) ^ 2) *
        (starWeight S w * (y c) ^ 2 + (∑ z ∈ S, w z * y z) ^ 2)
      ≤ (starWeight S w * (x ⬝ᵥ x)) * (starWeight S w * (y ⬝ᵥ y)) :=
    mul_le_mul h2 h3 (by positivity)
      (mul_nonneg hWpos.le (dotProduct_self_nonneg x))
  have hchain : starWeight S w *
        ((∑ z ∈ S, w z * x z) * y c + x c * ∑ z ∈ S, w z * y z) ^ 2
      ≤ starWeight S w * (starWeight S w * (x ⬝ᵥ x) * (y ⬝ᵥ y)) :=
    h1.trans (hprod.trans (le_of_eq (by ring)))
  have hsq : ((∑ z ∈ S, w z * x z) * y c + x c * ∑ z ∈ S, w z * y z) ^ 2
      ≤ starWeight S w * (x ⬝ᵥ x) * (y ⬝ᵥ y) :=
    le_of_mul_le_mul_left hchain hWpos
  calc |(∑ z ∈ S, w z * x z) * y c + x c * ∑ z ∈ S, w z * y z|
      = Real.sqrt (((∑ z ∈ S, w z * x z) * y c
          + x c * ∑ z ∈ S, w z * y z) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (starWeight S w * (x ⬝ᵥ x) * (y ⬝ᵥ y)) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (starWeight S w) * Real.sqrt (x ⬝ᵥ x) *
          Real.sqrt (y ⬝ᵥ y) := by
        rw [Real.sqrt_mul
            (mul_nonneg hWpos.le (dotProduct_self_nonneg x)),
          Real.sqrt_mul hWpos.le]

/-- The top eigenvector of a weighted star matrix. -/
noncomputable def wStarVec (S : Finset (ι → σ)) (c : ι → σ)
    (w : (ι → σ) → ℝ) : (ι → σ) → ℝ :=
  fun v => if v ∈ S then w v
    else if v = c then Real.sqrt (starWeight S w) else 0

lemma sqrt_starWeight_le_norm_wStarMatrix {S : Finset (ι → σ)}
    {c : ι → σ} (hc : c ∉ S) {w : (ι → σ) → ℝ}
    (hW : 0 < starWeight S w) :
    Real.sqrt (starWeight S w) ≤ ‖wStarMatrix S c w‖ := by
  set W : ℝ := starWeight S w with hWdef
  have hsW : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt hW.le
  set v := wStarVec S c w with hv
  have hvc : v c = Real.sqrt W := by
    rw [hv, wStarVec, ite_eq_right hc, ite_eq_left rfl]
  have hvS : ∀ z ∈ S, v z = w z := fun z hz => by rw [hv, wStarVec, ite_eq_left hz]
  have hsum : (∑ z ∈ S, w z * v z) = W := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hvS z hz]]
    exact hWdef.symm
  have hvv : v ⬝ᵥ v = 2 * W := by
    have hzero : ∀ u, u ∉ insert c S → v u * v u = 0 := by
      intro u hu
      rw [Finset.mem_insert] at hu
      push Not at hu
      rw [hv, wStarVec, ite_eq_right hu.2, ite_eq_right hu.1, mul_zero]
    have h1 : v ⬝ᵥ v = ∑ u ∈ insert c S, v u * v u :=
      (Finset.sum_subset (Finset.subset_univ _) fun u _ hu => hzero u hu).symm
    rw [h1, Finset.sum_insert hc, hvc, hsW,
      Finset.sum_congr rfl (fun z hz => by rw [hvS z hz]),
      show (∑ z ∈ S, w z * w z) = W from hWdef.symm]
    ring
  have h := abs_dotProduct_mulVec_le (wStarMatrix S c w) v v
  rw [wStarMatrix_bilinear, hsum, hvc, hvv] at h
  have habs : |W * Real.sqrt W + Real.sqrt W * W| = 2 * W * Real.sqrt W := by
    rw [abs_of_nonneg (by positivity)]
    ring
  have h2W : Real.sqrt (2 * W) * Real.sqrt (2 * W) = 2 * W :=
    Real.mul_self_sqrt (by positivity)
  rw [habs] at h
  nlinarith [h, h2W, hW, Real.sqrt_nonneg W]

theorem norm_wStarMatrix {S : Finset (ι → σ)} {c : ι → σ} (hc : c ∉ S)
    {w : (ι → σ) → ℝ} (hW : 0 < starWeight S w) :
    ‖wStarMatrix S c w‖ = Real.sqrt (starWeight S w) :=
  le_antisymm (norm_wStarMatrix_le hc w) (sqrt_starWeight_le_norm_wStarMatrix hc hW)

omit [DecidableEq ι] [Fintype σ] in
lemma wStarMatrix_hadamard_advD (S : Finset (ι → σ)) (c : ι → σ)
    (w : (ι → σ) → ℝ) (i : ι) :
    wStarMatrix S c w ⊙ advD i
      = wStarMatrix (S.filter fun z => ¬(z i = c i)) c w := by
  classical
  rw [wStarMatrix, sum_hadamard]
  rw [Finset.sum_congr rfl fun z (_ : z ∈ S) => by
    rw [Matrix.smul_hadamard, pairMatrix_hadamard_advD z c i]]
  rw [wStarMatrix, Finset.sum_filter]
  exact Finset.sum_congr rfl fun z _ => by
    by_cases h : z i = c i <;> simp [h]

end QuantumQueryComplexity

end SourceStar

section SourceOrAnd

/-!
# `ADV±(OR_n) = ADV±(AND_n) = √n`

We compute the adversary bound of the `n`-bit OR and AND functions, with
matching dual certificates, so strong duality holds at them and they compose
perfectly.

* the primal witness for `OR_n` is the star matrix centred at the all-zero
  input with the `n` weight-one inputs as leaves (`SourceStar`);
  its norm is `√n` and each masked norm is `1`;
* the dual witness is one-dimensional: weight `δ = n^(-1/4)` at the all-zero
  input, and `1/(|x| δ)` on the support of each nonzero `x`, where `|x|` is
  the Hamming weight.  Its cost is exactly `√n`.

`AND_n` follows from `OR_n` by De Morgan, using the relabelling invariance
lemmas of `SourceAndOr`.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The `n`-bit OR function -/

/-- The all-zero input. -/
@[expose]
def zeroVec : ι → Bool := fun _ => false

/-- The input with a single `true` in position `i`. -/
@[expose]
def unitVec (i : ι) : ι → Bool := fun j => decide (j = i)

/-- The `n`-bit OR function. -/
def orN (x : ι → Bool) : Bool := decide (∃ i, x i = true)

/-- The `n`-bit AND function. -/
def andN (x : ι → Bool) : Bool := decide (∀ i, x i = true)

omit [Fintype ι] in
@[simp] lemma unitVec_apply (i j : ι) : unitVec i j = decide (j = i) := rfl

omit [DecidableEq ι] [Fintype ι] in
@[simp] lemma zeroVec_apply (j : ι) : (zeroVec : ι → Bool) j = false := rfl

omit [DecidableEq ι] in
lemma orN_eq_false_iff {x : ι → Bool} : orN x = false ↔ x = zeroVec := by
  simp only [orN, decide_eq_false_iff_not, not_exists]
  constructor
  · intro h
    funext j
    simpa using h j
  · rintro rfl j
    simp

omit [DecidableEq ι] in
lemma orN_eq_true_iff {x : ι → Bool} : orN x = true ↔ x ≠ zeroVec := by
  classical
  constructor
  · intro h hz
    rw [orN_eq_false_iff.mpr hz] at h
    exact Bool.noConfusion h
  · intro h
    rcases Bool.eq_false_or_eq_true (orN x) with h' | h'
    · exact h'
    · exact absurd (orN_eq_false_iff.mp h') h

omit [DecidableEq ι] in
lemma orN_zeroVec : orN (zeroVec : ι → Bool) = false := by
  classical
  exact orN_eq_false_iff.mpr rfl

lemma orN_unitVec (i : ι) : orN (unitVec i) = true :=
  orN_eq_true_iff.mpr fun h => by
    have := congrFun h i
    simp at this

omit [Fintype ι] in
lemma unitVec_injective : Function.Injective (unitVec : ι → (ι → Bool)) := by
  intro i j h
  have := congrFun h i
  simpa using this.symm

/-- The leaf set of the `OR` star matrix. -/
noncomputable def unitSet : Finset (ι → Bool) := Finset.univ.image unitVec

lemma mem_unitSet {z : ι → Bool} : z ∈ (unitSet : Finset (ι → Bool)) ↔
    ∃ i, unitVec i = z := by
  simp [unitSet]

lemma card_unitSet : (unitSet : Finset (ι → Bool)).card = Fintype.card ι := by
  rw [unitSet, Finset.card_image_of_injective Finset.univ unitVec_injective,
    Finset.card_univ]

lemma zeroVec_notMem_unitSet : (zeroVec : ι → Bool) ∉ unitSet := by
  rw [mem_unitSet]
  rintro ⟨i, hi⟩
  have := congrFun hi i
  simp at this

/-! ## The primal witness -/

lemma orN_isAdvMatrix :
    IsAdvMatrix (orN : (ι → Bool) → Bool) (starMatrix unitSet zeroVec) := by
  refine ⟨starMatrix_isHermitian _ _, fun x y hxy => ?_⟩
  rw [starMatrix, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun z hz => ?_
  obtain ⟨i, rfl⟩ := mem_unitSet.mp hz
  refine pairMatrix_apply_eq_zero ?_ ?_
  · rintro ⟨rfl, rfl⟩
    rw [orN_unitVec, orN_zeroVec] at hxy
    exact Bool.noConfusion hxy
  · rintro ⟨rfl, rfl⟩
    rw [orN_unitVec, orN_zeroVec] at hxy
    exact Bool.noConfusion hxy

lemma unitSet_filter (j : ι) :
    ((unitSet : Finset (ι → Bool)).filter
      fun z => ¬(z j = (zeroVec : ι → Bool) j)) = {unitVec j} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨mem_unitSet.mpr ⟨j, rfl⟩, ?_⟩
    rw [zeroVec_apply, unitVec_apply]
    simp
  · intro z hz
    obtain ⟨hzu, hzj⟩ := Finset.mem_filter.mp hz
    obtain ⟨i, rfl⟩ := mem_unitSet.mp hzu
    rw [zeroVec_apply, unitVec_apply] at hzj
    have hij : j = i := by
      by_contra hne
      exact hzj (by simp [hne])
    rw [hij]

lemma orN_feasible (j : ι) :
    ‖starMatrix (unitSet : Finset (ι → Bool)) zeroVec ⊙ advD j‖ ≤ 1 := by
  rw [starMatrix_hadamard_advD, unitSet_filter, starMatrix, Finset.sum_singleton,
    norm_pairMatrix]
  intro h
  have := congrFun h j
  simp at this

theorem sqrt_card_le_advPM_orN :
    Real.sqrt (Fintype.card ι : ℝ) ≤ advPM (orN : (ι → Bool) → Bool) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : Fintype.card ι = 0 := Fintype.card_eq_zero
    rw [this]
    simpa using advPM_nonneg (orN : (ι → Bool) → Bool)
  · have hne : (unitSet : Finset (ι → Bool)).Nonempty := by
      obtain ⟨i⟩ := hι
      exact ⟨unitVec i, mem_unitSet.mpr ⟨i, rfl⟩⟩
    have h := le_advPM (Γ := starMatrix (unitSet : Finset (ι → Bool)) zeroVec)
      orN_isAdvMatrix orN_feasible
    rwa [norm_starMatrix zeroVec_notMem_unitSet hne, card_unitSet] at h

/-! ## The dual witness -/

/-- The Hamming weight of an input. -/
def supportCard (x : ι → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i = true).card

omit [DecidableEq ι] in
lemma supportCard_pos {x : ι → Bool} (hx : x ≠ zeroVec) : 0 < supportCard x := by
  rw [supportCard, Finset.card_pos]
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
  exact hx (funext fun i => by simpa using h (Finset.mem_univ i))

/-- `δ = n^(-1/4)`. -/
noncomputable def orNDelta (ι : Type*) [Fintype ι] : ℝ :=
  (Real.sqrt (Real.sqrt (Fintype.card ι : ℝ)))⁻¹

omit [DecidableEq ι] in
lemma orNDelta_pos [Nonempty ι] : 0 < orNDelta ι := by
  rw [orNDelta, inv_pos]
  refine Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ?_)
  exact_mod_cast Fintype.card_pos

omit [DecidableEq ι] in
lemma orNDelta_ne_zero [Nonempty ι] : orNDelta ι ≠ 0 := by
  classical
  exact ne_of_gt orNDelta_pos

omit [DecidableEq ι] in
/-- `δ² = 1/√n`. -/
lemma orNDelta_sq :
    orNDelta ι * orNDelta ι = 1 / Real.sqrt (Fintype.card ι : ℝ) := by
  have hn : (0:ℝ) ≤ Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_nonneg _
  rw [orNDelta, ← mul_inv, Real.mul_self_sqrt hn, one_div]

omit [DecidableEq ι] in
/-- `n δ² = √n`. -/
lemma card_mul_orNDelta_sq [Nonempty ι] :
    (Fintype.card ι : ℝ) * (orNDelta ι * orNDelta ι)
      = Real.sqrt (Fintype.card ι : ℝ) := by
  classical
  have hpos : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ)
      = (Fintype.card ι : ℝ) := Real.mul_self_sqrt hpos.le
  have hsp : (0:ℝ) < Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_pos.mpr hpos
  rw [orNDelta_sq]
  field_simp
  linarith [hs]

/-- The one-dimensional dual weights for `OR_n`. -/
noncomputable def orNDualVec (x : ι → Bool) (i : ι) : ℝ :=
  if x = zeroVec then orNDelta ι
  else if x i then 1 / ((supportCard x : ℝ) * orNDelta ι) else 0

/-- The dual solution for `OR_n`. -/
noncomputable def orNDual [Nonempty ι] : DualPair Unit (orN : (ι → Bool) → Bool) where
  u x i _ := orNDualVec x i
  v x i _ := orNDualVec x i
  constraint x y := by
    have hδ : orNDelta ι ≠ 0 := orNDelta_ne_zero
    by_cases hx : x = zeroVec <;> by_cases hy : y = zeroVec
    · subst hx; subst hy
      rw [ite_eq_left rfl]
      exact Finset.sum_eq_zero fun i _ => ite_eq_left rfl
    · -- `x = 0`, `y ≠ 0`: the sum is `|y| δ γ_y = 1`
      subst hx
      rw [ite_eq_right (by rw [orN_zeroVec, orN_eq_true_iff.mpr hy]; exact Bool.noConfusion)]
      have hstep : ∀ i : ι,
          (if (zeroVec : ι → Bool) i = y i then (0:ℝ)
            else ∑ _k : Unit, orNDualVec zeroVec i * orNDualVec y i)
          = if y i = true then
              orNDelta ι * (1 / ((supportCard y : ℝ) * orNDelta ι)) else 0 := by
        intro i
        by_cases hyi : y i = true
        · rw [ite_eq_right (by rw [zeroVec_apply, hyi]; exact Bool.noConfusion),
            ite_eq_left hyi]
          simp [orNDualVec, hy, hyi]
        · simp only [Bool.not_eq_true] at hyi
          rw [ite_eq_left (by rw [zeroVec_apply, hyi]), ite_eq_right (by simp [hyi])]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
        sum_ite_const]
      have hcard : ((Finset.univ.filter fun i : ι => y i = true).card : ℝ)
          = (supportCard y : ℝ) := rfl
      rw [hcard]
      have hpos : (0:ℝ) < (supportCard y : ℝ) := by
        exact_mod_cast supportCard_pos hy
      field_simp
    · -- `x ≠ 0`, `y = 0`: symmetric
      subst hy
      rw [ite_eq_right (by rw [orN_zeroVec, orN_eq_true_iff.mpr hx]; simp)]
      have hstep : ∀ i : ι,
          (if x i = (zeroVec : ι → Bool) i then (0:ℝ)
            else ∑ _k : Unit, orNDualVec x i * orNDualVec zeroVec i)
          = if x i = true then
              (1 / ((supportCard x : ℝ) * orNDelta ι)) * orNDelta ι else 0 := by
        intro i
        by_cases hxi : x i = true
        · rw [ite_eq_right (by rw [zeroVec_apply, hxi]; exact Bool.noConfusion),
            ite_eq_left hxi]
          simp [orNDualVec, hx, hxi]
        · simp only [Bool.not_eq_true] at hxi
          rw [ite_eq_left (by rw [zeroVec_apply, hxi]), ite_eq_right (by simp [hxi])]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
        sum_ite_const]
      have hcard : ((Finset.univ.filter fun i : ι => x i = true).card : ℝ)
          = (supportCard x : ℝ) := rfl
      rw [hcard]
      have hpos : (0:ℝ) < (supportCard x : ℝ) := by
        exact_mod_cast supportCard_pos hx
      field_simp
    · -- both nonzero: every differing coordinate kills one of the two factors
      rw [ite_eq_left (by rw [orN_eq_true_iff.mpr hx, orN_eq_true_iff.mpr hy])]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : x i = y i
      · rw [ite_eq_left hi]
      · rw [ite_eq_right hi]
        have hzero : orNDualVec x i * orNDualVec y i = 0 := by
          rcases Bool.eq_false_or_eq_true (x i) with hxi | hxi
          · have hyi : y i = false := by
              rcases Bool.eq_false_or_eq_true (y i) with h | h
              · exact absurd (hxi.trans h.symm) hi
              · exact h
            have h0 : orNDualVec y i = 0 := by
              rw [orNDualVec, ite_eq_right hy, ite_eq_right (by simp [hyi] : ¬(y i = true))]
            rw [h0, mul_zero]
          · have h0 : orNDualVec x i = 0 := by
              rw [orNDualVec, ite_eq_right hx, ite_eq_right (by simp [hxi] : ¬(x i = true))]
            rw [h0, zero_mul]
        simpa using hzero

omit [DecidableEq ι] in
lemma orNDual_isCostLe [Nonempty ι] :
    (orNDual (ι := ι)).IsCostLe (Real.sqrt (Fintype.card ι : ℝ)) := by
  have hδ : orNDelta ι ≠ 0 := orNDelta_ne_zero
  have hn : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ)
      = (Fintype.card ι : ℝ) := Real.mul_self_sqrt hn.le
  have key : ∀ x : ι → Bool,
      (∑ i : ι, ∑ _k : Unit, orNDualVec x i * orNDualVec x i)
        ≤ Real.sqrt (Fintype.card ι : ℝ) := by
    intro x
    by_cases hx : x = zeroVec
    · subst hx
      have : (∑ i : ι, ∑ _k : Unit,
          orNDualVec (zeroVec : ι → Bool) i * orNDualVec zeroVec i)
          = (Fintype.card ι : ℝ) * (orNDelta ι * orNDelta ι) := by
        simp [orNDualVec, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [this, card_mul_orNDelta_sq]
    · have hpos : (0:ℝ) < (supportCard x : ℝ) := by
        exact_mod_cast supportCard_pos hx
      have hstep : ∀ i : ι,
          (∑ _k : Unit, orNDualVec x i * orNDualVec x i)
          = if x i = true then
              (1 / ((supportCard x : ℝ) * orNDelta ι)) *
              (1 / ((supportCard x : ℝ) * orNDelta ι)) else 0 := by
        intro i
        by_cases hxi : x i = true
        · rw [ite_eq_left hxi]
          simp [orNDualVec, hx, hxi]
        · simp only [Bool.not_eq_true] at hxi
          rw [ite_eq_right (by simp [hxi])]
          simp [orNDualVec, hx, hxi]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
        sum_ite_const]
      have hcard : ((Finset.univ.filter fun i : ι => x i = true).card : ℝ)
          = (supportCard x : ℝ) := rfl
      rw [hcard]
      -- the value is `1 / (|x| δ²) ≤ 1 / δ² = √n`
      have hval : (supportCard x : ℝ) *
          ((1 / ((supportCard x : ℝ) * orNDelta ι)) *
            (1 / ((supportCard x : ℝ) * orNDelta ι)))
          = Real.sqrt (Fintype.card ι : ℝ) / (supportCard x : ℝ) := by
        rw [orNDelta] at *
        field_simp
        nlinarith [hs, Real.sq_sqrt (Real.sqrt_nonneg (Fintype.card ι : ℝ)),
          Real.sqrt_nonneg (Fintype.card ι : ℝ),
          Real.mul_self_sqrt (Real.sqrt_nonneg (Fintype.card ι : ℝ))]
      rw [hval]
      have hone : (1:ℝ) ≤ (supportCard x : ℝ) := by
        exact_mod_cast supportCard_pos hx
      rw [div_le_iff₀ hpos]
      nlinarith [Real.sqrt_nonneg (Fintype.card ι : ℝ), hone]
  exact ⟨key, key⟩

omit [DecidableEq ι] in
theorem advDual_orN_le [Nonempty ι] :
    advDual (orN : (ι → Bool) → Bool) ≤ Real.sqrt (Fintype.card ι : ℝ) := by
  classical
  exact advDual_le_of_dualPair orNDual (Real.sqrt_nonneg _) orNDual_isCostLe

/-- **`ADV±(OR_n) = √n`, with a matching dual certificate.** -/
theorem hasAdvValue_orN :
    HasAdvValue (orN : (ι → Bool) → Bool) (Real.sqrt (Fintype.card ι : ℝ)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hcard : Fintype.card ι = 0 := Fintype.card_eq_zero
    have hconst : ∀ x y : ι → Bool, orN x = orN y := by
      intro x y
      have hx : x = zeroVec := funext fun i => (hι.false i).elim
      have hy : y = zeroVec := funext fun i => (hι.false i).elim
      rw [hx, hy]
    refine ⟨?_, ?_⟩
    · rw [hcard]
      simpa using advPM_eq_zero_of_forall_eq hconst
    · refine le_antisymm ?_ ?_
      · refine advDual_le_of_dualPair
          (K := Unit) ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun x y => ?_⟩
          (by rw [hcard]; simp) ⟨fun x => by rw [hcard]; simp, fun x => by
            rw [hcard]; simp⟩
        rw [ite_eq_left (hconst x y)]
        exact Finset.sum_eq_zero fun i _ => by simp
      · rw [hcard]
        simpa using advDual_nonneg (orN : (ι → Bool) → Bool)
  · exact hasAdvValue_of_le sqrt_card_le_advPM_orN advDual_orN_le

/-! ## The `n`-bit AND function -/

omit [DecidableEq ι] in
lemma andN_eq : (andN : (ι → Bool) → Bool) = fun x => !(orN (flipAll x)) := by
  classical
  funext x
  show andN x = !(orN (flipAll x))
  rw [andN, orN]
  by_cases h : ∀ i, x i = true
  · have hne : ¬ ∃ i, (flipAll x : ι → Bool) i = true := by
      rintro ⟨i, hi⟩
      rw [flipAll_apply, h i] at hi
      exact Bool.noConfusion hi
    rw [decide_eq_true h, decide_eq_false hne, Bool.not_false]
  · have hex : ∃ i, (flipAll x : ι → Bool) i = true := by
      by_contra hc
      push Not at hc
      refine h fun i => ?_
      have hi := hc i
      rw [flipAll_apply] at hi
      simpa using hi
    rw [decide_eq_false h, decide_eq_true hex, Bool.not_true]

/-- **`ADV±(AND_n) = √n`, with a matching dual certificate.** -/
theorem hasAdvValue_andN :
    HasAdvValue (andN : (ι → Bool) → Bool) (Real.sqrt (Fintype.card ι : ℝ)) := by
  rw [andN_eq]
  exact hasAdvValue_orN.compFlipAll.not

end QuantumQueryComplexity

end SourceOrAnd

section SourceWeightedOr

/-!
# The weighted `OR` witness and weighted `OR`-composition

The weighted star centred at the all-zero input, with weight `c i` on the
edge to the `i`-th unit input, is the optimal cost-`c` witness for `OR_n`:
its norm is `√(∑ cᵢ²)` and its `i`-th masked norm is `cᵢ`
(`norm_orWStar`, `norm_orWStar_hadamard`).

Feeding it into the weighted composition theorem gives the key inductive step
for read-once formulas:

  `ADV±(OR_k ∘ (g₁, …, g_k)) ≥ √(∑ᵢ ADV±(gᵢ)²)`

(`sqrt_sum_sq_le_advPM_composeFunFam_orN`), and the same for `AND_k` by
De Morgan.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight function attaching `c i` to the `i`-th unit input. -/
def wOf (c : ι → ℝ) (z : ι → Bool) : ℝ := ∑ i, if z i then c i else 0

lemma wOf_unitVec (c : ι → ℝ) (i : ι) : wOf c (unitVec i) = c i := by
  rw [wOf, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [unitVec_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The weighted star witness for `OR_n` with costs `c`. -/
noncomputable def orWStar (c : ι → ℝ) : Matrix (ι → Bool) (ι → Bool) ℝ :=
  wStarMatrix unitSet zeroVec (wOf c)

lemma orWStar_isHermitian (c : ι → ℝ) : (orWStar c).IsHermitian :=
  wStarMatrix_isHermitian _ _ _

lemma starWeight_unitSet (c : ι → ℝ) :
    starWeight (unitSet : Finset (ι → Bool)) (wOf c) = ∑ i, c i * c i := by
  rw [starWeight, unitSet,
    Finset.sum_image fun i _ j _ h => unitVec_injective h]
  exact Finset.sum_congr rfl fun i _ => by rw [wOf_unitVec]

lemma orWStar_isAdvMatrix (c : ι → ℝ) :
    IsAdvMatrix (orN : (ι → Bool) → Bool) (orWStar c) := by
  refine ⟨wStarMatrix_isHermitian _ _ _, fun x y hxy => ?_⟩
  rw [orWStar, wStarMatrix, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun z hz => ?_
  obtain ⟨i, rfl⟩ := mem_unitSet.mp hz
  rw [Matrix.smul_apply, smul_eq_mul]
  refine mul_eq_zero_of_right _ (pairMatrix_apply_eq_zero ?_ ?_)
  · rintro ⟨rfl, rfl⟩
    rw [orN_unitVec, orN_zeroVec] at hxy
    exact Bool.noConfusion hxy
  · rintro ⟨rfl, rfl⟩
    rw [orN_unitVec, orN_zeroVec] at hxy
    exact Bool.noConfusion hxy

theorem norm_orWStar {c : ι → ℝ} (hc : 0 < ∑ i, c i * c i) :
    ‖orWStar c‖ = Real.sqrt (∑ i, c i * c i) := by
  rw [orWStar, norm_wStarMatrix zeroVec_notMem_unitSet
    (by rw [starWeight_unitSet]; exact hc), starWeight_unitSet]

theorem norm_orWStar_hadamard (c : ι → ℝ) (j : ι) :
    ‖orWStar c ⊙ advD j‖ = |c j| := by
  rw [orWStar, wStarMatrix_hadamard_advD, unitSet_filter, wStarMatrix,
    Finset.sum_singleton, norm_smul, Real.norm_eq_abs, wOf_unitVec,
    norm_pairMatrix, mul_one]
  intro h
  have := congrFun h j
  simp at this

/-- **The weighted `OR`-composition lower bound.**  Composing `OR_k` with
inner functions certified by witnesses `M i` gives at least
`√(∑ᵢ ‖M i‖²)`. -/
theorem sqrt_sum_sq_le_advPM_composeFunFam_orN {β : Type*} [Fintype β]
    [DecidableEq β] {g : ι → (β → Bool) → Bool}
    {M : ι → Matrix (β → Bool) (β → Bool) ℝ}
    (hM : ∀ i, IsAdvMatrix (g i) (M i))
    (hMfeas : ∀ i q, ‖M i ⊙ advD q‖ ≤ 1) (hMpos : ∀ i, 0 < ‖M i‖)
    [Nonempty ι] :
    Real.sqrt (∑ i, ‖M i‖ * ‖M i‖)
      ≤ advPM (composeFunFam (orN : (ι → Bool) → Bool) g) := by
  classical
  set c : ι → ℝ := fun i => ‖M i‖ with hcdef
  have hcpos : 0 < ∑ i, c i * c i := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine Finset.sum_pos' (fun i _ => mul_self_nonneg _) ⟨i₀, Finset.mem_univ _, ?_⟩
    exact mul_pos (hMpos i₀) (hMpos i₀)
  have hVpos : 0 < Real.sqrt (∑ i, c i * c i) := Real.sqrt_pos.mpr hcpos
  have hnorm : ‖orWStar c‖ = Real.sqrt (∑ i, c i * c i) := norm_orWStar hcpos
  refine advPM_composeFunFam_ge (orWStar_isAdvMatrix c) hM hMfeas hMpos
    hVpos (by rw [hnorm]; exact hVpos) fun p => ?_
  -- `‖Γf ⊙ D_p‖ · V = c_p · V = V · ‖M p‖ = ‖Γf‖ · ‖M p‖`
  rw [norm_orWStar_hadamard, hnorm, abs_of_pos (hMpos p)]
  exact le_of_eq (mul_comm _ _)

omit [DecidableEq ι] in
/-- Composing `AND` is composing `OR` with negated inner functions, up to
negating the output. -/
lemma composeFunFam_andN_eq {β : Type*}
    {g : ι → (β → Bool) → Bool} :
    composeFunFam (andN : (ι → Bool) → Bool) g
      = fun x => !(composeFunFam (orN : (ι → Bool) → Bool)
          (fun i u => !(g i u)) x) := by
  classical
  funext x
  change andN (tilde g x) = !(orN (tilde (fun i u => !(g i u)) x))
  rw [andN_eq]
  rfl

/-- The same bound for `AND_k`, by De Morgan. -/
theorem sqrt_sum_sq_le_advPM_composeFunFam_andN {β : Type*} [Fintype β]
    [DecidableEq β] {g : ι → (β → Bool) → Bool}
    {M : ι → Matrix (β → Bool) (β → Bool) ℝ}
    (hM : ∀ i, IsAdvMatrix (g i) (M i))
    (hMfeas : ∀ i q, ‖M i ⊙ advD q‖ ≤ 1) (hMpos : ∀ i, 0 < ‖M i‖)
    [Nonempty ι] :
    Real.sqrt (∑ i, ‖M i‖ * ‖M i‖)
      ≤ advPM (composeFunFam (andN : (ι → Bool) → Bool) g) := by
  have hg' : ∀ i, IsAdvMatrix (fun u => !(g i u)) (M i) := fun i =>
    isAdvMatrix_not.mpr (hM i)
  have h := sqrt_sum_sq_le_advPM_composeFunFam_orN hg' hMfeas hMpos
  rw [composeFunFam_andN_eq, advPM_not]
  exact h

end QuantumQueryComplexity

end SourceWeightedOr

section SourceWeightedDual

/-!
# The weighted dual and weighted dual composition

The cost side of the weighted composition theorem.  Composing an outer dual
solution with inner ones of costs `c i` gives a composed cost

  `∑_p c_p ‖ψ_{x_tilde,p}‖²`,

which is the **`c`-weighted** cost of the outer solution
(`DualPair.IsWeightedCostLe`).  So `DualPair.compose_isWeightedCostLe` turns
a weighted outer bound into an ordinary bound on the composition.

For `OR_n` with costs `c` the optimal weighted dual is one-dimensional, with
`δₚ = √cₚ / √V` at the all-zero input (where `V = √(∑ cᵢ²)`) and
`1 / (∑_{p ∈ supp x} δₚ)` on the support of each nonzero `x`; its `c`-weighted
cost is exactly `V` (`orWDual_isWeightedCostLe`).  Composing gives

  `advDual (OR_k ∘ (g₁, …, g_k)) ≤ √(∑ᵢ cᵢ²)`

whenever the inner functions have dual solutions of cost `cᵢ`
(`advDual_composeFunFam_orN_le`), matching the primal bound of
`SourceWeightedOr`.
-/


namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## The weighted cost of a dual solution -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-! ## The weighted `OR` dual -/

omit [DecidableEq ι] [Fintype ι] in
lemma sum_sq_le_sq_sum {S : Finset ι} {a : ι → ℝ} (ha : ∀ i ∈ S, 0 ≤ a i) :
    ∑ i ∈ S, a i * a i ≤ (∑ i ∈ S, a i) * ∑ i ∈ S, a i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  exact Finset.single_le_sum (fun j hj => mul_nonneg (ha i hi) (ha j hj)) hi

variable (c : ι → ℝ)

/-- The target value `V = √(∑ cᵢ²)`. -/
noncomputable def orWVal : ℝ := Real.sqrt (∑ i, c i * c i)

omit [DecidableEq ι] in
lemma orWVal_sq : orWVal c * orWVal c = ∑ i, c i * c i :=
  Real.mul_self_sqrt (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)

omit [DecidableEq ι] in
lemma orWVal_pos [Nonempty ι] (hc : ∀ i, 0 < c i) : 0 < orWVal c := by
  rw [orWVal]
  refine Real.sqrt_pos.mpr ?_
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact Finset.sum_pos' (fun i _ => (mul_pos (hc i) (hc i)).le)
    ⟨i₀, Finset.mem_univ _, mul_pos (hc i₀) (hc i₀)⟩

/-- `δₚ = √cₚ / √V`. -/
noncomputable def orWDelta (p : ι) : ℝ :=
  Real.sqrt (c p) / Real.sqrt (orWVal c)

/-- `D x = ∑_{p ∈ supp x} δₚ`. -/
noncomputable def orWSupp (x : ι → Bool) : ℝ :=
  ∑ p, if x p then orWDelta c p else 0

/-- The support sum of square roots, `∑_{p ∈ supp x} √cₚ`. -/
noncomputable def orWSqrtSupp (x : ι → Bool) : ℝ :=
  ∑ p, if x p then Real.sqrt (c p) else 0

variable {c}

omit [DecidableEq ι] in
lemma orWDelta_pos [Nonempty ι] (hc : ∀ i, 0 < c i) (p : ι) :
    0 < orWDelta c p := by
  classical
  exact div_pos (Real.sqrt_pos.mpr (hc p)) (Real.sqrt_pos.mpr (orWVal_pos c hc))

omit [DecidableEq ι] [Fintype ι] in
lemma exists_true_of_ne_zeroVec {x : ι → Bool} (hx : x ≠ zeroVec) :
    ∃ p, x p = true := by
  classical
  by_contra h
  push Not at h
  exact hx (funext fun p => by simpa using h p)

omit [DecidableEq ι] in
lemma orWSqrtSupp_pos (hc : ∀ i, 0 < c i) {x : ι → Bool}
    (hx : x ≠ zeroVec) : 0 < orWSqrtSupp c x := by
  classical
  obtain ⟨p₀, hp₀⟩ := exists_true_of_ne_zeroVec hx
  rw [orWSqrtSupp]
  refine Finset.sum_pos' (fun p _ => ?_) ⟨p₀, Finset.mem_univ _, ?_⟩
  · by_cases h : x p
    · rw [ite_eq_left h]
      exact Real.sqrt_nonneg _
    · rw [ite_eq_right h]
  · rw [ite_eq_left hp₀]
    exact Real.sqrt_pos.mpr (hc p₀)

omit [DecidableEq ι] in
lemma orWSupp_eq (x : ι → Bool) :
    orWSupp c x = orWSqrtSupp c x / Real.sqrt (orWVal c) := by
  rw [orWSupp, orWSqrtSupp, Finset.sum_div]
  exact Finset.sum_congr rfl fun p _ => by
    by_cases h : x p <;> simp [h, orWDelta]

omit [DecidableEq ι] in
lemma orWSupp_pos [Nonempty ι] (hc : ∀ i, 0 < c i) {x : ι → Bool}
    (hx : x ≠ zeroVec) : 0 < orWSupp c x := by
  classical
  rw [orWSupp_eq]
  exact div_pos (orWSqrtSupp_pos hc hx)
    (Real.sqrt_pos.mpr (orWVal_pos c hc))

/-- The one-dimensional weighted dual weights for `OR_n`. -/
noncomputable def orWDualVec (c : ι → ℝ) (x : ι → Bool) (p : ι) : ℝ :=
  if x = zeroVec then orWDelta c p
  else if x p then 1 / orWSupp c x else 0

/-- The weighted dual solution for `OR_n`. -/
noncomputable def orWDual [Nonempty ι] (hc : ∀ i, 0 < c i) :
    DualPair Unit (orN : (ι → Bool) → Bool) where
  u x p _ := orWDualVec c x p
  v x p _ := orWDualVec c x p
  constraint x y := by
    by_cases hx : x = zeroVec <;> by_cases hy : y = zeroVec
    · subst hx; subst hy
      rw [ite_eq_left rfl]
      exact Finset.sum_eq_zero fun p _ => ite_eq_left rfl
    · subst hx
      have hne : ¬(orN (zeroVec : ι → Bool) = orN y) := by
        rw [orN_zeroVec, orN_eq_true_iff.mpr hy]
        simp
      rw [ite_eq_right hne]
      have hstep : ∀ p : ι,
          (if (zeroVec : ι → Bool) p = y p then (0:ℝ)
            else ∑ _k : Unit, orWDualVec c zeroVec p * orWDualVec c y p)
          = if y p = true then orWDelta c p * (1 / orWSupp c y) else 0 := by
        intro p
        by_cases hyp : y p = true
        · rw [ite_eq_right (by rw [zeroVec_apply, hyp]; exact Bool.noConfusion),
            ite_eq_left hyp]
          simp [orWDualVec, hy, hyp]
        · simp only [Bool.not_eq_true] at hyp
          rw [ite_eq_left (by rw [zeroVec_apply, hyp]), ite_eq_right (by simp [hyp])]
      rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) => hstep p]
      rw [show (∑ p : ι, if y p = true then
            orWDelta c p * (1 / orWSupp c y) else 0)
          = (∑ p : ι, if y p = true then orWDelta c p else 0) *
            (1 / orWSupp c y) from by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by
          by_cases h : y p <;> simp [h]]
      rw [← orWSupp]
      have hDpos : 0 < orWSupp c y := orWSupp_pos hc hy
      field_simp
    · subst hy
      have hne : ¬(orN x = orN (zeroVec : ι → Bool)) := by
        rw [orN_zeroVec, orN_eq_true_iff.mpr hx]
        simp
      rw [ite_eq_right hne]
      have hstep : ∀ p : ι,
          (if x p = (zeroVec : ι → Bool) p then (0:ℝ)
            else ∑ _k : Unit, orWDualVec c x p * orWDualVec c zeroVec p)
          = if x p = true then (1 / orWSupp c x) * orWDelta c p else 0 := by
        intro p
        by_cases hxp : x p = true
        · rw [ite_eq_right (by rw [zeroVec_apply, hxp]; exact Bool.noConfusion),
            ite_eq_left hxp]
          simp [orWDualVec, hx, hxp]
        · simp only [Bool.not_eq_true] at hxp
          rw [ite_eq_left (by rw [zeroVec_apply, hxp]), ite_eq_right (by simp [hxp])]
      rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) => hstep p]
      rw [show (∑ p : ι, if x p = true then
            (1 / orWSupp c x) * orWDelta c p else 0)
          = (1 / orWSupp c x) *
            ∑ p : ι, (if x p = true then orWDelta c p else 0) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by
          by_cases h : x p <;> simp [h]]
      rw [← orWSupp]
      have hDpos : 0 < orWSupp c x := orWSupp_pos hc hx
      field_simp
    · rw [ite_eq_left (by rw [orN_eq_true_iff.mpr hx, orN_eq_true_iff.mpr hy])]
      refine Finset.sum_eq_zero fun p _ => ?_
      by_cases hp : x p = y p
      · rw [ite_eq_left hp]
      · rw [ite_eq_right hp]
        have hzero : orWDualVec c x p * orWDualVec c y p = 0 := by
          rcases Bool.eq_false_or_eq_true (x p) with hxp | hxp
          · have hyp : y p = false := by
              rcases Bool.eq_false_or_eq_true (y p) with h | h
              · exact absurd (hxp.trans h.symm) hp
              · exact h
            have h0 : orWDualVec c y p = 0 := by
              rw [orWDualVec, ite_eq_right hy, ite_eq_right (by simp [hyp] : ¬(y p = true))]
            rw [h0, mul_zero]
          · have h0 : orWDualVec c x p = 0 := by
              rw [orWDualVec, ite_eq_right hx, ite_eq_right (by simp [hxp] : ¬(x p = true))]
            rw [h0, zero_mul]
        simpa using hzero

omit [DecidableEq ι] in
theorem orWDual_isWeightedCostLe [Nonempty ι] (hc : ∀ i, 0 < c i) :
    (orWDual hc).IsWeightedCostLe c (orWVal c) := by
  have hV : 0 < orWVal c := orWVal_pos c hc
  have hsV : 0 < Real.sqrt (orWVal c) := Real.sqrt_pos.mpr hV
  have key : ∀ x : ι → Bool,
      (∑ p, c p * ∑ _k : Unit, orWDualVec c x p * orWDualVec c x p)
        ≤ orWVal c := by
    intro x
    by_cases hx : x = zeroVec
    · subst hx
      have hval : (∑ p, c p * ∑ _k : Unit,
          orWDualVec c (zeroVec : ι → Bool) p *
            orWDualVec c (zeroVec : ι → Bool) p)
          = (∑ p, c p * c p) / orWVal c := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun p _ => ?_
        have hδ : orWDelta c p * orWDelta c p = c p / orWVal c := by
          rw [orWDelta, div_mul_div_comm, Real.mul_self_sqrt (hc p).le,
            Real.mul_self_sqrt hV.le]
        rw [orWDualVec, ite_eq_left rfl]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unit,
          one_smul]
        rw [hδ]
        field_simp
      have hVne : orWVal c ≠ 0 := ne_of_gt hV
      rw [hval, ← orWVal_sq c, mul_div_assoc, div_self hVne, mul_one]
    · have hDpos : 0 < orWSupp c x := orWSupp_pos hc hx
      have hSpos : 0 < orWSqrtSupp c x := orWSqrtSupp_pos hc hx
      have hval : (∑ p, c p * ∑ _k : Unit, orWDualVec c x p * orWDualVec c x p)
          = (1 / orWSupp c x) * (1 / orWSupp c x) *
            ∑ p, (if x p then c p else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unit,
          one_smul, orWDualVec, ite_eq_right hx]
        by_cases hxp : x p
        · rw [ite_eq_left hxp, ite_eq_left hxp]
          ring
        · rw [ite_eq_right hxp, ite_eq_right hxp]
          ring
      rw [hval]
      -- `∑_{supp} c ≤ (∑_{supp} √c)²`
      have hsum : (∑ p, if x p then c p else 0)
          ≤ orWSqrtSupp c x * orWSqrtSupp c x := by
        have h := sum_sq_le_sq_sum (S := (Finset.univ : Finset ι))
          (a := fun p => if x p then Real.sqrt (c p) else 0)
          (fun p _ => by by_cases h : x p <;> simp [h, Real.sqrt_nonneg])
        rw [orWSqrtSupp]
        refine le_trans (le_of_eq ?_) h
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases h : x p
        · rw [ite_eq_left h, ite_eq_left h, Real.mul_self_sqrt (hc p).le]
        · rw [ite_eq_right h, ite_eq_right h, mul_zero]
      -- `D = S/√V`, so `(1/D)² = V/S²`
      have hDS : orWSupp c x * orWSupp c x
          = orWSqrtSupp c x * orWSqrtSupp c x / orWVal c := by
        rw [orWSupp_eq, div_mul_div_comm, Real.mul_self_sqrt hV.le]
      have hVne : orWVal c ≠ 0 := ne_of_gt hV
      rw [show (1 / orWSupp c x) * (1 / orWSupp c x) *
            (∑ p, if x p then c p else 0)
          = (∑ p, if x p then c p else 0) /
            (orWSupp c x * orWSupp c x) from by ring]
      rw [div_le_iff₀ (mul_pos hDpos hDpos), hDS,
        show orWVal c * (orWSqrtSupp c x * orWSqrtSupp c x / orWVal c)
          = orWSqrtSupp c x * orWSqrtSupp c x from by field_simp]
      exact hsum
  exact ⟨key, key⟩

/-! ## The weighted `OR`-composition upper bound -/

variable {β : Type*} [Fintype β] [DecidableEq β]

omit [DecidableEq β] [DecidableEq ι] in
/-- **The weighted `OR`-composition upper bound**, matching the primal bound
`sqrt_sum_sq_le_advPM_composeFunFam_orN`. -/
theorem advDual_composeFunFam_orN_le [Nonempty ι] {g : ι → (β → Bool) → Bool}
    {K₂ : Type*} [Fintype K₂] {Pg : ∀ i, DualPair K₂ (g i)} {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) (hg : ∀ i, (Pg i).IsCostLe (c i)) :
    advDual (composeFunFam (orN : (ι → Bool) → Bool) g)
      ≤ Real.sqrt (∑ i, c i * c i) := by
  classical
  exact advDual_le_of_dualPair ((orWDual hc).compose Pg)
      (Real.sqrt_nonneg _)
      ((orWDual hc).compose_isWeightedCostLe (orWDual_isWeightedCostLe hc) hg)

end QuantumQueryComplexity

end SourceWeightedDual

section SourceComposeShared

/-!
# Dual composition with shared inputs

The composition in `SourceDualCompose` gives each inner function its
own block of variables (`composeFunFam` over `α × β`).  Divide-and-conquer needs
the opposite: finitely many subproblems `g p`, all reading the *same* input `x`,
whose domains typically overlap.  Write

  `sharedFun h g x = h (fun p => g p x)`.

Duals compose in this setting too, and the argument is shorter than the disjoint
one.  Tensoring the outer solution at `p` with the `p`-th inner solution,

  `u x i = ⊕_p U_{g(x)} p ⊗ u^p x i`,   `v y i = ⊕_p V_{g(y)} p ⊗ v^p y i`,

the masked sum factors as

  `∑_{i : x i ≠ y i} ⟨u x i, v y i⟩ = ∑_p ⟨U_{g x} p, V_{g y} p⟩ · [g p x ≠ g p y]`,

which is exactly the outer constraint evaluated at the pair `(g x, g y)`.  No
property of the inner functions' supports is used, so they may overlap freely.

The cost telescopes the same way: the `p`-th block contributes
`‖U_{g x} p‖²` times the `p`-th inner cost, so an outer solution of *weighted*
cost `V` with weights `c` and inner solutions of cost `c p` compose to cost `V`
(`DualPair.composeShared_isCostLe`).  That is the whole quantitative content of
"solve subproblem `p` at cost `c p`, then optimise over `p`".
-/


namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [DecidableEq σ]
variable {P : Type*} [Fintype P] [DecidableEq P]
variable {V : Type*} [DecidableEq V]
variable {O : Type*} [DecidableEq O]

/-- The composition of an outer function with subproblems that all read the same
input. -/
def sharedFun (h : (P → V) → O) (g : P → (ι → σ) → V) : (ι → σ) → O :=
  fun x => h fun p => g p x

omit [DecidableEq O] [DecidableEq P] [DecidableEq V] [DecidableEq ι] [DecidableEq σ]
    [Fintype P] [Fintype ι] in
@[simp] lemma sharedFun_apply (h : (P → V) → O) (g : P → (ι → σ) → V)
    (x : ι → σ) : sharedFun h g x = h (fun p => g p x) := by
  classical
  exact rfl

namespace DualPair

variable {K K' : Type*} [Fintype K] [Fintype K']
variable {h : (P → V) → O} {g : P → (ι → σ) → V}

/-- **Shared-input dual composition.** -/
@[expose]
noncomputable def composeShared (Q : DualPair K h) (R : ∀ p, DualPair K' (g p)) :
    DualPair (P × K × K') (sharedFun h g) where
  u x i := fun c => Q.u (fun p => g p x) c.1 c.2.1 * (R c.1).u x i c.2.2
  v y i := fun c => Q.v (fun p => g p y) c.1 c.2.1 * (R c.1).v y i c.2.2
  constraint x y := by
    classical
    simp only [sharedFun]
    set A : P → ℝ := fun p =>
      ∑ k : K, Q.u (fun p => g p x) p k * Q.v (fun p => g p y) p k with hA
    set B : P → ι → ℝ := fun p i =>
      ∑ k' : K', (R p).u x i k' * (R p).v y i k' with hB
    have hpt : ∀ i : ι,
        (∑ c : P × K × K',
          (Q.u (fun p => g p x) c.1 c.2.1 * (R c.1).u x i c.2.2) *
            (Q.v (fun p => g p y) c.1 c.2.1 * (R c.1).v y i c.2.2))
        = ∑ p : P, A p * B p i := by
      intro i
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Fintype.sum_prod_type, hA, hB, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
    calc (∑ i : ι, if x i = y i then (0 : ℝ)
            else ∑ c : P × K × K',
              (Q.u (fun p => g p x) c.1 c.2.1 * (R c.1).u x i c.2.2) *
                (Q.v (fun p => g p y) c.1 c.2.1 * (R c.1).v y i c.2.2))
        = ∑ i : ι, ∑ p : P, A p * (if x i = y i then (0 : ℝ) else B p i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : x i = y i
          · rw [ite_eq_left hi]
            exact (Finset.sum_eq_zero fun p _ => by rw [ite_eq_left hi, mul_zero]).symm
          · rw [ite_eq_right hi, hpt i]
            exact Finset.sum_congr rfl fun p _ => by rw [ite_eq_right hi]
      _ = ∑ p : P, A p * ∑ i : ι, (if x i = y i then (0 : ℝ) else B p i) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ p : P, A p * (if g p x = g p y then (0 : ℝ) else 1) :=
          Finset.sum_congr rfl fun p _ => by rw [hB, (R p).constraint x y]
      _ = if h (fun p => g p x) = h (fun p => g p y) then (0 : ℝ) else 1 := by
          rw [← Q.constraint (fun p => g p x) (fun p => g p y)]
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases hp : g p x = g p y
          · rw [ite_eq_left hp, ite_eq_left hp, mul_zero]
          · rw [ite_eq_right hp, ite_eq_right hp, mul_one, hA]

omit [DecidableEq P] [DecidableEq ι] in
@[simp] lemma composeShared_u (Q : DualPair K h) (R : ∀ p, DualPair K' (g p))
    (x : ι → σ) (i : ι) (c : P × K × K') :
    (Q.composeShared R).u x i c
      = Q.u (fun p => g p x) c.1 c.2.1 * (R c.1).u x i c.2.2 := rfl

omit [DecidableEq P] [DecidableEq ι] in
@[simp] lemma composeShared_v (Q : DualPair K h) (R : ∀ p, DualPair K' (g p))
    (y : ι → σ) (i : ι) (c : P × K × K') :
    (Q.composeShared R).v y i c
      = Q.v (fun p => g p y) c.1 c.2.1 * (R c.1).v y i c.2.2 := rfl

omit [DecidableEq P] [DecidableEq ι] in
/-- The `ℓ²` mass of the composed solution splits as (outer mass at `p`) times
(inner mass of the `p`-th solution). -/
private lemma sum_composeShared_u_sq (Q : DualPair K h) (R : ∀ p, DualPair K' (g p))
    (x : ι → σ) :
    (∑ i : ι, ∑ c : P × K × K',
      (Q.composeShared R).u x i c * (Q.composeShared R).u x i c)
      = ∑ p : P, (∑ k : K, Q.u (fun p => g p x) p k * Q.u (fun p => g p x) p k)
          * ∑ i : ι, ∑ k' : K', (R p).u x i k' * (R p).u x i k' := by
  have hstep : ∀ i : ι,
      (∑ c : P × K × K', (Q.composeShared R).u x i c * (Q.composeShared R).u x i c)
        = ∑ p : P, (∑ k : K, Q.u (fun p => g p x) p k * Q.u (fun p => g p x) p k)
            * ∑ k' : K', (R p).u x i k' * (R p).u x i k' := by
    intro i
    simp only [composeShared_u]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm

omit [DecidableEq P] [DecidableEq ι] in
private lemma sum_composeShared_v_sq (Q : DualPair K h) (R : ∀ p, DualPair K' (g p))
    (y : ι → σ) :
    (∑ i : ι, ∑ c : P × K × K',
      (Q.composeShared R).v y i c * (Q.composeShared R).v y i c)
      = ∑ p : P, (∑ k : K, Q.v (fun p => g p y) p k * Q.v (fun p => g p y) p k)
          * ∑ i : ι, ∑ k' : K', (R p).v y i k' * (R p).v y i k' := by
  have hstep : ∀ i : ι,
      (∑ c : P × K × K', (Q.composeShared R).v y i c * (Q.composeShared R).v y i c)
        = ∑ p : P, (∑ k : K, Q.v (fun p => g p y) p k * Q.v (fun p => g p y) p k)
            * ∑ k' : K', (R p).v y i k' * (R p).v y i k' := by
    intro i
    simp only [composeShared_v]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm

omit [DecidableEq P] [DecidableEq ι] in
/-- **The cost of a shared composition.**  An outer solution of `c`-weighted cost
`V` composed with inner solutions of cost `c p` has cost `V`. -/
theorem composeShared_isCostLe {c : P → ℝ} {Vout : ℝ} (Q : DualPair K h)
    (R : ∀ p, DualPair K' (g p))
    (hQ : Q.IsWeightedCostLe c Vout) (hR : ∀ p, (R p).IsCostLe (c p)) :
    (Q.composeShared R).IsCostLe Vout := by
  classical
  constructor
  · intro x
    rw [sum_composeShared_u_sq]
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) (hQ.1 fun p => g p x)
    exact (mul_le_mul_of_nonneg_left ((hR p).1 x)
      (Finset.sum_nonneg fun k _ => mul_self_nonneg _)).trans_eq (mul_comm _ _)
  · intro y
    rw [sum_composeShared_v_sq]
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) (hQ.2 fun p => g p y)
    exact (mul_le_mul_of_nonneg_left ((hR p).2 y)
      (Finset.sum_nonneg fun k _ => mul_self_nonneg _)).trans_eq (mul_comm _ _)

end DualPair

omit [DecidableEq P] in
/-- The adversary bound of a shared composition, from an outer weighted solution
and inner solutions. -/
theorem advPM_sharedFun_le [Fintype σ] {K K' : Type*} [Fintype K] [Fintype K']
    {h : (P → V) → O} {g : P → (ι → σ) → V} {c : P → ℝ} {Vout : ℝ}
    (Q : DualPair K h) (R : ∀ p, DualPair K' (g p))
    (hV : 0 ≤ Vout) (hQ : Q.IsWeightedCostLe c Vout)
    (hR : ∀ p, (R p).IsCostLe (c p)) :
    advPM (sharedFun h g) ≤ Vout := by
  classical
  exact advPM_le_of_dualPair (Q.composeShared R) hV
      (DualPair.composeShared_isCostLe Q R hQ hR)

end QuantumQueryComplexity

end SourceComposeShared

section SourceFirstDiff

/-!
# The first-difference dual: `ADV±(f) ≤ 2n` for every `f`

Order the coordinates arbitrarily.  For inputs `x ≠ y` there is exactly one
coordinate at which they *first* differ, so

  `∑_{i : x i ≠ y i} [x agrees with y before i] = 1`.

Tensoring that indicator with a cheap factorization of the "different output"
matrix, `⟨φ_a, ψ_b⟩ = [a ≠ b]`, turns it into a feasible dual solution: the
count `1` is switched on precisely when `f x ≠ f y`, and the LMRSS equality
constraints hold because the `φψ` factor already vanishes there.  Each input
puts mass `‖φ‖² = 2` on each of the `n` coordinates, so the cost is `2n`.

This is the dual attached to the trivial decision tree that reads every
coordinate in order.  Its point here is that **the bound carries no alphabet
dependence at all**, so it complements `upstream Max/Dyadic.lean`, whose
`2⌈log₂ m⌉√n` degrades for very large alphabets.

The same construction applied to an arbitrary decision tree gives
`ADV±(f) ≤ 2 D(f)`, and averaging duals (which is legitimate, since the
constraint is linear in `⟨u, v⟩`) gives `ADV±(f) ≤ 2 R₀(f)`.  Neither helps for
maximum finding, where every coordinate must be read: `D(MAX) = R₀(MAX) = n`.
-/


namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} [Fintype O] [DecidableEq O]

/-! ## An arbitrary ordering of the coordinates -/

/-- An arbitrary injective ranking of the finite index type; it supplies the
"reading order" of the trivial decision tree. -/
noncomputable def idxRank (i : ι) : Fin (Fintype.card ι) := Fintype.equivFin ι i

omit [DecidableEq ι] in
lemma idxRank_inj : Function.Injective (idxRank : ι → Fin (Fintype.card ι)) :=
  (Fintype.equivFin ι).injective

/-- What has been read about `x` before coordinate `i` is queried. -/
noncomputable def prefixOf (x : ι → σ) (i : ι) : ι → Option σ :=
  fun j => if idxRank j < idxRank i then some (x j) else none

omit [DecidableEq ι] [DecidableEq σ] [Fintype σ] in
lemma prefixOf_eq_iff {x y : ι → σ} {i : ι} :
    prefixOf x i = prefixOf y i ↔ ∀ j, idxRank j < idxRank i → x j = y j := by
  constructor
  · intro h j hj
    have hj' := congrFun h j
    simp only [prefixOf, ite_eq_left hj, Option.some.injEq] at hj'
    exact hj'
  · intro h
    funext j
    simp only [prefixOf]
    by_cases hj : idxRank j < idxRank i
    · rw [ite_eq_left hj, ite_eq_left hj, h j hj]
    · rw [ite_eq_right hj, ite_eq_right hj]

/-! ## Exactly one first difference -/

/-- The coordinates at which `x` and `y` differ for the first time. -/
noncomputable def firstDiffSet (x y : ι → σ) : Finset ι :=
  Finset.univ.filter fun i => x i ≠ y i ∧ prefixOf x i = prefixOf y i

omit [DecidableEq ι] [Fintype σ] in
/-- **Distinct inputs have exactly one first difference.** -/
lemma card_firstDiffSet {x y : ι → σ} (h : x ≠ y) :
    (firstDiffSet x y).card = 1 := by
  classical
  have hD : (Finset.univ.filter fun i => x i ≠ y i).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact ⟨i, by simpa using hi⟩
  obtain ⟨i₀, hmem, hmin⟩ :=
    Finset.exists_min_image (Finset.univ.filter fun i => x i ≠ y i) idxRank hD
  rw [Finset.mem_filter] at hmem
  have hlow : ∀ j, idxRank j < idxRank i₀ → x j = y j := by
    intro j hj
    by_contra hne
    exact absurd (hmin j (by simpa using hne)) (by omega)
  rw [Finset.card_eq_one]
  refine ⟨i₀, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun i hi => ?_⟩⟩
  · simp only [firstDiffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hmem.2, prefixOf_eq_iff.2 hlow⟩
  · simp only [firstDiffSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have h1 : idxRank i₀ ≤ idxRank i := hmin i (by simpa using hi.1)
    have h2 : ¬ idxRank i₀ < idxRank i := fun hlt =>
      hmem.2 (prefixOf_eq_iff.1 hi.2 i₀ hlt)
    exact idxRank_inj (le_antisymm (by omega) h1)

/-! ## A cheap factorization of the "different output" matrix -/

/-- `φ a` and `ψ b` pair to `1` exactly when `a ≠ b`, with squared norms `2`. -/
def phiVec (a : O) : Option O → ℝ :=
  fun t => if t = none then 1 else if t = some a then -1 else 0

/-- The partner of `phiVec`. -/
def psiVec (b : O) : Option O → ℝ :=
  fun t => if t = none then 1 else if t = some b then 1 else 0

lemma sum_phiVec_mul_psiVec (a b : O) :
    (∑ t : Option O, phiVec a t * psiVec b t) = if a = b then 0 else 1 := by
  rw [Fintype.sum_option]
  have hnone : phiVec a none * psiVec b none = 1 := by simp [phiVec, psiVec]
  have hsome : ∀ c : O, phiVec a (some c) * psiVec b (some c)
      = if c = a then (if c = b then (-1 : ℝ) else 0) else 0 := by
    intro c
    simp only [phiVec, psiVec, reduceCtorEq, ite_false, Option.some.injEq]
    by_cases h1 : c = a <;> by_cases h2 : c = b <;> simp [h1, h2]
  rw [hnone, Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hsome c,
    Finset.sum_ite_eq' Finset.univ a fun c => if c = b then (-1 : ℝ) else 0,
    ite_eq_left (Finset.mem_univ a)]
  by_cases hab : a = b <;> simp [hab]

lemma sum_phiVec_sq (a : O) : (∑ t : Option O, phiVec a t * phiVec a t) = 2 := by
  rw [Fintype.sum_option]
  have hsome : ∀ c : O, phiVec a (some c) * phiVec a (some c)
      = if c = a then (1 : ℝ) else 0 := by
    intro c
    simp only [phiVec, reduceCtorEq, ite_false, Option.some.injEq]
    by_cases h1 : c = a <;> simp [h1]
  rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hsome c,
    Finset.sum_ite_eq' Finset.univ a fun _ => (1 : ℝ), ite_eq_left (Finset.mem_univ a)]
  norm_num [phiVec]

lemma sum_psiVec_sq (b : O) : (∑ t : Option O, psiVec b t * psiVec b t) = 2 := by
  rw [Fintype.sum_option]
  have hsome : ∀ c : O, psiVec b (some c) * psiVec b (some c)
      = if c = b then (1 : ℝ) else 0 := by
    intro c
    simp only [psiVec, reduceCtorEq, ite_false, Option.some.injEq]
    by_cases h1 : c = b <;> simp [h1]
  rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hsome c,
    Finset.sum_ite_eq' Finset.univ b fun _ => (1 : ℝ), ite_eq_left (Finset.mem_univ b)]
  norm_num [psiVec]

/-! ## The dual solution -/

/-- The dual solution of the trivial decision tree that reads every coordinate
in the order given by `idxRank`. -/
noncomputable def firstDiffDual (f : (ι → σ) → O) :
    DualPair ((ι → Option σ) × Option O) f where
  u x i := fun c => (if c.1 = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) c.2
  v y i := fun c => (if c.1 = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) c.2
  constraint x y := by
    have hpt : ∀ i : ι,
        (∑ c : (ι → Option σ) × Option O,
          ((if c.1 = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) c.2) *
            ((if c.1 = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) c.2))
        = (if prefixOf x i = prefixOf y i then (1 : ℝ) else 0)
            * (if f x = f y then 0 else 1) := by
      intro i
      rw [Fintype.sum_prod_type, ← sum_phiVec_mul_psiVec (f x) (f y)]
      rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
        show (∑ t : Option O,
            ((if p = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) t) *
              ((if p = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) t))
          = ((if p = prefixOf x i then (1 : ℝ) else 0) *
              (if p = prefixOf y i then (1 : ℝ) else 0))
            * ∑ t : Option O, phiVec (f x) t * psiVec (f y) t from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring]
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
        show ((if p = prefixOf x i then (1 : ℝ) else 0) *
            (if p = prefixOf y i then (1 : ℝ) else 0))
          = (if p = prefixOf x i then
              (if prefixOf x i = prefixOf y i then (1 : ℝ) else 0) else 0) from by
          by_cases h1 : p = prefixOf x i <;> by_cases h2 : p = prefixOf y i <;>
            simp [h1, h2]; grind]
      rw [Finset.sum_ite_eq' Finset.univ (prefixOf x i)
        fun _ => (if prefixOf x i = prefixOf y i then (1 : ℝ) else 0),
        ite_eq_left (Finset.mem_univ _)]
    simp only [hpt]
    have hmask : ∀ i : ι,
        (if x i = y i then (0 : ℝ)
          else (if prefixOf x i = prefixOf y i then (1 : ℝ) else 0)
            * (if f x = f y then 0 else 1))
        = (if i ∈ firstDiffSet x y then (1 : ℝ) else 0)
            * (if f x = f y then 0 else 1) := by
      intro i
      have hmem : i ∈ firstDiffSet x y
          ↔ (x i ≠ y i ∧ prefixOf x i = prefixOf y i) := by
        simp [firstDiffSet]
      by_cases h : x i = y i
      · have hnot : i ∉ firstDiffSet x y := fun hc => (hmem.mp hc).1 h
        rw [ite_eq_left h, ite_eq_right hnot, zero_mul]
      · by_cases h2 : prefixOf x i = prefixOf y i
        · rw [ite_eq_right h, ite_eq_left h2, ite_eq_left (hmem.mpr ⟨h, h2⟩)]
        · have hnot : i ∉ firstDiffSet x y := fun hc => h2 (hmem.mp hc).2
          rw [ite_eq_right h, ite_eq_right h2, ite_eq_right hnot]
    simp only [hmask]
    rw [← Finset.sum_mul]
    by_cases hf : f x = f y
    · rw [ite_eq_left hf, mul_zero]
    · rw [ite_eq_right hf, mul_one]
      have hxy : x ≠ y := fun h => hf (by rw [h])
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
        card_firstDiffSet hxy, Nat.cast_one, mul_one]

omit [DecidableEq O] [Fintype O] in
/-- **`ADV±(f) ≤ 2n` for every function on `n` variables**, with no dependence
on the input alphabet or the output type. -/
theorem advPM_le_two_mul_card (f : (ι → σ) → O) [Finite O] :
    advPM f ≤ 2 * (Fintype.card ι : ℝ) := by
  classical
  let := Fintype.ofFinite O
  refine advPM_le_of_dualPair (firstDiffDual f) (by positivity) ⟨fun x => ?_, fun y => ?_⟩
  · have hstep : ∀ i : ι,
        (∑ c : (ι → Option σ) × Option O,
          (firstDiffDual f).u x i c * (firstDiffDual f).u x i c) = 2 := by
      intro i
      change (∑ c : (ι → Option σ) × Option O,
        ((if c.1 = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) c.2) *
          ((if c.1 = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) c.2)) = 2
      rw [Fintype.sum_prod_type, ← sum_phiVec_sq (f x)]
      rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
        show (∑ t : Option O,
            ((if p = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) t) *
              ((if p = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) t))
          = (if p = prefixOf x i then (1 : ℝ) else 0)
            * ∑ t : Option O, phiVec (f x) t * phiVec (f x) t from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by
            by_cases h : p = prefixOf x i <;> simp [h]]
      rw [← Finset.sum_mul, Finset.sum_ite_eq' Finset.univ (prefixOf x i)
        fun _ => (1 : ℝ), ite_eq_left (Finset.mem_univ _), one_mul]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact le_of_eq (mul_comm _ _)
  · have hstep : ∀ i : ι,
        (∑ c : (ι → Option σ) × Option O,
          (firstDiffDual f).v y i c * (firstDiffDual f).v y i c) = 2 := by
      intro i
      change (∑ c : (ι → Option σ) × Option O,
        ((if c.1 = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) c.2) *
          ((if c.1 = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) c.2)) = 2
      rw [Fintype.sum_prod_type, ← sum_psiVec_sq (f y)]
      rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
        show (∑ t : Option O,
            ((if p = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) t) *
              ((if p = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) t))
          = (if p = prefixOf y i then (1 : ℝ) else 0)
            * ∑ t : Option O, psiVec (f y) t * psiVec (f y) t from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by
            by_cases h : p = prefixOf y i <;> simp [h]]
      rw [← Finset.sum_mul, Finset.sum_ite_eq' Finset.univ (prefixOf y i)
        fun _ => (1 : ℝ), ite_eq_left (Finset.mem_univ _), one_mul]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact le_of_eq (mul_comm _ _)

/-- Each input puts mass exactly `‖φ‖² = 2` on each coordinate. -/
lemma sum_firstDiffDual_u_sq (f : (ι → σ) → O) (x : ι → σ) (i : ι) :
    (∑ c : (ι → Option σ) × Option O,
      (firstDiffDual f).u x i c * (firstDiffDual f).u x i c) = 2 := by
  change (∑ c : (ι → Option σ) × Option O,
    ((if c.1 = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) c.2) *
      ((if c.1 = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) c.2)) = 2
  rw [Fintype.sum_prod_type, ← sum_phiVec_sq (f x)]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
    show (∑ t : Option O,
        ((if p = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) t) *
          ((if p = prefixOf x i then (1 : ℝ) else 0) * phiVec (f x) t))
      = (if p = prefixOf x i then (1 : ℝ) else 0)
        * ∑ t : Option O, phiVec (f x) t * phiVec (f x) t from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by
        by_cases h : p = prefixOf x i <;> simp [h]]
  rw [← Finset.sum_mul, Finset.sum_ite_eq' Finset.univ (prefixOf x i)
    fun _ => (1 : ℝ), ite_eq_left (Finset.mem_univ _), one_mul]

lemma sum_firstDiffDual_v_sq (f : (ι → σ) → O) (y : ι → σ) (i : ι) :
    (∑ c : (ι → Option σ) × Option O,
      (firstDiffDual f).v y i c * (firstDiffDual f).v y i c) = 2 := by
  change (∑ c : (ι → Option σ) × Option O,
    ((if c.1 = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) c.2) *
      ((if c.1 = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) c.2)) = 2
  rw [Fintype.sum_prod_type, ← sum_psiVec_sq (f y)]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
    show (∑ t : Option O,
        ((if p = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) t) *
          ((if p = prefixOf y i then (1 : ℝ) else 0) * psiVec (f y) t))
      = (if p = prefixOf y i then (1 : ℝ) else 0)
        * ∑ t : Option O, psiVec (f y) t * psiVec (f y) t from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by
        by_cases h : p = prefixOf y i <;> simp [h]]
  rw [← Finset.sum_mul, Finset.sum_ite_eq' Finset.univ (prefixOf y i)
    fun _ => (1 : ℝ), ite_eq_left (Finset.mem_univ _), one_mul]

/-- The weighted cost of the first-difference dual: mass `2` on every
coordinate, so the `c`-weighted cost is `2 ∑ c`. -/
theorem firstDiffDual_isWeightedCostLe (f : (ι → σ) → O) (c : ι → ℝ) :
    (firstDiffDual f).IsWeightedCostLe c (2 * ∑ i, c i) := by
  constructor
  · intro x
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
      rw [sum_firstDiffDual_u_sq f x i], Finset.mul_sum]
    exact le_of_eq (Finset.sum_congr rfl fun i _ => mul_comm _ _)
  · intro y
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
      rw [sum_firstDiffDual_v_sq f y i], Finset.mul_sum]
    exact le_of_eq (Finset.sum_congr rfl fun i _ => mul_comm _ _)

end QuantumQueryComplexity

end SourceFirstDiff

section SourceScanAverage

/-!
# Averaging dual solutions

The dual constraint is **linear** in `⟨u x i, v y i⟩`, so a convex combination
of solutions for the *same* function is again a solution: scale the `z`-th by
`√(p z)` and take an orthogonal direct sum, and the pairing averages copies of
the same number `[f x ≠ f y]`.

What makes this worth doing is the cost.  The averaged solution costs

  `∑ z, p z · (cost of the z-th solution at that input)`

*per input* — an average of costs, not a cost of averages.  A family of
solutions that is individually bad but good on average is therefore fine, which
is exactly the situation for maximum finding: for a fixed scan order an
increasing input sets a record at every step, but over a uniformly random order
the probability of a record at step `t` is only `1/t`.
-/


namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [DecidableEq σ]
variable {O : Type*} [DecidableEq O]
variable {Z K : Type*} [Fintype Z] [Fintype K]
variable {f : (ι → σ) → O}

namespace DualPair

/-- **A convex combination of dual solutions for the same function.** -/
noncomputable def average (P : Z → DualPair K f) (p : Z → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z = 1) : DualPair (Z × K) f where
  u x i := fun zk => Real.sqrt (p zk.1) * (P zk.1).u x i zk.2
  v y i := fun zk => Real.sqrt (p zk.1) * (P zk.1).v y i zk.2
  constraint x y := by
    have hpt : ∀ i : ι,
        (∑ zk : Z × K, (Real.sqrt (p zk.1) * (P zk.1).u x i zk.2) *
          (Real.sqrt (p zk.1) * (P zk.1).v y i zk.2))
        = ∑ z : Z, p z * ∑ k : K, (P z).u x i k * (P z).v y i k := by
      intro i
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (Real.sqrt (p z) * (P z).u x i k) * (Real.sqrt (p z) * (P z).v y i k)
          = (Real.sqrt (p z) * Real.sqrt (p z))
            * ((P z).u x i k * (P z).v y i k) from by ring,
        Real.mul_self_sqrt (hp0 z)]
    have hmask : ∀ i : ι,
        (if x i = y i then (0 : ℝ)
          else ∑ z : Z, p z * ∑ k : K, (P z).u x i k * (P z).v y i k)
        = ∑ z : Z, p z * (if x i = y i then (0 : ℝ)
            else ∑ k : K, (P z).u x i k * (P z).v y i k) := by
      intro i
      by_cases h : x i = y i
      · rw [ite_eq_left h]
        exact (Finset.sum_eq_zero fun z _ => by rw [ite_eq_left h, mul_zero]).symm
      · rw [ite_eq_right h]
        exact Finset.sum_congr rfl fun z _ => by rw [ite_eq_right h]
    simp only [hpt, hmask]
    rw [Finset.sum_comm]
    have hz : ∀ z : Z, (∑ i : ι, p z * (if x i = y i then (0 : ℝ)
        else ∑ k : K, (P z).u x i k * (P z).v y i k))
        = p z * (if f x = f y then 0 else 1) := by
      intro z
      rw [← Finset.mul_sum, (P z).constraint x y]
    rw [Finset.sum_congr rfl fun z (_ : z ∈ Finset.univ) => hz z, ← Finset.sum_mul,
      hp1, one_mul]

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] in
/-- The averaged squared mass at one coordinate is the average of the squared
masses there.  Stated per coordinate so that a *weighted* cost, which inserts a
different factor at each one, can use it too. -/
private lemma sum_average_sq_coord (p : Z → ℝ) (hp0 : ∀ z, 0 ≤ p z)
    (U : Z → (ι → σ) → ι → K → ℝ) (x : ι → σ) (i : ι) :
    (∑ zk : Z × K, (Real.sqrt (p zk.1) * U zk.1 x i zk.2)
        * (Real.sqrt (p zk.1) * U zk.1 x i zk.2))
      = ∑ z : Z, p z * ∑ k : K, U z x i k * U z x i k := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Real.sqrt (p z) * U z x i k) * (Real.sqrt (p z) * U z x i k)
      = (Real.sqrt (p z) * Real.sqrt (p z)) * (U z x i k * U z x i k) from by ring,
    Real.mul_self_sqrt (hp0 z)]

omit [DecidableEq ι] [DecidableEq σ] in
lemma sum_average_sq (p : Z → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (U : Z → (ι → σ) → ι → K → ℝ) (x : ι → σ) :
    (∑ i : ι, ∑ zk : Z × K, (Real.sqrt (p zk.1) * U zk.1 x i zk.2)
        * (Real.sqrt (p zk.1) * U zk.1 x i zk.2))
      = ∑ z : Z, p z * ∑ i : ι, ∑ k : K, U z x i k * U z x i k := by
  classical
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    sum_average_sq_coord p hp0 U x i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => (Finset.mul_sum _ _ _).symm

omit [DecidableEq ι] [DecidableEq σ] in
private lemma sum_average_sq_weighted (p : Z → ℝ) (hp0 : ∀ z, 0 ≤ p z)
    (U : Z → (ι → σ) → ι → K → ℝ) (c : ι → ℝ) (x : ι → σ) :
    (∑ i : ι, c i * ∑ zk : Z × K, (Real.sqrt (p zk.1) * U zk.1 x i zk.2)
        * (Real.sqrt (p zk.1) * U zk.1 x i zk.2))
      = ∑ z : Z, p z * ∑ i : ι, c i * ∑ k : K, U z x i k * U z x i k := by
  classical
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
      rw [sum_average_sq_coord p hp0 U x i, Finset.mul_sum],
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq ι] in
/-- **The averaged cost is the average of the costs, input by input.** -/
theorem average_isCostLe (P : Z → DualPair K f) (p : Z → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z = 1) {c : ℝ}
    (hu : ∀ x : ι → σ,
      (∑ z : Z, p z * ∑ i : ι, ∑ k : K, (P z).u x i k * (P z).u x i k) ≤ c)
    (hv : ∀ y : ι → σ,
      (∑ z : Z, p z * ∑ i : ι, ∑ k : K, (P z).v y i k * (P z).v y i k) ≤ c) :
    (average P p hp0 hp1).IsCostLe c := by
  classical
  constructor
  · intro x
    exact le_trans (le_of_eq (sum_average_sq p hp0 (fun z => (P z).u) x)) (hu x)
  · intro y
    exact le_trans (le_of_eq (sum_average_sq p hp0 (fun z => (P z).v) y)) (hv y)

omit [DecidableEq ι] in
/-- **The averaged weighted cost is the average of the weighted costs.** -/
theorem average_isWeightedCostLe (P : Z → DualPair K f) (p : Z → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z = 1) {c : ι → ℝ} {V : ℝ}
    (hu : ∀ x : ι → σ, (∑ z : Z, p z *
      ∑ i : ι, c i * ∑ k : K, (P z).u x i k * (P z).u x i k) ≤ V)
    (hv : ∀ y : ι → σ, (∑ z : Z, p z *
      ∑ i : ι, c i * ∑ k : K, (P z).v y i k * (P z).v y i k) ≤ V) :
    (average P p hp0 hp1).IsWeightedCostLe c V := by
  classical
  constructor
  · intro x
    exact le_trans (le_of_eq
      (sum_average_sq_weighted p hp0 (fun z => (P z).u) c x)) (hu x)
  · intro y
    exact le_trans (le_of_eq
      (sum_average_sq_weighted p hp0 (fun z => (P z).v) c y)) (hv y)

/-- The uniform average over a nonempty finite family. -/
noncomputable def averageUnif [Nonempty Z] (P : Z → DualPair K f) :
    DualPair (Z × K) f :=
  average P (fun _ => (Fintype.card Z : ℝ)⁻¹)
    (fun _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero))

omit [DecidableEq ι] in
/-- **The averaged `ℓ²` mass at a single input.**  Exposing this, rather than
only the cost bound it implies, is what lets a dual solution be restricted to a
*promise* domain: its cost there is the maximum of these over the promise
only. -/
theorem sum_averageUnif_u_sq [Nonempty Z] (P : Z → DualPair K f) (x : ι → σ) :
    (∑ i : ι, ∑ zk : Z × K, (averageUnif P).u x i zk * (averageUnif P).u x i zk)
      = (Fintype.card Z : ℝ)⁻¹
        * ∑ z : Z, ∑ i : ι, ∑ k : K, (P z).u x i k * (P z).u x i k := by
  classical
  have h := sum_average_sq (fun _ => (Fintype.card Z : ℝ)⁻¹)
    (fun _ => by positivity) (fun z => (P z).u) x
  rw [← Finset.mul_sum] at h
  exact h

omit [DecidableEq ι] in
theorem sum_averageUnif_v_sq [Nonempty Z] (P : Z → DualPair K f) (y : ι → σ) :
    (∑ i : ι, ∑ zk : Z × K, (averageUnif P).v y i zk * (averageUnif P).v y i zk)
      = (Fintype.card Z : ℝ)⁻¹
        * ∑ z : Z, ∑ i : ι, ∑ k : K, (P z).v y i k * (P z).v y i k := by
  classical
  have h := sum_average_sq (fun _ => (Fintype.card Z : ℝ)⁻¹)
    (fun _ => by positivity) (fun z => (P z).v) y
  rw [← Finset.mul_sum] at h
  exact h

omit [DecidableEq ι] in
theorem averageUnif_isWeightedCostLe [Nonempty Z] (P : Z → DualPair K f)
    {c : ι → ℝ} {V : ℝ}
    (hu : ∀ x : ι → σ, (Fintype.card Z : ℝ)⁻¹ *
      ∑ z : Z, (∑ i : ι, c i * ∑ k : K, (P z).u x i k * (P z).u x i k) ≤ V)
    (hv : ∀ y : ι → σ, (Fintype.card Z : ℝ)⁻¹ *
      ∑ z : Z, (∑ i : ι, c i * ∑ k : K, (P z).v y i k * (P z).v y i k) ≤ V) :
    (averageUnif P).IsWeightedCostLe c V := by
  classical
  refine average_isWeightedCostLe P _ _ _ (fun x => ?_) (fun y => ?_)
  · rw [← Finset.mul_sum]
    exact hu x
  · rw [← Finset.mul_sum]
    exact hv y

omit [DecidableEq ι] in
theorem averageUnif_isCostLe [Nonempty Z] (P : Z → DualPair K f) {c : ℝ}
    (hu : ∀ x : ι → σ, (Fintype.card Z : ℝ)⁻¹ *
      ∑ z : Z, (∑ i : ι, ∑ k : K, (P z).u x i k * (P z).u x i k) ≤ c)
    (hv : ∀ y : ι → σ, (Fintype.card Z : ℝ)⁻¹ *
      ∑ z : Z, (∑ i : ι, ∑ k : K, (P z).v y i k * (P z).v y i k) ≤ c) :
    (averageUnif P).IsCostLe c := by
  classical
  refine average_isCostLe P _ _ _ (fun x => ?_) (fun y => ?_)
  · rw [← Finset.mul_sum]
    exact hu x
  · rw [← Finset.mul_sum]
    exact hv y

end DualPair

end QuantumQueryComplexity

end SourceScanAverage

section SourceScanDefs

/-!
# Weighted scans: the decision-tree dual with black/red weights

A **scan** orders the coordinates and records, for each input and coordinate,
the *branch* taken there and its *colour*.  This is the algebraic core of
Beigi–Taghavi's generalized-decision-tree dual, with weights assigned to nodes.

The point of the reformulation used here is that a scan is
`SourceFirstDiff` applied to the **branch sequence** instead of the raw
input.  A tree node is exactly a branch-prefix, so "two paths agree until their
first different branch" is literally `card_firstDiffSet`, and no tree datatype is
needed.  Three conditions make the argument go through:

* `br_ne` — a differing branch forces a differing symbol, so the coordinate is
  visible to the adversary mask;
* `out_eq` — equal branch sequences force equal outputs, so the pairing is
  switched on whenever the outputs differ;
* `black_unique` — at most one branch at a node is black, which is what makes
  the two square-root weights cancel.

The colours are what the ordinary first-difference dual lacks.  `u` pays
`1 / W` at the branch it takes, while `v` pays `∑ W` over the *other* colours;
choosing `W` per coordinate then trades the two costs off against each other.
With constant weights this collapses back to `ADV±(f) ≤ 2 D(f)`; with
depth-dependent weights it is what removes the alphabet dependence from maximum
finding.
-/


namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- A scan of the coordinates: an order, and for each input the branch taken at
each coordinate together with its colour. -/
structure Scan (ι σ O Q : Type*) [Fintype ι] where
  /-- The order in which coordinates are scanned. -/
  rank : ι → Fin (Fintype.card ι)
  /-- The order is a genuine ordering. -/
  rank_inj : Function.Injective rank
  /-- The branch taken at each coordinate. -/
  br : (ι → σ) → ι → Q
  /-- Its colour: `false` is black, `true` is red. -/
  col : (ι → σ) → ι → Bool
  /-- The value computed. -/
  out : (ι → σ) → O
  /-- At the same node, a differing branch forces a differing symbol: the
  branches at a node partition the alphabet, so the branch is determined by the
  symbol read. -/
  br_ne : ∀ x y i, (∀ j, rank j < rank i → br x j = br y j) →
    br x i ≠ br y i → x i ≠ y i
  /-- Equal branch sequences force equal outputs. -/
  out_eq : ∀ x y, (∀ i, br x i = br y i) → out x = out y
  /-- At most one branch at each node is black. -/
  black_unique : ∀ x y i, col x i = false → col y i = false →
    (∀ j, rank j < rank i → br x j = br y j) → br x i = br y i

namespace Scan

variable (S : Scan ι σ O Q)

/-- The node reached before scanning `i`: the branches taken so far. -/
def node (x : ι → σ) (i : ι) : ι → Option Q :=
  fun j => if S.rank j < S.rank i then some (S.br x j) else none

omit [DecidableEq O] [DecidableEq Q] [DecidableEq ι] [DecidableEq σ] [Fintype O] [Fintype Q]
    [Fintype σ] in
lemma node_eq_iff {x y : ι → σ} {i : ι} :
    S.node x i = S.node y i ↔ ∀ j, S.rank j < S.rank i → S.br x j = S.br y j := by
  classical
  constructor
  · intro h j hj
    have hj' := congrFun h j
    simp only [node, ite_eq_left hj, Option.some.injEq] at hj'
    exact hj'
  · intro h
    funext j
    simp only [node]
    by_cases hj : S.rank j < S.rank i
    · rw [ite_eq_left hj, ite_eq_left hj, h j hj]
    · rw [ite_eq_right hj, ite_eq_right hj]

/-! ## Exactly one first divergence -/

/-- The coordinate at which two branch sequences first differ. -/
noncomputable def divSet (x y : ι → σ) : Finset ι :=
  Finset.univ.filter fun i => S.br x i ≠ S.br y i ∧ S.node x i = S.node y i

omit [DecidableEq O] [DecidableEq ι] [DecidableEq σ] [Fintype O] [Fintype Q] [Fintype σ] in
lemma card_divSet {x y : ι → σ} (h : S.br x ≠ S.br y) : (S.divSet x y).card = 1 := by
  classical
  have hD : (Finset.univ.filter fun i => S.br x i ≠ S.br y i).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact ⟨i, by simpa using hi⟩
  obtain ⟨i₀, hmem, hmin⟩ :=
    Finset.exists_min_image (Finset.univ.filter fun i => S.br x i ≠ S.br y i)
      S.rank hD
  rw [Finset.mem_filter] at hmem
  have hlow : ∀ j, S.rank j < S.rank i₀ → S.br x j = S.br y j := by
    intro j hj
    by_contra hne
    exact absurd (hmin j (by simpa using hne)) (by omega)
  rw [Finset.card_eq_one]
  refine ⟨i₀, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun i hi => ?_⟩⟩
  · simp only [divSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hmem.2, S.node_eq_iff.2 hlow⟩
  · simp only [divSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have h1 : S.rank i₀ ≤ S.rank i := hmin i (by simpa using hi.1)
    have h2 : ¬ S.rank i₀ < S.rank i := fun hlt =>
      hmem.2 (S.node_eq_iff.1 hi.2 i₀ hlt)
    exact S.rank_inj (le_antisymm (by omega) h1)

omit [DecidableEq O] [DecidableEq ι] [DecidableEq σ] [Fintype O] [Fintype Q] [Fintype σ] in
lemma card_divSet_of_out_ne {x y : ι → σ} (h : S.out x ≠ S.out y) :
    (S.divSet x y).card = 1 := by
  classical
  exact S.card_divSet fun hbr => h (S.out_eq x y (congrFun hbr))

end Scan

end QuantumQueryComplexity

end SourceScanDefs

section SourceScanDual

/-!
# The dual solution attached to a weighted scan

`u` sits at the branch it takes, weighted `1/√W`; `v` spreads over the *other*
colours, weighted `√W`.  At the first differing branch the two square roots
cancel — this is where `black_unique` is used, since it rules out both sides
taking a black branch at the same node, which would leave no common colour.

The resulting costs are

  `∑ i, ‖u x i‖² ≤ 4 ∑ i, 1 / W i (col x i)`,
  `∑ i, ‖v y i‖² ≤ 4 ∑ i, (W i true + if col y i then W i false else 0)`,

so the weights trade one side against the other.  Constant weights give the
first-difference dual back; the maximum scan will make them depend on depth.
-/


namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The dimension type: node, colour, branch gadget, output gadget. -/
abbrev ScanDim (ι O Q : Type*) := (ι → Option Q) × Bool × Option Q × Option O

namespace Scan

variable (S : Scan ι σ O Q) (W : ι → Bool → ℝ)

omit [DecidableEq O] [DecidableEq Q] in
/-- Splitting a sum over the four dimension components.  Stated with the
component functions explicit, so no higher-order unification is needed. -/
private lemma sum_four (a a' : (ι → Option Q) → ℝ) (b b' : Bool → ℝ)
    (c c' : Option Q → ℝ) (d d' : Option O → ℝ) :
    (∑ k : ScanDim ι O Q,
        (a k.1 * (b k.2.1 * (c k.2.2.1 * d k.2.2.2)))
          * (a' k.1 * (b' k.2.1 * (c' k.2.2.1 * d' k.2.2.2))))
      = (∑ p, a p * a' p) * ((∑ t, b t * b' t)
          * ((∑ q, c q * c' q) * (∑ o, d o * d' o))) := by
  have h : ∀ p t q o, (a p * (b t * (c q * d o))) * (a' p * (b' t * (c' q * d' o)))
      = (a p * a' p) * ((b t * b' t) * ((c q * c' q) * (d o * d' o))) := by
    intros; ring
  simp only [Fintype.sum_prod_type, h, ← Finset.mul_sum, ← Finset.sum_mul]

/-- The node component of `u` and of `v`. -/
def ndVec (x : ι → σ) (i : ι) (p : ι → Option Q) : ℝ :=
  if p = S.node x i then 1 else 0

/-- The colour component of `u`: mass at the colour actually taken. -/
noncomputable def colU (x : ι → σ) (i : ι) (c : Bool) : ℝ :=
  if c = S.col x i then (Real.sqrt (W i (S.col x i)))⁻¹ else 0

/-- The colour component of `v`: mass on every *other* colour. -/
noncomputable def colV (y : ι → σ) (i : ι) (c : Bool) : ℝ :=
  if S.col y i || c then Real.sqrt (W i c) else 0

omit [DecidableEq O] [DecidableEq σ] [Fintype O] [Fintype σ] in
lemma sum_ndVec (x y : ι → σ) (i : ι) :
    (∑ p : ι → Option Q, S.ndVec x i p * S.ndVec y i p)
      = if S.node x i = S.node y i then 1 else 0 := by
  classical
  simp only [ndVec]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
    show ((if p = S.node x i then (1 : ℝ) else 0) * if p = S.node y i then 1 else 0)
      = (if p = S.node x i then (if S.node x i = S.node y i then (1 : ℝ) else 0)
          else 0) from by
      by_cases h1 : p = S.node x i <;> by_cases h2 : p = S.node y i <;>
        simp [h1, h2]; grind]
  rw [Finset.sum_ite_eq' Finset.univ (S.node x i)
    fun _ => (if S.node x i = S.node y i then (1 : ℝ) else 0),
    ite_eq_left (Finset.mem_univ _)]

omit [DecidableEq O] [DecidableEq Q] [DecidableEq ι] [DecidableEq σ] [Fintype O] [Fintype Q]
    [Fintype σ] in
lemma sum_col (hW : ∀ i c, 0 < W i c) (x y : ι → σ) (i : ι) :
    (∑ c : Bool, S.colU W x i c * S.colV W y i c)
      = if S.col y i || S.col x i then 1 else 0 := by
  classical
  have hne : Real.sqrt (W i (S.col x i)) ≠ 0 := (Real.sqrt_pos.mpr (hW _ _)).ne'
  simp only [colU, colV]
  rw [Fintype.sum_bool]
  cases hx : S.col x i <;> cases hy : S.col y i <;>
    simp only [Bool.or_false, Bool.or_true,
      ite_true] <;> norm_num <;>
    rw [hx] at hne <;> field_simp

omit [DecidableEq O] [DecidableEq σ] [Fintype O] [Fintype σ] in
lemma sum_ndVec_sq (x : ι → σ) (i : ι) :
    (∑ p : ι → Option Q, S.ndVec x i p * S.ndVec x i p) = 1 := by
  classical
  simp only [ndVec]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
    show ((if p = S.node x i then (1 : ℝ) else 0) * if p = S.node x i then 1 else 0)
      = (if p = S.node x i then (1 : ℝ) else 0) from by
      by_cases h1 : p = S.node x i <;> simp [h1]]
  rw [Finset.sum_ite_eq' Finset.univ (S.node x i) fun _ => (1 : ℝ),
    ite_eq_left (Finset.mem_univ _)]

omit [DecidableEq O] [DecidableEq Q] [DecidableEq ι] [DecidableEq σ] [Fintype O] [Fintype Q]
    [Fintype σ] in
lemma sum_colU_sq (hW : ∀ i c, 0 < W i c) (x : ι → σ) (i : ι) :
    (∑ c : Bool, S.colU W x i c * S.colU W x i c) = (W i (S.col x i))⁻¹ := by
  classical
  have hpos := hW i (S.col x i)
  simp only [colU]
  rw [Fintype.sum_bool]
  cases hx : S.col x i <;>
    simp only [ite_true] <;> norm_num <;>
    rw [hx] at hpos <;>
    rw [← Real.sqrt_inv, Real.mul_self_sqrt (by positivity)]

omit [DecidableEq O] [DecidableEq Q] [DecidableEq ι] [DecidableEq σ] [Fintype O] [Fintype Q]
    [Fintype σ] in
lemma sum_colV_sq (hW : ∀ i c, 0 < W i c) (y : ι → σ) (i : ι) :
    (∑ c : Bool, S.colV W y i c * S.colV W y i c)
      = W i true + (if S.col y i then W i false else 0) := by
  classical
  simp only [colV]
  rw [Fintype.sum_bool]
  cases hy : S.col y i <;>
    simp only [Bool.false_or, Bool.true_or, ite_true] <;> norm_num <;>
    rw [Real.mul_self_sqrt (hW _ _).le];
    try rw [Real.mul_self_sqrt (hW _ _).le]

/-! ## The dual solution -/

/-- **The dual solution attached to a weighted scan.** -/
noncomputable def dual (hW : ∀ i c, 0 < W i c) :
    DualPair (ScanDim ι O Q) S.out where
  u x i := fun k => S.ndVec x i k.1 *
    (S.colU W x i k.2.1 * (phiVec (S.br x i) k.2.2.1 * phiVec (S.out x) k.2.2.2))
  v y i := fun k => S.ndVec y i k.1 *
    (S.colV W y i k.2.1 * (psiVec (S.br y i) k.2.2.1 * psiVec (S.out y) k.2.2.2))
  constraint x y := by
    classical
    have hpt : ∀ i : ι,
        (∑ k : ScanDim ι O Q,
          (S.ndVec x i k.1 * (S.colU W x i k.2.1 *
            (phiVec (S.br x i) k.2.2.1 * phiVec (S.out x) k.2.2.2))) *
          (S.ndVec y i k.1 * (S.colV W y i k.2.1 *
            (psiVec (S.br y i) k.2.2.1 * psiVec (S.out y) k.2.2.2))))
        = (if S.node x i = S.node y i then (1 : ℝ) else 0)
          * ((if S.col y i || S.col x i then (1 : ℝ) else 0)
            * ((if S.br x i = S.br y i then (0 : ℝ) else 1)
              * (if S.out x = S.out y then (0 : ℝ) else 1))) := by
      intro i
      rw [sum_four (S.ndVec x i) (S.ndVec y i) (S.colU W x i) (S.colV W y i)
        (phiVec (S.br x i)) (psiVec (S.br y i))
        (phiVec (S.out x)) (psiVec (S.out y)),
        S.sum_ndVec x y i, S.sum_col W hW x y i,
        sum_phiVec_mul_psiVec, sum_phiVec_mul_psiVec]
    simp only [hpt]
    -- each term is the indicator of the first divergence, times the output test
    have hterm : ∀ i : ι,
        (if x i = y i then (0 : ℝ)
          else (if S.node x i = S.node y i then (1 : ℝ) else 0)
            * ((if S.col y i || S.col x i then (1 : ℝ) else 0)
              * ((if S.br x i = S.br y i then (0 : ℝ) else 1)
                * (if S.out x = S.out y then (0 : ℝ) else 1))))
        = (if i ∈ S.divSet x y then (1 : ℝ) else 0)
          * (if S.out x = S.out y then (0 : ℝ) else 1) := by
      intro i
      have hmem : i ∈ S.divSet x y
          ↔ (S.br x i ≠ S.br y i ∧ S.node x i = S.node y i) := by
        simp [Scan.divSet]
      by_cases hnd : S.node x i = S.node y i
      · by_cases hbr : S.br x i = S.br y i
        · have h1 : i ∉ S.divSet x y := fun hc => (hmem.1 hc).1 hbr
          rw [ite_eq_right h1, zero_mul]
          by_cases hxy : x i = y i
          · rw [ite_eq_left hxy]
          · rw [ite_eq_right hxy, ite_eq_left hbr]
            ring
        · have hxy : x i ≠ y i := S.br_ne x y i (S.node_eq_iff.1 hnd) hbr
          have hcol : (S.col y i || S.col x i) = true := by
            by_contra hc
            simp only [Bool.or_eq_true, not_or] at hc
            exact hbr (S.black_unique x y i (by simpa using hc.2)
              (by simpa using hc.1) (S.node_eq_iff.1 hnd))
          have h2 : i ∈ S.divSet x y := hmem.2 ⟨hbr, hnd⟩
          rw [ite_eq_right hxy, ite_eq_right hbr, ite_eq_left hnd, ite_eq_left hcol, ite_eq_left h2]
          ring
      · have h1 : i ∉ S.divSet x y := fun hc => hnd (hmem.1 hc).2
        rw [ite_eq_right h1, zero_mul]
        by_cases hxy : x i = y i
        · rw [ite_eq_left hxy]
        · rw [ite_eq_right hxy, ite_eq_right hnd]
          ring
    simp only [hterm]
    rw [← Finset.sum_mul]
    by_cases hout : S.out x = S.out y
    · rw [ite_eq_left hout, mul_zero]
    · rw [ite_eq_right hout, mul_one, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul, S.card_divSet_of_out_ne hout,
        Nat.cast_one, mul_one]

omit [Fintype σ] in
/-- The exact `ℓ²` mass of `u` at one coordinate: the reciprocal weight of the
branch taken there.

Stated per coordinate, not just summed, because a *weighted* cost inserts a
different factor at each one. -/
lemma sum_dual_u_sq_coord (hW : ∀ i c, 0 < W i c) (x : ι → σ) (i : ι) :
    (∑ k : ScanDim ι O Q, (S.dual W hW).u x i k * (S.dual W hW).u x i k)
      = 4 * (W i (S.col x i))⁻¹ := by
  change (∑ k : ScanDim ι O Q,
    (S.ndVec x i k.1 * (S.colU W x i k.2.1 *
      (phiVec (S.br x i) k.2.2.1 * phiVec (S.out x) k.2.2.2))) *
    (S.ndVec x i k.1 * (S.colU W x i k.2.1 *
      (phiVec (S.br x i) k.2.2.1 * phiVec (S.out x) k.2.2.2)))) = _
  rw [sum_four (S.ndVec x i) (S.ndVec x i) (S.colU W x i) (S.colU W x i)
    (phiVec (S.br x i)) (phiVec (S.br x i)) (phiVec (S.out x)) (phiVec (S.out x)),
    S.sum_ndVec_sq x i, S.sum_colU_sq W hW x i, sum_phiVec_sq, sum_phiVec_sq]
  ring

omit [Fintype σ] in
/-- The exact `ℓ²` mass of `u` at an input: the reciprocal weights of the
branches taken. -/
lemma sum_dual_u_sq (hW : ∀ i c, 0 < W i c) (x : ι → σ) :
    (∑ i : ι, ∑ k : ScanDim ι O Q, (S.dual W hW).u x i k * (S.dual W hW).u x i k)
      = 4 * ∑ i : ι, (W i (S.col x i))⁻¹ := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => S.sum_dual_u_sq_coord W hW x i

omit [Fintype σ] in
/-- The exact `ℓ²` mass of `v` at one coordinate: the weights of the other
colours. -/
lemma sum_dual_v_sq_coord (hW : ∀ i c, 0 < W i c) (y : ι → σ) (i : ι) :
    (∑ k : ScanDim ι O Q, (S.dual W hW).v y i k * (S.dual W hW).v y i k)
      = 4 * (W i true + if S.col y i then W i false else 0) := by
  change (∑ k : ScanDim ι O Q,
    (S.ndVec y i k.1 * (S.colV W y i k.2.1 *
      (psiVec (S.br y i) k.2.2.1 * psiVec (S.out y) k.2.2.2))) *
    (S.ndVec y i k.1 * (S.colV W y i k.2.1 *
      (psiVec (S.br y i) k.2.2.1 * psiVec (S.out y) k.2.2.2)))) = _
  rw [sum_four (S.ndVec y i) (S.ndVec y i) (S.colV W y i) (S.colV W y i)
    (psiVec (S.br y i)) (psiVec (S.br y i)) (psiVec (S.out y)) (psiVec (S.out y)),
    S.sum_ndVec_sq y i, S.sum_colV_sq W hW y i, sum_psiVec_sq, sum_psiVec_sq]
  ring

omit [Fintype σ] in
/-- The exact `ℓ²` mass of `v` at an input: the weights of the other colours. -/
lemma sum_dual_v_sq (hW : ∀ i c, 0 < W i c) (y : ι → σ) :
    (∑ i : ι, ∑ k : ScanDim ι O Q, (S.dual W hW).v y i k * (S.dual W hW).v y i k)
      = 4 * ∑ i : ι, (W i true + if S.col y i then W i false else 0) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => S.sum_dual_v_sq_coord W hW y i

omit [Fintype σ] in
/-- **The weighted cost of the scan dual.**  Each coordinate contributes its own
factor `c i`, which is what a composition with subproblems of differing costs
consumes. -/
theorem dual_isWeightedCostLe (hW : ∀ i c, 0 < W i c) {c : ι → ℝ} {V : ℝ}
    (hu : ∀ x : ι → σ, (4 : ℝ) * ∑ i, c i * (W i (S.col x i))⁻¹ ≤ V)
    (hv : ∀ y : ι → σ, (4 : ℝ) * ∑ i, c i *
      (W i true + if S.col y i then W i false else 0) ≤ V) :
    (S.dual W hW).IsWeightedCostLe c V := by
  constructor
  · intro x
    refine le_trans (le_of_eq ?_) (hu x)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [S.sum_dual_u_sq_coord W hW x i]; ring
  · intro y
    refine le_trans (le_of_eq ?_) (hv y)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [S.sum_dual_v_sq_coord W hW y i]; ring

omit [Fintype σ] in
/-- The cost of the scan dual: `u` pays the reciprocal weight of the branch it
takes, `v` pays the weights of the other colours. -/
theorem dual_isCostLe (hW : ∀ i c, 0 < W i c) {c : ℝ}
    (hu : ∀ x : ι → σ, (4 : ℝ) * ∑ i, (W i (S.col x i))⁻¹ ≤ c)
    (hv : ∀ y : ι → σ, (4 : ℝ) *
      ∑ i, (W i true + if S.col y i then W i false else 0) ≤ c) :
    (S.dual W hW).IsCostLe c :=
  ⟨fun x => (S.sum_dual_u_sq W hW x).trans_le (hu x),
   fun y => (S.sum_dual_v_sq W hW y).trans_le (hv y)⟩

end Scan

end QuantumQueryComplexity

end SourceScanDual

section SourceScanMax

/-!
# The maximum scan

Scan the coordinates in a fixed order, keeping the largest value seen.  At each
step the branch is black when the new value does not beat the running maximum,
and is the red singleton `{x i}` when it does.

The branch label is taken to be the **running maximum after scanning `i`**,
`runAfter`.  This is what makes the three `Scan` conditions nearly free, and it
avoids induction entirely:

* the running maximum *before* `i` is the sup of the labels strictly before `i`,
  so equal branch prefixes give equal running maxima — no recursion needed;
* `br_ne` then says `a ⊔ x i ≠ a ⊔ y i → x i ≠ y i`, which is immediate;
* `black_unique` says two non-records at the same node take the same branch —
  both labels are just the running maximum `a`;
* `out_eq` holds because `maxFun x` is the sup of the labels.

A branch is red exactly when the step is a *strict record*.  That is the event
whose probability, over a uniformly random scan order, is at most `1/t` — the
estimate that will make the weighted cost `O(√n)`.
-/


namespace QuantumQueryComplexity

/-- `WithBot α` is definitionally `Option α`; mathlib carries no `Fintype`
instance for it, and the scan needs one because the branch labels are running
maxima. -/
instance instFintypeWithBot {A : Type*} [Fintype A] : Fintype (WithBot A) :=
  inferInstanceAs (Fintype (Option A))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## The running join

Nothing about the *running value* of a scan needs a linear order: it is a
supremum, so a `SemilatticeSup` suffices.  Keeping this section general is what
lets `upstream Scan/Join.lean` reuse it for products in a commutative
idempotent semigroup, where two values may be incomparable. -/

section Sup

variable [SemilatticeSup A]

/-- The coordinates scanned strictly before `i`. -/
def beforeSet (rk : ι → Fin (Fintype.card ι)) (i : ι) : Finset ι :=
  Finset.univ.filter fun j => rk j < rk i

/-- The running maximum strictly before `i` (`⊥` if nothing has been scanned). -/
def runBefore (rk : ι → Fin (Fintype.card ι)) (x : ι → A) (i : ι) : WithBot A :=
  (beforeSet rk i).sup fun j => (x j : WithBot A)

/-- The running maximum up to and including `i`. -/
def runAfter (rk : ι → Fin (Fintype.card ι)) (x : ι → A) (i : ι) : WithBot A :=
  runBefore rk x i ⊔ (x i : WithBot A)

omit [DecidableEq A] [DecidableEq ι] [Fintype A] [Nonempty ι] in
lemma le_runBefore {rk : ι → Fin (Fintype.card ι)} {x : ι → A} {i j : ι}
    (h : rk j < rk i) : (x j : WithBot A) ≤ runBefore rk x i :=
  Finset.le_sup (f := fun j => (x j : WithBot A))
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)

omit [DecidableEq A] [DecidableEq ι] [Fintype A] [Nonempty ι] in
lemma runBefore_le {rk : ι → Fin (Fintype.card ι)} {x : ι → A} {i : ι}
    {b : WithBot A} (h : ∀ j, rk j < rk i → (x j : WithBot A) ≤ b) :
    runBefore rk x i ≤ b :=
  Finset.sup_le fun j hj => h j (by simpa [beforeSet] using hj)

omit [DecidableEq A] [DecidableEq ι] [Fintype A] [Nonempty ι] in
lemma le_runAfter (rk : ι → Fin (Fintype.card ι)) (x : ι → A) (i : ι) :
    (x i : WithBot A) ≤ runAfter rk x i := le_sup_right

omit [DecidableEq A] [DecidableEq ι] [Fintype A] in
omit [Nonempty ι] in
/-- **The running maximum before `i` is the sup of the branch labels before
`i`.**  This is what replaces an induction on the scan order. -/
lemma runBefore_eq_sup_runAfter (rk : ι → Fin (Fintype.card ι)) (x : ι → A)
    (i : ι) :
    runBefore rk x i = (beforeSet rk i).sup fun j => runAfter rk x j := by
  classical
  refine le_antisymm (Finset.sup_le fun j hj => ?_) (Finset.sup_le fun j hj => ?_)
  · exact le_trans (le_runAfter rk x j) (Finset.le_sup hj)
  · have hj' : rk j < rk i := by simpa [beforeSet] using hj
    refine sup_le (runBefore_le fun j' hj'' => ?_) (le_runBefore hj')
    exact le_runBefore (lt_trans hj'' hj')

omit [DecidableEq A] [DecidableEq ι] [Fintype A] in
omit [Nonempty ι] in
/-- Equal branch prefixes give equal running maxima. -/
lemma runBefore_congr {rk : ι → Fin (Fintype.card ι)} {x y : ι → A} {i : ι}
    (h : ∀ j, rk j < rk i → runAfter rk x j = runAfter rk y j) :
    runBefore rk x i = runBefore rk y i := by
  classical
  rw [runBefore_eq_sup_runAfter, runBefore_eq_sup_runAfter]
  refine Finset.sup_congr rfl fun j hj => ?_
  exact h j (by simpa [beforeSet] using hj)

end Sup

/-! ## The maximum scan -/

variable [LinearOrder A]

omit [DecidableEq A] [DecidableEq ι] [Fintype A] in
/-- `maxFun` is the sup of the branch labels. -/
lemma maxFun_eq_sup_runAfter (rk : ι → Fin (Fintype.card ι)) (x : ι → A) :
    ((maxFun x : A) : WithBot A) = Finset.univ.sup fun i => runAfter rk x i := by
  classical
  refine le_antisymm ?_ (Finset.sup_le fun i _ => ?_)
  · obtain ⟨i, hi⟩ := exists_eq_maxFun x
    rw [← hi]
    exact le_trans (le_runAfter rk x i) (Finset.le_sup (Finset.mem_univ i))
  · refine sup_le (runBefore_le fun j _ => ?_) ?_
    · exact_mod_cast le_maxFun x j
    · exact_mod_cast le_maxFun x i

/-! ## The scan -/

/-- Whether scanning `i` sets a strict record. -/
def isRecord (rk : ι → Fin (Fintype.card ι)) (x : ι → A) (i : ι) : Bool :=
  decide (runBefore rk x i < (x i : WithBot A))

omit [DecidableEq A] [DecidableEq ι] [Fintype A] [Nonempty ι] in
lemma runAfter_eq_of_not_record {rk : ι → Fin (Fintype.card ι)} {x : ι → A}
    {i : ι} (h : isRecord rk x i = false) : runAfter rk x i = runBefore rk x i := by
  simp only [isRecord, decide_eq_false_iff_not, not_lt] at h
  exact sup_eq_left.2 h

/-- **The maximum scan**, for a given order of the coordinates and a given
*value map* `m : σ → A`.

The letters read by the queries need not be the values being maximised: a query
returns a whole letter `x i : σ`, and the quantity of interest is the largest
`m (x i)`.  This costs the construction nothing, because the three `Scan`
conditions only ever go in the direction "differing branch ⟹ differing letter",
and `m (x i) ≠ m (y i)` certainly forces `x i ≠ y i`.  A non-injective `m` is
therefore fine — which matters, since the entries of distinct letter matrices
routinely coincide. -/
noncomputable def maxScanMap (m : σ → A) (rk : ι → Fin (Fintype.card ι))
    (hrk : Function.Injective rk) : Scan ι σ A (WithBot A) where
  rank := rk
  rank_inj := hrk
  br x i := runAfter rk (fun j => m (x j)) i
  col x i := isRecord rk (fun j => m (x j)) i
  out x := maxFun fun j => m (x j)
  br_ne x y i hpre hbr := by
    intro hxy
    exact hbr (by rw [runAfter, runAfter, runBefore_congr hpre, hxy])
  out_eq x y h := by
    have : ((maxFun fun j => m (x j) : A) : WithBot A)
        = ((maxFun fun j => m (y j) : A) : WithBot A) := by
      rw [maxFun_eq_sup_runAfter rk, maxFun_eq_sup_runAfter rk]
      exact Finset.sup_congr rfl fun i _ => h i
    exact_mod_cast this
  black_unique x y i hx hy hpre := by
    rw [runAfter_eq_of_not_record hx, runAfter_eq_of_not_record hy,
      runBefore_congr hpre]

/-- The maximum scan of the input itself: the value map is the identity. -/
noncomputable def maxScan (rk : ι → Fin (Fintype.card ι))
    (hrk : Function.Injective rk) : Scan ι A A (WithBot A) :=
  maxScanMap id rk hrk

end QuantumQueryComplexity

end SourceScanMax

section SourceScanRecord

/-!
# The record lemma

Over a uniformly random scan order, the probability that step `t` sets a strict
record is at most `1 / (t + 1)`.

No bijection onto a quotient is needed.  For each position `s ≤ t` let
`domSet x t s` be the orders whose position-`s` coordinate *strictly dominates*
all the others at positions `≤ t`.  Then

* the `domSet x t s` for `s ≤ t` are **pairwise disjoint** — a strict dominator
  is unique;
* they are **equinumerous**, by composing an order with the transposition of
  positions `s` and `t`;
* `domSet x t t` is exactly the event "step `t` is a strict record".

So `(t + 1)` disjoint sets of equal size fit inside all the orders, giving
`(t + 1) * |record event| ≤ n!`.  Ties are handled for free: if the maximum
over the first `t + 1` positions is attained twice, *no* order is counted, which
only helps.

This is the one place where randomising the scan order earns its keep.  For a
fixed order an increasing input sets a record at every step.
-/


namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [LinearOrder A]

/-- A scan order: a bijection of the coordinates onto positions. -/
abbrev Order (ι : Type*) [Fintype ι] := ι ≃ Fin (Fintype.card ι)

/-- The orders whose position-`s` coordinate strictly dominates every other
coordinate at a position `≤ t`. -/
def domSet (x : ι → A) (t s : Fin (Fintype.card ι)) : Finset (Order ι) :=
  Finset.univ.filter fun e =>
    ∀ s' : Fin (Fintype.card ι), s' ≤ t → s' ≠ s → x (e.symm s') < x (e.symm s)

lemma mem_domSet {x : ι → A} {t s : Fin (Fintype.card ι)} {e : Order ι} :
    e ∈ domSet x t s ↔ ∀ s' : Fin (Fintype.card ι), s' ≤ t → s' ≠ s →
      x (e.symm s') < x (e.symm s) := by
  simp [domSet]

/-- A strict dominator is unique, so the sets are pairwise disjoint. -/
lemma domSet_disjoint (x : ι → A) (t : Fin (Fintype.card ι))
    {s₁ s₂ : Fin (Fintype.card ι)} (hne : s₁ ≠ s₂) (h1 : s₁ ≤ t) (h2 : s₂ ≤ t) :
    Disjoint (domSet x t s₁) (domSet x t s₂) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  have k1 := (mem_domSet.1 he₁) s₂ h2 (Ne.symm hne)
  have k2 := (mem_domSet.1 he₂) s₁ h1 hne
  exact absurd k1 (not_lt.2 k2.le)

/-- Swapping positions `s` and `t` matches the two dominance events. -/
lemma card_domSet_eq (x : ι → A) {t s : Fin (Fintype.card ι)} (hs : s ≤ t) :
    (domSet x t s).card = (domSet x t t).card := by
  classical
  refine Finset.card_nbij' (fun e => e.trans (Equiv.swap s t))
    (fun e => e.trans (Equiv.swap s t)) ?_ ?_ ?_ ?_
  · -- forward: dominance at `s` becomes dominance at `t`
    intro e he
    simp only [Finset.mem_coe] at he ⊢
    rw [mem_domSet] at he ⊢
    intro s' hs' hne
    have hswt : (Equiv.swap s t) t = s := Equiv.swap_apply_right s t
    have hkey : ∀ u : Fin (Fintype.card ι), u ≤ t → u ≠ t →
        (Equiv.swap s t) u ≤ t ∧ (Equiv.swap s t) u ≠ s := by
      intro u hu hut
      by_cases hus : u = s
      · rw [hus, Equiv.swap_apply_left]
        exact ⟨le_rfl, fun h => hut (hus.trans h.symm)⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hus hut]
        exact ⟨hu, hus⟩
    obtain ⟨hle, hnes⟩ := hkey s' hs' hne
    have := he ((Equiv.swap s t) s') hle hnes
    simpa [Equiv.symm_trans_apply, Equiv.symm_swap, hswt] using this
  · -- backward: the same map, since the transposition is an involution
    intro e he
    simp only [Finset.mem_coe] at he ⊢
    rw [mem_domSet] at he ⊢
    intro s' hs' hne
    have hsws : (Equiv.swap s t) s = t := Equiv.swap_apply_left s t
    have hkey : ∀ u : Fin (Fintype.card ι), u ≤ t → u ≠ s →
        (Equiv.swap s t) u ≤ t ∧ (Equiv.swap s t) u ≠ t := by
      intro u hu hus
      by_cases hut : u = t
      · rw [hut, Equiv.swap_apply_right]
        exact ⟨hs, fun h => hus (hut.trans h.symm)⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hus hut]
        exact ⟨hu, hut⟩
    obtain ⟨hle, hnet⟩ := hkey s' hs' hne
    have := he ((Equiv.swap s t) s') hle hnet
    simpa [Equiv.symm_trans_apply, Equiv.symm_swap, hsws] using this
  · intro e _
    simp [Equiv.trans_assoc]
  · intro e _
    simp [Equiv.trans_assoc]

/-- **The record bound in counting form.** -/
lemma card_domSet_mul_le (x : ι → A) (t : Fin (Fintype.card ι)) :
    ((t : ℕ) + 1) * (domSet x t t).card ≤ Fintype.card (Order ι) := by
  classical
  have hdisj : ((Finset.Iic t : Finset (Fin (Fintype.card ι))) : Set _).PairwiseDisjoint
      (fun s => domSet x t s) := by
    intro s₁ h1 s₂ h2 hne
    exact domSet_disjoint x t hne (Finset.mem_Iic.1 h1) (Finset.mem_Iic.1 h2)
  have hcard : ((Finset.Iic t).biUnion fun s => domSet x t s).card
      = ∑ s ∈ Finset.Iic t, (domSet x t s).card :=
    Finset.card_biUnion fun s₁ h1 s₂ h2 hne =>
      domSet_disjoint x t hne (Finset.mem_Iic.1 h1) (Finset.mem_Iic.1 h2)
  have hconst : ∑ s ∈ Finset.Iic t, (domSet x t s).card
      = ∑ _s ∈ Finset.Iic t, (domSet x t t).card :=
    Finset.sum_congr rfl fun s hs => card_domSet_eq x (Finset.mem_Iic.1 hs)
  calc ((t : ℕ) + 1) * (domSet x t t).card
      = ∑ _s ∈ Finset.Iic t, (domSet x t t).card := by
        rw [Finset.sum_const, Fin.card_Iic, smul_eq_mul]
    _ = ((Finset.Iic t).biUnion fun s => domSet x t s).card := by
        rw [hcard, hconst]
    _ ≤ Fintype.card (Order ι) := Finset.card_le_univ _

/-! ## Identifying the record event -/

omit [DecidableEq ι] in
lemma isRecord_eq_true_iff (x : ι → A) (e : Order ι) (i : ι) :
    isRecord (⇑e) x i = true ↔ ∀ j : ι, e j < e i → x j < x i := by
  rw [isRecord, decide_eq_true_iff, runBefore, Finset.sup_lt_iff (by simp)]
  constructor
  · intro h j hj
    exact_mod_cast h j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
  · intro h j hj
    exact_mod_cast h j (by simpa [beforeSet] using hj)

/-- **The record event is exactly the top dominance set.** -/
lemma isRecord_iff_mem_domSet (x : ι → A) (e : Order ι)
    (t : Fin (Fintype.card ι)) :
    isRecord (⇑e) x (e.symm t) = true ↔ e ∈ domSet x t t := by
  rw [isRecord_eq_true_iff, mem_domSet]
  constructor
  · intro h s' hs' hne
    refine h (e.symm s') ?_
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact lt_of_le_of_ne hs' hne
  · intro h j hj
    rw [Equiv.apply_symm_apply] at hj
    have := h (e j) (le_of_lt hj) (ne_of_lt hj)
    rwa [Equiv.symm_apply_apply] at this

/-- **The record lemma.**  At most a `1/(t+1)` fraction of scan orders make
step `t` a strict record. -/
theorem card_record_mul_le (x : ι → A) (t : Fin (Fintype.card ι)) :
    ((t : ℕ) + 1) *
        (Finset.univ.filter fun e : Order ι =>
          isRecord (⇑e) x (e.symm t) = true).card
      ≤ Fintype.card (Order ι) := by
  classical
  have : (Finset.univ.filter fun e : Order ι =>
      isRecord (⇑e) x (e.symm t) = true) = domSet x t t := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isRecord_iff_mem_domSet x e t
  rw [this]
  exact card_domSet_mul_le x t

end QuantumQueryComplexity

end SourceScanRecord

section SourceScanFinal

/-!
# `ADV±(MAX) = O(√n)`, with no alphabet dependence

Give the coordinate scanned at time `t` the
weights

  `W(t, black) = √(t+1)`,   `W(t, red) = 1/√(t+1)`,

and average the resulting scan duals over all scan orders.  A red branch is a
strict record, which by the record lemma happens for at most a `1/(t+1)`
fraction of orders, so at each time the two contributions balance:

  `√(t+1) · (fraction of records) + 1/√(t+1) ≤ 2/√(t+1)`,

and `∑_{t<n} 1/√(t+1) ≤ 2√n`.  Both squared masses are therefore `O(√n)`.

The bound is independent of the alphabet.  This is what the threshold/staircase
route could not achieve: there the pairing constraints force a γ₂ factorization
of the greater-than matrix, costing `Θ(log m)`.  The scan never compares two
alphabet symbols through an inner product — the comparison happens inside the
branch structure, and the dual only ever tests branch labels for *equality*.
-/


namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## The elementary sum -/

lemma inv_sqrt_le_two_mul_sub (t : ℕ) :
    (Real.sqrt (t + 1))⁻¹ ≤ 2 * (Real.sqrt (t + 1) - Real.sqrt t) := by
  have ha : Real.sqrt t * Real.sqrt t = (t : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hb : Real.sqrt ((t : ℝ) + 1) * Real.sqrt ((t : ℝ) + 1) = (t : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  have hbpos : 0 < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  rw [inv_le_iff_one_le_mul₀ hbpos]
  nlinarith [sq_nonneg (Real.sqrt ((t : ℝ) + 1) - Real.sqrt t),
    Real.sqrt_nonneg ((t : ℝ) + 1), Real.sqrt_nonneg (t : ℝ)]

/-- `∑_{t < n} 1/√(t+1) ≤ 2√n`, by telescoping. -/
lemma sum_inv_sqrt_le (n : ℕ) :
    (∑ t ∈ Finset.range n, (Real.sqrt (t + 1))⁻¹) ≤ 2 * Real.sqrt n := by
  calc (∑ t ∈ Finset.range n, (Real.sqrt (t + 1))⁻¹)
      ≤ ∑ t ∈ Finset.range n, 2 * (Real.sqrt (t + 1) - Real.sqrt t) :=
        Finset.sum_le_sum fun t _ => inv_sqrt_le_two_mul_sub t
    _ = 2 * Real.sqrt n := by
        have hcast : ∀ i : ℕ, Real.sqrt ((i : ℝ) + 1) = Real.sqrt ((i + 1 : ℕ) : ℝ) := by
          intro i; norm_cast
        simp only [hcast]
        rw [← Finset.mul_sum,
          Finset.sum_range_sub fun t : ℕ => Real.sqrt ((t : ℕ) : ℝ)]
        simp

lemma sum_inv_sqrt_fin_le (n : ℕ) :
    (∑ t : Fin n, (Real.sqrt ((t : ℕ) + 1))⁻¹) ≤ 2 * Real.sqrt n := by
  rw [Fin.sum_univ_eq_sum_range fun t : ℕ => (Real.sqrt ((t : ℝ) + 1))⁻¹]
  exact_mod_cast sum_inv_sqrt_le n

/-! ## The weights -/

/-- Depth-dependent weights: black is `√(t+1)`, red is `1/√(t+1)`. -/
noncomputable def scanWeight (e : Order ι) (i : ι) (c : Bool) : ℝ :=
  if c then (Real.sqrt ((e i : ℕ) + 1))⁻¹ else Real.sqrt ((e i : ℕ) + 1)

omit [DecidableEq ι] [Nonempty ι] in
lemma scanWeight_pos (e : Order ι) (i : ι) (c : Bool) : 0 < scanWeight e i c := by
  have h : (0 : ℝ) < Real.sqrt ((e i : ℕ) + 1) :=
    Real.sqrt_pos.mpr (by positivity)
  cases c <;> simp only [scanWeight, ite_true] <;> positivity

omit [DecidableEq A] [DecidableEq ι] [Fintype A] [Nonempty ι] in
/-- The `u`-side weight at a coordinate: `√(t+1)` on a record, `1/√(t+1)`
otherwise. -/
lemma scanWeight_inv (e : Order ι) (x : ι → A) (i : ι) :
    (scanWeight e i (isRecord (⇑e) x i))⁻¹
      = if isRecord (⇑e) x i then Real.sqrt ((e i : ℕ) + 1)
        else (Real.sqrt ((e i : ℕ) + 1))⁻¹ := by
  have h : (0 : ℝ) < Real.sqrt ((e i : ℕ) + 1) := Real.sqrt_pos.mpr (by positivity)
  cases hc : isRecord (⇑e) x i <;>
    simp only [scanWeight, ite_true] <;>
    simp [inv_inv]

omit [DecidableEq A] [DecidableEq ι] [Fintype A] [Nonempty ι] in
/-- The `v`-side weight at a coordinate. -/
lemma scanWeight_v (e : Order ι) (x : ι → A) (i : ι) :
    scanWeight e i true + (if isRecord (⇑e) x i then scanWeight e i false else 0)
      = (Real.sqrt ((e i : ℕ) + 1))⁻¹
        + if isRecord (⇑e) x i then Real.sqrt ((e i : ℕ) + 1) else 0 := by
  cases hc : isRecord (⇑e) x i <;> simp [scanWeight]

/-! ## Summing over the scan order -/

omit [DecidableEq ι] [Nonempty ι] in
/-- Reindexing a sum over coordinates as a sum over times. -/
lemma sum_over_times (e : Order ι) (F : Fin (Fintype.card ι) → ℝ) :
    (∑ i : ι, F (e i)) = ∑ t : Fin (Fintype.card ι), F t :=
  Fintype.sum_equiv e _ _ fun _ => rfl

omit [DecidableEq A] [Fintype A] [Nonempty ι] in
/-- **The key per-time estimate.**  Summed over all scan orders, the `u`-side
cost at time `t` is at most `2 / √(t+1)` times the number of orders. -/
lemma sum_orders_u_le (x : ι → A) (t : Fin (Fintype.card ι)) :
    (∑ e : Order ι, if isRecord (⇑e) x (e.symm t) then Real.sqrt ((t : ℕ) + 1)
        else (Real.sqrt ((t : ℕ) + 1))⁻¹)
      ≤ (Fintype.card (Order ι) : ℝ) * (2 * (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
  classical
  have hsq : Real.sqrt ((t : ℕ) + 1) * Real.sqrt ((t : ℕ) + 1) = ((t : ℕ) : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  have hpos : (0 : ℝ) < Real.sqrt ((t : ℕ) + 1) := Real.sqrt_pos.mpr (by positivity)
  set R := (Finset.univ.filter fun e : Order ι =>
    isRecord (⇑e) x (e.symm t) = true).card with hRdef
  set R' := (Finset.univ.filter fun e : Order ι =>
    ¬ (isRecord (⇑e) x (e.symm t) = true)).card with hR'def
  have hsplit : (∑ e : Order ι, if isRecord (⇑e) x (e.symm t) then
        Real.sqrt ((t : ℕ) + 1) else (Real.sqrt ((t : ℕ) + 1))⁻¹)
      = (R : ℝ) * Real.sqrt ((t : ℕ) + 1)
        + (R' : ℝ) * (Real.sqrt ((t : ℕ) + 1))⁻¹ := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
      nsmul_eq_mul, hRdef, hR'def]
  -- the record count is small, so the first piece is no bigger than the second
  have hcount : (((t : ℕ) : ℝ) + 1) * (R : ℝ) ≤ (Fintype.card (Order ι) : ℝ) := by
    exact_mod_cast card_record_mul_le x t
  have hkey : (R : ℝ) * Real.sqrt ((t : ℕ) + 1)
      ≤ (Fintype.card (Order ι) : ℝ) * (Real.sqrt ((t : ℕ) + 1))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_assoc, hsq]
    calc (R : ℝ) * (((t : ℕ) : ℝ) + 1) = (((t : ℕ) : ℝ) + 1) * (R : ℝ) := by ring
      _ ≤ (Fintype.card (Order ι) : ℝ) := hcount
  have hR' : (R' : ℝ) ≤ (Fintype.card (Order ι) : ℝ) := by
    rw [hR'def]
    exact_mod_cast Finset.card_le_univ _
  rw [hsplit]
  have h2 : (R' : ℝ) * (Real.sqrt ((t : ℕ) + 1))⁻¹
      ≤ (Fintype.card (Order ι) : ℝ) * (Real.sqrt ((t : ℕ) + 1))⁻¹ :=
    mul_le_mul_of_nonneg_right hR' (by positivity)
  linarith [hkey, h2]

omit [DecidableEq A] [Fintype A] in
omit [Nonempty ι] in
/-- The `v`-side analogue: at most `3 / √(t+1)` per order. -/
lemma sum_orders_v_le (x : ι → A) (t : Fin (Fintype.card ι)) :
    (∑ e : Order ι, ((Real.sqrt ((t : ℕ) + 1))⁻¹
        + if isRecord (⇑e) x (e.symm t) then Real.sqrt ((t : ℕ) + 1) else 0))
      ≤ (Fintype.card (Order ι) : ℝ) * (3 * (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
  classical
  have hpos : (0 : ℝ) < Real.sqrt ((t : ℕ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hle : ∀ e : Order ι,
      ((Real.sqrt ((t : ℕ) + 1))⁻¹
        + if isRecord (⇑e) x (e.symm t) then Real.sqrt ((t : ℕ) + 1) else 0)
      ≤ ((if isRecord (⇑e) x (e.symm t) then Real.sqrt ((t : ℕ) + 1)
            else (Real.sqrt ((t : ℕ) + 1))⁻¹) + (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
    intro e
    have hnn : (0 : ℝ) ≤ (Real.sqrt ((t : ℕ) + 1))⁻¹ := by positivity
    split_ifs <;> linarith
  calc (∑ e : Order ι, ((Real.sqrt ((t : ℕ) + 1))⁻¹
        + if isRecord (⇑e) x (e.symm t) then Real.sqrt ((t : ℕ) + 1) else 0))
      ≤ ∑ e : Order ι, ((if isRecord (⇑e) x (e.symm t) then Real.sqrt ((t : ℕ) + 1)
          else (Real.sqrt ((t : ℕ) + 1))⁻¹) + (Real.sqrt ((t : ℕ) + 1))⁻¹) :=
        Finset.sum_le_sum fun e _ => hle e
    _ = (∑ e : Order ι, if isRecord (⇑e) x (e.symm t) then Real.sqrt ((t : ℕ) + 1)
          else (Real.sqrt ((t : ℕ) + 1))⁻¹)
        + (Fintype.card (Order ι) : ℝ) * (Real.sqrt ((t : ℕ) + 1))⁻¹ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card (Order ι) : ℝ) * (2 * (Real.sqrt ((t : ℕ) + 1))⁻¹)
        + (Fintype.card (Order ι) : ℝ) * (Real.sqrt ((t : ℕ) + 1))⁻¹ := by
        gcongr
        exact sum_orders_u_le x t
    _ = (Fintype.card (Order ι) : ℝ) * (3 * (Real.sqrt ((t : ℕ) + 1))⁻¹) := by ring

/-! ## The theorem -/

-- the dimension type and the order Fintype make unification costly
omit [Fintype σ] in
/-- **`ADV±(MAX) ≤ 24 √n`, with no dependence on the alphabet**, for the maximum
of a *value map* applied to the letters.

Averaging the depth-weighted scan duals over all scan orders.  A red branch is a
strict record, which happens for at most a `1/(t+1)` fraction of orders, so the
two colour contributions balance at every time and the total is governed by
`∑_t 1/√(t+1) ≤ 2√n`.

Nothing about the bound sees `m`: neither its injectivity nor the size of the
alphabet `σ` of letters plays any role. -/
theorem exists_maxMap_dual_isCostLe (m : σ → A) :
    ∃ P : DualPair (Order ι × ScanDim ι A (WithBot A))
      (fun x : ι → σ => maxFun fun j => m (x j)),
      P.IsCostLe (24 * Real.sqrt (Fintype.card ι)) := by
  classical
  have : Nonempty (Order ι) := ⟨Fintype.equivFin ι⟩
  set N : ℝ := (Fintype.card (Order ι) : ℝ) with hNdef
  have hNpos : (0 : ℝ) < N := by rw [hNdef, Nat.cast_pos]; exact Fintype.card_pos
  set P : Order ι → DualPair (ScanDim ι A (WithBot A))
      (fun x : ι → σ => maxFun fun j => m (x j)) :=
    fun e => (maxScanMap m (⇑e) e.injective).dual (scanWeight e) (scanWeight_pos e)
    with hPdef
  refine ⟨DualPair.averageUnif P, ?_⟩
  refine DualPair.averageUnif_isCostLe P (fun x => ?_) (fun y => ?_)
  · -- the `u` side
    have hmass : ∀ e : Order ι,
        (∑ i : ι, ∑ k : ScanDim ι A (WithBot A), (P e).u x i k * (P e).u x i k)
          = 4 * ∑ t : Fin (Fintype.card ι),
            (if isRecord (⇑e) (fun j => m (x j)) (e.symm t) then
                Real.sqrt ((t : ℕ) + 1)
              else (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
      intro e
      rw [hPdef, Scan.sum_dual_u_sq]
      congr 1
      rw [← sum_over_times e fun t =>
        if isRecord (⇑e) (fun j => m (x j)) (e.symm t) then
        Real.sqrt ((t : ℕ) + 1) else (Real.sqrt ((t : ℕ) + 1))⁻¹]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Equiv.symm_apply_apply]
      exact scanWeight_inv e (fun j => m (x j)) i
    have hstep : (∑ e : Order ι, ∑ i : ι, ∑ k : ScanDim ι A (WithBot A),
        (P e).u x i k * (P e).u x i k) ≤ N * (24 * Real.sqrt (Fintype.card ι)) := by
      calc (∑ e : Order ι, ∑ i : ι, ∑ k : ScanDim ι A (WithBot A),
            (P e).u x i k * (P e).u x i k)
          = ∑ e : Order ι, 4 * ∑ t : Fin (Fintype.card ι),
              (if isRecord (⇑e) (fun j => m (x j)) (e.symm t) then
                  Real.sqrt ((t : ℕ) + 1)
                else (Real.sqrt ((t : ℕ) + 1))⁻¹) :=
            Finset.sum_congr rfl fun e _ => hmass e
        _ = 4 * ∑ t : Fin (Fintype.card ι), ∑ e : Order ι,
              (if isRecord (⇑e) (fun j => m (x j)) (e.symm t) then
                  Real.sqrt ((t : ℕ) + 1)
                else (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
            rw [← Finset.mul_sum, Finset.sum_comm]
        _ ≤ 4 * ∑ t : Fin (Fintype.card ι), N * (2 * (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
            gcongr with t
            exact sum_orders_u_le (fun j => m (x j)) t
        _ = 4 * (N * 2 * ∑ t : Fin (Fintype.card ι), (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
            congr 1
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun t _ => by ring
        _ ≤ 4 * (N * 2 * (2 * Real.sqrt (Fintype.card ι))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (sum_inv_sqrt_fin_le (Fintype.card ι)) (by positivity)) (by norm_num)
        _ ≤ N * (24 * Real.sqrt (Fintype.card ι)) := by
            have : (0:ℝ) ≤ N * Real.sqrt (Fintype.card ι) := by positivity
            nlinarith [this]
    calc N⁻¹ * (∑ e : Order ι, ∑ i : ι, ∑ k : ScanDim ι A (WithBot A),
          (P e).u x i k * (P e).u x i k)
        ≤ N⁻¹ * (N * (24 * Real.sqrt (Fintype.card ι))) := by
          exact mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 24 * Real.sqrt (Fintype.card ι) := by field_simp
  · -- the `v` side
    have hmass : ∀ e : Order ι,
        (∑ i : ι, ∑ k : ScanDim ι A (WithBot A), (P e).v y i k * (P e).v y i k)
          = 4 * ∑ t : Fin (Fintype.card ι),
            ((Real.sqrt ((t : ℕ) + 1))⁻¹
              + if isRecord (⇑e) (fun j => m (y j)) (e.symm t) then
                  Real.sqrt ((t : ℕ) + 1) else 0) := by
      intro e
      rw [hPdef, Scan.sum_dual_v_sq]
      congr 1
      rw [← sum_over_times e fun t => (Real.sqrt ((t : ℕ) + 1))⁻¹
        + if isRecord (⇑e) (fun j => m (y j)) (e.symm t) then
            Real.sqrt ((t : ℕ) + 1) else 0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Equiv.symm_apply_apply]
      exact scanWeight_v e (fun j => m (y j)) i
    have hstep : (∑ e : Order ι, ∑ i : ι, ∑ k : ScanDim ι A (WithBot A),
        (P e).v y i k * (P e).v y i k) ≤ N * (24 * Real.sqrt (Fintype.card ι)) := by
      calc (∑ e : Order ι, ∑ i : ι, ∑ k : ScanDim ι A (WithBot A),
            (P e).v y i k * (P e).v y i k)
          = ∑ e : Order ι, 4 * ∑ t : Fin (Fintype.card ι),
              ((Real.sqrt ((t : ℕ) + 1))⁻¹
                + if isRecord (⇑e) (fun j => m (y j)) (e.symm t) then
                    Real.sqrt ((t : ℕ) + 1) else 0) :=
            Finset.sum_congr rfl fun e _ => hmass e
        _ = 4 * ∑ t : Fin (Fintype.card ι), ∑ e : Order ι,
              ((Real.sqrt ((t : ℕ) + 1))⁻¹
                + if isRecord (⇑e) (fun j => m (y j)) (e.symm t) then
                    Real.sqrt ((t : ℕ) + 1) else 0) := by
            rw [← Finset.mul_sum, Finset.sum_comm]
        _ ≤ 4 * ∑ t : Fin (Fintype.card ι), N * (3 * (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
            gcongr with t
            exact sum_orders_v_le (fun j => m (y j)) t
        _ = 4 * (N * 3 * ∑ t : Fin (Fintype.card ι), (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
            congr 1
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun t _ => by ring
        _ ≤ 4 * (N * 3 * (2 * Real.sqrt (Fintype.card ι))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (sum_inv_sqrt_fin_le (Fintype.card ι)) (by positivity)) (by norm_num)
        _ = N * (24 * Real.sqrt (Fintype.card ι)) := by ring
    calc N⁻¹ * (∑ e : Order ι, ∑ i : ι, ∑ k : ScanDim ι A (WithBot A),
          (P e).v y i k * (P e).v y i k)
        ≤ N⁻¹ * (N * (24 * Real.sqrt (Fintype.card ι))) := by
          exact mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 24 * Real.sqrt (Fintype.card ι) := by field_simp

/-- The maximum of the input itself: the value map is the identity. -/
theorem exists_maxFun_dual_isCostLe :
    ∃ P : DualPair (Order ι × ScanDim ι A (WithBot A)) (maxFun : (ι → A) → A),
      P.IsCostLe (24 * Real.sqrt (Fintype.card ι)) :=
  exists_maxMap_dual_isCostLe (ι := ι) (A := A) (σ := A) id

/-- **`ADV±(MAX) ≤ 24 √n`**, with no dependence on the alphabet. -/
theorem advPM_maxFun_le_sqrt :
    advPM (maxFun : (ι → A) → A) ≤ 24 * Real.sqrt (Fintype.card ι) := by
  obtain ⟨P, hP⟩ := exists_maxFun_dual_isCostLe (ι := ι) (A := A)
  exact advPM_le_of_dualPair P (by positivity) hP

end QuantumQueryComplexity

end SourceScanFinal

section SourceHasDual

/-!
# Bundled dual solutions

A divide-and-conquer construction builds one dual solution out of many, and the
dimension types of the pieces are all different: a maximum over a block of `q`
positions carries `Order` and `ScanDim` types built from that block, a
first-difference combination carries prefix and output gadgets, and a recursive
call carries whatever its own subtree produced.  Threading those types through a
recursion requires a `Sigma` type and `DualPair.embedDim` to combine the
different finite dimensions.

So we hide the dimension:

  `HasDual f c` — *some* feasible dual solution for `f` has cost at most `c`;
  `HasWeightedDual f c V` — *some* solution has `c`-weighted cost at most `V`.

Every construction of `SourcePullback`, `SourceFirstDiff`, and `SourceComposeShared` is
restated at this level, and the `Sigma`-plus-`embedDim` step happens exactly once,
inside `HasWeightedDual.composeShared`.  What is left are two combinators that
say what divide-and-conquer actually does:

* `HasDual.combine` — evaluate finitely many subproblems and feed the results to
  an **arbitrary** outer function, at cost `2 ∑ₚ cₚ`;
* `HasDual.max` — take the maximum of `q` equally expensive subproblems, at cost
  `24 √q · c`, with no dependence on the alphabet of values.

Dimension types are pinned to `Type`; every construction in this development
produces one (`Fin`, `Order`, `ScanDim`, products, sums and sigmas of these).
-/


namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {O : Type} [DecidableEq O]

/-! ## The two predicates -/

/-- `f` has a feasible dual solution of cost at most `c`. -/
@[expose]
def HasDual {ι : Type} [Fintype ι] {σ : Type} [DecidableEq σ] {O : Type}
    [DecidableEq O] (f : (ι → σ) → O) (c : ℝ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (P : DualPair K f), P.IsCostLe c

/-- `f` has a feasible dual solution of `c`-weighted cost at most `V`. -/
def HasWeightedDual {ι : Type} [Fintype ι] {σ : Type} [DecidableEq σ] {O : Type}
    [DecidableEq O] (f : (ι → σ) → O) (c : ι → ℝ) (V : ℝ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (P : DualPair K f), P.IsWeightedCostLe c V

variable {f g : (ι → σ) → O} {c d : ℝ}

omit [DecidableEq ι] [Fintype σ] in
lemma hasDual_of_dualPair {K : Type} [Fintype K] (P : DualPair K f)
    (h : P.IsCostLe c) : HasDual f c := ⟨K, inferInstance, P, h⟩

omit [DecidableEq ι] [Fintype σ] in
lemma hasWeightedDual_of_dualPair {K : Type} [Fintype K] {w : ι → ℝ} {V : ℝ}
    (P : DualPair K f) (h : P.IsWeightedCostLe w V) : HasWeightedDual f w V :=
  ⟨K, inferInstance, P, h⟩

omit [DecidableEq ι] [Fintype σ] in
lemma HasDual.mono (h : HasDual f c) (hcd : c ≤ d) : HasDual f d := by
  classical
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P, hP.mono hcd⟩

omit [DecidableEq ι] [Fintype σ] in
lemma HasWeightedDual.mono {w : ι → ℝ} {V V' : ℝ} (h : HasWeightedDual f w V)
    (hV : V ≤ V') : HasWeightedDual f w V' := by
  obtain ⟨K, hK, P, hP⟩ := h
  refine ⟨K, hK, P, fun x => ?_, fun x => ?_⟩
  · exact (hP.1 x).trans hV
  · exact (hP.2 x).trans hV

omit [DecidableEq ι] [Fintype σ] in
lemma HasDual.nonneg [Nonempty σ] (h : HasDual f c) : 0 ≤ c := by
  classical
  obtain ⟨K, hK, P, hP⟩ := h
  exact DualPair.isCostLe_nonneg hP

/-- **Weak duality, bundled.** -/
theorem advPM_le_of_hasDual (hc : 0 ≤ c) (h : HasDual f c) :
    advPM f ≤ c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact advPM_le_of_dualPair P hc hP

/-! ## Constant weights

The one quantitative fact linking the two predicates: an ordinary bound `V`
*is* a constant-weight bound `c₀ V`.  This is what lets a family of equally
expensive subproblems be fed to an outer solution whose cost was measured
without weights. -/

omit [DecidableEq ι] [Fintype σ] in
lemma DualPair.isWeightedCostLe_const {K : Type} [Fintype K] {P : DualPair K f}
    {V c₀ : ℝ} (hc₀ : 0 ≤ c₀) (h : P.IsCostLe V) :
    P.IsWeightedCostLe (fun _ => c₀) (c₀ * V) := by
  constructor
  · intro x
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (h.1 x) hc₀
  · intro x
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (h.2 x) hc₀

omit [DecidableEq ι] [Fintype σ] in
lemma HasDual.weighted_const {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (h : HasDual f c) :
    HasWeightedDual f (fun _ => c₀) (c₀ * c) := by
  classical
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P, DualPair.isWeightedCostLe_const hc₀ hP⟩

omit [DecidableEq ι] [Fintype σ] in
lemma DualPair.isCostLe_of_isWeightedCostLe_one {K : Type} [Fintype K]
    {P : DualPair K f} {V : ℝ} (h : P.IsWeightedCostLe (fun _ => 1) V) :
    P.IsCostLe V :=
  ⟨fun x => by simpa using h.1 x, fun x => by simpa using h.2 x⟩

/-! ## Transport -/

omit [DecidableEq ι] [Fintype σ] in
lemma HasDual.ofEq (hfg : ∀ x, f x = g x) (h : HasDual f c) : HasDual g c := by
  classical
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.ofEq hfg, DualPair.ofEq_isCostLe hfg hP⟩

omit [DecidableEq ι] [Fintype σ] in
/-- **A dual solution only sees which inputs share an output value.**

The feasibility constraint reads `= if f x = f y then 0 else 1`, so nothing but
the partition of inputs into level sets enters.  Two functions inducing the same
partition therefore have the same dual solutions, at the same cost — even when
their output *types* are different.  This is what makes it harmless to recode an
output into a finite type. -/
lemma HasDual.ofKer {O' : Type} [DecidableEq O'] {f' : (ι → σ) → O'}
    (hker : ∀ x y, f x = f y ↔ f' x = f' y) (h : HasDual f c) : HasDual f' c := by
  obtain ⟨K, hK, P, hP⟩ := h
  have hcon : ∀ x y : ι → σ,
      (∑ i, if x i = y i then (0 : ℝ) else ∑ k, P.u x i k * P.v y i k)
        = if f' x = f' y then 0 else 1 := by
    intro x y
    rw [P.constraint x y]
    by_cases hxy : f x = f y
    · rw [ite_eq_left hxy, ite_eq_left ((hker x y).1 hxy)]
    · rw [ite_eq_right hxy, ite_eq_right fun hc => hxy ((hker x y).2 hc)]
  exact ⟨K, hK, ⟨P.u, P.v, hcon⟩, hP.1, hP.2⟩

omit [DecidableEq ι] [Fintype σ] in
/-- A dual solution restricted to a block of coordinates: injectivity of the
inclusion is what keeps the cost unchanged. -/
lemma HasDual.pullback {κ : Type} [Fintype κ] {e : κ → ι}
    (he : Function.Injective e) {f : (κ → σ) → O} (h : HasDual f c) :
    HasDual (pullbackFun e f) c := by
  classical
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.pullback he, DualPair.pullback_isCostLe he P hP⟩

omit [DecidableEq ι] [Fintype σ] in
/-- **A dual solution restricted along a padding.**  A function of `n` letters is
a function of `N ≥ n` letters whose last `N - n` are frozen at known values, and
freezing costs nothing. -/
lemma HasDual.restrict {κ σ' : Type} [Fintype κ] [DecidableEq σ']
    {e : ι → κ} (he : Function.Injective e) {Φ : (ι → σ) → κ → σ'}
    (hin : ∀ (x y : ι → σ) (i : ι), Φ x (e i) = Φ y (e i) ↔ x i = y i)
    (hout : ∀ (x y : ι → σ) (j : κ), (∀ i, e i ≠ j) → Φ x j = Φ y j)
    {F : (κ → σ') → O} (h : HasDual F c) : HasDual (fun x => F (Φ x)) c := by
  classical
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.restrict he hin hout,
    DualPair.restrict_isCostLe he hin hout P hP⟩

omit [DecidableEq ι] [Fintype σ] in
/-- Recoding the input alphabet along an injection. -/
lemma HasDual.alphaMap {σ' : Type} [DecidableEq σ'] {m : σ → σ'}
    (hm : Function.Injective m) {f : (ι → σ') → O} (h : HasDual f c) :
    HasDual (alphaFun m f) c := by
  classical
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.alphaMap hm, DualPair.alphaMap_isCostLe hm P hP⟩

omit [DecidableEq ι] [Fintype σ] in
/-- A function that never changes value costs nothing: both vector families are
zero, and every dual constraint reads `0 = 0`. -/
lemma hasDual_const (hf : ∀ x y, f x = f y) : HasDual f 0 := by
  refine ⟨Unit, inferInstance, ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun x y => ?_⟩,
    ⟨fun x => ?_, fun x => ?_⟩⟩
  · rw [ite_eq_left (hf x y)]
    exact Finset.sum_eq_zero fun i _ => by
      by_cases h : x i = y i
      · rw [ite_eq_left h]
      · rw [ite_eq_right h]
        exact Finset.sum_eq_zero fun k _ => by ring
  · exact le_of_eq (Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun k _ => by ring)
  · exact le_of_eq (Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun k _ => by ring)

omit [DecidableEq ι] [Fintype σ] in
/-- The zero solution has weighted cost zero for *every* weight vector, whatever
its sign. -/
lemma hasWeightedDual_const {w : ι → ℝ} (hf : ∀ x y, f x = f y) :
    HasWeightedDual f w 0 := by
  refine ⟨Unit, inferInstance, ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun x y => ?_⟩,
    fun x => ?_, fun x => ?_⟩
  · rw [ite_eq_left (hf x y)]
    exact Finset.sum_eq_zero fun i _ => by
      by_cases h : x i = y i
      · rw [ite_eq_left h]
      · rw [ite_eq_right h]
        exact Finset.sum_eq_zero fun k _ => by ring
  · exact le_of_eq (Finset.sum_eq_zero fun i _ => by
      rw [Finset.sum_eq_zero fun k _ => by ring, mul_zero])
  · exact le_of_eq (Finset.sum_eq_zero fun i _ => by
      rw [Finset.sum_eq_zero fun k _ => by ring, mul_zero])

omit [DecidableEq ι] [Fintype σ] in
/-- `HasDual.ofKer` for the weighted predicate: recoding the output changes
neither the feasible solutions nor their cost. -/
lemma HasWeightedDual.ofKer {O' : Type} [DecidableEq O'] {f' : (ι → σ) → O'}
    {w : ι → ℝ} {V : ℝ} (hker : ∀ x y, f x = f y ↔ f' x = f' y)
    (h : HasWeightedDual f w V) : HasWeightedDual f' w V := by
  obtain ⟨K, hK, P, hP⟩ := h
  have hcon : ∀ x y : ι → σ,
      (∑ i, if x i = y i then (0 : ℝ) else ∑ k, P.u x i k * P.v y i k)
        = if f' x = f' y then 0 else 1 := by
    intro x y
    rw [P.constraint x y]
    by_cases hxy : f x = f y
    · rw [ite_eq_left hxy, ite_eq_left ((hker x y).1 hxy)]
    · rw [ite_eq_right hxy, ite_eq_right fun hc => hxy ((hker x y).2 hc)]
  exact ⟨K, hK, ⟨P.u, P.v, hcon⟩, hP.1, hP.2⟩

/-! ## Composition with shared inputs

This is the only place where dimension types are unified.  The subproblems'
solutions live in types `K p` depending on `p`; the sigma type `Σ p, K p` holds
them all, and `DualPair.embedDim` moves each into it by padding with zeros, at
no cost. -/

section Shared

variable {P V : Type} [Fintype P] [DecidableEq P] [DecidableEq V]
variable {h : (P → V) → O} {g : P → (ι → σ) → V}

omit [DecidableEq P] [DecidableEq ι] [Fintype σ] in
/-- **Shared-input composition, bundled.**  An outer solution of `c`-weighted
cost `Vout` and subproblem solutions of costs `c p` compose to cost `Vout`. -/
theorem HasWeightedDual.composeShared {c : P → ℝ} {Vout : ℝ}
    (hQ : HasWeightedDual h c Vout)
    (hg : ∀ p, HasDual (g p) (c p)) : HasDual (sharedFun h g) Vout := by
  classical
  obtain ⟨K, hK, Q, hQ'⟩ := hQ
  choose Kp instKp R hR using hg
  let : ∀ p, Fintype (Kp p) := instKp
  let : ∀ p, DecidableEq (Kp p) := fun p => Classical.decEq _
  let : DecidableEq ((p : P) × Kp p) := Classical.decEq _
  refine ⟨P × K × ((p : P) × Kp p), inferInstance,
    Q.composeShared fun p => (R p).embedDim (sigma_mk_injective (i := p)), ?_⟩
  exact DualPair.composeShared_isCostLe _ _ hQ' fun p =>
    DualPair.embedDim_isCostLe _ _ (hR p)

end Shared

/-! ## The two combinators -/

omit [DecidableEq ι] [Fintype σ] in
/-- **Feed finitely many subproblems to an arbitrary outer function.**

The first-difference dual is feasible for *any* outer function, so nothing about
`h` is assumed: it may add two tropical path weights, take a maximum of level
summaries, or assemble a whole matrix out of its entries.  The price is a factor
`2` on the total of the subproblem costs. -/
theorem HasDual.combine {P V : Type} [Fintype P]
    [DecidableEq V] (h : (P → V) → O) {g : P → (ι → σ) → V}
    {c : P → ℝ} (hg : ∀ p, HasDual (g p) (c p)) [Finite O] [Finite V] :
    HasDual (fun x => h fun p => g p x) (2 * ∑ p, c p) := by
  classical
  let := Fintype.ofFinite O
  let := Fintype.ofFinite V
  exact HasWeightedDual.composeShared
      (hasWeightedDual_of_dualPair (firstDiffDual h)
        (firstDiffDual_isWeightedCostLe h c)) hg

omit [DecidableEq ι] [Fintype σ] in
/-- **The maximum of equally expensive subproblems.**

`24 √q` is the alphabet-free cost of maximum finding on `q` coordinates
(`SourceScanFinal`); with constant weights it turns `q` subproblems of
cost `c₀` into their maximum at cost `24 √q · c₀`.  The values compared may range
over any finite linear order, and the bound does not see how large it is. -/
theorem HasDual.max {P A : Type} [Fintype P] [Nonempty P]
     [DecidableEq A] [LinearOrder A] {g : P → (ι → σ) → A} {c₀ : ℝ}
    (hc₀ : 0 ≤ c₀) (hg : ∀ p, HasDual (g p) c₀) [Finite A] :
    HasDual (fun x => maxFun fun p => g p x)
      (c₀ * (24 * Real.sqrt (Fintype.card P))) := by
  classical
  let := Fintype.ofFinite A
  obtain ⟨Q, hQ⟩ := exists_maxFun_dual_isCostLe (ι := P) (A := A)
  exact HasWeightedDual.composeShared
    (hasWeightedDual_of_dualPair Q (DualPair.isWeightedCostLe_const hc₀ hQ))
    hg

/-! ## Maximum of a value map over a block of coordinates

The base case of every divide-and-conquer over letters: a query returns a whole
letter, and the quantity wanted is the largest value of some map on the letters
read in a given block. -/

omit [DecidableEq ι] [Fintype σ] in
/-- The maximum of `m` over the letters, as a bundled dual. -/
theorem hasDual_maxMap {A : Type} [Nonempty ι]
    [DecidableEq A] [LinearOrder A] (m : σ → A) [Finite A] :
    HasDual (fun x : ι → σ => maxFun fun j => m (x j))
      (24 * Real.sqrt (Fintype.card ι)) := by
  classical
  let := Fintype.ofFinite A
  obtain ⟨P, hP⟩ := exists_maxMap_dual_isCostLe (ι := ι) (A := A) (σ := σ) m
  exact ⟨_, inferInstance, P, hP⟩

omit [DecidableEq ι] in
/-- `MAX` itself, as a bundled dual: `hasDual_maxMap` at the identity value
map, with the alphabet the finite linear order being maximized.  The
operational `Θ(√n)` endpoints extracted from these certificates live in
`upstream Quantum/MaxApplications.lean`. -/
theorem hasDual_maxFun {A : Type} [Nonempty ι]
    [DecidableEq A] [LinearOrder A] [Finite A] :
    HasDual (maxFun : (ι → A) → A) (24 * Real.sqrt (Fintype.card ι)) := by
  classical
  let := Fintype.ofFinite A
  obtain ⟨P, hP⟩ := exists_maxFun_dual_isCostLe (ι := ι) (A := A)
  exact ⟨_, inferInstance, P, hP⟩

omit [DecidableEq ι] [Fintype σ] in
/-- The maximum of `m` over the letters in a block, at a cost governed by the
size of the block. -/
theorem hasDual_maxMap_block {κ A : Type} [Fintype κ]
    [Nonempty κ] [DecidableEq A] [LinearOrder A] {e : κ → ι}
    (he : Function.Injective e) (m : σ → A) [Finite A] :
    HasDual (fun x : ι → σ => maxFun fun j : κ => m (x (e j)))
      (24 * Real.sqrt (Fintype.card κ)) := by
  classical
  let := Fintype.ofFinite A
  exact (hasDual_maxMap (ι := κ) (σ := σ) m).pullback he

/-! ## Infinite value types

The scan and the first-difference gadget both need *finite* branch and output
types, while the values a divide-and-conquer computes naturally live somewhere
infinite — tropical path weights are elements of `ℝ ∪ {-∞}`.

Nothing is lost.  The input space `ι → σ` is finite, so every function on it has
finite range; restricting to that range changes neither the level sets nor, by
`HasDual.ofKer`, the dual solutions.  The three combinators are therefore
restated with no finiteness assumption on the values at all, and it is these
versions that a recursion over tropical matrices consumes. -/

section FiniteRange

/-- A strictly monotone map commutes with `maxFun`.  Used to compare a maximum
computed inside a finite subtype of values with the same maximum computed
outside it. -/
lemma maxFun_strictMono {κ A B : Type} [Fintype κ] [Nonempty κ] [LinearOrder A]
    [LinearOrder B] {φ : A → B} (hφ : StrictMono φ) (G : κ → A) :
    (maxFun fun j => φ (G j)) = φ (maxFun G) := by
  obtain ⟨j, hj⟩ := exists_eq_maxFun G
  exact maxFun_eq_iff.2 ⟨⟨j, by rw [hj]⟩, fun j => hφ.monotone (le_maxFun G j)⟩

omit [DecidableEq ι] [Fintype σ] in
/-- **The maximum of equally expensive subproblems, over any linear order of
values.** -/
theorem HasDual.max' {Pi A : Type} [Fintype Pi] [Nonempty Pi]
    [DecidableEq A] [LinearOrder A] {g : Pi → (ι → σ) → A} {c₀ : ℝ}
    (hc₀ : 0 ≤ c₀) (hg : ∀ p, HasDual (g p) c₀) [Finite σ] :
    HasDual (fun x => maxFun fun p => g p x)
      (c₀ * (24 * Real.sqrt (Fintype.card Pi))) := by
  classical
  let := Fintype.ofFinite σ
  set S : Finset A :=
    Finset.image (fun q : Pi × (ι → σ) => g q.1 q.2) Finset.univ with hSdef
  have hmem : ∀ (p : Pi) (x : ι → σ), g p x ∈ S := fun p x =>
    Finset.mem_image_of_mem _ (Finset.mem_univ (p, x))
  set g₀ : Pi → (ι → σ) → {a // a ∈ S} := fun p x => ⟨g p x, hmem p x⟩ with hg₀def
  have hstrict : StrictMono (fun a : {a // a ∈ S} => (a : A)) := fun _ _ hab => hab
  have hcoe : ∀ x : ι → σ,
      ((maxFun fun p => g₀ p x : {a // a ∈ S}) : A) = maxFun fun p => g p x := by
    intro x
    exact (maxFun_strictMono hstrict fun p => g₀ p x).symm
  have hbase : HasDual (fun x => maxFun fun p => g₀ p x)
      (c₀ * (24 * Real.sqrt (Fintype.card Pi))) :=
    HasDual.max hc₀ fun p => (hg p).ofKer fun x y => by
      simp [hg₀def, Subtype.ext_iff]
  refine hbase.ofKer fun x y => ⟨fun hxy => ?_, fun hxy => Subtype.ext ?_⟩
  · rw [← hcoe x, ← hcoe y, hxy]
  · rw [hcoe x, hcoe y, hxy]

omit [DecidableEq ι] [Fintype σ] in
/-- **An arbitrary outer function of finitely many subproblems, over any value
and output types.** -/
theorem HasDual.combine' {Pi V O' : Type} [Fintype Pi]
    [DecidableEq V] [DecidableEq O'] (h : (Pi → V) → O') {g : Pi → (ι → σ) → V}
    {c : Pi → ℝ} (hg : ∀ p, HasDual (g p) (c p)) [Finite σ] :
    HasDual (fun x => h fun p => g p x) (2 * ∑ p, c p) := by
  classical
  let := Fintype.ofFinite σ
  set SV : Finset V :=
    Finset.image (fun q : Pi × (ι → σ) => g q.1 q.2) Finset.univ with hSVdef
  have hmemV : ∀ (p : Pi) (x : ι → σ), g p x ∈ SV := fun p x =>
    Finset.mem_image_of_mem _ (Finset.mem_univ (p, x))
  set g₀ : Pi → (ι → σ) → {v // v ∈ SV} := fun p x => ⟨g p x, hmemV p x⟩ with hg₀def
  set SO : Finset O' :=
    Finset.image (fun z : Pi → {v // v ∈ SV} => h fun p => (z p : V))
      Finset.univ with hSOdef
  have hmemO : ∀ z : Pi → {v // v ∈ SV}, (h fun p => (z p : V)) ∈ SO := fun z =>
    Finset.mem_image_of_mem _ (Finset.mem_univ z)
  set h₀ : (Pi → {v // v ∈ SV}) → {o // o ∈ SO} := fun z =>
    ⟨h fun p => (z p : V), hmemO z⟩ with hh₀def
  have hbase : HasDual (fun x => h₀ fun p => g₀ p x) (2 * ∑ p, c p) :=
    HasDual.combine h₀ fun p => (hg p).ofKer fun x y => by
      simp [Subtype.ext_iff]
  exact hbase.ofKer fun x y =>
    ⟨fun hxy => congrArg Subtype.val hxy, fun hxy => Subtype.ext hxy⟩

omit [DecidableEq ι] [Fintype σ] in
/-- **Postcomposition is available within a factor two.**  `combine'` with a
one-element index set: its outer function is arbitrary, so *any* recoding of
the output — a coarsening included — costs at most twice the original.  It is
not free in general: a dual for `f` satisfies an equality constraint keyed to
`f`'s level sets, and merging two of them turns a required `1` into a
required `0`.  Two is an upper bound obtained this way, not a lower bound on
what a coarsening must cost — a particular recoding may well be cheaper, and
an injective one is free (`HasDual.ofKer`).  This is the priced form of the
joint-output discipline. -/
theorem HasDual.postcomp {V O' : Type} [DecidableEq V] [DecidableEq O']
    {f : (ι → σ) → V} {c : ℝ} (h : HasDual f c) (H : V → O') [Finite σ] :
    HasDual (fun x => H (f x)) (2 * c) := by
  classical
  let := Fintype.ofFinite σ
  have hcomb := HasDual.combine' (ι := ι) (σ := σ) (Pi := Unit) (V := V)
    (O' := O') (fun z : Unit → V => H (z ())) (g := fun _ => f)
    (c := fun _ => c) fun _ => h
  simpa using hcomb

omit [DecidableEq ι] [Fintype σ] in
/-- **A joint may be collapsed onto anything it determines**, within the same
factor two — with the collapsing map obtained from the determination rather
than supplied.  This is the form a transcript compiler needs: it builds a
joint and reads off the answer that the joint determines. -/
theorem HasDual.postcomp_of_determined {V O' : Type} [DecidableEq V] [DecidableEq O']
    [Nonempty O'] {f : (ι → σ) → V} {g : (ι → σ) → O'} {c : ℝ}
    (h : HasDual f c) (hdet : ∀ x y, f x = f y → g x = g y) [Finite σ] :
    HasDual g (2 * c) := by
  classical
  let := Fintype.ofFinite σ
  refine (h.postcomp (fun v => if hv : ∃ x, f x = v then g hv.choose
    else Classical.arbitrary O')).ofEq fun x => ?_
  have hv : ∃ z, f z = f x := ⟨x, rfl⟩
  rw [dite_eq_left hv]
  exact hdet _ _ hv.choose_spec

omit [DecidableEq ι] [Fintype σ] in
/-- **Every function of `n` letters costs `2n`**, whatever its output type.  The
first-difference dual with the output recoded into its finite range. -/
theorem hasDual_two_mul_card (f : (ι → σ) → O) [Finite σ] :
    HasDual f (2 * (Fintype.card ι : ℝ)) := by
  classical
  let := Fintype.ofFinite σ
  set S : Finset O := Finset.image f Finset.univ with hSdef
  have hmem : ∀ x, f x ∈ S := fun x =>
    Finset.mem_image_of_mem _ (Finset.mem_univ x)
  set f₀ : (ι → σ) → {o // o ∈ S} := fun x => ⟨f x, hmem x⟩ with hf₀def
  have hw := firstDiffDual_isWeightedCostLe f₀ (fun _ => 1)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hw
  refine (hasDual_of_dualPair (firstDiffDual f₀)
    (DualPair.isCostLe_of_isWeightedCostLe_one hw)).ofKer fun x y => ?_
  exact ⟨fun hxy => congrArg Subtype.val hxy, fun hxy => Subtype.ext hxy⟩

omit [DecidableEq ι] [Fintype σ] in
/-- **A function of a single letter costs `2`.**  Both the letter alphabet and
the output type are arbitrary. -/
theorem hasDual_ofCoord (i₀ : ι) (m : σ → O) [Finite σ] :
    HasDual (fun x : ι → σ => m (x i₀)) 2 := by
  classical
  let := Fintype.ofFinite σ
  have he : Function.Injective (fun _ : Unit => i₀) := fun a b _ =>
    Subsingleton.elim a b
  have h := (hasDual_two_mul_card (ι := Unit) (σ := σ)
    (fun z : Unit → σ => m (z ()))).pullback he
  have h2 : HasDual (fun x : ι → σ => m (x i₀)) (2 * (Fintype.card Unit : ℝ)) :=
    h.ofEq fun _ => rfl
  simpa using h2

/-- **A finite supremum, as a maximum over a nonempty index.**  Padding the index
set with a `none` carrying `⊥` makes an empty supremum legal, so no nonemptiness
hypothesis has to be threaded through a recursion. -/
lemma finsetSup_eq_maxFun {α : Type} {A : Type} [LinearOrder A]
    [OrderBot A] (S : Finset α) (F : α → A) :
    S.sup F = maxFun fun c : Option {i // i ∈ S} => c.elim ⊥ fun i => F i := by
  classical
  refine le_antisymm (Finset.sup_le fun i hi => ?_) (maxFun_le fun c => ?_)
  · exact le_maxFun (fun c : Option {i // i ∈ S} => c.elim ⊥ fun i => F i)
      (some ⟨i, hi⟩)
  · cases c with
    | none => exact bot_le
    | some i => exact Finset.le_sup i.2

omit [DecidableEq ι] [Fintype σ] in
/-- **The supremum of a finite family of equally expensive subproblems.**

The workhorse of the divide-and-conquer: `q` candidates each solved at cost `c₀`
give their maximum at cost `24 √(q+1) · c₀`.  Stated for `Finset.sup` rather than
`maxFun`, so that an empty candidate set — the maximum of nothing is `⊥` — is
allowed and costs nothing extra. -/
theorem HasDual.finsetSup {α A : Type} [DecidableEq A]
    [LinearOrder A] [OrderBot A] (S : Finset α) {g : α → (ι → σ) → A} {c₀ : ℝ}
    (hc₀ : 0 ≤ c₀) (hg : ∀ i ∈ S, HasDual (g i) c₀) [Finite σ] :
    HasDual (fun x => S.sup fun i => g i x)
      (c₀ * (24 * Real.sqrt ((S.card : ℝ) + 1))) := by
  classical
  let := Fintype.ofFinite σ
  have hcard : (Fintype.card (Option {i // i ∈ S}) : ℝ) = (S.card : ℝ) + 1 := by
    rw [Fintype.card_option, Fintype.card_coe]
    push_cast
    ring
  have hmax : HasDual (fun x => maxFun fun c : Option {i // i ∈ S} =>
      c.elim ⊥ fun i => g (i : α) x)
      (c₀ * (24 * Real.sqrt (Fintype.card (Option {i // i ∈ S})))) := by
    refine HasDual.max' hc₀ fun c => ?_
    cases c with
    | none => exact (hasDual_const (f := fun _ : ι → σ => (⊥ : A))
        fun _ _ => rfl).mono hc₀
    | some i => exact hg (i : α) i.2
  rw [hcard] at hmax
  exact hmax.ofEq fun x => (finsetSup_eq_maxFun S fun i => g i x).symm

omit [DecidableEq ι] [Fintype σ] in
/-- **Two subproblems fed to an arbitrary binary outer function.**  This is how
two tropical path weights are multiplied — `h` is `(+)` on `ℝ ∪ {-∞}` — and
nothing about `h` is used. -/
theorem HasDual.combine₂ {V O' : Type} [DecidableEq V] [DecidableEq O']
    (h : V → V → O') {g₀ g₁ : (ι → σ) → V} {c₀ c₁ : ℝ}
    (hg₀ : HasDual g₀ c₀) (hg₁ : HasDual g₁ c₁) [Finite σ] :
    HasDual (fun x => h (g₀ x) (g₁ x)) (2 * (c₀ + c₁)) := by
  classical
  let := Fintype.ofFinite σ
  have hsum : (∑ b : Bool, bif b then c₁ else c₀) = c₀ + c₁ := by
    rw [Fintype.sum_bool]
    exact add_comm _ _
  have hgb : ∀ b : Bool,
      HasDual (bif b then g₁ else g₀) (bif b then c₁ else c₀) := by
    intro b; cases b
    · exact hg₀
    · exact hg₁
  have := HasDual.combine' (Pi := Bool) (fun z : Bool → V => h (z false) (z true))
    (g := fun b => bif b then g₁ else g₀) (c := fun b => bif b then c₁ else c₀)
    hgb
  rwa [hsum] at this

omit [DecidableEq ι] [Fintype σ] in
/-- **The maximum of a value map over a block of letters, over any linear order
of values.**  This is the base case of the tropical recursion: the largest
`(s,t)` entry among the letters read in a block. -/
theorem hasDual_maxMap_block' {κ A : Type} [Fintype κ]
    [Nonempty κ] [DecidableEq A] [LinearOrder A] {e : κ → ι}
    (he : Function.Injective e) (m : σ → A) [Finite σ] :
    HasDual (fun x : ι → σ => maxFun fun j : κ => m (x (e j)))
      (24 * Real.sqrt (Fintype.card κ)) := by
  classical
  let := Fintype.ofFinite σ
  set S : Finset A := Finset.image m Finset.univ with hSdef
  have hmem : ∀ s : σ, m s ∈ S := fun s =>
    Finset.mem_image_of_mem _ (Finset.mem_univ s)
  set m₀ : σ → {a // a ∈ S} := fun s => ⟨m s, hmem s⟩ with hm₀def
  have hstrict : StrictMono (fun a : {a // a ∈ S} => (a : A)) := fun _ _ hab => hab
  have hcoe : ∀ x : ι → σ,
      ((maxFun fun j : κ => m₀ (x (e j)) : {a // a ∈ S}) : A)
        = maxFun fun j : κ => m (x (e j)) := fun x =>
    (maxFun_strictMono hstrict fun j : κ => m₀ (x (e j))).symm
  exact (hasDual_maxMap_block (ι := ι) (σ := σ) he m₀).ofKer fun x y =>
    ⟨fun hxy => by rw [← hcoe x, ← hcoe y, hxy],
     fun hxy => Subtype.ext (by rw [hcoe x, hcoe y, hxy])⟩

end FiniteRange

end QuantumQueryComplexity

end SourceHasDual

section SourcePromiseHasDual

/-!
# Bundled dual solutions on a promise domain

`SourceHasDual` hides the dimension type of a dual solution for a
*total* function; a divide-and-conquer recursion whose subproblems live on
input-dependent promises needs the same service on `DualPairOn`.  This section
is that layer, plus the two structural moves every promise construction
needs:

* `DualPairOn.ofKer` — the constraint sees the output only through the
  equality pattern `f x = f y`, so a solution for `f` is a solution for any
  `f'` with the same kernel, *at the same vectors*.  This is what lets a
  descriptor chain be repackaged as a transcript without paying anything.
* `HasDual.restrictToOn` — a total solution restricts to a promise for free
  (`DualPair.restrictTo`), which is how the windowed element-distinctness
  duals of `ED/*` become the leaves of the LDS recursion.

Cost-`0` solutions exist exactly for functions that are constant on the
promise (`hasDualOn_of_const`): on such a promise the constraint's right-hand
side is identically `0`, so the zero vectors are feasible.  That is the
"value determined by the transcript" case of descriptor composition.
-/


namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {O O' : Type} [DecidableEq O] [DecidableEq O']

/-! ## Recoding the output -/

namespace DualPairOn

variable {K : Type} [Fintype K] {read : X → ι → σ} {f : X → O} {f' : X → O'}

/-- **Output recoding.**  A dual solution for `f` is a dual solution for any
`f'` with the same kernel on the promise — same vectors, same cost. -/
@[expose]
def ofKer (P : DualPairOn read K f) (h : ∀ x y, f x = f y ↔ f' x = f' y) :
    DualPairOn read K f' where
  u := P.u
  v := P.v
  constraint x y := by
    rw [P.constraint x y]
    by_cases hxy : f x = f y
    · rw [ite_eq_left hxy, ite_eq_left ((h x y).mp hxy)]
    · rw [ite_eq_right hxy, ite_eq_right fun hc => hxy ((h x y).mpr hc)]

omit [DecidableEq X] [DecidableEq ι] in
@[simp] lemma ofKer_u (P : DualPairOn read K f)
    (h : ∀ x y, f x = f y ↔ f' x = f' y) : (P.ofKer h).u = P.u := rfl

omit [DecidableEq X] [DecidableEq ι] in
@[simp] lemma ofKer_v (P : DualPairOn read K f)
    (h : ∀ x y, f x = f y ↔ f' x = f' y) : (P.ofKer h).v = P.v := rfl

omit [DecidableEq X] [DecidableEq ι] in
lemma ofKer_isCostLe {c : ℝ} {P : DualPairOn read K f}
    {h : ∀ x y, f x = f y ↔ f' x = f' y} (hP : P.IsCostLe c) :
    (P.ofKer h).IsCostLe c := hP

/-- **Pulling a promise solution back along a map of promises.**  Every
sub-promise — in particular every fiber of a descriptor — inherits the
ambient solution at the same cost, since the constraint at `(y, y')` *is* the
constraint at `(e y, e y')`. -/
def comap {Y : Type} [Fintype Y] (P : DualPairOn read K f) (e : Y → X) :
    DualPairOn (fun y => read (e y)) K (fun y => f (e y)) where
  u y := P.u (e y)
  v y := P.v (e y)
  constraint y y' := P.constraint (e y) (e y')

/-- The zero solution is feasible for a function that is constant on the
promise. -/
def const (read : X → ι → σ) (f : X → O) (hf : ∀ x y, f x = f y) :
    DualPairOn read Empty f where
  u _ _ _ := 0
  v _ _ _ := 0
  constraint x y := by simp [hf x y]

omit [DecidableEq X] [DecidableEq ι] in
lemma const_isCostLe {read : X → ι → σ} {f : X → O} (hf : ∀ x y, f x = f y) :
    (const read f hf).IsCostLe 0 := by
  constructor <;> intro x <;> simp [const]

end DualPairOn

/-! ## The bundled predicate -/

/-- `f` has a feasible dual solution of cost at most `c` on the promise
domain `read`. -/
@[expose]
def HasDualOn {ι : Type} [Fintype ι] {σ : Type} [DecidableEq σ] {X : Type}
    [Fintype X] {O : Type} [DecidableEq O] (read : X → ι → σ) (f : X → O)
    (c : ℝ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (P : DualPairOn read K f), P.IsCostLe c

variable {read : X → ι → σ} {f : X → O} {f' : X → O'} {c d : ℝ}

omit [DecidableEq X] [DecidableEq ι] in
lemma hasDualOn_of_dualPairOn {K : Type} [Fintype K] (P : DualPairOn read K f)
    (h : P.IsCostLe c) : HasDualOn read f c := ⟨K, inferInstance, P, h⟩

omit [DecidableEq X] [DecidableEq ι] in
lemma HasDualOn.mono (h : HasDualOn read f c) (hcd : c ≤ d) :
    HasDualOn read f d := by
  classical
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P, hP.mono hcd⟩

omit [DecidableEq ι] in
/-- **Weak duality on a promise, bundled.** -/
theorem advPMOn_le_of_hasDualOn (hc : 0 ≤ c) (h : HasDualOn read f c) :
    advPMOn read f ≤ c := by
  classical
  obtain ⟨K, hK, P, hP⟩ := h
  exact advPMOn_le_of_dualPairOn P hc hP

/-! ## Total solutions as promise solutions

A total function is the promise problem over `read = id`, and a `DualPair`
is literally a `DualPairOn` there — the constraint's mask `id x i = id y i`
is definitionally `x i = y i`. -/

section Total

variable [Fintype σ] {g : (ι → σ) → O}

/-- A total dual solution, read as a promise solution over `read = id`. -/
def DualPair.toOn {K : Type} [Fintype K] (P : DualPair K g) :
    DualPairOn (id : (ι → σ) → ι → σ) K g where
  u := P.u
  v := P.v
  constraint := P.constraint

lemma DualPair.toOn_isCostLe {K : Type} [Fintype K] (P : DualPair K g)
    (h : P.IsCostLe c) : P.toOn.IsCostLe c := h

/-- **A total bundled dual is a bundled promise dual over `read = id`.** -/
lemma HasDual.hasDualOn (h : HasDual g c) :
    HasDualOn (id : (ι → σ) → ι → σ) g c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.toOn, hP⟩

/-- **The converse of `HasDual.hasDualOn`.**  With both directions available
the promise-side calculus — descriptor composition in particular — can be run
inside a total development and handed back as a `HasDual`. -/
theorem HasDual.of_hasDualOn_id (h : HasDualOn (id : (ι → σ) → ι → σ) g c) :
    HasDual g c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.toTotal, DualPairOn.toTotal_isCostLe hP⟩

end Total

omit [DecidableEq X] [DecidableEq ι] in
/-- Recoding the output of a bundled solution. -/
lemma HasDualOn.ofKer (h : HasDualOn read f c)
    (hker : ∀ x y, f x = f y ↔ f' x = f' y) : HasDualOn read f' c := by
  classical
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.ofKer hker, DualPairOn.ofKer_isCostLe hP⟩

omit [DecidableEq X] [DecidableEq ι] in
/-- Replacing the function by a pointwise equal one. -/
lemma HasDualOn.ofEq (h : HasDualOn read f c) {g : X → O}
    (hg : ∀ x, f x = g x) : HasDualOn read g c := by
  classical
  exact h.ofKer fun x y => by rw [hg x, hg y]

omit [DecidableEq X] [DecidableEq ι] in
/-- Restricting a bundled promise solution to a sub-promise, at the same
cost. -/
theorem HasDualOn.comap {Y : Type} [Fintype Y] (h : HasDualOn read f c)
    (e : Y → X) : HasDualOn (fun y => read (e y)) (fun y => f (e y)) c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.comap e, fun y => hP.1 (e y), fun y => hP.2 (e y)⟩

omit [DecidableEq X] [DecidableEq ι] in
/-- A function constant on the promise costs nothing. -/
lemma hasDualOn_of_const (read : X → ι → σ) {f : X → O} (hf : ∀ x y, f x = f y) :
    HasDualOn read f 0 := by
  classical
  exact hasDualOn_of_dualPairOn (DualPairOn.const read f hf)
      (DualPairOn.const_isCostLe hf)

/-! ## Moving between query index types -/

namespace DualPairOn

variable {K : Type} [Fintype K] {read : X → ι → σ} {f : X → O}

/-- **A solution that only queries a sub-family of coordinates.**  If the
promise is observed through `ι' ↪ ι` — the arena of a divide-and-conquer node
is such a sub-family of the word's positions — a solution written in arena
coordinates becomes one in the ambient coordinates, at the same cost: the
`ℓ²` mass moves to the image of the injection without accumulating
(`spread`). -/
noncomputable def pullbackCoord {ι' : Type} [Fintype ι']
    {e : ι' → ι} (he : Function.Injective e)
    (P : DualPairOn (fun x k => read x (e k)) K f) : DualPairOn read K f where
  u x i := fun k => spread e (fun j => P.u x j k) i
  v y i := fun k => spread e (fun j => P.v y j k) i
  constraint x y := by
    set T : ι' → ℝ := fun j => ∑ k : K, P.u x j k * P.v y j k with hT
    have hpt : ∀ i : ι,
        (∑ k : K, spread e (fun j => P.u x j k) i
            * spread e (fun j => P.v y j k) i) = spread e T i := by
      intro i
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        spread_mul_spread he i (fun j => P.u x j k) (fun j => P.v y j k)]
      simp only [spread, hT]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    simp only [hpt]
    have hmask : ∀ i : ι,
        (if read x i = read y i then (0 : ℝ) else spread e T i)
        = spread e (fun j => if read x (e j) = read y (e j) then (0 : ℝ)
            else T j) i := by
      intro i
      by_cases h : ∃ j, e j = i
      · obtain ⟨j₀, hj⟩ := h
        rw [spread_eq_of_mem he hj, spread_eq_of_mem he hj, hj]
      · push Not at h
        rw [spread_eq_zero h, spread_eq_zero h, ite_self]
    simp only [hmask]
    rw [sum_spread]
    exact P.constraint x y

omit [DecidableEq X] in
theorem pullbackCoord_isCostLe {ι' : Type} [Fintype ι']
    {e : ι' → ι} (he : Function.Injective e)
    (P : DualPairOn (fun x k => read x (e k)) K f) {c : ℝ} (hP : P.IsCostLe c) :
    (P.pullbackCoord he).IsCostLe c := by
  classical
  constructor
  · intro x
    have h : ∀ i : ι,
        (∑ k : K, (P.pullbackCoord he).u x i k * (P.pullbackCoord he).u x i k)
          = spread e (fun j => ∑ k : K, P.u x j k * P.u x j k) i := by
      intro i
      change (∑ k : K, spread e (fun j => P.u x j k) i
          * spread e (fun j => P.u x j k) i) = _
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        spread_mul_spread he i (fun j => P.u x j k) (fun j => P.u x j k)]
      simp only [spread]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    simp only [h]
    rw [sum_spread]
    exact hP.1 x
  · intro y
    have h : ∀ i : ι,
        (∑ k : K, (P.pullbackCoord he).v y i k * (P.pullbackCoord he).v y i k)
          = spread e (fun j => ∑ k : K, P.v y j k * P.v y j k) i := by
      intro i
      change (∑ k : K, spread e (fun j => P.v y j k) i
          * spread e (fun j => P.v y j k) i) = _
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        spread_mul_spread he i (fun j => P.v y j k) (fun j => P.v y j k)]
      simp only [spread]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    simp only [h]
    rw [sum_spread]
    exact hP.2 y

end DualPairOn

omit [DecidableEq X] [DecidableEq ι] in
/-- **Arena coordinates, bundled**: a promise solution written in the
coordinates of a sub-family costs the same in the ambient coordinates. -/
theorem HasDualOn.pullbackCoord {ι' : Type} [Fintype ι']
    {e : ι' → ι} (he : Function.Injective e)
    (h : HasDualOn (fun x k => read x (e k)) f c) : HasDualOn read f c := by
  classical
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.pullbackCoord he, DualPairOn.pullbackCoord_isCostLe he P hP⟩

/-! ## Restricting a total solution -/

omit [DecidableEq X] [DecidableEq ι] in
/-- **A total dual solution restricted to a promise domain**, bundled: the
vectors are unchanged, so the cost is inherited.  This is how the windowed
`ED` duals enter a promise-relativized recursion. -/
theorem HasDual.restrictToOn {g : (ι → σ) → O} (h : HasDual g c)
    (read : X → ι → σ) : HasDualOn read (fun x => g (read x)) c := by
  classical
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.restrictTo read, fun x => hP.1 (read x), fun x => hP.2 (read x)⟩

end QuantumQueryComplexity

end SourcePromiseHasDual
