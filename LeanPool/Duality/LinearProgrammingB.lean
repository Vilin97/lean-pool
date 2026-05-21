/-
Copyright (c) 2026 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Tactic.Peel
import LeanPool.Duality.LinearProgramming

/-!
We prove properties of "normal" linear programs as a corollary of properties of extended
linear programs. The only exception is the weak duality theorem, which is proved separately,
to allow weaker assumptions.
-/


/-- Linear program in the standard form. Variables are of type `J`. Conditions are indexed by
    type `I`. The objective function is intended to be minimized. -/
structure StandardLP (I J R : Type*) where
  /-- The left-hand-side matrix -/
  A : Matrix I J R
  /-- The right-hand-side vector -/
  b : I → R
  /-- The objective function coefficients -/
  c : J → R


variable {I R : Type*}

/-- Coerce a vector of nonnegative values into a vector of the underlying ring. -/
@[coe] def coeNN [Zero R] [LE R] : (I → R≥0) → (I → R) := (Subtype.val ∘ ·)

instance [Zero R] [LE R] : Coe (I → R≥0) (I → R) :=
  ⟨coeNN⟩

open scoped Matrix

variable {J : Type*} [Fintype J]

/-- A nonnegative vector `x` is a solution to a linear program `P` iff
    its multiplication by matrix `A` from the left yields a vector whose
    all entries are less or equal to corresponding entries of the vector `b`. -/
def StandardLP.IsSolution [Semiring R] [PartialOrder R]
    (P : StandardLP I J R) (x : J → R≥0) : Prop :=
  P.A *ᵥ x ≤ P.b

/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `r`. -/
def StandardLP.Reaches [Semiring R] [PartialOrder R]
    (P : StandardLP I J R) (r : R) : Prop :=
  ∃ x : J → R≥0, P.IsSolution x ∧ P.c ⬝ᵥ x = r

/-- Linear program `P` is feasible iff there exists a solution to `P`. -/
def StandardLP.IsFeasible [Semiring R] [PartialOrder R]
    (P : StandardLP I J R) : Prop :=
  ∃ r : R, P.Reaches r

/-- Linear program `P` is bounded by `r` iff every value reached by `P` is
    greater or equal to `r` (i.e., `P` is bounded by `r` from below). -/
def StandardLP.IsBoundedBy [Semiring R] [PartialOrder R]
    (P : StandardLP I J R) (r : R) : Prop :=
  ∀ p : R, P.Reaches p → r ≤ p

/-- Linear program `P` is unbounded iff values reached by `P` have no lower bound. -/
def StandardLP.IsUnbounded [Semiring R] [PartialOrder R]
    (P : StandardLP I J R) : Prop :=
  ¬∃ r : R, P.IsBoundedBy r

/-- Dualize a linear program in the standard form.
    The matrix gets transposed and its values flip signs.
    The original objective function becomes the new right-hand-side vector.
    The original right-hand-side vector becomes the new objective function.
    Both linear programs are intended to be minimized. -/
def StandardLP.dualize [Ring R] (P : StandardLP I J R) : StandardLP J I R :=
  ⟨-P.Aᵀ, P.c, P.b⟩


lemma Matrix.transpose_mulVec_dotProduct [Fintype I] [CommSemiring R] (M : Matrix I J R)
    (v : I → R) (w : J → R) :
    Mᵀ *ᵥ v ⬝ᵥ w = M *ᵥ w ⬝ᵥ v := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem StandardLP.weakDuality [Fintype I] [CommRing R] [PartialOrder R] [IsOrderedRing R]
    {P : StandardLP I J R}
    {p : R} (hP : P.Reaches p) {q : R} (hQ : P.dualize.Reaches q) :
    0 ≤ p + q := by
  obtain ⟨x, hxb, rfl⟩ := hP
  obtain ⟨y, hyc, rfl⟩ := hQ
  have hyxx : (-P.Aᵀ) *ᵥ ↑y ⬝ᵥ ↑x ≤ P.c ⬝ᵥ ↑x :=
    dotProduct_le_dotProduct_of_nonneg_right hyc (x ·|>.property)
  have hxyy : P.A *ᵥ ↑x ⬝ᵥ ↑y ≤ P.b ⬝ᵥ ↑y :=
    dotProduct_le_dotProduct_of_nonneg_right hxb (y ·|>.property)
  rw [←neg_le_iff_add_nonneg']
  rw [Matrix.neg_mulVec, neg_dotProduct, neg_le, Matrix.transpose_mulVec_dotProduct] at hyxx
  exact (hyxx.trans hxyy)


variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]

open scoped Classical in
/-- The "optimum" of "minimization LP" (the less the better). -/
noncomputable def StandardLP.optimum (P : StandardLP I J R) : Option R∞ :=
  if ¬P.IsFeasible then
    some ⊤ -- infeasible means that the minimum is `⊤`
  else
    if P.IsUnbounded then
      some ⊥ -- unbounded means that the minimum is `⊥`
    else
      if hr : ∃ r : R, P.Reaches r ∧ P.IsBoundedBy r then
        some (toE hr.choose) -- the minimum exists
      else
        none -- invalid finite value (infimum is not attained)


private def StandardLP.toValidELP (P : StandardLP I J R) : ValidELP I J R :=
  ⟨⟨P.A.map toE, toE ∘ P.b, toE ∘ P.c⟩, by aesop, by aesop, by aesop, by aesop, by aesop, by aesop⟩

omit [IsStrictOrderedRing R] in
private lemma StandardLP.toE_dotProduct_apply (P : StandardLP I J R) (x : J → R≥0) :
    toE (P.c ⬝ᵥ x) = (toE ∘ P.c ᵥ⬝ x) := by
  simp_rw [dotProduct, dotWeig, mul_comm]
  apply Finset.sum_toE

omit [IsStrictOrderedRing R] in
private lemma StandardLP.toE_mulVec_apply (P : StandardLP I J R) (x : J → R≥0) (i : I) :
    toE ((P.A *ᵥ x) i) = (P.A.map toE ₘ* x) i := by
  simp_rw [Matrix.mulVec, Matrix.mulWeig, Matrix.map, dotProduct, dotWeig, Matrix.of_apply,
    mul_comm]
  apply Finset.sum_toE

private lemma StandardLP.toValidELP.isSolution_iff (P : StandardLP I J R) (x : J → R≥0) :
    P.toValidELP.IsSolution x ↔ P.IsSolution x := by
  change P.A.map toE ₘ* x ≤ toE ∘ P.b ↔ P.A *ᵥ x ≤ P.b
  constructor
  · intro h i
    have := h i
    rw [Function.comp_apply, ←StandardLP.toE_mulVec_apply, EF.coe_le_coe_iff] at this
    exact this
  · intro h i
    rw [Function.comp_apply, ←StandardLP.toE_mulVec_apply, EF.coe_le_coe_iff]
    exact h i

private lemma StandardLP.toValidELP_reaches_iff (P : StandardLP I J R) (r : R) :
    P.toValidELP.Reaches r ↔ P.Reaches r := by
  peel with x
  apply and_congr
  · apply StandardLP.toValidELP.isSolution_iff
  · exact P.toE_dotProduct_apply x ▸ EF.coe_eq_coe_iff

private lemma StandardLP.toValidELP_isFeasible_iff (P : StandardLP I J R) :
    P.toValidELP.IsFeasible ↔ P.IsFeasible := by
  constructor
  · intro ⟨r, ⟨x, hx, hxr⟩, hr⟩
    match r with
    | ⊥ =>
      exfalso
      rw [←dotWeig_eq_bot] at hxr
      simp [StandardLP.toValidELP] at hxr
    | ⊤ =>
      exfalso
      exact hr rfl
    | (p : R) =>
      refine ⟨p, x, ?_, ?_⟩
      · rwa [StandardLP.toValidELP.isSolution_iff] at hx
      · rwa [←EF.coe_eq_coe_iff, P.toE_dotProduct_apply]
  · intro ⟨r, x, hx, hxr⟩
    refine ⟨toE r, ⟨x, ?_, ?_⟩, EF.coe_neq_top r⟩
    · rwa [StandardLP.toValidELP.isSolution_iff]
    · rwa [←EF.coe_eq_coe_iff, P.toE_dotProduct_apply] at hxr

private lemma StandardLP.toValidELP_isBoundedBy_iff (P : StandardLP I J R) (r : R) :
    P.toValidELP.IsBoundedBy r ↔ P.IsBoundedBy r := by
  unfold StandardLP.IsBoundedBy ExtendedLP.IsBoundedBy
  constructor <;> intro hP p hPp
  · simpa [EF.coe_le_coe_iff] using
      hP (toE p) (by simpa [StandardLP.toValidELP_reaches_iff] using hPp)
  · match p with
    | ⊥ =>
      exfalso
      obtain ⟨_, -, impos⟩ := hPp
      rw [←dotWeig_eq_bot] at impos
      simp [StandardLP.toValidELP] at impos
    | ⊤ =>
      apply le_top
    | (_ : R) =>
      rw [EF.coe_le_coe_iff]
      apply hP
      simpa [StandardLP.toValidELP_reaches_iff] using hPp

private lemma StandardLP.toValidELP_isUnbounded_iff (P : StandardLP I J R) :
    P.toValidELP.IsUnbounded ↔ P.IsUnbounded := by
  constructor <;> intro hP hr <;> apply hP <;>
    simpa only [P.toValidELP_isBoundedBy_iff] using hr

private theorem StandardLP.toValidELP_optimum_eq (P : StandardLP I J R) :
    P.toValidELP.optimum = P.optimum := by
  if feas : P.IsFeasible then
    if unbo : P.IsUnbounded then
      convert Eq.refl (some (⊥ : R∞))
      · simp [ExtendedLP.optimum, feas, unbo, P.toValidELP_isFeasible_iff,
          P.toValidELP_isUnbounded_iff]
      · simp [StandardLP.optimum, feas, unbo]
    else
      simp only [StandardLP.optimum, ExtendedLP.optimum, feas, unbo,
        P.toValidELP_isFeasible_iff, P.toValidELP_isUnbounded_iff]
      if hr : ∃ r : R, P.Reaches r ∧ P.IsBoundedBy r then
        convert Eq.refl (some (toE hr.choose))
        · simp [hr, P.toValidELP_reaches_iff, P.toValidELP_isBoundedBy_iff]
        · simp [hr]
      else
        convert Eq.refl none
        · simp [hr, P.toValidELP_reaches_iff, P.toValidELP_isBoundedBy_iff]
        · simp [hr]
  else
    convert Eq.refl (some (⊤ : R∞))
    · simp [ExtendedLP.optimum, feas, P.toValidELP_isFeasible_iff]
    · simp [StandardLP.optimum, feas]

omit [Fintype J] in
private lemma StandardLP.toValidELP_dualize_eq (P : StandardLP I J R) :
    P.toValidELP.dualize = P.dualize.toValidELP :=
  rfl


variable [Fintype I]

omit [Fintype I] in
theorem StandardLP.optimum_neq_none [Finite I] (P : StandardLP I J R) :
    P.optimum ≠ none := by
  letI : Fintype I := Fintype.ofFinite I
  exact P.toValidELP_optimum_eq ▸ P.toValidELP.optimum_neq_none

theorem StandardLP.strongDuality (P : StandardLP I J R)
    (hP : P.IsFeasible ∨ P.dualize.IsFeasible) :
    OppositesOpt P.optimum P.dualize.optimum := by
  simpa [StandardLP.toValidELP_optimum_eq, P.toValidELP_dualize_eq] using
    P.toValidELP.strongDuality (by
      simpa [StandardLP.toValidELP_isFeasible_iff, P.toValidELP_dualize_eq] using
        hP)
