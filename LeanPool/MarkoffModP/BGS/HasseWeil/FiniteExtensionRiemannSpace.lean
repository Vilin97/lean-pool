/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionOneSubGcdHeight
import Mathlib.FieldTheory.Finite.Basic

/-!
# Riemann spaces for finite extensions of a rational function field

This file supplies the elementary divisor-linear-algebra layer needed by a
Bombieri--Stepanov proof of Hasse--Weil.  For a divisor `D` on the exhaustive
finite and infinite places of a finite separable extension `L / K(X)`, it
defines the Riemann space

`L(D) = {x : L | x = 0 or div(x) + D is effective}`

as a `K`-submodule of `L`.  It also proves the order-theoretic and
multiplicative properties of these spaces, together with their specialization
to the one-point filtration `L(nP)`.

The integer-valued principal-divisor API is defined only for nonzero elements,
so zero is an explicit branch of the carrier predicate.  Scalar closure uses
that a nonzero constant over the finite constant field has trivial principal
divisor.

Two substantive stages are deliberately *not* postulated here:

* finite-dimensionality of every `L(D)` over `K`;
* the Riemann--Roch lower bound, which can be stated without introducing genus
  as `2 * deg D - deg K_can <= 2 * finrank_K L(D)`.

The ambient function field `L` is not finite-dimensional over `K`, so the first
item is a genuine theorem and cannot be obtained by typeclass inference from
the ambient space.  Both stages must be proved before `finrank` is used in the
Hasse--Weil argument.
-/

namespace BGS.CorvajaZannier

noncomputable section

open scoped nonZeroDivisors Polynomial

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance finiteExtensionRiemannSpaceConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance finiteExtensionRiemannSpaceConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- A finitely supported divisor on all finite and infinite places of
`L / K(X)`. -/
abbrev FiniteExtensionDivisor := FiniteExtensionPlace K L →₀ ℤ

/-- Divisor degree is additive. -/
theorem finiteExtensionDivisorDegree_add
    (D E : FiniteExtensionDivisor K L) :
    finiteExtensionDivisorDegree K L (D + E) =
      finiteExtensionDivisorDegree K L D +
        finiteExtensionDivisorDegree K L E := by
  classical
  simpa only [finiteExtensionDivisorDegree] using
    (Finsupp.sum_add_index (f := D) (g := E)
      (h := fun v e ↦ e * (finiteExtensionPlaceDegree K L v : ℤ))
      (by simp) (by intros; ring))

/-- The product formula says that every nonzero principal divisor has degree
zero. -/
theorem finiteExtensionDivisorDegree_principal
    (x : L) (hx : x ≠ 0) :
    finiteExtensionDivisorDegree K L
      (finiteExtensionPrincipalDivisor K L x) = 0 := by
  exact finiteExtensionPrincipalDivisorDegreeSum_eq_zero K L x hx

/-- An effective divisor has nonnegative degree. -/
theorem finiteExtensionDivisorDegree_nonnegative_of_effective
    (D : FiniteExtensionDivisor K L) (hD : ∀ v, 0 ≤ D v) :
    0 ≤ finiteExtensionDivisorDegree K L D := by
  apply D.sum_nonneg'
  intro v
  exact mul_nonneg (hD v) (by positivity)

/-- Nonzero elements of the finite constant field have trivial exhaustive
principal divisor. -/
theorem finiteExtensionPrincipalDivisor_algebraMap_constant
    (c : K) (hc : c ≠ 0) :
    finiteExtensionPrincipalDivisor K L (algebraMap K L c) = 0 := by
  let n := Fintype.card K - 1
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.sub_pos_of_lt Fintype.one_lt_card
  have hcL : algebraMap K L c ≠ 0 := by
    simpa only [map_zero] using (algebraMap K L).injective.ne hc
  have hpow : (algebraMap K L c) ^ n = 1 := by
    rw [← map_pow, FiniteField.pow_card_sub_one_eq_one c hc, map_one]
  have hdiv := finiteExtensionPrincipalDivisor_pow K L
    (algebraMap K L c) hcL n
  rw [hpow, finiteExtensionPrincipalDivisor_one K L] at hdiv
  ext v
  change finiteExtensionPrincipalDivisor K L (algebraMap K L c) v = (0 : ℤ)
  have hv := congrArg (fun D : FiniteExtensionDivisor K L ↦ D v) hdiv
  simp only [Finsupp.zero_apply, Finsupp.smul_apply, nsmul_eq_mul] at hv
  exact (mul_eq_zero.mp hv.symm).resolve_left (by exact_mod_cast hn.ne')

/-- The all-place Riemann space `L(D)`.  Zero is handled separately because
the existing principal-divisor API assigns integer coefficients only to
nonzero functions. -/
def finiteExtensionRiemannSpace (D : FiniteExtensionDivisor K L) :
    Submodule K L where
  carrier := {x | x = 0 ∨ (x ≠ 0 ∧ ∀ v,
    0 ≤ finiteExtensionPrincipalDivisor K L x v + D v)}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro x y (hx0 | ⟨hx0, hx⟩) (hy0 | ⟨hy0, hy⟩)
    · exact Or.inl (by simp [hx0, hy0])
    · subst x
      simpa only [zero_add, Set.mem_setOf_eq] using
        (Or.inr ⟨hy0, hy⟩ : y = 0 ∨ (y ≠ 0 ∧ ∀ v,
          0 ≤ finiteExtensionPrincipalDivisor K L y v + D v))
    · subst y
      simpa only [add_zero, Set.mem_setOf_eq] using
        (Or.inr ⟨hx0, hx⟩ : x = 0 ∨ (x ≠ 0 ∧ ∀ v,
          0 ≤ finiteExtensionPrincipalDivisor K L x v + D v))
    · by_cases hxy : x + y = 0
      · exact Or.inl hxy
      · refine Or.inr ⟨hxy, ?_⟩
        intro v
        have horder := finiteExtensionPrincipalDivisor_add_ge_min
          K L x y hx0 hy0 hxy v
        have hxmin : -D v ≤ finiteExtensionPrincipalDivisor K L x v := by
          have hxv := hx v
          omega
        have hymin : -D v ≤ finiteExtensionPrincipalDivisor K L y v := by
          have hyv := hy v
          omega
        have hmin : -D v ≤ min
            (finiteExtensionPrincipalDivisor K L x v)
            (finiteExtensionPrincipalDivisor K L y v) :=
          le_min hxmin hymin
        omega
  smul_mem' := by
    intro c x hx
    by_cases hc : c = 0
    · subst c
      exact Or.inl (zero_smul K x)
    rcases hx with hx | ⟨hx, horders⟩
    · subst x
      exact Or.inl (smul_zero c)
    · have hcL : algebraMap K L c ≠ 0 := by
        simpa only [map_zero] using (algebraMap K L).injective.ne hc
      have hcx : c • x ≠ 0 := by
        rw [Algebra.smul_def]
        exact mul_ne_zero hcL hx
      refine Or.inr ⟨hcx, ?_⟩
      intro v
      rw [Algebra.smul_def,
        finiteExtensionPrincipalDivisor_mul K L _ _ hcL hx,
        finiteExtensionPrincipalDivisor_algebraMap_constant K L c hc]
      simpa using horders v

@[simp]
theorem mem_finiteExtensionRiemannSpace
    {D : FiniteExtensionDivisor K L} {x : L} :
    x ∈ finiteExtensionRiemannSpace K L D ↔
      x = 0 ∨ (x ≠ 0 ∧ ∀ v,
        0 ≤ finiteExtensionPrincipalDivisor K L x v + D v) :=
  Iff.rfl

/-- Increasing the allowed divisor enlarges the Riemann space. -/
theorem finiteExtensionRiemannSpace_mono
    {D E : FiniteExtensionDivisor K L} (hDE : D ≤ E) :
    finiteExtensionRiemannSpace K L D ≤
      finiteExtensionRiemannSpace K L E := by
  intro x hx
  rw [mem_finiteExtensionRiemannSpace] at hx ⊢
  rcases hx with hx | ⟨hx0, hx⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hx0, ?_⟩
    intro v
    have hv := hDE v
    have hxv := hx v
    omega

/-- Every constant belongs to `L(D)` when `D` is effective. -/
theorem algebraMap_mem_finiteExtensionRiemannSpace_of_effective
    {D : FiniteExtensionDivisor K L} (hD : ∀ v, 0 ≤ D v) (c : K) :
    algebraMap K L c ∈ finiteExtensionRiemannSpace K L D := by
  by_cases hc : c = 0
  · subst c
    simpa using (finiteExtensionRiemannSpace K L D).zero_mem
  · rw [mem_finiteExtensionRiemannSpace]
    refine Or.inr ⟨?_, ?_⟩
    · simpa only [map_zero] using (algebraMap K L).injective.ne hc
    intro v
    rw [finiteExtensionPrincipalDivisor_algebraMap_constant K L c hc]
    simpa using hD v

/-- The Riemann spaces form a multiplicative divisor filtration. -/
theorem finiteExtensionRiemannSpace_mul_mem
    {D E : FiniteExtensionDivisor K L} {x y : L}
    (hx : x ∈ finiteExtensionRiemannSpace K L D)
    (hy : y ∈ finiteExtensionRiemannSpace K L E) :
    x * y ∈ finiteExtensionRiemannSpace K L (D + E) := by
  rw [mem_finiteExtensionRiemannSpace] at hx hy ⊢
  rcases hx with hx | ⟨hx0, hx⟩
  · exact Or.inl (by simp [hx])
  rcases hy with hy | ⟨hy0, hy⟩
  · exact Or.inl (by simp [hy])
  refine Or.inr ⟨mul_ne_zero hx0 hy0, ?_⟩
  intro v
  rw [finiteExtensionPrincipalDivisor_mul K L x y hx0 hy0,
    Finsupp.add_apply]
  have hxv := hx v
  have hyv := hy v
  simp only [Finsupp.add_apply] at hxv hyv ⊢
  omega

/-- Powers respect the multiplicative divisor filtration. -/
theorem finiteExtensionRiemannSpace_pow_mem
    {D : FiniteExtensionDivisor K L} {x : L}
    (hx : x ∈ finiteExtensionRiemannSpace K L D) (n : ℕ) :
    x ^ n ∈ finiteExtensionRiemannSpace K L (n • D) := by
  rw [mem_finiteExtensionRiemannSpace] at hx ⊢
  rcases hx with hx | ⟨hx0, hx⟩
  · subst x
    by_cases hn : n = 0
    · subst n
      simp only [pow_zero, zero_nsmul]
      refine Or.inr ⟨one_ne_zero, ?_⟩
      intro v
      rw [finiteExtensionPrincipalDivisor_one K L]
      simp
    · exact Or.inl (zero_pow hn)
  refine Or.inr ⟨pow_ne_zero n hx0, ?_⟩
  intro v
  rw [finiteExtensionPrincipalDivisor_pow K L x hx0 n]
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  have hxv := hx v
  have hn : (0 : ℤ) ≤ n := by positivity
  nlinarith

/-- The elementary vanishing half of Riemann--Roch: a divisor of negative
degree has no nonzero section.  This uses only effectiveness and the product
formula, not Riemann--Roch. -/
theorem finiteExtensionRiemannSpace_eq_bot_of_divisorDegree_neg
    {D : FiniteExtensionDivisor K L}
    (hD : finiteExtensionDivisorDegree K L D < 0) :
    finiteExtensionRiemannSpace K L D = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_bot]
    rw [mem_finiteExtensionRiemannSpace] at hx
    rcases hx with hx | ⟨hx0, hx⟩
    · exact hx
    · exfalso
      let E := finiteExtensionPrincipalDivisor K L x + D
      have hEeffective : ∀ v, 0 ≤ E v := by
        intro v
        exact hx v
      have hEdegree :=
        finiteExtensionDivisorDegree_nonnegative_of_effective K L E hEeffective
      rw [finiteExtensionDivisorDegree_add,
        finiteExtensionDivisorDegree_principal K L x hx0, zero_add] at hEdegree
      omega
  · exact bot_le

/-- Functions whose only permitted pole is at `P`, with order at most `n`. -/
def finiteExtensionOnePointRiemannSpace
    (P : FiniteExtensionPlace K L) (n : ℕ) : Submodule K L := by
  classical
  exact finiteExtensionRiemannSpace K L (Finsupp.single P (n : ℤ))

/-- Membership in `L(nP)` is the expected pole bound at `P`, together with
regularity at every other place. -/
theorem mem_finiteExtensionOnePointRiemannSpace_iff
    (P : FiniteExtensionPlace K L) (n : ℕ) (x : L) :
    x ∈ finiteExtensionOnePointRiemannSpace K L P n ↔
      x = 0 ∨ (x ≠ 0 ∧
        -(n : ℤ) ≤ finiteExtensionPrincipalDivisor K L x P ∧
        ∀ v, v ≠ P → 0 ≤ finiteExtensionPrincipalDivisor K L x v) := by
  classical
  rw [finiteExtensionOnePointRiemannSpace,
    mem_finiteExtensionRiemannSpace]
  constructor
  · rintro (hx | ⟨hx0, hx⟩)
    · exact Or.inl hx
    · refine Or.inr ⟨hx0, ?_, ?_⟩
      · have hP := hx P
        simp only [Finsupp.single_eq_same] at hP
        omega
      · intro v hv
        have hvOrder := hx v
        simp only [Finsupp.single_eq_of_ne hv] at hvOrder
        simpa using hvOrder
  · rintro (hx | ⟨hx0, hP, hAway⟩)
    · exact Or.inl hx
    · refine Or.inr ⟨hx0, ?_⟩
      intro v
      by_cases hv : v = P
      · subst v
        simp only [Finsupp.single_eq_same]
        omega
      · simp only [Finsupp.single_eq_of_ne hv, add_zero]
        exact hAway v hv

/-- Every constant belongs to every one-point Riemann space. -/
theorem algebraMap_mem_finiteExtensionOnePointRiemannSpace
    (P : FiniteExtensionPlace K L) (n : ℕ) (c : K) :
    algebraMap K L c ∈ finiteExtensionOnePointRiemannSpace K L P n := by
  classical
  apply algebraMap_mem_finiteExtensionRiemannSpace_of_effective K L
  intro v
  by_cases hv : v = P
  · subst v
    simp
  · simp [Finsupp.single_eq_of_ne hv]

/-- The one-point Riemann spaces are nested by pole order. -/
theorem finiteExtensionOnePointRiemannSpace_mono
    (P : FiniteExtensionPlace K L) {m n : ℕ} (hmn : m ≤ n) :
    finiteExtensionOnePointRiemannSpace K L P m ≤
      finiteExtensionOnePointRiemannSpace K L P n := by
  classical
  apply finiteExtensionRiemannSpace_mono K L
  intro v
  by_cases hv : v = P
  · subst v
    simp only [Finsupp.single_eq_same]
    exact_mod_cast hmn
  · simp only [Finsupp.single_eq_of_ne hv]
    exact le_rfl

/-- Products add the allowed pole orders in the one-point filtration. -/
theorem finiteExtensionOnePointRiemannSpace_mul_mem
    (P : FiniteExtensionPlace K L) {m n : ℕ} {x y : L}
    (hx : x ∈ finiteExtensionOnePointRiemannSpace K L P m)
    (hy : y ∈ finiteExtensionOnePointRiemannSpace K L P n) :
    x * y ∈ finiteExtensionOnePointRiemannSpace K L P (m + n) := by
  classical
  change x * y ∈ finiteExtensionRiemannSpace K L
    (Finsupp.single P ((m + n : ℕ) : ℤ))
  have hmul := finiteExtensionRiemannSpace_mul_mem K L hx hy
  have hdivisor :
      Finsupp.single P ((m + n : ℕ) : ℤ) =
        Finsupp.single P (m : ℤ) + Finsupp.single P (n : ℤ) := by
    ext v
    by_cases hv : v = P
    · subst v
      simp
    · simp [Finsupp.single_eq_of_ne hv]
  rw [hdivisor]
  exact hmul

end

end BGS.CorvajaZannier
