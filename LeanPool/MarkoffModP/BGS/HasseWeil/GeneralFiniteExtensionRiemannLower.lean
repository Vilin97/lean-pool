/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneInfinityRiemannLower
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneFinitePlaceRiemannLower
import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncParameterPole
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Tactic

/-!
# A coarse Riemann inequality for arbitrary function fields

This file derives the amount of Riemann-space growth needed by the intrinsic
Stepanov argument without appealing to an external Riemann--Roch theorem.

For a finite separable extension `L / K(X)`, choose a primitive element `y`.
The monomials `X^i y^j` with `j < [L : K(X)]` are linearly independent.  Their
pole divisors give a cofinal family of effective divisors supported above
infinity and hence a coarse, but uniform-for-`L`, Riemann inequality.  The
finite-place approximation theorem then transfers this inequality to every
one-point divisor at a finite place.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped nonZeroDivisors Polynomial BigOperators

noncomputable section


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance generalRiemannConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance generalRiemannConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance generalRiemannInfinityModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

/-- A monomial grid with the expected `X`-height gives a Riemann inequality
for every effective divisor supported above infinity. -/
theorem infinitySupported_riemann_lower_of_monomial
    (x y : L) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (b : Nat)
    (hLI : ∀ n, LinearIndependent K
      (planeMonomialGrid x y (n + 1) b))
    (hxHeight : finiteExtensionHeight K L x = b)
    (hxInfinity : ∀ P : FiniteExtensionInfinityPlace K L,
      0 < finiteExtensionPoleDivisor K L x (.inr P)) :
    ∀ (E : FiniteExtensionDivisor K L),
      (∀ v, 0 ≤ E v) →
      (∀ q : FiniteExtensionFinitePlace K L, E (.inl q) = 0) →
      (finiteExtensionDivisorDegree K L E).toNat + 1 ≤
        Module.finrank K (finiteExtensionRiemannSpace K L E) +
          ((b - 1) * finiteExtensionHeight K L y + 1) := by
  intro E hE hEfinite
  let H := finiteExtensionPoleDivisor K L x
  have hH : ∀ v, 0 ≤ H v :=
    finiteExtensionPoleDivisor_effective K L x
  obtain ⟨n, hEH⟩ :=
    exists_nsmul_ge_of_effective_supportedAtInfinity
      K L E H hE hEfinite hH hxInfinity
  let D : FiniteExtensionDivisor K L :=
    planeMonomialPoleBudget K L x y n b
  have hD : ∀ v, 0 ≤ D v := by
    intro v
    dsimp only [D, planeMonomialPoleBudget]
    simp only [Finsupp.add_apply, Finsupp.nsmul_apply]
    exact add_nonneg
      (nsmul_nonneg (finiteExtensionPoleDivisor_effective K L x v) n)
      (nsmul_nonneg (finiteExtensionPoleDivisor_effective K L y v) (b - 1))
  have hED : E ≤ D := by
    intro v
    have hleft := hEH v
    dsimp only [H] at hleft
    dsimp only [D, planeMonomialPoleBudget]
    exact hleft.trans (le_add_of_nonneg_right
      (nsmul_nonneg (finiteExtensionPoleDivisor_effective K L y v) (b - 1)))
  let A : FiniteExtensionDivisor K L := D - E
  have hA : ∀ v, 0 ≤ A v := by
    intro v
    dsimp only [A]
    exact sub_nonneg.mpr (hED v)
  have hsplit : E + A = D := by
    dsimp only [A]
    abel
  let : Module.Finite K (finiteExtensionRiemannSpace K L E) :=
    finiteExtensionRiemannSpace_effective_moduleFinite K L E hE
  have hstrip :=
    finiteExtensionRiemannSpace_add_effective K L E A hE hA
  rw [hsplit] at hstrip
  have hmono : (n + 1) * b ≤
      Module.finrank K (finiteExtensionRiemannSpace K L D) := by
    let hfiniteD : Module.Finite K (finiteExtensionRiemannSpace K L D) :=
      finiteExtensionRiemannSpace_effective_moduleFinite K L D hD
    exact add_one_mul_le_finrank_poleDivisorBudget
      K L x y hx0 hy0 n b (hLI n) hfiniteD
  have hDdegree : finiteExtensionDivisorDegree K L D =
      (n * b + (b - 1) * finiteExtensionHeight K L y : Nat) := by
    dsimp only [D, planeMonomialPoleBudget]
    rw [finiteExtensionDivisorDegree_pow_mul_pow_budget, hxHeight]
    push_cast
    ring
  have hDdegreeNonnegative : 0 ≤ finiteExtensionDivisorDegree K L D :=
    finiteExtensionDivisorDegree_nonnegative_of_effective K L D hD
  have hDdegreeNat : (finiteExtensionDivisorDegree K L D).toNat =
      n * b + (b - 1) * finiteExtensionHeight K L y := by
    apply Int.ofNat_injective
    rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg hDdegreeNonnegative]
    exact hDdegree
  have hDriemann : (finiteExtensionDivisorDegree K L D).toNat + 1 ≤
      Module.finrank K (finiteExtensionRiemannSpace K L D) +
        ((b - 1) * finiteExtensionHeight K L y + 1) := by
    rw [hDdegreeNat]
    have hnb : n * b ≤ (n + 1) * b :=
      Nat.mul_le_mul_right b (Nat.le_succ n)
    omega
  have hEdegreeNonnegative : 0 ≤ finiteExtensionDivisorDegree K L E :=
    finiteExtensionDivisorDegree_nonnegative_of_effective K L E hE
  have hAdegreeNonnegative : 0 ≤ finiteExtensionDivisorDegree K L A :=
    finiteExtensionDivisorDegree_nonnegative_of_effective K L A hA
  have hdegreeSplit :
      (finiteExtensionDivisorDegree K L D).toNat =
        (finiteExtensionDivisorDegree K L E).toNat +
          (finiteExtensionDivisorDegree K L A).toNat := by
    have hdegree : finiteExtensionDivisorDegree K L D =
        finiteExtensionDivisorDegree K L E +
          finiteExtensionDivisorDegree K L A := by
      rw [← hsplit, finiteExtensionDivisorDegree_add]
    rw [hdegree, Int.toNat_add hEdegreeNonnegative hAdegreeNonnegative]
  have hstripRank :
      Module.finrank K (finiteExtensionRiemannSpace K L D) ≤
        Module.finrank K (finiteExtensionRiemannSpace K L E) +
          (finiteExtensionDivisorDegree K L A).toNat := hstrip.2
  have hcombined :
      (finiteExtensionDivisorDegree K L E).toNat +
          (finiteExtensionDivisorDegree K L A).toNat + 1 ≤
        (Module.finrank K (finiteExtensionRiemannSpace K L E) +
            (finiteExtensionDivisorDegree K L A).toNat) +
          ((b - 1) * finiteExtensionHeight K L y + 1) := by
    calc
      (finiteExtensionDivisorDegree K L E).toNat +
            (finiteExtensionDivisorDegree K L A).toNat + 1 =
          (finiteExtensionDivisorDegree K L D).toNat + 1 := by
        rw [hdegreeSplit]
      _ ≤ Module.finrank K (finiteExtensionRiemannSpace K L D) +
          ((b - 1) * finiteExtensionHeight K L y + 1) := hDriemann
      _ ≤ (Module.finrank K (finiteExtensionRiemannSpace K L E) +
            (finiteExtensionDivisorDegree K L A).toNat) +
          ((b - 1) * finiteExtensionHeight K L y + 1) :=
        Nat.add_le_add_right hstripRank _
  omega

/-- A nonzero primitive element and the exact pole height of `X` supply the
monomial hypotheses of `infinitySupported_riemann_lower_of_monomial`. -/
theorem infinitySupported_riemann_lower_of_primitive
    (x y : L) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hxMap : algebraMap (RatFunc K) L RatFunc.X = x)
    (hprimitive : IntermediateField.adjoin (RatFunc K) {y} = ⊤)
    (hxHeight : finiteExtensionHeight K L x =
      Module.finrank (RatFunc K) L)
    (hxInfinity : ∀ P : FiniteExtensionInfinityPlace K L,
      0 < finiteExtensionPoleDivisor K L x (.inr P)) :
    ∀ (E : FiniteExtensionDivisor K L),
      (∀ v, 0 ≤ E v) →
      (∀ q : FiniteExtensionFinitePlace K L, E (.inl q) = 0) →
      (finiteExtensionDivisorDegree K L E).toNat + 1 ≤
        Module.finrank K (finiteExtensionRiemannSpace K L E) +
          ((Module.finrank (RatFunc K) L - 1) *
            finiteExtensionHeight K L y + 1) := by
  let d := Module.finrank (RatFunc K) L
  have hyInt : IsIntegral (RatFunc K) y := IsIntegral.of_finite _ _
  have hdegree : (minpoly (RatFunc K) y).natDegree = d := by
    calc
      (minpoly (RatFunc K) y).natDegree =
          Module.finrank (RatFunc K)
            (IntermediateField.adjoin (RatFunc K) {y}) :=
        (IntermediateField.adjoin.finrank hyInt).symm
      _ = Module.finrank (RatFunc K)
          (⊤ : IntermediateField (RatFunc K) L) := by
        rw [hprimitive]
      _ = Module.finrank (RatFunc K) L := by
        rw [IntermediateField.finrank_top']
  have hLI : ∀ n, LinearIndependent K
      (planeMonomialGrid x y (n + 1) d) := by
    intro n
    have h := planeMonomialGrid_linearIndependent_of_transcendental_minpoly
      (RatFunc.X : RatFunc K) y (n + 1) d RatFunc.transcendental_X
        (by rw [hdegree])
    rw [hxMap] at h
    exact h
  simpa only [d] using
    infinitySupported_riemann_lower_of_monomial K L x y hx0 hy0 d hLI
      (by simpa only [d] using hxHeight) hxInfinity

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- A finite separable extension has a primitive element which can be chosen
nonzero, including the degree-one case. -/
theorem exists_nonzero_primitive_element :
    ∃ y : L, y ≠ 0 ∧
      IntermediateField.adjoin (RatFunc K) {y} = ⊤ := by
  obtain ⟨y, hy⟩ := Field.exists_primitive_element (RatFunc K) L
  by_cases hy0 : y = 0
  · subst y
    refine ⟨1, one_ne_zero, ?_⟩
    simpa using hy
  · exact ⟨y, hy0, hy⟩

/-- The coarse primitive-element Riemann inequality at every finite place. -/
theorem finitePlace_riemann_lower_of_primitive
    (x y : L) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hxMap : algebraMap (RatFunc K) L RatFunc.X = x)
    (hprimitive : IntermediateField.adjoin (RatFunc K) {y} = ⊤)
    (hxHeight : finiteExtensionHeight K L x =
      Module.finrank (RatFunc K) L)
    (hxInfinity : ∀ P : FiniteExtensionInfinityPlace K L,
      0 < finiteExtensionPoleDivisor K L x (.inr P)) :
    ∀ (q : FiniteExtensionFinitePlace K L) (N : ℕ),
      N * finiteExtensionPlaceDegree K L (.inl q) + 1 ≤
        Module.finrank K (finiteExtensionOnePointRiemannSpace K L (.inl q) N) +
          ((Module.finrank (RatFunc K) L - 1) *
            finiteExtensionHeight K L y + 1) := by
  intro q N
  let g := (Module.finrank (RatFunc K) L - 1) *
    finiteExtensionHeight K L y + 1
  have hinfinity := infinitySupported_riemann_lower_of_primitive
    K L x y hx0 hy0 hxMap hprimitive hxHeight hxInfinity
  by_cases hN : N = 0
  · subst N
    have hzero := hinfinity
      (0 : FiniteExtensionDivisor K L) (by simp) (by simp)
    have hdegreezero :
        finiteExtensionDivisorDegree K L
          (0 : FiniteExtensionDivisor K L) = 0 := by
      simp [finiteExtensionDivisorDegree]
    rw [hdegreezero] at hzero
    simp only [Int.toNat_zero, zero_add] at hzero
    simp only [zero_mul, zero_add]
    change 1 ≤ Module.finrank K
      (finiteExtensionRiemannSpace K L (Finsupp.single (.inl q) 0)) + g
    rw [Finsupp.single_zero]
    simpa only [g] using hzero
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    obtain ⟨E, hE, hEfinite, hrank⟩ :=
      exists_infinityDivisor_finitePlacePrincipalParts_rank K L q N hNpos
    have hEinfinity :
        (finiteExtensionDivisorDegree K L E).toNat + 1 ≤
          Module.finrank K (finiteExtensionRiemannSpace K L E) + g := by
      simpa only [g] using hinfinity E hE hEfinite
    let Dq : FiniteExtensionDivisor K L :=
      Finsupp.single (.inl q) (N : ℤ)
    have hDq : ∀ v, 0 ≤ Dq v := by
      intro v
      by_cases hv : v = (.inl q : FiniteExtensionPlace K L)
      · subst v
        simp [Dq]
      · simp [Dq, Finsupp.single_eq_of_ne hv]
    let : Module.Finite K (finiteExtensionRiemannSpace K L Dq) :=
      finiteExtensionRiemannSpace_effective_moduleFinite K L Dq hDq
    have hstrip := finiteExtensionRiemannSpace_add_effective
      K L Dq E hDq hE
    change N * finiteExtensionPlaceDegree K L (.inl q) + 1 ≤
      Module.finrank K (finiteExtensionRiemannSpace K L Dq) + g
    have hDqEq : Dq = Finsupp.single (.inl q) (N : ℤ) := rfl
    rw [← hDqEq] at hrank
    omega

/-- Every finite separable extension of `K(X)` admits a single natural-number
budget for Riemann's inequality at all of its finite places.  The budget is
constructed from a nonzero primitive element; no genus or Riemann--Roch input
is assumed. -/
theorem exists_finitePlace_riemann_lower_budget :
    ∃ g : ℕ, ∀ (q : FiniteExtensionFinitePlace K L) (N : ℕ),
      N * finiteExtensionPlaceDegree K L (.inl q) + 1 ≤
        Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L (.inl q) N) + g := by
  let x : L := algebraMap (RatFunc K) L RatFunc.X
  obtain ⟨y, hy0, hprimitive⟩ := exists_nonzero_primitive_element K L
  let g := (Module.finrank (RatFunc K) L - 1) *
    finiteExtensionHeight K L y + 1
  refine ⟨g, ?_⟩
  have hx0 : x ≠ 0 := by
    dsimp only [x]
    simpa using (algebraMap (RatFunc K) L).injective.ne RatFunc.X_ne_zero
  have hxInfinity : ∀ P : FiniteExtensionInfinityPlace K L,
      0 < finiteExtensionPoleDivisor K L x (.inr P) := by
    intro P
    dsimp only [x]
    rw [finiteExtensionPoleDivisor_ratFuncX_inr_eq_ramificationIdx]
    exact_mod_cast P.1.ramificationIdx_pos (RatFuncInfinityIntegers K)
  simpa only [g] using
    finitePlace_riemann_lower_of_primitive K L x y hx0 hy0 rfl
      hprimitive (finiteExtensionHeight_ratFuncX_eq_finrank K L) hxInfinity

end

end BGS.HasseWeil
