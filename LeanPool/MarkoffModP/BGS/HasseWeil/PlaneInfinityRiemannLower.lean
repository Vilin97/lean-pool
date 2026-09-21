/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneOnePointRiemannLower
import Mathlib.Tactic

/-!
# Riemann's inequality for divisors supported above infinity

The first coordinate of a plane curve has a pole at every branch above the
rational-function place at infinity.  Its pole divisor is therefore cofinal
among effective divisors supported on those branches.  A sufficiently large
rectangular monomial pole budget dominates any such divisor.

The monomial budget already satisfies the bidegree form of Riemann's
inequality.  Removing the effective difference costs at most its divisor
degree, so the same inequality descends to the original infinity-supported
divisor.
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

/-- An effective divisor supported above infinity is dominated by a natural
multiple of any effective divisor that is positive at every infinity
place. -/
theorem exists_nsmul_ge_of_effective_supportedAtInfinity
    (E H : FiniteExtensionDivisor K L)
    (hE : ∀ v, 0 ≤ E v)
    (hEfinite : ∀ q : FiniteExtensionFinitePlace K L, E (.inl q) = 0)
    (hH : ∀ v, 0 ≤ H v)
    (hHinfinity : ∀ P : FiniteExtensionInfinityPlace K L, 0 < H (.inr P)) :
    ∃ n : ℕ, E ≤ n • H := by
  classical
  let n : ℕ := ∑ v ∈ E.support, (E v).toNat
  refine ⟨n, ?_⟩
  intro v
  rcases v with q | P
  · rw [hEfinite q]
    exact nsmul_nonneg (hH (.inl q)) n
  · have hEPnonneg : 0 ≤ E (.inr P) := hE (.inr P)
    by_cases hEPzero : E (.inr P) = 0
    · rw [hEPzero]
      exact nsmul_nonneg (hH (.inr P)) n
    · have hmem : (.inr P : FiniteExtensionPlace K L) ∈ E.support :=
        Finsupp.mem_support_iff.mpr hEPzero
      have htermNonneg : ∀ v ∈ E.support, 0 ≤ (E v).toNat := by
        intro v hv
        positivity
      have hcoeff : (E (.inr P)).toNat ≤ n := by
        dsimp only [n]
        exact Finset.single_le_sum htermNonneg hmem
      have hcoeffInt : E (.inr P) ≤ (n : ℤ) := by
        rw [← Int.toNat_of_nonneg hEPnonneg]
        exact_mod_cast hcoeff
      have hHone : (1 : ℤ) ≤ H (.inr P) := by
        exact hHinfinity P
      simp only [Finsupp.nsmul_apply, nsmul_eq_mul]
      nlinarith

variable {K}

/-- Bidegree Riemann inequality for every effective divisor supported on the
infinity branches of an absolutely irreducible plane curve. -/
theorem planeCurve_infinitySupported_riemann_lower
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    ∀ (E : FiniteExtensionDivisor K (PlaneCurveFunctionField f)),
      (∀ v, 0 ≤ E v) →
      (∀ q : FiniteExtensionFinitePlace K
        (PlaneCurveFunctionField f), E (.inl q) = 0) →
      (finiteExtensionDivisorDegree K (PlaneCurveFunctionField f) E).toNat + 1 ≤
        Module.finrank K
            (finiteExtensionRiemannSpace K (PlaneCurveFunctionField f) E) +
          planeCurveBidegreeGenusBudget f := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  let a := MvPolynomial.degreeOf 0 f
  let b := MvPolynomial.degreeOf 1 f
  let g := planeCurveBidegreeGenusBudget f
  letI : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let constantAlg : Algebra K L :=
    RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
      (algebraMap K (RatFunc K)))
  letI : Algebra K L := constantAlg
  letI : SMul K L := constantAlg.toSMul
  letI : Module K L := constantAlg.toModule
  letI : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro E hE hEfinite
  let H := finiteExtensionPoleDivisor K L x
  have hH : ∀ v, 0 ≤ H v :=
    finiteExtensionPoleDivisor_effective K L x
  have hHinfinity : ∀ P : FiniteExtensionInfinityPlace K L,
      0 < H (.inr P) := by
    simpa only [H, L, x] using
      finiteExtensionPoleDivisor_planeCurveFirstCoordinate_inr_positive
        hf hpartialSecond
  obtain ⟨n, hEH⟩ :=
    exists_nsmul_ge_of_effective_supportedAtInfinity
      K L E H hE hEfinite hH hHinfinity
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
  letI : Module.Finite K (finiteExtensionRiemannSpace K L E) :=
    finiteExtensionRiemannSpace_effective_moduleFinite K L E hE
  have hstrip :=
    finiteExtensionRiemannSpace_add_effective K L E A hE hA
  rw [hsplit] at hstrip
  have hmono : (n + 1) * b ≤
      Module.finrank K (finiteExtensionRiemannSpace K L D) := by
    simpa only [D, L, x, y, b] using
      planeCurveMonomialPoleBudget_finrank_lower
        hf hpartialFirst hpartialSecond n
  have hxHeight : finiteExtensionHeight K L x = b := by
    simpa only [L, x, b] using
      finiteExtensionHeight_planeCurveFirstCoordinate hf hpartialSecond
  have hyHeight : finiteExtensionHeight K L y ≤ a := by
    simpa only [L, y, a] using
      planeCurveSecondCoordinate_height_le_degreeOf_first
        hf hpartialFirst hpartialSecond
  have hDdegree : finiteExtensionDivisorDegree K L D ≤
      (n * b + (b - 1) * a : ℕ) := by
    dsimp only [D, planeMonomialPoleBudget]
    rw [finiteExtensionDivisorDegree_pow_mul_pow_budget, hxHeight]
    have hyCast : (finiteExtensionHeight K L y : ℤ) ≤ (a : ℤ) := by
      exact_mod_cast hyHeight
    calc
      (n : ℤ) * (b : ℤ) + ((b - 1 : ℕ) : ℤ) *
          (finiteExtensionHeight K L y : ℤ) ≤
          (n : ℤ) * (b : ℤ) + ((b - 1 : ℕ) : ℤ) * (a : ℤ) := by
        gcongr
      _ = (n * b + (b - 1) * a : ℕ) := by
        push_cast
        ring
  have hDdegreeNonnegative : 0 ≤ finiteExtensionDivisorDegree K L D :=
    finiteExtensionDivisorDegree_nonnegative_of_effective K L D hD
  have hDdegreeNat : (finiteExtensionDivisorDegree K L D).toNat ≤
      n * b + (b - 1) * a := by
    have hcast : (((finiteExtensionDivisorDegree K L D).toNat : ℕ) : ℤ) =
        finiteExtensionDivisorDegree K L D :=
      Int.toNat_of_nonneg hDdegreeNonnegative
    exact_mod_cast (hcast ▸ hDdegree)
  have haPos : 0 < a := degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst
  have hbPos : 0 < b := degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond
  have hgenusIdentity :
      n * b + (b - 1) * a + 1 = (n + 1) * b + g := by
    dsimp only [g, planeCurveBidegreeGenusBudget, a, b]
    nlinarith [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr haPos.ne'),
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hbPos.ne')]
  have hDriemann : (finiteExtensionDivisorDegree K L D).toNat + 1 ≤
      Module.finrank K (finiteExtensionRiemannSpace K L D) + g := by
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
  change (finiteExtensionDivisorDegree K L E).toNat + 1 ≤
    Module.finrank K (finiteExtensionRiemannSpace K L E) + g
  omega

end

end BGS.HasseWeil
