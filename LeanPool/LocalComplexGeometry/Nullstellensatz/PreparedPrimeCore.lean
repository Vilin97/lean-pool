/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Nullstellensatz.GenericFiber
import LeanPool.LocalComplexGeometry.Nullstellensatz.DivisibilitySpecialization
import LeanPool.LocalComplexGeometry.Nullstellensatz.DivisionRepresentatives
import LeanPool.LocalComplexGeometry.Nullstellensatz.MinpolyResultant
import LeanPool.LocalComplexGeometry.Nullstellensatz.PolynomialFibers
import LeanPool.LocalComplexGeometry.Nullstellensatz.PolynomialRepresentativeOperations
import LeanPool.LocalComplexGeometry.Nullstellensatz.PrimeCancellation
import LeanPool.LocalComplexGeometry.Nullstellensatz.PrimeInduction
import LeanPool.LocalComplexGeometry.Nullstellensatz.PreparedRootLocality
import LeanPool.LocalComplexGeometry.Nullstellensatz.ResultantSpecialization
import LeanPool.LocalComplexGeometry.Nullstellensatz.PolynomialSpecialization

/-!
# The prepared-prime geometric step

This file joins the generic-fibre algebra to the local geometry of finite
prepared fibres.  The small certificate below deliberately records only the
finite pointwise information used by the geometric argument.  Its fields are
later furnished by denominator-cleared minimal-polynomial identities.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

/-- Chosen representatives respect a finite product after one common
shrinking. -/
theorem eventually_representative_finsetProd {n : ℕ} {ι : Type*}
    (S : Finset ι) (f : ι → HolomorphicGerm n) :
    ∀ᶠ z in nhds (0 : ComplexEuclidean n),
      HolomorphicGerm.representative (∏ i ∈ S, f i) z =
        ∏ i ∈ S, HolomorphicGerm.representative (f i) z := by
  apply Filter.Germ.coe_eq.mp
  calc
    (HolomorphicGerm.representative (∏ i ∈ S, f i) : FunctionGerm n) =
        ((∏ i ∈ S, f i : HolomorphicGerm n) : FunctionGerm n) :=
      HolomorphicGerm.coe_representative (∏ i ∈ S, f i)
    _ = ∏ i ∈ S, (f i : FunctionGerm n) := by
      exact map_prod (holomorphicGermSubring n).subtype f S
    _ = ∏ i ∈ S,
        (HolomorphicGerm.representative (f i) : FunctionGerm n) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (HolomorphicGerm.coe_representative (f i)).symm
    _ = (Filter.Germ.coeRingHom (nhds (0 : ComplexEuclidean n)))
          (∏ i ∈ S, HolomorphicGerm.representative (f i)) := by
      exact (map_prod
        (Filter.Germ.coeRingHom (nhds (0 : ComplexEuclidean n)))
        (fun i ↦ HolomorphicGerm.representative (f i)) S).symm
    _ = ((fun z ↦ ∏ i ∈ S,
        HolomorphicGerm.representative (f i) z) : FunctionGerm n) := by
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall (fun _ ↦ by simp)

/-- Binary form of representative multiplication. -/
theorem eventually_representative_mul {n : ℕ}
    (f g : HolomorphicGerm n) :
    ∀ᶠ z in nhds (0 : ComplexEuclidean n),
      HolomorphicGerm.representative (f * g) z =
        HolomorphicGerm.representative f z *
          HolomorphicGerm.representative g z := by
  apply Filter.Germ.coe_eq.mp
  calc
    (HolomorphicGerm.representative (f * g) : FunctionGerm n) =
        (f * g : FunctionGerm n) :=
      HolomorphicGerm.coe_representative (f * g)
    _ = (f : FunctionGerm n) * (g : FunctionGerm n) := rfl
    _ = (HolomorphicGerm.representative f : FunctionGerm n) *
        (HolomorphicGerm.representative g : FunctionGerm n) := by
      rw [HolomorphicGerm.coe_representative,
        HolomorphicGerm.coe_representative]
    _ = (Filter.Germ.coeRingHom (nhds (0 : ComplexEuclidean n)))
        (HolomorphicGerm.representative f *
          HolomorphicGerm.representative g) := by
      exact (map_mul
        (Filter.Germ.coeRingHom (nhds (0 : ComplexEuclidean n)))
        (HolomorphicGerm.representative f)
        (HolomorphicGerm.representative g)).symm
    _ = ((fun z ↦ HolomorphicGerm.representative f z *
        HolomorphicGerm.representative g z) : FunctionGerm n) := rfl

/-- Finite pointwise data extracted from the denominator-cleared generic
minimal polynomial for one target germ.  The final field is the purely
algebraic return path: once all coefficients of the small remainder lie in
the contraction, generic divisibility puts the target back in the ambient
prime. -/
structure PreparedPrimeFiberCertificate {n d : ℕ}
    (a : Fin d → ComplexEuclidean n → ℂ)
    (P : Ideal (HolomorphicGerm (n + 1)))
    (g : HolomorphicGerm (n + 1)) where
  /-- The positive degree of the generic minimal polynomial. -/
  e : ℕ
  positiveDegree : 0 < e
  /-- Coefficients of the specialized minimal polynomial. -/
  q : Fin (e + 1) → HolomorphicGerm n
  /-- Coefficients of the specialized strict remainder. -/
  b : Fin e → HolomorphicGerm n
  /-- A base germ whose nonvanishing controls specialization. -/
  bad : HolomorphicGerm n
  bad_not_mem : bad ∉ lowerDimensionalContraction P
  eventually_specializes :
    ∀ᶠ z in nhds (0 : ComplexEuclidean n),
      (∀ f : idealGeneratorFinset (lowerDimensionalContraction P),
          HolomorphicGerm.representative (f : HolomorphicGerm n) z = 0) →
      HolomorphicGerm.representative bad z ≠ 0 →
      let Qz := fixedDegreePolynomialAt
        (HolomorphicGerm.coefficientRepresentatives q) z
      Qz.natDegree = e ∧ Qz.Separable ∧
        ∀ w : ℂ, Qz.eval w = 0 →
          preparedValue a z w = 0 ∧
          (∀ f : idealGeneratorFinset P,
              HolomorphicGerm.representative
                (f : HolomorphicGerm (n + 1))
                (appendLastCLE n (z, w)) = 0) ∧
          (HolomorphicGerm.representative g
                (appendLastCLE n (z, w)) = 0 →
            (remainderPolynomialAt
              (HolomorphicGerm.coefficientRepresentatives b) z).eval w = 0)
  mem_of_coeff_mem :
    (∀ i, b i ∈ lowerDimensionalContraction P) → g ∈ P

/-- The geometric heart of the prepared-prime argument.  A finite-fibre
certificate turns vanishing on the ambient prime zero set into membership in
the prime, using the lower-dimensional prime theorem and cancellation of one
common bad factor. -/
theorem mem_prime_of_preparedPrimeFiberCertificate {n d : ℕ}
    (hprime : PrimeZeroSetProperty n)
    (hd : 0 < d)
    (a : Fin d → ComplexEuclidean n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (P : Ideal (HolomorphicGerm (n + 1))) (hP : P.IsPrime)
    (g : HolomorphicGerm (n + 1))
    (hg : g ∈ vanishingIdeal (idealZeroSetGerm P))
    (C : PreparedPrimeFiberCertificate a P g) :
    g ∈ P := by
  let P₀ : Ideal (HolomorphicGerm n) := lowerDimensionalContraction P
  have hP₀ : P₀.IsPrime := lowerDimensionalContraction_isPrime hP
  let S₀ := idealGeneratorFinset P₀
  let S := idealGeneratorFinset P
  let F₀ : S₀ → ComplexEuclidean n → ℂ :=
    fun f ↦ HolomorphicGerm.representative (f : HolomorphicGerm n)
  let F : S → ComplexEuclidean (n + 1) → ℂ :=
    fun f ↦ HolomorphicGerm.representative
      (f : HolomorphicGerm (n + 1))
  let G : ComplexEuclidean (n + 1) → ℂ :=
    HolomorphicGerm.representative g
  have hF₀ : ∀ f, AnalyticAt ℂ (F₀ f) 0 := by
    intro f
    exact HolomorphicGerm.analyticAt_representative (f : HolomorphicGerm n)
  have hF : ∀ f, AnalyticAt ℂ (F f) 0 := by
    intro f
    exact HolomorphicGerm.analyticAt_representative
      (f : HolomorphicGerm (n + 1))
  have hG : AnalyticAt ℂ G 0 :=
    HolomorphicGerm.analyticAt_representative g
  have hzeroG : ∀ᶠ x in nhds (0 : ComplexEuclidean (n + 1)),
      (∀ f, F f x = 0) → G x = 0 := by
    have hZG : idealZeroSetGerm P ≤ germZeroLocus g := hg
    rw [idealZeroSetGerm_eq_of_span_eq P S
      (by simpa only [S] using span_idealGeneratorFinset P)] at hZG
    rw [finiteCommonZeroSet_eq_fintypeCommonZeroSet_subtype] at hZG
    have hfamily :
        (fun f ↦ HolomorphicGerm.ofFunction (F f) (hF f)) =
          (fun f : S ↦ (f : HolomorphicGerm (n + 1))) := by
      funext f
      apply Subtype.ext
      exact HolomorphicGerm.coe_representative
        (f : HolomorphicGerm (n + 1))
    have hgerm : HolomorphicGerm.ofFunction G hG = g := by
      apply Subtype.ext
      exact HolomorphicGerm.coe_representative g
    have hZG' :
        fintypeCommonZeroSet
            (fun f ↦ HolomorphicGerm.ofFunction (F f) (hF f)) ≤
          germZeroLocus (HolomorphicGerm.ofFunction G hG) := by
      rw [hfamily, hgerm]
      exact hZG
    exact (fintypeCommonZeroSet_le_iff_eventually F hF G hG).mp hZG'
  have hzeroGOnRoots :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n), ∀ w : ℂ,
        preparedValue a z w = 0 →
          ((∀ f, F f (appendLastCLE n (z, w)) = 0) →
            G (appendLastCLE n (z, w)) = 0) :=
    eventually_on_all_prepared_roots hd a ha ha0 hzeroG
  have hcoeff (i : Fin C.e) : C.b i ∈ P₀ := by
    apply mem_prime_of_mul_vanishes_on_zeroSet hprime P₀ hP₀
      C.bad_not_mem
    let Bfun : ComplexEuclidean n → ℂ :=
      HolomorphicGerm.representative (C.b i)
    let Dfun : ComplexEuclidean n → ℂ :=
      HolomorphicGerm.representative C.bad
    have hBfun : AnalyticAt ℂ Bfun 0 :=
      HolomorphicGerm.analyticAt_representative (C.b i)
    have hDfun : AnalyticAt ℂ Dfun 0 :=
      HolomorphicGerm.analyticAt_representative C.bad
    have hDBfun : AnalyticAt ℂ (Dfun * Bfun) 0 := hDfun.mul hBfun
    have hprod : HolomorphicGerm.ofFunction (Dfun * Bfun) hDBfun =
        C.bad * C.b i := by
      apply Subtype.ext
      change ((Dfun * Bfun : ComplexEuclidean n → ℂ) : FunctionGerm n) =
        (C.bad : FunctionGerm n) * (C.b i : FunctionGerm n)
      rw [Filter.Germ.coe_mul,
        HolomorphicGerm.coe_representative,
        HolomorphicGerm.coe_representative]
    rw [← hprod]
    rw [idealZeroSetGerm_eq_of_span_eq P₀ S₀
      (by simpa only [S₀] using span_idealGeneratorFinset P₀)]
    rw [finiteCommonZeroSet_eq_fintypeCommonZeroSet_subtype]
    have hfamily :
        (fun f ↦ HolomorphicGerm.ofFunction (F₀ f) (hF₀ f)) =
          (fun f : S₀ ↦ (f : HolomorphicGerm n)) := by
      funext f
      apply Subtype.ext
      exact HolomorphicGerm.coe_representative (f : HolomorphicGerm n)
    rw [← hfamily]
    apply (fintypeCommonZeroSet_le_iff_eventually F₀ hF₀
      (Dfun * Bfun) hDBfun).mpr
    filter_upwards [C.eventually_specializes, hzeroGOnRoots] with z hspec hzG
    intro hz₀
    by_cases hDz : Dfun z = 0
    · simp [hDz]
    · have hdata := hspec (by simpa only [F₀, S₀, P₀] using hz₀)
          (by simpa only [Dfun] using hDz)
      dsimp only at hdata
      obtain ⟨hdegree, hsep, hroots⟩ := hdata
      have hQne : fixedDegreePolynomialAt
          (HolomorphicGerm.coefficientRepresentatives C.q) z ≠ 0 := by
        intro hQzero
        rw [hQzero, Polynomial.natDegree_zero] at hdegree
        exact (Nat.ne_of_gt C.positiveDegree) hdegree.symm
      have hBzero : remainderPolynomialAt
          (HolomorphicGerm.coefficientRepresentatives C.b) z = 0 := by
        apply polynomial_eq_zero_of_natDegree_lt_of_vanishes_on_separableRoots
          hQne hsep
        · rw [hdegree]
          exact remainderPolynomialAt_natDegree_lt C.positiveDegree _ z
        · intro w hw
          obtain ⟨hprepared, hgens, htarget⟩ := hroots w hw
          apply htarget
          apply hzG w hprepared
          simpa only [F, S] using hgens
      have hbiz : Bfun z = 0 := by
        simpa only [Bfun, HolomorphicGerm.coefficientRepresentatives] using
          remainderPolynomialAt_coeff_eq_zero
            (HolomorphicGerm.coefficientRepresentatives C.b) z hBzero i
      simp [hbiz]
  exact C.mem_of_coeff_mem fun i ↦ by
    simpa only [P₀] using hcoeff i


end

end LocalComplexGeometry
