/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalDifferentDivisor
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryFinitePlace
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic

/-!
# The sharp finite different bound for a plane curve

This file bounds the residue-weighted finite different of the plane function
field by the discriminant degree of the original second-coordinate equation.
The key local step chooses a reciprocal primitive element separately at each
base prime; a prime-unit denominator-clearing argument then compares its
minimal-polynomial discriminant with the global different.
-/

open scoped Polynomial nonZeroDivisors BigOperators
open Polynomial IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

theorem adjoin_smul_eq_top_of_adjoin_eq_top
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (r : K) (hr : r ≠ 0) (z : L)
    (hz : Algebra.adjoin K {z} = ⊤) :
    Algebra.adjoin K {r • z} = ⊤ := by
  apply (IntermediateField.adjoin_eq_top_iff).mp
  have hz' : IntermediateField.adjoin K {z} =
      (⊤ : IntermediateField K L) :=
    (IntermediateField.adjoin_eq_top_iff).mpr hz
  apply top_unique
  rw [← hz']
  apply IntermediateField.adjoin_simple_le_iff.mpr
  let H := IntermediateField.adjoin K {r • z}
  have hxmem : r • z ∈ H :=
    IntermediateField.mem_adjoin_simple_self K (r • z)
  have hmem : algebraMap K L (r⁻¹) * (r • z) ∈ H :=
    mul_mem (IntermediateField.algebraMap_mem H (r⁻¹)) hxmem
  have heq : z = algebraMap K L (r⁻¹) * (r • z) := by
    simp [Algebra.smul_def, hr]
  exact Eq.mpr (congrArg (fun x : L => x ∈ H) heq) hmem

theorem minpoly_discr_ne_zero_of_adjoin_eq_top
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (z : L) (hz : Algebra.adjoin K {z} = ⊤) :
    (minpoly K z).discr ≠ 0 := by
  let pb : PowerBasis K L :=
    PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral z) hz
  have hgen : pb.gen = z := PowerBasis.ofAdjoinEqTop'_gen _ _
  have hdisc := discr_powerBasis_eq_minpoly_discr pb
  rw [hgen] at hdisc
  rw [← hdisc]
  exact Algebra.discr_not_zero_of_basis K pb.basis

theorem powerBasis_discr_smul_eq_diagonal_det_sq_mul
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (r : K) (z : L) (pbz pbx : PowerBasis K L)
    (hgenZ : pbz.gen = z) (hgenX : pbx.gen = r • z) :
    Algebra.discr K pbx.basis =
      (Matrix.diagonal (fun i : Fin pbx.dim => r ^ (i : ℕ))).det ^ 2 *
        Algebra.discr K pbz.basis := by
  have hdim : pbx.dim = pbz.dim := pbx.finrank.symm.trans pbz.finrank
  let e : Fin pbx.dim ≃ Fin pbz.dim := finCongr hdim
  let P : Matrix (Fin pbx.dim) (Fin pbx.dim) K :=
    Matrix.diagonal (fun i => r ^ (i : ℕ))
  have hbasis : (fun i => pbx.basis i) =
      (P.map (algebraMap K L)).mulVec (fun i => pbz.basis (e i)) := by
    funext i
    rw [show pbx.basis i = pbx.gen ^ (i : ℕ) by
      simpa only [PowerBasis.coe_basis] using congrFun (PowerBasis.coe_basis pbx) i]
    rw [show P.map (algebraMap K L) =
        Matrix.diagonal (fun i : Fin pbx.dim =>
          algebraMap K L (r ^ (i : ℕ))) by
      ext i j
      simp only [P, Matrix.map_apply, Matrix.diagonal_apply]
      split <;> simp_all]
    rw [Matrix.mulVec_diagonal]
    rw [show pbz.basis (e i) = pbz.gen ^ ((e i : Fin pbz.dim) : ℕ) by
      simpa only [PowerBasis.coe_basis] using
        congrFun (PowerBasis.coe_basis pbz) (e i)]
    rw [hgenX, hgenZ]
    have hei : ((e i : Fin pbz.dim) : ℕ) = (i : ℕ) := by simp [e]
    rw [hei]
    simp [Algebra.smul_def, mul_pow]
  have hreindex : Algebra.discr K (fun i => pbz.basis (e i)) =
      Algebra.discr K pbz.basis := by
    simpa [Function.comp_def] using Algebra.discr_reindex K pbz.basis e.symm
  have hchange := Algebra.discr_of_matrix_mulVec
    (fun i => pbz.basis (e i)) P
  rw [← hbasis, hreindex] at hchange
  exact hchange

theorem exists_minpoly_discr_smul_eq_pow_mul
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (r : K) (hr : r ≠ 0) (z : L)
    (hz : Algebra.adjoin K {z} = ⊤) :
    ∃ N : ℕ, (minpoly K (r • z)).discr =
      r ^ N * (minpoly K z).discr := by
  let pbz : PowerBasis K L :=
    PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral z) hz
  have hgenZ : pbz.gen = z := by
    exact PowerBasis.ofAdjoinEqTop'_gen _ _
  have hx : Algebra.adjoin K {r • z} = ⊤ :=
    adjoin_smul_eq_top_of_adjoin_eq_top r hr z hz
  let pbx : PowerBasis K L :=
    PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral (r • z)) hx
  have hgenX : pbx.gen = r • z := by
    exact PowerBasis.ofAdjoinEqTop'_gen _ _
  have hdiscX := discr_powerBasis_eq_minpoly_discr pbx
  have hdiscZ := discr_powerBasis_eq_minpoly_discr pbz
  rw [hgenX] at hdiscX
  rw [hgenZ] at hdiscZ
  have hchange := powerBasis_discr_smul_eq_diagonal_det_sq_mul
    r z pbz pbx hgenZ hgenX
  let P : Matrix (Fin pbx.dim) (Fin pbx.dim) K :=
    Matrix.diagonal (fun i => r ^ (i : ℕ))
  have hdisc : (minpoly K (r • z)).discr =
      P.det ^ 2 * (minpoly K z).discr := by
    exact hdiscX.symm.trans (hchange.trans
      (congrArg (P.det ^ 2 * ·) hdiscZ))
  let d : ℕ := ∑ i : Fin pbx.dim, (i : ℕ)
  have hdet : P.det = r ^ d := by
    rw [show P.det = ∏ i : Fin pbx.dim, r ^ (i : ℕ) by
      simp [P, Matrix.det_diagonal]]
    simpa [d] using
      (Finset.prod_pow_eq_pow_sum Finset.univ
        (fun i : Fin pbx.dim => (i : ℕ)) r)
  refine ⟨2 * d, ?_⟩
  rw [hdisc, hdet]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

theorem finitePlaceOrder_mul_of_ne_zero
    {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (v : HeightOneSpectrum R) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    finitePlaceOrder v (x * y) =
      finitePlaceOrder v x + finitePlaceOrder v y := by
  have h := finitePlaceOrderTop_mul v x y
  rw [finitePlaceOrderTop_eq_coe v (x * y) (mul_ne_zero hx hy),
    finitePlaceOrderTop_eq_coe v x hx,
    finitePlaceOrderTop_eq_coe v y hy] at h
  exact_mod_cast h

theorem finitePlaceOrder_pow_of_ne_zero
    {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (v : HeightOneSpectrum R) (x : F) (hx : x ≠ 0) (n : ℕ) :
    finitePlaceOrder v (x ^ n) = n • finitePlaceOrder v x := by
  have h := finitePlaceOrderTop_pow v x n
  rw [finitePlaceOrderTop_eq_coe v (x ^ n) (pow_ne_zero n hx),
    finitePlaceOrderTop_eq_coe v x hx] at h
  exact_mod_cast h

theorem finitePlaceOrder_algebraMap_unit_eq_zero
    {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (v : HeightOneSpectrum R) (u : Rˣ) :
    finitePlaceOrder v (algebraMap R F (u : R)) = 0 := by
  have h := finitePlaceOrderTop_algebraMap_unit (A := R) (K := F) v u
  have hu : algebraMap R F (u : R) ≠ 0 :=
    by simpa using (IsFractionRing.injective R F).ne u.ne_zero
  rw [finitePlaceOrderTop_eq_coe v _ hu] at h
  exact_mod_cast h

/-- The discriminant of the second-coordinate plane equation is nonzero
under the separating-coordinate hypothesis. -/
theorem planeCurvePolynomialInSecondCoordinate_discr_ne_zero
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    (planeCurvePolynomialInSecondCoordinate f).discr ≠ 0 := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let F : (RatFunc K)[X] :=
    (planeCurvePolynomialInSecondCoordinate f).map
      (algebraMap K[X] (RatFunc K))
  have hFirreducible : Irreducible F :=
    planeCurvePolynomialInSecondCoordinate_ratFunc_irreducible
      hf hpartialSecond
  have hFroot : Polynomial.aeval (planeCurveFunction f 1) F = 0 :=
    aeval_planeCurvePolynomialInSecondCoordinate_ratFunc_eq_zero
      hf hpartialSecond
  have heq := minpoly.eq_of_irreducible hFirreducible hFroot
  have hprimitive := adjoin_secondCoordinate_over_firstRatFunc_eq_top
    hf hpartialSecond
  have hminNe :
      (minpoly (RatFunc K) (planeCurveFunction f 1)).discr ≠ 0 :=
    minpoly_discr_ne_zero_of_adjoin_eq_top
      (planeCurveFunction f 1) hprimitive
  have hinvNe : F.leadingCoeff⁻¹ ≠ 0 :=
    inv_ne_zero (leadingCoeff_ne_zero.mpr hFirreducible.ne_zero)
  have hscaledNe : (Polynomial.C F.leadingCoeff⁻¹ * F).discr ≠ 0 := by
    simpa only [mul_comm] using (heq ▸ hminNe)
  rw [discr_C_mul F F.leadingCoeff⁻¹ hinvNe] at hscaledNe
  have hFdiscrNe : F.discr ≠ 0 := by
    intro hzero
    exact hscaledNe (by rw [hzero, mul_zero])
  have hmap := discr_map_of_injective
    (algebraMap K[X] (RatFunc K))
    (IsFractionRing.injective K[X] (RatFunc K))
    (planeCurvePolynomialInSecondCoordinate f)
  intro hzero
  apply hFdiscrNe
  rw [show F.discr = algebraMap K[X] (RatFunc K)
      (planeCurvePolynomialInSecondCoordinate f).discr by
    exact hmap]
  rw [hzero, map_zero]

section FiniteDifferentBelow

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) finiteDifferentBoundPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance finiteDifferentBoundPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  ⟨fun r s x => by
    simp only [Algebra.smul_def]
    rw [map_mul]
    change (algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) *
      algebraMap (RatFunc K) L s) * x =
      algebraMap K[X] L r * (algebraMap (RatFunc K) L s * x)
    rw [show algebraMap K[X] L r =
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) by rfl]
    ring⟩

local instance finiteDifferentBoundFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance finiteDifferentBoundFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance finiteDifferentBoundPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance finiteDifferentBoundFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

/-- The finite different, weighted by residue degree but not yet by the
degree of the base prime. -/
def finiteExtensionFiniteDifferentResidueWeightedDivisor
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥) :
    FiniteExtensionFinitePlace K L →₀ ℕ :=
  (differentMultiplicityDivisor K[X]
      (RatFuncFiniteIntegralClosure K L) hDifferent).sum (fun q e =>
    Finsupp.single q (e * q.asIdeal.inertiaDeg K[X]))

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
@[simp] theorem finiteExtensionFiniteDifferentResidueWeightedDivisor_apply
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥)
    (q : FiniteExtensionFinitePlace K L) :
    finiteExtensionFiniteDifferentResidueWeightedDivisor K L hDifferent q =
      multiplicity q.asIdeal
        (differentIdeal K[X] (RatFuncFiniteIntegralClosure K L)) *
          q.asIdeal.inertiaDeg K[X] := by
  classical
  let D := differentMultiplicityDivisor K[X]
    (RatFuncFiniteIntegralClosure K L) hDifferent
  rw [finiteExtensionFiniteDifferentResidueWeightedDivisor, Finsupp.sum_apply]
  unfold Finsupp.sum
  by_cases hq : q ∈ D.support
  · rw [Finset.sum_eq_single q]
    · simp [differentMultiplicityDivisor_apply]
    · intro b hb hbq
      simp [hbq]
    · exact fun hnot => (hnot hq).elim
  · rw [Finset.sum_eq_zero]
    · change 0 = multiplicity q.asIdeal
          (differentIdeal K[X] (RatFuncFiniteIntegralClosure K L)) *
            q.asIdeal.inertiaDeg K[X]
      have hzero : D q = 0 := Finsupp.notMem_support_iff.mp hq
      simpa [D, differentMultiplicityDivisor_apply] using
        congrArg (fun n => n * q.asIdeal.inertiaDeg K[X]) hzero.symm
    · intro b hb
      have hbq : b ≠ q := by
        intro h
        subst h
        exact hq hb
      simp [hbq]

/-- Push the residue-weighted finite different down to the finite primes of
`K[X]`. -/
def finiteExtensionFiniteDifferentDivisorBelow
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥) :
    HeightOneSpectrum K[X] →₀ ℕ :=
  (finiteExtensionFiniteDifferentResidueWeightedDivisor K L hDifferent).mapDomain
    (HeightOneSpectrum.under K[X])

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
theorem finiteExtensionFiniteDifferentDivisorBelow_apply
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥)
    (p : HeightOneSpectrum K[X]) :
    finiteExtensionFiniteDifferentDivisorBelow K L hDifferent p =
      ∑ P : p.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L),
        P.1.inertiaDeg K[X] *
          multiplicity P.1
            (differentIdeal K[X] (RatFuncFiniteIntegralClosure K L)) := by
  classical
  let e := finitePlaceFiberEquivPrimesOver K L p
  let : Fintype {q : FiniteExtensionFinitePlace K L //
      HeightOneSpectrum.under K[X] q = p} :=
    Fintype.ofEquiv (p.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L)) e.symm
  let P₀ : p.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L) :=
    Classical.choice (Set.nonempty_coe_sort.mpr
      (Set.nonempty_iff_ne_empty.mpr (by
        intro hempty
        have hncard := IsDedekindDomain.primesOver_ncard_ne_zero p.asIdeal
          (RatFuncFiniteIntegralClosure K L)
        exact hncard (by simp [hempty]))))
  let q₀ : FiniteExtensionFinitePlace K L := primeOverHeightOne p P₀
  have hq₀ : HeightOneSpectrum.under K[X] q₀ = p := by
    apply HeightOneSpectrum.ext
    exact (Ideal.over_def P₀.1 p.asIdeal).symm
  rw [finiteExtensionFiniteDifferentDivisorBelow, show p =
    HeightOneSpectrum.under K[X] q₀ from hq₀.symm,
    Finsupp.mapDomain_apply_eq_sum]
  let D := finiteExtensionFiniteDifferentResidueWeightedDivisor K L hDifferent
  have hfilter :
      (∑ q ∈ D.support with HeightOneSpectrum.under K[X] q =
          HeightOneSpectrum.under K[X] q₀, D q) =
        ∑ q : {q : FiniteExtensionFinitePlace K L //
          HeightOneSpectrum.under K[X] q = p}, D q := by
    rw [hq₀]
    calc
      _ = ∑ q ∈ Finset.subtype
            (fun q => HeightOneSpectrum.under K[X] q = p) D.support,
            D q := (Finset.sum_subtype_eq_sum_filter (s := D.support)
              (fun q => D q)).symm
      _ = ∑ q : {q : FiniteExtensionFinitePlace K L //
          HeightOneSpectrum.under K[X] q = p}, D q := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro q _ hq
        have hnot : q.1 ∉ D.support := by
          intro hmem
          exact hq (Finset.mem_subtype.mpr hmem)
        exact Finsupp.notMem_support_iff.mp hnot
  rw [hfilter, hq₀]
  apply Fintype.sum_equiv e
  intro q
  rw [finiteExtensionFiniteDifferentResidueWeightedDivisor_apply]
  change multiplicity q.1.asIdeal
      (differentIdeal K[X] (RatFuncFiniteIntegralClosure K L)) *
        q.1.asIdeal.inertiaDeg K[X] =
    q.1.asIdeal.inertiaDeg K[X] *
      multiplicity q.1.asIdeal
        (differentIdeal K[X] (RatFuncFiniteIntegralClosure K L))
  ring

omit [DecidableEq (RatFunc K)] in
/-- Pushing the residue-weighted different down to the base does not change
its degree-weighted sum. -/
theorem finiteExtensionFiniteDifferentDegree_eq_belowWeightedDegree
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥) :
    finiteExtensionFiniteDifferentDegree K L hDifferent =
      (finiteExtensionFiniteDifferentDivisorBelow K L hDifferent).sum
        (fun p e => e * ratFuncFinitePlaceDegree p) := by
  classical
  let D := differentMultiplicityDivisor K[X]
    (RatFuncFiniteIntegralClosure K L) hDifferent
  let DW := finiteExtensionFiniteDifferentResidueWeightedDivisor
    K L hDifferent
  let DB := finiteExtensionFiniteDifferentDivisorBelow K L hDifferent
  calc
    finiteExtensionFiniteDifferentDegree K L hDifferent =
        DW.sum (fun q e => e *
          ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q)) := by
      rw [finiteExtensionFiniteDifferentDegree]
      change D.sum _ = DW.sum _
      dsimp only [DW]
      rw [finiteExtensionFiniteDifferentResidueWeightedDivisor,
        Finsupp.sum_sum_index (fun _ => by simp)
          (fun _ _ _ => by ring)]
      apply Finsupp.sum_congr
      intro q _
      rw [Finsupp.sum_single_index]
      · ring
    _ = DB.sum (fun p e => e * ratFuncFinitePlaceDegree p) := by
      dsimp only [DB, DW]
      rw [finiteExtensionFiniteDifferentDivisorBelow]
      symm
      apply Finsupp.sum_mapDomain_index
      · intro
        simp
      · intro _ _ _
        ring

omit [DecidableEq (RatFunc K)] in
/-- A coefficientwise finite-place discriminant bound sums to the corresponding
degree bound. -/
theorem finiteExtensionFiniteDifferentDegree_le_polynomialDegree_of_localBounds
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥)
    (Δ : K[X]) (hΔ : Δ ≠ 0)
    (hlocal : ∀ p : HeightOneSpectrum K[X],
      (finiteExtensionFiniteDifferentDivisorBelow K L hDifferent p : ℤ) ≤
        ratFuncFiniteOrder p (algebraMap K[X] (RatFunc K) Δ)) :
    finiteExtensionFiniteDifferentDegree K L hDifferent ≤ Δ.natDegree := by
  classical
  let DB := finiteExtensionFiniteDifferentDivisorBelow K L hDifferent
  let DBZ : HeightOneSpectrum K[X] →₀ ℤ :=
    DB.mapRange (fun n : ℕ => (n : ℤ)) (by simp)
  let P := ratFuncFiniteDivisor (algebraMap K[X] (RatFunc K) Δ)
  have hpoint : DBZ ≤ P := by
    intro p
    dsimp only [DBZ, P]
    rw [Finsupp.mapRange_apply, ratFuncFiniteDivisor_apply]
    exact hlocal p
  have hsum :
      DBZ.sum (fun p e => e * (ratFuncFinitePlaceDegree p : ℤ)) ≤
        P.sum (fun p e => e * (ratFuncFinitePlaceDegree p : ℤ)) := by
    apply Finsupp.sum_le_sum_index hpoint
    · intro p _ a b hab
      exact mul_le_mul_of_nonneg_right hab (Int.natCast_nonneg _)
    · intro p _
      simp
  have hcast : (finiteExtensionFiniteDifferentDegree K L hDifferent : ℤ) ≤
      (Δ.natDegree : ℤ) := by
    calc
      (finiteExtensionFiniteDifferentDegree K L hDifferent : ℤ) =
          DBZ.sum (fun p e => e *
            (ratFuncFinitePlaceDegree p : ℤ)) := by
        rw [finiteExtensionFiniteDifferentDegree_eq_belowWeightedDegree]
        rw [Nat.cast_finsupp_sum]
        dsimp only [DBZ, DB]
        rw [Finsupp.sum_mapRange_index (fun _ => by simp)]
        apply Finsupp.sum_congr
        intro p _
        push_cast
        rfl
      _ ≤ P.sum (fun p e => e *
            (ratFuncFinitePlaceDegree p : ℤ)) := hsum
      _ = ratFuncExhaustiveFinitePlaceDegreeSum
          (algebraMap K[X] (RatFunc K) Δ) := by rfl
      _ = (algebraMap K[X] (RatFunc K) Δ).intDegree :=
        ratFuncExhaustiveFinitePlaceDegreeSum_eq_intDegree _
          (RatFunc.algebraMap_ne_zero hΔ)
      _ = (Δ.natDegree : ℤ) := RatFunc.intDegree_polynomial
  exact_mod_cast hcast

theorem finiteExtensionFiniteDifferentDivisorBelow_apply_le_minpolyDiscr_of_localPrimitive
    (hDifferent : differentIdeal K[X]
      (RatFuncFiniteIntegralClosure K L) ≠ ⊥)
    (p : HeightOneSpectrum K[X])
    [Algebra (Localization.AtPrime p.asIdeal) L]
    [IsScalarTower K[X] (Localization.AtPrime p.asIdeal) L]
    (z : L) (hzIntegral : IsIntegral (Localization.AtPrime p.asIdeal) z)
    (hzPrimitive : Algebra.adjoin (RatFunc K) {z} = ⊤) :
    (finiteExtensionFiniteDifferentDivisorBelow K L hDifferent p : ℤ) ≤
      ratFuncFiniteOrder p (minpoly (RatFunc K) z).discr := by
  let A := Localization.AtPrime p.asIdeal
  let B := RatFuncFiniteIntegralClosure K L
  obtain ⟨m, hmIntegral⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization
      p.asIdeal.primeCompl z hzIntegral
  have hm_ne : (m : K[X]) ≠ 0 := by
    intro hm
    exact m.property (hm ▸ p.asIdeal.zero_mem)
  let r : RatFunc K := algebraMap K[X] (RatFunc K) (m : K[X])
  have hr : r ≠ 0 := RatFunc.algebraMap_ne_zero hm_ne
  let x : B := IsIntegralClosure.mk' B ((m : K[X]) • z) hmIntegral
  have hxMap : algebraMap B L x = (m : K[X]) • z := by
    simp [x]
  have hxScale : algebraMap B L x = r • z := by
    rw [hxMap]
    simp only [Algebra.smul_def, r]
    rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) L]
  have hxPrimitive : Algebra.adjoin (RatFunc K)
      {algebraMap B L x} = ⊤ := by
    rw [hxScale]
    exact adjoin_smul_eq_top_of_adjoin_eq_top r hr z hzPrimitive
  let d : B := aeval x (derivative (minpoly K[X] x))
  have hd : d ≠ 0 := by
    simpa [d] using minpolyDerivative_ne_zero
      (A := K[X]) (K := RatFunc K) (L := L) x
  let dL : L := algebraMap B L d
  have hdL : dL ≠ 0 := (IsFractionRing.injective B L).ne hd
  have hrepr :
      (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm dL =
        algebraMap B (FractionRing B) d := by
    apply (ratFuncFiniteIntegralClosureFractionRingEquiv K L).injective
    rw [(ratFuncFiniteIntegralClosureFractionRingEquiv K L).apply_symm_apply]
    exact (ratFuncFiniteIntegralClosureFractionRingEquiv K L).commutes d |>.symm
  have hpoint : ∀ P : p.asIdeal.primesOver B,
      ((P.1.inertiaDeg K[X] *
        multiplicity P.1 (differentIdeal K[X] B) : ℕ) : ℤ) ≤
        (P.1.inertiaDeg K[X] : ℤ) *
          finitePlaceOrder (primeOverHeightOne p P)
            ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm dL) := by
    intro P
    have hmul := differentIdeal_multiplicity_le_minpolyDerivativeSpan
      (A := K[X]) (K := RatFunc K) (L := L) (B := B)
      x hxPrimitive (primeOverHeightOne p P)
    have horder :
        finitePlaceOrder (primeOverHeightOne p P)
            ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm dL) =
          (multiplicity P.1 (Ideal.span {d}) : ℤ) := by
      rw [hrepr]
      simpa using finitePlaceOrder_algebraMap_eq_multiplicity
        (primeOverHeightOne p P) d hd
    rw [horder]
    exact_mod_cast Nat.mul_le_mul_left (P.1.inertiaDeg K[X]) hmul
  have hsum :
      (finiteExtensionFiniteDifferentDivisorBelow K L hDifferent p : ℤ) ≤
        ∑ P : p.asIdeal.primesOver B,
          (P.1.inertiaDeg K[X] : ℤ) *
            finitePlaceOrder (primeOverHeightOne p P)
              ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm dL) := by
    rw [finiteExtensionFiniteDifferentDivisorBelow_apply, Nat.cast_sum]
    exact Finset.sum_le_sum fun P _ => hpoint P
  rw [finitePrimesAbove_weightedOrder_eq_normOrder K L p dL hdL] at hsum
  let pb : PowerBasis (RatFunc K) L :=
    PowerBasis.ofAdjoinEqTop'
      (Algebra.IsIntegral.isIntegral (algebraMap B L x)) hxPrimitive
  have hdiscNorm := discr_powerBasisOfPrimitiveElement_eq_norm_minpolyDerivative
    (A := K[X]) (K := RatFunc K) (L := L) (B := B) x hxPrimitive
  have hpb : Algebra.discr (RatFunc K) pb.basis =
      (minpoly (RatFunc K) (algebraMap B L x)).discr := by
    have hpbg : pb.gen = algebraMap B L x := by simp [pb]
    simpa only [hpbg] using discr_powerBasis_eq_minpoly_discr pb
  change Algebra.discr (RatFunc K) pb.basis =
      (-1) ^ (Module.finrank (RatFunc K) L *
        (Module.finrank (RatFunc K) L - 1) / 2) *
          Algebra.norm (RatFunc K) dL at hdiscNorm
  rw [hpb] at hdiscNorm
  have hnormNe : Algebra.norm (RatFunc K) dL ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hdL
  have hsignNe :
      ((-1 : RatFunc K) ^ (Module.finrank (RatFunc K) L *
        (Module.finrank (RatFunc K) L - 1) / 2)) ≠ 0 := by simp
  have hminXNe :
      (minpoly (RatFunc K) (algebraMap B L x)).discr ≠ 0 := by
    rw [hdiscNorm]
    exact mul_ne_zero hsignNe hnormNe
  have hnormOrder :
      ratFuncFiniteOrder p (Algebra.norm (RatFunc K) dL) =
        ratFuncFiniteOrder p
          (minpoly (RatFunc K) (algebraMap B L x)).discr := by
    have horder := congrArg (finitePlaceOrder p) hdiscNorm
    rw [finitePlaceOrder_mul_of_ne_zero p _ _ hsignNe hnormNe] at horder
    have hsignOrder : finitePlaceOrder p
        ((-1 : RatFunc K) ^ (Module.finrank (RatFunc K) L *
          (Module.finrank (RatFunc K) L - 1) / 2)) = 0 := by
      rw [finitePlaceOrder_pow_of_ne_zero p (-1 : RatFunc K) (by simp)]
      have hminus := finitePlaceOrder_algebraMap_unit_eq_zero
        (R := K[X]) (F := RatFunc K) p (-1 : K[X]ˣ)
      have hminus' : finitePlaceOrder p (-1 : RatFunc K) = 0 := by
        simpa using hminus
      rw [hminus', smul_zero]
    rw [hsignOrder, zero_add] at horder
    exact horder.symm
  have hmMultiplicity :
      multiplicity p.asIdeal (Ideal.span {(m : K[X])}) = 0 := by
    apply multiplicity_eq_zero_of_not_dvd
    rw [Ideal.dvd_span_singleton]
    exact m.property
  have hrOrder : ratFuncFiniteOrder p r = 0 := by
    change finitePlaceOrder p (algebraMap K[X] (RatFunc K) (m : K[X])) = 0
    rw [finitePlaceOrder_algebraMap_eq_multiplicity p (m : K[X]) hm_ne]
    exact_mod_cast hmMultiplicity
  obtain ⟨N, hscaleDisc⟩ :=
    exists_minpoly_discr_smul_eq_pow_mul r hr z hzPrimitive
  rw [← hxScale] at hscaleDisc
  have hminZNe : (minpoly (RatFunc K) z).discr ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hscaleDisc
    exact hminXNe hscaleDisc
  have hscaleOrder :
      ratFuncFiniteOrder p
          (minpoly (RatFunc K) (algebraMap B L x)).discr =
        ratFuncFiniteOrder p (minpoly (RatFunc K) z).discr := by
    have horder := congrArg (finitePlaceOrder p) hscaleDisc
    rw [finitePlaceOrder_mul_of_ne_zero p _ _
      (pow_ne_zero N hr) hminZNe,
      finitePlaceOrder_pow_of_ne_zero p r hr N] at horder
    have hrOrder' : finitePlaceOrder p r = 0 := hrOrder
    rw [hrOrder', smul_zero, zero_add] at horder
    exact horder
  exact hsum.trans_eq (hnormOrder.trans hscaleOrder)

end FiniteDifferentBelow

section PlaneCurveFiniteDifferentBound

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

/-- At each finite first-coordinate prime, the residue-weighted different is
bounded by the order of the discriminant of the original plane equation. -/
theorem planeCurve_finiteDifferentDivisorBelow_apply_le_discrOrder
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K)
    (p : HeightOneSpectrum K[X]) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    (finiteExtensionFiniteDifferentDivisorBelow K
        (PlaneCurveFunctionField f)
        (finiteExtensionFiniteDifferentIdeal_ne_bot K
          (PlaneCurveFunctionField f)) p : ℤ) ≤
      ratFuncFiniteOrder p (algebraMap K[X] (RatFunc K)
        (planeCurvePolynomialInSecondCoordinate f).discr) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let algRL : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (RatFunc K) L := algRL
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let A := Localization.AtPrime p.asIdeal
  let ι := localizationAtPrimeToRatFunc p
  obtain ⟨a, u, hu, hroot, hvc, hprimitive, hdegree⟩ :=
    planeCurve_local_reciprocal_certificate_of_degreeOf_second_lt_fintypeCard
      hf hpartialSecond hcardK p
  let c : A := algebraMap K[X] A a
  let G : A[X] := (planeCurvePolynomialInSecondCoordinate f).map
    (algebraMap K[X] A)
  let algRA : Algebra K[X] A := inferInstance
  let algRR : Algebra K[X] (RatFunc K) := inferInstance
  let algAR : Algebra A (RatFunc K) := ι.toAlgebra
  let algPL : Algebra K[X] L := RingHom.toAlgebra
    ((algebraMap (RatFunc K) L).comp (algebraMap K[X] (RatFunc K)))
  let : Algebra K[X] A := algRA
  let : Algebra K[X] (RatFunc K) := algRR
  let : Algebra A (RatFunc K) := algAR
  let : Algebra K[X] L := algPL
  let : SMul K[X] A := algRA.toSMul
  let : SMul K[X] (RatFunc K) := algRR.toSMul
  let : SMul A (RatFunc K) := algAR.toSMul
  let : SMul K[X] L := algPL.toSMul
  let : IsScalarTower K[X] A (RatFunc K) := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (localizationAtPrimeToRatFunc_comp_algebraMap p).symm
  let : IsFractionRing A (RatFunc K) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      p.asIdeal.primeCompl A (RatFunc K)
  let algAL : Algebra A L :=
    ((algebraMap (RatFunc K) L).comp ι).toAlgebra
  let : SMul (RatFunc K) L := algRL.toSMul
  let : Algebra A L := algAL
  let : SMul A L := algAL.toSMul
  let : IsScalarTower A (RatFunc K) L := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  let : IsScalarTower K[X] A L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply DFunLike.ext _ _
    intro r
    change algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) =
      algebraMap (RatFunc K) L (ι (algebraMap K[X] A r))
    exact (congrArg (algebraMap (RatFunc K) L)
      (DFunLike.congr_fun
        (localizationAtPrimeToRatFunc_comp_algebraMap p) r)).symm
  let : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      K[X] p.ne_bot A
  let v : L := planeCurveFunction f 1
  let z : L := (v - algebraMap A L c)⁻¹
  have hroot' : Polynomial.aeval v G = 0 := by
    simpa [Polynomial.aeval_def, algAL, RingHom.algebraMap_toAlgebra,
      G, v] using hroot
  have hvc' : v ≠ algebraMap A L c := by
    simpa [algAL, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      c, v] using hvc
  have hzIntegral : IsIntegral A z := by
    exact isIntegral_inv_sub_of_eval_eq_unit
      G c u v hu hvc' hroot'
  have hzPrimitive : Algebra.adjoin (RatFunc K) {z} = ⊤ := by
    change Algebra.adjoin (RatFunc K)
      {(v - algebraMap A L c)⁻¹} = ⊤
    have hmap : algebraMap A L c =
        algebraMap (RatFunc K) L (ι c) := by rfl
    rw [hmap]
    exact adjoin_inv_sub_eq_top_of_adjoin_eq_top (ι c) v hprimitive
  have hbound :=
    finiteExtensionFiniteDifferentDivisorBelow_apply_le_minpolyDiscr_of_localPrimitive
      K L (finiteExtensionFiniteDifferentIdeal_ne_bot K L) p
        z hzIntegral hzPrimitive
  have htop := finitePlaceOrderTop_minpoly_inv_sub_discr
    (A := A) (K := RatFunc K) (L := L)
    (IsDiscreteValuationRing.maximalIdeal A)
      G c u v hu hvc' hroot' hprimitive hdegree
  change finitePlaceOrderTop (IsDiscreteValuationRing.maximalIdeal A)
      (minpoly (RatFunc K) z).discr =
    finitePlaceOrderTop (IsDiscreteValuationRing.maximalIdeal A)
      (algebraMap A (RatFunc K) G.discr) at htop
  rw [localizationAtPrime_finitePlaceOrderTop_eq p,
    localizationAtPrime_finitePlaceOrderTop_eq p] at htop
  have hminNe : (minpoly (RatFunc K) z).discr ≠ 0 :=
    minpoly_discr_ne_zero_of_adjoin_eq_top z hzPrimitive
  have hFdiscr : (planeCurvePolynomialInSecondCoordinate f).discr ≠ 0 :=
    planeCurvePolynomialInSecondCoordinate_discr_ne_zero
      hf hpartialSecond
  have hGdiscEq : G.discr = algebraMap K[X] A
      (planeCurvePolynomialInSecondCoordinate f).discr := by
    exact discr_map_of_injective (algebraMap K[X] A)
      (IsLocalization.injective A
        p.asIdeal.primeCompl_le_nonZeroDivisors)
      (planeCurvePolynomialInSecondCoordinate f)
  have hGdiscr : G.discr ≠ 0 := by
    rw [hGdiscEq]
    simpa only [map_zero] using (IsLocalization.injective A
      p.asIdeal.primeCompl_le_nonZeroDivisors).ne hFdiscr
  have hmapGdiscr : algebraMap A (RatFunc K) G.discr ≠ 0 :=
    by simpa only [map_zero] using
      (IsFractionRing.injective A (RatFunc K)).ne hGdiscr
  rw [finitePlaceOrderTop_eq_coe p _ hminNe,
    finitePlaceOrderTop_eq_coe p _ hmapGdiscr] at htop
  have hmapEq : algebraMap A (RatFunc K) G.discr =
      algebraMap K[X] (RatFunc K)
        (planeCurvePolynomialInSecondCoordinate f).discr := by
    rw [hGdiscEq]
    exact (IsScalarTower.algebraMap_apply K[X] A (RatFunc K) _).symm
  have horderEq : ratFuncFiniteOrder p (minpoly (RatFunc K) z).discr =
      ratFuncFiniteOrder p (algebraMap K[X] (RatFunc K)
        (planeCurvePolynomialInSecondCoordinate f).discr) := by
    change finitePlaceOrder p (minpoly (RatFunc K) z).discr =
      finitePlaceOrder p (algebraMap K[X] (RatFunc K)
        (planeCurvePolynomialInSecondCoordinate f).discr)
    rw [← hmapEq]
    exact_mod_cast htop
  exact hbound.trans_eq horderEq

/-- The sharp finite different contribution for the plane function field is
bounded by the discriminant degree of the original second-coordinate
equation. -/
theorem planeCurve_finiteDifferentDegree_le_discrNatDegree
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    finiteExtensionFiniteDifferentDegree K (PlaneCurveFunctionField f)
        (finiteExtensionFiniteDifferentIdeal_ne_bot K
          (PlaneCurveFunctionField f)) ≤
      (planeCurvePolynomialInSecondCoordinate f).discr.natDegree := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  apply finiteExtensionFiniteDifferentDegree_le_polynomialDegree_of_localBounds
    K (PlaneCurveFunctionField f)
      (finiteExtensionFiniteDifferentIdeal_ne_bot K
        (PlaneCurveFunctionField f))
      (planeCurvePolynomialInSecondCoordinate f).discr
      (planeCurvePolynomialInSecondCoordinate_discr_ne_zero
        hf hpartialSecond)
  intro p
  exact planeCurve_finiteDifferentDivisorBelow_apply_le_discrOrder
    hf hpartialSecond hcardK p

end PlaneCurveFiniteDifferentBound

end

end BGS.CorvajaZannier
