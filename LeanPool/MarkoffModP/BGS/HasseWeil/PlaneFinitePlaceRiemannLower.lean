/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FinitePlaceApproximation
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionLocalPoleQuotient
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneInfinityRiemannLower
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionPrincipalParts
import Mathlib.Tactic

/-!
# Riemann's inequality at finite plane-curve places

Weak approximation lifts a basis of the principal parts at one finite place
to global functions regular at every other finite place.  A common effective
divisor above infinity absorbs the remaining poles.  The resulting
principal-part map is surjective, so rank-nullity contributes exactly
`N * degree(q)` new dimensions over the infinity-supported Riemann space.

The infinity-supported bidegree Riemann inequality and the effective-divisor
increment upper bound then cancel the auxiliary infinity divisor.  This gives
Riemann's inequality for `L(N q)` at every finite exhaustive place.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open IsDedekindDomain
open scoped nonZeroDivisors Polynomial BigOperators

noncomputable section


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance finiteRiemannConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance finiteRiemannConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10) finiteRiemannPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance finiteRiemannPolynomialTower : IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance finiteRiemannClosureIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance finiteRiemannClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance finiteRiemannPolynomialTorsionFree :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance finiteRiemannClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance finiteRiemannClosureDedekind :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) L
    (RatFuncFiniteIntegralClosure K L)

local instance finiteRiemannClosureFractionRing :
    IsFractionRing (RatFuncFiniteIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    K[X] (RatFunc K) L (RatFuncFiniteIntegralClosure K L)

theorem mem_finiteExtensionLocalPoleSpace_zero_of_valuation_le_one
    (q : FiniteExtensionFinitePlace K L) (x : L)
    (hx : q.valuation L x ≤ 1) :
    x ∈ finiteExtensionLocalPoleSpace K L (.inl q) 0 := by
  rw [mem_finiteExtensionLocalPoleSpace_iff]
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · refine Or.inr ⟨hx0, ?_⟩
    rw [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder]
    rw [valuation_eq_exp_neg_finitePlaceOrder q x hx0, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at hx
    omega

theorem exists_global_finitePrincipalPart_representative
    (q : FiniteExtensionFinitePlace K L) (N : ℕ)
    (p : finiteExtensionLocalPoleSpace K L (.inl q) N ⧸
      relativeSubmodule
        (finiteExtensionLocalPoleSpace K L (.inl q) 0)
        (finiteExtensionLocalPoleSpace K L (.inl q) N)) :
    ∃ z : finiteExtensionLocalPoleSpace K L (.inl q) N,
      Submodule.Quotient.mk z = p ∧
      ∀ q' : FiniteExtensionFinitePlace K L, q' ≠ q →
        (z : L) ∈ finiteExtensionLocalPoleSpace K L (.inl q') 0 := by
  classical
  obtain ⟨x, hxmk⟩ :=
    (Submodule.Quotient.mk_surjective
      (relativeSubmodule
        (finiteExtensionLocalPoleSpace K L (.inl q) 0)
        (finiteExtensionLocalPoleSpace K L (.inl q) N))) p
  let selected : Finset (Ideal (RatFuncFiniteIntegralClosure K L)) :=
    {q.asIdeal}
  let target : Ideal (RatFuncFiniteIntegralClosure K L) → L := fun Q =>
    if Q = q.asIdeal then (x : L) else 0
  obtain ⟨z, happrox, hregular⟩ :=
    exists_fraction_approximating_at_finitePlaces_regular_elsewhere
      selected (by
        intro P hP
        simp only [selected, Finset.mem_singleton] at hP
        subst P
        exact (Ideal.prime_iff_isPrime q.ne_bot).mpr q.isPrime) target
      (fun _ => 0)
  have hzsub : z - (x : L) ∈
      finiteExtensionLocalPoleSpace K L (.inl q) 0 := by
    apply mem_finiteExtensionLocalPoleSpace_zero_of_valuation_le_one K L
    have h := happrox q (by simp [selected])
    simpa only [target, ite_eq_left rfl, CharP.cast_eq_zero, neg_zero,
      WithZero.exp_zero] using h
  have hzMem : z ∈ finiteExtensionLocalPoleSpace K L (.inl q) N := by
    have hxMem : (x : L) ∈ finiteExtensionLocalPoleSpace K L (.inl q) N := x.2
    have hzeroLe := finiteExtensionLocalPoleSpace_mono K L (.inl q)
      (Nat.zero_le N)
    have hsubMem := hzeroLe hzsub
    have hadd := (finiteExtensionLocalPoleSpace K L (.inl q) N).add_mem
      hxMem hsubMem
    rw [show (x : L) + (z - (x : L)) = z by abel] at hadd
    exact hadd
  refine ⟨⟨z, hzMem⟩, ?_, ?_⟩
  · rw [← hxmk]
    rw [Submodule.Quotient.eq]
    change z - (x : L) ∈
      finiteExtensionLocalPoleSpace K L (.inl q) 0
    exact hzsub
  · intro q' hq'
    apply mem_finiteExtensionLocalPoleSpace_zero_of_valuation_le_one K L
    apply hregular q'
    simp only [selected, Finset.mem_singleton]
    intro hideal
    apply hq'
    exact HeightOneSpectrum.ext hideal

/-- The part of an exhaustive divisor supported at infinity. -/
def finiteExtensionDivisorInfinityPart
    (D : FiniteExtensionDivisor K L) : FiniteExtensionDivisor K L := by
  classical
  exact Finsupp.filter (fun v => match v with
    | .inl _ => False
    | .inr _ => True) D

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem finiteExtensionDivisorInfinityPart_inl
    (D : FiniteExtensionDivisor K L)
    (q : FiniteExtensionFinitePlace K L) :
    finiteExtensionDivisorInfinityPart K L D (.inl q) = 0 := by
  simp [finiteExtensionDivisorInfinityPart]

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem finiteExtensionDivisorInfinityPart_inr
    (D : FiniteExtensionDivisor K L)
    (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionDivisorInfinityPart K L D (.inr P) = D (.inr P) := by
  simp [finiteExtensionDivisorInfinityPart]

theorem exists_infinityDivisor_finitePlacePrincipalParts_rank
    (q : FiniteExtensionFinitePlace K L) (N : ℕ) (hN : 0 < N) :
    ∃ E : FiniteExtensionDivisor K L,
      (∀ v, 0 ≤ E v) ∧
      (∀ q' : FiniteExtensionFinitePlace K L, E (.inl q') = 0) ∧
      Module.finrank K (finiteExtensionRiemannSpace K L E) +
          N * finiteExtensionPlaceDegree K L (.inl q) ≤
        Module.finrank K (finiteExtensionRiemannSpace K L
          (Finsupp.single (.inl q) (N : ℤ) + E)) := by
  classical
  let A := finiteExtensionLocalPoleSpace K L (.inl q) N
  let A0 := finiteExtensionLocalPoleSpace K L (.inl q) 0
  let PP := A ⧸ relativeSubmodule A0 A
  have hPPfinrank : Module.finrank K PP =
      N * finiteExtensionPlaceDegree K L (.inl q) := by
    simpa only [A, A0, PP] using
      finiteExtensionLocalPoleSpace_inl_cumulative_finrank K L q N
  let : Module.Finite K PP := by
    apply Module.finite_of_finrank_pos
    rw [hPPfinrank]
    exact Nat.mul_pos hN (finiteExtensionPlaceDegree_pos K L (.inl q))
  let b := Module.finBasis K PP
  have hzExists (i : Fin (Module.finrank K PP)) :=
    exists_global_finitePrincipalPart_representative K L q N (b i)
  let z : Fin (Module.finrank K PP) → A := fun i =>
    Classical.choose (hzExists i)
  have hzmk (i : Fin (Module.finrank K PP)) :
      Submodule.Quotient.mk (z i) = b i :=
    (Classical.choose_spec (hzExists i)).1
  have hzregular (i : Fin (Module.finrank K PP))
      (q' : FiniteExtensionFinitePlace K L) (hq' : q' ≠ q) :
      (z i : L) ∈ finiteExtensionLocalPoleSpace K L (.inl q') 0 :=
    (Classical.choose_spec (hzExists i)).2 q' hq'
  have hzNe (i : Fin (Module.finrank K PP)) : (z i : L) ≠ 0 := by
    intro hzero
    have hzSubtype : z i = 0 := Subtype.ext hzero
    have hmk := hzmk i
    rw [hzSubtype] at hmk
    exact b.linearIndependent.ne_zero i (by simpa using hmk.symm)
  let H : FiniteExtensionDivisor K L :=
    ∑ i, finiteExtensionPoleDivisor K L (z i : L)
  have hH : (0 : FiniteExtensionDivisor K L) ≤ H := by
    dsimp only [H]
    apply Finset.sum_nonneg
    intro i _ v
    exact finiteExtensionPoleDivisor_effective K L (z i : L) v
  have hPoleLeH (i : Fin (Module.finrank K PP)) :
      finiteExtensionPoleDivisor K L (z i : L) ≤ H := by
    dsimp only [H]
    calc
      finiteExtensionPoleDivisor K L (z i : L) ≤
          finiteExtensionPoleDivisor K L (z i : L) +
            ∑ j ∈ Finset.univ.erase i,
              finiteExtensionPoleDivisor K L (z j : L) :=
        le_add_of_nonneg_right (Finset.sum_nonneg fun j _ v =>
          finiteExtensionPoleDivisor_effective K L (z j : L) v)
      _ = ∑ j, finiteExtensionPoleDivisor K L (z j : L) := by
        rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  let E : FiniteExtensionDivisor K L :=
    finiteExtensionDivisorInfinityPart K L H
  have hE : ∀ v, 0 ≤ E v := by
    intro v
    rcases v with q' | P
    · simp [E]
    · simp only [E, finiteExtensionDivisorInfinityPart_inr, H]
      exact hH (.inr P)
  have hEfinite : ∀ q' : FiniteExtensionFinitePlace K L,
      E (.inl q') = 0 := by
    intro q'
    simp [E]
  let D : FiniteExtensionDivisor K L :=
    Finsupp.single (.inl q) (N : ℤ) + E
  have hD : ∀ v, 0 ≤ D v := by
    intro v
    exact add_nonneg (by
      by_cases hv : v = (.inl q : FiniteExtensionPlace K L)
      · subst v
        simp
      · simp [Finsupp.single_eq_of_ne hv]) (hE v)
  have hzPoleLe (i : Fin (Module.finrank K PP)) :
      finiteExtensionPoleDivisor K L (z i : L) ≤ D := by
    intro v
    rcases v with q' | P
    · by_cases hq' : q' = q
      · subst q'
        have hzOrder : -(N : ℤ) ≤
            finiteExtensionPrincipalDivisor K L (z i : L) (.inl q) := by
          have hzmem := (z i).2
          rw [mem_finiteExtensionLocalPoleSpace_iff] at hzmem
          rcases hzmem with hzero | ⟨_, horder⟩
          · exact (hzNe i hzero).elim
          · exact horder
        rw [finiteExtensionPoleDivisor_apply]
        by_cases hneg :
            finiteExtensionPrincipalDivisor K L (z i : L) (.inl q) < 0
        · rw [ite_eq_left hneg]
          simp only [D, Finsupp.add_apply, Finsupp.single_eq_same,
            hEfinite q, add_zero]
          omega
        · rw [ite_eq_right hneg]
          exact hD (.inl q)
      · have hzreg := hzregular i q' hq'
        rw [mem_finiteExtensionLocalPoleSpace_iff] at hzreg
        have hzOrder : 0 ≤
            finiteExtensionPrincipalDivisor K L (z i : L) (.inl q') := by
          rcases hzreg with hzero | ⟨_, horder⟩
          · exact (hzNe i hzero).elim
          · simpa using horder
        rw [finiteExtensionPoleDivisor_apply, ite_eq_right (not_lt_of_ge hzOrder)]
        exact hD (.inl q')
    · simp only [D, Finsupp.add_apply,
        Finsupp.single_eq_of_ne (by simp :
          (Sum.inr P : FiniteExtensionPlace K L) ≠ Sum.inl q),
        zero_add, E, finiteExtensionDivisorInfinityPart_inr, H]
      exact hPoleLeH i (.inr P)
  have hzD (i : Fin (Module.finrank K PP)) :
      (z i : L) ∈ finiteExtensionRiemannSpace K L D := by
    apply finiteExtensionRiemannSpace_mono K L (hzPoleLe i)
    exact mem_finiteExtensionRiemannSpace_poleDivisor K L
      (z i : L) (hzNe i)
  have hDq : D (.inl q) = N := by
    simp [D, hEfinite]
  have hlocal (x : finiteExtensionRiemannSpace K L D) :
      (x : L) ∈ A := by
    have hx := finiteExtensionRiemannSpace_le_localPoleSpace K L D hD
      (.inl q) x.2
    simpa only [A, hDq, Int.toNat_natCast] using hx
  let toLocal : finiteExtensionRiemannSpace K L D →ₗ[K] A :=
    LinearMap.codRestrict A
      (finiteExtensionRiemannSpace K L D).subtype hlocal
  let φ : finiteExtensionRiemannSpace K L D →ₗ[K] PP :=
    (relativeSubmodule A0 A).mkQ.comp toLocal
  have hφz (i : Fin (Module.finrank K PP)) :
      φ ⟨(z i : L), hzD i⟩ = b i := by
    change Submodule.Quotient.mk (z i) = b i
    exact hzmk i
  have hφsurj : Function.Surjective φ := by
    intro p
    let w : finiteExtensionRiemannSpace K L D :=
      ∑ i, (b.repr p) i • ⟨(z i : L), hzD i⟩
    refine ⟨w, ?_⟩
    simp only [w, map_sum, map_smul, hφz]
    exact b.sum_repr p
  have hED : E ≤ D := by
    intro v
    exact le_add_of_nonneg_left (by
      by_cases hv : v = (.inl q : FiniteExtensionPlace K L)
      · subst v
        simp
      · simp [Finsupp.single_eq_of_ne hv])
  let incl : finiteExtensionRiemannSpace K L E →ₗ[K]
      finiteExtensionRiemannSpace K L D :=
    Submodule.inclusion (finiteExtensionRiemannSpace_mono K L hED)
  have hinclKer (x : finiteExtensionRiemannSpace K L E) : incl x ∈ φ.ker := by
    rw [LinearMap.mem_ker]
    change Submodule.Quotient.mk (toLocal (incl x)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change (x : L) ∈ A0
    have hx := finiteExtensionRiemannSpace_le_localPoleSpace K L E hE
      (.inl q) x.2
    simpa only [A0, hEfinite q, Int.toNat_zero] using hx
  let inclKer : finiteExtensionRiemannSpace K L E →ₗ[K] φ.ker :=
    LinearMap.codRestrict φ.ker incl hinclKer
  have hinclKerInjective : Function.Injective inclKer := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun w : φ.ker => ((w : finiteExtensionRiemannSpace K L D) : L)) hxy
  let : Module.Finite K (finiteExtensionRiemannSpace K L D) :=
    finiteExtensionRiemannSpace_effective_moduleFinite K L D hD
  have hkerLower : Module.finrank K (finiteExtensionRiemannSpace K L E) ≤
      Module.finrank K φ.ker :=
    inclKer.finrank_le_finrank_of_injective hinclKerInjective
  have hrank := φ.finrank_range_add_finrank_ker
  have hrange : Module.finrank K φ.range = Module.finrank K PP := by
    rw [LinearMap.range_eq_top.mpr hφsurj]
    simp
  refine ⟨E, hE, hEfinite, ?_⟩
  change Module.finrank K (finiteExtensionRiemannSpace K L E) +
      N * finiteExtensionPlaceDegree K L (.inl q) ≤
    Module.finrank K (finiteExtensionRiemannSpace K L D)
  rw [← hPPfinrank, ← hrange]
  omega

end

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

variable {K}

/-- Bidegree Riemann inequality at an arbitrary finite exhaustive place of
an irreducible plane curve. -/
theorem planeCurve_finitePlace_riemann_lower
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
    ∀ (q : FiniteExtensionFinitePlace K (PlaneCurveFunctionField f)) (N : ℕ),
      N * finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) (.inl q) + 1 ≤
        Module.finrank K (finiteExtensionOnePointRiemannSpace K
          (PlaneCurveFunctionField f) (.inl q) N) +
            planeCurveBidegreeGenusBudget f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let g := planeCurveBidegreeGenusBudget f
  let : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let constantAlg : Algebra K L :=
    RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
      (algebraMap K (RatFunc K)))
  let : Algebra K L := constantAlg
  let : SMul K L := constantAlg.toSMul
  let : Module K L := constantAlg.toModule
  let : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro q N
  by_cases hN : N = 0
  · subst N
    have hzero := planeCurve_infinitySupported_riemann_lower
      hf hpartialFirst hpartialSecond
      (0 : FiniteExtensionDivisor K L) (by simp) (by simp)
    have hdegreezero :
        finiteExtensionDivisorDegree K L (0 : FiniteExtensionDivisor K L) = 0 := by
      simp [finiteExtensionDivisorDegree]
    rw [hdegreezero] at hzero
    simp only [Int.toNat_zero, zero_add] at hzero
    simp only [zero_mul, zero_add]
    change 1 ≤ Module.finrank K
      (finiteExtensionRiemannSpace K L (Finsupp.single (.inl q) 0)) + g
    rw [Finsupp.single_zero]
    simpa only [L, g] using hzero
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    obtain ⟨E, hE, hEfinite, hrank⟩ :=
      exists_infinityDivisor_finitePlacePrincipalParts_rank K L q N hNpos
    have hinfinity :
        (finiteExtensionDivisorDegree K L E).toNat + 1 ≤
          Module.finrank K (finiteExtensionRiemannSpace K L E) + g := by
      simpa only [L, g] using
        (planeCurve_infinitySupported_riemann_lower
          hf hpartialFirst hpartialSecond E hE hEfinite)
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

end

end BGS.HasseWeil
