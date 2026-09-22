/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneOnePointRiemannLower
import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointSectionSelection
import LeanPool.MarkoffModP.BGS.HasseWeil.StepanovRestrictionMaps
import LeanPool.MarkoffModP.BGS.HasseWeil.StepanovParameters

/-!
# The degree-one plane Stepanov auxiliary

This file assembles the one-point ingredients of the Bombieri--Stepanov
construction for an absolutely irreducible bivariate plane curve.

The plane monomial theorem initially gives the coarse Riemann lower bound
only along an explicit arithmetic progression of pole levels.  Since the
progression has positive step, every level lies below a later progression
level.  The one-place increment estimate therefore transports the lower
bound back to every level.  Exact constants then force enough strict levels
to select the two section families prescribed by `stepanovEll` and
`stepanovM`.

At a degree-one selected place, the target Riemann space has dimension at
most its pole budget plus one.  The existing numerical parameter inequality
then gives a nonzero coefficient grid killed by the second Frobenius
restriction and detected by the first.

The degree-one hypothesis is deliberately an implication in the final
theorem.  This module does **not** assert that the controlled infinity place
has degree one, and it does not count square-extension points.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance planeStepanovConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance planeStepanovConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The data furnished by strict-level section selection at pole budget
`N`: nonzero sections with distinct exact pole orders, bounded digits, and
linear independence. -/
def onePointSectionFamilySpec
    {α : Type*} (P : FiniteExtensionPlace K L) (N : ℕ)
    (f : α → L) (d : α → ℕ) : Prop :=
  (∀ i, f i ∈ finiteExtensionOnePointRiemannSpace K L P N) ∧
    (∀ i, f i ≠ 0) ∧
    (∀ i, finiteExtensionPrincipalDivisor K L (f i) P = -(d i : ℤ)) ∧
    Function.Injective d ∧
    (∀ i, d i ≤ N) ∧
    LinearIndependent K f

/-- A coefficient grid is a Stepanov auxiliary when it is nonzero, is killed
by the swapped restriction, and gives a nonzero function under the first
restriction. -/
def onePointStepanovAuxiliarySpec
    {α β : Type*} (f : α → L) (g : β → L) (s : ℕ)
    (c : α × β →₀ K) : Prop :=
  c ≠ 0 ∧
    onePointStepanovSecondRestrictionMap K L f g s c = 0 ∧
    onePointStepanovFirstRestrictionMap K L f g s c ≠ 0

private theorem finiteExtensionOnePointRiemannSpace_finrank_le_add_gap
    (P : FiniteExtensionPlace K L) {N M : ℕ} (hNM : N ≤ M) :
    Module.finrank K (finiteExtensionOnePointRiemannSpace K L P M) ≤
      Module.finrank K (finiteExtensionOnePointRiemannSpace K L P N) +
        (M - N) * finiteExtensionPlaceDegree K L P := by
  let D : FiniteExtensionDivisor K L := Finsupp.single P (N : ℤ)
  have hD : ∀ v, 0 ≤ D v := by
    intro v
    by_cases hv : v = P
    · subst v
      simp [D]
    · simp [D, Finsupp.single_eq_of_ne hv]
  let : Module.Finite K (finiteExtensionRiemannSpace K L D) :=
    finiteExtensionRiemannSpace_effective_moduleFinite K L D hD
  have hinc := finiteExtensionRiemannSpace_natPlace_increment
    K L D hD P (M - N)
  have hdivisor : D + Finsupp.single P ((M - N : ℕ) : ℤ) =
      Finsupp.single P (M : ℤ) := by
    ext v
    by_cases hv : v = P
    · subst v
      simp only [D, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    · simp [D, Finsupp.single_eq_of_ne hv]
  rw [hdivisor] at hinc
  exact hinc.2

private theorem finiteExtensionOnePointRiemannSpace_finrank_upper_degree_one
    (P : FiniteExtensionPlace K L)
    (hconstants : algebraicClosure K L = ⊥)
    (hdegree : finiteExtensionPlaceDegree K L P = 1) :
    ∀ N, Module.finrank K
      (finiteExtensionOnePointRiemannSpace K L P N) ≤ N + 1 := by
  intro N
  induction N with
  | zero =>
      simpa using
        (finiteExtensionOnePointRiemannSpace_zero_finrank K L P hconstants).le
  | succ N ih =>
      have hstep := finiteExtensionOnePointRiemannSpace_finrank_succ_le
        K L P N
      rw [hdegree] at hstep
      omega

/-- **Conditional degree-one Stepanov auxiliary for a plane curve.**

For an absolutely irreducible bivariate plane equation with both coordinate
partials nonzero, this theorem chooses the controlled infinity place from
the plane monomial argument and retains its positive pole coefficient and
degree bound.  If that selected place has degree one, then for

`g = (degreeOf 0 F - 1) * (degreeOf 1 F - 1)`,
`s = #K`, `ell = s - 1`, and `m = s + 2g`,

it produces two strict-level section families and a nonzero coefficient grid
whose second Stepanov restriction vanishes while its first restriction is a
nonzero function.

The implication on the degree-one equality is essential: no existence of a
degree-one place is claimed here. -/
theorem exists_planeCurve_onePointStepanovAuxiliary_of_degree_one
    {F : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) F))
    (hpartialFirst : MvPolynomial.pderiv 0 F ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 F ≠ 0)
    (hlarge :
      let genusBudget := planeCurveBidegreeGenusBudget F
      (genusBudget + 1) * (genusBudget + 2) ≤ Fintype.card K) :
    let hF : Irreducible F :=
      irreducible_of_irreducible_map_algebraicClosure habsolute
    letI := planeCurveCoordinateRing_isDomain hF
    let hx := firstCoordinate_transcendental hF
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra F hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hF hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hF hpartialSecond
    ∃ P : FiniteExtensionInfinityPlace K (PlaneCurveFunctionField F),
      let Q : FiniteExtensionPlace K (PlaneCurveFunctionField F) := .inr P
      let genusBudget := planeCurveBidegreeGenusBudget F
      let s := Fintype.card K
      let ell := stepanovEll s
      let m := stepanovM genusBudget s
      0 < finiteExtensionPoleDivisor K (PlaneCurveFunctionField F)
          (planeCurveFunction F 0) Q ∧
        0 < finiteExtensionPlaceDegree K (PlaneCurveFunctionField F) Q ∧
        finiteExtensionPlaceDegree K (PlaneCurveFunctionField F) Q ≤
          MvPolynomial.degreeOf 1 F ∧
        (finiteExtensionPlaceDegree K (PlaneCurveFunctionField F) Q = 1 →
          ∃ (u : Option (Fin (ell - genusBudget)) →
                PlaneCurveFunctionField F)
            (du : Option (Fin (ell - genusBudget)) → ℕ)
            (v : Option (Fin (m - genusBudget)) →
                PlaneCurveFunctionField F)
            (dv : Option (Fin (m - genusBudget)) → ℕ)
            (c : (Option (Fin (ell - genusBudget)) ×
                Option (Fin (m - genusBudget))) →₀ K),
            onePointSectionFamilySpec K (PlaneCurveFunctionField F)
                Q ell u du ∧
              onePointSectionFamilySpec K (PlaneCurveFunctionField F)
                Q m v dv ∧
              onePointStepanovAuxiliarySpec K (PlaneCurveFunctionField F)
                u v s c) := by
  let hF : Irreducible F :=
    irreducible_of_irreducible_map_algebraicClosure habsolute
  let : IsDomain (PlaneCurveCoordinateRing F) :=
    planeCurveCoordinateRing_isDomain hF
  let hx := firstCoordinate_transcendental hF
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField F
  let x : L := planeCurveFunction F 0
  let y : L := planeCurveFunction F 1
  let b := MvPolynomial.degreeOf 1 F
  let genusBudget := planeCurveBidegreeGenusBudget F
  let s := Fintype.card K
  let ell := stepanovEll s
  let m := stepanovM genusBudget s
  let canonicalAlg : Algebra K L := inferInstance
  let : Algebra K L := canonicalAlg
  let ratAlg : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra F hx
  let : Algebra (RatFunc K) L := ratAlg
  let : SMul (RatFunc K) L := ratAlg.toSMul
  let : Module (RatFunc K) L := ratAlg.toModule
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hF hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hF hpartialSecond
  let inducedAlg : Algebra K L := planeStepanovConstantAlgebra K L
  have hinducedAlg : inducedAlg = canonicalAlg := by
    apply Algebra.algebra_ext
    intro c
    change (@ratFuncSpecialization K L _ _ canonicalAlg x hx) (RatFunc.C c) =
      @algebraMap K L _ _ canonicalAlg c
    have h := DFunLike.congr_fun
      (@ratFuncSpecialization_comp_polynomial_algebraMap
        K L _ _ canonicalAlg x hx)
      (Polynomial.C c)
    simpa using h
  let : Algebra K L := inducedAlg
  let : SMul K L := inducedAlg.toSMul
  let : Module K L := inducedAlg.toModule
  let : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hconstantsCanonical :
      @algebraicClosure K L _ _ canonicalAlg = ⊥ := by
    simpa only [L] using
      planeCurveFunctionField_algebraicClosure_eq_bot
        F habsolute hpartialSecond
  have hconstants : algebraicClosure K L = ⊥ := by
    change @algebraicClosure K L _ _ inducedAlg = ⊥
    rw [hinducedAlg]
    exact hconstantsCanonical
  obtain ⟨P, hPpole, hPdegreePositive, hPdegreeBound, hprogress⟩ :=
    exists_planeCurve_onePointRiemannSpace_progression_lower_bound
      habsolute hpartialFirst hpartialSecond
  let Q : FiniteExtensionPlace K L := .inr P
  refine ⟨P, hPpole, hPdegreePositive, hPdegreeBound, ?_⟩
  intro hPdegree
  have hcoarse : ∀ N,
      N * finiteExtensionPlaceDegree K L Q + 1 ≤
        Module.finrank K (finiteExtensionOnePointRiemannSpace K L Q N) +
          genusBudget := by
    intro N
    let M := planeMonomialPoleLevel K L x y N b Q
    obtain ⟨hMformula, _hMfinite, hMlowerRaw⟩ := hprogress N
    have hMformula' : M =
        N * (finiteExtensionPoleDivisor K L x Q).toNat +
          (b - 1) * (finiteExtensionPoleDivisor K L y Q).toNat := by
      simpa only [M, L, x, y, b, Q] using hMformula
    have hPoleNat : 0 < (finiteExtensionPoleDivisor K L x Q).toNat := by
      have hPole : 0 < finiteExtensionPoleDivisor K L x Q := by
        simpa only [L, x, Q] using hPpole
      omega
    have hNM : N ≤ M := by
      rw [hMformula']
      have hbase : N ≤
          N * (finiteExtensionPoleDivisor K L x Q).toNat :=
        Nat.le_mul_of_pos_right N hPoleNat
      omega
    have hgap := finiteExtensionOnePointRiemannSpace_finrank_le_add_gap
      K L Q hNM
    have hMlower : M * finiteExtensionPlaceDegree K L Q + 1 ≤
        Module.finrank K (finiteExtensionOnePointRiemannSpace K L Q M) +
          genusBudget := by
      simpa only [M, L, x, y, b, Q, genusBudget] using hMlowerRaw
    have hMdecomp : M = N + (M - N) := by omega
    have hmul : M * finiteExtensionPlaceDegree K L Q =
        N * finiteExtensionPlaceDegree K L Q +
          (M - N) * finiteExtensionPlaceDegree K L Q := by
      calc
        M * finiteExtensionPlaceDegree K L Q =
            (N + (M - N)) * finiteExtensionPlaceDegree K L Q := by
          rw [← hMdecomp]
        _ = N * finiteExtensionPlaceDegree K L Q +
            (M - N) * finiteExtensionPlaceDegree K L Q := by
          rw [Nat.add_mul]
    omega
  have hstrict : ∀ N, genusBudget ≤ N →
      N - genusBudget ≤
        (strictFiltrationLevels
          (fun r => finiteExtensionOnePointRiemannSpace K L Q r) N).card := by
    intro N hgenusN
    apply le_card_onePointStrictLevels_of_finrank_lower
      K L Q N (N - genusBudget) hconstants
    have hN := hcoarse N
    rw [hPdegree] at hN ⊢
    omega
  have hlarge' : (genusBudget + 1) * (genusBudget + 2) ≤ s := by
    simpa only [genusBudget, s] using hlarge
  have hsPositive : 0 < s := Fintype.card_pos
  have hgenusLtS : genusBudget < s := by
    nlinarith
  have hgenusEll : genusBudget ≤ ell := by
    simp only [ell, stepanovEll]
    omega
  have hgenusM : genusBudget ≤ m := by
    simp only [m, stepanovM]
    omega
  have hellLt : ell < s := stepanovEll_lt hlarge'
  have hellStrict := hstrict ell hgenusEll
  have hmStrict := hstrict m hgenusM
  obtain ⟨u, du, huMem, huNe, huOrder, hduInjective,
      hduLe, huLI⟩ :=
    exists_onePointSectionsWithConstant_of_le_card_strictLevels
      K L Q ell (ell - genusBudget) hellStrict
  obtain ⟨v, dv, hvMem, hvNe, hvOrder, hdvInjective,
      hdvLe, hvLI⟩ :=
    exists_onePointSectionsWithConstant_of_le_card_strictLevels
      K L Q m (m - genusBudget) hmStrict
  have hgridLI : LinearIndependent K
      (fun ij : Option (Fin (ell - genusBudget)) ×
          Option (Fin (m - genusBudget)) => u ij.1 * (v ij.2) ^ s) := by
    exact onePointStepanovGrid_linearIndependent K L Q u v du dv s
      huNe hvNe huOrder hvOrder hduInjective hdvInjective
      (fun i => (hduLe i).trans_lt hellLt)
  have hupper : Module.finrank K
      (finiteExtensionOnePointRiemannSpace K L Q (s * ell + m)) ≤
        s * ell + m + 1 :=
    finiteExtensionOnePointRiemannSpace_finrank_upper_degree_one
      K L Q hconstants hPdegree (s * ell + m)
  have hellCard : ell - genusBudget + 1 = ell + 1 - genusBudget := by
    omega
  have hmCard : m - genusBudget + 1 = m + 1 - genusBudget := by
    omega
  have hnumeric : s * ell + m + 1 <
      Fintype.card (Option (Fin (ell - genusBudget))) *
        Fintype.card (Option (Fin (m - genusBudget))) := by
    have hdim := stepanov_dimension_inequality hlarge'
    simpa only [Fintype.card_option, Fintype.card_fin, hellCard, hmCard,
      Nat.mul_comm s ell] using hdim
  obtain ⟨c, hcNe, hsecond, hfirst⟩ :=
    exists_onePointStepanovAuxiliary_of_target_finrank_upper
      K L Q u v ell m s (s * ell + m + 1)
      huMem hvMem hgridLI hupper hnumeric
  have hsecondRaw :
      onePointStepanovSecondRestrictionMap K L u v s c = 0 := by
    have h := congrArg Subtype.val hsecond
    simpa only [onePointStepanovSecondCodRestrictionMap_coe,
      Submodule.coe_zero] using h
  refine ⟨u, du, v, dv, c, ?_, ?_, ?_⟩
  · exact ⟨huMem, huNe, huOrder, hduInjective, hduLe, huLI⟩
  · exact ⟨hvMem, hvNe, hvOrder, hdvInjective, hdvLe, hvLI⟩
  · exact ⟨hcNe, hsecondRaw, hfirst⟩

end

end BGS.HasseWeil
