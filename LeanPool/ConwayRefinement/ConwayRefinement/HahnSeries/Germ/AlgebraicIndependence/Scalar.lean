/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Derivation
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.Residue
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.InternalGrading
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.GermChainRule
import Mathlib.Tactic.Abel

/-!
# Coefficients in the associated graded ring of the Cantor–Bendixson degree

For a coefficient field `K`, constant Hahn series have degree zero. Projection to the
zero homogeneous component is a bijective ring homomorphism: a degree-zero representative
differs from its ordinary coefficient by a series bounded strictly below zero. This identifies
the zero component with `K`, gives every component its canonical vector-space structure, and
makes the associated graded ring a graded `K`-algebra.

The additive truncation map is linear for this action and satisfies the Leibniz rule, so it is a
derivation from the associated graded ring to germs of associated-graded-valued functions. It
vanishes on components indexed by limit ordinals and is injective from degree `α + 1` to degree `α`.
The exponent group remains arbitrary, complete, and ordered; no real-exponent reduction is used.
-/

public noncomputable section
open Set Filter Topology
open scoped DirectSum NatOrdinal
universe u v w
namespace HahnSeries.Nonpositive
variable {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

/-- A nonzero constant series has degree exactly zero. -/
theorem degree_C_of_ne (k : K) (hk : k ≠ 0) :
    ν (C k) = (0 : NatOrdinal) := by
  rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
    coe_C, cantorBendixsonValue_of_finite_of_coeff_ne_zero (HahnSeries.C k)
      ((finite_singleton (0 : G)).subset support_single_subset) (by simpa using hk),
    NatOrdinal.of_one, NatOrdinal.cantorDegree_eq_ordinalCantorDegree,
    NatOrdinal.val_one, Ordinal.cantorDegree_one, WithBot.coe_zero]

/-- Every constant series has degree at most zero. -/
theorem degree_C_le (k : K) : ν (C k) ≤ (0 : NatOrdinal) := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [degree_C_of_ne k hk]

private def constantToNonpositiveDegree (k : K) : (ν).nonpositiveSubring :=
  ⟨C k, ((ν).mem_nonpositiveSubring_iff _).mpr (by
    by_cases hk : k = 0
    · subst k
      simp
    · rw [degree_C_of_ne k hk]
      exact le_rfl)⟩

private theorem constantToNonpositiveDegree_zero :
    constantToNonpositiveDegree (G := G) (K := K) 0 = 0 := by
  apply Subtype.ext
  exact map_zero C

private theorem constantToNonpositiveDegree_add (k l : K) :
    constantToNonpositiveDegree (G := G) (k + l) =
      constantToNonpositiveDegree k + constantToNonpositiveDegree l := by
  apply Subtype.ext
  exact map_add C k l

private theorem constantToNonpositiveDegree_one :
    constantToNonpositiveDegree (G := G) (K := K) 1 = 1 := by
  apply Subtype.ext
  exact map_one C

private theorem constantToNonpositiveDegree_mul (k l : K) :
    constantToNonpositiveDegree (G := G) (k * l) =
      constantToNonpositiveDegree k * constantToNonpositiveDegree l := by
  apply Subtype.ext
  exact map_mul C k l

private def constantToNonpositiveDegreeHom : K →+* (ν).nonpositiveSubring where
  toFun := constantToNonpositiveDegree
  map_zero' := constantToNonpositiveDegree_zero
  map_add' := constantToNonpositiveDegree_add
  map_one' := constantToNonpositiveDegree_one
  map_mul' := constantToNonpositiveDegree_mul

/-- The coefficient field mapped isomorphically to the grade-zero component. -/
def cantorBendixsonLayerScalarHom : K →+* (ν).ResidueRing :=
  (ν).residueMap.comp constantToNonpositiveDegreeHom

/-- A coefficient maps to the grade-zero class of its constant Hahn series. -/
theorem cantorBendixsonLayerScalarHom_apply (k : K) :
    cantorBendixsonLayerScalarHom (G := G) k =
      (ν).componentMk 0 ⟨C k, ((ν).mem_filtrationLE_iff _ _).mpr (by
        by_cases hk : k = 0
        · subst k
          simp
        · rw [degree_C_of_ne k hk])⟩ := by
  rw [cantorBendixsonLayerScalarHom, RingHom.comp_apply, (ν).residueMap_apply]
  apply congrArg ((ν).componentMk 0)
  apply Subtype.ext
  rw [(ν).coe_nonpositiveEquivFiltrationLEZero]
  rfl

/-- Distinct coefficients give distinct grade-zero classes. -/
theorem cantorBendixsonLayerScalarHom_injective :
    Function.Injective (cantorBendixsonLayerScalarHom (G := G) (K := K)) := by
  intro k l hkl
  have hsub : cantorBendixsonLayerScalarHom (G := G) (k - l) = 0 := by
    rw [map_sub, hkl, sub_self]
  rw [cantorBendixsonLayerScalarHom_apply, (ν).componentMk_eq_zero_iff] at hsub
  by_contra hne
  rw [degree_C_of_ne _ (sub_ne_zero.mpr hne)] at hsub
  exact (lt_irrefl (0 : WithBot NatOrdinal)) hsub

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]
  [CompleteSpace G] [CharZero K] in
private theorem coe_C_eq_single (k : K) :
    ((C k : Nonpositive G K) : HahnSeries G K) = HahnSeries.single 0 k := by
  ext g
  simp [coe_C]

/-- Every grade-zero class has a unique constant representative modulo strict lower degree. -/
theorem cantorBendixsonLayerScalarHom_surjective :
    Function.Surjective (cantorBendixsonLayerScalarHom (G := G) (K := K)) := by
  intro a
  induction a using QuotientAddGroup.induction_on with
  | H b =>
    let k := constantCoeff (b : Nonpositive G K)
    refine ⟨k, ?_⟩
    rw [cantorBendixsonLayerScalarHom_apply, (ν).coe_component_eq_componentMk]
    apply ((ν).componentMk_eq_componentMk_iff _ _ _).mpr
    change ν (C k - (b : Nonpositive G K)) < (0 : NatOrdinal)
    have hb := ((ν).mem_filtrationLE_iff _ _).mp b.property
    have hv : (b : HahnSeries G K).cantorBendixsonValue = 0 ∨
        (b : HahnSeries G K).cantorBendixsonValue = 1 := by
      by_cases hm : 0 ∈ (b : HahnSeries G K).closedSupport
      · right
        have hr : (b : HahnSeries G K).cantorBendixsonRank 0 = 0 := by
          rw [cantorBendixsonDegreeValuation_of_mem _ hm, WithBot.coe_le_coe] at hb
          exact le_zero_iff.mp hb
        rw [cantorBendixsonValue_of_mem _ ((mem_closedSupport _ _).mp hm), hr,
          Ordinal.opow_zero]
      · left
        exact cantorBendixsonValue_of_notMem _
          (by simpa only [mem_closedSupport] using hm)
    rcases hv with hv | hv
    · have hk : k = 0 := by
        dsimp [k]
        rw [constantCoeff_apply]
        apply not_ne_iff.mp
        intro hn
        have hmem : 0 ∈ (b : HahnSeries G K).support := hn
        rw [cantorBendixsonValue_of_mem _ (subset_closure hmem)] at hv
        exact Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero hv
      rw [hk, map_zero, zero_sub, (ν).map_neg,
        cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply, hv,
        NatOrdinal.of_zero, NatOrdinal.cantorDegree_zero]
      exact WithBot.bot_lt_coe 0
    · have hz := (cantorBendixsonValue_eq_one_iff (b : HahnSeries G K)).mp hv |>.2
      rw [show C k - (b : Nonpositive G K) =
        -((b : Nonpositive G K) - C k) by abel, (ν).map_neg,
        cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply]
      change NatOrdinal.cantorDegree
        (NatOrdinal.of (((b : HahnSeries G K) - (C k : Nonpositive G K)).cantorBendixsonValue)) < 0
      have hz' : ((b : HahnSeries G K) - (C k : Nonpositive G K)).cantorBendixsonValue = 0 := by
        simpa only [coe_C_eq_single, k, constantCoeff_apply] using hz
      rw [hz', NatOrdinal.of_zero, NatOrdinal.cantorDegree_zero]
      exact WithBot.bot_lt_coe 0

/-- Every homogeneous component is a vector space over the coefficient field. -/
noncomputable instance cantorBendixsonComponentModule (α : NatOrdinal.{u}) :
    Module K ((ν).Component α) :=
  Module.compHom ((ν).Component α) (cantorBendixsonLayerScalarHom (G := G) (K := K))

/-- The componentwise coefficient action on the associated graded ring. -/
instance cantorBendixsonGAlgebra : DirectSum.GAlgebra K (ν).Component where
  toFun := (cantorBendixsonLayerScalarHom (G := G) (K := K)).toAddMonoidHom
  map_one := map_one (cantorBendixsonLayerScalarHom (G := G) (K := K))
  map_mul k l := by
    change GradedMonoid.mk 0 (cantorBendixsonLayerScalarHom (G := G) (k * l)) = _
    rw [map_mul]
    exact GradedMonoid.mk_zero_smul _ _
  commutes _ x := DirectSum.GCommSemiring.mul_comm _ x
  smul_def k x := GradedMonoid.mk_zero_smul
    (cantorBendixsonLayerScalarHom (G := G) k) x.2

/-- The associated graded ring as an algebra over its coefficient field. -/
instance cantorBendixsonAlgebra : Algebra K (ν).AssociatedGraded := inferInstance

/-- Coefficients embed in grade zero. -/
@[simp]
theorem cantorBendixson_algebraMap_apply (k : K) :
    algebraMap K (ν).AssociatedGraded k =
      DirectSum.of (ν).Component 0 (cantorBendixsonLayerScalarHom (G := G) k) :=
  DirectSum.algebraMap_apply K (ν).Component k

/-- The graded derivation vanishes on the coefficient field. -/
theorem cantorBendixsonGradedDerivation_algebraMap (k : K) :
    cantorBendixsonGradedDerivation
      (algebraMap K (ν).AssociatedGraded k) = 0 := by
  rw [cantorBendixson_algebraMap_apply, cantorBendixsonGradedDerivation_of,
    cantorBendixsonHomogeneousDerivation_limit 0 NatOrdinal.constantCoeff_zero,
    AddMonoidHom.zero_apply]

private def cantorBendixsonDerivationLinearMap :
    (ν).AssociatedGraded →ₗ[K]
      Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded where
  toFun := cantorBendixsonGradedDerivation
  map_add' := map_add cantorBendixsonGradedDerivation
  map_smul' k x := by
    rw [Algebra.smul_def, cantorBendixsonGradedDerivation_mul,
      cantorBendixsonGradedDerivation_algebraMap, zero_mul, zero_add]
    generalize cantorBendixsonGradedDerivation x = f
    induction f using Filter.Germ.inductionOn with
    | h f =>
      rw [← Filter.Germ.coe_smul]
      exact Filter.EventuallyEq.germ_eq (Filter.Eventually.of_forall fun γ ↦ by
        change algebraMap K (ν).AssociatedGraded k * f γ = k • f γ
        rw [Algebra.smul_def])

private theorem cantorBendixsonDerivationLinearMap_apply (x : (ν).AssociatedGraded) :
    cantorBendixsonDerivationLinearMap x = cantorBendixsonGradedDerivation x := (rfl)

private theorem germ_smul_eq_const_mul
    (x : (ν).AssociatedGraded)
    (f : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) :
    x • f = (x : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) * f := by
  induction f using Filter.Germ.inductionOn with
  | h f => rfl

/-- The translated-truncation map as a derivation on the associated graded ring. -/
def cantorBendixsonDerivation :
    Derivation K (ν).AssociatedGraded
      (Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) :=
  Derivation.mk' cantorBendixsonDerivationLinearMap fun x y => by
    rw [cantorBendixsonDerivationLinearMap_apply,
      cantorBendixsonGradedDerivation_mul]
    rw [germ_smul_eq_const_mul, germ_smul_eq_const_mul]
    ac_rfl

/-- The derivation has the same values as the additive translated-truncation map. -/
@[simp]
theorem cantorBendixsonDerivation_apply (x : (ν).AssociatedGraded) :
    cantorBendixsonDerivation x = cantorBendixsonGradedDerivation x := (rfl)

/-- The derivation is injective on every successor homogeneous component. -/
theorem cantorBendixsonDerivation_injective_on_successor (α : NatOrdinal.{u}) :
    Function.Injective (fun a : (ν).Component (α + 1) ↦
      cantorBendixsonDerivation
        (DirectSum.of (ν).Component (α + 1) a)) :=
  cantorBendixsonGradedDerivation_injective_on_successor α

/-- The Cantor–Bendixson derivation lowers successor degrees, vanishes on degrees that are limit
ordinals, and is
injective on successor grades. -/
theorem cantorBendixson_isLoweringDerivation :
    GermPolynomial.IsLoweringDerivation
      (DirectSum.rangeLof K (ν).Component)
      (cantorBendixsonDerivation (G := G) (K := K)) where
  mem_lower {α} hα {x} hx := by
    obtain ⟨a, rfl⟩ := (DirectSum.mem_rangeLof_iff K (ν).Component α x).mp hx
    rw [DirectSum.lof_eq_of]
    have hsucc : α.removeNat 1 + 1 = α := by
      simpa only [Nat.cast_one] using NatOrdinal.removeNat_add_natCast hα
    let a' : (ν).Component (α.removeNat 1 + 1) :=
      AddEquiv.cast (M := (ν).Component) hsucc.symm a
    have ha' : DirectSum.of (ν).Component (α.removeNat 1 + 1) a' =
        DirectSum.of (ν).Component α a := by
      apply DirectSum.of_eq_of_gradedMonoid_eq
      apply Sigma.ext hsucc
      change a' ≍ a
      exact cast_heq (congrArg (ν).Component hsucc.symm) a
    rw [← ha', GermPolynomial.mem_germSubmodule_iff]
    have hf : cantorBendixsonDerivation
          (DirectSum.of (ν).Component (α.removeNat 1 + 1) a') =
        Filter.Germ.map (DirectSum.of (ν).Component (α.removeNat 1))
          (cantorBendixsonLayerDeriv (α.removeNat 1) a') := by
      induction a' using MaxAddDegree.componentInductionOn with
      | H b =>
        change cantorBendixsonGradedDerivation
          (DirectSum.of (ν).Component (α.removeNat 1 + 1)
            ((ν).componentMk (α.removeNat 1 + 1) b)) = _
        rw [← (ν).homogeneousMk_apply,
          cantorBendixsonGradedDerivation_homogeneousMk_succ _ rfl,
          cantorBendixsonLayerDeriv_componentMk]
        rfl
    rw [hf]
    induction cantorBendixsonLayerDeriv (α.removeNat 1) a' using Filter.Germ.inductionOn with
    | h f =>
      rw [Filter.Germ.map_coe, Filter.Germ.liftPred_coe]
      exact Filter.Eventually.of_forall fun t ↦
        DirectSum.of_mem_rangeLof K (ν).Component _ (f t)
  eq_zero {α} hα {x} hx := by
    obtain ⟨a, rfl⟩ := (DirectSum.mem_rangeLof_iff K (ν).Component α x).mp hx
    rw [DirectSum.lof_eq_of]
    change cantorBendixsonGradedDerivation (DirectSum.of (ν).Component α a) = 0
    rw [cantorBendixsonGradedDerivation_of,
      cantorBendixsonHomogeneousDerivation_limit α hα, AddMonoidHom.zero_apply]
  injective {α} hα {x} hx hx0 := by
    obtain ⟨a, rfl⟩ := (DirectSum.mem_rangeLof_iff K (ν).Component α x).mp hx
    rw [DirectSum.lof_eq_of] at hx0 ⊢
    have hsucc : α.removeNat 1 + 1 = α := by
      simpa only [Nat.cast_one] using NatOrdinal.removeNat_add_natCast hα
    let a' : (ν).Component (α.removeNat 1 + 1) :=
      AddEquiv.cast (M := (ν).Component) hsucc.symm a
    have ha' : DirectSum.of (ν).Component (α.removeNat 1 + 1) a' =
        DirectSum.of (ν).Component α a := by
      apply DirectSum.of_eq_of_gradedMonoid_eq
      apply Sigma.ext hsucc
      change a' ≍ a
      exact cast_heq (congrArg (ν).Component hsucc.symm) a
    rw [← ha'] at hx0 ⊢
    have ha0 : a' = 0 :=
      cantorBendixsonDerivation_injective_on_successor (α.removeNat 1) (by simpa using hx0)
    rw [ha0, map_zero]

/-- The internal grade-zero component consists exactly of coefficient scalars. -/
theorem cantorBendixson_gradeZeroScalars :
    GermPolynomial.GradeZeroScalars (DirectSum.rangeLof K (ν).Component) := by
  rw [GermPolynomial.gradeZeroScalars_iff]
  intro x hx
  obtain ⟨a, rfl⟩ :=
    (DirectSum.mem_rangeLof_iff K (ν).Component 0 x).mp hx
  rw [DirectSum.lof_eq_of]
  obtain ⟨k, hk⟩ := cantorBendixsonLayerScalarHom_surjective (G := G) (K := K) a
  refine ⟨k, ?_⟩
  rw [cantorBendixson_algebraMap_apply, hk]

/-- Every minimal homogeneous system in the finite-degree components is algebraically
independent over the coefficient field. -/
theorem cantorBendixson_minimalSystem_aeval_injective
    {ι : Type w} (wt : ι → ℕ) (x : ι → (ν).AssociatedGraded)
    (hx : GermPolynomial.IsMinimalSystem
      (DirectSum.rangeLof K (ν).Component) wt x) :
    Function.Injective (MvPolynomial.aeval x :
      MvPolynomial ι K →ₐ[K] (ν).AssociatedGraded) := by
  classical
  letI : Nontrivial ((ν).Component 0) :=
    Function.Injective.nontrivial
      (cantorBendixsonLayerScalarHom_injective (G := G) (K := K))
  letI : Nontrivial (ν).AssociatedGraded :=
    Function.Injective.nontrivial (DirectSum.of_injective 0)
  have hc := hx.isHomogeneousCoordinates cantorBendixson_gradeZeroScalars
  exact hc.aeval_injective cantorBendixson_isLoweringDerivation

/-- An ordinal minimal system generates the associated graded ring of the Cantor–Bendixson
degree. -/
theorem cantorBendixson_ordinalMinimalSystem_aeval_surjective
    {ι : Type w} (wt : ι → NatOrdinal.{u})
    (x : ι → (ν).AssociatedGraded)
    (hx : OrdinalGraded.IsMinimalSystem
      (DirectSum.rangeLof K (ν).Component) wt x) :
    Function.Surjective (MvPolynomial.aeval x :
      MvPolynomial ι K →ₐ[K] (ν).AssociatedGraded) :=
  hx.aeval_surjective cantorBendixson_gradeZeroScalars

/-- Every ordinal minimal system has pointwise polynomial representatives for the
Cantor–Bendixson derivative of each generator. -/
theorem cantorBendixson_ordinalMinimalSystem_exists_derivativeRep
    {ι : Type w} (wt : ι → NatOrdinal.{u})
    (x : ι → (ν).AssociatedGraded)
    (hx : OrdinalGraded.IsMinimalSystem
      (DirectSum.rangeLof K (ν).Component) wt x) :
    ∃ g : ι → G → MvPolynomial ι K,
      OrdinalGraded.DerivativeRep wt x
        (cantorBendixsonDerivation (G := G) (K := K)) g :=
  OrdinalGraded.IsMinimalSystem.exists_derivativeRep hx cantorBendixson_isLoweringDerivation
    cantorBendixson_gradeZeroScalars

end HahnSeries.Nonpositive
