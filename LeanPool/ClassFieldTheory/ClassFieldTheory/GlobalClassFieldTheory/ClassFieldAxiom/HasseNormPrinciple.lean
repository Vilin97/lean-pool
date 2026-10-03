/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitNormContainment
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Principal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormProperties
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Cardinality
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.TateH0.Main
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.CohomologyBridge
/-!
# The Hasse norm principle: the concrete local-global map

This file proves the Hasse norm principle on the actual idele and field norm
maps.  The local condition is expressed canonically:
at a place `v` it is the image of the determinant norm on
`K_v ⊗[K] L`.  At finite places this is the chosen completion norm
subgroup by
`_root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup`.

The resulting homomorphism

`Kˣ / N(Lˣ) ⟶ I_K / I_K,loc-norm`

is the concrete diagonal local-norm map.  Its injectivity is exactly the
Hasse norm principle.  The global-to-local inclusion and this equivalence
are independent of the global class-field axiom; the reverse inclusion
follows from degree-minus-one Tate-cohomology vanishing.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField

noncomputable
section

namespace GlobalClassFieldTheory.ClassFieldAxiom

open CategoryTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand

private theorem mulExact_transport_mulEquiv
    {A B C B' C' : Type*}
    [Monoid A] [Monoid B] [Monoid C] [Monoid B'] [Monoid C']
    (f : A →* B) (g : B →* C)
    (eB : B ≃* B') (eC : C ≃* C')
    (h : Function.MulExact f g) :
    Function.MulExact
      (eB.toMonoidHom.comp f)
      (eC.toMonoidHom.comp (g.comp eB.symm.toMonoidHom)) := by
  intro y
  change
    eC (g (eB.symm y)) = 1 ↔
      ∃ x, eB (f x) = y
  constructor
  · intro hy
    have hy' : g (eB.symm y) = 1 :=
      eC.map_eq_one_iff.mp hy
    obtain ⟨x, hx⟩ := (h (eB.symm y)).mp hy'
    refine ⟨x, ?_⟩
    simpa only [eB.apply_symm_apply] using congrArg eB hx
  · rintro ⟨x, hx⟩
    apply eC.map_eq_one_iff.mpr
    apply (h (eB.symm y)).mpr
    refine ⟨x, ?_⟩
    apply eB.injective
    simpa only [eB.apply_symm_apply] using hx

private noncomputable def tateH0FixedCycle
    {G A : Type}
    [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (a : fixedSubgroup G A) :
    (tateComplex (Rep.ofMulDistribMulAction G A)).cycles 0 := by
  let M := Rep.ofMulDistribMulAction G A
  let S : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk M.norm.toModuleCatHom (groupCohomology.d₀₁ M)
      (Rep.norm_comp_d_eq_zero M)
  let eS : (tateComplex M).sc' (-1) 0 1 ≅ S :=
    ShortComplex.isoMk
      (by exact groupHomology.chainsIso₀ M)
      (groupCohomology.cochainsIso₀ M)
      (groupCohomology.cochainsIso₁ M)
      (by
        change
          (groupHomology.chainsIso₀ M).hom ≫ M.norm.toModuleCatHom =
            M.tateNorm ≫ (groupCohomology.cochainsIso₀ M).hom
        rw [Rep.tateNorm]
        simp)
      (groupCohomology.comp_d₀₁_eq M)
  let x : S.moduleCatLeftHomologyData.K := by
    change LinearMap.ker
      (groupCohomology.d₀₁ (Rep.ofMulDistribMulAction G A)).hom
    exact ⟨Additive.ofMul a.1, by
      rw [groupCohomology.d₀₁_ker_eq_invariants]
      intro g
      apply Additive.ofMul.injective
      exact a.2 g⟩
  exact
    ((tateComplex M).cyclesIsoSc' (-1) 0 1 (by simp) (by simp)).inv
      ((ShortComplex.cyclesMapIso eS).inv
        (S.moduleCatCyclesIso.inv x))

private theorem tateH0FixedCycle_iCycles
    {G A : Type}
    [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (a : fixedSubgroup G A) :
    let M := Rep.ofMulDistribMulAction G A
    (tateComplex M).iCycles 0 (tateH0FixedCycle a) =
      (groupCohomology.cochainsIso₀ M).inv
        (by
          change Additive A
          exact Additive.ofMul a.1) := by
  let M := Rep.ofMulDistribMulAction G A
  let S : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk M.norm.toModuleCatHom (groupCohomology.d₀₁ M)
      (Rep.norm_comp_d_eq_zero M)
  let eS : (tateComplex M).sc' (-1) 0 1 ≅ S :=
    ShortComplex.isoMk
      (by exact groupHomology.chainsIso₀ M)
      (groupCohomology.cochainsIso₀ M)
      (groupCohomology.cochainsIso₁ M)
      (by
        change
          (groupHomology.chainsIso₀ M).hom ≫ M.norm.toModuleCatHom =
            M.tateNorm ≫ (groupCohomology.cochainsIso₀ M).hom
        rw [Rep.tateNorm]
        simp)
      (groupCohomology.comp_d₀₁_eq M)
  let x : S.moduleCatLeftHomologyData.K := by
    change LinearMap.ker
      (groupCohomology.d₀₁ (Rep.ofMulDistribMulAction G A)).hom
    exact ⟨Additive.ofMul a.1, by
      rw [groupCohomology.d₀₁_ker_eq_invariants]
      intro g
      apply Additive.ofMul.injective
      exact a.2 g⟩
  change
    (((((tateComplex M).cyclesIsoSc'
            (-1) 0 1 (by simp) (by simp)).inv ≫
          (tateComplex M).iCycles 0).hom
      ((ShortComplex.cyclesMapIso eS).inv
        (S.moduleCatCyclesIso.inv x)))) =
      (groupCohomology.cochainsIso₀ M).inv
        (by
          change Additive A
          exact Additive.ofMul a.1)
  rw [HomologicalComplex.cyclesIsoSc'_inv_iCycles]
  change
    (((ShortComplex.cyclesMap eS.inv ≫
          ((tateComplex M).sc' (-1) 0 1).iCycles).hom
      (S.moduleCatCyclesIso.inv x))) =
      (groupCohomology.cochainsIso₀ M).inv
        (by
          change Additive A
          exact Additive.ofMul a.1)
  rw [ShortComplex.cyclesMap_i]
  change
    (((S.moduleCatCyclesIso.inv ≫ S.iCycles ≫ eS.inv.τ₂).hom x)) =
      (groupCohomology.cochainsIso₀ M).inv
        (by
          change Additive A
          exact Additive.ofMul a.1)
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles_assoc]
  change
    (groupCohomology.cochainsIso₀
        (Rep.ofMulDistribMulAction G A)).inv (Additive.ofMul a.1) =
      (groupCohomology.cochainsIso₀
        (Rep.ofMulDistribMulAction G A)).inv (Additive.ofMul a.1)
  rfl

private theorem tateH0FixedCycle_map
    {G A B : Type}
    [Group G] [Fintype G] [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    (f : A →* B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a)
    (a : fixedSubgroup G A) :
    let φ := equivariantRepHom f hf
    let b : fixedSubgroup G B :=
      ⟨f a, fun g ↦ by rw [← hf g a, a.2 g]⟩
    HomologicalComplex.cyclesMap (tateComplex.map φ) 0
        (tateH0FixedCycle a) =
      tateH0FixedCycle b := by
  let MA := Rep.ofMulDistribMulAction G A
  let MB := Rep.ofMulDistribMulAction G B
  let φ := equivariantRepHom f hf
  let b : fixedSubgroup G B :=
    ⟨f a, fun g ↦ by rw [← hf g a, a.2 g]⟩
  apply
    (ModuleCat.mono_iff_injective ((tateComplex MB).iCycles 0)).1
      inferInstance
  change
    (((HomologicalComplex.cyclesMap (tateComplex.map φ) 0 ≫
          (tateComplex MB).iCycles 0).hom
        (tateH0FixedCycle a))) =
      (tateComplex MB).iCycles 0 (tateH0FixedCycle b)
  rw [HomologicalComplex.cyclesMap_i]
  simp only [ModuleCat.comp_apply]
  rw [tateH0FixedCycle_iCycles a, tateH0FixedCycle_iCycles b]
  apply
    (ModuleCat.mono_iff_injective
      (groupCohomology.cochainsIso₀ MB).hom).1 inferInstance
  change
    (((groupCohomology.cochainsMap (.id G) φ).f 0 ≫
          (groupCohomology.cochainsIso₀ MB).hom).hom
        ((groupCohomology.cochainsIso₀ MA).inv
          (by
            change Additive A
            exact Additive.ofMul a.1))) =
      (groupCohomology.cochainsIso₀ MB).hom
        ((groupCohomology.cochainsIso₀ MB).inv
          (Additive.ofMul b.1))
  rw [groupCohomology.cochainsMap_f_0_comp_cochainsIso₀]
  rfl

private theorem isoZeroBoundary_fixedCycle
    {G A : Type}
    [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (a : fixedSubgroup G A) :
    let M := Rep.ofMulDistribMulAction G A
    let S : ShortComplex (ModuleCat ℤ) :=
      ShortComplex.mk M.norm.toModuleCatHom (groupCohomology.d₀₁ M)
        (Rep.norm_comp_d_eq_zero M)
    (TateCohomology.isoZeroBoundary M).hom
        ((tateComplex M).homologyπ 0 (tateH0FixedCycle a)) =
      S.homologyπ
        (S.moduleCatCyclesIso.inv
          (by
            change LinearMap.ker
              (groupCohomology.d₀₁
                (Rep.ofMulDistribMulAction G A)).hom
            exact ⟨Additive.ofMul a.1, by
              rw [groupCohomology.d₀₁_ker_eq_invariants]
              intro g
              apply Additive.ofMul.injective
              exact a.2 g⟩)) := by
  dsimp only
  let M := Rep.ofMulDistribMulAction G A
  let S : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk M.norm.toModuleCatHom (groupCohomology.d₀₁ M)
      (Rep.norm_comp_d_eq_zero M)
  let eSc :
      (tateComplex M).sc 0 ≅ (tateComplex M).sc' (-1) 0 1 :=
    (tateComplex M).isoSc' (-1) 0 1 (by simp) (by simp)
  let eS : (tateComplex M).sc' (-1) 0 1 ≅ S :=
    ShortComplex.isoMk
      (by exact groupHomology.chainsIso₀ M)
      (groupCohomology.cochainsIso₀ M)
      (groupCohomology.cochainsIso₁ M)
      (by
        change
          (groupHomology.chainsIso₀ M).hom ≫ M.norm.toModuleCatHom =
            M.tateNorm ≫ (groupCohomology.cochainsIso₀ M).hom
        rw [Rep.tateNorm]
        simp)
      (groupCohomology.comp_d₀₁_eq M)
  let x : S.moduleCatLeftHomologyData.K := by
    change LinearMap.ker
      (groupCohomology.d₀₁ (Rep.ofMulDistribMulAction G A)).hom
    exact ⟨Additive.ofMul a.1, by
      rw [groupCohomology.d₀₁_ker_eq_invariants]
      intro g
      apply Additive.ofMul.injective
      exact a.2 g⟩
  let y : S.cycles := S.moduleCatCyclesIso.inv x
  have hcycle :
      ShortComplex.cyclesMap eS.hom
          (((tateComplex M).cyclesIsoSc'
            (-1) 0 1 (by simp) (by simp)).hom
            (tateH0FixedCycle a)) =
        y := by
    rw [show
      tateH0FixedCycle a =
        ((tateComplex M).cyclesIsoSc'
          (-1) 0 1 (by simp) (by simp)).inv
          ((ShortComplex.cyclesMapIso eS).inv y) by
      rfl]
    change
      (ShortComplex.cyclesMapIso eS).hom
          (((tateComplex M).cyclesIsoSc'
              (-1) 0 1 (by simp) (by simp)).hom
            (((tateComplex M).cyclesIsoSc'
                (-1) 0 1 (by simp) (by simp)).inv
              ((ShortComplex.cyclesMapIso eS).inv y))) =
        y
    rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  have hIso :
      (TateCohomology.isoZeroBoundary M).hom =
        ((tateComplex M).homologyIsoSc'
            (-1) 0 1 (by simp) (by simp)).hom ≫
          ShortComplex.homologyMap eS.hom := by
    change
      ShortComplex.homologyMap ((eSc ≪≫ eS).hom) =
        ShortComplex.homologyMap eSc.hom ≫
          ShortComplex.homologyMap eS.hom
    rw [Iso.trans_hom, ShortComplex.homologyMap_comp]
  rw [hIso]
  change
    ((((tateComplex M).homologyπ 0 ≫
        ((tateComplex M).homologyIsoSc'
          (-1) 0 1 (by simp) (by simp)).hom) ≫
      ShortComplex.homologyMap eS.hom).hom
        (tateH0FixedCycle a)) =
    S.homologyπ y
  rw [HomologicalComplex.π_homologyIsoSc'_hom]
  rw [Category.assoc, ShortComplex.homologyπ_naturality]
  simp only [ModuleCat.comp_apply]
  exact congrArg (fun z : S.cycles ↦ S.homologyπ z) hcycle

private theorem tateH0IsoHerbrandH0_fixedCycle
    {G A : Type}
    [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (a : fixedSubgroup G A) :
    (tateH0IsoHerbrandH0 (G := G) (A := A)).hom
        ((tateComplex (Rep.ofMulDistribMulAction G A)).homologyπ 0
          (tateH0FixedCycle a)) =
      Additive.ofMul (HerbrandH0.mk a) := by
  let M := Rep.ofMulDistribMulAction G A
  let S : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk M.norm.toModuleCatHom (groupCohomology.d₀₁ M)
      (Rep.norm_comp_d_eq_zero M)
  let x : S.moduleCatLeftHomologyData.K := by
    change LinearMap.ker
      (groupCohomology.d₀₁ (Rep.ofMulDistribMulAction G A)).hom
    exact ⟨Additive.ofMul a.1, by
      rw [groupCohomology.d₀₁_ker_eq_invariants]
      intro g
      apply Additive.ofMul.injective
      exact a.2 g⟩
  let y : S.cycles := S.moduleCatCyclesIso.inv x
  have hz :
      (TateCohomology.isoZeroBoundary M).hom
          ((tateComplex M).homologyπ 0 (tateH0FixedCycle a)) =
        S.homologyπ y := by
    exact isoZeroBoundary_fixedCycle a
  change
    (tateH0IsoHerbrandH0 (G := G) (A := A)).hom
        (show tateCohomology M 0 from
          (tateComplex M).homologyπ 0 (tateH0FixedCycle a)) =
      Additive.ofMul (HerbrandH0.mk a)
  have hy :
      S.moduleCatHomologyIso.hom (S.homologyπ y) =
        S.moduleCatLeftHomologyData.π x := by
    rw [ShortComplex.π_moduleCatCyclesIso_hom_apply]
    rw [show y = S.moduleCatCyclesIso.inv x by rfl,
      Iso.inv_hom_id_apply]
  have hPresentation :
      ∃ eQ : S.moduleCatLeftHomologyData.H ≅
          ModuleCat.of ℤ (Additive (HerbrandH0 G A)),
        tateH0IsoHerbrandH0 (G := G) (A := A) =
            TateCohomology.isoZeroBoundary M ≪≫
              S.moduleCatHomologyIso ≪≫ eQ ∧
          eQ.hom (S.moduleCatLeftHomologyData.π x) =
            Additive.ofMul (HerbrandH0.mk a) := by
    exact ⟨_, rfl, rfl⟩
  obtain ⟨eQ, hIso, hQ⟩ := hPresentation
  calc
    (tateH0IsoHerbrandH0 (G := G) (A := A)).hom
        ((tateComplex M).homologyπ 0 (tateH0FixedCycle a)) =
      (TateCohomology.isoZeroBoundary M ≪≫
        S.moduleCatHomologyIso ≪≫ eQ).hom
          ((tateComplex M).homologyπ 0 (tateH0FixedCycle a)) :=
      congrArg
        (fun e ↦ e.hom
          ((tateComplex M).homologyπ 0 (tateH0FixedCycle a))) hIso
    _ = eQ.hom
        (S.moduleCatHomologyIso.hom
          ((TateCohomology.isoZeroBoundary M).hom
            ((tateComplex M).homologyπ 0 (tateH0FixedCycle a)))) := rfl
    _ = eQ.hom (S.moduleCatHomologyIso.hom (S.homologyπ y)) :=
      congrArg (fun z ↦ eQ.hom (S.moduleCatHomologyIso.hom z)) hz
    _ = eQ.hom (S.moduleCatLeftHomologyData.π x) :=
      congrArg (fun z ↦ eQ.hom z) hy
    _ = Additive.ofMul (HerbrandH0.mk a) := hQ

/-- Ideles whose component at every infinite place lies in the image of
the determinant norm on the corresponding archimedean local tensor
algebra. -/
def allInfinitePlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
  :
    Subgroup (IdeleGroup K) :=
  ⨅ v : InfinitePlace K,
    (Units.map
      (Algebra.norm v.Completion :
        (v.Completion ⊗[K] L) →* v.Completion)).range.comap
      (IdeleGroup.infiniteComponent v)

/-- The simultaneous determinant-norm condition at every finite and
infinite place. -/
def allPlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Subgroup (IdeleGroup K) :=
  allFinitePlaceLocalNormCondition (K := K) (L := L) ⊓
    allInfinitePlaceLocalNormCondition (K := K) (L := L)

/-- Every global relative-idele norm is a local determinant norm at every
place. -/
theorem relativeIdeleNorm_range_le_allPlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (RelativeIdeleGroup.norm K L).range ≤
      allPlaceLocalNormCondition (K := K) (L := L) := by
  intro a ha
  refine ⟨relativeIdeleNorm_range_le_allFinitePlaceLocalNormCondition
      (K := K) (L := L) ha, ?_⟩
  rcases ha with ⟨b, rfl⟩
  rw [allInfinitePlaceLocalNormCondition]
  apply Subgroup.mem_iInf.mpr
  intro v
  exact
    ⟨RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) v b,
      (RelativeIdeleGroup.infiniteComponent_norm
        (K := K) (L := L) v b).symm⟩

/-- An idele is a relative-idele norm exactly when every one of its
finite and infinite components is a determinant norm.  The nontrivial
reverse inclusion uses the restricted-product preimage construction:
integral local preimages are chosen at almost every finite place. -/
theorem relativeIdeleNorm_range_eq_allPlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (RelativeIdeleGroup.norm K L).range =
      allPlaceLocalNormCondition (K := K) (L := L) := by
  apply le_antisymm
  · exact
      relativeIdeleNorm_range_le_allPlaceLocalNormCondition
        (K := K) (L := L)
  · intro a ha
    apply
      (_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms
        (K := K) (L := L) a).2
    constructor
    · intro v
      have hv :
          IdeleGroup.infiniteComponent v a ∈
            (Units.map
              (Algebra.norm v.Completion :
                (v.Completion ⊗[K] L) →* v.Completion)).range := by
        exact
          Subgroup.mem_iInf.mp
            (show
              a ∈ allInfinitePlaceLocalNormCondition
                (K := K) (L := L) from ha.2) v
      simpa [_root_.infiniteTensorNormSubgroup,
        _root_.infiniteTensorDetNorm] using hv
    · intro v
      have hv :
          IdeleGroup.finiteComponent v a ∈
            _root_.chosenFinitePlaceLocalNormSubgroup
              (K := K) (L := L) v := by
        exact
          Subgroup.mem_iInf.mp
            (show
              a ∈ allFinitePlaceLocalNormCondition
                (K := K) (L := L) from ha.1) v
      rw [
        _root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup]
      exact hv

/-- The actual global field-norm subgroup `N_{L/K}(Lˣ)` of `Kˣ`. -/
def globalFieldNormSubgroup
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    :
    Subgroup Kˣ :=
  (Units.map
    (Algebra.norm K : L →* K)).range

/-- Base-field units that are determinant norms at every completion. -/
def everywhereLocalFieldNormSubgroup
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Subgroup Kˣ :=
  (allPlaceLocalNormCondition (K := K) (L := L)).comap
    (IdeleGroup.principalIdele K)

/-- A global field norm is a local norm at every place.  This is the
unconditional direction of the Hasse norm principle. -/
theorem globalFieldNormSubgroup_le_everywhereLocalFieldNormSubgroup
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    globalFieldNormSubgroup K L ≤
      everywhereLocalFieldNormSubgroup K L := by
  rintro x ⟨y, rfl⟩
  change
    IdeleGroup.principalIdele K
        (Units.map
          (Algebra.norm K : L →* K) y) ∈
      allPlaceLocalNormCondition (K := K) (L := L)
  rw [← RelativeIdeleGroup.norm_principalIdele K L y]
  exact
    relativeIdeleNorm_range_le_allPlaceLocalNormCondition
      (K := K) (L := L) ⟨_, rfl⟩

/-- The map
`H⁰(G, P_L) → H⁰(G, I_L)` induced by the actual inclusion of principal
relative ideles. -/
noncomputable def principalIdeleHerbrandH0Map
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    letI :=
      RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
    HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) →*
      HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup K L) := by
  letI :=
    RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
  letI :=
    RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
  let f :=
    equivariantRepHom
      (RelativeIdeleGroup.principalSubgroup K L).subtype
      (RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant K L)
  let eP :=
    (tateH0IsoHerbrandH0
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.principalSubgroup K L)).toLinearEquiv
      |>.toAddEquiv.toMultiplicative
  let eI :=
    (tateH0IsoHerbrandH0
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup K L)).toLinearEquiv
      |>.toAddEquiv.toMultiplicative
  exact eI.toMonoidHom.comp <|
    ((tateCohomologyFunctor 0).map f).hom.toAddMonoidHom.toMultiplicative.comp
      eP.symm.toMonoidHom

private theorem principalIdeleHerbrandH0Map_mk
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    letI :=
      RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
    ∀ a : fixedSubgroup (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L),
      principalIdeleHerbrandH0Map K L (HerbrandH0.mk a) =
        HerbrandH0.mk
          (⟨(RelativeIdeleGroup.principalSubgroup K L).subtype a,
            fun σ ↦ by
              rw [← RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant
                K L σ a, a.2 σ]⟩ :
            fixedSubgroup (L ≃ₐ[K] L) (RelativeIdeleGroup K L)) := by
  let :=
    RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
  intro a
  let aI :
      fixedSubgroup (L ≃ₐ[K] L) (RelativeIdeleGroup K L) :=
    ⟨(RelativeIdeleGroup.principalSubgroup K L).subtype a, fun σ ↦ by
      rw [← RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant
        K L σ a, a.2 σ]⟩
  let f :=
    equivariantRepHom
      (RelativeIdeleGroup.principalSubgroup K L).subtype
      (RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant K L)
  let eP :=
    (tateH0IsoHerbrandH0
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.principalSubgroup K L)).toLinearEquiv.toAddEquiv
  let eI :=
    (tateH0IsoHerbrandH0
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup K L)).toLinearEquiv.toAddEquiv
  let cP :
      tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.principalSubgroup K L)) 0 :=
    (tateComplex
        (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
          (RelativeIdeleGroup.principalSubgroup K L))).homologyπ 0
      (tateH0FixedCycle a)
  let cI :
      tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup K L)) 0 :=
    (tateComplex
        (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
          (RelativeIdeleGroup K L))).homologyπ 0
      (tateH0FixedCycle aI)
  have hPe : eP cP = Additive.ofMul (HerbrandH0.mk a) :=
    tateH0IsoHerbrandH0_fixedCycle a
  have hIe : eI cI = Additive.ofMul (HerbrandH0.mk aI) :=
    tateH0IsoHerbrandH0_fixedCycle aI
  have hc :
      ((tateCohomologyFunctor 0).map f).hom cP = cI := by
    dsimp only [cP, cI]
    change
      ((((tateComplex
            (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
              (RelativeIdeleGroup.principalSubgroup K L))).homologyπ 0) ≫
          HomologicalComplex.homologyMap (tateComplex.map f) 0).hom
        (tateH0FixedCycle a)) =
        (tateComplex
            (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
              (RelativeIdeleGroup K L))).homologyπ 0
          (tateH0FixedCycle aI)
    rw [HomologicalComplex.homologyπ_naturality]
    simp only [ModuleCat.comp_apply]
    exact congrArg
      (fun z ↦
        (tateComplex
            (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
              (RelativeIdeleGroup K L))).homologyπ 0 z)
      (by
        simpa only [f, aI] using
          tateH0FixedCycle_map
            (G := L ≃ₐ[K] L)
            (RelativeIdeleGroup.principalSubgroup K L).subtype
            (RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant
              K L)
            a)
  have hadd :
    eI
        (((tateCohomologyFunctor 0).map f).hom
          (eP.symm
            (Additive.ofMul (HerbrandH0.mk a) :
              Additive
                (HerbrandH0 (L ≃ₐ[K] L)
                  (RelativeIdeleGroup.principalSubgroup K L))))) =
      (Additive.ofMul (HerbrandH0.mk aI) :
        Additive (HerbrandH0 (L ≃ₐ[K] L) (RelativeIdeleGroup K L))) := by
    rw [← hPe, eP.symm_apply_apply, ← hIe]
    exact congrArg eI hc
  change
    Additive.toMul
        (eI (((tateCohomologyFunctor 0).map f).hom
          (eP.symm
            (Additive.ofMul (HerbrandH0.mk a) :
              Additive
                (HerbrandH0 (L ≃ₐ[K] L)
                  (RelativeIdeleGroup.principalSubgroup K L)))))) =
      HerbrandH0.mk aI
  exact congrArg Additive.toMul hadd

section IdeleClassConnecting

attribute [local instance]
  RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction
  RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction
  RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction

/-- The low-degree connecting homomorphism
`H⁻¹(G, C_L) → H⁰(G, P_L)` attached to
`1 → P_L → I_L → C_L → 1`. -/
noncomputable def ideleClassToPrincipalConnecting
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    letI :=
      RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    Multiplicative
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1)) →*
      HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) := by
  let q :
      RelativeIdeleGroup K L →*
        RelativeIdeleGroup.ClassGroup K L :=
    QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K L)
  have hqEquivariant :
      ∀ (τ : L ≃ₐ[K] L) (a : RelativeIdeleGroup K L),
        q (τ • a) = τ • q a :=
    RelativeIdeleGroup.Cohomology.ideleClassQuotientMap_equivariant K L
  have hqExact :
      ∀ a : RelativeIdeleGroup K L,
        q a = 1 ↔
          ∃ p : RelativeIdeleGroup.principalSubgroup K L,
            (RelativeIdeleGroup.principalSubgroup K L).subtype p = a :=
    RelativeIdeleGroup.Cohomology.principalIdele_ideleClass_exact K L
  have hqSurjective : Function.Surjective q :=
    QuotientGroup.mk'_surjective
      (RelativeIdeleGroup.principalSubgroup K L)
  let S :=
    equivariantShortComplex
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.principalSubgroup K L)
      (B := RelativeIdeleGroup K L)
      (C := RelativeIdeleGroup.ClassGroup K L)
      (i := (RelativeIdeleGroup.principalSubgroup K L).subtype)
      (j := q)
      (hi := RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant K L)
      (hj := hqEquivariant)
      (hker := hqExact)
  have hS : S.ShortExact :=
    equivariantShortComplex_shortExact
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.principalSubgroup K L)
      (B := RelativeIdeleGroup K L)
      (C := RelativeIdeleGroup.ClassGroup K L)
      (i := (RelativeIdeleGroup.principalSubgroup K L).subtype)
      (j := q)
      (hi := RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant K L)
      (hj := hqEquivariant)
      (hker := hqExact)
      (hinj := (RelativeIdeleGroup.principalSubgroup K L).subtype_injective)
      (hsurj := hqSurjective)
  let eP :=
    (tateH0IsoHerbrandH0
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.principalSubgroup K L)).toLinearEquiv
      |>.toAddEquiv.toMultiplicative
  exact eP.toMonoidHom.comp <|
    (TateCohomology.δ hS (-1)).hom.toAddMonoidHom.toMultiplicative

/-- Exactness of the concrete low-degree sequence: the image of
`H⁻¹(G,C_L)` is precisely the kernel of
`H⁰(G,P_L) → H⁰(G,I_L)`. -/
theorem ideleClassToPrincipalConnecting_range_eq_ker
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    letI :=
      RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    MonoidHom.range (ideleClassToPrincipalConnecting K L) =
      MonoidHom.ker (principalIdeleHerbrandH0Map K L) := by
  let q :
      RelativeIdeleGroup K L →*
        RelativeIdeleGroup.ClassGroup K L :=
    QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K L)
  have hqEquivariant :
      ∀ (τ : L ≃ₐ[K] L) (a : RelativeIdeleGroup K L),
        q (τ • a) = τ • q a :=
    RelativeIdeleGroup.Cohomology.ideleClassQuotientMap_equivariant K L
  have hqExact :
      ∀ a : RelativeIdeleGroup K L,
        q a = 1 ↔
          ∃ p : RelativeIdeleGroup.principalSubgroup K L,
            (RelativeIdeleGroup.principalSubgroup K L).subtype p = a :=
    RelativeIdeleGroup.Cohomology.principalIdele_ideleClass_exact K L
  have hqSurjective : Function.Surjective q :=
    QuotientGroup.mk'_surjective
      (RelativeIdeleGroup.principalSubgroup K L)
  let S :=
    equivariantShortComplex
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.principalSubgroup K L)
      (B := RelativeIdeleGroup K L)
      (C := RelativeIdeleGroup.ClassGroup K L)
      (i := (RelativeIdeleGroup.principalSubgroup K L).subtype)
      (j := q)
      (hi := RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant K L)
      (hj := hqEquivariant)
      (hker := hqExact)
  have hS : S.ShortExact :=
    equivariantShortComplex_shortExact
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.principalSubgroup K L)
      (B := RelativeIdeleGroup K L)
      (C := RelativeIdeleGroup.ClassGroup K L)
      (i := (RelativeIdeleGroup.principalSubgroup K L).subtype)
      (j := q)
      (hi := RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant K L)
      (hj := hqEquivariant)
      (hker := hqExact)
      (hinj := (RelativeIdeleGroup.principalSubgroup K L).subtype_injective)
      (hsurj := hqSurjective)
  let δm :=
    (TateCohomology.δ hS (-1)).hom.toAddMonoidHom.toMultiplicative
  let fm :=
    ((tateCohomologyFunctor 0).map S.f).hom.toAddMonoidHom.toMultiplicative
  let eP :=
    (tateH0IsoHerbrandH0
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.principalSubgroup K L)).toLinearEquiv
      |>.toAddEquiv.toMultiplicative
  let eI :=
    (tateH0IsoHerbrandH0
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup K L)).toLinearEquiv
      |>.toAddEquiv.toMultiplicative
  let connecting := eP.toMonoidHom.comp δm
  let principal :=
    eI.toMonoidHom.comp (fm.comp eP.symm.toMonoidHom)
  have hbase : Function.MulExact δm fm := by
    apply
      CyclicCohomology.ProfiniteCohomology.Herbrand.mulExact_of_moduleCat_shortComplex_exact
    · simpa using TateCohomology.exact₁ hS (-1)
  have htarget : Function.MulExact connecting principal := by
    exact
      mulExact_transport_mulEquiv δm fm eP eI hbase
  change MonoidHom.range connecting = MonoidHom.ker principal
  exact htarget.monoidHom_ker_eq.symm

end IdeleClassConnecting

/-- Degree-zero Tate cohomology of the actual field-unit action is the
concrete global norm quotient `Kˣ / N_{L/K}(Lˣ)`. -/
noncomputable def fieldUnitsHerbrandH0EquivGlobalNormQuotient
    (K L : Type)
    [Field K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    letI :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    HerbrandH0 (L ≃ₐ[K] L) Lˣ ≃*
      Kˣ ⧸ globalFieldNormSubgroup K L := by
  letI :=
    LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
  let eTate :
      (CyclicCohomology.unitsInvariantSubmodule K L ⧸
        CyclicCohomology.unitsTateH0NormSubmodule K L) ≃+
        tateCohomology
          (Rep.ofAlgebraAutOnUnits K L) 0 :=
    (CyclicCohomology.tateUnitsH0IsoInvariantsQuotient
      K L).symm.toLinearEquiv.toAddEquiv
  let e₀ :=
    (LocalClassFieldTheory.herbrandH0MulEquivInvariantsNormQuotient
      K L).trans eTate.toMultiplicative
  let e₁ :
      tateCohomology
          (Rep.ofAlgebraAutOnUnits K L) 0 ≃+
        Additive (LocalFieldTheory.NormQuotient K L) :=
    (CyclicCohomology.H0TateUnitsIsoNormQuotient
      K L).toLinearEquiv.toAddEquiv
  exact
    e₀.trans <|
      e₁.toMultiplicative.trans <|
        (MulEquiv.multiplicativeAdditive
          (LocalFieldTheory.NormQuotient K L)).trans <|
            LocalFieldTheory.normQuotientEquivOfSubgroupEq
              K L (globalFieldNormSubgroup K L) rfl

/-- The map on degree-zero Tate cohomology induced by the actual diagonal
embedding `Lˣ → I_L`. -/
noncomputable def fieldUnitsToRelativeIdeleHerbrandH0
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    letI :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
    HerbrandH0 (L ≃ₐ[K] L) Lˣ →*
      HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup K L) := by
  letI :=
    LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
  letI :=
    RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
  letI :=
    RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
  exact
    (principalIdeleHerbrandH0Map K L).comp
      (fieldUnitsHerbrandH0EquivPrincipalIdeles
        K L).toMonoidHom

/-- A base-field unit, regarded as a Galois-fixed unit of the extension
field. -/
noncomputable def baseFieldUnitAsFixedUnit
    (K L : Type)
    [Field K]
    [Field L] [Algebra K L]
    (x : Kˣ) :
    letI :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    fixedSubgroup (L ≃ₐ[K] L) Lˣ := by
  letI :=
    LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
  refine
    ⟨Units.map (algebraMap K L) x, ?_⟩
  intro σ
  apply Units.ext
  simp

/-- If the principal idele of a base-field unit is an actual relative
idele norm, its field-unit Tate class maps trivially to relative-idele
Tate cohomology. -/
theorem fieldUnitsHerbrandH0_map_baseFieldUnit_eq_one_of_mem_norm
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (x : Kˣ)
    (hx :
      IdeleGroup.principalIdele K x ∈
        (RelativeIdeleGroup.norm K L).range) :
    letI :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
    fieldUnitsToRelativeIdeleHerbrandH0 K L
        (HerbrandH0.mk (baseFieldUnitAsFixedUnit K L x)) = 1 := by
  let :=
    LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
  let aP :
      fixedSubgroup (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) :=
    CyclicCohomology.fixedSubgroupEquivariantMulEquiv
      (fieldUnitsEquivPrincipalIdeles K L)
      (fieldUnitsEquivPrincipalIdeles_smul K L)
      (baseFieldUnitAsFixedUnit K L x)
  let aI :
      fixedSubgroup (L ≃ₐ[K] L) (RelativeIdeleGroup K L) :=
    ⟨(RelativeIdeleGroup.principalSubgroup K L).subtype aP, fun σ ↦ by
      rw [← RelativeIdeleGroup.Cohomology.principalIdeleSubtype_equivariant
        K L σ aP, aP.2 σ]⟩
  have hmk : HerbrandH0.mk aI = 1 := by
    apply (HerbrandH0.mk_eq_one_iff aI).2
    obtain ⟨z, hz⟩ := hx
    refine ⟨z, ?_⟩
    change
      tateNorm (L ≃ₐ[K] L) (RelativeIdeleGroup K L) z =
        (aI : RelativeIdeleGroup K L)
    dsimp only [aP,
      aI,
      CyclicCohomology.fixedSubgroupEquivariantMulEquiv,
      fieldUnitsEquivPrincipalIdeles]
    rw [RelativeIdeleGroup.Cohomology.relativeIdele_tateNorm_eq_inclusion_norm,
      hz, RelativeIdeleGroup.inclusion_principalIdele]
    rfl
  have hmap :
      fieldUnitsToRelativeIdeleHerbrandH0 K L
          (HerbrandH0.mk (baseFieldUnitAsFixedUnit K L x)) =
        HerbrandH0.mk aI := by
    have hfield :
        fieldUnitsHerbrandH0EquivPrincipalIdeles K L
            (HerbrandH0.mk (baseFieldUnitAsFixedUnit K L x)) =
          HerbrandH0.mk aP := by
      simpa only [fieldUnitsHerbrandH0EquivPrincipalIdeles, aP] using
        CyclicCohomology.herbrandH0EquivariantMulEquiv_mk
          (fieldUnitsEquivPrincipalIdeles K L)
          (fieldUnitsEquivPrincipalIdeles_smul K L)
          (baseFieldUnitAsFixedUnit K L x)
    change
      principalIdeleHerbrandH0Map K L
          (fieldUnitsHerbrandH0EquivPrincipalIdeles K L
            (HerbrandH0.mk (baseFieldUnitAsFixedUnit K L x))) =
        HerbrandH0.mk aI
    rw [hfield]
    simpa only [aI] using
      principalIdeleHerbrandH0Map_mk K L aP
  exact hmap.trans hmk

/-- The connecting map in the low-degree sequence, with its target
transported from principal ideles back to the actual field-unit
cohomology. -/
noncomputable def ideleClassToFieldUnitsConnecting
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    letI :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    Multiplicative
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1)) →*
      HerbrandH0 (L ≃ₐ[K] L) Lˣ := by
  letI :=
    LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
  letI :=
    RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
  letI :=
    RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
  letI :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  exact
    (fieldUnitsHerbrandH0EquivPrincipalIdeles
      K L).symm.toMonoidHom.comp
        (ideleClassToPrincipalConnecting K L)

/-- Exactness after replacing `H⁰(G,P_L)` by the canonically equivalent
field-unit cohomology `H⁰(G,Lˣ)`. -/
theorem ideleClassToFieldUnitsConnecting_range_eq_ker
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    letI :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    MonoidHom.range
        (ideleClassToFieldUnitsConnecting K L) =
      MonoidHom.ker
        (fieldUnitsToRelativeIdeleHerbrandH0 K L) := by
  let :=
    LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  let e :=
    fieldUnitsHerbrandH0EquivPrincipalIdeles K L
  ext q
  constructor
  · rintro ⟨c, rfl⟩
    change
      principalIdeleHerbrandH0Map K L
          (e (e.symm
            (ideleClassToPrincipalConnecting K L c))) = 1
    rw [e.apply_symm_apply]
    exact
      (ideleClassToPrincipalConnecting_range_eq_ker
        K L).le
        ⟨c, rfl⟩
  · intro hq
    change
      principalIdeleHerbrandH0Map K L (e q) = 1 at hq
    have heq :
        e q ∈
          MonoidHom.range
            (ideleClassToPrincipalConnecting K L) := by
      rw [ideleClassToPrincipalConnecting_range_eq_ker K L]
      exact hq
    obtain ⟨c, hc⟩ := heq
    refine ⟨c, ?_⟩
    change e.symm
        (ideleClassToPrincipalConnecting K L c) = q
    rw [hc, e.symm_apply_apply]

/-- Vanishing of `H⁻¹(G,C_L)` makes the diagonal map from field-unit
cohomology to idele cohomology injective. -/
theorem fieldUnitsToRelativeIdeleHerbrandH0_injective_of_subsingleton
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Subsingleton
      (letI :=
        RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
      Multiplicative
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1)))] :
    letI :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
    Function.Injective
      (fieldUnitsToRelativeIdeleHerbrandH0 K L) := by
  let :=
    LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [← ideleClassToFieldUnitsConnecting_range_eq_ker K L]
  ext q
  constructor
  · rintro ⟨c, rfl⟩
    have hc : c = 1 := Subsingleton.elim c 1
    subst c
    simp
  · intro hq
    have hqOne : q = 1 := Subgroup.mem_bot.mp hq
    subst q
    exact ⟨1, map_one _⟩

/-- Vanishing of `H⁻¹(G,C_L)` gives the reverse inclusion in the Hasse norm
principle through the concrete low-degree sequence. -/
theorem everywhereLocalFieldNormSubgroup_le_global_of_subsingleton
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Subsingleton
      (letI :=
        RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
      Multiplicative
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1)))] :
    everywhereLocalFieldNormSubgroup K L ≤
      globalFieldNormSubgroup K L := by
  let :=
    LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  intro x hx
  have hxNorm :
      IdeleGroup.principalIdele K x ∈
        (RelativeIdeleGroup.norm K L).range := by
    rw [
      relativeIdeleNorm_range_eq_allPlaceLocalNormCondition
        (K := K) (L := L)]
    exact hx
  let q : HerbrandH0 (L ≃ₐ[K] L) Lˣ :=
    HerbrandH0.mk (baseFieldUnitAsFixedUnit K L x)
  have hqMap :
      fieldUnitsToRelativeIdeleHerbrandH0 K L q = 1 :=
    fieldUnitsHerbrandH0_map_baseFieldUnit_eq_one_of_mem_norm
      K L x hxNorm
  have hq : q = 1 := by
    apply
      fieldUnitsToRelativeIdeleHerbrandH0_injective_of_subsingleton
        K L
    simpa using hqMap
  have hxTate :
      (baseFieldUnitAsFixedUnit K L x : Lˣ) ∈
        tateNormSubgroup (L ≃ₐ[K] L) Lˣ :=
    (HerbrandH0.mk_eq_one_iff
      (baseFieldUnitAsFixedUnit K L x)).1 hq
  obtain ⟨y, hy⟩ := hxTate
  refine ⟨y, ?_⟩
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective K L
  change
    algebraMap K L
        ((Units.map (Algebra.norm K : L →* K) y : Kˣ) : K) =
      algebraMap K L (x : K)
  have hUnits :
      Units.map (algebraMap K L).toMonoidHom
          (Units.map (Algebra.norm K : L →* K) y) =
        Units.map (algebraMap K L).toMonoidHom x := by
    calc
      Units.map (algebraMap K L).toMonoidHom
          (Units.map (Algebra.norm K : L →* K) y) =
          ∏ τ : L ≃ₐ[K] L,
            Units.map τ.toRingEquiv.toMonoidHom y :=
        RelativeIdeleGroup.fieldNormUnits_eq_prod_conjugates K L y
      _ = tateNorm (L ≃ₐ[K] L) Lˣ y := rfl
      _ = (baseFieldUnitAsFixedUnit K L x : Lˣ) := hy
      _ = Units.map (algebraMap K L).toMonoidHom x := rfl
  exact congrArg Units.val hUnits

/-- The concrete diagonal local-norm map.  Its source is the global norm
quotient, while its target kills precisely those ideles satisfying every
local norm condition. -/
noncomputable def hasseNormDiagonal
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Kˣ ⧸ globalFieldNormSubgroup K L →*
      IdeleGroup K ⧸ allPlaceLocalNormCondition (K := K) (L := L) :=
  QuotientGroup.map
    (globalFieldNormSubgroup K L)
    (allPlaceLocalNormCondition (K := K) (L := L))
    (IdeleGroup.principalIdele K)
    globalFieldNormSubgroup_le_everywhereLocalFieldNormSubgroup

/-- The Hasse norm diagonal sends the class of a field unit to the class
of its principal idele. -/
theorem hasseNormDiagonal_mk
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (x : Kˣ) :
    hasseNormDiagonal K L
        (QuotientGroup.mk' (globalFieldNormSubgroup K L) x) =
      QuotientGroup.mk'
        (allPlaceLocalNormCondition (K := K) (L := L))
        (IdeleGroup.principalIdele K x) :=
  rfl

/-- Injectivity of the concrete diagonal is exactly the missing
local-to-global inclusion. -/
theorem hasseNormDiagonal_injective_iff
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Function.Injective (hasseNormDiagonal K L) ↔
      everywhereLocalFieldNormSubgroup K L ≤
        globalFieldNormSubgroup K L := by
  constructor
  · intro hinj x hx
    have hdiag :
        hasseNormDiagonal K L
            (QuotientGroup.mk'
              (globalFieldNormSubgroup K L) x) =
          hasseNormDiagonal K L 1 := by
      rw [map_one, hasseNormDiagonal_mk]
      exact
        (QuotientGroup.eq_one_iff
          (IdeleGroup.principalIdele K x)).2 hx
    have hq :
        QuotientGroup.mk' (globalFieldNormSubgroup K L) x = 1 :=
      hinj hdiag
    exact (QuotientGroup.eq_one_iff x).1 hq
  · intro hlocal
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro q hq
      refine QuotientGroup.induction_on q ?_ hq
      intro x hx
      have hxlocal :
          x ∈ everywhereLocalFieldNormSubgroup K L := by
        exact
          (QuotientGroup.eq_one_iff
            (IdeleGroup.principalIdele K x)).1 hx
      change
        QuotientGroup.mk'
            (globalFieldNormSubgroup K L) x = 1
      exact (QuotientGroup.eq_one_iff x).2 (hlocal hxlocal)
    · exact bot_le

/-- Equivalent subgroup formulation of the Hasse norm principle. -/
theorem hasseNormDiagonal_injective_iff_subgroup_eq
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Function.Injective (hasseNormDiagonal K L) ↔
      globalFieldNormSubgroup K L =
        everywhereLocalFieldNormSubgroup K L := by
  rw [hasseNormDiagonal_injective_iff]
  exact
    ⟨fun h => le_antisymm
        globalFieldNormSubgroup_le_everywhereLocalFieldNormSubgroup h,
      fun h => h ▸ le_rfl⟩

/-- Degree-minus-one Tate-cohomology vanishing makes the concrete diagonal
local-norm map injective. -/
theorem hasseNormDiagonal_injective_of_subsingleton
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Subsingleton
      (letI :=
        RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
      Multiplicative
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1)))] :
    Function.Injective (hasseNormDiagonal K L) :=
  hasseNormDiagonal_injective_iff.mpr
    (everywhereLocalFieldNormSubgroup_le_global_of_subsingleton
      K L)

/-- Hasse's norm theorem as equality of the actual global norm subgroup
and the subgroup of elements that are norms at every place. -/
theorem hasseNormPrinciple_of_subsingleton
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Subsingleton
      (letI :=
        RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
      Multiplicative
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1)))] :
    globalFieldNormSubgroup K L =
      everywhereLocalFieldNormSubgroup K L :=
  (hasseNormDiagonal_injective_iff_subgroup_eq.mp
    (hasseNormDiagonal_injective_of_subsingleton K L))

/-- For a finite cyclic extension, the concrete diagonal from the global
field-norm quotient to the simultaneous local norm quotient is injective.
The cyclic idele-class calculation supplies the required degree-minus-one
Tate-cohomology vanishing. -/
theorem hasseNormDiagonal_injective_cyclic
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    Function.Injective (hasseNormDiagonal K L) := by
  obtain ⟨sigma, hsigma⟩ :=
    IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  let :
      Subsingleton
        (Multiplicative
          (tateCohomology
            (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)) (-1))) :=
    ideleClass_tateHMinusOne_subsingleton_cyclic
      K L sigma hsigma
  exact hasseNormDiagonal_injective_of_subsingleton K L

/-- Hasse's norm theorem for a finite cyclic extension: an element of
`Kˣ` is a global norm from `L` exactly when it is a norm at every place. -/
theorem hasseNormPrinciple_cyclic
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    globalFieldNormSubgroup K L =
      everywhereLocalFieldNormSubgroup K L :=
  hasseNormDiagonal_injective_iff_subgroup_eq.mp
    (hasseNormDiagonal_injective_cyclic K L)

end GlobalClassFieldTheory.ClassFieldAxiom
