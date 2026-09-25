/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Core
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.Continuity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.FiniteRamifiedPrimes
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness
public import Mathlib.Algebra.BigOperators.Finprod
/-!
# The finite-place product of local Artin homomorphisms

For a finite abelian extension of number fields `L / K`, the local
Artin factors of an idele are trivial at all but finitely many finite
places.  This file forms their `finprod` directly in the actual global
Galois group.
-/

@[expose] public section

open scoped IsMulCommutative NumberField NNReal ValuativeRel
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open Function

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

open scoped Classical in
/-- A finitely supported product may be regrouped over the fibers of an
arbitrary indexing map. -/
theorem finprod_fibers_eq_sigma
    {α β G : Type*} [CommMonoid G]
    (g : α → β) (f : α → G)
    (hf : HasFiniteMulSupport f) :
    (∏ᶠ b : β,
        ∏ᶠ x : {x : α // g x = b}, f x.1) =
      ∏ᶠ x : α, f x := by
  classical
  let s := hf.toFinset
  have hFiber (b : β) :
      (∏ᶠ x : {x : α // g x = b}, f x.1) =
        ∏ x ∈ s with g x = b, f x := by
    rw [finprod_eq_prod_of_mulSupport_subset
      (fun x : {x : α // g x = b} => f x.1)
      (s := s.subtype fun x => g x = b)]
    · simp only [Finset.prod_subtype_eq_prod_filter]
    · intro x hx
      change x ∈ s.subtype (fun x => g x = b)
      change f x.1 ≠ 1 at hx
      exact Finset.mem_subtype.mpr (hf.mem_toFinset.2 hx)
  calc
    (∏ᶠ b : β,
        ∏ᶠ x : {x : α // g x = b}, f x.1) =
        ∏ᶠ b : β,
          ∏ x ∈ s with g x = b, f x :=
      finprod_congr hFiber
    _ = ∏ x ∈ s, f x := by
      rw [finprod_eq_prod_of_mulSupport_subset _
        (s.mulSupport_of_fiberwise_prod_subset_image f g)]
      exact
        Finset.prod_fiberwise_of_maps_to
          (t := s.image g)
          (fun x hx => Finset.mem_image_of_mem g hx) f
    _ = ∏ᶠ x : α, f x :=
      (finprod_eq_prod f hf).symm

open scoped Classical in
/-- A local norm of an integral unit at a finite place is again an
integral unit at the place below. -/
theorem normUnits_mem_finitePlaceIntegerUnits
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) M)
    (x :
      ((finitePlaceExtensionCentre
        (K := K) (L := M) v w).adicCompletion M)ˣ)
    (hx :
      x ∈
        ((finitePlaceExtensionCentre
          (K := K) (L := M) v w).adicCompletionIntegers M).units) :
    letI : Algebra (v.adicCompletion K)
        ((finitePlaceExtensionCentre
          (K := K) (L := M) v w).adicCompletion M) :=
      (finitePlaceAdicCompletionMap K M v
        ⟨finitePlaceExtensionCentre (K := K) (L := M) v w,
          finitePlaceBelow_finitePlaceExtensionCentre
            (K := K) (L := M) v w⟩).toAlgebra
    LocalFieldTheory.normUnits
        (v.adicCompletion K)
        ((finitePlaceExtensionCentre
          (K := K) (L := M) v w).adicCompletion M) x ∈
      (v.adicCompletionIntegers K).units := by
  let W : {W : HeightOneSpectrum (𝓞 M) //
      _root_.finitePlaceBelow (K := K) W = v} :=
    ⟨finitePlaceExtensionCentre (K := K) (L := M) v w,
      finitePlaceBelow_finitePlaceExtensionCentre
        (K := K) (L := M) v w⟩
  let : Algebra (v.adicCompletion K)
      ((finitePlaceExtensionCentre
        (K := K) (L := M) v w).adicCompletion M) :=
    (finitePlaceAdicCompletionMap K M v W).toAlgebra
  let z : (W.1.adicCompletionIntegers M).units := ⟨x, hx⟩
  simpa only [W, z, Subgroup.coe_subtype] using
    IdeleGroup.finitePlace_normUnits_mem_integerUnits
      (K := K) (L := M) v W z

open scoped Classical in
/-- The finite local Artin factors of an idele have finite multiplicative
support.  This is the support input for applying homomorphisms to the
finite-place global Artin product. -/
theorem finitePlaceArtinFactors_hasFiniteMulSupport
    (a : IdeleGroup K) :
    HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) =>
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.finiteComponent v a)) := by
  let S : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | a.2 v ∉ (v.adicCompletionIntegers K).units}
  let T : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | ∃ W : HeightOneSpectrum (𝓞 L),
      W.asIdeal.LiesOver v.asIdeal ∧
        ¬ Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal}
  have hS : S.Finite :=
    Filter.eventually_cofinite.mp
      (FiniteIdeleGroup.eventually_mem_localUnits a.2)
  have hT : T.Finite :=
    AlgebraicNumberTheory.Ramification.finite_ramified_base_heightOne_primes
      (𝓞 K) (𝓞 L)
  rw [HasFiniteMulSupport]
  apply (hS.union hT).subset
  rw [mulSupport_subset_iff']
  intro v hv
  have hvS : v ∉ S := by
    intro hvS
    exact hv (Set.mem_union_left T hvS)
  have hvT : v ∉ T := by
    intro hvT
    exact hv (Set.mem_union_right S hvT)
  have hNorm :
      IdeleGroup.finiteComponent v a ∈
        chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v := by
    apply
      adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v
        (chosenFinitePlaceIsUnramified_of_isUnramifiedAt
          (K := K) (L := L) v (by
            by_contra hram
            apply hvT
            change
              ∃ W : HeightOneSpectrum (𝓞 L),
                W.asIdeal.LiesOver v.asIdeal ∧
                  ¬ Algebra.IsUnramifiedAt
                    (𝓞 K) W.asIdeal
            exact
              ⟨finitePlaceExtensionCentre
                  (K := K) (L := L) v
                  (chosenFinitePlaceExtension
                    (L := L) v),
                finitePlaceExtensionCentre_liesOver
                  (K := K) (L := L) v
                  (chosenFinitePlaceExtension
                    (L := L) v),
                hram⟩))
    simpa only [S, Set.mem_ofPred_eq, not_not,
      IdeleGroup.finiteComponent_apply] using hvS
  rw [← chosenFinitePlaceArtinMonoidHom_ker
    (K := K) (L := L) v] at hNorm
  exact MonoidHom.mem_ker.mp hNorm

open scoped Classical in
/-- At an unramified finite place, the chosen local Artin map kills
integral idele components. -/
theorem chosenFinitePlaceArtinMonoidHom_eq_one_of_integral_of_unramifiedAt
    (v : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup K)
    (ha :
      IdeleGroup.finiteComponent v a ∈
        (v.adicCompletionIntegers K).units)
    (hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension
            (L := L) v)).asIdeal) :
    chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (IdeleGroup.finiteComponent v a) = 1 := by
  have hNorm :
      IdeleGroup.finiteComponent v a ∈
        chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v := by
    apply
      adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v
        (chosenFinitePlaceIsUnramified_of_isUnramifiedAt
          (K := K) (L := L) v hunram)
    exact ha
  rw [← chosenFinitePlaceArtinMonoidHom_ker
    (K := K) (L := L) v] at hNorm
  exact MonoidHom.mem_ker.mp hNorm

open scoped Classical in
private theorem chosenFinitePlaceArtinMonoidHom_eq_one_of_mem_localNorm
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (hx : x ∈ chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v) :
    chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v x = 1 := by
  rw [← chosenFinitePlaceArtinMonoidHom_ker
    (K := K) (L := L) v] at hx
  exact MonoidHom.mem_ker.mp hx

open scoped Classical in
/-- The product over all finite places of the actual local Artin
homomorphisms.  Its value on an idele is a finite product because the
idele is locally integral almost everywhere and the extension is
unramified away from a finite set. -/
noncomputable def finitePlaceGlobalArtinMonoidHom :
    IdeleGroup K →* (L ≃ₐ[K] L) where
  toFun a :=
    ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (IdeleGroup.finiteComponent v a)
  map_one' := by
    simp only [map_one]
    exact finprod_one
  map_mul' a b := by
    simp only [map_mul]
    exact
      finprod_mul_distrib
        (finitePlaceArtinFactors_hasFiniteMulSupport
          (K := K) (L := L) a)
        (finitePlaceArtinFactors_hasFiniteMulSupport
          (K := K) (L := L) b)

open scoped Classical in
/-- The finite-place global Artin homomorphism is continuous for the
restricted-product topology on ideles and the finite Krull topology on
the Galois group. -/
theorem finitePlaceGlobalArtinMonoidHom_continuous :
    Continuous
      (finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)) := by
  classical
  let T : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | ∃ W : HeightOneSpectrum (𝓞 L),
      W.asIdeal.LiesOver v.asIdeal ∧
        ¬ Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal}
  have hT : T.Finite :=
    AlgebraicNumberTheory.Ramification.finite_ramified_base_heightOne_primes
      (𝓞 K) (𝓞 L)
  let S : Finset (HeightOneSpectrum (𝓞 K)) :=
    hT.toFinset
  let U : Set (IdeleGroup K) :=
    (IdeleGroup.supportedAt (K := K) (S : Set _) : Set _) ∩
      {a | ∀ v ∈ S,
        IdeleGroup.finiteComponent v a ∈
          chosenFinitePlaceLocalNormSubgroup
            (K := K) (L := L) v}
  have hUopen : IsOpen U := by
    have hLocalOpen : IsOpen
        {a : IdeleGroup K | ∀ v ∈ S,
          IdeleGroup.finiteComponent v a ∈
            chosenFinitePlaceLocalNormSubgroup
              (K := K) (L := L) v} := by
      rw [show
        {a : IdeleGroup K | ∀ v ∈ S,
          IdeleGroup.finiteComponent v a ∈
            chosenFinitePlaceLocalNormSubgroup
              (K := K) (L := L) v} =
          ⋂ v ∈ S,
            (IdeleGroup.finiteComponent v) ⁻¹'
              (chosenFinitePlaceLocalNormSubgroup
                (K := K) (L := L) v : Set _) by
        ext a
        simp]
      exact isOpen_biInter_finset fun v _ =>
        (chosenFinitePlaceLocalNormSubgroup_isOpen
          (K := K) (L := L) v).preimage
            (IdeleGroup.finiteComponentContinuous v).continuous
    exact (IdeleGroup.isOpen_supportedAt S).inter hLocalOpen
  have hUone : (1 : IdeleGroup K) ∈ U := by
    constructor
    · exact (IdeleGroup.supportedAt
        (K := K) (S : Set _)).one_mem
    · intro v _
      rw [map_one]
      exact
        (chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v).one_mem
  have hUker :
      U ⊆
        (finitePlaceGlobalArtinMonoidHom
          (K := K) (L := L)) ⁻¹' {1} := by
    intro a ha
    change finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L) a = 1
    apply finprod_eq_one_of_forall_eq_one
    intro v
    by_cases hv : v ∈ S
    · have hvNorm := ha.2 v hv
      rw [← chosenFinitePlaceArtinMonoidHom_ker
        (K := K) (L := L) v] at hvNorm
      exact MonoidHom.mem_ker.mp hvNorm
    · have hvT : v ∉ T := by
        simp only [S, Set.Finite.mem_toFinset] at hv
        exact hv
      have haIntegral :
          IdeleGroup.finiteComponent v a ∈
            (v.adicCompletionIntegers K).units := by
        exact
          (IdeleGroup.mem_supportedAt_iff
            (K := K) (S : Set _) a).mp ha.1 v hv
      apply
        chosenFinitePlaceArtinMonoidHom_eq_one_of_integral_of_unramifiedAt
          (K := K) (L := L) v a haIntegral
      by_contra hram
      apply hvT
      exact
        ⟨finitePlaceExtensionCentre
            (K := K) (L := L) v
            (chosenFinitePlaceExtension
              (L := L) v),
          finitePlaceExtensionCentre_liesOver
            (K := K) (L := L) v
            (chosenFinitePlaceExtension
              (L := L) v),
          hram⟩
  apply continuous_of_continuousAt_one _
  rw [continuousAt_def, map_one]
  intro V hV
  apply Filter.mem_of_superset (hUopen.mem_nhds hUone)
  intro a ha
  have hmap : finitePlaceGlobalArtinMonoidHom
      (K := K) (L := L) a = 1 :=
    Set.mem_preimage.mp (hUker ha)
  change finitePlaceGlobalArtinMonoidHom
      (K := K) (L := L) a ∈ V
  simpa only [hmap] using mem_of_mem_nhds hV

open scoped Classical in
/-- The finite Artin product after an idele norm is the `finprod`, over
base finite places, of the products of the corresponding local norm
factors at all finite places upstairs. -/
theorem finitePlaceGlobalArtinMonoidHom_norm_eq_finprod_fibers
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    (a : IdeleGroup M) :
    letI : ∀ v : HeightOneSpectrum (𝓞 K),
        Fintype {W : HeightOneSpectrum (𝓞 M) //
          finitePlaceBelow (K := K) W = v} :=
      fun v => by
        let vK := HeightOneSpectrum.adicAbv K v
        let hvK : vK.IsNontrivial :=
          RayClass.adicAbv_isNontrivial v
        letI :=
          completionTensorDecompositionExtensionFintype
            (K := K) (L := M) vK hvK
        exact
          Fintype.ofEquiv (AbsoluteValueExtension vK M)
            (finitePlaceExtensionEquivAbove
              (K := K) (L := M) v)
    letI : ∀ v : HeightOneSpectrum (𝓞 K),
        ∀ W : {W : HeightOneSpectrum (𝓞 M) //
          finitePlaceBelow (K := K) W = v},
          Algebra (v.adicCompletion K)
            (W.1.adicCompletion M) :=
      fun v W =>
        (finitePlaceAdicCompletionMap
          K M v W).toAlgebra
    finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K M a) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        ∏ W : {W : HeightOneSpectrum (𝓞 M) //
            finitePlaceBelow (K := K) W = v},
          chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v
            (LocalFieldTheory.normUnits
              (v.adicCompletion K)
              (W.1.adicCompletion M)
              (IdeleGroup.finiteComponent W.1 a)) := by
  classical
  let : ∀ v : HeightOneSpectrum (𝓞 K),
      Fintype {W : HeightOneSpectrum (𝓞 M) //
        finitePlaceBelow (K := K) W = v} :=
    fun v => by
      let vK := HeightOneSpectrum.adicAbv K v
      let hvK : vK.IsNontrivial :=
        RayClass.adicAbv_isNontrivial v
      letI :=
        completionTensorDecompositionExtensionFintype
          (K := K) (L := M) vK hvK
      exact
        Fintype.ofEquiv (AbsoluteValueExtension vK M)
          (finitePlaceExtensionEquivAbove
            (K := K) (L := M) v)
  let : ∀ v : HeightOneSpectrum (𝓞 K),
      ∀ W : {W : HeightOneSpectrum (𝓞 M) //
        finitePlaceBelow (K := K) W = v},
        Algebra (v.adicCompletion K)
          (W.1.adicCompletion M) :=
    fun v W =>
      (finitePlaceAdicCompletionMap
        K M v W).toAlgebra
  rw [finitePlaceGlobalArtinMonoidHom]
  apply finprod_congr
  intro v
  rw [IdeleGroup.finiteComponent_norm_eq_prod]
  rw [map_prod]

open scoped Classical in
private theorem finitePlaceNormArtinFactor_eq_one_of_component_unit_of_unramified
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    (a : IdeleGroup M)
    (W : HeightOneSpectrum (𝓞 M))
    (hComponentUnit :
      IdeleGroup.finiteComponent W a ∈
        (W.adicCompletionIntegers M).units)
    (hunram : ChosenFinitePlaceIsUnramified
      (K := K) (L := L) (finitePlaceBelow (K := K) W)) :
    let v := finitePlaceBelow (K := K) W
    letI : Algebra (v.adicCompletion K) (W.adicCompletion M) :=
      (finitePlaceAdicCompletionMap K M v ⟨W, rfl⟩).toAlgebra
    chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (LocalFieldTheory.normUnits
          (v.adicCompletion K)
          (W.adicCompletion M)
          (IdeleGroup.finiteComponent W a)) = 1 := by
  let v := finitePlaceBelow (K := K) W
  let Wv :
      {Q : HeightOneSpectrum (𝓞 M) //
        finitePlaceBelow (K := K) Q = v} :=
    ⟨W, rfl⟩
  let z : (W.adicCompletionIntegers M).units :=
    ⟨IdeleGroup.finiteComponent W a, hComponentUnit⟩
  let : Algebra (v.adicCompletion K) (W.adicCompletion M) :=
    (finitePlaceAdicCompletionMap K M v Wv).toAlgebra
  have hNormUnit :
      LocalFieldTheory.normUnits
          (v.adicCompletion K)
          (W.adicCompletion M)
          (IdeleGroup.finiteComponent W a) ∈
        (v.adicCompletionIntegers K).units := by
    simpa only [z, Subgroup.coe_subtype] using
      IdeleGroup.finitePlace_normUnits_mem_integerUnits
        (K := K) (L := M) v Wv z
  apply
    chosenFinitePlaceArtinMonoidHom_eq_one_of_mem_localNorm
      (K := K) (L := L) v
  apply
    adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v hunram
  exact hNormUnit

open scoped Classical in
/-- The local Artin factors obtained after an idele norm have finite
multiplicative support. -/
theorem finitePlaceNormArtinFactors_hasFiniteMulSupport
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    (a : IdeleGroup M) :
    HasFiniteMulSupport
      (fun W : HeightOneSpectrum (𝓞 M) =>
        let v :=
          finitePlaceBelow (K := K) W
        letI : Algebra (v.adicCompletion K)
            (W.adicCompletion M) :=
          (finitePlaceAdicCompletionMap
            K M v ⟨W, rfl⟩).toAlgebra
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (LocalFieldTheory.normUnits
            (v.adicCompletion K)
            (W.adicCompletion M)
            (IdeleGroup.finiteComponent W a))) := by
  let S : Set (HeightOneSpectrum (𝓞 M)) :=
    {W | a.2 W ∉ (W.adicCompletionIntegers M).units}
  let T : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | ∃ V : HeightOneSpectrum (𝓞 L),
      V.asIdeal.LiesOver v.asIdeal ∧
        ¬ Algebra.IsUnramifiedAt (𝓞 K) V.asIdeal}
  let U : Set (HeightOneSpectrum (𝓞 M)) :=
    {W | finitePlaceBelow (K := K) W ∈ T}
  have hS : S.Finite :=
    Filter.eventually_cofinite.mp
      (FiniteIdeleGroup.eventually_mem_localUnits a.2)
  have hT : T.Finite :=
    AlgebraicNumberTheory.Ramification.finite_ramified_base_heightOne_primes
      (𝓞 K) (𝓞 L)
  have hU : U.Finite := by
    exact
      Set.Finite.preimage_finitePlaceBelow
        (K := K) (L := M) hT
  rw [HasFiniteMulSupport]
  apply (hS.union hU).subset
  rw [mulSupport_subset_iff']
  intro W hW
  have hWS : W ∉ S := by
    intro hWS
    exact hW (Set.mem_union_left U hWS)
  have hWU : W ∉ U := by
    intro hWU
    exact hW (Set.mem_union_right S hWU)
  let v :=
    finitePlaceBelow (K := K) W
  have hComponentUnit :
      IdeleGroup.finiteComponent W a ∈
        (W.adicCompletionIntegers M).units := by
    simpa only [S, Set.mem_ofPred_eq, not_not,
      IdeleGroup.finiteComponent_apply] using hWS
  have hvT : v ∉ T := by
    intro hvT
    apply hWU
    exact hvT
  apply
    finitePlaceNormArtinFactor_eq_one_of_component_unit_of_unramified
      (K := K) (L := L) a W hComponentUnit
  apply chosenFinitePlaceIsUnramified_of_isUnramifiedAt
    (K := K) (L := L) v
  by_contra hram
  apply hvT
  exact
    ⟨finitePlaceExtensionCentre
        (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v),
      finitePlaceExtensionCentre_liesOver
        (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v),
      hram⟩

open scoped Classical in
/-- The finite Artin product after an idele norm, indexed directly by
the actual finite places upstairs.  This is the flattened finite-place
form of the local norm--restriction identity used in the global square. -/
theorem finitePlaceGlobalArtinMonoidHom_norm_eq_finprod
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    (a : IdeleGroup M) :
    letI : ∀ W : HeightOneSpectrum (𝓞 M),
        Algebra
          ((finitePlaceBelow
            (K := K) W).adicCompletion K)
          (W.adicCompletion M) :=
      fun W =>
        (finitePlaceAdicCompletionMap
          K M
          (finitePlaceBelow (K := K) W)
          ⟨W, rfl⟩).toAlgebra
    finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K M a) =
      ∏ᶠ W : HeightOneSpectrum (𝓞 M),
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L)
          (finitePlaceBelow (K := K) W)
          (LocalFieldTheory.normUnits
            ((finitePlaceBelow
              (K := K) W).adicCompletion K)
            (W.adicCompletion M)
            (IdeleGroup.finiteComponent W a)) := by
  classical
  let : ∀ W : HeightOneSpectrum (𝓞 M),
      Algebra
        ((finitePlaceBelow
          (K := K) W).adicCompletion K)
        (W.adicCompletion M) :=
    fun W =>
      (finitePlaceAdicCompletionMap
        K M
        (finitePlaceBelow (K := K) W)
        ⟨W, rfl⟩).toAlgebra
  let : ∀ v : HeightOneSpectrum (𝓞 K),
      Fintype {W : HeightOneSpectrum (𝓞 M) //
        finitePlaceBelow (K := K) W = v} :=
    fun v => by
      let vK := HeightOneSpectrum.adicAbv K v
      let hvK : vK.IsNontrivial :=
        RayClass.adicAbv_isNontrivial v
      letI :=
        completionTensorDecompositionExtensionFintype
          (K := K) (L := M) vK hvK
      exact
        Fintype.ofEquiv (AbsoluteValueExtension vK M)
          (finitePlaceExtensionEquivAbove
            (K := K) (L := M) v)
  let : ∀ v : HeightOneSpectrum (𝓞 K),
      ∀ W : {W : HeightOneSpectrum (𝓞 M) //
        finitePlaceBelow (K := K) W = v},
        Algebra (v.adicCompletion K)
          (W.1.adicCompletion M) :=
    fun v W =>
      (finitePlaceAdicCompletionMap
        K M v W).toAlgebra
  let g :
      HeightOneSpectrum (𝓞 M) →
        HeightOneSpectrum (𝓞 K) :=
    finitePlaceBelow (K := K)
  let f :
      HeightOneSpectrum (𝓞 M) →
        (L ≃ₐ[K] L) :=
    fun W =>
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) (g W)
        (LocalFieldTheory.normUnits
          ((g W).adicCompletion K)
          (W.adicCompletion M)
          (IdeleGroup.finiteComponent W a))
  have hf : HasFiniteMulSupport f := by
    simpa only [f, g] using
      finitePlaceNormArtinFactors_hasFiniteMulSupport
        (K := K) (L := L) a
  calc
    finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K M a) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          ∏ W : {W : HeightOneSpectrum (𝓞 M) //
              g W = v},
            chosenFinitePlaceArtinMonoidHom
              (K := K) (L := L) v
              (LocalFieldTheory.normUnits
                (v.adicCompletion K)
                (W.1.adicCompletion M)
                (IdeleGroup.finiteComponent W.1 a)) := by
      simpa only [g] using
        finitePlaceGlobalArtinMonoidHom_norm_eq_finprod_fibers
          (K := K) (L := L) a
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          ∏ᶠ W : {W : HeightOneSpectrum (𝓞 M) //
              g W = v},
            f W.1 := by
      apply finprod_congr
      intro v
      rw [finprod_eq_prod_of_fintype]
      apply Finset.prod_congr rfl
      intro W _
      rcases W with ⟨W, hW⟩
      subst v
      simp only [f, g]
    _ = ∏ᶠ W : HeightOneSpectrum (𝓞 M), f W :=
      finprod_fibers_eq_sigma g f hf
    _ = ∏ᶠ W : HeightOneSpectrum (𝓞 M),
          chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L)
            (finitePlaceBelow (K := K) W)
            (LocalFieldTheory.normUnits
              ((finitePlaceBelow (K := K) W).adicCompletion K)
              (W.adicCompletion M)
              (IdeleGroup.finiteComponent W a)) := by
      apply finprod_congr
      intro W
      simp only [f, g]

open scoped Classical in
/-- The finite part of the Artin norm--restriction field diamond.
Restriction of the upper finite Artin product is the lower finite Artin product
after the ordinary idele norm. -/
theorem finitePlaceGlobalArtinMonoidHom_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L'] :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (finitePlaceGlobalArtinMonoidHom
          (K := K') (L := L')) =
      (finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)).comp
        (IdeleGroup.norm K K') := by
  apply MonoidHom.ext
  intro a
  let : ∀ W : HeightOneSpectrum (𝓞 K'),
      Algebra
        ((finitePlaceBelow
          (K := K) W).adicCompletion K)
        (W.adicCompletion K') :=
    fun W =>
      (finitePlaceAdicCompletionMap
        K K'
        (finitePlaceBelow (K := K) W)
        ⟨W, rfl⟩).toAlgebra
  change
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (∏ᶠ W : HeightOneSpectrum (𝓞 K'),
          chosenFinitePlaceArtinMonoidHom
            (K := K') (L := L') W
            (IdeleGroup.finiteComponent W a)) =
      finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K K' a)
  rw [finitePlaceGlobalArtinMonoidHom_norm_eq_finprod]
  rw [MonoidHom.map_finprod
    ((AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K))
    (finitePlaceArtinFactors_hasFiniteMulSupport
      (K := K') (L := L') a)]
  apply finprod_congr
  intro W
  exact
    DFunLike.congr_fun
      (chosenFinitePlaceArtinMonoidHom_norm_restriction
        (K := K) (L := L) W)
      (IdeleGroup.finiteComponent W a)

open scoped Classical in
/-- On an idele supported at one finite place, the finite global product
is exactly that local Artin factor. -/
@[simp]
theorem finitePlaceGlobalArtinMonoidHom_finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (finitePlaceIdele v x) =
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x := by
  change
    (∏ᶠ w : HeightOneSpectrum (𝓞 K),
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) w
        (IdeleGroup.finiteComponent w (finitePlaceIdele v x))) =
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x
  rw [finprod_eq_single _ v]
  · rw [finitePlaceIdele_finiteComponent_same]
  · intro w hw
    rw [finitePlaceIdele_finiteComponent_of_ne v w x hw,
      map_one]

end Reciprocity
end GlobalClassFieldTheory
