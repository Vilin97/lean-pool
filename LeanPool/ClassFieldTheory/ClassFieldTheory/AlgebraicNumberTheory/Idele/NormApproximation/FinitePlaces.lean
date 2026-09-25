/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Approximation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.CompMulEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Generator
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.HerbrandEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.H0
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.HMinusOne
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Trivial
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Quotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.ExtensionFactorClassification
/-!
# Weak approximation for actual local norm quotients

For a finite Galois extension `L / K` and a finite set `S` of finite
places of `K`, this file chooses an actual extension of every `v ∈ S`,
forms the corresponding algebraic localization `L_w / K_v`, and
transports its local norm subgroup to mathlib's concrete adic
completion.  These transported norm subgroups are open.  Multiplicative
weak approximation therefore gives a surjection

`Kˣ → ∏ v ∈ S, K_vˣ / N(L_wˣ)`.

All choices are made from the extension theorem for absolute values;
none of the local conclusions is included as input data.
-/

@[expose] public section

open scoped NumberField NNReal
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

open scoped Classical in
/-- The canonical dense embedding used to compare the absolute-value
completion at `v` with the concrete adic completion. -/
noncomputable def finitePlaceCompletionBaseMap
    (v : HeightOneSpectrum (𝓞 K)) :
    WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) →+*
      v.adicCompletion K :=
  (FinitePlace.embedding v).comp
    (WithAbs.equiv
      (NumberField.HeightOneSpectrum.adicAbv K v)).toRingHom

open scoped Classical in
@[simp]
theorem finitePlaceCompletionBaseMap_apply
    (v : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K v)) :
    finitePlaceCompletionBaseMap v x =
      FinitePlace.embedding v
        (WithAbs.equiv
          (NumberField.HeightOneSpectrum.adicAbv K v) x) :=
  rfl

open scoped Classical in
theorem finitePlaceCompletionBaseMap_norm
    (v : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K v)) :
    ‖finitePlaceCompletionBaseMap v x‖ = ‖x‖ := by
  rw [finitePlaceCompletionBaseMap_apply,
    FinitePlace.norm_embedding]
  rfl

open scoped Classical in
/-- The base embedding is an isometry. -/
theorem finitePlaceCompletionBaseMap_isometry
    (v : HeightOneSpectrum (𝓞 K)) :
    Isometry (finitePlaceCompletionBaseMap v) :=
  AddMonoidHomClass.isometry_of_norm _
    (finitePlaceCompletionBaseMap_norm v)

open scoped Classical in
/-- Extension of the base embedding to the absolute-value completion. -/
noncomputable def finitePlaceCompletionRingHom
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion →+*
      v.adicCompletion K :=
  UniformSpace.Completion.extensionHom
    (finitePlaceCompletionBaseMap v)
    (finitePlaceCompletionBaseMap_isometry v).continuous

open scoped Classical in
@[simp]
theorem finitePlaceCompletionRingHom_coe
    (v : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K v)) :
    finitePlaceCompletionRingHom v
        (x :
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion) =
      finitePlaceCompletionBaseMap v x :=
  UniformSpace.Completion.extensionHom_coe
    (finitePlaceCompletionBaseMap v)
    (finitePlaceCompletionBaseMap_isometry v).continuous x

open scoped Classical in
theorem finitePlaceCompletionRingHom_isometry
    (v : HeightOneSpectrum (𝓞 K)) :
    Isometry (finitePlaceCompletionRingHom v) :=
  (finitePlaceCompletionBaseMap_isometry v).completion_extension

open scoped Classical in
/-- The completed comparison map is onto the concrete adic
completion. -/
theorem finitePlaceCompletionRingHom_surjective
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (finitePlaceCompletionRingHom v) := by
  let f := finitePlaceCompletionRingHom v
  have hrangeClosed : IsClosed (Set.range f) :=
    (finitePlaceCompletionRingHom_isometry v).isClosedEmbedding.isClosed_range
  have hdense :
      DenseRange (algebraMap K (v.adicCompletion K)) :=
    v.denseRange_algebraMap K
  have hrange :
      Set.range (algebraMap K (v.adicCompletion K)) ⊆
        Set.range f := by
    rintro _ ⟨x, rfl⟩
    let x' : WithAbs
        (NumberField.HeightOneSpectrum.adicAbv K v) :=
      (WithAbs.equiv
        (NumberField.HeightOneSpectrum.adicAbv K v)).symm x
    refine
      ⟨(x' :
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion),
        ?_⟩
    rw [finitePlaceCompletionRingHom_coe]
    rfl
  intro x
  have hx :
      x ∈ closure
        (Set.range (algebraMap K (v.adicCompletion K))) := by
    rw [hdense.closure_range]
    trivial
  exact closure_minimal hrange hrangeClosed hx

open scoped Classical in
/-- The two concrete models of `K_v` are canonically isomorphic. -/
noncomputable def finitePlaceCompletionRingEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion ≃+*
      v.adicCompletion K :=
  RingEquiv.ofBijective (finitePlaceCompletionRingHom v)
    ⟨(finitePlaceCompletionRingHom_isometry v).injective,
      finitePlaceCompletionRingHom_surjective v⟩

open scoped Classical in
/-- The preceding ring equivalence, with its native topologies. -/
noncomputable def finitePlaceCompletionContinuousMulEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion ≃ₜ*
      v.adicCompletion K where
  __ := (finitePlaceCompletionRingEquiv v).toMulEquiv
  continuous_toFun :=
    (finitePlaceCompletionRingHom_isometry v).continuous
  continuous_invFun :=
    ((finitePlaceCompletionRingHom_isometry v).right_inv
      (finitePlaceCompletionRingEquiv v).right_inv).continuous

open scoped Classical in
/-- The induced topological multiplicative equivalence on unit
groups. -/
noncomputable def finitePlaceCompletionUnitsContinuousMulEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completionˣ ≃ₜ*
      (v.adicCompletion K)ˣ :=
  Units.mapContinuousMulEquiv
    (finitePlaceCompletionContinuousMulEquiv v)

open scoped Classical in
/-- The chosen extension of the `v`-adic absolute value to `L`.
The embedding is supplied by algebraic closedness of the completion's
algebraic closure. -/
noncomputable def chosenFinitePlaceExtension
    (v : HeightOneSpectrum (𝓞 K)) :
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L :=
  pullbackAbsoluteValueExtension
    (NumberField.HeightOneSpectrum.adicAbv K v)
    (RayClass.adicAbv_isNontrivial v)
    IsAlgClosed.lift

open scoped Classical in
/-- The chosen actual localization `L_w` above the finite place `v`. -/
abbrev ChosenFinitePlaceLocalizedCompletion
    (v : HeightOneSpectrum (𝓞 K)) :=
  LocalizedCompletion
    (NumberField.HeightOneSpectrum.adicAbv K v)
    (chosenFinitePlaceExtension (L := L) v)

open scoped Classical in
/-- The concrete local norm subgroup at `v`.  It is first formed in the
absolute-value completion model and then transported to the adic
completion used by the idele library. -/
noncomputable def chosenFinitePlaceLocalNormSubgroup
    (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (v.adicCompletion K)ˣ := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := LocalizedCompletion vK w
  let e :
      vK.Completionˣ ≃ₜ* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  exact
    (localNormSubgroup vK.Completion E).map
      e.toMonoidHom

open scoped Classical in
/-- The local norm subgroup transported to the actual finite idele
coordinate is open. -/
theorem chosenFinitePlaceLocalNormSubgroup_isOpen
    (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen
      (chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v :
        Set (v.adicCompletion K)ˣ) := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let E := LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    localizedCompletionModuleFinite vK hvK w
  let : IsGalois vK.Completion E :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtensionCompletionNontriviallyNormedField
      vK hvK
  let : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let : IsUltrametricDist vK.Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
        vK
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
          K v))
  let : Valued vK.Completion ℝ≥0 :=
    NormedField.toValued
  let vC : Valuation vK.Completion ℝ≥0 := Valued.v
  let : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vK.Completion)).IsNontrivial)
  let : ValuativeRel vK.Completion :=
    ValuativeRel.ofValuation vC
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  let : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  let : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let e :
      vK.Completionˣ ≃ₜ* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  have hN :
      IsOpen
        (localNormSubgroup vK.Completion E :
          Set vK.Completionˣ) :=
    LocalClassFieldTheory.localNormSubgroup_isOpen
      vK.Completion E
  change IsOpen
    (e '' (localNormSubgroup vK.Completion E :
      Set vK.Completionˣ))
  exact e.isOpenMap _ hN

open scoped Classical in
/-- The actual local norm quotient in the concrete finite-place
completion used by ideles. -/
abbrev ChosenFinitePlaceNormQuotient
    (v : HeightOneSpectrum (𝓞 K)) :=
  (v.adicCompletion K)ˣ ⧸
    chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v

open scoped Classical in
/-- The same local quotient in the absolute-value completion and
`LocalizedCompletion` model used by local class field theory. -/
noncomputable def ChosenFinitePlaceIntrinsicNormQuotient
    (v : HeightOneSpectrum (𝓞 K)) : Type := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  exact
    NormQuotient vK.Completion
      (LocalizedCompletion vK w)

open scoped Classical in
noncomputable instance
    chosenFinitePlaceIntrinsicNormQuotientCommGroup
    (v : HeightOneSpectrum (𝓞 K)) :
    CommGroup
      (ChosenFinitePlaceIntrinsicNormQuotient
        (K := K) (L := L) v) := by
  unfold ChosenFinitePlaceIntrinsicNormQuotient
  infer_instance

open scoped Classical in
/-- Comparison between the intrinsic local-class-field norm quotient
and the concrete quotient occurring in the finite idele coordinate. -/
noncomputable def chosenFinitePlaceNormQuotientEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    ChosenFinitePlaceIntrinsicNormQuotient
        (K := K) (L := L) v ≃*
      ChosenFinitePlaceNormQuotient
        (K := K) (L := L) v := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := LocalizedCompletion vK w
  let e :
      vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  let N := localNormSubgroup vK.Completion E
  have heq :
      N.map e.toMonoidHom =
        chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v :=
    rfl
  exact
    (normQuotientConcreteEquiv vK.Completion E).trans
      (QuotientGroup.congr N
        (chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v)
        e heq)

omit [FiniteDimensional K L] in
open scoped Classical in
@[simp]
theorem chosenFinitePlaceNormQuotientEquiv_normClass
    (v : HeightOneSpectrum (𝓞 K))
    (x :
      (NumberField.HeightOneSpectrum.adicAbv K v).Completionˣ) :
    let vK :=
      NumberField.HeightOneSpectrum.adicAbv K v
    let w := chosenFinitePlaceExtension (L := L) v
    let hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    let : SMul K w.1.Completion := hK.toSMul
    let : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    chosenFinitePlaceNormQuotientEquiv
        (K := K) (L := L) v
        (normClass vK.Completion
          (LocalizedCompletion vK w) x) =
      QuotientGroup.mk'
        (chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v)
        (finitePlaceCompletionUnitsContinuousMulEquiv v x) := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  rfl

open scoped Classical in
/-- Product comparison over a finite set of places. -/
noncomputable def chosenFinitePlaceNormQuotientFamilyEquiv
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (∀ v : ↥S,
        ChosenFinitePlaceIntrinsicNormQuotient
          (K := K) (L := L) v.1) ≃*
      (∀ v : ↥S,
        ChosenFinitePlaceNormQuotient
          (K := K) (L := L) v.1) :=
  MulEquiv.piCongrRight fun v ↦
    chosenFinitePlaceNormQuotientEquiv
      (K := K) (L := L) v.1

open scoped Classical in
/-- The diagonal map from global units to the chosen finite family of
actual local norm quotients. -/
noncomputable def principalLocalNormQuotientMap
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Kˣ →*
      (∀ v : ↥S,
        ChosenFinitePlaceNormQuotient
          (K := K) (L := L) v.1) :=
  IdeleGroup.principalLocalQuotientMap S
    (fun v ↦ chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v.1)

omit [FiniteDimensional K L] in
open scoped Classical in
@[simp]
theorem principalLocalNormQuotientMap_apply
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : Kˣ) (v : ↥S) :
    principalLocalNormQuotientMap
        (K := K) (L := L) S x v =
      QuotientGroup.mk'
        (chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v.1)
        ((IdeleGroup.principalIdele K x).2 v.1) :=
  rfl

open scoped Classical in
/-- Actual multiplicative local norm approximation: every prescribed
finite family of classes modulo `N(L_wˣ)` is represented by one global
element of `Kˣ`. -/
theorem principalLocalNormQuotientMap_surjective
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective
      (principalLocalNormQuotientMap
        (K := K) (L := L) S) :=
  IdeleGroup.principalLocalQuotientMap_surjective
    S
    (fun v ↦ chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v.1)
    (fun v ↦
      chosenFinitePlaceLocalNormSubgroup_isOpen
        (K := K) (L := L) v.1)

open scoped Classical in
/-- The same diagonal approximation map with target written directly as
a product of `LocalFieldTheory.NormQuotient`s. -/
noncomputable def principalIntrinsicLocalNormQuotientMap
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Kˣ →*
      (∀ v : ↥S,
        ChosenFinitePlaceIntrinsicNormQuotient
          (K := K) (L := L) v.1) :=
  (chosenFinitePlaceNormQuotientFamilyEquiv
    (K := K) (L := L) S).symm.toMonoidHom.comp
      (principalLocalNormQuotientMap
        (K := K) (L := L) S)

open scoped Classical in
/-- Surjectivity in the intrinsic `NormQuotient` model. -/
theorem principalIntrinsicLocalNormQuotientMap_surjective
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective
      (principalIntrinsicLocalNormQuotientMap
        (K := K) (L := L) S) := by
  intro q
  let E :=
    chosenFinitePlaceNormQuotientFamilyEquiv
      (K := K) (L := L) S
  obtain ⟨x, hx⟩ :=
    principalLocalNormQuotientMap_surjective
      (K := K) (L := L) S (E q)
  refine ⟨x, ?_⟩
  change E.symm
      (principalLocalNormQuotientMap
        (K := K) (L := L) S x) = q
  rw [hx, E.symm_apply_apply]

omit [FiniteDimensional K L] in
open scoped Classical in
/-- Kernel membership has the expected simultaneous local-norm
description. -/
theorem mem_ker_principalLocalNormQuotientMap_iff
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : Kˣ) :
    x ∈
        (principalLocalNormQuotientMap
          (K := K) (L := L) S).ker ↔
      ∀ v : ↥S,
        (IdeleGroup.principalIdele K x).2 v.1 ∈
          chosenFinitePlaceLocalNormSubgroup
            (K := K) (L := L) v.1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx v
    exact
      (QuotientGroup.eq_one_iff _).mp
        (congrFun hx v)
  · intro hx
    funext v
    exact
      (QuotientGroup.eq_one_iff _).mpr
        (hx v)

omit [FiniteDimensional K L] in
open scoped Classical in
/-- The kernel is the intersection of the pullbacks of the actual local
norm subgroups. -/
theorem principalLocalNormQuotientMap_ker
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (principalLocalNormQuotientMap
      (K := K) (L := L) S).ker =
      ⨅ v : ↥S,
        (chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v.1).comap
          ((IdeleGroup.finiteComponent v.1).comp
            (IdeleGroup.principalIdele K)) := by
  ext x
  rw [mem_ker_principalLocalNormQuotientMap_iff]
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl
