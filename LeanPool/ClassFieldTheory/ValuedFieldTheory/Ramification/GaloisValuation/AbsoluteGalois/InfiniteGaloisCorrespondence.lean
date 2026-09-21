/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.AbsoluteRamification
/-! Provides the public declarations in the `RamificationTheory.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence` Lean module. -/

namespace RamificationTheory

open ValuationTheory

noncomputable section

universe u v w z

namespace Field
namespace absoluteGaloisGroup

open scoped Topology Pointwise
open CategoryTheory

private theorem quotientAction_ker_eq_normalCore
    {G : Type*} [Group G] (H : Subgroup G) :
    (MulAction.toPermHom G (G ⧸ H)).ker = H.normalCore := by
  ext g
  constructor
  · intro hg b
    have hq : g • (QuotientGroup.mk (b⁻¹) : G ⧸ H) =
        QuotientGroup.mk (b⁻¹) := by
      have := congrArg
        (fun e : Equiv.Perm (G ⧸ H) => e (QuotientGroup.mk (b⁻¹))) hg
      simpa using this
    have hmem : (g * b⁻¹)⁻¹ * b⁻¹ ∈ H := QuotientGroup.eq.1 hq
    have hinv := H.inv_mem hmem
    simpa [mul_assoc] using hinv
  · intro hg
    ext q
    refine Quotient.inductionOn q ?_
    intro b
    apply QuotientGroup.eq.2
    have hmem := hg (b⁻¹)
    have hinv := H.inv_mem hmem
    simpa [mul_assoc] using hinv

private theorem normalCore_finiteIndex_of_finite_quotient
    {G : Type*} [Group G] (H : Subgroup G) [Finite (G ⧸ H)] :
    H.normalCore.FiniteIndex := by
  rw [← quotientAction_ker_eq_normalCore H, Subgroup.finiteIndex_iff,
    Subgroup.index_ker]
  exact ne_of_gt Nat.card_pos

private theorem finiteDimensional_comap_algEquiv
    {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) (E : IntermediateField F B)
    [FiniteDimensional F E] :
    FiniteDimensional F (E.comap e.toAlgHom) := by
  let Ecomap : IntermediateField F A := E.comap e.toAlgHom
  let eLin : Ecomap ≃ₗ[F] E :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun x => ⟨e.symm x.1, by
        change e (e.symm x.1) ∈ E
        rw [e.apply_symm_apply]
        exact x.2⟩
      left_inv := by
        intro x
        ext
        exact e.symm_apply_apply x.1
      right_inv := by
        intro x
        ext
        exact e.apply_symm_apply x.1
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  exact Module.Finite.equiv eLin.symm

private theorem finiteDimensional_map_algEquiv
    {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) (E : IntermediateField F A)
    [FiniteDimensional F E] :
    FiniteDimensional F (E.map e.toAlgHom) := by
  let Emap : IntermediateField F B := E.map e.toAlgHom
  let eLin : E ≃ₗ[F] Emap :=
    { toFun := fun x => ⟨e x.1, ⟨x.1, x.2, rfl⟩⟩
      invFun := fun x => ⟨e.symm x.1, by
        rcases x.2 with ⟨y, hy, hxy⟩
        rw [← hxy]
        simpa using hy⟩
      left_inv := by
        intro x
        ext
        exact e.symm_apply_apply x.1
      right_inv := by
        intro x
        ext
        exact e.apply_symm_apply x.1
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        exact e.toLinearEquiv.map_smul a x.1 }
  exact Module.Finite.equiv eLin

/-- Pull back an intermediate field along a ring equivalence which is
semilinear over a base-field equivalence.  This is the finite-level source
needed for Krull-continuity of conjugation by such a semilinear equivalence. -/
def semilinearRingEquivPreimageIntermediateField
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') : IntermediateField F Ω where
  carrier := {x : Ω | e x ∈ E}
  zero_mem' := by
    simp
  one_mem' := by
    simp
  add_mem' := by
    intro x y hx hy
    simpa using E.add_mem hx hy
  mul_mem' := by
    intro x y hx hy
    simpa using E.mul_mem hx hy
  inv_mem' := by
    intro x hx
    simpa using E.inv_mem hx
  algebraMap_mem' := by
    intro x
    change e (algebraMap F Ω x) ∈ E
    rw [he x]
    exact E.algebraMap_mem (τ x)

/-- States the theorem `mem_semilinearRingEquivPreimageIntermediateField_iff`. -/
@[simp]
theorem mem_semilinearRingEquivPreimageIntermediateField_iff
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') (x : Ω) :
    x ∈ semilinearRingEquivPreimageIntermediateField τ e he E ↔ e x ∈ E :=
  Iff.rfl

/-- States the theorem `semilinearRingEquivPreimageIntermediateField_symm_mem`. -/
theorem semilinearRingEquivPreimageIntermediateField_symm_mem
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') {x : Ω'} (hx : x ∈ E) :
    e.symm x ∈ semilinearRingEquivPreimageIntermediateField τ e he E := by
  change e (e.symm x) ∈ E
  simpa using hx

/-- The semilinear pullback of a finite intermediate field is finite. -/
theorem finiteDimensional_semilinearRingEquivPreimageIntermediateField
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') [FiniteDimensional F' E] :
    FiniteDimensional F
      (semilinearRingEquivPreimageIntermediateField τ e he E) := by
  let T := semilinearRingEquivPreimageIntermediateField τ e he E
  let f : E →ₛₗ[(τ.symm : F' →+* F)] T :=
    { toFun := fun x =>
        ⟨e.symm x.1,
          semilinearRingEquivPreimageIntermediateField_symm_mem
            τ e he E x.2⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp only [Algebra.smul_def]
        change e.symm (algebraMap F' Ω' a * x.1) =
          algebraMap F Ω (τ.symm a) * e.symm x.1
        have hbase :
            e (algebraMap F Ω (τ.symm a)) =
              algebraMap F' Ω' a := by
          simpa using he (τ.symm a)
        apply e.injective
        calc
          e (e.symm (algebraMap F' Ω' a * x.1)) =
              algebraMap F' Ω' a * x.1 := by
                rw [e.apply_symm_apply]
          _ = e (algebraMap F Ω (τ.symm a)) * x.1 := by
                rw [hbase]
          _ = e (algebraMap F Ω (τ.symm a)) * e (e.symm x.1) := by
                rw [e.apply_symm_apply]
          _ = e (algebraMap F Ω (τ.symm a) * e.symm x.1) := by
                rw [map_mul] }
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨⟨e y.1, y.2⟩, ?_⟩
    ext
    exact e.symm_apply_apply y.1
  have hfgImage : Submodule.FG ((⊤ : Submodule F' E).map f) :=
    (Module.Finite.fg_top (R := F') (M := E)).map f
  have hmaptop : (⊤ : Submodule F' E).map f =
      (⊤ : Submodule F T) := by
    rw [Submodule.map_top, LinearMap.range_eq_top_of_surjective f hsurj]
  change Module.Finite F T
  exact Module.Finite.of_fg_top (by simpa [hmaptop] using hfgImage)

/-- Conjugation by a semilinear equivalence of an algebraic closure is
continuous for the Krull topology.  The semilinear base action is recorded
explicitly by `he`, and the group homomorphism is required only to have the
corresponding conjugation formula on underlying ring equivalences. -/
theorem semilinear_conjugation_continuous
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (φ : Gal(Ω / F) →* Gal(Ω' / F'))
    (hφ : ∀ g : Gal(Ω / F),
      (φ g).toRingEquiv =
        e.symm.trans (g.toRingEquiv.trans e)) :
    Continuous φ := by
  refine continuous_of_continuousAt_one φ ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff F' Ω' s).1 hs with
    ⟨E, hE, hEs⟩
  let Epre : IntermediateField F Ω :=
    semilinearRingEquivPreimageIntermediateField τ e he E
  have : FiniteDimensional F' E := hE
  have : FiniteDimensional F Epre :=
    finiteDimensional_semilinearRingEquivPreimageIntermediateField
      τ e he E
  refine (krullTopology_mem_nhds_one_iff F Ω (φ ⁻¹' s)).2 ?_
  refine ⟨Epre, inferInstance, ?_⟩
  intro σ hσ
  apply hEs
  change φ σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hxpre : e.symm x ∈ Epre :=
    semilinearRingEquivPreimageIntermediateField_symm_mem
      τ e he E hx
  have hfix :=
    (IntermediateField.mem_fixingSubgroup_iff Epre σ).1 hσ
      (e.symm x) hxpre
  change (φ σ).toRingEquiv x = x
  rw [hφ σ]
  change e (σ (e.symm x)) = x
  rw [hfix, e.apply_symm_apply]

/-- Algebra-equivalence conjugation is continuous for Krull topologies. -/
theorem algEquiv_autCongr_continuous
    {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) :
    Continuous (AlgEquiv.autCongr e : Gal(A / F) → Gal(B / F)) := by
  refine continuous_of_continuousAt_one (AlgEquiv.autCongr e).toMonoidHom ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff F B s).1 hs with
    ⟨E, hE, hEs⟩
  let Ecomap : IntermediateField F A := E.comap e.toAlgHom
  have : FiniteDimensional F E := hE
  have : FiniteDimensional F Ecomap :=
    finiteDimensional_comap_algEquiv e E
  refine (krullTopology_mem_nhds_one_iff F A
    ((AlgEquiv.autCongr e) ⁻¹' s)).2 ?_
  refine ⟨Ecomap, inferInstance, ?_⟩
  intro σ hσ
  apply hEs
  change AlgEquiv.autCongr e σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change e (σ (e.symm x)) = x
  have hxEcomap : e.symm x ∈ Ecomap := by
    change e (e.symm x) ∈ E
    rw [e.apply_symm_apply]
    exact hx
  have hfix := (IntermediateField.mem_fixingSubgroup_iff Ecomap σ).1 hσ
    (e.symm x) hxEcomap
  rw [hfix]
  exact e.apply_symm_apply x

/-- The inverse of algebra-equivalence conjugation is continuous for Krull
topologies. -/
theorem algEquiv_autCongr_symm_continuous
    {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) :
    Continuous ((AlgEquiv.autCongr e).symm : Gal(B / F) → Gal(A / F)) := by
  rw [AlgEquiv.autCongr_symm]
  exact algEquiv_autCongr_continuous e.symm

/-- Extend a `K`-automorphism of the absolute separable closure to the fixed
chosen algebraic closure.  The extension is canonical because
`AlgebraicClosure K` is purely inseparable over `SeparableClosure K`. -/
noncomputable def separableClosureExtensionAlgEquiv
    (K : Type u) [Field K]
    (τ : Gal(SeparableClosure K / K)) :
    Gal(AlgebraicClosure K / K) := by
  letI : Algebra (SeparableClosure K) (AlgebraicClosure K) :=
    (separableClosure K (AlgebraicClosure K)).val.toRingHom.toAlgebra
  haveI : IsScalarTower K (SeparableClosure K) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => by
      rfl
  haveI : Algebra.IsAlgebraic (SeparableClosure K) (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (L := SeparableClosure K)
      (A := AlgebraicClosure K)
  haveI : IsAlgClosure (SeparableClosure K) (AlgebraicClosure K) :=
    { isAlgClosed := inferInstance
      isAlgebraic := inferInstance }
  let eRing : SeparableClosure K ≃+* SeparableClosure K := τ.toRingEquiv
  let e0 : AlgebraicClosure K ≃+* AlgebraicClosure K :=
    IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) eRing
  refine
    { e0 with
      commutes' := ?_ }
  intro x
  calc
    e0 (algebraMap K (AlgebraicClosure K) x) =
        algebraMap (SeparableClosure K) (AlgebraicClosure K)
          (eRing (algebraMap K (SeparableClosure K) x)) := by
      change
        IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K)
            eRing (algebraMap K (AlgebraicClosure K) x) =
          algebraMap (SeparableClosure K) (AlgebraicClosure K)
            (eRing (algebraMap K (SeparableClosure K) x))
      have hmap :
          algebraMap K (AlgebraicClosure K) x =
            algebraMap (SeparableClosure K) (AlgebraicClosure K)
              (algebraMap K (SeparableClosure K) x) :=
        (IsScalarTower.algebraMap_apply K (SeparableClosure K)
          (AlgebraicClosure K) x).symm
      rw [hmap]
      exact
        IsAlgClosure.equivOfEquiv_algebraMap
          (AlgebraicClosure K) (AlgebraicClosure K) eRing
          (algebraMap K (SeparableClosure K) x)
    _ = algebraMap (SeparableClosure K) (AlgebraicClosure K)
          (algebraMap K (SeparableClosure K) x) := by
      rw [show eRing (algebraMap K (SeparableClosure K) x) =
          algebraMap K (SeparableClosure K) x from τ.commutes x]
    _ = algebraMap K (AlgebraicClosure K) x := rfl

/-- Restrict an absolute Galois element of the chosen algebraic closure to the
absolute separable closure. -/
def restrictToSeparableClosure
    (K : Type u) [Field K] :
    Gal(AlgebraicClosure K / K) →* Gal(SeparableClosure K / K) where
  toFun σ := AlgEquiv.separableClosure σ
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

/-- States the theorem `separableClosureExtensionAlgEquiv_restricts`. -/
@[simp]
theorem separableClosureExtensionAlgEquiv_restricts
    (K : Type u) [Field K]
    (τ : Gal(SeparableClosure K / K)) (x : SeparableClosure K) :
    separableClosureExtensionAlgEquiv K τ x = τ x := by
  dsimp [separableClosureExtensionAlgEquiv]
  let : Algebra (SeparableClosure K) (AlgebraicClosure K) :=
    (separableClosure K (AlgebraicClosure K)).val.toRingHom.toAlgebra
  have : IsScalarTower K (SeparableClosure K) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => by
      rfl
  have : Algebra.IsAlgebraic (SeparableClosure K) (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (L := SeparableClosure K)
      (A := AlgebraicClosure K)
  have : IsAlgClosure (SeparableClosure K) (AlgebraicClosure K) :=
    { isAlgClosed := inferInstance
      isAlgebraic := inferInstance }
  change
    IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K)
      τ.toRingEquiv (algebraMap (SeparableClosure K) (AlgebraicClosure K) x) =
        algebraMap (SeparableClosure K) (AlgebraicClosure K) (τ x)
  exact
    IsAlgClosure.equivOfEquiv_algebraMap
      (AlgebraicClosure K) (AlgebraicClosure K) τ.toRingEquiv x

/-- States the theorem `restrictToSeparableClosure_extension`. -/
@[simp]
theorem restrictToSeparableClosure_extension
    (K : Type u) [Field K] (τ : Gal(SeparableClosure K / K)) :
    AlgEquiv.separableClosure (separableClosureExtensionAlgEquiv K τ) = τ := by
  ext x
  exact separableClosureExtensionAlgEquiv_restricts K τ x

/-- States the theorem `extension_restrictToSeparableClosure`. -/
@[simp]
theorem extension_restrictToSeparableClosure
    (K : Type u) [Field K] (σ : Gal(AlgebraicClosure K / K)) :
    separableClosureExtensionAlgEquiv K (AlgEquiv.separableClosure σ) = σ := by
  let : Algebra (SeparableClosure K) (AlgebraicClosure K) :=
    (separableClosure K (AlgebraicClosure K)).val.toRingHom.toAlgebra
  have : IsScalarTower K (SeparableClosure K) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => by
      rfl
  have : Algebra.IsAlgebraic (SeparableClosure K) (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (L := SeparableClosure K)
      (A := AlgebraicClosure K)
  have : IsPurelyInseparable (SeparableClosure K) (AlgebraicClosure K) :=
    separableClosure.isPurelyInseparable K (AlgebraicClosure K)
  have hAlg :
      (separableClosureExtensionAlgEquiv K
        (AlgEquiv.separableClosure σ)).toAlgHom = σ.toAlgHom := by
    apply IsPurelyInseparable.injective_restrictDomain
        (F := SeparableClosure K) (E := AlgebraicClosure K)
        (R := K) (L := AlgebraicClosure K)
    ext x
    change
      separableClosureExtensionAlgEquiv K (AlgEquiv.separableClosure σ) x =
        σ x
    exact separableClosureExtensionAlgEquiv_restricts K
      (AlgEquiv.separableClosure σ) x
  ext x
  exact congrArg (fun f : AlgebraicClosure K →ₐ[K] AlgebraicClosure K => f x) hAlg

/-- The algebraic absolute Galois group of the chosen algebraic closure is
canonically the Galois group of the absolute separable closure. -/
noncomputable def separableClosureMulEquiv
    (K : Type u) [Field K] :
    Gal(AlgebraicClosure K / K) ≃* Gal(SeparableClosure K / K) where
  toFun σ := AlgEquiv.separableClosure σ
  invFun τ := separableClosureExtensionAlgEquiv K τ
  left_inv σ := extension_restrictToSeparableClosure K σ
  right_inv τ := restrictToSeparableClosure_extension K τ
  map_mul' σ τ := by
    ext x
    rfl

/-- States the theorem `separableClosureMulEquiv_continuous`. -/
theorem separableClosureMulEquiv_continuous
    (K : Type u) [Field K] :
    Continuous (separableClosureMulEquiv K :
      Gal(AlgebraicClosure K / K) → Gal(SeparableClosure K / K)) := by
  refine continuous_of_continuousAt_one (restrictToSeparableClosure K) ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff K (SeparableClosure K) s).1 hs with
    ⟨E, hE, hEs⟩
  let Elift : IntermediateField K (AlgebraicClosure K) := IntermediateField.lift E
  have : FiniteDimensional K E := hE
  have : FiniteDimensional K Elift := by
    let eLin : E ≃ₗ[K] Elift := (IntermediateField.liftAlgEquiv E).toLinearEquiv
    exact Module.Finite.equiv eLin
  refine (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K)
    ((separableClosureMulEquiv K) ⁻¹' s)).2 ?_
  refine ⟨Elift, inferInstance, ?_⟩
  intro σ hσ
  apply hEs
  change AlgEquiv.separableClosure σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  apply Subtype.ext
  change σ x = x
  have hxElift : (x : AlgebraicClosure K) ∈ Elift := by
    exact (IntermediateField.mem_lift x).2 hx
  exact (IntermediateField.mem_fixingSubgroup_iff Elift σ).1 hσ x hxElift

/-- States the theorem `lift_separableClosure_le_absoluteSeparableClosure`. -/
theorem lift_separableClosure_le_absoluteSeparableClosure
    (K : Type u) [Field K]
    (E : IntermediateField K (AlgebraicClosure K)) :
    IntermediateField.lift (separableClosure K E) ≤
      (separableClosure K (AlgebraicClosure K)) := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact (mem_separableClosure_iff.1 hy).map E.val E.val.injective

/-- The separable part of a finite algebraic-closure intermediate field, viewed
inside the absolute separable closure. -/
def separablePartInAbsoluteSeparableClosure
    (K : Type u) [Field K]
    (E : IntermediateField K (AlgebraicClosure K)) :
    IntermediateField K (SeparableClosure K) :=
  IntermediateField.restrict
    (lift_separableClosure_le_absoluteSeparableClosure K E)

/-- States the theorem `finiteDimensional_separablePartInAbsoluteSeparableClosure`. -/
theorem finiteDimensional_separablePartInAbsoluteSeparableClosure
    (K : Type u) [Field K]
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    FiniteDimensional K (separablePartInAbsoluteSeparableClosure K E) := by
  let Esep : IntermediateField K E := separableClosure K E
  have : FiniteDimensional K Esep := inferInstance
  let EsepLift : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.lift Esep
  have : FiniteDimensional K EsepLift := by
    let eLin : Esep ≃ₗ[K] EsepLift :=
      (IntermediateField.liftAlgEquiv Esep).toLinearEquiv
    exact Module.Finite.equiv eLin
  let hle := lift_separableClosure_le_absoluteSeparableClosure K E
  let eAlg :
      EsepLift ≃ₐ[K] separablePartInAbsoluteSeparableClosure K E :=
    IntermediateField.restrictAlgEquiv hle
  exact Module.Finite.equiv eAlg.toLinearEquiv

/-- States the theorem `separableClosureExtension_mem_fixingSubgroup_of_mem_separablePart`. -/
theorem separableClosureExtension_mem_fixingSubgroup_of_mem_separablePart
    (K : Type u) [Field K]
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    (τ : Gal(SeparableClosure K / K))
    (hτ : τ ∈ (separablePartInAbsoluteSeparableClosure K E).fixingSubgroup) :
    separableClosureExtensionAlgEquiv K τ ∈ E.fixingSubgroup := by
  let Esep : IntermediateField K E := separableClosure K E
  let EsepLift : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.lift Esep
  let hle := lift_separableClosure_le_absoluteSeparableClosure K E
  have hfixSepLift :
      ∀ y ∈ EsepLift, separableClosureExtensionAlgEquiv K τ y = y := by
    intro y hy
    have hyS : y ∈ separableClosure K (AlgebraicClosure K) := hle hy
    let ys : SeparableClosure K := ⟨y, hyS⟩
    have hyF : ys ∈ separablePartInAbsoluteSeparableClosure K E := by
      exact (IntermediateField.mem_restrict hle ys).2 hy
    have hτfix :
        τ ys = ys :=
      (IntermediateField.mem_fixingSubgroup_iff
        (separablePartInAbsoluteSeparableClosure K E) τ).1 hτ ys hyF
    calc
      separableClosureExtensionAlgEquiv K τ y =
          separableClosureExtensionAlgEquiv K τ (ys : AlgebraicClosure K) := rfl
      _ = τ ys := separableClosureExtensionAlgEquiv_restricts K τ ys
      _ = ys := congrArg Subtype.val hτfix
      _ = y := rfl
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let : Algebra E (AlgebraicClosure K) := E.val.toRingHom.toAlgebra
  have : IsScalarTower K E (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => by
      rfl
  have : IsPurelyInseparable Esep E :=
    separableClosure.isPurelyInseparable K E
  let : Algebra Esep (AlgebraicClosure K) :=
    ((algebraMap E (AlgebraicClosure K)).comp
      (algebraMap Esep E)).toAlgebra
  let incl : E →ₐ[Esep] AlgebraicClosure K :=
    { algebraMap E (AlgebraicClosure K) with
      commutes' := by
        intro y
        rfl }
  let moved : E →ₐ[Esep] AlgebraicClosure K :=
    { ((separableClosureExtensionAlgEquiv K τ).toRingHom.comp
        (algebraMap E (AlgebraicClosure K))) with
      commutes' := by
        intro y
        change separableClosureExtensionAlgEquiv K τ
            (algebraMap E (AlgebraicClosure K) (algebraMap Esep E y)) =
          algebraMap E (AlgebraicClosure K) (algebraMap Esep E y)
        have hyLift : (algebraMap E (AlgebraicClosure K)
            (algebraMap Esep E y)) ∈ EsepLift := by
          exact (IntermediateField.mem_lift (algebraMap Esep E y)).2 y.2
        exact hfixSepLift
          (algebraMap E (AlgebraicClosure K) (algebraMap Esep E y)) hyLift }
  have hmoved : moved = incl := Subsingleton.elim _ _
  have hpoint :=
    congrArg (fun f : E →ₐ[Esep] AlgebraicClosure K => f ⟨x, hx⟩) hmoved
  dsimp [moved, incl] at hpoint
  exact hpoint

/-- States the theorem `separableClosureMulEquiv_symm_continuous`. -/
theorem separableClosureMulEquiv_symm_continuous
    (K : Type u) [Field K] :
    Continuous ((separableClosureMulEquiv K).symm :
      Gal(SeparableClosure K / K) → Gal(AlgebraicClosure K / K)) := by
  refine continuous_of_continuousAt_one (separableClosureMulEquiv K).symm.toMonoidHom ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K) s).1 hs with
    ⟨E, hE, hEs⟩
  let F : IntermediateField K (SeparableClosure K) :=
    separablePartInAbsoluteSeparableClosure K E
  have : FiniteDimensional K E := hE
  have : FiniteDimensional K F :=
    finiteDimensional_separablePartInAbsoluteSeparableClosure K E
  refine (krullTopology_mem_nhds_one_iff K (SeparableClosure K)
    (((separableClosureMulEquiv K).symm) ⁻¹' s)).2 ?_
  refine ⟨F, inferInstance, ?_⟩
  intro τ hτ
  apply hEs
  change separableClosureExtensionAlgEquiv K τ ∈ E.fixingSubgroup
  exact
    separableClosureExtension_mem_fixingSubgroup_of_mem_separablePart
      K E τ hτ

/-- Topological identification of the usual algebraic-closure absolute Galois
group with the Galois group of the absolute separable closure. -/
noncomputable def separableClosureContinuousMulEquiv
    (K : Type u) [Field K] :
    Gal(AlgebraicClosure K / K) ≃ₜ* Gal(SeparableClosure K / K) where
  toMulEquiv := separableClosureMulEquiv K
  continuous_toFun := separableClosureMulEquiv_continuous K
  continuous_invFun := separableClosureMulEquiv_symm_continuous K

/-- The natural inclusion `Gal(M/E) -> Gal(M/K)` for an intermediate field
`E` of a field extension `M/K`. -/
def ofIntermediateFieldInExtension
    {K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M]
    (E : IntermediateField K M) :
    Gal(M / E) →* Gal(M / K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

/-- States the theorem `ofIntermediateFieldInExtension_apply`. -/
@[simp]
theorem ofIntermediateFieldInExtension_apply
    {K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M]
    (E : IntermediateField K M) (σ : Gal(M / E)) :
    ofIntermediateFieldInExtension E σ = σ.restrictScalars K :=
  rfl

/-- The image of `Gal(M/E)` in `Gal(M/K)` is exactly the subgroup fixing `E`. -/
theorem range_ofIntermediateFieldInExtension
    {K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M]
    (E : IntermediateField K M) :
    MonoidHom.range (ofIntermediateFieldInExtension E) = E.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change τ x = x
    simpa using τ.commutes ⟨x, hx⟩
  · intro hσ
    refine ⟨IntermediateField.fixingSubgroupEquiv E ⟨σ, hσ⟩, ?_⟩
    apply AlgEquiv.ext
    intro x
    rfl

/-- Exactness of the finite-level Galois restriction map:
`ker(Gal(M/K) -> Gal(E/K))` is the image of `Gal(M/E) -> Gal(M/K)`. -/
theorem restrictNormalHom_ker_eq_range_ofIntermediateFieldInExtension
    {K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M]
    (E : IntermediateField K M) [Normal K E] :
    (AlgEquiv.restrictNormalHom E : Gal(M / K) →* Gal(E / K)).ker =
      MonoidHom.range (ofIntermediateFieldInExtension E) := by
  rw [IntermediateField.restrictNormalHom_ker E,
    range_ofIntermediateFieldInExtension]

variable (K : Type u) [Field K]

/-- The natural inclusion `Gal(K^al/E) → G_K`, for an intermediate field
`E ⊆ K^al`. -/
def ofIntermediateField (E : IntermediateField K (AlgebraicClosure K)) :
    Gal(AlgebraicClosure K / E) →* Gal(AlgebraicClosure K / K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

/-- States the theorem `ofIntermediateField_apply`. -/
@[simp]
theorem ofIntermediateField_apply
    (E : IntermediateField K (AlgebraicClosure K))
    (σ : Gal(AlgebraicClosure K / E)) :
    ofIntermediateField K E σ = σ.restrictScalars K :=
  rfl

/-- The image of `Gal(K^al/E)` in `G_K` is exactly the subgroup fixing `E`. -/
theorem range_ofIntermediateField
    (E : IntermediateField K (AlgebraicClosure K)) :
    MonoidHom.range (ofIntermediateField K E) = E.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change τ x = x
    simpa using τ.commutes ⟨x, hx⟩
  · intro hσ
    refine ⟨IntermediateField.fixingSubgroupEquiv E ⟨σ, hσ⟩, ?_⟩
    apply AlgEquiv.ext
    intro x
    rfl

/-- The natural inclusion `Gal(K^al/E) → G_K` is injective. -/
theorem ofIntermediateField_injective
    (E : IntermediateField K (AlgebraicClosure K)) :
    Function.Injective (ofIntermediateField K E) := by
  intro σ τ hστ
  apply AlgEquiv.ext
  intro x
  exact congrArg
    (fun ρ : Gal(AlgebraicClosure K / K) => ρ x) hστ

/-- States the theorem `ofIntermediateField_eq_iff`. -/
theorem ofIntermediateField_eq_iff
    (E : IntermediateField K (AlgebraicClosure K))
    (σ τ : Gal(AlgebraicClosure K / E)) :
    ofIntermediateField K E σ = ofIntermediateField K E τ ↔ σ = τ :=
  ⟨fun h => ofIntermediateField_injective K E h, fun h => by rw [h]⟩

theorem finiteDimensional_extendScalars_sup
    (k : Type u) (M : Type v) [Field k] [Field M] [Algebra k M]
    (E F : IntermediateField k M)
    [FiniteDimensional k E] [FiniteDimensional k F] :
    FiniteDimensional E
      (IntermediateField.extendScalars (F := E) (E := E ⊔ F) le_sup_left) := by
  let EF : IntermediateField k M := E ⊔ F
  let EEF : IntermediateField E M :=
    IntermediateField.extendScalars (F := E) (E := EF) le_sup_left
  have : FiniteDimensional k EF := E.finiteDimensional_sup F
  let : Algebra E EF := (IntermediateField.inclusion le_sup_left).toAlgebra
  have : IsScalarTower k E EF := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    change (algebraMap k M) x =
      ((IntermediateField.inclusion le_sup_left) ((algebraMap k E) x) :
        M)
    rfl
  have : Module.Finite E EF := FiniteDimensional.right k E EF
  let eLin : EEF ≃ₗ[E] EF :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro x
        ext
        rfl
      map_add' := by
        intro x y
        ext
        rfl
      map_smul' := by
        intro a x
        ext
        rfl }
  exact Module.Finite.equiv eLin.symm

/-- For a finite intermediate extension `E/K`, the natural inclusion
`Gal(M/E) → Gal(M/K)` is continuous for the two Krull topologies. -/
theorem ofIntermediateFieldInExtension_continuous
    {k : Type u} {M : Type v} [Field k] [Field M] [Algebra k M]
    [IsGalois k M]
    (E : IntermediateField k M) [FiniteDimensional k E] :
    Continuous (ofIntermediateFieldInExtension E) := by
  refine continuous_of_continuousAt_one
    (ofIntermediateFieldInExtension E) ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rcases (krullTopology_mem_nhds_one_iff k M s).1 hs with
    ⟨F, hF, hFs⟩
  let EF : IntermediateField k M := E ⊔ F
  let EEF : IntermediateField E M :=
    IntermediateField.extendScalars (F := E) (E := EF) le_sup_left
  have : FiniteDimensional k F := hF
  have : FiniteDimensional E EEF :=
    finiteDimensional_extendScalars_sup k M E F
  refine (krullTopology_mem_nhds_one_iff E M
    ((ofIntermediateFieldInExtension E) ⁻¹' s)).2 ?_
  refine ⟨EEF, inferInstance, ?_⟩
  intro σ hσ
  apply hFs
  change ofIntermediateFieldInExtension E σ ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change σ x = x
  have hxEF : x ∈ EF := (show F ≤ EF from le_sup_right) hx
  have hxEEF : x ∈ EEF := by
    change x ∈ EF
    exact hxEF
  exact (IntermediateField.mem_fixingSubgroup_iff EEF σ).1 hσ x hxEEF

private theorem finiteDimensional_restrictScalars
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    (F : IntermediateField E (AlgebraicClosure K)) [FiniteDimensional E F] :
    FiniteDimensional K (F.restrictScalars K) := by
  have : FiniteDimensional K F := FiniteDimensional.trans K E F
  let FK : IntermediateField K (AlgebraicClosure K) := F.restrictScalars K
  let eLin : FK ≃ₗ[K] F :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro x
        ext
        rfl
      map_add' := by
        intro x y
        ext
        rfl
      map_smul' := by
        intro a x
        ext
        rfl }
  exact Module.Finite.equiv eLin.symm

/-- The natural inclusion `Gal(K^al/E) → G_K` is continuous for the Krull
topologies when `E/K` is finite. -/
theorem ofIntermediateField_continuous
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    Continuous (ofIntermediateField K E) := by
  refine continuous_of_continuousAt_one (ofIntermediateField K E) ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rcases (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K) s).1 hs with
    ⟨F, hF, hFs⟩
  let EF : IntermediateField K (AlgebraicClosure K) := E ⊔ F
  let EEF : IntermediateField E (AlgebraicClosure K) :=
    IntermediateField.extendScalars (F := E) (E := EF) le_sup_left
  have : FiniteDimensional K F := hF
  have : FiniteDimensional E EEF :=
    finiteDimensional_extendScalars_sup K (AlgebraicClosure K) E F
  refine (krullTopology_mem_nhds_one_iff E (AlgebraicClosure K)
    ((ofIntermediateField K E) ⁻¹' s)).2 ?_
  refine ⟨EEF, inferInstance, ?_⟩
  intro σ hσ
  apply hFs
  change ofIntermediateField K E σ ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change σ x = x
  have hxEF : x ∈ EF := (show F ≤ EF from le_sup_right) hx
  have hxEEF : x ∈ EEF := by
    change x ∈ EF
    exact hxEF
  exact (IntermediateField.mem_fixingSubgroup_iff EEF σ).1 hσ x hxEEF

/-- The finite-subextension open subgroup of `G_K` corresponding to
`E ⊆ K^al`. This is the concrete form of `G_E ≤ G_K`. -/
def openSubgroupOfFiniteIntermediateField
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    OpenSubgroup (Gal(AlgebraicClosure K / K)) :=
  ⟨E.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen E⟩

/-- States the theorem `openSubgroupOfFiniteIntermediateField_toSubgroup`. -/
@[simp]
theorem openSubgroupOfFiniteIntermediateField_toSubgroup
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    (openSubgroupOfFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K))) =
      E.fixingSubgroup :=
  rfl

/-- States the theorem `mem_openSubgroupOfFiniteIntermediateField`. -/
@[simp]
theorem mem_openSubgroupOfFiniteIntermediateField
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    (σ : Gal(AlgebraicClosure K / K)) :
    σ ∈ openSubgroupOfFiniteIntermediateField K E ↔
      ∀ x ∈ E, σ x = x := by
  rw [← IntermediateField.mem_fixingSubgroup_iff E σ]
  rfl

/-- The finite-intermediate-field open subgroup construction is contravariant:
if `E ≤ F`, then `G_F ≤ G_E` inside `G_K`. -/
theorem openSubgroupOfFiniteIntermediateField_le
    (E F : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [FiniteDimensional K F] (hEF : E ≤ F) :
    (openSubgroupOfFiniteIntermediateField K F :
      Subgroup (Gal(AlgebraicClosure K / K))) ≤
      openSubgroupOfFiniteIntermediateField K E := by
  change F.fixingSubgroup ≤ E.fixingSubgroup
  exact E.fixingSubgroup_le hEF

/-- The finite-subextension open subgroup attached to the compositum `E ⊔ F`.
Its underlying subgroup is the intersection of the open subgroups attached to
`E` and `F`. -/
def openSubgroupOfFiniteIntermediateFieldSup
    (E F : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [FiniteDimensional K F] :
    OpenSubgroup (Gal(AlgebraicClosure K / K)) := by
  let EF : IntermediateField K (AlgebraicClosure K) := E ⊔ F
  haveI : FiniteDimensional K EF := E.finiteDimensional_sup F
  exact openSubgroupOfFiniteIntermediateField K EF

/-- States the theorem `openSubgroupOfFiniteIntermediateFieldSup_toSubgroup`. -/
@[simp]
theorem openSubgroupOfFiniteIntermediateFieldSup_toSubgroup
    (E F : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [FiniteDimensional K F] :
    (openSubgroupOfFiniteIntermediateFieldSup K E F :
      Subgroup (Gal(AlgebraicClosure K / K))) =
      (openSubgroupOfFiniteIntermediateField K E :
        Subgroup (Gal(AlgebraicClosure K / K))) ⊓
        openSubgroupOfFiniteIntermediateField K F := by
  change (E ⊔ F).fixingSubgroup = E.fixingSubgroup ⊓ F.fixingSubgroup
  exact IntermediateField.fixingSubgroup_sup

/-- States the theorem `mem_openSubgroupOfFiniteIntermediateFieldSup`. -/
theorem mem_openSubgroupOfFiniteIntermediateFieldSup
    (E F : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [FiniteDimensional K F]
    (σ : Gal(AlgebraicClosure K / K)) :
    σ ∈ openSubgroupOfFiniteIntermediateFieldSup K E F ↔
      σ ∈ openSubgroupOfFiniteIntermediateField K E ∧
        σ ∈ openSubgroupOfFiniteIntermediateField K F := by
  change
    σ ∈ (openSubgroupOfFiniteIntermediateFieldSup K E F :
      Subgroup (Gal(AlgebraicClosure K / K))) ↔
      σ ∈ (openSubgroupOfFiniteIntermediateField K E :
        Subgroup (Gal(AlgebraicClosure K / K))) ∧
        σ ∈ (openSubgroupOfFiniteIntermediateField K F :
          Subgroup (Gal(AlgebraicClosure K / K)))
  rw [openSubgroupOfFiniteIntermediateFieldSup_toSubgroup]
  simp

/-- States the theorem `range_ofIntermediateField_sup`. -/
theorem range_ofIntermediateField_sup
    (E F : IntermediateField K (AlgebraicClosure K)) :
    MonoidHom.range (ofIntermediateField K (E ⊔ F)) =
      E.fixingSubgroup ⊓ F.fixingSubgroup := by
  rw [range_ofIntermediateField, IntermediateField.fixingSubgroup_sup]

/-- States the theorem `mem_range_ofIntermediateField_sup_iff`. -/
theorem mem_range_ofIntermediateField_sup_iff
    (E F : IntermediateField K (AlgebraicClosure K))
    (σ : Gal(AlgebraicClosure K / K)) :
    σ ∈ MonoidHom.range (ofIntermediateField K (E ⊔ F)) ↔
      σ ∈ E.fixingSubgroup ∧ σ ∈ F.fixingSubgroup := by
  rw [range_ofIntermediateField_sup, Subgroup.mem_inf]

/-- The normal-closure open subgroup contained in the open subgroup attached
to a finite intermediate field. -/
def openSubgroupOfNormalClosureFiniteIntermediateField
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    OpenSubgroup (Gal(AlgebraicClosure K / K)) :=
  openSubgroupOfFiniteIntermediateField K
    (IntermediateField.normalClosure K E (AlgebraicClosure K))

/-- States the theorem `openSubgroupOfNormalClosureFiniteIntermediateField_toSubgroup`. -/
@[simp]
theorem openSubgroupOfNormalClosureFiniteIntermediateField_toSubgroup
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    (openSubgroupOfNormalClosureFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K))) =
      (IntermediateField.normalClosure K E
        (AlgebraicClosure K)).fixingSubgroup :=
  rfl

/-- The normal-closure open subgroup lies inside the open subgroup for `E`. -/
theorem openSubgroupOfNormalClosureFiniteIntermediateField_le
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    (openSubgroupOfNormalClosureFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K))) ≤
      openSubgroupOfFiniteIntermediateField K E := by
  change (IntermediateField.normalClosure K E
      (AlgebraicClosure K)).fixingSubgroup ≤ E.fixingSubgroup
  exact E.fixingSubgroup_le (IntermediateField.le_normalClosure E)

/-- The open subgroup `Gal(K^al/E) ≤ G_K` is canonically isomorphic to the
ordinary Galois group `Gal(K^al/E)`. -/
def openSubgroupOfFiniteIntermediateFieldEquiv
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    openSubgroupOfFiniteIntermediateField K E ≃* Gal(AlgebraicClosure K / E) :=
  IntermediateField.fixingSubgroupEquiv E

/-- States the theorem `openSubgroupOfFiniteIntermediateFieldEquiv_apply`. -/
@[simp]
theorem openSubgroupOfFiniteIntermediateFieldEquiv_apply
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    (σ : openSubgroupOfFiniteIntermediateField K E) :
    openSubgroupOfFiniteIntermediateFieldEquiv K E σ =
      { AlgEquiv.toRingEquiv (σ : Gal(AlgebraicClosure K / K)) with
        commutes' := σ.2 } :=
  rfl

/-- States the theorem `coe_openSubgroupOfFiniteIntermediateFieldEquiv_symm_apply`. -/
@[simp]
theorem coe_openSubgroupOfFiniteIntermediateFieldEquiv_symm_apply
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    (σ : Gal(AlgebraicClosure K / E)) :
    ((openSubgroupOfFiniteIntermediateFieldEquiv K E).symm σ :
      Gal(AlgebraicClosure K / K)) =
      ofIntermediateField K E σ :=
  rfl

/-- The identification between the finite-subextension open subgroup and
`Gal(K^al/E)` is continuous from the open subgroup to the Galois group. -/
theorem openSubgroupOfFiniteIntermediateFieldEquiv_continuous
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    Continuous (openSubgroupOfFiniteIntermediateFieldEquiv K E :
      openSubgroupOfFiniteIntermediateField K E → Gal(AlgebraicClosure K / E)) := by
  let H : Subgroup (Gal(AlgebraicClosure K / K)) :=
    openSubgroupOfFiniteIntermediateField K E
  let e : H ≃* Gal(AlgebraicClosure K / E) :=
    openSubgroupOfFiniteIntermediateFieldEquiv K E
  change Continuous (e : H → Gal(AlgebraicClosure K / E))
  refine continuous_of_continuousAt_one e.toMonoidHom ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff E (AlgebraicClosure K) s).1 hs with
    ⟨F, hF, hFs⟩
  let FK : IntermediateField K (AlgebraicClosure K) := F.restrictScalars K
  have : FiniteDimensional E F := hF
  have : FiniteDimensional K FK :=
    finiteDimensional_restrictScalars K E F
  have hOpen :
      IsOpen {τ : openSubgroupOfFiniteIntermediateField K E |
        (τ : Gal(AlgebraicClosure K / K)) ∈ FK.fixingSubgroup} :=
    (IntermediateField.fixingSubgroup_isOpen FK).preimage continuous_subtype_val
  have hMem :
      {τ : openSubgroupOfFiniteIntermediateField K E |
        (τ : Gal(AlgebraicClosure K / K)) ∈ FK.fixingSubgroup} ∈
          𝓝 (1 : openSubgroupOfFiniteIntermediateField K E) := by
    apply hOpen.mem_nhds
    change (1 : Gal(AlgebraicClosure K / K)) ∈ FK.fixingSubgroup
    exact FK.fixingSubgroup.one_mem
  refine Filter.mem_of_superset hMem ?_
  intro τ hτ
  apply hFs
  change e τ ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change (τ : Gal(AlgebraicClosure K / K)) x = x
  have hxFK : x ∈ FK := by
    change x ∈ F
    exact hx
  exact (IntermediateField.mem_fixingSubgroup_iff FK
    (τ : Gal(AlgebraicClosure K / K))).1 hτ x hxFK

/-- The inverse identification `Gal(K^al/E) → Gal(K^al/E) ≤ G_K` is
continuous for finite `E/K`. -/
theorem openSubgroupOfFiniteIntermediateFieldEquiv_symm_continuous
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    Continuous ((openSubgroupOfFiniteIntermediateFieldEquiv K E).symm :
      Gal(AlgebraicClosure K / E) → openSubgroupOfFiniteIntermediateField K E) := by
  have hcomp :
      Continuous
        (fun σ : Gal(AlgebraicClosure K / E) =>
          (((openSubgroupOfFiniteIntermediateFieldEquiv K E).symm σ :
            openSubgroupOfFiniteIntermediateField K E) :
            Gal(AlgebraicClosure K / K))) := by
    simpa only [coe_openSubgroupOfFiniteIntermediateFieldEquiv_symm_apply,
      ofIntermediateField] using ofIntermediateField_continuous K E
  exact Continuous.subtype_mk hcomp fun σ =>
    ((openSubgroupOfFiniteIntermediateFieldEquiv K E).symm σ).property

/-- The finite-subextension open subgroup is topologically isomorphic to
`Gal(K^al/E)`. -/
def openSubgroupOfFiniteIntermediateFieldContinuousMulEquiv
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    openSubgroupOfFiniteIntermediateField K E ≃ₜ*
      Gal(AlgebraicClosure K / E) :=
  { toMulEquiv := openSubgroupOfFiniteIntermediateFieldEquiv K E
    continuous_toFun := openSubgroupOfFiniteIntermediateFieldEquiv_continuous K E
    continuous_invFun := openSubgroupOfFiniteIntermediateFieldEquiv_symm_continuous K E }

/-- The range of the natural inclusion is the finite-subextension open
subgroup. -/
theorem range_ofIntermediateField_eq_openSubgroup
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    MonoidHom.range (ofIntermediateField K E) =
      (openSubgroupOfFiniteIntermediateField K E :
        Subgroup (Gal(AlgebraicClosure K / K))) := by
  rw [range_ofIntermediateField]
  rfl

/-- In particular, the image of `Gal(K^al/E)` inside `G_K` is open whenever
`E/K` is finite. -/
theorem isOpen_range_ofIntermediateField
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    IsOpen (MonoidHom.range (ofIntermediateField K E) :
      Set (Gal(AlgebraicClosure K / K))) := by
  rw [range_ofIntermediateField_eq_openSubgroup]
  exact (openSubgroupOfFiniteIntermediateField K E).isOpen'

/-- States the theorem `mem_range_ofIntermediateField_iff`. -/
theorem mem_range_ofIntermediateField_iff
    (E : IntermediateField K (AlgebraicClosure K))
    (σ : Gal(AlgebraicClosure K / K)) :
    σ ∈ MonoidHom.range (ofIntermediateField K E) ↔
      σ ∈ E.fixingSubgroup := by
  rw [range_ofIntermediateField]

/-- If `E/K` is normal inside `K^al`, then the subgroup fixing `E` is normal
in `G_K`. -/
instance fixingSubgroup_normal_of_normal
    (E : IntermediateField K (AlgebraicClosure K)) [Normal K E] :
    E.fixingSubgroup.Normal := by
  rw [← IntermediateField.restrictNormalHom_ker E]
  infer_instance

/-- The finite-subextension open subgroup is normal when the finite
subextension is normal over `K`. -/
theorem openSubgroupOfFiniteIntermediateField_normal
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    [Normal K E] :
    ((openSubgroupOfFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K)))).Normal := by
  change E.fixingSubgroup.Normal
  infer_instance

/-- The normal-closure open subgroup is normal in `G_K`. -/
theorem openSubgroupOfNormalClosureFiniteIntermediateField_normal
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    ((openSubgroupOfNormalClosureFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K)))).Normal := by
  change (IntermediateField.normalClosure K E
    (AlgebraicClosure K)).fixingSubgroup.Normal
  have : Normal K (IntermediateField.normalClosure K E (AlgebraicClosure K)) := by
    have : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    exact (Algebra.IsAlgebraic.isNormalClosure_normalClosure
      (F := K) (K := E) (L := AlgebraicClosure K)
      (fun _ => IsAlgClosed.splits _)).normal
  infer_instance

/-- Provides the instance `instNormal`. -/
instance openSubgroupOfNormalClosureFiniteIntermediateField.instNormal
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    (openSubgroupOfNormalClosureFiniteIntermediateField K E).toSubgroup.Normal :=
  openSubgroupOfNormalClosureFiniteIntermediateField_normal K E

/-- For a normal intermediate field `E ⊆ K^al`, the quotient `G_K/G_E` is the
ordinary Galois group `Gal(E/K)`.  The quotient is written with
`Gal(AlgebraicClosure K / K)` so that the normal-subgroup instance for
`E.fixingSubgroup` is available by typeclass search. -/
def quotientEquivGalOfNormalIntermediateField
    (E : IntermediateField K (AlgebraicClosure K)) [Normal K E] :
    Gal(AlgebraicClosure K / K) ⧸ E.fixingSubgroup ≃* Gal(E / K) :=
  (QuotientGroup.quotientMulEquivOfEq
      ((IntermediateField.restrictNormalHom_ker E).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (AlgEquiv.restrictNormalHom E : Gal(AlgebraicClosure K / K) →* Gal(E / K))
      (AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K)))

/-- States the theorem `quotientEquivGalOfNormalIntermediateField_mk'`. -/
@[simp]
theorem quotientEquivGalOfNormalIntermediateField_mk'
    (E : IntermediateField K (AlgebraicClosure K)) [Normal K E]
    (σ : Gal(AlgebraicClosure K / K)) :
    quotientEquivGalOfNormalIntermediateField K E
        (QuotientGroup.mk' E.fixingSubgroup σ) =
      AlgEquiv.restrictNormalHom E σ := by
  exact QuotientGroup.kerLift_mk
    (AlgEquiv.restrictNormalHom E : Gal(AlgebraicClosure K / K) →* Gal(E / K)) σ

/-- Quotienting `G_K` by the normal-closure open subgroup attached to a finite
intermediate field gives the Galois group of that normal closure. -/
def quotientNormalClosureOpenSubgroupEquivGal
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    Gal(AlgebraicClosure K / K) ⧸
        (openSubgroupOfNormalClosureFiniteIntermediateField K E :
          Subgroup (Gal(AlgebraicClosure K / K))) ≃*
      Gal(IntermediateField.normalClosure K E (AlgebraicClosure K) / K) :=
  quotientEquivGalOfNormalIntermediateField K
    (IntermediateField.normalClosure K E (AlgebraicClosure K))

/-- States the theorem `quotientNormalClosureOpenSubgroupEquivGal_mk'`. -/
@[simp]
theorem quotientNormalClosureOpenSubgroupEquivGal_mk'
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    (σ : Gal(AlgebraicClosure K / K)) :
    quotientNormalClosureOpenSubgroupEquivGal K E
        (QuotientGroup.mk'
          (openSubgroupOfNormalClosureFiniteIntermediateField K E :
            Subgroup (Gal(AlgebraicClosure K / K))) σ) =
      AlgEquiv.restrictNormalHom
        (IntermediateField.normalClosure K E (AlgebraicClosure K)) σ :=
  quotientEquivGalOfNormalIntermediateField_mk' K
    (IntermediateField.normalClosure K E (AlgebraicClosure K)) σ

/-- The index of the normal-closure open subgroup is the cardinality of the
finite automorphism group of the normal closure. -/
theorem openSubgroupOfNormalClosureFiniteIntermediateField_index_eq_natCard_gal
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    (openSubgroupOfNormalClosureFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K))).index =
      Nat.card (Gal(IntermediateField.normalClosure K E (AlgebraicClosure K) / K)) := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (quotientNormalClosureOpenSubgroupEquivGal K E).toEquiv

/-- Provides the instance `instFiniteIndex`. -/
instance openSubgroupOfNormalClosureFiniteIntermediateField.instFiniteIndex
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    ((openSubgroupOfNormalClosureFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K)))).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff,
    openSubgroupOfNormalClosureFiniteIntermediateField_index_eq_natCard_gal]
  exact Nat.card_pos.ne'

/-- Provides the instance `instFiniteIndex`. -/
instance openSubgroupOfFiniteIntermediateField.instFiniteIndex
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    ((openSubgroupOfFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K)))).FiniteIndex :=
  Subgroup.finiteIndex_of_le
    (openSubgroupOfNormalClosureFiniteIntermediateField_le K E)

/-- If the chosen algebraic closure is Galois over `K`, the index of the
finite-intermediate-field open subgroup is `[E : K]`.  This hypothesis is
automatic in characteristic zero, but is intentionally explicit in general. -/
theorem openSubgroupOfFiniteIntermediateField_index_eq_finrank
    [IsGalois K (AlgebraicClosure K)]
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    (openSubgroupOfFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K))).index = Module.finrank K E := by
  change E.fixingSubgroup.index = Module.finrank K E
  exact (IntermediateField.finrank_eq_fixingSubgroup_index
    (F := K) (AlgebraicClosure K) E).symm

/-- The image of `Gal(K^al/E) → G_K` has finite index for finite `E/K`. -/
theorem range_ofIntermediateField_finiteIndex
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    (MonoidHom.range (ofIntermediateField K E)).FiniteIndex := by
  rw [range_ofIntermediateField_eq_openSubgroup]
  infer_instance

/-- If the chosen algebraic closure is Galois over `K`, the image of
`Gal(K^al/E) → G_K` has index `[E : K]`. -/
theorem range_ofIntermediateField_index_eq_finrank
    [IsGalois K (AlgebraicClosure K)]
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    (MonoidHom.range (ofIntermediateField K E)).index = Module.finrank K E := by
  rw [range_ofIntermediateField_eq_openSubgroup]
  exact openSubgroupOfFiniteIntermediateField_index_eq_finrank K E

/-- An open subgroup of `G_K`, viewed as a closed subgroup.  This is the bridge
from the topological finite-level API to mathlib's infinite Galois
correspondence. -/
def closedSubgroupOfOpenSubgroup
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    ClosedSubgroup (Gal(AlgebraicClosure K / K)) :=
  ⟨H.toSubgroup, by
    change IsClosed (H : Set (Gal(AlgebraicClosure K / K)))
    exact H.isClosed⟩

/-- States the theorem `closedSubgroupOfOpenSubgroup_toSubgroup`. -/
@[simp]
theorem closedSubgroupOfOpenSubgroup_toSubgroup
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    (closedSubgroupOfOpenSubgroup K H :
      Subgroup (Gal(AlgebraicClosure K / K))) = H.toSubgroup :=
  rfl

/-- The finite fixed field attached to an open subgroup of `G_K`. -/
def fixedFieldOfOpenSubgroup
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField H.toSubgroup

/-- States the theorem `fixedFieldOfOpenSubgroup_def`. -/
@[simp]
theorem fixedFieldOfOpenSubgroup_def
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    fixedFieldOfOpenSubgroup K H =
      IntermediateField.fixedField H.toSubgroup :=
  rfl

/-- The fixing subgroup of the fixed field of an open subgroup is the original
open subgroup, as a subgroup of `G_K`. -/
theorem fixingSubgroup_fixedFieldOfOpenSubgroup
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    (fixedFieldOfOpenSubgroup K H).fixingSubgroup = H.toSubgroup := by
  exact InfiniteGalois.fixingSubgroup_fixedField
    (closedSubgroupOfOpenSubgroup K H)

/-- Open subgroups of `G_K` have finite fixed fields. -/
theorem finiteDimensional_fixedFieldOfOpenSubgroup
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    FiniteDimensional K (fixedFieldOfOpenSubgroup K H) := by
  refine (InfiniteGalois.isOpen_iff_finite
    (K := AlgebraicClosure K) (fixedFieldOfOpenSubgroup K H)).1 ?_
  rw [fixingSubgroup_fixedFieldOfOpenSubgroup K H]
  exact H.isOpen'

/-- Provides the instance `instFiniteDimensional`. -/
instance fixedFieldOfOpenSubgroup.instFiniteDimensional
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    FiniteDimensional K (fixedFieldOfOpenSubgroup K H) :=
  finiteDimensional_fixedFieldOfOpenSubgroup K H

/-- The reverse construction sends the finite-subextension open subgroup back
to the original finite intermediate field. -/
@[simp]
theorem fixedFieldOfOpenSubgroup_openSubgroupOfFiniteIntermediateField
    [IsGalois K (AlgebraicClosure K)]
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    fixedFieldOfOpenSubgroup K
        (openSubgroupOfFiniteIntermediateField K E) = E := by
  change IntermediateField.fixedField E.fixingSubgroup = E
  exact InfiniteGalois.fixedField_fixingSubgroup E

/-- The finite-intermediate-field construction sends the fixed field of an
open subgroup back to that open subgroup. -/
@[simp]
theorem openSubgroupOfFiniteIntermediateField_fixedFieldOfOpenSubgroup
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    openSubgroupOfFiniteIntermediateField K
        (fixedFieldOfOpenSubgroup K H) = H := by
  apply OpenSubgroup.toSubgroup_injective
  exact fixingSubgroup_fixedFieldOfOpenSubgroup K H

private theorem intermediateField_eq_of_fixingSubgroup_eq
    [IsGalois K (AlgebraicClosure K)]
    {E F : IntermediateField K (AlgebraicClosure K)}
    (h : E.fixingSubgroup = F.fixingSubgroup) :
    E = F := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup E,
    ← InfiniteGalois.fixedField_fixingSubgroup F, h]

/-- The open-subgroup fixed-field construction is antitone. -/
theorem fixedFieldOfOpenSubgroup_le_of_le
    (H J : OpenSubgroup (Gal(AlgebraicClosure K / K))) (hHJ : H ≤ J) :
    fixedFieldOfOpenSubgroup K J ≤ fixedFieldOfOpenSubgroup K H := by
  exact IntermediateField.fixedField_le hHJ

/-- Order comparison under the open-subgroup fixed-field correspondence. -/
theorem fixedFieldOfOpenSubgroup_le_iff
    [IsGalois K (AlgebraicClosure K)]
    (H J : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    fixedFieldOfOpenSubgroup K H ≤ fixedFieldOfOpenSubgroup K J ↔ J ≤ H := by
  constructor
  · intro h
    have hfix :
        (fixedFieldOfOpenSubgroup K J).fixingSubgroup ≤
          (fixedFieldOfOpenSubgroup K H).fixingSubgroup :=
      IntermediateField.fixingSubgroup_le h
    rw [fixingSubgroup_fixedFieldOfOpenSubgroup K J,
      fixingSubgroup_fixedFieldOfOpenSubgroup K H] at hfix
    exact hfix
  · intro h
    exact fixedFieldOfOpenSubgroup_le_of_le K J H h

/-- Intersection of open subgroups corresponds to compositum of finite fixed
fields. -/
theorem fixedFieldOfOpenSubgroup_inf
    [IsGalois K (AlgebraicClosure K)]
    (H J : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    fixedFieldOfOpenSubgroup K (H ⊓ J) =
      fixedFieldOfOpenSubgroup K H ⊔ fixedFieldOfOpenSubgroup K J := by
  apply intermediateField_eq_of_fixingSubgroup_eq K
  rw [fixingSubgroup_fixedFieldOfOpenSubgroup K (H ⊓ J),
    IntermediateField.fixingSubgroup_sup,
    fixingSubgroup_fixedFieldOfOpenSubgroup K H,
    fixingSubgroup_fixedFieldOfOpenSubgroup K J,
    OpenSubgroup.toSubgroup_inf]

/-- The open subgroup generated by two open subgroups corresponds to the
intersection of their finite fixed fields. -/
theorem fixedFieldOfOpenSubgroup_sup
    (H J : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    fixedFieldOfOpenSubgroup K (H ⊔ J) =
      fixedFieldOfOpenSubgroup K H ⊓ fixedFieldOfOpenSubgroup K J := by
  ext x
  rw [IntermediateField.mem_inf]
  constructor
  · intro hx
    constructor
    · exact (fixedFieldOfOpenSubgroup_le_of_le K H (H ⊔ J) le_sup_left) hx
    · exact (fixedFieldOfOpenSubgroup_le_of_le K J (H ⊔ J) le_sup_right) hx
  · rintro ⟨hxH, hxJ⟩
    rw [fixedFieldOfOpenSubgroup_def, IntermediateField.mem_fixedField_iff] at hxH hxJ ⊢
    intro σ hσ
    change σ ∈ (H.toSubgroup ⊔ J.toSubgroup :
      Subgroup (Gal(AlgebraicClosure K / K))) at hσ
    rw [Subgroup.sup_eq_closure] at hσ
    refine Subgroup.closure_induction (p := fun τ _ =>
      (show Gal(AlgebraicClosure K / K) from τ) x = x) ?mem ?one ?mul ?inv hσ
    · intro τ hτ
      rcases hτ with hτ | hτ
      · exact hxH τ hτ
      · exact hxJ τ hτ
    · rfl
    · intro τ η _ _ hτ hη
      change (show Gal(AlgebraicClosure K / K) from τ)
        ((show Gal(AlgebraicClosure K / K) from η) x) = x
      rw [hη, hτ]
    · intro τ _ hτ
      have h :=
        congrArg (fun y =>
          ((show Gal(AlgebraicClosure K / K) from τ)⁻¹) y) hτ
      simpa using h.symm

/-- Conjugate an arbitrary open subgroup of `G_K` through the finite-level
reverse Galois correspondence.  Its fixed field is the image of the original
finite fixed field under the chosen absolute Galois element. -/
def conjugateOpenSubgroupOfOpenSubgroup
    [IsGalois K (AlgebraicClosure K)]
    (σ : Gal(AlgebraicClosure K / K))
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    OpenSubgroup (Gal(AlgebraicClosure K / K)) := by
  let E : IntermediateField K (AlgebraicClosure K) :=
    fixedFieldOfOpenSubgroup K H
  haveI : FiniteDimensional K E :=
    fixedFieldOfOpenSubgroup.instFiniteDimensional K H
  let σ' : Gal(AlgebraicClosure K / K) := σ
  haveI : FiniteDimensional K (E.map σ'.toAlgHom) :=
    finiteDimensional_map_algEquiv σ' E
  exact openSubgroupOfFiniteIntermediateField K (E.map σ'.toAlgHom)

/-- The subgroup underlying the conjugate open subgroup is the pointwise
conjugate subgroup. -/
@[simp]
theorem conjugateOpenSubgroupOfOpenSubgroup_toSubgroup
    [IsGalois K (AlgebraicClosure K)]
    (σ : Gal(AlgebraicClosure K / K))
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    (conjugateOpenSubgroupOfOpenSubgroup K σ H :
      Subgroup (Gal(AlgebraicClosure K / K))) =
      Subgroup.map (MulAut.conj σ).toMonoidHom H.toSubgroup := by
  let E : IntermediateField K (AlgebraicClosure K) :=
    fixedFieldOfOpenSubgroup K H
  let σ' : Gal(AlgebraicClosure K / K) := σ
  change (E.map σ'.toAlgHom).fixingSubgroup =
    Subgroup.map (MulAut.conj σ').toMonoidHom H.toSubgroup
  calc
    (E.map σ'.toAlgHom).fixingSubgroup =
        (MulAut.conj σ') • E.fixingSubgroup :=
      IsGalois.map_fixingSubgroup E σ'
    _ = Subgroup.map (MulAut.conj σ').toMonoidHom E.fixingSubgroup := by
      ext τ
      rw [Subgroup.pointwise_smul_def]
      constructor <;> rintro ⟨η, hη, rfl⟩ <;> exact ⟨η, hη, rfl⟩
    _ = Subgroup.map (MulAut.conj σ').toMonoidHom H.toSubgroup := by
      rw [fixingSubgroup_fixedFieldOfOpenSubgroup K H]

/-- Membership in a conjugate arbitrary open subgroup can be tested by
conjugating the element back into the original open subgroup. -/
theorem mem_conjugateOpenSubgroupOfOpenSubgroup_iff
    [IsGalois K (AlgebraicClosure K)]
    (σ τ : Gal(AlgebraicClosure K / K))
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    τ ∈ conjugateOpenSubgroupOfOpenSubgroup K σ H ↔
      σ⁻¹ * τ * σ ∈ H := by
  change τ ∈ (conjugateOpenSubgroupOfOpenSubgroup K σ H :
      Subgroup (Gal(AlgebraicClosure K / K))) ↔
    σ⁻¹ * τ * σ ∈ H
  rw [conjugateOpenSubgroupOfOpenSubgroup_toSubgroup]
  constructor
  · rintro ⟨η, hη, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hη
  · intro hτ
    refine ⟨σ⁻¹ * τ * σ, hτ, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

/-- The fixed field of the conjugate open subgroup is the conjugate of the
finite fixed field. -/
@[simp]
theorem fixedFieldOfConjugateOpenSubgroupOfOpenSubgroup
    [IsGalois K (AlgebraicClosure K)]
    (σ : Gal(AlgebraicClosure K / K))
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    fixedFieldOfOpenSubgroup K
        (conjugateOpenSubgroupOfOpenSubgroup K σ H) =
      (fixedFieldOfOpenSubgroup K H).map
        (show Gal(AlgebraicClosure K / K) from σ).toAlgHom := by
  let E : IntermediateField K (AlgebraicClosure K) :=
    fixedFieldOfOpenSubgroup K H
  change fixedFieldOfOpenSubgroup K
      (openSubgroupOfFiniteIntermediateField K
        (E.map (show Gal(AlgebraicClosure K / K) from σ).toAlgHom)) =
    E.map (show Gal(AlgebraicClosure K / K) from σ).toAlgHom
  exact fixedFieldOfOpenSubgroup_openSubgroupOfFiniteIntermediateField K
    (E.map (show Gal(AlgebraicClosure K / K) from σ).toAlgHom)

/-- Conjugation carries the fixed field of an intersection of open subgroups
to the conjugate of the compositum of their fixed fields. -/
@[simp]
theorem fixedFieldOfConjugateOpenSubgroupOfOpenSubgroup_inf
    [IsGalois K (AlgebraicClosure K)]
    (σ : Gal(AlgebraicClosure K / K))
    (H J : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    fixedFieldOfOpenSubgroup K
        (conjugateOpenSubgroupOfOpenSubgroup K σ (H ⊓ J)) =
      (fixedFieldOfOpenSubgroup K H ⊔ fixedFieldOfOpenSubgroup K J).map
        (show Gal(AlgebraicClosure K / K) from σ).toAlgHom := by
  rw [fixedFieldOfConjugateOpenSubgroupOfOpenSubgroup,
    fixedFieldOfOpenSubgroup_inf]

/-- Conjugation carries the fixed field of the generated open subgroup to the
conjugate of the intersection of the fixed fields. -/
@[simp]
theorem fixedFieldOfConjugateOpenSubgroupOfOpenSubgroup_sup
    [IsGalois K (AlgebraicClosure K)]
    (σ : Gal(AlgebraicClosure K / K))
    (H J : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    fixedFieldOfOpenSubgroup K
        (conjugateOpenSubgroupOfOpenSubgroup K σ (H ⊔ J)) =
      (fixedFieldOfOpenSubgroup K H ⊓ fixedFieldOfOpenSubgroup K J).map
        (show Gal(AlgebraicClosure K / K) from σ).toAlgHom := by
  rw [fixedFieldOfConjugateOpenSubgroupOfOpenSubgroup,
    fixedFieldOfOpenSubgroup_sup]

/-- States the theorem `conjugateOpenSubgroupOfOpenSubgroup_one`. -/
@[simp]
theorem conjugateOpenSubgroupOfOpenSubgroup_one
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    conjugateOpenSubgroupOfOpenSubgroup K 1 H = H := by
  apply OpenSubgroup.toSubgroup_injective
  rw [conjugateOpenSubgroupOfOpenSubgroup_toSubgroup]
  ext τ
  simp

/-- States the theorem `conjugateOpenSubgroupOfOpenSubgroup_inf`. -/
@[simp]
theorem conjugateOpenSubgroupOfOpenSubgroup_inf
    [IsGalois K (AlgebraicClosure K)]
    (σ : Gal(AlgebraicClosure K / K))
    (H J : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    conjugateOpenSubgroupOfOpenSubgroup K σ (H ⊓ J) =
      conjugateOpenSubgroupOfOpenSubgroup K σ H ⊓
        conjugateOpenSubgroupOfOpenSubgroup K σ J := by
  apply OpenSubgroup.toSubgroup_injective
  rw [conjugateOpenSubgroupOfOpenSubgroup_toSubgroup]
  rw [OpenSubgroup.toSubgroup_inf, OpenSubgroup.toSubgroup_inf,
    conjugateOpenSubgroupOfOpenSubgroup_toSubgroup,
    conjugateOpenSubgroupOfOpenSubgroup_toSubgroup,
    Subgroup.map_inf]
  exact (MulAut.conj σ).injective

/-- States the theorem `conjugateOpenSubgroupOfOpenSubgroup_sup`. -/
@[simp]
theorem conjugateOpenSubgroupOfOpenSubgroup_sup
    [IsGalois K (AlgebraicClosure K)]
    (σ : Gal(AlgebraicClosure K / K))
    (H J : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    conjugateOpenSubgroupOfOpenSubgroup K σ (H ⊔ J) =
      conjugateOpenSubgroupOfOpenSubgroup K σ H ⊔
        conjugateOpenSubgroupOfOpenSubgroup K σ J := by
  apply OpenSubgroup.toSubgroup_injective
  rw [conjugateOpenSubgroupOfOpenSubgroup_toSubgroup]
  rw [OpenSubgroup.toSubgroup_sup, OpenSubgroup.toSubgroup_sup,
    conjugateOpenSubgroupOfOpenSubgroup_toSubgroup,
    conjugateOpenSubgroupOfOpenSubgroup_toSubgroup,
    Subgroup.map_sup]

/-- The normal core of an open subgroup of `G_K`, as an open normal subgroup.
This is the canonical finite Galois quotient lying below an arbitrary finite
level. -/
def openNormalCoreOfOpenSubgroup
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    OpenNormalSubgroup (Gal(AlgebraicClosure K / K)) where
  toOpenSubgroup :=
    ⟨H.toSubgroup.normalCore, by
      have : Finite (Gal(AlgebraicClosure K / K) ⧸ H.toSubgroup) :=
        Subgroup.quotient_finite_of_isOpen H.toSubgroup H.isOpen
      have : H.toSubgroup.normalCore.FiniteIndex :=
        normalCore_finiteIndex_of_finite_quotient H.toSubgroup
      exact Subgroup.isOpen_of_isClosed_of_finiteIndex H.toSubgroup.normalCore
        (Subgroup.normalCore_isClosed H.toSubgroup (by simpa using H.isClosed))⟩
  isNormal' := Subgroup.normalCore_normal H.toSubgroup

/-- States the theorem `openNormalCoreOfOpenSubgroup_toSubgroup`. -/
@[simp]
theorem openNormalCoreOfOpenSubgroup_toSubgroup
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    (openNormalCoreOfOpenSubgroup K H :
      Subgroup (Gal(AlgebraicClosure K / K))) = H.toSubgroup.normalCore :=
  rfl

/-- The normal core is contained in the original open subgroup. -/
theorem openNormalCoreOfOpenSubgroup_le
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    (openNormalCoreOfOpenSubgroup K H :
      Subgroup (Gal(AlgebraicClosure K / K))) ≤ H.toSubgroup := by
  rw [openNormalCoreOfOpenSubgroup_toSubgroup]
  exact Subgroup.normalCore_le H.toSubgroup

/-- The fixed field of an open normal subgroup is a finite Galois
intermediate field. -/
def fixedFieldOfOpenNormalSubgroup
    (H : OpenNormalSubgroup (Gal(AlgebraicClosure K / K))) :
    IntermediateField K (AlgebraicClosure K) :=
  fixedFieldOfOpenSubgroup K H.toOpenSubgroup

/-- States the theorem `fixedFieldOfOpenNormalSubgroup_def`. -/
@[simp]
theorem fixedFieldOfOpenNormalSubgroup_def
    (H : OpenNormalSubgroup (Gal(AlgebraicClosure K / K))) :
    fixedFieldOfOpenNormalSubgroup K H =
      IntermediateField.fixedField H.toSubgroup :=
  rfl

/-- Provides the instance `instFiniteDimensional`. -/
instance fixedFieldOfOpenNormalSubgroup.instFiniteDimensional
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenNormalSubgroup (Gal(AlgebraicClosure K / K))) :
    FiniteDimensional K (fixedFieldOfOpenNormalSubgroup K H) :=
  fixedFieldOfOpenSubgroup.instFiniteDimensional K H.toOpenSubgroup

/-- States the theorem `isGalois_fixedFieldOfOpenNormalSubgroup`. -/
theorem isGalois_fixedFieldOfOpenNormalSubgroup
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenNormalSubgroup (Gal(AlgebraicClosure K / K))) :
    IsGalois K (fixedFieldOfOpenNormalSubgroup K H) := by
  refine (InfiniteGalois.normal_iff_isGalois
    (K := AlgebraicClosure K) (fixedFieldOfOpenNormalSubgroup K H)).1 ?_
  change (fixedFieldOfOpenSubgroup K H.toOpenSubgroup).fixingSubgroup.Normal
  rw [fixingSubgroup_fixedFieldOfOpenSubgroup K H.toOpenSubgroup]
  infer_instance

/-- Provides the instance `instNormal`. -/
instance fixedFieldOfOpenNormalSubgroup.instNormal
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenNormalSubgroup (Gal(AlgebraicClosure K / K))) :
    Normal K (fixedFieldOfOpenNormalSubgroup K H) := by
  have : IsGalois K (fixedFieldOfOpenNormalSubgroup K H) :=
    isGalois_fixedFieldOfOpenNormalSubgroup K H
  infer_instance

/-- The finite Galois quotient attached to an arbitrary open normal subgroup
of `G_K`. -/
def quotientOpenNormalSubgroupEquivGalFixedField
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenNormalSubgroup (Gal(AlgebraicClosure K / K))) :
    Gal(AlgebraicClosure K / K) ⧸ H.toSubgroup ≃*
      Gal(fixedFieldOfOpenNormalSubgroup K H / K) := by
  let Hc : ClosedSubgroup (Gal(AlgebraicClosure K / K)) :=
    closedSubgroupOfOpenSubgroup K H.toOpenSubgroup
  haveI : Hc.Normal := by
    change H.toSubgroup.Normal
    infer_instance
  exact InfiniteGalois.normalAutEquivQuotient Hc

/-- States the theorem `quotientOpenNormalSubgroupEquivGalFixedField_mk'`. -/
@[simp]
theorem quotientOpenNormalSubgroupEquivGalFixedField_mk'
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenNormalSubgroup (Gal(AlgebraicClosure K / K)))
    (σ : Gal(AlgebraicClosure K / K)) :
    quotientOpenNormalSubgroupEquivGalFixedField K H
        (QuotientGroup.mk' H.toSubgroup σ) =
      AlgEquiv.restrictNormalHom
        (fixedFieldOfOpenNormalSubgroup K H) σ := by
  let Hc : ClosedSubgroup (Gal(AlgebraicClosure K / K)) :=
    closedSubgroupOfOpenSubgroup K H.toOpenSubgroup
  have : Hc.Normal := by
    change H.toSubgroup.Normal
    infer_instance
  change InfiniteGalois.normalAutEquivQuotient Hc
      (QuotientGroup.mk' Hc.toSubgroup σ) =
    AlgEquiv.restrictNormalHom (IntermediateField.fixedField Hc.toSubgroup) σ
  exact InfiniteGalois.normalAutEquivQuotient_apply Hc σ

/-- Passing from an open subgroup to its normal core corresponds on fixed
fields to taking the normal closure. -/
theorem fixedFieldOfOpenNormalCoreOfOpenSubgroup
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    fixedFieldOfOpenNormalSubgroup K
        (openNormalCoreOfOpenSubgroup K H) =
      IntermediateField.normalClosure K (fixedFieldOfOpenSubgroup K H)
        (AlgebraicClosure K) := by
  let E : IntermediateField K (AlgebraicClosure K) :=
    fixedFieldOfOpenSubgroup K H
  let C : OpenNormalSubgroup (Gal(AlgebraicClosure K / K)) :=
    openNormalCoreOfOpenSubgroup K H
  apply intermediateField_eq_of_fixingSubgroup_eq K
  change (fixedFieldOfOpenSubgroup K C.toOpenSubgroup).fixingSubgroup =
    (IntermediateField.normalClosure K E (AlgebraicClosure K)).fixingSubgroup
  rw [fixingSubgroup_fixedFieldOfOpenSubgroup K C.toOpenSubgroup]
  change H.toSubgroup.normalCore =
    (IntermediateField.normalClosure K E (AlgebraicClosure K)).fixingSubgroup
  apply le_antisymm
  · have hE_le_core :
        E ≤ fixedFieldOfOpenNormalSubgroup K C := by
      change fixedFieldOfOpenSubgroup K H ≤
        fixedFieldOfOpenSubgroup K C.toOpenSubgroup
      exact fixedFieldOfOpenSubgroup_le_of_le K C.toOpenSubgroup H
        (openNormalCoreOfOpenSubgroup_le K H)
    have : Normal K (fixedFieldOfOpenNormalSubgroup K C) := by
      infer_instance
    have hcl :
        IntermediateField.normalClosure K E (AlgebraicClosure K) ≤
          fixedFieldOfOpenNormalSubgroup K C := by
      exact (IntermediateField.normalClosure_le_iff_of_normal
        (K₁ := E) (K₂ := fixedFieldOfOpenNormalSubgroup K C)).2 hE_le_core
    have hfix :
        (fixedFieldOfOpenNormalSubgroup K C).fixingSubgroup ≤
          (IntermediateField.normalClosure K E
            (AlgebraicClosure K)).fixingSubgroup :=
      IntermediateField.fixingSubgroup_le hcl
    change H.toSubgroup.normalCore ≤
      (IntermediateField.normalClosure K E
        (AlgebraicClosure K)).fixingSubgroup
    rw [← openNormalCoreOfOpenSubgroup_toSubgroup K H,
      ← fixingSubgroup_fixedFieldOfOpenSubgroup K C.toOpenSubgroup]
    exact hfix
  · have hNleH :
        (IntermediateField.normalClosure K E
          (AlgebraicClosure K)).fixingSubgroup ≤ H.toSubgroup := by
      rw [← fixingSubgroup_fixedFieldOfOpenSubgroup K H]
      exact IntermediateField.fixingSubgroup_le
        (IntermediateField.le_normalClosure E)
    have : IsGalois K
        (IntermediateField.normalClosure K E (AlgebraicClosure K)) := by
      infer_instance
    have :
        ((IntermediateField.normalClosure K E
          (AlgebraicClosure K)).fixingSubgroup).Normal := by
      infer_instance
    exact (Subgroup.normal_le_normalCore
      (H := H.toSubgroup)
      (N := (IntermediateField.normalClosure K E
        (AlgebraicClosure K)).fixingSubgroup)).2 hNleH

/-- Normal core is invariant under conjugating the original open subgroup,
expressed on fixed fields. -/
@[simp]
theorem fixedFieldOfOpenNormalCoreOfConjugateOpenSubgroupOfOpenSubgroup
    [IsGalois K (AlgebraicClosure K)]
    (σ : Gal(AlgebraicClosure K / K))
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    fixedFieldOfOpenNormalSubgroup K
        (openNormalCoreOfOpenSubgroup K
          (conjugateOpenSubgroupOfOpenSubgroup K σ H)) =
      fixedFieldOfOpenNormalSubgroup K
        (openNormalCoreOfOpenSubgroup K H) := by
  rw [fixedFieldOfOpenNormalCoreOfOpenSubgroup,
    fixedFieldOfConjugateOpenSubgroupOfOpenSubgroup,
    IntermediateField.normalClosure_map_eq,
    fixedFieldOfOpenNormalCoreOfOpenSubgroup]

end absoluteGaloisGroup
end Field

end

end RamificationTheory
