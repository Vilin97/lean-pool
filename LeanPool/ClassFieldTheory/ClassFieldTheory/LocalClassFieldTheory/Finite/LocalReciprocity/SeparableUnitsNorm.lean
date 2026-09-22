/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.RingTheory.Norm.Transitivity
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.TateH0.NormImage

/-! # Separable Units Norm -/
namespace LocalClassFieldTheory
open RamificationTheory KummerTheory

open LocalFieldTheory

open ClassFormation CyclicCohomology

/-!
# Finite local reciprocity: the abstract norm on separable-closure units

The coefficient module in local class field theory is the unit group of a
separable closure.  This file compares the norm defined in the abstract class-formation framework by
  a
sum over abstract Galois cosets with the ordinary field norm.  The comparison
is proved first for an arbitrary (possibly infinite) Galois ambient field, so
it does not require the ground field to be perfect.
-/

noncomputable section

open scoped BigOperators

variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

/-- Canonical identification of `Kˣ` with the coefficient group fixed by the
full absolute Galois group. -/
def baseUnitsEquivGaloisAmbientFixed :
    Additive Kˣ ≃+ ambientFixedAddSubgroup
      (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)) := by
  let eBot : Additive Kˣ ≃+
      Additive (⊥ : IntermediateField K Ω)ˣ :=
    MulEquiv.toAdditive
      (Units.mapEquiv (IntermediateField.botEquiv K Ω).symm.toMulEquiv)
  exact eBot.trans
    (intermediateFieldUnitsEquivGaloisFixed K Ω ⊥)

/-- States the theorem `baseUnitsEquivGaloisAmbientFixed_val`. -/
@[simp]
theorem baseUnitsEquivGaloisAmbientFixed_val (x : Kˣ) :
    ((Additive.toMul
      ((baseUnitsEquivGaloisAmbientFixed K Ω (Additive.ofMul x)).1 :
        Additive Ωˣ) : Ωˣ) : Ω) = algebraMap K Ω (x : K) := by
  rfl

section FiniteGaloisIntermediate

variable (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]

/-- Provides the instance `baseFixingExtensionQuotient_finite`. -/
noncomputable instance baseFixingExtensionQuotient_finite :
    Finite ((closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E)
        (fixingSubgroupLeBase K Ω E)) :=
  (baseFixingExtensionQuotientEquivGaloisGroup K Ω E).toEquiv.finite_iff.mpr
    inferInstance

omit [FiniteDimensional K E] in
/-- States the theorem `relativeCosetAction_intermediateFieldUnit_val`. -/
theorem relativeCosetAction_intermediateFieldUnit_val
    (x : Eˣ)
    (q : (closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E)
        (fixingSubgroupLeBase K Ω E)) :
    ((Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) q) : Ωˣ) : Ω) =
      E.val ((baseFixingExtensionQuotientEquivGaloisGroup K Ω E q) (x : E)) := by
  refine Quotient.inductionOn' q ?_
  intro σ
  rw [relativeCosetAction_mk]
  change σ.1 (E.val (x : E)) =
    E.val ((baseFixingExtensionQuotientEquivGaloisGroup K Ω E
      (QuotientGroup.mk' _ σ)) (x : E))
  have hq :
      baseFixingExtensionQuotientEquivAmbient K Ω E
          (QuotientGroup.mk' _ σ) =
        QuotientGroup.mk' (closedFixingSubgroup K Ω E).toSubgroup σ.1 := by
    rfl
  have hn := InfiniteGalois.normalAutEquivQuotient_apply
    (closedFixingSubgroup K Ω E) σ.1
  change InfiniteGalois.normalAutEquivQuotient (closedFixingSubgroup K Ω E)
      (QuotientGroup.mk' _ σ.1) = _ at hn
  rw [baseFixingExtensionQuotientEquivGaloisGroup, MulEquiv.trans_apply, hq,
    MulEquiv.trans_apply, hn, AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, IntermediateField.equivOfEq_symm,
    IntermediateField.equivOfEq_apply]
  change σ.1 (E.val (x : E)) =
    (((AlgEquiv.restrictNormalHom
      (IntermediateField.fixedField
        (closedFixingSubgroup K Ω E).toSubgroup) σ.1)
      ⟨E.val (x : E), _⟩ : IntermediateField.fixedField
        (closedFixingSubgroup K Ω E).toSubgroup) : Ω)
  rw [AlgEquiv.restrictNormalHom_apply]

/-- On units coming from a finite Galois intermediate field, the abstract
relative norm is the ordinary field norm. -/
theorem relativeNorm_intermediateFieldUnit_val (x : Eˣ) :
    ((Additive.toMul
      ((relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
      algebraMap K Ω (Algebra.norm K (x : E)) := by
  let Q := (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup ⧸
    extensionSubgroup
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E)
      (fixingSubgroupLeBase K Ω E)
  let := Fintype.ofFinite Q
  change
    ((Additive.toMul
      (relativeNormValue (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x))) : Ωˣ) : Ω) = _
  rw [relativeNormValue]
  let action : Q → Additive Ωˣ := fun q =>
    relativeCosetAction (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
      (intermediateFieldUnitsEquivGaloisFixed K Ω E
        (Additive.ofMul x)) q
  change (↑(Additive.toMul (∑ q : Q, action q)) : Ω) = _
  rw [toMul_sum]
  change (Units.coeHom Ω) (∏ q : Q, Additive.toMul (action q)) = _
  rw [map_prod]
  change
    (∏ q : Q,
      ((Additive.toMul
        (relativeCosetAction (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
          (intermediateFieldUnitsEquivGaloisFixed K Ω E
            (Additive.ofMul x)) q) : Ωˣ) : Ω)) = _
  calc
    _ = ∏ σ : Gal(E/K), E.val (σ (x : E)) := by
      exact Fintype.prod_equiv
        (baseFixingExtensionQuotientEquivGaloisGroup K Ω E).toEquiv
        (fun q : Q => ((Additive.toMul (action q) : Ωˣ) : Ω))
        (fun σ : Gal(E/K) => E.val (σ (x : E)))
        (relativeCosetAction_intermediateFieldUnit_val K Ω E x)
    _ = E.val (algebraMap K E (Algebra.norm K (x : E))) := by
      rw [Algebra.norm_eq_prod_automorphisms, map_prod]
    _ = algebraMap K Ω (Algebra.norm K (x : E)) := rfl

/-- Equivariant form of the norm comparison, with both fixed coefficient
groups identified with the corresponding field unit groups. -/
theorem relativeNorm_intermediateFieldUnit (x : Eˣ) :
    relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) =
      baseUnitsEquivGaloisAmbientFixed K Ω
        (Additive.ofMul (normUnits K E x)) := by
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  exact relativeNorm_intermediateFieldUnit_val K Ω E x

/-- Under the base-field fixed-unit equivalence, the abstract finite norm
subgroup is exactly the ordinary field-norm subgroup. -/
theorem map_finiteNormSubgroup_eq_additiveNormSubgroup :
    (finiteNormSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)).map
        (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom =
      additiveNormSubgroup K E := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ⟨b, rfl⟩
    let u : Eˣ := Additive.toMul
      ((intermediateFieldUnitsEquivGaloisFixed K Ω E).symm b)
    have hb :
        intermediateFieldUnitsEquivGaloisFixed K Ω E
            (Additive.ofMul u) = b := by
      change intermediateFieldUnitsEquivGaloisFixed K Ω E
          ((intermediateFieldUnitsEquivGaloisFixed K Ω E).symm b) = b
      exact (intermediateFieldUnitsEquivGaloisFixed K Ω E).apply_symm_apply b
    rw [← hb, relativeNorm_intermediateFieldUnit]
    change (baseUnitsEquivGaloisAmbientFixed K Ω).symm
      (baseUnitsEquivGaloisAmbientFixed K Ω
        (Additive.ofMul (normUnits K E u))) ∈ additiveNormSubgroup K E
    rw [(baseUnitsEquivGaloisAmbientFixed K Ω).symm_apply_apply]
    exact ⟨u, rfl⟩
  · intro hy
    change Additive.toMul y ∈ localNormSubgroup K E at hy
    rcases hy with ⟨u, hu⟩
    refine ⟨baseUnitsEquivGaloisAmbientFixed K Ω
      (Additive.ofMul (normUnits K E u)), ?_, ?_⟩
    · refine ⟨intermediateFieldUnitsEquivGaloisFixed K Ω E
        (Additive.ofMul u), ?_⟩
      exact relativeNorm_intermediateFieldUnit K Ω E u
    · change (baseUnitsEquivGaloisAmbientFixed K Ω).symm
        (baseUnitsEquivGaloisAmbientFixed K Ω
          (Additive.ofMul (normUnits K E u))) = y
      rw [(baseUnitsEquivGaloisAmbientFixed K Ω).symm_apply_apply]
      exact congrArg Additive.ofMul hu

/-- The abstract finite norm quotient is the actual multiplicative field
norm quotient, written additively for the abstract class-formation API. -/
def finiteNormQuotientEquivNormQuotient :
    FiniteNormQuotient (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E) ≃+
      Additive (NormQuotient K E) := by
  let S := finiteNormSubgroup (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
  let normAdd : Additive Kˣ →+ Additive (NormQuotient K E) :=
    MonoidHom.toAdditive (normClass K E)
  let T := normAdd.ker
  let e := baseUnitsEquivGaloisAmbientFixed K Ω
  have hmap : S.map e.symm.toAddMonoidHom = T := by
    simpa [S, T, normAdd, e] using
      (map_finiteNormSubgroup_eq_additiveNormSubgroup K Ω E).trans
        (additiveNormSubgroup_eq_ker_quotient_map K E)
  have hforward : S ≤ AddSubgroup.comap e.symm.toAddMonoidHom T := by
    intro x hx
    change e.symm x ∈ T
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hinverse : T ≤ AddSubgroup.comap e.toAddMonoidHom S := by
    intro y hy
    change e y ∈ S
    have hy' : y ∈ S.map e.symm.toAddMonoidHom := by
      rw [hmap]
      exact hy
    rcases hy' with ⟨x, hx, hxy⟩
    have heq : e y = x := by
      apply e.symm.injective
      simpa using hxy.symm
    rw [heq]
    exact hx
  let f : (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)) ⧸ S) →+
      (Additive Kˣ ⧸ T) :=
    QuotientAddGroup.map S T e.symm.toAddMonoidHom hforward
  let g : (Additive Kˣ ⧸ T) →+
      (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)) ⧸ S) :=
    QuotientAddGroup.map T S e.toAddMonoidHom hinverse
  let modelEquiv :
      (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)) ⧸ S) ≃+
        (Additive Kˣ ⧸ T) :=
    { toFun := f
      invFun := g
      left_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        change ↑(e (e.symm x)) = (↑x :
          ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
            (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)) ⧸ S)
        rw [e.apply_symm_apply]
      right_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        change ↑(e.symm (e x)) = (↑x : Additive Kˣ ⧸ T)
        rw [e.symm_apply_apply]
      map_add' := f.map_add }
  let firstIso : (Additive Kˣ ⧸ T) ≃+ Additive (NormQuotient K E) :=
    QuotientAddGroup.quotientKerEquivOfSurjective normAdd
      (QuotientGroup.mk'_surjective (localNormSubgroup K E))
  exact (finiteNormQuotientConcreteEquiv (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)).trans
      (modelEquiv.trans firstIso)

/-- The fixed-unit comparison carries the canonical finite norm class to the
canonical field norm class.  The concrete quotient representation remains
private to the proof of this boundary theorem. -/
@[simp]
theorem finiteNormQuotientEquivNormQuotient_finiteNormClass
    (a : ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))) :
    finiteNormQuotientEquivNormQuotient K Ω E
        (finiteNormClass (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E) a) =
      (MonoidHom.toAdditive (normClass K E))
        ((baseUnitsEquivGaloisAmbientFixed K Ω).symm a) := by
  let S := finiteNormSubgroup (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
  let normAdd : Additive Kˣ →+ Additive (NormQuotient K E) :=
    MonoidHom.toAdditive (normClass K E)
  let T := normAdd.ker
  let e := baseUnitsEquivGaloisAmbientFixed K Ω
  have hmap : S.map e.symm.toAddMonoidHom = T := by
    simpa [S, T, normAdd, e] using
      (map_finiteNormSubgroup_eq_additiveNormSubgroup K Ω E).trans
        (additiveNormSubgroup_eq_ker_quotient_map K E)
  have hforward : S ≤ AddSubgroup.comap e.symm.toAddMonoidHom T := by
    intro x hx
    change e.symm x ∈ T
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  simp only [finiteNormQuotientEquivNormQuotient,
    finiteNormQuotientConcreteEquiv_finiteNormClass,
    AddEquiv.trans_apply,
    QuotientAddGroup.quotientKerEquivOfSurjective,
    QuotientAddGroup.quotientKerEquivOfRightInverse]
  change QuotientAddGroup.kerLift normAdd
      (QuotientAddGroup.map S T e.symm.toAddMonoidHom hforward
        (QuotientAddGroup.mk' S a)) = normAdd (e.symm a)
  rw [QuotientAddGroup.map_mk', QuotientAddGroup.kerLift_mk]
  rfl

end FiniteGaloisIntermediate

section EmbeddedFiniteGaloisExtension

variable (L : Type) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (i : L →ₐ[K] Ω)

noncomputable local instance embeddedFieldRangeFiniteDimensional :
    FiniteDimensional K (AlgHom.fieldRange i) :=
  (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional

noncomputable local instance embeddedFieldRangeIsGalois :
    IsGalois K (AlgHom.fieldRange i) :=
  IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField i)

omit [IsGalois K Ω] [FiniteDimensional K L] [IsGalois K L] in
/-- The field norm is invariant under an algebra equivalence, at unit level. -/
theorem normUnits_embeddedExtensionAlgEquiv (x : Lˣ) :
    normUnits K (AlgHom.fieldRange i)
        (Units.mapEquiv (AlgEquiv.ofInjectiveField i).toMulEquiv x) =
      normUnits K L x := by
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv
    (AlgEquiv.ofInjectiveField i) (x : L)

omit [IsGalois K Ω] [FiniteDimensional K L] [IsGalois K L] in
/-- The ordinary norm subgroups are independent of the chosen realization of
the finite extension inside the ambient Galois extension. -/
theorem localNormSubgroup_fieldRange_eq :
    localNormSubgroup K (AlgHom.fieldRange i) = localNormSubgroup K L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    let z : Lˣ := Units.mapEquiv
      (AlgEquiv.ofInjectiveField i).symm.toMulEquiv y
    refine ⟨z, ?_⟩
    have hz : Units.mapEquiv
        (AlgEquiv.ofInjectiveField i).toMulEquiv z = y := by
      exact (Units.mapEquiv
        (AlgEquiv.ofInjectiveField i).toMulEquiv).apply_symm_apply y
    rw [← hz, normUnits_embeddedExtensionAlgEquiv]
  · rintro ⟨x, rfl⟩
    refine ⟨Units.mapEquiv
      (AlgEquiv.ofInjectiveField i).toMulEquiv x, ?_⟩
    exact normUnits_embeddedExtensionAlgEquiv K Ω L i x

/-- The abstract relative norm attached to an embedded finite Galois
extension is the actual field norm on its unit group. -/
theorem relativeNorm_embeddedExtensionUnit (x : Lˣ) :
    relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω (AlgHom.fieldRange i))
        (fixingSubgroupLeBase K Ω (AlgHom.fieldRange i))
        (embeddedFieldUnitsEquivGaloisFixed K Ω L i (Additive.ofMul x)) =
      baseUnitsEquivGaloisAmbientFixed K Ω
        (Additive.ofMul (normUnits K L x)) := by
  let e : L ≃ₐ[K] i.fieldRange := AlgEquiv.ofInjectiveField i
  let y : i.fieldRangeˣ := Units.mapEquiv e.toMulEquiv x
  exact (relativeNorm_intermediateFieldUnit K Ω i.fieldRange y).trans
    (congrArg (fun u : Kˣ =>
      baseUnitsEquivGaloisAmbientFixed K Ω (Additive.ofMul u))
      (normUnits_embeddedExtensionAlgEquiv K Ω L i x))

/-- For an embedded finite Galois extension `L/K`, the finite norm quotient
in the abstract class formation is the actual quotient `Kˣ/N_{L/K}Lˣ`. -/
def finiteNormQuotientEquivEmbeddedNormQuotient :
    FiniteNormQuotient (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω (AlgHom.fieldRange i))
        (fixingSubgroupLeBase K Ω (AlgHom.fieldRange i)) ≃+
      Additive (NormQuotient K L) :=
  (finiteNormQuotientEquivNormQuotient K Ω (AlgHom.fieldRange i)).trans
    (MulEquiv.toAdditive
      (normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
        (localNormSubgroup_fieldRange_eq K Ω L i)))

/-- The embedded-extension comparison carries a canonical finite norm class
to the corresponding field norm class, followed by the canonical transport
from the embedded field range to `L`. -/
@[simp]
theorem finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass
    (a : ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))) :
    finiteNormQuotientEquivEmbeddedNormQuotient K Ω L i
        (finiteNormClass (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup K Ω (AlgHom.fieldRange i))
          (fixingSubgroupLeBase K Ω (AlgHom.fieldRange i)) a) =
      (MulEquiv.toAdditive
        (normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
          (localNormSubgroup_fieldRange_eq K Ω L i)))
        ((MonoidHom.toAdditive (normClass K (AlgHom.fieldRange i)))
          ((baseUnitsEquivGaloisAmbientFixed K Ω).symm a)) := by
  change (MulEquiv.toAdditive
      (normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
        (localNormSubgroup_fieldRange_eq K Ω L i)))
      (finiteNormQuotientEquivNormQuotient K Ω (AlgHom.fieldRange i)
        (finiteNormClass (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup K Ω (AlgHom.fieldRange i))
          (fixingSubgroupLeBase K Ω (AlgHom.fieldRange i)) a)) = _
  rw [finiteNormQuotientEquivNormQuotient_finiteNormClass]

end EmbeddedFiniteGaloisExtension

end
end LocalClassFieldTheory
