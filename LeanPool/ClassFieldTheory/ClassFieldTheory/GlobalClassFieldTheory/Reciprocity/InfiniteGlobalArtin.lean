/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicZHatBaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtin
import Mathlib.FieldTheory.Galois.Profinite
/-!
# The infinite global Artin homomorphism

This file assembles the finite global Artin homomorphisms in the
`FiniteGaloisIntermediateField` inverse limit supplied by mathlib.  The
first target is the actual `ZHat`-extension of `ℚ` constructed in
`CyclotomicZHatBaseChange`.

The positive archimedean section below is the cyclotomic normalization device:
multiplying an idele by the section of its absolute
norm produces a norm-one idele without changing its Artin symbol.
-/

open scoped IsMulCommutative NNReal NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp

open scoped Classical in
/-- Every infinite place of `ℚ` is the canonical real place. -/
theorem rationalInfinitePlace_isReal
    (v : InfinitePlace ℚ) :
    v.IsReal := by
  rw [Subsingleton.elim v Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

open scoped Classical in
private noncomputable def rationalPositiveArchimedeanLocalComponent
    (v : InfinitePlace ℚ) :
    ℝ≥0ˣ →* v.Completionˣ :=
  (Units.mapEquiv
      (InfinitePlace.Completion.ringEquivRealOfIsReal
        (rationalInfinitePlace_isReal v)).symm.toMulEquiv).toMonoidHom.comp
    (Units.map NNReal.toRealHom.toMonoidHom)

open scoped Classical in
private noncomputable def rationalPositiveArchimedeanInfinitePart :
    ℝ≥0ˣ →* InfiniteIdeleGroup ℚ :=
  ContinuousMulEquiv.piUnits.symm.toMonoidHom.comp
    (MonoidHom.pi rationalPositiveArchimedeanLocalComponent)

open scoped Classical in
private theorem rationalPositiveArchimedeanInfinitePart_component
    (r : ℝ≥0ˣ) (v : InfinitePlace ℚ) :
    ContinuousMulEquiv.piUnits
        (rationalPositiveArchimedeanInfinitePart r) v =
      rationalPositiveArchimedeanLocalComponent v r := by
  change
    ContinuousMulEquiv.piUnits
        (ContinuousMulEquiv.piUnits.symm
          ((MonoidHom.pi rationalPositiveArchimedeanLocalComponent) r)) v =
      rationalPositiveArchimedeanLocalComponent v r
  exact congrFun
    (ContinuousMulEquiv.piUnits.apply_symm_apply
      ((MonoidHom.pi rationalPositiveArchimedeanLocalComponent) r)) v

open scoped Classical in
/-- The positive archimedean section
`ℝ₊ˣ → I_ℚ`.  Its finite component is one, and at the unique infinite
place it is the positive real unit supplied by the input. -/
noncomputable def rationalPositiveArchimedeanIdele :
    ℝ≥0ˣ →* IdeleGroup ℚ := by
  exact
    { toFun := fun r =>
        (rationalPositiveArchimedeanInfinitePart r, 1)
      map_one' := by simp
      map_mul' := by simp }

open scoped Classical in
/-- The positive archimedean section has trivial finite component at
every finite place of `ℚ`. -/
theorem rationalPositiveArchimedeanIdele_finiteComponent
    (r : ℝ≥0ˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    IdeleGroup.finiteComponent v
        (rationalPositiveArchimedeanIdele r) =
      1 :=
  rfl

open scoped Classical in
/-- At the unique rational infinite place, the positive section becomes
the original positive real unit under mathlib's canonical completion
equivalence. -/
theorem rationalPositiveArchimedeanIdele_infiniteComponent
    (r : ℝ≥0ˣ) :
    Units.mapEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace).toMulEquiv
        (IdeleGroup.infiniteComponent Rat.infinitePlace
          (rationalPositiveArchimedeanIdele r)) =
      Units.map NNReal.toRealHom.toMonoidHom r := by
  change
    Units.mapEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace).toMulEquiv
        (ContinuousMulEquiv.piUnits
          (rationalPositiveArchimedeanInfinitePart r)
          Rat.infinitePlace) =
      Units.map NNReal.toRealHom.toMonoidHom r
  rw [rationalPositiveArchimedeanInfinitePart_component]
  let e :=
    (InfinitePlace.Completion.ringEquivRealOfIsReal
      Rat.isReal_infinitePlace).toMulEquiv
  change
    Units.mapEquiv e
        (Units.mapEquiv e.symm
          (Units.map NNReal.toRealHom.toMonoidHom r)) =
      Units.map NNReal.toRealHom.toMonoidHom r
  rw [← Units.mapEquiv_symm]
  exact
    (Units.mapEquiv e).apply_symm_apply
      (Units.map NNReal.toRealHom.toMonoidHom r)

open scoped Classical in
/-- The positive archimedean section has absolute idele norm `r⁻¹`.
This is the normalization dictated by the convention in
`IdeleGroup.absoluteNorm`. -/
theorem rationalPositiveArchimedeanIdele_absoluteNorm
    (r : ℝ≥0ˣ) :
    IdeleGroup.absoluteNorm
        (rationalPositiveArchimedeanIdele r) =
      r⁻¹ := by
  have hcomponent :=
    congrArg Units.val
      (rationalPositiveArchimedeanIdele_infiniteComponent r)
  have hcomponent' :
      InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace
          ((IdeleGroup.infiniteComponent Rat.infinitePlace
            (rationalPositiveArchimedeanIdele r) :
              Rat.infinitePlace.Completionˣ) :
            Rat.infinitePlace.Completion) =
        ((r : ℝ≥0ˣ) : ℝ) := by
    simpa using hcomponent
  have hlocalNorm :
      ‖((IdeleGroup.infiniteComponent Rat.infinitePlace
          (rationalPositiveArchimedeanIdele r) :
            Rat.infinitePlace.Completionˣ) :
          Rat.infinitePlace.Completion)‖₊ =
        (r : ℝ≥0) := by
    apply NNReal.eq
    simp only [coe_nnnorm]
    calc
      ‖((IdeleGroup.infiniteComponent Rat.infinitePlace
          (rationalPositiveArchimedeanIdele r) :
            Rat.infinitePlace.Completionˣ) :
          Rat.infinitePlace.Completion)‖ =
          ‖InfinitePlace.Completion.ringEquivRealOfIsReal
            Rat.isReal_infinitePlace
            ((IdeleGroup.infiniteComponent Rat.infinitePlace
              (rationalPositiveArchimedeanIdele r) :
                Rat.infinitePlace.Completionˣ) :
              Rat.infinitePlace.Completion)‖ :=
        ((InfinitePlace.Completion.isometryEquivRealOfIsReal
          Rat.isReal_infinitePlace).isometry.norm_map_of_map_zero
          (map_zero
            (InfinitePlace.Completion.ringEquivRealOfIsReal
              Rat.isReal_infinitePlace))
          _).symm
      _ = ‖((r : ℝ≥0ˣ) : ℝ)‖ := by
        rw [hcomponent']
      _ = ((r : ℝ≥0ˣ) : ℝ) :=
        Real.norm_of_nonneg (r : ℝ≥0).coe_nonneg
  have hinfinite :
      InfiniteIdeleGroup.archimedeanNorm
          (rationalPositiveArchimedeanIdele r).1 =
        r := by
    rw [InfiniteIdeleGroup.archimedeanNorm_apply,
      Fintype.prod_unique]
    rw [show
      (default : InfinitePlace ℚ) = Rat.infinitePlace by
        exact Subsingleton.elim _ _,
      InfinitePlace.mult_isReal
      ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩,
      pow_one]
    apply Units.ext
    exact hlocalNorm
  rw [IdeleGroup.absoluteNorm_apply]
  change
    FiniteIdeleGroup.absoluteNorm (1 : FiniteIdeleGroup ℚ) *
        (InfiniteIdeleGroup.archimedeanNorm
          (rationalPositiveArchimedeanIdele r).1)⁻¹ =
      r⁻¹
  rw [map_one, hinfinite, one_mul]

open scoped Classical in
/-- Every finite abelian global Artin homomorphism kills the positive
archimedean section over `ℚ`. -/
theorem globalArtinMonoidHom_rationalPositiveArchimedeanIdele
    {L : Type}
    [Field L] [NumberField L] [Algebra ℚ L]
    [IsAbelianGalois ℚ L]
    (r : ℝ≥0ˣ) :
    globalArtinMonoidHom
        (K := ℚ) (L := L)
        (rationalPositiveArchimedeanIdele r) =
      1 := by
  have hcomponent :=
    congrArg Units.val
      (rationalPositiveArchimedeanIdele_infiniteComponent r)
  have hpos :
      0 <
        InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace
          ((IdeleGroup.infiniteComponent Rat.infinitePlace
            (rationalPositiveArchimedeanIdele r) :
              Rat.infinitePlace.Completionˣ) :
            Rat.infinitePlace.Completion) := by
    have hvalue :
        InfinitePlace.Completion.ringEquivRealOfIsReal
            Rat.isReal_infinitePlace
            ((IdeleGroup.infiniteComponent Rat.infinitePlace
              (rationalPositiveArchimedeanIdele r) :
                Rat.infinitePlace.Completionˣ) :
              Rat.infinitePlace.Completion) =
          ((r : ℝ≥0ˣ) : ℝ) := by
      simpa using hcomponent
    rw [hvalue]
    exact
      NNReal.coe_pos.mpr
        (pos_iff_ne_zero.mpr (Units.ne_zero r))
  rw [globalArtinMonoidHom_apply]
  have hinfinite :
      (∏ v : InfinitePlace ℚ,
        chosenInfinitePlaceArtinMonoidHom
          (K := ℚ) (L := L) v
          (IdeleGroup.infiniteComponent v
            (rationalPositiveArchimedeanIdele r))) =
        1 := by
    rw [Fintype.prod_unique,
      show
        (default : InfinitePlace ℚ) = Rat.infinitePlace by
          exact Subsingleton.elim _ _]
    exact
      chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
        (K := ℚ) (L := L)
        Rat.infinitePlace Rat.isReal_infinitePlace _ hpos
  have hfinite :
      (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        chosenFinitePlaceArtinMonoidHom
          (K := ℚ) (L := L) v
          (IdeleGroup.finiteComponent v
            (rationalPositiveArchimedeanIdele r))) =
        1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [rationalPositiveArchimedeanIdele_finiteComponent,
      map_one]
  rw [hinfinite, hfinite, mul_one]

/-!
## Assembly in the finite-Galois inverse limit

The following construction is the global analogue of LCFT's
`residueFrobeniusToLimit`: its coordinates are the actual finite global
Artin homomorphisms, and compatibility is restriction in a finite
abelian tower.
-/

open scoped Classical in
/-- The compatible family of finite global Artin symbols attached to
an idele, regarded as a point of the finite-Galois inverse limit. -/
noncomputable def infiniteGlobalArtinLimitPoint
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) :
    limit
      (InfiniteGalois.asProfiniteGaloisGroupFunctor
        K Ω) := by
  letI (E :
      FiniteGaloisIntermediateField
        K Ω) :
      NumberField E :=
    NumberField.of_module_finite K E
  exact
    { val := fun E =>
        globalArtinMonoidHom
          (K := K) (L := E.unop) a
      property := by
        intro E F f
        algebraize [Subsemiring.inclusion <| leOfHom f.1]
        have : IsScalarTower K F.unop E.unop :=
          IsScalarTower.of_algebraMap_eq (congrFun rfl)
        change
          AlgEquiv.restrictNormalHom F.unop
              (globalArtinMonoidHom
                (K := K) (L := E.unop) a) =
            globalArtinMonoidHom
              (K := K) (L := F.unop) a
        exact
          DFunLike.congr_fun
            (globalArtinMonoidHom_restrict_tower
              (K := K) (E := F.unop) (L := E.unop)) a }

open scoped Classical in
/-- The continuous global Artin homomorphism into the finite-Galois
inverse limit, before transport to the Krull-topological Galois group. -/
noncomputable def infiniteGlobalArtinToLimit
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    IdeleGroup K →ₜ*
      limit
        (InfiniteGalois.asProfiniteGaloisGroupFunctor
          K Ω) := by
  letI
      (E :
        FiniteGaloisIntermediateField
          K Ω) :
      NumberField E :=
    NumberField.of_module_finite K E
  exact
    { toFun := infiniteGlobalArtinLimitPoint K Ω
      map_one' := by
        apply Subtype.ext
        funext E
        exact
          (globalArtinMonoidHom
            (K := K) (L := E.unop)).map_one
      map_mul' := by
        intro x y
        apply Subtype.ext
        funext E
        exact
          (globalArtinMonoidHom
            (K := K) (L := E.unop)).map_mul x y
      continuous_toFun := by
        have hcontinuous
            (E :
              (FiniteGaloisIntermediateField
                K Ω)ᵒᵖ) :
            @Continuous
              (IdeleGroup K) (E.unop ≃ₐ[K] E.unop)
              inferInstance (krullTopology K E.unop)
              (globalArtinMonoidHom
                (K := K) (L := E.unop)) :=
          globalArtinMonoidHom_continuous
            (K := K) (L := E.unop)
        let
            (E :
              (FiniteGaloisIntermediateField
                K Ω)ᵒᵖ) :
            TopologicalSpace (E.unop ≃ₐ[K] E.unop) :=
          ((InfiniteGalois.asProfiniteGaloisGroupFunctor
            K Ω).obj E).toProfinite.toTop.str
        apply Continuous.subtype_mk
        exact continuous_pi fun E => by
          change
            @Continuous
              (IdeleGroup K) (E.unop ≃ₐ[K] E.unop)
              inferInstance inferInstance
              (globalArtinMonoidHom
                (K := K) (L := E.unop))
          rw [show
            (inferInstance :
              TopologicalSpace (E.unop ≃ₐ[K] E.unop)) =
                krullTopology K E.unop by
            change
              (⊥ : TopologicalSpace
                (E.unop ≃ₐ[K] E.unop)) =
                  krullTopology K E.unop
            exact
              (@DiscreteTopology.eq_bot _
                (krullTopology K E.unop)
                inferInstance).symm]
          exact hcontinuous E }

open scoped Classical in
/-- The continuous global Artin homomorphism of an arbitrary abelian
Galois extension of a number field.  Its finite coordinates are the
finite global Artin homomorphisms. -/
noncomputable def infiniteGlobalArtinMonoidHom
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    IdeleGroup K →ₜ* (Ω ≃ₐ[K] Ω) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (InfiniteGalois.continuousMulEquivToLimit
      K Ω).symm).comp
    (infiniteGlobalArtinToLimit K Ω)

open scoped Classical in
/-- Projection of the infinite global Artin homomorphism to a finite
Galois intermediate field is exactly that field's finite global Artin
homomorphism, using a caller-supplied number-field witness. -/
@[simp]
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E) :
    letI : NumberField E := hE
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom
        (K := K) (L := E) a := by
  let : NumberField E := hE
  have hcomponent :=
    congrArg
      (InfiniteGalois.proj
        (k := K) (K := Ω) E)
      ((InfiniteGalois.continuousMulEquivToLimit
        K Ω).apply_symm_apply
          (infiniteGlobalArtinToLimit K Ω a))
  exact hcomponent

open scoped Classical in
/-- Finite projection with both finite-layer structures supplied explicitly.
This is useful when a concrete tower already has named canonical witnesses
and must not resynthesize them while checking the projected Artin endpoint. -/
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_of_structures
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois K E) :
    letI : NumberField E := hE
    letI : IsAbelianGalois K E := hAbelian
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom
        (K := K) (L := E) a := by
  let : NumberField E := hE
  let : IsAbelianGalois K E := hAbelian
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E hE

open scoped Classical in
/-- Finite projection stated for a plain intermediate field with its finite
Galois structures supplied separately.  This avoids packaging a concrete
dependent field into `FiniteGaloisIntermediateField` at every call site. -/
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_of_intermediateField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) (E : IntermediateField K Ω)
    [FiniteDimensional K E] [IsGalois K E]
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois K E) :
    letI : NumberField E := hE
    letI : IsAbelianGalois K E := hAbelian
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom (K := K) (L := E) a := by
  let G : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := E
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  let : NumberField E := hE
  let : IsAbelianGalois K E := hAbelian
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_structures
      K Ω a G hE hAbelian

open scoped Classical in
/-- Finite projection for a plain intermediate field when its structures are
already installed as ambient instances. -/
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_intermediateField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) (E : IntermediateField K Ω)
    [FiniteDimensional K E] [NumberField E] [IsAbelianGalois K E] :
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom (K := K) (L := E) a := by
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_intermediateField
      K Ω a E (inferInstance : NumberField E)
        (inferInstance : IsAbelianGalois K E)

open scoped Classical in
/-- Pointwise form of finite projection of the infinite global Artin map.
This is the stable interface when a concrete finite layer carries algebra
instances propositionally, but not definitionally, equal to the canonical
intermediate-field instances. -/
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField_apply
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    (x : E) :
    letI : NumberField E := hE
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) x =
      globalArtinMonoidHom
        (K := K) (L := E) a x := by
  let : NumberField E := hE
  exact DFunLike.congr_fun
    (restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E hE) x

open scoped Classical in
/-- Postcomposition of a finite projection of the infinite global Artin map.
Keeping `congrArg` at this generic level prevents large concrete towers from
being normalized merely to infer the endpoints of the mapped equality. -/
theorem map_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    {M : Type} (f : (E ≃ₐ[K] E) → M) :
    letI : NumberField E := hE
    f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)) =
      f (globalArtinMonoidHom
        (K := K) (L := E) a) := by
  let : NumberField E := hE
  exact congrArg f
    (restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E hE)

open scoped Classical in
/-- Postcomposition of a finite projection with both finite-layer structures
supplied explicitly.  This avoids resynthesizing proposition-valued instances
when the finite field is a concrete dependent intermediate field. -/
theorem map_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_structures
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois K E)
    {M : Type} (f : (E ≃ₐ[K] E) → M) :
    letI : NumberField E := hE
    letI : IsAbelianGalois K E := hAbelian
    f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)) =
      f (globalArtinMonoidHom
        (K := K) (L := E) a) := by
  let : NumberField E := hE
  let : IsAbelianGalois K E := hAbelian
  exact congrArg f
    (restrictNormalHom_infiniteGlobalArtinMonoidHom_of_structures
      K Ω a E hE hAbelian)

open scoped Classical in
/-- Postcomposition of the finite projection for a plain intermediate field.
The explicit structures keep concrete cyclotomic levels out of instance
normalization at the consumer. -/
theorem
    map_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_intermediateField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) (E : IntermediateField K Ω)
    [FiniteDimensional K E] [IsGalois K E]
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois K E)
    {M : Type} (f : (E ≃ₐ[K] E) → M) :
    letI : NumberField E := hE
    letI : IsAbelianGalois K E := hAbelian
    f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)) =
      f (globalArtinMonoidHom (K := K) (L := E) a) := by
  let : NumberField E := hE
  let : IsAbelianGalois K E := hAbelian
  exact congrArg f
    (restrictNormalHom_infiniteGlobalArtinMonoidHom_of_intermediateField
      K Ω a E hE hAbelian)

open scoped Classical in
/-- The finite global Artin homomorphism with its number-field witness fixed
as an explicit argument.  Concrete intermediate-field towers can share this
opaque hom without repeatedly comparing independently synthesized witnesses. -/
noncomputable def globalArtinMonoidHomOfNumberField
    (K L : Type) [Field K] [NumberField K]
    [Field L] [Algebra K L] [IsAbelianGalois K L]
    (hL : NumberField L) :
    IdeleGroup K →* (L ≃ₐ[K] L) := by
  letI : NumberField L := hL
  exact globalArtinMonoidHom (K := K) (L := L)

open scoped Classical in
/-- Norm-restriction naturality with the upper finite global Artin homomorphism
expressed through an explicit number-field witness. -/
theorem globalArtinMonoidHomOfNumberField_norm_restriction
    (K L K' L' : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    [Field K'] [NumberField K']
    [Field L'] [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (hL' : NumberField L') :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (globalArtinMonoidHomOfNumberField K' L' hL') =
      (globalArtinMonoidHom (K := K) (L := L)).comp
        (IdeleGroup.norm K K') := by
  let : NumberField L' := hL'
  exact globalArtinMonoidHom_norm_restriction

open scoped Classical in
/-- Monoid-hom postcomposition of a finite projection, stated at the hom
application level.  This keeps concrete consumers from unfolding
`MonoidHom.comp` merely to join the projection and finite Artin endpoints. -/
theorem comp_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    {M : Type} [Monoid M]
    (f : (E ≃ₐ[K] E) →* M) :
    letI : NumberField E := hE
    f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)) =
      (f.comp (globalArtinMonoidHomOfNumberField K E hE)) a := by
  let : NumberField E := hE
  exact
    (map_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E hE f).trans rfl

open scoped Classical in
/-- The mapped finite projection and its finite Artin specification, with
both endpoints fixed while the ambient field instances are still generic.
Concrete towers can reuse the package without asking the elaborator to
normalize those instances while checking the equality again. -/
noncomputable def
    compRestrictNormalHomInfiniteGlobalArtinDataOfNumberField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    {M : Type} [Monoid M]
    (f : (E ≃ₐ[K] E) →* M) :
    letI : NumberField E := hE
    {x : M //
      x = (f.comp
        (globalArtinMonoidHomOfNumberField K E hE)) a} := by
  letI : NumberField E := hE
  exact
    ⟨f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)),
      comp_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
        K Ω a E hE f⟩

open scoped Classical in
/-- The mapped infinite projection transported through a supplied naturality
square.  The intermediate finite Artin hom is the explicit-witness version,
so the equality is composed once in this generic provider rather than by a
concrete dependent field tower. -/
noncomputable def
    compRestrictNormalHomInfiniteGlobalArtinNaturalityDataOfNumberField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    {M : Type} [Monoid M]
    (f : (E ≃ₐ[K] E) →* M)
    (g : IdeleGroup K →* M)
    (hnat :
      f.comp (globalArtinMonoidHomOfNumberField K E hE) = g) :
    letI : NumberField E := hE
    {x : M // x = g a} := by
  letI : NumberField E := hE
  have hprojection :=
    comp_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E hE f
  exact
    ⟨f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)),
      hprojection.trans (DFunLike.congr_fun hnat a)⟩

open scoped Classical in
/-- Postcomposition of a finite projection when the finite layer's number
field structure is already installed as the ambient instance. -/
theorem map_restrictNormalHom_infiniteGlobalArtinMonoidHom
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    [NumberField E]
    {M : Type} (f : (E ≃ₐ[K] E) → M) :
    f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)) =
      f (globalArtinMonoidHom
        (K := K) (L := E) a) :=
  congrArg f
    (restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E (inferInstance : NumberField E))

open scoped Classical in
/-- Projection of the infinite global Artin homomorphism to a finite
Galois intermediate field, with its canonical module-finite number-field
structure. -/
@[simp]
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω) :
    letI : NumberField E :=
      NumberField.of_module_finite K E
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom
        (K := K) (L := E) a := by
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E (NumberField.of_module_finite K E)

open scoped Classical in
/-- Restriction of the infinite global Artin map along an abstract finite
abelian scalar tower.  Unlike the intermediate-field projection theorem, this
form allows the finite extension to be supplied through any chosen embedding
into the ambient infinite extension. -/
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_of_scalarTower
    (K E Ω : Type) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [IsAbelianGalois K E]
    [Field Ω] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) :
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom (K := K) (L := E) a := by
  let j : E →ₐ[K] Ω := IsScalarTower.toAlgHom K E Ω
  let G : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := j.fieldRange
      finiteDimensional :=
        j.equivFieldRange.toLinearEquiv.finiteDimensional
      isGalois := IsGalois.of_algEquiv j.equivFieldRange }
  let _ : FiniteDimensional K G := G.finiteDimensional
  let _ : NumberField G :=
    NumberField.of_module_finite K G
  let _ : IsAbelianGalois K G :=
    IsAbelianGalois.of_algHom G.toIntermediateField.val
  let _ : Algebra E G :=
    j.equivFieldRange.toRingHom.toAlgebra
  let _ : SMul E G := Algebra.toSMul
  let _ : IsScalarTower K E G :=
    IsScalarTower.of_algHom j.equivFieldRange.toAlgHom
  let _ : IsScalarTower K G Ω :=
    IntermediateField.isScalarTower_mid G.toIntermediateField
  let _ : IsScalarTower E G Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hProjection :
      AlgEquiv.restrictNormalHom G
          (infiniteGlobalArtinMonoidHom K Ω a) =
        globalArtinMonoidHom (K := K) (L := G) a :=
    restrictNormalHom_infiniteGlobalArtinMonoidHom K Ω a G
  calc
    AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom K Ω a) =
        AlgEquiv.restrictNormalHom E
          (AlgEquiv.restrictNormalHom G
            (infiniteGlobalArtinMonoidHom K Ω a)) :=
      IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E G
        (infiniteGlobalArtinMonoidHom K Ω a)
    _ = AlgEquiv.restrictNormalHom E
          (globalArtinMonoidHom (K := K) (L := G) a) :=
      congrArg (AlgEquiv.restrictNormalHom E) hProjection
    _ = globalArtinMonoidHom (K := K) (L := E) a :=
      DFunLike.congr_fun
        (globalArtinMonoidHom_restrict_tower
          (K := K) (L := G) (E := E)) a

open scoped Classical in
/-- Finite global reciprocity at every coordinate makes the infinite
global Artin homomorphism dense in the Krull topology. -/
theorem infiniteGlobalArtinMonoidHom_denseRange
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    DenseRange (infiniteGlobalArtinMonoidHom K Ω) := by
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨σ, hσU⟩
  let V : Set (Ω ≃ₐ[K] Ω) :=
    (Homeomorph.mulLeft σ) ⁻¹' U
  have hVopen : IsOpen V :=
    hU.preimage (Homeomorph.mulLeft σ).continuous
  have hVone : (1 : Ω ≃ₐ[K] Ω) ∈ V := by
    change σ * 1 ∈ U
    simpa using hσU
  have hVnhds :
      V ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω) :=
    hVopen.mem_nhds hVone
  obtain ⟨E, hEV⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
        (k := K) (K := Ω) V).mp
      hVnhds
  let : NumberField E :=
    NumberField.of_module_finite K E
  obtain ⟨a, ha⟩ :=
    globalArtinMonoidHom_surjective
      (K := K) (L := E)
      (AlgEquiv.restrictNormalHom E σ)
  have hfix :
      σ⁻¹ * infiniteGlobalArtinMonoidHom K Ω a ∈
        E.fixingSubgroup := by
    rw [
      FiniteGaloisIntermediateField.mem_fixingSubgroup_iff,
      map_mul, map_inv,
      restrictNormalHom_infiniteGlobalArtinMonoidHom,
      ha, inv_mul_cancel]
  have hmemV :
      σ⁻¹ * infiniteGlobalArtinMonoidHom K Ω a ∈ V :=
    hEV hfix
  refine
    ⟨infiniteGlobalArtinMonoidHom K Ω a, ?_,
      ⟨a, rfl⟩⟩
  simpa [V, mul_assoc] using hmemV

open scoped Classical in
/-- The actual continuous global Artin homomorphism from rational ideles
to the Galois group of the `ZHat`-extension of `ℚ`. -/
noncomputable def rationalCyclotomicZHatGlobalArtin :
    IdeleGroup ℚ →ₜ*
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
  infiniteGlobalArtinMonoidHom ℚ rationalCyclotomicZHatField

open scoped Classical in
private theorem
    continuousMulEquivToLimit_rationalCyclotomicZHatGlobalArtin_apply
    (a : IdeleGroup ℚ) :
    InfiniteGalois.continuousMulEquivToLimit
        ℚ rationalCyclotomicZHatField
        (rationalCyclotomicZHatGlobalArtin a) =
      infiniteGlobalArtinToLimit
        ℚ rationalCyclotomicZHatField a := by
  exact
    (InfiniteGalois.continuousMulEquivToLimit
      ℚ rationalCyclotomicZHatField).apply_symm_apply _

open scoped Classical in
/-- Projection of the rational `ZHat` Artin homomorphism is the finite
global Artin homomorphism. -/
@[simp]
theorem restrictNormalHom_rationalCyclotomicZHatGlobalArtin
    (a : IdeleGroup ℚ)
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    letI : IsAbelianGalois ℚ E :=
      IsAbelianGalois.of_algHom E.toIntermediateField.val
    AlgEquiv.restrictNormalHom E
        (rationalCyclotomicZHatGlobalArtin a) =
      globalArtinMonoidHom
        (K := ℚ) (L := E) a :=
  restrictNormalHom_infiniteGlobalArtinMonoidHom
    ℚ rationalCyclotomicZHatField a E

open scoped Classical in
/-- Rational cyclotomic projection with caller-supplied finite-layer
structures. -/
theorem restrictNormalHom_rationalCyclotomicZHatGlobalArtin_of_structures
    (a : IdeleGroup ℚ)
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois ℚ E) :
    letI : NumberField E := hE
    letI : IsAbelianGalois ℚ E := hAbelian
    AlgEquiv.restrictNormalHom E
        (rationalCyclotomicZHatGlobalArtin a) =
      globalArtinMonoidHom
        (K := ℚ) (L := E) a := by
  let : NumberField E := hE
  let : IsAbelianGalois ℚ E := hAbelian
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_structures
      ℚ rationalCyclotomicZHatField a E hE hAbelian

open scoped Classical in
/-- A mapped relative infinite Artin projection, the corresponding rational
finite Artin value, and the rational infinite projection, packaged with both
comparison steps.  The common finite value is generated only once in this
generic provider, so concrete dependent towers never compare separately
elaborated finite-field structures. -/
noncomputable def
    compRestrictNormalHomInfiniteGlobalArtinRationalCyclotomicDataOfNumberField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E' : FiniteGaloisIntermediateField K Ω)
    (hE' : NumberField E')
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois ℚ E)
    (f : (E' ≃ₐ[K] E') →* Gal(E/ℚ))
    (hnat :
      letI : NumberField E' := hE'
      letI : NumberField E := hE
      letI : IsAbelianGalois ℚ E := hAbelian
      f.comp (globalArtinMonoidHomOfNumberField K E' hE') =
        (globalArtinMonoidHom (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ K)) :
    letI : NumberField E' := hE'
    letI : NumberField E := hE
    letI : IsAbelianGalois ℚ E := hAbelian
    {x : Gal(E / ℚ) × Gal(E / ℚ) × Gal(E / ℚ) //
      x.1 = x.2.1 ∧ x.2.1 = x.2.2} := by
  letI : NumberField E' := hE'
  letI : NumberField E := hE
  letI : IsAbelianGalois ℚ E := hAbelian
  let relativeData :=
    compRestrictNormalHomInfiniteGlobalArtinNaturalityDataOfNumberField
      K Ω a E' hE' f
      ((globalArtinMonoidHom (K := ℚ) (L := E)).comp
        (IdeleGroup.norm ℚ K))
      hnat
  have hcomp :
      ((globalArtinMonoidHom (K := ℚ) (L := E)).comp
        (IdeleGroup.norm ℚ K)) a =
        globalArtinMonoidHom (K := ℚ) (L := E)
          (IdeleGroup.norm ℚ K a) :=
    rfl
  exact
    ⟨(relativeData.1,
        ((globalArtinMonoidHom (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ K)) a,
        AlgEquiv.restrictNormalHom E
          (rationalCyclotomicZHatGlobalArtin
            (IdeleGroup.norm ℚ K a))),
      relativeData.2,
      hcomp.trans
        (restrictNormalHom_rationalCyclotomicZHatGlobalArtin_of_structures
          (IdeleGroup.norm ℚ K a) E hE hAbelian).symm⟩

open scoped Classical in
/-- The rational `ZHat` specialization has dense Artin image. -/
theorem rationalCyclotomicZHatGlobalArtin_denseRange :
    DenseRange rationalCyclotomicZHatGlobalArtin :=
  infiniteGlobalArtinMonoidHom_denseRange
    ℚ rationalCyclotomicZHatField

open scoped Classical in
/-- The infinite global Artin homomorphism, like each of its finite
coordinates, kills the positive archimedean section. -/
@[simp]
theorem
    rationalCyclotomicZHatGlobalArtin_rationalPositiveArchimedeanIdele
    (r : ℝ≥0ˣ) :
    rationalCyclotomicZHatGlobalArtin
        (rationalPositiveArchimedeanIdele r) =
      1 := by
  let
      (E :
        FiniteGaloisIntermediateField
          ℚ rationalCyclotomicZHatField) :
      NumberField E :=
    NumberField.of_module_finite ℚ E
  let
      (E :
        FiniteGaloisIntermediateField
          ℚ rationalCyclotomicZHatField) :
      IsAbelianGalois ℚ E :=
    IsAbelianGalois.of_algHom E.toIntermediateField.val
  apply
    (InfiniteGalois.continuousMulEquivToLimit
      ℚ rationalCyclotomicZHatField).injective
  rw [
    continuousMulEquivToLimit_rationalCyclotomicZHatGlobalArtin_apply,
    map_one]
  apply Subtype.ext
  funext E
  exact
    globalArtinMonoidHom_rationalPositiveArchimedeanIdele
      (L := E.unop) r

open scoped Classical in
/-- Every rational idele has the same infinite Artin symbol as a
norm-one idele. -/
theorem
    exists_normOneIdele_same_rationalCyclotomicZHatGlobalArtin
    (a : IdeleGroup ℚ) :
    ∃ b : IdeleGroup.normOneSubgroup (K := ℚ),
      rationalCyclotomicZHatGlobalArtin b =
        rationalCyclotomicZHatGlobalArtin a := by
  let r := IdeleGroup.absoluteNorm a
  refine
    ⟨⟨a * rationalPositiveArchimedeanIdele r, ?_⟩,
      ?_⟩
  · change
      IdeleGroup.absoluteNorm
          (a * rationalPositiveArchimedeanIdele r) =
        1
    rw [map_mul,
      rationalPositiveArchimedeanIdele_absoluteNorm]
    simp [r]
  · change
      rationalCyclotomicZHatGlobalArtin
          (a * rationalPositiveArchimedeanIdele r) =
        rationalCyclotomicZHatGlobalArtin a
    rw [map_mul,
      rationalCyclotomicZHatGlobalArtin_rationalPositiveArchimedeanIdele,
      mul_one]

open scoped Classical in
/-- The norm-one rational ideles already have dense Artin image. -/
theorem rationalCyclotomicZHatGlobalArtin_normOne_denseRange :
    DenseRange
      (fun b : IdeleGroup.normOneSubgroup (K := ℚ) =>
        rationalCyclotomicZHatGlobalArtin b) := by
  apply rationalCyclotomicZHatGlobalArtin_denseRange.mono
  rintro σ ⟨a, rfl⟩
  obtain ⟨b, hb⟩ :=
    exists_normOneIdele_same_rationalCyclotomicZHatGlobalArtin a
  exact ⟨b, hb⟩

end Reciprocity
end GlobalClassFieldTheory
