/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionConstants
public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionRationalPlaceCount
public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionTower
public import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionClosedPlaceSplittingFormula
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionClosedPlaceAlgEquiv
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZetaDegreeIndexOne
public import LeanPool.MarkoffModP.BGS.HasseWeil.FunctionFieldNormalClosureOriginalCompositum

/-!
# The exact constant-extension tower of a function-field normal closure

Let `F / K(X)` have exact constant field `K`, let `N` be the chosen normal
closure, let `C` be the full algebraic constant field of `N`, and let
`M = CF ⊆ N` be the original compositum.  For a finite Galois extension
`S / C`, this file specializes the generic exact-constant-extension tower to

`S ⊗[C] M ⊆ S ⊗[C] N`.

It packages the canonical `S(X)`-linear inclusion, the finite Galois
structure of the top over the bottom, and preservation of both the relative
degree and the two rational-function-field degrees.  This is a structural
consumer of the exact constant-extension API; it deliberately does not use
the genus-invariance layer.
-/

@[expose] public section

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section CountOneBridge
open BGS.CorvajaZannier
variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
local instance : Algebra C N := bridgeBaseConstantAlgebra C N
local instance : IsScalarTower C (RatFunc C) N := IsScalarTower.of_algebraMap_eq' rfl

private theorem exactConstantExtensionClosedPlaceExtensionCount_one_eq_baseCount
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    let : Fintype S := Fintype.ofFinite S
    let : DecidableEq C := Classical.decEq C
    let : DecidableEq (RatFunc C) := Classical.decEq (RatFunc C)
    exactConstantExtensionClosedPlaceExtensionCount C S N hExact 1 =
      finiteExtensionClosedPlaceExtensionCount C N (Module.finrank C S) := by
  intro finiteS decideC decideRatFuncC
  classical
  rw [exactConstantExtensionClosedPlaceExtensionCount_eq_classical_decidableEq]
  have h := exactConstantExtensionClosedPlaceExtensionCount_eq C S N hExact 1
  simpa using h

private theorem rationalExactConstantCount_eq_of_algEquiv
    (E : Type*) [Field E] [Algebra (RatFunc C) E]
    [FiniteDimensional (RatFunc C) E] [Algebra.IsSeparable (RatFunc C) E]
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N))
    (e : E ≃ₐ[RatFunc C] N) :
    let : Fintype S := Fintype.ofFinite S
    let : DecidableEq C := Classical.decEq C
    let : DecidableEq (RatFunc C) := Classical.decEq (RatFunc C)
    let : DecidableEq S := Classical.decEq S
    let : DecidableEq (RatFunc S) := Classical.decEq (RatFunc S)
    let EM := ExactConstantExtension C N S
    let : Field EM := exactConstantExtensionField C N S hExact
    let : Algebra (RatFunc S) EM := ratFuncExactConstantExtensionAlgebra C S N hExact
    let : SMul (RatFunc S) EM := Algebra.toSMul
    let : Module (RatFunc S) EM := Algebra.toModule
    let : FiniteDimensional (RatFunc S) EM :=
      finiteDimensional_over_extendedRatFunc C S N hExact
    let : Algebra.IsSeparable (RatFunc S) EM :=
      isSeparable_over_extendedRatFunc C S N hExact
    finiteExtensionRationalPlaceCount S EM =
      finiteExtensionClosedPlaceExtensionCount C E (Module.finrank C S) := by
  intro finiteS decideC decideRatFuncC decideS decideRatFuncS EM
    fieldEM algebraEM smulEM moduleEM finiteEM separableEM
  classical
  have hFirst := exactConstantExtensionClosedPlaceExtensionCount_one_eq_rationalPlaceCount
    C S N hExact
  have hMiddle := exactConstantExtensionClosedPlaceExtensionCount_one_eq_baseCount C S N hExact
  have hLast := finiteExtensionClosedPlaceExtensionCount_eq_of_algEquiv C E N e
    (Module.finrank C S)
  exact hFirst.symm.trans (hMiddle.trans hLast.symm)

end CountOneBridge

private theorem finite_of_injective_field_tower
    (B M N : Type*) [Field B] [Field M] [Field N]
    [Algebra B M] [Algebra B N] [Algebra M N] [IsScalarTower B M N]
    [Module.Finite B N] : Module.Finite B M :=
  Module.Finite.of_injective (IsScalarTower.toAlgHom B M N).toLinearMap
    (IsScalarTower.toAlgHom B M N).injective


noncomputable section


variable (K F : Type*) [Field K] [Field F]
  [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)]
  [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]
  [Algebra.IsSeparable (RatFunc K) F]

/-- The `C(X)`-algebra on the constant-base field `C K(X)`, transported
through its canonical rational-function presentation. -/
@[reducible] noncomputable instance
    functionFieldNormalClosureConstantBaseConstantRatFuncAlgebra :
    Algebra (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosureConstantBase K F) :=
  (functionFieldNormalClosureConstantBaseRatFuncAlgEquiv K F).toAlgHom.toAlgebra

/-- The canonical rational-function presentation of the constant-base field,
viewed as an equivalence over `C(X)` itself. -/
noncomputable def
    functionFieldNormalClosureConstantBaseRatFuncSelfAlgEquiv :
    RatFunc (FunctionFieldNormalClosureConstantField K F) ≃ₐ[
        RatFunc (FunctionFieldNormalClosureConstantField K F)]
      FunctionFieldNormalClosureConstantBase K F :=
  { functionFieldNormalClosureConstantBaseRatFuncAlgEquiv K F with
    commutes' := fun _ => rfl }

/-- The constant-base field is one-dimensional, hence finite, over its
canonical `C(X)` presentation. -/
noncomputable instance
    functionFieldNormalClosureConstantBase_finiteDimensional_over_constantRatFunc :
    FiniteDimensional
      (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosureConstantBase K F) := by
  let e := functionFieldNormalClosureConstantBaseRatFuncSelfAlgEquiv K F
  exact Module.Finite.equiv e.toLinearEquiv

/-- The canonical `C(X)`-algebra on the normal closure, obtained by including
the constant-base field `C K(X)` into the normal closure. -/
@[reducible] noncomputable instance
    functionFieldNormalClosureConstantRatFuncAlgebra :
    Algebra (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosure K F) :=
  RingHom.toAlgebra
    ((algebraMap (FunctionFieldNormalClosureConstantBase K F)
        (FunctionFieldNormalClosure K F)).comp
      (algebraMap (RatFunc (FunctionFieldNormalClosureConstantField K F))
        (FunctionFieldNormalClosureConstantBase K F)))

/-- The canonical `C(X)` map to the normal closure factors through the
constant-base field. -/
noncomputable instance
    functionFieldNormalClosureConstantRatFuncBaseTower :
    IsScalarTower
      (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosureConstantBase K F)
      (FunctionFieldNormalClosure K F) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The normal closure is finite over the canonical copy of `C(X)`. -/
noncomputable instance
    functionFieldNormalClosure_finiteDimensional_over_constantRatFunc :
    FiniteDimensional
      (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosure K F) := by
  exact Module.Finite.trans (FunctionFieldNormalClosureConstantBase K F)
    (FunctionFieldNormalClosure K F)

omit [Algebra K F] [IsScalarTower K (RatFunc K) F] in
/-- The normal closure remains Galois after replacing the constant-base fixed
field by its canonical rational-function presentation `C(X)`. -/
theorem functionFieldNormalClosure_isGalois_over_constantRatFunc :
    IsGalois (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosure K F) := by
  let C := FunctionFieldNormalClosureConstantField K F
  let B := FunctionFieldNormalClosureConstantBase K F
  let N := FunctionFieldNormalClosure K F
  let e : RatFunc C ≃ₐ[RatFunc C] B :=
    functionFieldNormalClosureConstantBaseRatFuncSelfAlgEquiv K F
  let : IsGalois B N :=
    functionFieldNormalClosure_isGalois_over_constantBase K F
  refine IsGalois.of_equiv_equiv (F := B) (E := N)
    (f := e.symm.toRingEquiv) (g := RingEquiv.refl N) ?_
  ext x
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply (RatFunc C) B N]
  rw [← e.commutes]
  simp

/-- Exactness of the full normal-closure constant field, stated for the
constant algebra obtained by restricting the canonical `C(X)` presentation.
This is the exact instance expected by the generic tower API. -/
theorem functionFieldNormalClosureConstantField_isExact_for_constantRatFunc :
    let C := FunctionFieldNormalClosureConstantField K F
    let N := FunctionFieldNormalClosure K F
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    algebraicClosure C N = (⊥ : IntermediateField C N) := by
  let C := FunctionFieldNormalClosureConstantField K F
  let B := FunctionFieldNormalClosureConstantBase K F
  let N := FunctionFieldNormalClosure K F
  let old : Algebra C N := inferInstance
  let fresh : Algebra C N :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C N
  have hfresh : fresh = old := by
    apply Algebra.algebra_ext
    intro c
    let : Algebra C N := old
    change algebraMap B N
        (functionFieldNormalClosureConstantBaseRatFuncAlgEquiv K F
          (algebraMap C (RatFunc C) c)) = algebraMap C N c
    rw [(functionFieldNormalClosureConstantBaseRatFuncAlgEquiv K F).commutes]
    exact (IsScalarTower.algebraMap_apply C B N c).symm
  let exactFor : Algebra C N → Prop := fun a =>
    letI : Algebra C N := a
    algebraicClosure C N = (⊥ : IntermediateField C N)
  have hOld : exactFor old :=
    functionFieldNormalClosureConstantField_isExact K F
  have hFresh : exactFor fresh :=
    Eq.mp (congrArg exactFor hfresh).symm hOld
  let : Algebra C N := fresh
  exact hFresh

section OriginalCompositum

variable (hExact : algebraicClosure K F =
  (⊥ : IntermediateField K F))

/-- The constant-base field embeds into the original compositum `CF`. -/
@[reducible] noncomputable instance
    functionFieldNormalClosureConstantBaseOriginalCompositumAlgebra :
    Algebra (FunctionFieldNormalClosureConstantBase K F)
      (FunctionFieldNormalClosureOriginalCompositum K F hExact) :=
  (functionFieldNormalClosureConstantBaseToOriginalCompositum
    K F hExact).toAlgebra

local instance constantBaseOriginalCompositumSmul :
    SMul (FunctionFieldNormalClosureConstantBase K F)
      (FunctionFieldNormalClosureOriginalCompositum K F hExact) :=
  (functionFieldNormalClosureConstantBaseOriginalCompositumAlgebra K F hExact).toSMul

local instance constantBaseOriginalCompositumModule :
    Module (FunctionFieldNormalClosureConstantBase K F)
      (FunctionFieldNormalClosureOriginalCompositum K F hExact) :=
  (functionFieldNormalClosureConstantBaseOriginalCompositumAlgebra K F hExact).toModule

/-- The embeddings of the constant base into `CF` and then into the normal
closure agree with its direct inclusion. -/
noncomputable instance
    functionFieldNormalClosureConstantBaseOriginalCompositumTower :
    IsScalarTower (FunctionFieldNormalClosureConstantBase K F)
      (FunctionFieldNormalClosureOriginalCompositum K F hExact)
      (FunctionFieldNormalClosure K F) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext b
  rfl

/-- The existing `C(X)` structure on `CF` factors through the constant-base
field. -/
noncomputable instance
    functionFieldNormalClosureOriginalCompositumConstantRatFuncBaseTower :
    IsScalarTower
      (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosureConstantBase K F)
      (FunctionFieldNormalClosureOriginalCompositum K F hExact) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext r
  rfl

/-- The canonical `C(X)` structures on `CF` and on the normal closure are
compatible with the inclusion `CF ⊆ N`. -/
noncomputable instance
    functionFieldNormalClosureOriginalCompositumConstantRatFuncTower :
    IsScalarTower
      (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosureOriginalCompositum K F hExact)
      (FunctionFieldNormalClosure K F) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext r
  rfl

/-- The original compositum is finite over its canonical copy of `C(X)`. -/
noncomputable instance
    functionFieldNormalClosureOriginalCompositum_finiteDimensional_over_constantRatFunc :
    FiniteDimensional
      (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosureOriginalCompositum K F hExact) := by
  let B := FunctionFieldNormalClosureConstantBase K F
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  let N := FunctionFieldNormalClosure K F
  let : Module.Finite B M := finite_of_injective_field_tower B M N
  exact Module.Finite.trans B M

end OriginalCompositum

end

noncomputable section

section CanonicalNormalClosureTower


variable (K F : Type*) [Field K] [Field F]
  [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)]
  [Algebra (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]
  [Algebra.IsSeparable (RatFunc K) F]

local instance canonicalOriginalConstantAlgebra : Algebra K F :=
  functionFieldCanonicalConstantAlgebra K F

local instance canonicalOriginalConstantTower :
    IsScalarTower K (RatFunc K) F :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- In the canonical `C(X)` presentation, `C` is also the exact constant
field of the original compositum `CF`. -/
theorem
    functionFieldNormalClosureOriginalCompositumConstantField_isExact_for_constantRatFunc
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    let C := FunctionFieldNormalClosureConstantField K F
    let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    algebraicClosure C M = (⊥ : IntermediateField C M) := by
  let C := FunctionFieldNormalClosureConstantField K F
  let B := FunctionFieldNormalClosureConstantBase K F
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  let : Algebra (RatFunc C) M :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgebra
      K F hExact
  let old : Algebra C M :=
    functionFieldNormalClosureOriginalCompositumConstantAlgebra K F hExact
  let fresh : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  have hfresh : fresh = old := by
    apply Algebra.algebra_ext
    intro c
    let : Algebra C M := old
    let : Algebra B M :=
      functionFieldNormalClosureConstantBaseOriginalCompositumAlgebra
        K F hExact
    change algebraMap B M
        (functionFieldNormalClosureConstantBaseRatFuncAlgEquiv K F
          (algebraMap C (RatFunc C) c)) = algebraMap C M c
    rw [(functionFieldNormalClosureConstantBaseRatFuncAlgEquiv K F).commutes]
    rfl
  let exactFor : Algebra C M → Prop := fun a =>
    letI : Algebra C M := a
    algebraicClosure C M = (⊥ : IntermediateField C M)
  have hOld : exactFor old :=
    functionFieldNormalClosureOriginalCompositumConstantField_isExact
      K F hExact
  have hFresh : exactFor fresh :=
    Eq.mp (congrArg exactFor hfresh).symm hOld
  let : Algebra C M := fresh
  exact hFresh

/-- The original compositum remains separable over the canonical rational
function field of the full constant field.  This is transported from the
original function field after exact extension of constants. -/
private theorem originalCompositum_separable_constantRatFunc
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    Algebra.IsSeparable
      (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosureOriginalCompositum K F hExact) := by
  let N := FunctionFieldNormalClosure K F
  let : Algebra K N := functionFieldNormalClosureConstantAlgebra K F
  let C := FunctionFieldNormalClosureConstantField K F
  let : Algebra K C :=
    SubalgebraClass.toAlgebra (algebraicClosure K N)
  let E := ExactConstantExtension K F C
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  let : Field E := exactConstantExtensionField K F C hExact
  let : Algebra (RatFunc C) E :=
    ratFuncExactConstantExtensionAlgebra K C F hExact
  let : Algebra.IsSeparable (RatFunc C) E :=
    isSeparable_over_extendedRatFunc K C F hExact
  let e : E ≃ₐ[RatFunc C] M :=
    exactConstantExtensionOriginalCompositumCanonicalRatFuncAlgEquiv
      K F hExact
  constructor
  intro x
  have hx : IsSeparable (RatFunc C) (e.symm x) :=
    Algebra.IsSeparable.isSeparable (RatFunc C) (e.symm x)
  have hex : IsSeparable (RatFunc C) (e (e.symm x)) :=
    (AlgEquiv.isSeparable_iff e).mpr hx
  simpa using hex

noncomputable instance
    functionFieldNormalClosureOriginalCompositum_isSeparable_over_constantRatFunc
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    Algebra.IsSeparable
      (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosureOriginalCompositum K F hExact) :=
  originalCompositum_separable_constantRatFunc K F hExact

section ConstantExtension

variable (S : Type*) [Field S]
  [Algebra (FunctionFieldNormalClosureConstantField K F) S]

local instance normalClosureConstantExtensionModule :
    Module (FunctionFieldNormalClosureConstantField K F) S :=
  Algebra.toModule

variable [Module.Finite (FunctionFieldNormalClosureConstantField K F) S]
  [IsGalois (FunctionFieldNormalClosureConstantField K F) S]

/-- The field structure on `S ⊗[C] CF` used by the normal-closure tower. -/
@[reducible] noncomputable def
    functionFieldNormalClosureOriginalCompositumConstantExtensionField
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    let C := FunctionFieldNormalClosureConstantField K F
    let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    Field (ExactConstantExtension C M S) := by
  let C := FunctionFieldNormalClosureConstantField K F
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  letI : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  exact exactConstantExtensionField C M S
    (functionFieldNormalClosureOriginalCompositumConstantField_isExact_for_constantRatFunc
      K F hExact)

/-- The field structure on `S ⊗[C] N` in the same canonical
`C(X)` presentation. -/
@[reducible] noncomputable def
    functionFieldNormalClosureConstantExtensionFieldForTower :
    let C := FunctionFieldNormalClosureConstantField K F
    let N := FunctionFieldNormalClosure K F
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    Field (ExactConstantExtension C N S) := by
  let C := FunctionFieldNormalClosureConstantField K F
  let N := FunctionFieldNormalClosure K F
  letI : Algebra C N :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C N
  exact exactConstantExtensionField C N S
    (functionFieldNormalClosureConstantField_isExact_for_constantRatFunc K F)

/-- The canonical `S(X)`-algebra on `S ⊗[C] CF`. -/
@[reducible] noncomputable def
    functionFieldNormalClosureOriginalCompositumConstantExtensionRatFuncAlgebra
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    let C := FunctionFieldNormalClosureConstantField K F
    let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    Algebra (RatFunc S) (ExactConstantExtension C M S) := by
  let C := FunctionFieldNormalClosureConstantField K F
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  letI : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  letI : Field (ExactConstantExtension C M S) :=
    functionFieldNormalClosureOriginalCompositumConstantExtensionField
      K F S hExact
  exact ratFuncExactConstantExtensionAlgebra C S M
    (functionFieldNormalClosureOriginalCompositumConstantField_isExact_for_constantRatFunc
      K F hExact)

/-- The canonical `S(X)`-algebra on `S ⊗[C] N`. -/
@[reducible] noncomputable def
    functionFieldNormalClosureConstantExtensionRatFuncAlgebraForTower :
    let C := FunctionFieldNormalClosureConstantField K F
    let N := FunctionFieldNormalClosure K F
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    Algebra (RatFunc S) (ExactConstantExtension C N S) := by
  let C := FunctionFieldNormalClosureConstantField K F
  let N := FunctionFieldNormalClosure K F
  letI : Algebra C N :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C N
  letI : Field (ExactConstantExtension C N S) :=
    functionFieldNormalClosureConstantExtensionFieldForTower K F S
  exact ratFuncExactConstantExtensionAlgebra C S N
    (functionFieldNormalClosureConstantField_isExact_for_constantRatFunc K F)

/-- The canonical `S(X)`-linear inclusion
`S ⊗[C] CF → S ⊗[C] N`. -/
noncomputable def functionFieldNormalClosureConstantExtensionTowerAlgHom
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    let C := FunctionFieldNormalClosureConstantField K F
    let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
    let N := FunctionFieldNormalClosure K F
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    let E_M := ExactConstantExtension C M S
    let E_N := ExactConstantExtension C N S
    letI : Field E_M :=
      functionFieldNormalClosureOriginalCompositumConstantExtensionField
        K F S hExact
    letI : Field E_N :=
      functionFieldNormalClosureConstantExtensionFieldForTower K F S
    letI : Algebra (RatFunc S) E_M :=
      functionFieldNormalClosureOriginalCompositumConstantExtensionRatFuncAlgebra
        K F S hExact
    letI : Algebra (RatFunc S) E_N :=
      functionFieldNormalClosureConstantExtensionRatFuncAlgebraForTower K F S
    E_M →ₐ[RatFunc S] E_N := by
  let C := FunctionFieldNormalClosureConstantField K F
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  let N := FunctionFieldNormalClosure K F
  letI : Algebra (RatFunc C) M :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgebra
      K F hExact
  letI : Algebra (RatFunc C) N :=
    functionFieldNormalClosureConstantRatFuncAlgebra K F
  letI : IsScalarTower (RatFunc C) M N :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncTower
      K F hExact
  letI : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  letI : Algebra C N :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C N
  let E_M := ExactConstantExtension C M S
  let E_N := ExactConstantExtension C N S
  letI : Field E_M :=
    functionFieldNormalClosureOriginalCompositumConstantExtensionField
      K F S hExact
  letI : Field E_N :=
    functionFieldNormalClosureConstantExtensionFieldForTower K F S
  letI : Algebra (RatFunc S) E_M :=
    functionFieldNormalClosureOriginalCompositumConstantExtensionRatFuncAlgebra
      K F S hExact
  letI : Algebra (RatFunc S) E_N :=
    functionFieldNormalClosureConstantExtensionRatFuncAlgebraForTower K F S
  exact exactConstantExtensionTowerRatFuncAlgHom C M N S
    (functionFieldNormalClosureConstantField_isExact_for_constantRatFunc K F)

/-- The algebra structure underlying the specialized tensor inclusion. -/
@[reducible] noncomputable def
    functionFieldNormalClosureConstantExtensionTowerAlgebra
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    let C := FunctionFieldNormalClosureConstantField K F
    let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
    let N := FunctionFieldNormalClosure K F
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    Algebra (ExactConstantExtension C M S)
      (ExactConstantExtension C N S) := by
  let C := FunctionFieldNormalClosureConstantField K F
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  let N := FunctionFieldNormalClosure K F
  letI : Algebra (RatFunc C) M :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgebra
      K F hExact
  letI : Algebra (RatFunc C) N :=
    functionFieldNormalClosureConstantRatFuncAlgebra K F
  letI : IsScalarTower (RatFunc C) M N :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncTower
      K F hExact
  letI : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  letI : Algebra C N :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C N
  exact exactConstantExtensionTowerRatFuncAlgebra C M N S

/-- The specialized inclusion and the canonical `S(X)` structures form a
scalar tower. -/
theorem functionFieldNormalClosureConstantExtension_ratFuncScalarTower
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    let C := FunctionFieldNormalClosureConstantField K F
    let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
    let N := FunctionFieldNormalClosure K F
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    let E_M := ExactConstantExtension C M S
    let E_N := ExactConstantExtension C N S
    letI : Field E_M :=
      functionFieldNormalClosureOriginalCompositumConstantExtensionField
        K F S hExact
    letI : Field E_N :=
      functionFieldNormalClosureConstantExtensionFieldForTower K F S
    letI : Algebra (RatFunc S) E_M :=
      functionFieldNormalClosureOriginalCompositumConstantExtensionRatFuncAlgebra
        K F S hExact
    letI : Algebra (RatFunc S) E_N :=
      functionFieldNormalClosureConstantExtensionRatFuncAlgebraForTower K F S
    letI : Algebra E_M E_N :=
      functionFieldNormalClosureConstantExtensionTowerAlgebra K F S hExact
    letI : SMul (RatFunc S) E_M := Algebra.toSMul
    letI : SMul (RatFunc S) E_N := Algebra.toSMul
    letI : SMul E_M E_N := Algebra.toSMul
    IsScalarTower (RatFunc S) E_M E_N := by
  let C := FunctionFieldNormalClosureConstantField K F
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  let N := FunctionFieldNormalClosure K F
  let : Algebra (RatFunc C) M :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgebra
      K F hExact
  let : Algebra (RatFunc C) N :=
    functionFieldNormalClosureConstantRatFuncAlgebra K F
  let : IsScalarTower (RatFunc C) M N :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncTower
      K F hExact
  let : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  let : Algebra C N :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C N
  let E_M := ExactConstantExtension C M S
  let E_N := ExactConstantExtension C N S
  let : Field E_M :=
    functionFieldNormalClosureOriginalCompositumConstantExtensionField
      K F S hExact
  let : Field E_N :=
    functionFieldNormalClosureConstantExtensionFieldForTower K F S
  let : Algebra (RatFunc S) E_M :=
    functionFieldNormalClosureOriginalCompositumConstantExtensionRatFuncAlgebra
      K F S hExact
  let : Algebra (RatFunc S) E_N :=
    functionFieldNormalClosureConstantExtensionRatFuncAlgebraForTower K F S
  let : Algebra E_M E_N :=
    functionFieldNormalClosureConstantExtensionTowerAlgebra K F S hExact
  let : SMul (RatFunc S) E_M := Algebra.toSMul
  let : SMul (RatFunc S) E_N := Algebra.toSMul
  let : SMul E_M E_N := Algebra.toSMul
  exact exactConstantExtensionTower_ratFuncScalarTower C M N S
    (functionFieldNormalClosureConstantField_isExact_for_constantRatFunc K F)

/-- The extended normal closure is finite-dimensional over the extended
original compositum. -/
theorem
    functionFieldNormalClosureConstantExtension_finiteDimensional
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    let C := FunctionFieldNormalClosureConstantField K F
    let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
    let N := FunctionFieldNormalClosure K F
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    let E_M := ExactConstantExtension C M S
    let E_N := ExactConstantExtension C N S
    letI : Field E_M :=
      functionFieldNormalClosureOriginalCompositumConstantExtensionField
        K F S hExact
    letI : Field E_N :=
      functionFieldNormalClosureConstantExtensionFieldForTower K F S
    letI : Algebra E_M E_N :=
      functionFieldNormalClosureConstantExtensionTowerAlgebra K F S hExact
    letI : Module E_M E_N := Algebra.toModule
    Module.Finite E_M E_N := by
  let C := FunctionFieldNormalClosureConstantField K F
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  let N := FunctionFieldNormalClosure K F
  let : Algebra (RatFunc C) M :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgebra
      K F hExact
  let : Algebra (RatFunc C) N :=
    functionFieldNormalClosureConstantRatFuncAlgebra K F
  let : IsScalarTower (RatFunc C) M N :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncTower
      K F hExact
  let : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  let : Algebra C N :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C N
  let : SMul C M := Algebra.toSMul
  let : SMul C N := Algebra.toSMul
  let : SMul M N := Algebra.toSMul
  let : IsScalarTower C M N :=
    exactConstantExtensionTowerCanonicalConstantScalarTower C M N
  let E_M := ExactConstantExtension C M S
  let E_N := ExactConstantExtension C N S
  let : Field E_M :=
    functionFieldNormalClosureOriginalCompositumConstantExtensionField
      K F S hExact
  let : Field E_N :=
    functionFieldNormalClosureConstantExtensionFieldForTower K F S
  let : Algebra E_M E_N :=
    functionFieldNormalClosureConstantExtensionTowerAlgebra K F S hExact
  let : Module E_M E_N := Algebra.toModule
  let : FiniteDimensional M N :=
    functionFieldNormalClosure_finiteDimensional_over_originalCompositum
      K F hExact
  let : IsGalois M N :=
    functionFieldNormalClosure_isGalois_over_originalCompositum K F hExact
  exact exactConstantExtensionTower_finiteDimensional C M N S
    (functionFieldNormalClosureConstantField_isExact_for_constantRatFunc K F)

/-- The extended normal closure remains Galois over the extended original
compositum. -/
theorem functionFieldNormalClosureConstantExtension_isGalois
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    let C := FunctionFieldNormalClosureConstantField K F
    let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
    let N := FunctionFieldNormalClosure K F
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    let E_M := ExactConstantExtension C M S
    let E_N := ExactConstantExtension C N S
    letI : Field E_M :=
      functionFieldNormalClosureOriginalCompositumConstantExtensionField
        K F S hExact
    letI : Field E_N :=
      functionFieldNormalClosureConstantExtensionFieldForTower K F S
    letI : Algebra E_M E_N :=
      functionFieldNormalClosureConstantExtensionTowerAlgebra K F S hExact
    IsGalois E_M E_N := by
  let C := FunctionFieldNormalClosureConstantField K F
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  let N := FunctionFieldNormalClosure K F
  let : Algebra (RatFunc C) M :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgebra
      K F hExact
  let : Algebra (RatFunc C) N :=
    functionFieldNormalClosureConstantRatFuncAlgebra K F
  let : IsScalarTower (RatFunc C) M N :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncTower
      K F hExact
  let : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  let : Algebra C N :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C N
  let : SMul C M := Algebra.toSMul
  let : SMul C N := Algebra.toSMul
  let : SMul M N := Algebra.toSMul
  let : IsScalarTower C M N :=
    exactConstantExtensionTowerCanonicalConstantScalarTower C M N
  let E_M := ExactConstantExtension C M S
  let E_N := ExactConstantExtension C N S
  let : Field E_M :=
    functionFieldNormalClosureOriginalCompositumConstantExtensionField
      K F S hExact
  let : Field E_N :=
    functionFieldNormalClosureConstantExtensionFieldForTower K F S
  let : Algebra E_M E_N :=
    functionFieldNormalClosureConstantExtensionTowerAlgebra K F S hExact
  let : FiniteDimensional M N :=
    functionFieldNormalClosure_finiteDimensional_over_originalCompositum
      K F hExact
  let : IsGalois M N :=
    functionFieldNormalClosure_isGalois_over_originalCompositum K F hExact
  exact exactConstantExtensionTower_isGalois C M N S
    (functionFieldNormalClosureConstantField_isExact_for_constantRatFunc K F)

/-- Extending the full constant field preserves the degree of the normal
closure over the original compositum. -/
theorem functionFieldNormalClosureConstantExtension_finrank
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    let C := FunctionFieldNormalClosureConstantField K F
    let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
    let N := FunctionFieldNormalClosure K F
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    let E_M := ExactConstantExtension C M S
    let E_N := ExactConstantExtension C N S
    letI : Field E_M :=
      functionFieldNormalClosureOriginalCompositumConstantExtensionField
        K F S hExact
    letI : Field E_N :=
      functionFieldNormalClosureConstantExtensionFieldForTower K F S
    letI : Algebra E_M E_N :=
      functionFieldNormalClosureConstantExtensionTowerAlgebra K F S hExact
    letI : Module E_M E_N := Algebra.toModule
    letI : Module.Finite E_M E_N :=
      functionFieldNormalClosureConstantExtension_finiteDimensional
        K F S hExact
    Module.finrank E_M E_N = Module.finrank M N := by
  let C := FunctionFieldNormalClosureConstantField K F
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  let N := FunctionFieldNormalClosure K F
  let : Algebra (RatFunc C) M :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgebra
      K F hExact
  let : Algebra (RatFunc C) N :=
    functionFieldNormalClosureConstantRatFuncAlgebra K F
  let : IsScalarTower (RatFunc C) M N :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncTower
      K F hExact
  let : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  let : Algebra C N :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C N
  let : SMul C M := Algebra.toSMul
  let : SMul C N := Algebra.toSMul
  let : SMul M N := Algebra.toSMul
  let : IsScalarTower C M N :=
    exactConstantExtensionTowerCanonicalConstantScalarTower C M N
  let E_M := ExactConstantExtension C M S
  let E_N := ExactConstantExtension C N S
  let : Field E_M :=
    functionFieldNormalClosureOriginalCompositumConstantExtensionField
      K F S hExact
  let : Field E_N :=
    functionFieldNormalClosureConstantExtensionFieldForTower K F S
  let : Algebra E_M E_N :=
    functionFieldNormalClosureConstantExtensionTowerAlgebra K F S hExact
  let : Module E_M E_N := Algebra.toModule
  let : Module.Finite E_M E_N :=
    functionFieldNormalClosureConstantExtension_finiteDimensional
      K F S hExact
  let : FiniteDimensional M N :=
    functionFieldNormalClosure_finiteDimensional_over_originalCompositum
      K F hExact
  let : IsGalois M N :=
    functionFieldNormalClosure_isGalois_over_originalCompositum K F hExact
  exact exactConstantExtensionTower_finrank C M N S
    (functionFieldNormalClosureConstantField_isExact_for_constantRatFunc K F)

/-- Consequently the specialized tower Galois group has the same
cardinality as the normal-closure group over the original compositum. -/
theorem functionFieldNormalClosureConstantExtension_card_aut_eq
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    let C := FunctionFieldNormalClosureConstantField K F
    let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
    let N := FunctionFieldNormalClosure K F
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    letI : Algebra C N :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C N
    let E_M := ExactConstantExtension C M S
    let E_N := ExactConstantExtension C N S
    letI : Field E_M :=
      functionFieldNormalClosureOriginalCompositumConstantExtensionField
        K F S hExact
    letI : Field E_N :=
      functionFieldNormalClosureConstantExtensionFieldForTower K F S
    letI : Algebra E_M E_N :=
      functionFieldNormalClosureConstantExtensionTowerAlgebra K F S hExact
    letI : Module E_M E_N := Algebra.toModule
    letI : Module.Finite E_M E_N :=
      functionFieldNormalClosureConstantExtension_finiteDimensional
        K F S hExact
    letI : IsGalois E_M E_N :=
      functionFieldNormalClosureConstantExtension_isGalois K F S hExact
    Nat.card (E_N ≃ₐ[E_M] E_N) = Nat.card (N ≃ₐ[M] N) := by
  let C := FunctionFieldNormalClosureConstantField K F
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  let N := FunctionFieldNormalClosure K F
  let : Algebra (RatFunc C) M :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgebra
      K F hExact
  let : Algebra (RatFunc C) N :=
    functionFieldNormalClosureConstantRatFuncAlgebra K F
  let : IsScalarTower (RatFunc C) M N :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncTower
      K F hExact
  let : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  let : Algebra C N :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C N
  let : SMul C M := Algebra.toSMul
  let : SMul C N := Algebra.toSMul
  let : SMul M N := Algebra.toSMul
  let : IsScalarTower C M N :=
    exactConstantExtensionTowerCanonicalConstantScalarTower C M N
  let E_M := ExactConstantExtension C M S
  let E_N := ExactConstantExtension C N S
  let : Field E_M :=
    functionFieldNormalClosureOriginalCompositumConstantExtensionField
      K F S hExact
  let : Field E_N :=
    functionFieldNormalClosureConstantExtensionFieldForTower K F S
  let : Algebra E_M E_N :=
    functionFieldNormalClosureConstantExtensionTowerAlgebra K F S hExact
  let : Module E_M E_N := Algebra.toModule
  let : Module.Finite E_M E_N :=
    functionFieldNormalClosureConstantExtension_finiteDimensional
      K F S hExact
  let : IsGalois E_M E_N :=
    functionFieldNormalClosureConstantExtension_isGalois K F S hExact
  let : FiniteDimensional M N :=
    functionFieldNormalClosure_finiteDimensional_over_originalCompositum
      K F hExact
  let : IsGalois M N :=
    functionFieldNormalClosure_isGalois_over_originalCompositum K F hExact
  exact exactConstantExtensionTower_card_aut_eq C M N S
    (functionFieldNormalClosureConstantField_isExact_for_constantRatFunc K F)

/-- The rational-place count of the extended original compositum is the
packaged level-one exact constant-extension count of that compositum. -/
theorem
    normalClosureOriginalCompositum_rationalPlaceCount_eq_exactExtensionCount
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    let C := FunctionFieldNormalClosureConstantField K F
    let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
    letI : Algebra (RatFunc C) M :=
      functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgebra
        K F hExact
    letI : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    let hExactM :=
      functionFieldNormalClosureOriginalCompositumConstantField_isExact_for_constantRatFunc
        K F hExact
    let E_M := ExactConstantExtension C M S
    letI : Field E_M :=
      functionFieldNormalClosureOriginalCompositumConstantExtensionField
        K F S hExact
    letI : Algebra (RatFunc S) E_M :=
      functionFieldNormalClosureOriginalCompositumConstantExtensionRatFuncAlgebra
        K F S hExact
    letI : Module (RatFunc S) E_M := Algebra.toModule
    letI : Module.Finite (RatFunc S) E_M :=
      finiteDimensional_over_extendedRatFunc C S M hExactM
    letI : Algebra.IsSeparable (RatFunc S) E_M :=
      isSeparable_over_extendedRatFunc C S M hExactM
    letI : Fintype C := Fintype.ofFinite C
    letI : Finite S := Module.finite_of_finite C
    letI : Fintype S :=
      Fintype.ofFinite S
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableEq (RatFunc C) := Classical.decEq (RatFunc C)
    letI : DecidableEq S := Classical.decEq S
    letI : DecidableEq (RatFunc S) := Classical.decEq (RatFunc S)
    finiteExtensionRationalPlaceCount S E_M =
      exactConstantExtensionClosedPlaceExtensionCount C S M hExactM 1 := by
  let C := FunctionFieldNormalClosureConstantField K F
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  let : Algebra (RatFunc C) M :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgebra
      K F hExact
  let : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  let hExactM :=
    functionFieldNormalClosureOriginalCompositumConstantField_isExact_for_constantRatFunc
      K F hExact
  let E_M := ExactConstantExtension C M S
  let : Field E_M :=
    functionFieldNormalClosureOriginalCompositumConstantExtensionField
      K F S hExact
  let : Algebra (RatFunc S) E_M :=
    functionFieldNormalClosureOriginalCompositumConstantExtensionRatFuncAlgebra
      K F S hExact
  let : Module (RatFunc S) E_M := Algebra.toModule
  let : Module.Finite (RatFunc S) E_M :=
    finiteDimensional_over_extendedRatFunc C S M hExactM
  let : Algebra.IsSeparable (RatFunc S) E_M :=
    isSeparable_over_extendedRatFunc C S M hExactM
  let : Fintype C := Fintype.ofFinite C
  let : Finite S := Module.finite_of_finite C
  let : Fintype S :=
    Fintype.ofFinite S
  let : DecidableEq C := Classical.decEq C
  let : DecidableEq (RatFunc C) := Classical.decEq (RatFunc C)
  let : DecidableEq S := Classical.decEq S
  let : DecidableEq (RatFunc S) := Classical.decEq (RatFunc S)
  exact
    (exactConstantExtensionClosedPlaceExtensionCount_one_eq_rationalPlaceCount
      C S M hExactM).symm

/-- Combining the exact splitting formula with the canonical
`C(X)`-equivalence `C ⊗[K] F ≃ CF` identifies the same rational-place count
with the packaged exact-extension count of the original function field at
level `[S : C]`. -/
theorem
    normalClosureOriginalCompositum_rationalPlaceCount_eq_originalExactExtensionCount
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    let N := FunctionFieldNormalClosure K F
    let : Algebra K N := functionFieldNormalClosureConstantAlgebra K F
    let C := FunctionFieldNormalClosureConstantField K F
    let : Algebra K C :=
      SubalgebraClass.toAlgebra (algebraicClosure K N)
    let : Module.Finite K C :=
      functionFieldConstantField_finiteDimensional K N
    let : IsGalois K C := functionFieldConstantField_isGalois K N
    let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
    let : Algebra (RatFunc C) M :=
      functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgebra
        K F hExact
    let : Algebra C M :=
      exactConstantExtensionTowerCanonicalConstantAlgebra C M
    let hExactM :=
      functionFieldNormalClosureOriginalCompositumConstantField_isExact_for_constantRatFunc
        K F hExact
    let E_M := ExactConstantExtension C M S
    let : Field E_M :=
      functionFieldNormalClosureOriginalCompositumConstantExtensionField
        K F S hExact
    let : Algebra (RatFunc S) E_M :=
      functionFieldNormalClosureOriginalCompositumConstantExtensionRatFuncAlgebra
        K F S hExact
    let : Module (RatFunc S) E_M := Algebra.toModule
    let : Module.Finite (RatFunc S) E_M :=
      finiteDimensional_over_extendedRatFunc C S M hExactM
    let : Algebra.IsSeparable (RatFunc S) E_M :=
      isSeparable_over_extendedRatFunc C S M hExactM
    let : Finite C := functionFieldConstantField_finite K N
    let : Fintype C := Fintype.ofFinite C
    let : Finite S := Module.finite_of_finite C
    let : Fintype S := Fintype.ofFinite S
    let : DecidableEq C := Classical.decEq C
    let : DecidableEq (RatFunc C) := Classical.decEq (RatFunc C)
    let : DecidableEq S := Classical.decEq S
    let : DecidableEq (RatFunc S) := Classical.decEq (RatFunc S)
    finiteExtensionRationalPlaceCount S E_M =
      exactConstantExtensionClosedPlaceExtensionCount
        K C F hExact (Module.finrank C S) := by
  intro N model1 C model3 model4 model5 M model7 model8 hExactM E_M
    model11 model12 model13 model14 model15 model16 model17 model18 model19
    model20 model21 model22 model23
  classical
  let : Module (RatFunc C) M := model7.toModule
  let : FiniteDimensional (RatFunc C) M :=
    functionFieldNormalClosureOriginalCompositum_finiteDimensional_over_constantRatFunc K F hExact
  let : Algebra.IsSeparable (RatFunc C) M :=
    functionFieldNormalClosureOriginalCompositum_isSeparable_over_constantRatFunc K F hExact
  let E := ExactConstantExtension K F C
  let : Field E := exactConstantExtensionField K F C hExact
  let : Algebra (RatFunc C) E := ratFuncExactConstantExtensionAlgebra K C F hExact
  let : Module (RatFunc C) E := Algebra.toModule
  let : FiniteDimensional (RatFunc C) E :=
    finiteDimensional_over_extendedRatFunc K C F hExact
  let : Algebra.IsSeparable (RatFunc C) E :=
    isSeparable_over_extendedRatFunc K C F hExact
  let e : E ≃ₐ[RatFunc C] M :=
    exactConstantExtensionOriginalCompositumCanonicalRatFuncAlgEquiv K F hExact
  have hRational := rationalExactConstantCount_eq_of_algEquiv C S M E hExactM e
  have hLast := exactConstantExtensionClosedPlaceExtensionCount_eq_classical_decidableEq
    K C F hExact (Module.finrank C S)
  exact hRational.trans hLast.symm

end ConstantExtension

end CanonicalNormalClosureTower

end

end BGS.HasseWeil
