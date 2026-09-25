/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionAutomorphism
public import LeanPool.MarkoffModP.BGS.HasseWeil.FunctionFieldNormalClosureRatFuncEquiv
public import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncExactConstantExtension

/-!
# The original function field after enlarging the normal-closure constants

Let `F / K(t)` be finite separable, let `N` be the chosen normal closure, and
let `C` be the full algebraic constant field of `N`.  If `K` is already the
exact constant field of `F`, linear disjointness identifies the scalar
extension `C ⊗[K] F` with its multiplication image `CF` inside `N`.

This file constructs that image as an intermediate field, equips it with the
`C(t)`-structure inherited from the constant base inside `N`, and records the
two structural facts needed downstream: `N / CF` is finite Galois and `C` is
the exact constant field of `CF`.
-/

@[expose] public section

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section


variable (K F : Type*) [Field K] [Field F]
  [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)]
  [Algebra K F]
  [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]
  [Algebra.IsSeparable (RatFunc K) F]

local instance originalCompositumNormalClosureSMul :
    SMul K (FunctionFieldNormalClosure K F) := Algebra.toSMul

local instance originalCompositumNormalClosureModule :
    Module K (FunctionFieldNormalClosure K F) := Algebra.toModule

local instance originalCompositumNormalClosureSelfTower :
    IsScalarTower K K (FunctionFieldNormalClosure K F) :=
  ⟨fun x y z => (smul_smul x y z).symm⟩

local instance originalCompositumBaseConstantSMul :
    SMul K (FunctionFieldNormalClosureConstantField K F) := Algebra.toSMul

local instance originalCompositumBaseConstantModule :
    Module K (FunctionFieldNormalClosureConstantField K F) := Algebra.toModule

local instance originalCompositumConstantBaseSMul :
    SMul (FunctionFieldNormalClosureConstantField K F)
      (FunctionFieldNormalClosureConstantBase K F) := Algebra.toSMul

local instance originalCompositumConstantBaseModule :
    Module (FunctionFieldNormalClosureConstantField K F)
      (FunctionFieldNormalClosureConstantBase K F) := Algebra.toModule

/-- Multiplication of the two embedded factors `C` and `F` inside the normal
closure.  Before exactness is imposed this is merely an algebra homomorphism
from the tensor product; exactness will make its source a field and hence the
map injective. -/
noncomputable def functionFieldNormalClosureOriginalMultiplication :
    ExactConstantExtension K F
        (FunctionFieldNormalClosureConstantField K F) →ₐ[K]
      FunctionFieldNormalClosure K F :=
  Algebra.TensorProduct.lift
    (FunctionFieldNormalClosureConstantField K F).val
    ((functionFieldToNormalClosure K F).restrictScalars K)
    (fun _ _ => Commute.all _ _)

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] [FiniteDimensional (RatFunc K) F] in
@[simp]
theorem functionFieldNormalClosureOriginalMultiplication_tmul
    (c : FunctionFieldNormalClosureConstantField K F) (x : F) :
    functionFieldNormalClosureOriginalMultiplication K F (c ⊗ₜ[K] x) =
      c.1 * functionFieldToNormalClosure K F x := by
  simp [functionFieldNormalClosureOriginalMultiplication]

/-- The compositum `CF` inside the chosen normal closure, realized as the
field range of tensor multiplication. -/
noncomputable def FunctionFieldNormalClosureOriginalCompositum
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    IntermediateField K (FunctionFieldNormalClosure K F) := by
  letI : Field (ExactConstantExtension K F
      (FunctionFieldNormalClosureConstantField K F)) :=
    exactConstantExtensionField K F
      (FunctionFieldNormalClosureConstantField K F) hExact
  exact (functionFieldNormalClosureOriginalMultiplication K F).fieldRange

/-- Tensor scalar extension is the same field as the compositum `CF` inside
the normal closure. -/
noncomputable def exactConstantExtensionOriginalCompositumAlgEquiv
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    ExactConstantExtension K F
        (FunctionFieldNormalClosureConstantField K F) ≃ₐ[K]
      FunctionFieldNormalClosureOriginalCompositum K F hExact := by
  letI : Field (ExactConstantExtension K F
      (FunctionFieldNormalClosureConstantField K F)) :=
    exactConstantExtensionField K F
      (FunctionFieldNormalClosureConstantField K F) hExact
  exact AlgEquiv.ofInjectiveField
    (functionFieldNormalClosureOriginalMultiplication K F)

/-- Every algebraic constant of the normal closure belongs to `CF`. -/
theorem functionFieldNormalClosureConstant_mem_originalCompositum
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F))
    (c : FunctionFieldNormalClosureConstantField K F) :
    c.1 ∈ FunctionFieldNormalClosureOriginalCompositum K F hExact := by
  let : Field (ExactConstantExtension K F
      (FunctionFieldNormalClosureConstantField K F)) :=
    exactConstantExtensionField K F
      (FunctionFieldNormalClosureConstantField K F) hExact
  exact ⟨c ⊗ₜ[K] (1 : F), by simp⟩

omit [DecidableEq (RatFunc K)] in
/-- The original rational-function field belongs to `CF`. -/
theorem functionFieldNormalClosureRatFunc_mem_originalCompositum
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F))
    (r : RatFunc K) :
    algebraMap (RatFunc K) (FunctionFieldNormalClosure K F) r ∈
      FunctionFieldNormalClosureOriginalCompositum K F hExact := by
  let : Field (ExactConstantExtension K F
      (FunctionFieldNormalClosureConstantField K F)) :=
    exactConstantExtensionField K F
      (FunctionFieldNormalClosureConstantField K F) hExact
  refine ⟨1 ⊗ₜ[K] algebraMap (RatFunc K) F r, ?_⟩
  simp [functionFieldNormalClosureOriginalMultiplication]

/-- The inclusion of the full constant field into `CF`. -/
noncomputable def functionFieldNormalClosureConstantToOriginalCompositum
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    FunctionFieldNormalClosureConstantField K F →ₐ[K]
      FunctionFieldNormalClosureOriginalCompositum K F hExact :=
  (FunctionFieldNormalClosureConstantField K F).val.codRestrict
    (FunctionFieldNormalClosureOriginalCompositum K F hExact).toSubalgebra
    (functionFieldNormalClosureConstant_mem_originalCompositum K F hExact)

/-- The compositum is naturally an algebra over the full constant field. -/
@[reducible] noncomputable instance
    functionFieldNormalClosureOriginalCompositumConstantAlgebra
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    Algebra (FunctionFieldNormalClosureConstantField K F)
      (FunctionFieldNormalClosureOriginalCompositum K F hExact) :=
  (functionFieldNormalClosureConstantToOriginalCompositum K F hExact).toAlgebra

local instance originalCompositumConstantSMul
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    SMul (FunctionFieldNormalClosureConstantField K F)
      (FunctionFieldNormalClosureOriginalCompositum K F hExact) := Algebra.toSMul

local instance originalCompositumConstantModule
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    Module (FunctionFieldNormalClosureConstantField K F)
      (FunctionFieldNormalClosureOriginalCompositum K F hExact) := Algebra.toModule

/-- The tensor/compositum equivalence respects the enlarged constants. -/
noncomputable def exactConstantExtensionOriginalCompositumConstantAlgEquiv
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    let : Field (ExactConstantExtension K F
        (FunctionFieldNormalClosureConstantField K F)) :=
      exactConstantExtensionField K F
        (FunctionFieldNormalClosureConstantField K F) hExact
    let : Algebra (FunctionFieldNormalClosureConstantField K F)
        (ExactConstantExtension K F
          (FunctionFieldNormalClosureConstantField K F)) :=
      Algebra.TensorProduct.leftAlgebra
    ExactConstantExtension K F
        (FunctionFieldNormalClosureConstantField K F) ≃ₐ[
      FunctionFieldNormalClosureConstantField K F]
        FunctionFieldNormalClosureOriginalCompositum K F hExact := by
  intro model1 model2
  refine
    { exactConstantExtensionOriginalCompositumAlgEquiv K F hExact with
      commutes' := ?_ }
  intro c
  apply Subtype.ext
  change functionFieldNormalClosureOriginalMultiplication K F
      (c ⊗ₜ[K] (1 : F)) = c.1
  simp

/-- The constant embedding into `CF` agrees with its embedding into `N`. -/
noncomputable instance
    functionFieldNormalClosureOriginalCompositumConstantTower
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    IsScalarTower (FunctionFieldNormalClosureConstantField K F)
      (FunctionFieldNormalClosureOriginalCompositum K F hExact)
      (FunctionFieldNormalClosure K F) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  rfl

/-- The inclusion of `K(t)` into `CF`. -/
noncomputable def functionFieldNormalClosureRatFuncToOriginalCompositum
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    RatFunc K →ₐ[K]
      FunctionFieldNormalClosureOriginalCompositum K F hExact :=
  (IsScalarTower.toAlgHom K (RatFunc K)
      (FunctionFieldNormalClosure K F)).codRestrict
    (FunctionFieldNormalClosureOriginalCompositum K F hExact).toSubalgebra
    (functionFieldNormalClosureRatFunc_mem_originalCompositum K F hExact)

/-- The compositum is naturally a `K(t)`-algebra. -/
@[reducible] noncomputable instance
    functionFieldNormalClosureOriginalCompositumRatFuncAlgebra
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    Algebra (RatFunc K)
      (FunctionFieldNormalClosureOriginalCompositum K F hExact) :=
  (functionFieldNormalClosureRatFuncToOriginalCompositum K F hExact).toAlgebra

/-- The `K(t)` embedding into `CF` agrees with its embedding into `N`. -/
noncomputable instance
    functionFieldNormalClosureOriginalCompositumRatFuncTower
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    IsScalarTower (RatFunc K)
      (FunctionFieldNormalClosureOriginalCompositum K F hExact)
      (FunctionFieldNormalClosure K F) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext r
  rfl

/-- The constant base `C(t)` inside `N` is contained in the larger compositum
`CF`. -/
theorem functionFieldNormalClosureConstantBase_le_originalCompositum
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F))
    (b : FunctionFieldNormalClosureConstantBase K F) :
    b.1 ∈ FunctionFieldNormalClosureOriginalCompositum K F hExact := by
  have hb : b.1 ∈ functionFieldNormalClosureConstantCompositum K F := by
    rw [← functionFieldNormalClosureConstantBase_eq_compositum K F]
    exact b.2
  refine IntermediateField.adjoin_induction (RatFunc K)
    (p := fun z _ =>
      z ∈ FunctionFieldNormalClosureOriginalCompositum K F hExact)
    ?_ ?_ ?_ ?_ ?_ hb
  · rintro _ ⟨c, rfl⟩
    exact functionFieldNormalClosureConstant_mem_originalCompositum
      K F hExact c
  · exact functionFieldNormalClosureRatFunc_mem_originalCompositum
      K F hExact
  · intro x y _ _ hx hy
    exact (FunctionFieldNormalClosureOriginalCompositum K F hExact).add_mem hx hy
  · intro x _ hx
    exact (FunctionFieldNormalClosureOriginalCompositum K F hExact).inv_mem hx
  · intro x y _ _ hx hy
    exact (FunctionFieldNormalClosureOriginalCompositum K F hExact).mul_mem hx hy

/-- Inclusion of the constant base `C(t)` into `CF`, linear over `C`. -/
noncomputable def functionFieldNormalClosureConstantBaseToOriginalCompositum
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    FunctionFieldNormalClosureConstantBase K F →ₐ[
        FunctionFieldNormalClosureConstantField K F]
      FunctionFieldNormalClosureOriginalCompositum K F hExact where
  toFun b := ⟨b.1,
    functionFieldNormalClosureConstantBase_le_originalCompositum
      K F hExact b⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem originalCompositum_ratFunc_algHom_ext
    {C M : Type*} [Field C] [Field M] [Algebra C M]
    (f g : RatFunc C →ₐ[C] M) (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  have hRing : f.toRingHom = g.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := C[X])
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simpa only [map_add] using congrArg₂ (fun x y => x + y) hp hq
    | monomial n c =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        simp only [map_mul, map_pow, RatFunc.algebraMap_C,
          RatFunc.algebraMap_X]
        rw [← RatFunc.algebraMap_eq_C]
        have hfc : f.toRingHom (algebraMap C (RatFunc C) c) =
            algebraMap C M c := f.commutes c
        have hgc : g.toRingHom (algebraMap C (RatFunc C) c) =
            algebraMap C M c := g.commutes c
        have hX' : f.toRingHom RatFunc.X = g.toRingHom RatFunc.X := hX
        rw [hfc, hgc, hX']
  exact DFunLike.ext _ _ (fun r => DFunLike.congr_fun hRing r)

/-- The standard coefficient algebra structure on `C(t)` used by the
rational-function equivalence. -/
@[reducible] noncomputable instance (priority := 2000)
    functionFieldNormalClosureConstantFieldRatFuncAlgebraForOriginalCompositum :
    Algebra (FunctionFieldNormalClosureConstantField K F)
      (RatFunc (FunctionFieldNormalClosureConstantField K F)) :=
  ratFuncSelfAlgebra (FunctionFieldNormalClosureConstantField K F)

/-- The `C(t)`-algebra structure on `CF`, transported through the canonical
equivalence `C(t) ≃ C K(t)` inside the normal closure. -/
noncomputable def
    functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgHom
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    RatFunc (FunctionFieldNormalClosureConstantField K F) →ₐ[
        FunctionFieldNormalClosureConstantField K F]
      FunctionFieldNormalClosureOriginalCompositum K F hExact :=
  (functionFieldNormalClosureConstantBaseToOriginalCompositum K F hExact).comp
    (functionFieldNormalClosureConstantBaseRatFuncAlgEquiv K F).toAlgHom

/-- `CF` as an algebra over the enlarged rational-function field `C(t)`. -/
@[reducible] noncomputable instance
    functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgebra
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    Algebra (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosureOriginalCompositum K F hExact) :=
  (functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgHom
    K F hExact).toAlgebra

/-- The two embeddings of `K` into `CF`, directly and through `C`, agree. -/
noncomputable instance
    functionFieldNormalClosureOriginalCompositumBaseConstantTower
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    IsScalarTower K (FunctionFieldNormalClosureConstantField K F)
      (FunctionFieldNormalClosureOriginalCompositum K F hExact) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext k
  rfl

/-- The chosen normal closure is finite over the original compositum `CF`. -/
noncomputable instance
    functionFieldNormalClosure_finiteDimensional_over_originalCompositum
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    FiniteDimensional
      (FunctionFieldNormalClosureOriginalCompositum K F hExact)
      (FunctionFieldNormalClosure K F) := by
  let : Module.Finite
      (FunctionFieldNormalClosureOriginalCompositum K F hExact)
      (FunctionFieldNormalClosure K F) :=
    Module.Finite.of_restrictScalars_finite (RatFunc K)
      (FunctionFieldNormalClosureOriginalCompositum K F hExact)
      (FunctionFieldNormalClosure K F)
  infer_instance

/-- The chosen normal closure remains Galois after enlarging the base from
`K(t)` to the intermediate field `CF`. -/
noncomputable instance functionFieldNormalClosure_isGalois_over_originalCompositum
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    IsGalois (FunctionFieldNormalClosureOriginalCompositum K F hExact)
      (FunctionFieldNormalClosure K F) := by
  exact IsGalois.tower_top_of_isGalois (RatFunc K)
    (FunctionFieldNormalClosureOriginalCompositum K F hExact)
    (FunctionFieldNormalClosure K F)

/-- Enlarging the original function field to `CF` introduces exactly the
constants `C` and no others. -/
theorem functionFieldNormalClosureOriginalCompositumConstantField_isExact
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    algebraicClosure (FunctionFieldNormalClosureConstantField K F)
        (FunctionFieldNormalClosureOriginalCompositum K F hExact) =
      (⊥ : IntermediateField (FunctionFieldNormalClosureConstantField K F)
        (FunctionFieldNormalClosureOriginalCompositum K F hExact)) := by
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  let N := FunctionFieldNormalClosure K F
  let C := FunctionFieldNormalClosureConstantField K F
  let i : M →ₐ[C] N :=
    { toFun := fun x => x.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  apply eq_bot_iff.mpr
  intro z hz
  have hzN : i z ∈ algebraicClosure C N :=
    (map_mem_algebraicClosure_iff i).mpr hz
  rw [functionFieldNormalClosureConstantField_isExact K F] at hzN
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hzN
  apply IntermediateField.mem_bot.mpr
  refine ⟨c, ?_⟩
  apply Subtype.ext
  exact hc

end

noncomputable section

section CanonicalConstantPresentation


variable (K F : Type*) [Field K] [Field F]
  [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)]
  [Algebra (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]
  [Algebra.IsSeparable (RatFunc K) F]

/-- The constant algebra on `F` obtained by restricting the given
`K(t)`-algebra.  This named definition is useful when applying constructions
whose constant algebra is definitionally this restriction. -/
@[reducible] noncomputable def functionFieldCanonicalConstantAlgebra :
    Algebra K F :=
  RingHom.toAlgebra
    ((algebraMap (RatFunc K) F).comp (algebraMap K (RatFunc K)))

private theorem originalMultiplicationCanonicalRatFunc_X :
    let : Algebra K F := functionFieldCanonicalConstantAlgebra K F
    let : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq' rfl
    ∀ (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)),
      functionFieldNormalClosureOriginalMultiplication K F
        (ratFuncToExactConstantExtension K
          (FunctionFieldNormalClosureConstantField K F) F hExact RatFunc.X) =
        algebraMap (RatFunc K) (FunctionFieldNormalClosure K F) RatFunc.X := by
  intro model1 model2 hExact
  let C := FunctionFieldNormalClosureConstantField K F
  let : Algebra K[X] F :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) F).comp (algebraMap K[X] (RatFunc K)))
  rw [ratFuncToExactConstantExtension_X]
  simp only [polynomialTensorCancelEvaluationPoint, Algebra.TensorProduct.includeRight_apply]
  rw [functionFieldNormalClosureOriginalMultiplication_tmul]
  change (1 : FunctionFieldNormalClosure K F) *
      functionFieldToNormalClosure K F (algebraMap K[X] F Polynomial.X) = _
  rw [one_mul]
  change functionFieldToNormalClosure K F
      (algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) Polynomial.X)) = _
  rw [RatFunc.algebraMap_X]
  exact (functionFieldToNormalClosure K F).commutes RatFunc.X

/-- For the canonical restricted constant algebra, the tensor/compositum
equivalence is linear over `C(t)`, not merely over `K`. -/
noncomputable def
    exactConstantExtensionOriginalCompositumCanonicalRatFuncAlgEquiv :
    let : Algebra K F := functionFieldCanonicalConstantAlgebra K F
    let : IsScalarTower K (RatFunc K) F :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)),
      let C := FunctionFieldNormalClosureConstantField K F
      let E := ExactConstantExtension K F C
      let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
      let : Field E := exactConstantExtensionField K F C hExact
      let : Algebra C E := Algebra.TensorProduct.leftAlgebra
      let : Algebra (RatFunc C) E :=
        ratFuncExactConstantExtensionAlgebra K C F hExact
      E ≃ₐ[RatFunc C] M := by
  intro model1 model2 hExact C E M model3 model4 model5
  letI : Algebra C (RatFunc C) := ratFuncSelfAlgebra C
  letI : Algebra K[X] F :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) F).comp
        (algebraMap K[X] (RatFunc K)))
  let eC : E ≃ₐ[C] M :=
    exactConstantExtensionOriginalCompositumConstantAlgEquiv K F hExact
  let f : RatFunc C →ₐ[C] M :=
    eC.toAlgHom.comp (ratFuncToExactConstantExtension K C F hExact)
  let g : RatFunc C →ₐ[C] M :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgHom
      K F hExact
  exact
    { eC with
      commutes' := by
        intro r
        have hX : f RatFunc.X = g RatFunc.X := by
          apply Subtype.ext
          have hfX := originalMultiplicationCanonicalRatFunc_X K F hExact
          have hgX := congrArg Subtype.val
            (functionFieldNormalClosureConstantBaseRatFuncAlgEquiv_X K F)
          exact hfX.trans hgX.symm
        have hfg : f = g :=
          originalCompositum_ratFunc_algHom_ext (C := C) (M := M) f g hX
        exact DFunLike.congr_fun hfg r }

end CanonicalConstantPresentation

end

end BGS.HasseWeil
