/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FunctionFieldNormalClosureConstantBase
import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncConstantExtension
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The rational-function constant base of the normal closure

Let `N / K(t)` be the chosen function-field normal closure and let `C` be its
full algebraic constant field.  The field generated in `N` by `K(t)` and `C`
is exactly the fixed field of the automorphisms acting trivially on `C`.
This is the Galois-theoretic identification of that fixed field with the
constant extension `C(t)`.
-/

namespace BGS.HasseWeil

noncomputable section


variable (K L : Type*) [Field K] [Field L]
  [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)]
  [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance ratFuncBaseConstantSMul :
    SMul (FunctionFieldNormalClosureConstantField K L)
      (FunctionFieldNormalClosureConstantBase K L) := Algebra.toSMul

local instance ratFuncBaseConstantModule :
    Module (FunctionFieldNormalClosureConstantField K L)
      (FunctionFieldNormalClosureConstantBase K L) := Algebra.toModule

local instance normalClosureConstantBaseRatFuncTower :
    IsScalarTower K (RatFunc K) (FunctionFieldNormalClosureConstantBase K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The compositum of the original rational function field and the algebraic
constant field, formed inside the chosen normal closure. -/
def functionFieldNormalClosureConstantCompositum :
    IntermediateField (RatFunc K) (FunctionFieldNormalClosure K L) :=
  IntermediateField.adjoin (RatFunc K)
    (Set.range (fun c : FunctionFieldNormalClosureConstantField K L => c.1))

/-- The subgroup fixing the constant compositum is precisely the kernel of
restriction to the algebraic constant field. -/
theorem functionFieldNormalClosureConstantCompositum_fixingSubgroup :
    (functionFieldNormalClosureConstantCompositum K L).fixingSubgroup =
      (functionFieldNormalClosureConstantRestriction K L).ker := by
  apply le_antisymm
  · intro g hg
    rw [MonoidHom.mem_ker]
    apply AlgEquiv.ext
    intro c
    apply Subtype.ext
    exact (IntermediateField.mem_fixingSubgroup_iff
      (functionFieldNormalClosureConstantCompositum K L) g).mp hg c.1
        (IntermediateField.subset_adjoin (RatFunc K) _ ⟨c, rfl⟩)
  · apply (IntermediateField.le_iff_le
      (functionFieldNormalClosureConstantRestriction K L).ker
      (functionFieldNormalClosureConstantCompositum K L)).mp
    unfold functionFieldNormalClosureConstantCompositum
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨c, rfl⟩
    exact (functionFieldNormalClosureConstantToBase K L c).property

/-- The kernel fixed field is the compositum `K(t)C` inside the normal
closure. -/
theorem functionFieldNormalClosureConstantBase_eq_compositum :
    FunctionFieldNormalClosureConstantBase K L =
      functionFieldNormalClosureConstantCompositum K L := by
  change IntermediateField.fixedField
      (functionFieldNormalClosureConstantRestriction K L).ker = _
  rw [show (functionFieldNormalClosureConstantRestriction K L).ker =
      (functionFieldNormalClosureConstantCompositum K L).fixingSubgroup by
        exact (functionFieldNormalClosureConstantCompositum_fixingSubgroup
          K L).symm]
  exact IsGalois.fixedField_fixingSubgroup
    (functionFieldNormalClosureConstantCompositum K L)

/-- The original parameter `t` as an element of the kernel fixed field. -/
def functionFieldNormalClosureConstantBaseX :
    FunctionFieldNormalClosureConstantBase K L :=
  ⟨algebraMap (RatFunc K) (FunctionFieldNormalClosure K L) RatFunc.X, by
    apply (IntermediateField.mem_fixedField_iff
      (H := (functionFieldNormalClosureConstantRestriction K L).ker) _).mpr
    intro g hg
    exact g.commutes RatFunc.X⟩

/-- The `K`-, `C`-, and kernel-fixed-field algebra structures form a tower. -/
noncomputable instance functionFieldNormalClosureConstantBase_constantTower :
    IsScalarTower K (FunctionFieldNormalClosureConstantField K L)
      (FunctionFieldNormalClosureConstantBase K L) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext k
  rfl

/-- The original parameter remains transcendental after adjoining all
algebraic constants of the normal closure. -/
theorem functionFieldNormalClosureConstantBaseX_transcendental :
    Transcendental (FunctionFieldNormalClosureConstantField K L)
      (functionFieldNormalClosureConstantBaseX K L) := by
  let : Algebra.IsAlgebraic K (FunctionFieldNormalClosureConstantField K L) :=
    algebraicClosure.isAlgebraic K (FunctionFieldNormalClosure K L)
  let : Algebra.IsIntegral K (FunctionFieldNormalClosureConstantField K L) :=
    Algebra.IsAlgebraic.isIntegral
  intro hx
  have hxIntegralK : IsIntegral K
      (functionFieldNormalClosureConstantBaseX K L) :=
    isIntegral_trans _ hx.isIntegral
  have hxRatFunc : IsIntegral K (RatFunc.X : RatFunc K) := by
    apply (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom K (RatFunc K)
        (FunctionFieldNormalClosureConstantBase K L))
      (algebraMap (RatFunc K)
        (FunctionFieldNormalClosureConstantBase K L)).injective).mp
    simpa [functionFieldNormalClosureConstantBaseX] using hxIntegralK
  exact RatFunc.transcendental_X hxRatFunc.isAlgebraic

/-- The kernel fixed field is generated over the full constant field by the
original rational parameter. -/
theorem functionFieldNormalClosureConstantBase_adjoin_X :
    IntermediateField.adjoin
        (FunctionFieldNormalClosureConstantField K L)
        ({functionFieldNormalClosureConstantBaseX K L} :
          Set (FunctionFieldNormalClosureConstantBase K L)) = ⊤ := by
  let C := FunctionFieldNormalClosureConstantField K L
  let B := FunctionFieldNormalClosureConstantBase K L
  let N := FunctionFieldNormalClosure K L
  let x : B := functionFieldNormalClosureConstantBaseX K L
  let D : IntermediateField C B := IntermediateField.adjoin C ({x} : Set B)
  let f : RatFunc K →ₐ[K] B := IsScalarTower.toAlgHom K (RatFunc K) B
  have hfX : f RatFunc.X = x := rfl
  have hfieldRange : f.fieldRange =
      IntermediateField.adjoin K ({x} : Set B) := by
    calc
      f.fieldRange = IntermediateField.map f
          (⊤ : IntermediateField K (RatFunc K)) :=
        AlgHom.fieldRange_eq_map f
      _ = IntermediateField.map f
          (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K))) := by
        rw [RatFunc.adjoin_X]
      _ = IntermediateField.adjoin K (f '' ({RatFunc.X} : Set (RatFunc K))) :=
        IntermediateField.adjoin_map K _ f
      _ = IntermediateField.adjoin K ({x} : Set B) := by
        congr 1
        ext y
        simp only [Set.mem_image, Set.mem_singleton_iff]
        constructor
        · rintro ⟨z, rfl, rfl⟩
          exact hfX
        · intro hy
          refine ⟨RatFunc.X, rfl, ?_⟩
          simpa [hy] using hfX
  have hRatFuncRange : f.fieldRange ≤ D.restrictScalars K := by
    rw [hfieldRange]
    apply IntermediateField.adjoin_simple_le_iff.mpr
    rw [IntermediateField.mem_restrictScalars]
    exact IntermediateField.subset_adjoin C ({x} : Set B) (Set.mem_singleton x)
  have hRatFunc (r : RatFunc K) :
      algebraMap (RatFunc K) B r ∈ D := by
    rw [← IntermediateField.mem_restrictScalars K]
    apply hRatFuncRange
    exact ⟨r, rfl⟩
  apply top_unique
  intro y hy
  change y ∈ D
  have hyCompositum : y.1 ∈ functionFieldNormalClosureConstantCompositum K L := by
    rw [← functionFieldNormalClosureConstantBase_eq_compositum K L]
    exact y.2
  refine IntermediateField.adjoin_induction (RatFunc K)
    (p := fun z hz => ∀ hzB : z ∈ FunctionFieldNormalClosureConstantBase K L,
      (⟨z, hzB⟩ : B) ∈ D) ?_ ?_ ?_ ?_ ?_ hyCompositum y.2
  · rintro z ⟨c, rfl⟩ hzB
    exact D.algebraMap_mem c
  · intro r hzB
    exact hRatFunc r
  · intro z w hz hw hzD hwD hzwB
    have hzB : z ∈ FunctionFieldNormalClosureConstantBase K L := by
      rw [functionFieldNormalClosureConstantBase_eq_compositum K L]
      exact hz
    have hwB : w ∈ FunctionFieldNormalClosureConstantBase K L := by
      rw [functionFieldNormalClosureConstantBase_eq_compositum K L]
      exact hw
    exact D.add_mem (hzD hzB) (hwD hwB)
  · intro z hz hzD hzInvB
    have hzB : z ∈ FunctionFieldNormalClosureConstantBase K L := by
      rw [functionFieldNormalClosureConstantBase_eq_compositum K L]
      exact hz
    exact D.inv_mem (hzD hzB)
  · intro z w hz hw hzD hwD hzwB
    have hzB : z ∈ FunctionFieldNormalClosureConstantBase K L := by
      rw [functionFieldNormalClosureConstantBase_eq_compositum K L]
      exact hz
    have hwB : w ∈ FunctionFieldNormalClosureConstantBase K L := by
      rw [functionFieldNormalClosureConstantBase_eq_compositum K L]
      exact hw
    exact D.mul_mem (hzD hzB) (hwD hwB)

end

end BGS.HasseWeil
