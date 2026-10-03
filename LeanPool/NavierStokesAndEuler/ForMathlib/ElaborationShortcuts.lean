/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Shortcut instances for queries made by almost every declaration

Two kinds of instance problem occur in nearly every declaration of this project, are answered by
a search through general instances each time, and are not shared between declarations.

* **Coercions.** Using a set or a subobject as a type, using an element of a subtype as an
  element of the ambient type, and writing `∞` for a smoothness order each ask for a coercion.
  The answer is found through the chain of coercion classes. Each `CoercionShortcut` definition
  records the instance selected for its displayed `CoeT` query when its body is elaborated, then
  registers that alias at high priority. The declarations are sequential, so a later capture can
  see earlier aliases. This capture order alone does not establish equality with all coercion
  queries in an environment preceding the complete shortcut set.

* **Facts about `ℝ`.** Arithmetic on `ℝ` needs that `ℝ` has characteristic zero, that addition
  and multiplication are monotone, that the operations are continuous. None of these is stated
  directly for `ℝ`; each is derived from the ordered field or normed field structure after the
  search has tried the unrelated ways of proving such a fact. The instances of `RealShortcut`
  state them for `ℝ` itself. These 44 theorem aliases have proposition-valued targets; for a
  fixed target and its data parameters, proof irrelevance identifies their proof values. This
  does not assert that instance search follows an identical route for other queries with unknown
  data parameters.
-/

public section

namespace NavierStokesAndEuler.CoercionShortcut

universe u v

/-- Shortcut for using a set as a type. -/
instance (priority := high) instSetCoeT {α : Type u} {s : Set α} : CoeT (Set α) s (Type u) :=
  inferInstance

/-- Shortcut for the coercion from a subtype to the ambient type. -/
instance (priority := high) instSubtypeCoeT {α : Sort u} {p : α → Prop} {x : Subtype p} :
    CoeT (Subtype p) x α :=
  inferInstance

/-- Shortcut for using an additive subgroup as a type. -/
instance (priority := high) instAddSubgroupCoeT {G : Type u} [AddGroup G] {S : AddSubgroup G} :
    CoeT (AddSubgroup G) S (Type u) :=
  inferInstance

/-- Shortcut for using a submodule as a type. -/
instance (priority := high) instSubmoduleCoeT {R : Type u} {M : Type v} [Semiring R]
    [AddCommMonoid M] [Module R M] {p : Submodule R M} : CoeT (Submodule R M) p (Type v) :=
  inferInstance

/-- Shortcut for the coercion of an extended natural number to a smoothness order. -/
instance (priority := high) instENatCoeT {n : ℕ∞} : CoeT ℕ∞ n (WithTop ℕ∞) :=
  inferInstance

end NavierStokesAndEuler.CoercionShortcut

namespace NavierStokesAndEuler.RealShortcut

/-! ### Algebra -/

theorem instCharZero : CharZero ℝ := inferInstance
theorem instNoZeroDivisors : NoZeroDivisors ℝ := inferInstance
theorem instIsCancelMulZero : IsCancelMulZero ℝ := inferInstance
theorem instNeZeroOne : NeZero (1 : ℝ) := inferInstance
theorem instIsScalarTower : IsScalarTower ℝ ℝ ℝ := inferInstance
theorem instSMulCommClass : SMulCommClass ℝ ℝ ℝ := inferInstance

attribute [instance] instCharZero instNoZeroDivisors instIsCancelMulZero instNeZeroOne
  instIsScalarTower instSMulCommClass

/-! ### Order -/

theorem instIsOrderedAddMonoid : IsOrderedAddMonoid ℝ := inferInstance
theorem instIsOrderedRing : IsOrderedRing ℝ := inferInstance
theorem instIsStrictOrderedRing : IsStrictOrderedRing ℝ := inferInstance
theorem instZeroLEOneClass : ZeroLEOneClass ℝ := inferInstance
theorem instExistsAddOfLE : ExistsAddOfLE ℝ := inferInstance
theorem instDenselyOrdered : DenselyOrdered ℝ := inferInstance
theorem instIsOrderedModule : IsOrderedModule ℝ ℝ := inferInstance
theorem instAddLeftMono : AddLeftMono ℝ := inferInstance
theorem instAddRightMono : AddRightMono ℝ := inferInstance
theorem instAddLeftStrictMono : AddLeftStrictMono ℝ := inferInstance
theorem instAddRightStrictMono : AddRightStrictMono ℝ := inferInstance
theorem instAddLeftReflectLE : AddLeftReflectLE ℝ := inferInstance
theorem instAddRightReflectLE : AddRightReflectLE ℝ := inferInstance
theorem instAddLeftReflectLT : AddLeftReflectLT ℝ := inferInstance
theorem instAddRightReflectLT : AddRightReflectLT ℝ := inferInstance
theorem instPosMulMono : PosMulMono ℝ := inferInstance
theorem instMulPosMono : MulPosMono ℝ := inferInstance
theorem instPosMulStrictMono : PosMulStrictMono ℝ := inferInstance
theorem instMulPosStrictMono : MulPosStrictMono ℝ := inferInstance
theorem instPosMulReflectLT : PosMulReflectLT ℝ := inferInstance
theorem instMulPosReflectLT : MulPosReflectLT ℝ := inferInstance
theorem instPosMulReflectLE : PosMulReflectLE ℝ := inferInstance
theorem instMulPosReflectLE : MulPosReflectLE ℝ := inferInstance

attribute [instance] instIsOrderedAddMonoid instIsOrderedRing instIsStrictOrderedRing
  instZeroLEOneClass instExistsAddOfLE instDenselyOrdered instIsOrderedModule instAddLeftMono
  instAddRightMono instAddLeftStrictMono instAddRightStrictMono instAddLeftReflectLE
  instAddRightReflectLE instAddLeftReflectLT instAddRightReflectLT instPosMulMono instMulPosMono
  instPosMulStrictMono instMulPosStrictMono instPosMulReflectLT instMulPosReflectLT
  instPosMulReflectLE instMulPosReflectLE

/-! ### Topology -/

theorem instContinuousAdd : ContinuousAdd ℝ := inferInstance
theorem instContinuousNeg : ContinuousNeg ℝ := inferInstance
theorem instContinuousSub : ContinuousSub ℝ := inferInstance
theorem instContinuousMul : ContinuousMul ℝ := inferInstance
theorem instIsTopologicalAddGroup : IsTopologicalAddGroup ℝ := inferInstance
theorem instIsTopologicalRing : IsTopologicalRing ℝ := inferInstance
theorem instOrderTopology : OrderTopology ℝ := inferInstance
theorem instOrderClosedTopology : OrderClosedTopology ℝ := inferInstance
theorem instClosedIicTopology : ClosedIicTopology ℝ := inferInstance
theorem instClosedIciTopology : ClosedIciTopology ℝ := inferInstance
theorem instT2Space : T2Space ℝ := inferInstance

attribute [instance] instContinuousAdd instContinuousNeg instContinuousSub instContinuousMul
  instIsTopologicalAddGroup instIsTopologicalRing instOrderTopology instOrderClosedTopology
  instClosedIicTopology instClosedIciTopology instT2Space

/-! ### The real line as a normed space over itself -/

theorem instContinuousSMul : ContinuousSMul ℝ ℝ := inferInstance
theorem instContinuousConstSMul : ContinuousConstSMul ℝ ℝ := inferInstance
theorem instIsBoundedSMul : IsBoundedSMul ℝ ℝ := inferInstance
theorem instNormSMulClass : NormSMulClass ℝ ℝ := inferInstance

attribute [instance] instContinuousSMul instContinuousConstSMul instIsBoundedSMul
  instNormSMulClass

end NavierStokesAndEuler.RealShortcut

end
