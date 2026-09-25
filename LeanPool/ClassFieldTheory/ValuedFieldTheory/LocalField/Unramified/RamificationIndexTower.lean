/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.BasicInvariants
/-!
# Ramification index in valued-field towers

The generic tower and embedding-monotonicity lemmas extracted from the tame adapter.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicNumberTheory
namespace Valuations

section RamificationIndexTower

variable {K M L : Type u} [Field K] [Field M] [Field L]
variable [Algebra K M] [Algebra M L]

/-- The actual value-group ramification index is multiplicative in exact
valued-field towers. -/
theorem exponentialRamificationIndex_mul_in_tower
    (v : LubinTate.Valuations.ExponentialValuation K)
    (u : LubinTate.Valuations.ExponentialValuation M)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hKM : ∀ a : K, u (algebraMap K M a) = v a)
    (hML : ∀ a : M, w (algebraMap M L a) = u a) :
    exponentialRamificationIndex v u * exponentialRamificationIndex u w =
      exponentialRamificationIndex v w := by
  let GammaK := exponentialValueSubgroup v
  let GammaM := exponentialValueSubgroup u
  let GammaL := exponentialValueSubgroup w
  let H : AddSubgroup GammaL := GammaK.comap GammaL.subtype
  let J : AddSubgroup GammaL := GammaM.comap GammaL.subtype
  have hHJ : H ≤ J := by
    intro x hx
    change (x : ℝ) ∈ GammaM
    exact exponentialValueSubgroup_le_of_extends v u hKM hx
  let f : J →+ GammaM :=
    { toFun := fun x ↦ ⟨(x : ℝ), x.property⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hf : Function.Surjective f := by
    intro y
    have hyL : (y : ℝ) ∈ GammaL :=
      exponentialValueSubgroup_le_of_extends u w hML y.property
    let x : J := ⟨⟨(y : ℝ), hyL⟩, y.property⟩
    refine ⟨x, ?_⟩
    exact Subtype.ext rfl
  let HKM : AddSubgroup GammaM := GammaK.comap GammaM.subtype
  have hcomap : HKM.comap f = H.addSubgroupOf J := by
    ext x
    rfl
  have hrelative : H.relIndex J = exponentialRamificationIndex v u := by
    have hi := AddSubgroup.index_comap_of_surjective HKM hf
    rw [hcomap] at hi
    simpa only [AddSubgroup.relIndex, exponentialRamificationIndex,
      ExponentialValueGroupQuotient, AddSubgroup.index_eq_card,
      GammaK, GammaM, HKM] using hi
  rw [← hrelative]
  simpa only [exponentialRamificationIndex, ExponentialValueGroupQuotient,
    AddSubgroup.index_eq_card, GammaK, GammaM, GammaL, H, J] using
      (AddSubgroup.relIndex_mul_index hHJ)

/-- In a finite relative extension, the ramification index of the lower
stage is at most that of the whole exact valued-field tower. -/
theorem exponentialRamificationIndex_le_in_tower
    [FiniteDimensional M L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (u : LubinTate.Valuations.ExponentialValuation M)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hKM : ∀ a : K, u (algebraMap K M a) = v a)
    (hML : ∀ a : M, w (algebraMap M L a) = u a) :
    exponentialRamificationIndex v u ≤ exponentialRamificationIndex v w := by
  calc
    exponentialRamificationIndex v u ≤
        exponentialRamificationIndex v u * exponentialRamificationIndex u w :=
      Nat.le_mul_of_pos_right _
        (exponentialRamificationIndex_pos_of_finiteDimensional u w hML)
    _ = exponentialRamificationIndex v w :=
      exponentialRamificationIndex_mul_in_tower v u w hKM hML

/-- Ramification index is monotone along an algebra embedding of finite
extensions.  The embedding supplies the relative algebra and scalar-tower
structures used by `exponentialRamificationIndex_le_in_tower`. -/
theorem exponentialRamificationIndex_le_of_algHom
    {K E D : Type} [Field K] [Field E] [Field D]
    [Algebra K E] [Algebra K D]
    [FiniteDimensional K D]
    (i : E →ₐ[K] D)
    (v : LubinTate.Valuations.ExponentialValuation K)
    (u : LubinTate.Valuations.ExponentialValuation E)
    (w : LubinTate.Valuations.ExponentialValuation D)
    (hKE : ∀ x : K, u (algebraMap K E x) = v x)
    (hED : ∀ x : E, w (i x) = u x) :
    exponentialRamificationIndex v u ≤ exponentialRamificationIndex v w := by
  let : Algebra E D := i.toRingHom.toAlgebra
  let : IsScalarTower K E D := IsScalarTower.of_algebraMap_eq fun x => by
    exact (i.commutes x).symm
  let : FiniteDimensional E D := FiniteDimensional.right K E D
  have hED' : ∀ x : E, w (algebraMap E D x) = u x := by
    intro x
    exact hED x
  exact exponentialRamificationIndex_le_in_tower v u w hKE hED'

end RamificationIndexTower


end Valuations
end AlgebraicNumberTheory

end
