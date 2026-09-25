/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.OnePlaceNormKernel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.RationalComplexification
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.InfinitePlaceOverfield
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.NumberFieldComplexification
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.RamifiedOverextension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.OverextensionArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.InfinitePlaceCompatibility
/-!
# Archimedean local-global compatibility of Artin homomorphisms

This file compares the actual Artin homomorphism at an infinite place
with the global norm-residue homomorphism on idele classes.  The
one-place norm statements are proved from genuine relative ideles
supported at the chosen archimedean place.
-/

@[expose] public section

open scoped NumberField
open NumberField
open IdeleGroup RelativeIdeleGroup

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

omit [IsAbelianGalois K L] in
/-- A determinant norm at one infinite place gives an actual global
idele-class norm.  The witness is the relative idele supported at that
place, transported to an ordinary idele of the extension field. -/
theorem infinitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_infiniteTensorNorm
    (v : InfinitePlace K)
    (x : v.Completionˣ)
    (hx :
      x ∈ infiniteTensorNormSubgroup
        (K := K) (L := L) v) :
    IdeleGroup.infinitePlaceIdeleClass v x ∈
      (_root_.ideleClassNorm K L).range := by
  have hnorm :
      IdeleGroup.infinitePlaceIdele v x ∈
        ideleNormSubgroup (K := K) (L := L) :=
    (infinitePlaceIdele_mem_ideleNormSubgroup_iff
      (K := K) (L := L) v x).2 hx
  obtain ⟨z, hz⟩ := hnorm
  refine
    ⟨QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (_root_.relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z), ?_⟩
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.norm K L
          (_root_.relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L) z)) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.infinitePlaceIdele v x)
  rw [IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv, hz]

omit [FiniteDimensional K L] in
/-- Triviality of the actual chosen infinite-place Artin symbol is
equivalent to membership in the corresponding determinant-norm
subgroup. -/
@[simp]
theorem chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v x = 1 ↔
      x ∈ infiniteTensorNormSubgroup
        (K := K) (L := L) v := by
  change
    x ∈ (chosenInfinitePlaceArtinMonoidHom
      (K := K) (L := L) v).ker ↔ _
  rw [chosenInfinitePlaceArtinMonoidHom_ker
    (K := K) (L := L) v]

/-- An infinite-place element killed by the actual local Artin
homomorphism is killed by the global norm-residue homomorphism after
insertion as a one-place idele class. -/
theorem globalNormResidueMonoidHom_infinitePlaceIdeleClass_eq_one_of_localArtin_eq_one
    (v : InfinitePlace K)
    (x : v.Completionˣ)
    (hx :
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v x = 1) :
    globalNormResidueMonoidHom K L
        (IdeleGroup.infinitePlaceIdeleClass v x) = 1 := by
  rw [globalNormResidueMonoidHom_eq_one_iff]
  exact
    infinitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_infiniteTensorNorm
      (K := K) (L := L) v x
      ((chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm
        (K := K) (L := L) v x).1 hx)

/-- The infinite tensor norm subgroup lies in the kernel of the global
norm-residue homomorphism restricted to the one-place idele class map. -/
theorem infiniteTensorNormSubgroup_le_globalNormResidueKernel
    (v : InfinitePlace K) :
    infiniteTensorNormSubgroup
        (K := K) (L := L) v ≤
      ((globalNormResidueMonoidHom K L).comp
        (IdeleGroup.infinitePlaceIdeleClass v)).ker := by
  intro x hx
  exact
    globalNormResidueMonoidHom_infinitePlaceIdeleClass_eq_one_of_localArtin_eq_one
      (K := K) (L := L) v x
      ((chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm
        (K := K) (L := L) v x).2 hx)

/-- A positive element at a real infinite place gives an actual
idele-class norm. -/
theorem infinitePlaceIdeleClass_mem_ideleClassNorm_range_of_real_pos
    (v : InfinitePlace K)
    (hvReal : v.IsReal)
    (x : v.Completionˣ)
    (hx :
      0 <
        InfinitePlace.Completion.ringEquivRealOfIsReal
          hvReal (x : v.Completion)) :
    IdeleGroup.infinitePlaceIdeleClass v x ∈
      (_root_.ideleClassNorm K L).range := by
  apply
    infinitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_infiniteTensorNorm
      (K := K) (L := L) v x
  exact
    (chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm
      (K := K) (L := L) v x).1
      (chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
        (K := K) (L := L) v hvReal x hx)

/-- The global norm-residue symbol of a positive real one-place idele
class is trivial. -/
theorem globalNormResidueMonoidHom_infinitePlaceIdeleClass_eq_one_of_real_pos
    (v : InfinitePlace K)
    (hvReal : v.IsReal)
    (x : v.Completionˣ)
    (hx :
      0 <
        InfinitePlace.Completion.ringEquivRealOfIsReal
          hvReal (x : v.Completion)) :
    globalNormResidueMonoidHom K L
        (IdeleGroup.infinitePlaceIdeleClass v x) = 1 := by
  rw [globalNormResidueMonoidHom_eq_one_iff]
  exact
    infinitePlaceIdeleClass_mem_ideleClassNorm_range_of_real_pos
      (K := K) (L := L) v hvReal x hx

/-- At an actually unramified infinite place, both the restricted
global norm-residue map and the chosen local Artin map are trivial,
hence the local-global compatibility square commutes. -/
theorem globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_of_unramified
    (v : InfinitePlace K)
    (hUnramified :
      (chosenInfinitePlaceAbove (L := L) v).IsUnramified K) :
    (globalNormResidueMonoidHom K L).comp
        (IdeleGroup.infinitePlaceIdeleClass v) =
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v := by
  apply MonoidHom.ext
  intro x
  have hlocal :
      chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v x = 1 := by
    unfold chosenInfinitePlaceArtinMonoidHom
    unfold infinitePlaceArtinMonoidHomOfPlace
    rw [dite_eq_left hUnramified]
    rfl
  have hglobal :
      globalNormResidueMonoidHom K L
          (IdeleGroup.infinitePlaceIdeleClass v x) = 1 :=
    globalNormResidueMonoidHom_infinitePlaceIdeleClass_eq_one_of_localArtin_eq_one
      (K := K) (L := L) v x hlocal
  rw [MonoidHom.comp_apply, hglobal, hlocal]

/-- At a complex base place the chosen place upstairs is automatically
unramified, so the archimedean local-global compatibility square is
trivial. -/
theorem globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_of_isComplex
    (v : InfinitePlace K)
    (hvComplex : v.IsComplex) :
    (globalNormResidueMonoidHom K L).comp
        (IdeleGroup.infinitePlaceIdeleClass v) =
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v := by
  apply
    globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_of_unramified
      (K := K) (L := L) v
  apply InfinitePlace.isUnramified_iff.mpr
  apply Or.inr
  rw [chosenInfinitePlaceAbove_comap (L := L) v]
  exact hvComplex

/-- At an actually unramified infinite place, one-place idele-class
norm membership is exactly local determinant-norm membership. -/
theorem infinitePlaceIdeleClass_mem_ideleClassNorm_range_iff_of_unramified
    (v : InfinitePlace K)
    (hUnramified :
      (chosenInfinitePlaceAbove (L := L) v).IsUnramified K)
    (x : v.Completionˣ) :
    IdeleGroup.infinitePlaceIdeleClass v x ∈
        (_root_.ideleClassNorm K L).range ↔
      x ∈ infiniteTensorNormSubgroup
        (K := K) (L := L) v := by
  rw [← globalNormResidueMonoidHom_eq_one_iff]
  rw [←
    chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm
      (K := K) (L := L) v x]
  have hcompat :
      globalNormResidueMonoidHom K L
          (IdeleGroup.infinitePlaceIdeleClass v x) =
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v x := by
    simpa only [MonoidHom.comp_apply] using
      DFunLike.congr_fun
        (globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_of_unramified
          (K := K) (L := L) v hUnramified) x
  rw [hcompat]

omit [FiniteDimensional K L] in
/-- At an actually ramified real place, negative one is not a local
determinant norm.  This is the concrete real/complex norm obstruction:
every norm from the complex completion is positive. -/
theorem neg_one_not_mem_infiniteTensorNormSubgroup_of_ramified
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    (-1 : v.Completionˣ) ∉
      infiniteTensorNormSubgroup
        (K := K) (L := L) v := by
  let w := chosenInfinitePlaceAbove (L := L) v
  have hw :
      w.comap (algebraMap K L) = v :=
    chosenInfinitePlaceAbove_comap (L := L) v
  let chosenInfinitePlaceLiesOver : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  rw [infiniteTensorNormSubgroup_eq_localNormSubgroup
    (K := K) (L := L) v w hw]
  rintro ⟨z, hz⟩
  have hvReal : v.IsReal := by
    exact hw ▸ hRamified.isReal
  have hwComplex : w.IsComplex :=
    hRamified.isComplex
  have hpos :=
    infinitePlace_normUnits_real_complex_pos
      (K := K) (K' := L) v w hw
      hvReal hwComplex z
  have hneg : (0 : ℝ) < -1 := by
    rw [hz] at hpos
    simpa only [
      InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      Units.coe_neg_one, map_neg, map_one] using hpos
  norm_num at hneg

omit [FiniteDimensional K L] in
/-- The actual chosen local Artin symbol of negative one is nontrivial
at a ramified real place. -/
theorem chosenInfinitePlaceArtinMonoidHom_neg_one_ne_one_of_ramified
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (-1 : v.Completionˣ) ≠ 1 := by
  intro htrivial
  exact
    neg_one_not_mem_infiniteTensorNormSubgroup_of_ramified
      (K := K) (L := L) v hRamified
      ((chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm
        (K := K) (L := L) v (-1 : v.Completionˣ)).1 htrivial)

omit [NumberField K] in
/-- Every unit at a real completion is positive either as given or
after multiplication by negative one. -/
private theorem realCompletionUnit_pos_or_neg_one_mul_pos
    (v : InfinitePlace K)
    (hvReal : v.IsReal)
    (x : v.Completionˣ) :
    0 <
        InfinitePlace.Completion.ringEquivRealOfIsReal
          hvReal (x : v.Completion) ∨
      0 <
        InfinitePlace.Completion.ringEquivRealOfIsReal
          hvReal
          (((-1 : v.Completionˣ) * x : v.Completionˣ) :
            v.Completion) := by
  let e :
      v.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal hvReal
  have hne :
      e (x : v.Completion) ≠ 0 :=
    (map_ne_zero e).2 (Units.ne_zero x)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · right
    change 0 < e ((-1 : v.Completion) * (x : v.Completion))
    rw [map_mul, map_neg, map_one]
    simpa only [neg_one_mul] using neg_pos.mpr hneg
  · exact Or.inl hpos

/-- At a real place, the full archimedean local-global Artin square is
equivalent to its single value at negative one.  Positivity kills both
maps, so this isolates the unique ramified real source calculation. -/
theorem globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_eq_iff_neg_one
    (v : InfinitePlace K)
    (hvReal : v.IsReal) :
    (globalNormResidueMonoidHom K L).comp
          (IdeleGroup.infinitePlaceIdeleClass v) =
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v ↔
      globalNormResidueMonoidHom K L
          (IdeleGroup.infinitePlaceIdeleClass v
            (-1 : v.Completionˣ)) =
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (-1 : v.Completionˣ) := by
  constructor
  · intro h
    exact DFunLike.congr_fun h (-1 : v.Completionˣ)
  · intro hneg
    apply MonoidHom.ext
    intro x
    rcases
        realCompletionUnit_pos_or_neg_one_mul_pos
          (K := K) v hvReal x with hx | hx
    · rw [MonoidHom.comp_apply,
        globalNormResidueMonoidHom_infinitePlaceIdeleClass_eq_one_of_real_pos
          (K := K) (L := L) v hvReal x hx,
        chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
          (K := K) (L := L) v hvReal x hx]
    · have hglobal :
          globalNormResidueMonoidHom K L
              (IdeleGroup.infinitePlaceIdeleClass v
                ((-1 : v.Completionˣ) * x)) = 1 :=
        globalNormResidueMonoidHom_infinitePlaceIdeleClass_eq_one_of_real_pos
          (K := K) (L := L) v hvReal
          ((-1 : v.Completionˣ) * x) hx
      have hlocal :
          chosenInfinitePlaceArtinMonoidHom
              (K := K) (L := L) v
              ((-1 : v.Completionˣ) * x) = 1 :=
        chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
          (K := K) (L := L) v hvReal
          ((-1 : v.Completionˣ) * x) hx
      change
        ((globalNormResidueMonoidHom K L).comp
          (IdeleGroup.infinitePlaceIdeleClass v))
            ((-1 : v.Completionˣ) * x) = 1 at hglobal
      rw [map_mul] at hglobal hlocal
      have hglobalX :
          globalNormResidueMonoidHom K L
              (IdeleGroup.infinitePlaceIdeleClass v x) =
            (globalNormResidueMonoidHom K L
              (IdeleGroup.infinitePlaceIdeleClass v
                (-1 : v.Completionˣ)))⁻¹ :=
        eq_inv_of_mul_eq_one_right hglobal
      have hlocalX :
          chosenInfinitePlaceArtinMonoidHom
              (K := K) (L := L) v x =
            (chosenInfinitePlaceArtinMonoidHom
              (K := K) (L := L) v
              (-1 : v.Completionˣ))⁻¹ :=
        eq_inv_of_mul_eq_one_right hlocal
      rw [MonoidHom.comp_apply, hglobalX, hlocalX, hneg]

/-- For an arbitrary infinite place, the local-global Artin square is
reduced canonically to the negative-one calculation in the real case;
the complex case is already trivial. -/
theorem
    globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_eq_iff_real_neg_one
    (v : InfinitePlace K) :
    (globalNormResidueMonoidHom K L).comp
          (IdeleGroup.infinitePlaceIdeleClass v) =
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v ↔
      ∀ _hvReal : v.IsReal,
        globalNormResidueMonoidHom K L
            (IdeleGroup.infinitePlaceIdeleClass v
              (-1 : v.Completionˣ)) =
          chosenInfinitePlaceArtinMonoidHom
            (K := K) (L := L) v
            (-1 : v.Completionˣ) := by
  constructor
  · intro h _hvReal
    exact DFunLike.congr_fun h (-1 : v.Completionˣ)
  · intro h
    rcases v.isReal_or_isComplex with hvReal | hvComplex
    · exact
        (globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_eq_iff_neg_one
          (K := K) (L := L) v hvReal).2
          (h hvReal)
    · exact
        globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_of_isComplex
          (K := K) (L := L) v hvComplex

/-- The global norm-residue homomorphism restricted to a single
archimedean component is the actual local Artin homomorphism at that
place.

At an unramified archimedean place both maps are trivial.  In the only
remaining case, a ramified real place, positivity reduces the equality
to negative one and the complexification overextension identifies its
global symbol with the genuine local complex conjugation. -/
theorem globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass
    (v : InfinitePlace K) :
    (globalNormResidueMonoidHom K L).comp
          (IdeleGroup.infinitePlaceIdeleClass v) =
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v := by
  rw [
    globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_eq_iff_real_neg_one]
  intro _hvReal
  by_cases hUnramified :
      (chosenInfinitePlaceAbove (L := L) v).IsUnramified K
  · exact
      DFunLike.congr_fun
        (globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass_of_unramified
          (K := K) (L := L) v hUnramified)
        (-1 : v.Completionˣ)
  · exact
      globalNormResidueMonoidHom_infinitePlaceIdeleClass_neg_one_of_ramified
        (K := K) (L := L) v hUnramified

/-- One-place archimedean norm membership is exactly membership in the
local determinant-norm subgroup.  This is the norm-kernel form of
archimedean local-global Artin compatibility. -/
theorem infinitePlaceIdeleClass_mem_ideleClassNorm_range_iff
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    IdeleGroup.infinitePlaceIdeleClass v x ∈
        (_root_.ideleClassNorm K L).range ↔
      x ∈ infiniteTensorNormSubgroup
        (K := K) (L := L) v := by
  rw [← globalNormResidueMonoidHom_eq_one_iff]
  rw [←
    chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm
      (K := K) (L := L) v x]
  have hcompat :
      globalNormResidueMonoidHom K L
          (IdeleGroup.infinitePlaceIdeleClass v x) =
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v x := by
    simpa only [MonoidHom.comp_apply] using
      DFunLike.congr_fun
        (globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass
          (K := K) (L := L) v) x
  rw [hcompat]

end Reciprocity
end GlobalClassFieldTheory
