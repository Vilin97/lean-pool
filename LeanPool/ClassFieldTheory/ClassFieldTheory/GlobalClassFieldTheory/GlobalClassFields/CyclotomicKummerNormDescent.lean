/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.KummerNormDescent
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SUnitKummerNormRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormalClosureNorm
public import Mathlib.NumberTheory.Cyclotomic.Basic
/-!
# Cyclotomic descent for full S-unit Kummer norms

This file implements the roots-of-unity descent in the existence proof of
global class field theory.  Starting from a finite seed of finite places of
`K`, it enlarges the seed just enough that its full inverse image in
`CyclotomicField n K` is a chosen Kummer norm support.  Thus the full
S-unit Kummer extension over the cyclotomic field has its concrete norm
subgroup described by Kummer theory, while the support is still exactly a
full inverse image and hence descends through the cyclotomic norm.

The final normal-closure step turns the resulting finite extension of `K`
into a genuine finite Galois extension without enlarging its norm subgroup.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain
open KummerTheory

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
local instance cyclotomicKummerNormDescent_neZero
    (n : ℕ+) : NeZero (n : ℕ) :=
  ⟨n.ne_zero⟩

attribute [local instance] cyclotomicKummerNormDescent_neZero

open scoped Classical in
noncomputable local instance
    cyclotomicKummerNormDescent_cyclotomicFiniteDimensional
    (n : ℕ+) :
    FiniteDimensional K (CyclotomicField (n : ℕ) K) :=
  IsCyclotomicExtension.finiteDimensional
    {(n : ℕ)} K (CyclotomicField (n : ℕ) K)

attribute [local instance] cyclotomicKummerNormDescent_cyclotomicFiniteDimensional

open scoped Classical in
noncomputable local instance
    cyclotomicKummerNormDescent_cyclotomicIsGalois
    (n : ℕ+) :
    IsGalois K (CyclotomicField (n : ℕ) K) :=
  IsCyclotomicExtension.isGalois
    {(n : ℕ)} K (CyclotomicField (n : ℕ) K)

attribute [local instance] cyclotomicKummerNormDescent_cyclotomicIsGalois

open scoped Classical in
private theorem cyclotomicKummerNormDescent_primitiveRoots_nonempty
    (n : ℕ+) :
    (primitiveRoots (n : ℕ)
      (CyclotomicField (n : ℕ) K)).Nonempty := by
  obtain ⟨ζ, hζ⟩ :=
    (CyclotomicField.isCyclotomicExtension (n : ℕ) K).exists_isPrimitiveRoot
      (Set.mem_singleton (n : ℕ)) n.ne_zero
  exact ⟨ζ, (mem_primitiveRoots n.pos).2 hζ⟩

open scoped Classical in
private theorem cyclotomicKummerNormDescent_natCast_ne_zero
    (n : ℕ+) :
    ((n : ℕ) : CyclotomicField (n : ℕ) K) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr n.ne_zero

open scoped Classical in
/-- A finite support on `K` whose full inverse image in
`CyclotomicField n K` contains the chosen Kummer norm support upstairs.

The construction first forms the chosen support above the prescribed
seed and then adds the places below it.  Taking all places above this enlarged
base support saturates every fibre without losing the largeness and exponent
support required by the full S-unit Kummer calculation. -/
noncomputable def cyclotomicKummerNormSupport
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  let C := CyclotomicField (n : ℕ) K
  let seedAbove :=
    finitePlacesAbove (K := K) (L := C) seed
  let canonicalAbove :=
    sUnitKummerNormSupport (K := C) n seedAbove
  exact seed ∪ canonicalAbove.image
    (fun W => finitePlaceBelow (K := K) W)

open scoped Classical in
/-- The prescribed finite seed is contained in its cyclotomic Kummer norm
support. -/
theorem subset_cyclotomicKummerNormSupport
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    seed ⊆ cyclotomicKummerNormSupport (K := K) n seed := by
  classical
  intro v hv
  simp only [cyclotomicKummerNormSupport]
  exact Finset.mem_union_left _ hv

open scoped Classical in
/-- All finite places of the cyclotomic field above the enlarged base
support.  This is the fibre-saturated support used by norm descent. -/
noncomputable def cyclotomicKummerNormSupportAbove
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset
      (HeightOneSpectrum
        (𝓞 (CyclotomicField (n : ℕ) K))) := by
  let C := CyclotomicField (n : ℕ) K
  exact finitePlacesAbove (K := K) (L := C)
    (cyclotomicKummerNormSupport (K := K) n seed)

open scoped Classical in
/-- Membership in the upstairs support is exactly membership of the place
below in the enlarged base support. -/
@[simp]
theorem mem_cyclotomicKummerNormSupportAbove_iff
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K)))
    (W :
      HeightOneSpectrum
        (𝓞 (CyclotomicField (n : ℕ) K))) :
    W ∈ cyclotomicKummerNormSupportAbove (K := K) n seed ↔
      finitePlaceBelow (K := K) W ∈
        cyclotomicKummerNormSupport (K := K) n seed := by
  let C := CyclotomicField (n : ℕ) K
  simpa only [cyclotomicKummerNormSupportAbove] using
    (mem_finitePlacesAbove_iff
      (K := K) (L := C)
      (cyclotomicKummerNormSupport (K := K) n seed) W)

open scoped Classical in
/-- The fibre-saturated support upstairs is already fixed by the chosen
Kummer-support enlargement. -/
theorem sUnitKummerNormSupport_cyclotomicKummerNormSupportAbove
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnitKummerNormSupport
        (K := CyclotomicField (n : ℕ) K) n
        (cyclotomicKummerNormSupportAbove (K := K) n seed) =
      cyclotomicKummerNormSupportAbove (K := K) n seed := by
  classical
  let C := CyclotomicField (n : ℕ) K
  let seedAbove :=
    finitePlacesAbove (K := K) (L := C) seed
  let canonicalAbove :=
    sUnitKummerNormSupport (K := C) n seedAbove
  let baseSupport :=
    cyclotomicKummerNormSupport (K := K) n seed
  let saturatedAbove :=
    cyclotomicKummerNormSupportAbove (K := K) n seed
  have hcanonical :
      canonicalAbove ⊆ saturatedAbove := by
    intro W hW
    rw [show saturatedAbove =
      finitePlacesAbove (K := K) (L := C) baseSupport by
        rfl]
    rw [mem_finitePlacesAbove_iff]
    change finitePlaceBelow (K := K) W ∈
      seed ∪ canonicalAbove.image
        (fun V => finitePlaceBelow (K := K) V)
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨W, hW, rfl⟩)
  apply Finset.Subset.antisymm
  · intro W hW
    have hW' :
        (W ∈ saturatedAbove ∨
          W ∈ IdeleGroup.sufficientlyLargeFiniteSet (K := C)) ∨
          W ∈ chosenUnitFiniteSupport
            (K := C)
            (Units.mk0 ((n : ℕ) : C)
              (cyclotomicKummerNormDescent_natCast_ne_zero
                (K := K) n)) := by
      simpa only [sUnitKummerNormSupport, Finset.mem_union] using hW
    rcases hW' with (hWsat | hWlarge) | hWexp
    · exact hWsat
    · apply hcanonical
      simp only [canonicalAbove, sUnitKummerNormSupport,
        Finset.mem_union]
      exact Or.inl (Or.inr hWlarge)
    · apply hcanonical
      simp only [canonicalAbove, sUnitKummerNormSupport,
        Finset.mem_union]
      exact Or.inr hWexp
  · exact subset_sUnitKummerNormSupport
      (K := C) n saturatedAbove

open scoped Classical in
/-- Enlarging a support by the cyclotomic Kummer requirements is
idempotent.  In particular, downstream neighbourhood arguments may choose a
support containing these requirements from the outset without a second
change of support. -/
@[simp]
theorem cyclotomicKummerNormSupport_idem
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    cyclotomicKummerNormSupport (K := K) n
        (cyclotomicKummerNormSupport (K := K) n seed) =
      cyclotomicKummerNormSupport (K := K) n seed := by
  classical
  let C := CyclotomicField (n : ℕ) K
  let S := cyclotomicKummerNormSupport (K := K) n seed
  let SAbove :=
    cyclotomicKummerNormSupportAbove (K := K) n seed
  have hstable :
      sUnitKummerNormSupport (K := C) n SAbove = SAbove := by
    simpa only [C, SAbove] using
      sUnitKummerNormSupport_cyclotomicKummerNormSupportAbove
        (K := K) n seed
  apply Finset.Subset.antisymm
  · intro v hv
    change v ∈
      S ∪
        (sUnitKummerNormSupport (K := C) n SAbove).image
          (fun W => finitePlaceBelow (K := K) W) at hv
    rcases Finset.mem_union.mp hv with hvS | hvAbove
    · exact hvS
    · rw [hstable] at hvAbove
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hvAbove
      exact
        (mem_cyclotomicKummerNormSupportAbove_iff
          (K := K) n seed W).mp hW
  · exact subset_cyclotomicKummerNormSupport (K := K) n S

open scoped Classical in
/-- The actual full S-unit Kummer extension over the cyclotomic base,
formed inside its fixed separable closure and using the chosen enlargement
of the fibre-saturated support above `K`.  The preceding stability theorem
shows that this enlargement is equal to the fibre-saturated support; retaining
it in the definition keeps the extension definitionally aligned with the
exact Kummer norm-realization theorem. -/
noncomputable abbrev cyclotomicFullSUnitKummerExtension
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    IntermediateField
      (CyclotomicField (n : ℕ) K)
      (SeparableClosure (CyclotomicField (n : ℕ) K)) :=
  KummerTheory.fullSUnitKummerExtension
    (K := CyclotomicField (n : ℕ) K)
    (Omega := SeparableClosure (CyclotomicField (n : ℕ) K))
    n (sUnitKummerNormSupport
      (K := CyclotomicField (n : ℕ) K) n
      (cyclotomicKummerNormSupportAbove (K := K) n seed))

open scoped Classical in
/-- The cyclotomic full S-unit Kummer extension is Galois over the
cyclotomic base. -/
theorem cyclotomicFullSUnitKummerExtension_isGalois
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    IsGalois
      (CyclotomicField (n : ℕ) K)
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) := by
  simpa only [cyclotomicFullSUnitKummerExtension] using
    (KummerTheory.fullSUnitKummerExtension_isGalois
      (K := CyclotomicField (n : ℕ) K)
      (Omega := SeparableClosure (CyclotomicField (n : ℕ) K))
      n (sUnitKummerNormSupport
        (K := CyclotomicField (n : ℕ) K) n
        (cyclotomicKummerNormSupportAbove (K := K) n seed)))

open scoped Classical in
/-- The cyclotomic full S-unit Kummer extension is finite over the
cyclotomic base. -/
theorem cyclotomicFullSUnitKummerExtension_finiteDimensional
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    FiniteDimensional
      (CyclotomicField (n : ℕ) K)
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) := by
  let C := CyclotomicField (n : ℕ) K
  have hmu : (primitiveRoots (n : ℕ) C).Nonempty :=
    cyclotomicKummerNormDescent_primitiveRoots_nonempty
      (K := K) n
  have hnC : ((n : ℕ) : C) ≠ 0 :=
    cyclotomicKummerNormDescent_natCast_ne_zero
      (K := K) n
  simpa only [C, cyclotomicFullSUnitKummerExtension] using
    (KummerTheory.fullSUnitKummerExtension_finiteDimensional
      (K := C) (Omega := SeparableClosure C)
      n hnC hmu
      (sUnitKummerNormSupport (K := C) n
        (cyclotomicKummerNormSupportAbove (K := K) n seed)))

open scoped Classical in
noncomputable local instance
    cyclotomicKummerNormDescent_kummerFiniteDimensional
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    FiniteDimensional
      (CyclotomicField (n : ℕ) K)
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
  cyclotomicFullSUnitKummerExtension_finiteDimensional
    (K := K) n seed

attribute [local instance] cyclotomicKummerNormDescent_kummerFiniteDimensional

open scoped Classical in
/-- The Kummer layer is a number field via its finite extension of the
cyclotomic number field.  This is deliberately a named, non-instance boundary:
downstream base-tower instances must not make every `NumberField` search unfold
the full S-unit Kummer construction. -/
private theorem cyclotomicKummerNormDescent_kummerNumberField
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    NumberField
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
  NumberField.of_module_finite
    (CyclotomicField (n : ℕ) K)
    (cyclotomicFullSUnitKummerExtension (K := K) n seed)

open scoped Classical in
/-- The expensive Kummer norm computation over the cyclotomic base, isolated
before the `K`-to-Kummer-field instance tower is introduced. -/
private theorem
    cyclotomicFullSUnitKummerExtension_cyclotomicNormRange
    (n : ℕ+)
    (hn : 1 < (n : ℕ))
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    let C := CyclotomicField (n : ℕ) K
    let S' := cyclotomicKummerNormSupportAbove (K := K) n seed
    let E := cyclotomicFullSUnitKummerExtension (K := K) n seed
    letI : NumberField E :=
      cyclotomicKummerNormDescent_kummerNumberField (K := K) n seed
    (_root_.ideleClassNorm C E).range =
      ideleClassPowerLocalUnitSubgroup (K := C) n S' ∅ := by
  classical
  dsimp only
  let C := CyclotomicField (n : ℕ) K
  let S' := cyclotomicKummerNormSupportAbove (K := K) n seed
  let E := cyclotomicFullSUnitKummerExtension (K := K) n seed
  let : NumberField E :=
    cyclotomicKummerNormDescent_kummerNumberField (K := K) n seed
  have hmu : (primitiveRoots (n : ℕ) C).Nonempty :=
    cyclotomicKummerNormDescent_primitiveRoots_nonempty
      (K := K) n
  have hstable :
      sUnitKummerNormSupport (K := C) n S' = S' := by
    simpa only [C, S'] using
      sUnitKummerNormSupport_cyclotomicKummerNormSupportAbove
        (K := K) n seed
  have hNormCanonical :
      (_root_.ideleClassNorm C E).range =
        ideleClassPowerLocalUnitSubgroup (K := C) n
          (sUnitKummerNormSupport (K := C) n S') ∅ := by
    simpa only [C, S', E, cyclotomicFullSUnitKummerExtension] using
      (fullSUnitKummerExtension_ideleClassNormRange_eq_powerLocalUnit
        (K := C) (Omega := SeparableClosure C)
        n hn hmu S')
  exact hNormCanonical.trans
    (congrArg
      (fun T => ideleClassPowerLocalUnitSubgroup (K := C) n T ∅)
      hstable)

open scoped Classical in
/-- The cyclotomic S-unit Kummer extension is an algebra over the original base field. -/
@[reducible]
noncomputable local instance
    cyclotomicKummerNormDescentKummerAlgebraOverBase
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    Algebra K
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
  ((algebraMap
      (CyclotomicField (n : ℕ) K)
      (cyclotomicFullSUnitKummerExtension (K := K) n seed)).comp
    (algebraMap K (CyclotomicField (n : ℕ) K))).toAlgebra

attribute [local instance] cyclotomicKummerNormDescentKummerAlgebraOverBase

open scoped Classical in
@[reducible]
private noncomputable def
    cyclotomicKummerNormDescent_kummerSMulOverBase
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    SMul K
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
  Algebra.toSMul
    (self := cyclotomicKummerNormDescentKummerAlgebraOverBase
      (K := K) n seed)

open scoped Classical in
@[reducible]
private noncomputable def
    cyclotomicKummerNormDescent_kummerModuleOverBase
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    Module K
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
  Algebra.toModule

open scoped Classical in
private theorem
    cyclotomicKummerNormDescent_kummerScalarTower
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    IsScalarTower K
      (CyclotomicField (n : ℕ) K)
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
  IsScalarTower.of_algebraMap_eq' rfl

open scoped Classical in
noncomputable local instance
    cyclotomicKummerNormDescent_kummerFiniteDimensionalOverBase
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    FiniteDimensional K
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
  by
    let : IsScalarTower K
        (CyclotomicField (n : ℕ) K)
        (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
      cyclotomicKummerNormDescent_kummerScalarTower (K := K) n seed
    exact FiniteDimensional.trans K
      (CyclotomicField (n : ℕ) K)
      (cyclotomicFullSUnitKummerExtension (K := K) n seed)

attribute [local instance] cyclotomicKummerNormDescent_kummerFiniteDimensionalOverBase

open scoped Classical in
/-- The norm range of the actual cyclotomic full S-unit Kummer extension,
viewed as a finite extension of `K`, lies in the power-local-unit subgroup
on the enlarged base support.  This is the pointwise tower-norm step in the
roots-of-unity descent. -/
theorem
    cyclotomicFullSUnitKummerExtension_ideleClassNormRange_le_powerLocalUnit
    (n : ℕ+)
    (hn : 1 < (n : ℕ))
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    let E := cyclotomicFullSUnitKummerExtension (K := K) n seed
    letI : NumberField E :=
      cyclotomicKummerNormDescent_kummerNumberField (K := K) n seed
    (_root_.ideleClassNorm K E).range ≤
      ideleClassPowerLocalUnitSubgroup
        (K := K) n
        (cyclotomicKummerNormSupport (K := K) n seed) ∅ := by
  classical
  dsimp only
  let C := CyclotomicField (n : ℕ) K
  let S := cyclotomicKummerNormSupport (K := K) n seed
  let S' := cyclotomicKummerNormSupportAbove (K := K) n seed
  let E := cyclotomicFullSUnitKummerExtension (K := K) n seed
  let : IsScalarTower K C E :=
    cyclotomicKummerNormDescent_kummerScalarTower (K := K) n seed
  let : NumberField E :=
    cyclotomicKummerNormDescent_kummerNumberField (K := K) n seed
  have hNormC :
      (_root_.ideleClassNorm C E).range =
        ideleClassPowerLocalUnitSubgroup (K := C) n S' ∅ :=
    cyclotomicFullSUnitKummerExtension_cyclotomicNormRange
      (K := K) n hn seed
  have hSupport :
      ∀ W : HeightOneSpectrum (𝓞 C),
        W ∈ S' ↔ finitePlaceBelow (K := K) W ∈ S := by
    intro W
    simpa only [C, S, S'] using
      (mem_cyclotomicKummerNormSupportAbove_iff
        (K := K) n seed W)
  rintro _ ⟨c, rfl⟩
  rw [← ordinaryIdeleClassNorm_tower
    (K := K) (M := C) (L := E) c]
  apply
    (ideleClassNorm_map_powerLocalUnitSubgroup_le_of_supports_above
      (K := K) (L := C) n S S' hSupport)
  refine ⟨_root_.ideleClassNorm C E c, ?_, rfl⟩
  rw [← hNormC]
  exact ⟨c, rfl⟩

open scoped Classical in
/-- Passing to the finite normal closure produces an actual finite Galois
extension of `K` whose norm range is still contained in the prescribed
power-local-unit subgroup.  This is the finite Galois norm neighbourhood
constructed in the roots-of-unity-free case. -/
theorem
    cyclotomicFullSUnitKummerFiniteNormalClosure_ideleClassNormRange_le_powerLocalUnit
    (n : ℕ+)
    (hn : 1 < (n : ℕ))
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    let E := cyclotomicFullSUnitKummerExtension (K := K) n seed
    letI : NumberField E :=
      cyclotomicKummerNormDescent_kummerNumberField (K := K) n seed
    let F := finiteNormalClosure K E
    (_root_.ideleClassNorm K F).range ≤
      ideleClassPowerLocalUnitSubgroup
        (K := K) n
        (cyclotomicKummerNormSupport (K := K) n seed) ∅ := by
  classical
  dsimp only
  let E := cyclotomicFullSUnitKummerExtension (K := K) n seed
  let : NumberField E :=
    cyclotomicKummerNormDescent_kummerNumberField (K := K) n seed
  let F := finiteNormalClosure K E
  calc
    (_root_.ideleClassNorm K F).range ≤
        (_root_.ideleClassNorm K E).range := by
      simpa only [F] using
        (finiteNormalClosure_ideleClassNorm_range_le_source
          (K := K) (L := E))
    _ ≤ ideleClassPowerLocalUnitSubgroup
          (K := K) n
          (cyclotomicKummerNormSupport (K := K) n seed) ∅ := by
      simpa only [E] using
        (cyclotomicFullSUnitKummerExtension_ideleClassNormRange_le_powerLocalUnit
          (K := K) n hn seed)

end GlobalClassFields
end GlobalClassFieldTheory
