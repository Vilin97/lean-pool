/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PowerCongruenceCore
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.CyclotomicKummerNormDescent
/-!
# Class fields of closed finite-index idele-class subgroups

For a closed finite-index subgroup `H` of the idele class group, the
canonical ray modulus inside `H` supplies the finite seed for the full
S-unit Kummer construction.  When `H` is proper, the Kummer exponent is
the index of `H`; when `H` is the whole group, exponent two gives a
uniform finite Galois norm neighbourhood and the required containment is
automatic.

The finite normal closure of the cyclotomic full S-unit Kummer extension
therefore has ordinary idele-class norm range contained in `H`.
Finite-abelian classification applied to that actual norm neighbourhood
then realizes `H`, transported to the canonical embedded copy of the base
field, as an exact determinant-norm subgroup.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain
open GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- The Kummer exponent attached to a closed finite-index idele-class
subgroup.  A proper subgroup uses its exact index.  The top subgroup uses
exponent two, so the same concrete finite Galois construction also covers
the trivial class field case. -/
noncomputable def closedFiniteIndexNormExponent
    (H : Subgroup (IdeleClassGroup K))
    [H.FiniteIndex] :
    ℕ+ :=
  if H = ⊤ then 2
  else
    ⟨H.index,
      Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩

open scoped Classical in
/-- For a proper finite-index subgroup, its norm exponent is its index. -/
theorem closedFiniteIndexNormExponent_eq_index
    (H : Subgroup (IdeleClassGroup K))
    [H.FiniteIndex]
    (hH : H ≠ ⊤) :
    closedFiniteIndexNormExponent (K := K) H =
      ⟨H.index,
        Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩ := by
  change
    (if H = ⊤ then (2 : ℕ+) else
      H.index.toPNat (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)) =
      H.index.toPNat (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
  exact ite_eq_right hH

open scoped Classical in
/-- The Kummer exponent attached to a finite-index subgroup is always
strictly larger than one. -/
theorem one_lt_closedFiniteIndexNormExponent
    (H : Subgroup (IdeleClassGroup K))
    [H.FiniteIndex] :
    1 < (closedFiniteIndexNormExponent (K := K) H : ℕ) := by
  by_cases hH : H = ⊤
  · have hexponent : closedFiniteIndexNormExponent (K := K) H = (2 : ℕ+) := by
      change
        (if H = ⊤ then (2 : ℕ+) else
          H.index.toPNat (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)) =
          (2 : ℕ+)
      exact ite_eq_left hH
    have hvalue : (closedFiniteIndexNormExponent (K := K) H : ℕ) = 2 :=
      congrArg PNat.val hexponent
    rw [hvalue]
    decide
  · have hindex : (closedFiniteIndexNormExponent (K := K) H : ℕ) = H.index :=
      congrArg PNat.val (closedFiniteIndexNormExponent_eq_index (K := K) H hH)
    rw [hindex]
    exact Subgroup.one_lt_index_of_ne_top hH

open scoped Classical in
/-- The finite seed used in the norm-neighbourhood construction is the
support of the canonical ray modulus whose congruence subgroup lies in
`H`. -/
noncomputable def closedFiniteIndexNormSeed
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (RayClass.modulusInsideClosedFiniteIndex H hclosed).finitePart.support

open scoped Classical in
/-- The cyclotomic layer used by the finite-index norm construction. -/
noncomputable abbrev closedFiniteIndexNormCyclotomicField
    (H : Subgroup (IdeleClassGroup K))
    [H.FiniteIndex] : Type :=
  CyclotomicField
    (closedFiniteIndexNormExponent (K := K) H : ℕ) K

open scoped Classical in
instance closedFiniteIndexNormExponentNeZero
    (H : Subgroup (IdeleClassGroup K))
    [H.FiniteIndex] :
    NeZero (closedFiniteIndexNormExponent (K := K) H : ℕ) :=
  ⟨(closedFiniteIndexNormExponent (K := K) H).ne_zero⟩

open scoped Classical in
noncomputable instance
    closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension
    (H : Subgroup (IdeleClassGroup K)) [H.FiniteIndex] :
    IsCyclotomicExtension
      {(closedFiniteIndexNormExponent (K := K) H : ℕ)} K
      (closedFiniteIndexNormCyclotomicField (K := K) H) := by
  unfold closedFiniteIndexNormCyclotomicField
  exact
    CyclotomicField.isCyclotomicExtension
      (closedFiniteIndexNormExponent (K := K) H : ℕ) K

open scoped Classical in
noncomputable instance
    closedFiniteIndexNormCyclotomicFieldFiniteDimensional
    (H : Subgroup (IdeleClassGroup K)) [H.FiniteIndex] :
    FiniteDimensional K
      (closedFiniteIndexNormCyclotomicField (K := K) H) :=
  IsCyclotomicExtension.finiteDimensional
    {(closedFiniteIndexNormExponent (K := K) H : ℕ)} K
    (closedFiniteIndexNormCyclotomicField (K := K) H)

open scoped Classical in
noncomputable instance closedFiniteIndexNormCyclotomicFieldNumberField
    (H : Subgroup (IdeleClassGroup K)) [H.FiniteIndex] :
    NumberField
      (closedFiniteIndexNormCyclotomicField (K := K) H) :=
  NumberField.of_module_finite K
    (closedFiniteIndexNormCyclotomicField (K := K) H)

open scoped Classical in
noncomputable instance closedFiniteIndexNormCyclotomicFieldIsGalois
    (H : Subgroup (IdeleClassGroup K)) [H.FiniteIndex] :
    IsGalois K
      (closedFiniteIndexNormCyclotomicField (K := K) H) :=
  IsCyclotomicExtension.isGalois
    {(closedFiniteIndexNormExponent (K := K) H : ℕ)} K
    (closedFiniteIndexNormCyclotomicField (K := K) H)

open scoped Classical in
/-- The full S-unit Kummer layer used by the finite-index norm
construction. -/
noncomputable abbrev closedFiniteIndexNormKummerField
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] : Type :=
  cyclotomicFullSUnitKummerExtension
    (K := K) (closedFiniteIndexNormExponent (K := K) H)
    (closedFiniteIndexNormSeed (K := K) H hclosed)

open scoped Classical in
noncomputable instance closedFiniteIndexNormKummerFieldFiniteDimensional
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    FiniteDimensional
      (closedFiniteIndexNormCyclotomicField (K := K) H)
      (closedFiniteIndexNormKummerField (K := K) H hclosed) := by
  unfold closedFiniteIndexNormCyclotomicField
    closedFiniteIndexNormKummerField
  exact
    cyclotomicFullSUnitKummerExtension_finiteDimensional
      (K := K) (closedFiniteIndexNormExponent (K := K) H)
      (closedFiniteIndexNormSeed (K := K) H hclosed)

open scoped Classical in
noncomputable instance closedFiniteIndexNormKummerFieldIsGalois
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    IsGalois (closedFiniteIndexNormCyclotomicField (K := K) H)
      (closedFiniteIndexNormKummerField (K := K) H hclosed) := by
  unfold closedFiniteIndexNormCyclotomicField
    closedFiniteIndexNormKummerField
  exact
    cyclotomicFullSUnitKummerExtension_isGalois
      (K := K) (closedFiniteIndexNormExponent (K := K) H)
      (closedFiniteIndexNormSeed (K := K) H hclosed)

open scoped Classical in
noncomputable instance closedFiniteIndexNormKummerFieldNumberField
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    NumberField (closedFiniteIndexNormKummerField (K := K) H hclosed) :=
  NumberField.of_module_finite
    (closedFiniteIndexNormCyclotomicField (K := K) H)
    (closedFiniteIndexNormKummerField (K := K) H hclosed)

open scoped Classical in
@[reducible]
noncomputable instance closedFiniteIndexNormKummerFieldAlgebraOverBase
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Algebra K (closedFiniteIndexNormKummerField (K := K) H hclosed) :=
  ((algebraMap
      (closedFiniteIndexNormCyclotomicField (K := K) H)
      (closedFiniteIndexNormKummerField (K := K) H hclosed)).comp
    (algebraMap K
      (closedFiniteIndexNormCyclotomicField (K := K) H))).toAlgebra

open scoped Classical in
@[reducible]
noncomputable instance closedFiniteIndexNormKummerFieldSMulOverBase
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    SMul K (closedFiniteIndexNormKummerField (K := K) H hclosed) :=
  Algebra.toSMul
    (self := closedFiniteIndexNormKummerFieldAlgebraOverBase H hclosed)

open scoped Classical in
@[reducible]
noncomputable instance closedFiniteIndexNormKummerFieldModuleOverBase
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Module K (closedFiniteIndexNormKummerField (K := K) H hclosed) :=
  Algebra.toModule

open scoped Classical in
noncomputable instance closedFiniteIndexNormKummerFieldScalarTower
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    IsScalarTower K
      (closedFiniteIndexNormCyclotomicField (K := K) H)
      (closedFiniteIndexNormKummerField (K := K) H hclosed) := by
  exact IsScalarTower.of_algebraMap_eq' rfl

open scoped Classical in
noncomputable instance
    closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    FiniteDimensional K
      (closedFiniteIndexNormKummerField (K := K) H hclosed) :=
  FiniteDimensional.trans K
    (closedFiniteIndexNormCyclotomicField (K := K) H)
    (closedFiniteIndexNormKummerField (K := K) H hclosed)

open scoped Classical in
/-- The finite normal closure which is the actual Galois norm
neighbourhood attached to `H`. -/
noncomputable abbrev closedFiniteIndexNormAmbient
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] : Type :=
  finiteNormalClosure K
    (closedFiniteIndexNormKummerField (K := K) H hclosed)

open scoped Classical in
noncomputable instance closedFiniteIndexNormAmbientFiniteDimensional
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    FiniteDimensional K
      (closedFiniteIndexNormAmbient (K := K) H hclosed) := by
  unfold closedFiniteIndexNormAmbient
  infer_instance

open scoped Classical in
noncomputable instance closedFiniteIndexNormAmbientNumberField
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    NumberField (closedFiniteIndexNormAmbient (K := K) H hclosed) := by
  unfold closedFiniteIndexNormAmbient
  exact
    finiteNormalClosure_numberField K
      (closedFiniteIndexNormKummerField (K := K) H hclosed)

open scoped Classical in
noncomputable instance closedFiniteIndexNormAmbientIsGalois
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    IsGalois K (closedFiniteIndexNormAmbient (K := K) H hclosed) := by
  unfold closedFiniteIndexNormAmbient
  exact
    finiteNormalClosure_isGalois K
      (closedFiniteIndexNormKummerField (K := K) H hclosed)

open scoped Classical in
/-- The finite normal closure of the cyclotomic full S-unit Kummer
extension attached to a closed finite-index subgroup is an actual finite
Galois norm neighbourhood contained in that subgroup. -/
theorem closedFiniteIndexSubgroup_has_finiteGaloisNormNeighborhood
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    (_root_.ideleClassNorm K
      (closedFiniteIndexNormAmbient (K := K) H hclosed)).range ≤ H := by
  classical
  let n := closedFiniteIndexNormExponent (K := K) H
  let seed := closedFiniteIndexNormSeed (K := K) H hclosed
  have hNormPower :
      (_root_.ideleClassNorm K
        (closedFiniteIndexNormAmbient (K := K) H hclosed)).range ≤
        ideleClassPowerLocalUnitSubgroup
          (K := K) n
          (cyclotomicKummerNormSupport (K := K) n seed) ∅ := by
    simpa only [n, seed, closedFiniteIndexNormAmbient,
      closedFiniteIndexNormKummerField,
      closedFiniteIndexNormCyclotomicField] using
      (cyclotomicFullSUnitKummerFiniteNormalClosure_ideleClassNormRange_le_powerLocalUnit
        (K := K) n
        (one_lt_closedFiniteIndexNormExponent (K := K) H) seed)
  have hPower :
      ideleClassPowerLocalUnitSubgroup
          (K := K) n
          (cyclotomicKummerNormSupport (K := K) n seed) ∅ ≤
        H := by
    by_cases hH : H = ⊤
    · simpa only [hH] using
        (le_top :
          ideleClassPowerLocalUnitSubgroup
              (K := K) n
              (cyclotomicKummerNormSupport (K := K) n seed) ∅ ≤
            (⊤ : Subgroup (IdeleClassGroup K)))
    · have hSeed :
          (RayClass.modulusInsideClosedFiniteIndex H hclosed).finitePart.support ⊆
            cyclotomicKummerNormSupport (K := K) n seed := by
        simpa only [seed, closedFiniteIndexNormSeed] using
          (subset_cyclotomicKummerNormSupport
            (K := K) n seed)
      have hIndexPower :=
        ideleClassPowerLocalUnitSubgroup_le_closedFiniteIndexSubgroup
          (K := K) H hclosed
          (cyclotomicKummerNormSupport (K := K) n seed) hSeed
      simpa only [n,
        closedFiniteIndexNormExponent_eq_index (K := K) H hH
      ] using hIndexPower
  exact hNormPower.trans hPower

end GlobalClassFields
end GlobalClassFieldTheory
