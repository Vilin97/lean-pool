/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.PublicHigherUnitComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Finite conductor exponents and local norms

The finite exponent of the conductor is characterized by the determinant
norm from `K_v ⊗[K] L`. This formulation does not choose a place of `L`
above `v`; the implementation proves that the tensor norm image agrees
with the norm group of a chosen local field extension.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

open GlobalClassFieldTheory.GlobalClassFields renaming
  ideleClassNormLocalHigherUnitExponent_eq_localConductorExponent →
    ideleClassNormLocalHigherUnitExponent_eq_localConductorExponent in
/-- The conductor exponent at `v` is at most `n` exactly when the `n`-th
higher-unit group lies in the finite-place tensor norm image. -/
theorem IsAbelianConductor.finiteExponent_le_iff_higherUnit_le_tensorNorm
    {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    {c : RayClassModulus K}
    (hc : IsAbelianConductor K L c)
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    c.finitePart v ≤ n ↔
      rayLocalHigherUnitGroup v n ≤
        (Units.map (Algebra.norm (v.adicCompletion K)) :
          (v.adicCompletion K ⊗[K] L)ˣ →*
            (v.adicCompletion K)ˣ).range := by
  let H :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
      (K := K) (L := L)
  let d : RayClassModulus K :=
    { finitePart := H.fullConductor.finitePart
      infinitePart := H.fullConductor.infinitePart }
  have hd : IsAbelianConductor K L d :=
    normFullConductor_isAbelianConductor K L
  have hcd : c = d := by
    apply le_antisymm
    · exact (hc d).mp ((hd d).mpr le_rfl)
    · exact (hd c).mp ((hc c).mpr le_rfl)
  have hsource :
      H.fullConductor.finitePart v =
        GlobalClassFieldTheory.GlobalClassFields.ideleClassNormLocalHigherUnitExponent
          (K := K) (L := L) v := by
    rw [abelianFullConductor_finiteExponent_eq_localConductorExponent
      (K := K) (L := L) v]
    exact
      (ideleClassNormLocalHigherUnitExponent_eq_localConductorExponent
        (K := K) (L := L) v).symm
  have hcoeff :
      c.finitePart v =
        GlobalClassFieldTheory.GlobalClassFields.ideleClassNormLocalHigherUnitExponent
          (K := K) (L := L) v := by
    rw [hcd]
    simpa only [d] using hsource
  have hnorm :
      (Units.map (Algebra.norm (v.adicCompletion K)) :
        (v.adicCompletion K ⊗[K] L)ˣ →*
          (v.adicCompletion K)ˣ).range =
        _root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v := by
    simpa only [_root_.localTensorNorm] using
      (finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
        (K := K) (L := L) v)
  rw [hcoeff, hnorm]
  rw [rayLocalHigherUnitGroup_eq_rayClass v n]
  constructor
  · intro hn
    exact
      (RayClass.localHigherUnitGroup_antitone v hn).trans
        (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormLocalHigherUnitExponent_spec
          (K := K) (L := L) v)
  · intro hn
    exact
      GlobalClassFieldTheory.GlobalClassFields.ideleClassNormLocalHigherUnitExponent_min
        (K := K) (L := L) v hn

end ClassFieldTheory
