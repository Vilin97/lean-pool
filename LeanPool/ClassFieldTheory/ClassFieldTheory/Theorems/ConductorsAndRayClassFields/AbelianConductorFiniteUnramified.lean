/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.EmbedsInRayClassFieldIffConductorLe
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.IsAbelianConductorUnique
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness
/-!
# Zero finite exponent and unramifiedness
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- A finite place has exponent zero in the public conductor exactly when
every place above it is unramified. -/
theorem IsAbelianConductor.finiteExponent_eq_zero_iff_unramified
    {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    {c : RayClassModulus K}
    (hc : IsAbelianConductor K L c)
    (v : HeightOneSpectrum (𝓞 K)) :
    c.finitePart v = 0 ↔
      ∀ W : HeightOneSpectrum (𝓞 L),
        W.asIdeal.LiesOver v.asIdeal →
          Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := by
  let H := GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
    (K := K) (L := L)
  have heq : c =
      ({ finitePart := H.fullConductor.finitePart
         infinitePart := H.fullConductor.infinitePart } : RayClassModulus K) :=
    hc.unique (normFullConductor_isAbelianConductor K L)
  have hsupport : c.finitePart.support =
      _root_.ramifiedBaseFinitePlaces (K := K) (L := L) := by
    rw [heq]
    change H.narrowFiniteConductor.support = _
    exact
      GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_narrowFiniteConductor_support_eq_ramifiedBaseFinitePlaces
        (K := K) (L := L)
  calc
    c.finitePart v = 0 ↔ v ∉ c.finitePart.support :=
      (Finsupp.notMem_support_iff).symm
    _ ↔ v ∉ _root_.ramifiedBaseFinitePlaces (K := K) (L := L) := by
      rw [hsupport]
    _ ↔
        ∀ W : HeightOneSpectrum (𝓞 L),
          W.asIdeal.LiesOver v.asIdeal →
            Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := by
      rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
      constructor
      · intro h W hW
        by_contra hram
        exact h ⟨W, hW, hram⟩
      · intro h hram
        obtain ⟨W, hW, hnot⟩ := hram
        exact hnot (h W hW)

end ClassFieldTheory
