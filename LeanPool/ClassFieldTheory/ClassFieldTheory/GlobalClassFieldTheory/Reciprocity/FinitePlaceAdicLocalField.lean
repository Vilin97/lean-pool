/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingFiniteFactor
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingProperties
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport
import Mathlib.NumberTheory.LocalField.Basic
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuedTopology
/-!
# Local-field structure on a finite adic completion

The distinguished integer-valued valuation on a number-field completion
provides the valuation relation required by local reciprocity.  The
valuation relation is passed explicitly, not registered globally.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

/-- The valuation relation induced by the canonical discrete valuation on
the completion at a finite place. -/
@[reducible]
def finitePlaceCompletionValuativeRel
    (F : Type u) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ValuativeRel (v.adicCompletion F) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))

/-- The canonical finite adic completion is a nonarchimedean local field for
its distinguished valuation. -/
theorem finitePlaceCompletionIsNonarchimedeanLocalField
    (F : Type u) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    @IsNonarchimedeanLocalField (v.adicCompletion F) inferInstance
      (finitePlaceCompletionValuativeRel F v) inferInstance := by
  let C := v.adicCompletion F
  let ν : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  let _ : ν.IsNontrivial := inferInstance
  let _ : ValuativeRel C := finitePlaceCompletionValuativeRel F v
  let _ : ν.Compatible := Valuation.Compatible.ofValuation ν
  let _ : ValuativeRel.IsNontrivial C :=
    (ValuativeRel.isNontrivial_iff_isNontrivial ν).2 inferInstance
  let _ : IsValuativeTopology C :=
    LocalFieldTheory.isValuativeTopology_of_valued_ofValuation
      C (WithZero (Multiplicative ℤ))
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

end ClassFieldTheory

section CompletionComparison

open LocalClassFieldTheory

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

local instance finitePlaceCompletionComparisonSourceValuativeRel :
    ValuativeRel (HeightOneSpectrum.adicAbv F v).Completion :=
  GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v

local instance finitePlaceCompletionComparisonTargetValuativeRel :
    ValuativeRel (v.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F v

/-- The canonical equivalence between the two finite-completion models
respects their chosen valuation relations. -/
theorem finitePlaceCompletion_semilinearValuationCompatible :
    SemilinearValuationCompatible
      (HeightOneSpectrum.adicAbv F v).Completion
      (v.adicCompletion F)
      (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv := by
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  let C' := v.adicCompletion F
  let e := (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let _ : Algebra C C' := e.toRingHom.toAlgebra
  change (ValuativeRel.valuation C).HasExtension (ValuativeRel.valuation C')
  constructor
  intro x y
  change ValuativeRel.valuation C x ≤ ValuativeRel.valuation C y ↔
    ValuativeRel.valuation C' (e x) ≤ ValuativeRel.valuation C' (e y)
  rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le]
  change ‖x‖₊ ≤ ‖y‖₊ ↔
    (Valued.v : Valuation C' (WithZero (Multiplicative ℤ))) (e x) ≤ Valued.v (e y)
  rw [← Valued.toNormedField.norm_le_iff]
  change ‖x‖ ≤ ‖y‖ ↔ ‖relativeFinitePlaceCompletionRingEquiv v x‖ ≤
    ‖relativeFinitePlaceCompletionRingEquiv v y‖
  rw [relativeFinitePlaceCompletionRingEquiv_norm,
    relativeFinitePlaceCompletionRingEquiv_norm]

end CompletionComparison

namespace ClassFieldTheory

/-- At each finite place, transport the local Hilbert pairing from the
absolute-value completion to Mathlib's adic completion. -/
def finitePlaceAdicHilbertPairingFamily
    (F : Type) [Field F] [NumberField F]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    GlobalHilbertPairingFamily F n := by
  intro v
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  letI : ValuativeRel C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : CharZero C :=
    charZero_of_injective_algebraMap (algebraMap F C).injective
  have hnC : ((n : ℕ) : C) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr n.ne_zero
  have hmuC : (primitiveRoots (n : ℕ) C).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmu
    exact ⟨algebraMap F C ζ,
      (mem_primitiveRoots n.pos).2
        (((mem_primitiveRoots n.pos).1 hζ).map_of_injective
          (algebraMap F C).injective)⟩
  exact hilbertPairingOfRingEquiv
    (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv n hmuC
    (localHilbertPairing C n hnC hmuC)

/-- Every finite member of the transported family satisfies the local
Steinberg, skew-symmetry, nondegeneracy, and Kummer norm-residue laws. -/
theorem finitePlaceAdicHilbertPairingFamily_isLocallyHilbert
    (F : Type) [Field F] [NumberField F]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    GlobalHilbertPairingFamily.IsLocallyHilbert F
      (finitePlaceAdicHilbertPairingFamily F n hmu) := by
  intro v
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  exact
    letI : ValuativeRel C :=
      GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    letI : CharZero C :=
      charZero_of_injective_algebraMap (algebraMap F C).injective
    have hnC : ((n : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
    have hmuC : (primitiveRoots (n : ℕ) C).Nonempty := by
      obtain ⟨ζ, hζ⟩ := hmu
      exact ⟨algebraMap F C ζ,
        (mem_primitiveRoots n.pos).2
          (((mem_primitiveRoots n.pos).1 hζ).map_of_injective
            (algebraMap F C).injective)⟩
    show HilbertPairing.IsLocalHilbertPairing (hilbertPairingOfRingEquiv
      (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv n hmuC
      (localHilbertPairing C n hnC hmuC)) from
      hilbertPairingOfRingEquiv_isLocalHilbertPairing
        (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv n hmuC
        (localHilbertPairing C n hnC hmuC)
        (localHilbertPairing_isLocalHilbertPairing C n hnC hmuC)

end ClassFieldTheory
