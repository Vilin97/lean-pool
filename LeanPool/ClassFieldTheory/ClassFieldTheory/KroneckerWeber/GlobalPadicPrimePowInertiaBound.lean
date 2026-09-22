/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.InertiaRestrictionCard
import LeanPool.ClassFieldTheory.ClassFieldTheory.RamificationTheory.HilbertRamification.PadicCyclotomicInertiaBound
import LeanPool.ClassFieldTheory.ClassFieldTheory.RamificationTheory.HilbertRamification.PadicLocalizationCanonicalValuation
import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.LocalCyclotomicEmbedding
/-!
# The one-prime p-primary inertia bound

This endpoint combines the localization–inertia comparison, the structured
local cyclotomic embedding, and the ramification comparison to replace the full cyclotomic
  totient by
the exact `p`-primary factor `φ(p ^ n)`.
-/

noncomputable section

namespace KroneckerWeber

open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable (p : ℕ) [Fact p.Prime]
variable (L : Type) [Field L] [Algebra ℚ L]
  [FiniteDimensional ℚ L] [IsAbelianGalois ℚ L]

/-- If the localization at `w` actually embeds into the cyclotomic field of
order `r * p ^ n`, with `r` prime to `p`, then its global inertia group has
order at most `φ(p ^ n)`.  This is the fixed-conductor local input used in
the global Kronecker–Weber argument. -/
theorem globalPadicInertia_natCard_le_coprimeCyclotomicPrimePowTotient
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) L)
    (r n : ℕ) (hpr : p.Coprime r)
    (i : globalPadicLocalizationCyclotomicAlgHom
      p L w (r * p ^ n)) :
    let vK := Rat.AbsoluteValue.padic p
    let hw := HilbertRamification.absoluteValueExtension_nonarchimedean_of_base
      vK w (rationalPadicAbsoluteValue_nonarchimedean p)
    Nat.card
        (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ
          (HilbertRamification.absoluteValueExtensionValuationSubring
            vK w hw)) ≤
      Nat.totient (p ^ n) := by
  let vK := Rat.AbsoluteValue.padic p
  let hvK := padicAbsoluteValue_isNontrivial p
  let hv := rationalPadicAbsoluteValue_nonarchimedean p
  let hw := HilbertRamification.absoluteValueExtension_nonarchimedean_of_base
    vK w hv
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) w.1
  let : SMul ℚ w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let hE : Field E := inferInstance
  let hBaseE : Algebra vK.Completion E := inferInstance
  let e := padicAbsoluteValueCompletionRingEquiv p
  let hQpE : Algebra ℚ_[p] E :=
    @transportedAlgebraAlongRingEquiv vK.Completion ℚ_[p] E _ _
      (@CommRing.toCommSemiring E hE.toCommRing) hBaseE e
  let : Module.Finite vK.Completion E :=
    globalPadicLocalizationModuleFinite p L w
  let : IsAbelianGalois vK.Completion E :=
    globalPadicLocalization_isAbelianGalois p L w
  let : Algebra ℚ_[p] vK.Completion := e.symm.toRingHom.toAlgebra
  let : IsScalarTower ℚ_[p] vK.Completion E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      exact transportedAlgebraAlongRingEquiv_algebraMap e x)
  let : Module.Finite ℚ_[p] vK.Completion :=
    FiniteDimensional.of_surjective
      (Algebra.linearMap ℚ_[p] vK.Completion) e.symm.surjective
  let : Module.Finite ℚ_[p] E := Module.Finite.trans vK.Completion E
  let : IsGalois ℚ_[p] E := by
    apply IsGalois.of_equiv_equiv
      (F := vK.Completion) (E := E) (M := ℚ_[p]) (N := E)
      (f := e) (g := RingEquiv.refl E)
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply]
    change
      (@algebraMap ℚ_[p] E _ hE.toSemiring hQpE) (e x) =
        (@algebraMap vK.Completion E _ hE.toSemiring hBaseE) x
    change
      (@algebraMap vK.Completion E _ hE.toSemiring hBaseE)
          (e.symm (e x)) =
        (@algebraMap vK.Completion E _ hE.toSemiring hBaseE) x
    rw [e.symm_apply_apply]
  change E →ₐ[ℚ_[p]] CyclotomicField (r * p ^ n) ℚ_[p] at i
  let A := HilbertRamification.algebraicLocalizationValuationSubring
    vK w hw
  have hA := globalPadicLocalizationValuationSubring_eq_canonical p L w
  change A =
    absoluteValueValuationSubring
      (padicFiniteExtensionAbsoluteValue p E)
      (padicFiniteExtensionAbsoluteValue_nonarchimedean p E) at hA
  have hRestrict :
      Nat.card
          (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup vK.Completion A) ≤
        Nat.card
          (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ_[p] A) :=
    HilbertRamification.ValuationSubring.natCard_inertiaGroup_le_restrictScalars
      (K := ℚ_[p]) (M := vK.Completion) A
  have hCanonical :
      Nat.card
          (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ_[p]
            (absoluteValueValuationSubring
              (padicFiniteExtensionAbsoluteValue p E)
              (padicFiniteExtensionAbsoluteValue_nonarchimedean p E))) ≤
        Nat.totient (p ^ n) :=
    natCard_padicCanonicalInertia_le_totient_primePow_of_coprimeEmbedding
      p r n hpr E i
  calc
    Nat.card
        (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ
          (HilbertRamification.absoluteValueExtensionValuationSubring
            vK w hw)) =
        Nat.card
          (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup vK.Completion A) :=
      Nat.card_congr
        (HilbertRamification.inertiaGroupEquivAlgebraicLocalization
          vK hvK w hw).toEquiv
    _ ≤ Nat.card
          (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ_[p] A) :=
      hRestrict
    _ = Nat.card
          (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ_[p]
            (absoluteValueValuationSubring
              (padicFiniteExtensionAbsoluteValue p E)
              (padicFiniteExtensionAbsoluteValue_nonarchimedean p E))) := by
      rw [hA]
    _ ≤ Nat.totient (p ^ n) := hCanonical

end KroneckerWeber

end
