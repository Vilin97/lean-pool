/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.IntegerRingComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.RamificationIndex
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelian
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
/-!
# Tame finite conductor exponents

For a finite abelian number-field extension, the conductor exponent at a
finite place is at most one exactly when the residue characteristic does not
divide the ideal-theoretic ramification index at any place above it.
-/

open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

open GlobalClassFieldTheory.GlobalClassFields renaming
  ideleClassNormChosenFinitePlaceLocalConductorExponent →
    ideleClassNormChosenFinitePlaceLocalConductorExponent in
/-- At any prime above `v`, the finite conductor exponent is at most one
exactly when the residue characteristic is prime to the ramification index.
The criterion is independent of the chosen prime above `v`. -/
theorem IsAbelianConductor.finiteExponent_le_one_iff_residueChar_not_dvd_ramificationIdx
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    {c : RayClassModulus K}
    (hc : IsAbelianConductor K L c)
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 L))
    (hW : W.asIdeal.LiesOver v.asIdeal) :
    c.finitePart v ≤ 1 ↔
      ¬ ringChar (𝓞 K ⧸ v.asIdeal) ∣
        W.asIdeal.ramificationIdx (𝓞 K) := by
  let p : ℕ := ringChar (𝓞 K ⧸ v.asIdeal)
  let : Finite (𝓞 K ⧸ v.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let : Fact p.Prime :=
    ⟨CharP.prime_ringChar (𝓞 K ⧸ v.asIdeal)⟩
  let : CharP (𝓞 K ⧸ v.asIdeal) p :=
    ringChar.charP (R := 𝓞 K ⧸ v.asIdeal)
  let C := _root_.ChosenFinitePlaceBaseCompletion (K := K) v
  let E := _root_.ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let : FiniteDimensional C E :=
    _root_.chosenFinitePlaceLocalizedFiniteDimensional
      (K := K) (L := L) v
  let : Algebra.IsSeparable C E :=
    (_root_.chosenFinitePlaceLocalizedIsGalois
      (K := K) (L := L) v).to_isSeparable
  let vK := HeightOneSpectrum.adicAbv K v
  let w := _root_.chosenFinitePlaceExtension (L := L) v
  let : IsAbelianGalois C E :=
    LocalClassFieldTheory.localizedCompletion_isAbelianGalois
      vK (RayClass.adicAbv_isNontrivial v) w
  let base := (LocalFieldTheory.localCompleteDVF C).toDVF
  let target :=
    (LocalFieldTheory.chosenLocalExtensionCompleteDVF C E).toDVF
  have hp_ne : p ≠ 0 :=
    (Fact.out : p.Prime).ne_zero
  let eBase := _root_.finitePlaceIdealResidueEquivCompletion v
  let : CharP base.residueField p := by
    change CharP (IsLocalRing.ResidueField 𝒪[C]) p
    exact CharP.of_ringHom_of_ne_zero eBase.toRingHom p hp_ne
  let : CharP target.residueField p :=
    CharP.of_ringHom_of_ne_zero
      (ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap
        base target) p hp_ne
  have hLocal :
      LocalClassFieldTheory.localConductorExponent C E ≤ 1 ↔
        ¬ p ∣
          ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
            base target := by
    exact
      LocalClassFieldTheory.localConductorExponent_le_one_iff_residueChar_not_dvd_ramificationIndex
        C E p
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
  have hCoeff :
      c.finitePart v =
        ideleClassNormChosenFinitePlaceLocalConductorExponent
          (K := K) (L := L) v := by
    rw [hcd]
    simpa only [d] using
      (abelianFullConductor_finiteExponent_eq_localConductorExponent
        (K := K) (L := L) v)
  have hChosen :
      ideleClassNormChosenFinitePlaceLocalConductorExponent
          (K := K) (L := L) v =
        LocalClassFieldTheory.localConductorExponent C E := by
    rfl
  let P := v.asIdeal
  let Q := W.asIdeal
  let Qc :=
    (_root_.finitePlaceExtensionCentre
      (K := K) (L := L) v w).asIdeal
  let : Q.LiesOver P := hW
  let : Qc.LiesOver P :=
    _root_.finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) v w
  let G := L ≃ₐ[K] L
  let : Finite G := IsGaloisGroup.finite G K L
  let : IsGaloisGroup G (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing G (𝓞 K) (𝓞 L) K L
  have hIdxLocal :
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base target = P.ramificationIdx' Qc := by
    exact _root_.chosenFinitePlace_chosenLocal_ramificationIndex_eq_centre
      (K := K) (L := L) v
  have hIdxOldNew : P.ramificationIdx' Qc =
      Qc.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx'_eq_ramificationIdx P Qc v.ne_bot
  have hIdxConjugate : Qc.ramificationIdx (𝓞 K) =
      Q.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_eq_of_isGaloisGroup P Qc Q G
  rw [hCoeff, hChosen, hLocal, hIdxLocal, hIdxOldNew,
    hIdxConjugate]

end ClassFieldTheory
