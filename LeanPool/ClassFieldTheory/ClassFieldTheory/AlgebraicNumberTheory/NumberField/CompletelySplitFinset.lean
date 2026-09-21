/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.CompletelySplitPrimes
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SUnit.GaloisAction
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Data.Finset.Card
/-!
# A finite set of primes witnessing complete splitting

The Galois orbit of the centre of one actual extended finite place is free
when the rational prime splits completely. Its prime ideals form a finite
set of cardinality equal to the number-field degree.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace AlgebraicNumberTheory.PrimeSelection

/-- A completely split rational prime gives exactly a field-degree-sized
finite set of distinct maximal ideals containing that rational prime. -/
theorem exists_finset_maximalIdeals_of_finitePlaceSplitsCompletely
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    (q : Nat.Primes)
    (hsplit : FinitePlaceSplitsCompletely (K := ℚ) (L := F)
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q)) :
    ∃ factors : Finset (Ideal (𝓞 F)),
      factors.card = Module.finrank ℚ F ∧
        ∀ P ∈ factors, P.IsMaximal ∧ (q.val : 𝓞 F) ∈ P := by
  classical
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q
  let w := chosenFinitePlaceExtension (L := F) v
  let W : HeightOneSpectrum (𝓞 F) :=
    finitePlaceExtensionCentre (K := ℚ) (L := F) v w
  let := finitePlaceMulAction ℚ F
  have hStab : MulAction.stabilizer (F ≃ₐ[ℚ] F) W = ⊥ :=
    (finitePlaceSplitsCompletely_iff_centre_stabilizer_eq_bot
      (K := ℚ) (L := F) v w).mp hsplit
  have hOrbit : Function.Injective (fun σ : F ≃ₐ[ℚ] F =>
      finitePlaceEquiv ℚ F σ W) := by
    intro σ τ h
    change finitePlaceEquiv ℚ F σ W = finitePlaceEquiv ℚ F τ W at h
    have hFix : σ⁻¹ * τ ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) W := by
      change finitePlaceEquiv ℚ F (σ⁻¹ * τ) W = W
      rw [finitePlaceEquiv_mul, h.symm, ← finitePlaceEquiv_mul]
      simp
    have hOne : σ⁻¹ * τ = 1 := by
      simpa only [hStab, Subgroup.mem_bot] using hFix
    exact inv_mul_eq_one.mp hOne
  have hIdealOrbit : Function.Injective (fun σ : F ≃ₐ[ℚ] F =>
      (finitePlaceEquiv ℚ F σ W).asIdeal) := by
    intro σ τ h
    exact hOrbit (HeightOneSpectrum.ext h)
  have hBelow : finitePlaceBelow (K := ℚ) W = v :=
    finitePlaceBelow_finitePlaceExtensionCentre v w
  have hBase : (q.val : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [rationalPrimePlace_asIdeal q]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hUnder : (q.val : 𝓞 ℚ) ∈
      (finitePlaceBelow (K := ℚ) W).asIdeal := by
    simpa only [hBelow] using hBase
  have hWq : (q.val : 𝓞 F) ∈ W.asIdeal := by
    change algebraMap (𝓞 ℚ) (𝓞 F) (q.val : 𝓞 ℚ) ∈ W.asIdeal at hUnder
    simpa only [map_natCast] using hUnder
  let : Fintype (F ≃ₐ[ℚ] F) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun σ : F ≃ₐ[ℚ] F =>
    (finitePlaceEquiv ℚ F σ W).asIdeal), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hIdealOrbit, Finset.card_univ,
      Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank ℚ F]
  · intro P hP
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hP
    refine ⟨(finitePlaceEquiv ℚ F σ W).isMaximal, ?_⟩
    rw [finitePlaceEquiv_asIdeal]
    simpa only [map_natCast] using
      Ideal.mem_map_of_mem
        (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv hWq

end AlgebraicNumberTheory.PrimeSelection
