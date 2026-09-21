/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.CyclicPrimeSubextension
/-!
# Finite-place splitting through prime ideals

For a finite Galois extension of number fields, an exact extension of a
normalized finite absolute value and its centre prime ideal have the same
decomposition group.  This file makes that comparison independent of the
chosen extension and records the finiteness of the fibres of contraction.
These are the place-theoretic ingredients used in the cyclic prime-power and
normal-closure splitting reductions.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The decomposition group of an exact finite-place extension is the
stabilizer of its centre prime. -/
theorem absoluteValueDecompositionGroup_eq_finitePlaceStabilizer
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    letI := finitePlaceMulAction K L
    absoluteValueDecompositionGroup K w.1 =
      MulAction.stabilizer (L ≃ₐ[K] L)
        (finitePlaceExtensionCentre (K := K) (L := L) v w) := by
  let := finitePlaceMulAction K L
  ext σ
  rw [mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
      (HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v) w σ]
  simp only [MulAction.mem_stabilizer_iff]
  change
    absoluteValueExtensionConjugate
        (HeightOneSpectrum.adicAbv K v) w σ = w ↔
      finitePlaceEquiv K L σ
          (finitePlaceExtensionCentre (K := K) (L := L) v w) =
        finitePlaceExtensionCentre (K := K) (L := L) v w
  constructor
  · intro h
    have hc := congrArg
      (finitePlaceExtensionCentre (K := K) (L := L) v) h
    rw [finitePlaceExtensionCentre_conjugate] at hc
    calc
      finitePlaceEquiv K L σ
          (finitePlaceExtensionCentre (K := K) (L := L) v w) =
          finitePlaceEquiv K L σ
            (finitePlaceEquiv K L σ⁻¹
              (finitePlaceExtensionCentre (K := K) (L := L) v w)) :=
        congrArg (finitePlaceEquiv K L σ) hc.symm
      _ = finitePlaceExtensionCentre (K := K) (L := L) v w := by
        rw [← finitePlaceEquiv_mul]
        simp
  · intro h
    apply finitePlaceExtensionCentre_injective
      (K := K) (L := L) v
    rw [finitePlaceExtensionCentre_conjugate]
    calc
      finitePlaceEquiv K L σ⁻¹
          (finitePlaceExtensionCentre (K := K) (L := L) v w) =
          finitePlaceEquiv K L σ⁻¹
            (finitePlaceEquiv K L σ
              (finitePlaceExtensionCentre (K := K) (L := L) v w)) :=
        congrArg (finitePlaceEquiv K L σ⁻¹) h.symm
      _ = finitePlaceExtensionCentre (K := K) (L := L) v w := by
        rw [← finitePlaceEquiv_mul]
        simp

omit [FiniteDimensional K L] in
/-- Complete splitting can be tested at the centre of any exact extension
of the normalized absolute value. -/
theorem finitePlaceSplitsCompletely_iff_centre_stabilizer_eq_bot
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    FinitePlaceSplitsCompletely (K := K) (L := L) v ↔
      letI := finitePlaceMulAction K L
      MulAction.stabilizer (L ≃ₐ[K] L)
        (finitePlaceExtensionCentre (K := K) (L := L) v w) = ⊥ := by
  let := finitePlaceMulAction K L
  unfold FinitePlaceSplitsCompletely finitePlaceDecompositionGroup
  constructor
  · intro h
    have hw :
        absoluteValueDecompositionGroup K w.1 = ⊥ :=
      absoluteValueDecompositionGroup_eq_bot_independent_extension
        (HeightOneSpectrum.adicAbv K v)
        (RayClass.adicAbv_isNontrivial v)
        (chosenFinitePlaceExtension (L := L) v) w h
    rwa [absoluteValueDecompositionGroup_eq_finitePlaceStabilizer
      (K := K) (L := L) v w] at hw
  · intro h
    have hw :
        absoluteValueDecompositionGroup K w.1 = ⊥ := by
      rwa [absoluteValueDecompositionGroup_eq_finitePlaceStabilizer
        (K := K) (L := L) v w]
    exact
      absoluteValueDecompositionGroup_eq_bot_independent_extension
        (HeightOneSpectrum.adicAbv K v)
        (RayClass.adicAbv_isNontrivial v)
        w (chosenFinitePlaceExtension (L := L) v) hw

/-- Complete splitting can equivalently be tested at any finite place
above the base place. -/
theorem finitePlaceSplitsCompletely_iff_stabilizer_eq_bot
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 L))
    (hW : finitePlaceBelow (K := K) W = v) :
    FinitePlaceSplitsCompletely (K := K) (L := L) v ↔
      letI := finitePlaceMulAction K L
      MulAction.stabilizer (L ≃ₐ[K] L) W = ⊥ := by
  let := finitePlaceMulAction K L
  let Wv :
      {W : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := K) W = v} :=
    ⟨W, hW⟩
  let w :=
    (finitePlaceExtensionEquivAbove (K := K) (L := L) v).symm Wv
  have hw :
      finitePlaceExtensionCentre (K := K) (L := L) v w = W := by
    have happ :=
      (finitePlaceExtensionEquivAbove (K := K) (L := L) v).apply_symm_apply Wv
    exact congrArg Subtype.val happ
  rw [finitePlaceSplitsCompletely_iff_centre_stabilizer_eq_bot
    (K := K) (L := L) v w, hw]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- There are finitely many finite places of `L` above a fixed finite
place of `K`. -/
theorem finite_finitePlaceBelow_fibre
    (v : HeightOneSpectrum (𝓞 K)) :
    Set.Finite
      {W : HeightOneSpectrum (𝓞 L) |
        finitePlaceBelow (K := K) W = v} := by
  apply Set.Finite.of_finite_image
  · apply
      (Algebra.QuasiFinite.finite_primesOver
        (R := 𝓞 K) (S := 𝓞 L) v.asIdeal).subset
    rintro I ⟨W, hW, rfl⟩
    exact
      ⟨W.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hW).symm⟩⟩
  · intro W₁ _ W₂ _ h
    apply HeightOneSpectrum.ext
    exact h

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The inverse image of a finite set of base finite places under
contraction is finite. -/
theorem Set.Finite.preimage_finitePlaceBelow
    {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) :
    {W : HeightOneSpectrum (𝓞 L) |
      finitePlaceBelow (K := K) W ∈ S}.Finite := by
  show
    ((finitePlaceBelow (K := K)) ⁻¹' S).Finite
  exact hS.preimage'
    (fun v _ => finite_finitePlaceBelow_fibre
      (K := K) (L := L) v)

section IntermediateField

variable {M : Type}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]
    [IsGalois M L]

omit [NumberField K] [NumberField M] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [IsGalois M L] in
/-- Restricting the scalars of a Galois automorphism does not change
its action on the finite primes of the top field. -/
theorem finitePlaceEquiv_restrictAutomorphismScalars
    (σ : L ≃ₐ[M] L)
    (W : HeightOneSpectrum (𝓞 L)) :
    finitePlaceEquiv K L
        (RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
          (K := K) (M := M) σ) W =
      finitePlaceEquiv M L σ W := by
  apply HeightOneSpectrum.ext
  ext x
  rfl

/-- If a finite place splits completely in `L / K`, then every finite
place of an intermediate field above it splits completely in `L / M`.
The relation "above" is expressed canonically by ideal contraction,
so no comparison of differently normalized absolute values is needed. -/
theorem finitePlaceSplitsCompletely_over_intermediate_of_below
    (v' : HeightOneSpectrum (𝓞 M))
    (hsplit :
      FinitePlaceSplitsCompletely
        (K := K) (L := L)
        (finitePlaceBelow (K := K) v')) :
    FinitePlaceSplitsCompletely
      (K := M) (L := L) v' := by
  let w :=
    chosenFinitePlaceExtension (L := L) v'
  let W :=
    finitePlaceExtensionCentre
      (K := M) (L := L) v' w
  have hWM :
      finitePlaceBelow (K := M) W = v' :=
    finitePlaceBelow_finitePlaceExtensionCentre
      (K := M) (L := L) v' w
  have hWK :
      finitePlaceBelow (K := K) W =
        finitePlaceBelow (K := K) v' := by
    rw [← finitePlaceBelow_finitePlaceBelow
      (K := K) (M := M) (L := L) W, hWM]
  let := finitePlaceMulAction K L
  have hKbot :
      MulAction.stabilizer (L ≃ₐ[K] L) W = ⊥ :=
    (finitePlaceSplitsCompletely_iff_stabilizer_eq_bot
      (K := K) (L := L)
      (finitePlaceBelow (K := K) v') W hWK).mp hsplit
  let := finitePlaceMulAction M L
  apply
    (finitePlaceSplitsCompletely_iff_stabilizer_eq_bot
      (K := M) (L := L) v' W hWM).mpr
  apply le_bot_iff.mp
  intro σ hσ
  rw [Subgroup.mem_bot]
  let ρ : L ≃ₐ[K] L :=
    RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
      (K := K) (M := M) σ
  have hρ :
      ρ ∈ MulAction.stabilizer (L ≃ₐ[K] L) W := by
    simp only [MulAction.mem_stabilizer_iff] at hσ ⊢
    change finitePlaceEquiv M L σ W = W at hσ
    change finitePlaceEquiv K L ρ W = W
    unfold ρ
    rw [finitePlaceEquiv_restrictAutomorphismScalars
      (K := K) (M := M) (L := L)]
    exact hσ
  have hρOne : ρ = 1 :=
    Subgroup.mem_bot.mp (hKbot ▸ hρ)
  ext x
  have hx := DFunLike.congr_fun hρOne x
  change σ x = x
  change σ x = x at hx
  exact hx

/-- Finiteness of the nonsplitting finite places ascends from `K` to
an intermediate field `M`. -/
theorem finite_nonsplittingPlaces_over_intermediate
    (hfinite :
      {v : HeightOneSpectrum (𝓞 K) |
        ¬ FinitePlaceSplitsCompletely
          (K := K) (L := L) v}.Finite) :
    {v' : HeightOneSpectrum (𝓞 M) |
      ¬ FinitePlaceSplitsCompletely
        (K := M) (L := L) v'}.Finite := by
  apply
    (Set.Finite.preimage_finitePlaceBelow
      (K := K) (L := M) hfinite).subset
  intro v' hv'
  change
    ¬ FinitePlaceSplitsCompletely
      (K := K) (L := L)
      (finitePlaceBelow (K := K) v')
  intro hsplit
  exact hv'
    (finitePlaceSplitsCompletely_over_intermediate_of_below
      (K := K) (M := M) (L := L) v' hsplit)

end IntermediateField
