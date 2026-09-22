/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces
import LeanPool.ClassFieldTheory.GaloisCohomology.GroupTheory.Finite
/-!
# Decomposition groups and complete splitting at finite places

For a finite Galois extension of number fields `L / K`, this file
attaches an actual decomposition subgroup to every finite place of
`K`.  The extension of the adic absolute value is the one constructed
in `LocalNormApproximation`; no place above `v` is supplied as an
additional hypothesis.

The stabilizer is identified with the automorphism group of the algebraic
localization. The finite-localization theorem supplies finite dimensionality,
so the order of
the decomposition group is exactly the local degree.  Consequently
complete splitting is equivalent both to cardinality one and to local
degree one.
-/

open scoped NumberField open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

open scoped Classical in
/-- The actual decomposition subgroup at the chosen extension of the
finite place `v`. -/
noncomputable def finitePlaceDecompositionGroup
    (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (L ≃ₐ[K] L) :=
  absoluteValueDecompositionGroup K
    (chosenFinitePlaceExtension (L := L) v).1

open scoped Classical in
/-- A finite place splits completely when its chosen decomposition
subgroup is trivial.  Conjugacy of extensions makes this independent
of the chosen extension, but the chosen representative gives a
concrete subgroup for subsequent constructions. -/
def FinitePlaceSplitsCompletely
    (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  finitePlaceDecompositionGroup
    (K := K) (L := L) v = ⊥

omit [FiniteDimensional K L] in
open scoped Classical in
/-- Membership in the finite-place decomposition group is exactly
stabilization of the chosen extension of the absolute value. -/
@[simp]
theorem mem_finitePlaceDecompositionGroup_iff
    (v : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L) :
    σ ∈ finitePlaceDecompositionGroup
        (K := K) (L := L) v ↔
      absoluteValueExtensionConjugate
          (NumberField.HeightOneSpectrum.adicAbv K v)
          (chosenFinitePlaceExtension (L := L) v) σ =
        chosenFinitePlaceExtension (L := L) v := by
  exact
    mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v)
      (chosenFinitePlaceExtension (L := L) v) σ

open scoped Classical in
/-- The local degree at `v`, defined using the actual algebraic
localization selected above. -/
noncomputable def finitePlaceLocalDegree
    (v : HeightOneSpectrum (𝓞 K)) : ℕ := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w :=
    chosenFinitePlaceExtension (L := L) v
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  exact
    Module.finrank vK.Completion
      (LocalizedCompletion vK w)

open scoped Classical in
/-- The decomposition-group localization equivalence together with the finite-localization theorem
the finite-localization theorem: the order of the decomposition group equals the local
degree. -/
theorem finitePlaceDecompositionGroup_card_eq_localDegree
    (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card
        (finitePlaceDecompositionGroup
          (K := K) (L := L) v) =
      finitePlaceLocalDegree
        (K := K) (L := L) v := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let w :=
    chosenFinitePlaceExtension (L := L) v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let :=
    localizedCompletionGlobalAlgebra vK w
  let :=
    localizedCompletionIsScalarTower vK w
  let E :=
    LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    localizedCompletionModuleFinite vK hvK w
  let : IsGalois vK.Completion E :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  calc
    Nat.card
        (finitePlaceDecompositionGroup
          (K := K) (L := L) v) =
        Nat.card
          (E ≃ₐ[vK.Completion] E) :=
      Nat.card_congr
        (decompositionGroupEquivAlgebraicLocalizationAut
          vK hvK w).toEquiv
    _ = Module.finrank vK.Completion E :=
      IsGalois.card_aut_eq_finrank
        vK.Completion E
    _ = finitePlaceLocalDegree
        (K := K) (L := L) v := rfl

omit [FiniteDimensional K L] in
open scoped Classical in
/-- A finite place splits completely exactly when its decomposition
group has one element. -/
theorem finitePlaceSplitsCompletely_iff_card_eq_one
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceSplitsCompletely
        (K := K) (L := L) v ↔
      Nat.card
          (finitePlaceDecompositionGroup
            (K := K) (L := L) v) = 1 := by
  unfold FinitePlaceSplitsCompletely
  exact
    (finitePlaceDecompositionGroup
      (K := K) (L := L) v).eq_bot_iff_card

open scoped Classical in
/-- Complete splitting is equivalent to local degree one. -/
theorem finitePlaceSplitsCompletely_iff_localDegree_eq_one
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceSplitsCompletely
        (K := K) (L := L) v ↔
      finitePlaceLocalDegree
          (K := K) (L := L) v = 1 := by
  rw [finitePlaceSplitsCompletely_iff_card_eq_one,
    finitePlaceDecompositionGroup_card_eq_localDegree]

omit [FiniteDimensional K L] in
open scoped Classical in
/-- A finite place fails to split completely exactly when its
decomposition group contains a nonidentity automorphism. -/
theorem finitePlace_not_splitsCompletely_iff_exists_nontrivial_stabilizer
    (v : HeightOneSpectrum (𝓞 K)) :
    ¬ FinitePlaceSplitsCompletely
        (K := K) (L := L) v ↔
      ∃ σ : L ≃ₐ[K] L,
        absoluteValueExtensionConjugate
            (NumberField.HeightOneSpectrum.adicAbv K v)
            (chosenFinitePlaceExtension (L := L) v) σ =
          chosenFinitePlaceExtension (L := L) v ∧
        σ ≠ 1 := by
  constructor
  · intro hsplit
    have hne :
        finitePlaceDecompositionGroup
            (K := K) (L := L) v ≠ ⊥ :=
      hsplit
    obtain ⟨σ, hσ⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp hne
    refine
      ⟨σ.1,
        (mem_finitePlaceDecompositionGroup_iff
          (K := K) (L := L) v σ.1).mp σ.2,
        ?_⟩
    intro hσOne
    apply hσ
    apply Subtype.ext
    exact hσOne
  · rintro ⟨σ, hσ, hσOne⟩ hsplit
    have hmem :
        σ ∈ finitePlaceDecompositionGroup
          (K := K) (L := L) v :=
      (mem_finitePlaceDecompositionGroup_iff
        (K := K) (L := L) v σ).mpr hσ
    have hbot : σ ∈
        (⊥ : Subgroup (L ≃ₐ[K] L)) := by
      rw [← hsplit]
      exact hmem
    exact hσOne (Subgroup.mem_bot.mp hbot)

open scoped Classical in
/-- Nonsplitting is equivalently strict positivity above one of the
decomposition-group order. -/
theorem finitePlace_not_splitsCompletely_iff_one_lt_card
    (v : HeightOneSpectrum (𝓞 K)) :
    ¬ FinitePlaceSplitsCompletely
        (K := K) (L := L) v ↔
      1 < Nat.card
          (finitePlaceDecompositionGroup
            (K := K) (L := L) v) := by
  unfold FinitePlaceSplitsCompletely
  exact
    (finitePlaceDecompositionGroup
      (K := K) (L := L) v).one_lt_card_iff_ne_bot.symm

open scoped Classical in
/-- Nonsplitting is equivalently local degree greater than one. -/
theorem finitePlace_not_splitsCompletely_iff_one_lt_localDegree
    (v : HeightOneSpectrum (𝓞 K)) :
    ¬ FinitePlaceSplitsCompletely
        (K := K) (L := L) v ↔
      1 < finitePlaceLocalDegree
          (K := K) (L := L) v := by
  rw [finitePlace_not_splitsCompletely_iff_one_lt_card,
    finitePlaceDecompositionGroup_card_eq_localDegree]

open scoped Classical in
/-- In a nontrivial finite Galois extension, a place whose
decomposition group is the whole Galois group cannot split
completely. This bridges the cyclic prime-power criterion, where
"nonsplit" means full decomposition group, and the normal-closure criterion. -/
theorem finitePlace_not_splitsCompletely_of_decompositionGroup_eq_top
    (hdegree : 1 < Module.finrank K L)
    (v : HeightOneSpectrum (𝓞 K))
    (hfull :
      finitePlaceDecompositionGroup
          (K := K) (L := L) v = ⊤) :
    ¬ FinitePlaceSplitsCompletely
        (K := K) (L := L) v := by
  intro hsplit
  have htopbot :
      (⊤ : Subgroup (L ≃ₐ[K] L)) = ⊥ := by
    rw [← hfull]
    exact hsplit
  have hcard : Nat.card (L ≃ₐ[K] L) = 1 := by
    have h :=
      congrArg
        (fun H : Subgroup (L ≃ₐ[K] L) => Nat.card H)
        htopbot
    simpa using h
  rw [IsGalois.card_aut_eq_finrank] at hcard
  omega

section IntermediateField

variable {M : Type}
    [Field M] [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
open scoped Classical in
/-- Complete splitting of a valuation over `K` remains complete
after enlarging the base to an intermediate field `M`.

This is the subgroup-intersection criterion,
combined with injectivity of scalar restriction. -/
theorem absoluteValueDecompositionGroup_eq_bot_over_intermediate
    (w : AbsoluteValue L ℝ)
    (hsplit :
      absoluteValueDecompositionGroup K w = ⊥) :
    absoluteValueDecompositionGroup M w = ⊥ := by
  apply
    ((absoluteValueDecompositionGroup M w).map_eq_bot_iff_of_injective
      (decompositionGroupRestriction_restrictAutomorphismScalars_injective
        (K := K) (M := M) (L := L))).mp
  rw [decompositionGroupRestriction_absoluteValueDecompositionGroup_range_eq_inf
      (K := K) (M := M) w]
  simp [hsplit]

end IntermediateField

section Quotient

open scoped Classical in
/-- The image of the finite-place decomposition subgroup in a group
quotient.  In the Galois correspondence this is the decomposition
group in the corresponding intermediate extension. -/
noncomputable def finitePlaceDecompositionGroupInQuotient
    (v : HeightOneSpectrum (𝓞 K))
    (P : Subgroup (L ≃ₐ[K] L))
    [P.Normal] :
    Subgroup ((L ≃ₐ[K] L) ⧸ P) :=
  (finitePlaceDecompositionGroup
    (K := K) (L := L) v).map
      (QuotientGroup.mk' P)

omit [FiniteDimensional K L] in
open scoped Classical in
/-- The quotient decomposition group is trivial exactly when the
original decomposition group is contained in the quotient kernel. -/
theorem finitePlaceDecompositionGroupInQuotient_eq_bot_iff
    (v : HeightOneSpectrum (𝓞 K))
    (P : Subgroup (L ≃ₐ[K] L))
    [P.Normal] :
    finitePlaceDecompositionGroupInQuotient
        (K := K) (L := L) v P = ⊥ ↔
      finitePlaceDecompositionGroup
          (K := K) (L := L) v ≤ P := by
  rw [finitePlaceDecompositionGroupInQuotient,
    Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk']

open scoped Classical in
/-- In a cyclic extension of prime-power degree, every proper
finite-place decomposition group is contained in a normal subgroup
of index `p`; the resulting order-`p` quotient has trivial
decomposition image.  This is the group/prime bridge used in
the cyclic prime-power splitting argument. -/
theorem finitePlace_exists_index_prime_quotient_of_decompositionGroup_ne_top
    [IsCyclic (L ≃ₐ[K] L)]
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent)
    (v : HeightOneSpectrum (𝓞 K))
    (hproper :
      finitePlaceDecompositionGroup
          (K := K) (L := L) v ≠ ⊤) :
    ∃ P : Subgroup (L ≃ₐ[K] L),
      finitePlaceDecompositionGroup
          (K := K) (L := L) v ≤ P ∧
      P.index = p ∧
      P.Normal ∧
      Nat.card ((L ≃ₐ[K] L) ⧸ P) = p ∧
      finitePlaceDecompositionGroupInQuotient
          (K := K) (L := L) v P = ⊥ := by
  obtain
      ⟨P, hDP, hPindex, hPnormal, hPquotient⟩ :=
    cyclic_exists_normal_index_prime_supergroup
      hp hexponent hcard
      (finitePlaceDecompositionGroup
        (K := K) (L := L) v)
      hproper
  refine
    ⟨P, hDP, hPindex, hPnormal,
      hPquotient, ?_⟩
  exact
    (finitePlaceDecompositionGroupInQuotient_eq_bot_iff
      (K := K) (L := L) v P).mpr hDP

end Quotient
