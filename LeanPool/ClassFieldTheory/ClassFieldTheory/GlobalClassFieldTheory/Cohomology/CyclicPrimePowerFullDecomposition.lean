/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.CyclicPrimeSubextension
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
import LeanPool.ClassFieldTheory.GaloisCohomology.GroupTheory.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleClassHerbrandSupportedFinal
/-!
# Full decomposition places in cyclic prime-power extensions

This file proves the infinitude of full-decomposition places in cyclic
prime-power extensions.  For a cyclic group of prime-power order, every
proper subgroup is contained in the
chosen subgroup of index `p`.  Consequently every finite place whose
decomposition group is proper splits completely in the chosen
degree-`p` subextension.

The second part records the idelic approximation argument: if all
finite places outside a finite set split completely, then the idele
class norm is surjective.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open RelativeIdeleGroup.Cohomology

namespace GlobalClassFieldTheory
namespace Cohomology

open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]

omit [NumberField L] in
/-- A proper decomposition group in the original cyclic
prime-power extension becomes trivial in the chosen degree-`p`
subextension. -/
theorem
    cyclicPrimeSubextensionDecompositionGroup_eq_bot_of_ne_top
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard : Nat.card (L ≃ₐ[K] L) = p ^ exponent)
    (v : HeightOneSpectrum (𝓞 K))
    (hproper :
      finitePlaceDecompositionGroup
          (K := K) (L := L) v ≠ ⊤) :
    cyclicPrimeSubextensionDecompositionGroup
        (K := K) (L := L)
        hp hexponent hcard v = ⊥ := by
  let P :=
    cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard
  let : P.Normal :=
    cyclicPrimeIndexSubgroup_normal
      (K := K) (L := L)
      hp hexponent hcard
  have hDP :
      finitePlaceDecompositionGroup
          (K := K) (L := L) v ≤ P :=
    subgroup_le_index_prime_subgroup_of_ne_top_cyclic_prime_power
      hp hcard P
      (finitePlaceDecompositionGroup
        (K := K) (L := L) v)
      (cyclicPrimeIndexSubgroup_index
        (K := K) (L := L)
        hp hexponent hcard)
      hproper
  have hquot :
      finitePlaceDecompositionGroupInQuotient
          (K := K) (L := L) v P = ⊥ :=
    (finitePlaceDecompositionGroupInQuotient_eq_bot_iff
      (K := K) (L := L) v P).2 hDP
  rw [
    cyclicPrimeSubextensionDecompositionGroup_eq_quotient_image
      (K := K) (L := L) hp hexponent hcard v,
    hquot]
  exact Subgroup.map_bot _

omit [NumberField L] in
/-- Every place with proper decomposition group in `L / K` splits
completely, in the standard chosen-extension sense, in the actual
degree-`p` fixed subextension. -/
theorem
    finitePlaceSplitsCompletely_in_cyclicPrimeSubextension_of_decompositionGroup_ne_top
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard : Nat.card (L ≃ₐ[K] L) = p ^ exponent)
    (v : HeightOneSpectrum (𝓞 K))
    (hproper :
      finitePlaceDecompositionGroup
          (K := K) (L := L) v ≠ ⊤) :
    FinitePlaceSplitsCompletely
      (K := K)
      (L := cyclicPrimeSubextension
        (K := K) (L := L)
        hp hexponent hcard) v := by
  let M :=
    cyclicPrimeSubextension
      (K := K) (L := L)
      hp hexponent hcard
  let : IsGalois K M :=
    cyclicPrimeSubextension_isGalois
      (K := K) (L := L)
      hp hexponent hcard
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let w :=
    chosenFinitePlaceExtension (L := L) v
  let wM :=
    restrictAbsoluteValueExtensionToIntermediate
      vK w M
  have hcustom :
      cyclicPrimeSubextensionDecompositionGroup
          (K := K) (L := L)
          hp hexponent hcard v = ⊥ :=
    cyclicPrimeSubextensionDecompositionGroup_eq_bot_of_ne_top
      (K := K) (L := L)
      hp hexponent hcard v hproper
  have hwMbot :
      absoluteValueDecompositionGroup K wM.1 = ⊥ := by
    change
      absoluteValueDecompositionGroup K
        (w.1.comp (f := algebraMap M L)
          (algebraMap M L).injective) = ⊥
    rw [← absoluteValueDecompositionGroup_map_restrictNormalHom
      (M := M) vK hvK w]
    exact hcustom
  change
    absoluteValueDecompositionGroup K
      (chosenFinitePlaceExtension
        (L := M) v).1 = ⊥
  exact
    absoluteValueDecompositionGroup_eq_bot_independent_extension
      vK hvK wM
      (chosenFinitePlaceExtension (L := M) v)
      hwMbot

/-- If every finite place outside a finite set splits completely, then
idelic approximation shows that every idele class is a norm. -/
theorem ideleClassNorm_range_eq_top_of_splitsCompletely_outside
    {E : Type}
    [Field E] [NumberField E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hsplit :
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        FinitePlaceSplitsCompletely
          (K := K) (L := E) v) :
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range = ⊤ := by
  apply top_unique
  intro c _
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (IdeleGroup.principalSubgroup K) c
  obtain ⟨x, hfinite, hinfinite⟩ :=
    exists_principal_quotient_locallyNormEverywhere_of_splitsOutside
      (K := K) (L := E) S hsplit a
  let b : IdeleGroup K :=
    a * (IdeleGroup.principalIdele K x)⁻¹
  have hInfinite :
      ∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w b ∈
          infiniteTensorNormSubgroup
            (K := K) (L := E) w := by
    intro w
    change
      IdeleGroup.infiniteComponent w
          (a * (IdeleGroup.principalIdele K x)⁻¹) ∈
        infiniteTensorNormSubgroup
          (K := K) (L := E) w
    rw [map_mul, map_inv]
    exact hinfinite w
  have hFinite :
      ∀ v : HeightOneSpectrum (𝓞 K),
        IdeleGroup.finiteComponent v b ∈
          (_root_.localTensorNorm
            (K := K) (L := E) v).range := by
    intro v
    rw [
      finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
        (K := K) (L := E) v]
    simpa [b] using hfinite v
  have hb :
      b ∈ (RelativeIdeleGroup.norm K E).range :=
    (mem_relativeIdeleNorm_range_iff_localTensorNorms
      (K := K) (L := E) b).2 ⟨hInfinite, hFinite⟩
  obtain ⟨z, hz⟩ := hb
  refine
    ⟨QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K E) z, ?_⟩
  rw [RelativeIdeleGroup.Cohomology.ideleClassNorm_mk, hz]
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) b =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a
  have hp :
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (IdeleGroup.principalIdele K x) = 1 :=
    (QuotientGroup.eq_one_iff
      (IdeleGroup.principalIdele K x)).2 ⟨x, rfl⟩
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (a * (IdeleGroup.principalIdele K x)⁻¹) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a
  rw [map_mul, map_inv, hp]
  exact
    mul_one
      (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a)

/-- The preceding surjectivity says that the idele-class norm index is
one. -/
theorem ideleClassNorm_index_eq_one_of_splitsCompletely_outside
    {E : Type}
    [Field E] [NumberField E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hsplit :
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        FinitePlaceSplitsCompletely
          (K := K) (L := E) v) :
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index = 1 := by
  rw [
    ideleClassNorm_range_eq_top_of_splitsCompletely_outside
      (K := K) (E := E) S hsplit,
    Subgroup.index_top]

/-- Assuming the norm-index lower bound for the chosen prime-degree
subextension, the set of finite places whose decomposition group is the
whole Galois group is infinite. -/
theorem
    cyclic_prime_power_fullDecompositionPlaces_infinite_of_primeSubextension_normIndex
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard : Nat.card (L ≃ₐ[K] L) = p ^ exponent)
    (hLower :
      p ≤
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K
          (cyclicPrimeSubextension
            (K := K) (L := L)
            hp hexponent hcard)).range.index) :
    Set.Infinite
      {v : HeightOneSpectrum (𝓞 K) |
        finitePlaceDecompositionGroup
            (K := K) (L := L) v = ⊤} := by
  intro hfinite
  let S : Finset (HeightOneSpectrum (𝓞 K)) :=
    hfinite.toFinset
  have hsplit :
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        FinitePlaceSplitsCompletely
          (K := K)
          (L := cyclicPrimeSubextension
            (K := K) (L := L)
            hp hexponent hcard) v := by
    intro v hv
    apply
      finitePlaceSplitsCompletely_in_cyclicPrimeSubextension_of_decompositionGroup_ne_top
        (K := K) (L := L)
        hp hexponent hcard v
    intro htop
    apply hv
    simp [S, htop]
  have hindex :
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K
        (cyclicPrimeSubextension
          (K := K) (L := L)
          hp hexponent hcard)).range.index = 1 :=
    ideleClassNorm_index_eq_one_of_splitsCompletely_outside
      (K := K)
      (E := cyclicPrimeSubextension
        (K := K) (L := L)
        hp hexponent hcard)
      S hsplit
  have hp_le_one : p ≤ 1 := by
    simpa [hindex] using hLower
  exact (Nat.not_lt_of_ge hp_le_one) hp.one_lt

/-- In a cyclic extension of prime-power degree, infinitely many finite
places have full decomposition group.  The norm-index input in the
preceding theorem is supplied by the unconditional lower bound for the
chosen degree-`p` subextension. -/
theorem cyclic_prime_power_infinite_fullDecompositionPlaces
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard : Nat.card (L ≃ₐ[K] L) = p ^ exponent) :
    Set.Infinite
      {v : HeightOneSpectrum (𝓞 K) |
        finitePlaceDecompositionGroup
            (K := K) (L := L) v = ⊤} := by
  let M :=
    cyclicPrimeSubextension
      (K := K) (L := L)
      hp hexponent hcard
  let : IsGalois K M :=
    cyclicPrimeSubextension_isGalois
      (K := K) (L := L)
      hp hexponent hcard
  let : IsCyclic (M ≃ₐ[K] M) := by
    simpa [M] using
      cyclicPrimeSubextension_isCyclic
        (K := K) (L := L)
        hp hexponent hcard
  obtain ⟨σ, hσ⟩ :=
    IsCyclic.exists_generator (α := M ≃ₐ[K] M)
  have hLowerM :
      Module.finrank K M ≤
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range.index :=
    finrank_le_ideleClassNorm_index
      (K := K) (L := M) σ hσ
  have hDegree : Module.finrank K M = p := by
    simpa [M] using
      cyclicPrimeSubextension_finrank
        (K := K) (L := L)
        hp hexponent hcard
  apply
    cyclic_prime_power_fullDecompositionPlaces_infinite_of_primeSubextension_normIndex
      (K := K) (L := L)
      hp hexponent hcard
  simpa [M, hDegree] using hLowerM

/-- Finset-avoidance form of the conditional full-decomposition
infinitude result, convenient for recursively choosing new places. -/
theorem
    exists_fullDecompositionPlace_outside_finset_of_primeSubextension_normIndex
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard : Nat.card (L ≃ₐ[K] L) = p ^ exponent)
    (hLower :
      p ≤
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K
          (cyclicPrimeSubextension
            (K := K) (L := L)
            hp hexponent hcard)).range.index)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v : HeightOneSpectrum (𝓞 K),
      v ∉ S ∧
      finitePlaceDecompositionGroup
          (K := K) (L := L) v = ⊤ := by
  have hinfinite :=
    cyclic_prime_power_fullDecompositionPlaces_infinite_of_primeSubextension_normIndex
      (K := K) (L := L)
      hp hexponent hcard hLower
  by_contra hexists
  push Not at hexists
  apply hinfinite
  apply S.finite_toSet.subset
  intro v hv
  by_contra hvS
  exact (hexists v hvS) hv

/-- Finset-avoidance form of the unconditional full-decomposition
infinitude theorem. -/
theorem exists_fullDecompositionPlace_outside_finset
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard : Nat.card (L ≃ₐ[K] L) = p ^ exponent)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v : HeightOneSpectrum (𝓞 K),
      v ∉ S ∧
      finitePlaceDecompositionGroup
          (K := K) (L := L) v = ⊤ := by
  have hinfinite :=
    cyclic_prime_power_infinite_fullDecompositionPlaces
      (K := K) (L := L)
      hp hexponent hcard
  by_contra hexists
  push Not at hexists
  apply hinfinite
  apply S.finite_toSet.subset
  intro v hv
  by_contra hvS
  exact (hexists v hvS) hv

end Cohomology
end GlobalClassFieldTheory
