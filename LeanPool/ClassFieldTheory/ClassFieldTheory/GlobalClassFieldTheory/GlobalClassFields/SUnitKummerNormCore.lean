/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.ArchimedeanPowerIndex
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.LocalResidueArithmetic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlacePowerIndex
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.NormContainment
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.SupportedIdeleIndex
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.SupportedPrincipalQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.PrimePowerKummerIndex
/-!
# The full S-unit Kummer norm core

Starting from a prescribed finite set of finite places, we enlarge it by
a fixed idelic support and by a chosen support of the exponent.  For this
enlarged set, a principal idele satisfies the local power conditions exactly
when it is the power of an `S`-unit.  Consequently the associated idele-class
power quotient has the same cardinality as the Galois group of the full
`S`-unit Kummer extension.

These are the two concrete cardinal ingredients in the class-field existence
argument.
-/

@[expose] public section

open scoped NumberField BigOperators

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain
open GlobalClassFieldTheory.ClassFieldAxiom
open KummerTheory

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- If `K` contains the `n`-th roots of unity and `n > 1`, then either
`n` is even or `K` has no real infinite places.  This is exactly the
archimedean condition needed to place all local `n`-th powers in the
infinite norm subgroup. -/
theorem even_or_no_realInfinitePlace_of_primitiveRoots
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hn : 1 < (n : ℕ)) :
    Even (n : ℕ) ∨
      ∀ w : InfinitePlace K, ¬ w.IsReal := by
  by_cases hnEven : Even (n : ℕ)
  · exact Or.inl hnEven
  · refine Or.inr ?_
    have hnNeTwo : (n : ℕ) ≠ 2 := by
      intro hnTwo
      apply hnEven
      rw [hnTwo]
      exact ⟨1, by omega⟩
    have hnLarge : 2 < (n : ℕ) := by
      omega
    obtain ⟨zeta, hzeta⟩ := hmu
    have hzetaPrimitive :
        IsPrimitiveRoot zeta (n : ℕ) :=
      (mem_primitiveRoots n.pos).mp hzeta
    have hRealZero :
        InfinitePlace.nrRealPlaces K = 0 :=
      InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
        hnLarge hzetaPrimitive
    intro w hwReal
    have hRealPos :
        0 < InfinitePlace.nrRealPlaces K :=
      Fintype.card_pos_iff.mpr ⟨⟨w, hwReal⟩⟩
    omega

open scoped Classical in
/-- The chosen finite support used for the full `S`-unit Kummer
construction: it contains the prescribed seed, a support large enough to
represent every idele class, and the finite support of the exponent. -/
noncomputable def sUnitKummerNormSupport
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let nUnit : Kˣ := Units.mk0 ((n : ℕ) : K) hnK
  (S ∪ IdeleGroup.sufficientlyLargeFiniteSet (K := K)) ∪
    chosenUnitFiniteSupport (K := K) nUnit

open scoped Classical in
/-- The prescribed seed is contained in the chosen Kummer norm
support. -/
theorem subset_sUnitKummerNormSupport
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    S ⊆ sUnitKummerNormSupport (K := K) n S := by
  intro v hv
  exact Finset.mem_union_left _
    (Finset.mem_union_left _ hv)

open scoped Classical in
/-- Away from the chosen Kummer norm support, the exponent is a local
unit.  This is the local input needed for the unramifiedness of the full
`S`-unit Kummer extension. -/
theorem valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {w : HeightOneSpectrum (𝓞 K)}
    (hw : w ∉ sUnitKummerNormSupport (K := K) n S) :
    w.valuation K ((n : ℕ) : K) = 1 := by
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let nUnit : Kˣ := Units.mk0 ((n : ℕ) : K) hnK
  have hwSupport :
      w ∉ chosenUnitFiniteSupport (K := K) nUnit := by
    intro hwSupport
    apply hw
    exact Finset.mem_union_right _ hwSupport
  have hnUnitVal :
      w.valuation K (nUnit : K) = 1 :=
    (mem_SUnitGroup_iff
      (K := K)
      (chosenUnitFiniteSupport (K := K) nUnit) nUnit).mp
        (mem_sUnitGroup_chosenUnitFiniteSupport
          (K := K) nUnit)
        w hwSupport
  change w.valuation K ((n : ℕ) : K) = 1 at hnUnitVal
  exact hnUnitVal

open scoped Classical in
/-- Every finite place dividing the exponent belongs to the chosen
Kummer norm support. -/
theorem mem_sUnitKummerNormSupport_of_asIdeal_dvd_natCast
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {w : HeightOneSpectrum (𝓞 K)}
    (hw : w.asIdeal ∣ Ideal.span {((n : ℕ) : 𝓞 K)}) :
    w ∈ sUnitKummerNormSupport (K := K) n S := by
  by_contra hwSupport
  have hnValLt :
      w.valuation K ((n : ℕ) : K) < 1 := by
    simpa using
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_dvd
        (K := K) w ((n : ℕ) : 𝓞 K)).2 hw
  exact
    (ne_of_lt hnValLt)
      (valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport
        (K := K) n S hwSupport)

open scoped Classical in
/-- The chosen Kummer norm support is large enough to represent every
idele class by an idele supported on it. -/
theorem supportedAt_sUnitKummerNormSupport_sup_principalSubgroup_eq_top
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IdeleGroup.supportedAt
          (K := K)
          (sUnitKummerNormSupport (K := K) n S : Set _) ⊔
        IdeleGroup.principalSubgroup K =
      ⊤ := by
  apply top_unique
  rw [
    ← IdeleGroup.supportedAt_sup_principalSubgroup_eq_top
      (K := K)]
  apply sup_le_sup
  · apply IdeleGroup.supportedAt_mono
    intro v hv
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ hv)
  · exact le_rfl

/-- A root of a unit descends along a surjective field homomorphism. -/
private theorem unit_mem_power_range_of_surjective
    {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (hf : Function.Surjective f) (n : ℕ) (b : Fˣ) (beta : Eˣ)
    (hbeta : beta ^ n = Units.map f.toMonoidHom b) :
    b ∈ (powMonoidHom n : Fˣ →* Fˣ).range := by
  obtain ⟨x, hx⟩ := hf (beta : E)
  have hx_ne : x ≠ 0 := by
    intro hzero
    apply beta.ne_zero
    rw [← hx, hzero, map_zero]
  refine ⟨Units.mk0 x hx_ne, ?_⟩
  apply Units.ext
  apply f.injective
  change f (x ^ n) = f (b : F)
  rw [map_pow, hx]
  exact congrArg Units.val hbeta

open scoped Classical in

open _root_.KummerTheory
  (chosenSimpleKummerExtension_infiniteTensorNormSubgroup_eq_top_of_mem_nthPowerSubgroup) in
/-- On the chosen Kummer norm support, the principal part of the
local power subgroup consists exactly of powers of `S`-units. -/
theorem
    principalIdelePowerLocalUnitSubgroup_eq_sUnitNthPowers_on_kummerNormSupport
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let S' := sUnitKummerNormSupport (K := K) n S
    principalIdelePowerLocalUnitSubgroup (K := K) n S' ∅ =
      sUnitNthPowersInField (K := K) n S' := by
  classical
  dsimp only
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let S' := sUnitKummerNormSupport (K := K) n S
  change
    principalIdelePowerLocalUnitSubgroup (K := K) n S' ∅ =
      sUnitNthPowersInField (K := K) n S'
  have hLarge := supportedAt_sUnitKummerNormSupport_sup_principalSubgroup_eq_top
    (K := K) n S
  apply le_antisymm
  · intro b hb
    have hbData :=
      (mem_idelePowerLocalUnitSubgroup_iff
        (K := K) n S' ∅
        (IdeleGroup.principalIdele K b)).mp hb
    have hbSUnit :
        b ∈ SUnitGroup (K := K) S' := by
      simpa only [Finset.union_empty] using
        (principalIdelePowerLocalUnitSubgroup_le_sUnitGroup
          (K := K) n S' ∅ hb)
    let M := KummerTheory.chosenSimpleKummerExtension K n hnK b
    let : FiniteDimensional K M :=
      KummerTheory.chosenSimpleKummerExtension_finiteDimensional
        K n hnK b
    let : IsAbelianGalois K M :=
      KummerTheory.chosenSimpleKummerExtension_isAbelianGalois
        K n hnK hmu b
    let : NumberField M :=
      NumberField.of_module_finite K M
    let : (RelativeIdeleGroup.principalSubgroup K M).Normal :=
      ⟨fun x hx g => by
        have hconj : g * x * g⁻¹ = x := by
          rw [mul_comm g x, mul_assoc, mul_inv_cancel, mul_one]
        rwa [hconj]⟩
    have hSplitS :
        ∀ w : HeightOneSpectrum (𝓞 K), w ∈ S' →
          _root_.FinitePlaceSplitsCompletely
            (K := K) (L := M) w := by
      intro w hw
      have hbLocal := hbData.2.1 w hw
      have hprincipal :
          IdeleGroup.finiteComponent w
              (IdeleGroup.principalIdele K b) =
            Units.map
              (algebraMap K (w.adicCompletion K)).toMonoidHom b := by
        apply Units.ext
        rfl
      rw [hprincipal] at hbLocal
      simpa only [M] using
        KummerTheory.chosenSimpleKummerExtension_finitePlaceSplitsCompletely_of_mem_nthPowerSubgroup
          (K := K) n hnK hmu b w hbLocal
    have hInfiniteTop :
        ∀ w : InfinitePlace K,
          _root_.infiniteTensorNormSubgroup
            (K := K) (L := M) w = ⊤ := by
      intro w
      have hbLocal := hbData.1 w
      have hprincipal :
          IdeleGroup.infiniteComponent w
              (IdeleGroup.principalIdele K b) =
            Units.map
              (algebraMap K w.Completion).toMonoidHom b := by
        apply Units.ext
        rfl
      rw [hprincipal] at hbLocal
      simpa only [M] using
        chosenSimpleKummerExtension_infiniteTensorNormSubgroup_eq_top_of_mem_nthPowerSubgroup
          (K := K) n hnK hmu b w hbLocal
    have hAway :
        ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S' →
          _root_.ChosenFinitePlaceIsUnramified
            (K := K) (L := M) w := by
      intro w hw
      have hbVal :
          w.valuation K (b : K) = 1 :=
        (mem_SUnitGroup_iff
          (K := K) S' b).mp hbSUnit w hw
      have hnVal :
          w.valuation K ((n : ℕ) : K) = 1 := by
        exact
          valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport
            (K := K) n S hw
      simpa only [M] using
        KummerTheory.chosenSimpleKummerExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
          (K := K) n hnK hmu b w hbVal hnVal
    have hNormTop :
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range =
          ⊤ := by
      apply top_unique
      intro c _
      obtain ⟨a, rfl⟩ :=
        QuotientGroup.mk'_surjective
          (IdeleGroup.principalSubgroup K) c
      have ha :
          a ∈
            IdeleGroup.supportedAt
                (K := K)
                (S' : Set (HeightOneSpectrum (𝓞 K))) ⊔
              IdeleGroup.principalSubgroup K := by
        rw [hLarge]
        exact Subgroup.mem_top a
      rcases Subgroup.mem_sup.mp ha with
        ⟨u, hu, q, hq, huq⟩
      have hInfinite :
          ∀ w : InfinitePlace K,
            IdeleGroup.infiniteComponent w u ∈
              _root_.infiniteTensorNormSubgroup
                (K := K) (L := M) w := by
        intro w
        rw [hInfiniteTop w]
        exact Subgroup.mem_top _
      have hFinite :
          ∀ w : HeightOneSpectrum (𝓞 K),
            IdeleGroup.finiteComponent w u ∈
              (localTensorNorm
                (K := K) (L := M) w).range := by
        intro w
        rw [
          _root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
            (K := K) (L := M) w]
        by_cases hwS : w ∈ S'
        · rw [
            _root_.chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely
              (K := K) (L := M) w (hSplitS w hwS)]
          exact Subgroup.mem_top _
        · apply
            _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
              (K := K) (L := M) w (hAway w hwS)
          exact
            (IdeleGroup.mem_supportedAt_iff
              (K := K)
              (S' : Set (HeightOneSpectrum (𝓞 K))) u).mp
                hu w (by simpa using hwS)
      have huNorm :
          u ∈ (RelativeIdeleGroup.norm K M).range :=
        (_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms
          (K := K) (L := M) u).2
            ⟨hInfinite, hFinite⟩
      obtain ⟨z, hz⟩ := huNorm
      refine
        ⟨QuotientGroup.mk'
            (RelativeIdeleGroup.principalSubgroup K M) z, ?_⟩
      rw [RelativeIdeleGroup.Cohomology.ideleClassNorm_mk, hz]
      change
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) u =
          QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a
      have hqOne :
          QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K) q = 1 :=
        (QuotientGroup.eq_one_iff q).mpr hq
      rw [← huq, map_mul, hqOne]
      exact
        (mul_one
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) u :
            IdeleClassGroup K)).symm
    let : IsCyclic (M ≃ₐ[K] M) := by
      simpa only [M] using
        KummerTheory.chosenSimpleKummerExtension_isCyclic
          K n hnK hmu b
    obtain ⟨sigma, hsigma⟩ :=
      IsCyclic.exists_generator (α := M ≃ₐ[K] M)
    have hLower :
        Module.finrank K M ≤
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range.index :=
      Cohomology.finrank_le_ideleClassNorm_index
        (K := K) (L := M) sigma hsigma
    have hDegreeLe :
        Module.finrank K M ≤ 1 := by
      simpa only [hNormTop, Subgroup.index_top] using hLower
    have hDegree :
        Module.finrank K M = 1 :=
      le_antisymm hDegreeLe Module.finrank_pos
    have hAlgMap :
        Function.Bijective (algebraMap K M) :=
      (Algebra.finrank_eq_one_iff_bijective_algebraMap).mp
        hDegree
    let beta : Mˣ :=
      KummerTheory.chosenSimpleKummerRootUnit K n hnK b
    have hbeta :
        beta ^ (n : ℕ) =
          Units.map (algebraMap K M).toMonoidHom b := by
      simpa only [M, beta] using
        KummerTheory.chosenSimpleKummerRootUnit_pow K n hnK b
    have hbPower := unit_mem_power_range_of_surjective
      (algebraMap K M) hAlgMap.2 (n : ℕ) b beta hbeta
    exact
      (mem_sUnitNthPowersInField_iff
        (K := K) n S' b).2
          ⟨hbSUnit, hbPower⟩
  · simpa only [Finset.union_empty] using
      sUnitNthPowersInField_le_principalIdelePowerLocalUnitSubgroup
        (K := K) n S' ∅

open scoped Classical in
/-- The idele-class power quotient attached to the chosen Kummer norm
support has cardinality `n` to the number of supported places. -/
theorem card_ideleClassPowerLocalUnitQuotient_on_kummerNormSupport
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let S' := sUnitKummerNormSupport (K := K) n S
    Nat.card
        (IdeleClassPowerLocalUnitQuotient
          (K := K) n S' ∅) =
      (n : ℕ) ^ totalPlaceCard (K := K) S' := by
  classical
  dsimp only
  let S' := sUnitKummerNormSupport (K := K) n S
  change
    Nat.card
        (IdeleClassPowerLocalUnitQuotient
          (K := K) n S' ∅) =
      (n : ℕ) ^ totalPlaceCard (K := K) S'
  have hPrincipal :
      principalIdelePowerLocalUnitSubgroup
          (K := K) n S' ∅ =
        sUnitNthPowersInField (K := K) n S' := by
    simpa only [S'] using
      principalIdelePowerLocalUnitSubgroup_eq_sUnitNthPowers_on_kummerNormSupport
        (K := K) n hmu S
  have hDen :
      sUnitPrincipalIdelePowerSubgroup
          (K := K) n S' ∅ =
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) (S' ∪ ∅) →*
            SUnitGroup (K := K) (S' ∪ ∅)).range := by
    unfold sUnitPrincipalIdelePowerSubgroup
    rw [Finset.union_empty]
    rw [hPrincipal, sUnitNthPowersInField]
    exact
      Subgroup.comap_map_eq_self_of_injective
        (SUnitGroup (K := K) S').subtype_injective _
  have hDiv :
      ∀ w : HeightOneSpectrum (𝓞 K),
        w.asIdeal ∣
            Ideal.span {((n : ℕ) : 𝓞 K)} →
          w ∈ S' := by
    intro w hwDvd
    exact
      mem_sUnitKummerNormSupport_of_asIdeal_dvd_natCast
        (K := K) n S hwDvd
  have hLarge :
      IdeleGroup.supportedAt
            (K := K) (S' : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤ := by
    simpa only [S'] using
      supportedAt_sUnitKummerNormSupport_sup_principalSubgroup_eq_top
        (K := K) n S
  have hProduct :=
    card_sUnitPrincipalQuotient_mul_card_ideleClassQuotient_eq_power_two_totalPlaceCard
      (K := K) n hmu S' ∅ hDiv
      (by
        simpa only [Finset.coe_empty, Set.union_empty] using hLarge)
  rw [hDen,
    card_sUnit_nthPowerQuotient
      (K := K) (S' ∪ ∅) n hmu] at hProduct
  simp only [Finset.union_empty] at hProduct
  have hPower :
      (n : ℕ) ^ (2 * totalPlaceCard (K := K) S') =
        (n : ℕ) ^ totalPlaceCard (K := K) S' *
          (n : ℕ) ^ totalPlaceCard (K := K) S' := by
    rw [two_mul, pow_add]
  exact
    Nat.eq_of_mul_eq_mul_left
      (pow_pos n.pos (totalPlaceCard (K := K) S'))
      (hProduct.trans hPower)

open scoped Classical in
/-- The power quotient on the chosen support has the same cardinality
as the degree of the full `S`-unit Kummer extension. -/
theorem
    card_ideleClassPowerLocalUnitQuotient_eq_finrank_fullSUnitKummerExtension
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let S' := sUnitKummerNormSupport (K := K) n S
    let E :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    letI : FiniteDimensional K E :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n
        (by exact_mod_cast n.ne_zero) hmu S'
    Nat.card
        (IdeleClassPowerLocalUnitQuotient
          (K := K) n S' ∅) =
      Module.finrank K E := by
  classical
  dsimp only
  let S' := sUnitKummerNormSupport (K := K) n S
  let E :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K E :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  let : IsGalois K E :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  calc
    Nat.card
          (IdeleClassPowerLocalUnitQuotient
            (K := K) n S' ∅) =
        (n : ℕ) ^ totalPlaceCard (K := K) S' := by
      simpa only [S'] using
        card_ideleClassPowerLocalUnitQuotient_on_kummerNormSupport
          (K := K) n hmu S
    _ = Nat.card Gal(E/K) := by
      symm
      simpa only [E] using
        card_fullSUnitKummerExtension_galois
          (K := K) (Omega := Omega) n hnK hmu S'
    _ = Module.finrank K E :=
      IsGalois.card_aut_eq_finrank K E

end GlobalClassFields
end GlobalClassFieldTheory
