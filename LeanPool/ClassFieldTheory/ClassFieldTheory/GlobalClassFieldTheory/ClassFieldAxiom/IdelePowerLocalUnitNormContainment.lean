/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitLocalPowerMap
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitSubgroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.KummerLocalNormContainment
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleClassHerbrandSupportedFinal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm
/-!
# Norm containment for idele power-local-unit subgroups

This module packages the finite-place local norm conditions and proves the
global norm containment and principal-intersection identity used in the
idele-class norm-index argument.
-/

@[expose] public section

open scoped NumberField NNReal IsMulCommutative
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open KummerTheory
open LocalFieldTheory

noncomputable
section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- Ideles whose components at the finite places of `S` are local norms
from the chosen localizations of `L / K`. -/
def finitePlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [IsGalois K L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (IdeleGroup K) :=
  ⨅ v : ↥S,
    (_root_.chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v.1).comap
        (IdeleGroup.finiteComponent v.1)

open scoped Classical in
/-- Elementwise form of the finite family of local norm conditions. -/
theorem mem_finitePlaceLocalNormCondition_iff
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : IdeleGroup K) :
    a ∈ finitePlaceLocalNormCondition
        (K := K) (L := L) S ↔
      ∀ v : ↥S,
        IdeleGroup.finiteComponent v.1 a ∈
          _root_.chosenFinitePlaceLocalNormSubgroup
            (K := K) (L := L) v.1 := by
  simp [finitePlaceLocalNormCondition]

open scoped Classical in
/-- At every finite place in `S`, the `n`-power condition defining
`h(S,T)` implies the actual local norm condition for an exponent-`n`
Kummer extension. -/
theorem idelePowerLocalUnitSubgroup_le_finitePlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+) (r : ℕ)
    (eG :
      (L ≃ₐ[K] L) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    idelePowerLocalUnitSubgroup (K := K) n S T ≤
      finitePlaceLocalNormCondition
        (K := K) (L := L) S := by
  intro a ha
  rw [mem_finitePlaceLocalNormCondition_iff]
  intro v
  apply
    nthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) n r eG v.1
  exact
    ((mem_idelePowerLocalUnitSubgroup_iff
      (K := K) n S T a).mp ha).2.1 v.1 v.2

open scoped Classical in
/-- The finite components of `h(S,T)` at `S ∪ T` are actual local norms:
at `S` this follows from the exponent-`n` Galois structure, while at `T`
it follows from complete splitting. -/
theorem idelePowerLocalUnitSubgroup_le_unionLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+) (r : ℕ)
    (eG :
      (L ≃ₐ[K] L) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT :
      ∀ v, v ∈ T →
        _root_.FinitePlaceSplitsCompletely
          (K := K) (L := L) v) :
    idelePowerLocalUnitSubgroup (K := K) n S T ≤
      finitePlaceLocalNormCondition
        (K := K) (L := L) (S ∪ T) := by
  intro a ha
  rw [mem_finitePlaceLocalNormCondition_iff]
  intro v
  rcases Finset.mem_union.mp v.2 with hvS | hvT
  · apply
      nthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) n r eG v.1
    exact
      ((mem_idelePowerLocalUnitSubgroup_iff
        (K := K) n S T a).mp ha).2.1 v.1 hvS
  · rw [
      _root_.chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely
        (K := K) (L := L) v.1 (hT v.1 hvT)]
    exact Subgroup.mem_top _

open scoped Classical in
/-- The simultaneous local norm condition at every finite place. -/
def allFinitePlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [IsGalois K L] :
    Subgroup (IdeleGroup K) :=
  ⨅ v : HeightOneSpectrum (𝓞 K),
    (_root_.chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v).comap
        (IdeleGroup.finiteComponent v)

open scoped Classical in
/-- Under the concrete splitting and unramifiedness conditions, every finite
component of `h(S,T)` is an actual local norm. -/
theorem idelePowerLocalUnitSubgroup_le_allFinitePlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+) (r : ℕ)
    (eG :
      (L ≃ₐ[K] L) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT :
      ∀ v, v ∈ T →
        _root_.FinitePlaceSplitsCompletely
          (K := K) (L := L) v)
    (hAway :
      ∀ v, v ∉ S ∪ T →
        _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := L) v) :
    idelePowerLocalUnitSubgroup (K := K) n S T ≤
      allFinitePlaceLocalNormCondition
        (K := K) (L := L) := by
  intro a ha
  rw [allFinitePlaceLocalNormCondition]
  apply Subgroup.mem_iInf.mpr
  intro v
  by_cases hv : v ∈ S ∪ T
  · rcases Finset.mem_union.mp hv with hvS | hvT
    · apply
        nthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) n r eG v
      exact
        ((mem_idelePowerLocalUnitSubgroup_iff
          (K := K) n S T a).mp ha).2.1 v hvS
    · rw [
        _root_.chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely
          (K := K) (L := L) v (hT v hvT)]
      exact Subgroup.mem_top _
  · apply
      _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v (hAway v hv)
    exact
      ((mem_idelePowerLocalUnitSubgroup_iff
        (K := K) n S T a).mp ha).2.2 v hv

open scoped Classical in
/-- Every global relative-idele norm satisfies all of the actual
finite-place local norm conditions. -/
theorem relativeIdeleNorm_range_le_allFinitePlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (RelativeIdeleGroup.norm K L).range ≤
      allFinitePlaceLocalNormCondition
        (K := K) (L := L) := by
  rintro a ⟨b, rfl⟩
  rw [allFinitePlaceLocalNormCondition]
  apply Subgroup.mem_iInf.mpr
  intro v
  exact
    _root_.relativeIdeleNorm_finiteComponent_mem_chosenLocalNormSubgroup
      (K := K) (L := L) v b

private theorem exists_supported_idele_same_class_local_powers
    {K : Type} [Field K] [NumberField K]
    (n : ℕ+) (S' T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S' T)
    (hSurj : Function.Surjective (sUnitLocalUnitPowerMap (K := K) n S' T hST))
    (u : IdeleGroup K)
    (hu : u ∈ IdeleGroup.supportedAt (K := K) (S' : Set (HeightOneSpectrum (𝓞 K)))) :
    ∃ d : IdeleGroup K,
      d ∈ IdeleGroup.supportedAt (K := K) (S' : Set (HeightOneSpectrum (𝓞 K))) ∧
      (∀ w : T, IdeleGroup.finiteComponent w.1 d ∈
        (powMonoidHom (n : ℕ) : (w.1.adicCompletion K)ˣ →* (w.1.adicCompletion K)ˣ).range) ∧
      QuotientGroup.mk' (IdeleGroup.principalSubgroup K) d =
        QuotientGroup.mk' (IdeleGroup.principalSubgroup K) u := by
  classical
  have hT_not_mem_S (w : T) : w.1 ∉ S' := by
    intro hwS
    exact (Finset.disjoint_left.mp hST) hwS w.2
  let uLocalUnit (w : T) :
      (w.1.adicCompletionIntegers K)ˣ :=
    (w.1.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType
      ⟨IdeleGroup.finiteComponent w.1 u,
        (IdeleGroup.mem_supportedAt_iff
          (K := K)
          (S' : Set (HeightOneSpectrum (𝓞 K))) u).mp
            hu w.1 (by simpa using hT_not_mem_S w)⟩
  let target :
      ∀ w : T,
        (w.1.adicCompletionIntegers K)ˣ ⧸
          (powMonoidHom (n : ℕ) :
            (w.1.adicCompletionIntegers K)ˣ →*
              (w.1.adicCompletionIntegers K)ˣ).range :=
    fun w =>
      QuotientGroup.mk'
        (powMonoidHom (n : ℕ) :
          (w.1.adicCompletionIntegers K)ˣ →*
            (w.1.adicCompletionIntegers K)ˣ).range
        (uLocalUnit w)
  obtain ⟨s, hs⟩ := hSurj target
  have hsSupported :
      IdeleGroup.principalIdele K (s : Kˣ) ∈
        IdeleGroup.supportedAt
          (K := K)
          (S' : Set (HeightOneSpectrum (𝓞 K))) :=
    (_root_.principalIdele_mem_supportedAt_iff_sUnit
      (L := K) S' (s : Kˣ)).2 s.2
  let sLocalUnit (w : T) :
      (w.1.adicCompletionIntegers K)ˣ :=
    (w.1.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType
      ⟨IdeleGroup.finiteComponent w.1
          (IdeleGroup.principalIdele K (s : Kˣ)),
        (IdeleGroup.mem_supportedAt_iff
          (K := K)
          (S' : Set (HeightOneSpectrum (𝓞 K)))
          (IdeleGroup.principalIdele K (s : Kˣ))).mp
            hsSupported w.1 (by simpa using hT_not_mem_S w)⟩
  let d : IdeleGroup K :=
    u * (IdeleGroup.principalIdele K (s : Kˣ))⁻¹
  have hdSupported :
      d ∈
        IdeleGroup.supportedAt
          (K := K)
          (S' : Set (HeightOneSpectrum (𝓞 K))) := by
    dsimp only [d]
    exact
      (IdeleGroup.supportedAt
        (K := K)
        (S' : Set (HeightOneSpectrum (𝓞 K)))).mul_mem
          hu
          ((IdeleGroup.supportedAt
            (K := K)
            (S' : Set (HeightOneSpectrum (𝓞 K)))).inv_mem
              hsSupported)
  have hTpower (w : T) :
      IdeleGroup.finiteComponent w.1 d ∈
        (powMonoidHom (n : ℕ) :
          (w.1.adicCompletion K)ˣ →*
            (w.1.adicCompletion K)ˣ).range := by
    have hw := congrFun hs w
    change
      QuotientGroup.mk'
          (powMonoidHom (n : ℕ) :
            (w.1.adicCompletionIntegers K)ˣ →*
              (w.1.adicCompletionIntegers K)ˣ).range
          (sLocalUnit w) =
        QuotientGroup.mk'
          (powMonoidHom (n : ℕ) :
            (w.1.adicCompletionIntegers K)ˣ →*
              (w.1.adicCompletionIntegers K)ˣ).range
          (uLocalUnit w) at hw
    have hIntegerPower :
        uLocalUnit w / sLocalUnit w ∈
          (powMonoidHom (n : ℕ) :
            (w.1.adicCompletionIntegers K)ˣ →*
              (w.1.adicCompletionIntegers K)ˣ).range :=
      (QuotientGroup.eq_iff_div_mem).mp hw.symm
    let toField :
        (w.1.adicCompletionIntegers K)ˣ →*
          (w.1.adicCompletion K)ˣ :=
      Units.map
        (w.1.adicCompletionIntegers K).subtype.toMonoidHom
    obtain ⟨z, hz⟩ := hIntegerPower
    have hFieldPower :
        toField (uLocalUnit w / sLocalUnit w) ∈
          (powMonoidHom (n : ℕ) :
            (w.1.adicCompletion K)ˣ →*
              (w.1.adicCompletion K)ˣ).range := by
      refine ⟨toField z, ?_⟩
      change
        (toField z) ^ (n : ℕ) =
          toField (uLocalUnit w / sLocalUnit w)
      simpa only [powMonoidHom_apply, map_pow] using
        congrArg toField hz
    have huToField :
        toField (uLocalUnit w) =
          IdeleGroup.finiteComponent w.1 u := by
      apply Units.ext
      rfl
    have hsToField :
        toField (sLocalUnit w) =
          IdeleGroup.finiteComponent w.1
            (IdeleGroup.principalIdele K (s : Kˣ)) := by
      apply Units.ext
      rfl
    simpa only [d, div_eq_mul_inv, map_mul, map_inv,
      huToField, hsToField] using hFieldPower
  refine ⟨d, hdSupported, hTpower, ?_⟩
  have hsOne : QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
      (IdeleGroup.principalIdele K (s : Kˣ)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨(s : Kˣ), rfl⟩
  simp only [d, map_mul, map_inv, hsOne, inv_one]
  exact mul_one (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) u)

open scoped Classical in
private theorem ideleClassNorm_range_eq_top_of_local_power_surjectivity
    {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsAbelianGalois K M]
    [(RelativeIdeleGroup.principalSubgroup K M).Normal]
    (n : ℕ+) (S' T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S' T)
    (hSurj : Function.Surjective (sUnitLocalUnitPowerMap (K := K) n S' T hST))
    (hLarge : IdeleGroup.supportedAt (K := K) (S' : Set (HeightOneSpectrum (𝓞 K))) ⊔
      IdeleGroup.principalSubgroup K = ⊤)
    (hSplitS : ∀ w : HeightOneSpectrum (𝓞 K), w ∈ S' →
      _root_.FinitePlaceSplitsCompletely (K := K) (L := M) w)
    (hInfiniteTop : ∀ w : InfinitePlace K,
      _root_.infiniteTensorNormSubgroup (K := K) (L := M) w = ⊤)
    (hAway : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S' ∪ T →
      _root_.ChosenFinitePlaceIsUnramified (K := K) (L := M) w)
    (hPower : ∀ w : HeightOneSpectrum (𝓞 K),
      (powMonoidHom (n : ℕ) : (w.adicCompletion K)ˣ →* (w.adicCompletion K)ˣ).range ≤
        _root_.chosenFinitePlaceLocalNormSubgroup (K := K) (L := M) w) :
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range = ⊤ := by
  classical
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
  obtain ⟨d, hdSupported, hTpower, hdClass⟩ :=
    exists_supported_idele_same_class_local_powers n S' T hST hSurj u hu
  have hInfinite :
      ∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w d ∈
          _root_.infiniteTensorNormSubgroup
            (K := K) (L := M) w := by
    intro w
    rw [hInfiniteTop w]
    exact Subgroup.mem_top _
  have hFinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        IdeleGroup.finiteComponent w d ∈
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
    · by_cases hwT : w ∈ T
      · exact hPower w (hTpower ⟨w, hwT⟩)
      · have hwAway : w ∉ S' ∪ T := by
          intro hw
          rcases Finset.mem_union.mp hw with hw | hw
          · exact hwS hw
          · exact hwT hw
        apply
          _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
            (K := K) (L := M) w (hAway w hwAway)
        exact
          (IdeleGroup.mem_supportedAt_iff
            (K := K)
            (S' : Set (HeightOneSpectrum (𝓞 K))) d).mp
              hdSupported w (by simpa using hwS)
  have hdNorm :
      d ∈ (RelativeIdeleGroup.norm K M).range :=
    (_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms
      (K := K) (L := M) d).2
        ⟨hInfinite, hFinite⟩
  obtain ⟨z, hz⟩ := hdNorm
  refine
    ⟨QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M) z, ?_⟩
  rw [RelativeIdeleGroup.Cohomology.ideleClassNorm_mk, hz]
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) d =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a
  have hqOne : QuotientGroup.mk' (IdeleGroup.principalSubgroup K) q = 1 :=
    (QuotientGroup.eq_one_iff q).mpr hq
  rw [hdClass, ← huq, map_mul, hqOne]
  exact (mul_one (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) u)).symm

private theorem unit_mem_power_range_of_ideleClassNorm_top
    {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsAbelianGalois K M]
    [(RelativeIdeleGroup.principalSubgroup K M).Normal] [IsCyclic Gal(M/K)]
    (n : ℕ+) (b : Kˣ) (beta : Mˣ)
    (hbeta : beta ^ (n : ℕ) = Units.map (algebraMap K M).toMonoidHom b)
    (hNormTop : (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range = ⊤) :
    b ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  classical
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
  obtain ⟨x, hx⟩ :=
    hAlgMap.2 (beta : M)
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    apply beta.ne_zero
    calc
      (beta : M) = algebraMap K M x := hx.symm
      _ = 0 := by rw [hx_zero, map_zero]
  let xUnit : Kˣ :=
    Units.mk0 x hx_ne
  apply
    (MonoidHom.mem_range
      (G := Kˣ)).mpr
  refine ⟨xUnit, ?_⟩
  rw [powMonoidHom_apply]
  apply Units.ext
  apply (algebraMap K M).injective
  change
    algebraMap K M (x ^ (n : ℕ)) =
      algebraMap K M (b : K)
  calc
    algebraMap K M (x ^ (n : ℕ)) =
        (beta : M) ^ (n : ℕ) := by
      rw [map_pow, hx]
    _ = algebraMap K M (b : K) := by
      simpa using congrArg Units.val hbeta

open scoped Classical in

open _root_.KummerTheory
  (chosenSimpleKummerExtension_infiniteTensorNormSubgroup_eq_top_of_mem_nthPowerSubgroup) in
/-- Equality between the power/local-unit subgroup and the everywhere-local
norm condition for the Kummer-selected prime set.  Starting from an arbitrary
prescribed finite set `S`, the construction first adjoins a sufficiently large
idelic support and the support of the exponent, then performs the chosen
finite Kummer-radical enlargement before choosing `T`. -/
theorem
    principalIdelePowerLocalUnitSubgroup_eq_sUnitNthPowersInField_sUnitKummerPrimeSet
    {K : Type} [Field K] [NumberField K]
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    let nUnit : Kˣ :=
      Units.mk0 ((n : ℕ) : K) hnK
    let S₀ :=
      (S ∪ IdeleGroup.sufficientlyLargeFiniteSet (K := K)) ∪
        chosenUnitFiniteSupport (K := K) nUnit
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S₀
    let T :=
      sUnitKummerPrimeSet
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S₀
    principalIdelePowerLocalUnitSubgroup (K := K) n S' T =
      sUnitNthPowersInField (K := K) n (S' ∪ T) := by
  classical
  dsimp only
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let nUnit : Kˣ :=
    Units.mk0 ((n : ℕ) : K) hnK
  let S₀ :=
    (S ∪ IdeleGroup.sufficientlyLargeFiniteSet (K := K)) ∪
      chosenUnitFiniteSupport (K := K) nUnit
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S₀
  let T :=
    sUnitKummerPrimeSet
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S₀
  let hST : Disjoint S' T :=
    (sUnitKummerPrimeSet_disjoint_enlargeByFiniteKummerRadicalSupport
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S₀).symm
  change
    principalIdelePowerLocalUnitSubgroup (K := K) n S' T =
      sUnitNthPowersInField (K := K) n (S' ∪ T)
  have hSurj :
      Function.Surjective
        (sUnitLocalUnitPowerMap (K := K) n S' T hST) := by
    simpa only [S', T, hST] using
      sUnitLocalUnitPowerMap_sUnitKummerPrimeSet_surjective
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S₀
  have hCanonical :
      (IdeleGroup.sufficientlyLargeFiniteSet (K := K) :
          Set (HeightOneSpectrum (𝓞 K))) ⊆
        (S₀ : Set (HeightOneSpectrum (𝓞 K))) := by
    intro w hw
    exact
      Finset.mem_union_left _
        (Finset.mem_union_right _ hw)
  have hS₀ :
      IdeleGroup.supportedAt
            (K := K) (S₀ : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤ := by
    apply top_unique
    rw [
      ← IdeleGroup.supportedAt_sup_principalSubgroup_eq_top
        (K := K)]
    exact
      sup_le_sup
        (IdeleGroup.supportedAt_mono
          (K := K) hCanonical)
        le_rfl
  have hLarge :
      IdeleGroup.supportedAt
            (K := K) (S' : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤ := by
    simpa only [S'] using
      supportedAt_sup_principalSubgroup_eq_top_of_enlargeByRadicalSupport
        (K := K) (L := E) n hmu S₀ hS₀
  apply le_antisymm
  · intro b hb
    have hbData :=
      (mem_idelePowerLocalUnitSubgroup_iff
        (K := K) n S' T
        (IdeleGroup.principalIdele K b)).mp hb
    have hbSUnit :
        b ∈ SUnitGroup (K := K) (S' ∪ T) :=
      principalIdelePowerLocalUnitSubgroup_le_sUnitGroup
        (K := K) n S' T hb
    let M :=
      KummerTheory.chosenSimpleKummerExtension K n hnK b
    let : FiniteDimensional K M :=
      KummerTheory.chosenSimpleKummerExtension_finiteDimensional
        K n hnK b
    let : IsAbelianGalois K M :=
      KummerTheory.chosenSimpleKummerExtension_isAbelianGalois
        K n hnK hmu b
    let : NumberField M :=
      NumberField.of_module_finite K M
    let : (RelativeIdeleGroup.principalSubgroup K M).Normal :=
      ⟨fun n hn g => by
        have hconj : g * n * g⁻¹ = n := by
          rw [mul_comm g n, mul_assoc, mul_inv_cancel, mul_one]
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
        ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S' ∪ T →
          _root_.ChosenFinitePlaceIsUnramified
            (K := K) (L := M) w := by
      intro w hw
      have hbVal :
          w.valuation K (b : K) = 1 :=
        (mem_SUnitGroup_iff
          (K := K) (S' ∪ T) b).mp hbSUnit w hw
      have hwS' : w ∉ S' := by
        intro hwS'
        exact hw (Finset.mem_union_left T hwS')
      have hwSupport :
          w ∉ chosenUnitFiniteSupport (K := K) nUnit := by
        intro hwSupport
        apply hwS'
        exact
          subset_enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S₀
            (Finset.mem_union_right _ hwSupport)
      have hnUnitVal :
          w.valuation K (nUnit : K) = 1 :=
        (mem_SUnitGroup_iff
          (K := K)
          (chosenUnitFiniteSupport (K := K) nUnit) nUnit).mp
            (mem_sUnitGroup_chosenUnitFiniteSupport
              (K := K) nUnit)
            w hwSupport
      have hnVal :
          w.valuation K ((n : ℕ) : K) = 1 := by
        change w.valuation K ((n : ℕ) : K) = 1 at hnUnitVal
        exact hnUnitVal
      simpa only [M] using
        KummerTheory.chosenSimpleKummerExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
          (K := K) n hnK hmu b w hbVal hnVal
    have hNormTop : (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range = ⊤ :=
      ideleClassNorm_range_eq_top_of_local_power_surjectivity
        n S' T hST hSurj hLarge hSplitS hInfiniteTop hAway
        (fun w => chosenSimpleKummerNthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup
          (K := K) n hnK hmu b w)
    let : IsCyclic (M ≃ₐ[K] M) := by
      simpa only [M] using
        KummerTheory.chosenSimpleKummerExtension_isCyclic
          K n hnK hmu b
    let beta : Mˣ :=
      KummerTheory.chosenSimpleKummerRootUnit K n hnK b
    have hbeta :
        beta ^ (n : ℕ) =
          Units.map (algebraMap K M).toMonoidHom b := by
      simpa only [M, beta] using
        KummerTheory.chosenSimpleKummerRootUnit_pow K n hnK b
    have hbPower := unit_mem_power_range_of_ideleClassNorm_top n b beta hbeta hNormTop
    exact
      (mem_sUnitNthPowersInField_iff
        (K := K) n (S' ∪ T) b).2
          ⟨hbSUnit, hbPower⟩
  · exact
      sUnitNthPowersInField_le_principalIdelePowerLocalUnitSubgroup
        (K := K) n S' T


end GlobalClassFieldTheory.ClassFieldAxiom
