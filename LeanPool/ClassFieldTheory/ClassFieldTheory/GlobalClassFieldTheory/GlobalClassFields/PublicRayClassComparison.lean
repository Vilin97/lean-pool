/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticRayClassFieldReciprocity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FullConductorRayClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayFrobeniusRigidity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassSubgroupPrimeArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Narrow
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsRayCongruent
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayPrincipalIdealSubgroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsUnramifiedOutsideModulus
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
public import Mathlib.Data.Finsupp.Order
/-!
# Conductors and ray class fields implementation

This module supplies the implementation proofs for the compact conductor and
ray-class-field statements in the parent `Theorems` directory.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory.GlobalClassFieldComparison

universe u

open scoped Classical in
/-- Interpret a public ray modulus in the existing idèle-theoretic ray-class
library, preserving both its finite exponents and selected real places. -/
def rayClassModulusToOriginal
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) : RayClass.Modulus K where
  finitePart := m.finitePart
  infinitePart := m.infinitePart

open scoped Classical in
/-- At a real place, positivity of a principal idele component is exactly
positivity of its field generator under the corresponding real embedding. -/
private theorem principalIdele_mem_infinitePositiveSubgroup_iff
    (K : Type u) [Field K] [NumberField K] (x : Kˣ)
    (v : {v : InfinitePlace K // v.IsReal}) :
    IdeleGroup.infiniteComponent v.1 (IdeleGroup.principalIdele K x) ∈
        RayClass.infinitePositiveSubgroup v.1 ↔
      0 < v.1.embedding_of_isReal v.2 (x : K) := by
  rw [RayClass.mem_infinitePositiveSubgroup_iff]
  have hcoe (hv : v.1.IsReal) :
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
          ((IdeleGroup.infiniteComponent v.1
              (IdeleGroup.principalIdele K x) : v.1.Completionˣ) :
            v.1.Completion) =
        v.1.embedding_of_isReal hv (x : K) := by
    rw [IdeleGroup.infiniteComponent_principalIdele,
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
    rfl
  constructor
  · intro h
    simpa only [hcoe] using h v.2
  · intro h hv
    simpa only [hcoe] using h

open scoped Classical in
/-- A principal idèle satisfies the existing prime-to-modulus condition
exactly when its generator satisfies the public ray congruence. -/
theorem principalIdele_mem_primeTo_iff_isRayCongruent
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (x : Kˣ) :
    IdeleGroup.principalIdele K x ∈
        RayClass.idelePrimeToModulusSubgroup
          (rayClassModulusToOriginal K m) ↔
      IsRayCongruent m x := by
  have hinfinite :
      (IdeleGroup.principalIdele K x).1 ∈
          (rayClassModulusToOriginal K m).infiniteCongruenceSubgroup ↔
        ∀ v : RayClassRealPlace K, v ∈ m.infinitePart →
          0 < v.1.embedding_of_isReal v.2 (x : K) := by
    rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
    exact ⟨fun h v hv =>
      (principalIdele_mem_infinitePositiveSubgroup_iff K x v).mp (h v hv),
      fun h v hv =>
        (principalIdele_mem_infinitePositiveSubgroup_iff K x v).mpr (h v hv)⟩
  have hfinite :
      (IdeleGroup.principalIdele K x).2 ∈
          RayClass.finitePrimeToModulusSubgroup
            (rayClassModulusToOriginal K m) ↔
        ∀ v, v ∈ m.finitePart.support →
          finitePlaceUnitEmbedding v x ∈
            rayLocalHigherUnitGroup v (m.finitePart v) := by
    change (∀ v, v ∈ m.finitePart.support →
      (IdeleGroup.principalIdele K x).2 v ∈
        RayClass.localHigherUnitGroup v (m.finitePart v)) ↔ _
    constructor
    · intro h v hv
      have h' := h v hv
      change finitePlaceUnitEmbedding v x ∈
        rayLocalHigherUnitGroup v (m.finitePart v) at h'
      exact h'
    · intro h v hv
      have h' := h v hv
      change (IdeleGroup.principalIdele K x).2 v ∈
        RayClass.localHigherUnitGroup v (m.finitePart v) at h'
      exact h'
  change ((IdeleGroup.principalIdele K x).1 ∈
      (rayClassModulusToOriginal K m).infiniteCongruenceSubgroup ∧
      (IdeleGroup.principalIdele K x).2 ∈
        RayClass.finitePrimeToModulusSubgroup
          (rayClassModulusToOriginal K m)) ↔ _
  exact ⟨fun h => ⟨hfinite.mp h.2, hinfinite.mp h.1⟩,
    fun h => ⟨hinfinite.mpr h.2, hfinite.mpr h.1⟩⟩

open scoped Classical in
/-- At narrow modulus zero, the older idele-theoretic prime-to condition on
a principal idele agrees with the public generator congruence. -/
theorem principalIdele_mem_narrowPrimeTo_iff_isRayCongruent
    (K : Type u) [Field K] [NumberField K] (x : Kˣ) :
    IdeleGroup.principalIdele K x ∈
        RayClass.idelePrimeToModulusSubgroup
          (RayClass.Modulus.narrowOfFinite (0 : RayClass.FiniteModulus K)) ↔
      IsRayCongruent (narrowRayClassModulus K) x := by
  change IdeleGroup.principalIdele K x ∈
      RayClass.idelePrimeToModulusSubgroup
        (rayClassModulusToOriginal K (narrowRayClassModulus K)) ↔
      IsRayCongruent (narrowRayClassModulus K) x
  exact principalIdele_mem_primeTo_iff_isRayCongruent K
    (narrowRayClassModulus K) x

open scoped Classical in
/-- The public ray-principal subgroup equals the existing ideal-theoretic
ray-principal subgroup for every finite and infinite modulus. -/
theorem rayPrincipalIdealSubgroup_eq
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) :
    rayPrincipalIdealSubgroupInPrimeTo m =
      RayClass.principalRayIdealSubgroup
        (rayClassModulusToOriginal K m) := by
  classical
  let m' := rayClassModulusToOriginal K m
  let P := rayClassPrimeToIdeals m
  let T : Subgroup (NumberFieldFractionalIdealGroup K) :=
    Subgroup.map P.subtype (RayClass.principalRayIdealSubgroup m')
  have hCarrier :
      {I : NumberFieldFractionalIdealGroup K |
        ∃ x : Kˣ,
          IsRayCongruent m x ∧
            toPrincipalIdeal (𝓞 K) K x = I} = (T : Set _) := by
    ext I
    constructor
    · rintro ⟨x, hx, hIx⟩
      have hi : IdeleGroup.principalIdele K x ∈
          RayClass.idelePrimeToModulusSubgroup m' :=
        (principalIdele_mem_primeTo_iff_isRayCongruent K m x).2 hx
      have hI : I ∈ P := by
        change I ∈ RayClass.primeToModulusIdeals m'
        rw [← hIx, ← IdeleGroup.fractionalIdeal_principalIdele]
        exact RayClass.fractionalIdeal_mem_primeToModulusIdeals
          m' (IdeleGroup.principalIdele K x) hi
      let J : P := ⟨I, hI⟩
      have hJ : J ∈ RayClass.principalRayIdealSubgroup m' :=
        (RayClass.mem_principalRayIdealSubgroup_iff m' J).2
          ⟨x, hi, hIx⟩
      exact ⟨J, hJ, rfl⟩
    · rintro ⟨J, hJ, hIJ⟩
      obtain ⟨x, hx, hEq⟩ :=
        (RayClass.mem_principalRayIdealSubgroup_iff m' J).1 hJ
      exact ⟨x,
        (principalIdele_mem_primeTo_iff_isRayCongruent K m x).1 hx,
        hEq.trans hIJ⟩
  have hUnrestricted : rayPrincipalIdealSubgroup m = T := by
    unfold rayPrincipalIdealSubgroup
    rw [hCarrier, Subgroup.closure_eq]
  apply Subgroup.ext
  intro I
  change (I : NumberFieldFractionalIdealGroup K) ∈
      rayPrincipalIdealSubgroup m ↔
    I ∈ RayClass.principalRayIdealSubgroup m'
  rw [hUnrestricted]
  constructor
  · rintro ⟨J, hJ, hIJ⟩
    have hJI : J = I := Subtype.ext hIJ
    exact hJI ▸ hJ
  · intro hI
    exact ⟨I, hI, rfl⟩

open scoped Classical in
/-- The zero-finite-part narrow case of the general principal-ideal
comparison. -/
theorem narrowRayPrincipalIdealSubgroup_eq
    (K : Type u) [Field K] [NumberField K] :
    rayPrincipalIdealSubgroupInPrimeTo (narrowRayClassModulus K) =
      RayClass.principalRayIdealSubgroup
        (RayClass.Modulus.narrowOfFinite (0 : RayClass.FiniteModulus K)) := by
  change rayPrincipalIdealSubgroupInPrimeTo (narrowRayClassModulus K) =
    RayClass.principalRayIdealSubgroup
      (rayClassModulusToOriginal K (narrowRayClassModulus K))
  exact rayPrincipalIdealSubgroup_eq K (narrowRayClassModulus K)

open scoped Classical in
/-- The public ideal-theoretic ray class group is the existing ideal ray
class group for the same modulus. -/
noncomputable def rayClassGroupEquivOriginal
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) :
    RayClassGroup m ≃*
      RayClass.IdealRayClassGroup (rayClassModulusToOriginal K m) := by
  let G := RayClass.primeToModulusIdeals (rayClassModulusToOriginal K m)
  let M : Subgroup G := rayPrincipalIdealSubgroupInPrimeTo m
  let N : Subgroup G :=
    RayClass.principalRayIdealSubgroup (rayClassModulusToOriginal K m)
  have hMN : M = N := rayPrincipalIdealSubgroup_eq K m
  let hComm : IsMulCommutative G :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (mul_comm a.1 b.1))
  have hM : M.Normal := @Subgroup.normal_of_isMulCommutative G _ hComm M
  have hN : N.Normal := @Subgroup.normal_of_isMulCommutative G _ hComm N
  exact @QuotientGroup.quotientMulEquivOfEq G _ M N hM hN hMN

open scoped Classical in
/-- The comparison preserves the class of each prime away from the
modulus. -/
theorem rayClassGroupEquivOriginal_prime
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    rayClassGroupEquivOriginal K m (rayClassOfFinitePrime m v hv) =
      QuotientGroup.mk'
        (RayClass.principalRayIdealSubgroup (rayClassModulusToOriginal K m))
        (RayClass.primeToModulusIdeal
          (rayClassModulusToOriginal K m) v hv) := by
  let G := RayClass.primeToModulusIdeals (rayClassModulusToOriginal K m)
  let M : Subgroup G := rayPrincipalIdealSubgroupInPrimeTo m
  let N : Subgroup G :=
    RayClass.principalRayIdealSubgroup (rayClassModulusToOriginal K m)
  have hMN : M = N := rayPrincipalIdealSubgroup_eq K m
  let hComm : IsMulCommutative G :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (mul_comm a.1 b.1))
  have hM : M.Normal := @Subgroup.normal_of_isMulCommutative G _ hComm M
  have hN : N.Normal := @Subgroup.normal_of_isMulCommutative G _ hComm N
  change (@QuotientGroup.quotientMulEquivOfEq G _ M N hM hN hMN)
      (QuotientGroup.mk' M
        (⟨finitePrimeFractionalIdeal v, by
          intro w hw
          exact FractionalIdeal.count_maximal_coprime K w
            (fun h => (h ▸ hv) hw)⟩ : G)) =
      QuotientGroup.mk' N
        (RayClass.primeToModulusIdeal
          (rayClassModulusToOriginal K m) v hv)
  rfl

open scoped Classical in
/-- Compare the public ideal ray class group directly with the original
idèle-class ray class group.  This is the composite of the ideal comparison
above and the original idelic-to-ideal equivalence. -/
noncomputable def rayClassGroupEquivOriginalIdele
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) :
    RayClassGroup m ≃*
      RayClass.RayClassGroup (rayClassModulusToOriginal K m) :=
  (rayClassGroupEquivOriginal K m).trans
    (RayClass.rayClassGroupEquivIdealRayClassGroup
      (rayClassModulusToOriginal K m)).symm

open scoped Classical in
open GlobalClassFieldTheory.GlobalClassFields renaming
  finitePrimeIdele_mem_idelePrimeToModulusSubgroup →
    finitePrimeIdele_mem_idelePrimeToModulusSubgroup in
/-- A public prime ray class corresponds to the original normalized prime
idèle class, with the same finite and infinite modulus. -/
theorem rayClassGroupEquivOriginalIdele_prime
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    rayClassGroupEquivOriginalIdele K m (rayClassOfFinitePrime m v hv) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup (rayClassModulusToOriginal K m))
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
          (IdeleGroup.finitePrimeIdele v)) := by
  let m' := rayClassModulusToOriginal K m
  have hv' : v ∉ m'.finitePart.support := hv
  let a : RayClass.idelePrimeToModulusSubgroup m' :=
    ⟨IdeleGroup.finitePrimeIdele v,
      finitePrimeIdele_mem_idelePrimeToModulusSubgroup
        m' v hv'⟩
  let e := RayClass.rayClassGroupEquivIdealRayClassGroup m'
  apply e.injective
  calc
    e (rayClassGroupEquivOriginalIdele K m (rayClassOfFinitePrime m v hv)) =
        rayClassGroupEquivOriginal K m (rayClassOfFinitePrime m v hv) := by
      change e (e.symm (rayClassGroupEquivOriginal K m
        (rayClassOfFinitePrime m v hv))) = _
      exact e.apply_symm_apply _
    _ = QuotientGroup.mk'
          (RayClass.principalRayIdealSubgroup m')
          (RayClass.primeToModulusIdeal m' v hv) :=
      rayClassGroupEquivOriginal_prime K m v hv
    _ = RayClass.idealRayProjection m' a := by
      change QuotientGroup.mk'
          (RayClass.principalRayIdealSubgroup m')
          (RayClass.primeToModulusIdeal m' v hv') =
        RayClass.idealRayProjection m'
          ⟨IdeleGroup.finitePrimeIdele v,
            finitePrimeIdele_mem_idelePrimeToModulusSubgroup
              m' v hv'⟩
      exact (GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele
        m' v hv').symm
    _ = e (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m')
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) (a : IdeleGroup K))) := by
      exact
        (GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo
        m' a).symm

open scoped Classical in
/-- The public ideal-theoretic narrow ray class group agrees with the
existing narrow class group used by global class field theory. -/
noncomputable def narrowRayClassGroupEquivNarrowClassGroup
    (K : Type) [Field K] [NumberField K] :
    RayClassGroup (narrowRayClassModulus K) ≃*
      RayClass.NarrowClassGroup K := by
  let m : RayClass.Modulus K := RayClass.Modulus.narrowOfFinite 0
  let e₀ : RayClassGroup (narrowRayClassModulus K) ≃*
      RayClass.IdealRayClassGroup m := by
    exact rayClassGroupEquivOriginal K (narrowRayClassModulus K)
  exact e₀.trans
    ((RayClass.rayClassGroupEquivIdealRayClassGroup m).symm.trans
      (RayClass.rayClassGroupNarrowZeroEquivNarrowClassGroup (K := K)))

open scoped Classical in
/-- The norm subgroup of the selected ray class field is the ray
congruence subgroup. -/
theorem rayClassField_normSubgroup
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) :
    (_root_.ideleClassNorm K
      (GlobalClassFieldTheory.GlobalClassFields.rayClassField K m)).range =
      RayClass.Modulus.congruenceSubgroup m :=
  GlobalClassFieldTheory.GlobalClassFields.rayClassField_ideleClassNorm_range_over_original m

open scoped Classical in
open GlobalClassFieldTheory.GlobalClassFields renaming
  ideleClassNorm_narrowFiniteConductor_support_eq_ramifiedBaseFinitePlaces →
    ideleClassNorm_conductor_support_eq_ramifiedPlaces in
open GlobalClassFieldTheory.GlobalClassFields renaming
  ideleClassNormFullConductor_infinitePart_eq_realRamificationLocus →
    ideleClassNormFullConductor_infinitePart_eq_realRamificationLocus in
/-- Any finite abelian extension whose norm group contains the ray
congruence subgroup is unramified outside that modulus. -/
theorem unramifiedOutsideModulus_of_definingModulus
    (K E : Type) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (m : RayClassModulus K)
    (hm : RayClass.Modulus.congruenceSubgroup
        (rayClassModulusToOriginal K m) ≤
          (_root_.ideleClassNorm K E).range) :
    IsUnramifiedOutsideModulus K E m := by
  classical
  let m' := rayClassModulusToOriginal K m
  let H :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
      (K := K) (L := E)
  have hDefining : GlobalClassFieldTheory.GlobalClassFields.IsDefiningModulus H.1 m' := by
    change m'.congruenceSubgroup ≤ (_root_.ideleClassNorm K E).range
    exact hm
  have hfinite := H.narrowFiniteConductor_le hDefining
  have hinfinite := H.fullConductorInfinitePart_subset_of_isDefiningModulus hDefining
  have hfiniteSupport :=
    ideleClassNorm_conductor_support_eq_ramifiedPlaces
      (K := K) (L := E)
  have hinfiniteSupport :=
    ideleClassNormFullConductor_infinitePart_eq_realRamificationLocus
      (K := K) (L := E)
  constructor
  · intro v hv Q hQ hlie
    by_contra hram
    have hQne : Q ≠ ⊥ := by
      intro hbot
      have hunder := hlie.over
      rw [hbot, Ideal.under_bot] at hunder
      exact v.ne_bot hunder
    let w : HeightOneSpectrum (𝓞 E) := ⟨Q, hQ, hQne⟩
    have hvram : v ∈ _root_.ramifiedBaseFinitePlaces (K := K) (L := E) := by
      rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
      exact ⟨w, hlie, hram⟩
    have hvcond : v ∈
        (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormNarrowFiniteConductor
          (K := K) (L := E)).support := by
      rw [hfiniteSupport]
      exact hvram
    apply hv
    change v ∈ m'.finitePart.support
    exact (Finsupp.support_mono hfinite) hvcond
  · intro v hv hnot
    by_contra hram
    have hvcond : (⟨v, hv⟩ : RayClass.RealPlace K) ∈
        H.fullConductorInfinitePart := by
      change (⟨v, hv⟩ : RayClass.RealPlace K) ∈ H.fullConductor.infinitePart
      rw [hinfiniteSupport]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hram⟩
    exact hnot (hinfinite hvcond)

open scoped Classical in
/-- The selected ray class field is unramified away from the finite and real
places selected by the public modulus. -/
theorem rayClassField_unramifiedOutsideModulus
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K) :
    IsUnramifiedOutsideModulus K
      (GlobalClassFieldTheory.GlobalClassFields.rayClassField K
        (rayClassModulusToOriginal K m)) m := by
  let m' := rayClassModulusToOriginal K m
  let E := GlobalClassFieldTheory.GlobalClassFields.rayClassField K m'
  have hnorm : (_root_.ideleClassNorm K E).range = m'.congruenceSubgroup :=
    GlobalClassFieldTheory.GlobalClassFields.rayClassField_ideleClassNorm_range_over_original m'
  exact unramifiedOutsideModulus_of_definingModulus K E m (le_of_eq hnorm.symm)

open scoped Classical in
/-- Ray class reciprocity identifies the Galois group of the selected ray
class field with the corresponding ray class group. -/
theorem rayClassField_reciprocity
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) :
    Nonempty
      ((GlobalClassFieldTheory.GlobalClassFields.rayClassField K m ≃ₐ[K]
          GlobalClassFieldTheory.GlobalClassFields.rayClassField K m) ≃*
        RayClass.RayClassGroup m) :=
  ⟨GlobalClassFieldTheory.GlobalClassFields.rayClassFieldGaloisEquivRayClassGroup m⟩

open scoped Classical in
/-- The selected ray class field has degree equal to the order of its ray
class group. -/
theorem rayClassField_degree
    (K : Type) [Field K] [NumberField K]
    (m : RayClass.Modulus K) :
    Module.finrank K
        (GlobalClassFieldTheory.GlobalClassFields.rayClassField K m) =
      Nat.card (RayClass.RayClassGroup m) :=
  GlobalClassFieldTheory.GlobalClassFields.rayClassField_finrank_eq_rayClassGroup_card m

open scoped Classical in
/-- The full conductor is the least modulus whose ray class field contains
the given finite abelian extension. -/
theorem embedsInRayClassField_iff_conductor_le
    {K : Type} [Field K] [NumberField K]
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]
    (m : RayClass.Modulus K) :
    Nonempty
        (L →ₐ[K]
          GlobalClassFieldTheory.GlobalClassFields.rayClassField K m) ↔
      (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
          (K := K) (L := L)).fullConductor ≤ m :=
  GlobalClassFieldTheory.GlobalClassFields.nonempty_algHom_to_rayClassField_iff_fullConductor_le L m

open scoped Classical in
/-- Build the public Frobenius-normalized realization attached to a ray-class subgroup. -/
theorem rayClassSubgroup_existence
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m)) :
    Nonempty (RayClassSubgroupRealization K m H) := by
  let m' := rayClassModulusToOriginal K m
  let e := rayClassGroupEquivOriginalIdele K m
  let H' : Subgroup (RayClass.RayClassGroup m') := H.map e.toMonoidHom
  let E :=
    GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupSubextension
      (K := K) m' H'
  let artin : RayClassGroup m →* (E ≃ₐ[K] E) :=
    (GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupArtin
      (K := K) m' H').comp e.toMonoidHom
  let hram : IsUnramifiedOutsideModulus K E m :=
    unramifiedOutsideModulus_of_definingModulus K E m
      (GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupSubextension_norm_range
        (K := K) m' H')
  refine ⟨{
    extension := E
    unramifiedOutsideModulus := hram
    artin := artin
    artin_surjective := ?_
    artin_ker := ?_
    artin_frobenius := ?_
  }⟩
  · exact
      (GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupArtin_surjective
        (K := K) m' H').comp e.surjective
  · ext x
    change e x ∈
      (GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupArtin
        (K := K) m' H').ker ↔ x ∈ H
    rw [GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupArtin_ker]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (e.injective hxy) ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  · intro v hv w hw
    calc
      artin (rayClassOfFinitePrime m v hv) =
          GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupArtin
            (K := K) m' H'
            (QuotientGroup.mk' m'.congruenceSubgroup
              (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
                (IdeleGroup.finitePrimeIdele v))) := by
        change GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupArtin
          (K := K) m' H'
          (e (rayClassOfFinitePrime m v hv)) = _
        rw [rayClassGroupEquivOriginalIdele_prime K m v hv]
      _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
            (K := K) (L := E) v :=
        GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupArtin_finitePrimeIdele
          (K := K) m' H' v
      _ = arithmeticFrobeniusAt (K := K) w :=
        arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
          (K := K) (L := E) v w hw (hram.1 v hv w.asIdeal inferInstance hw)

end ClassFieldTheory.GlobalClassFieldComparison

namespace ClassFieldTheory

open scoped Classical in
open GlobalClassFieldTheory.GlobalClassFields renaming
  rayModulus_normSubgroup_eq_of_arithmeticPrimeArtinEquiv →
    rayModulus_normSubgroup_eq_of_arithmeticPrimeArtinEquiv in
open GlobalClassFieldTheory.GlobalClassFields renaming
  finiteAbelianExtension_nonempty_algHom_of_normRange_le →
    finiteAbelianExtension_nonempty_algHom_of_normRange_le in
/-- The concrete full norm conductor is the least public modulus whose ray
class field contains the finite abelian extension. This implementation theorem
uses the original idelic full conductor in its statement. -/
theorem normFullConductor_isAbelianConductor
    (K : Type) [Field K] [NumberField K]
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] :
    IsAbelianConductor K L
      { finitePart :=
          (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
            (K := K) (L := L)).fullConductor.finitePart
        infinitePart :=
          (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
            (K := K) (L := L)).fullConductor.infinitePart } := by
  let H := GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
    (K := K) (L := L)
  let c : RayClassModulus K :=
    { finitePart := H.fullConductor.finitePart
      infinitePart := H.fullConductor.infinitePart }
  intro m
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  have hnorm (R : RayClassFieldRealization K m) :
      (_root_.ideleClassNorm K R.extension).range = m'.congruenceSubgroup := by
    let E := R.extension
    let r : RayClassGroup m ≃* (E ≃ₐ[K] E) := R.artinEquiv
    let e : RayClass.RayClassGroup m' ≃* (E ≃ₐ[K] E) :=
      (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm.trans r
    apply
      rayModulus_normSubgroup_eq_of_arithmeticPrimeArtinEquiv
      m' e
    intro v hv
    have hvm : v ∉ m.finitePart.support := hv
    let w₀ := _root_.chosenFinitePlaceExtension (L := E) v
    let w := _root_.finitePlaceExtensionCentre (K := K) (L := E) v w₀
    have hw : w.asIdeal.LiesOver v.asIdeal :=
      _root_.finitePlaceExtensionCentre_liesOver (K := K) (L := E) v w₀
    have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
      (R.unramifiedOutsideModulus.1 v hvm) w.asIdeal inferInstance hw
    calc
      e (QuotientGroup.mk' m'.congruenceSubgroup
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
            (IdeleGroup.finitePrimeIdele v))) =
          R.artinEquiv (rayClassOfFinitePrime m v hvm) := by
        change R.artinEquiv
          ((GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm
            (QuotientGroup.mk' m'.congruenceSubgroup
              (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
                (IdeleGroup.finitePrimeIdele v)))) = _
        rw [← GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime K m v hvm]
        exact congrArg R.artinEquiv
          ((GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm_apply_apply _)
      _ = arithmeticFrobeniusAt (K := K) w :=
        R.artin_frobenius v hvm w hw
      _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
            (K := K) (L := E) v :=
        (GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
          (K := K) (L := E) v w hw hunram).symm
  change EmbedsInRayClassField K L m ↔ c ≤ m
  constructor
  · rintro ⟨R, ⟨f⟩⟩
    have hR := hnorm R
    have hnormLE :
        (_root_.ideleClassNorm K R.extension).range ≤
          (_root_.ideleClassNorm K L).range :=
      GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_range_le_of_algHom
        (K := K) L R.extension f
    have hdef : m'.congruenceSubgroup ≤
        (_root_.ideleClassNorm K L).range := by
      rw [← hR]
      exact hnormLE
    have hc : H.fullConductor ≤ m' :=
      (H.isDefiningModulus_iff_fullConductor_le m').mp hdef
    exact hc
  · intro hc
    obtain ⟨S⟩ := GlobalClassFieldComparison.rayClassSubgroup_existence K m ⊥
    have hinj : Function.Injective S.artin :=
      (MonoidHom.ker_eq_bot_iff S.artin).mp S.artin_ker
    let e : RayClassGroup m ≃* (S.extension ≃ₐ[K] S.extension) :=
      MulEquiv.ofBijective S.artin ⟨hinj, S.artin_surjective⟩
    let R : RayClassFieldRealization K m :=
      { extension := S.extension
        unramifiedOutsideModulus := S.unramifiedOutsideModulus
        artinEquiv := e
        artin_frobenius := by
          intro v hv w hlie
          exact S.artin_frobenius v hv w hlie }
    have hR := hnorm R
    have hc' : H.fullConductor ≤ m' := hc
    have hdef : m'.congruenceSubgroup ≤
        (_root_.ideleClassNorm K L).range :=
      (H.isDefiningModulus_iff_fullConductor_le m').mpr hc'
    have hnormLE :
        (_root_.ideleClassNorm K R.extension).range ≤
          (_root_.ideleClassNorm K L).range := by
      rw [hR]
      exact hdef
    exact ⟨R,
      finiteAbelianExtension_nonempty_algHom_of_normRange_le
        (K := K) L R.extension hnormLE⟩

end ClassFieldTheory
