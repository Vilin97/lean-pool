/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.ArchimedeanPowerIndex
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.LocalResidueArithmetic
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlacePowerIndex
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.NormContainment
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.SupportedIdeleIndex
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.SupportedPrincipalQuotient
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.PrimePowerKummerIndex
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Principal
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.BaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.CyclotomicPrimeBaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.CyclicPrimeDegreeSubextension
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleClassHerbrandSupportedFinal
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.PrimeOrderFixedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.CohomologyBridge
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Hilbert90
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
/-!
# The global class-field axiom

This file proves the cyclic idele-class norm-index formula.  The first
input is the `H⁻¹` calculation for the principal-idele term in

`1 → Lˣ → I_L → C_L → 1`.

For a cyclic extension this term vanishes by Hilbert 90.  The result below
is transported through the actual low-degree Tate comparison and then
through the equivariant identification of `Lˣ` with the subgroup of
principal relative ideles.
-/

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

/-- Every degree-zero Tate class is annihilated by the order of the
acting group.  For a fixed representative `a`, its group norm is
`a ^ |G|`.  This exponent observation drives the prime-degree descent
step. -/
theorem herbrandH0_pow_card_eq_one
    {G A : Type}
    [Group G] [Fintype G]
    [CommGroup A] [MulDistribMulAction G A]
    (q : HerbrandH0 G A) :
    q ^ Fintype.card G = 1 := by
  refine HerbrandH0.inductionOn
    (motive := fun q : HerbrandH0 G A =>
      q ^ Fintype.card G = 1)
    q ?_
  intro a
  rw [← map_pow, HerbrandH0.mk_eq_one_iff]
  refine ⟨(a : A), ?_⟩
  change (∏ g : G, g • (a : A)) =
    (a : A) ^ Fintype.card G
  calc
    (∏ g : G, g • (a : A)) =
        ∏ _g : G, (a : A) := by
      apply Finset.prod_congr rfl
      intro g _hg
      exact a.property g
    _ = (a : A) ^ Fintype.card G := by
      rw [Finset.prod_const, Finset.card_univ]

/-- Specialization of the exponent calculation to the actual relative
idele class group. -/
theorem ideleClassHerbrandH0_pow_finrank_eq_one
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q :
      letI :=
        RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
      HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L)) :
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    q ^ Module.finrank K L = 1 := by
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  rw [← IsGalois.card_aut_eq_finrank,
    Nat.card_eq_fintype_card]
  exact herbrandH0_pow_card_eq_one q

section NormQuotientCommutativity

local instance cyclicNormBase_isMulCommutative
    (A : Type) [Field A] [NumberField A] :
    IsMulCommutative (IdeleClassGroup A) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The concrete class-norm quotient `C_K / N C_L` has exponent dividing
`[L:K]`. -/
theorem ideleClassNormQuotient_pow_finrank_eq_one
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) :
    q ^ Module.finrank K L = 1 := by
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  let e :=
    RelativeIdeleGroup.Cohomology.ideleClassHerbrandH0EquivNormQuotient K L
  have h :=
    ideleClassHerbrandH0_pow_finrank_eq_one K L (e.symm q)
  simpa only [map_pow, e.apply_symm_apply, map_one] using
    congrArg e h

/-- If a commutative group has exponent dividing `p`, then every
`d`-power map with `d` coprime to `p` is injective.  In the prime-degree
argument, `p` is the extension degree and `d` is the roots-of-unity
base-change degree. -/
theorem pow_injective_of_exponent_of_coprime
    {A : Type} [CommGroup A]
    (p d : ℕ)
    (hexponent : ∀ x : A, x ^ p = 1)
    (hcoprime : d.Coprime p) :
    Function.Injective (fun x : A => x ^ d) := by
  intro x y hxy
  change x ^ d = y ^ d at hxy
  have hdpow : (x * y⁻¹) ^ d = 1 := by
    calc
      (x * y⁻¹) ^ d = x ^ d * (y ^ d)⁻¹ := by
        rw [mul_pow, inv_pow]
      _ = 1 := by rw [hxy, mul_inv_cancel]
  have horder_d : orderOf (x * y⁻¹) ∣ d :=
    orderOf_dvd_of_pow_eq_one hdpow
  have horder_p : orderOf (x * y⁻¹) ∣ p :=
    orderOf_dvd_of_pow_eq_one (hexponent (x * y⁻¹))
  have horder_gcd :
      orderOf (x * y⁻¹) ∣ Nat.gcd d p :=
    Nat.dvd_gcd horder_d horder_p
  rw [hcoprime.gcd_eq_one] at horder_gcd
  have hxy_one : x * y⁻¹ = 1 :=
    orderOf_eq_one_iff.mp (Nat.dvd_one.mp horder_gcd)
  exact mul_inv_eq_one.mp hxy_one

/-- On the actual class-norm quotient, every power coprime to the
extension degree is injective. -/
theorem ideleClassNormQuotient_pow_injective_of_coprime
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (d : ℕ)
    (hd : d.Coprime (Module.finrank K L)) :
    Function.Injective
      (fun q : RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L => q ^ d) := by
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  let e :=
    RelativeIdeleGroup.Cohomology.ideleClassHerbrandH0EquivNormQuotient K L
  have hpow :
      Function.Injective
        (fun x : HerbrandH0 (L ≃ₐ[K] L) (RelativeIdeleGroup.ClassGroup K L) =>
          x ^ d) :=
    pow_injective_of_exponent_of_coprime
      (A := HerbrandH0 (L ≃ₐ[K] L) (RelativeIdeleGroup.ClassGroup K L))
      (Module.finrank K L) d
      (ideleClassHerbrandH0_pow_finrank_eq_one K L) hd
  intro x y hxy
  apply e.symm.injective
  apply hpow
  exact
    ((map_pow e.symm x d).symm.trans (congrArg e.symm hxy)).trans
      (map_pow e.symm y d)

/-- Source-producing form of the roots-of-unity base-change step.  For a
pushout square `N = M ⊗[K] L`, if `[M:K]` is coprime
to `[L:K]`, the induced map

`C_K / N_{L/K}C_L → C_M / N_{N/M}C_N`

is injective.  The target is expressed in the fixed-bottom-field tower
model, so no unproved identification `𝔸_K ⊗_K M ≃ 𝔸_M` is assumed. -/
theorem pushoutNormQuotientMap_injective_of_coprime
    (K M L N : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K L]
    [Algebra M N] [Algebra L N] [Algebra K N]
    [IsScalarTower K M N] [IsScalarTower K L N]
    [Algebra.IsPushout K M L N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N]
    [IsGalois K L]
    (hcoprime :
      (Module.finrank K M).Coprime
        (Module.finrank K L)) :
    Function.Injective
      (pushoutNormQuotientMap K M L N) :=
  pushoutNormQuotientMap_injective_of_pow_injective
    K M L N
    (ideleClassNormQuotient_pow_injective_of_coprime
      K L (Module.finrank K M) hcoprime)

section IntermediateNormQuotientCommutativity

local instance cyclicNormRelative_isMulCommutative
    (A B : Type) [Field A] [NumberField A] [Field B] [Algebra A B] :
    IsMulCommutative (RelativeIdeleGroup.ClassGroup A B) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The pushout map with its target changed from the fixed-bottom tower
presentation to the actual norm quotient `C_M / N_{N/M} C_N`.

Only the Galois hypothesis on the auxiliary extension `M/K` is needed
for this last comparison. -/
noncomputable def actualPushoutNormQuotientMap
    (K M L N : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K L]
    [Algebra M N] [Algebra L N] [Algebra K N]
    [IsScalarTower K M N] [IsScalarTower K L N]
    [Algebra.IsPushout K M L N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N]
    [IsGalois K M] :
    RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L →
      RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M N :=
  fun q =>
    intermediateClassNormQuotientBaseChangeMulEquiv
      K M N (pushoutNormQuotientMap K M L N q)

/-- The actual pushout norm-quotient map sends a quotient representative
to the corresponding base-changed representative. -/
@[simp]
theorem actualPushoutNormQuotientMap_mk
    (K M L N : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K L]
    [Algebra M N] [Algebra L N] [Algebra K N]
    [IsScalarTower K M N] [IsScalarTower K L N]
    [Algebra.IsPushout K M L N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N]
    [IsGalois K M]
    (c : IdeleClassGroup K) :
    actualPushoutNormQuotientMap K M L N
        (QuotientGroup.mk'
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range c) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.Cohomology.ideleClassNorm M N).range
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M)
          (RelativeIdeleGroup.classInclusion K M c)) := by
  change
    intermediateClassNormQuotientBaseChangeMulEquiv
        K M N
        (pushoutNormQuotientMap K M L N
          (QuotientGroup.mk'
            (RelativeIdeleGroup.classNorm K L).range c)) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.classNorm M N).range
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M)
          (RelativeIdeleGroup.classInclusion K M c))
  rw [pushoutNormQuotientMap_mk,
    intermediateClassNormQuotientBaseChangeMulEquiv_mk]

/-- Actual-target form of the injective roots-of-unity base-change
step. -/
theorem actualPushoutNormQuotientMap_injective_of_coprime
    (K M L N : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K L]
    [Algebra M N] [Algebra L N] [Algebra K N]
    [IsScalarTower K M N] [IsScalarTower K L N]
    [Algebra.IsPushout K M L N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N]
    [IsGalois K L] [IsGalois K M]
    (hcoprime :
      (Module.finrank K M).Coprime
        (Module.finrank K L)) :
    Function.Injective
      (actualPushoutNormQuotientMap K M L N) := by
  intro x y hxy
  apply
    pushoutNormQuotientMap_injective_of_coprime
      K M L N hcoprime
  apply
    (intermediateClassNormQuotientBaseChangeMulEquiv K M N).injective
  exact hxy

/-- Cardinal consequence with the actual `N/M` norm quotient as
target. -/
theorem ideleClassNormQuotient_card_le_actualPushout
    (K M L N : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K L]
    [Algebra M N] [Algebra L N] [Algebra K N]
    [IsScalarTower K M N] [IsScalarTower K L N]
    [Algebra.IsPushout K M L N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N]
    [IsGalois K L] [IsGalois K M]
    [Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M N)]
    (hcoprime :
      (Module.finrank K M).Coprime
        (Module.finrank K L)) :
    Nat.card (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) ≤
      Nat.card (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M N) :=
  Nat.card_le_card_of_injective
    (actualPushoutNormQuotientMap K M L N)
    (actualPushoutNormQuotientMap_injective_of_coprime
      K M L N hcoprime)

/-- Prime-degree upper bound.  After adjoining the `p`-th roots of unity,
the prime-power Kummer calculation gives norm index `p` for the concrete
cyclotomic pushout.  Coprimality of the cyclotomic degree then makes the
actual pushout map on norm quotients injective. -/
theorem ideleClassNorm_index_le_prime_of_finrank_eq
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index ≤ p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let M := KummerTheory.PrimeCyclotomicBase K p
  let N := KummerTheory.PrimeCyclotomicPushout K L p
  let : Field N :=
    KummerTheory.primeCyclotomicPushoutField
      K L p hp hdegree
  let : Algebra L N :=
    Algebra.TensorProduct.rightAlgebra
  let : Algebra M N :=
    KummerTheory.primeCyclotomicPushoutAlgebra
      K L p hp hdegree
  let : FiniteDimensional M N :=
    Module.Finite.of_restrictScalars_finite K M N
  let : FiniteDimensional L N :=
    Module.Finite.of_restrictScalars_finite K L N
  let : NumberField N :=
    KummerTheory.primeCyclotomicPushout_numberField
      K L p hp hdegree
  let : IsGalois M N :=
    KummerTheory.primeCyclotomicPushout_isGalois
      K L p hp hdegree
  let n : ℕ+ := ⟨p, hp.pos⟩
  have hTargetIndex :
      (RelativeIdeleGroup.Cohomology.ideleClassNorm M N).range.index = p := by
    calc
      (RelativeIdeleGroup.Cohomology.ideleClassNorm M N).range.index =
          Module.finrank M N := by
        simpa only [M, N, n] using
          (ideleClassNorm_index_eq_finrank_primePowerKummer
            (K := M) (E := N) n
            (KummerTheory.primeCyclotomicBase_primitiveRoots_nonempty
              (K := K) p hp)
            p 1 hp (by omega) (by simp [n])
            (KummerTheory.primeCyclotomicPushoutGalEquivPiZMod
              K L p hp hdegree))
      _ = p :=
        KummerTheory.primeCyclotomicPushout_finrank
          K L p hp hdegree
  have hTargetCard :
      Nat.card
          (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M N) =
        p := by
    rw [← Subgroup.index_eq_card]
    exact hTargetIndex
  let :
      Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M N) :=
    Nat.finite_of_card_ne_zero (by
      rw [hTargetCard]
      exact hp.ne_zero)
  rw [Subgroup.index_eq_card]
  calc
    Nat.card (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) ≤
        Nat.card
          (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M N) :=
      ideleClassNormQuotient_card_le_actualPushout
        K M L N
        (KummerTheory.primeCyclotomicBase_finrank_coprime
          (K := K) (L := L) p hp hdegree)
    _ = p := hTargetCard

/-- Actual tower form of the cardinal bound:

`#(C_K / N_{L/K}C_L) ≤
  #(C_M / N_{L/M}C_L) · #(C_K / N_{M/K}C_M)`. -/
theorem ideleClassNormQuotient_card_le_actual_tower_mul
    (K M L : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [IsGalois K M]
    [Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L)]
    [Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M)] :
    Nat.card (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) ≤
      Nat.card (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L) *
        Nat.card (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M) := by
  let : Finite (RelativeIdeleGroup.ClassNormQuotient M L) := by
    change
      Finite
        (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L)
    infer_instance
  let : Finite (RelativeIdeleGroup.ClassNormQuotient K M) := by
    change
      Finite
        (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M)
    infer_instance
  change
    Nat.card (RelativeIdeleGroup.ClassNormQuotient K L) ≤
      Nat.card (RelativeIdeleGroup.ClassNormQuotient M L) *
        Nat.card (RelativeIdeleGroup.ClassNormQuotient K M)
  let e :=
    intermediateClassNormQuotientBaseChangeMulEquiv
      K M L
  let :
      Finite
        (IntermediateClassNormQuotient K M L) :=
    Finite.of_injective e e.injective
  calc
    Nat.card (RelativeIdeleGroup.ClassNormQuotient K L) ≤
        Nat.card
            (IntermediateClassNormQuotient K M L) *
          Nat.card
            (RelativeIdeleGroup.ClassNormQuotient K M) :=
      ideleClassNormQuotient_card_le_mul K M L
    _ =
        Nat.card (RelativeIdeleGroup.ClassNormQuotient M L) *
          Nat.card
            (RelativeIdeleGroup.ClassNormQuotient K M) := by
      rw [Nat.card_congr e.toEquiv]

end IntermediateNormQuotientCommutativity

/-- Relative-coordinate source for the norm-index calculation. -/
theorem relativeIdeleClassNorm_index_eq_finrank_cyclic
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index =
      Module.finrank K L := by
  classical
  induction hfinrank : Module.finrank K L using
      Nat.strong_induction_on generalizing K L with
  | h degree ih =>
    by_cases hdegreeOne : Module.finrank K L = 1
    · have hsurjective :
          Function.Surjective
            (RelativeIdeleGroup.Cohomology.ideleClassNorm K L) := by
        intro c
        refine
          ⟨RelativeIdeleGroup.classInclusion K L c, ?_⟩
        calc
          RelativeIdeleGroup.Cohomology.ideleClassNorm K L
                (RelativeIdeleGroup.classInclusion K L c) =
              c ^ Module.finrank K L :=
            ideleClassNorm_classInclusion K L c
          _ = c := by rw [hdegreeOne, pow_one]
      have hRange :
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range = ⊤ :=
        MonoidHom.range_eq_top.mpr hsurjective
      rw [hRange, Subgroup.index_top, ← hfinrank, hdegreeOne]
    · have hdegreeLarge :
          1 < Module.finrank K L := by
        have hpositive : 0 < Module.finrank K L :=
          Module.finrank_pos
        omega
      let p :=
        cyclicDegreePrime
          (K := K) (L := L) hdegreeLarge
      let M :=
        cyclicPrimeDegreeIntermediate
          (K := K) (L := L) hdegreeLarge
      let : IsGalois K M :=
        cyclicPrimeDegreeIntermediate_isGalois
          (K := K) (L := L) hdegreeLarge
      let : IsGalois M L :=
        cyclicPrimeDegreeIntermediate_top_isGalois
          (K := K) (L := L) hdegreeLarge
      let : IsCyclic (M ≃ₐ[K] M) :=
        cyclicPrimeDegreeIntermediate_base_isCyclic
          (K := K) (L := L) hdegreeLarge
      let : IsCyclic (L ≃ₐ[M] L) :=
        cyclicPrimeDegreeIntermediate_top_isCyclic
          (K := K) (L := L) hdegreeLarge
      let : NumberField M :=
        NumberField.of_module_finite K M
      have hp : p.Prime := by
        simpa only [p] using
          cyclicDegreePrime_prime
            (K := K) (L := L) hdegreeLarge
      have hBaseDegree :
          Module.finrank K M = p := by
        simpa only [M, p] using
          cyclicPrimeDegreeIntermediate_finrank
            (K := K) (L := L) hdegreeLarge
      have hTopDegree :
          Module.finrank M L =
            Module.finrank K L / p := by
        simpa only [M, p] using
          cyclicPrimeDegreeIntermediate_top_finrank
            (K := K) (L := L) hdegreeLarge
      have hTopLt :
          Module.finrank M L <
            Module.finrank K L := by
        rw [hTopDegree]
        exact
          Nat.div_lt_self Module.finrank_pos hp.one_lt
      have hTopLtDegree :
          Module.finrank M L < degree := by
        exact hTopLt.trans_eq hfinrank
      have hTopIndex :
          (RelativeIdeleGroup.Cohomology.ideleClassNorm M L).range.index =
            Module.finrank M L :=
        ih (Module.finrank M L) hTopLtDegree M L rfl
      have hBaseUpper :
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range.index ≤
            Module.finrank K M := by
        rw [hBaseDegree]
        exact
          ideleClassNorm_index_le_prime_of_finrank_eq
            K M p hp hBaseDegree
      obtain ⟨sigmaM, hsigmaM⟩ :=
        IsCyclic.exists_generator (α := M ≃ₐ[K] M)
      have hBaseLower :
          Module.finrank K M ≤
            (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range.index :=
        _root_.GlobalClassFieldTheory.Cohomology.finrank_le_ideleClassNorm_index
          (K := K) (L := M) sigmaM hsigmaM
      have hBaseIndex :
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range.index =
            Module.finrank K M :=
        le_antisymm hBaseUpper hBaseLower
      have hTopCard :
          Nat.card
              (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L) =
            Module.finrank M L := by
        rw [← Subgroup.index_eq_card]
        exact hTopIndex
      have hBaseCard :
          Nat.card
              (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M) =
            Module.finrank K M := by
        rw [← Subgroup.index_eq_card]
        exact hBaseIndex
      let :
          Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L) :=
        Nat.finite_of_card_ne_zero (by
          rw [hTopCard]
          exact Nat.ne_of_gt Module.finrank_pos)
      let :
          Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M) :=
        Nat.finite_of_card_ne_zero (by
          rw [hBaseCard]
          exact Nat.ne_of_gt Module.finrank_pos)
      have hUpperCard :
          Nat.card
              (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) ≤
            Module.finrank K L := by
        calc
          Nat.card
                (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) ≤
              Nat.card
                  (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L) *
                Nat.card
                  (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M) :=
            ideleClassNormQuotient_card_le_actual_tower_mul
              K M L
          _ =
              Module.finrank M L *
                Module.finrank K M := by
            rw [hTopCard, hBaseCard]
          _ = Module.finrank K L := by
            rw [Nat.mul_comm,
              Module.finrank_mul_finrank K M L]
      have hUpper :
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index ≤
            Module.finrank K L := by
        rw [Subgroup.index_eq_card]
        exact hUpperCard
      obtain ⟨sigma, hsigma⟩ :=
        IsCyclic.exists_generator (α := L ≃ₐ[K] L)
      have hLower :
          Module.finrank K L ≤
            (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index :=
        _root_.GlobalClassFieldTheory.Cohomology.finrank_le_ideleClassNorm_index
          (K := K) (L := L) sigma hsigma
      exact (le_antisymm hUpper hLower).trans hfinrank

/-- The ordinary idele-class norm has index equal to the degree for every
finite cyclic extension. -/
theorem ideleClassNorm_index_eq_finrank_cyclic
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    (_root_.ideleClassNorm K L).range.index =
      Module.finrank K L := by
  rw [ordinaryIdeleClassNorm_range_eq_relative]
  exact
    relativeIdeleClassNorm_index_eq_finrank_cyclic K L

/-- Finiteness propagation through the actual tower norm-quotient
sequence. -/
theorem relativeIdeleClassNormQuotient_finite_of_actual_tower
    (K M L : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [IsGalois K M]
    [Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L)]
    [Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M)] :
    Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) := by
  let : IsMulCommutative (RelativeIdeleGroup.ClassGroup K M) :=
    ⟨⟨fun a b => mul_comm a b⟩⟩
  let : Finite (RelativeIdeleGroup.ClassNormQuotient M L) := by
    change
      Finite
        (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L)
    infer_instance
  let : Finite (RelativeIdeleGroup.ClassNormQuotient K M) := by
    change
      Finite
        (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M)
    infer_instance
  change Finite (RelativeIdeleGroup.ClassNormQuotient K L)
  let e :=
    intermediateClassNormQuotientBaseChangeMulEquiv
      K M L
  let :
      Finite
        (IntermediateClassNormQuotient K M L) :=
    Finite.of_injective e e.injective
  let f :=
    intermediateToCompositeNormQuotient K M L
  let g :=
    compositeToBaseNormQuotient K M L
  let :
      Fintype
        (IntermediateClassNormQuotient K M L) :=
    Fintype.ofFinite _
  let :
      Fintype (RelativeIdeleGroup.ClassNormQuotient K M) :=
    Fintype.ofFinite _
  let :
      Fintype
        (TowerCompositeClassNormQuotient K M L) :=
    Group.fintypeOfKerEqRange f g
      (_root_.intermediateToCompositeNormQuotient_range_eq_ker
        K M L).symm
  exact
    Finite.of_equiv
      (TowerCompositeClassNormQuotient K M L)
      (towerCompositeClassNormQuotientEquiv
        K M L).toEquiv

/-- The relative-coordinate presentation of the idele-class norm quotient
is finite and has cardinality at most
the extension degree for every finite abelian Galois extension. -/
theorem
    relativeIdeleClassNormQuotient_finite_and_card_le_finrank_abelian
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) ∧
      Nat.card (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) ≤
        Module.finrank K L := by
  classical
  induction hfinrank : Module.finrank K L using
      Nat.strong_induction_on generalizing K L with
  | h degree ih =>
    by_cases hdegreeOne : Module.finrank K L = 1
    · have hAutCard :
          Nat.card (L ≃ₐ[K] L) = 1 := by
        rw [IsGalois.card_aut_eq_finrank K L, hdegreeOne]
      let : Subsingleton (L ≃ₐ[K] L) :=
        (Nat.card_eq_one_iff_unique.mp hAutCard).1
      let : IsCyclic (L ≃ₐ[K] L) := inferInstance
      have hCard :
          Nat.card
              (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) =
            1 := by
        rw [← Subgroup.index_eq_card,
          relativeIdeleClassNorm_index_eq_finrank_cyclic K L,
          hdegreeOne]
      let :
          Finite
            (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) :=
        Nat.finite_of_card_ne_zero (by
          rw [hCard]
          exact one_ne_zero)
      exact
        ⟨inferInstance, by
          rw [hCard, ← hfinrank, hdegreeOne]⟩
    · have hdegreeLarge :
          1 < Module.finrank K L := by
        have hpositive : 0 < Module.finrank K L :=
          Module.finrank_pos
        omega
      let M :=
        primeOrderFixedField
          (K := K) (L := L) hdegreeLarge
      let : NumberField M :=
        NumberField.of_module_finite K M
      let : IsAbelianGalois K M := inferInstance
      let : IsAbelianGalois M L := inferInstance
      let : IsCyclic (L ≃ₐ[M] L) :=
        primeOrderFixedField_isCyclic
          (K := K) (L := L) hdegreeLarge
      have hp :
          (fixedFieldPrime
            (K := K) (L := L) hdegreeLarge).Prime :=
        fixedFieldPrime_prime
          (K := K) (L := L) hdegreeLarge
      have hTopDegree :
          Module.finrank M L =
            fixedFieldPrime
              (K := K) (L := L) hdegreeLarge := by
        simpa only [M] using
          (primeOrderFixedField_finrank
            (K := K) (L := L) hdegreeLarge)
      have hTopLarge :
          1 < Module.finrank M L := by
        rw [hTopDegree]
        exact hp.one_lt
      have hBaseLt :
          Module.finrank K M < Module.finrank K L := by
        calc
          Module.finrank K M <
              Module.finrank K M * Module.finrank M L :=
            (Nat.lt_mul_iff_one_lt_right
              Module.finrank_pos).2 hTopLarge
          _ = Module.finrank K L :=
            Module.finrank_mul_finrank K M L
      have hBaseLtDegree :
          Module.finrank K M < degree :=
        hBaseLt.trans_eq hfinrank
      have hBaseData :
          Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M) ∧
            Nat.card
                (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M) ≤
              Module.finrank K M :=
        ih (Module.finrank K M) hBaseLtDegree K M rfl
      let :
          Finite
            (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M) :=
        hBaseData.1
      have hTopCard :
          Nat.card
              (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L) =
            Module.finrank M L := by
        rw [← Subgroup.index_eq_card]
        exact relativeIdeleClassNorm_index_eq_finrank_cyclic M L
      let :
          Finite
            (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L) :=
        Nat.finite_of_card_ne_zero (by
          rw [hTopCard]
          exact Nat.ne_of_gt Module.finrank_pos)
      let :
          Finite
            (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) :=
        relativeIdeleClassNormQuotient_finite_of_actual_tower
          K M L
      refine ⟨inferInstance, ?_⟩
      calc
        Nat.card
              (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) ≤
            Nat.card
                (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L) *
              Nat.card
                (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M) :=
          ideleClassNormQuotient_card_le_actual_tower_mul
            K M L
        _ =
            Module.finrank M L *
              Nat.card
                (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M) := by
          rw [hTopCard]
        _ ≤ Module.finrank M L * Module.finrank K M :=
          Nat.mul_le_mul_left _ hBaseData.2
        _ = Module.finrank K L := by
          rw [Nat.mul_comm,
            Module.finrank_mul_finrank K M L]
        _ = degree := hfinrank

/-- Finiteness of the actual ordinary idele-class norm quotient of a finite
abelian Galois extension. -/
theorem ideleClassNormQuotient_finite_abelian
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    Finite
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) := by
  rw [ordinaryIdeleClassNorm_range_eq_relative]
  exact
    (relativeIdeleClassNormQuotient_finite_and_card_le_finrank_abelian
      K L).1

/-- Degree upper bound for the cardinality of the actual ordinary
idele-class norm quotient of a finite abelian Galois
extension. -/
theorem ideleClassNormQuotient_card_le_finrank_abelian
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    Nat.card
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≤
      Module.finrank K L := by
  rw [ordinaryIdeleClassNorm_range_eq_relative]
  exact
    (relativeIdeleClassNormQuotient_finite_and_card_le_finrank_abelian
      K L).2

/-- The cardinalities of the actual Herbrand models of the low Tate groups
for a finite cyclic extension.  The canonical Herbrand support
gives the Herbrand quotient `|G|`; the norm-index theorem supplies the
matching upper bound for `H⁰`, so the standard low-degree cardinal lemma
forces `H⁻¹` to have one element. -/
theorem ideleClass_lowDegree_card_eq_finrank_cyclic
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (sigma : L ≃ₐ[K] L)
    (hsigma :
      ∀ tau : L ≃ₐ[K] L,
        tau ∈ Subgroup.zpowers sigma) :
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    Nat.card
          (HerbrandH0 (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) =
        Module.finrank K L ∧
      Nat.card
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L) sigma) =
        1 := by
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  let : IsCyclic (L ≃ₐ[K] L) :=
    ⟨⟨sigma, hsigma⟩⟩
  obtain ⟨hC, hCvalue⟩ :=
    _root_.GlobalClassFieldTheory.Cohomology.ideleClass_herbrandQuotient_eq_card_of_supported_local_calculation
      (K := K) (L := L)
      (_root_.ideleClassHerbrandSupport
        (K := K) (L := L))
      sigma hsigma
      (_root_.relativeSupportedAboveHerbrandSupport_sup_principal_eq_top
        (K := K) (L := L))
      (_root_.GlobalClassFieldTheory.Cohomology.chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
        (K := K) (L := L))
  let :
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)) :=
    hC.1
  let :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) sigma) :=
    hC.2
  have hQuotient :
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := RelativeIdeleGroup.ClassGroup K L)
          sigma =
        (Module.finrank K L : ℚ) := by
    simpa only [Fintype.card_eq_nat_card,
      IsGalois.card_aut_eq_finrank K L] using
      hCvalue
  have hH0 :
      Nat.card
          (HerbrandH0 (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) =
        Module.finrank K L := by
    calc
      Nat.card
            (HerbrandH0 (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)) =
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index :=
        (RelativeIdeleGroup.Cohomology.ideleClassNorm_index_eq_herbrandH0_card
          K L).symm
      _ = Module.finrank K L :=
        relativeIdeleClassNorm_index_eq_finrank_cyclic K L
  exact
    CyclicCohomology.lowDegree_card_eq_of_herbrandQuotient_eq_nat_of_le
      sigma (Module.finrank K L) Module.finrank_pos
      hQuotient hH0.le

/-- Finiteness and cardinalities of the actual low-degree Tate cohomology
groups of the relative idele class representation. -/
theorem ideleClass_tate_lowDegree_finite_card_eq_finrank_cyclic
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (sigma : L ≃ₐ[K] L)
    (hsigma :
      ∀ tau : L ≃ₐ[K] L,
        tau ∈ Subgroup.zpowers sigma) :
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)) 0) ∧
      Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)) (-1)) ∧
      Nat.card
          (tateCohomology
            (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)) 0) =
        Module.finrank K L ∧
      Nat.card
          (tateCohomology
            (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)) (-1)) =
        1 := by
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  have hHerbrand :=
    ideleClass_lowDegree_card_eq_finrank_cyclic
      K L sigma hsigma
  let :
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)) :=
    Nat.finite_of_card_ne_zero (by
      rw [hHerbrand.1]
      exact Nat.ne_of_gt Module.finrank_pos)
  let :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) sigma) :=
    Nat.finite_of_card_ne_zero (by
      rw [hHerbrand.2]
      exact one_ne_zero)
  let e0 :
      tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) 0 ≃
        Additive
          (HerbrandH0 (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) :=
    (tateH0IsoHerbrandH0
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.ClassGroup K L)).toLinearEquiv.toEquiv
  let em :
      tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1) ≃
        Additive
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L) sigma) :=
    (tateHMinusOneIsoHerbrandHMinusOne
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.ClassGroup K L)
      sigma hsigma).toLinearEquiv.toEquiv
  let :
      Finite
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) 0) :=
    Finite.of_injective e0 e0.injective
  let :
      Finite
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1)) :=
    Finite.of_injective em em.injective
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · calc
      Nat.card
            (tateCohomology
              (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
                (RelativeIdeleGroup.ClassGroup K L)) 0) =
          Nat.card
            (Additive
              (HerbrandH0 (L ≃ₐ[K] L)
                (RelativeIdeleGroup.ClassGroup K L))) :=
        Nat.card_congr e0
      _ = Module.finrank K L := by
        change
          Nat.card
              (HerbrandH0 (L ≃ₐ[K] L)
                (RelativeIdeleGroup.ClassGroup K L)) =
            Module.finrank K L
        exact hHerbrand.1
  · calc
      Nat.card
            (tateCohomology
              (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
                (RelativeIdeleGroup.ClassGroup K L)) (-1)) =
          Nat.card
            (Additive
              (HerbrandHMinusOne (L ≃ₐ[K] L)
                (RelativeIdeleGroup.ClassGroup K L) sigma)) :=
        Nat.card_congr em
      _ = 1 := by
        change
          Nat.card
              (HerbrandHMinusOne (L ≃ₐ[K] L)
                (RelativeIdeleGroup.ClassGroup K L) sigma) =
            1
        exact hHerbrand.2

/-- The degree-minus-one vanishing conclusion in the exact multiplicative
form consumed by the Hasse norm principle. -/
theorem ideleClass_tateHMinusOne_subsingleton_cyclic
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (sigma : L ≃ₐ[K] L)
    (hsigma :
      ∀ tau : L ≃ₐ[K] L,
        tau ∈ Subgroup.zpowers sigma) :
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    Subsingleton
      (Multiplicative
        (tateCohomology
          (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) (-1))) := by
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  have h :=
    ideleClass_tate_lowDegree_finite_card_eq_finrank_cyclic
      K L sigma hsigma
  change
    Subsingleton
      (tateCohomology
        (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)) (-1))
  exact (Nat.card_eq_one_iff_unique.mp h.2.2.2).1

/-- Hilbert 90 makes the actual multiplicative `H⁻¹(G,Lˣ)` a
subsingleton for a supplied cyclic generator. -/
theorem fieldUnitsHerbrandHMinusOne_subsingleton
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    letI :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    Subsingleton (HerbrandHMinusOne (L ≃ₐ[K] L) Lˣ σ) := by
  let :=
    LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
  let e :=
    LocalClassFieldTheory.herbrandHminusOneEquivUnitsTateHminusOne
      K L σ hσ
  constructor
  intro x y
  apply e.injective
  have hTateSubsingleton :
      Subsingleton
        (tateCohomology
          (Rep.ofAlgebraAutOnUnits K L) (-1)) :=
    (Nat.card_eq_one_iff_unique.mp
      (LocalClassFieldTheory.unitsTateHminusOne_card_eq_one
        K L σ hσ)).1
  exact hTateSubsingleton.elim (e x) (e y)

/-- Cardinal form of the Hilbert-90 calculation. -/
theorem fieldUnitsHerbrandHMinusOne_card_eq_one
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    letI :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    Nat.card (HerbrandHMinusOne (L ≃ₐ[K] L) Lˣ σ) = 1 := by
  let :=
    LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
  let :
      Subsingleton
        (HerbrandHMinusOne (L ≃ₐ[K] L) Lˣ σ) :=
    fieldUnitsHerbrandHMinusOne_subsingleton K L σ hσ
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨inferInstance, ⟨1⟩⟩

/-- Transport Hilbert 90 from field units to the actual subgroup of
principal relative ideles. -/
theorem principalIdelesHerbrandHMinusOne_subsingleton
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    letI :=
      LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
    Subsingleton
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) σ) := by
  let :=
    LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
  let e :=
    fieldUnitsHerbrandHMinusOneEquivPrincipalIdeles
      K L σ
  let :
      Subsingleton
        (HerbrandHMinusOne (L ≃ₐ[K] L) Lˣ σ) :=
    fieldUnitsHerbrandHMinusOne_subsingleton K L σ hσ
  constructor
  intro x y
  apply e.symm.injective
  exact Subsingleton.elim (e.symm x) (e.symm y)

/-- Cardinal form for the principal-idele term in the class-group exact
sequence. -/
theorem principalIdelesHerbrandHMinusOne_card_eq_one
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    letI :=
      RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
    letI :=
      RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
    Nat.card
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) σ) = 1 := by
  let :=
    LocalClassFieldTheory.galoisGroupFieldUnitsMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.relativeIdeleMulDistribMulAction K L
  let :=
    RelativeIdeleGroup.Cohomology.principalIdeleMulDistribMulAction K L
  let :
      Subsingleton
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeIdeleGroup.principalSubgroup K L) σ) :=
    principalIdelesHerbrandHMinusOne_subsingleton K L σ hσ
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨inferInstance, ⟨1⟩⟩

end NormQuotientCommutativity

end GlobalClassFieldTheory.ClassFieldAxiom
