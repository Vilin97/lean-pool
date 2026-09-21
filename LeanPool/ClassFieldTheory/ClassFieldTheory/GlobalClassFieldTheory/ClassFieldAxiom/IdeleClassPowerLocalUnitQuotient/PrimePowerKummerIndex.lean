/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.SupportedIdeleIndex
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.NormContainment
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.SupportedPrincipalQuotient
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleClassHerbrandSupportedFinal
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge
import Mathlib.FieldTheory.IsSepClosed
/-!
# Prime-power Kummer norm index

This file combines the supported local index, principal-ideles exact sequence,
and norm containment to prove the prime-power Kummer norm-index theorem.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open KummerTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The actual exact-sequence product after evaluating the middle local
power quotient as `n^(2s)`. -/
theorem card_sUnitPrincipalQuotient_mul_card_ideleClassQuotient_eq_power_two_totalPlaceCard
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hS :
      ∀ v : HeightOneSpectrum (𝓞 K),
        v.asIdeal ∣
            Ideal.span {((n : ℕ) : 𝓞 K)} →
          v ∈ S)
    (hLarge :
      IdeleGroup.supportedAt
            (K := K)
            (S ∪ T :
              Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤) :
    Nat.card
          (SUnitGroup (K := K) (S ∪ T) ⧸
            sUnitPrincipalIdelePowerSubgroup
              (K := K) n S T) *
        Nat.card
          (IdeleClassPowerLocalUnitQuotient
            (K := K) n S T) =
      (n : ℕ) ^
        (2 * totalPlaceCard (K := K) S) := by
  rw [
    card_sUnitPrincipalQuotient_mul_card_ideleClassQuotient
      (K := K) n S T hLarge,
    card_supportedIdeleQuotient_eq_power_two_totalPlaceCard
      (K := K) n hmu S T hS]

/-- The class-quotient calculation for the Kummer-selected prime set.
The localization equality identifies the left term of the exact sequence
with the canonical `n`-th-power quotient of the `(S' ∪ T)`-unit group;
all support and divisibility hypotheses are derived from the prescribed
seed `S`. -/
theorem
    card_ideleClassPowerLocalUnitQuotient_eq_finrank_sUnitKummerPrimeSet
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
    Nat.card
        (IdeleClassPowerLocalUnitQuotient
          (K := K) n S' T) =
      Module.finrank K E := by
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
    Nat.card
        (IdeleClassPowerLocalUnitQuotient
          (K := K) n S' T) =
      Module.finrank K E
  have hnOne : 1 < (n : ℕ) := by
    rw [hn]
    calc
      1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ v :=
        Nat.pow_le_pow_right hp.pos
          (Nat.succ_le_iff.mpr hv)
  have hr :
      r ≤ totalPlaceCard (K := K) S' := by
    simpa only [S'] using
      galoisRank_le_totalPlaceCard_enlargedS
        (K := K) (Omega := Omega) E n hnOne hmu
        r eG S₀
  have hTcard :
      T.card =
        totalPlaceCard (K := K) S' - r := by
    simpa only [T, S', sUnitKummerPrimeCount] using
      sUnitKummerPrimeSet_card
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S₀
  have hDoubleSub :
      2 * totalPlaceCard (K := K) S' - r =
        totalPlaceCard (K := K) S' +
          (totalPlaceCard (K := K) S' - r) := by
    rw [two_mul]
    exact Nat.add_sub_assoc hr _
  have hTotal :
      totalPlaceCard (K := K) (S' ∪ T) =
        2 * totalPlaceCard (K := K) S' - r := by
    change
      Fintype.card (InfinitePlace K) + (S' ∪ T).card =
        2 * totalPlaceCard (K := K) S' - r
    rw [Finset.card_union_of_disjoint hST, hTcard, hDoubleSub]
    unfold totalPlaceCard
    simp only [Nat.add_assoc]
  have hPrincipal :=
    principalIdelePowerLocalUnitSubgroup_eq_sUnitNthPowersInField_sUnitKummerPrimeSet
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S
  dsimp only at hPrincipal
  change
    principalIdelePowerLocalUnitSubgroup
        (K := K) n S' T =
      sUnitNthPowersInField
        (K := K) n (S' ∪ T) at hPrincipal
  have hDen :
      sUnitPrincipalIdelePowerSubgroup
          (K := K) n S' T =
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) (S' ∪ T) →*
            SUnitGroup (K := K) (S' ∪ T)).range := by
    rw [sUnitPrincipalIdelePowerSubgroup, hPrincipal,
      sUnitNthPowersInField]
    exact
      Subgroup.comap_map_eq_self_of_injective
        (SUnitGroup
          (K := K) (S' ∪ T)).subtype_injective _
  have hLeft :
      Nat.card
          (SUnitGroup (K := K) (S' ∪ T) ⧸
            sUnitPrincipalIdelePowerSubgroup
              (K := K) n S' T) =
        (n : ℕ) ^
          (2 * totalPlaceCard (K := K) S' - r) := by
    rw [hDen,
      card_sUnit_nthPowerQuotient
        (K := K) (S' ∪ T) n hmu,
      hTotal]
  have hDiv :
      ∀ w : HeightOneSpectrum (𝓞 K),
        w.asIdeal ∣
            Ideal.span {((n : ℕ) : 𝓞 K)} →
          w ∈ S' := by
    intro w hwDvd
    have hnValLt :
        w.valuation K ((n : ℕ) : K) < 1 := by
      simpa using
        (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_dvd
          (K := K) w ((n : ℕ) : 𝓞 K)).2 hwDvd
    have hwSupport :
        w ∈ chosenUnitFiniteSupport (K := K) nUnit := by
      by_contra hwNotSupport
      have hnUnitVal :
          w.valuation K (nUnit : K) = 1 :=
        (mem_SUnitGroup_iff
          (K := K)
          (chosenUnitFiniteSupport (K := K) nUnit) nUnit).mp
            (mem_sUnitGroup_chosenUnitFiniteSupport
              (K := K) nUnit)
            w hwNotSupport
      have hnValEq :
          w.valuation K ((n : ℕ) : K) = 1 := by
        change w.valuation K ((n : ℕ) : K) = 1 at hnUnitVal
        exact hnUnitVal
      exact (ne_of_lt hnValLt) hnValEq
    exact
      subset_enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S₀
        (Finset.mem_union_right _ hwSupport)
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
  have hLargeS' :
      IdeleGroup.supportedAt
            (K := K) (S' : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤ := by
    simpa only [S'] using
      supportedAt_sup_principalSubgroup_eq_top_of_enlargeByRadicalSupport
        (K := K) (L := E) n hmu S₀ hS₀
  have hLarge :
      IdeleGroup.supportedAt
            (K := K)
            (S' ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤ := by
    apply top_unique
    rw [← hLargeS']
    exact
      sup_le_sup
          (IdeleGroup.supportedAt_mono
            (K := K) (by
              intro w hw
              exact Or.inl hw))
        le_rfl
  have hProduct :=
    card_sUnitPrincipalQuotient_mul_card_ideleClassQuotient_eq_power_two_totalPlaceCard
      (K := K) n hmu S' T hDiv hLarge
  rw [hLeft] at hProduct
  have hr2 :
      r ≤ 2 * totalPlaceCard (K := K) S' := by
    omega
  have hPow :
      (n : ℕ) ^
          (2 * totalPlaceCard (K := K) S') =
        (n : ℕ) ^
            (2 * totalPlaceCard (K := K) S' - r) *
          (n : ℕ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr2]
  have hClassCard :
      Nat.card
          (IdeleClassPowerLocalUnitQuotient
            (K := K) n S' T) =
        (n : ℕ) ^ r := by
    exact
      Nat.eq_of_mul_eq_mul_left
        (pow_pos n.pos
          (2 * totalPlaceCard (K := K) S' - r))
        (hProduct.trans hPow)
  calc
    Nat.card
          (IdeleClassPowerLocalUnitQuotient
            (K := K) n S' T) =
        (n : ℕ) ^ r :=
      hClassCard
    _ = Nat.card Gal(E/K) := by
      symm
      rw [Nat.card_congr eG.toEquiv, Nat.card_pi]
      simp
    _ = Module.finrank K E :=
      IsGalois.card_aut_eq_finrank K E

/-- Separable-closure realization of the norm-index calculation for a
prime-power Kummer extension presented as an intermediate field.  This
form is useful when the extension is already constructed inside a fixed
separable closure. -/
theorem
    ideleClassNorm_index_eq_finrank_primePowerKummer_intermediateField
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (eG :
      Gal(E/K) ≃*
        (Fin 1 → Multiplicative (ZMod (n : ℕ)))) :
    letI : NumberField E :=
      NumberField.of_module_finite K E
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index =
      Module.finrank K E := by
  classical
  let _ : NumberField E :=
    NumberField.of_module_finite K E
  let eCyclic :
      Gal(E/K) ≃* Multiplicative (ZMod (n : ℕ)) :=
    eG.trans
      (MulEquiv.piUnique
        (fun _ : Fin 1 =>
          Multiplicative (ZMod (n : ℕ))))
  let : IsCyclic Gal(E/K) :=
    eCyclic.isCyclic.mpr inferInstance
  let S : Finset (HeightOneSpectrum (𝓞 K)) :=
    _root_.ideleClassHerbrandSupport
      (K := K) (L := E)
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
      p v hp hv hn 1 eG S₀
  have hClassCard :=
    card_ideleClassPowerLocalUnitQuotient_eq_finrank_sUnitKummerPrimeSet
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn 1 eG S
  dsimp only at hClassCard
  change
    Nat.card
        (IdeleClassPowerLocalUnitQuotient
          (K := K) n S' T) =
      Module.finrank K E at hClassCard
  have hT :
      ∀ w, w ∈ T →
        _root_.FinitePlaceSplitsCompletely
          (K := K) (L := E) w := by
    intro w hw
    apply
      finitePlaceSplitsCompletely_of_mem_sUnitKummerPrimeSet
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn 1 eG S₀ w
    simpa only [T] using hw
  have hAway :
      ∀ w, w ∉ S' ∪ T →
        _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := E) w := by
    intro w hwAway
    apply
      _root_.GlobalClassFieldTheory.Cohomology.chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
    intro hwSupport
    have hwS : w ∈ S := by
      simpa only [S] using hwSupport
    have hwS₀ : w ∈ S₀ :=
      Finset.mem_union_left _
        (Finset.mem_union_left _ hwS)
    have hwS' : w ∈ S' :=
      subset_enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S₀ hwS₀
    exact hwAway (Finset.mem_union_left T hwS')
  have hnOne : 1 < (n : ℕ) := by
    rw [hn]
    calc
      1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ v :=
        Nat.pow_le_pow_right hp.pos
          (Nat.succ_le_iff.mpr hv)
  have harch :
      Even (n : ℕ) ∨
        ∀ w : InfinitePlace K, ¬ w.IsReal := by
    by_cases hnEven : Even (n : ℕ)
    · exact Or.inl hnEven
    · refine Or.inr ?_
      have hnNeTwo : (n : ℕ) ≠ 2 := by
        intro hnTwo
        apply hnEven
        rw [hnTwo]
        decide
      have hnLarge : 2 < (n : ℕ) := by
        omega
      obtain ⟨ζ, hζ⟩ := hmu
      have hζPrim : IsPrimitiveRoot ζ (n : ℕ) :=
        (mem_primitiveRoots n.pos).mp hζ
      have hRealZero :
          InfinitePlace.nrRealPlaces K = 0 :=
        InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
          hnLarge hζPrim
      intro w hwReal
      have hRealPos :
          0 < InfinitePlace.nrRealPlaces K :=
        Fintype.card_pos_iff.mpr ⟨⟨w, hwReal⟩⟩
      omega
  have hSub :
      ideleClassPowerLocalUnitSubgroup
          (K := K) n S' T ≤
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range :=
    ideleClassPowerLocalUnitSubgroup_le_ideleClassNorm_range
      (K := K) (L := E) n 1 eG S' T
      harch hT hAway
  have hPowerIndex :
      (ideleClassPowerLocalUnitSubgroup
          (K := K) n S' T).index =
        Module.finrank K E := by
    rw [Subgroup.index_eq_card]
    change
      Nat.card
          (IdeleClassPowerLocalUnitQuotient
            (K := K) n S' T) =
        Module.finrank K E
    exact hClassCard
  have hIndexDvd :
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index ∣
        (ideleClassPowerLocalUnitSubgroup
          (K := K) n S' T).index :=
    Subgroup.index_dvd_of_le hSub
  have hDvd :
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index ∣
        Module.finrank K E := by
    simpa only [hPowerIndex] using hIndexDvd
  have hUpper :
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index ≤
        Module.finrank K E :=
    Nat.le_of_dvd Module.finrank_pos hDvd
  obtain ⟨sigma, hsigma⟩ :=
    IsCyclic.exists_generator (α := Gal(E/K))
  have hLower :
      Module.finrank K E ≤
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index :=
    Cohomology.finrank_le_ideleClassNorm_index
      (K := K) (L := E) sigma hsigma
  exact le_antisymm hUpper hLower

/-- The norm subgroup has index `[E : K]` for an arbitrary prime-power
Kummer extension.  The proof realizes `E` as its field range in a fixed
separable closure, applies the intermediate-field calculation there,
and transports both the norm index and the degree back across the
resulting `K`-algebra equivalence. -/
theorem ideleClassNorm_index_eq_finrank_primePowerKummer
    {E : Type} [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (eG :
      Gal(E/K) ≃*
        (Fin 1 → Multiplicative (ZMod (n : ℕ)))) :
    letI : NumberField E :=
      NumberField.of_module_finite K E
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index =
      Module.finrank K E := by
  classical
  let : NumberField E :=
    NumberField.of_module_finite K E
  let i : E →ₐ[K] SeparableClosure K :=
    IsSepClosed.lift
  let R : IntermediateField K (SeparableClosure K) :=
    AlgHom.fieldRange i
  let e : E ≃ₐ[K] R :=
    AlgHom.equivFieldRange i
  let _ : FiniteDimensional K R :=
    e.toLinearEquiv.finiteDimensional
  let _ : IsGalois K R :=
    IsGalois.of_algEquiv e
  let _ : NumberField R :=
    NumberField.of_module_finite K R
  let _ : (RelativeIdeleGroup.principalSubgroup K R).Normal :=
    ⟨fun n hn g => by
      have hconj : g * n * g⁻¹ = n := by
        rw [mul_comm g n, mul_assoc, mul_inv_cancel, mul_one]
      rwa [hconj]⟩
  let _ : Group (RelativeIdeleGroup.ClassGroup K R) :=
    QuotientGroup.Quotient.group
      (RelativeIdeleGroup.principalSubgroup K R)
  let eG' :
      Gal(R/K) ≃*
        (Fin 1 → Multiplicative (ZMod (n : ℕ))) :=
    (AlgEquiv.autCongr e).symm.trans eG
  have hR :=
    ideleClassNorm_index_eq_finrank_primePowerKummer_intermediateField
      (K := K) (Omega := SeparableClosure K) R n hmu
      p v hp hv hn eG'
  calc
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index =
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K R).range.index :=
      (ideleClassNorm_index_algEquiv
        (K := K) e).symm
    _ = Module.finrank K R := hR
    _ = Module.finrank K E :=
      e.toLinearEquiv.finrank_eq.symm


end GlobalClassFieldTheory.ClassFieldAxiom
