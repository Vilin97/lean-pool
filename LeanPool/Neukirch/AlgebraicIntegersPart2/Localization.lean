/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hu Yongle
-/

/-
Copyright (c) 2023 Hu Yongle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hu Yongle
-/
import Mathlib.Tactic
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.LocalProperties
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.Algebra.Category.GroupCat.Images
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DedekindDomain.SelmerGroup


set_option autoImplicit false

section Localization

open Ideal Localization IsLocalization IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]



-- Proposition 11.1
#check orderIsoOfPrime

-- Proposition 11.2
#check AtPrime.localRing

instance : Algebra (R ⧸ p)
    ((Localization.AtPrime p) ⧸ LocalRing.maximalIdeal (Localization.AtPrime p)) :=
  Ideal.Quotient.algebraQuotientOfLEComap (Eq.ge (@AtPrime.comap_maximalIdeal _ _ p _))

instance fractionRing_of_quotient_of_prime : IsFractionRing (R ⧸ p) ((Localization.AtPrime p) ⧸ LocalRing.maximalIdeal (Localization.AtPrime p)) := sorry

def quotient_of_maximal_ideal_power_eq_localization [IsMaximal p] (n : ℕ) (h : n ≥ 1): R ⧸ p ^ n
  ≃+* (Localization.AtPrime p) ⧸ LocalRing.maximalIdeal (Localization.AtPrime p) ^ n := sorry



-- Definition 11.3
#check DiscreteValuationRing

-- Proposition 11.4
#check isDedekindDomain

-- Proposition 11.5
#check IsDedekindDomainDvr

#check isDedekindDomainDvr

instance : IsScalarTower R (Localization.AtPrime p) (FractionRing R) :=
  localization_isScalarTower_of_submonoid_le (Localization.AtPrime p) (FractionRing R)
  (primeCompl p) (nonZeroDivisors R) (primeCompl_le_nonZeroDivisors p)

instance : IsFractionRing (Localization.AtPrime p) (FractionRing R) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (primeCompl p)
  (Localization.AtPrime p) (FractionRing R)

lemma field_toisIntegrallyClosed {R : Type*} [Field R] : IsIntegrallyClosed R :=
  inferInstance
#check isIntegrallyClosed_iff
instance isIntegrallyClosed_ofLocalizationMaximal₀ (h : ∀ p : Ideal R, p ≠ ⊥ → [p.IsMaximal] →
    IsIntegrallyClosed (Localization.AtPrime p)) : IsIntegrallyClosed R := by
  by_cases hf : IsField R
  apply @field_toisIntegrallyClosed R (IsField.toField hf)
  apply (isIntegrallyClosed_iff (FractionRing R)).mpr
  rintro ⟨x⟩ hx
  let I : Ideal R := {
    carrier := { a : R | ∃ y, mk (a * x.1) x.2 = (algebraMap R (FractionRing R)) y }
    add_mem' := by
      intro a b ⟨y, hy⟩ ⟨z, hz⟩
      use y + z
      calc _ = mk (a * x.1) x.2 + mk (b * x.1) x.2 := by
            rw [add_mk_self (a * x.1) x.2 (b * x.1), add_mul]
        _ = (algebraMap R (FractionRing R)) y + (algebraMap R (FractionRing R)) z := by rw [hy, hz]
        _ = _ := by rw [map_add]
    zero_mem' := by use 0; rw [zero_mul, FractionRing.mk_eq_div, map_zero, zero_div]
    smul_mem' := by
      intro a b ⟨y, hy⟩
      use a * y
      rw [smul_eq_mul, mul_assoc, ← one_mul x.2, ← mk_mul a (b * x.1) 1 x.2, _root_.map_mul, hy]
      rfl
  }
  have ht : I = ⊤ := by
    by_contra hn
    rcases exists_le_maximal I hn with ⟨p, hpm, hpi⟩
    have hic := h p (Ring.ne_bot_of_isMaximal_of_not_isField hpm hf)
    have hxp : IsIntegral (Localization.AtPrime p) (mk x.1 x.2) := IsIntegral.tower_top hx
    rcases (isIntegrallyClosed_iff (FractionRing R)).mp hic hxp with ⟨⟨y⟩, hy⟩
    have hxy : mk x.1 x.2 = algebraMap (Localization.AtPrime p) (FractionRing R) (mk y.1 y.2) := by
      rw [← hy]
      rfl
    have hy : mk y.2.1 1 = algebraMap (Localization.AtPrime p) (FractionRing R)
      (algebraMap R (Localization.AtPrime p) y.2.1) := by
        rw [mk_one_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
    have hyi : y.2.1 ∈ I := by
      use y.1
      rw [← one_mul x.2, ← mk_mul, hxy, hy, ← _root_.map_mul, mk_eq_mk'_apply, mk'_spec',
        IsScalarTower.algebraMap_apply R (Localization.AtPrime p) (FractionRing R) y.1]
    exact y.2.2 (hpi hyi)
  have h1 : 1 ∈ I := Eq.mpr (ht ▸ Eq.refl (1 ∈ I)) trivial
  rcases h1 with ⟨y, hy⟩
  use y
  rw [← hy, one_mul]
  rfl

theorem isIntegrallyClosed_ofLocalizationMaximal :
    OfLocalizationMaximal fun R _ ↦ ([IsDomain R] → IsIntegrallyClosed R) :=
  fun _ _ h _ ↦ isIntegrallyClosed_ofLocalizationMaximal₀ fun p _ hpm ↦ h p hpm



instance IsDedekindDomainDvr.isNoetherian (h : IsDedekindDomainDvr R) : IsNoetherian R R :=
  h.isNoetherianRing

instance IsDedekindDomainDvr.Ring.DimensionLEOne (h : IsDedekindDomainDvr R) : Ring.DimensionLEOne R
  where maximalOfPrime := by
          intro p hp hpp
          rcases exists_le_maximal p (IsPrime.ne_top hpp) with ⟨q, hq, hpq⟩
          let f := OrderIso.symm <|
            orderIsoOfPrime (primeCompl q) (Localization.AtPrime q)
          let P := f ⟨p, hpp, HasSubset.Subset.disjoint_compl_left hpq⟩
          let Q := f ⟨q, IsMaximal.isPrime hq, HasSubset.Subset.disjoint_compl_left (Eq.subset rfl)⟩
          have hinj : Function.Injective (algebraMap R (Localization.AtPrime q)) :=
            IsLocalization.injective (Localization.AtPrime q) (primeCompl_le_nonZeroDivisors q)
          have hp1 : P.1 ≠ ⊥ := fun x ↦ hp ((map_eq_bot_iff_of_injective hinj).mp x)
          have hq1 : Q.1 ≠ ⊥ :=
            fun x ↦ (ne_bot_of_le_ne_bot hp hpq) ((map_eq_bot_iff_of_injective hinj).mp x)
          rcases (DiscreteValuationRing.iff_pid_with_one_nonzero_prime (Localization.AtPrime q)).mp
            (h.is_dvr_at_nonzero_prime q (ne_bot_of_le_ne_bot hp hpq) _) with ⟨_, huq⟩
          have peqq := Subtype.val_inj.mpr <| OrderIso.injective f <|
            Subtype.val_inj.mp (ExistsUnique.unique huq ⟨hp1, P.2⟩ ⟨hq1, Q.2⟩)
          simp only at peqq
          rw [peqq]
          exact hq

instance IsDedekindDomainDvr.isIntegrallyClosed (h : IsDedekindDomainDvr R) :
    IsIntegrallyClosed R := by
  refine isIntegrallyClosed_ofLocalizationMaximal₀ ?_
  intro p hp0 _
  rcases (DiscreteValuationRing.iff_pid_with_one_nonzero_prime (Localization.AtPrime p)).mp
    (h.is_dvr_at_nonzero_prime p hp0 _) with ⟨_, _⟩
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

instance IsDedekindDomainDvr.instIsDedekindRing (h : IsDedekindDomainDvr R) : IsDedekindRing R where
  __ := h.1
  __ := IsDedekindDomainDvr.Ring.DimensionLEOne h
  __ := IsDedekindDomainDvr.isIntegrallyClosed h

instance IsDedekindDomainDvr.instIsDedekindDomain (h : IsDedekindDomainDvr R) : IsDedekindDomain R :=
  @IsDedekindDomain.mk R _ _ h.instIsDedekindRing

end Localization



open DirectSum FractionalIdeal IsDedekindDomain Ideal



#check HeightOneSpectrum.intValuationDef

#check HeightOneSpectrum.valuation

#check HeightOneSpectrum.valuationOfNeZeroToFun



noncomputable section

#check Set.integer

#check Set.unit

#check Set.unitEquivUnitsInteger

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
  (S : Set (HeightOneSpectrum R)) [Fintype S] (p : HeightOneSpectrum R)
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]



def unit_to_set_unit : Additive Rˣ →+ Additive (Set.integer S K)ˣ :=
  MonoidHom.toAdditive (Units.map (algebraMap R (Set.integer S K)))



abbrev prime_set_unit : Subgroup Kˣ := Set.unit ({p} : Set (HeightOneSpectrum R))ᶜ K

abbrev set_unit_to_quotient₀ : Additive (Set.integer S K)ˣ →+ Additive (Kˣ⧸prime_set_unit p K) :=
  MonoidHom.toAdditive <|
    (QuotientGroup.mk' (prime_set_unit p K)).comp (Units.map (algebraMap (Set.integer S K) K))

open Classical

instance (p : S) : AddCommMonoid (Additive (Set.integer S K)ˣ →+ Additive (Kˣ⧸prime_set_unit p.1 K)) :=
  @AddMonoidHom.addCommMonoid (Additive (Set.integer S K)ˣ) (Additive (Kˣ⧸prime_set_unit p.1 K)) _ _

def set_unit_to_quotient : Additive (Set.integer S K)ˣ →+
    (⨁ (p : S), Additive (Kˣ⧸prime_set_unit p.1 K)) := fromAddMonoid
  (mk (fun (p : S) ↦ (Additive (Set.integer S K)ˣ →+ Additive (Kˣ⧸prime_set_unit p.1 K)))
  (@Finset.univ (Set.Elem S) _) (fun p ↦ set_unit_to_quotient₀ S p.1.1 K))



def quotient_to_int : (Kˣ⧸prime_set_unit p K) →* Multiplicative ℤ := by
  refine QuotientGroup.lift (prime_set_unit p K) (HeightOneSpectrum.valuationOfNeZero p) ?_
  intro x hx
  apply WithZero.coe_inj.mp
  rw [HeightOneSpectrum.valuationOfNeZero_eq p x, hx p (Iff.mpr Set.not_mem_compl_iff rfl)]
  rfl

def prime_to_unit_of_FractionalIdeal (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
  HeightOneSpectrum R → (FractionalIdeal (nonZeroDivisors R) K)ˣ := fun p ↦ {
    val := coeIdeal p.1
    inv := (coeIdeal p.1)⁻¹
    val_inv := mul_inv_cancel₀ (coeIdeal_ne_zero.mpr (p.ne_bot))
    inv_val := inv_mul_cancel₀ (coeIdeal_ne_zero.mpr (p.ne_bot))
}

instance : Pow (FractionalIdeal (nonZeroDivisors R) K)ˣ ℤ := by exact DivInvMonoid.Pow
def int_to_unit_of_FractionalIdeal :
    Multiplicative ℤ →* (FractionalIdeal (nonZeroDivisors R) K)ˣ where
  toFun n := (prime_to_unit_of_FractionalIdeal K p) ^ (Multiplicative.toAdd.toFun n)
  map_one' := zpow_eq_one_iff_modEq.mpr rfl
  map_mul' m n := by simpa only [Equiv.toFun_as_coe, toAdd_mul] using zpow_add _ _ _

abbrev quotient_to_ClassGroup₀ : Kˣ ⧸ prime_set_unit p K →* ClassGroup R :=
  ClassGroup.mk.comp ((int_to_unit_of_FractionalIdeal p K).comp (quotient_to_int p K))

def quotient_to_ClassGroup :
    (⨁ (p : S), Additive (Kˣ ⧸ prime_set_unit p.1 K)) →+ Additive (ClassGroup R) :=
  toAddMonoid (fun (p : S) ↦ MonoidHom.toAdditive (quotient_to_ClassGroup₀ p.1 K))


/-
instance (A : Subalgebra R K) : IsFractionRing A K where
  map_units' := fun x ↦ isUnit_iff_exists_inv.mpr ⟨x.1.1⁻¹, (mul_inv_eq_one₀
    (fun h ↦ (nonZeroDivisors.coe_ne_zero x) (by apply Subtype.val_inj.mp; rw[h]; rfl))).mpr rfl⟩
  surj' := by
    intro z
    rcases @IsFractionRing.div_surjective R _ _ _ _ _ _ z with ⟨x,y, hy, hxy⟩
    have h := nonZeroDivisors.coe_ne_zero ⟨y, hy⟩
    refine' ⟨⟨(algebraMap R A) x, ⟨(algebraMap R A) y, _⟩⟩, _⟩
    · exact mem_nonZeroDivisors_of_ne_zero <|
        (map_ne_zero_iff (algebraMap R A) (NoZeroSMulDivisors.algebraMap_injective R A)).mpr h
    · simp only [← IsScalarTower.algebraMap_apply, ← hxy]
      exact div_mul_cancel ((algebraMap R K) x) <|
        (map_ne_zero_iff (algebraMap R K) (NoZeroSMulDivisors.algebraMap_injective R K)).mpr h
  eq_iff_exists' := by
    intro x y
    calc _ ↔ x = y := Function.Injective.eq_iff (NoZeroSMulDivisors.algebraMap_injective A K)
      _ ↔ _ := by
        refine' ⟨fun h ↦ ⟨1, by rw[h]⟩, fun h ↦ _⟩
        exact Exists.casesOn h fun c hc ↦ (mul_cancel_left_mem_nonZeroDivisors c.property).mp hc

lemma ceo_commute (I : FractionalIdeal (nonZeroDivisors R) K) : (I.1 : Set K) = (I : Set K) := rfl

def FractionalIdeal.Subalgebra_map (A : Subalgebra R K) [IsDedekindDomain A] :
    (FractionalIdeal (nonZeroDivisors R) K) →* (FractionalIdeal (nonZeroDivisors A) K) where
  toFun I := by
    refine' ⟨Submodule.span A (I : Set K), _⟩
    rcases I.2 with ⟨a, ha, h⟩
    use algebraMap R A a
    constructor
    exact map_mem_nonZeroDivisors (algebraMap R A) (NoZeroSMulDivisors.algebraMap_injective R A) ha
    intro _ hb
    refine' Submodule.span_induction hb _ _ _ _
    · intro x hx
      rcases h x hx with ⟨t, ht⟩
      use algebraMap R A t
      rw[← IsScalarTower.algebraMap_apply, ht, algebra_compatible_smul A a x]
    · exact ⟨0, by rw[_root_.map_zero, smul_zero]⟩
    · intro x y ⟨s, hs⟩ ⟨t, ht⟩
      exact ⟨s + t, by simp only [_root_.map_add, hs, algebraMap_smul, ht, smul_add]⟩
    · exact fun s x ⟨t, ht⟩ ↦
      ⟨s * t, by simp only [_root_.map_mul, ht, algebraMap_smul, Algebra.mul_smul_comm]; rfl⟩
  map_one' := by
    apply Subtype.val_inj.mp
    apply Submodule.span_eq_of_le
    · intro x hx
      rcases (mem_one_iff (nonZeroDivisors R)).mp (SetLike.mem_coe.mp hx) with ⟨s, hs⟩
      apply (mem_one_iff (nonZeroDivisors A)).mpr
      use algebraMap R A s
      rw[← IsScalarTower.algebraMap_apply, hs]
    · intro x hx
      rcases (mem_one_iff (nonZeroDivisors _)).mp (SetLike.mem_coe.mp hx) with ⟨s, hs⟩
      let r : FractionalIdeal (nonZeroDivisors R) K := 1
      have hsx : s • (1 : K) = x := by
        dsimp[HSMul.hSMul, SMul.smul]
        rw[mul_one, ← hs]
        rfl
      rw[← hsx]
      exact Submodule.smul_mem _ s <|
        (@Submodule.subset_span A K _ _ _ ↑r) (one_mem_one (nonZeroDivisors R))
  map_mul' := by
    intro I J
    apply Subtype.val_inj.mp
    dsimp
    simp only [coe_mul, coe_mk, Submodule.span_mul_span]
    apply Submodule.span_eq_span
    · have hij : (I * J).1 = I.1 * J.1 := coe_mul I J
      rw[← Submodule.span_eq I.1, ← Submodule.span_eq J.1, Submodule.span_mul_span] at hij
      have hij := SetLike.coe_set_eq.mpr hij
      rw[ceo_commute K I, ceo_commute K J, ceo_commute K (I * J)] at hij
      rw[hij]
      exact Submodule.span_subset_span R A _
    · have hij := Submodule.mul_subset_mul I.1 J.1
      have hm : I.1 * J.1 = (I * J).1 := by simp only [val_eq_coe, coe_mul]
      rw[hm, ceo_commute K I, ceo_commute K J, ceo_commute K (I * J)] at hij
      exact hij.trans (@Submodule.subset_span A K _ _ _ ((I * J) : Set K))



def set_Submonoid : Submonoid R where
  carrier := {x : R | x ≠ 0 ∧ ∀ p : HeightOneSpectrum R, x ∈ p.1 → p ∈ S }
  mul_mem' := fun {_ _} hx hy ↦ ⟨mul_ne_zero hx.left hy.left, fun p hxy ↦ Or.casesOn
    (IsPrime.mem_or_mem p.isPrime hxy) (fun h ↦ And.right hx p h) (fun h ↦ And.right hy p h)⟩
  one_mem' := ⟨one_ne_zero, fun p hp ↦ False.elim <|
    IsMaximal.ne_top (HeightOneSpectrum.isMaximal p) (Iff.mpr (eq_top_iff_one p.1) hp)⟩

lemma set_Submonoid_le : (set_Submonoid S) ≤ nonZeroDivisors R :=
  le_nonZeroDivisors_of_noZeroDivisors fun h ↦ And.left h rfl

-- It may only hold in the cases of Number Fields.
instance : IsLocalization (set_Submonoid S) (Set.integer S K) where
  map_units' := by
    intro x
    apply isUnit_iff_exists_inv.mpr
    refine' ⟨⟨(algebraMap R K x.1)⁻¹, _⟩, _⟩
    · intro p hp
      have h : (HeightOneSpectrum.intValuation p) x.1 = 1 := Decidable.byContradiction fun h ↦
        hp <| x.2.2 p <| Iff.mp dvd_span_singleton <|
          (HeightOneSpectrum.int_valuation_lt_one_iff_dvd p x.1).mp <|
            Ne.lt_of_le h (HeightOneSpectrum.int_valuation_le_one p x.1)
      rw[map_inv₀, HeightOneSpectrum.valuation_of_algebraMap, h]
      exact Eq.ge rfl
    · exact Subtype.val_inj.mp <| mul_inv_cancel <|
        (map_ne_zero_iff (algebraMap R K) (NoZeroSMulDivisors.algebraMap_injective R K)).mpr x.2.1
  surj' := sorry
  eq_iff_exists' := sorry



instance : IsDedekindDomain (Set.integer S K) := sorry

instance : Algebra (Set.integer S K) (Set.integer S K) := Algebra.id (Set.integer S K)

instance : Algebra (Set.integer S K) (FractionRing (Set.integer S K)) := Localization.algebra

def ClassGroup_to_ClassGroup_of_set_unit₀ :
    (FractionalIdeal (nonZeroDivisors R) K)ˣ ⧸ MonoidHom.range (toPrincipalIdeal R K) →*
    (FractionalIdeal (nonZeroDivisors (Set.integer S K)) K)ˣ ⧸
    MonoidHom.range (toPrincipalIdeal (Set.integer S K) K) := by
  apply QuotientGroup.map _ _ (Units.map (Subalgebra_map K (Set.integer S K)))
  intro x hx
  apply Subgroup.mem_comap.mpr
  rcases MonoidHom.mem_range.mp hx with ⟨y, hy⟩
  refine' MonoidHom.mem_range.mpr ⟨y, _⟩
  apply Units.eq_iff.mp
  dsimp
  rw[coe_toPrincipalIdeal, ← hy, coe_toPrincipalIdeal, spanSingleton, spanSingleton, Subalgebra_map]
  apply coeToSubmodule_inj.mp
  dsimp
  rw[← ceo_commute]
  refine' Submodule.span_eq_span _ (Submodule.span_subset_span R (Set.integer S K) {y.1})
  have h := @Submodule.subset_span (Set.integer S K) _ _ _ _ ((Submodule.span R {y.1}) : Set K)
  exact (@Submodule.subset_span R _ _ _ _ {y.1}).trans h

def ClassGroup_to_ClassGroup_of_set_unit :
  Additive (ClassGroup R) →+ Additive (ClassGroup (Set.integer S K)) := MonoidHom.toAdditive <|
    (@ClassGroup.equiv (Set.integer S K) K _ _ _ _ _).symm.toMonoidHom.comp <|
      (ClassGroup_to_ClassGroup_of_set_unit₀ S K).comp (ClassGroup.equiv K).toMonoidHom
 -/
