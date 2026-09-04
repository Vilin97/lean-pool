/-
Copyright (c) 2026 FltRegular contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FltRegular contributors
-/

module

import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

import LeanPool.FltRegular.NumberTheory.Unramified

/-!
# The field-theoretic part of Kummer's lemma

This file constructs Kummer's auxiliary polynomial and proves the associated splitting field is
unramified.
-/

@[expose] public section

open scoped NumberField

attribute [local implicit_reducible] integralClosure NumberField.RingOfIntegers

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] (hp : p ≠ 2)

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

variable (u : (𝓞 K)ˣ)
  (hcong : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1) (hu : ∀ v : K, v ^ p ≠ u)

open Polynomial IsCyclotomicExtension.Rat

include hcong hp in
lemma zeta_sub_one_pow_dvd_poly :
    C ((hζ.toInteger - 1 : 𝓞 K) ^ p) ∣
      (C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (u : 𝓞 K) := by
  rw [← dvd_sub_left (_root_.map_dvd C hcong), add_sub_assoc, C.map_sub (u : 𝓞 K), ← sub_add,
    sub_self, map_one, zero_add]
  refine dvd_C_mul_X_sub_one_pow_add_one hpri.out hp _ _ dvd_rfl ?_
  have hassoc : Associated ((hζ.toInteger - 1 : 𝓞 K) ^ (p - 1)) p := by
    simpa only using associated_zeta_sub_one_pow_prime _ hζ
  convert mul_dvd_mul_right hassoc.dvd _
  rw [← pow_succ, tsub_add_cancel_of_le (Nat.Prime.one_lt hpri.out).le]

namespace KummersLemma

lemma natDegree_poly_aux :
    natDegree ((C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (u : 𝓞 K)) = p := by
  rw [natDegree_add_C, natDegree_pow, ← C.map_one, natDegree_sub_C, natDegree_mul_X, natDegree_C,
    zero_add, mul_one]
  exact C_ne_zero.mpr (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)

lemma monic_poly_aux :
    leadingCoeff ((C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (u : 𝓞 K)) =
      (hζ.toInteger - 1 : 𝓞 K) ^ p := by
  trans leadingCoeff ((C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p)
  · rw [leadingCoeff, leadingCoeff, coeff_add]
    nth_rewrite 1 [natDegree_add_C]
    convert add_zero _ using 2
    rw [natDegree_poly_aux hζ, coeff_C, ite_eq_right (NeZero.pos p).ne.symm]
  · rw [leadingCoeff_pow, ← C.map_one, leadingCoeff, natDegree_sub_C, natDegree_mul_X]
    · simp only [map_one, natDegree_C, zero_add, coeff_sub, coeff_mul_X, coeff_C,
        coeff_one, sub_zero, one_ne_zero, ↓reduceIte]
    · exact C_ne_zero.mpr (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)
/-- The monic polynomial used in Kummer's lemma after dividing by `(ζ - 1)^p`. -/
noncomputable def poly : (𝓞 K)[X] := (zeta_sub_one_pow_dvd_poly hp hζ u hcong).choose

lemma poly_spec :
    C ((hζ.toInteger - 1 : 𝓞 K) ^ p) * poly hp hζ u hcong =
      (C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (u : 𝓞 K) :=
  (zeta_sub_one_pow_dvd_poly hp hζ u hcong).choose_spec.symm

lemma monic_poly : Monic (poly hp hζ u hcong) := by
  have := congr_arg leadingCoeff (poly_spec hp hζ u hcong)
  simp only [map_pow, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_C,
    monic_poly_aux hζ] at this
  refine mul_right_injective₀ ?_ (this.trans (mul_one _).symm)
  exact pow_ne_zero _ (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)

lemma natDegree_poly : natDegree (poly hp hζ u hcong) = p := by
  have := congr_arg natDegree (poly_spec hp hζ u hcong)
  rwa [natDegree_C_mul, natDegree_poly_aux hζ] at this
  exact pow_ne_zero _ (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)

lemma map_poly : (poly hp hζ u hcong).map (algebraMap (𝓞 K) K) =
    (X - C (1 / (ζ - 1))) ^ p + C (u / (ζ - 1) ^ p : K) := by
  ext i
  have := congr_arg (fun P : (𝓞 K)[X] ↦ (↑(coeff P i) : K)) (poly_spec hp hζ u hcong)
  change _ = algebraMap (𝓞 K) K _ at this
  rw [← coeff_map] at this
  replace this : (ζ - 1) ^ p * ↑((poly hp hζ u hcong).coeff i) =
    (((C ζ - 1) * X - 1) ^ p).coeff i +
    (C ((algebraMap (𝓞 K) K) ↑u)).coeff i := by
    simp only [map_pow, map_sub, map_one, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_mul, map_C, Polynomial.map_one, map_X, coeff_add] at this
    convert this
    · simp only [← Polynomial.coeff_map]
      simp only [coeff_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_C,
        Polynomial.map_one]
      rw [← Polynomial.coeff_map, mul_comm, ← Polynomial.coeff_mul_C, mul_comm]
      simp
    · rfl
  apply mul_right_injective₀ (pow_ne_zero p (hζ.sub_one_ne_zero hpri.out.one_lt))
  simp only [coeff_map, one_div, coeff_add, this, mul_add]
  simp_rw [← smul_eq_mul (α := K), ← coeff_smul]
  rw [smul_C, smul_eq_mul, ← _root_.smul_pow, ← mul_div_assoc, mul_div_cancel_left₀, smul_sub,
    smul_C, smul_eq_mul, mul_inv_cancel₀, map_one, Algebra.smul_def, ← C_eq_algebraMap, map_sub,
    map_one]
  · exact hζ.sub_one_ne_zero hpri.out.one_lt
  · exact pow_ne_zero _ (hζ.sub_one_ne_zero hpri.out.one_lt)

include hu in
lemma irreducible_map_poly :
    Irreducible ((poly hp hζ u hcong).map (algebraMap (𝓞 K) K)) := by
  rw [map_poly]
  refine Irreducible.of_map (f := algEquivAevalXAddC (1 / (ζ - 1))) ?_
  simp only [one_div, map_add, algEquivAevalXAddC_apply, map_pow, map_sub, aeval_X, aeval_C,
    algebraMap_eq, add_sub_cancel_right]
  rw [← sub_neg_eq_add, ← (C : K →+* _).map_neg]
  apply X_pow_sub_C_irreducible_of_prime hpri.out
  intro b hb
  apply hu (- b * (ζ - 1))
  rw [mul_pow, (hpri.out.odd_of_ne_two hp).neg_pow, hb, neg_neg,
    div_mul_cancel₀ _ (pow_ne_zero _ (hζ.sub_one_ne_zero hpri.out.one_lt))]

theorem aeval_poly {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (m : ℕ) :
    aeval (((1 : L) - ζ ^ m • α) / (algebraMap K L (ζ - 1))) (poly hp hζ u hcong) = 0 := by
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  rw [map_sub, map_one]
  have := congr_arg (aeval ((1 - ζ ^ m • α) / (algebraMap K L (ζ - 1))))
    (poly_spec hp hζ u hcong)
  have hcoe : (algebraMap (𝓞 K) L) (↑hζ.toInteger) = algebraMap K L ζ := rfl
  have hcoe1 : (algebraMap (𝓞 K) L) ↑u = algebraMap K L ↑↑u := rfl
  simp only [map_sub, map_one, map_pow, map_mul, aeval_C, _root_.smul_pow, hcoe, e, hcoe1, map_add,
    aeval_X, ← mul_div_assoc, mul_div_cancel_left₀ _ hζ', sub_sub_cancel_left,
    (hpri.out.odd_of_ne_two hp).neg_pow] at this
  rw [← pow_mul, mul_comm m, pow_mul, hζ.pow_eq_one, one_pow, one_smul, neg_add_cancel,
    mul_eq_zero] at this
  exact this.resolve_left (pow_ne_zero _ hζ')

/-- The integral root obtained by the Kummer transform from a `p`-th root of `u`. -/
def polyRoot {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (m : ℕ) : 𝓞 L :=
  ⟨((1 : L) - ζ ^ m • α) / (algebraMap K L (ζ - 1)), isIntegral_trans _
      ⟨poly hp hζ u hcong, monic_poly hp hζ u hcong, aeval_poly hp hζ u hcong α e m⟩⟩

theorem roots_poly {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) :
    roots ((poly hp hζ u hcong).map (algebraMap (𝓞 K) L)) =
      (Finset.range p).val.map
        (fun i ↦ ((1 : L) - ζ ^ i • α) / (algebraMap K L (ζ - 1))) := by
  by_cases hα : α = 0
  · rw [hα, zero_pow (NeZero.ne p)] at e
    exact (((algebraMap (𝓞 K) L).isUnit_map u.isUnit).ne_zero e.symm).elim
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  classical
  symm
  apply Multiset.eq_of_le_of_card_le
  · rw [← Finset.image_val_of_injOn, Finset.val_le_iff_val_subset]
    · intro x hx
      simp only [Finset.image_val, Finset.range_val, Multiset.mem_dedup, Multiset.mem_map,
        Multiset.mem_range] at hx
      obtain ⟨m, _, rfl⟩ := hx
      rw [mem_roots, IsRoot.def, eval_map, ← aeval_def, aeval_poly hp hζ u hcong α e]
      exact ((monic_poly hp hζ u hcong).map (algebraMap (𝓞 K) L)).ne_zero
    · intros i hi j hj e
      apply (hζ.map_of_injective (algebraMap K L).injective).injOn_pow_mul hα hi hj
      apply_fun (1 - · * (algebraMap K L ζ - 1)) at e
      dsimp only at e
      simpa only [Nat.cast_one, map_sub, map_one, Algebra.smul_def, map_pow,
        div_mul_cancel₀ _ hζ', sub_sub_cancel] using e
  · simp only [Finset.range_val, Multiset.card_map, Multiset.card_range]
    refine (Polynomial.card_roots' _).trans ?_
    rw [(monic_poly hp hζ u hcong).natDegree_map, natDegree_poly hp hζ]

theorem splits_poly {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) :
    ((poly hp hζ u hcong).map (algebraMap (𝓞 K) L)).Splits := by
  rw [splits_iff_card_roots, roots_poly hp hζ u hcong α e,
    (monic_poly hp hζ u hcong).natDegree_map, natDegree_poly hp hζ,
    Finset.range_val, Multiset.card_map, Multiset.card_range]

theorem map_poly_eq_prod {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) :
    (poly hp hζ u hcong).map (algebraMap (𝓞 K) (𝓞 L)) =
      ∏ i ∈ Finset.range p, (X - C (polyRoot hp hζ u hcong α e i)) := by
  apply map_injective (algebraMap (𝓞 L) L) Subtype.coe_injective
  rw [← coe_mapRingHom, map_prod, coe_mapRingHom, map_map, ← IsScalarTower.algebraMap_eq,
    (splits_poly hp hζ u hcong α e).eq_prod_roots_of_monic ((monic_poly hp hζ u hcong).map _),
    roots_poly hp hζ u hcong α e, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  simp [polyRoot]

include hu in
lemma minpoly_polyRoot'' {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (i) :
    minpoly K (polyRoot hp hζ u hcong α e i : L) =
      (poly hp hζ u hcong).map (algebraMap (𝓞 K) K) := by
  have : IsIntegral K (polyRoot hp hζ u hcong α e i : L) :=
    IsIntegral.tower_top (polyRoot hp hζ u hcong α e i).prop
  apply eq_of_monic_of_associated (minpoly.monic this) ((monic_poly hp hζ u hcong).map _)
  refine Irreducible.associated_of_dvd (minpoly.irreducible this)
    (irreducible_map_poly hp hζ u hcong hu) (minpoly.dvd _ _ ?_)
  rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq, ← aeval_def]
  exact aeval_poly hp hζ u hcong α e i

variable [NumberField K]

include hu in
lemma minpoly_polyRoot' {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (i) :
    minpoly (𝓞 K) (polyRoot hp hζ u hcong α e i : L) = (poly hp hζ u hcong) := by
  apply map_injective (algebraMap (𝓞 K) K) Subtype.coe_injective
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' K]
  · exact minpoly_polyRoot'' hp hζ u hcong hu α e i
  · exact IsIntegral.tower_top (polyRoot hp hζ u hcong α e i).prop

omit [NumberField K] in
lemma separable_poly_aux {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) : Separable ((poly hp hζ u hcong).map
    (algebraMap (𝓞 K) (𝓞 L))) := by
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  rw [map_poly_eq_prod (e := e)]
  refine separable_prod' ?_ (fun _ _ ↦ separable_X_sub_C)
  intros i hi j hj hij
  apply isCoprime_X_sub_C_of_isUnit_sub
  obtain ⟨v, hv⟩ : Associated (hζ.toInteger - 1 : 𝓞 K)
      ((hζ.toInteger : 𝓞 K) ^ j - (hζ.toInteger : 𝓞 K) ^ i) := by
    refine hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out ?_ ?_ ?_
    · rw [Finset.mem_coe, mem_nthRootsFinset (NeZero.pos p), ← pow_mul, mul_comm, pow_mul,
        hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    · rw [Finset.mem_coe, mem_nthRootsFinset (NeZero.pos p), ← pow_mul, mul_comm, pow_mul,
        hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    · exact mt (hζ.toInteger_isPrimitiveRoot.injOn_pow hj hi) hij.symm
  rw [NumberField.RingOfIntegers.ext_iff] at hv
  have hcoe : (algebraMap (𝓞 K) K) (↑hζ.toInteger) = ζ := rfl
  simp only [map_mul, map_sub, map_one, map_pow, hcoe] at hv
  have hα : IsIntegral (𝓞 K) α := by
    apply IsIntegral.of_pow (NeZero.pos p)
    rw [e]
    exact isIntegral_algebraMap
  have : IsUnit (⟨α, isIntegral_trans _ hα⟩ : 𝓞 L) := by
    rw [← isUnit_pow_iff (NeZero.pos p).ne.symm]
    have hpow : (⟨α, isIntegral_trans _ hα⟩ : 𝓞 L) ^ p =
        algebraMap (𝓞 K) (𝓞 L) ↑u := by
      ext
      simp only [SubmonoidClass.coe_pow, e]
      rfl
    rw [hpow]
    exact (algebraMap (𝓞 K) (𝓞 L)).isUnit_map u.isUnit
  convert ((algebraMap (𝓞 K) (𝓞 L)).isUnit_map v.isUnit).mul this using 1
  ext
  simp only [polyRoot, map_sub, map_one, sub_div, one_div, map_sub,
    sub_sub_sub_cancel_left, map_mul, NumberField.RingOfIntegers.map_mk]
  rw [← sub_div, ← sub_smul, ← hv, Algebra.smul_def, map_mul, map_sub, map_one, mul_assoc,
    mul_div_cancel_left₀ _ hζ']
  rfl

include hu in
open scoped KummerExtension in
attribute [local instance] Ideal.Quotient.field in
omit [NumberField K] in
lemma separable_poly (I : Ideal (𝓞 K)) [I.IsMaximal] :
    Separable ((poly hp hζ u hcong).map (Ideal.Quotient.mk I)) := by
  let L := K[p√(u : K)]
  have := Fact.mk (X_pow_sub_C_irreducible_of_prime hpri.out hu)
  let J := I.map (algebraMap (𝓞 K) (𝓞 L))
  let i : 𝓞 K ⧸ I →+* 𝓞 L ⧸ J := Ideal.quotientMap _
    (algebraMap (𝓞 K) (𝓞 L)) Ideal.le_comap_map
  have : Nontrivial (𝓞 L ⧸ J) := by
    apply Ideal.Quotient.nontrivial_iff.mpr
    rw [ne_eq, Ideal.map_eq_top_iff]
    · exact Ideal.IsMaximal.ne_top ‹_›
    · intros x y e
      ext
      exact (algebraMap K L).injective (congr_arg Subtype.val e)
    · intro x
      exact IsIntegral.tower_top (NumberField.RingOfIntegers.isIntegral x)
  rw [← Polynomial.separable_map i, map_map, Ideal.quotientMap_comp_mk, ← map_map]
  exact Separable.map <|
    separable_poly_aux hp hζ u hcong (AdjoinRoot.root _) (root_X_pow_sub_C_pow _ _)

omit [NumberField K] in
lemma polyRoot_spec {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (i) :
    α = (ζ ^ i)⁻¹ • (1 - (ζ - 1) • (polyRoot hp hζ u hcong α e i : L)) := by
  apply smul_right_injective (M := L) (r := ζ ^ i) (pow_ne_zero _ <| hζ.ne_zero
    (NeZero.pos p).ne.symm)
  simp only [polyRoot, map_sub, map_one, NumberField.RingOfIntegers.map_mk,
    Algebra.smul_def (ζ - 1), ← mul_div_assoc,
    mul_div_cancel_left₀ _
      ((hζ.map_of_injective (algebraMap K L).injective).sub_one_ne_zero hpri.out.one_lt),
    sub_sub_cancel, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ <| hζ.ne_zero (NeZero.pos p).ne.symm), one_smul]

omit [NumberField K] in
lemma mem_adjoin_polyRoot {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (i) :
    α ∈ Algebra.adjoin K {(polyRoot hp hζ u hcong α e i : L)} := by
  conv =>
    enter [2]
    rw [polyRoot_spec hp hζ u hcong α e i]
  exact Subalgebra.smul_mem _ (sub_mem (one_mem _)
    (Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton K _) _)) _

include hu hp hζ hcong in
attribute [local instance] Ideal.Quotient.field in
lemma isUnramified (L) [Field L] [Algebra K L] [IsSplittingField K L (X ^ p - C (u : K))] :
    Algebra.Unramified (𝓞 K) (𝓞 L) := by
  let α := polyRoot hp hζ u hcong _ (rootOfSplitsXPowSubC_pow _ L) 0
  have := Polynomial.IsSplittingField.finiteDimensional L (X ^ p - C (u : K))
  have : Module.Finite (𝓞 K) (𝓞 L) := IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)
  have hα : Algebra.adjoin K {(α : L)} = ⊤ := by
    rw [eq_top_iff, ← Algebra.adjoin_root_eq_top_of_isSplittingField
      ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩
      (X_pow_sub_C_irreducible_of_prime hpri.out hu) (rootOfSplitsXPowSubC_pow (u : K) L),
      Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact mem_adjoin_polyRoot hp hζ u hcong _ _ 0
  refine Algebra.unramified_iff_forall.mpr ?_
  rintro ⟨P, hP⟩
  by_cases hPbot : P = ⊥
  · subst P
    exact Algebra.isUnramifiedAt_bot
  refine isUnramifiedAt_of_Separable_minpoly K L P hPbot α (IsIntegral.tower_top α.prop) hα ?_
  rw [minpoly_polyRoot' hp hζ u hcong hu]
  have hPbot' : P.under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot (𝓞 K) hPbot
  have : (P.under (𝓞 K)).IsMaximal :=
    (inferInstance : (P.under (𝓞 K)).IsPrime).isMaximal hPbot'
  exact separable_poly hp hζ u hcong hu (P.under (𝓞 K))

end KummersLemma
