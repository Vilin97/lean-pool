/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.SimpleExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient
import Mathlib.GroupTheory.Coset.Card
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
/-!
# Norm witnesses in simple Kummer extensions

This file constructs a field-generic norm witness for the pair formed by a
unit and its nonzero complement.  The construction uses the finite quotient
of the roots of unity by the image of the simple Kummer character, so it does
not require the defining power polynomial to be irreducible.
-/

noncomputable section

namespace KummerTheory

open scoped BigOperators

variable (K : Type) [Field K]

/-- If both `a` and `1 - a` are nonzero, then `a` is a norm from the simple
Kummer extension obtained by adjoining an `n`-th root of `1 - a`. -/
theorem unit_mem_localNormSubgroup_chosenSimpleKummerExtension_one_sub
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : Kˣ) (h_one_sub : 1 - (a : K) ≠ 0) :
    a ∈ LocalFieldTheory.localNormSubgroup K
      (chosenSimpleKummerExtension K n hnK
        (Units.mk0 (1 - (a : K)) h_one_sub)) := by
  classical
  let b : Kˣ := Units.mk0 (1 - (a : K)) h_one_sub
  let E := chosenSimpleKummerExtension K n hnK b
  let beta : Eˣ := chosenSimpleKummerRootUnit K n hnK b
  let _ : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let _ : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let _ : MulDistribMulAction Gal(E / K) Eˣ :=
    AlgEquiv.instMulDistribMulActionUnits
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let mu := nthRootsSubgroup E (n : ℕ)
  let chi : Gal(E / K) →* mu :=
    chosenSimpleKummerRootCharacter K n hnK hmu b
  let H : Subgroup mu := chi.range
  let Q := mu ⧸ H
  let _ : Fintype mu := nthRootsSubgroupFintype E (n : ℕ)
  let _ : Fintype Q := Fintype.ofFinite _
  have hchi : Function.Injective chi := by
    simpa only [chi, E] using
      chosenSimpleKummerRootCharacter_injective K n hnK hmu b
  let indexMap : Q × Gal(E / K) → mu := fun p =>
    Quotient.out p.1 * chi p.2
  have indexMap_injective : Function.Injective indexMap := by
    rintro ⟨q, sigma⟩ ⟨r, tau⟩ h
    have hchi_sigma : chi sigma ∈ H := ⟨sigma, rfl⟩
    have hchi_tau : chi tau ∈ H := ⟨tau, rfl⟩
    have hq : q = r := by
      have hm := congrArg
        (fun z : mu => (QuotientGroup.mk z : Q)) h
      rw [QuotientGroup.mk_mul_of_mem _ hchi_sigma,
        QuotientGroup.mk_mul_of_mem _ hchi_tau] at hm
      simpa only [Quotient.out_eq'] using hm
    subst r
    have hsigma : sigma = tau := by
      apply hchi
      exact mul_left_cancel h
    subst tau
    rfl
  have indexMap_surjective : Function.Surjective indexMap := by
    intro z
    let q : Q := QuotientGroup.mk z
    have hrel : (Quotient.out q) ⁻¹ * z ∈ H := by
      apply QuotientGroup.leftRel_apply.mp
      exact @Quotient.exact' mu (QuotientGroup.leftRel H) _ _
        (by simpa only [q] using Quotient.out_eq' q)
    change (Quotient.out q) ⁻¹ * z ∈ chi.range at hrel
    rcases hrel with ⟨sigma, hsigma⟩
    refine ⟨(q, sigma), ?_⟩
    change Quotient.out q * chi sigma = z
    rw [hsigma]
    simp
  let indexEquiv : Q × Gal(E / K) ≃ mu :=
    Equiv.ofBijective indexMap ⟨indexMap_injective, indexMap_surjective⟩
  have indexEquiv_apply (q : Q) (sigma : Gal(E / K)) :
      indexEquiv (q, sigma) = Quotient.out q * chi sigma := by
    rfl
  have factor_ne (q : Q) :
      1 - ((((Quotient.out q : mu).1 : Eˣ) : E) * (beta : E)) ≠ 0 := by
    intro hzero
    have hmul : (Quotient.out q : mu).1 * beta = 1 := by
      apply Units.ext
      exact (sub_eq_zero.mp hzero).symm
    have hb_map : Units.map (algebraMap K E).toMonoidHom b = 1 := by
      calc
        Units.map (algebraMap K E).toMonoidHom b = beta ^ (n : ℕ) :=
          (chosenSimpleKummerRootUnit_pow K n hnK b).symm
        _ = ((Quotient.out q : mu).1 * beta) ^ (n : ℕ) := by
          rw [mul_pow, (Quotient.out q : mu).2, one_mul]
        _ = 1 := by rw [hmul, one_pow]
    have hb : b = 1 :=
      (Units.map_injective (f := (algebraMap K E).toMonoidHom)
        (algebraMap K E).injective) hb_map
    have hb_val := congrArg Units.val hb
    change 1 - (a : K) = 1 at hb_val
    exact a.ne_zero (sub_eq_self.mp hb_val)
  let factor (q : Q) : Eˣ :=
    Units.mk0
      (1 - ((((Quotient.out q : mu).1 : Eˣ) : E) * (beta : E)))
      (factor_ne q)
  let witness : Eˣ := ∏ q : Q, factor q
  let hbase : NthRootsOfUnityInBase (K := K) (L := E) n :=
    nthRootsOfUnityInBase_of_primitiveRoots
      (K := K) (L := E) n hmu
  have chi_mul_beta (sigma : Gal(E / K)) :
      (chi sigma).1 * beta = Units.map sigma.toMonoidHom beta := by
    change
      (chosenSimpleKummerRootCharacter K n hnK hmu b sigma).1 * beta =
        Units.map sigma.toMonoidHom beta
    rw [chosenSimpleKummerRootCharacter_apply]
    change
      rootQuotient (K := K) (L := E) beta sigma * beta =
        Units.map sigma.toMonoidHom beta
    simp only [rootQuotient]
    rw [div_mul_cancel]
    simp only [AlgEquiv.smul_units_def]
    apply Units.ext
    rfl
  have map_factor (sigma : Gal(E / K)) (q : Q) :
      sigma (factor q : E) =
        1 - (((((Quotient.out q : mu) * chi sigma).1 : Eˣ) : E) *
          (beta : E)) := by
    have hroot_fixed := nthRootsOfUnity_fixed n hbase sigma
      (Quotient.out q : mu).1 (Quotient.out q : mu).2
    change
      Units.map sigma.toMonoidHom (Quotient.out q : mu).1 =
        (Quotient.out q : mu).1 at hroot_fixed
    have hroot_fixed_val := congrArg Units.val hroot_fixed
    have hbeta_val := congrArg Units.val (chi_mul_beta sigma)
    change
      sigma
          (1 - (((Quotient.out q : mu).1 : Eˣ) : E) * (beta : E)) =
        1 - (((((Quotient.out q : mu) * chi sigma).1 : Eˣ) : E) *
          (beta : E))
    rw [map_sub, map_one, map_mul]
    change
      sigma ((((Quotient.out q : mu).1 : Eˣ) : E)) =
        (((Quotient.out q : mu).1 : Eˣ) : E) at hroot_fixed_val
    change
      ((((chi sigma).1 * beta : Eˣ) : E)) = sigma (beta : E) at hbeta_val
    rw [hroot_fixed_val, ← hbeta_val]
    change
      1 - ((((Quotient.out q : mu).1 : Eˣ) : E) *
          ((((chi sigma).1 : Eˣ) : E) * (beta : E))) =
        1 - (((((Quotient.out q : mu).1 : Eˣ) : E) *
          (((chi sigma).1 : Eˣ) : E)) * (beta : E))
    rw [mul_assoc]
  let rootsEquiv :
      mu ≃ {z : E // z ∈ Polynomial.nthRootsFinset (n : ℕ) (1 : E)} :=
    { toFun := fun z =>
        ⟨((z.1 : Eˣ) : E), by
          rw [Polynomial.mem_nthRootsFinset n.pos]
          exact congrArg Units.val z.2⟩
      invFun := fun z =>
        ⟨Units.mk0 z.1
            (Polynomial.ne_zero_of_mem_nthRootsFinset one_ne_zero z.2),
          by
            apply Units.ext
            exact (Polynomial.mem_nthRootsFinset n.pos (1 : E)).1 z.2⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Units.ext
        rfl
      right_inv := by
        intro z
        apply Subtype.ext
        rfl }
  have roots_product :
      Finset.univ.prod
          (fun z : mu => 1 - (((z.1 : Eˣ) : E) * (beta : E))) =
        1 - (beta : E) ^ (n : ℕ) := by
    obtain ⟨zeta, hzeta_mem⟩ := hmu
    have hzeta : IsPrimitiveRoot zeta (n : ℕ) :=
      (mem_primitiveRoots n.pos).1 hzeta_mem
    have hzeta_E : IsPrimitiveRoot (algebraMap K E zeta) (n : ℕ) :=
      hzeta.map_of_injective (algebraMap K E).injective
    calc
      Finset.univ.prod
          (fun z : mu => 1 - (((z.1 : Eˣ) : E) * (beta : E))) =
          Finset.univ.prod
            (fun z : {z : E //
                z ∈ Polynomial.nthRootsFinset (n : ℕ) (1 : E)} =>
              1 - ((z : E) * (beta : E))) := by
        exact Fintype.prod_equiv rootsEquiv _ _ (fun _ => rfl)
      _ = (Polynomial.nthRootsFinset (n : ℕ) (1 : E)).prod
            (fun z => 1 - z * (beta : E)) := by
        simpa only using
          (Finset.prod_coe_sort
            (s := Polynomial.nthRootsFinset (n : ℕ) (1 : E))
            (f := fun z => 1 - z * (beta : E)))
      _ = 1 - (beta : E) ^ (n : ℕ) := by
        simpa only [one_pow] using
          (hzeta_E.pow_sub_pow_eq_prod_sub_mul
            (1 : E) (beta : E) n.pos).symm
  change a ∈ (LocalFieldTheory.normUnits K E).range
  refine ⟨witness, ?_⟩
  apply Units.ext
  apply (algebraMap K E).injective
  change
    algebraMap K E (Algebra.norm K (witness : E)) =
      algebraMap K E (a : K)
  calc
    algebraMap K E (Algebra.norm K (witness : E)) =
        Finset.univ.prod
          (fun sigma : Gal(E / K) => sigma (witness : E)) :=
      Algebra.norm_eq_prod_automorphisms K (witness : E)
    _ = Finset.univ.prod (fun sigma : Gal(E / K) =>
          Finset.univ.prod (fun q : Q => sigma (factor q : E))) := by
      apply Finset.prod_congr rfl
      intro sigma _
      simp only [witness, Units.coe_prod, map_prod]
    _ = Finset.univ.prod (fun sigma : Gal(E / K) =>
          Finset.univ.prod (fun q : Q =>
            1 - (((((Quotient.out q : mu) * chi sigma).1 : Eˣ) : E) *
              (beta : E)))) := by
      apply Finset.prod_congr rfl
      intro sigma _
      apply Finset.prod_congr rfl
      intro q _
      exact map_factor sigma q
    _ = Finset.univ.prod (fun p : Q × Gal(E / K) =>
          1 - (((((Quotient.out p.1 : mu) * chi p.2).1 : Eˣ) : E) *
            (beta : E))) := by
      exact (Fintype.prod_prod_type_right' _).symm
    _ = Finset.univ.prod
          (fun z : mu => 1 - (((z.1 : Eˣ) : E) * (beta : E))) := by
      exact Fintype.prod_equiv indexEquiv _ _ (by
        intro p
        rw [indexEquiv_apply p.1 p.2])
    _ = 1 - (beta : E) ^ (n : ℕ) := roots_product
    _ = algebraMap K E (a : K) := by
      have hbeta_pow := congrArg Units.val
        (chosenSimpleKummerRootUnit_pow K n hnK b)
      change
        (beta : E) ^ (n : ℕ) =
          algebraMap K E (1 - (a : K)) at hbeta_pow
      rw [hbeta_pow, map_sub, map_one]
      ring

end KummerTheory
