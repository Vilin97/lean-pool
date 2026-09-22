/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.Abelian
import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.FiniteGeneration
/-!
# the radical-extension construction

Let `Delta` be a subgroup of `Kˣ`.  Inside a fixed separable closure `Omega/K`,
we adjoin *all* roots `beta` of the equations `beta ^ n = a`, for `a ∈ Delta`.
Using all roots makes the construction independent of choices and visibly
stable under `Gal(Omega/K)`.

The hypothesis `(n : K) ≠ 0` is the usual assumption that `n` is prime to
the characteristic.  It is used exactly to make `X ^ n - a` separable.  The
primitive-root hypothesis is used later to make the resulting Galois group
abelian of exponent dividing `n`.
-/

noncomputable section

namespace KummerTheory

section RadicalExtension

open Polynomial

variable {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]

/-- The subgroup `Kˣ^n` of `n`-th powers in the unit group. -/
def unitNthPowersSubgroup (K : Type*) [Field K] (n : ℕ+) : Subgroup Kˣ :=
  (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range

/-- A unit lies in the unit power subgroup exactly when it is an `n`th power of a unit. -/
@[simp] theorem mem_unitNthPowersSubgroup_iff
    (n : ℕ+) {a : Kˣ} :
    a ∈ unitNthPowersSubgroup K n ↔ ∃ b : Kˣ, b ^ (n : ℕ) = a :=
  Iff.rfl

/-- The subgroup-side objects in the Kummer correspondence: subgroups `Delta ≤ Kˣ`
containing `Kˣ^n`. -/
def KummerSubgroup (K : Type*) [Field K] (n : ℕ+) :=
  {Delta : Subgroup Kˣ // unitNthPowersSubgroup K n ≤ Delta}

/-- All roots in `Omega` of the Kummer equations belonging to `Delta`. -/
def kummerRootSet (n : ℕ+) (Delta : Subgroup Kˣ) : Set Omega :=
  {beta | ∃ a : Delta,
    beta ^ (n : ℕ) = algebraMap K Omega (a.1 : K)}

/-- The field `K(√[n]{Delta})` inside the chosen separable closure. -/
def kummerRadicalExtension (n : ℕ+) (Delta : Subgroup Kˣ) :
    IntermediateField K Omega :=
  IntermediateField.adjoin K (kummerRootSet (K := K) (Omega := Omega) n Delta)

/-- Every prescribed Kummer equation has a root in the separable closure.
This is the only point where the characteristic hypothesis is needed. -/
theorem exists_kummerRootSet
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) (Delta : Subgroup Kˣ) (a : Delta) :
    ∃ beta : Omega,
      beta ∈ kummerRootSet (K := K) (Omega := Omega) n Delta ∧
        beta ^ (n : ℕ) = algebraMap K Omega (a.1 : K) := by
  let aOmega : Omega := algebraMap K Omega (a.1 : K)
  have haOmega : aOmega ≠ 0 :=
    (_root_.map_ne_zero (algebraMap K Omega)).2 a.1.ne_zero
  have hnOmega : ((n : ℕ) : Omega) ≠ 0 := by
    rw [← map_natCast (algebraMap K Omega)]
    exact (_root_.map_ne_zero (algebraMap K Omega)).2 hn
  let : IsSepClosed Omega := IsSepClosure.sep_closed K
  obtain ⟨beta, hbeta⟩ := IsSepClosed.exists_root
    (X ^ (n : ℕ) - C aOmega)
    (by rw [degree_X_pow_sub_C n.pos]; exact_mod_cast n.ne_zero)
    (separable_X_pow_sub_C aOmega hnOmega haOmega)
  have hpow : beta ^ (n : ℕ) = aOmega := by
    apply sub_eq_zero.mp
    simpa [IsRoot.def, aOmega] using hbeta
  exact ⟨beta, ⟨a, hpow⟩, hpow⟩

/-- Every element of `Delta` acquires an `n`-th root in the constructed
field.  This is the elementary inclusion `Delta ≤ Delta_{K(√[n]{Delta})}`
in the Kummer correspondence. -/
theorem le_finiteKummerRadicalSubgroup_kummerRadicalExtension
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) (Delta : Subgroup Kˣ) :
    Delta ≤ finiteKummerRadicalSubgroup
      (K := K) (L := kummerRadicalExtension (K := K) (Omega := Omega) n Delta) n := by
  intro a ha
  let aDelta : Delta := ⟨a, ha⟩
  obtain ⟨beta, hbeta, hpow⟩ :=
    exists_kummerRootSet (K := K) (Omega := Omega) n hn Delta aDelta
  let E := kummerRadicalExtension (K := K) (Omega := Omega) n Delta
  let betaE : E :=
    ⟨beta, IntermediateField.subset_adjoin K
      (kummerRootSet (K := K) (Omega := Omega) n Delta) hbeta⟩
  have hbetaE : betaE ≠ 0 := by
    intro hzero
    have hbeta_zero : beta = 0 := congrArg Subtype.val hzero
    have hmap_zero : algebraMap K Omega (a : K) = 0 := by
      rw [← hpow, hbeta_zero, zero_pow n.ne_zero]
    exact ((_root_.map_ne_zero (algebraMap K Omega)).2 a.ne_zero) hmap_zero
  refine ⟨Units.mk0 betaE hbetaE, ?_⟩
  apply Units.ext
  apply Subtype.ext
  exact hpow

/-- In particular, for an admissible subgroup-side object, the radical
subgroup recovered from its field still contains `Kˣ^n`. -/
theorem unitNthPowersSubgroup_le_constructedRadical
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) (Delta : KummerSubgroup K n) :
    unitNthPowersSubgroup K n ≤ finiteKummerRadicalSubgroup
      (K := K)
      (L := kummerRadicalExtension (K := K) (Omega := Omega) n Delta.1) n :=
  Delta.2.trans
    (le_finiteKummerRadicalSubgroup_kummerRadicalExtension n hn Delta.1)

/-- A Kummer root is nonzero because its prescribed power is a unit. -/
theorem kummerRootSet_ne_zero
    (n : ℕ+) (Delta : Subgroup Kˣ) {beta : Omega}
    (hbeta : beta ∈ kummerRootSet (K := K) (Omega := Omega) n Delta) :
    beta ≠ 0 := by
  obtain ⟨a, ha⟩ := hbeta
  intro hzero
  have : algebraMap K Omega (a.1 : K) = 0 := by
    rw [← ha, hzero, zero_pow n.ne_zero]
  exact ((_root_.map_ne_zero (algebraMap K Omega)).2 a.1.ne_zero) this

/-- Every `K`-automorphism of the separable closure preserves the full root
set. -/
theorem kummerRootSet_mapsTo
    (n : ℕ+) (Delta : Subgroup Kˣ) (sigma : Gal(Omega/K)) :
    Set.MapsTo sigma
      (kummerRootSet (K := K) (Omega := Omega) n Delta)
      (kummerRootSet (K := K) (Omega := Omega) n Delta) := by
  rintro beta ⟨a, hbeta⟩
  refine ⟨a, ?_⟩
  calc
    sigma beta ^ (n : ℕ) = sigma (beta ^ (n : ℕ)) :=
      (map_pow sigma beta (n : ℕ)).symm
    _ = sigma (algebraMap K Omega (a.1 : K)) := congrArg sigma hbeta
    _ = algebraMap K Omega (a.1 : K) := sigma.commutes (a.1 : K)

/-- Because inverse automorphisms preserve the same equations, the root set
is carried onto itself, not merely into itself. -/
theorem kummerRootSet_image
    (n : ℕ+) (Delta : Subgroup Kˣ) (sigma : Gal(Omega/K)) :
    sigma '' kummerRootSet (K := K) (Omega := Omega) n Delta =
      kummerRootSet (K := K) (Omega := Omega) n Delta := by
  apply Set.Subset.antisymm
  · rintro _ ⟨beta, hbeta, rfl⟩
    exact kummerRootSet_mapsTo n Delta sigma hbeta
  · intro beta hbeta
    refine ⟨sigma.symm beta, kummerRootSet_mapsTo n Delta sigma.symm hbeta, ?_⟩
    exact sigma.apply_symm_apply beta

/-- The actual radical field is stable under every automorphism of the
separable closure. -/
theorem kummerRadicalExtension_map
    (n : ℕ+) (Delta : Subgroup Kˣ) (sigma : Gal(Omega/K)) :
    (kummerRadicalExtension (K := K) (Omega := Omega) n Delta).map sigma =
      kummerRadicalExtension (K := K) (Omega := Omega) n Delta := by
  rw [kummerRadicalExtension, IntermediateField.adjoin_map]
  congr 1
  exact kummerRootSet_image n Delta sigma

/-- The stability just proved is precisely normality over `K`. -/
theorem kummerRadicalExtension_normal
    [IsSepClosure K Omega]
    (n : ℕ+) (Delta : Subgroup Kˣ) :
    Normal K (kummerRadicalExtension (K := K) (Omega := Omega) n Delta) := by
  rw [IntermediateField.normal_iff_forall_map_eq']
  exact kummerRadicalExtension_map n Delta

/-- The extension `K(√[n]{Delta})/K` is Galois.  Separability comes from the
ambient separable closure and normality from invariance of the full root
set. -/
theorem kummerRadicalExtension_isGalois
    [IsSepClosure K Omega]
    (n : ℕ+) (Delta : Subgroup Kˣ) :
    IsGalois K (kummerRadicalExtension (K := K) (Omega := Omega) n Delta) := by
  rw [isGalois_iff]
  exact ⟨inferInstance, kummerRadicalExtension_normal n Delta⟩

/-- On every radical generator, two automorphisms commute.  The quotient
`sigma(beta) / beta` is an `n`-th root of unity, hence lies in and is fixed
by the base field under the primitive-root hypothesis. -/
theorem kummerRadicalExtension_generator_commute
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : Subgroup Kˣ)
    (sigma tau : Gal(kummerRadicalExtension (K := K) (Omega := Omega) n Delta/K))
    {beta : Omega}
    (hbeta : beta ∈ kummerRootSet (K := K) (Omega := Omega) n Delta) :
    (sigma * tau)
        ⟨beta, IntermediateField.subset_adjoin K
          (kummerRootSet (K := K) (Omega := Omega) n Delta) hbeta⟩ =
      (tau * sigma)
        ⟨beta, IntermediateField.subset_adjoin K
          (kummerRootSet (K := K) (Omega := Omega) n Delta) hbeta⟩ := by
  let E := kummerRadicalExtension (K := K) (Omega := Omega) n Delta
  let betaE : E :=
    ⟨beta, IntermediateField.subset_adjoin K
      (kummerRootSet (K := K) (Omega := Omega) n Delta) hbeta⟩
  let betaUnit : Eˣ := Units.mk0 betaE (by
    intro hzero
    apply kummerRootSet_ne_zero n Delta hbeta
    exact congrArg Subtype.val hzero)
  obtain ⟨a, ha⟩ := hbeta
  have hpow : betaUnit ^ (n : ℕ) =
      Units.map (algebraMap K E).toMonoidHom a.1 := by
    apply Units.ext
    apply Subtype.ext
    exact ha
  have hpow_fixed : ∀ rho : Gal(E/K),
      rho • (betaUnit ^ (n : ℕ)) = betaUnit ^ (n : ℕ) := by
    intro rho
    rw [hpow]
    exact RadicalDatum.smul_algebraMap_unit (K := K) (L := E) rho a.1
  let hbase : NthRootsOfUnityInBase (K := K) (L := E) n :=
    nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := E) n hmu
  have hquot_pow (rho : Gal(E/K)) :
      rootQuotient (K := K) (L := E) betaUnit rho ^ (n : ℕ) = 1 :=
    rootQuotient_pow_eq_one_of_pow_fixed (K := K) (L := E) hpow_fixed rho
  have hquot_fixed (rho eta : Gal(E/K)) :
      eta • rootQuotient (K := K) (L := E) betaUnit rho =
        rootQuotient (K := K) (L := E) betaUnit rho :=
    nthRootsOfUnity_fixed (K := K) (L := E) n hbase eta _ (hquot_pow rho)
  have hquot_commute :
      rootQuotient (K := K) (L := E) betaUnit (sigma * tau) =
        rootQuotient (K := K) (L := E) betaUnit (tau * sigma) := by
    rw [rootQuotient_mul, rootQuotient_mul,
      hquot_fixed tau sigma, hquot_fixed sigma tau, mul_comm]
  have hunit_commute : (sigma * tau) • betaUnit = (tau * sigma) • betaUnit := by
    rw [← rootQuotient_mul_right (K := K) (L := E) betaUnit (sigma * tau),
      ← rootQuotient_mul_right (K := K) (L := E) betaUnit (tau * sigma),
      hquot_commute]
  exact congrArg Units.val hunit_commute

/-- Hence `Gal(K(√[n]{Delta})/K)` is commutative.  Equality is checked on
the radical generators of the adjoin. -/
theorem kummerRadicalExtension_isMulCommutative
    [IsSepClosure K Omega]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : Subgroup Kˣ) :
    IsMulCommutative Gal(kummerRadicalExtension (K := K) (Omega := Omega) n Delta/K) := by
  refine ⟨⟨fun sigma tau => ?_⟩⟩
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.adjoin_algHom_ext K
  intro beta hbeta
  exact kummerRadicalExtension_generator_commute n hmu Delta sigma tau hbeta

/-- On every radical generator, the `n`-th power of an automorphism is the
identity. -/
theorem kummerRadicalExtension_generator_pow_eq_one
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : Subgroup Kˣ)
    (sigma : Gal(kummerRadicalExtension (K := K) (Omega := Omega) n Delta/K))
    {beta : Omega}
    (hbeta : beta ∈ kummerRootSet (K := K) (Omega := Omega) n Delta) :
    (sigma ^ (n : ℕ))
        ⟨beta, IntermediateField.subset_adjoin K
          (kummerRootSet (K := K) (Omega := Omega) n Delta) hbeta⟩ =
      ⟨beta, IntermediateField.subset_adjoin K
        (kummerRootSet (K := K) (Omega := Omega) n Delta) hbeta⟩ := by
  let E := kummerRadicalExtension (K := K) (Omega := Omega) n Delta
  let betaE : E :=
    ⟨beta, IntermediateField.subset_adjoin K
      (kummerRootSet (K := K) (Omega := Omega) n Delta) hbeta⟩
  let betaUnit : Eˣ := Units.mk0 betaE (by
    intro hzero
    apply kummerRootSet_ne_zero n Delta hbeta
    exact congrArg Subtype.val hzero)
  obtain ⟨a, ha⟩ := hbeta
  have hpow : betaUnit ^ (n : ℕ) =
      Units.map (algebraMap K E).toMonoidHom a.1 := by
    apply Units.ext
    apply Subtype.ext
    exact ha
  have hpow_fixed : ∀ rho : Gal(E/K),
      rho • (betaUnit ^ (n : ℕ)) = betaUnit ^ (n : ℕ) := by
    intro rho
    rw [hpow]
    exact RadicalDatum.smul_algebraMap_unit (K := K) (L := E) rho a.1
  let hbase : NthRootsOfUnityInBase (K := K) (L := E) n :=
    nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := E) n hmu
  let q : Eˣ := rootQuotient (K := K) (L := E) betaUnit sigma
  have hq_pow : q ^ (n : ℕ) = 1 :=
    rootQuotient_pow_eq_one_of_pow_fixed (K := K) (L := E) hpow_fixed sigma
  have hq_fixed (rho : Gal(E/K)) : rho • q = q :=
    nthRootsOfUnity_fixed (K := K) (L := E) n hbase rho q hq_pow
  have hquot_pow : ∀ m : ℕ,
      rootQuotient (K := K) (L := E) betaUnit (sigma ^ m) = q ^ m := by
    intro m
    induction m with
    | zero => simp [q]
    | succ m ih =>
        rw [pow_succ, rootQuotient_mul, hq_fixed, ih]
        exact (pow_succ' q m).symm
  have hquot_one :
      rootQuotient (K := K) (L := E) betaUnit (sigma ^ (n : ℕ)) = 1 := by
    rw [hquot_pow, hq_pow]
  have hunit_fixed : (sigma ^ (n : ℕ)) • betaUnit = betaUnit :=
    (rootQuotient_eq_one_iff (K := K) (L := E) betaUnit
      (sigma ^ (n : ℕ))).1 hquot_one
  exact congrArg Units.val hunit_fixed

/-- Every element of the Galois group has `n`-th power one. -/
theorem kummerRadicalExtension_galois_pow_eq_one
    [IsSepClosure K Omega]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : Subgroup Kˣ)
    (sigma : Gal(kummerRadicalExtension (K := K) (Omega := Omega) n Delta/K)) :
    sigma ^ (n : ℕ) = 1 := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.adjoin_algHom_ext K
  intro beta hbeta
  exact kummerRadicalExtension_generator_pow_eq_one n hmu Delta sigma hbeta

/-- the Kummer correspondence, forward construction: adjoining the radicals attached to
`Delta` produces an abelian Galois extension. -/
theorem kummerRadicalExtension_isAbelianGalois
    [IsSepClosure K Omega]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : Subgroup Kˣ) :
    IsAbelianGalois K
      (kummerRadicalExtension (K := K) (Omega := Omega) n Delta) where
  toIsGalois := kummerRadicalExtension_isGalois n Delta
  toIsMulCommutative := kummerRadicalExtension_isMulCommutative n hmu Delta

end RadicalExtension

end KummerTheory
