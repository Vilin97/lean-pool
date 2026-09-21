/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebraNormSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.CanonicalKummerNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.MathlibInterface
import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.SimpleExtension
import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.FiniteGeneration
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.LocalField.Basic
/-!
# Chosen Kummer radical: norm index and power-class degree

Implementation-level comparisons for the chosen simple Kummer extension. The
reader-facing Hilbert-symbol theorems state these results without exposing this
particular choice of a radical in their types.
-/

noncomputable section

namespace ClassFieldTheory.LocalClassFieldTheory.Kummer

/-- The unit-norm image of a possibly reducible Kummer algebra has index
equal to the degree of the chosen simple radical field, not necessarily `n`. -/
theorem kummerAlgebraNormSubgroup_index_eq_chosenRadicalDegree
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ) :
    (kummerAlgebraNormSubgroup K n a).index =
      Module.finrank K (KummerTheory.chosenSimpleKummerExtension K n hnK a) := by
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  let : FiniteDimensional K E :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional K n hnK a
  let : IsAbelianGalois K E :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu a
  have hnorm : kummerAlgebraNormSubgroup K n a = fieldNormSubgroup K E := by
    apply Subgroup.ext
    intro b
    change
      (∃ y : (KummerAlgebra K n a)ˣ,
        Units.map (Algebra.norm K) y = b) ↔
      (∃ z : Eˣ, Units.map (Algebra.norm K) z = b)
    have hcomparison :=
      LocalClassFieldTheory.Kummer.adjoinRoot_norm_iff_chosenSimpleKummerNorm
        K n hnK hmu a b
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨z, hz⟩ := hcomparison.mp ⟨y, congrArg Units.val hy⟩
      refine ⟨z, ?_⟩
      apply Units.ext
      exact hz
    · rintro ⟨z, hz⟩
      obtain ⟨y, hy⟩ := hcomparison.mpr ⟨z, congrArg Units.val hz⟩
      refine ⟨y, ?_⟩
      apply Units.ext
      exact hy
  change (kummerAlgebraNormSubgroup K n a).index = Module.finrank K E
  rw [hnorm]
  exact LocalCFT.fieldNormSubgroup_index_eq_finrank K E

private theorem chosenRoot_pow_mem_base_iff_powerClass_pow_eq_one
    (K : Type) [Field K] (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ) (m : ℕ) :
    let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
    let β := KummerTheory.chosenSimpleKummerRootUnit K n hnK a
    ((β ^ m : Eˣ) : E) ∈ Set.range (algebraMap K E) ↔
      (powerClass K n a) ^ m = 1 := by
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  let β : Eˣ := KummerTheory.chosenSimpleKummerRootUnit K n hnK a
  let ι : Kˣ →* Eˣ := Units.map (algebraMap K E).toMonoidHom
  have hβ : β ^ (n : ℕ) = ι a :=
    KummerTheory.chosenSimpleKummerRootUnit_pow K n hnK a
  have hι : Function.Injective ι :=
    Units.map_injective (algebraMap K E).injective
  constructor
  · rintro ⟨b, hb⟩
    have hbne : b ≠ 0 := by
      intro hz
      have hzero : ((β ^ m : Eˣ) : E) = 0 := by
        simpa only [hz, map_zero] using hb.symm
      exact (β ^ m).ne_zero hzero
    let bu : Kˣ := Units.mk0 b hbne
    have hβm : β ^ m = ι bu := by
      apply Units.ext
      exact hb.symm
    have ha : a ^ m = bu ^ (n : ℕ) := by
      apply hι
      calc
        ι (a ^ m) = (ι a) ^ m := map_pow ι a m
        _ = (β ^ (n : ℕ)) ^ m := by rw [hβ]
        _ = (β ^ m) ^ (n : ℕ) := pow_right_comm β (n : ℕ) m
        _ = (ι bu) ^ (n : ℕ) := by rw [hβm]
        _ = ι (bu ^ (n : ℕ)) := (map_pow ι bu (n : ℕ)).symm
    rw [← map_pow (powerClass K n) a m]
    exact (QuotientGroup.eq_one_iff (a ^ m)).2 ⟨bu, ha.symm⟩
  · intro hclass
    have ha : a ^ m ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range :=
      (QuotientGroup.eq_one_iff (a ^ m)).1
        ((map_pow (powerClass K n) a m).symm.trans hclass)
    obtain ⟨bu, hbu⟩ := ha
    have hbu' : bu ^ (n : ℕ) = a ^ m := hbu
    let u : Eˣ := β ^ m / ι bu
    have hu : u ^ (n : ℕ) = 1 := by
      have hnum : (β ^ m) ^ (n : ℕ) = ι (a ^ m) := by
        calc
          (β ^ m) ^ (n : ℕ) = (β ^ (n : ℕ)) ^ m := pow_right_comm β m (n : ℕ)
          _ = (ι a) ^ m := by rw [hβ]
          _ = ι (a ^ m) := (map_pow ι a m).symm
      have hden : (ι bu) ^ (n : ℕ) = ι (a ^ m) := by
        rw [← map_pow, hbu']
      change (β ^ m / ι bu) ^ (n : ℕ) = 1
      rw [div_pow, hnum, hden, div_self']
    obtain ⟨ζ, hζ⟩ :=
      KummerTheory.nthRootsOfUnityInBase_of_primitiveRoots
        (K := K) (L := E) n hmu u hu
    refine ⟨(ζ * bu : Kˣ), ?_⟩
    have hβm : β ^ m = ι (ζ * bu) := by
      calc
        β ^ m = u * ι bu := by
          dsimp only [u]
          exact (div_mul_cancel (β ^ m) (ι bu)).symm
        _ = ι ζ * ι bu := by rw [hζ]
        _ = ι (ζ * bu) := (map_mul ι ζ bu).symm
    exact (congrArg Units.val hβm).symm

/-- A chosen simple Kummer extension has degree equal to the order of its
defining power class. This includes the reducible case `a = 1`. -/
theorem chosenSimpleKummerExtension_finrank_eq_powerClassOrder
    (K : Type) [Field K] (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ) :
    Module.finrank K (KummerTheory.chosenSimpleKummerExtension K n hnK a) =
      orderOf (powerClass K n a) := by
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  let β : Eˣ := KummerTheory.chosenSimpleKummerRootUnit K n hnK a
  let ι : Kˣ →* Eˣ := Units.map (algebraMap K E).toMonoidHom
  let : FiniteDimensional K E :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional K n hnK a
  let : IsAbelianGalois K E :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu a
  have hβ : β ^ (n : ℕ) = ι a :=
    KummerTheory.chosenSimpleKummerRootUnit_pow K n hnK a
  have hβint : IsIntegral K (β : E) := by
    apply IsIntegral.of_pow n.pos
    have h := congrArg Units.val hβ
    have hpow : (β : E) ^ (n : ℕ) = (ι a : E) := by
      simpa only [Units.val_pow_eq_pow_val] using h
    rw [hpow]
    change IsIntegral K (algebraMap K E (a : K))
    exact isIntegral_algebraMap
  have htop : IntermediateField.adjoin K {(β : E)} = ⊤ :=
    KummerTheory.chosenSimpleKummerExtension_adjoin_root_eq_top K n hnK a
  have hdegree : Module.finrank K E = (minpoly K (β : E)).natDegree := by
    calc
      Module.finrank K E =
          Module.finrank K (IntermediateField.adjoin K {(β : E)}) := by
            rw [htop]
            exact (IntermediateField.finrank_top').symm
      _ = (minpoly K (β : E)).natDegree :=
        IntermediateField.adjoin.finrank hβint
  let d := orderOf (powerClass K n a)
  let e := Module.finrank K E
  have hclass_n : (powerClass K n a) ^ (n : ℕ) = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (a ^ (n : ℕ))).2 ⟨a, rfl⟩
  have hdpos : 0 < d :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨(n : ℕ), n.pos, hclass_n⟩).orderOf_pos
  have hβd : ((β ^ d : Eˣ) : E) ∈ Set.range (algebraMap K E) :=
    (chosenRoot_pow_mem_base_iff_powerClass_pow_eq_one K n hnK hmu a d).2
      (pow_orderOf_eq_one (powerClass K n a))
  obtain ⟨c, hc⟩ := hβd
  have hpolyroot : Polynomial.aeval (β : E)
      (Polynomial.X ^ d - Polynomial.C c) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    exact sub_eq_zero.mpr hc.symm
  have hdegree_le : e ≤ d := by
    rw [show e = (minpoly K (β : E)).natDegree from hdegree]
    calc
      (minpoly K (β : E)).natDegree ≤
          (Polynomial.X ^ d - Polynomial.C c).natDegree :=
        Polynomial.natDegree_le_of_dvd
          (minpoly.dvd K (β : E) hpolyroot)
          (Polynomial.X_pow_sub_C_ne_zero hdpos c)
      _ = d := Polynomial.natDegree_X_pow_sub_C
  let χ := KummerTheory.chosenSimpleKummerRootCharacter K n hnK hmu a
  have hcard : Nat.card Gal(E/K) = e :=
    IsGalois.card_aut_eq_finrank K E
  have hquot_pow (σ : Gal(E/K)) :
      KummerTheory.rootQuotient (K := K) (L := E) β σ ^ e = 1 := by
    have hσ : σ ^ e = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    have hχ : (χ σ) ^ e = 1 := by
      rw [← map_pow, hσ, map_one]
    have hval := congrArg Subtype.val hχ
    rw [KummerTheory.chosenSimpleKummerRootCharacter_apply] at hval
    exact hval
  have hβe_fixed (σ : Gal(E/K)) :
      Units.map σ.toMonoidHom (β ^ e) = β ^ e := by
    have hσβ : Units.map σ.toMonoidHom β =
        KummerTheory.rootQuotient (K := K) (L := E) β σ * β := by
      simp only [KummerTheory.rootQuotient]
      rw [div_mul_cancel]
      simp only [AlgEquiv.smul_units_def]
      apply Units.ext
      rfl
    calc
      Units.map σ.toMonoidHom (β ^ e) = (Units.map σ.toMonoidHom β) ^ e :=
        map_pow (Units.map σ.toMonoidHom) β e
      _ = (KummerTheory.rootQuotient (K := K) (L := E) β σ * β) ^ e := by
        rw [hσβ]
      _ = (KummerTheory.rootQuotient (K := K) (L := E) β σ) ^ e * β ^ e :=
        mul_pow _ _ _
      _ = β ^ e := by rw [hquot_pow σ, one_mul]
  have hβe : ((β ^ e : Eˣ) : E) ∈ Set.range (algebraMap K E) := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed
      (((β ^ e : Eˣ) : E))).2
    intro σ
    have hval := congrArg Units.val (hβe_fixed σ)
    change σ (((β ^ e : Eˣ) : E)) = ((β ^ e : Eˣ) : E) at hval
    exact hval
  have hclass_e : (powerClass K n a) ^ e = 1 :=
    (chosenRoot_pow_mem_base_iff_powerClass_pow_eq_one K n hnK hmu a e).1 hβe
  have hdvd : d ∣ e := orderOf_dvd_of_pow_eq_one hclass_e
  have hdegree_ge : d ≤ e := Nat.le_of_dvd Module.finrank_pos hdvd
  exact Nat.le_antisymm hdegree_le hdegree_ge

end ClassFieldTheory.LocalClassFieldTheory.Kummer
