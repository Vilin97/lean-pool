/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.SimpleExtension
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.FiniteGeneration
/-!
# Divisibility of simple Kummer extensions

If `m ∣ n` and the base contains `μₘ`, an `m`-th root of `a` differs from
the `(n/m)`-th power of an `n`-th root by a base-field root of unity. Thus
the chosen simple extensions form an actual tower in the separable closure.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory.Kummer

/-- A simple `m`-Kummer extension is contained in the corresponding
`n`-Kummer extension when `m ∣ n`. -/
theorem chosenSimpleKummerExtension_le_of_dvd
    (K : Type) [Field K]
    (m n : ℕ+) (hmK : ((m : ℕ) : K) ≠ 0)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmuM : (primitiveRoots (m : ℕ) K).Nonempty)
    (hmn : (m : ℕ) ∣ (n : ℕ)) (a : Kˣ) :
    KummerTheory.chosenSimpleKummerExtension K m hmK a ≤
      KummerTheory.chosenSimpleKummerExtension K n hnK a := by
  obtain ⟨q, hq⟩ := hmn
  let Ω := SeparableClosure K
  let αm : Ω := KummerTheory.chosenSimpleKummerRoot K m hmK a
  let αn : Ω := KummerTheory.chosenSimpleKummerRoot K n hnK a
  let Em := KummerTheory.chosenSimpleKummerExtension K m hmK a
  let En := KummerTheory.chosenSimpleKummerExtension K n hnK a
  have hαm : αm ^ (m : ℕ) = algebraMap K Ω (a : K) :=
    KummerTheory.chosenSimpleKummerRoot_pow K m hmK a
  have hαn : αn ^ (n : ℕ) = algebraMap K Ω (a : K) :=
    KummerTheory.chosenSimpleKummerRoot_pow K n hnK a
  have hαmne : αm ≠ 0 := by
    intro hz
    rw [hz, zero_pow m.pos.ne'] at hαm
    exact ((map_ne_zero (algebraMap K Ω)).2 (Units.ne_zero a)) hαm.symm
  have hαnne : αn ≠ 0 := by
    intro hz
    rw [hz, zero_pow n.pos.ne'] at hαn
    exact ((map_ne_zero (algebraMap K Ω)).2 (Units.ne_zero a)) hαn.symm
  let um : Ωˣ := Units.mk0 αm hαmne
  let un : Ωˣ := Units.mk0 αn hαnne
  let ι : Kˣ →* Ωˣ := Units.map (algebraMap K Ω).toMonoidHom
  have humpow : um ^ (m : ℕ) = ι a := by
    apply Units.ext
    exact hαm
  have hunpow : un ^ (n : ℕ) = ι a := by
    apply Units.ext
    exact hαn
  have hqm : q * (m : ℕ) = (n : ℕ) := by
    rw [mul_comm, ← hq]
  let u : Ωˣ := un ^ q / um
  have hu : u ^ (m : ℕ) = 1 := by
    change (un ^ q / um) ^ (m : ℕ) = 1
    rw [div_pow, ← pow_mul, hqm, hunpow, humpow, div_self']
  obtain ⟨ζ, hζ⟩ :=
    KummerTheory.nthRootsOfUnityInBase_of_primitiveRoots
      (K := K) (L := Ω) m hmuM u hu
  have hζmul : ι ζ * um = un ^ q := by
    rw [hζ]
    exact div_mul_cancel (un ^ q) um
  have hum : um = (ι ζ)⁻¹ * un ^ q := by
    calc
      um = (ι ζ)⁻¹ * (ι ζ * um) := by
        rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = (ι ζ)⁻¹ * un ^ q := by rw [hζmul]
  have hαmval : αm = (algebraMap K Ω (ζ : K))⁻¹ * αn ^ q := by
    have h := congrArg Units.val hum
    dsimp only [um, un, ι] at h
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val, Units.coe_map, Units.val_mk0,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] using h
  have hαmmem : αm ∈ En := by
    rw [hαmval]
    have hζmem : algebraMap K Ω (ζ : K) ∈ En :=
      En.algebraMap_mem (ζ : K)
    have hαnmem : αn ∈ En :=
      IntermediateField.subset_adjoin K {αn} (Set.mem_singleton αn)
    exact mul_mem (inv_mem hζmem) (pow_mem hαnmem q)
  change IntermediateField.adjoin K {αm} ≤ En
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  have hx' : x = αm := Set.mem_singleton_iff.mp hx
  rw [hx']
  exact hαmmem

end LocalClassFieldTheory.Kummer
