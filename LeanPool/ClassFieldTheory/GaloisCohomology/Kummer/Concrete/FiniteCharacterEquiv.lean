/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.RadicalQuotient
/-!
# finite Kummer character isomorphism

For an actual finite Galois extension `L/K`, this file constructs

`Delta = {a : Kˣ | there is beta : Lˣ with beta ^ n = a}`

as a subgroup, chooses one root for each element only after the subgroup has
been constructed, and proves the character isomorphism

`Delta / (Delta intersect Kˣ^n) ~= Hom(Gal(L/K), mu_n)`.

There is no multiplicative choice of roots.  Surjectivity is produced by
Noether's Hilbert theorem 90.  This is the finite actual-field character-
isomorphism half of The finite Kummer character equivalence; it does not assert the full
lattice correspondence between radical subgroups and abelian extensions.
-/

@[expose] public section

noncomputable
section

namespace KummerTheory

section FiniteKummerCharacterIso

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The radical subgroup `A_L^n intersect Kˣ` for the actual extension
`L/K`: its elements are precisely the base-field units admitting an `n`-th
root in `Lˣ`. -/
def finiteKummerRadicalSubgroup (n : ℕ+) : Subgroup Kˣ where
  carrier := {a | ∃ β : Lˣ,
    β ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨α, hα⟩ ⟨β, hβ⟩
    refine ⟨α * β, ?_⟩
    rw [mul_pow, hα, hβ, map_mul]
  inv_mem' := by
    rintro a ⟨α, hα⟩
    refine ⟨α⁻¹, ?_⟩
    rw [inv_pow, hα, map_inv]

/-- The finite Kummer radical consists exactly of classes annihilated by every
defining character. -/
@[simp] theorem mem_finiteKummerRadicalSubgroup_iff
    (n : ℕ+) {a : Kˣ} :
    a ∈ finiteKummerRadicalSubgroup (K := K) (L := L) n ↔
      ∃ β : Lˣ, β ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a :=
  Iff.rfl

/-- An arbitrary root choice on the already constructed radical subgroup.
No compatibility between the choices is imposed. -/
def chosenFiniteKummerRadicalDatum (n : ℕ+) : RadicalDatum (K := K) (L := L) n where
  carrier := finiteKummerRadicalSubgroup (K := K) (L := L) n
  root a := Classical.choose a.property
  root_pow_eq a := Classical.choose_spec a.property

/-- The field-level form of the roots-of-unity hypothesis `mu_n subset K`, restricted
to the roots of unity occurring in `L`: every `n`-th root of unity in `Lˣ`
comes from a unit of `K`. -/
def NthRootsOfUnityInBase (n : ℕ+) : Prop :=
  ∀ u : Lˣ, u ^ (n : ℕ) = 1 →
    ∃ zeta : Kˣ, Units.map (algebraMap K L).toMonoidHom zeta = u

/-- Under `mu_n subset K`, every Galois automorphism fixes `mu_n(L)`. -/
theorem nthRootsOfUnity_fixed
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := L) n)
    (sigma : Gal(L/K)) (u : Lˣ) (hu : u ^ (n : ℕ) = 1) :
    sigma • u = u := by
  obtain ⟨zeta, rfl⟩ := hmu u hu
  exact RadicalDatum.smul_algebraMap_unit (K := K) (L := L) sigma zeta

/-- The root-choice-free Kummer character on the ambient-power quotient is
surjective.  The preimage of a character is produced by Noether Hilbert 90,
not supplied as a hypothesis. -/
theorem finiteKummerQuotientCharacter_surjective
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := L) n) :
    Function.Surjective
      ((chosenFiniteKummerRadicalDatum (K := K) (L := L) n).quotientKummerCharacterWithoutSection
          (nthRootsOfUnity_fixed (K := K) (L := L) n hmu)) := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := L) n
  let hfixed : ∀ sigma : Gal(L/K), ∀ u : Lˣ,
      u ^ (n : ℕ) = 1 → sigma • u = u :=
    nthRootsOfUnity_fixed (K := K) (L := L) n hmu
  intro chi
  let f : Gal(L/K) → Lˣ := fun sigma => (chi sigma).1
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro sigma tau
    change (chi (sigma * tau)).1 = sigma • (chi tau).1 * (chi sigma).1
    rw [map_mul, hfixed sigma (chi tau).1 (chi tau).2, mul_comm]
    rfl
  obtain ⟨beta, hbeta_div⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  have hbeta : ∀ sigma : Gal(L/K), sigma • beta = f sigma * beta := by
    intro sigma
    rw [← hbeta_div sigma]
    exact (div_mul_cancel (sigma • beta) beta).symm
  have hbeta_pow_fixed : ∀ sigma : Gal(L/K),
      sigma • (beta ^ (n : ℕ)) = beta ^ (n : ℕ) := by
    intro sigma
    calc
      sigma • (beta ^ (n : ℕ)) = (sigma • beta) ^ (n : ℕ) := by
        exact map_pow (MulDistribMulAction.toMonoidHom Lˣ sigma) beta (n : ℕ)
      _ = (f sigma * beta) ^ (n : ℕ) := by rw [hbeta sigma]
      _ = (f sigma) ^ (n : ℕ) * beta ^ (n : ℕ) := mul_pow _ _ _
      _ = beta ^ (n : ℕ) := by
        rw [show (f sigma) ^ (n : ℕ) = 1 from (chi sigma).2, one_mul]
  have hbeta_pow_range : ((beta ^ (n : ℕ) : Lˣ) : L) ∈
      Set.range (algebraMap K L) := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed
      (((beta ^ (n : ℕ) : Lˣ) : L))).2
    intro sigma
    exact congrArg Units.val (hbeta_pow_fixed sigma)
  obtain ⟨a, ha⟩ := hbeta_pow_range
  have ha_ne : a ≠ 0 := by
    intro ha_zero
    have : (((beta ^ (n : ℕ) : Lˣ) : L)) = 0 := by
      simpa [ha_zero] using ha.symm
    exact (beta ^ (n : ℕ)).ne_zero this
  let aunit : Kˣ := Units.mk0 a ha_ne
  have hbeta_pow : beta ^ (n : ℕ) =
      Units.map (algebraMap K L).toMonoidHom aunit := by
    apply Units.ext
    exact ha.symm
  let delta : D.carrier := ⟨aunit, beta, hbeta_pow⟩
  refine ⟨D.radicalQuotientMk delta, ?_⟩
  rw [D.quotientKummerCharacterWithoutSection_mk]
  apply MonoidHom.ext
  intro sigma
  apply Subtype.ext
  change D.rootCharacter delta hfixed sigma = (chi sigma).1
  rw [← D.rootCharacter_eq_of_same_pow hfixed delta hbeta_pow sigma]
  simp [rootQuotient, hbeta sigma, f]

/-- The finite actual-field Kummer character isomorphism on
`Delta / (Delta intersect Kˣ^n)`.  This is the character-isomorphism half of
the finite Kummer character equivalence, not the full subgroup/extension correspondence. -/
def finiteKummerCharacterEquiv
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := L) n) :
    (chosenFiniteKummerRadicalDatum (K := K) (L := L) n).RadicalQuotient ≃*
      (Gal(L/K) →* nthRootsSubgroup L (n : ℕ)) :=
  MulEquiv.ofBijective
    ((chosenFiniteKummerRadicalDatum (K := K) (L := L) n).quotientKummerCharacterWithoutSection
        (nthRootsOfUnity_fixed (K := K) (L := L) n hmu))
    ⟨(chosenFiniteKummerRadicalDatum (K := K) (L := L)
      n).quotientKummerCharacterWithoutSection_injective
          (nthRootsOfUnity_fixed (K := K) (L := L) n hmu),
      finiteKummerQuotientCharacter_surjective (K := K) (L := L) n hmu⟩

end FiniteKummerCharacterIso

end KummerTheory
