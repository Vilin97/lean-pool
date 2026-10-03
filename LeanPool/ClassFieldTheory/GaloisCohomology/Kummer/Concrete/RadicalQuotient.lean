/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.Infinite
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.RootCharacters
/-!
# Ambient radical quotients

Source lemmas for the quotient on the radical side of the Kummer pairing in
Concrete Kummer radical quotients.  Unlike `MultiplicativeRadicalDatum`, this construction starts
with an arbitrary choice of roots.  The hypothesis that `μₙ(L)` is fixed by
Galois makes the resulting root characters independent of that choice.

The denominator is the subgroup of elements of `D.carrier` which are `n`-th
powers in the ambient group `Kˣ`, in the ambient group, rather than the generally
smaller subgroup of `n`-th powers of elements of `D.carrier`.
-/

@[expose] public section

namespace KummerTheory

section RadicalQuotient

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace RadicalDatum

variable {n : ℕ+} (D : RadicalDatum (K := K) (L := L) n)

/-- Multiplicativity of root characters does not require a multiplicative choice of roots. -/
theorem rootCharacter_mul_withoutSection
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    (a b : D.carrier) :
    D.rootCharacter (a * b) hfixed =
      D.rootCharacter a hfixed * D.rootCharacter b hfixed := by
  apply MonoidHom.ext
  intro σ
  change D.rootCocycle (a * b) σ = D.rootCocycle a σ * D.rootCocycle b σ
  rw [← D.rootQuotient_eq_rootCocycle_of_same_pow hfixed (a * b) (u := D.root a * D.root b)]
  · exact rootQuotient_mul_root (K := K) (L := L) (D.root a) (D.root b) σ
  · rw [mul_pow, D.root_pow_eq_map, D.root_pow_eq_map]
    exact (map_mul (Units.map (algebraMap K L).toMonoidHom) a.1 b.1).symm

/-- The root character of `1` is trivial, without choosing roots multiplicatively. -/
theorem rootCharacter_one_withoutSection
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    D.rootCharacter 1 hfixed = 1 := by
  apply MonoidHom.ext
  intro σ
  rw [D.rootCharacter_apply]
  rw [← D.rootQuotient_eq_rootCocycle_of_same_pow hfixed (1 : D.carrier)
    (u := Units.map (algebraMap K L).toMonoidHom (1 : Kˣ))]
  · exact rootQuotient_algebraMap_unit (K := K) (L := L) 1 σ
  · simp

/-- The root character, bundled with its codomain restricted to `μₙ(L)`. -/
def rootCharacterToMuWithoutSection (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    Gal(L/K) →* nthRootsSubgroup L (n : ℕ) where
  toFun := fun σ =>
    ⟨D.rootCharacter a hfixed σ, D.rootCharacter_mem_nthRootsSubgroup a hfixed σ⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (D.rootCharacter a hfixed)
  map_mul' := by
    intro σ τ
    apply Subtype.ext
    exact map_mul (D.rootCharacter a hfixed) σ τ

/-- The section-free root character evaluates as the quotient of the transported
root by the root itself. -/
@[simp] theorem rootCharacterToMuWithoutSection_apply (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    (σ : Gal(L/K)) :
    D.rootCharacterToMuWithoutSection a hfixed σ =
      ⟨D.rootCharacter a hfixed σ, D.rootCharacter_mem_nthRootsSubgroup a hfixed σ⟩ :=
  rfl

/-- The root-character construction is a homomorphism on the radical subgroup. -/
def kummerCharacterWithoutSection
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    D.carrier →* (Gal(L/K) →* nthRootsSubgroup L (n : ℕ)) where
  toFun := fun a => D.rootCharacterToMuWithoutSection a hfixed
  map_one' := by
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    exact congrArg (fun χ : Gal(L/K) →* Lˣ => χ σ)
      (D.rootCharacter_one_withoutSection hfixed)
  map_mul' := by
    intro a b
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    exact congrArg (fun χ : Gal(L/K) →* Lˣ => χ σ)
      (D.rootCharacter_mul_withoutSection hfixed a b)

/-- Elements of the radical subgroup which are `n`-th powers in the ambient `Kˣ`. -/
def ambientNthPowersSubgroup : Subgroup D.carrier :=
  (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range.comap D.carrier.subtype

/-- An element belongs to the ambient power subgroup exactly when it is an `n`th power. -/
theorem mem_ambientNthPowersSubgroup_iff {a : D.carrier} :
    a ∈ D.ambientNthPowersSubgroup ↔ ∃ b : Kˣ, b ^ (n : ℕ) = a.1 :=
  Iff.rfl

/-- A root character is trivial on an ambient `n`-th power. -/
theorem rootCharacter_eq_one_of_mem_ambientNthPowers
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    {a : D.carrier} (ha : a ∈ D.ambientNthPowersSubgroup) :
    D.rootCharacter a hfixed = 1 := by
  obtain ⟨b, hb⟩ := (D.mem_ambientNthPowersSubgroup_iff).1 ha
  apply MonoidHom.ext
  intro σ
  rw [D.rootCharacter_apply]
  rw [← D.rootQuotient_eq_rootCocycle_of_same_pow hfixed a
    (u := Units.map (algebraMap K L).toMonoidHom b)]
  · exact rootQuotient_algebraMap_unit (K := K) (L := L) b σ
  · rw [← map_pow, hb]

/-- The ambient `n`-th-power subgroup lies in the kernel of the Kummer character. -/
theorem ambientNthPowersSubgroup_le_ker
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    D.ambientNthPowersSubgroup ≤ MonoidHom.ker (D.kummerCharacterWithoutSection hfixed) := by
  intro a ha
  change D.kummerCharacterWithoutSection hfixed a = 1
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  exact congrArg (fun χ : Gal(L/K) →* Lˣ => χ σ)
    (D.rootCharacter_eq_one_of_mem_ambientNthPowers hfixed ha)

/-- For a Galois extension, triviality of the Kummer character forces the
chosen root to come from the base field.  Consequently the kernel is exactly
the subgroup of ambient `n`-th powers, not merely a subgroup containing it. -/
theorem ker_kummerCharacterWithoutSection_eq_ambientNthPowers
    [IsGalois K L]
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    MonoidHom.ker (D.kummerCharacterWithoutSection hfixed) =
      D.ambientNthPowersSubgroup := by
  apply le_antisymm
  · intro a ha
    have hroot : ∀ σ : Gal(L/K), σ • D.root a = D.root a := by
      intro σ
      have hvalue : D.rootCharacterToMuWithoutSection a hfixed σ = 1 := by
        have happ := congrArg
          (fun χ : Gal(L/K) →* nthRootsSubgroup L (n : ℕ) ↦ χ σ) ha
        simpa [kummerCharacterWithoutSection] using happ
      have hquot : rootQuotient (K := K) (L := L) (D.root a) σ = 1 := by
        exact congrArg Subtype.val hvalue
      exact (rootQuotient_eq_one_iff (K := K) (L := L) (D.root a) σ).1 hquot
    have hfixedVal : ∀ σ : Gal(L/K), σ (D.root a : L) = D.root a := by
      intro σ
      exact congrArg Units.val (hroot σ)
    obtain ⟨b, hb⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (K := L) (D.root a : L)).2
        hfixedVal
    have hb0 : b ≠ 0 := by
      intro hbzero
      have : (D.root a : L) = 0 := by simpa [hbzero] using hb.symm
      exact Units.ne_zero (D.root a) this
    refine (D.mem_ambientNthPowersSubgroup_iff).2 ⟨Units.mk0 b hb0, ?_⟩
    apply Units.ext
    calc
      ((Units.mk0 b hb0 : Kˣ) ^ (n : ℕ) : K) = b ^ (n : ℕ) := rfl
      _ = a.1 := by
        apply (algebraMap K L).injective
        calc
          algebraMap K L (b ^ (n : ℕ)) = (D.root a : L) ^ (n : ℕ) := by
            rw [map_pow, hb]
          _ = algebraMap K L (a.1 : K) := congrArg Units.val (D.root_pow_eq_map a)
  · exact D.ambientNthPowersSubgroup_le_ker hfixed

/-- The ambient radical quotient `Δ / (Δ ∩ Kˣⁿ)`. -/
def RadicalQuotient : Type _ :=
  D.carrier ⧸ D.ambientNthPowersSubgroup

/-- The commutative group structure transported to the named ambient
radical quotient. -/
instance radicalQuotientCommGroupInstance : CommGroup D.RadicalQuotient := by
  change CommGroup (D.carrier ⧸ D.ambientNthPowersSubgroup)
  infer_instance

/-- Comparison with the group-library presentation of the ambient radical
quotient. -/
def radicalQuotientMulEquiv :
    D.RadicalQuotient ≃* (D.carrier ⧸ D.ambientNthPowersSubgroup) :=
  MulEquiv.refl _

/-- The canonical projection to the named ambient radical quotient. -/
def radicalQuotientMk : D.carrier →* D.RadicalQuotient :=
  QuotientGroup.mk' D.ambientNthPowersSubgroup

/-- The named radical quotient projection agrees with the underlying quotient map. -/
@[simp]
theorem radicalQuotientMk_apply (a : D.carrier) :
    D.radicalQuotientMulEquiv (D.radicalQuotientMk a) =
      (QuotientGroup.mk a : D.carrier ⧸ D.ambientNthPowersSubgroup) :=
  rfl

/-- A radical quotient class is trivial exactly when its representative is an
ambient `n`th power. -/
@[simp]
theorem radicalQuotientMk_eq_one_iff (a : D.carrier) :
    D.radicalQuotientMk a = 1 ↔ a ∈ D.ambientNthPowersSubgroup := by
  change
    (QuotientGroup.mk' D.ambientNthPowersSubgroup) a = 1 ↔
      a ∈ D.ambientNthPowersSubgroup
  exact QuotientGroup.eq_one_iff a

/-- Two radical quotient representatives agree exactly when their ratio is an
ambient `n`th power. -/
@[simp]
theorem radicalQuotientMk_eq_iff (a b : D.carrier) :
    D.radicalQuotientMk a = D.radicalQuotientMk b ↔
      a / b ∈ D.ambientNthPowersSubgroup := by
  change
    (QuotientGroup.mk' D.ambientNthPowersSubgroup) a =
        (QuotientGroup.mk' D.ambientNthPowersSubgroup) b ↔
      a / b ∈ D.ambientNthPowersSubgroup
  exact QuotientGroup.eq_iff_div_mem

/-- Every ambient radical class has a representative in `D.carrier`. -/
theorem radicalQuotientMk_surjective :
    Function.Surjective D.radicalQuotientMk := by
  change Function.Surjective
    (QuotientGroup.mk' D.ambientNthPowersSubgroup)
  exact QuotientGroup.mk'_surjective D.ambientNthPowersSubgroup

/-- Eliminate a named ambient radical quotient through its canonical
representatives. -/
protected theorem radicalQuotient_inductionOn
    {motive : D.RadicalQuotient → Prop} (q : D.RadicalQuotient)
    (mk : ∀ a : D.carrier, motive (D.radicalQuotientMk a)) :
    motive q := by
  exact QuotientGroup.induction_on' q mk

/-- Descend a homomorphism through the named ambient radical quotient. -/
def radicalQuotientLift {M : Type*} [Group M]
    (f : D.carrier →* M)
    (hf : D.ambientNthPowersSubgroup ≤ MonoidHom.ker f) :
    D.RadicalQuotient →* M :=
  (QuotientGroup.lift D.ambientNthPowersSubgroup f hf).comp
    D.radicalQuotientMulEquiv.toMonoidHom

/-- The radical quotient lift evaluates on a representative by the prescribed lift. -/
@[simp]
theorem radicalQuotientLift_mk {M : Type*} [Group M]
    (f : D.carrier →* M)
    (hf : D.ambientNthPowersSubgroup ≤ MonoidHom.ker f)
    (a : D.carrier) :
    D.radicalQuotientLift f hf (D.radicalQuotientMk a) = f a :=
  rfl

/-- The Kummer character descended to the correct ambient-power quotient. -/
def quotientKummerCharacterWithoutSection
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    D.RadicalQuotient →* (Gal(L/K) →* nthRootsSubgroup L (n : ℕ)) :=
  D.radicalQuotientLift (D.kummerCharacterWithoutSection hfixed)
    (D.ambientNthPowersSubgroup_le_ker hfixed)

/-- The section-free Kummer character on a quotient class is computed from any representative. -/
@[simp] theorem quotientKummerCharacterWithoutSection_mk (a : D.carrier)
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    D.quotientKummerCharacterWithoutSection hfixed
        (D.radicalQuotientMk a) =
      D.kummerCharacterWithoutSection hfixed a :=
  D.radicalQuotientLift_mk _ _ a

/-- The character map on the ambient radical quotient is injective.  This is
the kernel half of the canonical isomorphism in the finite Kummer character equivalence. -/
theorem quotientKummerCharacterWithoutSection_injective
    [IsGalois K L]
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    Function.Injective (D.quotientKummerCharacterWithoutSection hfixed) := by
  intro q
  refine D.radicalQuotient_inductionOn
    (motive := fun q => ∀ r,
      D.quotientKummerCharacterWithoutSection hfixed q =
          D.quotientKummerCharacterWithoutSection hfixed r →
        q = r)
    q ?_
  intro a r
  refine D.radicalQuotient_inductionOn
    (motive := fun r =>
      D.quotientKummerCharacterWithoutSection hfixed
          (D.radicalQuotientMk a) =
          D.quotientKummerCharacterWithoutSection hfixed r →
        D.radicalQuotientMk a = r)
    r ?_
  intro b hab
  apply (D.radicalQuotientMk_eq_iff a b).2
  rw [← D.ker_kummerCharacterWithoutSection_eq_ambientNthPowers hfixed]
  have hab' : D.kummerCharacterWithoutSection hfixed a =
      D.kummerCharacterWithoutSection hfixed b := by
    simpa using hab
  rw [MonoidHom.mem_ker, map_div, hab']
  exact div_self' (D.kummerCharacterWithoutSection hfixed b)

end RadicalDatum
end RadicalQuotient

end KummerTheory
