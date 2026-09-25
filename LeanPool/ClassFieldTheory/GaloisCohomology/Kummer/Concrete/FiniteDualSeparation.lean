/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.FiniteGeneration
/-!
# finite Kummer dual separation

This file supplies the first missing finite-duality source for the full
subgroup/extension correspondence in the Kummer correspondence.  Characters of a finite
abelian group killed by `n` can be chosen with values in `μₙ`, and these
characters separate points.  Consequently, the transpose of a character
equivalence `R ≃ Hom(G, μₙ)` is injective.

No lattice correspondence or infinite Kummer endpoint is asserted here.
-/

@[expose] public section

noncomputable section

namespace KummerTheory

/-- Restrict a unit-valued character to `μₙ` when its source is killed by
`n`. -/
def characterToNthRoots
    {G K : Type*} [Group G] [Field K]
    (n : ℕ+) (hexponent : ∀ g : G, g ^ (n : ℕ) = 1)
    (φ : G →* Kˣ) : G →* nthRootsSubgroup K (n : ℕ) where
  toFun g :=
    ⟨φ g, by
      calc
        φ g ^ (n : ℕ) = φ (g ^ (n : ℕ)) := (map_pow φ g (n : ℕ)).symm
        _ = 1 := by rw [hexponent g, map_one]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one φ
  map_mul' := by
    intro g h
    apply Subtype.ext
    exact map_mul φ g h

/-- A finite character evaluates in the subgroup of `n`th roots of unity. -/
@[simp] theorem characterToNthRoots_apply
    {G K : Type*} [Group G] [Field K]
    (n : ℕ+) (hexponent : ∀ g : G, g ^ (n : ℕ) = 1)
    (φ : G →* Kˣ) (g : G) :
    (characterToNthRoots n hexponent φ g : Kˣ) = φ g :=
  rfl

/-- Characters with values in the actual `n`-th roots of unity of `K`
separate points of a finite abelian group killed by `n`. -/
theorem exists_nthRoots_character_apply_ne_one
    {G K : Type*} [CommGroup G] [Finite G] [Field K]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ g : G, g ^ (n : ℕ) = 1)
    {g : G} (hg : g ≠ 1) :
    ∃ χ : G →* nthRootsSubgroup K (n : ℕ), χ g ≠ 1 := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  obtain ⟨zeta, hzeta⟩ := hmu
  have hzeta_primitive : IsPrimitiveRoot zeta (n : ℕ) :=
    (mem_primitiveRoots n.pos).1 hzeta
  let : HasEnoughRootsOfUnity K (n : ℕ) :=
    { prim := ⟨zeta, hzeta_primitive⟩
      cyc := rootsOfUnity.isCyclic K (n : ℕ) }
  have hexponent_dvd : Monoid.exponent G ∣ (n : ℕ) :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun q => by
      simpa only using hexponent q)
  let : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd K hexponent_dvd
  obtain ⟨φ, hφ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G K hg
  refine ⟨characterToNthRoots n hexponent φ, ?_⟩
  intro h
  apply hφ
  exact congrArg Subtype.val h

/-- Algebraic extension maps carry `μₙ(K)` injectively into `μₙ(L)`. -/
def nthRootsSubgroupMap
    (K L : Type*) [Field K] [Field L] [Algebra K L] (n : ℕ) :
    nthRootsSubgroup K n →* nthRootsSubgroup L n where
  toFun z :=
    ⟨Units.map (algebraMap K L).toMonoidHom z.1, by
      calc
        Units.map (algebraMap K L).toMonoidHom z.1 ^ n =
            Units.map (algebraMap K L).toMonoidHom (z.1 ^ n) :=
          (map_pow (Units.map (algebraMap K L).toMonoidHom) z.1 n).symm
        _ = 1 := by rw [z.2, map_one]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Units.map (algebraMap K L).toMonoidHom)
  map_mul' := by
    intro z w
    apply Subtype.ext
    exact map_mul (Units.map (algebraMap K L).toMonoidHom) z.1 w.1

/-- The canonical map from roots of unity into the `n`th-roots subgroup is injective. -/
theorem nthRootsSubgroupMap_injective
    (K L : Type*) [Field K] [Field L] [Algebra K L] (n : ℕ) :
    Function.Injective (nthRootsSubgroupMap K L n) := by
  intro z w h
  apply Subtype.ext
  apply (Units.map_injective (f := (algebraMap K L).toMonoidHom)
    (algebraMap K L).injective)
  exact congrArg Subtype.val h

/-- The locally defined `nthRootsSubgroup` is canonically the same group as
mathlib's `rootsOfUnity`. -/
def nthRootsSubgroupEquivRootsOfUnity
    (K : Type*) [Field K] (n : ℕ) :
    nthRootsSubgroup K n ≃* rootsOfUnity n K where
  toFun z := ⟨z.1, z.2⟩
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The subgroup of `n`th roots of unity has a canonical finite type structure. -/
noncomputable instance nthRootsSubgroupFintype
    (K : Type*) [Field K] (n : ℕ) [NeZero n] : Fintype (nthRootsSubgroup K n) :=
  letI : Fintype (rootsOfUnity n K) := Fintype.ofFinite _
  Fintype.ofEquiv (rootsOfUnity n K)
    (nthRootsSubgroupEquivRootsOfUnity K n).symm.toEquiv

/-- If `K` contains a primitive `n`-th root, extension of scalars identifies
the `n`-th roots of unity in `K` and in every extension field `L`. -/
def nthRootsSubgroupEquivOfPrimitiveRoots
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    nthRootsSubgroup K (n : ℕ) ≃* nthRootsSubgroup L (n : ℕ) :=
  MulEquiv.ofBijective (nthRootsSubgroupMap K L (n : ℕ))
    ⟨nthRootsSubgroupMap_injective K L (n : ℕ), by
      intro u
      obtain ⟨zeta, hzeta⟩ :=
        nthRootsOfUnityInBase_of_primitiveRoots
          (K := K) (L := L) n hmu u.1 u.2
      have hzeta_pow : zeta ^ (n : ℕ) = 1 := by
        apply (Units.map_injective (f := (algebraMap K L).toMonoidHom)
          (algebraMap K L).injective)
        calc
          Units.map (algebraMap K L).toMonoidHom (zeta ^ (n : ℕ)) =
              (Units.map (algebraMap K L).toMonoidHom zeta) ^ (n : ℕ) :=
            map_pow (Units.map (algebraMap K L).toMonoidHom) zeta (n : ℕ)
          _ = u.1 ^ (n : ℕ) := by rw [hzeta]
          _ = 1 := u.2
          _ = Units.map (algebraMap K L).toMonoidHom 1 :=
            (map_one (Units.map (algebraMap K L).toMonoidHom)).symm
      exact ⟨⟨zeta, hzeta_pow⟩, Subtype.ext hzeta⟩⟩

/-- For a group killed by `n`, restricting a `Kˣ`-valued character to
`μₙ(K)` loses no information. -/
def unitCharactersEquivNthRoots
    {G K : Type*} [CommGroup G] [Field K]
    (n : ℕ+) (hexponent : ∀ g : G, g ^ (n : ℕ) = 1) :
    (G →* Kˣ) ≃* (G →* nthRootsSubgroup K (n : ℕ)) where
  toFun := characterToNthRoots n hexponent
  invFun χ := (nthRootsSubgroup K (n : ℕ)).subtype.comp χ
  left_inv φ := by
    apply MonoidHom.ext
    intro g
    rfl
  right_inv χ := by
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    rfl
  map_mul' φ ψ := by
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    rfl

/-- Finite abelian duality with the character codomain restricted to the
actual `n`-th roots of unity in an extension field. -/
theorem finiteNthRootsCharacterDuality
    {G K L : Type*} [CommGroup G] [Finite G]
    [Field K] [Field L] [Algebra K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ g : G, g ^ (n : ℕ) = 1) :
    Nonempty ((G →* nthRootsSubgroup L (n : ℕ)) ≃* G) := by
  let rootsEquiv := nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  obtain ⟨zeta, hzeta⟩ := hmu
  have hzeta_primitive : IsPrimitiveRoot zeta (n : ℕ) :=
    (mem_primitiveRoots n.pos).1 hzeta
  let : HasEnoughRootsOfUnity K (n : ℕ) :=
    { prim := ⟨zeta, hzeta_primitive⟩
      cyc := rootsOfUnity.isCyclic K (n : ℕ) }
  have hexponent_dvd : Monoid.exponent G ∣ (n : ℕ) :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => by
      simpa only using hexponent g)
  let : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd K hexponent_dvd
  obtain ⟨dual⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G K
  exact ⟨(rootsEquiv.monoidHomCongrRight (M := G)).symm |>.trans
    (unitCharactersEquivNthRoots n hexponent).symm |>.trans dual⟩

/-- The same separation result with values in the roots of unity of an
extension field `L`. -/
theorem exists_nthRoots_character_apply_ne_one_in_extension
    {G K L : Type*} [CommGroup G] [Finite G]
    [Field K] [Field L] [Algebra K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ g : G, g ^ (n : ℕ) = 1)
    {g : G} (hg : g ≠ 1) :
    ∃ χ : G →* nthRootsSubgroup L (n : ℕ), χ g ≠ 1 := by
  obtain ⟨χ, hχ⟩ :=
    exists_nthRoots_character_apply_ne_one n hmu hexponent hg
  refine ⟨(nthRootsSubgroupMap K L (n : ℕ)).comp χ, ?_⟩
  intro h
  apply hχ
  apply nthRootsSubgroupMap_injective K L (n : ℕ)
  simpa using h

/-- Transpose a character equivalence by evaluation. -/
def transposeCharacterEquiv
    {G R M : Type*} [CommGroup G] [CommGroup R] [CommGroup M]
    (e : R ≃* (G →* M)) : G →* (R →* M) where
  toFun g :=
    { toFun := fun r => e r g
      map_one' := by simp
      map_mul' := by
        intro r s
        exact congrArg (fun χ : G →* M => χ g) (map_mul e r s) }
  map_one' := by
    apply MonoidHom.ext
    intro r
    exact map_one (e r)
  map_mul' := by
    intro g h
    apply MonoidHom.ext
    intro r
    exact map_mul (e r) g h

/-- The transposed character equivalence evaluates by pairing with the original character. -/
@[simp] theorem transposeCharacterEquiv_apply
    {G R M : Type*} [CommGroup G] [CommGroup R] [CommGroup M]
    (e : R ≃* (G →* M)) (g : G) (r : R) :
    transposeCharacterEquiv e g r = e r g :=
  rfl

/-- Nondegeneracy on the Galois side of the finite Kummer pairing.  This is
the injectivity source needed before the cardinality step can upgrade the
transpose to the canonical isomorphism in the Kummer correspondence. -/
theorem transposeCharacterEquiv_injective
    {G R K L : Type*} [CommGroup G] [Finite G] [CommGroup R]
    [Field K] [Field L] [Algebra K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ g : G, g ^ (n : ℕ) = 1)
    (e : R ≃* (G →* nthRootsSubgroup L (n : ℕ))) :
    Function.Injective (transposeCharacterEquiv e) := by
  intro g h hgh
  apply div_eq_one.mp
  by_contra hdiv
  obtain ⟨χ, hχ⟩ :=
    exists_nthRoots_character_apply_ne_one_in_extension
      (G := G) (K := K) (L := L) n hmu hexponent hdiv
  obtain ⟨r, hr⟩ := e.surjective χ
  have hquotient : transposeCharacterEquiv e (g / h) = 1 := by
    rw [map_div, hgh]
    exact div_self' (transposeCharacterEquiv e h)
  have hvalue := congrArg
    (fun ψ : R →* nthRootsSubgroup L (n : ℕ) => ψ r) hquotient
  change e r (g / h) = 1 at hvalue
  apply hχ
  simpa only [hr] using hvalue

/-- The finite cardinality step upgrades nondegeneracy of the transposed
Kummer pairing to surjectivity.  The needed equality of cardinalities is
produced by finite abelian duality; it is not assumed. -/
theorem transposeCharacterEquiv_surjective
    {G R K L : Type*} [CommGroup G] [Finite G] [CommGroup R]
    [Field K] [Field L] [Algebra K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ g : G, g ^ (n : ℕ) = 1)
    (e : R ≃* (G →* nthRootsSubgroup L (n : ℕ))) :
    Function.Surjective (transposeCharacterEquiv e) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : Finite (G →* nthRootsSubgroup L (n : ℕ)) :=
    Finite.of_injective
      (fun χ : G →* nthRootsSubgroup L (n : ℕ) =>
        (χ : G → nthRootsSubgroup L (n : ℕ))) DFunLike.coe_injective
  let : Finite R := Finite.of_equiv
    (G →* nthRootsSubgroup L (n : ℕ)) e.symm.toEquiv
  have hRexponent : ∀ r : R, r ^ (n : ℕ) = 1 := by
    intro r
    apply e.injective
    rw [map_pow, map_one]
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    exact (e r g).2
  obtain ⟨dualR⟩ := finiteNthRootsCharacterDuality
    (G := R) (K := K) (L := L) n hmu hRexponent
  obtain ⟨dualG⟩ := finiteNthRootsCharacterDuality
    (G := G) (K := K) (L := L) n hmu hexponent
  let targetEquivG : (R →* nthRootsSubgroup L (n : ℕ)) ≃ G :=
    dualR.toEquiv.trans (e.toEquiv.trans dualG.toEquiv)
  exact (transposeCharacterEquiv_injective n hmu hexponent e).surjective_of_finite
    targetEquivG.symm

/-- The canonical finite Kummer transpose equivalence.  This is the finite
perfect-pairing equivalence underlying the Galois-group isomorphism; it
does not yet assert the subgroup/extension lattice endpoint. -/
def transposeCharacterMulEquiv
    {G R K L : Type*} [CommGroup G] [Finite G] [CommGroup R]
    [Field K] [Field L] [Algebra K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ g : G, g ^ (n : ℕ) = 1)
    (e : R ≃* (G →* nthRootsSubgroup L (n : ℕ))) :
    G ≃* (R →* nthRootsSubgroup L (n : ℕ)) :=
  MulEquiv.ofBijective (transposeCharacterEquiv e)
    ⟨transposeCharacterEquiv_injective n hmu hexponent e,
      transposeCharacterEquiv_surjective n hmu hexponent e⟩

end KummerTheory
