/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.Product
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.EquivariantEquiv
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.SetTheory.Cardinal.Finite
/-!
# Herbrand quotients of permutation lattices

This file supplies the abstract cohomology calculation for permutation
lattices.  It proves the value of the Herbrand quotient on the trivial
integer lattice, transports that calculation through Shapiro's lemma to
transitive permutation lattices, and multiplies over a finite family of
orbits.  It also records invariance under passage to a finite-index stable
subgroup.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA uι

/-- The trivial multiplicative action on the additive group of integers,
written multiplicatively. -/
@[reducible]
def trivialIntMulDistribMulAction
    (G : Type uG) [Group G] :
    MulDistribMulAction G (Multiplicative ℤ) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

section TrivialInteger

variable {G : Type uG} [Group G] [Fintype G]

/-- For the trivial integer module, the norm is multiplication by the
order of the group. -/
theorem trivialInt_tateNorm_toAdd
    (a : Multiplicative ℤ) :
    letI := trivialIntMulDistribMulAction G
    Multiplicative.toAdd
        (tateNorm G (Multiplicative ℤ) a) =
      (Fintype.card G : ℤ) * Multiplicative.toAdd a := by
  let := trivialIntMulDistribMulAction G
  have hsmul (g : G) : g • a = a := rfl
  simp [tateNorm, hsmul]

/-- Reduction modulo `|G|` on the fixed subgroup of the trivial integer
module. -/
def trivialIntFixedToZModHom :
    letI := trivialIntMulDistribMulAction G
    fixedSubgroup G (Multiplicative ℤ) →*
      Multiplicative (ZMod (Fintype.card G)) := by
  letI := trivialIntMulDistribMulAction G
  exact
    { toFun := fun x ↦ Multiplicative.ofAdd
        ((Multiplicative.toAdd
          (x : Multiplicative ℤ) : ℤ) :
            ZMod (Fintype.card G))
      map_one' := by simp
      map_mul' := by
        intro x y
        simp }

theorem trivialIntFixedToZModHom_surjective :
    letI := trivialIntMulDistribMulAction G
    Function.Surjective
      (trivialIntFixedToZModHom (G := G)) := by
  let := trivialIntMulDistribMulAction G
  intro y
  rcases ZMod.intCast_surjective
      (Multiplicative.toAdd y) with ⟨z, hz⟩
  let x : fixedSubgroup G (Multiplicative ℤ) :=
    ⟨Multiplicative.ofAdd z, by intro g; rfl⟩
  refine ⟨x, ?_⟩
  rw [show trivialIntFixedToZModHom
      (G := G) x =
        Multiplicative.ofAdd
          ((z : ℤ) : ZMod (Fintype.card G)) by rfl]
  exact congrArg Multiplicative.ofAdd hz

/-- The kernel of reduction modulo `|G|` is the norm subgroup. -/
theorem trivialIntFixedToZModHom_ker :
    letI := trivialIntMulDistribMulAction G
    MonoidHom.ker
        (trivialIntFixedToZModHom (G := G)) =
      (tateNormSubgroup G
        (Multiplicative ℤ)).subgroupOf
          (fixedSubgroup G (Multiplicative ℤ)) := by
  let := trivialIntMulDistribMulAction G
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hx0 :
        ((Multiplicative.toAdd
          (x : Multiplicative ℤ) : ℤ) :
            ZMod (Fintype.card G)) = 0 := by
      exact congrArg Multiplicative.toAdd hx
    rcases
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hx0
      with ⟨z, hz⟩
    change (x : Multiplicative ℤ) ∈
      tateNormSubgroup G (Multiplicative ℤ)
    refine ⟨Multiplicative.ofAdd z, ?_⟩
    have htoAdd :
        Multiplicative.toAdd
            (tateNorm G (Multiplicative ℤ)
              (Multiplicative.ofAdd z)) =
          Multiplicative.toAdd
            (x : Multiplicative ℤ) := by
      rw [trivialInt_tateNorm_toAdd]
      exact hz.symm
    exact congrArg Multiplicative.ofAdd htoAdd
  · intro hx
    change (x : Multiplicative ℤ) ∈
      tateNormSubgroup G (Multiplicative ℤ) at hx
    rcases hx with ⟨z, hz⟩
    exact congrArg Multiplicative.ofAdd (by
      change
        ((Multiplicative.toAdd
          (x : Multiplicative ℤ) : ℤ) :
            ZMod (Fintype.card G)) = 0
      rw [← hz, tateNormHom_apply, trivialInt_tateNorm_toAdd]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      exact ⟨Multiplicative.toAdd z, rfl⟩)

/-- The degree-zero Herbrand group of the trivial integer module is
`ℤ / |G|ℤ`. -/
noncomputable def trivialIntHerbrandH0EquivZMod :
    letI := trivialIntMulDistribMulAction G
    HerbrandH0 G (Multiplicative ℤ) ≃*
      Multiplicative (ZMod (Fintype.card G)) := by
  letI := trivialIntMulDistribMulAction G
  exact
    (HerbrandH0.equiv
      (G := G) (A := Multiplicative ℤ)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (trivialIntFixedToZModHom_ker
          (G := G)).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective
          (trivialIntFixedToZModHom (G := G))
          (trivialIntFixedToZModHom_surjective
            (G := G))))

theorem trivialIntHerbrandH0Finite :
    letI := trivialIntMulDistribMulAction G
    Finite (HerbrandH0 G (Multiplicative ℤ)) := by
  let := trivialIntMulDistribMulAction G
  exact Finite.of_equiv
    (Multiplicative (ZMod (Fintype.card G)))
    (trivialIntHerbrandH0EquivZMod
      (G := G)).symm.toEquiv

theorem trivialInt_herbrandH0_card :
    letI := trivialIntMulDistribMulAction G
    letI := trivialIntHerbrandH0Finite (G := G)
    Nat.card
        (HerbrandH0 G (Multiplicative ℤ)) =
      Fintype.card G := by
  let := trivialIntMulDistribMulAction G
  let := trivialIntHerbrandH0Finite (G := G)
  rw [Nat.card_congr
      (trivialIntHerbrandH0EquivZMod
        (G := G)).toEquiv]
  simp

/-- The norm kernel of the trivial torsion-free integer module is
trivial. -/
theorem trivialInt_normKernelSubgroup_eq_bot :
    letI := trivialIntMulDistribMulAction G
    normKernelSubgroup G (Multiplicative ℤ) = ⊥ := by
  let := trivialIntMulDistribMulAction G
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_bot]
    exact congrArg Multiplicative.ofAdd (by
      change
        Multiplicative.toAdd
          (x : Multiplicative ℤ) = 0
      have hnorm :
          (Fintype.card G : ℤ) *
              Multiplicative.toAdd
                (x : Multiplicative ℤ) = 0 := by
        rw [← trivialInt_tateNorm_toAdd]
        exact congrArg Multiplicative.toAdd hx
      exact (mul_eq_zero.mp hnorm).resolve_left (by
        exact_mod_cast Fintype.card_ne_zero))
  · exact bot_le

theorem trivialIntHerbrandHMinusOneFinite
    (σ : G) :
    letI := trivialIntMulDistribMulAction G
    Finite
      (HerbrandHMinusOne G
        (Multiplicative ℤ) σ) := by
  let := trivialIntMulDistribMulAction G
  have : Subsingleton
      (normKernelSubgroup G
        (Multiplicative ℤ)) := by
    rw [trivialInt_normKernelSubgroup_eq_bot
      (G := G)]
    infer_instance
  let : Subsingleton
      (HerbrandHMinusOne G
        (Multiplicative ℤ) σ) :=
    ⟨fun q ↦
      HerbrandHMinusOne.inductionOn σ
        (motive := fun q ↦ ∀ r, q = r) q fun x r ↦
          HerbrandHMinusOne.inductionOn σ
            (motive := fun r ↦
              HerbrandHMinusOne.mk σ x = r)
            r fun y ↦
              congrArg
                (fun z ↦ HerbrandHMinusOne.mk σ z)
                (Subsingleton.elim x y)⟩
  exact Finite.of_injective
    (fun _ : HerbrandHMinusOne G
      (Multiplicative ℤ) σ ↦ false)
    (fun x y _ ↦ Subsingleton.elim x y)

theorem trivialInt_herbrandHMinusOne_card_eq_one
    (σ : G) :
    letI := trivialIntMulDistribMulAction G
    letI :=
      trivialIntHerbrandHMinusOneFinite
        (G := G) σ
    Nat.card
      (HerbrandHMinusOne G
        (Multiplicative ℤ) σ) = 1 := by
  let := trivialIntMulDistribMulAction G
  let :=
    trivialIntHerbrandHMinusOneFinite
      (G := G) σ
  have : Subsingleton
      (normKernelSubgroup G
        (Multiplicative ℤ)) := by
    rw [trivialInt_normKernelSubgroup_eq_bot
      (G := G)]
    infer_instance
  let : Subsingleton
      (HerbrandHMinusOne G
        (Multiplicative ℤ) σ) :=
    ⟨fun q ↦
      HerbrandHMinusOne.inductionOn σ
        (motive := fun q ↦ ∀ r, q = r) q fun x r ↦
          HerbrandHMinusOne.inductionOn σ
            (motive := fun r ↦
              HerbrandHMinusOne.mk σ x = r)
            r fun y ↦
              congrArg
                (fun z ↦ HerbrandHMinusOne.mk σ z)
                (Subsingleton.elim x y)⟩
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, inferInstance⟩

/-- For the one-point orbit, the Herbrand quotient of the trivial
integer lattice is the order of the acting group. -/
theorem trivialInt_herbrandQuotient_eq_card
    (σ : G) :
    letI := trivialIntMulDistribMulAction G
    letI := trivialIntHerbrandH0Finite (G := G)
    letI :=
      trivialIntHerbrandHMinusOneFinite
        (G := G) σ
    herbrandQuotient
        (G := G) (A := Multiplicative ℤ) σ =
      (Fintype.card G : ℚ) := by
  let := trivialIntMulDistribMulAction G
  let := trivialIntHerbrandH0Finite (G := G)
  let :=
    trivialIntHerbrandHMinusOneFinite
      (G := G) σ
  rw [herbrandQuotient_eq_card_ratio,
    trivialInt_herbrandH0_card (G := G),
    trivialInt_herbrandHMinusOne_card_eq_one
      (G := G) σ]
  simp

end TrivialInteger

section TransitivePermutationLattice

variable {G : Type uG} [Group G] [Fintype G]

/-- A transitive permutation lattice in orbit coordinates: the stabilizer
`H` acts trivially on `ℤ`, and induction gives the integer-valued
functions on the corresponding orbit. -/
abbrev TransitivePermutationLattice
    (H : Subgroup G)
    [MulDistribMulAction H (Multiplicative ℤ)] :=
  InducedModule (G := G)
    (B := Multiplicative ℤ) H

theorem transitivePermutationLatticeHerbrandH0Finite
    (H : Subgroup G)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _stabilizerAction :
        MulDistribMulAction H (Multiplicative ℤ) :=
      trivialIntMulDistribMulAction H
    letI _stabilizerFintype : Fintype H :=
      Fintype.ofFinite H
    Finite
      (HerbrandH0 G
        (TransitivePermutationLattice H)) := by
  let stabilizerAction :
      MulDistribMulAction H (Multiplicative ℤ) :=
    trivialIntMulDistribMulAction H
  let stabilizerFintype : Fintype H :=
    Fintype.ofFinite H
  let : Finite
      (HerbrandH0 H (Multiplicative ℤ)) :=
    trivialIntHerbrandH0Finite (G := H)
  exact Finite.of_equiv
    (HerbrandH0 H (Multiplicative ℤ))
    (inducedHerbrandH0EquivOfFiniteCyclic
      H σ hgen).symm.toEquiv

theorem transitivePermutationLatticeHerbrandHMinusOneFinite
    (H : Subgroup G)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _stabilizerAction :
        MulDistribMulAction H (Multiplicative ℤ) :=
      trivialIntMulDistribMulAction H
    letI _stabilizerFintype : Fintype H :=
      Fintype.ofFinite H
    Finite
      (HerbrandHMinusOne G
        (TransitivePermutationLattice H) σ) := by
  let stabilizerAction :
      MulDistribMulAction H (Multiplicative ℤ) :=
    trivialIntMulDistribMulAction H
  let stabilizerFintype : Fintype H :=
    Fintype.ofFinite H
  let δ :=
    subgroupGeneratorOfGenerator H σ hgen
  let : Finite
      (HerbrandHMinusOne H
        (Multiplicative ℤ) δ) :=
    trivialIntHerbrandHMinusOneFinite
      (G := H) δ
  exact Finite.of_equiv
    (HerbrandHMinusOne H
      (Multiplicative ℤ) δ)
    (inducedHerbrandHMinusOneEquivOfFiniteCyclic
      H σ hgen).symm.toEquiv

/-- The Herbrand quotient of the permutation lattice on one orbit is the
order of the stabilizer. -/
theorem transitivePermutationLattice_herbrandQuotient_eq_stabilizerCard
    (H : Subgroup G)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _stabilizerAction :
        MulDistribMulAction H (Multiplicative ℤ) :=
      trivialIntMulDistribMulAction H
    letI _stabilizerFintype : Fintype H :=
      Fintype.ofFinite H
    letI _h0Finite :
        Finite
          (HerbrandH0 G
            (TransitivePermutationLattice H)) :=
      transitivePermutationLatticeHerbrandH0Finite
        H σ hgen
    letI _hMinusOneFinite :
        Finite
          (HerbrandHMinusOne G
            (TransitivePermutationLattice H) σ) :=
      transitivePermutationLatticeHerbrandHMinusOneFinite
        H σ hgen
    herbrandQuotient
        (G := G)
        (A := TransitivePermutationLattice H) σ =
      (Fintype.card H : ℚ) := by
  let stabilizerAction :
      MulDistribMulAction H (Multiplicative ℤ) :=
    trivialIntMulDistribMulAction H
  let stabilizerFintype : Fintype H :=
    Fintype.ofFinite H
  let δ :=
    subgroupGeneratorOfGenerator H σ hgen
  let stabilizerH0Finite :
      Finite
        (HerbrandH0 H (Multiplicative ℤ)) :=
    trivialIntHerbrandH0Finite (G := H)
  let stabilizerHMinusOneFinite :
      Finite
        (HerbrandHMinusOne H
          (Multiplicative ℤ) δ) :=
    trivialIntHerbrandHMinusOneFinite
      (G := H) δ
  let h0Finite :
      Finite
        (HerbrandH0 G
          (TransitivePermutationLattice H)) :=
    transitivePermutationLatticeHerbrandH0Finite
      H σ hgen
  let hMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (TransitivePermutationLattice H) σ) :=
    transitivePermutationLatticeHerbrandHMinusOneFinite
      H σ hgen
  have h0Card :
      Nat.card
          (HerbrandH0 G
            (TransitivePermutationLattice H)) =
        Fintype.card H := by
    calc
      Nat.card
          (HerbrandH0 G
            (TransitivePermutationLattice H)) =
        Nat.card
          (HerbrandH0 H
            (Multiplicative ℤ)) :=
        Nat.card_congr
          (inducedHerbrandH0EquivOfFiniteCyclic
            H σ hgen).toEquiv
      _ = Fintype.card H :=
        trivialInt_herbrandH0_card (G := H)
  have hMinusOneCard :
      Nat.card
          (HerbrandHMinusOne G
            (TransitivePermutationLattice H) σ) =
        1 := by
    calc
      Nat.card
          (HerbrandHMinusOne G
            (TransitivePermutationLattice H) σ) =
        Nat.card
          (HerbrandHMinusOne H
            (Multiplicative ℤ) δ) :=
        Nat.card_congr
          (inducedHerbrandHMinusOneEquivOfFiniteCyclic
            H σ hgen).toEquiv
      _ = 1 :=
        trivialInt_herbrandHMinusOne_card_eq_one
          (G := H) δ
  rw [herbrandQuotient_eq_card_ratio,
    h0Card, hMinusOneCard]
  simp

end TransitivePermutationLattice

section PermutationLatticeOrbits

variable {G : Type uG} [Group G] [Fintype G]
variable {ι : Type uι} [Fintype ι]

/-- A finite permutation lattice presented by chosen orbit representatives:
`H i` is the stabilizer of the representative of orbit `i`. -/
abbrev PermutationLatticeOrbitFamily
    (H : ι → Subgroup G)
    [∀ i,
      MulDistribMulAction (H i)
        (Multiplicative ℤ)] :=
  ∀ i, TransitivePermutationLattice (H i)

/-- The Herbrand quotient of a finite permutation lattice is
the product of the orders of the stabilizers of chosen orbit
representatives. -/
theorem permutationLattice_herbrandQuotient_eq_stabilizerProduct
    (H : ι → Subgroup G)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _stabilizerAction : ∀ i,
        MulDistribMulAction (H i)
          (Multiplicative ℤ) :=
      fun i ↦ trivialIntMulDistribMulAction (H i)
    letI _stabilizerFintype : ∀ i,
        Fintype (H i) :=
      fun _ ↦ Fintype.ofFinite _
    letI _orbitAction : ∀ i,
        MulDistribMulAction G
          (TransitivePermutationLattice (H i)) :=
      fun i ↦ inducedMulDistribMulAction (H i)
    letI _familyAction :
        MulDistribMulAction G
          (PermutationLatticeOrbitFamily H) :=
      piMulDistribMulAction G
        (fun i ↦
          TransitivePermutationLattice (H i))
    letI _orbitH0Finite : ∀ i,
        Finite
          (HerbrandH0 G
            (TransitivePermutationLattice (H i))) :=
      fun i ↦
        transitivePermutationLatticeHerbrandH0Finite
          (H i) σ hgen
    letI _orbitHMinusOneFinite : ∀ i,
        Finite
          (HerbrandHMinusOne G
            (TransitivePermutationLattice (H i)) σ) :=
      fun i ↦
        transitivePermutationLatticeHerbrandHMinusOneFinite
          (H i) σ hgen
    letI _familyH0Finite :
        Finite
          (HerbrandH0 G
            (PermutationLatticeOrbitFamily H)) :=
      Finite.of_equiv
        (∀ i,
          HerbrandH0 G
            (TransitivePermutationLattice (H i)))
        (herbrandH0PiEquiv
          (G := G)
          (fun i ↦
            TransitivePermutationLattice
              (H i))).symm.toEquiv
    letI _familyHMinusOneFinite :
        Finite
          (HerbrandHMinusOne G
            (PermutationLatticeOrbitFamily H) σ) :=
      Finite.of_equiv
        (∀ i,
          HerbrandHMinusOne G
            (TransitivePermutationLattice (H i)) σ)
        (herbrandHMinusOnePiEquiv
          (G := G)
          (fun i ↦
            TransitivePermutationLattice
              (H i)) σ).symm.toEquiv
    herbrandQuotient
        (G := G)
        (A := PermutationLatticeOrbitFamily H) σ =
      ∏ i, (Fintype.card (H i) : ℚ) := by
  let stabilizerAction : ∀ i,
      MulDistribMulAction (H i)
        (Multiplicative ℤ) :=
    fun i ↦ trivialIntMulDistribMulAction (H i)
  let stabilizerFintype : ∀ i,
      Fintype (H i) :=
    fun _ ↦ Fintype.ofFinite _
  let orbitAction : ∀ i,
      MulDistribMulAction G
        (TransitivePermutationLattice (H i)) :=
    fun i ↦ inducedMulDistribMulAction (H i)
  let familyAction :
      MulDistribMulAction G
        (PermutationLatticeOrbitFamily H) :=
    piMulDistribMulAction G
      (fun i ↦
        TransitivePermutationLattice (H i))
  let orbitH0Finite : ∀ i,
      Finite
        (HerbrandH0 G
          (TransitivePermutationLattice (H i))) :=
    fun i ↦
      transitivePermutationLatticeHerbrandH0Finite
        (H i) σ hgen
  let orbitHMinusOneFinite : ∀ i,
      Finite
        (HerbrandHMinusOne G
          (TransitivePermutationLattice (H i)) σ) :=
    fun i ↦
      transitivePermutationLatticeHerbrandHMinusOneFinite
        (H i) σ hgen
  let familyH0Finite :
      Finite
        (HerbrandH0 G
          (PermutationLatticeOrbitFamily H)) :=
    Finite.of_equiv
      (∀ i,
        HerbrandH0 G
          (TransitivePermutationLattice (H i)))
      (herbrandH0PiEquiv
        (G := G)
        (fun i ↦
          TransitivePermutationLattice
            (H i))).symm.toEquiv
  let familyHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (PermutationLatticeOrbitFamily H) σ) :=
    Finite.of_equiv
      (∀ i,
        HerbrandHMinusOne G
          (TransitivePermutationLattice (H i)) σ)
      (herbrandHMinusOnePiEquiv
        (G := G)
        (fun i ↦
          TransitivePermutationLattice
            (H i)) σ).symm.toEquiv
  calc
    herbrandQuotient
        (G := G)
        (A := PermutationLatticeOrbitFamily H) σ =
        ∏ i, herbrandQuotient
          (G := G)
          (A := TransitivePermutationLattice
            (H i)) σ :=
      herbrandQuotient_pi
        (fun i ↦
          TransitivePermutationLattice
            (H i)) σ
    _ = ∏ i, (Fintype.card (H i) : ℚ) := by
      apply Finset.prod_congr rfl
      intro i _
      exact
        transitivePermutationLattice_herbrandQuotient_eq_stabilizerCard
          (H i) σ hgen

end PermutationLatticeOrbits

section CanonicalPermutationFunctions

variable {G : Type uG} [Group G] [Fintype G]
variable {ι : Type uι} [Fintype ι] [MulAction G ι]

/-- The contragredient action on integer-valued functions on a finite
`G`-set. -/
@[reducible]
def permutationFunctionMulDistribMulAction :
    MulDistribMulAction G (ι → Multiplicative ℤ) where
  smul g f i := f (g⁻¹ • i)
  one_smul f := by
    funext i
    change f ((1 : G)⁻¹ • i) = f i
    rw [inv_one, one_smul]
  mul_smul g h f := by
    funext i
    change f ((g * h)⁻¹ • i) =
      f (h⁻¹ • (g⁻¹ • i))
    rw [mul_inv_rev, mul_smul]
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- A chosen representative of the orbit containing `i`. -/
noncomputable def chosenPermutationOrbitRepresentative
    (i : ι) : ι :=
  Quotient.out
    (Quotient.mk'' i :
      MulAction.orbitRel.Quotient G ι)

omit [Fintype G] [Fintype ι] in
theorem chosenPermutationOrbitRepresentative_sameOrbit
    (i : ι) :
    i ∈ MulAction.orbit G
      (chosenPermutationOrbitRepresentative (G := G) i) := by
  rw [← MulAction.orbitRel_apply, ← Quotient.eq'']
  exact
    (Quotient.out_eq'
      (Quotient.mk'' i :
        MulAction.orbitRel.Quotient G ι)).symm

/-- A chosen group element carrying the chosen representative of
the orbit of `i` to `i`. -/
noncomputable def chosenPermutationOrbitTransport
    (i : ι) : G :=
  Classical.choose
    (chosenPermutationOrbitRepresentative_sameOrbit
      (G := G) i)

omit [Fintype G] [Fintype ι] in
theorem chosenPermutationOrbitTransport_smul
    (i : ι) :
    chosenPermutationOrbitTransport (G := G) i •
        chosenPermutationOrbitRepresentative (G := G) i = i :=
  Classical.choose_spec
    (chosenPermutationOrbitRepresentative_sameOrbit
      (G := G) i)

/-- The stabilizer of the chosen representative of an orbit. -/
abbrev permutationOrbitStabilizer
    (ω : MulAction.orbitRel.Quotient G ι) :
    Subgroup G :=
  MulAction.stabilizer G ω.out

/-- Integer-valued functions on a finite `G`-set, decomposed into the
induced modules belonging to its orbits. -/
noncomputable def permutationFunctionOrbitEquiv :
    letI _stabilizerAction :
        ∀ ω : MulAction.orbitRel.Quotient G ι,
          MulDistribMulAction
            (permutationOrbitStabilizer ω)
            (Multiplicative ℤ) :=
      fun ω =>
        trivialIntMulDistribMulAction
          (permutationOrbitStabilizer ω)
    (ι → Multiplicative ℤ) ≃*
      PermutationLatticeOrbitFamily
        (fun ω : MulAction.orbitRel.Quotient G ι =>
          permutationOrbitStabilizer ω) := by
  letI stabilizerAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction
          (permutationOrbitStabilizer ω)
          (Multiplicative ℤ) :=
    fun ω =>
      trivialIntMulDistribMulAction
        (permutationOrbitStabilizer ω)
  refine
    { toFun := fun f ω =>
        ⟨fun x => f (x⁻¹ • ω.out), ?_⟩
      invFun := fun F i =>
        (F (Quotient.mk'' i)).1
          ((chosenPermutationOrbitTransport
            (G := G) i)⁻¹)
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · intro h x
    change
      f ((h.1 * x)⁻¹ • ω.out) =
        f (x⁻¹ • ω.out)
    have hhInv :
        h.1⁻¹ • ω.out = ω.out := by
      calc
        h.1⁻¹ • ω.out =
            h.1⁻¹ • (h.1 • ω.out) :=
          congrArg (fun y => h.1⁻¹ • y) h.2.symm
        _ = ω.out := inv_smul_smul h.1 ω.out
    rw [mul_inv_rev, mul_smul, hhInv]
  · intro f
    funext i
    change
      f (((chosenPermutationOrbitTransport
          (G := G) i)⁻¹)⁻¹ •
          chosenPermutationOrbitRepresentative
            (G := G) i) = f i
    rw [inv_inv, chosenPermutationOrbitTransport_smul]
  · intro F
    funext ω
    apply Subtype.ext
    funext x
    have hω :
        (Quotient.mk'' (x⁻¹ • ω.out) :
            MulAction.orbitRel.Quotient G ι) = ω := by
      calc
        (Quotient.mk'' (x⁻¹ • ω.out) :
            MulAction.orbitRel.Quotient G ι) =
            Quotient.mk'' ω.out := by
              exact Quotient.sound
                (MulAction.orbitRel_apply.mpr
                  ⟨x⁻¹, rfl⟩)
        _ = ω := Quotient.out_eq' ω
    let t : G :=
      chosenPermutationOrbitTransport
        (G := G) (x⁻¹ • ω.out)
    have ht :
        t • ω.out = x⁻¹ • ω.out := by
      have ht' :=
        chosenPermutationOrbitTransport_smul
          (G := G) (x⁻¹ • ω.out)
      simpa only [t, chosenPermutationOrbitRepresentative,
        hω] using ht'
    let h : permutationOrbitStabilizer ω :=
      ⟨t⁻¹ * x⁻¹, by
        change (t⁻¹ * x⁻¹) • ω.out = ω.out
        rw [mul_smul, ← ht, inv_smul_smul]⟩
    change
      (F (Quotient.mk'' (x⁻¹ • ω.out))).1
          ((chosenPermutationOrbitTransport
            (G := G) (x⁻¹ • ω.out))⁻¹) =
        (F ω).1 x
    rw [hω]
    change (F ω).1 t⁻¹ = (F ω).1 x
    have hcov := (F ω).2 h x
    change (F ω).1 (h.1 * x) = (F ω).1 x at hcov
    simpa [h, mul_assoc] using hcov
  · intro f k
    funext ω
    apply Subtype.ext
    funext x
    rfl

omit [Fintype G] [Fintype ι] in
/-- The orbit decomposition of integer-valued functions is
`G`-equivariant. -/
theorem permutationFunctionOrbitEquiv_equivariant :
    letI _functionAction :
        MulDistribMulAction G (ι → Multiplicative ℤ) :=
      permutationFunctionMulDistribMulAction
    letI _stabilizerAction :
        ∀ ω : MulAction.orbitRel.Quotient G ι,
          MulDistribMulAction
            (permutationOrbitStabilizer ω)
            (Multiplicative ℤ) :=
      fun ω =>
        trivialIntMulDistribMulAction
          (permutationOrbitStabilizer ω)
    letI _orbitAction :
        ∀ ω : MulAction.orbitRel.Quotient G ι,
          MulDistribMulAction G
            (TransitivePermutationLattice
              (permutationOrbitStabilizer ω)) :=
      fun ω =>
        inducedMulDistribMulAction
          (permutationOrbitStabilizer ω)
    letI _familyAction :
        MulDistribMulAction G
          (PermutationLatticeOrbitFamily
            (fun ω : MulAction.orbitRel.Quotient G ι =>
              permutationOrbitStabilizer ω)) :=
      piMulDistribMulAction G
        (fun ω : MulAction.orbitRel.Quotient G ι =>
          TransitivePermutationLattice
            (permutationOrbitStabilizer ω))
    ∀ (g : G) (f : ι → Multiplicative ℤ),
      permutationFunctionOrbitEquiv (G := G) (ι := ι)
          (g • f) =
        g • permutationFunctionOrbitEquiv
          (G := G) (ι := ι) f := by
  let functionAction :
      MulDistribMulAction G (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let stabilizerAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction
          (permutationOrbitStabilizer ω)
          (Multiplicative ℤ) :=
    fun ω =>
      trivialIntMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let orbitAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) :=
    fun ω =>
      inducedMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let familyAction :
      MulDistribMulAction G
        (PermutationLatticeOrbitFamily
          (fun ω : MulAction.orbitRel.Quotient G ι =>
            permutationOrbitStabilizer ω)) :=
    piMulDistribMulAction G
      (fun ω : MulAction.orbitRel.Quotient G ι =>
        TransitivePermutationLattice
          (permutationOrbitStabilizer ω))
  intro g f
  funext ω
  apply Subtype.ext
  funext x
  change
    f (g⁻¹ • (x⁻¹ • ω.out)) =
      f ((x * g)⁻¹ • ω.out)
  rw [mul_inv_rev, mul_smul]

omit [Fintype ι] in
/-- Degree-zero Tate cohomology of a finite integral permutation module
is finite for a cyclic generator. -/
theorem permutationFunctionHerbrandH0Finite [Finite ι]
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _functionAction :
        MulDistribMulAction G (ι → Multiplicative ℤ) :=
      permutationFunctionMulDistribMulAction
    Finite
      (HerbrandH0 G (ι → Multiplicative ℤ)) := by
  classical
  let := Fintype.ofFinite ι
  let functionAction :
      MulDistribMulAction G (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let stabilizerAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction
          (permutationOrbitStabilizer ω)
          (Multiplicative ℤ) :=
    fun ω =>
      trivialIntMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let stabilizerFintype :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  let orbitAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) :=
    fun ω =>
      inducedMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let familyAction :
      MulDistribMulAction G
        (PermutationLatticeOrbitFamily
          (fun ω : MulAction.orbitRel.Quotient G ι =>
            permutationOrbitStabilizer ω)) :=
    piMulDistribMulAction G
      (fun ω : MulAction.orbitRel.Quotient G ι =>
        TransitivePermutationLattice
          (permutationOrbitStabilizer ω))
  let orbitH0Finite :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Finite
          (HerbrandH0 G
            (TransitivePermutationLattice
              (permutationOrbitStabilizer ω))) :=
    fun ω =>
      transitivePermutationLatticeHerbrandH0Finite
        (permutationOrbitStabilizer ω) σ hgen
  let familyH0Finite :
      Finite
        (HerbrandH0 G
          (PermutationLatticeOrbitFamily
            (fun ω : MulAction.orbitRel.Quotient G ι =>
              permutationOrbitStabilizer ω))) :=
    Finite.of_equiv
      (∀ ω : MulAction.orbitRel.Quotient G ι,
        HerbrandH0 G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)))
      (herbrandH0PiEquiv
        (G := G)
        (fun ω : MulAction.orbitRel.Quotient G ι =>
          TransitivePermutationLattice
            (permutationOrbitStabilizer ω))).symm.toEquiv
  let e :=
    permutationFunctionOrbitEquiv
      (G := G) (ι := ι)
  let he :=
    permutationFunctionOrbitEquiv_equivariant
      (G := G) (ι := ι)
  exact
    herbrandH0Finite_of_equivariantMulEquiv
      e.symm (mulEquiv_symm_commutes_smul e he)

omit [Fintype ι] in
/-- Degree-minus-one Tate cohomology of a finite integral permutation
module is finite for a cyclic generator. -/
theorem permutationFunctionHerbrandHMinusOneFinite [Finite ι]
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _functionAction :
        MulDistribMulAction G (ι → Multiplicative ℤ) :=
      permutationFunctionMulDistribMulAction
    Finite
      (HerbrandHMinusOne G
        (ι → Multiplicative ℤ) σ) := by
  classical
  let := Fintype.ofFinite ι
  let functionAction :
      MulDistribMulAction G (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let stabilizerAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction
          (permutationOrbitStabilizer ω)
          (Multiplicative ℤ) :=
    fun ω =>
      trivialIntMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let stabilizerFintype :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  let orbitAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) :=
    fun ω =>
      inducedMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let familyAction :
      MulDistribMulAction G
        (PermutationLatticeOrbitFamily
          (fun ω : MulAction.orbitRel.Quotient G ι =>
            permutationOrbitStabilizer ω)) :=
    piMulDistribMulAction G
      (fun ω : MulAction.orbitRel.Quotient G ι =>
        TransitivePermutationLattice
          (permutationOrbitStabilizer ω))
  let orbitHMinusOneFinite :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Finite
          (HerbrandHMinusOne G
            (TransitivePermutationLattice
              (permutationOrbitStabilizer ω)) σ) :=
    fun ω =>
      transitivePermutationLatticeHerbrandHMinusOneFinite
        (permutationOrbitStabilizer ω) σ hgen
  let familyHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (PermutationLatticeOrbitFamily
            (fun ω : MulAction.orbitRel.Quotient G ι =>
              permutationOrbitStabilizer ω)) σ) :=
    Finite.of_equiv
      (∀ ω : MulAction.orbitRel.Quotient G ι,
        HerbrandHMinusOne G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) σ)
      (herbrandHMinusOnePiEquiv
        (G := G)
        (fun ω : MulAction.orbitRel.Quotient G ι =>
          TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) σ).symm.toEquiv
  let e :=
    permutationFunctionOrbitEquiv
      (G := G) (ι := ι)
  let he :=
    permutationFunctionOrbitEquiv_equivariant
      (G := G) (ι := ι)
  exact
    herbrandHMinusOneFinite_of_equivariantMulEquiv
      e.symm (mulEquiv_symm_commutes_smul e he) σ

omit [Fintype ι] in
/-- Canonical orbit form of the permutation-lattice Herbrand quotient formula: the Herbrand
quotient of the
integer-valued functions on a finite `G`-set is the product of the
orders of the stabilizers of its orbits. -/
theorem permutationFunction_herbrandQuotient_eq_stabilizerProduct [Finite ι]
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _functionAction :
        MulDistribMulAction G (ι → Multiplicative ℤ) :=
      permutationFunctionMulDistribMulAction
    letI _orbitFintype :
        Fintype (MulAction.orbitRel.Quotient G ι) :=
      Fintype.ofFinite _
    letI _stabilizerFintype :
        ∀ ω : MulAction.orbitRel.Quotient G ι,
          Fintype (permutationOrbitStabilizer ω) :=
      fun _ => Fintype.ofFinite _
    letI _functionH0Finite :
        Finite
          (HerbrandH0 G
            (ι → Multiplicative ℤ)) :=
      permutationFunctionHerbrandH0Finite σ hgen
    letI _functionHMinusOneFinite :
        Finite
          (HerbrandHMinusOne G
            (ι → Multiplicative ℤ) σ) :=
      permutationFunctionHerbrandHMinusOneFinite σ hgen
    herbrandQuotient
        (G := G) (A := ι → Multiplicative ℤ) σ =
      ∏ ω : MulAction.orbitRel.Quotient G ι,
        (Fintype.card
          (permutationOrbitStabilizer ω) : ℚ) := by
  classical
  let := Fintype.ofFinite ι
  let functionAction :
      MulDistribMulAction G (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let orbitFintype :
      Fintype (MulAction.orbitRel.Quotient G ι) :=
    Fintype.ofFinite _
  let stabilizerAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction
          (permutationOrbitStabilizer ω)
          (Multiplicative ℤ) :=
    fun ω =>
      trivialIntMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let stabilizerFintype :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  let orbitAction :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        MulDistribMulAction G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) :=
    fun ω =>
      inducedMulDistribMulAction
        (permutationOrbitStabilizer ω)
  let familyAction :
      MulDistribMulAction G
        (PermutationLatticeOrbitFamily
          (fun ω : MulAction.orbitRel.Quotient G ι =>
            permutationOrbitStabilizer ω)) :=
    piMulDistribMulAction G
      (fun ω : MulAction.orbitRel.Quotient G ι =>
        TransitivePermutationLattice
          (permutationOrbitStabilizer ω))
  let orbitH0Finite :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Finite
          (HerbrandH0 G
            (TransitivePermutationLattice
              (permutationOrbitStabilizer ω))) :=
    fun ω =>
      transitivePermutationLatticeHerbrandH0Finite
        (permutationOrbitStabilizer ω) σ hgen
  let orbitHMinusOneFinite :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Finite
          (HerbrandHMinusOne G
            (TransitivePermutationLattice
              (permutationOrbitStabilizer ω)) σ) :=
    fun ω =>
      transitivePermutationLatticeHerbrandHMinusOneFinite
        (permutationOrbitStabilizer ω) σ hgen
  let familyH0Finite :
      Finite
        (HerbrandH0 G
          (PermutationLatticeOrbitFamily
            (fun ω : MulAction.orbitRel.Quotient G ι =>
              permutationOrbitStabilizer ω))) :=
    Finite.of_equiv
      (∀ ω : MulAction.orbitRel.Quotient G ι,
        HerbrandH0 G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)))
      (herbrandH0PiEquiv
        (G := G)
        (fun ω : MulAction.orbitRel.Quotient G ι =>
          TransitivePermutationLattice
            (permutationOrbitStabilizer ω))).symm.toEquiv
  let familyHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (PermutationLatticeOrbitFamily
            (fun ω : MulAction.orbitRel.Quotient G ι =>
              permutationOrbitStabilizer ω)) σ) :=
    Finite.of_equiv
      (∀ ω : MulAction.orbitRel.Quotient G ι,
        HerbrandHMinusOne G
          (TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) σ)
      (herbrandHMinusOnePiEquiv
        (G := G)
        (fun ω : MulAction.orbitRel.Quotient G ι =>
          TransitivePermutationLattice
            (permutationOrbitStabilizer ω)) σ).symm.toEquiv
  let functionH0Finite :
      Finite
        (HerbrandH0 G
          (ι → Multiplicative ℤ)) :=
    permutationFunctionHerbrandH0Finite σ hgen
  let functionHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (ι → Multiplicative ℤ) σ) :=
    permutationFunctionHerbrandHMinusOneFinite σ hgen
  let e :=
    permutationFunctionOrbitEquiv
      (G := G) (ι := ι)
  let he :=
    permutationFunctionOrbitEquiv_equivariant
      (G := G) (ι := ι)
  calc
    herbrandQuotient
        (G := G) (A := ι → Multiplicative ℤ) σ =
        herbrandQuotient
          (G := G)
          (A := PermutationLatticeOrbitFamily
            (fun ω : MulAction.orbitRel.Quotient G ι =>
              permutationOrbitStabilizer ω)) σ := by
      simpa only [e, he] using
        (herbrandQuotient_eq_of_equivariantMulEquiv
          e he σ)
    _ = ∏ ω : MulAction.orbitRel.Quotient G ι,
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ) :=
      permutationLattice_herbrandQuotient_eq_stabilizerProduct
        (fun ω : MulAction.orbitRel.Quotient G ι =>
          permutationOrbitStabilizer ω) σ hgen

end CanonicalPermutationFunctions

section FiniteIndexStableSubgroup

variable {G : Type uG} {A : Type uA}
    [Group G] [CommGroup A]
    [MulDistribMulAction G A]

/-- Restriction of an action to a stable subgroup. -/
@[reducible]
def stableSubgroupMulDistribMulAction
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B) :
    MulDistribMulAction G B where
  smul g x := ⟨g • x.1, hstable g x.1 x.2⟩
  one_smul x := by
    apply Subtype.ext
    exact one_smul G x.1
  mul_smul g h x := by
    apply Subtype.ext
    exact mul_smul g h x.1
  smul_one g := by
    apply Subtype.ext
    exact MulDistribMulAction.smul_one g
  smul_mul g x y := by
    apply Subtype.ext
    exact MulDistribMulAction.smul_mul
      g x.1 y.1

@[simp]
theorem stableSubgroup_smul_coe
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B)
    (g : G) (x : B) :
    letI :=
      stableSubgroupMulDistribMulAction
        B hstable
    ((g • x : B) : A) = g • (x : A) :=
  rfl

/-- The action induced on the quotient by a stable subgroup. -/
@[reducible]
def stableQuotientMulDistribMulAction
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B) :
    MulDistribMulAction G (A ⧸ B) where
  smul g q :=
    QuotientGroup.map B B
      (MulDistribMulAction.toMonoidHom A g)
      (fun _ hx ↦ hstable g _ hx) q
  one_smul q := by
    refine QuotientGroup.induction_on q ?_
    intro x
    change
      QuotientGroup.mk' B ((1 : G) • x) =
        QuotientGroup.mk' B x
    rw [one_smul]
  mul_smul g h q := by
    refine QuotientGroup.induction_on q ?_
    intro x
    change
      QuotientGroup.mk' B ((g * h) • x) =
        QuotientGroup.mk' B (g • h • x)
    rw [mul_smul]
  smul_one g :=
    map_one
      (QuotientGroup.map B B
        (MulDistribMulAction.toMonoidHom A g)
        (fun _ hx ↦ hstable g _ hx))
  smul_mul g q r :=
    map_mul
      (QuotientGroup.map B B
        (MulDistribMulAction.toMonoidHom A g)
        (fun _ hx ↦ hstable g _ hx))
      q r

theorem stableQuotient_smul_mk
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B)
    (g : G) (x : A) :
    letI :=
      stableQuotientMulDistribMulAction
        B hstable
    g • QuotientGroup.mk' B x =
      QuotientGroup.mk' B (g • x) :=
  rfl

/-- The inclusion of a stable subgroup is equivariant. -/
theorem stableSubgroup_subtype_equivariant
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B) :
    letI :=
      stableSubgroupMulDistribMulAction
        B hstable
    ∀ (g : G) (x : B),
      B.subtype (g • x) = g • B.subtype x := by
  let :=
    stableSubgroupMulDistribMulAction
      B hstable
  intro g x
  rfl

/-- The quotient map by a stable subgroup is equivariant. -/
theorem stableSubgroup_quotientMap_equivariant
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B) :
    letI :=
      stableQuotientMulDistribMulAction
        B hstable
    ∀ (g : G) (x : A),
      QuotientGroup.mk' B (g • x) =
        g • QuotientGroup.mk' B x := by
  let :=
    stableQuotientMulDistribMulAction
      B hstable
  intro g x
  rfl

/-- Exactness of the inclusion followed by the quotient map. -/
theorem stableSubgroup_quotientMap_exact
    (B : Subgroup A) :
    ∀ x : A,
      QuotientGroup.mk' B x = 1 ↔
        ∃ b : B, B.subtype b = x := by
  intro x
  constructor
  · intro hx
    have hxB :
        x ∈ B :=
      (QuotientGroup.eq_one_iff x).mp hx
    exact ⟨⟨x, hxB⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact
      (QuotientGroup.eq_one_iff b.1).mpr
        b.2

end FiniteIndexStableSubgroup

section FiniteIndexStableSubgroupFiniteness

variable {G A : Type}
    [Group G] [CommGroup A]
    [MulDistribMulAction G A]

variable [Fintype G]

/-- If the Herbrand quotient is defined on a stable finite-index
subgroup, then it is defined on the ambient module.  Finiteness of the
quotient supplies the third term of the exact-sequence argument. -/
theorem finiteIndexStableSubgroup_ambientHerbrandQuotientDefined
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ)
    (hB :
      letI :=
        stableSubgroupMulDistribMulAction
          B hstable
      HerbrandQuotientDefined G B σ)
    [Finite (A ⧸ B)] :
    letI _subgroupAction :=
      stableSubgroupMulDistribMulAction
        B hstable
    letI _quotientAction :=
      stableQuotientMulDistribMulAction
        B hstable
    HerbrandQuotientDefined G A σ := by
  let subgroupAction :=
    stableSubgroupMulDistribMulAction
      B hstable
  let quotientAction :=
    stableQuotientMulDistribMulAction
      B hstable
  let hQ :
      HerbrandQuotientDefined
        G (A ⧸ B) σ :=
    ⟨inferInstance, inferInstance⟩
  exact
    herbrandQuotientDefined_middle_of_left_right
      B.subtype (QuotientGroup.mk' B)
      (stableSubgroup_subtype_equivariant
        B hstable)
      (stableSubgroup_quotientMap_equivariant
        B hstable)
      (stableSubgroup_quotientMap_exact B)
      B.subtype_injective
      (QuotientGroup.mk'_surjective B)
      σ hgen hB hQ

/-- Finite-index invariance for permutation lattices: passing from a cyclic
`G`-module to a stable subgroup with finite quotient does not change the
Herbrand quotient. -/
theorem herbrandQuotient_eq_of_finiteIndex_stableSubgroup
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ)
    (hB :
      letI :=
        stableSubgroupMulDistribMulAction
          B hstable
      HerbrandQuotientDefined G B σ)
    [Finite (A ⧸ B)] :
    letI _subgroupAction :=
      stableSubgroupMulDistribMulAction
        B hstable
    letI _quotientAction :=
      stableQuotientMulDistribMulAction
        B hstable
    let hA :=
      finiteIndexStableSubgroup_ambientHerbrandQuotientDefined
        B hstable σ hgen hB
    @herbrandQuotient G A _ _ _ _
        σ hA.1 hA.2 =
      @herbrandQuotient G B _ _ _ _
        σ hB.1 hB.2 := by
  let subgroupAction :=
    stableSubgroupMulDistribMulAction
      B hstable
  let quotientAction :=
    stableQuotientMulDistribMulAction
      B hstable
  let hQ :
      HerbrandQuotientDefined
        G (A ⧸ B) σ :=
    ⟨inferInstance, inferInstance⟩
  let hA :=
    finiteIndexStableSubgroup_ambientHerbrandQuotientDefined
      B hstable σ hgen hB
  let : Finite
      (HerbrandH0 G B) := hB.1
  let : Finite
      (HerbrandHMinusOne G B σ) := hB.2
  let : Finite
      (HerbrandH0 G A) := hA.1
  let : Finite
      (HerbrandHMinusOne G A σ) := hA.2
  let : Finite
      (HerbrandH0 G (A ⧸ B)) := hQ.1
  let : Finite
      (HerbrandHMinusOne G (A ⧸ B) σ) :=
    hQ.2
  have hmult :
      herbrandQuotient
          (G := G) (A := A) σ =
        herbrandQuotient
            (G := G) (A := B) σ *
          herbrandQuotient
            (G := G) (A := A ⧸ B) σ :=
    herbrandQuotient_multiplicative_of_shortExact
      B.subtype (QuotientGroup.mk' B)
      (stableSubgroup_subtype_equivariant
        B hstable)
      (stableSubgroup_quotientMap_equivariant
        B hstable)
      (stableSubgroup_quotientMap_exact B)
      B.subtype_injective
      (QuotientGroup.mk'_surjective B)
      σ hgen
  have hquotient :
      herbrandQuotient
          (G := G) (A := A ⧸ B) σ = 1 :=
    herbrandQuotient_eq_one_of_finite_module
      (G := G) (A := A ⧸ B) σ hgen
  change
    @herbrandQuotient G A _ _ _ _
        σ hA.1 hA.2 =
      @herbrandQuotient G B _ _ _ _
        σ hB.1 hB.2
  calc
    @herbrandQuotient G A _ _ _ _
          σ hA.1 hA.2 =
        @herbrandQuotient G B _ _ _ _
            σ hB.1 hB.2 *
          @herbrandQuotient G (A ⧸ B)
            _ _ _ _ σ hQ.1 hQ.2 :=
      hmult
    _ = @herbrandQuotient G B _ _ _ _
          σ hB.1 hB.2 := by
      rw [hquotient, mul_one]

end FiniteIndexStableSubgroupFiniteness

end CyclicCohomology
