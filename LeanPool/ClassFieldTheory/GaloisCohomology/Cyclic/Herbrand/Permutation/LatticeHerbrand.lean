/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.Permutation.Lattice
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.Permutation.Module
/-!
# Herbrand quotients of complete permutation sublattices

This file connects the complete permutation sublattice with its
orbit-stabilizer Herbrand quotient calculation.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace CyclicCohomology

open Module Submodule
open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uι

variable {G : Type uG} {ι : Type uι}

/-- The action on an indexing type specified by a permutation
representation. -/
@[reducible]
def permutationMulAction
    [Group G] (ρ : G →* Equiv.Perm ι) :
    MulAction G ι where
  smul g i := ρ g i
  one_smul i := by
    change ρ 1 i = i
    rw [map_one]
    rfl
  mul_smul g h i := by
    change ρ (g * h) i = ρ g (ρ h i)
    rw [map_mul]
    rfl

/-- Coordinate permutation over the integers. -/
def intCoordinatePermutation (σ : Equiv.Perm ι) :
    (ι → ℤ) ≃ₗ[ℤ] (ι → ℤ) where
  toFun x i := x (σ.symm i)
  invFun x i := x (σ i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section IntegralPermutationBasis

variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]
variable {M : Type*} [AddCommGroup M] [Module ℤ M]

omit [Fintype G] in
omit [DecidableEq ι] [Fintype ι] in
/-- Coordinates in a basis permuted by `G` transform by the
contragredient coordinate permutation. -/
theorem basisEquivFun_symm_intCoordinatePermutation [Finite ι]
    (b : Basis ι ℤ M)
    (ρ : G →* Equiv.Perm ι)
    (α : G →* (M ≃ₗ[ℤ] M))
    (hb : ∀ (g : G) (i : ι),
      α g (b i) = b (ρ g i))
    (g : G) (x : ι → ℤ) :
    b.equivFun.symm
        (intCoordinatePermutation (ρ g) x) =
      α g (b.equivFun.symm x) := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  let := Fintype.ofFinite ι
  have hmaps :
      b.equivFun.symm.toLinearMap.comp
          (intCoordinatePermutation (ρ g)).toLinearMap =
        (α g).toLinearMap.comp
          b.equivFun.symm.toLinearMap := by
    apply (Pi.basisFun ℤ ι).ext
    intro i
    simp only [LinearMap.comp_apply, Pi.basisFun_apply]
    have hsingle (j : ι) :
        b.equivFun.symm (Pi.single j 1) = b j := by
      exact _root_.Basis.equivFun_symm_single b j
    calc
      b.equivFun.symm
          (intCoordinatePermutation (ρ g)
            (Pi.single i 1)) =
          b.equivFun.symm
            (Pi.single (ρ g i) 1) := by
              congr 1
              ext j
              by_cases h : j = ρ g i
              · subst j
                simp [intCoordinatePermutation]
              · have h' : (ρ g).symm j ≠ i := by
                  intro hij
                  apply h
                  simpa using congrArg (ρ g) hij
                simp [intCoordinatePermutation, h, h']
      _ = b (ρ g i) := hsingle (ρ g i)
      _ = α g (b i) := (hb g i).symm
      _ = α g
          (b.equivFun.symm (Pi.single i 1)) := by
        rw [hsingle i]
  exact LinearMap.congr_fun hmaps x

end IntegralPermutationBasis

section StableSublattice

variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- The canonical permutation sublattice is stable under the
permutation representation. -/
theorem permutationSublattice_stable
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    ∀ (g : G) (x : ι → ℝ),
      x ∈ permutationSublattice ρ L hL →
        permutationRepresentation ρ g x ∈
          permutationSublattice ρ L hL := by
  intro g x hx
  rw [permutationSublattice] at hx ⊢
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i, rfl⟩
    have heq :
        permutationRepresentation ρ g
            (averagedLatticeVector ρ L hL
              (permutationLatticeScale L) i : ι → ℝ) =
          (averagedLatticeVector ρ L hL
            (permutationLatticeScale L) (ρ g i) :
              ι → ℝ) := by
      have h :=
        congrArg (fun q : L => (q : ι → ℝ))
          (averagedLatticeVector_equivariant
            ρ L hL (permutationLatticeScale L) g i)
      simpa only [coe_permutationLatticeEquiv] using h
    rw [heq]
    exact Submodule.subset_span ⟨ρ g i, rfl⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  · intro n y _ hy
    rw [map_zsmul]
    exact Submodule.smul_mem _ n hy

/-- The additive action on the canonical permutation sublattice. -/
@[reducible]
def permutationSublatticeDistribMulAction
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    DistribMulAction G (permutationSublattice ρ L hL) where
  smul g x :=
    ⟨permutationRepresentation ρ g x.1,
      permutationSublattice_stable ρ L hL g x.1 x.2⟩
  one_smul x := by
    apply Subtype.ext
    change permutationRepresentation ρ 1 x.1 = x.1
    rw [permutationRepresentation_one]
    rfl
  mul_smul g h x := by
    apply Subtype.ext
    change
      permutationRepresentation ρ (g * h) x.1 =
        permutationRepresentation ρ g
          (permutationRepresentation ρ h x.1)
    rw [permutationRepresentation_mul]
    rfl
  smul_zero g := by
    apply Subtype.ext
    exact map_zero (permutationRepresentation ρ g)
  smul_add g x y := by
    apply Subtype.ext
    exact map_add (permutationRepresentation ρ g) x.1 y.1

/-- An additive action, written multiplicatively. -/
@[reducible]
def multiplicativeDistribMulAction
    {A : Type*} [AddCommGroup A]
    [DistribMulAction G A] :
    MulDistribMulAction G (Multiplicative A) where
  smul g x := Multiplicative.ofAdd (g • Multiplicative.toAdd x)
  one_smul x := congrArg Multiplicative.ofAdd
    (one_smul G (Multiplicative.toAdd x))
  mul_smul g h x := congrArg Multiplicative.ofAdd
    (mul_smul g h (Multiplicative.toAdd x))
  smul_one g := congrArg Multiplicative.ofAdd
    (DistribMulAction.smul_zero g)
  smul_mul g x y := congrArg Multiplicative.ofAdd
    (DistribMulAction.smul_add g
      (Multiplicative.toAdd x) (Multiplicative.toAdd y))

/-- A submodule, written as a subgroup of the multiplicative copy of
its ambient additive group. -/
@[reducible]
def multiplicativeSubmoduleSubgroup
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (N : Submodule ℤ M) :
    Subgroup (Multiplicative M) :=
  N.toAddSubgroup.toSubgroup

/-- The multiplicative copy of a submodule is canonically equivalent
to the corresponding subgroup of the multiplicative ambient group. -/
def multiplicativeSubmoduleMulEquiv
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (N : Submodule ℤ M) :
    Multiplicative N ≃*
      multiplicativeSubmoduleSubgroup N where
  toFun x :=
    ⟨Multiplicative.ofAdd
        ((Multiplicative.toAdd x : N) : M),
      (Multiplicative.toAdd x : N).property⟩
  invFun x :=
    Multiplicative.ofAdd
      ⟨Multiplicative.toAdd x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Finiteness of an additive submodule quotient is unchanged after
passing to multiplicative notation. -/
theorem multiplicativeSubmoduleQuotientFinite
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (N : Submodule ℤ M)
    [Finite (M ⧸ N)] :
    Finite
      (Multiplicative M ⧸
        multiplicativeSubmoduleSubgroup N) := by
  let f :
      Multiplicative M →*
        Multiplicative (M ⧸ N) :=
    (QuotientAddGroup.mk'
      N.toAddSubgroup).toMultiplicative
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ :=
      QuotientAddGroup.mk'_surjective
        N.toAddSubgroup
        (Multiplicative.toAdd y)
    exact
      ⟨Multiplicative.ofAdd x,
        congrArg Multiplicative.ofAdd hx⟩
  have hker :
      f.ker =
        multiplicativeSubmoduleSubgroup N := by
    change
      (QuotientAddGroup.mk'
          N.toAddSubgroup).ker.toSubgroup =
        N.toAddSubgroup.toSubgroup
    rw [QuotientAddGroup.ker_mk']
  let e :
      Multiplicative M ⧸
          multiplicativeSubmoduleSubgroup N ≃*
        Multiplicative (M ⧸ N) :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact
    Finite.of_equiv
      (Multiplicative (M ⧸ N)) e.symm.toEquiv

/-- The action on any complete stable lattice induced by its
permutation representation. -/
@[reducible]
def completePermutationLatticeDistribMulAction
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    DistribMulAction G L where
  smul g x :=
    ⟨permutationRepresentation ρ g x.1,
      hL g x.1 x.2⟩
  one_smul x := by
    apply Subtype.ext
    change permutationRepresentation ρ 1 x.1 = x.1
    rw [permutationRepresentation_one]
    rfl
  mul_smul g h x := by
    apply Subtype.ext
    change
      permutationRepresentation ρ (g * h) x.1 =
        permutationRepresentation ρ g
          (permutationRepresentation ρ h x.1)
    rw [permutationRepresentation_mul]
    rfl
  smul_zero g := by
    apply Subtype.ext
    exact map_zero (permutationRepresentation ρ g)
  smul_add g x y := by
    apply Subtype.ext
    exact map_add (permutationRepresentation ρ g) x.1 y.1

/-- The canonical complete permutation sublattice, viewed as a
subgroup of the multiplicative copy of the ambient lattice. -/
noncomputable def permutationSublatticeMultiplicativeSubgroup
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Subgroup (Multiplicative L) :=
  multiplicativeSubmoduleSubgroup
    ((permutationSublattice ρ L hL).comap L.subtype)

/-- The permutation-sublattice subgroup is stable under the ambient
lattice action. -/
theorem
    permutationSublatticeMultiplicativeSubgroup_stable
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    letI _ambientAction :
        DistribMulAction G L :=
      completePermutationLatticeDistribMulAction
        ρ L hL
    letI _multiplicativeAction :
        MulDistribMulAction G
          (Multiplicative L) :=
      multiplicativeDistribMulAction
    ∀ (g : G) (x : Multiplicative L),
      x ∈
          permutationSublatticeMultiplicativeSubgroup
            ρ L hL →
        g • x ∈
          permutationSublatticeMultiplicativeSubgroup
            ρ L hL := by
  let ambientAction :
      DistribMulAction G L :=
    completePermutationLatticeDistribMulAction
      ρ L hL
  let multiplicativeAction :
      MulDistribMulAction G
        (Multiplicative L) :=
    multiplicativeDistribMulAction
  intro g x hx
  change
    permutationRepresentation ρ g
        ((Multiplicative.toAdd x : L) : ι → ℝ) ∈
      permutationSublattice ρ L hL
  change
    ((Multiplicative.toAdd x : L) : ι → ℝ) ∈
      permutationSublattice ρ L hL at hx
  exact
    permutationSublattice_stable
      ρ L hL g _ hx

/-- The canonical permutation-sublattice subgroup has finite quotient
in the multiplicative ambient lattice. -/
theorem
    permutationSublatticeMultiplicativeSubgroup_finite_quotient
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Finite
      (Multiplicative L ⧸
        permutationSublatticeMultiplicativeSubgroup
          ρ L hL) := by
  let N :
      Submodule ℤ L :=
    (permutationSublattice ρ L hL).comap
      L.subtype
  let quotientFinite : Finite (L ⧸ N) :=
    permutationSublattice_finite_quotient
      ρ L hL
  exact
    multiplicativeSubmoduleQuotientFinite N

/-- The subgroup cut out by the canonical permutation sublattice is
canonically the multiplicative copy of that sublattice. -/
noncomputable def
    permutationSublatticeSubgroupMulEquiv
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    permutationSublatticeMultiplicativeSubgroup
        ρ L hL ≃*
      Multiplicative
        (permutationSublattice ρ L hL) :=
  (multiplicativeSubmoduleMulEquiv
      ((permutationSublattice ρ L hL).comap
        L.subtype)).symm.trans
    (Submodule.comapSubtypeEquivOfLe
        (permutationSublattice_le ρ L hL)).toAddEquiv.toMultiplicative

/-- The canonical identification of the finite-index subgroup with
the permutation sublattice is equivariant. -/
theorem
    permutationSublatticeSubgroupMulEquiv_equivariant
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    letI _ambientAction :
        DistribMulAction G L :=
      completePermutationLatticeDistribMulAction
        ρ L hL
    letI _ambientMultiplicativeAction :
        MulDistribMulAction G
          (Multiplicative L) :=
      multiplicativeDistribMulAction
    letI _subgroupAction :
        MulDistribMulAction G
          (permutationSublatticeMultiplicativeSubgroup
            ρ L hL) :=
      stableSubgroupMulDistribMulAction
        (permutationSublatticeMultiplicativeSubgroup
          ρ L hL)
        (permutationSublatticeMultiplicativeSubgroup_stable
          ρ L hL)
    letI _sublatticeAction :
        DistribMulAction G
          (permutationSublattice ρ L hL) :=
      permutationSublatticeDistribMulAction ρ L hL
    letI _sublatticeMultiplicativeAction :
        MulDistribMulAction G
          (Multiplicative
            (permutationSublattice ρ L hL)) :=
      multiplicativeDistribMulAction
    ∀ (g : G)
      (x :
        permutationSublatticeMultiplicativeSubgroup
          ρ L hL),
      permutationSublatticeSubgroupMulEquiv
          ρ L hL (g • x) =
        g •
          permutationSublatticeSubgroupMulEquiv
            ρ L hL x := by
  let ambientAction :
      DistribMulAction G L :=
    completePermutationLatticeDistribMulAction
      ρ L hL
  let ambientMultiplicativeAction :
      MulDistribMulAction G
        (Multiplicative L) :=
    multiplicativeDistribMulAction
  let subgroupAction :
      MulDistribMulAction G
        (permutationSublatticeMultiplicativeSubgroup
          ρ L hL) :=
    stableSubgroupMulDistribMulAction
      (permutationSublatticeMultiplicativeSubgroup
        ρ L hL)
      (permutationSublatticeMultiplicativeSubgroup_stable
        ρ L hL)
  let sublatticeAction :
      DistribMulAction G
        (permutationSublattice ρ L hL) :=
    permutationSublatticeDistribMulAction ρ L hL
  let sublatticeMultiplicativeAction :
      MulDistribMulAction G
        (Multiplicative
          (permutationSublattice ρ L hL)) :=
    multiplicativeDistribMulAction
  intro g x
  rfl

/-- The integral-linear automorphisms underlying the action on the
canonical permutation sublattice. -/
noncomputable def permutationSublatticeModuleAut
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    G →* (permutationSublattice ρ L hL ≃ₗ[ℤ]
      permutationSublattice ρ L hL) := by
  letI :=
    permutationSublatticeDistribMulAction ρ L hL
  exact DistribMulAction.toModuleAut ℤ
    (permutationSublattice ρ L hL)

/-- Multiplicative coordinates in the distinguished integral basis of
the canonical permutation sublattice. -/
noncomputable def permutationSublatticeBasisMulEquivFunctions
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Multiplicative (permutationSublattice ρ L hL) ≃*
      (ι → Multiplicative ℤ) :=
  (AddEquiv.toMultiplicative
      (permutationSublatticeBasis ρ L hL).equivFun.toAddEquiv).trans
    (MulEquiv.funMultiplicative ι ℤ)

@[simp]
theorem permutationSublatticeModuleAut_basis
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (g : G) (i : ι) :
    permutationSublatticeModuleAut ρ L hL g
        (permutationSublatticeBasis ρ L hL i) =
      permutationSublatticeBasis ρ L hL (ρ g i) := by
  apply Subtype.ext
  exact permutationSublatticeBasis_permuted
    ρ L hL g i

/-- The distinguished basis coordinates identify the canonical
permutation sublattice equivariantly with integer-valued functions. -/
theorem permutationSublatticeBasisMulEquivFunctions_equivariant
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    letI _indexAction : MulAction G ι :=
      permutationMulAction ρ
    letI _sublatticeAction :
        DistribMulAction G
          (permutationSublattice ρ L hL) :=
      permutationSublatticeDistribMulAction ρ L hL
    letI _multiplicativeAction :
        MulDistribMulAction G
          (Multiplicative
            (permutationSublattice ρ L hL)) :=
      multiplicativeDistribMulAction
    letI _functionAction :
        MulDistribMulAction G
          (ι → Multiplicative ℤ) :=
      permutationFunctionMulDistribMulAction
    ∀ (g : G)
      (x : Multiplicative
        (permutationSublattice ρ L hL)),
      permutationSublatticeBasisMulEquivFunctions
          ρ L hL (g • x) =
        g • permutationSublatticeBasisMulEquivFunctions
          ρ L hL x := by
  let indexAction : MulAction G ι :=
    permutationMulAction ρ
  let sublatticeAction :
      DistribMulAction G
        (permutationSublattice ρ L hL) :=
    permutationSublatticeDistribMulAction ρ L hL
  let multiplicativeAction :
      MulDistribMulAction G
        (Multiplicative
          (permutationSublattice ρ L hL)) :=
    multiplicativeDistribMulAction
  let functionAction :
      MulDistribMulAction G
        (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  intro g x
  let b :=
    permutationSublatticeBasis ρ L hL
  ext i
  change
    b.equivFun (g • Multiplicative.toAdd x) i =
      b.equivFun (Multiplicative.toAdd x) (ρ g⁻¹ i)
  let α :=
    permutationSublatticeModuleAut ρ L hL
  have hinter :=
    basisEquivFun_symm_intCoordinatePermutation
      b ρ α
      (permutationSublatticeModuleAut_basis ρ L hL)
      g (b.equivFun (Multiplicative.toAdd x))
  have hcoord :=
    congrArg (fun y => b.equivFun y i) hinter
  have hα
      (y : permutationSublattice ρ L hL) :
      α g y = g • y :=
    rfl
  have hinv :
      ((ρ g)⁻¹ : Equiv.Perm ι) = (ρ g).symm :=
    rfl
  rw [map_inv, hinv]
  have hcoord' :
      (intCoordinatePermutation (ρ g)
        (b.equivFun (Multiplicative.toAdd x))) i =
        b.equivFun (g • Multiplicative.toAdd x) i := by
    simpa only [LinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply, hα] using hcoord
  change
    b.equivFun (Multiplicative.toAdd x) ((ρ g).symm i) =
      b.equivFun (g • Multiplicative.toAdd x) i at hcoord'
  exact hcoord'.symm

/-- Degree-zero Tate cohomology of the canonical complete permutation
sublattice is finite. -/
theorem permutationSublatticeHerbrandH0Finite
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _indexAction : MulAction G ι :=
      permutationMulAction ρ
    letI _sublatticeAction :
        DistribMulAction G
          (permutationSublattice ρ L hL) :=
      permutationSublatticeDistribMulAction ρ L hL
    letI _multiplicativeAction :
        MulDistribMulAction G
          (Multiplicative
            (permutationSublattice ρ L hL)) :=
      multiplicativeDistribMulAction
    Finite
      (HerbrandH0 G
        (Multiplicative
          (permutationSublattice ρ L hL))) := by
  let indexAction : MulAction G ι :=
    permutationMulAction ρ
  let sublatticeAction :
      DistribMulAction G
        (permutationSublattice ρ L hL) :=
    permutationSublatticeDistribMulAction ρ L hL
  let multiplicativeAction :
      MulDistribMulAction G
        (Multiplicative
          (permutationSublattice ρ L hL)) :=
    multiplicativeDistribMulAction
  let functionAction :
      MulDistribMulAction G
        (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let functionH0Finite :
      Finite
        (HerbrandH0 G
          (ι → Multiplicative ℤ)) :=
    permutationFunctionHerbrandH0Finite σ hgen
  let e :=
    permutationSublatticeBasisMulEquivFunctions
      ρ L hL
  let he :=
    permutationSublatticeBasisMulEquivFunctions_equivariant
      ρ L hL
  exact
    herbrandH0Finite_of_equivariantMulEquiv
      e.symm (mulEquiv_symm_commutes_smul e he)

/-- Degree-minus-one Tate cohomology of the canonical complete
permutation sublattice is finite. -/
theorem permutationSublatticeHerbrandHMinusOneFinite
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _indexAction : MulAction G ι :=
      permutationMulAction ρ
    letI _sublatticeAction :
        DistribMulAction G
          (permutationSublattice ρ L hL) :=
      permutationSublatticeDistribMulAction ρ L hL
    letI _multiplicativeAction :
        MulDistribMulAction G
          (Multiplicative
            (permutationSublattice ρ L hL)) :=
      multiplicativeDistribMulAction
    Finite
      (HerbrandHMinusOne G
        (Multiplicative
          (permutationSublattice ρ L hL)) σ) := by
  let indexAction : MulAction G ι :=
    permutationMulAction ρ
  let sublatticeAction :
      DistribMulAction G
        (permutationSublattice ρ L hL) :=
    permutationSublatticeDistribMulAction ρ L hL
  let multiplicativeAction :
      MulDistribMulAction G
        (Multiplicative
          (permutationSublattice ρ L hL)) :=
    multiplicativeDistribMulAction
  let functionAction :
      MulDistribMulAction G
        (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let functionHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (ι → Multiplicative ℤ) σ) :=
    permutationFunctionHerbrandHMinusOneFinite σ hgen
  let e :=
    permutationSublatticeBasisMulEquivFunctions
      ρ L hL
  let he :=
    permutationSublatticeBasisMulEquivFunctions_equivariant
      ρ L hL
  exact
    herbrandHMinusOneFinite_of_equivariantMulEquiv
      e.symm (mulEquiv_symm_commutes_smul e he) σ

/-- For the canonical complete permutation sublattice, its Herbrand quotient
is the product of the orders of the
stabilizers of the index orbits. -/
theorem
    permutationSublattice_herbrandQuotient_eq_stabilizerProduct
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _indexAction : MulAction G ι :=
      permutationMulAction ρ
    letI _sublatticeAction :
        DistribMulAction G
          (permutationSublattice ρ L hL) :=
      permutationSublatticeDistribMulAction ρ L hL
    letI _multiplicativeAction :
        MulDistribMulAction G
          (Multiplicative
            (permutationSublattice ρ L hL)) :=
      multiplicativeDistribMulAction
    letI _orbitFintype :
        Fintype (MulAction.orbitRel.Quotient G ι) :=
      Fintype.ofFinite _
    letI _stabilizerFintype :
        ∀ ω : MulAction.orbitRel.Quotient G ι,
          Fintype (permutationOrbitStabilizer ω) :=
      fun _ => Fintype.ofFinite _
    letI _sublatticeH0Finite :
        Finite
          (HerbrandH0 G
            (Multiplicative
              (permutationSublattice ρ L hL))) :=
      permutationSublatticeHerbrandH0Finite
        ρ L hL σ hgen
    letI _sublatticeHMinusOneFinite :
        Finite
          (HerbrandHMinusOne G
            (Multiplicative
              (permutationSublattice ρ L hL)) σ) :=
      permutationSublatticeHerbrandHMinusOneFinite
        ρ L hL σ hgen
    herbrandQuotient
        (G := G)
        (A := Multiplicative
          (permutationSublattice ρ L hL)) σ =
      ∏ ω : MulAction.orbitRel.Quotient G ι,
        (Fintype.card
          (permutationOrbitStabilizer ω) : ℚ) := by
  let indexAction : MulAction G ι :=
    permutationMulAction ρ
  let sublatticeAction :
      DistribMulAction G
        (permutationSublattice ρ L hL) :=
    permutationSublatticeDistribMulAction ρ L hL
  let multiplicativeAction :
      MulDistribMulAction G
        (Multiplicative
          (permutationSublattice ρ L hL)) :=
    multiplicativeDistribMulAction
  let functionAction :
      MulDistribMulAction G
        (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  let orbitFintype :
      Fintype (MulAction.orbitRel.Quotient G ι) :=
    Fintype.ofFinite _
  let stabilizerFintype :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  let sublatticeH0Finite :
      Finite
        (HerbrandH0 G
          (Multiplicative
            (permutationSublattice ρ L hL))) :=
    permutationSublatticeHerbrandH0Finite
      ρ L hL σ hgen
  let sublatticeHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (Multiplicative
            (permutationSublattice ρ L hL)) σ) :=
    permutationSublatticeHerbrandHMinusOneFinite
      ρ L hL σ hgen
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
    permutationSublatticeBasisMulEquivFunctions
      ρ L hL
  let he :=
    permutationSublatticeBasisMulEquivFunctions_equivariant
      ρ L hL
  calc
    herbrandQuotient
        (G := G)
        (A := Multiplicative
          (permutationSublattice ρ L hL)) σ =
        herbrandQuotient
          (G := G) (A := ι → Multiplicative ℤ) σ := by
      simpa only [e, he] using
        (herbrandQuotient_eq_of_equivariantMulEquiv
          e he σ)
    _ = ∏ ω : MulAction.orbitRel.Quotient G ι,
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ) :=
      permutationFunction_herbrandQuotient_eq_stabilizerProduct
        σ hgen

/-- For an arbitrary complete stable lattice, passing to the canonical
finite-index permutation sublattice computes
the ambient Herbrand quotient as the product of orbit-stabilizer
orders. -/
theorem
    completePermutationLattice_herbrandQuotient_eq_stabilizerProduct
    {G ι : Type}
    [Fintype G] [Group G] [Fintype ι]
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ) :
    letI _indexAction : MulAction G ι :=
      permutationMulAction ρ
    letI _ambientAction :
        DistribMulAction G L :=
      completePermutationLatticeDistribMulAction
        ρ L hL
    letI _ambientMultiplicativeAction :
        MulDistribMulAction G
          (Multiplicative L) :=
      multiplicativeDistribMulAction
    letI _orbitFintype :
        Fintype (MulAction.orbitRel.Quotient G ι) :=
      Fintype.ofFinite _
    letI _stabilizerFintype :
        ∀ ω : MulAction.orbitRel.Quotient G ι,
          Fintype (permutationOrbitStabilizer ω) :=
      fun _ => Fintype.ofFinite _
    ∃ h :
        HerbrandQuotientDefined
          G (Multiplicative L) σ,
      @herbrandQuotient
          G (Multiplicative L) _ _ _ _
          σ h.1 h.2 =
        ∏ ω : MulAction.orbitRel.Quotient G ι,
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ) := by
  classical
  let indexAction : MulAction G ι :=
    permutationMulAction ρ
  let ambientAction :
      DistribMulAction G L :=
    completePermutationLatticeDistribMulAction
      ρ L hL
  let ambientMultiplicativeAction :
      MulDistribMulAction G
        (Multiplicative L) :=
    multiplicativeDistribMulAction
  let orbitFintype :
      Fintype (MulAction.orbitRel.Quotient G ι) :=
    Fintype.ofFinite _
  let stabilizerFintype :
      ∀ ω : MulAction.orbitRel.Quotient G ι,
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  let B :=
    permutationSublatticeMultiplicativeSubgroup
      ρ L hL
  have hstable :
      ∀ (g : G) (x : Multiplicative L),
        x ∈ B → g • x ∈ B := by
    simpa only [B] using
      (permutationSublatticeMultiplicativeSubgroup_stable
        ρ L hL)
  let subgroupAction :
      MulDistribMulAction G B :=
    stableSubgroupMulDistribMulAction
      B hstable
  let quotientAction :
      MulDistribMulAction G
        (Multiplicative L ⧸ B) :=
    stableQuotientMulDistribMulAction
      B hstable
  let quotientFinite :
      Finite (Multiplicative L ⧸ B) := by
    simpa only [B] using
      (permutationSublatticeMultiplicativeSubgroup_finite_quotient
        ρ L hL)
  let sublatticeAction :
      DistribMulAction G
        (permutationSublattice ρ L hL) :=
    permutationSublatticeDistribMulAction ρ L hL
  let sublatticeMultiplicativeAction :
      MulDistribMulAction G
        (Multiplicative
          (permutationSublattice ρ L hL)) :=
    multiplicativeDistribMulAction
  let sublatticeH0Finite :
      Finite
        (HerbrandH0 G
          (Multiplicative
            (permutationSublattice ρ L hL))) :=
    permutationSublatticeHerbrandH0Finite
      ρ L hL σ hgen
  let sublatticeHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (Multiplicative
            (permutationSublattice ρ L hL)) σ) :=
    permutationSublatticeHerbrandHMinusOneFinite
      ρ L hL σ hgen
  let e :=
    permutationSublatticeSubgroupMulEquiv
      ρ L hL
  have he :
      ∀ (g : G) (x : B),
        e (g • x) = g • e x := by
    intro g x
    exact
      permutationSublatticeSubgroupMulEquiv_equivariant
        ρ L hL g x
  let subgroupH0Finite :
      Finite (HerbrandH0 G B) :=
    herbrandH0Finite_of_equivariantMulEquiv
      e.symm
      (mulEquiv_symm_commutes_smul e he)
  let subgroupHMinusOneFinite :
      Finite (HerbrandHMinusOne G B σ) :=
    herbrandHMinusOneFinite_of_equivariantMulEquiv
      e.symm
      (mulEquiv_symm_commutes_smul e he) σ
  let hB :
      HerbrandQuotientDefined G B σ :=
    ⟨subgroupH0Finite,
      subgroupHMinusOneFinite⟩
  let hA :
      HerbrandQuotientDefined
        G (Multiplicative L) σ :=
    finiteIndexStableSubgroup_ambientHerbrandQuotientDefined
      B hstable σ hgen hB
  refine ⟨hA, ?_⟩
  let ambientH0Finite :
      Finite
        (HerbrandH0 G
          (Multiplicative L)) :=
    hA.1
  let ambientHMinusOneFinite :
      Finite
        (HerbrandHMinusOne G
          (Multiplicative L) σ) :=
    hA.2
  calc
    @herbrandQuotient
          G (Multiplicative L) _ _ _ _
          σ hA.1 hA.2 =
        @herbrandQuotient
          G B _ _ _ _
          σ hB.1 hB.2 := by
      simpa only [hA] using
        (herbrandQuotient_eq_of_finiteIndex_stableSubgroup
          B hstable σ hgen hB)
    _ =
        herbrandQuotient
          (G := G)
          (A := Multiplicative
            (permutationSublattice ρ L hL)) σ := by
      simpa only [e, he] using
        (herbrandQuotient_eq_of_equivariantMulEquiv
          e he σ)
    _ = ∏ ω : MulAction.orbitRel.Quotient G ι,
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ) :=
      permutationSublattice_herbrandQuotient_eq_stabilizerProduct
        ρ L hL σ hgen

end StableSublattice

end CyclicCohomology
