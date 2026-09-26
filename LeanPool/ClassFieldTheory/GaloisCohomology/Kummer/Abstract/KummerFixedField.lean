/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.IntegralRepUniverse
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.NormKernelVanishing

/-! # Kummer Fixed Field -/

@[expose] public section
namespace KummerTheory

open CyclicCohomology

/-!
# finite abelian Kummer theory: the abstract field `K(S)`

in this construction, for a subset `S` of the coefficient module, `K(S)` is the
abstract field whose subgroup consists of the elements of `G_K` fixing every
member of `S`.  This file constructs that subgroup and proves that it is
closed.  Closedness follows directly from continuity of each orbit map and
the discrete topology on the coefficient module.
-/

noncomputable
section

/-- The subgroup of `G_K` fixing every element of `S`, viewed as a subgroup
of the ambient abstract Galois group `G`. -/
def setFixingSubgroup
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (S : Set A.V) : Subgroup G := by
  letI : Module ℤ A.V := A.hV2
  exact
    { carrier := {σ | σ ∈ K ∧ ∀ a, a ∈ S → A.ρ σ a = a}
      one_mem' := by
        refine ⟨K.one_mem, ?_⟩
        intro a _ha
        exact congrArg (fun f : Module.End ℤ A.V => f a) (map_one A.ρ)
      mul_mem' := by
        intro σ τ hσ hτ
        refine ⟨K.mul_mem hσ.1 hτ.1, ?_⟩
        intro a ha
        rw [map_mul]
        change A.ρ σ (A.ρ τ a) = a
        rw [hτ.2 a ha, hσ.2 a ha]
      inv_mem' := by
        intro σ hσ
        refine ⟨K.inv_mem hσ.1, ?_⟩
        intro a ha
        calc
          A.ρ σ⁻¹ a = A.ρ σ⁻¹ (A.ρ σ a) :=
            congrArg (A.ρ σ⁻¹) (hσ.2 a ha).symm
          _ = a := Representation.inv_self_apply A.ρ σ a }

/-- For a continuous discrete representation, the stabilizer of one
coefficient element is closed. -/
theorem isClosed_setOf_representation_fixed
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (hcontinuous : IsContinuousDiscreteRepresentation A)
    (a : A.V) : IsClosed {σ : G | A.ρ σ a = a} := by
  let : TopologicalSpace A.V := ⊥
  let : DiscreteTopology A.V := discreteTopology_bot A.V
  have horbit : Continuous (fun σ : G => A.ρ σ a) :=
    hcontinuous.comp (continuous_id.prodMk continuous_const)
  have hsingleton : IsClosed ({a} : Set A.V) := isClosed_discrete {a}
  change IsClosed ((fun σ : G => A.ρ σ a) ⁻¹' ({a} : Set A.V))
  exact hsingleton.preimage horbit

/-- The subgroup defining `K(S)` is closed. -/
theorem setFixingSubgroup_isClosed
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (hcontinuous : IsContinuousDiscreteRepresentation A)
    (K : ClosedSubgroup G) (S : Set A.V) :
    IsClosed (setFixingSubgroup A K S : Set G) := by
  change IsClosed ((K : Set G) ∩ {σ : G | ∀ a, a ∈ S → A.ρ σ a = a})
  apply K.isClosed'.inter
  have hset : {σ : G | ∀ a, a ∈ S → A.ρ σ a = a} =
      ⋂ a : S, {σ : G | A.ρ σ a.1 = a.1} := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Subtype.forall]
  rw [hset]
  exact isClosed_iInter fun a =>
    isClosed_setOf_representation_fixed A hcontinuous a.1

/-- The closed subgroup representing the abstract field `K(S)`.
Its underlying subgroup is exactly the elements of `G_K` which fix `S`
pointwise. -/
def closedSetFixingSubgroup
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (hcontinuous : IsContinuousDiscreteRepresentation A)
    (K : ClosedSubgroup G) (S : Set A.V) : ClosedSubgroup G :=
  ⟨setFixingSubgroup A K S, setFixingSubgroup_isClosed A hcontinuous K S⟩

/-- An automorphism lies in the fixing subgroup exactly when it fixes every element
of the closed set. -/
@[simp]
theorem mem_closedSetFixingSubgroup_iff
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (hcontinuous : IsContinuousDiscreteRepresentation A)
    (K : ClosedSubgroup G) (S : Set A.V) (σ : G) :
    σ ∈ closedSetFixingSubgroup A hcontinuous K S ↔
      σ ∈ K ∧ ∀ a, a ∈ S → A.ρ σ a = a :=
  Iff.rfl

end
end KummerTheory
