/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.TateComparison

/-! # Norm Kernel Vanishing -/
namespace CyclicCohomology

/-!
# The cyclic-cohomology vanishing condition

This file formalizes the cyclic norm-kernel vanishing condition as a property, not as a new Lean
  axiom, and
the finite-cyclic cohomology calculation using the actual finite-cyclic group-cohomology
  computation.

The construction writes multiplicative modules with a right action.  Here an abelian
group is represented additively as a `ℤ`-linear left representation; passing
between the two conventions replaces a generator by its inverse and does not
change either quotient below.
-/

noncomputable section

open CategoryTheory

universe u

/-- A specified generator supplies the `IsCyclic` instance used throughout
the cyclic cohomology constructions. -/
theorem isCyclic_of_generator {G : Type} [Group G] (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) : IsCyclic G := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨g, ?_⟩
  ext x
  constructor
  · intro _
    exact Subgroup.mem_top x
  · intro _
    exact hg x

/-- If the abstract field `L` extends `K`, this is exactly `G_L` regarded as
a subgroup of `G_K`.  The standard `Subgroup.subgroupOf` construction is the
canonical representation; the containment proof only changes the subtype
membership proof and therefore cannot create a second subgroup representation. -/
abbrev extensionSubgroup {G : Type u} [Group G] [TopologicalSpace G]
    (K L : ClosedSubgroup G) (_hLK : L.toSubgroup ≤ K.toSubgroup) :
    Subgroup K.toSubgroup :=
  L.toSubgroup.subgroupOf K.toSubgroup

/-- The actual coefficient module `A_L` for an abstract Galois extension
`L | K`: restrict the global representation to `G_K`, take `G_L`-fixed
vectors, and descend the action to `G_K / G_L`.

The subgroup occurring in the quotient is `G_L` viewed inside `G_K`. -/
noncomputable def extensionFixedRepresentation {G : Type} [Group G]
    [TopologicalSpace G] (A : Rep.{0} ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    Rep ℤ (K.toSubgroup ⧸ extensionSubgroup K L hLK) := by
  exact Rep.quotientToInvariants
    (Rep.res K.toSubgroup.subtype A)
    (extensionSubgroup K L hLK)

/-- Continuity of the action on the coefficient module when its carrier has
the discrete topology, exactly as in this construction's definition of a continuous
`G`-module. -/
def IsContinuousDiscreteRepresentation {G : Type} [Group G] [TopologicalSpace G]
    (A : Rep.{0} ℤ G) : Prop :=
  -- Mathlib orders topologies by reverse inclusion, so `⊥` is discrete.
  letI : TopologicalSpace A.V := ⊥
  Continuous fun p : G × A.V => A.ρ p.1 p.2

/-- **the cyclic norm-kernel vanishing condition.**  The condition on a continuous `G`-module
used by the
construction: `H⁻¹(G(L | K), A_L)` is trivial for every finite cyclic abstract
extension `L | K`.

Profinite-ness of `G` and continuity of `A` are ambient hypotheses in the
construction, not parts of the cyclic norm-kernel vanishing condition itself.  This predicate
  therefore records only
the numbered vanishing condition.  `hLK` expresses `G_L ≤ G_K`, `hnormal`
that the extension is Galois, `hfinite` that it is finite, and `g, hg` that
its Galois group is cyclic. -/
def SatisfiesCyclicNormKernelVanishing {G : Type} [Group G] [TopologicalSpace G]
    (A : Rep.{0} ℤ G) : Prop :=
  ∀ (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (_hg : ∀ x, x ∈ Subgroup.zpowers g),
      letI := hnormal
      letI := hfinite
      letI := Fintype.ofFinite
        (K.toSubgroup ⧸ extensionSubgroup K L hLK)
      Limits.IsZero
        (tateCohomology (extensionFixedRepresentation A K L hLK hnormal) (-1))

/-- **the finite-cyclic cohomology calculation.**  If `G` is finite cyclic, then
`H¹(G,A) ≅ H⁻¹(G,A)`.

The right-hand side is the actual homology object
`ker(N_G) / im(ρ(g) - 1)`, not a compatibility placeholder. -/
noncomputable def finiteCyclicH1IsoTateHMinusOne {G : Type} [Group G] [Fintype G]
    (A : Rep.{0} ℤ G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    groupCohomology.H1 A ≅ tateCohomology A (-1) := by
  letI : IsCyclic G := isCyclic_of_generator g hg
  letI : CommGroup G := IsCyclic.commGroup (α := G)
  let e :
      groupCohomology.H1 A ≅
        (Rep.FiniteCyclicGroup.subCompNormHom A g).homology := by
    simpa using
      (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 (by simp))
  exact e ≪≫ (TateCohomology.isoFiniteCyclicNegOne A g hg).symm

/-- Elementwise content of the vanishing condition in the cyclic norm-kernel vanishing
condition: every
norm-zero element is in the image of `ρ(g) - 1`.  This is the source used in
the cyclic step of abstract Kummer theory; the conclusion is extracted from
the actual homology object rather than assumed separately. -/
theorem normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
    {G : Type} [Group G] [Fintype G]
    (A : Rep.{0} ℤ G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hzero : Limits.IsZero (tateCohomology A (-1))) :
    ∀ x : A.V, A.norm.hom x = 0 →
      ∃ y : A.V, A.ρ g y - y = x := by
  let : IsCyclic G := isCyclic_of_generator g hg
  let : CommGroup G := IsCyclic.commGroup (α := G)
  have hH1 : Limits.IsZero (groupCohomology.H1 A) :=
    Limits.IsZero.of_iso hzero (finiteCyclicH1IsoTateHMinusOne A g hg)
  let : Subsingleton (groupCohomology.H1 A) :=
    ModuleCat.subsingleton_of_isZero hH1
  intro x hx
  let : Module ℤ A.V := A.hV2
  let x' : LinearMap.ker A.norm.hom.toLinearMap := ⟨x, hx⟩
  have hclass :
      Rep.FiniteCyclicGroup.groupCohomologyπOdd A g hg 1 (by simp) x' = 0 :=
    Subsingleton.elim _ _
  rcases (Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff
    A g hg 1 (by simp) x').1 hclass with ⟨y, hy⟩
  exact ⟨y, by simpa [Rep.sub_hom] using hy⟩

end
end CyclicCohomology
