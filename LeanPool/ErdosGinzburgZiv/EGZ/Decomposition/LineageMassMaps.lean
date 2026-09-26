/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NodeMassMapLevels
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Lineages

/-!
# Composed geometric and mass transport along low-level lineages

A transport bundles a subdivision with compatible stable mass maps. These
data compose without changing parent-node identifications. Iterating them
gives the geometric and measure comparison between any two stages, while
the parent agrees with the abstract lineage ancestor.
-/

@[expose] public section

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}

namespace SubdivisionMap

/-- The identity subdivision of a flag decomposition. -/
def refl (Φ : FlagDecomposition p d f) : SubdivisionMap Φ Φ where
  node := SupHom.id _
  fibre _ := AffineMap.id ℝ _
  polytope_mem _ := fun _ h ↦ h
  transition_comm _ _ := rfl
  proper _ h := h

@[simp]
theorem refl_comp {Φ Ψ : FlagDecomposition p d f} (M : SubdivisionMap Φ Ψ) :
    (refl Φ).comp M = M := rfl

@[simp]
theorem comp_refl {Φ Ψ : FlagDecomposition p d f} (M : SubdivisionMap Φ Ψ) :
    M.comp (refl Ψ) = M := rfl

theorem comp_assoc {Φ Ψ Ω Θ : FlagDecomposition p d f}
    (M : SubdivisionMap Φ Ψ) (N : SubdivisionMap Ψ Ω) (Q : SubdivisionMap Ω Θ) :
    (M.comp N).comp Q = M.comp (N.comp Q) := rfl

end SubdivisionMap

/-- Stepwise geometric and measure data for an iteration of minimal
decompositions. Stability and parent injectivity are required only below
the cutoff at that step. -/
structure LineageMassMaps (Φ : ℕ → FlagDecomposition p d f) where
  minimal : ∀ i, (Φ i).IsMinimal
  /-- The subdivision map for each successive pair of decompositions. -/
  step : ∀ i, SubdivisionMap (Φ i) (Φ (i + 1))
  /-- The level up to which node maps must be stable at each step. -/
  cutoff : ℕ → ℕ
  level_parent : ∀ i x, (Φ i).level ((step i).node x) ≤ (Φ (i + 1)).level x
  /-- Stable node maps below the cutoff of each successive subdivision. -/
  stable : ∀ i y, (Φ (i + 1)).level y ≤ cutoff i →
    StableNodeMap (Φ i) (Φ (i + 1)) ((step i).node y) y
  stable_real : ∀ i y h, (stable i y h).coord.real = (step i).fibre y
  injective_below : ∀ i L, L ≤ cutoff i →
    Set.InjOn (step i).node {y | (Φ (i + 1)).level y ≤ L}

namespace LineageMassMaps

variable {Φ : ℕ → FlagDecomposition p d f}

/-- All comparisons needed between two times at a fixed level cutoff. -/
structure Transport (Φ : ℕ → FlagDecomposition p d f) (L i j : ℕ) where
  /-- The subdivision map transporting nodes across the interval of stages. -/
  subdivision : SubdivisionMap (Φ i) (Φ j)
  level_parent : ∀ y, (Φ i).level (subdivision.node y) ≤ (Φ j).level y
  /-- Stable node maps for transported nodes of level at most `L`. -/
  stable : ∀ y : {y : (Φ j).flag.Node // (Φ j).level y ≤ L},
    StableNodeMap (Φ i) (Φ j) (subdivision.node y) y
  stable_real : ∀ y, (stable y).coord.real = subdivision.fibre y

namespace Transport

variable {L i j k l : ℕ}

/-- Identity transport at a single stage. -/
def refl (Φ : ℕ → FlagDecomposition p d f) (L i : ℕ) : Transport Φ L i i where
  subdivision := SubdivisionMap.refl (Φ i)
  level_parent _ := le_rfl
  stable y := StableNodeMap.refl (Φ i) y
  stable_real _ := rfl

/-- The parent of a low-level node is still below the cutoff. -/
def lowParent (M : Transport Φ L i j)
    (y : {y : (Φ j).flag.Node // (Φ j).level y ≤ L}) :
    {x : (Φ i).flag.Node // (Φ i).level x ≤ L} :=
  ⟨M.subdivision.node y, (M.level_parent y).trans y.property⟩

/-- Compose transports across two consecutive intervals of stages. -/
def comp (M : Transport Φ L i j) (N : Transport Φ L j k) : Transport Φ L i k where
  subdivision := M.subdivision.comp N.subdivision
  level_parent y := (M.level_parent (N.subdivision.node y)).trans (N.level_parent y)
  stable y := (M.stable (N.lowParent y)).comp (N.stable y)
  stable_real y := by
    change (M.stable (N.lowParent y)).coord.real.comp (N.stable y).coord.real = _
    rw [M.stable_real, N.stable_real]
    rfl

@[simp]
theorem refl_comp (M : Transport Φ L i j) : (refl Φ L i).comp M = M := rfl

@[simp]
theorem comp_refl (M : Transport Φ L i j) : M.comp (refl Φ L j) = M := rfl

theorem comp_assoc (M : Transport Φ L i j) (N : Transport Φ L j k)
    (Q : Transport Φ L k l) : (M.comp N).comp Q = M.comp (N.comp Q) := rfl

@[simp]
theorem comp_stable_coord (M : Transport Φ L i j) (N : Transport Φ L j k)
    (y : {y : (Φ k).flag.Node // (Φ k).level y ≤ L}) :
    ((M.comp N).stable y).coord = (M.stable (N.lowParent y)).coord.comp (N.stable y).coord := rfl

/-- A stable map whose target is named by an equal node. -/
def stableAt (M : Transport Φ L i j)
    (y : {y : (Φ j).flag.Node // (Φ j).level y ≤ L})
    (x : (Φ i).flag.Node) (h : M.subdivision.node y = x) :
    StableNodeMap (Φ i) (Φ j) x y := h ▸ M.stable y

theorem stableAt_coord_congr (M N : Transport Φ L i j) (hMN : M = N)
    (y : {y : (Φ j).flag.Node // (Φ j).level y ≤ L})
    (x : (Φ i).flag.Node) (hM : M.subdivision.node y = x)
    (hN : N.subdivision.node y = x) :
    (M.stableAt y x hM).coord = (N.stableAt y x hN).coord := by
  subst N
  rfl

theorem stableAt_comp_coord (M : Transport Φ L i j) (N : Transport Φ L j k)
    (z : {z : (Φ k).flag.Node // (Φ k).level z ≤ L})
    (y : {y : (Φ j).flag.Node // (Φ j).level y ≤ L}) (x : (Φ i).flag.Node)
    (hy : N.subdivision.node z = y.val) (hx : M.subdivision.node y = x)
    (hxz : (M.comp N).subdivision.node z = x) :
    ((M.comp N).stableAt z x hxz).coord =
      (M.stableAt y x hx).coord.comp (N.stableAt z y hy).coord := by
  have hey : y = N.lowParent z := Subtype.ext hy.symm
  subst y
  subst x
  rfl

theorem stableAt_real_preimage (M : Transport Φ L i j)
    (y : {y : (Φ j).flag.Node // (Φ j).level y ≤ L})
    (x : (Φ i).flag.Node) (h : M.subdivision.node y = x)
    (S : Set (RealCoord ((Φ i).flag.rank x))) :
    (M.stableAt y x h).coord.real ⁻¹' S =
      M.subdivision.fibre y ⁻¹' (h.symm ▸ S) := by
  subst x
  simp only [stableAt, M.stable_real]

end Transport

variable (D : LineageMassMaps Φ)

/-- Forget the geometry and masses to obtain the abstract lineage system. -/
noncomputable abbrev system : Lineages.System where
  Node i := (Φ i).flag.Node
  finiteNode i := (Φ i).flag.nodeFintype
  level i := (Φ i).level
  parent i := (D.step i).node
  level_parent := D.level_parent

variable {L : ℕ} (hL : ∀ i, L ≤ D.cutoff i)

include hL in
theorem system_injectiveBelow : D.system.InjectiveBelow L :=
  fun i ↦ D.injective_below i L (hL i)

/-- A one-step comparison at a cutoff below the current selected level. -/
def stepTransport (i : ℕ) : Transport Φ L i (i + 1) where
  subdivision := D.step i
  level_parent := D.level_parent i
  stable y := D.stable i y (y.property.trans (hL i))
  stable_real y := D.stable_real i y _

/-- Compose the subdivisions and stable mass maps from any time `i` to
any later time `j`. -/
def transport {i j : ℕ} (h : i ≤ j) : Transport Φ L i j :=
  Nat.leRecOn h (fun {k} M ↦ M.comp (D.stepTransport hL k)) (Transport.refl Φ L i)

@[simp]
theorem transport_self (i : ℕ) : D.transport hL (le_refl i) = Transport.refl Φ L i :=
  Nat.leRecOn_self _

theorem transport_succ {i j : ℕ} (h : i ≤ j) :
    D.transport hL (h.trans (Nat.le_succ j)) =
      (D.transport hL h).comp (D.stepTransport hL j) := Nat.leRecOn_succ h _

/-- Pairwise comparisons compose coherently, including their integer
coordinates, their real fibres, and all stable mass estimates. -/
theorem transport_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    D.transport hL (hij.trans hjk) = (D.transport hL hij).comp (D.transport hL hjk) := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [D.transport_succ hL (hij.trans hk), D.transport_succ hL hk, ih,
      Transport.comp_assoc]

/-- The composed geometric parent is exactly the abstract low-level
ancestor, so geometric and counting arguments use the same lineage. -/
theorem transport_node_eq_ancestor {i j : ℕ} (h : i ≤ j) (y : D.system.LowNode L j) :
    (D.transport hL h).subdivision.node y =
      (D.system.ancestor (D.system_injectiveBelow hL) h y).val := by
  revert y
  induction j, h using Nat.le_induction with
  | base => intro y; simp [Transport.refl, SubdivisionMap.refl]
  | succ j hj ih =>
    intro y
    rw [D.transport_succ hL hj, D.system.ancestor_succ (D.system_injectiveBelow hL) hj]
    exact ih (D.system.parentEmbedding (D.system_injectiveBelow hL) j y)

/-- The stable map to the actual abstract ancestor. -/
def ancestorMap {i j : ℕ} (h : i ≤ j) (y : D.system.LowNode L j) :
    StableNodeMap (Φ i) (Φ j)
      (D.system.ancestor (D.system_injectiveBelow hL) h y).val y := by
  rw [← D.transport_node_eq_ancestor hL h y]
  exact (D.transport hL h).stable y

/-- Selected nodes with the same initial lineage label are related by the
composed parent map at any two ordered times. -/
theorem transport_node_eq_of_ancestry_eq {i j : ℕ} (h : i ≤ j)
    (x : D.system.LowNode L i) (y : D.system.LowNode L j)
    (heq : D.system.ancestry (D.system_injectiveBelow hL) i x =
      D.system.ancestry (D.system_injectiveBelow hL) j y) :
    (D.transport hL h).subdivision.node y = x.val := by
  rw [D.transport_node_eq_ancestor hL h y]
  apply congrArg Subtype.val
  apply (D.system.ancestry (D.system_injectiveBelow hL) i).injective
  exact (D.system.ancestry_ancestor (D.system_injectiveBelow hL) h y).trans heq.symm

/-- The mass map between two selected nodes on the same persistent lineage. -/
def mapOfSameAncestry {i j : ℕ} (h : i ≤ j)
    (x : D.system.LowNode L i) (y : D.system.LowNode L j)
    (heq : D.system.ancestry (D.system_injectiveBelow hL) i x =
      D.system.ancestry (D.system_injectiveBelow hL) j y) :
    StableNodeMap (Φ i) (Φ j) x.val y.val :=
  (D.transport hL h).stableAt y x.val
    (D.transport_node_eq_of_ancestry_eq hL h x y heq)

/-- Coordinate transport is coherent even when each intermediate node is
specified by its persistent ancestry label. -/
theorem mapOfSameAncestry_comp_coord {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (x : D.system.LowNode L i) (y : D.system.LowNode L j) (z : D.system.LowNode L k)
    (hxy : D.system.ancestry (D.system_injectiveBelow hL) i x =
      D.system.ancestry (D.system_injectiveBelow hL) j y)
    (hyz : D.system.ancestry (D.system_injectiveBelow hL) j y =
      D.system.ancestry (D.system_injectiveBelow hL) k z)
    (hxz : D.system.ancestry (D.system_injectiveBelow hL) i x =
      D.system.ancestry (D.system_injectiveBelow hL) k z) :
    (D.mapOfSameAncestry hL (hij.trans hjk) x z hxz).coord =
      (D.mapOfSameAncestry hL hij x y hxy).coord.comp
        (D.mapOfSameAncestry hL hjk y z hyz).coord := by
  unfold mapOfSameAncestry
  have hxz' : ((D.transport hL hij).comp (D.transport hL hjk)).subdivision.node z = x := by
    rw [← D.transport_trans hL hij hjk]
    exact D.transport_node_eq_of_ancestry_eq hL _ x z hxz
  exact (Transport.stableAt_coord_congr _ _ (D.transport_trans hL hij hjk) z x _ hxz').trans
    (Transport.stableAt_comp_coord (D.transport hL hij) (D.transport hL hjk) z y x.val
      (D.transport_node_eq_of_ancestry_eq hL hjk y z hyz)
      (D.transport_node_eq_of_ancestry_eq hL hij x y hxy) hxz')

theorem mapOfSameAncestry_real_preimage {i j : ℕ} (h : i ≤ j)
    (x : D.system.LowNode L i) (y : D.system.LowNode L j)
    (heq : D.system.ancestry (D.system_injectiveBelow hL) i x =
      D.system.ancestry (D.system_injectiveBelow hL) j y)
    (S : Set (RealCoord ((Φ i).flag.rank x))) :
    (D.mapOfSameAncestry hL h x y heq).coord.real ⁻¹' S =
      (D.transport hL h).subdivision.fibre y ⁻¹'
        ((D.transport_node_eq_of_ancestry_eq hL h x y heq).symm ▸ S) :=
  (D.transport hL h).stableAt_real_preimage y x.val
    (D.transport_node_eq_of_ancestry_eq hL h x y heq) S

/-- Equal levels along a lineage make the composed real coordinate map
an affine isomorphism. -/
theorem transport_real_bijective_of_level_eq {i j : ℕ} (h : i ≤ j)
    (y : D.system.LowNode L j)
    (heq : (Φ i).level ((D.transport hL h).subdivision.node y) = (Φ j).level y) :
    Function.Bijective ((D.transport hL h).subdivision.fibre y) := by
  rw [← (D.transport hL h).stable_real y]
  exact ((D.transport hL h).stable y).toNodeMassMap.real_bijective_of_level_eq (D.minimal j) heq

/-- A realized face stays realized throughout any number of subdivision
steps whenever its final pullback is nonempty. -/
theorem transport_isRealizedFace {i j : ℕ} (h : i ≤ j) (y : (Φ j).flag.Node)
    (Γ : ((Φ i).flag.polytope ((D.transport hL h).subdivision.node y)).Face)
    (hne : (((Φ j).flag.polytope y).carrier ∩
      (D.transport hL h).subdivision.fibre y ⁻¹' Γ.carrier).Nonempty)
    (hΓ : (Φ i).IsRealizedFace ((D.transport hL h).subdivision.node y) Γ) :
    (Φ j).IsRealizedFace y ((D.transport hL h).subdivision.face y Γ hne) :=
  (D.transport hL h).subdivision.isRealizedFace y Γ hne hΓ

end LineageMassMaps
end EGZ.FlagDecomposition
