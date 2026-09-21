/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.ReducedToUnreducedSphereTopHomology
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SingularHomologyHomotopyInvariance
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible

/-!
# Ball--boundary long-exact-sequence route for sphere homology

Develops the contractibility and positive-degree homology vanishing of the disk and records the
relative-homology input needed by the classical pair `(Dⁿ⁺¹, Sⁿ)` argument. This is an alternate
route; the unconditional sphere top-homology theorem used by the public API is obtained through
the Mayer--Vietoris suspension construction.
-/

open CategoryTheory AlgebraicTopology Limits

noncomputable section

namespace SphereOddDegree

/-! ## Homology isomorphism from a homotopy equivalence of spaces -/

/-- **Homology iso from a homotopy equivalence.** A homotopy equivalence
`e : X ≃ₕ Y` of topological spaces induces an isomorphism on the `k`-th integral
singular homology, by the library's unconditional homotopy invariance. The two
maps are the homologies of `e.toFun` and `e.invFun`; the round-trip identities
hold because `e.invFun ∘ e.toFun` (resp. `e.toFun ∘ e.invFun`) is homotopic to the
identity. -/
noncomputable def singularHomologyℤ_isoOfHomotopyEquivSpace (k : ℕ)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    (singularHomologyℤ k).obj (TopCat.of X) ≅ (singularHomologyℤ k).obj (TopCat.of Y) where
  hom := (singularHomologyℤ k).map (TopCat.ofHom e.toFun)
  inv := (singularHomologyℤ k).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← singularHomologyℤ_map_comp]
    have key := map_singularHomologyℤ_eq_of_homotopic_continuousMap
      (X := TopCat.of X) (Y := TopCat.of X)
      (f := e.invFun.comp e.toFun) (g := ContinuousMap.id X) e.left_inv k
    have h : TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun
        = TopCat.ofHom (e.invFun.comp e.toFun) := rfl
    rw [h, key]
    simp
  inv_hom_id := by
    rw [← singularHomologyℤ_map_comp]
    have key := map_singularHomologyℤ_eq_of_homotopic_continuousMap
      (X := TopCat.of Y) (Y := TopCat.of Y)
      (f := e.toFun.comp e.invFun) (g := ContinuousMap.id Y) e.right_inv k
    have h : TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun
        = TopCat.ofHom (e.toFun.comp e.invFun) := rfl
    rw [h, key]
    simp

/-! ## Contractible spaces have vanishing positive homology -/

/-- **Vanishing of positive homology for contractible spaces.** If `X` is
contractible and `k ≥ 1`, then `Hₖ(X; ℤ) = 0`. Indeed `X` is homotopy equivalent
to a point (`ContractibleSpace.hequiv_unit`), and the higher homology of a point
vanishes (it is totally disconnected). -/
theorem isZero_singularHomologyℤ_of_contractibleSpace (k : ℕ) (hk : 1 ≤ k)
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    IsZero ((singularHomologyℤ k).obj (TopCat.of X)) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  apply IsZero.of_iso _ (singularHomologyℤ_isoOfHomotopyEquivSpace k e)
  exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℤ) k (ModuleCat.of ℤ ℤ) (TopCat.of Unit) (by omega)

/-! ## The disk `Dⁿ⁺¹` and its vanishing homology -/

/-- A concrete model of the closed disk `Dⁿ⁺¹` as the closed unit ball in
`EuclideanSpace ℝ (Fin (n+1))`. Its topological boundary is the library's
`Sphere n`. -/
abbrev Disk (n : ℕ) : Type :=
  ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) (1 : ℝ))

/-- The disk `Dⁿ⁺¹` is contractible: it is a nonempty convex set. -/
instance instContractibleSpaceDisk (n : ℕ) : ContractibleSpace (Disk n) :=
  (convex_closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1).contractibleSpace
    ⟨0, by simp⟩

/-- **Homology of the disk.** For `k ≥ 1`, `Hₖ(Dⁿ⁺¹; ℤ) = 0`, since the disk is
contractible. -/
theorem isZero_singularHomologyℤ_disk (k n : ℕ) (hk : 1 ≤ k) :
    IsZero ((singularHomologyℤ k).obj (TopCat.of (Disk n))) :=
  isZero_singularHomologyℤ_of_contractibleSpace k hk (Disk n)

end SphereOddDegree
