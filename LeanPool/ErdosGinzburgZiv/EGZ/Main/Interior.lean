/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Convex.LeastFaceInterior
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceMassChain

/-!
# Why the selected flag centerpoint is interior

On a finite support, a sufficiently large multiple of a face's exposing
functional suppresses all points outside that face.  This gives the
halfspaces needed to show that the centerpoint's least face is large.
-/

open scoped BigOperators

namespace EGZ.RationalPolytope.Face

/-- A halfspace through a point of `F \ G` whose intersection with a
prescribed finite support lies in `F \ G`. -/
theorem exists_halfspace_subset_sdiff {r : ℕ} {P : RationalPolytope r}
    (F G : P.Face) {c : RealCoord r} (hcF : c ∈ F.carrier)
    (hcG : c ∉ G.carrier) (S : Finset (IntCoord r)) (hS : S.Nonempty)
    (hSP : ∀ q ∈ S, q.real ∈ P.carrier) :
    ∃ ξ : RealCoord r →ᵃ[ℝ] ℝ, ∀ q ∈ S,
      ξ c ≤ ξ q.real → q.real ∈ F.carrier ∧ q.real ∉ G.carrier := by
  classical
  obtain ⟨f, a, hf, hF⟩ := F.is_exposed
  obtain ⟨g, b, hg, hG⟩ := G.is_exposed
  have hfc : f c = a := (hF ▸ hcF).2
  have hgc : g c < b := by
    have hle := hg c (F.subset_polytope hcF)
    have hne : g c ≠ b := by
      intro heq
      exact hcG (hG ▸ ⟨F.subset_polytope hcF, heq⟩)
    exact lt_of_le_of_ne hle hne
  let ratio : IntCoord r → ℝ := fun q ↦ (g c - g q.real) / (a - f q.real)
  let M : ℝ := max (S.sup' hS ratio) 0 + 1
  have hratio (q : IntCoord r) (hq : q ∈ S) : ratio q < M := by
    exact (Finset.le_sup' ratio hq).trans_lt (by
      dsimp [M]
      linarith [le_max_left (S.sup' hS ratio) 0])
  refine ⟨M • f - g, ?_⟩
  intro q hq hupper
  change M * f c - g c ≤ M * f q.real - g q.real at hupper
  rw [hfc] at hupper
  have hqF : q.real ∈ F.carrier := by
    by_contra hnot
    have hle := hf q.real (hSP q hq)
    have hne : f q.real ≠ a := by
      intro heq
      exact hnot (hF ▸ ⟨hSP q hq, heq⟩)
    have hpos : 0 < a - f q.real := sub_pos.mpr (lt_of_le_of_ne hle hne)
    have hstrict := (div_lt_iff₀ hpos).mp (hratio q hq)
    linarith
  refine ⟨hqF, ?_⟩
  intro hqG
  have hfq : f q.real = a := (hF ▸ hqF).2
  have hgq : g q.real = b := (hG ▸ hqG).2
  rw [hfq, hgq] at hupper
  linarith

end EGZ.RationalPolytope.Face

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

/-- A proper point based at `x` cannot lie on a realized proper face at
`x`: its own base occurs in the supremum defining the face index. -/
theorem realized_face_eq_top_of_point (Φ : FlagDecomposition p d f)
    (q : Φ.flag.Point) (hq : q ∈ Φ.omega)
    (F : (Φ.flag.polytope q.base).Face) (hqF : q.val ∈ F.carrier)
    (hreal : Φ.IsRealizedFace q.base F) :
    F = ⊤ := by
  classical
  have hmem : q.base ∈ Φ.faceBases q.base F := by
    simp only [faceBases, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨q, ⟨hq, ?_⟩, rfl⟩
    exact ⟨le_rfl, by simpa using hqF⟩
  have hle : q.base ≤ Φ.faceIndex q.base F := Finset.le_sup' id hmem
  have heq : Φ.faceIndex q.base F = q.base := le_antisymm (Φ.faceIndex_le _ _) hle
  apply RationalPolytope.Face.ext
  apply Set.Subset.antisymm F.subset_polytope
  intro z hz
  have hcollapse (y : Φ.flag.Node) (hy : y ≤ q.base) (he : y = q.base)
      (hr : ∀ z ∈ (Φ.flag.polytope y).carrier,
        (Φ.flag.transition hy).real z ∈ F.carrier) :
      ∀ z ∈ (Φ.flag.polytope q.base).carrier, z ∈ F.carrier := by
    subst y
    simpa only [Φ.flag.transition_refl, IntegralAffineMap.id_real,
      AffineMap.id_apply] using hr
  exact hcollapse _ _ heq hreal z hz

/-- The lifted mass of any subset is at most total retained mass. -/
theorem liftedMassOn_le_retainedMass (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.flag.Node) (S : Set (RealCoord (Φ.flag.rank x))) :
    Φ.liftedMassOn x S ≤ Φ.retainedMass := by
  classical
  calc
    Φ.liftedMassOn x S ≤ ∑ q ∈ Φ.liftedSupport x, Φ.hat x q := by
      apply Finset.sum_le_sum
      intro q _
      split_ifs <;> omega
    _ = natMass (Φ.cumulativeWeight x) := Φ.sum_liftedSupport hp x
    _ ≤ Φ.retainedMass := Φ.cumulativeMass_le_retainedMass x

/-- Completeness forces a proper centerpoint to lie in the relative
interior of its base polytope. This includes rank zero. -/
theorem centerpoint_mem_interior (Φ : FlagDecomposition p d f) (hp : Odd p)
    (q : Φ.flag.Point) (hq : q ∈ Φ.omega) {ε : ℝ} (hε : 0 ≤ ε)
    (hcentral : ∀ ξ : RealCoord (Φ.flag.rank q.base) →ᵃ[ℝ] ℝ,
      ε * (Φ.retainedMass : ℝ) ≤
        (Φ.liftedMassOn q.base {z | ξ q.val ≤ ξ z} : ℝ))
    (hfaces : ∀ F : (Φ.flag.polytope q.base).Face,
      Φ.IsLargeFace ε q.base F → Φ.IsRealizedFace q.base F) :
    q.val ∈ intrinsicInterior ℝ (Φ.flag.polytope q.base).carrier := by
  classical
  obtain ⟨F, hF⟩ := RationalPolytope.Face.exists_isLeastFaceAt
    (Φ.flag.polytope q.base) q.val_mem
  have hSP (z : IntCoord (Φ.flag.rank q.base)) (hz : z ∈ Φ.liftedSupport q.base) :
      z.real ∈ (Φ.flag.polytope q.base).carrier := by
    rw [Φ.polytope_eq_liftedSupport]
    exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩
  have hlarge : Φ.IsLargeFace ε q.base F := by
    constructor
    · obtain ⟨ξ, a, hξ, hcarrier⟩ := F.is_exposed
      have hξq : ξ q.val = a := (hcarrier ▸ hF.1).2
      have heq : Φ.liftedMassOn q.base {z | ξ q.val ≤ ξ z} =
          Φ.liftedMassOn q.base F.carrier := by
        apply Finset.sum_congr rfl
        intro z hz
        have hiff : ξ q.val ≤ ξ z.real ↔ z.real ∈ F.carrier := by
          rw [hξq, hcarrier]
          exact ⟨fun h ↦ ⟨hSP z hz, le_antisymm (hξ _ (hSP z hz)) h⟩,
            fun h ↦ h.2.ge⟩
        simp only [Set.mem_ofPred_eq, hiff]
      simpa only [heq] using hcentral ξ
    · intro G hGF
      have hqG : q.val ∉ G.carrier := by
        intro hqG
        exact hGF.2 (hF.2 G hqG)
      obtain ⟨ξ, hξ⟩ := F.exists_halfspace_subset_sdiff G hF.1 hqG
        (Φ.liftedSupport q.base) (Φ.liftedSupport_nonempty q.base) hSP
      have hmass : Φ.liftedMassOn q.base {z | ξ q.val ≤ ξ z} +
          Φ.liftedMassOn q.base G.carrier ≤ Φ.liftedMassOn q.base F.carrier := by
        unfold liftedMassOn
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro z hz
        by_cases hupper : ξ q.val ≤ ξ z.real
        · obtain ⟨hzF, hzG⟩ := hξ z hz hupper
          simp [hupper, hzF, hzG]
        · by_cases hzG : z.real ∈ G.carrier
          · simp [hupper, hzG, hGF.1 hzG]
          · simp [hupper, hzG]
      have hmassR : (Φ.liftedMassOn q.base {z | ξ q.val ≤ ξ z} : ℝ) +
          (Φ.liftedMassOn q.base G.carrier : ℝ) ≤ Φ.liftedMassOn q.base F.carrier := by
        exact_mod_cast hmass
      have htotal : (Φ.liftedMassOn q.base F.carrier : ℝ) ≤ Φ.retainedMass := by
        exact_mod_cast Φ.liftedMassOn_le_retainedMass hp q.base F.carrier
      have hmul := mul_le_mul_of_nonneg_left htotal hε
      linarith [hcentral ξ]
  have htop := Φ.realized_face_eq_top_of_point q hq F hF.1 (hfaces F hlarge)
  have hinterior := hF.mem_relInterior
  rw [htop] at hinterior
  exact hinterior

end EGZ.FlagDecomposition
