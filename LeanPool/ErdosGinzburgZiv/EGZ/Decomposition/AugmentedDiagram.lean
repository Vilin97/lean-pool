/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedCoordinates
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportDiagram
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceSelection
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SlabPruning

/-!
# Support diagrams with additional slab coordinates

At each node append an initial segment of a common sequence of affine
functionals to the old coordinate map. An antitone number of additional
coordinates ensures that transitions retain exactly the available prefix.
Centered lifts of cumulative atoms give a finite support diagram, even when
the augmented finite-field maps are not surjective.
-/

open Classical

namespace EGZ.FlagDecomposition.Augmented

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (e : Φ.flag.Node → ℕ)
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p)

/-- The integer lift of one ambient atom with its extra slab coordinates. -/
def lift (x : Φ.flag.Node) (v : FpCoord p d) : IntCoord (Φ.flag.rank x + e x) :=
  Fin.append (FpCoord.centeredLift (Φ.representation.map x v)) (slabCoordinates (e x) ξ v)

@[simp]
theorem lift_first (x : Φ.flag.Node) (v : FpCoord p d) :
    Coord.first (Φ.flag.rank x) (e x) (lift Φ e ξ x v) =
      FpCoord.centeredLift (Φ.representation.map x v) := by
  ext i
  simp [lift]

@[simp]
theorem lift_last (x : Φ.flag.Node) (v : FpCoord p d) :
    Coord.last (Φ.flag.rank x) (e x) (lift Φ e ξ x v) = slabCoordinates (e x) ξ v := by
  ext i
  simp [lift]

/-- The finite-field affine map augmented by the same sequence of directions. -/
def map (x : Φ.flag.Node) : FpCoord p d →ᵃ[ZMod p] FpCoord p (Φ.flag.rank x + e x) :=
  Coord.append (Φ.representation.map x) (AffineMap.pi fun i : Fin (e x) ↦ ξ i)

@[simp]
theorem lift_mod (x : Φ.flag.Node) (v : FpCoord p d) : (lift Φ e ξ x v).mod p = map Φ e ξ x v := by
  apply Coord.ext_first_last
  · ext i
    simp [lift, map, IntCoord.mod, FpCoord.centeredLift]
  · ext i
    simp [lift, map, IntCoord.mod, slabCoordinates]

/-- The augmented support consists of lifts of the nonzero cumulative atoms. -/
noncomputable def support (x : Φ.flag.Node) : Finset (IntCoord (Φ.flag.rank x + e x)) :=
  (Finset.univ.filter fun v ↦ Φ.cumulativeWeight x v ≠ 0).image (lift Φ e ξ x)

@[simp]
theorem mem_support (x : Φ.flag.Node) (q : IntCoord (Φ.flag.rank x + e x)) :
    q ∈ support Φ e ξ x ↔ ∃ v, Φ.cumulativeWeight x v ≠ 0 ∧ lift Φ e ξ x v = q := by
  simp [support]

theorem support_nonempty (x : Φ.flag.Node) : (support Φ e ξ x).Nonempty := by
  obtain ⟨q, hq⟩ := Φ.liftedSupport_nonempty x
  obtain ⟨_, v, _, hv⟩ := (Φ.originalWeights.hat_ne_zero_iff x q).mp
    ((Φ.liftedSupport_spec x q).mp hq)
  exact ⟨lift Φ e ξ x v, (mem_support Φ e ξ x _).mpr ⟨v, hv, rfl⟩⟩

/-- Reducing the augmented integer support gives precisely the finite-field
image of the cumulative support. -/
theorem support_mod (x : Φ.flag.Node) :
    IntCoord.mod p '' (support Φ e ξ x : Set (IntCoord (Φ.flag.rank x + e x))) =
      map Φ e ξ x '' {v | Φ.cumulativeWeight x v ≠ 0} := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨v, hv, rfl⟩ := (mem_support Φ e ξ x z).mp hz
    exact ⟨v, hv, (lift_mod Φ e ξ x v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨lift Φ e ξ x v, (mem_support Φ e ξ x _).mpr ⟨v, hv, rfl⟩,
      lift_mod Φ e ξ x v⟩

/-- Projection of the augmented support recovers the entire old lifted support. -/
theorem first_image_support (hp : Odd p) (x : Φ.flag.Node) :
    (support Φ e ξ x).image (Coord.first (Φ.flag.rank x) (e x)) = Φ.liftedSupport x := by
  ext q
  constructor
  · rintro hq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨v, hv, rfl⟩ := (mem_support Φ e ξ x z).mp hz
    rw [lift_first]
    exact Φ.centeredLift_mem_liftedSupport hp x hv
  · intro hq
    obtain ⟨hc, v, hmap, hv⟩ := (Φ.originalWeights.hat_ne_zero_iff x q).mp
      ((Φ.liftedSupport_spec x q).mp hq)
    refine Finset.mem_image.mpr ⟨lift Φ e ξ x v,
      (mem_support Φ e ξ x _).mpr ⟨v, hv, rfl⟩, ?_⟩
    rw [lift_first, hmap, FpCoord.centeredLift_mod hc]

/-- Along an order relation keep only the upper node's prefix of directions. -/
noncomputable def transition (he : Antitone e) {x y : Φ.flag.Node} (h : x ≤ y) :
    IntegralAffineMap (Φ.flag.rank x + e x) (Φ.flag.rank y + e y) :=
  (Φ.flag.transition h).extendPrefix (e x) (e y) (he h)

theorem transition_lift (hp : Odd p) (he : Antitone e) {x y : Φ.flag.Node} (h : x ≤ y)
    (v : FpCoord p d) (hv : Φ.cumulativeWeight x v ≠ 0) :
    (transition Φ e he h).integer (lift Φ e ξ x v) = lift Φ e ξ y v := by
  apply Coord.ext_first_last
  · change Coord.first (Φ.flag.rank y) (e y)
        (Coord.extendPrefix (Φ.flag.transition h).toIntAffineMap (e x) (e y) (he h)
          (lift Φ e ξ x v)) = _
    rw [Coord.first_extendPrefix, lift_first, lift_first]
    exact Φ.transition_centeredLift hp h v hv
  · change Coord.last (Φ.flag.rank y) (e y)
        (Coord.extendPrefix (Φ.flag.transition h).toIntAffineMap (e x) (e y) (he h)
          (lift Φ e ξ x v)) = _
    rw [Coord.last_extendPrefix, lift_last, lift_last]
    rfl

theorem transition_support (hp : Odd p) (he : Antitone e) {x y : Φ.flag.Node} (h : x ≤ y)
    {q : IntCoord (Φ.flag.rank x + e x)} (hq : q ∈ support Φ e ξ x) :
    (transition Φ e he h).integer q ∈ support Φ e ξ y := by
  obtain ⟨v, hv, rfl⟩ := (mem_support Φ e ξ x q).mp hq
  rw [transition_lift Φ e ξ hp he h v hv]
  exact (mem_support Φ e ξ y _).mpr
    ⟨v, Φ.originalWeights.cumulative_ne_zero_of_le h hv, rfl⟩

theorem transition_refl (he : Antitone e) (x : Φ.flag.Node) :
    transition Φ e he (le_refl x) = IntegralAffineMap.id (Φ.flag.rank x + e x) := by
  unfold transition
  rw [Φ.flag.transition_refl]
  exact IntegralAffineMap.extendPrefix_id _ _

theorem transition_trans (he : Antitone e) {x y z : Φ.flag.Node}
    (hxy : x ≤ y) (hyz : y ≤ z) :
    transition Φ e he (hxy.trans hyz) =
      (transition Φ e he hyz).comp (transition Φ e he hxy) := by
  unfold transition
  rw [Φ.flag.transition_trans]
  exact IntegralAffineMap.extendPrefix_comp _ _ (he hxy) (he hyz)

/-- The actual support diagram used before minimalizing augmented fibres. -/
noncomputable abbrev diagram (hp : Odd p) (he : Antitone e) : LatticeSupportDiagram where
  Node := Φ.flag.Node
  rank x := Φ.flag.rank x + e x
  support := support Φ e ξ
  support_nonempty := support_nonempty Φ e ξ
  transition h := transition Φ e he h
  transition_support h := transition_support Φ e ξ hp he h
  transition_refl := transition_refl Φ e he
  transition_trans := transition_trans Φ e he

/-- The old-coordinate projection maps the augmented support hull onto the
original node polytope. -/
theorem first_image_polytope (hp : Odd p) (he : Antitone e) (x : Φ.flag.Node) :
    (IntegralAffineMap.first (Φ.flag.rank x) (e x)).real ''
        ((diagram Φ e ξ hp he).polytope x).carrier = (Φ.flag.polytope x).carrier := by
  rw [(diagram Φ e ξ hp he).polytope_carrier, AffineMap.image_convexHull,
    Φ.polytope_eq_liftedSupport]
  congr 1
  ext q
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨Coord.first (Φ.flag.rank x) (e x) z, ?_, ?_⟩
    · rw [← first_image_support Φ e ξ hp x]
      exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
    · rfl
  · rintro ⟨z, hz, rfl⟩
    rw [← first_image_support Φ e ξ hp x] at hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨IntCoord.real q, ⟨q, hq, rfl⟩, rfl⟩

/-- The augmented affine maps commute with the augmented transitions on the
old represented affine spaces. -/
theorem map_compatible (he : Antitone e) {x y : Φ.flag.Node} (h : x ≤ y)
    {v : FpCoord p d} (hv : v ∈ Φ.representation.space x) :
    map Φ e ξ y v = (transition Φ e he h).modp p (map Φ e ξ x v) := by
  apply Coord.ext_first_last
  · change Coord.first (Φ.flag.rank y) (e y) (map Φ e ξ y v) =
      Coord.first (Φ.flag.rank y) (e y)
        (Coord.extendPrefix ((Φ.flag.transition h).modp p) (e x) (e y) (he h) (map Φ e ξ x v))
    simp only [map, Coord.first_append, Coord.first_extendPrefix]
    exact Φ.representation.compatible h hv
  · change Coord.last (Φ.flag.rank y) (e y) (map Φ e ξ y v) =
      Coord.last (Φ.flag.rank y) (e y)
        (Coord.extendPrefix ((Φ.flag.transition h).modp p) (e x) (e y) (he h) (map Φ e ξ x v))
    simp only [map, Coord.last_append, Coord.last_extendPrefix]
    rfl

/-- Forgetting the slab coordinates commutes with diagram transitions. -/
theorem first_comp_transition (he : Antitone e) {x y : Φ.flag.Node} (h : x ≤ y) :
    (IntegralAffineMap.first (Φ.flag.rank y) (e y)).comp (transition Φ e he h) =
      (Φ.flag.transition h).comp (IntegralAffineMap.first (Φ.flag.rank x) (e x)) :=
  IntegralAffineMap.first_comp_extendPrefix _ _ _ (he h)

theorem lift_centered (hp : Odd p) (x : Φ.flag.Node) (v : FpCoord p d) :
    IsCenteredLift p (lift Φ e ξ x v) := by
  apply latticeSupNorm_le_of_first_last
  · rw [lift_first]
    exact FpCoord.isCenteredLift_centeredLift hp _
  · rw [lift_last]
    exact FpCoord.isCenteredLift_centeredLift hp (fun i : Fin (e x) ↦ ξ i v)

theorem support_centered (hp : Odd p) (x : Φ.flag.Node)
    (q : IntCoord (Φ.flag.rank x + e x)) (hq : q ∈ support Φ e ξ x) : IsCenteredLift p q := by
  obtain ⟨v, _, rfl⟩ := (mem_support Φ e ξ x q).mp hq
  exact lift_centered Φ e ξ hp x v

/-- Bounds for the old support and slab block give a uniform bound for every
augmented support point. -/
theorem support_bound (hp : Odd p) {K L : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K)
    (hL : ∀ x v, Φ.cumulativeWeight x v ≠ 0 → latticeSupNorm (slabCoordinates (e x) ξ v) ≤ L x)
    (x : Φ.flag.Node) (q : IntCoord (Φ.flag.rank x + e x)) (hq : q ∈ support Φ e ξ x) :
    latticeSupNorm q ≤ max (K x) (L x) := by
  obtain ⟨v, hv, rfl⟩ := (mem_support Φ e ξ x q).mp hq
  apply latticeSupNorm_le_of_first_last
  · rw [lift_first]
    apply (le_max_left _ _).trans'
    apply hK
    rw [Φ.polytope_eq_liftedSupport]
    exact subset_convexHull ℝ _
      ⟨_, Φ.centeredLift_mem_liftedSupport hp x hv, rfl⟩
  · rw [lift_last]
    exact (hL x v hv).trans (le_max_right _ _)

end EGZ.FlagDecomposition.Augmented
