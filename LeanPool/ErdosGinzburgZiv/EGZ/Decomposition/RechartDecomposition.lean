/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartRepresentation
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartMass
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Faces

/-!
# A decomposition in support-generated lattice coordinates

The recharted flag and finite-field representation form an actual flag
decomposition. Every face contains a new support generator; lifting its old
chart image to an old local generator produces a new proper point over that
face. All weights and lifted masses are preserved, and the new decomposition
has minimal ambient affine spaces and integer lattices.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.FlagDecomposition.Rechart

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f)
    (C : ∀ x, IntegerLatticeChart (Φ.liftedSupport x))
    (hp : Odd p)
    (hinj : ∀ x, Function.Injective ((chart Φ C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

include hp hinj hcenter

open Classical in
theorem raw_hat (x : Φ.flag.Node) (q : IntCoord (C x).rank) :
    FlagDecompositionRaw.hat (representation Φ C hp hinj) Φ.localWeight x q =
      Φ.hat x ((C x).map q) :=
  Φ.hat_rechart hp x (C x) (hinj x) (hcenter x) q

open Classical in
theorem raw_localLift (x : Φ.flag.Node) (q : IntCoord (C x).rank) :
    FlagDecompositionRaw.localLift (representation Φ C hp hinj) Φ.localWeight x q =
      Φ.localLift x ((C x).map q) :=
  Φ.localLift_rechart hp x (C x) (hinj x) (hcenter x) q

open Classical in
/-- Every new face is visible to a local generator transported from the old
decomposition. This proves the visibility field of the new decomposition. -/
theorem faces_visible (x : Φ.flag.Node) (Γ : (polytope Φ C x).Face) :
    FlagDecompositionRaw.VisibleFace (representation Φ C hp hinj) Φ.localWeight x Γ := by
  obtain ⟨q, hq⟩ := Γ.generatorFinset_nonempty
  have hq' := Finset.mem_filter.mp hq
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq'.1
  have hzold : (C x).map z ∈ Φ.liftedSupport x := (C x).mem_coordinateSupport.mp hz
  obtain ⟨y, hyx, w, hw, hwz⟩ := Φ.originalWeights.exists_localLift_of_hat_ne_zero hp
    x ((C x).map z) ((Φ.liftedSupport_spec x _).mp hzold)
  have hwold : Φ.localLift y w ≠ 0 := hw
  have hwsupport : w ∈ Φ.liftedSupport y :=
    (Φ.liftedSupport_spec y w).mpr
      (ne_of_gt ((Nat.pos_of_ne_zero hwold).trans_le (Φ.localLift_le_hat y w)))
  let w' := (C y).coordinates w
  have hwmap : (C y).map w' = w := (C y).map_coordinates_of_mem hwsupport
  have hwmem : w'.real ∈ (polytope Φ C y).carrier := by
    rw [polytope_carrier]
    exact _root_.subset_convexHull ℝ _
      ⟨w', (C y).coordinates_mem_coordinateSupport hwsupport, rfl⟩
  have hwlocal : FlagDecompositionRaw.localLift (representation Φ C hp hinj)
      Φ.localWeight y w' ≠ 0 := by
    rw [raw_localLift Φ C hp hinj hcenter, hwmap]
    exact hwold
  have htransition : (transition Φ C hyx).real w'.real = z.real := by
    apply chart_real_injective Φ C x
    rw [chart_transition_real, (chart Φ C y).real_integer,
      (chart Φ C x).real_integer]
    change (Φ.flag.transition hyx).real (((C y).map w').real) = ((C x).map z).real
    rw [hwmap, (Φ.flag.transition hyx).real_integer, hwz]
  let r : (flag Φ C).Point := ⟨y, w'.real, hwmem⟩
  refine ⟨r, ConvexFlag.subset_convexHull (flag Φ C) _ ?_, hyx, ?_⟩
  · exact ⟨w', rfl, hwlocal⟩
  · change (transition Φ C hyx).real w'.real ∈ Γ.carrier
    rw [htransition]
    exact hq'.2

open Classical in
/-- Replace every fibre by its support-generated integer lattice coordinates
and every ambient affine space by its cumulative support span. -/
noncomputable abbrev decomposition : FlagDecomposition p d f where
  flag := flag Φ C
  representation := representation Φ C hp hinj
  localWeight := Φ.localWeight
  local_supported := localWeight_supported Φ
  retained_le := Φ.retained_le
  liftedSupport x := (C x).coordinateSupport
  liftedSupport_spec x q := by
    rw [raw_hat Φ C hp hinj hcenter, (C x).mem_coordinateSupport]
    exact Φ.liftedSupport_spec x ((C x).map q)
  liftedSupport_nonempty x := (C x).coordinateSupport_nonempty (Φ.liftedSupport_nonempty x)
  polytope_eq_liftedSupport := polytope_carrier Φ C
  faces_visible := faces_visible Φ C hp hinj hcenter

open Classical in
@[simp]
theorem decomposition_localWeight (x : Φ.flag.Node) :
    (decomposition Φ C hp hinj hcenter).localWeight x = Φ.localWeight x := rfl

open Classical in
@[simp]
theorem decomposition_cumulativeWeight (x : Φ.flag.Node) :
    (decomposition Φ C hp hinj hcenter).cumulativeWeight x = Φ.cumulativeWeight x := rfl

open Classical in
@[simp]
theorem decomposition_retainedWeight :
    (decomposition Φ C hp hinj hcenter).retainedWeight = Φ.retainedWeight := rfl

open Classical in
@[simp]
theorem decomposition_retainedMass :
    (decomposition Φ C hp hinj hcenter).retainedMass = Φ.retainedMass := rfl

open Classical in
@[simp]
theorem decomposition_liftedSupport (x : Φ.flag.Node) :
    (decomposition Φ C hp hinj hcenter).liftedSupport x = (C x).coordinateSupport := rfl

open Classical in
@[simp]
theorem decomposition_hat (x : Φ.flag.Node) (q : IntCoord (C x).rank) :
    (decomposition Φ C hp hinj hcenter).hat x q = Φ.hat x ((C x).map q) :=
  raw_hat Φ C hp hinj hcenter x q

open Classical in
@[simp]
theorem decomposition_localLift (x : Φ.flag.Node) (q : IntCoord (C x).rank) :
    (decomposition Φ C hp hinj hcenter).localLift x q = Φ.localLift x ((C x).map q) :=
  raw_localLift Φ C hp hinj hcenter x q

open Classical in
/-- The new ambient spaces and integer coordinate supports satisfy both
minimality conditions. -/
theorem decomposition_isMinimal : (decomposition Φ C hp hinj hcenter).IsMinimal := by
  intro x
  exact ⟨rfl, (C x).coordinateSupport_affineIntSpans⟩

open Classical in
theorem decomposition_isKBounded {K B : Φ.flag.Node → ℕ} (hΦ : Φ.IsKBounded K)
    (hC : ∀ x (q : IntCoord (C x).rank),
      latticeSupNorm ((C x).map q) ≤ K x → latticeSupNorm q ≤ B x) :
    (decomposition Φ C hp hinj hcenter).IsKBounded B :=
  polytope_bound Φ C hΦ hC

open Classical in
/-- Recharting preserves the complete finite set of positive lifted masses,
so in particular it preserves their minimum. -/
theorem decomposition_gap (x : Φ.flag.Node) :
    (decomposition Φ C hp hinj hcenter).gap x = Φ.gap x := by
  have hmass : (C x).coordinateSupport.image
      (Φ.hat x ∘ (C x).map) = (Φ.liftedSupport x).image (Φ.hat x) := by
    rw [← Finset.image_image, (C x).image_coordinateSupport]
  have hhat : (decomposition Φ C hp hinj hcenter).hat x = Φ.hat x ∘ (C x).map :=
    funext (decomposition_hat Φ C hp hinj hcenter x)
  unfold gap
  change ((C x).coordinateSupport.image ((decomposition Φ C hp hinj hcenter).hat x)).min' _ = _
  simp only [hhat, hmass]

end EGZ.FlagDecomposition.Rechart
