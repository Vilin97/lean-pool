/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedDiagram
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedRepresentation
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportRechartMass
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportDecomposition
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportParameters
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FacePreservation

/-!
# Decompositions with additional affine coordinates

Appending a common prefix of slab coordinates and then choosing the generated
integer lattice charts yields an actual minimal decomposition on the same
nodes and with the same local weights. Forgetting the additional coordinates
maps its proper points to the original decomposition.
-/

open scoped BigOperators

namespace EGZ.FlagDecomposition

open Classical in
/-- Reduced nodes depend only on the bases carrying nonzero local weight,
and are unchanged when the coordinate maps or polytopes are replaced. -/
theorem isReducedElement_iff_sup'_localWeight {p d : ℕ} [NeZero p]
    {f : FpCoord p d → ℕ} (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : Φ.flag.Node) :
    Φ.IsReducedElement x ↔
      ∃ (s : Finset Φ.flag.Node) (hs : s.Nonempty),
        (∀ y ∈ s, ∃ v, Φ.localWeight y v ≠ 0) ∧ s.sup' hs id = x := by
  rw [Φ.isReducedElement_iff_sup'_localLift]
  constructor
  · rintro ⟨s, hs, hlocal, hsup⟩
    refine ⟨s, hs, ?_, hsup⟩
    intro y hy
    obtain ⟨z, hz⟩ := hlocal y hy
    obtain ⟨_, v, _, hv⟩ := (FlagDecompositionRaw.centeredFibreMass_ne_zero_iff
      (Φ.localWeight y) (Φ.representation.map y) z).mp hz
    exact ⟨v, hv⟩
  · rintro ⟨s, hs, hlocal, hsup⟩
    refine ⟨s, hs, ?_, hsup⟩
    intro y hy
    obtain ⟨v, hv⟩ := hlocal y hy
    refine ⟨FpCoord.centeredLift (Φ.representation.map y v), ?_⟩
    exact (FlagDecompositionRaw.centeredFibreMass_ne_zero_iff
      (Φ.localWeight y) (Φ.representation.map y) _).mpr
      ⟨FpCoord.isCenteredLift_centeredLift hp _, v,
        (FpCoord.mod_centeredLift _).symm, hv⟩

end EGZ.FlagDecomposition

namespace EGZ.FlagDecomposition.Augmented

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (e : Φ.flag.Node → ℕ)
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p)
    (hp : Odd p)

include hp

open Classical in
theorem lift_eq_centeredLift (x : Φ.flag.Node) (v : FpCoord p d) :
    lift Φ e ξ x v = FpCoord.centeredLift (map Φ e ξ x v) :=
  (lift_centered Φ e ξ hp x v).eq_of_mod_eq
    (FpCoord.isCenteredLift_centeredLift hp _)
    ((lift_mod Φ e ξ x v).trans (FpCoord.mod_centeredLift _).symm)

open Classical in
/-- The augmented supports are exactly the nonzero centered cumulative
fibres, even though the augmented affine maps need not be surjective. -/
theorem support_spec_centeredFibreMass (x : Φ.flag.Node)
    (q : IntCoord (Φ.flag.rank x + e x)) :
    q ∈ support Φ e ξ x ↔ FlagDecompositionRaw.centeredFibreMass
      (Φ.cumulativeWeight x) (map Φ e ξ x) q ≠ 0 := by
  rw [mem_support, FlagDecompositionRaw.centeredFibreMass_ne_zero_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨lift_centered Φ e ξ hp x v, v, (lift_mod Φ e ξ x v).symm, hv⟩
  · rintro ⟨hc, v, hmap, hv⟩
    exact ⟨v, hv, (lift_centered Φ e ξ hp x v).eq_of_mod_eq hc
      ((lift_mod Φ e ξ x v).trans hmap)⟩

open Classical in
theorem centeredLift_map_mem_support (x : Φ.flag.Node) (v : FpCoord p d)
    (hv : Φ.cumulativeWeight x v ≠ 0) :
    FpCoord.centeredLift (map Φ e ξ x v) ∈ support Φ e ξ x := by
  rw [← lift_eq_centeredLift Φ e ξ hp]
  exact (mem_support Φ e ξ x _).mpr ⟨v, hv, rfl⟩

open Classical in
/-- Forgetting the additional coordinates sends a nonzero augmented local
fibre to a nonzero original local fibre. -/
theorem localLift_first_ne_zero (x : Φ.flag.Node)
    (q : IntCoord (Φ.flag.rank x + e x))
    (hq : FlagDecompositionRaw.centeredFibreMass
      (Φ.localWeight x) (map Φ e ξ x) q ≠ 0) :
    Φ.localLift x (Coord.first (Φ.flag.rank x) (e x) q) ≠ 0 := by
  obtain ⟨hc, v, hmap, hv⟩ :=
    (FlagDecompositionRaw.centeredFibreMass_ne_zero_iff _ _ _).mp hq
  have heq : lift Φ e ξ x v = q :=
    (lift_centered Φ e ξ hp x v).eq_of_mod_eq hc ((lift_mod Φ e ξ x v).trans hmap)
  rw [← heq, lift_first]
  exact (FlagDecompositionRaw.centeredFibreMass_ne_zero_iff
    (Φ.localWeight x) (Φ.representation.map x) _).mpr
    ⟨FpCoord.isCenteredLift_centeredLift hp _, v, (FpCoord.mod_centeredLift _).symm, hv⟩

variable (he : Antitone e)
    (C : ∀ x, IntegerLatticeChart (support Φ e ξ x))

open Classical in
/-- The map from charted augmented coordinates to the original coordinates. -/
noncomputable def forget (x : Φ.flag.Node) :
    IntegralAffineMap (C x).rank (Φ.flag.rank x) :=
  (IntegralAffineMap.first (Φ.flag.rank x) (e x)).comp
    ((diagram Φ e ξ hp he).chart C x)

open Classical in
theorem forget_image_polytope (x : Φ.flag.Node) :
    (forget Φ e ξ hp he C x).real ''
        (((diagram Φ e ξ hp he).chartedFlag C).polytope x).carrier =
      (Φ.flag.polytope x).carrier := by
  change ((IntegralAffineMap.first (Φ.flag.rank x) (e x)).real ∘
    ((diagram Φ e ξ hp he).chart C x).real) '' _ = _
  rw [Set.image_comp, (diagram Φ e ξ hp he).chart_image_polytope,
    first_image_polytope]

open Classical in
theorem forget_mem_polytope (x : Φ.flag.Node) :
    Set.MapsTo (forget Φ e ξ hp he C x).real
      (((diagram Φ e ξ hp he).chartedFlag C).polytope x).carrier
      (Φ.flag.polytope x).carrier := by
  intro q hq
  rw [← forget_image_polytope Φ e ξ hp he C x]
  exact ⟨q, hq, rfl⟩

open Classical in
theorem forget_transition {x y : Φ.flag.Node} (h : x ≤ y)
    (q : RealCoord (C x).rank) :
    (forget Φ e ξ hp he C y).real
        (((diagram Φ e ξ hp he).chartedFlag C).transition h |>.real q) =
      (Φ.flag.transition h).real ((forget Φ e ξ hp he C x).real q) := by
  change (IntegralAffineMap.first (Φ.flag.rank y) (e y)).real
      (((diagram Φ e ξ hp he).chart C y).real
        (((diagram Φ e ξ hp he).chartedTransition C h).real q)) = _
  rw [(diagram Φ e ξ hp he).chart_transition_real]
  exact AffineMap.congr_fun
    (congrArg IntegralAffineMap.real (first_comp_transition Φ e he h))
    (((diagram Φ e ξ hp he).chart C x).real q)

variable [Fact p.Prime]
    (hmod : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

open Classical in
/-- The new represented space is the cumulative support span and is
contained in the old represented space. -/
theorem representation_space_le_original (x : Φ.flag.Node) :
    (representation Φ e ξ hp he C hmod).space x ≤ Φ.representation.space x := by
  change affineSpan (ZMod p) {v | Φ.cumulativeWeight x v ≠ 0} ≤ _
  exact affineSpan_le.mpr (fun v hv ↦ Φ.originalWeights.cumulative_supported x v hv)

open Classical in
/-- The modular chart retracts to the augmented affine map on the full
represented affine space, not only on its nonzero cumulative atoms. -/
theorem chart_representation_map (x : Φ.flag.Node) (v : FpCoord p d)
    (hv : v ∈ (representation Φ e ξ hp he C hmod).space x) :
    ((diagram Φ e ξ hp he).chart C x).modp p
        ((representation Φ e ξ hp he C hmod).map x v) = map Φ e ξ x v := by
  apply AffineMap.eqOn_affineSpan
    (f := (((diagram Φ e ξ hp he).chart C x).modp p).comp
      ((representation Φ e ξ hp he C hmod).map x)) (g := map Φ e ξ x) ?_ hv
  intro w hw
  exact (diagram Φ e ξ hp he).chart_coordinateMap C Φ.localWeight (map Φ e ξ) hmod
    (fun y ↦ (support_mod Φ e ξ y).symm) x w hw

open Classical in
theorem representation_map_eq_iff (x : Φ.flag.Node) (v w : FpCoord p d)
    (hv : v ∈ (representation Φ e ξ hp he C hmod).space x)
    (hw : w ∈ (representation Φ e ξ hp he C hmod).space x) :
    (representation Φ e ξ hp he C hmod).map x v =
        (representation Φ e ξ hp he C hmod).map x w ↔
      map Φ e ξ x v = map Φ e ξ x w := by
  constructor
  · intro heq
    rw [← chart_representation_map Φ e ξ hp he C hmod x v hv,
      ← chart_representation_map Φ e ξ hp he C hmod x w hw, heq]
  · intro heq
    exact congrArg (affineLeftInverse
      ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p)) heq

open Classical in
/-- The forgotten new coordinate is exactly the original coordinate on
the new represented affine space. -/
theorem forget_representation_map (x : Φ.flag.Node) (v : FpCoord p d)
    (hv : v ∈ (representation Φ e ξ hp he C hmod).space x) :
    (forget Φ e ξ hp he C x).modp p ((representation Φ e ξ hp he C hmod).map x v) =
      Φ.representation.map x v := by
  have h := congrArg (Coord.first (Φ.flag.rank x) (e x))
    (chart_representation_map Φ e ξ hp he C hmod x v hv)
  exact h.trans (Coord.first_append _ _ _)

open Classical in
/-- The charted augmented flag has the exact cumulative support required by
the decomposition constructor. -/
noncomputable def supportData : FlagDecompositionRaw.SupportData
    (representation Φ e ξ hp he C hmod) Φ.localWeight where
  support x := (C x).coordinateSupport
  support_spec x q := (C x).coordinateSupport_spec_rechart (map Φ e ξ x) (hmod x)
    hp (hcenter x) (Φ.cumulativeWeight x) (support_spec_centeredFibreMass Φ e ξ hp x) q
  support_nonempty x := (C x).coordinateSupport_nonempty (support_nonempty Φ e ξ x)
  polytope_eq x := ((diagram Φ e ξ hp he).rechart C).polytope_carrier x
  transition_support h _q hq := (diagram Φ e ξ hp he).chartedTransition_support C h hq
  local_supported := local_supported Φ e ξ hp he C hmod

open Classical in
/-- The actual augmented and minimalized decomposition, with unchanged
nodes and unchanged local weights. -/
noncomputable abbrev decomposition : FlagDecomposition p d f :=
  (supportData Φ e ξ hp he C hmod hcenter).decomposition hp f Φ.retained_le

open Classical in
theorem decomposition_isMinimal : (decomposition Φ e ξ hp he C hmod hcenter).IsMinimal := by
  intro x
  exact ⟨rfl, (C x).coordinateSupport_affineIntSpans⟩

open Classical in
@[simp]
theorem decomposition_retainedWeight :
    (decomposition Φ e ξ hp he C hmod hcenter).retainedWeight = Φ.retainedWeight := rfl

open Classical in
@[simp]
theorem decomposition_retainedMass :
    (decomposition Φ e ξ hp he C hmod hcenter).retainedMass = Φ.retainedMass := rfl

open Classical in
@[simp]
theorem decomposition_cumulativeWeight (x : Φ.flag.Node) :
    (decomposition Φ e ξ hp he C hmod hcenter).cumulativeWeight x =
      Φ.cumulativeWeight x := rfl

open Classical in
@[simp]
theorem decomposition_localWeight (x : Φ.flag.Node) :
    (decomposition Φ e ξ hp he C hmod hcenter).localWeight x = Φ.localWeight x := rfl

open Classical in
@[simp]
theorem card_decomposition :
    @Fintype.card (decomposition Φ e ξ hp he C hmod hcenter).flag.Node
        (decomposition Φ e ξ hp he C hmod hcenter).flag.nodeFintype =
      Fintype.card Φ.flag.Node := rfl

open Classical in
/-- The new centered cumulative mass is the old augmented centered mass at
the image under the integer chart. -/
theorem decomposition_hat (x : Φ.flag.Node) (q : IntCoord (C x).rank) :
    (decomposition Φ e ξ hp he C hmod hcenter).hat x q =
      FlagDecompositionRaw.centeredFibreMass (Φ.cumulativeWeight x)
        (map Φ e ξ x) ((C x).map q) :=
  (C x).centeredFibreMass_rechart (map Φ e ξ x) (hmod x) hp (hcenter x)
    (Φ.cumulativeWeight x) (centeredLift_map_mem_support Φ e ξ hp x) q

open Classical in
theorem decomposition_localLift (x : Φ.flag.Node) (q : IntCoord (C x).rank) :
    (decomposition Φ e ξ hp he C hmod hcenter).localLift x q =
      FlagDecompositionRaw.centeredFibreMass (Φ.localWeight x)
        (map Φ e ξ x) ((C x).map q) :=
  (C x).centeredFibreMass_rechart (map Φ e ξ x) (hmod x) hp (hcenter x)
    (Φ.localWeight x) (fun v hv ↦ centeredLift_map_mem_support Φ e ξ hp x v
      (ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le
        (FlagDecompositionRaw.localWeight_le_cumulative Φ.localWeight x v)))) q

open Classical in
/-- Changing coordinates leaves the set of reduced nodes exactly unchanged. -/
theorem decomposition_isReducedElement_iff (x : Φ.flag.Node) :
    (decomposition Φ e ξ hp he C hmod hcenter).IsReducedElement x ↔
      Φ.IsReducedElement x := by
  rw [(decomposition Φ e ξ hp he C hmod hcenter).isReducedElement_iff_sup'_localWeight hp,
    Φ.isReducedElement_iff_sup'_localWeight hp]

open Classical in
theorem decomposition_isReduced_iff :
    (decomposition Φ e ξ hp he C hmod hcenter).IsReduced ↔ Φ.IsReduced :=
  forall_congr' (decomposition_isReducedElement_iff Φ e ξ hp he C hmod hcenter)

open Classical in
/-- Completeness of an old element persists when the coordinate fibres are
refined by the additional affine directions. -/
theorem decomposition_isCompleteElement (x : Φ.flag.Node) (t : ℕ) (δ : ℝ)
    (hcomplete : Φ.IsCompleteElement x t δ) :
    (decomposition Φ e ξ hp he C hmod hcenter).IsCompleteElement x t δ := by
  intro η hη
  apply hcomplete η
  obtain ⟨v, w, hv, hw, heq, hne⟩ := hη
  refine ⟨v, w, representation_space_le_original Φ e ξ hp he C hmod x hv,
    representation_space_le_original Φ e ξ hp he C hmod x hw, ?_, hne⟩
  rw [← forget_representation_map Φ e ξ hp he C hmod x v hv,
    ← forget_representation_map Φ e ξ hp he C hmod x w hw]
  exact congrArg ((forget Φ e ξ hp he C x).modp p) heq

open Classical in
/-- Bounds for the slab block and the chart inverse bound every integer
point of the new polytope. -/
theorem decomposition_isKBounded {K L B : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K)
    (hL : ∀ x v, Φ.cumulativeWeight x v ≠ 0 →
      latticeSupNorm (slabCoordinates (e x) ξ v) ≤ L x)
    (hC : ∀ x (q : IntCoord (C x).rank),
      latticeSupNorm ((C x).map q) ≤ max (K x) (L x) → latticeSupNorm q ≤ B x) :
    (decomposition Φ e ξ hp he C hmod hcenter).IsKBounded B :=
  (diagram Φ e ξ hp he).charted_polytope_bound C
    ((diagram Φ e ξ hp he).polytope_bound (support_bound Φ e ξ hp hK hL)) hC

open Classical in
/-- Project a new flag point by forgetting the augmented coordinate block. -/
noncomputable def forwardPoint
    (q : (decomposition Φ e ξ hp he C hmod hcenter).flag.Point) : Φ.flag.Point :=
  q.map (SupHom.id _) (fun x ↦ (forget Φ e ξ hp he C x).real)
    (forget_mem_polytope Φ e ξ hp he C)

open Classical in
theorem forwardPoint_mem_omegaZero
    {q : (decomposition Φ e ξ hp he C hmod hcenter).flag.Point}
    (hq : q ∈ (decomposition Φ e ξ hp he C hmod hcenter).omegaZero) :
    forwardPoint Φ e ξ hp he C hmod hcenter q ∈ Φ.omegaZero := by
  obtain ⟨z, hz, hw⟩ := hq
  refine ⟨Coord.first (Φ.flag.rank q.base) (e q.base) ((C q.base).map z), ?_, ?_⟩
  · change ((forget Φ e ξ hp he C q.base).integer z).real =
      (forget Φ e ξ hp he C q.base).real q.val
    rw [← hz, (forget Φ e ξ hp he C q.base).real_integer]
  · apply localLift_first_ne_zero Φ e ξ hp
    change (decomposition Φ e ξ hp he C hmod hcenter).localLift q.base z ≠ 0 at hw
    rwa [decomposition_localLift] at hw

open Classical in
/-- Forgetting the slab block is a subdivision map to the original flag. -/
noncomputable def subdivisionMap :
    SubdivisionMap Φ (decomposition Φ e ξ hp he C hmod hcenter) :=
  SubdivisionMap.ofLocalGenerators (SupHom.id _)
    (fun x ↦ (forget Φ e ξ hp he C x).real)
    (forget_mem_polytope Φ e ξ hp he C) (forget_transition Φ e ξ hp he C)
    (fun _ hq ↦ forwardPoint_mem_omegaZero Φ e ξ hp he C hmod hcenter hq)

omit [Fact p.Prime] hmod hcenter in
open Classical in
theorem face_preimage_nonempty (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face) :
    ((((diagram Φ e ξ hp he).chartedFlag C).polytope x).carrier ∩
      (forget Φ e ξ hp he C x).real ⁻¹' Γ.carrier).Nonempty := by
  obtain ⟨q, hq⟩ := Γ.nonempty
  have hpoly := Γ.subset_polytope hq
  rw [← forget_image_polytope Φ e ξ hp he C x] at hpoly
  obtain ⟨r, hr, rfl⟩ := hpoly
  exact ⟨r, hr, hq⟩

open Classical in
/-- Previously realized faces remain realized after pulling back along the
old-coordinate projection. -/
theorem decomposition_isRealizedFace (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face)
    (hΓ : Φ.IsRealizedFace x Γ) :
    (decomposition Φ e ξ hp he C hmod hcenter).IsRealizedFace x
      ((subdivisionMap Φ e ξ hp he C hmod hcenter).face x Γ
        (face_preimage_nonempty Φ e ξ hp he C x Γ)) :=
  (subdivisionMap Φ e ξ hp he C hmod hcenter).isRealizedFace x Γ
    (face_preimage_nonempty Φ e ξ hp he C x Γ) hΓ

end EGZ.FlagDecomposition.Augmented
