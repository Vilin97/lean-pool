/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Pullback
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.TwoLayer
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceSelection
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceSupport
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.FaceCombinations

/-!
# Realizing a face by splitting local weights

The positive generators of a proper point over an exposed face also lie over
that face. This allows a refinement that moves the selected local atoms to
a lower layer to realize the face while retaining the old upper fibres.
-/

open scoped BigOperators

namespace EGZ

namespace ConvexFlag.ConvexCombination

open Classical in
/-- Every positively weighted generator of a flag combination lies on any
upper face containing the combination. -/
theorem mem_face_of_pos {F : ConvexFlag} {I : Type*} [Fintype I]
    {points : I → F.Point} {weight : I → ℝ} {result : F.Point}
    (c : ConvexCombination points weight result) {x : F.Node}
    (hx : result.base ≤ x) (Γ : (F.polytope x).Face)
    (hΓ : result.coord hx ∈ Γ.carrier) {i : I} (hi : 0 < weight i) :
    (points i).coord ((c.base_isLUB.1 i hi).trans hx) ∈ Γ.carrier := by
  classical
  exact Γ.mem_of_pos_of_eq_convexCombination
    (fun j : {j // 0 < weight j} ↦
      (points j).coord ((c.base_isLUB.1 j j.property).trans hx))
    (fun j ↦ weight j) (result.coord hx)
    (fun j ↦ F.transition_mem _ (points j).val_mem)
    (fun j ↦ (j.property).le) c.sum_active (c.coord_eq hx) hΓ
    (i := ⟨i, hi⟩) hi

end ConvexFlag.ConvexCombination

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

open Classical in
/-- Bounding the bases of the local generators over a face bounds its face
index. The same bound passes to every proper convex combination. -/
theorem faceIndex_le_of_local_bases (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face) (b : Φ.flag.Node)
    (hlocal : ∀ q, q ∈ Φ.omegaZero → ∀ h : q.base ≤ x,
      q.coord h ∈ Γ.carrier → q.base ≤ b) : Φ.faceIndex x Γ ≤ b := by
  classical
  apply Finset.sup'_le
  intro y hy
  simp only [faceBases, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  obtain ⟨⟨n, points, weight, hpoints, hcomb⟩, hx, hface⟩ := hq
  apply hcomb.base_isLUB.2
  intro i hi
  exact hlocal (points i) (hpoints i) ((hcomb.base_isLUB.1 i hi).trans hx)
    (hcomb.mem_face_of_pos hx Γ hface hi)

open Classical in
/-- A node containing every local-generator base over a face realizes the
face as soon as its whole polytope maps into that face. -/
theorem isRealizedFace_of_local_bases (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face) (b : Φ.flag.Node)
    (hb : b ≤ x)
    (hlocal : ∀ q, q ∈ Φ.omegaZero → ∀ h : q.base ≤ x,
      q.coord h ∈ Γ.carrier → q.base ≤ b)
    (hpoly : ∀ q ∈ (Φ.flag.polytope b).carrier,
      (Φ.flag.transition hb).real q ∈ Γ.carrier) : Φ.IsRealizedFace x Γ := by
  have hindex : Φ.faceIndex x Γ ≤ b := Φ.faceIndex_le_of_local_bases x Γ b hlocal
  intro q hq
  have hq' := hpoly ((Φ.flag.transition hindex).real q) (Φ.flag.transition_mem hindex hq)
  have htrans := Φ.flag.transition_trans hindex hb
  change (Φ.flag.transition (Φ.faceIndex_le x Γ)).real q ∈ Γ.carrier
  rw [htrans]
  exact hq'

namespace FaceRefinement

variable (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (selected : FpCoord p d → Prop)

open Classical in
/-- The layer-forgetting order map. -/
def projection : TwoLayer.Node anchor →o Φ.flag.Node where
  toFun := TwoLayer.projection anchor
  monotone' := OrderHomClass.monotone (TwoLayer.projection anchor)

open Classical in
/-- Split the local atoms selected below the anchor into lower copies. -/
noncomputable abbrev splitWeights : Φ.SplitWeights (projection Φ anchor) where
  weight := TwoLayer.splitWeight anchor Φ.localWeight selected
  weight_le := TwoLayer.splitWeight_le anchor Φ.localWeight selected
  nonzero := by
    obtain ⟨x, v, hv⟩ := Φ.originalWeights.nonzero
    obtain ⟨a, _, ha⟩ := TwoLayer.exists_splitWeight_eq anchor Φ.localWeight selected x v
    exact ⟨a, v, by rwa [ha]⟩
  retained_le v := by
    rw [TwoLayer.sum_splitWeight]
    exact Φ.retained_le v

open Classical in
@[simp]
theorem cumulative_upper (x : Φ.flag.Node) (v : FpCoord p d) :
    (splitWeights Φ anchor selected).cumulative (TwoLayer.upper anchor x) v =
      Φ.cumulativeWeight x v :=
  TwoLayer.cumulativeWeight_upper anchor Φ.localWeight selected x v

open Classical in
@[simp]
theorem cumulative_lower (x : Φ.flag.Node) (hx : x ≤ anchor) (v : FpCoord p d) :
    (splitWeights Φ anchor selected).cumulative (TwoLayer.lower anchor x hx) v =
      if selected v then Φ.cumulativeWeight x v else 0 :=
  TwoLayer.cumulativeWeight_lower anchor Φ.localWeight selected x hx v

open Classical in
@[simp]
theorem hat_upper (x : Φ.flag.Node) (q : IntCoord (Φ.flag.rank x)) :
    (splitWeights Φ anchor selected).hat (TwoLayer.upper anchor x) q = Φ.hat x q := by
  have hc := funext (cumulative_upper Φ anchor selected x)
  change (if IsCenteredLift p q then FlagDecompositionRaw.affineFibreMass
    ((splitWeights Φ anchor selected).cumulative (TwoLayer.upper anchor x))
      (Φ.representation.map x) (q.mod p) else 0) = _
  rw [hc]
  rfl

variable (hp : Odd p)

open Classical in
/-- Rebuild the selected split on its active nodes. -/
noncomputable abbrev decomposition : FlagDecomposition p d f :=
  (splitWeights Φ anchor selected).decomposition hp

open Classical in
/-- Every old node survives in the upper layer. -/
theorem active_upper (x : Φ.flag.Node) :
    ((splitWeights Φ anchor selected).rebuildData hp).Active (TwoLayer.upper anchor x) := by
  obtain ⟨q, hq⟩ := Φ.liftedSupport_nonempty x
  obtain ⟨_, v, _, hv⟩ := (Φ.originalWeights.hat_ne_zero_iff x q).mp
    ((Φ.liftedSupport_spec x q).mp hq)
  have hv' : (splitWeights Φ anchor selected).cumulative (TwoLayer.upper anchor x) v ≠ 0 := by
    rwa [cumulative_upper]
  obtain ⟨a, ha, hav⟩ := (FlagDecompositionRaw.cumulative_ne_zero_iff
    (F := Φ.flag.reindex (projection Φ anchor))
    (splitWeights Φ anchor selected).weight (TwoLayer.upper anchor x) v).mp hv'
  exact ⟨a, ha, v, hav⟩

open Classical in
/-- A lower node is active whenever its old cumulative mass contains a
selected atom. -/
theorem active_lower (x : Φ.flag.Node) (hx : x ≤ anchor) (v : FpCoord p d)
    (hv : Φ.cumulativeWeight x v ≠ 0) (hselected : selected v) :
    ((splitWeights Φ anchor selected).rebuildData hp).Active (TwoLayer.lower anchor x hx) := by
  have hv' : (splitWeights Φ anchor selected).cumulative (TwoLayer.lower anchor x hx) v ≠ 0 := by
    rwa [cumulative_lower, ite_eq_left hselected]
  obtain ⟨a, ha, hav⟩ := (FlagDecompositionRaw.cumulative_ne_zero_iff
    (F := Φ.flag.reindex (projection Φ anchor))
    (splitWeights Φ anchor selected).weight (TwoLayer.lower anchor x hx) v).mp hv'
  exact ⟨a, ha, v, hav⟩

open Classical in
/-- The active upper copy of an old node. -/
noncomputable def upper (x : Φ.flag.Node) : (decomposition Φ anchor selected hp).flag.Node :=
  ⟨TwoLayer.upper anchor x, active_upper Φ anchor selected hp x⟩

open Classical in
/-- The original node order embeds into the active upper layer. -/
noncomputable def upperOrderEmbedding :
    Φ.flag.Node ↪o (decomposition Φ anchor selected hp).flag.Node where
  toFun := upper Φ anchor selected hp
  inj' _ _ h :=
    congrArg (fun a : (decomposition Φ anchor selected hp).flag.Node ↦
      projection Φ anchor a.1) h
  map_rel_iff' := by
    intro x y
    exact TwoLayer.upper_le_upper anchor x y

open Classical in
theorem upper_cumulativeWeight (x : Φ.flag.Node) :
    (decomposition Φ anchor selected hp).cumulativeWeight (upper Φ anchor selected hp x) =
      Φ.cumulativeWeight x := by
  rw [SplitWeights.decomposition_cumulativeWeight]
  exact funext (cumulative_upper Φ anchor selected x)

open Classical in
@[simp]
theorem upper_hat (x : Φ.flag.Node) (q : IntCoord (Φ.flag.rank x)) :
    (decomposition Φ anchor selected hp).hat (upper Φ anchor selected hp x) q = Φ.hat x q := by
  rw [SplitWeights.decomposition_hat]
  exact hat_upper Φ anchor selected x q

open Classical in
@[simp]
theorem upper_space (x : Φ.flag.Node) :
    (decomposition Φ anchor selected hp).representation.space (upper Φ anchor selected hp x) =
      Φ.representation.space x := rfl

open Classical in
@[simp]
theorem upper_map (x : Φ.flag.Node) :
    (decomposition Φ anchor selected hp).representation.map (upper Φ anchor selected hp x) =
      Φ.representation.map x := rfl

open Classical in
@[simp]
theorem upper_liftedSupport (x : Φ.flag.Node) :
    (decomposition Φ anchor selected hp).liftedSupport (upper Φ anchor selected hp x) =
      Φ.liftedSupport x := by
  ext q
  exact ((decomposition Φ anchor selected hp).liftedSupport_spec _ q).trans
    ((Iff.of_eq (congrArg (fun m : ℕ ↦ m ≠ 0) (upper_hat Φ anchor selected hp x q))).trans
      (Φ.liftedSupport_spec x q).symm)

open Classical in
@[simp]
theorem upper_gap (x : Φ.flag.Node) :
    (decomposition Φ anchor selected hp).gap (upper Φ anchor selected hp x) = Φ.gap x := by
  have hhat := funext (upper_hat Φ anchor selected hp x)
  have hmass := congrArg₂
    (fun (S : Finset (IntCoord (Φ.flag.rank x))) (w : IntCoord (Φ.flag.rank x) → ℕ) ↦ S.image w)
    (upper_liftedSupport Φ anchor selected hp x) hhat
  have hmin {s t : Finset ℕ} (hs : s.Nonempty) (ht : t.Nonempty) (hst : s = t) :
      s.min' hs = t.min' ht := by
    subst t
    rfl
  exact hmin _ _ hmass

open Classical in
/-- The upper copy retains its original polytope. -/
theorem upper_polytope (x : Φ.flag.Node) :
    ((decomposition Φ anchor selected hp).flag.polytope (upper Φ anchor selected hp x)).carrier =
      (Φ.flag.polytope x).carrier := by
  rw [(decomposition Φ anchor selected hp).polytope_eq_liftedSupport,
    upper_liftedSupport, Φ.polytope_eq_liftedSupport]
  rfl

open Classical in
/-- An original face, viewed in its unchanged upper polytope. -/
noncomputable def upperFace (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face) :
    ((decomposition Φ anchor selected hp).flag.polytope (upper Φ anchor selected hp x)).Face where
  carrier := Γ.carrier
  is_exposed := by
    obtain ⟨functional, level, hle, hcarrier⟩ := Γ.is_exposed
    refine ⟨functional, level, ?_, ?_⟩
    · intro q hq
      exact hle q (by rwa [upper_polytope] at hq)
    · rw [upper_polytope]
      exact hcarrier
  nonempty := Γ.nonempty

open Classical in
@[simp]
theorem upperFace_carrier (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face) :
    (upperFace Φ anchor selected hp x Γ).carrier = Γ.carrier := rfl

open Classical in
theorem retainedWeight :
    (decomposition Φ anchor selected hp).retainedWeight = Φ.retainedWeight := by
  funext v
  rw [SplitWeights.decomposition_retainedWeight, TwoLayer.sum_splitWeight]
  rfl

open Classical in
@[simp]
theorem retainedMass : (decomposition Φ anchor selected hp).retainedMass = Φ.retainedMass :=
  congrArg natMass (retainedWeight Φ anchor selected hp)

open Classical in
/-- At most two copies of each old node survive. -/
theorem card_le :
    @Fintype.card (decomposition Φ anchor selected hp).flag.Node
      (decomposition Φ anchor selected hp).flag.nodeFintype ≤ 2 * Fintype.card Φ.flag.Node :=
  ((splitWeights Φ anchor selected).decomposition_card_le hp).trans
    (TwoLayer.card_nodes_le anchor)

open Classical in
/-- Both layers retain the old nodewise coordinate bounds. -/
theorem isKBounded {K : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K) :
    (decomposition Φ anchor selected hp).IsKBounded
      (fun x ↦ K (projection Φ anchor x.1)) :=
  (splitWeights Φ anchor selected).decomposition_isKBounded hp hK

open Classical in
/-- Forgetting layers maps the split decomposition into the old one. -/
noncomputable def subdivisionMap : SubdivisionMap Φ (decomposition Φ anchor selected hp) :=
  (splitWeights Φ anchor selected).subdivisionMap hp (fun _ _ ↦ rfl)

open Classical in
/-- Complete upper elements retain the same cumulative weight and
representation fibres. -/
theorem upper_isCompleteElement (x : Φ.flag.Node) (t : ℕ) (δ : ℝ)
    (hc : Φ.IsCompleteElement x t δ) :
    (decomposition Φ anchor selected hp).IsCompleteElement (upper Φ anchor selected hp x) t δ := by
  intro ξ hξ
  rw [upper_cumulativeWeight]
  exact hc ξ hξ

open Classical in
/-- Realized old faces remain realized at the unchanged upper nodes. -/
theorem upper_isRealizedFace (x : Φ.flag.Node) (Γ : (Φ.flag.polytope x).Face)
    (hΓ : Φ.IsRealizedFace x Γ) :
    (decomposition Φ anchor selected hp).IsRealizedFace
      (upper Φ anchor selected hp x) (upperFace Φ anchor selected hp x Γ) := by
  have hne :
      (((decomposition Φ anchor selected hp).flag.polytope
          (upper Φ anchor selected hp x)).carrier ∩ Γ.carrier).Nonempty := by
    rw [upper_polytope]
    exact Γ.nonempty.mono (fun _ hq ↦ ⟨Γ.subset_polytope hq, hq⟩)
  have hreal := (subdivisionMap Φ anchor selected hp).isRealizedFace
    (upper Φ anchor selected hp x) Γ hne hΓ
  have hface : (subdivisionMap Φ anchor selected hp).face
      (upper Φ anchor selected hp x) Γ hne = upperFace Φ anchor selected hp x Γ := by
    apply RationalPolytope.Face.ext
    ext q
    change (q ∈ ((decomposition Φ anchor selected hp).flag.polytope
      (upper Φ anchor selected hp x)).carrier ∧ q ∈ Γ.carrier) ↔ q ∈ Γ.carrier
    rw [upper_polytope]
    exact ⟨And.right, fun hq ↦ ⟨Γ.subset_polytope hq, hq⟩⟩
  rwa [hface] at hreal

include hp

open Classical in
/-- On the face-selected lower layer, a cumulative lifted fibre is either
retained in full or deleted according to its upper transition coordinate. -/
theorem face_hat_lower (Γ : (Φ.flag.polytope anchor).Face)
    (x : Φ.flag.Node) (hx : x ≤ anchor) (q : IntCoord (Φ.flag.rank x)) :
    (splitWeights Φ anchor (Φ.faceSelector anchor Γ)).hat (TwoLayer.lower anchor x hx) q =
      if (Φ.flag.transition hx).real q.real ∈ Γ.carrier then Φ.hat x q else 0 := by
  have hc := funext (cumulative_lower Φ anchor (Φ.faceSelector anchor Γ) x hx)
  change FlagDecompositionRaw.centeredFibreMass
    ((splitWeights Φ anchor (Φ.faceSelector anchor Γ)).cumulative (TwoLayer.lower anchor x hx))
      (Φ.representation.map x) q = _
  rw [hc]
  exact Φ.centeredFibreMass_faceSelector hp hx Γ q

open Classical in
/-- The lower anchor keeps precisely the lifted support points on its face. -/
theorem face_hat_lower_anchor (Γ : (Φ.flag.polytope anchor).Face)
    (q : IntCoord (Φ.flag.rank anchor)) :
    (splitWeights Φ anchor (Φ.faceSelector anchor Γ)).hat
        (TwoLayer.lower anchor anchor le_rfl) q =
      if q.real ∈ Γ.carrier then Φ.hat anchor q else 0 := by
  simpa only [Φ.flag.transition_refl, IntegralAffineMap.id_real, AffineMap.id_apply] using
    face_hat_lower Φ anchor hp Γ anchor le_rfl q

open Classical in
/-- A surviving local generator projecting onto the selected face lies in
the lower layer: its selected ambient atoms were removed from the upper
copy of its base. -/
theorem face_local_layer_zero (Γ : (Φ.flag.polytope anchor).Face)
    (q : (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).flag.Point)
    (hq : q ∈ (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).omegaZero)
    (h : q.base ≤ upper Φ anchor (Φ.faceSelector anchor Γ) hp anchor)
    (hface : q.coord h ∈ Γ.carrier) : q.base.1.1.2 = 0 := by
  obtain ⟨z, hz, hmass⟩ := hq
  have hproj : (projection Φ anchor q.base.1) ≤ anchor := h.1
  have hraw : (splitWeights Φ anchor (Φ.faceSelector anchor Γ)).localLift q.base.1 z ≠ 0 := hmass
  obtain ⟨hc, v, hmap, hv⟩ :=
    (FlagDecompositionRaw.localLift_ne_zero_iff _ _ _ _).mp hraw
  have hvold : Φ.localWeight (projection Φ anchor q.base.1) v ≠ 0 :=
    ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le
      ((splitWeights Φ anchor (Φ.faceSelector anchor Γ)).weight_le q.base.1 v))
  have hcum : Φ.cumulativeWeight (projection Φ anchor q.base.1) v ≠ 0 :=
    (Φ.originalWeights.cumulative_ne_zero_iff _ v).mpr ⟨_, le_rfl, hvold⟩
  have hcoordinate : (Φ.flag.transition hproj).real z.real ∈ Γ.carrier := by
    change (Φ.flag.transition hproj).real q.val ∈ Γ.carrier at hface
    rwa [hz]
  have hs : Φ.faceSelector anchor Γ v :=
    (Φ.faceSelector_iff hp hproj Γ z hc v hmap hcum).mpr hcoordinate
  by_contra hlayer
  apply hv
  change TwoLayer.splitWeight anchor Φ.localWeight (Φ.faceSelector anchor Γ) q.base.1 v = 0
  rw [TwoLayer.splitWeight, ite_eq_right hlayer, ite_eq_left ⟨hproj, hs⟩]

open Classical in
/-- Every nonempty face supplies a selected cumulative atom at the lower
anchor, so that anchor survives the rebuilding. -/
theorem face_active_lower_anchor (Γ : (Φ.flag.polytope anchor).Face) :
    ((splitWeights Φ anchor (Φ.faceSelector anchor Γ)).rebuildData hp).Active
      (TwoLayer.lower anchor anchor le_rfl) := by
  obtain ⟨z, hz⟩ := Φ.liftedSupport_face_nonempty anchor Γ
  obtain ⟨hz, hzΓ⟩ := Finset.mem_filter.mp hz
  obtain ⟨hc, v, hmap, hv⟩ := (Φ.originalWeights.hat_ne_zero_iff anchor z).mp
    ((Φ.liftedSupport_spec anchor z).mp hz)
  have hs : Φ.faceSelector anchor Γ v :=
    (Φ.faceSelector_iff hp le_rfl Γ z hc v hmap hv).mpr (by
      simpa only [Φ.flag.transition_refl, IntegralAffineMap.id_real, AffineMap.id_apply] using hzΓ)
  exact active_lower Φ anchor (Φ.faceSelector anchor Γ) hp anchor le_rfl v hv hs

open Classical in
/-- The active lower copy of the selected anchor. -/
noncomputable def lowerAnchor (Γ : (Φ.flag.polytope anchor).Face) :
    (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).flag.Node :=
  ⟨TwoLayer.lower anchor anchor le_rfl, face_active_lower_anchor Φ anchor hp Γ⟩

open Classical in
theorem lowerAnchor_le_upper (Γ : (Φ.flag.polytope anchor).Face) :
    lowerAnchor Φ anchor hp Γ ≤ upper Φ anchor (Φ.faceSelector anchor Γ) hp anchor := by
  change TwoLayer.lower anchor anchor le_rfl ≤ TwoLayer.upper anchor anchor
  exact (TwoLayer.lower_le_upper anchor anchor anchor le_rfl).mpr le_rfl

open Classical in
@[simp]
theorem lowerAnchor_liftedSupport (Γ : (Φ.flag.polytope anchor).Face) :
    (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).liftedSupport
        (lowerAnchor Φ anchor hp Γ) =
      (Φ.liftedSupport anchor).filter (fun q ↦ q.real ∈ Γ.carrier) := by
  ext q
  have hhat : (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).hat
      (lowerAnchor Φ anchor hp Γ) q =
        if q.real ∈ Γ.carrier then Φ.hat anchor q else 0 :=
    (congrFun ((splitWeights Φ anchor (Φ.faceSelector anchor Γ)).decomposition_hat hp
      (lowerAnchor Φ anchor hp Γ)) q).trans (face_hat_lower_anchor Φ anchor hp Γ q)
  apply ((decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).liftedSupport_spec _ q).trans
  change (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).hat
    (lowerAnchor Φ anchor hp Γ) q ≠ 0 ↔ _
  rw [hhat]
  by_cases hqΓ : q.real ∈ Γ.carrier
  · rw [ite_eq_left hqΓ]
    exact ⟨fun hq ↦ Finset.mem_filter.mpr ⟨(Φ.liftedSupport_spec anchor q).mpr hq, hqΓ⟩,
      fun hq ↦ (Φ.liftedSupport_spec anchor q).mp (Finset.mem_filter.mp hq).1⟩
  · rw [ite_eq_right hqΓ]
    exact ⟨fun h ↦ (h rfl).elim, fun h ↦ (hqΓ (Finset.mem_filter.mp h).2).elim⟩

open Classical in
/-- The new lower anchor polytope is exactly the selected old face. -/
theorem lowerAnchor_polytope (Γ : (Φ.flag.polytope anchor).Face) :
    ((decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).flag.polytope
      (lowerAnchor Φ anchor hp Γ)).carrier = Γ.carrier := by
  rw [(decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).polytope_eq_liftedSupport,
    lowerAnchor_liftedSupport]
  exact (Φ.face_eq_convexHull_liftedSupport anchor Γ).symm

open Classical in
/-- Splitting all atoms over the face into the lower layer realizes that
face at the unchanged upper anchor. -/
theorem face_isRealized (Γ : (Φ.flag.polytope anchor).Face) :
    (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).IsRealizedFace
      (upper Φ anchor (Φ.faceSelector anchor Γ) hp anchor)
      (upperFace Φ anchor (Φ.faceSelector anchor Γ) hp anchor Γ) := by
  apply (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).isRealizedFace_of_local_bases
    _ _ (lowerAnchor Φ anchor hp Γ) (lowerAnchor_le_upper Φ anchor hp Γ)
  · intro q hq h hface
    have hzero := face_local_layer_zero Φ anchor hp Γ q hq h hface
    change q.base.1.1.1 ≤ anchor ∧ q.base.1.1.2 ≤ (0 : Fin 2)
    exact ⟨h.1, by rw [hzero]⟩
  · intro q hq
    change (Φ.flag.transition (le_refl anchor)).real q ∈ Γ.carrier
    rw [Φ.flag.transition_refl]
    exact (lowerAnchor_polytope Φ anchor hp Γ).subset hq

end FaceRefinement

open Classical in
/-- Splitting the atoms over a chosen face realizes it at an upper copy of
the anchor. This operation retains every old upper fibre and all mass, uses
at most twice as many nodes, and preserves the old coordinate bounds. -/
theorem face_refinement_lemma (Φ : FlagDecomposition p d f) (hp : Odd p)
    (anchor : Φ.flag.Node) (Γ : (Φ.flag.polytope anchor).Face)
    {K : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K) :
    let selected := Φ.faceSelector anchor Γ
    let Ψ := FaceRefinement.decomposition Φ anchor selected hp
    Ψ.retainedWeight = Φ.retainedWeight ∧
    Ψ.retainedMass = Φ.retainedMass ∧
    @Fintype.card Ψ.flag.Node Ψ.flag.nodeFintype ≤ 2 * Fintype.card Φ.flag.Node ∧
    Ψ.IsKBounded (fun x ↦ K (FaceRefinement.projection Φ anchor x.1)) ∧
    (∀ x, Ψ.cumulativeWeight (FaceRefinement.upper Φ anchor selected hp x) =
      Φ.cumulativeWeight x) ∧
    (∀ x, (Ψ.flag.polytope (FaceRefinement.upper Φ anchor selected hp x)).carrier =
      (Φ.flag.polytope x).carrier) ∧
    (Ψ.flag.polytope (FaceRefinement.lowerAnchor Φ anchor hp Γ)).carrier = Γ.carrier ∧
    Ψ.IsRealizedFace (FaceRefinement.upper Φ anchor selected hp anchor)
      (FaceRefinement.upperFace Φ anchor selected hp anchor Γ) ∧
    (∀ x t δ, Φ.IsCompleteElement x t δ →
      Ψ.IsCompleteElement (FaceRefinement.upper Φ anchor selected hp x) t δ) ∧
    (∀ x (Δ : (Φ.flag.polytope x).Face), Φ.IsRealizedFace x Δ →
      Ψ.IsRealizedFace (FaceRefinement.upper Φ anchor selected hp x)
        (FaceRefinement.upperFace Φ anchor selected hp x Δ)) := by
  exact ⟨FaceRefinement.retainedWeight Φ anchor _ hp,
    FaceRefinement.retainedMass Φ anchor _ hp,
    FaceRefinement.card_le Φ anchor _ hp,
    FaceRefinement.isKBounded Φ anchor _ hp hK,
    FaceRefinement.upper_cumulativeWeight Φ anchor _ hp,
    FaceRefinement.upper_polytope Φ anchor _ hp,
    FaceRefinement.lowerAnchor_polytope Φ anchor hp Γ,
    FaceRefinement.face_isRealized Φ anchor hp Γ,
    FaceRefinement.upper_isCompleteElement Φ anchor _ hp,
    FaceRefinement.upper_isRealizedFace Φ anchor _ hp⟩

end FlagDecomposition

end EGZ
