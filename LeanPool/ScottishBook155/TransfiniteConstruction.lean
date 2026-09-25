/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.PrefixGlue
public import LeanPool.ScottishBook155.BookkeepingSchedule
public import LeanPool.ScottishBook155.FinalChainAssembly
public import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData


/-!
# Unconditional transfinite construction for Claim 14

This file builds the coherent protected chain by well-founded recursion on the
fixed regular recursion cardinal.  Successor stages process the bookkeeping
schedule, limit stages glue and complete the earlier prefixes, and the resulting
scheduled chain supplies the unconditional witness for `Claim14`.
-/

@[expose] public section

namespace ScottishBook155

local notation "RI" => RecursionIndexZero

@[simp]
theorem successorSegmentWithTop_apply_top (j : RI) :
    successorSegmentWithTop j (not_isMax j)
        ⟨Order.succ j, show Order.succ j ≤ Order.succ j from le_rfl⟩ = ⊤ := by
  change successorSegmentWithTop j (not_isMax j)
      (⊤ : Set.Iic (Order.succ j)) = ⊤
  exact map_top _

namespace ProtectedStage

theorem map_castSourcePoint {r : ℝ} {A B : ProtectedStage.{0} r}
    (h : A = B) (x : A.source) :
    B.map (castSourcePoint h x) = castTargetPoint h (A.map x) := by
  subst B
  rfl

/-- The linear isometry transporting source points along equality of protected stages. -/
noncomputable def castSourceLinearIsometry {r : ℝ}
    {A B : ProtectedStage.{0} r} (h : A = B) :
    A.source →ₗᵢ[ℝ] B.source := by
  subst B
  exact LinearIsometry.id

/-- The linear isometry transporting target points along equality of protected stages. -/
noncomputable def castTargetLinearIsometry {r : ℝ}
    {A B : ProtectedStage.{0} r} (h : A = B) :
    A.target →ₗᵢ[ℝ] B.target := by
  subst B
  exact LinearIsometry.id

theorem castSourceLinearIsometry_apply {r : ℝ}
    {A B : ProtectedStage.{0} r} (h : A = B) (x : A.source) :
    castSourceLinearIsometry h x = castSourcePoint h x := by
  subst B
  rfl

theorem castTargetLinearIsometry_apply {r : ℝ}
    {A B : ProtectedStage.{0} r} (h : A = B) (x : A.target) :
    castTargetLinearIsometry h x = castTargetPoint h x := by
  subst B
  rfl

theorem cast_bentSeed_compatible
    (A : ProtectedStage.{0} ((1 : ℝ) / 2)) (h : A = bentSeedStage)
    (t : ℝ) :
    A.map (castSourceLinearIsometry h.symm t) =
      castTargetLinearIsometry h.symm (bentMapL1 t) := by
  subst A
  rfl

end ProtectedStage

namespace ProtectedChain

theorem reindex_target_embed_of_eq {ι κ : Type} [LinearOrder ι]
    [LinearOrder κ] {r L : ℝ} (C : ProtectedChain (ι := ι) r L)
    (e : κ ↪o ι) (a b : κ) (hab : a ≤ b) (a' b' : ι)
    (ha : e a = a') (hb : e b = b') (hab' : a' ≤ b')
    (x : ((C.reindex e).stage a).target) :
    ProtectedStage.castTargetPoint (congrArg C.stage hb)
        ((C.reindex e).targetSystem.embed a b hab x) =
      C.targetSystem.embed a' b' hab'
        (ProtectedStage.castTargetPoint (congrArg C.stage ha) x) := by
  subst a'
  subst b'
  exact (ProtectedStage.castTargetPoint_rfl _ _).trans
    (congrArg (C.targetSystem.embed (e a) (e b) (e.monotone hab))
      (ProtectedStage.castTargetPoint_rfl _ x).symm)

end ProtectedChain

namespace ProtectedPrefix

/-- Embed the point named by a requirement whose scheduled transition is
`j` into the top target of a prefix ending at `j`. -/
noncomputable def pointOfScheduledRequirement {j : RI}
    (P : ProtectedPrefix j)
    (q : {p : RI × RI // bookkeepingSchedule p = j}) :
    P.topStage.target := by
  have hqj : q.1.1 ≤ j :=
    (bookkeepingSchedule_gt q.1).le.trans q.2.le
  exact P.chain.targetSystem.embed
    ⟨q.1.1, hqj⟩ ⟨j, show j ≤ j from le_rfl⟩ hqj
    (P.enumerate ⟨q.1.1, hqj⟩ q.1.2)

/-- The target point processed at the transition out of `j`. -/
noncomputable def scheduledPoint (j : RI) (P : ProtectedPrefix j) :
    P.topStage.target := by
  classical
  by_cases h : ∃ p : RI × RI, bookkeepingSchedule p = j
  · exact P.pointOfScheduledRequirement
      ⟨Classical.choose h, Classical.choose_spec h⟩
  · exact P.topStage.map 0

theorem scheduledPoint_of_schedule (p : RI × RI)
    (P : ProtectedPrefix (bookkeepingSchedule p)) :
    P.scheduledPoint (bookkeepingSchedule p) =
      P.chain.targetSystem.embed
        ⟨p.1, (bookkeepingSchedule_gt p).le⟩
        ⟨bookkeepingSchedule p,
          show bookkeepingSchedule p ≤ bookkeepingSchedule p from le_rfl⟩
        (bookkeepingSchedule_gt p).le
        (P.enumerate ⟨p.1, (bookkeepingSchedule_gt p).le⟩ p.2) := by
  unfold scheduledPoint
  split
  · rename_i h
    let qh : {q : RI × RI // bookkeepingSchedule q = bookkeepingSchedule p} :=
      ⟨Classical.choose h, Classical.choose_spec h⟩
    let ph : {q : RI × RI // bookkeepingSchedule q = bookkeepingSchedule p} :=
      ⟨p, rfl⟩
    have hqp : qh = ph := by
      apply Subtype.ext
      exact bookkeepingSchedule_injective
        (qh.2.trans ph.2.symm)
    change P.pointOfScheduledRequirement qh =
      P.pointOfScheduledRequirement ph
    rw [hqp]
  · rename_i h
    exact False.elim (h ⟨p, rfl⟩)

theorem linkOfRestriction_targetEmbedding_enumerate {i j : RI}
    (Pi : ProtectedPrefix i) (Pj : ProtectedPrefix j) (hij : i ≤ j)
    (hchain : (Pj.restriction hij).chain = Pi.chain) (ξ : RI) :
    (Pi.linkOfRestriction Pj hij hchain).targetEmbedding
        (Pi.enumerate ⟨i, show i ≤ i from le_rfl⟩ ξ) =
      Pj.chain.targetSystem.embed
        ⟨i, hij⟩ ⟨j, show j ≤ j from le_rfl⟩ hij
        (Pj.enumerate ⟨i, hij⟩ ξ) := by
  have hpref : Pj.restriction hij = Pi := ProtectedPrefix.ext hchain
  subst Pi
  rfl

theorem linkOfRestriction_targetEmbedding_transportTarget {i j : RI}
    (Pi : ProtectedPrefix i) (Pj Qj : ProtectedPrefix j) (hij : i ≤ j)
    (hPj : (Pj.restriction hij).chain = Pi.chain)
    (hQj : (Qj.restriction hij).chain = Pi.chain) (h : Pj = Qj)
    (x : Pi.topStage.target) :
    ProtectedStage.castTargetPoint (congrArg ProtectedPrefix.topStage h)
        ((Pi.linkOfRestriction Pj hij hPj).targetEmbedding x) =
      (Pi.linkOfRestriction Qj hij hQj).targetEmbedding x := by
  subst Qj
  simp

theorem successor_topStage {j : RI} (P : ProtectedPrefix j)
    (y : P.topStage.target) :
    (P.successor y).topStage = (scheduledSuccessor P.topStage y).next := by
  unfold successor topStage
  dsimp
  change P.chain.appendStage (scheduledSuccessor P.topStage y)
      (successorSegmentWithTop j (not_isMax j)
        ⟨Order.succ j,
          show Order.succ j ≤ Order.succ j from le_rfl⟩) = _
  rw [successorSegmentWithTop_apply_top]
  rfl

theorem successor_link_targetEmbedding {j : RI} (P : ProtectedPrefix j)
    (y : P.topStage.target) :
    (P.linkOfRestriction (P.successor y) (Order.le_succ j)
      (congrArg ProtectedPrefix.chain (P.successor_restriction y))).targetEmbedding y =
      ProtectedStage.castTargetPoint (P.successor_topStage y).symm
        ((scheduledSuccessor P.topStage y).targetEmbedding y) := by
  let T := scheduledSuccessor P.topStage y
  let Cplus := P.chain.append T
  let e := (successorSegmentWithTop j (not_isMax j)).toOrderEmbedding
  let a : Set.Iic (Order.succ j) := ⟨j, Order.le_succ j⟩
  let b : Set.Iic (Order.succ j) :=
    ⟨Order.succ j, show Order.succ j ≤ Order.succ j from le_rfl⟩
  let a' : WithTop (Set.Iic j) :=
    (⟨j, show j ≤ j from le_rfl⟩ : Set.Iic j)
  let b' : WithTop (Set.Iic j) := ⊤
  have ha : e a = a' := by
    exact successorSegmentWithTop_apply_old j (not_isMax j)
      ⟨j, show j ≤ j from le_rfl⟩
  have hb : e b = b' := by
    exact successorSegmentWithTop_apply_top j
  let Q := P.successor y
  let hchain : (Q.restriction (Order.le_succ j)).chain = P.chain :=
    congrArg ProtectedPrefix.chain (P.successor_restriction y)
  let hs : Q.chain.stage a = P.topStage :=
    congrArg
      (fun C : ProtectedChain (ι := Set.Iic j) ((1 : ℝ) / 2) 1 =>
        C.stage ⟨j, show j ≤ j from le_rfl⟩) hchain
  refine (ProtectedLink.castSource_targetEmbedding hs
    (Q.chain.link a b (Order.le_succ j)) y).trans ?_
  change Q.chain.targetSystem.embed a b (Order.le_succ j)
      (ProtectedStage.castTargetPoint hs.symm y) = _
  have hQ : Q.chain = Cplus.reindex e := by
    rfl
  let hs0 : (Cplus.reindex e).stage a = P.topStage := hs
  let htop0 : (Cplus.reindex e).stage b = T.next :=
    congrArg Cplus.stage hb
  let x0 : ((Cplus.reindex e).stage a).target :=
    ProtectedStage.castTargetPoint hs0.symm y
  change (Cplus.reindex e).targetSystem.embed a b (Order.le_succ j)
      x0 =
    ProtectedStage.castTargetPoint htop0.symm (T.targetEmbedding y)
  have ht := ProtectedChain.reindex_target_embed_of_eq Cplus e a b
    (Order.le_succ j) a' b' ha hb le_top
    x0
  have haeq : congrArg Cplus.stage ha = hs0 :=
    Subsingleton.elim _ _
  have hcast : ProtectedStage.castTargetPoint (congrArg Cplus.stage ha)
      x0 = y := by
    dsimp [x0]
    rw [haeq]
    exact ProtectedStage.castTargetPoint_apply_symm hs0 y
  rw [hcast] at ht
  have htail : Cplus.targetSystem.embed a' b' le_top y =
      T.targetEmbedding y := by
    change T.targetEmbedding
        (P.chain.targetSystem.embed
          ⟨j, show j ≤ j from le_rfl⟩
          ⟨j, show j ≤ j from le_rfl⟩ le_rfl y) = T.targetEmbedding y
    rw [P.chain.targetSystem.embed_refl]
  have htfinal := ht.trans htail
  calc
    (Cplus.reindex e).targetSystem.embed a b (Order.le_succ j) x0 =
        ProtectedStage.castTargetPoint htop0.symm
          (ProtectedStage.castTargetPoint htop0
            ((Cplus.reindex e).targetSystem.embed a b
              (Order.le_succ j) x0)) := by
      symm
      exact ProtectedStage.castTargetPoint_symm_apply htop0 _
    _ = ProtectedStage.castTargetPoint htop0.symm (T.targetEmbedding y) := by
      exact congrArg (ProtectedStage.castTargetPoint htop0.symm) htfinal

theorem successor_link_hits {j : RI} (P : ProtectedPrefix j)
    (y : P.topStage.target) :
    ∃ x : (P.successor y).topStage.source,
      (P.successor y).topStage.map x =
        (P.linkOfRestriction (P.successor y) (Order.le_succ j)
          (congrArg ProtectedPrefix.chain
            (P.successor_restriction y))).targetEmbedding y := by
  obtain ⟨x, hx⟩ := scheduledSuccessor_hits P.topStage y
  let htop := P.successor_topStage y
  refine ⟨ProtectedStage.castSourcePoint htop.symm x, ?_⟩
  rw [ProtectedStage.map_castSourcePoint htop.symm x, hx]
  exact (P.successor_link_targetEmbedding y).symm

end ProtectedPrefix

open CategoryTheory Opposite

/-- The inverse system of protected prefixes under restriction. -/
noncomputable def protectedPrefixFunctor : RIᵒᵖ ⥤ Type 1 where
  obj j := ProtectedPrefix j.unop
  map {X Y} f := ↾(fun P : ProtectedPrefix X.unop =>
    P.restriction f.unop.le)
  map_id j := by
    ext P
    exact P.restriction_refl
  map_comp f g := by
    ext P
    exact ProtectedPrefix.restriction_trans P g.unop.le f.unop.le

/-- A compatible family of prefixes extracted from a section below a limit
index. -/
noncomputable def compatiblePrefixFamilyOfSection (j : RI)
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙
      protectedPrefixFunctor).sections) : CompatiblePrefixFamily j where
  item i := x.val (op i)
  coherent i k hik := by
    have hx := x.property ((CategoryTheory.homOfLE hik).op)
    change ((x.val (op k)).restriction hik) = x.val (op i) at hx
    exact congrArg ProtectedPrefix.chain hx

theorem CompatiblePrefixFamily.openChain_source_mk_le {j : RI}
    (F : CompatiblePrefixFamily j) (i : Set.Iio j) :
    Cardinal.mk (F.openChain.stage i).source ≤ stageCardinal := by
  exact (F.item i).source_mk_le
    ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩

theorem CompatiblePrefixFamily.openChain_target_mk_le {j : RI}
    (F : CompatiblePrefixFamily j) (i : Set.Iio j) :
    Cardinal.mk (F.openChain.stage i).target ≤ stageCardinal := by
  exact (F.item i).target_mk_le
    ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩

/-- The completed prefix attached to a compatible section at a limit index. -/
noncomputable def limitPrefix (j : RI) (hj : Order.IsSuccLimit j)
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙
      protectedPrefixFunctor).sections) : ProtectedPrefix j :=
  let F := compatiblePrefixFamilyOfSection j x
  ProtectedPrefix.ofLimit j hj F.openChain F.openChain_source_mk_le
    F.openChain_target_mk_le

theorem limitPrefix_restriction (j : RI) (hj : Order.IsSuccLimit j)
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙
      protectedPrefixFunctor).sections) (i : RI) (hi : i < j) :
    (limitPrefix j hj x).restriction hi.le = x.val (op ⟨i, hi⟩) := by
  let F := compatiblePrefixFamilyOfSection j x
  change (ProtectedPrefix.ofLimit j hj F.openChain
      F.openChain_source_mk_le F.openChain_target_mk_le).restriction hi.le = _
  exact ProtectedPrefix.ofLimit_restriction hj F
    F.openChain_source_mk_le F.openChain_target_mk_le ⟨i, hi⟩

/-- Successor and limit lifts for the inverse system of bounded prefixes. -/
noncomputable def protectedPrefixInductionData :
    protectedPrefixFunctor.WellOrderInductionData where
  succ j _ P := P.successor (P.scheduledPoint j)
  map_succ j _ P := by
    change (P.successor (P.scheduledPoint j)).restriction
      (Order.le_succ j) = P
    exact P.successor_restriction (P.scheduledPoint j)
  lift j hj x := limitPrefix j hj x
  map_lift j hj x i hi := by
    change (limitPrefix j hj x).restriction hi.le = x.val (op ⟨i, hi⟩)
    exact limitPrefix_restriction j hj x i hi

/-- The bent seed prefix at the least recursion index. -/
noncomputable def seedPrefix : ProtectedPrefix (⊥ : RI) :=
  ProtectedPrefix.ofMin ⊥ isMin_bot

/-- The coherent transfinite section selected from the successor and limit
clauses. -/
noncomputable def protectedPrefixSection : protectedPrefixFunctor.sections :=
  protectedPrefixInductionData.sectionsMk seedPrefix

/-- The canonical bounded prefix ending at `j`. -/
noncomputable def canonicalPrefix (j : RI) : ProtectedPrefix j :=
  protectedPrefixSection.val (op j)

theorem canonicalPrefix_restriction {i j : RI} (hij : i ≤ j) :
    (canonicalPrefix j).restriction hij = canonicalPrefix i := by
  have h := protectedPrefixSection.property
    ((CategoryTheory.homOfLE hij).op)
  change (canonicalPrefix j).restriction hij = canonicalPrefix i at h
  exact h

theorem canonicalPrefix_bot : canonicalPrefix (⊥ : RI) = seedPrefix := by
  exact protectedPrefixInductionData.sectionsMk_val_op_bot seedPrefix

theorem canonicalPrefix_succ (j : RI) :
    canonicalPrefix (Order.succ j) =
      (canonicalPrefix j).successor
        ((canonicalPrefix j).scheduledPoint j) := by
  let e : protectedPrefixInductionData.Extension seedPrefix (Order.succ j) :=
    show protectedPrefixInductionData.Extension
      (show protectedPrefixFunctor.obj (op ⊥) from seedPrefix) (Order.succ j) from default
  have h := e.map_succ j
    (Order.lt_succ_of_not_isMax (not_isMax j))
  change e.val =
      (e.val.restriction (Order.le_succ j)).successor
        ((e.val.restriction (Order.le_succ j)).scheduledPoint j) at h
  have h' : canonicalPrefix (Order.succ j) =
      ((canonicalPrefix (Order.succ j)).restriction (Order.le_succ j)).successor
        (((canonicalPrefix (Order.succ j)).restriction
          (Order.le_succ j)).scheduledPoint j) := by
    simpa [e, canonicalPrefix, protectedPrefixSection,
      protectedPrefixFunctor,
      CategoryTheory.Functor.WellOrderInductionData.sectionsMk] using h
  rw [h', canonicalPrefix_restriction]

/-- A coherent family of closed prefixes over the whole recursion order. -/
structure CompatiblePrefixSequence where
  /-- The closed protected prefix at each index of the complete recursion order. -/
  item : ∀ j : RI, ProtectedPrefix j
  coherent : ∀ (_i _j : RI) (hij : _i ≤ _j),
    ((item _j).restriction hij).chain = (item _i).chain

/-- The canonical transfinite section as a coherent prefix sequence. -/
noncomputable def canonicalPrefixSequence : CompatiblePrefixSequence where
  item := canonicalPrefix
  coherent _ _ hij := congrArg ProtectedPrefix.chain
    (canonicalPrefix_restriction hij)

namespace CompatiblePrefixSequence

variable (G : CompatiblePrefixSequence)

/-- Restrict a global prefix sequence to indices below `j`. -/
noncomputable def below (j : RI) : CompatiblePrefixFamily j where
  item i := G.item i.1
  coherent i k hik := G.coherent i.1 k.1 hik

/-- The top protected stage of the prefix at the specified recursion index. -/
abbrev stage (i : RI) : ProtectedStage.{0} ((1 : ℝ) / 2) :=
  (G.item i).topStage

/-- The protected link between two stages, obtained from coherence of their closed
prefixes. -/
noncomputable def link (i j : RI) (hij : i ≤ j) :
    ProtectedLink (G.stage i) (G.stage j) 1 :=
  (G.item i).linkOfRestriction (G.item j) hij (G.coherent i j hij)

theorem below_link (j : RI) (i k : Set.Iio j) (hik : i ≤ k) :
    (G.below j).link i k hik = G.link i.1 k.1 hik := by
  rfl

theorem sourceEmbedding_refl (i : RI) (x : (G.stage i).source) :
    (G.link i i le_rfl).sourceEmbedding x = x := by
  let F := G.below (Order.succ i)
  let ii : Set.Iio (Order.succ i) :=
    ⟨i, Order.lt_succ_of_not_isMax (not_isMax i)⟩
  have h := F.openChain.sourceSystem.embed_refl ii x
  change (F.link ii ii le_rfl).sourceEmbedding x = x at h
  have hlink : F.link ii ii le_rfl = G.link i i le_rfl := by
    rfl
  rw [hlink] at h
  exact h

theorem targetEmbedding_refl (i : RI) (x : (G.stage i).target) :
    (G.link i i le_rfl).targetEmbedding x = x := by
  let F := G.below (Order.succ i)
  let ii : Set.Iio (Order.succ i) :=
    ⟨i, Order.lt_succ_of_not_isMax (not_isMax i)⟩
  have h := F.openChain.targetSystem.embed_refl ii x
  change (F.link ii ii le_rfl).targetEmbedding x = x at h
  rw [G.below_link (Order.succ i) ii ii le_rfl] at h
  exact h

theorem sourceEmbedding_trans (i k m : RI) (hik : i ≤ k) (hkm : k ≤ m)
    (x : (G.stage i).source) :
    (G.link k m hkm).sourceEmbedding
        ((G.link i k hik).sourceEmbedding x) =
      (G.link i m (hik.trans hkm)).sourceEmbedding x := by
  let F := G.below (Order.succ m)
  let mm : Set.Iio (Order.succ m) :=
    ⟨m, Order.lt_succ_of_not_isMax (not_isMax m)⟩
  let kk : Set.Iio (Order.succ m) :=
    ⟨k, hkm.trans_lt mm.2⟩
  let ii : Set.Iio (Order.succ m) :=
    ⟨i, (hik.trans hkm).trans_lt mm.2⟩
  have h := F.openChain.sourceSystem.embed_trans ii kk mm hik hkm x
  change (F.link kk mm hkm).sourceEmbedding
      ((F.link ii kk hik).sourceEmbedding x) =
    (F.link ii mm (hik.trans hkm)).sourceEmbedding x at h
  rw [G.below_link (Order.succ m) kk mm hkm,
    G.below_link (Order.succ m) ii kk hik,
    G.below_link (Order.succ m) ii mm (hik.trans hkm)] at h
  exact h

theorem targetEmbedding_trans (i k m : RI) (hik : i ≤ k) (hkm : k ≤ m)
    (x : (G.stage i).target) :
    (G.link k m hkm).targetEmbedding
        ((G.link i k hik).targetEmbedding x) =
      (G.link i m (hik.trans hkm)).targetEmbedding x := by
  let F := G.below (Order.succ m)
  let mm : Set.Iio (Order.succ m) :=
    ⟨m, Order.lt_succ_of_not_isMax (not_isMax m)⟩
  let kk : Set.Iio (Order.succ m) :=
    ⟨k, hkm.trans_lt mm.2⟩
  let ii : Set.Iio (Order.succ m) :=
    ⟨i, (hik.trans hkm).trans_lt mm.2⟩
  have h := F.openChain.targetSystem.embed_trans ii kk mm hik hkm x
  change (F.link kk mm hkm).targetEmbedding
      ((F.link ii kk hik).targetEmbedding x) =
    (F.link ii mm (hik.trans hkm)).targetEmbedding x at h
  rw [G.below_link (Order.succ m) kk mm hkm,
    G.below_link (Order.succ m) ii kk hik,
    G.below_link (Order.succ m) ii mm (hik.trans hkm)] at h
  exact h

theorem sourceProjection_embed (a i j : RI) (hai : a ≤ i) (hij : i ≤ j)
    (x : (G.stage i).source) :
    (G.link a j (hai.trans hij)).sourceProjection
        ((G.link i j hij).sourceEmbedding x) =
      (G.link a i hai).sourceProjection x := by
  let F := G.below (Order.succ j)
  let jj : Set.Iio (Order.succ j) :=
    ⟨j, Order.lt_succ_of_not_isMax (not_isMax j)⟩
  let ii : Set.Iio (Order.succ j) := ⟨i, hij.trans_lt jj.2⟩
  let aa : Set.Iio (Order.succ j) :=
    ⟨a, (hai.trans hij).trans_lt jj.2⟩
  have h := F.openChain.sourceSystem.project_embed aa ii jj hai hij x
  change (F.link aa jj (hai.trans hij)).sourceProjection
      ((F.link ii jj hij).sourceEmbedding x) =
    (F.link aa ii hai).sourceProjection x at h
  rw [G.below_link (Order.succ j) aa jj (hai.trans hij),
    G.below_link (Order.succ j) ii jj hij,
    G.below_link (Order.succ j) aa ii hai] at h
  exact h

theorem targetProjection_embed (a i j : RI) (hai : a ≤ i) (hij : i ≤ j)
    (x : (G.stage i).target) :
    (G.link a j (hai.trans hij)).targetProjection
        ((G.link i j hij).targetEmbedding x) =
      (G.link a i hai).targetProjection x := by
  let F := G.below (Order.succ j)
  let jj : Set.Iio (Order.succ j) :=
    ⟨j, Order.lt_succ_of_not_isMax (not_isMax j)⟩
  let ii : Set.Iio (Order.succ j) := ⟨i, hij.trans_lt jj.2⟩
  let aa : Set.Iio (Order.succ j) :=
    ⟨a, (hai.trans hij).trans_lt jj.2⟩
  have h := F.openChain.targetSystem.project_embed aa ii jj hai hij x
  change (F.link aa jj (hai.trans hij)).targetProjection
      ((F.link ii jj hij).targetEmbedding x) =
    (F.link aa ii hai).targetProjection x at h
  rw [G.below_link (Order.succ j) aa jj (hai.trans hij),
    G.below_link (Order.succ j) ii jj hij,
    G.below_link (Order.succ j) aa ii hai] at h
  exact h

/-- Glue a coherent sequence of closed prefixes into one protected chain on
the whole recursion order. -/
noncomputable def toProtectedChain :
    ProtectedChain (ι := RI) ((1 : ℝ) / 2) 1 where
  stage := G.stage
  sourceSystem := {
    embed := fun i j hij => (G.link i j hij).sourceEmbedding
    project := fun i j hij => (G.link i j hij).sourceProjection
    embed_refl := G.sourceEmbedding_refl
    embed_trans := G.sourceEmbedding_trans
    project_embed := G.sourceProjection_embed
    project_retracts := fun i j hij => (G.link i j hij).sourceRetracts
    project_contractive := fun i j hij => (G.link i j hij).sourceContractive }
  targetSystem := {
    embed := fun i j hij => (G.link i j hij).targetEmbedding
    project := fun i j hij => (G.link i j hij).targetProjection
    embed_refl := G.targetEmbedding_refl
    embed_trans := G.targetEmbedding_trans
    project_embed := G.targetProjection_embed
    project_retracts := fun i j hij => (G.link i j hij).targetRetracts
    project_contractive := fun i j hij => (G.link i j hij).targetContractive }
  compatible := fun i j hij => (G.link i j hij).compatible
  recovers := fun i j hij => (G.link i j hij).recovers

end CompatiblePrefixSequence

/-- The global coherent protected chain produced by the transfinite section. -/
noncomputable def canonicalProtectedChain :
    ProtectedChain (ι := RI) ((1 : ℝ) / 2) 1 :=
  canonicalPrefixSequence.toProtectedChain

/-- The fixed enumeration of the target at each global stage. -/
noncomputable def canonicalEnumerate (i : RI) :
    RI → (canonicalProtectedChain.stage i).target :=
  (canonicalPrefix i).enumerate
    ⟨i, show i ≤ i from le_rfl⟩

theorem canonicalEnumerate_surjective (i : RI) :
    Function.Surjective (canonicalEnumerate i) :=
  (canonicalPrefix i).enumerate_surjective
    ⟨i, show i ≤ i from le_rfl⟩

theorem canonical_stage_bot :
    canonicalProtectedChain.stage (⊥ : RI) = bentSeedStage := by
  have h := congrArg ProtectedPrefix.topStage canonicalPrefix_bot
  simpa [canonicalProtectedChain, canonicalPrefixSequence,
    CompatiblePrefixSequence.toProtectedChain, seedPrefix,
    ProtectedPrefix.ofMin, constantProtectedChain] using h

theorem canonical_scheduledPoint_eq_link (p : RI × RI) :
    (canonicalPrefix (bookkeepingSchedule p)).scheduledPoint
        (bookkeepingSchedule p) =
      (canonicalPrefixSequence.link p.1 (bookkeepingSchedule p)
        (bookkeepingSchedule_gt p).le).targetEmbedding
        (canonicalEnumerate p.1 p.2) := by
  let Pi := canonicalPrefix p.1
  let Pj := canonicalPrefix (bookkeepingSchedule p)
  have hs := Pj.scheduledPoint_of_schedule p
  have hl := Pi.linkOfRestriction_targetEmbedding_enumerate Pj
    (bookkeepingSchedule_gt p).le
    (canonicalPrefixSequence.coherent p.1 (bookkeepingSchedule p)
      (bookkeepingSchedule_gt p).le) p.2
  exact hs.trans hl.symm

theorem canonical_processed (i ξ : RI) :
    ∃ x : (canonicalProtectedChain.stage
        (bookkeepingReceivingStage (i, ξ))).source,
      (canonicalProtectedChain.stage
          (bookkeepingReceivingStage (i, ξ))).map x =
        canonicalProtectedChain.targetSystem.embed i
          (bookkeepingReceivingStage (i, ξ))
          (bookkeepingReceivingStage_gt (i, ξ)).le
          (canonicalEnumerate i ξ) := by
  let p : RI × RI := (i, ξ)
  let j := bookkeepingSchedule p
  let k := Order.succ j
  change ∃ x : (canonicalPrefix k).topStage.source,
    (canonicalPrefix k).topStage.map x =
      (canonicalPrefixSequence.link i k
        (bookkeepingReceivingStage_gt p).le).targetEmbedding
        (canonicalEnumerate i ξ)
  let P := canonicalPrefix j
  let y := P.scheduledPoint j
  let Q := P.successor y
  let Ck := canonicalPrefix k
  have hcanon : Ck = Q := by
    exact canonicalPrefix_succ j
  let hstage : Ck.topStage = Q.topStage :=
    congrArg ProtectedPrefix.topStage hcanon
  obtain ⟨xQ, hxQ⟩ := P.successor_link_hits y
  refine ⟨ProtectedStage.castSourcePoint hstage.symm xQ, ?_⟩
  rw [ProtectedStage.map_castSourcePoint hstage.symm xQ, hxQ]
  have htransport := P.linkOfRestriction_targetEmbedding_transportTarget
    Ck Q (Order.le_succ j)
    (canonicalPrefixSequence.coherent j k (Order.le_succ j))
    (congrArg ProtectedPrefix.chain (P.successor_restriction y))
    hcanon y
  have hback :
      ProtectedStage.castTargetPoint hstage.symm
          ((P.linkOfRestriction Q (Order.le_succ j)
            (congrArg ProtectedPrefix.chain
              (P.successor_restriction y))).targetEmbedding y) =
        (canonicalPrefixSequence.link j k
          (Order.le_succ j)).targetEmbedding y := by
    have hh := congrArg (ProtectedStage.castTargetPoint hstage.symm) htransport
    rw [ProtectedStage.castTargetPoint_symm_apply hstage] at hh
    exact hh.symm
  rw [hback]
  have hij : i ≤ j := (bookkeepingSchedule_gt p).le
  have hjk : j ≤ k := Order.le_succ j
  have hy := canonical_scheduledPoint_eq_link p
  change y = (canonicalPrefixSequence.link i j hij).targetEmbedding
    (canonicalEnumerate i ξ) at hy
  rw [hy]
  exact canonicalPrefixSequence.targetEmbedding_trans i j k hij hjk
    (canonicalEnumerate i ξ)

/-- The unconditional scheduled chain required by the final direct-limit
assembly. -/
noncomputable def canonicalScheduledProtectedChain : ScheduledProtectedChain where
  chain := canonicalProtectedChain
  enumerate := canonicalEnumerate
  enumerate_surjective := canonicalEnumerate_surjective
  processed := canonical_processed
  seedIndex := ⊥
  seedSource := ProtectedStage.castSourceLinearIsometry
    canonical_stage_bot.symm
  seedTarget := ProtectedStage.castTargetLinearIsometry
    canonical_stage_bot.symm
  seedCompatible := by
    intro t
    exact ProtectedStage.cast_bentSeed_compatible
      (canonicalProtectedChain.stage (⊥ : RI)) canonical_stage_bot t

/-- Canonical claim 14, with the transfinite recursion discharged. -/
theorem claim14 : Claim14.{0} :=
  canonicalScheduledProtectedChain.claim14

end ScottishBook155
