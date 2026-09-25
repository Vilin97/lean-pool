/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.EnumeratedStage
public import LeanPool.ScottishBook155.ProtectedChainReindex
public import LeanPool.ScottishBook155.ProtectedChainSingleton
public import LeanPool.ScottishBook155.ProtectedChainSuccessor
public import LeanPool.ScottishBook155.InitialSegmentOrder
public import LeanPool.ScottishBook155.ProtectedChainLimitAppend
public import LeanPool.ScottishBook155.LimitCardinal


/-!
# Cardinal-controlled protected prefixes
-/

@[expose] public section

namespace ScottishBook155

local notation "RI" => RecursionIndexZero

/-- A coherent chain on a closed initial segment, with the cardinal bounds
needed to enumerate every target stage. -/
structure ProtectedPrefix (j : RI) where
  /-- The protected chain on the closed initial segment through the prefix index. -/
  chain : ProtectedChain (ι := Set.Iic j) ((1 : ℝ) / 2) 1
  source_mk_le : ∀ i, Cardinal.mk (chain.stage i).source ≤ stageCardinal
  target_mk_le : ∀ i, Cardinal.mk (chain.stage i).target ≤ stageCardinal

namespace ProtectedPrefix

variable {j : RI} (P : ProtectedPrefix j)

/-- A bounded protected prefix is determined by its coherent chain; the two
cardinal bounds are propositions. -/
theorem ext {P Q : ProtectedPrefix j} (h : P.chain = Q.chain) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- The top stage of a prefix. -/
abbrev topStage : ProtectedStage.{0} ((1 : ℝ) / 2) :=
  P.chain.stage ⟨j, show j ≤ j from le_rfl⟩

/-- The canonical recursion-indexed enumeration at a stage of a prefix. -/
noncomputable def enumerate (i : Set.Iic j) : RI → (P.chain.stage i).target :=
  stageEnumeration (P.target_mk_le i)

theorem enumerate_surjective (i : Set.Iic j) :
    Function.Surjective (P.enumerate i) :=
  stageEnumeration_surjective (P.target_mk_le i)

/-- The bent seed as the bounded prefix at the minimum recursion index. -/
noncomputable def ofMin (j : RI) (_hj : IsMin j) : ProtectedPrefix j where
  chain := constantProtectedChain bentSeedStage
  source_mk_le := fun _ ↦ bentSeedStage_source_mk_le
  target_mk_le := fun _ ↦ bentSeedStage_target_mk_le

/-- Append one scheduled successor to a bounded prefix. -/
noncomputable def successor (P : ProtectedPrefix j) (y : P.topStage.target) :
    ProtectedPrefix (Order.succ j) := by
  let T := scheduledSuccessor P.topStage y
  let Cplus := P.chain.append T
  let e := (successorSegmentWithTop j (not_isMax j)).toOrderEmbedding
  let Cnext := Cplus.reindex e
  have hSource : ∀ k : WithTop (Set.Iic j),
      Cardinal.mk (Cplus.stage k).source ≤ stageCardinal := by
    intro k
    induction k using WithTop.recTopCoe with
    | top =>
        exact scheduledSuccessor_source_mk_le P.topStage y
          (P.source_mk_le ⟨j, show j ≤ j from le_rfl⟩)
    | coe k => exact P.source_mk_le k
  have hTarget : ∀ k : WithTop (Set.Iic j),
      Cardinal.mk (Cplus.stage k).target ≤ stageCardinal := by
    intro k
    induction k using WithTop.recTopCoe with
    | top =>
        exact scheduledSuccessor_target_mk_le P.topStage y
          (P.source_mk_le ⟨j, show j ≤ j from le_rfl⟩)
          (P.target_mk_le ⟨j, show j ≤ j from le_rfl⟩)
    | coe k => exact P.target_mk_le k
  exact {
    chain := Cnext
    source_mk_le := fun i ↦ hSource (e i)
    target_mk_le := fun i ↦ hTarget (e i) }

/-- Append the completed direct limit at a nonzero limit index. -/
noncomputable def ofLimit (j : RI) (hj : Order.IsSuccLimit j)
    (C : ProtectedChain (ι := Set.Iio j) ((1 : ℝ) / 2) 1)
    (hSource : ∀ i, Cardinal.mk (C.stage i).source ≤ stageCardinal)
    (hTarget : ∀ i, Cardinal.mk (C.stage i).target ≤ stageCardinal) :
    ProtectedPrefix j := by
  let i : RI := Classical.choose (not_isMin_iff.mp hj.not_isMin)
  have hi : i < j := Classical.choose_spec (not_isMin_iff.mp hj.not_isMin)
  letI : Nonempty (Set.Iio j) := ⟨⟨i, hi⟩⟩
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hL : (0 : ℝ) < 1 := by norm_num
  let Cplus := C.appendLimit hr hL
  let e := (initialSegmentWithTop j).toOrderEmbedding
  let Cnext := Cplus.reindex e
  have hSourcePlus : ∀ k : WithTop (Set.Iio j),
      Cardinal.mk (Cplus.stage k).source ≤ stageCardinal := by
    intro k
    induction k using WithTop.recTopCoe with
    | top =>
        exact C.limitStage_source_mk_le hr hL
          (initialSegment_mk_le_stageCardinal j) hSource
    | coe k => exact hSource k
  have hTargetPlus : ∀ k : WithTop (Set.Iio j),
      Cardinal.mk (Cplus.stage k).target ≤ stageCardinal := by
    intro k
    induction k using WithTop.recTopCoe with
    | top =>
        exact C.limitStage_target_mk_le hr hL
          (initialSegment_mk_le_stageCardinal j) hTarget
    | coe k => exact hTarget k
  exact {
    chain := Cnext
    source_mk_le := fun i ↦ hSourcePlus (e i)
    target_mk_le := fun i ↦ hTargetPlus (e i) }

/-- Restrict a bounded prefix to an earlier closed initial segment. -/
noncomputable def restriction {i : RI} (hij : i ≤ j) : ProtectedPrefix i where
  chain := P.chain.reindex
    ⟨⟨fun k ↦ (⟨k.1, k.2.trans hij⟩ : Set.Iic j),
      fun x y h ↦ Subtype.ext
        (congrArg (fun z : Set.Iic j ↦ z.1) h)⟩,
      by intro x y; rfl⟩
  source_mk_le k := P.source_mk_le ⟨k.1, k.2.trans hij⟩
  target_mk_le k := P.target_mk_le ⟨k.1, k.2.trans hij⟩

@[simp]
theorem restriction_refl :
    P.restriction (show j ≤ j from le_rfl) = P := by
  apply ext
  cases P
  rfl

theorem restriction_trans {a i : RI} (P : ProtectedPrefix j)
    (hai : a ≤ i) (hij : i ≤ j) :
    (P.restriction hij).restriction hai = P.restriction (hai.trans hij) := by
  apply ext
  cases P
  rfl

/-- The new successor prefix restricts to the prefix from which it was
constructed. -/
theorem successor_restriction (P : ProtectedPrefix j) (y : P.topStage.target) :
    (P.successor y).restriction (Order.le_succ j) = P := by
  apply ext
  unfold successor restriction
  dsimp
  let e := (successorSegmentWithTop j (not_isMax j)).toOrderEmbedding
  let f : Set.Iic j ↪o Set.Iic (Order.succ j) :=
    { toFun := fun k =>
        (⟨k.1, k.2.trans (Order.le_succ j)⟩ : Set.Iic (Order.succ j))
      inj' := fun x y h => Subtype.ext
        (congrArg (fun z : Set.Iic (Order.succ j) => z.1) h)
      map_rel_iff' := by intro x z; rfl }
  rw [ProtectedChain.reindex_comp]
  rw [ProtectedChain.reindex_congr _ (f.trans e)
    (ProtectedChain.withTopCoeOrderEmbedding (ι := Set.Iic j))]
  · exact ProtectedChain.append_reindex_withTopCoe _ _
  · intro k
    exact successorSegmentWithTop_apply_old j (not_isMax j) k

end ProtectedPrefix

end ScottishBook155
