/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.BuildStrategies

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.GaleStewart

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace GaleStewartGame
open Stream'.Discrete Descriptive Tree PreStrategy

/-!
#Closed determinacy

This file proves the Gale-Stewart lemma on the determinacy of closed games. More precisely, the
defensive strategy is winning for closed games.
-/

variable {A : Type*} {T : tree A} {G G' : Game A} {p p' : Player}

lemma PreStrategy.cast_quasi {T T' : tree A} {p p' : Player} (hT : T = T') (hP : p = p')
  (S : PreStrategy T p) :
  (cast (by rw [hT, hP]) S : PreStrategy T' p').IsQuasi ↔ S.IsQuasi := by subst hT hP; rfl
lemma PreStrategy.cast_winning {G G' : Game A} (h : G = G') (S : PreStrategy G.tree p) :
  (cast (by rw [h]) S : PreStrategy G'.tree p).IsWinning
  ↔ S.IsWinning := by subst h; rfl
namespace Game
lemma defensive_equals_pre {G : Game A} {p : Player} (hP : IsPruned G.tree)
  (h : ¬ G.ExistsWinning p.swap) :
  (defensiveQuasi G p hP).1.subtree = (defensivePre G p).subtree := by
  refine preserveProp_eq_extQuasi _ ?_ hP ?_ ?_
  · intro x hp nw a; simp_rw [preserveProp, WinningPosition]
    by_contra hc; conv at hc => simp [Set.Nonempty]
    apply nw; rw [WinningPosition, existsWinning_iff_quasi]
    let f (b : A) (h : [b] ∈ ((G.residual x).residual [a.val]).tree) :
      PreStrategy (((G.residual x).residual [a.val]).residual [b]).tree Player.zero :=
      cast (by simp [ExtensionsAt.val']) (hc ⟨b, by simpa [ExtensionsAt.val']⟩).choose.pre
    let S := (sew f).firstMove _ (by exact a.prop)
    use S.extQuasi (hP.sub _); rw [firstMove_extQuasi_isWinning]
    · apply sew_isWinning; intro b h
      rw [cast_winning (G := G.residual _) (by simp [ExtensionsAt.val'])]
      exact (hc ⟨b, by simpa [ExtensionsAt.val']⟩).choose_spec
    · apply sew_isQuasi; intros
      exact (PreStrategy.cast_quasi (by simp [ExtensionsAt.val']) rfl _).mpr (Strategy.isQuasi _)
  · rintro rfl; by_contra hc; conv at hc => simp
    apply h; rw [existsWinning_iff_quasi]
    let f (a : A) (h : [a] ∈ G.tree) := (existsWinning_iff_quasi.mp (hc a h)).choose
    use ⟨sew (fun a h ↦ (f a h).1), sew_isQuasi _ (fun a h ↦ (f a h).2)⟩
    apply sew_isWinning (f := fun a h ↦ (f a h).1); intro a ha
    exact (existsWinning_iff_quasi.mp (hc a ha)).choose_spec
  · rintro rfl _; simpa [WinningPosition, ExistsWinning] using h

lemma isClosed_image_payoff {G : Game A} :
  IsClosed G.payoff ↔ IsClosed (Subtype.val '' G.payoff) :=
  (Topology.IsClosedEmbedding.subtypeVal (body_isClosed G.tree)).isClosed_iff_image_isClosed
lemma defensive_winning_isClosed (hC : IsClosed G.payoff) (hP : IsPruned G.tree) :
  (defensivePre G Player.zero).IsWinning := by
  intro a ha; rw [Player.payoff_zero,
    ← (isClosed_image_payoff.mp hC).closure_eq,
    mem_closure_iff_nhds_basis (hasBasis_principalOpen a)]
  intro x h; by_contra hfa; simp_rw [not_exists, not_and'] at hfa
  specialize ha (a.take (2 * (x.length / 2)) ++ [a.get (2 * (x.length / 2))]) (by simp)
  apply (defensivePre G Player.zero).subtree_compatible ⟨_, mem_of_append ha⟩
    (by synthIsPosition) ha
  apply AllWinning.existsWinning _ (hP.sub _); apply wonPosition_iff_disjoint.mpr
  rw [← Set.subset_empty_iff]; intro a' ⟨h1, h2⟩; apply hfa a'
  · conv at h1 => simp [ExtensionsAt.val']
    apply principalOpen_mono _ h1
    rw [(principalOpen_iff_restrict _ _).mp h]; simp; omega
  · rw [Player.residual_odd _ _ (by simp)] at h2; simpa using h2

lemma defensive_winning_isOpen (hC : IsOpen G.payoff) (hP : IsPruned G.tree) :
  (defensivePre G Player.one).IsWinning := by
  rw [← sew_residual (defensivePre G Player.one)]; apply sew_isWinning
  simp only [defensivePre_residual]; intro a _; apply defensive_winning_isClosed
  · exact isClosed_compl_iff.mpr (hC.preimage (body.append_con [a]))
  · exact hP.sub _
lemma gale_stewart_precise (h : IsClosed G.payoff) (hP : IsPruned G.tree)
  (h' : ¬ G.ExistsWinning Player.one) : (defensiveQuasi G Player.zero hP).1.IsWinning := by
  dsimp [IsWinning]; rw [defensive_equals_pre hP h' (p := Player.zero)]
  exact defensive_winning_isClosed h hP
lemma gale_stewart (h : IsClosed G.payoff) (hP : IsPruned G.tree) : G.IsDetermined := by
  classical
  exact
    if h' : _ then ⟨Player.one, h'⟩
    else ⟨Player.zero, existsWinning_iff_quasi.mpr ⟨_, gale_stewart_precise h hP h'⟩⟩
lemma gale_stewart_precise' (h : IsOpen G.payoff) (hP : IsPruned G.tree)
  (h' : ¬ ∃ S : Strategy G.tree Player.zero, S.pre.IsWinning) :
  (defensiveQuasi G Player.one hP).1.IsWinning := by
  dsimp [IsWinning]; rw [defensive_equals_pre hP h' (p := Player.one)]
  exact defensive_winning_isOpen h hP

end GaleStewartGame.Game
