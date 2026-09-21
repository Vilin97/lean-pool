/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeAssoc

/-!
# Commutativity of pair closure

The closed fragment `pairClose F G`, formed by composing
an `(0+t)`- with a `(t+0)`-fragment, is invariant (up to
`Fragment.Equiv`) under swapping `F` and `G`.
-/

namespace RS

namespace Fragment

private def pcSwapFun (t : ℕ) :
    Fin (0 + t) ⊕ Fin (t + 0) →
      Fin (0 + t) ⊕ Fin (t + 0) :=
  Sum.elim
    (fun x => Sum.inr (finCongr (by omega) x))
    (fun y => Sum.inl (finCongr (by omega) y))

/-- Self-inverse sum-swap equivalence used in the
`pairClose` commutativity proof. -/
private def pairCloseSwap (t : ℕ) :
    Fin (0 + t) ⊕ Fin (t + 0) ≃
      Fin (0 + t) ⊕ Fin (t + 0) where
  toFun := pcSwapFun t
  invFun := pcSwapFun t
  left_inv x := by
    rcases x with a | b <;> simp [pcSwapFun, finCongr]
  right_inv x := by
    rcases x with a | b <;> simp [pcSwapFun, finCongr]

/-- The disjoint-union ambients of `pairClose F G`
and `pairClose G F` are related by `pairCloseSwap`. -/
private noncomputable def pairCloseAmbient
    {t : ℕ} (F G : Fragment (Fin t)) :
    (disjUnion
      (F.relabel (finCongr (by omega : t = 0 + t)))
      (G.relabel (finCongr (by omega : t = t + 0)))
    ).Equiv
    (relabel
      (disjUnion
        (G.relabel
          (finCongr (by omega : t = 0 + t)))
        (F.relabel
          (finCongr (by omega : t = t + 0))))
      (pairCloseSwap t)) where
  flagEquiv :=
    _root_.Equiv.sumComm F.Flag G.Flag
  vertexEquiv :=
    _root_.Equiv.sumComm F.Vertex G.Vertex
  attach_comm f := by
    rcases f with g | g
    · show (((F.attach g).map id
              (finCongr (by omega : t = t + 0))).map
            Sum.inr Sum.inr).map
            id (pairCloseSwap t) =
          (((F.attach g).map id
              (finCongr (by omega : t = 0 + t))).map
            Sum.inl Sum.inl).map
            (_root_.Equiv.sumComm F.Vertex
              G.Vertex) id
      rcases F.attach g with v | ℓ <;> rfl
    · show (((G.attach g).map id
              (finCongr (by omega : t = 0 + t))).map
            Sum.inl Sum.inl).map
            id (pairCloseSwap t) =
          (((G.attach g).map id
              (finCongr (by omega : t = t + 0))).map
            Sum.inr Sum.inr).map
            (_root_.Equiv.sumComm F.Vertex
              G.Vertex) id
      rcases G.attach g with v | ℓ <;> rfl
  pairing_comm f := by
    rcases f with g | g <;> rfl
  circles_eq := by
    show F.circles + G.circles =
      G.circles + F.circles
    omega

/-- `mapPairs` through `(pairCloseSwap t).symm` on
the interface pairs yields the swap of each pair. -/
private theorem mapPairs_pcs_symm (t : ℕ) :
    mapPairs (pairCloseSwap t).symm
      (interfacePairs 0 t 0) =
      (interfacePairs 0 t 0).map Prod.swap := by
  simp only [interfacePairs, mapPairs,
    List.map_map, List.map_reverse]
  refine congrArg List.reverse
    (List.map_congr_left fun k _ => ?_)
  -- Each pair: (Sum.inl ⟨0+k, _⟩, Sum.inr ⟨k, _⟩)
  -- .symm acts as pcSwapFun since self-inverse
  show (pcSwapFun t (Sum.inl ⟨0 + k.val, _⟩),
        pcSwapFun t (Sum.inr ⟨k.val, _⟩)) =
    (Sum.inr ⟨k.val, _⟩,
     Sum.inl ⟨0 + k.val, _⟩)
  simp only [pcSwapFun, Sum.elim_inl,
    Sum.elim_inr]
  exact Prod.ext
    (congrArg Sum.inr (Fin.ext (by simp)))
    (congrArg Sum.inl (Fin.ext (by simp)))

/-- Composing `pairClose F G` and `pairClose G F`
yields equivalent closed fragments. -/
noncomputable def pairCloseComm {t : ℕ}
    (F G : Fragment (Fin t)) :
    (pairClose F G).Equiv (pairClose G F) := by
  -- Abbreviations
  set fc₁ := finCongr (show t = 0 + t by omega)
  set fc₂ := finCongr (show t = t + 0 by omega)
  set A_FG := disjUnion (F.relabel fc₁)
    (G.relabel fc₂)
  set A_GF := disjUnion (G.relabel fc₁)
    (F.relabel fc₂)
  set e := pairCloseSwap t
  set ips := interfacePairs 0 t 0
  set wf := interfacePairs_wf 0 t 0
  set survE :=
    (interfaceSurvEquiv 0 t 0).trans
      finSumFinEquiv
  -- Normal forms via composeNormal
  have nFG := composeNormal (F.relabel fc₁)
    (G.relabel fc₂)
  have nGF := composeNormal (G.relabel fc₁)
    (F.relabel fc₂)
  -- The ambient fragments are related
  have amb := pairCloseAmbient F G
  -- glueList respects the ambient equiv
  have gc := glueListCongr amb ips wf
  -- Pull relabel through glueList
  set mips := mapPairs e.symm ips
  have wf_m : PairsWF mips :=
    mapPairs_wf e.symm ips wf
  have hcancel : mapPairs e mips = ips :=
    mapPairs_symm_cancel e ips
  -- glueListEqEquiv bridges pair lists
  have eq1 :=
    (glueListEqEquiv (A_GF.relabel e)
      hcancel (mapPairs_wf e mips wf_m) wf
      (hcancel ▸ List.Perm.refl _)).symm
  -- glueListRelabel pulls e through
  have rl := glueListRelabel A_GF e mips wf_m
  -- mips = ips.map Prod.swap
  have hswap : mips = ips.map Prod.swap :=
    mapPairs_pcs_symm t
  have wf_sw := swapPairs_wf ips wf
  -- Bridge mips to ips.map Prod.swap
  have eq2 := glueListEqEquiv A_GF hswap
    wf_m wf_sw (hswap ▸ List.Perm.refl _)
  -- glueListSwap
  have sw := glueListSwap A_GF ips wf
  -- The surviving label type is empty
  have hempty :
      IsEmpty (FoldSurviving
        (Fin (0 + t) ⊕ Fin (t + 0)) ips) := by
    have h0 : IsEmpty (Fin 0 ⊕ Fin 0) :=
      isEmpty_sum.mpr ⟨Fin.isEmpty, Fin.isEmpty⟩
    exact ⟨fun x => h0.false
      ((interfaceSurvEquiv 0 t 0) x)⟩
  -- Build the chain at glueList level:
  -- GL(A_FG) ≡ GL(A_GF.relabel e) [gc]
  -- ≡ GL(A_GF.relabel e, mapPairs e mips).relabel
  --     fSPE₁  [eq1]
  -- ≡ (GL(A_GF, mips).relabel fSME).relabel
  --     fSPE₁  [rl]
  -- ≡ GL(A_GF, mips).relabel (fSME.trans fSPE₁)
  --     [relabelTrans]
  -- ≡ (GL(A_GF, ips.map swap).relabel
  --     fSPE₂.symm).relabel (fSME.trans fSPE₁)
  --     [relabelFlip eq2.symm]
  -- ≡ GL(A_GF, ips.map swap).relabel _
  --     [relabelTrans]
  -- ≡ (GL(A_GF, ips).relabel
  --     (swapFoldEquiv ips).symm).relabel _
  --     [sw]
  -- ≡ GL(A_GF, ips).relabel e_mid
  --     [relabelTrans]
  have chain :=
    gc.trans (eq1.trans
      ((Equiv.relabelCongr rl _).trans
        ((Equiv.relabelTrans _ _ _).trans
          ((Equiv.relabelCongr
            (Equiv.relabelFlip eq2.symm) _).trans
            ((Equiv.relabelTrans _ _ _).trans
              ((Equiv.relabelCongr sw _).trans
                (Equiv.relabelTrans _ _ _)))))))
  -- chain : GL(A_FG, ips) ≡ GL(A_GF, ips).relabel
  --   e_mid
  -- Lift to the survE level
  have lifted :=
    (Equiv.relabelCongr chain survE).trans
      (Equiv.relabelTrans _ _ _)
  -- lifted : GL(A_FG).relabel survE ≡
  --   GL(A_GF).relabel (e_mid.trans survE)
  -- Since source is empty, e_mid.trans survE = survE
  have bridge :
      ((glueList A_FG ips wf).relabel survE).Equiv
      ((glueList A_GF ips wf).relabel survE) :=
    lifted.trans
      (Equiv.relabelEq _ (_root_.Equiv.ext
        fun x => False.elim (hempty.false x)))
  exact nFG.trans (bridge.trans nGF.symm)

end Fragment

end RS
