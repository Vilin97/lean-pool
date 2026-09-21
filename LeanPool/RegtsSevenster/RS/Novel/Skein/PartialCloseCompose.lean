/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.PartialCloseTensor

/-!
# Partial closure as a composition

The partial closure is a composition in disguise: reshuffle the
test fragment's boundary so that the `z`-blocks form the incoming
interface and the `x`-blocks the outgoing free side
(`pcReshuffle`), and gluing `z` into `G` is composing `z`
(as a `(0, u+v)`-fragment) with the reshuffled `G`.  This lets
the entire compose-calculus (identity laws, free-side relabels,
permutation absorption) act on partial closures.
-/

namespace RS

/-- The reshuffle of the test boundary: `z`-blocks first (the
interface), `x`-blocks last (the free side). -/
noncomputable def pcReshuffle (s t u v : ℕ) :
    Fin ((s + u) + (t + v)) ≃ Fin ((u + v) + (s + t)) :=
  (interleaveEquiv s t u v).symm.trans
    ((_root_.Equiv.sumComm (Fin (s + t)) (Fin (u + v))).trans
      finSumFinEquiv)

/-- The reshuffle on the low `z`-block. -/
theorem pcReshuffle_zlow (s t u v : ℕ) (j : Fin u) :
    pcReshuffle s t u v
        (Fin.castAdd (t + v) (Fin.natAdd s j)) =
      Fin.castAdd (s + t) (Fin.castAdd v j) := by
  unfold pcReshuffle
  rw [_root_.Equiv.trans_apply, interleaveEquiv_symm_low_right]
  rfl

/-- The reshuffle on the high `z`-block. -/
theorem pcReshuffle_zhigh (s t u v : ℕ) (l : Fin v) :
    pcReshuffle s t u v
        (Fin.natAdd (s + u) (Fin.natAdd t l)) =
      Fin.castAdd (s + t) (Fin.natAdd u l) := by
  unfold pcReshuffle
  rw [_root_.Equiv.trans_apply, interleaveEquiv_symm_high_right]
  rfl

/-- The reshuffle on the low `x`-block. -/
theorem pcReshuffle_xlow (s t u v : ℕ) (i : Fin s) :
    pcReshuffle s t u v
        (Fin.castAdd (t + v) (Fin.castAdd u i)) =
      Fin.natAdd (u + v) (Fin.castAdd t i) := by
  unfold pcReshuffle
  rw [_root_.Equiv.trans_apply, interleaveEquiv_symm_low_left]
  rfl

/-- The reshuffle on the high `x`-block. -/
theorem pcReshuffle_xhigh (s t u v : ℕ) (k : Fin t) :
    pcReshuffle s t u v
        (Fin.natAdd (s + u) (Fin.castAdd v k)) =
      Fin.natAdd (u + v) (Fin.natAdd s k) := by
  unfold pcReshuffle
  rw [_root_.Equiv.trans_apply, interleaveEquiv_symm_high_left]
  rfl

/-- The inverse reshuffle on the low interface. -/
theorem pcReshuffle_symm_low (s t u v : ℕ) (j : Fin u) :
    (pcReshuffle s t u v).symm
        (Fin.castAdd (s + t) (Fin.castAdd v j)) =
      Fin.castAdd (t + v) (Fin.natAdd s j) :=
  (_root_.Equiv.symm_apply_eq _).mpr
    (pcReshuffle_zlow s t u v j).symm

/-- The inverse reshuffle on the high interface. -/
theorem pcReshuffle_symm_high (s t u v : ℕ) (l : Fin v) :
    (pcReshuffle s t u v).symm
        (Fin.castAdd (s + t) (Fin.natAdd u l)) =
      Fin.natAdd (s + u) (Fin.natAdd t l) :=
  (_root_.Equiv.symm_apply_eq _).mpr
    (pcReshuffle_zhigh s t u v l).symm

/-! ### The peeled ground pairs are the z-gluing pairs -/

/-- The full-interface split of the composition pairs at
`(0, u + v, s + t)`. -/
theorem interfacePairs_zsplit (s t u v : ℕ) :
    interfacePairs 0 (u + v) (s + t) =
      (List.finRange v).reverse.map (fun l =>
        ((Sum.inl ⟨u + l.val, by have := l.isLt; omega⟩ :
          Fin (0 + (u + v)) ⊕ Fin ((u + v) + (s + t))),
         Sum.inr ⟨u + l.val, by have := l.isLt; omega⟩)) ++
      (List.finRange u).reverse.map (fun j =>
        (Sum.inl ⟨j.val, by have := j.isLt; omega⟩,
         Sum.inr ⟨j.val, by have := j.isLt; omega⟩)) := by
  unfold interfacePairs
  rw [List.map_reverse, List.map_reverse, List.map_reverse,
    ← List.reverse_append]
  refine congrArg List.reverse ?_
  rw [← List.ofFn_eq_map, List.ofFn_add, List.ofFn_eq_map,
    List.ofFn_eq_map]
  refine congrArg₂ (· ++ ·)
    (List.map_congr_left fun j _ => ?_)
    (List.map_congr_left fun l _ => ?_)
  · refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
      (congrArg Sum.inr (Fin.ext ?_))
    · show 0 + j.val = j.val
      omega
    · rfl
  · refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
      (congrArg Sum.inr (Fin.ext ?_))
    · show 0 + (u + l.val) = u + l.val
      omega
    · rfl

private theorem pc_compose_ground_v_aux (s t u v : ℕ) :
    ∀ (l : List (Fin v)),
      Fragment.mapPairs
          (_root_.Equiv.sumCongr
            (finCongr (by omega : u + v = 0 + (u + v)))
            (pcReshuffle s t u v)).symm
          (l.map (fun l' =>
            ((Sum.inl ⟨u + l'.val, by have := l'.isLt; omega⟩ :
              Fin (0 + (u + v)) ⊕ Fin ((u + v) + (s + t))),
             Sum.inr ⟨u + l'.val, by have := l'.isLt; omega⟩))) =
        l.map (fun l' =>
          ((Sum.inl ⟨u + l'.val, by have := l'.isLt; omega⟩ :
            Fin (u + v) ⊕ Fin ((s + u) + (t + v))),
           Sum.inr ⟨(s + u) + (t + l'.val),
             by have := l'.isLt; omega⟩))
  | [] => rfl
  | l' :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext rfl ?_)
      (pc_compose_ground_v_aux s t u v l)
    show Sum.inr ((pcReshuffle s t u v).symm
      ⟨u + l'.val, by have := l'.isLt; omega⟩) = _
    refine congrArg Sum.inr ?_
    rw [show (⟨u + l'.val, by have := l'.isLt; omega⟩ :
        Fin ((u + v) + (s + t))) =
        Fin.castAdd (s + t) (Fin.natAdd u l') from Fin.ext rfl,
      pcReshuffle_symm_high]
    exact Fin.ext rfl

private theorem pc_compose_ground_u_aux (s t u v : ℕ) :
    ∀ (l : List (Fin u)),
      Fragment.mapPairs
          (_root_.Equiv.sumCongr
            (finCongr (by omega : u + v = 0 + (u + v)))
            (pcReshuffle s t u v)).symm
          (l.map (fun j =>
            ((Sum.inl ⟨j.val, by have := j.isLt; omega⟩ :
              Fin (0 + (u + v)) ⊕ Fin ((u + v) + (s + t))),
             Sum.inr ⟨j.val, by have := j.isLt; omega⟩))) =
        l.map (fun j =>
          ((Sum.inl ⟨j.val, by have := j.isLt; omega⟩ :
            Fin (u + v) ⊕ Fin ((s + u) + (t + v))),
           Sum.inr ⟨s + j.val, by have := j.isLt; omega⟩))
  | [] => rfl
  | j :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext rfl ?_)
      (pc_compose_ground_u_aux s t u v l)
    show Sum.inr ((pcReshuffle s t u v).symm
      ⟨j.val, by have := j.isLt; omega⟩) = _
    refine congrArg Sum.inr ?_
    rw [show (⟨j.val, by have := j.isLt; omega⟩ :
        Fin ((u + v) + (s + t))) =
        Fin.castAdd (s + t) (Fin.castAdd v j) from Fin.ext rfl,
      pcReshuffle_symm_low]
    exact Fin.ext rfl

/-- The peeled composition pairs of the reshuffled test fragment
are the `z`-gluing pairs. -/
theorem pc_compose_ground (s t u v : ℕ) :
    Fragment.mapPairs
        (_root_.Equiv.sumCongr
          (finCongr (by omega : u + v = 0 + (u + v)))
          (pcReshuffle s t u v)).symm
        (interfacePairs 0 (u + v) (s + t)) =
      zClosePairs s t u v := by
  rw [interfacePairs_zsplit s t u v, mapPairs_append]
  unfold zClosePairs
  rw [pc_compose_ground_v_aux s t u v,
    pc_compose_ground_u_aux s t u v]

/-! ### The label meet -/

/-- The peeled composition pairs. -/
noncomputable def pcComposeQs (s t u v : ℕ) :=
  Fragment.mapPairs
    (_root_.Equiv.sumCongr
      (finCongr (by omega : u + v = 0 + (u + v)))
      (pcReshuffle s t u v)).symm
    (interfacePairs 0 (u + v) (s + t))

/-- The composed label of the compose-side normalization is the
partial-closure survivor identification. -/
theorem pc_compose_meet (s t u v : ℕ) :
    (Fragment.foldSurvivingPermEquiv
        (List.Perm.of_eq (pc_compose_ground s t u v))).symm.trans
      ((Fragment.foldSurvivingMapEquiv
          (_root_.Equiv.sumCongr
            (finCongr (by omega : u + v = 0 + (u + v)))
            (pcReshuffle s t u v))
          (pcComposeQs s t u v)).trans
        ((Fragment.foldSurvivingPermEquiv
            (List.Perm.of_eq (mapPairs_symm_cancel
              (_root_.Equiv.sumCongr
                (finCongr (by omega : u + v = 0 + (u + v)))
                (pcReshuffle s t u v))
              (interfacePairs 0 (u + v) (s + t))).symm)).symm.trans
          (((interfaceSurvEquiv 0 (u + v) (s + t)).trans
            finSumFinEquiv).trans
            (finCongr (by omega : 0 + (s + t) = s + t))))) =
      pcSurvEquiv s t u v := by
  apply _root_.Equiv.ext
  intro x
  obtain ⟨xv, hx⟩ := x
  have hpred : pcSurvPred s t u v xv :=
    (pcSurv_iff s t u v xv).mp
      ((forall_ne_iff_not_mem_flat _ xv).mp hx)
  rcases xv with a | b
  · exact hpred.elim
  · rcases hpred with hb | hb
    · have hbv : pcReshuffle s t u v b =
          Fin.natAdd (u + v) (Fin.castAdd t ⟨b.val, hb⟩) := by
        conv_lhs => rw [show b = Fin.castAdd (t + v)
          (Fin.castAdd u ⟨b.val, hb⟩) from Fin.ext rfl]
        exact pcReshuffle_xlow s t u v ⟨b.val, hb⟩
      have hsurvL : ∀ p ∈ interfacePairs 0 (u + v) (s + t),
          (Sum.inr (pcReshuffle s t u v b) :
            Fin (0 + (u + v)) ⊕ Fin ((u + v) + (s + t))) ≠ p.1 ∧
          (Sum.inr (pcReshuffle s t u v b) :
            Fin (0 + (u + v)) ⊕ Fin ((u + v) + (s + t))) ≠ p.2 :=
        (forall_ne_iff_not_mem_flat _ _).mpr
          ((interfaceSurv_iff 0 (u + v) (s + t) _).mpr
            (by show ¬ (pcReshuffle s t u v b).val < u + v
                rw [hbv]
                show ¬ (u + v) + b.val < u + v
                omega))
      show finCongr (by omega : 0 + (s + t) = s + t)
        (finSumFinEquiv (interfaceSurvEquiv 0 (u + v) (s + t)
          ⟨Sum.inr (pcReshuffle s t u v b), hsurvL⟩)) =
        pcSurvEquiv s t u v ⟨Sum.inr b, hx⟩
      rw [interfaceSurvEquiv_inr 0 (u + v) (s + t)
          ⟨Sum.inr (pcReshuffle s t u v b), hsurvL⟩ _ rfl
          (by rw [hbv]; show u + v ≤ (u + v) + b.val; omega),
        finSumFinEquiv_apply_right,
        pcSurvEquiv_val_low s t u v b hx hb]
      refine Fin.ext ?_
      show 0 + ((pcReshuffle s t u v b).val - (u + v)) = b.val
      rw [hbv]
      show 0 + ((u + v) + b.val - (u + v)) = b.val
      omega
    · have hk : b.val - (s + u) < t := by omega
      have hb2 : b = Fin.natAdd (s + u)
          (Fin.castAdd v ⟨b.val - (s + u), hk⟩) :=
        Fin.ext (by
          show b.val = (s + u) + (b.val - (s + u))
          omega)
      have hbv : pcReshuffle s t u v b =
          Fin.natAdd (u + v)
            (Fin.natAdd s ⟨b.val - (s + u), hk⟩) := by
        conv_lhs => rw [hb2]
        exact pcReshuffle_xhigh s t u v ⟨b.val - (s + u), hk⟩
      have hsurvL : ∀ p ∈ interfacePairs 0 (u + v) (s + t),
          (Sum.inr (pcReshuffle s t u v b) :
            Fin (0 + (u + v)) ⊕ Fin ((u + v) + (s + t))) ≠ p.1 ∧
          (Sum.inr (pcReshuffle s t u v b) :
            Fin (0 + (u + v)) ⊕ Fin ((u + v) + (s + t))) ≠ p.2 :=
        (forall_ne_iff_not_mem_flat _ _).mpr
          ((interfaceSurv_iff 0 (u + v) (s + t) _).mpr
            (by show ¬ (pcReshuffle s t u v b).val < u + v
                rw [hbv]
                show ¬ (u + v) + (s + (b.val - (s + u))) < u + v
                omega))
      show finCongr (by omega : 0 + (s + t) = s + t)
        (finSumFinEquiv (interfaceSurvEquiv 0 (u + v) (s + t)
          ⟨Sum.inr (pcReshuffle s t u v b), hsurvL⟩)) =
        pcSurvEquiv s t u v ⟨Sum.inr b, hx⟩
      rw [interfaceSurvEquiv_inr 0 (u + v) (s + t)
          ⟨Sum.inr (pcReshuffle s t u v b), hsurvL⟩ _ rfl
          (by rw [hbv]
              show u + v ≤ (u + v) + (s + (b.val - (s + u)))
              omega),
        finSumFinEquiv_apply_right,
        pcSurvEquiv_val_high s t u v b hx
          (by omega) (by omega) (by omega)]
      refine Fin.ext ?_
      show 0 + ((pcReshuffle s t u v b).val - (u + v)) =
        s + (b.val - (s + u))
      rw [hbv]
      show 0 + ((u + v) + (s + (b.val - (s + u))) - (u + v)) =
        s + (b.val - (s + u))
      omega

/-- **Partial closure as a composition**: gluing `z` into `G` is
composing `z` with the reshuffled `G`. -/
noncomputable def partialCloseEqCompose {s t u v : ℕ}
    (z : Fragment (Fin (u + v)))
    (G : Fragment (Fin ((s + u) + (t + v)))) :
    (partialClose z G).Equiv
      (((z.relabel
          (finCongr (by omega : u + v = 0 + (u + v)))).compose
        (G.relabel (pcReshuffle s t u v))).relabel
        (finCongr (by omega : 0 + (s + t) = s + t))) := by
  let eZ := _root_.Equiv.sumCongr
    (finCongr (by omega : u + v = 0 + (u + v)))
    (pcReshuffle s t u v)
  let qs := pcComposeQs s t u v
  have wfqs : Fragment.PairsWF qs :=
    Fragment.mapPairs_wf eZ.symm _
      (interfacePairs_wf 0 (u + v) (s + t))
  let Amb := z.disjUnion G
  -- C5: bridge the peeled pairs to the z-gluing pairs.
  have C5 : (Fragment.glueList Amb qs wfqs).Equiv
      ((Fragment.glueList Amb (zClosePairs s t u v)
          (zClosePairs_wf s t u v)).relabel
        (Fragment.foldSurvivingPermEquiv
          (List.Perm.of_eq (pc_compose_ground s t u v))).symm) :=
    Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv Amb (pc_compose_ground s t u v)
        wfqs (zClosePairs_wf s t u v)
        (List.Perm.of_eq (pc_compose_ground s t u v)))
  -- C3: the relabelling stage.
  have C3 := (Fragment.glueListRelabel Amb eZ qs wfqs).trans
    ((Fragment.Equiv.relabelCongr C5
      (Fragment.foldSurvivingMapEquiv eZ qs)).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- C2: bridge the composition pairs.
  have C2 := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (Amb.relabel eZ)
        (mapPairs_symm_cancel eZ
          (interfacePairs 0 (u + v) (s + t))).symm
        (interfacePairs_wf 0 (u + v) (s + t))
        (Fragment.mapPairs_wf eZ _ wfqs)
        (List.Perm.of_eq (mapPairs_symm_cancel eZ
          (interfacePairs 0 (u + v) (s + t))).symm))).trans
    ((Fragment.Equiv.relabelCongr C3
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel eZ
          (interfacePairs 0 (u + v) (s + t))).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- C1: transport across the peel.
  have C1 : (Fragment.glueList
      ((z.relabel
        (finCongr (by omega : u + v = 0 + (u + v)))).disjUnion
        (G.relabel (pcReshuffle s t u v)))
      (interfacePairs 0 (u + v) (s + t))
      (interfacePairs_wf 0 (u + v) (s + t))).Equiv
      (Fragment.glueList (Amb.relabel eZ)
        (interfacePairs 0 (u + v) (s + t))
        (interfacePairs_wf 0 (u + v) (s + t))) :=
    Fragment.glueListCongr
      ((Fragment.relabelDisjUnionLeft z
          (G.relabel (pcReshuffle s t u v))
          (finCongr (by omega : u + v = 0 + (u + v)))).trans
        ((Fragment.Equiv.relabelCongr
          (Fragment.relabelDisjUnionRight z G
            (pcReshuffle s t u v))
          (_root_.Equiv.sumCongr
            (finCongr (by omega : u + v = 0 + (u + v)))
            (_root_.Equiv.refl _))).trans
        ((Fragment.Equiv.relabelTrans _ _ _).trans
        (Fragment.Equiv.relabelEq _
          (_root_.Equiv.ext (fun x => by cases x <;> rfl))))))
      (interfacePairs 0 (u + v) (s + t))
      (interfacePairs_wf 0 (u + v) (s + t))
  -- The compose side, fully normalized onto the z-gluing fold.
  have RHSchain : (((z.relabel
      (finCongr (by omega : u + v = 0 + (u + v)))).compose
        (G.relabel (pcReshuffle s t u v))).relabel
        (finCongr (by omega : 0 + (s + t) = s + t))).Equiv
      ((Fragment.glueList Amb (zClosePairs s t u v)
          (zClosePairs_wf s t u v)).relabel
        ((((Fragment.foldSurvivingPermEquiv
            (List.Perm.of_eq
              (pc_compose_ground s t u v))).symm.trans
          (Fragment.foldSurvivingMapEquiv eZ qs)).trans
          (Fragment.foldSurvivingPermEquiv
            ((mapPairs_symm_cancel eZ
              (interfacePairs 0 (u + v) (s + t))).symm ▸
              List.Perm.refl _)).symm).trans
          (((interfaceSurvEquiv 0 (u + v) (s + t)).trans
            finSumFinEquiv).trans
            (finCongr (by omega : 0 + (s + t) = s + t))))) :=
    (Fragment.Equiv.relabelCongr
      ((composeNormal
        (z.relabel (finCongr (by omega : u + v = 0 + (u + v))))
        (G.relabel (pcReshuffle s t u v))).trans
        ((Fragment.Equiv.relabelCongr (C1.trans C2)
          ((interfaceSurvEquiv 0 (u + v) (s + t)).trans
            finSumFinEquiv)).trans
        (Fragment.Equiv.relabelTrans _ _ _)))
      (finCongr (by omega : 0 + (s + t) = s + t))).trans
    (Fragment.Equiv.relabelTrans _ _ _)
  exact (Fragment.Equiv.relabelEq _
    (pc_compose_meet s t u v).symm).trans RHSchain.symm

end RS
