/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.StarPrep
public import LeanPool.RegtsSevenster.RS.Novel.Skein.IdentityLawRight

/-!
# The bundle closure is the straight-matching self-glue

The full closure of an `(m + m)`-fragment against the strand
bundle is the self-glue of its straight matching `i ↔ m + i`.
The proof fuses and splits folds using only established
machinery: the closure's interface fold splits into the
high-block glues followed by the low-block glues
(`interfacePairs_split` and `glueListAppend`); the high-block
stage is itself a composition against the transposed bundle
(`composeNormal` read backwards), which the right identity law
collapses to the fragment; and the lifted low-block pairs are
then exactly the straight matching.
-/

@[expose] public section

namespace RS

section BundleClose

variable (m : ℕ)

/-! ### Flat membership of the two blocks -/

/-- The high block's flags are exactly the labels at or above `m`
on either side. -/
theorem mem_highCross_flat
    (z : Fin (0 + (m + m)) ⊕ Fin ((m + m) + 0)) :
    z ∈ (highCross m).flatMap (fun p => [p.1, p.2]) ↔
      (∃ a, z = Sum.inl a ∧ m ≤ a.val) ∨
      (∃ b, z = Sum.inr b ∧ m ≤ b.val) := by
  unfold highCross
  rw [List.flatMap_map]
  simp only [List.mem_flatMap, List.mem_reverse, List.mem_finRange,
    List.mem_cons, List.not_mem_nil, or_false, true_and]
  constructor
  · rintro ⟨k, hk | hk⟩
    · exact Or.inl ⟨_, hk, by simp⟩
    · exact Or.inr ⟨_, hk, by simp⟩
  · rintro (⟨a, rfl, ha⟩ | ⟨b, rfl, hb⟩)
    · refine ⟨⟨a.val - m, by have := a.isLt; omega⟩, Or.inl ?_⟩
      refine congrArg Sum.inl (Fin.ext ?_)
      change a.val = m + (a.val - m)
      omega
    · refine ⟨⟨b.val - m, by have := b.isLt; omega⟩, Or.inr ?_⟩
      refine congrArg Sum.inr (Fin.ext ?_)
      change b.val = m + (b.val - m)
      omega

/-- The high block is a well-formed gluing list. -/
theorem highCross_wf : Fragment.PairsWF (highCross m) :=
  (interfacePairs_split m ▸
    interfacePairs_wf 0 (m + m) 0).append_left

/-- And so is the whole closure list, high block then low. -/
theorem splitCross_wf :
    Fragment.PairsWF (highCross m ++ lowCross m) :=
  interfacePairs_split m ▸ interfacePairs_wf 0 (m + m) 0

/-! ### The surviving labels of the high-block stage -/

/-- The forward survivor map: low labels to the surviving left
slots, high labels to the surviving right slots. -/
noncomputable def bcPhiFun (x : Fin (m + m)) :
    Fragment.FoldSurviving
      (Fin (0 + (m + m)) ⊕ Fin ((m + m) + 0)) (highCross m) :=
  if h : x.val < m then
    ⟨Sum.inl ⟨x.val, by omega⟩,
     (forall_ne_iff_not_mem_flat _ _).mpr (by
        rw [mem_highCross_flat]
        rintro (⟨a, ha, hm⟩ | ⟨b, hb, _⟩)
        · rw [show a = ⟨x.val, by omega⟩ from
            (Sum.inl.inj ha).symm] at hm
          exact absurd hm (by simpa using h)
        · exact Sum.inl_ne_inr hb)⟩
  else
    ⟨Sum.inr ⟨x.val - m, by have := x.isLt; omega⟩,
     (forall_ne_iff_not_mem_flat _ _).mpr (by
        rw [mem_highCross_flat]
        rintro (⟨a, ha, _⟩ | ⟨b, hb, hm⟩)
        · exact Sum.inr_ne_inl ha
        · rw [show b = ⟨x.val - m, by have := x.isLt; omega⟩ from
            (Sum.inr.inj hb).symm] at hm
          have := x.isLt
          simp only [] at hm
          omega)⟩

/-- The inverse survivor map. -/
noncomputable def bcPhiInv
    (s : Fragment.FoldSurviving
      (Fin (0 + (m + m)) ⊕ Fin ((m + m) + 0)) (highCross m)) :
    Fin (m + m) :=
  match hs : s.val with
  | Sum.inl a => ⟨a.val, by
      have hnot := (forall_ne_iff_not_mem_flat _ _).mp s.prop
      by_contra hge
      exact hnot ((mem_highCross_flat m s.val).mpr
        (Or.inl ⟨a, hs, by omega⟩))⟩
  | Sum.inr b => ⟨m + b.val, by
      have hnot := (forall_ne_iff_not_mem_flat _ _).mp s.prop
      have hb : b.val < m := by
        by_contra hge
        exact hnot ((mem_highCross_flat m s.val).mpr
          (Or.inr ⟨b, hs, by omega⟩))
      omega⟩

/-- The survivor identification of the high-block stage. -/
noncomputable def bcPhi : Fin (m + m) ≃
    Fragment.FoldSurviving
      (Fin (0 + (m + m)) ⊕ Fin ((m + m) + 0)) (highCross m) where
  toFun := bcPhiFun m
  invFun := bcPhiInv m
  left_inv x := by
    by_cases h : x.val < m
    · have h1 : bcPhiFun m x = ⟨Sum.inl ⟨x.val, by omega⟩, _⟩ :=
        dite_eq_left h
      rw [h1]
      change (⟨x.val, _⟩ : Fin (m + m)) = x
      exact Fin.ext rfl
    · have h1 : bcPhiFun m x =
          ⟨Sum.inr ⟨x.val - m, by have := x.isLt; omega⟩, _⟩ :=
        dite_eq_right h
      rw [h1]
      change (⟨m + (x.val - m), _⟩ : Fin (m + m)) = x
      exact Fin.ext (show m + (x.val - m) = x.val by omega)
  right_inv s := by
    obtain ⟨sv, hp⟩ := s
    rcases sv with a | b
    · have ha : a.val < m := by
        have hnot := (forall_ne_iff_not_mem_flat _ _).mp hp
        by_contra hge
        exact hnot ((mem_highCross_flat m _).mpr
          (Or.inl ⟨a, rfl, by omega⟩))
      change bcPhiFun m ⟨a.val, by omega⟩ = _
      have h1 : bcPhiFun m ⟨a.val, by omega⟩ =
          ⟨Sum.inl ⟨a.val, by omega⟩, _⟩ := dite_eq_left ha
      rw [h1]
    · have hb : b.val < m := by
        have hnot := (forall_ne_iff_not_mem_flat _ _).mp hp
        by_contra hge
        exact hnot ((mem_highCross_flat m _).mpr
          (Or.inr ⟨b, rfl, by omega⟩))
      change bcPhiFun m ⟨m + b.val, by omega⟩ = _
      have h1 : bcPhiFun m ⟨m + b.val, by omega⟩ =
          ⟨Sum.inr ⟨m + b.val - m, by omega⟩, _⟩ :=
        dite_eq_right (show ¬ m + b.val < m by omega)
      rw [h1]
      exact Subtype.ext (congrArg Sum.inr (Fin.ext (by
        change m + b.val - m = b.val
        omega)))

/-! ### The ambient relabelling -/

/-- From the `(m,m,m)`-interface ambient to the full-closure
ambient: a cast on the left factor, the block transpose threaded
through a cast on the right. -/
noncomputable def bcDelta :
    (Fin (m + m) ⊕ Fin (m + m)) ≃
      (Fin (0 + (m + m)) ⊕ Fin ((m + m) + 0)) :=
  _root_.Equiv.sumCongr
    (finCongr (by omega : m + m = 0 + (m + m)))
    ((transposeEquiv m m).symm.trans
      (finCongr (by omega : m + m = (m + m) + 0)))

/-- The mapped `(m,m,m)`-interface pairs are the high-block
pairs. -/
theorem mapPairs_bcDelta :
    Fragment.mapPairs (bcDelta m) (interfacePairs m m m) =
      highCross m := by
  apply List.ext_getElem
  · simp [Fragment.mapPairs, interfacePairs, highCross]
  intro i hi hi'
  have him : i < m := by
    have h0 : (Fragment.mapPairs (bcDelta m)
        (interfacePairs m m m)).length = m := by
      simp [Fragment.mapPairs, interfacePairs]
    omega
  have hip : i < (interfacePairs m m m).length := by
    simp only [interfacePairs, List.length_map,
      List.length_reverse, List.length_finRange]
    omega
  rw [mapPairs_getElem (bcDelta m) _ i hi hip]
  have hI : (interfacePairs m m m)[i]'hip =
      (Sum.inl ⟨m + (m - 1 - i), by omega⟩,
       Sum.inr ⟨m - 1 - i, by omega⟩) := by
    simp only [interfacePairs, List.getElem_map,
      List.getElem_reverse, List.length_finRange,
      List.getElem_finRange]
    refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
      (congrArg Sum.inr (Fin.ext ?_)) <;> simp
  rw [hI]
  have hml : i < (highCross m).length := by
    simp only [highCross, List.length_map, List.length_reverse,
      List.length_finRange]
    omega
  have hR : (highCross m)[i]'hml =
      (Sum.inl ⟨m + (m - 1 - i), by omega⟩,
       Sum.inr ⟨m + (m - 1 - i), by omega⟩) := by
    simp only [highCross, List.getElem_map,
      List.getElem_reverse, List.length_finRange,
      List.getElem_finRange]
    refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
      (congrArg Sum.inr (Fin.ext ?_)) <;> simp
  rw [hR]
  refine Prod.ext (congrArg Sum.inl (Fin.ext rfl))
    (congrArg Sum.inr (Fin.ext ?_))
  rw [_root_.Equiv.trans_apply,
    show (transposeEquiv m m).symm = transposeEquiv m m from
      transposeEquiv_symm m m,
    transposeEquiv_low m m (m - 1 - i) (by omega) (by omega)
      (by omega)]
  rfl

/-! ### The high-block stage collapses to the fragment -/

/-- The full-closure ambient. -/
noncomputable def bcAmbient (V : Fragment (Fin (m + m))) :
    Fragment (Fin (0 + (m + m)) ⊕ Fin ((m + m) + 0)) :=
  (V.relabel (finCongr (by omega : m + m = 0 + (m + m)))).disjUnion
    ((strandBundle m).relabel
      (finCongr (by omega : m + m = (m + m) + 0)))

/-- The `(m,m,m)`-interface ambient: the fragment against the
transposed bundle. -/
noncomputable def bcAmbient2 (V : Fragment (Fin (m + m))) :
    Fragment (Fin (m + m) ⊕ Fin (m + m)) :=
  V.disjUnion ((strandBundle m).relabel (transposeEquiv m m))

/-- The two ambients agree through the ambient relabelling. -/
noncomputable def bcAmbientEquiv (V : Fragment (Fin (m + m))) :
    (bcAmbient m V).Equiv
      ((bcAmbient2 m V).relabel (bcDelta m)) := by
  have hB : ((strandBundle m).relabel
      (finCongr (by omega : m + m = (m + m) + 0))).Equiv
      (((strandBundle m).relabel (transposeEquiv m m)).relabel
        ((transposeEquiv m m).symm.trans
          (finCongr (by omega : m + m = (m + m) + 0)))) :=
    ((Fragment.Equiv.relabelTrans (strandBundle m)
        (transposeEquiv m m) _).trans
      (Fragment.Equiv.relabelEq (strandBundle m)
        (_root_.Equiv.ext (fun x => by simp)))).symm
  refine (Fragment.Equiv.disjUnionCongr
    (Fragment.Equiv.refl _) hB).trans ?_
  refine (Fragment.relabelDisjUnionRight _ _ _).trans ?_
  refine (Fragment.Equiv.relabelCongr
    (Fragment.relabelDisjUnionLeft V _ _) _).trans ?_
  refine (Fragment.Equiv.relabelTrans _ _ _).trans ?_
  exact Fragment.Equiv.relabelEq _
    (_root_.Equiv.ext (fun x => by rcases x with x | x <;> rfl))

/-- The assembled survivor identification equals the direct
one. -/
theorem bcPhi_eq :
    ((((interfaceSurvEquiv m m m).trans finSumFinEquiv).symm.trans
      (Fragment.foldSurvivingMapEquiv (bcDelta m)
        (interfacePairs m m m))).trans
      (Fragment.foldSurvivingPermEquiv
        (List.Perm.of_eq (mapPairs_bcDelta m)))) = bcPhi m := by
  refine _root_.Equiv.ext (fun x => Subtype.ext ?_)
  by_cases hx : x.val < m
  · -- low labels: the surviving left slot
    have hz : finSumFinEquiv.symm x =
        (Sum.inl ⟨x.val, hx⟩ : Fin m ⊕ Fin m) := by
      conv_lhs => rw [show x = Fin.castAdd m ⟨x.val, hx⟩ from
        Fin.ext rfl]
      exact finSumFinEquiv_symm_apply_castAdd _
    have wpf : ∀ p ∈ interfacePairs m m m,
        (Sum.inl ⟨x.val, by omega⟩ :
          Fin (m + m) ⊕ Fin (m + m)) ≠ p.1 ∧
        (Sum.inl ⟨x.val, by omega⟩ :
          Fin (m + m) ⊕ Fin (m + m)) ≠ p.2 :=
      (forall_ne_iff_not_mem_flat _ _).mpr (by
        rw [mem_interfacePairs_flat]
        rintro (⟨a, ha, hm⟩ | ⟨b, hb, _⟩)
        · rw [show a = ⟨x.val, by omega⟩ from
            (Sum.inl.inj ha).symm] at hm
          exact absurd hm (by simpa using hx)
        · exact Sum.inl_ne_inr hb)
    have hw : interfaceSurvEquiv m m m
        ⟨Sum.inl ⟨x.val, by omega⟩, wpf⟩ =
        (Sum.inl ⟨x.val, hx⟩ : Fin m ⊕ Fin m) :=
      interfaceSurvEquiv_inl m m m _ _ rfl hx
    have hy : (((interfaceSurvEquiv m m m).trans
        finSumFinEquiv).symm x) =
        ⟨Sum.inl ⟨x.val, by omega⟩, wpf⟩ := by
      change (interfaceSurvEquiv m m m).symm
        (finSumFinEquiv.symm x) = _
      rw [hz]
      exact (_root_.Equiv.symm_apply_eq _).mpr hw.symm
    have hval := congrArg Subtype.val hy
    have hbc : (bcPhiFun m x).val =
        Sum.inl ⟨x.val, by omega⟩ :=
      congrArg Subtype.val (dite_eq_left hx)
    change bcDelta m ((((interfaceSurvEquiv m m m).trans
        finSumFinEquiv).symm x)).val = (bcPhiFun m x).val
    rw [hval, hbc]
    exact congrArg Sum.inl (Fin.ext rfl)
  · -- high labels: the surviving right slot
    have hz : finSumFinEquiv.symm x =
        (Sum.inr ⟨x.val - m, by have := x.isLt; omega⟩ :
          Fin m ⊕ Fin m) := by
      conv_lhs => rw [show x = Fin.natAdd m
        ⟨x.val - m, by have := x.isLt; omega⟩ from
        Fin.ext (by change x.val = m + (x.val - m); omega)]
      exact finSumFinEquiv_symm_apply_natAdd _
    have wpf : ∀ p ∈ interfacePairs m m m,
        (Sum.inr ⟨x.val, x.isLt⟩ :
          Fin (m + m) ⊕ Fin (m + m)) ≠ p.1 ∧
        (Sum.inr ⟨x.val, x.isLt⟩ :
          Fin (m + m) ⊕ Fin (m + m)) ≠ p.2 :=
      (forall_ne_iff_not_mem_flat _ _).mpr (by
        rw [mem_interfacePairs_flat]
        rintro (⟨a, ha, _⟩ | ⟨b, hb, hm⟩)
        · exact Sum.inr_ne_inl ha
        · rw [show b = ⟨x.val, x.isLt⟩ from
            (Sum.inr.inj hb).symm] at hm
          simp only [] at hm
          omega)
    have hw : interfaceSurvEquiv m m m
        ⟨Sum.inr ⟨x.val, x.isLt⟩, wpf⟩ =
        (Sum.inr ⟨x.val - m, by have := x.isLt; omega⟩ :
          Fin m ⊕ Fin m) :=
      interfaceSurvEquiv_inr m m m _ _ rfl (by omega)
    have hy : (((interfaceSurvEquiv m m m).trans
        finSumFinEquiv).symm x) =
        ⟨Sum.inr ⟨x.val, x.isLt⟩, wpf⟩ := by
      change (interfaceSurvEquiv m m m).symm
        (finSumFinEquiv.symm x) = _
      rw [hz]
      exact (_root_.Equiv.symm_apply_eq _).mpr hw.symm
    have hval := congrArg Subtype.val hy
    have hbc : (bcPhiFun m x).val =
        Sum.inr ⟨x.val - m, by have := x.isLt; omega⟩ :=
      congrArg Subtype.val (dite_eq_right hx)
    change bcDelta m ((((interfaceSurvEquiv m m m).trans
        finSumFinEquiv).symm x)).val = (bcPhiFun m x).val
    rw [hval, hbc]
    refine congrArg Sum.inr (Fin.ext ?_)
    change ((transposeEquiv m m).symm.trans
      (finCongr (by omega : m + m = (m + m) + 0))
        ⟨x.val, x.isLt⟩).val = x.val - m
    rw [_root_.Equiv.trans_apply,
      show (transposeEquiv m m).symm = transposeEquiv m m from
        transposeEquiv_symm m m,
      show (⟨x.val, x.isLt⟩ : Fin (m + m)) =
        ⟨m + (x.val - m), by have := x.isLt; omega⟩ from
        Fin.ext (by change x.val = m + (x.val - m); omega),
      transposeEquiv_high m m (x.val - m)
        (by have := x.isLt; omega) (by have := x.isLt; omega)
        (by have := x.isLt; omega)]
    rfl

/-- **The high-block stage**: gluing the high-block pairs in the
closure ambient is the identity composition against the bundle,
hence the fragment itself. -/
noncomputable def bcStageA (V : Fragment (Fin (m + m))) :
    (Fragment.glueList (bcAmbient m V) (highCross m)
        (highCross_wf m)).Equiv (V.relabel (bcPhi m)) := by
  have C1 := Fragment.glueListCongr (bcAmbientEquiv m V)
    (highCross m) (highCross_wf m)
  have C2 := Fragment.glueListEqEquiv
    ((bcAmbient2 m V).relabel (bcDelta m))
    (mapPairs_bcDelta m)
    (Fragment.mapPairs_wf (bcDelta m) _
      (interfacePairs_wf m m m))
    (highCross_wf m)
    (List.Perm.of_eq (mapPairs_bcDelta m))
  have C3 := Fragment.glueListRelabel (bcAmbient2 m V)
    (bcDelta m) (interfacePairs m m m)
    (interfacePairs_wf m m m)
  have C4 := Fragment.Equiv.relabelFlip
    (composeNormal V
      ((strandBundle m).relabel (transposeEquiv m m)))
  have C5 := Fragment.composeCongr (Fragment.Equiv.refl V)
    (strandBundleTranspose m)
  have C6 := composeStrandBundleRight m m V
  have D1 := C4.trans
    (Fragment.Equiv.relabelCongr (C5.trans C6) _)
  have D2 := C3.trans
    ((Fragment.Equiv.relabelCongr D1 _).trans
      (Fragment.Equiv.relabelTrans V _ _))
  have D3 := C2.symm.trans
    ((Fragment.Equiv.relabelCongr D2 _).trans
      (Fragment.Equiv.relabelTrans V _ _))
  exact C1.trans (D3.trans
    (Fragment.Equiv.relabelEq V (bcPhi_eq m)))

/-! ### The lifted low-block pairs are the straight matching -/

/-- Lifting a pair list past an earlier fold keeps its length. -/
theorem liftPairs_length {α : Type} (ps : List (α × α)) :
    ∀ (qs : List (α × α)) (h : Fragment.PairsSepAll ps qs),
      (Fragment.liftPairs ps qs h).length = qs.length
  | [], _ => rfl
  | _ :: qs, _ => congrArg Nat.succ (liftPairs_length ps qs _)

/-- And keeps each pair's underlying labels. -/
theorem liftPairs_getElem_val {α : Type} (ps : List (α × α)) :
    ∀ (qs : List (α × α)) (h : Fragment.PairsSepAll ps qs) (j : ℕ)
      (hj : j < (Fragment.liftPairs ps qs h).length)
      (hj' : j < qs.length),
      ((Fragment.liftPairs ps qs h)[j]'hj).1.val =
          (qs[j]'hj').1 ∧
        ((Fragment.liftPairs ps qs h)[j]'hj).2.val =
          (qs[j]'hj').2
  | [], _, j, _, hj' => absurd hj' (by simp)
  | _ :: _, _, 0, _, _ => ⟨rfl, rfl⟩
  | _ :: qs, h, j + 1, hj, hj' =>
    liftPairs_getElem_val ps qs _ j
      (by simpa [Fragment.liftPairs] using hj)
      (by simpa using hj')

/-- The inverse survivor identification on left values. -/
theorem bcPhi_symm_val_inl
    (s : Fragment.FoldSurviving
      (Fin (0 + (m + m)) ⊕ Fin ((m + m) + 0)) (highCross m))
    (a : Fin (0 + (m + m))) (hs : s.val = Sum.inl a) :
    (bcPhi m).symm s = ⟨a.val, by have := a.isLt; omega⟩ := by
  obtain ⟨sv, hp⟩ := s
  subst hs
  exact Fin.ext rfl

/-- The inverse survivor identification on right values. -/
theorem bcPhi_symm_val_inr
    (s : Fragment.FoldSurviving
      (Fin (0 + (m + m)) ⊕ Fin ((m + m) + 0)) (highCross m))
    (b : Fin ((m + m) + 0)) (hs : s.val = Sum.inr b)
    (hb : b.val < m) :
    (bcPhi m).symm s = ⟨m + b.val, by omega⟩ := by
  obtain ⟨sv, hp⟩ := s
  subst hs
  exact Fin.ext rfl

/-- Read through the high stage's survivor identification, the
lifted low block is the straight matching reversed. -/
theorem mapPairs_bcPhi_lift :
    Fragment.mapPairs (bcPhi m).symm
      (Fragment.liftPairs (highCross m) (lowCross m)
        ((splitCross_wf m).append_sep)) =
      (matchPairs m).reverse := by
  have hlcl : (lowCross m).length = m := by
    simp only [lowCross, List.length_map, List.length_reverse,
      List.length_finRange]
  apply List.ext_getElem
  · rw [mapPairs_length, liftPairs_length, List.length_reverse,
      matchPairs_length, hlcl]
  intro j hj hj'
  have hjm : j < m := by
    rw [List.length_reverse, matchPairs_length] at hj'
    exact hj'
  have hjl : j < (lowCross m).length := by omega
  have hlift : j < (Fragment.liftPairs (highCross m)
      (lowCross m) ((splitCross_wf m).append_sep)).length := by
    rw [liftPairs_length]
    omega
  rw [mapPairs_getElem _ _ j hj hlift]
  obtain ⟨h1, h2⟩ := liftPairs_getElem_val (highCross m)
    (lowCross m) ((splitCross_wf m).append_sep) j hlift hjl
  have hlow : (lowCross m)[j]'hjl =
      (Sum.inl ⟨m - 1 - j, by omega⟩,
       Sum.inr ⟨m - 1 - j, by omega⟩) := by
    simp only [lowCross, List.getElem_map,
      List.getElem_reverse, List.length_finRange,
      List.getElem_finRange]
    refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
      (congrArg Sum.inr (Fin.ext ?_)) <;> simp
  have hmrev : (matchPairs m).reverse =
      (List.finRange m).reverse.map
        (fun k => (Fin.castAdd m k, Fin.natAdd m k)) := by
    unfold matchPairs
    exact List.map_reverse.symm
  have hrev : ((matchPairs m).reverse)[j]'hj' =
      (Fin.castAdd m ⟨m - 1 - j, by omega⟩,
       Fin.natAdd m ⟨m - 1 - j, by omega⟩) := by
    rw [List.getElem_of_eq hmrev]
    simp only [List.getElem_map, List.getElem_reverse,
      List.length_finRange, List.getElem_finRange]
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp
  rw [hrev]
  have hs1 := bcPhi_symm_val_inl m _ ⟨m - 1 - j, by omega⟩
    (h1.trans (congrArg Prod.fst hlow))
  have hs2 := bcPhi_symm_val_inr m _ ⟨m - 1 - j, by omega⟩
    (h2.trans (congrArg Prod.snd hlow)) (by
      change m - 1 - j < m
      omega)
  rw [hs1, hs2]
  exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)

/-- Equivalently, the lifted low block is the transported straight
matching — the identification the closure theorem runs on. -/
theorem lift_eq_mapPairs :
    Fragment.liftPairs (highCross m) (lowCross m)
      ((splitCross_wf m).append_sep) =
      Fragment.mapPairs (bcPhi m) ((matchPairs m).reverse) := by
  have h := congrArg (Fragment.mapPairs (bcPhi m))
    (mapPairs_bcPhi_lift m)
  rw [mapPairs_symm_cancel (bcPhi m)] at h
  exact h

attribute [instance] matchPairs_surv_isEmpty

-- The closure is matched with the self-glue along
-- the straight matching, which unfolds the glue list.
/-- **The bundle closure is the straight-matching self-glue**:
the full closure of an `(m + m)`-fragment against the strand
bundle is the self-glue of its straight matching. -/
noncomputable def pairCloseStrandBundle
    (V : Fragment (Fin (m + m))) :
    (pairClose V (strandBundle m)).Equiv
      ((Fragment.glueList V (matchPairs m)
          (matchPairs_wf m)).relabel
        (_root_.Equiv.equivOfIsEmpty _ _)) := by
  change ((V.relabel
      (finCongr (by omega : m + m = 0 + (m + m)))).compose
    ((strandBundle m).relabel
      (finCongr (by omega : m + m = (m + m) + 0)))).Equiv _
  have wfRev : Fragment.PairsWF ((matchPairs m).reverse) :=
    (matchPairs_wf m).perm (List.reverse_perm (matchPairs m)).symm
  have F1 := Fragment.Equiv.relabelFlip'
    (Fragment.glueListEqEquiv (bcAmbient m V)
      (interfacePairs_split m)
      (interfacePairs_wf 0 (m + m) 0) (splitCross_wf m)
      (List.Perm.of_eq (interfacePairs_split m)))
  have F2 := Fragment.glueListAppend (bcAmbient m V)
    (highCross m) (lowCross m) (splitCross_wf m)
  have F3 := Fragment.glueListCongr (bcStageA m V)
    (Fragment.liftPairs (highCross m) (lowCross m)
      ((splitCross_wf m).append_sep))
    (Fragment.liftPairs_wf (highCross m) (lowCross m)
      (splitCross_wf m).append_right
      (splitCross_wf m).append_sep)
  have F4 := Fragment.Equiv.relabelFlip'
    (Fragment.glueListEqEquiv (V.relabel (bcPhi m))
      (lift_eq_mapPairs m)
      (Fragment.liftPairs_wf (highCross m) (lowCross m)
        (splitCross_wf m).append_right
        (splitCross_wf m).append_sep)
      (Fragment.mapPairs_wf (bcPhi m) _ wfRev)
      (List.Perm.of_eq (lift_eq_mapPairs m)))
  have F5 := Fragment.glueListRelabel V (bcPhi m)
    ((matchPairs m).reverse) wfRev
  have F6 := Fragment.glueListPerm V
    (List.reverse_perm (matchPairs m)) wfRev
  -- the low-stage chain, from the appended base to the matching
  have G1 := F3.trans (F4.trans
    (Fragment.Equiv.relabelCongr
      (F5.trans (Fragment.Equiv.relabelCongr
        (F6.trans (Fragment.Equiv.relabelCongr
          (Fragment.glueListProofIrrel V (matchPairs m) _
            (matchPairs_wf m)) _)) _)) _))
  -- fold the whole tower and collapse the empty relabels
  refine (composeNormal _ _).trans ?_
  refine (Fragment.Equiv.relabelCongr
    (F1.trans (Fragment.Equiv.relabelCongr
      (F2.trans (Fragment.Equiv.relabelCongr G1 _)) _)) _).trans
    ?_
  -- now everything is nested relabels of the matching self-glue;
  -- merge the six layers innermost-first, then collapse over the
  -- empty survivor type
  refine (Fragment.Equiv.relabelCongr (Fragment.Equiv.relabelCongr
    (Fragment.Equiv.relabelCongr (Fragment.Equiv.relabelCongr
      (Fragment.Equiv.relabelTrans _ _ _) _) _) _) _).trans ?_
  refine (Fragment.Equiv.relabelCongr (Fragment.Equiv.relabelCongr
    (Fragment.Equiv.relabelCongr
      (Fragment.Equiv.relabelTrans _ _ _) _) _) _).trans ?_
  refine (Fragment.Equiv.relabelCongr (Fragment.Equiv.relabelCongr
    (Fragment.Equiv.relabelTrans _ _ _) _) _).trans ?_
  refine (Fragment.Equiv.relabelCongr
    (Fragment.Equiv.relabelTrans _ _ _) _).trans ?_
  refine (Fragment.Equiv.relabelTrans _ _ _).trans ?_
  exact Fragment.Equiv.relabelEq _
    (_root_.Equiv.ext (fun s =>
      ((matchPairs_surv_isEmpty m).false s).elim))

end BundleClose

end RS
