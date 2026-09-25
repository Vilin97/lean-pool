/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.IdentityLaw

/-!
# The right identity law: stage equivalences

Mirror of `RS.Novel.Skein.IdentityLaw` (the left identity law).  Composing
with a strand bundle on the right is the identity up to fragment
equivalence.  The proof runs by descending induction through
`glueInterface` with the invariant that the stage-`t'` fragment is
equivalent to `F.disjUnion (strandBundle t')` relabelled along a
stage equivalence relocating the not-yet-glued interface labels and
the strand labels into the two output blocks.

The transformation: where the left law places the strand bundle in
the left factor (its outgoing ends glued to F's leading interface
labels), the right law places F in the left factor and the strand
bundle in the right (interface pairs `(Sum.inl (s + k), Sum.inr k)`
hit F's trailing labels and the bundle's incoming labels; the
bundle's outgoing labels survive and become the output's trailing
labels).

The stage equivalence maps `Fin (s + u) ⊕ Fin (t' + t')` to
`Fin (s + t') ⊕ Fin (t' + u)`.  Block decomposition:
  D = Fin s (F's leading/outer labels)
  C = Fin t' (F's not-yet-glued trailing interface labels)
  B = Fin (u - t') (F's already-glued trailing labels)
  A = Fin t' (strand-bundle incoming ends)
  A' = Fin t' (strand-bundle outgoing ends)
The shuffle: `((D ⊕ C) ⊕ B) ⊕ (A ⊕ A') ≃ (D ⊕ C) ⊕ ((A ⊕ A') ⊕ B)`.
-/

@[expose] public section

namespace RS

/-- The stage relabelling for the right identity law.  On the left
output, F's outer labels and the not-yet-glued interface labels; on
the right output, the strand-bundle labels followed by F's
already-glued trailing labels. -/
def stageEquivR (s t' u : ℕ) (ht : t' ≤ u) :
    Fin (s + u) ⊕ Fin (t' + t') ≃ Fin (s + t') ⊕ Fin (t' + u) where
  toFun x := match x with
    | Sum.inl ℓ =>
        if h : ℓ.val < s + t' then Sum.inl ⟨ℓ.val, h⟩
        else Sum.inr ⟨t' + (ℓ.val - s), by omega⟩
    | Sum.inr a => Sum.inr ⟨a.val, by omega⟩
  invFun y := match y with
    | Sum.inl j => Sum.inl ⟨j.val, by omega⟩
    | Sum.inr k =>
        if h : k.val < t' + t' then Sum.inr ⟨k.val, h⟩
        else Sum.inl ⟨s + (k.val - t'), by omega⟩
  left_inv x := by
    rcases x with ℓ | a
    · -- Sum.inl ℓ
      simp only
      by_cases h : ℓ.val < s + t'
      · rw [dite_eq_left h]
      · simp only
        [dite_eq_right h, dite_eq_right (show ¬ (t' + (ℓ.val - s) < t' + t') from by omega)]
        exact congrArg Sum.inl (Fin.ext (by simp; omega))
    · -- Sum.inr a
      simp only
      rw [dite_eq_left a.isLt]
  right_inv y := by
    rcases y with j | k
    · -- Sum.inl j
      simp only
      rw [dite_eq_left j.isLt]
    · -- Sum.inr k
      simp only
      by_cases h : k.val < t' + t'
      · rw [dite_eq_left h]
      · simp only
        [dite_eq_right h, dite_eq_right (show ¬ (s + (k.val - t') < s + t') from by omega)]
        exact congrArg Sum.inr (Fin.ext (by simp; omega))

/-! ### Label evaluations -/

/-- Evaluation of the right stage equivalence on a left label (F's
labels): a label below `s + t'` stays left; a label at or above
`s + t'` relocates to the right block. -/
theorem stageEquivR_inl (s t' u : ℕ) (ht : t' ≤ u) (ℓ : Fin (s + u)) :
    stageEquivR s t' u ht (Sum.inl ℓ) =
      if h : ℓ.val < s + t' then Sum.inl ⟨ℓ.val, h⟩
      else Sum.inr ⟨t' + (ℓ.val - s), by omega⟩ := rfl

/-- Evaluation of the right stage equivalence on a right label
(strand-bundle labels): it maps to the right output block at the
same index. -/
theorem stageEquivR_inr (s t' u : ℕ) (ht : t' ≤ u) (a : Fin (t' + t')) :
    stageEquivR s t' u ht (Sum.inr a) =
      Sum.inr ⟨a.val, by omega⟩ := rfl

/-! ### The base case -/

/-- Evaluation of the stage-zero right equivalence on a left label:
a leading label stays left; a trailing label relocates to the right
block. -/
theorem stageEquivR_zero_inl (s u : ℕ) (ℓ : Fin (s + u)) :
    stageEquivR s 0 u (Nat.zero_le u) (Sum.inl ℓ) =
      if h : ℓ.val < s then Sum.inl ⟨ℓ.val, by omega⟩
      else Sum.inr ⟨ℓ.val - s, by omega⟩ := by
  rw [stageEquivR_inl]
  by_cases h : ℓ.val < s
  · rw [dite_eq_left (show ℓ.val < s + 0 from by omega), dite_eq_left h]
  · rw [dite_eq_right (show ¬ ℓ.val < s + 0 from by omega), dite_eq_right h]
    exact congrArg Sum.inr (Fin.ext (by simp))

/-- The base case of the right identity law: after zero interface
gluings, the triply-relabelled F/(strand-0) union is equivalent to
F. -/
noncomputable def stageZeroEquivR (s u : ℕ) (F : Fragment (Fin (s + u))) :
    ((glueInterface s 0 u ((F.disjUnion (strandBundle 0)).relabel
      (stageEquivR s 0 u (Nat.zero_le u)))).relabel finSumFinEquiv).Equiv F
        where
  flagEquiv := Equiv.sumEmpty _ _
  vertexEquiv := Equiv.sumEmpty _ _
  attach_comm f := by
    rcases f with g | ⟨⟨k, hk⟩, _⟩
    · -- inl g (F-flag)
      change F.attach ((Equiv.sumEmpty _ _) (Sum.inl g)) =
        (((glueInterface s 0 u ((F.disjUnion (strandBundle 0)).relabel
          (stageEquivR s 0 u (Nat.zero_le u)))).relabel finSumFinEquiv).attach
          (Sum.inl g)).map (Equiv.sumEmpty _ _) id
      simp only [Equiv.sumEmpty_apply_inl]
      change F.attach g =
        (((((F.attach g).map Sum.inl Sum.inl).map id
          (stageEquivR s 0 u (Nat.zero_le u))).map id
          (Equiv.sumCongr (finCongr (by omega : s + 0 = s))
            (finCongr (by omega : 0 + u = u)))).map id finSumFinEquiv).map
          (Equiv.sumEmpty _ _) id
      rcases ha : F.attach g with v | ℓ
      · simp
      · simp only [Sum.map_inr]
        congr 1
        rw [stageEquivR_zero_inl]
        split
        · rename_i h
          simp [finSumFinEquiv_apply_left]
        · rename_i h
          simp [finSumFinEquiv_apply_right, Fin.ext_iff]
          omega
    · -- inr (strand-0 flag) — impossible
      exact absurd hk (Nat.not_lt_zero k)
  pairing_comm f := by
    rcases f with g | x
    · rfl
    · exact (IsEmpty.false x).elim
  circles_eq := rfl

/-! ### The descent step -/

/-- The boundary flag at the left interface label in the relabelled
disjoint union: it is F's boundary flag at `s + t'`. -/
theorem stageStepR_leftBoundary (s t' u : ℕ) (ht : t' + 1 ≤ u)
    (F : Fragment (Fin (s + u))) :
    ((F.disjUnion (strandBundle (t' + 1))).relabel
      (stageEquivR s (t' + 1) u ht)).boundaryFlag
      (Sum.inl ⟨s + t', by omega⟩) =
    Sum.inl (F.boundaryFlag ⟨s + t', by omega⟩) := by
  change (F.disjUnion (strandBundle (t' + 1))).boundaryFlag
    ((stageEquivR s (t' + 1) u ht).symm (Sum.inl ⟨s + t', by omega⟩)) =
    Sum.inl (F.boundaryFlag ⟨s + t', by omega⟩)
  have hsymm : (stageEquivR s (t' + 1) u ht).symm (Sum.inl ⟨s + t', by omega⟩) =
      Sum.inl ⟨s + t', by omega⟩ := by
    rw [Equiv.symm_apply_eq, stageEquivR_inl]
    rw [dite_eq_left (show (s + t' : ℕ) < s + (t' + 1) from by omega)]
  rw [hsymm]
  rfl

/-- The boundary flag at the right interface label in the relabelled
disjoint union: it is the incoming end of strand `t'`. -/
theorem stageStepR_rightBoundary (s t' u : ℕ) (ht : t' + 1 ≤ u)
    (F : Fragment (Fin (s + u))) :
    ((F.disjUnion (strandBundle (t' + 1))).relabel
      (stageEquivR s (t' + 1) u ht)).boundaryFlag
      (Sum.inr ⟨t', by omega⟩) =
    Sum.inr (⟨t', by omega⟩, false) := by
  change (F.disjUnion (strandBundle (t' + 1))).boundaryFlag
    ((stageEquivR s (t' + 1) u ht).symm (Sum.inr ⟨t', by omega⟩)) =
    Sum.inr (⟨t', by omega⟩, false)
  have hsymm : (stageEquivR s (t' + 1) u ht).symm (Sum.inr ⟨t', by omega⟩) =
      Sum.inr ⟨t', by omega⟩ := by
    rw [Equiv.symm_apply_eq, stageEquivR_inr]
  rw [hsymm]
  exact congrArg Sum.inr (strandBundle_boundaryFlag_low (t' + 1) ⟨t', by omega⟩
    (Nat.lt_add_one t'))

/-- The glue in the descent step is always the open case. -/
theorem stageStepR_hopen (s t' u : ℕ) (ht : t' + 1 ≤ u)
    (F : Fragment (Fin (s + u))) :
    ((F.disjUnion (strandBundle (t' + 1))).relabel
      (stageEquivR s (t' + 1) u ht)).pairing
      (((F.disjUnion (strandBundle (t' + 1))).relabel
        (stageEquivR s (t' + 1) u ht)).boundaryFlag
        (Sum.inl ⟨s + t', by omega⟩)) ≠
    ((F.disjUnion (strandBundle (t' + 1))).relabel
      (stageEquivR s (t' + 1) u ht)).boundaryFlag
      (Sum.inr ⟨t', by omega⟩) := by
  rw [stageStepR_leftBoundary, stageStepR_rightBoundary]
  exact (nomatch ·)

/-- The pairing partner of the right boundary flag in the relabelled
fragment: it is `(t', true)`, the outgoing end of strand `t'`. -/
theorem stageStepR_rightPairing (s t' u : ℕ) (ht : t' + 1 ≤ u)
    (F : Fragment (Fin (s + u))) :
    ((F.disjUnion (strandBundle (t' + 1))).relabel
      (stageEquivR s (t' + 1) u ht)).pairing
      (Sum.inr (⟨t', by omega⟩, false)) =
    Sum.inr (⟨t', by omega⟩, true) := rfl

/-- The flag equivalence for the descent step: surviving flags of the
open glue at stage `t' + 1` correspond to flags of the stage-`t'`
disjoint union `F.disjUnion (strandBundle t')`. -/
noncomputable def stageStepFlagEquivR (s t' u : ℕ) (ht : t' + 1 ≤ u)
    (F : Fragment (Fin (s + u))) :
    Fragment.SurvivingFlag
      ((F.disjUnion (strandBundle (t' + 1))).relabel (stageEquivR s (t' + 1) u
        ht))
      (Sum.inl ⟨s + t', by omega⟩) (Sum.inr ⟨t', by omega⟩) ≃
    F.Flag ⊕ (Fin t' × Bool) where
  toFun x :=
    match x.val with
    | Sum.inl g => Sum.inl g
    | Sum.inr (⟨k, _⟩, b) =>
        if hlt : k < t' then Sum.inr (⟨k, hlt⟩, b)
        else Sum.inl (F.boundaryFlag ⟨s + t', by omega⟩)
  invFun y :=
    match y with
    | Sum.inl g =>
        if hg : g = F.boundaryFlag ⟨s + t', by omega⟩ then
          ⟨Sum.inr (⟨t', by omega⟩, true), by
            refine ⟨fun h => ?_, fun h => ?_⟩
            · rw [stageStepR_leftBoundary] at h; simp at h
            · rw [stageStepR_rightBoundary] at h
              have hbeq : (true : Bool) = false :=
                congrArg Prod.snd (Sum.inr.inj h)
              exact absurd hbeq (Ne.symm Bool.false_ne_true)⟩
        else
          ⟨Sum.inl g, by
            refine ⟨fun h => ?_, fun h => ?_⟩
            · rw [stageStepR_leftBoundary] at h
              exact hg (Sum.inl.inj h)
            · rw [stageStepR_rightBoundary] at h; simp at h⟩
    | Sum.inr (⟨k, hk⟩, b) =>
        ⟨Sum.inr (⟨k, by omega⟩, b), by
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rw [stageStepR_leftBoundary] at h; simp at h
          · rw [stageStepR_rightBoundary] at h
            have hkeq : k = t' := congrArg Fin.val
              (congrArg Prod.fst (Sum.inr.inj h))
            omega⟩
  left_inv x := by
    obtain ⟨f, hne⟩ := x
    rcases f with g | ⟨⟨k, hk⟩, b⟩
    · -- f = Sum.inl g
      dsimp only
      have hg : g ≠ F.boundaryFlag ⟨s + t', by omega⟩ := by
        intro heq
        exact hne.1 (by
          rw [stageStepR_leftBoundary]
          exact congrArg Sum.inl heq)
      simp only [dite_eq_right hg]
    · -- f = Sum.inr (⟨k, hk⟩, b)
      by_cases hlt : k < t'
      · simp only [dite_eq_left hlt]
      · have hk_eq : k = t' := by omega
        have hb : b = true := by
          by_contra hbf
          have hbfalse : b = false := by cases b <;> simp_all
          exact hne.2 (by
            rw [stageStepR_rightBoundary]
            exact hk_eq ▸ hbfalse ▸ congrArg Sum.inr (Prod.ext (Fin.ext rfl)
              rfl))
        simp only [dite_eq_right hlt, dite_true]
        exact Subtype.ext (hk_eq ▸ hb ▸ congrArg Sum.inr (Prod.ext (Fin.ext rfl)
          rfl))
  right_inv y := by
    match y with
    | Sum.inl g =>
      dsimp only
      by_cases hg : g = F.boundaryFlag ⟨s + t', by omega⟩
      · simp only [dite_eq_left hg, dite_eq_right (show ¬ (t' : ℕ) < t' from Nat.lt_irrefl
        t')]
        exact congrArg Sum.inl hg.symm
      · simp only [dite_eq_right hg]
    | Sum.inr (⟨k, hk⟩, b) =>
      simp only [dite_eq_left hk]

/-! ### The stage step equivalence -/

/-- The relabelled fragment-strand union before the next right identity glue. -/
abbrev baseFragmentR (s t' u : ℕ) (ht : t' + 1 ≤ u)
    (F : Fragment (Fin (s + u))) :=
  (F.disjUnion (strandBundle (t' + 1))).relabel (stageEquivR s (t' + 1) u ht)

/-- The relabelled fragment-strand union at the target stage of right identity descent. -/
abbrev targetFragmentR (s t' u : ℕ) (ht' : t' ≤ u)
    (F : Fragment (Fin (s + u))) :=
  (F.disjUnion (strandBundle t')).relabel (stageEquivR s t' u ht')

/-- The source fragment obtained by one open glue in the right identity descent. -/
noncomputable abbrev sourceFragmentR (s t' u : ℕ) (ht : t' + 1 ≤ u)
    (F : Fragment (Fin (s + u))) :=
  ((baseFragmentR s t' u ht F).gluePairOpen
    (Sum.inl ⟨s + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
    (by simp) (by exact stageStepR_hopen s t' u ht F)).relabel (interfaceStepEquiv s t'
      u)

private theorem stageStepR_attach_inl (s t' u : ℕ) (ht : t' + 1 ≤ u)
    (F : Fragment (Fin (s + u)))
    (g : F.Flag)
    (hne : (Sum.inl g : (baseFragmentR s t' u ht F).Flag) ≠
      (baseFragmentR s t' u ht F).boundaryFlag (Sum.inl ⟨s + t', by omega⟩) ∧
      (Sum.inl g : (baseFragmentR s t' u ht F).Flag) ≠
      (baseFragmentR s t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩)) :
    (targetFragmentR s t' u (by omega) F).attach
      (stageStepFlagEquivR s t' u ht F ⟨Sum.inl g, hne⟩) =
      ((sourceFragmentR s t' u ht F).attach ⟨Sum.inl g, hne⟩).map (Equiv.refl _) id := by
  have hg_ne : g ≠ F.boundaryFlag ⟨s + t', by omega⟩ := by
    intro heq
    exact hne.1
      (by rw [stageStepR_leftBoundary]; exact congrArg Sum.inl heq)
  have hflag : (stageStepFlagEquivR s t' u ht F) ⟨Sum.inl g, hne⟩ = Sum.inl
    g := rfl
  rcases ha : F.attach g with v | ℓ
  · -- F.attach g = Sum.inl v (vertex)
    set common : (targetFragmentR s t' u (by omega) F).Vertex ⊕
        (Fin (s + t') ⊕ Fin (t' + u)) := Sum.inl (Sum.inl v)
    have hLHS : (targetFragmentR s t' u (by omega) F).attach (Sum.inl g) =
        common := by
      change ((F.disjUnion (strandBundle t')).attach (Sum.inl g)).map id
        (stageEquivR s t' u _) = _
      change ((F.attach g).map Sum.inl Sum.inl).map id (stageEquivR s t' u
        _) = _
      rw [ha]; rfl
    have hRHS : (sourceFragmentR s t' u ht F).attach ⟨Sum.inl g, hne⟩ =
        common := by
      change ((Fragment.glueAttach (baseFragmentR s t' u ht F)
          (Sum.inl ⟨s + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
          ⟨Sum.inl g, hne⟩).map id (interfaceStepEquiv s t' u)) = _
      have hba : (baseFragmentR s t' u ht F).attach (Sum.inl g) =
          Sum.inl (Sum.inl v) := by
        change ((F.disjUnion (strandBundle (t' + 1))).attach (Sum.inl
          g)).map id
          (stageEquivR s (t' + 1) u ht) = _
        change ((F.attach g).map Sum.inl Sum.inl).map id (stageEquivR s (t'
          + 1) u ht) = _
        rw [ha]; rfl
      refine Fragment.glueAttach_cases _ (fun v' hv' => ?_)
        (fun ℓ' hℓ' => ?_)
      · simp only [Sum.map_inl, id_eq]
        exact congrArg Sum.inl (Sum.inl.inj (hv'.symm.trans hba))
      · obtain ⟨ℓ', _hs₁, _hs₂⟩ := ℓ'
        exact absurd (hℓ'.symm.trans hba) (nomatch ·)
    exact (hflag ▸ hLHS).trans
      (by rw [hRHS]; rfl : ((sourceFragmentR s t' u ht F).attach
        ⟨Sum.inl g, hne⟩).map (Equiv.refl _) id = common).symm
  · -- F.attach g = Sum.inr ℓ (label)
    have hℓ_ne_st' : ℓ.val ≠ s + t' := by
      intro heq
      have hatt : F.attach g = Sum.inr ⟨s + t', by omega⟩ := by
        exact ha.trans (congrArg Sum.inr (Fin.ext heq))
      exact hg_ne (F.eq_boundaryFlag ⟨s + t', by omega⟩ g hatt)
    by_cases hℓ_lt : ℓ.val < s + t'
    · -- ℓ.val < s + t'
      set common : (targetFragmentR s t' u (by omega) F).Vertex ⊕
          (Fin (s + t') ⊕ Fin (t' + u)) := Sum.inr
            (Sum.inl ⟨ℓ.val, by omega⟩)
      have hLHS : (targetFragmentR s t' u (by omega) F).attach (Sum.inl g) =
          common := by
        change ((F.disjUnion (strandBundle t')).attach (Sum.inl g)).map id
          (stageEquivR s t' u _) = _
        change ((F.attach g).map Sum.inl Sum.inl).map id (stageEquivR s t' u
          _) = _
        rw [ha]; simp only [Sum.map_inr]; refine congrArg Sum.inr ?_
        rw [stageEquivR_inl, dite_eq_left hℓ_lt]
      have hRHS : (sourceFragmentR s t' u ht F).attach ⟨Sum.inl g, hne⟩ =
          common := by
        change ((Fragment.glueAttach (baseFragmentR s t' u ht F)
            (Sum.inl ⟨s + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
            ⟨Sum.inl g, hne⟩).map id (interfaceStepEquiv s t' u)) = _
        have hba : (baseFragmentR s t' u ht F).attach (Sum.inl g) =
            Sum.inr (Sum.inl ⟨ℓ.val, by omega⟩) := by
          change ((F.disjUnion (strandBundle (t' + 1))).attach (Sum.inl
            g)).map id
            (stageEquivR s (t' + 1) u ht) = _
          change ((F.attach g).map Sum.inl Sum.inl).map id
            (stageEquivR s (t' + 1) u ht) = _
          rw [ha]; simp only [Sum.map_inr]; refine congrArg Sum.inr ?_
          rw [stageEquivR_inl,
            dite_eq_left (show ℓ.val < s + (t' + 1) from by omega)]
        refine Fragment.glueAttach_cases _ (fun v' hv' => ?_)
          (fun ℓ' hℓ' => ?_)
        · exact absurd (hv'.symm.trans hba) (nomatch ·)
        · obtain ⟨ℓ', _hs₁, _hs₂⟩ := ℓ'
          simp only [Sum.map_inr]
          have hℓ'_eq : ℓ' = Sum.inl ⟨ℓ.val, by omega⟩ :=
            Sum.inr.inj (hℓ'.symm.trans hba)
          subst hℓ'_eq; refine congrArg Sum.inr ?_
          exact interfaceStepEquiv_eval_inl s t' u ℓ.val (by omega)
      exact (hflag ▸ hLHS).trans
        (by rw [hRHS]; rfl : ((sourceFragmentR s t' u ht F).attach
          ⟨Sum.inl g, hne⟩).map (Equiv.refl _) id = common).symm
    · -- ℓ.val > s + t'
      have hℓ_gt : s + t' < ℓ.val := by omega
      set common : (targetFragmentR s t' u (by omega) F).Vertex ⊕
          (Fin (s + t') ⊕ Fin (t' + u)) :=
        Sum.inr (Sum.inr ⟨t' + (ℓ.val - s), by omega⟩)
      have hLHS : (targetFragmentR s t' u (by omega) F).attach (Sum.inl g) =
          common := by
        change ((F.disjUnion (strandBundle t')).attach (Sum.inl g)).map id
          (stageEquivR s t' u _) = _
        change ((F.attach g).map Sum.inl Sum.inl).map id (stageEquivR s t' u
          _) = _
        rw [ha]; simp only [Sum.map_inr]; refine congrArg Sum.inr ?_
        rw [stageEquivR_inl, dite_eq_right (show ¬ ℓ.val < s + t' from by omega)]
      have hRHS : (sourceFragmentR s t' u ht F).attach ⟨Sum.inl g, hne⟩ =
          common := by
        change ((Fragment.glueAttach (baseFragmentR s t' u ht F)
            (Sum.inl ⟨s + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
            ⟨Sum.inl g, hne⟩).map id (interfaceStepEquiv s t' u)) = _
        have hba : (baseFragmentR s t' u ht F).attach (Sum.inl g) =
            Sum.inr (Sum.inr ⟨(t' + 1) + (ℓ.val - s), by omega⟩) := by
          change ((F.disjUnion (strandBundle (t' + 1))).attach (Sum.inl
            g)).map id
            (stageEquivR s (t' + 1) u ht) = _
          change ((F.attach g).map Sum.inl Sum.inl).map id
            (stageEquivR s (t' + 1) u ht) = _
          rw [ha]; simp only [Sum.map_inr]; refine congrArg Sum.inr ?_
          rw [stageEquivR_inl,
            dite_eq_right (show ¬ ℓ.val < s + (t' + 1) from by omega)]
        refine Fragment.glueAttach_cases _ (fun v' hv' => ?_)
          (fun ℓ' hℓ' => ?_)
        · exact absurd (hv'.symm.trans hba) (nomatch ·)
        · obtain ⟨ℓ', _hs₁, _hs₂⟩ := ℓ'
          have hℓ'_eq : ℓ' = Sum.inr ⟨(t' + 1) + (ℓ.val - s), by omega⟩ :=
            Sum.inr.inj (hℓ'.symm.trans hba)
          subst hℓ'_eq
          simp only [Sum.map_inr]
          exact congrArg Sum.inr ((interfaceStepEquiv_eval_inr_above s t' u
            ((t' + 1) + (ℓ.val - s)) (by omega) (by omega)).trans
            (congrArg Sum.inr (Fin.ext (by simp))))
      exact (hflag ▸ hLHS).trans
        (by rw [hRHS]; rfl : ((sourceFragmentR s t' u ht F).attach
          ⟨Sum.inl g, hne⟩).map (Equiv.refl _) id = common).symm

private theorem stageStepR_attach_inr (s t' u : ℕ) (ht : t' + 1 ≤ u)
    (F : Fragment (Fin (s + u)))
    (k : ℕ) (hk : k < t' + 1) (b : Bool)
    (hne : (Sum.inr (⟨k, hk⟩, b) : (baseFragmentR s t' u ht F).Flag) ≠
      (baseFragmentR s t' u ht F).boundaryFlag (Sum.inl ⟨s + t', by omega⟩) ∧
      (Sum.inr (⟨k, hk⟩, b) : (baseFragmentR s t' u ht F).Flag) ≠
      (baseFragmentR s t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩)) :
    (targetFragmentR s t' u (by omega) F).attach
      (stageStepFlagEquivR s t' u ht F ⟨Sum.inr (⟨k, hk⟩, b), hne⟩) =
      ((sourceFragmentR s t' u ht F).attach ⟨Sum.inr (⟨k, hk⟩, b), hne⟩).map (Equiv.refl _) id := by
  by_cases hlt : k < t'
  · -- Sub-case: k < t'
    have hflag : (stageStepFlagEquivR s t' u ht F)
        ⟨Sum.inr (⟨k, hk⟩, b), hne⟩ = Sum.inr (⟨k, hlt⟩, b) := by
      have key : (stageStepFlagEquivR s t' u ht F)
          ⟨Sum.inr (⟨k, hk⟩, b), hne⟩ =
        if hlt' : k < t' then Sum.inr (⟨k, hlt'⟩, b)
        else Sum.inl (F.boundaryFlag ⟨s + t', by omega⟩) := rfl
      rw [key, dite_eq_left hlt]
    set common : (targetFragmentR s t' u (by omega) F).Vertex ⊕
        (Fin (s + t') ⊕ Fin (t' + u)) :=
      Sum.inr (Sum.inr ⟨if b then t' + k else k, by split <;> omega⟩)
    have hLHS : (targetFragmentR s t' u (by omega) F).attach
        (Sum.inr (⟨k, hlt⟩, b)) = common := by
      change ((F.disjUnion (strandBundle t')).attach
        (Sum.inr (⟨k, hlt⟩, b))).map id (stageEquivR s t' u _) = _
      change (((strandBundle t').attach (⟨k, hlt⟩, b)).map Sum.inr
        Sum.inr).map id
        (stageEquivR s t' u _) = _
      simp only [strandBundle, Sum.map, Sum.elim, Function.comp]
      apply congrArg Sum.inr; cases b
      · simp only [ite_false, Bool.false_eq_true]
        rw [stageEquivR_inr]
      · simp only [ite_true]
        rw [stageEquivR_inr]
    have hRHS : (sourceFragmentR s t' u ht F).attach
        ⟨Sum.inr (⟨k, hk⟩, b), hne⟩ = common := by
      change ((Fragment.glueAttach (baseFragmentR s t' u ht F)
          (Sum.inl ⟨s + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
          ⟨Sum.inr (⟨k, hk⟩, b), hne⟩).map id (interfaceStepEquiv s t' u)) =
            _
      have hba : (baseFragmentR s t' u ht F).attach (Sum.inr (⟨k, hk⟩, b)) =
          Sum.inr
            (Sum.inr ⟨if b then (t' + 1) + k else k, by split <;> omega⟩) :=
            by
        change ((F.disjUnion (strandBundle (t' + 1))).attach
          (Sum.inr (⟨k, hk⟩, b))).map id (stageEquivR s (t' + 1) u ht) = _
        change (((strandBundle (t' + 1)).attach (⟨k, hk⟩, b)).map
          Sum.inr Sum.inr).map id (stageEquivR s (t' + 1) u ht) = _
        simp only [strandBundle, Sum.map, Sum.elim, Function.comp]
        apply congrArg Sum.inr; cases b
        · simp only [ite_false, Bool.false_eq_true]
          rw [stageEquivR_inr]
        · simp only [ite_true]
          rw [stageEquivR_inr]
      refine Fragment.glueAttach_cases _ (fun v' hv' => ?_)
        (fun ℓ' hℓ' => ?_)
      · exact absurd (hv'.symm.trans hba) (nomatch ·)
      · obtain ⟨ℓ', _hs₁, _hs₂⟩ := ℓ'
        simp only [Sum.map_inr]
        have hℓ'_eq : ℓ' = Sum.inr ⟨if b then (t' + 1) + k else k,
            by split <;> omega⟩ :=
          Sum.inr.inj (hℓ'.symm.trans hba)
        subst hℓ'_eq; refine congrArg Sum.inr ?_
        cases b
        · exact interfaceStepEquiv_eval_inr_below s t' u k hlt
        · exact (interfaceStepEquiv_eval_inr_above s t' u
            ((t' + 1) + k) (by omega) (by omega)).trans
            (congrArg Sum.inr (Fin.ext (by simp only [ite_true]; omega)))
    exact (hflag ▸ hLHS).trans
      (by rw [hRHS]; rfl : ((sourceFragmentR s t' u ht F).attach
        ⟨Sum.inr (⟨k, hk⟩, b), hne⟩).map (Equiv.refl _) id = common).symm
  · -- Sub-case: k ≥ t' (must be k = t', b = true)
    have hk_eq : k = t' := by omega
    have hb : b = true := by
      by_contra hbf
      have hbfalse : b = false := by cases b <;> simp_all
      exact hne.2 (by
        rw [stageStepR_rightBoundary]
        exact hk_eq ▸ hbfalse ▸ congrArg Sum.inr (Prod.ext (Fin.ext rfl)
          rfl))
    have hflag : (stageStepFlagEquivR s t' u ht F)
        ⟨Sum.inr (⟨k, hk⟩, b), hne⟩ =
        Sum.inl (F.boundaryFlag ⟨s + t', by omega⟩) := by
      have key : (stageStepFlagEquivR s t' u ht F)
          ⟨Sum.inr (⟨k, hk⟩, b), hne⟩ =
        if hlt' : k < t' then Sum.inr (⟨k, hlt'⟩, b)
        else Sum.inl (F.boundaryFlag ⟨s + t', by omega⟩) := rfl
      rw [key, dite_eq_right hlt]
    set common : (targetFragmentR s t' u (by omega) F).Vertex ⊕
        (Fin (s + t') ⊕ Fin (t' + u)) := Sum.inr
          (Sum.inr ⟨t' + t', by omega⟩)
    have hLHS : (targetFragmentR s t' u (by omega) F).attach
        (Sum.inl (F.boundaryFlag ⟨s + t', by omega⟩)) = common := by
      change ((F.disjUnion (strandBundle t')).attach
        (Sum.inl (F.boundaryFlag ⟨s + t', by omega⟩))).map id
        (stageEquivR s t' u _) = _
      change ((F.attach (F.boundaryFlag ⟨s + t', by omega⟩)).map
        Sum.inl Sum.inl).map id (stageEquivR s t' u _) = _
      rw [F.attach_boundaryFlag]; simp only [Sum.map_inr]; refine congrArg
        Sum.inr ?_
      rw [stageEquivR_inl,
        dite_eq_right (show ¬ (s + t' : ℕ) < s + t' from by omega)]
      exact congrArg Sum.inr (Fin.ext (by simp))
    have hRHS : (sourceFragmentR s t' u ht F).attach
        ⟨Sum.inr (⟨k, hk⟩, b), hne⟩ = common := by
      change ((Fragment.glueAttach (baseFragmentR s t' u ht F)
          (Sum.inl ⟨s + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
          ⟨Sum.inr (⟨k, hk⟩, b), hne⟩).map id (interfaceStepEquiv s t' u)) =
            _
      have hba : (baseFragmentR s t' u ht F).attach (Sum.inr (⟨k, hk⟩, b)) =
          Sum.inr (Sum.inr ⟨(t' + 1) + t', by omega⟩) := by
        change ((F.disjUnion (strandBundle (t' + 1))).attach
          (Sum.inr (⟨k, hk⟩, b))).map id (stageEquivR s (t' + 1) u ht) = _
        change (((strandBundle (t' + 1)).attach (⟨k, hk⟩, b)).map
          Sum.inr Sum.inr).map id (stageEquivR s (t' + 1) u ht) = _
        simp only [strandBundle, Sum.map, Sum.elim, Function.comp]
        refine congrArg Sum.inr ?_
        rw [show (if (b : Bool) = true then
              (⟨(t' + 1) + k, by omega⟩ : Fin ((t' + 1) + (t' + 1)))
            else ⟨k, by omega⟩) =
            (⟨(t' + 1) + k, by omega⟩ : Fin ((t' + 1) + (t' + 1))) from
              by rw [hb]; rfl]
        rw [stageEquivR_inr]
        exact congrArg Sum.inr (Fin.ext (by simp; omega))
      refine Fragment.glueAttach_cases _ (fun v' hv' => ?_)
        (fun ℓ' hℓ' => ?_)
      · exact absurd (hv'.symm.trans hba) (nomatch ·)
      · obtain ⟨ℓ', _hs₁, _hs₂⟩ := ℓ'
        simp only [Sum.map_inr]
        have hℓ'_eq : ℓ' = Sum.inr ⟨(t' + 1) + t', by omega⟩ :=
          Sum.inr.inj (hℓ'.symm.trans hba)
        subst hℓ'_eq; refine congrArg Sum.inr ?_
        exact (interfaceStepEquiv_eval_inr_above s t' u
          ((t' + 1) + t') (by omega) (by omega)).trans
          (congrArg Sum.inr (Fin.ext (by simp)))
    exact (hflag ▸ hLHS).trans
      (by rw [hRHS]; rfl : ((sourceFragmentR s t' u ht F).attach
        ⟨Sum.inr (⟨k, hk⟩, b), hne⟩).map (Equiv.refl _) id = common).symm

private theorem stageStepR_pairing_inl (s t' u : ℕ) (ht : t' + 1 ≤ u)
    (F : Fragment (Fin (s + u)))
    (g : F.Flag)
    (hne : (Sum.inl g : (baseFragmentR s t' u ht F).Flag) ≠
      (baseFragmentR s t' u ht F).boundaryFlag (Sum.inl ⟨s + t', by omega⟩) ∧
      (Sum.inl g : (baseFragmentR s t' u ht F).Flag) ≠
      (baseFragmentR s t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩)) :
    stageStepFlagEquivR s t' u ht F
      (Fragment.rewire (stageStepR_hopen s t' u ht F) ⟨Sum.inl g, hne⟩) =
      (targetFragmentR s t' u (by omega) F).pairing
        (stageStepFlagEquivR s t' u ht F ⟨Sum.inl g, hne⟩) := by
  have hg_ne : g ≠ F.boundaryFlag ⟨s + t', by omega⟩ := by
    intro heq
    exact hne.1
      (by rw [stageStepR_leftBoundary]; exact congrArg Sum.inl heq)
  have hnj : (baseFragmentR s t' u ht F).pairing (Sum.inl g) ≠
      (baseFragmentR s t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩) :=
        by
    change Sum.inl (F.pairing g) ≠
      (baseFragmentR s t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩)
    rw [stageStepR_rightBoundary]; exact (nomatch ·)
  have hflag_f : (stageStepFlagEquivR s t' u ht F) ⟨Sum.inl g, hne⟩ =
      Sum.inl g := rfl
  by_cases hpg : F.pairing g = F.boundaryFlag ⟨s + t', by omega⟩
  · -- Sub-case: F.pairing g = F.boundaryFlag ⟨s + t', _⟩
    -- rewire branch 1: pairing(g) = boundaryFlag(left)
    have hpi : (baseFragmentR s t' u ht F).pairing (Sum.inl g) =
        (baseFragmentR s t' u ht F).boundaryFlag
          (Sum.inl ⟨s + t', by omega⟩) := by
      change Sum.inl (F.pairing g) = _
      rw [stageStepR_leftBoundary, hpg]
    have hrewire_val : (Fragment.rewire (stageStepR_hopen s t' u ht F)
        ⟨Sum.inl g, hne⟩).val =
        Sum.inr (⟨t', by omega⟩, true) := by
      simp only [Fragment.rewire, dite_eq_left hpi]
      change (baseFragmentR s t' u ht F).pairing
        ((baseFragmentR s t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩))
          = _
      rw [stageStepR_rightBoundary]
      exact stageStepR_rightPairing s t' u ht F
    have hne_rw : Sum.inr (⟨t', by omega⟩, true) ≠
        (baseFragmentR s t' u ht F).boundaryFlag
          (Sum.inl ⟨s + t', by omega⟩) ∧
        Sum.inr (⟨t', by omega⟩, true) ≠
        (baseFragmentR s t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩) :=
          by
      refine ⟨?_, ?_⟩
      · rw [stageStepR_leftBoundary]; exact (nomatch ·)
      · rw [stageStepR_rightBoundary]; intro h
        exact absurd (congrArg Prod.snd (Sum.inr.inj h)) (Ne.symm
          Bool.false_ne_true)
    have heq_rw : Fragment.rewire (stageStepR_hopen s t' u ht F)
        ⟨Sum.inl g, hne⟩ = ⟨Sum.inr (⟨t', by omega⟩, true), hne_rw⟩ :=
      Subtype.ext hrewire_val
    have hflag_rw : (stageStepFlagEquivR s t' u ht F)
        (Fragment.rewire (stageStepR_hopen s t' u ht F) ⟨Sum.inl g, hne⟩) =
        Sum.inl (F.boundaryFlag ⟨s + t', by omega⟩) := by
      rw [heq_rw]
      have key : (stageStepFlagEquivR s t' u ht F)
          ⟨Sum.inr (⟨t', by omega⟩, true), hne_rw⟩ =
        if hlt' : t' < t' then Sum.inr (⟨t', hlt'⟩, true)
        else Sum.inl (F.boundaryFlag ⟨s + t', by omega⟩) := rfl
      rw [key, dite_eq_right (Nat.lt_irrefl t')]
    rw [hflag_rw, hflag_f]
    change Sum.inl (F.boundaryFlag ⟨s + t', _⟩) = Sum.inl (F.pairing g)
    exact congrArg Sum.inl hpg.symm
  · -- Sub-case: F.pairing g ≠ F.boundaryFlag ⟨s + t', _⟩
    -- rewire branch 3: neither
    have hni : (baseFragmentR s t' u ht F).pairing (Sum.inl g) ≠
        (baseFragmentR s t' u ht F).boundaryFlag
          (Sum.inl ⟨s + t', by omega⟩) := by
      change Sum.inl (F.pairing g) ≠ _
      rw [stageStepR_leftBoundary]
      exact fun h => hpg (Sum.inl.inj h)
    have hrewire_val : (Fragment.rewire (stageStepR_hopen s t' u ht F)
        ⟨Sum.inl g, hne⟩).val = Sum.inl (F.pairing g) := by
      unfold Fragment.rewire
      simp only [show (baseFragmentR s t' u ht F).pairing (Sum.inl g) =
        Sum.inl (F.pairing g) from rfl]
      rw [dite_eq_right hni, dite_eq_right hnj]
    have heq_rw : Fragment.rewire (stageStepR_hopen s t' u ht F)
        ⟨Sum.inl g, hne⟩ = ⟨Sum.inl (F.pairing g), ⟨hni, hnj⟩⟩ :=
      Subtype.ext hrewire_val
    have hflag_rw : (stageStepFlagEquivR s t' u ht F)
        (Fragment.rewire (stageStepR_hopen s t' u ht F) ⟨Sum.inl g, hne⟩) =
        Sum.inl (F.pairing g) := by
      rw [heq_rw]; rfl
    rw [hflag_rw, hflag_f]
    rfl

private theorem stageStepR_pairing_inr (s t' u : ℕ) (ht : t' + 1 ≤ u)
    (F : Fragment (Fin (s + u)))
    (k : ℕ) (hk : k < t' + 1) (b : Bool)
    (hne : (Sum.inr (⟨k, hk⟩, b) : (baseFragmentR s t' u ht F).Flag) ≠
      (baseFragmentR s t' u ht F).boundaryFlag (Sum.inl ⟨s + t', by omega⟩) ∧
      (Sum.inr (⟨k, hk⟩, b) : (baseFragmentR s t' u ht F).Flag) ≠
      (baseFragmentR s t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩)) :
    stageStepFlagEquivR s t' u ht F
      (Fragment.rewire (stageStepR_hopen s t' u ht F) ⟨Sum.inr (⟨k, hk⟩, b), hne⟩) =
      (targetFragmentR s t' u (by omega) F).pairing
        (stageStepFlagEquivR s t' u ht F ⟨Sum.inr (⟨k, hk⟩, b), hne⟩) := by
  by_cases hlt : k < t'
  · -- Sub-case: k < t', rewire "neither" branch
    have hni : (baseFragmentR s t' u ht F).pairing (Sum.inr (⟨k, hk⟩, b)) ≠
        (baseFragmentR s t' u ht F).boundaryFlag
          (Sum.inl ⟨s + t', by omega⟩) := by
      change Sum.inr (⟨k, hk⟩, !b) ≠
        (baseFragmentR s t' u ht F).boundaryFlag
          (Sum.inl ⟨s + t', by omega⟩)
      rw [stageStepR_leftBoundary]; exact (nomatch ·)
    have hnj : (baseFragmentR s t' u ht F).pairing (Sum.inr (⟨k, hk⟩, b)) ≠
        (baseFragmentR s t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩) :=
          by
      change Sum.inr (⟨k, hk⟩, !b) ≠
        (baseFragmentR s t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩)
      rw [stageStepR_rightBoundary]; intro h
      have := congrArg Prod.fst (Sum.inr.inj h)
      exact absurd (Fin.ext_iff.mp this) (Nat.ne_of_lt hlt)
    have hrewire_val : (Fragment.rewire (stageStepR_hopen s t' u ht F)
        ⟨Sum.inr (⟨k, hk⟩, b), hne⟩).val = Sum.inr (⟨k, hk⟩, !b) := by
      unfold Fragment.rewire
      simp only [show (baseFragmentR s t' u ht F).pairing (Sum.inr (⟨k, hk⟩,
        b)) =
        Sum.inr (⟨k, hk⟩, !b) from rfl]
      rw [dite_eq_right hni, dite_eq_right hnj]
    have heq_rw : Fragment.rewire (stageStepR_hopen s t' u ht F)
        ⟨Sum.inr (⟨k, hk⟩, b), hne⟩ = ⟨Sum.inr (⟨k, hk⟩, !b), ⟨hni, hnj⟩⟩ :=
      Subtype.ext hrewire_val
    have hflag_rw : (stageStepFlagEquivR s t' u ht F)
        (Fragment.rewire (stageStepR_hopen s t' u ht F)
        ⟨Sum.inr (⟨k, hk⟩, b), hne⟩) =
        Sum.inr (⟨k, hlt⟩, !b) := by
      rw [heq_rw]
      have key : (stageStepFlagEquivR s t' u ht F)
          ⟨Sum.inr (⟨k, hk⟩, !b), ⟨hni, hnj⟩⟩ =
        if hlt' : k < t' then Sum.inr (⟨k, hlt'⟩, !b)
        else Sum.inl (F.boundaryFlag ⟨s + t', by omega⟩) := rfl
      rw [key, dite_eq_left hlt]
    have hflag_f : (stageStepFlagEquivR s t' u ht F) ⟨Sum.inr (⟨k, hk⟩, b),
      hne⟩ =
        Sum.inr (⟨k, hlt⟩, b) := by
      have key : (stageStepFlagEquivR s t' u ht F)
          ⟨Sum.inr (⟨k, hk⟩, b), hne⟩ =
        if hlt' : k < t' then Sum.inr (⟨k, hlt'⟩, b)
        else Sum.inl (F.boundaryFlag ⟨s + t', by omega⟩) := rfl
      rw [key, dite_eq_left hlt]
    rw [hflag_rw, hflag_f]
    rfl
  · -- Sub-case: k = t', b = true
    have hk_eq : k = t' := by omega
    have hb : b = true := by
      by_contra hbf
      have hbfalse : b = false := by cases b <;> simp_all
      exact hne.2 (by
        rw [stageStepR_rightBoundary]
        exact hk_eq ▸ hbfalse ▸ congrArg Sum.inr (Prod.ext (Fin.ext rfl)
          rfl))
    -- rewire branch 2: pairing(strand t' true) = (t', false) =
    --   boundaryFlag(right)
    have hpair_eq_bdy : (baseFragmentR s t' u ht F).pairing (Sum.inr (⟨k,
      hk⟩, b)) =
        (baseFragmentR s t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩) :=
          by
      change Sum.inr (⟨k, hk⟩, !b) =
        (baseFragmentR s t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩)
      rw [stageStepR_rightBoundary]; subst hk_eq; subst hb; rfl
    have hni : (baseFragmentR s t' u ht F).pairing (Sum.inr (⟨k, hk⟩, b)) ≠
        (baseFragmentR s t' u ht F).boundaryFlag
          (Sum.inl ⟨s + t', by omega⟩) := by
      change Sum.inr (⟨k, hk⟩, !b) ≠
        (baseFragmentR s t' u ht F).boundaryFlag
          (Sum.inl ⟨s + t', by omega⟩)
      rw [stageStepR_leftBoundary]; exact (nomatch ·)
    have hrewire_val : (Fragment.rewire (stageStepR_hopen s t' u ht F)
        ⟨Sum.inr (⟨k, hk⟩, b), hne⟩).val =
        Sum.inl (F.pairing (F.boundaryFlag ⟨s + t', by omega⟩)) := by
      simp only [Fragment.rewire, dite_eq_right hni, dite_eq_left hpair_eq_bdy]
      change (baseFragmentR s t' u ht F).pairing
        ((baseFragmentR s t' u ht F).boundaryFlag
          (Sum.inl ⟨s + t', by omega⟩)) = _
      rw [stageStepR_leftBoundary]; rfl
    have hprop : Sum.inl (F.pairing (F.boundaryFlag ⟨s + t', by omega⟩)) ≠
        (baseFragmentR s t' u ht F).boundaryFlag
          (Sum.inl ⟨s + t', by omega⟩) ∧
        Sum.inl (F.pairing (F.boundaryFlag ⟨s + t', by omega⟩)) ≠
        (baseFragmentR s t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩) :=
          by
      refine ⟨?_, ?_⟩
      · rw [stageStepR_leftBoundary]; intro h
        exact F.pairing_ne (F.boundaryFlag ⟨s + t', by omega⟩)
          (Sum.inl.inj h)
      · rw [stageStepR_rightBoundary]; exact (nomatch ·)
    have heq_rw : Fragment.rewire (stageStepR_hopen s t' u ht F)
        ⟨Sum.inr (⟨k, hk⟩, b), hne⟩ =
        ⟨Sum.inl (F.pairing (F.boundaryFlag ⟨s + t', by omega⟩)), hprop⟩ :=
      Subtype.ext hrewire_val
    have hflag_rw : (stageStepFlagEquivR s t' u ht F)
        (Fragment.rewire (stageStepR_hopen s t' u ht F)
        ⟨Sum.inr (⟨k, hk⟩, b), hne⟩) =
        Sum.inl (F.pairing (F.boundaryFlag ⟨s + t', by omega⟩)) := by
      rw [heq_rw]; rfl
    have hflag_f : (stageStepFlagEquivR s t' u ht F) ⟨Sum.inr (⟨k, hk⟩, b),
      hne⟩ =
        Sum.inl (F.boundaryFlag ⟨s + t', by omega⟩) := by
      have key : (stageStepFlagEquivR s t' u ht F)
          ⟨Sum.inr (⟨k, hk⟩, b), hne⟩ =
        if hlt' : k < t' then Sum.inr (⟨k, hlt'⟩, b)
        else Sum.inl (F.boundaryFlag ⟨s + t', by omega⟩) := rfl
      rw [key, dite_eq_right hlt]
    rw [hflag_rw, hflag_f]
    rfl

/-- The descent step: after one open glue (at the `t'`-th interface
pair), the resulting fragment is equivalent to the stage-`t'`
disjoint union relabelled by the stage-`t'` equivalence. -/
noncomputable def stageStepEquivR (s t' u : ℕ) (ht : t' + 1 ≤ u)
    (F : Fragment (Fin (s + u))) :
    (sourceFragmentR s t' u ht F).Equiv (targetFragmentR s t' u (by omega) F)
      where
  flagEquiv := stageStepFlagEquivR s t' u ht F
  vertexEquiv := Equiv.refl _
  circles_eq := rfl
  attach_comm f := by
    obtain ⟨fval, hne⟩ := f
    rcases fval with g | ⟨⟨k, hk⟩, b⟩
    · exact stageStepR_attach_inl s t' u ht F g hne
    · exact stageStepR_attach_inr s t' u ht F k hk b hne
  pairing_comm f := by
    obtain ⟨fval, hne⟩ := f
    rcases fval with g | ⟨⟨k, hk⟩, b⟩
    · exact stageStepR_pairing_inl s t' u ht F g hne
    · exact stageStepR_pairing_inr s t' u ht F k hk b hne

/-! ### Assembly: the right identity law -/

/-- The stage equivalence at `t' = u` acts as the identity: every
element is mapped to itself. -/
theorem stageEquivR_self (s u : ℕ) (x : Fin (s + u) ⊕ Fin (u + u)) :
    stageEquivR s u u (le_refl u) x = x := by
  rcases x with ℓ | a
  · rw [stageEquivR_inl, dite_eq_left ℓ.isLt]
  · rw [stageEquivR_inr]

/-- In the base fragment, the glue is always open, so `gluePair`
coincides with `gluePairOpen`. -/
theorem baseFragmentR_gluePair_eq (s t' u : ℕ) (ht : t' + 1 ≤ u)
    (F : Fragment (Fin (s + u))) :
    (baseFragmentR s t' u ht F).gluePair (Sum.inl ⟨s + t', by omega⟩)
      (Sum.inr ⟨t', by omega⟩) (by simp) =
    (baseFragmentR s t' u ht F).gluePairOpen (Sum.inl ⟨s + t', by omega⟩)
      (Sum.inr ⟨t', by omega⟩) (by simp) (by exact stageStepR_hopen s t' u ht F) := by
  unfold Fragment.gluePair
  exact dite_eq_right (stageStepR_hopen s t' u ht F)

/-- Descending induction: iterating `glueInterface` from stage `t'`
down to zero, with the stage-`t'` fragment, yields a result
equivalent to iterating from stage `u` on the original F/strand
union. -/
noncomputable def glueInterfaceStrandBundleDescentRight
    (s u : ℕ) (F : Fragment (Fin (s + u))) :
    ∀ (t' : ℕ) (ht' : t' ≤ u),
    (glueInterface s u u (F.disjUnion (strandBundle u))).Equiv
    (glueInterface s t' u ((F.disjUnion (strandBundle t')).relabel
      (stageEquivR s t' u ht')))
  | t', ht' => by
    by_cases htop : t' = u
    · cases htop
      exact glueInterfaceCongr _ _ u
        ((Fragment.Equiv.relabelPointwiseId _ _
          (stageEquivR_self _ u)).symm)
    · have ht'_lt : t' + 1 ≤ u := by omega
      have ih := glueInterfaceStrandBundleDescentRight s u F (t' + 1) ht'_lt
      have step : ((baseFragmentR s t' u ht'_lt F).gluePair
          (Sum.inl ⟨s + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
          (by simp)).relabel (interfaceStepEquiv s t' u) =
        sourceFragmentR s t' u ht'_lt F := by
        unfold sourceFragmentR
        rw [← baseFragmentR_gluePair_eq]
      exact ih.trans (glueInterfaceCongr s t' u
        (step ▸ (stageStepEquivR s t' u ht'_lt F)))
termination_by t' _ => u - t'
decreasing_by omega

/-- **The right identity law for fragment composition**: composing
with the strand bundle on the right yields an equivalent fragment. -/
noncomputable def composeStrandBundleRight (s u : ℕ)
    (F : Fragment (Fin (s + u))) :
    (F.compose (strandBundle u)).Equiv F :=
  (Fragment.Equiv.relabelCongr
    (glueInterfaceStrandBundleDescentRight s u F 0 (Nat.zero_le u))
      finSumFinEquiv).trans
    (stageZeroEquivR s u F)

end RS
