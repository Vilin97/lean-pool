/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.ConversePair

/-!
# The pair family and the base sum

A choice of pair datum (`ConversePair.lean`) at every subset of the
composition's base: the family `pairFamily`, its behaviour under
the interface glue, and the sum of the composition's own terms over
the base.  The sum is read with the bits each subset itself
determines, and `base_sum_eq_superForm_pairing_bitsOf` writes it as
the super form pairing of the two fragments' tensors — the tensor
side of the Gram identity.
-/

@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment
/-- The lexicographic order on the interface's label type. -/
@[reducible] local instance famBaseOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

/-- The same order one stage up. -/
@[reducible] local instance famOrderSucc (n : ℕ) :
    LinearOrder (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) :=
  sumLexLinearOrder _ _

/-- The order a stage's surviving labels carry. -/
@[reducible] local instance famSurvOrder (n : ℕ) :
    LinearOrder (SurvivingLabel
      (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) (cutL n) (cutR n)) :=
  sumLexSubtypeLinearOrder _ _ _

/-- The order the composition's own label type carries. -/
@[reducible] local instance famTopOrder :
    LinearOrder (Fin 0 ⊕ Fin 0) :=
  sumLexLinearOrder _ _

open Classical in
/-- **The pair datum, against the total summand.**  RS21's (13) and
(14) in the form the composition's sum needs: no state-matching
hypothesis, the mismatched states contributing nothing on both
sides. -/
theorem exists_pairDatum_total {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t))
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (hE₁ : (EdgeSubset.mk s₁ hc₁).Eulerian)
    (hn₁ : Nonempty (EdgeSubset.mk s₁ hc₁).CanonData)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (hE₂ : (EdgeSubset.mk s₂ hc₂).Eulerian)
    (hn₂ : Nonempty (EdgeSubset.mk s₂ hc₂).CanonData)
    (hused : ∀ i : Fin t,
      F.boundaryFlag i ∈ s₁ ↔ G.boundaryFlag i ∈ s₂)
    (hb : ∀ i : Fin t,
      F.boundaryFlag i ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
        ↔ G.boundaryFlag i ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags)
    :
    ∃ (κ : (EdgeSubset.mk (closeJoin s₁ s₂)
        (closeJoin_pairing_mem hc₁ hc₂)).RelTransitionSystem)
      (O : κ.Orientation),
      ((∑ x : GenBoundaryState k ℓ (Fin t),
          ∑ y : GenBoundaryState k ℓ (Fin t),
            superForm t x y * tensorTermAt F h s₁ x
              * tensorTermAt G h s₂ y)
        = (-1 : ℂ) ^ (glueData t (closeBase F G)
              (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
                (Classical.choice hn₂).1)).rel.openCircuitCount
          * ∑ x : GenBoundaryState k ℓ (Fin t),
              edgeTermOf h ⟨κ, O⟩ (diagOf t x)
                (glueCount t (closeBase F G)
                  (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
                    (Classical.choice hn₂).1)))
      ∧ (∀ ℓ' : Fin (0 + t) ⊕ Fin (t + 0),
        O.isOut ((closeBase F G).pairing
            ((closeBase F G).boundaryFlag ℓ'))
          = !O.isOut ((closeBase F G).boundaryFlag ℓ'))
      ∧ (∀ m : Fin t,
        O.isOut ((closeBase F G).boundaryFlag (intR t m))
          = !O.isOut ((closeBase F G).boundaryFlag (intL t m)))
      ∧ κ.MatchEq (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
        (Classical.choice hn₂).1).rel := by
  obtain ⟨o₁', o₂', M₁, M₂, hM₁, hM₂, halt, hag₁, hag₂, _halt',
    hval⟩ :=
    exists_pairTerm_eq_glued_sign h t F G hc₁ hE₁ hn₁ hc₂ hE₂ hn₂
      hused hb
  obtain ⟨c, hcol, hcut⟩ :=
    exists_cut_colouring t (closeBase F G)
  refine ⟨_, orientReplace
      (prodOrient
        (relabelOrientUp (finCongr (by omega : t = 0 + t))
          (EdgeSubset.relabelDown
            (finCongr (by omega : t = 0 + t))
            (leftSub (EdgeSubset.mk (closeJoin s₁ s₂)
              (closeJoin_pairing_mem hc₁ hc₂))))
          (orientOfEq (relabelDown_leftSub_closeJoin
            (closeJoin_pairing_mem hc₁ hc₂) hc₁).symm o₁'))
        (relabelOrientUp (finCongr (by omega : t = t + 0))
          (EdgeSubset.relabelDown
            (finCongr (by omega : t = t + 0))
            (rightSub (EdgeSubset.mk (closeJoin s₁ s₂)
              (closeJoin_pairing_mem hc₁ hc₂))))
          (orientOfEq (relabelDown_rightSub_closeJoin
            (closeJoin_pairing_mem hc₁ hc₂) hc₂).symm o₂')))
      (pairTailFun hc₁ hc₂ M₁ M₂ c), ?_, ?_, ?_, ?_⟩
  · rw [hval, pow_add, mul_assoc, Finset.mul_sum]
    refine congrArg (fun z => _ * z) (Finset.sum_congr rfl
      (fun st _ => ?_))
    unfold edgeTermOf
    split_ifs with hbnd
    · obtain ⟨hm₁, hm₂⟩ := (matches_closeJoin_iff s₁ s₂ st).mp hbnd
      refine congrArg (fun z => _ * z) ?_
      rw [edgeSum_orientReplace]
      refine pairAgreeValue_eq_edgeSum_closeJoin h t F G hc₁ hc₂ o₁'
        o₂' st hbnd ?_ ?_
      · rw [show (leftSub (EdgeSubset.mk (closeJoin s₁ s₂)
          (closeJoin_pairing_mem hc₁ hc₂))).flags = s₁ from
            leftPart_joinParts s₁ s₂]
        exact hm₁
      · rw [show (rightSub (EdgeSubset.mk (closeJoin s₁ s₂)
          (closeJoin_pairing_mem hc₁ hc₂))).flags = s₂ from
            rightPart_joinParts s₁ s₂]
        exact hm₂
    · by_cases hm₁ : genBoundarySubsetMatches F s₁ st
      · by_cases hm₂ : genBoundarySubsetMatches G s₂ st
        · exact absurd ((matches_closeJoin_iff s₁ s₂ st).mpr
            ⟨hm₁, hm₂⟩) hbnd
        · rw [show pairAgreeValue (EdgeSubset.mk s₁ hc₁)
              (EdgeSubset.mk s₂ hc₂) h o₁' o₂' st = 0 by
            unfold pairAgreeValue
            rw [dite_eq_left hm₁, dite_eq_right hm₂]]
          ring
      · rw [pairAgreeValue_eq_zero (EdgeSubset.mk s₁ hc₁)
          (EdgeSubset.mk s₂ hc₂) h o₁' o₂' st hm₁]
        ring
  · exact orientReplace_pairTailFun_flip hc₁ hc₂ o₁' o₂' M₁ M₂ c
      hcol hM₁ hM₂ hag₁ hag₂ _
      (fun x => isOut_orientOfEq _ o₁' x)
      (fun y => isOut_orientOfEq _ o₂' y)
  · exact orientReplace_pairTailFun_cut hc₁ hc₂ M₁ M₂ c hcut hb halt
      _
  · intro f hf
    cases f with
    | inl g =>
      change Sum.inl _ = Sum.inl _
      refine congrArg Sum.inl ?_
      exact Eq.trans (match_relOfEq _ (Classical.choice hn₁).1 g)
        (match_relOfEq _ (relabelTransUp (leftIso t).toEquiv
          (EdgeSubset.mk s₁ hc₁) (Classical.choice hn₁).1) g).symm
    | inr g =>
      change Sum.inr _ = Sum.inr _
      refine congrArg Sum.inr ?_
      exact Eq.trans (match_relOfEq _ (Classical.choice hn₂).1 g)
        (match_relOfEq _ (relabelTransUp (rightIso t).toEquiv
          (EdgeSubset.mk s₂ hc₂) (Classical.choice hn₂).1) g).symm

open Classical in
/-- **The pair datum, read at an equal subset.**  Everything the
datum says transports along an equality of subsets. -/
theorem exists_pairDatum_ofEq {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t))
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (hE₁ : (EdgeSubset.mk s₁ hc₁).Eulerian)
    (hn₁ : Nonempty (EdgeSubset.mk s₁ hc₁).CanonData)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (hE₂ : (EdgeSubset.mk s₂ hc₂).Eulerian)
    (hn₂ : Nonempty (EdgeSubset.mk s₂ hc₂).CanonData)
    (hused : ∀ i : Fin t,
      F.boundaryFlag i ∈ s₁ ↔ G.boundaryFlag i ∈ s₂)
    (hb : ∀ i : Fin t,
      F.boundaryFlag i ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
        ↔ G.boundaryFlag i ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags)
    (u : Finset (closeBase F G).Flag)
    (hc : ∀ f ∈ u, (closeBase F G).pairing f ∈ u)
    (hu : (EdgeSubset.mk u hc : EdgeSubset (closeBase F G))
      = EdgeSubset.mk (closeJoin s₁ s₂)
        (closeJoin_pairing_mem hc₁ hc₂)) :
    ∃ (κ : (EdgeSubset.mk u hc).RelTransitionSystem)
      (O : κ.Orientation),
      ((∑ x : GenBoundaryState k ℓ (Fin t),
          ∑ y : GenBoundaryState k ℓ (Fin t),
            superForm t x y * tensorTermAt F h s₁ x
              * tensorTermAt G h s₂ y)
        = (-1 : ℂ) ^ (glueData t (closeBase F G)
              (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
                (Classical.choice hn₂).1)).rel.openCircuitCount
          * ∑ x : GenBoundaryState k ℓ (Fin t),
              edgeTermOf h ⟨κ, O⟩ (diagOf t x)
                (glueCount t (closeBase F G)
                  (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
                    (Classical.choice hn₂).1)))
      ∧ (∀ ℓ' : Fin (0 + t) ⊕ Fin (t + 0),
        O.isOut ((closeBase F G).pairing
            ((closeBase F G).boundaryFlag ℓ'))
          = !O.isOut ((closeBase F G).boundaryFlag ℓ'))
      ∧ (∀ m : Fin t,
        O.isOut ((closeBase F G).boundaryFlag (intR t m))
          = !O.isOut ((closeBase F G).boundaryFlag (intL t m)))
      ∧ κ.MatchEq (relOfEq hu.symm
        (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
          (Classical.choice hn₂).1).rel) := by
  obtain ⟨κ₀, O₀, hval, hflip, hcut, hmatch⟩ :=
    exists_pairDatum_total h t F G hc₁ hE₁ hn₁ hc₂ hE₂ hn₂ hused
      hb
  refine ⟨relOfEq hu.symm κ₀, orientOfEq hu.symm O₀, ?_,
    fun ℓ' => ?_, fun m => ?_, ?_⟩
  · refine hval.trans (congrArg (fun z => _ * z)
      (Finset.sum_congr rfl (fun x _ => ?_)))
    exact (edgeTermOf_ofEq h hu.symm ⟨κ₀, O₀⟩ (diagOf t x) _).symm
  · rw [isOut_orientOfEq hu.symm O₀ _, isOut_orientOfEq hu.symm O₀ _]
    exact hflip ℓ'
  · rw [isOut_orientOfEq hu.symm O₀ _, isOut_orientOfEq hu.symm O₀ _]
    exact hcut m
  · intro f hf
    refine Eq.trans (match_relOfEq hu.symm κ₀ f) (Eq.trans ?_
      (match_relOfEq hu.symm
        (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
          (Classical.choice hn₂).1).rel f).symm)
    exact hmatch f (by
      rw [congrArg EdgeSubset.internalFlags hu] at hf
      exact hf)

/-- **Matching used labels make the join balanced.** -/
theorem cutBalanced_closeJoin {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hused : ∀ i : Fin t,
      F.boundaryFlag i ∈ s₁ ↔ G.boundaryFlag i ∈ s₂) :
    CutBalanced (closeBase F G) (closeJoin s₁ s₂) := fun m =>
  (inl_mem_joinParts (s₁ := s₁) (s₂ := s₂)
      (f := F.boundaryFlag m)).trans
    ((hused m).trans (inr_mem_joinParts (s₁ := s₁) (s₂ := s₂)
      (f := G.boundaryFlag m)).symm)

open Classical in
/-- **A datum at every subset**, carrying both the directions and,
at a join of compatible halves, RS21's value. -/
theorem exists_pairDatum_sigma_full {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t))
    (u : Finset (closeBase F G).Flag)
    (hc : ∀ f ∈ u, (closeBase F G).pairing f ∈ u)
    (hE : (EdgeSubset.mk u hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk u hc).CanonData) :
    ∃ d : Σ κ : (EdgeSubset.mk u hc).RelTransitionSystem,
        κ.Orientation,
      (CutBalanced (closeBase F G) u →
        (∀ ℓ' : Fin (0 + t) ⊕ Fin (t + 0),
          d.2.isOut ((closeBase F G).pairing
              ((closeBase F G).boundaryFlag ℓ'))
            = !d.2.isOut ((closeBase F G).boundaryFlag ℓ'))
        ∧ (∀ m : Fin t,
          d.2.isOut ((closeBase F G).boundaryFlag (intR t m))
            = !d.2.isOut
              ((closeBase F G).boundaryFlag (intL t m))))
      ∧ ∀ (s₁ : Finset F.Flag) (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
          (_hE₁ : (EdgeSubset.mk s₁ hc₁).Eulerian)
          (hn₁ : Nonempty (EdgeSubset.mk s₁ hc₁).CanonData)
          (s₂ : Finset G.Flag) (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
          (_hE₂ : (EdgeSubset.mk s₂ hc₂).Eulerian)
          (hn₂ : Nonempty (EdgeSubset.mk s₂ hc₂).CanonData)
          (hused : ∀ i : Fin t,
            F.boundaryFlag i ∈ s₁ ↔ G.boundaryFlag i ∈ s₂)
          (_hb : ∀ i : Fin t,
            F.boundaryFlag i ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
              ↔ G.boundaryFlag i
                ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags)
          (hu : (EdgeSubset.mk u hc : EdgeSubset (closeBase F G))
            = EdgeSubset.mk (closeJoin s₁ s₂)
              (closeJoin_pairing_mem hc₁ hc₂)),
        d.1.MatchEq (relOfEq hu.symm
          (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
            (Classical.choice hn₂).1).rel) ∧
        ((∑ x : GenBoundaryState k ℓ (Fin t),
            ∑ y : GenBoundaryState k ℓ (Fin t),
              superForm t x y * tensorTermAt F h s₁ x
                * tensorTermAt G h s₂ y)
          = (-1 : ℂ) ^ (glueData t (closeBase F G)
                (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
                  (Classical.choice hn₂).1)).rel.openCircuitCount
            * ∑ x : GenBoundaryState k ℓ (Fin t),
                edgeTermOf h d (diagOf t x)
                  (glueCount t (closeBase F G)
                    (pairStage hc₁ hc₂ hused
                      (Classical.choice hn₁).1
                      (Classical.choice hn₂).1))) := by
  -- ═══════ IS THE SUBSET CUT-BALANCED? ═══════
  -- A balanced subset carries a datum on each side, which join;
  -- an unbalanced one contributes nothing.
  by_cases hcb : CutBalanced (closeBase F G) u
  · obtain ⟨hcL, hEL, hneL⟩ := join_support_left hc hE hne
    obtain ⟨hcR, hER, hneR⟩ := join_support_right hc hE hne
    have hused : ∀ i : Fin t, F.boundaryFlag i ∈ leftPart u
        ↔ G.boundaryFlag i ∈ rightPart u := fun i =>
      (mem_leftPart (s := u) (f := F.boundaryFlag i)).trans
        ((hcb i).trans (mem_rightPart (s := u)
          (f := G.boundaryFlag i)).symm)
    have hb : ∀ i : Fin t,
        F.boundaryFlag i ∈ (EdgeSubset.mk (leftPart u) hcL :
            EdgeSubset F).boundaryFlags
          ↔ G.boundaryFlag i ∈ (EdgeSubset.mk (rightPart u) hcR :
            EdgeSubset G).boundaryFlags := by
      intro i
      constructor
      · intro hx
        exact boundaryFlag_mem_boundaryFlags
          (F := (EdgeSubset.mk (rightPart u) hcR : EdgeSubset G))
          (a := i) ((hused i).mp (mem_flags_of_boundaryFlags _ hx))
      · intro hx
        exact boundaryFlag_mem_boundaryFlags
          (F := (EdgeSubset.mk (leftPart u) hcL : EdgeSubset F))
          (a := i) ((hused i).mpr (mem_flags_of_boundaryFlags _ hx))
    have hEL' : (EdgeSubset.mk (leftPart u) hcL :
        EdgeSubset F).Eulerian :=
      (relabelUp_eulerian (finCongr (by omega : t = 0 + t))
        (EdgeSubset.mk (leftPart u) hcL : EdgeSubset F)).mp hEL
    have hneL' : Nonempty (EdgeSubset.mk (leftPart u) hcL :
        EdgeSubset F).CanonData :=
      (EdgeSubset.nonempty_canonData_relabelUp
        (Fin.castOrderIso (by omega : t = 0 + t))
        (EdgeSubset.mk (leftPart u) hcL : EdgeSubset F)).mp hneL
    have hER' : (EdgeSubset.mk (rightPart u) hcR :
        EdgeSubset G).Eulerian :=
      (relabelUp_eulerian (finCongr (by omega : t = t + 0))
        (EdgeSubset.mk (rightPart u) hcR : EdgeSubset G)).mp hER
    have hneR' : Nonempty (EdgeSubset.mk (rightPart u) hcR :
        EdgeSubset G).CanonData :=
      (EdgeSubset.nonempty_canonData_relabelUp
        (Fin.castOrderIso (by omega : t = t + 0))
        (EdgeSubset.mk (rightPart u) hcR : EdgeSubset G)).mp hneR
    have hu0 : (EdgeSubset.mk u hc : EdgeSubset (closeBase F G))
        = (EdgeSubset.mk (closeJoin (leftPart u) (rightPart u))
          (closeJoin_pairing_mem hcL hcR) :
            EdgeSubset (closeBase F G)) :=
      EdgeSubset.ext (joinParts_parts u).symm
    obtain ⟨κ₀, O₀, hval, hflip, hcut, hmatch⟩ :=
      exists_pairDatum_ofEq h t F G hcL hEL' hneL' hcR hER' hneR'
        hused hb u hc hu0
    refine ⟨⟨κ₀, O₀⟩, fun _ => ⟨hflip, hcut⟩, ?_⟩
    intro s₁ hc₁ hE₁ hn₁ s₂ hc₂ hE₂ hn₂ hused' hb' hu'
    have hflags : u = closeJoin s₁ s₂ :=
      congrArg EdgeSubset.flags hu'
    have h1 : s₁ = leftPart u := by
      rw [hflags]
      exact (leftPart_joinParts s₁ s₂).symm
    have h2 : s₂ = rightPart u := by
      rw [hflags]
      exact (rightPart_joinParts s₁ s₂).symm
    subst h1
    subst h2
    exact ⟨hmatch, hval⟩
  · obtain ⟨κ, o, -⟩ := Classical.choice hne
    refine ⟨⟨κ, o⟩, fun hx => absurd hx hcb, ?_⟩
    intro s₁ hc₁ hE₁ hn₁ s₂ hc₂ hE₂ hn₂ hused' hb' hu'
    have hflags : u = closeJoin s₁ s₂ :=
      congrArg EdgeSubset.flags hu'
    exact absurd (by
      rw [hflags]
      exact cutBalanced_closeJoin hused') hcb

open Classical in
/-- **The pair family.**  At every balanced subset of the base it
carries the directions the lift asks for. -/
noncomputable def pairFamily {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (t : ℕ) (F G : Fragment (Fin t)) :
    DataFamily (closeBase F G) :=
  fun u hc hE hne =>
    Classical.choose
      (exists_pairDatum_sigma_full h t F G u hc hE hne)

open Classical in
/-- **The pair family has the base's directions.** -/
theorem baseDirections_pairFamily {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t)) :
    BaseDirections (closeBase F G) (pairFamily h t F G) := by
  intro u hc hE hne hcb
  obtain ⟨hflip, hcut⟩ := (Classical.choose_spec
    (exists_pairDatum_sigma_full h t F G u hc hE hne)).1 hcb
  exact ⟨hflip, fun m =>
    (isOut_cut_iff_boundary _ hflip m).mpr (hcut m)⟩

open Classical in
/-- **The pair family's system is the pair stage's.**  The two agree
on the partner map, which is what the circuit count sees. -/
theorem pairFamily_matchEq {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (t : ℕ) (F G : Fragment (Fin t))
    (u : Finset (closeBase F G).Flag)
    (hc : ∀ f ∈ u, (closeBase F G).pairing f ∈ u)
    (hE : (EdgeSubset.mk u hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk u hc).CanonData)
    (s₁ : Finset F.Flag) (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (hE₁ : (EdgeSubset.mk s₁ hc₁).Eulerian)
    (hn₁ : Nonempty (EdgeSubset.mk s₁ hc₁).CanonData)
    (s₂ : Finset G.Flag) (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (hE₂ : (EdgeSubset.mk s₂ hc₂).Eulerian)
    (hn₂ : Nonempty (EdgeSubset.mk s₂ hc₂).CanonData)
    (hused : ∀ i : Fin t,
      F.boundaryFlag i ∈ s₁ ↔ G.boundaryFlag i ∈ s₂)
    (hb : ∀ i : Fin t,
      F.boundaryFlag i ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
        ↔ G.boundaryFlag i
          ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags)
    (hu : (EdgeSubset.mk u hc : EdgeSubset (closeBase F G))
      = EdgeSubset.mk (closeJoin s₁ s₂)
        (closeJoin_pairing_mem hc₁ hc₂)) :
    (pairFamily h t F G u hc hE hne).1.MatchEq
      (relOfEq hu.symm
        (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
          (Classical.choice hn₂).1).rel) :=
  ((Classical.choose_spec
    (exists_pairDatum_sigma_full h t F G u hc hE hne)).2 s₁ hc₁
    hE₁ hn₁ s₂ hc₂ hE₂ hn₂ hused hb hu).1

open Classical in
/-- **The pair family computes RS21's pair term.**  At a join of
compatible halves, the family's own datum is the one (13) and (14)
speak of. -/
theorem pairFamily_value {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (t : ℕ) (F G : Fragment (Fin t))
    (u : Finset (closeBase F G).Flag)
    (hc : ∀ f ∈ u, (closeBase F G).pairing f ∈ u)
    (hE : (EdgeSubset.mk u hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk u hc).CanonData)
    (s₁ : Finset F.Flag) (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (hE₁ : (EdgeSubset.mk s₁ hc₁).Eulerian)
    (hn₁ : Nonempty (EdgeSubset.mk s₁ hc₁).CanonData)
    (s₂ : Finset G.Flag) (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (hE₂ : (EdgeSubset.mk s₂ hc₂).Eulerian)
    (hn₂ : Nonempty (EdgeSubset.mk s₂ hc₂).CanonData)
    (hused : ∀ i : Fin t,
      F.boundaryFlag i ∈ s₁ ↔ G.boundaryFlag i ∈ s₂)
    (hb : ∀ i : Fin t,
      F.boundaryFlag i ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
        ↔ G.boundaryFlag i
          ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags)
    (hu : (EdgeSubset.mk u hc : EdgeSubset (closeBase F G))
      = EdgeSubset.mk (closeJoin s₁ s₂)
        (closeJoin_pairing_mem hc₁ hc₂)) :
    (∑ x : GenBoundaryState k ℓ (Fin t),
        ∑ y : GenBoundaryState k ℓ (Fin t),
          superForm t x y * tensorTermAt F h s₁ x
            * tensorTermAt G h s₂ y)
      = (-1 : ℂ) ^ (glueData t (closeBase F G)
            (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
              (Classical.choice hn₂).1)).rel.openCircuitCount
        * ∑ x : GenBoundaryState k ℓ (Fin t),
            edgeTermOf h (pairFamily h t F G u hc hE hne)
              (diagOf t x)
              (glueCount t (closeBase F G)
                (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
                  (Classical.choice hn₂).1)) :=
  ((Classical.choose_spec
    (exists_pairDatum_sigma_full h t F G u hc hE hne)).2 s₁ hc₁
    hE₁ hn₁ s₂ hc₂ hE₂ hn₂ hused hb hu).2

/-- **The base's directions survive a stage of the lift.**  Both
halves of the invariant come back at the stage: the glue neither
moves a direction nor breaks a flip. -/
theorem baseDirections_stepDataUp (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (b : Bool) (𝒟 : DataFamily V) (hbd : BaseDirections V 𝒟) :
    BaseDirections (stepFragment n V) (stepDataUp n V b 𝒟) := by
  intro t hct hEt hnet hbal
  have ht : t = flagsOfEq
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_open n V hop)
      (flagsOfEq (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
        (gluePair_eq_open n V hop).symm t) :=
    (flagsOfEq_symm (gluePair_eq_open n V hop).symm t).symm
  have hcu := flagsOfEq_pairing_mem
    (gluePair_eq_open n V hop).symm t hct
  have hEg := (relabelUp_eulerian (stepIso n).toEquiv
    (EdgeSubset.mk t hct)).mp hEt
  have hneg := (nonempty_canonData_relabelUp (stepIso n)
    (EdgeSubset.mk t hct)).mp hnet
  have hEu := flagsOfEq_eulerian (gluePair_eq_open n V hop).symm t
    hct hEg
  have hneu := flagsOfEq_canon (gluePair_eq_open n V hop).symm t
    hct hneg
  have hcL := liftSubsetOpen_pairing_closed (cutL_ne_cutR n) hop _
    hcu
  have hEL := (eulerian_lift_open_iff (cutL_ne_cutR n) hop _ hcu
    hcL).mpr hEu
  have hneL := nonempty_canonData_unglueOpen (cutL_ne_cutR n) hop _
    hcu hcL hneu
  have hcbL : CutBalanced V
      (liftSubsetOpen hop _) :=
    cutBalanced_liftSubsetOpen n V hop _ hcu (ht ▸ hbal)
  have hag : (𝒟 _ hcL hEL hneL).2.isOut
        (V.pairing (V.boundaryFlag (cutR n)))
      = !(𝒟 _ hcL hEL hneL).2.isOut
        (V.pairing (V.boundaryFlag (cutL n))) := by
    have h := (hbd _ hcL hEL hneL hcbL).2 (Fin.last n)
    rwa [intR_last, intL_last] at h
  refine ⟨fun bl => ?_, fun m => ?_⟩
  · rw [chainDir_stepDataUp_eq n V hop b 𝒟 _ t ht hct hEt hnet hcL
      hEL hneL hag (fun ℓ => (hbd _ hcL hEL hneL hcbL).1 ℓ) bl,
      isOut_stepDataUp_boundaryFlag n V hop b 𝒟 _ t ht hct hEt hnet
        hcL hEL hneL hag bl]
    exact (hbd _ hcL hEL hneL hcbL).1 _
  · rw [chainDir_stepDataUp_eq n V hop b 𝒟 _ t ht hct hEt hnet hcL
      hEL hneL hag (fun ℓ => (hbd _ hcL hEL hneL hcbL).1 ℓ) (intR n m),
      chainDir_stepDataUp_eq n V hop b 𝒟 _ t ht hct hEt hnet hcL
        hEL hneL hag (fun ℓ => (hbd _ hcL hEL hneL hcbL).1 ℓ)
        (intL n m),
      interfaceStepEquiv_symm_intR, interfaceStepEquiv_symm_intL]
    exact (hbd _ hcL hEL hneL hcbL).2 _

open Classical in
/-- **The base's directions survive a closing glue.**  A closing cut
rewires nothing, so the stage's family reads its boundary flags and
their partners exactly as the base family reads the lift's — and the
lift of a balanced subset is balanced. -/
theorem baseDirections_stepDataUp_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (b : Bool) (𝒟 : DataFamily V) (hbd : BaseDirections V 𝒟) :
    BaseDirections (stepFragment n V) (stepDataUp n V b 𝒟) := by
  intro t hct hEt hnet hbal
  have ht : t = flagsOfEq
      (V.gluePairClosed (cutL n) (cutR n) hcl)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_closed n V hcl)
      (flagsOfEq (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (V.gluePairClosed (cutL n) (cutR n) hcl)
        (gluePair_eq_closed n V hcl).symm t) :=
    (flagsOfEq_symm (gluePair_eq_closed n V hcl).symm t).symm
  have hcu := flagsOfEq_pairing_mem
    (gluePair_eq_closed n V hcl).symm t hct
  have hEg := (relabelUp_eulerian (stepIso n).toEquiv
    (EdgeSubset.mk t hct)).mp hEt
  have hneg := (nonempty_canonData_relabelUp (stepIso n)
    (EdgeSubset.mk t hct)).mp hnet
  have hEu := flagsOfEq_eulerian (gluePair_eq_closed n V hcl).symm t
    hct hEg
  have hneu := flagsOfEq_canon (gluePair_eq_closed n V hcl).symm t
    hct hneg
  have hcL := liftSubsetClosed_pairing_closed hcl _ b hcu
  have hEL := (eulerian_liftClosed_iff' hcl b _ hcu hcL).mpr hEu
  have hneL := nonempty_canonData_unglueClosed hcl _ hcu b hcL hneu
  have hcbL : CutBalanced V (liftSubsetClosed _ b) :=
    cutBalanced_liftSubsetClosed n V hcl _ b (ht ▸ hbal)
  refine ⟨fun bl => ?_, fun m => ?_⟩
  · rw [chainDir_stepDataUp_eq_closed n V hcl b 𝒟 _ t ht hct hEt
      hnet hcL hEL hneL bl,
      isOut_stepDataUp_boundaryFlag_closed n V hcl b 𝒟 _ t ht hct
        hEt hnet hcL hEL hneL bl]
    exact (hbd _ hcL hEL hneL hcbL).1 _
  · rw [chainDir_stepDataUp_eq_closed n V hcl b 𝒟 _ t ht hct hEt
      hnet hcL hEL hneL (intR n m),
      chainDir_stepDataUp_eq_closed n V hcl b 𝒟 _ t ht hct hEt hnet
        hcL hEL hneL (intL n m),
      interfaceStepEquiv_symm_intR, interfaceStepEquiv_symm_intL]
    exact (hbd _ hcL hEL hneL hcbL).2 _

open Classical in
/-- **The family alternates at every cut of the interface.**  RS21's
step 1, as a condition on the family the lift consumes: at every
stage the data give the cut's two flags opposite directions, which is
what an open cut needs to glue its two arcs into one. -/
def Aligned : (n : ℕ) → (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) →
    (Fin n → Bool) → DataFamily V → Prop
  | 0, _, _, _ => True
  | n + 1, V, bits, 𝒟 =>
      (V.pairing (V.boundaryFlag (cutL n)) ≠ V.boundaryFlag (cutR n) →
        ∀ (u : Finset V.Flag) (hc : ∀ f ∈ u, V.pairing f ∈ u)
        (hE : (EdgeSubset.mk u hc).Eulerian)
        (hne : Nonempty (EdgeSubset.mk u hc).CanonData),
        CutBalanced V u →
        (𝒟 u hc hE hne).2.isOut (V.pairing (V.boundaryFlag (cutR n)))
          = !(𝒟 u hc hE hne).2.isOut
            (V.pairing (V.boundaryFlag (cutL n))))
      ∧ Aligned n (stepFragment n V) (fun a => bits a.castSucc)
          (stepDataUp n V (bits (Fin.last n)) 𝒟)

open Classical in
/-- **A subset, dropped to the next stage.** -/
noncomputable def stageSubset (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (s : Finset V.Flag) : Finset (stepFragment n V).Flag :=
  if hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n) then
    flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_closed n V hcl)
      (V.dropSubset (cutL n) (cutR n) s)
  else
    flagsOfEq (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hcl)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_open n V hcl)
      (V.dropSubset (cutL n) (cutR n) s)

/-- **The bits a subset determines.**  At each stage the bit records
whether the subset carries the cut's own edge; the deeper stages read
the dropped subset. -/
noncomputable def bitsOf : ∀ (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) (_s : Finset V.Flag),
    Fin n → Bool
  | 0, _, _ => fun i => i.elim0
  | n + 1, V, s =>
      Fin.snoc
        (bitsOf n (stepFragment n V) (stageSubset n V s))
        (decide (V.boundaryFlag (cutL n) ∈ s))

/-- The top bit a subset determines is whether it carries the cut. -/
theorem bitsOf_last (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (s : Finset V.Flag) :
    bitsOf (n + 1) V s (Fin.last n)
      = decide (V.boundaryFlag (cutL n) ∈ s) := by
  unfold bitsOf
  exact Fin.snoc_last _ _

open Classical in
/-- **A balanced subset's drop is balanced.** -/
theorem cutBalanced_stageSubset (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) (s : Finset V.Flag)
    (hc : ∀ f ∈ s, V.pairing f ∈ s) (hbal : CutBalanced V s) :
    CutBalanced (stepFragment n V) (stageSubset n V s) := by
  intro b
  have hlift : liftSubsetOpen hop
      (V.dropSubset (cutL n) (cutR n) s) = s :=
    liftSubsetOpen_dropSubset (cutL_ne_cutR n) hop s hc
  have key := fun bl => mem_stage_boundaryFlag_iff n V hop
    (V.dropSubset (cutL n) (cutR n) s) bl
  have hss : stageSubset n V s = flagsOfEq
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_open n V hop)
      (V.dropSubset (cutL n) (cutR n) s) := by
    unfold stageSubset
    exact dite_eq_right hop
  rw [hss]
  refine (key (intL n b)).trans (Iff.trans ?_ (key (intR n b)).symm)
  rw [hlift, interfaceStepEquiv_symm_intL n b,
    interfaceStepEquiv_symm_intR n b]
  exact hbal b.castSucc

/-- **A balanced subset agrees at the top cut.** -/
theorem agreeingSubset_of_cutBalanced {n : ℕ}
    {V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0))}
    {u : Finset V.Flag} (hc : ∀ f ∈ u, V.pairing f ∈ u)
    (hcb : CutBalanced V u) :
    AgreeingSubset (cutL n) (cutR n) u := by
  refine ⟨hc, ?_⟩
  have h := hcb (Fin.last n)
  rwa [intL_last, intR_last] at h

/-- The lower bits a subset determines are the drop's own. -/
theorem bitsOf_castSucc (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (s : Finset V.Flag) (a : Fin n) :
    bitsOf (n + 1) V s a.castSucc
      = bitsOf n (stepFragment n V) (stageSubset n V s) a := by
  change (Fin.snoc (bitsOf n (stepFragment n V) (stageSubset n V s))
      (decide (V.boundaryFlag (cutL n) ∈ s)) : Fin (n + 1) → Bool)
      a.castSucc
    = bitsOf n (stepFragment n V) (stageSubset n V s) a
  exact Fin.snoc_castSucc _ _ a

/-- The stage subset, at a closing cut. -/
theorem stageSubset_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) (s : Finset V.Flag) :
    stageSubset n V s
      = flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_closed n V hcl)
        (V.dropSubset (cutL n) (cutR n) s) := by
  unfold stageSubset
  exact dite_eq_left hcl

/-- The stage subset, at an open cut. -/
theorem stageSubset_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) (s : Finset V.Flag) :
    stageSubset n V s
      = flagsOfEq
        (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_open n V hop)
        (V.dropSubset (cutL n) (cutR n) s) := by
  unfold stageSubset
  exact dite_eq_right hop

open Classical in
/-- **The base's directions give the alignment at every stage.**
With no closing cut, a family whose directions flip at the boundary
flags and alternate at every interface pair is aligned all the way
down the interface. -/
theorem aligned_of_baseDirections : ∀ (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))),
    ∀ (bits : Fin n → Bool)
    (𝒟 : DataFamily V), BaseDirections V 𝒟 → Aligned n V bits 𝒟
  | 0, _, _, _, _ => trivial
  | n + 1, V, bits, 𝒟, hbd => by
    refine ⟨fun _ u hc hE hne hcb => ?_, ?_⟩
    · have h := (hbd u hc hE hne hcb).2 (Fin.last n)
      rwa [intR_last, intL_last] at h
    · by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
          = V.boundaryFlag (cutR n)
      · exact aligned_of_baseDirections n (stepFragment n V) _ _
          (baseDirections_stepDataUp_closed n V hcl
            (bits (Fin.last n)) 𝒟 hbd)
      · exact aligned_of_baseDirections n (stepFragment n V) _ _
          (baseDirections_stepDataUp n V hcl (bits (Fin.last n)) 𝒟
            hbd)

open Classical in
/-- **The drop carries the stage's state, at a closing cut.** -/
theorem dropSubset_matches_of_matches_closed {k ℓ : ℕ} (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (x : Fin (n + 1) → (Fin k ⊕ Fin (2 * ℓ)))
    (hm : genBoundarySubsetMatches V s (diagOf (n + 1) x)) :
    genBoundarySubsetMatches
      (V.gluePairClosed (cutL n) (cutR n) hcl)
      (V.dropSubset (cutL n) (cutR n) s)
      (stageState n (diagOf n (fun a => x a.castSucc))) := by
  refine genBoundarySubsetMatches_glued_of_liftClosed hcl
    (V.dropSubset (cutL n) (cutR n) s)
    (decide (V.boundaryFlag (cutL n) ∈ s)) _
    (x (Fin.last n)) (x (Fin.last n)) ?_
  rw [liftSubsetClosed_dropSubset (cutL_ne_cutR n) hcl s hc,
    ← diagOf_succ n x]
  exact hm

open Classical in
/-- **The stage carries the stage's state, at a closing cut.** -/
theorem stage_matches_of_matches_closed {k ℓ : ℕ} (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (x : Fin (n + 1) → (Fin k ⊕ Fin (2 * ℓ)))
    (hm : genBoundarySubsetMatches V s (diagOf (n + 1) x)) :
    genBoundarySubsetMatches (stepFragment n V)
      (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_closed n V hcl)
        (V.dropSubset (cutL n) (cutR n) s))
      (diagOf n (fun a => x a.castSucc)) := by
  refine (relabel_genBoundarySubsetMatches_iff
    (interfaceStepEquiv 0 n 0) _
    (diagOf n (fun a => x a.castSucc))).mpr ?_
  exact genBoundarySubsetMatches_flagsOfEq
    (gluePair_eq_closed n V hcl) _ _
    (dropSubset_matches_of_matches_closed n V hcl s hc x hm)

open Classical in
/-- **The interface round trip at one subset, with the subset's own
bits.**  A closing cut's lift needs a bit, and the bit the subset
itself determines is the one that returns it; the open cuts need the
alignment, as before. -/
theorem match_pushData_liftData_bitsOf {k ℓ : ℕ} : ∀ (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0)))
    (𝒟 : DataFamily V) (x : Fin n → (Fin k ⊕ Fin (2 * ℓ)))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData),
    Aligned n V (bitsOf n V s) 𝒟 →
    genBoundarySubsetMatches V s (diagOf n x) →
    (pushData n V (liftData n V (bitsOf n V s) 𝒟) s hc hE
        hne).1.MatchEq (𝒟 s hc hE hne).1
  | 0, V, 𝒟, _, s, hc, hE, hne, _, _ =>
      match_pushData_liftData_zero V (bitsOf 0 V s) 𝒟 s hc hE hne
  | n + 1, V, 𝒟, x, s, hc, hE, hne, hal, hbm => by
    have hbits : (fun a : Fin n => bitsOf (n + 1) V s a.castSucc)
        = bitsOf n (stepFragment n V) (stageSubset n V s) :=
      funext (fun a => bitsOf_castSucc n V s a)
    by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
        = V.boundaryFlag (cutR n)
    · have hct := dropSubset_pairing_closed_of_closed hcl s hc
      have hcL := liftSubsetClosed_pairing_closed hcl
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s)) hct
      have hlift : liftSubsetClosed
          (V.dropSubset (cutL n) (cutR n) s)
          (decide (V.boundaryFlag (cutL n) ∈ s)) = s :=
        liftSubsetClosed_dropSubset (cutL_ne_cutR n) hcl s hc
      have hF : (EdgeSubset.mk (liftSubsetClosed
            (V.dropSubset (cutL n) (cutR n) s)
            (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
            EdgeSubset V) = EdgeSubset.mk s hc :=
        EdgeSubset.ext hlift
      have hEL : (EdgeSubset.mk (liftSubsetClosed
          (V.dropSubset (cutL n) (cutR n) s)
          (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
          EdgeSubset V).Eulerian := by rw [hF]; exact hE
      have hneL : Nonempty (EdgeSubset.mk (liftSubsetClosed
          (V.dropSubset (cutL n) (cutR n) s)
          (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
          EdgeSubset V).CanonData := by rw [hF]; exact hne
      refine match_pushData_liftData_succ_closed_at n V hcl _ 𝒟 hc
        hE hne (bitsOf_last n V s) ?_ hcL hEL hneL
      intro t ht hct' hEt hnet
      subst ht
      have hbits' : (fun a : Fin n => bitsOf (n + 1) V s a.castSucc)
          = bitsOf n (stepFragment n V)
            (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_closed n V hcl)
              (V.dropSubset (cutL n) (cutR n) s)) := by
        rw [hbits, stageSubset_closed n V hcl s]
      rw [hbits']
      exact match_pushData_liftData_bitsOf n (stepFragment n V) _
        (fun a => x a.castSucc) _ hct' hEt hnet (hbits' ▸ hal.2)
        (stage_matches_of_matches_closed n V hcl s hc x hbm)
    · have hop := hcl
      have hdc := dropSubset_rewire_closed_of_matches n V hcl s hc x
        hbm
      have hcL := liftSubsetOpen_pairing_closed (cutL_ne_cutR n) hcl
        (V.dropSubset (cutL n) (cutR n) s) hdc
      have hlift : liftSubsetOpen hcl
          (V.dropSubset (cutL n) (cutR n) s) = s :=
        liftSubsetOpen_dropSubset (cutL_ne_cutR n) hcl s hc
      have hF : (EdgeSubset.mk (liftSubsetOpen hcl
            (V.dropSubset (cutL n) (cutR n) s)) hcL : EdgeSubset V)
          = EdgeSubset.mk s hc := EdgeSubset.ext hlift
      have hEL : (EdgeSubset.mk (liftSubsetOpen hcl
          (V.dropSubset (cutL n) (cutR n) s)) hcL :
          EdgeSubset V).Eulerian := by rw [hF]; exact hE
      have hneL : Nonempty (EdgeSubset.mk
          (liftSubsetOpen hcl
            (V.dropSubset (cutL n) (cutR n) s)) hcL :
          EdgeSubset V).CanonData := by rw [hF]; exact hne
      refine match_pushData_liftData_succ_open_at n V hcl _ 𝒟 hc hE
        hne ?_ hdc hcL hEL hneL (hal.1 hcl _ hcL hEL hneL
          (by rw [hlift]; exact cutBalanced_of_matches_diag x hbm))
      intro t ht hct' hEt hnet
      subst ht
      have hbits' : (fun a : Fin n => bitsOf (n + 1) V s a.castSucc)
          = bitsOf n (stepFragment n V)
            (flagsOfEq
              (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_open n V hcl)
              (V.dropSubset (cutL n) (cutR n) s)) := by
        rw [hbits, stageSubset_open n V hcl s]
      rw [hbits']
      exact match_pushData_liftData_bitsOf n (stepFragment n V) _
        (fun a => x a.castSucc) _ hct' hEt hnet (hbits' ▸ hal.2)
        (stage_matches_of_matches n V hcl s hc x hbm)

-- Raised budget: the round trip is followed through one stage of
-- the recursion, so the push, the lift and the closing cut all
-- unfold on the same subset.
open Classical in
/-- **The round trip on directions, one stage on, at a closing cut,
at one subset.** -/
theorem isOut_pushData_liftData_succ_closed_at (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (bits : Fin (n + 1) → Bool) (𝒟 : DataFamily V)
    {s : Finset V.Flag} (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc : EdgeSubset V).CanonData)
    (hbit : bits (Fin.last n)
      = decide (V.boundaryFlag (cutL n) ∈ s))
    (hIH : ∀ (t : Finset (stepFragment n V).Flag),
      t = flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_closed n V hcl)
          (V.dropSubset (cutL n) (cutR n) s) →
      ∀ (hct : ∀ f ∈ t, (stepFragment n V).pairing f ∈ t)
        (hEt : (EdgeSubset.mk t hct).Eulerian)
        (hnet : Nonempty (EdgeSubset.mk t hct).CanonData)
        (g : (stepFragment n V).Flag),
      (∀ b, g ≠ (stepFragment n V).boundaryFlag b) →
      (pushData n (stepFragment n V)
          (liftData n (stepFragment n V)
            (fun a => bits a.castSucc)
            (stepDataUp n V (bits (Fin.last n)) 𝒟))
          t hct hEt hnet).2.isOut g
        = (stepDataUp n V (bits (Fin.last n)) 𝒟 t hct hEt
          hnet).2.isOut g)
    (hcL : ∀ f ∈ liftSubsetClosed
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s)),
      V.pairing f ∈ liftSubsetClosed
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s)))
    (hEL : (EdgeSubset.mk (liftSubsetClosed
      (V.dropSubset (cutL n) (cutR n) s)
      (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
      EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk (liftSubsetClosed
      (V.dropSubset (cutL n) (cutR n) s)
      (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
      EdgeSubset V).CanonData)
    (f : V.Flag) (hfb : ∀ a, f ≠ V.boundaryFlag a) :
    (pushData (n + 1) V (liftData (n + 1) V bits 𝒟) s hc hE
        hne).2.isOut f = (𝒟 s hc hE hne).2.isOut f := by
  have h1 : f ≠ V.boundaryFlag (cutL n) := hfb _
  have h2 : f ≠ V.boundaryFlag (cutR n) := hfb _
  have h3 := isOut_stepDataDown_congr_at_closed n V hcl
    (pushData n (stepFragment n V)
      (liftData n (stepFragment n V) (fun a => bits a.castSucc)
        (stepDataUp n V (bits (Fin.last n)) 𝒟)))
    (stepDataUp n V (bits (Fin.last n)) 𝒟) hIH hc hE hne f hfb
  rw [stepData_roundTrip_closed n V hcl (bits (Fin.last n)) 𝒟] at h3
  have h4 := isOut_unglue_glueDataClosed (cutL_ne_cutR n) hcl 𝒟 hc
    hE hne hcL hEL hneL f h1 h2
  rw [← hbit] at h4
  exact h3.trans h4

open Classical in
/-- **The round trip on directions at one subset, with the subset's
own bits.** -/
theorem isOut_pushData_liftData_bitsOf {k ℓ : ℕ} : ∀ (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0)))
    (𝒟 : DataFamily V) (x : Fin n → (Fin k ⊕ Fin (2 * ℓ)))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData),
    Aligned n V (bitsOf n V s) 𝒟 →
    genBoundarySubsetMatches V s (diagOf n x) →
    ∀ (f : V.Flag), (∀ a, f ≠ V.boundaryFlag a) →
    (pushData n V (liftData n V (bitsOf n V s) 𝒟) s hc hE
        hne).2.isOut f = (𝒟 s hc hE hne).2.isOut f
  | 0, V, 𝒟, _, s, hc, hE, hne, _, _, f, _ =>
      isOut_pushData_liftData_zero V (bitsOf 0 V s) 𝒟 s hc hE hne f
  | n + 1, V, 𝒟, x, s, hc, hE, hne, hal, hbm, f, hfb => by
    have hbits : (fun a : Fin n => bitsOf (n + 1) V s a.castSucc)
        = bitsOf n (stepFragment n V) (stageSubset n V s) :=
      funext (fun a => bitsOf_castSucc n V s a)
    -- ═══════ THE CUT CLOSES ═══════
    -- The dropped subset stays pairing-closed and canonical data
    -- migrate across the closed glue; the open branch follows.
    by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
        = V.boundaryFlag (cutR n)
    · have hct := dropSubset_pairing_closed_of_closed hcl s hc
      have hcL := liftSubsetClosed_pairing_closed hcl
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s)) hct
      have hlift : liftSubsetClosed
          (V.dropSubset (cutL n) (cutR n) s)
          (decide (V.boundaryFlag (cutL n) ∈ s)) = s :=
        liftSubsetClosed_dropSubset (cutL_ne_cutR n) hcl s hc
      have hF : (EdgeSubset.mk (liftSubsetClosed
            (V.dropSubset (cutL n) (cutR n) s)
            (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
            EdgeSubset V) = EdgeSubset.mk s hc :=
        EdgeSubset.ext hlift
      have hEL : (EdgeSubset.mk (liftSubsetClosed
          (V.dropSubset (cutL n) (cutR n) s)
          (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
          EdgeSubset V).Eulerian := by rw [hF]; exact hE
      have hneL : Nonempty (EdgeSubset.mk (liftSubsetClosed
          (V.dropSubset (cutL n) (cutR n) s)
          (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
          EdgeSubset V).CanonData := by rw [hF]; exact hne
      refine isOut_pushData_liftData_succ_closed_at n V hcl _ 𝒟 hc
        hE hne (bitsOf_last n V s) ?_ hcL hEL hneL f hfb
      intro t ht hct' hEt hnet g hgb
      subst ht
      have hbits' : (fun a : Fin n => bitsOf (n + 1) V s a.castSucc)
          = bitsOf n (stepFragment n V)
            (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_closed n V hcl)
              (V.dropSubset (cutL n) (cutR n) s)) := by
        rw [hbits, stageSubset_closed n V hcl s]
      rw [hbits']
      exact isOut_pushData_liftData_bitsOf n (stepFragment n V) _
        (fun a => x a.castSucc) _ hct' hEt hnet (hbits' ▸ hal.2)
        (stage_matches_of_matches_closed n V hcl s hc x hbm) g hgb
    · have hdc := dropSubset_rewire_closed_of_matches n V hcl s hc x
        hbm
      have hcL := liftSubsetOpen_pairing_closed (cutL_ne_cutR n) hcl
        (V.dropSubset (cutL n) (cutR n) s) hdc
      have hlift : liftSubsetOpen hcl
          (V.dropSubset (cutL n) (cutR n) s) = s :=
        liftSubsetOpen_dropSubset (cutL_ne_cutR n) hcl s hc
      have hF : (EdgeSubset.mk (liftSubsetOpen hcl
            (V.dropSubset (cutL n) (cutR n) s)) hcL : EdgeSubset V)
          = EdgeSubset.mk s hc := EdgeSubset.ext hlift
      have hEL : (EdgeSubset.mk (liftSubsetOpen hcl
          (V.dropSubset (cutL n) (cutR n) s)) hcL :
          EdgeSubset V).Eulerian := by rw [hF]; exact hE
      have hneL : Nonempty (EdgeSubset.mk
          (liftSubsetOpen hcl
            (V.dropSubset (cutL n) (cutR n) s)) hcL :
          EdgeSubset V).CanonData := by rw [hF]; exact hne
      refine isOut_pushData_liftData_succ_open_at n V hcl _ 𝒟 hc hE
        hne ?_ hdc hcL hEL hneL (hal.1 hcl _ hcL hEL hneL
          (by rw [hlift]; exact cutBalanced_of_matches_diag x hbm))
        f hfb
      intro t ht hct' hEt hnet g hgb
      subst ht
      have hbits' : (fun a : Fin n => bitsOf (n + 1) V s a.castSucc)
          = bitsOf n (stepFragment n V)
            (flagsOfEq
              (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_open n V hcl)
              (V.dropSubset (cutL n) (cutR n) s)) := by
        rw [hbits, stageSubset_open n V hcl s]
      rw [hbits']
      exact isOut_pushData_liftData_bitsOf n (stepFragment n V) _
        (fun a => x a.castSucc) _ hct' hEt hnet (hbits' ▸ hal.2)
        (stage_matches_of_matches n V hcl s hc x hbm) g hgb

open Classical in
/-- **A balanced subset's drop is balanced**, at a closing cut. -/
theorem cutBalanced_stageSubset_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) (s : Finset V.Flag)
    (hc : ∀ f ∈ s, V.pairing f ∈ s) (hbal : CutBalanced V s) :
    CutBalanced (stepFragment n V) (stageSubset n V s) := by
  intro b
  have hlift : liftSubsetClosed
      (V.dropSubset (cutL n) (cutR n) s)
      (decide (V.boundaryFlag (cutL n) ∈ s)) = s :=
    liftSubsetClosed_dropSubset (cutL_ne_cutR n) hcl s hc
  have key := fun bl => mem_stage_boundaryFlag_iff_closed n V hcl
    (V.dropSubset (cutL n) (cutR n) s)
    (decide (V.boundaryFlag (cutL n) ∈ s)) bl
  have hss : stageSubset n V s = flagsOfEq
      (V.gluePairClosed (cutL n) (cutR n) hcl)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_closed n V hcl)
      (V.dropSubset (cutL n) (cutR n) s) := by
    unfold stageSubset
    exact dite_eq_left hcl
  rw [hss]
  refine (key (intL n b)).trans (Iff.trans ?_ (key (intR n b)).symm)
  rw [hlift, interfaceStepEquiv_symm_intL n b,
    interfaceStepEquiv_symm_intR n b]
  exact hbal b.castSucc

open Classical in
/-- **A base subset's whole colour sum is the composition's own
term.**  Summed over the interface colourings, a guarded balanced
subset's summand is the composition's term at the subset's image,
times the free circles the subset's own closing cuts contribute.
Nothing is asked of the family: the identification is stage by stage,
an open cut summing its colour away and a closing one splitting into
the free circle's two sectors. -/
theorem edgeTermAt_pushData_colourSum {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) :
    ∀ (n : ℕ) (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0)))
      (𝒢 : DataFamily (glueInterface 0 n 0 V)) (s : Finset V.Flag),
      (∀ f ∈ s, V.pairing f ∈ s) → CutBalanced V s → ∀ (C : ℕ),
      (∑ x : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
          edgeTermAt h (pushData n V 𝒢) (diagOf n x) s
            (C + carried n V s))
        = cutFactor k ℓ n V s
          * edgeTermAt h 𝒢 emptyState (imageOf n V s) C
  | 0, V, 𝒢, s, _, _, C => by
      rw [Fintype.sum_unique]
      change edgeTermAt h (relabelDataDown baseIso 𝒢) _ s C
        = (1 : ℂ) * _
      rw [one_mul]
      refine Eq.trans ?_
        (edgeTermAt_relabel baseIso h 𝒢 emptyState s C).symm
      exact congrArg
        (fun st => edgeTermAt h (relabelDataDown baseIso 𝒢) st s C)
        (funext fun a => isEmptyElim a)
  | n + 1, V, 𝒢, s, hc, hbal, C => by
      change (∑ x : Fin (n + 1) → (Fin k ⊕ Fin (2 * ℓ)),
          edgeTermAt h (stepDataDown n V
            (pushData n (stepFragment n V) 𝒢)) (diagOf (n + 1) x) s
            (C + carried (n + 1) V s)) = _
      rw [sum_colours_snoc h n V (pushData n (stepFragment n V) 𝒢) s
        (C + carried (n + 1) V s)]
      -- ═══════ THE CUT CLOSES ═══════
      -- The dropped subset stays pairing-closed and the stage's own
      -- factor is the closed one; the open branch follows below.
      by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
          = V.boundaryFlag (cutR n)
      · have hct : ∀ f ∈ V.dropSubset (cutL n) (cutR n) s,
            (V.gluePairClosed (cutL n) (cutR n) hcl).pairing f
              ∈ V.dropSubset (cutL n) (cutR n) s :=
          dropSubset_pairing_closed_of_closed hcl s hc
        have hcs := flagsOfEq_pairing_mem
          (gluePair_eq_closed n V hcl) _ hct
        have hb2 := cutBalanced_stageSubset_closed n V hcl s hc hbal
        rw [stageSubset_closed n V hcl s] at hb2
        have hIH := edgeTermAt_pushData_colourSum h n
          (stepFragment n V) 𝒢
          (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_closed n V hcl)
            (V.dropSubset (cutL n) (cutR n) s)) hcs hb2 C
        obtain ⟨t, b, hs⟩ : ∃ (t : Finset (SurvivingFlag V (cutL n)
            (cutR n))) (b : Bool), liftSubsetClosed t b = s :=
          ⟨_, _, liftSubsetClosed_dropSubset (cutL_ne_cutR n) hcl s
            hc⟩
        subst hs
        rw [dropSubset_liftSubsetClosed t b] at hIH
        have hinner : ∀ y : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
            (∑ c : Fin k ⊕ Fin (2 * ℓ),
                edgeTermAt h (stepDataDown n V
                  (pushData n (stepFragment n V) 𝒢))
                  (GenBoundaryState.extendPair (cutL n) (cutR n)
                    (stageState n (diagOf n y)) c c)
                  (liftSubsetClosed t b)
                  (C + ((if b = true then 1 else 0)
                    + carried n (stepFragment n V) (flagsOfEq (V.gluePairClosed
                      (cutL n) (cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_closed n V hcl) t))))
              = (if b = true then (-(2 * ℓ : ℕ) : ℂ) else (k : ℂ))
                * edgeTermAt h (pushData n (stepFragment n V) 𝒢)
                  (diagOf n y) (flagsOfEq (V.gluePairClosed (cutL n) (cutR n)
                    hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_closed n V hcl) t)
                  (C + carried n (stepFragment n V) (flagsOfEq (V.gluePairClosed
                    (cutL n) (cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_closed n V hcl) t)) := by
          intro y
          cases b with
          | false =>
              rw [show C + ((if (false : Bool) = true then 1 else 0)
                    + carried n (stepFragment n V) (flagsOfEq (V.gluePairClosed
                      (cutL n) (cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_closed n V hcl) t))
                  = C + carried n (stepFragment n V) (flagsOfEq
                    (V.gluePairClosed (cutL n) (cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_closed n V hcl) t)
                from by simp, ite_eq_right (by simp : ¬ ((false : Bool)
                  = true))]
              exact edgeTermAt_stepClosed_false_all n V h
                (pushData n (stepFragment n V) 𝒢) hcl t (diagOf n y)
                _
          | true =>
              rw [show C + ((if (true : Bool) = true then 1 else 0)
                    + carried n (stepFragment n V) (flagsOfEq (V.gluePairClosed
                      (cutL n) (cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_closed n V hcl) t))
                  = (C + carried n (stepFragment n V) (flagsOfEq
                    (V.gluePairClosed (cutL n) (cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_closed n V hcl) t)) + 1
                from by simp; omega, ite_eq_left rfl]
              exact edgeTermAt_stepClosed_true_all n V h
                (pushData n (stepFragment n V) 𝒢) hcl t (diagOf n y)
                _
        rw [carried_liftClosed n V hcl t b,
          cutFactor_liftClosed k ℓ n V hcl t b,
          imageOf_succ_closed n V hcl (liftSubsetClosed t b),
          dropSubset_liftSubsetClosed t b]
        refine Eq.trans (Finset.sum_congr rfl
          (fun y (_ : y ∈ Finset.univ) => hinner y)) ?_
        rw [← Finset.mul_sum, mul_assoc]
        exact congrArg (fun z => (if b = true then
          (-(2 * ℓ : ℕ) : ℂ) else (k : ℂ)) * z) hIH
      · have hct : ∀ f ∈ V.dropSubset (cutL n) (cutR n) s,
            (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
                hcl).pairing f
              ∈ V.dropSubset (cutL n) (cutR n) s :=
          dropSubset_rewire_closed (hopen := hcl) s
            (agreeingSubset_of_cutBalanced hc hbal)
        have hcs := flagsOfEq_pairing_mem
          (gluePair_eq_open n V hcl) _ hct
        have hb2 := cutBalanced_stageSubset n V hcl s hc hbal
        rw [stageSubset_open n V hcl s] at hb2
        have hIH := edgeTermAt_pushData_colourSum h n
          (stepFragment n V) 𝒢
          (flagsOfEq
            (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_open n V hcl)
            (V.dropSubset (cutL n) (cutR n) s)) hcs hb2 C
        obtain ⟨t, hs⟩ : ∃ t : Finset (SurvivingFlag V (cutL n)
            (cutR n)), liftSubsetOpen hcl t = s :=
          ⟨_, liftSubsetOpen_dropSubset (cutL_ne_cutR n) hcl s hc⟩
        subst hs
        rw [dropSubset_liftSubsetOpen hcl t] at hIH
        have hinner : ∀ y : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
            (∑ c : Fin k ⊕ Fin (2 * ℓ),
                edgeTermAt h (stepDataDown n V
                  (pushData n (stepFragment n V) 𝒢))
                  (GenBoundaryState.extendPair (cutL n) (cutR n)
                    (stageState n (diagOf n y)) c c)
                  (liftSubsetOpen hcl t)
                  (C + carried n (stepFragment n V) (flagsOfEq (V.gluePairOpen
                    (cutL n) (cutR n) (cutL_ne_cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_open n V hcl) t)))
              = edgeTermAt h (pushData n (stepFragment n V) 𝒢)
                  (diagOf n y) (flagsOfEq (V.gluePairOpen (cutL n) (cutR n)
                    (cutL_ne_cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_open n V hcl) t)
                  (C + carried n (stepFragment n V) (flagsOfEq (V.gluePairOpen
                    (cutL n) (cutR n) (cutL_ne_cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_open n V hcl) t)) :=
          fun y => edgeTermAt_stepOpen_all n V h
            (pushData n (stepFragment n V) 𝒢) hcl t (diagOf n y) _
        rw [carried_liftOpen n V hcl t,
          cutFactor_liftOpen k ℓ n V hcl t,
          imageOf_succ_open n V hcl
            (liftSubsetOpen hcl t),
          dropSubset_liftSubsetOpen hcl t]
        refine Eq.trans (Finset.sum_congr rfl
          (fun y (_ : y ∈ Finset.univ) => hinner y)) hIH

open Classical in
/-- **The base sum with the subset's own bits** — the statement the
closing cut needs.  The composition's own sum is family-free, so the
left side may be read at any fixed bits; the right side reads each
base subset with the bits that subset itself determines, which is
what the round trip asks for. -/
def BaseSumBitsOf {k ℓ : ℕ} (h : MixedFunctional k ℓ) (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) (𝒟 : DataFamily V)
    (C : ℕ) : Prop :=
  ((k : ℂ) - 2 * ℓ) ^ closedCuts n V
      * ∑ u : Finset (glueInterface 0 n 0 V).Flag,
        circuitWeight (liftData n V (fun _ => false) 𝒟) u
          * edgeTermAt h (liftData n V (fun _ => false) 𝒟)
            emptyState u C
    = ∑ s : Finset V.Flag,
        ∑ x : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
          circuitWeight (liftData n V (bitsOf n V s) 𝒟)
              (imageOf n V s)
            * edgeTermAt h
              (pushData n V (liftData n V (bitsOf n V s) 𝒟))
              (diagOf n x) s (C + carried n V s)

open Classical in
/-- **THE SUMMAND DOES NOT READ THE LIFT'S BITS.**  Summed over the
interface colourings, a base subset's weighted summand is the free
circles its own closing cuts contribute, times the composition's own
weighted term at its image — and that product is family-free at the
closed top.  So which lift computed it makes no difference. -/
theorem summandSum_bits_indep {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (n : ℕ) (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0)))
    (𝒟 : DataFamily V) (s : Finset V.Flag) (C : ℕ)
    (bits bits' : Fin n → Bool) :
    (∑ x : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
        circuitWeight (liftData n V bits 𝒟) (imageOf n V s)
          * edgeTermAt h (pushData n V (liftData n V bits 𝒟))
            (diagOf n x) s (C + carried n V s))
      = ∑ x : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
          circuitWeight (liftData n V bits' 𝒟) (imageOf n V s)
            * edgeTermAt h (pushData n V (liftData n V bits' 𝒟))
              (diagOf n x) s (C + carried n V s) := by
  by_cases hc : ∀ f ∈ s, V.pairing f ∈ s
  · by_cases hbal : CutBalanced V s
    · rw [← Finset.mul_sum, ← Finset.mul_sum,
        edgeTermAt_pushData_colourSum h n V (liftData n V bits 𝒟) s
          hc hbal C,
        edgeTermAt_pushData_colourSum h n V (liftData n V bits' 𝒟) s
          hc hbal C]
      calc circuitWeight (liftData n V bits 𝒟) (imageOf n V s)
            * (cutFactor k ℓ n V s
              * edgeTermAt h (liftData n V bits 𝒟) emptyState
                (imageOf n V s) C)
          = cutFactor k ℓ n V s
              * (circuitWeight (liftData n V bits 𝒟)
                  (imageOf n V s)
                * edgeTermAt h (liftData n V bits 𝒟) emptyState
                  (imageOf n V s) C) := by ring
        _ = cutFactor k ℓ n V s
              * (circuitWeight (liftData n V bits' 𝒟)
                  (imageOf n V s)
                * edgeTermAt h (liftData n V bits' 𝒟) emptyState
                  (imageOf n V s) C) :=
            congrArg (fun z => cutFactor k ℓ n V s * z)
              (circuitWeight_mul_edgeTermAt_indep h emptyState
                (imageOf n V s) C (liftData n V bits 𝒟)
                (liftData n V bits' 𝒟))
        _ = circuitWeight (liftData n V bits' 𝒟) (imageOf n V s)
              * (cutFactor k ℓ n V s
                * edgeTermAt h (liftData n V bits' 𝒟) emptyState
                  (imageOf n V s) C) := by ring
    · rw [Finset.sum_eq_zero (fun x _ => ?_),
        Finset.sum_eq_zero (fun x _ => ?_)]
      · rw [edgeTermAt_eq_zero_of_not_matches h _ _
          (fun hx => hbal (cutBalanced_of_matches_diag x hx)) _,
          mul_zero]
      · rw [edgeTermAt_eq_zero_of_not_matches h _ _
          (fun hx => hbal (cutBalanced_of_matches_diag x hx)) _,
          mul_zero]
  · rw [Finset.sum_eq_zero (fun x _ => ?_),
      Finset.sum_eq_zero (fun x _ => ?_)]
    · rw [edgeTermAt_eq_zero_of_not_closed h _ _ hc _, mul_zero]
    · rw [edgeTermAt_eq_zero_of_not_closed h _ _ hc _, mul_zero]

open Classical in
/-- **THE BASE SUM, WITH EACH SUBSET'S OWN BITS.**  The composition's
own total is the sum over the base's subsets of the summand each
subset's own bits compute — because the summand does not read the
bits at all. -/
theorem baseSumBitsOf_all {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (n : ℕ) (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0)))
    (𝒟 : DataFamily V) (C : ℕ) :
    BaseSumBitsOf h n V 𝒟 C := by
  unfold BaseSumBitsOf
  refine Eq.trans (edgeTermAt_glueInterface h n V
    (liftData n V (fun _ => false) 𝒟) C
    (circuitWeight (liftData n V (fun _ => false) 𝒟))) ?_
  exact Finset.sum_congr rfl (fun s _ =>
    summandSum_bits_indep h n V 𝒟 s C (fun _ => false)
      (bitsOf n V s))

open Classical in
/-- **The pushed lift computes the family's own term, with the
subset's own bits** — at a closing cut as much as an open one. -/
theorem edgeTermAt_pushData_liftData_bitsOf {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) (𝒟 : DataFamily V)
    (x : Fin n → (Fin k ⊕ Fin (2 * ℓ))) {s : Finset V.Flag}
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hbnd : genBoundarySubsetMatches V s (diagOf n x))
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData)
    (hal : Aligned n V (bitsOf n V s) 𝒟) (C : ℕ) :
    edgeTermAt h (pushData n V (liftData n V (bitsOf n V s) 𝒟))
        (diagOf n x) s C
      = edgeTermAt h 𝒟 (diagOf n x) s C := by
  rw [edgeTermAt_eq_signed_edgeSum_internal h
      (pushData n V (liftData n V (bitsOf n V s) 𝒟)) (diagOf n x)
      hc hbnd hE hne C (𝒟 s hc hE hne).2
      (match_pushData_liftData_bitsOf n V 𝒟 x s hc hE hne hal hbnd)
      (fun f hf => isOut_pushData_liftData_bitsOf n V 𝒟 x s hc hE
        hne hal hbnd f
        (ne_boundaryFlag_of_mem_internalFlags _ hf)),
    edgeTermAt_pos h 𝒟 (diagOf n x) hc hbnd hE hne C]

open Classical in
/-- **The pushed lift computes the family's own term, at every
subset, with the subset's own bits.**  Off the matching subsets both
terms vanish, and elsewhere the round trip at the subset's own bits
returns the family — at a closing cut as much as an open one. -/
theorem edgeTermAt_pushData_liftData_all_bitsOf {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0)))
    (𝒟 : DataFamily V)
    (hal : ∀ s : Finset V.Flag, Aligned n V (bitsOf n V s) 𝒟)
    (x : Fin n → (Fin k ⊕ Fin (2 * ℓ))) (s : Finset V.Flag)
    (C : ℕ) :
    edgeTermAt h (pushData n V (liftData n V (bitsOf n V s) 𝒟))
        (diagOf n x) s C
      = edgeTermAt h 𝒟 (diagOf n x) s C := by
  by_cases hc : ∀ f ∈ s, V.pairing f ∈ s
  · by_cases hbnd : genBoundarySubsetMatches V s (diagOf n x)
    · by_cases hE : (EdgeSubset.mk s hc).Eulerian
      · by_cases hne : Nonempty (EdgeSubset.mk s hc).CanonData
        · exact edgeTermAt_pushData_liftData_bitsOf h n V 𝒟 x hc
            hbnd hE hne (hal s) C
        · rw [edgeTermAt_eq_zero_of_not_canon h _ _ hc hne C,
            edgeTermAt_eq_zero_of_not_canon h 𝒟 _ hc hne C]
      · rw [edgeTermAt_eq_zero_of_not_eulerian h _ _ hc hE C,
          edgeTermAt_eq_zero_of_not_eulerian h 𝒟 _ hc hE C]
    · rw [edgeTermAt_eq_zero_of_not_matches h _ _ hbnd C,
        edgeTermAt_eq_zero_of_not_matches h 𝒟 _ hbnd C]
  · rw [edgeTermAt_eq_zero_of_not_closed h _ _ hc C,
      edgeTermAt_eq_zero_of_not_closed h 𝒟 _ hc C]

open Classical in
/-- **The stage subset is the ledger's step.** -/
theorem stageSubset_stepData (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (D : StageData (n + 1) V) :
    stageSubset n V D.sub.flags = (stepData n V D).sub.flags := by
  by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)
  · rw [stageSubset_closed n V hcl, stepData_sub_flags_closed n V D
      hcl]
  · rw [stageSubset_open n V hcl, stepData_sub_flags_open n V D hcl]

open Classical in
/-- **The bits the ledger's subset determines, one stage on.** -/
theorem bitsOf_stepData (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (D : StageData (n + 1) V) :
    (fun a : Fin n => bitsOf (n + 1) V D.sub.flags a.castSucc)
      = bitsOf n (stepFragment n V) (stepData n V D).sub.flags := by
  refine funext (fun a => ?_)
  rw [bitsOf_castSucc n V D.sub.flags a, stageSubset_stepData n V D]

open Classical in
/-- **The lift is the ledger, at every interface.**  Read with the
bits the ledger's own subset determines, the lifted family's system
at the glued subset is the ledger's glued system, up to its partner
map — at a closing cut as much as an open one, because the bit the
subset determines is the bit the ledger's step uses. -/
theorem match_liftData_glueData_bitsOf : ∀ (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0)))
    (𝒟 : DataFamily V) (D : StageData n V),
    Aligned n V (bitsOf n V D.sub.flags) 𝒟 →
    (∀ hc hE hne, (𝒟 D.sub.flags hc hE hne).1.MatchEq D.rel) →
    CutBalanced V D.sub.flags →
    ∀ (hc : ∀ f ∈ (glueData n V D).sub.flags,
      (glueInterface 0 n 0 V).pairing f ∈ (glueData n V D).sub.flags)
      (hE : (EdgeSubset.mk (glueData n V D).sub.flags hc).Eulerian)
      (hne : Nonempty
        (EdgeSubset.mk (glueData n V D).sub.flags hc).CanonData),
    (liftData n V (bitsOf n V D.sub.flags) 𝒟
        (glueData n V D).sub.flags hc hE hne).1.MatchEq
      (glueData n V D).rel
  | 0, V, 𝒟, D, _, hcompat, _, hc, hE, hne => by
    intro f hf
    exact hcompat _ _ _ f
      ((relabelUp_internalFlags endEquiv D.sub) ▸ hf)
  | n + 1, V, 𝒟, D, hal, hcompat, hbal, hc, hE, hne => by
    have hal' : (V.pairing (V.boundaryFlag (cutL n))
        ≠ V.boundaryFlag (cutR n) → ∀ (u : Finset V.Flag)
        (hcu : ∀ f ∈ u, V.pairing f ∈ u)
        (hEu : (EdgeSubset.mk u hcu).Eulerian)
        (hneu : Nonempty (EdgeSubset.mk u hcu).CanonData),
        CutBalanced V u →
        (𝒟 u hcu hEu hneu).2.isOut
            (V.pairing (V.boundaryFlag (cutR n)))
          = !(𝒟 u hcu hEu hneu).2.isOut
            (V.pairing (V.boundaryFlag (cutL n))))
      ∧ Aligned n (stepFragment n V)
          (fun a => bitsOf (n + 1) V D.sub.flags a.castSucc)
          (stepDataUp n V
            (bitsOf (n + 1) V D.sub.flags (Fin.last n)) 𝒟) := hal
    have hbits := bitsOf_stepData n V D
    have hlast : bitsOf (n + 1) V D.sub.flags (Fin.last n)
        = stepBit n V D := bitsOf_last n V D.sub.flags
    change (liftData n (stepFragment n V)
        (fun a => bitsOf (n + 1) V D.sub.flags a.castSucc)
        (stepDataUp n V
          (bitsOf (n + 1) V D.sub.flags (Fin.last n)) 𝒟)
        (glueData n (stepFragment n V) (stepData n V D)).sub.flags
        hc hE hne).1.MatchEq
      (glueData n (stepFragment n V) (stepData n V D)).rel
    rw [hbits, hlast]
    rw [hbits, hlast] at hal'
    by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
        = V.boundaryFlag (cutR n)
    · exact match_liftData_glueData_bitsOf n (stepFragment n V)
        (stepDataUp n V (stepBit n V D) 𝒟) (stepData n V D) hal'.2
        (fun hct hEt hnet => match_stepDataUp_stepData_closed n V
          hcl 𝒟 D hcompat hct hEt hnet)
        (cutBalanced_stepData_closed n V hcl D hbal) hc hE hne
    · exact match_liftData_glueData_bitsOf n (stepFragment n V)
        (stepDataUp n V (stepBit n V D) 𝒟) (stepData n V D) hal'.2
        (fun hct hEt hnet => match_stepDataUp_stepData_open n V hcl
          (stepBit n V D) 𝒟 D hcompat
          (fun hcL hEL hneL => hal'.1 hcl _ hcL hEL hneL
            (by
              change CutBalanced V (liftSubsetOpen
                hcl (V.dropSubset (cutL n) (cutR n) D.sub.flags))
              rw [liftSubsetOpen_dropSubset (cutL_ne_cutR n) hcl
                D.sub.flags D.sub.pairing_mem]
              exact hbal)) hct hEt hnet)
        (cutBalanced_stepData n V hcl D hbal) hc hE hne

open Classical in
/-- **The composition's weight is the ledger's sign, at every
interface.**  Read with the bits the ledger's own subset determines,
the weight the composition's sum carries at the image of a base
subset is exactly the circuit sign the ledger records for it. -/
theorem circuitWeight_liftData_imageOf_bitsOf (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0)))
    (𝒟 : DataFamily V) (D : StageData n V)
    (hal : Aligned n V (bitsOf n V D.sub.flags) 𝒟)
    (hcompat : ∀ hc hE hne,
      (𝒟 D.sub.flags hc hE hne).1.MatchEq D.rel)
    (hbal : CutBalanced V D.sub.flags)
    (hE : (EdgeSubset.mk (glueData n V D).sub.flags
      (glueData n V D).sub.pairing_mem).Eulerian)
    (hne : Nonempty (EdgeSubset.mk (glueData n V D).sub.flags
      (glueData n V D).sub.pairing_mem).CanonData) :
    circuitWeight (liftData n V (bitsOf n V D.sub.flags) 𝒟)
        (imageOf n V D.sub.flags)
      = (-1 : ℂ) ^ (glueData n V D).rel.openCircuitCount := by
  rw [imageOf_eq_glueData_sub n V D,
    circuitWeight_pos (liftData n V (bitsOf n V D.sub.flags) 𝒟)
      (glueData n V D).sub.pairing_mem hE hne]
  exact congrArg (fun m => (-1 : ℂ) ^ m)
    (openCircuitCount_matchEq (RelTransitionSystem.MatchEq.symm
      (match_liftData_glueData_bitsOf n V 𝒟 D hal hcompat hbal _
        hE hne)))

open Classical in
/-- **A term of the fragment tensor needs its own labels.** -/
theorem tensorTermAt_eq_zero_of_not_matches {α : Type}
    [LinearOrder α] [Fintype α] (V : Fragment α) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (s : Finset V.Flag)
    (x : GenBoundaryState k ℓ α)
    (hx : ¬ genBoundarySubsetMatches V s x) :
    tensorTermAt V h s x = 0 := by
  unfold tensorTermAt
  split_ifs with hc hE hne
  · exact tFull_eq_zero_of_not_matches (EdgeSubset.mk s hc) h _ _ x
      hx
  · rfl
  · rfl
  · rfl

open Classical in
/-- **An unclosed subset carries no tensor term.** -/
theorem tensorTermAt_eq_zero_of_not_closed {α : Type} [LinearOrder α]
    [Fintype α] (V : Fragment α) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (s : Finset V.Flag) (x : GenBoundaryState k ℓ α)
    (hc : ¬ ∀ f ∈ s, V.pairing f ∈ s) : tensorTermAt V h s x = 0 := by
  unfold tensorTermAt
  rw [dite_eq_right hc]

open Classical in
/-- **A non-Eulerian subset carries no tensor term.** -/
theorem tensorTermAt_eq_zero_of_not_eulerian {α : Type}
    [LinearOrder α] [Fintype α] (V : Fragment α) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) {s : Finset V.Flag}
    (hc : ∀ f ∈ s, V.pairing f ∈ s) (x : GenBoundaryState k ℓ α)
    (hE : ¬ (EdgeSubset.mk s hc).Eulerian) :
    tensorTermAt V h s x = 0 := by
  unfold tensorTermAt
  rw [dite_eq_left hc, dite_eq_right hE]

open Classical in
/-- **A subset with no canonical data carries no tensor term.** -/
theorem tensorTermAt_eq_zero_of_not_canon {α : Type} [LinearOrder α]
    [Fintype α] (V : Fragment α) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    {s : Finset V.Flag} (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (x : GenBoundaryState k ℓ α)
    (hne : ¬ Nonempty (EdgeSubset.mk s hc).CanonData) :
    tensorTermAt V h s x = 0 := by
  unfold tensorTermAt
  rw [dite_eq_left hc, dite_eq_left hE, dite_eq_right hne]

open Classical in
/-- **Tensors of subsets using different labels are orthogonal.** -/
theorem pairTerm_eq_zero_of_used_ne {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t))
    (s₁ : Finset F.Flag) (s₂ : Finset G.Flag) (i : Fin t)
    (h₁ : F.boundaryFlag i ∈ s₁) (h₂ : G.boundaryFlag i ∉ s₂) :
    (∑ x : GenBoundaryState k ℓ (Fin t),
        ∑ y : GenBoundaryState k ℓ (Fin t),
          superForm t x y * tensorTermAt F h s₁ x
            * tensorTermAt G h s₂ y) = 0 := by
  refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero
    (fun y _ => ?_))
  by_cases hx : genBoundarySubsetMatches F s₁ x
  · by_cases hy : genBoundarySubsetMatches G s₂ y
    · obtain ⟨c, hcx⟩ := (hx i).mp h₁
      obtain ⟨a, hay⟩ := exists_left_of_not_right
        (fun hr => h₂ ((hy i).mpr hr))
      rw [superForm_eq_zero_of_right_left x y i hcx hay]
      ring
    · rw [tensorTermAt_eq_zero_of_not_matches G h s₂ y hy]
      ring
  · rw [tensorTermAt_eq_zero_of_not_matches F h s₁ x hx]
    ring

open Classical in
/-- **The join is Eulerian when its halves are.** -/
theorem eulerian_closeJoin {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (hE₁ : (EdgeSubset.mk s₁ hc₁).Eulerian)
    (hE₂ : (EdgeSubset.mk s₂ hc₂).Eulerian) :
    (EdgeSubset.mk (closeJoin s₁ s₂)
      (closeJoin_pairing_mem hc₁ hc₂)).Eulerian := by
  refine (eulerian_iff_parts (closeJoin s₁ s₂)
    (closeJoin_pairing_mem hc₁ hc₂)
    (by
      rw [show leftPart (closeJoin s₁ s₂) = s₁ from
        leftPart_joinParts s₁ s₂]
      exact hc₁)
    (by
      rw [show rightPart (closeJoin s₁ s₂) = s₂ from
        rightPart_joinParts s₁ s₂]
      exact hc₂)).mpr ⟨?_, ?_⟩
  · have h1 : (EdgeSubset.mk (leftPart (closeJoin s₁ s₂))
        (by
          rw [show leftPart (closeJoin s₁ s₂) = s₁ from
            leftPart_joinParts s₁ s₂]
          exact hc₁) :
        EdgeSubset (F.relabel (finCongr (by omega : t = 0 + t))))
        = (EdgeSubset.mk s₁ hc₁ :
          EdgeSubset (F.relabel (finCongr (by omega : t = 0 + t)))) :=
      EdgeSubset.ext (leftPart_joinParts s₁ s₂)
    rw [h1]
    exact (relabelUp_eulerian (finCongr (by omega : t = 0 + t))
      (EdgeSubset.mk s₁ hc₁ : EdgeSubset F)).mpr hE₁
  · have h2 : (EdgeSubset.mk (rightPart (closeJoin s₁ s₂))
        (by
          rw [show rightPart (closeJoin s₁ s₂) = s₂ from
            rightPart_joinParts s₁ s₂]
          exact hc₂) :
        EdgeSubset (G.relabel (finCongr (by omega : t = t + 0))))
        = (EdgeSubset.mk s₂ hc₂ :
          EdgeSubset (G.relabel (finCongr (by omega : t = t + 0)))) :=
      EdgeSubset.ext (rightPart_joinParts s₁ s₂)
    rw [h2]
    exact (relabelUp_eulerian (finCongr (by omega : t = t + 0))
      (EdgeSubset.mk s₂ hc₂ : EdgeSubset G)).mpr hE₂

open Classical in
/-- **The join carries canonical data when its halves do.** -/
theorem canonData_closeJoin {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (hused : ∀ i : Fin t,
      F.boundaryFlag i ∈ s₁ ↔ G.boundaryFlag i ∈ s₂)
    (hn₁ : Nonempty (EdgeSubset.mk s₁ hc₁).CanonData)
    (hn₂ : Nonempty (EdgeSubset.mk s₂ hc₂).CanonData) :
    Nonempty (EdgeSubset.mk (closeJoin s₁ s₂)
      (closeJoin_pairing_mem hc₁ hc₂)).CanonData :=
  (nonempty_canonData_iff_system _).mpr
    ⟨(pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
      (Classical.choice hn₂).1).rel⟩

open Classical in
/-- **An unclosed half leaves the join unclosed.** -/
theorem not_closeJoin_closed_left {t : ℕ} {F G : Fragment (Fin t)}
    (s₁ : Finset F.Flag) (s₂ : Finset G.Flag)
    (hc₁ : ¬ ∀ f ∈ s₁, F.pairing f ∈ s₁) :
    ¬ ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂ := by
  intro hc
  refine hc₁ (fun f hf => ?_)
  have h := hc (Sum.inl f) (inl_mem_joinParts.mpr hf)
  exact inl_mem_joinParts.mp h

open Classical in
/-- **An unclosed half leaves the join unclosed**, on the right. -/
theorem not_closeJoin_closed_right {t : ℕ} {F G : Fragment (Fin t)}
    (s₁ : Finset F.Flag) (s₂ : Finset G.Flag)
    (hc₂ : ¬ ∀ f ∈ s₂, G.pairing f ∈ s₂) :
    ¬ ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂ := by
  intro hc
  refine hc₂ (fun f hf => ?_)
  have h := hc (Sum.inr f) (inr_mem_joinParts.mpr hf)
  exact inr_mem_joinParts.mp h

open Classical in
/-- **A non-Eulerian half leaves the join non-Eulerian.** -/
theorem not_eulerian_closeJoin {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (hbad : ¬ ((EdgeSubset.mk s₁ hc₁).Eulerian
      ∧ (EdgeSubset.mk s₂ hc₂).Eulerian)) :
    ¬ (EdgeSubset.mk (closeJoin s₁ s₂)
      (closeJoin_pairing_mem hc₁ hc₂)).Eulerian := by
  intro hE
  obtain ⟨hL, hR⟩ := (eulerian_iff_parts (closeJoin s₁ s₂)
    (closeJoin_pairing_mem hc₁ hc₂)
    (by
      rw [show leftPart (closeJoin s₁ s₂) = s₁ from
        leftPart_joinParts s₁ s₂]
      exact hc₁)
    (by
      rw [show rightPart (closeJoin s₁ s₂) = s₂ from
        rightPart_joinParts s₁ s₂]
      exact hc₂)).mp hE
  refine hbad ⟨?_, ?_⟩
  · refine (relabelUp_eulerian (finCongr (by omega : t = 0 + t))
      (EdgeSubset.mk s₁ hc₁ : EdgeSubset F)).mp ?_
    have hEq : (EdgeSubset.mk (leftPart (closeJoin s₁ s₂))
          (by
            rw [show leftPart (closeJoin s₁ s₂) = s₁ from
              leftPart_joinParts s₁ s₂]
            exact hc₁) :
          EdgeSubset (F.relabel (finCongr (by omega : t = 0 + t))))
        = EdgeSubset.relabelUp (finCongr (by omega : t = 0 + t))
          (EdgeSubset.mk s₁ hc₁ : EdgeSubset F) :=
      EdgeSubset.ext (leftPart_joinParts s₁ s₂)
    exact hEq ▸ hL
  · refine (relabelUp_eulerian (finCongr (by omega : t = t + 0))
      (EdgeSubset.mk s₂ hc₂ : EdgeSubset G)).mp ?_
    have hEq : (EdgeSubset.mk (rightPart (closeJoin s₁ s₂))
          (by
            rw [show rightPart (closeJoin s₁ s₂) = s₂ from
              rightPart_joinParts s₁ s₂]
            exact hc₂) :
          EdgeSubset (G.relabel (finCongr (by omega : t = t + 0))))
        = EdgeSubset.relabelUp (finCongr (by omega : t = t + 0))
          (EdgeSubset.mk s₂ hc₂ : EdgeSubset G) :=
      EdgeSubset.ext (rightPart_joinParts s₁ s₂)
    exact hEq ▸ hR

open Classical in
/-- **The base's summand vanishes off a matching subset.** -/
theorem base_term_eq_zero_of_not_matches {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t))
    (bits : Fin t → Bool)
    (s : Finset (closeBase F G).Flag) (C : ℕ)
    (hbad : ∀ x : GenBoundaryState k ℓ (Fin t),
      ¬ genBoundarySubsetMatches (closeBase F G) s (diagOf t x)) :
    (∑ x : GenBoundaryState k ℓ (Fin t),
        circuitWeight (liftData t (closeBase F G) bits
            (pairFamily h t F G))
            (imageOf t (closeBase F G) s)
          * edgeTermAt h (pairFamily h t F G) (diagOf t x) s C)
      = 0 :=
  Finset.sum_eq_zero (fun x _ => by
    rw [edgeTermAt_eq_zero_of_not_matches h
      (pairFamily h t F G) (diagOf t x) (hbad x) C]
    ring)

open Classical in
/-- **A mismatched join carries no diagonal state.** -/
theorem not_matches_of_used_ne {k ℓ : ℕ} {t : ℕ}
    {F G : Fragment (Fin t)} {s₁ : Finset F.Flag}
    {s₂ : Finset G.Flag} (i : Fin t)
    (hne : ¬ (F.boundaryFlag i ∈ s₁ ↔ G.boundaryFlag i ∈ s₂))
    (x : GenBoundaryState k ℓ (Fin t)) :
    ¬ genBoundarySubsetMatches (closeBase F G) (closeJoin s₁ s₂)
      (diagOf t x) := by
  intro hm
  obtain ⟨h₁, h₂⟩ := (matches_closeJoin_iff s₁ s₂ x).mp hm
  exact hne ((h₁ i).trans (h₂ i).symm)

open Classical in
/-- **A tensor term needs a closed subset.** -/
theorem pairTerm_eq_zero_of_not_closed_left {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t))
    (s₁ : Finset F.Flag) (s₂ : Finset G.Flag)
    (hc₁ : ¬ ∀ f ∈ s₁, F.pairing f ∈ s₁) :
    (∑ x : GenBoundaryState k ℓ (Fin t),
        ∑ y : GenBoundaryState k ℓ (Fin t),
          superForm t x y * tensorTermAt F h s₁ x
            * tensorTermAt G h s₂ y) = 0 :=
  Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun y _ => by
    rw [tensorTermAt_eq_zero_of_not_closed F h s₁ x hc₁]
    ring))

open Classical in
/-- **A tensor term needs a closed subset**, on the right. -/
theorem pairTerm_eq_zero_of_not_closed_right {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t))
    (s₁ : Finset F.Flag) (s₂ : Finset G.Flag)
    (hc₂ : ¬ ∀ f ∈ s₂, G.pairing f ∈ s₂) :
    (∑ x : GenBoundaryState k ℓ (Fin t),
        ∑ y : GenBoundaryState k ℓ (Fin t),
          superForm t x y * tensorTermAt F h s₁ x
            * tensorTermAt G h s₂ y) = 0 :=
  Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun y _ => by
    rw [tensorTermAt_eq_zero_of_not_closed G h s₂ y hc₂]
    ring))

open Classical in
/-- **A tensor term needs an Eulerian subset.** -/
theorem pairTerm_eq_zero_of_not_eulerian {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t))
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (hbad : ¬ ((EdgeSubset.mk s₁ hc₁).Eulerian
      ∧ (EdgeSubset.mk s₂ hc₂).Eulerian)) :
    (∑ x : GenBoundaryState k ℓ (Fin t),
        ∑ y : GenBoundaryState k ℓ (Fin t),
          superForm t x y * tensorTermAt F h s₁ x
            * tensorTermAt G h s₂ y) = 0 := by
  by_cases hE₁ : (EdgeSubset.mk s₁ hc₁).Eulerian
  · have hE₂ : ¬ (EdgeSubset.mk s₂ hc₂).Eulerian :=
      fun hx => hbad ⟨hE₁, hx⟩
    exact Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero
      (fun y _ => by
        rw [tensorTermAt_eq_zero_of_not_eulerian G h hc₂ y hE₂]
        ring))
  · exact Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero
      (fun y _ => by
        rw [tensorTermAt_eq_zero_of_not_eulerian F h hc₁ x hE₁]
        ring))

open Classical in
/-- **A tensor term needs canonical data.** -/
theorem pairTerm_eq_zero_of_not_canon {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t))
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (hE₁ : (EdgeSubset.mk s₁ hc₁).Eulerian)
    (hE₂ : (EdgeSubset.mk s₂ hc₂).Eulerian)
    (hbad : ¬ (Nonempty (EdgeSubset.mk s₁ hc₁).CanonData
      ∧ Nonempty (EdgeSubset.mk s₂ hc₂).CanonData)) :
    (∑ x : GenBoundaryState k ℓ (Fin t),
        ∑ y : GenBoundaryState k ℓ (Fin t),
          superForm t x y * tensorTermAt F h s₁ x
            * tensorTermAt G h s₂ y) = 0 := by
  by_cases hn₁ : Nonempty (EdgeSubset.mk s₁ hc₁).CanonData
  · have hn₂ : ¬ Nonempty (EdgeSubset.mk s₂ hc₂).CanonData :=
      fun hx => hbad ⟨hn₁, hx⟩
    exact Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero
      (fun y _ => by
        rw [tensorTermAt_eq_zero_of_not_canon G h hc₂ hE₂ y hn₂]
        ring))
  · exact Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero
      (fun y _ => by
        rw [tensorTermAt_eq_zero_of_not_canon F h hc₁ hE₁ x hn₁]
        ring))

open Classical in
/-- **The base's summand vanishes at an unguarded subset.** -/
theorem base_term_eq_zero_of_not_guarded {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t))
    (bits : Fin t → Bool)
    (s : Finset (closeBase F G).Flag) (C : ℕ)
    (hbad : ¬ ∃ (hc : ∀ f ∈ s, (closeBase F G).pairing f ∈ s),
      (EdgeSubset.mk s hc).Eulerian
        ∧ Nonempty (EdgeSubset.mk s hc).CanonData) :
    (∑ x : GenBoundaryState k ℓ (Fin t),
        circuitWeight (liftData t (closeBase F G) bits
            (pairFamily h t F G))
            (imageOf t (closeBase F G) s)
          * edgeTermAt h (pairFamily h t F G) (diagOf t x) s C)
      = 0 := by
  refine Finset.sum_eq_zero (fun x _ => ?_)
  by_cases hc : ∀ f ∈ s, (closeBase F G).pairing f ∈ s
  · by_cases hE : (EdgeSubset.mk s hc).Eulerian
    · have hne : ¬ Nonempty (EdgeSubset.mk s hc).CanonData :=
        fun hx => hbad ⟨hc, hE, hx⟩
      rw [edgeTermAt_eq_zero_of_not_canon h
        (pairFamily h t F G) (diagOf t x) hc hne C]
      ring
    · rw [edgeTermAt_eq_zero_of_not_eulerian h
        (pairFamily h t F G) (diagOf t x) hc hE C]
      ring
  · rw [edgeTermAt_eq_zero_of_not_closed h
      (pairFamily h t F G) (diagOf t x) hc C]
    ring

/-- **The pair sums regroup.**  Summing the pair terms over all
subsets of the two fragments is the superform pairing of the two
fragments' vectors. -/
theorem sum_pairs_regroup {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (t : ℕ) (F G : Fragment (Fin t)) :
    (∑ s₁ : Finset F.Flag, ∑ s₂ : Finset G.Flag,
        ∑ x : GenBoundaryState k ℓ (Fin t),
          ∑ y : GenBoundaryState k ℓ (Fin t),
            superForm t x y * tensorTermAt F h s₁ x
              * tensorTermAt G h s₂ y)
      = ∑ x : GenBoundaryState k ℓ (Fin t),
          ∑ y : GenBoundaryState k ℓ (Fin t),
            superForm t x y
              * (∑ s₁ : Finset F.Flag, tensorTermAt F h s₁ x)
              * (∑ s₂ : Finset G.Flag, tensorTermAt G h s₂ y) := by
  have step : ∀ s₁ : Finset F.Flag,
      (∑ s₂ : Finset G.Flag, ∑ x : GenBoundaryState k ℓ (Fin t),
          ∑ y : GenBoundaryState k ℓ (Fin t),
            superForm t x y * tensorTermAt F h s₁ x
              * tensorTermAt G h s₂ y)
        = ∑ x : GenBoundaryState k ℓ (Fin t),
            ∑ s₂ : Finset G.Flag,
              ∑ y : GenBoundaryState k ℓ (Fin t),
                superForm t x y * tensorTermAt F h s₁ x
                  * tensorTermAt G h s₂ y := fun _ => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun s₁ _ => step s₁), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have step2 : ∀ s₁ : Finset F.Flag,
      (∑ s₂ : Finset G.Flag, ∑ y : GenBoundaryState k ℓ (Fin t),
          superForm t x y * tensorTermAt F h s₁ x
            * tensorTermAt G h s₂ y)
        = ∑ y : GenBoundaryState k ℓ (Fin t),
            ∑ s₂ : Finset G.Flag,
              superForm t x y * tensorTermAt F h s₁ x
                * tensorTermAt G h s₂ y := fun _ => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun s₁ _ => step2 s₁), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  refine Eq.trans (Finset.sum_congr rfl
    (fun s₁ _ => (Finset.mul_sum _ _ _).symm)) ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]

open Classical in
/-- **The glue keeps a balanced subset Eulerian.**  At each stage the
drop has the lift's degrees, and the final relabel changes
nothing. -/
theorem eulerian_glueData : ∀ (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))),
    ∀ (D : StageData n V),
    CutBalanced V D.sub.flags →
    (EdgeSubset.mk D.sub.flags D.sub.pairing_mem).Eulerian →
    (EdgeSubset.mk (glueData n V D).sub.flags
      (glueData n V D).sub.pairing_mem).Eulerian
  | 0, _, D, _, hE => (relabelUp_eulerian endEquiv D.sub).mpr hE
  | n + 1, V, D, hbal, hE => by
    by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
        = V.boundaryFlag (cutR n)
    · have hct := dropSubset_pairing_closed_of_closed hcl
        D.sub.flags D.sub.pairing_mem
      have hcL := liftSubsetClosed_pairing_closed hcl _
        (decide (V.boundaryFlag (cutL n) ∈ D.sub.flags)) hct
      have hlift : liftSubsetClosed
          (V.dropSubset (cutL n) (cutR n) D.sub.flags)
          (decide (V.boundaryFlag (cutL n) ∈ D.sub.flags))
          = D.sub.flags :=
        liftSubsetClosed_dropSubset (cutL_ne_cutR n) hcl
          D.sub.flags D.sub.pairing_mem
      have hEl : (EdgeSubset.mk (liftSubsetClosed
          (V.dropSubset (cutL n) (cutR n) D.sub.flags)
          (decide (V.boundaryFlag (cutL n) ∈ D.sub.flags))) hcL :
          EdgeSubset V).Eulerian := by
        rw [show (EdgeSubset.mk (liftSubsetClosed
            (V.dropSubset (cutL n) (cutR n) D.sub.flags)
            (decide (V.boundaryFlag (cutL n) ∈ D.sub.flags))) hcL :
            EdgeSubset V)
          = EdgeSubset.mk D.sub.flags D.sub.pairing_mem from
            EdgeSubset.ext hlift]
        exact hE
      have hdrop := (eulerian_liftClosed_iff' hcl _
        (V.dropSubset (cutL n) (cutR n) D.sub.flags) hct hcL).mp hEl
      refine eulerian_glueData n (stepFragment n V)
        (stepData n V D)
        (cutBalanced_stepData_closed n V hcl D hbal) ?_
      have hstage := flagsOfEq_eulerian (gluePair_eq_closed n V hcl)
        (V.dropSubset (cutL n) (cutR n) D.sub.flags) hct hdrop
      have hgoal : (EdgeSubset.mk (flagsOfEq
            (V.gluePairClosed (cutL n) (cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_closed n V hcl)
            (V.dropSubset (cutL n) (cutR n) D.sub.flags))
          (flagsOfEq_pairing_mem (gluePair_eq_closed n V hcl) _
            hct) :
          EdgeSubset (stepFragment n V)).Eulerian :=
        (relabelUp_eulerian (interfaceStepEquiv 0 n 0) _).mpr hstage
      have hsub : (EdgeSubset.mk (stepData n V D).sub.flags
            (stepData n V D).sub.pairing_mem :
            EdgeSubset (stepFragment n V))
          = (EdgeSubset.mk (flagsOfEq
              (V.gluePairClosed (cutL n) (cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_closed n V hcl)
              (V.dropSubset (cutL n) (cutR n) D.sub.flags))
            (flagsOfEq_pairing_mem (gluePair_eq_closed n V hcl) _
              hct) :
            EdgeSubset (stepFragment n V)) :=
        EdgeSubset.ext (stepData_sub_flags_closed n V D hcl)
      rw [hsub]
      exact hgoal
    · have hct := dropSubset_rewire_closed (hopen := hcl)
        D.sub.flags
        (agreeingSubset_of_cutBalanced D.sub.pairing_mem hbal)
      have hcL := liftSubsetOpen_pairing_closed (cutL_ne_cutR n) hcl
        _ hct
      have hlift : liftSubsetOpen hcl
          (V.dropSubset (cutL n) (cutR n) D.sub.flags)
          = D.sub.flags :=
        liftSubsetOpen_dropSubset (cutL_ne_cutR n) hcl D.sub.flags
          D.sub.pairing_mem
      have hEl : (EdgeSubset.mk (liftSubsetOpen hcl
          (V.dropSubset (cutL n) (cutR n) D.sub.flags)) hcL :
          EdgeSubset V).Eulerian := by
        rw [show (EdgeSubset.mk (liftSubsetOpen hcl
            (V.dropSubset (cutL n) (cutR n) D.sub.flags)) hcL :
            EdgeSubset V)
          = EdgeSubset.mk D.sub.flags D.sub.pairing_mem from
            EdgeSubset.ext hlift]
        exact hE
      have hdrop := (eulerian_lift_open_iff (cutL_ne_cutR n) hcl
        (V.dropSubset (cutL n) (cutR n) D.sub.flags) hct hcL).mp hEl
      refine eulerian_glueData n (stepFragment n V)
        (stepData n V D)
        (cutBalanced_stepData n V hcl D hbal) ?_
      have hstage := flagsOfEq_eulerian (gluePair_eq_open n V hcl)
        (V.dropSubset (cutL n) (cutR n) D.sub.flags) hct hdrop
      have hgoal : (EdgeSubset.mk (flagsOfEq
            (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_open n V hcl)
            (V.dropSubset (cutL n) (cutR n) D.sub.flags))
          (flagsOfEq_pairing_mem (gluePair_eq_open n V hcl) _ hct) :
          EdgeSubset (stepFragment n V)).Eulerian :=
        (relabelUp_eulerian (interfaceStepEquiv 0 n 0) _).mpr hstage
      have hsub : (EdgeSubset.mk (stepData n V D).sub.flags
            (stepData n V D).sub.pairing_mem :
            EdgeSubset (stepFragment n V))
          = (EdgeSubset.mk (flagsOfEq
              (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
                hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_open n V hcl)
              (V.dropSubset (cutL n) (cutR n) D.sub.flags))
            (flagsOfEq_pairing_mem (gluePair_eq_open n V hcl) _
              hct) :
            EdgeSubset (stepFragment n V)) :=
        EdgeSubset.ext (stepData_sub_flags_open n V D hcl)
      rw [hsub]
      exact hgoal

open Classical in
/-- **The glue keeps a balanced subset's canonical data.** -/
theorem canonData_glueData : ∀ (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))),
    ∀ (D : StageData n V),
    CutBalanced V D.sub.flags →
    Nonempty (EdgeSubset.mk D.sub.flags
      D.sub.pairing_mem).CanonData →
    Nonempty (EdgeSubset.mk (glueData n V D).sub.flags
      (glueData n V D).sub.pairing_mem).CanonData
  | 0, _, D, _, hE => by
    refine (EdgeSubset.nonempty_canonData_relabelUp
      ⟨endEquiv, fun {a b} => ?_⟩ D.sub).mpr hE
    exact a.elim (fun x => x.elim0) (fun x => x.elim0)
  -- ═══════ ONE CUT AT A TIME ═══════
  -- The recursion glues the top interface pair and hands the rest
  -- to the stage below; the cut closes or it does not.
  | n + 1, V, D, hbal, hE => by
    by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
        = V.boundaryFlag (cutR n)
    · have hct := dropSubset_pairing_closed_of_closed hcl
        D.sub.flags D.sub.pairing_mem
      have hcL := liftSubsetClosed_pairing_closed hcl _
        (decide (V.boundaryFlag (cutL n) ∈ D.sub.flags)) hct
      have hlift : liftSubsetClosed
          (V.dropSubset (cutL n) (cutR n) D.sub.flags)
          (decide (V.boundaryFlag (cutL n) ∈ D.sub.flags))
          = D.sub.flags :=
        liftSubsetClosed_dropSubset (cutL_ne_cutR n) hcl
          D.sub.flags D.sub.pairing_mem
      have hEl : Nonempty (EdgeSubset.mk (liftSubsetClosed
          (V.dropSubset (cutL n) (cutR n) D.sub.flags)
          (decide (V.boundaryFlag (cutL n) ∈ D.sub.flags))) hcL :
          EdgeSubset V).CanonData := by
        rw [show (EdgeSubset.mk (liftSubsetClosed
            (V.dropSubset (cutL n) (cutR n) D.sub.flags)
            (decide (V.boundaryFlag (cutL n) ∈ D.sub.flags))) hcL :
            EdgeSubset V)
          = EdgeSubset.mk D.sub.flags D.sub.pairing_mem from
            EdgeSubset.ext hlift]
        exact hE
      have hdrop := nonempty_canonData_glueClosed hcl
        (V.dropSubset (cutL n) (cutR n) D.sub.flags) hct _ hcL hEl
      refine canonData_glueData n (stepFragment n V)
        (stepData n V D)
        (cutBalanced_stepData_closed n V hcl D hbal) ?_
      have hstage := flagsOfEq_canon (gluePair_eq_closed n V hcl)
        (V.dropSubset (cutL n) (cutR n) D.sub.flags) hct hdrop
      have hgoal : Nonempty (EdgeSubset.mk (flagsOfEq
            (V.gluePairClosed (cutL n) (cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_closed n V hcl)
            (V.dropSubset (cutL n) (cutR n) D.sub.flags))
          (flagsOfEq_pairing_mem (gluePair_eq_closed n V hcl) _
            hct) :
          EdgeSubset (stepFragment n V)).CanonData :=
        (EdgeSubset.nonempty_canonData_relabelUp (stepIso n) _).mpr
          hstage
      have hsub : (EdgeSubset.mk (stepData n V D).sub.flags
            (stepData n V D).sub.pairing_mem :
            EdgeSubset (stepFragment n V))
          = (EdgeSubset.mk (flagsOfEq
              (V.gluePairClosed (cutL n) (cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_closed n V hcl)
              (V.dropSubset (cutL n) (cutR n) D.sub.flags))
            (flagsOfEq_pairing_mem (gluePair_eq_closed n V hcl) _
              hct) :
            EdgeSubset (stepFragment n V)) :=
        EdgeSubset.ext (stepData_sub_flags_closed n V D hcl)
      rw [hsub]
      exact hgoal
    · have hct := dropSubset_rewire_closed (hopen := hcl)
        D.sub.flags
        (agreeingSubset_of_cutBalanced D.sub.pairing_mem hbal)
      have hcL := liftSubsetOpen_pairing_closed (cutL_ne_cutR n) hcl
        _ hct
      have hlift : liftSubsetOpen hcl
          (V.dropSubset (cutL n) (cutR n) D.sub.flags)
          = D.sub.flags :=
        liftSubsetOpen_dropSubset (cutL_ne_cutR n) hcl D.sub.flags
          D.sub.pairing_mem
      have hEl : Nonempty (EdgeSubset.mk
          (liftSubsetOpen hcl
          (V.dropSubset (cutL n) (cutR n) D.sub.flags)) hcL :
          EdgeSubset V).CanonData := by
        rw [show (EdgeSubset.mk (liftSubsetOpen hcl
            (V.dropSubset (cutL n) (cutR n) D.sub.flags)) hcL :
            EdgeSubset V)
          = EdgeSubset.mk D.sub.flags D.sub.pairing_mem from
            EdgeSubset.ext hlift]
        exact hE
      have hdrop := nonempty_canonData_glueOpen (cutL_ne_cutR n) hcl
        (V.dropSubset (cutL n) (cutR n) D.sub.flags) hct hcL hEl
      refine canonData_glueData n (stepFragment n V)
        (stepData n V D)
        (cutBalanced_stepData n V hcl D hbal) ?_
      have hstage := flagsOfEq_canon (gluePair_eq_open n V hcl)
        (V.dropSubset (cutL n) (cutR n) D.sub.flags) hct hdrop
      have hgoal : Nonempty (EdgeSubset.mk (flagsOfEq
            (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_open n V hcl)
            (V.dropSubset (cutL n) (cutR n) D.sub.flags))
          (flagsOfEq_pairing_mem (gluePair_eq_open n V hcl) _ hct) :
          EdgeSubset (stepFragment n V)).CanonData :=
        (EdgeSubset.nonempty_canonData_relabelUp (stepIso n) _).mpr
          hstage
      have hsub : (EdgeSubset.mk (stepData n V D).sub.flags
            (stepData n V D).sub.pairing_mem :
            EdgeSubset (stepFragment n V))
          = (EdgeSubset.mk (flagsOfEq
              (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
                hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_open n V hcl)
              (V.dropSubset (cutL n) (cutR n) D.sub.flags))
            (flagsOfEq_pairing_mem (gluePair_eq_open n V hcl) _
              hct) :
            EdgeSubset (stepFragment n V)) :=
        EdgeSubset.ext (stepData_sub_flags_open n V D hcl)
      rw [hsub]
      exact hgoal

/-- At a good pair of subsets the composition's own term is the
pair's term: RS21's (13) and (14) at one subset of the base. -/
theorem base_term_eq_pairTerm_bitsOf {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (t : ℕ) (F G : Fragment (Fin t))
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (hE₁ : (EdgeSubset.mk s₁ hc₁).Eulerian)
    (hn₁ : Nonempty (EdgeSubset.mk s₁ hc₁).CanonData)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (hE₂ : (EdgeSubset.mk s₂ hc₂).Eulerian)
    (hn₂ : Nonempty (EdgeSubset.mk s₂ hc₂).CanonData)
    (hused : ∀ i : Fin t,
      F.boundaryFlag i ∈ s₁ ↔ G.boundaryFlag i ∈ s₂)
    (hb : ∀ i : Fin t,
      F.boundaryFlag i ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
        ↔ G.boundaryFlag i ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags)
    (hEJ : (EdgeSubset.mk (closeJoin s₁ s₂)
      (closeJoin_pairing_mem hc₁ hc₂)).Eulerian)
    (hneJ : Nonempty (EdgeSubset.mk (closeJoin s₁ s₂)
      (closeJoin_pairing_mem hc₁ hc₂)).CanonData) :
    (∑ x : GenBoundaryState k ℓ (Fin t),
        ∑ y : GenBoundaryState k ℓ (Fin t),
          superForm t x y * tensorTermAt F h s₁ x
            * tensorTermAt G h s₂ y)
      = ∑ x : GenBoundaryState k ℓ (Fin t),
          circuitWeight (liftData t (closeBase F G)
              (bitsOf t (closeBase F G) (closeJoin s₁ s₂))
              (pairFamily h t F G))
              (imageOf t (closeBase F G) (closeJoin s₁ s₂))
            * edgeTermAt h (pairFamily h t F G) (diagOf t x)
              (closeJoin s₁ s₂)
              (carried t (closeBase F G) (closeJoin s₁ s₂)) := by
  have hal : Aligned t (closeBase F G)
      (bitsOf t (closeBase F G) (closeJoin s₁ s₂))
      (pairFamily h t F G) :=
    aligned_of_baseDirections t (closeBase F G) _ _
      (baseDirections_pairFamily h t F G)
  have hcompat : ∀ hc hE hne,
      (pairFamily h t F G (pairStage hc₁ hc₂ hused
          (Classical.choice hn₁).1
          (Classical.choice hn₂).1).sub.flags hc hE hne).1.MatchEq
        (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
          (Classical.choice hn₂).1).rel := by
    intro hc' hE' hne'
    exact pairFamily_matchEq h t F G _ hc' hE' hne' s₁ hc₁ hE₁
      hn₁ s₂ hc₂ hE₂ hn₂ hused hb rfl
  have hEg := eulerian_glueData t (closeBase F G)
    (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
      (Classical.choice hn₂).1) (cutBalanced_closeJoin hused) hEJ
  have hneg := canonData_glueData t (closeBase F G)
    (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
      (Classical.choice hn₂).1) (cutBalanced_closeJoin hused) hneJ
  have hw := circuitWeight_liftData_imageOf_bitsOf t (closeBase F G)
    (pairFamily h t F G)
    (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
      (Classical.choice hn₂).1) hal hcompat
    (cutBalanced_closeJoin hused) hEg hneg
  have hw' : circuitWeight (liftData t (closeBase F G)
        (bitsOf t (closeBase F G) (closeJoin s₁ s₂))
        (pairFamily h t F G))
        (imageOf t (closeBase F G) (closeJoin s₁ s₂))
      = (-1 : ℂ) ^ (glueData t (closeBase F G)
        (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
          (Classical.choice hn₂).1)).rel.openCircuitCount := hw
  have hcar : carried t (closeBase F G) (closeJoin s₁ s₂)
      = glueCount t (closeBase F G)
        (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
          (Classical.choice hn₂).1) :=
    carried_eq_glueCount t (closeBase F G)
      (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
        (Classical.choice hn₂).1)
  rw [pairFamily_value h t F G (closeJoin s₁ s₂)
      (closeJoin_pairing_mem hc₁ hc₂) hEJ hneJ s₁ hc₁ hE₁ hn₁ s₂ hc₂
      hE₂ hn₂ hused hb rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [hw', hcar, edgeTermAt_eq_edgeTermOf h (pairFamily h t F G)
    (diagOf t x) (closeJoin_pairing_mem hc₁ hc₂) hEJ hneJ _]

/-- Summed over all boundary states, the form-weighted product of
the two fragments' terms is the composition's base sum — the
identity the converse runs on. -/
theorem base_term_eq_pairTerm_all_bitsOf {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t))
    (s₁ : Finset F.Flag) (s₂ : Finset G.Flag) :
    (∑ x : GenBoundaryState k ℓ (Fin t),
        ∑ y : GenBoundaryState k ℓ (Fin t),
          superForm t x y * tensorTermAt F h s₁ x
            * tensorTermAt G h s₂ y)
      = ∑ x : GenBoundaryState k ℓ (Fin t),
          circuitWeight (liftData t (closeBase F G)
              (bitsOf t (closeBase F G) (closeJoin s₁ s₂))
              (pairFamily h t F G))
              (imageOf t (closeBase F G) (closeJoin s₁ s₂))
            * edgeTermAt h (pairFamily h t F G) (diagOf t x)
              (closeJoin s₁ s₂)
              (carried t (closeBase F G) (closeJoin s₁ s₂)) := by
  by_cases hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁
  · by_cases hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂
    · by_cases hused : ∀ i : Fin t,
          F.boundaryFlag i ∈ s₁ ↔ G.boundaryFlag i ∈ s₂
      · have hb : ∀ i : Fin t,
            F.boundaryFlag i ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
              ↔ G.boundaryFlag i
                ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags := by
          intro i
          constructor
          · intro hx
            exact boundaryFlag_mem_boundaryFlags
              (F := EdgeSubset.mk s₂ hc₂) (a := i)
              ((hused i).mp (mem_flags_of_boundaryFlags _ hx))
          · intro hx
            exact boundaryFlag_mem_boundaryFlags
              (F := EdgeSubset.mk s₁ hc₁) (a := i)
              ((hused i).mpr (mem_flags_of_boundaryFlags _ hx))
        by_cases hE : (EdgeSubset.mk s₁ hc₁).Eulerian
            ∧ (EdgeSubset.mk s₂ hc₂).Eulerian
        · by_cases hn : Nonempty (EdgeSubset.mk s₁ hc₁).CanonData
              ∧ Nonempty (EdgeSubset.mk s₂ hc₂).CanonData
          · exact base_term_eq_pairTerm_bitsOf h t F G hc₁ hE.1
              hn.1 hc₂ hE.2 hn.2 hused hb
              (eulerian_closeJoin hc₁ hc₂ hE.1 hE.2)
              (canonData_closeJoin hc₁ hc₂ hused hn.1 hn.2)
          · have hbad : ¬ ∃ (hc : ∀ f ∈ closeJoin s₁ s₂,
                (closeBase F G).pairing f ∈ closeJoin s₁ s₂),
                (EdgeSubset.mk (closeJoin s₁ s₂) hc).Eulerian
                  ∧ Nonempty (EdgeSubset.mk (closeJoin s₁ s₂)
                    hc).CanonData := by
              rintro ⟨hcj, -, hnej⟩
              refine hn ⟨?_, ?_⟩
              · exact (nonempty_canonData_iff_system _).mpr
                  ⟨pairRelLeftDown hcj hc₁ (Classical.choice hnej).1⟩
              · exact (nonempty_canonData_iff_system _).mpr
                  ⟨pairRelRightDown hcj hc₂
                    (Classical.choice hnej).1⟩
            rw [pairTerm_eq_zero_of_not_canon h t F G hc₁ hc₂ hE.1
                hE.2 hn,
              base_term_eq_zero_of_not_guarded h t F G _ _ _
                hbad]
        · have hbad : ¬ ∃ (hc : ∀ f ∈ closeJoin s₁ s₂,
              (closeBase F G).pairing f ∈ closeJoin s₁ s₂),
              (EdgeSubset.mk (closeJoin s₁ s₂) hc).Eulerian
                ∧ Nonempty (EdgeSubset.mk (closeJoin s₁ s₂)
                  hc).CanonData := by
            rintro ⟨hcj, hEj, -⟩
            exact not_eulerian_closeJoin hc₁ hc₂ hE hEj
          rw [pairTerm_eq_zero_of_not_eulerian h t F G hc₁ hc₂ hE,
            base_term_eq_zero_of_not_guarded h t F G _ _ _
              hbad]
      · obtain ⟨i, hi⟩ := not_forall.mp hused
        rw [base_term_eq_zero_of_not_matches h t F G _ _ _
          (not_matches_of_used_ne i hi)]
        by_cases hL : F.boundaryFlag i ∈ s₁
        · exact pairTerm_eq_zero_of_used_ne h t F G s₁ s₂ i hL
            (fun hx => hi ⟨fun _ => hx, fun _ => hL⟩)
        · have hR : G.boundaryFlag i ∈ s₂ := by
            by_contra hx
            exact hi ⟨fun hy => absurd hy hL, fun hy => absurd hy hx⟩
          refine Eq.trans Finset.sum_comm (Finset.sum_eq_zero
            (fun y _ => Finset.sum_eq_zero (fun x _ => ?_)))
          by_cases hy : genBoundarySubsetMatches G s₂ y
          · by_cases hx : genBoundarySubsetMatches F s₁ x
            · obtain ⟨c, hcy⟩ := (hy i).mp hR
              obtain ⟨a, hax⟩ := exists_left_of_not_right
                (fun hr => hL ((hx i).mpr hr))
              rw [superForm_eq_zero_of_left_right x y i hax hcy]
              ring
            · rw [tensorTermAt_eq_zero_of_not_matches F h s₁ x hx]
              ring
          · rw [tensorTermAt_eq_zero_of_not_matches G h s₂ y hy]
            ring
    · have hbad : ¬ ∃ (hc : ∀ f ∈ closeJoin s₁ s₂,
          (closeBase F G).pairing f ∈ closeJoin s₁ s₂),
          (EdgeSubset.mk (closeJoin s₁ s₂) hc).Eulerian
            ∧ Nonempty (EdgeSubset.mk (closeJoin s₁ s₂)
              hc).CanonData := by
        rintro ⟨hcj, -, -⟩
        exact not_closeJoin_closed_right s₁ s₂ hc₂ hcj
      rw [pairTerm_eq_zero_of_not_closed_right h t F G s₁ s₂ hc₂,
        base_term_eq_zero_of_not_guarded h t F G _ _ _ hbad]
  · have hbad : ¬ ∃ (hc : ∀ f ∈ closeJoin s₁ s₂,
        (closeBase F G).pairing f ∈ closeJoin s₁ s₂),
        (EdgeSubset.mk (closeJoin s₁ s₂) hc).Eulerian
          ∧ Nonempty (EdgeSubset.mk (closeJoin s₁ s₂)
            hc).CanonData := by
      rintro ⟨hcj, -, -⟩
      exact not_closeJoin_closed_left s₁ s₂ hc₁ hcj
    rw [pairTerm_eq_zero_of_not_closed_left h t F G s₁ s₂ hc₁,
      base_term_eq_zero_of_not_guarded h t F G _ _ _ hbad]

open Classical in
/-- **The composition's base sum is the superform pairing, at every
interface.**  Summing each base subset's term — read with the bits
that subset itself determines — over all subsets gives RS21's pairing
of the two fragments' tensors. -/
theorem base_sum_eq_superForm_pairing_bitsOf {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t)) :
    (∑ s : Finset (closeBase F G).Flag,
        ∑ x : GenBoundaryState k ℓ (Fin t),
          circuitWeight (liftData t (closeBase F G)
              (bitsOf t (closeBase F G) s) (pairFamily h t F G))
              (imageOf t (closeBase F G) s)
            * edgeTermAt h (pairFamily h t F G) (diagOf t x) s
              (carried t (closeBase F G) s))
      = ∑ x : GenBoundaryState k ℓ (Fin t),
          ∑ y : GenBoundaryState k ℓ (Fin t),
            superForm t x y
              * (∑ s₁ : Finset F.Flag, tensorTermAt F h s₁ x)
              * (∑ s₂ : Finset G.Flag, tensorTermAt G h s₂ y) := by
  rw [sum_subsets_disjUnion (W₁ := F.relabel
      (finCongr (by omega : t = 0 + t)))
    (W₂ := G.relabel (finCongr (by omega : t = t + 0)))
    (fun s => ∑ x : GenBoundaryState k ℓ (Fin t),
      circuitWeight (liftData t (closeBase F G)
          (bitsOf t (closeBase F G) s) (pairFamily h t F G))
          (imageOf t (closeBase F G) s)
        * edgeTermAt h (pairFamily h t F G) (diagOf t x) s
          (carried t (closeBase F G) s))]
  refine Eq.trans (Finset.sum_congr rfl (fun s₁ _ =>
    Finset.sum_congr rfl (fun s₂ _ =>
      (base_term_eq_pairTerm_all_bitsOf h t F G s₁ s₂).symm))) ?_
  exact sum_pairs_regroup h t F G

end EdgeSubset

end RS
