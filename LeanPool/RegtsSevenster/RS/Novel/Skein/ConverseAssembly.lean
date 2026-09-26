/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.RSTensor
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ClosedIdentify
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ClosedTopSum

/-!
# The closure of two fragments, read on the base

The connection pairing evaluates the mixed partition function at
`pairClose F G`, which is the interface glue of the two fragments'
disjoint union, relabelled to the empty label type.  Composing the
closed identification with the colouring recursion writes that value
as the base's summands, summed over its subsets and over the
interface colours.
-/

@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment
/-- The lexicographic order on the interface's label type. -/
@[reducible] local instance assemblyBaseOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

/-- The same order one stage up. -/
@[reducible] local instance assemblyOrderSucc (n : ℕ) :
    LinearOrder (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) :=
  sumLexLinearOrder _ _

/-- The order a stage's surviving labels carry. -/
@[reducible] local instance assemblySurvOrder (n : ℕ) :
    LinearOrder (SurvivingLabel
      (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) (cutL n) (cutR n)) :=
  sumLexSubtypeLinearOrder _ _ _

/-- The order the composition's own label type carries. -/
@[reducible] local instance assemblyTopOrder :
    LinearOrder (Fin 0 ⊕ Fin 0) :=
  sumLexLinearOrder _ _

/-- The two fragments, moved onto the interface's label type. -/
noncomputable abbrev closeBase {t : ℕ} (F G : Fragment (Fin t)) :
    Fragment (Fin (0 + t) ⊕ Fin (t + 0)) :=
  (F.relabel (finCongr (by omega : t = 0 + t))).disjUnion
    (G.relabel (finCongr (by omega : t = t + 0)))

/-- The closure is the interface glue, relabelled. -/
theorem pairClose_eq {t : ℕ} (F G : Fragment (Fin t)) :
    pairClose F G
      = (glueInterface 0 t 0 (closeBase F G)).relabel
        finSumFinEquiv := rfl

open Classical in
/-- **The closure's value is the interface glue's constrained
value.** -/
theorem mixedPartition_pairClose {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (t : ℕ) (F G : Fragment (Fin t)) :
    mixedPartition h (pairClose F G)
      = throughMixedPartitionC h
        (glueInterface 0 t 0 (closeBase F G)) emptyState := by
  exact mixedPartition_relabel_closed_of_eq
    (glueInterface 0 t 0 (closeBase F G)) finSumFinEquiv
    (pairClose_eq F G) h emptyState

/-! ## The tensor side, split over subsets

The closing display of RS21's Theorem 6 sums the identity (13)
over the Eulerian subsets of the two fragments.  Splitting the
fragment tensors into their per-subset terms and exchanging the
four sums puts the pairing in that form.
-/

open Classical in
/-- A fragment tensor's term at one subset. -/
noncomputable def tensorTermAt {α : Type} [LinearOrder α]
    [Fintype α] (V : Fragment α) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (s : Finset V.Flag) (x : GenBoundaryState k ℓ α) : ℂ :=
  if hc : ∀ f ∈ s, V.pairing f ∈ s then
    if _hE : (EdgeSubset.mk s hc).Eulerian then
      if hne : Nonempty (EdgeSubset.mk s hc).CanonData then
        (EdgeSubset.mk s hc).tFull h (Classical.choice hne).1
          (Classical.choice hne).2.val x
      else 0
    else 0
  else 0

open Classical in
/-- The fragment tensor is the sum of its terms. -/
theorem tensorSum_eq_sum {α : Type} [LinearOrder α] [Fintype α]
    (V : Fragment α)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (x : GenBoundaryState k ℓ α) :
    tensorSum V h x = ∑ s : Finset V.Flag, tensorTermAt V h s x :=
  rfl

open Classical in
/-- A tensor term at a good subset is the normalised tensor. -/
theorem tensorTermAt_pos {α : Type} [LinearOrder α] [Fintype α]
    (V : Fragment α) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    {s : Finset V.Flag} (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData)
    (x : GenBoundaryState k ℓ α) :
    tensorTermAt V h s x
      = (EdgeSubset.mk s hc).tFull h (Classical.choice hne).1
        (Classical.choice hne).2.val x := by
  unfold tensorTermAt
  rw [dite_eq_left hc, dite_eq_left hE, dite_eq_left hne]

open Classical in
/-- **The pair term when the two subsets use the same labels.**  This
is RS21's (13), read on the two fragment tensors' per-subset terms:
the pairing is the two circuit-and-matching signs times the colouring
sum of the two subsets' agreement. -/
theorem exists_sum_sum_superForm_tensorTermAt {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t))
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (hE₁ : (EdgeSubset.mk s₁ hc₁).Eulerian)
    (hn₁ : Nonempty (EdgeSubset.mk s₁ hc₁).CanonData)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (hE₂ : (EdgeSubset.mk s₂ hc₂).Eulerian)
    (hn₂ : Nonempty (EdgeSubset.mk s₂ hc₂).CanonData)
    (_hused : ∀ i : Fin t,
      F.boundaryFlag i ∈ s₁ ↔ G.boundaryFlag i ∈ s₂)
    (hb : ∀ i : Fin t,
      F.boundaryFlag i ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
        ↔ G.boundaryFlag i ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags) :
    ∃ (o₁' : (Classical.choice hn₁).1.Orientation)
      (o₂' : (Classical.choice hn₂).1.Orientation)
      (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
      (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂))),
      (∀ a : UsedLab (EdgeSubset.mk s₁ hc₁), (M₁.edge a).val
        = chordInv (EdgeSubset.mk s₁ hc₁)
          (Classical.choice hn₁).1 a.val) ∧
      (∀ b : UsedLab (EdgeSubset.mk s₂ hc₂), (M₂.edge b).val
        = chordInv (EdgeSubset.mk s₂ hc₂)
          (Classical.choice hn₂).1 b.val) ∧
      (∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
        M₂.tail (usedLabInterfaceEquiv (EdgeSubset.mk s₁ hc₁)
            (EdgeSubset.mk s₂ hc₂) hb a)
          = !M₁.tail a) ∧
      (∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
        ¬ IsThroughLabel (EdgeSubset.mk s₁ hc₁) a.val →
        M₁.tail a = (cutMatching (EdgeSubset.mk s₁ hc₁)
          (Classical.choice hn₁).1 o₁').tail a) ∧
      (∀ b : UsedLab (EdgeSubset.mk s₂ hc₂),
        ¬ IsThroughLabel (EdgeSubset.mk s₂ hc₂) b.val →
        M₂.tail b = (cutMatching (EdgeSubset.mk s₂ hc₂)
          (Classical.choice hn₂).1 o₂').tail b) ∧
      (∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
        ¬ IsThroughLabel (EdgeSubset.mk s₁ hc₁) a.val →
        ¬ IsThroughLabel (EdgeSubset.mk s₂ hc₂)
          (usedLabInterfaceEquiv (EdgeSubset.mk s₁ hc₁)
            (EdgeSubset.mk s₂ hc₂) hb a).val →
        (cutMatching (EdgeSubset.mk s₂ hc₂)
              (Classical.choice hn₂).1 o₂').tail
            (usedLabInterfaceEquiv (EdgeSubset.mk s₁ hc₁)
              (EdgeSubset.mk s₂ hc₂) hb a)
          = !(cutMatching (EdgeSubset.mk s₁ hc₁)
              (Classical.choice hn₁).1 o₁').tail a) ∧
      (∑ x : GenBoundaryState k ℓ (Fin t),
          ∑ y : GenBoundaryState k ℓ (Fin t),
            superForm t x y * tensorTermAt F h s₁ x
              * tensorTermAt G h s₂ y)
        = (((DirMatching.sgnRel (DirMatching.stdMatching
                  (card_usedLab_eq (EdgeSubset.mk s₁ hc₁) M₁)) M₁
                : ℤ) : ℂ)
              * ((-1 : ℂ) ^ (Classical.choice hn₁).1.openCircuitCount)
            * (((DirMatching.sgnRel (DirMatching.stdMatching
                  (card_usedLab_eq (EdgeSubset.mk s₂ hc₂) M₂)) M₂
                : ℤ) : ℂ)
              * ((-1 : ℂ) ^
                (Classical.choice hn₂).1.openCircuitCount)))
          * ∑ st : GenBoundaryState k ℓ (Fin t),
              pairAgreeValue (EdgeSubset.mk s₁ hc₁)
                (EdgeSubset.mk s₂ hc₂) h o₁' o₂' st := by
  have hcard : Fintype.card (UsedLab (EdgeSubset.mk s₂ hc₂))
      = Fintype.card (UsedLab (EdgeSubset.mk s₁ hc₁)) :=
    Fintype.card_congr
      (usedLabInterfaceEquiv (EdgeSubset.mk s₁ hc₁)
        (EdgeSubset.mk s₂ hc₂) hb).symm
  obtain ⟨o₁', o₂', M₁, M₂, hM₁, hM₂, halt, hag₁, hag₂, halt',
    hval⟩ :=
    exists_sum_sum_superForm_tFull (EdgeSubset.mk s₁ hc₁)
      (EdgeSubset.mk s₂ hc₂) h (Classical.choice hn₁).1
      (Classical.choice hn₁).2.val (Classical.choice hn₂).1
      (Classical.choice hn₂).2.val
      (Fintype.card (UsedLab (EdgeSubset.mk s₁ hc₁)) / 2)
      (card_usedLab_eq _ (cutMatching (EdgeSubset.mk s₁ hc₁) _
        (Classical.choice hn₁).2.val))
      (by
        rw [hcard]
        exact card_usedLab_eq _ (cutMatching (EdgeSubset.mk s₁ hc₁) _
          (Classical.choice hn₁).2.val))
      hb
  refine ⟨o₁', o₂', M₁, M₂, hM₁, hM₂, halt, hag₁, hag₂, halt',
    ?_⟩
  simp only [tensorTermAt_pos F h hc₁ hE₁ hn₁,
    tensorTermAt_pos G h hc₂ hE₂ hn₂]
  exact hval

/-! ## The diagonal state on the two sides

The interface colours enter the base as one state on the disjoint
union.  Restricting it to either summand and pulling back along that
fragment's relabel gives the colours themselves, which is the form
`relabel_edgeSum` and `edgeSum_disjUnion` consume.
-/

/-- The diagonal state, restricted to the left fragment. -/
theorem diagOf_inl_relabel {k ℓ : ℕ} (t : ℕ)
    (x : GenBoundaryState k ℓ (Fin t)) :
    (fun a : Fin t => diagOf t x
        (Sum.inl (finCongr (by omega : t = 0 + t) a))) = x :=
  funext fun a => congrArg x (Fin.ext (by simp))

/-- The diagonal state, restricted to the right fragment. -/
theorem diagOf_inr_relabel {k ℓ : ℕ} (t : ℕ)
    (x : GenBoundaryState k ℓ (Fin t)) :
    (fun b : Fin t => diagOf t x
        (Sum.inr (finCongr (by omega : t = t + 0) b))) = x :=
  funext fun b => congrArg x (Fin.ext (by simp))

/-! ## The base's colouring sum, split into the two fragments'

The base is the two fragments' disjoint union, so its colouring sum
factors; each factor then comes down to its own fragment along that
fragment's relabel.
-/

open Classical in
/-- **The base's colouring sum factors.** -/
theorem edgeSum_closeBase {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (t : ℕ) (F G : Fragment (Fin t))
    (B : EdgeSubset (closeBase F G))
    (st : GenBoundaryState k ℓ (Fin (0 + t) ⊕ Fin (t + 0)))
    (hbnd : genBoundarySubsetMatches (closeBase F G) B.flags st)
    (hbnd₁ : genBoundarySubsetMatches
      (F.relabel (finCongr (by omega : t = 0 + t)))
      (leftSub B).flags (fun a => st (Sum.inl a)))
    (hbnd₂ : genBoundarySubsetMatches
      (G.relabel (finCongr (by omega : t = t + 0)))
      (rightSub B).flags (fun b => st (Sum.inr b)))
    {κ₁ : (leftSub B).RelTransitionSystem}
    {κ₂ : (rightSub B).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation) :
    B.edgeSum h st hbnd (prodOrient o₁ o₂)
      = (leftSub B).edgeSum h (fun a => st (Sum.inl a)) hbnd₁ o₁
        * (rightSub B).edgeSum h (fun b => st (Sum.inr b)) hbnd₂
          o₂ :=
  edgeSum_disjUnion B h st hbnd hbnd₁ hbnd₂ o₁ o₂

open Classical in
/-- **A half's colouring sum comes down to its own fragment.** -/
theorem edgeSum_relabelDown {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    {t n : ℕ} (F : Fragment (Fin t)) (he : t = n)
    (A : EdgeSubset (F.relabel (finCongr he)))
    (st : GenBoundaryState k ℓ (Fin n))
    (st' : GenBoundaryState k ℓ (Fin t))
    (hst : (fun a => st (finCongr he a)) = st')
    (hbnd : genBoundarySubsetMatches (F.relabel (finCongr he))
      A.flags st)
    (hbnd' : genBoundarySubsetMatches F
      (EdgeSubset.relabelDown (finCongr he) A).flags st')
    {κ : (EdgeSubset.relabelDown (finCongr he) A).RelTransitionSystem}
    (o : κ.Orientation) :
    A.edgeSum h st hbnd
        (relabelOrientUp (finCongr he)
          (EdgeSubset.relabelDown (finCongr he) A) o)
      = (EdgeSubset.relabelDown (finCongr he) A).edgeSum h st' hbnd'
        o := by
  subst hst
  exact relabel_edgeSum (finCongr he)
    (EdgeSubset.relabelDown (finCongr he) A) h st hbnd hbnd' o

open Classical in
/-- **The base's colouring sum is the pair's agreement value.**  This
is the composition's side of RS21's (13): the base subset's colouring
sum at a diagonal state is exactly the object the pairing identity
produces. -/
theorem edgeSum_closeBase_eq_pairAgreeValue {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t))
    (x : GenBoundaryState k ℓ (Fin t))
    (B : EdgeSubset (closeBase F G))
    (hbnd : genBoundarySubsetMatches (closeBase F G) B.flags
      (diagOf t x))
    (hbnd₁ : genBoundarySubsetMatches F (leftSub B).flags x)
    (hbnd₂ : genBoundarySubsetMatches G (rightSub B).flags x)
    {κ₁ : (EdgeSubset.relabelDown
      (finCongr (by omega : t = 0 + t))
      (leftSub B)).RelTransitionSystem}
    {κ₂ : (EdgeSubset.relabelDown
      (finCongr (by omega : t = t + 0))
      (rightSub B)).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation) :
    B.edgeSum h (diagOf t x) hbnd
        (prodOrient
          (relabelOrientUp (finCongr (by omega : t = 0 + t))
            (EdgeSubset.relabelDown _ (leftSub B)) o₁)
          (relabelOrientUp (finCongr (by omega : t = t + 0))
            (EdgeSubset.relabelDown _ (rightSub B)) o₂))
      = pairAgreeValue
        (EdgeSubset.relabelDown (finCongr (by omega : t = 0 + t))
          (leftSub B))
        (EdgeSubset.relabelDown (finCongr (by omega : t = t + 0))
          (rightSub B)) h o₁ o₂ x := by
  have hb₁ : genBoundarySubsetMatches
      (F.relabel (finCongr (by omega : t = 0 + t)))
      (leftSub B).flags (fun a => diagOf t x (Sum.inl a)) := by
    refine (relabel_genBoundarySubsetMatches_iff
      (finCongr (by omega : t = 0 + t)) (leftSub B).flags
      (fun a => diagOf t x (Sum.inl a))).mpr ?_
    show genBoundarySubsetMatches F (leftSub B).flags
      (fun a => diagOf t x
        (Sum.inl (finCongr (by omega : t = 0 + t) a)))
    rw [diagOf_inl_relabel]
    exact hbnd₁
  have hb₂ : genBoundarySubsetMatches
      (G.relabel (finCongr (by omega : t = t + 0)))
      (rightSub B).flags (fun b => diagOf t x (Sum.inr b)) := by
    refine (relabel_genBoundarySubsetMatches_iff
      (finCongr (by omega : t = t + 0)) (rightSub B).flags
      (fun b => diagOf t x (Sum.inr b))).mpr ?_
    change genBoundarySubsetMatches G (rightSub B).flags
      (fun b => diagOf t x
        (Sum.inr (finCongr (by omega : t = t + 0) b)))
    rw [diagOf_inr_relabel]
    exact hbnd₂
  refine Eq.trans (edgeSum_closeBase h t F G B (diagOf t x) hbnd hb₁
    hb₂ _ _) ?_
  refine Eq.trans (congrArg₂ (· * ·)
    (edgeSum_relabelDown h F (by omega : t = 0 + t) (leftSub B) _ x
      (diagOf_inl_relabel t x) hb₁ hbnd₁ o₁)
    (edgeSum_relabelDown h G (by omega : t = t + 0) (rightSub B) _ x
      (diagOf_inr_relabel t x) hb₂ hbnd₂ o₂)) ?_
  exact (pairAgreeValue_eq_edgeSum _ _ h o₁ o₂ x hbnd₁ hbnd₂).symm

/-! ## Transports of a subset along a relabel

The colouring recursion and the ledger recursion carry their subsets
along equalities of fragments taken at different points: one before
the stage's relabel, one after.  The two agree.
-/

/-- **A transport commutes with a relabel.** -/
theorem flagsOfEq_relabel {L L' : Type} {V₁ V₂ : Fragment L}
    (hV : V₁ = V₂) (e : L ≃ L') (t : Finset V₁.Flag) :
    flagsOfEq (V₁.relabel e) (V₂.relabel e)
        (congrArg (fun X => Fragment.relabel X e) hV) t
      = flagsOfEq V₁ V₂ hV t := by
  subst hV
  rfl

open Classical in
/-- The transported stage data's subset. -/
theorem stageDataOfEq_sub_flags {m : ℕ}
    {V₁ V₂ : Fragment (Fin (0 + m) ⊕ Fin (m + 0))} (hV : V₁ = V₂)
    (Dm : StageData m V₁) :
    (stageDataOfEq hV Dm).sub.flags
      = flagsOfEq V₁ V₂ hV Dm.sub.flags := by
  subst hV
  rfl

open Classical in
/-- **The ledger's step drops the subset**, at a closing cut. -/
theorem stepData_sub_flags_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (D : StageData (n + 1) V)
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) :
    (stepData n V D).sub.flags
      = flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_closed n V hcl)
        (V.dropSubset (cutL n) (cutR n) D.sub.flags) := by
  refine Eq.trans (congrArg (fun X => X.sub.flags)
    (show stepData n V D = _ from dite_eq_left hcl)) ?_
  refine Eq.trans (stageDataOfEq_sub_flags _ _) ?_
  exact flagsOfEq_relabel (gluePair_eq_closed n V hcl)
    (interfaceStepEquiv 0 n 0) _

open Classical in
/-- **The ledger's step drops the subset**, at an open cut. -/
theorem stepData_sub_flags_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (D : StageData (n + 1) V)
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) :
    (stepData n V D).sub.flags
      = flagsOfEq
        (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_open n V hop)
        (V.dropSubset (cutL n) (cutR n) D.sub.flags) := by
  refine Eq.trans (congrArg (fun X => X.sub.flags)
    (show stepData n V D = _ from dite_eq_right hop)) ?_
  refine Eq.trans (stageDataOfEq_sub_flags _ _) ?_
  exact flagsOfEq_relabel (gluePair_eq_open n V hop)
    (interfaceStepEquiv 0 n 0) _

open Classical in
/-- **The colouring side's carried count is the ledger's.**  Both
count the closing cuts whose own edge the subset carries. -/
theorem carried_eq_glueCount : ∀ (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) (D : StageData n V),
    carried n V D.sub.flags = glueCount n V D
  | 0, _, _ => rfl
  | n + 1, V, D => by
    have hstep := carried_eq_glueCount n (stepFragment n V)
      (stepData n V D)
    by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
        = V.boundaryFlag (cutR n)
    · rw [stepData_sub_flags_closed n V D hcl] at hstep
      simp only [carried, glueCount, dite_eq_left hcl, stepBit]
      by_cases hm : V.boundaryFlag (cutL n) ∈ D.sub.flags
      · have hb : V.pairing (V.boundaryFlag (cutL n))
              = V.boundaryFlag (cutR n)
            ∧ decide (V.boundaryFlag (cutL n) ∈ D.sub.flags)
              = true := ⟨hcl, by simpa using hm⟩
        rw [ite_eq_left hm]
        exact congrArg₂ (· + ·) (ite_eq_left hb).symm hstep
      · have hb : ¬ (V.pairing (V.boundaryFlag (cutL n))
              = V.boundaryFlag (cutR n)
            ∧ decide (V.boundaryFlag (cutL n) ∈ D.sub.flags)
              = true) := fun hx => hm (by simpa using hx.2)
        rw [ite_eq_right hm]
        exact congrArg₂ (· + ·) (ite_eq_right hb).symm hstep
    · rw [stepData_sub_flags_open n V D hcl] at hstep
      simp only [carried, glueCount, dite_eq_right hcl, stepBit]
      have hb : ¬ (V.pairing (V.boundaryFlag (cutL n))
            = V.boundaryFlag (cutR n)
          ∧ decide (V.boundaryFlag (cutL n) ∈ D.sub.flags)
            = true) := fun hx => hcl hx.1
      exact Eq.trans hstep (Eq.trans (zero_add _).symm
        (congrArg₂ (· + ·) (ite_eq_right hb).symm rfl))

open Classical in
/-- **The colouring side's image subset is the ledger's.**  Both are
the iterated drop of the base subset. -/
theorem imageOf_eq_glueData_sub : ∀ (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) (D : StageData n V),
    imageOf n V D.sub.flags = (glueData n V D).sub.flags
  | 0, _, _ => rfl
  | n + 1, V, D => by
    by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
        = V.boundaryFlag (cutR n)
    · rw [imageOf_succ_closed n V hcl D.sub.flags,
        ← stepData_sub_flags_closed n V D hcl]
      exact imageOf_eq_glueData_sub n (stepFragment n V)
        (stepData n V D)
    · rw [imageOf_succ_open n V hcl D.sub.flags,
        ← stepData_sub_flags_open n V D hcl]
      exact imageOf_eq_glueData_sub n (stepFragment n V)
        (stepData n V D)

/-! ## The base's subsets, split into the two fragments'

A subset of a disjoint union is a pair of subsets, so the sum over
the base's subsets is the double sum the tensor side carries.
-/

section Parts

variable {α β : Type} {W₁ : Fragment α} {W₂ : Fragment β}

open Classical in
/-- **A subset of a disjoint union is a pair of subsets.** -/
noncomputable def partsEquiv (W₁ : Fragment α) (W₂ : Fragment β) :
    Finset ((W₁.disjUnion W₂).Flag)
      ≃ Finset W₁.Flag × Finset W₂.Flag where
  toFun s := (leftPart s, rightPart s)
  invFun p := joinParts p.1 p.2
  left_inv s := joinParts_parts s
  right_inv p := Prod.ext (leftPart_joinParts p.1 p.2)
    (rightPart_joinParts p.1 p.2)

open Classical in
/-- **The sum over the base's subsets is the double sum.** -/
theorem sum_subsets_disjUnion {M : Type} [AddCommMonoid M]
    (f : Finset ((W₁.disjUnion W₂).Flag) → M) :
    (∑ s : Finset ((W₁.disjUnion W₂).Flag), f s)
      = ∑ s₁ : Finset W₁.Flag, ∑ s₂ : Finset W₂.Flag,
          f (joinParts s₁ s₂) := by
  refine Eq.trans (Fintype.sum_equiv (partsEquiv W₁ W₂) _
    (fun p : Finset W₁.Flag × Finset W₂.Flag =>
      f (joinParts p.1 p.2))
    (fun s => congrArg f (joinParts_parts s).symm)) ?_
  exact Fintype.sum_prod_type _

end Parts

/-- The base subset a pair of subsets makes. -/
noncomputable abbrev closeJoin {t : ℕ} {F G : Fragment (Fin t)}
    (s₁ : Finset F.Flag) (s₂ : Finset G.Flag) :
    Finset (closeBase F G).Flag :=
  joinParts (W₁ := F.relabel (finCongr (by omega : t = 0 + t)))
    (W₂ := G.relabel (finCongr (by omega : t = t + 0))) s₁ s₂

open Classical in
/-- **The base subset is interface-paired** exactly when the two
fragments' subsets use the same labels.  This is (14)'s hypothesis,
read on the pair. -/
theorem swapPaired_joinParts (t : ℕ) (F G : Fragment (Fin t))
    (s₁ : Finset F.Flag) (s₂ : Finset G.Flag)
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hused : ∀ i : Fin t,
      F.boundaryFlag i ∈ s₁ ↔ G.boundaryFlag i ∈ s₂) :
    SwapPaired (EdgeSubset.mk (closeJoin s₁ s₂) hc)
      (interfaceSwap (stepIdent t)) := by
  refine (swapPaired_iff_interfacePaired
    (EdgeSubset.mk (closeJoin s₁ s₂) hc) (stepIdent t)).mpr ?_
  intro a
  have hidx : (finCongr (by omega : t = t + 0)).symm (stepIdent t a)
      = (finCongr (by omega : t = 0 + t)).symm a :=
    Fin.ext (by simp [stepIdent])
  constructor
  · intro hx
    refine boundaryFlag_mem_boundaryFlags ?_
    refine inr_mem_joinParts.mpr ?_
    change G.boundaryFlag ((finCongr (by omega : t = t + 0)).symm
      (stepIdent t a)) ∈ s₂
    rw [hidx]
    exact (hused _).mp (inl_mem_joinParts.mp
      (mem_flags_of_boundaryFlags _ hx))
  · intro hx
    refine boundaryFlag_mem_boundaryFlags ?_
    refine inl_mem_joinParts.mpr ?_
    change F.boundaryFlag ((finCongr (by omega : t = 0 + t)).symm a)
      ∈ s₁
    refine (hused _).mpr ?_
    rw [← hidx]
    exact inr_mem_joinParts.mp (mem_flags_of_boundaryFlags _ hx)

open Classical in
/-- The base subset a pair makes is closed under the pairing. -/
theorem closeJoin_pairing_mem {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂) :
    ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂ := by
  refine (pairing_closed_iff_parts (closeJoin s₁ s₂)).mpr ⟨?_, ?_⟩
  · rw [show leftPart (closeJoin s₁ s₂) = s₁
      from leftPart_joinParts s₁ s₂]
    exact hc₁
  · rw [show rightPart (closeJoin s₁ s₂) = s₂
      from rightPart_joinParts s₁ s₂]
    exact hc₂

open Classical in
/-- **The base subset's left half is the first subset.** -/
theorem leftSub_closeJoin {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₁ : ∀ f ∈ s₁,
      (F.relabel (finCongr (by omega : t = 0 + t))).pairing f
        ∈ s₁) :
    leftSub (EdgeSubset.mk (closeJoin s₁ s₂) hc)
      = (EdgeSubset.mk s₁ hc₁ : EdgeSubset
        (F.relabel (finCongr (by omega : t = 0 + t)))) :=
  EdgeSubset.ext (leftPart_joinParts
    (W₁ := F.relabel (finCongr (by omega : t = 0 + t)))
    (W₂ := G.relabel (finCongr (by omega : t = t + 0))) s₁ s₂)

open Classical in
/-- **The base subset's right half is the second subset.** -/
theorem rightSub_closeJoin {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₂ : ∀ f ∈ s₂,
      (G.relabel (finCongr (by omega : t = t + 0))).pairing f
        ∈ s₂) :
    rightSub (EdgeSubset.mk (closeJoin s₁ s₂) hc)
      = (EdgeSubset.mk s₂ hc₂ : EdgeSubset
        (G.relabel (finCongr (by omega : t = t + 0)))) :=
  EdgeSubset.ext (rightPart_joinParts
    (W₁ := F.relabel (finCongr (by omega : t = 0 + t)))
    (W₂ := G.relabel (finCongr (by omega : t = t + 0))) s₁ s₂)

/-! ## The matchings under a relabel

RS21's (13) produces its matchings on the fragments' own subsets;
(14) asks for them on the halves of the base subset, which live one
relabel away.  The used labels correspond (`usedLabRelabelEquiv`) and
the chord matching shifts with them (`cutMatching_relabelUp_edge`);
what is left is the sign.
-/

open Classical in
/-- **A matching's sign survives a transport.**  The two fragments'
matchings may therefore be read on the base subset's halves, where
(14) wants them. -/
theorem sgnRel_stdMatching_map {α β : Type} [LinearOrder α]
    [Fintype α] [LinearOrder β] [Fintype β] (e : α ≃o β) {m : ℕ}
    (h : Fintype.card α = 2 * m) (h' : Fintype.card β = 2 * m)
    (M : DirMatching α) :
    DirMatching.sgnRel (DirMatching.stdMatching h')
        (M.map e.toEquiv)
      = DirMatching.sgnRel (DirMatching.stdMatching h) M := by
  rw [← DirMatching.stdMatching_map e h h',
    DirMatching.sgnRel_map e.toEquiv (DirMatching.stdMatching h) M]

open Classical in
/-- **The interface identification acts by the interface map.**  It
is therefore the same identification `exists_eulerianPosition` uses,
read on the two halves. -/
theorem interfaceSideDisjEquiv_val {γ δ : Type}
    {W₁ : Fragment γ} {W₂ : Fragment δ}
    (F : EdgeSubset (W₁.disjUnion W₂)) (e : γ ≃ δ)
    (hp : InterfacePaired F e) (a : UsedLab (leftSub F)) :
    (interfaceSideDisjEquiv F e hp a).val = e a.val := rfl

/-! ## The pair's transition data, read on the base

(14) asks for the two systems on the halves of the base subset.  The
fragments' own systems get there by the relabel and the half
identification, and neither move changes the open circuit count.
-/

open Classical in
/-- The first fragment's system, read on the base subset's left
half. -/
noncomputable def pairRelLeft {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc₁ : ∀ f ∈ s₁,
      (F.relabel (finCongr (by omega : t = 0 + t))).pairing f ∈ s₁)
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (κ₁ : (EdgeSubset.mk s₁ hc₁ : EdgeSubset
      (F.relabel (finCongr (by omega : t = 0 + t)))).RelTransitionSystem) :
    (leftSub (EdgeSubset.mk (closeJoin s₁ s₂) hc)
      ).RelTransitionSystem :=
  relOfEq (leftSub_closeJoin hc hc₁).symm κ₁

open Classical in
/-- The second fragment's system, read on the base subset's right
half. -/
noncomputable def pairRelRight {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc₂ : ∀ f ∈ s₂,
      (G.relabel (finCongr (by omega : t = t + 0))).pairing f ∈ s₂)
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (κ₂ : (EdgeSubset.mk s₂ hc₂ : EdgeSubset
      (G.relabel (finCongr (by omega : t = t + 0)))).RelTransitionSystem) :
    (rightSub (EdgeSubset.mk (closeJoin s₁ s₂) hc)
      ).RelTransitionSystem :=
  relOfEq (rightSub_closeJoin hc hc₂).symm κ₂

open Classical in
/-- Reading the first system on the half leaves its circuit count
alone. -/
theorem openCircuitCount_pairRelLeft {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc₁ : ∀ f ∈ s₁,
      (F.relabel (finCongr (by omega : t = 0 + t))).pairing f ∈ s₁)
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (κ₁ : (EdgeSubset.mk s₁ hc₁ : EdgeSubset
      (F.relabel (finCongr (by omega : t = 0 + t)))).RelTransitionSystem) :
    (pairRelLeft (s₂ := s₂) hc₁ hc κ₁).openCircuitCount
      = κ₁.openCircuitCount :=
  openCircuitCount_relOfEq _ κ₁

open Classical in
/-- Reading the second system on the half leaves its circuit count
alone. -/
theorem openCircuitCount_pairRelRight {t : ℕ}
    {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc₂ : ∀ f ∈ s₂,
      (G.relabel (finCongr (by omega : t = t + 0))).pairing f ∈ s₂)
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (κ₂ : (EdgeSubset.mk s₂ hc₂ : EdgeSubset
      (G.relabel (finCongr (by omega : t = t + 0)))).RelTransitionSystem) :
    (pairRelRight (s₁ := s₁) hc₂ hc κ₂).openCircuitCount
      = κ₂.openCircuitCount :=
  openCircuitCount_relOfEq _ κ₂

open Classical in
/-- **A matching with the chord pairings is the chord matching**, on
pairings.  RS21's (13) records its matchings pointwise; (14) wants
them as an equality of pairing maps. -/
theorem edge_eq_cutMatching {α : Type} [LinearOrder α]
    {W : Fragment α} (F : EdgeSubset W) (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (M : DirMatching (UsedLab F))
    (hM : ∀ a : UsedLab F,
      (M.edge a).val = chordInv F κ a.val) :
    M.edge = (cutMatching F κ o).edge :=
  funext fun a => Subtype.ext (hM a)

open Classical in
/-- **The used labels are untouched by an equality of subsets**, as
an order isomorphism — the form the sign transport wants. -/
def usedLabOrderIsoOfEq {α : Type} [LinearOrder α] {W : Fragment α}
    {F₁ F₂ : EdgeSubset W} (h : F₁ = F₂) : UsedLab F₁ ≃o UsedLab F₂
    := by
  subst h
  exact OrderIso.refl _

open Classical in
/-- **The used labels shift through a relabel**, as an order
isomorphism. -/
noncomputable def usedLabRelabelOrderIso {α β : Type}
    [LinearOrder α] [LinearOrder β] {W : Fragment α} (e : α ≃o β)
    (F : EdgeSubset W) :
    UsedLab (F.relabelUp e.toEquiv) ≃o UsedLab F where
  toEquiv := usedLabRelabelEquiv e F
  map_rel_iff' := e.symm.map_rel_iff

/-- The left relabel, as an order isomorphism. -/
def leftIso (t : ℕ) : Fin t ≃o Fin (0 + t) :=
  Fin.castOrderIso (by omega)

/-- The right relabel, as an order isomorphism. -/
def rightIso (t : ℕ) : Fin t ≃o Fin (t + 0) :=
  Fin.castOrderIso (by omega)

open Classical in
/-- **The base subset's left half has the first subset's used
labels.** -/
noncomputable def usedLabLeftCloseJoin {t : ℕ}
    {F G : Fragment (Fin t)} {s₁ : Finset F.Flag}
    {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁) :
    UsedLab (leftSub (EdgeSubset.mk (closeJoin s₁ s₂) hc))
      ≃o UsedLab (EdgeSubset.mk s₁ hc₁) :=
  (usedLabOrderIsoOfEq (leftSub_closeJoin hc hc₁)).trans
    (usedLabRelabelOrderIso (leftIso t) (EdgeSubset.mk s₁ hc₁))

open Classical in
/-- **The base subset's right half has the second subset's used
labels.** -/
noncomputable def usedLabRightCloseJoin {t : ℕ}
    {F G : Fragment (Fin t)} {s₁ : Finset F.Flag}
    {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂) :
    UsedLab (rightSub (EdgeSubset.mk (closeJoin s₁ s₂) hc))
      ≃o UsedLab (EdgeSubset.mk s₂ hc₂) :=
  (usedLabOrderIsoOfEq (rightSub_closeJoin hc hc₂)).trans
    (usedLabRelabelOrderIso (rightIso t) (EdgeSubset.mk s₂ hc₂))

open Classical in
/-- The base subset's left half has as many used labels as the first
subset. -/
theorem card_usedLab_leftSub_closeJoin {t : ℕ}
    {F G : Fragment (Fin t)} {s₁ : Finset F.Flag}
    {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁) :
    Fintype.card
        (UsedLab (leftSub (EdgeSubset.mk (closeJoin s₁ s₂) hc)))
      = Fintype.card (UsedLab (EdgeSubset.mk s₁ hc₁)) :=
  Fintype.card_congr (usedLabLeftCloseJoin hc hc₁).toEquiv

open Classical in
/-- The base subset's right half has as many used labels as the
second subset. -/
theorem card_usedLab_rightSub_closeJoin {t : ℕ}
    {F G : Fragment (Fin t)} {s₁ : Finset F.Flag}
    {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂) :
    Fintype.card
        (UsedLab (rightSub (EdgeSubset.mk (closeJoin s₁ s₂) hc)))
      = Fintype.card (UsedLab (EdgeSubset.mk s₂ hc₂)) :=
  Fintype.card_congr (usedLabRightCloseJoin hc hc₂).toEquiv

open Classical in
/-- **The chord involution on the base subset's left half** is the
first subset's, shifted by the relabel. -/
theorem chordInv_pairRelLeft {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (κ₁ : (EdgeSubset.mk s₁ hc₁).RelTransitionSystem)
    (a : Fin (0 + t)) :
    chordInv (leftSub (EdgeSubset.mk (closeJoin s₁ s₂) hc))
        (pairRelLeft hc₁ hc
          (relabelTransUp (leftIso t).toEquiv
            (EdgeSubset.mk s₁ hc₁) κ₁)) a
      = leftIso t (chordInv (EdgeSubset.mk s₁ hc₁) κ₁
          ((leftIso t).symm a)) :=
  Eq.trans (chordInv_relOfEq _ _ a)
    (chordInv_relabelUp (leftIso t) (EdgeSubset.mk s₁ hc₁) κ₁ a)

open Classical in
/-- **The chord involution on the base subset's right half** is the
second subset's, shifted by the relabel. -/
theorem chordInv_pairRelRight {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (κ₂ : (EdgeSubset.mk s₂ hc₂).RelTransitionSystem)
    (b : Fin (t + 0)) :
    chordInv (rightSub (EdgeSubset.mk (closeJoin s₁ s₂) hc))
        (pairRelRight hc₂ hc
          (relabelTransUp (rightIso t).toEquiv
            (EdgeSubset.mk s₂ hc₂) κ₂)) b
      = rightIso t (chordInv (EdgeSubset.mk s₂ hc₂) κ₂
          ((rightIso t).symm b)) :=
  Eq.trans (chordInv_relOfEq _ _ b)
    (chordInv_relabelUp (rightIso t) (EdgeSubset.mk s₂ hc₂) κ₂ b)

open Classical in
/-- The subset-equality transport keeps the label. -/
theorem usedLabOrderIsoOfEq_val {α : Type} [LinearOrder α]
    {W : Fragment α} {F₁ F₂ : EdgeSubset W} (h : F₁ = F₂)
    (x : UsedLab F₁) : (usedLabOrderIsoOfEq h x).val = x.val := by
  subst h
  rfl

open Classical in
/-- The left transport acts by the relabel on labels. -/
theorem usedLabLeftCloseJoin_val {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (a : UsedLab (leftSub (EdgeSubset.mk (closeJoin s₁ s₂) hc))) :
    (usedLabLeftCloseJoin hc hc₁ a).val
      = (leftIso t).symm a.val := by
  change (leftIso t).symm
      (usedLabOrderIsoOfEq (leftSub_closeJoin hc hc₁) a).val = _
  rw [usedLabOrderIsoOfEq_val]

open Classical in
/-- The right transport acts by the relabel on labels. -/
theorem usedLabRightCloseJoin_val {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (b : UsedLab (rightSub (EdgeSubset.mk (closeJoin s₁ s₂) hc))) :
    (usedLabRightCloseJoin hc hc₂ b).val
      = (rightIso t).symm b.val := by
  change (rightIso t).symm
      (usedLabOrderIsoOfEq (rightSub_closeJoin hc hc₂) b).val = _
  rw [usedLabOrderIsoOfEq_val]

open Classical in
/-- The left transport's inverse acts by the relabel. -/
theorem usedLabLeftCloseJoin_symm_val {t : ℕ}
    {F G : Fragment (Fin t)} {s₁ : Finset F.Flag}
    {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (x : UsedLab (EdgeSubset.mk s₁ hc₁)) :
    ((usedLabLeftCloseJoin (s₂ := s₂) hc hc₁).symm x).val
      = leftIso t x.val := by
  have h := usedLabLeftCloseJoin_val (s₂ := s₂) hc hc₁
    ((usedLabLeftCloseJoin (s₂ := s₂) hc hc₁).symm x)
  rw [OrderIso.apply_symm_apply] at h
  rw [h, OrderIso.apply_symm_apply]

open Classical in
/-- The right transport's inverse acts by the relabel. -/
theorem usedLabRightCloseJoin_symm_val {t : ℕ}
    {F G : Fragment (Fin t)} {s₁ : Finset F.Flag}
    {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (x : UsedLab (EdgeSubset.mk s₂ hc₂)) :
    ((usedLabRightCloseJoin (s₁ := s₁) hc hc₂).symm x).val
      = rightIso t x.val := by
  have h := usedLabRightCloseJoin_val (s₁ := s₁) hc hc₂
    ((usedLabRightCloseJoin (s₁ := s₁) hc hc₂).symm x)
  rw [OrderIso.apply_symm_apply] at h
  rw [h, OrderIso.apply_symm_apply]

open Classical in
/-- **The transported matching keeps the chord record**, on the base
subset's left half. -/
theorem edge_val_map_left {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (κ₁ : (EdgeSubset.mk s₁ hc₁).RelTransitionSystem)
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (hM₁ : ∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
      (M₁.edge a).val = chordInv (EdgeSubset.mk s₁ hc₁) κ₁ a.val)
    (a : UsedLab (leftSub (EdgeSubset.mk (closeJoin s₁ s₂) hc))) :
    ((M₁.map
        (usedLabLeftCloseJoin (s₂ := s₂) hc hc₁).symm.toEquiv).edge
        a).val
      = chordInv (leftSub (EdgeSubset.mk (closeJoin s₁ s₂) hc))
        (pairRelLeft hc₁ hc (relabelTransUp (leftIso t).toEquiv
          (EdgeSubset.mk s₁ hc₁) κ₁)) a.val := by
  change ((usedLabLeftCloseJoin (s₂ := s₂) hc hc₁).symm
      (M₁.edge (usedLabLeftCloseJoin (s₂ := s₂) hc hc₁ a))).val = _
  rw [usedLabLeftCloseJoin_symm_val, hM₁,
    usedLabLeftCloseJoin_val, chordInv_pairRelLeft]

open Classical in
/-- **The transported matching keeps the chord record**, on the base
subset's right half. -/
theorem edge_val_map_right {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (κ₂ : (EdgeSubset.mk s₂ hc₂).RelTransitionSystem)
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂)))
    (hM₂ : ∀ b : UsedLab (EdgeSubset.mk s₂ hc₂),
      (M₂.edge b).val = chordInv (EdgeSubset.mk s₂ hc₂) κ₂ b.val)
    (b : UsedLab (rightSub (EdgeSubset.mk (closeJoin s₁ s₂) hc))) :
    ((M₂.map
        (usedLabRightCloseJoin (s₁ := s₁) hc hc₂).symm.toEquiv).edge
        b).val
      = chordInv (rightSub (EdgeSubset.mk (closeJoin s₁ s₂) hc))
        (pairRelRight hc₂ hc (relabelTransUp (rightIso t).toEquiv
          (EdgeSubset.mk s₂ hc₂) κ₂)) b.val := by
  change ((usedLabRightCloseJoin (s₁ := s₁) hc hc₂).symm
      (M₂.edge (usedLabRightCloseJoin (s₁ := s₁) hc hc₂ b))).val = _
  rw [usedLabRightCloseJoin_symm_val, hM₂,
    usedLabRightCloseJoin_val, chordInv_pairRelRight]

open Classical in
/-- **The two interface identifications agree.**  (14) states its
alternation against the base subset's halves, (13) against the two
fragments' own subsets; the transports carry one to the other. -/
theorem usedLabRight_interfaceSideDisj {t : ℕ}
    {F G : Fragment (Fin t)} {s₁ : Finset F.Flag}
    {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (hp : InterfacePaired (EdgeSubset.mk (closeJoin s₁ s₂) hc)
      (stepIdentOrderIso t).toEquiv)
    (hb : ∀ i : Fin t,
      F.boundaryFlag i ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
        ↔ G.boundaryFlag i ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags)
    (a : UsedLab (leftSub (EdgeSubset.mk (closeJoin s₁ s₂) hc))) :
    usedLabRightCloseJoin (s₁ := s₁) hc hc₂
        (interfaceSideDisjOrderIso (EdgeSubset.mk (closeJoin s₁ s₂)
          hc) (stepIdentOrderIso t) hp a)
      = usedLabInterfaceEquiv (EdgeSubset.mk s₁ hc₁)
        (EdgeSubset.mk s₂ hc₂) hb
        (usedLabLeftCloseJoin (s₂ := s₂) hc hc₁ a) := by
  refine Subtype.ext ?_
  rw [usedLabRightCloseJoin_val]
  change (rightIso t).symm
      ((interfaceSideDisjEquiv (EdgeSubset.mk (closeJoin s₁ s₂) hc)
        (stepIdentOrderIso t).toEquiv hp a).val)
    = ((usedLabLeftCloseJoin (s₂ := s₂) hc hc₁) a).val
  rw [interfaceSideDisjEquiv_val, usedLabLeftCloseJoin_val]
  exact Fin.ext (by simp [leftIso, rightIso, stepIdentOrderIso])

/-! ## The stage data a pair of subsets makes

Everything (14) reads off the composition is a function of this one
object: the base subset, its interface pairing, and the two systems
carried over from the fragments.
-/

open Classical in
/-- **The stage data a pair of subsets makes.** -/
noncomputable def pairStage {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (hused : ∀ i : Fin t,
      F.boundaryFlag i ∈ s₁ ↔ G.boundaryFlag i ∈ s₂)
    (κ₁ : (EdgeSubset.mk s₁ hc₁).RelTransitionSystem)
    (κ₂ : (EdgeSubset.mk s₂ hc₂).RelTransitionSystem) :
    StageData t (closeBase F G) where
  sub := EdgeSubset.mk (closeJoin s₁ s₂)
    (closeJoin_pairing_mem hc₁ hc₂)
  paired := swapPaired_joinParts t F G s₁ s₂
    (closeJoin_pairing_mem hc₁ hc₂) hused
  rel := prodRel
    (pairRelLeft hc₁ (closeJoin_pairing_mem hc₁ hc₂)
      (relabelTransUp (leftIso t).toEquiv
        (EdgeSubset.mk s₁ hc₁) κ₁))
    (pairRelRight hc₂ (closeJoin_pairing_mem hc₁ hc₂)
      (relabelTransUp (rightIso t).toEquiv
        (EdgeSubset.mk s₂ hc₂) κ₂))

open Classical in
/-- **RS21's (14), read on a pair of subsets.**  The two fragments'
circuit-and-matching signs multiply to the composition's own sign,
with one extra factor for each closing cut the subsets carry. -/
theorem sign_composition_pair {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (hused : ∀ i : Fin t,
      F.boundaryFlag i ∈ s₁ ↔ G.boundaryFlag i ∈ s₂)
    (hb : ∀ i : Fin t,
      F.boundaryFlag i ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags
        ↔ G.boundaryFlag i ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags)
    (κ₁ : (EdgeSubset.mk s₁ hc₁).RelTransitionSystem)
    (o₁ : κ₁.Orientation)
    (κ₂ : (EdgeSubset.mk s₂ hc₂).RelTransitionSystem)
    (o₂ : κ₂.Orientation)
    (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
    (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂))) {m : ℕ}
    (hcard₁ : Fintype.card (UsedLab (EdgeSubset.mk s₁ hc₁)) = 2 * m)
    (hcard₂ : Fintype.card (UsedLab (EdgeSubset.mk s₂ hc₂)) = 2 * m)
    (hM₁ : ∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
      (M₁.edge a).val = chordInv (EdgeSubset.mk s₁ hc₁) κ₁ a.val)
    (hM₂ : ∀ b : UsedLab (EdgeSubset.mk s₂ hc₂),
      (M₂.edge b).val = chordInv (EdgeSubset.mk s₂ hc₂) κ₂ b.val)
    (halt : ∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
      M₂.tail (usedLabInterfaceEquiv (EdgeSubset.mk s₁ hc₁)
        (EdgeSubset.mk s₂ hc₂) hb a) = !M₁.tail a) :
    (((DirMatching.sgnRel (DirMatching.stdMatching hcard₁) M₁
            : ℤ) : ℂ)
        * ((-1 : ℂ) ^ κ₁.openCircuitCount))
      * (((DirMatching.sgnRel (DirMatching.stdMatching hcard₂) M₂
            : ℤ) : ℂ)
        * ((-1 : ℂ) ^ κ₂.openCircuitCount))
      = (-1 : ℂ) ^ ((glueData t (closeBase F G)
            (pairStage hc₁ hc₂ hused κ₁ κ₂)).rel.openCircuitCount
          + glueCount t (closeBase F G)
            (pairStage hc₁ hc₂ hused κ₁ κ₂)) := by
  set hc := closeJoin_pairing_mem hc₁ hc₂ with hcdef
  set B : EdgeSubset (closeBase F G) :=
    EdgeSubset.mk (closeJoin s₁ s₂) hc with hBdef
  set eL := usedLabLeftCloseJoin (s₂ := s₂) hc hc₁ with heL
  set eR := usedLabRightCloseJoin (s₁ := s₁) hc hc₂ with heR
  have hcard₁' : Fintype.card (UsedLab (leftSub B)) = 2 * m :=
    (card_usedLab_leftSub_closeJoin hc hc₁).trans hcard₁
  have hcard₂' : Fintype.card (UsedLab (rightSub B)) = 2 * m :=
    (card_usedLab_rightSub_closeJoin hc hc₂).trans hcard₂
  have hsgn₁ := sgnRel_stdMatching_map eL.symm hcard₁ hcard₁' M₁
  have hsgn₂ := sgnRel_stdMatching_map eR.symm hcard₂ hcard₂' M₂
  have hcnt₁ : (pairRelLeft hc₁ hc (relabelTransUp
      (leftIso t).toEquiv (EdgeSubset.mk s₁ hc₁) κ₁)
      ).openCircuitCount = κ₁.openCircuitCount :=
    (openCircuitCount_pairRelLeft (s₂ := s₂) hc₁ hc _).trans
      (relabel_openCircuitCount (leftIso t).toEquiv
        (EdgeSubset.mk s₁ hc₁) κ₁)
  have hcnt₂ : (pairRelRight hc₂ hc (relabelTransUp
      (rightIso t).toEquiv (EdgeSubset.mk s₂ hc₂) κ₂)
      ).openCircuitCount = κ₂.openCircuitCount :=
    (openCircuitCount_pairRelRight (s₁ := s₁) hc₂ hc _).trans
      (relabel_openCircuitCount (rightIso t).toEquiv
        (EdgeSubset.mk s₂ hc₂) κ₂)
  have hmain := sign_composition t B
    (swapPaired_joinParts t F G s₁ s₂ hc hused)
    (pairRelLeft hc₁ hc (relabelTransUp (leftIso t).toEquiv
      (EdgeSubset.mk s₁ hc₁) κ₁))
    (pairRelRight hc₂ hc (relabelTransUp (rightIso t).toEquiv
      (EdgeSubset.mk s₂ hc₂) κ₂))
    (orientOfEq (leftSub_closeJoin hc hc₁).symm
      (relabelOrientUp (leftIso t).toEquiv
        (EdgeSubset.mk s₁ hc₁) o₁))
    (orientOfEq (rightSub_closeJoin hc hc₂).symm
      (relabelOrientUp (rightIso t).toEquiv
        (EdgeSubset.mk s₂ hc₂) o₂))
    (M₁.map eL.symm.toEquiv) (M₂.map eR.symm.toEquiv)
    hcard₁' hcard₂'
    (edge_eq_cutMatching _ _ _ _
      (edge_val_map_left hc hc₁ κ₁ M₁ hM₁))
    (edge_eq_cutMatching _ _ _ _
      (edge_val_map_right hc hc₂ κ₂ M₂ hM₂))
    (fun a => by
      change M₂.tail (eR _) = !M₁.tail (eL a)
      exact Eq.trans (congrArg M₂.tail
        (usedLabRight_interfaceSideDisj hc hc₁ hc₂ _ hb a))
        (halt (eL a)))
  simp only [hcnt₁, hcnt₂] at hmain
  refine Eq.trans ?_ hmain
  exact congrArg₂ (· * ·)
    (congrArg (fun z : ℤˣ => ((z : ℤ) : ℂ)
      * (-1 : ℂ) ^ κ₁.openCircuitCount) hsgn₁.symm)
    (congrArg (fun z : ℤˣ => ((z : ℤ) : ℂ)
      * (-1 : ℂ) ^ κ₂.openCircuitCount) hsgn₂.symm)

open Classical in
/-- **The pair term, with its constant named.**  RS21's (13) read
against (14): the pairing of the two fragments' terms at a pair of
subsets is the composition's own circuit sign, one factor for each
cut the pair closes, times the colouring sum of their agreement. -/
theorem exists_pairTerm_eq_glued_sign {k ℓ : ℕ}
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
        ↔ G.boundaryFlag i ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags) :
    ∃ (o₁' : (Classical.choice hn₁).1.Orientation)
      (o₂' : (Classical.choice hn₂).1.Orientation)
      (M₁ : DirMatching (UsedLab (EdgeSubset.mk s₁ hc₁)))
      (M₂ : DirMatching (UsedLab (EdgeSubset.mk s₂ hc₂))),
      (∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
        (M₁.edge a).val = chordInv (EdgeSubset.mk s₁ hc₁)
          (Classical.choice hn₁).1 a.val) ∧
      (∀ b : UsedLab (EdgeSubset.mk s₂ hc₂),
        (M₂.edge b).val = chordInv (EdgeSubset.mk s₂ hc₂)
          (Classical.choice hn₂).1 b.val) ∧
      (∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
        M₂.tail (usedLabInterfaceEquiv (EdgeSubset.mk s₁ hc₁)
            (EdgeSubset.mk s₂ hc₂) hb a)
          = !M₁.tail a) ∧
      (∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
        ¬ IsThroughLabel (EdgeSubset.mk s₁ hc₁) a.val →
        M₁.tail a = (cutMatching (EdgeSubset.mk s₁ hc₁)
          (Classical.choice hn₁).1 o₁').tail a) ∧
      (∀ b : UsedLab (EdgeSubset.mk s₂ hc₂),
        ¬ IsThroughLabel (EdgeSubset.mk s₂ hc₂) b.val →
        M₂.tail b = (cutMatching (EdgeSubset.mk s₂ hc₂)
          (Classical.choice hn₂).1 o₂').tail b) ∧
      (∀ a : UsedLab (EdgeSubset.mk s₁ hc₁),
        ¬ IsThroughLabel (EdgeSubset.mk s₁ hc₁) a.val →
        ¬ IsThroughLabel (EdgeSubset.mk s₂ hc₂)
          (usedLabInterfaceEquiv (EdgeSubset.mk s₁ hc₁)
            (EdgeSubset.mk s₂ hc₂) hb a).val →
        (cutMatching (EdgeSubset.mk s₂ hc₂)
              (Classical.choice hn₂).1 o₂').tail
            (usedLabInterfaceEquiv (EdgeSubset.mk s₁ hc₁)
              (EdgeSubset.mk s₂ hc₂) hb a)
          = !(cutMatching (EdgeSubset.mk s₁ hc₁)
              (Classical.choice hn₁).1 o₁').tail a) ∧
      (∑ x : GenBoundaryState k ℓ (Fin t),
          ∑ y : GenBoundaryState k ℓ (Fin t),
            superForm t x y * tensorTermAt F h s₁ x
              * tensorTermAt G h s₂ y)
        = (-1 : ℂ) ^ ((glueData t (closeBase F G)
              (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
                (Classical.choice hn₂).1)).rel.openCircuitCount
            + glueCount t (closeBase F G)
              (pairStage hc₁ hc₂ hused (Classical.choice hn₁).1
                (Classical.choice hn₂).1))
          * ∑ st : GenBoundaryState k ℓ (Fin t),
              pairAgreeValue (EdgeSubset.mk s₁ hc₁)
                (EdgeSubset.mk s₂ hc₂) h o₁' o₂' st := by
  obtain ⟨o₁', o₂', M₁, M₂, hM₁, hM₂, halt, hag₁, hag₂, halt',
    hval⟩ :=
    exists_sum_sum_superForm_tensorTermAt h t F G hc₁ hE₁ hn₁ hc₂
      hE₂ hn₂ hused hb
  refine ⟨o₁', o₂', M₁, M₂, hM₁, hM₂, halt, hag₁, hag₂, halt',
    hval.trans (congrArg₂ (· * ·) ?_ rfl)⟩
  have hcard : Fintype.card (UsedLab (EdgeSubset.mk s₂ hc₂))
      = Fintype.card (UsedLab (EdgeSubset.mk s₁ hc₁)) :=
    Fintype.card_congr (usedLabInterfaceEquiv (EdgeSubset.mk s₁ hc₁)
      (EdgeSubset.mk s₂ hc₂) hb).symm
  have hstd : ∀ {m m' : ℕ}
      (h1 : Fintype.card (UsedLab (EdgeSubset.mk s₂ hc₂)) = 2 * m)
      (h2 : Fintype.card (UsedLab (EdgeSubset.mk s₂ hc₂)) = 2 * m'),
      DirMatching.stdMatching h1 = DirMatching.stdMatching h2 := by
    intro m m' h1 h2
    have hmm : m = m' := by omega
    subst hmm
    rfl
  rw [hstd (card_usedLab_eq _ M₂) (hcard.trans (card_usedLab_eq _ M₁))]
  exact sign_composition_pair hc₁ hc₂ hused hb _ o₁' _ o₂' M₁ M₂
    (card_usedLab_eq _ M₁) (hcard.trans (card_usedLab_eq _ M₁)) hM₁
    hM₂ halt

open Classical in
/-- The base's free circles are the two fragments'. -/
theorem circles_closeBase {t : ℕ} (F G : Fragment (Fin t)) :
    (closeBase F G).circles = F.circles + G.circles := rfl

/-! ## Restricting the composition's data to the two fragments

The base's own transition data restrict to its two halves and descend
to the fragments; these are the data RS21's (13) is applied at, so
that the orientations on the two sides are the composition's own.
-/

open Classical in
/-- The base's system, restricted to the first fragment. -/
noncomputable def pairRelLeftDown {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    (κ : (EdgeSubset.mk (closeJoin s₁ s₂) hc).RelTransitionSystem) :
    (EdgeSubset.mk s₁ hc₁ : EdgeSubset F).RelTransitionSystem :=
  relabelTransDown (leftIso t).toEquiv (EdgeSubset.mk s₁ hc₁)
    (relOfEq (leftSub_closeJoin hc hc₁) (leftRel κ))

open Classical in
/-- The base's system, restricted to the second fragment. -/
noncomputable def pairRelRightDown {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (κ : (EdgeSubset.mk (closeJoin s₁ s₂) hc).RelTransitionSystem) :
    (EdgeSubset.mk s₂ hc₂ : EdgeSubset G).RelTransitionSystem :=
  relabelTransDown (rightIso t).toEquiv (EdgeSubset.mk s₂ hc₂)
    (relOfEq (rightSub_closeJoin hc hc₂) (rightRel κ))

open Classical in
/-- **Replacing an orientation off the internal flags.**  The two
laws bind only internal flags, so the directions elsewhere may be
given by any function at all. -/
noncomputable def orientReplace {α : Type}
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    (o : κ.Orientation) (g : W.Flag → Bool) : κ.Orientation where
  isOut f := if f ∈ F.internalFlags then o.isOut f else g f
  match_flip f hf := by
    rw [ite_eq_left (κ.match_mem f hf), ite_eq_left hf]
    exact o.match_flip f hf
  pairing_flip f hf hp := by
    rw [ite_eq_left hp, ite_eq_left hf]
    exact o.pairing_flip f hf hp

open Classical in
/-- At an internal flag the replacement keeps the direction. -/
theorem isOut_orientReplace_internal {α : Type}
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    (o : κ.Orientation) (g : W.Flag → Bool) {f : W.Flag}
    (hf : f ∈ F.internalFlags) :
    (orientReplace o g).isOut f = o.isOut f := ite_eq_left hf

open Classical in
/-- Off the internal flags the replacement is the given function. -/
theorem isOut_orientReplace_of_not_internal {α : Type}
    {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} (o : κ.Orientation)
    (g : W.Flag → Bool) {f : W.Flag} (hf : f ∉ F.internalFlags) :
    (orientReplace o g).isOut f = g f := ite_eq_right hf

/-! ## The colouring sum sees only the internal directions

RS21's colouring sum is built from the in-flag list at each vertex,
and a flag is on that list only if it is attached to the vertex —
that is, only if it is internal.  So the sum does not see how an
orientation directs a labelled end, and in particular is unchanged by
the port flips (13) performs.
-/

section OrientCongr

variable {α : Type}

private theorem attachWith_map_congr' {δ γ : Type} {P : δ → Prop}
    {l₁ l₂ : List δ} (hl : l₁ = l₂) (h₁ : ∀ x ∈ l₁, P x)
    (h₂ : ∀ x ∈ l₂, P x) (f : {x // P x} → γ) :
    (l₁.attachWith P h₁).map f = (l₂.attachWith P h₂).map f := by
  subst hl
  rfl

private theorem attachWith_flatMap_congr' {δ γ : Type} {P : δ → Prop}
    {l₁ l₂ : List δ} (hl : l₁ = l₂) (h₁ : ∀ x ∈ l₁, P x)
    (h₂ : ∀ x ∈ l₂, P x) (f : {x // P x} → List γ) :
    (l₁.attachWith P h₁).flatMap f
      = (l₂.attachWith P h₂).flatMap f := by
  subst hl
  rfl

open Classical in
/-- **The in-flag list sees only the internal directions.** -/
theorem relInFlagsAt_congr_internal {W : Fragment α}
    (F : EdgeSubset W)
    {κ : F.RelTransitionSystem} (o o' : κ.Orientation)
    (hio : ∀ f ∈ F.internalFlags, o.isOut f = o'.isOut f)
    (v : W.Vertex) :
    F.relInFlagsAt o v = F.relInFlagsAt o' v := by
  unfold EdgeSubset.relInFlagsAt
  congr 1
  ext f
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hf, hv, hb⟩
    exact ⟨hf, hv, by
      rw [← hio f (EdgeSubset.mem_internalFlags_iff.mpr ⟨hf, v, hv⟩)]
      exact hb⟩
  · rintro ⟨hf, hv, hb⟩
    exact ⟨hf, hv, by
      rw [hio f (EdgeSubset.mem_internalFlags_iff.mpr ⟨hf, v, hv⟩)]
      exact hb⟩

open Classical in
/-- The odd sign at a vertex sees only the internal directions. -/
theorem coreOddSignAt_congr_internal {W : Fragment α}
    (F : EdgeSubset W) {ℓ : ℕ}
    {κ : F.RelTransitionSystem} (o o' : κ.Orientation)
    (hio : ∀ f ∈ F.internalFlags, o.isOut f = o'.isOut f)
    (φ : F.CoreOddColouring ℓ) (v : W.Vertex) :
    F.coreOddSignAt o φ v = F.coreOddSignAt o' φ v :=
  congrArg List.prod (attachWith_map_congr'
    (relInFlagsAt_congr_internal F o o' hio v) _ _ _)

open Classical in
/-- The odd list at a vertex sees only the internal directions. -/
theorem coreOddListAt_congr_internal {W : Fragment α}
    (F : EdgeSubset W) {ℓ : ℕ}
    {κ : F.RelTransitionSystem} (o o' : κ.Orientation)
    (hio : ∀ f ∈ F.internalFlags, o.isOut f = o'.isOut f)
    (φ : F.CoreOddColouring ℓ) (v : W.Vertex) :
    F.coreOddListAt o φ v = F.coreOddListAt o' φ v :=
  attachWith_flatMap_congr'
    (relInFlagsAt_congr_internal F o o' hio v) _ _ _

open Classical in
/-- **RS21's colouring sum sees only the internal directions.**  It is
therefore unchanged by a port flip. -/
theorem edgeSum_congr_orient {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} (o o' : κ.Orientation)
    (hio : ∀ f ∈ F.internalFlags, o.isOut f = o'.isOut f) :
    F.edgeSum h st hbnd o = F.edgeSum h st hbnd o' := by
  unfold EdgeSubset.edgeSum
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  refine if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl (fun φ _ => ?_)
  refine if_congr Iff.rfl ?_ rfl
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [coreOddSignAt_congr_internal F o o' hio φ.core v,
    coreOddListAt_congr_internal F o o' hio φ.core v]

open Classical in
/-- **Replacing off the internal flags costs the colouring sum
nothing.** -/
theorem edgeSum_orientReplace [LinearOrder α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} (o : κ.Orientation)
    (g : W.Flag → Bool) :
    F.edgeSum h st hbnd (orientReplace o g)
      = F.edgeSum h st hbnd o :=
  edgeSum_congr_orient F h st hbnd _ o
    (fun _f hf => isOut_orientReplace_internal o g hf)

end OrientCongr

/-! ## The composition's value at any canonical family

The composition's constrained value does not depend on which
canonical data compute it, so the colouring recursion may be run from
whichever family is convenient — in particular from one built out of
the two fragments' own data.
-/

section AnyCanon

variable {L : Type}

open Classical in
/-- **The composition's constrained value at an arbitrary canonical
family.** -/
theorem throughMixedPartitionC_eq_edgeTermAt_canon
    [LinearOrder L] [IsEmpty L] {V : Fragment L}
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ L)
    (𝒟 : DataFamily V)
    (hcanon : ∀ (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
      (hE : (EdgeSubset.mk s hc).Eulerian)
      (hne : Nonempty (EdgeSubset.mk s hc).CanonData),
      EdgeSubset.PathCanonical (𝒟 s hc hE hne).2) :
    throughMixedPartitionC h V st
      = ((k : ℂ) - 2 * ℓ) ^ V.circles *
        ∑ s : Finset V.Flag,
          circuitWeight 𝒟 s * edgeTermAt h 𝒟 st s 0 := by
  rw [throughMixedPartitionC_isEmpty h st]
  refine congrArg (fun z => ((k : ℂ) - 2 * ℓ) ^ V.circles * z)
    (Finset.sum_congr rfl (fun s _ => ?_))
  by_cases hc : ∀ f ∈ s, V.pairing f ∈ s
  · by_cases hbnd : genBoundarySubsetMatches V s st
    · by_cases hE : (EdgeSubset.mk s hc).Eulerian
      · by_cases hne : Nonempty (EdgeSubset.mk s hc).CanonData
        · rw [dite_eq_left hc, dite_eq_left hbnd, ite_eq_left hE, dite_eq_left hne,
            circuitWeight_pos 𝒟 hc hE hne,
            edgeTermAt_pos h 𝒟 st hc hbnd hE hne 0, pow_zero,
            one_mul,
            ← throughSummand_eq_edgeSum (EdgeSubset.mk s hc) h st
              hbnd _ _]
          exact throughSummand_canon_indep (EdgeSubset.mk s hc) h st
            hbnd (Classical.choice hne)
            ⟨(𝒟 s hc hE hne).1,
              ⟨(𝒟 s hc hE hne).2, hcanon s hc hE hne⟩⟩
        · rw [dite_eq_left hc, dite_eq_left hbnd, ite_eq_left hE, dite_eq_right hne,
            edgeTermAt_eq_zero_of_not_canon h 𝒟 st hc hne 0,
            mul_zero]
      · rw [dite_eq_left hc, dite_eq_left hbnd, ite_eq_right hE,
          edgeTermAt_eq_zero_of_not_eulerian h 𝒟 st hc hE 0,
          mul_zero]
    · rw [dite_eq_left hc, dite_eq_right hbnd,
        edgeTermAt_eq_zero_of_not_matches h 𝒟 st hbnd 0, mul_zero]
  · rw [dite_eq_right hc, edgeTermAt_eq_zero_of_not_closed h 𝒟 st hc 0,
      mul_zero]

open Classical in
/-- **At the composition every orientation is path-canonical.**  So
any family of transition data there is a canonical one. -/
theorem pathCanonical_isEmpty [LinearOrder L] [IsEmpty L] {V : Fragment L}
    (F : EdgeSubset V)
    {κ : F.RelTransitionSystem} (o : κ.Orientation) :
    EdgeSubset.PathCanonical o :=
  pathCanonical_of_allInternal (allInternal_isEmpty F) o

open Classical in
/-- **The composition's constrained value at an arbitrary family.**
No canonicality hypothesis is needed: at an empty label type there
are no chords to order. -/
theorem throughMixedPartitionC_eq_edgeTermAt_any
    [LinearOrder L] [IsEmpty L] {V : Fragment L}
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ L)
    (𝒟 : DataFamily V) :
    throughMixedPartitionC h V st
      = ((k : ℂ) - 2 * ℓ) ^ V.circles *
        ∑ s : Finset V.Flag,
          circuitWeight 𝒟 s * edgeTermAt h 𝒟 st s 0 :=
  throughMixedPartitionC_eq_edgeTermAt_canon h st 𝒟
    (fun s hc _hE _hne => pathCanonical_isEmpty (EdgeSubset.mk s hc)
      (𝒟 s hc _hE _hne).2)

end AnyCanon

/-! ## The alternation, in chain-direction form

(13) reports its alternation on the chord matchings' tails; the glue
reads it on the chain directions.  At a chain label the two are the
same thing, negated.
-/

section TailChain

variable {α : Type}

open Classical in
/-- **The chord matching's tail at a chain label** is that label's
chain direction, reversed. -/
theorem cutMatching_tail_of_not_through [LinearOrder α] {W : Fragment α}
    (F : EdgeSubset W)
    (κ : F.RelTransitionSystem) (o : κ.Orientation) (i : UsedLab F)
    (hnt : ¬ IsThroughLabel F i.val) :
    (cutMatching F κ o).tail i
      = !chainDir o (W.boundaryFlag i.val) := by
  change (if IsThroughLabel F i.val then
      decide (i.val < chordInv F κ i.val)
    else !chainDir o (W.boundaryFlag i.val)) = _
  rw [ite_eq_right hnt]

end TailChain

/-! ## Lifting a data family across an open cut

The downward direction is `unglueDataOpen`; this is its upward
counterpart.  Where the family's own orientation directs the two
rewired ends oppositely — which is what RS21's step 1 arranges — the
glue applies; elsewhere the value is junk the identity never reads.
-/

open Classical in
/-- **The upward glue of a data family, at an open cut.** -/
noncomputable def glueDataOpen {α : Type} [LinearOrder α]
    {V : Fragment α} {i j : α} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (𝒟 : DataFamily V) :
    DataFamily (V.gluePairOpen i j hij hopen) :=
  fun t hct hEt hnet =>
    have hcL := liftSubsetOpen_pairing_closed hij hopen t hct
    have hEL := (eulerian_lift_open_iff hij hopen t hct hcL).mpr hEt
    have hneL :=
      nonempty_canonData_unglueOpen hij hopen t hct hcL hnet
    if hag : (𝒟 _ hcL hEL hneL).2.isOut
          (V.pairing (V.boundaryFlag j))
        = !(𝒟 _ hcL hEL hneL).2.isOut
          (V.pairing (V.boundaryFlag i)) then
      ⟨RelTransitionSystem.glueOpen hij hopen t hct hcL
          (𝒟 _ hcL hEL hneL).1,
        glueOrientationOpen hij hopen t hct hcL
          (𝒟 _ hcL hEL hneL).1 (𝒟 _ hcL hEL hneL).2 hag⟩
    else
      ⟨(Classical.choice hnet).1, (Classical.choice hnet).2.val⟩

open Classical in
/-- **The upward glue of a data family, at a closing cut.**  A
closing cut rewires no directions, so no compatibility is needed;
what it does need is the lift's bit, since a glued subset has two
lifts and they are different subsets of the base. -/
noncomputable def glueDataClosed {α : Type} [LinearOrder α]
    {V : Fragment α} {i j : α}
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (b : Bool) (𝒟 : DataFamily V) :
    DataFamily (V.gluePairClosed i j hclosed) :=
  fun t hct hEt hnet =>
    have hcL := liftSubsetClosed_pairing_closed hclosed t b hct
    have hEL :=
      (eulerian_liftClosed_iff' hclosed b t hct hcL).mpr hEt
    have hneL :=
      nonempty_canonData_unglueClosed hclosed t hct b hcL hnet
    ⟨RelTransitionSystem.glueClosed hclosed b t hct hcL
        (𝒟 _ hcL hEL hneL).1,
      glueOrientationClosed hclosed b t hct hcL
        (𝒟 _ hcL hEL hneL).1 (𝒟 _ hcL hEL hneL).2⟩

open Classical in
/-- **A data family under a relabel, upward.**  The counterpart of
`relabelDataDown`. -/
noncomputable def relabelDataUp {α' β' : Type} [LinearOrder α']
    [LinearOrder β'] (e : α' ≃o β') {W' : Fragment α'}
    (𝒟 : DataFamily W') : DataFamily (W'.relabel e.toEquiv) :=
  fun s hc hE hne =>
    ⟨relabelTransUp e.toEquiv (EdgeSubset.mk s hc)
        (𝒟 s hc
          ((relabelUp_eulerian e.toEquiv
            (EdgeSubset.mk s hc)).mp hE)
          ((nonempty_canonData_relabelUp e
            (EdgeSubset.mk s hc)).mp hne)).1,
      relabelOrientUp e.toEquiv (EdgeSubset.mk s hc)
        (𝒟 s hc
          ((relabelUp_eulerian e.toEquiv
            (EdgeSubset.mk s hc)).mp hE)
          ((nonempty_canonData_relabelUp e
            (EdgeSubset.mk s hc)).mp hne)).2⟩

open Classical in
/-- **One stage of the upward lift.**  The mirror of
`stepDataDown`: dispatch on whether the stage's cut closes, glue the
family across it, and relabel up. -/
noncomputable def stepDataUp (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (b : Bool) (𝒟 : DataFamily V) :
    DataFamily (stepFragment n V) :=
  relabelDataUp (stepIso n)
    (if hcl : V.pairing (V.boundaryFlag (cutL n))
        = V.boundaryFlag (cutR n) then
      dataOfEq (gluePair_eq_closed n V hcl).symm
        (glueDataClosed hcl b 𝒟)
    else
      dataOfEq (gluePair_eq_open n V hcl).symm
        (glueDataOpen (cutL_ne_cutR n) hcl 𝒟))

open Classical in
/-- **The upward lift over the whole interface.**  The mirror of
`pushData`, carrying one bit for each stage — the lift the closing
cuts leave undetermined. -/
noncomputable def liftData : (n : ℕ) →
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) →
    (Fin n → Bool) → DataFamily V →
    DataFamily (glueInterface 0 n 0 V)
  | 0, _, _, 𝒟 => relabelDataUp baseIso 𝒟
  | n + 1, V, bits, 𝒟 =>
      liftData n (stepFragment n V) (fun a => bits a.castSucc)
        (stepDataUp n V (bits (Fin.last n)) 𝒟)

/-! ## The colouring sum under a matching-equal system

The single-cut round trips rebuild the system rather than storing
it, so they hold only up to `MatchEq`.  The colouring sum reads the
system only through the partner of an internal flag, so it does not
tell the difference.
-/

section MatchEqSum

variable {α : Type}

open Classical in
/-- The odd sign function sees only the internal partners. -/
theorem coreOddSignFn_matchEq {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    (hm : κ.MatchEq κ') {ℓ : ℕ} (φ : F.CoreOddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.internalFlags}) :
    F.coreOddSignFn κ φ f = F.coreOddSignFn κ' φ f := by
  unfold EdgeSubset.coreOddSignFn
  exact congrArg (oddPartnerSign ℓ)
    (congrArg φ.val (Subtype.ext (hm f.val f.prop)))

open Classical in
/-- The odd pair function sees only the internal partners. -/
theorem coreOddPairFn_matchEq {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    (hm : κ.MatchEq κ') {ℓ : ℕ} (φ : F.CoreOddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.internalFlags}) :
    F.coreOddPairFn κ φ f = F.coreOddPairFn κ' φ f := by
  unfold EdgeSubset.coreOddPairFn
  refine congrArg (fun z => [φ.val ⟨f.val, _⟩, oddPartner ℓ z]) ?_
  exact congrArg φ.val (Subtype.ext (hm f.val f.prop))

open Classical in
/-- **The in-flag list sees only the internal directions**, across
two systems: it is cut out by the directions at the flags attached to
the vertex, and those are internal. -/
theorem relInFlagsAt_congr_isOut_internal {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    (o : κ.Orientation) (o' : κ'.Orientation)
    (hio : ∀ f ∈ F.internalFlags, o.isOut f = o'.isOut f)
    (v : W.Vertex) :
    F.relInFlagsAt o v = F.relInFlagsAt o' v := by
  unfold EdgeSubset.relInFlagsAt
  congr 1
  ext f
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hf, hv, hb⟩
    exact ⟨hf, hv, by
      rw [← hio f (EdgeSubset.mem_internalFlags_iff.mpr ⟨hf, v, hv⟩)]
      exact hb⟩
  · rintro ⟨hf, hv, hb⟩
    exact ⟨hf, hv, by
      rw [hio f (EdgeSubset.mem_internalFlags_iff.mpr ⟨hf, v, hv⟩)]
      exact hb⟩

open Classical in
/-- The odd sign at a vertex, under a matching-equal system, from the
internal directions alone. -/
theorem coreOddSignAt_matchEq_internal {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    (hm : κ.MatchEq κ') {ℓ : ℕ} (o : κ.Orientation)
    (o' : κ'.Orientation)
    (hio : ∀ f ∈ F.internalFlags, o.isOut f = o'.isOut f)
    (φ : F.CoreOddColouring ℓ) (v : W.Vertex) :
    F.coreOddSignAt o φ v = F.coreOddSignAt o' φ v := by
  unfold EdgeSubset.coreOddSignAt
  refine Eq.trans (congrArg List.prod (attachWith_map_congr'
    (relInFlagsAt_congr_isOut_internal o o' hio v) _
    (fun _x hf => mem_internal_of_mem_relInFlagsAt hf) _)) ?_
  exact congrArg List.prod
    (List.map_congr_left (fun x _ => coreOddSignFn_matchEq hm φ x))

open Classical in
/-- The odd list at a vertex, under a matching-equal system, from the
internal directions alone. -/
theorem coreOddListAt_matchEq_internal {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    (hm : κ.MatchEq κ') {ℓ : ℕ} (o : κ.Orientation)
    (o' : κ'.Orientation)
    (hio : ∀ f ∈ F.internalFlags, o.isOut f = o'.isOut f)
    (φ : F.CoreOddColouring ℓ) (v : W.Vertex) :
    F.coreOddListAt o φ v = F.coreOddListAt o' φ v := by
  unfold EdgeSubset.coreOddListAt
  refine Eq.trans (attachWith_flatMap_congr'
    (relInFlagsAt_congr_isOut_internal o o' hio v) _
    (fun _x hf => mem_internal_of_mem_relInFlagsAt hf) _) ?_
  exact List.flatMap_congr (fun x _ => coreOddPairFn_matchEq hm φ x)

open Classical in
/-- **RS21's colouring sum under a matching-equal system, from the
internal directions alone.**  The sum reads the directions only at
the flags attached to a vertex, so two orientations that agree there
compute it alike. -/
theorem edgeSum_matchEq_internal {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    (hm : κ.MatchEq κ') {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (o : κ.Orientation) (o' : κ'.Orientation)
    (hio : ∀ f ∈ F.internalFlags, o.isOut f = o'.isOut f) :
    F.edgeSum h st hbnd o = F.edgeSum h st hbnd o' := by
  unfold EdgeSubset.edgeSum
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  refine if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl (fun φ _ => ?_)
  refine if_congr Iff.rfl ?_ rfl
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [coreOddSignAt_matchEq_internal hm o o' hio φ.core v,
    coreOddListAt_matchEq_internal hm o o' hio φ.core v]

end MatchEqSum

/-! ## The summand under a change of family

Two families whose data at a subset are matching-equal at the same
directions give that subset the same summand.  This is the form in
which the round trip is read.
-/

section FamilyCongr

variable {L : Type}

/-- A transported system has the same partner map. -/
theorem match_relOfEq {V : Fragment L}
    {F₁ F₂ : EdgeSubset V} (hF : F₁ = F₂)
    (κ : F₁.RelTransitionSystem) (f : V.Flag) :
    (relOfEq hF κ).match_ f = κ.match_ f := by
  subst hF
  rfl

/-- A transported orientation has the same directions. -/
theorem isOut_orientOfEq {V : Fragment L}
    {F₁ F₂ : EdgeSubset V} (hF : F₁ = F₂)
    {κ : F₁.RelTransitionSystem} (o : κ.Orientation) (f : V.Flag) :
    (orientOfEq hF o).isOut f = o.isOut f := by
  subst hF
  rfl

end FamilyCongr

open Classical in
/-- **The open glue's value where it applies.**  Stated with the
lifted subset's own proofs, so that the call site may supply them
rather than reconstruct the definition's. -/
theorem glueDataOpen_pos {α : Type} [LinearOrder α]
    {V : Fragment α} {i j : α} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (𝒟 : DataFamily V) (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairOpen i j hij hopen).pairing f ∈ t)
    (hEt : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).CanonData)
    (hcL : ∀ f ∈ liftSubsetOpen hopen t,
      V.pairing f ∈ liftSubsetOpen hopen t)
    (hEL : (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
      EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk (liftSubsetOpen hopen t)
      hcL : EdgeSubset V).CanonData)
    (hag : (𝒟 (liftSubsetOpen hopen t) hcL hEL hneL).2.isOut
        (V.pairing (V.boundaryFlag j))
      = !(𝒟 (liftSubsetOpen hopen t) hcL hEL hneL).2.isOut
        (V.pairing (V.boundaryFlag i))) :
    (glueDataOpen hij hopen 𝒟 t hct hEt hnet).1
      = RelTransitionSystem.glueOpen hij hopen t hct hcL
        (𝒟 (liftSubsetOpen hopen t) hcL hEL hneL).1 := by
  unfold glueDataOpen
  rw [dite_eq_left hag]

open Classical in
/-- **The closing glue's directions.**  A closing cut rewires
nothing, so the glued orientation reads a surviving flag exactly as
the family at the lift does. -/
theorem isOut_glueDataClosed_pos {α : Type} [LinearOrder α]
    {V : Fragment α} {i j : α}
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (b : Bool) (𝒟 : DataFamily V) (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairClosed i j hclosed).pairing f ∈ t)
    (hEt : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).CanonData)
    (hcL : ∀ f ∈ liftSubsetClosed t b,
      V.pairing f ∈ liftSubsetClosed t b)
    (hEL : (EdgeSubset.mk (liftSubsetClosed t b) hcL :
      EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk (liftSubsetClosed t b) hcL :
      EdgeSubset V).CanonData)
    (f' : SurvivingFlag V i j) :
    (glueDataClosed hclosed b 𝒟 t hct hEt hnet).2.isOut f'
      = (𝒟 (liftSubsetClosed t b) hcL hEL hneL).2.isOut f'.val :=
  rfl

open Classical in
/-- **The open glue's directions where it applies.** -/
theorem isOut_glueDataOpen_pos {α : Type} [LinearOrder α]
    {V : Fragment α} {i j : α} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (𝒟 : DataFamily V) (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairOpen i j hij hopen).pairing f ∈ t)
    (hEt : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).CanonData)
    (hcL : ∀ f ∈ liftSubsetOpen hopen t,
      V.pairing f ∈ liftSubsetOpen hopen t)
    (hEL : (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
      EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk (liftSubsetOpen hopen t)
      hcL : EdgeSubset V).CanonData)
    (hag : (𝒟 (liftSubsetOpen hopen t) hcL hEL hneL).2.isOut
        (V.pairing (V.boundaryFlag j))
      = !(𝒟 (liftSubsetOpen hopen t) hcL hEL hneL).2.isOut
        (V.pairing (V.boundaryFlag i)))
    (f' : SurvivingFlag V i j) :
    (glueDataOpen hij hopen 𝒟 t hct hEt hnet).2.isOut f'
      = (𝒟 (liftSubsetOpen hopen t) hcL hEL hneL).2.isOut
        f'.val := by
  unfold glueDataOpen
  rw [dite_eq_left hag]
  rfl

section FamilySubsetCongr

variable {L : Type}

/-- **A family at equal subsets has the same partner map.**  The two
values have different types, so the equality is read on the partner
map rather than on the data. -/
theorem match_dataFamily_congr [LinearOrder L] {V : Fragment L}
    (𝒟 : DataFamily V)
    {s₁ s₂ : Finset V.Flag} (hs : s₁ = s₂)
    (hc₁ : ∀ f ∈ s₁, V.pairing f ∈ s₁)
    (hE₁ : (EdgeSubset.mk s₁ hc₁).Eulerian)
    (hne₁ : Nonempty (EdgeSubset.mk s₁ hc₁).CanonData)
    (hc₂ : ∀ f ∈ s₂, V.pairing f ∈ s₂)
    (hE₂ : (EdgeSubset.mk s₂ hc₂).Eulerian)
    (hne₂ : Nonempty (EdgeSubset.mk s₂ hc₂).CanonData)
    (f : V.Flag) :
    (𝒟 s₁ hc₁ hE₁ hne₁).1.match_ f = (𝒟 s₂ hc₂ hE₂ hne₂).1.match_ f
    := by
  subst hs
  rfl

/-- **A family at equal subsets has the same directions.** -/
theorem isOut_dataFamily_congr [LinearOrder L] {V : Fragment L}
    (𝒟 : DataFamily V)
    {s₁ s₂ : Finset V.Flag} (hs : s₁ = s₂)
    (hc₁ : ∀ f ∈ s₁, V.pairing f ∈ s₁)
    (hE₁ : (EdgeSubset.mk s₁ hc₁).Eulerian)
    (hne₁ : Nonempty (EdgeSubset.mk s₁ hc₁).CanonData)
    (hc₂ : ∀ f ∈ s₂, V.pairing f ∈ s₂)
    (hE₂ : (EdgeSubset.mk s₂ hc₂).Eulerian)
    (hne₂ : Nonempty (EdgeSubset.mk s₂ hc₂).CanonData)
    (f : V.Flag) :
    (𝒟 s₁ hc₁ hE₁ hne₁).2.isOut f = (𝒟 s₂ hc₂ hE₂ hne₂).2.isOut f
    := by
  subst hs
  rfl

end FamilySubsetCongr

open Classical in
/-- **The single-cut round trip, at an open cut.**  Lifting a family
across the cut and pushing it back returns the system up to
`MatchEq` — the glue rebuilds it rather than storing it. -/
theorem match_unglue_glueDataOpen {α : Type} [LinearOrder α]
    {V : Fragment α} {i j : α} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (𝒟 : DataFamily V) {s : Finset V.Flag}
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc : EdgeSubset V).CanonData)
    (hdc : ∀ f ∈ V.dropSubset i j s,
      (V.gluePairOpen i j hij hopen).pairing f
        ∈ V.dropSubset i j s)
    (hcL : ∀ f ∈ liftSubsetOpen hopen (V.dropSubset i j s),
      V.pairing f ∈ liftSubsetOpen hopen (V.dropSubset i j s))
    (hEL : (EdgeSubset.mk
      (liftSubsetOpen hopen (V.dropSubset i j s)) hcL :
      EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk
      (liftSubsetOpen hopen (V.dropSubset i j s)) hcL :
      EdgeSubset V).CanonData)
    (hag : (𝒟 (liftSubsetOpen hopen (V.dropSubset i j s))
          hcL hEL hneL).2.isOut (V.pairing (V.boundaryFlag j))
      = !(𝒟 (liftSubsetOpen hopen (V.dropSubset i j s))
          hcL hEL hneL).2.isOut (V.pairing (V.boundaryFlag i))) :
    ((unglueDataOpen hij hopen (glueDataOpen hij hopen 𝒟)) s hc hE
        hne).1.MatchEq (𝒟 s hc hE hne).1 := by
  have hlift : liftSubsetOpen hopen (V.dropSubset i j s) = s :=
    liftSubsetOpen_dropSubset hij hopen s hc
  have hF : (EdgeSubset.mk
        (liftSubsetOpen hopen (V.dropSubset i j s)) hcL :
      EdgeSubset V) = EdgeSubset.mk s hc := EdgeSubset.ext hlift
  intro f hf
  have hfL : f ∈ (EdgeSubset.mk
      (liftSubsetOpen hopen (V.dropSubset i j s)) hcL :
      EdgeSubset V).internalFlags := by
    rw [hF]
    exact hf
  unfold unglueDataOpen
  rw [dite_eq_left hdc, match_relOfEq,
    glueDataOpen_pos hij hopen 𝒟 (V.dropSubset i j s) hdc _ _
      hcL hEL hneL hag,
    unglueOpen_glueOpen_match hij hopen (V.dropSubset i j s) hdc
      hcL _ hfL]
  exact match_dataFamily_congr 𝒟 hlift hcL hEL hneL hc hE hne f

open Classical in
/-- **The single-cut round trip on directions, at an open cut.**  At
a surviving flag the round trip returns the direction on the nose. -/
theorem isOut_unglue_glueDataOpen {α : Type} [LinearOrder α]
    {V : Fragment α} {i j : α} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (𝒟 : DataFamily V) {s : Finset V.Flag}
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc : EdgeSubset V).CanonData)
    (hdc : ∀ f ∈ V.dropSubset i j s,
      (V.gluePairOpen i j hij hopen).pairing f
        ∈ V.dropSubset i j s)
    (hcL : ∀ f ∈ liftSubsetOpen hopen (V.dropSubset i j s),
      V.pairing f ∈ liftSubsetOpen hopen (V.dropSubset i j s))
    (hEL : (EdgeSubset.mk
      (liftSubsetOpen hopen (V.dropSubset i j s)) hcL :
      EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk
      (liftSubsetOpen hopen (V.dropSubset i j s)) hcL :
      EdgeSubset V).CanonData)
    (hag : (𝒟 (liftSubsetOpen hopen (V.dropSubset i j s))
          hcL hEL hneL).2.isOut (V.pairing (V.boundaryFlag j))
      = !(𝒟 (liftSubsetOpen hopen (V.dropSubset i j s))
          hcL hEL hneL).2.isOut (V.pairing (V.boundaryFlag i)))
    (f : V.Flag) (h1 : f ≠ V.boundaryFlag i)
    (h2 : f ≠ V.boundaryFlag j) :
    ((unglueDataOpen hij hopen (glueDataOpen hij hopen 𝒟)) s hc hE
        hne).2.isOut f = (𝒟 s hc hE hne).2.isOut f := by
  have hlift : liftSubsetOpen hopen (V.dropSubset i j s) = s :=
    liftSubsetOpen_dropSubset hij hopen s hc
  unfold unglueDataOpen
  rw [dite_eq_left hdc, isOut_orientOfEq]
  refine Eq.trans (unglueIsOut_of_surviving _ f ⟨h1, h2⟩) ?_
  rw [isOut_glueDataOpen_pos hij hopen 𝒟 (V.dropSubset i j s) hdc
    _ _ hcL hEL hneL hag]
  exact isOut_dataFamily_congr 𝒟 hlift hcL hEL hneL hc hE hne f

open Classical in
/-- **The single-cut round trip, at a closing cut.**  With the bit
the subset itself determines, lifting and pushing back returns the
system up to `MatchEq`. -/
theorem match_unglue_glueDataClosed {α : Type} [LinearOrder α]
    {V : Fragment α} {i j : α} (hij : i ≠ j)
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (𝒟 : DataFamily V) {s : Finset V.Flag}
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc : EdgeSubset V).CanonData)
    (hcL : ∀ f ∈ liftSubsetClosed (V.dropSubset i j s)
        (decide (V.boundaryFlag i ∈ s)),
      V.pairing f ∈ liftSubsetClosed (V.dropSubset i j s)
        (decide (V.boundaryFlag i ∈ s)))
    (hEL : (EdgeSubset.mk (liftSubsetClosed (V.dropSubset i j s)
      (decide (V.boundaryFlag i ∈ s))) hcL :
      EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk
      (liftSubsetClosed (V.dropSubset i j s)
        (decide (V.boundaryFlag i ∈ s))) hcL :
      EdgeSubset V).CanonData) :
    ((unglueDataClosed hij hclosed (glueDataClosed hclosed
        (decide (V.boundaryFlag i ∈ s)) 𝒟)) s hc hE
        hne).1.MatchEq (𝒟 s hc hE hne).1 := by
  have hlift : liftSubsetClosed (V.dropSubset i j s)
      (decide (V.boundaryFlag i ∈ s)) = s :=
    liftSubsetClosed_dropSubset hij hclosed s hc
  have hF : (EdgeSubset.mk (liftSubsetClosed (V.dropSubset i j s)
        (decide (V.boundaryFlag i ∈ s))) hcL :
      EdgeSubset V) = EdgeSubset.mk s hc := EdgeSubset.ext hlift
  intro f hf
  have hfL : f ∈ (EdgeSubset.mk
      (liftSubsetClosed (V.dropSubset i j s)
        (decide (V.boundaryFlag i ∈ s))) hcL :
      EdgeSubset V).internalFlags := by
    rw [hF]
    exact hf
  unfold unglueDataClosed
  rw [match_relOfEq]
  refine Eq.trans (unglueClosed_glueClosed_match hclosed
    (decide (V.boundaryFlag i ∈ s)) (V.dropSubset i j s) _ hcL
    (𝒟 (liftSubsetClosed (V.dropSubset i j s)
      (decide (V.boundaryFlag i ∈ s))) hcL hEL hneL).1 hfL) ?_
  exact match_dataFamily_congr 𝒟 hlift hcL hEL hneL hc hE hne f

open Classical in
/-- **The single-cut round trip on directions, at a closing cut.** -/
theorem isOut_unglue_glueDataClosed {α : Type} [LinearOrder α]
    {V : Fragment α} {i j : α} (hij : i ≠ j)
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (𝒟 : DataFamily V) {s : Finset V.Flag}
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc : EdgeSubset V).CanonData)
    (hcL : ∀ f ∈ liftSubsetClosed (V.dropSubset i j s)
        (decide (V.boundaryFlag i ∈ s)),
      V.pairing f ∈ liftSubsetClosed (V.dropSubset i j s)
        (decide (V.boundaryFlag i ∈ s)))
    (hEL : (EdgeSubset.mk (liftSubsetClosed (V.dropSubset i j s)
      (decide (V.boundaryFlag i ∈ s))) hcL :
      EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk
      (liftSubsetClosed (V.dropSubset i j s)
        (decide (V.boundaryFlag i ∈ s))) hcL :
      EdgeSubset V).CanonData)
    (f : V.Flag) (h1 : f ≠ V.boundaryFlag i)
    (h2 : f ≠ V.boundaryFlag j) :
    ((unglueDataClosed hij hclosed (glueDataClosed hclosed
        (decide (V.boundaryFlag i ∈ s)) 𝒟)) s hc hE hne).2.isOut f
      = (𝒟 s hc hE hne).2.isOut f := by
  have hlift : liftSubsetClosed (V.dropSubset i j s)
      (decide (V.boundaryFlag i ∈ s)) = s :=
    liftSubsetClosed_dropSubset hij hclosed s hc
  unfold unglueDataClosed
  rw [isOut_orientOfEq]
  refine Eq.trans (unglueIsOut_of_surviving _ f ⟨h1, h2⟩) ?_
  exact isOut_dataFamily_congr 𝒟 hlift hcL hEL hneL hc hE hne f

section TransportRoundTrip

variable {L : Type}

/-- **The relabel round trip is the identity on families.** -/
theorem relabelData_roundTrip {α' β' : Type} [LinearOrder α']
    [LinearOrder β'] (e : α' ≃o β') {W' : Fragment α'}
    (𝒟 : DataFamily W') :
    relabelDataDown e (relabelDataUp e 𝒟) = 𝒟 := rfl

/-- **The transport round trip is the identity on families.** -/
theorem dataOfEq_roundTrip [LinearOrder L]
    {V₁ V₂ : Fragment L} (h : V₁ = V₂)
    (𝒟 : DataFamily V₁) :
    dataOfEq h (dataOfEq h.symm 𝒟) = 𝒟 := by
  subst h
  rfl

end TransportRoundTrip

end EdgeSubset

end RS
