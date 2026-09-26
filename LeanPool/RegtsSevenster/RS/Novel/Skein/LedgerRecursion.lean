/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.LedgerCast
public import LeanPool.RegtsSevenster.RS.Novel.Skein.OrientExistence

/-!
# The data the interface recursion carries

RS21 composes two fragments in one step; the flag model glues the
interface one pair at a time, so the ledger (14) is proved by a
recursion over `glueInterface`.  What the recursion carries is a
subset of the current fragment, a transition system on it, and the
record that the subset uses the two halves of every remaining
interface pair together — the condition that makes the interface
matching exist and that a glue preserves.

This file names that data and the step that advances it.
-/

@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment Equiv
/-- The lexicographic order on the recursion's label type, as the
ambient instance.  It has to outrank the sum's own `≤`, which
otherwise wins on a sum type and does not agree with it. -/
@[reducible] local instance stageOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

/-- The same order one stage up, where the index shape differs. -/
@[reducible] local instance stageOrderSucc (n : ℕ) :
    LinearOrder (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) :=
  sumLexLinearOrder _ _

/-- The left label of the pair the recursion glues at size `n+1`. -/
abbrev cutL (n : ℕ) : Fin (0 + n + 1) ⊕ Fin (n + 1 + 0) :=
  Sum.inl ⟨0 + n, Nat.lt_succ_self _⟩

/-- The right label of the pair the recursion glues at size `n+1`. -/
abbrev cutR (n : ℕ) : Fin (0 + n + 1) ⊕ Fin (n + 1 + 0) :=
  Sum.inr ⟨n, by omega⟩

/-- The two labels of the pair being glued are distinct. -/
theorem cutL_ne_cutR (n : ℕ) : cutL n ≠ cutR n := Sum.inl_ne_inr

/-- The relabel the recursion performs after a glue.  The order has
to be pinned: on a sum type the ambient `≤` is the sum's own, which
is not the lexicographic one the interface uses. -/
@[reducible] noncomputable def stepIso (n : ℕ) :
    @OrderIso
      (SurvivingLabel (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) (cutL n)
        (cutR n))
      (Fin (0 + n) ⊕ Fin (n + 0))
      (sumLexSubtypeLE (Fin (0 + n + 1)) (Fin (n + 1 + 0))
        (fun x => x ≠ cutL n ∧ x ≠ cutR n))
      (sumLexLE (Fin (0 + n)) (Fin (n + 0))) :=
  interfaceStepOrderIso 0 n 0

/-- The swap on the labels surviving the glue: the next stage's
swap, read back through the relabel. -/
noncomputable def stepSwap (n : ℕ) :
    SurvivingLabel (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) (cutL n)
        (cutR n)
      → SurvivingLabel (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) (cutL n)
        (cutR n) :=
  fun x => (interfaceStepEquiv 0 n 0).symm
    (interfaceSwap (stepIdent n) (interfaceStepEquiv 0 n 0 x))

/-- The surviving-label swap agrees with the current stage's
interface swap on underlying labels. -/
theorem stepSwap_val (n : ℕ)
    (x : SurvivingLabel (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) (cutL n)
      (cutR n)) :
    ((stepSwap n x).val
        : Fin (0 + n + 1) ⊕ Fin (n + 1 + 0))
      = interfaceSwap (stepIdent (n + 1)) x.val :=
  interfaceSwap_interfaceStep n x

/-- The interface swap exchanges the pair the recursion glues. -/
theorem interfaceSwap_cutL (n : ℕ) :
    interfaceSwap (stepIdent (n + 1)) (cutL n) = cutR n :=
  interfaceSwap_cut n

/-- **The data one stage of the recursion carries.** -/
structure StageData (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) where
  /-- The subset of the current fragment. -/
  sub : EdgeSubset V
  /-- It uses the two halves of every remaining interface pair
  together. -/
  paired : SwapPaired sub (interfaceSwap (stepIdent n))
  /-- A transition system on it. -/
  rel : sub.RelTransitionSystem

/-! ## One step

Gluing the top interface pair takes the subset to its drop, the
system to its glue, and the pairing record along with them; the
relabel that follows carries all three.  The subset's own pairing
record is what makes the step total: it is exactly the condition
under which the drop is closed under the glued pairing.

The two branches are built over the fragment each glue actually
produces, and the dispatch `Fragment.gluePair` performs is undone
once, on the finished data.
-/

section Step

variable (n : ℕ)
  (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
  (D : StageData (n + 1) V)

/-- The flags the glue passes down: the subset's, less the two
glued ones. -/
noncomputable def stepFlags :
    Finset (SurvivingFlag V (cutL n) (cutR n)) :=
  V.dropSubset (cutL n) (cutR n) D.sub.flags

/-- Whether the subset carries the closed cut's own edge. -/
noncomputable def stepBit : Bool :=
  decide (V.boundaryFlag (cutL n) ∈ D.sub.flags)

/-- Transport the stage data along an equality of fragments. -/
noncomputable def stageDataOfEq {m : ℕ}
    {V₁ V₂ : Fragment (Fin (0 + m) ⊕ Fin (m + 0))} (h : V₁ = V₂)
    (Dm : StageData m V₁) : StageData m V₂ := by
  subst h; exact Dm

section Closed

variable (hcl : V.pairing (V.boundaryFlag (cutL n))
  = V.boundaryFlag (cutR n))

/-- On a closed cut the passed-down flags are edge-closed in the
glued fragment. -/
theorem stepFlags_closed_pairing_mem :
    ∀ f ∈ stepFlags n V D,
      (V.gluePairClosed (cutL n) (cutR n) hcl).pairing f
        ∈ stepFlags n V D :=
  dropSubset_pairing_closed_of_closed hcl D.sub.flags D.sub.pairing_mem

include hcl in
/-- Lifting the passed-down flags back through a closed glue
recovers the subset's flags. -/
theorem liftSubsetClosed_stepFlags :
    liftSubsetClosed (stepFlags n V D) (stepBit n V D)
      = D.sub.flags :=
  liftSubsetClosed_dropSubset (cutL_ne_cutR n) hcl D.sub.flags
    D.sub.pairing_mem

include hcl in
/-- The lifted flags are edge-closed in the unglued fragment. -/
theorem liftSubsetClosed_stepFlags_pairing_mem :
    ∀ f ∈ liftSubsetClosed (stepFlags n V D) (stepBit n V D),
      V.pairing f
        ∈ liftSubsetClosed (stepFlags n V D) (stepBit n V D) := by
  rw [liftSubsetClosed_stepFlags n V D hcl]
  exact D.sub.pairing_mem

include hcl in
/-- The stage's subset is the lift of what the closed glue passes
down: nothing is lost across the step. -/
theorem sub_eq_liftSubsetClosed :
    D.sub = EdgeSubset.mk _
      (liftSubsetClosed_stepFlags_pairing_mem n V D hcl) :=
  EdgeSubset.ext (liftSubsetClosed_stepFlags n V D hcl).symm

include hcl in
/-- The glued subset at a closed cut. -/
@[reducible] noncomputable def stepSubClosed :
    EdgeSubset (V.gluePairClosed (cutL n) (cutR n) hcl) :=
  EdgeSubset.mk (stepFlags n V D)
    (stepFlags_closed_pairing_mem n V D hcl)

open Fragment in
/-- One step at a closed cut. -/
noncomputable def stepDataClosed :
    StageData n
      ((V.gluePairClosed (cutL n) (cutR n) hcl).relabel
        (interfaceStepEquiv 0 n 0)) where
  sub := (stepSubClosed n V D hcl).relabelUp (stepIso n).toEquiv
  paired := swapPaired_relabelUp (stepIso n) (stepSubClosed n V D hcl)
    (stepSwap n) (interfaceSwap (stepIdent n)) (fun _ => rfl)
    (swapPaired_glueClosed hcl (stepBit n V D) (stepFlags n V D)
      (stepFlags_closed_pairing_mem n V D hcl)
      (liftSubsetClosed_stepFlags_pairing_mem n V D hcl)
      (interfaceSwap (stepIdent (n + 1))) (stepSwap n)
      (stepSwap_val n)
      (swapPaired_of_eq (sub_eq_liftSubsetClosed n V D hcl) _
        D.paired))
  rel := relabelTransUp (stepIso n).toEquiv (stepSubClosed n V D hcl)
    (RelTransitionSystem.glueClosed hcl (stepBit n V D)
      (stepFlags n V D) (stepFlags_closed_pairing_mem n V D hcl)
      (liftSubsetClosed_stepFlags_pairing_mem n V D hcl)
      (relOfEq (sub_eq_liftSubsetClosed n V D hcl) D.rel))

end Closed

section Open

variable (hop : V.pairing (V.boundaryFlag (cutL n))
  ≠ V.boundaryFlag (cutR n))

/-- The stage's subset uses the two halves of the glued pair
together — the record the recursion carries. -/
theorem agreeingSubset_sub :
    AgreeingSubset (cutL n) (cutR n) D.sub.flags :=
  agreeingSubset_of_swapPaired D.sub _ D.paired (interfaceSwap_cutL n)

/-- On an open cut the passed-down flags are edge-closed in the
glued fragment. -/
theorem stepFlags_open_pairing_mem :
    ∀ f ∈ stepFlags n V D,
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop).pairing f
        ∈ stepFlags n V D :=
  dropSubset_rewire_closed hop D.sub.flags (agreeingSubset_sub n V D)

include hop in
/-- Lifting the passed-down flags back through an open glue
recovers the subset's flags. -/
theorem liftSubsetOpen_stepFlags :
    liftSubsetOpen hop (stepFlags n V D)
      = D.sub.flags :=
  liftSubsetOpen_dropSubset (cutL_ne_cutR n) hop D.sub.flags
    D.sub.pairing_mem

include hop in
/-- The lifted flags are edge-closed in the unglued fragment. -/
theorem liftSubsetOpen_stepFlags_pairing_mem :
    ∀ f ∈ liftSubsetOpen hop (stepFlags n V D),
      V.pairing f
        ∈ liftSubsetOpen hop (stepFlags n V D) := by
  rw [liftSubsetOpen_stepFlags n V D hop]
  exact D.sub.pairing_mem

include hop in
/-- The open-cut analogue: the stage's subset is the lift. -/
theorem sub_eq_liftSubsetOpen :
    D.sub = EdgeSubset.mk _
      (liftSubsetOpen_stepFlags_pairing_mem n V D hop) :=
  EdgeSubset.ext (liftSubsetOpen_stepFlags n V D hop).symm

include hop in
/-- The glued subset at an open cut. -/
@[reducible] noncomputable def stepSubOpen :
    EdgeSubset (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop) :=
  EdgeSubset.mk (stepFlags n V D)
    (stepFlags_open_pairing_mem n V D hop)

open Fragment in
/-- One step at an open cut. -/
noncomputable def stepDataOpen :
    StageData n
      ((V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop).relabel
        (interfaceStepEquiv 0 n 0)) where
  sub := (stepSubOpen n V D hop).relabelUp (stepIso n).toEquiv
  paired := swapPaired_relabelUp (stepIso n) (stepSubOpen n V D hop)
    (stepSwap n) (interfaceSwap (stepIdent n)) (fun _ => rfl)
    (swapPaired_glueOpen (cutL_ne_cutR n) hop (stepFlags n V D)
      (stepFlags_open_pairing_mem n V D hop)
      (liftSubsetOpen_stepFlags_pairing_mem n V D hop)
      (interfaceSwap (stepIdent (n + 1))) (stepSwap n)
      (stepSwap_val n)
      (swapPaired_of_eq (sub_eq_liftSubsetOpen n V D hop) _ D.paired))
  rel := relabelTransUp (stepIso n).toEquiv (stepSubOpen n V D hop)
    (RelTransitionSystem.glueOpen (cutL_ne_cutR n) hop
      (stepFlags n V D) (stepFlags_open_pairing_mem n V D hop)
      (liftSubsetOpen_stepFlags_pairing_mem n V D hop)
      (relOfEq (sub_eq_liftSubsetOpen n V D hop) D.rel))

end Open

open Fragment Classical in
/-- **One step of the recursion**: glue the top interface pair and
relabel. -/
noncomputable def stepData :
    StageData n
      ((V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n)).relabel
        (interfaceStepEquiv 0 n 0)) :=
  if hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n) then
    stageDataOfEq
      (congrArg (fun X => X.relabel (interfaceStepEquiv 0 n 0))
        (gluePair_eq_closed (cutL_ne_cutR n) hcl).symm)
      (stepDataClosed n V D hcl)
  else
    stageDataOfEq
      (congrArg (fun X => X.relabel (interfaceStepEquiv 0 n 0))
        (gluePair_eq_open (cutL_ne_cutR n) hcl).symm)
      (stepDataOpen n V D hcl)

end Step

/-! ## The recursion

Iterating the step over the whole interface carries the data to the
composed fragment, and the accumulator records the cuts at which a
component of the union disappears: the closed ones whose edge the
subset carries.
-/

/-- The relabel that closes the recursion at the empty interface. -/
noncomputable def endEquiv :
    (Fin (0 + 0) ⊕ Fin (0 + 0)) ≃ (Fin 0 ⊕ Fin 0) :=
  Equiv.sumCongr (finCongr (by omega)) (finCongr (by omega))

/-- **The data carried to the composed fragment.** -/
noncomputable def glueData : (n : ℕ) →
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) → StageData n V →
    StageData 0 (glueInterface 0 n 0 V)
  | 0, _, D =>
      { sub := D.sub.relabelUp endEquiv
        paired := fun x =>
          match x with
          | Sum.inl a => a.elim0
          | Sum.inr b => b.elim0
        rel := relabelTransUp endEquiv D.sub D.rel }
  | n + 1, V, D => glueData n _ (stepData n V D)

open Classical in
/-- **The cuts at which a component disappears**: the closed ones
whose edge the subset carries. -/
noncomputable def glueCount : (n : ℕ) →
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) → StageData n V → ℕ
  | 0, _, _ => 0
  | n + 1, V, D =>
      (if V.pairing (V.boundaryFlag (cutL n))
            = V.boundaryFlag (cutR n) ∧ stepBit n V D = true then 1
        else 0)
        + glueCount n _ (stepData n V D)

/-! ## The ledger the recursion transports

RS21's (14) compares the composed system's circuit count with the two
fragments' counts and the number of components of the union.  In the
recursion that quantity is read at every stage, of the current
fragment's own system and the interface matching still to be glued.
-/

/-- **The ledger at one stage**: the circuit count plus the number of
components of the union with the interface matching. -/
noncomputable def ledgerOf {n : ℕ}
    {V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))} (F : EdgeSubset V)
    (hp : SwapPaired F (interfaceSwap (stepIdent n)))
    (κ : F.RelTransitionSystem) : ℕ :=
  κ.openCircuitCount
    + DirMatching.unionCount (cutMatching F κ (relBuildOrientation κ))
        (interfaceCut F (stepIdent n)
          ((swapPaired_iff_interfacePaired F (stepIdent n)).mp hp))

/-- The ledger of a stage's data. -/
noncomputable def stageLedger (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) (D : StageData n V) :
    ℕ := ledgerOf D.sub D.paired D.rel

/-- The ledger does not see which of two equal subsets it is
stated at. -/
theorem ledgerOf_congr {n : ℕ}
    {V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))} {F F' : EdgeSubset V}
    (hF : F = F') (hp : SwapPaired F (interfaceSwap (stepIdent n)))
    (hp' : SwapPaired F' (interfaceSwap (stepIdent n)))
    (κ : F.RelTransitionSystem) :
    ledgerOf F' hp' (relOfEq hF κ) = ledgerOf F hp κ := by
  subst hF; rfl

/-- Transporting the stage data along an equality of fragments does
not change its ledger. -/
theorem stageLedger_stageDataOfEq {m : ℕ}
    {V₁ V₂ : Fragment (Fin (0 + m) ⊕ Fin (m + 0))} (h : V₁ = V₂)
    (D : StageData m V₁) :
    stageLedger m V₂ (stageDataOfEq h D) = stageLedger m V₁ D := by
  subst h; rfl

open Classical in
/-- On a closed cut the step is the closed branch, transported. -/
theorem stepData_eq_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (D : StageData (n + 1) V)
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) :
    stepData n V D
      = stageDataOfEq
          (congrArg (fun X => X.relabel (interfaceStepEquiv 0 n 0))
            (gluePair_eq_closed (cutL_ne_cutR n) hcl).symm)
          (stepDataClosed n V D hcl) := by
  unfold stepData
  rw [dite_eq_left hcl]

open Classical in
/-- On an open cut the step is the open branch, transported. -/
theorem stepData_eq_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (D : StageData (n + 1) V)
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) :
    stepData n V D
      = stageDataOfEq
          (congrArg (fun X => X.relabel (interfaceStepEquiv 0 n 0))
            (gluePair_eq_open (cutL_ne_cutR n) hop).symm)
          (stepDataOpen n V D hop) := by
  unfold stepData
  rw [dite_eq_right hop]

/-! ## One stage of the ledger

Each branch of the step is discharged by the stage theorem for its
kind of cut, at the interface matching and any orientation — the
ledger reads neither the orientation nor which proof of the pairing
record is supplied.
-/

-- The ledger of the stepped data is computed, so
-- the stage data and its glue all unfold.
/-- **The closed-cut step of the ledger**: gluing a closed pair the
subset carries closes one more circuit, so the ledger drops by the
step bit. -/
theorem stageLedger_stepDataClosed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (D : StageData (n + 1) V)
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) :
    stageLedger n _ (stepDataClosed n V D hcl)
        + (if stepBit n V D = true then 1 else 0)
      = stageLedger (n + 1) V D := by
  have hpl := swapPaired_of_eq (sub_eq_liftSubsetClosed n V D hcl) _
    D.paired
  have hpg := (stepDataClosed n V D hcl).paired
  rw [stageLedger, stageLedger, ←
    ledgerOf_congr (sub_eq_liftSubsetClosed n V D hcl) D.paired hpl
      D.rel]
  simp only [ledgerOf]
  exact ledgerStage_closed_bit (cutL_ne_cutR n) hcl (stepFlags n V D)
    (stepBit n V D) (stepFlags_closed_pairing_mem n V D hcl)
    (liftSubsetClosed_stepFlags_pairing_mem n V D hcl) (stepIso n)
    (relOfEq (sub_eq_liftSubsetClosed n V D hcl) D.rel)
    (relBuildOrientation _) (relBuildOrientation _)
    (relBuildOrientation _) (relBuildOrientation _)
    (interfaceSwap (stepIdent (n + 1))) (interfaceSwap_cutL n)
    (interfaceCut_edge_val _ (stepIdent (n + 1))
      ((swapPaired_iff_interfacePaired _ (stepIdent (n + 1))).mp hpl))
    (fun z =>
      (congrArg Subtype.val (interfaceCut_relabelUp_edge
        (stepSubClosed n V D hcl) (stepIso n) (stepIdent n)
        ((swapPaired_iff_interfacePaired _ (stepIdent n)).mp hpg)
        z)).trans (stepSwap_val n z.val))

-- As for the closed cut.
/-- **The open-cut step of the ledger**: gluing an open pair closes
nothing, so the ledger is unchanged. -/
theorem stageLedger_stepDataOpen (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (D : StageData (n + 1) V)
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) :
    stageLedger n _ (stepDataOpen n V D hop)
      = stageLedger (n + 1) V D := by
  have hpl := swapPaired_of_eq (sub_eq_liftSubsetOpen n V D hop) _
    D.paired
  have hpg := (stepDataOpen n V D hop).paired
  rw [stageLedger, stageLedger, ←
    ledgerOf_congr (sub_eq_liftSubsetOpen n V D hop) D.paired hpl
      D.rel]
  simp only [ledgerOf]
  exact ledgerStage_open_any (cutL_ne_cutR n) hop (stepFlags n V D)
    (stepFlags_open_pairing_mem n V D hop)
    (liftSubsetOpen_stepFlags_pairing_mem n V D hop) (stepIso n)
    (relOfEq (sub_eq_liftSubsetOpen n V D hop) D.rel)
    (relBuildOrientation _) (relBuildOrientation _)
    (relBuildOrientation _)
    (interfaceSwap (stepIdent (n + 1))) (interfaceSwap_cutL n)
    (interfaceCut_edge_val _ (stepIdent (n + 1))
      ((swapPaired_iff_interfacePaired _ (stepIdent (n + 1))).mp hpl))
    (fun z =>
      (congrArg Subtype.val (interfaceCut_relabelUp_edge
        (stepSubOpen n V D hop) (stepIso n) (stepIdent n)
        ((swapPaired_iff_interfacePaired _ (stepIdent n)).mp hpg)
        z)).trans (stepSwap_val n z.val))

/-! ## RS21's (14)

The ledger is transported by the whole recursion: the composed
system's circuit count, plus one for each closed cut whose edge the
subset carries, is the starting system's circuit count plus the
number of components of the union with the interface matching.
-/

/-- At stage zero there are no labels left: the recursion's base. -/
instance stageEmpty : IsEmpty (Fin (0 + 0) ⊕ Fin (0 + 0)) :=
  ⟨fun x =>
    match x with
    | Sum.inl a => a.elim0
    | Sum.inr b => b.elim0⟩

-- The recursion on the cut count carries the whole
-- stage data at every step.
/-- **RS21's (14), transported by the recursion.** -/
theorem ledger_glueData : ∀ (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) (D : StageData n V),
    stageLedger 0 _ (glueData n V D) + glueCount n V D
      = stageLedger n V D
  | 0, V, D => by
    have hzero : ∀ {W : Fragment (Fin (0 + 0) ⊕ Fin (0 + 0))}
        (F : EdgeSubset W) (M N : DirMatching (UsedLab F)),
        DirMatching.unionCount M N = 0 := by
      intro W F M N
      have : IsEmpty (UsedLab F) := ⟨fun x => isEmptyElim x.val⟩
      exact DirMatching.unionCount_of_isEmpty M N
    simp only [glueCount, stageLedger, ledgerOf, glueData, hzero,
      Nat.add_zero]
    exact relabel_openCircuitCount endEquiv D.sub D.rel
  | n + 1, V, D => by
    have ih := ledger_glueData n _ (stepData n V D)
    have hgd : glueData (n + 1) V D
        = glueData n _ (stepData n V D) := rfl
    have hgc : glueCount (n + 1) V D
        = (if V.pairing (V.boundaryFlag (cutL n))
              = V.boundaryFlag (cutR n) ∧ stepBit n V D = true then 1
            else 0)
          + glueCount n _ (stepData n V D) := rfl
    have hstep : stageLedger n _ (stepData n V D)
          + (if V.pairing (V.boundaryFlag (cutL n))
                = V.boundaryFlag (cutR n) ∧ stepBit n V D = true then 1
              else 0)
        = stageLedger (n + 1) V D := by
      by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
          = V.boundaryFlag (cutR n)
      · rw [stepData_eq_closed n V D hcl, stageLedger_stageDataOfEq,
          show (if V.pairing (V.boundaryFlag (cutL n))
                = V.boundaryFlag (cutR n) ∧ stepBit n V D = true then 1
              else 0) = (if stepBit n V D = true then 1 else 0) from by
            by_cases hb : stepBit n V D = true
            · rw [ite_eq_left ⟨hcl, hb⟩, ite_eq_left hb]
            · rw [ite_eq_right (fun h => hb h.2), ite_eq_right hb]]
        exact stageLedger_stepDataClosed n V D hcl
      · rw [stepData_eq_open n V D hcl, stageLedger_stageDataOfEq,
          ite_eq_right (fun h => hcl h.1), Nat.add_zero]
        exact stageLedger_stepDataOpen n V D hcl
    rw [show stageLedger 0 _ (glueData (n + 1) V D)
          + glueCount (n + 1) V D
        = stageLedger 0 _ (glueData n _ (stepData n V D))
          + ((if V.pairing (V.boundaryFlag (cutL n))
                = V.boundaryFlag (cutR n) ∧ stepBit n V D = true then 1
              else 0)
            + glueCount n _ (stepData n V D)) from by
      rw [hgc]
      exact congrArg (fun X => stageLedger 0 _ X + _) hgd]
    omega

/-- At the empty interface the ledger is the circuit count: there
are no used labels, hence no components to count. -/
theorem ledgerOf_isEmpty {V : Fragment (Fin (0 + 0) ⊕ Fin (0 + 0))}
    (F : EdgeSubset V)
    (hp : SwapPaired F (interfaceSwap (stepIdent 0)))
    (κ : F.RelTransitionSystem) :
    ledgerOf F hp κ = κ.openCircuitCount := by
  have : IsEmpty (UsedLab F) := ⟨fun x => isEmptyElim x.val⟩
  rw [ledgerOf, DirMatching.unionCount_of_isEmpty, Nat.add_zero]

/-- **RS21's (14).**  The composed system's circuit count, plus one
for each closed cut whose edge the subset carries, is the starting
system's circuit count plus the number of components of its union
with the interface matching. -/
theorem openCircuitCount_glueData (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) (D : StageData n V) :
    (glueData n V D).rel.openCircuitCount + glueCount n V D
      = stageLedger n V D := by
  rw [← ledger_glueData n V D, stageLedger, ledgerOf_isEmpty]

/-! ## The circles the composition creates

A closed cut turns its edge into a free circle, and the partition
function weights each by `k - 2ℓ`.  RS21's graph model has no room
for a vertex-free circle, so this is bookkeeping the flag model has
to carry on its own; it depends only on the fragment, not on the
subset.
-/

open Classical in
/-- **The cuts the composition closes.** -/
noncomputable def closedCuts : (n : ℕ) →
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) → ℕ
  | 0, _ => 0
  | n + 1, V =>
      (if V.pairing (V.boundaryFlag (cutL n))
          = V.boundaryFlag (cutR n) then 1 else 0)
        + closedCuts n ((V.gluePair (cutL n) (cutR n)
            (cutL_ne_cutR n)).relabel (interfaceStepEquiv 0 n 0))

open Classical in
/-- **The composition's free circles.** -/
theorem circles_glueInterface : ∀ (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))),
    (glueInterface 0 n 0 V).circles = V.circles + closedCuts n V
  | 0, V => by
    change V.circles = V.circles + 0
    omega
  | n + 1, V => by
    have ih := circles_glueInterface n
      ((V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n)).relabel
        (interfaceStepEquiv 0 n 0))
    have hstep : ((V.gluePair (cutL n) (cutR n)
          (cutL_ne_cutR n)).relabel
          (interfaceStepEquiv 0 n 0)).circles
        = V.circles + (if V.pairing (V.boundaryFlag (cutL n))
            = V.boundaryFlag (cutR n) then 1 else 0) := by
      change (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n)).circles = _
      unfold Fragment.gluePair
      by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
          = V.boundaryFlag (cutR n)
      · rw [dite_eq_left hcl, ite_eq_left hcl]
        rfl
      · rw [dite_eq_right hcl, ite_eq_right hcl]
        change V.circles = V.circles + 0
        omega
    change (glueInterface 0 n 0 _).circles = _
    rw [ih, hstep]
    change _ = V.circles + ((if V.pairing (V.boundaryFlag (cutL n))
        = V.boundaryFlag (cutR n) then 1 else 0) + _)
    omega

/-! ## The ledger at the start of the recursion

The recursion starts at the disjoint union of the two fragments, and
there the ledger splits into RS21's own terms: the two circuit counts
and the number of components of the union of the two chord matchings,
read on one copy of the label set.
-/

/-- **The ledger at a disjoint union.** -/
theorem stageLedger_disjUnion (n : ℕ)
    {W₁ : Fragment (Fin (0 + n))} {W₂ : Fragment (Fin (n + 0))}
    (F : EdgeSubset (W₁.disjUnion W₂))
    (hp : SwapPaired F (interfaceSwap (stepIdent n)))
    (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem)
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation) :
    stageLedger n (W₁.disjUnion W₂)
        ⟨F, hp, prodRel κ₁ κ₂⟩
      = κ₁.openCircuitCount + κ₂.openCircuitCount
        + DirMatching.unionCount (cutMatching (leftSub F) κ₁ o₁)
            ((cutMatching (rightSub F) κ₂ o₂).map
              (interfaceSideDisjEquiv F (stepIdent n)
                ((swapPaired_iff_interfacePaired F
                  (stepIdent n)).mp hp)).symm) := by
  rw [stageLedger, ledgerOf, openCircuitCount_prodRel κ₁ κ₂,
    DirMatching.unionCount_congr
      (cutMatching_congr_matchEq (RelTransitionSystem.MatchEq.refl _)
        (prodOrient o₁ o₂) (relBuildOrientation (prodRel κ₁ κ₂)))
      (rfl : (interfaceCut F (stepIdent n)
        ((swapPaired_iff_interfacePaired F (stepIdent n)).mp hp)).edge
        = _),
    unionCount_cutMatching_disjUnion F (stepIdent n) κ₁ κ₂ o₁ o₂]

/-- The interface identification at size `n`, as an order
isomorphism. -/
def stepIdentOrderIso (n : ℕ) : Fin (0 + n) ≃o Fin (n + 0) :=
  Fin.castOrderIso (by omega)

open Classical in
/-- **RS21's (14), as the sign identity it is used as.**  The two
fragments' matching signs and circuit signs multiply to the composed
system's circuit sign, together with the sign of the cuts at which a
component disappears. -/
theorem sign_composition (n : ℕ) {W₁ : Fragment (Fin (0 + n))}
    {W₂ : Fragment (Fin (n + 0))}
    (F : EdgeSubset (W₁.disjUnion W₂))
    (hp : SwapPaired F (interfaceSwap (stepIdent n)))
    (κ₁ : (leftSub F).RelTransitionSystem)
    (κ₂ : (rightSub F).RelTransitionSystem)
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation)
    (M₁ : DirMatching (UsedLab (leftSub F)))
    (M₂ : DirMatching (UsedLab (rightSub F))) {m : ℕ}
    (hc₁ : Fintype.card (UsedLab (leftSub F)) = 2 * m)
    (hc₂ : Fintype.card (UsedLab (rightSub F)) = 2 * m)
    (hM₁ : M₁.edge = (cutMatching (leftSub F) κ₁ o₁).edge)
    (hM₂ : M₂.edge = (cutMatching (rightSub F) κ₂ o₂).edge)
    (halt : ∀ a : UsedLab (leftSub F),
      M₂.tail (interfaceSideDisjOrderIso F (stepIdentOrderIso n)
        ((swapPaired_iff_interfacePaired F (stepIdent n)).mp hp) a)
        = !M₁.tail a) :
    ((DirMatching.sgnRel (DirMatching.stdMatching hc₁) M₁ : ℤ) : ℂ)
        * ((-1 : ℂ) ^ κ₁.openCircuitCount)
        * (((DirMatching.sgnRel (DirMatching.stdMatching hc₂) M₂
              : ℤ) : ℂ) * ((-1 : ℂ) ^ κ₂.openCircuitCount))
      = (-1 : ℂ) ^ ((glueData n (W₁.disjUnion W₂)
            ⟨F, hp, prodRel κ₁ κ₂⟩).rel.openCircuitCount
          + glueCount n (W₁.disjUnion W₂) ⟨F, hp, prodRel κ₁ κ₂⟩) := by
  have hEs : (interfaceSideDisjOrderIso F (stepIdentOrderIso n)
        ((swapPaired_iff_interfacePaired F
          (stepIdent n)).mp hp)).symm.toEquiv
      = (interfaceSideDisjEquiv F (stepIdent n)
          ((swapPaired_iff_interfacePaired F
            (stepIdent n)).mp hp)).symm := rfl
  have hsgn := DirMatching.sgnRel_mul_sgnRel_of_alternating
    (interfaceSideDisjOrderIso F (stepIdentOrderIso n)
      ((swapPaired_iff_interfacePaired F (stepIdent n)).mp hp))
    hc₁ hc₂ M₁ M₂ halt
  rw [hEs] at hsgn
  have hcnt : DirMatching.unionCount M₁
        (M₂.map (interfaceSideDisjEquiv F (stepIdent n)
          ((swapPaired_iff_interfacePaired F
            (stepIdent n)).mp hp)).symm)
      = DirMatching.unionCount (cutMatching (leftSub F) κ₁ o₁)
        ((cutMatching (rightSub F) κ₂ o₂).map
          (interfaceSideDisjEquiv F (stepIdent n)
            ((swapPaired_iff_interfacePaired F
              (stepIdent n)).mp hp)).symm) :=
    DirMatching.unionCount_congr hM₁
      (DirMatching.map_edge_congr _ hM₂)
  rw [openCircuitCount_glueData n (W₁.disjUnion W₂)
      ⟨F, hp, prodRel κ₁ κ₂⟩,
    stageLedger_disjUnion n F hp κ₁ κ₂ o₁ o₂, pow_add, pow_add,
    ← hcnt, ← hsgn, mul_mul_mul_comm]
  exact mul_comm _ _

end EdgeSubset

end RS
