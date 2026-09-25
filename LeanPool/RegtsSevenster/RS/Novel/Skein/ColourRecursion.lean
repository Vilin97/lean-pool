/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.EdgeTerm
import LeanPool.RegtsSevenster.RS.Novel.Skein.CutSubsetSum

/-!
# Iterating the glue

RS21's `∗` glues every interface pair at once; `glueInterface` glues
them one at a time, top pair first, relabelling the survivors at each
stage.  This file carries RS21's summand along that iteration: the
per-cut identities of `EdgeTerm` are the step, and the transports
below are the bookkeeping the staging needs — the relabel at each
stage and at the base, and the dispatch on whether the stage's cut
closes.
-/

namespace RS

namespace EdgeSubset

open Fragment
/-! ## The base of the iteration

At an empty interface the composition still relabels, between two
label types that are both empty.
-/

/-- The order isomorphism the base stage relabels along. -/
noncomputable def baseIso :
    @OrderIso (Fin (0 + 0) ⊕ Fin (0 + 0)) (Fin 0 ⊕ Fin 0)
      (sumLexLE (Fin (0 + 0)) (Fin (0 + 0)))
      (sumLexLE (Fin 0) (Fin 0)) where
  toEquiv :=
    Equiv.sumCongr (finCongr (by omega)) (finCongr (by omega))
  map_rel_iff' := by
    rintro (x | x) <;> exact absurd x.isLt (by omega)

/-! ## Transporting a family along an equality of fragments

The stage's glue dispatches on whether the cut closes, and each
branch is built over its own fragment; the finished family is carried
back across that identification.
-/

/-- Transport a set of flags along an equality of fragments. -/
noncomputable def flagsOfEq {β : Type} (V₁ V₂ : Fragment β)
    (hV : V₁ = V₂) (s : Finset V₁.Flag) : Finset V₂.Flag := by
  subst hV; exact s

section DataEq

variable {β : Type}

/-- Transport a data family along an equality of fragments. -/
noncomputable def dataOfEq
    [LinearOrder β] {V₁ : Fragment β} {V₂ : Fragment β} (hV : V₁ = V₂)
    (𝒟 : DataFamily V₂) : DataFamily V₁ := by
  subst hV; exact 𝒟

/-- The summand reads the transported family on the transported
subset. -/
theorem edgeTermAt_dataOfEq
    [LinearOrder β] {V₁ : Fragment β} {V₂ : Fragment β} (hV : V₁ = V₂)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (𝒟 : DataFamily V₂) (st : GenBoundaryState k ℓ β)
    (s : Finset V₁.Flag) (C : ℕ) :
    edgeTermAt h (dataOfEq hV 𝒟) st s C
      = edgeTermAt h 𝒟 st (flagsOfEq V₁ V₂ hV s) C := by
  subst hV
  rfl

end DataEq

/-! ## One stage of the iteration

The stage glues the top interface pair and relabels the survivors.
Its data family therefore comes back in two moves: pull along the
relabel, then unglue.
-/

section Step

/-- The lexicographic order on the stage's label type. -/
@[reducible] local instance recOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

/-- The same order one stage up. -/
@[reducible] local instance recOrderSucc (n : ℕ) :
    LinearOrder (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) :=
  sumLexLinearOrder _ _

/-- The order the surviving labels of a stage carry. -/
@[reducible] local instance recSurvOrder (n : ℕ) :
    LinearOrder (SurvivingLabel (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0))
      (cutL n) (cutR n)) :=
  sumLexSubtypeLinearOrder (Fin (0 + n + 1)) (Fin (n + 1 + 0)) _

variable (n : ℕ)
  (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))

/-- The stage's family, pulled back along the relabel. -/
noncomputable def stepDataGlued (𝒟 : DataFamily (stepFragment n V)) :
    DataFamily (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n)) :=
  relabelDataDown (stepIso n) 𝒟

/-- The stage's glue, at a closing cut. -/
theorem gluePair_eq_closed (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) :
    V.gluePairClosed (cutL n) (cutR n) hcl
      = V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n) := by
  unfold Fragment.gluePair
  rw [dite_eq_left hcl]

/-- The stage's glue, at an open cut. -/
theorem gluePair_eq_open (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) :
    V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop
      = V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n) := by
  unfold Fragment.gluePair
  rw [dite_eq_right hop]

/-- **One stage of the composition, on the data.**  The family is
chosen at the composition and pushed back: along the relabel, then
across the glue. -/
noncomputable def stepDataDown (𝒟 : DataFamily (stepFragment n V)) :
    DataFamily V :=
  if hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n) then
    unglueDataClosed (cutL_ne_cutR n) hcl
      (dataOfEq (gluePair_eq_closed n V hcl) (stepDataGlued n V 𝒟))
  else
    unglueDataOpen (cutL_ne_cutR n) hcl
      (dataOfEq (gluePair_eq_open n V hcl) (stepDataGlued n V 𝒟))

/-- The stage's state, read back through the relabel. -/
noncomputable def stageState {k ℓ : ℕ}
    (stβ : GenBoundaryState k ℓ (Fin (0 + n) ⊕ Fin (n + 0))) :
    GenBoundaryState k ℓ
      (SurvivingLabel (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0))
        (cutL n) (cutR n)) :=
  fun a => stβ (stepIso n a)

open Classical in
/-- **One open stage, with nothing assumed of the subset.** -/
theorem edgeTermAt_stepOpen_all {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (𝒟 : DataFamily (stepFragment n V))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (t : Finset (SurvivingFlag V (cutL n) (cutR n)))
    (stβ : GenBoundaryState k ℓ (Fin (0 + n) ⊕ Fin (n + 0)))
    (C : ℕ) :
    (∑ c : Fin k ⊕ Fin (2 * ℓ),
        edgeTermAt h (stepDataDown n V 𝒟)
          (GenBoundaryState.extendPair (cutL n) (cutR n)
            (stageState n stβ) c c)
          (liftSubsetOpen hop t) C)
      = edgeTermAt h 𝒟 stβ
        (flagsOfEq
          (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_open n V hop) t) C := by
  have hstep : stepDataDown n V 𝒟
      = unglueDataOpen (cutL_ne_cutR n) hop
        (dataOfEq (gluePair_eq_open n V hop)
          (stepDataGlued n V 𝒟)) := by
    unfold stepDataDown
    rw [dite_eq_right hop]
  rw [hstep, edgeTermAt_openCut_all (cutL_ne_cutR n) hop t h _
      (stageState n stβ) C,
    edgeTermAt_dataOfEq (gluePair_eq_open n V hop) h
      (stepDataGlued n V 𝒟) (stageState n stβ) t C]
  exact (edgeTermAt_relabel (stepIso n) h 𝒟 stβ
    (flagsOfEq
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_open n V hop) t) C).symm

open Classical in
/-- **The empty branch of a closing stage weighs `k`**, with nothing
assumed of the subset. -/
theorem edgeTermAt_stepClosed_false_all {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (𝒟 : DataFamily (stepFragment n V))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (t : Finset (SurvivingFlag V (cutL n) (cutR n)))
    (stβ : GenBoundaryState k ℓ (Fin (0 + n) ⊕ Fin (n + 0)))
    (C : ℕ) :
    (∑ c : Fin k ⊕ Fin (2 * ℓ),
        edgeTermAt h (stepDataDown n V 𝒟)
          (GenBoundaryState.extendPair (cutL n) (cutR n)
            (stageState n stβ) c c)
          (liftSubsetClosed t false) C)
      = (k : ℂ) *
        edgeTermAt h 𝒟 stβ
          (flagsOfEq
            (V.gluePairClosed (cutL n) (cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_closed n V hcl) t) C := by
  have hstep : stepDataDown n V 𝒟
      = unglueDataClosed (cutL_ne_cutR n) hcl
        (dataOfEq (gluePair_eq_closed n V hcl)
          (stepDataGlued n V 𝒟)) := by
    unfold stepDataDown
    rw [dite_eq_left hcl]
  rw [hstep, edgeTermAt_closedCut_false_row_all (cutL_ne_cutR n) hcl
      t h _ (stageState n stβ) C,
    edgeTermAt_dataOfEq (gluePair_eq_closed n V hcl) h
      (stepDataGlued n V 𝒟) (stageState n stβ) t C]
  exact congrArg (fun z => (k : ℂ) * z)
    (edgeTermAt_relabel (stepIso n) h 𝒟 stβ
      (flagsOfEq
        (V.gluePairClosed (cutL n) (cutR n) hcl)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_closed n V hcl) t) C).symm

open Classical in
/-- **The carried branch of a closing stage weighs `−2ℓ`**, with
nothing assumed of the subset. -/
theorem edgeTermAt_stepClosed_true_all {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (𝒟 : DataFamily (stepFragment n V))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (t : Finset (SurvivingFlag V (cutL n) (cutR n)))
    (stβ : GenBoundaryState k ℓ (Fin (0 + n) ⊕ Fin (n + 0)))
    (C : ℕ) :
    (∑ c : Fin k ⊕ Fin (2 * ℓ),
        edgeTermAt h (stepDataDown n V 𝒟)
          (GenBoundaryState.extendPair (cutL n) (cutR n)
            (stageState n stβ) c c)
          (liftSubsetClosed t true) (C + 1))
      = (-(2 * ℓ : ℕ) : ℂ) *
        edgeTermAt h 𝒟 stβ
          (flagsOfEq
            (V.gluePairClosed (cutL n) (cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_closed n V hcl) t) C := by
  have hstep : stepDataDown n V 𝒟
      = unglueDataClosed (cutL_ne_cutR n) hcl
        (dataOfEq (gluePair_eq_closed n V hcl)
          (stepDataGlued n V 𝒟)) := by
    unfold stepDataDown
    rw [dite_eq_left hcl]
  rw [hstep, edgeTermAt_closedCut_true_row_all (cutL_ne_cutR n) hcl
      t h _ (stageState n stβ) C,
    edgeTermAt_dataOfEq (gluePair_eq_closed n V hcl) h
      (stepDataGlued n V 𝒟) (stageState n stβ) t C]
  exact congrArg (fun z => (-(2 * ℓ : ℕ) : ℂ) * z)
    (edgeTermAt_relabel (stepIso n) h 𝒟 stβ
      (flagsOfEq
        (V.gluePairClosed (cutL n) (cutR n) hcl)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_closed n V hcl) t) C).symm

open Classical in
/-- **One closing stage, with nothing assumed of the subset.** -/
theorem edgeTermAt_stepClosed_all {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (𝒟 : DataFamily (stepFragment n V))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (t : Finset (SurvivingFlag V (cutL n) (cutR n)))
    (stβ : GenBoundaryState k ℓ (Fin (0 + n) ⊕ Fin (n + 0)))
    (C : ℕ) :
    (∑ c : Fin k ⊕ Fin (2 * ℓ),
        edgeTermAt h (stepDataDown n V 𝒟)
          (GenBoundaryState.extendPair (cutL n) (cutR n)
            (stageState n stβ) c c)
          (liftSubsetClosed t false) C)
      + (∑ c : Fin k ⊕ Fin (2 * ℓ),
          edgeTermAt h (stepDataDown n V 𝒟)
            (GenBoundaryState.extendPair (cutL n) (cutR n)
              (stageState n stβ) c c)
            (liftSubsetClosed t true) (C + 1))
      = ((k : ℂ) - 2 * ℓ) *
        edgeTermAt h 𝒟 stβ
          (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_closed n V hcl) t) C := by
  have hstep : stepDataDown n V 𝒟
      = unglueDataClosed (cutL_ne_cutR n) hcl
        (dataOfEq (gluePair_eq_closed n V hcl)
          (stepDataGlued n V 𝒟)) := by
    unfold stepDataDown
    rw [dite_eq_left hcl]
  rw [hstep, edgeTermAt_closedCut_all (cutL_ne_cutR n) hcl t h _
      (stageState n stβ) C,
    edgeTermAt_dataOfEq (gluePair_eq_closed n V hcl) h
      (stepDataGlued n V 𝒟) (stageState n stβ) t C]
  exact congrArg (fun z => ((k : ℂ) - 2 * ℓ) * z)
    (edgeTermAt_relabel (stepIso n) h 𝒟 stβ
      (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_closed n V hcl) t) C).symm

end Step

/-! ## The iteration

The family is chosen at the composition and pushed back stage by
stage; the count the base is read at rises by one at each closing cut
whose edge the subset carries, which is the ledger's `glueCount`.
-/

section Iterate

/-- The lexicographic order on the stage's label type. -/
@[reducible] local instance iterOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

/-- The same order one stage up. -/
@[reducible] local instance iterOrderSucc (n : ℕ) :
    LinearOrder (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) :=
  sumLexLinearOrder _ _

/-- The order the composition's own (empty) label type carries. -/
@[reducible] local instance closureOrder :
    LinearOrder (Fin 0 ⊕ Fin 0) :=
  sumLexLinearOrder _ _

/-- **The family, pushed back to the base.**  A choice at the
composition determines one at every stage, by ungluing. -/
noncomputable def pushData : (n : ℕ) →
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) →
    DataFamily (glueInterface 0 n 0 V) → DataFamily V
  | 0, _, 𝒟 => relabelDataDown baseIso 𝒟
  | n + 1, V, 𝒟 =>
      stepDataDown n V (pushData n (stepFragment n V) 𝒟)

open Classical in
/-- **The closing cuts a subset carries.**  This is the ledger's
`glueCount`, read on the colouring side: the count the base's summand
is taken at rises by one at each of them. -/
noncomputable def carried : (n : ℕ) →
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) →
    Finset V.Flag → ℕ
  | 0, _, _ => 0
  | n + 1, V, s =>
      if hcl : V.pairing (V.boundaryFlag (cutL n))
          = V.boundaryFlag (cutR n) then
        (if V.boundaryFlag (cutL n) ∈ s then 1 else 0)
          + carried n (stepFragment n V)
            (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_closed n V hcl)
              (V.dropSubset (cutL n) (cutR n) s))
      else
        carried n (stepFragment n V)
          (flagsOfEq
            (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_open n V hcl)
            (V.dropSubset (cutL n) (cutR n) s))

/-- **The diagonal interface state**: both ends of a cut carry the
colour the composition gives it. -/
noncomputable def diagOf {k ℓ : ℕ} (n : ℕ)
    (x : Fin n → (Fin k ⊕ Fin (2 * ℓ))) :
    GenBoundaryState k ℓ (Fin (0 + n) ⊕ Fin (n + 0)) :=
  Sum.elim (fun a => x (Fin.cast (by omega) a))
    (fun b => x (Fin.cast (by omega) b))

/-- **The diagonal state, one stage down.**  Its top colour is the
stage's cut colour, and the rest is the next stage's diagonal
state. -/
theorem diagOf_succ {k ℓ : ℕ} (n : ℕ)
    (x : Fin (n + 1) → (Fin k ⊕ Fin (2 * ℓ))) :
    diagOf (n + 1) x
      = GenBoundaryState.extendPair (cutL n) (cutR n)
          (stageState n (diagOf n (fun a => x a.castSucc)))
          (x (Fin.last n)) (x (Fin.last n)) := by
  funext y
  by_cases hL : y = cutL n
  · subst hL
    rw [GenBoundaryState.extendPair_left]
    exact congrArg x (Fin.ext (by simp))
  · by_cases hR : y = cutR n
    · subst hR
      rw [GenBoundaryState.extendPair_right (cutL_ne_cutR n)]
      exact congrArg x (Fin.ext (by simp))
    · rw [GenBoundaryState.extendPair_surviving
        (st := stageState n (diagOf n (fun a => x a.castSucc)))
        (c := x (Fin.last n)) (c' := x (Fin.last n))
        (a := ⟨y, hL, hR⟩)]
      change _ = diagOf n (fun a => x a.castSucc)
        (interfaceStepEquiv 0 n 0 ⟨y, hL, hR⟩)
      rcases y with v | w
      · rw [interfaceStepEquiv_apply_inl 0 n 0 v ⟨hL, hR⟩]
        refine congrArg x (Fin.ext ?_)
        change (v : ℕ) = _
        rw [Fin.val_castSucc, Fin.val_cast]
        exact (finRemoveEquiv_top_val (n := 0 + n)
          ⟨v, fun he => hL (congrArg Sum.inl he)⟩).symm
      · rw [interfaceStepEquiv_apply_inr 0 n 0 w ⟨hL, hR⟩]
        refine congrArg x (Fin.ext ?_)
        change (w : ℕ) = _
        rw [Fin.val_castSucc, Fin.val_cast, rightRemoveEquiv_val]
        have hw : (w : ℕ) ≠ n := fun hx => hR (congrArg Sum.inr
          (Fin.ext hx))
        have hlt : (w : ℕ) < n := by omega
        rw [ite_eq_left hlt]

open Classical in
/-- **The carried count at an open stage** is the next stage's. -/
theorem carried_liftOpen (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (t : Finset (SurvivingFlag V (cutL n) (cutR n))) :
    carried (n + 1) V
        (liftSubsetOpen hop t)
      = carried n (stepFragment n V)
        (flagsOfEq
          (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_open n V hop) t) := by
  change (if hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n) then _ else _) = _
  rw [dite_eq_right hop]
  exact congrArg (fun z => carried n (stepFragment n V)
    (flagsOfEq
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_open n V hop) z))
    (dropSubset_liftSubsetOpen hop t)

open Classical in
/-- **The carried count at a closing stage** rises by one exactly
when the subset carries the closed edge. -/
theorem carried_liftClosed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (t : Finset (SurvivingFlag V (cutL n) (cutR n))) (b : Bool) :
    carried (n + 1) V (liftSubsetClosed t b)
      = (if b = true then 1 else 0)
        + carried n (stepFragment n V)
          (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_closed n V hcl) t) := by
  change (if hc : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n) then _ else _) = _
  rw [dite_eq_left hcl]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact if_congr
      (boundaryFlagI_mem_liftClosed_iff (cutL_ne_cutR n) t b) rfl
      rfl
  · exact congrArg (fun z => carried n (stepFragment n V)
      (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_closed n V hcl) z))
      (dropSubset_liftSubsetClosed t b)

/-- The composition's own state: its label type is empty. -/
noncomputable def emptyState {k ℓ : ℕ} :
    GenBoundaryState k ℓ (Fin 0 ⊕ Fin 0) := fun a => isEmptyElim a

/-- The interface colours, split off the last cut. -/
def snocEquiv (n : ℕ) (α : Type) :
    ((Fin n → α) × α) ≃ (Fin (n + 1) → α) where
  toFun p := Fin.snoc p.1 p.2
  invFun x := (fun a => x a.castSucc, x (Fin.last n))
  left_inv p := by
    refine Prod.ext (funext fun a => ?_) ?_ <;> simp
  right_inv x := by
    funext a
    refine Fin.lastCases ?_ ?_ a <;> simp

/-- **The interface colour sum, one cut at a time.** -/
theorem sum_snoc {n : ℕ} {α : Type} [Fintype α]
    (F : (Fin (n + 1) → α) → ℂ) :
    (∑ x : Fin (n + 1) → α, F x)
      = ∑ y : Fin n → α, ∑ c : α, F (Fin.snoc y c) := by
  rw [← Fintype.sum_equiv (snocEquiv n α) (fun p => F (Fin.snoc p.1 p.2))
    F (fun _ => rfl), Fintype.sum_prod_type]

open Classical in
/-- **The composition's subset a stage's subset maps to.** -/
noncomputable def imageOf : (n : ℕ) →
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) →
    Finset V.Flag → Finset (glueInterface 0 n 0 V).Flag
  | 0, _, s => s
  | n + 1, V, s =>
      if hcl : V.pairing (V.boundaryFlag (cutL n))
          = V.boundaryFlag (cutR n) then
        imageOf n (stepFragment n V)
          (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_closed n V hcl)
            (V.dropSubset (cutL n) (cutR n) s))
      else
        imageOf n (stepFragment n V)
          (flagsOfEq
            (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_open n V hcl)
            (V.dropSubset (cutL n) (cutR n) s))

open Classical in
/-- The image, one stage down, at an open cut. -/
theorem imageOf_succ_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) (s : Finset V.Flag) :
    imageOf (n + 1) V s
      = imageOf n (stepFragment n V)
        (flagsOfEq
          (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_open n V hop)
          (V.dropSubset (cutL n) (cutR n) s)) := by
  change (if hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n) then _ else _) = _
  exact dite_eq_right hop

open Classical in
/-- The image, one stage down, at a closing cut. -/
theorem imageOf_succ_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) (s : Finset V.Flag) :
    imageOf (n + 1) V s
      = imageOf n (stepFragment n V)
        (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_closed n V hcl)
          (V.dropSubset (cutL n) (cutR n) s)) := by
  change (if hc : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n) then _ else _) = _
  exact dite_eq_left hcl

/-- Sums over the flags of identified fragments agree. -/
theorem sum_flagsOfEq {β : Type} {V₁ V₂ : Fragment β}
    (hV : V₁ = V₂) (F : Finset V₂.Flag → ℂ) :
    (∑ s : Finset V₂.Flag, F s)
      = ∑ s : Finset V₁.Flag, F (flagsOfEq V₁ V₂ hV s) := by
  subst hV
  rfl

open Classical in
/-- The stage's sum, with the interface colour split off. -/
theorem stageSum_snoc {k ℓ : ℕ} (h : MixedFunctional k ℓ) (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (𝒟 : DataFamily (stepFragment n V)) (C : ℕ)
    (W : Finset V.Flag → ℂ) :
    (∑ s : Finset V.Flag,
        ∑ x : Fin (n + 1) → (Fin k ⊕ Fin (2 * ℓ)),
          W s * edgeTermAt h (stepDataDown n V 𝒟)
            (diagOf (n + 1) x) s (C + carried (n + 1) V s))
      = ∑ y : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
          ∑ s : Finset V.Flag, ∑ c : Fin k ⊕ Fin (2 * ℓ),
            W s * edgeTermAt h (stepDataDown n V 𝒟)
              (GenBoundaryState.extendPair (cutL n) (cutR n)
                (stageState n (diagOf n y)) c c) s
              (C + carried (n + 1) V s) := by
  have hs : ∀ s : Finset V.Flag,
      (∑ x : Fin (n + 1) → (Fin k ⊕ Fin (2 * ℓ)),
        W s * edgeTermAt h (stepDataDown n V 𝒟)
          (diagOf (n + 1) x) s (C + carried (n + 1) V s))
        = ∑ y : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
            ∑ c : Fin k ⊕ Fin (2 * ℓ),
              W s * edgeTermAt h (stepDataDown n V 𝒟)
                (GenBoundaryState.extendPair (cutL n) (cutR n)
                  (stageState n (diagOf n y)) c c) s
                (C + carried (n + 1) V s) := by
    intro s
    rw [sum_snoc]
    refine Finset.sum_congr rfl (fun y _ =>
      Finset.sum_congr rfl (fun c _ => ?_))
    refine congrArg (fun st => W s * edgeTermAt h
      (stepDataDown n V 𝒟) st s (C + carried (n + 1) V s)) ?_
    rw [diagOf_succ]
    simp
  rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => hs s),
    Finset.sum_comm]

open Classical in
/-- **The free circles a subset's own cuts contribute.**  At an open
cut, nothing; at a closing cut, `k` if the subset leaves the cut's
edge out and `−2ℓ` if it carries it — the free circle's two sectors,
read one subset at a time. -/
noncomputable def cutFactor (k ℓ : ℕ) : (n : ℕ) →
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) →
    Finset V.Flag → ℂ
  | 0, _, _ => 1
  | n + 1, V, s =>
      if hcl : V.pairing (V.boundaryFlag (cutL n))
          = V.boundaryFlag (cutR n) then
        (if V.boundaryFlag (cutL n) ∈ s then (-(2 * ℓ : ℕ) : ℂ)
            else (k : ℂ))
          * cutFactor k ℓ n (stepFragment n V)
            (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_closed n V hcl)
              (V.dropSubset (cutL n) (cutR n) s))
      else
        cutFactor k ℓ n (stepFragment n V)
          (flagsOfEq
            (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_open n V hcl)
            (V.dropSubset (cutL n) (cutR n) s))

open Classical in
/-- The factor at an open cut is the next stage's. -/
theorem cutFactor_liftOpen (k ℓ : ℕ) (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (t : Finset (SurvivingFlag V (cutL n) (cutR n))) :
    cutFactor k ℓ (n + 1) V (liftSubsetOpen hop t)
      = cutFactor k ℓ n (stepFragment n V)
        (flagsOfEq
          (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_open n V hop) t) := by
  change (if hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n) then _ else _) = _
  rw [dite_eq_right hop]
  exact congrArg (fun z => cutFactor k ℓ n (stepFragment n V)
    (flagsOfEq
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_open n V hop) z))
    (dropSubset_liftSubsetOpen hop t)

open Classical in
/-- The factor at a closing cut: `k` on the empty branch and `−2ℓ`
on the carried one. -/
theorem cutFactor_liftClosed (k ℓ : ℕ) (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (t : Finset (SurvivingFlag V (cutL n) (cutR n))) (b : Bool) :
    cutFactor k ℓ (n + 1) V (liftSubsetClosed t b)
      = (if b = true then (-(2 * ℓ : ℕ) : ℂ) else (k : ℂ))
        * cutFactor k ℓ n (stepFragment n V)
          (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_closed n V hcl) t) := by
  change (if hc : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n) then _ else _) = _
  rw [dite_eq_left hcl]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact if_congr
      (boundaryFlagI_mem_liftClosed_iff (cutL_ne_cutR n) t b) rfl
      rfl
  · exact congrArg (fun z => cutFactor k ℓ n (stepFragment n V)
      (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_closed n V hcl) z))
      (dropSubset_liftSubsetClosed t b)

open Classical in
/-- **A subset's colour sum, one cut at a time.** -/
theorem sum_colours_snoc {k ℓ : ℕ} (h : MixedFunctional k ℓ) (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (𝒟 : DataFamily (stepFragment n V)) (s : Finset V.Flag)
    (C : ℕ) :
    (∑ x : Fin (n + 1) → (Fin k ⊕ Fin (2 * ℓ)),
        edgeTermAt h (stepDataDown n V 𝒟) (diagOf (n + 1) x) s C)
      = ∑ y : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
          ∑ c : Fin k ⊕ Fin (2 * ℓ),
            edgeTermAt h (stepDataDown n V 𝒟)
              (GenBoundaryState.extendPair (cutL n) (cutR n)
                (stageState n (diagOf n y)) c c) s C := by
  rw [sum_snoc]
  refine Finset.sum_congr rfl (fun y _ =>
    Finset.sum_congr rfl (fun c _ => ?_))
  refine congrArg (fun st => edgeTermAt h
    (stepDataDown n V 𝒟) st s C) ?_
  rw [diagOf_succ]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

open Classical in
/-- **An open stage, summed against a weight on the composition's
subsets.** -/
theorem stageSum_open {k ℓ : ℕ} (h : MixedFunctional k ℓ) (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (𝒟 : DataFamily (stepFragment n V))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) (C : ℕ)
    (w : Finset (stepFragment n V).Flag → ℂ) :
    (∑ s : Finset V.Flag,
        ∑ x : Fin (n + 1) → (Fin k ⊕ Fin (2 * ℓ)),
          w (flagsOfEq
              (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
                hop)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_open n V hop)
              (V.dropSubset (cutL n) (cutR n) s))
            * edgeTermAt h (stepDataDown n V 𝒟) (diagOf (n + 1) x)
                s (C + carried (n + 1) V s))
      = ∑ t : Finset (stepFragment n V).Flag,
          ∑ y : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
            w t * edgeTermAt h 𝒟 (diagOf n y) t
              (C + carried n (stepFragment n V) t) := by
  rw [stageSum_snoc h n V 𝒟 C _,
    show (∑ t : Finset (stepFragment n V).Flag,
        ∑ y : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
          w t * edgeTermAt h 𝒟 (diagOf n y) t
            (C + carried n (stepFragment n V) t))
      = ∑ y : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
          ∑ t : Finset (stepFragment n V).Flag,
            w t * edgeTermAt h 𝒟 (diagOf n y) t
              (C + carried n (stepFragment n V) t)
      from Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [sum_split_open (cutL_ne_cutR n) hop
    (fun s => ∑ c : Fin k ⊕ Fin (2 * ℓ),
      w (flagsOfEq
          (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_open n V hop)
          (V.dropSubset (cutL n) (cutR n) s))
        * edgeTermAt h (stepDataDown n V 𝒟)
            (GenBoundaryState.extendPair (cutL n) (cutR n)
              (stageState n (diagOf n y)) c c) s
            (C + carried (n + 1) V s))
    (fun s hs => Finset.sum_eq_zero (fun c _ => by
      rw [edgeTermAt_eq_zero_of_not_closed h _ _ hs _, mul_zero]))]
  refine Eq.trans ?_ (sum_flagsOfEq (gluePair_eq_open n V hop)
    (fun t => w t * edgeTermAt h 𝒟 (diagOf n y) t
      (C + carried n (stepFragment n V) t))).symm
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [dropSubset_liftSubsetOpen hop t,
    carried_liftOpen n V hop t, ← Finset.mul_sum,
    edgeTermAt_stepOpen_all n V h 𝒟 hop t (diagOf n y) _]

open Classical in
/-- **A closing stage, summed against a weight on the composition's
subsets.** -/
theorem stageSum_closed {k ℓ : ℕ} (h : MixedFunctional k ℓ) (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (𝒟 : DataFamily (stepFragment n V))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) (C : ℕ)
    (w : Finset (stepFragment n V).Flag → ℂ) :
    (∑ s : Finset V.Flag,
        ∑ x : Fin (n + 1) → (Fin k ⊕ Fin (2 * ℓ)),
          w (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_closed n V hcl)
              (V.dropSubset (cutL n) (cutR n) s))
            * edgeTermAt h (stepDataDown n V 𝒟) (diagOf (n + 1) x)
                s (C + carried (n + 1) V s))
      = ((k : ℂ) - 2 * ℓ) *
        ∑ t : Finset (stepFragment n V).Flag,
          ∑ y : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
            w t * edgeTermAt h 𝒟 (diagOf n y) t
              (C + carried n (stepFragment n V) t) := by
  rw [stageSum_snoc h n V 𝒟 C _,
    show (∑ t : Finset (stepFragment n V).Flag,
        ∑ y : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
          w t * edgeTermAt h 𝒟 (diagOf n y) t
            (C + carried n (stepFragment n V) t))
      = ∑ y : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
          ∑ t : Finset (stepFragment n V).Flag,
            w t * edgeTermAt h 𝒟 (diagOf n y) t
              (C + carried n (stepFragment n V) t)
      from Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [sum_split_closed (cutL_ne_cutR n) hcl
      (fun s => ∑ c : Fin k ⊕ Fin (2 * ℓ),
        w (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_closed n V hcl)
            (V.dropSubset (cutL n) (cutR n) s))
          * edgeTermAt h (stepDataDown n V 𝒟)
              (GenBoundaryState.extendPair (cutL n) (cutR n)
                (stageState n (diagOf n y)) c c) s
              (C + carried (n + 1) V s))
      (fun s hs => Finset.sum_eq_zero (fun c _ => by
        rw [edgeTermAt_eq_zero_of_not_closed h _ _ hs _, mul_zero])),
    Finset.mul_sum]
  refine Eq.trans ?_ (sum_flagsOfEq (gluePair_eq_closed n V hcl)
    (fun t => ((k : ℂ) - 2 * ℓ) *
      (w t * edgeTermAt h 𝒟 (diagOf n y) t
        (C + carried n (stepFragment n V) t)))).symm
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have hcF := carried_liftClosed n V hcl t false
  have hcT := carried_liftClosed n V hcl t true
  rw [Fintype.sum_bool, dropSubset_liftSubsetClosed t false,
    dropSubset_liftSubsetClosed t true, hcF, hcT]
  have hz : (C + ((if (false : Bool) = true then 1 else 0)
        + carried n (stepFragment n V)
          (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_closed n V hcl) t)))
      = C + carried n (stepFragment n V)
        (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_closed n V hcl) t) := by
    simp
  have ho : (C + ((if (true : Bool) = true then 1 else 0)
        + carried n (stepFragment n V)
          (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_closed n V hcl) t)))
      = (C + carried n (stepFragment n V)
        (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_closed n V hcl) t)) + 1 := by
    simp
    omega
  rw [hz, ho, ← Finset.mul_sum, ← Finset.mul_sum, ← mul_add,
    add_comm (∑ c : Fin k ⊕ Fin (2 * ℓ),
      edgeTermAt h (stepDataDown n V 𝒟)
        (GenBoundaryState.extendPair (cutL n) (cutR n)
          (stageState n (diagOf n y)) c c)
        (liftSubsetClosed t true) _),
    edgeTermAt_stepClosed_all n V h 𝒟 hcl t (diagOf n y) _]
  ring

open Classical in
/-- **The composition's summand, stage by stage.**  RS21's `∗` glues
the whole interface at once; iterating the per-cut identity carries
the composition's summand back to the two fragments, with the free
circles' `k − 2ℓ` in front and the ledger's count on the base's
side.  The weight rides along on the composition's own subsets. -/
theorem edgeTermAt_glueInterface {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) :
    ∀ (n : ℕ) (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0)))
      (𝒟 : DataFamily (glueInterface 0 n 0 V)) (C : ℕ)
      (w : Finset (glueInterface 0 n 0 V).Flag → ℂ),
      ((k : ℂ) - 2 * ℓ) ^ closedCuts n V *
          (∑ s' : Finset (glueInterface 0 n 0 V).Flag,
            w s' * edgeTermAt h 𝒟 emptyState s' C)
        = ∑ s : Finset V.Flag,
            ∑ x : Fin n → (Fin k ⊕ Fin (2 * ℓ)),
              w (imageOf n V s) *
                edgeTermAt h (pushData n V 𝒟) (diagOf n x) s
                  (C + carried n V s)
  | 0, V, 𝒟, C, w => by
      have h0 : closedCuts 0 V = 0 := rfl
      rw [h0, pow_zero, one_mul]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [Fintype.sum_unique]
      refine congrArg (fun z => w s * z) ?_
      refine Eq.trans (edgeTermAt_relabel baseIso h 𝒟 emptyState s C)
        ?_
      exact congrArg
        (fun st => edgeTermAt h (relabelDataDown baseIso 𝒟) st s C)
        (funext fun a => isEmptyElim a)
  | n + 1, V, 𝒟, C, w => by
      have ih := edgeTermAt_glueInterface h n (stepFragment n V) 𝒟 C
        w
      by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
          = V.boundaryFlag (cutR n)
      · have hcc : closedCuts (n + 1) V
            = 1 + closedCuts n (stepFragment n V) := by
          change (if V.pairing (V.boundaryFlag (cutL n))
              = V.boundaryFlag (cutR n) then 1 else 0)
            + closedCuts n (stepFragment n V) = _
          rw [ite_eq_left hcl]
        rw [hcc, pow_add, pow_one, mul_assoc]
        refine Eq.trans (congrArg (fun z => ((k : ℂ) - 2 * ℓ) * z)
          ih) ?_
        refine Eq.trans (stageSum_closed h n V
          (pushData n (stepFragment n V) 𝒟) hcl C
          (fun t => w (imageOf n (stepFragment n V) t))).symm ?_
        refine Finset.sum_congr rfl (fun s _ =>
          Finset.sum_congr rfl (fun x _ => ?_))
        exact congrArg (fun z => z * edgeTermAt h
          (pushData (n + 1) V 𝒟) (diagOf (n + 1) x) s
          (C + carried (n + 1) V s))
          (congrArg w (imageOf_succ_closed n V hcl s).symm)
      · have hcc : closedCuts (n + 1) V
            = closedCuts n (stepFragment n V) := by
          change (if V.pairing (V.boundaryFlag (cutL n))
              = V.boundaryFlag (cutR n) then 1 else 0)
            + closedCuts n (stepFragment n V) = _
          rw [ite_eq_right hcl, Nat.zero_add]
        rw [hcc]
        refine Eq.trans ih ?_
        refine Eq.trans (stageSum_open h n V
          (pushData n (stepFragment n V) 𝒟) hcl C
          (fun t => w (imageOf n (stepFragment n V) t))).symm ?_
        refine Finset.sum_congr rfl (fun s _ =>
          Finset.sum_congr rfl (fun x _ => ?_))
        exact congrArg (fun z => z * edgeTermAt h
          (pushData (n + 1) V 𝒟) (diagOf (n + 1) x) s
          (C + carried (n + 1) V s))
          (congrArg w (imageOf_succ_open n V hcl s).symm)

end Iterate

end EdgeSubset

end RS
