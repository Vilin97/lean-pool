/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.GluePathMatch
import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueCrossDelta
import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseDischarge
import LeanPool.RegtsSevenster.RS.Novel.Skein.PropThreeOpen

/-!
# Path data across a closed glue

A closed glue never rewires: the cut edge is the single edge joining
the two boundary flags, so a chain of the glued system transports to
the unglued one on the nose.  The three transports here say so —
which flags are boundary after the glue, that the walk agrees step
for step, and that the path matching is carried across unchanged.
-/

namespace RS

open scoped Classical
open Fragment

namespace EdgeSubset

variable {α : Type} {W : Fragment α}

/-! ## Generic helpers -/

/-- Exit steps of boundary-terminated chain data agree. -/
private theorem exit_unique_chain {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) {g : W.Flag} {n n' : ℕ}
    (hcont : ∀ t, t < n →
      W.pairing (iterWalk κ g t) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ g n) ∈ F.boundaryFlags)
    (hcont' : ∀ t, t < n' →
      W.pairing (iterWalk κ g t) ∈ F.internalFlags)
    (hterm' : W.pairing (iterWalk κ g n') ∈ F.boundaryFlags) :
    n = n' := by
  rcases Nat.lt_trichotomy n n' with h | h | h
  · exact absurd hterm
      (Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags (hcont' n h))
  · exact h
  · exact absurd hterm'
      (Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags (hcont n' h))

/-- `pathMatch` equals the terminal pairing of any
boundary-terminated chain data. -/
private theorem pathMatch_eq_of_chainData {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) {g : W.Flag}
    (hg : g ∈ F.boundaryFlags) {n : ℕ}
    (hcont : ∀ t, t < n →
      W.pairing (iterWalk κ g t) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ g n) ∈ F.boundaryFlags) :
    κ.pathMatch g hg = W.pairing (iterWalk κ g n) := by
  obtain ⟨n₀, -, hcont₀, hpm₀⟩ := pathMatch_chain_length κ hg
  have hterm₀ : W.pairing (iterWalk κ g n₀) ∈ F.boundaryFlags := by
    rw [← hpm₀]
    exact κ.pathMatch_mem hg
  rw [hpm₀, exit_unique_chain κ hcont hterm hcont₀ hterm₀]

/-! ## The closed path-data engine (either `b`) -/

section ClosedPathData

variable {i j : α}
  (hij : i ≠ j)
  (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (b : Bool)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetClosed s' b,
    W.pairing f ∈ liftSubsetClosed s' b)
  (κ' : (EdgeSubset.mk s' hc' : EdgeSubset
    (W.gluePairClosed i j hclosed)).RelTransitionSystem)
  (o' : κ'.Orientation)

/-- The glued edge subset. -/
local notation "Fg" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

/-- The lifted edge subset. -/
local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetClosed s' b) hc : EdgeSubset W)

local notation "κW" =>
  RelTransitionSystem.unglueClosed hclosed b s' hc' hc κ'

local notation "oW" =>
  unglueOrientationClosed hclosed b s' hc' hc κ' o'

/-- **Boundary-flag correspondence (closed case)**: a surviving
flag is glued-boundary iff its value is lifted-boundary. -/
theorem mem_boundaryFlags_glueClosed {f' : SurvivingFlag W i j} :
    f' ∈ (Fg).boundaryFlags ↔ f'.val ∈ (Fl).boundaryFlags := by
  constructor
  · intro h
    have hf : f'.val ∈ (Fl).flags :=
      (surviving_val_mem_liftClosed_iff s' b f').mpr
        (mem_flags_of_boundaryFlags _ h)
    rcases mem_internalFlags_or_boundaryFlags (Fl) hf with hint | hbd
    · exact absurd h
        (Finset.disjoint_left.mp
          ((Fg).internalFlags_disjoint_boundaryFlags)
          ((mem_internalFlags_glueClosed hclosed b s' hc' hc).mpr
            hint))
    · exact hbd
  · intro h
    have hf : f' ∈ (Fg).flags :=
      (surviving_val_mem_liftClosed_iff s' b f').mp
        (mem_flags_of_boundaryFlags _ h)
    rcases mem_internalFlags_or_boundaryFlags (Fg) hf with hint | hbd
    · exact absurd h
        (Finset.disjoint_left.mp
          ((Fl).internalFlags_disjoint_boundaryFlags)
          ((mem_internalFlags_glueClosed hclosed b s' hc' hc).mp
            hint))
    · exact hbd

/-- **Unconditional walk agreement (closed case)**: the closed glue
never rewires, so the unglued walk from a surviving flag follows
the glued walk valuewise, with no continuation hypothesis. -/
theorem iterWalk_unglueClosed_val_all (δ' : SurvivingFlag W i j) :
    ∀ t, iterWalk (κW) δ'.val t = (iterWalk κ' δ' t).val := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show (κW).match_ (W.pairing (iterWalk (κW) δ'.val t)) =
      (κ'.match_ ((W.gluePairClosed i j hclosed).pairing
        (iterWalk κ' δ' t))).val
    rw [ih]
    exact unglueClosed_match_of_surviving hclosed b s' hc' hc κ'
      (W.pairing (iterWalk κ' δ' t).val)
      (pairing_val_surviving_closed hclosed (iterWalk κ' δ' t))

/-- **`pathMatch` transport across the closed unglue**: chains of
surviving boundary flags transport on the nose, for either `b`. -/
theorem pathMatch_unglueClosed {δ' : SurvivingFlag W i j}
    (hδ' : δ' ∈ (Fg).boundaryFlags)
    (hδl : δ'.val ∈ (Fl).boundaryFlags) :
    (κW).pathMatch δ'.val hδl = (κ'.pathMatch δ' hδ').val := by
  -- ═══════ THE GLUED CHAIN IS THE BASE CHAIN ═══════
  -- A closed cut adds a circle and touches no walk, so the chain
  -- of a surviving flag runs identically on both sides.
  obtain ⟨n, -, hcont, hpm⟩ := pathMatch_chain_length κ' hδ'
  have hwalk := iterWalk_unglueClosed_val_all hclosed b s' hc' hc
    κ' δ'
  have hcontW : ∀ t, t < n →
      W.pairing (iterWalk (κW) δ'.val t) ∈ (Fl).internalFlags := by
    intro t ht
    rw [hwalk t]
    exact internal_val_of_glueClosed hclosed b s' hc' hc
      (hcont t ht)
  have htermW : W.pairing (iterWalk (κW) δ'.val n) ∈
      (Fl).boundaryFlags := by
    rw [hwalk n]
    have hbg : (W.gluePairClosed i j hclosed).pairing
        (iterWalk κ' δ' n) ∈ (Fg).boundaryFlags := by
      rw [← hpm]
      exact κ'.pathMatch_mem hδ'
    exact (mem_boundaryFlags_glueClosed hclosed b s' hc'
      hc).mp hbg
  rw [pathMatch_eq_of_chainData (κW) hδl hcontW htermW, hwalk n,
    hpm]
  exact (gluePairClosed_pairing_val hclosed
    (iterWalk κ' δ' n)).symm

end ClosedPathData

/-! ## The non-participating lift (`b = false`): chord diagram,
path sign, and the signed-value transport -/

section ClosedFalse

variable {i j : α}
  (hij : i ≠ j)
  (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hcF : ∀ f ∈ liftSubsetClosed s' false,
    W.pairing f ∈ liftSubsetClosed s' false)
  (κ' : (EdgeSubset.mk s' hc' : EdgeSubset
    (W.gluePairClosed i j hclosed)).RelTransitionSystem)
  (o' : κ'.Orientation)

local notation "Fg" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

local notation "FlF" =>
  (EdgeSubset.mk (liftSubsetClosed s' false) hcF : EdgeSubset W)

local notation "κWF" =>
  RelTransitionSystem.unglueClosed hclosed false s' hc' hcF κ'

local notation "oWF" =>
  unglueOrientationClosed hclosed false s' hc' hcF κ' o'

end ClosedFalse

/-! ## The participating lift (`b = true`): the signed-value
transport with explicit sign weight -/

section ClosedTrue

variable {i j : α}
  (hij : i ≠ j)
  (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hcT : ∀ f ∈ liftSubsetClosed s' true,
    W.pairing f ∈ liftSubsetClosed s' true)
  (κ' : (EdgeSubset.mk s' hc' : EdgeSubset
    (W.gluePairClosed i j hclosed)).RelTransitionSystem)
  (o' : κ'.Orientation)

local notation "Fg" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

local notation "FlT" =>
  (EdgeSubset.mk (liftSubsetClosed s' true) hcT : EdgeSubset W)

local notation "κWT" =>
  RelTransitionSystem.unglueClosed hclosed true s' hc' hcT κ'

local notation "oWT" =>
  unglueOrientationClosed hclosed true s' hc' hcT κ' o'

end ClosedTrue

/-! ## The assembled per-subset split -/

section ClosedAssembly

variable {i j : α}
  (hij : i ≠ j)
  (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hcF : ∀ f ∈ liftSubsetClosed s' false,
    W.pairing f ∈ liftSubsetClosed s' false)
  (hcT : ∀ f ∈ liftSubsetClosed s' true,
    W.pairing f ∈ liftSubsetClosed s' true)
  (κ' : (EdgeSubset.mk s' hc' : EdgeSubset
    (W.gluePairClosed i j hclosed)).RelTransitionSystem)
  (o' : κ'.Orientation)

local notation "Fg" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

local notation "FlF" =>
  (EdgeSubset.mk (liftSubsetClosed s' false) hcF : EdgeSubset W)

local notation "FlT" =>
  (EdgeSubset.mk (liftSubsetClosed s' true) hcT : EdgeSubset W)

local notation "κWF" =>
  RelTransitionSystem.unglueClosed hclosed false s' hc' hcF κ'

local notation "κWT" =>
  RelTransitionSystem.unglueClosed hclosed true s' hc' hcT κ'

end ClosedAssembly

end EdgeSubset

end RS
