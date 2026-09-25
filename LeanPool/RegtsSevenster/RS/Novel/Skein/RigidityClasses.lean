/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinCatInstance
import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeRelabel

/-!
# The rigidity classes of the skein category

The evaluation and coevaluation classes — the single strand read
as a `(2,0)`- or `(0,2)`-fragment — together with the braiding
class on two strands, and the supersymmetry of the evaluation:
precomposing the evaluation with the braiding (or postcomposing
the coevaluation) is absorbed, because the strand is symmetric
under any boundary relabelling.  These are the data that the
Deligne fibre functor sends to the standard form and copairing.
-/

namespace RS

/-- The strand is invariant under every boundary relabelling: any
permutation of `Fin 2` commutes with the end swap. -/
noncomputable def strandRelabelEquiv (e : Fin 2 ≃ Fin 2) :
    (Fragment.strand.relabel e).Equiv Fragment.strand where
  flagEquiv := e
  vertexEquiv := _root_.Equiv.refl Empty
  attach_comm := fun g => by
    change Sum.inr (e g) =
      ((Sum.inr (e g) : Empty ⊕ Fin 2).map
        (_root_.Equiv.refl Empty) id)
    rfl
  pairing_comm := fun g => by
    change e ⟨1 - g.val, by omega⟩ = ⟨1 - (e g).val, by omega⟩
    set x := (⟨1 - g.val, by omega⟩ : Fin 2) with hx
    have hxv : x.val = 1 - g.val := congrArg Fin.val hx
    have hne : x ≠ g := by
      intro he
      have hv : x.val = g.val := congrArg Fin.val he
      have := g.isLt
      omega
    have hnev : (e x).val ≠ (e g).val :=
      fun hv => hne (e.injective (Fin.ext hv))
    have h1 : (e x).val < 2 := (e x).isLt
    have h2 : (e g).val < 2 := (e g).isLt
    refine Fin.ext ?_
    change (e x).val = 1 - (e g).val
    omega
  circles_eq := rfl

/-- The evaluation fragment: the strand as a `(2,0)`-morphism. -/
noncomputable def evFrag : Fragment (Fin (2 + 0)) :=
  Fragment.strand.relabel (finCongr (by omega : 2 = 2 + 0))

/-- The coevaluation fragment: the strand as a `(0,2)`-morphism. -/
noncomputable def coevFrag : Fragment (Fin (0 + 2)) :=
  Fragment.strand.relabel (finCongr (by omega : 2 = 0 + 2))

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The evaluation class. -/
noncomputable def evClass : HomSpace f.val (2 + 0) :=
  HomSpace.ofFragment f.val evFrag

/-- The coevaluation class. -/
noncomputable def coevClass : HomSpace f.val (0 + 2) :=
  HomSpace.ofFragment f.val coevFrag

/-- The braiding class on two strands. -/
noncomputable def braidClass : HomSpace f.val (2 + 2) :=
  HomSpace.ofFragment f.val
    (permFragment (_root_.Equiv.swap (0 : Fin 2) 1))

/-- **Supersymmetry of the evaluation**: the braiding is absorbed
by the evaluation class. -/
theorem braid_comp_evClass :
    HomSpace.comp f 2 2 0 (braidClass f) (evClass f) =
      evClass f := by
  rw [braidClass, evClass, HomSpace.comp_ofFragment]
  refine HomSpace.ofFragment_congr f ?_
  refine (permFragmentComposeLeft
    (_root_.Equiv.swap (0 : Fin 2) 1) evFrag).trans ?_
  refine (Fragment.Equiv.relabelTrans Fragment.strand _ _).trans
    ?_
  exact (strandRelabelEquiv _).trans
    (strandRelabelEquiv _).symm

end RS
