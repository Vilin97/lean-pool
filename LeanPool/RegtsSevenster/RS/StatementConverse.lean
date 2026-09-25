/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.EulerianIndependence

/-!
# The converse statement, assembled

The converse of the Regts–Sevenster theorem: every mixed partition
function has exponentially bounded edge-connection rank, with base
the total dimension `k + 2ℓ`.  This file defines the statement and
assembles it from the Eulerian independence of the Definition 5
value (a theorem, `eulerianIndependence`) and the connection-rank
bound, which the super-Gram identity supplies downstream
(`RS/TheoremConverse.lean`).  The normalization on the empty graph is
proved here: the Definition 5 value of any flagless
fragment is `(k − 2ℓ) ^ circles`.
-/

@[expose] public section

namespace RS

/-! ## The value on flagless fragments -/

section EmptyValue

variable {α : Type} (W : Fragment α)

/-- The empty edge subset of a flagless fragment. -/
private def flaglessEmptySubset : EdgeSubset W :=
  ⟨∅, fun f hf => absurd hf (Finset.notMem_empty f)⟩

/-- The vacuous transition system on the empty subset of a
flagless fragment. -/
private def flaglessTransition [IsEmpty W.Flag] :
    (flaglessEmptySubset W).TransitionSystem where
  match_ := fun f => isEmptyElim f
  match_invol := fun f => isEmptyElim f
  match_ne := fun f => isEmptyElim f
  match_mem := fun f => isEmptyElim f
  match_vertex := fun f => isEmptyElim f
  attach_internal := fun f => isEmptyElim f

/-- The vacuous orientation. -/
private def flaglessOrientation [IsEmpty W.Flag] :
    (flaglessTransition W).Orientation where
  isOut := fun f => isEmptyElim f
  match_flip := fun f => isEmptyElim f
  pairing_flip := fun f => isEmptyElim f

open Classical in
/-- **The Definition 5 value of a flagless fragment** is the circle
factor alone. -/
theorem mixedPartition_of_flagless [IsEmpty W.Flag] [IsEmpty W.Vertex]
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) :
    mixedPartition h W = ((k : ℂ) - 2 * ℓ) ^ W.circles := by
  unfold mixedPartition
  rw [Fintype.sum_eq_single ∅
    (fun s hs => absurd (Finset.eq_empty_of_isEmpty s) hs)]
  rw [dite_eq_left (fun f hf => absurd hf (Finset.notMem_empty f))]
  rw [ite_eq_left (show (EdgeSubset.mk (∅ : Finset W.Flag)
      (fun f hf => absurd hf (Finset.notMem_empty f))).Eulerian
    from fun v => isEmptyElim v)]
  have hval : (EdgeSubset.mk (∅ : Finset W.Flag)
      (fun f hf => absurd hf (Finset.notMem_empty f))).mixedValue h =
      1 := by
    have hne : Nonempty
        ((κ : (flaglessEmptySubset W).TransitionSystem) ×
          κ.Orientation) :=
      ⟨⟨flaglessTransition W, flaglessOrientation W⟩⟩
    rw [show (EdgeSubset.mk (∅ : Finset W.Flag)
        (fun f hf => absurd hf (Finset.notMem_empty f))) =
      flaglessEmptySubset W from rfl]
    rw [EdgeSubset.mixedValue, dite_eq_left hne]
    unfold EdgeSubset.mixedSummand
    have hcirc : ∀ κ : (flaglessEmptySubset W).TransitionSystem,
        κ.circuitCount = 0 := by
      intro κ
      unfold EdgeSubset.TransitionSystem.circuitCount
      have : IsEmpty {f : W.Flag //
          f ∈ (flaglessEmptySubset W).flags} :=
        ⟨fun f => isEmptyElim f.val⟩
      rw [Subsingleton.elim κ.walkPerm 1, Equiv.Perm.cycleType_one]
      simp
    rw [hcirc, pow_zero, one_mul]
    have : IsEmpty {f : W.Flag //
        f ∉ (flaglessEmptySubset W).flags} :=
      ⟨fun f => isEmptyElim f.val⟩
    have : IsEmpty {f : W.Flag //
        f ∈ (flaglessEmptySubset W).flags} :=
      ⟨fun f => isEmptyElim f.val⟩
    have : Subsingleton
        ((flaglessEmptySubset W).EvenColouring k) :=
      ⟨fun a b => Subtype.ext (funext fun f => isEmptyElim f)⟩
    have : Subsingleton
        ((flaglessEmptySubset W).OddColouring ℓ) :=
      ⟨fun a b => Subtype.ext (funext fun f => isEmptyElim f)⟩
    rw [Fintype.sum_subsingleton _
      ⟨fun f => isEmptyElim f, fun f => isEmptyElim f⟩]
    rw [Fintype.sum_subsingleton _
      ⟨fun f => isEmptyElim f, fun f => isEmptyElim f⟩]
    rw [Finset.univ_eq_empty, Finset.prod_empty]
  rw [hval]
  ring

end EmptyValue

/-- **The empty-graph normalization**: the Definition 5 value of
the empty closed fragment is `1`. -/
theorem mixedPartition_empty {k ℓ : ℕ} (h : MixedFunctional k ℓ) :
    mixedPartition h emptyClosedFragment = 1 := by
  have : IsEmpty emptyClosedFragment.Flag :=
    inferInstanceAs (IsEmpty Empty)
  have : IsEmpty emptyClosedFragment.Vertex :=
    inferInstanceAs (IsEmpty Empty)
  rw [mixedPartition_of_flagless emptyClosedFragment h]
  rw [show emptyClosedFragment.circles = 0 from rfl]
  ring

/-! ## The converse statement -/

/-- **Assembly of the converse** from the Eulerian-independence
input and the connection-rank bound. -/
theorem converseStatement_of_rank_bounded (hInd : EulerianIndependence)
    (Hrank : ∀ (k ℓ : ℕ) (hf : MixedFunctional k ℓ),
      EdgeRankBounded (fun W => mixedPartition hf W) (k + 2 * ℓ)) :
    RegtsSevensterConverseStatement := by
  intro k ℓ hf
  exact ⟨⟨fun W => mixedPartition hf W, mixedPartition_empty hf,
    fun W₁ W₂ e => mixedPartition_transport hInd e hf,
    (Hrank k ℓ hf).mono (le_max_right 1 (k + 2 * ℓ))⟩,
    fun W => rfl⟩

end RS
