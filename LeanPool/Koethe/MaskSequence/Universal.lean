/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
import LeanPool.Koethe.MaskSequence.Chain

/-!
# Universal mortal sequences from abstract mask mortality

This file supplies the combinatorial implication from `MaskMortality k` to a
single nonzero sequence with uniformly vanishing windows for every pencil.
The only matrix facts used are the forward concatenation law for `wordProd`
and absorption by zero.  There are no algebraic-geometric hypotheses beyond
the abstract mortality assumption, and no assertion about the density of an
infinite union of masks.
-/

noncomputable section

namespace KoetheCounterexample
namespace MaskSequence

variable {k : Type*} [Field k] {d : ℕ}

/-- Split a forward window at a specified length. -/
theorem window_add (P : Pencil k d) (v : ℕ → Triple k) (start a b : ℕ) :
    P.window v start (a + b) = P.window v start a * P.window v (start + a) b := by
  simp [Pencil.window, List.ofFn_add, Nat.add_assoc]

/-- A window containing a zero contiguous subwindow is itself zero.
No commutation or rearrangement of the matrix factors is used. -/
theorem window_eq_zero_of_subwindow (P : Pencil k d) (v : ℕ → Triple k)
    (start N offset len : ℕ) (hfit : offset + len ≤ N)
    (hz : P.window v (start + offset) len = 0) : P.window v start N = 0 := by
  have hN : N = (offset + len) + (N - (offset + len)) := by omega
  rw [hN, window_add, window_add, hz, mul_zero, zero_mul]

/-- An installed word occurs at every nonnegative multiple of the mask period
in every compatible sequence. -/
theorem carries_window (P : Pencil k d) (M : PeriodicMask k)
    {w : List (Triple k)} (hw : Carries M w) {v : ℕ → Triple k}
    (hv : M.SeqCompatible v) {b : ℕ} (hb : b % M.period = 0) :
    P.window v b w.length = P.wordProd w := by
  have hword : (List.ofFn fun i : Fin w.length => v (b + i.val)) = w := by
    calc
      _ = List.ofFn w.get := by
        apply congrArg List.ofFn
        funext i
        apply hv (b + i.val) (w.get i)
        rw [lookup_add_of_mod_eq_zero M hb]
        exact hw.2 i
      _ = w := List.ofFn_get w
  rw [Pencil.window, hword]

/-- Twice the mask period is one bound that works at *every* starting site. -/
theorem kills_windows (P : Pencil k d) (M : PeriodicMask k)
    {v : ℕ → Triple k} (hv : M.SeqCompatible v) (hkill : Kills M P) :
    ∀ start, P.window v start (2 * M.period) = 0 := by
  obtain ⟨w, hw, hz⟩ := hkill
  intro start
  let offset := M.period - start % M.period
  have hoffset : offset ≤ M.period := Nat.sub_le _ _
  have hfit : offset + w.length ≤ 2 * M.period := by
    have := hw.1
    omega
  have hrem : start % M.period ≤ M.period := (Nat.mod_lt start M.period_pos).le
  have hb : (start + offset) % M.period = 0 := by
    calc
      _ = (start % M.period + offset) % M.period :=
        (Nat.mod_add_mod start M.period offset).symm
      _ = 0 := by rw [show start % M.period + offset = M.period from
        Nat.add_sub_of_le hrem, Nat.mod_self]
  exact window_eq_zero_of_subwindow P v start (2 * M.period) offset w.length hfit
    ((carries_window P M hw hv hb).trans hz)

end MaskSequence

/-- The complete combinatorial construction, independent of any proof of
matrix mortality.  Countability is used only to enumerate all pencils. -/
theorem exists_universalMortalSequence (k : Type*) [Field k] [Countable k]
    (hm : MaskMortality k) : ∃ v : ℕ → Triple k, UniversalMortalSequence k v := by
  classical
  have : Nonempty (Σ d : ℕ, Pencil k d) :=
    ⟨⟨0, { scalar := 0, linear := 0, linear_off_root := by simp }⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (Σ d : ℕ, Pencil k d)
  obtain ⟨v, hv, hcompat⟩ := MaskSequence.exists_sequence_for_enumeration hm e
  refine ⟨v, hv, ?_⟩
  intro d P
  obtain ⟨j, hj⟩ := he ⟨d, P⟩
  have hkill : MaskSequence.Kills (MaskSequence.masks hm e (j + 1)).val P :=
    (congrArg (fun a : Σ d : ℕ, Pencil k d =>
      MaskSequence.Kills (MaskSequence.masks hm e (j + 1)).val a.2) hj).mp
        (MaskSequence.masks_succ hm e j).2.2
  refine ⟨2 * (MaskSequence.masks hm e (j + 1)).val.period, ?_, ?_⟩
  · exact Nat.mul_pos (by decide) (MaskSequence.masks hm e (j + 1)).val.period_pos
  · exact MaskSequence.kills_windows P _ (hcompat (j + 1)) hkill

end KoetheCounterexample

end
