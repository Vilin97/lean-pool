/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.FragmentEquiv

/-!
# Strand bundles

The identity fragments of the skein category: `strandBundle t` is
the disjoint union of `t` parallel strands, with strand `k` joining
boundary label `k` to boundary label `t + k`.  Flags are pairs
`(k, b)` with `b = false` at the incoming end (label `k`) and
`b = true` at the outgoing end (label `t + k`).
-/

namespace RS

/-- The bundle of `t` parallel strands: strand `k` joins label `k`
to label `t + k`. -/
def strandBundle (t : ℕ) : Fragment (Fin (t + t)) where
  Flag := Fin t × Bool
  Vertex := Empty
  attach := fun f =>
    Sum.inr (if f.2 then ⟨t + f.1.val, by omega⟩ else ⟨f.1.val, by omega⟩)
  pairing := fun f => (f.1, !f.2)
  pairing_invol := fun f => by simp
  pairing_ne := fun f h => by
    have hsnd := congrArg Prod.snd h
    simp at hsnd
  boundaryFlag := fun ℓ =>
    if h : ℓ.val < t then (⟨ℓ.val, h⟩, false)
    else (⟨ℓ.val - t, by omega⟩, true)
  attach_boundaryFlag := fun ℓ => by
    by_cases h : ℓ.val < t
    · rw [dite_eq_left h]
      exact congrArg Sum.inr (Fin.ext rfl)
    · rw [dite_eq_right h]
      refine congrArg Sum.inr (Fin.ext ?_)
      change t + (ℓ.val - t) = ℓ.val
      omega
  eq_boundaryFlag := fun ℓ f h => by
    obtain ⟨a, b⟩ := f
    have hℓ := (Sum.inr.inj h).symm
    cases b
    · simp only [Bool.false_eq_true, ite_false] at hℓ
      subst hℓ
      rw [dite_eq_left a.isLt]
    · simp only [ite_true] at hℓ
      subst hℓ
      rw [dite_eq_right (show ¬ t + a.val < t by omega)]
      refine Prod.ext_iff.mpr ⟨Fin.ext ?_, rfl⟩
      change a.val = t + a.val - t
      omega
  circles := 0

/-- The boundary flag of an incoming label. -/
theorem strandBundle_boundaryFlag_low (t : ℕ) (ℓ : Fin (t + t))
    (h : ℓ.val < t) :
    (strandBundle t).boundaryFlag ℓ = (⟨ℓ.val, h⟩, false) := by
  simp only [strandBundle, dite_eq_left h]

/-- The boundary flag of an outgoing label. -/
theorem strandBundle_boundaryFlag_high (t : ℕ) (ℓ : Fin (t + t))
    (h : ¬ ℓ.val < t) :
    (strandBundle t).boundaryFlag ℓ =
      (⟨ℓ.val - t, by omega⟩, true) := by
  simp only [strandBundle, dite_eq_right h]

end RS
