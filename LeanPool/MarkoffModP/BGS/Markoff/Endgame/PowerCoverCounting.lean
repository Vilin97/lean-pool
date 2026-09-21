/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Basic

/-!
# Exact power-cover multiplicities in the endgame

The paper divides its trace-cover point count by the two power-map degrees.  This module proves
that step exactly for finite cyclic groups: a cover solution is a target trace solution together
with one point in each power-map fiber, and every such fiber is equivalent to the corresponding
kernel.  No asymptotic or geometric estimate enters this multiplicity identity.
-/

namespace BGS.Markoff

noncomputable section

variable {G H T : Type*} [CommGroup G] [CommGroup H]

/-- Solutions of a trace equation after applying power maps to two finite groups. -/
def powerTraceCoverSolutions
    (leftTrace : G → T) (rightTrace : H → T) (d e : ℕ) :=
  {z : G × H // leftTrace (z.1 ^ d) = rightTrace (z.2 ^ e)}

/-- The corresponding equation on the two power-map images. -/
def powerTraceRangeSolutions
    (leftTrace : G → T) (rightTrace : H → T) (d e : ℕ) :=
  {z : (powMonoidHom d : G →* G).range × (powMonoidHom e : H →* H).range //
    leftTrace z.1 = rightTrace z.2}

/-- A power-cover solution is a target solution together with one point in each power-map fiber. -/
def powerTraceCoverEquivSigmaFibers
    (leftTrace : G → T) (rightTrace : H → T) (d e : ℕ) :
    powerTraceCoverSolutions leftTrace rightTrace d e ≃
      Σ s : powerTraceRangeSolutions leftTrace rightTrace d e,
        ((powMonoidHom d : G →* G) ⁻¹' {(s.1.1 : G)} : Set G) ×
          ((powMonoidHom e : H →* H) ⁻¹' {(s.1.2 : H)} : Set H) where
  toFun z := ⟨⟨⟨⟨z.1.1 ^ d, ⟨z.1.1, by simp⟩⟩,
      ⟨z.1.2 ^ e, ⟨z.1.2, by simp⟩⟩⟩, z.2⟩,
    ⟨⟨z.1.1, by simp⟩, ⟨z.1.2, by simp⟩⟩⟩
  invFun w := ⟨(w.2.1.1, w.2.2.1), by
    have hx : (powMonoidHom d : G →* G) w.2.1.1 = (w.1.1.1 : G) := w.2.1.2
    have hy : (powMonoidHom e : H →* H) w.2.2.1 = (w.1.1.2 : H) := w.2.2.2
    change leftTrace (w.2.1.1 ^ d) = rightTrace (w.2.2.1 ^ e)
    rw [show w.2.1.1 ^ d = w.1.1.1 by exact hx,
      show w.2.2.1 ^ e = w.1.1.2 by exact hy]
    exact w.1.2⟩
  left_inv z := by rfl
  right_inv w := by
    rcases w with ⟨⟨⟨⟨sx, hsx⟩, ⟨sy, hsy⟩⟩, hs⟩,
      ⟨⟨x, hx⟩, ⟨y, hy⟩⟩⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hy
    dsimp at hx hy ⊢
    subst sx
    subst sy
    rfl

theorem natCard_powerMapFiber_eq_ker
    [Finite G] (d : ℕ) (x : (powMonoidHom d : G →* G).range) :
    Nat.card ((powMonoidHom d : G →* G) ⁻¹' {x.1} : Set G) =
      Nat.card (powMonoidHom d : G →* G).ker := by
  obtain ⟨a, ha⟩ := x.2
  have hset :
      (powMonoidHom d : G →* G) ⁻¹' {x.1} =
        (powMonoidHom d : G →* G) ⁻¹' {(powMonoidHom d) a} := by
    rw [ha]
  rw [hset]
  exact Nat.card_congr ((powMonoidHom d : G →* G).fiberEquivKer a)

theorem natCard_powerTraceCoverSolutions
    [Finite G] [Finite H]
    (leftTrace : G → T) (rightTrace : H → T) (d e : ℕ) :
    Nat.card (powerTraceCoverSolutions leftTrace rightTrace d e) =
      Nat.card (powMonoidHom d : G →* G).ker *
      Nat.card (powMonoidHom e : H →* H).ker *
          Nat.card (powerTraceRangeSolutions leftTrace rightTrace d e) := by
  letI : Finite (powMonoidHom d : G →* G).range :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (powMonoidHom e : H →* H).range :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (powerTraceRangeSolutions leftTrace rightTrace d e) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI := Fintype.ofFinite (powerTraceRangeSolutions leftTrace rightTrace d e)
  rw [Nat.card_congr (powerTraceCoverEquivSigmaFibers leftTrace rightTrace d e),
    Nat.card_sigma]
  simp_rw [Nat.card_prod, natCard_powerMapFiber_eq_ker]
  simp [mul_comm]

theorem natCard_powerTraceCoverSolutions_of_dvd
    [Finite G] [Finite H] [IsCyclic G] [IsCyclic H]
    (leftTrace : G → T) (rightTrace : H → T) (d e : ℕ)
    (hd : d ∣ Nat.card G) (he : e ∣ Nat.card H) :
    Nat.card (powerTraceCoverSolutions leftTrace rightTrace d e) =
      d * e * Nat.card (powerTraceRangeSolutions leftTrace rightTrace d e) := by
  rw [natCard_powerTraceCoverSolutions,
    IsCyclic.card_powMonoidHom_ker, IsCyclic.card_powMonoidHom_ker,
    Nat.gcd_eq_right_iff_dvd.mpr hd, Nat.gcd_eq_right_iff_dvd.mpr he]

end

end BGS.Markoff
