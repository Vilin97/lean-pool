/-
Copyright (c) 2026 Wondermonger-daydreaming. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wondermonger-daydreaming
-/

import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
  CANONICAL DELETION OF THE BOUNDARY PAIR

  Canonical deletion of coordinates {0, 1} from Fin (2n+2),
  producing Fin (2n) via the uniform shift x ↦ x + 2.

  The construction avoids piecewise reindexing by restricting to the
  invariant subtype `{x | 2 ≤ x.val}` and conjugating through a single
  equivalence.

  Architecture:
  1. shiftTwoEquiv: the bijection Fin(2n) ≃ { x : Fin(2n+2) | 2 ≤ x }
  2. mapsTo_remaining: π(0)=1 ∧ π(1)=0 → π maps {x≥2} to {x≥2}
  3. contractZeroOne: restrict π to {x≥2}, conjugate through shiftTwoEquiv

  The full deleteAdjacent is then:
    rotate to (0,1) → contractZeroOne → rotate back (if needed)
-/

namespace SemicircleCore

variable {n : ℕ}

/-- The uniform, piecewise-free embedding of the reduced universe
    into the expanded universe, bypassing coordinates 0 and 1. -/
def shiftTwoEquiv (n : ℕ) :
    Fin (2 * n) ≃ { x : Fin (2 * n + 2) // 2 ≤ x.val } where
  toFun x := ⟨⟨x.val + 2, by omega⟩, by simp⟩
  invFun y := ⟨y.val.val - 2, by omega⟩
  left_inv x := Fin.ext (by simp)
  right_inv y := Subtype.ext (Fin.ext (by simp; omega))

/-- The invariant subspace after 0 and 1 are claimed by adjacency. -/
def RemainingDomain (n : ℕ) : Set (Fin (2 * n + 2)) :=
  { x | 2 ≤ x.val }

/-- If π(0) = 1 and π(1) = 0, then π maps {x | x ≥ 2} into itself.

    Proof: for x ≥ 2, π(x) ≠ 0 because π(1) = 0 and π is injective,
    so x = 1, contradicting x ≥ 2. Similarly π(x) ≠ 1 because
    π(0) = 1 and π is injective, so x = 0, contradicting x ≥ 2.
    Therefore π(x) ≥ 2. -/
lemma mapsTo_remaining {π : Equiv.Perm (Fin (2 * n + 2))}
    (h₀ : π ⟨0, by omega⟩ = ⟨1, by omega⟩)
    (h₁ : π ⟨1, by omega⟩ = ⟨0, by omega⟩) :
    Set.MapsTo π (RemainingDomain n) (RemainingDomain n) := by
  intro x hx
  simp only [RemainingDomain, Set.mem_setOf_eq] at *
  -- By contradiction: assume (π x).val < 2
  by_contra hlt
  push Not at hlt
  have : (π x).val = 0 ∨ (π x).val = 1 := by omega
  rcases this with hv | hv
  · -- π(x) = ⟨0,_⟩ = π(⟨1,_⟩), so x = ⟨1,_⟩, contradicting x.val ≥ 2
    have heq : π x = ⟨0, by omega⟩ := Fin.ext hv
    have hx1 : x = ⟨1, by omega⟩ := π.injective (heq.trans h₁.symm)
    simp [hx1] at hx
  · -- π(x) = ⟨1,_⟩ = π(⟨0,_⟩), so x = ⟨0,_⟩, contradicting x.val ≥ 2
    have heq : π x = ⟨1, by omega⟩ := Fin.ext hv
    have hx0 : x = ⟨0, by omega⟩ := π.injective (heq.trans h₀.symm)
    simp [hx0] at hx

/-- π.symm also maps the remaining domain to itself. -/
private lemma symm_mapsTo_remaining {π : Equiv.Perm (Fin (2 * n + 2))}
    (h₀ : π ⟨0, by omega⟩ = ⟨1, by omega⟩)
    (h₁ : π ⟨1, by omega⟩ = ⟨0, by omega⟩) :
    Set.MapsTo π.symm (RemainingDomain n) (RemainingDomain n) :=
  mapsTo_remaining
    (by rw [Equiv.symm_apply_eq]; exact h₁.symm)
    (by rw [Equiv.symm_apply_eq]; exact h₀.symm)

/-- The sanitized deletion operator.
    Restrict π to the invariant subtype {x ≥ 2}, then pull back
    to Fin(2n) via shiftTwoEquiv.

    Construction: build the restricted permutation on `{x | 2 ≤ x.val}`,
    then conjugate through `shiftTwoEquiv`. -/
def contractZeroOne (π : Equiv.Perm (Fin (2 * n + 2)))
    (h₀ : π ⟨0, by omega⟩ = ⟨1, by omega⟩)
    (h₁ : π ⟨1, by omega⟩ = ⟨0, by omega⟩) :
    Equiv.Perm (Fin (2 * n)) :=
  let hmaps := mapsTo_remaining h₀ h₁
  let hmaps_inv := symm_mapsTo_remaining h₀ h₁
  let restrictPerm : Equiv.Perm { x : Fin (2 * n + 2) // 2 ≤ x.val } :=
    { toFun := fun ⟨x, hx⟩ => ⟨π x, hmaps hx⟩
      invFun := fun ⟨x, hx⟩ => ⟨π.symm x, hmaps_inv hx⟩
      left_inv := fun ⟨x, _⟩ => Subtype.ext (π.symm_apply_apply x)
      right_inv := fun ⟨x, _⟩ => Subtype.ext (π.apply_symm_apply x) }
  (shiftTwoEquiv n).trans (restrictPerm.trans (shiftTwoEquiv n).symm)

/-- contractZeroOne preserves the pairing property.
    If π is a fixed-point-free involution on Fin(2n+2) with π(0)=1,
    then contractZeroOne π is a fixed-point-free involution on Fin(2n). -/
theorem contractZeroOne_isPairing {π : Equiv.Perm (Fin (2 * n + 2))}
    (h₀ : π ⟨0, by omega⟩ = ⟨1, by omega⟩)
    (h₁ : π ⟨1, by omega⟩ = ⟨0, by omega⟩)
    (hinv : π ^ 2 = 1)
    (hfpf : ∀ x, π x ≠ x) :
    let π' := contractZeroOne π h₀ h₁
    π' ^ 2 = 1 ∧ ∀ x, π' x ≠ x := by
  -- Extract the pointwise involution from π ^ 2 = 1
  have hππ : ∀ x, π (π x) = x := by
    intro x; have h : π * π = 1 := by rwa [← sq]
    change (π * π) x = x; simp [h]
  refine ⟨?_, ?_⟩
  · -- INVOLUTION: π'(π'(x)) = x
    -- π' = e.trans(p.trans(e.symm)) where e = shiftTwoEquiv, p = restrictPerm
    -- π'(π'(x)) = e.symm(p(e(e.symm(p(e(x)))))) = e.symm(p(p(e(x)))) = e.symm(e(x)) = x
    ext x
    simp only [sq, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id_eq,
      contractZeroOne, Equiv.trans_apply, Equiv.apply_symm_apply]
    -- Beta-reduce the anonymous restrictPerm, then collapse π(π(z)) = z
    dsimp
    simp [hππ, shiftTwoEquiv]
  · -- FIXED-POINT-FREE: π'(x) = x → False
    -- If e.symm(p(e(x))) = x, apply e: p(e(x)) = e(x)
    -- Unpack p: π(z) = z where z = (e(x)).val, contradicting hfpf
    intro x hfix
    simp only [contractZeroOne, Equiv.trans_apply] at hfix
    -- hfix : (shiftTwoEquiv n).symm (restrictPerm (shiftTwoEquiv n x)) = x
    have h := congr_arg (shiftTwoEquiv n) hfix
    simp only [Equiv.apply_symm_apply] at h
    -- h : restrictPerm (shiftTwoEquiv n x) = shiftTwoEquiv n x
    -- Extract the Fin-level equality: π(z) = z
    have h2 := congr_arg Subtype.val h
    simp only [Equiv.coe_fn_mk] at h2
    -- h2 : π(z) = z at the Fin level, contradicting hfpf
    exact hfpf _ h2

end SemicircleCore
