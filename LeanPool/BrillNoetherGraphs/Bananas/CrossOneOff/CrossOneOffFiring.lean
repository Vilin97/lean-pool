/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffArithmetic
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaPrefix
import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.Semibreak

/-!
# Firing identities for the cross-one-off marking

This file formalizes the chip-firing calculation behind Lemma 4.30 of
the twice-marked banana paper.  Coordinates are the normalized coordinates of
`strandVertex`.  Write `L,R` for the two multivalent vertices, put

`u = v_{α,1}`, `v = v_{β,N-1}`, and `b = mN+r`.

The common identity is

`gR + au - bv ~ (a-m-2)L + (g+m-b)R + v_{α,a} + v_{β,r}`.

It simultaneously fixes the residue convention and the two-off-by-one error
in the printed third case.  The three residue-specific corollaries below are
the divisor identities needed before applying the banana normal-form rank
calculus.
-/

namespace Bananas

open Utilities


private theorem linearEquiv_zsmul {G : CFGraph} {D E : CFDiv G}
    (h : linear_equiv G D E) (q : ℤ) :
    linear_equiv G (q • D) (q • E) := by
  unfold linear_equiv at h ⊢
  simpa [smul_sub] using
    (AddSubgroup.zsmul_mem (principal_divisors G) h q)

private theorem linearEquiv_sub {G : CFGraph} {A B C D : CFDiv G}
    (h₁ : linear_equiv G A B) (h₂ : linear_equiv G C D) :
    linear_equiv G (A - C) (B - D) := by
  unfold linear_equiv at h₁ h₂ ⊢
  have h := (principal_divisors G).sub_mem h₁ h₂
  convert h using 1 ; abel

/-- A multiple of the first off-endpoint mark can be replaced by one chip at
the corresponding coordinate and the remaining chips at the left endpoint.
This is the `α`-strand part of Lemma 4.30. -/
theorem crossOneOff_first_mark_multiple
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (a : ℕ)
    (ha : a ≤ B.length α) :
    linear_equiv B.graph
      ((a : ℤ) • one_chip
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩))
      (((a : ℤ) - 1) • one_chip (leftEndpoint B) +
        one_chip (strandVertex B α ⟨a, by omega⟩)) := by
  have h := strand_prefix_linearEquiv B α ⟨a, by omega⟩
  unfold linear_equiv at h ⊢
  convert h using 1 ;
    simp only [smul_sub   ] ;
    ring

/-- Deleting the first off-endpoint mark from a chip farther along the same
strand shifts that chip one step toward the left endpoint. -/
theorem crossOneOff_sub_first_mark_shift
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (p : ℕ)
    (hpLo : 1 ≤ p) (hpHi : p ≤ B.length α) :
    linear_equiv B.graph
      (one_chip (strandVertex B α ⟨p, by omega⟩) -
        one_chip (strandVertex B α ⟨1, by
          have := B.length_pos α; omega⟩))
      (one_chip (strandVertex B α ⟨p - 1, by omega⟩) -
        one_chip (leftEndpoint B)) := by
  have hp := strand_prefix_linearEquiv B α ⟨p, by omega⟩
  have hpPrev := strand_prefix_linearEquiv B α ⟨p - 1, by omega⟩
  have hStep := linearEquiv_sub hp hpPrev
  have hStepSymm := hStep.symm
  have hpPred : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  unfold linear_equiv at hStepSymm ⊢
  convert hStepSymm using 1 ;
    ext z ;
    simp only [smul_sub, Pi.smul_apply, Pi.sub_apply ] ;
    rw [hpPred] ;
    ring

/-- Deleting the second off-endpoint mark from a chip earlier on the same
strand shifts that chip one step toward the right endpoint. -/
theorem crossOneOff_sub_second_mark_shift
    {g : ℕ} (B : Banana g) (β : Fin (g + 1)) (q : ℕ)
    (hq : q < B.length β) :
    linear_equiv B.graph
      (one_chip (strandVertex B β ⟨q, by omega⟩) -
        one_chip (strandVertex B β ⟨B.length β - 1, by
          have := B.length_pos β; omega⟩))
      (one_chip (strandVertex B β ⟨q + 1, by omega⟩) -
        one_chip (rightEndpoint B)) := by
  have hqPrefix := strand_prefix_linearEquiv B β ⟨q, by omega⟩
  have hPenultimate := strand_prefix_linearEquiv B β
    ⟨B.length β - 1, by have := B.length_pos β; omega⟩
  have hqNext := strand_prefix_linearEquiv B β ⟨q + 1, by omega⟩
  have hEnd := strand_prefix_linearEquiv B β ⟨B.length β, by omega⟩
  rw [strandVertex_length B β] at hEnd
  have hLeft := linearEquiv_sub hqPrefix hPenultimate
  have hRight := linearEquiv_sub hqNext hEnd
  have hLength : ((B.length β - 1 : ℕ) : ℤ) =
      (B.length β : ℤ) - 1 := by
    have := B.length_pos β
    omega
  have hScalars :
      linear_equiv B.graph
        ((q : ℤ) •
            (one_chip (strandVertex B β ⟨1, by
              have := B.length_pos β; omega⟩) - one_chip (leftEndpoint B)) -
          ((B.length β - 1 : ℕ) : ℤ) •
            (one_chip (strandVertex B β ⟨1, by
              have := B.length_pos β; omega⟩) - one_chip (leftEndpoint B)))
        (((q + 1 : ℕ) : ℤ) •
            (one_chip (strandVertex B β ⟨1, by
              have := B.length_pos β; omega⟩) - one_chip (leftEndpoint B)) -
          (B.length β : ℤ) •
            (one_chip (strandVertex B β ⟨1, by
              have := B.length_pos β; omega⟩) - one_chip (leftEndpoint B))) := by
    unfold linear_equiv
    convert (principal_divisors B.graph).zero_mem using 1
    ext z
    simp only [Pi.sub_apply, Pi.smul_apply]
    push_cast
    rw [hLength]
    ring_nf
    simp
  have h := hLeft.symm.trans (hScalars.trans hRight)
  unfold linear_equiv at h ⊢
  convert h using 1 ; abel

/-- If `b = mN+r`, a multiple of the second off-endpoint mark has the
canonical endpoint-plus-residue representative.  This is the common
`β`-strand calculation behind all three cases of Lemma 4.30. -/
theorem crossOneOff_second_mark_multiple
    {g : ℕ} (B : Banana g) (β : Fin (g + 1)) (b m r : ℕ)
    (hb : b = m * B.length β + r) (hr : r ≤ B.length β) :
    linear_equiv B.graph
      ((b : ℤ) • one_chip
        (strandVertex B β ⟨B.length β - 1, by
          have := B.length_pos β; omega⟩))
      (((m : ℤ) + 1) • one_chip (leftEndpoint B) +
        ((b : ℤ) - (m : ℤ)) • one_chip (rightEndpoint B) -
          one_chip (strandVertex B β ⟨r, by omega⟩)) := by
  let e : CFDiv B.graph :=
    one_chip (strandVertex B β ⟨1, by
      have := B.length_pos β; omega⟩) - one_chip (leftEndpoint B)
  have hPenultimate := strand_prefix_linearEquiv B β
    ⟨B.length β - 1, by have := B.length_pos β; omega⟩
  have hEnd := strand_prefix_linearEquiv B β
    ⟨B.length β, by omega⟩
  have hRemainder := strand_prefix_linearEquiv B β ⟨r, by omega⟩
  rw [strandVertex_length B β] at hEnd
  have hPenultimateScaled := linearEquiv_zsmul hPenultimate (b : ℤ)
  have hEndScaled := linearEquiv_zsmul hEnd ((b : ℤ) - (m : ℤ))
  have hCombined := linearEquiv_sub hEndScaled hRemainder
  have hbInt : (b : ℤ) = (m : ℤ) * (B.length β : ℤ) + (r : ℤ) := by
    exact_mod_cast hb
  have hLengthPred : ((B.length β - 1 : ℕ) : ℤ) =
      (B.length β : ℤ) - 1 := by
    have := B.length_pos β
    omega
  have hCoefficient :
      (b : ℤ) * ((B.length β - 1 : ℕ) : ℤ) =
        ((b : ℤ) - (m : ℤ)) * (B.length β : ℤ) - (r : ℤ) := by
    rw [hLengthPred, hbInt]
    ring
  have hMiddle : linear_equiv B.graph
      ((b : ℤ) • ((B.length β - 1 : ℕ) : ℤ) • e)
      (((b : ℤ) - (m : ℤ)) •
          (one_chip (rightEndpoint B) - one_chip (leftEndpoint B)) -
        (one_chip (strandVertex B β ⟨r, by omega⟩) -
          one_chip (leftEndpoint B))) := by
    convert hCombined using 1 ;
      ext z ;
      simp only [e, smul_sub, smul_smul, Pi.smul_apply, Pi.sub_apply,
        ] ;
      rw [hCoefficient] ;
      ring
  have hDifference : linear_equiv B.graph
      ((b : ℤ) •
        (one_chip
          (strandVertex B β ⟨B.length β - 1, by
            have := B.length_pos β; omega⟩) - one_chip (leftEndpoint B)))
      (((b : ℤ) - (m : ℤ)) •
          (one_chip (rightEndpoint B) - one_chip (leftEndpoint B)) -
        (one_chip (strandVertex B β ⟨r, by omega⟩) -
          one_chip (leftEndpoint B))) := by
    exact hPenultimateScaled.symm.trans hMiddle
  unfold linear_equiv at hDifference ⊢
  convert hDifference using 1 ;
    simp only [smul_sub   ] ;
    ring

/-- The common corrected firing identity for the cross-one-off marking. -/
theorem crossOneOff_firing_identity
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1)) (a b m r : ℕ)
    (ha : a ≤ B.length α) (hb : b = m * B.length β + r)
    (hr : r ≤ B.length β) :
    linear_equiv B.graph
      ((g : ℤ) • one_chip (rightEndpoint B) +
        (a : ℤ) • one_chip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        (b : ℤ) • one_chip
          (strandVertex B β ⟨B.length β - 1, by
            have := B.length_pos β; omega⟩))
      (((a : ℤ) - (m : ℤ) - 2) • one_chip (leftEndpoint B) +
        ((g : ℤ) + (m : ℤ) - (b : ℤ)) •
          one_chip (rightEndpoint B) +
        one_chip (strandVertex B α ⟨a, by omega⟩) +
        one_chip (strandVertex B β ⟨r, by omega⟩)) := by
  have hFirst := crossOneOff_first_mark_multiple B α a ha
  have hSecond := crossOneOff_second_mark_multiple B β b m r hb hr
  unfold linear_equiv at hFirst hSecond ⊢
  have h := (principal_divisors B.graph).sub_mem hFirst hSecond
  convert h using 1 ;
    ext z ;
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply] ;
    ring

/-! ## The corrected residue cases of Lemma 4.30 -/

/-- Lemma 4.30(1), at a positive multiple `b = mN`.  The theorem is only a
firing identity; the numerical hypotheses used later to identify the
transmission value are deliberately kept separate. -/
theorem crossOneOff_firing_multiple
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1)) (b m : ℕ)
    (hb : b = m * B.length β) (ha : m + 1 ≤ B.length α) :
    linear_equiv B.graph
      ((g : ℤ) • one_chip (rightEndpoint B) +
        ((m + 1 : ℕ) : ℤ) • one_chip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        (b : ℤ) • one_chip
          (strandVertex B β ⟨B.length β - 1, by
            have := B.length_pos β; omega⟩))
      (one_chip (strandVertex B α ⟨m + 1, by omega⟩) +
        ((g : ℤ) + (m : ℤ) - (b : ℤ)) •
          one_chip (rightEndpoint B)) := by
  have h := crossOneOff_firing_identity B α β (m + 1) b m 0 ha
    (by simp [hb]) (by omega)
  rw [strandVertex_zero B β] at h
  unfold linear_equiv at h ⊢
  convert h using 1 ;
    ext z ;
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply] ;
    push_cast ;
    ring

/-- Lemma 4.30(2), in the unambiguous convention `b+1 = mN`.  The
length-two, `b=1` exception concerns the subsequent `Δ` claim, not this
firing identity. -/
theorem crossOneOff_firing_complement_residue
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1)) (b m : ℕ)
    (hm : 1 ≤ m) (hb : b + 1 = m * B.length β)
    (ha : g + m ≤ B.length α) :
    linear_equiv B.graph
      ((g : ℤ) • one_chip (rightEndpoint B) +
        ((g + m : ℕ) : ℤ) • one_chip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        (b : ℤ) • one_chip
          (strandVertex B β ⟨B.length β - 1, by
            have := B.length_pos β; omega⟩))
      (((g : ℤ) - 1) • one_chip (leftEndpoint B) +
        ((g : ℤ) - (m : ℤ) * ((B.length β : ℤ) - 1)) •
          one_chip (rightEndpoint B) +
        one_chip (strandVertex B α ⟨g + m, by omega⟩) +
        one_chip
          (strandVertex B β ⟨B.length β - 1, by
            have := B.length_pos β; omega⟩)) := by
  have hN : 0 < B.length β := B.length_pos β
  have hDecompose :
      b = (m - 1) * B.length β + (B.length β - 1) := by
    calc
      b = m * B.length β - 1 := by omega
      _ = ((m - 1) + 1) * B.length β - 1 := by
        rw [Nat.sub_add_cancel hm]
      _ = (m - 1) * B.length β + (B.length β - 1) := by
        rw [Nat.add_mul, one_mul]
        omega
  have h := crossOneOff_firing_identity B α β (g + m) b (m - 1)
    (B.length β - 1) ha hDecompose (by omega)
  have hmCast : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  have hbCast : (b : ℤ) = (m : ℤ) * (B.length β : ℤ) - 1 := by
    have hbInt : (b : ℤ) + 1 = (m : ℤ) * (B.length β : ℤ) := by
      exact_mod_cast hb
    omega
  unfold linear_equiv at h ⊢
  convert h using 1 ;
    ext z ;
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply] ;
    push_cast ;
    rw [hmCast, hbCast] ;
    ring

/-- Corrected Lemma 4.30(3), using the positive remainder convention
`b = mN+r`, `1 ≤ r ≤ N-2`.  The printed coefficient of `L+R` is one too
large and its complementary coordinate belongs to the other residue
convention. -/
theorem crossOneOff_firing_positive_residue
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1)) (b m r : ℕ)
    (hb : b = m * B.length β + r)
    (_hrLo : 1 ≤ r) (hrHi : r + 1 < B.length β)
    (hCandidate : b ≤ g + 2 * m + 2)
    (ha : g + 2 * m + 2 - b ≤ B.length α) :
    linear_equiv B.graph
      ((g : ℤ) • one_chip (rightEndpoint B) +
        ((g + 2 * m + 2 - b : ℕ) : ℤ) • one_chip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        (b : ℤ) • one_chip
          (strandVertex B β ⟨B.length β - 1, by omega⟩))
      (((g : ℤ) + (m : ℤ) - (b : ℤ)) •
          (one_chip (leftEndpoint B) + one_chip (rightEndpoint B)) +
        one_chip
          (strandVertex B α ⟨g + 2 * m + 2 - b, by omega⟩) +
        one_chip (strandVertex B β ⟨r, by omega⟩)) := by
  have h := crossOneOff_firing_identity B α β
    (g + 2 * m + 2 - b) b m r ha hb (by omega)
  have hCandidateCast : ((g + 2 * m + 2 - b : ℕ) : ℤ) =
      (g : ℤ) + 2 * (m : ℤ) + 2 - (b : ℤ) := by
    omega
  unfold linear_equiv at h ⊢
  convert h using 1 ;
    ext z ;
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply] ;
    rw [hCandidateCast] ;
    ring

end Bananas
