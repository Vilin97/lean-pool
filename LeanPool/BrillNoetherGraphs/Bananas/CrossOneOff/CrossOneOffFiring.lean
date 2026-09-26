/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffArithmetic
public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaPrefix
public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.Semibreak

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

@[expose] public section

namespace Bananas

open Utilities


private theorem linearEquiv_zsmul {G : CFGraph} {D E : CFDiv G}
    (h : linearEquiv G D E) (q : ℤ) :
    linearEquiv G (q • D) (q • E) := by
  unfold linearEquiv at h ⊢
  simpa [smul_sub] using
    (AddSubgroup.zsmul_mem (principalDivisors G) h q)

private theorem linearEquiv_sub {G : CFGraph} {A B C D : CFDiv G}
    (h₁ : linearEquiv G A B) (h₂ : linearEquiv G C D) :
    linearEquiv G (A - C) (B - D) := by
  unfold linearEquiv at h₁ h₂ ⊢
  have h := (principalDivisors G).sub_mem h₁ h₂
  convert h using 1 ; abel

/-- A multiple of the first off-endpoint mark can be replaced by one chip at
the corresponding coordinate and the remaining chips at the left endpoint.
This is the `α`-strand part of Lemma 4.30. -/
theorem crossOneOff_first_mark_multiple
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (a : ℕ)
    (ha : a ≤ B.length α) :
    linearEquiv B.graph
      ((a : ℤ) • oneChip
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩))
      (((a : ℤ) - 1) • oneChip (leftEndpoint B) +
        oneChip (strandVertex B α ⟨a, by omega⟩)) := by
  have h := strand_prefix_linearEquiv B α ⟨a, by omega⟩
  unfold linearEquiv at h ⊢
  convert h using 1 ;
    simp only [smul_sub   ] ;
    ring

/-- Deleting the first off-endpoint mark from a chip farther along the same
strand shifts that chip one step toward the left endpoint. -/
theorem crossOneOff_sub_first_mark_shift
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (p : ℕ)
    (hpLo : 1 ≤ p) (hpHi : p ≤ B.length α) :
    linearEquiv B.graph
      (oneChip (strandVertex B α ⟨p, by omega⟩) -
        oneChip (strandVertex B α ⟨1, by
          have := B.length_pos α; omega⟩))
      (oneChip (strandVertex B α ⟨p - 1, by omega⟩) -
        oneChip (leftEndpoint B)) := by
  have hp := strand_prefix_linearEquiv B α ⟨p, by omega⟩
  have hpPrev := strand_prefix_linearEquiv B α ⟨p - 1, by omega⟩
  have hStep := linearEquiv_sub hp hpPrev
  have hStepSymm := hStep.symm
  have hpPred : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  unfold linearEquiv at hStepSymm ⊢
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
    linearEquiv B.graph
      (oneChip (strandVertex B β ⟨q, by omega⟩) -
        oneChip (strandVertex B β ⟨B.length β - 1, by
          have := B.length_pos β; omega⟩))
      (oneChip (strandVertex B β ⟨q + 1, by omega⟩) -
        oneChip (rightEndpoint B)) := by
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
      linearEquiv B.graph
        ((q : ℤ) •
            (oneChip (strandVertex B β ⟨1, by
              have := B.length_pos β; omega⟩) - oneChip (leftEndpoint B)) -
          ((B.length β - 1 : ℕ) : ℤ) •
            (oneChip (strandVertex B β ⟨1, by
              have := B.length_pos β; omega⟩) - oneChip (leftEndpoint B)))
        (((q + 1 : ℕ) : ℤ) •
            (oneChip (strandVertex B β ⟨1, by
              have := B.length_pos β; omega⟩) - oneChip (leftEndpoint B)) -
          (B.length β : ℤ) •
            (oneChip (strandVertex B β ⟨1, by
              have := B.length_pos β; omega⟩) - oneChip (leftEndpoint B))) := by
    unfold linearEquiv
    convert (principalDivisors B.graph).zero_mem using 1
    ext z
    simp only [Pi.sub_apply, Pi.smul_apply]
    push_cast
    rw [hLength]
    ring_nf
    simp
  have h := hLeft.symm.trans (hScalars.trans hRight)
  unfold linearEquiv at h ⊢
  convert h using 1 ; abel

/-- If `b = mN+r`, a multiple of the second off-endpoint mark has the
canonical endpoint-plus-residue representative.  This is the common
`β`-strand calculation behind all three cases of Lemma 4.30. -/
theorem crossOneOff_second_mark_multiple
    {g : ℕ} (B : Banana g) (β : Fin (g + 1)) (b m r : ℕ)
    (hb : b = m * B.length β + r) (hr : r ≤ B.length β) :
    linearEquiv B.graph
      ((b : ℤ) • oneChip
        (strandVertex B β ⟨B.length β - 1, by
          have := B.length_pos β; omega⟩))
      (((m : ℤ) + 1) • oneChip (leftEndpoint B) +
        ((b : ℤ) - (m : ℤ)) • oneChip (rightEndpoint B) -
          oneChip (strandVertex B β ⟨r, by omega⟩)) := by
  let e : CFDiv B.graph :=
    oneChip (strandVertex B β ⟨1, by
      have := B.length_pos β; omega⟩) - oneChip (leftEndpoint B)
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
  have hMiddle : linearEquiv B.graph
      ((b : ℤ) • ((B.length β - 1 : ℕ) : ℤ) • e)
      (((b : ℤ) - (m : ℤ)) •
          (oneChip (rightEndpoint B) - oneChip (leftEndpoint B)) -
        (oneChip (strandVertex B β ⟨r, by omega⟩) -
          oneChip (leftEndpoint B))) := by
    convert hCombined using 1 ;
      ext z ;
      simp only [e, smul_sub, smul_smul, Pi.smul_apply, Pi.sub_apply,
        ] ;
      rw [hCoefficient] ;
      ring
  have hDifference : linearEquiv B.graph
      ((b : ℤ) •
        (oneChip
          (strandVertex B β ⟨B.length β - 1, by
            have := B.length_pos β; omega⟩) - oneChip (leftEndpoint B)))
      (((b : ℤ) - (m : ℤ)) •
          (oneChip (rightEndpoint B) - oneChip (leftEndpoint B)) -
        (oneChip (strandVertex B β ⟨r, by omega⟩) -
          oneChip (leftEndpoint B))) := by
    exact hPenultimateScaled.symm.trans hMiddle
  unfold linearEquiv at hDifference ⊢
  convert hDifference using 1 ;
    simp only [smul_sub   ] ;
    ring

/-- The common corrected firing identity for the cross-one-off marking. -/
theorem crossOneOff_firing_identity
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1)) (a b m r : ℕ)
    (ha : a ≤ B.length α) (hb : b = m * B.length β + r)
    (hr : r ≤ B.length β) :
    linearEquiv B.graph
      ((g : ℤ) • oneChip (rightEndpoint B) +
        (a : ℤ) • oneChip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        (b : ℤ) • oneChip
          (strandVertex B β ⟨B.length β - 1, by
            have := B.length_pos β; omega⟩))
      (((a : ℤ) - (m : ℤ) - 2) • oneChip (leftEndpoint B) +
        ((g : ℤ) + (m : ℤ) - (b : ℤ)) •
          oneChip (rightEndpoint B) +
        oneChip (strandVertex B α ⟨a, by omega⟩) +
        oneChip (strandVertex B β ⟨r, by omega⟩)) := by
  have hFirst := crossOneOff_first_mark_multiple B α a ha
  have hSecond := crossOneOff_second_mark_multiple B β b m r hb hr
  unfold linearEquiv at hFirst hSecond ⊢
  have h := (principalDivisors B.graph).sub_mem hFirst hSecond
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
    linearEquiv B.graph
      ((g : ℤ) • oneChip (rightEndpoint B) +
        ((m + 1 : ℕ) : ℤ) • oneChip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        (b : ℤ) • oneChip
          (strandVertex B β ⟨B.length β - 1, by
            have := B.length_pos β; omega⟩))
      (oneChip (strandVertex B α ⟨m + 1, by omega⟩) +
        ((g : ℤ) + (m : ℤ) - (b : ℤ)) •
          oneChip (rightEndpoint B)) := by
  have h := crossOneOff_firing_identity B α β (m + 1) b m 0 ha
    (by simp [hb]) (by omega)
  rw [strandVertex_zero B β] at h
  unfold linearEquiv at h ⊢
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
    linearEquiv B.graph
      ((g : ℤ) • oneChip (rightEndpoint B) +
        ((g + m : ℕ) : ℤ) • oneChip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        (b : ℤ) • oneChip
          (strandVertex B β ⟨B.length β - 1, by
            have := B.length_pos β; omega⟩))
      (((g : ℤ) - 1) • oneChip (leftEndpoint B) +
        ((g : ℤ) - (m : ℤ) * ((B.length β : ℤ) - 1)) •
          oneChip (rightEndpoint B) +
        oneChip (strandVertex B α ⟨g + m, by omega⟩) +
        oneChip
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
  unfold linearEquiv at h ⊢
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
    linearEquiv B.graph
      ((g : ℤ) • oneChip (rightEndpoint B) +
        ((g + 2 * m + 2 - b : ℕ) : ℤ) • oneChip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        (b : ℤ) • oneChip
          (strandVertex B β ⟨B.length β - 1, by omega⟩))
      (((g : ℤ) + (m : ℤ) - (b : ℤ)) •
          (oneChip (leftEndpoint B) + oneChip (rightEndpoint B)) +
        oneChip
          (strandVertex B α ⟨g + 2 * m + 2 - b, by omega⟩) +
        oneChip (strandVertex B β ⟨r, by omega⟩)) := by
  have h := crossOneOff_firing_identity B α β
    (g + 2 * m + 2 - b) b m r ha hb (by omega)
  have hCandidateCast : ((g + 2 * m + 2 - b : ℕ) : ℤ) =
      (g : ℤ) + 2 * (m : ℤ) + 2 - (b : ℤ) := by
    omega
  unfold linearEquiv at h ⊢
  convert h using 1 ;
    ext z ;
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply] ;
    rw [hCandidateCast] ;
    ring

end Bananas
