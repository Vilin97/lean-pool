/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaPrefix
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaArithmetic

/-! # Theta Residue -/

namespace Bananas

open Utilities

private theorem linear_equiv_zsmul {G : CFGraph} {D E : CFDiv G}
    (h : linearEquiv G D E) (q : ℤ) :
    linearEquiv G (q • D) (q • E) := by
  unfold linearEquiv at h ⊢
  have hq := AddSubgroup.zsmul_mem (principalDivisors G) h q
  simpa [smul_sub] using hq

private theorem linear_equiv_sub_common {G : CFGraph} {D E F : CFDiv G}
    (h : linearEquiv G D E) :
    linearEquiv G (D - F) (E - F) := by
  unfold linearEquiv at h ⊢
  convert h using 1 ; abel

/-! Paper source: `eq:multDiffMarkedPts` and `cor:evenlyMarkedKGT`.
The one-strand prefix identity, together with the common reduced ratio,
already gives the multi-strand annihilation at the gcd period. -/
/- TeX label: `eq:multDiffMarkedPts` / `cor:evenlyMarkedKGT`. -/
theorem evenlyMarkedTheta_multiple_principal
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hEven : EvenlyMarkedTheta B α β i j) :
    linearEquiv B.graph
      (((B.length α / Nat.gcd (B.length α) i.val : ℕ) : ℤ) •
        (oneChip (strandVertex B α i) -
          oneChip (strandVertex B β j))) 0 := by
  rcases hEven with ⟨hαβ, hi, hiLt, hj, hjLt, hcross⟩
  let k : ℕ := B.length α / Nat.gcd (B.length α) i.val
  let q : ℕ := i.val / Nat.gcd (B.length α) i.val
  have hkA : k * i.val = q * B.length α := by
    dsimp [k, q]
    have hg := Nat.gcd_dvd_left (B.length α) i.val
    have hi' := Nat.gcd_dvd_right (B.length α) i.val
    have hA := Nat.div_mul_cancel hg
    have hi'' := Nat.div_mul_cancel hi'
    calc
      (B.length α / Nat.gcd (B.length α) i.val) * i.val =
          (B.length α / Nat.gcd (B.length α) i.val) *
            ((i.val / Nat.gcd (B.length α) i.val) * Nat.gcd (B.length α) i.val) := by
              rw [hi'']
      _ = (i.val / Nat.gcd (B.length α) i.val) *
            ((B.length α / Nat.gcd (B.length α) i.val) * Nat.gcd (B.length α) i.val) := by ac_rfl
      _ = (i.val / Nat.gcd (B.length α) i.val) * B.length α := by rw [hA]
  have hqEq : q = j.val / Nat.gcd (B.length β) j.val :=
    evenlyMarkedTheta_reduced_coordinates_eq B α β i j
      ⟨hαβ, hi, hiLt, hj, hjLt, hcross⟩
  have hkEq : k = B.length β / Nat.gcd (B.length β) j.val :=
    evenlyMarkedTheta_gcd_quotients_eq B α β i j
      ⟨hαβ, hi, hiLt, hj, hjLt, hcross⟩
  have hPrefixA := strand_prefix_linearEquiv B α i
  have hEndA := strand_prefix_linearEquiv B α
    ⟨B.length α, by omega⟩
  have hA1 := linear_equiv_zsmul hPrefixA (k : ℤ)
  have hA2 := linear_equiv_zsmul hEndA (q : ℤ)
  have hA : linearEquiv B.graph
      ((k : ℤ) •
        (oneChip (strandVertex B α i) - oneChip (leftEndpoint B)))
      ((q : ℤ) •
        (oneChip (rightEndpoint B) - oneChip (leftEndpoint B))) := by
    have hA2' : linearEquiv B.graph
        ((q : ℤ) •
          ((B.length α : ℤ) •
            (oneChip (strandVertex B α ⟨1, by omega⟩) -
              oneChip (leftEndpoint B))))
        ((q : ℤ) •
          (oneChip (rightEndpoint B) - oneChip (leftEndpoint B))) := by
      simpa [smul_smul, strandVertex_length] using hA2
    have hScale :
        (q : ℤ) • ((B.length α : ℤ) •
          (oneChip (strandVertex B α ⟨1, by omega⟩) -
            oneChip (leftEndpoint B))) =
          (k : ℤ) • ((i.val : ℤ) •
            (oneChip (strandVertex B α ⟨1, by omega⟩) -
              oneChip (leftEndpoint B))) := by
      rw [smul_smul, smul_smul]
      congr 1
      exact_mod_cast hkA.symm
    rw [hScale] at hA2'
    have hChain := hA1.symm.trans hA2'
    simpa [smul_smul] using hChain
  have hB : linearEquiv B.graph
      ((k : ℤ) •
        (oneChip (strandVertex B β j) - oneChip (leftEndpoint B)))
      ((q : ℤ) •
        (oneChip (rightEndpoint B) - oneChip (leftEndpoint B))) := by
    have hqB : q = j.val / Nat.gcd (B.length β) j.val := hqEq
    have hB1 := linear_equiv_zsmul (strand_prefix_linearEquiv B β j) (k : ℤ)
    have hB2 := linear_equiv_zsmul
      (strand_prefix_linearEquiv B β ⟨B.length β, by omega⟩)
      ((j.val / Nat.gcd (B.length β) j.val : ℕ) : ℤ)
    have hkB : k * j.val =
        (j.val / Nat.gcd (B.length β) j.val) * B.length β := by
      dsimp [k]
      have hg := Nat.gcd_dvd_left (B.length α) i.val
      have hj' := Nat.gcd_dvd_right (B.length α) i.val
      have hLen := Nat.div_mul_cancel hg
      have hj'' := Nat.div_mul_cancel hj'
      apply Nat.mul_left_cancel
        (Nat.gcd_pos_of_pos_left _ (B.length_pos α))
      calc
        Nat.gcd (B.length α) i.val *
              ((B.length α / Nat.gcd (B.length α) i.val) * j.val) =
            ((B.length α / Nat.gcd (B.length α) i.val) *
              Nat.gcd (B.length α) i.val) * j.val := by ac_rfl
        _ = B.length α * j.val := by rw [hLen]
        _ = i.val * B.length β := by simpa [Nat.mul_comm] using hcross.symm
        _ = ((i.val / Nat.gcd (B.length α) i.val) *
              Nat.gcd (B.length α) i.val) * B.length β := by rw [hj'']
        _ = Nat.gcd (B.length α) i.val *
              ((i.val / Nat.gcd (B.length α) i.val) * B.length β) := by ac_rfl
        _ = Nat.gcd (B.length α) i.val *
              ((j.val / Nat.gcd (B.length β) j.val) * B.length β) := by
                rw [← hqEq]
    have hB2' : linearEquiv B.graph
        ((q : ℤ) •
          ((B.length β : ℤ) •
            (oneChip (strandVertex B β ⟨1, by omega⟩) -
              oneChip (leftEndpoint B))))
        ((q : ℤ) •
          (oneChip (rightEndpoint B) - oneChip (leftEndpoint B))) := by
      simpa [hqB, smul_smul, strandVertex_length] using hB2
    have hScaleB :
        (q : ℤ) • ((B.length β : ℤ) •
          (oneChip (strandVertex B β ⟨1, by omega⟩) -
            oneChip (leftEndpoint B))) =
          (k : ℤ) • ((j.val : ℤ) •
            (oneChip (strandVertex B β ⟨1, by omega⟩) -
              oneChip (leftEndpoint B))) := by
      rw [smul_smul, smul_smul]
      congr 1
      rw [hqB]
      exact_mod_cast hkB.symm
    rw [hScaleB] at hB2'
    have hChain := hB1.symm.trans hB2'
    simpa [smul_smul, hqB] using hChain
  have hAB := hA.trans hB.symm
  have hZero := linear_equiv_sub_common (F :=
    (k : ℤ) • (oneChip (strandVertex B β j) - oneChip (leftEndpoint B))) hAB
  unfold linearEquiv at hZero ⊢
  simpa [k, smul_sub, sub_eq_add_neg] using hZero

end Bananas
