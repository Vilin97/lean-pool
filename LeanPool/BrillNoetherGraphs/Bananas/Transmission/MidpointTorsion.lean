/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Classification.CorrectedMidpointKGeneral
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaNonrecurrence
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffResidueDelta

/-!
# The midpoint torsion bound

The revised paper lemma `lem-midpointTorsion` excludes every positive even
period through `2g - 2`, and hence every positive period below `g`, for a
length-two midpoint paired with a non-midpoint on another strand.

We use the paper's quotient/remainder reduction and Dhar argument, via the
existing reduced banana normal forms. Reducing at either endpoint also handles
the reflected case without choosing an orientation. In fact the even-period
argument only needs the first mark to be a midpoint, of any strand length.
-/

namespace Bananas

open Utilities

private theorem linear_equiv_zsmul {G : CFGraph} {D E : CFDiv G}
    (h : linear_equiv G D E) (n : ℤ) :
    linear_equiv G (n • D) (n • E) := by
  unfold linear_equiv at h ⊢
  simpa [smul_sub] using (principal_divisors G).zsmul_mem h n

private theorem zero_isSemibreak {g : ℕ} (B : Banana g) : IsSemibreak B 0 := by
  refine ⟨fun _ => none, ?_⟩
  funext z
  rcases z with core | ⟨γ, offset⟩
  · rfl
  · simp [semibreakDivisor]

/-- A normal form with a negative endpoint coefficient is not principal,
provided the other endpoint and semibreak chips lie in the reduced range. -/
private theorem normalForm_not_linearEquiv_zero {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (h : (a < 0 ∧ 0 ≤ b ∧ b + deg E ≤ g) ∨
      (b < 0 ∧ 0 ≤ a ∧ a + deg E ≤ g)) :
    ¬ linear_equiv B.graph (bananaNormalForm B a b E) 0 := by
  intro heq
  have hRank : rank B.graph (bananaNormalForm B a b E) = -1 := by
    rcases h with ⟨ha, hb, hdeg⟩ | ⟨hb, ha, hdeg⟩
    · exact (rank_bananaNormalForm_neg_iff B a b E hE hb hdeg).2 ha
    · apply rank_eq_neg_one_of_qReduced_debt B.graph (rightEndpoint B)
        _ (q_reduced_bananaNormalForm_right B a b E hE ha hdeg)
      simpa only [bananaNormalForm_rightEndpoint B a b E hE] using hb
  rw [rank_eq_of_linear_equiv B.graph heq, zero_divisor_rank] at hRank
  omega

/-- The even-period midpoint bound, including either side of the second
strand's midpoint. The first marked strand need not have length two. -/
theorem midpoint_not_linearEquiv_even_multiple
    {g k : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : 2 * i.val = B.length α) (hj : B.IsInteriorPosition β j)
    (hmid : 2 * j.val ≠ B.length β)
    (hk : 0 < k) (heven : Even k) (hbound : k ≤ 2 * g - 2) :
    ¬ linear_equiv B.graph
      ((k : ℤ) • one_chip (strandVertex B α i))
      ((k : ℤ) • one_chip (strandVertex B β j)) := by
  obtain ⟨t, rfl⟩ := heven
  have ht : 0 < t := by omega
  have htg : t < g := by omega
  let q := (t + t) * j.val / B.length β
  let r := (t + t) * j.val % B.length β
  have hr : r < B.length β := Nat.mod_lt _ (B.length_pos β)
  let p : B.PathPosition β := ⟨r, by omega⟩
  have hdiv : (t + t) * j.val = q * B.length β + r := by
    simpa [q, r, Nat.mul_comm] using (Nat.div_add_mod ((t + t) * j.val) (B.length β)).symm
  have hq : q < t + t := by
    dsimp [q]
    exact (Nat.div_lt_iff_lt_mul (B.length_pos β)).2
      (Nat.mul_lt_mul_of_pos_left hj.2 (by omega))
  have hdivZ : ((t : ℤ) + t) * j.val = (q : ℤ) * B.length β + r := by
    exact_mod_cast hdiv
  have htZ : (0 : ℤ) < t := by exact_mod_cast ht
  have htgZ : (t : ℤ) < g := by exact_mod_cast htg
  have hqZ : (q : ℤ) < t + t := by exact_mod_cast hq
  have hqNonneg : (0 : ℤ) ≤ q := Nat.cast_nonneg q
  have hmidrel := linear_equiv_zsmul
    (two_smul_strand_midpoint_linearEquiv_endpoints B α i hi) (t : ℤ)
  have hprefix := strand_multiple_prefix_normalForm_linearEquiv B β j p (t + t) q hdiv
  intro heq
  -- For k = 2t, the marked difference is equivalent to
  -- (t - q - 1)L + (q - t)R + v_{β,r}.
  have hprincipal : linear_equiv B.graph
      (bananaNormalForm B ((t : ℤ) - q - 1) ((q : ℤ) - t)
        (one_chip (strandVertex B β p))) 0 := by
    unfold linear_equiv at hmidrel hprefix heq ⊢
    have h := (principal_divisors B.graph).sub_mem
      ((principal_divisors B.graph).sub_mem hmidrel heq) hprefix
    convert h using 1
    simp only [bananaNormalForm, Nat.cast_add, smul_sub, smul_add, smul_smul]
    module
  by_cases hrzero : r = 0
  -- When the remainder is zero, its chip belongs to L, not the semibreak part.
  · have hp : p = ⟨0, by omega⟩ := Fin.ext hrzero
    rw [hp, strandVertex_zero] at hprincipal
    have hform : bananaNormalForm B ((t : ℤ) - q - 1) ((q : ℤ) - t)
        (one_chip (leftEndpoint B)) =
        bananaNormalForm B ((t : ℤ) - q) ((q : ℤ) - t) 0 := by
      unfold bananaNormalForm
      module
    rw [hform] at hprincipal
    have hqt : q ≠ t := by
      intro h
      rw [h, hrzero] at hdivZ
      have he : (2 : ℤ) * j.val = B.length β := by nlinarith
      exact hmid (by exact_mod_cast he)
    apply normalForm_not_linearEquiv_zero B _ _ 0 (zero_isSemibreak B) _ hprincipal
    simp only [map_zero]
    rcases lt_or_gt_of_ne hqt with hlt | hgt
    · right
      have : (q : ℤ) < t := by exact_mod_cast hlt
      constructor <;> omega
    · left
      have : (t : ℤ) < q := by exact_mod_cast hgt
      constructor <;> omega
  · have hpInt : B.IsInteriorPosition β p := ⟨Nat.pos_of_ne_zero hrzero, hr⟩
    apply normalForm_not_linearEquiv_zero B _ _ _
      (isSemibreak_one_strand_chip B β p hpInt) _ hprincipal
    rw [deg_one_chip]
    by_cases hqt : q < t
    -- Burn from R below the midpoint, and from L above it.
    · right
      have : (q : ℤ) < t := by exact_mod_cast hqt
      constructor <;> omega
    · left
      have : (t : ℤ) ≤ q := by exact_mod_cast (Nat.le_of_not_gt hqt)
      constructor <;> omega

/-- Doubling a putative period gives the second assertion of
`lem-midpointTorsion`, without an evenness assumption. -/
theorem midpoint_not_linearEquiv_small_multiple
    {g k : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : 2 * i.val = B.length α) (hj : B.IsInteriorPosition β j)
    (hmid : 2 * j.val ≠ B.length β) (hk : 0 < k) (hbound : k < g) :
    ¬ linear_equiv B.graph
      ((k : ℤ) • one_chip (strandVertex B α i))
      ((k : ℤ) • one_chip (strandVertex B β j)) := by
  intro heq
  have hdouble := linear_equiv_zsmul heq (2 : ℤ)
  apply midpoint_not_linearEquiv_even_multiple B α β i j hi hj hmid
    (by omega : 0 < 2 * k) (even_two_mul k) (by omega)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, smul_smul] using hdouble

/-- The length-two branch of Proposition 4.19, now deduced from the stronger
midpoint lemma rather than initial-slope estimates. -/
theorem length_two_cross_torsion_dichotomy
    {g k : ℕ} (_hg : 1 ≤ g) (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β)
    (hαβ : α ≠ β) (_hiInt : B.IsInteriorPosition α i)
    (hjInt : B.IsInteriorPosition β j)
    (hαLen : B.length α = 2) (hi : i.val = 1)
    (hTO : IsTorsionOrder
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k) :
    (CorrectedMidpointException B α β i j ∧ k = 2) ∨ g ≤ k := by
  have hiMid : 2 * i.val = B.length α := by omega
  by_cases hjMid : 2 * j.val = B.length β
  · have hException : CorrectedMidpointException B α β i j :=
      ⟨hαβ, hiMid, hjMid, Or.inl hαLen⟩
    have hTwo := correctedMidpointException_torsionOrder_two B α β i j hException
    exact Or.inl ⟨hException, Nat.le_antisymm (hTO.2 2 hTwo.1) (hTwo.2 k hTO.1)⟩
  · right
    by_contra hlt
    apply midpoint_not_linearEquiv_small_multiple B α β i j hiMid hjInt hjMid
      hTO.1.1 (by omega)
    have h := hTO.1.2
    change linear_equiv B.graph
      ((k : ℤ) • (one_chip (strandVertex B α i) - one_chip (strandVertex B β j))) 0 at h
    unfold linear_equiv at h ⊢
    convert h using 1
    module

end Bananas
