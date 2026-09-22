/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaGenusTwoCornerSum
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionAPI

/-!
# The exact genus-two inversion formula, with its correction term

`ThetaGenusTwoCornerSum.lean` reduces `inv_k(τ_D)` to three finite degree
slices and then evaluates them *under the rigidity hypothesis* `u + v ≁ K_G`,
which makes the residual degree-two product vanish pointwise.  This file
evaluates that residual product instead of discarding it, and so proves the
paper's Lemma 4.10 (`lem:invtau`) as stated:

`inv_k(τ_D) = # {[D'] ∈ T¹_D : |D'| ≠ ∅} + δ(0 ∈ T⁰_D and u + v ∼ K_G)`.

The correction term is `invTauCorrection`.  Two facts pin it down: each
factor of the residual product is the principality indicator of a
*degree-zero* divisor, and exact torsion makes at most one residue in a
fundamental period principal.  The upshot is that the whole cyclic sum of
residual products is `0` or `1`, and is `1` exactly under the paper's
conjunction.

The converse half of `thm:kgtThetas` (Theorem 4.8) is then immediate: apply
the formula to `D = w` for a vertex `w` and read the bound `inv_k ≤ g = 2`
backwards.
-/

namespace Bananas

open Utilities

/-! ## Generic divisor bookkeeping

Everything in this section is stated for an abstract `{G : CFGraph}` with
abstract divisors, so that no downstream use has to run divisor algebra on a
concrete banana. -/

section Generic

variable {G : CFGraph}

/-- `fixedDegreeTwist` and `degreeTwistInt` are the same twist family, the
former carrying its marks as separate arguments. -/
theorem fixedDegreeTwist_eq_degreeTwistInt
    (G : CFGraph) (u v : G.V) (D : CFDiv G) (d b : ℤ) :
    fixedDegreeTwist G u v D d b = degreeTwistInt (mark G u v) D d b := rfl

/-- The degree-two twist is the next degree-zero twist with both marks added
back. -/
theorem fixedDegreeTwist_two_eq_next_zero_add_uv
    (G : CFGraph) (u v : G.V) (D : CFDiv G) (b : ℤ) :
    fixedDegreeTwist G u v D 2 b =
      fixedDegreeTwist G u v D 0 (b + 1) + one_chip u + one_chip v := by
  unfold fixedDegreeTwist
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- The degree-one twists of a single chip are its marked-difference
translates. -/
theorem degreeTwistInt_one_chip_one
    (G : CFGraph) (u v w : G.V) (b : ℤ) :
    degreeTwistInt (mark G u v) (one_chip w) 1 b =
      one_chip w + b • (one_chip u - one_chip v) := by
  unfold degreeTwistInt
  change (one_chip w + (1 - deg (one_chip w) + b) • one_chip u -
    b • one_chip v : CFDiv G) = _
  rw [deg_one_chip]
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- A degree twist may be replaced by its Euclidean residue index modulo any
torsion witness. -/
theorem degreeTwistInt_emod_linearEquiv
    {M : TwiceMarked} {k : ℕ} (hk : TorsionWitness M k)
    (D : CFDiv M.graph) (d b : ℤ) :
    linear_equiv M.graph
      (degreeTwistInt M D d b) (degreeTwistInt M D d (b % k)) := by
  rw [degreeTwistInt_eq_zero_add_marked_difference M D d b,
    degreeTwistInt_eq_zero_add_marked_difference M D d (b % k)]
  exact linearEquiv_add_left_of_linearEquiv
    (marked_difference_mod_period_linearEquiv hk b)

/-- Principality of a degree twist depends only on the index modulo a torsion
witness. -/
theorem degreeTwistInt_linearEquiv_zero_of_emod_eq
    {M : TwiceMarked} {k : ℕ} (hk : TorsionWitness M k)
    (D : CFDiv M.graph) (d b c : ℤ) (hmod : b % k = c % k)
    (hc : linear_equiv M.graph (degreeTwistInt M D d c) 0) :
    linear_equiv M.graph (degreeTwistInt M D d b) 0 := by
  have h1 := degreeTwistInt_emod_linearEquiv hk D d b
  have h2 := degreeTwistInt_emod_linearEquiv hk D d c
  rw [hmod] at h1
  exact (h1.trans h2.symm).trans hc

/-- Every twist `D + a·u - b·v` of degree `d` is the degree-`d` twist family
member at index `b`.  Together with the next lemma and
`degreeTwistInt_injective_on_fundamental_period` this says that the finite
family `degreeTwistInt M D d ·` on `Fin k` is a system of representatives for
the paper's set `T^d_D` of degree-`d` twist classes. -/
theorem twist_eq_degreeTwistInt
    (M : TwiceMarked) (D : CFDiv M.graph) (a b d : ℤ)
    (h : deg D + a - b = d) :
    D + a • one_chip M.u - b • one_chip M.v = degreeTwistInt M D d b := by
  have ha : a = d - deg D + b := by omega
  unfold degreeTwistInt
  rw [ha]

/-- Every degree-`d` twist index is represented in one fundamental period. -/
theorem exists_fin_degreeTwistInt_linearEquiv
    {M : TwiceMarked} {k : ℕ} (hk : TorsionWitness M k)
    (D : CFDiv M.graph) (d b : ℤ) :
    ∃ c : Fin k, linear_equiv M.graph
      (degreeTwistInt M D d b) (degreeTwistInt M D d (c : ℤ)) := by
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk.1
  have h0 : 0 ≤ b % k := Int.emod_nonneg _ (by omega)
  have hlt : b % k < k := Int.emod_lt_of_pos _ hkZ
  have hc : (b % k).toNat < k := by
    have := (Int.toNat_lt h0).mpr hlt
    exact_mod_cast this
  refine ⟨⟨(b % k).toNat, hc⟩, ?_⟩
  have hcast : (((b % k).toNat : ℕ) : ℤ) = b % k := Int.toNat_of_nonneg h0
  change linear_equiv M.graph (degreeTwistInt M D d b)
    (degreeTwistInt M D d (((b % k).toNat : ℕ) : ℤ))
  rw [hcast]
  exact degreeTwistInt_emod_linearEquiv hk D d b

/-- With `A` principal, the canonical complement of `A + u + v` is principal
exactly when the marked pair is canonical.  This is the pointwise content of
the paper's correction term. -/
theorem canonical_sub_add_marks_linearEquiv_zero_iff
    {u v : G.V} {A : CFDiv G} (hA : linear_equiv G A 0) :
    linear_equiv G
        (canonical_divisor G - (A + one_chip u + one_chip v)) 0 ↔
      linear_equiv G (one_chip u + one_chip v) (canonical_divisor G) := by
  unfold linear_equiv at hA ⊢
  constructor
  · intro h
    have hSum := AddSubgroup.add_mem (principal_divisors G) h hA
    have hNeg := AddSubgroup.neg_mem (principal_divisors G) hSum
    convert hNeg using 1
    abel
  · intro h
    have hNegh := AddSubgroup.neg_mem (principal_divisors G) h
    have hNegA := AddSubgroup.neg_mem (principal_divisors G) hA
    have hSum := AddSubgroup.add_mem (principal_divisors G) hNegh hNegA
    convert hSum using 1
    abel

/-- A product of two degree-zero multiplicities is one when both divisors are
principal and zero otherwise. -/
theorem rankPlusOne_mul_eq_one_of_linearEquiv_zero
    (A Y : CFDiv G) (hA : deg A = 0) (hY : deg Y = 0)
    (h1 : linear_equiv G A 0) (h2 : linear_equiv G Y 0) :
    rankPlusOne G A * rankPlusOne G Y = 1 := by
  have e1 : rankPlusOne G A = 1 :=
    (rank_add_one_eq_one_iff_linearEquiv_zero_of_degree_zero G A hA).mpr h1
  have e2 : rankPlusOne G Y = 1 :=
    (rank_add_one_eq_one_iff_linearEquiv_zero_of_degree_zero G Y hY).mpr h2
  rw [e1, e2]
  norm_num

/-- If either factor of a degree-zero multiplicity product is nonprincipal,
the product vanishes. -/
theorem rankPlusOne_mul_eq_zero_of_not_linearEquiv_zero_left
    (A Y : CFDiv G) (hA : deg A = 0) (h1 : ¬ linear_equiv G A 0) :
    rankPlusOne G A * rankPlusOne G Y = 0 := by
  rw [rankPlusOne_eq_zero_of_degree_zero_not_principal G A hA h1, zero_mul]

theorem rankPlusOne_mul_eq_zero_of_not_linearEquiv_zero_right
    (A Y : CFDiv G) (hY : deg Y = 0) (h2 : ¬ linear_equiv G Y 0) :
    rankPlusOne G A * rankPlusOne G Y = 0 := by
  rw [rankPlusOne_eq_zero_of_degree_zero_not_principal G Y hY h2, mul_zero]

end Generic

/-! ## The correction term -/

open Classical in
/-- Paper source: the second summand of `lem:invtau` (Lemma 4.10),
`δ(0 ∈ T⁰_D and u + v ∼ K_G)`.

`0 ∈ T⁰_D` says some degree-zero twist of `D` is principal; the second
conjunct is the failure of the paper's rigidity condition (in genus two,
`r(u+v) = 0` is equivalent to `u + v ≁ K_G`). -/
noncomputable def invTauCorrection (M : TwiceMarked) (D : CFDiv M.graph) : ℤ :=
  if (∃ b : ℤ, linear_equiv M.graph (degreeTwistInt M D 0 b) 0) ∧
      linear_equiv M.graph (one_chip M.u + one_chip M.v)
        (canonical_divisor M.graph)
    then 1 else 0

open Classical in
/-- `rfl`-wrapper: the correction term at an explicitly marked graph, stated
without the `TwiceMarked` projections so that `rw` fires on it. -/
theorem invTauCorrection_mark (G : CFGraph) (u v : G.V) (D : CFDiv G) :
    invTauCorrection (mark G u v) D =
      if (∃ b : ℤ, linear_equiv G (degreeTwistInt (mark G u v) D 0 b) 0) ∧
          linear_equiv G (one_chip u + one_chip v) (canonical_divisor G)
        then 1 else 0 := rfl

/-- Rigid markings have no correction. -/
theorem invTauCorrection_eq_zero_of_not_mark_pair_canonical
    (M : TwiceMarked) (D : CFDiv M.graph)
    (hRigid : ¬ linear_equiv M.graph (one_chip M.u + one_chip M.v)
      (canonical_divisor M.graph)) :
    invTauCorrection M D = 0 := by
  unfold invTauCorrection
  rw [if_neg]
  rintro ⟨-, hCanon⟩
  exact hRigid hCanon

/-- The canonical complement of a degree-two twist has degree zero. -/
theorem deg_canonical_sub_fixedDegreeTwist_two
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph) (b : ℤ) :
    deg (canonical_divisor B.graph -
      fixedDegreeTwist B.graph u v D 2 b) = 0 := by
  rw [deg.map_sub, degree_of_canonical_divisor, B.genus_graph,
    deg_fixedDegreeTwist]
  norm_num

/-- Two principal degree-zero twists in one fundamental period, at indices
shifted by one, have the same index. -/
theorem fin_eq_of_shifted_degreeTwist_linearEquiv_zero
    {B : Banana 2} {u v : B.graph.V} {D : CFDiv B.graph} {k : ℕ}
    (hk : IsTorsionOrder (mark B.graph u v) k) {b c : Fin k}
    (hb : linear_equiv B.graph
      (fixedDegreeTwist B.graph u v D 0 ((b : ℤ) + 1)) 0)
    (hc : linear_equiv B.graph
      (fixedDegreeTwist B.graph u v D 0 ((c : ℤ) + 1)) 0) :
    b = c := by
  have hbc : linear_equiv B.graph
      (degreeTwistInt (mark B.graph u v) D 0 ((b : ℤ) + 1))
      (degreeTwistInt (mark B.graph u v) D 0 ((c : ℤ) + 1)) := by
    exact hb.trans hc.symm
  have hDvd := isTorsionOrder_dvd_natAbs_sub_of_degreeTwistInt_linearEquiv
    hk D 0 ((b : ℤ) + 1) ((c : ℤ) + 1) hbc
  have hbLt : (b : ℤ) < k := by exact_mod_cast b.isLt
  have hcLt : (c : ℤ) < k := by exact_mod_cast c.isLt
  have hb0 : (0 : ℤ) ≤ (b : ℤ) := by positivity
  have hc0 : (0 : ℤ) ≤ (c : ℤ) := by positivity
  by_contra hne
  have hDiff : ((b : ℤ) + 1) - ((c : ℤ) + 1) ≠ 0 := by
    intro h
    exact hne (Fin.ext (by exact_mod_cast (by omega : (b : ℤ) = (c : ℤ))))
  have hPos : 0 < (((b : ℤ) + 1) - ((c : ℤ) + 1)).natAbs :=
    Int.natAbs_pos.mpr hDiff
  have hkLe : k ≤ (((b : ℤ) + 1) - ((c : ℤ) + 1)).natAbs :=
    Nat.le_of_dvd hPos hDvd
  have hLt : ((((b : ℤ) + 1) - ((c : ℤ) + 1)).natAbs : ℤ) < k := by
    rw [Int.natCast_natAbs, abs_lt]
    omega
  have hkLe' : (k : ℤ) ≤ ((((b : ℤ) + 1) - ((c : ℤ) + 1)).natAbs : ℤ) := by
    exact_mod_cast hkLe
  omega

/-- The residual degree-two products of the genus-two telescoping sum add up
to exactly the paper's correction term. -/
theorem sum_correctionProduct_eq_invTauCorrection
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph) (k : ℕ)
    (hk : IsTorsionOrder (mark B.graph u v) k) :
    ∑ b : Fin k,
        rankPlusOne B.graph
            (fixedDegreeTwist B.graph u v D 0 ((b : ℤ) + 1)) *
          rankPlusOne B.graph (canonical_divisor B.graph -
            fixedDegreeTwist B.graph u v D 2 (b : ℤ)) =
      invTauCorrection (mark B.graph u v) D := by
  classical
  have hDegA : ∀ b : ℤ,
      deg (fixedDegreeTwist B.graph u v D 0 b) = 0 := by
    intro b
    exact deg_fixedDegreeTwist B.graph u v D 0 b
  have hDegY : ∀ b : ℤ,
      deg (canonical_divisor B.graph -
        fixedDegreeTwist B.graph u v D 2 b) = 0 :=
    deg_canonical_sub_fixedDegreeTwist_two B u v D
  -- The residual product at index `b` reduces to a conjunction of
  -- principality statements.
  have hYiff : ∀ b : ℤ,
      linear_equiv B.graph (fixedDegreeTwist B.graph u v D 0 (b + 1)) 0 →
        (linear_equiv B.graph (canonical_divisor B.graph -
            fixedDegreeTwist B.graph u v D 2 b) 0 ↔
          linear_equiv B.graph (one_chip u + one_chip v)
            (canonical_divisor B.graph)) := by
    intro b hA
    rw [fixedDegreeTwist_two_eq_next_zero_add_uv]
    exact canonical_sub_add_marks_linearEquiv_zero_iff hA
  by_cases hCond :
      (∃ b : ℤ, linear_equiv B.graph
        (degreeTwistInt (mark B.graph u v) D 0 b) 0) ∧
      linear_equiv B.graph (one_chip u + one_chip v)
        (canonical_divisor B.graph)
  · obtain ⟨⟨b₀, hb₀⟩, hUV⟩ := hCond
    have hkPos : 0 < k := hk.1.1
    have hkZ : (0 : ℤ) < k := by exact_mod_cast hkPos
    -- Move the witness index into the fundamental period, shifted by one.
    have hRes0 : 0 ≤ (b₀ - 1) % k := Int.emod_nonneg _ (by omega)
    have hResLt : (b₀ - 1) % k < k := Int.emod_lt_of_pos _ hkZ
    have hcLt : ((b₀ - 1) % k).toNat < k := by
      have := (Int.toNat_lt hRes0).mpr hResLt
      exact_mod_cast this
    have hval : ((((b₀ - 1) % k).toNat : ℤ) + 1) % k = b₀ % k := by
      rw [Int.toNat_of_nonneg hRes0, Int.emod_add_emod]
      congr 1
      ring
    have hA : linear_equiv B.graph
        (fixedDegreeTwist B.graph u v D 0
          ((((b₀ - 1) % k).toNat : ℤ) + 1)) 0 :=
      degreeTwistInt_linearEquiv_zero_of_emod_eq hk.1 D 0 _ b₀ hval hb₀
    refine (Finset.sum_eq_single (⟨((b₀ - 1) % k).toNat, hcLt⟩ : Fin k)
      ?_ ?_).trans ?_
    · -- every other index has a nonprincipal degree-zero twist
      intro b _ hbne
      apply rankPlusOne_mul_eq_zero_of_not_linearEquiv_zero_left
        _ _ (hDegA _)
      intro hb
      exact hbne (fin_eq_of_shifted_degreeTwist_linearEquiv_zero hk hb hA)
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
    · -- the surviving index contributes one
      have hY : linear_equiv B.graph (canonical_divisor B.graph -
          fixedDegreeTwist B.graph u v D 2 (((b₀ - 1) % k).toNat : ℤ)) 0 :=
        (hYiff _ hA).mpr hUV
      have hOne := rankPlusOne_mul_eq_one_of_linearEquiv_zero
        (fixedDegreeTwist B.graph u v D 0
          ((((b₀ - 1) % k).toNat : ℤ) + 1))
        (canonical_divisor B.graph -
          fixedDegreeTwist B.graph u v D 2 (((b₀ - 1) % k).toNat : ℤ))
        (hDegA _) (hDegY _) hA hY
      rw [hOne, invTauCorrection_mark, if_pos ⟨⟨b₀, hb₀⟩, hUV⟩]
  · -- no correction: every residual product vanishes
    have hZero : ∀ b : Fin k,
        rankPlusOne B.graph
            (fixedDegreeTwist B.graph u v D 0 ((b : ℤ) + 1)) *
          rankPlusOne B.graph (canonical_divisor B.graph -
            fixedDegreeTwist B.graph u v D 2 (b : ℤ)) = 0 := by
      intro b
      by_cases hA : linear_equiv B.graph
          (fixedDegreeTwist B.graph u v D 0 ((b : ℤ) + 1)) 0
      · apply rankPlusOne_mul_eq_zero_of_not_linearEquiv_zero_right
          _ _ (hDegY _)
        intro hY
        exact hCond ⟨⟨(b : ℤ) + 1, hA⟩, (hYiff _ hA).mp hY⟩
      · exact rankPlusOne_mul_eq_zero_of_not_linearEquiv_zero_left
          _ _ (hDegA _) hA
    rw [Finset.sum_congr rfl (fun b _ => hZero b), invTauCorrection_mark,
      if_neg hCond]
    simp

/-- Paper source: `lem:invtau` (Lemma 4.10), in full, with its correction
term.

For a theta graph with any two marks, an exact torsion order `k` and any
divisor `D` admitting a `k`-affine transmission permutation, the number of
`k`-inversions is the number of effective degree-one twists of `D` in one
torsion period, plus `δ(0 ∈ T⁰_D and u + v ∼ K_G)`. -/
theorem intCast_kInversionCount_eq_effectiveResidues_add_correction
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph)
    (k : ℕ) (tau : ℤ → ℤ)
    (hk : IsTorsionOrder (mark B.graph u v) k)
    (hTau : IsTransmissionPermutation (mark B.graph u v) D tau)
    (hAffine : IsKAffine k tau) :
    (kInversionCount k tau : ℤ) =
      ((effectiveDegreeOneTwistResidues (mark B.graph u v) D k).ncard : ℤ) +
        invTauCorrection (mark B.graph u v) D := by
  rw [intCast_kInversionCount_eq_sum_threeDegreeTwistContribution
    B u v D k tau hk.1.1 hTau hAffine]
  calc
    ∑ b : Fin k, threeDegreeTwistContribution B.graph u v D (b : ℤ) =
        ∑ b : Fin k,
          (rankPlusOne B.graph
              (fixedDegreeTwist B.graph u v D 1 (b : ℤ)) +
            (rankPlusOne B.graph
                (fixedDegreeTwist B.graph u v D 0 (b : ℤ)) -
              rankPlusOne B.graph
                (fixedDegreeTwist B.graph u v D 0 ((b : ℤ) + 1))) +
            rankPlusOne B.graph
                (fixedDegreeTwist B.graph u v D 0 ((b : ℤ) + 1)) *
              rankPlusOne B.graph (canonical_divisor B.graph -
                fixedDegreeTwist B.graph u v D 2 (b : ℤ))) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [threeDegreeTwistContribution_eq_telescoping]
          ring
    _ = ((∑ b : Fin k, rankPlusOne B.graph
              (fixedDegreeTwist B.graph u v D 1 (b : ℤ))) +
          ∑ b : Fin k,
            (rankPlusOne B.graph
                (fixedDegreeTwist B.graph u v D 0 (b : ℤ)) -
              rankPlusOne B.graph
                (fixedDegreeTwist B.graph u v D 0 ((b : ℤ) + 1)))) +
        ∑ b : Fin k,
          rankPlusOne B.graph
              (fixedDegreeTwist B.graph u v D 0 ((b : ℤ) + 1)) *
            rankPlusOne B.graph (canonical_divisor B.graph -
              fixedDegreeTwist B.graph u v D 2 (b : ℤ)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = ((effectiveDegreeOneTwistResidues (mark B.graph u v) D k).ncard : ℤ) +
        invTauCorrection (mark B.graph u v) D := by
          rw [sum_rankPlusOne_fixedDegreeTwist_zero_sub_next_eq_zero
              B u v D k hk.1,
            sum_rankPlusOne_degreeOne_eq_effectiveResidues_ncard B u v D k,
            sum_correctionProduct_eq_invTauCorrection B u v D k hk]
          ring

/-! ## The converse half of Theorem 4.8 -/

/-- A finite set of size at most two containing a distinguished element has
at most one other element. -/
theorem eq_of_ncard_le_two_of_mem_three
    {α : Type*} [Finite α] {S : Set α} (h : S.ncard ≤ 2)
    {z n m : α} (hz : z ∈ S) (hn : n ∈ S) (hm : m ∈ S)
    (hnz : n ≠ z) (hmz : m ≠ z) : n = m := by
  classical
  by_contra hnm
  have hSub : ({z, n, m} : Set α) ⊆ S := by
    intro x hx
    rcases hx with rfl | hx
    · exact hz
    rcases hx with rfl | hx
    · exact hn
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hm
  have hPair : ({n, m} : Set α).ncard = 2 := Set.ncard_pair hnm
  have hTriple : ({z, n, m} : Set α).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨z, n, m, Ne.symm hnz, Ne.symm hmz, hnm, rfl⟩
  have hLe := Set.ncard_le_ncard hSub (Set.toFinite S)
  omega

/-- The effective degree-one twists of a single chip are exactly the
non-recurrence indices. -/
theorem mem_effectiveDegreeOneTwistResidues_one_chip_iff
    (G : CFGraph) (u v w : G.V) (k : ℕ) (b : Fin k) :
    b ∈ effectiveDegreeOneTwistResidues (mark G u v) (one_chip w) k ↔
      0 ≤ rank G (one_chip w + (b : ℤ) • (one_chip u - one_chip v)) := by
  rw [mem_effectiveDegreeOneTwistResidues_iff,
    degreeTwistInt_one_chip_one]
/-- Paper source: `thm:kgtThetas` (Theorem 4.8), the "only if" direction.

For a rigidly marked theta graph, `k`-general transmission forces the marked
difference class to be non-recurrent.  The proof is the paper's: apply the
exact formula of Lemma 4.10 to `D = w` for each vertex `w`, note that the
zero residue is always effective, and read the inversion bound `inv_k ≤ 2`
backwards. -/
theorem nonRecurrent_of_kGeneralTransmission
    (B : Banana 2) (u v : B.graph.V) (k : ℕ)
    (hRigid : ¬ linear_equiv B.graph
      (one_chip u + one_chip v) (canonical_divisor B.graph))
    (hKGT : KGeneralTransmission (mark B.graph u v) k) :
    NonRecurrent (mark B.graph u v) k := by
  obtain ⟨hTorsion, -, hData⟩ := hKGT
  intro w n m hn hm hnRank hmRank
  obtain ⟨tau, hTau, hAffine, -, hCount⟩ := hData (one_chip w)
  have hEq := kInversionCount_eq_effectiveResidues_ncard_of_rigid
    B u v (one_chip w) k tau hTorsion hTau hAffine hRigid
  have hGenus : Int.toNat (genus (mark B.graph u v).graph) = 2 := by
    change Int.toNat (genus B.graph) = 2
    rw [B.genus_graph]
    rfl
  rw [hGenus, hEq] at hCount
  have hzero : (⟨0, hTorsion.1⟩ : Fin k) ∈
      effectiveDegreeOneTwistResidues (mark B.graph u v) (one_chip w) k := by
    rw [mem_effectiveDegreeOneTwistResidues_one_chip_iff B.graph u v w k _]
    have hRank : rank B.graph (one_chip w) = 0 :=
      rank_one_chip_zero_banana_two B w
    simpa using hRank.ge
  have hnMem : n ∈
      effectiveDegreeOneTwistResidues (mark B.graph u v) (one_chip w) k := by
    rw [mem_effectiveDegreeOneTwistResidues_one_chip_iff B.graph u v w k _]
    exact hnRank
  have hmMem : m ∈
      effectiveDegreeOneTwistResidues (mark B.graph u v) (one_chip w) k := by
    rw [mem_effectiveDegreeOneTwistResidues_one_chip_iff B.graph u v w k _]
    exact hmRank
  exact eq_of_ncard_le_two_of_mem_three hCount hzero hnMem hmMem
    (fun h => hn (congrArg Fin.val h)) (fun h => hm (congrArg Fin.val h))

/-- Paper source: `thm:kgtThetas` (Theorem 4.8), both directions.

A rigidly marked theta graph of exact torsion order `k` has `k`-general
transmission if and only if the marked difference class is non-recurrent. -/
theorem thetaRigid_kGeneral_iff_nonRecurrent
    {k : ℕ} (B : Banana 2) (u v : B.graph.V)
    (hSub : AllSubmodular (mark B.graph u v))
    (hTO : IsTorsionOrder (mark B.graph u v) k)
    (hRigid : ¬ linear_equiv B.graph
      (one_chip u + one_chip v) (canonical_divisor B.graph)) :
    KGeneralTransmission (mark B.graph u v) k ↔
      NonRecurrent (mark B.graph u v) k := by
  constructor
  · exact nonRecurrent_of_kGeneralTransmission B u v k hRigid
  · intro hNonrec
    refine ⟨hTO.1, hSub, ?_⟩
    intro D
    obtain ⟨τ, hτ, hAffine, hFinite⟩ :=
      exists_affine_transmission_of_allSubmodular
        (graph_connected B) hTO.1 hSub D
    refine ⟨τ, hτ, hAffine, hFinite, ?_⟩
    have hCount := kInversionCount_le_two_of_nonRecurrent_of_rigid
      B u v D k τ hTO hτ hAffine hNonrec hRigid
    simpa [mark, B.genus_graph] using hCount

end Bananas
