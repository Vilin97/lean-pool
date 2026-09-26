/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointBlock
public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.AffineInversionFinite
public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaNonrecurrence
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TorsionOrderExact

/-!
# Counting the endpoint inversion block

This file turns the decreasing block supplied by `EndpointBlock` into the
corresponding lower bound on the number of affine inversion classes, and
assembles the resulting quadratic-versus-linear contradiction that rules out
`k`-general transmission for the endpoint marking.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Encode an unordered endpoint pair by its minimum and one more than its maximum. -/
noncomputable def endpointPairEmbedding (g : ℕ) : Sym2 (Fin g) → ℤ × ℤ :=
  Sym2.lift ⟨(fun (a b : Fin g) => (((min a.val b.val : ℕ) : ℤ),
    ((max a.val b.val + 1 : ℕ) : ℤ))), by
    intro a b
    simp [min_comm, max_comm]⟩

theorem endpointPairEmbedding_injective (g : ℕ) :
    Function.Injective (endpointPairEmbedding g) := by
  intro x y hxy
  induction x using Sym2.ind with
  | _ a b =>
    induction y using Sym2.ind with
    | _ c d =>
      simp only [endpointPairEmbedding, Sym2.lift_mk] at hxy
      rw [Sym2.eq]
      simp only [Sym2.rel_iff]
      by_cases hab : a.val ≤ b.val
      · by_cases hcd : c.val ≤ d.val
        · left
          simp [min_eq_left hab, max_eq_right hab,
            min_eq_left hcd, max_eq_right hcd] at hxy
          constructor <;> apply Fin.ext <;> omega
        · right
          have hdc : d.val ≤ c.val := by omega
          simp [min_eq_left hab, max_eq_right hab,
            min_eq_right hdc, max_eq_left hdc] at hxy
          constructor <;> apply Fin.ext <;> omega
      · by_cases hcd : c.val ≤ d.val
        · right
          have hba : b.val ≤ a.val := by omega
          simp [min_eq_right hba, max_eq_left hba,
            min_eq_left hcd, max_eq_right hcd] at hxy
          constructor <;> apply Fin.ext <;> omega
        · left
          have hba : b.val ≤ a.val := by omega
          have hdc : d.val ≤ c.val := by omega
          simp [min_eq_right hba, max_eq_left hba,
            min_eq_right hdc, max_eq_left hdc] at hxy
          constructor <;> apply Fin.ext <;> omega

theorem endpoint_block_inversion_lower_bound
    {g k : ℕ} {τ : ℤ → ℤ}
    (hk : 0 < k) (hAffine : IsKAffine k τ)
    (hBlock : ∀ b : ℕ, b ≤ g → τ b = (g - b : ℕ))
    (hfinite : (kInversions k τ).Finite) :
    Nat.choose (g + 1) 2 ≤ kInversionCount k τ := by
  have hgk : g < k := endpoint_affine_period_gt_genus hk hAffine hBlock
  have hmap : ∀ x : Sym2 (Fin g), x ∈ Set.univ →
      endpointPairEmbedding g x ∈ kInversions k τ := by
    intro x _
    induction x using Sym2.ind with
    | _ a b =>
      simp only [endpointPairEmbedding, Sym2.lift_mk, kInversions, Set.mem_ofPred_eq]
      let m := min a.val b.val
      let n := max a.val b.val + 1
      have hmn : m < n := by
        dsimp [m, n]
        omega
      have hnle : n ≤ g := by
        dsimp [n]
        exact Nat.succ_le_of_lt (max_lt a.isLt b.isLt)
      have hmle : m ≤ g := by
        calc
          m = min a.val b.val := rfl
          _ ≤ max a.val b.val := min_le_max
          _ ≤ max a.val b.val + 1 := Nat.le_succ _
          _ = n := rfl
          _ ≤ g := hnle
      have hτm := hBlock m hmle
      have hτn := hBlock n hnle
      change (m : ℤ) < n ∧ τ m > τ n ∧ 0 ≤ (m : ℤ) ∧ (m : ℤ) < k
      rw [hτm, hτn]
      refine ⟨by exact_mod_cast hmn, ?_, by exact_mod_cast Nat.zero_le m, ?_⟩
      · have hdiff : g - n < g - m := by omega
        exact_mod_cast hdiff
      · have hmk : m < k := (lt_of_lt_of_le hmn hnle).trans hgk
        exact_mod_cast hmk
  have hle := Set.ncard_le_ncard_of_injOn (s := (Set.univ : Set (Sym2 (Fin g))))
    (t := kInversions k τ) (endpointPairEmbedding g) hmap
    (endpointPairEmbedding_injective g).injOn hfinite
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hle
  change (Finset.univ : Finset (Sym2 (Fin g))).card ≤ _ at hle
  rw [← Finset.sym2_univ, Finset.card_sym2, Finset.card_univ] at hle
  simpa [kInversionCount] using hle

/-- TeX labels: `lem-TriangleInversionII` (Lemma 4.20),
`prop-TriangleInversionNumber` (Proposition 4.21).

With `(u,v) = (v_{0,0}, v_{0,n_0})` and `D = g·v_{0,n_0}`, the transmission
permutation contains the decreasing block `τ(b) = g - b` for `0 ≤ b ≤ g`,
yielding `M ≥ choose (g+1) 2` inversion classes.  The `∃ D τ` form is the
formal reading of the paper's `M`, the maximum over all divisors.

Only `hk.1` (a torsion *witness*) is used; `IsTorsionOrder` is kept because
the paper's `M` and `inv_k` refer to the torsion order. -/
theorem endpoint_marked_inversion_lower_bound
    {g k : ℕ} (B : Banana g)
    (hsub : AllSubmodular (mark B.graph (leftEndpoint B) (rightEndpoint B)))
    (hk : IsTorsionOrder (mark B.graph (leftEndpoint B) (rightEndpoint B)) k) :
    ∃ D τ, IsTransmissionPermutation
      (mark B.graph (leftEndpoint B) (rightEndpoint B)) D τ ∧
      IsKAffine k τ ∧ Nat.choose (g + 1) 2 ≤ kInversionCount k τ := by
  let M := mark B.graph (leftEndpoint B) (rightEndpoint B)
  obtain ⟨τ, hτ, hAffine, hBlock⟩ :=
    exists_endpoint_transmission_block B hsub hk.1
  refine ⟨g • oneChip (rightEndpoint B), τ, hτ, hAffine, ?_⟩
  exact endpoint_block_inversion_lower_bound hk.1.1 hAffine hBlock
    (kInversions_finite_of_isKAffine hk.1.1 hAffine)

/-! The period conclusion used in Proposition 4.19 is already forced by the
endpoint transmission block, before counting its inversions. -/

theorem endpoint_marking_torsionOrder_gt_genus
    {g k : ℕ} (B : Banana g)
    (hsub : AllSubmodular (mark B.graph (leftEndpoint B) (rightEndpoint B)))
    (hk : IsTorsionOrder
      (mark B.graph (leftEndpoint B) (rightEndpoint B)) k) :
    g < k := by
  obtain ⟨τ, _hτ, hAffine, hBlock⟩ :=
    exists_endpoint_transmission_block B hsub hk.1
  exact endpoint_affine_period_gt_genus hk.1.1 hAffine hBlock

/-- TeX labels: `thm:bananas` (Theorem 1.17) / `cor:bananasWithKGT`
(Corollary 6.4), **endpoint-marking branch, unconditional**.

For every genus at least two, the endpoint-marked banana `(B, v_0, v_{n})`
admits `k`-general transmission for no `k` at all.

The proof is an assembly of results that were already present separately.
Suppose `KGeneralTransmission (mark B v_0 v_n) k`.  Then

* all divisors are submodular (second conjunct of Definition 1.10), and by
  `banana_kGeneral_isTorsionOrder` (`lem:kgtImpliesTorsionOrder`, Lemma 4.2)
  `k` is the exact torsion order;
* so `endpoint_marked_inversion_lower_bound` (`lem-TriangleInversionII` 4.20 /
  `prop-TriangleInversionNumber` 4.21) supplies a divisor `D` whose
  transmission permutation has at least `choose (g+1) 2` inversion classes;
* the third conjunct of Definition 1.10 supplies, for that same `D`, a
  transmission permutation with at most `genus = g` inversion classes;
* transmission permutations are unique (`transmissionPermutation_unique`), so
  these are the same permutation, giving `choose (g+1) 2 ≤ g`, false for
  `g ≥ 2`.

The quadratic-versus-linear gap is exactly the paper's argument; the only
ingredient that had to be added was uniqueness, which is immediate from
`def-tauD` (Definition 2.11). -/
theorem endpoint_marking_not_kGeneral
    {g k : ℕ} (hg : 2 ≤ g) (B : Banana g) :
    ¬ KGeneralTransmission
      (mark B.graph (leftEndpoint B) (rightEndpoint B)) k := by
  intro hK
  have hSub : AllSubmodular
      (mark B.graph (leftEndpoint B) (rightEndpoint B)) := hK.2.1
  have hTO : IsTorsionOrder
      (mark B.graph (leftEndpoint B) (rightEndpoint B)) k :=
    banana_kGeneral_isTorsionOrder B _ _ (leftEndpoint_ne_rightEndpoint B)
      (by rw [B.genus_graph]; omega) hK
  obtain ⟨D, τ, hτ, _hAffine, hLower⟩ :=
    endpoint_marked_inversion_lower_bound B hSub hTO
  obtain ⟨σ, hσ, _hAffineσ, _hFin, hCount⟩ := hK.2.2 D
  have hEq : τ = σ := transmissionPermutation_unique hτ hσ
  rw [hEq] at hLower
  have hGenus : Int.toNat (genus (mark B.graph (leftEndpoint B)
      (rightEndpoint B)).graph) = g := by
    change Int.toNat (genus B.graph) = g
    rw [B.genus_graph]
    omega
  rw [hGenus] at hCount
  have hle : Nat.choose (g + 1) 2 ≤ g := le_trans hLower hCount
  obtain ⟨m, hm⟩ : ∃ m, (g + 1) * g = m := ⟨_, rfl⟩
  have hval : Nat.choose (g + 1) 2 = m / 2 := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel, hm]
  have hge : 2 * g + 2 ≤ m := by
    rw [← hm]
    nlinarith
  omega

end Bananas
