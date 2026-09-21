/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionFiveDefinitions
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaNonrecurrence
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.KGeneralSwap

/-!
# The inversion count in Section 5

This module isolates the finite combinatorial part of the final proposition
in Section 5.  Its remaining graph-theoretic input is the identification of
the displayed rank-drop sum with the cardinality of the finite fibres below.
-/

namespace Bananas

open Utilities

/-- The points counted by the rank-drop summand at `m`: they lie weakly to
the southeast of `(m - 1, m)` and have transmission value exactly `m - 1`. -/
def sectionFiveRankDropFibre (tau : ℤ → ℤ) (m : ℤ) : Set ℤ :=
  {b | m ≤ b ∧ tau b = m - 1}

/-- The finite rank-drop fibres inject into normalized affine inversions when
the transmission permutation is self-inverse.  This is the ``below the
diagonal gives an inversion'' step of the paper proof, with the normalization
needed by the Lean definition of `kInversionCount`. -/
theorem sectionFive_rankDropFibre_sum_le_inversionCount
    {tau : ℤ → ℤ} {k : ℕ} (hk : 0 < k)
    (hAffine : IsKAffine k tau)
    (hInvolutive : ∀ a b : ℤ, tau b = a ↔ tau a = b)
    (hFinite : ∀ m : Fin k,
      (sectionFiveRankDropFibre tau ((m : ℕ) : ℤ)).Finite) :
    (∑ m : Fin k,
      (sectionFiveRankDropFibre tau ((m : ℕ) : ℤ)).ncard : ℤ) ≤
      kInversionCount k tau := by
  classical
  let S : Set (Σ m : Fin k,
      {b : ℤ // b ∈ sectionFiveRankDropFibre tau ((m : ℕ) : ℤ)}) := Set.univ
  let f : (Σ m : Fin k,
      {b : ℤ // b ∈ sectionFiveRankDropFibre tau ((m : ℕ) : ℤ)}) → ℤ × ℤ :=
    fun x => normalizeFirstPair k (((x.1 : ℕ) : ℤ) - 1, x.2)
  have hmaps : ∀ x ∈ S, f x ∈ kInversions k tau := by
    rintro ⟨m, b⟩ _
    rcases b.property with ⟨hmb, hval⟩
    apply inversion_normalize_first_coordinate hk hAffine
    have hinv : tau (((m : ℕ) : ℤ) - 1) = b :=
      (hInvolutive (((m : ℕ) : ℤ) - 1) b).mp hval
    change ((m : ℕ) : ℤ) - 1 < b ∧
      tau (((m : ℕ) : ℤ) - 1) > tau b
    rw [hinv, hval]
    omega
  have hinj : Set.InjOn f S := by
    rintro ⟨m, b⟩ _ ⟨m', b'⟩ _ heq
    have hfirst := congrArg Prod.fst heq
    simp only [f, normalizeFirstPair] at hfirst
    have hm : m = m' := by
      apply Fin.ext
      have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
      have hmod : ((m.val : ℤ) - 1) ≡ ((m'.val : ℤ) - 1) [ZMOD (k : ℤ)] :=
        hfirst
      have hdiv : (k : ℤ) ∣ (m'.val : ℤ) - m.val := by
        have := Int.modEq_iff_dvd.mp hmod
        convert this using 1
        ring_nf
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hpos : 0 < (m'.val : ℤ) - (m.val : ℤ) := by
          omega
        have hle := Int.le_of_dvd hpos hdiv
        have := m'.isLt
        omega
      · have hpos : 0 < (m.val : ℤ) - (m'.val : ℤ) := by
          omega
        have hdiv' : (k : ℤ) ∣ (m.val : ℤ) - m'.val := by
          have hneg : (k : ℤ) ∣ -((m'.val : ℤ) - m.val) := dvd_neg.mpr hdiv
          simpa only [neg_sub] using hneg
        have hle := Int.le_of_dvd hpos hdiv'
        have := m.isLt
        omega
    subst m'
    have hsecond := congrArg Prod.snd heq
    simp only [f, normalizeFirstPair] at hsecond
    apply Sigma.mk.inj_iff.mpr
    constructor
    · rfl
    exact heq_of_eq (Subtype.ext (by omega))
  have htarget := kInversions_finite_of_isKAffine hk hAffine
  have hle := Set.ncard_le_ncard_of_injOn (s := S) (t := kInversions k tau)
    f hmaps hinj htarget
  have hcard : S.ncard = ∑ m : Fin k,
      (sectionFiveRankDropFibre tau ((m : ℕ) : ℤ)).ncard := by
    let : ∀ m : Fin k,
        Fintype {b : ℤ // b ∈ sectionFiveRankDropFibre tau ((m : ℕ) : ℤ)} :=
      fun m => (hFinite m).fintype
    simp only [S, Set.ncard_univ]
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro m _
    rw [Nat.card_coe_set_eq]
  rw [hcard] at hle
  exact_mod_cast hle

/-- The Section 5 rank-drop summand is the cardinality of its corresponding
transmission fibre.  This is the `tauChars` part of the paper argument. -/
theorem sectionFive_rankDropSum_eq_fibre_sum
    {M : TwiceMarked} {D : CFDiv M.graph} {tau : ℤ → ℤ} {k : ℕ}
    (hconn : _root_.graph_connected M.graph)
    (hTau : IsTransmissionPermutation M D tau) :
    sectionFiveRankDropSum M D k =
      ∑ m : Fin k,
        (sectionFiveRankDropFibre tau ((m : ℕ) : ℤ)).ncard := by
  classical
  obtain ⟨sigma, hSigmaTau, -⟩ :=
    transmissionPermutation_rankSlipFace M D hconn tau hTau
  unfold sectionFiveRankDropSum
  push_cast
  apply Finset.sum_congr rfl
  intro m _
  let big : Set ℤ := southeast_set tau ((m : ℕ) : ℤ) ((m : ℕ) : ℤ)
  let small : Set ℤ := southeast_set tau (((m : ℕ) : ℤ) - 1) ((m : ℕ) : ℤ)
  let fibre : Set ℤ := sectionFiveRankDropFibre tau ((m : ℕ) : ℤ)
  have hbigFin : big.Finite := by
    rw [show big = southeast_set sigma.func ((m : ℕ) : ℤ) ((m : ℕ) : ℤ) by
      simp only [big, hSigmaTau]]
    exact sigma.se_finite _ _
  have hsmallFin : small.Finite := by
    apply hbigFin.subset
    intro b hb
    change ((m : ℕ) : ℤ) ≤ b ∧ tau b < ((m : ℕ) : ℤ) - 1 at hb
    change ((m : ℕ) : ℤ) ≤ b ∧ tau b < ((m : ℕ) : ℤ)
    omega
  have hfibreFin : fibre.Finite := by
    apply hbigFin.subset
    intro b hb
    change ((m : ℕ) : ℤ) ≤ b ∧ tau b = ((m : ℕ) : ℤ) - 1 at hb
    change ((m : ℕ) : ℤ) ≤ b ∧ tau b < ((m : ℕ) : ℤ)
    omega
  have hunion : big = small ∪ fibre := by
    ext b
    change (((m : ℕ) : ℤ) ≤ b ∧ tau b < ((m : ℕ) : ℤ)) ↔
      (((m : ℕ) : ℤ) ≤ b ∧ tau b < ((m : ℕ) : ℤ) - 1) ∨
        (((m : ℕ) : ℤ) ≤ b ∧ tau b = ((m : ℕ) : ℤ) - 1)
    omega
  have hdisj : Disjoint small fibre := by
    rw [Set.disjoint_left]
    intro b hbSmall hbFibre
    dsimp [small] at hbSmall
    dsimp [fibre] at hbFibre
    change ((m : ℕ) : ℤ) ≤ b ∧ tau b < ((m : ℕ) : ℤ) - 1 at hbSmall
    change ((m : ℕ) : ℤ) ≤ b ∧ tau b = ((m : ℕ) : ℤ) - 1 at hbFibre
    omega
  have hcard : big.ncard = small.ncard + fibre.ncard := by
    rw [hunion]
    exact Set.ncard_union_eq hdisj hsmallFin hfibreFin
  have hrankBig := transmission_rank_eq_southeast_ncard
    M D hconn tau hTau (((m : ℕ) : ℤ) - 1) ((m : ℕ) : ℤ)
  have hrankSmall := transmission_rank_eq_southeast_ncard
    M D hconn tau hTau (((m : ℕ) : ℤ) - 2) ((m : ℕ) : ℤ)
  simp only [sub_add_cancel] at hrankBig
  change rank M.graph
      (D + (((m : ℕ) : ℤ) - 1) • one_chip M.u - ((m : ℕ) : ℤ) • one_chip M.v) -
    rank M.graph
      (D + (((m : ℕ) : ℤ) - 2) • one_chip M.u - ((m : ℕ) : ℤ) • one_chip M.v) = _
  change _ = ((sectionFiveRankDropFibre tau ((m : ℕ) : ℤ)).ncard : ℤ)
  have hsmallThreshold : ((m : ℕ) : ℤ) - 2 + 1 = ((m : ℕ) : ℤ) - 1 := by ring
  rw [hsmallThreshold] at hrankSmall
  change rank M.graph
      (D + (((m : ℕ) : ℤ) - 1) • one_chip M.u - ((m : ℕ) : ℤ) • one_chip M.v) + 1 =
    big.ncard at hrankBig
  change rank M.graph
      (D + (((m : ℕ) : ℤ) - 2) • one_chip M.u - ((m : ℕ) : ℤ) • one_chip M.v) + 1 =
    small.ncard at hrankSmall
  dsimp [big, small, fibre] at hcard hrankBig hrankSmall
  omega

/-- Corrected, connected form of the final Section 5 proposition.  The paper
assumes connected graphs throughout; `CFGraph` does not bundle that condition,
so it is explicit here. -/
theorem sectionFive_inversion_lower_bound_of_involutive_transmission_connected
    {M : TwiceMarked} {D : CFDiv M.graph} {tau : ℤ → ℤ} {k : ℕ}
    (hk : 0 < k) (hconn : _root_.graph_connected M.graph)
    (hTau : IsTransmissionPermutation M D tau)
    (hAffine : IsKAffine k tau)
    (hInvolutive : ∀ a b : ℤ, tau b = a ↔ tau a = b) :
    sectionFiveRankDropSum M D k ≤ kInversionCount k tau := by
  rw [sectionFive_rankDropSum_eq_fibre_sum hconn hTau]
  push_cast
  apply sectionFive_rankDropFibre_sum_le_inversionCount hk hAffine hInvolutive
  intro m
  obtain ⟨sigma, hSigmaTau, -⟩ :=
    transmissionPermutation_rankSlipFace M D hconn tau hTau
  apply (sigma.se_finite _ _).subset
  intro b hb
  change ((m : ℕ) : ℤ) ≤ b ∧ tau b = ((m : ℕ) : ℤ) - 1 at hb
  rw [← hSigmaTau] at hb
  change ((m : ℕ) : ℤ) ≤ b ∧ sigma.func b < ((m : ℕ) : ℤ)
  omega

end Bananas
