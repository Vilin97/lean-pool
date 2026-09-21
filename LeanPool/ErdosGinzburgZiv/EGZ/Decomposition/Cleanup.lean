/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Mass
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredLift

/-!
# Finite gap cleanup

The numerical core of the gap cleanup lemma removes an entire fibre whenever
its positive mass is at most its threshold. Each fibre can be charged only
once: after deletion its mass remains zero. Strong induction on the remaining
finite set of fibres proves termination and the total mass bound together.
-/

open scoped BigOperators

namespace EGZ

/-- Simultaneous gap cleanup for any finite family of sets of atoms.
The resulting weight is obtained only by deleting atoms, all surviving fibre
masses exceed their thresholds, and the loss is at most the sum of thresholds.
No disjointness assumption on the sets is needed. -/
theorem exists_gap_pruning {α β : Type*} [Fintype α]
    (s : Finset β) (fibre : β → Set α) (threshold : β → ℝ)
    (hnonneg : ∀ b ∈ s, 0 ≤ threshold b) (w : α → ℕ) :
    ∃ w' : α → ℕ,
      (∀ a, w' a = 0 ∨ w' a = w a) ∧ w' ≤ w ∧
      (∀ b ∈ s, natMassOn w' (fibre b) = 0 ∨
        threshold b < (natMassOn w' (fibre b) : ℝ)) ∧
      (natMass w : ℝ) - natMass w' ≤ ∑ b ∈ s, threshold b := by
  classical
  induction s using Finset.strongInductionOn generalizing w
  case _ s ih =>
    by_cases hgood : ∀ b ∈ s, natMassOn w (fibre b) = 0 ∨
        threshold b < (natMassOn w (fibre b) : ℝ)
    · refine ⟨w, fun _ ↦ Or.inr rfl, le_rfl, hgood, ?_⟩
      simpa using Finset.sum_nonneg hnonneg
    · push Not at hgood
      obtain ⟨b, hb, hpos, hsmall⟩ := hgood
      let u : α → ℕ := fun a ↦ if a ∈ fibre b then 0 else w a
      have hu : u ≤ w := by
        intro a
        dsimp [u]
        split_ifs <;> omega
      have huclear : natMassOn u (fibre b) = 0 := by
        unfold natMassOn
        apply Finset.sum_eq_zero
        intro a _
        by_cases ha : a ∈ fibre b <;> simp [u, ha]
      have humass : natMass u = natMassOn w (fibre b)ᶜ := by
        unfold natMass natMassOn
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a ∈ fibre b <;> simp [u, ha]
      have hloss : (natMass w : ℝ) - natMass u = natMassOn w (fibre b) := by
        have hm := natMassOn_add_compl w (fibre b)
        rw [← humass] at hm
        have hm' : (natMassOn w (fibre b) : ℝ) + natMass u = natMass w := by
          exact_mod_cast hm
        linarith
      obtain ⟨w', hatoms, hle, hgap, hbound⟩ :=
        ih (s.erase b) (Finset.erase_ssubset hb)
          (fun c hc ↦ hnonneg c (Finset.mem_of_mem_erase hc)) u
      refine ⟨w', ?_, hle.trans hu, ?_, ?_⟩
      · intro a
        rcases hatoms a with ha | ha
        · exact Or.inl ha
        · by_cases hmem : a ∈ fibre b
          · exact Or.inl (ha.trans (by simp [u, hmem]))
          · exact Or.inr (ha.trans (by simp [u, hmem]))
      · intro c hc
        by_cases hcb : c = b
        · subst c
          exact Or.inl (Nat.eq_zero_of_le_zero
            ((natMassOn_mono_weight hle (fibre b)).trans_eq huclear))
        · exact hgap c (Finset.mem_erase.mpr ⟨hcb, hc⟩)
      · have hsum : (∑ c ∈ s.erase b, threshold c) + threshold b =
            ∑ c ∈ s, threshold c := Finset.sum_erase_add _ _ hb
        linarith

namespace FlagDecompositionRaw

variable {p d : ℕ} [NeZero p] {F : ConvexFlag}

omit [NeZero p] in
theorem cumulativeWeight_mono {pieces pieces' : F.Node → FpCoord p d → ℕ}
    (hle : ∀ x v, pieces' x v ≤ pieces x v) (x : F.Node) (v : FpCoord p d) :
    cumulativeWeight pieces' x v ≤ cumulativeWeight pieces x v := by
  classical
  apply Finset.sum_le_sum
  intro y _
  split_ifs
  · exact hle y v
  · exact le_rfl

theorem hat_mono (R : FpRepresentation p d F)
    {pieces pieces' : F.Node → FpCoord p d → ℕ}
    (hle : ∀ x v, pieces' x v ≤ pieces x v) (x : F.Node)
    (q : IntCoord (F.rank x)) : hat R pieces' x q ≤ hat R pieces x q := by
  classical
  unfold hat
  split_ifs
  · apply Finset.sum_le_sum
    intro v _
    split_ifs
    · exact cumulativeWeight_mono hle x v
    · exact le_rfl
  · exact le_rfl

/-- The atoms in a cumulative coordinate fibre. Atoms remember their local
node, so overlapping ambient supports do not cause double counting. -/
def cumulativeFibre (R : FpRepresentation p d F)
    (x : F.Node) (q : IntCoord (F.rank x)) : Set (F.Node × FpCoord p d) :=
  {a | a.1 ≤ x ∧ R.map x a.2 = q.mod p}

theorem hat_eq_natMassOn (R : FpRepresentation p d F)
    (pieces : F.Node → FpCoord p d → ℕ) (x : F.Node)
    (q : IntCoord (F.rank x)) (hq : IsCenteredLift p q) :
    hat R pieces x q =
      natMassOn (fun a : F.Node × FpCoord p d ↦ pieces a.1 a.2)
        (cumulativeFibre R x q) := by
  classical
  unfold hat
  rw [ite_eq_left hq]
  unfold affineFibreMass cumulativeWeight natMassOn
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : R.map x v = q.mod p
  · simp [cumulativeFibre, hv]
  · simp [cumulativeFibre, hv]

theorem natMass_retainedWeight (pieces : F.Node → FpCoord p d → ℕ) :
    natMass (retainedWeight pieces) =
      natMass (fun a : F.Node × FpCoord p d ↦ pieces a.1 a.2) := by
  unfold natMass retainedWeight
  rw [Fintype.sum_prod_type, Finset.sum_comm]

end FlagDecompositionRaw

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

theorem gap_pos (Φ : FlagDecomposition p d f) (x : Φ.flag.Node) :
    0 < Φ.gap x := by
  classical
  have hmem := Finset.min'_mem ((Φ.liftedSupport x).image (Φ.hat x))
    ((Φ.liftedSupport_nonempty x).image (Φ.hat x))
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hmem
  change 0 < ((Φ.liftedSupport x).image (Φ.hat x)).min' _
  rw [← heq]
  exact Nat.pos_of_ne_zero ((Φ.liftedSupport_spec x q).mp hq)

theorem gap_le_hat (Φ : FlagDecomposition p d f) (x : Φ.flag.Node)
    (q : IntCoord (Φ.flag.rank x)) (hq : Φ.hat x q ≠ 0) :
    Φ.gap x ≤ Φ.hat x q := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨q, (Φ.liftedSupport_spec x q).mpr hq, rfl⟩)

/-- A coordinate bound controls the number of positive cumulative fibres,
uniformly in the prime. -/
theorem card_liftedSupport_le (Φ : FlagDecomposition p d f)
    {K : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K) (x : Φ.flag.Node) :
    (Φ.liftedSupport x).card ≤ (2 * K x + 1) ^ Φ.flag.rank x := by
  apply card_le_of_latticeSupNorm_le
  intro q hq
  apply hK x q
  rw [Φ.polytope_eq_liftedSupport]
  exact _root_.subset_convexHull ℝ _ ⟨q, hq, rfl⟩

theorem card_liftedSupport_le_pow_dim [Fact p.Prime]
    (Φ : FlagDecomposition p d f)
    {K : Φ.flag.Node → ℕ} (hK : Φ.IsKBounded K) (x : Φ.flag.Node) :
    (Φ.liftedSupport x).card ≤ (2 * K x + 1) ^ d :=
  (Φ.card_liftedSupport_le hK x).trans
    (pow_le_pow_right' (by omega) (Φ.representation.rank_le x))

/-- Gap cleanup of all local atoms, before rebuilding the active polytopes.
Its loss bound counts only the original lifted supports. The theorem applies
to arbitrary node thresholds and preserves the original value of every
surviving local atom. -/
theorem exists_gap_pruned_localWeight (Φ : FlagDecomposition p d f)
    (threshold : Φ.flag.Node → ℝ) (hnonneg : ∀ x, 0 ≤ threshold x) :
    ∃ pieces : Φ.flag.Node → FpCoord p d → ℕ,
      (∀ x v, pieces x v = 0 ∨ pieces x v = Φ.localWeight x v) ∧
      (∀ x v, pieces x v ≤ Φ.localWeight x v) ∧
      (∀ x q, FlagDecompositionRaw.hat Φ.representation pieces x q = 0 ∨
        threshold x < (FlagDecompositionRaw.hat Φ.representation pieces x q : ℝ)) ∧
      (Φ.retainedMass : ℝ) - natMass (FlagDecompositionRaw.retainedWeight pieces) ≤
        ∑ x, (Φ.liftedSupport x).card * threshold x := by
  classical
  let s := Finset.univ.sigma Φ.liftedSupport
  obtain ⟨w', hatoms, hle, hgap, hloss⟩ := exists_gap_pruning s
    (fun a ↦ FlagDecompositionRaw.cumulativeFibre Φ.representation a.1 a.2)
    (fun a ↦ threshold a.1) (fun a _ ↦ hnonneg a.1)
    (fun a : Φ.flag.Node × FpCoord p d ↦ Φ.localWeight a.1 a.2)
  let pieces := fun x v ↦ w' (x, v)
  have hpieces : ∀ x v, pieces x v ≤ Φ.localWeight x v := fun x v ↦ hle (x, v)
  refine ⟨pieces, fun x v ↦ hatoms (x, v), hpieces, ?_, ?_⟩
  · intro x q
    by_cases hq : Φ.hat x q = 0
    · exact Or.inl (Nat.eq_zero_of_le_zero
        ((FlagDecompositionRaw.hat_mono Φ.representation hpieces x q).trans_eq hq))
    · have hmem := (Φ.liftedSupport_spec x q).mpr hq
      have hcentered : IsCenteredLift p q := by
        by_contra hc
        exact hq (by simp only [hat, FlagDecompositionRaw.hat, ite_eq_right hc])
      have h := hgap ⟨x, q⟩ (Finset.mem_sigma.mpr ⟨Finset.mem_univ x, hmem⟩)
      simpa only [FlagDecompositionRaw.hat_eq_natMassOn _ _ _ _ hcentered] using h
  · have hsum : (∑ a ∈ s, threshold a.1) =
        ∑ x, (Φ.liftedSupport x).card * threshold x := by
      simp [s, Finset.sum_sigma, nsmul_eq_mul]
    rw [hsum] at hloss
    simpa only [retainedMass, retainedWeight,
      FlagDecompositionRaw.natMass_retainedWeight] using hloss

/-- The numerical conclusion of the gap cleanup lemma with the paper's
uniform threshold. Rebuilding the reduced active flag is a separate geometric
operation; this theorem supplies its local weights and complete loss estimate. -/
theorem exists_bounded_gap_pruning [Fact p.Prime]
    (Φ : FlagDecomposition p d f) {K : Φ.flag.Node → ℕ}
    (hK : Φ.IsKBounded K) {α : ℝ} (hα : 0 ≤ α) :
    ∃ pieces : Φ.flag.Node → FpCoord p d → ℕ,
      (∀ x v, pieces x v = 0 ∨ pieces x v = Φ.localWeight x v) ∧
      (∀ x v, pieces x v ≤ Φ.localWeight x v) ∧
      (∀ x q, FlagDecompositionRaw.hat Φ.representation pieces x q ≠ 0 →
        α * (Φ.retainedMass : ℝ) /
            ((Fintype.card Φ.flag.Node : ℝ) * (2 * (K x : ℝ) + 1) ^ d) <
          (FlagDecompositionRaw.hat Φ.representation pieces x q : ℝ)) ∧
      (1 - α) * (Φ.retainedMass : ℝ) ≤
        (natMass (FlagDecompositionRaw.retainedWeight pieces) : ℝ) := by
  classical
  let N : ℝ := Fintype.card Φ.flag.Node
  let M : ℝ := Φ.retainedMass
  let volume : Φ.flag.Node → ℝ := fun x ↦ (2 * (K x : ℝ) + 1) ^ d
  let threshold : Φ.flag.Node → ℝ := fun x ↦ α * M / (N * volume x)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hvolume : ∀ x, 0 < volume x := by intro x; dsimp [volume]; positivity
  have hthreshold : ∀ x, 0 ≤ threshold x := by
    intro x
    exact div_nonneg (mul_nonneg hα hM) (mul_pos hN (hvolume x)).le
  obtain ⟨pieces, hatoms, hle, hgap, hloss⟩ :=
    Φ.exists_gap_pruned_localWeight threshold hthreshold
  have hterm (x : Φ.flag.Node) :
      (Φ.liftedSupport x).card * threshold x ≤ α * M / N := by
    have hcard : ((Φ.liftedSupport x).card : ℝ) ≤ volume x := by
      dsimp [volume]
      exact_mod_cast Φ.card_liftedSupport_le_pow_dim hK x
    calc
      (Φ.liftedSupport x).card * threshold x ≤ volume x * threshold x :=
        mul_le_mul_of_nonneg_right hcard (hthreshold x)
      _ = α * M / N := by
        dsimp [threshold]
        field_simp [ne_of_gt hN, ne_of_gt (hvolume x)]
  have hsum : (∑ x, (Φ.liftedSupport x).card * threshold x) ≤ α * M := by
    calc
      (∑ x, (Φ.liftedSupport x).card * threshold x) ≤
          ∑ _x : Φ.flag.Node, α * M / N := Finset.sum_le_sum fun x _ ↦ hterm x
      _ = α * M := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change N * (α * M / N) = α * M
        field_simp [ne_of_gt hN]
  refine ⟨pieces, hatoms, hle, ?_, ?_⟩
  · intro x q hq
    exact (hgap x q).resolve_left hq
  · have hb := hloss.trans hsum
    dsimp [M] at hb
    nlinarith

end FlagDecomposition

end EGZ
