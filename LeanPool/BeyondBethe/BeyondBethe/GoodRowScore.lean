/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Cycles
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic

/-! # Good Row Score -/

open scoped BigOperators Topology
open Filter

namespace BeyondBethe

/-- A genuinely continuous formula for the suffix error near every point
`(a,x)` with `a+x != 0`.  On the nonnegative quadrant it agrees with
`suffixError`; the rewrite removes the apparent singularity at `x=0`. -/
noncomputable def continuousSuffixError (a x : ℝ) : ℝ :=
  a - x * Real.log (a + x) - Real.negMulLog x

theorem suffixError_eq_continuousSuffixError
    {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    suffixError a x = continuousSuffixError a x := by
  by_cases hx0 : x = 0
  · subst x
    simp [suffixError, continuousSuffixError]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hsum : a + x ≠ 0 := (add_pos_of_nonneg_of_pos ha hxpos).ne'
    have hratio : 1 + a / x = (a + x) / x := by
      field_simp
      ring
    rw [suffixError, continuousSuffixError, hratio,
      Real.log_div hsum hx0, Real.negMulLog_def]
    ring

theorem continuousAt_continuousSuffixError
    {a x : ℝ} (hsum : a + x ≠ 0) :
    ContinuousAt
      (fun z : ℝ × ℝ ↦ continuousSuffixError z.1 z.2) (a, x) := by
  unfold continuousSuffixError
  fun_prop

/-- The paper's assertion that `e(a,x)` is continuous is a statement on the
nonnegative quadrant.  This is the exact domain-qualified version. -/
theorem continuousWithinAt_suffixError_nonnegative
    {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hsum : a + x ≠ 0) :
    ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ suffixError z.1 z.2)
      (Set.Ici 0 ×ˢ Set.Ici 0) (a, x) := by
  apply (continuousAt_continuousSuffixError hsum).continuousWithinAt.congr_of_mem
  · intro z hz
    exact suffixError_eq_continuousSuffixError hz.1 hz.2
  · exact ⟨ha, hx⟩

theorem binaryEntropy_eq_realBinEntropy (t : ℝ) :
    binaryEntropy t = Real.binEntropy t := by
  rw [binaryEntropy, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem continuous_binaryEntropy : Continuous binaryEntropy := by
  apply Continuous.congr Real.binEntropy_continuous
  exact fun t ↦ (binaryEntropy_eq_realBinEntropy t).symm

/-- The scalar lower bound `Psi` in paper (28). -/
noncomputable def goodRowPsi (u v q : ℝ) : ℝ :=
  (1 - q) * binaryEntropy (u / (1 - q)) - 1 +
    (1 / 2) *
      (suffixError u q + suffixError u (v + q) +
        suffixError v q + suffixError v (u + q))

/-- A continuous local representative of `goodRowPsi`. -/
noncomputable def continuousGoodRowPsi (u v q : ℝ) : ℝ :=
  (1 - q) * Real.binEntropy (u / (1 - q)) - 1 +
    (1 / 2) *
      (continuousSuffixError u q + continuousSuffixError u (v + q) +
        continuousSuffixError v q + continuousSuffixError v (u + q))

theorem goodRowPsi_eq_continuousGoodRowPsi
    {u v q : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hq : 0 ≤ q) :
    goodRowPsi u v q = continuousGoodRowPsi u v q := by
  rw [goodRowPsi, continuousGoodRowPsi, binaryEntropy_eq_realBinEntropy,
    suffixError_eq_continuousSuffixError hu hq,
    suffixError_eq_continuousSuffixError hu (add_nonneg hv hq),
    suffixError_eq_continuousSuffixError hv hq,
    suffixError_eq_continuousSuffixError hv (add_nonneg hu hq)]

theorem continuousAt_continuousGoodRowPsi_half_half_zero :
    ContinuousAt
      (fun z : ℝ × (ℝ × ℝ) ↦
        continuousGoodRowPsi z.1 z.2.1 z.2.2)
      (1 / 2, (1 / 2, 0)) := by
  unfold continuousGoodRowPsi continuousSuffixError
  fun_prop (disch := norm_num)

/-- Exact domain-qualified continuity statement used in the compactness
argument for paper Lemma 12. -/
theorem continuousWithinAt_goodRowPsi_half_half_zero :
    ContinuousWithinAt
      (fun z : ℝ × (ℝ × ℝ) ↦ goodRowPsi z.1 z.2.1 z.2.2)
      (Set.Ici 0 ×ˢ (Set.Ici 0 ×ˢ Set.Ici 0))
      (1 / 2, (1 / 2, 0)) := by
  apply continuousAt_continuousGoodRowPsi_half_half_zero.continuousWithinAt.congr_of_mem
  · intro z hz
    exact goodRowPsi_eq_continuousGoodRowPsi hz.1 hz.2.1 hz.2.2
  · norm_num

/-- The half--half row produces exactly half a bit of score after paying for
the one ambiguity bit of its core component. -/
theorem goodRowPsi_half_half_zero :
    goodRowPsi (1 / 2) (1 / 2) 0 = Real.log 2 / 2 := by
  rw [goodRowPsi, binaryEntropy_eq_realBinEntropy]
  norm_num [suffixError]
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
  ring

/-- Relative order of two coordinates in an ordering. -/
def CoordinateBefore {n : ℕ} (a b : Fin n) (π : Equiv.Perm (Fin n)) : Prop :=
  π.symm a < π.symm b

instance instDecidableCoordinateBefore
    {n : ℕ} (a b : Fin n) (π : Equiv.Perm (Fin n)) :
    Decidable (CoordinateBefore a b π) := by
  unfold CoordinateBefore
  infer_instance

noncomputable def coordinateBeforeProbability
    {n : ℕ} (a b : Fin n) : ℝ :=
  uniformAverage fun π : Equiv.Perm (Fin n) ↦
    if CoordinateBefore a b π then 1 else 0

theorem coordinateBefore_trans_swap
    {n : ℕ} (a b : Fin n) (π : Equiv.Perm (Fin n)) :
    CoordinateBefore a b (π.trans (Equiv.swap a b)) ↔
      CoordinateBefore b a π := by
  simp [CoordinateBefore, Equiv.trans_apply, Equiv.swap_apply_def]

theorem coordinateBeforeProbability_symm
    {n : ℕ} (a b : Fin n) :
    coordinateBeforeProbability a b = coordinateBeforeProbability b a := by
  let f : Equiv.Perm (Fin n) → ℝ := fun π ↦
    if CoordinateBefore a b π then 1 else 0
  calc
    coordinateBeforeProbability a b = uniformAverage f := rfl
    _ = uniformAverage (fun π : Equiv.Perm (Fin n) ↦
          f (π.trans (Equiv.swap a b))) :=
      (uniformAverage_perm_trans f (Equiv.swap a b)).symm
    _ = coordinateBeforeProbability b a := by
      apply congrArg uniformAverage
      funext π
      exact if_congr (coordinateBefore_trans_swap a b π) rfl rfl

theorem coordinateBeforeProbability_add_reverse
    {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    coordinateBeforeProbability a b + coordinateBeforeProbability b a = 1 := by
  rw [coordinateBeforeProbability, coordinateBeforeProbability,
    ← uniformAverage_add]
  calc
    uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        (if CoordinateBefore a b π then (1 : ℝ) else 0) +
          if CoordinateBefore b a π then 1 else 0) =
        uniformAverage (fun _ : Equiv.Perm (Fin n) ↦ (1 : ℝ)) := by
      apply congrArg uniformAverage
      funext π
      have hne : π.symm a ≠ π.symm b := π.symm.injective.ne hab
      rcases lt_or_gt_of_ne hne with h | h <;>
        simp [CoordinateBefore, h, not_lt_of_ge h.le]
    _ = 1 := uniformAverage_const 1

theorem coordinateBeforeProbability_eq_half
    {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    coordinateBeforeProbability a b = 1 / 2 := by
  have hsymm := coordinateBeforeProbability_symm a b
  have hsum := coordinateBeforeProbability_add_reverse hab
  linarith

theorem strictRightMass_nonneg
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    (π : Equiv.Perm (Fin n)) (a : Fin n) :
    0 ≤ strictRightMass p π a := by
  unfold strictRightMass
  exact Finset.sum_nonneg fun j _ ↦ by
    split_ifs <;> simp_all [hp.nonnegative j]

theorem strictRightMass_le_one_sub
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    (π : Equiv.Perm (Fin n)) (a : Fin n) :
    strictRightMass p π a ≤ 1 - p a := by
  have hleft : 0 ≤ strictLeftMass p π a := by
    unfold strictLeftMass
    exact Finset.sum_nonneg fun j _ ↦ by
      split_ifs <;> simp_all [hp.nonnegative j]
  linarith [strictLeftMass_add_strictRightMass hp π a]

/-- If `b` lies before `a`, the mass after `a` can contain only coordinates
outside the pair `{a,b}`. -/
theorem strictRightMass_le_outside_of_before
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    {π : Equiv.Perm (Fin n)} {a b : Fin n} (hab : a ≠ b)
    (hbefore : CoordinateBefore b a π) :
    strictRightMass p π a ≤ 1 - p a - p b := by
  rw [← sum_away_from_two hp hab]
  unfold strictRightMass
  apply Finset.sum_le_sum
  intro j _
  by_cases haj : a = j
  · subst j
    simp
  by_cases hbj : b = j
  · subst j
    have hnot : ¬π.symm a < π.symm b :=
      not_lt_of_ge hbefore.le
    simp [hnot]
  · by_cases horder : π.symm a < π.symm j
    · simp [haj, hbj, horder, hp.nonnegative j]
    · simp [haj, hbj, horder, hp.nonnegative j]

theorem uniformAverage_mono
    {α : Type*} [Fintype α] {f g : α → ℝ}
    (hfg : ∀ x, f x ≤ g x) :
    uniformAverage f ≤ uniformAverage g := by
  unfold uniformAverage
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun x _ ↦ hfg x) (Nat.cast_nonneg _)

theorem uniformAverage_ite_const
    {α : Type*} [Fintype α] [Nonempty α]
    (P : α → Prop) [DecidablePred P] (a b : ℝ) :
    uniformAverage (fun x ↦ if P x then a else b) =
      b + (a - b) * uniformAverage (fun x ↦ if P x then 1 else 0) := by
  calc
    uniformAverage (fun x ↦ if P x then a else b) =
        uniformAverage (fun x ↦
          b + (a - b) * if P x then (1 : ℝ) else 0) := by
      apply congrArg uniformAverage
      funext x
      by_cases hx : P x <;> simp [hx]
    _ = uniformAverage (fun _ : α ↦ b) +
          uniformAverage (fun x ↦
            (a - b) * if P x then (1 : ℝ) else 0) :=
      uniformAverage_add _ _
    _ = b + (a - b) * uniformAverage
          (fun x ↦ if P x then (1 : ℝ) else 0) := by
      rw [uniformAverage_const, uniformAverage_const_mul]

theorem listSuffixErrorSum_ofFn
    {n : ℕ} (f : Fin n → ℝ) :
    listSuffixErrorSum (List.ofFn f) =
      ∑ t, suffixError (f t) (∑ k, if t < k then f k else 0) := by
  induction n with
  | zero => simp [listSuffixErrorSum]
  | succ n ih =>
      rw [List.ofFn_succ, listSuffixErrorSum, Fin.sum_univ_succ,
        ih (fun k ↦ f k.succ)]
      congr 1
      · congr 1
        rw [List.sum_ofFn, Fin.sum_univ_succ]
        simp
      · apply Finset.sum_congr rfl
        intro t _
        congr 1
        rw [Fin.sum_univ_succ]
        simp

theorem orderedStrictRightMass_eq
    {n : ℕ} (p : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n) :
    (∑ k, if t < k then p (π k) else 0) =
      strictRightMass p π (π t) := by
  unfold strictRightMass
  calc
    (∑ k, if t < k then p (π k) else 0) =
        ∑ k, if π.symm (π t) < π.symm (π k) then p (π k) else 0 := by
      simp
    _ = ∑ j, if π.symm (π t) < π.symm j then p j else 0 :=
      Equiv.sum_comp π
        (fun j ↦ if π.symm (π t) < π.symm j then p j else 0)

theorem listSuffixErrorSum_ofFn_eq_ordered_errors
    {n : ℕ} (p : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    listSuffixErrorSum (List.ofFn (fun t ↦ p (π t))) =
      ∑ j, suffixError (p j) (strictRightMass p π j) := by
  rw [listSuffixErrorSum_ofFn]
  calc
    (∑ t, suffixError (p (π t))
        (∑ k, if t < k then p (π k) else 0)) =
        ∑ t, suffixError (p (π t)) (strictRightMass p π (π t)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [orderedStrictRightMass_eq]
    _ = ∑ j, suffixError (p j) (strictRightMass p π j) :=
      Equiv.sum_comp π (fun j ↦ suffixError (p j) (strictRightMass p π j))

theorem fixed_order_suffixScore_eq_neg_one_add_errors
    {n : ℕ} {p : Fin n → ℝ}
    (hp : IsProbabilityVector p) (π : Equiv.Perm (Fin n)) :
    (∑ j, p j * Real.log (suffixMass p π j)) =
      -1 + ∑ j, suffixError (p j) (strictRightMass p π j) := by
  rw [← listSuffixScore_ofFn_eq_ordered_score,
    ← listSuffixErrorSum_ofFn_eq_ordered_errors]
  apply listSuffixScore_eq_neg_one_add_errors
  · intro x hx
    simp only [List.mem_ofFn] at hx
    obtain ⟨t, rfl⟩ := hx
    exact hp.nonnegative (π t)
  · rw [List.sum_ofFn]
    exact (Equiv.sum_comp π p).trans hp.sum_eq_one

theorem rowT_ge_core_errors
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b) :
    -1 + uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        suffixError (p a) (strictRightMass p π a) +
          suffixError (p b) (strictRightMass p π b)) ≤ rowT p := by
  rw [rowT]
  calc
    -1 + uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        suffixError (p a) (strictRightMass p π a) +
          suffixError (p b) (strictRightMass p π b)) ≤
        -1 + uniformAverage (fun π : Equiv.Perm (Fin n) ↦
          ∑ j, suffixError (p j) (strictRightMass p π j)) := by
      gcongr
      apply uniformAverage_mono
      intro π
      calc
        suffixError (p a) (strictRightMass p π a) +
            suffixError (p b) (strictRightMass p π b) =
            ∑ j ∈ ({a, b} : Finset (Fin n)),
              suffixError (p j) (strictRightMass p π j) := by
          rw [Finset.sum_pair hab]
        _ ≤ ∑ j, suffixError (p j) (strictRightMass p π j) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro j _ _
          exact suffixError_nonneg (hp.nonnegative j)
            (strictRightMass_nonneg hp π j)
    _ = uniformAverage (fun π : Equiv.Perm (Fin n) ↦
          ∑ j, p j * Real.log (suffixMass p π j)) := by
      rw [← uniformAverage_const
        (α := Equiv.Perm (Fin n)) (-1), ← uniformAverage_add]
      apply congrArg uniformAverage
      funext π
      exact (fixed_order_suffixScore_eq_neg_one_add_errors hp π).symm

/-- Each core coordinate sees only outside mass when the other core
coordinate precedes it, an event of probability exactly one half. -/
theorem average_suffixError_core_lower
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b) :
    (1 / 2) *
        (suffixError (p a) (1 - p a - p b) +
          suffixError (p a) (p b + (1 - p a - p b))) ≤
      uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        suffixError (p a) (strictRightMass p π a)) := by
  let q : ℝ := 1 - p a - p b
  have hq : 0 ≤ q := by
    change 0 ≤ 1 - p a - p b
    rw [← sum_away_from_two hp hab]
    exact Finset.sum_nonneg fun j _ ↦ by
      by_cases h : a ≠ j ∧ b ≠ j <;> simp [h, hp.nonnegative j]
  have hpoint : ∀ π : Equiv.Perm (Fin n),
      (if CoordinateBefore b a π then suffixError (p a) q
        else suffixError (p a) (p b + q)) ≤
        suffixError (p a) (strictRightMass p π a) := by
    intro π
    have hright0 := strictRightMass_nonneg hp π a
    by_cases hbefore : CoordinateBefore b a π
    · rw [ite_eq_left hbefore]
      exact suffixError_anti (hp.nonnegative a) hright0
        (strictRightMass_le_outside_of_before hp hab hbefore)
    · rw [ite_eq_right hbefore]
      have hright := strictRightMass_le_one_sub hp π a
      have hmass : p b + q = 1 - p a := by
        dsimp [q]
        ring
      rw [hmass]
      exact suffixError_anti (hp.nonnegative a) hright0 hright
  calc
    (1 / 2) *
        (suffixError (p a) (1 - p a - p b) +
          suffixError (p a) (p b + (1 - p a - p b))) =
        uniformAverage (fun π : Equiv.Perm (Fin n) ↦
          if CoordinateBefore b a π then suffixError (p a) q
          else suffixError (p a) (p b + q)) := by
      rw [uniformAverage_ite_const]
      change _ = _ + _ * coordinateBeforeProbability b a
      rw [coordinateBeforeProbability_eq_half (Ne.symm hab)]
      dsimp [q]
      ring
    _ ≤ uniformAverage (fun π : Equiv.Perm (Fin n) ↦
          suffixError (p a) (strictRightMass p π a)) :=
      uniformAverage_mono hpoint

/-- Averaged two-core suffix-error estimate in paper (28), separated from
the entropy coarsening identity. -/
theorem rowT_ge_two_core_suffix_bound
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b) :
    -1 + (1 / 2) *
        (suffixError (p a) (1 - p a - p b) +
          suffixError (p a) (p b + (1 - p a - p b)) +
          suffixError (p b) (1 - p a - p b) +
          suffixError (p b) (p a + (1 - p a - p b))) ≤
      rowT p := by
  have ha := average_suffixError_core_lower hp hab
  have hb0 := average_suffixError_core_lower hp (Ne.symm hab)
  have hb : (1 / 2) *
        (suffixError (p b) (1 - p a - p b) +
          suffixError (p b) (p a + (1 - p a - p b))) ≤
      uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        suffixError (p b) (strictRightMass p π b)) := by
    convert hb0 using 1 <;> ring
  have hcore := rowT_ge_core_errors hp hab
  rw [uniformAverage_add] at hcore
  nlinarith

/-- Entropy after merging the two core outcomes into one atom while leaving
every outside outcome distinct. -/
noncomputable def twoCoreCoarsenedEntropy
    {n : ℕ} (p : Fin n → ℝ) (a b : Fin n) : ℝ :=
  Real.negMulLog (p a + p b) +
    ∑ j, if a ≠ j ∧ b ≠ j then Real.negMulLog (p j) else 0

theorem sum_eq_two_add_away
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) {a b : ι} (hab : a ≠ b) :
    (∑ j, f j) = f a + f b +
      ∑ j, if a ≠ j ∧ b ≠ j then f j else 0 := by
  calc
    (∑ j, f j) =
        ∑ j, ((if j = a then f j else 0) +
          (if j = b then f j else 0) +
          (if a ≠ j ∧ b ≠ j then f j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hja : j = a
      · subst j
        simp [hab]
      · by_cases hjb : j = b
        · subst j
          simp [hja]
        · simp [hja, hjb, Ne.symm hja, Ne.symm hjb]
    _ = f a + f b +
        ∑ j, if a ≠ j ∧ b ≠ j then f j else 0 := by
      simp_rw [Finset.sum_add_distrib]
      simp

theorem entropy_sub_twoCoreCoarsenedEntropy
    {n : ℕ} (p : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    shannonEntropy p - twoCoreCoarsenedEntropy p a b =
      Real.negMulLog (p a) + Real.negMulLog (p b) -
        Real.negMulLog (p a + p b) := by
  rw [shannonEntropy, twoCoreCoarsenedEntropy,
    sum_eq_two_add_away (fun j ↦ Real.negMulLog (p j)) hab]
  ring

/-- Exact entropy loss from the paper's two-core coarsening, in the
`(u,v,q)` coordinates used to define `Psi`. -/
theorem entropy_sub_twoCoreCoarsenedEntropy_eq
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b) :
    shannonEntropy p - twoCoreCoarsenedEntropy p a b =
      (1 - (1 - p a - p b)) *
        binaryEntropy (p a / (1 - (1 - p a - p b))) := by
  rw [entropy_sub_twoCoreCoarsenedEntropy p hab,
    entropy_loss_merge_two (hp.positive a) (hp.positive b)]
  ring_nf

/-- Paper inequality (28), now including both the entropy-coarsening identity
and the exact permutation-pairing argument for the suffix score. -/
theorem rowScore_sub_twoCoreCoarsenedEntropy_ge_Psi
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b) :
    goodRowPsi (p a) (p b) (1 - p a - p b) ≤
      rowScore p - twoCoreCoarsenedEntropy p a b := by
  have hentropy := entropy_sub_twoCoreCoarsenedEntropy_eq hp hab
  have hsuffix := rowT_ge_two_core_suffix_bound hp.probability hab
  rw [rowScore, goodRowPsi]
  linarith [hentropy]

abbrev GoodRowTriple := ℝ × (ℝ × ℝ)

noncomputable def goodRowCenter : GoodRowTriple := (1 / 2, (1 / 2, 0))

/-- Clamp the radius to the interval on which the paper uses the good-row
estimate.  This makes the modulus defined on all real inputs without changing
it on `[0,1/10]`. -/
noncomputable def goodRowRadius (η : ℝ) : ℝ := max 0 (min η (1 / 10))

theorem goodRowRadius_nonneg (η : ℝ) : 0 ≤ goodRowRadius η := by
  simp [goodRowRadius]

theorem goodRowRadius_le_tenth (η : ℝ) : goodRowRadius η ≤ 1 / 10 := by
  rw [goodRowRadius, max_le_iff]
  constructor
  · norm_num
  · exact min_le_right _ _

theorem goodRowRadius_le_abs (η : ℝ) : goodRowRadius η ≤ |η| := by
  by_cases hη : 0 ≤ η
  · rw [abs_of_nonneg hη, goodRowRadius, max_le_iff]
    exact ⟨hη, min_le_left _ _⟩
  · have hη' : η ≤ 0 := le_of_not_ge hη
    have hmin : min η (1 / 10) ≤ 0 := (min_le_left _ _).trans hη'
    rw [goodRowRadius, max_eq_left hmin]
    exact abs_nonneg η

theorem goodRowRadius_eq { η : ℝ } (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1 / 10) :
    goodRowRadius η = η := by
  unfold goodRowRadius
  rw [min_eq_left hη₁, max_eq_right hη₀]

theorem monotone_goodRowRadius : Monotone goodRowRadius := by
  intro η θ hηθ
  exact max_le_max le_rfl (min_le_min hηθ le_rfl)

theorem goodRowTriple_bounds_of_mem_closedBall
    {z : GoodRowTriple}
    (hz : z ∈ Metric.closedBall goodRowCenter (1 / 10)) :
    2 / 5 ≤ z.1 ∧ z.1 ≤ 3 / 5 ∧
      2 / 5 ≤ z.2.1 ∧ z.2.1 ≤ 3 / 5 ∧
      -(1 / 10) ≤ z.2.2 ∧ z.2.2 ≤ 1 / 10 := by
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff,
    Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq,
    Real.dist_eq] at hz
  rcases hz with ⟨hu, hv, hq⟩
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  have hq' := abs_le.mp hq
  dsimp [goodRowCenter] at hu' hv' hq'
  norm_num at hu' hv' hq' ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith [hu'.1, hu'.2, hv'.1, hv'.2, hq'.1, hq'.2]

theorem continuousOn_continuousGoodRowPsi_closedBall :
    ContinuousOn
      (fun z : GoodRowTriple ↦ continuousGoodRowPsi z.1 z.2.1 z.2.2)
      (Metric.closedBall goodRowCenter (1 / 10)) := by
  intro z hz
  have hb := goodRowTriple_bounds_of_mem_closedBall hz
  have hden : 1 - z.2.2 ≠ 0 := by
    have : 0 < 1 - z.2.2 := by linarith [hb.2.2.2.2.2]
    exact this.ne'
  have huq : z.1 + z.2.2 ≠ 0 := by
    have : 0 < z.1 + z.2.2 := by linarith [hb.1, hb.2.2.2.2.1]
    exact this.ne'
  have hvq : z.2.1 + z.2.2 ≠ 0 := by
    have : 0 < z.2.1 + z.2.2 := by linarith [hb.2.2.1, hb.2.2.2.2.1]
    exact this.ne'
  have huvq : z.1 + (z.2.1 + z.2.2) ≠ 0 := by
    have : 0 < z.1 + (z.2.1 + z.2.2) := by
      linarith [hb.1, hb.2.2.1, hb.2.2.2.2.1]
    exact this.ne'
  have hvuq : z.2.1 + (z.1 + z.2.2) ≠ 0 := by
    have : 0 < z.2.1 + (z.1 + z.2.2) := by
      linarith [hb.1, hb.2.2.1, hb.2.2.2.2.1]
    exact this.ne'
  let S := Metric.closedBall goodRowCenter (1 / 10)
  have hu : ContinuousAt (fun w : GoodRowTriple ↦ w.1) z := continuousAt_fst
  have htail : ContinuousAt (fun w : GoodRowTriple ↦ w.2) z := continuousAt_snd
  have hv : ContinuousAt (fun w : GoodRowTriple ↦ w.2.1) z :=
    continuousAt_fst.comp' htail
  have hq : ContinuousAt (fun w : GoodRowTriple ↦ w.2.2) z :=
    continuousAt_snd.comp' htail
  have hdenC : ContinuousAt (fun w : GoodRowTriple ↦ 1 - w.2.2) z :=
    continuousAt_const.sub hq
  have hentropy : ContinuousAt (fun w : GoodRowTriple ↦
      (1 - w.2.2) * Real.binEntropy (w.1 / (1 - w.2.2)) - 1) z :=
    (hdenC.mul (Real.binEntropy_continuous.continuousAt.comp'
      (hu.div hdenC hden))).sub continuousAt_const
  have hsUQ : ContinuousAt (fun w : GoodRowTriple ↦
      continuousSuffixError w.1 w.2.2) z :=
    ContinuousAt.comp' (f := fun w : GoodRowTriple ↦ (w.1, w.2.2))
      (continuousAt_continuousSuffixError huq) (hu.prodMk hq)
  have hvqC : ContinuousAt (fun w : GoodRowTriple ↦ w.2.1 + w.2.2) z :=
    hv.add hq
  have hsUVQ : ContinuousAt (fun w : GoodRowTriple ↦
      continuousSuffixError w.1 (w.2.1 + w.2.2)) z :=
    ContinuousAt.comp'
      (f := fun w : GoodRowTriple ↦ (w.1, w.2.1 + w.2.2))
      (continuousAt_continuousSuffixError huvq) (hu.prodMk hvqC)
  have hsVQ : ContinuousAt (fun w : GoodRowTriple ↦
      continuousSuffixError w.2.1 w.2.2) z :=
    ContinuousAt.comp' (f := fun w : GoodRowTriple ↦ (w.2.1, w.2.2))
      (continuousAt_continuousSuffixError hvq) (hv.prodMk hq)
  have huqC : ContinuousAt (fun w : GoodRowTriple ↦ w.1 + w.2.2) z :=
    hu.add hq
  have hsVUQ : ContinuousAt (fun w : GoodRowTriple ↦
      continuousSuffixError w.2.1 (w.1 + w.2.2)) z :=
    ContinuousAt.comp'
      (f := fun w : GoodRowTriple ↦ (w.2.1, w.1 + w.2.2))
      (continuousAt_continuousSuffixError hvuq) (hv.prodMk huqC)
  have hhalf : ContinuousAt (fun _w : GoodRowTriple ↦ (1 / 2 : ℝ)) z :=
    continuousAt_const
  have htotal : ContinuousAt (fun w : GoodRowTriple ↦
      (1 - w.2.2) * Real.binEntropy (w.1 / (1 - w.2.2)) - 1 +
        (1 / 2) *
          (continuousSuffixError w.1 w.2.2 +
            continuousSuffixError w.1 (w.2.1 + w.2.2) +
            continuousSuffixError w.2.1 w.2.2 +
            continuousSuffixError w.2.1 (w.1 + w.2.2))) z :=
    hentropy.add (hhalf.mul (((hsUQ.add hsUVQ).add hsVQ).add hsVUQ))
  simpa only [continuousGoodRowPsi] using htotal.continuousWithinAt

noncomputable def goodRowDeviation (z : GoodRowTriple) : ℝ :=
  |Real.log 2 / 2 - continuousGoodRowPsi z.1 z.2.1 z.2.2|

theorem continuousGoodRowPsi_center :
    continuousGoodRowPsi goodRowCenter.1 goodRowCenter.2.1 goodRowCenter.2.2 =
      Real.log 2 / 2 := by
  rw [← goodRowPsi_eq_continuousGoodRowPsi
    (by norm_num [goodRowCenter]) (by norm_num [goodRowCenter])
    (by norm_num [goodRowCenter])]
  simpa [goodRowCenter] using goodRowPsi_half_half_zero

theorem goodRowDeviation_center : goodRowDeviation goodRowCenter = 0 := by
  rw [goodRowDeviation, continuousGoodRowPsi_center]
  simp

theorem continuousAt_goodRowDeviation_center :
    ContinuousAt goodRowDeviation goodRowCenter := by
  unfold goodRowDeviation
  apply ContinuousAt.abs
  apply continuousAt_const.sub
  simpa [goodRowCenter] using
    continuousAt_continuousGoodRowPsi_half_half_zero

theorem continuousOn_goodRowDeviation_closedBall :
    ContinuousOn goodRowDeviation
      (Metric.closedBall goodRowCenter (1 / 10)) := by
  unfold goodRowDeviation
  exact (continuousOn_const.sub
    continuousOn_continuousGoodRowPsi_closedBall).abs

theorem goodRowBall_subset_tenth (η : ℝ) :
    Metric.closedBall goodRowCenter (goodRowRadius η) ⊆
      Metric.closedBall goodRowCenter (1 / 10) :=
  Metric.closedBall_subset_closedBall (goodRowRadius_le_tenth η)

theorem goodRowDeviation_image_bddAbove (η : ℝ) :
    BddAbove (goodRowDeviation ''
      Metric.closedBall goodRowCenter (goodRowRadius η)) := by
  have hbig : BddAbove (goodRowDeviation ''
      Metric.closedBall goodRowCenter (1 / 10)) :=
    (isCompact_closedBall goodRowCenter (1 / 10)).bddAbove_image
      continuousOn_goodRowDeviation_closedBall
  exact hbig.mono (Set.image_mono (goodRowBall_subset_tenth η))

theorem goodRowBall_nonempty (η : ℝ) :
    (Metric.closedBall goodRowCenter (goodRowRadius η)).Nonempty := by
  exact ⟨goodRowCenter, by
    rw [Metric.mem_closedBall, dist_self]
    exact goodRowRadius_nonneg η⟩

/-- A monotone modulus for the compactness step in paper Lemma 12.  We use
absolute deviation rather than only its positive part; this is slightly
stronger and gives the same score bound. -/
noncomputable def goodRowOmega (η : ℝ) : ℝ :=
  sSup (goodRowDeviation ''
    Metric.closedBall goodRowCenter (goodRowRadius η))

theorem goodRowOmega_nonneg (η : ℝ) : 0 ≤ goodRowOmega η := by
  rw [goodRowOmega, ← goodRowDeviation_center]
  apply le_csSup (goodRowDeviation_image_bddAbove η)
  exact ⟨goodRowCenter, by
    rw [Metric.mem_closedBall, dist_self]
    exact goodRowRadius_nonneg η, rfl⟩

theorem monotone_goodRowOmega : Monotone goodRowOmega := by
  intro η θ hηθ
  unfold goodRowOmega
  apply csSup_le_csSup (goodRowDeviation_image_bddAbove θ)
    ((goodRowBall_nonempty η).image goodRowDeviation)
  exact Set.image_mono (Metric.closedBall_subset_closedBall
    (monotone_goodRowRadius hηθ))

theorem goodRowDeviation_le_omega
    {η : ℝ} {z : GoodRowTriple}
    (hz : z ∈ Metric.closedBall goodRowCenter (goodRowRadius η)) :
    goodRowDeviation z ≤ goodRowOmega η := by
  apply le_csSup (goodRowDeviation_image_bddAbove η)
  exact ⟨z, hz, rfl⟩

theorem goodRowPsi_ge_half_log_sub_omega
    {η u v q : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hq : 0 ≤ q)
    (hz : (u, (v, q)) ∈
      Metric.closedBall goodRowCenter (goodRowRadius η)) :
    Real.log 2 / 2 - goodRowOmega η ≤ goodRowPsi u v q := by
  have hdev := goodRowDeviation_le_omega hz
  rw [goodRowDeviation, ← goodRowPsi_eq_continuousGoodRowPsi hu hv hq] at hdev
  exact le_of_sub_nonneg (by
    have := le_trans (le_abs_self (Real.log 2 / 2 - goodRowPsi u v q)) hdev
    linarith)

/-- The compact-ball modulus tends to zero as its radius shrinks. -/
theorem tendsto_goodRowOmega_zero :
    Tendsto goodRowOmega (nhds 0) (nhds 0) := by
  rw [Metric.tendsto_nhds_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ :=
    (Metric.continuousAt_iff.mp continuousAt_goodRowDeviation_center)
      (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro η hη
  have hωle : goodRowOmega η ≤ ε / 2 := by
    unfold goodRowOmega
    apply csSup_le ((goodRowBall_nonempty η).image goodRowDeviation)
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hzdist : dist z goodRowCenter < δ := by
      have hzle : dist z goodRowCenter ≤ goodRowRadius η :=
        Metric.mem_closedBall.mp hz
      have hrabs := goodRowRadius_le_abs η
      have habs : |η| = dist η 0 := by rw [Real.dist_eq, sub_zero]
      have habslt : |η| < δ := by rw [habs]; exact hη
      exact hzle.trans_lt (hrabs.trans_lt habslt)
    have hsmall := hcont hzdist
    rw [goodRowDeviation_center, Real.dist_eq, sub_zero] at hsmall
    have hdev0 : 0 ≤ goodRowDeviation z := by
      unfold goodRowDeviation
      exact abs_nonneg _
    rw [abs_of_nonneg hdev0] at hsmall
    exact hsmall.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (goodRowOmega_nonneg η)]
  exact hωle.trans_lt (half_lt_self hε)

/-- Paper Lemma 12.  A row within `η` in `L¹` of a half--half vector admits
two core coordinates such that its averaged sequential score exceeds the
entropy of the corresponding two-core coarsening by
`(log 2)/2 - goodRowOmega η`.  The modulus is monotone and tends to zero by
`monotone_goodRowOmega` and `tendsto_goodRowOmega_zero`. -/
theorem goodRow_score
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1 / 10)
    (hgood : IsGoodRow η p) :
    ∃ a b : Fin n, a ≠ b ∧
      halfHalfL1Distance p a b ≤ η ∧
        Real.log 2 / 2 - goodRowOmega η ≤
          rowScore p - twoCoreCoarsenedEntropy p a b := by
  obtain ⟨a, b, hab, hdist⟩ := hgood
  let q := 1 - p a - p b
  have hq₀ : 0 ≤ q := by
    have hsum : 0 ≤
        ∑ j, if a ≠ j ∧ b ≠ j then p j else 0 := by
      apply Finset.sum_nonneg
      intro j _
      split_ifs
      · exact hp.probability.nonnegative j
      · exact le_rfl
    rw [sum_away_from_two hp.probability hab] at hsum
    exact hsum
  have hdist' : |p a - 1 / 2| + |p b - 1 / 2| + q ≤ η := by
    rw [halfHalfL1Distance_eq hp.probability hab] at hdist
    exact hdist
  have haη : |p a - 1 / 2| ≤ η := by
    linarith [abs_nonneg (p b - 1 / 2)]
  have hbη : |p b - 1 / 2| ≤ η := by
    linarith [abs_nonneg (p a - 1 / 2)]
  have hqη : q ≤ η := by
    linarith [abs_nonneg (p a - 1 / 2), abs_nonneg (p b - 1 / 2)]
  have hz : (p a, (p b, q)) ∈
      Metric.closedBall goodRowCenter (goodRowRadius η) := by
    rw [Metric.mem_closedBall, goodRowRadius_eq hη₀ hη₁,
      Prod.dist_eq, Prod.dist_eq, max_le_iff, max_le_iff]
    dsimp [goodRowCenter]
    constructor
    · simpa [Real.dist_eq] using haη
    constructor
    · simpa [Real.dist_eq] using hbη
    · simpa [Real.dist_eq, abs_of_nonneg hq₀] using hqη
  refine ⟨a, b, hab, hdist, ?_⟩
  exact (goodRowPsi_ge_half_log_sub_omega
    (hp.probability.nonnegative a) (hp.probability.nonnegative b) hq₀ hz).trans
      (rowScore_sub_twoCoreCoarsenedEntropy_ge_Psi hp hab)

end BeyondBethe
