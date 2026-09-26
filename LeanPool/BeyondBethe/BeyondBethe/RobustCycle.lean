/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.GoodRowScore
public import LeanPool.BeyondBethe.BeyondBethe.Sequential
public import LeanPool.BeyondBethe.BeyondBethe.Slack

/-! # Robust Cycle -/

@[expose] public section

namespace BeyondBethe

/-- Inversion as an equivalence on permutations.  The Gibbs layer represents
an assignment as `column -> row`, whereas the cycle layer represents it as
`row -> column`; this equivalence makes the conversion explicit. -/
def permInverseEquiv {α : Type*} : Equiv.Perm α ≃ Equiv.Perm α where
  toFun σ := σ.symm
  invFun σ := σ.symm
  left_inv σ := by simp
  right_inv σ := by simp

/-- The row-oriented version of a mass on Mathlib's column-oriented
permutations. -/
noncomputable def rowOrientedMass
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : Equiv.Perm α → ℝ) : Equiv.Perm α → ℝ :=
  pushforwardMass μ permInverseEquiv

theorem rowOrientedMass_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : Equiv.Perm α → ℝ) (σ : Equiv.Perm α) :
    rowOrientedMass μ σ = μ σ.symm := by
  exact pushforwardMass_equiv_apply μ permInverseEquiv σ

theorem rowOrientedMass_isProbabilityVector
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : Equiv.Perm α → ℝ} (hμ : IsProbabilityVector μ) :
    IsProbabilityVector (rowOrientedMass μ) :=
  pushforwardMass_isProbabilityVector μ hμ permInverseEquiv

theorem shannonEntropy_rowOrientedMass
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : Equiv.Perm α → ℝ) :
    shannonEntropy (rowOrientedMass μ) = shannonEntropy μ :=
  shannonEntropy_pushforward_equiv μ permInverseEquiv

/-- Evaluation of the row-oriented assignment has exactly the prescribed
row marginal. -/
theorem rowOriented_evaluation_mass
    {n : ℕ} {μ : Equiv.Perm (Fin n) → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hmarg : HasAssignmentMarginals μ P) (i j : Fin n) :
    pushforwardMass (rowOrientedMass μ) (fun σ ↦ σ i) j = P i j := by
  classical
  rw [rowOrientedMass, pushforwardMass_comp]
  rw [hmarg i j]
  unfold pushforwardMass
  apply Finset.sum_congr rfl
  intro σ _
  have heq : (permInverseEquiv σ) i = j ↔ σ j = i := by
    change σ.symm i = j ↔ σ j = i
    constructor
    · intro h
      simpa using (congrArg σ h).symm
    · intro h
      simpa using (congrArg σ.symm h).symm
  by_cases h : σ j = i
  · simp [h, heq.mpr h]
  · have hs : ¬(permInverseEquiv σ) i = j := fun hs ↦ h (heq.mp hs)
    simp [h, hs]

/-- Relabel the two core outcomes by `none` and retain every outside outcome
as `some j`. -/
def coreOutcome {α : Type*} [DecidableEq α] (a b j : α) : Option α :=
  if j = a ∨ j = b then none else some j

theorem twoMatchingEncoding_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (f g σ : Equiv.Perm α) (i : α) :
    twoMatchingEncoding f g σ i = coreOutcome (f i) (g i) (σ i) := by
  by_cases h : UsesCoreEdge f g σ i
  · have h' : σ i = f i ∨ σ i = g i := h
    simp [twoMatchingEncoding, coreOutcome, h, h']
  · have h' : ¬(σ i = f i ∨ σ i = g i) := h
    simp [twoMatchingEncoding, coreOutcome, h, h']

theorem coordinateEncoding_mass
    {n : ℕ} {μ : Equiv.Perm (Fin n) → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hmarg : HasAssignmentMarginals μ P)
    (f g : Equiv.Perm (Fin n)) (i : Fin n) :
    pushforwardMass (rowOrientedMass μ)
        (fun σ ↦ twoMatchingEncoding f g σ i) =
      pushforwardMass (P i) (coreOutcome (f i) (g i)) := by
  funext y
  have hfun : (fun σ ↦ twoMatchingEncoding f g σ i) =
      coreOutcome (f i) (g i) ∘ (fun σ ↦ σ i) := by
    funext σ
    exact twoMatchingEncoding_apply f g σ i
  rw [hfun, ← pushforwardMass_comp]
  congr 1
  funext j
  exact rowOriented_evaluation_mass hmarg i j

theorem coreOutcome_none_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) {a b : α} (hab : a ≠ b) :
    pushforwardMass p (coreOutcome a b) none = p a + p b := by
  unfold pushforwardMass
  calc
    (∑ j, if coreOutcome a b j = none then p j else 0) =
        ∑ j, if j = a ∨ j = b then p j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = a ∨ j = b <;> simp [coreOutcome, h]
    _ = p a + p b := by
      calc
        (∑ j, if j = a ∨ j = b then p j else 0) =
            ∑ j, ((if j = a then p j else 0) +
              (if j = b then p j else 0)) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hja : j = a
          · subst j
            simp [hab]
          · by_cases hjb : j = b <;> simp [hja, hjb, hab, Ne.symm hab]
        _ = p a + p b := by rw [Finset.sum_add_distrib]; simp

theorem coreOutcome_some_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (a b j : α) :
    pushforwardMass p (coreOutcome a b) (some j) =
      if a ≠ j ∧ b ≠ j then p j else 0 := by
  unfold pushforwardMass
  by_cases hj : a ≠ j ∧ b ≠ j
  · rw [ite_eq_left hj, Finset.sum_eq_single j]
    · simp [coreOutcome, hj.1.symm, hj.2.symm]
    · intro k _ hkj
      have hne : coreOutcome a b k ≠ some j := by
        by_cases hk : k = a ∨ k = b
        · simp [coreOutcome, hk]
        · simp [coreOutcome, hk, hkj]
      simp [hne]
    · simp
  · rw [ite_eq_right hj]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = a ∨ k = b
    · simp [coreOutcome, hk]
    · have hkj : k ≠ j := by
        intro h
        subst k
        exact hj ⟨fun h ↦ hk (Or.inl h.symm), fun h ↦ hk (Or.inr h.symm)⟩
      simp [coreOutcome, hk, hkj]

/-- The rowwise encoding entropy is exactly the entropy obtained by merging
the two distinct core atoms. -/
theorem coreOutcome_entropy_eq_twoCoreCoarsenedEntropy
    {n : ℕ} (p : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    shannonEntropy (pushforwardMass p (coreOutcome a b)) =
      twoCoreCoarsenedEntropy p a b := by
  rw [shannonEntropy, Fintype.sum_option, coreOutcome_none_mass p hab]
  simp_rw [coreOutcome_some_mass]
  unfold twoCoreCoarsenedEntropy
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem coreOutcome_none_mass_same
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (a : α) :
    pushforwardMass p (coreOutcome a a) none = p a := by
  unfold pushforwardMass
  rw [Finset.sum_eq_single a]
  · simp [coreOutcome]
  · intro j _ hja
    simp [coreOutcome, hja]
  · simp

theorem coreOutcome_entropy_same
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (a : α) :
    shannonEntropy (pushforwardMass p (coreOutcome a a)) =
      shannonEntropy p := by
  rw [shannonEntropy, Fintype.sum_option, coreOutcome_none_mass_same p a]
  simp_rw [coreOutcome_some_mass]
  have hout := sum_ite_ne_eq_sum_sub
    (fun j ↦ Real.negMulLog (p j)) a
  have hsimp :
      (∑ x, Real.negMulLog (if a ≠ x ∧ a ≠ x then p x else 0)) =
        ∑ x, if x ≠ a then Real.negMulLog (p x) else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hxa : x = a
    · subst x
      simp
    · have hax : a ≠ x := Ne.symm hxa
      simp [hxa, hax]
  rw [shannonEntropy]
  rw [hsimp, hout]
  ring

theorem coreOutcome_entropy_le
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    (a b : Fin n) :
    shannonEntropy (pushforwardMass p (coreOutcome a b)) ≤
      shannonEntropy p := by
  by_cases hab : a = b
  · subst b
    exact (coreOutcome_entropy_same p a).le
  · rw [coreOutcome_entropy_eq_twoCoreCoarsenedEntropy p hab]
    have hu := hp.positive a
    have hv := hp.positive b
    have hsum : 0 < p a + p b := add_pos hu hv
    have hr0 : 0 ≤ p a / (p a + p b) := div_nonneg hu.le hsum.le
    have hr1 : p a / (p a + p b) ≤ 1 :=
      (div_le_one hsum).2 (le_add_of_nonneg_right hv.le)
    have hbin : 0 ≤ binaryEntropy (p a / (p a + p b)) := by
      rw [binaryEntropy_eq_realBinEntropy]
      exact Real.binEntropy_nonneg hr0 hr1
    have hloss := entropy_loss_merge_two hu hv
    have hent := entropy_sub_twoCoreCoarsenedEntropy p hab
    rw [hloss] at hent
    nlinarith

theorem coreOutcome_comm
    {α : Type*} [DecidableEq α] (a b : α) :
    coreOutcome a b = coreOutcome b a := by
  funext j
  by_cases h : j = a ∨ j = b
  · have h' : j = b ∨ j = a := h.elim Or.inr Or.inl
    simp [coreOutcome, h, h']
  · have h' : ¬(j = b ∨ j = a) := by
      intro h'
      exact h (h'.elim Or.inr Or.inl)
    simp [coreOutcome, h, h']

theorem coreOutcome_eq_of_pair_membership
    {α : Type*} [DecidableEq α]
    {a b c d : α} (hab : a ≠ b)
    (ha : a = c ∨ a = d) (hb : b = c ∨ b = d) :
    coreOutcome c d = coreOutcome a b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact False.elim (hab (ha.trans hb.symm))
  · rw [ha, hb]
  · rw [ha, hb, coreOutcome_comm]
  · exact False.elim (hab (ha.trans hb.symm))

/-- The exact `L¹` witness of a good row supplies two heavy coordinates. -/
theorem goodRow_witness_mem_heavyCoordinates
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    {η : ℝ} {a b : Fin n} (hab : a ≠ b)
    (hdist : halfHalfL1Distance p a b ≤ η) :
    a ∈ heavyCoordinates η p ∧ b ∈ heavyCoordinates η p := by
  have hq₀ : 0 ≤ 1 - p a - p b := by
    have hsum : 0 ≤
        ∑ j, if a ≠ j ∧ b ≠ j then p j else 0 := by
      apply Finset.sum_nonneg
      intro j _
      split_ifs
      · exact hp.nonnegative j
      · exact le_rfl
    rw [sum_away_from_two hp hab] at hsum
    exact hsum
  rw [halfHalfL1Distance_eq hp hab] at hdist
  have haη : |p a - 1 / 2| ≤ η := by
    linarith [abs_nonneg (p b - 1 / 2)]
  have hbη : |p b - 1 / 2| ≤ η := by
    linarith [abs_nonneg (p a - 1 / 2)]
  have ha : 1 / 2 - η ≤ p a := by
    linarith [neg_abs_le (p a - 1 / 2)]
  have hb : 1 / 2 - η ≤ p b := by
    linarith [neg_abs_le (p b - 1 / 2)]
  simpa [heavyCoordinates] using And.intro ha hb

/-- A good row has the paper's half-bit score relative to the coordinate of
the actual two-matching encoding. -/
theorem goodRow_coordinateEncoding_score
    {n : ℕ} {μ : Equiv.Perm (Fin n) → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hmarg : HasAssignmentMarginals μ P)
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1 / 10)
    (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (P i) →
      j = f i ∨ j = g i)
    {i : Fin n} (hgood : IsGoodRow η (P i)) :
    Real.log 2 / 2 - goodRowOmega η ≤
      rowScore (P i) -
        shannonEntropy (pushforwardMass (rowOrientedMass μ)
          (fun σ ↦ twoMatchingEncoding f g σ i)) := by
  obtain ⟨a, b, hab, hdist, hscore⟩ :=
    goodRow_score (hP i) hη₀ hη₁ hgood
  have hcore := goodRow_witness_mem_heavyCoordinates
    (hP i).probability hab hdist
  have ha := hheavy i a hcore.1
  have hb := hheavy i b hcore.2
  have houtcome : coreOutcome (f i) (g i) = coreOutcome a b :=
    coreOutcome_eq_of_pair_membership hab ha hb
  have hentropy :
      shannonEntropy (pushforwardMass (rowOrientedMass μ)
        (fun σ ↦ twoMatchingEncoding f g σ i)) =
        twoCoreCoarsenedEntropy (P i) a b := by
    rw [coordinateEncoding_mass hmarg f g i, houtcome,
      coreOutcome_entropy_eq_twoCoreCoarsenedEntropy (P i) hab]
  rw [hentropy]
  exact hscore

/-- The coarse `-1` score bound for any row, relative to the same coordinate
encoding. -/
theorem coordinateEncoding_score_ge_neg_one
    {n : ℕ} {μ : Equiv.Perm (Fin n) → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hmarg : HasAssignmentMarginals μ P)
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    (f g : Equiv.Perm (Fin n)) (i : Fin n) :
    -1 ≤ rowScore (P i) -
      shannonEntropy (pushforwardMass (rowOrientedMass μ)
        (fun σ ↦ twoMatchingEncoding f g σ i)) := by
  have hrow := rowScore_ge_entropy_sub_one (hP i).probability
  have hentropy :
      shannonEntropy (pushforwardMass (rowOrientedMass μ)
        (fun σ ↦ twoMatchingEncoding f g σ i)) ≤
        shannonEntropy (P i) := by
    rw [coordinateEncoding_mass hmarg f g i]
    exact coreOutcome_entropy_le (hP i) (f i) (g i)
  linarith

/-- Paper Lemma 9 with the joint encoding entropy replaced by the sum of its
coordinate entropies. -/
theorem twoMatching_coreEncoding_sum_coordinates
    {n : ℕ} {μ : Equiv.Perm (Fin n) → ℝ}
    (hμ : IsProbabilityVector μ) (f g : Equiv.Perm (Fin n)) :
    shannonEntropy μ ≤
      (∑ i, shannonEntropy (pushforwardMass (rowOrientedMass μ)
        (fun σ ↦ twoMatchingEncoding f g σ i))) +
      (alternatingRowPerm f g).cycleFactorsFinset.card * Real.log 2 := by
  let μr := rowOrientedMass μ
  let Y := twoMatchingEncoding f g
  have hμr : IsProbabilityVector μr := rowOrientedMass_isProbabilityVector hμ
  have hcore := twoMatching_coreEncoding hμr f g
  have hY : IsProbabilityVector (pushforwardMass μr Y) :=
    pushforwardMass_isProbabilityVector μr hμr Y
  have hsub := functionEntropy_le_sum_coordinateEntropies hY
  have hcoord (i : Fin n) :
      pushforwardMass (pushforwardMass μr Y) (fun y ↦ y i) =
        pushforwardMass μr (fun σ ↦ twoMatchingEncoding f g σ i) := by
    funext y
    rw [pushforwardMass_comp]
    congr 1
  simp_rw [hcoord] at hsub
  rw [shannonEntropy_rowOrientedMass] at hcore
  linarith

/-- Selects the matrix rows satisfying the good-row predicate at threshold `η`. -/
noncomputable def goodRows
    {n : ℕ} (η : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i ↦ IsGoodRow η (P i)

theorem goodRows_disjoint_badRows
    {n : ℕ} (η : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :
    Disjoint (goodRows η P) (badRows η P) := by
  classical
  rw [Finset.disjoint_left]
  intro i hgood hbad
  simp [goodRows, badRows] at hgood hbad
  exact hbad hgood

theorem goodRows_union_badRows
    {n : ℕ} (η : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :
    goodRows η P ∪ badRows η P = Finset.univ := by
  classical
  ext i
  by_cases h : IsGoodRow η (P i) <;> simp [goodRows, badRows, h]

theorem goodRows_card_add_badRows_card
    {n : ℕ} (η : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :
    (goodRows η P).card + (badRows η P).card = n := by
  rw [← Finset.card_union_of_disjoint (goodRows_disjoint_badRows η P),
    goodRows_union_badRows]
  simp

/-- Sum of the good-row and coarse bad-row estimates, before applying the
joint core-encoding inequality. -/
theorem sum_coordinateEncoding_score_lower
    {n : ℕ} {μ : Equiv.Perm (Fin n) → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hmarg : HasAssignmentMarginals μ P)
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1 / 10)
    (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (P i) →
      j = f i ∨ j = g i) :
    ((goodRows η P).card : ℝ) *
          (Real.log 2 / 2 - goodRowOmega η) -
        (badRows η P).card ≤
      ∑ i, (rowScore (P i) -
        shannonEntropy (pushforwardMass (rowOrientedMass μ)
          (fun σ ↦ twoMatchingEncoding f g σ i))) := by
  let d : Fin n → ℝ := fun i ↦ rowScore (P i) -
    shannonEntropy (pushforwardMass (rowOrientedMass μ)
      (fun σ ↦ twoMatchingEncoding f g σ i))
  have hgood : ((goodRows η P).card : ℝ) *
        (Real.log 2 / 2 - goodRowOmega η) ≤
      ∑ i ∈ goodRows η P, d i := by
    calc
      ((goodRows η P).card : ℝ) *
          (Real.log 2 / 2 - goodRowOmega η) =
          ∑ i ∈ goodRows η P,
            (Real.log 2 / 2 - goodRowOmega η) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ goodRows η P, d i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : IsGoodRow η (P i) := by
          simpa [goodRows] using hi
        exact goodRow_coordinateEncoding_score hmarg hP hη₀ hη₁
          f g hheavy hi'
  have hbad : -((badRows η P).card : ℝ) ≤
      ∑ i ∈ badRows η P, d i := by
    calc
      -((badRows η P).card : ℝ) = ∑ i ∈ badRows η P, (-1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ∑ i ∈ badRows η P, d i := by
        apply Finset.sum_le_sum
        intro i _
        exact coordinateEncoding_score_ge_neg_one hmarg hP f g i
  have hpartition : (∑ i, d i) =
      (∑ i ∈ goodRows η P, d i) + ∑ i ∈ badRows η P, d i := by
    rw [← Finset.sum_union (goodRows_disjoint_badRows η P),
      goodRows_union_badRows]
  change _ ≤ ∑ i, d i
  rw [hpartition]
  linarith

/-- The graph-indexed entropy-score inequality (paper (29)). -/
theorem divergence_ge_good_bad_cycleScore
    {n : ℕ} {μ : Equiv.Perm (Fin n) → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hμ : IsProbabilityVector μ)
    (hmarg : HasAssignmentMarginals μ P)
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1 / 10)
    (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (P i) →
      j = f i ∨ j = g i)
    {D : ℝ} (hD : D = -shannonEntropy μ + ∑ i, rowScore (P i)) :
    ((goodRows η P).card : ℝ) *
          (Real.log 2 / 2 - goodRowOmega η) -
        (badRows η P).card -
        (alternatingRowPerm f g).cycleFactorsFinset.card * Real.log 2 ≤ D := by
  have hcore := twoMatching_coreEncoding_sum_coordinates hμ f g
  have hrows := sum_coordinateEncoding_score_lower
    hmarg hP hη₀ hη₁ f g hheavy
  rw [Finset.sum_sub_distrib] at hrows
  rw [hD]
  linarith

theorem goodRow_mem_alternating_support
    {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    {η : ℝ} (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (P i) →
      j = f i ∨ j = g i)
    {i : Fin n} (hgood : IsGoodRow η (P i)) :
    i ∈ (alternatingRowPerm f g).support := by
  obtain ⟨a, b, hab, hdist⟩ := hgood
  have hcore := goodRow_witness_mem_heavyCoordinates
    (hP i).probability hab hdist
  have ha := hheavy i a hcore.1
  have hb := hheavy i b hcore.2
  have hfg : f i ≠ g i := by
    intro h
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hab (ha.trans hb.symm)
    · exact hab (ha.trans (h.trans hb.symm))
    · exact hab (ha.trans (h.symm.trans hb.symm))
    · exact hab (ha.trans hb.symm)
  rw [Equiv.Perm.mem_support]
  intro hfix
  exact hfg ((alternatingRowPerm_fixed_iff f g i).1 hfix)

/-- The supports of the nontrivial cycle factors partition any set contained
in the support of the ambient permutation. -/
theorem sum_cycleSupport_inter_card
    {α : Type*} [Fintype α] [DecidableEq α]
    (h : Equiv.Perm α) (S : Finset α) (hS : S ⊆ h.support) :
    (∑ c : h.cycleFactorsFinset, ((c : Equiv.Perm α).support ∩ S).card) =
      S.card := by
  let t : Equiv.Perm α → Finset α := fun c ↦ c.support ∩ S
  have hpair : (↑h.cycleFactorsFinset : Set (Equiv.Perm α)).PairwiseDisjoint t := by
    intro c hc d hd hcd
    have hdisj := h.cycleFactorsFinset_pairwise_disjoint hc hd hcd
    exact hdisj.disjoint_support.mono inf_le_left inf_le_left
  have hunion : h.cycleFactorsFinset.biUnion t = S := by
    ext i
    constructor
    · intro hi
      obtain ⟨c, _, hi⟩ := Finset.mem_biUnion.mp hi
      exact (Finset.mem_inter.mp hi).2
    · intro hi
      have hisupp := hS hi
      obtain ⟨c, hc, hic⟩ :=
        Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hisupp
      exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_inter.mpr ⟨hic, hi⟩⟩
  calc
    (∑ c : h.cycleFactorsFinset,
        ((c : Equiv.Perm α).support ∩ S).card) =
        ∑ c ∈ h.cycleFactorsFinset, (t c).card := by
      simpa [t] using Finset.sum_coe_sort h.cycleFactorsFinset
        (fun c ↦ (t c).card)
    _ = (h.cycleFactorsFinset.biUnion t).card :=
      (Finset.card_biUnion hpair).symm
    _ = S.card := by rw [hunion]

theorem sum_cycleSupport_inter_card_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (h : Equiv.Perm α) (S : Finset α) :
    (∑ c : h.cycleFactorsFinset, ((c : Equiv.Perm α).support ∩ S).card) ≤
      S.card := by
  let t : Equiv.Perm α → Finset α := fun c ↦ c.support ∩ S
  have hpair : (↑h.cycleFactorsFinset : Set (Equiv.Perm α)).PairwiseDisjoint t := by
    intro c hc d hd hcd
    have hdisj := h.cycleFactorsFinset_pairwise_disjoint hc hd hcd
    exact hdisj.disjoint_support.mono inf_le_left inf_le_left
  have hsubset : h.cycleFactorsFinset.biUnion t ⊆ S := by
    intro i hi
    obtain ⟨c, _, hi⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_inter.mp hi).2
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_biUnion hpair] at hcard
  calc
    (∑ c : h.cycleFactorsFinset,
        ((c : Equiv.Perm α).support ∩ S).card) =
        ∑ c ∈ h.cycleFactorsFinset, (t c).card := by
      simpa [t] using Finset.sum_coe_sort h.cycleFactorsFinset
        (fun c ↦ (t c).card)
    _ ≤ S.card := hcard

/-- Counts the good rows in a permutation cycle factor's support. -/
noncomputable def cycleGoodCount
    {n : ℕ} (η : ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (h : Equiv.Perm (Fin n)) (c : h.cycleFactorsFinset) : ℕ :=
  ((c : Equiv.Perm (Fin n)).support ∩ goodRows η P).card

/-- Counts the bad rows in a permutation cycle factor's support. -/
noncomputable def cycleBadCount
    {n : ℕ} (η : ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (h : Equiv.Perm (Fin n)) (c : h.cycleFactorsFinset) : ℕ :=
  ((c : Equiv.Perm (Fin n)).support ∩ badRows η P).card

/-- Sums the long-component good-row contribution over all cycle factors of the permutation. -/
noncomputable def longCycleGoodRows
    {n : ℕ} (η : ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (h : Equiv.Perm (Fin n)) : ℕ :=
  ∑ c : h.cycleFactorsFinset,
    longComponentGoodRows (c : Equiv.Perm (Fin n)).support.card
      (cycleGoodCount η P h c)

/-- Indicator that a nontrivial alternating component has exactly two rows,
both of them good.  Such a component is one of the paper's clean pairs. -/
noncomputable def cleanCycleIndicator
    {n : ℕ} (η : ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (h : Equiv.Perm (Fin n)) (c : h.cycleFactorsFinset) : ℕ :=
  if (c : Equiv.Perm (Fin n)).support.card = 2 ∧
      cycleGoodCount η P h c = 2 then 1 else 0

/-- Sums clean-cycle indicators over the permutation's cycle factors. -/
noncomputable def cleanCycleCount
    {n : ℕ} (η : ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (h : Equiv.Perm (Fin n)) : ℕ :=
  ∑ c : h.cycleFactorsFinset, cleanCycleIndicator η P h c

theorem cycleGoodCount_add_cycleBadCount
    {n : ℕ} (η : ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (h : Equiv.Perm (Fin n)) (c : h.cycleFactorsFinset) :
    cycleGoodCount η P h c + cycleBadCount η P h c =
      (c : Equiv.Perm (Fin n)).support.card := by
  have hdisj : Disjoint
      ((c : Equiv.Perm (Fin n)).support ∩ goodRows η P)
      ((c : Equiv.Perm (Fin n)).support ∩ badRows η P) :=
    (goodRows_disjoint_badRows η P).mono inf_le_right inf_le_right
  rw [cycleGoodCount, cycleBadCount,
    ← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext i
  simp only [Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
  · intro hi
    have hcover : i ∈ goodRows η P ∪ badRows η P := by
      rw [goodRows_union_badRows]
      simp
    rcases Finset.mem_union.mp hcover with hgood | hbad
    · exact Or.inl ⟨hi, hgood⟩
    · exact Or.inr ⟨hi, hbad⟩

/-- Paper component accounting (30), now instantiated with the actual cycle
factors of the completed two-matching graph. -/
theorem alternating_component_accounting
    {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    {η : ℝ} (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (P i) →
      j = f i ∨ j = g i) :
    ((longCycleGoodRows η P (alternatingRowPerm f g) : ℕ) : ℝ) / 6 -
        ((badRows η P).card : ℝ) / 2 ≤
      ((goodRows η P).card : ℝ) / 2 -
        ((alternatingRowPerm f g).cycleFactorsFinset.card : ℝ) := by
  let h := alternatingRowPerm f g
  let k : h.cycleFactorsFinset → ℕ :=
    fun c ↦ (c : Equiv.Perm (Fin n)).support.card
  let gc : h.cycleFactorsFinset → ℕ := cycleGoodCount η P h
  let bc : h.cycleFactorsFinset → ℕ := cycleBadCount η P h
  have hk2 : ∀ c, 2 ≤ k c := by
    intro c
    exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.property).1.two_le_card_support
  have hpartition : ∀ c, gc c + bc c = k c := by
    intro c
    exact cycleGoodCount_add_cycleBadCount η P h c
  have hcomp := component_accounting k gc bc
    (fun c ↦ le_trans (by norm_num) (hk2 c)) hpartition
    (fun c hc ↦ False.elim (by
      have hc2 := hk2 c
      omega))
  have hgoodSupport : goodRows η P ⊆ h.support := by
    intro i hi
    have hgood : IsGoodRow η (P i) := by simpa [goodRows] using hi
    exact goodRow_mem_alternating_support hP f g hheavy hgood
  have hgoodSum : (∑ c, gc c) = (goodRows η P).card := by
    simpa [gc, cycleGoodCount] using
      sum_cycleSupport_inter_card h (goodRows η P) hgoodSupport
  have hbadSum : (∑ c, bc c) ≤ (badRows η P).card := by
    simpa [bc, cycleBadCount] using
      sum_cycleSupport_inter_card_le h (badRows η P)
  have hm : (∑ c, nontrivialComponentCount (k c)) =
      h.cycleFactorsFinset.card := by
    calc
      (∑ c, nontrivialComponentCount (k c)) = ∑ _c, 1 := by
        apply Finset.sum_congr rfl
        intro c _
        simp [nontrivialComponentCount, hk2 c]
      _ = h.cycleFactorsFinset.card := by simp
  have hlong : (∑ c, longComponentGoodRows (k c) (gc c)) =
      longCycleGoodRows η P h := by rfl
  have hgoodSumR : (∑ c, (gc c : ℝ)) =
      ((goodRows η P).card : ℝ) := by
    exact_mod_cast hgoodSum
  have hmR : (∑ c, (nontrivialComponentCount (k c) : ℝ)) =
      (h.cycleFactorsFinset.card : ℝ) := by
    exact_mod_cast hm
  have hlongR : (∑ c, (longComponentGoodRows (k c) (gc c) : ℝ)) =
      (longCycleGoodRows η P h : ℝ) := by
    exact_mod_cast hlong
  rw [hgoodSumR, hmR, hlongR] at hcomp
  have hbadCast : (∑ c, (bc c : ℝ)) ≤ ((badRows η P).card : ℝ) := by
    exact_mod_cast hbadSum
  linarith

/-- Full graph-indexed robust cycle-information inequality, paper Lemma 13. -/
theorem robust_cycle_information_twoMatchings
    {n : ℕ} {μ : Equiv.Perm (Fin n) → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hμ : IsProbabilityVector μ)
    (hmarg : HasAssignmentMarginals μ P)
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1 / 10)
    (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (P i) →
      j = f i ∨ j = g i)
    {D : ℝ} (hD : D = -shannonEntropy μ + ∑ i, rowScore (P i)) :
    Real.log 2 / 6 *
          (longCycleGoodRows η P (alternatingRowPerm f g) : ℕ) -
        (1 + Real.log 2 / 2) * (badRows η P).card -
        n * goodRowOmega η ≤ D := by
  have hscore := divergence_ge_good_bad_cycleScore
    hμ hmarg hP hη₀ hη₁ f g hheavy hD
  have haccount := alternating_component_accounting hP f g hheavy
  have hG : ((goodRows η P).card : ℝ) ≤ n := by
    have hGNat : (goodRows η P).card ≤ n := by
      simpa using Finset.card_le_univ (goodRows η P)
    exact_mod_cast hGNat
  exact robust_cycle_information_of_accounting
    (goodRowOmega_nonneg η) hG hscore haccount

/-- The exact graph-indexed form of paper (31): after discarding bad rows
and good rows in long components, the remaining rows occur in vertex-disjoint
clean two-row components. -/
theorem alternating_cleanCycle_count
    {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    {η : ℝ} (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (P i) →
      j = f i ∨ j = g i) :
    n ≤ 2 * (badRows η P).card +
      longCycleGoodRows η P (alternatingRowPerm f g) +
      2 * cleanCycleCount η P (alternatingRowPerm f g) := by
  let h := alternatingRowPerm f g
  let k : h.cycleFactorsFinset → ℕ :=
    fun c ↦ (c : Equiv.Perm (Fin n)).support.card
  let gc : h.cycleFactorsFinset → ℕ := cycleGoodCount η P h
  let bc : h.cycleFactorsFinset → ℕ := cycleBadCount η P h
  have hk2 : ∀ c, 2 ≤ k c := by
    intro c
    exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.property).1.two_le_card_support
  have hpoint : ∀ c, gc c ≤
      2 * cleanCycleIndicator η P h c + bc c +
        longComponentGoodRows (k c) (gc c) := by
    intro c
    have hpart : gc c + bc c = k c :=
      cycleGoodCount_add_cycleBadCount η P h c
    by_cases hk3 : 3 ≤ k c
    · simp [cleanCycleIndicator, longComponentGoodRows, hk3]
    · have hc2 := hk2 c
      have hkEq : k c = 2 := by omega
      by_cases hg2 : gc c = 2
      · have hclean :
            (c : Equiv.Perm (Fin n)).support.card = 2 ∧
              cycleGoodCount η P h c = 2 := by
          simpa [k, gc] using And.intro hkEq hg2
        rw [cleanCycleIndicator, ite_eq_left hclean]
        simp [longComponentGoodRows, hkEq]
        omega
      · have hgb : gc c ≤ bc c := by omega
        have hnotclean : ¬((c : Equiv.Perm (Fin n)).support.card = 2 ∧
              cycleGoodCount η P h c = 2) := by
          intro hclean
          exact hg2 (by simpa [gc] using hclean.2)
        rw [cleanCycleIndicator, ite_eq_right hnotclean]
        simp [longComponentGoodRows, hkEq]
        exact hgb
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun c _ ↦ hpoint c)
  have hsum' : (∑ c, gc c) ≤
      2 * cleanCycleCount η P h + (∑ c, bc c) +
        longCycleGoodRows η P h := by
    simpa [cleanCycleCount, longCycleGoodRows,
      Finset.sum_add_distrib, Finset.mul_sum] using hsum
  have hgoodSupport : goodRows η P ⊆ h.support := by
    intro i hi
    have hgood : IsGoodRow η (P i) := by simpa [goodRows] using hi
    exact goodRow_mem_alternating_support hP f g hheavy hgood
  have hgoodSum : (∑ c, gc c) = (goodRows η P).card := by
    simpa [gc, cycleGoodCount] using
      sum_cycleSupport_inter_card h (goodRows η P) hgoodSupport
  have hbadSum : (∑ c, bc c) ≤ (badRows η P).card := by
    simpa [bc, cycleBadCount] using
      sum_cycleSupport_inter_card_le h (badRows η P)
  have hrows := goodRows_card_add_badRows_card (η := η) P
  rw [hgoodSum] at hsum'
  have hfinal : n ≤ 2 * (badRows η P).card +
      longCycleGoodRows η P h + 2 * cleanCycleCount η P h := by
    omega
  simpa [h] using hfinal

/-- Paper Lemma 13 for the Gibbs law of a positive matrix, with the completed
heavy graph and its two perfect matchings constructed rather than assumed. -/
theorem exists_gibbs_robust_cycle_information
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 < A i j)
    {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1 / 10) :
    ∃ f g : Equiv.Perm (Fin n),
      (∀ i j, j ∈ heavyCoordinates η (assignmentMarginal A i) →
        j = f i ∨ j = g i) ∧
      Real.log 2 / 6 *
            (longCycleGoodRows η (assignmentMarginal A)
              (alternatingRowPerm f g) : ℕ) -
          (1 + Real.log 2 / 2) *
            (badRows η (assignmentMarginal A)).card -
          n * goodRowOmega η ≤ gibbsSequentialDivergence A := by
  have hper := permanent_pos_of_positive A hA
  have hDS : IsDoublyStochastic (assignmentMarginal A) :=
    assignmentMarginal_doublyStochastic A
      (fun i j ↦ (hA i j).le) hper.ne'
  obtain ⟨f, g, hheavy⟩ :=
    exists_heavyCompletion_twoMatchings hDS hη₁
  refine ⟨f, g, hheavy, ?_⟩
  exact robust_cycle_information_twoMatchings
    (gibbsProbability_isProbabilityVector A hA)
    (gibbs_hasAssignmentMarginals A)
    (assignmentMarginal_strictProbabilityVector A hA)
    hη₀ hη₁ f g hheavy
    (gibbsSequentialDivergence_eq_entropy A hA)

end BeyondBethe
