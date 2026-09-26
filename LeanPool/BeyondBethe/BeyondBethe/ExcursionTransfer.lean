/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.TransferIdentity
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Tactic

/-! # Excursion Transfer -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-- Mass of a vector on a designated set of outside coordinates. -/
noncomputable def massOn
    {ι : Type*} (s : Finset ι) (p : ι → ℝ) : ℝ :=
  ∑ i ∈ s, p i

/-- The conditional-entropy term `rho H(p/rho)` written without division,
with its continuous value at `rho = 0`. -/
noncomputable def scaledConditionalEntropyOn
    {ι : Type*} (s : Finset ι) (p : ι → ℝ) : ℝ :=
  (∑ i ∈ s, Real.negMulLog (p i)) +
    massOn s p * Real.log (massOn s p)

/-- Transfer cost accumulated on a designated coordinate set. -/
noncomputable def transferCostOn
    {ι : Type*} (s : Finset ι) (p u : ι → ℝ) : ℝ :=
  ∑ i ∈ s, p i * Real.log (1 / u i)

theorem massOn_pos_of_nonempty
    {ι : Type*} {s : Finset ι} {p : ι → ℝ}
    (hs : s.Nonempty) (hp : ∀ i, 0 < p i) :
    0 < massOn s p := by
  rw [massOn]
  exact Finset.sum_pos (fun i _ ↦ hp i) hs

/-- Exact entropy/KL decomposition behind paper (40). -/
theorem transferCostOn_eq_entropy_add_KL
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (hs : s.Nonempty)
    {p u : ι → ℝ} (hp : ∀ i, 0 < p i) (hu : ∀ i, 0 < u i) :
    let ρ := massOn s p
    let W := massOn s u
    let pO : s → ℝ := fun i ↦ p i / ρ
    let uO : s → ℝ := fun i ↦ u i / W
    transferCostOn s p u =
      scaledConditionalEntropyOn s p + ρ * finiteKL pO uO - ρ * Real.log W := by
  dsimp only
  have hρ : 0 < massOn s p := massOn_pos_of_nonempty hs hp
  have hW : 0 < massOn s u := massOn_pos_of_nonempty hs hu
  rw [transferCostOn, scaledConditionalEntropyOn, finiteKL,
    Finset.mul_sum]
  have hsub :
      (∑ i : s, massOn s p *
        ((p i / massOn s p) *
          Real.log ((p i / massOn s p) / (u i / massOn s u)))) =
      ∑ i ∈ s, massOn s p *
        ((p i / massOn s p) *
          Real.log ((p i / massOn s p) / (u i / massOn s u))) :=
    by
      simpa using Finset.sum_coe_sort s (fun i ↦ massOn s p *
        ((p i / massOn s p) *
          Real.log ((p i / massOn s p) / (u i / massOn s u))))
  rw [hsub]
  have hρlog : massOn s p * Real.log (massOn s p) =
      ∑ i ∈ s, p i * Real.log (massOn s p) := by
    rw [massOn, Finset.sum_mul]
  have hWlog : massOn s p * Real.log (massOn s u) =
      ∑ i ∈ s, p i * Real.log (massOn s u) := by
    rw [massOn, Finset.sum_mul]
  rw [hρlog, hWlog, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hpρ : p i / massOn s p ≠ 0 := (div_pos (hp i) hρ).ne'
  have huW : u i / massOn s u ≠ 0 := (div_pos (hu i) hW).ne'
  rw [Real.negMulLog_def,
    Real.log_div one_ne_zero (hu i).ne', Real.log_one,
    Real.log_div hpρ huW,
    Real.log_div (hp i).ne' hρ.ne',
    Real.log_div (hu i).ne' hW.ne']
  field_simp [hρ.ne', hW.ne', (hp i).ne', (hu i).ne']
  ring

theorem normalizedOutside_isProbabilityVector
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (hs : s.Nonempty)
    {p : ι → ℝ} (hp : ∀ i, 0 < p i) :
    IsProbabilityVector (fun i : s ↦ p i / massOn s p) := by
  have hρ : 0 < massOn s p := massOn_pos_of_nonempty hs hp
  constructor
  · intro i
    exact div_nonneg (hp i).le hρ.le
  · calc
      (∑ i : s, p i / massOn s p) =
          ∑ i ∈ s, p i / massOn s p := by
            simpa using Finset.sum_coe_sort s
              (fun i ↦ p i / massOn s p)
      _ = 1 := by
        rw [← Finset.sum_div]
        exact div_self (by simpa only [massOn] using hρ.ne')

/-- Paper tail-transfer inequality (41), before substituting the entropy of
the coarsened row.  The theorem includes the empty-set/zero-mass case. -/
theorem scaledConditionalEntropyOn_sub_mass_le_transferCostOn
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {p u : ι → ℝ}
    (hp : ∀ i, 0 < p i) (hu : ∀ i, 0 < u i)
    (hUsum : massOn s u ≤ Real.exp 1) :
    scaledConditionalEntropyOn s p - massOn s p ≤
      transferCostOn s p u := by
  by_cases hs : s.Nonempty
  · have hρ : 0 < massOn s p := massOn_pos_of_nonempty hs hp
    have hW : 0 < massOn s u := massOn_pos_of_nonempty hs hu
    let pO : s → ℝ := fun i ↦ p i / massOn s p
    let uO : s → ℝ := fun i ↦ u i / massOn s u
    have hpO : IsProbabilityVector pO :=
      normalizedOutside_isProbabilityVector hs hp
    have huO : IsProbabilityVector uO :=
      normalizedOutside_isProbabilityVector hs hu
    have hpOpos : ∀ i, 0 < pO i := fun i ↦ div_pos (hp i) hρ
    have huOpos : ∀ i, 0 < uO i := fun i ↦ div_pos (hu i) hW
    have hKL : 0 ≤ finiteKL pO uO :=
      finiteKL_nonneg hpO huO hpOpos huOpos
    have hlogW : Real.log (massOn s u) ≤ 1 := by
      have hlog := Real.log_le_log hW hUsum
      simpa using hlog
    rw [transferCostOn_eq_entropy_add_KL hs hp hu]
    dsimp only [pO, uO] at hKL
    nlinarith [mul_nonneg hρ.le hKL,
      mul_le_mul_of_nonneg_left hlogW hρ.le]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp [scaledConditionalEntropyOn, massOn, transferCostOn]

/-- Entropy of the coarsening which merges the complement of a core set into
one atom, expressed as binary entropy plus conditional outside entropy. -/
noncomputable def coarsenedRowEntropy
    {ι : Type*} (outside : Finset ι) (p : ι → ℝ) : ℝ :=
  binaryEntropy (massOn outside p) + scaledConditionalEntropyOn outside p

theorem coarsenedRowEntropy_sub_binary_sub_mass_le_transferCostOn
    {ι : Type*} [DecidableEq ι]
    (outside : Finset ι) {p u : ι → ℝ}
    (hp : ∀ i, 0 < p i) (hu : ∀ i, 0 < u i)
    (hUsum : massOn outside u ≤ Real.exp 1) :
    coarsenedRowEntropy outside p - binaryEntropy (massOn outside p) -
        massOn outside p ≤ transferCostOn outside p u := by
  rw [coarsenedRowEntropy]
  convert scaledConditionalEntropyOn_sub_mass_le_transferCostOn outside hp hu hUsum using 1 <;>
    ring

theorem binaryEntropy_eq_binEntropy (ρ : ℝ) :
    binaryEntropy ρ = Real.binEntropy ρ := by
  rw [binaryEntropy, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

/-- The total rowwise transfer cost over all matrix coordinates. -/
noncomputable def matrixTransferCost
    {ι : Type*} [Fintype ι]
    (P U : Matrix ι ι ℝ) : ℝ :=
  ∑ i, transferCostOn Finset.univ (P i) (U i)

/-- The total transfer cost over the designated outside coordinates in each row. -/
noncomputable def outsideTransferCost
    {ι : Type*} [Fintype ι]
    (outside : ι → Finset ι) (P U : Matrix ι ι ℝ) : ℝ :=
  ∑ i, transferCostOn (outside i) (P i) (U i)

/-- The total transfer cost over the complements of the designated outside coordinates. -/
noncomputable def coreTransferCost
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (outside : ι → Finset ι) (P U : Matrix ι ι ℝ) : ℝ :=
  ∑ i, transferCostOn (Finset.univ \ outside i) (P i) (U i)

/-- Equation (39) from the global transfer upper bound and the cycle-encoding
entropy estimate.  This is the exact bridge between paper Lemmas 13, 16, and
17. -/
theorem transfer_before_tail_of_global_and_encoding
    {n : ℕ} {P U : Matrix (Fin n) (Fin n) ℝ}
    (outside : Fin n → Finset (Fin n))
    {slack ξ gibbsEntropy : ℝ}
    (hglobal : matrixTransferCost P U ≤
      slack + 2 * ξ * n + gibbsEntropy - n * (Real.log 2 / 2))
    (hencoding : gibbsEntropy ≤
      n * (Real.log 2 / 2) +
        ∑ i, coarsenedRowEntropy (outside i) (P i)) :
    matrixTransferCost P U ≤
      slack + 2 * ξ * n +
        ∑ i, coarsenedRowEntropy (outside i) (P i) := by
  linarith

theorem matrixTransferCost_eq_core_add_outside
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (outside : ι → Finset ι) (P U : Matrix ι ι ℝ) :
    matrixTransferCost P U =
      coreTransferCost outside P U + outsideTransferCost outside P U := by
  rw [matrixTransferCost, coreTransferCost, outsideTransferCost,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [transferCostOn, transferCostOn, transferCostOn]
  exact (Finset.sum_sdiff (Finset.subset_univ (outside i))).symm

theorem massOn_le_sum_univ
    {ι : Type*} [Fintype ι]
    (s : Finset ι) {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) :
    massOn s u ≤ ∑ i, u i := by
  rw [massOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ ↦ hu i)

/-- Paper Lemma 17, first inequality, in its graph-independent form.  The
encoding supplies `coarsenedRowEntropy`; this theorem performs the complete
excursion-entropy cancellation. -/
theorem coreTransferCost_le_of_entropy_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (outside : ι → Finset ι) {P U : Matrix ι ι ℝ} {B : ℝ}
    (hPpos : ∀ i j, 0 < P i j) (hUpos : ∀ i j, 0 < U i j)
    (hUrow : ∀ i, ∑ j, U i j ≤ Real.exp 1)
    (hbefore : matrixTransferCost P U ≤
      B + ∑ i, coarsenedRowEntropy (outside i) (P i)) :
    coreTransferCost outside P U ≤
      B + ∑ i, (binaryEntropy (massOn (outside i) (P i)) +
        massOn (outside i) (P i)) := by
  have htailRow : ∀ i,
      coarsenedRowEntropy (outside i) (P i) -
          (binaryEntropy (massOn (outside i) (P i)) +
            massOn (outside i) (P i)) ≤
        transferCostOn (outside i) (P i) (U i) := by
    intro i
    have hUsum : massOn (outside i) (U i) ≤ Real.exp 1 :=
      (massOn_le_sum_univ (outside i) (fun j ↦ (hUpos i j).le)).trans
        (hUrow i)
    have htail := coarsenedRowEntropy_sub_binary_sub_mass_le_transferCostOn
      (outside i) (hPpos i) (hUpos i) hUsum
    linarith
  have htailSum :
      (∑ i, (coarsenedRowEntropy (outside i) (P i) -
        (binaryEntropy (massOn (outside i) (P i)) +
          massOn (outside i) (P i)))) ≤
      outsideTransferCost outside P U := by
    rw [outsideTransferCost]
    exact Finset.sum_le_sum (fun i _ ↦ htailRow i)
  have hpartition := matrixTransferCost_eq_core_add_outside outside P U
  simp only [Finset.sum_sub_distrib] at htailSum
  linarith

/-- The graph-independent cancellation specialized to the transfer matrix
`U` from paper (37).  Thus the only remaining input from the cycle encoding
is the entropy bound `hbefore`. -/
theorem coreTransferCost_le_for_transferU
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (outside : ι → Finset ι) {P X : Matrix ι ι ℝ} {τ B : ℝ}
    (hτ : 0 ≤ τ) (hPpos : ∀ i j, 0 < P i j)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hbefore : matrixTransferCost P (fun i j ↦ transferU τ (X i) j) ≤
      B + ∑ i, coarsenedRowEntropy (outside i) (P i)) :
    coreTransferCost outside P (fun i j ↦ transferU τ (X i) j) ≤
      B + ∑ i, (binaryEntropy (massOn (outside i) (P i)) +
        massOn (outside i) (P i)) := by
  apply coreTransferCost_le_of_entropy_bound outside hPpos
    (fun i j ↦ transferU_pos (hXint i) j)
    (fun i ↦ sum_transferU_le_exp_one hτ (hXint i)) hbefore

theorem binaryEntropy_nonneg_of_mem_Icc
    {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ binaryEntropy ρ := by
  rw [binaryEntropy_eq_binEntropy]
  exact Real.binEntropy_nonneg hρ.1 hρ.2

theorem binaryEntropy_mono_to_half
    {ρ η : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) (2 : ℝ)⁻¹)
    (hη : η ∈ Set.Icc (0 : ℝ) (2 : ℝ)⁻¹) (hρη : ρ ≤ η) :
    binaryEntropy ρ ≤ binaryEntropy η := by
  rw [binaryEntropy_eq_binEntropy, binaryEntropy_eq_binEntropy]
  exact Real.binEntropy_strictMonoOn.monotoneOn hρ hη hρη

/-- The good-row/bad-row aggregation in the second conclusion of paper
Lemma 17.  We deliberately retain the paper's slightly loose bad-row term:
every row receives the good-row allowance, and each bad row receives an
additional `1 + log 2`. -/
theorem sum_binaryEntropy_add_mass_le_good_bad
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (good : Finset ι) (ρ : ι → ℝ) {η : ℝ}
    (hη : η ∈ Set.Icc (0 : ℝ) (2 : ℝ)⁻¹)
    (hρ : ∀ i, ρ i ∈ Set.Icc (0 : ℝ) 1)
    (hgood : ∀ i ∈ good, ρ i ≤ η) :
    ∑ i, (binaryEntropy (ρ i) + ρ i) ≤
      (Fintype.card ι : ℝ) * (binaryEntropy η + η) +
        (1 + Real.log 2) * (Finset.card (Finset.univ \ good) : ℝ) := by
  have hηone : η ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact hη.1
    · exact hη.2.trans (by norm_num)
  have hbase : 0 ≤ binaryEntropy η + η :=
    add_nonneg (binaryEntropy_nonneg_of_mem_Icc hηone) hη.1
  have hgoodSum :
      (∑ i ∈ good, (binaryEntropy (ρ i) + ρ i)) ≤
        (Finset.card good : ℝ) * (binaryEntropy η + η) := by
    calc
      (∑ i ∈ good, (binaryEntropy (ρ i) + ρ i)) ≤
          ∑ _i ∈ good, (binaryEntropy η + η) := by
        apply Finset.sum_le_sum
        intro i hi
        have hρhalf : ρ i ∈ Set.Icc (0 : ℝ) (2 : ℝ)⁻¹ :=
          ⟨(hρ i).1, (hgood i hi).trans hη.2⟩
        exact add_le_add
          (binaryEntropy_mono_to_half hρhalf hη (hgood i hi))
          (hgood i hi)
      _ = (Finset.card good : ℝ) * (binaryEntropy η + η) := by
        simp
        ring
  have hbadSum :
      (∑ i ∈ (Finset.univ \ good),
        (binaryEntropy (ρ i) + ρ i)) ≤
        (Finset.card (Finset.univ \ good) : ℝ) *
          (Real.log 2 + 1) := by
    calc
      (∑ i ∈ (Finset.univ \ good),
          (binaryEntropy (ρ i) + ρ i)) ≤
          ∑ _i ∈ (Finset.univ \ good), (Real.log 2 + 1) := by
        apply Finset.sum_le_sum
        intro i _
        rw [binaryEntropy_eq_binEntropy]
        exact add_le_add Real.binEntropy_le_log_two (hρ i).2
      _ = (Finset.card (Finset.univ \ good) : ℝ) *
          (Real.log 2 + 1) := by
        simp
        ring
  have hgoodCard : (Finset.card good : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Finset.card_le_card (Finset.subset_univ good)
  have hgoodBound :
      (Finset.card good : ℝ) * (binaryEntropy η + η) ≤
        (Fintype.card ι : ℝ) * (binaryEntropy η + η) :=
    mul_le_mul_of_nonneg_right hgoodCard hbase
  rw [← Finset.sum_sdiff (Finset.subset_univ good)]
  linarith

/-- Both conclusions of paper Lemma 17, specialized to the paper's transfer
matrix and normalized by the number of rows.  The cycle encoding appears only
through `hbefore`, and the good-row geometry only through `hgood`. -/
theorem coreTransferCost_normalized_le_for_transferU
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (outside : ι → Finset ι) (good : Finset ι)
    {P X : Matrix ι ι ℝ} {τ B η : ℝ}
    (hτ : 0 ≤ τ) (hPpos : ∀ i j, 0 < P i j)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hbefore : matrixTransferCost P (fun i j ↦ transferU τ (X i) j) ≤
      B + ∑ i, coarsenedRowEntropy (outside i) (P i))
    (hη : η ∈ Set.Icc (0 : ℝ) (2 : ℝ)⁻¹)
    (hρ : ∀ i, massOn (outside i) (P i) ∈ Set.Icc (0 : ℝ) 1)
    (hgood : ∀ i ∈ good, massOn (outside i) (P i) ≤ η) :
    coreTransferCost outside P (fun i j ↦ transferU τ (X i) j) /
        (Fintype.card ι : ℝ) ≤
      B / (Fintype.card ι : ℝ) + binaryEntropy η + η +
        (1 + Real.log 2) * (Finset.card (Finset.univ \ good) : ℝ) /
          (Fintype.card ι : ℝ) := by
  have hcore := coreTransferCost_le_for_transferU outside hτ hPpos hXint hbefore
  have hsum := sum_binaryEntropy_add_mass_le_good_bad good
    (fun i ↦ massOn (outside i) (P i)) hη hρ hgood
  have hn : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hn).2
  calc
    coreTransferCost outside P (fun i j ↦ transferU τ (X i) j) ≤
        B + (Fintype.card ι : ℝ) * (binaryEntropy η + η) +
          (1 + Real.log 2) * (Finset.card (Finset.univ \ good) : ℝ) := by
      linarith
    _ = (B / (Fintype.card ι : ℝ) + binaryEntropy η + η +
          (1 + Real.log 2) * (Finset.card (Finset.univ \ good) : ℝ) /
            (Fintype.card ι : ℝ)) * (Fintype.card ι : ℝ) := by
      field_simp [hn.ne']
      ring

end BeyondBethe
