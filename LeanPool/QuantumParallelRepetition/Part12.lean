/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.QuantumParallelRepetition.Part11

/-! # Quantum parallel repetition, part 12 -/

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

private structure UnconditionalActualFairSourceSamplerData
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (gamma : ℝ) where
  base : ExactHistoryFlag X Y A B D
  denominator : ℕ
  denominator_positive : 0 < denominator
  numerator : ExactLocalSamplerIndex X Y D →
    ExactHistoryFlag X Y A B D → ℕ
  rational_normalized :
    ∀ index, (∑ history, numerator index history) = denominator
  support_preserving :
    ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history
  nonempty : ∀ index,
    (rationalMarked denominator (numerator index)).Nonempty
  total_variation :
    QuantumParallelRepetition.Pinsker.finiteTotalVariation
        (flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator))
        (exactSourceAliceFlagCoupling
          G n S D denominator numerator nonempty) ≤
      exactSourcePinskerRate G n S D + gamma
  mismatch :
    (∑ outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator) outcome *
        if exactSourcePermutationMatched
          D denominator numerator nonempty outcome
        then 0 else 1) ≤
      4 * (exactSourcePinskerRate G n S D + gamma)

theorem unconditionalActualFairSourceSamplerData_of_positive
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (gamma : ℝ) (gamma_positive : 0 < gamma) :
    Nonempty (UnconditionalActualFairSourceSamplerData
      G n S D gamma) := by
  obtain ⟨base, denominator, denominator_positive, numerator,
      rational_normalized, support_preserving, nonempty,
      total_variation, mismatch⟩ :=
    unconditionalSourcePhysicalRounding_exists_sourceSampler
      G n S D remaining positive gamma gamma_positive
  exact ⟨⟨base, denominator, denominator_positive, numerator,
    rational_normalized, support_preserving, nonempty,
    total_variation, mismatch⟩⟩

private structure UnconditionalActualFairSourceStoppingHazardData
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (alpha : ℝ) where
  w : ℝ
  N : ℕ
  L : ℕ
  P : ℕ
  Q : ℕ
  m : ℕ
  width_large : 1 ≤ w
  grid : 0 < N
  phases : 0 < P
  harmonic : 0 < m
  fine :
    (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) : ℝ) /
        (N : ℝ) < 1 / (w + 1)
  scalar :
    1 / w +
      (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) : ℝ) *
        w / (N : ℝ) ≤ 3 * alpha ^ (1 / 3 : ℝ) / 2
  UA : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ
  UB : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ
  asynchronous :
    (∑ h : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D h *
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N (fun _ : Fin 1 => w) (fun _ : Fin L => 0)
          (exactGlobalHistoryFinGamma
            G n S D h.2.2.2 h.2.1)
          (exactGlobalHistoryFinPhi
            G n S D h.2.2.2 h.2.2.1)) ≤
      64 * Real.sqrt (martingaleRate G n S D) +
        alpha ^ (1 / 3 : ℝ)
  terminal :
    (∑ h : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D h *
        dSVDensityRationalHeterogeneousPhysicalTerminalMass
          N (fun _ : Fin 1 => w) (fun _ : Fin L => 0)
          (exactGlobalHistoryFinGamma
            G n S D h.2.2.2 h.2.1)
          (exactGlobalHistoryFinPhi
            G n S D h.2.2.2 h.2.2.1)) ≤
      (alpha ^ (1 / 3 : ℝ)) ^ 2
  hazard :
    (∑ h : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D h *
        dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
          Q m (fun _ : Fin 1 => w) (fun _ : Fin L => 0)
          (exactGlobalHistoryFinGamma
            G n S D h.2.2.2 h.2.1)
          (exactGlobalHistoryFinPhi
            G n S D h.2.2.2 h.2.2.1)
          UA UB) ≤
      (34 / Real.sqrt
          (64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ))) *
          (64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ)) +
        4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt (martingaleRate G n S D) +
                alpha ^ (1 / 3 : ℝ))

theorem unconditionalActualFairSourceStoppingHazardData_of_positive
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha : ℝ) (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (small : 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ) ≤ 1) :
    Nonempty (UnconditionalActualFairSourceStoppingHazardData
      G n S D alpha) := by
  obtain ⟨w, N, L, P, Q, m, width_large, grid, horizon, phases,
      resolution, harmonic, precision, fine, scalar,
      UA, UB, canonical, asynchronous, terminal, hazard⟩ :=
    unconditionalSourcePhysicalRounding_exists_fairStoppingHazard
      G n S D remaining positive alpha alpha_positive alpha_bounded small
  refine ⟨{
    w := w
    N := N
    L := L
    P := P
    Q := Q
    m := m
    width_large := width_large
    grid := grid
    phases := phases
    harmonic := harmonic
    fine := fine
    scalar := scalar
    UA := UA
    UB := UB
    asynchronous := ?_
    terminal := ?_
    hazard := ?_
  }⟩
  · simpa only using asynchronous
  · simpa only using terminal
  · simpa only using hazard

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

private structure UnconditionalActualFairCachedStoppedAnalyticLedger
    {I K : Type} [Fintype I] [Fintype K]
    {H : I × K → Type}
    [∀ p, NormedAddCommGroup (H p)]
    [∀ p, InnerProductSpace ℂ (H p)]
    (law : I → ℝ)
    (actual canonical source : (p : I × K) → H p)
    (deviation clipping bad : ℝ) : Prop where
  actual_mass :
    (∑ h : I, law h * ∑ j : K, ‖actual (h, j)‖ ^ 2) ≤ 1
  canonical_mass :
    (∑ h : I, law h * ∑ j : K, ‖canonical (h, j)‖ ^ 2) ≤ 1
  canonical_row_mass : ∀ h : I,
    (∑ j : K, ‖canonical (h, j)‖ ^ 2) ≤ 1
  same_work_mass : ∀ (h : I) (j : K),
    ‖source (h, j)‖ = ‖canonical (h, j)‖
  clean_deviation :
    (∑ h : I, law h *
      ∑ j : K, ‖actual (h, j) - canonical (h, j)‖ ^ 2) ≤ deviation
  clip_deviation :
    (∑ h : I, law h *
      ∑ j : K, ‖canonical (h, j) - source (h, j)‖ ^ 2) ≤ clipping
  actual_success :
    1 - bad ≤ ∑ h : I, law h * ∑ j : K, ‖actual (h, j)‖ ^ 2

private structure UnconditionalActualFairCachedSourceVerifierLedger
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    {K : Type} [Fintype K]
    {H : ExactLocallySampleableTuple X Y A B D × K → Type}
    [∀ p, NormedAddCommGroup (H p)]
    [∀ p, InnerProductSpace ℂ (H p)]
    (effect : (p : ExactLocallySampleableTuple X Y A B D × K) →
      (H p →L[ℂ] H p))
    (actual source :
      (p : ExactLocallySampleableTuple X Y A B D × K) → H p) :
    Prop where
  contraction : ∀ p, ‖effect p‖ ≤ 1
  supported_born :
    ∀ h : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D h ≠ 0 →
        ∀ j : K,
          quadraticExpectation (effect (h, j)) (source (h, j)) =
            ‖source (h, j)‖ ^ 2 *
              exactSourceConditionalWinningProbability G n S D h
  history_born_nonnegative :
    ∀ h : ExactLocallySampleableTuple X Y A B D,
      0 ≤ ∑ j : K,
        quadraticExpectation (effect (h, j)) (actual (h, j))
  history_born_bounded :
    ∀ h : ExactLocallySampleableTuple X Y A B D,
      (∑ j : K,
        quadraticExpectation (effect (h, j)) (actual (h, j))) ≤ 1

theorem unconditionalActualFairCachedLedgerStoppingTransfer
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (rational_normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (support_preserving : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    {L : ℕ} {ι : Fin (L + 1) → Type}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (PA : ExactSourceSharedFlag X Y A B D denominator →
      (r : Fin (L + 1)) → X → POVM A (ι r))
    (PB : ExactSourceSharedFlag X Y A B D denominator →
      (r : Fin (L + 1)) → Y → POVM B (ι r))
    (U : ExactSourceSharedFlag X Y A B D denominator →
      X → Matrix.unitaryGroup (Σ r : Fin (L + 1), ι r) ℂ)
    (V : ExactSourceSharedFlag X Y A B D denominator →
      Y → Matrix.unitaryGroup (Σ r : Fin (L + 1), ι r) ℂ)
    (z : ExactSourceSharedFlag X Y A B D denominator →
      EuclideanSpace ℂ
        ((Σ r : Fin (L + 1), ι r) ×
          (Σ r : Fin (L + 1), ι r)))
    (z_normalized : ∀ flag, ‖z flag‖ = 1)
    (matched :
      ExactSourceSharedFlag X Y A B D denominator ×
        (X × Y) → Bool)
    {K : Type} [Fintype K]
    {H : ExactLocallySampleableTuple X Y A B D × K → Type}
    [∀ p, NormedAddCommGroup (H p)]
    [∀ p, InnerProductSpace ℂ (H p)]
    (effect : (p : ExactLocallySampleableTuple X Y A B D × K) →
      (H p →L[ℂ] H p))
    (actual canonical source :
      (p : ExactLocallySampleableTuple X Y A B D × K) → H p)
    (epsilon lam deviation clipping bad : ℝ)
    (analytic :
      UnconditionalActualFairCachedStoppedAnalyticLedger
        (exactLocallySampleableLaw G n S D)
        actual canonical source deviation clipping bad)
    (verifier :
      UnconditionalActualFairCachedSourceVerifierLedger
        G n S D effect actual source)
    (source_failure :
      uniformRemainingFailure
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D < epsilon / 2)
    (total_variation :
      QuantumParallelRepetition.Pinsker.finiteTotalVariation
        (flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator))
        (exactSourceAliceFlagCoupling
          G n S D denominator numerator nonempty) ≤ lam)
    (mismatch :
      (∑ outcome :
        ExactSourceSharedFlag X Y A B D denominator × (X × Y),
        flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator) outcome *
          if matched outcome then 0 else 1) ≤ 4 * lam)
    (matched_physical_branch :
      ∀ (flag : ExactSourceSharedFlag X Y A B D denominator)
        (x : X) (y : Y),
        matched (flag, (x, y)) = true →
          (∑ k : K,
            quadraticExpectation
              (effect
                (exactSourceAliceSampleTuple
                  D denominator numerator nonempty (flag, (x, y)), k))
              (actual
                (exactSourceAliceSampleTuple
                  D denominator numerator nonempty (flag, (x, y)), k))) ≤
            ∑ j : Fin L,
              quadraticExpectation
                (Matrix.toEuclideanCLM
                  (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
                  (actualStoppingBranchWinningEffect
                    G (PA flag) (PB flag) j.succ j.succ x y))
                (actualStoppingBranchVector
                  (actualStoppingQuestionLocalAction
                    (U flag x) (V flag y) (z flag))
                  j.succ j.succ)) :
    1 - epsilon / 2 - 5 * lam -
        (bad + 4 * Real.sqrt deviation + 2 * Real.sqrt clipping) ≤
      (pureFlaggedStrategy G
        (exactSourceSharedFlagWeight D denominator)
        (exactSourceSharedFlagWeight_nonneg D denominator)
        (exactSourceSharedFlagWeight_sum D remaining denominator)
        z z_normalized
        (fun flag x => unitaryConjugatePOVM
          (U flag x)
          (dependentBlockPOVM
            (fun r => PA flag r x)))
        (fun flag y => unitaryConjugatePOVM
          (V flag y)
          (dependentBlockPOVM
            (fun r => PB flag r y)))).winProbability := by
  exact unconditionalFairPhysicalFlaggedStoppingTransfer
    G n S D remaining positive base denominator denominator_positive
    numerator rational_normalized support_preserving nonempty
    PA PB U V z z_normalized matched
    effect verifier.contraction actual canonical source
    analytic.actual_mass analytic.canonical_mass analytic.canonical_row_mass
    analytic.same_work_mass verifier.supported_born
    epsilon lam deviation clipping bad
    analytic.clean_deviation analytic.clip_deviation analytic.actual_success
    verifier.history_born_nonnegative verifier.history_born_bounded
    source_failure total_variation mismatch matched_physical_branch

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

private structure UnconditionalActualFairSourceRoundingContext
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (alpha gamma : ℝ) where
  remaining : 0 < (Finset.univ \ D).card
  positive : 0 < repeatedPostselectionMass G n S D
  failure :
    uniformRemainingFailure
      (strategyEventLaw (G.repeat n) S)
      (repeatedCoordinateWin G n) D <
        (1 - entangledValue G) / 2
  sampler :
    UnconditionalActualFairSourceSamplerData G n S D gamma
  stopping :
    UnconditionalActualFairSourceStoppingHazardData G n S D alpha

/-- Builds the fair-source rounding context from positive sampling parameters. -/
def unconditionalActualFairSourceRoundingContextOfPositive
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha gamma : ℝ)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (gamma_positive : 0 < gamma)
    (small :
      64 * Real.sqrt (martingaleRate G n S D) +
        alpha ^ (1 / 3 : ℝ) ≤ 1)
    (failure :
      uniformRemainingFailure
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D <
          (1 - entangledValue G) / 2) :
    UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma := by
  classical
  exact {
    remaining := remaining
    positive := positive
    failure := failure
    sampler := Classical.choice
      (unconditionalActualFairSourceSamplerData_of_positive
        G n S D remaining positive gamma gamma_positive)
    stopping := Classical.choice
      (unconditionalActualFairSourceStoppingHazardData_of_positive
        G n S D remaining positive alpha alpha_positive alpha_bounded small)
  }

namespace UnconditionalActualFairSourceRoundingContext

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
variable {D : Finset (Fin n)} {alpha gamma : ℝ}

private def d (_c : UnconditionalActualFairSourceRoundingContext
    G n S D alpha gamma) : ℕ :=
  Fintype.card (ExactGlobalHistoryLocalIndex G n S D)

theorem dimension_pos
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : 0 < d c :=
  exactGlobalHistoryLocalIndex_card_pos G n S D

private def width
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : Fin 1 → ℝ :=
  fun _ => c.stopping.w

private def schedule
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : Fin c.stopping.L → Fin 1 :=
  fun _ => 0

theorem width_positive
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : 0 < c.stopping.w := by
  linarith [c.stopping.width_large]

theorem width_all
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : ∀ s : Fin 1, 0 < width c s := by
  intro s
  exact width_positive c

theorem fine_all
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    ∀ s : Fin 1,
      (d c : ℝ) / (c.stopping.N : ℝ) < 1 / (width c s + 1) := by
  intro s
  exact c.stopping.fine

private abbrev sourceIndex
    (_c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : Type :=
  ExactLocallySampleableTuple X Y A B D

private def law
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : sourceIndex c → ℝ :=
  exactLocallySampleableLaw G n S D

private def gammaVector
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    sourceIndex c → BipartiteUnitVector (d c) :=
  fun h => unconditionalExactFairGammaUnit G n S D h

private def phiVector
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    sourceIndex c → BipartiteUnitVector (d c) :=
  fun h => exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1

private def psiVector
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    sourceIndex c → EuclideanSpace ℂ (Fin (d c) × Fin (d c)) :=
  fun h => exactSourceTuplePsi G n S D h

private abbrev branchSpace
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (p : sourceIndex c × Fin c.stopping.L) : Type :=
  IntegratorActualC485BranchSpace
    1 c.stopping.P c.stopping.N (d c)
    c.stopping.L c.stopping.m p.2

private def actual
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (p : sourceIndex c × Fin c.stopping.L) : branchSpace c p :=
  integratorActualC485CleanedVector
    (S := 1) (B := c.stopping.P) (N := c.stopping.N)
    (d := d c) (L := c.stopping.L) (m := c.stopping.m)
    c.stopping.Q (width c) (schedule c)
    (gammaVector c p.1) (phiVector c p.1)
    c.stopping.UA c.stopping.UB p.2

private def canonical
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (p : sourceIndex c × Fin c.stopping.L) : branchSpace c p :=
  integratorActualC485CanonicalVector
    (S := 1) (B := c.stopping.P) (N := c.stopping.N)
    (d := d c) (L := c.stopping.L) (m := c.stopping.m)
    (width := width c) (schedule c)
    (gammaVector c p.1) (phiVector c p.1) p.2
    (width_all c (schedule c p.2)) c.stopping.grid
    (fine_all c (schedule c p.2))

private def source
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (p : sourceIndex c × Fin c.stopping.L) : branchSpace c p :=
  integratorActualC485SourceVector
    (S := 1) (B := c.stopping.P) (N := c.stopping.N)
    (d := d c) (L := c.stopping.L) (m := c.stopping.m)
    (width c) (schedule c)
    (gammaVector c p.1) (phiVector c p.1) (psiVector c p.1) p.2

theorem answerNonempty
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : Nonempty A ∧ Nonempty B :=
  exactSourceAnswerTypes_nonempty_of_remaining
    G n S D c.remaining

private def aliceDefault
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : A :=
  Classical.choice (answerNonempty c).1

private def bobDefault
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : B :=
  Classical.choice (answerNonempty c).2

private def effect
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (p : sourceIndex c × Fin c.stopping.L) :
    branchSpace c p →L[ℂ] branchSpace c p :=
  integratorActualC485WinningEffect
    (P := c.stopping.P) (N := c.stopping.N) (m := c.stopping.m)
    G n S D (aliceDefault c) (bobDefault c)
    p.2 p.1.2.1 p.1.2.2.1

private def deviation
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : ℝ :=
  ∑ h : sourceIndex c, law c h *
    ∑ j : Fin c.stopping.L,
      ‖actual c (h, j) - canonical c (h, j)‖ ^ 2

private def clipping
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : ℝ :=
  unconditionalActualC485FairSourceClipEnergy
    (P := c.stopping.P) (m := c.stopping.m)
    G n S D (width_positive c) c.stopping.grid c.stopping.fine
    (schedule c)

private def bad
    (_c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : ℝ :=
  64 * Real.sqrt (martingaleRate G n S D) +
    alpha ^ (1 / 3 : ℝ) + (alpha ^ (1 / 3 : ℝ)) ^ 2

private abbrev flag
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : Type :=
  ExactSourceSharedFlag X Y A B D c.sampler.denominator

private abbrev fiber
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : Type :=
  UnconditionalSourcePhysicalStoppingPhaseFiber
    1 c.stopping.P c.stopping.N (d c)
    c.stopping.L c.stopping.m

private def PA
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    flag c → Fin (c.stopping.L + 1) → X → POVM A (fiber c) := by
  classical
  exact unconditionalActualFairSourceAliceFlagPOVM
    G n S D c.sampler.denominator c.sampler.numerator
    c.sampler.nonempty (aliceDefault c)
    c.stopping.P c.stopping.N c.stopping.L c.stopping.m

private def PB
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    flag c → Fin (c.stopping.L + 1) → Y → POVM B (fiber c) := by
  classical
  exact unconditionalActualFairSourceBobFlagPOVM
    G n S D c.sampler.denominator c.sampler.numerator
    c.sampler.nonempty (bobDefault c)
    c.stopping.P c.stopping.N c.stopping.L c.stopping.m

private def U
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    flag c → X →
      Matrix.unitaryGroup
        (Σ _ : Fin (c.stopping.L + 1), fiber c) ℂ :=
  unconditionalActualFairSourceAliceStoppingUnitary
    G n S D c.sampler.denominator c.sampler.numerator
    c.sampler.nonempty c.stopping.Q
    (width c) (schedule c) c.stopping.UA

private def V
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    flag c → Y →
      Matrix.unitaryGroup
        (Σ _ : Fin (c.stopping.L + 1), fiber c) ℂ :=
  unconditionalActualFairSourceBobStoppingUnitary
    G n S D c.sampler.denominator c.sampler.numerator
    c.sampler.nonempty c.stopping.Q
    (width c) (schedule c) c.stopping.UB

private def prepared
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    flag c → EuclideanSpace ℂ
      ((Σ _ : Fin (c.stopping.L + 1), fiber c) ×
       (Σ _ : Fin (c.stopping.L + 1), fiber c)) :=
  fun _ => unconditionalSourcePhysicalCleanedStoppingFixedSource
    1 c.stopping.P c.stopping.N (d c)
    c.stopping.L c.stopping.m

theorem prepared_normalized
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    ∀ f : flag c, ‖prepared c f‖ = 1 := by
  intro f
  exact unconditionalSourcePhysicalCleanedStoppingFixedSource_norm
    c.stopping.phases c.stopping.grid (dimension_pos c)
    c.stopping.harmonic

private def rounded
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : Strategy G :=
  unconditionalOneScaleActualSourceFlaggedStrategy
    G n S D c.remaining
    c.sampler.denominator c.sampler.numerator c.sampler.nonempty
    c.stopping.w c.stopping.N c.stopping.L c.stopping.P
    c.stopping.Q c.stopping.m c.stopping.phases c.stopping.grid
    c.stopping.harmonic c.stopping.UA c.stopping.UB

end UnconditionalActualFairSourceRoundingContext

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling
open UnconditionalActualFairSourceRoundingContext

attribute [local instance] Classical.propDecidable

theorem unconditionalActualFairSourceRoundingContext_actualRow
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (h : ExactLocallySampleableTuple X Y A B D) :
    (∑ j : Fin c.stopping.L, ‖actual c (h, j)‖ ^ 2) ≤ 1 := by
  exact unconditionalActualFairCleanedRow_le_one
    c.stopping.phases c.stopping.grid (dimension_pos c)
    c.stopping.harmonic (width c) (width_all c) (schedule c)
    (gammaVector c h) (phiVector c h)
    c.stopping.Q c.stopping.UA c.stopping.UB

theorem unconditionalActualFairSourceRoundingContext_clippingBound
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    clipping c ≤
      16 * martingaleRate G n S D +
        8 * (3 * alpha ^ (1 / 3 : ℝ) / 2) := by
  exact unconditionalActualC485FairSourceClipEnergy_le_budget
    (P := c.stopping.P) (m := c.stopping.m)
    G n S D c.remaining c.positive
    (width_positive c) c.stopping.grid (dimension_pos c)
    c.stopping.fine c.stopping.phases c.stopping.harmonic
    (schedule c) c.stopping.scalar

theorem unconditionalActualFairSourceRoundingContext_cleanBound
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    deviation c ≤
      (34 / Real.sqrt
          (64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ))) *
        (64 * Real.sqrt (martingaleRate G n S D) +
          alpha ^ (1 / 3 : ℝ)) +
        4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt (martingaleRate G n S D) +
                alpha ^ (1 / 3 : ℝ)) := by
  have identification :=
    unconditionalActualC485WeightedCleanDeviation_eq_hazard
      (law c) c.stopping.Q (width c) (schedule c)
      (gammaVector c) (phiVector c)
      c.stopping.UA c.stopping.UB
      (width_all c) c.stopping.phases c.stopping.grid
      (dimension_pos c) (fine_all c)
  have fair_hazard :
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        law c h *
          dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
            c.stopping.Q c.stopping.m (width c) (schedule c)
            (gammaVector c h) (phiVector c h)
            c.stopping.UA c.stopping.UB) ≤
        (34 / Real.sqrt
            (64 * Real.sqrt (martingaleRate G n S D) +
              alpha ^ (1 / 3 : ℝ))) *
          (64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
            unconditionalPrefactorBucketCoefficient *
              Real.sqrt
                (64 * Real.sqrt (martingaleRate G n S D) +
                  alpha ^ (1 / 3 : ℝ)) := by
    change
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D h *
          dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
            c.stopping.Q c.stopping.m
            (fun _ : Fin 1 => c.stopping.w)
            (fun _ : Fin c.stopping.L => 0)
            (unconditionalExactFairGammaUnit G n S D h)
            (exactGlobalHistoryFinPhi
              G n S D h.2.2.2 h.2.2.1)
            c.stopping.UA c.stopping.UB) ≤ _
    simpa only [unconditionalExactFairGammaUnit_eq_global] using
      c.stopping.hazard
  calc
    deviation c =
        (∑ h : ExactLocallySampleableTuple X Y A B D,
          law c h *
            dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
              c.stopping.Q c.stopping.m (width c) (schedule c)
              (gammaVector c h) (phiVector c h)
              c.stopping.UA c.stopping.UB) := by
          simpa only [deviation, actual, canonical] using identification
    _ ≤ _ := fair_hazard

theorem unconditionalActualFairSourceRoundingContext_analyticLedger
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    UnconditionalActualFairCachedStoppedAnalyticLedger
      (law c) (actual c) (canonical c) (source c)
      (deviation c) (clipping c) (bad c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact unconditionalActualFairWeightedCleanedMass_le_one
      (law c)
      (exactLocallySampleableLaw_nonneg G n S D c.positive)
      (exactLocallySampleableLaw_sum
        G n S D c.remaining c.positive)
      c.stopping.phases c.stopping.grid (dimension_pos c)
      c.stopping.harmonic (width c) (width_all c) (schedule c)
      (gammaVector c) (phiVector c)
      c.stopping.Q c.stopping.UA c.stopping.UB
  · exact unconditionalActualFairWeightedCanonicalMass_le_one
      (law c)
      (exactLocallySampleableLaw_nonneg G n S D c.positive)
      (exactLocallySampleableLaw_sum
        G n S D c.remaining c.positive)
      c.stopping.phases c.stopping.grid (dimension_pos c)
      c.stopping.harmonic (width c) (width_all c) (schedule c)
      (gammaVector c) (phiVector c) (fine_all c)
  · intro h
    exact unconditionalActualFairCanonicalRow_le_one
      c.stopping.phases c.stopping.grid (dimension_pos c)
      c.stopping.harmonic (width c) (width_all c) (schedule c)
      (gammaVector c h) (phiVector c h) (fine_all c)
  · intro h j
    exact unconditionalActualFairSourceCanonicalVector_norm
      c.stopping.phases c.stopping.grid c.stopping.harmonic
      (width c) (schedule c) (gammaVector c h) (phiVector c h)
      (psiVector c h) (exactSourceTuplePsi_norm G n S D h) j
      (width_all c (schedule c j)) (fine_all c (schedule c j))
  · exact le_refl (deviation c)
  · change
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        law c h *
          ∑ j : Fin c.stopping.L,
            ‖canonical c (h, j) - source c (h, j)‖ ^ 2) ≤
        unconditionalActualC485FairSourceClipEnergy
          (P := c.stopping.P) (m := c.stopping.m)
          G n S D (width_positive c) c.stopping.grid
          c.stopping.fine (schedule c)
    unfold unconditionalActualC485FairSourceClipEnergy
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro h _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    change
      ‖canonical c (h, j) - source c (h, j)‖ ^ 2 =
        ‖source c (h, j) - canonical c (h, j)‖ ^ 2
    rw [norm_sub_rev]
  · have async :
        (∑ h : ExactLocallySampleableTuple X Y A B D,
          law c h *
            dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
              c.stopping.N (width c) (schedule c)
              (gammaVector c h) (phiVector c h)) ≤
          64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ) := by
      change
        (∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
              c.stopping.N
              (fun _ : Fin 1 => c.stopping.w)
              (fun _ : Fin c.stopping.L => 0)
              (unconditionalExactFairGammaUnit G n S D h)
              (exactGlobalHistoryFinPhi
                G n S D h.2.2.2 h.2.2.1)) ≤ _
      simpa only [unconditionalExactFairGammaUnit_eq_global] using
        c.stopping.asynchronous
    have finish :
        (∑ h : ExactLocallySampleableTuple X Y A B D,
          law c h *
            dSVDensityRationalHeterogeneousPhysicalTerminalMass
              c.stopping.N (width c) (schedule c)
              (gammaVector c h) (phiVector c h)) ≤
          (alpha ^ (1 / 3 : ℝ)) ^ 2 := by
      change
        (∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            dSVDensityRationalHeterogeneousPhysicalTerminalMass
              c.stopping.N
              (fun _ : Fin 1 => c.stopping.w)
              (fun _ : Fin c.stopping.L => 0)
              (unconditionalExactFairGammaUnit G n S D h)
              (exactGlobalHistoryFinPhi
                G n S D h.2.2.2 h.2.2.1)) ≤ _
      simpa only [unconditionalExactFairGammaUnit_eq_global] using
        c.stopping.terminal
    exact unconditionalActualFairWeightedStoppedSuccess
      (law c)
      (exactLocallySampleableLaw_sum
        G n S D c.remaining c.positive)
      c.stopping.phases c.stopping.grid (dimension_pos c)
      c.stopping.harmonic (width c) (width_all c) (schedule c)
      (gammaVector c) (phiVector c)
      c.stopping.Q c.stopping.UA c.stopping.UB
      (64 * Real.sqrt (martingaleRate G n S D) +
        alpha ^ (1 / 3 : ℝ))
      ((alpha ^ (1 / 3 : ℝ)) ^ 2) async finish

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

theorem unconditionalActualFairSourceRoundingContext_verifierLedger
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    UnconditionalActualFairCachedSourceVerifierLedger
      G n S D c.effect c.actual c.source := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    exact unconditionalActualFairSourceVerifier_norm_le_one
      G n S D c.aliceDefault c.bobDefault
      p.2 p.1.2.1 p.1.2.2.1
  · intro h supported j
    change
      quadraticExpectation
          (integratorActualC485WinningEffect
            (P := c.stopping.P) (N := c.stopping.N)
            (m := c.stopping.m)
            G n S D c.aliceDefault c.bobDefault
            j h.2.1 h.2.2.1)
          (integratorActualC485SourceVector
            (S := 1) (B := c.stopping.P) (N := c.stopping.N)
            (d := c.d) (L := c.stopping.L) (m := c.stopping.m)
            c.width c.schedule
            (unconditionalExactFairGammaUnit G n S D h)
            (exactGlobalHistoryFinPhi
              G n S D h.2.2.2 h.2.2.1)
            (exactSourceTuplePsi G n S D h) j) =
        ‖integratorActualC485SourceVector
            (S := 1) (B := c.stopping.P) (N := c.stopping.N)
            (d := c.d) (L := c.stopping.L) (m := c.stopping.m)
            c.width c.schedule
            (unconditionalExactFairGammaUnit G n S D h)
            (exactGlobalHistoryFinPhi
              G n S D h.2.2.2 h.2.2.1)
            (exactSourceTuplePsi G n S D h) j‖ ^ 2 *
          exactSourceConditionalWinningProbability G n S D h
    rw [unconditionalExactFairGammaUnit_eq_global]
    exact unconditionalActualFairSourceSupportedBorn
      G n S D c.positive c.aliceDefault c.bobDefault h supported
      c.stopping.phases c.stopping.grid c.stopping.harmonic
      c.width c.schedule j
  · intro h
    exact unconditionalActualFairSourceVerifier_historyBorn_nonnegative
      G n S D c.aliceDefault c.bobDefault
      (fun h j => c.actual (h, j))
      (unconditionalActualFairSourceRoundingContext_actualRow c) h
  · intro h
    exact unconditionalActualFairSourceVerifier_historyBorn_bounded
      G n S D c.aliceDefault c.bobDefault
      (fun h j => c.actual (h, j))
      (unconditionalActualFairSourceRoundingContext_actualRow c) h

theorem unconditionalActualFairSourceRoundingContext_physicalBranch
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (flag : ExactSourceSharedFlag
      X Y A B D c.sampler.denominator)
    (x : X) (y : Y)
    (matching :
      exactSourcePermutationMatched
        D c.sampler.denominator c.sampler.numerator
        c.sampler.nonempty (flag, (x, y)) = true) :
    (∑ j : Fin c.stopping.L,
      quadraticExpectation
        (c.effect
          (exactSourceAliceSampleTuple
            D c.sampler.denominator c.sampler.numerator
            c.sampler.nonempty (flag, (x, y)), j))
        (c.actual
          (exactSourceAliceSampleTuple
            D c.sampler.denominator c.sampler.numerator
            c.sampler.nonempty (flag, (x, y)), j))) ≤
      ∑ j : Fin c.stopping.L,
        quadraticExpectation
          (Matrix.toEuclideanCLM
            (n := c.fiber × c.fiber) (𝕜 := ℂ)
            (actualStoppingBranchWinningEffect
              G (c.PA flag) (c.PB flag) j.succ j.succ x y))
          (actualStoppingBranchVector
            (actualStoppingQuestionLocalAction
              (c.U flag x) (c.V flag y) (c.prepared flag))
            j.succ j.succ) := by
  classical
  apply le_of_eq
  change
    (∑ j : Fin c.stopping.L,
      unconditionalActualFairSourceHistoryStopBorn
        G n S D c.aliceDefault c.bobDefault
        c.stopping.Q c.width c.schedule c.stopping.UA c.stopping.UB
        (exactSourceAliceSampleTuple
          D c.sampler.denominator c.sampler.numerator
          c.sampler.nonempty (flag, (x, y))) j) =
      ∑ j : Fin c.stopping.L,
        unconditionalActualFairSourcePhysicalStopBorn
          G n S D c.sampler.denominator c.sampler.numerator
          c.sampler.nonempty c.aliceDefault c.bobDefault
          c.stopping.Q c.width c.schedule
          c.stopping.UA c.stopping.UB flag x y j
  exact unconditionalActualFairSourcePhysicalBranchWitness
    G n S D c.sampler.denominator c.sampler.numerator
    c.sampler.nonempty c.aliceDefault c.bobDefault
    c.stopping.Q c.width c.schedule c.stopping.UA c.stopping.UB
    c.stopping.grid c.width_all flag x y matching

theorem unconditionalActualFairSourceRoundingContext_stoppedVerifier
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    1 - (1 - entangledValue G) / 2 -
      5 * (exactSourcePinskerRate G n S D + gamma) -
        ((64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ) +
            (alpha ^ (1 / 3 : ℝ)) ^ 2) +
          4 * Real.sqrt c.deviation + 2 * Real.sqrt c.clipping) ≤
      c.rounded.winProbability := by
  classical
  have stopped :=
    unconditionalActualFairCachedLedgerStoppingTransfer
      G n S D c.remaining c.positive
      c.sampler.base c.sampler.denominator c.sampler.denominator_positive
      c.sampler.numerator c.sampler.rational_normalized
      c.sampler.support_preserving c.sampler.nonempty
      c.PA c.PB c.U c.V c.prepared c.prepared_normalized
      (exactSourcePermutationMatched
        D c.sampler.denominator c.sampler.numerator c.sampler.nonempty)
      c.effect c.actual c.canonical c.source
      (1 - entangledValue G)
      (exactSourcePinskerRate G n S D + gamma)
      c.deviation c.clipping c.bad
      (unconditionalActualFairSourceRoundingContext_analyticLedger c)
      (unconditionalActualFairSourceRoundingContext_verifierLedger c)
      c.failure c.sampler.total_variation c.sampler.mismatch
      (fun flag x y matching =>
        unconditionalActualFairSourceRoundingContext_physicalBranch
          c flag x y matching)
  change
    1 - (1 - entangledValue G) / 2 -
      5 * (exactSourcePinskerRate G n S D + gamma) -
        ((64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ) +
            (alpha ^ (1 / 3 : ℝ)) ^ 2) +
          4 * Real.sqrt c.deviation + 2 * Real.sqrt c.clipping) ≤
      c.rounded.winProbability at stopped
  exact stopped

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

theorem unconditionalActualFairSourceRoundingData_exists_stoppedVerifier
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha gamma : ℝ)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (gamma_positive : 0 < gamma)
    (small : 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ) ≤ 1)
    (failure :
      uniformRemainingFailure
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D <
        (1 - entangledValue G) / 2) :
    ∃ (deviation clipping : ℝ) (rounded : Strategy G),
      (deviation ≤
        (34 / Real.sqrt
            (64 * Real.sqrt (martingaleRate G n S D) +
              alpha ^ (1 / 3 : ℝ))) *
          (64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt (martingaleRate G n S D) +
                alpha ^ (1 / 3 : ℝ))) ∧
      (clipping ≤
        16 * martingaleRate G n S D +
          8 * (3 * alpha ^ (1 / 3 : ℝ) / 2)) ∧
      (1 - (1 - entangledValue G) / 2 -
        5 * (exactSourcePinskerRate G n S D + gamma) -
          ((64 * Real.sqrt (martingaleRate G n S D) +
              alpha ^ (1 / 3 : ℝ) +
              (alpha ^ (1 / 3 : ℝ)) ^ 2) +
            4 * Real.sqrt deviation + 2 * Real.sqrt clipping) ≤
        rounded.winProbability) := by
  classical
  let context :=
    unconditionalActualFairSourceRoundingContextOfPositive
      G n S D remaining positive alpha gamma
      alpha_positive alpha_bounded gamma_positive small failure
  exact ⟨
    UnconditionalActualFairSourceRoundingContext.deviation context,
    UnconditionalActualFairSourceRoundingContext.clipping context,
    UnconditionalActualFairSourceRoundingContext.rounded context,
    unconditionalActualFairSourceRoundingContext_cleanBound context,
    unconditionalActualFairSourceRoundingContext_clippingBound context,
    unconditionalActualFairSourceRoundingContext_stoppedVerifier context⟩

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

theorem unconditionalSourcePhysicalRounding_exists_small
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha gamma : ℝ)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (gamma_positive : 0 < gamma)
    (small : 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ) ≤ 1)
    (failure :
      uniformRemainingFailure
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D <
        (1 - entangledValue G) / 2) :
    ∃ rounded : Strategy G,
      roundedWinningLowerBound
          (1 - entangledValue G)
          unconditionalSourcePhysicalRoundingUniversalConstant
          alpha (martingaleRate G n S D)
          (exactSourcePinskerRate G n S D + gamma) ≤
        rounded.winProbability := by
  obtain ⟨deviation, clipping, rounded,
      deviation_bound, clipping_bound, stopped⟩ :=
    unconditionalActualFairSourceRoundingData_exists_stoppedVerifier
      G n S D remaining positive alpha gamma
      alpha_positive alpha_bounded gamma_positive small failure
  refine ⟨rounded, ?_⟩
  exact
    unconditionalSourcePhysicalRounding_smallRoundedLower_of_stoppedVerifier
      G n S D remaining positive alpha gamma deviation clipping
      alpha_positive alpha_bounded gamma_positive small
      deviation_bound clipping_bound rounded stopped

theorem unconditionalSourceOneGameRounding_uniform :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B)
        (n : ℕ) (S : Strategy (G.repeat n))
        (D : Finset (Fin n)),
        0 < (Finset.univ \ D).card →
        0 < repeatedPostselectionMass G n S D →
        ∀ (alpha gamma : ℝ),
          0 < alpha → alpha ≤ 1 → 0 < gamma →
          uniformRemainingFailure
              (strategyEventLaw (G.repeat n) S)
              (repeatedCoordinateWin G n) D <
            (1 - entangledValue G) / 2 →
          ∃ rounded : Strategy G,
            roundedWinningLowerBound (1 - entangledValue G)
                K alpha (martingaleRate G n S D)
                (exactSourcePinskerRate G n S D + gamma) ≤
              rounded.winProbability :=
  unconditionalSourceOneGameRounding_uniform_of_small
    unconditionalSourcePhysicalRounding_exists_small

end

section

theorem pdf_distributionUniformExponential_unconditional :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B),
        Nonempty A → Nonempty B →
        0 < 1 - entangledValue G →
        ∀ n : ℕ, 0 < n →
          repeatedEntangledValue G n ≤
            Real.exp
              (-(c *
                ((1 - entangledValue G) ^ 13 /
                  ((1 - entangledValue G) +
                    Real.log
                      ((Fintype.card A : ℝ) *
                        (Fintype.card B : ℝ))))) * (n : ℝ)) :=
  pdf_distributionUniformExponential_of_uniform_source_rounding
    unconditionalSourceOneGameRounding_uniform

theorem exactSourceOneGameRounding_unconditional
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) :
    ExactSourceOneGameRounding G := by
  obtain ⟨K, lowerBound, round⟩ :=
    unconditionalSourceOneGameRounding_uniform
  refine ⟨K, le_trans (by norm_num : (0 : ℝ) ≤ 1) lowerBound, ?_⟩
  exact round G

theorem exact_standardQuantumParallelRepetition_unconditional
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) :
    StandardQuantumParallelRepetition G :=
  exact_standardQuantumParallelRepetition_of_source_rounding G
    (exactSourceOneGameRounding_unconditional G)

/-- A universal exponential upper bound for the repeated entangled value. -/
theorem distributionUniformExponential :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B),
        Nonempty A → Nonempty B →
        0 < 1 - entangledValue G →
        ∀ n : ℕ, 0 < n →
          repeatedEntangledValue G n ≤
            Real.exp
              (-(c *
                ((1 - entangledValue G) ^ 13 /
                  ((1 - entangledValue G) +
                    Real.log
                      ((Fintype.card A : ℝ) *
                        (Fintype.card B : ℝ))))) * (n : ℝ)) :=
  pdf_distributionUniformExponential_unconditional

/-- The standard quantum parallel-repetition bound for every finite nonlocal game. -/
theorem standardQuantumParallelRepetition
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) :
    StandardQuantumParallelRepetition G :=
  exact_standardQuantumParallelRepetition_unconditional G

end


end QuantumParallelRepetition

end
