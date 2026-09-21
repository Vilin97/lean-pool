/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.KAveraging

/-! # Dirichlet Bridge -/

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

/-- The depthwise smoothing estimate implies the exact finite partial bound
used by the public Dirichlet Besov theorem.  The mean term in the public
statement is harmless here; the depthwise estimate controls the K-partial
seminorm directly by the overlapping partial seminorm. -/
theorem cubeKBesovPartialBoundByOverlappingPositive_of_depthBound
    {d : ℕ}
    (hdepth : CubeKBesovDepthBoundByOverlappingPositive d) :
    CubeKBesovPartialBoundByOverlappingPositive d := by
  intro s hs_pos hs_lt
  rcases hdepth hs_pos hs_lt with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro Q h N _hh
  have hpartial :
      cubeKBesovVectorPartialSeminormTwo Q s N h ≤
        C * cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N h :=
    cubeKBesovVectorPartialSeminormTwo_le_mul_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_of_forall_depthSeminorm_le
      Q s C N h hC_nonneg fun j _hj => hC Q h j _hh
  have hmean_nonneg : 0 ≤ Real.sqrt (vecNormSq (cubeAverageVec Q h)) :=
    Real.sqrt_nonneg _
  have hoverlap_nonneg :
      0 ≤ cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N h :=
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo_nonneg Q s N h
  have hsum :
      cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N h ≤
        Real.sqrt (vecNormSq (cubeAverageVec Q h)) +
          cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N h := by
    linarith
  exact hpartial.trans
    (mul_le_mul_of_nonneg_left hsum hC_nonneg)

/-- Uniform-in-`s` depth control implies the uniform finite partial
K/overlap comparison. -/
theorem cubeKBesovPartialBoundByOverlappingPositiveUniform_of_depthBound
    {d : ℕ} {C : ℝ}
    (hdepth : CubeKBesovDepthBoundByOverlappingPositiveUniform d C) :
    CubeKBesovPartialBoundByOverlappingPositiveUniform d C := by
  refine ⟨hdepth.1, ?_⟩
  intro s hs_pos hs_lt Q h N hh
  have hpartial :
      cubeKBesovVectorPartialSeminormTwo Q s N h ≤
        C * cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N h :=
    cubeKBesovVectorPartialSeminormTwo_le_mul_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_of_forall_depthSeminorm_le
      Q s C N h hdepth.1 fun j _hj =>
        hdepth.2 hs_pos hs_lt Q h j hh
  have hmean_nonneg : 0 ≤ Real.sqrt (vecNormSq (cubeAverageVec Q h)) :=
    Real.sqrt_nonneg _
  have hoverlap_nonneg :
      0 ≤ cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N h :=
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo_nonneg Q s N h
  have hsum :
      cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N h ≤
        Real.sqrt (vecNormSq (cubeAverageVec Q h)) +
          cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N h := by
    linarith
  exact hpartial.trans
    (mul_le_mul_of_nonneg_left hsum hdepth.1)

/-- Direct Phase-7 bridge: the one-depth overlap-averaging competitor estimate
is enough to replace the finite partial K/overlap axiom. -/
theorem cubeKBesovPartialBoundByOverlappingPositive_of_overlapAveragingCompetitorEstimate
    {d : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hcomp : CubeKBesovOverlapAveragingCompetitorEstimate d C) :
    CubeKBesovPartialBoundByOverlappingPositive d :=
  cubeKBesovPartialBoundByOverlappingPositive_of_depthBound
    (cubeKBesovDepthBoundByOverlappingPositive_of_overlapAveragingCompetitorEstimate
      hC hcomp)

/-- Uniform version of the Phase-7 bridge from the concrete overlap averaging
competitor estimate to the finite partial K/overlap comparison. -/
theorem cubeKBesovPartialBoundByOverlappingPositiveUniform_of_overlapAveragingCompetitorEstimate
    {d : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hcomp : CubeKBesovOverlapAveragingCompetitorEstimate d C) :
    CubeKBesovPartialBoundByOverlappingPositiveUniform d (2 * C) :=
  cubeKBesovPartialBoundByOverlappingPositiveUniform_of_depthBound
    (cubeKBesovDepthBoundByOverlappingPositiveUniform_of_overlapAveragingCompetitorEstimate
      hC hcomp)

/-- The finite-level K/overlapping comparison implies the boundedness bridge
needed to use the full K-functional seminorm for overlapping-regular inputs. -/
theorem cubeKBesovInputBoundednessOfOverlappingHRegularity_of_partialBoundByOverlappingPositive
    {d : ℕ}
    (hpartial : CubeKBesovPartialBoundByOverlappingPositive d) :
    CubeKBesovInputBoundednessOfOverlappingHRegularity d := by
  intro s hs_pos hs_lt Q h hh
  rcases hpartial hs_pos hs_lt with ⟨C, hC_nonneg, hC⟩
  rcases hh.partialSeminorms_bddAbove with ⟨B, hB⟩
  refine ⟨C * (Real.sqrt (vecNormSq (cubeAverageVec Q h)) + B), ?_⟩
  rintro y ⟨N, rfl⟩
  have hpos_le :
      cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N h ≤ B :=
    hB ⟨N, rfl⟩
  have hsum_le :
      Real.sqrt (vecNormSq (cubeAverageVec Q h)) +
          cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N h ≤
        Real.sqrt (vecNormSq (cubeAverageVec Q h)) + B :=
    add_le_add le_rfl hpos_le
  exact (hC Q h N hh.memLp).trans
    (mul_le_mul_of_nonneg_left hsum_le hC_nonneg)

/-- The proved overlap-Poincare estimate controls the full overlapping
positive seminorm by the full K-functional seminorm, provided the K partial
seminorms are bounded above so the real `sSup` is a genuine supremum. -/
theorem cubeBesovOverlappingPositiveVectorSeminormTwo_le_mul_cubeKBesovVectorSeminormTwo_of_overlapPoincare
    {d : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hPoincare : CubeVectorH1OverlapPoincareEstimate d C)
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hK_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N F)) :
    cubeBesovOverlappingPositiveVectorSeminormTwo Q s F ≤
      (8 * (3 ^ d : ℝ) + 2 * C ^ 2 + 1) *
        cubeKBesovVectorSeminormTwo Q s F := by
  let A : ℝ := 8 * (3 ^ d : ℝ) + 2 * C ^ 2 + 1
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  refine
    cubeBesovOverlappingPositiveVectorSeminormTwo_le_of_partialBound
      Q s F (B := A * cubeKBesovVectorSeminormTwo Q s F) ?_
  intro N
  have hpartial :
      cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F ≤
        A * cubeKBesovVectorPartialSeminormTwo Q s N F := by
    simpa [A] using
      cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_mul_cubeKBesovVectorPartialSeminormTwo_of_overlapPoincare
        hC hPoincare Q s N F hF
  exact hpartial.trans
    (mul_le_mul_of_nonneg_left
      (cubeKBesovVectorPartialSeminormTwo_le_seminorm_of_bddAbove
        Q s F hK_bdd N)
      hA_nonneg)

/-- Bounded K-functional partial sums give overlapping Besov regularity. -/
theorem cubeVectorOverlappingBesovHRegularity_of_memLp_of_kPartial_bddAbove
    {d : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hPoincare : CubeVectorH1OverlapPoincareEstimate d C)
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hK_bdd : BddAbove (Set.range fun N : ℕ =>
      cubeKBesovVectorPartialSeminormTwo Q s N F)) :
    CubeVectorOverlappingBesovHRegularity Q s F := by
  refine ⟨hF, ?_⟩
  let A : ℝ := 8 * (3 ^ d : ℝ) + 2 * C ^ 2 + 1
  have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
  rcases hK_bdd with ⟨B, hB⟩
  refine ⟨A * B, ?_⟩
  rintro y ⟨N, rfl⟩
  have hpartial :
      cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F ≤
        A * cubeKBesovVectorPartialSeminormTwo Q s N F := by
    simpa [A] using
      cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_mul_cubeKBesovVectorPartialSeminormTwo_of_overlapPoincare
        hC hPoincare Q s N F hF
  exact hpartial.trans (mul_le_mul_of_nonneg_left (hB ⟨N, rfl⟩) hA_nonneg)

/-- Norm-level version of the overlap-to-K comparison.  The mean term is the
same on both sides, so the seminorm comparison only costs one extra additive
constant. -/
theorem cubeBesovOverlappingPositiveVectorNormTwo_le_mul_cubeKBesovVectorNormTwo_of_overlapPoincare
    {d : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hPoincare : CubeVectorH1OverlapPoincareEstimate d C)
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hK_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N F)) :
    cubeBesovOverlappingPositiveVectorNormTwo Q s F ≤
      (8 * (3 ^ d : ℝ) + 2 * C ^ 2 + 2) *
        cubeKBesovVectorNormTwo Q s F := by
  let A : ℝ := 8 * (3 ^ d : ℝ) + 2 * C ^ 2 + 1
  let M : ℝ := Real.sqrt (vecNormSq (cubeAverageVec Q F))
  let BO : ℝ := cubeBesovOverlappingPositiveVectorSeminormTwo Q s F
  let BK : ℝ := cubeKBesovVectorSeminormTwo Q s F
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Real.sqrt_nonneg _
  have hBK_nonneg : 0 ≤ BK := by
    dsimp [BK]
    exact cubeKBesovVectorSeminormTwo_nonneg_of_bddAbove Q s F hK_bdd
  have hsemi : BO ≤ A * BK := by
    dsimp [BO, BK, A]
    exact
      cubeBesovOverlappingPositiveVectorSeminormTwo_le_mul_cubeKBesovVectorSeminormTwo_of_overlapPoincare
        hC hPoincare Q s F hF hK_bdd
  calc
    cubeBesovOverlappingPositiveVectorNormTwo Q s F
        = M + BO := by rfl
    _ ≤ M + A * BK := add_le_add le_rfl hsemi
    _ ≤ (A + 1) * (M + BK) := by
          nlinarith
    _ =
        (8 * (3 ^ d : ℝ) + 2 * C ^ 2 + 2) *
          cubeKBesovVectorNormTwo Q s F := by
          dsimp [A, M, BK, cubeKBesovVectorNormTwo]
          ring

/-- The finite-level K-partial comparison gives a full K-norm bound on every
input with overlapping Besov regularity. -/
theorem cubeKBesovVectorNormTwo_le_mul_cubeBesovOverlappingPositiveVectorNormTwo_of_partialBound
    {d : ℕ}
    (hpartial : CubeKBesovPartialBoundByOverlappingPositive d)
    {s : ℝ} (hs_pos : 0 < s) (hs_lt : s < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : TriadicCube d) (F : Vec d → Vec d),
        CubeVectorOverlappingBesovHRegularity Q s F →
          cubeKBesovVectorNormTwo Q s F ≤
            C * cubeBesovOverlappingPositiveVectorNormTwo Q s F := by
  rcases hpartial hs_pos hs_lt with ⟨C, hC_nonneg, hC⟩
  refine ⟨C + 1, add_nonneg hC_nonneg zero_le_one, ?_⟩
  intro Q F hF
  let M : ℝ := Real.sqrt (vecNormSq (cubeAverageVec Q F))
  let BO : ℝ := cubeBesovOverlappingPositiveVectorSeminormTwo Q s F
  let BK : ℝ := cubeKBesovVectorSeminormTwo Q s F
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Real.sqrt_nonneg _
  have hBO_nonneg : 0 ≤ BO := by
    dsimp [BO]
    exact hF.seminorm_nonneg
  have hNorm_nonneg :
      0 ≤ cubeBesovOverlappingPositiveVectorNormTwo Q s F :=
    hF.norm_nonneg
  have hM_le_norm :
      M ≤ cubeBesovOverlappingPositiveVectorNormTwo Q s F := by
    dsimp [M, BO, cubeBesovOverlappingPositiveVectorNormTwo]
    linarith
  have hsemi :
      BK ≤ C * cubeBesovOverlappingPositiveVectorNormTwo Q s F := by
    dsimp [BK]
    refine cubeKBesovVectorSeminormTwo_le_of_partialBound Q s F ?_
    intro N
    have hpartialN :
        cubeKBesovVectorPartialSeminormTwo Q s N F ≤
          C *
            (Real.sqrt (vecNormSq (cubeAverageVec Q F)) +
              cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F) :=
      hC Q F N hF.memLp
    have hsum_le :
        Real.sqrt (vecNormSq (cubeAverageVec Q F)) +
            cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F ≤
          cubeBesovOverlappingPositiveVectorNormTwo Q s F := by
      dsimp [cubeBesovOverlappingPositiveVectorNormTwo]
      exact add_le_add le_rfl (hF.partialSeminorm_le_seminorm N)
    exact hpartialN.trans
      (mul_le_mul_of_nonneg_left hsum_le hC_nonneg)
  calc
    cubeKBesovVectorNormTwo Q s F
        = M + BK := by rfl
    _ ≤ M + C * cubeBesovOverlappingPositiveVectorNormTwo Q s F :=
        add_le_add le_rfl hsemi
    _ ≤
        (C + 1) * cubeBesovOverlappingPositiveVectorNormTwo Q s F := by
        nlinarith

/-- Uniform version of the K-norm bound by the corrected overlapping positive
norm. -/
theorem cubeKBesovVectorNormTwo_le_mul_cubeBesovOverlappingPositiveVectorNormTwo_of_partialBoundUniform
    {d : ℕ} {C : ℝ}
    (hpartial : CubeKBesovPartialBoundByOverlappingPositiveUniform d C)
    {s : ℝ} (hs_pos : 0 < s) (hs_lt : s < 1)
    (Q : TriadicCube d) (F : Vec d → Vec d) :
    CubeVectorOverlappingBesovHRegularity Q s F →
      cubeKBesovVectorNormTwo Q s F ≤
        (C + 1) * cubeBesovOverlappingPositiveVectorNormTwo Q s F := by
  intro hF
  let M : ℝ := Real.sqrt (vecNormSq (cubeAverageVec Q F))
  let BO : ℝ := cubeBesovOverlappingPositiveVectorSeminormTwo Q s F
  let BK : ℝ := cubeKBesovVectorSeminormTwo Q s F
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Real.sqrt_nonneg _
  have hBO_nonneg : 0 ≤ BO := by
    dsimp [BO]
    exact hF.seminorm_nonneg
  have hNorm_nonneg :
      0 ≤ cubeBesovOverlappingPositiveVectorNormTwo Q s F :=
    hF.norm_nonneg
  have hM_le_norm :
      M ≤ cubeBesovOverlappingPositiveVectorNormTwo Q s F := by
    dsimp [M, BO, cubeBesovOverlappingPositiveVectorNormTwo]
    linarith
  have hsemi :
      BK ≤ C * cubeBesovOverlappingPositiveVectorNormTwo Q s F := by
    dsimp [BK]
    refine cubeKBesovVectorSeminormTwo_le_of_partialBound Q s F ?_
    intro N
    have hpartialN :
        cubeKBesovVectorPartialSeminormTwo Q s N F ≤
          C *
            (Real.sqrt (vecNormSq (cubeAverageVec Q F)) +
              cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F) :=
      hpartial.2 hs_pos hs_lt Q F N hF.memLp
    have hsum_le :
        Real.sqrt (vecNormSq (cubeAverageVec Q F)) +
            cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F ≤
          cubeBesovOverlappingPositiveVectorNormTwo Q s F := by
      dsimp [cubeBesovOverlappingPositiveVectorNormTwo]
      exact add_le_add le_rfl (hF.partialSeminorm_le_seminorm N)
    exact hpartialN.trans
      (mul_le_mul_of_nonneg_left hsum_le hpartial.1)
  calc
    cubeKBesovVectorNormTwo Q s F
        = M + BK := by rfl
    _ ≤ M + C * cubeBesovOverlappingPositiveVectorNormTwo Q s F :=
        add_le_add le_rfl hsemi
    _ ≤
        (C + 1) * cubeBesovOverlappingPositiveVectorNormTwo Q s F := by
        nlinarith

/-- Mean-term estimate for the gradient of the zero-Dirichlet divergence
solution. In the classical proof this is the zero-trace averaged-gradient
identity, packaged as an estimate so it composes with the norm algebra. -/
def CubeDirichletGradientAverageRegularity
    (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Q : TriadicCube d) (h : Vec d → Vec d)
      (w : H10Function (openCubeSet Q)),
      CubeDirichletDivergenceProblem Q w h →
        Real.sqrt
            (vecNormSq
              (cubeAverageVec Q fun x => w.toH1Function.grad x)) ≤
          C * Real.sqrt (vecNormSq (cubeAverageVec Q h))

/-- Pointwise-in-scale K-functional estimate for the zero-Dirichlet divergence
solution operator. This is the interpolation core before summing over
dyadic/triadic depths. -/
def CubeKFunctionalDirichletPointwiseRegularity
    (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Q : TriadicCube d) (h : Vec d → Vec d)
      (w : H10Function (openCubeSet Q)) (t : ℝ),
      MeasureTheory.MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
      CubeDirichletDivergenceProblem Q w h →
        cubeVectorKFunctional Q t (fun x => w.toH1Function.grad x) ≤
          C * cubeVectorKFunctional Q t h

/-- Endpoint decomposition needed for the K-functional proof. For each
`H¹` competitor `G` for the datum `h`, produce an `H¹` competitor `V` for the
solution gradient whose residual is controlled by the `L²` endpoint and whose
`H¹` size is controlled by the Dirichlet `H²` endpoint. -/
def CubeDirichletKEndpointDecomposition
    (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Q : TriadicCube d) (h : Vec d → Vec d)
      (w : H10Function (openCubeSet Q)) (G : CubeVectorH1Function Q),
      MeasureTheory.MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
      CubeDirichletDivergenceProblem Q w h →
        ∃ V : CubeVectorH1Function Q,
          cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x => w.toH1Function.grad x - V.toField x) ≤
            C * cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x => h x - G.toField x) ∧
          V.gradientCoordL2NormSum ≤ C * G.gradientCoordL2NormSum

/-- Two-constant endpoint construction behind
`CubeDirichletKEndpointDecomposition`. The first constant is the `L²` residual
stability constant; the second is the Dirichlet `H²`/`H¹` competitor-size
constant. Keeping them separate mirrors the analytic proof before the final
K-functional algebra absorbs both into one constant. -/
def CubeDirichletKEndpointCompetitorConstruction
    (d : ℕ) : Prop :=
  ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧
    ∀ (Q : TriadicCube d) (h : Vec d → Vec d)
      (w : H10Function (openCubeSet Q)) (G : CubeVectorH1Function Q),
      MeasureTheory.MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
      CubeDirichletDivergenceProblem Q w h →
        ∃ V : CubeVectorH1Function Q,
          cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x => w.toH1Function.grad x - V.toField x) ≤
            C0 * cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x => h x - G.toField x) ∧
          V.gradientCoordL2NormSum ≤ C1 * G.gradientCoordL2NormSum

/-- One-solution energy estimate for the constant-coefficient zero-Dirichlet
divergence solver. This is the real analytic input behind residual stability:
test the equation with the solution and apply Cauchy-Schwarz. -/
def CubeDirichletDivergenceEnergyEstimate
    (d : ℕ) : Prop :=
  ∃ C0 : ℝ, 0 ≤ C0 ∧
    ∀ (Q : TriadicCube d) (F : Vec d → Vec d)
      (u : H10Function (openCubeSet Q)),
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
      CubeDirichletDivergenceProblem Q u F →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.toH1Function.grad x) ≤
          C0 * cubeLpNorm Q (2 : ℝ≥0∞) F

/-- Residual `L²` stability for the constant-coefficient zero-Dirichlet
divergence solver. This packages the energy estimate applied to the difference
of two solutions, avoiding any commitment here to a particular formalization of
solution subtraction. -/
def CubeDirichletDivergenceResidualL2Stability
    (d : ℕ) : Prop :=
  ∃ C0 : ℝ, 0 ≤ C0 ∧
    ∀ (Q : TriadicCube d) (h : Vec d → Vec d)
      (w : H10Function (openCubeSet Q)) (G : CubeVectorH1Function Q)
      (v : H10Function (openCubeSet Q)),
      MeasureTheory.MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
      CubeDirichletDivergenceProblem Q w h →
      CubeDirichletDivergenceProblem Q v G.toField →
        cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => w.toH1Function.grad x - v.toH1Function.grad x) ≤
          C0 * cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => h x - G.toField x)

/-- Dirichlet `H²` endpoint as an `H¹` lift for vector-field competitors.
Given an `H¹` vector competitor `G`, solve the corresponding divergence-RHS
Dirichlet problem and realize its gradient as a coordinatewise `H¹` vector
field `V`, with the expected `H¹` bound. -/
def CubeDirichletH1CompetitorLiftRegularity
    (d : ℕ) : Prop :=
  ∃ C1 : ℝ, 0 ≤ C1 ∧
    ∀ (Q : TriadicCube d) (G : CubeVectorH1Function Q),
      ∃ (v : H10Function (openCubeSet Q)) (V : CubeVectorH1Function Q),
        CubeDirichletDivergenceProblem Q v G.toField ∧
          V.toField = (fun x => v.toH1Function.grad x) ∧
          V.gradientCoordL2NormSum ≤ C1 * G.gradientCoordL2NormSum

/-- Weak-divergence realization needed to feed the scalar Dirichlet `H²`
theorem.  For each coordinatewise `H¹` vector field `G`, the zero-Dirichlet
solution of the divergence problem is also a scalar Poisson solution with
forcing `div G`. -/
def CubeVectorH1DivergencePoissonRealization
    (d : ℕ) : Prop :=
  ∀ (Q : TriadicCube d) (G : CubeVectorH1Function Q),
    ∃ v : H10Function (openCubeSet Q),
      CubeDirichletDivergenceProblem Q v G.toField ∧
        CubeDirichletWeakPoissonProblem Q v G.divergence

/-- Sharper analytic form of the Dirichlet `H²` endpoint for H¹ vector
competitors. It supplies the divergence-RHS solution and a weak Hessian bound;
the coordinatewise H¹ competitor is then a formal wrapper around the Hessian
witness. -/
def CubeDirichletDivergenceH2CompetitorRegularity
    (d : ℕ) : Prop :=
  ∃ C1 : ℝ, 0 ≤ C1 ∧
    ∀ (Q : TriadicCube d) (G : CubeVectorH1Function Q),
      ∃ (v : H10Function (openCubeSet Q))
        (H : HasWeakHessianOn (openCubeSet Q) v.toH1Function),
        CubeDirichletDivergenceProblem Q v G.toField ∧
          H.hessianCoordL2NormSum ≤ C1 * G.gradientCoordL2NormSum

theorem cubeDirichletDivergenceH2CompetitorRegularity_of_vectorH1DivergencePoissonRealization
    {d : ℕ} [NeZero d]
    (hreal : CubeVectorH1DivergencePoissonRealization d) :
    CubeDirichletDivergenceH2CompetitorRegularity d := by
  rcases
    CubeDirichletWeakPoissonProblem.exists_cubeDirichletH2RegularityVolumeL2InDimension d
    with ⟨C1, hH2⟩
  refine ⟨C1, hH2.1, ?_⟩
  intro Q G
  rcases hreal Q G with ⟨v, hdivProblem, hpoisson⟩
  let hdivNorm : MemScalarL2 (openCubeSet Q) G.divergence :=
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q
      (G.divergence_memLp_normalizedCubeMeasure)
  rcases (hH2.2 Q).2 v G.divergence
      G.divergence_memLp_normalizedCubeMeasure hpoisson with
    ⟨H, hH⟩
  refine ⟨v, H, hdivProblem, ?_⟩
  exact hH.trans
    (mul_le_mul_of_nonneg_left
      (G.norm_toScalarL2_divergence_le_gradientCoordL2NormSum hdivNorm)
      hH2.1)

theorem cubeDirichletH1CompetitorLiftRegularity_of_divergenceH2CompetitorRegularity
    {d : ℕ}
    (hH2 : CubeDirichletDivergenceH2CompetitorRegularity d) :
    CubeDirichletH1CompetitorLiftRegularity d := by
  rcases hH2 with ⟨C1, hC1_nonneg, hH2⟩
  refine ⟨C1, hC1_nonneg, ?_⟩
  intro Q G
  rcases hH2 Q G with ⟨v, H, hweak, hH⟩
  refine ⟨v, CubeVectorH1Function.ofWeakHessianGradient H, hweak, ?_, ?_⟩
  · exact CubeVectorH1Function.ofWeakHessianGradient_toField H
  · simpa [CubeVectorH1Function.gradientCoordL2NormSum_ofWeakHessianGradient H] using hH

theorem cubeDirichletDivergenceProblem_sub
    {d : ℕ} {Q : TriadicCube d} {h k : Vec d → Vec d}
    {w v : H10Function (openCubeSet Q)}
    (hh : MeasureTheory.MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hk : MeasureTheory.MemLp k (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hw : CubeDirichletDivergenceProblem Q w h)
    (hv : CubeDirichletDivergenceProblem Q v k) :
    CubeDirichletDivergenceProblem Q (w - v) (fun x => h x - k x) := by
  intro φ
  have hhOpen : MemVectorL2 (openCubeSet Q) h :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hh
  have hkOpen : MemVectorL2 (openCubeSet Q) k :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hk
  have hwInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x))
        (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2
      w.toH1Function.grad_memVectorL2 φ.toH1Function.grad_memVectorL2
  have hvInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (v.toH1Function.grad x) (φ.toH1Function.grad x))
        (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2
      v.toH1Function.grad_memVectorL2 φ.toH1Function.grad_memVectorL2
  have hhInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (h x) (φ.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hhOpen φ.toH1Function.grad_memVectorL2
  have hkInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (k x) (φ.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hkOpen φ.toH1Function.grad_memVectorL2
  have hleft_fun :
      (fun x =>
          vecDot ((w - v).toH1Function.grad x) (φ.toH1Function.grad x)) =
        fun x =>
          vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) -
            vecDot (v.toH1Function.grad x) (φ.toH1Function.grad x) := by
    funext x
    have hgradSubX :
        (w - v).toH1Function.grad x =
          w.toH1Function.grad x - v.toH1Function.grad x := by
      change (w.toH1Function - v.toH1Function).grad x =
        w.toH1Function.grad x - v.toH1Function.grad x
      exact congrFun (H1Function.sub_grad w.toH1Function v.toH1Function) x
    rw [hgradSubX]
    simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  have hright_fun :
      (fun x => vecDot (h x - k x) (φ.toH1Function.grad x)) =
        fun x =>
          vecDot (h x) (φ.toH1Function.grad x) -
            vecDot (k x) (φ.toH1Function.grad x) := by
    funext x
    simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  have hrhs_sub :
      ∫ x in openCubeSet Q, vecDot (h x - k x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q, vecDot (h x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume -
        ∫ x in openCubeSet Q, vecDot (k x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume := by
    rw [hright_fun, MeasureTheory.integral_sub hhInt hkInt]
  calc
    ∫ x in openCubeSet Q,
        vecDot ((w - v).toH1Function.grad x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume
        =
          ∫ x in openCubeSet Q,
            (vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) -
              vecDot (v.toH1Function.grad x) (φ.toH1Function.grad x))
            ∂MeasureTheory.volume := by
              rw [hleft_fun]
    _ =
        ∫ x in openCubeSet Q, vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume -
        ∫ x in openCubeSet Q, vecDot (v.toH1Function.grad x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_sub hwInt hvInt]
    _ =
        -∫ x in openCubeSet Q, vecDot (h x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume -
        -∫ x in openCubeSet Q, vecDot (k x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume := by
            rw [hw φ, hv φ]
    _ =
        - (∫ x in openCubeSet Q, vecDot (h x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume -
        ∫ x in openCubeSet Q, vecDot (k x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume) := by
            ring
    _ =
        -∫ x in openCubeSet Q, vecDot (h x - k x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume := by
            rw [hrhs_sub]

theorem cubeDirichletDivergenceResidualL2Stability_of_energyEstimate
    {d : ℕ}
    (henergy : CubeDirichletDivergenceEnergyEstimate d) :
    CubeDirichletDivergenceResidualL2Stability d := by
  rcases henergy with ⟨C0, hC0_nonneg, henergy⟩
  refine ⟨C0, hC0_nonneg, ?_⟩
  intro Q h w G v hh hw hv
  have hGmem : MeasureTheory.MemLp G.toField (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    G.memLp_toField_normalizedCubeMeasure
  have hresMem :
      MeasureTheory.MemLp (fun x => h x - G.toField x) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
    G.memLp_sub_toField_normalizedCubeMeasure hh
  have hresWeak :
      CubeDirichletDivergenceProblem Q (w - v) (fun x => h x - G.toField x) :=
    cubeDirichletDivergenceProblem_sub
      (Q := Q) (h := h) (k := G.toField) hh hGmem hw hv
  have hgradEq :
      (fun x => (w - v).toH1Function.grad x) =
        fun x => w.toH1Function.grad x - v.toH1Function.grad x := by
    funext x
    change (w.toH1Function - v.toH1Function).grad x =
      w.toH1Function.grad x - v.toH1Function.grad x
    exact congrFun (H1Function.sub_grad w.toH1Function v.toH1Function) x
  simpa [hgradEq] using
    henergy Q (fun x => h x - G.toField x) (w - v) hresMem hresWeak

theorem cubeDirichletKEndpointCompetitorConstruction_of_residualStability_of_liftRegularity
    {d : ℕ}
    (hstable : CubeDirichletDivergenceResidualL2Stability d)
    (hlift : CubeDirichletH1CompetitorLiftRegularity d) :
    CubeDirichletKEndpointCompetitorConstruction d := by
  rcases hstable with ⟨C0, hC0_nonneg, hstable⟩
  rcases hlift with ⟨C1, hC1_nonneg, hlift⟩
  refine ⟨C0, C1, hC0_nonneg, hC1_nonneg, ?_⟩
  intro Q h w G hh hweak
  rcases hlift Q G with ⟨v, V, hv, hVfield, hVgrad⟩
  refine ⟨V, ?_, hVgrad⟩
  simpa [hVfield] using hstable Q h w G v hh hweak hv

theorem cubeDirichletKEndpointDecomposition_of_competitorConstruction
    {d : ℕ}
    (hendpoint : CubeDirichletKEndpointCompetitorConstruction d) :
    CubeDirichletKEndpointDecomposition d := by
  rcases hendpoint with ⟨C0, C1, hC0_nonneg, hC1_nonneg, hendpoint⟩
  refine ⟨C0 + C1, add_nonneg hC0_nonneg hC1_nonneg, ?_⟩
  intro Q h w G hh hweak
  rcases hendpoint Q h w G hh hweak with ⟨V, hL2, hGrad⟩
  refine ⟨V, ?_, ?_⟩
  · have hC0_le : C0 ≤ C0 + C1 := by
      linarith
    exact hL2.trans
      (mul_le_mul_of_nonneg_right hC0_le
        (cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
          (fun x => h x - G.toField x)))
  · have hC1_le : C1 ≤ C0 + C1 := by
      linarith
    exact hGrad.trans
      (mul_le_mul_of_nonneg_right hC1_le
        G.gradientCoordL2NormSum_nonneg)

theorem cubeKFunctionalDirichletPointwiseRegularity_of_endpointDecomposition
    {d : ℕ}
    (hendpoint : CubeDirichletKEndpointDecomposition d) :
    CubeKFunctionalDirichletPointwiseRegularity d := by
  rcases hendpoint with ⟨C, hC_nonneg, hendpoint⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro Q h w t hh hweak
  refine cubeVectorKFunctional_le_of_forall_competitorValue_le
    Q t C (fun x => w.toH1Function.grad x) h hC_nonneg ?_
  intro G
  rcases hendpoint Q h w G hh hweak with ⟨V, hL2, hGrad⟩
  exact ⟨V,
    cubeVectorKFunctionalCompetitorValue_le_of_endpoint_bounds
      Q t C (fun x => w.toH1Function.grad x) h V G hC_nonneg hL2 hGrad⟩

/-- The three focused ingredients that imply the K-functional Dirichlet
Besov regularity statement. -/
def CubeKBesovDirichletRegularityComponents
    (d : ℕ) : Prop :=
  CubeKBesovInputBoundednessOfOverlappingHRegularity d ∧
    CubeDirichletGradientAverageRegularity d ∧
      CubeKFunctionalDirichletPointwiseRegularity d

/-- The full pure function-space input for the canonical K-functional model:
norm equivalence with the corrected overlapping positive Besov norm, together
with boundedness of the canonical K partial sums for overlapping-regular
inputs. -/
def CubeKBesovCanonicalOverlappingTheory
    (d : ℕ) [NeZero d] : Prop :=
  CubeKBesovOverlappingEquivalence (cubeKBesovNormModel d) ∧
    CubeKBesovInputBoundednessOfOverlappingHRegularity d

/-- Sharpened pure canonical K-functional/overlapping theory. The second
component is finite-level K-partial control by the overlapping-positive partial
sums, which then implies the boundedness bridge for full K-seminorms. -/
def CubeKBesovCanonicalOverlappingTheoryCore
    (d : ℕ) [NeZero d] : Prop :=
  CubeKBesovOverlappingEquivalence (cubeKBesovNormModel d) ∧
    CubeKBesovPartialBoundByOverlappingPositive d

theorem CubeKBesovCanonicalOverlappingTheoryCore.to_canonicalOverlappingTheory
    {d : ℕ} [NeZero d]
    (hcore : CubeKBesovCanonicalOverlappingTheoryCore d) :
    CubeKBesovCanonicalOverlappingTheory d :=
  ⟨hcore.1,
    cubeKBesovInputBoundednessOfOverlappingHRegularity_of_partialBoundByOverlappingPositive
      hcore.2⟩

theorem cubeKBesovDirichletRegularity_of_components
    {d : ℕ}
    (hcomponents : CubeKBesovDirichletRegularityComponents d) :
    CubeKBesovDirichletRegularity (cubeKBesovNormModel d) := by
  rcases hcomponents with ⟨hbounded, hmean, hpointwise⟩
  rcases hmean with ⟨Cavg, hCavg_nonneg, hmean⟩
  rcases hpointwise with ⟨CK, hCK_nonneg, hpointwise⟩
  intro s hs_pos hs_lt
  refine ⟨Cavg + CK, add_nonneg hCavg_nonneg hCK_nonneg, ?_⟩
  intro Q h w hh hweak
  have hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N h) :=
    hbounded hs_pos hs_lt Q h hh
  have hCK_le : CK ≤ Cavg + CK := by
    linarith
  have hCavg_le : Cavg ≤ Cavg + CK := by
    linarith
  have hsemi_base :
      cubeKBesovVectorSeminormTwo Q s
          (fun x => w.toH1Function.grad x) ≤
        CK * cubeKBesovVectorSeminormTwo Q s h :=
    cubeKBesovVectorSeminormTwo_le_of_forall_kFunctional_le
      Q s CK (fun x => w.toH1Function.grad x) h hCK_nonneg hBdd
      fun j => hpointwise Q h w (Real.rpow (3 : ℝ) (-(j : ℝ))) hh.memLp hweak
  have hsemi_h_nonneg :
      0 ≤ cubeKBesovVectorSeminormTwo Q s h :=
    cubeKBesovVectorSeminormTwo_nonneg_of_bddAbove Q s h hBdd
  have hsemi :
      cubeKBesovVectorSeminormTwo Q s
          (fun x => w.toH1Function.grad x) ≤
        (Cavg + CK) * cubeKBesovVectorSeminormTwo Q s h :=
    hsemi_base.trans
      (mul_le_mul_of_nonneg_right hCK_le hsemi_h_nonneg)
  have havg_base :
      Real.sqrt
          (vecNormSq
            (cubeAverageVec Q fun x => w.toH1Function.grad x)) ≤
        Cavg * Real.sqrt (vecNormSq (cubeAverageVec Q h)) :=
    hmean Q h w hweak
  have havg_h_nonneg :
      0 ≤ Real.sqrt (vecNormSq (cubeAverageVec Q h)) :=
    Real.sqrt_nonneg _
  have havg :
      Real.sqrt
          (vecNormSq
            (cubeAverageVec Q fun x => w.toH1Function.grad x)) ≤
        (Cavg + CK) * Real.sqrt (vecNormSq (cubeAverageVec Q h)) :=
    havg_base.trans
      (mul_le_mul_of_nonneg_right hCavg_le havg_h_nonneg)
  simpa [cubeKBesovNormModel] using
    cubeKBesovVectorNormTwo_le_of_average_and_seminorm
      Q s (Cavg + CK) (fun x => w.toH1Function.grad x) h havg hsemi

/-- Uniform-in-`s` version of the PDE/K-functional regularity assembled from
the same three focused components. -/
theorem exists_cubeKBesovDirichletRegularityUniform_of_components
    {d : ℕ}
    (hcomponents : CubeKBesovDirichletRegularityComponents d) :
    ∃ C : ℝ, CubeKBesovDirichletRegularityUniform (cubeKBesovNormModel d) C := by
  rcases hcomponents with ⟨hbounded, hmean, hpointwise⟩
  rcases hmean with ⟨Cavg, hCavg_nonneg, hmean⟩
  rcases hpointwise with ⟨CK, hCK_nonneg, hpointwise⟩
  refine ⟨Cavg + CK, add_nonneg hCavg_nonneg hCK_nonneg, ?_⟩
  intro s hs_pos hs_lt Q h w hh hweak
  have hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N h) :=
    hbounded hs_pos hs_lt Q h hh
  have hCK_le : CK ≤ Cavg + CK := by
    linarith
  have hCavg_le : Cavg ≤ Cavg + CK := by
    linarith
  have hsemi_base :
      cubeKBesovVectorSeminormTwo Q s
          (fun x => w.toH1Function.grad x) ≤
        CK * cubeKBesovVectorSeminormTwo Q s h :=
    cubeKBesovVectorSeminormTwo_le_of_forall_kFunctional_le
      Q s CK (fun x => w.toH1Function.grad x) h hCK_nonneg hBdd
      fun j => hpointwise Q h w (Real.rpow (3 : ℝ) (-(j : ℝ))) hh.memLp hweak
  have hsemi_h_nonneg :
      0 ≤ cubeKBesovVectorSeminormTwo Q s h :=
    cubeKBesovVectorSeminormTwo_nonneg_of_bddAbove Q s h hBdd
  have hsemi :
      cubeKBesovVectorSeminormTwo Q s
          (fun x => w.toH1Function.grad x) ≤
        (Cavg + CK) * cubeKBesovVectorSeminormTwo Q s h :=
    hsemi_base.trans
      (mul_le_mul_of_nonneg_right hCK_le hsemi_h_nonneg)
  have havg_base :
      Real.sqrt
          (vecNormSq
            (cubeAverageVec Q fun x => w.toH1Function.grad x)) ≤
        Cavg * Real.sqrt (vecNormSq (cubeAverageVec Q h)) :=
    hmean Q h w hweak
  have havg_h_nonneg :
      0 ≤ Real.sqrt (vecNormSq (cubeAverageVec Q h)) :=
    Real.sqrt_nonneg _
  have havg :
      Real.sqrt
          (vecNormSq
            (cubeAverageVec Q fun x => w.toH1Function.grad x)) ≤
        (Cavg + CK) * Real.sqrt (vecNormSq (cubeAverageVec Q h)) :=
    havg_base.trans
      (mul_le_mul_of_nonneg_right hCavg_le havg_h_nonneg)
  simpa [cubeKBesovNormModel] using
    cubeKBesovVectorNormTwo_le_of_average_and_seminorm
      Q s (Cavg + CK) (fun x => w.toH1Function.grad x) h havg hsemi

/-- Discrete compatibility K-functional route: one pure norm-equivalence input
and one PDE/K-functional regularity input.  This is not the source theorem
pending the continuum `K`/`H^s` gate. -/
def DiscreteConstantCoefficientDirichletBesovKFunctionalRoute
    (d : ℕ) [NeZero d] : Prop :=
  CubeKBesovOverlappingEquivalence (cubeKBesovNormModel d) ∧
    CubeKBesovDirichletRegularity (cubeKBesovNormModel d)

/-- Discrete compatibility statement obtained from the finite-level
K-functional/overlap machinery.  It is not the source theorem
`l.constant.coefficient.Dirichlet.Besov.function.spaces` pending the continuum
`K`/`H^s` gate. -/
def DiscreteConstantCoefficientDirichletBesovFunctionSpaces
    (d : ℕ) [NeZero d] : Prop :=
  ∀ {s : ℝ}, 0 < s → s < 1 →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : TriadicCube d) (h : Vec d → Vec d)
        (w : H10Function (openCubeSet Q)),
        CubeVectorOverlappingBesovHRegularity Q s h →
        CubeDirichletDivergenceProblem Q w h →
          cubeBesovOverlappingPositiveVectorNormTwo Q s
              (fun x => w.toH1Function.grad x) ≤
            C * cubeBesovOverlappingPositiveVectorNormTwo Q s h

/-- Uniform-in-`s` discrete compatibility strengthening of
`DiscreteConstantCoefficientDirichletBesovFunctionSpaces`, used by the
compatibility duality route.  It is not the source theorem pending the
continuum `K`/`H^s` gate. -/
def DiscreteConstantCoefficientDirichletBesovFunctionSpacesUniform
    (d : ℕ) [NeZero d] (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ {s : ℝ}, 0 < s → s < 1 →
      ∀ (Q : TriadicCube d) (h : Vec d → Vec d)
        (w : H10Function (openCubeSet Q)),
        CubeVectorOverlappingBesovHRegularity Q s h →
        CubeDirichletDivergenceProblem Q w h →
          CubeVectorOverlappingBesovHRegularity Q s
              (fun x => w.toH1Function.grad x) ∧
            cubeBesovOverlappingPositiveVectorNormTwo Q s
                (fun x => w.toH1Function.grad x) ≤
              C * cubeBesovOverlappingPositiveVectorNormTwo Q s h

theorem DiscreteConstantCoefficientDirichletBesovFunctionSpacesUniform.to_functionSpaces
    {d : ℕ} [NeZero d] {C : ℝ}
    (h : DiscreteConstantCoefficientDirichletBesovFunctionSpacesUniform d C) :
    DiscreteConstantCoefficientDirichletBesovFunctionSpaces d := by
  intro s hs_pos hs_lt
  refine ⟨C, h.1, ?_⟩
  intro Q F w hF hw
  exact (h.2 hs_pos hs_lt Q F w hF hw).2

/-- Assemble the discrete compatibility Dirichlet Besov statement from the
discrete K-functional route. -/
theorem discreteConstantCoefficientDirichletBesovFunctionSpaces_of_discreteKFunctionalRoute
    {d : ℕ} [NeZero d]
    (hroute : DiscreteConstantCoefficientDirichletBesovKFunctionalRoute d) :
    DiscreteConstantCoefficientDirichletBesovFunctionSpaces d := by
  intro s hs_pos hs_lt
  let K : CubeKBesovNormModel d := cubeKBesovNormModel d
  rcases hroute with ⟨hK_equiv, hK_dir⟩
  rcases hK_equiv hs_pos hs_lt with ⟨Ce, hCe_nonneg, hCe⟩
  rcases hK_dir hs_pos hs_lt with ⟨Cd, hCd_nonneg, hCd⟩
  refine ⟨Ce * Cd * Ce, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg hCe_nonneg hCd_nonneg) hCe_nonneg
  · intro Q h w hh hweak
    have hout :
        cubeBesovOverlappingPositiveVectorNormTwo Q s
            (fun x => w.toH1Function.grad x) ≤
          Ce * K Q s (fun x => w.toH1Function.grad x) :=
      (hCe Q (fun x => w.toH1Function.grad x)).1
    have hdir :
        K Q s (fun x => w.toH1Function.grad x) ≤ Cd * K Q s h :=
      hCd Q h w hh hweak
    have hin :
        K Q s h ≤ Ce * cubeBesovOverlappingPositiveVectorNormTwo Q s h :=
      (hCe Q h).2
    calc
      cubeBesovOverlappingPositiveVectorNormTwo Q s
          (fun x => w.toH1Function.grad x)
          ≤ Ce * K Q s (fun x => w.toH1Function.grad x) := hout
      _ ≤ Ce * (Cd * K Q s h) :=
          mul_le_mul_of_nonneg_left hdir hCe_nonneg
      _ = (Ce * Cd) * K Q s h := by ring
      _ ≤ (Ce * Cd) * (Ce * cubeBesovOverlappingPositiveVectorNormTwo Q s h) :=
          mul_le_mul_of_nonneg_left hin (mul_nonneg hCe_nonneg hCd_nonneg)
      _ = Ce * Cd * Ce * cubeBesovOverlappingPositiveVectorNormTwo Q s h := by ring

/-- Direct uniform assembly of the discrete compatibility Dirichlet Besov
statement from the uniform finite-partial K/overlapping comparison.  This is
not the source theorem pending the continuum `K`/`H^s` gate. -/
theorem exists_discreteConstantCoefficientDirichletBesovFunctionSpacesUniform_of_partialBoundByOverlappingPositiveUniform
    {d : ℕ} [NeZero d] {Cpartial : ℝ}
    (hpartial : CubeKBesovPartialBoundByOverlappingPositiveUniform d Cpartial)
    (hcomponents : CubeKBesovDirichletRegularityComponents d) :
    ∃ C : ℝ, DiscreteConstantCoefficientDirichletBesovFunctionSpacesUniform d C := by
  let CP : ℝ := cubeVectorH1OverlapPoincareConstant d
  let Coverlap : ℝ := 8 * (3 ^ d : ℝ) + 2 * CP ^ 2 + 2
  let Cin : ℝ := Cpartial + 1
  have hcomponents' := hcomponents
  rcases exists_cubeKBesovDirichletRegularityUniform_of_components hcomponents with
    ⟨Cd, hCd⟩
  rcases hcomponents' with ⟨hbounded, _hmean, hpointwise_component⟩
  rcases hpointwise_component with ⟨CK, hCK_nonneg, hpointwise⟩
  have hCP_nonneg : 0 ≤ CP := by
    dsimp [CP]
    exact cubeVectorH1OverlapPoincareConstant_nonneg d
  have hCoverlap_nonneg : 0 ≤ Coverlap := by
    dsimp [Coverlap, CP]
    positivity
  have hCin_nonneg : 0 ≤ Cin := by
    dsimp [Cin]
    exact add_nonneg hpartial.1 zero_le_one
  refine ⟨Coverlap * Cd * Cin,
    mul_nonneg (mul_nonneg hCoverlap_nonneg hCd.1) hCin_nonneg, ?_⟩
  intro s hs_pos hs_lt Q h w hh hweak
  have hInKBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N h) :=
    hbounded hs_pos hs_lt Q h hh
  have hOutKBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N
          (fun x => w.toH1Function.grad x)) := by
    rcases hInKBdd with ⟨B, hB⟩
    refine ⟨CK * B, ?_⟩
    rintro y ⟨N, rfl⟩
    have hpartialOut :
        cubeKBesovVectorPartialSeminormTwo Q s N
            (fun x => w.toH1Function.grad x) ≤
          CK * cubeKBesovVectorPartialSeminormTwo Q s N h :=
      cubeKBesovVectorPartialSeminormTwo_le_of_forall_kFunctional_le
        Q s CK N (fun x => w.toH1Function.grad x) h hCK_nonneg
        fun j _hj =>
          hpointwise Q h w (Real.rpow (3 : ℝ) (-(j : ℝ))) hh.memLp hweak
    exact hpartialOut.trans
      (mul_le_mul_of_nonneg_left (hB ⟨N, rfl⟩) hCK_nonneg)
  have hOutMem :
      MeasureTheory.MemLp (fun x => w.toH1Function.grad x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    apply MeasureTheory.MemLp.of_eval
    intro i
    simpa using w.toH1Function.grad_memL2_normalizedCubeMeasure (Q := Q) i
  have hOutReg :
      CubeVectorOverlappingBesovHRegularity Q s
          (fun x => w.toH1Function.grad x) :=
    cubeVectorOverlappingBesovHRegularity_of_memLp_of_kPartial_bddAbove
      hCP_nonneg (cubeVectorH1OverlapPoincareEstimate d)
      Q s (fun x => w.toH1Function.grad x) hOutMem hOutKBdd
  have hOutOverlapK :
      cubeBesovOverlappingPositiveVectorNormTwo Q s
          (fun x => w.toH1Function.grad x) ≤
        Coverlap *
          cubeKBesovVectorNormTwo Q s (fun x => w.toH1Function.grad x) := by
    dsimp [Coverlap, CP]
    exact
      cubeBesovOverlappingPositiveVectorNormTwo_le_mul_cubeKBesovVectorNormTwo_of_overlapPoincare
        hCP_nonneg (cubeVectorH1OverlapPoincareEstimate d)
        Q s (fun x => w.toH1Function.grad x) hOutMem hOutKBdd
  have hDir :
      cubeKBesovVectorNormTwo Q s (fun x => w.toH1Function.grad x) ≤
        Cd * cubeKBesovVectorNormTwo Q s h :=
    hCd.2 hs_pos hs_lt Q h w hh hweak
  have hInKOverlap :
      cubeKBesovVectorNormTwo Q s h ≤
        Cin * cubeBesovOverlappingPositiveVectorNormTwo Q s h :=
    cubeKBesovVectorNormTwo_le_mul_cubeBesovOverlappingPositiveVectorNormTwo_of_partialBoundUniform
      hpartial hs_pos hs_lt Q h hh
  refine ⟨hOutReg, ?_⟩
  calc
    cubeBesovOverlappingPositiveVectorNormTwo Q s
        (fun x => w.toH1Function.grad x)
        ≤
          Coverlap *
            cubeKBesovVectorNormTwo Q s (fun x => w.toH1Function.grad x) :=
      hOutOverlapK
    _ ≤ Coverlap * (Cd * cubeKBesovVectorNormTwo Q s h) :=
      mul_le_mul_of_nonneg_left hDir hCoverlap_nonneg
    _ = (Coverlap * Cd) * cubeKBesovVectorNormTwo Q s h := by
      ring
    _ ≤ (Coverlap * Cd) *
          (Cin * cubeBesovOverlappingPositiveVectorNormTwo Q s h) :=
      mul_le_mul_of_nonneg_left hInKOverlap
        (mul_nonneg hCoverlap_nonneg hCd.1)
    _ =
        Coverlap * Cd * Cin *
          cubeBesovOverlappingPositiveVectorNormTwo Q s h := by
      ring


end

end Homogenization
