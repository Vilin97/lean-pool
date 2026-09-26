/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.Triangle
public import LeanPool.CoarseGraining.Homogenization.HighContrast.EntryScale.MomentConsequences.P2

/-! # P1 -/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open scoped Matrix.Norms.Elementwise
open scoped MatrixOrder


/-!
# Bad maximal observable

This file isolates the manuscript bad-event maximal slot from the scalar
post-split bound used in the no-drop response estimate.
-/


namespace Homogenization.HighContrast.EntryScale

noncomputable section

/-- Threshold a nonnegative maximal observable to the bad event `{1 < M}`. -/
noncomputable def badEventTruncation {Ω : Type*} (M : Ω → ℝ) : Ω → ℝ :=
  fun ω => if 1 < M ω then M ω else 0

/-- Nonnegativity of the bad-event truncation for a nonnegative observable. -/
theorem badEventTruncation_nonneg
    {Ω : Type*} {M : Ω → ℝ} {ω : Ω}
    (hM_nonneg : 0 ≤ M ω) :
    0 ≤ badEventTruncation M ω := by
  by_cases hbad : 1 < M ω
  · simp only [badEventTruncation, hbad, ↓reduceIte, hM_nonneg]
  · simp only [badEventTruncation, hbad, ↓reduceIte, le_refl]

/-- The bad-event truncation is bounded by the original nonnegative observable. -/
theorem badEventTruncation_le_self_of_nonneg
    {Ω : Type*} {M : Ω → ℝ} {ω : Ω}
    (hM_nonneg : 0 ≤ M ω) :
    badEventTruncation M ω ≤ M ω := by
  by_cases hbad : 1 < M ω
  · simp only [badEventTruncation, hbad, ↓reduceIte, le_refl]
  · simp only [badEventTruncation, hbad, ↓reduceIte, hM_nonneg]

/--
Sharp good/bad split of a nonnegative maximal observable: on the good event
`{M <= 1}` the observable equals `min M 1`, and on the bad event `{1 < M}` it
is paid by the bad-event truncation at first power (with the harmless extra
`min M 1 = 1`).  This is the first-power replacement for the crude split
`M <= 1 + badEventTruncation M`.
-/
theorem le_min_one_add_badEventTruncation
    {Ω : Type*} {M : Ω → ℝ} {ω : Ω} :
    M ω ≤ min (M ω) 1 + badEventTruncation M ω := by
  by_cases hbad : 1 < M ω
  · have hmin : min (M ω) 1 = 1 := min_eq_right hbad.le
    simp only [hmin, badEventTruncation, hbad, ↓reduceIte, le_add_iff_nonneg_left, zero_le_one]
  · have hle : M ω ≤ 1 := le_of_not_gt hbad
    have hmin : min (M ω) 1 = M ω := min_eq_left hle
    simp only [hmin, badEventTruncation, hbad, ↓reduceIte, add_zero, le_refl]

/--
First-power good/bad split of a nonnegative maximal factor against a
nonnegative response: `M * J` is paid by `min M 1 * J` on the good event and
by `badEventTruncation M * J` on the bad event.  No squaring and no
deterministic cap on `J` is introduced.
-/
theorem maximal_mul_le_min_one_mul_add_badEventTruncation_mul
    {Ω : Type*} {M : Ω → ℝ} {ω : Ω} {J : ℝ}
    (hJ_nonneg : 0 ≤ J) :
    M ω * J ≤ min (M ω) 1 * J + badEventTruncation M ω * J := by
  have hsplit : M ω ≤ min (M ω) 1 + badEventTruncation M ω :=
    le_min_one_add_badEventTruncation
  calc
    M ω * J ≤ (min (M ω) 1 + badEventTruncation M ω) * J :=
      mul_le_mul_of_nonneg_right hsplit hJ_nonneg
    _ = min (M ω) 1 * J + badEventTruncation M ω * J := by ring

/-- The bad-event truncation of an a.e. strongly measurable observable is a.e. strongly measurable. -/
theorem aestronglyMeasurable_badEventTruncation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {M : Ω → ℝ}
    (hM : AEStronglyMeasurable M μ) :
    AEStronglyMeasurable (badEventTruncation M) μ := by
  classical
  have hset : NullMeasurableSet {ω | 1 < M ω} μ :=
    aestronglyMeasurable_const.nullMeasurableSet_lt hM
  simpa only [badEventTruncation, Set.indicator_apply, Set.mem_ofPred_eq] using!
    hM.indicator₀ hset

/--
The deterministic weighted drift supremum in the manuscript split of
`\mathcal M_m`.
-/
noncomputable def terminalBadMaximalDriftSup
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) {N m : ℕ} (hNm : N ≤ m) : ℝ :=
  (Finset.Icc N m).sup'
    ⟨N, Finset.mem_Icc.mpr ⟨le_rfl, hNm⟩⟩
    (fun j =>
      (3 : ℝ) ^ (-(hc.rhoM * ((m - j : ℕ) : ℝ))) *
        terminalAnnealedFullBlockDriftAtScales hP hStruct j m)

/--
The stochastic/subthreshold/deterministic random envelope that appears after
the manuscript positive-part split.  This is not the source observable itself;
it is the pointwise upper envelope whose square is later integrated.
-/
noncomputable def terminalBadMaximalSplitEnvelope
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) {N m : ℕ} (hNm : N ≤ m)
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) (M_sub : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω =>
    terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω +
      |M_sub m ω| +
      terminalBadMaximalDriftSup hP hStruct hc hNm

theorem terminalCoarseBlockStochasticMax_nonneg
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) (N m : ℕ)
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) :
    ∀ ω, 0 ≤ terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω := by
  intro ω
  dsimp [terminalCoarseBlockStochasticMax, terminalCoarseBlockStochasticMaxOfWeak]
  exact ENNReal.toReal_nonneg

theorem terminalBadMaximalDriftSup_nonneg
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) {N m : ℕ} (hNm : N ≤ m) :
    0 ≤ terminalBadMaximalDriftSup hP hStruct hc hNm := by
  classical
  let f : ℕ → ℝ := fun j =>
    (3 : ℝ) ^ (-(hc.rhoM * ((m - j : ℕ) : ℝ))) *
      terminalAnnealedFullBlockDriftAtScales hP hStruct j m
  have hNmem : N ∈ Finset.Icc N m := Finset.mem_Icc.mpr ⟨le_rfl, hNm⟩
  have hterm_nonneg : 0 ≤ f N := by
    dsimp [f]
    exact mul_nonneg
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
        (-(hc.rhoM * ((m - N : ℕ) : ℝ)))))
      (terminalAnnealedFullBlockDriftAtScales_nonneg hP hStruct N m)
  have hle : f N ≤ (Finset.Icc N m).sup' ⟨N, hNmem⟩ f :=
    Finset.le_sup' (s := Finset.Icc N m) (f := f) hNmem
  exact hterm_nonneg.trans hle

/--
Any scale term in the deterministic drift split is selected by the drift
supremum over the high-scale window.
-/
theorem weighted_terminalAnnealedFullBlockDriftAtScales_le_terminalBadMaximalDriftSup
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) {N m j : ℕ} (hNm : N ≤ m)
    (hj : j ∈ Finset.Icc N m) :
    (3 : ℝ) ^ (-(hc.rhoM * ((m - j : ℕ) : ℝ))) *
        terminalAnnealedFullBlockDriftAtScales hP hStruct j m ≤
      terminalBadMaximalDriftSup hP hStruct hc hNm := by
  classical
  let f : ℕ → ℝ := fun i =>
    (3 : ℝ) ^ (-(hc.rhoM * ((m - i : ℕ) : ℝ))) *
      terminalAnnealedFullBlockDriftAtScales hP hStruct i m
  have hNmem : N ∈ Finset.Icc N m := Finset.mem_Icc.mpr ⟨le_rfl, hNm⟩
  have hle : f j ≤ (Finset.Icc N m).sup' ⟨N, hNmem⟩ f :=
    Finset.le_sup' (s := Finset.Icc N m) (f := f) hj
  simpa only [terminalBadMaximalDriftSup, Finset.le_sup'_iff, Finset.mem_Icc] using hle

theorem fullBlockOperatorNorm_add_le {d : ℕ}
    (A B : Homogenization.FullBlockMat d) :
    fullBlockOperatorNorm (A + B) ≤
      fullBlockOperatorNorm A + fullBlockOperatorNorm B := by
  calc
    fullBlockOperatorNorm (A + B)
        = ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
            (𝕜 := ℝ) (A + B)‖ := rfl
    _ = ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
            (𝕜 := ℝ) A +
          Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
            (𝕜 := ℝ) B‖ := by
        rw [map_add]
    _ ≤ ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
            (𝕜 := ℝ) A‖ +
          ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
            (𝕜 := ℝ) B‖ :=
        norm_add_le _ _
    _ = fullBlockOperatorNorm A + fullBlockOperatorNorm B := rfl

section L2OperatorNorm

open scoped Matrix.Norms.L2Operator

open ContinuousFunctionalCalculus

/-- Negation is isometric for the L2 operator norm on square matrices.  Stated
via `Matrix.cstar_norm_def` (bundling through `toEuclideanCLM`) rather than the
generic `norm_neg`, because this file has both `Matrix.Norms.Elementwise` and
`Matrix.Norms.L2Operator` open and a bare typeclass-inferred norm lemma can
resolve against the wrong scoped instance. -/
private lemma l2OpMatrixNormNeg
    {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ) :
    ‖(-B : Matrix n n ℝ)‖ = ‖B‖ := by
  rw [Matrix.cstar_norm_def, Matrix.cstar_norm_def, map_neg, norm_neg]

private lemma Matrix.IsHermitian.isometry_cfcAux_l2
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : Matrix.IsHermitian A) :
    Isometry hA.cfcAux := by
  rw [isometry_iff_dist_eq]
  intro f g
  let u : C(spectrum ℝ A, ℝ) := f - g
  have hnorm : ‖hA.cfcAux u‖ = ‖u‖ := by
    let eigVals : n → ℝ := fun i =>
      u ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩
    let D : Matrix n n ℝ := Matrix.diagonal eigVals
    have hunit :
        ‖((Unitary.conjStarAlgAut ℝ (Matrix n n ℝ)) hA.eigenvectorUnitary) D‖ = ‖D‖ := by
      calc
        ‖((Unitary.conjStarAlgAut ℝ (Matrix n n ℝ)) hA.eigenvectorUnitary) D‖ =
            ‖(hA.eigenvectorUnitary : Matrix n n ℝ) * D *
              star (hA.eigenvectorUnitary : Matrix n n ℝ)‖ := by
              simp only [Unitary.conjStarAlgAut_apply]
        _ = ‖D * star (hA.eigenvectorUnitary : Matrix n n ℝ)‖ := by
              rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
        _ = ‖D * (star hA.eigenvectorUnitary : unitary (Matrix n n ℝ))‖ := by
              simp only [Unitary.coe_star]
        _ = ‖D‖ := by
              rw [CStarRing.norm_mul_coe_unitary]
    have hfiniteSup : ‖eigVals‖ = ‖u‖ := by
      apply le_antisymm
      · rw [pi_norm_le_iff_of_nonneg (norm_nonneg u)]
        intro i
        simpa only [Real.norm_eq_abs] using
          ContinuousMap.norm_coe_le_norm u
            (⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩ :
              spectrum ℝ A)
      · rw [ContinuousMap.norm_le u (norm_nonneg _)]
        intro x
        rcases x with ⟨x, hx⟩
        obtain ⟨i, hi⟩ : ∃ i, hA.eigenvalues i = x := by
          simpa only [hA.spectrum_real_eq_range_eigenvalues, Set.mem_range] using hx
        subst x
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm eigVals i
    rw [Matrix.IsHermitian.cfcAux_apply]
    simpa only [RCLike.ofReal_real_eq_id, CompTriple.comp_eq, Unitary.conjStarAlgAut_apply,
      Function.comp_def] using!
      (calc
        ‖((Unitary.conjStarAlgAut ℝ (Matrix n n ℝ)) hA.eigenvectorUnitary) D‖ =
            ‖D‖ := hunit
        _ = ‖eigVals‖ := by
              change ‖Matrix.diagonal eigVals‖ = ‖eigVals‖
              rw [Matrix.l2_opNorm_diagonal]
        _ = ‖u‖ := hfiniteSup)
  calc
    dist (hA.cfcAux f) (hA.cfcAux g) =
        ‖hA.cfcAux f - hA.cfcAux g‖ := by
          rw [Matrix.instL2OpNormedRing.dist_eq]
          have hstep : -hA.cfcAux f + hA.cfcAux g = -(hA.cfcAux f - hA.cfcAux g) := by abel
          rw [hstep, l2OpMatrixNormNeg]
    _ = ‖hA.cfcAux (f - g)‖ := by rw [map_sub]
    _ = ‖f - g‖ := by simpa only [Matrix.IsHermitian.cfcAux_apply, RCLike.ofReal_real_eq_id, ContinuousMap.coe_sub, CompTriple.comp_eq, Unitary.conjStarAlgAut_apply, u] using hnorm
    _ = dist f g := (dist_eq_norm _ _).symm

private noncomputable local instance fullBlockMat_isometricContinuousFunctionalCalculus
    {d : ℕ} :
    IsometricContinuousFunctionalCalculus ℝ (Homogenization.FullBlockMat d) IsSelfAdjoint where
  isometric M hM := by
    have hHerm : Matrix.IsHermitian M := hM
    have hcfc :
        cfcHom hM = hHerm.cfcAux :=
      cfcHom_eq_of_continuous_of_map_id hM hHerm.cfcAux
        hHerm.isClosedEmbedding_cfcAux.continuous hHerm.cfcAux_id
    simpa only [hcfc] using Matrix.IsHermitian.isometry_cfcAux_l2 hHerm

/--
The operator norm of the C-star positive part is bounded by the operator norm
of the original full-block matrix.

This is the local analytic bridge behind the manuscript step
`|(X)_+| ≤ |X|`.  It is proved by diagonalizing self-adjoint matrices and
using unitary invariance of the C-star norm; non-self-adjoint matrices have
zero positive part by the Mathlib definition.
-/
theorem fullBlockOperatorNorm_posPart_le {d : ℕ}
    (M : Homogenization.FullBlockMat d) :
    fullBlockOperatorNorm (M⁺) ≤ fullBlockOperatorNorm M := by
  rw [fullBlockOperatorNorm_eq_l2_opNorm, fullBlockOperatorNorm_eq_l2_opNorm]
  by_cases hsa : IsSelfAdjoint M
  · classical
    let hHerm : M.IsHermitian := hsa
    let Dpos : Homogenization.FullBlockMat d :=
      Matrix.diagonal (fun i : Homogenization.BlockCoord d => (hHerm.eigenvalues i)⁺)
    let D : Homogenization.FullBlockMat d :=
      Matrix.diagonal hHerm.eigenvalues
    have hpos_eq :
        M⁺ =
          Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary Dpos := by
      dsimp [Dpos]
      rw [CFC.posPart_def]
      rw [cfcₙ_eq_cfc]
      rw [Matrix.IsHermitian.cfc_eq]
      rfl
    have hM_eq :
        M = Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D := by
      simpa only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, CompTriple.comp_eq] using hHerm.spectral_theorem
    have hunit_pos :
        ‖Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary Dpos‖ =
          ‖Dpos‖ := by
      calc
        ‖Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary Dpos‖ =
            ‖(hHerm.eigenvectorUnitary : Homogenization.FullBlockMat d) * Dpos *
              star (hHerm.eigenvectorUnitary : Homogenization.FullBlockMat d)‖ := by
              simp only [Unitary.conjStarAlgAut_apply]
        _ = ‖Dpos * star (hHerm.eigenvectorUnitary : Homogenization.FullBlockMat d)‖ := by
              rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
        _ = ‖Dpos * (star hHerm.eigenvectorUnitary :
              unitary (Homogenization.FullBlockMat d))‖ := by
              simp only [Unitary.coe_star]
        _ = ‖Dpos‖ := by
              rw [CStarRing.norm_mul_coe_unitary]
    have hunit :
        ‖Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D‖ =
          ‖D‖ := by
      calc
        ‖Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D‖ =
            ‖(hHerm.eigenvectorUnitary : Homogenization.FullBlockMat d) * D *
              star (hHerm.eigenvectorUnitary : Homogenization.FullBlockMat d)‖ := by
              simp only [Unitary.conjStarAlgAut_apply]
        _ = ‖D * star (hHerm.eigenvectorUnitary : Homogenization.FullBlockMat d)‖ := by
              rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
        _ = ‖D * (star hHerm.eigenvectorUnitary :
              unitary (Homogenization.FullBlockMat d))‖ := by
              simp only [Unitary.coe_star]
        _ = ‖D‖ := by
              rw [CStarRing.norm_mul_coe_unitary]
    have hdiag_le : ‖Dpos‖ ≤ ‖D‖ := by
      have heig_le :
          ‖(fun i : Homogenization.BlockCoord d => (hHerm.eigenvalues i)⁺)‖ ≤
            ‖hHerm.eigenvalues‖ := by
        rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
        intro i
        have hreal : ‖(hHerm.eigenvalues i)⁺‖ ≤ ‖hHerm.eigenvalues i‖ := by
          by_cases hx : 0 ≤ hHerm.eigenvalues i
          · rw [posPart_eq_self.mpr hx]
          · have hxle : hHerm.eigenvalues i ≤ 0 := le_of_not_ge hx
            rw [posPart_eq_zero.mpr hxle]
            simp only [norm_zero, Real.norm_eq_abs, abs_nonneg]
        exact hreal.trans (norm_le_pi_norm hHerm.eigenvalues i)
      calc
        ‖Dpos‖ =
            ‖(fun i : Homogenization.BlockCoord d => (hHerm.eigenvalues i)⁺)‖ := by
            simp only [Matrix.l2_opNorm_diagonal, Dpos]
        _ ≤ ‖hHerm.eigenvalues‖ := heig_le
        _ = ‖D‖ := by
            simp only [Matrix.l2_opNorm_diagonal, D]
    calc
      ‖M⁺‖ =
          ‖Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary Dpos‖ :=
            congrArg norm hpos_eq
      _ = ‖Dpos‖ := hunit_pos
      _ ≤ ‖D‖ := hdiag_le
      _ = ‖Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D‖ := hunit.symm
      _ = ‖M‖ := congrArg norm hM_eq.symm
  · rw [CFC.posPart_eq_zero_of_not_isSelfAdjoint hsa]
    rw [Matrix.cstar_norm_def]
    rw [Matrix.cstar_norm_def]
    simp only [map_zero, norm_zero, norm_nonneg]

private theorem measurable_fullBlockOperatorNorm_posPart {d : ℕ} :
    Measurable fun M : Homogenization.FullBlockMat d =>
      fullBlockOperatorNorm (M⁺) := by
  classical
  let selfAdjointSet : Set (Homogenization.FullBlockMat d) :=
    {M | IsSelfAdjoint M}
  have hself_closed : IsClosed selfAdjointSet := by
    have hstar : Continuous fun M : Homogenization.FullBlockMat d => star M := by
      fun_prop
    have hid : Continuous fun M : Homogenization.FullBlockMat d => M := continuous_id
    have hclosed : IsClosed {M : Homogenization.FullBlockMat d | star M = M} :=
      isClosed_eq hstar hid
    simpa only [selfAdjointSet, isSelfAdjoint_iff] using hclosed
  have hself_meas : MeasurableSet selfAdjointSet := hself_closed.measurableSet
  have hpos_cont :
      ContinuousOn (fun M : Homogenization.FullBlockMat d => M⁺) selfAdjointSet := by
    have hpos_cont_cfc :
        ContinuousOn
          (fun M : Homogenization.FullBlockMat d => cfcₙ (fun x : ℝ => x⁺) M)
          selfAdjointSet :=
      ContinuousOn.cfcₙ
        (f := fun x : ℝ => x⁺)
        (a := fun M : Homogenization.FullBlockMat d => M)
        (s := fun M : Homogenization.FullBlockMat d =>
          Metric.closedBall (0 : ℝ) (‖M‖ + 1))
        (t := selfAdjointSet)
        (hs := by
          intro M _hM
          exact isCompact_closedBall (0 : ℝ) (‖M‖ + 1))
        (ha_cont := continuous_id.continuousOn)
        (ha := by
          intro M _hM
          have hpos : 0 < (1 : ℝ) := by norm_num
          filter_upwards [inter_mem_nhdsWithin selfAdjointSet (Metric.ball_mem_nhds M hpos)]
            with M' hnear
          intro y hy
          have hdist_near : dist M' M < 1 := by
            simpa only [dist_comm, Metric.mem_ball] using hnear.2
          have hM'_norm : ‖M'‖ ≤ ‖M‖ + 1 := by
            have htri : ‖M'‖ ≤ dist M' M + ‖M‖ := by
              let distL2 :=
                @dist (Homogenization.FullBlockMat d) Matrix.instL2OpMetricSpace.toDist
              let normL2 :=
                @norm (Homogenization.FullBlockMat d) Matrix.instL2OpNormedRing.toNorm
              have htri_dist :
                  distL2 M' 0 ≤ distL2 M' M + distL2 M 0 :=
                @dist_triangle (Homogenization.FullBlockMat d)
                  Matrix.instL2OpMetricSpace.toPseudoMetricSpace M' M 0
              have hM'0 : distL2 M' 0 = normL2 M' := by
                change dist M' 0 = ‖M'‖
                rw [Matrix.instL2OpNormedRing.dist_eq, add_zero, l2OpMatrixNormNeg]
              have hM0 : distL2 M 0 = normL2 M := by
                change dist M 0 = ‖M‖
                rw [Matrix.instL2OpNormedRing.dist_eq, add_zero, l2OpMatrixNormNeg]
              simpa only [ge_iff_le, hM'0, hM0] using htri_dist
            linarith only [htri, hdist_near]
          have hM'_self : IsSelfAdjoint M' := by
            simpa only [Set.mem_ofPred_eq, selfAdjointSet] using hnear.1
          have hy_norm : ‖y‖ ≤ ‖M'‖ :=
            NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le
              (𝕜 := ℝ) (A := Homogenization.FullBlockMat d)
              (p := IsSelfAdjoint) M' hy hM'_self
          have hy_bound : ‖y‖ ≤ ‖M‖ + 1 := hy_norm.trans hM'_norm
          simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs, ge_iff_le] using hy_bound)
        (ha' := by
          intro M hM
          exact hM)
        (hf := by
          intro M _hM
          exact continuous_posPart.continuousOn)
        (hf0 := by simp only [posPart_zero])
    simpa only [CFC.posPart_def] using hpos_cont_cfc
  have hnorm_cont :
      Continuous fun M : Homogenization.FullBlockMat d =>
        fullBlockOperatorNorm M := by
    let L : Homogenization.FullBlockMat d →ₗ[ℝ]
        (EuclideanSpace ℝ (Homogenization.BlockCoord d) →L[ℝ]
          EuclideanSpace ℝ (Homogenization.BlockCoord d)) := {
      toFun := fun M =>
        Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ) M
      map_add' := by
        intro A B
        exact map_add
          (Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ)) A B
      map_smul' := by
        intro r A
        exact map_smul
          (Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ)) r A
    }
    have hcont : Continuous fun M : Homogenization.FullBlockMat d => ‖L M‖ :=
      L.continuous_of_finiteDimensional.norm
    simpa only [fullBlockOperatorNorm, L, LinearMap.coe_mk, AddHom.coe_mk] using hcont
  have hf_cont :
      ContinuousOn
        (fun M : Homogenization.FullBlockMat d => fullBlockOperatorNorm (M⁺))
        selfAdjointSet :=
    hnorm_cont.comp_continuousOn hpos_cont
  have hzero_cont :
      ContinuousOn (fun _ : Homogenization.FullBlockMat d => (0 : ℝ))
        selfAdjointSetᶜ :=
    continuous_const.continuousOn
  have hpw_meas :
      Measurable
        (selfAdjointSet.piecewise
          (fun M : Homogenization.FullBlockMat d => fullBlockOperatorNorm (M⁺))
          (fun _ : Homogenization.FullBlockMat d => (0 : ℝ))) :=
    hf_cont.measurable_piecewise hzero_cont hself_meas
  have hpw_eq :
      selfAdjointSet.piecewise
          (fun M : Homogenization.FullBlockMat d => fullBlockOperatorNorm (M⁺))
          (fun _ : Homogenization.FullBlockMat d => (0 : ℝ)) =
        (fun M : Homogenization.FullBlockMat d => fullBlockOperatorNorm (M⁺)) := by
    funext M
    by_cases hM : M ∈ selfAdjointSet
    · simp only [hM, Set.piecewise_eq_of_mem]
    · have hnot : ¬ IsSelfAdjoint M := by
        simpa only [Set.mem_ofPred_eq, selfAdjointSet] using hM
      simp only [fullBlockOperatorNorm, hM, not_false_eq_true, Set.piecewise_eq_of_notMem, CFC.posPart_eq_zero_of_not_isSelfAdjoint hnot, map_zero, norm_zero]
  simpa only [hpw_eq] using hpw_meas

end L2OperatorNorm

/--
The literal terminally-normalized spectral positive part on one block.

This uses the library's normalized full-block fluctuation matrix for
`Ahom_m^{-1/2} (bfA(Q) - Ahom_m) Ahom_m^{-1/2}` and mathlib's C-star
positive part `M⁺`.
-/
noncomputable def terminalSpectralPositivePartAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d) : ℝ :=
  fullBlockOperatorNorm
    ((Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
        hP hStruct (m : ℤ)
          (Homogenization.cubeSet Q) a)⁺)

theorem terminalSpectralPositivePartAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d) :
    0 ≤ terminalSpectralPositivePartAtScale hP hStruct m Q a := by
  dsimp [terminalSpectralPositivePartAtScale]
  exact fullBlockOperatorNorm_nonneg _

theorem aemeasurable_terminalFullBlockNormalizedFluctuationMatrixAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (m : ℕ) (Q : Homogenization.TriadicCube d) :
    AEMeasurable
      (fun a : Homogenization.RegCoeffField d =>
        Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
          hP hStruct (m : ℤ) (Homogenization.cubeSet Q) a) P :=
  Homogenization.Book.Ch05.Section56.aemeasurable_fullBlockNormalizedFluctuationMatrix_cubeSet
    hP hStruct (m : ℤ) Q

theorem aemeasurable_terminalSpectralPositivePartAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (m : ℕ) (Q : Homogenization.TriadicCube d) :
    AEMeasurable
      (fun a : Homogenization.RegCoeffField d =>
        terminalSpectralPositivePartAtScale hP hStruct m Q a) P := by
  exact
    (measurable_fullBlockOperatorNorm_posPart.comp_aemeasurable
      (aemeasurable_terminalFullBlockNormalizedFluctuationMatrixAtScale
        hP hStruct m Q)).congr (by
      filter_upwards with a
      rfl)

private theorem fullBlockQuadratic_le_fullBlockOperatorNorm_mul_dotProduct
    {d : ℕ} (M : Homogenization.FullBlockMat d)
    (x : Homogenization.FullBlockVec d) :
    Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic M x ≤
      fullBlockOperatorNorm M * dotProduct x x := by
  let X : PiLp 2 (fun _ : Homogenization.BlockCoord d => ℝ) := WithLp.toLp 2 x
  let Y : PiLp 2 (fun _ : Homogenization.BlockCoord d => ℝ) :=
    WithLp.toLp 2 (Matrix.mulVec M x)
  have hY :
      (Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
          (𝕜 := ℝ) M) X = Y := by
    simp only [Matrix.toEuclideanCLM_toLp, X, Y]
  have hinner :
      inner ℝ X Y =
        Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic M x := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm, Fintype.sum_sum_type, Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic, dotProduct, X, Y]
  have hnormY :
      ‖Y‖ ≤ fullBlockOperatorNorm M * ‖X‖ := by
    simpa only [fullBlockOperatorNorm, hY] using
      (Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
        (𝕜 := ℝ) M).le_opNorm X
  have hnormX_sq :
      ‖X‖ ^ 2 = dotProduct x x := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq, abs_mul_abs_self, Fintype.sum_sum_type, dotProduct, X]
  calc
    Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic M x
        ≤ |Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic M x| :=
          le_abs_self _
    _ = |inner ℝ X Y| := by rw [hinner]
    _ ≤ ‖X‖ * ‖Y‖ := abs_real_inner_le_norm X Y
    _ ≤ ‖X‖ * (fullBlockOperatorNorm M * ‖X‖) := by
          exact mul_le_mul_of_nonneg_left hnormY (norm_nonneg X)
    _ = fullBlockOperatorNorm M * dotProduct x x := by
          rw [← hnormX_sq]
          ring

private theorem fullBlockQuadratic_le_posPart_of_isSymm
    {d : ℕ} {M : Homogenization.FullBlockMat d}
    (hM : M.IsSymm) (x : Homogenization.FullBlockVec d) :
    Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic M x ≤
      Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic M⁺ x := by
  have hsa : IsSelfAdjoint M := Matrix.isHermitian_iff_isSymm.mpr hM
  let _ : PartialOrder (Homogenization.FullBlockMat d) := Matrix.instPartialOrder
  let _ : StarOrderedRing (Homogenization.FullBlockMat d) := Matrix.instStarOrderedRing
  have horder : M ≤ M⁺ := CFC.le_posPart (a := M) hsa
  have hdiff : (M⁺ - M).PosSemidef := Matrix.le_iff.mp horder
  have hdiff_quad :
      0 ≤
        Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic
          (M⁺ - M) x := by
    simpa only [Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic, star_trivial]
      using hdiff.dotProduct_mulVec_nonneg x
  have hsub :=
    Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic_sub
      M⁺ M x
  linarith only [hdiff_quad, hsub]

theorem fullBlockNormalizedQuadraticObservable_sub_dotProduct_le_terminalSpectralPositivePartAtScale_mul_dotProduct
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d)
    (hSymm : Homogenization.IsSymmetricBlockMat
      (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a))
    (q : Homogenization.FullBlockVec d) :
    Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedQuadraticObservable
        hP hStruct (m : ℤ) q (Homogenization.cubeSet Q) a -
      dotProduct q q ≤
        terminalSpectralPositivePartAtScale hP hStruct m Q a * dotProduct q q := by
  let M :=
    Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
      hP hStruct (m : ℤ) (Homogenization.cubeSet Q) a
  have hM_symm : M.IsSymm := by
    dsimp [M]
    exact
      Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix_isSymm_of_isSymmetricBlockMat
          hP hStruct (m : ℤ) hSymm
  have hcenter :
      Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedQuadraticObservable
          hP hStruct (m : ℤ) q (Homogenization.cubeSet Q) a -
        dotProduct q q =
          Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic M q := by
    dsimp [M]
    exact
      Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedQuadraticObservable_sub_dotProduct_eq_fluctuationQuadratic
          hP hStruct hP4 m q (Homogenization.cubeSet Q) a
  calc
    Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedQuadraticObservable
        hP hStruct (m : ℤ) q (Homogenization.cubeSet Q) a -
      dotProduct q q =
        Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic M q := hcenter
    _ ≤ Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic M⁺ q :=
        fullBlockQuadratic_le_posPart_of_isSymm hM_symm q
    _ ≤ fullBlockOperatorNorm M⁺ * dotProduct q q :=
        fullBlockQuadratic_le_fullBlockOperatorNorm_mul_dotProduct M⁺ q
    _ = terminalSpectralPositivePartAtScale hP hStruct m Q a * dotProduct q q := by
        rfl

theorem upperLeft_posSemidef_of_isSymmetricBlockMat_of_blockPosDef
    {d : ℕ} {A : Homogenization.BlockMat d}
    (hSymm : Homogenization.IsSymmetricBlockMat A)
    (hPos : Homogenization.Book.Ch02.BlockPosDef A) :
    A.upperLeft.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose, RCLike.star_def, Matrix.map_apply, Matrix.transpose_apply, conj_trivial]
    simpa only [Homogenization.blockMatEntry] using hSymm (Sum.inl j) (Sum.inl i)
  · intro x
    by_cases hx : x = 0
    · simp only [hx, star_trivial, Matrix.mulVec_zero, dotProduct_zero, le_refl]
    · have hX : ((x, 0) : Homogenization.BlockVec d) ≠ 0 := by
        intro hzero
        exact hx (congrArg Prod.fst hzero)
      have hquad := (hPos ((x, 0) : Homogenization.BlockVec d) hX).le
      simpa only [star_trivial, ge_iff_le, Homogenization.blockVecDot, Homogenization.blockMatVecMul, Homogenization.matVecMul_zero, add_zero, Homogenization.vecDot_zero_left]
        using! hquad

theorem lowerRight_posSemidef_of_isSymmetricBlockMat_of_blockPosDef
    {d : ℕ} {A : Homogenization.BlockMat d}
    (hSymm : Homogenization.IsSymmetricBlockMat A)
    (hPos : Homogenization.Book.Ch02.BlockPosDef A) :
    A.lowerRight.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose, RCLike.star_def, Matrix.map_apply, Matrix.transpose_apply, conj_trivial]
    simpa only [Homogenization.blockMatEntry] using hSymm (Sum.inr j) (Sum.inr i)
  · intro x
    by_cases hx : x = 0
    · simp only [hx, star_trivial, Matrix.mulVec_zero, dotProduct_zero, le_refl]
    · have hX : ((0, x) : Homogenization.BlockVec d) ≠ 0 := by
        intro hzero
        exact hx (congrArg Prod.snd hzero)
      have hquad := (hPos ((0, x) : Homogenization.BlockVec d) hX).le
      simpa only [star_trivial, ge_iff_le, Homogenization.blockVecDot, Homogenization.blockMatVecMul, Homogenization.matVecMul_zero, zero_add, Homogenization.vecDot_zero_left]
        using! hquad

theorem scalar_one_posSemidef_of_nonneg
    {d : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    (c • (1 : Homogenization.Mat d)).PosSemidef :=
  Matrix.PosSemidef.smul Matrix.PosSemidef.one hc

theorem vecDot_matVecMul_smul_one
    {d : ℕ} (c : ℝ) (x : Homogenization.Vec d) :
    Homogenization.vecDot x
        (Homogenization.matVecMul (c • (1 : Homogenization.Mat d)) x) =
      c * Homogenization.vecDot x x := by
  classical
  simp only [Homogenization.vecDot, Homogenization.matVecMul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, mul_comm, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_left_comm, Finset.mul_sum]

theorem coarseBlockMatrix_cubeSet_symm_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] (Q : Homogenization.TriadicCube d)
    {a : Homogenization.RegCoeffField d}
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) :
    Homogenization.IsSymmetricBlockMat
      (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a) := by
  let F : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hEq :
      Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a =
        Homogenization.Book.Ch02.coarseBlockMatrix
          (Homogenization.Book.Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa only using
      Homogenization.Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  rw [hEq]
  exact
    Homogenization.Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix
      (Homogenization.Book.Ch02.cubeDomain Q) (F.coeffOn Q)

theorem coarseBlockMatrix_cubeSet_blockPosDef_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] (Q : Homogenization.TriadicCube d)
    {a : Homogenization.RegCoeffField d}
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) :
    Homogenization.Book.Ch02.BlockPosDef
      (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a) := by
  let F : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hEq :
      Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a =
        Homogenization.Book.Ch02.coarseBlockMatrix
          (Homogenization.Book.Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa only using
      Homogenization.Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  rw [hEq]
  exact
    (Homogenization.Book.Ch02.blockCoarseMatrixTheory
      (Homogenization.Book.Ch02.cubeDomain Q) (F.coeffOn Q)).block_matrix_posDef

theorem fullBlockNormalizedQuadraticObservable_upperLift_eq
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d) (e : Homogenization.Vec d) :
    let b := hP.barSigmaAtScale hStruct (m : ℤ)
    let xu : Homogenization.FullBlockVec d :=
      Homogenization.toFullBlockVec ((Real.sqrt b) • e, 0)
    Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedQuadraticObservable
        hP hStruct (m : ℤ) xu (Homogenization.cubeSet Q) a =
      Homogenization.vecDot e
        (Homogenization.matVecMul
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).upperLeft e) := by
  classical
  dsimp only
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let D : Homogenization.FullBlockMat d :=
    Matrix.diagonal (Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag b c)
  let A := Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a
  let xu : Homogenization.FullBlockVec d :=
    Homogenization.toFullBlockVec ((Real.sqrt b) • e, 0)
  have hb : 0 < b := by
    simpa only using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
        hP hStruct hP4 m
  have hDxu :
      Matrix.mulVec D xu = Homogenization.toFullBlockVec (e, 0) := by
    funext α
    cases α with
    | inl i =>
        dsimp [D]
        rw [Matrix.mulVec_diagonal]
        simp only [Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag, Homogenization.toFullBlockVec, Pi.smul_apply, smul_eq_mul, b, xu]
        field_simp [ne_of_gt (Real.sqrt_pos.mpr (by simpa only [b] using hb))]
    | inr i =>
        dsimp [D]
        rw [Matrix.mulVec_diagonal]
        simp only [Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag, Homogenization.toFullBlockVec, Pi.zero_apply, mul_zero, xu]
  calc
    Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedQuadraticObservable
        hP hStruct (m : ℤ) xu (Homogenization.cubeSet Q) a =
        Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic
          (D * Homogenization.toFullBlockMat A * D) xu := by
          rfl
    _ =
        Homogenization.blockVecDot
          (Homogenization.ofFullBlockVec (Matrix.mulVec D xu))
          (Homogenization.blockMatVecMul A
            (Homogenization.ofFullBlockVec (Matrix.mulVec D xu))) := by
          exact
            Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot
                (Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag b c) A xu
    _ =
        Homogenization.blockVecDot (e, 0)
          (Homogenization.blockMatVecMul A (e, 0)) := by
          rw [hDxu]
          simp only [Homogenization.ofFullBlockVec_toFullBlockVec]
    _ =
        Homogenization.vecDot e
          (Homogenization.matVecMul
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).upperLeft e) := by
          simp only [Homogenization.blockVecDot, Homogenization.blockMatVecMul, Homogenization.matVecMul_zero, add_zero, Homogenization.vecDot_zero_left, A]

theorem fullBlockNormalizedQuadraticObservable_lowerLift_eq
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d) (e : Homogenization.Vec d) :
    let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
    let xl : Homogenization.FullBlockVec d :=
      Homogenization.toFullBlockVec (0, (Real.sqrt c)⁻¹ • e)
    Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedQuadraticObservable
        hP hStruct (m : ℤ) xl (Homogenization.cubeSet Q) a =
      Homogenization.vecDot e
        (Homogenization.matVecMul
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).lowerRight e) := by
  classical
  dsimp only
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let D : Homogenization.FullBlockMat d :=
    Matrix.diagonal (Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag b c)
  let A := Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a
  let xl : Homogenization.FullBlockVec d :=
    Homogenization.toFullBlockVec (0, (Real.sqrt c)⁻¹ • e)
  have hc : 0 < c := by
    simpa only using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
        hP hStruct hP4 m
  have hDxl :
      Matrix.mulVec D xl = Homogenization.toFullBlockVec (0, e) := by
    funext α
    cases α with
    | inl i =>
        dsimp [D]
        rw [Matrix.mulVec_diagonal]
        simp only [Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag, Homogenization.toFullBlockVec, Pi.zero_apply, mul_zero, xl]
    | inr i =>
        dsimp [D]
        rw [Matrix.mulVec_diagonal]
        simp only [Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag, Homogenization.toFullBlockVec, Pi.smul_apply, smul_eq_mul, c, xl]
        field_simp [ne_of_gt (Real.sqrt_pos.mpr (by simpa only [c] using hc))]
  calc
    Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedQuadraticObservable
        hP hStruct (m : ℤ) xl (Homogenization.cubeSet Q) a =
        Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic
          (D * Homogenization.toFullBlockMat A * D) xl := by
          rfl
    _ =
        Homogenization.blockVecDot
          (Homogenization.ofFullBlockVec (Matrix.mulVec D xl))
          (Homogenization.blockMatVecMul A
            (Homogenization.ofFullBlockVec (Matrix.mulVec D xl))) := by
          exact
            Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot
                (Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag b c) A xl
    _ =
        Homogenization.blockVecDot (0, e)
          (Homogenization.blockMatVecMul A (0, e)) := by
          rw [hDxl]
          simp only [Homogenization.ofFullBlockVec_toFullBlockVec]
    _ =
        Homogenization.vecDot e
          (Homogenization.matVecMul
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).lowerRight e) := by
          simp only [Homogenization.blockVecDot, Homogenization.blockMatVecMul, Homogenization.matVecMul_zero, zero_add, Homogenization.vecDot_zero_left, A]

theorem upperLift_dotProduct_eq
    {d : ℕ} {b : ℝ} (hb : 0 ≤ b) (e : Homogenization.Vec d) :
    dotProduct (Homogenization.toFullBlockVec ((Real.sqrt b) • e, 0))
        (Homogenization.toFullBlockVec ((Real.sqrt b) • e, 0)) =
      b * Homogenization.vecDot e e := by
  calc
    dotProduct (Homogenization.toFullBlockVec ((Real.sqrt b) • e, 0))
        (Homogenization.toFullBlockVec ((Real.sqrt b) • e, 0)) =
        Homogenization.blockVecDot ((Real.sqrt b) • e, 0) ((Real.sqrt b) • e, 0) := by
        exact Homogenization.dotProduct_toFullBlockVec _ _
    _ = Homogenization.vecNormSq ((Real.sqrt b) • e) := by
        simp only [Homogenization.blockVecDot, Homogenization.vecDot_zero_left, add_zero, Homogenization.vecNormSq]
    _ = b * Homogenization.vecDot e e := by
        rw [Homogenization.vecNormSq_smul, Real.sq_sqrt hb]
        simp only [Homogenization.vecNormSq]

theorem lowerLift_dotProduct_eq
    {d : ℕ} {c : ℝ} (hc : 0 ≤ c) (e : Homogenization.Vec d) :
    dotProduct (Homogenization.toFullBlockVec (0, (Real.sqrt c)⁻¹ • e))
        (Homogenization.toFullBlockVec (0, (Real.sqrt c)⁻¹ • e)) =
      c⁻¹ * Homogenization.vecDot e e := by
  calc
    dotProduct (Homogenization.toFullBlockVec (0, (Real.sqrt c)⁻¹ • e))
        (Homogenization.toFullBlockVec (0, (Real.sqrt c)⁻¹ • e)) =
        Homogenization.blockVecDot (0, (Real.sqrt c)⁻¹ • e)
          (0, (Real.sqrt c)⁻¹ • e) := by
        exact Homogenization.dotProduct_toFullBlockVec _ _
    _ = Homogenization.vecNormSq ((Real.sqrt c)⁻¹ • e) := by
        simp only [Homogenization.blockVecDot, Homogenization.vecDot_zero_left, zero_add, Homogenization.vecNormSq]
    _ = c⁻¹ * Homogenization.vecDot e e := by
        rw [Homogenization.vecNormSq_smul]
        have hsqrt_sq : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc
        rw [inv_pow, hsqrt_sq]
        simp only [Homogenization.vecNormSq]

end

end Homogenization.HighContrast.EntryScale
