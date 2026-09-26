/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.WeakFluxRHS.Selection.AveragedTail
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AbsorbedNoteApex

/-! # Weak Flux RHS -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Section 3.2.3: Weak flux estimate with right-hand side

This file assembles the public weak flux RHS theorem package from the selected
harmonic-remainder bridge layer and the deterministic absorbed apex.

## Audit tag

Claim: expose the single public weak-flux-with-RHS package after the
harmonic-remainder selection and deterministic absorbed apex have been
connected to the Book-facing data.

Downstream target: `InhomogeneousEquationsTheory`.  This file should not grow
parallel weak-flux `Theory` variants; missing inputs should be proved in the
selection or deterministic bridge layers.
-/

noncomputable section

theorem weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq_le_four_mul_add_of_decomposition_and_neumann_tail
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {s : ℝ} {g u : Vec d → Vec d}
    (v : TriadicCube d → Vec d → Vec d)
    (ω : (n : ℕ) → (R : TriadicCube d) → R ∈ descendantsAtDepth Q n →
      MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g))
    {BU Bω : ℝ}
    (hs : 0 < s)
    (hu_mem_desc :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n, MemVectorL2 (cubeSet R) u)
    (huBdd_desc :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N u))
    (hdecomp :
      ∀ n : ℕ, ∀ R : TriadicCube d, ∀ hR : R ∈ descendantsAtDepth Q n, ∀ x ∈ cubeSet R,
        u x =
          v R x + (ω n R hR).toH1MeanZero.toH1Function.grad x)
    (hu_tail : ∀ n : ℕ, coarsePoincareRHSSn Q s u n ≤ BU)
    (hω_tail :
      ∀ n : ℕ,
        coarsePoincareRHSDepthWeight s n *
          descendantsAverage Q n
            (fun R =>
              if hR : R ∈ descendantsAtDepth Q n then
                (cubeBesovNegativeVectorSeminormTwo R s
                  (fun x => (ω n R hR).toH1MeanZero.toH1Function.grad x)) ^ 2
              else 0) ≤ Bω) :
    ∀ n : ℕ,
      weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v n ≤
        4 * (BU + Bω) := by
  intro n
  let U : TriadicCube d → ℝ := fun R =>
    (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2
  let Ω : TriadicCube d → ℝ := fun R =>
    if hR : R ∈ descendantsAtDepth Q n then
      (cubeBesovNegativeVectorSeminormTwo R s
        (fun x => (ω n R hR).toH1MeanZero.toH1Function.grad x)) ^ 2
    else 0
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s (v R)) ^ 2 ≤
          4 * (U R + Ω R) := by
    intro R hR
    let ωR : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g) :=
      ω n R hR
    let ωgrad : Vec d → Vec d :=
      fun x => ωR.toH1MeanZero.toH1Function.grad x
    have hv_eq_sub :
        cubeBesovNegativeVectorSeminormTwo R s (v R) =
          cubeBesovNegativeVectorSeminormTwo R s (fun x => u x - ωgrad x) := by
      apply cubeBesovNegativeVectorSeminormTwo_eq_of_eq_on_cubeSet
      intro x hx
      ext i
      have hcoord :
          u x i = v R x i + ωgrad x i := by
        simpa [ωR, ωgrad] using
          congrArg (fun z => z i) (hdecomp n R hR x hx)
      change v R x i = u x i - ωgrad x i
      linarith
    have hu_mem : MemVectorL2 (cubeSet R) u := hu_mem_desc n R hR
    have hω_mem : MemVectorL2 (cubeSet R) ωgrad := by
      simpa [ωgrad] using ωR.toH1MeanZero.toH1Function.grad_memVectorL2
    have huBdd :
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N u) :=
      huBdd_desc n R hR
    have hωBdd :
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N ωgrad) :=
      cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp R hs ωgrad
        (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet R hω_mem)
    have hsub_mem : MemVectorL2 (cubeSet R) (fun x => u x - ωgrad x) :=
      hu_mem.sub hω_mem
    have hsubBdd :
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => u x - ωgrad x)) :=
      cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp R hs
        (fun x => u x - ωgrad x)
        (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet R hsub_mem)
    let Su : ℝ := cubeBesovNegativeVectorSeminormTwo R s u
    let Sω : ℝ := cubeBesovNegativeVectorSeminormTwo R s ωgrad
    let Sv : ℝ := cubeBesovNegativeVectorSeminormTwo R s (fun x => u x - ωgrad x)
    have hsub_le :
        Sv ≤ Real.sqrt 2 * (Su + Sω) := by
      simpa [Sv, Su, Sω, ωgrad] using
        cubeBesovNegativeVectorSeminormTwo_sub_le_sqrtTwo_mul_add_of_bddAbove
          R s u ωgrad hu_mem hω_mem huBdd hωBdd
    have hSv_nonneg : 0 ≤ Sv := by
      dsimp [Sv]
      exact cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove R s
        (fun x => u x - ωgrad x) hsubBdd
    have hSu_nonneg : 0 ≤ Su := by
      dsimp [Su]
      exact cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove R s u huBdd
    have hSω_nonneg : 0 ≤ Sω := by
      dsimp [Sω]
      exact cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove R s ωgrad hωBdd
    have hsqrt2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hSv_sq :
        Sv ^ 2 ≤ 4 * (Su ^ 2 + Sω ^ 2) := by
      have hright_nonneg : 0 ≤ Real.sqrt 2 * (Su + Sω) :=
        mul_nonneg (Real.sqrt_nonneg 2) (add_nonneg hSu_nonneg hSω_nonneg)
      have hsq_right :
          (Real.sqrt 2 * (Su + Sω)) ^ 2 =
            2 * (Su + Sω) ^ 2 := by
        rw [mul_pow, hsqrt2_sq]
      calc
        Sv ^ 2 ≤ (Real.sqrt 2 * (Su + Sω)) ^ 2 := by
          nlinarith
        _ = 2 * (Su + Sω) ^ 2 := hsq_right
        _ ≤ 4 * (Su ^ 2 + Sω ^ 2) := by
          nlinarith [sq_nonneg (Su - Sω)]
    have hΩ : Ω R = Sω ^ 2 := by
      simp [Ω, Sω, ωR, ωgrad, hR]
    calc
      (cubeBesovNegativeVectorSeminormTwo R s (v R)) ^ 2
          = Sv ^ 2 := by
            simpa [Sv] using congrArg (fun t : ℝ => t ^ 2) hv_eq_sub
      _ ≤ 4 * (Su ^ 2 + Sω ^ 2) := hSv_sq
      _ = 4 * (U R + Ω R) := by
            simp [U, hΩ, Su]
  have havg :
      weakFluxRHSHarmonicRemainderAveragedSeminormSq Q s v n ≤
        descendantsAverage Q n (fun R => 4 * (U R + Ω R)) := by
    unfold weakFluxRHSHarmonicRemainderAveragedSeminormSq
    exact descendantsAverage_le_descendantsAverage Q n hpoint
  have hweight_nonneg : 0 ≤ coarsePoincareRHSDepthWeight s n := by
    unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  calc
    weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v n
        =
      coarsePoincareRHSDepthWeight s n *
        weakFluxRHSHarmonicRemainderAveragedSeminormSq Q s v n := by
          rfl
    _ ≤
      coarsePoincareRHSDepthWeight s n *
        descendantsAverage Q n (fun R => 4 * (U R + Ω R)) :=
          mul_le_mul_of_nonneg_left havg hweight_nonneg
    _ =
      4 *
        (coarsePoincareRHSDepthWeight s n * descendantsAverage Q n U +
          coarsePoincareRHSDepthWeight s n * descendantsAverage Q n Ω) := by
          rw [show descendantsAverage Q n (fun R => 4 * (U R + Ω R)) =
            4 * descendantsAverage Q n (fun R => U R + Ω R) by
              exact descendantsAverage_smul Q n (4 : ℝ)
                (fun R => U R + Ω R)]
          rw [descendantsAverage_add Q n U Ω]
          ring
    _ ≤ 4 * (BU + Bω) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add
              (by simpa [coarsePoincareRHSSn, coarsePoincareRHSRn, U] using
                hu_tail n)
              (by simpa [Ω] using hω_tail n))
            (by norm_num : (0 : ℝ) ≤ 4)

/-- Public forced-solution specialization of the harmonic-remainder `BV`
closure: the original-gradient tail is supplied by the public coarse-Poincare
RHS budget, so only the selected Neumann-corrector tail remains explicit. -/
theorem forcedSolution_harmonicRemainderScaledAveragedSeminormSq_le_four_mul_add_of_decomposition_and_neumann_tail
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (v : TriadicCube d → Vec d → Vec d)
    (ω : (n : ℕ) → (R : TriadicCube d) → R ∈ descendantsAtDepth Q n →
      MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
        (fun x => g x - cubeAverageVec R g))
    {Bω : ℝ}
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (hdecomp :
      ∀ n : ℕ, ∀ R : TriadicCube d, ∀ hR : R ∈ descendantsAtDepth Q n, ∀ x ∈ cubeSet R,
        forcedSolutionGradientField u x =
          v R x + (ω n R hR).toH1MeanZero.toH1Function.grad x)
    (hω_tail :
      ∀ n : ℕ,
        coarsePoincareRHSDepthWeight s n *
          descendantsAverage Q n
            (fun R =>
              if hR : R ∈ descendantsAtDepth Q n then
                (cubeBesovNegativeVectorSeminormTwo R s
                  (fun x => (ω n R hR).toH1MeanZero.toH1Function.grad x)) ^ 2
              else 0) ≤ Bω) :
    ∀ n : ℕ,
      weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v n ≤
        4 * (forcedSolutionWeakFluxPoincareTailBudget Q a s u + Bω) := by
  refine
    weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq_le_four_mul_add_of_decomposition_and_neumann_tail
      (Q := Q) (a := publicCoeffField Q a) (s := s) (g := g)
      (u := forcedSolutionGradientField u) v ω
      (BU := forcedSolutionWeakFluxPoincareTailBudget Q a s u) (Bω := Bω)
      hs ?_ ?_ hdecomp ?_ hω_tail
  · intro n R hR
    exact forcedSolutionGradientField_memVectorL2_descendant_cubeSet u hR
  · intro n R hR
    exact forcedSolutionGradientField_descendant_negativeBesovPartialSeminormTwo_bddAbove
      (Q := Q) (R := R) (a := a) (g := g) u hR hs
  · intro n
    exact
      forcedSolutionGradientField_coarsePoincareRHSSn_le_weakFluxPoincareTailBudget_publicCoeffField
        (Q := Q) (a := a) (g := g) (s := s) u hs hs_lt.le hg n

/-- Public weak-flux bridge after choosing the local harmonic remainders and
their Neumann correctors.  The harmonic-remainder `BV` tail is closed by the
coarse-Poincare tail of the original solution plus the selected Neumann-corrector
negative-Besov tail. -/
theorem exists_harmonicRemainderSelector_localizedForcedSolutionPublicFlux_le_weakFluxExpandedRHS_of_selected_neumann_tail
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (m : ℕ) {Bω : ℝ}
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (hBω_nonneg : 0 ≤ Bω) :
    ∃ v : TriadicCube d → Vec d → Vec d,
      ∃ ω : (n : ℕ) → (R : TriadicCube d) → R ∈ descendantsAtDepth Q n →
          MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
            (fun x => g x - cubeAverageVec R g),
        (∀ n : ℕ, ∀ R : TriadicCube d, ∀ hR : R ∈ descendantsAtDepth Q n,
          ∀ x ∈ cubeSet R,
            forcedSolutionGradientField u x =
              v R x + (ω n R hR).toH1MeanZero.toH1Function.grad x) ∧
        ((∀ n : ℕ,
          coarsePoincareRHSDepthWeight s n *
            descendantsAverage Q n
              (fun R =>
                if hR : R ∈ descendantsAtDepth Q n then
                  (cubeBesovNegativeVectorSeminormTwo R s
                    (fun x => (ω n R hR).toH1MeanZero.toH1Function.grad x)) ^ 2
                else 0) ≤ Bω) →
          localizedFluxDefectNegativeBesovAverageTwo Q s
              (fun x => matVecMul (publicCoeffField Q a x)
                (forcedSolutionGradientField u x)) m ≤
            Real.sqrt
              ((coarsePoincareRHSDepthWeight s m)⁻¹ *
                (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
                    (publicCoeffField Q a) *
                    cubeAverage Q
                      (coefficientEnergyDensity (publicCoeffField Q a)
                        (forcedSolutionGradientField u)) +
                  (5 * s⁻¹) * forcedSolutionWeakFluxPoincareTailBudget Q a s u +
                  (5 * s⁻¹) *
                    (4 * (forcedSolutionWeakFluxPoincareTailBudget Q a s u + Bω)) +
                  2500 * (s⁻¹) ^ 4 *
                    (LambdaSq Q (s / 2) (.finite 2)
                      (publicCoeffField Q a)) ^ 2 *
                    ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
                    (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2))) := by
  let BV : ℝ := 4 * (forcedSolutionWeakFluxPoincareTailBudget Q a s u + Bω)
  have hBV_nonneg : 0 ≤ BV := by
    dsimp [BV]
    exact mul_nonneg (by norm_num : 0 ≤ (4 : ℝ))
      (add_nonneg (forcedSolutionWeakFluxPoincareTailBudget_nonneg u hs) hBω_nonneg)
  rcases
      exists_harmonicRemainderSelector_localizedForcedSolutionPublicFlux_le_weakFluxExpandedRHS_of_averaged_tail
        (Q := Q) (a := a) (s := s) (g := g) u m
        (BV := BV) hs hs_lt hg hBV_nonneg with
    ⟨v, hselector, hflux⟩
  let ω : (n : ℕ) → (R : TriadicCube d) → R ∈ descendantsAtDepth Q n →
      MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
        (fun x => g x - cubeAverageVec R g) :=
    fun n R hR => Classical.choose (hselector R ⟨n, hR⟩)
  have hdecomp :
      ∀ n : ℕ, ∀ R : TriadicCube d, ∀ hR : R ∈ descendantsAtDepth Q n,
        ∀ x ∈ cubeSet R,
          forcedSolutionGradientField u x =
            v R x + (ω n R hR).toH1MeanZero.toH1Function.grad x := by
    intro n R hR x hx
    let hsel := hselector R ⟨n, hR⟩
    let ωR : MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
        (fun x => g x - cubeAverageVec R g) :=
      Classical.choose hsel
    let w : AHarmonicFunction (publicCoeffField Q a) (cubeSet R) :=
      Classical.choose (Classical.choose_spec hsel)
    have hspec :
        v R = (fun x => w.toH1.grad x) ∧
          ∀ x ∈ cubeSet R,
            forcedSolutionGradientField u x =
              w.toH1.grad x + ωR.toH1MeanZero.toH1Function.grad x := by
      simpa [hsel, ωR, w] using
        Classical.choose_spec (Classical.choose_spec hsel)
    have hvx : v R x = w.toH1.grad x := by
      simpa using congrFun hspec.1 x
    calc
      forcedSolutionGradientField u x =
          w.toH1.grad x + ωR.toH1MeanZero.toH1Function.grad x := hspec.2 x hx
      _ = v R x + (ω n R hR).toH1MeanZero.toH1Function.grad x := by
          simp [ω, ωR, hvx]
  refine ⟨v, ω, hdecomp, ?_⟩
  intro hω_tail
  have hv_tail :
      ∀ n : ℕ,
        weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v n ≤ BV :=
    forcedSolution_harmonicRemainderScaledAveragedSeminormSq_le_four_mul_add_of_decomposition_and_neumann_tail
      (Q := Q) (a := a) (s := s) (g := g) u v ω hs hs_lt hg hdecomp hω_tail
  simpa [BV] using hflux (fun k => hv_tail (m + k))

/-- Depth-zero version of the selected-Neumann weak-flux bridge, with the
left side rewritten as the public negative Besov norm of the forced flux field.
The remaining input is the selected Neumann-corrector negative-Besov tail. -/
theorem exists_harmonicRemainderSelector_scaleNormalizedForcedFlux_le_selectedNeumannExpandedRHS
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    {Bω : ℝ}
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (hBω_nonneg : 0 ≤ Bω) :
    ∃ v : TriadicCube d → Vec d → Vec d,
      ∃ ω : (n : ℕ) → (R : TriadicCube d) → R ∈ descendantsAtDepth Q n →
          MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
            (fun x => g x - cubeAverageVec R g),
        (∀ n : ℕ, ∀ R : TriadicCube d, ∀ hR : R ∈ descendantsAtDepth Q n,
          ∀ x ∈ cubeSet R,
            forcedSolutionGradientField u x =
              v R x + (ω n R hR).toH1MeanZero.toH1Function.grad x) ∧
        ((∀ n : ℕ,
          coarsePoincareRHSDepthWeight s n *
            descendantsAverage Q n
              (fun R =>
                if hR : R ∈ descendantsAtDepth Q n then
                  (cubeBesovNegativeVectorSeminormTwo R s
                    (fun x => (ω n R hR).toH1MeanZero.toH1Function.grad x)) ^ 2
                else 0) ≤ Bω) →
          scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2)
              (forcedSolutionFluxField Q a u) ≤
            forcedSolutionWeakFluxSelectedNeumannTailExpandedRHS Q a s u Bω) := by
  rcases
      exists_harmonicRemainderSelector_localizedForcedSolutionPublicFlux_le_weakFluxExpandedRHS_of_selected_neumann_tail
        (Q := Q) (a := a) (s := s) (g := g) u 0 hs hs_lt hg hBω_nonneg with
    ⟨v, ω, hdecomp, hflux⟩
  refine ⟨v, ω, hdecomp, ?_⟩
  intro hω_tail
  let F : Vec d → Vec d :=
    fun x => matVecMul (publicCoeffField Q a x) (forcedSolutionGradientField u x)
  have hloc :
      localizedFluxDefectNegativeBesovAverageTwo Q s F 0 ≤
        forcedSolutionWeakFluxSelectedNeumannTailExpandedRHS Q a s u Bω := by
    simpa [F, forcedSolutionWeakFluxSelectedNeumannTailExpandedRHS] using
      hflux hω_tail
  have hF_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N F) := by
    simpa [F] using
      forcedSolutionPublicFlux_negativeBesovPartialSeminormTwo_bddAbove_descendant
        (Q := Q) (R := Q) (a := a) (g := g) (j := 0) u
        (by simp [descendantsAtDepth_zero]) hs
  have hF_nonneg : 0 ≤ cubeBesovNegativeVectorSeminormTwo Q s F :=
    cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove Q s F hF_bdd
  have hdepth :
      localizedFluxDefectNegativeBesovAverageTwo Q s F 0 =
        cubeBesovNegativeVectorSeminormTwo Q s F :=
    localizedFluxDefectNegativeBesovAverageTwo_depth_zero_of_nonneg
      Q s F hF_nonneg
  calc
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2)
        (forcedSolutionFluxField Q a u)
        =
      cubeBesovNegativeVectorSeminormTwo Q s F := by
        simpa [F] using
          scaleNormalizedNegativeBesovVectorNorm_forcedSolutionFluxField_finite_two_eq_cubeBesovNegativeVectorSeminormTwo_publicCoeffField
            Q a s u
    _ =
      localizedFluxDefectNegativeBesovAverageTwo Q s F 0 := hdepth.symm
    _ ≤ forcedSolutionWeakFluxSelectedNeumannTailExpandedRHS Q a s u Bω := hloc

/-- Public-RHS-facing form of
`exists_harmonicRemainderSelector_scaleNormalizedForcedFlux_le_selectedNeumannExpandedRHS`.
It isolates the remaining scalar absorption from the selected-Neumann expanded
RHS into the note-facing weak-flux RHS. -/
theorem exists_harmonicRemainderSelector_scaleNormalizedForcedFlux_le_weakFluxWithRHSRHS_of_selectedNeumannTail_of_expanded_bound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {C s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    {Bω : ℝ}
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (hBω_nonneg : 0 ≤ Bω)
    (hexpanded :
      forcedSolutionWeakFluxSelectedNeumannTailExpandedRHS Q a s u Bω ≤
        weakFluxWithRHSRHS C Q a s g u) :
    ∃ v : TriadicCube d → Vec d → Vec d,
      ∃ ω : (n : ℕ) → (R : TriadicCube d) → R ∈ descendantsAtDepth Q n →
          MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
            (fun x => g x - cubeAverageVec R g),
        (∀ n : ℕ, ∀ R : TriadicCube d, ∀ hR : R ∈ descendantsAtDepth Q n,
          ∀ x ∈ cubeSet R,
            forcedSolutionGradientField u x =
              v R x + (ω n R hR).toH1MeanZero.toH1Function.grad x) ∧
        ((∀ n : ℕ,
          coarsePoincareRHSDepthWeight s n *
            descendantsAverage Q n
              (fun R =>
                if hR : R ∈ descendantsAtDepth Q n then
                  (cubeBesovNegativeVectorSeminormTwo R s
                    (fun x => (ω n R hR).toH1MeanZero.toH1Function.grad x)) ^ 2
                else 0) ≤ Bω) →
          scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2)
              (forcedSolutionFluxField Q a u) ≤
            weakFluxWithRHSRHS C Q a s g u) := by
  rcases
      exists_harmonicRemainderSelector_scaleNormalizedForcedFlux_le_selectedNeumannExpandedRHS
        (Q := Q) (a := a) (s := s) (g := g) u hs hs_lt hg hBω_nonneg with
    ⟨v, ω, hdecomp, hflux⟩
  refine ⟨v, ω, hdecomp, ?_⟩
  intro hω_tail
  exact (hflux hω_tail).trans hexpanded

/-- Pointwise selected-Neumann corrector tail bounds imply the averaged `Bω`
tail consumed by the public weak-flux bridge. -/
theorem selectedNeumannCorrectorAveragedTail_le_of_pointwise_tail
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    {s : ℝ} {g : Vec d → Vec d}
    (ω : (n : ℕ) → (R : TriadicCube d) → R ∈ descendantsAtDepth Q n →
      MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g))
    {Bω : ℝ}
    (hω_point :
      ∀ n : ℕ, ∀ R : TriadicCube d, ∀ hR : R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => (ω n R hR).toH1MeanZero.toH1Function.grad x)) ^ 2 ≤
          (coarsePoincareRHSDepthWeight s n)⁻¹ * Bω) :
    ∀ n : ℕ,
      coarsePoincareRHSDepthWeight s n *
        descendantsAverage Q n
          (fun R =>
            if hR : R ∈ descendantsAtDepth Q n then
              (cubeBesovNegativeVectorSeminormTwo R s
                (fun x => (ω n R hR).toH1MeanZero.toH1Function.grad x)) ^ 2
            else 0) ≤ Bω := by
  intro n
  let W : ℝ := coarsePoincareRHSDepthWeight s n
  have hW_pos : 0 < W := by
    dsimp [W, coarsePoincareRHSDepthWeight]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
  have havg :
      descendantsAverage Q n
          (fun R =>
            if hR : R ∈ descendantsAtDepth Q n then
              (cubeBesovNegativeVectorSeminormTwo R s
                (fun x => (ω n R hR).toH1MeanZero.toH1Function.grad x)) ^ 2
            else 0) ≤
        descendantsAverage Q n (fun _R => W⁻¹ * Bω) := by
    refine descendantsAverage_le_descendantsAverage Q n ?_
    intro R hR
    simpa [W, hR] using hω_point n R hR
  calc
    coarsePoincareRHSDepthWeight s n *
        descendantsAverage Q n
          (fun R =>
            if hR : R ∈ descendantsAtDepth Q n then
              (cubeBesovNegativeVectorSeminormTwo R s
                (fun x => (ω n R hR).toH1MeanZero.toH1Function.grad x)) ^ 2
            else 0)
        ≤
      W * descendantsAverage Q n (fun _R => W⁻¹ * Bω) := by
        exact mul_le_mul_of_nonneg_left havg hW_pos.le
    _ = W * (W⁻¹ * Bω) := by
        rw [descendantsAverage_const]
    _ = Bω := by
        calc
          W * (W⁻¹ * Bω) = (W * W⁻¹) * Bω := by ring
          _ = Bω := by
              rw [mul_inv_cancel₀ hW_pos.ne']
              ring

/-- Public weak-flux bridge with the selected-Neumann tail accepted in the
pointwise form often produced by local corrector estimates. -/
theorem exists_harmonicRemainderSelector_scaleNormalizedForcedFlux_le_weakFluxWithRHSRHS_of_selectedNeumannPointwiseTail_of_expanded_bound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {C s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    {Bω : ℝ}
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (hBω_nonneg : 0 ≤ Bω)
    (hexpanded :
      forcedSolutionWeakFluxSelectedNeumannTailExpandedRHS Q a s u Bω ≤
        weakFluxWithRHSRHS C Q a s g u) :
    ∃ v : TriadicCube d → Vec d → Vec d,
      ∃ ω : (n : ℕ) → (R : TriadicCube d) → R ∈ descendantsAtDepth Q n →
          MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
            (fun x => g x - cubeAverageVec R g),
        (∀ n : ℕ, ∀ R : TriadicCube d, ∀ hR : R ∈ descendantsAtDepth Q n,
          ∀ x ∈ cubeSet R,
            forcedSolutionGradientField u x =
              v R x + (ω n R hR).toH1MeanZero.toH1Function.grad x) ∧
        ((∀ n : ℕ, ∀ R : TriadicCube d, ∀ hR : R ∈ descendantsAtDepth Q n,
          (cubeBesovNegativeVectorSeminormTwo R s
            (fun x => (ω n R hR).toH1MeanZero.toH1Function.grad x)) ^ 2 ≤
            (coarsePoincareRHSDepthWeight s n)⁻¹ * Bω) →
          scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2)
              (forcedSolutionFluxField Q a u) ≤
            weakFluxWithRHSRHS C Q a s g u) := by
  rcases
      exists_harmonicRemainderSelector_scaleNormalizedForcedFlux_le_weakFluxWithRHSRHS_of_selectedNeumannTail_of_expanded_bound
        (Q := Q) (a := a) (s := s) (g := g) u
        (Bω := Bω) hs hs_lt hg hBω_nonneg hexpanded with
    ⟨v, ω, hdecomp, hflux⟩
  refine ⟨v, ω, hdecomp, ?_⟩
  intro hω_point
  exact hflux
    (selectedNeumannCorrectorAveragedTail_le_of_pointwise_tail
      (Q := Q) (a := publicCoeffField Q a) (s := s) (g := g)
      ω hω_point)

/-- Same public weak-flux bridge with the automatic boundedness part of the
harmonic-remainder tail discharged from `H¹` membership.  The remaining input
is only the scalar `BV` estimate for the constructed harmonic remainders. -/
theorem localizedForcedSolutionPublicFlux_le_weakFluxExpandedRHS_of_harmonicRemainder_sq_bound_of_public_poincare_tail
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (m : ℕ) {BV : ℝ}
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (hBV_nonneg : 0 ≤ BV)
    (hv_sq :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
            (fun x => g x - cubeAverageVec R g),
          ∀ w : AHarmonicFunction (publicCoeffField Q a) (cubeSet R),
            (∀ x ∈ cubeSet R,
              forcedSolutionGradientField u x =
                w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => w.toH1.grad x)) ^ 2 ≤
              (coarsePoincareRHSDepthWeight s j)⁻¹ * BV) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (publicCoeffField Q a x)
          (forcedSolutionGradientField u x)) m ≤
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
              (publicCoeffField Q a) *
              cubeAverage Q
                (coefficientEnergyDensity (publicCoeffField Q a)
                  (forcedSolutionGradientField u)) +
            (5 * s⁻¹) * forcedSolutionWeakFluxPoincareTailBudget Q a s u +
            (5 * s⁻¹) * BV +
            2500 * (s⁻¹) ^ 4 *
              (LambdaSq Q (s / 2) (.finite 2)
                (publicCoeffField Q a)) ^ 2 *
              ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)) := by
  refine
    localizedForcedSolutionPublicFlux_le_weakFluxExpandedRHS_of_constructed_harmonicRemainder_bounds_of_public_poincare_tail
      (Q := Q) (a := a) (s := s) (g := g) u m
      (BV := BV) hs hs_lt hg hBV_nonneg ?_
  intro j R hR ω w hw
  exact
    ⟨AHarmonicFunction.grad_negativeBesovPartialSeminormTwo_bddAbove
        (Q := R) (a := publicCoeffField Q a) w hs,
      hv_sq j R hR ω w hw⟩

/-- Public theorem package for the weak flux estimate with right-hand side. -/
structure WeakFluxRHSTheory (d : ℕ) [NeZero d] : Prop where
  exists_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
        {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g),
        0 < s → s < 1 → ForceBesovRegularity Q s g →
          scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2)
              (forcedSolutionFluxField Q a u) ≤
            weakFluxWithRHSRHS C Q a s g u

/-- Conditional public theorem package for the corrected weak-flux route.  The
scalar absorption into the public RHS is included; the remaining input is only
the local corrected recurrence together with a selected Neumann-corrector
gradient on every descendant. -/
private theorem weakFluxRHSTheory_of_correctorEnergySelector
    {d : ℕ} [NeZero d] {C : ℝ}
    (hC_pos : 0 < C)
    (hC_energy : Real.sqrt 50 ≤ C)
    (hC_force :
      50 * ((d : ℝ) *
          (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2)) ≤ C)
    (hselector :
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
        {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g),
          0 < s → s < 1 → ForceBesovRegularity Q s g →
            ∃ z : TriadicCube d → Vec d → Vec d,
              (∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
                ∃ ω : MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
                    (fun x => g x - cubeAverageVec R g),
                  z R = (fun x => ω.toH1MeanZero.toH1Function.grad x)) ∧
              ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
                (cubeBesovNegativeVectorSeminormTwo R s
                  (fun x => matVecMul (publicCoeffField Q a x)
                    (forcedSolutionGradientField u x))) ^ 2 ≤
                  Real.rpow (3 : ℝ) (-2 * s) *
                    descendantsAverage R 1
                      (fun S =>
                        (cubeBesovNegativeVectorSeminormTwo S s
                          (fun x => matVecMul (publicCoeffField Q a x)
                            (forcedSolutionGradientField u x))) ^ 2) +
                  weakFluxRHSCorrectorEnergyLocalError R (publicCoeffField Q a)
                    (forcedSolutionGradientField u) (z R) s) :
    WeakFluxRHSTheory d := by
  refine ⟨⟨(d : ℝ) ^ 2 * C, ?_, ?_⟩⟩
  · have hd_pos : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact mul_pos (sq_pos_of_pos hd_pos) hC_pos
  intro Q a s g u hs hs_lt hg
  rcases hselector (Q := Q) (a := a) (s := s) (g := g) u hs hs_lt hg with
    ⟨z, hz, hlocal⟩
  exact
    scaleNormalizedForcedFlux_le_weakFluxWithRHSRHS_of_correctorEnergySelector
      (d := d) (C := C) hC_energy hC_force
      Q a u z hs hs_lt hg hlocal hz

/-- Final public theorem package for the weak-flux estimate with right-hand
side. -/
theorem weakFluxRHSTheory {d : ℕ} [NeZero d] : WeakFluxRHSTheory d := by
  let D : ℝ :=
    50 * ((d : ℝ) *
      (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2))
  let C : ℝ := Real.sqrt 50 + D + 1
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hC_pos : 0 < C := by
    dsimp [C]
    nlinarith [Real.sqrt_nonneg (50 : ℝ), hD_nonneg]
  have hC_energy : Real.sqrt 50 ≤ C := by
    dsimp [C]
    nlinarith [hD_nonneg]
  have hC_force :
      50 * ((d : ℝ) *
          (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2)) ≤ C := by
    dsimp [C, D]
    nlinarith [Real.sqrt_nonneg (50 : ℝ)]
  exact
    weakFluxRHSTheory_of_correctorEnergySelector
      (d := d) (C := C) hC_pos hC_energy hC_force
      (by
        intro Q a s g u hs _hs_lt hg
        exact
          exists_neumannCorrectorSelector_fluxSeminormStepCorrectorEnergyLocalError_forcedSolution
            (Q := Q) (a := a) (s := s) (g := g) u hs hg)

end

end Ch03
end Book
end Homogenization
