/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.FinalTheorems.ExpandedAndElliptic
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.Regularity
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.FluxStepping
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.NeumannCorrector

/-! # Weak Solution Bridge -/

namespace Homogenization

noncomputable section

/-!
# Weak-solution bridges for the RHS weak-flux lane

This file starts the Section 3.2.3 development by exposing the existing
RHS Poincare machinery through the same `H¹` weak-solution predicate used by
the Section 3.3 black boxes.  The theorem below controls the gradient field;
the full weak-flux estimate still needs the local Neumann-correction and
harmonic-flux recurrence from manuscript lines 1720--2224.
-/

/--
Build the centered Neumann corrector and the corresponding harmonic remainder
directly from an `H¹` RHS weak solution on one cube.

This is the manuscript Step 1 interface for Section 3.2.3, modulo the supplied
mean-zero coercive estimate on the half-open cube. -/
theorem exists_centeredNeumannCorrector_aHarmonicRemainder_of_h1DirichletRhsWeakSolutionOn
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) (u : H1Function (cubeSet Q)) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hg : MemVectorL2 (cubeSet Q) g)
    (hC : H1CoerciveEstimate (cubeSet Q)) :
    ∃ ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g),
      ∃ w : AHarmonicFunction a (cubeSet Q),
        ∀ x ∈ cubeSet Q,
          u.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) :=
    isFiniteMeasureVolumeMeasureOnCubeSet_rhs Q
  have hconst_mem :
      MemVectorL2 (cubeSet Q) (fun _ : Vec d => cubeAverageVec Q g) :=
    memVectorL2_const (cubeAverageVec Q g)
  have hg_centered :
      MemVectorL2 (cubeSet Q) (fun x => g x - cubeAverageVec Q g) :=
    hg.sub hconst_mem
  have hne : Set.Nonempty (cubeSet Q) := by
    refine ⟨cubeCenter Q, openCubeSet_subset_cubeSet Q ?_⟩
    rw [← ball_cubeCenter_eq_openCubeSet]
    simpa [Metric.mem_ball] using cubeRadius_pos Q
  let ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g) :=
    meanZeroNeumannCorrectorDataOf_h1CoerciveEstimate
      (Q := Q) (a := a) (g := fun x => g x - cubeAverageVec Q g)
      (lam := lam) (Lam := Lam) hg_centered hC hne hEll
  rcases
      ω.exists_aHarmonicRemainder_of_potential_solenoidal_centered
        (Q := Q) (a := a) (g := g) (u := u.grad)
        u.isPotentialOn (hu.residual_solenoidal hEll hg) hEll hg with
    ⟨w, hw⟩
  exact ⟨ω, w, hw⟩

/--
One-cube PDE-facing local recurrence interface for the weak-flux RHS lane.

Starting from an `H¹` RHS weak solution, this constructs the centered Neumann
corrector and harmonic remainder, and packages the flux local-step estimate
for any supplied descendant flux-energy control of that harmonic remainder.
This is the Lean counterpart of manuscript Section 3.2.3, Steps 1--3, at the
single-cube interface level. -/
theorem exists_centeredNeumannCorrector_aHarmonicRemainder_fluxStepEnergy_of_h1DirichletRhsWeakSolutionOn
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) (u : H1Function (cubeSet Q)) {s lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hg : MemVectorL2 (cubeSet Q) g)
    (hC : H1CoerciveEstimate (cubeSet Q)) (N : ℕ) :
    ∃ ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g),
      ∃ w : AHarmonicFunction a (cubeSet Q),
        (∀ x ∈ cubeSet Q,
          u.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        ∀ energy : Vec d → ℝ,
          (∀ x ∈ cubeSet Q, 0 ≤ energy x) →
          MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume →
          CubeAverageFluxEnergyControl Q a
            (fun x => matVecMul (a x) (w.toH1.grad x)) energy →
          Summable (fun n : ℕ =>
            geometricWeight s 2 n *
              maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) →
          (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1)
              (fun x => matVecMul (a x) (u.grad x))) ^ 2 ≤
            Real.rpow (3 : ℝ) (-2 * s) *
              descendantsAverage Q 1
                (fun R =>
                  (cubeBesovNegativeVectorPartialSeminormTwo R s N
                    (fun x => matVecMul (a x) (u.grad x))) ^ 2) +
            (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a *
              cubeAverage Q energy := by
  rcases
      exists_centeredNeumannCorrector_aHarmonicRemainder_of_h1DirichletRhsWeakSolutionOn
        (Q := Q) (a := a) (g := g) (u := u)
        hEll hu hg hC with
    ⟨ω, w, huw⟩
  refine ⟨ω, w, huw, ?_⟩
  intro energy henergy_nonneg henergy_int hflux hsum
  exact
    ω.sq_cubeBesovNegativeVectorPartialSeminormTwo_flux_succ_le_descendantsAverage_add_harmonic_energy
      (u := u.grad) w s hs N energy hEll u.grad_memVectorL2 hg
      henergy_nonneg henergy_int hflux hsum huw

/--
PDE-facing wrapper around the q=2 RHS Poincare final theorem.

If `u` solves `-div(a grad u) = div g` on `Q`, then `grad u` is a potential
field whose residual flux `a grad u - g` is solenoidal.  This packages those
two facts and applies
`cubeBesovNegativeVectorSeminormTwo_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_parent_potential_solenoidal`.

This is an infrastructure step for
`p.weak.flux.RHS.deterministic.theory`, not the final weak-flux estimate.
-/
theorem cubeBesovNegativeVectorSeminormTwo_grad_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_h1DirichletRhsWeakSolutionOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) (u : H1Function (cubeSet Q)) {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    cubeBesovNegativeVectorSeminormTwo Q s u.grad ≤
      Real.sqrt
        (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a u.grad) +
          15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
  have hgMem : MemVectorL2 (cubeSet Q) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q hg
  exact
    cubeBesovNegativeVectorSeminormTwo_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_parent_potential_solenoidal
      (Q := Q) (a := a) (g := g) (u := u.grad)
      (s := s) (lam := lam) (Lam := Lam)
      hs hs_le hEll u.isPotentialOn (hu.residual_solenoidal hEll hgMem)
      hg hGlobalBdd

/--
PDE-facing RHS Poincare estimate with the manuscript `g ∈ H^s` regularity
package, rather than separate `L²` and positive-Besov boundedness hypotheses.
-/
theorem cubeBesovNegativeVectorSeminormTwo_grad_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_h1DirichletRhsWeakSolutionOn_of_cubeVectorBesovHRegularity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) (u : H1Function (cubeSet Q)) {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hg : CubeVectorBesovHRegularity Q s g) :
    cubeBesovNegativeVectorSeminormTwo Q s u.grad ≤
      Real.sqrt
        (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a u.grad) +
          15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) :=
  cubeBesovNegativeVectorSeminormTwo_grad_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_h1DirichletRhsWeakSolutionOn
    (Q := Q) (a := a) (g := g) (u := u)
    (s := s) (lam := lam) (Lam := Lam)
    hs hs_le hEll hu hg.memLp hg.partialSeminorms_bddAbove

end

end Homogenization
