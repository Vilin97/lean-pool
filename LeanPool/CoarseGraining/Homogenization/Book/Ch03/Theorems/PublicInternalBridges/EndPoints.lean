/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoeffField
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Definitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHS
public import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
public import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.CoarseGrainingL2
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.ForceLocalization
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.TerminalBounds
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.GlobalIteration
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.WeakSolutionBridge
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.AECongruence
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesComponentwise
public import LeanPool.CoarseGraining.Homogenization.PDE.EnergyIdentities
public import LeanPool.CoarseGraining.Homogenization.PDE.NeumannRHS
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalCubeBridge

/-! # End Points -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Public/internal bridges for Chapter 3

This file now contains the Besov, flux-RHS, and coarse-graining public/internal
bridge endpoints.  Lower bridge layers live in the `PublicInternalBridges/`
submodules.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

theorem cubeBesovPairing_eq_of_left_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {f₁ f₂ g : Vec d → ℝ}
    (hf : f₁ =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] f₂) :
    cubeBesovPairing Q f₁ g = cubeBesovPairing Q f₂ g := by
  unfold cubeBesovPairing
  exact cubeAverage_eq_of_ae_eq_on_cubeSet <|
    hf.mono fun x hx => by simp [hx]

theorem cubeBesovDualFullNormValueSet_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {f₁ f₂ : Vec d → ℝ}
    (s : ℝ) (p q : ℝ≥0∞)
    (hf : f₁ =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] f₂) :
    cubeBesovDualFullNormValueSet Q s p q f₁ =
      cubeBesovDualFullNormValueSet Q s p q f₂ := by
  ext r
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg,
      congrArg abs (cubeBesovPairing_eq_of_left_ae_eq_on_cubeSet hf)⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg,
      congrArg abs (cubeBesovPairing_eq_of_left_ae_eq_on_cubeSet hf.symm)⟩

theorem cubeBesovDualFullNorm_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {f₁ f₂ : Vec d → ℝ}
    (s : ℝ) (p q : ℝ≥0∞)
    (hf : f₁ =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] f₂) :
    cubeBesovDualFullNorm Q s p q f₁ =
      cubeBesovDualFullNorm Q s p q f₂ := by
  unfold cubeBesovDualFullNorm
  rw [cubeBesovDualFullNormValueSet_eq_of_ae_eq_on_cubeSet s p q hf]

theorem scaleNormalizedDualNegativeBesovVectorNormTwo_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {F G : Vec d → Vec d}
    (s : ℝ) (hFG : F =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] G) :
    scaleNormalizedDualNegativeBesovVectorNormTwo Q s F =
      scaleNormalizedDualNegativeBesovVectorNormTwo Q s G := by
  unfold scaleNormalizedDualNegativeBesovVectorNormTwo
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact cubeBesovDualFullNorm_eq_of_ae_eq_on_cubeSet s (2 : ℝ≥0∞) (2 : ℝ≥0∞) <|
    hFG.mono fun x hx => congrArg (fun y : Vec d => y i) hx

theorem negativeBesovVectorDepthAverage_eq_cubeBesovNegativeVectorDepthAverage
    {d : ℕ} (Q : TriadicCube d) (F : Vec d → Vec d) (j : ℕ) :
    negativeBesovVectorDepthAverage Q F j =
      Homogenization.cubeBesovNegativeVectorDepthAverage Q F j := by
  rfl

theorem negativeBesovVectorDepthSeminorm_eq_cubeBesovNegativeVectorDepthSeminorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) :
    negativeBesovVectorDepthSeminorm Q s F j =
      Homogenization.cubeBesovNegativeVectorDepthSeminorm Q s F j := by
  simp [negativeBesovVectorDepthSeminorm,
    Homogenization.cubeBesovNegativeVectorDepthSeminorm,
    negativeBesovVectorDepthAverage_eq_cubeBesovNegativeVectorDepthAverage]

theorem negativeBesovVectorDepthAverage_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {F G : Vec d → Vec d}
    (hFG : F =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] G) (j : ℕ) :
    negativeBesovVectorDepthAverage Q F j =
      negativeBesovVectorDepthAverage Q G j := by
  rw [negativeBesovVectorDepthAverage_eq_cubeBesovNegativeVectorDepthAverage,
    negativeBesovVectorDepthAverage_eq_cubeBesovNegativeVectorDepthAverage]
  exact Homogenization.cubeBesovNegativeVectorDepthAverage_eq_of_ae_eq_on_cubeSet hFG j

theorem negativeBesovVectorDepthSeminorm_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {F G : Vec d → Vec d}
    (s : ℝ) (hFG : F =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] G) (j : ℕ) :
    negativeBesovVectorDepthSeminorm Q s F j =
      negativeBesovVectorDepthSeminorm Q s G j := by
  unfold negativeBesovVectorDepthSeminorm
  rw [negativeBesovVectorDepthAverage_eq_of_ae_eq_on_cubeSet hFG j]

theorem negativeBesovVectorPartialNormFinite_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {F G : Vec d → Vec d}
    (s q : ℝ) (N : ℕ)
    (hFG : F =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] G) :
    negativeBesovVectorPartialNormFinite Q s q N F =
      negativeBesovVectorPartialNormFinite Q s q N G := by
  unfold negativeBesovVectorPartialNormFinite
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [negativeBesovVectorDepthSeminorm_eq_of_ae_eq_on_cubeSet s hFG j]

theorem scaleNormalizedNegativeBesovVectorNorm_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {F G : Vec d → Vec d}
    (s : ℝ) (q : Ch02.MultiscaleExponent)
    (hFG : F =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] G) :
    scaleNormalizedNegativeBesovVectorNorm Q s q F =
      scaleNormalizedNegativeBesovVectorNorm Q s q G := by
  cases q with
  | finite q =>
      unfold scaleNormalizedNegativeBesovVectorNorm
      apply congrArg sSup
      ext y
      constructor
      · rintro ⟨N, rfl⟩
        exact ⟨N,
          (negativeBesovVectorPartialNormFinite_eq_of_ae_eq_on_cubeSet
            (Q := Q) (F := F) (G := G) s q N hFG).symm⟩
      · rintro ⟨N, rfl⟩
        exact ⟨N,
          negativeBesovVectorPartialNormFinite_eq_of_ae_eq_on_cubeSet
            (Q := Q) (F := F) (G := G) s q N hFG⟩
  | infinity =>
      unfold scaleNormalizedNegativeBesovVectorNorm
      apply congrArg sSup
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨j,
          (negativeBesovVectorDepthSeminorm_eq_of_ae_eq_on_cubeSet
            (Q := Q) (F := F) (G := G) s hFG j).symm⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j,
          negativeBesovVectorDepthSeminorm_eq_of_ae_eq_on_cubeSet
            (Q := Q) (F := F) (G := G) s hFG j⟩

theorem scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) :
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2) F =
      cubeBesovNegativeVectorSeminormTwo Q s F := by
  simp [scaleNormalizedNegativeBesovVectorNorm, negativeBesovVectorPartialNormFinite,
    negativeBesovVectorDepthSeminorm,
    Homogenization.cubeBesovNegativeVectorSeminormTwo,
    Homogenization.cubeBesovNegativeVectorPartialSeminormTwo,
    Homogenization.cubeBesovNegativeVectorDepthSeminorm,
    negativeBesovVectorDepthAverage_eq_cubeBesovNegativeVectorDepthAverage,
    Real.sqrt_eq_rpow]

theorem scaleNormalizedNegativeBesovVectorNorm_finite_one_eq_cubeBesovNegativeVectorSeminorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) :
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite 1) F =
      cubeBesovNegativeVectorSeminorm Q s F := by
  simp [scaleNormalizedNegativeBesovVectorNorm, negativeBesovVectorPartialNormFinite,
    negativeBesovVectorDepthSeminorm, negativeBesovVectorDepthAverage,
    Homogenization.cubeBesovNegativeVectorSeminorm,
    Homogenization.cubeBesovNegativeVectorPartialSeminorm,
    Homogenization.cubeBesovNegativeVectorDepthSeminorm,
    Homogenization.cubeBesovNegativeVectorDepthAverage,
    Real.rpow_one]

theorem publicDualBesovScaleWeight_eq_cubeBesovScaleWeight
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) :
    Real.rpow (3 : ℝ) (-s * (((Q.scale : ℤ) : ℝ))) =
      cubeBesovScaleWeight s Q := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  calc
    Real.rpow (3 : ℝ) (-s * (((Q.scale : ℤ) : ℝ)))
        = Real.rpow (3 : ℝ) ((((Q.scale : ℤ) : ℝ)) * (-s)) := by ring_nf
    _ = Real.rpow (Real.rpow (3 : ℝ) (((Q.scale : ℤ) : ℝ))) (-s) := by
          exact Real.rpow_mul h3.le (((Q.scale : ℤ) : ℝ)) (-s)
    _ = cubeBesovScaleWeight s Q := by
          simp [cubeBesovScaleWeight, cubeScaleFactor, Real.rpow_intCast]

theorem scaleNormalizedDualNegativeBesovVectorNormTwo_le_note_constant_mul_cubeBesovNegativeVectorSeminormTwo
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d)
    (hs : 0 < s) (hF : MemVectorL2 (cubeSet Q) F) :
    scaleNormalizedDualNegativeBesovVectorNormTwo Q s F ≤
      (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) *
        cubeBesovNegativeVectorSeminormTwo Q s F := by
  let B : ℝ := cubeBesovNegativeVectorSeminormTwo Q s F
  have hF_lp :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hF
  have hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N F) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs F hF_lp
  have hpartial : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N F ≤ B := by
    intro N
    unfold B cubeBesovNegativeVectorSeminormTwo
    exact le_csSup hBdd ⟨N, rfl⟩
  have hpConjTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [show cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) by
      simpa [cubeBesovConjExponent] using
        (ENNReal.HolderConjugate.conjExponent_eq
          (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))]
    norm_num
  have hcomponent :
      ∀ i : Fin d,
        cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F x i) ≤
          Real.rpow (3 : ℝ) ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * B) := by
    intro i
    have hFi :
        MeasureTheory.MemLp (fun x => F x i) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) :=
      memLp_component_of_memLp F i hF_lp
    have hdual :=
      cubeBesovDualFullNorm_le_note_constant_mul_cubeBesovCircNorm
        Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => F x i) hs hFi
        (by norm_num) (by norm_num) hpConjTop (by norm_num)
    have hcirc :=
      cubeBesovCircNorm_two_two_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBoundTwo
        Q s F i hpartial
    exact hdual.trans
      (mul_le_mul_of_nonneg_left hcirc
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
  have hsum :
      (∑ i : Fin d,
        cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
          (fun x => F x i)) ≤
        (d : ℝ) *
          (Real.rpow (3 : ℝ) ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * B)) := by
    calc
      (∑ i : Fin d,
        cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
          (fun x => F x i))
          ≤ ∑ _i : Fin d,
              Real.rpow (3 : ℝ) ((d : ℝ) + s) *
                (cubeBesovScaleWeight (-s) Q * B) := by
              exact Finset.sum_le_sum fun i _hi => hcomponent i
      _ = (d : ℝ) *
          (Real.rpow (3 : ℝ) ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * B)) := by
            simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  have hscale_nonneg : 0 ≤ cubeBesovScaleWeight s Q :=
    cubeBesovScaleWeight_nonneg s Q
  calc
    scaleNormalizedDualNegativeBesovVectorNormTwo Q s F
        = cubeBesovScaleWeight s Q *
          ∑ i : Fin d,
            cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
              (fun x => F x i) := by
            unfold scaleNormalizedDualNegativeBesovVectorNormTwo
            rw [publicDualBesovScaleWeight_eq_cubeBesovScaleWeight]
    _ ≤ cubeBesovScaleWeight s Q *
          ((d : ℝ) *
            (Real.rpow (3 : ℝ) ((d : ℝ) + s) *
              (cubeBesovScaleWeight (-s) Q * B))) :=
          mul_le_mul_of_nonneg_left hsum hscale_nonneg
    _ = (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) * B := by
          have hmul :
              cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q = 1 := by
            simpa [mul_comm] using cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight Q s
          rw [show cubeBesovScaleWeight s Q *
                ((d : ℝ) *
                  (Real.rpow (3 : ℝ) ((d : ℝ) + s) *
                    (cubeBesovScaleWeight (-s) Q * B))) =
              (cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q) *
                ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) * B) by ring,
            hmul]
          ring

theorem forcedSolutionFluxDefect_dualNorm_le_note_constant_mul_cubeBesovNegativeVectorSeminormTwo_publicCoeffField
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {a0 : ConstantCoeffMatrix d} {s : ℝ} {g : Vec d → Vec d}
    (u : ForcedCubeSolution Q a g) (hs : 0 < s) :
    scaleNormalizedDualNegativeBesovVectorNormTwo Q s
        (forcedSolutionFluxDefectField Q a a0 u) ≤
      (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) *
        cubeBesovNegativeVectorSeminormTwo Q s
          (fluxDefect (publicCoeffField Q a) a0.matrix
            (forcedSolutionGradientField u)) := by
  let F : Vec d → Vec d :=
    fluxDefect (publicCoeffField Q a) a0.matrix
      (forcedSolutionGradientField u)
  have hgrad : MemVectorL2 (cubeSet Q) (forcedSolutionGradientField u) :=
    forcedSolutionGradientField_memVectorL2_cubeSet u
  have hfluxA : MemVectorL2 (cubeSet Q)
      (fun x => matVecMul (publicCoeffField Q a x)
        (forcedSolutionGradientField u x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) hgrad
  have hEll0 :
      IsEllipticFieldOn a0.lam a0.Lam (cubeSet Q)
        (constantCoeffField a0.matrix) :=
    constantCoeffMatrix_isEllipticFieldOn_constantCoeffField a0
      (measurableSet_cubeSet Q)
  have hflux0 : MemVectorL2 (cubeSet Q)
      (fun x => matVecMul a0.matrix (forcedSolutionGradientField u x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll0 hgrad
  have hF_mem : MemVectorL2 (cubeSet Q) F := by
    dsimp [F, fluxDefect]
    exact hfluxA.sub hflux0
  have hnorm :=
    scaleNormalizedDualNegativeBesovVectorNormTwo_le_note_constant_mul_cubeBesovNegativeVectorSeminormTwo
      Q s F hs hF_mem
  have hae :
      forcedSolutionFluxDefectField Q a a0 u
        =ᵐ[volumeMeasureOn (cubeSet Q)] F := by
    simpa [F, forcedSolutionGradientField] using
      forcedSolutionFluxDefectField_ae_eq_fluxDefect_publicCoeffField_cubeSet
        (Q := Q) (a := a) (a0 := a0) u
  calc
    scaleNormalizedDualNegativeBesovVectorNormTwo Q s
        (forcedSolutionFluxDefectField Q a a0 u)
        = scaleNormalizedDualNegativeBesovVectorNormTwo Q s F :=
          scaleNormalizedDualNegativeBesovVectorNormTwo_eq_of_ae_eq_on_cubeSet
            (Q := Q) (F := forcedSolutionFluxDefectField Q a a0 u) (G := F) s hae
    _ ≤ (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) *
        cubeBesovNegativeVectorSeminormTwo Q s F := hnorm

theorem homogenizationComparisonNegativeBesovLHS_eq_solutionComparisonNegativeBesovLhs_publicCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    (a0 : ConstantCoeffMatrix d) (s : ℝ)
    (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    homogenizationComparisonNegativeBesovLHS Q a a0 s u v =
      solutionComparisonNegativeBesovLhs Q s (publicCoeffField Q a)
        a0.matrix u.grad v.grad := by
  let Gf : Vec d → Vec d :=
    fluxComparison (publicCoeffField Q a) a0.matrix u.grad v.grad
  have hflux_ae :
      homogenizationComparisonFluxField Q a a0 u v
        =ᵐ[volumeMeasureOn (cubeSet Q)] Gf := by
    simpa [Gf] using
      homogenizationComparisonFluxField_ae_eq_fluxComparison_publicCoeffField_cubeSet
        (Q := Q) (a := a) (a0 := a0) u v
  have hflux_eq :
      cubeBesovNegativeVectorSeminormTwo Q s
          (homogenizationComparisonFluxField Q a a0 u v) =
        cubeBesovNegativeVectorSeminormTwo Q s Gf :=
    cubeBesovNegativeVectorSeminormTwo_eq_of_ae_eq_on_cubeSet
      (Q := Q) (u := homogenizationComparisonFluxField Q a a0 u v)
      (v := Gf) s hflux_ae
  calc
    homogenizationComparisonNegativeBesovLHS Q a a0 s u v
        =
      cubeBesovNegativeVectorSeminormTwo Q s
          (constantGradientComparison a0.matrix u.grad v.grad) +
        cubeBesovNegativeVectorSeminormTwo Q s Gf := by
          unfold homogenizationComparisonNegativeBesovLHS
          rw [homogenizationComparisonConstantGradientField_eq_constantGradientComparison
            (Q := Q) (a0 := a0) u v, hflux_eq]
    _ =
      solutionComparisonNegativeBesovLhs Q s (publicCoeffField Q a)
        a0.matrix u.grad v.grad := by
          rfl

theorem homogenizationComparisonNegativeBesovLHS_le_note_constant_mul_solutionComparisonNegativeBesovLhs_publicCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    (a0 : ConstantCoeffMatrix d) (s : ℝ)
    (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (hs : 0 < s) :
    homogenizationComparisonNegativeBesovLHS Q a a0 s u v ≤
      (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) *
        solutionComparisonNegativeBesovLhs Q s (publicCoeffField Q a)
          a0.matrix u.grad v.grad := by
  let K : ℝ := (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s)
  let S : ℝ :=
    solutionComparisonNegativeBesovLhs Q s (publicCoeffField Q a)
      a0.matrix u.grad v.grad
  let Gc : Vec d → Vec d :=
    constantGradientComparison a0.matrix u.grad v.grad
  let Gf : Vec d → Vec d :=
    fluxComparison (publicCoeffField Q a) a0.matrix u.grad v.grad
  have hlhs_eq :
      homogenizationComparisonNegativeBesovLHS Q a a0 s u v = S := by
    dsimp [S]
    exact
      homogenizationComparisonNegativeBesovLHS_eq_solutionComparisonNegativeBesovLhs_publicCoeffField
        Q a a0 s u v
  have huGrad : MemVectorL2 (cubeSet Q) u.grad := by
    simpa using (publicH1ToCubeSet u).grad_memVectorL2
  have hvGrad : MemVectorL2 (cubeSet Q) v.grad := by
    simpa using (publicH1ToCubeSet v).grad_memVectorL2
  have hgradDiff : MemVectorL2 (cubeSet Q) (fun x => u.grad x - v.grad x) :=
    huGrad.sub hvGrad
  have hEll0 :
      IsEllipticFieldOn a0.lam a0.Lam (cubeSet Q)
        (constantCoeffField a0.matrix) :=
    constantCoeffMatrix_isEllipticFieldOn_constantCoeffField a0
      (measurableSet_cubeSet Q)
  have hGc_mem : MemVectorL2 (cubeSet Q) Gc := by
    simpa [Gc, constantGradientComparison, constantCoeffField] using!
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll0 hgradDiff
  have hfluxA : MemVectorL2 (cubeSet Q)
      (fun x => matVecMul (publicCoeffField Q a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) huGrad
  have hflux0 : MemVectorL2 (cubeSet Q)
      (fun x => matVecMul a0.matrix (v.grad x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll0 hvGrad
  have hGf_mem : MemVectorL2 (cubeSet Q) Gf := by
    dsimp [Gf, fluxComparison]
    exact hfluxA.sub hflux0
  have hGc_lp :
      MeasureTheory.MemLp Gc (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hGc_mem
  have hGf_lp :
      MeasureTheory.MemLp Gf (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hGf_mem
  have hS_nonneg : 0 ≤ S := by
    dsimp [S, solutionComparisonNegativeBesovLhs, Gc, Gf]
    exact add_nonneg
      (cubeBesovNegativeVectorSeminormTwo_nonneg_of_memLp Q hs Gc hGc_lp)
      (cubeBesovNegativeVectorSeminormTwo_nonneg_of_memLp Q hs Gf hGf_lp)
  have hK_ge_one : 1 ≤ K := by
    have hd_one : (1 : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    have hd_nonneg : 0 ≤ (d : ℝ) := by
      exact_mod_cast Nat.zero_le d
    have hpow_one :
        1 ≤ Real.rpow (3 : ℝ) ((d : ℝ) + s) := by
      exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) (by linarith)
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) :=
        mul_le_mul hd_one hpow_one (by norm_num) hd_nonneg
      _ = K := by rfl
  calc
    homogenizationComparisonNegativeBesovLHS Q a a0 s u v
        = S := hlhs_eq
    _ ≤ K * S := by
          calc
            S = 1 * S := by ring
            _ ≤ K * S := mul_le_mul_of_nonneg_right hK_ge_one hS_nonneg
    _ =
        (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) *
          solutionComparisonNegativeBesovLhs Q s (publicCoeffField Q a)
            a0.matrix u.grad v.grad := by
          rfl

theorem localizedHomogenizationFluxDefectAverage_eq_localizedFluxDefectNegativeBesovAverageTwo_publicCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    (a0 : ConstantCoeffMatrix d) (s : ℝ) (j : ℕ)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    localizedHomogenizationFluxDefectAverage Q a a0 s j u =
      localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect (publicCoeffField Q a) a0.matrix u.grad) j := by
  let Fpublic : TriadicCube d → ℝ := fun R =>
    (cubeBesovNegativeVectorSeminormTwo R s
      (homogenizationComparisonFluxDefectFromGradient R a a0 u.grad)) ^ 2
  let Finternal : TriadicCube d → ℝ := fun R =>
    (cubeBesovNegativeVectorSeminormTwo R s
      (fluxDefect (publicCoeffField Q a) a0.matrix u.grad)) ^ 2
  have havg : descendantsAverage Q j Fpublic = descendantsAverage Q j Finternal := by
    unfold descendantsAverage
    let D : Finset (TriadicCube d) := descendantsAtDepth Q j
    change ((D.card : ℝ)⁻¹) * D.sum Fpublic =
      ((D.card : ℝ)⁻¹) * D.sum Finternal
    refine congrArg (HMul.hMul _) ?_
    refine Finset.sum_congr rfl ?_
    intro R hR
    have hseminorm :
        cubeBesovNegativeVectorSeminormTwo R s
            (homogenizationComparisonFluxDefectFromGradient R a a0 u.grad) =
          cubeBesovNegativeVectorSeminormTwo R s
            (fluxDefect (publicCoeffField Q a) a0.matrix u.grad) :=
      cubeBesovNegativeVectorSeminormTwo_eq_of_ae_eq_on_cubeSet
        (Q := R)
        (u := homogenizationComparisonFluxDefectFromGradient R a a0 u.grad)
        (v := fluxDefect (publicCoeffField Q a) a0.matrix u.grad)
        s
        (homogenizationComparisonFluxDefectFromGradient_ae_eq_fluxDefect_parent_publicCoeffField_descendant_cubeSet
          (Q := Q) (R := R) (a := a) (a0 := a0) hR u.grad)
    simp [Fpublic, Finternal, hseminorm]
  simpa [localizedHomogenizationFluxDefectAverage,
    localizedFluxDefectNegativeBesovAverageTwo, Fpublic, Finternal] using
    congrArg Real.sqrt havg

theorem scaleNormalizedNegativeBesovVectorNorm_forcedSolutionFluxField_finite_two_eq_cubeBesovNegativeVectorSeminormTwo_publicCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    (s : ℝ) {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g) :
    scaleNormalizedNegativeBesovVectorNorm Q s (Ch02.MultiscaleExponent.finite 2)
        (forcedSolutionFluxField Q a u) =
      cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (publicCoeffField Q a x)
          (forcedSolutionGradientField u x)) := by
  let F : Vec d → Vec d :=
    fun x => matVecMul (publicCoeffField Q a x) (forcedSolutionGradientField u x)
  have hae :
      forcedSolutionFluxField Q a u =ᵐ[volumeMeasureOn (cubeSet Q)] F := by
    simpa [F, forcedSolutionGradientField] using
      forcedSolutionFluxField_ae_eq_publicCoeffField_cubeSet
        (Q := Q) (a := a) u
  calc
    scaleNormalizedNegativeBesovVectorNorm Q s (Ch02.MultiscaleExponent.finite 2)
        (forcedSolutionFluxField Q a u)
        = scaleNormalizedNegativeBesovVectorNorm Q s
            (Ch02.MultiscaleExponent.finite 2) F :=
          scaleNormalizedNegativeBesovVectorNorm_eq_of_ae_eq_on_cubeSet
            (Q := Q) (F := forcedSolutionFluxField Q a u) (G := F)
            s (Ch02.MultiscaleExponent.finite 2) hae
    _ = cubeBesovNegativeVectorSeminormTwo Q s F :=
          scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo
            Q s F

theorem scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} {g : Vec d → Vec d}
    (hg : ForceBesovRegularity Q s g) :
    0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by
  simpa [scaleNormalizedPositiveBesovVectorSeminormTwo] using
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s g
      hg.partialSeminorms_bddAbove


theorem coarseGrainingHomogenizationErrorAtDepth_publicCoeffField_eq_public
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    (a0 : ConstantCoeffMatrix d) (s : ℝ) (j : ℕ) :
    _root_.Homogenization.coarseGrainingHomogenizationErrorAtDepth
        Q (publicCoeffField Q a) a0.matrix s j =
      coarseGrainingHomogenizationErrorAtDepth Q a a0 s j := by
  unfold _root_.Homogenization.coarseGrainingHomogenizationErrorAtDepth
    coarseGrainingHomogenizationErrorAtDepth
  rw [Ch02.finsetSupReal_eq_finsetSsup]
  apply congrArg sSup
  ext y
  constructor
  · rintro ⟨R, hR, rfl⟩
    have hk : Q.scale - (j : ℤ) ≤ Q.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le j)
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      simpa using hR
    exact ⟨R, hR,
      (homogenizationErrorOnCube_parent_publicCoeffField_descendant_infinity_one_eq_ch02
        (a := a) hRscale s a0.matrix).symm⟩
  · rintro ⟨R, hR, rfl⟩
    have hk : Q.scale - (j : ℤ) ≤ Q.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le j)
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      simpa using hR
    exact ⟨R, hR,
      homogenizationErrorOnCube_parent_publicCoeffField_descendant_infinity_one_eq_ch02
        (a := a) hRscale s a0.matrix⟩

theorem weakFluxRHSBound_publicCoeffField_le_dim_sq_mul_public
    {d : ℕ} [NeZero d] (C : ℝ) (Q : TriadicCube d)
    (a : CoeffFamily d) {s : ℝ} {g : Vec d → Vec d}
    (u : ForcedCubeSolution Q a g) (hC : 0 ≤ C) (hs : 0 < s)
    (hB_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g) :
    C *
        (s⁻¹ *
            Real.sqrt (LambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
              (publicCoeffField Q a)) *
            Real.sqrt (cubeAverage Q
              (coefficientEnergyDensity (publicCoeffField Q a)
                (forcedSolutionGradientField u))) +
          Real.rpow s (-(5 / 2 : ℝ)) *
            Real.sqrt (LambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
              (publicCoeffField Q a)) *
            Real.sqrt ((lambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
              (publicCoeffField Q a))⁻¹) *
            cubeBesovPositiveVectorSeminormTwo Q s g) ≤
      weakFluxWithRHSRHS (((d : ℝ) ^ 2) * C) Q a s g u := by
  let D : ℝ := d
  let oldP : ℝ :=
    Real.sqrt (LambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
      (publicCoeffField Q a))
  let oldL : ℝ :=
    Real.sqrt ((lambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
      (publicCoeffField Q a))⁻¹)
  let P : ℝ := poincareUpperEllipticityFactor Q a (s / 2)
    (Ch02.MultiscaleExponent.finite 2)
  let L : ℝ := poincareLowerEllipticityFactor Q a (s / 2)
    (Ch02.MultiscaleExponent.finite 2)
  let E : ℝ :=
    Real.sqrt (cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q a)
        (forcedSolutionGradientField u)))
  let B : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  have hs_half : 0 < s / 2 := by positivity
  have hP_le : oldP ≤ D * P := by
    simpa [D, oldP, P] using
      sqrt_LambdaSq_publicCoeffField_finite_two_le_dim_mul_poincareUpperEllipticityFactor
        Q a hs_half
  have hL_le : oldL ≤ D * L := by
    simpa [D, oldL, L] using
      sqrt_lambdaSq_publicCoeffField_finite_two_inv_le_dim_mul_poincareLowerEllipticityFactor
        Q a hs_half
  have hE_eq : E = forcedSolutionEnergyNorm Q a u := by
    simpa [E] using
      (forcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
        (Q := Q) (a := a) u).symm
  have hD_one : 1 ≤ D := by
    norm_num [D, Nat.one_le_iff_ne_zero, NeZero.ne d]
  have hD_nonneg : 0 ≤ D := le_trans zero_le_one hD_one
  have hD_le_sq : D ≤ D ^ 2 := by nlinarith [hD_one]
  have hDsq_nonneg : 0 ≤ D ^ 2 := sq_nonneg D
  have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hs_pow_nonneg : 0 ≤ Real.rpow s (-(5 / 2 : ℝ)) :=
    Real.rpow_nonneg hs.le _
  have holdP_nonneg : 0 ≤ oldP := by simp [oldP]
  have holdL_nonneg : 0 ≤ oldL := by simp [oldL]
  have hP_nonneg : 0 ≤ P := by
    dsimp [P, poincareUpperEllipticityFactor]
    exact Real.rpow_nonneg
      (Ch02.LambdaSq_nonneg (Q := Q) (a := a)
        (q := Ch02.MultiscaleExponent.finite 2) hs_half (by norm_num)) _
  have hL_nonneg : 0 ≤ L := by
    dsimp [L, poincareLowerEllipticityFactor]
    exact Real.rpow_nonneg
      (Ch02.lambdaSq_nonneg (Q := Q) (a := a)
        (q := Ch02.MultiscaleExponent.finite 2) hs_half (by norm_num)) _
  have hE_nonneg : 0 ≤ E := by simp [E]
  have hterm_energy :
      s⁻¹ * oldP * E ≤ D ^ 2 * (s⁻¹ * P * E) := by
    calc
      s⁻¹ * oldP * E ≤ s⁻¹ * (D * P) * E := by
        gcongr
      _ = D * (s⁻¹ * P * E) := by ring
      _ ≤ D ^ 2 * (s⁻¹ * P * E) := by
        exact mul_le_mul_of_nonneg_right hD_le_sq
          (mul_nonneg (mul_nonneg hs_inv_nonneg hP_nonneg) hE_nonneg)
  have hprod :
      oldP * oldL ≤ (D * P) * (D * L) :=
    mul_le_mul hP_le hL_le holdL_nonneg (mul_nonneg hD_nonneg hP_nonneg)
  have hterm_force :
      Real.rpow s (-(5 / 2 : ℝ)) * oldP * oldL * B ≤
        D ^ 2 *
          (Real.rpow s (-(5 / 2 : ℝ)) * P * L * B) := by
    calc
      Real.rpow s (-(5 / 2 : ℝ)) * oldP * oldL * B =
          Real.rpow s (-(5 / 2 : ℝ)) * (oldP * oldL) * B := by ring
      _ ≤
          Real.rpow s (-(5 / 2 : ℝ)) * ((D * P) * (D * L)) * B := by
            gcongr
      _ =
          D ^ 2 * (Real.rpow s (-(5 / 2 : ℝ)) * P * L * B) := by ring
  have hsum :
      s⁻¹ * oldP * E +
          Real.rpow s (-(5 / 2 : ℝ)) * oldP * oldL * B ≤
        D ^ 2 *
          (s⁻¹ * P * E +
            Real.rpow s (-(5 / 2 : ℝ)) * P * L * B) := by
    calc
      s⁻¹ * oldP * E +
          Real.rpow s (-(5 / 2 : ℝ)) * oldP * oldL * B ≤
        D ^ 2 * (s⁻¹ * P * E) +
          D ^ 2 * (Real.rpow s (-(5 / 2 : ℝ)) * P * L * B) :=
          add_le_add hterm_energy hterm_force
      _ =
        D ^ 2 *
          (s⁻¹ * P * E +
            Real.rpow s (-(5 / 2 : ℝ)) * P * L * B) := by ring
  calc
    C *
        (s⁻¹ *
            Real.sqrt (LambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
              (publicCoeffField Q a)) *
            Real.sqrt (cubeAverage Q
              (coefficientEnergyDensity (publicCoeffField Q a)
                (forcedSolutionGradientField u))) +
          Real.rpow s (-(5 / 2 : ℝ)) *
            Real.sqrt (LambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
              (publicCoeffField Q a)) *
            Real.sqrt ((lambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
              (publicCoeffField Q a))⁻¹) *
            cubeBesovPositiveVectorSeminormTwo Q s g)
        =
        C * (s⁻¹ * oldP * E +
          Real.rpow s (-(5 / 2 : ℝ)) * oldP * oldL * B) := by
          simp [oldP, oldL, E, B]
    _ ≤
        C * (D ^ 2 *
          (s⁻¹ * P * E +
            Real.rpow s (-(5 / 2 : ℝ)) * P * L * B)) :=
          mul_le_mul_of_nonneg_left hsum hC
    _ =
        weakFluxWithRHSRHS (((d : ℝ) ^ 2) * C) Q a s g u := by
          unfold weakFluxWithRHSRHS
          simp [D, P, L, E, B, hE_eq, scaleNormalizedPositiveBesovVectorSeminormTwo]
          ring


end

end Ch03
end Book
end Homogenization
