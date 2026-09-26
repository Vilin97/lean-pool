/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApexZeroDirichletEnergy

/-! # RHSConstant Apex Zero Dirichlet Tail -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Zero-Dirichlet tail input for the RHS coarse-flux response apex

This leaf contains the zero-trace gradient-tail budget, the Poincare displayed
scalar budget, and the harmonic-remainder `BV` tail package used by the
corrected zero-Dirichlet §3.2.4 apex route.
-/

open scoped BigOperators ENNReal

/--
The expanded note-constant tail budget for the zero-trace correction gradient.
-/
noncomputable def zeroTraceDirichletGradientTailBudget {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (g : Vec d → Vec d) : ℝ :=
  250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
      zeroTraceDirichletEnergyEnvelope Q a s g +
    15000 * (s⁻¹) ^ 4 *
      ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
      ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
      (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2

theorem zeroTraceDirichletGradientTailBudget_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (g : Vec d → Vec d) (hs : 0 < s) :
    0 ≤ zeroTraceDirichletGradientTailBudget Q a s g := by
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have henergy_coeff_nonneg :
      0 ≤ 250 * (s⁻¹) ^ 2 *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (250 : ℝ)) (sq_nonneg (s⁻¹)))
        (inv_nonneg.mpr hlambda_nonneg)
  have henergy_nonneg :
      0 ≤ zeroTraceDirichletEnergyEnvelope Q a s g :=
    zeroTraceDirichletEnergyEnvelope_nonneg Q a s g hs
  have hs_inv_pow_four_nonneg : 0 ≤ (s⁻¹) ^ 4 := by
    rw [show (s⁻¹) ^ 4 = ((s⁻¹) ^ 2) ^ 2 by ring]
    exact sq_nonneg _
  have hforce_nonneg :
      0 ≤
        15000 * (s⁻¹) ^ 4 *
          ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num : 0 ≤ (15000 : ℝ)) hs_inv_pow_four_nonneg)
            (sq_nonneg ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)))
          (sq_nonneg ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))))
        (sq_nonneg (cubeBesovPositiveVectorSeminormTwo Q s g))
  unfold zeroTraceDirichletGradientTailBudget
  exact add_nonneg (mul_nonneg henergy_coeff_nonneg henergy_nonneg) hforce_nonneg

/--
The displayed Poincare scalar budget after inserting the zero-trace energy
envelope.
-/
noncomputable def zeroTraceDirichletPoincareDisplayedScalarBudget {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (g : Vec d → Vec d) : ℝ :=
  (matNorm a0) ^ 2 *
        (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          zeroTraceDirichletEnergyEnvelope Q a s g) +
      (matNorm a0) ^ 2 *
        (15000 * (s⁻¹) ^ 4 *
          ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)

theorem zeroTraceDirichletPoincareDisplayedScalarBudget_eq_scalarBudget
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (g : Vec d → Vec d) :
    zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g =
      zeroTraceDirichletPoincareScalarBudget Q a a0 s g := by
  rfl

theorem zeroTraceDirichletPoincareDisplayedScalarBudget_nonneg {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (g : Vec d → Vec d) (hs : 0 < s) :
    0 ≤ zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g := by
  rw [zeroTraceDirichletPoincareDisplayedScalarBudget_eq_scalarBudget]
  exact zeroTraceDirichletPoincareScalarBudget_nonneg Q a a0 s g hs

namespace ZeroTraceDirichletCorrectorData

/--
The expanded coarse-Poincare RHS estimate gives a uniform `S_k` tail bound for
the zero-trace corrector gradient after inserting the zero-Dirichlet energy
envelope.
-/
theorem coarsePoincareRHSSn_le_zeroTraceDirichletGradientTailBudget_noteConstants_expanded
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (m : ℕ) :
    coarsePoincareRHSSn Q s
        (fun x => ρ.toH10.toH1Function.grad x) m ≤
      zeroTraceDirichletGradientTailBudget Q a s g := by
  have hg_mem : MemVectorL2 (cubeSet Q) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q hg
  have hraw :
      coarsePoincareRHSSn Q s
          (fun x => ρ.toH10.toH1Function.grad x) m ≤
        250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a
              (fun x => ρ.toH10.toH1Function.grad x)) +
          15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 :=
    coarsePoincareRHSSn_le_intrinsicGlobalEnergyForce_noteConstants_expanded_of_parent_potential_solenoidal
      (Q := Q) (a := a) (g := g)
      (u := fun x => ρ.toH10.toH1Function.grad x)
      (s := s) (lam := lam) (Lam := Lam)
      hs hs_le hEll ρ.toH10.toH1Function.isPotentialOn
      (ρ.residualFlux_solenoidal hEll hg_mem) hg hGlobalBdd m
  have henergy :
      cubeAverage Q (coefficientEnergyDensity a
          (fun x => ρ.toH10.toH1Function.grad x)) ≤
        zeroTraceDirichletEnergyEnvelope Q a s g :=
    ρ.coefficientEnergy_average_le_zeroTraceDirichletEnergyEnvelope_noteConstants_expanded
      (s := s) (lam := lam) (Lam := Lam) hs hs_le hEll hg hGlobalBdd
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hcoeff_nonneg :
      0 ≤ 250 * (s⁻¹) ^ 2 *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (250 : ℝ)) (sq_nonneg (s⁻¹)))
        (inv_nonneg.mpr hlambda_nonneg)
  have henergy_term :
      250 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          cubeAverage Q (coefficientEnergyDensity a
            (fun x => ρ.toH10.toH1Function.grad x)) ≤
        250 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          zeroTraceDirichletEnergyEnvelope Q a s g :=
    mul_le_mul_of_nonneg_left henergy hcoeff_nonneg
  unfold zeroTraceDirichletGradientTailBudget
  exact hraw.trans (add_le_add henergy_term le_rfl)

theorem coarsePoincareRHSSn_tail_le_zeroTraceDirichletGradientTailBudget_noteConstants_expanded
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    ∀ k : ℕ,
      coarsePoincareRHSSn Q s
          (fun x => ρ.toH10.toH1Function.grad x) k ≤
        zeroTraceDirichletGradientTailBudget Q a s g := by
  intro k
  exact
    ρ.coarsePoincareRHSSn_le_zeroTraceDirichletGradientTailBudget_noteConstants_expanded
      (s := s) (lam := lam) (Lam := Lam) hs hs_le hEll hg hGlobalBdd k

/--
The named `BV` tail package for the harmonic remainders constructed from the
centered Neumann corrector decomposition on descendants of the parent cube.
-/
def zeroTraceDirichletHarmonicRemainderTailClose {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (s BV : ℝ) : Prop :=
  0 ≤ BV ∧
    ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
      ∀ ω : MeanZeroNeumannCorrectorData R a
          (fun x => g x - cubeAverageVec R g),
        ∀ w0 : AHarmonicFunction a (cubeSet R),
          (∀ x ∈ cubeSet R,
            ρ.toH10.toH1Function.grad x =
              w0.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
          BddAbove (Set.range fun N : ℕ =>
            cubeBesovNegativeVectorPartialSeminormTwo R s N
              (fun x => w0.toH1.grad x)) ∧
          (cubeBesovNegativeVectorSeminormTwo R s
            (fun x => w0.toH1.grad x)) ^ 2 ≤
            (coarsePoincareRHSDepthWeight s j)⁻¹ * BV

theorem zeroTraceDirichletHarmonicRemainderTailClose_nonneg {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} {ρ : ZeroTraceDirichletCorrectorData Q a g}
    {s BV : ℝ}
    (h : zeroTraceDirichletHarmonicRemainderTailClose ρ s BV) :
    0 ≤ BV :=
  h.1

theorem zeroTraceDirichletHarmonicRemainderTailClose_constructed {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} {ρ : ZeroTraceDirichletCorrectorData Q a g}
    {s BV : ℝ}
    (h : zeroTraceDirichletHarmonicRemainderTailClose ρ s BV) :
    ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
      ∀ ω : MeanZeroNeumannCorrectorData R a
          (fun x => g x - cubeAverageVec R g),
        ∀ w0 : AHarmonicFunction a (cubeSet R),
          (∀ x ∈ cubeSet R,
            ρ.toH10.toH1Function.grad x =
              w0.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
          BddAbove (Set.range fun N : ℕ =>
            cubeBesovNegativeVectorPartialSeminormTwo R s N
              (fun x => w0.toH1.grad x)) ∧
          (cubeBesovNegativeVectorSeminormTwo R s
            (fun x => w0.toH1.grad x)) ^ 2 ≤
            (coarsePoincareRHSDepthWeight s j)⁻¹ * BV :=
  h.2

theorem zeroTraceDirichletHarmonicRemainderTailClose_of_bounds {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s BV : ℝ}
    (hBV_nonneg : 0 ≤ BV)
    (hvConstructed :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          ∀ w0 : AHarmonicFunction a (cubeSet R),
            (∀ x ∈ cubeSet R,
              ρ.toH10.toH1Function.grad x =
                w0.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
            BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => w0.toH1.grad x)) ∧
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => w0.toH1.grad x)) ^ 2 ≤
              (coarsePoincareRHSDepthWeight s j)⁻¹ * BV) :
    zeroTraceDirichletHarmonicRemainderTailClose ρ s BV :=
  ⟨hBV_nonneg, hvConstructed⟩

end ZeroTraceDirichletCorrectorData

end

end Homogenization
