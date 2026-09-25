/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.DirichletEndpoint
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.NeumannEndpoint

/-!
# Dirichlet and Neumann Calderón--Zygmund endpoint

This file combines the arbitrary-cube Dirichlet and mean-zero Neumann
estimates under one positive real constant.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

/-- The Dirichlet and mean-zero Neumann divergence-form Calderón--Zygmund
estimates on arbitrary triadic cubes, with one constant depending only on the
dimension and finite exponent. -/
theorem exists_cubeDirichletNeumannDivergence_cz
    {d : ℕ} (dimension : 2 ≤ d)
    (p : ℝ≥0∞) (one_lt_p : 1 < p) (p_lt_top : p < ∞) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube d) (f : Vec d → Vec d),
        MemLp f p (normalizedCubeMeasure Q) →
          (∀ u : H10Function (openCubeSet Q),
              IsZeroTraceDirichletRhsWeakSolution
                  (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                  (openCubeSet Q) u (fun x => -f x) →
                MemLp u.toH1Function.grad p (normalizedCubeMeasure Q) ∧
                  cubeLpNorm Q p u.toH1Function.grad ≤ C * cubeLpNorm Q p f) ∧
          (∀ u : H1MeanZeroFunction (openCubeSet Q),
              IsMeanZeroNeumannRhsWeakSolution
                  (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                  (openCubeSet Q) u (fun x => -f x) →
                MemLp u.toH1Function.grad p (normalizedCubeMeasure Q) ∧
                  cubeLpNorm Q p u.toH1Function.grad ≤ C * cubeLpNorm Q p f) := by
  let : NeZero d := ⟨by omega⟩
  let q : FiniteLpExponent :=
    { exponent := p
      one_lt := one_lt_p
      lt_top := p_lt_top }
  obtain ⟨CD, hCDpos, hD⟩ := exists_cubeDirichletDivergence_cz d q
  obtain ⟨CN, hCNpos, hN⟩ := exists_cubeH1MeanZeroNeumannDivergence_cz d q
  let C : ℝ := max CD CN
  refine ⟨C, lt_of_lt_of_le hCDpos (le_max_left CD CN), ?_⟩
  intro Q f hf
  have hfq : MemLp f q.exponent (normalizedCubeMeasure Q) := by
    simpa only [q] using hf
  constructor
  · intro u hu
    obtain ⟨hgrad, hbound⟩ := hD Q f hfq u hu
    refine ⟨by simpa only [q] using hgrad, ?_⟩
    have henlarge : cubeLpNorm Q q.exponent u.toH1Function.grad ≤
        C * cubeLpNorm Q q.exponent f := by
      calc
        cubeLpNorm Q q.exponent u.toH1Function.grad ≤
            CD * cubeLpNorm Q q.exponent f := hbound
        _ ≤ C * cubeLpNorm Q q.exponent f :=
          mul_le_mul_of_nonneg_right (le_max_left CD CN)
            (cubeLpNorm_nonneg Q q.exponent f)
    simpa only [q] using henlarge
  · intro u hu
    obtain ⟨hgrad, hbound⟩ := hN Q f hfq u hu
    refine ⟨by simpa only [q] using hgrad, ?_⟩
    have henlarge : cubeLpNorm Q q.exponent u.toH1Function.grad ≤
        C * cubeLpNorm Q q.exponent f := by
      calc
        cubeLpNorm Q q.exponent u.toH1Function.grad ≤
            CN * cubeLpNorm Q q.exponent f := hbound
        _ ≤ C * cubeLpNorm Q q.exponent f :=
          mul_le_mul_of_nonneg_right (le_max_right CD CN)
            (cubeLpNorm_nonneg Q q.exponent f)
    simpa only [q] using henlarge

end CubeCalderonZygmund

end

end Homogenization
