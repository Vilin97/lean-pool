/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.LocalStep

/-! # Stepping -/

namespace Homogenization

noncomputable section

namespace ZeroTraceDirichletCorrectorData

variable {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_le_descendantsAverage_add_uCoeffEnergy_add_centeredCollapsedNoteTerm_two_two
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    {lam Lam : ℝ} (s : ℝ) {Bρ Bg : ℝ}
    (hs : 0 < s) (N : ℕ)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu_mem : MemVectorL2 (cubeSet Q) u)
    (hgrad :
      CubeAverageGradientEnergyControl Q a (fun x => w.toH1.grad x)
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hmem : MemVectorL2 (cubeSet Q) g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hgradρ : MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
      (2 : ENNReal) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => ρ.toH10.toH1Function.grad x) ≤ Bρ)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => g x - cubeAverageVec Q g) ≤ Bg) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
      2 *
        ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
          cubeAverage Q (coefficientEnergyDensity a u) +
      2 *
        ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Bρ * Bg)) := by
  have hρenergy :
      cubeAverage Q
          (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x)) ≤
        (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Bρ * Bg) :=
    ρ.coefficientEnergy_average_le_collapsed_note_term_centered_two_two
      s hs hmem hg hgradρ hBg hneg hpos
  exact
    ρ.sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_le_descendantsAverage_add_uCoeffEnergy_of_correctorCoeffEnergyBound
      (u := u) w s hs N hEll hu_mem hgrad hsum huw hρenergy


end ZeroTraceDirichletCorrectorData

end

end Homogenization
