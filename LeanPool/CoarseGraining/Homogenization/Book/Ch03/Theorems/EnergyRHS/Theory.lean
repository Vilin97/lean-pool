/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.EnergyRHS.Neumann
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.EnergyRHS.HarmonicRemainderSplit

/-! # Theory -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Energy RHS: Public theorem package

## Audit tag

Claim: expose the single public package for Dirichlet and mean-zero Neumann
energy consequences with right-hand side.

Downstream target: `InhomogeneousEquationsTheory`.  The remaining analytic
inputs belong in the Dirichlet/Neumann subfiles; this file should stay as the
package assembly endpoint.
-/

noncomputable section

open scoped ENNReal

/-- Public theorem package for the Dirichlet and mean-zero Neumann energy
consequences with right-hand side. -/
structure EnergyConsequencesRHSTheory (d : ℕ) [NeZero d] : Prop where
  exists_constant :
    ∃ C : ℝ, 0 < C ∧
      (∀ {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
        {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g),
        0 < s → s < 1 → ForceBesovRegularity Q s g →
          ForceBesovRegularity Q s (dirichletBoundaryGradientField v) →
            dirichletForcedSolutionEnergyNorm Q a v ≤
              dirichletEnergyWithRHSRHS C Q a s g v) ∧
      (∀ {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
        {g : Vec d → Vec d} (w : NeumannForcedCubeSolution Q a g),
        0 < s → s < 1 → ForceBesovRegularity Q s g →
          neumannForcedSolutionEnergyNorm Q a w ≤
            neumannEnergyWithRHSRHS C Q a s g)

/-- Conditional public theorem package for the Dirichlet and mean-zero Neumann
energy consequences with right-hand side.  The Neumann half is fully supplied
by the deterministic mean-zero corrector estimate; the remaining explicit
input is the dimension-only homogeneous boundary-remainder bound in the
Dirichlet manuscript decomposition. -/
private theorem energyConsequencesRHSTheory_of_dirichlet_harmonicRemainder_bound
    {d : ℕ} [NeZero d] {C₀ CneumannBase C : ℝ}
    (hC_pos : 0 < C)
    (hC₀_nonneg : 0 ≤ C₀)
    (hC₀_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C₀)
    (hC_absorb : 4 * ((d : ℝ) * C₀) ≤ C)
    (hC_neumann :
      Real.sqrt 500 *
          ((d : ℝ) *
            (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2)) ≤ CneumannBase)
    (hC_neumann_absorb : (d : ℝ) * CneumannBase ≤ C)
    (hharmonic :
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
        {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
        (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
        (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q)),
          0 < s → s < 1 → ForceBesovRegularity Q s g →
          ForceBesovRegularity Q s (dirichletBoundaryGradientField v) →
          v.toH1.grad =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
            (fun x => ρ.toH10.toH1Function.grad x + w.toH1.grad x) →
          Real.sqrt
              (2 * cubeAverage Q
                (coefficientEnergyDensity (publicCoeffField Q a)
                  (fun x => w.toH1.grad x))) ≤
            C * Real.rpow s (-(1 / 2 : ℝ)) *
              poincareUpperEllipticityFactor Q a s (.finite 2) *
              scaleNormalizedPositiveBesovVectorNormTwo Q s
                (dirichletBoundaryGradientField v)) :
    EnergyConsequencesRHSTheory d := by
  refine ⟨⟨C, hC_pos, ?_, ?_⟩⟩
  · intro Q a s g v hs hs_lt hg hboundary
    rcases
        exists_zeroTraceCorrector_harmonicRemainder_dirichletForcedSolutionEnergyNorm_le_dirichletEnergyWithRHSRHS_of_harmonicRemainder_bound
          (C₀ := C₀) (C := C) hC₀_nonneg hC₀_zero hC_absorb
          (Q := Q) (a := a) (s := s) (g := g) v hs hs_lt hg with
      ⟨ρ, w, hgrad, henergy⟩
    exact henergy
      (hharmonic (Q := Q) (a := a) (s := s) (g := g) v ρ w
        hs hs_lt hg hboundary hgrad)
  · intro Q a s g w hs hs_lt hg
    have hCneumannBase_nonneg : 0 ≤ CneumannBase := by
      have hraw_nonneg :
          0 ≤ Real.sqrt 500 *
            ((d : ℝ) *
              (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2)) := by
        exact mul_nonneg (Real.sqrt_nonneg 500)
          (mul_nonneg (by exact_mod_cast Nat.zero_le d)
            (mul_nonneg
              (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
              (Real.sqrt_nonneg 2)))
      exact le_trans
        hraw_nonneg hC_neumann
    have hbase :=
      neumannForcedSolutionEnergyNorm_le_publicRHS_of_constant
        (C := CneumannBase) hCneumannBase_nonneg hC_neumann
        (Q := Q) (a := a) (s := s) (g := g) w hs hs_lt hg
    have htail_nonneg :
        0 ≤ Real.rpow s (-(3 / 2 : ℝ)) *
          poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by
      have hlower_nonneg :
          0 ≤ poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) := by
        unfold poincareLowerEllipticityFactor
        exact Real.rpow_nonneg
          (Ch02.lambdaSq_finite_nonneg Q a (by nlinarith : 0 < s / 2)
            (by norm_num : (1 : ℝ) ≤ 2)) _
      have hseminorm_nonneg :
          0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q s g :=
        scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
          (Q := Q) (s := s) (g := g) hg
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hs.le _) hlower_nonneg)
        hseminorm_nonneg
    have hmono :
        neumannEnergyWithRHSRHS ((d : ℝ) * CneumannBase) Q a s g ≤
          neumannEnergyWithRHSRHS C Q a s g := by
      unfold neumannEnergyWithRHSRHS
      calc
        ((d : ℝ) * CneumannBase) *
            Real.rpow s (-(3 / 2 : ℝ)) *
            poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q s g
            =
          ((d : ℝ) * CneumannBase) *
            (Real.rpow s (-(3 / 2 : ℝ)) *
              poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) := by
            ring
        _ ≤
          C *
            (Real.rpow s (-(3 / 2 : ℝ)) *
              poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) :=
            mul_le_mul_of_nonneg_right hC_neumann_absorb htail_nonneg
        _ =
          C * Real.rpow s (-(3 / 2 : ℝ)) *
            poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by
            ring
    exact hbase.trans hmono

/-- Final public theorem package for the Dirichlet and mean-zero Neumann
energy estimates with right-hand side.  The Dirichlet branch follows the
manuscript route: zero-trace corrector energy, homogeneous weak testing,
Besov duality, homogeneous coarse flux Poincare, and scalar cancellation. -/
theorem energyConsequencesRHSTheory {d : ℕ} [NeZero d] :
    EnergyConsequencesRHSTheory d := by
  let CzeroBase : ℝ :=
    Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
      ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1))
  let C₀ : ℝ := max 0 CzeroBase
  let Charmonic : ℝ :=
    Real.sqrt 2 *
      (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
      ((d : ℝ) * Real.sqrt 5)
  let CneumannBase : ℝ :=
    Real.sqrt 500 *
      ((d : ℝ) * (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2))
  let Ccorrector : ℝ := 4 * ((d : ℝ) * C₀)
  let Cneumann : ℝ := (d : ℝ) * CneumannBase
  let C : ℝ := max 1 (max Ccorrector (max Charmonic Cneumann))
  have hC_pos : 0 < C := by
    exact lt_of_lt_of_le zero_lt_one
      (le_max_left 1 (max Ccorrector (max Charmonic Cneumann)))
  have hC₀_nonneg : 0 ≤ C₀ := by
    exact le_max_left 0 CzeroBase
  have hC₀_zero : CzeroBase ≤ C₀ := by
    exact le_max_right 0 CzeroBase
  have hC_absorb : 4 * ((d : ℝ) * C₀) ≤ C := by
    calc
      4 * ((d : ℝ) * C₀) = Ccorrector := rfl
      _ ≤ max Ccorrector (max Charmonic Cneumann) := le_max_left _ _
      _ ≤ C := le_max_right _ _
  have hC_harmonic : Charmonic ≤ C := by
    calc
      Charmonic ≤ max Charmonic Cneumann := le_max_left _ _
      _ ≤ max Ccorrector (max Charmonic Cneumann) := le_max_right _ _
      _ ≤ C := le_max_right _ _
  have hC_neumann_base : CneumannBase ≤ CneumannBase := le_rfl
  have hC_neumann : Cneumann ≤ C := by
    calc
      Cneumann ≤ max Charmonic Cneumann := le_max_right _ _
      _ ≤ max Ccorrector (max Charmonic Cneumann) := le_max_right _ _
      _ ≤ C := le_max_right _ _
  exact
    energyConsequencesRHSTheory_of_dirichlet_harmonicRemainder_bound
      (d := d) (C₀ := C₀) (CneumannBase := CneumannBase) (C := C)
      hC_pos hC₀_nonneg hC₀_zero hC_absorb hC_neumann_base hC_neumann
      (by
        intro Q a s g v ρ w hs hs_lt hg hboundary hgrad
        exact
          dirichletHarmonicRemainder_sqrt_two_energy_le_of_split
            (C := C) hC_harmonic
            (Q := Q) (a := a) (s := s) (g := g) v ρ w
            hs hs_lt.le hboundary hgrad)

end

end Ch03
end Book
end Homogenization
