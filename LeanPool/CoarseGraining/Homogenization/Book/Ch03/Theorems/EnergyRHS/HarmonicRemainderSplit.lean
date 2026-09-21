/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.EnergyRHS.HarmonicRemainder

/-! # Harmonic Remainder Split -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Energy RHS: harmonic remainder split wrappers

This file contains the terminal wrappers which turn the Dirichlet decomposition
into the zero-trace hypothesis required by the harmonic-remainder estimate.

## Audit tag

Claim: the manuscript Dirichlet split supplies the zero-trace boundary
difference, and hence the public harmonic-remainder estimate needed by the
Dirichlet energy assembly.

Downstream target: `EnergyRHS/Theory.lean`.  This file is endpoint assembly
only and introduces no public `*Theory` package.
-/

noncomputable section

open scoped ENNReal

/-- Direct public harmonic-remainder estimate from the zero-trace boundary
condition.  This combines weak testing, public Besov duality, and the
finite-depth homogeneous flux Poincare wrapper. -/
theorem dirichletHarmonicRemainder_sqrt_two_energy_le_of_zeroTrace
    {d : ℕ} [NeZero d] {C : ℝ}
    (hC_absorb :
      Real.sqrt 2 *
          (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
          ((d : ℝ) * Real.sqrt 5) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hboundary : ForceBesovRegularity Q s (dirichletBoundaryGradientField v))
    (hzero : IsPotentialZeroTraceOn (cubeSet Q)
      (fun x => w.toH1.grad x - dirichletBoundaryGradientField v x)) :
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => w.toH1.grad x))) ≤
      C * Real.rpow s (-(1 / 2 : ℝ)) *
        poincareUpperEllipticityFactor Q a s (.finite 2) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) :=
  dirichletHarmonicRemainder_sqrt_two_energy_le_of_zeroTrace_and_partial_flux_bound
    (C := C) (Cflux := (d : ℝ) * Real.sqrt 5)
    (mul_nonneg (by exact_mod_cast Nat.zero_le d) (Real.sqrt_nonneg 5)) hC_absorb
    (Q := Q) (a := a) (s := s) (g := g) v w hs hs_le hboundary hzero
    (by
      intro N
      simpa [neg_div] using
        dirichletHarmonicRemainder_fluxPartialSeminorm_le_poincareUpperEllipticityFactor
          (Q := Q) (a := a) (s := s) w N hs hs_le)

/-- The Dirichlet decomposition supplies the zero-trace boundary condition
needed by the homogeneous harmonic-remainder estimate.  Indeed
`w - h = (v - h) - ρ` at the gradient level on the cube, and both terms on the
right have zero trace. -/
theorem dirichletHarmonicRemainder_zeroTrace_boundaryDifference_of_split
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (hgrad :
      v.toH1.grad =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
        fun x => ρ.toH10.toH1Function.grad x + w.toH1.grad x) :
    IsPotentialZeroTraceOn (cubeSet Q)
      (fun x => w.toH1.grad x - dirichletBoundaryGradientField v x) := by
  let zgrad : Vec d → Vec d :=
    fun x => v.zeroTraceDifferenceH10CubeSet.toH1Function.grad x
  let rhograd : Vec d → Vec d := fun x => ρ.toH10.toH1Function.grad x
  let hgradBoundary : Vec d → Vec d := dirichletBoundaryGradientField v
  have hzpot : IsPotentialZeroTraceOn (cubeSet Q) zgrad := by
    simpa [zgrad] using v.zeroTraceDifferenceH10CubeSet.isPotentialZeroTraceOn
  have hrhopot : IsPotentialZeroTraceOn (cubeSet Q) rhograd := by
    simpa [rhograd] using ρ.toH10.isPotentialZeroTraceOn
  have hdiff_pot :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => zgrad x - rhograd x) := by
    have hsum :
        IsPotentialZeroTraceOn (cubeSet Q) (zgrad + (-1 : ℝ) • rhograd) :=
      isPotentialZeroTraceOn_add hzpot (isPotentialZeroTraceOn_smul hrhopot (-1))
    simpa [Pi.add_apply, Pi.smul_apply, sub_eq_add_neg] using! hsum
  have hz_ae :
      zgrad =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
        fun x => v.toH1.grad x - hgradBoundary x := by
    simpa [zgrad, hgradBoundary, dirichletBoundaryGradientField, volumeMeasureOn] using
      v.zeroTraceDifferenceH10CubeSet_grad_ae_eq
  have htarget :
      (fun x => zgrad x - rhograd x)
        =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
          fun x => w.toH1.grad x - hgradBoundary x := by
    filter_upwards [hz_ae, hgrad] with x hz hx
    ext i
    have hz_i :
        zgrad x i = v.toH1.grad x i - hgradBoundary x i :=
      congrArg (fun y : Vec d => y i) hz
    have hx_i :
        v.toH1.grad x i = rhograd x i + w.toH1.grad x i :=
      congrArg (fun y : Vec d => y i) hx
    simp [hz_i, hx_i, sub_eq_add_neg, add_comm, add_assoc]
  exact IsPotentialZeroTraceOn.congr_ae htarget hdiff_pot

/-- Harmonic-remainder estimate in the exact shape needed by the public
Dirichlet energy assembly.  The zero-trace condition is derived from the
manuscript split rather than passed as an extra public hypothesis. -/
theorem dirichletHarmonicRemainder_sqrt_two_energy_le_of_split
    {d : ℕ} [NeZero d] {C : ℝ}
    (hC_absorb :
      Real.sqrt 2 *
          (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
          ((d : ℝ) * Real.sqrt 5) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hboundary : ForceBesovRegularity Q s (dirichletBoundaryGradientField v))
    (hgrad :
      v.toH1.grad =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
        fun x => ρ.toH10.toH1Function.grad x + w.toH1.grad x) :
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => w.toH1.grad x))) ≤
      C * Real.rpow s (-(1 / 2 : ℝ)) *
        poincareUpperEllipticityFactor Q a s (.finite 2) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) :=
  dirichletHarmonicRemainder_sqrt_two_energy_le_of_zeroTrace
    (C := C) hC_absorb (Q := Q) (a := a) (s := s) (g := g) v w
    hs hs_le hboundary
    (dirichletHarmonicRemainder_zeroTrace_boundaryDifference_of_split
      (Q := Q) (a := a) (g := g) v ρ w hgrad)

end

end Ch03
end Book
end Homogenization
