/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34SliceIntegrated
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredCZResidual
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredResidual

/-!
# Theorem AAdapters Lin34

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN
namespace Core.Endgame

/-!
# Theorem A at the constant of `prop:lin34`

The small-data statement `thm:A` of `paper/ckn.tex` consumes the oscillation
display `eq:lin35-force` of `prop:lin34` with the constant attached to the
solution data.  This module fixes that constant,
`theoremALin34Constant q`, as the value `lin34SolutionForceExponent` of
`prop:lin34` evaluated at the Calderón--Zygmund constant `lin34CZConstant` of
`ext:CZ`, and records that it is nonnegative.

The adapter `theoremA_hLin34_of_sws` then restates `eq:lin35-force` in exactly
the shape `thm:A` expects, with no analytic hypothesis left: the Calderón--
Zygmund bound `ext:CZ` for the centred leading pressure term is supplied by
`lin34_hCZ_p1_of_residual_ae_of_sws`, whose Liouville decay input is the
content of `ext:newtonian`, itself discharged for suitable weak solutions by
`lin34_centred_residual_local_growth_ae_of_sws`.  Both are proved here rather
than assumed, so the only inputs of the exported display are the suitable
weak solution and the geometric side conditions on the cylinder.
-/

/-- The constant of the oscillation display `eq:lin35-force` of `prop:lin34`
for the solution data of `thm:A`, that is, the exponent constant
`lin34SolutionForceExponent` evaluated at the Calderón--Zygmund constant
`lin34CZConstant` of `ext:CZ`. -/
noncomputable def theoremALin34Constant (q : ℝ) : ℝ :=
  lin34ForceConstant (lin34SolutionForceExponent lin34CZConstant q)

/-- The constant of `eq:lin35-force` is nonnegative for every `q > 5/2`, the
range of exponents in which `prop:lin34` applies. -/
theorem theoremALin34Constant_nonneg (q : ℝ) (hq : 5 / 2 < q) :
    0 ≤ theoremALin34Constant q := by
  have hforce : 0 ≤ lin34ForceConstant (lin34ForceExponent lin34CZConstant) :=
    le_trans (lin34PointwiseConstant_nonneg lin34CZConstant_nonneg)
      (lin34_pointwiseConstant_le_forceConstant lin34CZConstant_nonneg)
  have hcyl : 0 ≤ lin34ForceCylinderConstant q ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (lin34ForceCylinderConstant_nonneg q hq) _
  have hC : 0 ≤ lin34SolutionForceExponent lin34CZConstant q := by
    unfold lin34SolutionForceExponent
    exact Real.rpow_nonneg (mul_nonneg hforce (by linarith only [hcyl])) _
  dsimp only [theoremALin34Constant]
  exact mul_nonneg (Real.sqrt_nonneg _)
    (add_nonneg (by norm_num) (Real.rpow_nonneg hC _))

/-- **`eq:lin35-force` of `prop:lin34` in the shape consumed by `thm:A`.**  For
a suitable weak solution, concentric parabolic cylinders with `r ≤ ρ/2`, and
`Q_ρ(z₀)` contained in the space-time domain, the inner pressure oscillation is
bounded by `theoremALin34Constant q` times the outer velocity oscillation, the
outer pressure oscillation and the force term `λ(z₀,ρ)^{3/2}`.  The
Calderón--Zygmund bound `ext:CZ` is not assumed: it is derived from the
Liouville decay of `ext:newtonian`, so no analytic hypothesis remains. -/
theorem theoremA_hLin34_of_sws (q : ℝ) :
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
      r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      pressureD p z r ≤ theoremALin34Constant q *
        ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ +
          (r / ρ) * pressureD p z ρ +
          (r / ρ) ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ)) := by
  intro Ω I u Du p f hsol z r ρ hρ hr hhalf hsub
  exact pressure_lin34_force_lambda_of_sws lin34CZConstant lin34CZConstant_nonneg
    hsol hρ hr hhalf hsub
    (lin34_hCZ_p1_of_residual_ae_of_sws hsol hρ hsub
      (lin34_centred_residual_local_growth_ae_of_sws hsol hρ hsub))

end Core.Endgame
end CKN
