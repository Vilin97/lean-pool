/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowDivergence
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowExpansionResidual
import LeanPool.NavierStokesAndEuler.NavierStokes.LocalAxisymmetricResidual
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The leading stress and its genuine divergence

The lag variables in this file are the regular primitives constructed in
`ProfileHistories`. Every profile and physical derivative is a Fréchet
derivative. The physical identities keep the axial-viscosity remainder.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.LeadingStress

open ProfileHistories
open SimilarityProfile (partialX partialEta pullback inner)
open CoordinateAlgebra (A L)
open scoped Topology ContDiff

variable {Ω : RadialDomain} (P : Profiles Ω)

/-- The angular source `S_q`; `Profiles.angularSource` is `H S_q`. -/
noncomputable def sourceTheta (h : ℝ) (w : Point) : ℝ :=
  P.angularSource h w / P.H w

/-- The axial source `S_n`. -/
noncomputable def sourceAxial (h : ℝ) (w : Point) : ℝ := P.axialSource h w

/-- The coefficient of the angular radial stress in Proposition 3.2. -/
noncomputable def theta (h : ℝ) (w : Point) : ℝ :=
  P.f w * w.1 * P.angularLag h w / L h w.2 + 2 * w.1 * partialX P.f w

/-- The coefficient of the axial radial stress in Proposition 3.2. -/
noncomputable def axial (h : ℝ) (w : Point) : ℝ :=
  Real.sqrt (2 * w.1) * (partialX P.U w + P.axialLag h w / (2 * L h w.2))

/-- Slope A, given by `-2 * w.1 * partialX P.f w / P.f w`. -/
noncomputable def slopeA (w : Point) : ℝ := -2 * w.1 * partialX P.f w / P.f w
/-- Slope B, given by `2 * w.1 * partialX P.U w / P.E w`. -/
noncomputable def slopeB (w : Point) : ℝ := 2 * w.1 * partialX P.U w / P.E w

theorem theta_eq_lag_minus_slope (h : ℝ) {w : Point} (hf : P.f w ≠ 0) :
    theta P h w = P.f w * (w.1 * P.angularLag h w / L h w.2 - slopeA P w) := by
  unfold theta slopeA
  field_simp; ring

theorem axial_eq_lag_plus_slope (h : ℝ) {w : Point} (hX : 0 < w.1)
    (hf : P.f w ≠ 0) :
    axial P h w = P.f w *
      (w.1 * P.axialLag h w / (L h w.2 * P.E w) + slopeB P w) := by
  have hr : Real.sqrt (2 * w.1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hr2 : Real.sqrt (2 * w.1) ^ 2 = 2 * w.1 := Real.sq_sqrt (by positivity)
  unfold axial slopeB Profiles.E
  generalize hrdef : Real.sqrt (2 * w.1) = r at *
  by_cases hL : L h w.2 = 0
  · simp only [hL, mul_zero, zero_mul, div_zero, add_zero, zero_add]
    field_simp
    linear_combination partialX P.U w * hr2
  · field_simp
    linear_combination (2 * L h w.2 * partialX P.U w + P.axialLag h w) * hr2

theorem partialX_hasDerivAt {f : Field} {w : Point} (hf : DifferentiableAt ℝ f w) :
    HasDerivAt (fun x => f (x, w.2)) (partialX f w) w.1 := by
  exact hf.hasFDerivAt.comp_hasDerivAt w.1
    ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))

theorem partialX_H {w : Point} (hw : w ∈ Ω.carrier) :
    partialX P.H w = 2 * P.f w + 2 * w.1 * partialX P.f w := by
  have hf := partialX_hasDerivAt (P.f_smooth.differentiableOn (by simp) w hw
    |>.differentiableAt (Ω.isOpen.mem_nhds hw))
  have hH := partialX_hasDerivAt (P.H_smooth.differentiableOn (by simp) w hw
    |>.differentiableAt (Ω.isOpen.mem_nhds hw))
  have hd := ((hasDerivAt_id w.1).const_mul 2).mul hf
  exact (hH.unique hd).trans (by simp)

theorem theta_smoothAt (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : w.1 ≠ 0) (hf : P.f w ≠ 0) (hL : L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (theta P h) w := by
  have hff := P.f_smooth.contDiffAt (Ω.isOpen.mem_nhds hw)
  have hfx : ContDiffAt ℝ ∞ (partialX P.f) w :=
    (radialPartial_smooth Ω P.f_smooth).contDiffAt (Ω.isOpen.mem_nhds hw)
  have hq := P.angularLag_smoothAt h hw hX (P.H_ne_zero hX hf)
  have hl : ContDiffAt ℝ ∞ (fun v : Point => L h v.2) w :=
    contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))
  exact ((((hff.mul contDiffAt_fst).mul hq).div hl hL).add
    ((contDiffAt_const.mul contDiffAt_fst).mul hfx))

theorem axial_smoothAt (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : w.1 ≠ 0) (hL : L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (axial P h) w := by
  have hux : ContDiffAt ℝ ∞ (partialX P.U) w :=
    (radialPartial_smooth Ω P.U_smooth).contDiffAt (Ω.isOpen.mem_nhds hw)
  have hn := P.axialLag_smoothAt h hw hX
  have hl : ContDiffAt ℝ ∞ (fun v : Point => 2 * L h v.2) w :=
    contDiffAt_const.mul (contDiffAt_const.sub
      (contDiffAt_const.mul (contDiffAt_snd.pow 2)))
  exact ((contDiffAt_const.mul contDiffAt_fst).sqrt (mul_ne_zero (by norm_num) hX)).mul
    (hux.add (hn.div hl (mul_ne_zero (by norm_num) hL)))

theorem partialX_theta (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : w.1 ≠ 0) (hf : P.f w ≠ 0) (hL : L h w.2 ≠ 0) :
    partialX (theta P h) w =
      (partialX P.f w * w.1 * P.angularLag h w + P.f w * P.angularLag h w +
        P.f w * w.1 * partialX (P.angularLag h) w) / L h w.2 +
        2 * partialX P.f w + 2 * w.1 * partialX (partialX P.f) w := by
  have hf' := partialX_hasDerivAt
    ((P.f_smooth.contDiffAt (Ω.isOpen.mem_nhds hw)).differentiableAt (by simp))
  have hfx : HasDerivAt (fun x => partialX P.f (x, w.2))
      (partialX (partialX P.f) w) w.1 := partialX_hasDerivAt
    (((radialPartial_smooth Ω P.f_smooth).contDiffAt
      (Ω.isOpen.mem_nhds hw)).differentiableAt (by simp))
  have hq := partialX_hasDerivAt
    ((P.angularLag_smoothAt h hw hX (P.H_ne_zero hX hf)).differentiableAt (by simp))
  have hd := (((hf'.fun_mul (hasDerivAt_id w.1)).fun_mul hq).div_const (L h w.2)).fun_add
    (((hasDerivAt_id w.1).const_mul 2).fun_mul hfx)
  have ht := partialX_hasDerivAt
    ((theta_smoothAt P h hw hX hf hL).differentiableAt (by simp))
  exact (ht.unique hd).trans (by simp only [id_eq, Prod.eta, mul_one]; ring)

/-- The unweighted angular identity, using the actual regular lag equation. -/
theorem theta_divergence_coefficient (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : w.1 ≠ 0) (hf : P.f w ≠ 0) (hL : L h w.2 ≠ 0) :
    partialX (theta P h) w + theta P h w / w.1 =
      P.f w * sourceTheta P h w / L h w.2 +
        2 * (w.1 * partialX (partialX P.f) w + 2 * partialX P.f w) := by
  have hq := P.angularLag_smoothAt h hw hX (P.H_ne_zero hX hf)
  have he := P.angularLag_equation h hw hX (P.H_ne_zero hX hf)
  rw [(partialX_hasDerivAt (hq.differentiableAt (by simp))).deriv] at he
  change w.1 * partialX (P.angularLag h) w +
    (1 + w.1 * partialX P.H w / P.H w) * P.angularLag h w = sourceTheta P h w at he
  rw [partialX_theta P h hw hX hf hL, ← he, partialX_H P hw]
  unfold theta Profiles.H
  field_simp; ring

/-- The angular profile divergence in Proposition 3.2. -/
theorem theta_divergence (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : 0 < w.1) (hf : P.f w ≠ 0) (hL : L h w.2 ≠ 0) :
    Real.sqrt (2 * w.1) * (partialX (theta P h) w + theta P h w / w.1) =
      Real.sqrt (2 * w.1) * (P.f w * sourceTheta P h w / L h w.2 +
        2 * (w.1 * partialX (partialX P.f) w + 2 * partialX P.f w)) := by
  rw [theta_divergence_coefficient P h hw hX.ne' hf hL]

theorem partialX_axial (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : 0 < w.1) (hL : L h w.2 ≠ 0) :
    partialX (axial P h) w =
      (partialX P.U w + P.axialLag h w / (2 * L h w.2)) / Real.sqrt (2 * w.1) +
      Real.sqrt (2 * w.1) * (partialX (partialX P.U) w +
        partialX (P.axialLag h) w / (2 * L h w.2)) := by
  have hux : HasDerivAt (fun x => partialX P.U (x, w.2))
      (partialX (partialX P.U) w) w.1 := partialX_hasDerivAt
    (((radialPartial_smooth Ω P.U_smooth).contDiffAt
      (Ω.isOpen.mem_nhds hw)).differentiableAt (by simp))
  have hn := partialX_hasDerivAt
    ((P.axialLag_smoothAt h hw hX.ne').differentiableAt (by simp))
  have hr := (Real.hasDerivAt_sqrt (show 2 * w.1 ≠ 0 by positivity)).comp w.1
    ((hasDerivAt_id w.1).const_mul 2)
  have hd := hr.fun_mul (hux.fun_add (hn.div_const (2 * L h w.2)))
  have ht := partialX_hasDerivAt
    ((axial_smoothAt P h hw hX.ne' hL).differentiableAt (by simp))
  exact (ht.unique hd).trans (by
    simp only [Prod.eta, mul_one, Function.comp_apply]
    ring)

/-- The axial profile divergence, obtained from the primitive-defined `N_s`. -/
theorem axial_divergence (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : 0 < w.1) (hL : L h w.2 ≠ 0) :
    Real.sqrt (2 * w.1) * partialX (axial P h) w +
        axial P h w / Real.sqrt (2 * w.1) =
      sourceAxial P h w / L h w.2 +
        2 * (w.1 * partialX (partialX P.U) w + partialX P.U w) := by
  have hn := P.axialLag_smoothAt h hw hX.ne'
  have he := P.axialLag_equation h hw hX.ne'
  rw [(partialX_hasDerivAt (hn.differentiableAt (by simp))).deriv] at he
  change w.1 * partialX (P.axialLag h) w + P.axialLag h w = sourceAxial P h w at he
  have hr : Real.sqrt (2 * w.1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hr2 : Real.sqrt (2 * w.1) ^ 2 = 2 * w.1 := Real.sq_sqrt (by positivity)
  rw [partialX_axial P h hw hX hL, ← he]
  unfold axial
  generalize hrdef : Real.sqrt (2 * w.1) = r at *
  have hr4 : r ^ 4 = 4 * w.1 ^ 2 := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = (2 * w.1) ^ 2 := by rw [hr2]
      _ = _ := by ring
  field_simp
  ring_nf
  simp only [hr2]
  ring

/-- The coefficient of the angular inviscid residual is the negative lag source. -/
theorem theta_transport_coefficient (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : w.1 ≠ 0) (hf : P.f w ≠ 0) (hL : L h w.2 ≠ 0) :
    SimilarityProfile.T h (-A h - 1 / 2) P.f w +
        SlowDivergence.radialFlux h 0 P.U w * (partialX P.f w + P.f w / w.1) +
        P.U w * SimilarityProfile.Z h (-A h - 1 / 2) P.f w =
      -P.f w * sourceTheta P h w / L h w.2 := by
  have hHx : radialPartial P.H w = 2 * P.f w + 2 * w.1 * partialX P.f w :=
    partialX_H P hw
  unfold sourceTheta Profiles.angularSource StressAlgebra.angularSource
  rw [hHx, P.parameterPartial_H hw, P.W_formula h hw]
  dsimp [SimilarityProfile.T, SimilarityProfile.Z, CoordinateAlgebra.timeCoeff,
    CoordinateAlgebra.axialCoeff, SlowDivergence.radialFlux, Profiles.H, Profiles.Ubar,
    CoordinateAlgebra.A, CoordinateAlgebra.D, StressAlgebra.axialExponent,
    StressAlgebra.coordinateFactor, CoordinateAlgebra.d, partialX, partialEta,
    radialPartial, parameterPartial]
  field_simp; ring

/-- The axial inviscid residual includes the actual derivative of the constructed pressure. -/
theorem axial_transport_coefficient (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hL : L h w.2 ≠ 0) :
    SimilarityProfile.T h (-A h) P.U w +
        SlowDivergence.radialFlux h 0 P.U w * partialX P.U w +
        P.U w * SimilarityProfile.Z h (-A h) P.U w +
        SimilarityProfile.Z h (-2 * A h) P.pressure w =
      -sourceAxial P h w / L h w.2 := by
  have hπ : partialX P.pressure w = P.f w ^ 2 := P.radialPartial_pressure hw
  unfold sourceAxial Profiles.axialSource StressAlgebra.axialSource
  dsimp [SimilarityProfile.T, SimilarityProfile.Z, CoordinateAlgebra.timeCoeff,
    CoordinateAlgebra.axialCoeff]
  rw [hπ, P.W_formula h hw]
  dsimp [SlowDivergence.radialFlux, Profiles.Ubar, CoordinateAlgebra.A, CoordinateAlgebra.D,
    StressAlgebra.axialExponent, StressAlgebra.velocityExponent, StressAlgebra.coordinateFactor,
    CoordinateAlgebra.d, partialX, partialEta, radialPartial, parameterPartial]
  field_simp; ring

/-- The exact zeroth-order transport formula. The added term is the full
axial viscosity, not an estimate or a discarded remainder. -/
theorem transport_pullback_add_axialViscosity {h e : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (α m : ℝ) (v u f source : Field) {p : SimilarityProfile.PhysicalPoint}
    (hp : p.1 < 1) (hs : 0 < p.2.1) (hf : ContDiffAt ℝ 2 f (inner h p)) :
    SlowExpansionResidual.transportResidual α m (pullback h 0 v) (pullback h (-A h) u)
        (pullback h e f) (pullback h (e - 1) source) p +
        SimilarityProfile.partialZ (SimilarityProfile.partialZ (pullback h e f)) p =
      SimilarityProfile.q h p ^ (e - 1) *
        (SimilarityProfile.T h e f (inner h p) +
          v (inner h p) * (partialX f (inner h p) + α * f (inner h p) / (inner h p).1) +
          u (inner h p) * SimilarityProfile.Z h e f (inner h p) -
          2 * ((inner h p).1 * partialX (partialX f) (inner h p) + m * partialX f (inner h p)) +
          source (inner h p)) := by
  have he := SlowExpansionResidual.transport_finiteProfile (e := e) hh hh1 0 α m
    (fun _ => v) (fun _ => u) (fun _ => f) (fun _ => source) hp hs (fun _ _ => hf)
  simp only [SlowExpansionResidual.finiteProfile_order_zero,
    SlowExpansionResidual.finiteSeries_order_zero, SlowExpansionResidual.transportTail_order_zero,
    SlowExpansionResidual.transportCoefficient, SlowExpansionResidual.recurrence,
    SlowExpansionResidual.previous_zero, sub_zero, SlowExpansionResidual.convolution,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton, SlowExpansionResidual.slowOrder_zero,
    add_zero, SlowExpansionResidual.transportLinear, SlowExpansionResidual.transportPair] at he
  rw [he, SimilarityProfile.partialZ_partialZ_pullback hh hh1 hp hf]
  have hexp : e - 2 * CoordinateAlgebra.D h = e - 1 + 2 * h := by
    unfold CoordinateAlgebra.D
    ring
  rw [hexp]
  unfold pullback SlowExpansionResidual.Z2
  ring

/-- Cylindrical radial divergence `(∂r + k/r)S`, in the regular coordinate `s=r²/2`. -/
noncomputable def radialDivergence (k : ℝ) (S : SimilarityProfile.PhysicalProfile)
    (p : SimilarityProfile.PhysicalPoint) : ℝ :=
  Real.sqrt (2 * p.2.1) * SimilarityProfile.partialS S p +
    k * S p / Real.sqrt (2 * p.2.1)

/-- The regular-coordinate radial derivative is the derivative of the actual
cylindrical slice, with the radius variable reconstructed by `s=r²/2`. -/
theorem hasDerivAt_radialSlice {S : SimilarityProfile.PhysicalProfile}
    {p : SimilarityProfile.PhysicalPoint} (hs : 0 ≤ p.2.1) (hS : DifferentiableAt ℝ S p) :
    HasDerivAt (fun r => S (p.1, (r ^ 2 / 2, p.2.2)))
      (Real.sqrt (2 * p.2.1) * SimilarityProfile.partialS S p) (Real.sqrt (2 * p.2.1)) := by
  let r := Real.sqrt (2 * p.2.1)
  have hr2 : r ^ 2 = 2 * p.2.1 := Real.sq_sqrt (by positivity)
  have hpoint : (p.1, (r ^ 2 / 2, p.2.2)) = p := by
    rw [hr2]
    simp
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2 / 2) r r := by
    apply (((hasDerivAt_id r).pow 2).div_const 2).congr_deriv
    simp
  have hc := (hasDerivAt_const r p.1).prodMk (hsq.prodMk (hasDerivAt_const r p.2.2))
  have hS' : DifferentiableAt ℝ S (p.1, (r ^ 2 / 2, p.2.2)) := by
    rw [hpoint]
    exact hS
  have hd := hS'.hasFDerivAt.comp_hasDerivAt r hc
  change HasDerivAt (fun y => S (p.1, (y ^ 2 / 2, p.2.2)))
    ((fderiv ℝ S (p.1, (r ^ 2 / 2, p.2.2))) (0, (r, 0))) r at hd
  rw [hpoint] at hd
  apply hd.congr_deriv
  rw [show (0, (r, 0)) = r • ((0, (1, 0)) : SimilarityProfile.PhysicalPoint) by ext <;> simp]
  rw [map_smul]
  rfl

theorem radialDivergence_eq_deriv (k : ℝ) {S : SimilarityProfile.PhysicalProfile}
    {p : SimilarityProfile.PhysicalPoint} (hs : 0 ≤ p.2.1) (hS : DifferentiableAt ℝ S p) :
    radialDivergence k S p =
      deriv (fun r => S (p.1, (r ^ 2 / 2, p.2.2))) (Real.sqrt (2 * p.2.1)) +
        k * S p / Real.sqrt (2 * p.2.1) := by
  rw [(hasDerivAt_radialSlice hs hS).deriv]
  rfl

theorem physical_radius {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) :
    Real.sqrt (2 * p.2.1) = SimilarityProfile.q h p ^ (1 / (2 : ℝ)) *
      Real.sqrt (2 * (inner h p).1) := by
  rw [← SlowExpansionResidual.q_mul_X hh hh1 hp,
    show 2 * (SimilarityProfile.q h p * (inner h p).1) =
      SimilarityProfile.q h p * (2 * (inner h p).1) by ring,
    Real.sqrt_mul (SimilarityProfile.q_pos hh hh1 hp).le, Real.sqrt_eq_rpow]

/-- The physical stress scaling produces exactly the cylindrical profile divergence. -/
theorem radialDivergence_pullback {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (k : ℝ) {S : Field} {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1)
    (hS : DifferentiableAt ℝ S (inner h p)) :
    radialDivergence k (pullback h b S) p = SimilarityProfile.q h p ^ (b - 1 / 2) *
      (Real.sqrt (2 * (inner h p).1) * partialX S (inner h p) +
        k * S (inner h p) / Real.sqrt (2 * (inner h p).1)) := by
  have hq := SimilarityProfile.q_pos hh hh1 hp
  have hprod : SimilarityProfile.q h p ^ (1 / (2 : ℝ)) *
      SimilarityProfile.q h p ^ (b - 1) = SimilarityProfile.q h p ^ (b - 1 / 2) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  have hdiv : SimilarityProfile.q h p ^ b / SimilarityProfile.q h p ^ (1 / (2 : ℝ)) =
      SimilarityProfile.q h p ^ (b - 1 / 2) := (Real.rpow_sub hq _ _).symm
  unfold radialDivergence
  rw [SimilarityProfile.partialS_pullback hh hh1 hp hS, physical_radius hh hh1 hp]
  unfold pullback
  calc
    _ = (SimilarityProfile.q h p ^ (1 / (2 : ℝ)) * SimilarityProfile.q h p ^ (b - 1)) *
        (Real.sqrt (2 * (inner h p).1) * partialX S (inner h p)) +
        (SimilarityProfile.q h p ^ b / SimilarityProfile.q h p ^ (1 / (2 : ℝ))) *
          (k * S (inner h p) / Real.sqrt (2 * (inner h p).1)) := by ring
    _ = _ := by rw [hprod, hdiv]; ring

theorem radius_mul_rpow {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (b : ℝ) {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) :
    Real.sqrt (2 * p.2.1) * SimilarityProfile.q h p ^ b =
      SimilarityProfile.q h p ^ (b + 1 / 2) * Real.sqrt (2 * (inner h p).1) := by
  rw [physical_radius hh hh1 hp]
  calc
    _ = (SimilarityProfile.q h p ^ (1 / (2 : ℝ)) * SimilarityProfile.q h p ^ b) *
        Real.sqrt (2 * (inner h p).1) := by ring
    _ = _ := by rw [← Real.rpow_add (SimilarityProfile.q_pos hh hh1 hp), add_comm]

theorem sqrt_radial_two {X : ℝ} (hX : 0 < X) (S SX : ℝ) :
    Real.sqrt (2 * X) * SX + 2 * S / Real.sqrt (2 * X) =
      Real.sqrt (2 * X) * (SX + S / X) := by
  have hr : Real.sqrt (2 * X) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hr2 : Real.sqrt (2 * X) ^ 2 = 2 * X := Real.sq_sqrt (by positivity)
  generalize hrdef : Real.sqrt (2 * X) = r at *
  field_simp
  ring_nf
  rw [hr2]
  ring

/-- Flux profile, given by `pullback h 0 (SlowDivergence.radialFlux h 0 P.U)`. -/
noncomputable def fluxProfile (h : ℝ) : SimilarityProfile.PhysicalProfile :=
  pullback h 0 (SlowDivergence.radialFlux h 0 P.U)

/-- Swirl profile, given by `pullback h (-A h - 1 / 2) P.f`. -/
noncomputable def swirlProfile (h : ℝ) : SimilarityProfile.PhysicalProfile :=
  pullback h (-A h - 1 / 2) P.f

/-- Axial profile, given by `pullback h (-A h) P.U`. -/
noncomputable def axialProfile (h : ℝ) : SimilarityProfile.PhysicalProfile :=
  pullback h (-A h) P.U

/-- Pressure profile, given by `pullback h (-2 * A h) P.pressure`. -/
noncomputable def pressureProfile (h : ℝ) : SimilarityProfile.PhysicalProfile :=
  pullback h (-2 * A h) P.pressure

/-- Physical stress theta, given by `pullback h (-A h - 1 / 2) (theta P h)`. -/
noncomputable def physicalStressTheta (h : ℝ) : SimilarityProfile.PhysicalProfile :=
  pullback h (-A h - 1 / 2) (theta P h)

/-- Physical stress axial, given by `pullback h (-A h - 1 / 2) (axial P h)`. -/
noncomputable def physicalStressAxial (h : ℝ) : SimilarityProfile.PhysicalProfile :=
  pullback h (-A h - 1 / 2) (axial P h)

/-- Physical velocity, given by `AxisymmetricResidual.velocity (RadialFluxResidual.radialB
(fluxProfile P h)) (swirlProfile P h) (axialProfile P h)`. -/
noncomputable def physicalVelocity (h : ℝ) : ProblemStatement.VelocityField :=
  AxisymmetricResidual.velocity (RadialFluxResidual.radialB (fluxProfile P h))
    (swirlProfile P h) (axialProfile P h)

/-- Physical pressure, given by `AxisymmetricResidual.pressure (pressureProfile P h)`. -/
noncomputable def physicalPressure (h : ℝ) : ProblemStatement.PressureField :=
  AxisymmetricResidual.pressure (pressureProfile P h)

/-- The angular axial-viscosity term omitted from the leading radial balance. -/
noncomputable def thetaAxialViscosity (h : ℝ) (p : SimilarityProfile.PhysicalPoint) : ℝ :=
  Real.sqrt (2 * p.2.1) *
    SimilarityProfile.partialZ (SimilarityProfile.partialZ (swirlProfile P h)) p

/-- The axial axial-viscosity term omitted from the leading radial balance. -/
noncomputable def axialAxialViscosity (h : ℝ) (p : SimilarityProfile.PhysicalPoint) : ℝ :=
  SimilarityProfile.partialZ (SimilarityProfile.partialZ (axialProfile P h)) p

theorem inner_X_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) (hs : 0 < p.2.1) :
    0 < (inner h p).1 := div_pos hs (SimilarityProfile.q_pos hh hh1 hp)

theorem radialDivergence_physicalStressTheta {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) (hs : 0 < p.2.1)
    (hw : inner h p ∈ Ω.carrier) (hf : P.f (inner h p) ≠ 0) :
    radialDivergence 2 (physicalStressTheta P h) p =
      SimilarityProfile.q h p ^ (-A h - 1) * (Real.sqrt (2 * (inner h p).1) *
        (P.f (inner h p) * sourceTheta P h (inner h p) / L h (inner h p).2 +
          2 * ((inner h p).1 * partialX (partialX P.f) (inner h p) +
            2 * partialX P.f (inner h p)))) := by
  have hX := inner_X_pos hh hh1 hp hs
  have hL : L h (inner h p).2 ≠ 0 := (SimilarityProfile.L_pos hh hh1 hp).ne'
  unfold physicalStressTheta
  rw [radialDivergence_pullback hh hh1 2 hp
    ((theta_smoothAt P h hw hX.ne' hf hL).differentiableAt (by simp)),
    sqrt_radial_two hX, theta_divergence P h hw hX hf hL]
  congr 2
  ring

theorem radialDivergence_physicalStressAxial {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) (hs : 0 < p.2.1)
    (hw : inner h p ∈ Ω.carrier) :
    radialDivergence 1 (physicalStressAxial P h) p =
      SimilarityProfile.q h p ^ (-A h - 1) *
        (sourceAxial P h (inner h p) / L h (inner h p).2 +
          2 * ((inner h p).1 * partialX (partialX P.U) (inner h p) +
            partialX P.U (inner h p))) := by
  have hX := inner_X_pos hh hh1 hp hs
  have hL : L h (inner h p).2 ≠ 0 := (SimilarityProfile.L_pos hh hh1 hp).ne'
  unfold physicalStressAxial
  rw [radialDivergence_pullback hh hh1 1 hp
    ((axial_smoothAt P h hw hX.ne' hL).differentiableAt (by simp)), one_mul,
    axial_divergence P h hw hX hL]
  congr 2
  ring

theorem thetaAxialViscosity_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) (hw : inner h p ∈ Ω.carrier) :
    thetaAxialViscosity P h p = SimilarityProfile.q h p ^ (-A h - 1 + 2 * h) *
      (Real.sqrt (2 * (inner h p).1) *
        SlowExpansionResidual.Z2 h (-A h - 1 / 2) P.f (inner h p)) := by
  have hfc : ContDiffAt ℝ 2 P.f (inner h p) :=
    (P.f_smooth.contDiffAt (Ω.isOpen.mem_nhds hw)).of_le (WithTop.coe_le_coe.mpr le_top)
  unfold thetaAxialViscosity swirlProfile
  rw [SimilarityProfile.partialZ_partialZ_pullback hh hh1 hp hfc]
  unfold pullback
  rw [← mul_assoc, radius_mul_rpow hh hh1 _ hp]
  have he : -A h - 1 / 2 - 2 * CoordinateAlgebra.D h + 1 / 2 = -A h - 1 + 2 * h := by
    unfold CoordinateAlgebra.D
    ring
  rw [he, mul_assoc]
  rfl

theorem axialAxialViscosity_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) (hw : inner h p ∈ Ω.carrier) :
    axialAxialViscosity P h p = SimilarityProfile.q h p ^ (-A h - 1 + 2 * h) *
      SlowExpansionResidual.Z2 h (-A h) P.U (inner h p) := by
  have huc : ContDiffAt ℝ 2 P.U (inner h p) :=
    (P.U_smooth.contDiffAt (Ω.isOpen.mem_nhds hw)).of_le (WithTop.coe_le_coe.mpr le_top)
  unfold axialAxialViscosity axialProfile
  rw [SimilarityProfile.partialZ_partialZ_pullback hh hh1 hp huc]
  unfold pullback
  have he : -A h - 2 * CoordinateAlgebra.D h = -A h - 1 + 2 * h := by
    unfold CoordinateAlgebra.D
    ring
  rw [he]
  rfl

theorem theta_transport_stress {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) (hs : 0 < p.2.1)
    (hw : inner h p ∈ Ω.carrier) (hf : P.f (inner h p) ≠ 0) :
    Real.sqrt (2 * p.2.1) * SlowExpansionResidual.transportResidual 1 2
        (fluxProfile P h) (axialProfile P h) (swirlProfile P h) (fun _ => 0) p +
        thetaAxialViscosity P h p = -radialDivergence 2 (physicalStressTheta P h) p := by
  have hfc : ContDiffAt ℝ 2 P.f (inner h p) :=
    (P.f_smooth.contDiffAt (Ω.isOpen.mem_nhds hw)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hX := inner_X_pos hh hh1 hp hs
  have hL : L h (inner h p).2 ≠ 0 := (SimilarityProfile.L_pos hh hh1 hp).ne'
  have he := transport_pullback_add_axialViscosity hh hh1 1 2
    (SlowDivergence.radialFlux h 0 P.U) P.U P.f (fun _ => 0) hp hs hfc
      (e := -A h - 1 / 2)
  have hz : pullback h (-A h - 1 / 2 - 1) (fun _ => 0) = fun _ => 0 := by
    funext y
    simp [pullback]
  rw [hz] at he
  simp only [one_mul, add_zero] at he
  rw [theta_transport_coefficient P h hw hX.ne' hf hL] at he
  change SlowExpansionResidual.transportResidual 1 2 (fluxProfile P h) (axialProfile P h)
      (swirlProfile P h) (fun _ => 0) p +
      SimilarityProfile.partialZ (SimilarityProfile.partialZ (swirlProfile P h)) p = _ at he
  unfold thetaAxialViscosity
  rw [← mul_add, he, ← mul_assoc, radius_mul_rpow hh hh1 _ hp,
    radialDivergence_physicalStressTheta P hh hh1 hp hs hw hf]
  have hexp : -A h - 1 / 2 - 1 + 1 / 2 = -A h - 1 := by ring
  rw [hexp]
  ring

theorem partialZ_pressureProfile {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) (hw : inner h p ∈ Ω.carrier) :
    SimilarityProfile.partialZ (pressureProfile P h) p =
      pullback h (-A h - 1) (SimilarityProfile.Z h (-2 * A h) P.pressure) p := by
  unfold pressureProfile
  rw [SimilarityProfile.partialZ_pullback hh hh1 hp
    ((P.pressure_smooth.contDiffAt (Ω.isOpen.mem_nhds hw)).differentiableAt (by simp))]
  have he : -2 * A h - CoordinateAlgebra.D h = -A h - 1 := by
    unfold CoordinateAlgebra.A CoordinateAlgebra.D
    ring
  rw [he]

theorem axial_transport_stress {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) (hs : 0 < p.2.1)
    (hw : inner h p ∈ Ω.carrier) :
    SlowExpansionResidual.transportResidual 0 1 (fluxProfile P h) (axialProfile P h)
        (axialProfile P h) (SimilarityProfile.partialZ (pressureProfile P h)) p +
        axialAxialViscosity P h p = -radialDivergence 1 (physicalStressAxial P h) p := by
  have huc : ContDiffAt ℝ 2 P.U (inner h p) :=
    (P.U_smooth.contDiffAt (Ω.isOpen.mem_nhds hw)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hL : L h (inner h p).2 ≠ 0 := (SimilarityProfile.L_pos hh hh1 hp).ne'
  have he := transport_pullback_add_axialViscosity hh hh1 0 1
    (SlowDivergence.radialFlux h 0 P.U) P.U P.U
    (SimilarityProfile.Z h (-2 * A h) P.pressure) hp hs huc (e := -A h)
  simp only [zero_mul, zero_div, add_zero, one_mul] at he
  have hsrc : SlowExpansionResidual.transportResidual 0 1 (fluxProfile P h) (axialProfile P h)
      (axialProfile P h) (pullback h (-A h - 1) (SimilarityProfile.Z h (-2 * A h) P.pressure)) p =
      SlowExpansionResidual.transportResidual 0 1 (fluxProfile P h) (axialProfile P h)
        (axialProfile P h) (SimilarityProfile.partialZ (pressureProfile P h)) p := by
    unfold SlowExpansionResidual.transportResidual
    rw [partialZ_pressureProfile P hh hh1 hp hw]
  change SlowExpansionResidual.transportResidual 0 1 (fluxProfile P h) (axialProfile P h)
      (axialProfile P h) (pullback h (-A h - 1) (SimilarityProfile.Z h (-2 * A h) P.pressure)) p +
      axialAxialViscosity P h p = _ at he
  rw [hsrc] at he
  rw [he, radialDivergence_physicalStressAxial P hh hh1 hp hs hw]
  have hc := axial_transport_coefficient P h hw hL
  calc
    _ = SimilarityProfile.q h p ^ (-A h - 1) *
        ((SimilarityProfile.T h (-A h) P.U (inner h p) +
          SlowDivergence.radialFlux h 0 P.U (inner h p) * partialX P.U (inner h p) +
          P.U (inner h p) * SimilarityProfile.Z h (-A h) P.U (inner h p) +
          SimilarityProfile.Z h (-2 * A h) P.pressure (inner h p)) -
          2 * ((inner h p).1 * partialX (partialX P.U) (inner h p) + partialX P.U (inner h p))) :=
              by
              ring
    _ = _ := by rw [hc]; ring

/-- The regular swirl coefficient reconstructs precisely `u_theta=q^(-A) E`. -/
theorem physical_swirl_value {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) :
    Real.sqrt (2 * p.2.1) * swirlProfile P h p = pullback h (-A h) P.E p := by
  unfold swirlProfile pullback Profiles.E
  rw [← mul_assoc, radius_mul_rpow hh hh1 _ hp]
  have he : -A h - 1 / 2 + 1 / 2 = -A h := by ring
  rw [he, mul_assoc]

/-- Cylindrical angular component of a genuine Cartesian vector. -/
noncomputable def angularComponent (x v : ProblemStatement.Space) : ℝ :=
  (x 0 * v 1 - x 1 * v 0) / Real.sqrt (2 * AxisymmetricFields.radialEnergy x)

theorem angularComponent_pack {x : ProblemStatement.Space}
    (hs : 0 < AxisymmetricFields.radialEnergy x) (R T Z : ℝ) :
    angularComponent x (AxisymmetricResidual.pack (x 0 * R + x 1 * T)
      (x 1 * R - x 0 * T) Z) = -Real.sqrt (2 * AxisymmetricFields.radialEnergy x) * T := by
  have hr : Real.sqrt (2 * AxisymmetricFields.radialEnergy x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hr2 : Real.sqrt (2 * AxisymmetricFields.radialEnergy x) ^ 2 =
      2 * AxisymmetricFields.radialEnergy x := Real.sq_sqrt (by positivity)
  simp only [angularComponent, AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_one]
  apply (div_eq_iff hr).2
  calc
    _ = -(2 * AxisymmetricFields.radialEnergy x) * T := by
      unfold AxisymmetricFields.radialEnergy
      ring
    _ = -(Real.sqrt (2 * AxisymmetricFields.radialEnergy x) ^ 2) * T :=
      congrArg (fun y => -y * T) hr2.symm
    _ = _ := by ring

/-- Proposition 3.2 for the actual Cartesian Navier--Stokes residual.

The local hypotheses avoid extending the quotient defining radial velocity
across the axis. The two added terms are the exact axial-viscosity terms;
their explicit similarity formulas are `thetaAxialViscosity_eq` and
`axialAxialViscosity_eq`.
-/
theorem navierStokesResidual_tangential {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {t : ℝ} {x : ProblemStatement.Space} (ht : t < 1)
    (hs : 0 < AxisymmetricFields.radialEnergy x)
    (hw : inner h (AxisymmetricFields.profilePoint t x) ∈ Ω.carrier)
    (hf : P.f (inner h (AxisymmetricFields.profilePoint t x)) ≠ 0) :
    (angularComponent x (ProblemStatement.navierStokesResidual
        (physicalVelocity P h) (physicalPressure P h) t x) +
        thetaAxialViscosity P h (AxisymmetricFields.profilePoint t x) =
      -radialDivergence 2 (physicalStressTheta P h) (AxisymmetricFields.profilePoint t x)) ∧
    ((ProblemStatement.navierStokesResidual (physicalVelocity P h) (physicalPressure P h) t x) 2 +
        axialAxialViscosity P h (AxisymmetricFields.profilePoint t x) =
      -radialDivergence 1 (physicalStressAxial P h) (AxisymmetricFields.profilePoint t x)) := by
  have hL : L h (inner h (AxisymmetricFields.profilePoint t x)).2 ≠ 0 :=
    (SimilarityProfile.L_pos hh hh1 ht).ne'
  have hvi : ContDiffAt ℝ 2 (SlowDivergence.radialFlux h 0 P.U)
      (inner h (AxisymmetricFields.profilePoint t x)) :=
    (SlowDivergence.radialFlux_smoothAt Ω P.U_smooth h 0 hw hL).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hfi : ContDiffAt ℝ 2 P.f (inner h (AxisymmetricFields.profilePoint t x)) :=
    (P.f_smooth.contDiffAt (Ω.isOpen.mem_nhds hw)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hui : ContDiffAt ℝ 2 P.U (inner h (AxisymmetricFields.profilePoint t x)) :=
    (P.U_smooth.contDiffAt (Ω.isOpen.mem_nhds hw)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hpi := (P.pressure_smooth.contDiffAt (Ω.isOpen.mem_nhds hw)).differentiableAt (by simp)
  have hv : ContDiffAt ℝ 2 (fluxProfile P h) (AxisymmetricFields.profilePoint t x) :=
    SimilarityProfile.pullback_smoothAt hh hh1 ht hvi
  have hff : ContDiffAt ℝ 2 (swirlProfile P h) (AxisymmetricFields.profilePoint t x) :=
    SimilarityProfile.pullback_smoothAt hh hh1 ht hfi
  have hu : ContDiffAt ℝ 2 (axialProfile P h) (AxisymmetricFields.profilePoint t x) :=
    SimilarityProfile.pullback_smoothAt hh hh1 ht hui
  have hp : DifferentiableAt ℝ (pressureProfile P h) (AxisymmetricFields.profilePoint t x) :=
    SimilarityProfile.pullback_differentiableAt hh hh1 ht hpi
  have hb := RadialFluxResidual.contDiffAt_radialB hv hs.ne'
  have he := LocalAxisymmetricResidual.navierStokesResidual_velocity hb hff hu hp
  change ProblemStatement.navierStokesResidual (physicalVelocity P h) (physicalPressure P h) t x =
      _ at he
  rw [he]
  constructor
  · rw [angularComponent_pack hs, SlowExpansionResidual.residualAngular_radialB _ _ _ hs.ne']
    have hhθ := theta_transport_stress P hh hh1 ht hs hw hf
    change Real.sqrt (2 * AxisymmetricFields.radialEnergy x) *
        SlowExpansionResidual.transportResidual 1 2 (fluxProfile P h) (axialProfile P h)
          (swirlProfile P h) (fun _ => 0) (AxisymmetricFields.profilePoint t x) + _ = _ at hhθ
    simpa only [neg_mul_neg] using hhθ
  · rw [AxisymmetricResidual.pack_two, SlowExpansionResidual.residualAxial_radialB _ _ _ hs.ne']
    exact axial_transport_stress P hh hh1 ht hs hw

end NavierStokes.LeadingStress
