/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ProfileHistories
public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityProfile

@[expose] public section

/-!
# The actual positive-order divergence primitive

Equation (21) is derived from genuine radial averages of a jointly smooth
axial profile. Its radial derivative is the actual similarity axial operator,
and its physical reconstruction satisfies the flux form of incompressibility.
-/

noncomputable section

namespace NavierStokes.SlowDivergence

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ProfileHistories

/-- The positive-order radial flux, with an arbitrary exponent increment lam. -/
def radialFlux (h lam : ℝ) (U : Field) (p : Point) : ℝ :=
  p.1 / CoordinateAlgebra.L h p.2 *
    (2 * p.2 * U p - 2 * p.2 * (CoordinateAlgebra.D h + lam) * average U p -
      CoordinateAlgebra.d p.2 * SimilarityProfile.partialEta (average U) p)

theorem radialFlux_at_axis (h lam η : ℝ) (U : Field) : radialFlux h lam U (0, η) = 0 := by
  simp [radialFlux]

theorem radialFlux_div_radial (h lam : ℝ) (U : Field) {p : Point} (hX : p.1 ≠ 0) :
    radialFlux h lam U p / p.1 = (CoordinateAlgebra.L h p.2)⁻¹ *
      (2 * p.2 * U p - 2 * p.2 * (CoordinateAlgebra.D h + lam) * average U p -
        CoordinateAlgebra.d p.2 * SimilarityProfile.partialEta (average U) p) := by
  dsimp [radialFlux]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    _ = (p.1 * p.1⁻¹) * ((CoordinateAlgebra.L h p.2)⁻¹ *
      (2 * p.2 * U p - 2 * p.2 * (CoordinateAlgebra.D h + lam) * average U p -
        CoordinateAlgebra.d p.2 * SimilarityProfile.partialEta (average U) p)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hX, one_mul]

/-- Rewriting the formula through actual radial histories removes every
division by X and permits differentiation at the axis. -/
theorem radialFlux_eq_histories (Ω : RadialDomain) {U : Field}
    (hU : ContDiffOn ℝ ∞ U Ω.carrier) (h lam : ℝ) {p : Point} (hp : p ∈ Ω.carrier) :
    radialFlux h lam U p =
      (2 * p.2 * (p.1 * U p) -
        2 * p.2 * (CoordinateAlgebra.D h + lam) * primitive U p -
          CoordinateAlgebra.d p.2 * primitive (parameterPartial U) p) /
            CoordinateAlgebra.L h p.2 := by
  have hη : SimilarityProfile.partialEta (average U) p = average (parameterPartial U) p :=
    parameterPartial_average Ω hU hp
  simp only [radialFlux, hη, primitive_eq_mul_average, div_eq_mul_inv]
  ring

theorem radialFlux_smoothAt (Ω : RadialDomain) {U : Field}
    (hU : ContDiffOn ℝ ∞ U Ω.carrier) (h lam : ℝ) {p : Point} (hp : p ∈ Ω.carrier)
    (hL : CoordinateAlgebra.L h p.2 ≠ 0) : ContDiffAt ℝ ∞ (radialFlux h lam U) p := by
  have hu := hU.contDiffAt (Ω.isOpen.mem_nhds hp)
  have ha := (average_smooth Ω hU).contDiffAt (Ω.isOpen.mem_nhds hp)
  have hη := (parameterPartial_smooth Ω (average_smooth Ω hU)).contDiffAt (Ω.isOpen.mem_nhds hp)
  exact (contDiffAt_fst.div
    (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))) hL).mul
      ((((contDiffAt_const.mul contDiffAt_snd).mul hu).sub
        (((contDiffAt_const.mul contDiffAt_snd).mul contDiffAt_const).mul ha)).sub
          ((contDiffAt_const.sub (contDiffAt_snd.pow 2)).mul hη))

/-- Joint C∞ regularity on every open profile domain avoiding L=0. -/
theorem radialFlux_smooth (Ω : RadialDomain) {U : Field}
    (hU : ContDiffOn ℝ ∞ U Ω.carrier) (h lam : ℝ)
    (hL : ∀ p ∈ Ω.carrier, CoordinateAlgebra.L h p.2 ≠ 0) :
    ContDiffOn ℝ ∞ (radialFlux h lam U) Ω.carrier := by
  intro p hp
  exact (radialFlux_smoothAt Ω hU h lam hp (hL p hp)).contDiffWithinAt

/-- The first identity in (21), derived by FTC from the actual histories.
The scalar radial statement also holds under total division when L=0. -/
theorem radialFlux_hasDerivAt (Ω : RadialDomain) {U : Field}
    (hU : ContDiffOn ℝ ∞ U Ω.carrier) (h lam : ℝ) {p : Point} (hp : p ∈ Ω.carrier) :
    HasDerivAt (fun x => radialFlux h lam U (x, p.2))
      (-SimilarityProfile.Z h (-CoordinateAlgebra.A h + lam) U p) p.1 := by
  have hd := (((((hasDerivAt_id p.1).mul (radialPartial_hasDerivAt Ω hU hp)).const_mul
    (2 * p.2)).sub ((primitive_hasDerivAt Ω hU hp).const_mul
      (2 * p.2 * (CoordinateAlgebra.D h + lam)))).sub
        ((primitive_hasDerivAt Ω (parameterPartial_smooth Ω hU) hp).const_mul
          (CoordinateAlgebra.d p.2))).div_const (CoordinateAlgebra.L h p.2)
  have hd' : HasDerivAt (fun x =>
      (2 * p.2 * (x * U (x, p.2)) -
        2 * p.2 * (CoordinateAlgebra.D h + lam) * primitive U (x, p.2) -
          CoordinateAlgebra.d p.2 * primitive (parameterPartial U) (x, p.2)) /
            CoordinateAlgebra.L h p.2)
      (-SimilarityProfile.Z h (-CoordinateAlgebra.A h + lam) U p) p.1 := by
    apply hd.congr_deriv
    dsimp [SimilarityProfile.Z, CoordinateAlgebra.axialCoeff, CoordinateAlgebra.A,
      CoordinateAlgebra.D, SimilarityProfile.partialX, SimilarityProfile.partialEta,
        radialPartial, parameterPartial]
    ring
  apply hd'.congr_of_eventuallyEq
  have hn : ∀ᶠ x in 𝓝 p.1, (x, p.2) ∈ Ω.carrier :=
    (continuous_id.prodMk continuous_const).continuousAt (Ω.isOpen.mem_nhds hp)
  filter_upwards [hn] with x hx
  exact radialFlux_eq_histories Ω hU h lam hx

/-- Equality with the partial derivative used by the similarity calculus. -/
theorem partialX_radialFlux (Ω : RadialDomain) {U : Field}
    (hU : ContDiffOn ℝ ∞ U Ω.carrier) (h lam : ℝ) {p : Point} (hp : p ∈ Ω.carrier)
    (hL : CoordinateAlgebra.L h p.2 ≠ 0) :
    SimilarityProfile.partialX (radialFlux h lam U) p =
      -SimilarityProfile.Z h (-CoordinateAlgebra.A h + lam) U p := by
  have hv := ((radialFlux_smoothAt Ω hU h lam hp hL).differentiableAt (by simp)).hasFDerivAt
  have hd := hv.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hd.unique (radialFlux_hasDerivAt Ω hU h lam hp)

theorem axial_source_intervalIntegrable (Ω : RadialDomain) {U : Field}
    (hU : ContDiffOn ℝ ∞ U Ω.carrier) (h b : ℝ) {p : Point} (hp : p ∈ Ω.carrier) :
    IntervalIntegrable (fun x => -SimilarityProfile.Z h b U (x, p.2)) volume 0 p.1 := by
  have hu : ContinuousOn (fun x => U (x, p.2)) (uIcc 0 p.1) :=
    (radial_slice_continuous Ω hU p.2).mono (fun _ hx => Ω.segment_mem hp hx)
  have hx : ContinuousOn (fun x => radialPartial U (x, p.2)) (uIcc 0 p.1) :=
    (radial_slice_continuous Ω (radialPartial_smooth Ω hU) p.2).mono
      (fun _ hx => Ω.segment_mem hp hx)
  have hη : ContinuousOn (fun x => parameterPartial U (x, p.2)) (uIcc 0 p.1) :=
    (radial_slice_continuous Ω (parameterPartial_smooth Ω hU) p.2).mono
      (fun _ hx => Ω.segment_mem hp hx)
  have hc : ContinuousOn (fun x =>
      -((2 * p.2 * b * U (x, p.2) + CoordinateAlgebra.d p.2 * parameterPartial U (x, p.2) -
        2 * p.2 * (x * radialPartial U (x, p.2))) / CoordinateAlgebra.L h p.2))
          (uIcc 0 p.1) :=
    ((((continuousOn_const.mul hu).add
      (continuousOn_const.mul hη)).sub
        (continuousOn_const.mul (continuousOn_id.mul hx))).div_const (CoordinateAlgebra.L h
          p.2)).neg
  simpa only [SimilarityProfile.Z, CoordinateAlgebra.axialCoeff, SimilarityProfile.partialX,
    SimilarityProfile.partialEta, radialPartial, parameterPartial, mul_assoc] using
      hc.intervalIntegrable

/-- The printed expression is precisely the zero-axis integral of -Z U. -/
theorem radialFlux_eq_integral (Ω : RadialDomain) {U : Field}
    (hU : ContDiffOn ℝ ∞ U Ω.carrier) (h lam : ℝ) {p : Point} (hp : p ∈ Ω.carrier) :
    radialFlux h lam U p =
      ∫ x in (0 : ℝ)..p.1, -SimilarityProfile.Z h (-CoordinateAlgebra.A h + lam) U (x, p.2) := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => radialFlux h lam U (x, p.2))
    (fun x hx => radialFlux_hasDerivAt Ω hU h lam (Ω.segment_mem hp hx))
    (axial_source_intervalIntegrable Ω hU h (-CoordinateAlgebra.A h + lam) hp)
  simpa only [radialFlux_at_axis, sub_zero, Prod.eta] using hi.symm

/-- Physical incompressibility in flux coordinates `(t,s,z)`, `s=r²/2`.
The radial flux has power q^lam and the axial velocity has power q^(-A+lam). -/
theorem physical_flux_axial_balance (Ω : RadialDomain) {U : Field}
    (hU : ContDiffOn ℝ ∞ U Ω.carrier) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (lam : ℝ) {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1)
    (hi : SimilarityProfile.inner h p ∈ Ω.carrier) :
    SimilarityProfile.partialS (SimilarityProfile.pullback h lam (radialFlux h lam U)) p +
      SimilarityProfile.partialZ (SimilarityProfile.pullback h (-CoordinateAlgebra.A h + lam) U) p
        = 0 := by
  have hL : CoordinateAlgebra.L h (SimilarityProfile.inner h p).2 ≠ 0 :=
    (SimilarityProfile.L_pos hh hh1 hp).ne'
  rw [SimilarityProfile.partialS_pullback hh hh1 hp
    ((radialFlux_smoothAt Ω hU h lam hi hL).differentiableAt (by simp))]
  rw [SimilarityProfile.partialZ_pullback hh hh1 hp
    ((hU.contDiffAt (Ω.isOpen.mem_nhds hi)).differentiableAt (by simp))]
  have he : -CoordinateAlgebra.A h + lam - SimilarityProfile.D h = lam - 1 := by
    dsimp [CoordinateAlgebra.A, SimilarityProfile.D, CoordinateAlgebra.D]
    ring
  rw [he]
  simp only [SimilarityProfile.pullback]
  rw [partialX_radialFlux Ω hU h lam hi hL]
  ring

/-- Specialization to the manuscript's lam_n = 2nh, with n represented honestly
as a natural-number order. -/
theorem slow_order_divergence (Ω : RadialDomain) {U : Field}
    (hU : ContDiffOn ℝ ∞ U Ω.carrier) (h : ℝ) (n : ℕ)
    {p : Point} (hp : p ∈ Ω.carrier) (hL : CoordinateAlgebra.L h p.2 ≠ 0) :
    SimilarityProfile.partialX (radialFlux h (2 * (n : ℝ) * h) U) p +
      SimilarityProfile.Z h (-CoordinateAlgebra.A h + 2 * (n : ℝ) * h) U p = 0 := by
  rw [partialX_radialFlux Ω hU h (2 * (n : ℝ) * h) hp hL]
  exact neg_add_cancel _

end NavierStokes.SlowDivergence

end
