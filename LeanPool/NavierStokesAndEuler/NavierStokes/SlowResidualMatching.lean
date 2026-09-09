/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowRecursion
public import LeanPool.NavierStokesAndEuler.NavierStokes.LeadingStress
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowStressSupport
public import LeanPool.NavierStokesAndEuler.NavierStokes.RenormalizedHeatMoment
import LeanPool.NavierStokesAndEuler.NavierStokes.SlowBorelBase

/-!
# Finite slow residuals and their radial stress primitives

The finite profiles and all derivatives below are the actual functions from
`SlowExpansionResidual`. The stored radial variable in `SlowRecursion` is
`beta = V / X`; its conversion to a flux includes the factor `X`.

The stress operator is the two tangential radial operators in (24). It is
not identified with the divergence of an unspecified symmetric tensor.
-/

@[expose] public section


noncomputable section

open Set Filter
open scoped BigOperators Topology ContDiff

namespace NavierStokes.SlowResidualMatching

open SimilarityProfile (InnerPoint InnerProfile PhysicalPoint PhysicalProfile
  partialX partialEta T Z pullback)
open SlowExpansionResidual
open AxisymmetricFields (radialEnergy profilePoint)

/-- Convert a regular radial quotient to the actual radial flux. -/
noncomputable def ofBeta (phi axial beta pressure : ℕ → InnerProfile) : SlowProfiles where
  phi := phi
  axial := axial
  flux := fun n => AxisSourceRegularity.axisFactor (beta n)
  pressure := pressure

/-- The actual functions constructed by the regular-axis recursion. -/
noncomputable def hierarchyProfiles {R : ℝ} {U : Set ℂ} {h C : ℝ}
    {base : Fin 5 → InnerProfile} (A : SlowRecursion.LocalHierarchy R U h C base) :
    SlowProfiles :=
  ofBeta (fun n => SlowRecursion.profile (A.coefficients n 0))
    (fun n => SlowRecursion.profile (A.coefficients n 1))
    (fun n => SlowRecursion.profile (A.coefficients n 4))
    (fun n => SlowRecursion.profile (A.coefficients n 3))

theorem convolution_eq_positiveAxis (F : ℕ → ℕ → ℝ) (n : ℕ) :
    convolution F n = PositiveAxisSystem.convolution n F := by
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ F n

theorem precedingDiffusion_eq_previous (h b : ℝ) (f : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint) :
    PositiveAxisSystem.precedingDiffusion h b f n w =
      previous (fun j => Z2 h (b + slowOrder h j) (f j) w) n := by
  cases n with
  | zero => simp [PositiveAxisSystem.precedingDiffusion, previous]
  | succ n => simp [PositiveAxisSystem.precedingDiffusion, previous, Z2,
      PositiveAxisSystem.slowPower, slowOrder, PositiveAxisSystem.dScale, CoordinateAlgebra.D]

theorem angular_convection_ofBeta (h : ℝ) (phi axial beta pressure : ℕ → InnerProfile)
    (n : ℕ) {w : InnerPoint} (hX : w.1 ≠ 0) :
    convolution (fun i j => (ofBeta phi axial beta pressure).flux i w *
        (partialX (phi j) w + phi j w / w.1) +
      axial i w * Z h (angularExponent h + slowOrder h j) (phi j) w) n =
    PositiveAxisSystem.convolution n
      (PositiveAxisSystem.angularConvection h w.2 w.1
        (fun j => PositiveAxisSystem.actualJet (phi j) w)
        (fun j => PositiveAxisSystem.actualJet (axial j) w) (fun j => beta j w)) := by
  rw [convolution_eq_positiveAxis]
  apply Finset.sum_congr rfl
  intro i hi
  change (w.1 * beta i w) * (partialX (phi (n - i)) w + phi (n - i) w / w.1) + _ = _
  rw [← PositiveAxisSystem.angularConvection_radial_term hX]
  rfl

theorem axial_convection_ofBeta (h : ℝ) (phi axial beta pressure : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint) :
    convolution (fun i j => (ofBeta phi axial beta pressure).flux i w *
        partialX (axial j) w +
      axial i w * Z h (axialExponent h + slowOrder h j) (axial j) w) n =
    PositiveAxisSystem.convolution n
      (PositiveAxisSystem.axialConvection h w.2 w.1
        (fun j => PositiveAxisSystem.actualJet (axial j) w) (fun j => beta j w)) := by
  rw [convolution_eq_positiveAxis]
  apply Finset.sum_congr rfl
  intro i hi
  change (w.1 * beta i w) * partialX (axial (n - i)) w + _ =
    beta i w * w.1 * partialX (axial (n - i)) w +
      axial i w * Z h (axialExponent h + slowOrder h (n-i)) (axial (n-i)) w
  ring

/-- The solved angular and axial rows are the literal residual coefficients. -/
theorem positiveOrder_tangential_coefficients (h C : ℝ)
    (phi axial beta pressure : ℕ → InnerProfile) (k : InnerProfile) (n : ℕ)
    {w : InnerPoint} (hX : w.1 ≠ 0)
    (he : PositiveAxisSystem.PositiveOrderEquations h C w.2 w.1 n
      (fun j => PositiveAxisSystem.actualJet (phi j) w)
      (fun j => PositiveAxisSystem.actualJet (axial j) w) (fun j => beta j w)
      (PositiveAxisSystem.actualJet k w) (PositiveAxisSystem.actualJet (pressure n) w)
      (PositiveAxisSystem.precedingDiffusion h (PositiveAxisSystem.angularPower h) phi n w)
      (PositiveAxisSystem.precedingDiffusion h (PositiveAxisSystem.axialPower h) axial n w)
      (AxisSourceRegularity.previousOmegaDivX h axial beta n w)) :
    angularCoefficient h (ofBeta phi axial beta pressure) n w = 0 ∧
      axialCoefficient h (ofBeta phi axial beta pressure) n w = 0 := by
  constructor
  · apply (angularCoefficient_eq_zero_iff h _ n w).2
    have hc := angular_convection_ofBeta h phi axial beta pressure n hX
    dsimp only [ofBeta] at hc ⊢
    rw [hc]
    have h := he.2.2.1
    simp only [precedingDiffusion_eq_previous] at h
    exact h
  · apply (axialCoefficient_eq_zero_iff h _ n w).2
    have hc := axial_convection_ofBeta h phi axial beta pressure n w
    dsimp only [ofBeta] at hc ⊢
    rw [hc]
    have h := he.2.2.2
    simp only [precedingDiffusion_eq_previous] at h
    exact h

theorem hierarchy_tangential_coefficients {R : ℝ} {U : Set ℂ} {h C : ℝ}
    {base : Fin 5 → InnerProfile} (A : SlowRecursion.LocalHierarchy R U h C base)
    {n : ℕ} (hn : 0 < n) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    angularCoefficient h (hierarchyProfiles A) n (X, eta) = 0 ∧
      axialCoefficient h (hierarchyProfiles A) n (X, eta) = 0 := by
  exact positiveOrder_tangential_coefficients h C _ _ _ _ _ n hX.1.ne'
    (A.equations n hn X hX eta heta)

theorem omegaCoefficient_eq_omega (h : ℝ) (f : SlowProfiles) (n : ℕ) (w : InnerPoint) :
    omegaCoefficient h f n w = AxisSourceRegularity.omega h f.axial f.flux n w := by
  rw [omegaCoefficient_eq]
  have hp : previous (fun j => Z2 h (slowOrder h j) (f.flux j) w) n =
      AxisSourceRegularity.shiftedAxial h f.flux n w := by
    cases n <;> rfl
  rw [hp]
  rfl

theorem previousOmega_ofBeta (h : ℝ) (phi axial beta pressure : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint) (hX : w.1 ≠ 0) (hL : CoordinateAlgebra.L h w.2 ≠ 0)
    (hb : ∀ j < n, ContDiffAt ℝ 2 (beta j) w) :
    previous (fun j => omegaCoefficient h (ofBeta phi axial beta pressure) j w) n /
        w.1 = AxisSourceRegularity.previousOmegaDivX h axial beta n w := by
  cases n with
  | zero => simp [previous, AxisSourceRegularity.previousOmegaDivX]
  | succ n =>
    simp only [previous_succ, AxisSourceRegularity.previousOmegaDivX]
    rw [omegaCoefficient_eq_omega]
    exact AxisSourceRegularity.omega_quotient_eq h axial beta n w
      (fun j hj => hb j (Nat.lt_succ_of_le hj)) hL hX

theorem positiveOrder_pressure_coefficient (h C : ℝ)
    (phi axial beta pressure : ℕ → InnerProfile) (k : InnerProfile) (n : ℕ)
    {w : InnerPoint} (hX : w.1 ≠ 0) (hL : CoordinateAlgebra.L h w.2 ≠ 0)
    (hb : ∀ j < n, ContDiffAt ℝ 2 (beta j) w)
    (he : PositiveAxisSystem.PositiveOrderEquations h C w.2 w.1 n
      (fun j => PositiveAxisSystem.actualJet (phi j) w)
      (fun j => PositiveAxisSystem.actualJet (axial j) w) (fun j => beta j w)
      (PositiveAxisSystem.actualJet k w) (PositiveAxisSystem.actualJet (pressure n) w)
      (PositiveAxisSystem.precedingDiffusion h (PositiveAxisSystem.angularPower h) phi n w)
      (PositiveAxisSystem.precedingDiffusion h (PositiveAxisSystem.axialPower h) axial n w)
      (AxisSourceRegularity.previousOmegaDivX h axial beta n w)) :
    pressureCoefficient h C (ofBeta phi axial beta pressure) n w = 0 := by
  apply (pressureCoefficient_eq_zero_iff h C _ n w).2
  have hp := previousOmega_ofBeta h phi axial beta pressure n w hX hL hb
  have hd : previous (fun j => omegaCoefficient h (ofBeta phi axial beta pressure) j w) n /
      (2 * w.1) = AxisSourceRegularity.previousOmegaDivX h axial beta n w / 2 := by
    rw [← hp]
    ring
  rw [hd]
  dsimp only [ofBeta]
  rw [convolution_eq_positiveAxis]
  simpa only [PositiveAxisSystem.actualJet, PositiveAxisSystem.inverseSquare, inv_pow] using he.2.1

theorem partialX_congr_germ {f g : InnerProfile} {w : InnerPoint}
    (hfg : f =ᶠ[𝓝 w] g) : partialX f =ᶠ[𝓝 w] partialX g := by
  filter_upwards [hfg.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L => L (1, 0)) hy

theorem Z_congr_germ (h b : ℝ) {f g : InnerProfile} {w : InnerPoint}
    (hfg : f =ᶠ[𝓝 w] g) : Z h b f =ᶠ[𝓝 w] Z h b g := by
  filter_upwards [hfg.eventuallyEq_nhds] with y hy
  exact AxisSourceRegularity.Z_congr_germ h b hy

theorem Z2_congr_germ (h b : ℝ) {f g : InnerProfile} {w : InnerPoint}
    (hfg : f =ᶠ[𝓝 w] g) : Z2 h b f w = Z2 h b g w :=
  AxisSourceRegularity.Z_congr_germ h (b - CoordinateAlgebra.D h) (Z_congr_germ h b hfg)

theorem T_congr_germ (h b : ℝ) {f g : InnerProfile} {w : InnerPoint}
    (hfg : f =ᶠ[𝓝 w] g) : T h b f w = T h b g w := by
  simp only [T, CoordinateAlgebra.timeCoeff, partialX, partialEta,
    hfg.eq_of_nhds, hfg.fderiv_eq]

/-- A finite residual coefficient depends only on the germs of the
coefficients through its own order. No global equality is required. -/
theorem transportCoefficient_congr_germ (h e α m : ℝ)
    {v u f s v' u' f' s' : ℕ → InnerProfile} (n : ℕ) {w : InnerPoint}
    (hv : ∀ j ≤ n, v j =ᶠ[𝓝 w] v' j) (hu : ∀ j ≤ n, u j =ᶠ[𝓝 w] u' j)
    (hf : ∀ j ≤ n, f j =ᶠ[𝓝 w] f' j) (hs : s n w = s' n w) :
    transportCoefficient h e α m v u f s n w =
      transportCoefficient h e α m v' u' f' s' n w := by
  have hlin :
      transportLinear w.1 m (fun j => T h (e + slowOrder h j) (f j) w)
          (fun j => partialX (f j) w) (fun j => partialX (partialX (f j)) w)
          (fun j => s j w) n =
      transportLinear w.1 m (fun j => T h (e + slowOrder h j) (f' j) w)
          (fun j => partialX (f' j) w) (fun j => partialX (partialX (f' j)) w)
          (fun j => s' j w) n := by
    simp only [transportLinear, T_congr_germ h (e + slowOrder h n) (hf n le_rfl),
      (partialX_congr_germ (hf n le_rfl)).eq_of_nhds,
      (partialX_congr_germ (partialX_congr_germ (hf n le_rfl))).eq_of_nhds, hs]
  have hconv :
      convolution (transportPair w.1 α (fun j => v j w) (fun j => u j w)
        (fun j => f j w) (fun j => partialX (f j) w)
        (fun j => Z h (e + slowOrder h j) (f j) w)) n =
      convolution (transportPair w.1 α (fun j => v' j w) (fun j => u' j w)
        (fun j => f' j w) (fun j => partialX (f' j) w)
        (fun j => Z h (e + slowOrder h j) (f' j) w)) n := by
    apply Finset.sum_congr rfl
    intro ij hij
    have hi : ij.1 ≤ n := Nat.le.intro (Finset.mem_antidiagonal.mp hij)
    have hj : ij.2 ≤ n := by have := Finset.mem_antidiagonal.mp hij; omega
    simp only [transportPair, (hv ij.1 hi).eq_of_nhds, (hu ij.1 hi).eq_of_nhds,
      (hf ij.2 hj).eq_of_nhds, (partialX_congr_germ (hf ij.2 hj)).eq_of_nhds,
      (Z_congr_germ h (e + slowOrder h ij.2) (hf ij.2 hj)).eq_of_nhds]
  have hprev : previous (fun j => Z2 h (e + slowOrder h j) (f j) w) n =
      previous (fun j => Z2 h (e + slowOrder h j) (f' j) w) n := by
    cases n with
    | zero => rfl
    | succ n => exact Z2_congr_germ h (e + slowOrder h n) (hf n (Nat.le_succ n))
  exact congrArg₂ Sub.sub (congrArg₂ Add.add hlin hconv) hprev

theorem angularCoefficient_congr_germ (h : ℝ) {f g : SlowProfiles}
    (n : ℕ) {w : InnerPoint}
    (hv : ∀ j ≤ n, f.flux j =ᶠ[𝓝 w] g.flux j)
    (hu : ∀ j ≤ n, f.axial j =ᶠ[𝓝 w] g.axial j)
    (hf : ∀ j ≤ n, f.phi j =ᶠ[𝓝 w] g.phi j) :
    angularCoefficient h f n w = angularCoefficient h g n w :=
  transportCoefficient_congr_germ h (angularExponent h) 1 2 n hv hu hf rfl

theorem axialCoefficient_congr_germ (h : ℝ) {f g : SlowProfiles}
    (n : ℕ) {w : InnerPoint}
    (hv : ∀ j ≤ n, f.flux j =ᶠ[𝓝 w] g.flux j)
    (hu : ∀ j ≤ n, f.axial j =ᶠ[𝓝 w] g.axial j)
    (hp : f.pressure n =ᶠ[𝓝 w] g.pressure n) :
    axialCoefficient h f n w = axialCoefficient h g n w :=
  transportCoefficient_congr_germ h (axialExponent h) 0 1 n hv hu hu
    ((Z_congr_germ h (pressureExponent h + slowOrder h n) hp).eq_of_nhds)

theorem omegaCoefficient_congr_germ (h : ℝ) {f g : SlowProfiles}
    (n : ℕ) {w : InnerPoint}
    (hv : ∀ j ≤ n, f.flux j =ᶠ[𝓝 w] g.flux j)
    (hu : ∀ j ≤ n, f.axial j =ᶠ[𝓝 w] g.axial j) :
    omegaCoefficient h f n w = omegaCoefficient h g n w :=
  transportCoefficient_congr_germ h 0 (-(1 / 2)) 0 n hv hu hv rfl

/-- Monotonicity of slow orders is the precise reason every omitted pair
has at least the next power of q. -/
theorem slowOrder_mono {h : ℝ} (hh : 0 ≤ h) : Monotone (slowOrder h) := by
  intro i j hij
  unfold slowOrder
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.mul_le_mul_left 2 hij)) hh

/-- Pair tail size, given by `∑ ij ∈ (pairs N).filter (fun ij => N < ij.1 + ij.2), |K ij.1
ij.2|`. -/
noncomputable def pairTailSize (N : ℕ) (K : ℕ → ℕ → ℝ) : ℝ :=
  ∑ ij ∈ (pairs N).filter (fun ij => N < ij.1 + ij.2), |K ij.1 ij.2|

theorem pairTailSize_nonneg (N : ℕ) (K : ℕ → ℕ → ℝ) : 0 ≤ pairTailSize N K :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem pairTail_bound {q h : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hh : 0 ≤ h)
    (N : ℕ) (b : ℝ) (K : ℕ → ℕ → ℝ) :
    |pairTail N (fun n => q ^ (b + slowOrder h n)) K| ≤
      pairTailSize N K * q ^ (b + slowOrder h (N + 1)) := by
  unfold pairTail pairTailSize
  calc
    _ ≤ ∑ ij ∈ (pairs N).filter (fun ij => N < ij.1 + ij.2),
        |q ^ (b + slowOrder h (ij.1 + ij.2)) * K ij.1 ij.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ij ∈ (pairs N).filter (fun ij => N < ij.1 + ij.2),
        |K ij.1 ij.2| * q ^ (b + slowOrder h (N + 1)) := by
      apply Finset.sum_le_sum
      intro ij hij
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hq _), mul_comm]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_ge hq hq1
      exact add_le_add_right (slowOrder_mono hh (Finset.mem_filter.mp hij).2) b
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Transport kernel, constructed using `transportPair`. -/
noncomputable def transportKernel (h e α : ℝ) (v u f : ℕ → InnerProfile)
    (w : InnerPoint) : ℕ → ℕ → ℝ :=
  transportPair w.1 α (fun j => v j w) (fun j => u j w) (fun j => f j w)
    (fun j => partialX (f j) w) (fun j => Z h (e + slowOrder h j) (f j) w)

/-- Transport tail size, given by `pairTailSize N (transportKernel h e α v u f w) + |Z2 h (e +
slowOrder h N) (f N) w|`. -/
noncomputable def transportTailSize (N : ℕ) (h e α : ℝ)
    (v u f : ℕ → InnerProfile) (w : InnerPoint) : ℝ :=
  pairTailSize N (transportKernel h e α v u f w) +
    |Z2 h (e + slowOrder h N) (f N) w|

theorem transportTailSize_nonneg (N : ℕ) (h e α : ℝ)
    (v u f : ℕ → InnerProfile) (w : InnerPoint) :
    0 ≤ transportTailSize N h e α v u f w :=
  add_nonneg (pairTailSize_nonneg _ _) (abs_nonneg _)

/-- Both the omitted quadratic interactions and the last axial viscosity
are bounded, with their true next-order power. -/
theorem transportTail_bound {q h : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hh : 0 ≤ h)
    (N : ℕ) (e α : ℝ) (v u f : ℕ → InnerProfile) (w : InnerPoint) :
    |transportTail N q h e α v u f w| ≤
      transportTailSize N h e α v u f w * q ^ (e - 1 + slowOrder h (N + 1)) := by
  change |pairTail N (fun n => q ^ (e - 1 + slowOrder h n))
      (transportKernel h e α v u f w) -
      q ^ (e - 1 + slowOrder h (N + 1)) * Z2 h (e + slowOrder h N) (f N) w| ≤ _
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hq _)]
  have hb := pairTail_bound hq hq1 hh N (e - 1) (transportKernel h e α v u f w)
  dsimp only [transportTailSize]
  nlinarith

/-- Pressure tail size, constructed using `transportTailSize`. -/
noncomputable def pressureTailSize (N : ℕ) (h C : ℝ) (f : SlowProfiles)
    (w : InnerPoint) : ℝ :=
  transportTailSize N h 0 (-1 / 2) f.flux f.axial f.flux w +
    |omegaCoefficient h f N w| +
    |2 * w.1 * C⁻¹ ^ 2| * pairTailSize N (fun i j => f.phi i w * f.phi j w)

theorem pressureTailSize_nonneg (N : ℕ) (h C : ℝ) (f : SlowProfiles)
    (w : InnerPoint) : 0 ≤ pressureTailSize N h C f w :=
  add_nonneg (add_nonneg (transportTailSize_nonneg _ _ _ _ _ _ _ _) (abs_nonneg _))
    (mul_nonneg (abs_nonneg _) (pairTailSize_nonneg _ _))

/-- The radial remainder retains the last radial acceleration as well as
the omitted swirl products. Its exponent is not silently equated with the
stronger tangential exponent. -/
theorem pressureTail_bound {q h : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hh : 0 ≤ h)
    (N : ℕ) (C : ℝ) (f : SlowProfiles) (w : InnerPoint) :
    |pressureTail N q h C f w| ≤
      pressureTailSize N h C f w * q ^ (pressureExponent h + slowOrder h (N + 1)) := by
  have ht := transportTail_bound hq hq1 hh N 0 (-1 / 2) f.flux f.axial f.flux w
  have he : pressureExponent h + slowOrder h (N + 1) ≤
      0 - 1 + slowOrder h (N + 1) := by
    unfold pressureExponent CoordinateAlgebra.A
    linarith
  have ht' := ht.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hq hq1 he)
    (transportTailSize_nonneg N h 0 (-1/2) f.flux f.axial f.flux w))
  have hp := pairTail_bound hq hq1 hh N (pressureExponent h)
    (fun i j => f.phi i w * f.phi j w)
  unfold pressureTail
  refine (abs_sub _ _).trans ((add_le_add_left (abs_add_le _ _) _).trans ?_)
  rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hq _)]
  have hh' := mul_le_mul_of_nonneg_left hp (abs_nonneg (2 * w.1 * C⁻¹ ^ 2))
  dsimp only [pressureTailSize]
  nlinarith

/-- The change from cylindrical radius R to the regular variable X. -/
noncomputable def radiusPoint (w : InnerPoint) : InnerPoint := (w.1 ^ 2 / 2, w.2)

/-- From radius, given by `F (Real.sqrt (2 * w.1), w.2)`. -/
noncomputable def fromRadius (F : InnerProfile) (w : InnerPoint) : ℝ :=
  F (Real.sqrt (2 * w.1), w.2)

/-- To radius, given by `f (radiusPoint w)`. -/
noncomputable def toRadius (f : InnerProfile) (w : InnerPoint) : ℝ := f (radiusPoint w)

/-- Swirl radius, given by `w.1 / C * toRadius f w`. -/
noncomputable def swirlRadius (C : ℝ) (f : InnerProfile) (w : InnerPoint) : ℝ :=
  w.1 / C * toRadius f w

theorem radiusPoint_smooth : ContDiff ℝ ∞ radiusPoint :=
  ((contDiff_fst.pow 2).div_const 2).prodMk contDiff_snd

theorem fromRadius_smoothAt {F : InnerProfile} {w : InnerPoint} (hX : 0 < w.1)
    (hF : ContDiffAt ℝ ∞ F (Real.sqrt (2 * w.1), w.2)) :
    ContDiffAt ℝ ∞ (fromRadius F) w :=
  hF.comp w (((contDiffAt_const.mul contDiffAt_fst).sqrt (by positivity)).prodMk contDiffAt_snd)

theorem partialX_fromRadius {F : InnerProfile} {w : InnerPoint} (hX : 0 < w.1)
    (hF : DifferentiableAt ℝ F (Real.sqrt (2 * w.1), w.2)) :
    partialX (fromRadius F) w =
      partialX F (Real.sqrt (2 * w.1), w.2) / Real.sqrt (2 * w.1) := by
  have hs := (Real.hasDerivAt_sqrt (show 2 * w.1 ≠ 0 by positivity)).comp w.1
    ((hasDerivAt_id w.1).const_mul 2)
  have hd := hF.hasFDerivAt.comp_hasDerivAt w.1
    (hs.prodMk (hasDerivAt_const w.1 w.2))
  have hc : DifferentiableAt ℝ (fromRadius F) w :=
    hF.comp w ((((differentiableAt_const (2 : ℝ)).fun_mul differentiableAt_fst).sqrt
      (by positivity)).prodMk differentiableAt_snd)
  have he := (LeadingStress.partialX_hasDerivAt hc).unique hd
  refine he.trans ?_
  simp only [SimilarityProfile.fderiv_inner_apply, mul_zero, add_zero,
    mul_one, one_mul, div_eq_mul_inv, mul_inv_rev]
  ring

/-- At a positive radius the primitive stress is smooth without an axis
vanishing assumption. The latter is needed only to extend through R=0. -/
theorem primitive_stress_smoothAt {S : Set ℝ} (hS : IsOpen S)
    {F : InnerProfile} (hF : SlowStressSupport.Smooth S F) (m : ℕ)
    {w : InnerPoint} (hR : 0 < w.1) (heta : w.2 ∈ S) :
    ContDiffAt ℝ ∞ (SlowStressSupport.stress m F) w := by
  have hP := (ProfileHistories.primitive_smooth
    (PositiveOrderMoments.parameterDomain S hS) hF).contDiffAt
      ((isOpen_univ.prod hS).mem_nhds ⟨mem_univ _, heta⟩)
  have ht : ContDiffAt ℝ ∞ (fun p : InnerPoint => -ProfileHistories.primitive F p / p.1 ^ m) w :=
    hP.neg.div (contDiffAt_fst.pow m) (pow_ne_zero m hR.ne')
  apply ht.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt (Ioi_mem_nhds hR)] with p hp
  exact SlowStressSupport.stress_of_pos m F hp

theorem primitive_stress_radial_identity {S : Set ℝ} (hS : IsOpen S)
    {F : InnerProfile} (hF : SlowStressSupport.Smooth S F) (m : ℕ)
    {w : InnerPoint} (hR : 0 < w.1) (heta : w.2 ∈ S) :
    (m : ℝ) * w.1 ^ (m - 1) * SlowStressSupport.stress m F w +
      w.1 ^ m * partialX (SlowStressSupport.stress m F) w = -F w := by
  have ht := LeadingStress.partialX_hasDerivAt
    ((primitive_stress_smoothAt hS hF m hR heta).differentiableAt (by simp))
  have hp := ((hasDerivAt_id w.1).fun_pow m).fun_mul ht
  have he := hp.unique (SlowStressSupport.stress_weighted_hasDerivAt hS hF m hR heta)
  simpa only [id_eq, mul_one, Prod.eta] using he

/-- Literal R²-weighted angular residual. -/
noncomputable def thetaDensity (h C : ℝ) (f : SlowProfiles) (n : ℕ) (w : InnerPoint) : ℝ :=
  w.1 ^ 3 / C * angularCoefficient h f n (radiusPoint w)

/-- Literal R-weighted axial residual. -/
noncomputable def zDensity (h : ℝ) (f : SlowProfiles) (n : ℕ) (w : InnerPoint) : ℝ :=
  w.1 * axialCoefficient h f n (radiusPoint w)

/-- Theta stress, given by `fromRadius (SlowStressSupport.stress 2 (thetaDensity h C f n))`. -/
noncomputable def thetaStress (h C : ℝ) (f : SlowProfiles) (n : ℕ) : InnerProfile :=
  fromRadius (SlowStressSupport.stress 2 (thetaDensity h C f n))

/-- Z stress, given by `fromRadius (SlowStressSupport.stress 1 (zDensity h f n))`. -/
noncomputable def zStress (h : ℝ) (f : SlowProfiles) (n : ℕ) : InnerProfile :=
  fromRadius (SlowStressSupport.stress 1 (zDensity h f n))

theorem thetaStress_smoothAt {S : Set ℝ} (hS : IsOpen S) (h C : ℝ)
    (f : SlowProfiles) (n : ℕ) (hF : SlowStressSupport.Smooth S (thetaDensity h C f n))
    {w : InnerPoint} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    ContDiffAt ℝ ∞ (thetaStress h C f n) w :=
  fromRadius_smoothAt hX (primitive_stress_smoothAt hS hF 2
    (Real.sqrt_pos.2 (by positivity)) heta)

theorem zStress_smoothAt {S : Set ℝ} (hS : IsOpen S) (h : ℝ)
    (f : SlowProfiles) (n : ℕ) (hF : SlowStressSupport.Smooth S (zDensity h f n))
    {w : InnerPoint} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    ContDiffAt ℝ ∞ (zStress h f n) w :=
  fromRadius_smoothAt hX (primitive_stress_smoothAt hS hF 1
    (Real.sqrt_pos.2 (by positivity)) heta)

/-- The angular primitive has exactly the required unweighted divergence. -/
theorem thetaStress_identity {S : Set ℝ} (hS : IsOpen S) (h C : ℝ)
    (f : SlowProfiles) (n : ℕ) (hF : SlowStressSupport.Smooth S (thetaDensity h C f n))
    {w : InnerPoint} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    Real.sqrt (2 * w.1) * partialX (thetaStress h C f n) w +
      2 * thetaStress h C f n w / Real.sqrt (2 * w.1) =
        -(Real.sqrt (2 * w.1) / C * angularCoefficient h f n w) := by
  let r := Real.sqrt (2 * w.1)
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 2 * w.1 := Real.sq_sqrt (by positivity)
  have hw : radiusPoint (r, w.2) = w := by
    ext <;> simp [radiusPoint, hr2]
  have hi := primitive_stress_radial_identity hS hF 2 (w := (r, w.2)) hr heta
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at hi
  rw [thetaDensity, hw] at hi
  unfold thetaStress
  rw [partialX_fromRadius hX ((primitive_stress_smoothAt hS hF 2
    (w := (r, w.2)) hr heta).differentiableAt (by simp))]
  change r * (partialX (SlowStressSupport.stress 2 (thetaDensity h C f n)) (r, w.2) / r) +
      2 * SlowStressSupport.stress 2 (thetaDensity h C f n) (r, w.2) / r =
        -(r / C * angularCoefficient h f n w)
  apply mul_right_injective₀ (pow_ne_zero 2 hr.ne')
  field_simp [hr.ne']
  apply mul_left_cancel₀ hr.ne'
  linear_combination hi

theorem zStress_identity {S : Set ℝ} (hS : IsOpen S) (h : ℝ)
    (f : SlowProfiles) (n : ℕ) (hF : SlowStressSupport.Smooth S (zDensity h f n))
    {w : InnerPoint} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    Real.sqrt (2 * w.1) * partialX (zStress h f n) w +
      zStress h f n w / Real.sqrt (2 * w.1) = -axialCoefficient h f n w := by
  let r := Real.sqrt (2 * w.1)
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 2 * w.1 := Real.sq_sqrt (by positivity)
  have hw : radiusPoint (r, w.2) = w := by ext <;> simp [radiusPoint, hr2]
  have hi := primitive_stress_radial_identity hS hF 1 (w := (r, w.2)) hr heta
  norm_num only [Nat.cast_one, Nat.reduceSub, pow_zero, pow_one, one_mul] at hi
  rw [zDensity, hw] at hi
  unfold zStress
  rw [partialX_fromRadius hX ((primitive_stress_smoothAt hS hF 1
    (w := (r, w.2)) hr heta).differentiableAt (by simp))]
  change r * (partialX (SlowStressSupport.stress 1 (zDensity h f n)) (r, w.2) / r) +
      SlowStressSupport.stress 1 (zDensity h f n) (r, w.2) / r = -axialCoefficient h f n w
  apply mul_right_injective₀ hr.ne'
  field_simp [hr.ne']
  linear_combination hi

/-- Physical theta stress, given by `finiteProfile N h (angularExponent h) (thetaStress h C f)`. -/
noncomputable def physicalThetaStress (N : ℕ) (h C : ℝ) (f : SlowProfiles) : PhysicalProfile :=
  finiteProfile N h (angularExponent h) (thetaStress h C f)

/-- Physical Z stress, given by `finiteProfile N h (angularExponent h) (zStress h f)`. -/
noncomputable def physicalZStress (N : ℕ) (h : ℝ) (f : SlowProfiles) : PhysicalProfile :=
  finiteProfile N h (angularExponent h) (zStress h f)

theorem radialDivergence_sum {ι : Type*} (s : Finset ι) (k : ℝ)
    (F : ι → PhysicalProfile) (p : PhysicalPoint)
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) p) :
    LeadingStress.radialDivergence k (fun y => ∑ i ∈ s, F i y) p =
      ∑ i ∈ s, LeadingStress.radialDivergence k (F i) p := by
  unfold LeadingStress.radialDivergence
  change Real.sqrt (2 * p.2.1) * derivativeAlong (0, (1, 0)) _ p + _ = _
  rw [derivativeAlong_sum s F (0, (1, 0)) p hF]
  simp only [Finset.mul_sum, Finset.sum_div, Finset.sum_add_distrib]
  rfl

theorem physicalThetaStress_divergence {S : Set ℝ} (hS : IsOpen S)
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (N : ℕ) (C : ℝ) (f : SlowProfiles)
    (hF : ∀ n ≤ N, SlowStressSupport.Smooth S (thetaDensity h C f n))
    {p : PhysicalPoint} (hp : p.1 < 1) (hs : 0 < p.2.1)
    (heta : (SimilarityProfile.inner h p).2 ∈ S) :
    LeadingStress.radialDivergence 2 (physicalThetaStress N h C f) p =
      -(Real.sqrt (2 * p.2.1) * C⁻¹ *
        finiteSeries N (SimilarityProfile.q h p) h (angularExponent h - 1)
          (fun n => angularCoefficient h f n (SimilarityProfile.inner h p))) := by
  have hX := LeadingStress.inner_X_pos hh hh1 hp hs
  have hd : ∀ n ≤ N, DifferentiableAt ℝ (thetaStress h C f n) (SimilarityProfile.inner h p) :=
    fun n hn => (thetaStress_smoothAt hS h C f n (hF n hn) hX heta).differentiableAt (by simp)
  unfold physicalThetaStress finiteProfile
  rw [radialDivergence_sum _ _ _ _ (fun n hn => SimilarityProfile.pullback_differentiableAt
    hh hh1 hp (hd n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))))]
  unfold finiteSeries
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  rw [LeadingStress.radialDivergence_pullback hh hh1 2 hp (hd n hnN),
    thetaStress_identity hS h C f n (hF n hnN) hX heta]
  have he := LeadingStress.radius_mul_rpow hh hh1 (angularExponent h - 1 + slowOrder h n) hp
  rw [show angularExponent h - 1 + slowOrder h n + 1 / 2 =
    angularExponent h + slowOrder h n - 1 / 2 by ring] at he
  rw [show -(Real.sqrt (2 * p.2.1) * C⁻¹ *
        (SimilarityProfile.q h p ^ (angularExponent h - 1 + slowOrder h n) *
          angularCoefficient h f n (SimilarityProfile.inner h p))) =
      -(Real.sqrt (2 * p.2.1) *
        SimilarityProfile.q h p ^ (angularExponent h - 1 + slowOrder h n)) *
          (C⁻¹ * angularCoefficient h f n (SimilarityProfile.inner h p)) by ring, he]
  ring

theorem physicalZStress_divergence {S : Set ℝ} (hS : IsOpen S)
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (N : ℕ) (f : SlowProfiles)
    (hF : ∀ n ≤ N, SlowStressSupport.Smooth S (zDensity h f n))
    {p : PhysicalPoint} (hp : p.1 < 1) (hs : 0 < p.2.1)
    (heta : (SimilarityProfile.inner h p).2 ∈ S) :
    LeadingStress.radialDivergence 1 (physicalZStress N h f) p =
      -finiteSeries N (SimilarityProfile.q h p) h (axialExponent h - 1)
          (fun n => axialCoefficient h f n (SimilarityProfile.inner h p)) := by
  have hX := LeadingStress.inner_X_pos hh hh1 hp hs
  have hd : ∀ n ≤ N, DifferentiableAt ℝ (zStress h f n) (SimilarityProfile.inner h p) :=
    fun n hn => (zStress_smoothAt hS h f n (hF n hn) hX heta).differentiableAt (by simp)
  unfold physicalZStress finiteProfile
  rw [radialDivergence_sum _ _ _ _ (fun n hn => SimilarityProfile.pullback_differentiableAt
    hh hh1 hp (hd n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))))]
  unfold finiteSeries
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  rw [LeadingStress.radialDivergence_pullback hh hh1 1 hp (hd n hnN), one_mul,
    zStress_identity hS h f n (hF n hnN) hX heta]
  rw [show angularExponent h + slowOrder h n - 1 / 2 =
    axialExponent h - 1 + slowOrder h n by unfold angularExponent axialExponent; ring]
  ring

/-- The two radial tangential operators appearing in the manuscript.
They are written as an actual Cartesian vector; no unspecified tensor is used. -/
noncomputable def tangentialStressForce (theta axial : PhysicalProfile)
    (t : ℝ) (x : ProblemStatement.Space) : ProblemStatement.Space :=
  let r := Real.sqrt (2 * radialEnergy x)
  let a := LeadingStress.radialDivergence 2 theta (profilePoint t x)
  let z := LeadingStress.radialDivergence 1 axial (profilePoint t x)
  AxisymmetricResidual.pack (x 1 / r * a) (-x 0 / r * a) (-z)

/-- The pressure recurrence contributes this separate radial vector. -/
noncomputable def retainedRadialForce (N : ℕ) (h C : ℝ) (f : SlowProfiles)
    (t : ℝ) (x : ProblemStatement.Space) : ProblemStatement.Space :=
  let q := SimilarityProfile.q h (profilePoint t x)
  let w := SimilarityProfile.inner h (profilePoint t x)
  let r := (2 * w.1 * finiteSeries N q h (pressureExponent h)
    (fun n => pressureCoefficient h C f n w)) / (2 * radialEnergy x)
  AxisymmetricResidual.pack (x 0 * r) (x 1 * r) 0

/-- Exact finite field matching. All nonlinear interactions not in the
retained coefficients, the final axial viscosities, and the final radial
acceleration remain in the explicitly defined `truncationResidual`. -/
theorem navierStokesResidual_eq_stress_add_tails {S : Set ℝ} (hS : IsOpen S)
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (N : ℕ) (C : ℝ) (f : SlowProfiles)
    (hTheta : ∀ n ≤ N, SlowStressSupport.Smooth S (thetaDensity h C f n))
    (hZ : ∀ n ≤ N, SlowStressSupport.Smooth S (zDensity h f n))
    {t : ℝ} {x : ProblemStatement.Space} (ht : t < 1) (hs : 0 < radialEnergy x)
    (heta : (SimilarityProfile.inner h (profilePoint t x)).2 ∈ S)
    (hv : ∀ n ≤ N, ContDiffAt ℝ 2 (f.flux n) (SimilarityProfile.inner h (profilePoint t x)))
    (hphi : ∀ n ≤ N, ContDiffAt ℝ 2 (f.phi n) (SimilarityProfile.inner h (profilePoint t x)))
    (hu : ∀ n ≤ N, ContDiffAt ℝ 2 (f.axial n) (SimilarityProfile.inner h (profilePoint t x)))
    (hp : ∀ n ≤ N, DifferentiableAt ℝ (f.pressure n) (SimilarityProfile.inner h (profilePoint t
        x))) :
    ProblemStatement.navierStokesResidual (slowVelocity N h C f) (slowPressureField N h f) t x =
      tangentialStressForce (physicalThetaStress N h C f) (physicalZStress N h f) t x +
        retainedRadialForce N h C f t x + truncationResidual N h C f t x := by
  rw [navierStokesResidual_slowVelocity hh hh1 N C f ht hs hv hphi hu hp]
  have ha := physicalThetaStress_divergence hS hh hh1 N C f hTheta ht hs heta
  have hz := physicalZStress_divergence hS hh hh1 N f hZ ht hs heta
  have hr : Real.sqrt (2 * radialEnergy x) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  unfold tangentialStressForce
  rw [ha, hz]
  simp only [profilePoint] at *
  generalize hrdef : Real.sqrt (2 * radialEnergy x) = r at *
  ext i
  fin_cases i <;>
    simp [retainedRadialForce, truncationResidual, radialFluxExpansion,
      angularExpansion, axialExpansion, AxisymmetricResidual.pack,
      ProblemStatement.coordinateVector, profilePoint]
  all_goals field_simp [hr, hs.ne']
  all_goals ring_nf

/-- If the pressure was recomputed from its actual radial recurrence, the
finite residual consists of the tangential stress force and the explicit tails. -/
theorem navierStokesResidual_eq_stress_add_truncation {S : Set ℝ} (hS : IsOpen S)
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (N : ℕ) (C : ℝ) (f : SlowProfiles)
    (hTheta : ∀ n ≤ N, SlowStressSupport.Smooth S (thetaDensity h C f n))
    (hZ : ∀ n ≤ N, SlowStressSupport.Smooth S (zDensity h f n))
    {t : ℝ} {x : ProblemStatement.Space} (ht : t < 1) (hs : 0 < radialEnergy x)
    (heta : (SimilarityProfile.inner h (profilePoint t x)).2 ∈ S)
    (hv : ∀ n ≤ N, ContDiffAt ℝ 2 (f.flux n) (SimilarityProfile.inner h (profilePoint t x)))
    (hphi : ∀ n ≤ N, ContDiffAt ℝ 2 (f.phi n) (SimilarityProfile.inner h (profilePoint t x)))
    (hu : ∀ n ≤ N, ContDiffAt ℝ 2 (f.axial n) (SimilarityProfile.inner h (profilePoint t x)))
    (hp : ∀ n ≤ N, DifferentiableAt ℝ (f.pressure n) (SimilarityProfile.inner h (profilePoint t x)))
    (hpressure : ∀ n ≤ N, pressureCoefficient h C f n (SimilarityProfile.inner h (profilePoint t
        x)) = 0) :
    ProblemStatement.navierStokesResidual (slowVelocity N h C f) (slowPressureField N h f) t x =
      tangentialStressForce (physicalThetaStress N h C f) (physicalZStress N h f) t x +
        truncationResidual N h C f t x := by
  rw [navierStokesResidual_eq_stress_add_tails hS hh hh1 N C f hTheta hZ ht hs heta hv hphi hu hp]
  have he : retainedRadialForce N h C f t x = 0 := by
    unfold retainedRadialForce
    dsimp only
    rw [finiteSeries_eq_zero _ _ _ _ _ hpressure]
    ext i
    fin_cases i <;> simp [AxisymmetricResidual.pack]
  rw [he, add_zero]

theorem toRadius_differentiableAt {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f (radiusPoint w)) : DifferentiableAt ℝ (toRadius f) w :=
  hf.comp w (radiusPoint_smooth.differentiable (by simp)).differentiableAt

theorem toRadius_contDiffAt_two {f : InnerProfile} {w : InnerPoint}
    (hf : ContDiffAt ℝ 2 f (radiusPoint w)) : ContDiffAt ℝ 2 (toRadius f) w :=
  hf.comp w ((radiusPoint_smooth.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt)

theorem partialX_toRadius {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f (radiusPoint w)) :
    partialX (toRadius f) w = w.1 * partialX f (radiusPoint w) := by
  have hs : HasDerivAt (fun r : ℝ => r ^ 2 / 2) w.1 w.1 := by
    convert! ((hasDerivAt_id w.1).pow 2).div_const 2 using 1
    simp
  have hd := hf.hasFDerivAt.comp_hasDerivAt w.1 (hs.prodMk (hasDerivAt_const w.1 w.2))
  have he := (LeadingStress.partialX_hasDerivAt (toRadius_differentiableAt hf)).unique hd
  simpa only [SimilarityProfile.fderiv_inner_apply, mul_zero, zero_mul, add_zero,
    radiusPoint, mul_comm] using he

theorem partialEta_toRadius {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f (radiusPoint w)) :
    partialEta (toRadius f) w = partialEta f (radiusPoint w) := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt w.2
    ((hasDerivAt_const w.2 (w.1 ^ 2 / 2)).prodMk (hasDerivAt_id w.2))
  have he := (PositiveAxisSystem.hasDerivAt_parameterProfile
    (toRadius_differentiableAt hf)).unique hd
  simpa only [SimilarityProfile.fderiv_inner_apply, mul_zero, zero_mul, zero_add,
    one_mul, mul_one, radiusPoint, Prod.eta] using he

theorem partialX_swirlRadius (C : ℝ) {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f (radiusPoint w)) :
    partialX (swirlRadius C f) w =
      f (radiusPoint w) / C + w.1 ^ 2 / C * partialX f (radiusPoint w) := by
  have hg : DifferentiableAt ℝ (swirlRadius C f) w := by
    change DifferentiableAt ℝ (fun y : InnerPoint => y.1 / C * toRadius f y) w
    simpa only [div_eq_mul_inv] using ((show DifferentiableAt ℝ (fun y : InnerPoint => y.1) w from
      differentiableAt_fst).mul_const C⁻¹).fun_mul (toRadius_differentiableAt hf)
  have hd := ((hasDerivAt_id w.1).div_const C).mul
    (LeadingStress.partialX_hasDerivAt (toRadius_differentiableAt hf))
  have he := (LeadingStress.partialX_hasDerivAt hg).unique hd
  rw [partialX_toRadius hf] at he
  exact he.trans (by simp only [id_eq, toRadius]; ring)

theorem partialEta_swirlRadius (C : ℝ) {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f (radiusPoint w)) :
    partialEta (swirlRadius C f) w = w.1 / C * partialEta f (radiusPoint w) := by
  have hg : DifferentiableAt ℝ (swirlRadius C f) w := by
    change DifferentiableAt ℝ (fun y : InnerPoint => y.1 / C * toRadius f y) w
    simpa only [div_eq_mul_inv] using ((show DifferentiableAt ℝ (fun y : InnerPoint => y.1) w from
      differentiableAt_fst).mul_const C⁻¹).fun_mul (toRadius_differentiableAt hf)
  have hd := (PositiveAxisSystem.hasDerivAt_parameterProfile
    (toRadius_differentiableAt hf)).const_mul (w.1 / C)
  have he := (PositiveAxisSystem.hasDerivAt_parameterProfile hg).unique hd
  simpa only [partialEta_toRadius hf] using he

theorem partialXX_toRadius {f : InnerProfile} {w : InnerPoint}
    (hf : ContDiffAt ℝ 2 f (radiusPoint w)) :
    partialX (partialX (toRadius f)) w =
      partialX f (radiusPoint w) + w.1 ^ 2 * partialX (partialX f) (radiusPoint w) := by
  have he : partialX (toRadius f) =ᶠ[𝓝 w]
      AxisSourceRegularity.axisFactor (toRadius (partialX f)) := by
    have hh := radiusPoint_smooth.continuous.continuousAt (hf.eventually (by norm_num))
    filter_upwards [hh] with y hy
    change ContDiffAt ℝ 2 f (radiusPoint y) at hy
    exact partialX_toRadius (hy.differentiableAt (by norm_num))
  have hx := (PositiveAxisSystem.partialX_contDiffAt hf).differentiableAt (by norm_num)
  change (fderiv ℝ (partialX (toRadius f)) w) (1, 0) = _
  rw [he.fderiv_eq]
  change partialX (AxisSourceRegularity.axisFactor (toRadius (partialX f))) w = _
  rw [AxisSourceRegularity.partialX_axisFactor (toRadius_differentiableAt hx), partialX_toRadius hx]
  simp only [toRadius]
  ring

theorem timeOp_toRadius (h b : ℝ) {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f (radiusPoint w)) :
    SlowStressSupport.timeOp h b (toRadius f) w = T h b f (radiusPoint w) := by
  unfold SlowStressSupport.timeOp
  change (-b * toRadius f w + PositiveAxisSystem.dScale h * w.2 * partialEta (toRadius f) w +
    w.1 / 2 * partialX (toRadius f) w) / _ = _
  rw [partialX_toRadius hf, partialEta_toRadius hf]
  simp only [T, CoordinateAlgebra.timeCoeff, radiusPoint, toRadius,
    PositiveAxisSystem.dScale, CoordinateAlgebra.D, PositiveAxisSystem.ell, CoordinateAlgebra.L]
  ring

theorem axialOp_toRadius (h b : ℝ) {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f (radiusPoint w)) :
    SlowStressSupport.axialOp h b (toRadius f) w = Z h b f (radiusPoint w) := by
  unfold SlowStressSupport.axialOp
  change (2 * w.2 * b * toRadius f w + PositiveAxisSystem.edge w.2 * partialEta (toRadius f) w -
    w.2 * w.1 * partialX (toRadius f) w) / _ = _
  rw [partialX_toRadius hf, partialEta_toRadius hf]
  simp only [Z, CoordinateAlgebra.axialCoeff, radiusPoint, toRadius,
    PositiveAxisSystem.edge, CoordinateAlgebra.d, PositiveAxisSystem.ell, CoordinateAlgebra.L]
  ring

theorem timeOp_swirlRadius (h b C : ℝ) {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f (radiusPoint w)) :
    SlowStressSupport.timeOp h b (swirlRadius C f) w =
      w.1 / C * T h (b - 1 / 2) f (radiusPoint w) := by
  unfold SlowStressSupport.timeOp
  change (-b * swirlRadius C f w + PositiveAxisSystem.dScale h * w.2 * partialEta (swirlRadius C f)
      w +
    w.1 / 2 * partialX (swirlRadius C f) w) / _ = _
  rw [partialX_swirlRadius C hf, partialEta_swirlRadius C hf]
  simp only [T, CoordinateAlgebra.timeCoeff, swirlRadius, toRadius, radiusPoint,
    PositiveAxisSystem.dScale, CoordinateAlgebra.D, PositiveAxisSystem.ell, CoordinateAlgebra.L]
  ring

theorem axialOp_swirlRadius (h b C : ℝ) {f : InnerProfile} {w : InnerPoint}
    (hf : DifferentiableAt ℝ f (radiusPoint w)) :
    SlowStressSupport.axialOp h b (swirlRadius C f) w =
      w.1 / C * Z h (b - 1 / 2) f (radiusPoint w) := by
  unfold SlowStressSupport.axialOp
  change (2 * w.2 * b * swirlRadius C f w + PositiveAxisSystem.edge w.2 * partialEta (swirlRadius C
      f) w -
    w.2 * w.1 * partialX (swirlRadius C f) w) / _ = _
  rw [partialX_swirlRadius C hf, partialEta_swirlRadius C hf]
  simp only [Z, CoordinateAlgebra.axialCoeff, swirlRadius, toRadius, radiusPoint,
    PositiveAxisSystem.edge, CoordinateAlgebra.d, PositiveAxisSystem.ell, CoordinateAlgebra.L]
  ring

theorem axialOp_congr_germ (h b : ℝ) {f g : InnerProfile} {w : InnerPoint}
    (hfg : f =ᶠ[𝓝 w] g) :
    SlowStressSupport.axialOp h b f w = SlowStressSupport.axialOp h b g w := by
  simp only [SlowStressSupport.axialOp, SlowStressSupport.dr, SlowStressSupport.de,
    ProfileHistories.radialPartial, ProfileHistories.parameterPartial,
    hfg.eq_of_nhds, hfg.fderiv_eq]

theorem axialOp2_toRadius (h b : ℝ) {f : InnerProfile} {w : InnerPoint}
    (hf : ContDiffAt ℝ 2 f (radiusPoint w)) (hL : CoordinateAlgebra.L h w.2 ≠ 0) :
    SlowStressSupport.axialOp2 h b (toRadius f) w = Z2 h b f (radiusPoint w) := by
  have he : SlowStressSupport.axialOp h b (toRadius f) =ᶠ[𝓝 w] toRadius (Z h b f) := by
    have hh := radiusPoint_smooth.continuous.continuousAt (hf.eventually (by norm_num))
    filter_upwards [hh] with y hy
    change ContDiffAt ℝ 2 f (radiusPoint y) at hy
    exact axialOp_toRadius h b (hy.differentiableAt (by norm_num))
  unfold SlowStressSupport.axialOp2
  rw [axialOp_congr_germ h (b - PositiveAxisSystem.dScale h) he,
    axialOp_toRadius h (b - PositiveAxisSystem.dScale h)
      ((SimilarityProfile.Z_smoothAt hf hL).differentiableAt (by norm_num))]
  rfl

theorem axialOp2_swirlRadius (h b C : ℝ) {f : InnerProfile} {w : InnerPoint}
    (hf : ContDiffAt ℝ 2 f (radiusPoint w)) (hL : CoordinateAlgebra.L h w.2 ≠ 0) :
    SlowStressSupport.axialOp2 h b (swirlRadius C f) w =
      w.1 / C * Z2 h (b - 1 / 2) f (radiusPoint w) := by
  have he : SlowStressSupport.axialOp h b (swirlRadius C f) =ᶠ[𝓝 w]
      swirlRadius C (Z h (b - 1 / 2) f) := by
    have hh := radiusPoint_smooth.continuous.continuousAt (hf.eventually (by norm_num))
    filter_upwards [hh] with y hy
    change ContDiffAt ℝ 2 f (radiusPoint y) at hy
    exact axialOp_swirlRadius h b C (hy.differentiableAt (by norm_num))
  unfold SlowStressSupport.axialOp2
  rw [axialOp_congr_germ h (b - PositiveAxisSystem.dScale h) he,
    axialOp_swirlRadius h (b - PositiveAxisSystem.dScale h) C
      ((SimilarityProfile.Z_smoothAt hf hL).differentiableAt (by norm_num))]
  rw [show b - PositiveAxisSystem.dScale h - 1 / 2 =
      b - 1 / 2 - CoordinateAlgebra.D h by
        unfold PositiveAxisSystem.dScale CoordinateAlgebra.D; ring]
  rfl

theorem partialXX_swirlRadius (C : ℝ) {f : InnerProfile} {w : InnerPoint}
    (hf : ContDiffAt ℝ 2 f (radiusPoint w)) :
    partialX (partialX (swirlRadius C f)) w =
      3 * w.1 / C * partialX f (radiusPoint w) +
        w.1 ^ 3 / C * partialX (partialX f) (radiusPoint w) := by
  have he : partialX (swirlRadius C f) =ᶠ[𝓝 w]
      (fun y => toRadius f y / C + y.1 ^ 2 / C * toRadius (partialX f) y) := by
    have hh := radiusPoint_smooth.continuous.continuousAt (hf.eventually (by norm_num))
    filter_upwards [hh] with y hy
    change ContDiffAt ℝ 2 f (radiusPoint y) at hy
    exact partialX_swirlRadius C (hy.differentiableAt (by norm_num))
  have hf' := hf.differentiableAt (by norm_num)
  have hfx := (PositiveAxisSystem.partialX_contDiffAt hf).differentiableAt (by norm_num)
  have hG : DifferentiableAt ℝ
      (fun y : InnerPoint => toRadius f y / C + y.1 ^ 2 / C * toRadius (partialX f) y) w := by
    simpa only [div_eq_mul_inv] using ((toRadius_differentiableAt hf').mul_const C⁻¹).fun_add
      (((show DifferentiableAt ℝ (fun y : InnerPoint => y.1) w from
          differentiableAt_fst).fun_pow 2).mul_const C⁻¹ |>.fun_mul (toRadius_differentiableAt hfx))
  have hd := ((LeadingStress.partialX_hasDerivAt (toRadius_differentiableAt hf')).div_const
      C).fun_add
    ((((hasDerivAt_id w.1).fun_pow 2).div_const C).fun_mul
      (LeadingStress.partialX_hasDerivAt (toRadius_differentiableAt hfx)))
  have hv := (LeadingStress.partialX_hasDerivAt hG).unique hd
  change (fderiv ℝ (partialX (swirlRadius C f)) w) (1, 0) = _
  rw [he.fderiv_eq]
  change partialX (fun y : InnerPoint => toRadius f y / C +
    y.1 ^ 2 / C * toRadius (partialX f) y) w = _
  rw [hv, partialX_toRadius hf', partialX_toRadius hfx]
  simp only [toRadius, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

/-- An explicit finite index for all omitted transport terms. `none` is
the last axial-viscosity coefficient. -/
abbrev TailIndex := Option (ℕ × ℕ)

/-- Transport indices, given by `insert none (((pairs N).filter (fun ij => N < ij.1 +
ij.2)).image some)`. -/
noncomputable def transportIndices (N : ℕ) : Finset TailIndex :=
  insert none (((pairs N).filter (fun ij => N < ij.1 + ij.2)).image some)

/-- Transport power as an element of `TailIndex → ℝ | none => e - 1 + slowOrder h (N + 1) | some
ij => e - 1 + slowOrder h (ij.1 + ij.2)`. -/
noncomputable def transportPower (N : ℕ) (h e : ℝ) : TailIndex → ℝ
  | none => e - 1 + slowOrder h (N + 1)
  | some ij => e - 1 + slowOrder h (ij.1 + ij.2)

/-- Transport term as an element of `TailIndex → InnerProfile | none => fun w => -Z2 h (e +
slowOrder h N) (f N) w | some ij => fun w => transportKernel h e α v u f w ij.1 ij.2`. -/
noncomputable def transportTerm (N : ℕ) (h e α : ℝ)
    (v u f : ℕ → InnerProfile) : TailIndex → InnerProfile
  | none => fun w => -Z2 h (e + slowOrder h N) (f N) w
  | some ij => fun w => transportKernel h e α v u f w ij.1 ij.2

theorem mem_transportIndices_some (N : ℕ) (ij : ℕ × ℕ) :
    some ij ∈ transportIndices N ↔ ij ∈ pairs N ∧ N < ij.1 + ij.2 := by
  simp [transportIndices]

/-- This equality is an identity of actual functions, suitable for taking
any fixed number of derivatives in q and the inner variables. -/
theorem transportTail_eq_finite_monomials (N : ℕ) (q h e α : ℝ)
    (v u f : ℕ → InnerProfile) (w : InnerPoint) :
    transportTail N q h e α v u f w =
      ∑ i ∈ transportIndices N, q ^ transportPower N h e i * transportTerm N h e α v u f i w := by
  unfold transportIndices
  rw [Finset.sum_insert (by simp), Finset.sum_image]
  · simp only [transportPower, transportTerm]
    change _ = _ + pairTail N (fun n => q ^ (e - 1 + slowOrder h n))
      (transportKernel h e α v u f w)
    unfold transportTail transportKernel
    ring
  · intro i hi j hj he
    exact Option.some.inj he

theorem transportPower_lower {h : ℝ} (hh : 0 ≤ h) (N : ℕ) (e : ℝ)
    {i : TailIndex} (hi : i ∈ transportIndices N) :
    e - 1 + slowOrder h (N + 1) ≤ transportPower N h e i := by
  cases i with
  | none => exact le_rfl
  | some ij =>
    exact add_le_add_right (slowOrder_mono hh ((mem_transportIndices_some N ij).mp hi).2) _

theorem transportKernel_smoothAt (h e α : ℝ) (v u f : ℕ → InnerProfile)
    (i j : ℕ) {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ (v i) w) (hu : ContDiffAt ℝ ∞ (u i) w)
    (hf : ContDiffAt ℝ ∞ (f j) w) (hX : w.1 ≠ 0) (hL : CoordinateAlgebra.L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => transportKernel h e α v u f y i j) w := by
  exact (hv.mul ((AxisSourceRegularity.partialX_smooth hf).add
    ((contDiffAt_const.mul hf).div contDiffAt_fst hX))).add
      (hu.mul (AxisSourceRegularity.Z_smooth h (e + slowOrder h j) hf hL))

theorem transportTerm_smoothOn {O : Set InnerPoint} (hO : IsOpen O)
    (N : ℕ) (h e α : ℝ) (v u f : ℕ → InnerProfile)
    (hv : ∀ j ≤ N, ContDiffOn ℝ ∞ (v j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hf : ∀ j ≤ N, ContDiffOn ℝ ∞ (f j) O)
    (hX : ∀ w ∈ O, w.1 ≠ 0) (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0)
    {i : TailIndex} (hi : i ∈ transportIndices N) :
    ContDiffOn ℝ ∞ (transportTerm N h e α v u f i) O := by
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  cases i with
  | none =>
    exact (AxisSourceRegularity.Z2_smooth h (e + slowOrder h N)
      ((hf N le_rfl).contDiffAt (hO.mem_nhds hw)) (hL w hw)).neg
  | some ij =>
    have hij := (mem_transportIndices_some N ij).mp hi
    have hj : ij.2 ≤ N := by
      have := (Finset.mem_product.mp hij.1).2
      exact Nat.le_of_lt_succ (Finset.mem_range.mp this)
    have hi' : ij.1 ≤ N := by
      have := (Finset.mem_product.mp hij.1).1
      exact Nat.le_of_lt_succ (Finset.mem_range.mp this)
    exact transportKernel_smoothAt h e α v u f ij.1 ij.2
      ((hv ij.1 hi').contDiffAt (hO.mem_nhds hw))
      ((hu ij.1 hi').contDiffAt (hO.mem_nhds hw))
      ((hf ij.2 hj).contDiffAt (hO.mem_nhds hw)) (hX w hw) (hL w hw)

theorem transportCoefficient_smoothAt (h e α m : ℝ)
    (v u f source : ℕ → InnerProfile) (n : ℕ) {w : InnerPoint}
    (hv : ∀ j ≤ n, ContDiffAt ℝ ∞ (v j) w)
    (hu : ∀ j ≤ n, ContDiffAt ℝ ∞ (u j) w)
    (hf : ∀ j ≤ n, ContDiffAt ℝ ∞ (f j) w)
    (hs : ContDiffAt ℝ ∞ (source n) w)
    (hX : w.1 ≠ 0) (hL : CoordinateAlgebra.L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (transportCoefficient h e α m v u f source n) w := by
  have hx := AxisSourceRegularity.partialX_smooth (hf n le_rfl)
  have hxx := AxisSourceRegularity.partialX_smooth hx
  have hlin : ContDiffAt ℝ ∞
      (fun y => transportLinear y.1 m (fun j => T h (e + slowOrder h j) (f j) y)
        (fun j => partialX (f j) y) (fun j => partialX (partialX (f j)) y)
        (fun j => source j y) n) w :=
    ((AxisSourceRegularity.T_smooth h (e + slowOrder h n) (hf n le_rfl) hL).sub
      (contDiffAt_const.mul ((contDiffAt_fst.mul hxx).add (contDiffAt_const.mul hx)))).add hs
  have hc : ContDiffAt ℝ ∞
      (fun y => convolution (transportKernel h e α v u f y) n) w := by
    apply ContDiffAt.sum
    intro ij hij
    have hi : ij.1 ≤ n := by have := Finset.mem_antidiagonal.mp hij; omega
    have hj : ij.2 ≤ n := by have := Finset.mem_antidiagonal.mp hij; omega
    exact transportKernel_smoothAt h e α v u f ij.1 ij.2 (hv ij.1 hi) (hu ij.1 hi)
      (hf ij.2 hj) hX hL
  have hp : ContDiffAt ℝ ∞
      (fun y => previous (fun j => Z2 h (e + slowOrder h j) (f j) y) n) w := by
    cases n with
    | zero => exact contDiffAt_const
    | succ n =>
      exact AxisSourceRegularity.Z2_smooth h (e + slowOrder h n) (hf n (Nat.le_succ n)) hL
  exact (hlin.add hc).sub hp

/-- Pressure index: an abbreviation for `Sum TailIndex TailIndex`. -/
abbrev PressureIndex := Sum TailIndex TailIndex

/-- Pressure indices, given by `((transportIndices N).image Sum.inl) ∪ ((transportIndices
N).image Sum.inr)`. -/
noncomputable def pressureIndices (N : ℕ) : Finset PressureIndex :=
  ((transportIndices N).image Sum.inl) ∪ ((transportIndices N).image Sum.inr)

/-- Pressure power used in slow residual matching. -/
noncomputable def pressurePower (N : ℕ) (h : ℝ) : PressureIndex → ℝ
  | Sum.inl i => transportPower N h 0 i
  | Sum.inr none => pressureExponent h + slowOrder h (N + 1)
  | Sum.inr (some ij) => pressureExponent h + slowOrder h (ij.1 + ij.2)

/-- Pressure term used in slow residual matching. -/
noncomputable def pressureTerm (N : ℕ) (h C : ℝ) (f : SlowProfiles) : PressureIndex → InnerProfile
  | Sum.inl i => transportTerm N h 0 (-(1 / 2)) f.flux f.axial f.flux i
  | Sum.inr none => omegaCoefficient h f N
  | Sum.inr (some ij) => fun w => -(2 * w.1 * C⁻¹ ^ 2) * (f.phi ij.1 w * f.phi ij.2 w)

theorem pressure_indices_disjoint (N : ℕ) :
    Disjoint ((transportIndices N).image (Sum.inl : TailIndex → PressureIndex))
      ((transportIndices N).image Sum.inr) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  rcases Finset.mem_image.mp hi with ⟨a, ha, rfl⟩
  rcases Finset.mem_image.mp hj with ⟨b, hb, he⟩
  cases he

theorem pressureTail_eq_finite_monomials (N : ℕ) (q h C : ℝ)
    (f : SlowProfiles) (w : InnerPoint) :
    pressureTail N q h C f w =
      ∑ i ∈ pressureIndices N, q ^ pressurePower N h i * pressureTerm N h C f i w := by
  unfold pressureIndices
  rw [Finset.sum_union (pressure_indices_disjoint N),
    Finset.sum_image (fun _ _ _ _ he => Sum.inl.inj he),
    Finset.sum_image (fun _ _ _ _ he => Sum.inr.inj he)]
  simp only [pressurePower, pressureTerm]
  rw [← transportTail_eq_finite_monomials]
  unfold transportIndices
  rw [Finset.sum_insert (by simp), Finset.sum_image (fun _ _ _ _ he => Option.some.inj he)]
  simp only []
  unfold pressureTail pairTail
  rw [Finset.mul_sum]
  have he : (∑ x ∈ {ij ∈ pairs N | N < ij.1 + ij.2},
      q ^ (pressureExponent h + slowOrder h (x.1 + x.2)) *
        (-(2 * w.1 * C⁻¹ ^ 2) * (f.phi x.1 w * f.phi x.2 w))) =
      -(∑ x ∈ {ij ∈ pairs N | N < ij.1 + ij.2},
        2 * w.1 * C⁻¹ ^ 2 *
          (q ^ (pressureExponent h + slowOrder h (x.1 + x.2)) * (f.phi x.1 w * f.phi x.2 w))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  ring

theorem pressurePower_lower {h : ℝ} (hh : 0 ≤ h) (N : ℕ)
    {i : PressureIndex} (hi : i ∈ pressureIndices N) :
    pressureExponent h + slowOrder h (N + 1) ≤ pressurePower N h i := by
  cases i with
  | inl i =>
    have hi' : i ∈ transportIndices N := by simpa [pressureIndices] using hi
    refine le_trans ?_ (transportPower_lower hh N 0 hi')
    unfold pressureExponent CoordinateAlgebra.A
    linarith
  | inr i =>
    have hi' : i ∈ transportIndices N := by simpa [pressureIndices] using hi
    cases i with
    | none => exact le_rfl
    | some ij =>
      exact add_le_add_right (slowOrder_mono hh ((mem_transportIndices_some N ij).mp hi').2) _

theorem pressureTerm_smoothOn {O : Set InnerPoint} (hO : IsOpen O)
    (N : ℕ) (h C : ℝ) (f : SlowProfiles)
    (hv : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.flux j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.axial j) O)
    (hf : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.phi j) O)
    (hX : ∀ w ∈ O, w.1 ≠ 0) (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0)
    {i : PressureIndex} (hi : i ∈ pressureIndices N) :
    ContDiffOn ℝ ∞ (pressureTerm N h C f i) O := by
  cases i with
  | inl i =>
    have hi' : i ∈ transportIndices N := by simpa [pressureIndices] using hi
    exact transportTerm_smoothOn hO N h 0 (-(1/2)) f.flux f.axial f.flux hv hu hv hX hL hi'
  | inr i =>
    have hi' : i ∈ transportIndices N := by simpa [pressureIndices] using hi
    cases i with
    | none =>
      intro w hw
      exact (transportCoefficient_smoothAt h 0 (-(1/2)) 0 f.flux f.axial f.flux (fun _ _ => 0) N
        (fun j hj => (hv j hj).contDiffAt (hO.mem_nhds hw))
        (fun j hj => (hu j hj).contDiffAt (hO.mem_nhds hw))
        (fun j hj => (hv j hj).contDiffAt (hO.mem_nhds hw))
        contDiffAt_const (hX w hw) (hL w hw)).contDiffWithinAt
    | some ij =>
      have hij := (mem_transportIndices_some N ij).mp hi'
      have hiN : ij.1 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hij.1).1)
      have hjN : ij.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hij.1).2)
      exact (((contDiffOn_const.mul contDiffOn_fst).mul contDiffOn_const).neg).mul
        ((hf ij.1 hiN).mul (hf ij.2 hjN))

/-- Division by the physical radial energy is converted to a single q
power and an ordinary smooth inner coefficient away from X=0. -/
theorem radialTail_eq_finite_monomials {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (C : ℝ) (f : SlowProfiles) {p : PhysicalPoint} (hp : p.1 < 1)
    (hs : 0 < p.2.1) :
    pressureTail N (SimilarityProfile.q h p) h C f (SimilarityProfile.inner h p) / (2 * p.2.1) =
      ∑ i ∈ pressureIndices N,
        SimilarityProfile.q h p ^ (pressurePower N h i - 1) *
          (pressureTerm N h C f i (SimilarityProfile.inner h p) /
            (2 * (SimilarityProfile.inner h p).1)) := by
  have hq := SimilarityProfile.q_pos hh hh1 hp
  have hX := LeadingStress.inner_X_pos hh hh1 hp hs
  rw [pressureTail_eq_finite_monomials, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.rpow_sub hq, Real.rpow_one, ← q_mul_X hh hh1 hp]
  field_simp [hq.ne', hX.ne']

theorem common_tail_power_lower {h : ℝ} (hh : 0 ≤ h) (N : ℕ) :
    pressureExponent h - 1 + slowOrder h (N + 1) = 2 * (N : ℝ) * h - 2 ∧
    pressureExponent h - 1 + slowOrder h (N + 1) ≤
      angularExponent h - 1 + slowOrder h (N + 1) ∧
    pressureExponent h - 1 + slowOrder h (N + 1) ≤
      axialExponent h - 1 + slowOrder h (N + 1) := by
  simp only [pressureExponent, angularExponent, axialExponent, CoordinateAlgebra.A,
    slowOrder, Nat.cast_add, Nat.cast_one]
  constructor
  · ring
  constructor <;> linarith

/-- Compact coefficient jets give a uniform bound for every fixed inner
derivative of a finite sum of actual powers. The exponent is unchanged by
inner differentiation. -/
theorem finite_monomial_inner_jet_bound {ι : Type*} (s : Finset ι)
    (b : ι → ℝ) (F : ι → InnerProfile) (bmin : ℝ)
    {O K : Set InnerPoint} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (hF : ∀ i ∈ s, ContDiffOn ℝ ∞ (F i) O) (hb : ∀ i ∈ s, bmin ≤ b i) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ w ∈ K,
      ‖iteratedFDeriv ℝ m (fun y => ∑ i ∈ s, q ^ b i * F i y) w‖ ≤ C * q ^ bmin := by
  classical
  have hex : ∀ i : ι, ∃ D : ℝ, 1 ≤ D ∧
      ∀ w ∈ K, i ∈ s → ‖iteratedFDeriv ℝ m (F i) w‖ ≤ D := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨D, hD, hDb⟩ := SlowBorelBase.compact_jet_bound hO (hF i hi) hK hKO m
      exact ⟨D, hD, fun w hw _ => hDb w hw⟩
    · exact ⟨1, le_rfl, fun _ _ hi' => (hi hi').elim⟩
  choose D hD hDb using hex
  have hDn : ∀ i, 0 ≤ D i := fun i => zero_le_one.trans (hD i)
  let C := 1 + ∑ i ∈ s, D i
  have hC : 0 < C := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ s) => hDn i)
    dsimp [C]
    linarith
  refine ⟨C, hC, fun q hq hq1 w hw => ?_⟩
  have hwO := hKO hw
  have hmn : (m : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  have hsum := iteratedFDerivWithin_fun_sum_apply (𝕜 := ℝ) (i := m) hO.uniqueDiffOn hwO
    (fun i hi => ((hF i hi w hwO).const_smul (q ^ b i)).of_le hmn)
  have hs : iteratedFDeriv ℝ m (fun y => ∑ i ∈ s, q ^ b i * F i y) w =
      ∑ i ∈ s, iteratedFDeriv ℝ m (fun y => q ^ b i * F i y) w := by
    simpa only [iteratedFDerivWithin_of_isOpen _ hO hwO, smul_eq_mul] using hsum
  rw [hs]
  calc
    _ ≤ ∑ i ∈ s, ‖iteratedFDeriv ℝ m (fun y => q ^ b i * F i y) w‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, D i * q ^ bmin := by
      apply Finset.sum_le_sum
      intro i hi
      have he : iteratedFDeriv ℝ m (fun y => q ^ b i * F i y) w =
          q ^ b i • iteratedFDeriv ℝ m (F i) w := by
        simpa only [smul_eq_mul] using iteratedFDeriv_const_smul_apply' (a := q ^ b i)
          (((hF i hi).contDiffAt (hO.mem_nhds hwO)).of_le hmn)
      rw [he, norm_smul (q ^ b i : ℝ) (iteratedFDeriv ℝ m (F i) w),
        Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hq _)]
      calc
        _ ≤ q ^ b i * D i := mul_le_mul_of_nonneg_left (hDb i w hw hi) (Real.rpow_nonneg hq.le _)
        _ ≤ q ^ bmin * D i := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge hq hq1 (hb i hi)) (hDn i)
        _ = _ := mul_comm _ _
    _ = (∑ i ∈ s, D i) * q ^ bmin := (Finset.sum_mul _ _ _).symm
    _ ≤ C * q ^ bmin := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
      (Real.rpow_nonneg hq.le _)

theorem transportTail_inner_jet_bound {O K : Set InnerPoint} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) {h : ℝ} (hh : 0 ≤ h)
    (N : ℕ) (e α : ℝ) (v u f : ℕ → InnerProfile)
    (hv : ∀ j ≤ N, ContDiffOn ℝ ∞ (v j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hf : ∀ j ≤ N, ContDiffOn ℝ ∞ (f j) O)
    (hX : ∀ w ∈ O, w.1 ≠ 0) (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ w ∈ K,
      ‖iteratedFDeriv ℝ m (transportTail N q h e α v u f) w‖ ≤
        C * q ^ (e - 1 + slowOrder h (N + 1)) := by
  obtain ⟨C, hC, hb⟩ := finite_monomial_inner_jet_bound (transportIndices N)
    (transportPower N h e) (transportTerm N h e α v u f) (e - 1 + slowOrder h (N + 1))
    hO hK hKO (fun i hi => transportTerm_smoothOn hO N h e α v u f hv hu hf hX hL hi)
    (fun i hi => transportPower_lower hh N e hi) m
  refine ⟨C, hC, fun q hq hq1 w hw => ?_⟩
  have he : transportTail N q h e α v u f =
      fun y => ∑ i ∈ transportIndices N, q ^ transportPower N h e i * transportTerm N h e α v u f i
          y :=
    funext (transportTail_eq_finite_monomials N q h e α v u f)
  rw [he]
  exact hb q hq hq1 w hw

theorem pressureTail_inner_jet_bound {O K : Set InnerPoint} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) {h : ℝ} (hh : 0 ≤ h)
    (N : ℕ) (C₀ : ℝ) (f : SlowProfiles)
    (hv : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.flux j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.axial j) O)
    (hf : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.phi j) O)
    (hX : ∀ w ∈ O, w.1 ≠ 0) (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ w ∈ K,
      ‖iteratedFDeriv ℝ m (pressureTail N q h C₀ f) w‖ ≤
        C * q ^ (pressureExponent h + slowOrder h (N + 1)) := by
  obtain ⟨C, hC, hb⟩ := finite_monomial_inner_jet_bound (pressureIndices N)
    (pressurePower N h) (pressureTerm N h C₀ f) (pressureExponent h + slowOrder h (N + 1))
    hO hK hKO (fun i hi => pressureTerm_smoothOn hO N h C₀ f hv hu hf hX hL hi)
    (fun i hi => pressurePower_lower hh N hi) m
  refine ⟨C, hC, fun q hq hq1 w hw => ?_⟩
  have he : pressureTail N q h C₀ f =
      fun y => ∑ i ∈ pressureIndices N, q ^ pressurePower N h i * pressureTerm N h C₀ f i y :=
    funext (pressureTail_eq_finite_monomials N q h C₀ f)
  rw [he]
  exact hb q hq hq1 w hw

theorem orderExponent_eq_axial (h : ℝ) (n : ℕ) :
    SlowStressSupport.orderExponent h n = axialExponent h + slowOrder h n := rfl

theorem orderExponent_sub_half (h : ℝ) (n : ℕ) :
    SlowStressSupport.orderExponent h n - 1 / 2 = angularExponent h + slowOrder h n := by
  unfold SlowStressSupport.orderExponent angularExponent PositiveAxisSystem.a CoordinateAlgebra.A
  ring

theorem previous_of_pos (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) : previous a n = a (n - 1) := by
  cases n with
  | zero => omega
  | succ n => rfl

theorem angular_radius_pair (h C : ℝ) (hC : C ≠ 0) (f : SlowProfiles) (i j : ℕ)
    {w : InnerPoint} (hR : w.1 ≠ 0)
    (hf : DifferentiableAt ℝ (f.phi j) (radiusPoint w)) :
    w.1 * toRadius (f.flux i) w * partialX (swirlRadius C (f.phi j)) w +
        toRadius (f.flux i) w * swirlRadius C (f.phi j) w +
        w.1 ^ 2 * toRadius (f.axial i) w *
          SlowStressSupport.axialOp h (SlowStressSupport.orderExponent h j) (swirlRadius C (f.phi
              j)) w =
      w.1 ^ 3 / C * transportKernel h (angularExponent h) 1 f.flux f.axial f.phi
        (radiusPoint w) i j := by
  rw [partialX_swirlRadius C hf, axialOp_swirlRadius h _ C hf, orderExponent_sub_half]
  simp only [toRadius, swirlRadius, transportKernel, transportPair, one_mul, radiusPoint]
  field_simp [hC, hR]; ring

theorem axial_radius_pair (h : ℝ) (f : SlowProfiles) (i j : ℕ)
    {w : InnerPoint} (hf : DifferentiableAt ℝ (f.axial j) (radiusPoint w)) :
    toRadius (f.flux i) w * partialX (toRadius (f.axial j)) w +
        w.1 * toRadius (f.axial i) w *
          SlowStressSupport.axialOp h (SlowStressSupport.orderExponent h j) (toRadius (f.axial j))
              w =
      w.1 * transportKernel h (axialExponent h) 0 f.flux f.axial f.axial
        (radiusPoint w) i j := by
  rw [partialX_toRadius hf, axialOp_toRadius h _ hf, orderExponent_eq_axial]
  simp only [toRadius, transportKernel, transportPair, zero_mul, zero_div, add_zero]
  ring

/-- The canonical R-coordinate weighted angular residual is exactly the
coefficient used by the finite Cartesian expansion. -/
theorem angularWeighted_eq_thetaDensity (h C : ℝ) (hC : C ≠ 0)
    (f : SlowProfiles) {n : ℕ} (hn : 0 < n) {w : InnerPoint} (hR : w.1 ≠ 0)
    (hf : ∀ j ≤ n, ContDiffAt ℝ 2 (f.phi j) (radiusPoint w))
    (hL : CoordinateAlgebra.L h w.2 ≠ 0) :
    SlowStressSupport.angularWeighted h n (fun j => toRadius (f.flux j))
      (fun j => toRadius (f.axial j)) (fun j => swirlRadius C (f.phi j)) w =
        thetaDensity h C f n w := by
  have hsum : (∑ j ∈ Finset.range (n + 1),
      (w.1 * toRadius (f.flux j) w * partialX (swirlRadius C (f.phi (n-j))) w +
        toRadius (f.flux j) w * swirlRadius C (f.phi (n-j)) w +
        w.1 ^ 2 * toRadius (f.axial j) w *
          SlowStressSupport.axialOp h (SlowStressSupport.orderExponent h (n-j))
            (swirlRadius C (f.phi (n-j))) w)) =
      w.1 ^ 3 / C * convolution
        (transportKernel h (angularExponent h) 1 f.flux f.axial f.phi (radiusPoint w)) n := by
    rw [convolution_eq_positiveAxis]
    unfold PositiveAxisSystem.convolution
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact angular_radius_pair h C hC f j (n-j) hR
      ((hf (n-j) (Nat.sub_le _ _)).differentiableAt (by norm_num))
  unfold SlowStressSupport.angularWeighted
  simp only [show SlowStressSupport.dr = partialX from rfl]
  change w.1 ^ 2 * SlowStressSupport.timeOp h (SlowStressSupport.orderExponent h n)
      (swirlRadius C (f.phi n)) w + _ -
    (w.1 ^ 2 * partialX (partialX (swirlRadius C (f.phi n))) w +
      w.1 * partialX (swirlRadius C (f.phi n)) w - swirlRadius C (f.phi n) w) - _ = _
  rw [hsum, timeOp_swirlRadius h _ C ((hf n le_rfl).differentiableAt (by norm_num)),
    partialXX_swirlRadius C (hf n le_rfl), partialX_swirlRadius C
      ((hf n le_rfl).differentiableAt (by norm_num)),
    axialOp2_swirlRadius h _ C (hf (n-1) (Nat.sub_le _ _)) hL,
    orderExponent_sub_half, orderExponent_sub_half]
  simp only [thetaDensity, angularCoefficient, transportCoefficient, recurrence, transportLinear,
    previous_of_pos _ hn, add_zero]
  simp only [swirlRadius, toRadius, radiusPoint, transportKernel]
  ring

/-- The canonical weighted axial residual uses the same pressure derivative
and preceding viscosity as the finite Cartesian expansion. -/
theorem axialWeighted_eq_zDensity (h : ℝ) (f : SlowProfiles) {n : ℕ} (hn : 0 < n)
    {w : InnerPoint} (hf : ∀ j ≤ n, ContDiffAt ℝ 2 (f.axial j) (radiusPoint w))
    (hp : DifferentiableAt ℝ (f.pressure n) (radiusPoint w))
    (hL : CoordinateAlgebra.L h w.2 ≠ 0) :
    SlowStressSupport.axialWeighted h n (fun j => toRadius (f.flux j))
      (fun j => toRadius (f.axial j)) (toRadius (f.pressure n)) w = zDensity h f n w := by
  have hsum : (∑ j ∈ Finset.range (n+1),
      (toRadius (f.flux j) w * partialX (toRadius (f.axial (n-j))) w +
        w.1 * toRadius (f.axial j) w * SlowStressSupport.axialOp h
          (SlowStressSupport.orderExponent h (n-j)) (toRadius (f.axial (n-j))) w)) =
      w.1 * convolution
        (transportKernel h (axialExponent h) 0 f.flux f.axial f.axial (radiusPoint w)) n := by
    rw [convolution_eq_positiveAxis]
    unfold PositiveAxisSystem.convolution
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact axial_radius_pair h f j (n-j)
      ((hf (n-j) (Nat.sub_le _ _)).differentiableAt (by norm_num))
  unfold SlowStressSupport.axialWeighted
  simp only [show SlowStressSupport.dr = partialX from rfl]
  change w.1 * SlowStressSupport.timeOp h (SlowStressSupport.orderExponent h n)
      (toRadius (f.axial n)) w + _ + _ -
    (w.1 * partialX (partialX (toRadius (f.axial n))) w +
      partialX (toRadius (f.axial n)) w) - _ = _
  rw [hsum, timeOp_toRadius h _ ((hf n le_rfl).differentiableAt (by norm_num)),
    partialXX_toRadius (hf n le_rfl), partialX_toRadius
      ((hf n le_rfl).differentiableAt (by norm_num)), axialOp_toRadius h _ hp,
    axialOp2_toRadius h _ (hf (n-1) (Nat.sub_le _ _)) hL,
    orderExponent_eq_axial, orderExponent_eq_axial]
  simp only [zDensity, axialCoefficient, transportCoefficient, recurrence, transportLinear,
    previous_of_pos _ hn, axialPressureSource]
  simp only [radiusPoint, transportKernel]
  change _ = w.1 * (T h (axialExponent h + slowOrder h n) (f.axial n) (radiusPoint w) -
    2 * (w.1^2 / 2 * partialX (partialX (f.axial n)) (radiusPoint w) +
      1 * partialX (f.axial n) (radiusPoint w)) +
    Z h (pressureExponent h + slowOrder h n) (f.pressure n) (radiusPoint w) + _ - _)
  simp only [radiusPoint, SlowStressSupport.pressureExponent, pressureExponent,
    PositiveAxisSystem.a, CoordinateAlgebra.A]
  ring

theorem radius_divergence (h : ℝ) (f : SlowProfiles) (n : ℕ) {w : InnerPoint}
    (hv : DifferentiableAt ℝ (f.flux n) (radiusPoint w))
    (hu : DifferentiableAt ℝ (f.axial n) (radiusPoint w))
    (hd : divergenceCoefficient h f n (radiusPoint w) = 0) :
    SlowStressSupport.dr (toRadius (f.flux n)) w =
      -w.1 * SlowStressSupport.axialOp h (SlowStressSupport.orderExponent h n)
        (toRadius (f.axial n)) w := by
  change partialX (toRadius (f.flux n)) w = _
  rw [partialX_toRadius hv, axialOp_toRadius h _ hu, orderExponent_eq_axial,
    (divergenceCoefficient_eq_zero_iff h f n (radiusPoint w)).mp hd]
  ring

theorem partialX_toRadius_zero {f : InnerProfile} {eta : ℝ}
    (hf : DifferentiableAt ℝ (toRadius f) (0, eta)) : partialX (toRadius f) (0, eta) = 0 := by
  have he : Function.Even (fun R => toRadius f (R, eta)) := by
    intro R
    simp [toRadius, radiusPoint]
  exact (LeadingStress.partialX_hasDerivAt hf).deriv.symm.trans
    (EvenSmoothDescent.deriv_zero_of_even he)

/-- The primitive source is the canonical conservative density, including
the axis. At the axis the equality uses the actual radial parity. -/
theorem thetaDensity_eq_angularDensity {S : Set ℝ} (hS : IsOpen S)
    (h C : ℝ) (hC : C ≠ 0) (f : SlowProfiles) {n : ℕ} (hn : 0 < n)
    (hv : ∀ j ≤ n, SlowStressSupport.Smooth S (toRadius (f.flux j)))
    (hu : ∀ j ≤ n, SlowStressSupport.Smooth S (toRadius (f.axial j)))
    (he : ∀ j ≤ n, SlowStressSupport.Smooth S (swirlRadius C (f.phi j)))
    (hf : ∀ w : InnerPoint, w.2 ∈ S → w.1 ≠ 0 → ∀ j ≤ n,
      ContDiffAt ℝ 2 (f.phi j) (radiusPoint w))
    (hL : ∀ eta ∈ S, CoordinateAlgebra.L h eta ≠ 0)
    (hdiv : ∀ w : InnerPoint, w.2 ∈ S → ∀ j ≤ n,
      SlowStressSupport.dr (toRadius (f.flux j)) w =
        -w.1 * SlowStressSupport.axialOp h (SlowStressSupport.orderExponent h j)
          (toRadius (f.axial j)) w) :
    EqOn (thetaDensity h C f n)
      (SlowStressSupport.angularDensity h n (fun j => toRadius (f.flux j))
        (fun j => toRadius (f.axial j)) (fun j => swirlRadius C (f.phi j)))
      (SlowStressSupport.region S) := by
  intro w hw
  rw [← SlowStressSupport.angularWeighted_eq_density hS hv hu he h hw.2 (hdiv w hw.2)]
  by_cases hR : w.1 = 0
  · simp [thetaDensity, SlowStressSupport.angularWeighted, swirlRadius, hR]
  · exact (angularWeighted_eq_thetaDensity h C hC f hn hR (hf w hw.2 hR) (hL w.2 hw.2)).symm

theorem zDensity_eq_axialDensity {S : Set ℝ} (hS : IsOpen S)
    (h : ℝ) (f : SlowProfiles) {n : ℕ} (hn : 0 < n)
    (hv : ∀ j ≤ n, SlowStressSupport.Smooth S (toRadius (f.flux j)))
    (hu : ∀ j ≤ n, SlowStressSupport.Smooth S (toRadius (f.axial j)))
    (hp : SlowStressSupport.Smooth S (toRadius (f.pressure n)))
    (hf : ∀ w : InnerPoint, w.2 ∈ S → w.1 ≠ 0 → ∀ j ≤ n,
      ContDiffAt ℝ 2 (f.axial j) (radiusPoint w))
    (hp' : ∀ w : InnerPoint, w.2 ∈ S → w.1 ≠ 0 →
      DifferentiableAt ℝ (f.pressure n) (radiusPoint w))
    (hL : ∀ eta ∈ S, CoordinateAlgebra.L h eta ≠ 0)
    (hdiv : ∀ w : InnerPoint, w.2 ∈ S → ∀ j ≤ n,
      SlowStressSupport.dr (toRadius (f.flux j)) w =
        -w.1 * SlowStressSupport.axialOp h (SlowStressSupport.orderExponent h j)
          (toRadius (f.axial j)) w) :
    EqOn (zDensity h f n)
      (SlowStressSupport.axialDensity h n (fun j => toRadius (f.flux j))
        (fun j => toRadius (f.axial j)) (toRadius (f.pressure n)))
      (SlowStressSupport.region S) := by
  intro w hw
  rw [← SlowStressSupport.axialWeighted_eq_density hS hv hu hp h hw.2 (hdiv w hw.2)]
  by_cases hR : w.1 = 0
  · have hdz : ∀ j ≤ n, SlowStressSupport.dr (toRadius (f.axial j)) w = 0 := by
      intro j hj
      have hw' : w = (0, w.2) := by ext <;> simp [hR]
      rw [hw']
      exact partialX_toRadius_zero (((hu j hj).contDiffAt (x := (0, w.2))
        ((isOpen_univ.prod hS).mem_nhds ⟨mem_univ _, hw.2⟩)).differentiableAt (by simp))
    simp only [zDensity, hR, zero_mul, SlowStressSupport.axialWeighted, add_zero, zero_add,
        sub_zero, hdz n le_rfl]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [hdz (n-j) (Nat.sub_le _ _), mul_zero]
  · exact (axialWeighted_eq_zDensity h f hn (hf w hw.2 hR) (hp' w hw.2 hR) (hL w.2 hw.2)).symm

theorem primitive_stress_congr_slice (m : ℕ) {F G : InnerProfile} {R eta : ℝ}
    (hFG : ∀ r : ℝ, F (r, eta) = G (r, eta)) :
    SlowStressSupport.stress m F (R, eta) = SlowStressSupport.stress m G (R, eta) := by
  have hp : ProfileHistories.primitive F (R, eta) = ProfileHistories.primitive G (R, eta) :=
    intervalIntegral.integral_congr (fun r _ => hFG r)
  simp only [SlowStressSupport.stress, hp]

/-- Equality of the actual negative integrals, not just their derivatives. -/
theorem thetaStress_eq_canonical {S : Set ℝ} (h C : ℝ) (f : SlowProfiles) (n : ℕ)
    (hEq : EqOn (thetaDensity h C f n)
      (SlowStressSupport.angularDensity h n (fun j => toRadius (f.flux j))
        (fun j => toRadius (f.axial j)) (fun j => swirlRadius C (f.phi j)))
      (SlowStressSupport.region S)) {w : InnerPoint} (hw : w.2 ∈ S) :
    thetaStress h C f n w = fromRadius
      (SlowStressSupport.angularStress h n (fun j => toRadius (f.flux j))
        (fun j => toRadius (f.axial j)) (fun j => swirlRadius C (f.phi j))) w :=
  primitive_stress_congr_slice 2 (fun r => hEq ⟨mem_univ r, hw⟩)

theorem zStress_eq_canonical {S : Set ℝ} (h : ℝ) (f : SlowProfiles) (n : ℕ)
    (hEq : EqOn (zDensity h f n)
      (SlowStressSupport.axialDensity h n (fun j => toRadius (f.flux j))
        (fun j => toRadius (f.axial j)) (toRadius (f.pressure n)))
      (SlowStressSupport.region S)) {w : InnerPoint} (hw : w.2 ∈ S) :
    zStress h f n w = fromRadius
      (SlowStressSupport.axialStress h n (fun j => toRadius (f.flux j))
        (fun j => toRadius (f.axial j)) (toRadius (f.pressure n))) w :=
  primitive_stress_congr_slice 1 (fun r => hEq ⟨mem_univ r, hw⟩)

theorem inner_smoothAt_of_radial {S : Set ℝ} (hS : IsOpen S) {F E : InnerProfile}
    (hF : SlowStressSupport.Smooth S F)
    (hFE : ∀ R : ℝ, 0 < R → ∀ eta ∈ S, F (R, eta) = E (R ^ 2 / 2, eta))
    {w : InnerPoint} (hX : 0 < w.1) (heta : w.2 ∈ S) : ContDiffAt ℝ ∞ E w := by
  have hs := fromRadius_smoothAt hX ((hF.contDiffAt
    ((isOpen_univ.prod hS).mem_nhds (show (Real.sqrt (2 * w.1), w.2) ∈ SlowStressSupport.region S
        from
      ⟨mem_univ _, heta⟩))))
  apply hs.congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioi.prod hS).mem_nhds ⟨hX, heta⟩] with y hy
  have hyX : 0 < y.1 := hy.1
  have hyR : 0 < Real.sqrt (2 * y.1) := Real.sqrt_pos.2 (by positivity)
  have hr2 := Real.sq_sqrt (show 0 ≤ 2 * y.1 by positivity)
  have hval := hFE (Real.sqrt (2 * y.1)) hyR y.2 hy.2
  have hpoint : (Real.sqrt (2 * y.1) ^ 2 / 2, y.2) = y := by
    rw [hr2]
    ext <;> simp
  rw [hpoint] at hval
  exact hval.symm

theorem axialOp2_congr_germ (h b : ℝ) {f g : InnerProfile} {w : InnerPoint}
    (hfg : f =ᶠ[𝓝 w] g) :
    SlowStressSupport.axialOp2 h b f w = SlowStressSupport.axialOp2 h b g w := by
  have he : SlowStressSupport.axialOp h b f =ᶠ[𝓝 w] SlowStressSupport.axialOp h b g := by
    filter_upwards [hfg.eventuallyEq_nhds] with y hy
    exact axialOp_congr_germ h b hy
  exact axialOp_congr_germ h (b - PositiveAxisSystem.dScale h) he

theorem axialOp2_radial_eq_Z2 {S : Set ℝ} (hS : IsOpen S) (h b : ℝ)
    {F E : InnerProfile} (hF : SlowStressSupport.Smooth S F)
    (hFE : ∀ R : ℝ, 0 < R → ∀ eta ∈ S, F (R, eta) = E (R ^ 2 / 2, eta))
    {w : InnerPoint} (hR : 0 < w.1) (heta : w.2 ∈ S) (hL : CoordinateAlgebra.L h w.2 ≠ 0) :
    SlowStressSupport.axialOp2 h b F w = Z2 h b E (radiusPoint w) := by
  have he : F =ᶠ[𝓝 w] toRadius E := by
    filter_upwards [(isOpen_Ioi.prod hS).mem_nhds ⟨hR, heta⟩] with y hy
    exact hFE y.1 hy.1 y.2 hy.2
  rw [axialOp2_congr_germ h b he]
  exact axialOp2_toRadius h b
    ((inner_smoothAt_of_radial hS hF hFE (w := radiusPoint w)
      (by dsimp [radiusPoint]; positivity) heta).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hL

theorem deriv_deriv_pullback_z {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : InnerProfile} {p : PhysicalPoint} (hp : p.1 < 1)
    (hf : ContDiffAt ℝ 2 f (SimilarityProfile.inner h p)) :
    deriv (deriv (fun z => pullback h b f (p.1, (p.2.1, z)))) p.2.2 =
      pullback h (b - 2 * CoordinateAlgebra.D h) (Z2 h b f) p := by
  have hc : ContinuousAt (fun z : ℝ => (p.1, (p.2.1, z))) p.2.2 :=
    continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)
  have he : deriv (fun z => pullback h b f (p.1, (p.2.1, z))) =ᶠ[𝓝 p.2.2]
      (fun z => pullback h (b - CoordinateAlgebra.D h) (Z h b f) (p.1, (p.2.1, z))) := by
    have hlocal := hc.eventually (SimilarityProfile.eventually_C2_inner hh hh1 hp hf)
    filter_upwards [hlocal] with z hz
    exact (SimilarityProfile.hasDerivAt_pullback_z hh hh1
      (p := (p.1, (p.2.1, z))) hp (hz.differentiableAt (by norm_num))).deriv
  rw [he.deriv_eq]
  have hd := (SimilarityProfile.hasDerivAt_pullback_z hh hh1 hp
    ((SimilarityProfile.Z_smoothAt (b := b) hf (SimilarityProfile.L_pos hh hh1
        hp).ne').differentiableAt (by
        norm_num))
    (b := b - CoordinateAlgebra.D h)).deriv
  rw [show b - CoordinateAlgebra.D h - CoordinateAlgebra.D h =
    b - 2 * CoordinateAlgebra.D h by ring] at hd
  exact hd

/-- At the normalized physical point q=1, the literal second axial
derivative is exactly the canonical R-coordinate operator. -/
theorem normalized_axial_viscosity {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {F E : InnerProfile} (hF : SlowStressSupport.Smooth (Ioo (-1) 1) F)
    (hFE : ∀ R : ℝ, 0 < R → ∀ eta ∈ Ioo (-1 : ℝ) 1, F (R, eta) = E (R ^ 2 / 2, eta))
    {eta R : ℝ} (heta : eta ∈ Ioo (-1 : ℝ) 1) (hR : 0 < R) :
    deriv (deriv (RenormalizedHeatMoment.uTheta h E (eta ^ 2) R)) eta =
      SlowStressSupport.axialOp2 h (-CoordinateAlgebra.A h) F (R, eta) := by
  obtain ⟨ht, hq, he⟩ := RenormalizedHeatMoment.normalized_coordinates hh hh1 heta
  let p : PhysicalPoint := (eta ^ 2, (R ^ 2 / 2, eta))
  have hqp : SimilarityProfile.q h p = 1 := hq
  have hep : SimilarityProfile.eta h p = eta := he
  have hip : SimilarityProfile.inner h p = radiusPoint (R, eta) := by
    ext <;> simp [SimilarityProfile.inner, SimilarityProfile.X, hqp, hep, radiusPoint, p]
  have hL : CoordinateAlgebra.L h eta ≠ 0 := by
    have hl := (SimilarityProfile.L_pos hh hh1 (p := p) ht).ne'
    rwa [hep] at hl
  have hE := inner_smoothAt_of_radial isOpen_Ioo hF hFE
    (w := radiusPoint (R, eta)) (by dsimp [radiusPoint]; positivity) heta
  have hE2 : ContDiffAt ℝ 2 E (SimilarityProfile.inner h p) := by
    rw [hip]
    exact hE.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [axialOp2_radial_eq_Z2 isOpen_Ioo h (-CoordinateAlgebra.A h) hF hFE hR heta hL]
  have hfun : RenormalizedHeatMoment.uTheta h E (eta ^ 2) R =
      fun z => pullback h (-CoordinateAlgebra.A h) E (p.1, (p.2.1, z)) :=
    funext (RenormalizedHeatMoment.uTheta_eq_similarity_pullback h E (eta ^ 2) R)
  rw [hfun, deriv_deriv_pullback_z hh hh1 (p := p) ht hE2]
  simp only [pullback, hqp, hip, Real.one_rpow, one_mul]

/-- The order-one angular viscosity moment follows from the restored
renormalized heat moment. Only the stated exterior support is used to
replace the positive half-line integral by its finite radial integral. -/
theorem lowerAngularViscosityMoment_of_renormalized {h C T B : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hT : 0 < T) (hB : 0 ≤ B)
    {F E : InnerProfile} (hF : SlowStressSupport.Smooth (Ioo (-1) 1) F)
    (hFE : ∀ R : ℝ, 0 < R → ∀ eta ∈ Ioo (-1 : ℝ) 1, F (R, eta) = E (R ^ 2 / 2, eta))
    (he : ∀ eta ∈ Ioo (-1 : ℝ) 1, ∀ X : ℝ, T ≤ X →
      E (X, eta) = C * X ^ (-RenormalizedHeatMoment.A h) *
        RadialHeatProfile.profile (1 + h) (2 * (1 - eta ^ 2) / X))
    (hm : ∀ eta ∈ Ioo (-1 : ℝ) 1, RenormalizedHeatMoment.xMoment h C E eta = 0)
    (hExt : SlowStressSupport.exterior B (Ioo (-1) 1)
      (SlowStressSupport.axialOp2 h (SlowStressSupport.orderExponent h 0) F)) :
    SlowStressSupport.LowerAngularViscosityMoment (Ioo (-1) 1) B h F := by
  intro eta heta
  obtain ⟨ht, _, _⟩ := RenormalizedHeatMoment.normalized_coordinates hh hh1 heta
  have hz := RenormalizedHeatMoment.uTheta_axial_viscosity_integral hh hh1 ht hT hF hFE he hm eta
  rw [SlowStressSupport.moment_eq_positive hB hExt heta 2]
  change (∫ R in Ioi (0 : ℝ), R ^ 2 *
    SlowStressSupport.axialOp2 h (SlowStressSupport.orderExponent h 0) F (R, eta)) = 0
  calc
    _ = ∫ R in Ioi (0 : ℝ), R ^ 2 *
        deriv (deriv (RenormalizedHeatMoment.uTheta h E (eta ^ 2) R)) eta := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro R hR
      dsimp only
      rw [normalized_axial_viscosity hh hh1 hF hFE heta hR]
      simp only [SlowStressSupport.orderExponent, slowOrder_zero, add_zero]
      rfl
    _ = 0 := hz

theorem hierarchy_profile_smoothAt {R : ℝ} {U : Set ℂ} {h C : ℝ}
    {base : Fin 5 → InnerProfile} (A : SlowRecursion.LocalHierarchy R U h C base)
    (hR : 0 < R) (hU : IsOpen U) (n : ℕ) (i : Fin 5)
    {w : InnerPoint} (hX : w.1 ∈ Ioo (0 : ℝ) (R ^ 2)) (heta : (w.2 : ℂ) ∈ U) :
    ContDiffAt ℝ ∞ (SlowRecursion.profile (A.coefficients n i)) w := by
  have hsub : Ioo (0 : ℝ) (R ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U ⊆
      Ico (0 : ℝ) (R ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U :=
    fun _ hw => ⟨⟨hw.1.1.le, hw.1.2⟩, hw.2⟩
  exact ((A.profiles_smooth hR hU n i).mono hsub).contDiffAt
    ((isOpen_Ioo.prod (PositiveAxisExistence.realParameterDomain_isOpen hU)).mem_nhds ⟨hX, heta⟩)

theorem hierarchy_pressure_coefficient {R : ℝ} {U : Set ℂ} {h C : ℝ}
    {base : Fin 5 → InnerProfile} (A : SlowRecursion.LocalHierarchy R U h C base)
    (hR : 0 < R) (hU : IsOpen U) {n : ℕ} (hn : 0 < n)
    {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) (heta : (eta : ℂ) ∈ U)
    (hL : CoordinateAlgebra.L h eta ≠ 0) :
    pressureCoefficient h C (hierarchyProfiles A) n (X, eta) = 0 := by
  exact positiveOrder_pressure_coefficient h C _ _ _ _ _ n hX.1.ne' hL
    (fun j _ => (hierarchy_profile_smoothAt A hR hU j 4 hX heta).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (A.equations n hn X hX eta heta)

/-- A repaired family that retains the finite input germs retains the
actual solved angular and axial equations in the inner region. -/
theorem repaired_tangential_coefficients {R : ℝ} {U : Set ℂ} {h C : ℝ}
    {base : Fin 5 → InnerProfile} (A : SlowRecursion.LocalHierarchy R U h C base)
    (f : SlowProfiles) {n : ℕ} (hn : 0 < n) {X eta : ℝ}
    (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) (heta : (eta : ℂ) ∈ U)
    (hv : ∀ j ≤ n, f.flux j =ᶠ[𝓝 (X, eta)] (hierarchyProfiles A).flux j)
    (hu : ∀ j ≤ n, f.axial j =ᶠ[𝓝 (X, eta)] (hierarchyProfiles A).axial j)
    (hphi : ∀ j ≤ n, f.phi j =ᶠ[𝓝 (X, eta)] (hierarchyProfiles A).phi j)
    (hp : f.pressure n =ᶠ[𝓝 (X, eta)] (hierarchyProfiles A).pressure n) :
    angularCoefficient h f n (X, eta) = 0 ∧ axialCoefficient h f n (X, eta) = 0 := by
  rw [angularCoefficient_congr_germ h n hv hu hphi, axialCoefficient_congr_germ h n hv hu hp]
  exact hierarchy_tangential_coefficients A hn hX heta

end NavierStokes.SlowResidualMatching
