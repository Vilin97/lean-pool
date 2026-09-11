/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowBorelBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.DiagonalResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActiveAnnulusWeight
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowFirstOrderEdge
import LeanPool.NavierStokesAndEuler.NavierStokes.BlowupImplication
import LeanPool.NavierStokesAndEuler.NavierStokes.NaturalCore
import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricModulation
import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualRegularity
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Prod
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowResidualMatching

/-!
# Residual and axis values of the asymptotically summed slow base

The series used here is the actual locally finite series in `SlowBorelBase`.
The radial streams are summed before taking their Cartesian curl.
-/

section

/-!
# Regular finite tail coefficients at the symmetry axis

The radial flux is `V_n = X * beta_n`.  This module uses that identity in the
actual finite tails.  The resulting coefficient functions contain no division
by `X`; their finite indices and powers of `q` are unchanged.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped BigOperators Topology ContDiff

namespace NavierStokes.AxisTailRegularity

open SimilarityProfile (InnerPoint InnerProfile PhysicalPoint partialX Z)
open SlowExpansionResidual
open SlowResidualMatching

/-- The transport kernel after canceling the radial flux factor. -/
noncomputable def regularTransportKernel (h e α : ℝ)
    (beta u f : ℕ → InnerProfile) (w : InnerPoint) (i j : ℕ) : ℝ :=
  beta i w * (w.1 * partialX (f j) w + α * f j w) +
    u i w * Z h (e + slowOrder h j) (f j) w

/-- The radial transport kernel divided by its factor `X`. -/
noncomputable def regularRadialKernel (h : ℝ)
    (beta u : ℕ → InnerProfile) (w : InnerPoint) (i j : ℕ) : ℝ :=
  beta i w * (beta j w / 2 + w.1 * partialX (beta j) w) +
    u i w * Z h (slowOrder h j - 1) (beta j) w

/-- Same omitted pairs and final viscosity term as the original transport tail. -/
noncomputable def regularTransportTerm (N : ℕ) (h e α : ℝ)
    (beta u f : ℕ → InnerProfile) : TailIndex → InnerProfile
  | none => fun w => -Z2 h (e + slowOrder h N) (f N) w
  | some ij => fun w => regularTransportKernel h e α beta u f w ij.1 ij.2

/-- Each original radial pressure coefficient divided by `2X`, with the
factor canceled before evaluation.  In particular this defines its smooth
extension at `X = 0`, rather than using total division there. -/
noncomputable def regularPressureTerm (N : ℕ) (h C : ℝ)
    (phi u beta : ℕ → InnerProfile) : PressureIndex → InnerProfile
  | Sum.inl none => fun w => -Z2 h (slowOrder h N - 1) (beta N) w / 2
  | Sum.inl (some ij) => fun w => regularRadialKernel h beta u w ij.1 ij.2 / 2
  | Sum.inr none => fun w => AxisSourceRegularity.omegaDivX h u beta N w / 2
  | Sum.inr (some ij) => fun w => -(C⁻¹ ^ 2) * (phi ij.1 w * phi ij.2 w)

theorem tail_pair_indices {N : ℕ} {ij : ℕ × ℕ}
    (hij : some ij ∈ transportIndices N) : ij.1 ≤ N ∧ ij.2 ≤ N := by
  have hp := ((mem_transportIndices_some N ij).mp hij).1
  exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hp).1),
    Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hp).2)⟩

theorem transportKernel_axisFactor (h e α : ℝ) (beta u f : ℕ → InnerProfile)
    (i j : ℕ) {w : InnerPoint} (hX : w.1 ≠ 0) :
    transportKernel h e α (fun n => AxisSourceRegularity.axisFactor (beta n)) u f w i j =
      regularTransportKernel h e α beta u f w i j := by
  simp only [transportKernel, transportPair, AxisSourceRegularity.axisFactor,
    regularTransportKernel]
  field_simp

/-- Radial transport is genuinely divisible by `X`, including at the axis. -/
theorem radialKernel_axisFactor (h : ℝ) (beta u : ℕ → InnerProfile)
    (i j : ℕ) {w : InnerPoint} (hb : DifferentiableAt ℝ (beta j) w) :
    transportKernel h 0 (-(1 / 2))
      (fun n => AxisSourceRegularity.axisFactor (beta n)) u
      (fun n => AxisSourceRegularity.axisFactor (beta n)) w i j =
      w.1 * regularRadialKernel h beta u w i j := by
  simp only [transportKernel, transportPair, zero_add]
  have hhalf : (-(1 / 2) : ℝ) * AxisSourceRegularity.axisFactor (beta j) w / w.1 =
      -(AxisSourceRegularity.axisFactor (beta j) w / (2 * w.1)) := by ring
  rw [hhalf, ← sub_eq_add_neg, AxisSourceRegularity.radial_advection_axisFactor hb,
    AxisSourceRegularity.Z_axisFactor h (slowOrder h j) hb]
  unfold regularRadialKernel
  ring

theorem transportTerm_axisFactor (N : ℕ) (h e α : ℝ)
    (beta u f : ℕ → InnerProfile) (i : TailIndex) {w : InnerPoint} (hX : w.1 ≠ 0) :
    transportTerm N h e α (fun n => AxisSourceRegularity.axisFactor (beta n)) u f i w =
      regularTransportTerm N h e α beta u f i w := by
  cases i with
  | none => rfl
  | some ij => exact transportKernel_axisFactor h e α beta u f ij.1 ij.2 hX

/-- All radial pressure branches have the factor `2X` before division. -/
theorem pressureTerm_axisFactor (N : ℕ) (h C : ℝ)
    (phi u beta pressure : ℕ → InnerProfile) {w : InnerPoint}
    (hb : ∀ j ≤ N, ContDiffAt ℝ 2 (beta j) w)
    (hL : CoordinateAlgebra.L h w.2 ≠ 0)
    {i : PressureIndex} (hi : i ∈ pressureIndices N) :
    pressureTerm N h C (ofBeta phi u beta pressure) i w =
      2 * w.1 * regularPressureTerm N h C phi u beta i w := by
  cases i with
  | inl i =>
    have hi' : i ∈ transportIndices N := by simpa [pressureIndices] using hi
    cases i with
    | none =>
      change -Z2 h (0 + slowOrder h N) (AxisSourceRegularity.axisFactor (beta N)) w = _
      rw [zero_add]
      rw [show Z2 h (slowOrder h N) (AxisSourceRegularity.axisFactor (beta N)) w =
        w.1 * Z2 h (slowOrder h N - 1) (beta N) w from
          AxisSourceRegularity.Z2_axisFactor h (slowOrder h N) (hb N le_rfl) hL]
      simp only [regularPressureTerm]
      ring
    | some ij =>
      have hj := (tail_pair_indices hi').2
      change transportKernel h 0 (-(1 / 2))
        (fun n => AxisSourceRegularity.axisFactor (beta n)) u
        (fun n => AxisSourceRegularity.axisFactor (beta n)) w ij.1 ij.2 = _
      rw [radialKernel_axisFactor h beta u ij.1 ij.2 ((hb ij.2 hj).differentiableAt (by norm_num))]
      simp only [regularPressureTerm]
      ring
  | inr i =>
    cases i with
    | none =>
      change omegaCoefficient h (ofBeta phi u beta pressure) N w = _
      rw [omegaCoefficient_eq_omega]
      change AxisSourceRegularity.omega h u (fun n => AxisSourceRegularity.axisFactor (beta n)) N w
          = _
      rw [AxisSourceRegularity.omega_axisFactor h u beta N w hb hL]
      simp only [regularPressureTerm]
      ring
    | some ij =>
      simp only [pressureTerm, ofBeta, regularPressureTerm]
      ring

theorem pressureTerm_div_axisFactor (N : ℕ) (h C : ℝ)
    (phi u beta pressure : ℕ → InnerProfile) {w : InnerPoint}
    (hb : ∀ j ≤ N, ContDiffAt ℝ 2 (beta j) w)
    (hL : CoordinateAlgebra.L h w.2 ≠ 0) (hX : w.1 ≠ 0)
    {i : PressureIndex} (hi : i ∈ pressureIndices N) :
    pressureTerm N h C (ofBeta phi u beta pressure) i w / (2 * w.1) =
      regularPressureTerm N h C phi u beta i w := by
  rw [pressureTerm_axisFactor N h C phi u beta pressure hb hL hi]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num) hX)

theorem regularTransportKernel_smoothAt (h e α : ℝ)
    (beta u f : ℕ → InnerProfile) (i j : ℕ) {w : InnerPoint}
    (hb : ContDiffAt ℝ ∞ (beta i) w) (hu : ContDiffAt ℝ ∞ (u i) w)
    (hf : ContDiffAt ℝ ∞ (f j) w) (hL : CoordinateAlgebra.L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => regularTransportKernel h e α beta u f y i j) w := by
  exact (hb.mul ((contDiffAt_fst.mul (AxisSourceRegularity.partialX_smooth hf)).add
    (contDiffAt_const.mul hf))).add
      (hu.mul (AxisSourceRegularity.Z_smooth h (e + slowOrder h j) hf hL))

theorem regularRadialKernel_smoothAt (h : ℝ)
    (beta u : ℕ → InnerProfile) (i j : ℕ) {w : InnerPoint}
    (hbi : ContDiffAt ℝ ∞ (beta i) w) (hbj : ContDiffAt ℝ ∞ (beta j) w)
    (hu : ContDiffAt ℝ ∞ (u i) w) (hL : CoordinateAlgebra.L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => regularRadialKernel h beta u y i j) w := by
  exact (hbi.mul ((hbj.div contDiffAt_const (by norm_num)).add
    (contDiffAt_fst.mul (AxisSourceRegularity.partialX_smooth hbj)))).add
      (hu.mul (AxisSourceRegularity.Z_smooth h (slowOrder h j - 1) hbj hL))

theorem regularTransportTerm_smoothOn {O : Set InnerPoint} (hO : IsOpen O)
    (N : ℕ) (h e α : ℝ) (beta u f : ℕ → InnerProfile)
    (hb : ∀ j ≤ N, ContDiffOn ℝ ∞ (beta j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hf : ∀ j ≤ N, ContDiffOn ℝ ∞ (f j) O)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0)
    {i : TailIndex} (hi : i ∈ transportIndices N) :
    ContDiffOn ℝ ∞ (regularTransportTerm N h e α beta u f i) O := by
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  cases i with
  | none =>
    exact (AxisSourceRegularity.Z2_smooth h (e + slowOrder h N)
      ((hf N le_rfl).contDiffAt (hO.mem_nhds hw)) (hL w hw)).neg
  | some ij =>
    obtain ⟨hiN, hjN⟩ := tail_pair_indices hi
    exact regularTransportKernel_smoothAt h e α beta u f ij.1 ij.2
      ((hb ij.1 hiN).contDiffAt (hO.mem_nhds hw))
      ((hu ij.1 hiN).contDiffAt (hO.mem_nhds hw))
      ((hf ij.2 hjN).contDiffAt (hO.mem_nhds hw)) (hL w hw)

theorem regularPressureTerm_smoothOn {O : Set InnerPoint} (hO : IsOpen O)
    (N : ℕ) (h C : ℝ) (phi u beta : ℕ → InnerProfile)
    (hp : ∀ j ≤ N, ContDiffOn ℝ ∞ (phi j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hb : ∀ j ≤ N, ContDiffOn ℝ ∞ (beta j) O)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0)
    {i : PressureIndex} (hi : i ∈ pressureIndices N) :
    ContDiffOn ℝ ∞ (regularPressureTerm N h C phi u beta i) O := by
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  have hba : ∀ j ≤ N, ContDiffAt ℝ ∞ (beta j) w :=
    fun j hj => (hb j hj).contDiffAt (hO.mem_nhds hw)
  have hua : ∀ j ≤ N, ContDiffAt ℝ ∞ (u j) w :=
    fun j hj => (hu j hj).contDiffAt (hO.mem_nhds hw)
  cases i with
  | inl i =>
    have hi' : i ∈ transportIndices N := by simpa [pressureIndices] using hi
    cases i with
    | none =>
      exact (AxisSourceRegularity.Z2_smooth h (slowOrder h N - 1)
        (hba N le_rfl) (hL w hw)).neg.div contDiffAt_const (by norm_num)
    | some ij =>
      obtain ⟨hiN, hjN⟩ := tail_pair_indices hi'
      exact (regularRadialKernel_smoothAt h beta u ij.1 ij.2 (hba ij.1 hiN)
        (hba ij.2 hjN) (hua ij.1 hiN) (hL w hw)).div contDiffAt_const (by norm_num)
  | inr i =>
    have hi' : i ∈ transportIndices N := by simpa [pressureIndices] using hi
    cases i with
    | none =>
      exact (AxisSourceRegularity.omegaDivX_smooth h u beta N w hua hba (hL w hw)).div
        contDiffAt_const (by norm_num)
    | some ij =>
      obtain ⟨hiN, hjN⟩ := tail_pair_indices hi'
      exact contDiffAt_const.mul (((hp ij.1 hiN).contDiffAt (hO.mem_nhds hw)).mul
        ((hp ij.2 hjN).contDiffAt (hO.mem_nhds hw)))

/-! ## Local identification with the actual coefficient functions -/

theorem transportKernel_congr_germ (h e α : ℝ)
    {v u f v' u' f' : ℕ → InnerProfile} (i j : ℕ) {w : InnerPoint}
    (hv : v i =ᶠ[𝓝 w] v' i) (hu : u i =ᶠ[𝓝 w] u' i)
    (hf : f j =ᶠ[𝓝 w] f' j) :
    transportKernel h e α v u f w i j = transportKernel h e α v' u' f' w i j := by
  simp only [transportKernel, transportPair, hv.eq_of_nhds, hu.eq_of_nhds,
    hf.eq_of_nhds, (partialX_congr_germ hf).eq_of_nhds,
    (Z_congr_germ h (e + slowOrder h j) hf).eq_of_nhds]

theorem transportTerm_congr_germ (N : ℕ) (h e α : ℝ)
    {v u f v' u' f' : ℕ → InnerProfile} {w : InnerPoint}
    (hv : ∀ j ≤ N, v j =ᶠ[𝓝 w] v' j)
    (hu : ∀ j ≤ N, u j =ᶠ[𝓝 w] u' j)
    (hf : ∀ j ≤ N, f j =ᶠ[𝓝 w] f' j)
    {i : TailIndex} (hi : i ∈ transportIndices N) :
    transportTerm N h e α v u f i w = transportTerm N h e α v' u' f' i w := by
  cases i with
  | none => exact congrArg Neg.neg (Z2_congr_germ h (e + slowOrder h N) (hf N le_rfl))
  | some ij =>
    obtain ⟨hiN, hjN⟩ := tail_pair_indices hi
    exact transportKernel_congr_germ h e α ij.1 ij.2
      (hv ij.1 hiN) (hu ij.1 hiN) (hf ij.2 hjN)

theorem pressureTerm_congr_germ (N : ℕ) (h C : ℝ)
    {f g : SlowProfiles} {w : InnerPoint}
    (hv : ∀ j ≤ N, f.flux j =ᶠ[𝓝 w] g.flux j)
    (hu : ∀ j ≤ N, f.axial j =ᶠ[𝓝 w] g.axial j)
    (hp : ∀ j ≤ N, f.phi j =ᶠ[𝓝 w] g.phi j)
    {i : PressureIndex} (hi : i ∈ pressureIndices N) :
    pressureTerm N h C f i w = pressureTerm N h C g i w := by
  cases i with
  | inl i =>
    have hi' : i ∈ transportIndices N := by simpa [pressureIndices] using hi
    exact transportTerm_congr_germ N h 0 (-(1 / 2)) hv hu hv hi'
  | inr i =>
    have hi' : i ∈ transportIndices N := by simpa [pressureIndices] using hi
    cases i with
    | none => exact omegaCoefficient_congr_germ h N hv hu
    | some ij =>
      obtain ⟨hiN, hjN⟩ := tail_pair_indices hi'
      simp only [pressureTerm, (hp ij.1 hiN).eq_of_nhds, (hp ij.2 hjN).eq_of_nhds]

/-- Only agreement of the local coefficient germs is required.  Global
extensions may have different values for negative `X`. -/
theorem transportTerm_eq_regular_of_germs (N : ℕ) (h e α : ℝ)
    {v u f beta u' f' : ℕ → InnerProfile} {w : InnerPoint}
    (hv : ∀ j ≤ N, v j =ᶠ[𝓝 w] AxisSourceRegularity.axisFactor (beta j))
    (hu : ∀ j ≤ N, u j =ᶠ[𝓝 w] u' j)
    (hf : ∀ j ≤ N, f j =ᶠ[𝓝 w] f' j)
    (hX : w.1 ≠ 0) {i : TailIndex} (hi : i ∈ transportIndices N) :
    transportTerm N h e α v u f i w = regularTransportTerm N h e α beta u' f' i w := by
  rw [transportTerm_congr_germ N h e α hv hu hf hi]
  exact transportTerm_axisFactor N h e α beta u' f' i hX

theorem pressureTerm_eq_regular_of_germs (N : ℕ) (h C : ℝ)
    {f : SlowProfiles} {phi u beta : ℕ → InnerProfile} {w : InnerPoint}
    (hv : ∀ j ≤ N, f.flux j =ᶠ[𝓝 w] AxisSourceRegularity.axisFactor (beta j))
    (hu : ∀ j ≤ N, f.axial j =ᶠ[𝓝 w] u j)
    (hp : ∀ j ≤ N, f.phi j =ᶠ[𝓝 w] phi j)
    (hb : ∀ j ≤ N, ContDiffAt ℝ 2 (beta j) w)
    (hL : CoordinateAlgebra.L h w.2 ≠ 0) (hX : w.1 ≠ 0)
    {i : PressureIndex} (hi : i ∈ pressureIndices N) :
    pressureTerm N h C f i w / (2 * w.1) = regularPressureTerm N h C phi u beta i w := by
  have he : pressureTerm N h C f i w =
      pressureTerm N h C (ofBeta phi u beta f.pressure) i w :=
    pressureTerm_congr_germ N h C hv hu hp hi
  rw [he]
  exact pressureTerm_div_axisFactor N h C phi u beta f.pressure hb hL hX hi

/-- Equality on the nonnegative part of an open set gives the needed germ
at every positive radial coordinate.  No negative-coordinate matching is used. -/
theorem germ_of_nonnegative_eqOn {O : Set InnerPoint} (hO : IsOpen O)
    {f g : InnerProfile} (hfg : ∀ w ∈ O, 0 ≤ w.1 → f w = g w)
    {w : InnerPoint} (hw : w ∈ O) (hX : 0 < w.1) : f =ᶠ[𝓝 w] g := by
  have hx : ∀ᶠ y : InnerPoint in 𝓝 w, 0 < y.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hX
  filter_upwards [hO.mem_nhds hw, hx] with y hy hyX
  exact hfg y hy hyX.le

theorem transportTerm_eq_regular_on_nonnegative {O : Set InnerPoint} (hO : IsOpen O)
    (N : ℕ) (h e α : ℝ) {v u f beta u' f' : ℕ → InnerProfile}
    (hv : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → v j w = w.1 * beta j w)
    (hu : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → u j w = u' j w)
    (hf : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → f j w = f' j w)
    {w : InnerPoint} (hw : w ∈ O) (hX : 0 < w.1)
    {i : TailIndex} (hi : i ∈ transportIndices N) :
    transportTerm N h e α v u f i w = regularTransportTerm N h e α beta u' f' i w := by
  exact transportTerm_eq_regular_of_germs N h e α
    (fun j hj => germ_of_nonnegative_eqOn hO (hv j hj) hw hX)
    (fun j hj => germ_of_nonnegative_eqOn hO (hu j hj) hw hX)
    (fun j hj => germ_of_nonnegative_eqOn hO (hf j hj) hw hX) hX.ne' hi

theorem pressureTerm_eq_regular_on_nonnegative {O : Set InnerPoint} (hO : IsOpen O)
    (N : ℕ) (h C : ℝ) {f : SlowProfiles} {phi u beta : ℕ → InnerProfile}
    (hv : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → f.flux j w = w.1 * beta j w)
    (hu : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → f.axial j w = u j w)
    (hp : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → f.phi j w = phi j w)
    (hb : ∀ j ≤ N, ContDiffOn ℝ ∞ (beta j) O)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0)
    {w : InnerPoint} (hw : w ∈ O) (hX : 0 < w.1)
    {i : PressureIndex} (hi : i ∈ pressureIndices N) :
    pressureTerm N h C f i w / (2 * w.1) = regularPressureTerm N h C phi u beta i w := by
  exact pressureTerm_eq_regular_of_germs N h C
    (fun j hj => germ_of_nonnegative_eqOn hO (hv j hj) hw hX)
    (fun j hj => germ_of_nonnegative_eqOn hO (hu j hj) hw hX)
    (fun j hj => germ_of_nonnegative_eqOn hO (hp j hj) hw hX)
    (fun j hj => ((hb j hj).contDiffAt (hO.mem_nhds hw)).of_le
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le)
    (hL w hw) hX.ne' hi

/-! ## The same finite monomials, with regular inner coefficients -/

theorem transportTail_eq_regular_of_germs (N : ℕ) (q h e α : ℝ)
    {v u f beta u' f' : ℕ → InnerProfile} {w : InnerPoint}
    (hv : ∀ j ≤ N, v j =ᶠ[𝓝 w] AxisSourceRegularity.axisFactor (beta j))
    (hu : ∀ j ≤ N, u j =ᶠ[𝓝 w] u' j)
    (hf : ∀ j ≤ N, f j =ᶠ[𝓝 w] f' j) (hX : w.1 ≠ 0) :
    transportTail N q h e α v u f w =
      ∑ i ∈ transportIndices N,
        q ^ transportPower N h e i * regularTransportTerm N h e α beta u' f' i w := by
  rw [transportTail_eq_finite_monomials]
  apply Finset.sum_congr rfl
  intro i hi
  rw [transportTerm_eq_regular_of_germs N h e α hv hu hf hX hi]

theorem pressureTail_div_eq_regular_of_germs (N : ℕ) (q h C : ℝ)
    {f : SlowProfiles} {phi u beta : ℕ → InnerProfile} {w : InnerPoint}
    (hv : ∀ j ≤ N, f.flux j =ᶠ[𝓝 w] AxisSourceRegularity.axisFactor (beta j))
    (hu : ∀ j ≤ N, f.axial j =ᶠ[𝓝 w] u j)
    (hp : ∀ j ≤ N, f.phi j =ᶠ[𝓝 w] phi j)
    (hb : ∀ j ≤ N, ContDiffAt ℝ 2 (beta j) w)
    (hL : CoordinateAlgebra.L h w.2 ≠ 0) (hX : w.1 ≠ 0) :
    pressureTail N q h C f w / (2 * w.1) =
      ∑ i ∈ pressureIndices N,
        q ^ pressurePower N h i * regularPressureTerm N h C phi u beta i w := by
  rw [pressureTail_eq_finite_monomials, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_div_assoc, pressureTerm_eq_regular_of_germs N h C hv hu hp hb hL hX hi]

/-- The physical radial denominator contributes precisely the original
single power of `q`.  Regularizing `X` costs no further power. -/
theorem radialTail_eq_regular_of_germs {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (C : ℝ) {f : SlowProfiles} {phi u beta : ℕ → InnerProfile}
    {p : PhysicalPoint} (hp : p.1 < 1) (hs : 0 < p.2.1)
    (hv : ∀ j ≤ N, f.flux j =ᶠ[𝓝 (SimilarityProfile.inner h p)]
      AxisSourceRegularity.axisFactor (beta j))
    (hu : ∀ j ≤ N, f.axial j =ᶠ[𝓝 (SimilarityProfile.inner h p)] u j)
    (hphi : ∀ j ≤ N, f.phi j =ᶠ[𝓝 (SimilarityProfile.inner h p)] phi j)
    (hb : ∀ j ≤ N, ContDiffAt ℝ 2 (beta j) (SimilarityProfile.inner h p))
    (hL : CoordinateAlgebra.L h (SimilarityProfile.inner h p).2 ≠ 0) :
    pressureTail N (SimilarityProfile.q h p) h C f (SimilarityProfile.inner h p) /
        (2 * p.2.1) =
      ∑ i ∈ pressureIndices N,
        SimilarityProfile.q h p ^ (pressurePower N h i - 1) *
          regularPressureTerm N h C phi u beta i (SimilarityProfile.inner h p) := by
  rw [radialTail_eq_finite_monomials hh hh1 N C f hp hs]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pressureTerm_eq_regular_of_germs N h C hv hu hphi hb hL
    (LeadingStress.inner_X_pos hh hh1 hp hs).ne' hi]

theorem angular_power_lower {h : ℝ} (hh : 0 ≤ h) (N : ℕ)
    {i : TailIndex} (hi : i ∈ transportIndices N) :
    2 * (N : ℝ) * h - 2 ≤ transportPower N h (angularExponent h) i := by
  have hb := common_tail_power_lower hh N
  exact hb.1 ▸ hb.2.1.trans (transportPower_lower hh N (angularExponent h) hi)

theorem axial_power_lower {h : ℝ} (hh : 0 ≤ h) (N : ℕ)
    {i : TailIndex} (hi : i ∈ transportIndices N) :
    2 * (N : ℝ) * h - 2 ≤ transportPower N h (axialExponent h) i := by
  have hb := common_tail_power_lower hh N
  exact hb.1 ▸ hb.2.2.trans (transportPower_lower hh N (axialExponent h) hi)

theorem radial_power_lower {h : ℝ} (hh : 0 ≤ h) (N : ℕ)
    {i : PressureIndex} (hi : i ∈ pressureIndices N) :
    2 * (N : ℝ) * h - 2 ≤ pressurePower N h i - 1 := by
  have hb := (common_tail_power_lower hh N).1
  have hp := pressurePower_lower hh N hi
  linarith

/-! ## Actual smoothness through `X = 0` and even radial pullbacks -/

theorem radiusPoint_contDiff : ContDiff ℝ ∞ radiusPoint := by
  change ContDiff ℝ ∞ (fun w : InnerPoint => (w.1 ^ 2 / 2, w.2))
  exact ((contDiff_fst.pow 2).div_const 2).prodMk contDiff_snd

theorem toRadius_smoothOn {O : Set InnerPoint} {f : InnerProfile}
    (hf : ContDiffOn ℝ ∞ f O) :
    ContDiffOn ℝ ∞ (toRadius f) (radiusPoint ⁻¹' O) :=
  hf.comp radiusPoint_contDiff.contDiffOn (fun _ hw => hw)

theorem toRadius_even (f : InnerProfile) (R η : ℝ) :
    toRadius f (-R, η) = toRadius f (R, η) := by
  simp [toRadius, radiusPoint]

theorem regularTransportTerm_right_smoothOn {O : Set InnerPoint} (hO : IsOpen O)
    (N : ℕ) (h e α : ℝ) (beta u f : ℕ → InnerProfile)
    (hb : ∀ j ≤ N, ContDiffOn ℝ ∞ (beta j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hf : ∀ j ≤ N, ContDiffOn ℝ ∞ (f j) O)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0)
    {i : TailIndex} (hi : i ∈ transportIndices N) :
    ContDiffOn ℝ ∞ (regularTransportTerm N h e α beta u f i)
      (O ∩ {w | 0 ≤ w.1}) :=
  (regularTransportTerm_smoothOn hO N h e α beta u f hb hu hf hL hi).mono
    Set.inter_subset_left

theorem regularPressureTerm_right_smoothOn {O : Set InnerPoint} (hO : IsOpen O)
    (N : ℕ) (h C : ℝ) (phi u beta : ℕ → InnerProfile)
    (hp : ∀ j ≤ N, ContDiffOn ℝ ∞ (phi j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hb : ∀ j ≤ N, ContDiffOn ℝ ∞ (beta j) O)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0)
    {i : PressureIndex} (hi : i ∈ pressureIndices N) :
    ContDiffOn ℝ ∞ (regularPressureTerm N h C phi u beta i)
      (O ∩ {w | 0 ≤ w.1}) :=
  (regularPressureTerm_smoothOn hO N h C phi u beta hp hu hb hL hi).mono
    Set.inter_subset_left

theorem regularTransportTerm_radial_smoothOn {O : Set InnerPoint} (hO : IsOpen O)
    (N : ℕ) (h e α : ℝ) (beta u f : ℕ → InnerProfile)
    (hb : ∀ j ≤ N, ContDiffOn ℝ ∞ (beta j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hf : ∀ j ≤ N, ContDiffOn ℝ ∞ (f j) O)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0)
    {i : TailIndex} (hi : i ∈ transportIndices N) :
    ContDiffOn ℝ ∞ (toRadius (regularTransportTerm N h e α beta u f i))
      (radiusPoint ⁻¹' O) :=
  toRadius_smoothOn (regularTransportTerm_smoothOn hO N h e α beta u f hb hu hf hL hi)

theorem regularPressureTerm_radial_smoothOn {O : Set InnerPoint} (hO : IsOpen O)
    (N : ℕ) (h C : ℝ) (phi u beta : ℕ → InnerProfile)
    (hp : ∀ j ≤ N, ContDiffOn ℝ ∞ (phi j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hb : ∀ j ≤ N, ContDiffOn ℝ ∞ (beta j) O)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0)
    {i : PressureIndex} (hi : i ∈ pressureIndices N) :
    ContDiffOn ℝ ∞ (toRadius (regularPressureTerm N h C phi u beta i))
      (radiusPoint ⁻¹' O) :=
  toRadius_smoothOn (regularPressureTerm_smoothOn hO N h C phi u beta hp hu hb hL hi)

end NavierStokes.AxisTailRegularity

end
end

end

@[expose] public section

noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.BaseResidual

open SlowBorelBase

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

section Axis

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Zero positive-order coefficient values are preserved by the actual sum,
irrespective of the cutoff schedule. -/
theorem slowSum_eq_leading_of_positive_zero (a : ℕ → ℕ) (h q : ℝ)
    {f : ℕ → Inner → V} {w : Inner} (hz : ∀ j, 0 < j → f j w = 0) :
    slowSum a h f (q, w) = f 0 w := by
  have hs : ∀ j, slowStage a h f j (q, w) = 0 := by
    intro j
    by_cases hj : j = 0
    · subst j; simp
    · rw [slowStage_eq hj]
      simp [powerStage, powerCoefficient, hz j (Nat.pos_of_ne_zero hj)]
  change f 0 w + ∑' j, slowStage a h f j (q, w) = f 0 w
  simp [hs]

/-- At the spatial origin the physical similarity coordinates have their
exact values; this is not an asymptotic coordinate comparison. -/
theorem physicalChart_origin {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {t : ℝ} (ht : t < 1) : physicalChart h (t, (0, 0)) = (1 - t, (0, 0)) := by
  have hq := NaturalCore.physicalQ_at_zero_z hh hh1 ht 0
  have he := NaturalCore.physicalEta_at_zero_z h t 0
  change (NaturalCore.physicalQ h (t, (0, 0)),
    (0 / NaturalCore.physicalQ h (t, (0, 0)),
      NaturalCore.physicalEta h (t, (0, 0)))) = _
  rw [hq, he, zero_div]

/-- Summing and cutting the streams before differentiation preserves the
leading axial value exactly when the positive axial axis constants vanish. -/
theorem baseVelocity_at_origin {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients}
    (hd : SmoothCoefficients d) (C : ℝ)
    (hz : ∀ j, 0 < j → d.axial j (0, 0) = 0) {t : ℝ} (ht : t < 1) :
    baseVelocity a h C d (t, 0) =
      ((1 - t) ^ (-CoordinateAlgebra.A h) * d.axial 0 (0, 0)) •
        ProblemStatement.coordinateVector 2 := by
  have hp : (AxisymmetricFields.profilePoint t (0 : ProblemStatement.Space)).1 < 1 := ht
  have hH := (physicalProfile_smoothAt ha hh hh1
    (bundleComponent_smooth hd C 0) (-CoordinateAlgebra.A h) hp).differentiableAt (by simp)
  have hK := (physicalProfile_smoothAt ha hh hh1
    (bundleComponent_smooth hd C 1) (1 / 2 - CoordinateAlgebra.A h) hp).differentiableAt (by simp)
  change AxisymmetricFields.velocity (streamFactor a h C d) (swirlPotential a h C d)
    (t, 0) = _
  unfold streamFactor swirlPotential
  rw [AxisymmetricFields.velocity_on_axis _ _ t 0 hH hK (by simp) (by simp)]
  change (physicalProfile a h (-CoordinateAlgebra.A h) (bundleComponent C d 0)
    (t, (0, 0))) • _ = _
  unfold physicalProfile
  rw [physicalChart_origin hh hh1 ht,
    slowSum_eq_leading_of_positive_zero a h (1 - t)]
  · change ((1 - t) ^ (-CoordinateAlgebra.A h) *
      ProfileHistories.average (d.axial 0) (0, 0)) • _ = _
    rw [ProfileHistories.average_at_axis]
  · intro j hj
    change ProfileHistories.average (d.axial j) (0, 0) = 0
    rw [ProfileHistories.average_at_axis]
    exact hz j hj

theorem baseVelocity_norm_at_origin {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients}
    (hd : SmoothCoefficients d) (C : ℝ)
    (hz : ∀ j, 0 < j → d.axial j (0, 0) = 0) (h0 : 0 < d.axial 0 (0, 0))
    {t : ℝ} (ht : t < 1) :
    ‖baseVelocity a h C d (t, 0)‖ =
      (1 - t) ^ (-CoordinateAlgebra.A h) * d.axial 0 (0, 0) := by
  rw [baseVelocity_at_origin ha hh hh1 hd C hz ht, norm_smul]
  simp only [ProblemStatement.coordinateVector, PiLp.norm_single, norm_one,
    mul_one, Real.norm_eq_abs]
  exact abs_of_pos (mul_pos (Real.rpow_pos_of_pos (sub_pos.mpr ht) _) h0)

/-- The concrete Borel base retains the leading axial blow-up. No agreement
with an unspecified limiting field is an input. -/
theorem baseVelocity_axis_tendsto_atTop {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients}
    (hd : SmoothCoefficients d) (C : ℝ)
    (hz : ∀ j, 0 < j → d.axial j (0, 0) = 0) (h0 : 0 < d.axial 0 (0, 0)) :
    Tendsto (fun t : ℝ => ‖baseVelocity a h C d (t, 0)‖) (𝓝[<] 1) atTop := by
  have hA : 0 < CoordinateAlgebra.A h := by dsimp [CoordinateAlgebra.A]; linarith
  have ht := (BlowupImplication.negative_power_tendsto_atTop hA
    (BlowupImplication.remaining_time_tendsto 1)).atTop_mul_pos h0 tendsto_const_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (baseVelocity_norm_at_origin ha hh hh1 hd C hz h0 ht).symm

theorem baseVelocity_speedUnbounded {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients}
    (hd : SmoothCoefficients d) (C : ℝ)
    (hz : ∀ j, 0 < j → d.axial j (0, 0) = 0) (h0 : 0 < d.axial 0 (0, 0)) :
    ProblemStatement.SpeedUnboundedAtOne (baseVelocity a h C d) :=
  NaturalCore.speedUnbounded_of_axis_tendsto
    (baseVelocity_axis_tendsto_atTop ha hh hh1 hd C hz h0)

end Axis

section Monomials

open PhysicalCoordinateBounds

/-- The homogeneous lift is defined before solving the implicit coordinate
equation. This makes its degree an exact scaling identity. -/
noncomputable def monomialLift (a b : ℝ) (f : Inner → ℝ) (y : Chart) : ℝ :=
  powerLift b y * f (xLift y, etaLift a y)

theorem monomialLift_smooth {f : Inner → ℝ} (hf : ContDiff ℝ ∞ f) (a b : ℝ) :
    ContDiffOn ℝ ∞ (monomialLift a b f) positiveTime := by
  exact (powerLift_contDiffOn b).mul
    (hf.comp_contDiffOn (xLift_contDiffOn.prodMk (etaLift_contDiffOn a)))

theorem monomialLift_homogeneous (a b : ℝ) (f : Inner → ℝ) {r : ℝ} (hr : 0 < r)
    {y : Chart} (hy : y ∈ positiveTime) :
    monomialLift a b f (dilation a r y) = r ^ b * monomialLift a b f y := by
  simp only [monomialLift, powerLift_homogeneous a b hr hy,
    xLift_homogeneous a hr hy, etaLift_homogeneous a hr hy, Real.rpow_zero, one_mul]
  ring

theorem pullback_eq_homogeneous (h b : ℝ) (f : Inner → ℝ) :
    SimilarityProfile.pullback h b f =
      (monomialLift (2 * h) b f ∘ inverseCoordinates (2 * h)) ∘ timeShift := by
  rfl

/-- Every smooth inner monomial has actual physical jets with a loss of one
power per derivative. The constant is derived by compactness and scaling. -/
theorem physical_monomial_bound {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : Inner → ℝ} (hf : ContDiff ℝ ∞ f) (b lo hi qbig : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Chart, p.1 < 1 → (physicalChart h p).1 ≤ qbig →
      (physicalChart h p).2.1 ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ m (SimilarityProfile.pullback h b f) p‖ ≤
        C * (physicalChart h p).1 ^ (b - m) := by
  obtain ⟨C, hC, hb⟩ := homogeneous_derivative_bound
    (a := 2 * h) (by linarith) (by linarith) (monomialLift_smooth hf (2 * h) b)
    (fun _ hr _ hy => monomialLift_homogeneous (2 * h) b f hr hy) lo hi qbig m
  refine ⟨C, hC, fun p hp hq hX => ?_⟩
  rw [pullback_eq_homogeneous, norm_iteratedFDeriv_timeShift]
  exact hb (timeShift p) (sub_pos.mpr hp) hq hX

/-- A local smooth coefficient has a genuine smooth extension on a
neighborhood of a compact set. This is used only to estimate its local jets. -/
theorem exists_local_coefficient_extension {U K : Set Inner} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {f : Inner → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ F : Inner → ℝ, ContDiff ℝ ∞ F ∧ ∀ w ∈ K, f =ᶠ[𝓝 w] F := by
  obtain ⟨χ⟩ := ParametricModulation.exists_compactCutoff K U hK hU hKU
  let F : Inner → ℝ := fun w => χ.value w * f w
  have hF : ContDiff ℝ ∞ F := by
    apply contDiff_iff_contDiffAt.mpr
    intro w
    by_cases hw : w ∈ U
    · exact χ.smooth.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hw))
    · have he : F =ᶠ[𝓝 w] (fun _ => 0) := by
        filter_upwards [χ.zero_near w hw] with v hv
        simp [F, hv]
      exact contDiffAt_const.congr_of_eventuallyEq he
  refine ⟨F, hF, fun w hw => ?_⟩
  filter_upwards [χ.open_neighborhood.mem_nhds (χ.contains hw)] with v hv
  simp [F, χ.one_on v hv]

/-- Local coefficient regularity suffices for the physical estimate. All
coefficients with `1/X` or `1/L` may therefore stay on their true domain. -/
theorem physical_monomial_bound_on {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {U K : Set Inner} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : Inner → ℝ} (hf : ContDiffOn ℝ ∞ f U) (b lo hi qbig : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Chart, p.1 < 1 → (physicalChart h p).1 ≤ qbig →
      (physicalChart h p).2.1 ∈ Icc lo hi → (physicalChart h p).2 ∈ K →
      ‖iteratedFDeriv ℝ m (SimilarityProfile.pullback h b f) p‖ ≤
        C * (physicalChart h p).1 ^ (b - m) := by
  obtain ⟨F, hF, hFe⟩ := exists_local_coefficient_extension hU hK hKU hf
  obtain ⟨C, hC, hb⟩ := physical_monomial_bound hh hh1 hF b lo hi qbig m
  refine ⟨C, hC, fun p hp hq hX hw => ?_⟩
  have he : SimilarityProfile.pullback h b f =ᶠ[𝓝 p]
      SimilarityProfile.pullback h b F := by
    filter_upwards [(hFe _ hw).comp_tendsto
      (physicalChart_smoothAt hh hh1 hp).snd.continuousAt] with y hy
    change (physicalChart h y).1 ^ b * f (physicalChart h y).2 =
      (physicalChart h y).1 ^ b * F (physicalChart h y).2
    exact congrArg (fun v => (physicalChart h y).1 ^ b * v) hy
  rw [iteratedFDeriv_eq_of_eventuallyEq he m]
  exact hb p hp hq hX

end Monomials

section CartesianMonomials

open ProblemStatement

/-- Cartesian monomial, given by `SimilarityProfile.pullback h b f
(AxisymmetricFields.profilePoint z.1 z.2)`. -/
noncomputable def cartesianMonomial (h b : ℝ) (f : Inner → ℝ) (z : SpaceTime) : ℝ :=
  SimilarityProfile.pullback h b f (AxisymmetricFields.profilePoint z.1 z.2)

theorem cartesianMonomial_smoothAt {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : Inner → ℝ} {z : SpaceTime} (ht : z.1 < 1)
    (hf : ContDiffAt ℝ ∞ f (cartesianChart h z).2) :
    ContDiffAt ℝ ∞ (cartesianMonomial h b f) z :=
  (SimilarityProfile.pullback_smoothAt hh hh1 ht hf).comp z
    AxisymmetricFields.contDiff_profilePoint.contDiffAt

theorem physical_monomial_finite_bound {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : Inner → ℝ} (hf : ContDiff ℝ ∞ f) (b lo hi : ℝ) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Chart, p.1 < 1 → (physicalChart h p).1 ≤ 1 →
      (physicalChart h p).2.1 ∈ Icc lo hi → ∀ m ≤ M,
      ‖iteratedFDeriv ℝ m (SimilarityProfile.pullback h b f) p‖ ≤
        C * (physicalChart h p).1 ^ (b - M) := by
  classical
  choose A hA hAb using fun m => physical_monomial_bound hh hh1 hf b lo hi 1 m
  let C := 1 + ∑ i ∈ Finset.range (M + 1), A i
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => (hA i).le))
  refine ⟨C, hC, fun p hp hq hX m hm => ?_⟩
  have hAm : A m ≤ C := by
    have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (M + 1)) => (hA i).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    dsimp [C]
    linarith
  have hqm := Real.rpow_le_rpow_of_exponent_ge (physicalChart_positive hh hh1 hp) hq
    (show b - (M : ℝ) ≤ b - m by exact sub_le_sub_left (by exact_mod_cast hm) b)
  exact (hAb m p hp hq hX).trans (mul_le_mul hAm hqm
    (Real.rpow_nonneg (physicalChart_positive hh hh1 hp).le _) hC.le)

/-- On a fixed compact Cartesian set, polynomial reconstruction from squared
radius adds a constant but no further loss of powers. -/
theorem cartesian_monomial_bound {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : Inner → ℝ} (hf : ContDiff ℝ ∞ f) (b lo hi : ℝ)
    {K : Set SpaceTime} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, z.1 < 1 → (cartesianChart h z).1 ≤ 1 →
      (cartesianChart h z).2.1 ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ m (cartesianMonomial h b f) z‖ ≤
        C * (cartesianChart h z).1 ^ (b - m) := by
  obtain ⟨A, hA, hAb⟩ := physical_monomial_finite_bound hh hh1 hf b lo hi m
  let G : SpaceTime → Chart := fun z => AxisymmetricFields.profilePoint z.1 z.2
  have hG : ContDiff ℝ ∞ G := AxisymmetricFields.contDiff_profilePoint
  obtain ⟨D, hD, hDb⟩ := compact_map_finite_bound hG hK m
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨(m.factorial : ℝ) * A * D ^ m, by positivity, ?_⟩
  intro z hz ht hq hX
  have hU : IsOpen {p : Chart | p.1 < 1} := isOpen_lt continuous_fst continuous_const
  have hS : IsOpen {p : SpaceTime | p.1 < 1} := isOpen_lt continuous_fst continuous_const
  have hF : ContDiffOn ℝ ∞ (SimilarityProfile.pullback h b f) {p | p.1 < 1} :=
    fun p hp => (SimilarityProfile.pullback_smoothAt hh hh1 hp hf.contDiffAt).contDiffWithinAt
  have hc := norm_iteratedFDerivWithin_comp_le hF hG.contDiffOn
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) hU.uniqueDiffOn hS.uniqueDiffOn
    (show MapsTo G {p | p.1 < 1} {p | p.1 < 1} from fun _ hp => hp) ht
    (C := A * (cartesianChart h z).1 ^ (b - m)) (D := D)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i hU ht]
      exact hAb (G z) ht hq hX i hi)
    (fun i hi him => by
      rw [iteratedFDerivWithin_of_isOpen i hS ht]
      exact hDb z hz i hi him)
  rw [iteratedFDerivWithin_of_isOpen m hS ht] at hc
  exact hc.trans_eq (by ring)

theorem cartesian_monomial_bound_on {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {U K : Set Inner} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : Inner → ℝ} (hf : ContDiffOn ℝ ∞ f U) (b lo hi : ℝ)
    {B : Set SpaceTime} (hB : IsCompact B) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ B, z.1 < 1 → (cartesianChart h z).1 ≤ 1 →
      (cartesianChart h z).2.1 ∈ Icc lo hi → (cartesianChart h z).2 ∈ K →
      ‖iteratedFDeriv ℝ m (cartesianMonomial h b f) z‖ ≤
        C * (cartesianChart h z).1 ^ (b - m) := by
  obtain ⟨F, hF, hFe⟩ := exists_local_coefficient_extension hU hK hKU hf
  obtain ⟨C, hC, hb⟩ := cartesian_monomial_bound hh hh1 hF b lo hi hB m
  refine ⟨C, hC, fun z hz ht hq hX hw => ?_⟩
  have he : cartesianMonomial h b f =ᶠ[𝓝 z] cartesianMonomial h b F := by
    have hg := (physicalChart_smoothAt hh hh1 ht).snd.comp z
      AxisymmetricFields.contDiff_profilePoint.contDiffAt
    filter_upwards [(hFe _ hw).comp_tendsto hg.continuousAt] with y hy
    exact congrArg (fun v => (cartesianChart h y).1 ^ b * v) hy
  rw [(SolenoidalDiagonal.iteratedFDeriv_eventuallyEq he m).self_of_nhds]
  exact hb z hz ht hq hX

theorem norm_jet_sum_le {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {ι : Type*} (s : Finset ι)
    (f : ι → D → V) {x : D} (hf : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => ∑ i ∈ s, f i y) x‖ ≤
      ∑ i ∈ s, ‖iteratedFDeriv ℝ m (f i) x‖ := by
  have hs : ∀ i ∈ s, ContDiffWithinAt ℝ m (f i) univ x :=
    fun i hi => ((hf i hi).of_le (nat_le_infty m)).contDiffWithinAt
  have he := iteratedFDerivWithin_fun_sum_apply uniqueDiffOn_univ (mem_univ x) hs
  simp only [iteratedFDerivWithin_univ] at he
  rw [he]
  exact norm_sum_le _ _

/-- A finite family of genuine local coefficient functions yields the
expected power bound for every actual Cartesian jet of its sum. -/
theorem cartesian_finite_monomials_bound {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {U K : Set Inner} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {ι : Type*} [Fintype ι] (f : ι → Inner → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (b : ι → ℝ) (bmin lo hi : ℝ) (hmin : ∀ i, bmin ≤ b i)
    {B : Set SpaceTime} (hB : IsCompact B) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ B, z.1 < 1 → (cartesianChart h z).1 ≤ 1 →
      (cartesianChart h z).2.1 ∈ Icc lo hi → (cartesianChart h z).2 ∈ K →
      ‖iteratedFDeriv ℝ m (fun y => ∑ i, cartesianMonomial h (b i) (f i) y) z‖ ≤
        C * (cartesianChart h z).1 ^ (bmin - m) := by
  classical
  choose A hA hAb using fun i => cartesian_monomial_bound_on hh hh1 hU hK hKU
    (hf i) (b i) lo hi hB m
  refine ⟨1 + ∑ i, A i, add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => (hA i).le)), ?_⟩
  intro z hz ht hq hX hw
  have hqp : 0 < (cartesianChart h z).1 := physicalChart_positive hh hh1 ht
  calc
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ m (cartesianMonomial h (b i) (f i)) z‖ :=
      norm_jet_sum_le Finset.univ _ (fun i _ => cartesianMonomial_smoothAt hh hh1 ht
        ((hf i).contDiffAt (hU.mem_nhds (hKU hw)))) m
    _ ≤ ∑ i, A i * (cartesianChart h z).1 ^ (bmin - m) := by
      apply Finset.sum_le_sum
      intro i _
      exact (hAb i z hz ht hq hX hw).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hqp hq (sub_le_sub_right (hmin i) _)) (hA i).le)
    _ = (∑ i, A i) * (cartesianChart h z).1 ^ (bmin - m) := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hqp.le _)

end CartesianMonomials

section FixedPrefixRates

open ProblemStatement DiagonalResidual

/-- The filter carries only geometric information: bounded physical
coordinates, a fixed inner radial window, and scale tending to zero. -/
structure PhysicalApproach (l : Filter SpaceTime) (h lo hi : ℝ) where
  /-- Carrier of `PhysicalApproach`, of type `Set SpaceTime`. -/
  carrier : Set SpaceTime
  compact : IsCompact carrier
  in_carrier : ∀ᶠ z in l, z ∈ carrier
  past : ∀ᶠ z in l, z.1 < 1
  radial : ∀ᶠ z in l, (cartesianChart h z).2.1 ∈ Icc lo hi
  scale : Tendsto (fun z => (cartesianChart h z).1) l (𝓝 0)

theorem PhysicalApproach.small {l : Filter SpaceTime} {h lo hi : ℝ}
    (A : PhysicalApproach l h lo hi) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ z in l, (cartesianChart h z).1 < δ :=
  A.scale.eventually (gt_mem_nhds hδ)

theorem PhysicalApproach.positive_small {l : Filter SpaceTime} {h lo hi : ℝ}
    (A : PhysicalApproach l h lo hi) (hh : 0 < h) (hh1 : h < 1 / 2) :
    ∀ᶠ z in l, 0 < (cartesianChart h z).1 ∧ (cartesianChart h z).1 ≤ 1 := by
  filter_upwards [A.past, A.small zero_lt_one] with z ht hq
  exact ⟨physicalChart_positive hh hh1 ht, hq.le⟩

theorem cartesian_fixed_prefix_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a : ℕ → ℕ} {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (lo hi b : ℝ)
    (ha : AdmissibleScales h f (innerBox lo hi) a)
    {K : Set SpaceTime} (hK : IsCompact K) (J m : ℕ) (hm : m ≤ J + 3) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ z ∈ K, z.1 < 1 →
      (cartesianChart h z).1 < δ → (cartesianChart h z).2.1 ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ m
        (fun y => cartesianProfile a h b f y - cartesianUncutPrefix h b f J y) z‖ ≤
          C * (cartesianChart h z).1 ^ (h * (J + 1) + b - 2 * m) := by
  obtain ⟨δ, C, hδ, hC, hb⟩ := powered_fixed_prefix_bound hh hh1 hf lo hi b ha J m hm
  let G : SpaceTime → Chart := fun z => AxisymmetricFields.profilePoint z.1 z.2
  have hG : ContDiff ℝ ∞ G := AxisymmetricFields.contDiff_profilePoint
  obtain ⟨D, hD, hDb⟩ := compact_map_finite_bound hG hK m
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨δ, (m.factorial : ℝ) * C * D ^ m, hδ, by positivity, ?_⟩
  intro z hz ht hq hX
  let F : Chart → V := fun p => physicalProfile a h b f p - physicalUncutPrefix h b f J p
  have hU : IsOpen {p : Chart | p.1 < 1} := isOpen_lt continuous_fst continuous_const
  have hS : IsOpen {p : SpaceTime | p.1 < 1} := isOpen_lt continuous_fst continuous_const
  have hF : ContDiffOn ℝ ∞ F {p | p.1 < 1} := by
    intro p hp
    exact ((physicalProfile_smoothAt ha.strictMono hh hh1 hf b hp).sub
      (physicalUncutPrefix_smoothAt hh hh1 hf b J hp)).contDiffWithinAt
  have hc := norm_iteratedFDerivWithin_comp_le hF hG.contDiffOn
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) hU.uniqueDiffOn hS.uniqueDiffOn
    (show MapsTo G {p | p.1 < 1} {p | p.1 < 1} from fun _ hp => hp) ht
    (C := C * (cartesianChart h z).1 ^ (h * (J + 1) + b - 2 * m)) (D := D)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i hU ht]
      exact hb i hi (G z) ht hq hX)
    (fun i hi him => by
      rw [iteratedFDerivWithin_of_isOpen i hS ht]
      exact hDb z hz i hi him)
  rw [iteratedFDerivWithin_of_isOpen m hS ht] at hc
  exact hc.trans_eq (by ring)

theorem cartesian_prefix_finiteJetRate
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter SpaceTime} {a : ℕ → ℕ} {h lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ)
    (ha : AdmissibleScales h f (innerBox lo hi) a)
    (J M : ℕ) (hM : M ≤ J + 3) :
    FiniteJetRate l (fun z => (cartesianChart h z).1)
      (fun z => cartesianProfile a h b f z - cartesianUncutPrefix h b f J z)
      M (h * (J + 1) + b - 2 * M) := by
  apply finiteJetRate_of_jetRate ((A.positive_small hh hh1).mono (fun _ hx => hx.1))
  intro m hm
  obtain ⟨δ, C, hδ, hC, hb⟩ := cartesian_fixed_prefix_bound hh hh1 hf lo hi b ha A.compact
    J m (hm.trans hM)
  have hr : JetRate l (fun z => (cartesianChart h z).1)
      (fun z => cartesianProfile a h b f z - cartesianUncutPrefix h b f J z)
      m (h * (J + 1) + b - 2 * m) := by
    refine ⟨C, hC.le, ?_⟩
    filter_upwards [A.in_carrier, A.past, A.radial, A.small hδ] with z hz ht hX hq
    exact hb z hz ht hq hX
  apply hr.weaken (A.positive_small hh hh1)
  have hmR : (m : ℝ) ≤ M := by exact_mod_cast hm
  linarith

end FixedPrefixRates

section RateAlgebra

open DiagonalResidual

variable {D E F G : Type}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem finiteRate_mono {l : Filter D} {q : D → ℝ} {f : D → E} {M N : ℕ} {r : ℝ}
    (hf : FiniteJetRate l q f M r) (hNM : N ≤ M) : FiniteJetRate l q f N r := by
  obtain ⟨C, hC, hb⟩ := hf
  exact ⟨C, hC, hb.mono (fun x hx m hm => hx m (hm.trans hNM))⟩

theorem finiteRate_at {l : Filter D} {q : D → ℝ} {f : D → E} {M m : ℕ} {r : ℝ}
    (hf : FiniteJetRate l q f M r) (hm : m ≤ M) : JetRate l q f m r := by
  obtain ⟨C, hC, hb⟩ := hf
  exact ⟨C, hC, hb.mono (fun _ hx => hx m hm)⟩

theorem finiteRate_weaken {l : Filter D} {q : D → ℝ} {f : D → E} {M : ℕ} {r s : ℝ}
    (hf : FiniteJetRate l q f M r) (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1) (hsr : s ≤ r) :
    FiniteJetRate l q f M s := by
  apply finiteJetRate_of_jetRate (hq.mono (fun _ hx => hx.1))
  intro m hm
  exact (finiteRate_at hf hm).weaken hq hsr

theorem finiteRate_congr_on {l : Filter D} {q : D → ℝ} {f g : D → E} {M : ℕ} {r : ℝ}
    {U : Set D} (hf : FiniteJetRate l q f M r) (hU : IsOpen U)
    (hlU : ∀ᶠ x in l, x ∈ U) (hfg : EqOn f g U) : FiniteJetRate l q g M r := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨C, hC, ?_⟩
  filter_upwards [hlU, hb] with x hx hbx
  intro m hm
  rw [← ResidualStability.iteratedFDeriv_eqOn hU hfg m hx]
  exact hbx m hm

theorem finiteRate_linear {l : Filter D} {q : D → ℝ} {f : D → E} {M : ℕ} {r : ℝ}
    {U : Set D} (hf : FiniteJetRate l q f M r) (hU : IsOpen U)
    (hlU : ∀ᶠ x in l, x ∈ U) (hs : ContDiffOn ℝ ∞ f U) (L : E →L[ℝ] F) :
    FiniteJetRate l q (fun x => L (f x)) M r := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  filter_upwards [hlU, hb] with x hx hbx
  intro m hm
  exact (ResidualStability.norm_jet_linear_map L hU hs hx m).trans
    ((mul_le_mul_of_nonneg_left (hbx m hm) (norm_nonneg L)).trans_eq (by ring))

theorem finiteRate_add {l : Filter D} {q : D → ℝ} {f g : D → E} {M : ℕ} {r : ℝ}
    {U : Set D} (hf : FiniteJetRate l q f M r) (hg : FiniteJetRate l q g M r)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hsf : ContDiffOn ℝ ∞ f U) (hsg : ContDiffOn ℝ ∞ g U) :
    FiniteJetRate l q (fun x => f x + g x) M r := by
  obtain ⟨A, hA, ha⟩ := hf
  obtain ⟨B, hB, hb⟩ := hg
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  filter_upwards [hlU, ha, hb] with x hx hax hbx
  intro m hm
  exact (ResidualStability.norm_jet_add_le hU hsf hsg hx m).trans
    ((add_le_add (hax m hm) (hbx m hm)).trans_eq (by ring))

theorem finiteRate_bilinear {l : Filter D} {q : D → ℝ} {f : D → E} {g : D → F}
    {M : ℕ} {r s : ℝ} {U : Set D}
    (hf : FiniteJetRate l q f M r) (hg : FiniteJetRate l q g M s)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U) (hq : ∀ᶠ x in l, 0 < q x)
    (hsf : ContDiffOn ℝ ∞ f U) (hsg : ContDiffOn ℝ ∞ g U)
    (L : E →L[ℝ] F →L[ℝ] G) :
    FiniteJetRate l q (fun x => L (f x) (g x)) M (r + s) := by
  obtain ⟨A, hA, ha⟩ := hf
  obtain ⟨B, hB, hb⟩ := hg
  refine ⟨‖L‖ * (2 : ℝ) ^ M * A * B, by positivity, ?_⟩
  filter_upwards [hlU, hq, ha, hb] with x hx hqx hax hbx
  intro m hm
  calc
    _ ≤ ‖L‖ * (2 : ℝ) ^ m * (A * q x ^ r) * (B * q x ^ s) :=
      ResidualStability.norm_jet_bilinear_bound L hU hsf hsg hx m
        (fun k hk => hax k (hk.trans hm)) (fun k hk => hbx k (hk.trans hm))
    _ ≤ ‖L‖ * (2 : ℝ) ^ M * (A * q x ^ r) * (B * q x ^ s) := by
      gcongr
      norm_num
    _ = (‖L‖ * (2 : ℝ) ^ M * A * B) * q x ^ (r + s) := by
      rw [Real.rpow_add hqx]
      ring

theorem finiteRate_fderiv {l : Filter D} {q : D → ℝ} {f : D → E} {M : ℕ} {r : ℝ}
    (hf : FiniteJetRate l q f (M + 1) r) :
    FiniteJetRate l q (fderiv ℝ f) M r := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨C, hC, hb.mono ?_⟩
  intro x hx m hm
  rw [norm_iteratedFDeriv_fderiv]
  exact hx (m + 1) (Nat.add_le_add_right hm 1)

theorem finiteRate_compact {l : Filter D} {q : D → ℝ} {f : D → E}
    {K : Set D} (hf : ContDiff ℝ ∞ f) (hK : IsCompact K)
    (hlK : ∀ᶠ x in l, x ∈ K) (M : ℕ) : FiniteJetRate l q f M 0 := by
  classical
  have hb0 (m : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ m f x‖ ≤ C :=
    compact_jet_bound (F := f) isOpen_univ hf.contDiffOn hK (subset_univ K) m
  choose A hA hAb using hb0
  let C := ∑ i ∈ Finset.range (M + 1), A i
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => zero_le_one.trans (hA i))
  refine ⟨C, hC, hlK.mono ?_⟩
  intro x hx m hm
  simp only [Real.rpow_zero, mul_one]
  exact (hAb m x hx).trans (Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range (M + 1)) => zero_le_one.trans (hA i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)))

end RateAlgebra

section PotentialRates

open ProblemStatement DiagonalResidual

/-- Past, given by `Iio 1 ×ˢ univ`. -/
noncomputable def past : Set SpaceTime := Iio 1 ×ˢ univ
/-- Profile past, given by `Iio 1 ×ˢ univ`. -/
noncomputable def profilePast : Set Chart := Iio 1 ×ˢ univ

theorem past_isOpen : IsOpen past := isOpen_Iio.prod isOpen_univ
theorem profilePast_isOpen : IsOpen profilePast := isOpen_Iio.prod isOpen_univ

/-- Potential from scalars, given by `(-(1 / 2 : ℝ) * z.2 1 * H z) • coordinateVector 0 + ((1 /
2 : ℝ) * z.2 0 * H z) • coordinateVector 1 + K z • coordinateVector 2`. -/
noncomputable def potentialFromScalars (H K : SpaceTime → ℝ) (z : SpaceTime) : Space :=
  (-(1 / 2 : ℝ) * z.2 1 * H z) • coordinateVector 0 +
    ((1 / 2 : ℝ) * z.2 0 * H z) • coordinateVector 1 + K z • coordinateVector 2

/-- Basis injection, given by `(ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector i)`. -/
noncomputable def basisInjection (i : Fin 3) : ℝ →L[ℝ] Space :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector i)

theorem potentialFromScalars_smooth {H K : SpaceTime → ℝ} {U : Set SpaceTime}
    (hH : ContDiffOn ℝ ∞ H U) (hK : ContDiffOn ℝ ∞ K U) :
    ContDiffOn ℝ ∞ (potentialFromScalars H K) U := by
  have h0 : ContDiff ℝ ∞ (fun z : SpaceTime => (-(1 / 2 : ℝ)) * z.2 1) :=
    contDiff_const.mul ((AxisymmetricFields.projection 1).contDiff.comp contDiff_snd)
  have h1 : ContDiff ℝ ∞ (fun z : SpaceTime => (1 / 2 : ℝ) * z.2 0) :=
    contDiff_const.mul ((AxisymmetricFields.projection 0).contDiff.comp contDiff_snd)
  exact (((h0.contDiffOn.mul hH).smul contDiffOn_const).add
    ((h1.contDiffOn.mul hH).smul contDiffOn_const)).add (hK.smul contDiffOn_const)

theorem potentialFromScalars_sub (H K H' K' : SpaceTime → ℝ) :
    (fun z => potentialFromScalars H K z - potentialFromScalars H' K' z) =
      potentialFromScalars (fun z => H z - H' z) (fun z => K z - K' z) := by
  funext z
  simp only [potentialFromScalars, mul_sub, sub_smul]
  abel

theorem potential_eq_scalars (H K : Chart → ℝ) :
    AxisymmetricFields.potential H K =
      potentialFromScalars (fun z => H (AxisymmetricFields.profilePoint z.1 z.2))
        (fun z => K (AxisymmetricFields.profilePoint z.1 z.2)) := by
  funext z
  simp only [AxisymmetricFields.potential, potentialFromScalars, mul_assoc]

theorem potentialFromScalars_rate {l : Filter SpaceTime} {q : SpaceTime → ℝ}
    {H K : SpaceTime → ℝ} {U B : Set SpaceTime} {M : ℕ} {r : ℝ}
    (hU : IsOpen U) (hlU : ∀ᶠ z in l, z ∈ U) (hq : ∀ᶠ z in l, 0 < q z)
    (hB : IsCompact B) (hlB : ∀ᶠ z in l, z ∈ B)
    (hH : ContDiffOn ℝ ∞ H U) (hK : ContDiffOn ℝ ∞ K U)
    (hrH : FiniteJetRate l q H M r) (hrK : FiniteJetRate l q K M r) :
    FiniteJetRate l q (potentialFromScalars H K) M r := by
  let c0 : SpaceTime → ℝ := fun z => (-(1 / 2 : ℝ)) * z.2 1
  let c1 : SpaceTime → ℝ := fun z => (1 / 2 : ℝ) * z.2 0
  have hc0 : ContDiff ℝ ∞ c0 :=
    contDiff_const.mul ((AxisymmetricFields.projection 1).contDiff.comp contDiff_snd)
  have hc1 : ContDiff ℝ ∞ c1 :=
    contDiff_const.mul ((AxisymmetricFields.projection 0).contDiff.comp contDiff_snd)
  have hr0 := finiteRate_bilinear (finiteRate_compact (q := q) hc0 hB hlB M) hrH
    hU hlU hq hc0.contDiffOn hH (ContinuousLinearMap.mul ℝ ℝ)
  have hr1 := finiteRate_bilinear (finiteRate_compact (q := q) hc1 hB hlB M) hrH
    hU hlU hq hc1.contDiffOn hH (ContinuousLinearMap.mul ℝ ℝ)
  simp only [zero_add] at hr0 hr1
  have ha := finiteRate_linear hr0 hU hlU (hc0.contDiffOn.mul hH) (basisInjection 0)
  have hb := finiteRate_linear hr1 hU hlU (hc1.contDiffOn.mul hH) (basisInjection 1)
  have hc := finiteRate_linear hrK hU hlU hK (basisInjection 2)
  exact finiteRate_add (finiteRate_add ha hb hU hlU
    ((hc0.contDiffOn.mul hH).smul contDiffOn_const)
    ((hc1.contDiffOn.mul hH).smul contDiffOn_const)) hc hU hlU
    (((hc0.contDiffOn.mul hH).smul contDiffOn_const).add
      ((hc1.contDiffOn.mul hH).smul contDiffOn_const)) (hK.smul contDiffOn_const)

/-- Prefix stream, given by `physicalUncutPrefix h (-CoordinateAlgebra.A h) (bundleComponent C d
0) J`. -/
noncomputable def prefixStream (J : ℕ) (h C : ℝ) (d : Coefficients) : Chart → ℝ :=
  physicalUncutPrefix h (-CoordinateAlgebra.A h) (bundleComponent C d 0) J

/-- Prefix swirl, given by `physicalUncutPrefix h (1 / 2 - CoordinateAlgebra.A h)
(bundleComponent C d 1) J`. -/
noncomputable def prefixSwirl (J : ℕ) (h C : ℝ) (d : Coefficients) : Chart → ℝ :=
  physicalUncutPrefix h (1 / 2 - CoordinateAlgebra.A h) (bundleComponent C d 1) J

/-- Prefix potential, given by `AxisymmetricFields.potential (prefixStream J h C d) (prefixSwirl
J h C d)`. -/
noncomputable def prefixPotential (J : ℕ) (h C : ℝ) (d : Coefficients) : VelocityField :=
  AxisymmetricFields.potential (prefixStream J h C d) (prefixSwirl J h C d)

/-- Summed potential, given by `AxisymmetricFields.potential (streamFactor a h C d)
(swirlPotential a h C d)`. -/
noncomputable def summedPotential (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : VelocityField :=
  AxisymmetricFields.potential (streamFactor a h C d) (swirlPotential a h C d)

/-- Prefix velocity, given by `SpatialCurl.spatialCurl (prefixPotential J h C d)`. -/
noncomputable def prefixVelocity (J : ℕ) (h C : ℝ) (d : Coefficients) : VelocityField :=
  SpatialCurl.spatialCurl (prefixPotential J h C d)

/-- Prefix pressure, given by `cartesianUncutPrefix h (-2 * CoordinateAlgebra.A h)
(bundleComponent C d 2) J`. -/
noncomputable def prefixPressure (J : ℕ) (h C : ℝ) (d : Coefficients) : PressureField :=
  cartesianUncutPrefix h (-2 * CoordinateAlgebra.A h) (bundleComponent C d 2) J

theorem cartesianProfile_smooth {a : ℕ → ℕ} (ha : StrictMono a) {h b : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {f : ℕ → Inner → ℝ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) : ContDiffOn ℝ ∞ (cartesianProfile a h b f) past := by
  intro z hz
  exact ((physicalProfile_smoothAt ha hh hh1 hf b
    (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1).comp z
    AxisymmetricFields.contDiff_profilePoint.contDiffAt).contDiffWithinAt

theorem cartesianUncutPrefix_smooth {h b : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {f : ℕ → Inner → ℝ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (J : ℕ) :
    ContDiffOn ℝ ∞ (cartesianUncutPrefix h b f J) past := by
  intro z hz
  exact ((physicalUncutPrefix_smoothAt hh hh1 hf b J
    (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1).comp z
    AxisymmetricFields.contDiff_profilePoint.contDiffAt).contDiffWithinAt

theorem summedPotential_smooth {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (summedPotential a h C d) past := by
  rw [summedPotential, potential_eq_scalars]
  exact potentialFromScalars_smooth
    (cartesianProfile_smooth (b := -CoordinateAlgebra.A h) ha hh hh1 (bundleComponent_smooth hd C
        0))
    (cartesianProfile_smooth (b := 1 / 2 - CoordinateAlgebra.A h) ha hh hh1
      (bundleComponent_smooth hd C 1))

theorem prefixPotential_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ) :
    ContDiffOn ℝ ∞ (prefixPotential J h C d) past := by
  rw [prefixPotential, potential_eq_scalars]
  exact potentialFromScalars_smooth
    (cartesianUncutPrefix_smooth (b := -CoordinateAlgebra.A h) hh hh1 (bundleComponent_smooth hd C
        0) J)
    (cartesianUncutPrefix_smooth (b := 1 / 2 - CoordinateAlgebra.A h) hh hh1
      (bundleComponent_smooth hd C 1) J)

/-- Both potentials share the same derived cutoff schedule. Their difference
from a fixed prefix has a finite order increasing with the prefix. -/
theorem potential_prefix_rate {l : Filter SpaceTime} {a : ℕ → ℕ} {h C lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {d : Coefficients} (hd : SmoothCoefficients d)
    (ha : AdmissibleScales h (coefficientBundle C d) (innerBox lo hi) a)
    (J M : ℕ) (hM : M ≤ J + 3) :
    FiniteJetRate l (fun z => (cartesianChart h z).1)
      (fun z => summedPotential a h C d z - prefixPotential J h C d z)
      M (h * (J + 1) - CoordinateAlgebra.A h - 2 * M) := by
  have hq := A.positive_small hh hh1
  have hp : ∀ᶠ z in l, z ∈ past := A.past.mono (fun z hz => ⟨hz, mem_univ _⟩)
  have hH := cartesian_prefix_finiteJetRate hh hh1 A (bundleComponent_smooth hd C 0)
    (-CoordinateAlgebra.A h) (admissible_component hd ha 0) J M hM
  have hK := cartesian_prefix_finiteJetRate hh hh1 A (bundleComponent_smooth hd C 1)
    (1 / 2 - CoordinateAlgebra.A h) (admissible_component hd ha 1) J M hM
  have hHs := (cartesianProfile_smooth (b := -CoordinateAlgebra.A h) ha.strictMono hh hh1
    (bundleComponent_smooth hd C 0)).sub
    (cartesianUncutPrefix_smooth (b := -CoordinateAlgebra.A h) hh hh1 (bundleComponent_smooth hd C
        0) J)
  have hKs := (cartesianProfile_smooth (b := 1 / 2 - CoordinateAlgebra.A h) ha.strictMono hh hh1
    (bundleComponent_smooth hd C 1)).sub
    (cartesianUncutPrefix_smooth (b := 1 / 2 - CoordinateAlgebra.A h) hh hh1
      (bundleComponent_smooth hd C 1) J)
  have hr := potentialFromScalars_rate past_isOpen hp (hq.mono (fun _ hz => hz.1))
    A.compact A.in_carrier hHs hKs hH
    (finiteRate_weaken hK hq (show h * (J + 1) + -CoordinateAlgebra.A h - 2 * M ≤
      h * (J + 1) + (1 / 2 - CoordinateAlgebra.A h) - 2 * M by linarith))
  have he : (fun z => summedPotential a h C d z - prefixPotential J h C d z) =
      potentialFromScalars
        (fun z => cartesianProfile a h (-CoordinateAlgebra.A h) (bundleComponent C d 0) z -
          cartesianUncutPrefix h (-CoordinateAlgebra.A h) (bundleComponent C d 0) J z)
        (fun z => cartesianProfile a h (1 / 2 - CoordinateAlgebra.A h) (bundleComponent C d 1) z -
          cartesianUncutPrefix h (1 / 2 - CoordinateAlgebra.A h) (bundleComponent C d 1) J z) := by
    simp only [summedPotential, prefixPotential, potential_eq_scalars]
    exact potentialFromScalars_sub _ _ _ _
  rw [he]
  simpa only [sub_eq_add_neg] using hr

end PotentialRates

section CurlRates

open ProblemStatement DiagonalResidual ResidualStability

theorem spatialCurl_eq_full {F : VelocityField} {z : SpaceTime}
    (hF : DifferentiableAt ℝ F z) :
    SpatialCurl.spatialCurl F z =
      (SpatialCurl.curlLinear.comp (spaceRestriction Space)) (fderiv ℝ F z) := by
  unfold SpatialCurl.spatialCurl SpatialCurl.curl
  rw [space_fderiv_eq_full hF]
  rfl

theorem spatialCurl_sub {F G : VelocityField} {z : SpaceTime}
    (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) :
    SpatialCurl.spatialCurl (fun y => F y - G y) z =
      SpatialCurl.spatialCurl F z - SpatialCurl.spatialCurl G z := by
  rw [spatialCurl_eq_full (hF.fun_sub hG), spatialCurl_eq_full hF, spatialCurl_eq_full hG,
    fderiv_fun_sub hF hG, map_sub]

theorem spatialCurl_finiteRate {l : Filter SpaceTime} {q : SpaceTime → ℝ}
    {F : VelocityField} {U : Set SpaceTime} {M : ℕ} {r : ℝ}
    (hU : IsOpen U) (hlU : ∀ᶠ z in l, z ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hr : FiniteJetRate l q F (M + 1) r) :
    FiniteJetRate l q (SpatialCurl.spatialCurl F) M r := by
  have hd := finiteRate_linear (finiteRate_fderiv hr) hU hlU
    (hF.fderiv_of_isOpen hU (by simp)) (SpatialCurl.curlLinear.comp (spaceRestriction Space))
  apply finiteRate_congr_on hd hU hlU
  intro z hz
  exact (spatialCurl_eq_full ((hF.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))).symm

theorem prefixVelocity_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ) :
    ContDiffOn ℝ ∞ (prefixVelocity J h C d) past :=
  SpatialCurl.contDiffOn_spatialCurl (prefixPotential_smooth hh hh1 hd J C) (by simp)

theorem velocity_prefix_rate {l : Filter SpaceTime} {a : ℕ → ℕ} {h C lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {d : Coefficients} (hd : SmoothCoefficients d)
    (ha : AdmissibleScales h (coefficientBundle C d) (innerBox lo hi) a)
    (J M : ℕ) (hM : M + 1 ≤ J + 3) :
    FiniteJetRate l (fun z => (cartesianChart h z).1)
      (fun z => baseVelocity a h C d z - prefixVelocity J h C d z)
      M (h * (J + 1) - CoordinateAlgebra.A h - 2 * (M + 1)) := by
  have hp : ∀ᶠ z in l, z ∈ past := A.past.mono (fun _ hz => ⟨hz, mem_univ _⟩)
  have hs := summedPotential_smooth ha.strictMono hh hh1 hd C
  have hJ := prefixPotential_smooth hh hh1 hd J C
  have hr := spatialCurl_finiteRate past_isOpen hp (hs.sub hJ)
    (potential_prefix_rate hh hh1 A hd ha J (M + 1) hM)
  simp only [Nat.cast_add, Nat.cast_one] at hr
  apply finiteRate_congr_on hr past_isOpen hp
  intro z hz
  exact spatialCurl_sub ((hs.contDiffAt (past_isOpen.mem_nhds hz)).differentiableAt (by simp))
    ((hJ.contDiffAt (past_isOpen.mem_nhds hz)).differentiableAt (by simp))

theorem pressure_prefix_rate {l : Filter SpaceTime} {a : ℕ → ℕ} {h C lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {d : Coefficients} (hd : SmoothCoefficients d)
    (ha : AdmissibleScales h (coefficientBundle C d) (innerBox lo hi) a)
    (J M : ℕ) (hM : M ≤ J + 3) :
    FiniteJetRate l (fun z => (cartesianChart h z).1)
      (fun z => basePressure a h C d z - prefixPressure J h C d z)
      M (h * (J + 1) - 2 * CoordinateAlgebra.A h - 2 * M) := by
  simpa only [basePressure, prefixPressure, cartesianProfile, sub_eq_add_neg, neg_mul] using
    cartesian_prefix_finiteJetRate hh hh1 A (bundleComponent_smooth hd C 2)
      (-2 * CoordinateAlgebra.A h) (admissible_component hd ha 2) J M hM

end CurlRates

section PrefixGrowth

open ProblemStatement DiagonalResidual SlowExpansionResidual

theorem cartesianUncutPrefix_eq_sum {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (b : ℝ) (f : ℕ → Inner → ℝ) (J : ℕ) {z : SpaceTime} (ht : z.1 < 1) :
    cartesianUncutPrefix h b f J z =
      ∑ i : Fin (J + 1), cartesianMonomial h (b + slowOrder h i) (f i) z := by
  unfold cartesianUncutPrefix
  rw [physicalUncutPrefix_eq_finiteProfile hh hh1 b f J ht]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

theorem cartesian_prefix_growth {l : Filter SpaceTime} {h lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {f : ℕ → Inner → ℝ} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ) (J M : ℕ) :
    FiniteJetRate l (fun z => (cartesianChart h z).1) (cartesianUncutPrefix h b f J)
      M (b - M) := by
  have hq := A.positive_small hh hh1
  apply finiteJetRate_of_jetRate (hq.mono (fun _ hz => hz.1))
  intro m hm
  obtain ⟨C, hC, hb⟩ := cartesian_finite_monomials_bound hh hh1 isOpen_univ
    (innerBox_isCompact lo hi) (subset_univ _) (fun i : Fin (J + 1) => f i)
    (fun i => (hf i).contDiffOn) (fun i => b + slowOrder h i) b lo hi
    (fun i => le_add_of_nonneg_right (by unfold slowOrder; positivity)) A.compact m
  have hr : JetRate l (fun z => (cartesianChart h z).1)
      (fun z => ∑ i : Fin (J + 1), cartesianMonomial h (b + slowOrder h i) (f i) z)
      m (b - m) := by
    refine ⟨C, hC.le, ?_⟩
    filter_upwards [A.in_carrier, A.past, A.radial, hq] with z hz ht hX hqz
    exact hb z hz ht hqz.2 hX (physicalChart_inner_mem hh hh1 ht hX)
  have he := hr.congr_on past_isOpen
    (A.past.mono (fun _ ht => ⟨ht, mem_univ _⟩))
    (fun z hz => (cartesianUncutPrefix_eq_sum hh hh1 b f J hz.1).symm)
  exact he.weaken hq (sub_le_sub_left (by exact_mod_cast hm) b)

theorem prefixPotential_growth {l : Filter SpaceTime} {h C lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {d : Coefficients} (hd : SmoothCoefficients d) (J M : ℕ) :
    FiniteJetRate l (fun z => (cartesianChart h z).1) (prefixPotential J h C d)
      M (-CoordinateAlgebra.A h - M) := by
  have hq := A.positive_small hh hh1
  have hp : ∀ᶠ z in l, z ∈ past := A.past.mono (fun _ ht => ⟨ht, mem_univ _⟩)
  have hrH := cartesian_prefix_growth hh hh1 A (bundleComponent_smooth hd C 0)
    (-CoordinateAlgebra.A h) J M
  have hrK := cartesian_prefix_growth hh hh1 A (bundleComponent_smooth hd C 1)
    (1 / 2 - CoordinateAlgebra.A h) J M
  have hr := potentialFromScalars_rate past_isOpen hp (hq.mono (fun _ hz => hz.1))
    A.compact A.in_carrier
    (cartesianUncutPrefix_smooth (b := -CoordinateAlgebra.A h) hh hh1 (bundleComponent_smooth hd C
        0) J)
    (cartesianUncutPrefix_smooth (b := 1 / 2 - CoordinateAlgebra.A h) hh hh1
      (bundleComponent_smooth hd C 1) J) hrH (finiteRate_weaken hrK hq (by linarith))
  simp only [prefixPotential, potential_eq_scalars] at hr ⊢
  exact hr

theorem prefixVelocity_growth {l : Filter SpaceTime} {h C lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {d : Coefficients} (hd : SmoothCoefficients d) (J M : ℕ) :
    FiniteJetRate l (fun z => (cartesianChart h z).1) (prefixVelocity J h C d)
      M (-CoordinateAlgebra.A h - (M + 1)) := by
  have hp : ∀ᶠ z in l, z ∈ past := A.past.mono (fun _ ht => ⟨ht, mem_univ _⟩)
  have hr := prefixPotential_growth (C := C) hh hh1 A hd J (M + 1)
  simp only [Nat.cast_add, Nat.cast_one] at hr
  exact spatialCurl_finiteRate past_isOpen hp (prefixPotential_smooth hh hh1 hd J C) hr

end PrefixGrowth

section ProfileDerivatives

open ProblemStatement DiagonalResidual

/-- Profile derivative, given by `fderiv ℝ F p v`. -/
noncomputable def profileDerivative (v : Chart) (F : Chart → ℝ) (p : Chart) : ℝ :=
  fderiv ℝ F p v

/-- Cartesian derivative, given by `profileDerivative v F (AxisymmetricFields.profilePoint z.1
z.2)`. -/
noncomputable def cartesianDerivative (v : Chart) (F : Chart → ℝ) (z : SpaceTime) : ℝ :=
  profileDerivative v F (AxisymmetricFields.profilePoint z.1 z.2)

theorem profileDerivative_smooth {F : Chart → ℝ} (hF : ContDiffOn ℝ ∞ F profilePast)
    (v : Chart) : ContDiffOn ℝ ∞ (profileDerivative v F) profilePast :=
  (hF.fderiv_of_isOpen profilePast_isOpen (by simp)).clm_apply contDiffOn_const

theorem cartesianDerivative_smooth {F : Chart → ℝ} (hF : ContDiffOn ℝ ∞ F profilePast)
    (v : Chart) : ContDiffOn ℝ ∞ (cartesianDerivative v F) past :=
  (profileDerivative_smooth hF v).comp AxisymmetricFields.contDiff_profilePoint.contDiffOn
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

/-- A physical derivative of the actual profile remainder is estimated
before the polynomial Cartesian coordinate map is applied. -/
theorem derivative_fixed_prefix_bound {a : ℕ → ℕ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : ℕ → Inner → ℝ} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (lo hi b : ℝ)
    (ha : AdmissibleScales h f (innerBox lo hi) a)
    {K : Set SpaceTime} (hK : IsCompact K) (v : Chart) (J m : ℕ) (hm : m + 1 ≤ J + 3) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ z ∈ K, z.1 < 1 →
      (cartesianChart h z).1 < δ → (cartesianChart h z).2.1 ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ m (cartesianDerivative v
        (fun p => physicalProfile a h b f p - physicalUncutPrefix h b f J p)) z‖ ≤
          C * (cartesianChart h z).1 ^ (h * (J + 1) + b - 2 * (m + 1)) := by
  obtain ⟨δ, C, hδ, hC, hb⟩ := powered_fixed_prefix_bound hh hh1 hf lo hi b ha J (m + 1) hm
  simp only [Nat.cast_add, Nat.cast_one] at hb
  let G : SpaceTime → Chart := fun z => AxisymmetricFields.profilePoint z.1 z.2
  have hG : ContDiff ℝ ∞ G := AxisymmetricFields.contDiff_profilePoint
  obtain ⟨D, hD, hDb⟩ := compact_map_finite_bound hG hK m
  let L := ContinuousLinearMap.apply ℝ ℝ v
  let B := 1 + ‖L‖ * C
  have hB : 0 < B := by dsimp [B]; positivity
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨δ, (m.factorial : ℝ) * B * D ^ m, hδ, by positivity, ?_⟩
  intro z hz ht hq hX
  let F : Chart → ℝ := fun p => physicalProfile a h b f p - physicalUncutPrefix h b f J p
  have hF : ContDiffOn ℝ ∞ F profilePast := by
    intro p hp
    exact ((physicalProfile_smoothAt ha.strictMono hh hh1 hf b hp.1).sub
      (physicalUncutPrefix_smoothAt hh hh1 hf b J hp.1)).contDiffWithinAt
  have hp : G z ∈ profilePast := ⟨ht, mem_univ _⟩
  have hzpast : z ∈ past := ⟨ht, mem_univ _⟩
  have hc := norm_iteratedFDerivWithin_comp_le (profileDerivative_smooth hF v) hG.contDiffOn
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) profilePast_isOpen.uniqueDiffOn
    past_isOpen.uniqueDiffOn (show MapsTo G past profilePast from fun _ hx => ⟨hx.1, mem_univ _⟩)
    hzpast (C := B * (cartesianChart h z).1 ^ (h * (J + 1) + b - 2 * (m + 1))) (D := D)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i profilePast_isOpen hp]
      calc
        _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ (i + 1) F (G z)‖ :=
          ResidualStability.norm_jet_linear_map_fderiv L profilePast_isOpen hF hp i
        _ ≤ ‖L‖ * (C * (cartesianChart h z).1 ^ (h * (J + 1) + b - 2 * (m + 1))) :=
          mul_le_mul_of_nonneg_left (hb (i + 1) (by omega) (G z) ht hq hX) (norm_nonneg L)
        _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
            (Real.rpow_nonneg (physicalChart_positive hh hh1 ht).le _))
    (fun i hi him => by
      rw [iteratedFDerivWithin_of_isOpen i past_isOpen hzpast]
      exact hDb z hz i hi him)
  rw [iteratedFDerivWithin_of_isOpen m past_isOpen hzpast] at hc
  exact hc.trans_eq (by ring)

theorem derivative_prefix_rate {l : Filter SpaceTime} {a : ℕ → ℕ} {h lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {f : ℕ → Inner → ℝ} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ)
    (ha : AdmissibleScales h f (innerBox lo hi) a)
    (v : Chart) (J M : ℕ) (hM : M + 1 ≤ J + 3) :
    FiniteJetRate l (fun z => (cartesianChart h z).1)
      (cartesianDerivative v (fun p => physicalProfile a h b f p - physicalUncutPrefix h b f J p))
      M (h * (J + 1) + b - 2 * (M + 1)) := by
  have hq := A.positive_small hh hh1
  apply finiteJetRate_of_jetRate (hq.mono (fun _ hx => hx.1))
  intro m hm
  obtain ⟨δ, C, hδ, hC, hb⟩ := derivative_fixed_prefix_bound hh hh1 hf lo hi b ha A.compact v
    J m (by omega)
  have hr : JetRate l (fun z => (cartesianChart h z).1)
      (cartesianDerivative v (fun p => physicalProfile a h b f p - physicalUncutPrefix h b f J p))
      m (h * (J + 1) + b - 2 * (m + 1)) := by
    refine ⟨C, hC.le, ?_⟩
    filter_upwards [A.in_carrier, A.past, A.radial, A.small hδ] with z hz ht hX hsmall
    exact hb z hz ht hsmall hX
  apply hr.weaken hq
  have hmR : (m : ℝ) ≤ M := by exact_mod_cast hm
  linarith

end ProfileDerivatives

section AnnularFactors

open ProblemStatement DiagonalResidual

/-- Annular past, given by `{z | z.1 < 1 ∧ 0 < AxisymmetricFields.radialEnergy z.2}`. -/
noncomputable def annularPast : Set SpaceTime :=
  {z | z.1 < 1 ∧ 0 < AxisymmetricFields.radialEnergy z.2}

theorem annularPast_isOpen : IsOpen annularPast :=
  (isOpen_lt continuous_fst continuous_const).inter
    (isOpen_lt continuous_const
      ((AxisymmetricFields.contDiff_radialEnergy (n := ∞)).continuous.comp continuous_snd))

theorem annularPast_subset : annularPast ⊆ past := fun _ hz => ⟨hz.1, mem_univ _⟩

theorem PhysicalApproach.in_annularPast {l : Filter SpaceTime} {h lo hi : ℝ}
    (A : PhysicalApproach l h lo hi) (hh : 0 < h) (hh1 : h < 1 / 2) (hlo : 0 < lo) :
    ∀ᶠ z in l, z ∈ annularPast := by
  filter_upwards [A.past, A.radial] with z ht hX
  refine ⟨ht, ?_⟩
  have hq := physicalChart_positive hh hh1 (p := AxisymmetricFields.profilePoint z.1 z.2) ht
  have hx : 0 < (cartesianChart h z).2.1 := hlo.trans_le hX.1
  change 0 < (AxisymmetricFields.profilePoint z.1 z.2).2.1
  rw [← SlowExpansionResidual.q_mul_X hh hh1 ht]
  exact mul_pos hq hx

theorem monomial_finiteRate_on {l : Filter SpaceTime} {h lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {U : Set Inner} (hU : IsOpen U) (hKU : innerBox lo hi ⊆ U)
    {f : Inner → ℝ} (hf : ContDiffOn ℝ ∞ f U) (b : ℝ) (M : ℕ) :
    FiniteJetRate l (fun z => (cartesianChart h z).1) (cartesianMonomial h b f) M (b - M) := by
  have hq := A.positive_small hh hh1
  apply finiteJetRate_of_jetRate (hq.mono (fun _ hz => hz.1))
  intro m hm
  obtain ⟨C, hC, hb⟩ := cartesian_monomial_bound_on hh hh1 hU (innerBox_isCompact lo hi)
    hKU hf b lo hi A.compact m
  have hr : JetRate l (fun z => (cartesianChart h z).1) (cartesianMonomial h b f) m (b - m) := by
    refine ⟨C, hC.le, ?_⟩
    filter_upwards [A.in_carrier, A.past, A.radial, hq] with z hz ht hX hqz
    exact hb z hz ht hqz.2 hX (physicalChart_inner_mem hh hh1 ht hX)
  exact hr.weaken hq (sub_le_sub_left (by exact_mod_cast hm) b)

/-- Radial power, given by `(2 * AxisymmetricFields.radialEnergy z.2) ^ c`. -/
noncomputable def radialPower (c : ℝ) (z : SpaceTime) : ℝ :=
  (2 * AxisymmetricFields.radialEnergy z.2) ^ c

theorem radialPower_smooth (c : ℝ) : ContDiffOn ℝ ∞ (radialPower c) annularPast := by
  intro z hz
  exact ((contDiffAt_const.mul (AxisymmetricFields.contDiff_radialEnergy.contDiffAt.comp z
    contDiffAt_snd)).rpow_const_of_ne (show 2 * AxisymmetricFields.radialEnergy z.2 ≠ 0 by
      have := hz.2; positivity)).contDiffWithinAt

theorem radialPower_eq_monomial {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (c : ℝ) {z : SpaceTime} (ht : z.1 < 1) :
    radialPower c z = cartesianMonomial h c (fun w => (2 * w.1) ^ c) z := by
  have hq := SimilarityProfile.q_pos hh hh1 (p := AxisymmetricFields.profilePoint z.1 z.2) ht
  have hX : 0 ≤ (cartesianChart h z).2.1 :=
    div_nonneg (AxisymmetricFields.radialEnergy_nonneg z.2) hq.le
  have hs := SlowExpansionResidual.q_mul_X hh hh1
    (p := AxisymmetricFields.profilePoint z.1 z.2) ht
  change (2 * (AxisymmetricFields.profilePoint z.1 z.2).2.1) ^ c =
    SimilarityProfile.q h (AxisymmetricFields.profilePoint z.1 z.2) ^ c *
      (2 * (cartesianChart h z).2.1) ^ c
  rw [← hs]
  change (2 * (SimilarityProfile.q h (AxisymmetricFields.profilePoint z.1 z.2) *
      (cartesianChart h z).2.1)) ^ c = _
  rw [mul_left_comm 2]
  exact Real.mul_rpow hq.le (by positivity)

theorem radialPower_rate {l : Filter SpaceTime} {h lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi) (hlo : 0 < lo)
    (c : ℝ) (M : ℕ) :
    FiniteJetRate l (fun z => (cartesianChart h z).1) (radialPower c) M (c - M) := by
  let U : Set Inner := {w | 0 < w.1}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_fst
  have hKU : innerBox lo hi ⊆ U := fun w hw => hlo.trans_le hw.1.1
  have hf : ContDiffOn ℝ ∞ (fun w : Inner => (2 * w.1) ^ c) U := by
    intro w hw
    have hwpos : 0 < w.1 := hw
    exact ((contDiffAt_const.mul contDiffAt_fst).rpow_const_of_ne
      (mul_ne_zero (by norm_num) hwpos.ne')).contDiffWithinAt
  have hr := monomial_finiteRate_on hh hh1 A hU hKU hf c M
  apply finiteRate_congr_on hr annularPast_isOpen (A.in_annularPast hh hh1 hlo)
  intro z hz
  exact (radialPower_eq_monomial hh hh1 c hz.1).symm

end AnnularFactors

section StressOperator

open ProblemStatement DiagonalResidual

/-- The manuscript's tangential radial stress operator. -/
noncomputable def stressForce (theta axial : Chart → ℝ) (z : SpaceTime) : Space :=
  SlowResidualMatching.tangentialStressForce theta axial z.1 z.2

/-- Lift profile, given by `F (AxisymmetricFields.profilePoint z.1 z.2)`. -/
noncomputable def liftProfile (F : Chart → ℝ) (z : SpaceTime) : ℝ :=
  F (AxisymmetricFields.profilePoint z.1 z.2)

/-- Stress angular scalar, given by `-2 * (cartesianDerivative (0, (1, 0)) theta z + 2 *
radialPower (-1) z * liftProfile theta z)`. -/
noncomputable def stressAngularScalar (theta : Chart → ℝ) (z : SpaceTime) : ℝ :=
  -2 * (cartesianDerivative (0, (1, 0)) theta z +
    2 * radialPower (-1) z * liftProfile theta z)

/-- Stress axial scalar, given by `-(radialPower (1 / 2) z * cartesianDerivative (0, (1, 0))
axial z + radialPower (-(1 / 2)) z * liftProfile axial z)`. -/
noncomputable def stressAxialScalar (axial : Chart → ℝ) (z : SpaceTime) : ℝ :=
  -(radialPower (1 / 2) z * cartesianDerivative (0, (1, 0)) axial z +
    radialPower (-(1 / 2)) z * liftProfile axial z)

theorem liftProfile_smooth {F : Chart → ℝ} (hF : ContDiffOn ℝ ∞ F profilePast) :
    ContDiffOn ℝ ∞ (liftProfile F) past :=
  hF.comp AxisymmetricFields.contDiff_profilePoint.contDiffOn (fun _ hz => ⟨hz.1, mem_univ _⟩)

theorem stressForce_eq_scalars (theta axial : Chart → ℝ) {z : SpaceTime}
    (hs : 0 < AxisymmetricFields.radialEnergy z.2) :
    stressForce theta axial z =
      potentialFromScalars (stressAngularScalar theta) (stressAxialScalar axial) z := by
  let r := Real.sqrt (2 * AxisymmetricFields.radialEnergy z.2)
  have hr : r ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hr2 : r ^ 2 = 2 * AxisymmetricFields.radialEnergy z.2 := Real.sq_sqrt (by positivity)
  have hp : radialPower (1 / 2) z = r := (Real.sqrt_eq_rpow _).symm
  have hn : radialPower (-(1 / 2)) z = r⁻¹ := by
    unfold radialPower
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  have hm : radialPower (-1) z = (r ^ 2)⁻¹ := by
    rw [radialPower, Real.rpow_neg_one, hr2]
  ext i
  fin_cases i <;>
    simp only [stressForce, SlowResidualMatching.tangentialStressForce,
        LeadingStress.radialDivergence,
      stressAngularScalar, stressAxialScalar, potentialFromScalars, hp, hn, hm,
      cartesianDerivative, profileDerivative, liftProfile, SimilarityProfile.partialS,
      AxisymmetricResidual.pack, AxisymmetricFields.profilePoint, coordinateVector,
      PiLp.single_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, Fin.zero_eta, Fin.isValue, ↓reduceIte, one_mul, mul_one]
  all_goals norm_num [Fin.ext_iff]
  all_goals dsimp only [r] at hr hr2 ⊢
  all_goals simp only [Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)] at hr hr2 ⊢
  all_goals field_simp [hr]

theorem stressForce_smooth {theta axial : Chart → ℝ}
    (ht : ContDiffOn ℝ ∞ theta profilePast) (ha : ContDiffOn ℝ ∞ axial profilePast) :
    ContDiffOn ℝ ∞ (stressForce theta axial) annularPast := by
  have htv := (liftProfile_smooth ht).mono annularPast_subset
  have hav := (liftProfile_smooth ha).mono annularPast_subset
  have htd := (cartesianDerivative_smooth ht (0, (1, 0))).mono annularPast_subset
  have had := (cartesianDerivative_smooth ha (0, (1, 0))).mono annularPast_subset
  have hs0 : ContDiffOn ℝ ∞ (stressAngularScalar theta) annularPast :=
    contDiffOn_const.mul (htd.add ((contDiffOn_const.mul (radialPower_smooth (-1))).mul htv))
  have hs1 : ContDiffOn ℝ ∞ (stressAxialScalar axial) annularPast :=
    (((radialPower_smooth (1 / 2)).mul had).add
      ((radialPower_smooth (-(1 / 2))).mul hav)).neg
  apply (potentialFromScalars_smooth hs0 hs1).congr
  intro z hz
  exact stressForce_eq_scalars theta axial hz.2

theorem stressForce_sub {theta axial theta' axial' : Chart → ℝ} {z : SpaceTime}
    (ht : DifferentiableAt ℝ theta (AxisymmetricFields.profilePoint z.1 z.2))
    (ha : DifferentiableAt ℝ axial (AxisymmetricFields.profilePoint z.1 z.2))
    (ht' : DifferentiableAt ℝ theta' (AxisymmetricFields.profilePoint z.1 z.2))
    (ha' : DifferentiableAt ℝ axial' (AxisymmetricFields.profilePoint z.1 z.2)) :
    stressForce (fun p => theta p - theta' p) (fun p => axial p - axial' p) z =
      stressForce theta axial z - stressForce theta' axial' z := by
  ext i
  fin_cases i <;>
    simp [stressForce, SlowResidualMatching.tangentialStressForce, LeadingStress.radialDivergence,
      SimilarityProfile.partialS, fderiv_fun_sub ht ht', fderiv_fun_sub ha ha',
      AxisymmetricResidual.pack, coordinateVector] <;> ring

theorem scalarConst_rate {l : Filter SpaceTime} {q : SpaceTime → ℝ}
    {F : SpaceTime → ℝ} {U : Set SpaceTime} {M : ℕ} {r : ℝ}
    (hF : FiniteJetRate l q F M r) (hU : IsOpen U) (hlU : ∀ᶠ z in l, z ∈ U)
    (hs : ContDiffOn ℝ ∞ F U) (c : ℝ) :
    FiniteJetRate l q (fun z => c * F z) M r :=
  finiteRate_linear hF hU hlU hs (c • ContinuousLinearMap.id ℝ ℝ)

/-- Finite loss for the actual stress differential operator, obtained from
the profile derivative and reciprocal-radius factors. -/
theorem stressForce_rate {l : Filter SpaceTime} {h lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi) (hlo : 0 < lo)
    {theta axial : Chart → ℝ} (ht : ContDiffOn ℝ ∞ theta profilePast)
    (ha : ContDiffOn ℝ ∞ axial profilePast) (M : ℕ) (r : ℝ)
    (htv : FiniteJetRate l (fun z => (cartesianChart h z).1) (liftProfile theta) M r)
    (hav : FiniteJetRate l (fun z => (cartesianChart h z).1) (liftProfile axial) M r)
    (htd : FiniteJetRate l (fun z => (cartesianChart h z).1)
      (cartesianDerivative (0, (1, 0)) theta) M r)
    (had : FiniteJetRate l (fun z => (cartesianChart h z).1)
      (cartesianDerivative (0, (1, 0)) axial) M r) :
    FiniteJetRate l (fun z => (cartesianChart h z).1) (stressForce theta axial)
      M (r - 1 - M) := by
  have hq := A.positive_small hh hh1
  have hq0 := hq.mono (fun _ hx => hx.1)
  have hU := annularPast_isOpen
  have hlU := A.in_annularPast hh hh1 hlo
  have hts := (liftProfile_smooth ht).mono annularPast_subset
  have has := (liftProfile_smooth ha).mono annularPast_subset
  have htds := (cartesianDerivative_smooth ht (0, (1, 0))).mono annularPast_subset
  have hads := (cartesianDerivative_smooth ha (0, (1, 0))).mono annularPast_subset
  have hr0 := radialPower_rate hh hh1 A hlo (-1) M
  have hrp := finiteRate_weaken (radialPower_rate hh hh1 A hlo (1 / 2) M) hq
    (show -1 - (M : ℝ) ≤ 1 / 2 - M by linarith)
  have hrn := finiteRate_weaken (radialPower_rate hh hh1 A hlo (-(1 / 2)) M) hq
    (show -1 - (M : ℝ) ≤ -(1 / 2) - M by linarith)
  have hpt := finiteRate_bilinear hr0 htv hU hlU hq0 (radialPower_smooth (-1)) hts
    (ContinuousLinearMap.mul ℝ ℝ)
  have hpa := finiteRate_bilinear hrp had hU hlU hq0 (radialPower_smooth (1 / 2)) hads
    (ContinuousLinearMap.mul ℝ ℝ)
  have hqa := finiteRate_bilinear hrn hav hU hlU hq0 (radialPower_smooth (-(1 / 2))) has
    (ContinuousLinearMap.mul ℝ ℝ)
  have hexp : -1 - (M : ℝ) + r = r - 1 - M := by ring
  rw [hexp] at hpt hpa hqa
  have hpt2 := scalarConst_rate hpt hU hlU ((radialPower_smooth (-1)).mul hts) 2
  have hdt := finiteRate_weaken htd hq (show r - 1 - M ≤ r by
    have := Nat.cast_nonneg (α := ℝ) M; linarith)
  have hs0 := scalarConst_rate (finiteRate_add hdt hpt2 hU hlU htds
    (contDiffOn_const.mul ((radialPower_smooth (-1)).mul hts))) hU hlU
    (htds.add (contDiffOn_const.mul ((radialPower_smooth (-1)).mul hts))) (-2)
  have hs1 := scalarConst_rate (finiteRate_add hpa hqa hU hlU
    ((radialPower_smooth (1 / 2)).mul hads) ((radialPower_smooth (-(1 / 2))).mul has)) hU hlU
    (((radialPower_smooth (1 / 2)).mul hads).add ((radialPower_smooth (-(1 / 2))).mul has)) (-1)
  have hsc0 : ContDiffOn ℝ ∞ (stressAngularScalar theta) annularPast :=
    contDiffOn_const.mul (htds.add ((contDiffOn_const.mul (radialPower_smooth (-1))).mul hts))
  have hsc1 : ContDiffOn ℝ ∞ (stressAxialScalar axial) annularPast :=
    (((radialPower_smooth (1 / 2)).mul hads).add ((radialPower_smooth (-(1 / 2))).mul has)).neg
  have hs0' : FiniteJetRate l (fun z => (cartesianChart h z).1) (stressAngularScalar theta)
      M (r - 1 - M) := by
        convert! hs0 using 1
        funext z
        change -2 * (_ + 2 * radialPower (-1) z * liftProfile theta z) = -2 * (_ + 2 * (_ * _))
        ring
  have hs1' : FiniteJetRate l (fun z => (cartesianChart h z).1) (stressAxialScalar axial)
      M (r - 1 - M) := by
    simp only [neg_one_mul] at hs1 ⊢
    exact hs1
  have hb := potentialFromScalars_rate hU hlU hq0 A.compact A.in_carrier hsc0 hsc1 hs0' hs1'
  apply finiteRate_congr_on hb hU hlU
  intro z hz
  exact (stressForce_eq_scalars theta axial hz.2).symm

end StressOperator

section StressPrefix

open ProblemStatement DiagonalResidual

/-- Prefix stress theta, given by `physicalUncutPrefix h (-CoordinateAlgebra.A h - 1 / 2)
(bundleComponent C d 3) J`. -/
noncomputable def prefixStressTheta (J : ℕ) (h C : ℝ) (d : Coefficients) : Chart → ℝ :=
  physicalUncutPrefix h (-CoordinateAlgebra.A h - 1 / 2) (bundleComponent C d 3) J

/-- Prefix stress axial, given by `physicalUncutPrefix h (-CoordinateAlgebra.A h - 1 / 2)
(bundleComponent C d 4) J`. -/
noncomputable def prefixStressAxial (J : ℕ) (h C : ℝ) (d : Coefficients) : Chart → ℝ :=
  physicalUncutPrefix h (-CoordinateAlgebra.A h - 1 / 2) (bundleComponent C d 4) J

/-- Base stress force, given by `stressForce (baseStressTheta a h C d) (baseStressAxial a h C
d)`. -/
noncomputable def baseStressForce (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : VelocityField :=
  stressForce (baseStressTheta a h C d) (baseStressAxial a h C d)

/-- Prefix stress force, given by `stressForce (prefixStressTheta J h C d) (prefixStressAxial J
h C d)`. -/
noncomputable def prefixStressForce (J : ℕ) (h C : ℝ) (d : Coefficients) : VelocityField :=
  stressForce (prefixStressTheta J h C d) (prefixStressAxial J h C d)

theorem prefixProfile_smooth {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : ℕ → Inner → ℝ} (hf : ∀ j, ContDiff ℝ ∞ (f j)) (J : ℕ) :
    ContDiffOn ℝ ∞ (physicalUncutPrefix h b f J) profilePast :=
  fun _p hp => (physicalUncutPrefix_smoothAt hh hh1 hf b J hp.1).contDiffWithinAt

theorem baseStressForce_smooth {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (baseStressForce a h C d) annularPast :=
  stressForce_smooth (physicalProfile_smoothOn ha hh hh1 (bundleComponent_smooth hd C 3) _)
    (physicalProfile_smoothOn ha hh hh1 (bundleComponent_smooth hd C 4) _)

theorem prefixStressForce_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ) :
    ContDiffOn ℝ ∞ (prefixStressForce J h C d) annularPast :=
  stressForce_smooth (prefixProfile_smooth hh hh1 (bundleComponent_smooth hd C 3) J)
    (prefixProfile_smooth hh hh1 (bundleComponent_smooth hd C 4) J)

/-- The stress tail is passed through the actual cylindrical operator. No
force-tail estimate is assumed. -/
theorem stress_prefix_rate {l : Filter SpaceTime} {a : ℕ → ℕ} {h C lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi) (hlo : 0 < lo)
    {d : Coefficients} (hd : SmoothCoefficients d)
    (ha : AdmissibleScales h (coefficientBundle C d) (innerBox lo hi) a)
    (J M : ℕ) (hM : M + 1 ≤ J + 3) :
    FiniteJetRate l (fun z => (cartesianChart h z).1)
      (fun z => baseStressForce a h C d z - prefixStressForce J h C d z)
      M (h * (J + 1) - CoordinateAlgebra.A h - 1 / 2 - 3 * (M + 1)) := by
  let b := -CoordinateAlgebra.A h - 1 / 2
  let ft := bundleComponent C d 3
  let fa := bundleComponent C d 4
  let T : Chart → ℝ := fun p => physicalProfile a h b ft p - physicalUncutPrefix h b ft J p
  let Z : Chart → ℝ := fun p => physicalProfile a h b fa p - physicalUncutPrefix h b fa J p
  have hts : ContDiffOn ℝ ∞ T profilePast :=
    (physicalProfile_smoothOn ha.strictMono hh hh1 (bundleComponent_smooth hd C 3) b).sub
      (prefixProfile_smooth hh hh1 (bundleComponent_smooth hd C 3) J)
  have hzs : ContDiffOn ℝ ∞ Z profilePast :=
    (physicalProfile_smoothOn ha.strictMono hh hh1 (bundleComponent_smooth hd C 4) b).sub
      (prefixProfile_smooth hh hh1 (bundleComponent_smooth hd C 4) J)
  have hq := A.positive_small hh hh1
  have ht0 := cartesian_prefix_finiteJetRate hh hh1 A (bundleComponent_smooth hd C 3) b
    (admissible_component hd ha 3) J M (by omega)
  have hz0 := cartesian_prefix_finiteJetRate hh hh1 A (bundleComponent_smooth hd C 4) b
    (admissible_component hd ha 4) J M (by omega)
  have ht1 := derivative_prefix_rate hh hh1 A (bundleComponent_smooth hd C 3) b
    (admissible_component hd ha 3) (0, (1, 0)) J M hM
  have hz1 := derivative_prefix_rate hh hh1 A (bundleComponent_smooth hd C 4) b
    (admissible_component hd ha 4) (0, (1, 0)) J M hM
  have hr := stressForce_rate hh hh1 A hlo hts hzs M (h * (J + 1) + b - 2 * (M + 1))
    (finiteRate_weaken ht0 hq (by linarith)) (finiteRate_weaken hz0 hq (by linarith)) ht1 hz1
  have he : h * (J + 1) + b - 2 * ((M : ℝ) + 1) - 1 - M =
      h * (J + 1) - CoordinateAlgebra.A h - 1 / 2 - 3 * (M + 1) := by dsimp [b]; ring
  rw [he] at hr
  apply finiteRate_congr_on hr annularPast_isOpen (A.in_annularPast hh hh1 hlo)
  intro z hz
  apply stressForce_sub
  · exact (physicalProfile_smoothAt ha.strictMono hh hh1 (bundleComponent_smooth hd C 3) b
      (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1).differentiableAt (by simp)
  · exact (physicalProfile_smoothAt ha.strictMono hh hh1 (bundleComponent_smooth hd C 4) b
      (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1).differentiableAt (by simp)
  · exact (physicalUncutPrefix_smoothAt hh hh1 (bundleComponent_smooth hd C 3) b J
      (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1).differentiableAt (by simp)
  · exact (physicalUncutPrefix_smoothAt hh hh1 (bundleComponent_smooth hd C 4) b J
      (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1).differentiableAt (by simp)

end StressPrefix

section FiniteTailRates

open ProblemStatement DiagonalResidual SlowExpansionResidual SlowResidualMatching

/-- Charted domain, given by `{z | z.1 < 1 ∧ (cartesianChart h z).2 ∈ U}`. -/
noncomputable def chartedDomain (h : ℝ) (U : Set Inner) : Set SpaceTime :=
  {z | z.1 < 1 ∧ (cartesianChart h z).2 ∈ U}

theorem chartedDomain_isOpen {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {U : Set Inner} (hU : IsOpen U) : IsOpen (chartedDomain h U) :=
  (SimilarityProfile.isOpen_physicalDomain hh hh1 hU).preimage
    (AxisymmetricFields.contDiff_profilePoint (n := ∞)).continuous

theorem PhysicalApproach.in_chartedDomain {l : Filter SpaceTime} {h lo hi : ℝ}
    (A : PhysicalApproach l h lo hi) (hh : 0 < h) (hh1 : h < 1 / 2)
    {U : Set Inner} (hU : innerBox lo hi ⊆ U) :
    ∀ᶠ z in l, z ∈ chartedDomain h U := by
  filter_upwards [A.past, A.radial] with z ht hX
  exact ⟨ht, hU (physicalChart_inner_mem hh hh1 ht hX)⟩

theorem monomial_smoothOn {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {U : Set Inner} (hU : IsOpen U) {f : Inner → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (cartesianMonomial h b f) (chartedDomain h U) := by
  intro z hz
  exact (cartesianMonomial_smoothAt hh hh1 hz.1
    (hf.contDiffAt (hU.mem_nhds hz.2))).contDiffWithinAt

theorem finset_monomial_rate {l : Filter SpaceTime} {h lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {U : Set Inner} (hU : IsOpen U) (hKU : innerBox lo hi ⊆ U)
    {ι : Type*} (s : Finset ι) (f : ι → Inner → ℝ) (b : ι → ℝ) (bmin : ℝ)
    (hf : ∀ i ∈ s, ContDiffOn ℝ ∞ (f i) U) (hmin : ∀ i ∈ s, bmin ≤ b i) (M : ℕ) :
    FiniteJetRate l (fun z => (cartesianChart h z).1)
      (fun z => ∑ i ∈ s, cartesianMonomial h (b i) (f i) z) M (bmin - M) := by
  classical
  have hq := A.positive_small hh hh1
  apply finiteJetRate_of_jetRate (hq.mono (fun _ hz => hz.1))
  intro m hm
  obtain ⟨C, hC, hb⟩ := cartesian_finite_monomials_bound hh hh1 hU
    (innerBox_isCompact lo hi) hKU (fun i : s => f i) (fun i => hf i i.2)
    (fun i => b i) bmin lo hi (fun i => hmin i i.2) A.compact m
  have hr : JetRate l (fun z => (cartesianChart h z).1)
      (fun z => ∑ i : s, cartesianMonomial h (b i) (f i) z) m (bmin - m) := by
    refine ⟨C, hC.le, ?_⟩
    filter_upwards [A.in_carrier, A.past, A.radial, hq] with z hz ht hX hqz
    exact hb z hz ht hqz.2 hX (physicalChart_inner_mem hh hh1 ht hX)
  have he : (fun z => ∑ i : s, cartesianMonomial h (b i) (f i) z) =
      (fun z => ∑ i ∈ s, cartesianMonomial h (b i) (f i) z) := by
    funext z
    exact Finset.sum_coe_sort s (fun i : ι => cartesianMonomial h (b i) (f i) z)
  rw [he] at hr
  exact hr.weaken hq (sub_le_sub_left (by exact_mod_cast hm) bmin)

/-- Radial vector, given by `z.2 0 • coordinateVector 0 + z.2 1 • coordinateVector 1`. -/
noncomputable def radialVector (z : SpaceTime) : Space :=
  z.2 0 • coordinateVector 0 + z.2 1 • coordinateVector 1

/-- Angular vector, given by `-z.2 1 • coordinateVector 0 + z.2 0 • coordinateVector 1`. -/
noncomputable def angularVector (z : SpaceTime) : Space :=
  -z.2 1 • coordinateVector 0 + z.2 0 • coordinateVector 1

theorem radialVector_smooth : ContDiff ℝ ∞ radialVector :=
  (((AxisymmetricFields.projection 0).contDiff.comp contDiff_snd).smul contDiff_const).add
    (((AxisymmetricFields.projection 1).contDiff.comp contDiff_snd).smul contDiff_const)

theorem angularVector_smooth : ContDiff ℝ ∞ angularVector :=
  ((((AxisymmetricFields.projection 1).contDiff.comp contDiff_snd).neg).smul contDiff_const).add
    (((AxisymmetricFields.projection 0).contDiff.comp contDiff_snd).smul contDiff_const)

/-- Assemble components, given by `R z • radialVector z + A z • angularVector z + Z z •
coordinateVector 2`. -/
noncomputable def assembleComponents (R A Z : SpaceTime → ℝ) (z : SpaceTime) : Space :=
  R z • radialVector z + A z • angularVector z + Z z • coordinateVector 2

theorem assembleComponents_eq_pack (R A Z : SpaceTime → ℝ) (z : SpaceTime) :
    assembleComponents R A Z z =
      AxisymmetricResidual.pack (z.2 0 * R z - z.2 1 * A z)
        (z.2 1 * R z + z.2 0 * A z) (Z z) := by
  ext i
  fin_cases i <;> simp [assembleComponents, radialVector, angularVector,
    AxisymmetricResidual.pack, coordinateVector] <;> ring

theorem assembleComponents_rate {l : Filter SpaceTime} {q : SpaceTime → ℝ}
    {U B : Set SpaceTime} (hU : IsOpen U) (hlU : ∀ᶠ z in l, z ∈ U)
    (hB : IsCompact B) (hlB : ∀ᶠ z in l, z ∈ B) (hq : ∀ᶠ z in l, 0 < q z)
    {R A Z : SpaceTime → ℝ} (hR : ContDiffOn ℝ ∞ R U) (hA : ContDiffOn ℝ ∞ A U)
    (hZ : ContDiffOn ℝ ∞ Z U) {M : ℕ} {r : ℝ}
    (hrR : FiniteJetRate l q R M r) (hrA : FiniteJetRate l q A M r)
    (hrZ : FiniteJetRate l q Z M r) : FiniteJetRate l q (assembleComponents R A Z) M r := by
  have hr := finiteRate_bilinear hrR (finiteRate_compact (q := q) radialVector_smooth hB hlB M)
    hU hlU hq hR radialVector_smooth.contDiffOn (ContinuousLinearMap.lsmul ℝ ℝ)
  have ha := finiteRate_bilinear hrA (finiteRate_compact (q := q) angularVector_smooth hB hlB M)
    hU hlU hq hA angularVector_smooth.contDiffOn (ContinuousLinearMap.lsmul ℝ ℝ)
  simp only [add_zero] at hr ha
  have hz := finiteRate_linear hrZ hU hlU hZ (basisInjection 2)
  exact finiteRate_add (finiteRate_add hr ha hU hlU (hR.smul radialVector_smooth.contDiffOn)
    (hA.smul angularVector_smooth.contDiffOn)) hz hU hlU
      ((hR.smul radialVector_smooth.contDiffOn).add (hA.smul angularVector_smooth.contDiffOn))
      (hZ.smul contDiffOn_const)

/-- Transport tail field, given by `transportTail N (cartesianChart h z).1 h e α v u f
(cartesianChart h z).2`. -/
noncomputable def transportTailField (N : ℕ) (h e α : ℝ)
    (v u f : ℕ → Inner → ℝ) (z : SpaceTime) : ℝ :=
  transportTail N (cartesianChart h z).1 h e α v u f (cartesianChart h z).2

/-- Radial tail field, given by `pressureTail N (cartesianChart h z).1 h C f (cartesianChart h
z).2 / (2 * AxisymmetricFields.radialEnergy z.2)`. -/
noncomputable def radialTailField (N : ℕ) (h C : ℝ) (f : SlowProfiles) (z : SpaceTime) : ℝ :=
  pressureTail N (cartesianChart h z).1 h C f (cartesianChart h z).2 /
    (2 * AxisymmetricFields.radialEnergy z.2)

theorem transportTailField_eq (N : ℕ) (h e α : ℝ) (v u f : ℕ → Inner → ℝ) :
    transportTailField N h e α v u f =
      (fun z => ∑ i ∈ transportIndices N,
        cartesianMonomial h (transportPower N h e i) (transportTerm N h e α v u f i) z) := by
  funext z
  exact transportTail_eq_finite_monomials N (cartesianChart h z).1 h e α v u f (cartesianChart h
      z).2

theorem transportTailField_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {O : Set Inner} (hO : IsOpen O) (N : ℕ) (e α : ℝ) (v u f : ℕ → Inner → ℝ)
    (hv : ∀ j ≤ N, ContDiffOn ℝ ∞ (v j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hf : ∀ j ≤ N, ContDiffOn ℝ ∞ (f j) O)
    (hX : ∀ w ∈ O, w.1 ≠ 0) (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0) :
    ContDiffOn ℝ ∞ (transportTailField N h e α v u f) (chartedDomain h O) := by
  rw [transportTailField_eq]
  exact ContDiffOn.sum (fun i hi => monomial_smoothOn hh hh1 hO
    (transportTerm_smoothOn hO N h e α v u f hv hu hf hX hL hi))

theorem transportTailField_rate {l : Filter SpaceTime} {h lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {O : Set Inner} (hO : IsOpen O) (hKO : innerBox lo hi ⊆ O)
    (N : ℕ) (e α : ℝ) (v u f : ℕ → Inner → ℝ)
    (hv : ∀ j ≤ N, ContDiffOn ℝ ∞ (v j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hf : ∀ j ≤ N, ContDiffOn ℝ ∞ (f j) O)
    (hX : ∀ w ∈ O, w.1 ≠ 0) (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0) (M : ℕ) :
    FiniteJetRate l (fun z => (cartesianChart h z).1) (transportTailField N h e α v u f)
      M (e - 1 + slowOrder h (N + 1) - M) := by
  rw [transportTailField_eq]
  exact finset_monomial_rate hh hh1 A hO hKO (transportIndices N)
    (transportTerm N h e α v u f) (transportPower N h e) (e - 1 + slowOrder h (N + 1))
    (fun _ hi => transportTerm_smoothOn hO N h e α v u f hv hu hf hX hL hi)
    (fun _ hi => transportPower_lower hh.le N e hi) M

end FiniteTailRates

section TruncationRate

open ProblemStatement DiagonalResidual SlowExpansionResidual SlowResidualMatching

/-- Radial tail expression, given by `∑ i ∈ pressureIndices N, cartesianMonomial h
(pressurePower N h i - 1) (fun w => pressureTerm N h C f i w / (2 * w.1)) z`. -/
noncomputable def radialTailExpression (N : ℕ) (h C : ℝ) (f : SlowProfiles) (z : SpaceTime) : ℝ :=
  ∑ i ∈ pressureIndices N, cartesianMonomial h (pressurePower N h i - 1)
    (fun w => pressureTerm N h C f i w / (2 * w.1)) z

theorem radialTailExpression_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (C : ℝ) (f : SlowProfiles) {z : SpaceTime} (hz : z ∈ annularPast) :
    radialTailExpression N h C f z = radialTailField N h C f z :=
  (radialTail_eq_finite_monomials hh hh1 N C f hz.1 hz.2).symm

theorem radialTailExpression_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {O : Set Inner} (hO : IsOpen O) (N : ℕ) (C : ℝ) (f : SlowProfiles)
    (hv : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.flux j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.axial j) O)
    (hf : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.phi j) O)
    (hX : ∀ w ∈ O, w.1 ≠ 0) (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0) :
    ContDiffOn ℝ ∞ (radialTailExpression N h C f) (chartedDomain h O) := by
  apply ContDiffOn.sum
  intro i hi
  apply monomial_smoothOn hh hh1 hO
  exact (pressureTerm_smoothOn hO N h C f hv hu hf hX hL hi).div
    (contDiffOn_const.mul contDiffOn_fst) (fun w hw => mul_ne_zero (by norm_num) (hX w hw))

theorem radialTailExpression_rate {l : Filter SpaceTime} {h lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {O : Set Inner} (hO : IsOpen O) (hKO : innerBox lo hi ⊆ O)
    (N : ℕ) (C : ℝ) (f : SlowProfiles)
    (hv : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.flux j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.axial j) O)
    (hf : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.phi j) O)
    (hX : ∀ w ∈ O, w.1 ≠ 0) (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0) (M : ℕ) :
    FiniteJetRate l (fun z => (cartesianChart h z).1) (radialTailExpression N h C f)
      M (pressureExponent h - 1 + slowOrder h (N + 1) - M) := by
  apply finset_monomial_rate hh hh1 A hO hKO (pressureIndices N)
    (fun i w => pressureTerm N h C f i w / (2 * w.1)) (fun i => pressurePower N h i - 1)
    (pressureExponent h - 1 + slowOrder h (N + 1))
  · intro i hi
    exact (pressureTerm_smoothOn hO N h C f hv hu hf hX hL hi).div
      (contDiffOn_const.mul contDiffOn_fst) (fun w hw => mul_ne_zero (by norm_num) (hX w hw))
  · intro i hi
    have hp := pressurePower_lower hh.le N hi
    linarith

/-- The actual finite residual left by the recurrence has arbitrary
increasing order as the truncation index increases. Its rate is derived
from the explicit omitted monomials, not supplied as a hypothesis. -/
theorem truncationResidual_rate {l : Filter SpaceTime} {h lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi) (hlo : 0 < lo)
    {O : Set Inner} (hO : IsOpen O) (hKO : innerBox lo hi ⊆ O)
    (N : ℕ) (C : ℝ) (f : SlowProfiles)
    (hv : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.flux j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.axial j) O)
    (hf : ∀ j ≤ N, ContDiffOn ℝ ∞ (f.phi j) O)
    (hX : ∀ w ∈ O, w.1 ≠ 0) (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0) (M : ℕ) :
    FiniteJetRate l (fun z => (cartesianChart h z).1)
      (fun z => truncationResidual N h C f z.1 z.2) M (2 * (N : ℝ) * h - 2 - M) := by
  let R := radialTailExpression N h C f
  let F := transportTailField N h (angularExponent h) 1 f.flux f.axial f.phi
  let Z := transportTailField N h (axialExponent h) 0 f.flux f.axial f.axial
  have hW := chartedDomain_isOpen hh hh1 hO
  have hlW := A.in_chartedDomain hh hh1 hKO
  have hq := A.positive_small hh hh1
  have hRs : ContDiffOn ℝ ∞ R (chartedDomain h O) :=
    radialTailExpression_smooth hh hh1 hO N C f hv hu hf hX hL
  have hFs : ContDiffOn ℝ ∞ F (chartedDomain h O) :=
    transportTailField_smooth hh hh1 hO N _ _ _ _ _ hv hu hf hX hL
  have hZs : ContDiffOn ℝ ∞ Z (chartedDomain h O) :=
    transportTailField_smooth hh hh1 hO N _ _ _ _ _ hv hu hu hX hL
  have hR := radialTailExpression_rate hh hh1 A hO hKO N C f hv hu hf hX hL M
  have hF := transportTailField_rate hh hh1 A hO hKO N (angularExponent h) 1
    f.flux f.axial f.phi hv hu hf hX hL M
  have hZ := transportTailField_rate hh hh1 A hO hKO N (axialExponent h) 0
    f.flux f.axial f.axial hv hu hu hX hL M
  obtain ⟨he, heF, heZ⟩ := common_tail_power_lower hh.le N
  have hF' := finiteRate_weaken hF hq (sub_le_sub_right heF (M : ℝ))
  have hZ' := finiteRate_weaken hZ hq (sub_le_sub_right heZ (M : ℝ))
  have hFC := scalarConst_rate hF' hW hlW hFs C⁻¹
  have hr := assembleComponents_rate hW hlW A.compact A.in_carrier
    (hq.mono (fun _ hz => hz.1)) hRs (contDiffOn_const.mul hFs) hZs hR hFC hZ'
  rw [he] at hr
  apply finiteRate_congr_on hr annularPast_isOpen (A.in_annularPast hh hh1 hlo)
  intro z hz
  rw [assembleComponents_eq_pack]
  dsimp only [R]
  rw [radialTailExpression_eq hh hh1 N C f hz]
  rfl

end TruncationRate

section NonlinearAssembly

open ProblemStatement DiagonalResidual ResidualStability SlowExpansionResidual

/-- Base residual, given by `navierStokesResidual (baseVelocity a h C d) (basePressure a h C d)
z.1 z.2 - baseStressForce a h C d z`. -/
noncomputable def baseResidual (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) (z : SpaceTime) : Space :=
  navierStokesResidual (baseVelocity a h C d) (basePressure a h C d) z.1 z.2 -
    baseStressForce a h C d z

theorem baseResidual_identity (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) (z : SpaceTime) :
    navierStokesResidual (baseVelocity a h C d) (basePressure a h C d) z.1 z.2 =
      baseStressForce a h C d z + baseResidual a h C d z := by
  unfold baseResidual
  abel

theorem basePressure_smooth {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (basePressure a h C d) past :=
  cartesianProfile_smooth ha hh hh1 (bundleComponent_smooth hd C 2)

theorem prefixPressure_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ) :
    ContDiffOn ℝ ∞ (prefixPressure J h C d) past :=
  cartesianUncutPrefix_smooth hh hh1 (bundleComponent_smooth hd C 2) J

theorem jetRate_neg {l : Filter SpaceTime} {q : SpaceTime → ℝ} {F : SpaceTime → Space}
    {m : ℕ} {r : ℝ} (hF : JetRate l q F m r) : JetRate l q (fun z => -F z) m r := by
  obtain ⟨C, hC, hb⟩ := hF
  exact ⟨C, hC, hb.mono (fun z hz => by simpa only [norm_jet_neg] using hz)⟩

/-- The finite identity in this interface is the exact identity for the
displayed uncut stream prefixes. It contains no asymptotic hypothesis. -/
def FiniteIdentities (h C : ℝ) (d : Coefficients) (f : SlowProfiles) : Prop :=
  ∀ J : ℕ, ∀ z ∈ annularPast,
    navierStokesResidual (prefixVelocity J h C d) (prefixPressure J h C d) z.1 z.2 =
      prefixStressForce J h C d z + truncationResidual J h C f z.1 z.2

/-- The nonlinear residual estimate for the concrete asymptotic sum. Every
rate used in its proof is derived above from smooth coefficients, the chosen
scales, and the explicit finite identities. -/
theorem baseResidual_jetRate {l : Filter SpaceTime} {a : ℕ → ℕ} {h C lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi) (hlo : 0 < lo)
    {d : Coefficients} (hd : SmoothCoefficients d)
    (ha : AdmissibleScales h (coefficientBundle C d) (innerBox lo hi) a)
    (f : SlowProfiles) {O : Set Inner} (hO : IsOpen O) (hKO : innerBox lo hi ⊆ O)
    (hv : ∀ j, ContDiffOn ℝ ∞ (f.flux j) O)
    (hu : ∀ j, ContDiffOn ℝ ∞ (f.axial j) O)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f.phi j) O)
    (hX : ∀ w ∈ O, w.1 ≠ 0) (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0)
    (hfinite : FiniteIdentities h C d f) (m : ℕ) (n : ℝ) (hn : 0 ≤ n) :
    JetRate l (fun z => (cartesianChart h z).1) (baseResidual a h C d) m n := by
  let b : ℝ := CoordinateAlgebra.A h + m + 2
  have hA : 0 < CoordinateAlgebra.A h := by unfold CoordinateAlgebra.A; linarith
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hb : 0 ≤ b := by dsimp [b]; positivity
  obtain ⟨N, hN⟩ := exists_nat_ge ((n + b + 2 * CoordinateAlgebra.A h + 6 * m + 12) / h)
  let J := max (m + 2) N
  have hJ : m + 2 ≤ J := le_max_left _ _
  have hJN : (N : ℝ) ≤ J := by exact_mod_cast le_max_right (m + 2) N
  have hgain : n + b + 2 * CoordinateAlgebra.A h + 6 * m + 12 ≤ h * ((J : ℝ) + 1) := by
    have hn' := (div_le_iff₀ hh).mp hN
    nlinarith
  have hq := A.positive_small hh hh1
  have hU := annularPast_isOpen
  have hlU := A.in_annularPast hh hh1 hlo
  have hus := (baseVelocity_smooth ha.strictMono hh hh1 hd C).mono annularPast_subset
  have hps := (basePressure_smooth ha.strictMono hh hh1 hd C).mono annularPast_subset
  have huJs := (prefixVelocity_smooth hh hh1 hd J C).mono annularPast_subset
  have hpJs := (prefixPressure_smooth hh hh1 hd J C).mono annularPast_subset
  have htS := baseStressForce_smooth ha.strictMono hh hh1 hd C
  have htJ := prefixStressForce_smooth hh hh1 hd J C
  have hbg : FiniteJetRate l (fun z => (cartesianChart h z).1) (prefixVelocity J h C d)
      (m + 1) (-b) := by
    convert! prefixVelocity_growth (C := C) hh hh1 A hd J (m + 1) using 1
    dsimp [b]
    push_cast
    ring
  have hvel : FiniteJetRate l (fun z => (cartesianChart h z).1)
      (fun z => baseVelocity a h C d z - prefixVelocity J h C d z) (m + 2) (n + b) := by
    apply finiteRate_weaken (velocity_prefix_rate hh hh1 A hd ha J (m + 2) (by omega)) hq
    push_cast
    linarith
  have hpres : FiniteJetRate l (fun z => (cartesianChart h z).1)
      (fun z => basePressure a h C d z - prefixPressure J h C d z) (m + 1) (n + b) := by
    apply finiteRate_weaken (pressure_prefix_rate hh hh1 A hd ha J (m + 1) (by omega)) hq
    push_cast
    linarith
  have hstress : JetRate l (fun z => (cartesianChart h z).1)
      (fun z => baseStressForce a h C d z - prefixStressForce J h C d z) m n := by
    apply (finiteRate_at (stress_prefix_rate hh hh1 A hlo hd ha J m (by omega)) le_rfl).weaken hq
    dsimp [b] at hgain
    linarith
  have htail : JetRate l (fun z => (cartesianChart h z).1)
      (fun z => truncationResidual J h C f z.1 z.2) m n := by
    apply (finiteRate_at (truncationResidual_rate hh hh1 A hlo hO hKO J C f
      (fun j _ => hv j) (fun j _ => hu j) (fun j _ => hf j) hX hL m) le_rfl).weaken hq
    dsimp [b] at hgain
    linarith
  let EJ : SpaceTime → Space := fun z =>
    navierStokesResidual (prefixVelocity J h C d) (prefixPressure J h C d) z.1 z.2 -
      prefixStressForce J h C d z
  have hEJ : JetRate l (fun z => (cartesianChart h z).1) EJ m n :=
    htail.congr_on hU hlU (fun z hz => by dsimp [EJ]; rw [hfinite J z hz]; abel)
  have hEJs : ContDiffOn ℝ ∞ EJ annularPast :=
    (ResidualRegularity.contDiffOn_residual hU huJs hpJs).sub htJ
  let Df := residualDifference (prefixVelocity J h C d)
    (fun z => baseVelocity a h C d z - prefixVelocity J h C d z)
    (prefixPressure J h C d) (fun z => basePressure a h C d z - prefixPressure J h C d z)
  have hDf : JetRate l (fun z => (cartesianChart h z).1) Df m n :=
    residualDifference_jetRate hU hlU hq huJs (hus.sub huJs) hpJs (hps.sub hpJs)
      m hb hn hbg hvel hpres
  have hDfs : ContDiffOn ℝ ∞ Df annularPast :=
    (ResidualRegularity.contDiffOn_residual hU (huJs.add (hus.sub huJs))
      (hpJs.add (hps.sub hpJs))).sub (ResidualRegularity.contDiffOn_residual hU huJs hpJs)
  have hsum := (hEJ.add hDf hU hlU hEJs hDfs).add (jetRate_neg hstress) hU hlU
    (hEJs.add hDfs) (htS.sub htJ).neg
  have hvelsum : (fun z => prefixVelocity J h C d z +
      (baseVelocity a h C d z - prefixVelocity J h C d z)) = baseVelocity a h C d := by
    funext z
    abel
  have hpressum : (fun z => prefixPressure J h C d z +
      (basePressure a h C d z - prefixPressure J h C d z)) = basePressure a h C d := by
    funext z
    abel
  have heq : (fun z => EJ z + Df z + -(baseStressForce a h C d z - prefixStressForce J h C d z)) =
      baseResidual a h C d := by
    funext z
    simp only [EJ, Df, residualDifference, hvelsum, hpressum, baseResidual]
    abel
  rwa [heq] at hsum

/-- All physical Cartesian space-time jets of the actual nonlinear error
are flat along every fixed compact annular approach to q=0. -/
theorem baseResidual_allJetsFlat {l : Filter SpaceTime} {a : ℕ → ℕ} {h C lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi) (hlo : 0 < lo)
    {d : Coefficients} (hd : SmoothCoefficients d)
    (ha : AdmissibleScales h (coefficientBundle C d) (innerBox lo hi) a)
    (f : SlowProfiles) {O : Set Inner} (hO : IsOpen O) (hKO : innerBox lo hi ⊆ O)
    (hv : ∀ j, ContDiffOn ℝ ∞ (f.flux j) O)
    (hu : ∀ j, ContDiffOn ℝ ∞ (f.axial j) O)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f.phi j) O)
    (hX : ∀ w ∈ O, w.1 ≠ 0) (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0)
    (hfinite : FiniteIdentities h C d f) :
    AllJetsFlat l (fun z => (cartesianChart h z).1) (baseResidual a h C d) := by
  intro m N
  obtain ⟨K, hK, hb⟩ := baseResidual_jetRate hh hh1 A hlo hd ha f hO hKO hv hu hf hX hL
    hfinite m N (Nat.cast_nonneg N)
  refine ⟨K, hK, ?_⟩
  filter_upwards [A.positive_small hh hh1, hb] with z hz hbound
  simpa only [abs_norm, abs_of_pos hz.1, Real.rpow_natCast] using hbound

end NonlinearAssembly

section EdgeJetTools

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Polynomial losses in the two logarithmic edge distances are allowed.
The estimate is on the full derivative tensor, including mixed derivatives. -/
def PolynomialEdgeJets (W : Set Inner) (zeta delta : Inner → ℝ) (f : Inner → V) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ w ∈ W,
    ‖iteratedFDeriv ℝ m f w‖ ≤ C * zeta w * (delta w)⁻¹ ^ N

theorem PolynomialEdgeJets.finite {W : Set Inner} {zeta delta : Inner → ℝ} {f : Inner → V}
    (hf : PolynomialEdgeJets W zeta delta f) (hz : ∀ w ∈ W, 0 ≤ zeta w)
    (hd : ∀ w ∈ W, 0 < delta w ∧ delta w ≤ 1) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ w ∈ W, ∀ m ≤ M,
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * zeta w * (delta w)⁻¹ ^ N := by
  classical
  choose A hA N hAb using hf
  let C := 1 + ∑ i ∈ Finset.range (M + 1), A i
  let J := ∑ i ∈ Finset.range (M + 1), N i
  have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => (hA i).le))
  refine ⟨C, hC, J, fun w hw m hm => ?_⟩
  have hAm : A m ≤ C := by
    have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (M + 1)) => (hA i).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    dsimp [C]
    linarith
  have hNm : N m ≤ J := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (M + 1)) =>
    Nat.zero_le (N i)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  have hinv : 1 ≤ (delta w)⁻¹ := (one_le_inv₀ (hd w hw).1).mpr (hd w hw).2
  exact (hAb m w hw).trans (mul_le_mul
    (mul_le_mul_of_nonneg_right hAm (hz w hw)) (pow_le_pow_right₀ hinv hNm)
    (by positivity) (mul_nonneg hC.le (hz w hw)))

theorem innerLift_blown_le {f : Inner → V} (hf : ContDiff ℝ ∞ f)
    (q : ℝ) (w : Inner) (m : ℕ) :
    ‖blownJet m (fun y : Chart => f y.2) (q, w)‖ ≤ ‖iteratedFDeriv ℝ m f w‖ := by
  let L : Chart →L[ℝ] Inner := ContinuousLinearMap.snd ℝ ℝ Inner
  change ‖iteratedFDeriv ℝ m (f ∘ L) (1, w)‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hf (1, w) (nat_le_infty m)]
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    change ‖y.2‖ ≤ 1 * ‖y‖
    simpa only [one_mul] using norm_snd_le y
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  change ‖iteratedFDeriv ℝ m f w‖ * (∏ _ : Fin m, ‖L‖) ≤ _
  simp only [Finset.prod_const, Finset.card_fin]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)

/-- Positive scale, given by `{y | 0 < y.1}`. -/
noncomputable def positiveScale : Set Chart := {y | 0 < y.1}

theorem positiveScale_isOpen : IsOpen positiveScale := isOpen_lt continuous_const continuous_fst

theorem blown_product_bound {F : Chart → ℝ} {G : Chart → V}
    (hF : ContDiffOn ℝ ∞ F positiveScale) (hG : ContDiffOn ℝ ∞ G positiveScale)
    {q : ℝ} (hq : 0 < q) (w : Inner) (m : ℕ) {A B : ℝ}
    (hA : ∀ k ≤ m, ‖blownJet k F (q, w)‖ ≤ A)
    (hB : ∀ k ≤ m, ‖blownJet k G (q, w)‖ ≤ B) :
    ‖blownJet m (fun y => F y • G y) (q, w)‖ ≤
      ‖ContinuousLinearMap.lsmul ℝ ℝ (E := V)‖ * 2 ^ m * A * B := by
  have hm : MapsTo (scaleMap q) positiveScale positiveScale :=
    fun y hy => mul_pos hq hy
  have hFc := hF.comp (scaleMap q).contDiff.contDiffOn hm
  have hGc := hG.comp (scaleMap q).contDiff.contDiffOn hm
  exact ResidualStability.norm_jet_bilinear_bound (ContinuousLinearMap.lsmul ℝ ℝ)
    positiveScale_isOpen hFc hGc (show (1, w) ∈ positiveScale by norm_num [positiveScale]) m hA hB

theorem slowSum_zero_leading_finite_bound {a : ℕ → ℕ} {h : ℝ}
    (hh : 0 < h) {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {K : Set Inner} (hK : IsCompact K) (ha : AdmissibleScales h f K a)
    (hzero : f 0 = 0) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ w ∈ K, ∀ m ≤ M,
      ‖blownJet m (slowSum a h f) (q, w)‖ ≤ C * q ^ (2 * h) := by
  classical
  have hb (m : ℕ) := normalized_correction_bound hh hf hK ha m
  simp only [hzero, Pi.zero_apply, sub_zero] at hb
  choose A hA hAb using hb
  let C := 1 + ∑ i ∈ Finset.range (M + 1), A i
  have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => (hA i).le))
  refine ⟨C, hC, fun q hq hq1 w hw m hm => ?_⟩
  have hAm : A m ≤ C := by
    have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (M + 1)) => (hA i).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    dsimp [C]
    linarith
  exact (hAb m q hq hq1 w hw).trans
    (mul_le_mul_of_nonneg_right hAm (Real.rpow_nonneg hq.le _))

/-- First cutoff, given by `powerStage (a 1) (2 * h) (fun _ => 1)`. -/
noncomputable def firstCutoff (a : ℕ → ℕ) (h : ℝ) : Chart → ℝ :=
  powerStage (a 1) (2 * h) (fun _ => 1)

theorem firstCutoff_finite_bound (a : ℕ → ℕ) (h : ℝ) {K : Set Inner}
    (hK : IsCompact K) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → ∀ w ∈ K, ∀ m ≤ M,
      ‖blownJet m (firstCutoff a h) (q, w)‖ ≤ C * q ^ (2 * h) := by
  classical
  have hb (m : ℕ) := exists_stage_blown_power_bound
    (f := fun _ (_ : Inner) => (1 : ℝ)) (fun _ => contDiff_const) hK a h 1 m
  simp only [slowStage_eq (by norm_num : (1 : ℕ) ≠ 0), Nat.cast_one, mul_one] at hb
  choose A hA hAb using hb
  let C := 1 + ∑ i ∈ Finset.range (M + 1), A i
  have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => (hA i).le))
  refine ⟨C, hC, fun q hq w hw m hm => ?_⟩
  have hAm : A m ≤ C := by
    have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (M + 1)) => (hA i).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    dsimp [C]
    linarith
  exact (hAb m q hq w hw).trans (mul_le_mul_of_nonneg_right hAm (Real.rpow_nonneg hq.le _))

end EdgeJetTools

section WeightedSum

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem slowSum_split_first {a : ℕ → ℕ} (ha : StrictMono a) (h : ℝ)
    (f g : ℕ → Inner → V) (zeta : Inner → ℝ) (hg0 : g 0 = 0) (hg1 : g 1 = 0)
    {O : Set Inner} (hfg : ∀ j, 2 ≤ j → ∀ w ∈ O, f j w = zeta w • g j w)
    {q : ℝ} (hq : 0 < q) {w : Inner} (hw : w ∈ O) :
    slowSum a h f (q, w) - f 0 w =
      firstCutoff a h (q, w) • f 1 w + zeta w • slowSum a h g (q, w) := by
  have hsG : Summable (fun j => slowStage a h g j (q, w)) :=
    SolenoidalDiagonal.summable_cutStage (SolenoidalDiagonal.realScales_tendsto ha)
      continuous_fst.continuousAt hq (positiveCoefficient h g)
  have hs1 : Summable (fun j : ℕ => if j = 1 then firstCutoff a h (q, w) • f 1 w else 0) := by
    apply summable_of_ne_finset_zero (s := {1})
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [hj]
  have he (j : ℕ) : slowStage a h f j (q, w) =
      (if j = 1 then firstCutoff a h (q, w) • f 1 w else 0) +
        zeta w • slowStage a h g j (q, w) := by
    by_cases hj0 : j = 0
    · subst j
      simp
    by_cases hj1 : j = 1
    · subst j
      simp [slowStage_eq (by norm_num : (1 : ℕ) ≠ 0), hg1,
        firstCutoff, powerStage, powerCoefficient, smul_smul]
    · rw [slowStage_eq hj0, slowStage_eq hj0, ite_eq_right hj1, zero_add]
      simp only [powerStage, powerCoefficient, hfg j (by omega) w hw, smul_smul]
      congr 1
      ring
  change f 0 w + (∑' j, slowStage a h f j (q, w)) - f 0 w =
    firstCutoff a h (q, w) • f 1 w + zeta w •
      (g 0 w + ∑' j, slowStage a h g j (q, w))
  rw [hg0, Pi.zero_apply, zero_add, tsum_congr he, hs1.tsum_add (hsG.const_smul (zeta w)),
    hsG.tsum_const_smul]
  simp

theorem blown_add_bound {F G : Chart → V}
    (hF : ContDiffOn ℝ ∞ F positiveScale) (hG : ContDiffOn ℝ ∞ G positiveScale)
    {q : ℝ} (hq : 0 < q) (w : Inner) (m : ℕ) :
    ‖blownJet m (fun y => F y + G y) (q, w)‖ ≤
      ‖blownJet m F (q, w)‖ + ‖blownJet m G (q, w)‖ := by
  have hm : MapsTo (scaleMap q) positiveScale positiveScale := fun y hy => mul_pos hq hy
  exact ResidualStability.norm_jet_add_le positiveScale_isOpen
    (hF.comp (scaleMap q).contDiff.contDiffOn hm) (hG.comp (scaleMap q).contDiff.contDiffOn hm)
    (show (1, w) ∈ positiveScale by norm_num [positiveScale]) m

/-- Weighted summation of the full coefficient vector. The first coefficient
uses polynomial edge bounds; higher coefficients use their genuine smooth
quotients by the flat weight and the explicitly chosen cutoff schedule. -/
theorem weighted_slowSum_bound {a : ℕ → ℕ} {h : ℝ} (hh : 0 < h)
    {f g : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) {K W O : Set Inner}
    (hK : IsCompact K) (hWK : W ⊆ K) (hO : IsOpen O) (hWO : W ⊆ O)
    {zeta delta : Inner → ℝ} (hzs : ContDiff ℝ ∞ zeta)
    (hz : ∀ w ∈ W, 0 ≤ zeta w) (hd : ∀ w ∈ W, 0 < delta w ∧ delta w ≤ 1)
    (hfirst : PolynomialEdgeJets W zeta delta (f 1))
    (hweight : PolynomialEdgeJets W zeta delta zeta)
    (hg0 : g 0 = 0) (hg1 : g 1 = 0)
    (hfg : ∀ j, 2 ≤ j → ∀ w ∈ O, f j w = zeta w • g j w)
    (ha : AdmissibleScales h g K a) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ w ∈ W,
      ‖blownJet m (fun y => slowSum a h f y - f 0 y.2) (q, w)‖ ≤
        C * q ^ h * zeta w * (delta w)⁻¹ ^ N := by
  obtain ⟨Cs, hCs, hsb⟩ := firstCutoff_finite_bound a h hK m
  obtain ⟨Cg, hCg, hgb⟩ := slowSum_zero_leading_finite_bound hh hg hK ha hg0 m
  obtain ⟨C1, hC1, N1, h1b⟩ := hfirst.finite hz hd m
  obtain ⟨Cz, hCz, Nz, hzb⟩ := hweight.finite hz hd m
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := V)
  let B := ‖L‖ * 2 ^ m * (Cs * C1 + Cz * Cg)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B + 1, by positivity, N1 + Nz, fun q hq hq1 w hw => ?_⟩
  let D := (delta w)⁻¹ ^ (N1 + Nz)
  have hdw := hd w hw
  have hdp : 0 < delta w := hdw.1
  have hzw := hz w hw
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hi : 1 ≤ (delta w)⁻¹ := (one_le_inv₀ (hd w hw).1).mpr (hd w hw).2
  have hN1 : (delta w)⁻¹ ^ N1 ≤ D := pow_le_pow_right₀ hi (Nat.le_add_right _ _)
  have hNz : (delta w)⁻¹ ^ Nz ≤ D := pow_le_pow_right₀ hi (Nat.le_add_left _ _)
  let F : Chart → V := fun y => firstCutoff a h y • f 1 y.2
  let G : Chart → V := fun y => zeta y.2 • slowSum a h g y
  have hs : ContDiffOn ℝ ∞ (firstCutoff a h) positiveScale := by
    intro y hy
    exact (powerStage_smoothAt contDiff_const (a 1) (2 * h) hy).contDiffWithinAt
  have hF : ContDiffOn ℝ ∞ F positiveScale :=
    hs.smul ((hf 1).comp contDiff_snd).contDiffOn
  have hG : ContDiffOn ℝ ∞ G positiveScale :=
    (hzs.comp contDiff_snd).contDiffOn.smul (slowSum_smoothOn ha.strictMono hg h)
  have hFbound : ‖blownJet m F (q, w)‖ ≤ ‖L‖ * 2 ^ m * (Cs * q ^ (2 * h)) * (C1 * zeta w * D) := by
    apply blown_product_bound hs ((hf 1).comp contDiff_snd).contDiffOn hq w m
    · exact fun k hk => hsb q hq w (hWK hw) k hk
    · intro k hk
      exact (innerLift_blown_le (hf 1) q w k).trans ((h1b w hw k hk).trans
        (mul_le_mul_of_nonneg_left hN1 (mul_nonneg hC1.le (hz w hw))))
  have hGbound : ‖blownJet m G (q, w)‖ ≤ ‖L‖ * 2 ^ m * (Cz * zeta w * D) * (Cg * q ^ (2 * h)) := by
    apply blown_product_bound (hzs.comp contDiff_snd).contDiffOn (slowSum_smoothOn ha.strictMono hg
        h) hq w m
    · intro k hk
      exact (innerLift_blown_le hzs q w k).trans ((hzb w hw k hk).trans
        (mul_le_mul_of_nonneg_left hNz (mul_nonneg hCz.le (hz w hw))))
    · exact fun k hk => hgb q hq hq1 w (hWK hw) k hk
  have he : (fun y => slowSum a h f y - f 0 y.2) =ᶠ[𝓝 (q, w)] (fun y => F y + G y) := by
    filter_upwards [(positiveScale_isOpen.inter
      (hO.preimage continuous_snd)).mem_nhds ⟨hq, hWO hw⟩] with y hy
    exact slowSum_split_first ha.strictMono h f g zeta hg0 hg1 hfg hy.1 hy.2
  have hmap : Tendsto (scaleMap q) (𝓝 (1, w)) (𝓝 (q, w)) := by
    simpa only [ContinuousAt, scaleMap_apply, mul_one] using
      (scaleMap q).continuous.continuousAt (x := (1, w))
  have hec := he.comp_tendsto hmap
  have hj : blownJet m (fun y => slowSum a h f y - f 0 y.2) (q, w) =
      blownJet m (fun y => F y + G y) (q, w) := by
    exact (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
      (show ((fun y => slowSum a h f y - f 0 y.2) ∘ scaleMap q) =ᶠ[𝓝 (1, w)]
          ((fun y => F y + G y) ∘ scaleMap q) from by
        simpa only [scaleMap_apply, mul_one] using hec) m).self_of_nhds
  rw [hj]
  have hpow : q ^ (2 * h) ≤ q ^ h :=
    Real.rpow_le_rpow_of_exponent_ge hq hq1 (by linarith)
  calc
    _ ≤ ‖blownJet m F (q, w)‖ + ‖blownJet m G (q, w)‖ := blown_add_bound hF hG hq w m
    _ ≤ ‖L‖ * 2 ^ m * (Cs * q ^ (2 * h)) * (C1 * zeta w * D) +
        ‖L‖ * 2 ^ m * (Cz * zeta w * D) * (Cg * q ^ (2 * h)) := add_le_add hFbound hGbound
    _ = B * q ^ (2 * h) * zeta w * D := by dsimp [B]; ring
    _ ≤ (B + 1) * q ^ h * zeta w * D := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) hpow
          (Real.rpow_nonneg hq.le _) (by positivity)) hzw) hD
    _ = _ := rfl

end WeightedSum

section WeightedTensor

/-- Both independent slots of the virtual tangential tensor. -/
noncomputable def stressPair (d : Coefficients) (j : ℕ) (w : Inner) : Inner :=
  (d.stressTheta j w, d.stressAxial j w)

theorem stressPair_smooth {d : Coefficients} (hd : SmoothCoefficients d) (j : ℕ) :
    ContDiff ℝ ∞ (stressPair d j) := (hd.stressTheta j).prodMk (hd.stressAxial j)

/-- Higher stress quotient, with branches according to `j ≤ 1`. -/
noncomputable def higherStressQuotient (d : Coefficients) (zeta : Inner → ℝ)
    (j : ℕ) (w : Inner) : Inner :=
  if j ≤ 1 then 0 else (zeta w)⁻¹ • stressPair d j w

@[simp] theorem higherStressQuotient_zero (d : Coefficients) (zeta : Inner → ℝ) :
    higherStressQuotient d zeta 0 = 0 := by funext w; simp [higherStressQuotient]

@[simp] theorem higherStressQuotient_one (d : Coefficients) (zeta : Inner → ℝ) :
    higherStressQuotient d zeta 1 = 0 := by funext w; simp [higherStressQuotient]

theorem higherStressQuotient_factor (d : Coefficients) (zeta : Inner → ℝ)
    {j : ℕ} (hj : 2 ≤ j) {w : Inner} (hz : zeta w ≠ 0) :
    stressPair d j w = zeta w • higherStressQuotient d zeta j w := by
  simp [higherStressQuotient, show ¬j ≤ 1 by omega, smul_smul, hz]

/-- A common enlarged bundle controls the actual base fields and the
higher-order stress quotients by the same cutoff sequence. -/
noncomputable def weightedBundle (C : ℝ) (d : Coefficients) (zeta : Inner → ℝ)
    (j : ℕ) (w : Inner) : Bundle × Inner :=
  (coefficientBundle C d j w, higherStressQuotient d zeta j w)

theorem weightedBundle_smooth {d : Coefficients} (hd : SmoothCoefficients d)
    {zeta : Inner → ℝ} (hq : ∀ j, ContDiff ℝ ∞ (higherStressQuotient d zeta j))
    (C : ℝ) (j : ℕ) : ContDiff ℝ ∞ (weightedBundle C d zeta j) :=
  (coefficientBundle_smooth hd C j).prodMk (hq j)

theorem weightedBundle_base_scales {a : ℕ → ℕ} {h C : ℝ} {d : Coefficients}
    (hd : SmoothCoefficients d) {zeta : Inner → ℝ}
    (hq : ∀ j, ContDiff ℝ ∞ (higherStressQuotient d zeta j)) {K : Set Inner}
    (ha : AdmissibleScales h (weightedBundle C d zeta) K a) :
    AdmissibleScales h (coefficientBundle C d) K a := by
  exact ha.map (weightedBundle_smooth hd hq C) (ContinuousLinearMap.fst ℝ Bundle Inner)
    (ContinuousLinearMap.norm_fst_le _ _ _)

theorem weightedBundle_quotient_scales {a : ℕ → ℕ} {h C : ℝ} {d : Coefficients}
    (hd : SmoothCoefficients d) {zeta : Inner → ℝ}
    (hq : ∀ j, ContDiff ℝ ∞ (higherStressQuotient d zeta j)) {K : Set Inner}
    (ha : AdmissibleScales h (weightedBundle C d zeta) K a) :
    AdmissibleScales h (higherStressQuotient d zeta) K a := by
  exact ha.map (weightedBundle_smooth hd hq C) (ContinuousLinearMap.snd ℝ Bundle Inner)
    (ContinuousLinearMap.norm_snd_le _ _ _)

/-- Normalized tensor, given by `slowSum a h (stressPair d)`. -/
noncomputable def normalizedTensor (a : ℕ → ℕ) (h : ℝ) (d : Coefficients) : Chart → Inner :=
  slowSum a h (stressPair d)

theorem normalizedTensor_components {a : ℕ → ℕ} (ha : StrictMono a) (h : ℝ)
    (d : Coefficients) {y : Chart} (hy : 0 < y.1) :
    normalizedTensor a h d y = (slowSum a h d.stressTheta y, slowSum a h d.stressAxial y) := by
  apply Prod.ext
  · exact (slowSum_map (ContinuousLinearMap.fst ℝ ℝ ℝ) ha h (stressPair d) hy).symm
  · exact (slowSum_map (ContinuousLinearMap.snd ℝ ℝ ℝ) ha h (stressPair d) hy).symm

/-- Both physical stress slots have exactly the common prefactor used in
the manuscript. The normalized tensor is the actual cut sum. -/
theorem physicalTensor_eq_normalized {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (C : ℝ) (d : Coefficients)
    {p : Chart} (hp : p.1 < 1) :
    (baseStressTheta a h C d p, baseStressAxial a h C d p) =
      (physicalChart h p).1 ^ (-CoordinateAlgebra.A h - 1 / 2) •
        normalizedTensor a h d (physicalChart h p) := by
  rw [normalizedTensor_components ha h d (physicalChart_positive hh hh1 hp)]
  rfl

/-- The full normalized two-slot tensor differs from its leading value by
O(q^h), with the allowed polynomial losses at both flat edges. -/
theorem normalizedTensor_weighted_bound {a : ℕ → ℕ} {h C : ℝ} (hh : 0 < h)
    {d : Coefficients} (hd : SmoothCoefficients d) {K W O : Set Inner}
    (hK : IsCompact K) (hWK : W ⊆ K) (hO : IsOpen O) (hWO : W ⊆ O)
    {zeta delta : Inner → ℝ} (hzs : ContDiff ℝ ∞ zeta)
    (hz : ∀ w ∈ O, 0 < zeta w) (hdelta : ∀ w ∈ W, 0 < delta w ∧ delta w ≤ 1)
    (hfirst : PolynomialEdgeJets W zeta delta (stressPair d 1))
    (hweight : PolynomialEdgeJets W zeta delta zeta)
    (hq : ∀ j, ContDiff ℝ ∞ (higherStressQuotient d zeta j))
    (ha : AdmissibleScales h (weightedBundle C d zeta) K a) (m : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ w ∈ W,
      ‖blownJet m (fun y => normalizedTensor a h d y - stressPair d 0 y.2) (q, w)‖ ≤
        B * q ^ h * zeta w * (delta w)⁻¹ ^ N :=
  weighted_slowSum_bound hh (stressPair_smooth hd) hq hK hWK hO hWO hzs
    (fun w hw => (hz w (hWO hw)).le) hdelta hfirst hweight
    (higherStressQuotient_zero d zeta) (higherStressQuotient_one d zeta)
    (fun _j hj w hw => higherStressQuotient_factor d zeta hj (hz w hw).ne')
    (weightedBundle_quotient_scales hd hq ha) m

/-- The common schedule is constructed from coefficient smoothness. The
weighted estimate is an output, not part of the admissibility assumptions. -/
theorem exists_weighted_base_scales {h : ℝ} (hh : 0 < h) (C : ℝ)
    {d : Coefficients} (hd : SmoothCoefficients d) {K W O : Set Inner}
    (hK : IsCompact K) (hWK : W ⊆ K) (hO : IsOpen O) (hWO : W ⊆ O)
    {zeta delta : Inner → ℝ} (hzs : ContDiff ℝ ∞ zeta)
    (hz : ∀ w ∈ O, 0 < zeta w) (hdelta : ∀ w ∈ W, 0 < delta w ∧ delta w ≤ 1)
    (hfirst : PolynomialEdgeJets W zeta delta (stressPair d 1))
    (hweight : PolynomialEdgeJets W zeta delta zeta)
    (hq : ∀ j, ContDiff ℝ ∞ (higherStressQuotient d zeta j)) (B : ℕ) :
    ∃ a : ℕ → ℕ, B ≤ a 0 ∧ AdmissibleScales h (coefficientBundle C d) K a ∧
      ∀ m : ℕ, ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ w ∈ W,
        ‖blownJet m (fun y => normalizedTensor a h d y - stressPair d 0 y.2) (q, w)‖ ≤
          D * q ^ h * zeta w * (delta w)⁻¹ ^ N := by
  obtain ⟨a, hB, ha⟩ := exists_admissibleScales (weightedBundle_smooth hd hq C) hh hK B
  exact ⟨a, hB, weightedBundle_base_scales hd hq ha,
    normalizedTensor_weighted_bound hh hd hK hWK hO hWO hzs hz hdelta hfirst hweight hq ha⟩

end WeightedTensor

section ConcreteWeight

open ActiveAnnulusWeight

/-- Log weight profile, given by `weight c a b w.2`. -/
noncomputable def logWeightProfile (c a b : ℝ) (w : Inner) : ℝ := weight c a b w.2

/-- Weight left factor, bundling `coefficient`, `order`, `width`, `width_pos` and the required
compatibility proofs. -/
noncomputable def weightLeftFactor {a b c : ℝ} (hab : a < b) (_hc : 0 < c) (K : Set ℝ) :
    EdgeFactor K c (leftChart a (logWeightProfile c a b)) where
  coefficient := fun w => FlatCutoff.edge 4 (b - a - w.2)
  order := 0
  width := b - a
  width_pos := sub_pos.mpr hab
  domain := univ
  domain_open := isOpen_univ
  boundary_mem := subset_univ _
  smooth := ((FlatCutoff.edge_contDiff (by norm_num : (0 : ℝ) < 4)).comp
    (contDiff_const.sub contDiff_snd)).contDiffOn
  boundary_ne_zero := by
    intro p _
    have hp : 0 < FlatCutoff.edge 4 (b - a - (0 : ℝ)) := by
      simpa using (FlatCutoff.edge_pos 4 (sub_pos.mpr hab))
    exact hp.ne'
  identity := by
    intro p hp x hx hxw
    simp only [leftChart, logWeightProfile, weight, pow_zero, div_one, smul_eq_mul]
    rw [show a + x - a = x by ring, show b - (a + x) = b - a - x by ring]

/-- Weight right factor, bundling `coefficient`, `order`, `width`, `width_pos` and the required
compatibility proofs. -/
noncomputable def weightRightFactor {a b c : ℝ} (hab : a < b) (hc : 0 < c) (K : Set ℝ) :
    EdgeFactor K 4 (rightChart b (logWeightProfile c a b)) where
  coefficient := fun w => FlatCutoff.edge c (b - a - w.2)
  order := 0
  width := b - a
  width_pos := sub_pos.mpr hab
  domain := univ
  domain_open := isOpen_univ
  boundary_mem := subset_univ _
  smooth := ((FlatCutoff.edge_contDiff hc).comp (contDiff_const.sub contDiff_snd)).contDiffOn
  boundary_ne_zero := by
    intro p _
    have hp : 0 < FlatCutoff.edge c (b - a - (0 : ℝ)) := by
      simpa using (FlatCutoff.edge_pos c (sub_pos.mpr hab))
    exact hp.ne'
  identity := by
    intro p hp x hx hxw
    simp only [rightChart, logWeightProfile, weight, pow_zero, div_one, smul_eq_mul]
    rw [show b - x - a = b - a - x by ring, show b - (b - x) = x by ring]
    ring

/-- Swap inner, bundling `toLinearEquiv`, `norm_map`. -/
noncomputable def swapInner : Inner ≃ₗᵢ[ℝ] Inner where
  toLinearEquiv := LinearEquiv.prodComm ℝ ℝ ℝ
  norm_map' := by intro w; exact max_comm _ _

/-- Active window, given by `Ioo (Real.exp a) (Real.exp b) ×ˢ Icc (-1) 1`. -/
noncomputable def activeWindow (a b : ℝ) : Set Inner :=
  Ioo (Real.exp a) (Real.exp b) ×ˢ Icc (-1) 1

/-- Active zeta, given by `radialWeight c a b w.1`. -/
noncomputable def activeZeta (c a b : ℝ) (w : Inner) : ℝ := radialWeight c a b w.1

/-- Active delta, given by `edgeDistance a b (Real.log w.1)`. -/
noncomputable def activeDelta (a b : ℝ) (w : Inner) : ℝ := edgeDistance a b (Real.log w.1)

theorem activeZeta_smooth {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    ContDiff ℝ ∞ (activeZeta c a b) := (radialWeight_smooth hc a b).comp contDiff_fst

theorem activeDelta_bounds {a b : ℝ} {w : Inner} (hw : w ∈ activeWindow a b) :
    0 < activeDelta a b w ∧ activeDelta a b w ≤ 1 := by
  have hX := (Real.exp_pos a).trans hw.1.1
  exact ⟨edgeDistance_pos ⟨(Real.lt_log_iff_exp_lt hX).mpr hw.1.1,
    (Real.log_lt_iff_lt_exp hX).mpr hw.1.2⟩, edgeDistance_le_one _ _ _⟩

/-- The actual two-edge Gaussian weight has the polynomial derivative
losses used in the summation theorem. This is derived from its edge factors. -/
theorem activeZeta_edgeJets {a b c : ℝ} (hab : a < b) (hc : 0 < c) :
    PolynomialEdgeJets (activeWindow a b) (activeZeta c a b) (activeDelta a b)
      (activeZeta c a b) := by
  intro m
  have hT : ContDiff ℝ ∞ (logWeightProfile c a b) := (weight_smooth hc a b).comp contDiff_snd
  obtain ⟨C, hC, N, hb⟩ := exists_radial_derivative_bound (E := ℝ) isCompact_Icc
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1)) hab hc isOpen_univ hT.contDiffOn
    (subset_univ _) (weightLeftFactor hab hc (Icc (-1) 1)) (weightRightFactor hab hc (Icc (-1) 1)) m
  refine ⟨C, hC, N, fun w hw => ?_⟩
  have hX := (Real.exp_pos a).trans hw.1.1
  have he : activeZeta c a b =ᶠ[𝓝 w] (radialPullback (logWeightProfile c a b) ∘ swapInner) := by
    filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hX)] with y hy
    simp [activeZeta, radialWeight, hy, radialPullback, logChart, logWeightProfile,
      swapInner]
  rw [(SolenoidalDiagonal.iteratedFDeriv_eventuallyEq he m).self_of_nhds,
    swapInner.norm_iteratedFDeriv_comp_right]
  have hbound := hb w.2 hw.2 w.1 hw.1
  simp only [activeZeta, activeDelta, div_eq_mul_inv, inv_pow] at hbound ⊢
  exact hbound

end ConcreteWeight

section AxisStress

open ProblemStatement DiagonalResidual

/-- A common inner zero region for every actual stress coefficient. -/
def StressZeroCore (d : Coefficients) (r : ℝ) : Prop :=
  ∀ j : ℕ, ∀ X ∈ Ico (0 : ℝ) r, ∀ eta ∈ Icc (-1 : ℝ) 1,
    d.stressTheta j (X, eta) = 0 ∧ d.stressAxial j (X, eta) = 0

theorem slowSum_zero_of_all {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : ℕ → ℕ) (h q : ℝ) {f : ℕ → Inner → V} {w : Inner}
    (hf : ∀ j, f j w = 0) : slowSum a h f (q, w) = 0 := by
  rw [slowSum_eq_leading_of_positive_zero a h q (fun j _ => hf j), hf 0]

theorem physicalProfile_zero_of_all {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : ℕ → ℕ) (h b : ℝ) {f : ℕ → Inner → V} {p : Chart}
    (hf : ∀ j, f j (physicalChart h p).2 = 0) : physicalProfile a h b f p = 0 := by
  unfold physicalProfile
  rw [show slowSum a h f (physicalChart h p) = 0 from slowSum_zero_of_all a h _ hf]
  exact smul_zero _

theorem physicalUncutPrefix_zero_of_all {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h b : ℝ) {f : ℕ → Inner → V} (J : ℕ) {p : Chart}
    (hf : ∀ j, f j (physicalChart h p).2 = 0) : physicalUncutPrefix h b f J p = 0 := by
  simp only [physicalChart_eq] at hf
  simp [physicalUncutPrefix, uncutPrefix_eq_sum, powerCoefficient, hf]

theorem stressForce_zero_at_axis (theta axial : Chart → ℝ) {z : SpaceTime}
    (hs : AxisymmetricFields.radialEnergy z.2 = 0) : stressForce theta axial z = 0 := by
  simp [stressForce, SlowResidualMatching.tangentialStressForce, LeadingStress.radialDivergence,
    AxisymmetricFields.profilePoint, hs, AxisymmetricResidual.pack]

theorem stressForce_zero_core {h r : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {theta axial : Chart → ℝ}
    (htheta : ∀ p : Chart, p.1 < 1 → (physicalChart h p).2.1 ∈ Ioo 0 r → theta p = 0)
    (haxial : ∀ p : Chart, p.1 < 1 → (physicalChart h p).2.1 ∈ Ioo 0 r → axial p = 0)
    {z : SpaceTime} (ht : z.1 < 1) (hX : (cartesianChart h z).2.1 < r) :
    stressForce theta axial z = 0 := by
  by_cases hs : 0 < AxisymmetricFields.radialEnergy z.2
  · let p := AxisymmetricFields.profilePoint z.1 z.2
    have hpX : 0 < (physicalChart h p).2.1 :=
      LeadingStress.inner_X_pos (p := p) hh hh1 ht hs
    let O : Set Inner := Ioo 0 r ×ˢ univ
    have hO : IsOpen O := isOpen_Ioo.prod isOpen_univ
    have hp : p ∈ SimilarityProfile.physicalDomain h O := ⟨ht, ⟨⟨hpX, hX⟩, mem_univ _⟩⟩
    have htheta0 : theta =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [(SimilarityProfile.isOpen_physicalDomain hh hh1 hO).mem_nhds hp] with y hy
      exact htheta y hy.1 hy.2.1
    have haxial0 : axial =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [(SimilarityProfile.isOpen_physicalDomain hh hh1 hO).mem_nhds hp] with y hy
      exact haxial y hy.1 hy.2.1
    have ht0 := htheta0.self_of_nhds
    have ha0 := haxial0.self_of_nhds
    have htd : SimilarityProfile.partialS theta p = 0 := by
      simp [SimilarityProfile.partialS, htheta0.fderiv_eq]
    have had : SimilarityProfile.partialS axial p = 0 := by
      simp [SimilarityProfile.partialS, haxial0.fderiv_eq]
    simp only [stressForce, SlowResidualMatching.tangentialStressForce,
        LeadingStress.radialDivergence]
    change AxisymmetricResidual.pack
      (_ * (Real.sqrt (2 * p.2.1) * SimilarityProfile.partialS theta p + 2 * theta p / _))
      (_ * (Real.sqrt (2 * p.2.1) * SimilarityProfile.partialS theta p + 2 * theta p / _))
      (-(Real.sqrt (2 * p.2.1) * SimilarityProfile.partialS axial p + 1 * axial p / _)) = _
    simp [ht0, ha0, htd, had, AxisymmetricResidual.pack]
  · exact stressForce_zero_at_axis _ _ (le_antisymm (le_of_not_gt hs)
      (AxisymmetricFields.radialEnergy_nonneg z.2))

theorem stressForce_core_germ {h r : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {theta axial : Chart → ℝ}
    (htheta : ∀ p : Chart, p.1 < 1 → (physicalChart h p).2.1 ∈ Ioo 0 r → theta p = 0)
    (haxial : ∀ p : Chart, p.1 < 1 → (physicalChart h p).2.1 ∈ Ioo 0 r → axial p = 0)
    {z : SpaceTime} (ht : z.1 < 1) (hX : (cartesianChart h z).2.1 < r) :
    stressForce theta axial =ᶠ[𝓝 z] (fun _ => 0) := by
  have hO : IsOpen {w : Inner | w.1 < r} := isOpen_lt continuous_fst continuous_const
  filter_upwards [(chartedDomain_isOpen hh hh1 hO).mem_nhds ⟨ht, hX⟩] with y hy
  exact stressForce_zero_core hh hh1 htheta haxial hy.1 hy.2

theorem baseStressForce_core_germ {h r C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (a : ℕ → ℕ) {d : Coefficients} (hc : StressZeroCore d r)
    {z : SpaceTime} (ht : z.1 < 1) (hX : (cartesianChart h z).2.1 < r) :
    baseStressForce a h C d =ᶠ[𝓝 z] (fun _ => 0) := by
  apply stressForce_core_germ hh hh1 (r := r) ?_ ?_ ht hX
  · intro p hp hpx
    have he := (physicalChart_inner_mem hh hh1 hp (show (physicalChart h p).2.1 ∈ Icc 0 r from
      ⟨hpx.1.le, hpx.2.le⟩)).2
    apply physicalProfile_zero_of_all
    intro j
    exact (hc j _ ⟨hpx.1.le, hpx.2⟩ _ he).1
  · intro p hp hpx
    have he := (physicalChart_inner_mem hh hh1 hp (show (physicalChart h p).2.1 ∈ Icc 0 r from
      ⟨hpx.1.le, hpx.2.le⟩)).2
    apply physicalProfile_zero_of_all
    intro j
    exact (hc j _ ⟨hpx.1.le, hpx.2⟩ _ he).2

theorem prefixStressForce_core_germ {h r C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (J : ℕ) {d : Coefficients} (hc : StressZeroCore d r)
    {z : SpaceTime} (ht : z.1 < 1) (hX : (cartesianChart h z).2.1 < r) :
    prefixStressForce J h C d =ᶠ[𝓝 z] (fun _ => 0) := by
  apply stressForce_core_germ hh hh1 (r := r) ?_ ?_ ht hX
  · intro p hp hpx
    have he := (physicalChart_inner_mem hh hh1 hp (show (physicalChart h p).2.1 ∈ Icc 0 r from
      ⟨hpx.1.le, hpx.2.le⟩)).2
    apply physicalUncutPrefix_zero_of_all
    intro j
    exact (hc j _ ⟨hpx.1.le, hpx.2⟩ _ he).1
  · intro p hp hpx
    have he := (physicalChart_inner_mem hh hh1 hp (show (physicalChart h p).2.1 ∈ Icc 0 r from
      ⟨hpx.1.le, hpx.2.le⟩)).2
    apply physicalUncutPrefix_zero_of_all
    intro j
    exact (hc j _ ⟨hpx.1.le, hpx.2⟩ _ he).2

theorem baseStressForce_smooth_past {a : ℕ → ℕ} (ha : StrictMono a) {h r C : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) {d : Coefficients}
    (hd : SmoothCoefficients d) (hc : StressZeroCore d r) :
    ContDiffOn ℝ ∞ (baseStressForce a h C d) past := by
  intro z hz
  by_cases hs : 0 < AxisymmetricFields.radialEnergy z.2
  · exact ((baseStressForce_smooth ha hh hh1 hd C).contDiffAt
      (annularPast_isOpen.mem_nhds ⟨hz.1, hs⟩)).contDiffWithinAt
  · have hs0 := le_antisymm (le_of_not_gt hs) (AxisymmetricFields.radialEnergy_nonneg z.2)
    have hx : (cartesianChart h z).2.1 < r := by
      change AxisymmetricFields.radialEnergy z.2 / _ < r
      simpa only [hs0, zero_div] using hr
    exact (contDiffAt_const.congr_of_eventuallyEq (baseStressForce_core_germ hh hh1 a hc hz.1
        hx)).contDiffWithinAt

theorem prefixStressForce_smooth_past {h r C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hr : 0 < r) {d : Coefficients} (hd : SmoothCoefficients d) (hc : StressZeroCore d r) (J : ℕ) :
    ContDiffOn ℝ ∞ (prefixStressForce J h C d) past := by
  intro z hz
  by_cases hs : 0 < AxisymmetricFields.radialEnergy z.2
  · exact ((prefixStressForce_smooth hh hh1 hd J C).contDiffAt
      (annularPast_isOpen.mem_nhds ⟨hz.1, hs⟩)).contDiffWithinAt
  · have hs0 := le_antisymm (le_of_not_gt hs) (AxisymmetricFields.radialEnergy_nonneg z.2)
    have hx : (cartesianChart h z).2.1 < r := by
      change AxisymmetricFields.radialEnergy z.2 / _ < r
      simpa only [hs0, zero_div] using hr
    exact (contDiffAt_const.congr_of_eventuallyEq (prefixStressForce_core_germ hh hh1 J hc hz.1
        hx)).contDiffWithinAt

end AxisStress

section AxisRateExtension

open ProblemStatement DiagonalResidual

theorem admissible_mono {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a : ℕ → ℕ} {h : ℝ} {f : ℕ → Inner → V} {K K' : Set Inner}
    (ha : AdmissibleScales h f K a) (hK : K' ⊆ K) : AdmissibleScales h f K' a := by
  exact ⟨ha.positive, ha.doubling, ha.strictMono,
    fun j hj m hm q hq hq1 w hw => ha.ordinary j hj m hm q hq hq1 w (hK hw),
    fun j hj m hm q hq hq1 w hw => ha.blown j hj m hm q hq hq1 w (hK hw)⟩

theorem finiteRate_extend_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter SpaceTime} {q : SpaceTime → ℝ} {F : SpaceTime → V} {S : Set SpaceTime}
    {M : ℕ} {r : ℝ} (hF : FiniteJetRate (l ⊓ 𝓟 S) q F M r)
    (hq : ∀ᶠ z in l, 0 < q z)
    (hz : ∀ᶠ z in l, z ∉ S → F =ᶠ[𝓝 z] (fun _ => 0)) : FiniteJetRate l q F M r := by
  obtain ⟨C, hC, hb⟩ := hF
  have hb' := Filter.eventually_inf_principal.mp hb
  refine ⟨C, hC, ?_⟩
  filter_upwards [hq, hz, hb'] with z hqz hzz hbz
  intro m hm
  by_cases hs : z ∈ S
  · exact hbz hs m hm
  · rw [(SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (hzz hs) m).self_of_nhds,
      iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg hC (Real.rpow_nonneg hqz.le _)

/-- The stress-force tail estimate also holds on boxes meeting the axis:
the apparent reciprocal-radius singularities lie in a common zero region. -/
theorem stress_prefix_rate_axis {l : Filter SpaceTime} {a : ℕ → ℕ} {h C hi r : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h 0 hi) (hr : 0 < r)
    {d : Coefficients} (hd : SmoothCoefficients d) (hc : StressZeroCore d r)
    (ha : AdmissibleScales h (coefficientBundle C d) (innerBox 0 hi) a)
    (J M : ℕ) (hM : M + 1 ≤ J + 3) :
    FiniteJetRate l (fun z => (cartesianChart h z).1)
      (fun z => baseStressForce a h C d z - prefixStressForce J h C d z)
      M (h * (J + 1) - CoordinateAlgebra.A h - 1 / 2 - 3 * (M + 1)) := by
  let S : Set SpaceTime := {z | r / 2 ≤ (cartesianChart h z).2.1}
  have hlS : ∀ᶠ z in l ⊓ 𝓟 S, z ∈ S :=
    (Filter.eventually_principal.mpr (fun _ hz => hz)).filter_mono inf_le_right
  let A' : PhysicalApproach (l ⊓ 𝓟 S) h (r / 2) hi := {
    carrier := A.carrier
    compact := A.compact
    in_carrier := A.in_carrier.filter_mono inf_le_left
    past := A.past.filter_mono inf_le_left
    radial := by
      filter_upwards [A.radial.filter_mono inf_le_left, hlS] with z hz hzs
      exact ⟨hzs, hz.2⟩
    scale := A.scale.mono_left inf_le_left }
  have ha' : AdmissibleScales h (coefficientBundle C d) (innerBox (r / 2) hi) a :=
    admissible_mono ha (fun w hw => ⟨⟨(by linarith : (0 : ℝ) ≤ r / 2).trans hw.1.1, hw.1.2⟩, hw.2⟩)
  have hb := stress_prefix_rate hh hh1 A' (by positivity) hd ha' J M hM
  apply finiteRate_extend_zero hb ((A.positive_small hh hh1).mono (fun _ hz => hz.1))
  filter_upwards [A.past] with z ht
  intro hz
  have hx : (cartesianChart h z).2.1 < r := by
    have hnot : ¬r / 2 ≤ (cartesianChart h z).2.1 := hz
    linarith [lt_of_not_ge hnot]
  have hb0 := baseStressForce_core_germ (C := C) hh hh1 a hc ht hx
  have hj0 := prefixStressForce_core_germ (C := C) hh hh1 J hc ht hx
  filter_upwards [hb0, hj0] with y hy hy'
  simp only [hy, hy', sub_zero]

/-- Equality of continuous physical fields away from the symmetry axis
extends across it. The proof uses an explicit Cartesian perturbation. -/
theorem eqOn_of_off_axis {V : Type} [NormedAddCommGroup V]
    {U : Set SpaceTime} (hU : IsOpen U) {F G : SpaceTime → V}
    (hF : ContinuousOn F U) (hG : ContinuousOn G U)
    (he : ∀ z ∈ U, 0 < AxisymmetricFields.radialEnergy z.2 → F z = G z) : EqOn F G U := by
  intro z hz
  by_cases hs : 0 < AxisymmetricFields.radialEnergy z.2
  · exact he z hz hs
  have hs0 : AxisymmetricFields.radialEnergy z.2 = 0 :=
    le_antisymm (le_of_not_gt hs) (AxisymmetricFields.radialEnergy_nonneg z.2)
  have hx0 : z.2 0 = 0 := by
    apply sq_eq_zero_iff.mp
    unfold AxisymmetricFields.radialEnergy at hs0
    linarith [sq_nonneg (z.2 0), sq_nonneg (z.2 1)]
  have hx1 : z.2 1 = 0 := by
    apply sq_eq_zero_iff.mp
    unfold AxisymmetricFields.radialEnergy at hs0
    linarith [sq_nonneg (z.2 0), sq_nonneg (z.2 1)]
  let gamma : ℝ → SpaceTime := fun t => (z.1, z.2 + t • coordinateVector 0)
  have hgamma : Continuous gamma := continuous_const.prodMk (continuous_const.add
      (continuous_id.smul continuous_const))
  have hg0 : gamma 0 = z := by simp [gamma]
  have hlim : Tendsto gamma (𝓝[>] 0) (𝓝 z) := by
    simpa only [← hg0] using (hgamma.tendsto 0).mono_left nhdsWithin_le_nhds
  have hpos : ∀ t : ℝ, 0 < t → 0 < AxisymmetricFields.radialEnergy (gamma t).2 := by
    intro t ht
    simp only [gamma, AxisymmetricFields.radialEnergy, PiLp.add_apply, PiLp.smul_apply,
      coordinateVector, PiLp.single_apply, hx0, hx1, zero_add, smul_eq_mul]
    norm_num
    positivity
  have hevent : (F ∘ gamma) =ᶠ[𝓝[>] 0] (G ∘ gamma) := by
    filter_upwards [self_mem_nhdsWithin, hlim.eventually (hU.mem_nhds hz)] with t ht htu
    exact he (gamma t) htu (hpos t ht)
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hF.continuousAt (hU.mem_nhds hz)).tendsto.comp hlim)
    ((hG.continuousAt (hU.mem_nhds hz)).tendsto.comp hlim) hevent

end AxisRateExtension

section RegularFiniteTails

open ProblemStatement DiagonalResidual SlowExpansionResidual SlowResidualMatching AxisTailRegularity

/-- The regular descriptors are actual finite sums of physical monomials. -/
noncomputable def regularTransportField (N : ℕ) (h e α : ℝ)
    (beta u f : ℕ → Inner → ℝ) (z : SpaceTime) : ℝ :=
  ∑ i ∈ transportIndices N,
    cartesianMonomial h (transportPower N h e i) (regularTransportTerm N h e α beta u f i) z

/-- Regular radial field, given by `∑ i ∈ pressureIndices N, cartesianMonomial h (pressurePower
N h i - 1) (regularPressureTerm N h C phi u beta i) z`. -/
noncomputable def regularRadialField (N : ℕ) (h C : ℝ)
    (phi u beta : ℕ → Inner → ℝ) (z : SpaceTime) : ℝ :=
  ∑ i ∈ pressureIndices N,
    cartesianMonomial h (pressurePower N h i - 1) (regularPressureTerm N h C phi u beta i) z

/-- Regular truncation, constructed using `assembleComponents`. -/
noncomputable def regularTruncation (N : ℕ) (h C : ℝ)
    (phi u beta : ℕ → Inner → ℝ) : SpaceTime → Space :=
  assembleComponents (regularRadialField N h C phi u beta)
    (fun z => C⁻¹ * regularTransportField N h (angularExponent h) 1 beta u phi z)
    (regularTransportField N h (axialExponent h) 0 beta u u)

theorem assembleComponents_smooth {U : Set SpaceTime} {R A Z : SpaceTime → ℝ}
    (hR : ContDiffOn ℝ ∞ R U) (hA : ContDiffOn ℝ ∞ A U) (hZ : ContDiffOn ℝ ∞ Z U) :
    ContDiffOn ℝ ∞ (assembleComponents R A Z) U :=
  ((hR.smul radialVector_smooth.contDiffOn).add
    (hA.smul angularVector_smooth.contDiffOn)).add (hZ.smul contDiffOn_const)

theorem regularTransportField_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {O : Set Inner} (hO : IsOpen O) (N : ℕ) (e α : ℝ) (beta u f : ℕ → Inner → ℝ)
    (hb : ∀ j ≤ N, ContDiffOn ℝ ∞ (beta j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hf : ∀ j ≤ N, ContDiffOn ℝ ∞ (f j) O)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0) :
    ContDiffOn ℝ ∞ (regularTransportField N h e α beta u f) (chartedDomain h O) :=
  ContDiffOn.sum (fun _ hi => monomial_smoothOn hh hh1 hO
    (regularTransportTerm_smoothOn hO N h e α beta u f hb hu hf hL hi))

theorem regularRadialField_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {O : Set Inner} (hO : IsOpen O) (N : ℕ) (C : ℝ) (phi u beta : ℕ → Inner → ℝ)
    (hp : ∀ j ≤ N, ContDiffOn ℝ ∞ (phi j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hb : ∀ j ≤ N, ContDiffOn ℝ ∞ (beta j) O)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0) :
    ContDiffOn ℝ ∞ (regularRadialField N h C phi u beta) (chartedDomain h O) :=
  ContDiffOn.sum (fun _ hi => monomial_smoothOn hh hh1 hO
    (regularPressureTerm_smoothOn hO N h C phi u beta hp hu hb hL hi))

theorem regularTruncation_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {O : Set Inner} (hO : IsOpen O) (N : ℕ) (C : ℝ) (phi u beta : ℕ → Inner → ℝ)
    (hp : ∀ j ≤ N, ContDiffOn ℝ ∞ (phi j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hb : ∀ j ≤ N, ContDiffOn ℝ ∞ (beta j) O)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0) :
    ContDiffOn ℝ ∞ (regularTruncation N h C phi u beta) (chartedDomain h O) := by
  exact assembleComponents_smooth (regularRadialField_smooth hh hh1 hO N C phi u beta hp hu hb hL)
    (contDiffOn_const.mul (regularTransportField_smooth hh hh1 hO N _ _ beta u phi hb hu hp hL))
    (regularTransportField_smooth hh hh1 hO N _ _ beta u u hb hu hu hL)

/-- Cancellation of the radial factor loses no power of `q`, including
for all physical derivatives on compact sets meeting the axis. -/
theorem regularTruncation_rate {l : Filter SpaceTime} {h lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {O : Set Inner} (hO : IsOpen O) (hKO : innerBox lo hi ⊆ O)
    (N : ℕ) (C : ℝ) (phi u beta : ℕ → Inner → ℝ)
    (hp : ∀ j ≤ N, ContDiffOn ℝ ∞ (phi j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hb : ∀ j ≤ N, ContDiffOn ℝ ∞ (beta j) O)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0) (M : ℕ) :
    FiniteJetRate l (fun z => (cartesianChart h z).1)
      (regularTruncation N h C phi u beta) M (2 * (N : ℝ) * h - 2 - M) := by
  have hW := chartedDomain_isOpen hh hh1 hO
  have hlW := A.in_chartedDomain hh hh1 hKO
  have hq := A.positive_small hh hh1
  have hRs := regularRadialField_smooth hh hh1 hO N C phi u beta hp hu hb hL
  have hFs := regularTransportField_smooth hh hh1 hO N (angularExponent h) 1 beta u phi hb hu hp hL
  have hZs := regularTransportField_smooth hh hh1 hO N (axialExponent h) 0 beta u u hb hu hu hL
  have hR := finset_monomial_rate hh hh1 A hO hKO (pressureIndices N)
    (regularPressureTerm N h C phi u beta) (fun i => pressurePower N h i - 1)
    (2 * (N : ℝ) * h - 2)
    (fun _ hi => regularPressureTerm_smoothOn hO N h C phi u beta hp hu hb hL hi)
    (fun _ hi => radial_power_lower hh.le N hi) M
  have hF := finset_monomial_rate hh hh1 A hO hKO (transportIndices N)
    (regularTransportTerm N h (angularExponent h) 1 beta u phi) (transportPower N h
        (angularExponent h))
    (2 * (N : ℝ) * h - 2)
    (fun _ hi => regularTransportTerm_smoothOn hO N h (angularExponent h) 1 beta u phi hb hu hp hL
        hi)
    (fun _ hi => angular_power_lower hh.le N hi) M
  have hZ := finset_monomial_rate hh hh1 A hO hKO (transportIndices N)
    (regularTransportTerm N h (axialExponent h) 0 beta u u) (transportPower N h (axialExponent h))
    (2 * (N : ℝ) * h - 2)
    (fun _ hi => regularTransportTerm_smoothOn hO N h (axialExponent h) 0 beta u u hb hu hu hL hi)
    (fun _ hi => axial_power_lower hh.le N hi) M
  exact assembleComponents_rate hW hlW A.compact A.in_carrier
    (hq.mono (fun _ hz => hz.1)) hRs (contDiffOn_const.mul hFs) hZs hR
    (scalarConst_rate hF hW hlW hFs C⁻¹) hZ

theorem regularTransportField_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {O : Set Inner} (hO : IsOpen O) (N : ℕ) (e α : ℝ)
    {v u f beta u' f' : ℕ → Inner → ℝ}
    (hv : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → v j w = w.1 * beta j w)
    (hu : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → u j w = u' j w)
    (hf : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → f j w = f' j w)
    {z : SpaceTime} (hz : z ∈ chartedDomain h O) (hs : 0 < AxisymmetricFields.radialEnergy z.2) :
    regularTransportField N h e α beta u' f' z = transportTailField N h e α v u f z := by
  rw [transportTailField_eq]
  apply Finset.sum_congr rfl
  intro i hi
  change _ * _ = _ * _
  congr 1
  exact (transportTerm_eq_regular_on_nonnegative hO N h e α hv hu hf hz.2
    (LeadingStress.inner_X_pos (p := AxisymmetricFields.profilePoint z.1 z.2) hh hh1 hz.1 hs)
        hi).symm

theorem regularRadialField_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {O : Set Inner} (hO : IsOpen O) (N : ℕ) (C : ℝ)
    {f : SlowProfiles} {phi u beta : ℕ → Inner → ℝ}
    (hv : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → f.flux j w = w.1 * beta j w)
    (hu : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → f.axial j w = u j w)
    (hp : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → f.phi j w = phi j w)
    (hb : ∀ j ≤ N, ContDiffOn ℝ ∞ (beta j) O)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0)
    {z : SpaceTime} (hz : z ∈ chartedDomain h O) (hs : 0 < AxisymmetricFields.radialEnergy z.2) :
    regularRadialField N h C phi u beta z = radialTailField N h C f z := by
  rw [← radialTailExpression_eq hh hh1 N C f ⟨hz.1, hs⟩]
  apply Finset.sum_congr rfl
  intro i hi
  change _ * _ = _ * _
  congr 1
  exact (pressureTerm_eq_regular_on_nonnegative hO N h C hv hu hp hb hL hz.2
    (LeadingStress.inner_X_pos (p := AxisymmetricFields.profilePoint z.1 z.2) hh hh1 hz.1 hs)
        hi).symm

theorem regularTruncation_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {O : Set Inner} (hO : IsOpen O) (N : ℕ) (C : ℝ)
    {f : SlowProfiles} {phi u beta : ℕ → Inner → ℝ}
    (hv : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → f.flux j w = w.1 * beta j w)
    (hu : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → f.axial j w = u j w)
    (hp : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → f.phi j w = phi j w)
    (hb : ∀ j ≤ N, ContDiffOn ℝ ∞ (beta j) O)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0)
    {z : SpaceTime} (hz : z ∈ chartedDomain h O) (hs : 0 < AxisymmetricFields.radialEnergy z.2) :
    regularTruncation N h C phi u beta z = truncationResidual N h C f z.1 z.2 := by
  rw [regularTruncation, assembleComponents_eq_pack,
    regularRadialField_eq hh hh1 hO N C hv hu hp hb hL hz hs,
    regularTransportField_eq hh hh1 hO N (angularExponent h) 1 hv hu hp hz hs,
    regularTransportField_eq hh hh1 hO N (axialExponent h) 0 hv hu hu hz hs]
  rfl

/-- The exact finite physical error has a smooth continuation through the
axis, and its physical jet bounds follow from its regular monomials. -/
theorem finite_error_rate {l : Filter SpaceTime} {h C lo hi r : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi) (hr : 0 < r)
    {d : Coefficients} (hd : SmoothCoefficients d) (hc : StressZeroCore d r)
    (f : SlowProfiles) (hfinite : FiniteIdentities h C d f)
    {O : Set Inner} (hO : IsOpen O) (hKO : innerBox lo hi ⊆ O)
    (N : ℕ) (phi u beta : ℕ → Inner → ℝ)
    (hp : ∀ j ≤ N, ContDiffOn ℝ ∞ (phi j) O)
    (hu : ∀ j ≤ N, ContDiffOn ℝ ∞ (u j) O)
    (hb : ∀ j ≤ N, ContDiffOn ℝ ∞ (beta j) O)
    (hv : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → f.flux j w = w.1 * beta j w)
    (heu : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → f.axial j w = u j w)
    (hep : ∀ j ≤ N, ∀ w ∈ O, 0 ≤ w.1 → f.phi j w = phi j w)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0) (M : ℕ) :
    FiniteJetRate l (fun z => (cartesianChart h z).1)
      (fun z => navierStokesResidual (prefixVelocity N h C d) (prefixPressure N h C d) z.1 z.2 -
        prefixStressForce N h C d z) M (2 * (N : ℝ) * h - 2 - M) := by
  have hW := chartedDomain_isOpen hh hh1 hO
  have hWP : chartedDomain h O ⊆ past := fun _ hz => ⟨hz.1, mem_univ _⟩
  have hRs := regularTruncation_smooth hh hh1 hO N C phi u beta hp hu hb hL
  have hEs := ((ResidualRegularity.contDiffOn_residual past_isOpen
    (prefixVelocity_smooth hh hh1 hd N C) (prefixPressure_smooth hh hh1 hd N C)).sub
      (prefixStressForce_smooth_past (C := C) hh hh1 hr hd hc N)).mono hWP
  have he := eqOn_of_off_axis hW hRs.continuousOn hEs.continuousOn (fun z hz hs => by
    rw [regularTruncation_eq hh hh1 hO N C hv heu hep hb hL hz hs, hfinite N z ⟨hz.1, hs⟩]
    abel)
  exact finiteRate_congr_on (regularTruncation_rate hh hh1 A hO hKO N C phi u beta hp hu hb hL M)
    hW (A.in_chartedDomain hh hh1 hKO) he

end RegularFiniteTails

section FullNonlinearAssembly

open ProblemStatement DiagonalResidual ResidualStability SlowExpansionResidual

/-- The actual nonlinear error is flat in all physical jets on compact
similarity boxes, including the symmetry axis. Smooth extensions are used
only for the coefficients; their positive-side values are specified here. -/
theorem baseResidual_jetRate_axis {l : Filter SpaceTime} {a : ℕ → ℕ} {h C hi r : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h 0 hi) (hr : 0 < r)
    {d : Coefficients} (hd : SmoothCoefficients d) (hc : StressZeroCore d r)
    (ha : AdmissibleScales h (coefficientBundle C d) (innerBox 0 hi) a)
    (f : SlowProfiles) (hfinite : FiniteIdentities h C d f)
    {O : Set Inner} (hO : IsOpen O) (hKO : innerBox 0 hi ⊆ O)
    (phi u beta : ℕ → Inner → ℝ)
    (hp : ∀ j, ContDiffOn ℝ ∞ (phi j) O)
    (hu : ∀ j, ContDiffOn ℝ ∞ (u j) O)
    (hb : ∀ j, ContDiffOn ℝ ∞ (beta j) O)
    (hv : ∀ j, ∀ w ∈ O, 0 ≤ w.1 → f.flux j w = w.1 * beta j w)
    (heu : ∀ j, ∀ w ∈ O, 0 ≤ w.1 → f.axial j w = u j w)
    (hep : ∀ j, ∀ w ∈ O, 0 ≤ w.1 → f.phi j w = phi j w)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0)
    (m : ℕ) (n : ℝ) (hn : 0 ≤ n) :
    JetRate l (fun z => (cartesianChart h z).1) (baseResidual a h C d) m n := by
  let b : ℝ := CoordinateAlgebra.A h + m + 2
  have hA : 0 < CoordinateAlgebra.A h := by unfold CoordinateAlgebra.A; linarith
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  obtain ⟨N, hN⟩ := exists_nat_ge ((n + b + 2 * CoordinateAlgebra.A h + 6 * m + 12) / h)
  let J := max (m + 2) N
  have hJ : m + 2 ≤ J := le_max_left _ _
  have hJN : (N : ℝ) ≤ J := by exact_mod_cast le_max_right (m + 2) N
  have hgain : n + b + 2 * CoordinateAlgebra.A h + 6 * m + 12 ≤ h * ((J : ℝ) + 1) := by
    have hn' := (div_le_iff₀ hh).mp hN
    nlinarith
  have hq := A.positive_small hh hh1
  have hU := past_isOpen
  have hlU : ∀ᶠ z in l, z ∈ past := A.past.mono (fun _ ht => ⟨ht, mem_univ _⟩)
  have hus := baseVelocity_smooth ha.strictMono hh hh1 hd C
  have hps := basePressure_smooth ha.strictMono hh hh1 hd C
  have huJs := prefixVelocity_smooth hh hh1 hd J C
  have hpJs := prefixPressure_smooth hh hh1 hd J C
  have htS := baseStressForce_smooth_past (C := C) ha.strictMono hh hh1 hr hd hc
  have htJ := prefixStressForce_smooth_past (C := C) hh hh1 hr hd hc J
  have hbg : FiniteJetRate l (fun z => (cartesianChart h z).1) (prefixVelocity J h C d)
      (m + 1) (-b) := by
    convert! prefixVelocity_growth (C := C) hh hh1 A hd J (m + 1) using 1
    dsimp [b]
    push_cast
    ring
  have hvel : FiniteJetRate l (fun z => (cartesianChart h z).1)
      (fun z => baseVelocity a h C d z - prefixVelocity J h C d z) (m + 2) (n + b) := by
    apply finiteRate_weaken (velocity_prefix_rate hh hh1 A hd ha J (m + 2) (by omega)) hq
    push_cast
    linarith
  have hpres : FiniteJetRate l (fun z => (cartesianChart h z).1)
      (fun z => basePressure a h C d z - prefixPressure J h C d z) (m + 1) (n + b) := by
    apply finiteRate_weaken (pressure_prefix_rate hh hh1 A hd ha J (m + 1) (by omega)) hq
    push_cast
    linarith
  have hstress : JetRate l (fun z => (cartesianChart h z).1)
      (fun z => baseStressForce a h C d z - prefixStressForce J h C d z) m n := by
    apply (finiteRate_at (stress_prefix_rate_axis hh hh1 A hr hd hc ha J m (by
        omega)) le_rfl).weaken hq
    dsimp [b] at hgain
    linarith
  let EJ : SpaceTime → Space := fun z =>
    navierStokesResidual (prefixVelocity J h C d) (prefixPressure J h C d) z.1 z.2 -
      prefixStressForce J h C d z
  have hEJ : JetRate l (fun z => (cartesianChart h z).1) EJ m n := by
    apply (finiteRate_at (finite_error_rate hh hh1 A hr hd hc f hfinite hO hKO J phi u beta
      (fun j _ => hp j) (fun j _ => hu j) (fun j _ => hb j)
      (fun j _ => hv j) (fun j _ => heu j) (fun j _ => hep j) hL m) le_rfl).weaken hq
    dsimp [b] at hgain
    linarith
  have hEJs : ContDiffOn ℝ ∞ EJ past :=
    (ResidualRegularity.contDiffOn_residual hU huJs hpJs).sub htJ
  let Df := residualDifference (prefixVelocity J h C d)
    (fun z => baseVelocity a h C d z - prefixVelocity J h C d z)
    (prefixPressure J h C d) (fun z => basePressure a h C d z - prefixPressure J h C d z)
  have hDf : JetRate l (fun z => (cartesianChart h z).1) Df m n :=
    residualDifference_jetRate hU hlU hq huJs (hus.sub huJs) hpJs (hps.sub hpJs)
      m hb0 hn hbg hvel hpres
  have hDfs : ContDiffOn ℝ ∞ Df past :=
    (ResidualRegularity.contDiffOn_residual hU (huJs.add (hus.sub huJs))
      (hpJs.add (hps.sub hpJs))).sub (ResidualRegularity.contDiffOn_residual hU huJs hpJs)
  have hsum := (hEJ.add hDf hU hlU hEJs hDfs).add (jetRate_neg hstress) hU hlU
    (hEJs.add hDfs) (htS.sub htJ).neg
  have hvelsum : (fun z => prefixVelocity J h C d z +
      (baseVelocity a h C d z - prefixVelocity J h C d z)) = baseVelocity a h C d := by
    funext z
    abel
  have hpressum : (fun z => prefixPressure J h C d z +
      (basePressure a h C d z - prefixPressure J h C d z)) = basePressure a h C d := by
    funext z
    abel
  have heq : (fun z => EJ z + Df z + -(baseStressForce a h C d z - prefixStressForce J h C d z)) =
      baseResidual a h C d := by
    funext z
    simp only [EJ, Df, residualDifference, hvelsum, hpressum, baseResidual]
    abel
  rwa [heq] at hsum

theorem baseResidual_allJetsFlat_axis {l : Filter SpaceTime} {a : ℕ → ℕ} {h C hi r : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h 0 hi) (hr : 0 < r)
    {d : Coefficients} (hd : SmoothCoefficients d) (hc : StressZeroCore d r)
    (ha : AdmissibleScales h (coefficientBundle C d) (innerBox 0 hi) a)
    (f : SlowProfiles) (hfinite : FiniteIdentities h C d f)
    {O : Set Inner} (hO : IsOpen O) (hKO : innerBox 0 hi ⊆ O)
    (phi u beta : ℕ → Inner → ℝ)
    (hp : ∀ j, ContDiffOn ℝ ∞ (phi j) O)
    (hu : ∀ j, ContDiffOn ℝ ∞ (u j) O)
    (hb : ∀ j, ContDiffOn ℝ ∞ (beta j) O)
    (hv : ∀ j, ∀ w ∈ O, 0 ≤ w.1 → f.flux j w = w.1 * beta j w)
    (heu : ∀ j, ∀ w ∈ O, 0 ≤ w.1 → f.axial j w = u j w)
    (hep : ∀ j, ∀ w ∈ O, 0 ≤ w.1 → f.phi j w = phi j w)
    (hL : ∀ w ∈ O, CoordinateAlgebra.L h w.2 ≠ 0) :
    AllJetsFlat l (fun z => (cartesianChart h z).1) (baseResidual a h C d) := by
  intro m N
  obtain ⟨K, hK, hb⟩ := baseResidual_jetRate_axis hh hh1 A hr hd hc ha f hfinite hO hKO
    phi u beta hp hu hb hv heu hep hL m N (Nat.cast_nonneg N)
  refine ⟨K, hK, ?_⟩
  filter_upwards [A.positive_small hh hh1, hb] with z hz hbound
  simpa only [abs_norm, abs_of_pos hz.1, Real.rpow_natCast] using hbound

end FullNonlinearAssembly

section WeightedInputConstruction

open ActiveAnnulusWeight

/-- Higher-order support is strictly interior to the active annulus.
The interval and its distance from the edges may depend on the order. -/
def HigherInteriorSupport (d : Coefficients) (left right : ℝ) : Prop :=
  ∀ j : ℕ, 2 ≤ j → ∃ a b : ℝ, Icc a b ⊆ Ioo (Real.exp left) (Real.exp right) ∧
    SlowStressSupport.radialSupport univ a b (d.stressTheta j) ∧
    SlowStressSupport.radialSupport univ a b (d.stressAxial j)

theorem higherStressQuotient_smooth_of_support {d : Coefficients} (hd : SmoothCoefficients d)
    {c left right : ℝ} (hc : 0 < c) (hs : HigherInteriorSupport d left right) (j : ℕ) :
    ContDiff ℝ ∞ (higherStressQuotient d (activeZeta c left right) j) := by
  by_cases hj : j ≤ 1
  · unfold higherStressQuotient
    simp only [ite_eq_left hj]
    exact contDiff_const
  obtain ⟨a, b, hab, ht, hz⟩ := hs j (by omega)
  have hq (f : Inner → ℝ) (hf : ContDiff ℝ ∞ f)
      (hfS : SlowStressSupport.radialSupport univ a b f) :
      ContDiff ℝ ∞ (fun w => f w / activeZeta c left right w) := by
    have h := SlowStressSupport.interior_quotient_smooth isOpen_univ hf.contDiffOn hfS hab
      (radialWeight_smooth hc left right).contDiffOn
      (fun _ hx => (radialWeight_pos hx).ne')
    simpa only [SlowStressSupport.Smooth, SlowStressSupport.region, univ_prod_univ,
      contDiffOn_univ, activeZeta] using h
  have htq := hq (d.stressTheta j) (hd.stressTheta j) ht
  have hzq := hq (d.stressAxial j) (hd.stressAxial j) hz
  unfold higherStressQuotient
  simp only [ite_eq_right hj]
  simpa only [stressPair, Prod.smul_mk, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using htq.prodMk hzq

theorem compact_weighted_jet_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Inner → V} (hf : ContDiff ℝ ∞ f) {zeta : Inner → ℝ} (hz : Continuous zeta)
    {K : Set Inner} (hK : IsCompact K) (hp : ∀ w ∈ K, 0 < zeta w) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ‖iteratedFDeriv ℝ m f w‖ ≤ C * zeta w := by
  have hj : Continuous (iteratedFDeriv ℝ m f) :=
    (hf.iteratedFDeriv_right (m := 0) (by simpa only [zero_add] using nat_le_infty m)).continuous
  have hc : ContinuousOn (fun w => ‖iteratedFDeriv ℝ m f w‖ / zeta w) K :=
    hj.norm.continuousOn.div hz.continuousOn (fun w hw => (hp w hw).ne')
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max B 0 + 1, by positivity, fun w hw => ?_⟩
  have he : ‖iteratedFDeriv ℝ m f w‖ / zeta w ≤ B := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (hp w hw).le)]
      using hB w hw
  exact ((div_le_iff₀ (hp w hw)).mp he).trans
    (mul_le_mul_of_nonneg_right (by linarith [le_max_left B 0]) (hp w hw).le)

/-- Outer window, given by `Ico cut (Real.exp right) ×ˢ Icc (-1) 1`. -/
noncomputable def outerWindow (cut right : ℝ) : Set Inner :=
  Ico cut (Real.exp right) ×ˢ Icc (-1) 1

/-- Compact middle-region bounds and actual zero germs at the inner edge
extend an outer collar estimate to the entire active annulus. -/
theorem edgeJets_of_outer_collar {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Inner → V} (hf : ContDiff ℝ ∞ f) {c left right inner cut : ℝ}
    (hc : 0 < c) (hl : Real.exp left < inner) (_hi : inner ≤ cut) (hr : cut < Real.exp right)
    (hzero : ∀ w : Inner, w.1 < inner → f w = 0)
    (ho : PolynomialEdgeJets (outerWindow cut right) (activeZeta c left right)
      (activeDelta left right) f) :
    PolynomialEdgeJets (activeWindow left right) (activeZeta c left right)
      (activeDelta left right) f := by
  intro m
  let K : Set Inner := Icc inner cut ×ˢ Icc (-1) 1
  have hKW : K ⊆ activeWindow left right := fun _ hw =>
    ⟨⟨hl.trans_le hw.1.1, hw.1.2.trans_lt hr⟩, hw.2⟩
  obtain ⟨A, hA, hAb⟩ := compact_weighted_jet_bound hf
    (activeZeta_smooth hc left right).continuous (isCompact_Icc.prod isCompact_Icc)
    (fun w (hw : w ∈ K) => radialWeight_pos (hKW hw).1) m
  obtain ⟨B, hB, N, hBb⟩ := ho m
  refine ⟨A + B, add_pos hA hB, N, fun w hw => ?_⟩
  have hz : 0 < activeZeta c left right w := radialWeight_pos hw.1
  have hdelta := activeDelta_bounds hw
  have hN : 1 ≤ (activeDelta left right w)⁻¹ ^ N :=
    one_le_pow₀ ((one_le_inv₀ hdelta.1).mpr hdelta.2)
  by_cases hwi : w.1 < inner
  · have he : f =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds hwi)] with v hv
      exact hzero v hv
    rw [(SolenoidalDiagonal.iteratedFDeriv_eventuallyEq he m).self_of_nhds,
      iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    positivity
  by_cases hwc : w.1 ≤ cut
  · have hb := hAb w ⟨⟨le_of_not_gt hwi, hwc⟩, hw.2⟩
    calc
      _ ≤ A * activeZeta c left right w := hb
      _ ≤ (A + B) * activeZeta c left right w :=
        mul_le_mul_of_nonneg_right (by linarith) hz.le
      _ ≤ (A + B) * activeZeta c left right w * (activeDelta left right w)⁻¹ ^ N :=
        le_mul_of_one_le_right (mul_nonneg (add_pos hA hB).le hz.le) hN
  · exact (hBb w ⟨⟨(lt_of_not_ge hwc).le, hw.1.2⟩, hw.2⟩).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hz.le)
        (pow_nonneg (inv_nonneg.mpr hdelta.1.le) _))

theorem terminal_zeta_eq {c left y0 : ℝ} {w : Inner} (hw : 0 < w.1) :
    SlowFirstOrderEdge.zeta c (Real.exp left) y0 w.1 = activeZeta c left (y0 + 3) w := by
  simp [SlowFirstOrderEdge.zeta, activeZeta, radialWeight, hw, weight,
    Real.log_div hw.ne' (Real.exp_ne_zero left), Real.log_exp]

theorem terminal_delta_eq {left y0 : ℝ} {w : Inner} (hw : 0 < w.1) :
    SlowFirstOrderEdge.edgeDistance (Real.exp left) y0 w.1 = activeDelta left (y0 + 3) w := by
  simp [SlowFirstOrderEdge.edgeDistance, activeDelta, edgeDistance,
    Real.log_div hw.ne' (Real.exp_ne_zero left), Real.log_exp]

/-- Stress slot injection, given by `(ContinuousLinearMap.id ℝ ℝ).prod 0`. -/
noncomputable def stressSlotInjection : ℝ →L[ℝ] Inner :=
  (ContinuousLinearMap.id ℝ ℝ).prod 0

/-- The first-order collar bound is imported from the actual backward
viscous stress primitive. Only its equality with the coefficient is supplied. -/
theorem firstOrder_pair_outer_edgeJets (C : ℝ) (d : OutgoingTail.TailData)
    (y0 : ℝ) {c left width : ℝ} (hc : 0 < c) (hw : 0 < width)
    (hl : left < y0 + 3 - width) {F : Inner → Inner}
    (he : ∀ w ∈ outerWindow (Real.exp (y0 + 3 - width)) (y0 + 3),
      F =ᶠ[𝓝 w] (fun v => (SlowFirstOrderEdge.stressX C d y0 v, 0))) :
    PolynomialEdgeJets (outerWindow (Real.exp (y0 + 3 - width)) (y0 + 3))
      (activeZeta c left (y0 + 3)) (activeDelta left (y0 + 3)) F := by
  intro m
  obtain ⟨B, hB, N, hBb⟩ := SlowFirstOrderEdge.stressX_weighted_jets C d y0 m hw
    (Real.exp_pos left) hc (Real.exp_lt_exp.mpr hl)
  refine ⟨(‖stressSlotInjection‖ + 1) * B, mul_pos (by positivity) hB, N, fun w hwW => ?_⟩
  have hX : 0 < w.1 := (Real.exp_pos _).trans_le hwW.1.1
  have hb := hBb w.1 hwW.1 w.2 hwW.2
  rw [terminal_zeta_eq hX, terminal_delta_eq hX, div_eq_mul_inv, ← inv_pow] at hb
  have hs := SlowFirstOrderEdge.stressX_contDiffOn C d y0
  have hO : IsOpen {v : Inner | 0 < v.1} := isOpen_lt continuous_const continuous_fst
  have hj := ResidualStability.norm_jet_linear_map stressSlotInjection hO hs hX m
  rw [(SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (he w hwW) m).self_of_nhds]
  change ‖iteratedFDeriv ℝ m (fun v => stressSlotInjection (SlowFirstOrderEdge.stressX C d y0 v))
      w‖ ≤ _
  have hz : 0 ≤ activeZeta c left (y0 + 3) w := by
    exact (radialWeight_pos ⟨(Real.exp_lt_exp.mpr hl).trans_le hwW.1.1, hwW.1.2⟩).le
  have hd : 0 ≤ (activeDelta left (y0 + 3) w)⁻¹ ^ N := by
    exact pow_nonneg (inv_nonneg.mpr (activeDelta_bounds
      ⟨⟨(Real.exp_lt_exp.mpr hl).trans_le hwW.1.1, hwW.1.2⟩, hwW.2⟩).1.le) _
  calc
    _ ≤ ‖stressSlotInjection‖ * ‖iteratedFDeriv ℝ m (SlowFirstOrderEdge.stressX C d y0) w‖ := hj
    _ ≤ ‖stressSlotInjection‖ * (B * activeZeta c left (y0 + 3) w * (activeDelta left (y0 + 3) w)⁻¹
        ^ N) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ ≤ (‖stressSlotInjection‖ + 1) * (B * activeZeta c left (y0 + 3) w * (activeDelta left (y0 +
        3) w)⁻¹ ^ N) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (mul_nonneg hB.le hz) hd)
    _ = _ := by ring

/-- A common scale sequence with the full weighted tensor estimate,
constructed from support, smoothness, and the actual first-order primitive.
No tensor estimate or summation-tail estimate is assumed. -/
theorem exists_weighted_base_scales_from_primitives {h : ℝ} (hh : 0 < h) (C : ℝ)
    {d : Coefficients} (hd : SmoothCoefficients d) (tail : OutgoingTail.TailData)
    (y0 : ℝ) {c left width inner : ℝ} (hc : 0 < c) (hw : 0 < width)
    (hl : Real.exp left < inner) (hi : inner ≤ Real.exp (y0 + 3 - width))
    (hs : HigherInteriorSupport d left (y0 + 3))
    (hz : ∀ w : Inner, w.1 < inner → stressPair d 1 w = 0)
    (he : ∀ w ∈ outerWindow (Real.exp (y0 + 3 - width)) (y0 + 3),
      stressPair d 1 =ᶠ[𝓝 w] (fun v => (SlowFirstOrderEdge.stressX C tail y0 v, 0)))
    {K : Set Inner} (hK : IsCompact K) (hWK : activeWindow left (y0 + 3) ⊆ K) (B : ℕ) :
    ∃ a : ℕ → ℕ, B ≤ a 0 ∧ AdmissibleScales h (coefficientBundle C d) K a ∧
      ∀ m : ℕ, ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ q : ℝ, 0 < q → q ≤ 1 →
        ∀ w ∈ activeWindow left (y0 + 3),
          ‖blownJet m (fun v => normalizedTensor a h d v - stressPair d 0 v.2) (q, w)‖ ≤
            D * q ^ h * activeZeta c left (y0 + 3) w * (activeDelta left (y0 + 3) w)⁻¹ ^ N := by
  have hlog : left < y0 + 3 - width := Real.exp_lt_exp.mp (hl.trans_le hi)
  have hright : Real.exp (y0 + 3 - width) < Real.exp (y0 + 3) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hfirst := edgeJets_of_outer_collar (stressPair_smooth hd 1) hc hl hi hright hz
    (firstOrder_pair_outer_edgeJets C tail y0 hc hw hlog he)
  let O : Set Inner := Ioo (Real.exp left) (Real.exp (y0 + 3)) ×ˢ univ
  have hO : IsOpen O := isOpen_Ioo.prod isOpen_univ
  have hWO : activeWindow left (y0 + 3) ⊆ O := fun _ hw => ⟨hw.1, mem_univ _⟩
  exact exists_weighted_base_scales hh C hd hK hWK hO hWO
    (activeZeta_smooth hc left (y0 + 3)) (fun _ hw => radialWeight_pos hw.1)
    (fun _ hw => activeDelta_bounds hw) hfirst
    (activeZeta_edgeJets (by linarith) hc) (higherStressQuotient_smooth_of_support hd hc hs) B

end WeightedInputConstruction

end NavierStokes.BaseResidual
