/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowResidualMatching

@[expose] public section

/-!
# Regular finite tail coefficients at the symmetry axis

The radial flux is `V_n = X * beta_n`.  This module uses that identity in the
actual finite tails.  The resulting coefficient functions contain no division
by `X`; their finite indices and powers of `q` are unchanged.
-/

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
