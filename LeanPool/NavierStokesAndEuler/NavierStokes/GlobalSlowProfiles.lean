/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TransportPrimitive
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowResidualMatching
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricRephase

/-!
# Globalization of the positive slow profiles

The radial coordinate in this file is the physical similarity radius `R`,
so that `X = R² / 2`.  Smoothness at the axis is represented by genuine
smooth even functions of the signed radius.  Moment corrections are supported
in a fixed positive-radius patch and are reflected with the appropriate parity.

All integrals and differential operators below are the actual ones.  In
particular the preceding radial source is retained when pressure is recomputed.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators

namespace NavierStokes.GlobalSlowProfiles

/-- Field: an abbreviation for `ℝ × ℝ → ℝ`. -/
abbrev Field := ℝ × ℝ → ℝ
/-- History: an abbreviation for `ℕ → Field`. -/
abbrev History := ℕ → Field
/-- Region: an abbreviation for `(univ : Set ℝ) ×ˢ S`. -/
abbrev region (S : Set ℝ) := (univ : Set ℝ) ×ˢ S
/-- Smooth: an abbreviation for `ContDiffOn ℝ ∞ f (region S)`. -/
abbrev Smooth (S : Set ℝ) (f : Field) := ContDiffOn ℝ ∞ f (region S)
/-- Dr, given by `ProfileHistories.radialPartial`. -/
noncomputable def dr := ProfileHistories.radialPartial
/-- De, given by `ProfileHistories.parameterPartial`. -/
noncomputable def de := ProfileHistories.parameterPartial

/-- Regular data, collecting `smooth`, `even`. -/
structure Regular (S : Set ℝ) (f : Field) : Prop where
  smooth : Smooth S f
  even : ∀ eta ∈ S, ∀ R, f (-R, eta) = f (R, eta)

theorem Regular.const (S : Set ℝ) (c : ℝ) : Regular S (fun _ => c) :=
  ⟨contDiffOn_const, fun _ _ _ => rfl⟩

theorem Regular.add {S : Set ℝ} {f g : Field} (hf : Regular S f) (hg : Regular S g) :
    Regular S (f + g) := by
  refine ⟨hf.smooth.add hg.smooth, ?_⟩
  intro eta heta R
  change f (-R, eta) + g (-R, eta) = f (R, eta) + g (R, eta)
  rw [hf.even eta heta, hg.even eta heta]

theorem Regular.mul {S : Set ℝ} {f g : Field} (hf : Regular S f) (hg : Regular S g) :
    Regular S (f * g) := by
  refine ⟨hf.smooth.mul hg.smooth, ?_⟩
  intro eta heta R
  change f (-R, eta) * g (-R, eta) = f (R, eta) * g (R, eta)
  rw [hf.even eta heta, hg.even eta heta]

/-- Regular algebra, bundling `carrier`, `zero_mem`, `one_mem`, `add_mem` and the required
compatibility proofs. -/
noncomputable def regularAlgebra (S : Set ℝ) : Subalgebra ℝ Field where
  carrier := {f | Regular S f}
  zero_mem' := by exact Regular.const S 0
  one_mem' := by exact Regular.const S 1
  add_mem' := Regular.add
  mul_mem' := Regular.mul
  algebraMap_mem' := Regular.const S

/-- Even profile: an abbreviation for `↥(regularAlgebra S) instance {S : Set ℝ} : CoeFun
(EvenProfile S) (fun _ => Field) := ⟨fun f => f.1⟩`. -/
abbrev EvenProfile (S : Set ℝ) := ↥(regularAlgebra S)

instance {S : Set ℝ} : CoeFun (EvenProfile S) (fun _ => Field) := ⟨fun f => f.1⟩

theorem EvenProfile.smooth {S : Set ℝ} (f : EvenProfile S) : Smooth S f := f.2.smooth

theorem EvenProfile.even {S : Set ℝ} (f : EvenProfile S) {eta : ℝ} (heta : eta ∈ S)
    (R : ℝ) : f (-R, eta) = f (R, eta) := f.2.even eta heta R

theorem slice_smooth {S : Set ℝ} {f : Field} (hf : Smooth S f)
    {eta : ℝ} (heta : eta ∈ S) : ContDiff ℝ ∞ (fun R => f (R, eta)) := by
  apply contDiffOn_univ.mp
  exact hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ _ => ⟨mem_univ _, heta⟩)

@[simp] theorem add_apply {S : Set ℝ} (f g : EvenProfile S) (w : ℝ × ℝ) :
    (f + g) w = f w + g w := rfl
@[simp] theorem mul_apply {S : Set ℝ} (f g : EvenProfile S) (w : ℝ × ℝ) :
    (f * g) w = f w * g w := rfl
@[simp] theorem sub_apply {S : Set ℝ} (f g : EvenProfile S) (w : ℝ × ℝ) :
    (f - g) w = f w - g w := rfl
@[simp] theorem neg_apply {S : Set ℝ} (f : EvenProfile S) (w : ℝ × ℝ) :
    (-f) w = -f w := rfl
@[simp] theorem zero_apply {S : Set ℝ} (w : ℝ × ℝ) : (0 : EvenProfile S) w = 0 := rfl
@[simp] theorem one_apply {S : Set ℝ} (w : ℝ × ℝ) : (1 : EvenProfile S) w = 1 := rfl

@[simp] theorem sum_apply {ι : Type*} {S : Set ℝ} (s : Finset ι)
    (f : ι → EvenProfile S) (w : ℝ × ℝ) : (∑ i ∈ s, f i) w = ∑ i ∈ s, f i w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, add_apply, ih]

/-- Bound constant, given by `algebraMap ℝ (EvenProfile S) c`. -/
noncomputable def boundConstant (S : Set ℝ) (c : ℝ) : EvenProfile S :=
  algebraMap ℝ (EvenProfile S) c

@[simp] theorem constant_apply (S : Set ℝ) (c : ℝ) (w : ℝ × ℝ) : boundConstant S c w = c := rfl

/-- Radius squared, given by `⟨fun w => w.1 ^ 2 / 2, ⟨(contDiffOn_fst.pow 2).div_const 2, fun _
_ _ => by simp only [neg_sq]⟩⟩`. -/
noncomputable def radiusSquared (S : Set ℝ) : EvenProfile S :=
  ⟨fun w => w.1 ^ 2 / 2, ⟨(contDiffOn_fst.pow 2).div_const 2,
    fun _ _ _ => by simp only [neg_sq]⟩⟩

/-- Parameter, given by `⟨Prod.snd, ⟨contDiffOn_snd, fun _ _ _ => rfl⟩⟩`. -/
noncomputable def parameter (S : Set ℝ) : EvenProfile S :=
  ⟨Prod.snd, ⟨contDiffOn_snd, fun _ _ _ => rfl⟩⟩

/-- Inverse, given by `⟨fun w => (f w)⁻¹, ⟨f.smooth.inv hf, fun _ heta R => congrArg Inv.inv
(f.even heta R)⟩⟩`. -/
noncomputable def inverse {S : Set ℝ} (f : EvenProfile S)
    (hf : ∀ w ∈ region S, f w ≠ 0) : EvenProfile S :=
  ⟨fun w => (f w)⁻¹, ⟨f.smooth.inv hf, fun _ heta R => congrArg Inv.inv (f.even heta R)⟩⟩

theorem smooth_de {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f) :
    Smooth S (de f) :=
  ProfileHistories.parameterPartial_smooth (PositiveOrderMoments.parameterDomain S hS) hf

theorem parameter_derivative {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {eta : ℝ} (heta : eta ∈ S) (R : ℝ) :
    HasDerivAt (fun t => f (R, t)) (de f (R, eta)) eta :=
  ProfileHistories.parameterPartial_hasDerivAt (PositiveOrderMoments.parameterDomain S hS)
    hf (p := (R, eta)) ⟨mem_univ _, heta⟩

/-- Eta derivative as an element of `EvenProfile S`. -/
noncomputable def etaDerivative {S : Set ℝ} (hS : IsOpen S) (f : EvenProfile S) :
    EvenProfile S := by
  refine ⟨de f, ⟨smooth_de hS f.smooth, ?_⟩⟩
  intro eta heta R
  have he : (fun t => f (-R, t)) =ᶠ[𝓝 eta] fun t => f (R, t) := by
    filter_upwards [hS.mem_nhds heta] with t ht using f.even ht R
  exact (parameter_derivative hS f.smooth heta (-R)).unique
    ((parameter_derivative hS f.smooth heta R).congr_of_eventuallyEq he)

/-- The genuine `X` derivative, smoothly continued through `R = 0`. -/
noncomputable def xDerivative {S : Set ℝ} (hS : IsOpen S) (f : EvenProfile S) :
    EvenProfile S :=
  ⟨fun w => 2 * BoundaryAxisJets.radialJet f 1 w.1 w.2, ⟨
    contDiffOn_const.mul (BoundaryAxisJets.radialJet_joint_contDiffOn hS f.smooth 1),
    fun _ heta R => congrArg (2 * ·) (BoundaryAxisJets.radialJet_even
      (fun r => f.even heta r) 1 R)⟩⟩

theorem radius_mul_xDerivative {S : Set ℝ} (hS : IsOpen S) (f : EvenProfile S)
    {eta : ℝ} (heta : eta ∈ S) (R : ℝ) :
    R * xDerivative hS f (R, eta) = dr f (R, eta) := by
  have hi := EvenSmoothDescent.radialDerivative_identity (slice_smooth f.smooth heta)
    (fun r => f.even heta r) R
  have hd := ProfileHistories.radialPartial_hasDerivAt
    (PositiveOrderMoments.parameterDomain S hS) f.smooth (p := (R, eta)) ⟨mem_univ _, heta⟩
  change R * xDerivative hS f (R, eta) = ProfileHistories.radialPartial f (R, eta)
  rw [← hd.deriv]
  simpa only [xDerivative, BoundaryAxisJets.radialJet,
    EvenSmoothDescent.radialIterate_succ, EvenSmoothDescent.radialIterate_zero,
    smul_eq_mul, mul_assoc, mul_left_comm] using hi

/-- Literal `X`-only cutoff.  The same two radii will be used at every order. -/
noncomputable def coreCutoff (inner stop : ℝ) (w : ℝ × ℝ) : ℝ :=
  1 - TransportPrimitive.cutoff inner stop (w.1 ^ 2 / 2)

theorem coreCutoff_smooth (inner stop : ℝ) : ContDiff ℝ ∞ (coreCutoff inner stop) :=
  contDiff_const.sub ((TransportPrimitive.cutoff_contDiff inner stop).comp
    ((contDiff_fst.pow 2).div_const 2))

theorem coreCutoff_one {inner stop : ℝ} (his : inner < stop) {w : ℝ × ℝ}
    (hw : w.1 ^ 2 / 2 ≤ inner) : coreCutoff inner stop w = 1 := by
  simp [coreCutoff, TransportPrimitive.cutoff_zero his hw]

theorem coreCutoff_zero {inner stop : ℝ} (his : inner < stop) {w : ℝ × ℝ}
    (hw : stop ≤ w.1 ^ 2 / 2) : coreCutoff inner stop w = 0 := by
  simp [coreCutoff, TransportPrimitive.cutoff_one his hw]

/-- A normalized mass average.  There is no division by the radius. -/
noncomputable def massAverage {S : Set ℝ} (hS : IsOpen S) (f : EvenProfile S) :
    EvenProfile S := by
  refine ⟨fun w => 2 * ∫ t in (0 : ℝ)..1, t * f (t * w.1, w.2), ⟨?_, ?_⟩⟩
  · let G : (ℝ × ℝ) × ℝ → ℝ := fun w => w.2 * f (w.2 * w.1.1, w.1.2)
    have hg : ContDiffOn ℝ ∞ G (region S ×ˢ univ) :=
      contDiffOn_snd.mul (f.smooth.comp
        ((contDiffOn_snd.mul contDiffOn_fst.fst).prodMk contDiffOn_fst.snd)
        (fun w hw => ⟨mem_univ _, hw.1.2⟩))
    exact contDiffOn_const.mul
      (ParametricRephase.intervalIntegral_contDiffOn_of_joint G (region S)
        (isOpen_univ.prod hS) hg 0 1 zero_le_one)
  · intro eta heta R
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    change t * f (t * -R, eta) = t * f (t * R, eta)
    rw [mul_neg, f.even heta]

theorem massHistory_eq_massAverage {S : Set ℝ} (hS : IsOpen S) (f : EvenProfile S)
    (w : ℝ × ℝ) :
    PositiveOrderMoments.massHistory f w = w.1 ^ 2 / 2 * massAverage hS f w := by
  rw [PositiveOrderMoments.massHistory, ProfileHistories.primitive_eq_mul_average]
  change w.1 * (∫ t in (0 : ℝ)..1, (t * w.1) * f (t * w.1, w.2)) =
    w.1 ^ 2 / 2 * (2 * ∫ t in (0 : ℝ)..1, t * f (t * w.1, w.2))
  have he : (fun t : ℝ => (t * w.1) * f (t * w.1, w.2)) =
      fun t => w.1 * (t * f (t * w.1, w.2)) := by funext t; ring
  rw [he, intervalIntegral.integral_const_mul]
  ring

theorem parameterMassHistory_eq_massAverage {S : Set ℝ} (hS : IsOpen S)
    (f : EvenProfile S) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    PositiveOrderMoments.parameterMassHistory f w =
      w.1 ^ 2 / 2 * massAverage hS (etaDerivative hS f) w := by
  rw [← massHistory_eq_massAverage]
  apply intervalIntegral.integral_congr
  intro t _
  exact PositiveOrderMoments.weightedAxial_parameterPartial_on hS f.smooth hw

/-- Domain data, collecting `isOpen`, `denominator`. -/
structure Domain (S : Set ℝ) (h : ℝ) : Prop where
  isOpen : IsOpen S
  denominator : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0

/-- Inverse denominator, given by `inverse (1 - boundConstant S (2 * h) * parameter S ^ 2) (fun
w hw => d.denominator w.2 hw.2)`. -/
noncomputable def inverseDenominator {S : Set ℝ} {h : ℝ} (d : Domain S h) : EvenProfile S :=
  inverse (1 - boundConstant S (2 * h) * parameter S ^ 2)
    (fun w hw => d.denominator w.2 hw.2)

@[simp] theorem inverseDenominator_apply {S : Set ℝ} {h : ℝ} (d : Domain S h)
    (w : ℝ × ℝ) : inverseDenominator d w = (PositiveAxisSystem.ell h w.2)⁻¹ := rfl

/-- The normalized divergence reconstruction `V = X β`. -/
noncomputable def betaFromU {S : Set ℝ} {h : ℝ} (d : Domain S h)
    (lam : ℝ) (u : EvenProfile S) : EvenProfile S :=
  (boundConstant S 2 * parameter S * u -
    boundConstant S (2 * (PositiveAxisSystem.dScale h + lam)) * parameter S * massAverage d.isOpen
        u -
    (1 - parameter S ^ 2) * massAverage d.isOpen (etaDerivative d.isOpen u)) *
      inverseDenominator d

theorem betaFromU_eq_fluxHistory {S : Set ℝ} {h : ℝ} (d : Domain S h)
    (lam : ℝ) (u : EvenProfile S) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    w.1 ^ 2 / 2 * betaFromU d lam u w = PositiveOrderMoments.fluxHistory h lam u w := by
  simp only [betaFromU, mul_apply, sub_apply, constant_apply, one_apply,
    inverseDenominator_apply, PositiveOrderMoments.fluxHistory,
    massHistory_eq_massAverage d.isOpen u, parameterMassHistory_eq_massAverage d.isOpen u hw]
  change w.1 ^ 2 / 2 * ((2 * w.2 * u w -
    2 * (PositiveAxisSystem.dScale h + lam) * w.2 * massAverage d.isOpen u w -
    (1 - w.2 ^ 2) * massAverage d.isOpen (etaDerivative d.isOpen u) w) *
      (PositiveAxisSystem.ell h w.2)⁻¹) = _
  simp only [PositiveAxisSystem.edge, div_eq_mul_inv]
  ring

theorem reconstructed_flux_derivative {S : Set ℝ} {h : ℝ} (d : Domain S h)
    (lam : ℝ) (u : EvenProfile S) {R eta : ℝ} (heta : eta ∈ S) :
    HasDerivAt (fun r => r ^ 2 / 2 * betaFromU d lam u (r, eta))
      (-R * PositiveOrderMoments.radialZ h (-PositiveAxisSystem.a h + lam) u (R, eta)) R := by
  have he : (fun r => r ^ 2 / 2 * betaFromU d lam u (r, eta)) =
      fun r => PositiveOrderMoments.fluxHistory h lam u (r, eta) :=
    funext (fun r => betaFromU_eq_fluxHistory d lam u (w := (r, eta)) heta)
  rw [he]
  exact PositiveOrderMoments.fluxHistory_hasDerivAt_on h lam d.isOpen u.smooth (w := (R, eta)) heta

/-- Time op as an element of `EvenProfile S`. -/
noncomputable def timeOp {S : Set ℝ} {h : ℝ} (d : Domain S h)
    (b : ℝ) (f : EvenProfile S) : EvenProfile S :=
  (-boundConstant S b * f + boundConstant S (SimilarityProfile.D h) * parameter S *
    etaDerivative d.isOpen f + radiusSquared S * xDerivative d.isOpen f) * inverseDenominator d

/-- Axial op as an element of `EvenProfile S`. -/
noncomputable def axialOp {S : Set ℝ} {h : ℝ} (d : Domain S h)
    (b : ℝ) (f : EvenProfile S) : EvenProfile S :=
  (boundConstant S (2 * b) * parameter S * f + (1 - parameter S ^ 2) * etaDerivative d.isOpen f -
    boundConstant S 2 * parameter S * radiusSquared S * xDerivative d.isOpen f) *
        inverseDenominator d

/-- Axial Op2, given by `axialOp d (b - SimilarityProfile.D h) (axialOp d b f)`. -/
noncomputable def axialOp2 {S : Set ℝ} {h : ℝ} (d : Domain S h)
    (b : ℝ) (f : EvenProfile S) : EvenProfile S :=
  axialOp d (b - SimilarityProfile.D h) (axialOp d b f)

/-- Shifted axial as an element of `ℕ → EvenProfile S | 0 => 0 | k + 1 => axialOp2 d
(AxisSourceRegularity.slowOrder h k - 1) (beta k)`. -/
noncomputable def shiftedAxial {S : Set ℝ} {h : ℝ} (d : Domain S h)
    (beta : ℕ → EvenProfile S) : ℕ → EvenProfile S
  | 0 => 0
  | k + 1 => axialOp2 d (AxisSourceRegularity.slowOrder h k - 1) (beta k)

/-- The complete radial source divided by `X`, including both viscous terms. -/
noncomputable def omegaDivX {S : Set ℝ} {h : ℝ} (d : Domain S h)
    (u beta : ℕ → EvenProfile S) (k : ℕ) : EvenProfile S :=
  timeOp d (AxisSourceRegularity.slowOrder h k - 1) (beta k) +
    (∑ ij ∈ Finset.antidiagonal k,
      (beta ij.1 * (boundConstant S (1 / 2) * beta ij.2 + radiusSquared S * xDerivative d.isOpen
          (beta ij.2)) +
       u ij.1 * axialOp d (AxisSourceRegularity.slowOrder h ij.2 - 1) (beta ij.2))) -
    (boundConstant S 4 * xDerivative d.isOpen (beta k) + boundConstant S 2 * radiusSquared S *
      xDerivative d.isOpen (xDerivative d.isOpen (beta k))) - shiftedAxial d beta k

/-- Previous omega div X as an element of `ℕ → EvenProfile S | 0 => 0 | k + 1 => omegaDivX d u
beta k`. -/
noncomputable def previousOmegaDivX {S : Set ℝ} {h : ℝ} (d : Domain S h)
    (u beta : ℕ → EvenProfile S) : ℕ → EvenProfile S
  | 0 => 0
  | k + 1 => omegaDivX d u beta k

/-- Angular field, given by `w.1 / C * phi w`. -/
noncomputable def angularField {S : Set ℝ} (C : ℝ) (phi : EvenProfile S) (w : ℝ × ℝ) : ℝ :=
  w.1 / C * phi w

theorem angularField_smooth {S : Set ℝ} (C : ℝ) (phi : EvenProfile S) :
    Smooth S (angularField C phi) := (contDiffOn_fst.div_const C).mul phi.smooth

/-- Pressure source, given by `boundConstant S (C ^ 2)⁻¹ * (∑ i ∈ Finset.range (n + 1), phi i *
phi (n - i)) - boundConstant S (1 / 2) * omega`. -/
noncomputable def pressureSource {S : Set ℝ} (C : ℝ) (phi : ℕ → EvenProfile S)
    (omega : EvenProfile S) (n : ℕ) : EvenProfile S :=
  boundConstant S (C ^ 2)⁻¹ * (∑ i ∈ Finset.range (n + 1), phi i * phi (n - i)) -
    boundConstant S (1 / 2) * omega

/-- Pressure from source, given by `radiusSquared S * massAverage hS source`. -/
noncomputable def pressureFromSource {S : Set ℝ} (hS : IsOpen S)
    (source : EvenProfile S) : EvenProfile S := radiusSquared S * massAverage hS source

theorem pressureFromSource_eq_primitive {S : Set ℝ} (hS : IsOpen S)
    (source : EvenProfile S) (w : ℝ × ℝ) :
    pressureFromSource hS source w =
      ProfileHistories.primitive (fun p => p.1 * source p) w :=
  (massHistory_eq_massAverage hS source w).symm

theorem actual_pressureGradient {S : Set ℝ} (C : ℝ) (phi : ℕ → EvenProfile S)
    (omega : EvenProfile S) (n : ℕ) (w : ℝ × ℝ) :
    PositiveOrderMoments.jointPressureGradient n (fun j => angularField C (phi j))
      (fun p => p.1 ^ 2 / 2 * omega p) w = w.1 * pressureSource C phi omega n w := by
  have hs : (∑ i ∈ Finset.range (n + 1),
      angularField C (phi i) w * angularField C (phi (n - i)) w) =
      w.1 ^ 2 / C ^ 2 * ∑ i ∈ Finset.range (n + 1), phi i w * phi (n - i) w := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij _
    dsimp [angularField]
    ring
  change ((∑ i ∈ Finset.range (n + 1),
    angularField C (phi i) w * angularField C (phi (n - i)) w) - w.1 ^ 2 / 2 * omega w) / w.1 = _
  rw [hs]
  have hv : (∑ i ∈ Finset.range (n + 1), phi i * phi (n - i)) w =
      ∑ i ∈ Finset.range (n + 1), phi i w * phi (n - i) w := by
    simp only [sum_apply, mul_apply]
  simp only [pressureSource, sub_apply, mul_apply, constant_apply, hv]
  by_cases hR : w.1 = 0
  · simp [hR]
  · field_simp [hR]

theorem pressureFromSource_eq_pressureHistory {S : Set ℝ} (hS : IsOpen S) (C : ℝ)
    (phi : ℕ → EvenProfile S) (omega : EvenProfile S) (n : ℕ) :
    (pressureFromSource hS (pressureSource C phi omega n) : Field) =
      PositiveOrderMoments.pressureHistory n (fun j => angularField C (phi j))
        (fun p => p.1 ^ 2 / 2 * omega p) := by
  funext w
  rw [pressureFromSource_eq_primitive]
  unfold PositiveOrderMoments.pressureHistory
  congr 1
  funext p
  exact (actual_pressureGradient C phi omega n p).symm

/-- Pull a local even axis function to the physical similarity radius. -/
noncomputable def radialLift {rho : ℝ} {U : Set ℂ} (f : SlowRecursion.AxisFunction rho U)
    (w : ℝ × ℝ) : ℝ := (f (w.1 / Real.sqrt 2, (w.2 : ℂ))).re

theorem radialLift_mem {rho R : ℝ} (hrho : 0 < rho) (hR : R ^ 2 / 2 < rho ^ 2) :
    R / Real.sqrt 2 ∈ Ioo (-rho) rho := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have he : (R / Real.sqrt 2) ^ 2 = R ^ 2 / 2 := by rw [div_pow, hs2]
  have hh : (R / Real.sqrt 2) ^ 2 < rho ^ 2 := by rw [he]; exact hR
  exact abs_lt.mp (abs_lt_of_sq_lt_sq hh hrho.le)

/-- Localizing never evaluates derivatives outside the common hierarchy
radius: the cutoff is already zero on a neighborhood of that boundary. -/
noncomputable def cutoffLift {rho : ℝ} {U : Set ℂ} {S : Set ℝ}
    (hrho : 0 < rho) (hU : IsOpen U) (_hS : IsOpen S)
    (hSU : ∀ eta ∈ S, (eta : ℂ) ∈ U)
    {inner stop : ℝ} (his : inner < stop) (hsrho : stop < rho ^ 2)
    (f : SlowRecursion.AxisFunction rho U) : EvenProfile S := by
  refine ⟨fun w => coreCutoff inner stop w * radialLift f w, ⟨?_, ?_⟩⟩
  · intro w hw
    by_cases hR : w.1 ^ 2 / 2 < rho ^ 2
    · have hf := f.smooth.contDiffAt (x := (w.1 / Real.sqrt 2, (w.2 : ℂ))) ((isOpen_Ioo.prod
        hU).mem_nhds
        ⟨radialLift_mem hrho hR, hSU w.2 hw.2⟩)
      have hc : ContDiffAt ℝ ∞ (radialLift f) w :=
        Complex.reCLM.contDiff.contDiffAt.comp w
          (hf.comp w ((contDiffAt_fst.div_const (Real.sqrt 2)).prodMk
            (Complex.ofRealCLM.contDiff.contDiffAt.comp w contDiffAt_snd)))
      exact ((coreCutoff_smooth inner stop).contDiffAt.mul hc).contDiffWithinAt
    · have he : (fun p : ℝ × ℝ => coreCutoff inner stop p * radialLift f p) =ᶠ[𝓝 w]
          fun _ => (0 : ℝ) := by
        have hn : ∀ᶠ p : ℝ × ℝ in 𝓝 w, stop < p.1 ^ 2 / 2 :=
          (isOpen_lt continuous_const ((continuous_fst.pow 2).div_const 2)).mem_nhds
            (hsrho.trans_le (le_of_not_gt hR))
        filter_upwards [hn] with p hp
        rw [coreCutoff_zero his hp.le, zero_mul]
      exact ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × ℝ => (0 : ℝ)) w).congr_of_eventuallyEq
          he).contDiffWithinAt
  · intro eta heta R
    have hcut : coreCutoff inner stop (-R, eta) = coreCutoff inner stop (R, eta) := by
      simp only [coreCutoff, neg_sq]
    rw [hcut]
    by_cases hR : stop ≤ R ^ 2 / 2
    · rw [coreCutoff_zero his hR, zero_mul, zero_mul]
    · have hr := radialLift_mem hrho ((lt_of_not_ge hR).trans hsrho)
      congr 1
      dsimp only [radialLift]
      rw [neg_div, f.even hr (hSU eta heta)]

theorem cutoffLift_eq {rho : ℝ} {U : Set ℂ} {S : Set ℝ}
    (hrho : 0 < rho) (hU : IsOpen U) (hS : IsOpen S) (hSU : ∀ eta ∈ S, (eta : ℂ) ∈ U)
    {inner stop : ℝ} (his : inner < stop) (hsrho : stop < rho ^ 2)
    (f : SlowRecursion.AxisFunction rho U) {w : ℝ × ℝ} (hw : w.1 ^ 2 / 2 ≤ inner) :
    cutoffLift hrho hU hS hSU his hsrho f w = radialLift f w := by
  change coreCutoff inner stop w * radialLift f w = _
  rw [coreCutoff_one his hw, one_mul]

theorem cutoffLift_zero {rho : ℝ} {U : Set ℂ} {S : Set ℝ}
    (hrho : 0 < rho) (hU : IsOpen U) (hS : IsOpen S) (hSU : ∀ eta ∈ S, (eta : ℂ) ∈ U)
    {inner stop : ℝ} (his : inner < stop) (hsrho : stop < rho ^ 2)
    (f : SlowRecursion.AxisFunction rho U) {w : ℝ × ℝ} (hw : stop ≤ w.1 ^ 2 / 2) :
    cutoffLift hrho hU hS hSU his hsrho f w = 0 := by
  change coreCutoff inner stop w * radialLift f w = _
  rw [coreCutoff_zero his hw, zero_mul]

/-- Patch support, given by `∀ eta, tsupport (fun R => f (R, eta)) ⊆ Ioo a b`. -/
noncomputable def PatchSupport (a b : ℝ) (f : Field) : Prop :=
  ∀ eta, tsupport (fun R => f (R, eta)) ⊆ Ioo a b

theorem patch_zero {a b : ℝ} {f : Field} (hs : PatchSupport a b f)
    {R eta : ℝ} (hR : R ∉ Ioo a b) : f (R, eta) = 0 := by
  by_contra hn
  exact hR (hs eta (subset_closure hn))

/-- Even correction as an element of `EvenProfile S`. -/
noncomputable def evenCorrection {S : Set ℝ} {f : Field} (hf : Smooth S f) : EvenProfile S :=
  ⟨fun w => f w + f (-w.1, w.2), ⟨hf.add (hf.comp
    (contDiffOn_fst.neg.prodMk contDiffOn_snd) (fun w hw => ⟨mem_univ _, hw.2⟩)),
    fun _ _ _ => by simp only [neg_neg, add_comm]⟩⟩

/-- Odd angular correction divided by `R`.  The support gap proves
smoothness at zero instead of appealing to a formal cancellation. -/
noncomputable def phiCorrection {S : Set ℝ} (_hS : IsOpen S) {a b : ℝ} (ha : 0 < a)
    {f : Field} (hf : Smooth S f) (hs : PatchSupport a b f) (C : ℝ) : EvenProfile S := by
  refine ⟨fun w => C * (f w - f (-w.1, w.2)) / w.1, ⟨?_, ?_⟩⟩
  · intro w hw
    by_cases hR : w.1 = 0
    · have hn : ∀ᶠ p : ℝ × ℝ in 𝓝 w, |p.1| < a :=
        (isOpen_lt continuous_fst.abs continuous_const).mem_nhds (by simpa [hR] using ha)
      have he : (fun p : ℝ × ℝ => C * (f p - f (-p.1, p.2)) / p.1) =ᶠ[𝓝 w]
          fun _ => (0 : ℝ) := by
        filter_upwards [hn] with p hp
        have h1 := patch_zero hs (eta := p.2) (R := p.1) (by
          intro hh; linarith [(abs_lt.mp hp).2, hh.1])
        have h2 := patch_zero hs (eta := p.2) (R := -p.1) (by
          intro hh; linarith [(abs_lt.mp hp).1, hh.1])
        simp [h1, h2]
      exact ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × ℝ => (0 : ℝ)) w).congr_of_eventuallyEq
          he).contDiffWithinAt
    · have hfr := hf.comp (s := region S) (contDiffOn_fst.neg.prodMk contDiffOn_snd)
        (fun p hp => (show (-p.1, p.2) ∈ region S from ⟨mem_univ _, hp.2⟩))
      exact (contDiffWithinAt_const.mul ((hf w hw).sub (hfr w hw))).div
        contDiffWithinAt_fst hR
  · intro eta _ R
    simp only [neg_neg]
    ring

theorem evenCorrection_nonneg {S : Set ℝ} {a b : ℝ} (ha : 0 < a) {f : Field}
    (hf : Smooth S f) (hs : PatchSupport a b f) {R eta : ℝ} (hR : 0 ≤ R) :
    evenCorrection hf (R, eta) = f (R, eta) := by
  have hz := patch_zero hs (R := -R) (eta := eta) (by intro hh; linarith [hh.1])
  change f (R, eta) + f (-R, eta) = _
  rw [hz, add_zero]

theorem phiCorrection_angular_nonneg {S : Set ℝ} (hS : IsOpen S) {a b : ℝ} (ha : 0 < a)
    {f : Field} (hf : Smooth S f) (hs : PatchSupport a b f) {C : ℝ} (hC : C ≠ 0)
    {R eta : ℝ} (hR : 0 ≤ R) :
    angularField C (phiCorrection hS ha hf hs C) (R, eta) = f (R, eta) := by
  have hz := patch_zero hs (R := -R) (eta := eta) (by intro hh; linarith [hh.1])
  change R / C * (C * (f (R, eta) - f (-R, eta)) / R) = _
  rw [hz, sub_zero]
  rcases hR.eq_or_lt with he | he
  · subst R
    have h0 := patch_zero hs (R := 0) (eta := eta) (by intro hh; linarith [hh.1])
    simp [h0]
  · field_simp [hC, he.ne']

theorem evenCorrection_inner {S : Set ℝ} {a b : ℝ} {f : Field} (hf : Smooth S f)
    (hs : PatchSupport a b f) {R eta : ℝ} (hR : |R| ≤ a) :
    evenCorrection hf (R, eta) = 0 := by
  have hz := patch_zero hs (R := R) (eta := eta) (by
    intro hh; linarith [(abs_le.mp hR).2, hh.1])
  have hn := patch_zero hs (R := -R) (eta := eta) (by
    intro hh; linarith [(abs_le.mp hR).1, hh.1])
  change f (R, eta) + f (-R, eta) = _
  rw [hz, hn, add_zero]

theorem phiCorrection_inner {S : Set ℝ} (hS : IsOpen S) {a b : ℝ} (ha : 0 < a)
    {f : Field} (hf : Smooth S f) (hs : PatchSupport a b f) (C : ℝ)
    {R eta : ℝ} (hR : |R| ≤ a) : phiCorrection hS ha hf hs C (R, eta) = 0 := by
  have hz := patch_zero hs (R := R) (eta := eta) (by
    intro hh; linarith [(abs_le.mp hR).2, hh.1])
  have hn := patch_zero hs (R := -R) (eta := eta) (by
    intro hh; linarith [(abs_le.mp hR).1, hh.1])
  change C * (f (R, eta) - f (-R, eta)) / R = _
  simp [hz, hn]

/-- Exterior: an abbreviation for `SlowStressSupport.exterior`. -/
abbrev Exterior := SlowStressSupport.exterior

theorem exterior_xDerivative {S : Set ℝ} (hS : IsOpen S) (f : EvenProfile S)
    {B : ℝ} (hB : 0 < B) (hf : Exterior B S f) : Exterior B S (xDerivative hS f) := by
  have hd := SlowStressSupport.exterior_dr hS f.smooth hf
  intro eta heta R hR
  have he := radius_mul_xDerivative hS f heta R
  change R * xDerivative hS f (R, eta) = ProfileHistories.radialPartial f (R, eta) at he
  have hz : ProfileHistories.radialPartial f (R, eta) = 0 := hd eta heta R hR
  rw [hz] at he
  exact (mul_eq_zero.mp he).resolve_left (ne_of_gt (hB.trans_le hR))

theorem exterior_etaDerivative {S : Set ℝ} (hS : IsOpen S) (f : EvenProfile S)
    {B : ℝ} (hf : Exterior B S f) : Exterior B S (etaDerivative hS f) :=
  SlowStressSupport.exterior_de hS f.smooth hf

theorem exterior_timeOp {S : Set ℝ} {h : ℝ} (d : Domain S h) (b : ℝ)
    (f : EvenProfile S) {B : ℝ} (hB : 0 < B) (hf : Exterior B S f) :
    Exterior B S (timeOp d b f) := by
  intro eta heta R hR
  simp only [timeOp, mul_apply, add_apply, neg_apply,
    hf eta heta R hR, exterior_xDerivative d.isOpen f hB hf eta heta R hR,
    exterior_etaDerivative d.isOpen f hf eta heta R hR, mul_zero, add_zero, zero_mul]

theorem exterior_axialOp {S : Set ℝ} {h : ℝ} (d : Domain S h) (b : ℝ)
    (f : EvenProfile S) {B : ℝ} (hB : 0 < B) (hf : Exterior B S f) :
    Exterior B S (axialOp d b f) := by
  intro eta heta R hR
  simp [axialOp, hf eta heta R hR, exterior_xDerivative d.isOpen f hB hf eta heta R hR,
    exterior_etaDerivative d.isOpen f hf eta heta R hR]

theorem exterior_axialOp2 {S : Set ℝ} {h : ℝ} (d : Domain S h) (b : ℝ)
    (f : EvenProfile S) {B : ℝ} (hB : 0 < B) (hf : Exterior B S f) :
    Exterior B S (axialOp2 d b f) :=
  exterior_axialOp d _ _ hB (exterior_axialOp d _ _ hB hf)

theorem exterior_omegaDivX {S : Set ℝ} {h : ℝ} (d : Domain S h)
    (u beta : ℕ → EvenProfile S) (k : ℕ) {B : ℝ} (hB : 0 < B)
    (hb : ∀ j ≤ k, Exterior B S (beta j)) : Exterior B S (omegaDivX d u beta k) := by
  intro eta heta R hR
  have hsum : (∑ ij ∈ Finset.antidiagonal k,
      (beta ij.1 * (boundConstant S (1 / 2) * beta ij.2 + radiusSquared S * xDerivative d.isOpen
          (beta ij.2)) +
       u ij.1 * axialOp d (AxisSourceRegularity.slowOrder h ij.2 - 1) (beta ij.2))) (R, eta) = 0 :=
           by
    rw [sum_apply]
    apply Finset.sum_eq_zero
    intro ij hij
    have hi := (AxisSourceRegularity.antidiagonal_indices_le hij).1
    have hj := (AxisSourceRegularity.antidiagonal_indices_le hij).2
    simp [hb _ hi eta heta R hR, exterior_axialOp d _ _ hB (hb _ hj) eta heta R hR]
  have hshift : shiftedAxial d beta k (R, eta) = 0 := by
    cases k with
    | zero => rfl
    | succ k => exact exterior_axialOp2 d _ _ hB (hb k (Nat.le_succ k)) eta heta R hR
  simp only [omegaDivX, sub_apply, add_apply, mul_apply, hsum, hshift,
    exterior_timeOp d _ _ hB (hb k le_rfl) eta heta R hR,
    exterior_xDerivative d.isOpen _ hB (hb k le_rfl) eta heta R hR,
    exterior_xDerivative d.isOpen _ hB (exterior_xDerivative d.isOpen _ hB (hb k le_rfl)) eta heta
        R hR,
    mul_zero, add_zero, sub_zero]

theorem exterior_previousOmegaDivX {S : Set ℝ} {h : ℝ} (d : Domain S h)
    (u beta : ℕ → EvenProfile S) (n : ℕ) {B : ℝ} (hB : 0 < B)
    (hb : ∀ j < n, Exterior B S (beta j)) : Exterior B S (previousOmegaDivX d u beta n) := by
  cases n with
  | zero => intro eta _ R _; rfl
  | succ n => exact exterior_omegaDivX d u beta n hB (fun j hj => hb j (Nat.lt_succ_iff.mpr hj))

theorem exterior_pressureSource {S : Set ℝ} (C : ℝ) (phi : ℕ → EvenProfile S)
    (omega : EvenProfile S) {n : ℕ} (hn : 0 < n) {B : ℝ}
    (hp : ∀ j, 0 < j → j ≤ n → Exterior B S (phi j)) (ho : Exterior B S omega) :
    Exterior B S (pressureSource C phi omega n) := by
  intro eta heta R hR
  have hs : (∑ i ∈ Finset.range (n + 1), phi i * phi (n - i)) (R, eta) = 0 := by
    rw [sum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hi0 : i = 0
    · subst i
      simp [hp n hn le_rfl eta heta R hR]
    · simp [hp i (Nat.pos_of_ne_zero hi0) hin eta heta R hR]
  simp [pressureSource, hs, ho eta heta R hR]

theorem exterior_evenCorrection {S : Set ℝ} {a b B : ℝ} (ha : 0 < a) (hab : a < b)
    (hbB : b ≤ B) {f : Field} (hf : Smooth S f) (hs : PatchSupport a b f) :
    Exterior B S (evenCorrection hf) := by
  intro eta _ R hR
  have hRa : a < R := hab.trans_le (hbB.trans hR)
  rw [evenCorrection_nonneg ha hf hs (ha.trans hRa).le]
  exact patch_zero hs (by intro hh; linarith [hh.2])

theorem exterior_phiCorrection {S : Set ℝ} (hS : IsOpen S) {a b B : ℝ}
    (ha : 0 < a) (hab : a < b) (hbB : b ≤ B) {f : Field} (hf : Smooth S f)
    (hs : PatchSupport a b f) (C : ℝ) : Exterior B S (phiCorrection hS ha hf hs C) := by
  intro eta _ R hR
  have hz := patch_zero hs (R := R) (eta := eta) (by intro hh; linarith [hh.2])
  have hn := patch_zero hs (R := -R) (eta := eta) (by intro hh; linarith [hh.1])
  change C * (f (R, eta) - f (-R, eta)) / R = 0
  simp [hz, hn]

theorem moments_congr_positive {n : ℕ}
    {u e u' e' : PositiveOrderMoments.History} {omega omega' : ℝ → ℝ}
    (hu : ∀ R, 0 < R → ∀ j, u j R = u' j R)
    (he : ∀ R, 0 < R → ∀ j, e j R = e' j R)
    (ho : ∀ R, 0 < R → omega R = omega' R) :
    PositiveOrderMoments.moments n u e omega = PositiveOrderMoments.moments n u' e' omega' := by
  funext i
  apply setIntegral_congr_fun measurableSet_Ioi
  intro R hR
  simp only [PositiveOrderMoments.rowDensity, PositiveOrderMoments.pressureGradient,
    PositiveOrderMoments.cauchy, PositiveAxisSystem.convolution, hu R hR, he R hR, ho R hR]

theorem actual_pressureGradient_smooth {S : Set ℝ} (C : ℝ) (phi : ℕ → EvenProfile S)
    (omega : EvenProfile S) (n : ℕ) :
    Smooth S (PositiveOrderMoments.jointPressureGradient n (fun j => angularField C (phi j))
      (fun p => p.1 ^ 2 / 2 * omega p)) := by
  have he := funext (actual_pressureGradient C phi omega n)
  rw [he]
  exact contDiffOn_fst.mul (pressureSource C phi omega n).smooth

/-- One repair step.  Only actual smooth profiles and their compact exterior
are inputs; the five zero moments are proved by the explicit linear repair. -/
theorem exists_repaired_order {S : Set ℝ} (hS : IsOpen S) {C lam a b B : ℝ}
    (hC : C ≠ 0) (hlam : 0 < lam) (ha : 0 < a) (hab : a < b) (hbB : b ≤ B)
    {n : ℕ} (hn : 0 < n) (u phi : ℕ → EvenProfile S) (omega : EvenProfile S)
    (A : ℝ → ℝ) (hA : ContDiffOn ℝ ∞ A S) (hAn : ∀ eta ∈ S, A eta ≠ 0)
    (hu0 : ∀ eta ∈ S, ∀ R ∈ Ioo a b, u 0 (R, eta) = 0)
    (he0 : ∀ eta ∈ S, ∀ R ∈ Ioo a b,
      angularField C (phi 0) (R, eta) = FiveRowRank.background lam (A eta) R)
    (huB : ∀ j ≤ n, Exterior B S (u j))
    (hpB : ∀ j, 0 < j → j ≤ n → Exterior B S (phi j))
    (hoB : Exterior B S omega) :
    ∃ un phin : EvenProfile S,
      (∀ eta R, |R| ≤ a → un (R, eta) = u n (R, eta)) ∧
      (∀ eta R, |R| ≤ a → phin (R, eta) = phi n (R, eta)) ∧
      Exterior B S un ∧ Exterior B S phin ∧
      (∀ eta R, b ≤ R → un (R, eta) = u n (R, eta)) ∧
      (∀ eta R, b ≤ R → phin (R, eta) = phi n (R, eta)) ∧
      ∀ eta ∈ S, PositiveOrderMoments.moments n
        (PositiveOrderMoments.slice (fun j => (Function.update u n un j : Field)) eta)
        (PositiveOrderMoments.slice (fun j => angularField C (Function.update phi n phin j)) eta)
        (fun R => R ^ 2 / 2 * omega (R, eta)) = 0 := by
  classical
  let uraw : History := fun j => u j
  let eraw : History := fun j => angularField C (phi j)
  let oraw : Field := fun p => p.1 ^ 2 / 2 * omega p
  have hd : ∀ i, Smooth S (fun w => PositiveOrderMoments.jointRowDensity n uraw eraw oraw w i) :=
    PositiveOrderMoments.jointRowDensity_contDiffOn (fun j _ => (u j).smooth)
      (fun j _ => angularField_smooth C (phi j)) (actual_pressureGradient_smooth C phi omega n)
  have hs : ∀ eta ∈ S, ∀ R, B ≤ R →
      PositiveOrderMoments.jointRowDensity n uraw eraw oraw (R, eta) = 0 := by
    intro eta heta R hR
    apply PositiveOrderMoments.jointRowDensity_exterior hn
    · intro j hj
      exact huB j hj eta heta R hR
    · intro j hj hjn
      change R / C * phi j (R, eta) = 0
      rw [hpB j hj hjn eta heta R hR, mul_zero]
    · change R ^ 2 / 2 * omega (R, eta) = 0
      rw [hoB eta heta R hR, mul_zero]
  have hB : 0 < B := ha.trans (hab.trans_le hbB)
  obtain ⟨du, de', hdu, hde, hduS, hdeS, hm⟩ :=
    PositiveOrderMoments.exists_parameterized_exact_repair lam a b hlam ha hab hS hn
      uraw eraw oraw A hA hAn hu0 he0 hd hB.le hs
  let un : EvenProfile S := u n + evenCorrection hdu
  let phin : EvenProfile S := phi n + phiCorrection hS ha hde hdeS C
  refine ⟨un, phin, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro eta R hR
    change u n (R, eta) + evenCorrection hdu (R, eta) = _
    rw [evenCorrection_inner hdu hduS hR, add_zero]
  · intro eta R hR
    change phi n (R, eta) + phiCorrection hS ha hde hdeS C (R, eta) = _
    rw [phiCorrection_inner hS ha hde hdeS C hR, add_zero]
  · intro eta heta R hR
    change u n (R, eta) + evenCorrection hdu (R, eta) = 0
    rw [huB n le_rfl eta heta R hR, exterior_evenCorrection ha hab hbB hdu hduS eta heta R hR,
        add_zero]
  · intro eta heta R hR
    change phi n (R, eta) + phiCorrection hS ha hde hdeS C (R, eta) = 0
    rw [hpB n hn le_rfl eta heta R hR, exterior_phiCorrection hS ha hab hbB hde hdeS C eta heta R
        hR, add_zero]
  · intro eta R hR
    have hz := patch_zero hduS (R := R) (eta := eta) (by intro hh; linarith [hh.2])
    have hn := patch_zero hduS (R := -R) (eta := eta) (by intro hh; linarith [hh.1])
    change u n (R, eta) + (du (R, eta) + du (-R, eta)) = u n (R, eta)
    rw [hz, hn, add_zero, add_zero]
  · intro eta R hR
    have hz := patch_zero hdeS (R := R) (eta := eta) (by intro hh; linarith [hh.2])
    have hn := patch_zero hdeS (R := -R) (eta := eta) (by intro hh; linarith [hh.1])
    change phi n (R, eta) + C * (de' (R, eta) - de' (-R, eta)) / R = phi n (R, eta)
    rw [hz, hn, sub_self, mul_zero, zero_div, add_zero]
  · intro eta heta
    rw [← hm eta heta]
    apply moments_congr_positive
    · intro R hR j
      by_cases hj : j = n
      · subst j
        simp only [PositiveOrderMoments.slice, Function.update_self, PositiveOrderMoments.increment]
        change u n (R, eta) + evenCorrection hdu (R, eta) = u n (R, eta) + du (R, eta)
        rw [evenCorrection_nonneg ha hdu hduS hR.le]
      · simp only [PositiveOrderMoments.slice, Function.update_of_ne hj,
          PositiveOrderMoments.increment]
        rfl
    · intro R hR j
      by_cases hj : j = n
      · subst j
        simp only [PositiveOrderMoments.slice, Function.update_self, PositiveOrderMoments.increment]
        change R / C * (phi n (R, eta) + phiCorrection hS ha hde hdeS C (R, eta)) =
          angularField C (phi n) (R, eta) + de' (R, eta)
        rw [mul_add]
        change _ + angularField C (phiCorrection hS ha hde hdeS C) (R, eta) = _
        rw [phiCorrection_angular_nonneg hS ha hde hdeS hC hR.le]
        rfl
      · simp only [PositiveOrderMoments.slice, Function.update_of_ne hj,
          PositiveOrderMoments.increment]
        rfl
    · intro R _
      rfl

theorem reconstructed_beta_exterior {S : Set ℝ} {h : ℝ} (d : Domain S h)
    (lam : ℝ) (u : EvenProfile S) {B : ℝ} (hB : 0 < B) (hu : Exterior B S u)
    (hm : ∀ eta ∈ S, PositiveOrderMoments.positiveIntegral (fun R => R * u (R, eta)) = 0) :
    Exterior B S (betaFromU d lam u) := by
  intro eta heta R hR
  have hz := PositiveOrderMoments.fluxHistory_exterior_on h lam d.isOpen u.smooth hB.le hu hm hR
      heta
  rw [← betaFromU_eq_fluxHistory d lam u (w := (R, eta)) heta] at hz
  have hR0 : R ≠ 0 := ne_of_gt (hB.trans_le hR)
  exact (mul_eq_zero.mp hz).resolve_left (div_ne_zero (pow_ne_zero 2 hR0) (by norm_num))

theorem reconstructed_pressure_exterior {S : Set ℝ} (hS : IsOpen S) (C : ℝ)
    (u phi : ℕ → EvenProfile S) (omega : EvenProfile S) {n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B)
    (hpB : ∀ j, 0 < j → j ≤ n → Exterior B S (phi j)) (hoB : Exterior B S omega)
    (hm : ∀ eta ∈ S, PositiveOrderMoments.moments n
      (PositiveOrderMoments.slice (fun j => (u j : Field)) eta)
      (PositiveOrderMoments.slice (fun j => angularField C (phi j)) eta)
      (fun R => R ^ 2 / 2 * omega (R, eta)) = 0) :
    Exterior B S (pressureFromSource hS (pressureSource C phi omega n)) := by
  intro eta heta R hR
  have hs : Exterior B S (PositiveOrderMoments.jointPressureGradient n
      (fun j => angularField C (phi j)) (fun p => p.1 ^ 2 / 2 * omega p)) := by
    intro t ht r hr
    rw [actual_pressureGradient, exterior_pressureSource C phi omega hn hpB hoB t ht r hr, mul_zero]
  change (pressureFromSource hS (pressureSource C phi omega n) : Field) (R, eta) = 0
  rw [pressureFromSource_eq_pressureHistory]
  exact PositiveOrderMoments.pressureHistory_exterior_on hB hs hm hR heta

/-- Coefficient data, collecting `phi`, `axial`, `beta`, `pressure`. -/
structure Coefficient (S : Set ℝ) where
  /-- Phi of `Coefficient`, of type `EvenProfile S`. -/
  phi : EvenProfile S
  /-- Axial of `Coefficient`, of type `EvenProfile S`. -/
  axial : EvenProfile S
  /-- Beta of `Coefficient`, of type `EvenProfile S`. -/
  beta : EvenProfile S
  /-- Pressure field of `Coefficient`, of type `EvenProfile S`. -/
  pressure : EvenProfile S

/-- The finite order-zero data and a sequence of localized seeds.  The
constructor `schemeFromHierarchy` below supplies the seeds from one actual
local hierarchy and one common cutoff. -/
structure Scheme (S : Set ℝ) (h C : ℝ) where
  domain : Domain S h
  nonzero_scale : C ≠ 0
  /-- Lam of `Scheme`, of type `ℝ`. -/
  lam : ℝ
  lam_pos : 0 < lam
  /-- A of `Scheme`, of type `ℝ`. -/
  a : ℝ
  /-- B of `Scheme`, of type `ℝ`. -/
  b : ℝ
  /-- Bound parameter of `Scheme`, of type `ℝ`. -/
  B : ℝ
  a_pos : 0 < a
  a_lt_b : a < b
  b_le_B : b ≤ B
  /-- Amplitude of `Scheme`, of type `ℝ → ℝ`. -/
  amplitude : ℝ → ℝ
  amplitude_smooth : ContDiffOn ℝ ∞ amplitude S
  amplitude_ne : ∀ eta ∈ S, amplitude eta ≠ 0
  /-- Base of `Scheme`, of type `Coefficient S`. -/
  base : Coefficient S
  base_axial_exterior : Exterior B S base.axial
  base_beta_exterior : Exterior B S base.beta
  base_axial_patch : ∀ eta ∈ S, ∀ R ∈ Ioo a b, base.axial (R, eta) = 0
  base_angular_patch : ∀ eta ∈ S, ∀ R ∈ Ioo a b,
    angularField C base.phi (R, eta) = FiveRowRank.background lam (amplitude eta) R
  /-- Seed axial of `Scheme`, of type `ℕ → EvenProfile S`. -/
  seedAxial : ℕ → EvenProfile S
  /-- Seed phi of `Scheme`, of type `ℕ → EvenProfile S`. -/
  seedPhi : ℕ → EvenProfile S
  seedAxial_exterior : ∀ n, Exterior B S (seedAxial n)
  seedPhi_exterior : ∀ n, Exterior B S (seedPhi n)

theorem Scheme.B_pos {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) : 0 < s.B :=
  s.a_pos.trans (s.a_lt_b.trans_le s.b_le_B)

/-- Admissible data, collecting `data`, `axial_exterior`, `beta_exterior`, `phi_exterior`,
`pressure_exterior`, `zero_data` and their compatibility conditions. -/
structure Admissible {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) where
  /-- Data of `Admissible`, of type `Coefficient S`. -/
  data : Coefficient S
  axial_exterior : Exterior s.B S data.axial
  beta_exterior : Exterior s.B S data.beta
  phi_exterior : 0 < n → Exterior s.B S data.phi
  pressure_exterior : 0 < n → Exterior s.B S data.pressure
  zero_data : n = 0 → data = s.base
  inner_axial : 0 < n → ∀ eta R, |R| ≤ s.a → data.axial (R, eta) = s.seedAxial n (R, eta)
  inner_phi : 0 < n → ∀ eta R, |R| ≤ s.a → data.phi (R, eta) = s.seedPhi n (R, eta)
  outer_axial : 0 < n → ∀ eta R, s.b ≤ R → data.axial (R, eta) = s.seedAxial n (R, eta)
  outer_phi : 0 < n → ∀ eta R, s.b ≤ R → data.phi (R, eta) = s.seedPhi n (R, eta)

/-- Previous axial, with branches according to `hj : j < n`. -/
noncomputable def previousAxial {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ)
    (previous : (j : ℕ) → j < n → Admissible s j) (j : ℕ) : EvenProfile S :=
  if hj : j < n then (previous j hj).data.axial else s.seedAxial n

/-- Previous phi, with branches according to `hj : j < n`. -/
noncomputable def previousPhi {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ)
    (previous : (j : ℕ) → j < n → Admissible s j) (j : ℕ) : EvenProfile S :=
  if hj : j < n then (previous j hj).data.phi else s.seedPhi n

/-- Previous beta, with branches according to `hj : j < n`. -/
noncomputable def previousBeta {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ)
    (previous : (j : ℕ) → j < n → Admissible s j) (j : ℕ) : EvenProfile S :=
  if hj : j < n then (previous j hj).data.beta else 0

/-- Previous source, given by `previousOmegaDivX s.domain (previousAxial s n previous)
(previousBeta s n previous) n`. -/
noncomputable def previousSource {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ)
    (previous : (j : ℕ) → j < n → Admissible s j) : EvenProfile S :=
  previousOmegaDivX s.domain (previousAxial s n previous) (previousBeta s n previous) n

/-- Step properties, constructed using `out.data.beta`. -/
def StepProperties {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ)
    (previous : (j : ℕ) → j < n → Admissible s j) (out : Admissible s n) : Prop :=
  out.data.beta = betaFromU s.domain (AxisSourceRegularity.slowOrder h n) out.data.axial ∧
  out.data.pressure = pressureFromSource s.domain.isOpen
    (pressureSource C (Function.update (previousPhi s n previous) n out.data.phi)
      (previousSource s n previous) n) ∧
  ∀ eta ∈ S, PositiveOrderMoments.moments n
    (PositiveOrderMoments.slice (fun j =>
      (Function.update (previousAxial s n previous) n out.data.axial j : Field)) eta)
    (PositiveOrderMoments.slice (fun j =>
      angularField C (Function.update (previousPhi s n previous) n out.data.phi j)) eta)
    (fun R => R ^ 2 / 2 * previousSource s n previous (R, eta)) = 0

theorem exists_step {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ} (hn : 0 < n)
    (previous : (j : ℕ) → j < n → Admissible s j) :
    ∃ out : Admissible s n, StepProperties s n previous out := by
  classical
  let u := previousAxial s n previous
  let p := previousPhi s n previous
  let o := previousSource s n previous
  have hu : ∀ j ≤ n, Exterior s.B S (u j) := by
    intro j _
    dsimp [u, previousAxial]
    split_ifs with hj
    · exact (previous j hj).axial_exterior
    · exact s.seedAxial_exterior n
  have hp : ∀ j, 0 < j → j ≤ n → Exterior s.B S (p j) := by
    intro j hj0 _
    dsimp [p, previousPhi]
    split_ifs with hj
    · exact (previous j hj).phi_exterior hj0
    · exact s.seedPhi_exterior n
  have ho : Exterior s.B S o := by
    apply exterior_previousOmegaDivX s.domain _ _ n s.B_pos
    intro j hj
    simpa only [previousBeta, dite_eq_left hj] using (previous j hj).beta_exterior
  have hu0 : u 0 = s.base.axial := by
    dsimp [u, previousAxial]
    rw [dite_eq_left hn, (previous 0 hn).zero_data rfl]
  have hp0 : p 0 = s.base.phi := by
    dsimp [p, previousPhi]
    rw [dite_eq_left hn, (previous 0 hn).zero_data rfl]
  obtain ⟨un, pn, hui, hpi, hue, hpe, huo, hpo, hm⟩ := exists_repaired_order s.domain.isOpen
    s.nonzero_scale s.lam_pos s.a_pos s.a_lt_b s.b_le_B hn u p o s.amplitude
    s.amplitude_smooth s.amplitude_ne
    (by simpa only [hu0] using s.base_axial_patch)
    (by simpa only [hp0] using s.base_angular_patch) hu hp ho
  let b := betaFromU s.domain (AxisSourceRegularity.slowOrder h n) un
  let pressure := pressureFromSource s.domain.isOpen (pressureSource C (Function.update p n pn) o n)
  have hmass : ∀ eta ∈ S,
      PositiveOrderMoments.positiveIntegral (fun R => R * un (R, eta)) = 0 := by
    intro eta heta
    have hm0 := congrFun (hm eta heta) 0
    simpa only [PositiveOrderMoments.moments, PositiveOrderMoments.rowDensity,
      PositiveOrderMoments.slice, Function.update_self, Matrix.cons_val_zero, Pi.zero_apply] using
          hm0
  have hbe : Exterior s.B S b := reconstructed_beta_exterior s.domain _ un s.B_pos hue hmass
  have hpu : ∀ j, 0 < j → j ≤ n → Exterior s.B S (Function.update p n pn j) := by
    intro j hj hjn
    by_cases he : j = n
    · subst j; simpa only [Function.update_self] using hpe
    · simpa only [Function.update_of_ne he] using hp j hj hjn
  have hpre : Exterior s.B S pressure :=
    reconstructed_pressure_exterior s.domain.isOpen C (Function.update u n un)
      (Function.update p n pn) o hn s.B_pos.le hpu ho hm
  let out : Admissible s n := {
    data := ⟨pn, un, b, pressure⟩
    axial_exterior := hue
    beta_exterior := hbe
    phi_exterior := fun _ => hpe
    pressure_exterior := fun _ => hpre
    zero_data := fun hz => (Nat.ne_of_gt hn hz).elim
    inner_axial := by
      intro _ eta R hR
      have hi := hui eta R hR
      simpa only [u, previousAxial, dite_eq_right (lt_irrefl n)] using hi
    inner_phi := by
      intro _ eta R hR
      have hi := hpi eta R hR
      simpa only [p, previousPhi, dite_eq_right (lt_irrefl n)] using hi
    outer_axial := by
      intro _ eta R hR
      have ho := huo eta R hR
      simpa only [u, previousAxial, dite_eq_right (lt_irrefl n)] using ho
    outer_phi := by
      intro _ eta R hR
      have ho := hpo eta R hR
      simpa only [p, previousPhi, dite_eq_right (lt_irrefl n)] using ho }
  exact ⟨out, rfl, rfl, hm⟩

/-- Step, given by `Classical.choose (exists_step s hn previous)`. -/
noncomputable def step {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ} (hn : 0 < n)
    (previous : (j : ℕ) → j < n → Admissible s j) : Admissible s n :=
  Classical.choose (exists_step s hn previous)

theorem step_spec {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ} (hn : 0 < n)
    (previous : (j : ℕ) → j < n → Admissible s j) :
    StepProperties s n previous (step s hn previous) :=
  Classical.choose_spec (exists_step s hn previous)

/-- Recursion step used in global slow profiles. -/
noncomputable def recursionStep {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) :
    (n : ℕ) → ((j : ℕ) → j < n → Admissible s j) → Admissible s n
  | 0, _ => {
      data := s.base
      axial_exterior := s.base_axial_exterior
      beta_exterior := s.base_beta_exterior
      phi_exterior := fun hn => (Nat.lt_irrefl 0 hn).elim
      pressure_exterior := fun hn => (Nat.lt_irrefl 0 hn).elim
      zero_data := fun _ => rfl
      inner_axial := fun hn => (Nat.lt_irrefl 0 hn).elim
      inner_phi := fun hn => (Nat.lt_irrefl 0 hn).elim
      outer_axial := fun hn => (Nat.lt_irrefl 0 hn).elim
      outer_phi := fun hn => (Nat.lt_irrefl 0 hn).elim }
  | n + 1, previous => step s (Nat.succ_pos n) previous

/-- A single coherent infinite sequence, constructed by well-founded
recursion; all coefficient indices used in the radial source are smaller. -/
noncomputable def sequence {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) :
    Admissible s n := Nat.lt_wfRel.wf.fix (recursionStep s) n

/-- Profiles, given by `(sequence s n).data`. -/
noncomputable def profiles {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) : Coefficient S :=
  (sequence s n).data

theorem sequence_succ {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) :
    sequence s (n + 1) = step s (Nat.succ_pos n) (fun j _ => sequence s j) := by
  unfold sequence
  rw [WellFounded.fix_eq]
  rfl

theorem profiles_zero {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) : profiles s 0 = s.base :=
  (sequence s 0).zero_data rfl

theorem profiles_axial_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) :
    Exterior s.B S (profiles s n).axial := (sequence s n).axial_exterior

theorem profiles_beta_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) :
    Exterior s.B S (profiles s n).beta := (sequence s n).beta_exterior

theorem profiles_phi_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ} (hn : 0 < n) :
    Exterior s.B S (profiles s n).phi := (sequence s n).phi_exterior hn

theorem profiles_pressure_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ} (hn : 0 < n) :
    Exterior s.B S (profiles s n).pressure := (sequence s n).pressure_exterior hn

theorem profiles_inner_axial {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ} (hn : 0 < n)
    {R eta : ℝ} (hR : |R| ≤ s.a) : (profiles s n).axial (R, eta) = s.seedAxial n (R, eta) :=
  (sequence s n).inner_axial hn eta R hR

theorem profiles_inner_phi {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ} (hn : 0 < n)
    {R eta : ℝ} (hR : |R| ≤ s.a) : (profiles s n).phi (R, eta) = s.seedPhi n (R, eta) :=
  (sequence s n).inner_phi hn eta R hR

/-- Positive-order repairs preserve the actual seed beyond the repair patch.
This property is retained in the predicate used to select each step. -/
theorem profiles_outer_axial {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ} (hn : 0 < n)
    {R eta : ℝ} (hR : s.b ≤ R) : (profiles s n).axial (R, eta) = s.seedAxial n (R, eta) :=
  (sequence s n).outer_axial hn eta R hR

theorem profiles_outer_phi {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ} (hn : 0 < n)
    {R eta : ℝ} (hR : s.b ≤ R) : (profiles s n).phi (R, eta) = s.seedPhi n (R, eta) :=
  (sequence s n).outer_phi hn eta R hR

theorem omegaDivX_congr_prefix {S : Set ℝ} {h : ℝ} (d : Domain S h)
    {u beta u' beta' : ℕ → EvenProfile S} (k : ℕ)
    (hu : ∀ j ≤ k, u j = u' j) (hb : ∀ j ≤ k, beta j = beta' j) :
    omegaDivX d u beta k = omegaDivX d u' beta' k := by
  have hs : shiftedAxial d beta k = shiftedAxial d beta' k := by
    cases k with
    | zero => rfl
    | succ k => simp only [shiftedAxial, hb k (Nat.le_succ k)]
  have hsum : (∑ ij ∈ Finset.antidiagonal k,
      (beta ij.1 * (boundConstant S (1 / 2) * beta ij.2 + radiusSquared S * xDerivative d.isOpen
          (beta ij.2)) +
       u ij.1 * axialOp d (AxisSourceRegularity.slowOrder h ij.2 - 1) (beta ij.2))) =
      (∑ ij ∈ Finset.antidiagonal k,
      (beta' ij.1 * (boundConstant S (1 / 2) * beta' ij.2 + radiusSquared S * xDerivative d.isOpen
          (beta' ij.2)) +
       u' ij.1 * axialOp d (AxisSourceRegularity.slowOrder h ij.2 - 1) (beta' ij.2))) := by
    apply Finset.sum_congr rfl
    intro ij hij
    have hi := AxisSourceRegularity.antidiagonal_indices_le hij
    rw [hb _ hi.1, hb _ hi.2, hu _ hi.1]
  simp only [omegaDivX, hsum, hs, hb k le_rfl]

theorem previousOmegaDivX_congr_prefix {S : Set ℝ} {h : ℝ} (d : Domain S h)
    {u beta u' beta' : ℕ → EvenProfile S} (n : ℕ)
    (hu : ∀ j < n, u j = u' j) (hb : ∀ j < n, beta j = beta' j) :
    previousOmegaDivX d u beta n = previousOmegaDivX d u' beta' n := by
  cases n with
  | zero => rfl
  | succ n =>
    exact omegaDivX_congr_prefix d n (fun j hj => hu j (Nat.lt_succ_iff.mpr hj))
      (fun j hj => hb j (Nat.lt_succ_iff.mpr hj))

theorem pressureSource_congr_prefix {S : Set ℝ} (C : ℝ) {phi phi' : ℕ → EvenProfile S}
    (omega : EvenProfile S) (n : ℕ) (hp : ∀ j ≤ n, phi j = phi' j) :
    pressureSource C phi omega n = pressureSource C phi' omega n := by
  have he : (∑ i ∈ Finset.range (n + 1), phi i * phi (n - i)) =
      ∑ i ∈ Finset.range (n + 1), phi' i * phi' (n - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hp i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)), hp (n - i) (Nat.sub_le _ _)]
  simp only [pressureSource, he]

theorem cauchy_congr_prefix {u e u' e' : PositiveOrderMoments.History} (n : ℕ) (R : ℝ)
    (hu : ∀ j ≤ n, u j R = u' j R) (he : ∀ j ≤ n, e j R = e' j R) :
    PositiveOrderMoments.cauchy n u e R = PositiveOrderMoments.cauchy n u' e' R := by
  unfold PositiveOrderMoments.cauchy PositiveAxisSystem.convolution
  apply Finset.sum_congr rfl
  intro i hi
  change u i R * e (n - i) R = u' i R * e' (n - i) R
  rw [hu i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)), he (n - i) (Nat.sub_le _ _)]

theorem moments_congr_prefix {n : ℕ}
    {u e u' e' : PositiveOrderMoments.History} {omega omega' : ℝ → ℝ}
    (hu : ∀ R, 0 < R → ∀ j ≤ n, u j R = u' j R)
    (he : ∀ R, 0 < R → ∀ j ≤ n, e j R = e' j R)
    (ho : ∀ R, 0 < R → omega R = omega' R) :
    PositiveOrderMoments.moments n u e omega = PositiveOrderMoments.moments n u' e' omega' := by
  funext i
  apply setIntegral_congr_fun measurableSet_Ioi
  intro R hR
  simp only [PositiveOrderMoments.rowDensity, PositiveOrderMoments.pressureGradient,
    cauchy_congr_prefix n R (hu R hR) (he R hR), cauchy_congr_prefix n R (hu R hR) (hu R hR),
    cauchy_congr_prefix n R (he R hR) (he R hR), hu R hR n le_rfl, he R hR n le_rfl, ho R hR]

theorem sequence_step_spec {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ} (hn : 0 < n) :
    StepProperties s n (fun j _ => sequence s j) (sequence s n) := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n => rw [sequence_succ]; exact step_spec s _ _

theorem previousSource_sequence {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ) :
    previousSource s n (fun j _ => sequence s j) =
      previousOmegaDivX s.domain (fun j => (profiles s j).axial) (fun j => (profiles s j).beta) n
          := by
  apply previousOmegaDivX_congr_prefix
  · intro j hj
    simp only [previousAxial, dite_eq_left hj, profiles]
  · intro j hj
    simp only [previousBeta, dite_eq_left hj, profiles]

theorem updated_sequence_axial {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ)
    {j : ℕ} (hj : j ≤ n) :
    Function.update (previousAxial s n (fun k _ => sequence s k)) n (profiles s n).axial j =
      (profiles s j).axial := by
  by_cases he : j = n
  · subst j; rw [Function.update_self]
  · rw [Function.update_of_ne he]
    have hjn : j < n := lt_of_le_of_ne hj he
    simp only [previousAxial, dite_eq_left hjn, profiles]

theorem updated_sequence_phi {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (n : ℕ)
    {j : ℕ} (hj : j ≤ n) :
    Function.update (previousPhi s n (fun k _ => sequence s k)) n (profiles s n).phi j =
      (profiles s j).phi := by
  by_cases he : j = n
  · subst j; rw [Function.update_self]
  · rw [Function.update_of_ne he]
    have hjn : j < n := lt_of_le_of_ne hj he
    simp only [previousPhi, dite_eq_left hjn, profiles]

/-- All five actual total rows hold at every positive order of the same
infinite sequence.  The source is recomputed from that sequence's lower fields. -/
theorem profiles_moments {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ} (hn : 0 < n)
    {eta : ℝ} (heta : eta ∈ S) :
    PositiveOrderMoments.moments n
      (PositiveOrderMoments.slice (fun j => ((profiles s j).axial : Field)) eta)
      (PositiveOrderMoments.slice (fun j => angularField C (profiles s j).phi) eta)
      (fun R => R ^ 2 / 2 * previousOmegaDivX s.domain
        (fun j => (profiles s j).axial) (fun j => (profiles s j).beta) n (R, eta)) = 0 := by
  have hm := (sequence_step_spec s hn).2.2 eta heta
  rw [← hm]
  apply moments_congr_prefix
  · intro R _ j hj
    exact congrArg (fun f : EvenProfile S => f (R, eta)) (updated_sequence_axial s n hj).symm
  · intro R _ j hj
    exact congrArg (fun f : EvenProfile S => angularField C f (R, eta)) (updated_sequence_phi s n
        hj).symm
  · intro R _
    rw [previousSource_sequence]

theorem profiles_beta_eq {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ} (hn : 0 < n) :
    (profiles s n).beta = betaFromU s.domain (AxisSourceRegularity.slowOrder h n) (profiles s
        n).axial :=
  (sequence_step_spec s hn).1

theorem profiles_pressure_eq {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) {n : ℕ} (hn : 0 < n) :
    (profiles s n).pressure = pressureFromSource s.domain.isOpen
      (pressureSource C (fun j => (profiles s j).phi)
        (previousOmegaDivX s.domain (fun j => (profiles s j).axial)
          (fun j => (profiles s j).beta) n) n) := by
  have hp := (sequence_step_spec s hn).2.1
  change (profiles s n).pressure = _ at hp
  rw [previousSource_sequence] at hp
  exact hp.trans (congrArg (pressureFromSource s.domain.isOpen)
    (pressureSource_congr_prefix C _ n (fun j hj => updated_sequence_phi s n hj)))

/-- Data required from the actual order-zero construction.  No positive-order
equations, moments, or extension properties are assumed here. -/
structure BaseData (S : Set ℝ) (C lam a b B : ℝ) where
  /-- Fields of `BaseData`, of type `Coefficient S`. -/
  fields : Coefficient S
  axial_exterior : Exterior B S fields.axial
  beta_exterior : Exterior B S fields.beta
  /-- Amplitude of `BaseData`, of type `ℝ → ℝ`. -/
  amplitude : ℝ → ℝ
  amplitude_smooth : ContDiffOn ℝ ∞ amplitude S
  amplitude_ne : ∀ eta ∈ S, amplitude eta ≠ 0
  axial_patch : ∀ eta ∈ S, ∀ R ∈ Ioo a b, fields.axial (R, eta) = 0
  angular_patch : ∀ eta ∈ S, ∀ R ∈ Ioo a b,
    angularField C fields.phi (R, eta) = FiveRowRank.background lam (amplitude eta) R

/-- The common cutoff is chosen strictly inside the hierarchy's proved
radius; the moment patch begins beyond that cutoff. -/
noncomputable def schemeFromHierarchy {rho : ℝ} {U : Set ℂ} {S : Set ℝ}
    {h C lam inner stop a b B : ℝ} {base : Fin 5 → SimilarityProfile.InnerProfile}
    (A : SlowRecursion.LocalHierarchy rho U h C base)
    (hrho : 0 < rho) (hU : IsOpen U) (d : Domain S h)
    (hSU : ∀ eta ∈ S, (eta : ℂ) ∈ U) (hC : C ≠ 0) (hlam : 0 < lam)
    (his : inner < stop) (hsrho : stop < rho ^ 2) (hsa : stop < a ^ 2 / 2)
    (ha : 0 < a) (hab : a < b) (hbB : b ≤ B) (B0 : BaseData S C lam a b B) : Scheme S h C where
  domain := d
  nonzero_scale := hC
  lam := lam
  lam_pos := hlam
  a := a
  b := b
  B := B
  a_pos := ha
  a_lt_b := hab
  b_le_B := hbB
  amplitude := B0.amplitude
  amplitude_smooth := B0.amplitude_smooth
  amplitude_ne := B0.amplitude_ne
  base := B0.fields
  base_axial_exterior := B0.axial_exterior
  base_beta_exterior := B0.beta_exterior
  base_axial_patch := B0.axial_patch
  base_angular_patch := B0.angular_patch
  seedAxial n := cutoffLift hrho hU d.isOpen hSU his hsrho (A.coefficients n 1)
  seedPhi n := cutoffLift hrho hU d.isOpen hSU his hsrho (A.coefficients n 0)
  seedAxial_exterior n := by
    intro eta _ R hR
    apply cutoffLift_zero
    have haR : a ≤ R := hab.le.trans (hbB.trans hR)
    have hs : a ^ 2 ≤ R ^ 2 := (sq_le_sq₀ ha.le (ha.le.trans haR)).2 haR
    linarith
  seedPhi_exterior n := by
    intro eta _ R hR
    apply cutoffLift_zero
    have haR : a ≤ R := hab.le.trans (hbB.trans hR)
    have hs : a ^ 2 ≤ R ^ 2 := (sq_le_sq₀ ha.le (ha.le.trans haR)).2 haR
    linarith

/-- The actual squared-radius profile.  We use ordinary derivatives only
at positive X; the axis jets are the right jets of this descent. -/
noncomputable def xProfile {S : Set ℝ} (f : EvenProfile S) (w : ℝ × ℝ) : ℝ :=
  f (Real.sqrt (2 * w.1), w.2)

theorem xProfile_radius {S : Set ℝ} (f : EvenProfile S) {R : ℝ} (hR : 0 ≤ R) (eta : ℝ) :
    xProfile f (R ^ 2 / 2, eta) = f (R, eta) := by
  simp only [xProfile, show 2 * (R ^ 2 / 2) = R ^ 2 by ring, Real.sqrt_sq hR]

theorem xProfile_contDiffAt {S : Set ℝ} (hS : IsOpen S) (f : EvenProfile S)
    {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) : ContDiffAt ℝ ∞ (xProfile f) w := by
  have hf := f.smooth.contDiffAt (x := (Real.sqrt (2 * w.1), w.2))
    ((isOpen_univ.prod hS).mem_nhds ⟨mem_univ _, heta⟩)
  exact hf.comp w (((Real.contDiffAt_sqrt (ne_of_gt (mul_pos (by norm_num) hX))).comp w
    (contDiffAt_const.mul contDiffAt_fst)).prodMk contDiffAt_snd)

theorem partialX_hasDerivAt {f : Field} {w : ℝ × ℝ} (hf : DifferentiableAt ℝ f w) :
    HasDerivAt (fun X => f (X, w.2)) (SimilarityProfile.partialX f w) w.1 := by
  simpa only [SimilarityProfile.partialX, Function.comp_def, id_eq, Prod.eta] using
    hf.hasFDerivAt.comp_hasDerivAt w.1 ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))

theorem partialEta_hasDerivAt {f : Field} {w : ℝ × ℝ} (hf : DifferentiableAt ℝ f w) :
    HasDerivAt (fun eta => f (w.1, eta)) (SimilarityProfile.partialEta f w) w.2 := by
  simpa only [SimilarityProfile.partialEta, Function.comp_def, id_eq, Prod.eta] using
    hf.hasFDerivAt.comp_hasDerivAt w.2 ((hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id w.2))

theorem xProfile_partialEta {S : Set ℝ} (hS : IsOpen S) (f : EvenProfile S)
    {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    SimilarityProfile.partialEta (xProfile f) w = xProfile (etaDerivative hS f) w :=
  (partialEta_hasDerivAt ((xProfile_contDiffAt hS f hX heta).differentiableAt (by simp))).unique
    (parameter_derivative hS f.smooth heta (Real.sqrt (2 * w.1)))

theorem xProfile_partialX {S : Set ℝ} (hS : IsOpen S) (f : EvenProfile S)
    {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    SimilarityProfile.partialX (xProfile f) w = xProfile (xDerivative hS f) w := by
  let R := Real.sqrt (2 * w.1)
  have hR : R ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (mul_pos (by norm_num) hX))
  have hd := ProfileHistories.radialPartial_hasDerivAt (PositiveOrderMoments.parameterDomain S hS)
    f.smooth (p := (R, w.2)) ⟨mem_univ _, heta⟩
  have hs : HasDerivAt (fun X : ℝ => Real.sqrt (2 * X)) (1 / R) w.1 := by
    convert! (Real.hasDerivAt_sqrt (ne_of_gt (mul_pos (by norm_num) hX))).scomp w.1
      ((hasDerivAt_id w.1).const_mul 2) using 1
    dsimp [R]
    field_simp
  have hc := hd.scomp w.1 hs
  have hx := radius_mul_xDerivative hS f heta R
  change R * xDerivative hS f (R, w.2) = ProfileHistories.radialPartial f (R, w.2) at hx
  rw [← hx] at hc
  have he : (1 / R) • (R * xDerivative hS f (R, w.2)) = xDerivative hS f (R, w.2) := by
    rw [smul_eq_mul]
    field_simp
  rw [he] at hc
  exact (partialX_hasDerivAt ((xProfile_contDiffAt hS f hX heta).differentiableAt (by
      simp))).unique hc

theorem xProfile_partialX_germ {S : Set ℝ} (hS : IsOpen S) (f : EvenProfile S)
    {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    SimilarityProfile.partialX (xProfile f) =ᶠ[𝓝 w] xProfile (xDerivative hS f) := by
  filter_upwards [(isOpen_Ioi.prod hS).mem_nhds ⟨hX, heta⟩] with p hp
  exact xProfile_partialX hS f hp.1 hp.2

theorem xProfile_partialXX {S : Set ℝ} (hS : IsOpen S) (f : EvenProfile S)
    {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    SimilarityProfile.partialX (SimilarityProfile.partialX (xProfile f)) w =
      xProfile (xDerivative hS (xDerivative hS f)) w := by
  have he := (xProfile_partialX_germ hS f hX heta).fderiv_eq (𝕜 := ℝ)
  change (fderiv ℝ _ w) (1, 0) = _
  rw [he]
  exact xProfile_partialX hS (xDerivative hS f) hX heta

@[simp] theorem xProfile_add {S : Set ℝ} (f g : EvenProfile S) (w : ℝ × ℝ) :
    xProfile (f + g) w = xProfile f w + xProfile g w := rfl
@[simp] theorem xProfile_sub {S : Set ℝ} (f g : EvenProfile S) (w : ℝ × ℝ) :
    xProfile (f - g) w = xProfile f w - xProfile g w := rfl
@[simp] theorem xProfile_mul {S : Set ℝ} (f g : EvenProfile S) (w : ℝ × ℝ) :
    xProfile (f * g) w = xProfile f w * xProfile g w := rfl
@[simp] theorem xProfile_constant (S : Set ℝ) (c : ℝ) (w : ℝ × ℝ) :
    xProfile (boundConstant S c) w = c := rfl

theorem xProfile_radiusSquared (S : Set ℝ) {w : ℝ × ℝ} (hX : 0 ≤ w.1) :
    xProfile (radiusSquared S) w = w.1 := by
  change (Real.sqrt (2 * w.1)) ^ 2 / 2 = w.1
  rw [Real.sq_sqrt (mul_nonneg (by norm_num) hX)]
  ring

theorem xProfile_timeOp {S : Set ℝ} {h : ℝ} (d : Domain S h) (b : ℝ) (f : EvenProfile S)
    {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    xProfile (timeOp d b f) w = SimilarityProfile.T h b (xProfile f) w := by
  simp only [timeOp, xProfile_mul, xProfile_add, xProfile_constant,
    SimilarityProfile.T, CoordinateAlgebra.timeCoeff,
    xProfile_partialEta d.isOpen f hX heta, xProfile_partialX d.isOpen f hX heta,
    xProfile_radiusSquared S hX.le]
  change (-b * xProfile f w + SimilarityProfile.D h * w.2 * xProfile (etaDerivative d.isOpen f) w +
    w.1 * xProfile (xDerivative d.isOpen f) w) * (PositiveAxisSystem.ell h w.2)⁻¹ = _
  rfl

theorem xProfile_axialOp {S : Set ℝ} {h : ℝ} (d : Domain S h) (b : ℝ) (f : EvenProfile S)
    {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    xProfile (axialOp d b f) w = SimilarityProfile.Z h b (xProfile f) w := by
  simp only [axialOp, xProfile_mul, xProfile_add, xProfile_sub, xProfile_constant,
    SimilarityProfile.Z, CoordinateAlgebra.axialCoeff,
    xProfile_partialEta d.isOpen f hX heta, xProfile_partialX d.isOpen f hX heta,
    xProfile_radiusSquared S hX.le]
  change (2 * b * w.2 * xProfile f w + (1 - w.2 ^ 2) * xProfile (etaDerivative d.isOpen f) w -
    2 * w.2 * w.1 * xProfile (xDerivative d.isOpen f) w) * (PositiveAxisSystem.ell h w.2)⁻¹ = _
  simp only [PositiveAxisSystem.ell, CoordinateAlgebra.L, CoordinateAlgebra.d, div_eq_mul_inv]
  ring

theorem xProfile_axialOp_germ {S : Set ℝ} {h : ℝ} (d : Domain S h) (b : ℝ) (f : EvenProfile S)
    {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    xProfile (axialOp d b f) =ᶠ[𝓝 w] SimilarityProfile.Z h b (xProfile f) := by
  filter_upwards [(isOpen_Ioi.prod d.isOpen).mem_nhds ⟨hX, heta⟩] with p hp
  exact xProfile_axialOp d b f hp.1 hp.2

theorem xProfile_axialOp2 {S : Set ℝ} {h : ℝ} (d : Domain S h) (b : ℝ) (f : EvenProfile S)
    {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    xProfile (axialOp2 d b f) w = AxisSourceRegularity.Z2 h b (xProfile f) w := by
  rw [axialOp2, xProfile_axialOp d _ _ hX heta]
  exact AxisSourceRegularity.Z_congr_germ h _ (xProfile_axialOp_germ d b f hX heta)

theorem xProfile_previousOmegaDivX {S : Set ℝ} {h : ℝ} (d : Domain S h)
    (u beta : ℕ → EvenProfile S) (n : ℕ) {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    xProfile (previousOmegaDivX d u beta n) w =
      AxisSourceRegularity.previousOmegaDivX h (fun j => xProfile (u j))
        (fun j => xProfile (beta j)) n w := by
  cases n with
  | zero => rfl
  | succ k =>
    have hsum (q : ℕ × ℕ → EvenProfile S) : xProfile (∑ ij ∈ Finset.antidiagonal k, q ij) w =
        ∑ ij ∈ Finset.antidiagonal k, xProfile (q ij) w := sum_apply _ q _
    have hs : xProfile (shiftedAxial d beta k) w =
        AxisSourceRegularity.shiftedAxialFactor h (fun j => xProfile (beta j)) k w := by
      cases k with
      | zero => rfl
      | succ k => exact xProfile_axialOp2 d _ _ hX heta
    simp only [previousOmegaDivX, AxisSourceRegularity.previousOmegaDivX, omegaDivX,
      AxisSourceRegularity.omegaDivX, xProfile_sub, xProfile_add, xProfile_mul,
      xProfile_constant, hsum, hs, xProfile_timeOp d _ _ hX heta,
      xProfile_radiusSquared S hX.le]
    simp only [
      xProfile_axialOp d _ _ hX heta, xProfile_partialX d.isOpen _ hX heta,
      xProfile_partialXX d.isOpen _ hX heta]
    congr 3
    apply Finset.sum_congr rfl
    intro ij _
    ring

theorem cutoffLift_xProfile {rho : ℝ} {U : Set ℂ} {S : Set ℝ}
    (hrho : 0 < rho) (hU : IsOpen U) (hS : IsOpen S) (hSU : ∀ eta ∈ S, (eta : ℂ) ∈ U)
    {inner stop : ℝ} (his : inner < stop) (hsrho : stop < rho ^ 2)
    (f : SlowRecursion.AxisFunction rho U) {w : ℝ × ℝ}
    (hX : 0 ≤ w.1) (hi : w.1 ≤ inner) :
    xProfile (cutoffLift hrho hU hS hSU his hsrho f) w = SlowRecursion.profile f w := by
  have hs : (Real.sqrt (2 * w.1)) ^ 2 / 2 = w.1 := by
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hX)]; ring
  unfold xProfile
  rw [cutoffLift_eq hrho hU hS hSU his hsrho f (by simpa only [hs] using hi)]
  change (f (Real.sqrt (2 * w.1) / Real.sqrt 2, (w.2 : ℂ))).re =
    (f (Real.sqrt w.1, (w.2 : ℂ))).re
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hz : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [mul_div_cancel_left₀ _ hz]

/-- A transparent interface supplied by the common cutoff constructor. -/
structure Localization {S : Set ℝ} {h C rho : ℝ} {U : Set ℂ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} (s : Scheme S h C)
    (A : SlowRecursion.LocalHierarchy rho U h C base) (inner : ℝ) : Prop where
  radius_pos : 0 < rho
  parameter_open : IsOpen U
  parameter_embedding : ∀ eta ∈ S, (eta : ℂ) ∈ U
  inner_pos : 0 < inner
  inner_radius : inner < rho ^ 2
  inner_patch : inner < s.a ^ 2 / 2
  axial_seed : ∀ n w, 0 ≤ w.1 → w.1 ≤ inner →
    xProfile (s.seedAxial n) w = SlowRecursion.profile (A.coefficients n 1) w
  phi_seed : ∀ n w, 0 ≤ w.1 → w.1 ≤ inner →
    xProfile (s.seedPhi n) w = SlowRecursion.profile (A.coefficients n 0) w

theorem localizationFromHierarchy {rho : ℝ} {U : Set ℂ} {S : Set ℝ}
    {h C lam inner stop a b B : ℝ} {base : Fin 5 → SimilarityProfile.InnerProfile}
    (A : SlowRecursion.LocalHierarchy rho U h C base)
    (hrho : 0 < rho) (hU : IsOpen U) (d : Domain S h)
    (hSU : ∀ eta ∈ S, (eta : ℂ) ∈ U) (hC : C ≠ 0) (hlam : 0 < lam)
    (hi : 0 < inner) (his : inner < stop) (hsrho : stop < rho ^ 2) (hsa : stop < a ^ 2 / 2)
    (ha : 0 < a) (hab : a < b) (hbB : b ≤ B) (B0 : BaseData S C lam a b B) :
    Localization (schemeFromHierarchy A hrho hU d hSU hC hlam his hsrho hsa ha hab hbB B0) A inner
        := by
  refine ⟨hrho, hU, hSU, hi, his.trans hsrho, his.trans hsa, ?_, ?_⟩
  · intro n w hX hwi
    exact cutoffLift_xProfile hrho hU d.isOpen hSU his hsrho (A.coefficients n 1) hX hwi
  · intro n w hX hwi
    exact cutoffLift_xProfile hrho hU d.isOpen hSU his hsrho (A.coefficients n 0) hX hwi

theorem actual_previousOmega_congr_germ (h : ℝ) {u beta u' beta' : ℕ → Field}
    (n : ℕ) {w : ℝ × ℝ}
    (hu : ∀ j < n, u j =ᶠ[𝓝 w] u' j) (hb : ∀ j < n, beta j =ᶠ[𝓝 w] beta' j) :
    AxisSourceRegularity.previousOmegaDivX h u beta n w =
      AxisSourceRegularity.previousOmegaDivX h u' beta' n w := by
  cases n with
  | zero => rfl
  | succ k =>
    have hbk := hb k (Nat.lt_succ_self k)
    have ht := SlowResidualMatching.T_congr_germ h (AxisSourceRegularity.slowOrder h k - 1) hbk
    have hx := (SlowResidualMatching.partialX_congr_germ hbk).eq_of_nhds
    have hxx := (SlowResidualMatching.partialX_congr_germ
      (SlowResidualMatching.partialX_congr_germ hbk)).eq_of_nhds
    have hshift : AxisSourceRegularity.shiftedAxialFactor h beta k w =
        AxisSourceRegularity.shiftedAxialFactor h beta' k w := by
      cases k with
      | zero => rfl
      | succ k =>
        exact AxisSourceRegularity.Z_congr_germ h _
          (SlowResidualMatching.Z_congr_germ h _ (hb k (by omega)))
    have hsum : (∑ ij ∈ Finset.antidiagonal k,
        (beta ij.1 w * (beta ij.2 w / 2 + w.1 * SimilarityProfile.partialX (beta ij.2) w) +
          u ij.1 w * SimilarityProfile.Z h (AxisSourceRegularity.slowOrder h ij.2 - 1) (beta ij.2)
              w)) =
        (∑ ij ∈ Finset.antidiagonal k,
        (beta' ij.1 w * (beta' ij.2 w / 2 + w.1 * SimilarityProfile.partialX (beta' ij.2) w) +
          u' ij.1 w * SimilarityProfile.Z h (AxisSourceRegularity.slowOrder h ij.2 - 1) (beta'
              ij.2) w)) := by
      apply Finset.sum_congr rfl
      intro ij hij
      have hi := AxisSourceRegularity.antidiagonal_indices_le hij
      have hi' : ij.1 < k + 1 := Nat.lt_succ_iff.mpr hi.1
      have hj' : ij.2 < k + 1 := Nat.lt_succ_iff.mpr hi.2
      rw [(hb _ hi').eq_of_nhds, (hb _ hj').eq_of_nhds, (hu _ hi').eq_of_nhds,
        (SlowResidualMatching.partialX_congr_germ (hb _ hj')).eq_of_nhds,
        AxisSourceRegularity.Z_congr_germ h _ (hb _ hj')]
    simp only [AxisSourceRegularity.previousOmegaDivX, AxisSourceRegularity.omegaDivX,
      ht, hx, hxx, hshift, hsum]

/-- Agreement of the finite order-zero input with the same local hierarchy.
These are identities on an inner region, not positive-order hypotheses. -/
structure BaseAgreement {S : Set ℝ} {h C rho : ℝ} {U : Set ℂ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} (s : Scheme S h C)
    (A : SlowRecursion.LocalHierarchy rho U h C base) (inner : ℝ) : Prop where
  phi : ∀ w : ℝ × ℝ, 0 ≤ w.1 → w.1 < inner → w.2 ∈ S →
    xProfile s.base.phi w = SlowRecursion.profile (A.coefficients 0 0) w
  axial : ∀ w : ℝ × ℝ, 0 ≤ w.1 → w.1 < inner → w.2 ∈ S →
    xProfile s.base.axial w = SlowRecursion.profile (A.coefficients 0 1) w
  beta : ∀ w : ℝ × ℝ, 0 ≤ w.1 → w.1 < inner → w.2 ∈ S →
    xProfile s.base.beta w = SlowRecursion.profile (A.coefficients 0 4) w

section LocalAgreement

variable {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
  {base : Fin 5 → SimilarityProfile.InnerProfile}
  {s : Scheme S h C} {A : SlowRecursion.LocalHierarchy rho U h C base}
  (L : Localization s A inner)

include L

theorem profiles_x_inner_axial {n : ℕ} (hn : 0 < n) {w : ℝ × ℝ}
    (hX : 0 ≤ w.1) (hi : w.1 ≤ inner) :
    xProfile (profiles s n).axial w = SlowRecursion.profile (A.coefficients n 1) w := by
  have hs : (Real.sqrt (2 * w.1)) ^ 2 = 2 * w.1 := Real.sq_sqrt (mul_nonneg (by norm_num) hX)
  have hr : |Real.sqrt (2 * w.1)| ≤ s.a := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) s.a_pos.le).mp (by linarith [L.inner_patch])
  change (profiles s n).axial (Real.sqrt (2 * w.1), w.2) = _
  rw [profiles_inner_axial s hn hr]
  exact L.axial_seed n w hX hi

theorem profiles_x_inner_phi {n : ℕ} (hn : 0 < n) {w : ℝ × ℝ}
    (hX : 0 ≤ w.1) (hi : w.1 ≤ inner) :
    xProfile (profiles s n).phi w = SlowRecursion.profile (A.coefficients n 0) w := by
  have hs : (Real.sqrt (2 * w.1)) ^ 2 = 2 * w.1 := Real.sq_sqrt (mul_nonneg (by norm_num) hX)
  have hr : |Real.sqrt (2 * w.1)| ≤ s.a := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) s.a_pos.le).mp (by linarith [L.inner_patch])
  change (profiles s n).phi (Real.sqrt (2 * w.1), w.2) = _
  rw [profiles_inner_phi s hn hr]
  exact L.phi_seed n w hX hi

theorem local_profile_smoothAt (n : ℕ) (i : Fin 5) {w : ℝ × ℝ}
    (hX : 0 < w.1) (hi : w.1 < rho ^ 2) (heta : w.2 ∈ S) :
    ContDiffAt ℝ ∞ (SlowRecursion.profile (A.coefficients n i)) w := by
  have hs : ContDiffOn ℝ ∞ (SlowRecursion.profile (A.coefficients n i))
      (Ioo (0 : ℝ) (rho ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U) :=
    (A.profiles_smooth L.radius_pos L.parameter_open n i).mono
      (Set.prod_mono Ioo_subset_Ico_self Subset.rfl)
  exact hs.contDiffAt ((isOpen_Ioo.prod (PositiveAxisExistence.realParameterDomain_isOpen
      L.parameter_open)).mem_nhds
    ⟨⟨hX, hi⟩, L.parameter_embedding w.2 heta⟩)

omit L in
/-- An actual substitution in the mass integral, with no axis differentiability
assumption on the squared-radius function. -/
theorem massHistory_of_composition (u : EvenProfile S) (g : Field) {R eta : ℝ}
    (hR : 0 ≤ R) (hg : ContinuousOn (fun X => g (X, eta)) (Icc 0 (R ^ 2 / 2)))
    (hu : ∀ r ∈ Icc 0 R, u (r, eta) = g (r ^ 2 / 2, eta)) :
    PositiveOrderMoments.massHistory u (R, eta) = ProfileHistories.primitive g (R ^ 2 / 2, eta) :=
        by
  have hder (r : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2 / 2) r r := by
    convert! ((hasDerivAt_id r).pow 2).div_const 2 using 1
    norm_num
  have him : (fun r : ℝ => r ^ 2 / 2) '' uIcc 0 R ⊆ Icc 0 (R ^ 2 / 2) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [uIcc_of_le hR] at hr
    constructor
    · positivity
    · have hs := (sq_le_sq₀ hr.1 hR).2 hr.2
      linarith
  have hint := intervalIntegral.integral_comp_mul_deriv'
    (f := fun r : ℝ => r ^ 2 / 2) (f' := fun r => r) (g := fun X => g (X, eta))
    (fun r _ => hder r) continuousOn_id (hg.mono him)
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, Function.comp_apply] at hint
  change (∫ r in (0 : ℝ)..R, r * u (r, eta)) = ∫ X in (0 : ℝ)..(R ^ 2 / 2), g (X, eta)
  rw [← hint]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hR] at hr
  change r * u (r, eta) = g (r ^ 2 / 2, eta) * r
  rw [hu r hr, mul_comm]

theorem local_mass {n : ℕ} (hn : 0 < n) {R eta : ℝ} (hR : 0 ≤ R)
    (hi : R ^ 2 / 2 ≤ inner) (heta : eta ∈ S) :
    PositiveOrderMoments.massHistory (profiles s n).axial (R, eta) = R ^ 2 / 2 *
      (SlowRecursion.profile (A.coefficients n 1) (R ^ 2 / 2, eta) +
       SlowRecursion.profile (A.coefficients n 2) (R ^ 2 / 2, eta)) := by
  have hX : 0 ≤ R ^ 2 / 2 := by positivity
  have hxrho : R ^ 2 / 2 < rho ^ 2 := hi.trans_lt L.inner_radius
  have hg : ContinuousOn (fun X => SlowRecursion.profile (A.coefficients n 1) (X, eta))
      (Icc 0 (R ^ 2 / 2)) :=
    (A.profiles_smooth L.radius_pos L.parameter_open n 1).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun X hXX => ⟨⟨hXX.1, hXX.2.trans_lt hxrho⟩, L.parameter_embedding eta heta⟩)
  rw [massHistory_of_composition (profiles s n).axial _ hR hg]
  · rw [ProfileHistories.primitive_eq_mul_average, A.average n hn _ ⟨hX, hxrho⟩ eta
      (L.parameter_embedding eta heta)]
  · intro r hr
    have hs : r ^ 2 / 2 ≤ inner := by
      have hsq := (sq_le_sq₀ hr.1 hR).2 hr.2
      linarith
    rw [← xProfile_radius (profiles s n).axial hr.1 eta]
    exact profiles_x_inner_axial L hn (by positivity) hs

theorem local_parameterMass {n : ℕ} (hn : 0 < n) {R eta : ℝ} (hR : 0 < R)
    (hi : R ^ 2 / 2 ≤ inner) (heta : eta ∈ S) :
    PositiveOrderMoments.parameterMassHistory (profiles s n).axial (R, eta) = R ^ 2 / 2 *
      (SimilarityProfile.partialEta (SlowRecursion.profile (A.coefficients n 1)) (R ^ 2 / 2, eta) +
       SimilarityProfile.partialEta (SlowRecursion.profile (A.coefficients n 2)) (R ^ 2 / 2, eta))
           := by
  have hX : 0 < R ^ 2 / 2 := div_pos (sq_pos_of_pos hR) (by norm_num)
  have hxr : R ^ 2 / 2 < rho ^ 2 := hi.trans_lt L.inner_radius
  have hmassSmooth := ProfileHistories.primitive_smooth (PositiveOrderMoments.parameterDomain S
      s.domain.isOpen)
    (contDiffOn_fst.mul (profiles s n).axial.smooth)
  have hd := parameter_derivative s.domain.isOpen hmassSmooth heta R
  change HasDerivAt (fun t => PositiveOrderMoments.massHistory (profiles s n).axial (R, t))
    (ProfileHistories.parameterPartial (PositiveOrderMoments.massHistory (profiles s n).axial) (R,
        eta)) eta at hd
  rw [PositiveOrderMoments.massHistory_parameterPartial_on s.domain.isOpen (profiles s
      n).axial.smooth heta] at hd
  have hu := partialEta_hasDerivAt ((local_profile_smoothAt L n 1 (w := (R ^ 2 / 2, eta)) hX hxr
      heta).differentiableAt (by
      simp))
  have hk := partialEta_hasDerivAt ((local_profile_smoothAt L n 2 (w := (R ^ 2 / 2, eta)) hX hxr
      heta).differentiableAt (by
      simp))
  have he : (fun t => PositiveOrderMoments.massHistory (profiles s n).axial (R, t)) =ᶠ[𝓝 eta]
      fun t => R ^ 2 / 2 * (SlowRecursion.profile (A.coefficients n 1) (R ^ 2 / 2, t) +
        SlowRecursion.profile (A.coefficients n 2) (R ^ 2 / 2, t)) := by
    filter_upwards [s.domain.isOpen.mem_nhds heta] with t ht
    exact local_mass L hn hR.le hi ht
  exact hd.unique (((hu.add hk).const_mul (R ^ 2 / 2)).congr_of_eventuallyEq he)

theorem profiles_radial_inner_beta_pos {n : ℕ} (hn : 0 < n) {R eta : ℝ} (hR : 0 < R)
    (hi : R ^ 2 / 2 ≤ inner) (heta : eta ∈ S) :
    (profiles s n).beta (R, eta) = SlowRecursion.profile (A.coefficients n 4) (R ^ 2 / 2, eta) := by
  have hX : 0 < R ^ 2 / 2 := div_pos (sq_pos_of_pos hR) (by norm_num)
  have hu : (profiles s n).axial (R, eta) =
      SlowRecursion.profile (A.coefficients n 1) (R ^ 2 / 2, eta) := by
    rw [← xProfile_radius (profiles s n).axial hR.le eta]
    exact profiles_x_inner_axial L hn hX.le hi
  have hb := A.beta n hn _ ⟨hX, hi.trans_lt L.inner_radius⟩ eta (L.parameter_embedding eta heta)
  rw [PositiveAxisExistence.newBeta, PositiveAxisSystem.betaValue_eq_average_formula] at hb
  have hf := betaFromU_eq_fluxHistory s.domain (AxisSourceRegularity.slowOrder h n)
    (profiles s n).axial (w := (R, eta)) heta
  rw [← profiles_beta_eq s hn] at hf
  apply mul_left_cancel₀ hX.ne'
  rw [hf, PositiveOrderMoments.fluxHistory, hu, local_mass L hn hR.le hi heta,
    local_parameterMass L hn hR hi heta, hb]
  simp only [PositiveAxisSystem.actualJet, AxisSourceRegularity.slowOrder,
      PositiveAxisSystem.slowPower]
  ring

/-- Local extension, constructed using `cutoffLift`. -/
noncomputable def localExtension (n : ℕ) (i : Fin 5) : EvenProfile S :=
  cutoffLift L.radius_pos L.parameter_open s.domain.isOpen L.parameter_embedding
    (inner := inner) (stop := (inner + rho ^ 2) / 2)
    (by linarith [L.inner_radius]) (by linarith [L.inner_radius]) (A.coefficients n i)

theorem localExtension_xProfile (n : ℕ) (i : Fin 5) {w : ℝ × ℝ}
    (hX : 0 ≤ w.1) (hi : w.1 ≤ inner) :
    xProfile (localExtension L n i) w = SlowRecursion.profile (A.coefficients n i) w :=
  cutoffLift_xProfile L.radius_pos L.parameter_open s.domain.isOpen L.parameter_embedding _ _ _ hX
      hi

theorem localExtension_radial (n : ℕ) (i : Fin 5) {R eta : ℝ} (hR : 0 ≤ R)
    (hi : R ^ 2 / 2 ≤ inner) :
    localExtension L n i (R, eta) = SlowRecursion.profile (A.coefficients n i) (R ^ 2 / 2, eta) :=
        by
  rw [← xProfile_radius (localExtension L n i) hR eta]
  exact localExtension_xProfile L n i (by positivity) hi

theorem localExtension_germ (n : ℕ) (i : Fin 5) {w : ℝ × ℝ}
    (hX : 0 < w.1) (hi : w.1 < inner) :
    xProfile (localExtension L n i) =ᶠ[𝓝 w] SlowRecursion.profile (A.coefficients n i) := by
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨hX, hi⟩, mem_univ w.2⟩] with p hp
  exact localExtension_xProfile L n i hp.1.1.le hp.1.2.le

theorem localExtension_axis {n : ℕ} (hn : 0 < n) (i : Fin 5) {eta : ℝ} (heta : eta ∈ S) :
    localExtension L n i (0, eta) = 0 := by
  rw [localExtension_radial L n i le_rfl (by simpa using L.inner_pos.le)]
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, SlowRecursion.profile, Real.sqrt_zero]
  rw [A.zero_axis n hn i _ (L.parameter_embedding eta heta)]
  rfl

theorem profiles_radial_inner_beta_axis {n : ℕ} (hn : 0 < n) {eta : ℝ} (heta : eta ∈ S) :
    (profiles s n).beta (0, eta) = localExtension L n 4 (0, eta) := by
  have hs : 0 < Real.sqrt inner := Real.sqrt_pos.mpr L.inner_pos
  have he : EqOn (fun R => (profiles s n).beta (R, eta)) (fun R => localExtension L n 4 (R, eta))
      (Ioo 0 (Real.sqrt inner)) := by
    intro R hR
    have hi : R ^ 2 / 2 ≤ inner := by
      have hh := (sq_le_sq₀ hR.1.le hs.le).2 hR.2.le
      rw [Real.sq_sqrt L.inner_pos.le] at hh
      linarith [sq_nonneg R]
    change (profiles s n).beta (R, eta) = localExtension L n 4 (R, eta)
    rw [profiles_radial_inner_beta_pos L hn hR.1 hi heta, localExtension_radial L n 4 hR.1.le hi]
  have hc := he.closure (slice_smooth (profiles s n).beta.smooth heta).continuous
    (slice_smooth (localExtension L n 4).smooth heta).continuous
  apply hc
  rw [closure_Ioo hs.ne]
  exact ⟨le_rfl, hs.le⟩

theorem profiles_x_inner_beta {n : ℕ} (hn : 0 < n) {w : ℝ × ℝ}
    (hX : 0 ≤ w.1) (hi : w.1 ≤ inner) (heta : w.2 ∈ S) :
    xProfile (profiles s n).beta w = SlowRecursion.profile (A.coefficients n 4) w := by
  have hs : (Real.sqrt (2 * w.1)) ^ 2 / 2 = w.1 := by
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hX)]; ring
  by_cases h0 : w.1 = 0
  · have he := profiles_radial_inner_beta_axis L hn heta
    have hw : w = (0, w.2) := Prod.ext h0 rfl
    rw [hw]
    simpa only [xProfile, mul_zero, Real.sqrt_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div] using
      he.trans (localExtension_radial L n 4 le_rfl (by simpa using L.inner_pos.le))
  · have hp : 0 < w.1 := lt_of_le_of_ne hX (Ne.symm h0)
    have hr : 0 < Real.sqrt (2 * w.1) := Real.sqrt_pos.mpr (mul_pos (by norm_num) hp)
    change (profiles s n).beta (Real.sqrt (2 * w.1), w.2) = _
    simpa only [hs, Prod.eta] using profiles_radial_inner_beta_pos L hn hr (by
        simpa only [hs] using hi) heta

variable (B0 : BaseAgreement s A inner)

include B0

theorem profiles_x_phi_germ (n : ℕ) {w : ℝ × ℝ}
    (hX : 0 < w.1) (hi : w.1 < inner) (heta : w.2 ∈ S) :
    xProfile (profiles s n).phi =ᶠ[𝓝 w] SlowRecursion.profile (A.coefficients n 0) := by
  filter_upwards [(isOpen_Ioo.prod s.domain.isOpen).mem_nhds ⟨⟨hX, hi⟩, heta⟩] with p hp
  by_cases hn : n = 0
  · subst n
    rw [profiles_zero]
    exact B0.phi p hp.1.1.le hp.1.2 hp.2
  · exact profiles_x_inner_phi L (Nat.pos_of_ne_zero hn) hp.1.1.le hp.1.2.le

theorem profiles_x_axial_germ (n : ℕ) {w : ℝ × ℝ}
    (hX : 0 < w.1) (hi : w.1 < inner) (heta : w.2 ∈ S) :
    xProfile (profiles s n).axial =ᶠ[𝓝 w] SlowRecursion.profile (A.coefficients n 1) := by
  filter_upwards [(isOpen_Ioo.prod s.domain.isOpen).mem_nhds ⟨⟨hX, hi⟩, heta⟩] with p hp
  by_cases hn : n = 0
  · subst n
    rw [profiles_zero]
    exact B0.axial p hp.1.1.le hp.1.2 hp.2
  · exact profiles_x_inner_axial L (Nat.pos_of_ne_zero hn) hp.1.1.le hp.1.2.le

theorem profiles_x_beta_germ (n : ℕ) {w : ℝ × ℝ}
    (hX : 0 < w.1) (hi : w.1 < inner) (heta : w.2 ∈ S) :
    xProfile (profiles s n).beta =ᶠ[𝓝 w] SlowRecursion.profile (A.coefficients n 4) := by
  filter_upwards [(isOpen_Ioo.prod s.domain.isOpen).mem_nhds ⟨⟨hX, hi⟩, heta⟩] with p hp
  by_cases hn : n = 0
  · subst n
    rw [profiles_zero]
    exact B0.beta p hp.1.1.le hp.1.2 hp.2
  · exact profiles_x_inner_beta L (Nat.pos_of_ne_zero hn) hp.1.1.le hp.1.2.le hp.2

theorem profiles_source_local (n : ℕ) {w : ℝ × ℝ}
    (hX : 0 < w.1) (hi : w.1 < inner) (heta : w.2 ∈ S) :
    xProfile (previousOmegaDivX s.domain (fun j => (profiles s j).axial)
      (fun j => (profiles s j).beta) n) w =
    AxisSourceRegularity.previousOmegaDivX h (fun j => SlowRecursion.profile (A.coefficients j 1))
      (fun j => SlowRecursion.profile (A.coefficients j 4)) n w := by
  rw [xProfile_previousOmegaDivX s.domain _ _ _ hX heta]
  exact actual_previousOmega_congr_germ h n
    (fun j _ => profiles_x_axial_germ L B0 j hX hi heta)
    (fun j _ => profiles_x_beta_germ L B0 j hX hi heta)

theorem profiles_pressureSource_local {n : ℕ} (hn : 0 < n) {R eta : ℝ} (hR : 0 < R)
    (hi : R ^ 2 / 2 < inner) (heta : eta ∈ S) :
    pressureSource C (fun j => (profiles s j).phi)
      (previousOmegaDivX s.domain (fun j => (profiles s j).axial) (fun j => (profiles s j).beta) n)
          n (R, eta) =
      SimilarityProfile.partialX (SlowRecursion.profile (A.coefficients n 3)) (R ^ 2 / 2, eta) := by
  have hX : 0 < R ^ 2 / 2 := div_pos (sq_pos_of_pos hR) (by norm_num)
  have ho := profiles_source_local L B0 n (w := (R ^ 2 / 2, eta)) hX hi heta
  rw [xProfile_radius _ hR.le eta] at ho
  have hphi (j : ℕ) : (profiles s j).phi (R, eta) =
      SlowRecursion.profile (A.coefficients j 0) (R ^ 2 / 2, eta) := by
    have he := (profiles_x_phi_germ L B0 j (w := (R ^ 2 / 2, eta)) hX hi heta).eq_of_nhds
    rw [xProfile_radius _ hR.le eta] at he
    exact he
  have hp := (A.equations n hn _ ⟨hX, hi.trans L.inner_radius⟩ eta
    (L.parameter_embedding eta heta)).2.1
  simp only [pressureSource, sub_apply, mul_apply, constant_apply, sum_apply, hphi, ho]
  simpa only [PositiveAxisSystem.actualJet, PositiveAxisSystem.convolution,
    PositiveAxisSystem.inverseSquare, inv_pow, div_eq_mul_inv, one_mul, mul_comm] using hp.symm

omit B0 in
theorem localExtension_radial_derivative (n : ℕ) (i : Fin 5) {R eta : ℝ} (hR : 0 < R)
    (hi : R ^ 2 / 2 < inner) (heta : eta ∈ S) :
    ProfileHistories.radialPartial (localExtension L n i) (R, eta) =
      R * SimilarityProfile.partialX (SlowRecursion.profile (A.coefficients n i)) (R ^ 2 / 2, eta)
          := by
  have hX : 0 < R ^ 2 / 2 := div_pos (sq_pos_of_pos hR) (by norm_num)
  have he := (localExtension_germ L n i (w := (R ^ 2 / 2, eta)) hX hi).fderiv_eq (𝕜 := ℝ)
  have hh := radius_mul_xDerivative s.domain.isOpen (localExtension L n i) heta R
  change R * xDerivative s.domain.isOpen (localExtension L n i) (R, eta) =
    ProfileHistories.radialPartial (localExtension L n i) (R, eta) at hh
  rw [← hh, ← xProfile_radius _ hR.le eta, ← xProfile_partialX s.domain.isOpen _ hX heta]
  unfold SimilarityProfile.partialX
  rw [he]

theorem profiles_radial_inner_pressure {n : ℕ} (hn : 0 < n) {R eta : ℝ} (hR : 0 ≤ R)
    (hi : R ^ 2 / 2 < inner) (heta : eta ∈ S) :
    (profiles s n).pressure (R, eta) =
      SlowRecursion.profile (A.coefficients n 3) (R ^ 2 / 2, eta) := by
  let q := pressureSource C (fun j => (profiles s j).phi)
    (previousOmegaDivX s.domain (fun j => (profiles s j).axial) (fun j => (profiles s j).beta) n) n
  let P := localExtension L n 3
  have hd : ∀ r ∈ uIcc (0 : ℝ) R,
      HasDerivAt (fun t => P (t, eta)) (r * q (r, eta)) r := by
    intro r hr
    rw [uIcc_of_le hR] at hr
    have hir : r ^ 2 / 2 < inner := by
      have hs := (sq_le_sq₀ hr.1 hR).2 hr.2
      linarith
    have hp := ProfileHistories.radialPartial_hasDerivAt
      (PositiveOrderMoments.parameterDomain S s.domain.isOpen) P.smooth (p := (r, eta)) ⟨mem_univ
          _, heta⟩
    apply hp.congr_deriv
    by_cases hz : r = 0
    · subst r
      have he := EvenSmoothDescent.deriv_zero_of_even (f := fun t : ℝ => P (t, eta)) (fun t =>
          P.even heta t)
      rw [hp.deriv] at he
      simpa only [zero_mul] using he
    · have hrp : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hz)
      rw [localExtension_radial_derivative L n 3 hrp hir heta]
      rw [profiles_pressureSource_local L B0 hn hrp hir heta]
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((slice_smooth (contDiffOn_fst.mul q.smooth) heta).continuous.intervalIntegrable 0 R)
  have hz : P (0, eta) = 0 := localExtension_axis L hn 3 heta
  rw [hz, sub_zero] at hint
  rw [profiles_pressure_eq s hn, pressureFromSource_eq_primitive]
  change (∫ r in (0 : ℝ)..R, r * q (r, eta)) = _
  rw [hint]
  exact localExtension_radial L n 3 hR hi.le

theorem profiles_x_inner_pressure {n : ℕ} (hn : 0 < n) {w : ℝ × ℝ}
    (hX : 0 ≤ w.1) (hi : w.1 < inner) (heta : w.2 ∈ S) :
    xProfile (profiles s n).pressure w = SlowRecursion.profile (A.coefficients n 3) w := by
  have hs : (Real.sqrt (2 * w.1)) ^ 2 / 2 = w.1 := by
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hX)]; ring
  change (profiles s n).pressure (Real.sqrt (2 * w.1), w.2) = _
  simpa only [hs, Prod.eta] using profiles_radial_inner_pressure L B0 hn (Real.sqrt_nonneg (2 *
      w.1))
    (by simpa only [hs] using hi) heta

end LocalAgreement

theorem pressureFromSource_hasDerivAt {S : Set ℝ} (hS : IsOpen S) (q : EvenProfile S)
    {R eta : ℝ} (heta : eta ∈ S) :
    HasDerivAt (fun r => pressureFromSource hS q (r, eta)) (R * q (R, eta)) R := by
  have he : (fun r => pressureFromSource hS q (r, eta)) =
      fun r => ProfileHistories.primitive (fun p => p.1 * q p) (r, eta) :=
    funext (fun r => pressureFromSource_eq_primitive hS q (r, eta))
  rw [he]
  exact ProfileHistories.primitive_hasDerivAt (PositiveOrderMoments.parameterDomain S hS)
    (contDiffOn_fst.mul q.smooth) (p := (R, eta)) ⟨mem_univ _, heta⟩

theorem profiles_x_pressure_derivative {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 0 < n) {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    SimilarityProfile.partialX (xProfile (profiles s n).pressure) w =
      xProfile (pressureSource C (fun j => (profiles s j).phi)
        (previousOmegaDivX s.domain (fun j => (profiles s j).axial) (fun j => (profiles s j).beta)
            n) n) w := by
  let q := pressureSource C (fun j => (profiles s j).phi)
    (previousOmegaDivX s.domain (fun j => (profiles s j).axial) (fun j => (profiles s j).beta) n) n
  let R := Real.sqrt (2 * w.1)
  have hR : R ≠ 0 := (Real.sqrt_pos.mpr (mul_pos (by norm_num) hX)).ne'
  rw [xProfile_partialX s.domain.isOpen _ hX heta]
  change xDerivative s.domain.isOpen (profiles s n).pressure (R, w.2) = q (R, w.2)
  apply mul_left_cancel₀ hR
  rw [radius_mul_xDerivative s.domain.isOpen _ heta R]
  have hp := ProfileHistories.radialPartial_hasDerivAt (PositiveOrderMoments.parameterDomain S
      s.domain.isOpen)
    (profiles s n).pressure.smooth (p := (R, w.2)) ⟨mem_univ _, heta⟩
  change ProfileHistories.radialPartial (profiles s n).pressure (R, w.2) = _
  have hd := pressureFromSource_hasDerivAt s.domain.isOpen q (R := R) heta
  rw [← profiles_pressure_eq s hn] at hd
  exact hp.unique hd

theorem radialZ_eq_axialOp {S : Set ℝ} {h : ℝ} (d : Domain S h) (b : ℝ) (u : EvenProfile S)
    {w : ℝ × ℝ} (heta : w.2 ∈ S) :
    PositiveOrderMoments.radialZ h b u w = axialOp d b u w := by
  have hx := radius_mul_xDerivative d.isOpen u heta w.1
  change w.1 * xDerivative d.isOpen u w = ProfileHistories.radialPartial u w at hx
  simp only [PositiveOrderMoments.radialZ, axialOp, mul_apply, add_apply, sub_apply,
    constant_apply, inverseDenominator_apply]
  change (2 * w.2 * b * u w + PositiveAxisSystem.edge w.2 * etaDerivative d.isOpen u w -
    w.2 * w.1 * ProfileHistories.radialPartial u w) / PositiveAxisSystem.ell h w.2 =
    (2 * b * w.2 * u w + (1 - w.2 ^ 2) * etaDerivative d.isOpen u w -
      2 * w.2 * (w.1 ^ 2 / 2) * xDerivative d.isOpen u w) * (PositiveAxisSystem.ell h w.2)⁻¹
  rw [← hx]
  simp only [PositiveAxisSystem.edge, div_eq_mul_inv]
  ring

theorem betaFromU_x_divergence {S : Set ℝ} {h : ℝ} (d : Domain S h) (lam : ℝ)
    (u : EvenProfile S) {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    SimilarityProfile.partialX (AxisSourceRegularity.axisFactor (xProfile (betaFromU d lam u))) w +
      SimilarityProfile.Z h (-PositiveAxisSystem.a h + lam) (xProfile u) w = 0 := by
  let b := betaFromU d lam u
  let R := Real.sqrt (2 * w.1)
  have hR : R ≠ 0 := (Real.sqrt_pos.mpr (mul_pos (by norm_num) hX)).ne'
  have hR2 : R ^ 2 / 2 = w.1 := by
    dsimp [R]; rw [Real.sq_sqrt (mul_pos (by norm_num) hX).le]; ring
  have hb := ProfileHistories.radialPartial_hasDerivAt (PositiveOrderMoments.parameterDomain S
      d.isOpen)
    b.smooth (p := (R, w.2)) ⟨mem_univ _, heta⟩
  have hr : HasDerivAt (fun r : ℝ => r ^ 2 / 2) R R := by
    convert! ((hasDerivAt_id R).pow 2).div_const 2 using 1
    norm_num
  have he := (hr.mul hb).unique (reconstructed_flux_derivative d lam u (R := R) heta)
  dsimp only at he
  have hx := radius_mul_xDerivative d.isOpen b heta R
  change R * xDerivative d.isOpen b (R, w.2) = ProfileHistories.radialPartial b (R, w.2) at hx
  rw [← hx, radialZ_eq_axialOp d _ u (w := (R, w.2)) heta, hR2] at he
  rw [AxisSourceRegularity.partialX_axisFactor ((xProfile_contDiffAt d.isOpen b hX
      heta).differentiableAt (by
      simp)),
    xProfile_partialX d.isOpen b hX heta, ← xProfile_axialOp d _ u hX heta]
  change b (R, w.2) + w.1 * xDerivative d.isOpen b (R, w.2) +
    axialOp d (-PositiveAxisSystem.a h + lam) u (R, w.2) = 0
  apply mul_left_cancel₀ hR
  linear_combination he

/-- As slow profiles, constructed using `SlowResidualMatching.ofBeta`. -/
noncomputable def asSlowProfiles {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) :
    SlowExpansionResidual.SlowProfiles :=
  SlowResidualMatching.ofBeta (fun j => xProfile (profiles s j).phi)
    (fun j => xProfile (profiles s j).axial) (fun j => xProfile (profiles s j).beta)
    (fun j => xProfile (profiles s j).pressure)

/-- Exact global divergence at every positive order. -/
theorem profiles_divergenceCoefficient {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 0 < n) {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    SlowExpansionResidual.divergenceCoefficient h (asSlowProfiles s) n w = 0 := by
  change SimilarityProfile.partialX (AxisSourceRegularity.axisFactor (xProfile (profiles s
      n).beta)) w +
    SimilarityProfile.Z h (SlowExpansionResidual.axialExponent h + SlowExpansionResidual.slowOrder
        h n)
      (xProfile (profiles s n).axial) w = 0
  rw [profiles_beta_eq s hn]
  exact betaFromU_x_divergence s.domain (AxisSourceRegularity.slowOrder h n) (profiles s n).axial
      hX heta

/-- Exact global pressure row, with the actual preceding radial residual. -/
theorem profiles_pressureCoefficient {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 0 < n) {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    SlowExpansionResidual.pressureCoefficient h C (asSlowProfiles s) n w = 0 := by
  have ho := SlowResidualMatching.previousOmega_ofBeta h
    (fun j => xProfile (profiles s j).phi) (fun j => xProfile (profiles s j).axial)
    (fun j => xProfile (profiles s j).beta) (fun j => xProfile (profiles s j).pressure)
    n w hX.ne' (s.domain.denominator w.2 heta)
    (fun j _ => (xProfile_contDiffAt s.domain.isOpen (profiles s j).beta hX heta).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  rw [← xProfile_previousOmegaDivX s.domain _ _ n hX heta] at ho
  have hdiv : SlowExpansionResidual.previous
      (fun j => SlowExpansionResidual.omegaCoefficient h (asSlowProfiles s) j w) n / (2 * w.1) =
      xProfile (previousOmegaDivX s.domain (fun j => (profiles s j).axial)
        (fun j => (profiles s j).beta) n) w / 2 := by
    rw [← ho]
    unfold asSlowProfiles
    ring
  unfold SlowExpansionResidual.pressureCoefficient
  rw [hdiv]
  change SimilarityProfile.partialX (xProfile (profiles s n).pressure) w -
    C⁻¹ ^ 2 * SlowExpansionResidual.convolution
      (fun i j => xProfile (profiles s i).phi w * xProfile (profiles s j).phi w) n + _ = 0
  rw [profiles_x_pressure_derivative s hn hX heta, SlowResidualMatching.convolution_eq_positiveAxis]
  simp only [pressureSource,
    xProfile, sum_apply, mul_apply, sub_apply, constant_apply,
    PositiveAxisSystem.convolution, inv_pow, div_eq_mul_inv]
  ring

/-- Component, given by `![q.phi, q.axial, q.beta, q.pressure] i`. -/
noncomputable def component {S : Set ℝ} (q : Coefficient S) (i : Fin 4) : EvenProfile S :=
  ![q.phi, q.axial, q.beta, q.pressure] i

/-- Local index, given by `![0, 1, 4, 3] i`. -/
noncomputable def localIndex (i : Fin 4) : Fin 5 := ![0, 1, 4, 3] i

/-- Every repaired coefficient agrees with the original local hierarchy on
one common inner domain, including the axis. -/
theorem profiles_inner_eq {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
    {A : SlowRecursion.LocalHierarchy rho U h C base}
    (L : Localization s A inner) (B0 : BaseAgreement s A inner)
    {n : ℕ} (hn : 0 < n) (i : Fin 4) {w : ℝ × ℝ}
    (hX : 0 ≤ w.1) (hi : w.1 < inner) (heta : w.2 ∈ S) :
    xProfile (component (profiles s n) i) w = SlowRecursion.profile (A.coefficients n (localIndex
        i)) w := by
  fin_cases i
  · simpa [component, localIndex] using profiles_x_inner_phi L hn hX hi.le
  · simpa [component, localIndex] using profiles_x_inner_axial L hn hX hi.le
  · simpa [component, localIndex] using profiles_x_inner_beta L hn hX hi.le heta
  · simpa [component, localIndex] using profiles_x_inner_pressure L B0 hn hX hi heta

theorem profiles_axis_zero {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
    {A : SlowRecursion.LocalHierarchy rho U h C base}
    (L : Localization s A inner) (B0 : BaseAgreement s A inner)
    {n : ℕ} (hn : 0 < n) (i : Fin 4) {eta : ℝ} (heta : eta ∈ S) :
    component (profiles s n) i (0, eta) = 0 := by
  have he := profiles_inner_eq L B0 hn i (w := (0, eta)) le_rfl L.inner_pos heta
  simp only [xProfile, mul_zero, Real.sqrt_zero, SlowRecursion.profile] at he
  rw [he, A.zero_axis n hn (localIndex i) _ (L.parameter_embedding eta heta)]
  rfl

/-- Joint smoothness up to the axis is inherited from actual local equality. -/
theorem profiles_inner_smooth {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
    {A : SlowRecursion.LocalHierarchy rho U h C base}
    (L : Localization s A inner) (B0 : BaseAgreement s A inner)
    {n : ℕ} (hn : 0 < n) (i : Fin 4) :
    ContDiffOn ℝ ∞ (xProfile (component (profiles s n) i)) (Ico 0 inner ×ˢ S) := by
  have hl : ContDiffOn ℝ ∞ (SlowRecursion.profile (A.coefficients n (localIndex i)))
      (Ico 0 inner ×ˢ S) :=
    (A.profiles_smooth L.radius_pos L.parameter_open n (localIndex i)).mono
      (fun w hw => ⟨⟨hw.1.1, hw.1.2.trans L.inner_radius⟩, L.parameter_embedding w.2 hw.2⟩)
  exact hl.congr (fun w hw => profiles_inner_eq L B0 hn i hw.1.1 hw.1.2 hw.2)

/-- All actual mixed right jets, not just the zero-order values, agree at
the axis.  The derivative is taken relative to the closed half-plane. -/
theorem profiles_axis_mixed_jets {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
    {A : SlowRecursion.LocalHierarchy rho U h C base}
    (L : Localization s A inner) (B0 : BaseAgreement s A inner)
    {n : ℕ} (hn : 0 < n) (i : Fin 4) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    iteratedFDerivWithin ℝ m (xProfile (component (profiles s n) i))
      (Ici 0 ×ˢ (univ : Set ℝ)) (0, eta) =
    iteratedFDerivWithin ℝ m (SlowRecursion.profile (A.coefficients n (localIndex i)))
      (Ici 0 ×ˢ (univ : Set ℝ)) (0, eta) := by
  have he : xProfile (component (profiles s n) i) =ᶠ[𝓝[Ici 0 ×ˢ (univ : Set ℝ)] (0, eta)]
      SlowRecursion.profile (A.coefficients n (localIndex i)) := by
    have hN : ∀ᶠ w : ℝ × ℝ in 𝓝 (0, eta), w.1 < inner ∧ w.2 ∈ S :=
      (isOpen_Iio.prod s.domain.isOpen).mem_nhds ⟨L.inner_pos, heta⟩
    filter_upwards [self_mem_nhdsWithin, hN.filter_mono nhdsWithin_le_nhds] with w hw hNw
    exact profiles_inner_eq L B0 hn i hw.1 hNw.1 hNw.2
  exact he.iteratedFDerivWithin_eq (profiles_inner_eq L B0 hn i le_rfl L.inner_pos heta) m

theorem profiles_axis_right_jets {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
    {A : SlowRecursion.LocalHierarchy rho U h C base}
    (L : Localization s A inner) (B0 : BaseAgreement s A inner)
    {n : ℕ} (hn : 0 < n) (i : Fin 4) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    iteratedDerivWithin m (fun X => xProfile (component (profiles s n) i) (X, eta)) (Ici 0) 0 =
    iteratedDerivWithin m (fun X => SlowRecursion.profile (A.coefficients n (localIndex i)) (X,
        eta)) (Ici 0) 0 := by
  have he : (fun X => xProfile (component (profiles s n) i) (X, eta)) =ᶠ[𝓝[Ici 0] 0]
      fun X => SlowRecursion.profile (A.coefficients n (localIndex i)) (X, eta) := by
    have hN : ∀ᶠ X : ℝ in 𝓝 0, X < inner := isOpen_Iio.mem_nhds L.inner_pos
    filter_upwards [self_mem_nhdsWithin, hN.filter_mono nhdsWithin_le_nhds] with X hX hXi
    exact profiles_inner_eq L B0 hn i (w := (X, eta)) hX hXi heta
  simp only [iteratedDerivWithin_eq_iteratedFDerivWithin]
  rw [he.iteratedFDerivWithin_eq (profiles_inner_eq L B0 hn i (w := (0, eta)) le_rfl L.inner_pos
      heta) m]

/-- Germ locality transfers the two solved tangential equations. No
agreement outside the fixed inner region is required. -/
theorem profiles_inner_tangential {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
    {A : SlowRecursion.LocalHierarchy rho U h C base}
    (L : Localization s A inner) (B0 : BaseAgreement s A inner)
    {n : ℕ} (hn : 0 < n) {w : ℝ × ℝ} (hX : 0 < w.1) (hi : w.1 < inner) (heta : w.2 ∈ S) :
    SlowExpansionResidual.angularCoefficient h (asSlowProfiles s) n w = 0 ∧
      SlowExpansionResidual.axialCoefficient h (asSlowProfiles s) n w = 0 := by
  have hv : ∀ j ≤ n, (asSlowProfiles s).flux j =ᶠ[𝓝 w] (SlowResidualMatching.hierarchyProfiles
      A).flux j := by
    intro j _
    filter_upwards [profiles_x_beta_germ L B0 j hX hi heta] with p hp
    exact congrArg (p.1 * ·) hp
  have hu : ∀ j ≤ n, (asSlowProfiles s).axial j =ᶠ[𝓝 w] (SlowResidualMatching.hierarchyProfiles
      A).axial j :=
    fun j _ => profiles_x_axial_germ L B0 j hX hi heta
  have hphi : ∀ j ≤ n, (asSlowProfiles s).phi j =ᶠ[𝓝 w] (SlowResidualMatching.hierarchyProfiles
      A).phi j :=
    fun j _ => profiles_x_phi_germ L B0 j hX hi heta
  have hp : (asSlowProfiles s).pressure n =ᶠ[𝓝 w] (SlowResidualMatching.hierarchyProfiles
      A).pressure n := by
    filter_upwards [(isOpen_Ioo.prod s.domain.isOpen).mem_nhds ⟨⟨hX, hi⟩, heta⟩] with p hp
    exact profiles_x_inner_pressure L B0 hn hp.1.1.le hp.1.2 hp.2
  rw [SlowResidualMatching.angularCoefficient_congr_germ h n hv hu hphi,
    SlowResidualMatching.axialCoefficient_congr_germ h n hv hu hp]
  exact SlowResidualMatching.hierarchy_tangential_coefficients A hn
    ⟨hX, hi.trans L.inner_radius⟩ (L.parameter_embedding w.2 heta)

theorem compactSupport_of_even_exterior {S : Set ℝ} (f : EvenProfile S) {B : ℝ}
    (hf : Exterior B S f) {eta : ℝ} (heta : eta ∈ S) : HasCompactSupport (fun R => f (R, eta)) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc (-B) B) isCompact_Icc
  intro R hR
  by_contra hout
  apply hR
  change f (R, eta) = 0
  by_cases hBR : B ≤ R
  · exact hf eta heta R hBR
  · have hneg : B ≤ -R := by
      by_contra hn
      exact hout ⟨by linarith, (lt_of_not_ge hBR).le⟩
    rw [← f.even heta R]
    exact hf eta heta (-R) hneg

theorem profiles_compactSupport {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 0 < n) (i : Fin 4) {eta : ℝ} (heta : eta ∈ S) :
    HasCompactSupport (fun R => component (profiles s n) i (R, eta)) := by
  apply compactSupport_of_even_exterior _ (B := s.B) _ heta
  fin_cases i
  · exact profiles_phi_exterior s hn
  · exact profiles_axial_exterior s n
  · exact profiles_beta_exterior s n
  · exact profiles_pressure_exterior s hn

theorem profiles_angular_compactSupport {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 0 < n) {eta : ℝ} (heta : eta ∈ S) :
    HasCompactSupport (fun R => angularField C (profiles s n).phi (R, eta)) :=
  (compactSupport_of_even_exterior _ (profiles_phi_exterior s hn) heta).mul_left

theorem profiles_flux_compactSupport {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (n : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    HasCompactSupport (fun R => R ^ 2 / 2 * (profiles s n).beta (R, eta)) :=
  (compactSupport_of_even_exterior _ (profiles_beta_exterior s n) heta).mul_left

/-- The radial pressure is literally the forward primitive used by the
moment module, with the actual preceding radial source retained. -/
theorem profiles_pressureHistory {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 0 < n) :
    ((profiles s n).pressure : Field) = PositiveOrderMoments.pressureHistory n
      (fun j => angularField C (profiles s j).phi)
      (fun w => w.1 ^ 2 / 2 * previousOmegaDivX s.domain
        (fun j => (profiles s j).axial) (fun j => (profiles s j).beta) n w) := by
  rw [profiles_pressure_eq s hn]
  exact pressureFromSource_eq_pressureHistory s.domain.isOpen C _ _ n

theorem profiles_fluxHistory {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 0 < n) {w : ℝ × ℝ} (heta : w.2 ∈ S) :
    w.1 ^ 2 / 2 * (profiles s n).beta w =
      PositiveOrderMoments.fluxHistory h (AxisSourceRegularity.slowOrder h n) (profiles s n).axial
          w := by
  rw [profiles_beta_eq s hn]
  exact betaFromU_eq_fluxHistory s.domain _ _ heta

/-- The genuine radial divergence identity holds at every signed radius,
including the axis, on the original open parameter domain. -/
theorem profiles_radial_divergence {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 0 < n) {R eta : ℝ} (heta : eta ∈ S) :
    HasDerivAt (fun r => r ^ 2 / 2 * (profiles s n).beta (r, eta))
      (-R * PositiveOrderMoments.radialZ h (-PositiveAxisSystem.a h +
          AxisSourceRegularity.slowOrder h n)
        (profiles s n).axial (R, eta)) R := by
  rw [profiles_beta_eq s hn]
  exact reconstructed_flux_derivative s.domain _ _ heta

end NavierStokes.GlobalSlowProfiles
