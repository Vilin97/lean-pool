/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisWeightEstimates
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A complete coefficient space with compatible actual derivatives

Normalized bounded continuous jets are restricted by closed, linear
fundamental-theorem-of-calculus identities. Thus a point of the resulting
Banach space determines genuine smooth coefficient functions, not unrelated
arrays masquerading as their derivatives.
-/

noncomputable section

namespace NavierStokes.AxisCoefficientSpace

open Set MeasureTheory
open scoped Topology BoundedContinuousFunction ContDiff

/-- A fixed nondegenerate compact real parameter interval. -/
structure Window where
  left : ℝ
  right : ℝ
  nondegenerate : left < right

def Window.interval (I : Window) : Set ℝ := Icc I.left I.right

/-- The continuous clamping map is only an extension device. Smoothness is
proved on the original closed interval, including its one-sided endpoint jets. -/
def Window.project (I : Window) : ℝ → I.interval :=
  projIcc I.left I.right I.nondegenerate.le

theorem Window.continuous_project (I : Window) : Continuous I.project :=
  continuous_projIcc

theorem Window.project_of_mem (I : Window) {x : ℝ} (hx : x ∈ I.interval) :
    I.project x = ⟨x, hx⟩ :=
  projIcc_of_mem I.nondegenerate.le hx

/-- Ambient normalized jets with the supremum norm over both indices and
the compact parameter interval. -/
abbrev RawJets (I : Window) := ((ℕ × ℕ) × I.interval) →ᵇ ℝ

/-- Unnormalized, continuously extended `m`-th jet of coefficient `n`. -/
def jet (I : Window) (w : ℕ → ℕ → ℝ) (A : RawJets I) (n m : ℕ) (x : ℝ) : ℝ :=
  w n m * A ((n, m), I.project x)

theorem continuous_jet (I : Window) (w : ℕ → ℕ → ℝ) (A : RawJets I) (n m : ℕ) :
    Continuous (jet I w A n m) := by
  exact continuous_const.mul
    (A.continuous.comp (continuous_const.prodMk I.continuous_project))

theorem continuous_jet_parameter (I : Window) (w : ℕ → ℕ → ℝ) (n m : ℕ) (x : ℝ) :
    Continuous (fun A : RawJets I => jet I w A n m x) := by
  exact continuous_const.mul (continuous_eval_const _)

theorem continuous_jet_joint (I : Window) (w : ℕ → ℕ → ℝ) (n m : ℕ) :
    Continuous (fun p : RawJets I × ℝ => jet I w p.1 n m p.2) := by
  exact continuous_const.mul
    (continuous_eval.comp
      (continuous_fst.prodMk
        (continuous_const.prodMk (I.continuous_project.comp continuous_snd))))

@[simp] theorem jet_zero (I : Window) (w : ℕ → ℕ → ℝ) (n m : ℕ) (x : ℝ) :
    jet I w 0 n m x = 0 := by simp [jet]

@[simp] theorem jet_add (I : Window) (w : ℕ → ℕ → ℝ) (A B : RawJets I)
    (n m : ℕ) (x : ℝ) :
    jet I w (A + B) n m x = jet I w A n m x + jet I w B n m x := by
  simp [jet, mul_add]

@[simp] theorem jet_sub (I : Window) (w : ℕ → ℕ → ℝ) (A B : RawJets I)
    (n m : ℕ) (x : ℝ) :
    jet I w (A - B) n m x = jet I w A n m x - jet I w B n m x := by
  simp [jet, mul_sub]

@[simp] theorem jet_smul (I : Window) (w : ℕ → ℕ → ℝ) (c : ℝ) (A : RawJets I)
    (n m : ℕ) (x : ℝ) :
    jet I w (c • A) n m x = c * jet I w A n m x := by
  simp [jet]
  ring

/-- Compatibility is an actual FTC identity for every successive pair of
jets, throughout the full interval. -/
def Compatible (I : Window) (w : ℕ → ℕ → ℝ) (A : RawJets I) : Prop :=
  ∀ n m x, x ∈ I.interval →
    jet I w A n m x = jet I w A n m I.left +
      ∫ t in I.left..x, jet I w A n (m + 1) t

/-- The compatible arrays form a linear subspace of the ambient Banach space. -/
def compatibleSubmodule (I : Window) (w : ℕ → ℕ → ℝ) : Submodule ℝ (RawJets I) where
  carrier := {A | Compatible I w A}
  zero_mem' := by
    intro n m x hx
    simp
  add_mem' := by
    intro A B hA hB n m x hx
    simp only [jet_add]
    rw [intervalIntegral.integral_add
      ((continuous_jet I w A n (m + 1)).intervalIntegrable I.left x)
      ((continuous_jet I w B n (m + 1)).intervalIntegrable I.left x),
      hA n m x hx, hB n m x hx]
    ring
  smul_mem' := by
    intro c A hA n m x hx
    simp only [jet_smul, intervalIntegral.integral_const_mul]
    rw [hA n m x hx]
    ring

/-- Closedness follows from continuous evaluation and continuous interval
integration. This is the completeness-critical compatibility argument. -/
theorem isClosed_compatible (I : Window) (w : ℕ → ℕ → ℝ) :
    IsClosed {A : RawJets I | Compatible I w A} := by
  simp only [Compatible, ofPred_forall]
  refine isClosed_iInter fun n => isClosed_iInter fun m =>
    isClosed_iInter fun x => isClosed_iInter fun hx => ?_
  exact isClosed_eq (continuous_jet_parameter I w n m x)
    ((continuous_jet_parameter I w n m I.left).add
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (continuous_jet_joint I w n (m + 1)) I.left x))

/-- The coefficient space, retaining the inherited genuine norm and linear structure. -/
abbrev CoefficientSpace (I : Window) (w : ℕ → ℕ → ℝ) := compatibleSubmodule I w

instance coefficientSpace_complete (I : Window) (w : ℕ → ℕ → ℝ) :
    CompleteSpace (CoefficientSpace I w) :=
  (isClosed_compatible I w).completeSpace_coe

/-- A coefficient is the zeroth actual jet. -/
def coefficient (I : Window) (w : ℕ → ℕ → ℝ) (A : CoefficientSpace I w) (n : ℕ) : ℝ → ℝ :=
  jet I w A.1 n 0

/-- FTC compatibility identifies the derivative within the closed interval;
this includes the corresponding one-sided endpoint derivatives. -/
theorem hasDerivWithinAt_jet (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    HasDerivWithinAt (jet I w A.1 n m) (jet I w A.1 n (m + 1) x) I.interval x := by
  have h := ((continuous_jet I w A.1 n (m + 1)).integral_hasStrictDerivAt I.left
    x).hasDerivAt.const_add
    (jet I w A.1 n m I.left)
  exact h.hasDerivWithinAt.congr_of_mem (fun y hy => A.2 n m y hy) hx

theorem derivWithin_jet (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    derivWithin (jet I w A.1 n m) I.interval x = jet I w A.1 n (m + 1) x :=
  (hasDerivWithinAt_jet I w A n m hx).derivWithin
    (uniqueDiffOn_Icc I.nondegenerate x hx)

/-- At every interior point these are the ordinary real derivatives. -/
theorem hasDerivAt_jet_interior (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ}
    (hx : x ∈ Ioo I.left I.right) :
    HasDerivAt (jet I w A.1 n m) (jet I w A.1 n (m + 1) x) x :=
  (hasDerivWithinAt_jet I w A n m ⟨hx.1.le, hx.2.le⟩).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)

/-- Every stored jet is the corresponding iterated derivative of the actual function. -/
theorem iteratedDerivWithin_jet (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n q m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    iteratedDerivWithin m (jet I w A.1 n q) I.interval x = jet I w A.1 n (q + m) x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [iteratedDerivWithin_succ,
      derivWithin_congr (fun y hy => ih hy) (ih hx), derivWithin_jet I w A n (q + m) hx]
    simp only [Nat.add_assoc]

theorem iteratedDerivWithin_coefficient (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    iteratedDerivWithin m (coefficient I w A n) I.interval x = jet I w A.1 n m x := by
  simpa only [coefficient, Nat.zero_add] using iteratedDerivWithin_jet I w A n 0 m hx

/-- Genuine infinite smoothness on the full compact interval. -/
theorem contDiffOn_jet (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n q : ℕ) :
    ContDiffOn ℝ ∞ (jet I w A.1 n q) I.interval := by
  apply contDiffOn_of_differentiableOn_deriv
  intro m hm x hx
  exact ((hasDerivWithinAt_jet I w A n (q + m) hx).congr_of_mem
    (fun y hy => iteratedDerivWithin_jet I w A n q m hy) hx).differentiableWithinAt

theorem contDiffOn_coefficient (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n : ℕ) :
    ContDiffOn ℝ ∞ (coefficient I w A n) I.interval :=
  contDiffOn_jet I w A n 0

/-- On the interior these are ordinary smooth real functions on an open
neighborhood, so an original interval may be placed inside this enlarged one. -/
theorem contDiffAt_coefficient_interior (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo I.left I.right) :
    ContDiffAt ℝ ∞ (coefficient I w A n) x :=
  ((contDiffOn_coefficient I w A n) x ⟨hx.1.le, hx.2.le⟩).contDiffAt
    (Icc_mem_nhds hx.1 hx.2)

/-- The inherited norm controls every actual parameter derivative with its weight. -/
theorem abs_jet_le (I : Window) (w : ℕ → ℕ → ℝ) (A : CoefficientSpace I w)
    (n m : ℕ) (x : ℝ) :
    |jet I w A.1 n m x| ≤ |w n m| * ‖A‖ := by
  rw [jet, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (A.1.norm_coe_le_norm ((n, m), I.project x)) (abs_nonneg _)

theorem abs_iteratedDerivWithin_coefficient_le (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    |iteratedDerivWithin m (coefficient I w A n) I.interval x| ≤ |w n m| * ‖A‖ := by
  rw [iteratedDerivWithin_coefficient I w A n m hx]
  exact abs_jet_le I w A n m x

/-- Norm convergence controls every derivative uniformly in the parameter. -/
theorem abs_jet_sub_le (I : Window) (w : ℕ → ℕ → ℝ) (A B : CoefficientSpace I w)
    (n m : ℕ) (x : ℝ) :
    |jet I w A.1 n m x - jet I w B.1 n m x| ≤ |w n m| * ‖A - B‖ := by
  simpa only [Submodule.coe_sub, jet_sub] using abs_jet_le I w (A - B) n m x

/-- For nonzero weights, the normalized actual derivative recovers exactly
the stored bounded-continuous coordinate. -/
theorem normalized_derivative (I : Window) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, w n m ≠ 0) (A : CoefficientSpace I w)
    (n m : ℕ) (x : I.interval) :
    iteratedDerivWithin m (coefficient I w A n) I.interval x / w n m =
      A.1 ((n, m), x) := by
  rw [iteratedDerivWithin_coefficient I w A n m x.property,
    jet, I.project_of_mem x.property]
  exact mul_div_cancel_left₀ _ (hw n m)

theorem quotient_abs_derivative (I : Window) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, 0 < w n m) (A : CoefficientSpace I w)
    (n m : ℕ) (x : I.interval) :
    |iteratedDerivWithin m (coefficient I w A n) I.interval x| / w n m =
      |A.1 ((n, m), x)| := by
  calc
    _ = |iteratedDerivWithin m (coefficient I w A n) I.interval x / w n m| := by
      rw [abs_div, abs_of_pos (hw n m)]
    _ = _ := by rw [normalized_derivative I w (fun n m => (hw n m).ne') A n m x]

/-- This is precisely the supremum quotient norm in the manuscript,
expressed by its universal upper-bound characterization. -/
theorem norm_le_iff_derivative_bound (I : Window) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, 0 < w n m) (A : CoefficientSpace I w) (C : ℝ) (hC : 0 ≤ C) :
    ‖A‖ ≤ C ↔ ∀ (n m : ℕ) (x : I.interval),
      |iteratedDerivWithin m (coefficient I w A n) I.interval x| / w n m ≤ C := by
  change ‖A.1‖ ≤ C ↔ _
  rw [BoundedContinuousFunction.norm_le hC]
  constructor
  · intro h n m x
    rw [quotient_abs_derivative I w hw A n m x]
    exact h ((n, m), x)
  · intro h p
    rcases p with ⟨⟨n, m⟩, x⟩
    have hx := h n m x
    rw [quotient_abs_derivative I w hw A n m x] at hx
    exact hx

/-- Positive weights leave no independent or invisible jet coordinates:
equality of the actual coefficient functions forces equality in the space. -/
theorem coefficient_ext (I : Window) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, w n m ≠ 0) (A B : CoefficientSpace I w)
    (h : ∀ n x, x ∈ I.interval → coefficient I w A n x = coefficient I w B n x) :
    A = B := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  rintro ⟨⟨n, m⟩, x⟩
  rw [← normalized_derivative I w hw A n m x,
    ← normalized_derivative I w hw B n m x]
  congr 1
  exact iteratedDerivWithin_congr (fun y hy => h n y hy) x.property

/-- Normalize an actual continuous jet family with a uniform weighted bound. -/
def rawOfJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (C : ℝ) (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m) : RawJets I :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p : (ℕ × ℕ) × I.interval => J p.1.1 p.1.2 p.2 / w p.1.1 p.1.2)
    (continuous_prod_of_discrete_left.mpr
      (fun p => (hcont p.1 p.2).domRestrict.div_const (w p.1 p.2))) C
    (by
      rintro ⟨⟨n, m⟩, x⟩
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (hw n m)]
      exact (div_le_iff₀ (hw n m)).mpr (hbound n m x x.property))

theorem jet_rawOfJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (C : ℝ) (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m)
    (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    jet I w (rawOfJetFamily I w hw J hcont C hbound) n m x = J n m x := by
  change w n m * (J n m (I.project x) / w n m) = J n m x
  rw [I.project_of_mem hx]
  exact mul_div_cancel₀ _ (hw n m).ne'

/-- Actual derivative compatibility implies the closed FTC compatibility
required by the Banach-space representation. -/
theorem compatible_rawOfJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m) :
    Compatible I w (rawOfJetFamily I w hw J hcont C hbound) := by
  intro n m x hx
  have hleft : I.left ∈ I.interval := ⟨le_rfl, I.nondegenerate.le⟩
  have hsub : Icc I.left x ⊆ I.interval := fun y hy => ⟨hy.1, hy.2.trans hx.2⟩
  have hint : IntervalIntegrable (J n (m + 1)) volume I.left x :=
    ContinuousOn.intervalIntegrable_of_Icc hx.1 ((hcont n (m + 1)).mono hsub)
  have hFTC : (∫ t in I.left..x, J n (m + 1) t) = J n m x - J n m I.left := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      ((hcont n m).mono hsub) _ hint
    intro y hy
    exact (hderiv n m y (hsub ⟨hy.1.le, hy.2.le⟩)).hasDerivAt
      (Icc_mem_nhds hy.1 (hy.2.trans_le hx.2))
  have hintEq : (∫ t in I.left..x,
      jet I w (rawOfJetFamily I w hw J hcont C hbound) n (m + 1) t) =
      ∫ t in I.left..x, J n (m + 1) t := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx.1] at hy
    exact jet_rawOfJetFamily I w hw J hcont C hbound n (m + 1) (hsub hy)
  rw [jet_rawOfJetFamily I w hw J hcont C hbound n m hx,
    jet_rawOfJetFamily I w hw J hcont C hbound n m hleft, hintEq, hFTC]
  ring

/-- Reverse constructor used by genuine products and radial operators:
a continuous family with actual adjacent derivatives and the weighted bound
becomes an element of the complete coefficient space. -/
def ofJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m) : CoefficientSpace I w :=
  ⟨rawOfJetFamily I w hw J hcont C hbound,
    compatible_rawOfJetFamily I w hw J hcont hderiv C hbound⟩

theorem jet_ofJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m)
    (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    jet I w (ofJetFamily I w hw J hcont hderiv C hC hbound).1 n m x = J n m x :=
  jet_rawOfJetFamily I w hw J hcont C hbound n m hx

theorem coefficient_ofJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m)
    (n : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    coefficient I w (ofJetFamily I w hw J hcont hderiv C hC hbound) n x = J n 0 x :=
  jet_ofJetFamily I w hw J hcont hderiv C hC hbound n 0 hx

theorem norm_ofJetFamily_le (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m) :
    ‖ofJetFamily I w hw J hcont hderiv C hC hbound‖ ≤ C := by
  apply (norm_le_iff_derivative_bound I w hw _ C hC).mpr
  intro n m x
  rw [iteratedDerivWithin_coefficient I w _ n m x.property,
    jet_ofJetFamily I w hw J hcont hderiv C hC hbound n m x.property]
  exact (div_le_iff₀ (hw n m)).mpr (hbound n m x x.property)

/-- A smooth coefficient family's genuine iterated derivatives form the
adjacent derivative chain required by `ofJetFamily`. -/
theorem hasDerivWithinAt_iterated_smooth (I : Window) (F : ℕ → ℝ → ℝ)
    (hF : ∀ n, ContDiffOn ℝ ∞ (F n) I.interval) (n m : ℕ)
    {x : ℝ} (hx : x ∈ I.interval) :
    HasDerivWithinAt (iteratedDerivWithin m (F n) I.interval)
      (iteratedDerivWithin (m + 1) (F n) I.interval x) I.interval x := by
  have hd : DifferentiableWithinAt ℝ (iteratedDerivWithin m (F n) I.interval) I.interval x :=
    (hF n).differentiableOn_iteratedDerivWithin (m := m)
      (by exact_mod_cast (ENat.natCast_lt_top m))
      (uniqueDiffOn_Icc I.nondegenerate) x hx
  simpa only [iteratedDerivWithin_succ] using hd.hasDerivWithinAt

/-- Reverse constructor from actual smooth coefficient functions with
uniform bounds on all their parameter derivatives. -/
def ofSmoothFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (F : ℕ → ℝ → ℝ) (hF : ∀ n, ContDiffOn ℝ ∞ (F n) I.interval)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval →
      |iteratedDerivWithin m (F n) I.interval x| ≤ C * w n m) : CoefficientSpace I w :=
  ofJetFamily I w hw (fun n m => iteratedDerivWithin m (F n) I.interval)
    (fun n m => (hF n).continuousOn_iteratedDerivWithin (m := m)
      (by exact_mod_cast (ENat.natCast_lt_top m).le)
      (uniqueDiffOn_Icc I.nondegenerate))
    (fun n m _ hx => hasDerivWithinAt_iterated_smooth I F hF n m hx) C hC hbound

theorem jet_ofSmoothFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (F : ℕ → ℝ → ℝ) (hF : ∀ n, ContDiffOn ℝ ∞ (F n) I.interval)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval →
      |iteratedDerivWithin m (F n) I.interval x| ≤ C * w n m)
    (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    jet I w (ofSmoothFamily I w hw F hF C hC hbound).1 n m x =
      iteratedDerivWithin m (F n) I.interval x := by
  unfold ofSmoothFamily
  exact jet_ofJetFamily I w hw _ _ _ C hC hbound n m hx

theorem coefficient_ofSmoothFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (F : ℕ → ℝ → ℝ) (hF : ∀ n, ContDiffOn ℝ ∞ (F n) I.interval)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval →
      |iteratedDerivWithin m (F n) I.interval x| ≤ C * w n m)
    (n : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    coefficient I w (ofSmoothFamily I w hw F hF C hC hbound) n x = F n x := by
  simpa only [coefficient, iteratedDerivWithin_zero] using
    jet_ofSmoothFamily I w hw F hF C hC hbound n 0 hx

theorem norm_ofSmoothFamily_le (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (F : ℕ → ℝ → ℝ) (hF : ∀ n, ContDiffOn ℝ ∞ (F n) I.interval)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval →
      |iteratedDerivWithin m (F n) I.interval x| ≤ C * w n m) :
    ‖ofSmoothFamily I w hw F hF C hC hbound‖ ≤ C := by
  unfold ofSmoothFamily
  exact norm_ofJetFamily_le I w hw _ _ _ C hC hbound

/-- The specific space in GAX.2, with the manuscript's exact positive weights
when `ε>0`. Completeness and normed vector-space structures are inherited. -/
abbrev AxisSpace (I : Window) (ε : ℝ) :=
  CoefficientSpace I (AxisWeightEstimates.weight ε)

/-- The concrete space is a complete normed space of actual smooth functions. -/
theorem axisSpace_complete (I : Window) (ε : ℝ) : CompleteSpace (AxisSpace I ε) :=
  inferInstance

theorem axisSpace_smooth (I : Window) (ε : ℝ) (A : AxisSpace I ε) (n : ℕ) :
    ContDiffOn ℝ ∞ (coefficient I (AxisWeightEstimates.weight ε) A n) I.interval :=
  contDiffOn_coefficient I (AxisWeightEstimates.weight ε) A n

/-- Each actual derivative is controlled by exactly the printed weight. -/
theorem axisSpace_derivative_bound (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    |iteratedDerivWithin m (coefficient I (AxisWeightEstimates.weight ε) A n) I.interval x| ≤
      AxisWeightEstimates.weight ε n m * ‖A‖ := by
  simpa only [abs_of_pos (AxisWeightEstimates.weight_pos hε n m)] using
    abs_iteratedDerivWithin_coefficient_le I (AxisWeightEstimates.weight ε) A n m hx

/-- The exact manuscript norm, with actual derivatives in its quotient. -/
theorem axisSpace_norm_le_iff (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (C : ℝ) (hC : 0 ≤ C) :
    ‖A‖ ≤ C ↔ ∀ (n m : ℕ) (x : I.interval),
      |iteratedDerivWithin m (coefficient I (AxisWeightEstimates.weight ε) A n) I.interval x| /
        AxisWeightEstimates.weight ε n m ≤ C :=
  norm_le_iff_derivative_bound I (AxisWeightEstimates.weight ε)
    (AxisWeightEstimates.weight_pos hε) A C hC

end NavierStokes.AxisCoefficientSpace

end
