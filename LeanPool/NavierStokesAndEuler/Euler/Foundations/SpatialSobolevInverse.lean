/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PressureSpatialRegularity
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.TransportDerivatives
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Finite spatial Sobolev jets in the actual lifted L² space.  Jet entries are
actual strong translation derivatives and therefore genuine weak derivatives.
The pressure jet is constructed, rather than assumed, from coercivity and
pointwise smooth coefficient data.
-/

@[expose] public section

noncomputable section

namespace EulerSpatialSobolevInverse


open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerMetricTransport EulerTransportDerivatives EulerPressureSpatialRegularity
   EulerCoerciveProjection
open scoped ContDiff ENNReal NNReal Topology

/-- The existing Mathlib normed group instance for matrix coefficients, named to keep inference
shallow. -/
local instance coefficientValueNormedGroup : NormedAddCommGroup (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for matrix coefficients. -/
local instance coefficientValueNormedSpace : NormedSpace ℝ (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace

/-- The existing Mathlib normed group instance for first coefficient derivatives. -/
local instance coefficientFirstNormedGroup :
    NormedAddCommGroup (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for first coefficient derivatives. -/
local instance coefficientFirstNormedSpace :
    NormedSpace ℝ (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace


variable (period : ℝ) [Fact (0 < period)]

/-- A bounded smooth pointwise coefficient field with quantitative first and second derivatives. -/
structure SmoothCoefficient where
  /-- The actual pointwise coefficient matrix field. -/
  coefficient : LiftDomain period → Vector3 →L[ℝ] Vector3
  smooth : ∀ x, ContDiff ℝ ∞ (localFieldLift period coefficient x)
  /-- A uniform operator-norm bound for the coefficient field. -/
  bound : ℝ≥0
  norm_bound : ∀ x, ‖coefficient x‖ ≤ bound
  /-- A uniform norm bound for the first covering derivative. -/
  firstBound : ℝ≥0
  norm_first : ∀ x, ‖fderiv ℝ (localFieldLift period coefficient x) 0‖ ≤ firstBound
  /-- A uniform norm bound for the second covering derivative. -/
  secondBound : ℝ≥0
  norm_second : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period coefficient x)) y‖ ≤ secondBound

namespace SmoothCoefficient

variable {period}

theorem measurable (A : SmoothCoefficient period) :
    AEStronglyMeasurable A.coefficient (liftMeasure period) :=
  (smoothField_continuous period A.coefficient A.smooth).aestronglyMeasurable

/-- Actual multiplication by the coefficient field in L². -/
def operator (A : SmoothCoefficient period) : LiftL2 period →L[ℝ] LiftL2 period :=
  coefficientOperator A.coefficient A.measurable A.bound A.norm_bound

theorem operator_ae (A : SmoothCoefficient period) (f : LiftL2 period) :
    A.operator f =ᵐ[liftMeasure period] fun x => A.coefficient x (f x) :=
  coefficientOperator_ae A.coefficient A.measurable A.bound A.norm_bound f

theorem operator_norm (A : SmoothCoefficient period) (f : LiftL2 period) :
    ‖A.operator f‖ ≤ A.bound * ‖f‖ :=
  coefficientApply_norm_le A.coefficient A.measurable A.bound A.norm_bound f

/-- The Lax–Milgram pressure associated with this actual coefficient. -/
def pressure (A : SmoothCoefficient period) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (f : LiftL2 period) : LiftL2 period :=
  liftedPressure period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos f

theorem pressure_norm (A : SmoothCoefficient period) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (f : LiftL2 period) :
    ‖A.pressure κ m c hc hpos f‖ ≤ c⁻¹ * ‖f‖ :=
  pressureSolver_apply_norm_le (gradientSpace period κ m) A.operator c hc
    (coefficientOperator_coercive A.coefficient A.measurable A.bound A.norm_bound c hpos) f

theorem derivative_operator_eq (A B : SmoothCoefficient period) (a : LiftTangent)
    (hB : ∀ x, B.coefficient x = fieldDerivative period a A.coefficient x) :
    coefficientOperator (translatedCoefficientDerivative period a A.coefficient 0)
      (translatedCoefficientDerivative_measurable period a A.coefficient A.smooth)
      (A.firstBound * ‖a‖₊)
      (fun x => translatedCoefficientDerivative_bound period a A.coefficient A.firstBound
        A.norm_first x) = B.operator := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [coefficientOperator_ae (translatedCoefficientDerivative period a A.coefficient 0)
      (translatedCoefficientDerivative_measurable period a A.coefficient A.smooth)
      (A.firstBound * ‖a‖₊)
      (fun x => translatedCoefficientDerivative_bound period a A.coefficient A.firstBound
        A.norm_first x) f, B.operator_ae f] with x hx hy
  rw [hx, hy, hB]
  simp [translatedCoefficientDerivative, fieldDerivative]

theorem operator_translation_hasDerivAt (A : SmoothCoefficient period) (a : LiftTangent) :
    HasDerivAt (fun t => coefficientOperator
      (translatedCoefficient period (translationPath period a t) A.coefficient)
      (translatedCoefficient_measurable period (translationPath period a t) A.coefficient
          A.measurable)
      A.bound (fun x => A.norm_bound (x + translationPath period a t)))
      (coefficientOperator (translatedCoefficientDerivative period a A.coefficient 0)
        (translatedCoefficientDerivative_measurable period a A.coefficient A.smooth)
        (A.firstBound * ‖a‖₊)
        (fun x => translatedCoefficientDerivative_bound period a A.coefficient A.firstBound
          A.norm_first x)) 0 := by
  apply coefficientOperator_hasDerivAt
    (A' := translatedCoefficientDerivative period a A.coefficient)
    (L := A.secondBound * ‖a‖₊ ^ 2)
  · exact translatedCoefficient_hasDerivAt period a A.coefficient A.smooth
  · intro t x
    simpa only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] using
      translatedCoefficientDerivative_lipschitz period a A.coefficient A.smooth
        A.secondBound A.norm_second t x

theorem product_hasDerivAt (A B : SmoothCoefficient period) (a : LiftTangent)
    (hB : ∀ x, B.coefficient x = fieldDerivative period a A.coefficient x)
    (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    HasDerivAt (fun t => translation period (translationPath period a t) (A.operator f))
      (A.operator f' + B.operator f) 0 := by
  have hprod := (A.operator_translation_hasDerivAt a).clm_apply hf
  rw [A.derivative_operator_eq B a hB] at hprod
  have hcov : (fun t => coefficientOperator
      (translatedCoefficient period (translationPath period a t) A.coefficient)
      (translatedCoefficient_measurable period (translationPath period a t) A.coefficient
          A.measurable)
      A.bound (fun x => A.norm_bound (x + translationPath period a t))
      (translation period (translationPath period a t) f)) =
      fun t => translation period (translationPath period a t) (A.operator f) := by
    funext t
    exact (coefficientOperator_translation period (translationPath period a t) A.coefficient
      A.measurable A.bound A.norm_bound f).symm
  rw [hcov] at hprod
  have hop0 : coefficientOperator
      (translatedCoefficient period (translationPath period a 0) A.coefficient)
      (translatedCoefficient_measurable period (translationPath period a 0) A.coefficient
          A.measurable)
      A.bound (fun x => A.norm_bound (x + translationPath period a 0)) = A.operator := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [coefficientOperator_ae
      (translatedCoefficient period (translationPath period a 0) A.coefficient)
      (translatedCoefficient_measurable period (translationPath period a 0) A.coefficient
          A.measurable)
      A.bound (fun x => A.norm_bound (x + translationPath period a 0)) u,
      A.operator_ae u] with x hx hy
    rw [hx, hy]
    simp [translatedCoefficient]
  rw [hop0] at hprod
  simp only [translationPath_zero, translation_zero] at hprod
  convert hprod using 1 <;> first | rfl | exact add_comm _ _

theorem pressure_hasDerivAt (A B : SmoothCoefficient period) (a : LiftTangent)
    (hB : ∀ x, B.coefficient x = fieldDerivative period a A.coefficient x)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    HasDerivAt (fun t => translation period (translationPath period a t)
      (A.pressure κ m c hc hpos f))
      (A.pressure κ m c hc hpos (f' - B.operator (A.pressure κ m c hc hpos f))) 0 := by
  have hp := pressure_translation_hasDerivAt period κ m a A.coefficient A.measurable A.smooth
    A.bound A.firstBound A.secondBound A.norm_bound A.norm_first A.norm_second c hc hpos f f' hf
  rwa [A.derivative_operator_eq B a hB] at hp

end SmoothCoefficient

/-- A finite tree of actual strong translation derivatives of an L² field. -/
inductive SpatialJet (directions : Fin 4 → LiftTangent) : ℕ → LiftL2 period → Type
  | zero (f : LiftL2 period) : SpatialJet directions 0 f
  | succ {n : ℕ} {f : LiftL2 period} (derivatives : Fin 4 → LiftL2 period)
      (lower : ∀ i, SpatialJet directions n (derivatives i))
      (hasDeriv : ∀ i, HasDerivAt (fun t => translation period
        (translationPath period (directions i) t) f) (derivatives i) 0) :
      SpatialJet directions (n + 1) f

/-- A finite tree of actual coefficient derivatives, with bounded smooth data at every node. -/
inductive CoefficientJet (directions : Fin 4 → LiftTangent) : ℕ → SmoothCoefficient period → Type
  | zero (A : SmoothCoefficient period) : CoefficientJet directions 0 A
  | succ {n : ℕ} {A : SmoothCoefficient period} (derivatives : Fin 4 → SmoothCoefficient period)
      (lower : ∀ i, CoefficientJet directions n (derivatives i))
      (derivative_eq : ∀ i x, (derivatives i).coefficient x =
        fieldDerivative period (directions i) A.coefficient x) :
      CoefficientJet directions (n + 1) A

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Forget the highest derivative order of a genuine spatial jet. -/
def truncate {n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions (n + 1) f) :
    SpatialJet period directions n f :=
  match n, J with
  | 0, _ => .zero f
  | _n + 1, .succ df lower hd => .succ df (fun i => (lower i).truncate) hd

/-- The sum of all derivative-word L² norms represented by the jet. -/
def sobolevNorm {n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions n f) : ℝ :=
  match J with
  | .zero f => ‖f‖
  | .succ _ lower _ => ‖f‖ + ∑ i, (lower i).sobolevNorm

theorem nonneg {n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions n f) :
    0 ≤ J.sobolevNorm := by
  induction J with
  | zero f => exact norm_nonneg f
  | succ df lower hd ih =>
    exact add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => ih i)

theorem value_norm_le {n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions n f) :
    ‖f‖ ≤ J.sobolevNorm := by
  cases J with
  | zero => exact le_rfl
  | succ df lower hd =>
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (lower i).nonneg)

theorem truncate_norm_le {n : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions (n + 1) f) :
    J.truncate.sobolevNorm ≤ J.sobolevNorm := by
  induction n generalizing f with
  | zero => exact J.value_norm_le
  | succ n ih =>
    cases J with
    | succ df lower hd =>
      exact add_le_add_right (Finset.sum_le_sum fun i _ => ih (lower i)) ‖f‖

theorem lower_norm_le {n : ℕ} {f : LiftL2 period} (df : Fin 4 → LiftL2 period)
    (lower : ∀ i, SpatialJet period directions n (df i))
    (hd : ∀ i, HasDerivAt (fun t => translation period
      (translationPath period (directions i) t) f) (df i) 0) (i : Fin 4) :
    (lower i).sobolevNorm ≤ (SpatialJet.succ df lower hd).sobolevNorm := by
  exact (Finset.single_le_sum (fun j _ => (lower j).nonneg) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_left (norm_nonneg f))

/-- Addition preserves the actual strong derivatives recorded in a spatial jet. -/
def add {n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions n f) (K : SpatialJet period directions n g) :
    SpatialJet period directions n (f + g) :=
  match J, K with
  | .zero _, .zero _ => .zero (f + g)
  | .succ df Jd hJ, .succ dg Kd hK =>
    .succ (fun i => df i + dg i) (fun i => (Jd i).add (Kd i)) (fun i => by
      convert (hJ i).add (hK i) using 1 <;> first | rfl | (funext t; simp))

/-- Subtraction preserves the actual strong derivatives recorded in a spatial jet. -/
def sub {n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions n f) (K : SpatialJet period directions n g) :
    SpatialJet period directions n (f - g) :=
  match J, K with
  | .zero _, .zero _ => .zero (f - g)
  | .succ df Jd hJ, .succ dg Kd hK =>
    .succ (fun i => df i - dg i) (fun i => (Jd i).sub (Kd i)) (fun i => by
      convert (hJ i).sub (hK i) using 1 <;> first | rfl | (funext t; simp))

theorem add_norm_le {n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions n f) (K : SpatialJet period directions n g) :
    (J.add K).sobolevNorm ≤ J.sobolevNorm + K.sobolevNorm := by
  induction n generalizing f g with
  | zero => cases J; cases K; exact norm_add_le _ _
  | succ n ih =>
    cases J with
    | succ df Jd hJ =>
      cases K with
      | succ dg Kd hK =>
        change ‖f + g‖ + ∑ i, ((Jd i).add (Kd i)).sobolevNorm ≤ _
        calc
          _ ≤ (‖f‖ + ‖g‖) + ∑ i, ((Jd i).sobolevNorm + (Kd i).sobolevNorm) :=
            add_le_add (norm_add_le _ _) (Finset.sum_le_sum fun i _ => ih (Jd i) (Kd i))
          _ = _ := by simp only [Finset.sum_add_distrib, sobolevNorm]; ring

theorem sub_norm_le {n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions n f) (K : SpatialJet period directions n g) :
    (J.sub K).sobolevNorm ≤ J.sobolevNorm + K.sobolevNorm := by
  induction n generalizing f g with
  | zero => cases J; cases K; exact norm_sub_le _ _
  | succ n ih =>
    cases J with
    | succ df Jd hJ =>
      cases K with
      | succ dg Kd hK =>
        change ‖f - g‖ + ∑ i, ((Jd i).sub (Kd i)).sobolevNorm ≤ _
        calc
          _ ≤ (‖f‖ + ‖g‖) + ∑ i, ((Jd i).sobolevNorm + (Kd i).sobolevNorm) :=
            add_le_add (norm_sub_le _ _) (Finset.sum_le_sum fun i _ => ih (Jd i) (Kd i))
          _ = _ := by simp only [Finset.sum_add_distrib, sobolevNorm]; ring

end SpatialJet

namespace CoefficientJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Forget the highest derivative level while retaining the original coefficient. -/
def truncate {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions (n + 1) A) : CoefficientJet period directions n A :=
  match n, J with
  | 0, _ => .zero A
  | _n + 1, .succ dA lower hd => .succ dA (fun i => (lower i).truncate) hd

/-- A finite polynomial bound for multiplication in the jet Sobolev norm. -/
def productConstant {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions n A) : ℝ :=
  match J with
  | .zero A => A.bound
  | .succ dA lower hd => A.bound + ∑ i : Fin 4,
      ((CoefficientJet.succ dA lower hd).truncate.productConstant + (lower i).productConstant)
termination_by n

omit [Fact (0 < period)] in
theorem productConstant_nonneg {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions n A) : 0 ≤ J.productConstant := by
  induction n generalizing A with
  | zero => cases J; rw [productConstant]; exact NNReal.coe_nonneg _
  | succ n ih =>
    cases J with
    | succ dA lower hd =>
      rw [productConstant]
      exact add_nonneg A.bound.coe_nonneg (Finset.sum_nonneg fun i _ =>
        add_nonneg (ih (CoefficientJet.succ dA lower hd).truncate) (ih (lower i)))

end CoefficientJet

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Construct every finite-order derivative of actual coefficient multiplication. -/
def multiply {n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions n A) (J : SpatialJet period directions n f) :
    SpatialJet period directions n (A.operator f) :=
  match n, K, J with
  | 0, .zero _, .zero _ => .zero (A.operator f)
  | _n + 1, .succ dA KA hA, .succ df Jf hf =>
    .succ (fun i => A.operator (df i) + (dA i).operator f)
      (fun i => (multiply (CoefficientJet.succ dA KA hA).truncate (Jf i)).add
        (multiply (KA i) (SpatialJet.succ df Jf hf).truncate))
      (fun i => A.product_hasDerivAt (dA i) (directions i) (hA i) f (df i) (hf i))
termination_by n

theorem multiply_norm_le {n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions n A) (J : SpatialJet period directions n f) :
    (multiply K J).sobolevNorm ≤ K.productConstant * J.sobolevNorm := by
  induction n generalizing A f with
  | zero =>
    cases K; cases J
    simpa only [multiply, sobolevNorm, CoefficientJet.productConstant] using A.operator_norm f
  | succ n ih =>
    cases K with
    | succ dA KA hA =>
      cases J with
      | succ df Jf hf =>
        let K₀ := (CoefficientJet.succ dA KA hA).truncate
        let J₀ := (SpatialJet.succ df Jf hf).truncate
        let N := (SpatialJet.succ df Jf hf).sobolevNorm
        have hlow : J₀.sobolevNorm ≤ N := (SpatialJet.succ df Jf hf).truncate_norm_le
        have hkid : ∀ i, (Jf i).sobolevNorm ≤ N := lower_norm_le df Jf hf
        have hterms : ∀ i,
            ((multiply K₀ (Jf i)).add (multiply (KA i) J₀)).sobolevNorm ≤
              (K₀.productConstant + (KA i).productConstant) * N := by
          intro i
          calc
            _ ≤ (multiply K₀ (Jf i)).sobolevNorm + (multiply (KA i) J₀).sobolevNorm :=
              add_norm_le _ _
            _ ≤ K₀.productConstant * (Jf i).sobolevNorm +
                (KA i).productConstant * J₀.sobolevNorm := add_le_add (ih K₀ (Jf i)) (ih (KA i) J₀)
            _ ≤ K₀.productConstant * N + (KA i).productConstant * N :=
              add_le_add (mul_le_mul_of_nonneg_left (hkid i) K₀.productConstant_nonneg)
                (mul_le_mul_of_nonneg_left hlow (KA i).productConstant_nonneg)
            _ = _ := by ring
        rw [multiply, sobolevNorm]
        change ‖A.operator f‖ + ∑ i,
          ((multiply K₀ (Jf i)).add (multiply (KA i) J₀)).sobolevNorm ≤ _
        calc
          _ ≤ A.bound * N + ∑ i, (K₀.productConstant + (KA i).productConstant) * N :=
            add_le_add ((A.operator_norm f).trans
              (mul_le_mul_of_nonneg_left (SpatialJet.succ df Jf hf).value_norm_le
                  A.bound.coe_nonneg))
              (Finset.sum_le_sum fun i _ => hterms i)
          _ = _ := by
            rw [← Finset.sum_mul, ← add_mul, CoefficientJet.productConstant]

end SpatialJet

namespace CoefficientJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- The explicit finite-order inverse constant obtained from coercivity and coefficient products. -/
def pressureConstant {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions n A) (c : ℝ) : ℝ :=
  match J with
  | .zero _ => c⁻¹
  | .succ dA lower hd => c⁻¹ + ∑ i : Fin 4,
      ((CoefficientJet.succ dA lower hd).truncate.pressureConstant c *
        (1 + (lower i).productConstant *
          (CoefficientJet.succ dA lower hd).truncate.pressureConstant c))
termination_by n

omit [Fact (0 < period)] in
theorem pressureConstant_nonneg {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions n A) (c : ℝ) (hc : 0 < c) :
    0 ≤ J.pressureConstant c := by
  induction n generalizing A with
  | zero => cases J; rw [pressureConstant]; exact inv_nonneg.mpr hc.le
  | succ n ih =>
    cases J with
    | succ dA lower hd =>
      rw [pressureConstant]
      exact add_nonneg (inv_nonneg.mpr hc.le) (Finset.sum_nonneg fun i _ =>
        mul_nonneg (ih (CoefficientJet.succ dA lower hd).truncate)
          (add_nonneg zero_le_one (mul_nonneg (lower i).productConstant_nonneg
            (ih (CoefficientJet.succ dA lower hd).truncate))))

end CoefficientJet

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Construct a genuine pressure Sobolev jet at every finite order. -/
def solvePressure {n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions n A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (J : SpatialJet period directions n f) :
    SpatialJet period directions n (A.pressure κ m c hc hpos f) :=
  match n, K, J with
  | 0, .zero _, .zero _ => .zero (A.pressure κ m c hc hpos f)
  | _n + 1, .succ dA KA hA, .succ df Jf hf =>
    let K₀ := (CoefficientJet.succ dA KA hA).truncate
    let J₀ := (SpatialJet.succ df Jf hf).truncate
    let P₀ := solvePressure K₀ κ m c hc hpos J₀
    .succ (fun i => A.pressure κ m c hc hpos
        (df i - (dA i).operator (A.pressure κ m c hc hpos f)))
      (fun i => solvePressure K₀ κ m c hc hpos ((Jf i).sub (multiply (KA i) P₀)))
      (fun i => A.pressure_hasDerivAt (dA i) (directions i) (hA i)
        κ m c hc hpos f (df i) (hf i))
termination_by n

theorem solvePressure_norm_le {n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions n A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (J : SpatialJet period directions n f) :
    (solvePressure K κ m c hc hpos J).sobolevNorm ≤ K.pressureConstant c * J.sobolevNorm := by
  induction n generalizing A f with
  | zero =>
    cases K; cases J
    simpa only [solvePressure, sobolevNorm, CoefficientJet.pressureConstant] using
      A.pressure_norm κ m c hc hpos f
  | succ n ih =>
    cases K with
    | succ dA KA hA =>
      cases J with
      | succ df Jf hf =>
        let K₀ := (CoefficientJet.succ dA KA hA).truncate
        let J₀ := (SpatialJet.succ df Jf hf).truncate
        let P₀ := solvePressure K₀ κ m c hc hpos J₀
        let N := (SpatialJet.succ df Jf hf).sobolevNorm
        have hlow : J₀.sobolevNorm ≤ N := (SpatialJet.succ df Jf hf).truncate_norm_le
        have hkid : ∀ i, (Jf i).sobolevNorm ≤ N := lower_norm_le df Jf hf
        have hp : P₀.sobolevNorm ≤ K₀.pressureConstant c * N :=
          (ih K₀ hpos J₀).trans
            (mul_le_mul_of_nonneg_left hlow (K₀.pressureConstant_nonneg c hc))
        have hterms : ∀ i,
            (solvePressure K₀ κ m c hc hpos ((Jf i).sub (multiply (KA i) P₀))).sobolevNorm ≤
              (K₀.pressureConstant c * (1 + (KA i).productConstant * K₀.pressureConstant c)) * N :=
                  by
          intro i
          calc
            _ ≤ K₀.pressureConstant c * ((Jf i).sub (multiply (KA i) P₀)).sobolevNorm :=
              ih K₀ hpos _
            _ ≤ K₀.pressureConstant c * ((Jf i).sobolevNorm + (multiply (KA i) P₀).sobolevNorm) :=
              mul_le_mul_of_nonneg_left (sub_norm_le _ _) (K₀.pressureConstant_nonneg c hc)
            _ ≤ K₀.pressureConstant c * (N + (KA i).productConstant * P₀.sobolevNorm) :=
              mul_le_mul_of_nonneg_left (add_le_add (hkid i) (multiply_norm_le (KA i) P₀))
                (K₀.pressureConstant_nonneg c hc)
            _ ≤ K₀.pressureConstant c * (N + (KA i).productConstant * (K₀.pressureConstant c * N))
                :=
              mul_le_mul_of_nonneg_left
                (add_le_add_right (mul_le_mul_of_nonneg_left hp (KA i).productConstant_nonneg) N)
                (K₀.pressureConstant_nonneg c hc)
            _ = _ := by ring
        rw [solvePressure, sobolevNorm]
        change ‖A.pressure κ m c hc hpos f‖ + ∑ i,
          (solvePressure K₀ κ m c hc hpos ((Jf i).sub (multiply (KA i) P₀))).sobolevNorm ≤ _
        calc
          _ ≤ c⁻¹ * N + ∑ i,
              (K₀.pressureConstant c * (1 + (KA i).productConstant * K₀.pressureConstant c)) * N :=
            add_le_add ((A.pressure_norm κ m c hc hpos f).trans
              (mul_le_mul_of_nonneg_left (SpatialJet.succ df Jf hf).value_norm_le (inv_nonneg.mpr
                  hc.le)))
              (Finset.sum_le_sum fun i _ => hterms i)
          _ = _ := by
            rw [← Finset.sum_mul, ← add_mul, CoefficientJet.pressureConstant]

end SpatialJet

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- A derivative word, ordered with its head differentiated last; invalid orders return zero. -/
def word {s : ℕ} {f : LiftL2 period} (J : SpatialJet period directions s f)
    {n : ℕ} (w : Fin n → Fin 4) : LiftL2 period :=
  match n, J with
  | 0, _ => f
  | _n + 1, .zero _ => 0
  | n + 1, .succ _ lower _ => (lower (w (Fin.last n))).word (Fin.init w)
termination_by s

@[simp]
theorem word_zero {s : ℕ} {f : LiftL2 period} (J : SpatialJet period directions s f)
    (w : Fin 0 → Fin 4) : J.word w = f := by rw [word]

@[simp]
theorem word_succ {s n : ℕ} {f : LiftL2 period} (df : Fin 4 → LiftL2 period)
    (lower : ∀ i, SpatialJet period directions s (df i))
    (hd : ∀ i, HasDerivAt (fun t => translation period
      (translationPath period (directions i) t) f) (df i) 0) (w : Fin (n + 1) → Fin 4) :
    (SpatialJet.succ df lower hd).word w = (lower (w (Fin.last n))).word (Fin.init w) := by
  rw [word]

theorem word_hasDerivAt {s n : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (hn : n < s) (w : Fin n → Fin 4) (i : Fin 4) :
    HasDerivAt (fun t => translation period (translationPath period (directions i) t) (J.word w))
      (J.word (Fin.cons i w)) 0 := by
  induction n generalizing s f with
  | zero =>
    cases J with
    | zero => omega
    | succ df lower hd => simpa using hd i
  | succ n ih =>
    cases J with
    | zero => omega
    | succ df lower hd =>
      have h := ih (lower (w (Fin.last n))) (by omega) (Fin.init w)
      have hi : Fin.init (n := n + 1) (α := fun _ : Fin (n + 2) => Fin 4)
          (Fin.cons (α := fun _ : Fin (n + 2) => Fin 4) i w) =
          Fin.cons (α := fun _ : Fin (n + 1) => Fin 4) i (Fin.init w) := by
        funext j
        cases j using Fin.cases <;> rfl
      simp only [word_succ, hi]
      convert h using 1
      rfl

/-- Split a coordinate word into its last direction and its initial word. -/
def wordSnocEquiv (n : ℕ) : (Fin (n + 1) → Fin 4) ≃ Fin 4 × (Fin n → Fin 4) where
  toFun w := (w (Fin.last n), Fin.init w)
  invFun v := Fin.snoc v.2 v.1
  left_inv w := Fin.snoc_init_self w
  right_inv v := by simp

/-- The sum over words of positive length is the sum over final directions and initial words. -/
theorem sum_word_succ {s n : ℕ} {f : LiftL2 period} (df : Fin 4 → LiftL2 period)
    (lower : ∀ i, SpatialJet period directions s (df i))
    (hd : ∀ i, HasDerivAt (fun t => translation period
      (translationPath period (directions i) t) f) (df i) 0) :
    (∑ w : Fin (n + 1) → Fin 4, ‖(SpatialJet.succ df lower hd).word w‖) =
      ∑ i, ∑ w : Fin n → Fin 4, ‖(lower i).word w‖ := by
  calc
    _ = ∑ v : Fin 4 × (Fin n → Fin 4), ‖(lower v.1).word v.2‖ :=
      Fintype.sum_equiv (wordSnocEquiv n)
        (fun w => ‖(SpatialJet.succ df lower hd).word w‖)
        (fun v => ‖(lower v.1).word v.2‖) (fun _ => by rw [word_succ]; rfl)
    _ = _ := Fintype.sum_prod_type _

/-- The recursive jet norm equals the explicit sum of the norms of all coordinate words. -/
theorem sobolevNorm_eq_sum_words {s : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) :
    J.sobolevNorm = ∑ n ∈ Finset.range (s + 1), ∑ w : Fin n → Fin 4, ‖J.word w‖ := by
  induction s generalizing f with
  | zero => cases J; simp [sobolevNorm]
  | succ s ih =>
    cases J with
    | succ df lower hd =>
      rw [sobolevNorm, Finset.sum_range_succ']
      simp only [word_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, pow_zero, one_smul]
      simp_rw [sum_word_succ]
      rw [Finset.sum_comm]
      simp_rw [← ih]
      exact add_comm _ _

end SpatialJet

end EulerSpatialSobolevInverse
