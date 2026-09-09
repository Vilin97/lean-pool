/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.NilpotentVolterra
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Positivity.Finset

/-!
# Symmetric extension and parity for the actual Volterra solution

The negative half is obtained by reflecting the differential equation.
The integral identity is proved for the glued function at and across the
axis; parity will follow from uniqueness, not from the definition of glue.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.VolterraParity

open Set Filter MeasureTheory
open scoped Topology
open VolterraAnalyticBounds
open NilpotentVolterra (equationRHS)

/-- Parity sign, with branches according to `i.val < 4`. -/
noncomputable def paritySign (i : Fin 6) : ℂ := if i.val < 4 then 1 else -1

/-- Parity vector, given by `ContinuousLinearMap.pi (fun i => paritySign i •
ContinuousLinearMap.proj i)`. -/
noncomputable def parityVec : Vec →L[ℂ] Vec :=
  ContinuousLinearMap.pi (fun i => paritySign i • ContinuousLinearMap.proj i)

@[simp] theorem parityVec_apply (v : Vec) (i : Fin 6) :
    parityVec v i = paritySign i * v i := rfl

@[simp] theorem paritySign_mul_self (i : Fin 6) : paritySign i * paritySign i = 1 := by
  by_cases hi : i.val < 4 <;> simp [paritySign, hi]

@[simp] theorem parityVec_involutive (v : Vec) : parityVec (parityVec v) = v := by
  funext i
  simp only [parityVec_apply, ← mul_assoc, paritySign_mul_self, one_mul]

/-- Coefficient parity on, given by `∀ r ∈ S, ∀ z ∈ U, ∀ i j, A (-r) z i j = -(paritySign i *
paritySign j) * A r z i j`. -/
def CoefficientParityOn (S : Set ℝ) (U : Set ℂ) (A : Coeff) : Prop :=
  ∀ r ∈ S, ∀ z ∈ U, ∀ i j,
    A (-r) z i j = -(paritySign i * paritySign j) * A r z i j

/-- Forcing parity on, given by `∀ r ∈ S, ∀ z ∈ U, ∀ i, f (-r) z i = -(paritySign i) * f r z i`. -/
def ForcingParityOn (S : Set ℝ) (U : Set ℂ) (f : Field) : Prop :=
  ∀ r ∈ S, ∀ z ∈ U, ∀ i, f (-r) z i = -(paritySign i) * f r z i

/-- Coefficient parity, given by `∀ r z i j, A (-r) z i j = -(paritySign i * paritySign j) * A r
z i j`. -/
def CoefficientParity (A : Coeff) : Prop :=
  ∀ r z i j, A (-r) z i j = -(paritySign i * paritySign j) * A r z i j

/-- Forcing parity, given by `∀ r z i, f (-r) z i = -(paritySign i) * f r z i`. -/
def ForcingParity (f : Field) : Prop :=
  ∀ r z i, f (-r) z i = -(paritySign i) * f r z i

/-- Reflect field, defined pointwise by `W (-r) z`. -/
noncomputable def reflectField (W : Field) : Field := fun r z => W (-r) z

/-- Reflect coefficient, defined pointwise by `-A (-r) z`. -/
noncomputable def reflectCoeff (A : Coeff) : Coeff := fun r z => -A (-r) z

/-- Reflected forcing, defined pointwise by `-f (-r) z`. -/
noncomputable def reflectedForcing (f : Field) : Field := fun r z => -f (-r) z

@[simp] theorem reflectField_twice (W : Field) : reflectField (reflectField W) = W := by
  funext r z
  simp [reflectField]

@[simp] theorem reflectCoeff_twice (A : Coeff) : reflectCoeff (reflectCoeff A) = A := by
  funext r z
  simp [reflectCoeff]

@[simp] theorem reflectedForcing_twice (f : Field) :
    reflectedForcing (reflectedForcing f) = f := by
  funext r z
  simp [reflectedForcing]

@[simp] theorem parameterDeriv_reflect (W : Field) :
    parameterDeriv (reflectField W) = reflectField (parameterDeriv W) := rfl

theorem equationRHS_reflect (A₀ A₁ : Coeff) (f W : Field) :
    equationRHS (reflectCoeff A₀) (reflectCoeff A₁) (reflectedForcing f) (reflectField W) =
      reflectedForcing (equationRHS A₀ A₁ f W) := by
  funext r z i
  simp [equationRHS, reflectCoeff, reflectedForcing, reflectField, matrixAction,
    parameterDeriv, Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]
  ring

/-- The sign from radial reflection is exactly the sign in the reflected
forcing. This is an identity of actual Bochner integrals. -/
theorem radialInverse_reflect (F : Field) :
    radialInverse (reflectedForcing F) = reflectField (radialInverse F) := by
  funext r z i
  simp [radialInverse, reflectedForcing, reflectField, smul_neg,
    intervalIntegral.integral_neg, mul_neg, neg_smul]

theorem radialInverse_equationRHS_reflect (A₀ A₁ : Coeff) (f W : Field) :
    radialInverse (equationRHS (reflectCoeff A₀) (reflectCoeff A₁)
      (reflectedForcing f) (reflectField W)) =
        reflectField (radialInverse (equationRHS A₀ A₁ f W)) := by
  rw [equationRHS_reflect, radialInverse_reflect]

/-- The actual regular integral equation on a specified radial set. -/
def IntegralEquationOn (S : Set ℝ) (U : Set ℂ) (A₀ A₁ : Coeff) (f W : Field) : Prop :=
  ∀ r ∈ S, ∀ z ∈ U, W r z = radialInverse (equationRHS A₀ A₁ f W) r z

theorem IntegralEquationOn.reflect {S : Set ℝ} {U : Set ℂ}
    {A₀ A₁ : Coeff} {f W : Field} (h : IntegralEquationOn S U A₀ A₁ f W) :
    IntegralEquationOn {r | -r ∈ S} U (reflectCoeff A₀) (reflectCoeff A₁)
      (reflectedForcing f) (reflectField W) := by
  intro r hr z hz
  rw [radialInverse_equationRHS_reflect]
  exact h (-r) hr z hz

theorem negativeHalf_equation {R : ℝ} {U : Set ℂ} {A₀ A₁ : Coeff} {f W : Field}
    (h : IntegralEquationOn (Icc 0 R) U (reflectCoeff A₀) (reflectCoeff A₁)
      (reflectedForcing f) W) :
    IntegralEquationOn (Icc (-R) 0) U A₀ A₁ f (reflectField W) := by
  intro r hr z hz
  have hh := h.reflect r ⟨neg_nonneg.mpr hr.2, by linarith [hr.1]⟩ z hz
  simpa using hh

/-- Glue, defined pointwise by `if 0 ≤ r then Wp r z else Wm (-r) z`. -/
noncomputable def glue (Wp Wm : Field) : Field :=
  fun r z => if 0 ≤ r then Wp r z else Wm (-r) z

theorem glue_nonneg (Wp Wm : Field) {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    glue Wp Wm r z = Wp r z := by simp [glue, hr]

theorem glue_nonpos {Wp Wm : Field} (h0 : ∀ z, Wp 0 z = Wm 0 z)
    {r : ℝ} (hr : r ≤ 0) (z : ℂ) : glue Wp Wm r z = Wm (-r) z := by
  by_cases hr0 : r = 0
  · subst r
    simpa [glue] using h0 z
  · simp [glue, show ¬ 0 ≤ r by exact not_le.mpr (lt_of_le_of_ne hr hr0)]

theorem equationRHS_congr_at {A₀ A₁ : Coeff} {f W V : Field} {r : ℝ}
    (h : ∀ z, W r z = V r z) (z : ℂ) :
    equationRHS A₀ A₁ f W r z = equationRHS A₀ A₁ f V r z := by
  have hd : parameterDeriv W r z = parameterDeriv V r z := by
    funext i
    apply congrArg (fun g : ℂ → ℂ => deriv g z)
    funext w
    exact congrFun (h w) i
  simp only [equationRHS, matrixAction]
  rw [h z, hd]

theorem radialInverse_congr_at {F G : Field} {r : ℝ} {z : ℂ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, F (t * r) z = G (t * r) z) :
    radialInverse F r z = radialInverse G r z := by
  funext i
  unfold radialInverse
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change t ^ exponent i • F (t * r) z i = t ^ exponent i • G (t * r) z i
  rw [congrFun (h t (by simpa only [uIcc_of_le zero_le_one] using ht)) i]

/-- Gluing solves the equation on the entire symmetric interval. Equality
of the axis traces is the only matching fact needed for this identity. -/
theorem glue_integralEquation {R : ℝ} {U : Set ℂ} {A₀ A₁ : Coeff}
    {f Wp Wm : Field} (h0 : ∀ z, Wp 0 z = Wm 0 z)
    (hp : IntegralEquationOn (Icc 0 R) U A₀ A₁ f Wp)
    (hm : IntegralEquationOn (Icc 0 R) U (reflectCoeff A₀) (reflectCoeff A₁)
      (reflectedForcing f) Wm) :
    IntegralEquationOn (Icc (-R) R) U A₀ A₁ f (glue Wp Wm) := by
  intro r hr z hz
  by_cases hs : 0 ≤ r
  · rw [glue_nonneg Wp Wm hs, hp r ⟨hs, hr.2⟩ z hz]
    apply radialInverse_congr_at
    intro t ht
    exact (equationRHS_congr_at (fun w => glue_nonneg Wp Wm (mul_nonneg ht.1 hs) w) z).symm
  · have hs' : r ≤ 0 := le_of_not_ge hs
    have he := negativeHalf_equation hm r ⟨hr.1, hs'⟩ z hz
    change Wm (-r) z = _ at he
    rw [glue_nonpos h0 hs', he]
    apply radialInverse_congr_at
    intro t ht
    exact (equationRHS_congr_at
      (fun w => glue_nonpos h0 (mul_nonpos_of_nonneg_of_nonpos ht.1 hs') w) z).symm

theorem glue_parameter_holomorphic {R : ℝ} {U : Set ℂ} {Wp Wm : Field}
    (hp : ∀ r ∈ Icc 0 R, ∀ i, DifferentiableOn ℂ (fun z => Wp r z i) U)
    (hm : ∀ r ∈ Icc 0 R, ∀ i, DifferentiableOn ℂ (fun z => Wm r z i) U)
    {r : ℝ} (hr : r ∈ Icc (-R) R) (i : Fin 6) :
    DifferentiableOn ℂ (fun z => glue Wp Wm r z i) U := by
  by_cases hs : 0 ≤ r
  · simpa [glue, hs] using hp r ⟨hs, hr.2⟩ i
  · have hn : -r ∈ Icc 0 R := ⟨neg_nonneg.mpr (le_of_not_ge hs), by linarith [hr.1]⟩
    simpa [glue, hs] using hm (-r) hn i

theorem glue_jointly_continuous {R : ℝ} {U : Set ℂ} {Wp Wm : Field}
    (h0 : ∀ z ∈ U, Wp 0 z = Wm 0 z)
    (hp : ContinuousOn (fun p : ℝ × ℂ => Wp p.1 p.2) (Icc 0 R ×ˢ U))
    (hm : ContinuousOn (fun p : ℝ × ℂ => Wm p.1 p.2) (Icc 0 R ×ˢ U)) :
    ContinuousOn (fun p : ℝ × ℂ => glue Wp Wm p.1 p.2) (Icc (-R) R ×ˢ U) := by
  apply ContinuousOn.if
  · intro p h
    have he : (0 : ℝ) = p.1 :=
      frontier_le_subset_eq continuous_const continuous_fst h.2
    simpa only [← he, neg_zero] using h0 p.2 h.1.2
  · apply hp.mono
    intro p h
    have hh : 0 ≤ p.1 := by
      simpa only [(isClosed_le continuous_const continuous_fst).closure_eq, Set.mem_ofPred_eq]
          using h.2
    exact ⟨⟨hh, h.1.1.2⟩, h.1.2⟩
  · apply hm.comp (continuous_fst.neg.prodMk continuous_snd).continuousOn
    intro p h
    have hh : p.1 ≤ 0 :=
      closure_lt_subset_le continuous_fst continuous_const
        (show p ∈ closure {p : ℝ × ℂ | p.1 < 0} by simpa only [not_le] using h.2)
    exact ⟨⟨neg_nonneg.mpr hh, show -p.1 ≤ R by linarith [h.1.1.1]⟩, h.1.2⟩

/-- The symmetric regular integral solution, before the radial smoothness
bootstrap. No differentiability at the glued axis is assumed. -/
structure IsSymmetricIntegralSolution (R : ℝ) (U : Set ℂ)
    (A₀ A₁ : Coeff) (f W : Field) : Prop where
  jointly_continuous : ContinuousOn (fun p : ℝ × ℂ => W p.1 p.2) (Icc (-R) R ×ˢ U)
  parameter_holomorphic : ∀ r ∈ Icc (-R) R, ∀ i,
    DifferentiableOn ℂ (fun z => W r z i) U
  integral_equation : IntegralEquationOn (Icc (-R) R) U A₀ A₁ f W
  axis_zero : ∀ z ∈ U, W 0 z = 0

/-- Symmetric path: an abbreviation for `C(Icc (-R) R, E)`. -/
abbrev SymmetricPath (R : ℝ) (E : Type*) [TopologicalSpace E] := C(Icc (-R) R, E)
/-- Symmetric coefficient path: an abbreviation for `SymmetricPath R (Vec →L[ℂ] Vec)`. -/
abbrev SymmetricCoefficientPath (R : ℝ) := SymmetricPath R (Vec →L[ℂ] Vec)

/-- Positive embedding, given by `⟨fun x => ⟨x.1, ⟨(neg_nonpos.mpr hR).trans x.2.1, x.2.2⟩⟩,
continuous_subtype_val.subtype_mk _⟩`. -/
noncomputable def positiveEmbedding {R : ℝ} (hR : 0 ≤ R) :
    C(Icc (0 : ℝ) R, Icc (-R) R) :=
  ⟨fun x => ⟨x.1, ⟨(neg_nonpos.mpr hR).trans x.2.1, x.2.2⟩⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Negative embedding, given by `⟨fun x => ⟨-x.1, ⟨neg_le_neg x.2.2, (neg_nonpos.mpr
x.2.1).trans hR⟩⟩, continuous_subtype_val.neg.subtype_mk _⟩`. -/
noncomputable def negativeEmbedding {R : ℝ} (hR : 0 ≤ R) :
    C(Icc (0 : ℝ) R, Icc (-R) R) :=
  ⟨fun x => ⟨-x.1, ⟨neg_le_neg x.2.2, (neg_nonpos.mpr x.2.1).trans hR⟩⟩,
    continuous_subtype_val.neg.subtype_mk _⟩

/-- Side embedding, with branches according to `b`. -/
noncomputable def sideEmbedding {R : ℝ} (hR : 0 ≤ R) (b : Bool) :
    C(Icc (0 : ℝ) R, Icc (-R) R) :=
  if b then negativeEmbedding hR else positiveEmbedding hR

/-- Side restriction, constructed using `LinearMap.mkContinuous`. -/
noncomputable def sideRestriction {R : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (hR : 0 ≤ R) (b : Bool) :
    SymmetricPath R E →L[ℂ] C(Icc (0 : ℝ) R, E) :=
  LinearMap.mkContinuous {
    toFun := fun f => f.comp (sideEmbedding hR b)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
  } 1 (by
    intro f
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro x
    exact f.norm_coe_le_norm _)

/-- Signed restriction, given by `(if b then (-1 : ℂ) else 1) • sideRestriction hR b`. -/
noncomputable def signedRestriction {R : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (hR : 0 ≤ R) (b : Bool) :
    SymmetricPath R E →L[ℂ] C(Icc (0 : ℝ) R, E) :=
  (if b then (-1 : ℂ) else 1) • sideRestriction hR b

/-- Side data, defined pointwise by `signedRestriction hR b (F z)`. -/
noncomputable def sideData {R : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (hR : 0 ≤ R) (b : Bool)
    (F : ℂ → SymmetricPath R E) : ℂ → C(Icc (0 : ℝ) R, E) :=
  fun z => signedRestriction hR b (F z)

@[simp] theorem sideData_false {R : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (hR : 0 ≤ R)
    (F : ℂ → SymmetricPath R E) (z : ℂ) (x : Icc (0 : ℝ) R) :
    sideData hR false F z x = F z (positiveEmbedding hR x) := by
  simp [sideData, signedRestriction, sideRestriction, sideEmbedding]

@[simp] theorem sideData_true {R : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (hR : 0 ≤ R)
    (F : ℂ → SymmetricPath R E) (z : ℂ) (x : Icc (0 : ℝ) R) :
    sideData hR true F z x = -F z (negativeEmbedding hR x) := by
  simp [sideData, signedRestriction, sideRestriction, sideEmbedding]

theorem sideData_holomorphic {R : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (hR : 0 ≤ R) (b : Bool)
    {F : ℂ → SymmetricPath R E} {U : Set ℂ} (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (sideData hR b F) U := by
  exact (signedRestriction (E := E) hR b).differentiable.comp_differentiableOn hF

/-- Symmetric raw field, defined pointwise by `F z (projIcc (-R) R (by linarith) r)`. -/
noncomputable def symmetricRawField {R : ℝ} (hR : 0 ≤ R)
    (F : ℂ → SymmetricPath R Vec) : Field :=
  fun r z => F z (projIcc (-R) R (by linarith) r)

/-- Symmetric raw coefficient, defined pointwise by `LinearMap.toMatrix' (A z (projIcc (-R) R
(by linarith) r)).toLinearMap`. -/
noncomputable def symmetricRawCoefficient {R : ℝ} (hR : 0 ≤ R)
    (A : ℂ → SymmetricCoefficientPath R) : Coeff :=
  fun r z => LinearMap.toMatrix' (A z (projIcc (-R) R (by linarith) r)).toLinearMap

theorem sideRawField_pos {R : ℝ} (hR : 0 ≤ R)
    (F : ℂ → SymmetricPath R Vec) {r : ℝ} (hr : r ∈ Icc 0 R) (z : ℂ) :
    NilpotentVolterra.rawField hR (sideData hR false F) r z =
      symmetricRawField hR F r z := by
  simp only [NilpotentVolterra.rawField, NilpotentVolterra.extendPath, sideData_false,
    symmetricRawField]
  rw [projIcc_of_mem hR hr, projIcc_of_mem (by linarith : -R ≤ R)
    ⟨(neg_nonpos.mpr hR).trans hr.1, hr.2⟩]
  rfl

theorem sideRawField_neg {R : ℝ} (hR : 0 ≤ R)
    (F : ℂ → SymmetricPath R Vec) {r : ℝ} (hr : r ∈ Icc 0 R) (z : ℂ) :
    NilpotentVolterra.rawField hR (sideData hR true F) r z =
      reflectedForcing (symmetricRawField hR F) r z := by
  simp only [NilpotentVolterra.rawField, NilpotentVolterra.extendPath, sideData_true,
    symmetricRawField, reflectedForcing]
  rw [projIcc_of_mem hR hr, projIcc_of_mem (by linarith : -R ≤ R)
    ⟨neg_le_neg hr.2, (neg_nonpos.mpr hr.1).trans hR⟩]
  rfl

theorem sideRawCoefficient_pos {R : ℝ} (hR : 0 ≤ R)
    (A : ℂ → SymmetricCoefficientPath R) {r : ℝ} (hr : r ∈ Icc 0 R) (z : ℂ) :
    NilpotentVolterra.rawCoefficient hR (sideData hR false A) r z =
      symmetricRawCoefficient hR A r z := by
  simp only [NilpotentVolterra.rawCoefficient, sideData_false, symmetricRawCoefficient]
  rw [projIcc_of_mem hR hr, projIcc_of_mem (by linarith : -R ≤ R)
    ⟨(neg_nonpos.mpr hR).trans hr.1, hr.2⟩]
  rfl

theorem sideRawCoefficient_neg {R : ℝ} (hR : 0 ≤ R)
    (A : ℂ → SymmetricCoefficientPath R) {r : ℝ} (hr : r ∈ Icc 0 R) (z : ℂ) :
    NilpotentVolterra.rawCoefficient hR (sideData hR true A) r z =
      reflectCoeff (symmetricRawCoefficient hR A) r z := by
  simp only [NilpotentVolterra.rawCoefficient, sideData_true, symmetricRawCoefficient,
    reflectCoeff]
  rw [projIcc_of_mem hR hr, projIcc_of_mem (by linarith : -R ≤ R)
    ⟨neg_le_neg hr.2, (neg_nonpos.mpr hr.1).trans hR⟩]
  ext i j
  rfl

theorem side_shape {R : ℝ} (hR : 0 ≤ R)
    {A : ℂ → SymmetricCoefficientPath R}
    (hA : DerivativeShape (symmetricRawCoefficient hR A)) (b : Bool) :
    DerivativeShape (NilpotentVolterra.rawCoefficient hR (sideData hR b A)) := by
  intro r z i j hij
  let s := projIcc 0 R hR r
  have hs : NilpotentVolterra.rawCoefficient hR (sideData hR b A) r z =
      NilpotentVolterra.rawCoefficient hR (sideData hR b A) s z := by
    simp only [NilpotentVolterra.rawCoefficient, s, projIcc_val]
  rw [hs]
  cases b with
  | false => rw [sideRawCoefficient_pos hR A s.2 z]; exact hA s z i j hij
  | true =>
      rw [sideRawCoefficient_neg hR A s.2 z]
      change -symmetricRawCoefficient hR A (-s) z i j = 0
      rw [hA (-s) z i j hij, neg_zero]

/-- The positive solver's lifted function satisfies the normalized integral
equation, including its value at zero. -/
theorem lifted_integralEquation {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → NilpotentVolterra.CoefficientPath R}
    {f W : ℂ → NilpotentVolterra.Path R} {U : Set ℂ}
    (hU : IsOpen U) (hWholo : DifferentiableOn ℂ W U)
    (hW : ∀ z ∈ U, W z = NilpotentVolterra.pathInverse hR exponent
      (NilpotentVolterra.rhsPath A₀ A₁ f W z)) :
    IntegralEquationOn (Icc 0 R) U (NilpotentVolterra.rawCoefficient hR A₀)
      (NilpotentVolterra.rawCoefficient hR A₁) (NilpotentVolterra.rawField hR f)
      (NilpotentVolterra.liftedField hR A₀ A₁ f W) := by
  intro r hr z hz
  change radialInverse (fun s z => NilpotentVolterra.extendPath hR
    (NilpotentVolterra.rhsPath A₀ A₁ f W z) s) r z = _
  apply radialInverse_congr_at
  intro t ht
  exact NilpotentVolterra.liftedField_rhs hR A₀ A₁ f W hU hWholo hW
    (NilpotentVolterra.scaled_radius_mem hr ht) hz

theorem positive_equation_change_data {R : ℝ} {U : Set ℂ}
    {A₀ A₁ B₀ B₁ : Coeff} {f g W : Field}
    (h : IntegralEquationOn (Icc 0 R) U A₀ A₁ f W)
    (h₀ : ∀ r ∈ Icc 0 R, ∀ z ∈ U, A₀ r z = B₀ r z)
    (h₁ : ∀ r ∈ Icc 0 R, ∀ z ∈ U, A₁ r z = B₁ r z)
    (hf : ∀ r ∈ Icc 0 R, ∀ z ∈ U, f r z = g r z) :
    IntegralEquationOn (Icc 0 R) U B₀ B₁ g W := by
  intro r hr z hz
  rw [h r hr z hz]
  apply radialInverse_congr_at
  intro t ht
  have htr := NilpotentVolterra.scaled_radius_mem hr ht
  simp only [equationRHS, matrixAction, h₀ _ htr _ hz, h₁ _ htr _ hz, hf _ htr _ hz]

/-- Side solution, constructed using `NilpotentVolterra.liftedField`. -/
noncomputable def sideSolution {R : ℝ} (hR : 0 ≤ R) (b : Bool)
    (A₀ A₁ : ℂ → SymmetricCoefficientPath R) (f : ℂ → SymmetricPath R Vec) : Field :=
  NilpotentVolterra.liftedField hR (sideData hR b A₀) (sideData hR b A₁) (sideData hR b f)
    (NilpotentVolterra.integralSolution hR
      (sideData hR b A₀) (sideData hR b A₁) (sideData hR b f))

/-- Two independently solved half-intervals are glued at their common zero
axis trace. No parity of the output occurs in this definition. -/
noncomputable def symmetricSolution {R : ℝ} (hR : 0 ≤ R)
    (A₀ A₁ : ℂ → SymmetricCoefficientPath R) (f : ℂ → SymmetricPath R Vec) : Field :=
  glue (sideSolution hR false A₀ A₁ f) (sideSolution hR true A₀ A₁ f)

theorem sideSolution_spec {R : ℝ} (hR : 0 ≤ R) (b : Bool)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁)) :
    NilpotentVolterra.IsRegularSolution R U
      (NilpotentVolterra.rawCoefficient hR (sideData hR b A₀))
      (NilpotentVolterra.rawCoefficient hR (sideData hR b A₁))
      (NilpotentVolterra.rawField hR (sideData hR b f)) (sideSolution hR b A₀ A₁ f) ∧
    IntegralEquationOn (Icc 0 R) U
      (NilpotentVolterra.rawCoefficient hR (sideData hR b A₀))
      (NilpotentVolterra.rawCoefficient hR (sideData hR b A₁))
      (NilpotentVolterra.rawField hR (sideData hR b f)) (sideSolution hR b A₀ A₁ f) ∧
    ∀ z, sideSolution hR b A₀ A₁ f 0 z = 0 := by
  obtain ⟨hholo, heq⟩ := NilpotentVolterra.integralSolution_spec_open hR hU
    (sideData_holomorphic hR b hA₀) (sideData_holomorphic hR b hA₁)
    (sideData_holomorphic hR b hf) (side_shape hR hshape b)
  exact ⟨NilpotentVolterra.liftedField_isRegularSolution hR _ _ _ _ hU hholo heq,
    lifted_integralEquation hR hU hholo heq,
    NilpotentVolterra.liftedField_axis_zero hR _ _ _ _⟩

/-- Actual existence on a symmetric radial interval. Only holomorphy in
the parameter and continuity in the radial coordinate are used here. -/
theorem symmetricSolution_spec {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁)) :
    IsSymmetricIntegralSolution R U (symmetricRawCoefficient hR A₀)
      (symmetricRawCoefficient hR A₁) (symmetricRawField hR f)
      (symmetricSolution hR A₀ A₁ f) := by
  obtain ⟨hp, hpEq, hpZero⟩ := sideSolution_spec hR false hU hA₀ hA₁ hf hshape
  obtain ⟨hm, hmEq, hmZero⟩ := sideSolution_spec hR true hU hA₀ hA₁ hf hshape
  have hzero : ∀ z, sideSolution hR false A₀ A₁ f 0 z =
      sideSolution hR true A₀ A₁ f 0 z := by
    intro z
    rw [hpZero z, hmZero z]
  have hpEq' : IntegralEquationOn (Icc 0 R) U (symmetricRawCoefficient hR A₀)
      (symmetricRawCoefficient hR A₁) (symmetricRawField hR f)
      (sideSolution hR false A₀ A₁ f) :=
    positive_equation_change_data hpEq
      (fun r hr z _ => sideRawCoefficient_pos hR A₀ hr z)
      (fun r hr z _ => sideRawCoefficient_pos hR A₁ hr z)
      (fun r hr z _ => sideRawField_pos hR f hr z)
  have hmEq' : IntegralEquationOn (Icc 0 R) U (reflectCoeff (symmetricRawCoefficient hR A₀))
      (reflectCoeff (symmetricRawCoefficient hR A₁)) (reflectedForcing (symmetricRawField hR f))
      (sideSolution hR true A₀ A₁ f) :=
    positive_equation_change_data hmEq
      (fun r hr z _ => sideRawCoefficient_neg hR A₀ hr z)
      (fun r hr z _ => sideRawCoefficient_neg hR A₁ hr z)
      (fun r hr z _ => sideRawField_neg hR f hr z)
  exact {
    jointly_continuous := glue_jointly_continuous (fun z _ => hzero z)
      hp.jointly_continuous hm.jointly_continuous
    parameter_holomorphic := fun _ hr i => glue_parameter_holomorphic
      hp.parameter_holomorphic hm.parameter_holomorphic hr i
    integral_equation := glue_integralEquation hzero hpEq' hmEq'
    axis_zero := fun z _ => (glue_nonneg _ _ le_rfl z).trans (hpZero z) }

theorem exists_symmetric_integral_solution {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁)) :
    ∃ W, IsSymmetricIntegralSolution R U (symmetricRawCoefficient hR A₀)
      (symmetricRawCoefficient hR A₁) (symmetricRawField hR f) W :=
  ⟨symmetricSolution hR A₀ A₁ f, symmetricSolution_spec hR hU hA₀ hA₁ hf hshape⟩

theorem reflected_matrix_parity {S : Set ℝ} {U : Set ℂ} {A : Coeff}
    (hA : CoefficientParityOn S U A) {r : ℝ} (hr : r ∈ S)
    {z : ℂ} (hz : z ∈ U) (v : Vec) :
    (reflectCoeff A r z).mulVec (parityVec v) = parityVec ((A r z).mulVec v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, parityVec_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (-A (-r) z i j) * (paritySign j * v j) = paritySign i * (A r z i j * v j)
  rw [hA r hr z hz i j]
  calc
    _ = paritySign i * A r z i j * (paritySign j * paritySign j) * v j := by ring
    _ = _ := by rw [paritySign_mul_self]; ring

theorem reflected_forcing_parity {S : Set ℝ} {U : Set ℂ} {f : Field}
    (hf : ForcingParityOn S U f) {r : ℝ} (hr : r ∈ S) {z : ℂ} (hz : z ∈ U) :
    reflectedForcing f r z = parityVec (f r z) := by
  funext i
  change -f (-r) z i = paritySign i * f r z i
  rw [hf r hr z hz i]
  ring

/-- Parity path, given by `ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) R) parityVec`. -/
noncomputable def parityPath (R : ℝ) :
    NilpotentVolterra.Path R →L[ℂ] NilpotentVolterra.Path R :=
  ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) R) parityVec

@[simp] theorem parityPath_apply {R : ℝ} (W : NilpotentVolterra.Path R)
    (r : Icc (0 : ℝ) R) : parityPath R W r = parityVec (W r) := rfl

@[simp] theorem parityPath_involutive {R : ℝ} (W : NilpotentVolterra.Path R) :
    parityPath R (parityPath R W) = W := by
  ext r i
  exact congrFun (parityVec_involutive (W r)) i

theorem parityPath_deriv {R : ℝ} {W : ℂ → NilpotentVolterra.Path R} {z : ℂ}
    (hW : DifferentiableAt ℂ W z) :
    deriv (fun w => parityPath R (W w)) z = parityPath R (deriv W z) :=
  ((parityPath R).hasFDerivAt.comp_hasDerivAt z hW.hasDerivAt).deriv

/-- The diagonal parity action commutes with the actual radial integral. -/
theorem parityPath_inverse {R : ℝ} (hR : 0 ≤ R) (W : NilpotentVolterra.Path R) :
    parityPath R (NilpotentVolterra.pathInverse hR exponent W) =
      NilpotentVolterra.pathInverse hR exponent (parityPath R W) := by
  ext r i
  change paritySign i • ((r : ℝ) • (∫ t in (0 : ℝ)..1,
      (t ^ exponent i) • NilpotentVolterra.extendPath hR W (t * r) i)) =
    (r : ℝ) • (∫ t in (0 : ℝ)..1,
      (t ^ exponent i) • (paritySign i • NilpotentVolterra.extendPath hR W (t * r) i))
  rw [smul_comm (paritySign i), ← intervalIntegral.integral_smul]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact smul_comm _ _ _

theorem sideData_coefficient_parity {R : ℝ} (hR : 0 ≤ R)
    {A : ℂ → SymmetricCoefficientPath R} {U : Set ℂ}
    (hA : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A))
    {z : ℂ} (hz : z ∈ U) (r : Icc (0 : ℝ) R) (v : Vec) :
    sideData hR true A z r (parityVec v) = parityVec (sideData hR false A z r v) := by
  have hh := reflected_matrix_parity hA r.2 hz v
  rw [← sideRawCoefficient_neg hR A r.2 z, ← sideRawCoefficient_pos hR A r.2 z] at hh
  simpa only [NilpotentVolterra.rawCoefficient_mulVec, projIcc_val] using hh

theorem sideData_forcing_parity {R : ℝ} (hR : 0 ≤ R)
    {f : ℂ → SymmetricPath R Vec} {U : Set ℂ}
    (hf : ForcingParityOn (Icc 0 R) U (symmetricRawField hR f))
    {z : ℂ} (hz : z ∈ U) (r : Icc (0 : ℝ) R) :
    sideData hR true f z r = parityVec (sideData hR false f z r) := by
  have hh := reflected_forcing_parity hf r.2 hz
  rw [← sideRawField_neg hR f r.2 z, ← sideRawField_pos hR f r.2 z] at hh
  simpa only [NilpotentVolterra.rawField, NilpotentVolterra.extendPath, projIcc_val] using hh

theorem rhsPath_parity {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {W : ℂ → NilpotentVolterra.Path R} {U : Set ℂ}
    (hA₀ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₀))
    (hA₁ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₁))
    (hf : ForcingParityOn (Icc 0 R) U (symmetricRawField hR f))
    {z : ℂ} (hz : z ∈ U) (hW : DifferentiableAt ℂ W z) :
    NilpotentVolterra.rhsPath (sideData hR true A₀) (sideData hR true A₁)
      (sideData hR true f) (fun w => parityPath R (W w)) z =
    parityPath R (NilpotentVolterra.rhsPath (sideData hR false A₀)
      (sideData hR false A₁) (sideData hR false f) W z) := by
  unfold NilpotentVolterra.rhsPath
  rw [parityPath_deriv hW]
  ext r i
  change (sideData hR true f z r + ((sideData hR true A₀ z r) (parityVec (W z r)) +
    (sideData hR true A₁ z r) (parityVec (deriv W z r)))) i =
    (parityVec (sideData hR false f z r +
      ((sideData hR false A₀ z r) (W z r) +
        (sideData hR false A₁ z r) (deriv W z r)))) i
  rw [sideData_forcing_parity hR hf hz r,
    sideData_coefficient_parity hR hA₀ hz r,
    sideData_coefficient_parity hR hA₁ hz r, map_add, map_add]

/-- Parity transforms a solution of the positive equation into a solution
of the reflected positive equation. -/
theorem parity_transforms_equation {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {W : ℂ → NilpotentVolterra.Path R} {U : Set ℂ} (hU : IsOpen U)
    (hW : DifferentiableOn ℂ W U)
    (hA₀ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₀))
    (hA₁ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₁))
    (hf : ForcingParityOn (Icc 0 R) U (symmetricRawField hR f))
    (heq : ∀ z ∈ U, W z = NilpotentVolterra.pathInverse hR exponent
      (NilpotentVolterra.rhsPath (sideData hR false A₀) (sideData hR false A₁)
        (sideData hR false f) W z)) :
    ∀ z ∈ U, parityPath R (W z) = NilpotentVolterra.pathInverse hR exponent
      (NilpotentVolterra.rhsPath (sideData hR true A₀) (sideData hR true A₁)
        (sideData hR true f) (fun w => parityPath R (W w)) z) := by
  intro z hz
  rw [rhsPath_parity hR hA₀ hA₁ hf hz (hW.differentiableAt (hU.mem_nhds hz)),
    heq z hz, parityPath_inverse]

/-- The half-interval solutions have the required relation by uniqueness
of the genuine integral equation. -/
theorem side_curves_parity {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁))
    (hpA₀ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₀))
    (hpA₁ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₁))
    (hpf : ForcingParityOn (Icc 0 R) U (symmetricRawField hR f)) :
    EqOn
      (NilpotentVolterra.integralSolution hR (sideData hR true A₀)
        (sideData hR true A₁) (sideData hR true f))
      (fun z => parityPath R (NilpotentVolterra.integralSolution hR
        (sideData hR false A₀) (sideData hR false A₁) (sideData hR false f) z)) U := by
  obtain ⟨hp, hpEq⟩ := NilpotentVolterra.integralSolution_spec_open hR hU
    (sideData_holomorphic hR false hA₀) (sideData_holomorphic hR false hA₁)
    (sideData_holomorphic hR false hf) (side_shape hR hshape false)
  obtain ⟨hm, hmEq⟩ := NilpotentVolterra.integralSolution_spec_open hR hU
    (sideData_holomorphic hR true hA₀) (sideData_holomorphic hR true hA₁)
    (sideData_holomorphic hR true hf) (side_shape hR hshape true)
  exact NilpotentVolterra.integral_solution_unique hR hU
    (sideData_holomorphic hR true hA₀) (sideData_holomorphic hR true hA₁)
    hm ((parityPath R).differentiable.comp_differentiableOn hp)
    (side_shape hR hshape true) hmEq
    (parity_transforms_equation hR hU hp hpA₀ hpA₁ hpf hpEq)

theorem sideSolution_parity {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁))
    (hpA₀ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₀))
    (hpA₁ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₁))
    (hpf : ForcingParityOn (Icc 0 R) U (symmetricRawField hR f))
    {r : ℝ} (hr : r ∈ Icc 0 R) {z : ℂ} (hz : z ∈ U) :
    sideSolution hR true A₀ A₁ f r z =
      parityVec (sideSolution hR false A₀ A₁ f r z) := by
  obtain ⟨_, hpEq⟩ := NilpotentVolterra.integralSolution_spec_open hR hU
    (sideData_holomorphic hR false hA₀) (sideData_holomorphic hR false hA₁)
    (sideData_holomorphic hR false hf) (side_shape hR hshape false)
  obtain ⟨_, hmEq⟩ := NilpotentVolterra.integralSolution_spec_open hR hU
    (sideData_holomorphic hR true hA₀) (sideData_holomorphic hR true hA₁)
    (sideData_holomorphic hR true hf) (side_shape hR hshape true)
  unfold sideSolution
  rw [NilpotentVolterra.liftedField_eq_trace hR _ _ _ _ (hmEq z hz) hr,
    NilpotentVolterra.liftedField_eq_trace hR _ _ _ _ (hpEq z hz) hr]
  exact congrArg (fun V : NilpotentVolterra.Path R => V (projIcc 0 R hR r))
    (side_curves_parity hR hU hA₀ hA₁ hf hshape hpA₀ hpA₁ hpf hz)

/-- The actual symmetric solution has the prescribed vector parity.
The coefficient/source parity hypotheses are transformed through the
integral equation, and equality follows from holomorphic uniqueness. -/
theorem symmetricSolution_parity {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁))
    (hpA₀ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₀))
    (hpA₁ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₁))
    (hpf : ForcingParityOn (Icc 0 R) U (symmetricRawField hR f))
    {r : ℝ} (hr : r ∈ Icc (-R) R) {z : ℂ} (hz : z ∈ U) :
    symmetricSolution hR A₀ A₁ f (-r) z =
      parityVec (symmetricSolution hR A₀ A₁ f r z) := by
  have hzero : ∀ w, sideSolution hR false A₀ A₁ f 0 w =
      sideSolution hR true A₀ A₁ f 0 w := by
    intro w
    exact (NilpotentVolterra.liftedField_axis_zero hR _ _ _ _ w).trans
      (NilpotentVolterra.liftedField_axis_zero hR _ _ _ _ w).symm
  unfold symmetricSolution
  by_cases hs : 0 ≤ r
  · rw [glue_nonpos hzero (neg_nonpos.mpr hs), neg_neg, glue_nonneg _ _ hs]
    exact sideSolution_parity hR hU hA₀ hA₁ hf hshape hpA₀ hpA₁ hpf ⟨hs, hr.2⟩ hz
  · have hs' : r ≤ 0 := le_of_not_ge hs
    have hn : -r ∈ Icc 0 R := ⟨neg_nonneg.mpr hs', by linarith [hr.1]⟩
    rw [glue_nonneg _ _ hn.1, glue_nonpos hzero hs',
      sideSolution_parity hR hU hA₀ hA₁ hf hshape hpA₀ hpA₁ hpf hn hz,
      parityVec_involutive]

theorem symmetricSolution_parity_of_global {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁))
    (hpA₀ : CoefficientParity (symmetricRawCoefficient hR A₀))
    (hpA₁ : CoefficientParity (symmetricRawCoefficient hR A₁))
    (hpf : ForcingParity (symmetricRawField hR f))
    {r : ℝ} (hr : r ∈ Icc (-R) R) {z : ℂ} (hz : z ∈ U) :
    symmetricSolution hR A₀ A₁ f (-r) z =
      parityVec (symmetricSolution hR A₀ A₁ f r z) :=
  symmetricSolution_parity hR hU hA₀ hA₁ hf hshape
    (fun r _ z _ => hpA₀ r z) (fun r _ z _ => hpA₁ r z)
    (fun r _ z _ => hpf r z) hr hz

/-- This is the component form used by the smooth even-descent theorem. -/
theorem first_components_even {W : Field} {R : ℝ} {U : Set ℂ}
    (hW : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, W (-r) z = parityVec (W r z))
    (i : Fin 6) (hi : i.val < 4) {z : ℂ} (hz : z ∈ U) :
    ∀ r ∈ Ioo (-R) R, W (-r) z i = W r z i := by
  intro r hr
  simpa [parityVec_apply, paritySign, hi] using congrFun (hW r ⟨hr.1.le, hr.2.le⟩ z hz) i

theorem last_components_odd {W : Field} {R : ℝ} {U : Set ℂ}
    (hW : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, W (-r) z = parityVec (W r z))
    (i : Fin 6) (hi : 4 ≤ i.val) {z : ℂ} (hz : z ∈ U) :
    ∀ r ∈ Ioo (-R) R, W (-r) z i = -W r z i := by
  intro r hr
  simpa [parityVec_apply, paritySign, not_lt.mpr hi] using
    congrFun (hW r ⟨hr.1.le, hr.2.le⟩ z hz) i

/-- Two derivatives with the same value and axis trace glue to an ordinary
two-sided derivative. -/
theorem hasDerivAt_glue_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {v : E} (hf : HasDerivAt f v 0) (hg : HasDerivAt g v 0)
    (h0 : f 0 = g 0) :
    HasDerivAt (fun r => if 0 ≤ r then f r else g r) v 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hh := hf.tendsto_slope_zero.if' (p := fun r : ℝ => 0 ≤ r) hg.tendsto_slope_zero
  convert! hh using 1
  funext r
  by_cases hr : 0 ≤ r <;> simp [hr, h0]

/-- The derivatives from both sides match at the axis. The value is
determined by the forcing, with the exact singular-diagonal factor. -/
theorem symmetricSolution_hasDerivAt_zero {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁))
    {z : ℂ} (hz : z ∈ U) (i : Fin 6) :
    HasDerivAt (fun r => symmetricSolution hR A₀ A₁ f r z i)
      ((1 / ((exponent i : ℝ) + 1)) • symmetricRawField hR f 0 z i) 0 := by
  obtain ⟨hp, _, _⟩ := sideSolution_spec hR false hU hA₀ hA₁ hf hshape
  obtain ⟨hm, _, _⟩ := sideSolution_spec hR true hU hA₀ hA₁ hf hshape
  have hdp := (hp.radial_differentiable z hz i 0).hasDerivAt
  have heqp := hp.axis_derivative_eq_forcing hU hz i
  change deriv (fun r => sideSolution hR false A₀ A₁ f r z i) 0 = _ at heqp
  rw [heqp, sideRawField_pos hR f ⟨le_rfl, hR⟩ z] at hdp
  have hdm := (hm.radial_differentiable z hz i 0).hasDerivAt
  have heqm := hm.axis_derivative_eq_forcing hU hz i
  change deriv (fun r => sideSolution hR true A₀ A₁ f r z i) 0 = _ at heqm
  rw [heqm, sideRawField_neg hR f ⟨le_rfl, hR⟩ z] at hdm
  simp only [reflectedForcing, neg_zero, Pi.neg_apply, smul_neg] at hdm
  have hdneg : HasDerivAt (fun r => sideSolution hR true A₀ A₁ f (-r) z i)
      ((1 / ((exponent i : ℝ) + 1)) • symmetricRawField hR f 0 z i) 0 := by
    simpa only [Function.comp_def, neg_one_smul, neg_neg] using
      hdm.scomp_of_eq 0 (hasDerivAt_neg (0 : ℝ)) (by simp)
  have hzero : sideSolution hR false A₀ A₁ f 0 z i =
      sideSolution hR true A₀ A₁ f (-0) z i := by
    simpa only [neg_zero] using congrFun ((hp.axis_zero z hz).trans (hm.axis_zero z hz).symm) i
  simpa only [symmetricSolution, glue, ite_apply] using hasDerivAt_glue_zero hdp hdneg hzero

/-- Uniqueness of the glued actual lifts in the holomorphic path class.
Both sides are compared by the proved positive Volterra uniqueness
theorem; no uniqueness premise is introduced. -/
theorem glued_solution_unique {R : ℝ} (hR : 0 ≤ R) {U : Set ℂ} (hU : IsOpen U)
    {A₀ A₁ : Bool → ℂ → NilpotentVolterra.CoefficientPath R}
    {f W₀ W₁ : Bool → ℂ → NilpotentVolterra.Path R}
    (hA₀ : ∀ b, DifferentiableOn ℂ (A₀ b) U)
    (hA₁ : ∀ b, DifferentiableOn ℂ (A₁ b) U)
    (hW₀ : ∀ b, DifferentiableOn ℂ (W₀ b) U)
    (hW₁ : ∀ b, DifferentiableOn ℂ (W₁ b) U)
    (hshape : ∀ b, DerivativeShape (NilpotentVolterra.rawCoefficient hR (A₁ b)))
    (heq₀ : ∀ b z, z ∈ U → W₀ b z = NilpotentVolterra.pathInverse hR exponent
      (NilpotentVolterra.rhsPath (A₀ b) (A₁ b) (f b) (W₀ b) z))
    (heq₁ : ∀ b z, z ∈ U → W₁ b z = NilpotentVolterra.pathInverse hR exponent
      (NilpotentVolterra.rhsPath (A₀ b) (A₁ b) (f b) (W₁ b) z))
    (r : ℝ) {z : ℂ} (hz : z ∈ U) :
    glue (NilpotentVolterra.liftedField hR (A₀ false) (A₁ false) (f false) (W₀ false))
      (NilpotentVolterra.liftedField hR (A₀ true) (A₁ true) (f true) (W₀ true)) r z =
    glue (NilpotentVolterra.liftedField hR (A₀ false) (A₁ false) (f false) (W₁ false))
      (NilpotentVolterra.liftedField hR (A₀ true) (A₁ true) (f true) (W₁ true)) r z := by
  have heq (b : Bool) : EqOn (W₀ b) (W₁ b) U :=
    NilpotentVolterra.integral_solution_unique hR hU (hA₀ b) (hA₁ b) (hW₀ b) (hW₁ b)
      (hshape b) (heq₀ b) (heq₁ b)
  have hboth (b : Bool) (s : ℝ) :
      NilpotentVolterra.liftedField hR (A₀ b) (A₁ b) (f b) (W₀ b) s z =
      NilpotentVolterra.liftedField hR (A₀ b) (A₁ b) (f b) (W₁ b) s z := by
    have hder : deriv (W₀ b) z = deriv (W₁ b) z :=
      (show W₀ b =ᶠ[𝓝 z] W₁ b from Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (heq b)).deriv_eq
    have hrhs : NilpotentVolterra.rhsPath (A₀ b) (A₁ b) (f b) (W₀ b) z =
        NilpotentVolterra.rhsPath (A₀ b) (A₁ b) (f b) (W₁ b) z := by
      simp only [NilpotentVolterra.rhsPath, heq b hz, hder]
    unfold NilpotentVolterra.liftedField
    rw [hrhs]
  unfold glue
  split_ifs
  · exact hboth false r
  · exact hboth true (-r)

end NavierStokes.VolterraParity
