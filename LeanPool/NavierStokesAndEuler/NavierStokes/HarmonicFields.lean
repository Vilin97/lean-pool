/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicCalculus
public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanResidual
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Finite integer-harmonic fields

The coefficients form a genuine finite group algebra. Evaluation is the
literal exponential sum, multiplication is convolution, and angular means
are actual interval integrals over a period of length `2*pi`.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped BigOperators Topology ContDiff ComplexConjugate Pointwise

namespace NavierStokes.HarmonicFields

/-- Coefficients: an abbreviation for `AddMonoidAlgebra (α → ℂ) ℤ`. -/
abbrev Coefficients (α : Type*) := AddMonoidAlgebra (α → ℂ) ℤ

/-- Coefficient access for the wrapped group algebra. -/
instance {α : Type*} : CoeFun (Coefficients α) (fun _ => ℤ → α → ℂ) :=
  ⟨fun c => c.coeff⟩

/-- Support: an abbreviation for `c.coeff.support`. -/
abbrev Coefficients.support {α : Type*} (c : Coefficients α) : Finset ℤ := c.coeff.support

/-- Sum: an abbreviation for `c.coeff.sum f`. -/
abbrev Coefficients.sum {α M : Type*} [AddCommMonoid M] (c : Coefficients α)
    (f : ℤ → (α → ℂ) → M) : M := c.coeff.sum f

/-- Character, given by `Complex.exp ((j : ℂ) * (φ : ℂ) * Complex.I)`. -/
noncomputable def character (j : ℤ) (φ : ℝ) : ℂ :=
  Complex.exp ((j : ℂ) * (φ : ℂ) * Complex.I)

@[simp] theorem character_zero (φ : ℝ) : character 0 φ = 1 := by
  simp [character]

theorem character_add (i j : ℤ) (φ : ℝ) :
    character (i + j) φ = character i φ * character j φ := by
  simp only [character, Int.cast_add, add_mul, Complex.exp_add]

theorem character_phase_add (j : ℤ) (φ ψ : ℝ) :
    character j (φ + ψ) = character j φ * character j ψ := by
  simp only [character, Complex.ofReal_add, mul_add, add_mul, Complex.exp_add]

theorem character_int_mul (j kp : ℤ) (θ : ℝ) :
    character j ((kp : ℝ) * θ) = character (j * kp) θ := by
  unfold character
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_intCast, Int.cast_mul]
  ring

@[simp] theorem norm_character (j : ℤ) (φ : ℝ) : ‖character j φ‖ = 1 := by
  have he : (j : ℂ) * (φ : ℂ) * Complex.I = ((j * φ : ℝ) : ℂ) * Complex.I := by
    simp only [Complex.ofReal_mul, Complex.ofReal_intCast]
  rw [character, he, Complex.norm_exp_ofReal_mul_I]

theorem character_neg (j : ℤ) (φ : ℝ) : character (-j) φ = conj (character j φ) := by
  rw [character, character, ← Complex.exp_conj]
  congr 1
  simp only [Int.cast_neg, map_mul, map_intCast, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem character_continuous (j : ℤ) : Continuous (character j) := by
  exact ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const).cexp

/-- Character hom, bundling `toFun`, `map_one`, `map_mul`. -/
noncomputable def characterHom (φ : ℝ) : Multiplicative ℤ →* ℂ where
  toFun j := character (Multiplicative.toAdd j) φ
  map_one' := character_zero φ
  map_mul' i j := character_add (Multiplicative.toAdd i) (Multiplicative.toAdd j) φ

/-- Evaluate hom, given by `AddMonoidAlgebra.liftNCRingHom (Pi.evalRingHom (fun _ : α => ℂ) x)
(characterHom φ) (fun _ _ => Commute.all _ _)`. -/
noncomputable def evaluateHom {α : Type*} (x : α) (φ : ℝ) : Coefficients α →+* ℂ :=
  AddMonoidAlgebra.liftNCRingHom (Pi.evalRingHom (fun _ : α => ℂ) x) (characterHom φ)
    (fun _ _ => Commute.all _ _)

/-- Evaluate, given by `c.sum (fun j a => a x * character j φ)`. -/
noncomputable def evaluate {α : Type*} (c : Coefficients α) (x : α) (φ : ℝ) : ℂ :=
  c.sum (fun j a => a x * character j φ)

theorem evaluate_eq_hom {α : Type*} (c : Coefficients α) (x : α) (φ : ℝ) :
    evaluate c x φ = evaluateHom x φ c := rfl

@[simp] theorem evaluate_zero {α : Type*} (x : α) (φ : ℝ) :
    evaluate (0 : Coefficients α) x φ = 0 := (evaluateHom x φ).map_zero

theorem evaluate_add {α : Type*} (c d : Coefficients α) (x : α) (φ : ℝ) :
    evaluate (c + d) x φ = evaluate c x φ + evaluate d x φ := (evaluateHom x φ).map_add c d

/-- The actual product of two finite fields is evaluation of the finite
coefficient convolution. -/
theorem evaluate_mul {α : Type*} (c d : Coefficients α) (x : α) (φ : ℝ) :
    evaluate (c * d) x φ = evaluate c x φ * evaluate d x φ := (evaluateHom x φ).map_mul c d

theorem evaluate_single {α : Type*} (j : ℤ) (a : α → ℂ) (x : α) (φ : ℝ) :
    evaluate (AddMonoidAlgebra.single j a : Coefficients α) x φ = a x * character j φ := by
  simp [evaluate, Coefficients.sum]

theorem evaluate_over {α : Type*} (c : Coefficients α) (s : Finset ℤ)
    (hs : c.support ⊆ s) (x : α) (φ : ℝ) :
    evaluate c x φ = ∑ j ∈ s, c j x * character j φ := by
  apply Finset.sum_subset hs
  intro j hj hnot
  rw [Finsupp.notMem_support_iff.mp hnot]
  simp

/-- The slow/auxiliary parameter is `x`. Its coefficient functions have
no angular input. The angular frequency is the literal integer `j*kp`. -/
noncomputable def field {α : Type*} (c : Coefficients α) (k : ℝ) (Φ : α → ℝ)
    (kp : ℤ) (p : α × ℝ) : ℂ := evaluate c p.1 (k * Φ p.1 + (kp : ℝ) * p.2)

theorem field_expansion {α : Type*} (c : Coefficients α) (k : ℝ) (Φ : α → ℝ)
    (kp : ℤ) (x : α) (θ : ℝ) :
    field c k Φ kp (x, θ) =
      ∑ j ∈ c.support, c j x * character j (k * Φ x) * character (j * kp) θ := by
  simp only [field, evaluate, Finsupp.sum, character_phase_add, character_int_mul, mul_assoc]

theorem field_mul {α : Type*} (c d : Coefficients α) (k : ℝ) (Φ : α → ℝ)
    (kp : ℤ) (p : α × ℝ) :
    field (c * d) k Φ kp p = field c k Φ kp p * field d k Φ kp p :=
  evaluate_mul c d p.1 _

theorem field_angular_continuous {α : Type*} (c : Coefficients α) (k : ℝ)
    (Φ : α → ℝ) (kp : ℤ) (x : α) : Continuous (fun θ => field c k Φ kp (x, θ)) := by
  simp only [field_expansion]
  exact continuous_finsetSum _ (fun j _ => continuous_const.fun_mul (character_continuous _))

/-- Period, given by `2 * Real.pi`. -/
noncomputable def period : ℝ := 2 * Real.pi

theorem period_pos : 0 < period := mul_pos (by norm_num) Real.pi_pos

theorem period_ne_zero : period ≠ 0 := period_pos.ne'

/-- This is a genuine normalized angular integral. -/
noncomputable def angularMean (f : ℝ → ℂ) : ℂ :=
  (period : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..period, f θ

theorem character_period (j : ℤ) : character j period = 1 := by
  have he : (j : ℂ) * (period : ℂ) * Complex.I =
      (j : ℂ) * (2 * Real.pi * Complex.I) := by
    simp only [period, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [character, he, Complex.exp_int_mul_two_pi_mul_I]

theorem character_periodic (j : ℤ) : Function.Periodic (character j) period := by
  intro θ
  rw [character_phase_add, character_period, mul_one]

theorem field_angular_periodic {α : Type*} (c : Coefficients α) (k : ℝ)
    (Φ : α → ℝ) (kp : ℤ) (x : α) :
    Function.Periodic (fun θ => field c k Φ kp (x, θ)) period := by
  intro θ
  simp only [field_expansion]
  exact Finset.sum_congr rfl (fun j _ => congrArg
    (c j x * character j (k * Φ x) * ·) (character_periodic (j * kp) θ))

theorem integral_character (j : ℤ) :
    (∫ θ in (0 : ℝ)..period, character j θ) = if j = 0 then (period : ℂ) else 0 := by
  by_cases hj : j = 0
  · simp [hj, period]
  · rw [ite_eq_right hj]
    have hc : (j : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hj) Complex.I_ne_zero
    have he : character j = fun θ : ℝ => Complex.exp (((j : ℂ) * Complex.I) * θ) := by
      funext θ
      unfold character
      congr 1
      ring
    rw [he, integral_exp_mul_complex hc]
    have hb : Complex.exp (((j : ℂ) * Complex.I) * (period : ℂ)) = 1 := by
      convert! character_period j using 1
      unfold character
      congr 1
      ring
    simp [hb]

theorem angularMean_const_character (A : ℂ) (j : ℤ) :
    angularMean (fun θ => A * character j θ) = if j = 0 then A else 0 := by
  rw [angularMean, intervalIntegral.integral_const_mul, integral_character]
  by_cases hj : j = 0
  · rw [ite_eq_left hj, ite_eq_left hj]
    have hp : (period : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr period_ne_zero
    field_simp
  · simp [hj]

theorem angularMean_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    angularMean (fun θ => ∑ i ∈ s, f i θ) = ∑ i ∈ s, angularMean (f i) := by
  simp only [angularMean]
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).intervalIntegrable _ _),
    Finset.mul_sum]

/-- Nonzero integer angular frequency makes the actual angular mean pick
precisely the zero harmonic, regardless of the slow phase or carrier band. -/
theorem angularMean_field {α : Type*} (c : Coefficients α) (k : ℝ) (Φ : α → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (x : α) :
    angularMean (fun θ => field c k Φ kp (x, θ)) = c 0 x := by
  simp only [field_expansion]
  rw [angularMean_sum c.support _ (fun j _ => continuous_const.fun_mul (character_continuous _))]
  simp only [angularMean_const_character, mul_eq_zero, hkp, or_false]
  by_cases h0 : 0 ∈ c.support
  · simp [h0]
  · have hc : c 0 = 0 := Finsupp.notMem_support_iff.mp h0
    simp [h0, hc]

/-- Coefficient mass, given by `∑ j ∈ c.support, ‖c j x‖`. -/
noncomputable def coefficientMass {α : Type*} (c : Coefficients α) (x : α) : ℝ :=
  ∑ j ∈ c.support, ‖c j x‖

theorem coefficientMass_nonneg {α : Type*} (c : Coefficients α) (x : α) :
    0 ≤ coefficientMass c x := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- A value estimate with constant one, independent of every frequency
and of the largest occupied harmonic. -/
theorem norm_evaluate_le_mass {α : Type*} (c : Coefficients α) (x : α) (φ : ℝ) :
    ‖evaluate c x φ‖ ≤ coefficientMass c x := by
  calc
    _ ≤ ∑ j ∈ c.support, ‖c j x * character j φ‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_character, mul_one, coefficientMass]

theorem norm_field_le_mass {α : Type*} (c : Coefficients α) (k : ℝ) (Φ : α → ℝ)
    (kp : ℤ) (p : α × ℝ) : ‖field c k Φ kp p‖ ≤ coefficientMass c p.1 :=
  norm_evaluate_le_mass c p.1 _

theorem norm_field_product_le {α : Type*} (c d : Coefficients α) (k : ℝ) (Φ : α → ℝ)
    (kp : ℤ) (p : α × ℝ) :
    ‖field (c * d) k Φ kp p‖ ≤ coefficientMass c p.1 * coefficientMass d p.1 := by
  rw [field_mul, norm_mul]
  exact mul_le_mul (norm_field_le_mass c k Φ kp p) (norm_field_le_mass d k Φ kp p)
    (norm_nonneg _) (coefficientMass_nonneg c p.1)

theorem convolution_apply {α : Type*} (c d : Coefficients α) (m : ℤ) (x : α) :
    (c * d) m x = ∑ j ∈ c.support, c j x * d (m - j) x := by
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum, Finset.sum_apply, ite_apply, Pi.mul_apply, Pi.zero_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simp_rw [show ∀ l : ℤ, j + l = m ↔ l = m - j by intro l; omega]
  rw [Finset.sum_ite_eq']
  by_cases hm : m - j ∈ d.support
  · simp [hm]
  · have hd : d (m - j) = 0 := Finsupp.notMem_support_iff.mp hm
    simp [hm, hd]

theorem angularMean_product {α : Type*} (c d : Coefficients α) (k : ℝ) (Φ : α → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (x : α) :
    angularMean (fun θ => field c k Φ kp (x, θ) * field d k Φ kp (x, θ)) =
      ∑ j ∈ c.support, c j x * d (-j) x := by
  have heq : (fun θ => field c k Φ kp (x, θ) * field d k Φ kp (x, θ)) =
      (fun θ => field (c * d) k Φ kp (x, θ)) := by
    funext θ
    exact (field_mul c d k Φ kp (x, θ)).symm
  rw [heq, angularMean_field (c * d) k Φ hkp x, convolution_apply]
  simp only [zero_sub]

/-- Conjugate reverse, constructed using `AddMonoidAlgebra.ofCoeff`. -/
noncomputable def conjugateReverse {α : Type*} (c : Coefficients α) : Coefficients α :=
  AddMonoidAlgebra.ofCoeff <| Finsupp.equivMapDomain (Equiv.neg ℤ)
    (Finsupp.mapRange (fun a : α → ℂ => fun x => conj (a x)) (by ext x; simp) c.coeff)

@[simp] theorem conjugateReverse_apply {α : Type*} (c : Coefficients α) (j : ℤ) (x : α) :
    conjugateReverse c j x = conj (c (-j) x) := rfl

theorem evaluate_conjugateReverse {α : Type*} (c : Coefficients α) (x : α) (φ : ℝ) :
    evaluate (conjugateReverse c) x φ = conj (evaluate c x φ) := by
  unfold evaluate conjugateReverse Coefficients.sum
  simp only []
  rw [Finsupp.sum_equivMapDomain, Finsupp.sum_mapRange_index (fun _ => by simp)]
  simp only [Equiv.neg_apply, Finsupp.sum, map_sum, map_mul, character_neg]

/-- Conjugate symmetric, given by `∀ j x, c (-j) x = conj (c j x)`. -/
def ConjugateSymmetric {α : Type*} (c : Coefficients α) : Prop :=
  ∀ j x, c (-j) x = conj (c j x)

theorem conjugateReverse_eq_self {α : Type*} {c : Coefficients α}
    (hc : ConjugateSymmetric c) : conjugateReverse c = c := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro j
  funext x
  rw [conjugateReverse_apply, hc j x]
  simp

theorem evaluate_conj_eq_self {α : Type*} {c : Coefficients α}
    (hc : ConjugateSymmetric c) (x : α) (φ : ℝ) : conj (evaluate c x φ) = evaluate c x φ := by
  rw [← evaluate_conjugateReverse, conjugateReverse_eq_self hc]

theorem field_real {α : Type*} {c : Coefficients α} (hc : ConjugateSymmetric c)
    (k : ℝ) (Φ : α → ℝ) (kp : ℤ) (p : α × ℝ) :
    ((field c k Φ kp p).re : ℂ) = field c k Φ kp p :=
  Complex.conj_eq_iff_re.mp (evaluate_conj_eq_self hc p.1 _)

/-- The zero mode of the actual product is the complex coefficient
covariance, with conjugacy supplying the negative harmonics. -/
theorem angularMean_coefficient_covariance {α : Type*} (c : Coefficients α)
    {d : Coefficients α} (hd : ConjugateSymmetric d) (k : ℝ) (Φ : α → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (x : α) :
    angularMean (fun θ => field c k Φ kp (x, θ) * field d k Φ kp (x, θ)) =
      ∑ j ∈ c.support, c j x * conj (d j x) := by
  rw [angularMean_product c d k Φ hkp x]
  exact Finset.sum_congr rfl (fun j _ => congrArg (c j x * ·) (hd j x))

theorem chart_trace (c : Coefficients ProblemStatement.SpaceTime) (Ψ : ProblemStatement.SpaceTime →
    ℝ)
    (kp : ℤ) (hc : ∀ j ∈ c.support, MeanResidual.AngularInvariant (c j))
    (hΨ : ∀ q θ, Ψ (MeanResidual.angularShift q θ) = Ψ q + (kp : ℝ) * θ)
    (q : ProblemStatement.SpaceTime) (θ : ℝ) :
    evaluate c (MeanResidual.angularShift q θ) (Ψ (MeanResidual.angularShift q θ)) =
      field c 1 Ψ kp (q, θ) := by
  rw [hΨ]
  unfold evaluate field
  simp only [one_mul]
  exact Finset.sum_congr rfl (fun j hj => congrArg (· * character j (Ψ q + (kp : ℝ) * θ))
    (hc j hj q θ))

/-- The coefficient covariance is the actual angular average used by
`MeanResidual`, when coefficients are angularly invariant and the phase
has the stated integer angular increment. -/
theorem meanResidual_product_covariance
    (c d : Coefficients ProblemStatement.SpaceTime) (Ψ : ProblemStatement.SpaceTime → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0)
    (hc : ∀ j ∈ c.support, MeanResidual.AngularInvariant (c j))
    (hd : ∀ j ∈ d.support, MeanResidual.AngularInvariant (d j))
    (hΨ : ∀ q θ, Ψ (MeanResidual.angularShift q θ) = Ψ q + (kp : ℝ) * θ)
    (hconj : ConjugateSymmetric d) (q : ProblemStatement.SpaceTime) :
    MeanResidual.average (fun y => evaluate c y (Ψ y) * evaluate d y (Ψ y)) q =
      ∑ j ∈ c.support, c j q * conj (d j q) := by
  have he : MeanResidual.average (fun y => evaluate c y (Ψ y) * evaluate d y (Ψ y)) q =
      angularMean (fun θ => field c 1 Ψ kp (q, θ) * field d 1 Ψ kp (q, θ)) := by
    simp only [MeanResidual.average, angularMean, MeanResidual.period, period,
      Complex.real_smul, Complex.ofReal_inv]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    dsimp only
    rw [chart_trace c Ψ kp hc hΨ, chart_trace d Ψ kp hd hΨ]
  rw [he, angularMean_coefficient_covariance c hconj 1 Ψ hkp q]

/-- Band limited, given by `∀ j ∈ c.support, j.natAbs ≤ N`. -/
def BandLimited {α : Type*} (c : Coefficients α) (N : ℕ) : Prop :=
  ∀ j ∈ c.support, j.natAbs ≤ N

theorem BandLimited.mono {α : Type*} {c : Coefficients α} {M N : ℕ}
    (hc : BandLimited c M) (hMN : M ≤ N) : BandLimited c N :=
  fun j hj => (hc j hj).trans hMN

theorem BandLimited.add {α : Type*} {c d : Coefficients α} {N : ℕ}
    (hc : BandLimited c N) (hd : BandLimited d N) : BandLimited (c + d) N := by
  intro j hj
  rcases Finset.mem_union.mp (Finsupp.support_add hj) with hj | hj
  · exact hc j hj
  · exact hd j hj

theorem BandLimited.mul {α : Type*} {c d : Coefficients α} {M N : ℕ}
    (hc : BandLimited c M) (hd : BandLimited d N) : BandLimited (c * d) (M + N) := by
  have hs : (c * d).support ⊆ c.support + d.support :=
    AddMonoidAlgebra.support_coeff_mul_subset c d
  intro j hj
  obtain ⟨i, hi, l, hl, rfl⟩ := Finset.mem_add.mp (hs hj)
  exact (Int.natAbs_add_le i l).trans (Nat.add_le_add (hc i hi) (hd l hl))

theorem band_single_zero {α : Type*} (a : α → ℂ) :
    BandLimited (AddMonoidAlgebra.single (0 : ℤ) a : Coefficients α) 0 := by
  intro j hj
  have hj0 : j = 0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hj)
  simp [hj0]

/-- Constant coefficient, given by `AddMonoidAlgebra.single 0 a`. -/
noncomputable def constantCoefficient {α : Type*} (a : α → ℂ) : Coefficients α :=
  AddMonoidAlgebra.single 0 a

theorem band_constantCoefficient {α : Type*} (a : α → ℂ) :
    BandLimited (constantCoefficient a) 0 := band_single_zero a

/-- A literal quadratic update with arbitrary slow coefficient functions. -/
noncomputable def quadraticStep {α : Type*} (A B C : α → ℂ) (c : Coefficients α) :
    Coefficients α :=
  constantCoefficient A + constantCoefficient B * c + constantCoefficient C * (c * c)

theorem band_quadraticStep {α : Type*} (A B C : α → ℂ) {c : Coefficients α} {N : ℕ}
    (hc : BandLimited c N) : BandLimited (quadraticStep A B C c) (N + N) := by
  have hB : BandLimited (constantCoefficient B * c) N := by
    simpa only [zero_add] using (band_constantCoefficient B).mul hc
  have hC : BandLimited (constantCoefficient C * (c * c)) (N + N) := by
    simpa only [zero_add] using (band_constantCoefficient C).mul (hc.mul hc)
  exact ((band_constantCoefficient A).mono (Nat.zero_le _) |>.add
    (hB.mono (Nat.le_add_right _ _))).add hC

/-- Quadratic iterate as an element of `ℕ → Coefficients α | 0 => c | n + 1 => quadraticStep (A
n) (B n) (C n) (quadraticIterate A B C c n)`. -/
noncomputable def quadraticIterate {α : Type*} (A B C : ℕ → α → ℂ) (c : Coefficients α) :
    ℕ → Coefficients α
  | 0 => c
  | n + 1 => quadraticStep (A n) (B n) (C n) (quadraticIterate A B C c n)

/-- Starting in harmonics `{-1,0,1}`, the actual convolution update has
largest harmonic value at most `2^stage`. This is a bound on values,
not merely on the number of supported frequencies. -/
theorem band_quadraticIterate {α : Type*} (A B C : ℕ → α → ℂ) {c : Coefficients α}
    (hc : BandLimited c 1) (n : ℕ) : BandLimited (quadraticIterate A B C c n) (2 ^ n) := by
  induction n with
  | zero => simpa only [quadraticIterate, pow_zero] using hc
  | succ n ih =>
    simpa only [quadraticIterate, pow_succ, mul_two] using
      band_quadraticStep (A n) (B n) (C n) ih

theorem quadratic_angular_frequency_bound {α : Type*} (A B C : ℕ → α → ℂ)
    {c : Coefficients α} (hc : BandLimited c 1) (n : ℕ) (kp : ℤ)
    {j : ℤ} (hj : j ∈ (quadraticIterate A B C c n).support) :
    (j * kp).natAbs ≤ 2 ^ n * kp.natAbs := by
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul_right _ (band_quadraticIterate A B C hc n j hj)

theorem field_quadraticStep {α : Type*} (A B C : α → ℂ) (c : Coefficients α)
    (k : ℝ) (Φ : α → ℝ) (kp : ℤ) (p : α × ℝ) :
    field (quadraticStep A B C c) k Φ kp p =
      A p.1 + B p.1 * field c k Φ kp p + C p.1 * field c k Φ kp p ^ 2 := by
  simp only [quadraticStep, field, evaluate_add, evaluate_mul, constantCoefficient, evaluate_single,
    character_zero, mul_one, pow_two]

/-- Quadratic envelope as an element of `ℕ → ℝ | 0 => coefficientMass c x | n + 1 => ‖A n x‖ +
‖B n x‖ * quadraticEnvelope A B C c x n + ‖C n x‖ * quadraticEnvelope A B C c x n ^ 2`. -/
noncomputable def quadraticEnvelope {α : Type*} (A B C : ℕ → α → ℂ)
    (c : Coefficients α) (x : α) : ℕ → ℝ
  | 0 => coefficientMass c x
  | n + 1 => ‖A n x‖ + ‖B n x‖ * quadraticEnvelope A B C c x n +
      ‖C n x‖ * quadraticEnvelope A B C c x n ^ 2

/-- The value envelope follows the actual quadratic update and contains
no factor involving the harmonic band or its cardinality. -/
theorem norm_quadraticIterate_le {α : Type*} (A B C : ℕ → α → ℂ) (c : Coefficients α)
    (k : ℝ) (Φ : α → ℝ) (kp : ℤ) (p : α × ℝ) (n : ℕ) :
    ‖field (quadraticIterate A B C c n) k Φ kp p‖ ≤ quadraticEnvelope A B C c p.1 n := by
  induction n with
  | zero => exact norm_field_le_mass c k Φ kp p
  | succ n ih =>
    rw [quadraticIterate, field_quadraticStep, quadraticEnvelope]
    calc
      _ ≤ ‖A n p.1‖ + ‖B n p.1‖ * ‖field (quadraticIterate A B C c n) k Φ kp p‖ +
          ‖C n p.1‖ * ‖field (quadraticIterate A B C c n) k Φ kp p‖ ^ 2 := by
        exact (norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (by rw [norm_mul])) (by rw [norm_mul, norm_pow]))
      _ ≤ _ := add_le_add
        (add_le_add_right (mul_le_mul_of_nonneg_left ih (norm_nonneg _)) _)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ih 2) (norm_nonneg _))

section Derivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Wave, given by `c.sum (fun j a => HarmonicCalculus.mode (k * (j : ℝ)) Φ a x)`. -/
noncomputable def wave (c : Coefficients E) (k : ℝ) (Φ : E → ℝ) (x : E) : ℂ :=
  c.sum (fun j a => HarmonicCalculus.mode (k * (j : ℝ)) Φ a x)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem character_eq_carrier (j : ℤ) (k : ℝ) (Φ : E → ℝ) (x : E) :
    character j (k * Φ x) = HarmonicCalculus.carrier (k * (j : ℝ)) Φ x := by
  apply congrArg Complex.exp
  simp only [HarmonicCalculus.phaseFactor, Complex.ofReal_mul, Complex.ofReal_intCast]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem wave_eq_evaluate (c : Coefficients E) (k : ℝ) (Φ : E → ℝ) (x : E) :
    wave c k Φ x = evaluate c x (k * Φ x) := by
  apply Finset.sum_congr rfl
  intro j hj
  change c j x * Complex.exp (HarmonicCalculus.phaseFactor (k * (j : ℝ)) * (Φ x : ℂ)) =
    c j x * Complex.exp ((j : ℂ) * ((k * Φ x : ℝ) : ℂ) * Complex.I)
  apply congrArg (c j x * ·)
  apply congrArg Complex.exp
  simp only [HarmonicCalculus.phaseFactor, Complex.ofReal_mul, Complex.ofReal_intCast]
  ring

/-- Derivative coefficient, given by `HarmonicCalculus.along V a x +
HarmonicCalculus.phaseFactor (k * (j : ℝ)) * Complex.ofReal (HarmonicCalculus.along V Φ x) *
a x`. -/
noncomputable def derivativeCoefficient (V : E → E) (k : ℝ) (Φ : E → ℝ)
    (j : ℤ) (a : E → ℂ) (x : E) : ℂ :=
  HarmonicCalculus.along V a x + HarmonicCalculus.phaseFactor (k * (j : ℝ)) *
    Complex.ofReal (HarmonicCalculus.along V Φ x) * a x

theorem derivativeCoefficient_zero (V : E → E) (k : ℝ) (Φ : E → ℝ) (j : ℤ) :
    derivativeCoefficient V k Φ j (0 : E → ℂ) = 0 := by
  funext x
  simp [derivativeCoefficient, HarmonicCalculus.along]

/-- Differentiate, constructed using `AddMonoidAlgebra.ofCoeff`. -/
noncomputable def differentiate (V : E → E) (k : ℝ) (Φ : E → ℝ)
    (c : Coefficients E) : Coefficients E :=
  AddMonoidAlgebra.ofCoeff <| Finsupp.onFinset c.support (fun j => derivativeCoefficient V k Φ j (c
      j)) (by
    intro j hj
    by_contra hnot
    apply hj
    change derivativeCoefficient V k Φ j (c j) = 0
    rw [Finsupp.notMem_support_iff.mp hnot, derivativeCoefficient_zero])

@[simp] theorem differentiate_apply (V : E → E) (k : ℝ) (Φ : E → ℝ)
    (c : Coefficients E) (j : ℤ) :
    differentiate V k Φ c j = derivativeCoefficient V k Φ j (c j) := rfl

theorem support_differentiate (V : E → E) (k : ℝ) (Φ : E → ℝ) (c : Coefficients E) :
    (differentiate V k Φ c).support ⊆ c.support := by
  unfold Coefficients.support differentiate
  simp only []
  exact Finsupp.support_onFinset_subset

theorem BandLimited.differentiate (V : E → E) (k : ℝ) (Φ : E → ℝ)
    {c : Coefficients E} {N : ℕ} (hc : BandLimited c N) :
    BandLimited (differentiate V k Φ c) N :=
  fun j hj => hc j (support_differentiate V k Φ c hj)

theorem wave_differentiate_expansion (V : E → E) (k : ℝ) (Φ : E → ℝ)
    (c : Coefficients E) (x : E) :
    wave (differentiate V k Φ c) k Φ x =
      ∑ j ∈ c.support, derivativeCoefficient V k Φ j (c j) x *
        HarmonicCalculus.carrier (k * (j : ℝ)) Φ x := by
  unfold wave Coefficients.sum Finsupp.sum
  have hs := Finset.sum_subset (support_differentiate V k Φ c) (f := fun j : ℤ =>
    HarmonicCalculus.mode (k * (j : ℝ)) Φ (differentiate V k Φ c j) x) (by
      intro j hj hnot
      change HarmonicCalculus.mode (k * (j : ℝ)) Φ (differentiate V k Φ c j) x = 0
      rw [Finsupp.notMem_support_iff.mp hnot]
      simp [HarmonicCalculus.mode])
  exact hs

/-- Differentiating the actual finite wave applies the full product rule
to each coefficient and phase, and introduces no new harmonic values. -/
theorem along_wave (V : E → E) (k : ℝ) (Φ : E → ℝ) (c : Coefficients E) {x : E}
    (hΦ : DifferentiableAt ℝ Φ x) (hc : ∀ j ∈ c.support, DifferentiableAt ℝ (c j) x) :
    HarmonicCalculus.along V (wave c k Φ) x = wave (differentiate V k Φ c) k Φ x := by
  rw [wave_differentiate_expansion]
  change fderiv ℝ (fun y => ∑ j ∈ c.support,
    HarmonicCalculus.mode (k * (j : ℝ)) Φ (c j) y) x (V x) = _
  dsimp only [HarmonicCalculus.mode]
  rw [fderiv_fun_sum (fun j hj => (hc j hj).fun_mul
    (HarmonicCalculus.differentiableAt_carrier (k * (j : ℝ)) hΦ))]
  simp only [_root_.sum_apply]
  exact Finset.sum_congr rfl (fun j hj => HarmonicCalculus.along_mode V
    (k * (j : ℝ)) hΦ (hc j hj))

theorem along_field_slow (V : E → E) (k : ℝ) (Φ : E → ℝ) (kp : ℤ)
    (c : Coefficients E) (θ : ℝ) {x : E}
    (hΦ : DifferentiableAt ℝ Φ x) (hc : ∀ j ∈ c.support, DifferentiableAt ℝ (c j) x) :
    HarmonicCalculus.along V (fun y => field c k Φ kp (y, θ)) x =
      field (differentiate V k Φ c) k Φ kp (x, θ) := by
  have heq : (fun y => field c k Φ kp (y, θ)) = fun y => ∑ j ∈ c.support,
      (c j y * HarmonicCalculus.carrier (k * (j : ℝ)) Φ y) * character (j * kp) θ := by
    funext y
    simp only [field_expansion, character_eq_carrier]
  rw [heq]
  change fderiv ℝ (fun y => ∑ j ∈ c.support,
    (c j y * HarmonicCalculus.carrier (k * (j : ℝ)) Φ y) * character (j * kp) θ) x (V x) = _
  rw [fderiv_fun_sum (fun j hj => ((hc j hj).fun_mul
    (HarmonicCalculus.differentiableAt_carrier (k * (j : ℝ)) hΦ)).mul_const _)]
  simp only [_root_.sum_apply]
  rw [field, evaluate_over _ c.support (support_differentiate V k Φ c)]
  simp only [differentiate_apply, character_phase_add, character_int_mul, character_eq_carrier]
  apply Finset.sum_congr rfl
  intro j hj
  have hm : DifferentiableAt ℝ (HarmonicCalculus.mode (k * (j : ℝ)) Φ (c j)) x :=
    (hc j hj).fun_mul (HarmonicCalculus.differentiableAt_carrier (k * (j : ℝ)) hΦ)
  change HarmonicCalculus.along V
    (fun y => HarmonicCalculus.mode (k * (j : ℝ)) Φ (c j) y * character (j * kp) θ) x = _
  rw [HarmonicCalculus.along_mul V hm (differentiableAt_const _),
    HarmonicCalculus.along_mode V (k * (j : ℝ)) hΦ (hc j hj)]
  simp only [HarmonicCalculus.along, fderiv_fun_const, Pi.zero_apply, _root_.zero_apply,
    mul_zero, add_zero, derivativeCoefficient]
  ring

theorem derivativeCoefficient_contDiffOn {U : Set E} (hU : IsOpen U)
    {V : E → E} {Φ : E → ℝ} {a : E → ℂ}
    (hV : ContDiffOn ℝ ∞ V U) (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (k : ℝ) (j : ℤ) : ContDiffOn ℝ ∞ (derivativeCoefficient V k Φ j a) U :=
  (HarmonicCalculus.contDiffOn_along hU hV ha).add
    ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (HarmonicCalculus.contDiffOn_along hU hV hΦ))).mul ha)

theorem differentiate_contDiffOn {U : Set E} (hU : IsOpen U)
    {V : E → E} {Φ : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (k : ℝ) {c : Coefficients E} (hc : ∀ j ∈ c.support, ContDiffOn ℝ ∞ (c j) U) :
    ∀ j ∈ (differentiate V k Φ c).support, ContDiffOn ℝ ∞ (differentiate V k Φ c j) U := by
  intro j hj
  exact derivativeCoefficient_contDiffOn hU hV hΦ (hc j (support_differentiate V k Φ c hj)) k j

/-- Iterated coefficients as an element of `ℕ → Coefficients E | 0 => c | n + 1 => differentiate
V k Φ (iteratedCoefficients V k Φ c n)`. -/
noncomputable def iteratedCoefficients (V : E → E) (k : ℝ) (Φ : E → ℝ) (c : Coefficients E) :
    ℕ → Coefficients E
  | 0 => c
  | n + 1 => differentiate V k Φ (iteratedCoefficients V k Φ c n)

/-- Iterated along as an element of `ℕ → (E → ℂ) → E → ℂ | 0, f => f | n + 1, f =>
HarmonicCalculus.along V (iteratedAlong V n f)`. -/
noncomputable def iteratedAlong (V : E → E) : ℕ → (E → ℂ) → E → ℂ
  | 0, f => f
  | n + 1, f => HarmonicCalculus.along V (iteratedAlong V n f)

theorem band_iteratedCoefficients (V : E → E) (k : ℝ) (Φ : E → ℝ)
    {c : Coefficients E} {N : ℕ} (hc : BandLimited c N) (n : ℕ) :
    BandLimited (iteratedCoefficients V k Φ c n) N := by
  induction n with
  | zero => exact hc
  | succ n ih => exact ih.differentiate V k Φ

theorem iteratedCoefficients_contDiffOn {U : Set E} (hU : IsOpen U)
    {V : E → E} {Φ : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (k : ℝ) {c : Coefficients E} (hc : ∀ j ∈ c.support, ContDiffOn ℝ ∞ (c j) U) (n : ℕ) :
    ∀ j ∈ (iteratedCoefficients V k Φ c n).support,
      ContDiffOn ℝ ∞ (iteratedCoefficients V k Φ c n j) U := by
  induction n with
  | zero => exact hc
  | succ n ih => exact differentiate_contDiffOn hU hV hΦ k ih

/-- All repeated actual directional derivatives retain the original
finite set of harmonic values. Direction-field derivatives are included. -/
theorem iteratedAlong_wave {U : Set E} (hU : IsOpen U)
    {V : E → E} {Φ : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (k : ℝ) {c : Coefficients E} (hc : ∀ j ∈ c.support, ContDiffOn ℝ ∞ (c j) U) (n : ℕ) :
    EqOn (iteratedAlong V n (wave c k Φ)) (wave (iteratedCoefficients V k Φ c n) k Φ) U := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro x hx
    change HarmonicCalculus.along V (iteratedAlong V n (wave c k Φ)) x = _
    rw [HarmonicCalculus.along_congr hU ih hx]
    exact along_wave V k Φ _ ((hΦ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
      (fun j hj => ((iteratedCoefficients_contDiffOn hU hV hΦ k hc n j hj).contDiffAt
        (hU.mem_nhds hx)).differentiableAt (by simp))

end Derivatives

theorem character_hasDerivAt (j : ℤ) (θ : ℝ) :
    HasDerivAt (character j) (((j : ℂ) * Complex.I) * character j θ) θ := by
  let c : ℂ := (j : ℂ) * Complex.I
  have hc : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c θ := by
    simpa only [mul_one, id_eq] using (((hasDerivAt_id (θ : ℂ)).const_mul c).comp_ofReal)
  have he : ∀ x : ℝ, Complex.exp (c * (x : ℂ)) = character j x := by
    intro x
    apply congrArg Complex.exp
    dsimp [c]
    ring
  have hd := hc.cexp
  simp only [he] at hd
  convert! hd using 1
  dsimp [c]
  ring

/-- Angular differentiate, constructed using `AddMonoidAlgebra.ofCoeff`. -/
noncomputable def angularDifferentiate {α : Type*} (kp : ℤ) (c : Coefficients α) :
    Coefficients α :=
  AddMonoidAlgebra.ofCoeff <| Finsupp.onFinset c.support (fun j x => (((j * kp : ℤ) : ℂ) *
      Complex.I) * c j x) (by
    intro j hj
    by_contra hn
    apply hj
    have hc : c j = 0 := Finsupp.notMem_support_iff.mp hn
    funext x
    simp [hc])

@[simp] theorem angularDifferentiate_apply {α : Type*} (kp : ℤ) (c : Coefficients α)
    (j : ℤ) (x : α) :
    angularDifferentiate kp c j x = (((j * kp : ℤ) : ℂ) * Complex.I) * c j x := rfl

theorem support_angularDifferentiate {α : Type*} (kp : ℤ) (c : Coefficients α) :
    (angularDifferentiate kp c).support ⊆ c.support := by
  unfold Coefficients.support angularDifferentiate
  simp only []
  exact Finsupp.support_onFinset_subset

theorem BandLimited.angularDifferentiate {α : Type*} (kp : ℤ) {c : Coefficients α}
    {N : ℕ} (hc : BandLimited c N) : BandLimited (angularDifferentiate kp c) N :=
  fun j hj => hc j (support_angularDifferentiate kp c hj)

/-- The literal angular derivative acts diagonally on the same harmonic
values, with multiplier `i*j*kp`. -/
theorem field_hasDerivAt_angle {α : Type*} (c : Coefficients α) (k : ℝ)
    (Φ : α → ℝ) (kp : ℤ) (x : α) (θ : ℝ) :
    HasDerivAt (fun a => field c k Φ kp (x, a))
      (field (angularDifferentiate kp c) k Φ kp (x, θ)) θ := by
  have hd := HasDerivAt.fun_sum (u := c.support) (fun j _ =>
    (character_hasDerivAt (j * kp) θ).const_mul (c j x * character j (k * Φ x)))
  convert! hd using 1
  · funext a
    exact field_expansion c k Φ kp x a
  · rw [field, evaluate_over _ c.support (support_angularDifferentiate kp c)]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [angularDifferentiate_apply, character_phase_add, character_int_mul]
    ring

end NavierStokes.HarmonicFields
