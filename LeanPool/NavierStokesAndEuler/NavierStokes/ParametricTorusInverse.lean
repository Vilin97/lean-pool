/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothFourierData
public import LeanPool.NavierStokesAndEuler.NavierStokes.TransportPrimitive
public import Mathlib.Analysis.Calculus.SmoothSeries

@[expose] public section

/-!
# The actual smooth torus inverse with an external real parameter

The coefficients are the integrals of the given function. Local uniform
decay is obtained from genuine derivatives on compact parameter intervals.
-/

noncomputable section

namespace NavierStokes.ParametricTorusInverse

open Set Filter MeasureTheory
open TorusInverse
open scoped Topology ContDiff BigOperators

abbrev Point := ℝ × Plane
abbrev Source := Point → ℂ

noncomputable def slice (f : Source) (p : ℝ) : Plane → ℂ := fun Y => f (p, Y)

def Periodic (f : Source) : Prop := ∀ p, SmoothFourierData.UnitPeriodic (slice f p)

noncomputable def parameterPartial (f : Source) (z : Point) : ℂ :=
  fderiv ℝ f z (1, 0)

noncomputable def torusXPartial (f : Source) (z : Point) : ℂ :=
  fderiv ℝ f z (0, (1, 0))

noncomputable def parameterJet (n : ℕ) (f : Source) : Source := parameterPartial^[n] f

noncomputable def torusXJet : ℕ → Source → Source
  | 0, f => f
  | n + 1, f => torusXPartial (torusXJet n f)

noncomputable def swapTorus (f : Source) : Source := fun z => f (z.1, (z.2.2, z.2.1))

noncomputable def coefficient (f : Source) (p : ℝ) (k : Frequency) : ℂ :=
  SmoothFourierData.coefficient (slice f p) k

noncomputable def mean (f : Source) (p : ℝ) : ℂ := coefficient f p 0

def ZeroMean (f : Source) : Prop := ∀ p, mean f p = 0

noncomputable def inverse (d : Direction) (f : Source) (z : Point) : ℂ :=
  directionalInverse d (coefficient f z.1) z.2

noncomputable def iterateInverse (d : Direction) (n : ℕ) (f : Source) : Source :=
  (inverse d)^[n] f

theorem mean_eq_integral (f : Source) (p : ℝ) :
    mean f p = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (p, (x, y)) :=
  SmoothFourierData.coefficient_zero_eq_integral _

theorem slice_smooth {f : Source} (hf : ContDiff ℝ ∞ f) (p : ℝ) :
    ContDiff ℝ ∞ (slice f p) :=
  hf.comp (contDiff_const.prodMk contDiff_id)

theorem fixedPartial_smooth {f : Source} (hf : ContDiff ℝ ∞ f) (v : Point) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ f z v) :=
  (ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp (hf.fderiv_right (by simp))

theorem parameterPartial_smooth {f : Source} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (parameterPartial f) := fixedPartial_smooth hf (1, 0)

theorem torusXPartial_smooth {f : Source} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (torusXPartial f) := fixedPartial_smooth hf (0, (1, 0))

theorem fixedPartial_periodic {f : Source} (hp : Periodic f) (v : Point) :
    Periodic (fun z => fderiv ℝ f z v) := by
  intro p Y k
  have he : (fun z : Point => f (z + (0, ((k.1 : ℝ), (k.2 : ℝ))))) = f := by
    funext z
    change f (z.1 + 0, z.2 + ((k.1 : ℝ), (k.2 : ℝ))) = f (z.1, z.2)
    simpa [slice] using hp z.1 z.2 k
  have hd := congrArg (fun g : Source => fderiv ℝ g (p, Y)) he
  rw [fderiv_comp_add_right] at hd
  simpa only [slice, Prod.mk_add_mk, add_zero] using
    congrArg (fun L : Point →L[ℝ] ℂ => L v) hd

theorem parameterPartial_periodic {f : Source} (hp : Periodic f) :
    Periodic (parameterPartial f) := fixedPartial_periodic hp (1, 0)

theorem torusXPartial_periodic {f : Source} (hp : Periodic f) :
    Periodic (torusXPartial f) := fixedPartial_periodic hp (0, (1, 0))

theorem torusXJet_smooth {f : Source} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (torusXJet n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact torusXPartial_smooth ih

theorem parameterJet_smooth {f : Source} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (parameterJet n f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
      rw [parameterJet, Function.iterate_succ_apply']
      exact parameterPartial_smooth ih

theorem parameterJet_periodic {f : Source} (hp : Periodic f) (n : ℕ) :
    Periodic (parameterJet n f) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
      rw [parameterJet, Function.iterate_succ_apply']
      exact parameterPartial_periodic ih

theorem swapTorus_smooth {f : Source} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (swapTorus f) :=
  hf.comp (contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst))

theorem parameter_slice_hasDerivAt {f : Source} (hf : ContDiff ℝ ∞ f)
    (p : ℝ) (Y : Plane) :
    HasDerivAt (fun q => f (q, Y)) (parameterPartial f (p, Y)) p := by
  exact ((hf.differentiable (by simp)) (p, Y)).hasFDerivAt.comp_hasDerivAt p
    ((hasDerivAt_id p).prodMk (hasDerivAt_const p Y))

theorem slice_hasFDerivAt {f : Source} (hf : ContDiff ℝ ∞ f) (p : ℝ) (Y : Plane) :
    HasFDerivAt (slice f p)
      ((fderiv ℝ f (p, Y)).comp (ContinuousLinearMap.inr ℝ ℝ Plane)) Y := by
  exact ((hf.differentiable (by simp)) (p, Y)).hasFDerivAt.comp Y
    ((hasFDerivAt_const p Y).prodMk (hasFDerivAt_id Y))

theorem slice_torusXPartial {f : Source} (hf : ContDiff ℝ ∞ f) (p : ℝ) :
    slice (torusXPartial f) p = SmoothFourierData.partialX (slice f p) := by
  funext Y
  symm
  exact congrArg (fun L : Plane →L[ℝ] ℂ => L (1, 0)) (slice_hasFDerivAt hf p Y).fderiv

theorem slice_torusXJet {f : Source} (hf : ContDiff ℝ ∞ f) (n : ℕ) (p : ℝ) :
    slice (torusXJet n f) p = SmoothFourierData.xJet n (slice f p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [torusXJet, slice_torusXPartial (torusXJet_smooth hf n),
        SmoothFourierData.xJet_succ, ih]

theorem kernel_eq_mode (k : Frequency) (Y : Plane) :
    SmoothFourierData.kernel k Y = mode (-k) Y := by
  rw [mode_eq_torusMode]
  rfl

theorem mode_smooth (k : Frequency) : ContDiff ℝ ∞ (mode k) :=
  Complex.contDiff_exp.comp (phase k).contDiff

theorem kernel_smooth (k : Frequency) : ContDiff ℝ ∞ (SmoothFourierData.kernel k) := by
  simpa only [funext (kernel_eq_mode k)] using mode_smooth (-k)

/-- Differentiation of an actual fixed-interval integral. -/
theorem integral_hasDerivAt {g g' : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hd : ∀ p u, HasDerivAt (fun q => g (q, u)) (g' (p, u)) p)
    (a b p : ℝ) :
    HasDerivAt (fun q => ∫ u in a..b, g (q, u)) (∫ u in a..b, g' (p, u)) p := by
  have hh := (TransportPrimitive.parameterIntegral_hasFDerivAt hg a b p).hasDerivAt
  have hi : IntervalIntegrable (fun u => TransportPrimitive.parameterDerivative g (p, u))
      volume a b :=
    ((TransportPrimitive.parameterDerivative_contDiff hg).continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  rw [ContinuousLinearMap.intervalIntegral_apply hi (1 : ℝ)] at hh
  convert! hh using 1
  apply intervalIntegral.integral_congr
  intro u hu
  exact ((TransportPrimitive.parameter_hasFDerivAt hg p u).hasDerivAt.unique (hd p u)).symm

noncomputable def weightedSource (k : Frequency) (f : Source) (q : (ℝ × ℝ) × ℝ) : ℂ :=
  SmoothFourierData.kernel k (q.2, q.1.2) * f (q.1.1, (q.2, q.1.2))

theorem weightedSource_smooth {f : Source} (hf : ContDiff ℝ ∞ f) (k : Frequency) :
    ContDiff ℝ ∞ (weightedSource k f) :=
  ((kernel_smooth k).comp (contDiff_snd.prodMk contDiff_fst.snd)).mul
    (hf.comp (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd)))

theorem coefficient_smooth {f : Source} (hf : ContDiff ℝ ∞ f) (k : Frequency) :
    ContDiff ℝ ∞ (fun p => coefficient f p k) := by
  have hi := TransportPrimitive.parameterIntegral_contDiff (weightedSource_smooth hf k)
    (0 : ℝ) 1
  have ho := TransportPrimitive.parameterIntegral_contDiff hi (0 : ℝ) 1
  simpa only [coefficient, SmoothFourierData.coefficient_eq_doubleIntegral, weightedSource,
    slice] using ho

theorem coefficient_hasDerivAt {f : Source} (hf : ContDiff ℝ ∞ f)
    (k : Frequency) (p : ℝ) :
    HasDerivAt (fun q => coefficient f q k) (coefficient (parameterPartial f) p k) p := by
  let inner : ℝ × ℝ → ℂ := fun q => ∫ x in (0 : ℝ)..1, weightedSource k f (q, x)
  let innerD : ℝ × ℝ → ℂ := fun q => ∫ x in (0 : ℝ)..1,
    weightedSource k (parameterPartial f) (q, x)
  have hi : ContDiff ℝ ∞ inner :=
    TransportPrimitive.parameterIntegral_contDiff (weightedSource_smooth hf k) 0 1
  have hd : ∀ q y, HasDerivAt (fun u => inner (u, y)) (innerD (q, y)) q := by
    intro q y
    have hy : ContDiff ℝ ∞ (fun z : ℝ × ℝ => weightedSource k f ((z.1, y), z.2)) :=
      ((weightedSource_smooth hf k).comp
        ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd))
    exact integral_hasDerivAt
      (g' := fun z : ℝ × ℝ => weightedSource k (parameterPartial f) ((z.1, y), z.2))
      hy (fun u x => by
        simpa only [weightedSource] using
          (parameter_slice_hasDerivAt hf u (x, y)).const_mul
            (SmoothFourierData.kernel k (x, y))) 0 1 q
  have ho := integral_hasDerivAt hi hd 0 1 p
  simpa only [coefficient, SmoothFourierData.coefficient_eq_doubleIntegral, slice,
    inner, innerD, weightedSource] using ho

theorem parameterPartial_zeroMean {f : Source} (hf : ContDiff ℝ ∞ f)
    (hm : ZeroMean f) : ZeroMean (parameterPartial f) := by
  intro p
  have he : (fun q => coefficient f q 0) = fun _ => (0 : ℂ) := funext hm
  have hd := (coefficient_hasDerivAt hf 0 p).deriv
  rw [he, deriv_const] at hd
  exact hd.symm

/-- Uniform polynomial decay on any fixed compact parameter interval,
derived from bounds for actual torus derivatives. -/
theorem exists_uniform_coefficient_bound {f : Source} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) (n : ℕ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Icc a b, ∀ k,
      weight k ^ n * ‖coefficient f p k‖ ≤ C := by
  let K : Set Point := Icc a b ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C₀, h₀⟩ := hK.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨C₁, h₁⟩ := hK.exists_bound_of_continuousOn
    (torusXJet_smooth hf n).continuous.continuousOn
  obtain ⟨C₂, h₂⟩ := hK.exists_bound_of_continuousOn
    (torusXJet_smooth (swapTorus_smooth hf) n).continuous.continuousOn
  let C := max 0 (max C₀ (max C₁ C₂))
  have hC : 0 ≤ C := le_max_left _ _
  have hC₀ : C₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC₁ : C₁ ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hC₂ : C₂ ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨3 ^ n * C, mul_nonneg (by positivity) hC, ?_⟩
  intro p hparam k
  apply SmoothFourierData.coefficient_polynomial_bound (slice_smooth hf p) (hp p) n
  · intro x hx y hy
    exact (h₀ (p, (x, y)) ⟨hparam, hx, hy⟩).trans hC₀
  · intro x hx y hy
    rw [← slice_torusXJet hf n p]
    exact (h₁ (p, (x, y)) ⟨hparam, hx, hy⟩).trans hC₁
  · intro x hx y hy
    change ‖SmoothFourierData.xJet n (slice (swapTorus f) p) (x, y)‖ ≤ C
    rw [← slice_torusXJet (swapTorus_smooth hf) n p]
    exact (h₂ (p, (x, y)) ⟨hparam, hx, hy⟩).trans hC₂

def PolynomialGrowth (m : Frequency → ℂ) : Prop :=
  ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ‖m k‖ ≤ C * weight k ^ s

noncomputable def multiplierX (m : Frequency → ℂ) (k : Frequency) : ℂ := freqX k * m k
noncomputable def multiplierY (m : Frequency → ℂ) (k : Frequency) : ℂ := freqY k * m k

theorem PolynomialGrowth.mulX {m : Frequency → ℂ} (hm : PolynomialGrowth m) :
    PolynomialGrowth (multiplierX m) := by
  obtain ⟨s, C, hC, hm⟩ := hm
  refine ⟨s + 1, ‖omega‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  intro k
  have hw := (weight_pos k).le
  calc
    ‖multiplierX m k‖ = ‖freqX k‖ * ‖m k‖ := norm_mul _ _
    _ ≤ (‖omega‖ * weight k) * (C * weight k ^ s) :=
      mul_le_mul (norm_freqX_le k) (hm k) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem PolynomialGrowth.mulY {m : Frequency → ℂ} (hm : PolynomialGrowth m) :
    PolynomialGrowth (multiplierY m) := by
  obtain ⟨s, C, hC, hm⟩ := hm
  refine ⟨s + 1, ‖omega‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  intro k
  have hw := (weight_pos k).le
  calc
    ‖multiplierY m k‖ = ‖freqY k‖ * ‖m k‖ := norm_mul _ _
    _ ≤ (‖omega‖ * weight k) * (C * weight k ^ s) :=
      mul_le_mul (norm_freqY_le k) (hm k) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem inverseMultiplier_growth (d : Direction) : PolynomialGrowth (multiplier d) :=
  ⟨1, 6 * ‖omega⁻¹‖, by positivity, fun k => by simpa using norm_multiplier_le d k⟩

theorem PolynomialGrowth.rapid_mul {m a : Frequency → ℂ} (hm : PolynomialGrowth m)
    (ha : Rapid a) : Rapid (fun k => m k * a k) := by
  obtain ⟨s, C, hC, hm⟩ := hm
  intro n
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (weight_pos k).le n) (norm_nonneg _))
    _ ((ha (n + s)).mul_left C)
  intro k
  have hw := (weight_pos k).le
  calc
    weight k ^ n * ‖m k * a k‖ = weight k ^ n * (‖m k‖ * ‖a k‖) := by rw [norm_mul]
    _ ≤ weight k ^ n * ((C * weight k ^ s) * ‖a k‖) := by
      gcongr
      exact hm k
    _ = _ := by rw [pow_add]; ring

theorem multiplied_coeff_bound {m a : Frequency → ℂ} {s : ℕ} {C B : ℝ}
    (hC : 0 ≤ C) (hm : ∀ k, ‖m k‖ ≤ C * weight k ^ s)
    (ha : ∀ k, weight k ^ (s + 4) * ‖a k‖ ≤ B) (k : Frequency) :
    ‖m k * a k‖ ≤ (C * B) * (weight k ^ 4)⁻¹ := by
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (weight_pos k) 4)).mpr
  calc
    ‖m k * a k‖ * weight k ^ 4 ≤
        ((C * weight k ^ s) * ‖a k‖) * weight k ^ 4 := by
      rw [norm_mul]
      gcongr
      exact hm k
    _ = C * (weight k ^ (s + 4) * ‖a k‖) := by rw [pow_add]; ring
    _ ≤ C * B := mul_le_mul_of_nonneg_left (ha k) hC

theorem uniform_multiplied_coeff_bound {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Icc a b, ∀ k,
      ‖m k * coefficient f p k‖ ≤ C * (weight k ^ 4)⁻¹ := by
  obtain ⟨s, M, hM, hm⟩ := hm
  obtain ⟨B, hB, hbound⟩ := exists_uniform_coefficient_bound hf hp (s + 4) a b
  exact ⟨M * B, mul_nonneg hM hB, fun p hp k => multiplied_coeff_bound hM hm (hbound p hp) k⟩

noncomputable def applyMultiplier (m : Frequency → ℂ) (f : Source) (z : Point) : ℂ :=
  series (fun k => m k * coefficient f z.1 k) z.2

theorem inverse_eq_applyMultiplier (d : Direction) (f : Source) :
    inverse d f = applyMultiplier (multiplier d) f := rfl

theorem multiplied_coeff_rapid {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (p : ℝ) :
    Rapid (fun k => m k * coefficient f p k) :=
  hm.rapid_mul (SmoothFourierData.rapid_coefficient (slice_smooth hf p) (hp p))

noncomputable def jointDP : Point →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ Plane
noncomputable def jointDX : Point →L[ℝ] ℝ :=
  TorusInverse.dx.comp (ContinuousLinearMap.snd ℝ ℝ Plane)
noncomputable def jointDY : Point →L[ℝ] ℝ :=
  TorusInverse.dy.comp (ContinuousLinearMap.snd ℝ ℝ Plane)

noncomputable def jointLiftP : ℂ →L[ℝ] (Point →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ Point ℂ jointDP
noncomputable def jointLiftX : ℂ →L[ℝ] (Point →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ Point ℂ jointDX
noncomputable def jointLiftY : ℂ →L[ℝ] (Point →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ Point ℂ jointDY

@[simp] theorem jointLiftP_apply (c : ℂ) (v : Point) : jointLiftP c v = v.1 • c := rfl
@[simp] theorem jointLiftX_apply (c : ℂ) (v : Point) : jointLiftX c v = v.2.1 • c := rfl
@[simp] theorem jointLiftY_apply (c : ℂ) (v : Point) : jointLiftY c v = v.2.2 • c := rfl

noncomputable def multiplierTermDerivative (m : Frequency → ℂ) (f : Source)
    (k : Frequency) (z : Point) : Point →L[ℝ] ℂ :=
  jointLiftP (m k * coefficient (parameterPartial f) z.1 k * mode k z.2) +
  jointLiftX (multiplierX m k * coefficient f z.1 k * mode k z.2) +
  jointLiftY (multiplierY m k * coefficient f z.1 k * mode k z.2)

theorem hasFDerivAt_multiplierTerm {f : Source} (hf : ContDiff ℝ ∞ f)
    (m : Frequency → ℂ) (k : Frequency) (z : Point) :
    HasFDerivAt (fun w : Point => m k * coefficient f w.1 k * mode k w.2)
      (multiplierTermDerivative m f k z) z := by
  have hc : HasFDerivAt (fun w : Point => coefficient f w.1 k)
      (jointLiftP (coefficient (parameterPartial f) z.1 k)) z := by
    convert! (coefficient_hasDerivAt hf k z.1).hasFDerivAt.comp z
      (hasFDerivAt_fst) using 1
  have he : HasFDerivAt (fun w : Point => mode k w.2)
      (mode k z.2 • ((phase k).comp (ContinuousLinearMap.snd ℝ ℝ Plane))) z :=
    ((phase k).hasFDerivAt.comp z (hasFDerivAt_snd)).cexp
  have hd : multiplierTermDerivative m f k z =
      (m k * coefficient f z.1 k) •
        (mode k z.2 • ((phase k).comp (ContinuousLinearMap.snd ℝ ℝ Plane))) +
      mode k z.2 • (m k • jointLiftP (coefficient (parameterPartial f) z.1 k)) := by
    apply ContinuousLinearMap.ext
    intro v
    change v.1 • (m k * coefficient (parameterPartial f) z.1 k * mode k z.2) +
        v.2.1 • (freqX k * m k * coefficient f z.1 k * mode k z.2) +
        v.2.2 • (freqY k * m k * coefficient f z.1 k * mode k z.2) =
      (m k * coefficient f z.1 k) •
        (mode k z.2 • (v.2.1 • freqX k + v.2.2 • freqY k)) +
      mode k z.2 • (m k • (v.1 • coefficient (parameterPartial f) z.1 k))
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  rw [hd]
  exact (hc.const_mul (m k)).mul he

theorem norm_multiplierTermDerivative_le (m : Frequency → ℂ) (f : Source)
    (k : Frequency) (z : Point) :
    ‖multiplierTermDerivative m f k z‖ ≤
      ‖jointLiftP‖ * ‖m k * coefficient (parameterPartial f) z.1 k‖ +
      ‖jointLiftX‖ * ‖multiplierX m k * coefficient f z.1 k‖ +
      ‖jointLiftY‖ * ‖multiplierY m k * coefficient f z.1 k‖ := by
  unfold multiplierTermDerivative
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    apply add_le_add
    · simpa only [norm_mul, norm_mode, mul_one] using
        jointLiftP.le_opNorm (m k * coefficient (parameterPartial f) z.1 k * mode k z.2)
    · simpa only [norm_mul, norm_mode, mul_one] using
        jointLiftX.le_opNorm (multiplierX m k * coefficient f z.1 k * mode k z.2)
  · simpa only [norm_mul, norm_mode, mul_one] using
      jointLiftY.le_opNorm (multiplierY m k * coefficient f z.1 k * mode k z.2)

theorem uniform_multiplierDerivative_bound {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Point, z.1 ∈ Icc a b → ∀ k,
      ‖multiplierTermDerivative m f k z‖ ≤ C * (weight k ^ 4)⁻¹ := by
  obtain ⟨CP, hCP, hP⟩ := uniform_multiplied_coeff_bound hm
    (parameterPartial_smooth hf) (parameterPartial_periodic hp) a b
  obtain ⟨CX, hCX, hX⟩ := uniform_multiplied_coeff_bound hm.mulX hf hp a b
  obtain ⟨CY, hCY, hY⟩ := uniform_multiplied_coeff_bound hm.mulY hf hp a b
  refine ⟨‖jointLiftP‖ * CP + ‖jointLiftX‖ * CX + ‖jointLiftY‖ * CY, by positivity, ?_⟩
  intro z hz k
  apply (norm_multiplierTermDerivative_le m f k z).trans
  calc
    _ ≤ ‖jointLiftP‖ * (CP * (weight k ^ 4)⁻¹) +
        ‖jointLiftX‖ * (CX * (weight k ^ 4)⁻¹) +
        ‖jointLiftY‖ * (CY * (weight k ^ 4)⁻¹) := by
      gcongr
      · exact hP z.1 hz k
      · exact hX z.1 hz k
      · exact hY z.1 hz k
    _ = _ := by ring

theorem hasFDerivAt_applyMultiplier {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (z : Point) :
    HasFDerivAt (applyMultiplier m f) (∑' k, multiplierTermDerivative m f k z) z := by
  obtain ⟨C, hC, hbound⟩ := uniform_multiplierDerivative_bound hm hf hp (z.1 - 1) (z.1 + 1)
  have hs : Summable (fun k : Frequency => C * (weight k ^ 4)⁻¹) :=
    SmoothFourierData.summable_weight_inv_four.mul_left C
  have hbox : ∀ w ∈ Metric.ball z 1, w.1 ∈ Icc (z.1 - 1) (z.1 + 1) := by
    intro w hw
    have hd : dist w.1 z.1 < 1 := by
      simpa only [dist_eq_norm, Prod.fst_sub] using
        (norm_fst_le (w - z)).trans_lt (show ‖w - z‖ < 1 by
          simpa only [dist_eq_norm] using Metric.mem_ball.mp hw)
    rw [Real.dist_eq] at hd
    constructor <;> linarith [(abs_lt.mp hd).1, (abs_lt.mp hd).2]
  exact hasFDerivAt_tsum_of_isPreconnected hs Metric.isOpen_ball
    (convex_ball z (1 : ℝ)).isPreconnected
    (fun k w _ => hasFDerivAt_multiplierTerm hf m k w)
    (fun k w hw => hbound w (hbox w hw) k)
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
    (summable_terms (multiplied_coeff_rapid hm hf hp z.1) z.2)
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))

theorem fderiv_applyMultiplier {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (z : Point) :
    fderiv ℝ (applyMultiplier m f) z =
      jointLiftP (applyMultiplier m (parameterPartial f) z) +
      jointLiftX (applyMultiplier (multiplierX m) f z) +
      jointLiftY (applyMultiplier (multiplierY m) f z) := by
  have hP := summable_terms (multiplied_coeff_rapid hm
    (parameterPartial_smooth hf) (parameterPartial_periodic hp) z.1) z.2
  have hX := summable_terms (multiplied_coeff_rapid hm.mulX hf hp z.1) z.2
  have hY := summable_terms (multiplied_coeff_rapid hm.mulY hf hp z.1) z.2
  rw [(hasFDerivAt_applyMultiplier hm hf hp z).fderiv]
  simp only [multiplierTermDerivative]
  rw [Summable.tsum_add ((jointLiftP.summable hP).add (jointLiftX.summable hX))
      (jointLiftY.summable hY),
    Summable.tsum_add (jointLiftP.summable hP) (jointLiftX.summable hX),
    ← jointLiftP.map_tsum hP, ← jointLiftX.map_tsum hX, ← jointLiftY.map_tsum hY]
  rfl

/-- Joint smoothness is derived from actual locally uniform Fourier
differentiation, allowing arbitrary polynomially growing multipliers. -/
theorem applyMultiplier_smooth_nat (n : ℕ) {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    ContDiff ℝ n (applyMultiplier m f) := by
  induction n generalizing m f with
  | zero =>
      exact contDiff_zero.mpr (show Differentiable ℝ (applyMultiplier m f) from
        fun z => (hasFDerivAt_applyMultiplier hm hf hp z).differentiableAt).continuous
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
        contDiff_succ_iff_fderiv]
      refine ⟨fun z => (hasFDerivAt_applyMultiplier hm hf hp z).differentiableAt, by simp, ?_⟩
      have he : fderiv ℝ (applyMultiplier m f) = fun z =>
          jointLiftP (applyMultiplier m (parameterPartial f) z) +
          jointLiftX (applyMultiplier (multiplierX m) f z) +
          jointLiftY (applyMultiplier (multiplierY m) f z) :=
        funext (fderiv_applyMultiplier hm hf hp)
      rw [he]
      exact ((jointLiftP.contDiff.comp
        (ih hm (parameterPartial_smooth hf) (parameterPartial_periodic hp))).add
        (jointLiftX.contDiff.comp (ih hm.mulX hf hp))).add
        (jointLiftY.contDiff.comp (ih hm.mulY hf hp))

theorem applyMultiplier_smooth {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    ContDiff ℝ ∞ (applyMultiplier m f) :=
  contDiff_infty.mpr (fun n => applyMultiplier_smooth_nat n hm hf hp)

theorem inverse_smooth (d : Direction) {f : Source} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) : ContDiff ℝ ∞ (inverse d f) :=
  applyMultiplier_smooth (inverseMultiplier_growth d) hf hp

theorem parameterPartial_applyMultiplier {m : Frequency → ℂ} (hm : PolynomialGrowth m)
    {f : Source} (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    parameterPartial (applyMultiplier m f) = applyMultiplier m (parameterPartial f) := by
  funext z
  simp [parameterPartial, fderiv_applyMultiplier hm hf hp, jointLiftP_apply,
    jointLiftX_apply, jointLiftY_apply]

theorem parameterPartial_inverse (d : Direction) {f : Source} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) : parameterPartial (inverse d f) = inverse d (parameterPartial f) :=
  parameterPartial_applyMultiplier (inverseMultiplier_growth d) hf hp

theorem inverse_periodic (d : Direction) (f : Source) : Periodic (inverse d f) := by
  intro p Y k
  exact directionalInverse_periodic d (coefficient f p) Y k.1 k.2

/-- The inverse has zero mean even if the input has a nonzero constant mode. -/
theorem inverse_zeroMean (d : Direction) {f : Source} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) : ZeroMean (inverse d f) := by
  intro p
  have ha := SmoothFourierData.rapid_coefficient (slice_smooth hf p) (hp p)
  let g : C(Torus, ℂ) :=
    ⟨torusSeries (inverseCoeff d (coefficient f p)),
      continuous_torusSeries (ha.inverseCoeff d)⟩
  have hg : SmoothFourierData.torusLift g = slice (inverse d f) p := by
    funext Y
    exact (series_eq_torusSeries (inverseCoeff d (coefficient f p)) Y).symm
  change SmoothFourierData.coefficient (slice (inverse d f) p) 0 = 0
  rw [← hg, SmoothFourierData.coefficient_zero_eq_mean]
  exact TorusInverse.inverse_zero_mean d ha

noncomputable def directionalPartial (d : Direction) (f : Source) (z : Point) : ℂ :=
  fderiv ℝ f z (0, vector d)

/-- Exact inversion for the given function, with the derivative taken in the
joint parameter--torus space. -/
theorem inverse_solves (d : Direction) {f : Source} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) (hm : ZeroMean f) : directionalPartial d (inverse d f) = f := by
  funext z
  have hz := SmoothFourierData.inverse_solves_smooth_periodic d
    (slice_smooth hf z.1) (hp z.1) (by
      change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (z.1, (x, y))) = 0
      rw [← mean_eq_integral]
      exact hm z.1) z.2
  have hd := congrArg (fun L : Plane →L[ℝ] ℂ => L (vector d))
    (slice_hasFDerivAt (inverse_smooth d hf hp) z.1 z.2).fderiv
  exact hd.symm.trans hz

theorem inverse_preserves_parameter_support (d : Direction) (f : Source) (S : Set ℝ)
    (hs : ∀ p, p ∉ S → ∀ Y, f (p, Y) = 0) :
    ∀ p, p ∉ S → ∀ Y, inverse d f (p, Y) = 0 := by
  apply TorusInverse.inverse_preserves_parameter_support d (coefficient f) S
  intro p hp k
  simp only [coefficient, SmoothFourierData.coefficient_eq_doubleIntegral, slice,
    hs p hp, mul_zero, intervalIntegral.integral_zero]

@[simp] theorem parameterJet_zero (f : Source) : parameterJet 0 f = f := rfl

theorem parameterJet_succ (n : ℕ) (f : Source) :
    parameterJet (n + 1) f = parameterPartial (parameterJet n f) :=
  Function.iterate_succ_apply' _ _ _

theorem parameterJet_zeroMean {f : Source} (hf : ContDiff ℝ ∞ f)
    (hm : ZeroMean f) (n : ℕ) : ZeroMean (parameterJet n f) := by
  induction n with
  | zero => exact hm
  | succ n ih =>
      rw [parameterJet_succ]
      exact parameterPartial_zeroMean (parameterJet_smooth hf n) ih

/-- All actual derivatives in the external parameter commute with inversion. -/
theorem parameterJet_inverse (d : Direction) {f : Source} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) (n : ℕ) :
    parameterJet n (inverse d f) = inverse d (parameterJet n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [parameterJet_succ, ih, parameterPartial_inverse d (parameterJet_smooth hf n)
        (parameterJet_periodic hp n), parameterJet_succ]

@[simp] theorem iterateInverse_zero (d : Direction) (f : Source) :
    iterateInverse d 0 f = f := rfl

theorem iterateInverse_succ (d : Direction) (n : ℕ) (f : Source) :
    iterateInverse d (n + 1) f = inverse d (iterateInverse d n f) :=
  Function.iterate_succ_apply' _ _ _

theorem iterateInverse_periodic (d : Direction) {f : Source} (hp : Periodic f)
    (n : ℕ) : Periodic (iterateInverse d n f) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
      rw [iterateInverse_succ]
      exact inverse_periodic d _

theorem iterateInverse_smooth (d : Direction) {f : Source} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) (n : ℕ) : ContDiff ℝ ∞ (iterateInverse d n f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
      rw [iterateInverse_succ]
      exact inverse_smooth d ih (iterateInverse_periodic d hp n)

theorem iterateInverse_zeroMean (d : Direction) {f : Source} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) (hm : ZeroMean f) (n : ℕ) : ZeroMean (iterateInverse d n f) := by
  induction n with
  | zero => exact hm
  | succ n ih =>
      rw [iterateInverse_succ]
      exact inverse_zeroMean d (iterateInverse_smooth d hf hp n)
        (iterateInverse_periodic d hp n)

theorem parameterPartial_iterateInverse (d : Direction) {f : Source}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (n : ℕ) :
    parameterPartial (iterateInverse d n f) = iterateInverse d n (parameterPartial f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterateInverse_succ, parameterPartial_inverse d (iterateInverse_smooth d hf hp n)
        (iterateInverse_periodic d hp n), ih, iterateInverse_succ]

theorem parameterJet_iterateInverse (d : Direction) {f : Source}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) (n q : ℕ) :
    parameterJet q (iterateInverse d n f) = iterateInverse d n (parameterJet q f) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [parameterJet_succ, ih, parameterPartial_iterateInverse d
        (parameterJet_smooth hf q) (parameterJet_periodic hp q), parameterJet_succ]

theorem iterateInverse_solves (d : Direction) {f : Source} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) (hm : ZeroMean f) (n : ℕ) :
    directionalPartial d (iterateInverse d (n + 1) f) = iterateInverse d n f := by
  rw [iterateInverse_succ]
  exact inverse_solves d (iterateInverse_smooth d hf hp n)
    (iterateInverse_periodic d hp n) (iterateInverse_zeroMean d hf hp hm n)

theorem iterateInverse_preserves_parameter_support (d : Direction) (f : Source) (S : Set ℝ)
    (hs : ∀ p, p ∉ S → ∀ Y, f (p, Y) = 0) (n : ℕ) :
    ∀ p, p ∉ S → ∀ Y, iterateInverse d n f (p, Y) = 0 := by
  induction n with
  | zero => exact hs
  | succ n ih =>
      rw [iterateInverse_succ]
      exact inverse_preserves_parameter_support d _ S ih

/-- A genuine mixed coordinate jet: first actual parameter derivatives, then
the indicated word of actual torus-coordinate derivatives. -/
noncomputable def mixedJet (q : ℕ) (w : List Bool) (f : Source) (z : Point) : ℂ :=
  derivativeWord w (slice (parameterJet q f) z.1) z.2

noncomputable def mixedLossConstant (r : ℕ) : ℝ :=
  ((6 * ‖omega⁻¹‖) * ‖omega‖ ^ r) * 3 ^ (r + 5) *
    ∑' k : Frequency, (weight k ^ 4)⁻¹

theorem mixedLossConstant_nonneg (r : ℕ) : 0 ≤ mixedLossConstant r := by
  unfold mixedLossConstant
  positivity

/-- Uniform finite loss: a mixed output jet with r torus derivatives requires
only r+5 pure torus derivatives of the same parameter jet of the input.
The constant is independent of the parameter set and the function. -/
theorem mixedJet_inverse_bound (d : Direction) {f : Source} (hf : ContDiff ℝ ∞ f)
    (hp : Periodic f) (q : ℕ) (w : List Bool) (S : Set ℝ) {C : ℝ}
    (hzero : ∀ p ∈ S, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖parameterJet q f (p, (x, y))‖ ≤ C)
    (hfirst : ∀ p ∈ S, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖SmoothFourierData.xJet (w.length + 5) (slice (parameterJet q f) p) (x, y)‖ ≤ C)
    (hsecond : ∀ p ∈ S, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖SmoothFourierData.xJet (w.length + 5)
        (SmoothFourierData.swapFunction (slice (parameterJet q f) p)) (x, y)‖ ≤ C)
    (p : ℝ) (hps : p ∈ S) (Y : Plane) :
    ‖mixedJet q w (inverse d f) (p, Y)‖ ≤ mixedLossConstant w.length * C := by
  rw [mixedJet, parameterJet_inverse d hf hp]
  have hq := slice_smooth (parameterJet_smooth hf q) p
  have hpq := parameterJet_periodic hp q p
  have hbound := SmoothFourierData.coefficient_seminorm_bound hq hpq (w.length + 1)
    (hzero p hps) (by simpa only [Nat.add_assoc] using hfirst p hps)
    (by simpa only [Nat.add_assoc] using hsecond p hps)
  calc
    _ ≤ ((6 * ‖omega⁻¹‖) * ‖omega‖ ^ w.length) *
        coeffSeminorm (w.length + 1) (coefficient (parameterJet q f) p) :=
      inverse_derivativeWord_bound d (SmoothFourierData.rapid_coefficient hq hpq) w Y
    _ ≤ ((6 * ‖omega⁻¹‖) * ‖omega‖ ^ w.length) *
        ((3 ^ ((w.length + 1) + 4) * C) * ∑' k : Frequency, (weight k ^ 4)⁻¹) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = mixedLossConstant w.length * C := by
      simp only [mixedLossConstant, Nat.add_assoc]
      ring

end NavierStokes.ParametricTorusInverse
