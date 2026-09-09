/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketGrowth
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Relative perturbation estimates for the finite-dimensional scalar ODE in the
Euler packet proposal.  These results do not assert the PDE packet lemma.
-/

@[expose] public section

noncomputable section

namespace EulerPacketPerturbation

open Set Filter Real EulerPacketGrowth
open scoped Topology

/-- A compact-interval Volterra absorption estimate with an explicit factor
of two and no exponential loss. -/
theorem integral_absorb
    {g : ℝ → ℝ} {a b A K : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (hgn : ∀ t ∈ Icc a b, 0 ≤ g t) (hK : 0 ≤ K)
    (hsmall : K * (b - a) ≤ 1 / 2)
    (hineq : ∀ t ∈ Icc a b, g t ≤ A + K * ∫ s in a..t, g s) :
    ∀ t ∈ Icc a b, g t ≤ 2 * A := by
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, ⟨le_rfl, hab⟩⟩ hg
  have hsubset : uIcc a c ⊆ Icc a b := by
    rw [uIcc_of_le hc.1]
    exact Icc_subset_Icc le_rfl hc.2
  have hgi : IntervalIntegrable g MeasureTheory.volume a c :=
    (hg.mono hsubset).intervalIntegrable
  have hi := intervalIntegral.integral_mono_on hc.1 hgi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => g c) MeasureTheory.volume a c)
    (fun t ht => hmax (Icc_subset_Icc le_rfl hc.2 ht))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  have hKi := mul_le_mul_of_nonneg_left hi hK
  have hKc : K * (c - a) ≤ 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_left hc.2 hK
    nlinarith
  have hmaxn : 0 ≤ g c := hgn c hc
  have hscaled := mul_le_mul_of_nonneg_right hKc hmaxn
  have hgc : g c ≤ 2 * A := by nlinarith [hineq c hc]
  intro t ht
  exact (hmax ht).trans hgc

/-- Absorbing a Duhamel inequality after division by a positive reference
solution.  This preserves relative rather than absolute control. -/
theorem relative_integral_absorb
    {f U : ℝ → ℝ} {a b A K : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hU : ContinuousOn U (Icc a b))
    (hfn : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hUp : ∀ t ∈ Icc a b, 0 < U t)
    (hK : 0 ≤ K) (hsmall : K * (b - a) ≤ 1 / 2)
    (hineq : ∀ t ∈ Icc a b,
      f t ≤ U t * (A + K * ∫ s in a..t, f s / U s)) :
    ∀ t ∈ Icc a b, f t ≤ 2 * A * U t := by
  have hg := integral_absorb (g := fun t => f t / U t) (A := A) (K := K) hab
    (hf.div hU (fun t ht => ne_of_gt (hUp t ht)))
    (fun t ht => div_nonneg (hfn t ht) (hUp t ht).le) hK hsmall
    (fun t ht => by
      apply (div_le_iff₀ (hUp t ht)).mpr
      convert! hineq t ht using 1
      ring)
  intro t ht
  exact (div_le_iff₀ (hUp t ht)).mp (hg t ht)

/-- The Wronskian of a homogeneous solution and a forced solution obeys an
exact first-order forcing identity. -/
theorem forced_wronskian_derivative
    {D c u u₁ Y Y₁ f g : ℝ → ℝ} {t : ℝ}
    (hu : HasDerivAt u (u₁ t) t)
    (hfu : HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hY : HasDerivAt Y (Y₁ t + f t) t)
    (hfY : HasDerivAt (fun s => D s * Y₁ s) (c t * Y t + D t * g t) t) :
    HasDerivAt (fun s => u s * (D s * Y₁ s) - (D s * u₁ s) * Y s)
      (D t * (u t * g t - u₁ t * f t)) t := by
  apply ((hu.mul hfY).sub (hfu.mul hY)).congr_deriv
  ring

/-- The integrated forced Wronskian identity. -/
theorem forced_wronskian_integral
    {D c u u₁ Y Y₁ f g : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => D s * Y₁ s) (c t * Y t + D t * g t) t)
    (hDc : ContinuousOn D (Icc a b)) (hu₁c : ContinuousOn u₁ (Icc a b))
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b)) :
    ∀ t ∈ Icc a b,
      u t * (D t * Y₁ t) - (D t * u₁ t) * Y t =
        u a * (D a * Y₁ a) - (D a * u₁ a) * Y a +
          ∫ s in a..t, D s * (u s * g s - u₁ s * f s) := by
  intro t ht
  have huc : ContinuousOn u (Icc a b) := fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hcont := hDc.mul ((huc.mul hgc).sub (hu₁c.mul hfc))
  have hsubset : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hint := (hcont.mono hsubset).intervalIntegrable (μ := MeasureTheory.volume)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => forced_wronskian_derivative (hu s (hsubset hs)) (hfu s (hsubset hs))
      (hY s (hsubset hs)) (hfY s (hsubset hs))) hint
  linarith

/-- Variation of constants from two homogeneous solutions whose Wronskian
flux is normalized to one.  This handles forcing in both state components. -/
theorem forced_variation_of_constants
    {D c u u₁ v v₁ Y Y₁ f g : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => D s * Y₁ s) (c t * Y t + D t * g t) t)
    (hDc : ContinuousOn D (Icc a b)) (hu₁c : ContinuousOn u₁ (Icc a b))
    (hv₁c : ContinuousOn v₁ (Icc a b))
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hW0 : u a * (D a * v₁ a) - (D a * u₁ a) * v a = 1) :
    ∀ t ∈ Icc a b,
      let A := u a * (D a * Y₁ a) - (D a * u₁ a) * Y a +
        ∫ s in a..t, D s * (u s * g s - u₁ s * f s)
      let B := v a * (D a * Y₁ a) - (D a * v₁ a) * Y a +
        ∫ s in a..t, D s * (v s * g s - v₁ s * f s)
      Y t = v t * A - u t * B ∧ Y₁ t = v₁ t * A - u₁ t * B := by
  intro t ht
  have hWu := forced_wronskian_integral hu hfu hY hfY hDc hu₁c hfc hgc t ht
  have hWv := forced_wronskian_integral hv hfv hY hfY hDc hv₁c hfc hgc t ht
  have hW := flux_wronskian_constant hu hv hfu hfv t ht
  rw [hW0] at hW
  dsimp only
  rw [← hWu, ← hWv]
  constructor
  · nlinarith [congrArg (fun r : ℝ => r * Y t) hW]
  · nlinarith [congrArg (fun r : ℝ => r * Y₁ t) hW]

/-- First displacement component of the scalar fundamental propagator. -/
def kernel11 (D u u₁ v v₁ : ℝ → ℝ) (t s : ℝ) : ℝ :=
  D s * (u t * v₁ s - v t * u₁ s)

/-- First velocity component of the scalar fundamental propagator. -/
def kernel12 (D u v : ℝ → ℝ) (t s : ℝ) : ℝ :=
  D s * (v t * u s - u t * v s)

/-- Second displacement component of the scalar fundamental propagator. -/
def kernel21 (D u₁ v₁ : ℝ → ℝ) (t s : ℝ) : ℝ :=
  D s * (u₁ t * v₁ s - v₁ t * u₁ s)

/-- Second velocity component of the scalar fundamental propagator. -/
def kernel22 (D u u₁ v v₁ : ℝ → ℝ) (t s : ℝ) : ℝ :=
  D s * (v₁ t * u s - u₁ t * v s)

/-- Duhamel's formula in component form, with an explicitly defined
fundamental kernel. -/
theorem forced_kernel_formula
    {D c u u₁ v v₁ Y Y₁ f g : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => D s * Y₁ s) (c t * Y t + D t * g t) t)
    (hDc : ContinuousOn D (Icc a b)) (hu₁c : ContinuousOn u₁ (Icc a b))
    (hv₁c : ContinuousOn v₁ (Icc a b))
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hW0 : u a * (D a * v₁ a) - (D a * u₁ a) * v a = 1) :
    ∀ t ∈ Icc a b,
      Y t = kernel11 D u u₁ v v₁ t a * Y a + kernel12 D u v t a * Y₁ a +
        ∫ s in a..t, kernel11 D u u₁ v v₁ t s * f s + kernel12 D u v t s * g s ∧
      Y₁ t = kernel21 D u₁ v₁ t a * Y a + kernel22 D u u₁ v v₁ t a * Y₁ a +
        ∫ s in a..t, kernel21 D u₁ v₁ t s * f s + kernel22 D u u₁ v v₁ t s * g s := by
  intro t ht
  have huc : ContinuousOn u (Icc a b) := fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hvc : ContinuousOn v (Icc a b) := fun s hs => (hv s hs).continuousAt.continuousWithinAt
  have hsubset : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hIu := ((hDc.mul ((huc.mul hgc).sub (hu₁c.mul hfc))).mono hsubset).intervalIntegrable
    (μ := MeasureTheory.volume)
  have hIv := ((hDc.mul ((hvc.mul hgc).sub (hv₁c.mul hfc))).mono hsubset).intervalIntegrable
    (μ := MeasureTheory.volume)
  change IntervalIntegrable (fun s => D s * (u s * g s - u₁ s * f s)) MeasureTheory.volume a t
      at hIu
  change IntervalIntegrable (fun s => D s * (v s * g s - v₁ s * f s)) MeasureTheory.volume a t
      at hIv
  have hInt (A B : ℝ) :
      (∫ s in a..t, D s * (A * v₁ s - B * u₁ s) * f s +
        D s * (B * u s - A * v s) * g s) =
      B * (∫ s in a..t, D s * (u s * g s - u₁ s * f s)) -
        A * (∫ s in a..t, D s * (v s * g s - v₁ s * f s)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hIu.const_mul B) (hIv.const_mul A)]
    congr 1
    ext s
    ring
  have hvar := forced_variation_of_constants hu hv hfu hfv hY hfY hDc hu₁c hv₁c hfc hgc hW0 t ht
  dsimp only at hvar
  constructor
  · unfold kernel11 kernel12
    rw [hInt (u t) (v t), hvar.1]
    ring
  · unfold kernel21 kernel22
    rw [hInt (u₁ t) (v₁ t), hvar.2]
    ring

/-- Linear combinations of homogeneous scalar solutions are homogeneous. -/
theorem linear_combination_solution
    {D c u u₁ v v₁ : ℝ → ℝ} {t A B : ℝ}
    (hu : HasDerivAt u (u₁ t) t) (hv : HasDerivAt v (v₁ t) t)
    (hfu : HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : HasDerivAt (fun s => D s * v₁ s) (c t * v t) t) :
    HasDerivAt (fun s => A * u s + B * v s) (A * u₁ t + B * v₁ t) t ∧
    HasDerivAt (fun s => D s * (A * u₁ s + B * v₁ s))
      (c t * (A * u t + B * v t)) t := by
  constructor
  · exact (hu.const_mul A).add (hv.const_mul B)
  · convert! (hfu.const_mul A).add (hfv.const_mul B) using 1
    · ext s
      dsimp only [Pi.add_apply]
      ring
    · ring

/-- The ideal fundamental kernel inherits the relative propagator bound
in each column. -/
theorem equation30_kernel_bound
    {ε Θ : ℝ} {U U₁ V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV₁0 : V₁ 0 = 1) :
    ∀ s t, 0 ≤ s → s ≤ t → t ≤ Θ →
      let D := fun r => 1 + (ε ^ 2 * r ^ 2) ^ 2
      |kernel11 D U U₁ V V₁ t s| + |kernel21 D U₁ V₁ t s| ≤
        20 * Θ ^ 8 * (U t / U s) ∧
      |kernel12 D U V t s| + |kernel22 D U U₁ V V₁ t s| ≤
        20 * Θ ^ 8 * (U t / U s) := by
  intro s t hs hst ht
  let D : ℝ → ℝ := fun r => 1 + (ε ^ 2 * r ^ 2) ^ 2
  let c : ℝ → ℝ := fun r => 2 * (1 - ε ^ 2 * (ε ^ 2 * r ^ 2))
  have hW : U s * (D s * V₁ s) - (D s * U₁ s) * V s = 1 := by
    have hw := flux_wronskian_constant
      (a := 0) (b := s) (D := D) (c := c)
      (fun r hr => hU r hr.1) (fun r hr => hV r hr.1)
      (fun r hr => hfluxU r hr.1) (fun r hr => hfluxV r hr.1) s ⟨hs, le_rfl⟩
    simpa [D, hU0, hU₁0, hV₁0] using hw
  have hlin (A B : ℝ) :
      |A * U t + B * V t| + |A * U₁ t + B * V₁ t| ≤
        20 * Θ ^ 8 * (U t / U s) *
          (|A * U s + B * V s| + |A * U₁ s + B * V₁ s|) := by
    exact equation30_relative_propagator hε hεsmall hΘ hs hst ht hU hfluxU hU0 hU₁0
      (fun r hr => (linear_combination_solution (A := A) (B := B) (D := D) (c := c)
        (hU r (hs.trans hr.1)) (hV r (hs.trans hr.1))
        (hfluxU r (hs.trans hr.1)) (hfluxV r (hs.trans hr.1))).1)
      (fun r hr => (linear_combination_solution (A := A) (B := B) (D := D) (c := c)
        (hU r (hs.trans hr.1)) (hV r (hs.trans hr.1))
        (hfluxU r (hs.trans hr.1)) (hfluxV r (hs.trans hr.1))).2)
  constructor
  · have hb := hlin (D s * V₁ s) (-(D s * U₁ s))
    have hfirst : D s * V₁ s * U s + -(D s * U₁ s) * V s = 1 := by nlinarith [hW]
    have hsecond : D s * V₁ s * U₁ s + -(D s * U₁ s) * V₁ s = 0 := by ring
    rw [hfirst, hsecond] at hb
    norm_num at hb
    convert! hb using 1
    congr 2 <;> dsimp [kernel11, kernel21, D] <;> ring
  · have hb := hlin (-(D s * V s)) (D s * U s)
    have hfirst : -(D s * V s) * U s + D s * U s * V s = 0 := by ring
    have hsecond : -(D s * V s) * U₁ s + D s * U s * V₁ s = 1 := by nlinarith [hW]
    rw [hfirst, hsecond] at hb
    norm_num at hb
    convert! hb using 1
    congr 2 <;> dsimp [kernel12, kernel22, D] <;> ring

/-- The induced sum-of-absolute-values bound from two column bounds. -/
theorem two_column_bound {a b c d x y C : ℝ}
    (h1 : |a| + |c| ≤ C) (h2 : |b| + |d| ≤ C) :
    |a * x + b * y| + |c * x + d * y| ≤ C * (|x| + |y|) := by
  have hfirst := abs_add_le (a * x) (b * y)
  have hsecond := abs_add_le (c * x) (d * y)
  simp only [abs_mul] at hfirst hsecond
  have hx := mul_le_mul_of_nonneg_right h1 (abs_nonneg x)
  have hy := mul_le_mul_of_nonneg_right h2 (abs_nonneg y)
  nlinarith

/-- Passing from Duhamel's formula and relative kernel bounds to a scalar
relative integral inequality, with the forcing in both components. -/
theorem kernel_integral_bound
    {K11 K12 K21 K22 f g U : ℝ → ℝ} {a b y0 y₁0 y y₁ C : ℝ}
    (hab : a ≤ b)
    (h11 : ContinuousOn K11 (Icc a b)) (h12 : ContinuousOn K12 (Icc a b))
    (h21 : ContinuousOn K21 (Icc a b)) (h22 : ContinuousOn K22 (Icc a b))
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hUc : ContinuousOn U (Icc a b)) (hUp : ∀ s ∈ Icc a b, 0 < U s)
    (hcol1 : ∀ s ∈ Icc a b, |K11 s| + |K21 s| ≤ C * (U b / U s))
    (hcol2 : ∀ s ∈ Icc a b, |K12 s| + |K22 s| ≤ C * (U b / U s))
    (hy : y = K11 a * y0 + K12 a * y₁0 + ∫ s in a..b, K11 s * f s + K12 s * g s)
    (hy₁ : y₁ = K21 a * y0 + K22 a * y₁0 + ∫ s in a..b, K21 s * f s + K22 s * g s) :
    |y| + |y₁| ≤ C * (U b / U a) * (|y0| + |y₁0|) +
      C * U b * ∫ s in a..b, (|f s| + |g s|) / U s := by
  have hc1 := (h11.mul hfc).add (h12.mul hgc)
  have hc2 := (h21.mul hfc).add (h22.mul hgc)
  have hi1 : IntervalIntegrable (fun s => |K11 s * f s + K12 s * g s|)
      MeasureTheory.volume a b := hc1.abs.intervalIntegrable_of_Icc hab
  have hi2 : IntervalIntegrable (fun s => |K21 s * f s + K22 s * g s|)
      MeasureTheory.volume a b := hc2.abs.intervalIntegrable_of_Icc hab
  have hsum : IntervalIntegrable
      (fun s => |K11 s * f s + K12 s * g s| + |K21 s * f s + K22 s * g s|)
      MeasureTheory.volume a b := hi1.add hi2
  have hquot : ContinuousOn (fun s => (|f s| + |g s|) / U s) (Icc a b) :=
    (hfc.abs.add hgc.abs).div hUc (fun s hs => ne_of_gt (hUp s hs))
  have hmajor : IntervalIntegrable (fun s => (C * U b) * ((|f s| + |g s|) / U s))
      MeasureTheory.volume a b :=
    (hquot.intervalIntegrable_of_Icc hab).const_mul (C * U b)
  have hpoint : ∀ s ∈ Icc a b,
      |K11 s * f s + K12 s * g s| + |K21 s * f s + K22 s * g s| ≤
        C * U b * ((|f s| + |g s|) / U s) := by
    intro s hs
    convert! two_column_bound (x := f s) (y := g s) (hcol1 s hs) (hcol2 s hs) using 1
    ring
  have hmono := intervalIntegral.integral_mono_on hab hsum hmajor hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have hI : |∫ s in a..b, K11 s * f s + K12 s * g s| +
      |∫ s in a..b, K21 s * f s + K22 s * g s| ≤
      ∫ s in a..b, |K11 s * f s + K12 s * g s| + |K21 s * f s + K22 s * g s| := by
    rw [intervalIntegral.integral_add hi1 hi2]
    exact add_le_add (intervalIntegral.abs_integral_le_integral_abs hab)
      (intervalIntegral.abs_integral_le_integral_abs hab)
  have hbase := two_column_bound (x := y0) (y := y₁0)
    (hcol1 a ⟨le_rfl, hab⟩) (hcol2 a ⟨le_rfl, hab⟩)
  have hfirst : |y| ≤ |K11 a * y0 + K12 a * y₁0| +
      |∫ s in a..b, K11 s * f s + K12 s * g s| := by rw [hy]; exact abs_add_le _ _
  have hsecond : |y₁| ≤ |K21 a * y0 + K22 a * y₁0| +
      |∫ s in a..b, K21 s * f s + K22 s * g s| := by rw [hy₁]; exact abs_add_le _ _
  linarith

/-- Duhamel's inequality for the exact scalar ODE, measured relative to the
zero-slope reference solution.  The forcing may occur in both components. -/
theorem equation30_forced_bound
    {ε Θ a b : ℝ} {U U₁ V V₁ Y Y₁ f g : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (ha : 0 ≤ a) (hb : b ≤ Θ)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV₁0 : V₁ 0 = 1)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfluxY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Y₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Y t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * g t) t)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b)) :
    ∀ t ∈ Icc a b,
      |Y t| + |Y₁ t| ≤ 20 * Θ ^ 8 * (U t / U a) * (|Y a| + |Y₁ a|) +
        20 * Θ ^ 8 * U t * ∫ s in a..t, (|f s| + |g s|) / U s := by
  let D : ℝ → ℝ := fun r => 1 + (ε ^ 2 * r ^ 2) ^ 2
  let c : ℝ → ℝ := fun r => 2 * (1 - ε ^ 2 * (ε ^ 2 * r ^ 2))
  have hUc : ContinuousOn U (Icc a b) :=
    fun t ht => (hU t (ha.trans ht.1)).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Icc a b) :=
    fun t ht => (hV t (ha.trans ht.1)).continuousAt.continuousWithinAt
  have hU₁c : ContinuousOn U₁ (Icc a b) :=
    fun t ht => (equation30_second_derivative (hfluxU t (ha.trans
        ht.1))).continuousAt.continuousWithinAt
  have hV₁c : ContinuousOn V₁ (Icc a b) :=
    fun t ht => (equation30_second_derivative (hfluxV t (ha.trans
        ht.1))).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D (Icc a b) := by fun_prop
  have hW : U a * (D a * V₁ a) - (D a * U₁ a) * V a = 1 := by
    have hw := flux_wronskian_constant
      (a := 0) (b := a) (D := D) (c := c)
      (fun r hr => hU r hr.1) (fun r hr => hV r hr.1)
      (fun r hr => hfluxU r hr.1) (fun r hr => hfluxV r hr.1) a ⟨ha, le_rfl⟩
    simpa [D, hU0, hU₁0, hV₁0] using hw
  have hformula := forced_kernel_formula
    (D := D) (c := c)
    (fun r hr => hU r (ha.trans hr.1)) (fun r hr => hV r (ha.trans hr.1))
    (fun r hr => hfluxU r (ha.trans hr.1)) (fun r hr => hfluxV r (ha.trans hr.1))
    hY hfluxY hDc hU₁c hV₁c hfc hgc hW
  have hUp := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hkernel := equation30_kernel_bound hε hεsmall hΘ hU hV hfluxU hfluxV hU0 hU₁0 hV₁0
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hUc' := hUc.mono hsub
  have hVc' := hVc.mono hsub
  have hU₁c' := hU₁c.mono hsub
  have hV₁c' := hV₁c.mono hsub
  have hDc' := hDc.mono hsub
  have h11 : ContinuousOn (kernel11 D U U₁ V V₁ t) (Icc a t) := by
    unfold kernel11
    exact hDc'.mul ((continuousOn_const.mul hV₁c').sub (continuousOn_const.mul hU₁c'))
  have h12 : ContinuousOn (kernel12 D U V t) (Icc a t) := by
    unfold kernel12
    exact hDc'.mul ((continuousOn_const.mul hUc').sub (continuousOn_const.mul hVc'))
  have h21 : ContinuousOn (kernel21 D U₁ V₁ t) (Icc a t) := by
    unfold kernel21
    exact hDc'.mul ((continuousOn_const.mul hV₁c').sub (continuousOn_const.mul hU₁c'))
  have h22 : ContinuousOn (kernel22 D U U₁ V V₁ t) (Icc a t) := by
    unfold kernel22
    exact hDc'.mul ((continuousOn_const.mul hUc').sub (continuousOn_const.mul hVc'))
  exact kernel_integral_bound ht.1 h11 h12 h21 h22 (hfc.mono hsub) (hgc.mono hsub) hUc'
    (fun s hs => hUp s (ha.trans hs.1))
    (fun s hs => (hkernel s t (ha.trans hs.1) hs.2 (ht.2.trans hb)).1)
    (fun s hs => (hkernel s t (ha.trans hs.1) hs.2 (ht.2.trans hb)).2)
    (hformula t ht).1 (hformula t ht).2

/-- Continuity of the second state component follows from continuity of its
nonvanishing flux coefficient and of the flux. -/
theorem continuousOn_of_flux
    {D f : ℝ → ℝ} {S : Set ℝ}
    (hD : ContinuousOn D S) (hf : ContinuousOn (fun t => D t * f t) S)
    (hDn : ∀ t ∈ S, D t ≠ 0) : ContinuousOn f S := by
  apply (hf.div hD hDn).congr
  intro t ht
  change f t = D t * f t / D t
  field_simp [hDn t ht]

/-- A sufficiently small perturbation grows by at most twice the ideal
relative propagator bound.  Smallness is an explicit interval inequality. -/
theorem equation30_perturbed_bound
    {ε Θ a b δ : ℝ} {U U₁ V V₁ Y Y₁ f g : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ) (hδ : 0 ≤ δ)
    (hsmall : 20 * Θ ^ 8 * δ * (b - a) ≤ 1 / 2)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV₁0 : V₁ 0 = 1)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfluxY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Y₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Y t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * g t) t)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hforcing : ∀ t ∈ Icc a b, |f t| + |g t| ≤ δ * (|Y t| + |Y₁ t|)) :
    ∀ t ∈ Icc a b,
      |Y t| + |Y₁ t| ≤ 40 * Θ ^ 8 * (U t / U a) * (|Y a| + |Y₁ a|) := by
  have hUp := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hUa : 0 < U a := hUp a ha
  have hUc : ContinuousOn U (Icc a b) := fun t ht => (hU t (ha.trans
      ht.1)).continuousAt.continuousWithinAt
  have hYc : ContinuousOn Y (Icc a b) := fun t ht => (hY t ht).continuousAt.continuousWithinAt
  have hY₁c : ContinuousOn Y₁ (Icc a b) := continuousOn_of_flux
    (D := fun s => 1 + (ε ^ 2 * s ^ 2) ^ 2) (by fun_prop)
    (fun t ht => (hfluxY t ht).continuousAt.continuousWithinAt)
    (fun _ _ => ne_of_gt (by positivity))
  have hNc := hYc.abs.add hY₁c.abs
  have hforcingBound := equation30_forced_bound hε hεsmall hΘ ha hb hU hV hfluxU hfluxV
    hU0 hU₁0 hV₁0 hY hfluxY hfc hgc
  have hineq : ∀ t ∈ Icc a b,
      |Y t| + |Y₁ t| ≤ U t *
        (20 * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a +
          (20 * Θ ^ 8 * δ) * ∫ s in a..t, (|Y s| + |Y₁ s|) / U s) := by
    intro t ht
    have hsub : uIcc a t ⊆ Icc a b := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hFcont := (hfc.abs.add hgc.abs).div hUc (fun s hs => ne_of_gt (hUp s (ha.trans hs.1)))
    have hNcont := hNc.div hUc (fun s hs => ne_of_gt (hUp s (ha.trans hs.1)))
    have hFi : IntervalIntegrable (fun s => (|f s| + |g s|) / U s) MeasureTheory.volume a t :=
      (hFcont.mono hsub).intervalIntegrable
    have hNi : IntervalIntegrable (fun s => δ * ((|Y s| + |Y₁ s|) / U s))
        MeasureTheory.volume a t := ((hNcont.mono hsub).intervalIntegrable).const_mul δ
    have hpoint : ∀ s ∈ Icc a t,
        (|f s| + |g s|) / U s ≤ δ * ((|Y s| + |Y₁ s|) / U s) := by
      intro s hs
      have hsab : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
      have hm := div_le_div_of_nonneg_right (hforcing s hsab) (hUp s (ha.trans hs.1)).le
      convert! hm using 1
      ring
    have hi := intervalIntegral.integral_mono_on ht.1 hFi hNi hpoint
    rw [intervalIntegral.integral_const_mul] at hi
    have hUt : 0 < U t := hUp t (ha.trans ht.1)
    have hscaled := mul_le_mul_of_nonneg_left hi
      (show 0 ≤ 20 * Θ ^ 8 * U t by positivity)
    calc
      |Y t| + |Y₁ t| ≤ 20 * Θ ^ 8 * (U t / U a) * (|Y a| + |Y₁ a|) +
          20 * Θ ^ 8 * U t * ∫ s in a..t, (|f s| + |g s|) / U s := hforcingBound t ht
      _ ≤ 20 * Θ ^ 8 * (U t / U a) * (|Y a| + |Y₁ a|) +
          20 * Θ ^ 8 * U t * (δ * ∫ s in a..t, (|Y s| + |Y₁ s|) / U s) :=
        add_le_add le_rfl hscaled
      _ = _ := by ring
  have hresult := relative_integral_absorb
    (f := fun t => |Y t| + |Y₁ t|) (U := U)
    (A := 20 * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a) (K := 20 * Θ ^ 8 * δ)
    hab hNc hUc (fun _ _ => by positivity) (fun t ht => hUp t (ha.trans ht.1))
    (by positivity) hsmall hineq
  intro t ht
  convert! hresult t ht using 1
  ring

/-- Quantitative difference from an ideal solution.  A perturbation of
size `δ = O(e Θ^12)` produces the source's `O(e Θ^29)` relative error. -/
theorem equation30_perturbed_difference_bound
    {ε Θ a b δ : ℝ} {U U₁ V V₁ Y Y₁ Z Z₁ f g : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ) (hδ : 0 ≤ δ)
    (hsmall : 20 * Θ ^ 8 * δ * (b - a) ≤ 1 / 2)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV₁0 : V₁ 0 = 1)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfluxY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Y₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Y t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * g t) t)
    (hZ : ∀ t ∈ Icc a b, HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Z t) t)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hforcing : ∀ t ∈ Icc a b, |f t| + |g t| ≤ δ * (|Y t| + |Y₁ t|)) :
    ∀ t ∈ Icc a b,
      |Y t - Z t| + |Y₁ t - Z₁ t| ≤
        20 * Θ ^ 8 * (U t / U a) * (|Y a - Z a| + |Y₁ a - Z₁ a|) +
          800 * δ * Θ ^ 17 * (U t / U a) * (|Y a| + |Y₁ a|) := by
  have hUp := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hUa : 0 < U a := hUp a ha
  have hUc : ContinuousOn U (Icc a b) := fun t ht => (hU t (ha.trans
      ht.1)).continuousAt.continuousWithinAt
  have hpert := equation30_perturbed_bound hε hεsmall hΘ ha hab hb hδ hsmall
    hU hV hfluxU hfluxV hU0 hU₁0 hV₁0 hY hfluxY hfc hgc hforcing
  have hE : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => Y s - Z s) ((Y₁ t - Z₁ t) + f t) t := by
    intro t ht
    apply ((hY t ht).sub (hZ t ht)).congr_deriv
    ring
  have hfluxE : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * (Y₁ s - Z₁ s))
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * (Y t - Z t) +
          (1 + (ε ^ 2 * t ^ 2) ^ 2) * g t) t := by
    intro t ht
    convert! (hfluxY t ht).sub (hfluxZ t ht) using 1
    · ext s
      dsimp only [Pi.sub_apply]
      ring
    · ring
  have hforced := equation30_forced_bound hε hεsmall hΘ ha hb hU hV hfluxU hfluxV
    hU0 hU₁0 hV₁0 hE hfluxE hfc hgc
  intro t ht
  have hUt : 0 < U t := hUp t (ha.trans ht.1)
  have hsub : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hFcont := (hfc.abs.add hgc.abs).div hUc (fun s hs => ne_of_gt (hUp s (ha.trans hs.1)))
  have hFi : IntervalIntegrable (fun s => (|f s| + |g s|) / U s) MeasureTheory.volume a t :=
    (hFcont.mono hsub).intervalIntegrable
  have hpoint : ∀ s ∈ Icc a t,
      (|f s| + |g s|) / U s ≤ 40 * δ * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a := by
    intro s hs
    have hsab : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
    have hspos := hUp s (ha.trans hs.1)
    apply (div_le_iff₀ hspos).mpr
    have hm := (hforcing s hsab).trans (mul_le_mul_of_nonneg_left (hpert s hsab) hδ)
    convert! hm using 1
    ring
  have hi := intervalIntegral.integral_mono_on ht.1 hFi
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => 40 * δ * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a) MeasureTheory.volume a t) hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  have hscaled := mul_le_mul_of_nonneg_left hi (show 0 ≤ 20 * Θ ^ 8 * U t by positivity)
  have hduration : t - a ≤ Θ := by linarith [ht.2]
  have hlast : 20 * Θ ^ 8 * U t *
      ((t - a) * (40 * δ * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a)) ≤
      800 * δ * Θ ^ 17 * (U t / U a) * (|Y a| + |Y₁ a|) := by
    have hm := mul_le_mul_of_nonneg_left hduration
      (show 0 ≤ 800 * δ * Θ ^ 16 * (U t / U a) * (|Y a| + |Y₁ a|) by positivity)
    convert! hm using 1 <;> ring
  exact (hforced t ht).trans (add_le_add le_rfl (hscaled.trans hlast))

/-- The explicit `Θ^29` relative error bound in the source's normalization.
Its `Θ^21` smallness condition follows from the exact Duhamel argument above. -/
theorem equation30_relative_error_order29
    {ε Θ b e lam : ℝ} {U U₁ V V₁ Y Y₁ Z Z₁ f g : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hb0 : 0 ≤ b) (hb : b ≤ Θ) (he : 0 ≤ e) (hlam : 0 ≤ lam)
    (hsmall : 40 * e * Θ ^ 21 ≤ 1)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV₁0 : V₁ 0 = 1)
    (hY : ∀ t ∈ Icc 0 b, HasDerivAt Y (Y₁ t + f t) t)
    (hfluxY : ∀ t ∈ Icc 0 b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Y₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Y t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * g t) t)
    (hZ : ∀ t ∈ Icc 0 b, HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t ∈ Icc 0 b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Z t) t)
    (hY0 : Y 0 = 1) (hY₁0 : Y₁ 0 = lam) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (hfc : ContinuousOn f (Icc 0 b)) (hgc : ContinuousOn g (Icc 0 b))
    (hforcing : ∀ t ∈ Icc 0 b, |f t| + |g t| ≤ (e * Θ ^ 12) * (|Y t| + |Y₁ t|)) :
    ∀ t ∈ Icc 0 b,
      |Y t - Z t| + |Y₁ t - Z₁ t| ≤ 800 * e * Θ ^ 29 * (1 + lam) * U t := by
  have hΘ0 : 0 ≤ Θ := le_trans zero_le_one hΘ
  have hδ : 0 ≤ e * Θ ^ 12 := by positivity
  have hsmall' : 20 * Θ ^ 8 * (e * Θ ^ 12) * (b - 0) ≤ 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 20 * e * Θ ^ 20 by positivity)
    nlinarith
  have hdiff := equation30_perturbed_difference_bound hε hεsmall hΘ
    (by norm_num : (0 : ℝ) ≤ 0) hb0 hb hδ hsmall'
    hU hV hfluxU hfluxV hU0 hU₁0 hV₁0 hY hfluxY hZ hfluxZ hfc hgc hforcing
  intro t ht
  have hd := hdiff t ht
  simp only [hY0, hY₁0, hZ0, hZ₁0, hU0, sub_self, abs_zero, zero_add,
    mul_zero, add_zero, div_one, abs_one, abs_of_nonneg hlam] at hd
  convert! hd using 1
  ring

end EulerPacketPerturbation
