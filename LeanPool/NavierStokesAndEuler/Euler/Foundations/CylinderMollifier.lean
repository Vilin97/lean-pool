/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderCoordinates
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.NoncompactTransport
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PressureJetIdentities
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! Genuine approximate identities for the lifted L² translation representation. -/

@[expose] public section

attribute [local instance] FiniteDimensional.hasContDiffBump

noncomputable section

namespace EulerCylinderMollifier

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderCoordinates
  EulerSobolev EulerNoncompactTransport EulerSpatialSobolevInverse
open scoped ContDiff ENNReal NNReal Topology Convolution

variable (period : ℝ) [Fact (0 < period)]

/-- Actual cylinder translations act strongly continuously on L². -/
theorem translation_continuous (f : LiftL2 period) :
    Continuous (fun a : LiftDomain period => translation period a f) := by
  let g : LiftDomain period → C(LiftDomain period, LiftDomain period) :=
    fun a => ⟨fun x => x + a, continuous_id.add_const a⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.add continuous_fst)
  have h := (continuous_const : Continuous (fun _ : LiftDomain period => f)).compMeasurePreservingLp
    hg (fun a => measurePreserving_translation period a) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  convert h using 1
  funext a
  rfl

omit [Fact (0 < period)] in
theorem euclideanCover_continuous : Continuous (euclideanCover period) := by
  exact ((continuous_fst).prodMk ((AddCircle.continuous_mk' period).comp continuous_snd)).comp
      coordinateEquiv.continuous

omit [Fact (0 < period)] in
theorem euclideanCover_add (x y : Domain 4) :
    euclideanCover period (x + y) = euclideanCover period x + euclideanCover period y := by
  simp [euclideanCover, coveringMap, map_add]

omit [Fact (0 < period)] in
theorem euclideanCover_zero : euclideanCover period 0 = 0 := by
  ext i <;> simp [euclideanCover, coveringMap]

/-- The actual L² translation orbit in Euclidean covering coordinates. -/
def orbit (f : LiftL2 period) (x : Domain 4) : LiftL2 period :=
  translation period (euclideanCover period x) f

theorem orbit_continuous (f : LiftL2 period) : Continuous (orbit period f) :=
  (translation_continuous period f).comp (euclideanCover_continuous period)

@[simp]
theorem orbit_zero (f : LiftL2 period) : orbit period f 0 = f := by
  simp [orbit, euclideanCover_zero, translation_zero]

theorem orbit_norm (f : LiftL2 period) (x : Domain 4) : ‖orbit period f x‖ = ‖f‖ :=
  translation_norm period _ f

/-- A normalized approximate-identity bump with radii tending to zero. -/
def mollifierBump (n : ℕ) : ContDiffBump (0 : Domain 4) where
  rIn := cutoffScale n
  rOut := 2 * cutoffScale n
  rIn_pos := cutoffScale_pos n
  rIn_lt_rOut := by have h := cutoffScale_pos n; linarith

/-- The real smooth compact approximate-identity kernel. -/
def mollifierKernel (n : ℕ) : Domain 4 → ℝ := (mollifierBump n).normed volume

theorem mollifierKernel_smooth (n : ℕ) : ContDiff ℝ ∞ (mollifierKernel n) :=
  (mollifierBump n).contDiff_normed

theorem mollifierKernel_compact (n : ℕ) : HasCompactSupport (mollifierKernel n) :=
  (mollifierBump n).hasCompactSupport_normed

theorem mollifierKernel_nonneg (n : ℕ) (x : Domain 4) : 0 ≤ mollifierKernel n x :=
  (mollifierBump n).nonneg_normed x

theorem mollifierKernel_integral (n : ℕ) : ∫ x, mollifierKernel n x = 1 :=
  (mollifierBump n).integral_normed

/-- Bochner convolution of the actual L² orbit with the smooth approximate identity. -/
def smoothOrbit (n : ℕ) (f : LiftL2 period) : Domain 4 → LiftL2 period :=
  convolution (mollifierKernel n) (orbit period f) (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- The actual L² mollification; its expected representative is the classical periodic convolution.
-/
def mollify (n : ℕ) (f : LiftL2 period) : LiftL2 period := smoothOrbit period n f 0

theorem smoothOrbit_contDiff (n : ℕ) (f : LiftL2 period) : ContDiff ℝ ∞ (smoothOrbit period n f) :=
  (mollifierKernel_compact n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (mollifierKernel_smooth n) (orbit_continuous period f).locallyIntegrable

/-- These actual smoothings converge strongly in the genuine cylinder L² space. -/
theorem mollify_tendsto (f : LiftL2 period) :
    Filter.Tendsto (fun n => mollify period n f) Filter.atTop (𝓝 f) := by
  have hr : Filter.Tendsto (fun n => (mollifierBump n).rOut) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [mollifierBump, mul_zero] using cutoffScale_tendsto.const_mul 2
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure (Domain
      4)))
    hr (orbit_continuous period f) 0
  simpa only [orbit_zero, mollify, smoothOrbit, mollifierKernel] using h

theorem mollify_eq_integral (n : ℕ) (f : LiftL2 period) :
    mollify period n f = ∫ y : Domain 4, mollifierKernel n y • orbit period f (-y) := by
  simp only [mollify, smoothOrbit, convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub]

theorem kernel_orbit_integrable (n : ℕ) (f : LiftL2 period) :
    Integrable (fun y : Domain 4 => mollifierKernel n y • orbit period f (-y)) :=
  ((mollifierKernel_smooth n).continuous.smul ((orbit_continuous period f).comp
      continuous_neg)).integrable_of_hasCompactSupport
    (mollifierKernel_compact n).smul_right

/-- Smoothing is contractive in the actual cylinder L² norm. -/
theorem mollify_norm_le (n : ℕ) (f : LiftL2 period) : ‖mollify period n f‖ ≤ ‖f‖ := by
  rw [mollify_eq_integral]
  have h := norm_integral_le_of_norm_le
    (((mollifierBump n).integrable_normed (μ := (volume : Measure (Domain 4)))).mul_const ‖f‖)
    (f := fun y : Domain 4 => mollifierKernel n y • orbit period f (-y)) ?_
  · simpa only [integral_mul_const, mollifierKernel, (mollifierBump n).integral_normed, one_mul]
      using h
  apply Filter.Eventually.of_forall
  intro y
  rw [norm_smul, orbit_norm, Real.norm_eq_abs, abs_of_nonneg (mollifierKernel_nonneg n y)]
  exact le_rfl

theorem mollify_add (n : ℕ) (f g : LiftL2 period) :
    mollify period n (f + g) = mollify period n f + mollify period n g := by
  simp only [mollify_eq_integral, orbit, map_add, smul_add]
  exact integral_add (kernel_orbit_integrable period n f) (kernel_orbit_integrable period n g)

theorem mollify_smul (n : ℕ) (c : ℝ) (f : LiftL2 period) :
    mollify period n (c • f) = c • mollify period n f := by
  simp only [mollify_eq_integral, orbit, map_smul]
  simp_rw [smul_comm (mollifierKernel n _) c]
  exact integral_smul c _

/-- The actual linear averaging map associated with a smooth compact kernel. -/
def mollifierLinearMap (n : ℕ) : LiftL2 period →ₗ[ℝ] LiftL2 period where
  toFun := mollify period n
  map_add' := mollify_add period n
  map_smul' := mollify_smul period n

/-- The bounded L² approximate-identity operator, with operator norm at most one. -/
def mollifierOperator (n : ℕ) : LiftL2 period →L[ℝ] LiftL2 period :=
  (mollifierLinearMap period n).mkContinuous 1 (fun f => by
    change ‖mollify period n f‖ ≤ 1 * ‖f‖
    simpa using mollify_norm_le period n f)

theorem mollifierOperator_apply (n : ℕ) (f : LiftL2 period) :
    mollifierOperator period n f = mollify period n f := rfl

theorem mollifierOperator_norm_le (n : ℕ) : ‖mollifierOperator period n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
    change ‖mollify period n f‖ ≤ 1 * ‖f‖
    simpa using mollify_norm_le period n f)

/-- The averaging operator commutes with every actual spatial or angular translation. -/
theorem mollify_translation (n : ℕ) (a : LiftDomain period) (f : LiftL2 period) :
    translation period a (mollify period n f) = mollify period n (translation period a f) := by
  rw [mollify_eq_integral, mollify_eq_integral]
  change (translation period a).toContinuousLinearMap
    (∫ y : Domain 4, mollifierKernel n y • orbit period f (-y)) = _
  rw [← (translation period a).toContinuousLinearMap.integral_comp_comm (kernel_orbit_integrable
      period n f)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [map_smul, orbit]
  change mollifierKernel n y • translation period a (translation period (euclideanCover period
      (-y)) f) = _
  rw [translation_add, translation_add, add_comm a]

/-- Smoothing produces actual strong Sobolev jets and commutes with every derivative word. -/
def mollifyJet {directions : Fin 4 → LiftTangent} {s : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (n : ℕ) :
    SpatialJet period directions s (mollify period n f) :=
  EulerPressureJetIdentities.SpatialJet.map (mollifierOperator period n)
    (mollify_translation period n) J

theorem mollifyJet_word {directions : Fin 4 → LiftTangent} {s k : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (n : ℕ) (w : Fin k → Fin 4) :
    (mollifyJet period J n).word w = mollify period n (J.word w) :=
  EulerPressureJetIdentities.SpatialJet.map_word J (mollifierOperator period n)
    (mollify_translation period n) w

/-- Every finite actual derivative word converges strongly under the same mollification. -/
theorem mollifyJet_word_tendsto {directions : Fin 4 → LiftTangent} {s k : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (w : Fin k → Fin 4) :
    Filter.Tendsto (fun n => (mollifyJet period J n).word w) Filter.atTop (𝓝 (J.word w)) := by
  simp only [mollifyJet_word]
  exact mollify_tendsto period (J.word w)

theorem sub_word {directions : Fin 4 → LiftTangent} {s k : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions s f) (K : SpatialJet period directions s g)
    (w : Fin k → Fin 4) : (J.sub K).word w = J.word w - K.word w := by
  induction s generalizing f g k with
  | zero => cases J; cases K; cases k <;> simp [SpatialJet.sub, SpatialJet.word]
  | succ s ih =>
    cases J with
    | succ df lower hd =>
      cases K with
      | succ dg lowerG hG =>
        cases k with
        | zero => simp
        | succ k =>
          simp only [SpatialJet.sub, SpatialJet.word_succ]
          exact ih (lower _) (lowerG _) _

/-- The same genuine mollifiers converge in every finite Sobolev jet norm. -/
theorem mollifyJet_sobolevNorm_tendsto {directions : Fin 4 → LiftTangent} {s : ℕ} {f : LiftL2
    period}
    (J : SpatialJet period directions s f) :
    Filter.Tendsto (fun n => ((mollifyJet period J n).sub J).sobolevNorm) Filter.atTop (𝓝 0) := by
  have hword : ∀ k (w : Fin k → Fin 4), Filter.Tendsto
      (fun n => ‖mollify period n (J.word w) - J.word w‖) Filter.atTop (𝓝 (0 : ℝ)) := by
    intro k w
    simpa using ((mollify_tendsto period (J.word w)).sub_const (J.word w)).norm
  have hlevel : ∀ k, Filter.Tendsto (fun n => ∑ w : Fin k → Fin 4,
      ‖mollify period n (J.word w) - J.word w‖) Filter.atTop (𝓝 (0 : ℝ)) := by
    intro k
    simpa using tendsto_finsetSum (s := (Finset.univ : Finset (Fin k → Fin 4))) (fun w _ => hword k
        w)
  have h := tendsto_finsetSum (s := Finset.range (s + 1)) (fun k _ => hlevel k)
  simpa only [SpatialJet.sobolevNorm_eq_sum_words, sub_word, mollifyJet_word,
      Finset.sum_const_zero] using h

/-- The smooth Hilbert-valued convolution is exactly the translation orbit of the mollified field.
-/
theorem smoothOrbit_eq_orbit_mollify (n : ℕ) (f : LiftL2 period) (x : Domain 4) :
    smoothOrbit period n f x = orbit period (mollify period n f) x := by
  rw [orbit, mollify_eq_integral]
  change _ = (translation period (euclideanCover period x)).toContinuousLinearMap
    (∫ y : Domain 4, mollifierKernel n y • orbit period f (-y))
  rw [← (translation period (euclideanCover period x)).toContinuousLinearMap.integral_comp_comm
    (kernel_orbit_integrable period n f)]
  simp only [smoothOrbit, convolution_def, ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [map_smul, orbit]
  change mollifierKernel n y • translation period (euclideanCover period (x - y)) f =
    mollifierKernel n y • translation period (euclideanCover period x)
      (translation period (euclideanCover period (-y)) f)
  rw [translation_add, ← euclideanCover_add, sub_eq_add_neg]

/-- Mollification produces C∞ vectors for the genuine L² translation representation. -/
theorem mollify_orbit_contDiff (n : ℕ) (f : LiftL2 period) :
    ContDiff ℝ ∞ (orbit period (mollify period n f)) := by
  have heq : orbit period (mollify period n f) = smoothOrbit period n f := by
    funext x
    exact (smoothOrbit_eq_orbit_mollify period n f x).symm
  rw [heq]
  exact smoothOrbit_contDiff period n f

/-- A single sequence of genuine mollifiers approximates every derivative order with
geometrically small errors once that order has entered the diagonal. -/
theorem mollify_diagonal_sequence {directions : Fin 4 → LiftTangent} {f : LiftL2 period}
    (J : ∀ s : ℕ, SpatialJet period directions s f) :
    ∃ index : ℕ → ℕ, (∀ n, n ≤ index n) ∧
      ∀ n s, s ≤ n → ((mollifyJet period (J s) (index n)).sub (J s)).sobolevNorm ≤ (1 / 2 : ℝ) ^ n
          := by
  have hex : ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧
      ∀ s ≤ n, ((mollifyJet period (J s) k).sub (J s)).sobolevNorm ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    have hsum := tendsto_finsetSum (s := Finset.range (n + 1))
      (fun s _ => mollifyJet_sobolevNorm_tendsto period (J s))
    have heps : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    have hsmall : ∀ᶠ k in Filter.atTop,
        (∑ s ∈ Finset.range (n + 1), ((mollifyJet period (J s) k).sub (J s)).sobolevNorm) <
          (1 / 2 : ℝ) ^ n := by
      have hsum0 : Filter.Tendsto (fun k => ∑ s ∈ Finset.range (n + 1),
          ((mollifyJet period (J s) k).sub (J s)).sobolevNorm) Filter.atTop (𝓝 (0 : ℝ)) := by
        simpa only [Finset.sum_const_zero] using hsum
      exact hsum0.eventually (gt_mem_nhds heps)
    obtain ⟨k, hkn, hk⟩ := ((Filter.eventually_ge_atTop n).and hsmall).exists
    refine ⟨k, hkn, fun s hs => ?_⟩
    have hs' : s ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    exact (Finset.single_le_sum (fun j _ => ((mollifyJet period (J j) k).sub (J j)).nonneg)
        hs').trans hk.le
  choose index hindex using hex
  exact ⟨index, fun n => (hindex n).1, fun n s hs => (hindex n).2 s hs⟩

end EulerCylinderMollifier
