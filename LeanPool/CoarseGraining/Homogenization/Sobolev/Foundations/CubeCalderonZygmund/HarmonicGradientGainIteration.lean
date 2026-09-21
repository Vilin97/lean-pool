/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicGradientIterationGeometry
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicInteriorHessian
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicDerivative
import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.LimitFiniteP
import LeanPool.CoarseGraining.Homogenization.Sobolev.MatchedPair.ScaledPoincare
import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpCoordinate
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicGradientOneDim

/-! # Harmonic Gradient Gain Iteration -/

namespace Homogenization

open scoped ENNReal BigOperators

noncomputable section

/-!
# Internal exponent-raising carrier for harmonic gradients

The declarations in `INTERNAL` are an induction carrier, not a
source-facing Calderón--Zygmund assumption.  Its membership field is kept
alongside the normalized extended-norm estimate because the next Sobolev step
must construct a genuine `W^{1,p}` witness; finiteness must never be silently
reintroduced as a caller hypothesis.
-/

namespace CubeCalderonZygmund

namespace INTERNAL

/-- The proved induction carrier for a harmonic-gradient integrability gain.
It is deliberately an explicit structure rather than an opaque predicate: its
only analytic data are the stated membership and bound, both quantified over
all harmonic cube solutions. -/
structure HarmonicGradientGain (d : ℕ) (r : FiniteLpExponent) (depth : ℕ) where
  fixedValue : ℝ≥0∞
  constant_pos : 0 < fixedValue
  constant_ne_top : fixedValue ≠ ∞
  memLp : ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
    WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) → ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => u.grad x i) r.exponent
        (normalizedCubeMeasure (centralDescendant Q depth))
  bound : ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
    WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) → ∀ i : Fin d,
      MeasureTheory.eLpNorm (fun x => u.grad x i) r.exponent
          (normalizedCubeMeasure (centralDescendant Q depth)) ≤
        fixedValue * ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q)

/-- Euclidean-facing form of the internal carrier.  This is the API consumed
by vector-valued good-`λ` arguments; no caller supplies coordinate
measurability data. -/
structure HarmonicEuclideanGradientGain (d : ℕ) (r : FiniteLpExponent) (depth : ℕ) where
  fixedValue : ℝ≥0∞
  constant_ne_top : fixedValue ≠ ∞
  memLp : ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
    WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) →
      MeasureTheory.MemLp (fun x => HilbertVec.ofVec (u.grad x)) r.exponent
        (normalizedCubeMeasure (centralDescendant Q depth))
  bound : ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
    WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) →
      MeasureTheory.eLpNorm (fun x => HilbertVec.ofVec (u.grad x)) r.exponent
          (normalizedCubeMeasure (centralDescendant Q depth)) ≤
        fixedValue * ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q)

/-- The unraised base of the induction carrier: normalized `L²` control at
depth zero costs exactly one. -/
noncomputable def harmonicGradientGain_two_zero (d : ℕ) :
    HarmonicGradientGain d FiniteLpExponent.two 0 := by
  refine ⟨1, by norm_num, by norm_num, ?_, ?_⟩
  · intro Q u _ i
    simpa using u.grad_memL2_normalizedCubeMeasure i
  · intro Q u _ i
    simpa only [centralDescendant_zero, one_mul] using!
      (Finset.single_le_sum
        (fun j _ => (bot_le : 0 ≤ MeasureTheory.eLpNorm (fun x => u.grad x j) 2
          (normalizedCubeMeasure Q)))
        (Finset.mem_univ i) :
        MeasureTheory.eLpNorm (fun x => u.grad x i) 2 (normalizedCubeMeasure Q) ≤
          ∑ j : Fin d, MeasureTheory.eLpNorm (fun x => u.grad x j) 2
            (normalizedCubeMeasure Q))

noncomputable def HarmonicEuclideanGradientGain.fromScalar {d : ℕ}
    {r : FiniteLpExponent} {depth : ℕ} (G : HarmonicGradientGain d r depth) :
    HarmonicEuclideanGradientGain d r depth := by
  let C : ℝ≥0∞ := ‖(d : ℝ)‖ₑ * (d : ℝ≥0∞) * G.fixedValue
  have hCtop : C ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top enorm_ne_top (ENNReal.natCast_ne_top d))
      G.constant_ne_top
  refine ⟨C, hCtop, ?_, ?_⟩
  · intro Q u h
    let μ := normalizedCubeMeasure (centralDescendant Q depth)
    have hcoord : ∀ i : Fin d, MeasureTheory.MemLp (fun x => u.grad x i)
        r.exponent μ := fun i => G.memLp Q u h i
    have hvec : MeasureTheory.AEStronglyMeasurable (fun x => u.grad x) μ :=
      (aemeasurable_pi_lambda _ fun i => (hcoord i).aemeasurable).aestronglyMeasurable
    have hhilbert : MeasureTheory.AEStronglyMeasurable
        (fun x => HilbertVec.ofVec (u.grad x)) μ := by
      simpa using (HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable hvec
    refine ⟨hhilbert, ?_⟩
    have hsum : ∑ i : Fin d,
        MeasureTheory.eLpNorm (fun x => u.grad x i) r.exponent μ ≤
        (d : ℝ≥0∞) * (G.fixedValue * ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q)) := by
      calc
        _ ≤ ∑ _i : Fin d, G.fixedValue * ∑ j : Fin d,
            MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q) :=
          Finset.sum_le_sum fun i _ => G.bound Q u h i
        _ = _ := by simp
    have hbound : MeasureTheory.eLpNorm (fun x => HilbertVec.ofVec (u.grad x))
        r.exponent μ ≤ C * ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q) := by
      calc
        _ ≤ ‖(d : ℝ)‖ₑ * ∑ i : Fin d,
            MeasureTheory.eLpNorm (fun x => u.grad x i) r.exponent μ :=
          euclidean_eLpNorm_le_dimension_mul_sum_coordinates μ r u.grad
            fun i => (hcoord i).aestronglyMeasurable
        _ ≤ ‖(d : ℝ)‖ₑ * ((d : ℝ≥0∞) * (G.fixedValue * ∑ j : Fin d,
            MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q))) :=
          mul_le_mul_right hsum _
        _ = _ := by simp [C]; ring
    have hRtop : (∑ j : Fin d,
        MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q)) ≠ ∞ :=
      (ENNReal.sum_ne_top).2 fun j _ =>
        (u.grad_memL2_normalizedCubeMeasure j).eLpNorm_ne_top
    apply lt_of_le_of_lt hbound
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hCtop hRtop)
  · intro Q u h
    let μ := normalizedCubeMeasure (centralDescendant Q depth)
    have hsum : ∑ i : Fin d,
        MeasureTheory.eLpNorm (fun x => u.grad x i) r.exponent μ ≤
        (d : ℝ≥0∞) * (G.fixedValue * ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q)) := by
      calc
        _ ≤ ∑ _i : Fin d, G.fixedValue * ∑ j : Fin d,
            MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q) :=
          Finset.sum_le_sum fun i _ => G.bound Q u h i
        _ = _ := by simp
    calc
      MeasureTheory.eLpNorm (fun x => HilbertVec.ofVec (u.grad x)) r.exponent μ ≤
          ‖(d : ℝ)‖ₑ * ∑ i : Fin d,
            MeasureTheory.eLpNorm (fun x => u.grad x i) r.exponent μ :=
        euclidean_eLpNorm_le_dimension_mul_sum_coordinates μ r u.grad
          fun i => (G.memLp Q u h i).aestronglyMeasurable
      _ ≤ ‖(d : ℝ)‖ₑ * ((d : ℝ≥0∞) * (G.fixedValue * ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q))) := by
        exact mul_le_mul_right hsum _
      _ = C * ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q) := by
        simp [C]
        ring

private theorem memLpOn_openCubeSet_of_memLp_normalizedCubeMeasure
    {d : ℕ} (Q : TriadicCube d) {p : ℝ≥0∞} {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp f p (volumeMeasureOn (openCubeSet Q)) := by
  have hle : cubeMeasure Q ≤ ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    have hvol_nonneg : 0 ≤ cubeVolume Q := cubeVolume_nonneg Q
    have hmul :
        ENNReal.ofReal (cubeVolume Q) * ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul hvol_nonneg]
      have hreal : cubeVolume Q * (cubeVolume Q)⁻¹ = 1 := by
        field_simp [(cubeVolume_pos Q).ne']
      rw [hreal]
      norm_num
    have heq : ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q = cubeMeasure Q := by
      rw [normalizedCubeMeasure]
      ext s
      rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.smul_apply]
      change ENNReal.ofReal (cubeVolume Q) *
          (ENNReal.ofReal ((cubeVolume Q)⁻¹) * cubeMeasure Q s) = cubeMeasure Q s
      rw [← mul_assoc, hmul, one_mul]
    exact le_of_eq heq.symm
  have hcube : MeasureTheory.MemLp f p (cubeMeasure Q) :=
    hf.of_measure_le_smul (c := ENNReal.ofReal (cubeVolume Q)) ENNReal.ofReal_ne_top hle
  simpa [volumeMeasureOn, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using hcube

private theorem eLpNorm_rawCube_eq_scale_mul_normalized {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) (f : Vec d → ℝ) :
    MeasureTheory.eLpNorm f p.exponent (volumeMeasureOn (openCubeSet Q)) =
      (ENNReal.ofReal (cubeScaleFactor Q) ^ ((d : ℝ) / p.exponent.toReal)) *
        MeasureTheory.eLpNorm f p.exponent (normalizedCubeMeasure Q) := by
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have hcoeff :
      ENNReal.ofReal (cubeVolume Q)⁻¹ ^ (1 / p.exponent).toReal =
        (ENNReal.ofReal (cubeScaleFactor Q) ^ ((d : ℝ) / p.exponent.toReal))⁻¹ := by
    rw [cubeVolume_eq_scaleFactor_pow, ENNReal.ofReal_inv_of_pos (pow_pos hscale d)]
    rw [ENNReal.ofReal_pow hscale.le, ENNReal.inv_rpow,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    simp only [one_div, ENNReal.toReal_inv]
    field_simp [ne_of_gt (ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne)]
  have hnorm : MeasureTheory.eLpNorm f p.exponent (normalizedCubeMeasure Q) =
      (ENNReal.ofReal (cubeVolume Q)⁻¹ ^ (1 / p.exponent).toReal) *
        MeasureTheory.eLpNorm f p.exponent (volumeMeasureOn (openCubeSet Q)) := by
    rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact MeasureTheory.eLpNorm_smul_measure_of_ne_zero
      (ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (cubeVolume_pos Q))) f p.exponent _
  rw [hcoeff] at hnorm
  set a : ℝ≥0∞ := ENNReal.ofReal (cubeScaleFactor Q) ^ ((d : ℝ) / p.exponent.toReal)
  have ha0 : a ≠ 0 := ne_of_gt <|
    ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hscale) ENNReal.ofReal_ne_top
  have hat : a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  rw [hnorm]
  calc
    _ = (a * a⁻¹) * MeasureTheory.eLpNorm f p.exponent
        (volumeMeasureOn (openCubeSet Q)) := by simp [a, ENNReal.mul_inv_cancel ha0 hat]
    _ = _ := by ring

private theorem centralDescendant_centralChild {d : ℕ} (Q : TriadicCube d) :
    ∀ n : ℕ, centralDescendant (centralChild Q) n = centralDescendant Q (n + 1)
  | 0 => by simp [centralDescendant]
  | n + 1 => by
    simp only [centralDescendant_succ]
    rw [centralDescendant_centralChild Q n]
    rfl

private theorem openCubeSet_eq_axisCube {d : ℕ} (Q : TriadicCube d) :
    openCubeSet Q =
      axisCube (fun j => ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)
        (cubeScaleFactor Q) := by
  have hupper : ∀ j : Fin d,
      ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + cubeScaleFactor Q =
        ((Q.index j : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by
    intro j
    ring
  ext x
  simp only [openCubeSet, axisCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ioo]
  simp_rw [hupper]

private theorem normalized_cubeSobolevEmbedding_finiteLp {d : ℕ} (hd : 0 < d)
    (r q : FiniteLpExponent)
    (hqr : (q.exponent.toReal)⁻¹ = r.exponent.toReal⁻¹ - (d : ℝ)⁻¹)
    (hrlt : r.exponent.toReal < d) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C ≠ ∞ ∧
      ∀ (Q : TriadicCube d) (v : W1pFunction (openCubeSet Q) r.exponent),
        MeasureTheory.eLpNorm v.toFun q.exponent (normalizedCubeMeasure Q) ≤ C *
          (ENNReal.ofReal (cubeScaleFactor Q) *
            ∑ j : Fin d, MeasureTheory.eLpNorm (fun x => v.grad x j) r.exponent
              (normalizedCubeMeasure Q) +
            MeasureTheory.eLpNorm v.toFun r.exponent (normalizedCubeMeasure Q)) := by
  obtain ⟨C, hCpos, hC⟩ := cubeSobolevEmbedding_finiteLp hd r hrlt
  refine ⟨C, ENNReal.coe_pos.mpr hCpos, ENNReal.coe_ne_top, ?_⟩
  intro Q v
  let z : Vec d := fun j => ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have haxis : openCubeSet Q = axisCube z (cubeScaleFactor Q) := by
    simpa [z] using openCubeSet_eq_axisCube Q
  have hraw : MeasureTheory.eLpNorm v.toFun q.exponent
      (volumeMeasureOn (openCubeSet Q)) ≤ (C : ℝ≥0∞) *
        ((∑ j : Fin d, MeasureTheory.eLpNorm (fun x => v.grad x j) r.exponent
            (volumeMeasureOn (openCubeSet Q))) +
          ENNReal.ofReal (cubeScaleFactor Q)⁻¹ *
            MeasureTheory.eLpNorm v.toFun r.exponent (volumeMeasureOn (openCubeSet Q))) := by
    let P : Set (Vec d) → Prop := fun U =>
      MeasureTheory.eLpNorm v.toFun q.exponent (volumeMeasureOn U) ≤ (C : ℝ≥0∞) *
        ((∑ j : Fin d, MeasureTheory.eLpNorm (fun x => v.grad x j) r.exponent
            (volumeMeasureOn U)) + ENNReal.ofReal (cubeScaleFactor Q)⁻¹ *
          MeasureTheory.eLpNorm v.toFun r.exponent (volumeMeasureOn U))
    let vAxis : W1pFunction (axisCube z (cubeScaleFactor Q)) r.exponent :=
      { toFun := v.toFun
        grad := v.grad
        memLp := by simpa [haxis] using v.memLp
        gradMemLp := by intro i; simpa [haxis] using v.gradMemLp i
        hasWeakGradient := by intro i; simpa [haxis] using v.hasWeakGradient i }
    have haxisBound := hC q hqr z (cubeScaleFactor Q) hscale vAxis
    simpa [P, vAxis, haxis] using haxisBound
  let a : ℝ≥0∞ := ENNReal.ofReal (cubeScaleFactor Q)
  let aq : ℝ≥0∞ := a ^ ((d : ℝ) / q.exponent.toReal)
  let ar : ℝ≥0∞ := a ^ ((d : ℝ) / r.exponent.toReal)
  have hapos : 0 < a := ENNReal.ofReal_pos.mpr hscale
  have ha0 : a ≠ 0 := ne_of_gt hapos
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have haq0 : aq ≠ 0 := ne_of_gt (ENNReal.rpow_pos hapos hat)
  have haqtop : aq ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hat
  have hpow : (d : ℝ) / r.exponent.toReal = (d : ℝ) / q.exponent.toReal + 1 := by
    have hrpos : 0 < r.exponent.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans r.one_lt)) r.lt_top.ne
    have hqpos : 0 < q.exponent.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans q.one_lt)) q.lt_top.ne
    field_simp [hrpos.ne', hqpos.ne'] at hqr ⊢
    linarith
  have har : ar = aq * a := by
    dsimp [ar, aq]
    rw [hpow, ENNReal.rpow_add _ _ ha0 hat]
    norm_num
  have hinv : ENNReal.ofReal (cubeScaleFactor Q)⁻¹ = a⁻¹ :=
    ENNReal.ofReal_inv_of_pos hscale
  rw [eLpNorm_rawCube_eq_scale_mul_normalized Q q] at hraw
  simp_rw [eLpNorm_rawCube_eq_scale_mul_normalized Q r] at hraw
  rw [hinv] at hraw
  change aq * MeasureTheory.eLpNorm v.toFun q.exponent (normalizedCubeMeasure Q) ≤
    (C : ℝ≥0∞) *
      ((∑ j : Fin d, ar * MeasureTheory.eLpNorm (fun x => v.grad x j) r.exponent
        (normalizedCubeMeasure Q)) + a⁻¹ *
          (ar * MeasureTheory.eLpNorm v.toFun r.exponent (normalizedCubeMeasure Q))) at hraw
  rw [har] at hraw
  apply (ENNReal.mul_le_mul_iff_right haq0 haqtop).mp
  calc
    aq * MeasureTheory.eLpNorm v.toFun q.exponent (normalizedCubeMeasure Q) ≤
        (C : ℝ≥0∞) *
          ((∑ j : Fin d, aq * a * MeasureTheory.eLpNorm (fun x => v.grad x j)
            r.exponent (normalizedCubeMeasure Q)) +
            a⁻¹ * (aq * a) * MeasureTheory.eLpNorm v.toFun r.exponent
              (normalizedCubeMeasure Q)) := by
      simpa [a, aq, ar, mul_assoc] using hraw
    _ = aq * ((C : ℝ≥0∞) *
          (a * ∑ j : Fin d, MeasureTheory.eLpNorm (fun x => v.grad x j) r.exponent
            (normalizedCubeMeasure Q) +
            MeasureTheory.eLpNorm v.toFun r.exponent (normalizedCubeMeasure Q))) := by
      have hcancel : a⁻¹ * (aq * a) = aq := by
        calc
          a⁻¹ * (aq * a) = aq * (a⁻¹ * a) := by ring
          _ = aq := by rw [ENNReal.inv_mul_cancel ha0 hat, mul_one]
      rw [hcancel, ← Finset.mul_sum]
      ring

private theorem raw_eLpNorm_two_toReal_eq_scale_pow_mul_cubeLpNorm {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f 2 (normalizedCubeMeasure Q)) :
    (MeasureTheory.eLpNorm f 2 (volumeMeasureOn (openCubeSet Q))).toReal =
      (cubeScaleFactor Q) ^ ((d : ℝ) / 2) * cubeLpNorm Q 2 f := by
  have hraw := eLpNorm_rawCube_eq_scale_mul_normalized Q FiniteLpExponent.two f
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have htop : ENNReal.ofReal (cubeScaleFactor Q) ^ ((d : ℝ) / 2) *
      MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q) ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      hf.eLpNorm_ne_top
  have hreal := congrArg ENNReal.toReal hraw
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hscale.le] at hreal
  simpa [cubeLpNorm] using hreal

private theorem hessianCoordL2NormSum_eq_sum_raw_eLpNorm {d : ℕ}
    {U : Set (Vec d)} {u : H1Function U} (H : HasWeakHessianOn U u) :
    H.hessianCoordL2NormSum =
      ∑ i : Fin d, ∑ j : Fin d,
        (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2 (volumeMeasureOn U)).toReal := by
  unfold HasWeakHessianOn.hessianCoordL2NormSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [HasWeakHessianOn.hessCoordToScalarL2, Homogenization.toScalarL2,
    MeasureTheory.Lp.norm_toLp]

/-- Lift an inequality between real realizations of finite extended norms back
to `ℝ≥0∞`.  All finiteness is explicit, so the induction carrier never turns
an extended-norm comparison into an implicit integrability hypothesis. -/
private theorem ennreal_le_of_toReal_le {a b : ℝ≥0∞}
    (ha : a ≠ ∞) (hb : b ≠ ∞) (h : a.toReal ≤ b.toReal) : a ≤ b :=
  (ENNReal.toReal_le_toReal ha hb).mp h

private theorem centralChild_normalized_hessian_energy_bound {d : ℕ} :
    ∃ A : ℝ, 0 < A ∧
      ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) →
          ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)),
            uS.toFun = u.toFun ∧ uS.grad = u.grad ∧
              ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS,
              cubeScaleFactor (centralChild Q) *
                ∑ i : Fin d, ∑ j : Fin d,
                  cubeLpNorm (centralChild Q) 2 (fun x => H.hess i j x) ≤
                A * ∑ j : Fin d, cubeLpNorm Q 2 (fun x => u.grad x j) := by
  obtain ⟨A, hApos, hA⟩ := exists_harmonic_innerHalf_hessian_energy_bound d
  let B : ℝ := A * (3 : ℝ) ^ ((d : ℝ) / 2 - 1)
  refine ⟨B, mul_pos hApos (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro Q u h
  obtain ⟨uS, huval, hugrad, H, hH⟩ := hA Q u h
  refine ⟨uS, huval, hugrad, H, ?_⟩
  let P : TriadicCube d := centralChild Q
  let S : ℝ := ∑ i : Fin d, ∑ j : Fin d, cubeLpNorm P 2 (fun x => H.hess i j x)
  let T : ℝ := ∑ j : Fin d, cubeLpNorm Q 2 (fun x => u.grad x j)
  have hPsub : openCubeSet P ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ) :=
    (openCubeSet_subset_cubeSet P).trans (by simpa [P] using
      centralChild_cubeSet_subset_scaledOpenInnerHalf Q)
  have hrawrow : ∀ i j : Fin d,
      (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2 (volumeMeasureOn (openCubeSet P))).toReal ≤
        (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
          (volumeMeasureOn (scaledOpenCubeSet Q (1 / 2 : ℝ)))).toReal := by
    intro i j
    apply ENNReal.toReal_mono (H.hess_memL2 i j).eLpNorm_ne_top
    exact MeasureTheory.eLpNorm_mono_measure _
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hPsub)
  have hrawsum : ∑ i : Fin d, ∑ j : Fin d,
      (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2 (volumeMeasureOn (openCubeSet P))).toReal ≤
      H.hessianCoordL2NormSum := by
    calc
      _ ≤ ∑ i : Fin d, ∑ j : Fin d,
          (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
            (volumeMeasureOn (scaledOpenCubeSet Q (1 / 2 : ℝ)))).toReal :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hrawrow i j
      _ = _ := (hessianCoordL2NormSum_eq_sum_raw_eLpNorm H).symm
  have hPmem : ∀ i j : Fin d,
      MeasureTheory.MemLp (fun x => H.hess i j x) 2 (normalizedCubeMeasure P) := by
    intro i j
    exact memL2On_openCubeSet_normalizedCubeMeasure
      ((H.restrict (isOpen_openCubeSet P) hPsub).hess_memL2 i j)
  have hQmem : ∀ j : Fin d,
      MeasureTheory.MemLp (fun x => u.grad x j) 2 (normalizedCubeMeasure Q) := by
    intro j
    exact u.grad_memL2_normalizedCubeMeasure j
  have hrawP : (cubeScaleFactor P) ^ ((d : ℝ) / 2) * S ≤ H.hessianCoordL2NormSum := by
    calc
      (cubeScaleFactor P) ^ ((d : ℝ) / 2) * S =
          ∑ i : Fin d, ∑ j : Fin d,
            (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
              (volumeMeasureOn (openCubeSet P))).toReal := by
        dsimp [S]
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact (raw_eLpNorm_two_toReal_eq_scale_pow_mul_cubeLpNorm P _ (hPmem i j)).symm
      _ ≤ _ := hrawsum
  have hrawQ : u.gradientCoordL2NormSum = (cubeScaleFactor Q) ^ ((d : ℝ) / 2) * T := by
    rw [gradientCoordL2NormSum_eq_sum_eLpNorm]
    dsimp [T]
    calc
      _ = ∑ j : Fin d, (cubeScaleFactor Q) ^ ((d : ℝ) / 2) *
          cubeLpNorm Q 2 (fun x => u.grad x j) := by
          apply Finset.sum_congr rfl
          intro j _
          exact raw_eLpNorm_two_toReal_eq_scale_pow_mul_cubeLpNorm Q _ (hQmem j)
      _ = _ := by rw [Finset.mul_sum]
  have hscaleP : cubeScaleFactor P = cubeScaleFactor Q / 3 := by
    simpa [P] using! cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
  have hscaleQpos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have hscalePpos : 0 < cubeScaleFactor P := by rw [hscaleP]; positivity
  have hpower : cubeScaleFactor P =
      (cubeScaleFactor P) ^ ((d : ℝ) / 2) *
        (cubeScaleFactor P) ^ (1 - (d : ℝ) / 2) := by
    rw [← Real.rpow_add hscalePpos]
    norm_num
  have hratio : (cubeScaleFactor P) ^ (1 - (d : ℝ) / 2) =
      (cubeScaleFactor Q) ^ (1 - (d : ℝ) / 2) *
        (3 : ℝ) ^ ((d : ℝ) / 2 - 1) := by
    rw [hscaleP, Real.div_rpow hscaleQpos.le (by norm_num : 0 ≤ (3 : ℝ))]
    rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : 0 ≤ (3 : ℝ))]
    congr 1
    ring_nf
  calc
    cubeScaleFactor (centralChild Q) * ∑ i : Fin d, ∑ j : Fin d,
        cubeLpNorm (centralChild Q) 2 (fun x => H.hess i j x) = cubeScaleFactor P * S := by rfl
    _ = (cubeScaleFactor P) ^ (1 - (d : ℝ) / 2) *
        ((cubeScaleFactor P) ^ ((d : ℝ) / 2) * S) := by
        calc
          cubeScaleFactor P * S =
              ((cubeScaleFactor P) ^ ((d : ℝ) / 2) *
                (cubeScaleFactor P) ^ (1 - (d : ℝ) / 2)) * S := by rw [← hpower]
          _ = _ := by ring
    _ ≤ (cubeScaleFactor P) ^ (1 - (d : ℝ) / 2) * H.hessianCoordL2NormSum := by
      gcongr
    _ ≤ (cubeScaleFactor P) ^ (1 - (d : ℝ) / 2) *
        (A * (cubeScaleFactor Q)⁻¹ * u.gradientCoordL2NormSum) := by
      gcongr
    _ = B * T := by
      rw [hratio, hrawQ]
      dsimp [B]
      have hqpower : (cubeScaleFactor Q) ^ (1 - (d : ℝ) / 2) *
          (cubeScaleFactor Q) ^ ((d : ℝ) / 2) = cubeScaleFactor Q := by
        rw [← Real.rpow_add hscaleQpos]
        norm_num
      calc
        _ = A * (3 : ℝ) ^ ((d : ℝ) / 2 - 1) *
            ((cubeScaleFactor Q) ^ (1 - (d : ℝ) / 2) *
              (cubeScaleFactor Q) ^ ((d : ℝ) / 2) * (cubeScaleFactor Q)⁻¹) * T := by ring
        _ = _ := by rw [hqpower, mul_inv_cancel₀ hscaleQpos.ne', mul_one]

private theorem centralChild_normalized_hessian_energy_bound_ennreal {d : ℕ} :
    ∃ A : ℝ≥0∞, 0 < A ∧ A ≠ ∞ ∧
      ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) →
          ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)),
            uS.toFun = u.toFun ∧ uS.grad = u.grad ∧
              ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS,
              ENNReal.ofReal (cubeScaleFactor (centralChild Q)) *
                ∑ i : Fin d, ∑ j : Fin d,
                  MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
                    (normalizedCubeMeasure (centralChild Q)) ≤
                A * ∑ j : Fin d,
                  MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q) := by
  obtain ⟨A, hApos, hA⟩ := centralChild_normalized_hessian_energy_bound (d := d)
  refine ⟨ENNReal.ofReal A, ENNReal.ofReal_pos.mpr hApos, ENNReal.ofReal_ne_top, ?_⟩
  intro Q u h
  obtain ⟨uS, huval, hugrad, H, hH⟩ := hA Q u h
  refine ⟨uS, huval, hugrad, H, ?_⟩
  let P : TriadicCube d := centralChild Q
  let L : ℝ≥0∞ := ∑ i : Fin d, ∑ j : Fin d,
    MeasureTheory.eLpNorm (fun x => H.hess i j x) 2 (normalizedCubeMeasure P)
  let R : ℝ≥0∞ := ∑ j : Fin d,
    MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q)
  have hLrowtop : ∀ i : Fin d,
      (∑ j : Fin d, MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
        (normalizedCubeMeasure P)) ≠ ∞ := fun i => ENNReal.sum_ne_top.2 fun j _ =>
      (memL2On_openCubeSet_normalizedCubeMeasure
        ((H.restrict (isOpen_openCubeSet P)
          ((openCubeSet_subset_cubeSet P).trans (by simpa [P] using
            centralChild_cubeSet_subset_scaledOpenInnerHalf Q))).hess_memL2 i j)).eLpNorm_ne_top
  have hLtop : L ≠ ∞ := ENNReal.sum_ne_top.2 fun i _ => hLrowtop i
  have hRtop : R ≠ ∞ := ENNReal.sum_ne_top.2 fun j _ =>
    (u.grad_memL2_normalizedCubeMeasure j).eLpNorm_ne_top
  have hlefttop : ENNReal.ofReal (cubeScaleFactor P) * L ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLtop
  have hrighttop : ENNReal.ofReal A * R ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRtop
  have hLtoReal : L.toReal = ∑ i : Fin d, ∑ j : Fin d,
      (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2 (normalizedCubeMeasure P)).toReal := by
    dsimp [L]
    rw [ENNReal.toReal_sum (fun i _ => hLrowtop i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.toReal_sum]
    intro j _
    exact (memL2On_openCubeSet_normalizedCubeMeasure
      ((H.restrict (isOpen_openCubeSet P)
        ((openCubeSet_subset_cubeSet P).trans (by simpa [P] using
          centralChild_cubeSet_subset_scaledOpenInnerHalf Q))).hess_memL2 i j)).eLpNorm_ne_top
  have hRtoReal : R.toReal = ∑ j : Fin d,
      (MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q)).toReal := by
    dsimp [R]
    rw [ENNReal.toReal_sum]
    intro j _
    exact (u.grad_memL2_normalizedCubeMeasure j).eLpNorm_ne_top
  apply ennreal_le_of_toReal_le hlefttop hrighttop
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
    simpa [cubeScaleFactor] using le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 3) P.scale)),
    hLtoReal, ENNReal.toReal_mul, ENNReal.toReal_ofReal hApos.le, hRtoReal]
  simpa [P, cubeLpNorm] using hH

private theorem centralDescendant_scaleFactor_le {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    ENNReal.ofReal (cubeScaleFactor (centralDescendant Q n)) ≤
      ENNReal.ofReal (cubeScaleFactor Q) := by
  rw [centralDescendant_cubeScaleFactor]
  apply ENNReal.ofReal_le_ofReal
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  apply div_le_self hscale.le
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)

private theorem sum_fin_le_natCast_mul {d : ℕ} (f : Fin d → ℝ≥0∞) (A : ℝ≥0∞)
    (h : ∀ i, f i ≤ A) :
    ∑ i : Fin d, f i ≤ (d : ℝ≥0∞) * A := by
  calc
    ∑ i : Fin d, f i ≤ ∑ _i : Fin d, A :=
      Finset.sum_le_sum fun i _ => h i
    _ = _ := by simp

private theorem row_sum_le_double_sum {d : ℕ} (f : Fin d → Fin d → ℝ≥0∞) (i : Fin d) :
    (∑ j : Fin d, f i j) ≤ ∑ k : Fin d, ∑ j : Fin d, f k j := by
  exact Finset.single_le_sum
    (fun k _ => (zero_le : (0 : ℝ≥0∞) ≤ ∑ j : Fin d, f k j))
    (Finset.mem_univ i)

private noncomputable def hessianGradCoordToW1p {d : ℕ} {U : Set (Vec d)}
    {u : H1Function U} (H : HasWeakHessianOn U u) (i : Fin d) (p : FiniteLpExponent)
    (hvalue : MeasureTheory.MemLp (fun x => u.grad x i) p.exponent
      (MeasureTheory.volume.restrict U))
    (hgrad : ∀ j : Fin d, MeasureTheory.MemLp (fun x => H.hess i j x) p.exponent
      (MeasureTheory.volume.restrict U)) :
    W1pFunction U p.exponent :=
  { toFun := fun x => u.grad x i
    grad := fun x j => H.hess i j x
    memLp := hvalue
    gradMemLp := hgrad
    hasWeakGradient := (H.gradCoordH1Function i).hasWeakGradient }

/-- The exact depth identity used in the derivative branch of the gain
upgrade. -/
private theorem centralDescendant_after_centralChild {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    centralDescendant (centralChild Q) n = centralDescendant Q (n + 1) :=
  centralDescendant_centralChild Q n

private theorem HarmonicGradientGain.restrict_one_more {d : ℕ} {r : FiniteLpExponent}
    {depth : ℕ} (G : HarmonicGradientGain d r depth)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (h : WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0)) (i : Fin d) :
    MeasureTheory.MemLp (fun x => u.grad x i) r.exponent
      (normalizedCubeMeasure (centralDescendant Q (depth + 1))) := by
  have hmem := memLp_centralDescendant_of_memLp (Q := centralDescendant Q depth) 1
    (G.memLp Q u h i)
  simpa [centralDescendant_succ] using hmem

/-- One source-faithful Sobolev step in the internal harmonic-gradient
iteration.  The derivative harmonicity and Hessian witness are both produced
inside the proof; callers supply only the preceding gain carrier. -/
noncomputable def HarmonicGradientGain.upgrade {d : ℕ} (hd : 0 < d)
    {r q : FiniteLpExponent} (hqr : (q.exponent.toReal)⁻¹ =
      r.exponent.toReal⁻¹ - (d : ℝ)⁻¹) (hrlt : r.exponent.toReal < d)
    {depth : ℕ} (G : HarmonicGradientGain d r depth) :
    HarmonicGradientGain d q (depth + 1) := by
  let C : ℝ≥0∞ := Classical.choose
    (normalized_cubeSobolevEmbedding_finiteLp hd r q hqr hrlt)
  have hCspec := Classical.choose_spec
    (normalized_cubeSobolevEmbedding_finiteLp hd r q hqr hrlt)
  have hCpos : 0 < C := hCspec.1
  have hCtop : C ≠ ∞ := hCspec.2.1
  have hC := hCspec.2.2
  let A : ℝ≥0∞ := Classical.choose
    (centralChild_normalized_hessian_energy_bound_ennreal (d := d))
  have hAspec := Classical.choose_spec
    (centralChild_normalized_hessian_energy_bound_ennreal (d := d))
  have hApos : 0 < A := hAspec.1
  have hAtop : A ≠ ∞ := hAspec.2.1
  have hA := hAspec.2.2
  let N : ℝ≥0∞ := ENNReal.ofReal ((3 ^ d : ℕ) : ℝ)
  let K : ℝ≥0∞ := C * ((d : ℝ≥0∞) * G.fixedValue * A + N * G.fixedValue)
  have hdpos : 0 < (d : ℝ≥0∞) := by exact_mod_cast hd
  have hNtop : N ≠ ∞ := by simp [N]
  have hKpos : 0 < K := by
    dsimp [K]
    rw [ENNReal.mul_pos_iff]
    refine ⟨hCpos, lt_of_lt_of_le ?_ (le_add_of_nonneg_right (zero_le))⟩
    rw [ENNReal.mul_pos_iff, ENNReal.mul_pos_iff]
    exact ⟨⟨hdpos, G.constant_pos⟩, hApos⟩
  have hKtop : K ≠ ∞ := by
    dsimp [K]
    apply ENNReal.mul_ne_top hCtop
    rw [ENNReal.add_ne_top]
    exact ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top G.constant_ne_top) hAtop,
      ENNReal.mul_ne_top hNtop G.constant_ne_top⟩
  have hpoint : ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
      WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) → ∀ i : Fin d,
        MeasureTheory.eLpNorm (fun x => u.grad x i) q.exponent
            (normalizedCubeMeasure (centralDescendant Q (depth + 1))) ≤
          K * ∑ j : Fin d,
            MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q) := by
    intro Q u h i
    let P : TriadicCube d := centralChild Q
    let D : TriadicCube d := centralDescendant Q (depth + 1)
    let R : ℝ≥0∞ := ∑ j : Fin d,
      MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q)
    have hSopen : IsOpen (scaledOpenCubeSet Q (1 / 2 : ℝ)) :=
      isOpen_scaledOpenCubeSet Q _
    have hSQ : scaledOpenCubeSet Q (1 / 2 : ℝ) ⊆ openCubeSet Q := by
      exact (scaledOpenCubeSet_subset_scaledClosedCubeSet Q _).trans
        (scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q
          (by norm_num) (by norm_num))
    have hPopen : IsOpen (openCubeSet P) := isOpen_openCubeSet P
    have hPS : openCubeSet P ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ) :=
      (openCubeSet_subset_cubeSet P).trans (by simpa [P] using
        centralChild_cubeSet_subset_scaledOpenInnerHalf Q)
    have hDopen : IsOpen (openCubeSet D) := isOpen_openCubeSet D
    have hDP : openCubeSet D ⊆ openCubeSet P := by
      have hdesc := centralDescendant_openCubeSet_subset P depth
      simpa [P, D, centralDescendant_after_centralChild] using hdesc
    obtain ⟨uS, huval, hugrad, H, henergy⟩ := hA Q u h
    have huS : uS = u.restrict hSopen hSQ := by
      apply H1Function.ext
      · simpa [H1Function.restrict] using huval
      · simpa [H1Function.restrict] using hugrad
    subst uS
    let HP := H.restrict hPopen hPS
    let v := HP.gradCoordH1Function i
    have hS : WeakPoissonEquationOn (scaledOpenCubeSet Q (1 / 2 : ℝ))
        (u.restrict hSopen hSQ) (fun _ => 0) := h.restrict hSopen hSQ
    have hvS : WeakPoissonEquationOn (scaledOpenCubeSet Q (1 / 2 : ℝ))
        (H.gradCoordH1Function i) (fun _ => 0) :=
      hS.gradCoordH1Function_harmonic hSopen H i
    have hv_eq : v = (H.gradCoordH1Function i).restrict hPopen hPS := by
      apply H1Function.ext <;> rfl
    have hv : WeakPoissonEquationOn (openCubeSet P) v (fun _ => 0) := by
      rw [hv_eq]
      exact hvS.restrict hPopen hPS
    let HD := HP.restrict hDopen hDP
    have hD_eq : centralDescendant P depth = D := by
      simpa [P, D] using centralDescendant_after_centralChild Q depth
    have hsource : MeasureTheory.eLpNorm (fun x => u.grad x i) r.exponent
        (normalizedCubeMeasure D) ≤ N * G.fixedValue * R := by
      calc
        MeasureTheory.eLpNorm (fun x => u.grad x i) r.exponent
            (normalizedCubeMeasure D) =
            MeasureTheory.eLpNorm (fun x => u.grad x i) r.exponent
              (normalizedCubeMeasure (centralDescendant (centralDescendant Q depth) 1)) := by
                simp [D, centralDescendant_succ]
        _ ≤ N * MeasureTheory.eLpNorm (fun x => u.grad x i) r.exponent
              (normalizedCubeMeasure (centralDescendant Q depth)) := by
                simpa [N] using eLpNorm_centralDescendant_le_descendantCount_mul
                  (centralDescendant Q depth) 1 r (fun x => u.grad x i)
        _ ≤ N * (G.fixedValue * R) := by
                gcongr
                simpa [R] using G.bound Q u h i
        _ = N * G.fixedValue * R := by ring
    have hgrad : ∀ j : Fin d,
        MeasureTheory.eLpNorm (fun x => HD.hess i j x) r.exponent
            (normalizedCubeMeasure D) ≤
          G.fixedValue * ∑ k : Fin d,
            MeasureTheory.eLpNorm (fun x => HP.hess i k x) 2
              (normalizedCubeMeasure P) := by
      intro j
      simpa [HD, v, hD_eq] using! G.bound P v hv j
    have hsum : ∑ j : Fin d,
        MeasureTheory.eLpNorm (fun x => HD.hess i j x) r.exponent
            (normalizedCubeMeasure D) ≤
          (d : ℝ≥0∞) * (G.fixedValue * ∑ k : Fin d,
            MeasureTheory.eLpNorm (fun x => HP.hess i k x) 2
              (normalizedCubeMeasure P)) :=
      sum_fin_le_natCast_mul _ _ hgrad
    have hrow : ∑ k : Fin d,
        MeasureTheory.eLpNorm (fun x => HP.hess i k x) 2
          (normalizedCubeMeasure P) ≤
        ∑ a : Fin d, ∑ b : Fin d,
          MeasureTheory.eLpNorm (fun x => HP.hess a b x) 2
            (normalizedCubeMeasure P) :=
      row_sum_le_double_sum (fun a b => MeasureTheory.eLpNorm
        (fun x => HP.hess a b x) 2 (normalizedCubeMeasure P)) i
    have hscale : ENNReal.ofReal (cubeScaleFactor D) ≤
        ENNReal.ofReal (cubeScaleFactor P) := by
      rw [← hD_eq]
      exact centralDescendant_scaleFactor_le P depth
    have henergy' : ENNReal.ofReal (cubeScaleFactor P) *
        ∑ a : Fin d, ∑ b : Fin d,
          MeasureTheory.eLpNorm (fun x => HP.hess a b x) 2
            (normalizedCubeMeasure P) ≤ A * R := by
      simpa [P, HP, R] using! henergy
    have hgradient : ENNReal.ofReal (cubeScaleFactor D) *
        ∑ j : Fin d, MeasureTheory.eLpNorm (fun x => HD.hess i j x) r.exponent
          (normalizedCubeMeasure D) ≤
        (d : ℝ≥0∞) * G.fixedValue * A * R := by
      calc
        _ ≤ ENNReal.ofReal (cubeScaleFactor D) *
            ((d : ℝ≥0∞) * (G.fixedValue * ∑ k : Fin d,
              MeasureTheory.eLpNorm (fun x => HP.hess i k x) 2
                (normalizedCubeMeasure P))) := by gcongr
        _ = (d : ℝ≥0∞) * G.fixedValue *
            (ENNReal.ofReal (cubeScaleFactor D) * ∑ k : Fin d,
              MeasureTheory.eLpNorm (fun x => HP.hess i k x) 2
                (normalizedCubeMeasure P)) := by ring
        _ ≤ (d : ℝ≥0∞) * G.fixedValue *
            (ENNReal.ofReal (cubeScaleFactor P) * ∑ a : Fin d, ∑ b : Fin d,
              MeasureTheory.eLpNorm (fun x => HP.hess a b x) 2
                (normalizedCubeMeasure P)) := by
              apply mul_le_mul_right
              calc
                ENNReal.ofReal (cubeScaleFactor D) * ∑ k : Fin d,
                    MeasureTheory.eLpNorm (fun x => HP.hess i k x) 2
                      (normalizedCubeMeasure P) ≤
                    ENNReal.ofReal (cubeScaleFactor P) * ∑ k : Fin d,
                      MeasureTheory.eLpNorm (fun x => HP.hess i k x) 2
                      (normalizedCubeMeasure P) := mul_le_mul_left hscale _
                _ ≤ _ := mul_le_mul_right hrow _

        _ ≤ (d : ℝ≥0∞) * G.fixedValue * (A * R) :=
          mul_le_mul_right henergy' _
        _ = _ := by ring
    let w : W1pFunction (openCubeSet D) r.exponent := hessianGradCoordToW1p HD i r
      (memLpOn_openCubeSet_of_memLp_normalizedCubeMeasure D (by
        simpa [HD, HP, H1Function.restrict] using! G.restrict_one_more Q u h i))
      (fun j => memLpOn_openCubeSet_of_memLp_normalizedCubeMeasure D (by
        simpa [HD, v, hD_eq] using! G.memLp P v hv j))
    have hsob := hC D w
    have hsob' : MeasureTheory.eLpNorm (fun x => u.grad x i) q.exponent
        (normalizedCubeMeasure D) ≤ C *
          (ENNReal.ofReal (cubeScaleFactor D) * ∑ j : Fin d,
            MeasureTheory.eLpNorm (fun x => HD.hess i j x) r.exponent
              (normalizedCubeMeasure D) +
            MeasureTheory.eLpNorm (fun x => u.grad x i) r.exponent
              (normalizedCubeMeasure D)) := by
      simpa [w, hessianGradCoordToW1p, HD, H1Function.restrict] using hsob
    calc
      MeasureTheory.eLpNorm (fun x => u.grad x i) q.exponent
          (normalizedCubeMeasure (centralDescendant Q (depth + 1))) =
          MeasureTheory.eLpNorm (fun x => u.grad x i) q.exponent
            (normalizedCubeMeasure D) := by rfl
      _ ≤ C * ((d : ℝ≥0∞) * G.fixedValue * A * R + N * G.fixedValue * R) := by
        calc
          _ ≤ C * (ENNReal.ofReal (cubeScaleFactor D) * ∑ j : Fin d,
              MeasureTheory.eLpNorm (fun x => HD.hess i j x) r.exponent
                (normalizedCubeMeasure D) +
              MeasureTheory.eLpNorm (fun x => u.grad x i) r.exponent
                (normalizedCubeMeasure D)) := hsob'
          _ ≤ _ := by gcongr
      _ = K * R := by simp [K]; ring
  refine ⟨K, hKpos, hKtop, ?_, hpoint⟩
  intro Q u h i
  refine ⟨(G.restrict_one_more Q u h i).aestronglyMeasurable, ?_⟩
  apply lt_of_le_of_lt (hpoint Q u h i)
  exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hKtop
    ((ENNReal.sum_ne_top).2 fun j _ =>
      (u.grad_memL2_normalizedCubeMeasure j).eLpNorm_ne_top))

/-- Lowering the exponent on a probability-normalized cube preserves an
internal gain carrier without changing its analytic constant. -/
noncomputable def HarmonicGradientGain.downgrade {d : ℕ} {r s : FiniteLpExponent}
    {depth : ℕ} (G : HarmonicGradientGain d r depth) (hsr : s.exponent ≤ r.exponent) :
    HarmonicGradientGain d s depth := by
  refine ⟨G.fixedValue, G.constant_pos, G.constant_ne_top, ?_, ?_⟩
  · intro Q u h i
    let : MeasureTheory.IsProbabilityMeasure
        (normalizedCubeMeasure (centralDescendant Q depth)) :=
      ⟨normalizedCubeMeasure_apply_univ _⟩
    refine ⟨(G.memLp Q u h i).aestronglyMeasurable, ?_⟩
    apply lt_of_le_of_lt
      (MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le hsr
        (G.memLp Q u h i).aestronglyMeasurable)
    exact lt_of_le_of_lt (G.bound Q u h i)
      (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top G.constant_ne_top
        ((ENNReal.sum_ne_top).2 fun j _ =>
          (u.grad_memL2_normalizedCubeMeasure j).eLpNorm_ne_top)))
  · intro Q u h i
    let : MeasureTheory.IsProbabilityMeasure
        (normalizedCubeMeasure (centralDescendant Q depth)) :=
      ⟨normalizedCubeMeasure_apply_univ _⟩
    exact (MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le hsr
      (G.memLp Q u h i).aestronglyMeasurable).trans (G.bound Q u h i)

/-- The explicit finite Sobolev ladder used above the `L²` base.  The side
condition is precisely the positivity of its denominator. -/
private noncomputable def sobolevLadderExponent (d : ℕ) (hd : 2 ≤ d)
    (n : ℕ) (hn : 2 * n < d) :
    FiniteLpExponent where
  exponent := ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 2 * n))
  one_lt := by
    rw [ENNReal.one_lt_ofReal]
    have hn' : (2 * n : ℝ) < d := by exact_mod_cast hn
    have hden : 0 < (d : ℝ) - 2 * n := by linarith
    have hd' : 2 ≤ (d : ℝ) := by exact_mod_cast hd
    rw [lt_div_iff₀ hden]
    nlinarith
  lt_top := ENNReal.ofReal_lt_top

private theorem sobolevLadderExponent_toReal (d : ℕ) (hd : 2 ≤ d)
    (n : ℕ) (hn : 2 * n < d) :
    (sobolevLadderExponent d hd n hn).exponent.toReal =
      2 * (d : ℝ) / ((d : ℝ) - 2 * n) := by
  have hn' : (2 * n : ℝ) < d := by exact_mod_cast hn
  have hden : 0 ≤ (d : ℝ) - 2 * n := by linarith
  have hnum : 0 ≤ 2 * (d : ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  simp [sobolevLadderExponent, ENNReal.toReal_ofReal
    (div_nonneg hnum hden)]

private theorem sobolevLadderExponent_step_relation (d : ℕ) (hd : 2 ≤ d)
    (n : ℕ) (hn : 2 * (n + 1) < d) :
    (sobolevLadderExponent d hd (n + 1) hn).exponent.toReal⁻¹ =
      (sobolevLadderExponent d hd n (by omega)).exponent.toReal⁻¹ - (d : ℝ)⁻¹ := by
  rw [sobolevLadderExponent_toReal, sobolevLadderExponent_toReal]
  have hd' : 0 < (d : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hn)
  have hn0 : 0 < (d : ℝ) - 2 * n := by
    have hn' : (2 * (n + 1) : ℝ) < d := by exact_mod_cast hn
    linarith
  have hn1 : 0 < (d : ℝ) - 2 * (n + 1) := by
    have hn' : (2 * (n + 1) : ℝ) < d := by exact_mod_cast hn
    linarith
  field_simp [hd'.ne', hn0.ne', hn1.ne']
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

private theorem sobolevLadderExponent_lt_dimension (d : ℕ) (hd : 2 ≤ d)
    (n : ℕ) (hn : 2 * (n + 1) < d) :
    (sobolevLadderExponent d hd n (by omega)).exponent.toReal < d := by
  rw [sobolevLadderExponent_toReal]
  have hd' : 0 < (d : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hn)
  have hn' : (2 * (n + 1) : ℝ) < d := by exact_mod_cast hn
  have hden : 0 < (d : ℝ) - 2 * n := by linarith
  rw [div_lt_iff₀ hden]
  nlinarith

private theorem finiteLpExponent_eq {p q : FiniteLpExponent}
    (h : p.exponent = q.exponent) : p = q := by
  cases p
  cases q
  simp_all

private theorem sobolevLadderExponent_zero (d : ℕ) (hd : 2 ≤ d) :
    sobolevLadderExponent d hd 0 (by omega) = FiniteLpExponent.two := by
  apply finiteLpExponent_eq
  have hd' : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
  simp [sobolevLadderExponent, hd'.ne']

private noncomputable def harmonicGradientGain_ladder (d : ℕ) (hd : 3 ≤ d) :
    ∀ (n : ℕ) (hn : 2 * n < d),
      HarmonicGradientGain d (sobolevLadderExponent d (by omega) n hn) n
  | 0, hn => by
      rw [sobolevLadderExponent_zero d (by omega)]
      exact harmonicGradientGain_two_zero d
  | n + 1, hn => by
      exact HarmonicGradientGain.upgrade (by omega)
        (sobolevLadderExponent_step_relation d (by omega) n hn)
        (sobolevLadderExponent_lt_dimension d (by omega) n hn)
        (harmonicGradientGain_ladder d hd n (by omega))

private theorem terminalLadderDepth_twice_lt (d : ℕ) (hd : 3 ≤ d) :
    2 * ((d - 1) / 2) < d := by omega

private theorem terminalLadderExponent_ge_dimension (d : ℕ) (hd : 3 ≤ d) :
    (d : ℝ) ≤ (sobolevLadderExponent d (by omega) ((d - 1) / 2)
      (terminalLadderDepth_twice_lt d hd)).exponent.toReal := by
  rw [sobolevLadderExponent_toReal]
  let N : ℕ := (d - 1) / 2
  have hden : 0 < (d : ℝ) - ((2 * N : ℕ) : ℝ) := by
    have hNat : 2 * ((d - 1) / 2) < d := terminalLadderDepth_twice_lt d hd
    have hNat' : ((2 * ((d - 1) / 2) : ℕ) : ℝ) < (d : ℝ) := by
      exact_mod_cast hNat
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hNat'
    simpa [N] using sub_pos.mpr hNat'
  change (d : ℝ) ≤ (2 * (d : ℝ)) / ((d : ℝ) - 2 * (N : ℝ))
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hden
  apply (le_div_iff₀ hden).2
  have hNat : d ≤ 2 * ((d - 1) / 2) + 2 := by omega
  have hNat' : (d : ℝ) ≤ ((2 * ((d - 1) / 2) + 2 : ℕ) : ℝ) := by
    exact_mod_cast hNat
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hNat'
  change (d : ℝ) * ((d : ℝ) - 2 * (N : ℝ)) ≤ 2 * (d : ℝ)
  simp only [N] at hden ⊢
  nlinarith

private noncomputable def targetSobolevSourceExponent (d : ℕ) (hd2 : 2 ≤ d) (q : FiniteLpExponent)
    (hq : (2 : ℝ) < q.exponent.toReal) : FiniteLpExponent where
  exponent := ENNReal.ofReal ((d : ℝ) * q.exponent.toReal /
    ((d : ℝ) + q.exponent.toReal))
  one_lt := by
    rw [ENNReal.one_lt_ofReal]
    have hd : 2 ≤ (d : ℝ) := by exact_mod_cast hd2
    have hq' : 0 < q.exponent.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans q.one_lt)) q.lt_top.ne
    have hden : 0 < (d : ℝ) + q.exponent.toReal := by positivity
    rw [lt_div_iff₀ hden]
    nlinarith
  lt_top := ENNReal.ofReal_lt_top

private theorem targetSobolevSourceExponent_toReal (d : ℕ) (hd2 : 2 ≤ d) (q : FiniteLpExponent)
    (hq : (2 : ℝ) < q.exponent.toReal) :
    (targetSobolevSourceExponent d hd2 q hq).exponent.toReal =
      (d : ℝ) * q.exponent.toReal / ((d : ℝ) + q.exponent.toReal) := by
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hq' : 0 ≤ q.exponent.toReal := ENNReal.toReal_nonneg
  simp [targetSobolevSourceExponent, ENNReal.toReal_ofReal
    (div_nonneg (mul_nonneg hd hq') (add_nonneg hd hq'))]

private theorem targetSobolevSourceExponent_lt_dimension (d : ℕ) (hd2 : 2 ≤ d)
    (q : FiniteLpExponent)
    (hq : (2 : ℝ) < q.exponent.toReal) :
    (targetSobolevSourceExponent d hd2 q hq).exponent.toReal < d := by
  rw [targetSobolevSourceExponent_toReal]
  have hd : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd2)
  have hq' : 0 < q.exponent.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans q.one_lt)) q.lt_top.ne
  have hden : 0 < (d : ℝ) + q.exponent.toReal := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith

private theorem targetSobolevSourceExponent_relation (d : ℕ) (hd2 : 2 ≤ d)
    (q : FiniteLpExponent)
    (hq : (2 : ℝ) < q.exponent.toReal) :
    q.exponent.toReal⁻¹ = (targetSobolevSourceExponent d hd2 q hq).exponent.toReal⁻¹ -
      (d : ℝ)⁻¹ := by
  rw [targetSobolevSourceExponent_toReal]
  have hd : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd2)
  have hq' : 0 < q.exponent.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans q.one_lt)) q.lt_top.ne
  have hden : 0 < (d : ℝ) + q.exponent.toReal := by positivity
  field_simp [hd.ne', hq'.ne', hden.ne']
  ring

private theorem targetSobolevSourceExponent_le_two_twoDim (q : FiniteLpExponent)
    (hq : (2 : ℝ) < q.exponent.toReal) :
    (targetSobolevSourceExponent 2 (by norm_num) q hq).exponent ≤ 2 := by
  apply (ENNReal.toReal_le_toReal
    (targetSobolevSourceExponent 2 (by norm_num) q hq).lt_top.ne (by norm_num)).mp
  rw [targetSobolevSourceExponent_toReal]
  have hq' : 0 < q.exponent.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans q.one_lt)) q.lt_top.ne
  have hden : 0 < (2 : ℝ) + q.exponent.toReal := by positivity
  norm_num
  rw [div_le_iff₀ hden]
  nlinarith

/-- In dimension two, one final finite Sobolev step from the downgraded `L²`
base reaches every target above two. -/
noncomputable def harmonicGradientGain_finiteTarget_gt_two_twoDim
    (q : FiniteLpExponent) (hq2 : 2 < q.exponent) :
    HarmonicGradientGain 2 q 1 := by
  have hq : (2 : ℝ) < q.exponent.toReal :=
    (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).2 hq2
  let r : FiniteLpExponent := targetSobolevSourceExponent 2 (by norm_num) q hq
  let Gr : HarmonicGradientGain 2 r 0 :=
    (harmonicGradientGain_two_zero 2).downgrade
      (targetSobolevSourceExponent_le_two_twoDim q hq)
  exact HarmonicGradientGain.upgrade (d := 2) (by norm_num)
    (targetSobolevSourceExponent_relation 2 (by norm_num) q hq)
    (targetSobolevSourceExponent_lt_dimension 2 (by norm_num) q hq) Gr

noncomputable def harmonicEuclideanGradientGain_finiteTarget_gt_two_twoDim
    (q : FiniteLpExponent) (hq2 : 2 < q.exponent) :
    HarmonicEuclideanGradientGain 2 q 1 :=
  HarmonicEuclideanGradientGain.fromScalar
    (harmonicGradientGain_finiteTarget_gt_two_twoDim q hq2)

private theorem targetSobolevSourceExponent_le_terminalLadder (d : ℕ) (hd : 3 ≤ d)
    (q : FiniteLpExponent) (hq : (2 : ℝ) < q.exponent.toReal) :
    (targetSobolevSourceExponent d (by omega) q hq).exponent ≤
      (sobolevLadderExponent d (by omega) ((d - 1) / 2)
        (terminalLadderDepth_twice_lt d hd)).exponent := by
  apply (ENNReal.toReal_le_toReal
    (targetSobolevSourceExponent d (by omega) q hq).lt_top.ne
    (sobolevLadderExponent d (by omega) ((d - 1) / 2)
      (terminalLadderDepth_twice_lt d hd)).lt_top.ne).mp
  exact (targetSobolevSourceExponent_lt_dimension d (by omega) q hq).le.trans
    (terminalLadderExponent_ge_dimension d hd)

/-- The final Sobolev step from the terminal ladder exponent. -/
noncomputable def harmonicGradientGain_finiteTarget_gt_two_of_three_le
    (d : ℕ) (hd : 3 ≤ d) (q : FiniteLpExponent) (hq2 : 2 < q.exponent) :
    HarmonicGradientGain d q (((d - 1) / 2) + 1) := by
  let n : ℕ := (d - 1) / 2
  let p : FiniteLpExponent := sobolevLadderExponent d (by omega) n
    (terminalLadderDepth_twice_lt d hd)
  let G : HarmonicGradientGain d p n := harmonicGradientGain_ladder d hd n
    (terminalLadderDepth_twice_lt d hd)
  have hq : (2 : ℝ) < q.exponent.toReal :=
    (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).2 hq2
  let r : FiniteLpExponent := targetSobolevSourceExponent d (by omega) q hq
  let Gr : HarmonicGradientGain d r n :=
    G.downgrade (targetSobolevSourceExponent_le_terminalLadder d hd q hq)
  simpa [n] using HarmonicGradientGain.upgrade (d := d) (by omega)
    (targetSobolevSourceExponent_relation d (by omega) q hq)
    (targetSobolevSourceExponent_lt_dimension d (by omega) q hq) Gr

/-- Every finite target exponent is reached in dimension at least three. -/
theorem nonempty_harmonicGradientGain_finiteTarget_of_three_le
    (d : ℕ) (hd : 3 ≤ d) (q : FiniteLpExponent) :
    Nonempty (Σ depth : ℕ, HarmonicGradientGain d q depth) := by
  by_cases hq2 : q.exponent ≤ 2
  · exact ⟨⟨0, (harmonicGradientGain_two_zero d).downgrade hq2⟩⟩
  · exact ⟨⟨((d - 1) / 2) + 1,
      harmonicGradientGain_finiteTarget_gt_two_of_three_le d hd q (lt_of_not_ge hq2)⟩⟩

/-- Vector-facing arbitrary finite target gain in dimensions at least three.
Its membership and bound are in the `HilbertVec.ofVec` representation used by
the stopping-time layer; all coordinate measurability is discharged inside
`fromScalar`. -/
noncomputable def harmonicEuclideanGradientGain_finiteTarget_gt_two_of_three_le
    (d : ℕ) (hd : 3 ≤ d) (q : FiniteLpExponent) (hq2 : 2 < q.exponent) :
    HarmonicEuclideanGradientGain d q (((d - 1) / 2) + 1) :=
  HarmonicEuclideanGradientGain.fromScalar
    (harmonicGradientGain_finiteTarget_gt_two_of_three_le d hd q hq2)

/-- Vector-facing normalized `L^q` gain for every target at or below `L²`. -/
noncomputable def harmonicEuclideanGradientGain_finiteTarget_le_two
    (d : ℕ) (q : FiniteLpExponent) (hq2 : q.exponent ≤ 2) :
    HarmonicEuclideanGradientGain d q 0 :=
  HarmonicEuclideanGradientGain.fromScalar
    ((harmonicGradientGain_two_zero d).downgrade hq2)

/-- Dimension-at-least-two public availability statement for the Euclidean
gain API.  It is deliberately `Nonempty Σ` because the depth is analytic data
of the construction, not a hypothesis that callers must provide. -/
theorem nonempty_harmonicEuclideanGradientGain_finiteTarget_of_two_le
    (d : ℕ) (hd : 2 ≤ d) (q : FiniteLpExponent) :
    Nonempty (Σ depth : ℕ, HarmonicEuclideanGradientGain d q depth) := by
  by_cases hq2 : q.exponent ≤ 2
  · exact ⟨⟨0, harmonicEuclideanGradientGain_finiteTarget_le_two d q hq2⟩⟩
  · by_cases hd2 : d = 2
    · subst d
      exact ⟨⟨1, harmonicEuclideanGradientGain_finiteTarget_gt_two_twoDim q
        (lt_of_not_ge hq2)⟩⟩
    · have hd3 : 3 ≤ d := by omega
      exact ⟨⟨((d - 1) / 2) + 1,
        harmonicEuclideanGradientGain_finiteTarget_gt_two_of_three_le d hd3 q
          (lt_of_not_ge hq2)⟩⟩

/-- One-dimensional finite-target carrier, obtained from the source theorem's
real bound only after the accompanying source-level `MemLp` witness has made
both ENNReal sides finite. -/
noncomputable def harmonicGradientGain_finiteTarget_oneDim
    (p : FiniteLpExponent) : HarmonicGradientGain 1 p 1 := by
  let C : ℝ := Classical.choose (exists_harmonic_gradCoord_finiteLp_bound_oneDim p)
  have hCspec := Classical.choose_spec (exists_harmonic_gradCoord_finiteLp_bound_oneDim p)
  have hCpos : 0 < C := hCspec.1
  have hC := hCspec.2
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_pos.mpr hCpos, ENNReal.ofReal_ne_top,
    ?_, ?_⟩
  · intro Q u h i
    fin_cases i
    simpa [centralDescendant_succ] using
      harmonic_gradCoord_memLp_centralDescendant_oneDim p Q u h
  · intro Q u h i
    fin_cases i
    have hleftmem := harmonic_gradCoord_memLp_centralDescendant_oneDim p Q u h
    have hrightmem := u.grad_memL2_normalizedCubeMeasure (0 : Fin 1)
    have hreal := hC Q u h
    have hscalar : MeasureTheory.eLpNorm (fun x => u.grad x 0) p.exponent
        (normalizedCubeMeasure (centralDescendant Q 1)) ≤
        ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x => u.grad x 0) 2
          (normalizedCubeMeasure Q) := by
      apply ennreal_le_of_toReal_le hleftmem.eLpNorm_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hrightmem.eLpNorm_ne_top)
      simpa [cubeLpNorm, centralDescendant_succ, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hCpos.le] using! hreal
    have hsingle : MeasureTheory.eLpNorm (fun x => u.grad x (0 : Fin 1)) 2
        (normalizedCubeMeasure Q) ≤ ∑ j : Fin 1,
          MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q) := by
      exact (by simpa only using (Finset.single_le_sum
        (s := Finset.univ) (f := fun j : Fin 1 =>
          MeasureTheory.eLpNorm (fun x => u.grad x j) 2 (normalizedCubeMeasure Q))
        (fun j _ => zero_le) (Finset.mem_univ (0 : Fin 1))))
    exact hscalar.trans (mul_le_mul_right hsingle _)

noncomputable def harmonicEuclideanGradientGain_finiteTarget_oneDim
    (p : FiniteLpExponent) : HarmonicEuclideanGradientGain 1 p 1 :=
  HarmonicEuclideanGradientGain.fromScalar (harmonicGradientGain_finiteTarget_oneDim p)

/-- All positive dimensions now expose the Euclidean finite-target carrier.
The depth is returned as construction data, not a caller hypothesis. -/
theorem nonempty_harmonicEuclideanGradientGain_finiteTarget_of_pos
    (d : ℕ) (hd : 0 < d) (q : FiniteLpExponent) :
    Nonempty (Σ depth : ℕ, HarmonicEuclideanGradientGain d q depth) := by
  by_cases hd1 : d = 1
  · subst d
    exact ⟨⟨1, harmonicEuclideanGradientGain_finiteTarget_oneDim q⟩⟩
  · exact nonempty_harmonicEuclideanGradientGain_finiteTarget_of_two_le d
      (by omega) q





end INTERNAL

end CubeCalderonZygmund

end

end Homogenization
