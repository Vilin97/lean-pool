/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicInteriorHessian
import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.LimitFiniteP
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.FiniteMeasureDowngrade
import LeanPool.CoarseGraining.Homogenization.Sobolev.MatchedPair.ScaledPoincare
import LeanPool.CoarseGraining.Homogenization.Besov.Duality.ProjectionLimit

/-! # Harmonic Gradient Two Dim -/

namespace Homogenization

open scoped ENNReal BigOperators

noncomputable section

namespace CubeCalderonZygmund

private noncomputable def finiteSobolevSourceExponent (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) < p.exponent) : FiniteLpExponent where
  exponent := ENNReal.ofReal (2 * p.exponent.toReal / (p.exponent.toReal + 2))
  one_lt := by
    rw [ENNReal.one_lt_ofReal]
    have hp' : 2 < p.exponent.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) p.lt_top.ne).2 hp
    have hden : 0 < p.exponent.toReal + 2 := by linarith
    calc
      1 = (p.exponent.toReal + 2) / (p.exponent.toReal + 2) := by field_simp
      _ < 2 * p.exponent.toReal / (p.exponent.toReal + 2) :=
        (div_lt_div_iff_of_pos_right hden).2 (by linarith)
  lt_top := ENNReal.ofReal_lt_top

private theorem finiteSobolevSourceExponent_le_two (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) < p.exponent) :
    (finiteSobolevSourceExponent p hp).exponent ≤ 2 := by
  rw [show (finiteSobolevSourceExponent p hp).exponent =
    ENNReal.ofReal (2 * p.exponent.toReal / (p.exponent.toReal + 2)) by rfl]
  norm_num
  have hden : 0 < p.exponent.toReal + 2 := by positivity
  exact (div_le_iff₀ hden).2 (by linarith)

private theorem finiteSobolevSourceExponent_relation (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) < p.exponent) :
    (p.exponent.toReal)⁻¹ =
      (finiteSobolevSourceExponent p hp).exponent.toReal⁻¹ - (2 : ℝ)⁻¹ := by
  rw [show (finiteSobolevSourceExponent p hp).exponent.toReal =
    2 * p.exponent.toReal / (p.exponent.toReal + 2) by
      simp [finiteSobolevSourceExponent]
      exact div_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) (by positivity)]
  have hp' : 0 < p.exponent.toReal := by
    have hp2 : 2 < p.exponent.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) p.lt_top.ne).2 hp
    linarith
  field_simp
  ring

private theorem eLpNorm_normalizedCubeMeasure_eq_scale_mul {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) (f : Vec d → ℝ) :
    MeasureTheory.eLpNorm f p.exponent (normalizedCubeMeasure Q) =
      (ENNReal.ofReal (cubeVolume Q)⁻¹ ^ (1 / p.exponent).toReal) *
        MeasureTheory.eLpNorm f p.exponent (volumeMeasureOn (openCubeSet Q)) := by
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact MeasureTheory.eLpNorm_smul_measure_of_ne_zero
    (ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (cubeVolume_pos Q))) f p.exponent _

private theorem eLpNorm_rawCubeMeasure_twoDim_eq_scale_mul_normalized
    (Q : TriadicCube 2) (p : FiniteLpExponent) (f : Vec 2 → ℝ) :
    MeasureTheory.eLpNorm f p.exponent (volumeMeasureOn (openCubeSet Q)) =
      (ENNReal.ofReal (cubeScaleFactor Q) ^ (2 / p.exponent.toReal)) *
        MeasureTheory.eLpNorm f p.exponent (normalizedCubeMeasure Q) := by
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have hcoeff :
      ENNReal.ofReal (cubeVolume Q)⁻¹ ^ (1 / p.exponent).toReal =
        (ENNReal.ofReal (cubeScaleFactor Q) ^ (2 / p.exponent.toReal))⁻¹ := by
    rw [cubeVolume_eq_scaleFactor_pow, ENNReal.ofReal_inv_of_pos (pow_pos hscale 2)]
    rw [ENNReal.ofReal_pow hscale.le, ENNReal.inv_rpow,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    simp only [one_div, ENNReal.toReal_inv]
    field_simp [ne_of_gt (ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne)]
    ring_nf
  have hnorm := eLpNorm_normalizedCubeMeasure_eq_scale_mul Q p f
  rw [hcoeff] at hnorm
  set a : ℝ≥0∞ := ENNReal.ofReal (cubeScaleFactor Q) ^ (2 / p.exponent.toReal)
  have ha0 : a ≠ 0 := ne_of_gt <|
    ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hscale) ENNReal.ofReal_ne_top
  have hat : a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg
    (by positivity) ENNReal.ofReal_ne_top
  rw [hnorm]
  calc
    _ = (a * a⁻¹) * MeasureTheory.eLpNorm f p.exponent
        (volumeMeasureOn (openCubeSet Q)) := by simp [ENNReal.mul_inv_cancel ha0 hat]
    _ = _ := by ring

private theorem cubeLpNorm_two_middleChild_le_three_mul (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) (hf : MeasureTheory.MemLp f 2 (normalizedCubeMeasure Q)) :
    cubeLpNorm ({ scale := Q.scale - 1, index := fun i => 3 * Q.index i } : TriadicCube 2)
        2 f ≤ 9 * cubeLpNorm Q 2 f := by
  let R : TriadicCube 2 := { scale := Q.scale - 1, index := fun i => 3 * Q.index i }
  have hR : R ∈ descendantsAtDepth Q 1 := by
    rw [mem_descendantsAtDepth_succ_iff]
    exact ⟨Q, by simp, by simpa [R] using middleChild_mem_childCubes Q⟩
  have hvol : cubeVolume Q / cubeVolume R = 9 := by
    have h := cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth hR
    have hcard : (descendantsAtDepth Q 1).card = 9 := by
      simp [descendantsAtDepth, childCubes_card]
    rw [hcard] at h
    norm_num at h
    calc
      cubeVolume Q / cubeVolume R = (9 * cubeVolume R) / cubeVolume R := by rw [h]
      _ = 9 := by field_simp [(cubeVolume_pos R).ne']
  have hsmul : ENNReal.ofReal (cubeVolume Q / cubeVolume R) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.2 (div_pos (cubeVolume_pos Q) (cubeVolume_pos R))
  have hle : MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure R) ≤
      9 * MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q) := by
    calc
      MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure R) =
          (ENNReal.ofReal (cubeVolume Q / cubeVolume R) ^ (1 / (2 : ℝ≥0∞)).toReal) •
            MeasureTheory.eLpNorm f 2 ((normalizedCubeMeasure Q).restrict (cubeSet R)) := by
        rw [normalizedCubeMeasure_descendant_eq_smul_restrict hR]
        exact MeasureTheory.eLpNorm_smul_measure_of_ne_zero hsmul f 2 _
      _ ≤ 9 * MeasureTheory.eLpNorm f 2 ((normalizedCubeMeasure Q).restrict (cubeSet R)) := by
        rw [hvol]
        norm_num
        apply mul_le_mul_left
        calc
          (9 : ℝ≥0∞) ^ (1 / (2 : ℝ)) ≤ (9 : ℝ≥0∞) ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 9 := by norm_num
      _ ≤ 9 * MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q) := by
        exact mul_le_mul_right (MeasureTheory.eLpNorm_mono_measure f
          MeasureTheory.Measure.restrict_le_self) _
  have hfinQ := hf.eLpNorm_ne_top
  have htop : 9 * MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hfinQ
  have hreal := ENNReal.toReal_mono htop hle
  simpa [R, cubeLpNorm, ENNReal.toReal_mul] using hreal

private theorem exists_harmonic_gradCoord_finiteLp_bound_twoDim_le_two
    (p : FiniteLpExponent) (hp : p.exponent ≤ 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) → ∀ i : Fin 2,
          cubeLpNorm
              ({ scale := Q.scale - 1, index := fun k => 3 * Q.index k } : TriadicCube 2)
              p.exponent (fun x => u.grad x i) ≤
            C * ∑ j : Fin 2, cubeLpNorm Q 2 (fun x => u.grad x j) := by
  refine ⟨9, by norm_num, ?_⟩
  intro Q u _ i
  let R : TriadicCube 2 := { scale := Q.scale - 1, index := fun k => 3 * Q.index k }
  have hR : R ∈ descendantsAtDepth Q 1 := by
    rw [mem_descendantsAtDepth_succ_iff]
    exact ⟨Q, by simp, by simpa [R] using middleChild_mem_childCubes Q⟩
  have hmemR : MeasureTheory.MemLp (fun x => u.grad x i) 2 (normalizedCubeMeasure R) :=
    u.grad_memL2_normalizedCubeMeasure_of_mem_descendantsAtDepth hR i
  have hdown := Homogenization.eLpNorm_normalizedCubeMeasure_downgrade_le R p hp
    (fun x => u.grad x i) hmemR.aestronglyMeasurable
  have hdownreal : cubeLpNorm R p.exponent (fun x => u.grad x i) ≤
      cubeLpNorm R 2 (fun x => u.grad x i) := by
    exact ENNReal.toReal_mono hmemR.eLpNorm_ne_top hdown
  have hchild := cubeLpNorm_two_middleChild_le_three_mul Q (fun x => u.grad x i)
    (u.grad_memL2_normalizedCubeMeasure i)
  calc
    cubeLpNorm R p.exponent (fun x => u.grad x i) ≤
        cubeLpNorm R 2 (fun x => u.grad x i) := hdownreal
    _ ≤ 9 * cubeLpNorm Q 2 (fun x => u.grad x i) := hchild
    _ ≤ 9 * ∑ j : Fin 2, cubeLpNorm Q 2 (fun x => u.grad x j) := by
      gcongr
      exact Finset.single_le_sum
        (fun j _ => cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (fun x => u.grad x j))
        (Finset.mem_univ i)

private theorem openCubeSet_eq_axisCube (Q : TriadicCube 2) :
    openCubeSet Q =
      axisCube (fun j => ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)
        (cubeScaleFactor Q) := by
  have hupper : ∀ j : Fin 2,
      ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + cubeScaleFactor Q =
        ((Q.index j : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by
    intro j
    ring
  ext x
  simp only [openCubeSet, axisCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ioo]
  simp_rw [hupper]

private theorem middleChildCube_subset_innerHalf (Q : TriadicCube 2) :
    cubeSet ({ scale := Q.scale - 1, index := fun i => 3 * Q.index i } : TriadicCube 2) ⊆
      scaledOpenCubeSet Q (1 / 2 : ℝ) := by
  intro x hx i
  have hscale : cubeScaleFactor
      ({ scale := Q.scale - 1, index := fun i => 3 * Q.index i } : TriadicCube 2) =
      cubeScaleFactor Q / 3 := by
    simpa using cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
  have hpos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have hx' := hx i
  rw [hscale] at hx'
  norm_num [Int.cast_mul] at hx'
  change |x i - cubeCenter Q i| < (1 / 2 : ℝ) * cubeRadius Q
  rw [cubeCenter, cubeRadius, abs_lt]
  constructor <;> nlinarith

private theorem highExponent_embedding_input (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) < p.exponent) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
        (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin 2),
        MeasureTheory.eLpNorm (fun x => u.grad x i) p.exponent
          (volumeMeasureOn (openCubeSet Q)) ≤
          (C : ℝ≥0∞) *
            ((∑ j : Fin 2,
                MeasureTheory.eLpNorm (fun x => H.hess i j x)
                  (finiteSobolevSourceExponent p hp).exponent
                  (volumeMeasureOn (openCubeSet Q))) +
              ENNReal.ofReal (cubeScaleFactor Q)⁻¹ *
                MeasureTheory.eLpNorm (fun x => u.grad x i)
                  (finiteSobolevSourceExponent p hp).exponent
                  (volumeMeasureOn (openCubeSet Q))) := by
  obtain ⟨C, hCpos, hC⟩ := cubeSobolevEmbedding_finiteLp (d := 2) (by norm_num)
    (finiteSobolevSourceExponent p hp) (by
      have hrlt : (finiteSobolevSourceExponent p hp).exponent.toReal < 2 := by
        rw [show (finiteSobolevSourceExponent p hp).exponent.toReal =
          2 * p.exponent.toReal / (p.exponent.toReal + 2) by
          simp [finiteSobolevSourceExponent]
          exact div_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) (by positivity)]
        have hp' : 0 < p.exponent.toReal := by
          have := (ENNReal.toReal_lt_toReal (by norm_num) p.lt_top.ne).2 hp
          exact lt_trans (by norm_num) this
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      exact hrlt)
  refine ⟨C, hCpos, ?_⟩
  intro Q
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let z : Vec 2 := fun j => ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have haxis : openCubeSet Q = axisCube z (cubeScaleFactor Q) := by
    simpa [z] using openCubeSet_eq_axisCube Q
  let P : Set (Vec 2) → Prop := fun U =>
    ∀ (u : H1Function U) (H : HasWeakHessianOn U u) (i : Fin 2),
      MeasureTheory.eLpNorm (fun x => u.grad x i) p.exponent (volumeMeasureOn U) ≤
        (C : ℝ≥0∞) *
          ((∑ j : Fin 2, MeasureTheory.eLpNorm (fun x => H.hess i j x)
              (finiteSobolevSourceExponent p hp).exponent (volumeMeasureOn U)) +
            ENNReal.ofReal (cubeScaleFactor Q)⁻¹ *
              MeasureTheory.eLpNorm (fun x => u.grad x i)
                (finiteSobolevSourceExponent p hp).exponent (volumeMeasureOn U))
  have haxisP : P (axisCube z (cubeScaleFactor Q)) := by
    intro v H i
    let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (axisCube z (cubeScaleFactor Q))) :=
      haxis ▸ inferInstance
    simpa [P, HasWeakHessianOn.gradCoordH1Function_apply,
      HasWeakHessianOn.gradCoordH1Function_grad_apply] using!
      (hC p (finiteSobolevSourceExponent_relation p hp) z (cubeScaleFactor Q) hscale
        ((H.gradCoordH1Function i).toW1pOfExponentLETwo
          (finiteSobolevSourceExponent p hp) (finiteSobolevSourceExponent_le_two p hp)))
  exact haxis.symm ▸ haxisP

private theorem highExponent_embedding_on_middleChild (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) < p.exponent) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
        (_h : WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0)) (i : Fin 2),
        ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)),
          uS.grad = u.grad ∧
            ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS,
              MeasureTheory.eLpNorm (fun x => u.grad x i) p.exponent
                (volumeMeasureOn (openCubeSet
                  ({ scale := Q.scale - 1, index := fun k => 3 * Q.index k } : TriadicCube 2))) ≤
                (C : ℝ≥0∞) *
                  ((∑ j : Fin 2,
                    MeasureTheory.eLpNorm (fun x => H.hess i j x)
                      (finiteSobolevSourceExponent p hp).exponent
                      (volumeMeasureOn (openCubeSet
                        ({ scale := Q.scale - 1, index := fun k => 3 * Q.index k } : TriadicCube 2)))) +
                    ENNReal.ofReal (cubeScaleFactor Q / 3)⁻¹ *
                      MeasureTheory.eLpNorm (fun x => u.grad x i)
                        (finiteSobolevSourceExponent p hp).exponent
                        (volumeMeasureOn (openCubeSet
                          ({ scale := Q.scale - 1, index := fun k => 3 * Q.index k } : TriadicCube 2)))) := by
  obtain ⟨C, hCpos, hC⟩ := highExponent_embedding_input p hp
  refine ⟨C, hCpos, ?_⟩
  intro Q u h i
  obtain ⟨A, hApos, hA⟩ := exists_harmonic_innerHalf_hessian_energy_bound 2
  obtain ⟨uS, huval, hugrad, H, hH⟩ :=
    hA Q u h
  let R : TriadicCube 2 := { scale := Q.scale - 1, index := fun k => 3 * Q.index k }
  have hRopen : IsOpen (openCubeSet R) := isOpen_openCubeSet R
  have hRsub : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ) :=
    (openCubeSet_subset_cubeSet R).trans (by simpa [R] using middleChildCube_subset_innerHalf Q)
  let uR := uS.restrict hRopen hRsub
  let HR := H.restrict hRopen hRsub
  refine ⟨uS, hugrad, H, ?_⟩
  have hraw := hC R uR HR i
  have hscale : cubeScaleFactor R = cubeScaleFactor Q / 3 := by
    simpa [R] using cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
  simpa [uR, HR, H1Function.restrict, HasWeakHessianOn.restrict, hugrad, hscale] using hraw

private theorem highExponent_normalized_embedding (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) < p.exponent) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
        (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin 2),
        MeasureTheory.eLpNorm (fun x => u.grad x i) p.exponent (normalizedCubeMeasure Q) ≤
          (C : ℝ≥0∞) *
            (ENNReal.ofReal (cubeScaleFactor Q) *
              ∑ j : Fin 2, MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
                (normalizedCubeMeasure Q) +
              MeasureTheory.eLpNorm (fun x => u.grad x i) 2 (normalizedCubeMeasure Q)) := by
  obtain ⟨C, hCpos, hC⟩ := highExponent_embedding_input p hp
  refine ⟨C, hCpos, ?_⟩
  intro Q u H i
  let r := finiteSobolevSourceExponent p hp
  let a : ℝ≥0∞ := ENNReal.ofReal (cubeScaleFactor Q)
  let ap : ℝ≥0∞ := a ^ (2 / p.exponent.toReal)
  let ar : ℝ≥0∞ := a ^ (2 / r.exponent.toReal)
  have hapos : 0 < a := ENNReal.ofReal_pos.mpr (by
    simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale)
  have ha0 : a ≠ 0 := ne_of_gt hapos
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hap0 : ap ≠ 0 := ne_of_gt (ENNReal.rpow_pos hapos hat)
  have hapt : ap ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hat
  have hpow : 2 / r.exponent.toReal = 2 / p.exponent.toReal + 1 := by
    have hrel := finiteSobolevSourceExponent_relation p hp
    dsimp [r]
    calc
      2 / (finiteSobolevSourceExponent p hp).exponent.toReal =
          2 * (finiteSobolevSourceExponent p hp).exponent.toReal⁻¹ := by ring
      _ = 2 * (p.exponent.toReal⁻¹ + (2 : ℝ)⁻¹) := by
        congr 1
        linarith
      _ = 2 / p.exponent.toReal + 1 := by ring
  have har : ar = ap * a := by
    dsimp [ar, ap]
    rw [hpow, ENNReal.rpow_add _ _ ha0 hat]
    norm_num
  have hinv : ENNReal.ofReal (cubeScaleFactor Q)⁻¹ = a⁻¹ := by
    dsimp [a]
    exact ENNReal.ofReal_inv_of_pos (by
      simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale)
  have hraw := hC Q u H i
  rw [eLpNorm_rawCubeMeasure_twoDim_eq_scale_mul_normalized Q p] at hraw
  change ap * MeasureTheory.eLpNorm (fun x => u.grad x i) p.exponent
      (normalizedCubeMeasure Q) ≤
    (C : ℝ≥0∞) *
      ((∑ j : Fin 2, MeasureTheory.eLpNorm (fun x => H.hess i j x) r.exponent
        (volumeMeasureOn (openCubeSet Q))) +
        ENNReal.ofReal (cubeScaleFactor Q)⁻¹ *
          MeasureTheory.eLpNorm (fun x => u.grad x i) r.exponent
            (volumeMeasureOn (openCubeSet Q))) at hraw
  simp_rw [eLpNorm_rawCubeMeasure_twoDim_eq_scale_mul_normalized Q r] at hraw
  rw [hinv] at hraw
  have hraw' : ap * MeasureTheory.eLpNorm (fun x => u.grad x i) p.exponent
      (normalizedCubeMeasure Q) ≤ (C : ℝ≥0∞) *
        ((∑ j : Fin 2, ar * MeasureTheory.eLpNorm (fun x => H.hess i j x) r.exponent
          (normalizedCubeMeasure Q)) +
          a⁻¹ * (ar * MeasureTheory.eLpNorm (fun x => u.grad x i) r.exponent
            (normalizedCubeMeasure Q))) := by
    simpa [a, ap, ar] using hraw
  rw [har] at hraw'
  have hrow : ∀ j : Fin 2,
      MeasureTheory.eLpNorm (fun x => H.hess i j x) r.exponent (normalizedCubeMeasure Q) ≤
        MeasureTheory.eLpNorm (fun x => H.hess i j x) 2 (normalizedCubeMeasure Q) := by
    intro j
    apply Homogenization.eLpNorm_normalizedCubeMeasure_downgrade_le Q r
      (finiteSobolevSourceExponent_le_two p hp)
    exact (memL2On_openCubeSet_normalizedCubeMeasure (H.hess_memL2 i j)).aestronglyMeasurable
  have hgrad : MeasureTheory.eLpNorm (fun x => u.grad x i) r.exponent (normalizedCubeMeasure Q) ≤
      MeasureTheory.eLpNorm (fun x => u.grad x i) 2 (normalizedCubeMeasure Q) := by
    apply Homogenization.eLpNorm_normalizedCubeMeasure_downgrade_le Q r
      (finiteSobolevSourceExponent_le_two p hp)
    exact (u.grad_memL2_normalizedCubeMeasure i).aestronglyMeasurable
  apply (ENNReal.mul_le_mul_iff_right hap0 hapt).mp
  calc
    ap * MeasureTheory.eLpNorm (fun x => u.grad x i) p.exponent
        (normalizedCubeMeasure Q) ≤
        (C : ℝ≥0∞) *
          ((∑ j : Fin 2, ap * a * MeasureTheory.eLpNorm (fun x => H.hess i j x)
            r.exponent (normalizedCubeMeasure Q)) +
            a⁻¹ * (ap * a) * MeasureTheory.eLpNorm (fun x => u.grad x i)
              r.exponent (normalizedCubeMeasure Q)) := by simpa [mul_assoc] using hraw'
    _ ≤ (C : ℝ≥0∞) *
          ((∑ j : Fin 2, ap * a * MeasureTheory.eLpNorm (fun x => H.hess i j x)
            2 (normalizedCubeMeasure Q)) +
            a⁻¹ * (ap * a) * MeasureTheory.eLpNorm (fun x => u.grad x i)
              2 (normalizedCubeMeasure Q)) := by
      gcongr
      · exact hrow _
    _ = ap * ((C : ℝ≥0∞) *
          (a * ∑ j : Fin 2, MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
              (normalizedCubeMeasure Q) +
            MeasureTheory.eLpNorm (fun x => u.grad x i) 2 (normalizedCubeMeasure Q))) := by
      have hcancel : a⁻¹ * (ap * a) = ap := by
        calc
          a⁻¹ * (ap * a) = ap * (a⁻¹ * a) := by ring
          _ = ap := by rw [ENNReal.inv_mul_cancel ha0 hat, mul_one]
      rw [hcancel]
      rw [← Finset.mul_sum]
      ring

private theorem raw_eLpNorm_two_toReal_eq_scale_mul_cubeLpNorm
    (Q : TriadicCube 2) (f : Vec 2 → ℝ)
    (hf : MeasureTheory.MemLp f 2 (normalizedCubeMeasure Q)) :
    (MeasureTheory.eLpNorm f 2 (volumeMeasureOn (openCubeSet Q))).toReal =
      cubeScaleFactor Q * cubeLpNorm Q 2 f := by
  have hraw := eLpNorm_rawCubeMeasure_twoDim_eq_scale_mul_normalized Q
    FiniteLpExponent.two f
  have htop : ENNReal.ofReal (cubeScaleFactor Q) *
      MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  have hraw' : MeasureTheory.eLpNorm f 2 (volumeMeasureOn (openCubeSet Q)) =
      ENNReal.ofReal (cubeScaleFactor Q) *
        MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q) := by
    simpa using hraw
  have hreal := congrArg ENNReal.toReal hraw'
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
    simpa [cubeScaleFactor] using le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale))] at hreal
  simpa [cubeLpNorm] using hreal

private theorem hessianCoordL2NormSum_eq_sum_raw_eLpNorm
    {U : Set (Vec 2)} {u : H1Function U} (H : HasWeakHessianOn U u) :
    H.hessianCoordL2NormSum =
      ∑ i : Fin 2, ∑ j : Fin 2,
        (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2 (volumeMeasureOn U)).toReal := by
  unfold HasWeakHessianOn.hessianCoordL2NormSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [HasWeakHessianOn.hessCoordToScalarL2, Homogenization.toScalarL2,
    MeasureTheory.Lp.norm_toLp]

private theorem highExponent_normalized_embedding_real (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) < p.exponent) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
        (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin 2),
        cubeLpNorm Q p.exponent (fun x => u.grad x i) ≤
          C *
            (cubeScaleFactor Q *
              ∑ j : Fin 2, cubeLpNorm Q 2 (fun x => H.hess i j x) +
              cubeLpNorm Q 2 (fun x => u.grad x i)) := by
  obtain ⟨C, hCpos, hC⟩ := highExponent_normalized_embedding p hp
  refine ⟨C, mod_cast hCpos, ?_⟩
  intro Q u H i
  have hh := hC Q u H i
  have hsum : ∑ j : Fin 2, MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
      (normalizedCubeMeasure Q) ≠ ∞ := ENNReal.sum_ne_top.2 fun j _ =>
    (memL2On_openCubeSet_normalizedCubeMeasure (H.hess_memL2 i j)).eLpNorm_ne_top
  have hfirst : ENNReal.ofReal (cubeScaleFactor Q) *
      ∑ j : Fin 2, MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
        (normalizedCubeMeasure Q) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum
  have hgradtop : MeasureTheory.eLpNorm (fun x => u.grad x i) 2
      (normalizedCubeMeasure Q) ≠ ∞ :=
    (u.grad_memL2_normalizedCubeMeasure i).eLpNorm_ne_top
  have htop : (C : ℝ≥0∞) *
      (ENNReal.ofReal (cubeScaleFactor Q) *
        ∑ j : Fin 2, MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
          (normalizedCubeMeasure Q) +
        MeasureTheory.eLpNorm (fun x => u.grad x i) 2 (normalizedCubeMeasure Q)) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.coe_ne_top
    exact ENNReal.add_ne_top.2 ⟨hfirst, hgradtop⟩
  have hreal := ENNReal.toReal_mono htop hh
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_add,
    ENNReal.toReal_mul, ENNReal.toReal_sum] at hreal
  · rw [ENNReal.toReal_ofReal (by
      simpa [cubeScaleFactor] using le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale))] at hreal
    simpa [cubeLpNorm, mul_add, Finset.mul_sum] using hreal
  · intro j _
    exact (memL2On_openCubeSet_normalizedCubeMeasure (H.hess_memL2 i j)).eLpNorm_ne_top
  · exact hfirst
  · exact hgradtop

private theorem exists_harmonic_gradCoord_finiteLp_bound_twoDim_gt_two
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) < p.exponent) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) → ∀ i : Fin 2,
          cubeLpNorm
              ({ scale := Q.scale - 1, index := fun k => 3 * Q.index k } : TriadicCube 2)
              p.exponent (fun x => u.grad x i) ≤
            C * ∑ j : Fin 2, cubeLpNorm Q 2 (fun x => u.grad x j) := by
  obtain ⟨B, hBpos, hB⟩ := highExponent_normalized_embedding_real p hp
  obtain ⟨A, hApos, hA⟩ := exists_harmonic_innerHalf_hessian_energy_bound 2
  refine ⟨B * (A + 9), mul_pos hBpos (by linarith), ?_⟩
  intro Q u h i
  let R : TriadicCube 2 := { scale := Q.scale - 1, index := fun k => 3 * Q.index k }
  obtain ⟨uS, huval, hugrad, H, hH⟩ := hA Q u h
  have hRopen : IsOpen (openCubeSet R) := isOpen_openCubeSet R
  have hRsub : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ) :=
    (openCubeSet_subset_cubeSet R).trans (by simpa [R] using middleChildCube_subset_innerHalf Q)
  let HR := H.restrict hRopen hRsub
  let uR := uS.restrict hRopen hRsub
  have hscaleR : cubeScaleFactor R = cubeScaleFactor Q / 3 := by
    simpa [R] using cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
  have hHR := hB R uR HR i
  have hhigh : cubeLpNorm R p.exponent (fun x => u.grad x i) ≤
      B * (cubeScaleFactor R * ∑ j : Fin 2, cubeLpNorm R 2 (fun x => H.hess i j x) +
        cubeLpNorm R 2 (fun x => u.grad x i)) := by
    simpa [uR, HR, H1Function.restrict, HasWeakHessianOn.restrict, hugrad] using hHR
  have hrawrow : ∀ j : Fin 2,
      (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2 (volumeMeasureOn (openCubeSet R))).toReal ≤
        (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
          (volumeMeasureOn (scaledOpenCubeSet Q (1 / 2 : ℝ)))).toReal := by
    intro j
    apply ENNReal.toReal_mono (H.hess_memL2 i j).eLpNorm_ne_top
    exact MeasureTheory.eLpNorm_mono_measure _
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hRsub)
  have hrawsum : ∑ j : Fin 2,
      (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2 (volumeMeasureOn (openCubeSet R))).toReal ≤
      H.hessianCoordL2NormSum := by
    calc
      _ ≤ ∑ j : Fin 2,
          (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
            (volumeMeasureOn (scaledOpenCubeSet Q (1 / 2 : ℝ)))).toReal :=
        Finset.sum_le_sum fun j _ => hrawrow j
      _ ≤ H.hessianCoordL2NormSum := by
        rw [hessianCoordL2NormSum_eq_sum_raw_eLpNorm H]
        show (∑ j : Fin 2,
          (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
            (volumeMeasureOn (scaledOpenCubeSet Q (1 / 2 : ℝ)))).toReal) ≤
          ∑ k : Fin 2, ∑ j : Fin 2,
            (MeasureTheory.eLpNorm (fun x => H.hess k j x) 2
              (volumeMeasureOn (scaledOpenCubeSet Q (1 / 2 : ℝ)))).toReal
        exact Finset.single_le_sum
          (s := Finset.univ)
          (f := fun k : Fin 2 => ∑ j : Fin 2,
            (MeasureTheory.eLpNorm (fun x => H.hess k j x) 2
              (volumeMeasureOn (scaledOpenCubeSet Q (1 / 2 : ℝ)))).toReal)
          (fun k _ => Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg)
          (Finset.mem_univ i)
  have hRmem : ∀ j : Fin 2,
      MeasureTheory.MemLp (fun x => H.hess i j x) 2 (normalizedCubeMeasure R) := by
    intro j
    exact memL2On_openCubeSet_normalizedCubeMeasure (HR.hess_memL2 i j)
  have hhess : cubeScaleFactor R * ∑ j : Fin 2, cubeLpNorm R 2 (fun x => H.hess i j x) ≤
      A * ∑ j : Fin 2, cubeLpNorm Q 2 (fun x => u.grad x j) := by
    calc
      _ = ∑ j : Fin 2,
          (MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
            (volumeMeasureOn (openCubeSet R))).toReal := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          exact (raw_eLpNorm_two_toReal_eq_scale_mul_cubeLpNorm R _ (hRmem j)).symm
      _ ≤ H.hessianCoordL2NormSum := hrawsum
      _ ≤ A * (cubeScaleFactor Q)⁻¹ * u.gradientCoordL2NormSum := hH
      _ = A * ∑ j : Fin 2, cubeLpNorm Q 2 (fun x => u.grad x j) := by
        rw [gradientCoordL2NormSum_eq_sum_eLpNorm]
        simp_rw [raw_eLpNorm_two_toReal_eq_scale_mul_cubeLpNorm Q _
          (u.grad_memL2_normalizedCubeMeasure _)]
        have hL : 0 < cubeScaleFactor Q := by
          simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
        field_simp [hL.ne']
        rw [Finset.mul_sum]
  have hgrad := cubeLpNorm_two_middleChild_le_three_mul Q (fun x => u.grad x i)
    (u.grad_memL2_normalizedCubeMeasure i)
  have hgradsum : cubeLpNorm R 2 (fun x => u.grad x i) ≤
      9 * ∑ j : Fin 2, cubeLpNorm Q 2 (fun x => u.grad x j) := by
    calc
      _ ≤ 9 * cubeLpNorm Q 2 (fun x => u.grad x i) := by simpa [R] using hgrad
      _ ≤ _ := by
        gcongr
        exact Finset.single_le_sum
          (fun j _ => cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (fun x => u.grad x j))
          (Finset.mem_univ i)
  calc
    cubeLpNorm R p.exponent (fun x => u.grad x i) ≤
        B * (cubeScaleFactor R * ∑ j : Fin 2, cubeLpNorm R 2 (fun x => H.hess i j x) +
          cubeLpNorm R 2 (fun x => u.grad x i)) := hhigh
    _ ≤ B * ((A + 9) * ∑ j : Fin 2, cubeLpNorm Q 2 (fun x => u.grad x j)) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hBpos)
      calc
        _ ≤ A * ∑ j : Fin 2, cubeLpNorm Q 2 (fun x => u.grad x j) +
            9 * ∑ j : Fin 2, cubeLpNorm Q 2 (fun x => u.grad x j) :=
          add_le_add hhess hgradsum
        _ = (A + 9) * ∑ j : Fin 2, cubeLpNorm Q 2 (fun x => u.grad x j) := by ring
    _ = B * (A + 9) * ∑ j : Fin 2, cubeLpNorm Q 2 (fun x => u.grad x j) := by ring

/-- In dimension two, a harmonic function gains every finite `Lp` exponent for each
gradient coordinate on the central child cube, controlled by the parent-cube normalized
`L²` gradient energy. -/
theorem exists_harmonic_gradCoord_finiteLp_bound_twoDim (p : FiniteLpExponent) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) → ∀ i : Fin 2,
          cubeLpNorm
              ({ scale := Q.scale - 1, index := fun k => 3 * Q.index k } : TriadicCube 2)
              p.exponent (fun x => u.grad x i) ≤
            C * ∑ j : Fin 2, cubeLpNorm Q 2 (fun x => u.grad x j) := by
  by_cases hp : p.exponent ≤ 2
  · exact exists_harmonic_gradCoord_finiteLp_bound_twoDim_le_two p hp
  · have hp' : (2 : ℝ≥0∞) < p.exponent := lt_of_not_ge hp
    exact exists_harmonic_gradCoord_finiteLp_bound_twoDim_gt_two p hp'

end CubeCalderonZygmund

end

end Homogenization
