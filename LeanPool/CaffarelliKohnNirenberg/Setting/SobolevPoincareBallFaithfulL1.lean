/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBallWeak
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBridge
public import LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1Ball
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareConstantFinite
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareConstantPos
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.W1p.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.GradientNorm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.NormTriangle
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.BallMemLp
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.LpConvergence
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Tactic.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBallFaithfulL1Local

/-!
# Approximation lemmas for Sobolev–Poincaré on Euclidean balls

These lemmas transfer smooth Euclidean-ball Poincaré estimates to W¹,¹ data.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

private theorem euclideanBall_eq_vec3Ball_faithful {x₀ : Vec3} {r : ℝ}
    (hr : 0 < r) : euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

private lemma w1p_euclideanBall_poincareL1_faithful_hDunion_1 :
    ∀ (x₀ : Vec3) {r : ℝ},
      0 < r →
        let B : Set Vec3 := euclideanBall x₀ r;
        ∀ (s : ℕ → ℝ),
          let D : ℕ → Set Vec3 := fun n => euclideanBall x₀ (s n);
          (∀ (v : Vec3), vecEuclideanNorm v = vec3EuclideanNorm v) →
            (∀ (n : ℕ), 0 < s n) → (∀ (n : ℕ), s n < r) → Tendsto s atTop (𝓝 r) → ⋃ n, D n = B
    := by
  intro x₀ r hr B s D hnormEq hspos hslt hstendsto
  apply Set.Subset.antisymm
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨n, hxn⟩
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt (hspos n)).1 hxn).trans_le
      (hslt n).le
  · intro x hx
    have hxnorm : vecEuclideanNorm (x - x₀) < r :=
      (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx
    have hxnorm3 : vec3EuclideanNorm (x - x₀) < r := by
      simpa [hnormEq] using hxnorm
    have hev : ∀ᶠ n in atTop, vec3EuclideanNorm (x - x₀) < s n :=
      hstendsto.eventually (Ioi_mem_nhds hxnorm3)
    rcases hev.exists with ⟨n, hn⟩
    have hn' : vecEuclideanNorm (x - x₀) < s n := by
      simpa [hnormEq] using hn
    exact Set.mem_iUnion.2 ⟨n,
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (hspos n)).2 hn'⟩

private lemma w1p_euclideanBall_poincareL1_faithful_hleft_2 :
    ∀ (x₀ : Vec3) {r : ℝ},
      0 < r →
        ∀ (u : W1pFunction (euclideanBall x₀ r) 1),
          let B : Set Vec3 := euclideanBall x₀ r;
          ∀ (s : ℕ → ℝ),
            let D : ℕ → Set Vec3 := fun n => euclideanBall x₀ (s n);
            ∀ (a₀ : ℝ) (a : ℕ → ℝ),
              (∀ (n : ℕ), 0 < s n) →
                (∀ (n : ℕ), s n < r) →
                  @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace
                      (u.toFun (U := euclideanBall x₀ r)) (Measure.restrict volume B) →
                    Tendsto (β := ℝ)
                        (fun (n : ℕ) =>
                          @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                            (Measure.restrict volume (D n)) fun x =>
                            |u.toFun (U := euclideanBall x₀ r) x - a₀|)
                        atTop
                        (𝓝
                          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                            (Measure.restrict volume B) fun x =>
                            |u.toFun (U := euclideanBall x₀ r) x - a₀|)) →
                      Tendsto (fun (n : ℕ) => ENNReal.toReal (volume (D n)) * |a n - a₀|) atTop
                          (𝓝 0) →
                        Tendsto (β := ℝ)
                          (fun (n : ℕ) =>
                            @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                              (Measure.restrict volume (D n)) fun x =>
                              |u.toFun (U := euclideanBall x₀ r) x - a n|)
                          atTop
                          (𝓝
                            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                              (Measure.restrict volume B) fun x =>
                              |u.toFun (U := euclideanBall x₀ r) x - a₀|))
    := by
  intro x₀ r hr u B s D a₀ a hspos hslt huInt hJ hvolavg
  have hbound (n : ℕ) : |(∫ x in D n, |u.toFun x - a n| ∂volume) -
      ∫ x in D n, |u.toFun x - a₀| ∂volume| ≤
      (volume (D n)).toReal * |a n - a₀| := by
    let μn : Measure Vec3 := volume.restrict (D n)
    have hDvol : volume (D n) < ∞ := by
      change volume (euclideanBall x₀ (s n)) < ∞
      rw [euclideanBall_eq_vec3Ball_faithful (hspos n), volume_vec3Ball_eq]
      finiteness
    let _ : IsFiniteMeasure μn := by
      refine ⟨?_⟩
      simpa [μn, Measure.restrict_apply_univ] using hDvol
    have huDn : Integrable u.toFun μn := huInt.mono_measure
      (Measure.restrict_mono_set volume (by
        intro x hx
        have hxB : x ∈ B := by
          exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
            ((mem_euclideanBall_iff_vecEuclideanNorm_lt (hspos n)).1 hx |>.trans_le
              (hslt n).le)
        exact hxB))
    have hIa : Integrable (fun x => |u.toFun x - a n|) μn :=
      (huDn.sub (integrable_const (a n))).abs
    have hI₀ : Integrable (fun x => |u.toFun x - a₀|) μn :=
      (huDn.sub (integrable_const a₀)).abs
    have hC : Integrable (fun _ : Vec3 => |a n - a₀|) μn := integrable_const _
    have hpoint₁ (x : Vec3) : |u.toFun x - a n| ≤
        |u.toFun x - a₀| + |a n - a₀| := by
      calc
        |u.toFun x - a n| = |(u.toFun x - a₀) + (a₀ - a n)| := by
          congr 1
          ring
        _ ≤ |u.toFun x - a₀| + |a₀ - a n| := abs_add_le _ _
        _ = |u.toFun x - a₀| + |a n - a₀| := by
          congr 1
          exact abs_sub_comm _ _
    have hpoint₂ (x : Vec3) : |u.toFun x - a₀| ≤
        |u.toFun x - a n| + |a n - a₀| := by
      calc
        |u.toFun x - a₀| = |(u.toFun x - a n) + (a n - a₀)| := by
          congr 1
          ring
        _ ≤ |u.toFun x - a n| + |a n - a₀| := abs_add_le _ _
    have hconst : ∫ x, |a n - a₀| ∂μn =
        |a n - a₀| * (volume (D n)).toReal := by
      rw [integral_const]
      simp [μn, Measure.real_def, mul_comm]
    have hupper : (∫ x, |u.toFun x - a n| ∂μn) ≤
        (∫ x, |u.toFun x - a₀| ∂μn) +
          |a n - a₀| * (volume (D n)).toReal := by
      have h := integral_mono_ae hIa (hI₀.add hC)
        (ae_of_all μn hpoint₁)
      calc
        (∫ x, |u.toFun x - a n| ∂μn) ≤
            ∫ x, |u.toFun x - a₀| + |a n - a₀| ∂μn := h
        _ = (∫ x, |u.toFun x - a₀| ∂μn) +
            ∫ x, |a n - a₀| ∂μn := integral_add hI₀ hC
        _ = _ := by rw [hconst]
    have hlower : (∫ x, |u.toFun x - a₀| ∂μn) ≤
        (∫ x, |u.toFun x - a n| ∂μn) +
          |a n - a₀| * (volume (D n)).toReal := by
      have h := integral_mono_ae hI₀ (hIa.add hC)
        (ae_of_all μn hpoint₂)
      calc
        (∫ x, |u.toFun x - a₀| ∂μn) ≤
            ∫ x, |u.toFun x - a n| + |a n - a₀| ∂μn := h
        _ = (∫ x, |u.toFun x - a n| ∂μn) +
            ∫ x, |a n - a₀| ∂μn := integral_add hIa hC
        _ = _ := by rw [hconst]
    have hEq₁ : ∫ x, |u.toFun x - a n| ∂μn =
        ∫ x in D n, |u.toFun x - a n| ∂volume := rfl
    have hEq₂ : ∫ x, |u.toFun x - a₀| ∂μn =
        ∫ x in D n, |u.toFun x - a₀| ∂volume := rfl
    rw [← hEq₁, ← hEq₂]
    exact (abs_le).2 ⟨
      (neg_le_sub_iff_le_add).2 (by simpa [mul_comm] using hlower),
      (sub_le_iff_le_add).2 (by simpa [add_comm, mul_comm] using hupper)⟩
  have hdiff : Tendsto (fun n =>
      (∫ x in D n, |u.toFun x - a n| ∂volume) -
        ∫ x in D n, |u.toFun x - a₀| ∂volume) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hvolavg
      (Eventually.of_forall fun _ => norm_nonneg _)
    filter_upwards [] with n
    simpa [Real.norm_eq_abs] using hbound n
  have hsum := hdiff.add hJ
  have hfun : (fun n => ∫ x in D n, |u.toFun x - a n| ∂volume) =
      (fun n => (∫ x in D n, |u.toFun x - a n| ∂volume -
        ∫ x in D n, |u.toFun x - a₀| ∂volume) +
        ∫ x in D n, |u.toFun x - a₀| ∂volume) := by
    funext n
    ring
  rw [hfun]
  simpa using hsum

/-- W¹,¹ Poincaré on an arbitrary Euclidean ball, with the volume-scaled constant. -/
theorem w1p_euclideanBall_poincareL1_faithful
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r)
    (u : W1pFunction (euclideanBall x₀ r) 1) :
    ∫ x in euclideanBall x₀ r,
        |u.toFun x - average (volume.restrict (euclideanBall x₀ r)) u.toFun|
          ∂volume ≤
      poincareSobolevL1Constant.toReal *
        (volume (euclideanBall x₀ r)).toReal ^ (1 / 3 : ℝ) *
          ∫ x in euclideanBall x₀ r, w1pGradientNorm u x ∂volume := by
  classical
  let B : Set Vec3 := euclideanBall x₀ r
  let ρ : ℕ → ℝ := fun n => 1 - ((n : ℝ) + 2)⁻¹
  let s : ℕ → ℝ := fun n => r * ρ n
  let D : ℕ → Set Vec3 := fun n => euclideanBall x₀ (s n)
  let a₀ : ℝ := average (volume.restrict B) u.toFun
  let a : ℕ → ℝ := fun n => average (volume.restrict (D n)) u.toFun
  let G : Vec3 → ℝ := w1pGradientNorm u
  have hnormEq (v : Vec3) : vecEuclideanNorm v = vec3EuclideanNorm v := by
    simp [vecEuclideanNorm, vec3EuclideanNorm, vecNormSq, vecDot, pow_two]
  have hBopen : IsOpen B := by
    change IsOpen (euclideanBall x₀ r)
    change IsOpen {x : Vec3 | euclideanSqDist x x₀ < r ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hBmeas : MeasurableSet B := hBopen.measurableSet
  have hBvol : volume B < ∞ := by
    change volume (euclideanBall x₀ r) < ∞
    rw [euclideanBall_eq_vec3Ball_faithful hr, volume_vec3Ball_eq]
    finiteness
  let _ : IsFiniteMeasure (volume.restrict B) := by
    refine ⟨?_⟩
    simpa [Measure.restrict_apply_univ] using hBvol
  have hBvolpos : 0 < volume B := by
    change 0 < volume (euclideanBall x₀ r)
    rw [euclideanBall_eq_vec3Ball_faithful hr, volume_vec3Ball_eq]
    positivity
  have hBrealpos : 0 < (volume B).toReal := ENNReal.toReal_pos hBvolpos.ne' hBvol.ne
  have hρpos (n : ℕ) : 0 < ρ n := by
    dsimp [ρ]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn : (1 : ℝ) < (n : ℝ) + 2 := by linarith only [hn0]
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hn)
  have hρlt (n : ℕ) : ρ n < 1 := by
    dsimp [ρ]
    have hn : 0 < ((n : ℝ) + 2)⁻¹ := by positivity
    linarith only [hn]
  have hρmono : Monotone ρ := by
    intro n m hnm
    dsimp [ρ]
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hden : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by linarith only [hnm']
    have hinv : ((m : ℝ) + 2)⁻¹ ≤ ((n : ℝ) + 2)⁻¹ :=
      by simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hden
    linarith only [hinv]
  have hspos (n : ℕ) : 0 < s n := by
    dsimp [s]
    exact mul_pos hr (hρpos n)
  have hslt (n : ℕ) : s n < r := by
    dsimp [s]
    simpa only [mul_one] using (mul_lt_mul_of_pos_left (hρlt n) hr)
  have hρtendsto : Tendsto ρ atTop (nhds 1) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
      simpa only [add_comm] using
        (tendsto_atTop_add_const_left atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hden
    simpa [ρ] using (tendsto_const_nhds.sub hinv)
  have hstendsto : Tendsto s atTop (nhds r) := by
    simpa [s] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (nhds r)).mul hρtendsto
  have hsmono : Monotone s := by
    intro n m hnm
    exact mul_le_mul_of_nonneg_left (hρmono hnm) hr.le
  have hDmono : Monotone D := by
    intro n m hnm x hx
    have hx' : vecEuclideanNorm (x - x₀) < s n :=
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (hspos n)).1 hx
    exact (mem_euclideanBall_iff_vecEuclideanNorm_lt (hspos m)).2
      (lt_of_lt_of_le hx' (hsmono hnm))
  have hDopen (n : ℕ) : IsOpen (D n) := by
    change IsOpen (euclideanBall x₀ (s n))
    change IsOpen {x : Vec3 | euclideanSqDist x x₀ < (s n) ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hDunion := @w1p_euclideanBall_poincareL1_faithful_hDunion_1 x₀ r hr s hnormEq hspos hslt
    hstendsto
  have huB : MemLp u.toFun 1 (volume.restrict B) := by
    change MemLp u.toFun 1 (volumeOn B)
    exact u.memLp
  have huInt : Integrable u.toFun (volume.restrict B) :=
    memLp_one_iff_integrable.mp huB
  have hnum : Tendsto (fun n => ∫ x in D n, u.toFun x ∂volume) atTop
      (nhds (∫ x in B, u.toFun x ∂volume)) := by
    have huUnion : IntegrableOn u.toFun (⋃ n, D n) volume := by
      rw [hDunion]
      exact huInt
    have h := tendsto_setIntegral_of_monotone (f := u.toFun)
      (fun n => (hDopen n).measurableSet) hDmono huUnion
    rw [hDunion] at h
    simpa [D, B] using h
  have hvol : Tendsto (fun n => (volume (D n)).toReal) atTop
      (nhds (volume B).toReal) := by
    have h := tendsto_measure_iUnion_atTop (μ := volume) hDmono
    rw [hDunion] at h
    exact (ENNReal.tendsto_toReal hBvol.ne).comp h
  have havg : Tendsto a atTop (nhds a₀) := by
    have hinv : Tendsto (fun n => (volume (D n)).toReal⁻¹) atTop
        (nhds (volume B).toReal⁻¹) := (tendsto_inv₀ hBrealpos.ne').comp hvol
    have hmul := hinv.mul hnum
    have hformula (n : ℕ) : a n = (volume (D n)).toReal⁻¹ *
        ∫ x in D n, u.toFun x ∂volume := by
      change (⨍ x in D n, u.toFun x ∂volume) = _
      rw [MeasureTheory.setAverage_eq]
      simp [Measure.real_def]
    have hformulaB : a₀ = (volume B).toReal⁻¹ *
        ∫ x in B, u.toFun x ∂volume := by
      change (⨍ x in B, u.toFun x ∂volume) = _
      rw [MeasureTheory.setAverage_eq]
      simp [Measure.real_def]
    rw [show a = fun n => (volume (D n)).toReal⁻¹ *
        ∫ x in D n, u.toFun x ∂volume by funext n; exact hformula n, hformulaB]
    exact hmul
  have hGmem : MemLp G 1 (volume.restrict B) := by
    change MemLp (fun x => ∑ i : Fin 3, |u.grad x i|) 1 (volume.restrict B)
    exact memLp_finsetSum (p := (1 : ℝ≥0∞)) (μ := volume.restrict B)
      Finset.univ (fun i _ => (u.grad_memLp i).abs)
  have hGint : Integrable G (volume.restrict B) :=
    memLp_one_iff_integrable.mp hGmem
  have hGnonneg (x : Vec3) : 0 ≤ G x := by
    simp [G, w1pGradientNorm, Finset.sum_nonneg]
  have hGset : Tendsto (fun n => ∫ x in D n, G x ∂volume) atTop
      (nhds (∫ x in B, G x ∂volume)) := by
    have hGunion : IntegrableOn G (⋃ n, D n) volume := by
      rw [hDunion]
      exact hGint
    have h := tendsto_setIntegral_of_monotone (f := G)
      (fun n => (hDopen n).measurableSet) hDmono hGunion
    rw [hDunion] at h
    simpa [D, B, G] using h
  have hshift : MemLp (fun x => u.toFun x - a₀) 1 (volume.restrict B) :=
    huB.sub (memLp_const a₀)
  have hshiftInt : Integrable (fun x => |u.toFun x - a₀|)
      (volume.restrict B) := (memLp_one_iff_integrable.mp hshift).abs
  have hJ : Tendsto (fun n => ∫ x in D n, |u.toFun x - a₀| ∂volume) atTop
      (nhds (∫ x in B, |u.toFun x - a₀| ∂volume)) := by
    have h := tendsto_setIntegral_of_monotone (f := fun x => |u.toFun x - a₀|)
      (fun n => (hDopen n).measurableSet) hDmono
      (by rw [hDunion]; exact hshiftInt)
    rw [hDunion] at h
    simpa [D, B] using h
  have hvolavg : Tendsto (fun n => (volume (D n)).toReal * |a n - a₀|)
      atTop (nhds 0) := by
    have hdiff : Tendsto (fun n => a n - a₀) atTop (nhds 0) := by
      simpa using havg.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => a₀)
        atTop (nhds a₀))
    have habs := (continuous_abs.tendsto 0).comp hdiff
    have hm := hvol.mul habs
    simpa using hm
  have hleft := @w1p_euclideanBall_poincareL1_faithful_hleft_2 x₀ r hr u s a₀ a hspos hslt huInt
    hJ hvolavg
  have hroot : Tendsto (fun n => (volume (D n)).toReal ^ (1 / 3 : ℝ)) atTop
      (nhds ((volume B).toReal ^ (1 / 3 : ℝ))) := by
    have hpair : Tendsto (fun n => ((volume (D n)).toReal, (1 / 3 : ℝ))) atTop
        (nhds ((volume B).toReal, (1 / 3 : ℝ))) := by
      simpa only [nhds_prod_eq] using
        hvol.prodMk (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 3 : ℝ))
          atTop (nhds (1 / 3 : ℝ)))
    exact (Real.continuousAt_rpow_of_pos ((volume B).toReal, (1 / 3 : ℝ))
      (by norm_num : 0 < (1 / 3 : ℝ))).tendsto.comp hpair
  have hright : Tendsto (fun n => poincareSobolevL1Constant.toReal *
      (volume (D n)).toReal ^ (1 / 3 : ℝ) *
        ∫ x in D n, G x ∂volume) atTop
      (nhds (poincareSobolevL1Constant.toReal *
        (volume B).toReal ^ (1 / 3 : ℝ) * ∫ x in B, G x ∂volume)) := by
    exact (tendsto_const_nhds.mul hroot).mul hGset
  have hbound (n : ℕ) : ∫ x in D n, |u.toFun x - a n| ∂volume ≤
      poincareSobolevL1Constant.toReal * (volume (D n)).toReal ^ (1 / 3 : ℝ) *
        ∫ x in D n, G x ∂volume := by
    simpa [D, a, G] using w1p_euclideanBall_poincareL1_inner_faithful
      x₀ hr (hspos n) (hslt n) u
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hbound)


end
end CKN
