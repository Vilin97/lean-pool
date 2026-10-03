/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Abstract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Derivative
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.EntryBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp

/-! # The third term of `e.ergodic.break.up`: integration by parts in time

Source: `enhance.tex` 8640–8830 (`e.ergodic.break.up.last`).  The zero-mean periodic matrix
`J - ⟨⟨J⟩⟩` is the time derivative of a bounded primitive `Q` with `Q(0) = Q(1) = 0`; integrating
by parts in time against `A_ij(t) = ∫_{𝕋²} ∂_iT ∂_jT` and using `∂_t A_ij = ∫ (D_t∂_iT ∂_jT +
∂_iT D_t∂_jT)` (since `∇·b = 0`) gives the stated bound.

The three ingredients live in the `TimeIBP/` modules: `Abstract` (the abstract time integration by
parts), `Derivative` (`hasDerivAt_integral_gradProduct`), `EntryBound` (the Cauchy–Schwarz bound
on `∫ |A_ij'|`). -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance

section Entry

variable {b : ℝ → Vec 2 → Vec 2} {T : ℝ → Vec 2 → ℝ}

/-- Entrywise integration by parts in time. -/
theorem abs_integral_mul_gradProd_le (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, Infra.Flow.spatialDivergence b t x = 0)
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hTper : ∀ t, 0 ≤ t → IsZ2Periodic (T t)) {G : ℝ → ℝ} {P B : ℝ} {N : ℕ}
    (hP : 0 < P) (hNP : (N : ℝ) * P = 1) (hG : Continuous G) (hGper : Function.Periodic G P)
    (hGmean : ∫ t in (0 : ℝ)..1, G t = 0) (hB : ∀ t, |G t| ≤ B) (i j : Fin 2) :
    |∫ t in (0 : ℝ)..1, G t * gradProd T i j t| ≤
      P * B * (2 * (Real.sqrt (spaceTimeGradNormSq (materialGrad b T)) *
        Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (T t) x)))) := by
  have hT' : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace := hT
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hgi := gradCoord_continuousOn_Icc hT' i
  have hgj := gradCoord_continuousOn_Icc hT' j
  have hA : ContinuousOn (gradProd T i j) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_integral_unitCube
      (h := fun t x => spaceGrad (T t) x i * spaceGrad (T t) x j) (hgi.mul hgj)
  have hA' : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (gradProd T i j) (gradProdDeriv b T i j t) t := by
    intro t ht
    have h := hasDerivAt_integral_gradProduct hb hdiv hT hTper ht.1 i j
    refine h.congr_deriv ?_
    refine setIntegral_congr_fun measurableSet_unitCube' fun x _ => ?_
    simp only [matGradExt_eq_materialGrad ht.1]
  have hD := gradProdDeriv_continuousOn hb hT' i j
  have h1 := abs_intervalIntegral_mul_le_of_periodic_mean_zero hP hNP hG hGper hGmean hB hA hA'
    (intervalIntegrable_of_continuousOn_Icc hD)
  have h2 := intervalIntegral_abs_gradProdDeriv_le hb hT' i j
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (mul_nonneg hP.le hB0))

end Entry

/-- e.ergodic.break.up.last, generic matrix field form: for `J` with continuous `P`-periodic
entries, `N P = 1`, and `|J - ⟨⟨J⟩⟩| ≤ B` entrywise. -/
theorem third_term_ibp {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, Infra.Flow.spatialDivergence b t x = 0) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hTper : ∀ t, 0 ≤ t → IsZ2Periodic (T t))
    (J : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hJ : ∀ i j, Continuous fun t => J t i j)
    {P B : ℝ} {N : ℕ} (hP : 0 < P) (hNP : (N : ℝ) * P = 1)
    (hJper : ∀ i j, Function.Periodic (fun t => J t i j) P)
    (hB : ∀ t i j, |(J t - timeAvgMat J) i j| ≤ B) :
    |(∫ t in (0 : ℝ)..1, gradQuad T (J t) t) - ∫ t in (0 : ℝ)..1, gradQuad T (timeAvgMat J) t| ≤
      8 * P * B * Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (T t) x)) *
        Real.sqrt (spaceTimeGradNormSq (materialGrad b T)) := by
  have hT' : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace := hT
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0 0)
  have hg : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    continuousOn_pi.2 fun k => gradCoord_continuousOn_Icc hT' k
  have hline : ∀ t ∈ Set.Icc (0 : ℝ) 1, Continuous fun x : Vec 2 => (t, x) :=
    fun t _ => continuous_const.prodMk continuous_id
  have hslice : ∀ t ∈ Set.Icc (0 : ℝ) 1, Continuous (spaceGrad (T t)) := fun t ht =>
    hg.comp_continuous (hline t ht) fun x => ⟨ht, mem_univ _⟩
  have hJc : ∀ i j, ContinuousOn (fun t => J t i j) (Set.Icc (0 : ℝ) 1) :=
    fun i j => (hJ i j).continuousOn
  -- the centred matrix
  set M : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => J t - timeAvgMat J with hM
  have hMc : ∀ i j, Continuous fun t => M t i j := fun i j => (hJ i j).sub continuous_const
  have ha : ContinuousOn (fun t => gradQuad T (J t) t) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_gradQuad hg hJc
  have hb' : ContinuousOn (fun t => gradQuad T (timeAvgMat J) t) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_gradQuad hg fun _ _ => continuousOn_const
  have hsub : (∫ t in (0 : ℝ)..1, gradQuad T (J t) t) -
      ∫ t in (0 : ℝ)..1, gradQuad T (timeAvgMat J) t = ∫ t in (0 : ℝ)..1, gradQuad T (M t) t := by
    rw [← intervalIntegral.integral_sub (intervalIntegrable_of_continuousOn_Icc ha)
      (intervalIntegrable_of_continuousOn_Icc hb')]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact (gradQuad_sub T (hslice t ht) (J t) (timeAvgMat J)).symm
  -- expansion in the matrix entries
  have hexpand : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      gradQuad T (M t) t = ∑ i : Fin 2, ∑ j : Fin 2, M t i j * gradProd T i j t := by
    intro t ht
    have hc : ∀ i j, Continuous fun x => spaceGrad (T t) x i * spaceGrad (T t) x j := fun i j =>
      ((continuous_apply i).comp (hslice t ht)).mul ((continuous_apply j).comp (hslice t ht))
    unfold gradQuad gradProd
    have hpt : ∀ x, vecDot (spaceGrad (T t) x) ((M t).mulVec (spaceGrad (T t) x)) =
        ∑ i : Fin 2, ∑ j : Fin 2, M t i j * (spaceGrad (T t) x i * spaceGrad (T t) x j) := by
      intro x
      simp only [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrableOn_unitCube_of_continuous ((hc i j).const_mul (M t i j)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => integrableOn_unitCube_of_continuous
      ((hc i j).const_mul (M t i j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  have hAc : ∀ i j, ContinuousOn (gradProd T i j) (Set.Icc (0 : ℝ) 1) := fun i j =>
    continuousOn_integral_unitCube
      (h := fun t x => spaceGrad (T t) x i * spaceGrad (T t) x j)
      ((gradCoord_continuousOn_Icc hT' i).mul (gradCoord_continuousOn_Icc hT' j))
  have hint : ∀ i j, IntervalIntegrable (fun t => M t i j * gradProd T i j t) volume 0 1 :=
    fun i j => intervalIntegrable_of_continuousOn_Icc ((hMc i j).continuousOn.mul (hAc i j))
  have hsum : ∫ t in (0 : ℝ)..1, gradQuad T (M t) t =
      (∫ t in (0 : ℝ)..1, M t 0 0 * gradProd T 0 0 t) +
        (∫ t in (0 : ℝ)..1, M t 0 1 * gradProd T 0 1 t) +
        ((∫ t in (0 : ℝ)..1, M t 1 0 * gradProd T 1 0 t) +
          ∫ t in (0 : ℝ)..1, M t 1 1 * gradProd T 1 1 t) := by
    have i0 : IntervalIntegrable (fun t => M t 0 0 * gradProd T 0 0 t +
        M t 0 1 * gradProd T 0 1 t) volume 0 1 := (hint 0 0).add (hint 0 1)
    have i1 : IntervalIntegrable (fun t => M t 1 0 * gradProd T 1 0 t +
        M t 1 1 * gradProd T 1 1 t) volume 0 1 := (hint 1 0).add (hint 1 1)
    rw [intervalIntegral.integral_congr (g := fun t => (M t 0 0 * gradProd T 0 0 t +
        M t 0 1 * gradProd T 0 1 t) + (M t 1 0 * gradProd T 1 0 t +
        M t 1 1 * gradProd T 1 1 t)) fun t ht => by
      rw [hexpand t (by rwa [Set.uIcc_of_le zero_le_one] at ht)]
      simp only [Fin.sum_univ_two]]
    rw [intervalIntegral.integral_add i0 i1, intervalIntegral.integral_add (hint 0 0) (hint 0 1),
      intervalIntegral.integral_add (hint 1 0) (hint 1 1)]
  -- entrywise bound
  have hentry : ∀ i j : Fin 2, |∫ t in (0 : ℝ)..1, M t i j * gradProd T i j t| ≤
      P * B * (2 * (Real.sqrt (spaceTimeGradNormSq (materialGrad b T)) *
        Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (T t) x)))) := by
    intro i j
    refine abs_integral_mul_gradProd_le hb hdiv hT hTper hP hNP (hMc i j)
      (fun t => by
        change J (t + P) i j - timeAvgMat J i j = J t i j - timeAvgMat J i j
        rw [show J (t + P) i j = J t i j from hJper i j t]) ?_ (fun t => hB t i j) i j
    have hint1 : IntervalIntegrable (fun t => J t i j) volume 0 1 :=
      (hJ i j).intervalIntegrable 0 1
    change ∫ t in (0 : ℝ)..1, (J t i j - timeAvgMat J i j) = 0
    rw [intervalIntegral.integral_sub hint1 intervalIntegrable_const]
    simp [timeAvgMat]
  rw [hsub, hsum]
  set X := P * B * (2 * (Real.sqrt (spaceTimeGradNormSq (materialGrad b T)) *
        Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (T t) x)))) with hX
  have h4 : |(∫ t in (0 : ℝ)..1, M t 0 0 * gradProd T 0 0 t) +
        (∫ t in (0 : ℝ)..1, M t 0 1 * gradProd T 0 1 t) +
        ((∫ t in (0 : ℝ)..1, M t 1 0 * gradProd T 1 0 t) +
          ∫ t in (0 : ℝ)..1, M t 1 1 * gradProd T 1 1 t)| ≤ 4 * X := by
    have e00 := hentry 0 0
    have e01 := hentry 0 1
    have e10 := hentry 1 0
    have e11 := hentry 1 1
    calc _ ≤ |∫ t in (0 : ℝ)..1, M t 0 0 * gradProd T 0 0 t| +
          |∫ t in (0 : ℝ)..1, M t 0 1 * gradProd T 0 1 t| +
          |∫ t in (0 : ℝ)..1, M t 1 0 * gradProd T 1 0 t| +
          |∫ t in (0 : ℝ)..1, M t 1 1 * gradProd T 1 1 t| := by
          refine (abs_add_le _ _).trans ?_
          have := abs_add_le (∫ t in (0 : ℝ)..1, M t 0 0 * gradProd T 0 0 t)
            (∫ t in (0 : ℝ)..1, M t 0 1 * gradProd T 0 1 t)
          have := abs_add_le (∫ t in (0 : ℝ)..1, M t 1 0 * gradProd T 1 0 t)
            (∫ t in (0 : ℝ)..1, M t 1 1 * gradProd T 1 1 t)
          linarith
      _ ≤ 4 * X := by linarith
  refine h4.trans (le_of_eq ?_)
  rw [hX]
  ring

end AVenhance.Infra.Section5.LeftToShow

end
