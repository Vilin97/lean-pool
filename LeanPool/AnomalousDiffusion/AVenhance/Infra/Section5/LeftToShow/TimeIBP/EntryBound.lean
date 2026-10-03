/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Abstract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Derivative
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp

/-! # Entrywise integration by parts in time

Source: `enhance.tex` 8780–8830.  For each pair `(i,j)` the function
`A_ij(t) = ∫_{𝕋²} ∂_iT ∂_jT` is continuous on `[0,1]`, differentiable on `(0,1)` with derivative
`∫ (D_t∂_iT ∂_jT + ∂_iT D_t∂_jT)`, and `∫_0^1 |A_ij'| ≤ 2 ‖∇T‖_{L²} ‖D_t∇T‖_{L²}`.  Combined with
    the
abstract time integration by parts this bounds `|∫_0^1 G A_ij|` for mean-zero periodic `G`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance

/-- `A_ij(t) = ∫_{𝕋²} ∂_iT ∂_jT`. -/
def gradProd (T : ℝ → Vec 2 → ℝ) (i j : Fin 2) (t : ℝ) : ℝ :=
  ∫ x in unitCube, spaceGrad (T t) x i * spaceGrad (T t) x j

/-- The derivative `∫ (D_t∂_iT ∂_jT + ∂_iT D_t∂_jT)` of `A_ij` (with the continuous extension of
`D_t∇T` to `t = 0`). -/
def gradProdDeriv (b : ℝ → Vec 2 → Vec 2) (T : ℝ → Vec 2 → ℝ) (i j : Fin 2) (t : ℝ) : ℝ :=
  ∫ x in unitCube, (matGradExt b T i (t, x) * spaceGrad (T t) x j +
    spaceGrad (T t) x i * matGradExt b T j (t, x))

/-- The vector field `D_t∇T` extended continuously to `t = 0`. -/
def matGradVec (b : ℝ → Vec 2 → Vec 2) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  fun i => matGradExt b T i (t, x)

section Setup

variable {b : ℝ → Vec 2 → Vec 2} {T : ℝ → Vec 2 → ℝ}

theorem icc_prod_subset_halfSpace :
    Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec 2)) ⊆ halfSpace :=
  Set.prod_mono Set.Icc_subset_Ici_self subset_rfl

theorem gradCoord_continuousOn_Icc
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace) (i : Fin 2) :
    ContinuousOn (gradCoord T i) (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
  (gradCoord_contDiffOn hT i).continuousOn.mono icc_prod_subset_halfSpace

theorem matGradVec_continuousOn (hb : Infra.Flow.SmoothPeriodicField b)
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace) :
    ContinuousOn (fun p : ℝ × Vec 2 => matGradVec b T p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
  continuousOn_pi.2 fun i => (matGradExt_continuousOn hb hT i).mono icc_prod_subset_halfSpace

theorem EntryBound.timeCube_measurable : MeasurableSet timeCube :=
  measurableSet_Ioo.prod measurableSet_unitCube'

/-- The norm of `D_t∇T` equals that of its continuous extension. -/
theorem spaceTimeGradNormSq_materialGrad_eq :
    spaceTimeGradNormSq (materialGrad b T) = spaceTimeGradNormSq (matGradVec b T) := by
  unfold spaceTimeGradNormSq
  refine setIntegral_congr_fun EntryBound.timeCube_measurable fun p hp => ?_
  have hp1 : 0 < p.1 := hp.1.1
  have : materialGrad b T p.1 p.2 = matGradVec b T p.1 p.2 := by
    funext i
    exact (matGradExt_eq_materialGrad hp1 p.2 i).symm
  simp only [this]

theorem abs_apply_le_sqrt_vecNormSq (v : Vec 2) (i : Fin 2) : |v i| ≤ Real.sqrt (vecNormSq v) := by
  apply Real.abs_le_sqrt
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

/-- Continuity in time of the spatial energy of a jointly continuous field. -/
theorem continuousOn_energy {V : ℝ → Vec 2 → Vec 2}
    (hV : ContinuousOn (fun p : ℝ × Vec 2 => V p.1 p.2) (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) :
    ContinuousOn (fun t => ∫ x in unitCube, vecNormSq (V t x)) (Set.Icc (0 : ℝ) 1) :=
  continuousOn_integral_unitCube (h := fun t x => vecNormSq (V t x))
    (continuous_vecNormSq_two.comp_continuousOn hV)

/-- Cauchy–Schwarz in time for continuous nonnegative energies. -/
theorem integral_sqrt_mul_sqrt_le {a c : ℝ → ℝ} (ha : ContinuousOn a (Set.Icc 0 1))
    (hc : ContinuousOn c (Set.Icc 0 1)) (ha0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ a t)
    (hc0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ c t) :
    ∫ t in (0 : ℝ)..1, Real.sqrt (a t) * Real.sqrt (c t) ≤
      Real.sqrt (∫ t in (0 : ℝ)..1, a t) * Real.sqrt (∫ t in (0 : ℝ)..1, c t) := by
  have hsa : ContinuousOn (fun t => Real.sqrt (a t)) (Set.Icc 0 1) := ha.sqrt
  have hsc : ContinuousOn (fun t => Real.sqrt (c t)) (Set.Icc 0 1) := hc.sqrt
  have hint : ∀ {f : ℝ → ℝ}, ContinuousOn f (Set.Icc 0 1) →
      IntegrableOn f (Set.Ioc (0 : ℝ) 1) := fun hf =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegrable_of_continuousOn_Icc hf)
  have e1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt (a t) ^ 2 = a t := fun t ht =>
    Real.sq_sqrt (ha0 t ht)
  have e2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt (c t) ^ 2 = c t := fun t ht =>
    Real.sq_sqrt (hc0 t ht)
  have hI1 : IntegrableOn (fun t => Real.sqrt (a t) ^ 2) (Set.Ioc (0 : ℝ) 1) := by
    refine (hint ha).congr_fun (fun t ht => (e1 t ⟨ht.1.le, ht.2⟩).symm) measurableSet_Ioc
  have hI2 : IntegrableOn (fun t => Real.sqrt (c t) ^ 2) (Set.Ioc (0 : ℝ) 1) := by
    refine (hint hc).congr_fun (fun t ht => (e2 t ⟨ht.1.le, ht.2⟩).symm) measurableSet_Ioc
  have hI3 : IntegrableOn (fun t => Real.sqrt (a t) * Real.sqrt (c t)) (Set.Ioc (0 : ℝ) 1) :=
    hint (hsa.mul hsc)
  have hcs := integral_mul_le_sqrt_mul_sqrt (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (f := fun t => Real.sqrt (a t)) (g := fun t => Real.sqrt (c t)) hI1 hI2 hI3
  have c1 : ∫ t in Set.Ioc (0 : ℝ) 1, Real.sqrt (a t) ^ 2 = ∫ t in (0 : ℝ)..1, a t := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact setIntegral_congr_fun measurableSet_Ioc fun t ht => e1 t ⟨ht.1.le, ht.2⟩
  have c2 : ∫ t in Set.Ioc (0 : ℝ) 1, Real.sqrt (c t) ^ 2 = ∫ t in (0 : ℝ)..1, c t := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact setIntegral_congr_fun measurableSet_Ioc fun t ht => e2 t ⟨ht.1.le, ht.2⟩
  rw [c1, c2] at hcs
  rwa [intervalIntegral.integral_of_le zero_le_one]

/-- Cauchy–Schwarz on the unit cube for continuous functions. -/
theorem integral_unitCube_mul_le {f g : Vec 2 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ∫ x in unitCube, f x * g x ≤
      Real.sqrt (∫ x in unitCube, f x ^ 2) * Real.sqrt (∫ x in unitCube, g x ^ 2) :=
  integral_mul_le_sqrt_mul_sqrt (integrableOn_unitCube_of_continuous (hf.pow 2))
    (integrableOn_unitCube_of_continuous (hg.pow 2))
    (integrableOn_unitCube_of_continuous (hf.mul hg))

theorem vecNormSq_nonneg' (v : Vec 2) : 0 ≤ vecNormSq v := by
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1)]

/-- Time-slice bound `|A_ij'(t)| ≤ 2 ‖D_t∇T(t)‖_{L²(𝕋²)} ‖∇T(t)‖_{L²(𝕋²)}`. -/
theorem abs_gradProdDeriv_le (hb : Infra.Flow.SmoothPeriodicField b)
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    |gradProdDeriv b T i j t| ≤
      2 * (Real.sqrt (∫ x in unitCube, vecNormSq (matGradVec b T t x)) *
        Real.sqrt (∫ x in unitCube, vecNormSq (spaceGrad (T t) x))) := by
  have hline : Continuous fun x : Vec 2 => (t, x) := continuous_const.prodMk continuous_id
  have hmem : ∀ x : Vec 2, (t, x) ∈ Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec 2)) :=
    fun x => ⟨ht, trivial⟩
  have hHc : Continuous (matGradVec b T t) :=
    (matGradVec_continuousOn hb hT).comp_continuous hline hmem
  have hGc : Continuous (spaceGrad (T t)) := by
    refine continuous_pi fun k => ?_
    exact (gradCoord_continuousOn_Icc hT k).comp_continuous hline hmem
  set nH : Vec 2 → ℝ := fun x => Real.sqrt (vecNormSq (matGradVec b T t x)) with hnH
  set nG : Vec 2 → ℝ := fun x => Real.sqrt (vecNormSq (spaceGrad (T t) x)) with hnG
  have hnHc : Continuous nH := (continuous_vecNormSq_two.comp hHc).sqrt
  have hnGc : Continuous nG := (continuous_vecNormSq_two.comp hGc).sqrt
  have hpt : ∀ x, ‖matGradExt b T i (t, x) * spaceGrad (T t) x j +
      spaceGrad (T t) x i * matGradExt b T j (t, x)‖ ≤ 2 * (nH x * nG x) := by
    intro x
    rw [Real.norm_eq_abs]
    have h1 : |matGradExt b T i (t, x)| ≤ nH x := abs_apply_le_sqrt_vecNormSq (matGradVec b T t x) i
    have h2 : |matGradExt b T j (t, x)| ≤ nH x := abs_apply_le_sqrt_vecNormSq (matGradVec b T t x) j
    have h3 : |spaceGrad (T t) x i| ≤ nG x := abs_apply_le_sqrt_vecNormSq (spaceGrad (T t) x) i
    have h4 : |spaceGrad (T t) x j| ≤ nG x := abs_apply_le_sqrt_vecNormSq (spaceGrad (T t) x) j
    calc _ ≤ |matGradExt b T i (t, x) * spaceGrad (T t) x j| +
          |spaceGrad (T t) x i * matGradExt b T j (t, x)| := abs_add_le _ _
      _ ≤ nH x * nG x + nG x * nH x := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul h1 h4 (abs_nonneg _) ((abs_nonneg _).trans h1))
          (mul_le_mul h3 h2 (abs_nonneg _) ((abs_nonneg _).trans h3))
      _ = 2 * (nH x * nG x) := by ring
  have hbound := norm_integral_le_of_norm_le (μ := volume.restrict unitCube)
    (f := fun x => matGradExt b T i (t, x) * spaceGrad (T t) x j +
      spaceGrad (T t) x i * matGradExt b T j (t, x))
    (integrableOn_unitCube_of_continuous ((hnHc.mul hnGc).const_mul 2))
    (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hbound
  have hcs := integral_unitCube_mul_le hnHc hnGc
  have e1 : (∫ x in unitCube, nH x ^ 2) = ∫ x in unitCube, vecNormSq (matGradVec b T t x) := by
    refine setIntegral_congr_fun measurableSet_unitCube' fun x _ => ?_
    exact Real.sq_sqrt (vecNormSq_nonneg' _)
  have e2 : (∫ x in unitCube, nG x ^ 2) = ∫ x in unitCube, vecNormSq (spaceGrad (T t) x) := by
    refine setIntegral_congr_fun measurableSet_unitCube' fun x _ => ?_
    exact Real.sq_sqrt (vecNormSq_nonneg' _)
  rw [e1, e2] at hcs
  have : ‖gradProdDeriv b T i j t‖ ≤ 2 * ∫ x in unitCube, nH x * nG x := hbound
  rw [Real.norm_eq_abs] at this
  exact this.trans (by linarith)

theorem gradProdDeriv_continuousOn (hb : Infra.Flow.SmoothPeriodicField b)
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace) (i j : Fin 2) :
    ContinuousOn (gradProdDeriv b T i j) (Set.Icc (0 : ℝ) 1) := by
  refine continuousOn_integral_unitCube
    (h := fun t x => matGradExt b T i (t, x) * spaceGrad (T t) x j +
      spaceGrad (T t) x i * matGradExt b T j (t, x)) ?_
  have hmi := (matGradExt_continuousOn hb hT i).mono icc_prod_subset_halfSpace
  have hmj := (matGradExt_continuousOn hb hT j).mono icc_prod_subset_halfSpace
  have hgi := gradCoord_continuousOn_Icc hT i
  have hgj := gradCoord_continuousOn_Icc hT j
  exact (hmi.mul hgj).add (hgi.mul hmj)

/-- `∫_0^1 |A_ij'| ≤ 2 ‖D_t∇T‖_{L²((0,1)×𝕋²)} ‖∇T‖_{L²((0,1)×𝕋²)}`. -/
theorem intervalIntegral_abs_gradProdDeriv_le (hb : Infra.Flow.SmoothPeriodicField b)
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) halfSpace) (i j : Fin 2) :
    ∫ t in (0 : ℝ)..1, |gradProdDeriv b T i j t| ≤
      2 * (Real.sqrt (spaceTimeGradNormSq (materialGrad b T)) *
        Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (T t) x))) := by
  have hg : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    continuousOn_pi.2 fun k => gradCoord_continuousOn_Icc hT k
  have hH := matGradVec_continuousOn hb hT
  have hEH := continuousOn_energy (V := matGradVec b T) hH
  have hEG := continuousOn_energy (V := fun t x => spaceGrad (T t) x) hg
  have hD := gradProdDeriv_continuousOn hb hT i j
  have hle : ∫ t in (0 : ℝ)..1, |gradProdDeriv b T i j t| ≤
      ∫ t in (0 : ℝ)..1, 2 * (Real.sqrt (∫ x in unitCube, vecNormSq (matGradVec b T t x)) *
        Real.sqrt (∫ x in unitCube, vecNormSq (spaceGrad (T t) x))) := by
    refine intervalIntegral.integral_mono_on zero_le_one
      (intervalIntegrable_of_continuousOn_Icc hD.abs)
      (intervalIntegrable_of_continuousOn_Icc ((hEH.sqrt.mul hEG.sqrt).const_mul 2)) ?_
    intro t ht
    exact abs_gradProdDeriv_le hb hT ht i j
  refine hle.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hcs := integral_sqrt_mul_sqrt_le hEH hEG
    (fun t _ => integral_nonneg fun x => vecNormSq_nonneg' _)
    (fun t _ => integral_nonneg fun x => vecNormSq_nonneg' _)
  rw [← spaceTimeGradNormSq_eq_intervalIntegral hH, ← spaceTimeGradNormSq_eq_intervalIntegral hg,
    ← spaceTimeGradNormSq_materialGrad_eq] at hcs
  linarith

end Setup

end AVenhance.Infra.Section5.LeftToShow

end
