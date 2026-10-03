/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.MatrixContinuity

/-! # The four-term break-up `e.ergodic.break.up`

Source: `enhance.tex` 8305–8394.  The source's triangle inequality is the exact identity
`ergodic_break_up`: every term is a continuous function of time on `[0,1]`, the spatial
quadratic form `A ↦ ∫ ∇T·A∇T` is linear in `A`, and the quantities telescope. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- `∫_{𝕋²} ∇T(t)·A ∇T(t)`. -/
def gradQuad (T : ℝ → Vec 2 → ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) : ℝ :=
  ∫ x in unitCube, vecDot (spaceGrad (T t) x) (A.mulVec (spaceGrad (T t) x))

/-- Continuity of the quadratic form `u ↦ u·A u` in terms of continuity of the entries. -/
theorem continuousOn_quadForm {X : Type*} [TopologicalSpace X] {s : Set X}
    {A : X → Matrix (Fin 2) (Fin 2) ℝ} {u : X → Vec 2}
    (hA : ∀ i j, ContinuousOn (fun p => A p i j) s) (hu : ∀ i, ContinuousOn (fun p => u p i) s) :
    ContinuousOn (fun p => vecDot (u p) ((A p).mulVec (u p))) s := by
  simp only [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h00 := hA 0 0
  have h01 := hA 0 1
  have h10 := hA 1 0
  have h11 := hA 1 1
  have h0 := hu 0
  have h1 := hu 1
  fun_prop

theorem intervalIntegrable_of_continuousOn_Icc {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    IntervalIntegrable f volume 0 1 :=
  hf.intervalIntegrable_of_Icc zero_le_one

theorem gradQuad_sub (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hT : Continuous (spaceGrad (T t)))
    (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    gradQuad T (A - B) t = gradQuad T A t - gradQuad T B t := by
  have hcont : ∀ C : Matrix (Fin 2) (Fin 2) ℝ, Continuous fun x =>
      vecDot (spaceGrad (T t) x) (C.mulVec (spaceGrad (T t) x)) := by
    intro C
    have h := continuousOn_quadForm (X := Vec 2) (s := Set.univ) (A := fun _ => C)
      (u := spaceGrad (T t)) (fun _ _ => continuousOn_const)
      (fun i => (continuous_apply i |>.comp hT).continuousOn)
    exact continuousOn_univ.mp h
  unfold gradQuad
  rw [← integral_sub (integrableOn_unitCube_of_continuous (hcont A))
    (integrableOn_unitCube_of_continuous (hcont B))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Matrix.sub_mulVec, vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem gradQuad_smul (T : ℝ → Vec 2 → ℝ) (c t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    gradQuad T (c • A) t = c * gradQuad T A t := by
  unfold gradQuad
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Matrix.smul_mulVec, vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem abs_gradQuad_le {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hT : Continuous (spaceGrad (T t)))
    {A : Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ} (hA : ∀ i j, |A i j| ≤ B) :
    |gradQuad T A t| ≤ 2 * B * ∫ x in unitCube, vecNormSq (spaceGrad (T t) x) := by
  have hint : Continuous fun x => vecNormSq (spaceGrad (T t) x) :=
    continuous_vecNormSq_two.comp hT
  have hbound := norm_integral_le_of_norm_le (μ := volume.restrict unitCube)
    (f := fun x => vecDot (spaceGrad (T t) x) (A.mulVec (spaceGrad (T t) x)))
    (g := fun x => 2 * B * vecNormSq (spaceGrad (T t) x))
    ((integrableOn_unitCube_of_continuous hint).const_mul (2 * B))
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using abs_vecDot_mulVec_le hA (spaceGrad (T t) x))
  rw [integral_const_mul] at hbound
  simpa [gradQuad, Real.norm_eq_abs] using hbound

theorem gradQuad_smul_one (T : ℝ → Vec 2 → ℝ) (c t : ℝ) :
    gradQuad T (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t =
      c * ∫ x in unitCube, vecNormSq (spaceGrad (T t) x) := by
  unfold gradQuad
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, vecDot, vecNormSq, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `t ↦ ∫ ∇T(t)·M(t) ∇T(t)` is continuous on `[0,1]` for a matrix field with continuous
entries. -/
theorem continuousOn_gradQuad {T : ℝ → Vec 2 → ℝ}
    (hg : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
    {M : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hM : ∀ i j, ContinuousOn (fun t => M t i j) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun t => gradQuad T (M t) t) (Set.Icc (0 : ℝ) 1) := by
  refine continuousOn_integral_unitCube
    (h := fun t x => vecDot (spaceGrad (T t) x) ((M t).mulVec (spaceGrad (T t) x))) ?_
  exact continuousOn_quadForm (X := ℝ × Vec 2) (A := fun p => M p.1)
    (u := fun p => spaceGrad (T p.1) p.2)
    (fun i j => (hM i j).comp continuousOn_fst fun p hp => hp.1)
    (fun i => continuousOn_pi.1 hg i)

/-- The space average `⟨FᵗF⟩(t)` has continuous entries. -/
theorem leadingGramAvg_continuousOn (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm : ℝ}
    (hκm : 0 < κm) (i j : Fin 2) :
    ContinuousOn (fun t => leadingGramAvg I hΦ m κm t i j) (Set.Icc (0 : ℝ) 1) := by
  have hF := leadingMatrix_continuous I hΦ hm hκm
  have hG : Continuous fun p : ℝ × Vec 2 =>
      ((leadingMatrix I hΦ m κm p.1 p.2).transpose * leadingMatrix I hΦ m κm p.1 p.2) i j :=
    (hF.matrix_transpose.matrix_mul hF).matrix_elem i j
  exact continuousOn_integral_unitCube
    (h := fun t x => ((leadingMatrix I hΦ m κm t x).transpose * leadingMatrix I hΦ m κm t x) i j)
    hG.continuousOn

/-- `e.ergodic.break.up` (source 8305–8394) as an exact identity; the source's inequality is its
triangle inequality.  `J` is any matrix field with continuous entries (it will be `J_m^{κ_m}`). -/
theorem ergodic_break_up (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm : ℝ} (hκm : 0 < κm)
    (κp : ℝ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (J : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hJ : ∀ i j, Continuous fun t => J t i j) :
    κm * spaceTimeGradNormSq (leadingGrad I hΦ m κm T) -
        κp * spaceTimeGradNormSq (fun t x => spaceGrad (T t) x) =
      κm * (∫ t in (0 : ℝ)..1, ((∫ x in unitCube, vecNormSq (leadingGrad I hΦ m κm T t x)) -
          gradQuad T (leadingGramAvg I hΦ m κm t) t)) +
        (∫ t in (0 : ℝ)..1, gradQuad T (κm • leadingGramAvg I hΦ m κm t - J t) t) +
        ((∫ t in (0 : ℝ)..1, gradQuad T (J t) t) -
          ∫ t in (0 : ℝ)..1, gradQuad T (timeAvgMat J) t) +
        ((∫ t in (0 : ℝ)..1, gradQuad T (timeAvgMat J) t) -
          κp * ∫ t in (0 : ℝ)..1, ∫ x in unitCube, vecNormSq (spaceGrad (T t) x)) := by
  have hg : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    (spaceGrad_continuousOn hT).mono (Set.prod_mono Set.Icc_subset_Ici_self subset_rfl)
  have hslice : ∀ t ∈ Set.Icc (0 : ℝ) 1, Continuous (spaceGrad (T t)) := fun t ht =>
    hg.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨ht, mem_univ _⟩
  have hF := leadingMatrix_continuous I hΦ hm hκm
  -- continuity of the leading gradient
  have hLG : ContinuousOn (fun p : ℝ × Vec 2 => leadingGrad I hΦ m κm T p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    refine continuousOn_pi.2 fun i => ?_
    have h0 := hF.matrix_elem i 0
    have h1 := hF.matrix_elem i 1
    have g0 := continuousOn_pi.1 hg 0
    have g1 := continuousOn_pi.1 hg 1
    simp only [leadingGrad, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    fun_prop
  have hN : ContinuousOn (fun t => ∫ x in unitCube, vecNormSq (leadingGrad I hΦ m κm T t x))
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_integral_unitCube
      (h := fun t x => vecNormSq (leadingGrad I hΦ m κm T t x))
      (continuous_vecNormSq_two.comp_continuousOn hLG)
  have hQ : ContinuousOn (fun t => ∫ x in unitCube, vecNormSq (spaceGrad (T t) x))
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_integral_unitCube
      (h := fun t x => vecNormSq (spaceGrad (T t) x))
      (continuous_vecNormSq_two.comp_continuousOn hg)
  have hGram : ∀ i j, ContinuousOn (fun t => leadingGramAvg I hΦ m κm t i j)
      (Set.Icc (0 : ℝ) 1) := leadingGramAvg_continuousOn I hΦ hm hκm
  have hG : ContinuousOn (fun t => gradQuad T (leadingGramAvg I hΦ m κm t) t)
      (Set.Icc (0 : ℝ) 1) := continuousOn_gradQuad hg hGram
  have hJc : ∀ i j, ContinuousOn (fun t => J t i j) (Set.Icc (0 : ℝ) 1) :=
    fun i j => (hJ i j).continuousOn
  have ha : ContinuousOn (fun t => gradQuad T (J t) t) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_gradQuad hg hJc
  have hb : ContinuousOn (fun t => gradQuad T (timeAvgMat J) t) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_gradQuad hg fun _ _ => continuousOn_const
  have hR : ContinuousOn (fun t => gradQuad T (κm • leadingGramAvg I hΦ m κm t - J t) t)
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_gradQuad hg fun i j => (continuousOn_const.mul (hGram i j)).sub (hJc i j)
  -- rewrite the two squared norms as iterated integrals
  rw [spaceTimeGradNormSq_eq_intervalIntegral hLG,
    spaceTimeGradNormSq_eq_intervalIntegral hg]
  -- pointwise linearity on `[0,1]`
  have hRlin : ∫ t in (0 : ℝ)..1, gradQuad T (κm • leadingGramAvg I hΦ m κm t - J t) t =
      ∫ t in (0 : ℝ)..1, (κm * gradQuad T (leadingGramAvg I hΦ m κm t) t -
        gradQuad T (J t) t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    rw [gradQuad_sub T (hslice t ht), gradQuad_smul]
  have iN := intervalIntegrable_of_continuousOn_Icc hN
  have iG := intervalIntegrable_of_continuousOn_Icc hG
  have ia := intervalIntegrable_of_continuousOn_Icc ha
  rw [hRlin, intervalIntegral.integral_sub iN iG,
    intervalIntegral.integral_sub (iG.const_mul κm) ia, intervalIntegral.integral_const_mul]
  ring

end AVenhance.Infra.Section5.LeftToShow

end
