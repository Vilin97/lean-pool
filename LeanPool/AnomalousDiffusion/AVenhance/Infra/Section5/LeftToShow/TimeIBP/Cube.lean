/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Unit-cube tools for the time integration by parts

Source: `enhance.tex` 8700–8830.  Differentiation under the integral sign over the unit cube,
periodic integration by parts on the unit cube (real-valued, `C¹` hypotheses), the periodicity
of the gradient of a periodic function, and the Cauchy–Schwarz inequality on a measure space
(via the discriminant of `λ ↦ ∫ (λ f - g)²`). -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance

/-- The closed unit square. -/
def cubeCl : Set (Vec 2) := Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1

theorem isCompact_cubeCl : IsCompact cubeCl :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem unitCube_subset_cubeCl : unitCube ⊆ cubeCl :=
  Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self

theorem measurableSet_unitCube' : MeasurableSet unitCube :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioo

/-! ### Differentiation under the integral over the unit cube -/

/-- Differentiation under the integral sign over the unit cube: a parameter function that is
jointly continuous with jointly continuous pointwise time derivative on `(0,∞) × ℝ²`. -/
theorem hasDerivAt_integral_unitCube {h h' : ℝ → Vec 2 → ℝ}
    (hc : ContinuousOn (fun p : ℝ × Vec 2 => h p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (hd : ∀ s, 0 < s → ∀ x, HasDerivAt (fun r => h r x) (h' s x) s)
    (hc' : ContinuousOn (fun p : ℝ × Vec 2 => h' p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in unitCube, h s x) (∫ x in unitCube, h' t x) t := by
  set r : ℝ := t / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hball : Metric.ball t r ⊆ Set.Ioi (0 : ℝ) := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have h := abs_lt.mp hs
    rw [Set.mem_Ioi]
    linarith
  let K : Set (ℝ × Vec 2) := Set.Icc (t - r) (t + r) ×ˢ cubeCl
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_cubeCl
  have hKsub : K ⊆ Set.Ioi (0 : ℝ) ×ˢ Set.univ := by
    rintro ⟨s, x⟩ hp
    simp only [K, Set.mem_prod, Set.mem_Icc] at hp
    exact ⟨by simp only [Set.mem_Ioi]; linarith [hp.1.1], trivial⟩
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hc'.mono hKsub)
  have hslice : ∀ s, 0 < s → Continuous (fun x => h s x) := by
    intro s hs
    have hline : Continuous fun x : Vec 2 => (s, x) := continuous_const.prodMk continuous_id
    exact (hc.comp_continuous hline fun x => ⟨hs, trivial⟩)
  have hslice' : ∀ s, 0 < s → Continuous (fun x => h' s x) := by
    intro s hs
    have hline : Continuous fun x : Vec 2 => (s, x) := continuous_const.prodMk continuous_id
    exact (hc'.comp_continuous hline fun x => ⟨hs, trivial⟩)
  let μ : Measure (Vec 2) := volume.restrict unitCube
  have hFmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (fun x => h s x) μ := by
    filter_upwards [Metric.ball_mem_nhds t hrpos] with s hs
    exact (hslice s (hball hs)).aestronglyMeasurable
  have hFint : Integrable (fun x => h t x) μ :=
    integrableOn_unitCube_of_continuous (hslice t ht)
  have hF'meas : AEStronglyMeasurable (fun x => h' t x) μ :=
    (hslice' t ht).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t r, ‖h' s x‖ ≤ C := by
    apply (ae_restrict_iff' measurableSet_unitCube').2
    filter_upwards with x hx s hs
    have hsK : (s, x) ∈ K := by
      refine ⟨?_, unitCube_subset_cubeCl hx⟩
      rw [Metric.mem_ball, Real.dist_eq] at hs
      have h := abs_lt.mp hs
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    exact hC (s, x) hsK
  have hdiff : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t r, HasDerivAt (fun r => h r x) (h' s x) s := by
    filter_upwards with x s hs
    exact hd s (hball hs) x
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball t r) (μ := μ) (bound := fun _ : Vec 2 => C)
    (Metric.ball_mem_nhds t hrpos) hFmeas hFint hF'meas hbound
    (integrableOn_unitCube_of_continuous continuous_const) hdiff
  exact hmain.2

/-! ### Periodic integration by parts on the unit cube -/

theorem Cube.integrableOn_unitCell_of_continuous {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f (Infra.Torus.unitCell 2) := by
  refine (hf.continuousOn.integrableOn_compact isCompact_cubeCl).mono_set ?_
  intro x hx
  simp only [Infra.Torus.unitCell, Infra.Torus.unitCellAt, Set.mem_ofPred_eq, zero_add] at hx
  intro i _
  exact ⟨(hx i).1.le, (hx i).2⟩

/-- Real periodic integration by parts on the unit cube. -/
theorem integral_unitCube_mul_spaceGrad {f g : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hpf : IsZ2Periodic f) (hpg : IsZ2Periodic g) (i : Fin 2) :
    (∫ x in unitCube, f x * spaceGrad g x i) = -∫ x in unitCube, spaceGrad f x i * g x := by
  let fc := Infra.Torus.realToComplex f
  let gc := Infra.Torus.realToComplex g
  have hfc : ContDiff ℝ 1 fc := Complex.ofRealCLM.contDiff.comp hf
  have hgc : ContDiff ℝ 1 gc := Complex.ofRealCLM.contDiff.comp hg
  have hper : ∀ {u : Vec 2 → ℝ}, IsZ2Periodic u →
      Infra.Torus.IsZdPeriodic (Infra.Torus.realToComplex u) := by
    intro u hu k x
    exact congrArg (fun y : ℝ => (y : ℂ)) ((Infra.Torus.isZdPeriodic_iff_frozen u).2 hu k x)
  have hcomplex := Infra.Torus.integral_unitCell_coord_ibp i hfc hgc (hper hpf) (hper hpg)
  have hcomplex' :
      (∫ x in Infra.Torus.unitCell 2, ((f x * spaceGrad g x i : ℝ) : ℂ)) =
        -∫ x in Infra.Torus.unitCell 2, ((spaceGrad f x i * g x : ℝ) : ℂ) := by
    calc
      _ = ∫ x in Infra.Torus.unitCell 2, fc x * Infra.Torus.coordDeriv i gc x := by
        apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
        intro x _
        simp only [fc, gc]
        rw [Infra.Torus.coordDeriv_realToComplex hg i x]
        simp [Infra.Torus.realToComplex, Complex.ofReal_mul]
      _ = -∫ x in Infra.Torus.unitCell 2, Infra.Torus.coordDeriv i fc x * gc x := hcomplex
      _ = -∫ x in Infra.Torus.unitCell 2, ((spaceGrad f x i * g x : ℝ) : ℂ) := by
        congr 1
        apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
        intro x _
        simp only [fc, gc]
        rw [Infra.Torus.coordDeriv_realToComplex hf i x]
        simp [Infra.Torus.realToComplex, Complex.ofReal_mul]
  have hDf : Continuous fun x => spaceGrad f x i :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDg : Continuous fun x => spaceGrad g x i :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hleft := Cube.integrableOn_unitCell_of_continuous (hf.continuous.mul hDg)
  have hright := Cube.integrableOn_unitCell_of_continuous (hDf.mul hg.continuous)
  have hlc : (∫ x in Infra.Torus.unitCell 2, ((f x * spaceGrad g x i : ℝ) : ℂ)) =
      ((∫ x in Infra.Torus.unitCell 2, f x * spaceGrad g x i : ℝ) : ℂ) := by
    simpa using (Complex.ofRealCLM.integral_comp_comm
      (μ := (volume : Measure (Vec 2)).restrict (Infra.Torus.unitCell 2)) hleft)
  have hrc : (∫ x in Infra.Torus.unitCell 2, ((spaceGrad f x i * g x : ℝ) : ℂ)) =
      ((∫ x in Infra.Torus.unitCell 2, spaceGrad f x i * g x : ℝ) : ℂ) := by
    simpa using (Complex.ofRealCLM.integral_comp_comm
      (μ := (volume : Measure (Vec 2)).restrict (Infra.Torus.unitCell 2)) hright)
  have hcell : (∫ x in Infra.Torus.unitCell 2, f x * spaceGrad g x i) =
      -∫ x in Infra.Torus.unitCell 2, spaceGrad f x i * g x := by
    have hcast := hlc.symm.trans (hcomplex'.trans (congrArg Neg.neg hrc))
    simpa using congrArg Complex.re hcast
  rw [← Infra.Torus.integral_unitCell_eq_unitCube, ← Infra.Torus.integral_unitCell_eq_unitCube]
  exact hcell

/-- The gradient of a `C¹` periodic function is periodic. -/
theorem isZ2Periodic_spaceGrad {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (hper : IsZ2Periodic f) :
    IsZ2Periodic (spaceGrad f) := by
  intro k x
  let v : Vec 2 := latticeShift k
  have hfun : (fun y : Vec 2 => f (y + v)) = f := funext fun y => hper k y
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have htranslate : HasFDerivAt (fun y : Vec 2 => y + v) (ContinuousLinearMap.id ℝ (Vec 2)) x := by
    simpa only [id_eq] using (hasFDerivAt_id x).add_const v
  have hcomp := (hdiff (x + v)).hasFDerivAt.comp x htranslate
  have hshift : HasFDerivAt f (fderiv ℝ f (x + v)) x := by
    have hcomp' := hcomp
    change HasFDerivAt (fun y : Vec 2 => f (y + v))
      (fderiv ℝ f (x + v) ∘L ContinuousLinearMap.id ℝ (Vec 2)) x at hcomp'
    rw [ContinuousLinearMap.comp_id, hfun] at hcomp'
    exact hcomp'
  have hderiv : fderiv ℝ f (x + v) = fderiv ℝ f x := hshift.unique (hdiff x).hasFDerivAt
  funext i
  change fderiv ℝ f (x + latticeShift k) (basisVec i) = fderiv ℝ f x (basisVec i)
  exact congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) hderiv

/-! ### Cauchy–Schwarz -/

/-- Cauchy–Schwarz for integrable `f²`, `g²`, `f g` (by the discriminant of
`λ ↦ ∫ (λ f - g)²`). -/
theorem integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    ∫ x, f x * g x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hq : ∀ l : ℝ, 0 ≤ (∫ x, f x ^ 2 ∂μ) * (l * l) + (-2 * ∫ x, f x * g x ∂μ) * l +
      ∫ x, g x ^ 2 ∂μ := by
    intro l
    have hnn : 0 ≤ ∫ x, (l * f x - g x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have hexp : ∫ x, (l * f x - g x) ^ 2 ∂μ =
        (∫ x, f x ^ 2 ∂μ) * (l * l) + (-2 * ∫ x, f x * g x ∂μ) * l + ∫ x, g x ^ 2 ∂μ := by
      have h1 : ∀ x, (l * f x - g x) ^ 2 =
          (l * l) * f x ^ 2 + (-2 * l) * (f x * g x) + g x ^ 2 := fun x => by ring
      simp_rw [h1]
      have i1 : Integrable (fun x => (l * l) * f x ^ 2) μ := hf.const_mul _
      have i2 : Integrable (fun x => (-2 * l) * (f x * g x)) μ := hfg.const_mul _
      have i3 : Integrable (fun x => (l * l) * f x ^ 2 + (-2 * l) * (f x * g x)) μ := i1.add i2
      rw [integral_add i3 hg, integral_add i1 i2, integral_const_mul, integral_const_mul]
      ring
    linarith
  have hdisc := discrim_le_zero hq
  unfold discrim at hdisc
  set a := ∫ x, f x ^ 2 ∂μ
  set b := ∫ x, g x ^ 2 ∂μ
  set c := ∫ x, f x * g x ∂μ
  have ha : 0 ≤ a := integral_nonneg fun x => sq_nonneg _
  have hb : 0 ≤ b := integral_nonneg fun x => sq_nonneg _
  have hc2 : c ^ 2 ≤ a * b := by nlinarith only [hdisc]
  calc c ≤ |c| := le_abs_self c
    _ = Real.sqrt (c ^ 2) := (Real.sqrt_sq_eq_abs c).symm
    _ ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt hc2
    _ = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha b

end AVenhance.Infra.Section5.LeftToShow

end
