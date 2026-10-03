/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.WeakGradientPeriodization
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsPeriodicH1With
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentFourierTest
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Linear operations on periodic weak gradients

Cell `L²` control and periodicity imply global integrability against compact tests. This lets the
whole-space weak derivative identities be subtracted without relying on junk integral values.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization

namespace AVenhance.Infra.Parabolic.WeakUniqueness

/-- Closed time-space unit cell for the weak equation algebra. -/
def WeakAlgebra.weakTimeClosedCell : Set (ℝ × Vec 2) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem WeakAlgebra.weakTimeClosedCell_compact : IsCompact WeakAlgebra.weakTimeClosedCell := by
  simpa [WeakAlgebra.weakTimeClosedCell] using
    isCompact_Icc.prod (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem WeakAlgebra.weakTimeCube_subset_closedCell :
    AVenhance.timeCube ⊆ WeakAlgebra.weakTimeClosedCell := by
  intro p hp
  rcases hp with ⟨ht, hx⟩
  refine ⟨⟨le_of_lt ht.1, le_of_lt ht.2⟩, ?_⟩
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  have hi := hx i (Set.mem_univ _)
  exact ⟨le_of_lt hi.1, le_of_lt hi.2⟩

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def WeakAlgebra.weakSpatialClosedCell : Set (Vec 2) :=
  Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem WeakAlgebra.weakSpatialClosedCell_compact : IsCompact WeakAlgebra.weakSpatialClosedCell :=
    by
  simpa [WeakAlgebra.weakSpatialClosedCell] using
    isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc

theorem WeakAlgebra.weakUnitCube_subset_closedCell :
    AVenhance.unitCube ⊆ WeakAlgebra.weakSpatialClosedCell := by
  intro x hx
  simp only [WeakAlgebra.weakSpatialClosedCell, Set.mem_pi, Set.mem_univ,
    forall_true_left] at hx ⊢
  intro i
  have hi := hx i (Set.mem_univ _)
  exact ⟨le_of_lt hi.1, le_of_lt hi.2⟩

theorem WeakAlgebra.weak_unitCube_volume_lt_top : volume AVenhance.unitCube < ⊤ := by
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance weak_finite_unitCube :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  simpa only [Measure.restrict_apply_univ] using WeakAlgebra.weak_unitCube_volume_lt_top

theorem WeakAlgebra.weakTimeCube_measure_eq_product :
    (volume.restrict AVenhance.timeCube) =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube) := by
  rw [AVenhance.timeCube, Measure.prod_restrict,
    ← Measure.volume_eq_prod ℝ (Vec 2)]

local instance weak_finite_timeCube :
    IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [WeakAlgebra.weakTimeCube_measure_eq_product]
  infer_instance

theorem weak_continuous_memLp_two_timeCube {F : ℝ × Vec 2 → ℝ}
    (hF : Continuous F) :
    MemLp F 2 (volume.restrict AVenhance.timeCube) := by
  apply (memLp_two_iff_integrable_sq hF.measurable.aestronglyMeasurable).2
  exact (hF.pow 2).continuousOn.integrableOn_compact
    WeakAlgebra.weakTimeClosedCell_compact |>.mono_set WeakAlgebra.weakTimeCube_subset_closedCell

theorem weak_continuous_memL2On {f : Vec 2 → ℝ}
    (hf : Continuous f) : MemL2On AVenhance.unitCube f := by
  apply (memLp_two_iff_integrable_sq hf.measurable.aestronglyMeasurable).2
  exact (hf.pow 2).continuousOn.integrableOn_compact
    WeakAlgebra.weakSpatialClosedCell_compact |>.mono_set WeakAlgebra.weakUnitCube_subset_closedCell

theorem weak_continuous_timeCube_bound {F : ℝ × Vec 2 → ℝ}
    (hF : Continuous F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ AVenhance.timeCube, ‖F p‖ ≤ C := by
  have hbounded : Bornology.IsBounded (F '' WeakAlgebra.weakTimeClosedCell) :=
    WeakAlgebra.weakTimeClosedCell_compact.image hF |>.isBounded
  obtain ⟨C, hCpos, hC⟩ := hbounded.subset_ball_lt 0 0
  refine ⟨C, hCpos.le, ?_⟩
  intro p hp
  have hb := hC ⟨p, WeakAlgebra.weakTimeCube_subset_closedCell hp, rfl⟩
  have hb' : ‖F p‖ < C := by
    simpa [Metric.mem_ball, dist_eq_norm] using hb
  exact hb'.le

theorem weak_product_integrable_timeCube
    {f g : ℝ × Vec 2 → ℝ}
    (hf : MemLp f 2 (volume.restrict AVenhance.timeCube))
    (hg : MemLp g 2 (volume.restrict AVenhance.timeCube)) :
    Integrable (fun p => f p * g p) (volume.restrict AVenhance.timeCube) := by
  exact ((hf.mul hg : MemLp (fun p => f p * g p) 1
    (volume.restrict AVenhance.timeCube)).integrable le_rfl)

theorem weak_product_integrable_cell
    {f g : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f)
    (hg : MemL2On AVenhance.unitCube g) :
    Integrable (fun x => f x * g x)
      (volume.restrict AVenhance.unitCube) := by
  exact ((hf.mul hg : MemLp (fun x => f x * g x) 1
    (volume.restrict AVenhance.unitCube)).integrable le_rfl)

theorem WeakAlgebra.weak_l2_sub_sq_le {f g : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) (hg : MemL2On AVenhance.unitCube g) :
    AVenhance.l2NormSq (fun x => f x - g x) ≤
      2 * AVenhance.l2NormSq f + 2 * AVenhance.l2NormSq g := by
  have hsub : MemL2On AVenhance.unitCube (fun x => f x - g x) := hf.sub hg
  have hleft : Integrable (fun x => (f x - g x) ^ 2)
      (volume.restrict AVenhance.unitCube) :=
    (memLp_two_iff_integrable_sq hsub.aestronglyMeasurable).1 hsub
  have hfi : Integrable (fun x => f x ^ 2)
      (volume.restrict AVenhance.unitCube) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hgi : Integrable (fun x => g x ^ 2)
      (volume.restrict AVenhance.unitCube) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).1 hg
  have hright : Integrable (fun x => 2 * f x ^ 2 + 2 * g x ^ 2)
      (volume.restrict AVenhance.unitCube) := (hfi.const_mul 2).add (hgi.const_mul 2)
  have hmono := integral_mono_ae hleft hright (Filter.Eventually.of_forall fun x => by
    nlinarith [sq_nonneg (f x + g x)])
  change (∫ x in AVenhance.unitCube, (f x - g x) ^ 2) ≤ _
  have hsum :
      (∫ x in AVenhance.unitCube, 2 * f x ^ 2 + 2 * g x ^ 2) =
        2 * AVenhance.l2NormSq f + 2 * AVenhance.l2NormSq g := by
    rw [integral_add (hfi.const_mul 2) (hgi.const_mul 2)]
    simp [AVenhance.l2NormSq, integral_const_mul]
  exact hmono.trans_eq hsum

theorem WeakAlgebra.weakSpacetimeSpatialGradient_continuous
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2)) :
    Continuous (fun p : ℝ × Vec 2 => AVenhance.spaceGrad (φ p.1) p.2) := by
  apply continuous_pi
  intro i
  have hFderiv : Continuous (fderiv ℝ (fun p : ℝ × Vec 2 => φ p.1 p.2)) :=
    hφ.continuous_fderiv (by simp)
  have hcont : Continuous (fun p : ℝ × Vec 2 =>
      (fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p)
        (0, Homogenization.basisVec i)) := hFderiv.clm_apply continuous_const
  have heq (p : ℝ × Vec 2) :
      AVenhance.spaceGrad (φ p.1) p.2 i =
        (fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p)
          (0, Homogenization.basisVec i) := by
    let F : ℝ × Vec 2 → ℝ := fun q => φ q.1 q.2
    have houter : HasFDerivAt F (fderiv ℝ F (p.1, p.2)) (p.1, p.2) :=
      (hφ.differentiable (by simp) (p.1, p.2)).hasFDerivAt
    have hline : HasFDerivAt (fun x : Vec 2 => (p.1, x))
        (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hcomp := HasFDerivAt.comp p.2 houter hline
    have hlineEval : ContinuousLinearMap.inr ℝ ℝ (Vec 2)
        (Homogenization.basisVec i) = (0, Homogenization.basisVec i) := by
      simp [ContinuousLinearMap.inr]
    change fderiv ℝ (F ∘ fun x : Vec 2 => (p.1, x)) p.2
        (Homogenization.basisVec i) = _
    rw [hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply, hlineEval]
    rfl
  exact hcont.congr fun p => (heq p).symm

/-- Time, drift, and diffusion terms of the tested weak parabolic equation. -/
def weakEquationIntegrand (b : ℝ → Vec 2 → Vec 2) (κ : ℝ)
    (θ : ℝ → Vec 2 → ℝ) (Dθ : ℝ → Vec 2 → Vec 2)
    (φ : ℝ → Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  -(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1 +
    Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2 +
    κ * Homogenization.vecDot (Dθ p.1 p.2) (AVenhance.spaceGrad (φ p.1) p.2)

theorem weakEquationIntegrand_integrable
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    {φ : ℝ → Vec 2 → ℝ}
    (hθ : MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2
      (volume.restrict AVenhance.timeCube))
    (hDθ : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 i) 2
      (volume.restrict AVenhance.timeCube))
    (hDrift : Integrable (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2))
      (volume.restrict AVenhance.timeCube))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2)) :
    Integrable (weakEquationIntegrand b κ θ Dθ φ)
      (volume.restrict AVenhance.timeCube) := by
  let qtime : ℝ × Vec 2 → ℝ := fun p =>
    AVenhance.Infra.Parabolic.FourierGalerkin.spacetimeTestTimeDerivative φ p.1 p.2
  have hqtimeCont : Continuous qtime :=
    (AVenhance.Infra.Parabolic.FourierGalerkin.spacetimeTestTimeDerivative_contDiff hφ).continuous
  have hqtime := weak_continuous_memLp_two_timeCube hqtimeCont
  have hfirst := weak_product_integrable_timeCube hθ hqtime
  have hφbound := weak_continuous_timeCube_bound hφ.continuous
  have hφboundAE : ∀ᵐ p ∂(volume.restrict AVenhance.timeCube),
      ‖φ p.1 p.2‖ ≤ hφbound.choose := by
    filter_upwards [ae_restrict_mem (by
      rw [AVenhance.timeCube]
      exact measurableSet_Ioo.prod (by
        unfold AVenhance.unitCube
        exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)))] with p hp
    exact hφbound.choose_spec.2 p hp
  have hsecond := hDrift.mul_bdd hφ.continuous.measurable.aestronglyMeasurable
    hφboundAE
  let hgradCont := WeakAlgebra.weakSpacetimeSpatialGradient_continuous hφ
  have hgradLp (i : Fin 2) : MemLp (fun p : ℝ × Vec 2 =>
      AVenhance.spaceGrad (φ p.1) p.2 i) 2
      (volume.restrict AVenhance.timeCube) :=
    weak_continuous_memLp_two_timeCube ((continuous_apply i).comp hgradCont)
  have hthirdCoord (i : Fin 2) : Integrable (fun p : ℝ × Vec 2 =>
      Dθ p.1 p.2 i * AVenhance.spaceGrad (φ p.1) p.2 i)
      (volume.restrict AVenhance.timeCube) := weak_product_integrable_timeCube
        (hDθ i) (hgradLp i)
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hthirdCoord i)
  have hgradEq (p : ℝ × Vec 2) :
      Homogenization.vecDot (Dθ p.1 p.2) (AVenhance.spaceGrad (φ p.1) p.2) =
        ∑ i : Fin 2, Dθ p.1 p.2 i * AVenhance.spaceGrad (φ p.1) p.2 i := by
    rfl
  have htimeEq (p : ℝ × Vec 2) : qtime p = deriv (fun s => φ s p.2) p.1 := by
    rfl
  have hparts' : Integrable
      (((-(fun p : ℝ × Vec 2 => θ p.1 p.2 * qtime p) +
        (fun p => Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2)) +
        (fun p => κ * ∑ i : Fin 2,
          Dθ p.1 p.2 i * AVenhance.spaceGrad (φ p.1) p.2 i)))
      (volume.restrict AVenhance.timeCube) :=
    (hfirst.neg.add hsecond).add (hsum.const_mul κ)
  have heq : weakEquationIntegrand b κ θ Dθ φ =
      (((-(fun p : ℝ × Vec 2 => θ p.1 p.2 * qtime p) +
        (fun p => Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2)) +
        (fun p => κ * ∑ i : Fin 2,
          Dθ p.1 p.2 i * AVenhance.spaceGrad (φ p.1) p.2 i))) := by
    funext p
    simp [weakEquationIntegrand, htimeEq, hgradEq]
  have hthird : Integrable (weakEquationIntegrand b κ θ Dθ φ)
      (volume.restrict AVenhance.timeCube) := by
    rw [heq]
    exact hparts'
  exact hthird

theorem WeakAlgebra.weakPartialDerivOn_sub_univ
    {u v : Vec 2 → ℝ} {Du Dv : Vec 2 → ℝ}
    {i : Fin 2}
    (hu : MemL2On AVenhance.unitCube u) (hv : MemL2On AVenhance.unitCube v)
    (hDu : MemL2On AVenhance.unitCube Du) (hDv : MemL2On AVenhance.unitCube Dv)
    (hperU : AVenhance.IsZ2Periodic u) (hperV : AVenhance.IsZ2Periodic v)
    (hperDu : AVenhance.IsZ2Periodic Du) (hperDv : AVenhance.IsZ2Periodic Dv)
    (hweakU : HasWeakPartialDerivOn Set.univ i u Du)
    (hweakV : HasWeakPartialDerivOn Set.univ i v Dv) :
    HasWeakPartialDerivOn Set.univ i (fun x => u x - v x) (fun x => Du x - Dv x) := by
  intro φ hφ hφcompact hφsupport
  let w : Vec 2 → ℝ := fun x => (fderiv ℝ φ x) (basisVec i)
  have hwcont : Continuous w := by
    dsimp [w]
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hwcompact : HasCompactSupport w := by
    dsimp [w]
    exact hφcompact.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hleftU := AVenhance.Infra.Parabolic.FourierGalerkin.periodic_compact_pairing_integrable
    hu hperU hwcont hwcompact
  have hleftV := AVenhance.Infra.Parabolic.FourierGalerkin.periodic_compact_pairing_integrable
    hv hperV hwcont hwcompact
  have hrightU := AVenhance.Infra.Parabolic.FourierGalerkin.periodic_compact_pairing_integrable
    hDu hperDu hφ.continuous hφcompact
  have hrightV := AVenhance.Infra.Parabolic.FourierGalerkin.periodic_compact_pairing_integrable
    hDv hperDv hφ.continuous hφcompact
  have hleft :
      ∫ x, (u x - v x) * w x =
        (∫ x, u x * w x) - ∫ x, v x * w x := by
    have hpoint : (fun x => (u x - v x) * w x) =
        fun x => u x * w x - v x * w x := by
      funext x
      ring
    rw [hpoint, integral_sub hleftU hleftV]
  have hright :
      ∫ x, (Du x - Dv x) * φ x =
        (∫ x, Du x * φ x) - ∫ x, Dv x * φ x := by
    have hpoint : (fun x => (Du x - Dv x) * φ x) =
        fun x => Du x * φ x - Dv x * φ x := by
      funext x
      ring
    rw [hpoint, integral_sub hrightU hrightV]
  have hU : (∫ x, u x * w x) = -∫ x, Du x * φ x := by
    simpa only [MeasureTheory.setIntegral_univ] using
      hweakU φ hφ hφcompact (Set.subset_univ _)
  have hV : (∫ x, v x * w x) = -∫ x, Dv x * φ x := by
    simpa only [MeasureTheory.setIntegral_univ] using
      hweakV φ hφ hφcompact (Set.subset_univ _)
  rw [MeasureTheory.setIntegral_univ, MeasureTheory.setIntegral_univ]
  calc
    ∫ x, (u x - v x) * w x = (∫ x, u x * w x) - ∫ x, v x * w x := hleft
    _ = -(∫ x, Du x * φ x) + ∫ x, Dv x * φ x := by rw [hU, hV]; abel
    _ = -((∫ x, Du x * φ x) - ∫ x, Dv x * φ x) := by abel
    _ = -∫ x, (Du x - Dv x) * φ x := congrArg Neg.neg hright.symm

/-- The periodic `H¹` witnesses are closed under subtraction, with the expected weak
gradient. -/
theorem isPeriodicH1With_sub
    {u v : Vec 2 → ℝ} {Du Dv : Vec 2 → Vec 2}
    (hu : AVenhance.IsPeriodicH1With u Du)
    (hv : AVenhance.IsPeriodicH1With v Dv) :
    AVenhance.IsPeriodicH1With (fun x => u x - v x) (fun x => Du x - Dv x) := by
  rcases hu with ⟨hperU, hperDu, hU, hDu, hweakU⟩
  rcases hv with ⟨hperV, hperDv, hV, hDv, hweakV⟩
  refine ⟨?_, ?_, hU.sub hV, ?_, ?_⟩
  · intro k x
    simp [hperU k x, hperV k x]
  · intro k x
    funext i
    simp [hperDu k x, hperDv k x]
  · intro i
    change MemLp (fun x => Du x i - Dv x i) 2 (volume.restrict AVenhance.unitCube)
    exact (hDu i).sub (hDv i)
  · intro i
    exact WeakAlgebra.weakPartialDerivOn_sub_univ hU hV (hDu i) (hDv i)
      hperU hperV (fun k x => congrFun (hperDu k x) i)
      (fun k x => congrFun (hperDv k x) i) (hweakU i) (hweakV i)

theorem WeakAlgebra.weak_vecDot_sub_right (v u w : Vec 2 → Vec 2) (x : Vec 2) :
    Homogenization.vecDot (v x) (u x - w x) =
      Homogenization.vecDot (v x) (u x) - Homogenization.vecDot (v x) (w x) := by
  unfold Homogenization.vecDot
  calc
    (∑ i, v x i * (u x i - w x i)) =
        ∑ i, (v x i * u x i - v x i * w x i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, v x i * u x i) - ∑ i, v x i * w x i := by
      rw [Finset.sum_sub_distrib]

theorem WeakAlgebra.weak_vecDot_sub_left (u w v : Vec 2 → Vec 2) (x : Vec 2) :
    Homogenization.vecDot (u x - w x) (v x) =
      Homogenization.vecDot (u x) (v x) - Homogenization.vecDot (w x) (v x) := by
  unfold Homogenization.vecDot
  calc
    (∑ i, (u x i - w x i) * v x i) =
        ∑ i, (u x i * v x i - w x i * v x i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, u x i * v x i) - ∑ i, w x i * v x i := by
      rw [Finset.sum_sub_distrib]

theorem WeakAlgebra.weakEquationIntegrand_sub
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {θ η : ℝ → Vec 2 → ℝ} {D E : ℝ → Vec 2 → Vec 2}
    (φ : ℝ → Vec 2 → ℝ) (p : ℝ × Vec 2) :
    weakEquationIntegrand b κ (fun t x => θ t x - η t x)
        (fun t x => D t x - E t x) φ p =
      weakEquationIntegrand b κ θ D φ p - weakEquationIntegrand b κ η E φ p := by
  simp [weakEquationIntegrand, WeakAlgebra.weak_vecDot_sub_right, WeakAlgebra.weak_vecDot_sub_left]
  ring

/-- Difference of two solutions of the same equation is a weak solution with the
corresponding difference datum and difference gradient. -/
theorem isWeakSolutionGrad_sub
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {f g : Vec 2 → ℝ} {θ η : ℝ → Vec 2 → ℝ}
    {D E : ℝ → Vec 2 → Vec 2}
    (hf : MemL2On AVenhance.unitCube f) (hg : MemL2On AVenhance.unitCube g)
    (hθ : AVenhance.IsWeakSolutionGrad b κ f θ D)
    (hη : AVenhance.IsWeakSolutionGrad b κ g η E) :
    AVenhance.IsWeakSolutionGrad b κ (fun x => f x - g x)
      (fun t x => θ t x - η t x) (fun t x => D t x - E t x) := by
  rcases hθ with ⟨hθpoint, hθbound, hθscalar, hθgradient, hθH1,
    hθdrift, hθpairing, hθweak⟩
  rcases hη with ⟨hηpoint, hηbound, hηscalar, hηgradient, hηH1,
    hηdrift, hηpairing, hηweak⟩
  refine ⟨?_, ?_, hθscalar.sub hηscalar, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases hθpoint t ht with ⟨hθper, hθcell⟩
    rcases hηpoint t ht with ⟨hηper, hηcell⟩
    constructor
    · intro k x
      simp [hθper k x, hηper k x]
    · exact hθcell.sub hηcell
  · obtain ⟨Cθ, hCθ⟩ := hθbound
    obtain ⟨Cη, hCη⟩ := hηbound
    refine ⟨2 * max Cθ 0 + 2 * max Cη 0, ?_⟩
    intro t ht
    have hθmem := (hθpoint t ht).2
    have hηmem := (hηpoint t ht).2
    have hsub := WeakAlgebra.weak_l2_sub_sq_le hθmem hηmem
    calc
      AVenhance.l2NormSq (fun x => θ t x - η t x) ≤
          2 * AVenhance.l2NormSq (θ t) + 2 * AVenhance.l2NormSq (η t) := hsub
      _ ≤ 2 * max Cθ 0 + 2 * max Cη 0 := by
        have hθle := hCθ t ht
        have hηle := hCη t ht
        have hθmax : AVenhance.l2NormSq (θ t) ≤ max Cθ 0 := hθle.trans (le_max_left _ _)
        have hηmax : AVenhance.l2NormSq (η t) ≤ max Cη 0 := hηle.trans (le_max_left _ _)
        nlinarith
  · intro i
    change MemLp (fun p : ℝ × Vec 2 => D p.1 p.2 i - E p.1 p.2 i) 2
      (volume.restrict AVenhance.timeCube)
    exact (hθgradient i).sub (hηgradient i)
  · filter_upwards [hθH1, hηH1] with t hθt hηt
    exact isPeriodicH1With_sub hθt hηt
  · have hpoint : (fun p : ℝ × Vec 2 =>
        Homogenization.vecDot (b p.1 p.2) (D p.1 p.2 - E p.1 p.2)) =
      (fun p => Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) -
        Homogenization.vecDot (b p.1 p.2) (E p.1 p.2)) := by
      funext p
      exact WeakAlgebra.weak_vecDot_sub_right (b p.1) (D p.1) (E p.1) p.2
    exact (hθdrift.sub hηdrift).congr
      (Filter.Eventually.of_forall fun p => congrFun hpoint.symm p)
  · intro ψ hψ hψper
    have hψmem : MemL2On AVenhance.unitCube ψ := weak_continuous_memL2On hψ.continuous
    have hpairEq (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
        (∫ x in AVenhance.unitCube, (θ t x - η t x) * ψ x) =
          (∫ x in AVenhance.unitCube, θ t x * ψ x) -
            ∫ x in AVenhance.unitCube, η t x * ψ x := by
      have hθψ := weak_product_integrable_cell (hθpoint t ht).2 hψmem
      have hηψ := weak_product_integrable_cell (hηpoint t ht).2 hψmem
      have hpoint : (fun x => (θ t x - η t x) * ψ x) =
          fun x => θ t x * ψ x - η t x * ψ x := by
        funext x
        ring
      rw [hpoint, integral_sub hθψ hηψ]
    apply ContinuousOn.congr ((hθpairing ψ hψ hψper).sub
      (hηpairing ψ hψ hψper))
    intro t ht
    exact hpairEq t ht
  · intro φ htest
    have hφsmooth := htest.1
    have hφ0smooth : ContDiff ℝ (⊤ : ℕ∞) (φ 0) := by
      exact hφsmooth.comp (contDiff_const.prodMk contDiff_id)
    have hφ0mem : MemL2On AVenhance.unitCube (φ 0) :=
      weak_continuous_memL2On hφ0smooth.continuous
    have hRhsF := weak_product_integrable_cell hf hφ0mem
    have hRhsG := weak_product_integrable_cell hg hφ0mem
    have hRhs :
        (∫ x in AVenhance.unitCube, (f x - g x) * φ 0 x) =
          (∫ x in AVenhance.unitCube, f x * φ 0 x) -
            ∫ x in AVenhance.unitCube, g x * φ 0 x := by
      have hpoint : (fun x => (f x - g x) * φ 0 x) =
          fun x => f x * φ 0 x - g x * φ 0 x := by
        funext x
        ring
      rw [hpoint, integral_sub hRhsF hRhsG]
    have hθint := weakEquationIntegrand_integrable (κ := κ) hθscalar hθgradient
      hθdrift hφsmooth
    have hηint := weakEquationIntegrand_integrable (κ := κ) hηscalar hηgradient
      hηdrift hφsmooth
    have hθeq := hθweak φ htest
    have hηeq := hηweak φ htest
    change (∫ p in AVenhance.timeCube,
        weakEquationIntegrand b κ θ D φ p) =
      ∫ x in AVenhance.unitCube, f x * φ 0 x at hθeq
    change (∫ p in AVenhance.timeCube,
        weakEquationIntegrand b κ η E φ p) =
      ∫ x in AVenhance.unitCube, g x * φ 0 x at hηeq
    have htimeEq :
        (∫ p in AVenhance.timeCube,
          weakEquationIntegrand b κ (fun t x => θ t x - η t x)
            (fun t x => D t x - E t x) φ p) =
          (∫ p in AVenhance.timeCube, weakEquationIntegrand b κ θ D φ p) -
            ∫ p in AVenhance.timeCube, weakEquationIntegrand b κ η E φ p := by
      have hpoint : weakEquationIntegrand b κ (fun t x => θ t x - η t x)
          (fun t x => D t x - E t x) φ =ᵐ[volume.restrict AVenhance.timeCube]
          fun p => weakEquationIntegrand b κ θ D φ p -
            weakEquationIntegrand b κ η E φ p :=
        Filter.Eventually.of_forall fun p => WeakAlgebra.weakEquationIntegrand_sub φ p
      calc
        _ = ∫ p in AVenhance.timeCube,
            weakEquationIntegrand b κ θ D φ p -
              weakEquationIntegrand b κ η E φ p := integral_congr_ae hpoint
        _ = _ := integral_sub hθint hηint
    change (∫ p in AVenhance.timeCube,
        weakEquationIntegrand b κ (fun t x => θ t x - η t x)
          (fun t x => D t x - E t x) φ p) =
      ∫ x in AVenhance.unitCube, (f x - g x) * φ 0 x
    calc
      _ = (∫ p in AVenhance.timeCube, weakEquationIntegrand b κ θ D φ p) -
          ∫ p in AVenhance.timeCube, weakEquationIntegrand b κ η E φ p := htimeEq
      _ = (∫ x in AVenhance.unitCube, f x * φ 0 x) -
          ∫ x in AVenhance.unitCube, g x * φ 0 x := by rw [hθeq, hηeq]
      _ = _ := hRhs.symm

end AVenhance.Infra.Parabolic.WeakUniqueness

end
