/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanMildParabolicSchauder
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherFunctionSpaceCore
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Full parabolic C2,alpha control of the Euclidean mild heat solution

This module connects the explicit Euclidean heat-kernel construction to the
generic higher parabolic Holder function-space API.  It first identifies the
independently auditable Euclidean second jet with `ParabolicSecondJet`, then
packages the Hessian and time-derivative estimates on finite positive-time
cylinders.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

section JetAdapter

/-- The explicit Euclidean jet is a generic parabolic second jet.  This is a
lossless adapter: the derivative fields and all three derivative witnesses are
preserved definitionally. -/
def EuclideanParabolicSecondJetND.toParabolicSecondJet
    {n : ℕ} {u : ℝ × (Fin n → ℝ) → ℝ}
    {s : Set (ℝ × (Fin n → ℝ))}
    (J : EuclideanParabolicSecondJetND u s) :
    ParabolicSecondJet u s where
  timeDeriv := J.timeDeriv
  spaceDeriv := J.spaceDeriv
  spaceSecondDeriv := J.spaceSecondDeriv
  hasTimeDeriv := by
    intro z hz
    simpa [timeSliceDomain] using J.hasTimeDeriv hz
  hasSpaceDeriv := by
    intro z hz
    simpa [spaceSliceDomain] using J.hasSpaceDeriv hz
  hasSpaceSecondDeriv := by
    intro z hz
    simpa [spaceSliceDomain] using J.hasSpaceSecondDeriv hz

/-- The actual mild heat-kernel solution, viewed through the repository's
generic parabolic second-jet interface. -/
def heatMildGenericParabolicSecondJetND
    {n : ℕ} {t₀ r : ℝ} (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ParabolicSecondJet (heatMildSpaceTimeND t₀ u₀ q)
      (Set.Ioi t₀ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
  (heatMildParabolicSecondJetND (t₀ := t₀) hr0 u₀ hq hH hqb hqholder).toParabolicSecondJet

@[simp] theorem heatMildGenericParabolicSecondJetND_timeDeriv
    {n : ℕ} {t₀ r : ℝ} (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    (heatMildGenericParabolicSecondJetND (t₀ := t₀) hr0 u₀ hq hH hqb hqholder).timeDeriv =
      heatMildTimeDerivND t₀ u₀ q := by
  rfl

@[simp] theorem heatMildGenericParabolicSecondJetND_spaceDeriv
    {n : ℕ} {t₀ r : ℝ} (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    (heatMildGenericParabolicSecondJetND (t₀ := t₀) hr0 u₀ hq hH hqb hqholder).spaceDeriv =
      fun z ↦ heatMildSpatialGradientCLM t₀ z.1 u₀ q z.2 := by
  rfl

@[simp] theorem heatMildGenericParabolicSecondJetND_spaceSecondDeriv
    {n : ℕ} {t₀ r : ℝ} (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    (heatMildGenericParabolicSecondJetND (t₀ := t₀) hr0 u₀ hq hH hqb hqholder).spaceSecondDeriv =
      heatMildSpaceHessianND t₀ hr0 u₀ hq hH hqb hqholder := by
  rfl

end JetAdapter

section FiniteCylinderHessian

local instance mildC2AlphaCoordinateDualNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance mildC2AlphaCoordinateBilinearNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance mildC2AlphaCoordinateBilinearContinuousAdd {n : ℕ} :
    ContinuousAdd ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  IsTopologicalAddGroup.toContinuousAdd

/-- The finite positive-time cylinder `(t₀,T] × ℝⁿ`. -/
def euclideanMildFiniteCylinderND (n : ℕ) (t₀ T : ℝ) :
    Set (ℝ × (Fin n → ℝ)) :=
  Set.Ioc t₀ T ×ˢ Set.univ

@[simp] theorem mem_euclideanMildFiniteCylinderND
    {n : ℕ} {t₀ T : ℝ} {z : ℝ × (Fin n → ℝ)} :
    z ∈ euclideanMildFiniteCylinderND n t₀ T ↔ t₀ < z.1 ∧ z.1 ≤ T := by
  simp [euclideanMildFiniteCylinderND]

/-- The genuine heat-kernel second jet restricted to a finite positive-time
cylinder. -/
def heatMildFiniteParabolicSecondJetND
    {n : ℕ} {t₀ T r : ℝ} (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ParabolicSecondJet (heatMildSpaceTimeND t₀ u₀ q)
      (euclideanMildFiniteCylinderND n t₀ T) :=
  (heatMildGenericParabolicSecondJetND (t₀ := t₀) hr0 u₀ hq hH hqb hqholder).restrict
    (by
      intro z hz
      exact ⟨(mem_euclideanMildFiniteCylinderND.mp hz).1, Set.mem_univ z.2⟩)

@[simp] theorem heatMildFiniteParabolicSecondJetND_timeDeriv
    {n : ℕ} {t₀ T r : ℝ} (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    (heatMildFiniteParabolicSecondJetND (t₀ := t₀) (T := T) hr0 u₀ hq hH hqb
      hqholder).timeDeriv = heatMildTimeDerivND t₀ u₀ q := by
  rfl

@[simp] theorem heatMildFiniteParabolicSecondJetND_spaceDeriv
    {n : ℕ} {t₀ T r : ℝ} (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    (heatMildFiniteParabolicSecondJetND (t₀ := t₀) (T := T) hr0 u₀ hq hH hqb
      hqholder).spaceDeriv =
      fun z ↦ heatMildSpatialGradientCLM t₀ z.1 u₀ q z.2 := by
  rfl

@[simp] theorem heatMildFiniteParabolicSecondJetND_spaceSecondDeriv
    {n : ℕ} {t₀ T r : ℝ} (hr0 : 0 < r)
    (D : EuclideanBoundedC2Data n)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    (heatMildFiniteParabolicSecondJetND (t₀ := t₀) (T := T) hr0 D.value hq hH hqb
      hqholder).spaceSecondDeriv =
      heatMildHessianFieldND t₀ hr0 D hq hH hqb hqholder := by
  rfl

/-- Uniform Hessian sup constant on `(t₀,T] × ℝⁿ`, using the
non-singular bounded-`C²` initial endpoint. -/
def heatMildHessianSupConstantND {n : ℕ}
    (t₀ T r H : ℝ) (D : EuclideanBoundedC2Data n) : ℝ :=
  (∑ j : Fin n, ∑ k : Fin n, ‖D.second j k‖) +
    ∑ j : Fin n, ∑ k : Fin n,
      H * heatHessianEntryHolderMoment n r j k *
        ((T - t₀) ^ (r / 2) / (r / 2))

lemma heatMildHessianSupConstantND_nonneg
    {n : ℕ} {t₀ T r H : ℝ} (hT : t₀ ≤ T) (hr0 : 0 < r)
    (hH : 0 ≤ H) (D : EuclideanBoundedC2Data n) :
    0 ≤ heatMildHessianSupConstantND t₀ T r H D := by
  unfold heatMildHessianSupConstantND
  apply add_nonneg
  · exact Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun k _ ↦ norm_nonneg _
  · exact Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun k _ ↦
      mul_nonneg
        (mul_nonneg hH (heatHessianEntryHolderMoment_nonneg n r j k))
        (div_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hT) _) (by positivity))

lemma heatMildHessianParabolicHolderConstant_nonneg
    (n : ℕ) {r H₀ H : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hH₀ : 0 ≤ H₀) (hH : 0 ≤ H) :
    0 ≤ heatMildHessianParabolicHolderConstant n r H₀ H := by
  unfold heatMildHessianParabolicHolderConstant
  exact add_nonneg
    (add_nonneg
      (heatInitialHessianSpatialHolderConstant_nonneg n hH₀)
      (heatInitialHessianTimeHolderConstant_nonneg n r hH₀))
    (add_nonneg
      (heatDuhamelHessianSpatialHolderConstant_nonneg n hr0 hr1 hH)
      (heatDuhamelHessianTimeHolderConstant_nonneg n hr0 hr1 hH))

/-- Uniform pointwise Hessian bound on a finite positive-time cylinder. -/
theorem parabolicBoundedWith_heatMildHessianFieldND_Ioc
    {n : ℕ} {t₀ T r : ℝ} (hT : t₀ ≤ T) (hr0 : 0 < r)
    (D : EuclideanBoundedC2Data n)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ParabolicBoundedWith (heatMildHessianSupConstantND t₀ T r H D)
      (heatMildHessianFieldND t₀ hr0 D hq hH hqb hqholder)
      (euclideanMildFiniteCylinderND n t₀ T) := by
  rintro ⟨t, x⟩ hz
  have ht : t₀ < t := (mem_euclideanMildFiniteCylinderND.mp hz).1
  have htT : t ≤ T := (mem_euclideanMildFiniteCylinderND.mp hz).2
  simp only [heatMildHessianFieldND, dif_pos ht]
  refine (norm_heatMildSpatialHessianCLM_le_of_boundedC2
    ht hr0 D hq hH hqb hqholder x).trans ?_
  unfold heatMildHessianSupConstantND
  refine add_le_add le_rfl ?_
  apply Finset.sum_le_sum
  intro j _hj
  apply Finset.sum_le_sum
  intro k _hk
  have hbase : 0 ≤ t - t₀ := sub_nonneg.mpr ht.le
  have hbase_le : t - t₀ ≤ T - t₀ := sub_le_sub_right htT t₀
  have hexp : 0 ≤ r / 2 := by positivity
  have hpow : (t - t₀) ^ (r / 2) ≤ (T - t₀) ^ (r / 2) :=
    Real.rpow_le_rpow hbase hbase_le hexp
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hpow (by positivity))
    (mul_nonneg hH (heatHessianEntryHolderMoment_nonneg n r j k))

/-- The full Hessian has an explicit `C^{0,r}` bound on every finite
positive-time cylinder. -/
theorem parabolicC0AlphaWith_heatMildHessianFieldND_Ioc
    {n : ℕ} {t₀ T r : ℝ} (hT : t₀ ≤ T) (hr0 : 0 < r) (hr1 : r < 1)
    (D : EuclideanBoundedC2Data n) {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ParabolicC0AlphaWith
      (heatMildHessianSupConstantND t₀ T r H D)
      (heatMildHessianParabolicHolderConstant n r H₀ H) r
      (heatMildHessianFieldND t₀ hr0 D hq hH hqb hqholder)
      (euclideanMildFiniteCylinderND n t₀ T) := by
  refine ⟨parabolicBoundedWith_heatMildHessianFieldND_Ioc
    hT hr0 D hq hH hqb hqholder, ?_⟩
  refine (parabolicHolderWith_heatMildHessianFieldND
    t₀ hr0 hr1 D hH₀ hsecondHolder hq hH hqb hqholder).mono_set ?_
  intro z hz
  exact (mem_euclideanMildFiniteCylinderND.mp hz).1

/-- Norm-ball form of the finite-cylinder Hessian Schauder estimate. -/
theorem parabolicC0AlphaNormLe_heatMildHessianFieldND_Ioc
    {n : ℕ} {t₀ T r : ℝ} (hT : t₀ ≤ T) (hr0 : 0 < r) (hr1 : r < 1)
    (D : EuclideanBoundedC2Data n) {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ParabolicC0AlphaNormLe
      (heatMildHessianSupConstantND t₀ T r H D +
        heatMildHessianParabolicHolderConstant n r H₀ H) r
      (heatMildHessianFieldND t₀ hr0 D hq hH hqb hqholder)
      (euclideanMildFiniteCylinderND n t₀ T) := by
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (heatMildHessianSupConstantND_nonneg hT hr0 hH D)
    (heatMildHessianParabolicHolderConstant_nonneg n hr0 hr1 hH₀ hH)
    (parabolicC0AlphaWith_heatMildHessianFieldND_Ioc
      hT hr0 hr1 D hH₀ hsecondHolder hq hH hqb hqholder)

end FiniteCylinderHessian

section FiniteCylinderTimeDerivative

local instance mildTimeCoordinateDualNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance mildTimeCoordinateBilinearNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance mildTimeCoordinateBilinearContinuousAdd {n : ℕ} :
    ContinuousAdd ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  IsTopologicalAddGroup.toContinuousAdd

/-- The difference of the standard-basis traces of two bilinear operators is
bounded by dimension times their operator-norm difference. -/
lemma abs_standardBasisTrace_sub_le {n : ℕ}
    (A B : (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :
    |∑ k : Fin n, A (Pi.single k 1) (Pi.single k 1) -
        ∑ k : Fin n, B (Pi.single k 1) (Pi.single k 1)| ≤
      (n : ℝ) * ‖A - B‖ := by
  rw [← Finset.sum_sub_distrib]
  simpa only [sub_apply] using abs_sum_standardBasis_diag_le (A - B)

/-- Uniform sup constant for `∂ₜu = Δu + q` on the finite cylinder. -/
def heatMildTimeDerivSupConstantND {n : ℕ}
    (t₀ T r H C : ℝ) (D : EuclideanBoundedC2Data n) : ℝ :=
  (n : ℝ) * heatMildHessianSupConstantND t₀ T r H D + C

/-- Parabolic Holder constant for `∂ₜu = Δu + q`: taking the
Hessian trace costs at most the dimension, and the source contributes its own
parabolic Holder constant. -/
def heatMildTimeDerivParabolicHolderConstantND
    (n : ℕ) (r H₀ H Hq : ℝ) : ℝ :=
  (n : ℝ) * heatMildHessianParabolicHolderConstant n r H₀ H + Hq

lemma heatMildTimeDerivSupConstantND_nonneg
    {n : ℕ} {t₀ T r H C : ℝ} (hT : t₀ ≤ T) (hr0 : 0 < r)
    (hH : 0 ≤ H) (hC : 0 ≤ C) (D : EuclideanBoundedC2Data n) :
    0 ≤ heatMildTimeDerivSupConstantND t₀ T r H C D := by
  unfold heatMildTimeDerivSupConstantND
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg n)
      (heatMildHessianSupConstantND_nonneg hT hr0 hH D)) hC

lemma heatMildTimeDerivParabolicHolderConstantND_nonneg
    (n : ℕ) {r H₀ H Hq : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hH₀ : 0 ≤ H₀) (hH : 0 ≤ H) (hHq : 0 ≤ Hq) :
    0 ≤ heatMildTimeDerivParabolicHolderConstantND n r H₀ H Hq := by
  unfold heatMildTimeDerivParabolicHolderConstantND
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg n)
      (heatMildHessianParabolicHolderConstant_nonneg n hr0 hr1 hH₀ hH)) hHq

/-- Uniform pointwise bound for the actual time derivative on `(t₀,T]`. -/
theorem parabolicBoundedWith_heatMildTimeDerivND_Ioc
    {n : ℕ} {t₀ T r : ℝ} (hT : t₀ ≤ T) (hr0 : 0 < r)
    (D : EuclideanBoundedC2Data n)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ParabolicBoundedWith (heatMildTimeDerivSupConstantND t₀ T r H C D)
      (heatMildTimeDerivND t₀ D.value q)
      (euclideanMildFiniteCylinderND n t₀ T) := by
  rintro ⟨t, x⟩ hz
  have ht : t₀ < t := (mem_euclideanMildFiniteCylinderND.mp hz).1
  rw [heatMildTimeDerivND, if_pos ht, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans ?_
  have hLap := abs_heatMildSpatialLaplacianND_le
    ht hr0 D.value hq hH hqb hqholder x
  have hHess := parabolicBoundedWith_heatMildHessianFieldND_Ioc
    hT hr0 D hq hH hqb hqholder hz
  have hHess' :
      ‖heatMildSpatialHessianCLM ht.le hr0 D.value hq hH hqb hqholder x‖ ≤
        heatMildHessianSupConstantND t₀ T r H D := by
    simpa only [heatMildHessianFieldND, dif_pos ht] using hHess
  unfold heatMildTimeDerivSupConstantND
  exact add_le_add
    (hLap.trans (mul_le_mul_of_nonneg_left hHess' (Nat.cast_nonneg n)))
    (by simpa only [Real.norm_eq_abs] using hqb t x)

/-- The actual time derivative is parabolically Holder whenever the source
itself is parabolically Holder.  No time regularity stronger than the stated
`C^{0,r}` source hypothesis is assumed. -/
theorem parabolicHolderWith_heatMildTimeDerivND_Ioc
    {n : ℕ} {t₀ T r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (D : EuclideanBoundedC2Data n) {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {Hq : ℝ}
    (hqParabolic : ParabolicHolderWith Hq r
      (fun z : ℝ × (Fin n → ℝ) ↦ q z.1 z.2)
      (euclideanMildFiniteCylinderND n t₀ T)) :
    ParabolicHolderWith
      (heatMildTimeDerivParabolicHolderConstantND n r H₀ H Hq) r
      (heatMildTimeDerivND t₀ D.value q)
      (euclideanMildFiniteCylinderND n t₀ T) := by
  have hHessian :=
    (parabolicHolderWith_heatMildHessianFieldND
      t₀ hr0 hr1 D hH₀ hsecondHolder hq hH hqb hqholder).mono_set
      (show euclideanMildFiniteCylinderND n t₀ T ⊆
          {p : ℝ × (Fin n → ℝ) | t₀ < p.1} from
        fun z hz ↦ (mem_euclideanMildFiniteCylinderND.mp hz).1)
  intro p hp z hz
  have hp0 : t₀ < p.1 := (mem_euclideanMildFiniteCylinderND.mp hp).1
  have hz0 : t₀ < z.1 := (mem_euclideanMildFiniteCylinderND.mp hz).1
  simp only [heatMildTimeDerivND, if_pos hp0, if_pos hz0, Real.norm_eq_abs]
  have hLap :
      |heatMildSpatialLaplacianND t₀ p.1 D.value q p.2 -
          heatMildSpatialLaplacianND t₀ z.1 D.value q z.2| ≤
        (n : ℝ) *
          ‖heatMildHessianFieldND t₀ hr0 D hq hH hqb hqholder p -
            heatMildHessianFieldND t₀ hr0 D hq hH hqb hqholder z‖ := by
    rw [← sum_heatMildSpatialHessianCLM_diag_eq_laplacian
      hp0 hr0 D.value hq hH hqb hqholder p.2]
    rw [← sum_heatMildSpatialHessianCLM_diag_eq_laplacian
      hz0 hr0 D.value hq hH hqb hqholder z.2]
    simpa only [heatMildHessianFieldND, dif_pos hp0, dif_pos hz0] using
      abs_standardBasisTrace_sub_le
        (heatMildHessianFieldND t₀ hr0 D hq hH hqb hqholder p)
        (heatMildHessianFieldND t₀ hr0 D hq hH hqb hqholder z)
  have hLapHolder := hLap.trans
    (mul_le_mul_of_nonneg_left (hHessian hp hz) (Nat.cast_nonneg n))
  have hLapHolder' :
      |heatMildSpatialLaplacianND t₀ p.1 D.value q p.2 -
          heatMildSpatialLaplacianND t₀ z.1 D.value q z.2| ≤
        ((n : ℝ) * heatMildHessianParabolicHolderConstant n r H₀ H) *
          parabolicDistance p z ^ r := by
    simpa only [mul_assoc] using hLapHolder
  have hsource := hqParabolic hp hz
  have hsplit :
      (heatMildSpatialLaplacianND t₀ p.1 D.value q p.2 + q p.1 p.2) -
          (heatMildSpatialLaplacianND t₀ z.1 D.value q z.2 + q z.1 z.2) =
        (heatMildSpatialLaplacianND t₀ p.1 D.value q p.2 -
          heatMildSpatialLaplacianND t₀ z.1 D.value q z.2) +
        (q p.1 p.2 - q z.1 z.2) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  calc
    |heatMildSpatialLaplacianND t₀ p.1 D.value q p.2 -
          heatMildSpatialLaplacianND t₀ z.1 D.value q z.2| +
        |q p.1 p.2 - q z.1 z.2| ≤
      ((n : ℝ) * heatMildHessianParabolicHolderConstant n r H₀ H) *
          parabolicDistance p z ^ r +
        Hq * parabolicDistance p z ^ r := by
      exact add_le_add hLapHolder' (by simpa only [Real.norm_eq_abs] using hsource)
    _ = heatMildTimeDerivParabolicHolderConstantND n r H₀ H Hq *
        parabolicDistance p z ^ r := by
      unfold heatMildTimeDerivParabolicHolderConstantND
      ring

/-- Full `C^{0,r}` control of the actual time derivative on a finite
positive-time cylinder. -/
theorem parabolicC0AlphaWith_heatMildTimeDerivND_Ioc
    {n : ℕ} {t₀ T r : ℝ} (hT : t₀ ≤ T) (hr0 : 0 < r) (hr1 : r < 1)
    (D : EuclideanBoundedC2Data n) {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H Hq : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (hqParabolic : ParabolicHolderWith Hq r
      (fun z : ℝ × (Fin n → ℝ) ↦ q z.1 z.2)
      (euclideanMildFiniteCylinderND n t₀ T)) :
    ParabolicC0AlphaWith
      (heatMildTimeDerivSupConstantND t₀ T r H C D)
      (heatMildTimeDerivParabolicHolderConstantND n r H₀ H Hq) r
      (heatMildTimeDerivND t₀ D.value q)
      (euclideanMildFiniteCylinderND n t₀ T) :=
  ⟨parabolicBoundedWith_heatMildTimeDerivND_Ioc
      hT hr0 D hq hH hqb hqholder,
    parabolicHolderWith_heatMildTimeDerivND_Ioc
      hr0 hr1 D hH₀ hsecondHolder hq hH hqb hqholder hqParabolic⟩

/-- Norm-ball form of the finite-cylinder time-derivative estimate. -/
theorem parabolicC0AlphaNormLe_heatMildTimeDerivND_Ioc
    {n : ℕ} {t₀ T r : ℝ} (hT : t₀ ≤ T) (hr0 : 0 < r) (hr1 : r < 1)
    (D : EuclideanBoundedC2Data n) {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H Hq : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hHq : 0 ≤ Hq) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (hqParabolic : ParabolicHolderWith Hq r
      (fun z : ℝ × (Fin n → ℝ) ↦ q z.1 z.2)
      (euclideanMildFiniteCylinderND n t₀ T)) :
    ParabolicC0AlphaNormLe
      (heatMildTimeDerivSupConstantND t₀ T r H C D +
        heatMildTimeDerivParabolicHolderConstantND n r H₀ H Hq) r
      (heatMildTimeDerivND t₀ D.value q)
      (euclideanMildFiniteCylinderND n t₀ T) := by
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (heatMildTimeDerivSupConstantND_nonneg hT hr0 hH hC D)
    (heatMildTimeDerivParabolicHolderConstantND_nonneg
      n hr0 hr1 hH₀ hH hHq)
    (parabolicC0AlphaWith_heatMildTimeDerivND_Ioc
      hT hr0 hr1 D hH₀ hsecondHolder hq hH hqb hqholder hqParabolic)

end FiniteCylinderTimeDerivative

section LowerOrderInterpolation

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]

/-- A bounded field with a Lipschitz estimate at parabolic distances at most
one is globally Holder of every exponent in `(0,1]`.  At large distances the
sup bound controls the oscillation. -/
lemma parabolicHolderWith_of_bounded_of_unit_lipschitz
    {B L r : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (hr0 : 0 < r) (hr1 : r ≤ 1)
    {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hb : ParabolicBoundedWith B u s)
    (hlocal : ∀ ⦃p⦄, p ∈ s → ∀ ⦃q⦄, q ∈ s →
      parabolicDistance p q ≤ 1 →
      ‖u p - u q‖ ≤ L * parabolicDistance p q) :
    ParabolicHolderWith (2 * B + L) r u s := by
  intro p hp q hq
  let d := parabolicDistance p q
  have hd0 : 0 ≤ d := parabolicDistance.nonneg p q
  by_cases hd1 : d ≤ 1
  · have hpow : d ≤ d ^ r := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' hd0 hd1 hr0.le hr1
    exact (hlocal hp hq hd1).trans <|
      calc
        L * d ≤ L * d ^ r := mul_le_mul_of_nonneg_left hpow hL
        _ ≤ (2 * B + L) * d ^ r := by
          exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hd0 r)
  · have hd1' : 1 ≤ d := le_of_not_ge hd1
    have hpow : 1 ≤ d ^ r := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hd1' hr0.le
    calc
      ‖u p - u q‖ ≤ ‖u p‖ + ‖u q‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hb hp) (hb hq)
      _ = 2 * B := by ring
      _ ≤ (2 * B + L) * d ^ r := by nlinarith [Real.rpow_nonneg hd0 r]

section EuclideanJet

variable {n : ℕ}

local instance lowerCoordinateDualNormedAddCommGroup :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance lowerCoordinateBilinearNormedAddCommGroup :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- On a full spatial cylinder, a second jet whose gradient and time
derivative are uniformly bounded gives a local parabolic Lipschitz estimate
for its value. -/
lemma ParabolicSecondJet.value_unit_lipschitz_Ioc
    {t₀ T Bx Bt : ℝ} (hBx : 0 ≤ Bx) (hBt : 0 ≤ Bt)
    {u : ℝ × (Fin n → ℝ) → ℝ}
    (J : ParabolicSecondJet u (euclideanMildFiniteCylinderND n t₀ T))
    (hgrad : ParabolicBoundedWith Bx J.spaceDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    (htime : ParabolicBoundedWith Bt J.timeDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    ⦃p q : ℝ × (Fin n → ℝ)⦄
    (hp : p ∈ euclideanMildFiniteCylinderND n t₀ T)
    (hq : q ∈ euclideanMildFiniteCylinderND n t₀ T)
    (hpq : parabolicDistance p q ≤ 1) :
    ‖u p - u q‖ ≤ (Bx + Bt) * parabolicDistance p q := by
  have hpt : t₀ < p.1 ∧ p.1 ≤ T := mem_euclideanMildFiniteCylinderND.mp hp
  have hqt : t₀ < q.1 ∧ q.1 ≤ T := mem_euclideanMildFiniteCylinderND.mp hq
  have hspace : ‖u (p.1, p.2) - u (p.1, q.2)‖ ≤ Bx * ‖p.2 - q.2‖ := by
    apply convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun x : Fin n → ℝ ↦ u (p.1, x))
      (f' := fun x ↦ J.spaceDeriv (p.1, x))
    · intro x _
      have hz : (p.1, x) ∈ euclideanMildFiniteCylinderND n t₀ T :=
        mem_euclideanMildFiniteCylinderND.mpr hpt
      convert J.hasSpaceDeriv hz using 1
      ext y
      simp [spaceSliceDomain, euclideanMildFiniteCylinderND, hpt]
    · intro x _
      exact hgrad (mem_euclideanMildFiniteCylinderND.mpr hpt)
    · simp
    · simp
  have htime' : ‖u (p.1, q.2) - u (q.1, q.2)‖ ≤ Bt * ‖p.1 - q.1‖ := by
    apply (convex_Ioc t₀ T).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t : ℝ ↦ u (t, q.2))
      (f' := fun t ↦ J.timeDeriv (t, q.2))
    · intro t ht
      have hz : (t, q.2) ∈ euclideanMildFiniteCylinderND n t₀ T :=
        mem_euclideanMildFiniteCylinderND.mpr ht
      convert J.hasTimeDeriv hz using 1
      ext τ
      simp [timeSliceDomain, euclideanMildFiniteCylinderND]
    · intro t ht
      exact htime (mem_euclideanMildFiniteCylinderND.mpr ht)
    · exact hqt
    · exact hpt
  have hdspace : ‖p.2 - q.2‖ ≤ parabolicDistance p q := by
    simpa only [dist_eq_norm] using parabolicDistance.space_dist_le p q
  have hdtime : ‖p.1 - q.1‖ ≤ parabolicDistance p q := by
    rw [Real.norm_eq_abs]
    have hs := parabolicDistance.sqrt_time_le p q
    have hs0 := Real.sqrt_nonneg |p.1 - q.1|
    have hs1 : Real.sqrt |p.1 - q.1| ≤ 1 := hs.trans hpq
    calc
      |p.1 - q.1| = (Real.sqrt |p.1 - q.1|) ^ 2 := by
        rw [Real.sq_sqrt (abs_nonneg _)]
      _ ≤ Real.sqrt |p.1 - q.1| := by nlinarith
      _ ≤ parabolicDistance p q := hs
  calc
    ‖u p - u q‖ ≤
        ‖u (p.1, p.2) - u (p.1, q.2)‖ +
          ‖u (p.1, q.2) - u (q.1, q.2)‖ := by
      calc
        ‖u p - u q‖ = ‖(u p - u (p.1, q.2)) +
            (u (p.1, q.2) - u q)‖ := by congr 1 <;> ring
        _ ≤ _ := norm_add_le _ _
    _ ≤ Bx * ‖p.2 - q.2‖ + Bt * ‖p.1 - q.1‖ := add_le_add hspace htime'
    _ ≤ Bx * parabolicDistance p q + Bt * parabolicDistance p q :=
      add_le_add (mul_le_mul_of_nonneg_left hdspace hBx)
        (mul_le_mul_of_nonneg_left hdtime hBt)
    _ = (Bx + Bt) * parabolicDistance p q := by ring

/-- The preceding local estimate plus a value sup bound gives global
parabolic Holder control of the value field. -/
theorem ParabolicSecondJet.value_parabolicHolderWith_Ioc
    {t₀ T Bu Bx Bt r : ℝ} (hBu : 0 ≤ Bu) (hBx : 0 ≤ Bx) (hBt : 0 ≤ Bt)
    (hr0 : 0 < r) (hr1 : r ≤ 1)
    {u : ℝ × (Fin n → ℝ) → ℝ}
    (J : ParabolicSecondJet u (euclideanMildFiniteCylinderND n t₀ T))
    (hu : ParabolicBoundedWith Bu u (euclideanMildFiniteCylinderND n t₀ T))
    (hgrad : ParabolicBoundedWith Bx J.spaceDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    (htime : ParabolicBoundedWith Bt J.timeDeriv
      (euclideanMildFiniteCylinderND n t₀ T)) :
    ParabolicHolderWith (2 * Bu + (Bx + Bt)) r u
      (euclideanMildFiniteCylinderND n t₀ T) := by
  exact parabolicHolderWith_of_bounded_of_unit_lipschitz hBu
    (add_nonneg hBx hBt) hr0 hr1 hu
    (by
      intro p hp q hq hpq
      exact J.value_unit_lipschitz_Ioc hBx hBt hgrad htime hp hq hpq)

/-- Norm-ball form of the lower-order value interpolation estimate. -/
theorem ParabolicSecondJet.value_parabolicC0AlphaNormLe_Ioc
    {t₀ T Bu Bx Bt r : ℝ} (hBu : 0 ≤ Bu) (hBx : 0 ≤ Bx) (hBt : 0 ≤ Bt)
    (hr0 : 0 < r) (hr1 : r ≤ 1)
    {u : ℝ × (Fin n → ℝ) → ℝ}
    (J : ParabolicSecondJet u (euclideanMildFiniteCylinderND n t₀ T))
    (hu : ParabolicBoundedWith Bu u (euclideanMildFiniteCylinderND n t₀ T))
    (hgrad : ParabolicBoundedWith Bx J.spaceDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    (htime : ParabolicBoundedWith Bt J.timeDeriv
      (euclideanMildFiniteCylinderND n t₀ T)) :
    ParabolicC0AlphaNormLe (Bu + (2 * Bu + (Bx + Bt))) r u
      (euclideanMildFiniteCylinderND n t₀ T) := by
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith hBu (by linarith)
    ⟨hu, J.value_parabolicHolderWith_Ioc hBu hBx hBt hr0 hr1 hu hgrad htime⟩

/-- The exact integrable `t^{-1/2}` kernel estimate for one coordinate of
the Duhamel gradient. -/
lemma abs_heatDuhamelGradientCoordND_le
    {t₀ t C : ℝ} (hT : t₀ ≤ t) (hC : 0 ≤ C)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (hqb : ∀ s y, ‖q s y‖ ≤ C) (x : Fin n → ℝ) (k : Fin n) :
    |heatDuhamelGradientCoordND t₀ t q k x| ≤
      2 * C * Real.sqrt (t - t₀) / Real.sqrt π := by
  let G : ℝ → ℝ := fun s => ∫ y : Fin n → ℝ,
    (heatKernelND (t - s) (x - y) * (-(x - y) k / (2 * (t - s)))) * q s y
  let g : ℝ → ℝ := fun s =>
    (C / Real.sqrt π) * (t - s) ^ (-(1 / 2) : ℝ)
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Ioc t₀ t → ‖G s‖ ≤ g s := by
    have hset : {a : ℝ | ¬ a ≠ t} = {t} := by ext s; simp
    have htne : ∀ᵐ s : ℝ, s ≠ t := by
      rw [ae_iff, hset]
      exact measure_singleton t
    filter_upwards [htne] with s hs hmem
    have hst : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hmem.2 hs)
    rw [Real.norm_eq_abs]
    have hb := heatSemigroupND_coord_deriv_integral_bound hst x k
      (q s).continuous.aestronglyMeasurable (hqb s)
    refine hb.trans_eq ?_
    simp only [g]
    rw [Real.sqrt_mul Real.pi_pos.le, Real.rpow_neg hst.le, ← Real.sqrt_eq_rpow]
    field_simp
  have hgint : IntervalIntegrable g volume t₀ t := by
    have hbase : IntervalIntegrable
        (fun z : ℝ => z ^ (-(1 / 2) : ℝ)) volume 0 (t - t₀) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hcomp := hbase.comp_sub_left t
    have hw : IntervalIntegrable
        (fun s : ℝ => (t - s) ^ (-(1 / 2) : ℝ)) volume t₀ t := by
      simpa using hcomp.symm
    exact hw.const_mul _
  have hmain := intervalIntegral.norm_integral_le_of_norm_le hT hae hgint
  have hgval : (∫ s in t₀..t, g s) =
      2 * C * Real.sqrt (t - t₀) / Real.sqrt π := by
    simp only [g]
    rw [intervalIntegral.integral_const_mul, integral_rpow_neg_half_sub,
      ← Real.sqrt_eq_rpow]
    ring
  rw [Real.norm_eq_abs, hgval] at hmain
  simpa only [heatDuhamelGradientCoordND, G] using hmain

/-- Explicit finite-cylinder sup constant for the actual mild gradient. -/
def heatMildGradientSupConstantND
    (t₀ T C : ℝ) (D : EuclideanBoundedC2Data n) : ℝ :=
  (∑ k : Fin n, ‖D.first k‖) +
    ∑ _k : Fin n, 2 * C * Real.sqrt (T - t₀) / Real.sqrt π

lemma heatMildGradientSupConstantND_nonneg
    {t₀ T C : ℝ} (hT : t₀ ≤ T) (hC : 0 ≤ C)
    (D : EuclideanBoundedC2Data n) :
    0 ≤ heatMildGradientSupConstantND t₀ T C D := by
  unfold heatMildGradientSupConstantND
  apply add_nonneg
  · exact Finset.sum_nonneg fun k _ ↦ norm_nonneg _
  · exact Finset.sum_nonneg fun k _ ↦
      div_nonneg (mul_nonneg (mul_nonneg (by positivity) hC)
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- Uniform bound for the actual mild gradient on a finite positive-time
cylinder.  The homogeneous part preserves the bounded initial gradient, and
the Duhamel part costs the integrable square-root factor. -/
theorem parabolicBoundedWith_heatMildSpatialGradientCLM_Ioc
    {t₀ T r C H : ℝ} (hT : t₀ ≤ T) (hr0 : 0 < r) (hC : 0 ≤ C)
    (D : EuclideanBoundedC2Data n)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ParabolicBoundedWith (heatMildGradientSupConstantND t₀ T C D)
      (fun z ↦ heatMildSpatialGradientCLM t₀ z.1 D.value q z.2)
      (euclideanMildFiniteCylinderND n t₀ T) := by
  rintro ⟨t, x⟩ hz
  have ht : t₀ < t := (mem_euclideanMildFiniteCylinderND.mp hz).1
  have htT : t ≤ T := (mem_euclideanMildFiniteCylinderND.mp hz).2
  unfold heatMildSpatialGradientCLM heatSemigroupGradientCLM
    heatDuhamelGradientCLM
  refine (norm_add_le _ _).trans ?_
  refine add_le_add (norm_coordinateLinearFunctional_le _ |>.trans ?_)
    (norm_coordinateLinearFunctional_le _ |>.trans ?_)
  · apply Finset.sum_le_sum
    intro k _
    rw [D.heatSemigroupGradientCoordND_eq (sub_pos.mpr ht) k x]
    exact abs_heatSemigroupND_le (sub_pos.mpr ht) x
      (fun y ↦ (D.first k).norm_coe_le_norm y)
  · apply Finset.sum_le_sum
    intro k _
    refine (show |heatDuhamelGradientCoordND t₀ t q k x| ≤ _ from
      abs_heatDuhamelGradientCoordND_le ht.le hC hq hqb x k).trans ?_
    have hsqrt := Real.sqrt_le_sqrt (sub_le_sub_right htT t₀)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt (mul_nonneg (by positivity) hC))
      (Real.sqrt_nonneg π)

/-- Explicit finite-cylinder sup constant for the mild solution value. -/
def heatMildValueSupConstantND
    (t₀ T C : ℝ) (D : EuclideanBoundedC2Data n) : ℝ :=
  ‖D.value‖ + C * (T - t₀)

lemma heatMildValueSupConstantND_nonneg
    {t₀ T C : ℝ} (hT : t₀ ≤ T) (hC : 0 ≤ C)
    (D : EuclideanBoundedC2Data n) :
    0 ≤ heatMildValueSupConstantND t₀ T C D := by
  unfold heatMildValueSupConstantND
  exact add_nonneg (norm_nonneg _) (mul_nonneg hC (sub_nonneg.mpr hT))

/-- Uniform value bound for the actual mild solution on a finite cylinder. -/
theorem parabolicBoundedWith_heatMildSpaceTimeND_Ioc
    {t₀ T C : ℝ} (hT : t₀ ≤ T) (hC : 0 ≤ C)
    (D : EuclideanBoundedC2Data n)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (hqb : ∀ s y, ‖q s y‖ ≤ C) :
    ParabolicBoundedWith (heatMildValueSupConstantND t₀ T C D)
      (heatMildSpaceTimeND t₀ D.value q)
      (euclideanMildFiniteCylinderND n t₀ T) := by
  rintro ⟨t, x⟩ hz
  have ht : t₀ < t := (mem_euclideanMildFiniteCylinderND.mp hz).1
  have htT : t ≤ T := (mem_euclideanMildFiniteCylinderND.mp hz).2
  have hnorm := norm_heatMildValueNDbcf_le ht D.value hq hqb
  calc
    ‖heatMildSpaceTimeND t₀ D.value q (t, x)‖ =
        ‖heatMildValueNDbcf ht D.value hq hqb x‖ := by
      rw [heatMildValueNDbcf_apply]
      rfl
    _ ≤ ‖heatMildValueNDbcf ht D.value hq hqb‖ :=
      (heatMildValueNDbcf ht D.value hq hqb).norm_coe_le_norm x
    _ ≤ ‖D.value‖ + C * (t - t₀) := hnorm
    _ ≤ heatMildValueSupConstantND t₀ T C D := by
      unfold heatMildValueSupConstantND
      gcongr

/-- A bounded Hessian makes the spatial derivative Lipschitz on each full
Euclidean slice. -/
lemma ParabolicSecondJet.spaceDeriv_spatial_lipschitz_Ioc
    {t₀ T Bxx : ℝ} (hBxx : 0 ≤ Bxx)
    {u : ℝ × (Fin n → ℝ) → ℝ}
    (J : ParabolicSecondJet u (euclideanMildFiniteCylinderND n t₀ T))
    (hxx : ParabolicBoundedWith Bxx J.spaceSecondDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) (x y : Fin n → ℝ) :
    ‖J.spaceDeriv (t, x) - J.spaceDeriv (t, y)‖ ≤ Bxx * ‖x - y‖ := by
  have hmain : ‖J.spaceDeriv (t, x) - J.spaceDeriv (t, y)‖ ≤ Bxx * ‖x - y‖ := by
    apply convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun z : Fin n → ℝ ↦ J.spaceDeriv (t, z))
      (f' := fun z ↦ J.spaceSecondDeriv (t, z))
    · intro z _
      have hz : (t, z) ∈ euclideanMildFiniteCylinderND n t₀ T :=
        mem_euclideanMildFiniteCylinderND.mpr ht
      have h := J.hasSpaceSecondDeriv hz
      have hset : spaceSliceDomain (euclideanMildFiniteCylinderND n t₀ T) t =
          Set.univ := by
        ext w
        simp [spaceSliceDomain, euclideanMildFiniteCylinderND, ht]
      rw [hset] at h
      exact h
    · intro z _
      exact hxx (mem_euclideanMildFiniteCylinderND.mpr ht)
    · simp
    · simp
  simpa only [norm_sub_rev] using hmain

/-- Time Lipschitz estimate for the value along a fixed spatial point. -/
lemma ParabolicSecondJet.value_time_lipschitz_Ioc
    {t₀ T Bt : ℝ} (hBt : 0 ≤ Bt)
    {u : ℝ × (Fin n → ℝ) → ℝ}
    (J : ParabolicSecondJet u (euclideanMildFiniteCylinderND n t₀ T))
    (htime : ParabolicBoundedWith Bt J.timeDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    {t τ : ℝ} (ht : t ∈ Set.Ioc t₀ T) (hτ : τ ∈ Set.Ioc t₀ T)
    (x : Fin n → ℝ) :
    |u (t, x) - u (τ, x)| ≤ Bt * |t - τ| := by
  have hmain : ‖u (t, x) - u (τ, x)‖ ≤ Bt * ‖t - τ‖ := by
    apply (convex_Ioc t₀ T).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun a : ℝ ↦ u (a, x))
      (f' := fun a ↦ J.timeDeriv (a, x))
    · intro a ha
      have hz : (a, x) ∈ euclideanMildFiniteCylinderND n t₀ T :=
        mem_euclideanMildFiniteCylinderND.mpr ha
      convert J.hasTimeDeriv hz using 1
      ext b
      simp [timeSliceDomain, euclideanMildFiniteCylinderND]
    · intro a ha
      exact htime (mem_euclideanMildFiniteCylinderND.mpr ha)
    · exact hτ
    · exact ht
  simpa only [Real.norm_eq_abs] using hmain
/-- Quantitative first-order Taylor remainder obtained only from the genuine
second-jet witnesses and the Hessian sup bound. -/
lemma ParabolicSecondJet.value_linearization_error_le_Ioc
    {t₀ T Bxx : ℝ} (hBxx : 0 ≤ Bxx)
    {u : ℝ × (Fin n → ℝ) → ℝ}
    (J : ParabolicSecondJet u (euclideanMildFiniteCylinderND n t₀ T))
    (hxx : ParabolicBoundedWith Bxx J.spaceSecondDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) (x v : Fin n → ℝ)
    (hv : ‖v‖ ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    |u (t, x + a • v) - u (t, x) - a * J.spaceDeriv (t, x) v| ≤
      Bxx * a ^ 2 := by
  let F : ℝ → ℝ :=
    (fun b ↦ u (t, x + b • v)) - (fun _ ↦ u (t, x)) -
      (fun b ↦ b * J.spaceDeriv (t, x) v)
  let F' : ℝ → ℝ := fun b ↦
    J.spaceDeriv (t, x + b • v) v - J.spaceDeriv (t, x) v
  have hderiv : ∀ b ∈ Set.Icc (0 : ℝ) a,
      @HasDerivWithinAt ℝ _ ℝ NormedAddCommGroup.toAddCommGroup
        RCLike.toInnerProductSpaceReal.toModule _ _
        F (F' b) (Set.Icc 0 a) b := by
    intro b hb
    have hz : (t, x + b • v) ∈ euclideanMildFiniteCylinderND n t₀ T :=
      mem_euclideanMildFiniteCylinderND.mpr ht
    have hspace : HasFDerivAt (fun y : Fin n → ℝ ↦ u (t, y))
        (J.spaceDeriv (t, x + b • v)) (x + b • v) := by
      have h := J.hasSpaceDeriv hz
      have hset : spaceSliceDomain (euclideanMildFiniteCylinderND n t₀ T) t =
          Set.univ := by
        ext y
        simp [spaceSliceDomain, euclideanMildFiniteCylinderND, ht]
      rw [hset] at h
      exact hasFDerivWithinAt_univ.mp (by simpa using h)
    have hline : HasDerivAt (fun c : ℝ ↦ u (t, x + c • v))
        (J.spaceDeriv (t, x + b • v) v) b := by
      have hi : HasDerivAt (fun c : ℝ ↦ x + c • v) v b :=
        by simpa using ((hasDerivAt_id b).smul_const v).const_add x
      simpa [Function.comp_def] using hspace.comp_hasDerivAt b hi
    have hlin : @HasDerivAt ℝ _ ℝ NormedAddCommGroup.toAddCommGroup
        RCLike.toInnerProductSpaceReal.toModule _ _
        (fun c : ℝ ↦ c * J.spaceDeriv (t, x) v)
        (J.spaceDeriv (t, x) v) b := by
      simpa using (hasDerivAt_id b).mul_const (J.spaceDeriv (t, x) v)
    have hout := (hline.sub_const (u (t, x))).sub hlin
    refine hout.hasDerivWithinAt.congr ?_ ?_
    · intro c hc
      simp [F]
    · simp [F]
  have hbound : ∀ b ∈ Set.Ico (0 : ℝ) a, ‖F' b‖ ≤ Bxx * a := by
    intro b hb
    have hgrad := J.spaceDeriv_spatial_lipschitz_Ioc hBxx hxx ht
      (x + b • v) x
    have happly : |J.spaceDeriv (t, x + b • v) v -
        J.spaceDeriv (t, x) v| ≤
        ‖J.spaceDeriv (t, x + b • v) - J.spaceDeriv (t, x)‖ * ‖v‖ := by
      simpa only [ContinuousLinearMap.sub_apply, Real.norm_eq_abs] using
        ContinuousLinearMap.le_opNorm
          (J.spaceDeriv (t, x + b • v) - J.spaceDeriv (t, x)) v
    calc
      ‖F' b‖ ≤ ‖J.spaceDeriv (t, x + b • v) - J.spaceDeriv (t, x)‖ * ‖v‖ := by
        simpa only [F', Real.norm_eq_abs] using happly
      _ ≤ (Bxx * ‖(x + b • v) - x‖) * ‖v‖ := by
        gcongr
      _ ≤ Bxx * a := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hb.1]
        have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
        have hv2 : ‖v‖ * ‖v‖ ≤ 1 := by nlinarith
        calc
          Bxx * (b * ‖v‖) * ‖v‖ = (Bxx * b) * (‖v‖ * ‖v‖) := by ring
          _ ≤ (Bxx * b) * 1 :=
            mul_le_mul_of_nonneg_left hv2 (mul_nonneg hBxx hb.1)
          _ ≤ Bxx * a := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.2.le hBxx
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    hderiv hbound a (right_mem_Icc.mpr ha)
  have hF0 : F 0 = 0 := by simp [F]
  rw [hF0, sub_zero, Real.norm_eq_abs] at hmvt
  simpa [F, pow_two, mul_assoc] using hmvt

/-- Applying the spatial derivative in a vector of norm at most one, its
variation between two times is controlled by the square root of the time
separation.  This is the finite-difference interpolation step behind the
parabolic regularity of the gradient. -/
lemma ParabolicSecondJet.spaceDeriv_time_sqrt_apply_le_Ioc
    {t₀ T Bxx Bt : ℝ} (hBxx : 0 ≤ Bxx) (hBt : 0 ≤ Bt)
    {u : ℝ × (Fin n → ℝ) → ℝ}
    (J : ParabolicSecondJet u (euclideanMildFiniteCylinderND n t₀ T))
    (hxx : ParabolicBoundedWith Bxx J.spaceSecondDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    (htime : ParabolicBoundedWith Bt J.timeDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    {t τ : ℝ} (ht : t ∈ Set.Ioc t₀ T) (hτ : τ ∈ Set.Ioc t₀ T)
    (x v : Fin n → ℝ) (hv : ‖v‖ ≤ 1) :
    |(J.spaceDeriv (t, x) - J.spaceDeriv (τ, x)) v| ≤
      (2 * Bt + 2 * Bxx) * Real.sqrt |t - τ| := by
  let δ := Real.sqrt |t - τ|
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  by_cases hδ : δ = 0
  · have htimeeq : t = τ := by
      have habsle : |t - τ| ≤ 0 := Real.sqrt_eq_zero'.mp hδ
      have habs : |t - τ| = 0 := le_antisymm habsle (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp habs)
    subst τ
    simp
  have hδpos : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδ)
  have hδsq : δ ^ 2 = |t - τ| := by
    exact Real.sq_sqrt (abs_nonneg _)
  let A : ℝ := u (t, x + δ • v) - u (t, x)
  let B : ℝ := u (τ, x + δ • v) - u (τ, x)
  have hAt : |A - δ * J.spaceDeriv (t, x) v| ≤ Bxx * δ ^ 2 := by
    simpa only [A] using
      J.value_linearization_error_le_Ioc hBxx hxx ht x v hv hδ0
  have hAτ : |B - δ * J.spaceDeriv (τ, x) v| ≤ Bxx * δ ^ 2 := by
    simpa only [B] using
      J.value_linearization_error_le_Ioc hBxx hxx hτ x v hv hδ0
  have hshift := J.value_time_lipschitz_Ioc hBt htime ht hτ (x + δ • v)
  have hbase := J.value_time_lipschitz_Ioc hBt htime ht hτ x
  have hAB : |A - B| ≤ 2 * Bt * |t - τ| := by
    have hid : A - B =
        (u (t, x + δ • v) - u (τ, x + δ • v)) -
          (u (t, x) - u (τ, x)) := by
      simp only [A, B]
      ring
    rw [hid]
    refine (abs_sub _ _).trans ?_
    calc
      |u (t, x + δ • v) - u (τ, x + δ • v)| +
          |u (t, x) - u (τ, x)| ≤
        Bt * |t - τ| + Bt * |t - τ| := add_le_add hshift hbase
      _ = 2 * Bt * |t - τ| := by ring
  have hidentity : δ *
      ((J.spaceDeriv (t, x) - J.spaceDeriv (τ, x)) v) =
      -(A - δ * J.spaceDeriv (t, x) v) + (A - B) +
        (B - δ * J.spaceDeriv (τ, x) v) := by
    simp only [ContinuousLinearMap.sub_apply]
    ring
  have hmul : δ * |(J.spaceDeriv (t, x) - J.spaceDeriv (τ, x)) v| ≤
      δ * ((2 * Bt + 2 * Bxx) * δ) := by
    calc
      δ * |(J.spaceDeriv (t, x) - J.spaceDeriv (τ, x)) v| =
          |δ * ((J.spaceDeriv (t, x) - J.spaceDeriv (τ, x)) v)| := by
            rw [abs_mul, abs_of_nonneg hδ0]
      _ = |-(A - δ * J.spaceDeriv (t, x) v) + (A - B) +
          (B - δ * J.spaceDeriv (τ, x) v)| := congrArg abs hidentity
      _ ≤ |-(A - δ * J.spaceDeriv (t, x) v)| + |A - B| +
          |B - δ * J.spaceDeriv (τ, x) v| := by
            exact (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) le_rfl)
      _ = |A - δ * J.spaceDeriv (t, x) v| + |A - B| +
          |B - δ * J.spaceDeriv (τ, x) v| := by rw [abs_neg]
      _ ≤ Bxx * δ ^ 2 + 2 * Bt * |t - τ| + Bxx * δ ^ 2 := by
          exact add_le_add (add_le_add hAt hAB) hAτ
      _ = δ * ((2 * Bt + 2 * Bxx) * δ) := by
        rw [← hδsq]
        ring
  nlinarith

/-- Operator-norm form of the square-root temporal modulus for the spatial
derivative. -/
theorem ParabolicSecondJet.spaceDeriv_time_sqrt_le_Ioc
    {t₀ T Bxx Bt : ℝ} (hBxx : 0 ≤ Bxx) (hBt : 0 ≤ Bt)
    {u : ℝ × (Fin n → ℝ) → ℝ}
    (J : ParabolicSecondJet u (euclideanMildFiniteCylinderND n t₀ T))
    (hxx : ParabolicBoundedWith Bxx J.spaceSecondDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    (htime : ParabolicBoundedWith Bt J.timeDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    {t τ : ℝ} (ht : t ∈ Set.Ioc t₀ T) (hτ : τ ∈ Set.Ioc t₀ T)
    (x : Fin n → ℝ) :
    ‖J.spaceDeriv (t, x) - J.spaceDeriv (τ, x)‖ ≤
      (2 * Bt + 2 * Bxx) * Real.sqrt |t - τ| := by
  let K : ℝ := (2 * Bt + 2 * Bxx) * Real.sqrt |t - τ|
  have hK : 0 ≤ K := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro v
  by_cases hv0 : v = 0
  · subst v
    simp [K]
  let w : Fin n → ℝ := ‖v‖⁻¹ • v
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hw : ‖w‖ = 1 := by
    simp only [w, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hvnorm, inv_mul_cancel₀ hvnorm.ne']
  have happly := J.spaceDeriv_time_sqrt_apply_le_Ioc hBxx hBt hxx htime
    ht hτ x w (by rw [hw])
  have hvrep : ‖v‖ • w = v := by
    simp only [w, smul_smul]
    rw [mul_inv_cancel₀ hvnorm.ne', one_smul]
  calc
    ‖(J.spaceDeriv (t, x) - J.spaceDeriv (τ, x)) v‖ =
        ‖(J.spaceDeriv (t, x) - J.spaceDeriv (τ, x)) (‖v‖ • w)‖ := by rw [hvrep]
    _ = ‖v‖ * ‖(J.spaceDeriv (t, x) - J.spaceDeriv (τ, x)) w‖ := by
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)]
    _ ≤
        ‖v‖ * K := by
      gcongr
      simpa only [K, Real.norm_eq_abs] using happly
    _ = K * ‖v‖ := by ring

/-- A bounded Hessian and bounded time derivative give a local parabolic
Lipschitz estimate for the spatial derivative.  The temporal part uses the
square-root interpolation estimate, exactly matching parabolic distance. -/
lemma ParabolicSecondJet.spaceDeriv_unit_lipschitz_Ioc
    {t₀ T Bxx Bt : ℝ} (hBxx : 0 ≤ Bxx) (hBt : 0 ≤ Bt)
    {u : ℝ × (Fin n → ℝ) → ℝ}
    (J : ParabolicSecondJet u (euclideanMildFiniteCylinderND n t₀ T))
    (hxx : ParabolicBoundedWith Bxx J.spaceSecondDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    (htime : ParabolicBoundedWith Bt J.timeDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    ⦃p q : ℝ × (Fin n → ℝ)⦄
    (hp : p ∈ euclideanMildFiniteCylinderND n t₀ T)
    (hq : q ∈ euclideanMildFiniteCylinderND n t₀ T)
    (_hpq : parabolicDistance p q ≤ 1) :
    ‖J.spaceDeriv p - J.spaceDeriv q‖ ≤
      (2 * Bt + 3 * Bxx) * parabolicDistance p q := by
  have hpt : p.1 ∈ Set.Ioc t₀ T := mem_euclideanMildFiniteCylinderND.mp hp
  have hqt : q.1 ∈ Set.Ioc t₀ T := mem_euclideanMildFiniteCylinderND.mp hq
  have hspace := J.spaceDeriv_spatial_lipschitz_Ioc hBxx hxx hpt p.2 q.2
  have htime' := J.spaceDeriv_time_sqrt_le_Ioc hBxx hBt hxx htime
    hpt hqt q.2
  have hdspace : ‖p.2 - q.2‖ ≤ parabolicDistance p q := by
    simpa only [dist_eq_norm] using parabolicDistance.space_dist_le p q
  have hdtime : Real.sqrt |p.1 - q.1| ≤ parabolicDistance p q :=
    parabolicDistance.sqrt_time_le p q
  calc
    ‖J.spaceDeriv p - J.spaceDeriv q‖ ≤
        ‖J.spaceDeriv (p.1, p.2) - J.spaceDeriv (p.1, q.2)‖ +
          ‖J.spaceDeriv (p.1, q.2) - J.spaceDeriv (q.1, q.2)‖ := by
      calc
        ‖J.spaceDeriv p - J.spaceDeriv q‖ =
            ‖(J.spaceDeriv p - J.spaceDeriv (p.1, q.2)) +
              (J.spaceDeriv (p.1, q.2) - J.spaceDeriv q)‖ := by
                congr 1
                abel
        _ ≤ _ := norm_add_le _ _
    _ ≤ Bxx * ‖p.2 - q.2‖ +
        (2 * Bt + 2 * Bxx) * Real.sqrt |p.1 - q.1| :=
      add_le_add hspace htime'
    _ ≤ Bxx * parabolicDistance p q +
        (2 * Bt + 2 * Bxx) * parabolicDistance p q := by
      exact add_le_add (mul_le_mul_of_nonneg_left hdspace hBxx)
        (mul_le_mul_of_nonneg_left hdtime (by linarith))
    _ = (2 * Bt + 3 * Bxx) * parabolicDistance p q := by ring

/-- Global parabolic Holder control of the spatial derivative on a finite
cylinder, obtained from its sup bound and the interpolated local estimate. -/
theorem ParabolicSecondJet.spaceDeriv_parabolicHolderWith_Ioc
    {t₀ T Bx Bxx Bt r : ℝ} (hBx : 0 ≤ Bx) (hBxx : 0 ≤ Bxx)
    (hBt : 0 ≤ Bt) (hr0 : 0 < r) (hr1 : r ≤ 1)
    {u : ℝ × (Fin n → ℝ) → ℝ}
    (J : ParabolicSecondJet u (euclideanMildFiniteCylinderND n t₀ T))
    (hgrad : ParabolicBoundedWith Bx J.spaceDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    (hxx : ParabolicBoundedWith Bxx J.spaceSecondDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    (htime : ParabolicBoundedWith Bt J.timeDeriv
      (euclideanMildFiniteCylinderND n t₀ T)) :
    ParabolicHolderWith (2 * Bx + (2 * Bt + 3 * Bxx)) r J.spaceDeriv
      (euclideanMildFiniteCylinderND n t₀ T) := by
  exact parabolicHolderWith_of_bounded_of_unit_lipschitz hBx
    (by linarith) hr0 hr1 hgrad
    (by
      intro p hp q hq hpq
      exact J.spaceDeriv_unit_lipschitz_Ioc hBxx hBt hxx htime hp hq hpq)

/-- Norm-ball form of the interpolated spatial-gradient estimate. -/
theorem ParabolicSecondJet.spaceDeriv_parabolicC0AlphaNormLe_Ioc
    {t₀ T Bx Bxx Bt r : ℝ} (hBx : 0 ≤ Bx) (hBxx : 0 ≤ Bxx)
    (hBt : 0 ≤ Bt) (hr0 : 0 < r) (hr1 : r ≤ 1)
    {u : ℝ × (Fin n → ℝ) → ℝ}
    (J : ParabolicSecondJet u (euclideanMildFiniteCylinderND n t₀ T))
    (hgrad : ParabolicBoundedWith Bx J.spaceDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    (hxx : ParabolicBoundedWith Bxx J.spaceSecondDeriv
      (euclideanMildFiniteCylinderND n t₀ T))
    (htime : ParabolicBoundedWith Bt J.timeDeriv
      (euclideanMildFiniteCylinderND n t₀ T)) :
    ParabolicC0AlphaNormLe (Bx + (2 * Bx + (2 * Bt + 3 * Bxx))) r
      J.spaceDeriv (euclideanMildFiniteCylinderND n t₀ T) := by
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith hBx (by linarith)
    ⟨hgrad,
      J.spaceDeriv_parabolicHolderWith_Ioc hBx hBxx hBt hr0 hr1
        hgrad hxx htime⟩

section FiniteCylinderC2Alpha

/-- Zeroth-order `C^{0,r}` radius used in the full finite-cylinder estimate. -/
def heatMildValueC0AlphaNormConstantND
    (t₀ T r H C : ℝ) (D : EuclideanBoundedC2Data n) : ℝ :=
  let Bu := heatMildValueSupConstantND t₀ T C D
  let Bx := heatMildGradientSupConstantND t₀ T C D
  let Bt := heatMildTimeDerivSupConstantND t₀ T r H C D
  Bu + (2 * Bu + (Bx + Bt))

/-- Spatial-gradient `C^{0,r}` radius used in the full estimate. -/
def heatMildGradientC0AlphaNormConstantND
    (t₀ T r H C : ℝ) (D : EuclideanBoundedC2Data n) : ℝ :=
  let Bx := heatMildGradientSupConstantND t₀ T C D
  let Bxx := heatMildHessianSupConstantND t₀ T r H D
  let Bt := heatMildTimeDerivSupConstantND t₀ T r H C D
  Bx + (2 * Bx + (2 * Bt + 3 * Bxx))

/-- Explicit scalar `C^{2+r,1+r/2}` radius on `(t₀,T] × ℝⁿ`. -/
def heatMildC2AlphaNormConstantND
    (n : ℕ) (t₀ T r H₀ H C Hq : ℝ)
    (D : EuclideanBoundedC2Data n) : ℝ :=
  heatMildValueC0AlphaNormConstantND t₀ T r H C D +
    heatMildGradientC0AlphaNormConstantND t₀ T r H C D +
    (heatMildHessianSupConstantND t₀ T r H D +
      heatMildHessianParabolicHolderConstant n r H₀ H) +
    (heatMildTimeDerivSupConstantND t₀ T r H C D +
      heatMildTimeDerivParabolicHolderConstantND n r H₀ H Hq)

/-- **Full scalar finite-cylinder Schauder estimate.**  The explicit
heat-kernel mild solution carries one genuine second jet, and its value,
gradient, Hessian, and time derivative all lie in the asserted parabolic
`C^{0,r}` balls.  Thus it belongs to `C^{2+r,1+r/2}` with a completely
explicit radius. -/
theorem parabolicC2AlphaNormLe_heatMildSpaceTimeND_Ioc
    {t₀ T r : ℝ} (hT : t₀ ≤ T) (hr0 : 0 < r) (hr1 : r < 1)
    (D : EuclideanBoundedC2Data n) {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H Hq : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hHq : 0 ≤ Hq) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (hqParabolic : ParabolicHolderWith Hq r
      (fun z : ℝ × (Fin n → ℝ) ↦ q z.1 z.2)
      (euclideanMildFiniteCylinderND n t₀ T)) :
    ParabolicC2AlphaNormLe
      (heatMildC2AlphaNormConstantND n t₀ T r H₀ H C Hq D) r
      (heatMildSpaceTimeND t₀ D.value q)
      (euclideanMildFiniteCylinderND n t₀ T) := by
  let J := heatMildFiniteParabolicSecondJetND (t₀ := t₀) (T := T)
    hr0 D.value hq hH hqb hqholder
  let Bu := heatMildValueSupConstantND t₀ T C D
  let Bx := heatMildGradientSupConstantND t₀ T C D
  let Bxx := heatMildHessianSupConstantND t₀ T r H D
  let Bt := heatMildTimeDerivSupConstantND t₀ T r H C D
  have hBu : 0 ≤ Bu := heatMildValueSupConstantND_nonneg hT hC D
  have hBx : 0 ≤ Bx := heatMildGradientSupConstantND_nonneg hT hC D
  have hBxx : 0 ≤ Bxx := heatMildHessianSupConstantND_nonneg hT hr0 hH D
  have hBt : 0 ≤ Bt := heatMildTimeDerivSupConstantND_nonneg hT hr0 hH hC D
  have huB : ParabolicBoundedWith Bu (heatMildSpaceTimeND t₀ D.value q)
      (euclideanMildFiniteCylinderND n t₀ T) :=
    parabolicBoundedWith_heatMildSpaceTimeND_Ioc hT hC D hq hqb
  have hxB : ParabolicBoundedWith Bx J.spaceDeriv
      (euclideanMildFiniteCylinderND n t₀ T) := by
    simpa only [J, heatMildFiniteParabolicSecondJetND_spaceDeriv] using
      (parabolicBoundedWith_heatMildSpatialGradientCLM_Ioc
        hT hr0 hC D hq hH hqb hqholder)
  have hxxB : ParabolicBoundedWith Bxx J.spaceSecondDeriv
      (euclideanMildFiniteCylinderND n t₀ T) := by
    simpa only [J, heatMildFiniteParabolicSecondJetND_spaceSecondDeriv] using
      (parabolicBoundedWith_heatMildHessianFieldND_Ioc
        hT hr0 D hq hH hqb hqholder)
  have htB : ParabolicBoundedWith Bt J.timeDeriv
      (euclideanMildFiniteCylinderND n t₀ T) := by
    simpa only [J, heatMildFiniteParabolicSecondJetND_timeDeriv] using
      (parabolicBoundedWith_heatMildTimeDerivND_Ioc
        hT hr0 D hq hH hqb hqholder)
  have huC : ParabolicC0AlphaNormLe (Bu + (2 * Bu + (Bx + Bt))) r
      (heatMildSpaceTimeND t₀ D.value q)
      (euclideanMildFiniteCylinderND n t₀ T) :=
    J.value_parabolicC0AlphaNormLe_Ioc hBu hBx hBt hr0 hr1.le huB hxB htB
  have hxC : ParabolicC0AlphaNormLe
      (Bx + (2 * Bx + (2 * Bt + 3 * Bxx))) r J.spaceDeriv
      (euclideanMildFiniteCylinderND n t₀ T) :=
    J.spaceDeriv_parabolicC0AlphaNormLe_Ioc
      hBx hBxx hBt hr0 hr1.le hxB hxxB htB
  have hxxC : ParabolicC0AlphaNormLe
      (heatMildHessianSupConstantND t₀ T r H D +
        heatMildHessianParabolicHolderConstant n r H₀ H) r
      J.spaceSecondDeriv (euclideanMildFiniteCylinderND n t₀ T) := by
    simpa only [J, heatMildFiniteParabolicSecondJetND_spaceSecondDeriv] using
      (parabolicC0AlphaNormLe_heatMildHessianFieldND_Ioc
        hT hr0 hr1 D hH₀ hsecondHolder hq hH hqb hqholder)
  have htC : ParabolicC0AlphaNormLe
      (heatMildTimeDerivSupConstantND t₀ T r H C D +
        heatMildTimeDerivParabolicHolderConstantND n r H₀ H Hq) r
      J.timeDeriv (euclideanMildFiniteCylinderND n t₀ T) := by
    simpa only [J, heatMildFiniteParabolicSecondJetND_timeDeriv] using
      (parabolicC0AlphaNormLe_heatMildTimeDerivND_Ioc
        hT hr0 hr1 D hH₀ hsecondHolder hq hC hH hHq hqb hqholder hqParabolic)
  simpa only [heatMildC2AlphaNormConstantND,
    heatMildValueC0AlphaNormConstantND,
    heatMildGradientC0AlphaNormConstantND, Bu, Bx, Bxx, Bt] using
    (ParabolicC2AlphaNormLe.of_secondJet
      (N := 0) (J := J) (by linarith : 0 ≤ Bu + (2 * Bu + (Bx + Bt)))
      (by linarith : 0 ≤ Bx + (2 * Bx + (2 * Bt + 3 * Bxx)))
      (add_nonneg hBxx
        (heatMildHessianParabolicHolderConstant_nonneg
          n hr0 hr1 hH₀ hH))
      (add_nonneg hBt
        (heatMildTimeDerivParabolicHolderConstantND_nonneg
          n hr0 hr1 hH₀ hH hHq))
      huC hxC hxxC htC)

end FiniteCylinderC2Alpha

end EuclideanJet
end LowerOrderInterpolation

end AnalyticPDE
end RicciFlow
