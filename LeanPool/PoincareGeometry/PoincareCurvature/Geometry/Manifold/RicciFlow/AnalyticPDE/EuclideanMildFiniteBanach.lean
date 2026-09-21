/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanMildC2Alpha
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteCylinderBanach
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherFunctionSpace

/-!
# The Euclidean mild solution in the finite-cylinder Banach space

This file turns the explicit scalar heat-kernel solution into an inhabitant of
the complete `C^{2+α,1+α/2}` space on `(t₀,T] × ℝⁿ`.  The construction uses
the genuine second jet already proved for the mild formula; the four component
Hölder bounds are transported to that particular jet using uniqueness of
derivatives on the interval and Euclidean spatial slices.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric Filter
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

section ScalarFiniteBanach

variable {n : ℕ}

/-- The explicit scalar heat-kernel solution, as an element of the complete
finite-cylinder parabolic Banach space. -/
def heatMildFiniteBanachND
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
    FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T r := by
  let u := heatMildSpaceTimeND t₀ D.value q
  let J : ParabolicSecondJet u
      (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) := by
    simpa only [u, parabolicFiniteCylinder, euclideanMildFiniteCylinderND] using
      (heatMildFiniteParabolicSecondJetND (t₀ := t₀) (T := T)
        hr0 D.value hq hH hqb hqholder)
  have hbound : ParabolicC2AlphaNormLe
      (heatMildC2AlphaNormConstantND n t₀ T r H₀ H C Hq D) r u
      (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) := by
    simpa only [u, parabolicFiniteCylinder, euclideanMildFiniteCylinderND] using
      (parabolicC2AlphaNormLe_heatMildSpaceTimeND_Ioc
        hT hr0 hr1 D hH₀ hsecondHolder hq hC hH hHq hqb hqholder hqParabolic)
  have hparts := hbound.secondJet_c0AlphaNormLe_self_of_unique J
    (fun {_z} hz ↦ uniqueDiffWithinAt_timeSlice_parabolicFiniteCylinder hz)
    (fun {_z} hz ↦ uniqueDiffWithinAt_spaceSlice_parabolicFiniteCylinder hz)
  exact FiniteParabolicC2AlphaBanach.ofSecondJet u J
    hparts.1.c0AlphaOn hparts.2.1.c0AlphaOn hparts.2.2.1.c0AlphaOn
      hparts.2.2.2.c0AlphaOn

variable {t₀ T r : ℝ} (hT : t₀ ≤ T) (hr0 : 0 < r) (hr1 : r < 1)
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
    (euclideanMildFiniteCylinderND n t₀ T))

/-- Value readout of the Banach-space mild solution. -/
@[simp] theorem heatMildFiniteBanachND_value
    {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :
    FiniteParabolicC2AlphaBanach.value
        (heatMildFiniteBanachND hT hr0 hr1 D hH₀ hsecondHolder hq
          hC hH hHq hqb hqholder hqParabolic) z =
      heatMildSpaceTimeND t₀ D.value q z := by
  simp [heatMildFiniteBanachND, hz]

/-- Time-derivative readout of the Banach-space mild solution. -/
@[simp] theorem heatMildFiniteBanachND_timeDeriv
    {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :
    FiniteParabolicC2AlphaBanach.timeDeriv
        (heatMildFiniteBanachND hT hr0 hr1 D hH₀ hsecondHolder hq
          hC hH hHq hqb hqholder hqParabolic) z =
      heatMildTimeDerivND t₀ D.value q z := by
  simp only [heatMildFiniteBanachND,
    FiniteParabolicC2AlphaBanach.timeDeriv_ofSecondJet _ _ _ _ _ _ hz]
  change (heatMildFiniteParabolicSecondJetND (t₀ := t₀) (T := T)
    hr0 D.value hq hH hqb hqholder).timeDeriv z = _
  exact congrFun (heatMildFiniteParabolicSecondJetND_timeDeriv
    (T := T) hr0 D.value hq hH hqb hqholder) z

/-- Spatial Hessian readout of the Banach-space mild solution. -/
@[simp] theorem heatMildFiniteBanachND_spaceSecondDeriv
    {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :
    FiniteParabolicC2AlphaBanach.spaceSecondDeriv
        (heatMildFiniteBanachND hT hr0 hr1 D hH₀ hsecondHolder hq
          hC hH hHq hqb hqholder hqParabolic) z =
      heatMildHessianFieldND t₀ hr0 D hq hH hqb hqholder z := by
  simp only [heatMildFiniteBanachND,
    FiniteParabolicC2AlphaBanach.spaceSecondDeriv_ofSecondJet _ _ _ _ _ _ hz]
  change (heatMildFiniteParabolicSecondJetND (t₀ := t₀) (T := T)
    hr0 D.value hq hH hqb hqholder).spaceSecondDeriv z = _
  exact congrFun (heatMildFiniteParabolicSecondJetND_spaceSecondDeriv
    (T := T) hr0 D hq hH hqb hqholder) z

/-- The Banach-space inhabitant satisfies the inhomogeneous scalar heat
equation pointwise at every positive time in the finite cylinder. -/
theorem heatMildFiniteBanachND_heatEquation
    {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) (x : Fin n → ℝ) :
    FiniteParabolicC2AlphaBanach.timeDeriv
        (heatMildFiniteBanachND hT hr0 hr1 D hH₀ hsecondHolder hq
          hC hH hHq hqb hqholder hqParabolic) (t, x) =
      (∑ k : Fin n,
        FiniteParabolicC2AlphaBanach.spaceSecondDeriv
            (heatMildFiniteBanachND hT hr0 hr1 D hH₀ hsecondHolder hq
              hC hH hHq hqb hqholder hqParabolic) (t, x)
          (Pi.single k 1) (Pi.single k 1)) + q t x := by
  have hz : (t, x) ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T := by
    simpa [parabolicFiniteCylinder] using ht
  rw [heatMildFiniteBanachND_timeDeriv hT hr0 hr1 D hH₀ hsecondHolder hq
    hC hH hHq hqb hqholder hqParabolic hz]
  rw [heatMildFiniteBanachND_spaceSecondDeriv hT hr0 hr1 D hH₀
    hsecondHolder hq hC hH hHq hqb hqholder hqParabolic hz]
  simp only [heatMildTimeDerivND, if_pos ht.1,
    heatMildHessianFieldND, dif_pos ht.1]
  rw [sum_heatMildSpatialHessianCLM_diag_eq_laplacian
    ht.1 hr0 D.value hq hH hqb hqholder x]

/-- Quantitative finite-cylinder Schauder bound for the packaged mild
solution. -/
theorem norm_heatMildFiniteBanachND_le :
    ‖heatMildFiniteBanachND hT hr0 hr1 D hH₀ hsecondHolder hq
        hC hH hHq hqb hqholder hqParabolic‖ ≤
      heatMildC2AlphaNormConstantND n t₀ T r H₀ H C Hq D := by
  let u := heatMildSpaceTimeND t₀ D.value q
  let J : ParabolicSecondJet u
      (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) := by
    simpa only [u, parabolicFiniteCylinder, euclideanMildFiniteCylinderND] using
      (heatMildFiniteParabolicSecondJetND (t₀ := t₀) (T := T)
        hr0 D.value hq hH hqb hqholder)
  have hbound : ParabolicC2AlphaNormLe
      (heatMildC2AlphaNormConstantND n t₀ T r H₀ H C Hq D) r u
      (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) := by
    simpa only [u, parabolicFiniteCylinder, euclideanMildFiniteCylinderND] using
      (parabolicC2AlphaNormLe_heatMildSpaceTimeND_Ioc
        hT hr0 hr1 D hH₀ hsecondHolder hq hC hH hHq hqb hqholder hqParabolic)
  have hparts := hbound.secondJet_c0AlphaNormLe_self_of_unique J
    (fun {_z} hz ↦ uniqueDiffWithinAt_timeSlice_parabolicFiniteCylinder hz)
    (fun {_z} hz ↦ uniqueDiffWithinAt_spaceSlice_parabolicFiniteCylinder hz)
  change ‖FiniteParabolicC2AlphaBanach.ofSecondJet u J _ _ _ _‖ ≤ _
  exact FiniteParabolicC2AlphaBanach.norm_ofSecondJet_le u J
    hparts.1 hparts.2.1 hparts.2.2.1 hparts.2.2.2

end ScalarFiniteBanach

end AnalyticPDE
end RicciFlow
