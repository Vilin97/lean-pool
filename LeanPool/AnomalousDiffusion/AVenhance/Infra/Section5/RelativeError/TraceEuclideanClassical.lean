/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceAveraging
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportTraceGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportPairingIntegral
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportTestSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ClassicalEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceEuclideanTransport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing

/-! # RelativeError: the classical low-mode trace bridge

This module connects the transported-test estimate to a classical solution.
The Fourier projection supplies the three explicit spectral facts in the
theorem: its initial pairing, gradient energy, and differentiated Laplacian
bound. -/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral
open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Classical
open AVenhance.Infra.Torus

private theorem low_mode_transport_pairing_bound :
  ∀ {b : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} {κ K B G : ℝ} {g f : Vec (2 : ℕ) → ℝ} {u : ℝ → Vec (2 :
    ℕ) → ℝ} {X : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ)}, Flow.SmoothPeriodicField b → (∀ (t : ℝ) (x
    : Vec (2 : ℕ)), vecDiv (b t) x = (0 : ℝ)) → IsFlow b X → (∀ (r : ℝ) (y : Vec (2 : ℕ)),
    ‖Flow.jointSpatialFDeriv b r y‖ ≤ B) → (0 : ℝ) ≤ B → (0 : ℝ) < K → (0 : ℝ) ≤ G →
    IsClassicalSol b κ (fun (_ : ℝ) (_ : Vec (2 : ℕ)) => (0 : ℝ)) g u → ∫ (x : Vec (2 : ℕ)) in
    unitCell (2 : ℕ), vecNormSq (spaceGrad (fun (x : Vec (2 : ℕ)) => -spaceLap f x) x) ≤ K ^ (4
    : ℕ) * G ^ (2 : ℕ) →
  let T : ℝ := (κ * K ^ (2 : ℕ))⁻¹;
  T ≤ (1 : ℝ) → B * T ≤ (1 : ℝ) →
  let H : ℝ → Vec (2 : ℕ) → ℝ := inverseFlowTransportTest (h₀ := fun x => -spaceLap f x) X;
  let F : ℝ → ℝ := fun (t : ℝ) => √(classicalCellGradientEnergy u t);
  let Q : ℝ → ℝ := fun (t : ℝ) => ∫ (x : Vec (2 : ℕ)) in unitCell (2 : ℕ), vecDot (spaceGrad (u
    t) x) (spaceGrad (H t) x);
  (ContDiff ℝ ∞ fun (x : Vec (2 : ℕ)) => -spaceLap f x) → (IsZ2Periodic fun (x : Vec (2 : ℕ)) =>
    -spaceLap f x) → ContDiff ℝ ∞ (Function.uncurry H) → (∀ (t : ℝ), (0 : ℝ) ≤ F t) → ∀ t ∈ Icc
    (0 : ℝ) T, Q t ≤ Real.exp (1 : ℝ) * K ^ (2 : ℕ) * G * F t
    := by
  intro b κ K B G g f u X hb hdiv hX hDb hB hK hG hsol hlapGrad T hTle hBT H F Q hlapSmooth
      hlapPer hHSmooth hFnonneg t ht
  have ht1 : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨ht.1, le_trans ht.2 hTle⟩
  have huSlice : ContDiff ℝ (⊤ : ℕ∞) (u t) :=
    classicalSmooth_slice_nonneg hsol.1 ht.1
  have hgradUcont : Continuous (spaceGrad (u t)) := by
    apply continuous_pi
    intro i
    change Continuous (fun x => fderiv ℝ (u t) x (basisVec i))
    exact (huSlice.continuous_fderiv (by simp)).clm_apply continuous_const
  have hHSlice : ContDiff ℝ (⊤ : ℕ∞) (H t) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by
      fun_prop
    exact hHSmooth.comp hmap
  have hgradHcont : Continuous (spaceGrad (H t)) := by
    apply continuous_pi
    intro i
    change Continuous (fun x => fderiv ℝ (H t) x (basisVec i))
    exact (hHSlice.continuous_fderiv (by simp)).clm_apply continuous_const
  have hCS := integral_unitCell_vecDot_abs_le hgradUcont hgradHcont
  have htrans := inverseFlow_transportedGradient_euclidean_cellL2_bound hb hX hdiv
    hB hBT hDb hlapSmooth hlapPer ht
  have hHnonneg : 0 ≤ ∫ x in unitCell 2,
      vecNormSq (spaceGrad (H t) x) :=
    integral_nonneg (fun x => vecNormSq_nonneg _)
  have hsourceNonneg : 0 ≤ ∫ x in unitCell 2,
      vecNormSq (spaceGrad (fun x => -spaceLap f x) x) :=
    integral_nonneg (fun x => vecNormSq_nonneg _)
  have hHbound : ∫ x in unitCell 2,
      vecNormSq (spaceGrad (H t) x) ≤ (Real.exp 1) ^ 2 * K ^ 4 * G ^ 2 := by
    calc
      _ ≤ (Real.exp 1) ^ 2 *
          (∫ x in unitCell 2,
            vecNormSq (spaceGrad (fun x => -spaceLap f x) x)) := htrans
      _ ≤ (Real.exp 1) ^ 2 * (K ^ 4 * G ^ 2) := by
        exact mul_le_mul_of_nonneg_left hlapGrad (by positivity)
      _ = _ := by ring
  have hHroot : Real.sqrt (∫ x in unitCell 2,
      vecNormSq (spaceGrad (H t) x)) ≤ Real.exp 1 * K ^ 2 * G := by
    calc
      _ ≤ Real.sqrt ((Real.exp 1) ^ 2 * K ^ 4 * G ^ 2) :=
        Real.sqrt_le_sqrt hHbound
      _ = Real.exp 1 * K ^ 2 * G := by
        rw [show (Real.exp 1) ^ 2 * K ^ 4 * G ^ 2 =
          (Real.exp 1 * K ^ 2 * G) ^ 2 by ring,
          Real.sqrt_sq_eq_abs]
        exact abs_of_nonneg (by positivity)
  have hFroot : Real.sqrt (∫ x in unitCell 2,
      vecNormSq (spaceGrad (u t) x)) = F t := by
    change Real.sqrt (classicalCellGradientEnergy u t) = F t
    rfl
  have hQabs : |Q t| ≤ F t *
      Real.sqrt (∫ x in unitCell 2,
        vecNormSq (spaceGrad (H t) x)) := by
    change |∫ x in unitCell 2,
      vecDot (spaceGrad (u t) x) (spaceGrad (H t) x)| ≤ _
    rw [← hFroot]
    exact hCS
  calc
    Q t ≤ |Q t| := le_abs_self _
    _ ≤ F t * Real.sqrt (∫ x in unitCell 2,
        vecNormSq (spaceGrad (H t) x)) := hQabs
    _ ≤ F t * (Real.exp 1 * K ^ 2 * G) :=
      mul_le_mul_of_nonneg_left hHroot (hFnonneg t)
    _ = Real.exp 1 * K ^ 2 * G * F t := by ring

private theorem classical_lowMode_trace_bound_of_spectralFacts_euclidean_dual2 :
  ∀ {κ K G : ℝ} {f : Vec (2 : ℕ) → ℝ} {u : ℝ → Vec (2 : ℕ) → ℝ} {X : ℝ → Vec (2 : ℕ) → ℝ → Vec
    (2 : ℕ)}, (0 : ℝ) < κ → (0 : ℝ) < K → (0 : ℝ) ≤ G →
  let T : ℝ := (κ * K ^ (2 : ℕ))⁻¹;
  T ≤ (1 : ℝ) →
  let H : ℝ → Vec (2 : ℕ) → ℝ := inverseFlowTransportTest (h₀ := fun x => -spaceLap f x) X;
  let F : ℝ → ℝ := fun (t : ℝ) => √(classicalCellGradientEnergy u t);
  let P : ℝ → ℝ := fun (t : ℝ) => ∫ (x : Vec (2 : ℕ)) in unitCell (2 : ℕ), u t x * H t x;
  let Q : ℝ → ℝ := fun (t : ℝ) => ∫ (x : Vec (2 : ℕ)) in unitCell (2 : ℕ), vecDot (spaceGrad (u
    t) x) (spaceGrad (H t) x);
  ContinuousOn F (Icc (0 : ℝ) (1 : ℝ)) → (∀ (t : ℝ), (0 : ℝ) ≤ F t) → ContinuousOn Q (Icc (0 :
    ℝ) T) → (∀ t ∈ Icc (0 : ℝ) T, G ^ (2 : ℕ) = P t + κ * ∫ (s : ℝ) in (0 : ℝ)..t, Q s) → (∀ t ∈
    Icc (0 : ℝ) T, |P t| ≤ Real.exp (1 : ℝ) * G * F t) → (∀ t ∈ Icc (0 : ℝ) T, Q t ≤ Real.exp (1
    : ℝ) * K ^ (2 : ℕ) * G * F t) → ∀ t ∈ Icc (0 : ℝ) T, G ≤ Real.exp (1 : ℝ) * F t + Real.exp
    (1 : ℝ) * κ * K ^ (2 : ℕ) * ∫ (s : ℝ) in (0 : ℝ)..t, F s
    := by
  intro κ K G f u X hκ hK hG T hTle H F P Q hFcont hFnonneg hQcont hpairing hPbound hQbound t ht
  let c : ℝ := Real.exp 1 * K ^ 2 * G
  let I : ℝ := ∫ s in (0 : ℝ)..t, F s
  have hQcont_t : ContinuousOn Q (Set.Icc (0 : ℝ) t) := hQcont.mono (by
    intro s hs
    exact ⟨hs.1, le_trans hs.2 ht.2⟩)
  have hQint : IntervalIntegrable Q volume 0 t :=
    hQcont_t.intervalIntegrable_of_Icc ht.1
  have hFcont_t : ContinuousOn F (Set.Icc (0 : ℝ) t) := hFcont.mono (by
    intro s hs
    exact ⟨hs.1, le_trans hs.2 (le_trans ht.2 hTle)⟩)
  have hFint : IntervalIntegrable F volume 0 t :=
    hFcont_t.intervalIntegrable_of_Icc ht.1
  have hcFint : IntervalIntegrable (fun s => c * F s) volume 0 t :=
    hFint.const_mul c
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) t, Q s ≤ c * F s := by
    intro s hs
    have hsT : s ∈ Set.Icc (0 : ℝ) T :=
      ⟨hs.1, le_trans hs.2 ht.2⟩
    simpa [c] using hQbound s hsT
  have hQintbound : (∫ s in (0 : ℝ)..t, Q s) ≤ c * I := by
    calc
      (∫ s in (0 : ℝ)..t, Q s) ≤
          ∫ s in (0 : ℝ)..t, c * F s :=
        intervalIntegral.integral_mono_on ht.1 hQint hcFint hpoint
      _ = c * I := by simp [I, intervalIntegral.integral_const_mul]
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact intervalIntegral.integral_nonneg ht.1 (fun s hs => hFnonneg s)
  have hGsquare : G ^ 2 ≤ Real.exp 1 * G * F t + κ * (c * I) := by
    calc
      G ^ 2 = P t + κ * (∫ s in (0 : ℝ)..t, Q s) := hpairing t ht
      _ ≤ |P t| + κ * (∫ s in (0 : ℝ)..t, Q s) := by
        exact add_le_add (le_abs_self _) le_rfl
      _ ≤ Real.exp 1 * G * F t + κ * (c * I) := by
        exact add_le_add (hPbound t ht)
          (mul_le_mul_of_nonneg_left hQintbound hκ.le)
  let R : ℝ := Real.exp 1 * F t +
    Real.exp 1 * κ * K ^ 2 * I
  have hfactor : G ^ 2 ≤ G * R := by
    calc
      G ^ 2 ≤ Real.exp 1 * G * F t + κ * (c * I) := hGsquare
      _ = G * R := by dsimp [R, c]; ring
  change G ≤ Real.exp 1 * F t +
    Real.exp 1 * κ * K ^ 2 * (∫ s in (0 : ℝ)..t, F s)
  change G ≤ R
  by_cases hGzero : G = 0
  · rw [hGzero]
    dsimp [R]
    positivity
  · have hGpos : 0 < G := lt_of_le_of_ne hG (Ne.symm hGzero)
    by_contra hnot
    have hgap : 0 < G - R := by linarith
    have hbad := mul_pos hGpos hgap
    nlinarith only [hfactor, hbad]

/-- The short-time trace estimate for a smooth Fourier low mode. The spectral
facts are stated separately so the transport and parabolic parts remain
independent of the chosen finite Fourier cutoff representation. -/
theorem classical_lowMode_trace_bound_of_spectralFacts_euclidean
    {b : ℝ → Vec 2 → Vec 2} {κ K B G : ℝ}
    {g f : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ}
    {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    (hX : IsFlow b X)
    (hDb : ∀ r y, ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ B)
    (hmax : max 1 B ≤ κ * K ^ 2)
    (hB : 0 ≤ B) (hκ : 0 < κ) (hK : 0 < K) (hG : 0 ≤ G)
    (hsol : IsClassicalSol b κ (fun _ _ => 0) g u)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfper : IsZ2Periodic f)
    (hinitial : ∫ x in unitCell 2, g x * (-spaceLap f x) = G ^ 2)
    (henergy : gradNormSq (spaceGrad f) = G ^ 2)
    (hlapGrad : ∫ x in unitCell 2,
      vecNormSq (spaceGrad (fun x => -spaceLap f x) x) ≤ K ^ 4 * G ^ 2) :
    G ≤ 2 * Real.exp 1 * K * Real.sqrt κ *
      Real.sqrt (∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t) := by
  have hden : 0 < κ * K ^ 2 := by
    have hone : (1 : ℝ) ≤ κ * K ^ 2 := (le_max_left 1 B).trans hmax
    linarith
  have hTleDen : B ≤ κ * K ^ 2 := (le_max_right 1 B).trans hmax
  let T : ℝ := (κ * K ^ 2)⁻¹
  have hTpos : 0 < T := inv_pos.mpr hden
  have hTle : T ≤ 1 := by
    dsimp [T]
    apply (inv_le_one₀ hden).2
    exact (le_max_left 1 B).trans hmax
  have hBT : B * T ≤ 1 := by
    dsimp [T]
    calc
      B * (κ * K ^ 2)⁻¹ ≤ (κ * K ^ 2) * (κ * K ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hTleDen (inv_nonneg.mpr hden.le)
      _ = 1 := by field_simp [ne_of_gt hden]
  let H : ℝ → Vec 2 → ℝ :=
    inverseFlowTransportTest (h₀ := fun x => -spaceLap f x) X
  let F : ℝ → ℝ := fun t => Real.sqrt (classicalCellGradientEnergy u t)
  let P : ℝ → ℝ := fun t => ∫ x in unitCell 2, u t x * H t x
  let Q : ℝ → ℝ := fun t => ∫ x in unitCell 2,
    vecDot (spaceGrad (u t) x) (spaceGrad (H t) x)
  have hlapSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => -spaceLap f x) :=
    contDiff_neg.comp (classicalSpaceLap_contDiff_top hf)
  have hlapPer : IsZ2Periodic (fun x => -spaceLap f x) := by
    intro k x
    simp [classicalSpaceLap_periodic hfper k x]
  have htest : IsClassicalTransportTest b H :=
    inverseFlowTransportTest_isClassicalTransportTest hb hX hlapSmooth hlapPer
  have hHSmooth : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H) :=
    inverseFlow_laplacianTransport_contDiff_infty hb hX hf
  have hgradJoint := LeftToShow.spaceGrad_continuousOn hsol.1
  have hgradEnergyJoint : ContinuousOn
      (fun p : ℝ × Vec 2 => vecNormSq (spaceGrad (u p.1) p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    apply LeftToShow.continuous_vecNormSq_two.comp_continuousOn
    exact hgradJoint.mono (by
      rintro ⟨s, x⟩ ⟨hs, hx⟩
      exact ⟨hs.1, trivial⟩)
  have hEcube : ContinuousOn
      (fun t => ∫ x in unitCube, vecNormSq (spaceGrad (u t) x))
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_unitCubeIntegral_Icc hgradEnergyJoint
  have hEcell : ContinuousOn (classicalCellGradientEnergy u)
      (Set.Icc (0 : ℝ) 1) := by
    have hEq : classicalCellGradientEnergy u =
        fun t => ∫ x in unitCube, vecNormSq (spaceGrad (u t) x) := by
      funext t
      exact integral_unitCell_eq_unitCube _
    rw [hEq]
    exact hEcube
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    exact Real.continuous_sqrt.comp_continuousOn hEcell
  have hFnonneg : ∀ t, 0 ≤ F t := fun _ => Real.sqrt_nonneg _
  have hhOn : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry H)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    hHSmooth.contDiffOn.mono (by
      intro p hp
      exact Set.mem_univ p)
  have hgradH := LeftToShow.spaceGrad_continuousOn hhOn
  have hdotJoint : ContinuousOn
      (fun p : ℝ × Vec 2 =>
        vecDot (spaceGrad (u p.1) p.2) (spaceGrad (H p.1) p.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
    change ContinuousOn (fun p : ℝ × Vec 2 =>
      ∑ i : Fin 2, spaceGrad (u p.1) p.2 i * spaceGrad (H p.1) p.2 i) _
    apply continuousOn_finsetSum
    intro i hi
    have hgradUcc : ContinuousOn (fun p : ℝ × Vec 2 =>
        spaceGrad (u p.1) p.2) (Set.Icc (0 : ℝ) T ×ˢ Set.univ) :=
      hgradJoint.mono (by
        rintro ⟨s, x⟩ ⟨hs, hx⟩
        exact ⟨hs.1, trivial⟩)
    have huIcc : ContinuousOn
        (fun p : ℝ × Vec 2 => spaceGrad (u p.1) p.2 i)
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
      exact (continuousOn_pi.mp hgradUcc i)
    have hgradHcc : ContinuousOn (fun p : ℝ × Vec 2 =>
        spaceGrad (H p.1) p.2) (Set.Icc (0 : ℝ) T ×ˢ Set.univ) :=
      hgradH.mono (by
        rintro ⟨s, x⟩ ⟨hs, hx⟩
        exact ⟨hs.1, trivial⟩)
    have hHcc : ContinuousOn
        (fun p : ℝ × Vec 2 => spaceGrad (H p.1) p.2 i)
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
      exact (continuousOn_pi.mp hgradHcc i)
    exact huIcc.mul hHcc
  have hQcube : ContinuousOn
      (fun t => ∫ x in unitCube,
        vecDot (spaceGrad (u t) x) (spaceGrad (H t) x))
      (Set.Icc (0 : ℝ) T) := continuousOn_unitCubeIntegral_Icc hdotJoint
  have hQcell : Q = fun t => ∫ x in unitCube,
      vecDot (spaceGrad (u t) x) (spaceGrad (H t) x) := by
    funext t
    simp [Q, Torus.integral_unitCell_eq_unitCube]
  have hQcont : ContinuousOn Q (Set.Icc (0 : ℝ) T) := by
    rw [hQcell]
    exact hQcube
  have hPzero : P 0 = G ^ 2 := by
    have hHzero (x : Vec 2) : H 0 x = -spaceLap f x := by
      change -spaceLap f (X 0 x 0) = -spaceLap f x
      rw [hX.1]
    calc
      P 0 = ∫ x in unitCell 2, g x * (-spaceLap f x) := by
        apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
        intro x hx
        change u 0 x * H 0 x = g x * (-spaceLap f x)
        rw [hsol.2.2.1 x, hHzero x]
      _ = G ^ 2 := hinitial
  have hpairing : ∀ t ∈ Set.Icc (0 : ℝ) T,
      G ^ 2 = P t + κ * (∫ s in (0 : ℝ)..t, Q s) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      rw [intervalIntegral.integral_same, mul_zero, add_zero]
      exact hPzero.symm
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hid := classical_solution_transportPairing_integral_identity
        hb hdiv hsol htest hHSmooth htpos
      calc
        G ^ 2 = P 0 := hPzero.symm
        _ = P t + κ * (∫ s in (0 : ℝ)..t, Q s) := by
          simpa [P, Q] using hid.symm
  have hgradFcell :
      Real.sqrt (∫ x in unitCell 2, vecNormSq (spaceGrad f x)) = G := by
    have hcell : (∫ x in unitCell 2, vecNormSq (spaceGrad f x)) = G ^ 2 := by
      rw [integral_unitCell_eq_unitCube]
      exact henergy
    rw [hcell, Real.sqrt_sq_eq_abs, abs_of_nonneg hG]
  have hFactual (t : ℝ) :
      F t = Real.sqrt (classicalCellGradientEnergy u t) := by
    rfl
  have hPbound : ∀ t ∈ Set.Icc (0 : ℝ) T,
      |P t| ≤ Real.exp 1 * G * F t := by
    intro t ht
    have hu : ContDiff ℝ 1 (u t) :=
      classicalSmooth_slice_nonneg hsol.1 ht.1 |>.of_le (by norm_num)
    have huper : IsZ2Periodic (u t) := hsol.2.1 t ht.1
    have hPa := inverseFlow_laplacian_pairing_abs_le_euclidean hb hX hdiv hB hBT hDb
      hf hfper hu huper ht
    calc
      |P t| ≤ Real.sqrt (classicalCellGradientEnergy u t) *
          (Real.exp 1 * G) := by
            simpa [P, H, classicalCellGradientEnergy, hgradFcell] using hPa
      _ = Real.exp 1 * G * F t := by
        rw [hFactual t]
        ring
  have hQbound : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Q t ≤ Real.exp 1 * K ^ 2 * G * F t := by
    exact @low_mode_transport_pairing_bound b κ K B G g f u X hb hdiv hX hDb hB hK hG hsol
        hlapGrad hTle hBT hlapSmooth hlapPer hHSmooth hFnonneg
  have hdual : ∀ t ∈ Set.Icc (0 : ℝ) T,
      G ≤ Real.exp 1 * F t +
        Real.exp 1 * κ * K ^ 2 * (∫ s in (0 : ℝ)..t, F s) := by
    exact @classical_lowMode_trace_bound_of_spectralFacts_euclidean_dual2 κ K G f u X hκ hK hG
        hTle hFcont hFnonneg hQcont hpairing hPbound hQbound
  have hmain := lowModeTrace_from_transportDuality
    hκ hK hTpos hTle (by rfl) hFcont hdual
  have hFsquare :
      (∫ t in (0 : ℝ)..1, F t ^ 2) =
        ∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le zero_le_one] using ht
    change F t ^ 2 = classicalCellGradientEnergy u t
    rw [hFactual t]
    rw [Real.sq_sqrt]
    exact integral_nonneg (fun x => vecNormSq_nonneg _)
  rw [hFsquare] at hmain
  exact hmain

end AVenhance.Infra.Section5.RelativeError

end
