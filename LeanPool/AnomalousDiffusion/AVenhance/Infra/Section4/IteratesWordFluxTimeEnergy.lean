/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Representation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordDriftPairing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordTimeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SMatRegularity

/-! All-order terminal energy with the actual explicit flux pairings. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The differentiated time energy has the literal preceding flux and the
current stream error on its right-hand side. The equality is at every
terminal time; no supremum and full-dissipation interchange is used. -/
theorem iterate_classical_word_flux_time_energy_identity
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    {κ : ℝ} {u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → ℝ}
    (hsol : IsClassicalSol (streamVel φ) κ
      (fun t => vecDiv (fun x => (A t x).mulVec (spaceGrad (v t) x))) u₀ u)
    (hA : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (A t))
    (hAp : ∀ t, 0 < t → IsZ2Periodic (A t))
    (hv : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hvp : ∀ t, 0 < t → IsZ2Periodic (v t))
    (w : List (Fin 2)) {s : ℝ} (hs : 0 ≤ s) :
    (l2NormSq (iterateSpatialWord w (u s)) - l2NormSq (iterateSpatialWord w u₀)) / 2 +
      κ * (∫ t in 0..s, ∫ x in unitCube,
        vecNormSq (spaceGrad (iterateSpatialWord w (u t)) x)) =
      ∫ t in 0..s,
        -(∫ x in unitCube, vecDot (spaceGrad (iterateSpatialWord w (u t)) x)
          (iterateWordFlux (A t) (v t) w x)) -
        (∫ x in unitCube, vecDot (spaceGrad (iterateSpatialWord w (u t)) x)
          (iterateWordFlux (fun y => φ t y • sigmaMat) (u t) w x)) := by
  rw [iterate_classical_word_time_energy_identity_of_smooth hφ hsol w hs]
  apply intervalIntegral.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t ht
  have htp : 0 < t := by
    rw [Set.uIoc_of_le hs] at ht
    exact ht.1
  exact iterate_word_forcing_drift_pairing hφ
    (hsol.1.mono (fun z hz => ⟨(show 0 < z.1 from hz.1).le, Set.mem_univ z.2⟩))
    (hA t htp) (hv t htp) (hAp t htp) (hvp t htp) htp (hsol.2.1 t htp.le) w

/-- Every actual iterate in the range has the initial-boundary smooth carrier. -/
theorem iterates_smooth_up_to_initial {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => θprev z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {i : ℕ} (hi : i ≤ Nstar β) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => T i z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  by_cases hz : i = 0
  · subst i
    simpa only [hT.1] using hθ
  · exact (hT.2 i (by omega) hi).1

/-- The preceding increment's smoothness is derived from the actual carriers. -/
theorem iterateIncrement_smooth_up_to_initial {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => θprev z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {i : ℕ} (hi : i ≤ Nstar β) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => iterateIncrement T i z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  cases i with
  | zero => simpa only [iterateIncrement_zero] using iterates_smooth_up_to_initial I hΦ hT hθ hi
  | succ i =>
    simpa only [iterateIncrement_succ] using
      (iterates_smooth_up_to_initial I hΦ hT hθ hi).sub
        (iterates_smooth_up_to_initial I hΦ hT hθ (by omega : i ≤ Nstar β))

/-- Actual increments inherit periodicity throughout the iteration range. -/
theorem iterateIncrement_periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : ∀ t, 0 ≤ t → IsZ2Periodic (θprev t))
    {i : ℕ} (hi : i ≤ Nstar β) {t : ℝ} (ht : 0 ≤ t) :
    IsZ2Periodic (iterateIncrement T i t) := by
  cases i with
  | zero => simpa only [iterateIncrement_zero, hT.1] using hθ t ht
  | succ i =>
    intro k x
    simp only [iterateIncrement_succ]
    rw [iterates_periodic I hΦ hT hθ hi ht k x,
      iterates_periodic I hΦ hT hθ (by omega : i ≤ Nstar β) ht k x]

/-- The actual sMat is periodic when the pulled flow Jacobians are periodic. -/
theorem iterate_sMat_periodic_of_flow {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κm t : ℝ)
    (hp : ∀ l, IsZ2Periodic (I.flowGrad hΦ m l t)) :
    IsZ2Periodic (I.sMat hΦ m κm t) := by
  exact (sMat_coarseCoeffForm I hΦ m κm).periodic t hp

/-- Literal all-order increment energy with both forcing fluxes explicit.
Coefficient regularity and periodicity are discharged from the conditional
actual flow carriers. No forcing formula, energy bound or recurrence is assumed. -/
theorem iterate_increment_word_flux_time_energy_identity {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hflow : ∀ t, 0 < t → ∀ l : ℤ,
      ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t))
    (hflowp : ∀ t, 0 < t → ∀ l : ℤ, IsZ2Periodic (I.flowGrad hΦ m l t))
    (hm : 1 ≤ m) (i : ℕ) (hi : i + 1 ≤ Nstar β)
    (w : List (Fin 2)) {s : ℝ} (hs : 0 ≤ s) :
    l2NormSq (iterateSpatialWord w (iterateIncrement T (i + 1) s)) / 2 +
      κprev * (∫ t in 0..s, ∫ x in unitCube, vecNormSq
        (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) t)) x)) =
      ∫ t in 0..s,
        -(∫ x in unitCube, vecDot
          (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) t)) x)
          (iterateWordFlux (fun y => I.Kmat κm m t -
            κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm t y)
            (iterateIncrement T i t) w x)) -
        (∫ x in unitCube, vecDot
          (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) t)) x)
          (iterateWordFlux (fun y => Φ (m - 1) t y • sigmaMat)
            (iterateIncrement T (i + 1) t) w x)) := by
  have hA (t : ℝ) (ht : 0 < t) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) :=
    contDiff_const.add (AVenhance.Infra.Section5.sMat_spatial_contDiff
      I hΦ m hm κm t (hflow t ht))
  have hAp (t : ℝ) (ht : 0 < t) : IsZ2Periodic
      (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) := by
    intro k x
    dsimp only
    rw [iterate_sMat_periodic_of_flow I hΦ m κm t (hflowp t ht) k x]
  have hv (t : ℝ) (ht : 0 < t) : ContDiff ℝ (⊤ : ℕ∞) (iterateIncrement T i t) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
    exact (iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 (by omega : i ≤ Nstar
        β)).comp_contDiff
      hmap (fun x => ⟨ht.le, Set.mem_univ x⟩)
  obtain ⟨hprev, _⟩ := hΦ.2 m hm
  have he := iterate_classical_word_flux_time_energy_identity hprev
    (increment_classical_forcing I hΦ hT hθ (fun t ht => (hA t ht).of_le (by simp)) i hi)
    hA hAp hv
    (fun t ht => iterateIncrement_periodic I hΦ hT hθ.2.1 (by omega : i ≤ Nstar β) ht.le)
    w hs
  simpa only [iterateSpatialWord_zero, l2NormSq, zero_pow (by omega : 2 ≠ 0),
    integral_zero, sub_zero] using he

end AVenhance.Infra.Section4
