/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportPairing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic

/-! # RelativeError: integrate the parabolic/transport pairing identity from time zero -/

@[expose] public section

noncomputable section

open Homogenization
open MeasureTheory Set intervalIntegral
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Section5.LeftToShow
open AVenhance.Infra.Torus

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def TransportPairingIntegral.transportClosedCube : Set (Vec 2) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1

theorem TransportPairingIntegral.transportClosedCube_compact : IsCompact
    TransportPairingIntegral.transportClosedCube :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem TransportPairingIntegral.transportUnitCube_ae_closedCube :
    unitCube =ᵐ[(volume : Measure (Vec 2))] TransportPairingIntegral.transportClosedCube := by
  simpa [volume_pi, unitCube, TransportPairingIntegral.transportClosedCube] using
    (Measure.univ_pi_Ioo_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ))
      (g := fun _ : Fin 2 => (1 : ℝ)))

theorem continuousOn_unitCubeIntegral_Icc
    {T : ℝ} {F : ℝ → Vec 2 → ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) :
    ContinuousOn (fun s => ∫ x in unitCube, F s x) (Set.Icc (0 : ℝ) T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hmap : Continuous
      (fun q : Set.Icc (0 : ℝ) T × Vec 2 => (q.1.1, q.2)) := by
    fun_prop
  have hF' : Continuous
      (fun q : Set.Icc (0 : ℝ) T × Vec 2 => F q.1.1 q.2) := by
    exact hF.comp_continuous hmap (fun q => ⟨q.1.2, mem_univ _⟩)
  have hclosed : Continuous
      (fun s : Set.Icc (0 : ℝ) T =>
        ∫ x in TransportPairingIntegral.transportClosedCube, F s.1 x) :=
    continuous_parametric_integral_of_continuous
      (f := fun (s : Set.Icc (0 : ℝ) T) (x : Vec 2) => F s.1 x)
      hF' TransportPairingIntegral.transportClosedCube_compact
  have hEq : (fun s : Set.Icc (0 : ℝ) T =>
      ∫ x in unitCube, F s.1 x) =
    fun s => ∫ x in TransportPairingIntegral.transportClosedCube, F s.1 x := by
    funext s
    exact setIntegral_congr_set TransportPairingIntegral.transportUnitCube_ae_closedCube
  change Continuous (fun s : Set.Icc (0 : ℝ) T =>
    ∫ x in unitCube, F s.1 x)
  rw [hEq]
  exact hclosed

/-- The integrated pairing identity for a smooth classical solution and a
smooth transported test. It includes the initial trace at `t = 0`. -/
theorem classical_solution_transportPairing_integral_identity
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {u h : ℝ → Vec 2 → ℝ}
    (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    (hsol : IsClassicalSol b κ (fun _ _ => 0) g u)
    (htest : IsClassicalTransportTest b h)
    (hhSmooth : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry h))
    {t : ℝ} (ht : 0 < t) :
    (∫ x in unitCell 2, u t x * h t x) + κ *
      (∫ s in (0 : ℝ)..t,
        ∫ x in unitCell 2,
          vecDot (spaceGrad (u s) x) (spaceGrad (h s) x)) =
      ∫ x in unitCell 2, u 0 x * h 0 x := by
  let P : ℝ → ℝ := fun s => ∫ x in unitCell 2, u s x * h s x
  let Q : ℝ → ℝ := fun s => ∫ x in unitCell 2,
    vecDot (spaceGrad (u s) x) (spaceGrad (h s) x)
  have huIcc : ContinuousOn (Function.uncurry u)
      (Set.Icc (0 : ℝ) t ×ˢ Set.univ) := by
    apply hsol.1.continuousOn.mono
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact ⟨hs.1, trivial⟩
  have hhIcc : ContinuousOn (Function.uncurry h)
      (Set.Icc (0 : ℝ) t ×ˢ Set.univ) :=
    hhSmooth.continuous.continuousOn.mono (by
      intro p hp
      exact Set.mem_univ p)
  have hprodIcc : ContinuousOn
      (fun p : ℝ × Vec 2 => u p.1 p.2 * h p.1 p.2)
      (Set.Icc (0 : ℝ) t ×ˢ Set.univ) := huIcc.mul hhIcc
  have hPcube : ContinuousOn
      (fun s => ∫ x in unitCube, u s x * h s x) (Set.Icc (0 : ℝ) t) :=
    continuousOn_unitCubeIntegral_Icc hprodIcc
  have hPcubeEq : P = fun s => ∫ x in unitCube, u s x * h s x := by
    funext s
    simp [P, Torus.integral_unitCell_eq_unitCube]
  have hPcont : ContinuousOn P (Set.Icc (0 : ℝ) t) := by
    rw [hPcubeEq]
    exact hPcube
  have hgradU : ContinuousOn
      (fun p : ℝ × Vec 2 => spaceGrad (u p.1) p.2)
      (Set.Icc (0 : ℝ) t ×ˢ Set.univ) := by
    apply (LeftToShow.spaceGrad_continuousOn hsol.1).mono
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact ⟨hs.1, trivial⟩
  have hhOn : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry h)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := hhSmooth.contDiffOn.mono (by
        intro p hp
        exact Set.mem_univ p)
  have hgradH : ContinuousOn
      (fun p : ℝ × Vec 2 => spaceGrad (h p.1) p.2)
      (Set.Icc (0 : ℝ) t ×ˢ Set.univ) := by
    apply (LeftToShow.spaceGrad_continuousOn hhOn).mono
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact ⟨hs.1, trivial⟩
  have hdotIcc : ContinuousOn
      (fun p : ℝ × Vec 2 =>
        vecDot (spaceGrad (u p.1) p.2) (spaceGrad (h p.1) p.2))
      (Set.Icc (0 : ℝ) t ×ˢ Set.univ) := by
    change ContinuousOn (fun p : ℝ × Vec 2 =>
      ∑ i : Fin 2, spaceGrad (u p.1) p.2 i * spaceGrad (h p.1) p.2 i) _
    apply continuousOn_finsetSum
    intro i hi
    exact ((continuousOn_pi.mp hgradU) i).mul
      ((continuousOn_pi.mp hgradH) i)
  have hQcube : ContinuousOn
      (fun s => ∫ x in unitCube,
        vecDot (spaceGrad (u s) x) (spaceGrad (h s) x))
      (Set.Icc (0 : ℝ) t) :=
    continuousOn_unitCubeIntegral_Icc hdotIcc
  have hQcubeEq : Q = fun s => ∫ x in unitCube,
      vecDot (spaceGrad (u s) x) (spaceGrad (h s) x) := by
    funext s
    simp [Q, Torus.integral_unitCell_eq_unitCube]
  have hQcont : ContinuousOn Q (Set.Icc (0 : ℝ) t) := by
    rw [hQcubeEq]
    exact hQcube
  have hQint : IntervalIntegrable Q volume 0 t :=
    hQcont.intervalIntegrable_of_Icc (le_of_lt ht)
  have hderivInt : IntervalIntegrable (fun s => -κ * Q s) volume 0 t := by
    simpa [mul_assoc] using hQint.const_mul (-κ)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (le_of_lt ht) hPcont
    (fun s hs => classical_solution_transportPairing_derivative
      hb hdiv hsol htest hs.1)
    hderivInt
  have hFTC' :
      (-κ) * (∫ s in (0 : ℝ)..t, Q s) = P t - P 0 := by
    simpa only [intervalIntegral.integral_const_mul] using hFTC
  have hQreplace :
      (∫ s in (0 : ℝ)..t, Q s) =
        ∫ s in (0 : ℝ)..t,
          ∫ x in unitCell 2,
            vecDot (spaceGrad (u s) x) (spaceGrad (h s) x) := by
    rfl
  change P t + κ *
      (∫ s in (0 : ℝ)..t,
        ∫ x in unitCell 2,
          vecDot (spaceGrad (u s) x) (spaceGrad (h s) x)) = P 0
  rw [← hQreplace]
  linarith [hFTC']

end AVenhance.Infra.Section5.RelativeError

end
