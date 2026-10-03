/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIEnergyIoiBound

/-! # The forced energy estimate on the open time half-line

`forced_energy_estimate_Ioi`: the energy estimate of `Energy/Estimate` for a comparison function
`v` that is jointly `C²` only on `(0,∞) × ℝ²`, with the initial defect controlled from the right,
`√‖u(s) - v(s)‖² ≤ D` for `s → 0⁺`.  Proof: the integrated energy bound on `[s,t]`
(`PartIEnergyIoiBound`), then `s → 0⁺` along the eventual set where the initial bound holds, using
monotone convergence for the space-time gradient energy. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Homogenization
open AVenhance.Infra.Torus AVenhance.Infra.Classical
open scoped Topology

namespace AVenhance.Infra.Section5.Integration.EnergyIoi

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration.Energy

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def PartIEnergyIoi.closedCube : Set (Vec 2) := Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1

theorem PartIEnergyIoi.isCompact_closedCube : IsCompact PartIEnergyIoi.closedCube :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem PartIEnergyIoi.unitCube_subset_closedCube : unitCube ⊆ PartIEnergyIoi.closedCube :=
  Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self

theorem PartIEnergyIoi.continuous_vecNormSq_two' : Continuous (fun v : Vec 2 => vecNormSq v) := by
  unfold vecNormSq vecDot
  fun_prop

/-- The space-time energy over `(a,1) × cube` as an iterated integral, for a field continuous on
`[a,1] × ℝ²`. -/
theorem setIntegral_Ioo_prod_unitCube {V : ℝ → Vec 2 → Vec 2} {a : ℝ} (hab : a ≤ 1)
    (hV : ContinuousOn (fun p : ℝ × Vec 2 => V p.1 p.2) (Set.Icc a 1 ×ˢ Set.univ)) :
    ∫ p in Set.Ioo a 1 ×ˢ unitCube, vecNormSq (V p.1 p.2) =
      ∫ t in a..1, ∫ x in unitCube, vecNormSq (V t x) := by
  have hcont : ContinuousOn (fun p : ℝ × Vec 2 => vecNormSq (V p.1 p.2))
      (Set.Icc a 1 ×ˢ PartIEnergyIoi.closedCube) :=
    PartIEnergyIoi.continuous_vecNormSq_two'.comp_continuousOn (hV.mono (fun p hp => ⟨hp.1,
        mem_univ _⟩))
  have hint : IntegrableOn (fun p : ℝ × Vec 2 => vecNormSq (V p.1 p.2))
      (Set.Ioo a 1 ×ˢ unitCube) volume :=
    (hcont.integrableOn_compact (isCompact_Icc.prod PartIEnergyIoi.isCompact_closedCube)).mono_set
      (Set.prod_mono Set.Ioo_subset_Icc_self PartIEnergyIoi.unitCube_subset_closedCube)
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [setIntegral_prod _ hint, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo]

variable {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ} {u v : ℝ → Vec 2 → ℝ}

/-- The joint error gradient is continuous on `[a,∞) × ℝ²` for `a > 0`. -/
theorem IoiSetup.errGrad_jointContinuousOn (S : IoiSetup φ κ θ₀ u v) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (u p.1) p.2 - spaceGrad (v p.1) p.2)
      (Set.Ici a ×ˢ Set.univ) := by
  refine ((S.cutoff ha).errGrad_jointContinuousOn.mono
    (Set.prod_mono (fun r hr => le_trans ha.le hr) le_rfl)).congr ?_
  rintro ⟨r, x⟩ hp
  have hr : a / 2 ≤ r := by linarith [(show a ≤ r from hp.1)]
  simp only [cutoffV_slice_eq ha v hr]

/-- Energy bound from the initial bound at a small positive time. -/
theorem IoiSetup.energy_bound_of_init (S : IoiSetup φ κ θ₀ u v)
    (hfin : timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x) ≠ ⊤)
    {D : ℝ} {s τ : ℝ} (hs : 0 < s) (hsτ : s ≤ τ) (hτ : τ ≤ 1)
    (hD : Real.sqrt (l2NormSq (fun x => u s x - v s x)) ≤ D) :
    l2NormSq (fun x => u τ x - v τ x) + κ * ∫ r in s..τ, errGrad u v r ≤
      D ^ 2 + (timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x)).toReal ^ 2 / κ := by
  have hcell : ∀ r, l2NormSq (fun x => u r x - v r x) =
      ∫ x in unitCell 2, (u r x - v r x) ^ 2 :=
    fun r => (integral_unitCell_eq_unitCube _).symm
  have h := S.interval_bound hfin hs hsτ hτ
  rw [← hcell, ← hcell] at h
  have hE : l2NormSq (fun x => u s x - v s x) ≤ D ^ 2 := (Real.sqrt_le_iff.1 hD).2
  linarith

/-- The space-time gradient energy, as `s → 0⁺`. -/
theorem IoiSetup.spaceTimeGradNormSq_bound (S : IoiSetup φ κ θ₀ u v)
    (hfin : timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x) ≠ ⊤)
    {D : ℝ}
    (hinit : ∀ᶠ s in 𝓝[>] (0 : ℝ), Real.sqrt (l2NormSq (fun x => u s x - v s x)) ≤ D) :
    κ * spaceTimeGradNormSq (fun s x => spaceGrad (u s) x - spaceGrad (v s) x) ≤
      D ^ 2 + (timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x)).toReal ^ 2 / κ := by
  set B := D ^ 2 + (timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x)).toReal ^ 2 / κ
    with hB
  have hκ := S.hκ
  have hBnn : 0 ≤ B := by positivity
  set V : ℝ → Vec 2 → Vec 2 := fun s x => spaceGrad (u s) x - spaceGrad (v s) x with hV
  by_cases hI : IntegrableOn (fun p : ℝ × Vec 2 => vecNormSq (V p.1 p.2)) timeCube
  swap
  · have h0 : spaceTimeGradNormSq V = 0 := by
      unfold spaceTimeGradNormSq
      exact integral_undef hI
    rw [h0]
    simpa using hBnn
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let A : ℕ → Set (ℝ × Vec 2) := fun n => Set.Ioo (a n) 1 ×ˢ unitCube
  have hapos : ∀ n, 0 < a n := fun n => by positivity
  have hmono : Monotone A := by
    intro m n hmn
    refine Set.prod_mono (Set.Ioo_subset_Ioo ?_ le_rfl) le_rfl
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hunion : (⋃ n, A n) = timeCube := by
    ext ⟨r, x⟩
    simp only [Set.mem_iUnion, A, timeCube, Set.mem_prod, Set.mem_Ioo]
    constructor
    · rintro ⟨n, ⟨h1, h2⟩, hx⟩
      exact ⟨⟨(hapos n).trans h1, h2⟩, hx⟩
    · rintro ⟨⟨h1, h2⟩, hx⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt h1
      exact ⟨n, ⟨hn, h2⟩, hx⟩
  have hlim := tendsto_setIntegral_of_monotone
    (f := fun p : ℝ × Vec 2 => vecNormSq (V p.1 p.2)) (μ := volume)
    (fun n => measurableSet_Ioo.prod measurableSet_unitCube) hmono (by rwa [hunion])
  rw [hunion] at hlim
  have hta : Tendsto a atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hapos⟩
  have hev : ∀ᶠ n in atTop, (∫ p in A n, vecNormSq (V p.1 p.2)) ≤ B / κ := by
    have h1 := hta.eventually (hinit.and (Ioo_mem_nhdsGT zero_lt_one))
    filter_upwards [h1] with n hn
    obtain ⟨hD, hn1⟩ := hn
    have hcont : ContinuousOn (fun p : ℝ × Vec 2 => V p.1 p.2) (Set.Icc (a n) 1 ×ˢ Set.univ) :=
      (S.errGrad_jointContinuousOn (hapos n)).mono
        (Set.prod_mono (fun r hr => hr.1) le_rfl)
    have heq := setIntegral_Ioo_prod_unitCube hn1.2.le hcont
    have hbd := S.energy_bound_of_init hfin (hapos n) hn1.2.le le_rfl hD
    have hE1 : 0 ≤ l2NormSq (fun x => u 1 x - v 1 x) := integral_nonneg fun _ => sq_nonneg _
    rw [le_div_iff₀ hκ]
    change (∫ p in Set.Ioo (a n) 1 ×ˢ unitCube, vecNormSq (V p.1 p.2)) * κ ≤ B
    rw [heq]
    change (∫ r in a n..1, errGrad u v r) * κ ≤ B
    linarith
  have hle := le_of_tendsto hlim hev
  rw [le_div_iff₀ hκ] at hle
  unfold spaceTimeGradNormSq
  change κ * ∫ p in timeCube, vecNormSq (V p.1 p.2) ≤ B
  linarith

end AVenhance.Infra.Section5.Integration.EnergyIoi

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5 EnergyIoi
open scoped Topology

/-- The forced energy estimate on the open time half-line: `v` need only be jointly `C²` on
`(0,∞) × ℝ²`, and the initial defect is controlled from the right (`s → 0⁺`). -/
theorem forced_energy_estimate_Ioi {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {κ : ℝ}
    (hκ : 0 < κ) {θ₀ : Vec 2 → ℝ} {u v : ℝ → Vec 2 → ℝ}
    (hu : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) θ₀ u)
    (hv : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => v p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (hvs : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hvp : ∀ t, 0 < t → IsZ2Periodic (v t))
    (hfin : timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x) ≠ ⊤)
    {D : ℝ} (hinit : ∀ᶠ s in 𝓝[>] (0 : ℝ), Real.sqrt (l2NormSq (fun x => u s x - v s x)) ≤ D) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => u t x - v t x)) +
        Real.sqrt κ * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (u s) x - spaceGrad (v s) x)) ≤
      2 * (D + (timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x)).toReal /
        Real.sqrt κ) := by
  intro t ht
  have S : IoiSetup φ κ θ₀ u v := ⟨hφ, hκ, hu, hv, hvs, hvp⟩
  set F := (timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x)).toReal with hF
  have hFnn : 0 ≤ F := ENNReal.toReal_nonneg
  have hD : 0 ≤ D := by
    obtain ⟨s, hs⟩ := hinit.exists
    exact (Real.sqrt_nonneg _).trans hs
  obtain ⟨s, hsD, hs0, hst⟩ : ∃ s, Real.sqrt (l2NormSq (fun x => u s x - v s x)) ≤ D ∧
      0 < s ∧ s < t := by
    obtain ⟨s, hs1, hs2⟩ := (hinit.and (Ioo_mem_nhdsGT ht.1)).exists
    exact ⟨s, hs1, hs2.1, hs2.2⟩
  have hbd := S.energy_bound_of_init hfin hs0 hst.le ht.2 hsD
  have hint : 0 ≤ ∫ r in s..t, Energy.errGrad u v r :=
    intervalIntegral.integral_nonneg hst.le fun r _ => Energy.errGrad_nonneg u v r
  have hgrad := S.spaceTimeGradNormSq_bound hfin hinit
  rw [← hF] at hbd hgrad
  have ha : l2NormSq (fun x => u t x - v t x) ≤ D ^ 2 + F ^ 2 / κ := by
    linarith [mul_nonneg hκ.le hint]
  have h := sqrt_energy_arith hκ (sq_nonneg D) hFnn ha hgrad
  rwa [Real.sqrt_sq hD] at h

end AVenhance.Infra.Section5.Integration

end
