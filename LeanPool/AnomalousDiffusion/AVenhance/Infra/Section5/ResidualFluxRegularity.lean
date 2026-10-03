/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ResidualDataRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenHmSourceIdentity

/-! Finite regularity of the spacetime fluxes used by the residual data. -/

@[expose] public section

noncomputable section

open Homogenization
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5

open AVenhance
open AVenhance.Infra.Section4

/-- Joint time-space domain with strictly positive time. -/
abbrev ResidualFluxRegularity.residualPositiveDomain : Set (ℝ × Vec 2) :=
  Set.Ioi (0 : ℝ) ×ˢ Set.univ

theorem ResidualFluxRegularity.residual_qMNR_entry_joint {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m n r : ℕ) (j k : Fin 2) :
    ContDiff ℝ ∞ (fun z : ℝ × Vec 2 => (I.qMNR κ m n r z.1) j k) := by
  have hq := residual_qMNR_contDiff I κ m n r
  have hqj : ContDiff ℝ ∞ (fun t => (I.qMNR κ m n r t) j) :=
    (contDiff_pi.mp hq) j
  have hqjk : ContDiff ℝ ∞ (fun t => (I.qMNR κ m n r t) j k) :=
    (contDiff_pi.mp hqj) k
  exact hqjk.comp contDiff_fst

/-- The finite `A q` flux inherits any regularity order allowed by the
AMNR budget. -/
theorem residual_pairFluxSum_contDiffOn {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (N r p : ℕ) (hbudget : ∀ n ∈ Finset.range N, p + r ≤ Nstar β) :
    ContDiffOn ℝ p
      (amnrPairFluxSum I hΦ m N κm (T (Nstar β)) r)
      ResidualFluxRegularity.residualPositiveDomain := by
  classical
  unfold amnrPairFluxSum
  refine ContDiffOn.sum fun a ha => ?_
  unfold amnrPairSet at ha
  rcases Finset.mem_product.mp ha with ⟨hleft, ha₂⟩
  rcases Finset.mem_product.mp hleft with ⟨hn, hj⟩
  have hn' : a.1.1 ∈ Finset.range N := by simpa using hn
  have hA (i : Fin 2) := amnr_actual_contDiffOn I hΦ hm hκm hθprev hT
    a.1.1 r p (hbudget a.1.1 hn') i a.1.2 a.2
  have hq := ResidualFluxRegularity.residual_qMNR_entry_joint I κm m a.1.1 (r + 1) a.1.2 a.2
  have hqOn : ContDiffOn ℝ p
      (fun z : ℝ × Vec 2 => (I.qMNR κm m a.1.1 (r + 1) z.1) a.1.2 a.2)
      Set.univ := (hq.of_le (by simp)).contDiffOn
  unfold amnrPairFlux
  exact contDiffOn_pi.mpr fun i => by
    simpa [ResidualFluxRegularity.residualPositiveDomain] using (hA i).mul (hqOn.mono
        (Set.subset_univ _))

/-- The endpoint `A q_r` flux has the same finite regularity budget. -/
theorem residual_pairEndpointFluxSum_contDiffOn {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (N r p : ℕ) (hbudget : ∀ n ∈ Finset.range N, p + r ≤ Nstar β) :
    ContDiffOn ℝ p
      (amnrPairEndpointFluxSum I hΦ m N κm (T (Nstar β)) r)
      ResidualFluxRegularity.residualPositiveDomain := by
  classical
  unfold amnrPairEndpointFluxSum
  refine ContDiffOn.sum fun a ha => ?_
  unfold amnrPairSet at ha
  rcases Finset.mem_product.mp ha with ⟨hleft, ha₂⟩
  rcases Finset.mem_product.mp hleft with ⟨hn, hj⟩
  have hn' : a.1.1 ∈ Finset.range N := by simpa using hn
  have hA (i : Fin 2) := amnr_actual_contDiffOn I hΦ hm hκm hθprev hT
    a.1.1 r p (hbudget a.1.1 hn') i a.1.2 a.2
  have hq := ResidualFluxRegularity.residual_qMNR_entry_joint I κm m a.1.1 r a.1.2 a.2
  have hqOn : ContDiffOn ℝ p
      (fun z : ℝ × Vec 2 => (I.qMNR κm m a.1.1 r z.1) a.1.2 a.2)
      Set.univ := (hq.of_le (by simp)).contDiffOn
  unfold amnrPairEndpointFlux
  exact contDiffOn_pi.mpr fun i => by
    simpa [ResidualFluxRegularity.residualPositiveDomain] using (hA i).mul (hqOn.mono
        (Set.subset_univ _))

theorem ResidualFluxRegularity.residual_stDiv_contDiffOn {p : ℕ}
    {F : ℝ × Vec 2 → Vec 2}
    (hF : ContDiffOn ℝ (p + 1) F ResidualFluxRegularity.residualPositiveDomain) :
    ContDiffOn ℝ p (stDiv F) ResidualFluxRegularity.residualPositiveDomain := by
  have hopen : IsOpen ResidualFluxRegularity.residualPositiveDomain := isOpen_Ioi.prod isOpen_univ
  have hD : ContDiffOn ℝ p (fun z => fderiv ℝ F z) ResidualFluxRegularity.residualPositiveDomain :=
    hF.fderiv_of_isOpen hopen (by simp)
  have hterm (i : Fin 2) : ContDiffOn ℝ p
      (fun z => (fderiv ℝ F z (0, basisVec i)) i) ResidualFluxRegularity.residualPositiveDomain :=
          by
    have hv : ContDiffOn ℝ p
        (fun _ : ℝ × Vec 2 => ((0 : ℝ), basisVec i)) ResidualFluxRegularity.residualPositiveDomain
            :=
      contDiffOn_const
    have heval := hD.clm_apply hv
    have hproj := (contDiffOn_const : ContDiffOn ℝ p
      (fun _ : ST => (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ))
      ResidualFluxRegularity.residualPositiveDomain).clm_apply heval
    simpa using hproj
  unfold stDiv
  exact ContDiffOn.sum fun i hi => hterm i

/-- `H_{m,r}` has the two derivatives required by the residual calculus. -/
theorem residual_Hmr_contDiffOn_two {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (r : ℕ) (hr : r ∈ Finset.range (Jcut β)) :
    ContDiffOn ℝ 2
      (fun z : ST => I.Hmr hΦ m κm (T (Nstar β)) r z.1 z.2)
      ResidualFluxRegularity.residualPositiveDomain := by
  have hbudget (n : ℕ) (_hn : n ∈ Finset.range (Nstar β)) :
      3 + r ≤ Nstar β := by
    have hcut := Finset.mem_range.mp hr
    unfold Jcut at hcut
    omega
  have hflux := residual_pairFluxSum_contDiffOn I hΦ hm hκm hθprev hT
    (Nstar β) r 3 hbudget
  have hdiv := ResidualFluxRegularity.residual_stDiv_contDiffOn hflux
  apply hdiv.congr
  intro z hz
  have hpos : ResidualFluxRegularity.residualPositiveDomain ∈ 𝓝 z :=
    (isOpen_Ioi.prod isOpen_univ).mem_nhds hz
  have hFat : DifferentiableAt ℝ
      (amnrPairFluxSum I hΦ m (Nstar β) κm (T (Nstar β)) r) z :=
    (hflux.contDiffAt hpos).differentiableAt (by simp)
  exact frozen_Hmr_eq_stDiv_pairFluxSum I hΦ m κm (T (Nstar β)) r z.1 z.2 hFat

/-- The finite `H_m` sum has two joint derivatives on positive time. -/
theorem residual_Hm_contDiffOn_two {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ContDiffOn ℝ 2
      (fun z : ST => I.Hm hΦ m κm (T (Nstar β)) z.1 z.2)
      ResidualFluxRegularity.residualPositiveDomain := by
  unfold Ingredients.Hm
  refine ContDiffOn.sum fun r hr =>
    residual_Hmr_contDiffOn_two I hΦ hm hκm hθprev hT r hr

end AVenhance.Infra.Section5

end
