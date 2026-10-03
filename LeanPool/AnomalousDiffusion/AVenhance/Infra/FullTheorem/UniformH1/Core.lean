/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformH1.Algebra
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.UniformContracts
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.Statements

/-! # `H¹` case of `r.LeBron.2`: the approximation argument

Given the analytic-case Hölder bound (`hana`), the `L²` contraction of differences (`hdiff`),
existence (`hexist`) and the energy bound (`henergy`) for a fixed drift `b` and `κ`, a weak solution
with mean-zero `H¹` data is `ν`-Hölder in time with `ν = μ/(1+p)` and constant `∝ ‖θ₀‖_{H¹}`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.UniformH1

open AVenhance AVenhance.Infra.Section5

theorem holder_of_analytic {b : ℝ → Vec 2 → Vec 2} {κ μ p K : ℝ}
    (hμ : 0 < μ) (hp : 0 ≤ p) (hK : 0 ≤ K) (happrox : HeatApproxH1Contract)
    (hana : ∀ R : ℝ, 0 < R → ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → IsZ2Periodic g →
      MeanZeroOn unitCube g → IsThetaAnalytic R g → ∀ θ' : ℝ → Vec 2 → ℝ,
      IsWeakSolution b κ g θ' →
      IsHolderTimeL2 μ (K * (1 + R ^ (-p)) *
        Real.sqrt (l2NormSq g + gradNormSq (spaceGrad g))) θ')
    (hdiff : ∀ f g : Vec 2 → ℝ, MemL2On unitCube f → MemL2On unitCube g →
      ∀ θ θ' : ℝ → Vec 2 → ℝ, IsWeakSolution b κ f θ → IsWeakSolution b κ g θ' →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        l2NormSq (fun x => θ t x - θ' t x) ≤ l2NormSq (fun x => f x - g x))
    (hexist : ∀ g : Vec 2 → ℝ, MemL2On unitCube g → ∃ θ' : ℝ → Vec 2 → ℝ, IsWeakSolution b κ g θ')
    (henergy : ∀ f : Vec 2 → ℝ, MemL2On unitCube f → ∀ θ : ℝ → Vec 2 → ℝ,
      IsWeakSolution b κ f θ → ∀ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (θ t) ≤ l2NormSq f)
    {θ₀ : Vec 2 → ℝ} {Dθ₀ : Vec 2 → Vec 2} (hθ₀ : IsPeriodicH1With θ₀ Dθ₀)
    (hm : MeanZeroOn unitCube θ₀) {θ : ℝ → Vec 2 → ℝ} (hθ : IsWeakSolution b κ θ₀ θ) :
    HolderTimeL2Le (μ / (1 + p))
      ((11 + 4 * (2 : ℝ) ^ p * K) * Real.sqrt (l2NormSq θ₀ + gradNormSq Dθ₀)) θ := by
  have hf0 : MemL2On unitCube θ₀ := hθ₀.2.2.1
  have hslice : ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (θ t) := by
    obtain ⟨Dθ, hD⟩ := hθ
    exact fun t ht => (hD.1 t ht).2
  set N₁ := Real.sqrt (l2NormSq θ₀ + gradNormSq Dθ₀) with hN₁
  set n0 := Real.sqrt (l2NormSq θ₀) with hn0
  have hl0 := l2NormSq_nonneg θ₀
  have hg0 := gradNormSq_nonneg Dθ₀
  have hN₀ : 0 ≤ N₁ := Real.sqrt_nonneg _
  have hn0N : n0 ≤ N₁ := Real.sqrt_le_sqrt (by linarith)
  have hp1 : 0 < 1 + p := by linarith
  set ν := μ / (1 + p) with hν
  have hνpos : 0 < ν := div_pos hμ hp1
  have hμν : μ = ν * (1 + p) := by rw [hν]; field_simp
  have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt (l2NormSq (θ t)) ≤ n0 := fun t ht =>
    Real.sqrt_le_sqrt (henergy θ₀ hf0 θ hθ t ht)
  have hn0nn : 0 ≤ n0 := Real.sqrt_nonneg _
  set C : ℝ := 11 + 4 * (2 : ℝ) ^ p * K with hC
  have h2p : (1 : ℝ) ≤ 2 ^ p := Real.one_le_rpow (by norm_num) hp
  have hC11 : 11 ≤ C := by rw [hC]; have : 0 ≤ 4 * (2 : ℝ) ^ p * K := by positivity
                           linarith
  have hC0 : 0 ≤ C := by linarith
  refine ⟨hslice, n0, C * N₁ - n0, by linarith, hsup, ?_⟩
  have hB0 : 0 ≤ C * N₁ - n0 := by
    have : 11 * N₁ ≤ C * N₁ := mul_le_mul_of_nonneg_right hC11 hN₀
    linarith
  set H := C * N₁ - n0 with hH
  have hH' : (10 + 4 * (2 : ℝ) ^ p * K) * N₁ ≤ H := by
    rw [hH, hC]; nlinarith only [hn0N]
  intro s hs t ht
  have hhs : |t - s| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hdiff0 : Real.sqrt (l2NormSq (fun x => θ t x - θ s x)) ≤ 2 * n0 := by
    have := sqrt_l2_sub_le (hslice t ht) (hslice s hs)
    linarith [hsup t ht, hsup s hs]
  have hnn : ∀ q : ℝ, 0 ≤ q → 0 ≤ H * q := fun q hq => mul_nonneg hB0 hq
  rcases eq_or_lt_of_le (abs_nonneg (t - s)) with h0 | hpos
  · have hts : t = s := by
      have := h0.symm; rwa [abs_eq_zero, sub_eq_zero] at this
    subst hts
    have : l2NormSq (fun x => θ t x - θ t x) = 0 := by simp [l2NormSq]
    rw [this, Real.sqrt_zero]
    exact hnn _ (Real.rpow_nonneg (abs_nonneg _) _)
  set h := |t - s| with hhdef
  have hhν : 0 < h ^ ν := Real.rpow_pos_of_pos hpos _
  have hhν1 : h ^ ν ≤ 1 := Real.rpow_le_one hpos.le hhs hνpos.le
  rcases eq_or_lt_of_le hl0 with hA0 | hA
  · -- zero data
    have : n0 = 0 := by rw [hn0, ← hA0, Real.sqrt_zero]
    have := hdiff0
    rw [‹n0 = 0›] at this
    exact this.trans (by simpa using hnn _ (Real.rpow_nonneg hpos.le ν))
  -- positive data
  have hgrad := gradient_pos hθ₀ hm hA
  have hG : 0 < Real.sqrt (gradNormSq Dθ₀) := Real.sqrt_pos.mpr hgrad
  set G := Real.sqrt (gradNormSq Dθ₀) with hGdef
  have hGN : G ≤ N₁ := Real.sqrt_le_sqrt (by linarith)
  have hn0pos : 0 < n0 := Real.sqrt_pos.mpr hA
  set L := datumLength θ₀ Dθ₀ with hL
  have hLG : L * G = n0 := by
    rw [hL, datumLength]; exact div_mul_cancel₀ _ hG.ne'
  have hLpos : 0 < L := by
    by_contra hneg
    have : L * G ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) hG.le
    linarith
  rcases le_or_gt (h ^ ν) (L / 4) with hsmall | hbig
  · -- approximation
    set α := h ^ ν / L with hα
    have hαpos : 0 < α := div_pos hhν hLpos
    have hα4 : α ≤ 1 / 4 := by
      rw [hα, div_le_iff₀ hLpos]; linarith
    obtain ⟨g, hgL2, hgper, hgmean, hgsm, hgan, herr, hlow, hgrg⟩ :=
      happrox hθ₀ hm hA hαpos hα4
    obtain ⟨θt, hθt⟩ := hexist g hgL2
    have hαL : α * L / 2 = h ^ ν / 2 := by rw [hα]; field_simp
    rw [hαL] at hgan
    have hRpos : 0 < h ^ ν / 2 := by positivity
    have hNg := hana _ hRpos g hgsm hgper hgmean hgan θt hθt s hs t ht
    -- the three terms
    have herrN : Real.sqrt (l2NormSq (fun x => θ₀ x - g x)) ≤ α * n0 := by
      calc Real.sqrt (l2NormSq (fun x => θ₀ x - g x)) ≤ Real.sqrt (α ^ 2 * l2NormSq θ₀) :=
            Real.sqrt_le_sqrt herr
        _ = α * n0 := by
          rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq_eq_abs, abs_of_pos hαpos]
    have e1 : Real.sqrt (l2NormSq (fun x => θ t x - θt t x)) ≤ α * n0 :=
      (Real.sqrt_le_sqrt (hdiff θ₀ g hf0 hgL2 θ θt hθ hθt t ht)).trans herrN
    have e3 : Real.sqrt (l2NormSq (fun x => θt s x - θ s x)) ≤ α * n0 := by
      have := hdiff θ₀ g hf0 hgL2 θ θt hθ hθt s hs
      have e : l2NormSq (fun x => θt s x - θ s x) = l2NormSq (fun x => θ s x - θt s x) := by
        simp only [l2NormSq]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only
        ring
      rw [e]
      exact (Real.sqrt_le_sqrt this).trans herrN
    have hts := sqrt_l2_tri (a := θ t) (b := θt t) (c := θ s)
      (hslice t ht) (hθt.elim fun D hD => (hD.1 t ht).2) (hslice s hs)
    have hts2 := sqrt_l2_tri (a := θt t) (b := θt s) (c := θ s)
      (hθt.elim fun D hD => (hD.1 t ht).2) (hθt.elim fun D hD => (hD.1 s hs).2) (hslice s hs)
    have hts3 : Real.sqrt (l2NormSq (fun x => θ t x - θ s x)) ≤
        Real.sqrt (l2NormSq (fun x => θ t x - θt t x)) +
        (Real.sqrt (l2NormSq (fun x => θt t x - θt s x)) +
          Real.sqrt (l2NormSq (fun x => θt s x - θ s x))) := by
      refine hts.trans ?_
      have h3 := sqrt_l2_tri (a := θt t) (b := θt s) (c := θ s)
        (hθt.elim fun D hD => (hD.1 t ht).2) (hθt.elim fun D hD => (hD.1 s hs).2) (hslice s hs)
      linarith
    -- the H¹ norm of g
    have hng : Real.sqrt (l2NormSq g) ≤ 5 / 4 * n0 := by
      have := sqrt_l2_sub_le hf0 (hf0.sub hgL2)
      have e : (fun x => θ₀ x - (θ₀ x - g x)) = g := by funext x; ring
      have h' := sqrt_l2_sub_le (a := θ₀) (b := fun x => θ₀ x - g x) hf0 (hf0.sub hgL2)
      rw [e] at h'
      have : α * n0 ≤ 1 / 4 * n0 := mul_le_mul_of_nonneg_right hα4 hn0nn
      linarith
    have hSg : Real.sqrt (l2NormSq g + gradNormSq (spaceGrad g)) ≤ 2 * N₁ := by
      rw [Real.sqrt_le_left (by positivity)]
      have hgsq : l2NormSq g ≤ (5 / 4 * n0) ^ 2 := by
        have := Real.sq_sqrt (l2NormSq_nonneg g)
        rw [← this]
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hng 2
      have : n0 ^ 2 = l2NormSq θ₀ := Real.sq_sqrt hl0
      have hN2 : N₁ ^ 2 = l2NormSq θ₀ + gradNormSq Dθ₀ := Real.sq_sqrt (by linarith)
      rw [mul_pow, hN2]
      nlinarith only [hgsq, hgrg, this, hl0, hg0]
    have hRp1 := one_le_scale (ν := ν) (p := p) hpos hhs hνpos.le hp
    set Rp := (h ^ ν / 2) ^ (-p) with hRp
    have hid : Rp * h ^ μ = (2 : ℝ) ^ p * h ^ ν := rpow_scale_identity hpos hμν
    have hhμ : 0 ≤ h ^ μ := Real.rpow_nonneg hpos.le _
    have e2 : Real.sqrt (l2NormSq (fun x => θt t x - θt s x)) ≤
        4 * K * N₁ * ((2 : ℝ) ^ p * h ^ ν) := by
      refine hNg.trans ?_
      rw [← hid]
      have h1 : K * (1 + Rp) ≤ K * (2 * Rp) :=
        mul_le_mul_of_nonneg_left (by linarith) hK
      calc K * (1 + Rp) * Real.sqrt (l2NormSq g + gradNormSq (spaceGrad g)) * h ^ μ
          ≤ K * (2 * Rp) * (2 * N₁) * h ^ μ := by gcongr
        _ = 4 * K * N₁ * (Rp * h ^ μ) := by ring
    have hαn : α * n0 ≤ h ^ ν * N₁ := by
      have : α * n0 = h ^ ν * G := by
        rw [hα, ← hLG]; field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hGN hhν.le
    have htot : Real.sqrt (l2NormSq (fun x => θ t x - θ s x)) ≤
        (10 + 4 * (2 : ℝ) ^ p * K) * N₁ * h ^ ν := by
      have hp0 : 0 ≤ N₁ * h ^ ν := mul_nonneg hN₀ hhν.le
      have e : 4 * K * N₁ * ((2 : ℝ) ^ p * h ^ ν) = 4 * (2 : ℝ) ^ p * K * (N₁ * h ^ ν) := by ring
      have e' : (10 + 4 * (2 : ℝ) ^ p * K) * N₁ * h ^ ν =
          10 * (N₁ * h ^ ν) + 4 * (2 : ℝ) ^ p * K * (N₁ * h ^ ν) := by ring
      have e'' : h ^ ν * N₁ = N₁ * h ^ ν := by ring
      rw [e']
      rw [e] at e2
      rw [e''] at hαn
      linarith
    exact htot.trans (mul_le_mul_of_nonneg_right hH' hhν.le)
  · -- large increment
    have : n0 = L * G := hLG.symm
    have h1 : 2 * n0 ≤ 8 * h ^ ν * N₁ := by
      rw [this]
      have : L * G ≤ L * N₁ := mul_le_mul_of_nonneg_left hGN hLpos.le
      have : L ≤ 4 * h ^ ν := by linarith
      calc 2 * (L * G) ≤ 2 * (L * N₁) := by linarith
        _ ≤ 2 * ((4 * h ^ ν) * N₁) := by gcongr
        _ = 8 * h ^ ν * N₁ := by ring
    refine hdiff0.trans (h1.trans ?_)
    have : 8 * N₁ ≤ H := by
      have : 0 ≤ 4 * (2 : ℝ) ^ p * K * N₁ := by positivity
      nlinarith only [hH', this, hN₀]
    calc 8 * h ^ ν * N₁ = (8 * N₁) * h ^ ν := by ring
      _ ≤ H * h ^ ν := mul_le_mul_of_nonneg_right this hhν.le

end AVenhance.Infra.FullTheorem.UniformH1
