/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.CutoffMemory
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.MatrixBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! # `C^∞` regularity of the memory coefficients `L_{m,n}` and of `𝐊_m`

The memory coefficient
`L^κ_{m,n}(t) = ∑_l ζ̂_{m,l}(t) ∫_{-∞}^t ζ̂_{m,l}(s) (ρ(s-t))ⁿ e^{ρ(s-t)} ds`
is a locally finite sum.  Each term is `f(t) · (K ⋆ f)(t)` with `f = ζ̂_{m,l}` smooth with compact
support and `K` the locally integrable memory kernel, hence smooth by the convolution theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization
open scoped Matrix.Norms.Elementwise ContDiff Convolution

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance

/-! ### Locally finite sums of smooth functions -/

/-- A locally finite sum of `C^n` functions is `C^n`. -/
theorem contDiff_tsum_of_locallyFinite {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω} {g : ι → E → F}
    (hg : ∀ i, ContDiff ℝ n (g i))
    (hloc : ∀ x, ∃ s : Finset ι, ∀ᶠ y in 𝓝 x, ∀ i, i ∉ s → g i y = 0) :
    ContDiff ℝ n (fun y => ∑' i, g i y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨s, hs⟩ := hloc x
  have heq : (fun y => ∑' i, g i y) =ᶠ[𝓝 x] fun y => ∑ i ∈ s, g i y := by
    filter_upwards [hs] with y hy
    exact tsum_eq_sum (fun i hi => hy i hi)
  exact (ContDiff.sum (fun i _ => hg i)).contDiffAt.congr_of_eventuallyEq heq

/-- Around every time `t`, only finitely many lattice points `l T` lie within `R + 1` of `t`;
any `l` outside this finite set is at distance more than `R` from every `s` with `|s - t| < 1`. -/
theorem exists_finset_far {T : ℝ} (hT : 0 < T) (R t : ℝ) :
    ∃ S : Finset ℤ, ∀ s : ℝ, |s - t| < 1 → ∀ l : ℤ, l ∉ S → R < |s - (l : ℝ) * T| := by
  refine ⟨(finite_lattice_near hT t (R + 1)).toFinset, fun s hs l hl => ?_⟩
  by_contra hle
  replace hle := not_lt.mp hle
  apply hl
  rw [Set.Finite.mem_toFinset]
  change |t - (l : ℝ) * T| ≤ R + 1
  have h1 : |t - (l : ℝ) * T| ≤ |t - s| + |s - (l : ℝ) * T| := by
    calc |t - (l : ℝ) * T| = |(t - s) + (s - (l : ℝ) * T)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  rw [abs_sub_comm] at hs
  linarith

/-! ### Support of the cutoff families -/

section Support

variable {β : ℝ} (I : Ingredients β)

/-- `ζ̂_{m,l}(t) ≠ 0` forces `|t - l τ''_m| ≤ τ''_m / 2`. -/
theorem hatZetaML_abs_le_of_ne_zero {m : ℕ} (hm : 1 ≤ m) {l : ℤ} {t : ℝ}
    (hne : I.hatZetaML m l t ≠ 0) : |t - (l : ℝ) * tauPP β I.Λ m| ≤ 1 / 2 * tauPP β I.Λ m := by
  have hle := I.hatZeta_le m hm l t
  have hge : 0 ≤ shiftCutoff (I.hatZeta m) (l * tauPP β I.Λ m) t :=
    (indIcc_nonneg' _ _ _).trans (I.hatZeta_ge m hm l t)
  have hmem : t ∈ Set.Icc ((l - 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m) := by
    by_contra hnot
    apply hne
    rw [indIcc_eq_zero_of_not_mem hnot] at hle
    exact le_antisymm hle hge
  have hp : 0 < tauP β I.Λ m := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le)
  rw [abs_le]
  constructor <;> nlinarith [hmem.1, hmem.2]

/-- `ξ̂_{m,l}(t) ≠ 0` forces `|t - l τ''_m| ≤ τ''_m / 2 + τ'_m`. -/
theorem hatXiML_abs_le_of_ne_zero {m : ℕ} (hm : 1 ≤ m) {l : ℤ} {t : ℝ}
    (hne : I.hatXiML m l t ≠ 0) :
    |t - (l : ℝ) * tauPP β I.Λ m| ≤ 1 / 2 * tauPP β I.Λ m + tauP β I.Λ m := by
  have hle := I.hatXi_le m hm l t
  have hge : 0 ≤ shiftCutoff (I.hatXi m) (l * tauPP β I.Λ m) t :=
    (indIcc_nonneg' _ _ _).trans (I.hatXi_ge m hm l t)
  have hmem : t ∈ Set.Icc ((l - 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m) := by
    by_contra hnot
    apply hne
    rw [indIcc_eq_zero_of_not_mem hnot] at hle
    exact le_antisymm hle hge
  rw [abs_le]
  constructor <;> nlinarith [hmem.1, hmem.2]

/-- Each `ζ̂_{m,l}` is smooth. -/
theorem hatZetaML_contDiff (m : ℕ) (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (I.hatZetaML m l) := by
  unfold Ingredients.hatZetaML shiftCutoff
  exact (I.hatZeta_smooth m).comp (by fun_prop)

/-- Each `ξ̂_{m,l}` is smooth. -/
theorem hatXiML_contDiff (m : ℕ) (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (I.hatXiML m l) := by
  unfold Ingredients.hatXiML shiftCutoff
  exact (I.hatXi_smooth m).comp (by fun_prop)

/-- Each `ζ̂_{m,l}` has compact support. -/
theorem hatZetaML_hasCompactSupport {m : ℕ} (hm : 1 ≤ m) (l : ℤ) :
    HasCompactSupport (I.hatZetaML m l) := by
  have hT := I.tauPP_pos' m
  refine HasCompactSupport.intro (isCompact_Icc (a := (l : ℝ) * tauPP β I.Λ m -
    1 / 2 * tauPP β I.Λ m) (b := (l : ℝ) * tauPP β I.Λ m + 1 / 2 * tauPP β I.Λ m)) ?_
  intro t ht
  by_contra hne
  have := abs_le.mp (hatZetaML_abs_le_of_ne_zero I hm hne)
  exact ht ⟨by linarith [this.1], by linarith [this.2]⟩

/-- The family `ξ̂_{m,l}`, `ζ̂_{m,l}` is locally finite in `l`, uniformly on unit time windows. -/
theorem exists_finset_hatXi_vanish {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    ∃ S : Finset ℤ, ∀ s : ℝ, |s - t| < 1 → ∀ l : ℤ, l ∉ S → I.hatXiML m l s = 0 := by
  obtain ⟨S, hS⟩ := exists_finset_far (I.tauPP_pos' m)
    (1 / 2 * tauPP β I.Λ m + tauP β I.Λ m) t
  refine ⟨S, fun s hs l hl => ?_⟩
  by_contra hne
  exact absurd (hatXiML_abs_le_of_ne_zero I hm hne) (not_le.mpr (hS s hs l hl))

theorem exists_finset_hatZeta_vanish {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    ∃ S : Finset ℤ, ∀ s : ℝ, |s - t| < 1 → ∀ l : ℤ, l ∉ S → I.hatZetaML m l s = 0 := by
  obtain ⟨S, hS⟩ := exists_finset_far (I.tauPP_pos' m) (1 / 2 * tauPP β I.Λ m) t
  refine ⟨S, fun s hs l hl => ?_⟩
  by_contra hne
  exact absurd (hatZetaML_abs_le_of_ne_zero I hm hne) (not_le.mpr (hS s hs l hl))

end Support

/-! ### The memory kernel as a convolution -/

/-- The memory kernel `y ↦ 1_{y ≥ 0} (-ρ y)ⁿ e^{-ρ y}`. -/
def memKernel (ρ : ℝ) (n : ℕ) : ℝ → ℝ :=
  (Set.Ici (0 : ℝ)).indicator (fun y => (-(ρ * y)) ^ n * Real.exp (-(ρ * y)))

theorem memKernel_locallyIntegrable (ρ : ℝ) (n : ℕ) :
    LocallyIntegrable (memKernel ρ n) volume := by
  have hc : Continuous (fun y : ℝ => (-(ρ * y)) ^ n * Real.exp (-(ρ * y))) := by fun_prop
  exact hc.locallyIntegrable.indicator measurableSet_Ici

/-- The memory integral is a convolution with the memory kernel. -/
theorem memory_integral_eq_convolution (f : ℝ → ℝ) (ρ : ℝ) (n : ℕ) (t : ℝ) :
    (∫ s in Set.Iic t, f s * (ρ * (s - t)) ^ n * Real.exp (ρ * (s - t))) =
      (memKernel ρ n ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f) t := by
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  have h := integral_sub_left_eq_self (fun y => memKernel ρ n y * f (t - y)) volume t
  simp only [sub_sub_cancel] at h
  rw [← h, ← integral_indicator measurableSet_Iic]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : s ≤ t
  · have hmem : t - s ∈ Set.Ici (0 : ℝ) := sub_nonneg.mpr hs
    simp only [memKernel, Set.indicator_of_mem hmem, Set.indicator_of_mem (Set.mem_Iic.mpr hs)]
    rw [show -(ρ * (t - s)) = ρ * (s - t) by ring]
    ring
  · have hmem : t - s ∉ Set.Ici (0 : ℝ) := by
      simp only [Set.mem_Ici, not_le]
      linarith [not_le.mp hs]
    simp only [memKernel, Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (show s ∉ Set.Iic t from hs), zero_mul]

/-- The `f(t) ∫_{-∞}^t f(s) (ρ(s-t))ⁿ e^{ρ(s-t)} ds` of a smooth compactly supported `f` is
    smooth. -/
theorem memory_term_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) (ρ : ℝ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => f t *
      ∫ s in Set.Iic t, f s * (ρ * (s - t)) ^ n * Real.exp (ρ * (s - t))) := by
  have hconv : ContDiff ℝ (⊤ : ℕ∞)
      (memKernel ρ n ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f) :=
    hcs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      (memKernel_locallyIntegrable ρ n) hf
  have heq : (fun t => f t *
      ∫ s in Set.Iic t, f s * (ρ * (s - t)) ^ n * Real.exp (ρ * (s - t))) =
      fun t => f t * (memKernel ρ n ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f) t := by
    funext t
    rw [memory_integral_eq_convolution]
  rw [heq]
  exact hf.mul hconv

/-! ### Smoothness of `L_{m,n}` and `𝐊_m` -/

/-- The memory coefficient `L^κ_{m,n}` is `C^∞` in time. -/
theorem LMN_contDiff_top {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) {κ : ℝ}
    (_hκ : 0 < κ) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (I.LMN κ m n) := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 := ⟨_, rfl⟩
  have hterm : ∀ (l : ℤ) (t : ℝ), I.hatZetaML m l t *
      (∫ s in Set.Iic t, I.hatZetaML m l s *
        (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ n *
        Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t))) =
      I.hatZetaML m l t * ∫ s in Set.Iic t,
        I.hatZetaML m l s * (ρ * (s - t)) ^ n * Real.exp (ρ * (s - t)) := by
    intro l t
    have e : ∀ s : ℝ, 4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2 = ρ * (s - t) := by
      intro s
      rw [hρ]
      ring
    simp only [e, ← hρ]
  unfold Ingredients.LMN
  apply contDiff_tsum_of_locallyFinite (g := fun (l : ℤ) (t : ℝ) =>
    I.hatZetaML m l t * ∫ s in Set.Iic t,
      I.hatZetaML m l s * (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ n *
        Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t)))
  · intro l
    have h := memory_term_contDiff (hatZetaML_contDiff I m l)
      (hatZetaML_hasCompactSupport I hm l) ρ n
    have hfun : (fun t => I.hatZetaML m l t * ∫ s in Set.Iic t,
      I.hatZetaML m l s * (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ n *
        Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t))) =
        fun t => I.hatZetaML m l t * ∫ s in Set.Iic t,
          I.hatZetaML m l s * (ρ * (s - t)) ^ n * Real.exp (ρ * (s - t)) :=
      funext (hterm l)
    rw [hfun]
    exact h
  · intro t
    obtain ⟨S, hS⟩ := exists_finset_hatZeta_vanish I hm t
    refine ⟨S, ?_⟩
    have hball : ∀ᶠ y in 𝓝 t, |y - t| < 1 := by
      have := Metric.ball_mem_nhds t (zero_lt_one' ℝ)
      filter_upwards [this] with y hy
      simpa [Metric.mem_ball, Real.dist_eq] using hy
    filter_upwards [hball] with y hy l hl
    simp only [hS y hy l hl, zero_mul]

/-- The matrix coefficient `𝐊^κ_m` is `C^∞` in time. -/
theorem Kmat_contDiff_top {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) {κ : ℝ}
    (hκ : 0 < κ) : ContDiff ℝ (⊤ : ℕ∞) (I.Kmat κ m) :=
  contDiff_const.add (ContDiff.sum (fun n _ => (LMN_contDiff_top I hm hκ n).smul contDiff_const))

end AVenhance.Infra.Section5.RelativeError
