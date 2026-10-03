/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Separation.WordEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Separation.Commutator

/-! # Differential inequalities for `E`, `G = ‖∇θ‖²`, `H = ‖∇²θ‖²`

For a classical solution `θ` of the drift `streamVel Ψ` with `|∂_i b_k| ≤ Lu`:

* `E' = -2κ G`;
* `G' = -2κ H - 2 C_G`, `|C_G| ≤ 2 Lu G`;
* `H' = -2κ D - 2 C_H`, `|C_H| ≤ (κ/2) D + 4 (Lu²/κ) G + 2 Lu H`, `D = ‖∇³θ‖²`. -/

@[expose] public section

open Homogenization MeasureTheory Filter
open AVenhance.Infra.Section4
open scoped Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem.Separation

open AVenhance

/-- `‖∇∂^w f‖² = ‖∂_0 ∂^w f‖² + ‖∂_1 ∂^w f‖²`. -/
theorem integral_vecNormSq_eq {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : List (Fin 2)) :
    (∫ x in unitCube, vecNormSq (spaceGrad (classicalWordDerivative w f) x)) =
      en (0 :: w) f + en (1 :: w) f := by
  have c0 : Continuous (fun x => (classicalWordDerivative (0 :: w) f x) ^ 2) :=
    (cont_word (0 :: w) hf).pow 2
  have c1 : Continuous (fun x => (classicalWordDerivative (1 :: w) f x) ^ 2) :=
    (cont_word (1 :: w) hf).pow 2
  unfold en
  rw [← integral_add (intOn c0) (intOn c1)]
  congr 1
  funext x
  simp [vecNormSq, vecDot, Fin.sum_univ_two, pow_two, classicalWordDerivative,
    Classical.classicalWordDerivative]

theorem wDiss_eq {θ : ℝ → Vec 2 → ℝ} {s : ℝ} (hs : ContDiff ℝ (⊤ : ℕ∞) (θ s))
    (w : List (Fin 2)) :
    wDiss w θ s = wEnergy (0 :: w) θ s + wEnergy (1 :: w) θ s :=
  integral_vecNormSq_eq hs w

/-- Smoothness and periodicity of the drift slices. -/
theorem drift_slice {Ψ : ℝ → Vec 2 → ℝ} (hΨ : IsAdmissibleStream Ψ) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (streamVel Ψ s) ∧ IsZ2Periodic (streamVel Ψ s) := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (s, x)) :=
    contDiff_const.prodMk contDiff_id
  have hΨs : ContDiff ℝ (⊤ : ℕ∞) (Ψ s) := by
    simpa [Function.uncurry, Function.comp_def] using hΨ.1.comp hmap
  have hΨp : IsZ2Periodic (Ψ s) := by
    intro k x
    simpa using hΨ.2 0 k s x
  exact ⟨theta_streamVel_contDiff (Ψ s) hΨs, theta_streamVel_periodic (Ψ s) hΨs hΨp⟩

/-- The gradient energy `‖∇θ(s)‖²`. -/
def gradE (θ : ℝ → Vec 2 → ℝ) (s : ℝ) : ℝ := wDiss [] θ s

/-- The Hessian energy `∑_{j,i} ‖∂_j ∂_i θ(s)‖²`. -/
def hessE (θ : ℝ → Vec 2 → ℝ) (s : ℝ) : ℝ := ∑ j : Fin 2, ∑ i : Fin 2, wEnergy [j, i] θ s

/-- The third-derivative dissipation `∑_{j,i} ‖∇∂_j∂_i θ(s)‖²`. -/
def thirdD (θ : ℝ → Vec 2 → ℝ) (s : ℝ) : ℝ := ∑ j : Fin 2, ∑ i : Fin 2, wDiss [j, i] θ s

variable {Ψ θ : ℝ → Vec 2 → ℝ} {κ Lu : ℝ} {θ₀ : Vec 2 → ℝ}

theorem slice_smooth (hsol : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ) {s : ℝ}
    (hs : 0 ≤ s) : ContDiff ℝ (⊤ : ℕ∞) (θ s) ∧ IsZ2Periodic (θ s) :=
  ⟨classicalSmooth_slice_nonneg hsol.1 hs, hsol.2.1 s hs⟩

theorem gradE_eq (hsol : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ) {s : ℝ}
    (hs : 0 ≤ s) : gradE θ s = en [0] (θ s) + en [1] (θ s) :=
  wDiss_eq (slice_smooth hsol hs).1 []

theorem gradE_nonneg (hsol : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ) {s : ℝ}
    (hs : 0 ≤ s) : 0 ≤ gradE θ s := by
  rw [gradE_eq hsol hs]
  unfold en
  exact add_nonneg (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)

theorem hessE_nonneg {s : ℝ} : 0 ≤ hessE θ s := by
  unfold hessE wEnergy
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => ?_
  exact integral_nonneg fun x => sq_nonneg _

theorem thirdD_nonneg (hsol : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ) {s : ℝ}
    (hs : 0 ≤ s) : 0 ≤ thirdD θ s := by
  unfold thirdD
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => ?_
  rw [wDiss_eq (slice_smooth hsol hs).1]
  unfold wEnergy
  exact add_nonneg (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)

theorem hasDerivAt_E (hΨ : IsAdmissibleStream Ψ)
    (hsol : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (wEnergy [] θ) (-2 * κ * gradE θ t) t := by
  have h := wEnergy_hasDerivAt hΨ hsol [] ht
  have hc : wComm [] Ψ θ t = 0 := commPair_nil _ _
  rw [hc] at h
  simpa [gradE] using h

theorem hasDerivAt_G (hΨ : IsAdmissibleStream Ψ)
    (hsol : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ) {t : ℝ} (ht : 0 < t)
    (hLu : ∀ x i k, |spaceGrad (fun y => streamVel Ψ t y k) x i| ≤ Lu) :
    ∃ C : ℝ, HasDerivAt (gradE θ) (-2 * κ * hessE θ t - 2 * C) t ∧
      |C| ≤ 2 * Lu * gradE θ t := by
  have h0 := wEnergy_hasDerivAt hΨ hsol [0] ht
  have h1 := wEnergy_hasDerivAt hΨ hsol [1] ht
  have hev : gradE θ =ᶠ[nhds t] fun s => wEnergy [0] θ s + wEnergy [1] θ s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [gradE_eq hsol (le_of_lt hs)]
    rfl
  have hd := (h0.add h1).congr_of_eventuallyEq hev
  have hts := (slice_smooth hsol ht.le).1
  refine ⟨wComm [0] Ψ θ t + wComm [1] Ψ θ t, hd.congr_deriv ?_, ?_⟩
  · have a0 := wDiss_eq hts [0]
    have a1 := wDiss_eq hts [1]
    simp only [hessE, Fin.sum_univ_two]
    rw [a0, a1]
    ring
  · have hb := drift_slice hΨ t
    have := commPair_one_abs_le (hb := hb.1) (hf := (slice_smooth hsol ht.le).1) hLu
    simp only [Fin.sum_univ_two] at this
    have hg := gradE_eq hsol ht.le
    rw [hg]
    exact this

theorem hasDerivAt_H (hΨ : IsAdmissibleStream Ψ)
    (hsol : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ) {t : ℝ} (ht : 0 < t)
    (hκ : 0 < κ) (hLu : ∀ x i k, |spaceGrad (fun y => streamVel Ψ t y k) x i| ≤ Lu) :
    ∃ C : ℝ, HasDerivAt (hessE θ) (-2 * κ * thirdD θ t - 2 * C) t ∧
      |C| ≤ κ / 2 * thirdD θ t + 4 * (Lu ^ 2 / κ) * gradE θ t + 2 * Lu * hessE θ t := by
  have hd : ∀ j i : Fin 2, HasDerivAt (wEnergy [j, i] θ)
      (-2 * κ * wDiss [j, i] θ t - 2 * wComm [j, i] Ψ θ t) t :=
    fun j i => wEnergy_hasDerivAt hΨ hsol [j, i] ht
  have hsum : HasDerivAt (hessE θ)
      (∑ j : Fin 2, ∑ i : Fin 2, (-2 * κ * wDiss [j, i] θ t - 2 * wComm [j, i] Ψ θ t)) t := by
    unfold hessE
    exact HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun i _ => hd j i
  have hts := (slice_smooth hsol ht.le).1
  have htp := (slice_smooth hsol ht.le).2
  refine ⟨∑ j : Fin 2, ∑ i : Fin 2, wComm [j, i] Ψ θ t, hsum.congr_deriv ?_, ?_⟩
  · unfold thirdD
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  · have hb := drift_slice hΨ t
    have := commPair_two_abs_le hκ hb.1 hb.2 hts htp hLu
    have e3 : thirdD θ t = ∑ l : Fin 2, ∑ j : Fin 2, ∑ i : Fin 2, en [l, j, i] (θ t) := by
      unfold thirdD
      have : ∀ j i : Fin 2, wDiss [j, i] θ t = en [0, j, i] (θ t) + en [1, j, i] (θ t) :=
        fun j i => wDiss_eq hts [j, i]
      simp only [this, Fin.sum_univ_two]
      ring
    have e1 : gradE θ t = ∑ k : Fin 2, en [k] (θ t) := by
      rw [gradE_eq hsol ht.le]
      simp [Fin.sum_univ_two]
    have e2 : hessE θ t = ∑ j : Fin 2, ∑ i : Fin 2, en [j, i] (θ t) := rfl
    rw [e3, e1, e2]
    exact this

end AVenhance.Infra.FullTheorem.Separation
