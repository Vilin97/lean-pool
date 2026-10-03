/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HmMaterialIncrement
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenHmTelescope

/-! Source indexing bridges between the finite `A`/`q` sums and
`H_{m,r}` and endpoint definitions. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance
open Homogenization
open Filter
open scoped Topology

theorem FrozenHmSourceIdentity.vecDot_spaceGrad_eq_fderiv
    {f : Vec 2 → ℝ} {x : Vec 2} (v : Vec 2) :
    vecDot v (spaceGrad f x) = fderiv ℝ f x v := by
  have hv : v = ∑ i : Fin 2, (v i) • basisVec i := by
    funext i
    fin_cases i <;> simp [basisVec, Fin.sum_univ_two]
  rw [hv]
  unfold vecDot spaceGrad
  simp only [Fin.sum_univ_two, Finset.sum_apply]
  simp [smul_eq_mul]

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)

theorem amnrPairFluxSum_eq_nested (m N : ℕ) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (r : ℕ) (z : ST) :
    amnrPairFluxSum I hΦ m N κ T r z = fun i =>
      ∑ n ∈ Finset.range N, ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κ n T r z.1 z.2 i j k *
          (I.qMNR κ m n (r + 1) z.1) j k := by
  ext i
  simp only [amnrPairFluxSum, amnrPairSet, Finset.sum_apply, amnrPairFlux]
  rw [Finset.sum_product, Finset.sum_product]

theorem amnrPairEndpointFluxSum_eq_nested (m N : ℕ) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (r : ℕ) (z : ST) :
    amnrPairEndpointFluxSum I hΦ m N κ T r z = fun i =>
      ∑ n ∈ Finset.range N, ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κ n T r z.1 z.2 i j k *
          (I.qMNR κ m n r z.1) j k := by
  ext i
  simp only [amnrPairEndpointFluxSum, amnrPairSet,
    Finset.sum_apply, amnrPairEndpointFlux]
  rw [Finset.sum_product, Finset.sum_product]

/-- `Hmr` is the spacetime divergence of its finite `A_r q_{r+1}` flux.
This is the exact source-indexing bridge, with only differentiability needed
to identify slice derivatives with spacetime derivatives. -/
theorem frozen_Hmr_eq_stDiv_pairFluxSum
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    (t : ℝ) (x : Vec 2)
    (hF : DifferentiableAt ℝ
      (amnrPairFluxSum I hΦ m (Nstar β) κ T r) (t, x)) :
    I.Hmr hΦ m κ T r t x =
      stDiv (amnrPairFluxSum I hΦ m (Nstar β) κ T r) (t, x) := by
  let F := amnrPairFluxSum I hΦ m (Nstar β) κ T r
  let B : ℝ → Vec 2 → Vec 2 := fun s y => F (s, y)
  have hB : DifferentiableAt ℝ (Function.uncurry B) (t, x) := by
    simpa [B, Function.uncurry, F] using hF
  have hspatial (v : Vec 2) := fderiv_uncurry_vector_spatial
    (B := B) (t := t) (x := x) (v := v) hB
  have hfield :
      (fun y i => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κ n T r t y i j k * I.qMNR κ m n (r + 1) t j k) =
      fun y => F (t, y) := by
    funext y i
    exact congrFun (amnrPairFluxSum_eq_nested I hΦ m (Nstar β) κ T r (t, y)) i |>.symm
  change vecDiv _ x = _
  rw [hfield]
  unfold vecDiv stDiv
  apply Finset.sum_congr rfl
  intro i hi
  change spaceGrad (fun y => (F (t, y)) i) x i =
    (fderiv ℝ (Function.uncurry B) (t, x) (0, basisVec i)) i
  have hslice : DifferentiableAt ℝ (B t) x := by
    have h := hB.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
    simpa [B, Function.uncurry, Function.comp_def] using h.differentiableAt
  change fderiv ℝ (fun y => (B t y) i) x (basisVec i) = _
  rw [fderiv_apply hslice i]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  exact congrArg (fun v : Vec 2 => v i) (hspatial (basisVec i)).symm

/-- The finite endpoint divergence is the corresponding spacetime divergence
of the `A_r q_r` flux. -/
theorem frozen_hmEndpoint_eq_stDiv_pairEndpointFluxSum
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    (t : ℝ) (x : Vec 2)
    (hF : DifferentiableAt ℝ
      (amnrPairEndpointFluxSum I hΦ m (Nstar β) κ T r) (t, x)) :
    hmEndpoint I hΦ m κ T r t x =
      stDiv (amnrPairEndpointFluxSum I hΦ m (Nstar β) κ T r) (t, x) := by
  let F := amnrPairEndpointFluxSum I hΦ m (Nstar β) κ T r
  let B : ℝ → Vec 2 → Vec 2 := fun s y => F (s, y)
  have hB : DifferentiableAt ℝ (Function.uncurry B) (t, x) := by
    simpa [B, Function.uncurry, F] using hF
  have hfield :
      (fun y i => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κ n T r t y i j k * I.qMNR κ m n r t j k) =
      fun y => F (t, y) := by
    funext y i
    exact congrFun (amnrPairEndpointFluxSum_eq_nested I hΦ m (Nstar β)
      κ T r (t, y)) i |>.symm
  change vecDiv _ x = _
  rw [hfield]
  have hspatial (v : Vec 2) := fderiv_uncurry_vector_spatial
    (B := B) (t := t) (x := x) (v := v) hB
  unfold vecDiv stDiv
  apply Finset.sum_congr rfl
  intro i hi
  change spaceGrad (fun y => (F (t, y)) i) x i =
    (fderiv ℝ (Function.uncurry B) (t, x) (0, basisVec i)) i
  have hslice : DifferentiableAt ℝ (B t) x := by
    have h := hB.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
    simpa [B, Function.uncurry, Function.comp_def] using h.differentiableAt
  change fderiv ℝ (fun y => (B t y) i) x (basisVec i) = _
  rw [fderiv_apply hslice i]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  exact congrArg (fun v : Vec 2 => v i) (hspatial (basisVec i)).symm

/-- The finite step is exactly the `Hmr` material equation. The
assumptions are regularity of the finite source fluxes and endpoint fluxes;
the proof uses the per-index recurrence and divergence-free transport proved
above. -/
theorem frozen_Hmr_material_step
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    (t : ℝ) (x : Vec 2) (ht : 0 < t)
    (hb : ContDiff ℝ 2
      (fun z : ST => streamVel (Φ (m - 1)) z.1 z.2))
    (hdiv : ∀ z : ST,
      stDiv (fun w => streamVel (Φ (m - 1)) w.1 w.2) z = 0)
    (hA : ∀ (n : ℕ) (i j k : Fin 2) (z : ST), 0 < z.1 →
      DifferentiableAt ℝ
        (fun w : ST => I.Amnr hΦ m κ n T r w.1 w.2 i j k) z)
    (hPair : ∀ (a : AmnrPairIndex) (z : ST), 0 < z.1 →
      DifferentiableAt ℝ (amnrPairFlux I hΦ m κ T r a) z)
    (hFlux : ContDiffAt ℝ 2
      (amnrPairFluxSum I hΦ m (Nstar β) κ T r) (t, x))
    (hEndNext : DifferentiableAt ℝ
      (amnrPairEndpointFluxSum I hΦ m (Nstar β) κ T (r + 1)) (t, x))
    (hEnd : DifferentiableAt ℝ
      (amnrPairEndpointFluxSum I hΦ m (Nstar β) κ T r) (t, x)) :
    deriv (fun s => I.Hmr hΦ m κ T r s x) t +
        fderiv ℝ (I.Hmr hΦ m κ T r t) x
          (streamVel (Φ (m - 1)) t x) =
      hmEndpoint I hΦ m κ T (r + 1) t x - hmEndpoint I hΦ m κ T r t x := by
  let F := amnrPairFluxSum I hΦ m (Nstar β) κ T r
  let U := amnrPairIncrementSum I hΦ m (Nstar β) κ T r
  let H : ℝ → Vec 2 → ℝ := fun s y => I.Hmr hΦ m κ T r s y
  let b : ℝ → Vec 2 → Vec 2 := fun s y => streamVel (Φ (m - 1)) s y
  let E₁ := amnrPairEndpointFluxSum I hΦ m (Nstar β) κ T (r + 1)
  let E₀ := amnrPairEndpointFluxSum I hΦ m (Nstar β) κ T r
  have hHfun : Function.uncurry H =ᶠ[𝓝 (t, x)] fun z => stDiv F z := by
    filter_upwards [hFlux.eventually (by norm_num)] with z hz
    exact frozen_Hmr_eq_stDiv_pairFluxSum I hΦ m κ T r z.1 z.2
      (hz.differentiableAt (by norm_num))
  have hS := stDiv_hasFDerivAt hFlux
  have hS' : HasFDerivAt (stDiv F) (fderiv ℝ (stDiv F) (t, x)) (t, x) := by
    simpa only [← hS.fderiv] using hS
  have hHderiv : HasFDerivAt (Function.uncurry H)
      (fderiv ℝ (stDiv F) (t, x)) (t, x) := by
    exact hS'.congr_of_eventuallyEq hHfun
  have hmat := materialDerivative_eq_advective_of_hasFDerivAt
    (T := H) (b := b) hHderiv
  have hmat' : fderiv ℝ (stDiv F) (t, x)
        (1, streamVel (Φ (m - 1)) t x) =
      deriv (fun s => I.Hmr hΦ m κ T r s x) t +
        vecDot (streamVel (Φ (m - 1)) t x)
          (spaceGrad (I.Hmr hΦ m κ T r t) x) := by
    calc
      fderiv ℝ (stDiv F) (t, x)
          (1, streamVel (Φ (m - 1)) t x) =
        materialDerivative H b t x := by
          rw [materialDerivative, hHderiv.fderiv]
      _ = _ := by simpa [H, b] using hmat
  have hinc := frozen_amnr_fluxSum_material_increment I hΦ m (Nstar β)
    κ T r (t, x) ht hb hdiv hA hPair hFlux
  have hdot := FrozenHmSourceIdentity.vecDot_spaceGrad_eq_fderiv (f := I.Hmr hΦ m κ T r t) (x := x)
    (streamVel (Φ (m - 1)) t x)
  have hfirst : deriv (fun s => I.Hmr hΦ m κ T r s x) t +
        fderiv ℝ (I.Hmr hΦ m κ T r t) x
          (streamVel (Φ (m - 1)) t x) = stDiv U (t, x) := by
    rw [← hdot]
    linarith [hmat', hinc]
  have hU : U = fun z => E₁ z - E₀ z := by
    funext z i
    simp [U, E₁, E₀, amnrPairIncrementSum, amnrPairEndpointFluxSum,
      amnrPairIncrement, amnrPairEndpointFlux, Finset.sum_sub_distrib]
  have hstDivSub : stDiv (fun z => E₁ z - E₀ z) (t, x) =
      stDiv E₁ (t, x) - stDiv E₀ (t, x) := by
    have hfun : (fun z => E₁ z - E₀ z) = E₁ - E₀ := by
      funext z
      rfl
    unfold stDiv
    rw [hfun, fderiv_sub hEndNext hEnd]
    simp only [sub_apply]
    simp only [Fin.sum_univ_two]
    dsimp [E₁, E₀]
    ring_nf
  have hEndpointNext := frozen_hmEndpoint_eq_stDiv_pairEndpointFluxSum
    I hΦ m κ T (r + 1) t x hEndNext
  have hEndpoint := frozen_hmEndpoint_eq_stDiv_pairEndpointFluxSum
    I hΦ m κ T r t x hEnd
  rw [hU] at hfirst
  rw [hstDivSub] at hfirst
  rw [← hEndpointNext, ← hEndpoint] at hfirst
  exact hfirst

end AVenhance.Infra.Section5

end
