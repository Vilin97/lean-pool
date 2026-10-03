/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AmnrPairDivergenceStep
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Hmr

/-! Finite `A`/`q` aggregation for the `H_{m,r}` material step. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance
open Homogenization
open Filter
open scoped Topology

/-- Iteration index together with the two tensor indices of an Amnr pair. -/
abbrev AmnrPairIndex := (ℕ × Fin 2) × Fin 2

/-- All tensor-index pairs with iteration index below the specified cutoff. -/
def amnrPairSet (N : ℕ) : Finset AmnrPairIndex :=
  (Finset.range N ×ˢ (Finset.univ : Finset (Fin 2))) ×ˢ Finset.univ

/-- Flux of one Amnr tensor pair against the next time primitive. -/
def amnrPairFlux {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    (a : AmnrPairIndex) (z : ST) : Vec 2 :=
  fun i => I.Amnr hΦ m κ a.1.1 T r z.1 z.2 i a.1.2 a.2 *
    (I.qMNR κ m a.1.1 (r + 1) z.1) a.1.2 a.2

/-- Difference of consecutive Amnr tensor-pair contributions in the material recurrence. -/
def amnrPairIncrement {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    (a : AmnrPairIndex) (z : ST) : Vec 2 :=
  fun i => I.Amnr hΦ m κ a.1.1 T (r + 1) z.1 z.2 i a.1.2 a.2 *
      (I.qMNR κ m a.1.1 (r + 1) z.1) a.1.2 a.2 -
    I.Amnr hΦ m κ a.1.1 T r z.1 z.2 i a.1.2 a.2 *
      (I.qMNR κ m a.1.1 r z.1) a.1.2 a.2

/-- Endpoint flux of one Amnr tensor pair against its current time primitive. -/
def amnrPairEndpointFlux {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ)
    (a : AmnrPairIndex) (z : ST) : Vec 2 :=
  fun i => I.Amnr hΦ m κ a.1.1 T r z.1 z.2 i a.1.2 a.2 *
    (I.qMNR κ m a.1.1 r z.1) a.1.2 a.2

/-- Sum of the Amnr pair fluxes below a finite iteration cutoff. -/
def amnrPairFluxSum {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m N : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ) (z : ST) : Vec 2 :=
  ∑ a ∈ amnrPairSet N, amnrPairFlux I hΦ m κ T r a z

/-- Sum of the Amnr pair increments below a finite iteration cutoff. -/
def amnrPairIncrementSum {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m N : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ) (z : ST) : Vec 2 :=
  ∑ a ∈ amnrPairSet N, amnrPairIncrement I hΦ m κ T r a z

/-- Sum of the Amnr endpoint pair fluxes below a finite iteration cutoff. -/
def amnrPairEndpointFluxSum {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m N : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ) (z : ST) : Vec 2 :=
  ∑ a ∈ amnrPairSet N, amnrPairEndpointFlux I hΦ m κ T r a z

/-- The row-corrected material derivative is linear over finite sums. -/
theorem stLieDerivative_finset_sum
    {ι : Type*} (S : Finset ι) (F : ι → ST → Vec 2)
    (b : ST → Vec 2) (p : ST)
    (hF : ∀ a ∈ S, DifferentiableAt ℝ (F a) p) :
    stLieDerivative (fun z => ∑ a ∈ S, F a z) b p =
      ∑ a ∈ S, stLieDerivative (F a) b p := by
  have hsum : HasFDerivAt (fun z => ∑ a ∈ S, F a z)
      (∑ a ∈ S, fderiv ℝ (F a) p) p := by
    convert (HasFDerivAt.sum fun a ha => (hF a ha).hasFDerivAt) using 1
    ext z
    simp [Finset.sum_apply]
  ext i
  simp [stLieDerivative, stMaterial, stCorrection, hsum.fderiv,
    Finset.sum_apply, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

/-- and `∂ₜ q_{r+1}=-q_r` aggregate to the material increment of the
finite `A_{m,n,r} q_{m,n,r+1}` sum. The hypotheses expose only the
smoothness needed to differentiate that finite flux and its factors. -/
theorem frozen_amnr_fluxSum_material_increment
    {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m N : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (r : ℕ) (p : ST)
    (hp : 0 < p.1)
    (hb : ContDiff ℝ 2
      (fun z : ST => streamVel (Φ (m - 1)) z.1 z.2))
    (hdiv : ∀ z : ST,
      stDiv (fun w => streamVel (Φ (m - 1)) w.1 w.2) z = 0)
    (hA : ∀ (n : ℕ) (i j k : Fin 2) (z : ST), 0 < z.1 →
      DifferentiableAt ℝ
        (fun w : ST => I.Amnr hΦ m κ n T r w.1 w.2 i j k) z)
    (hPair : ∀ (a : AmnrPairIndex) (z : ST), 0 < z.1 →
      DifferentiableAt ℝ (amnrPairFlux I hΦ m κ T r a) z)
    (hFlux : ContDiffAt ℝ 2 (amnrPairFluxSum I hΦ m N κ T r) p) :
    fderiv ℝ (stDiv (amnrPairFluxSum I hΦ m N κ T r)) p
        (1, streamVel (Φ (m - 1)) p.1 p.2) =
      stDiv (amnrPairIncrementSum I hΦ m N κ T r) p := by
  let F := amnrPairFluxSum I hΦ m N κ T r
  let U := amnrPairIncrementSum I hΦ m N κ T r
  let b : ST → Vec 2 := fun z => streamVel (Φ (m - 1)) z.1 z.2
  have hLie : stLieDerivative F b =ᶠ[𝓝 p] U := by
    have hpos : Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) ∈ 𝓝 p :=
      prod_mem_nhds (Ioi_mem_nhds hp) Filter.univ_mem
    filter_upwards [hpos] with z hz
    have hLieAt : stLieDerivative F b z = U z := by
      rw [show F = fun w => ∑ a ∈ amnrPairSet N,
        amnrPairFlux I hΦ m κ T r a w from rfl]
      rw [show U = fun w => ∑ a ∈ amnrPairSet N,
        amnrPairIncrement I hΦ m κ T r a w from rfl]
      rw [stLieDerivative_finset_sum (amnrPairSet N)
        (amnrPairFlux I hΦ m κ T r) b z
        (fun a ha => hPair a z hz.1)]
      apply Finset.sum_congr rfl
      intro a ha
      rcases a with ⟨⟨n, j⟩, k⟩
      have hpair := frozen_amnrPair_correctedMaterial I hΦ m κ n r T
        z.1 z.2 j k
        (fun i => hA n i j k z hz.1)
        (by
          have hbdiff := hb.differentiable (by norm_num) z
          simpa [b, Function.uncurry] using hbdiff)
      change stLieDerivative
          (fun w i => I.Amnr hΦ m κ n T r w.1 w.2 i j k *
            I.qMNR κ m n (r + 1) w.1 j k)
          (fun w => streamVel (Φ (m - 1)) w.1 w.2) z =
        (fun i => I.Amnr hΦ m κ n T (r + 1) z.1 z.2 i j k *
            I.qMNR κ m n (r + 1) z.1 j k -
          I.Amnr hΦ m κ n T r z.1 z.2 i j k * I.qMNR κ m n r z.1 j k)
        at hpair
      exact hpair
    exact hLieAt
  have hcomm := stDiv_material_eq_stDiv_lieDerivative hFlux hb.contDiffAt hdiv
  have hcomm' : fderiv ℝ (stDiv F) p (1, b p) = stDiv (stLieDerivative F b) p := by
    simpa [F, b] using hcomm
  have hLieDiff : DifferentiableAt ℝ (stLieDerivative F b) p := by
    apply stLieDerivative_differentiableAt
    · simpa [F] using hFlux
    · exact hb.contDiffAt
  calc
    _ = stDiv (stLieDerivative F b) p := hcomm'
    _ = stDiv U p := stDiv_congr_of_eventuallyEq hLieDiff hLie

end AVenhance.Infra.Section5

end
