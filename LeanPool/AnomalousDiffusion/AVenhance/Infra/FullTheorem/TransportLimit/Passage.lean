/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.TransportLimit.ViscousError
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.TransportLimit.Construction

/-!
# Passing to the limit in the weak form

If weak solutions with diffusivities `κ j → 0` converge uniformly in `L²(cell)` to `Θ`, then `Θ`
satisfies the divergence-form transport identity, has weakly continuous pairings, and bounded
energy.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

noncomputable section

namespace AVenhance.Infra.FullTheorem.TransportLimit

open AVenhance.Infra.Parabolic.WeakUniqueness

theorem l2_pairing_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ p, f p * g p ∂μ| ≤ Real.sqrt (∫ p, f p ^ 2 ∂μ) * Real.sqrt (∫ p, g p ^ 2 ∂μ) := by
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (f := fun p => |f p|) (g := fun p => |g p|)
    (μ := μ) Real.HolderConjugate.two_two
    (ae_of_all _ fun p => abs_nonneg _) (ae_of_all _ fun p => abs_nonneg _)
    (by simpa [Real.norm_eq_abs] using hf.norm)
    (by simpa [Real.norm_eq_abs] using hg.norm)
  have hAbs : |∫ p, f p * g p ∂μ| ≤ ∫ p, |f p| * |g p| ∂μ := by
    simpa [Real.norm_eq_abs, abs_mul] using
      (norm_integral_le_integral_norm (fun p => f p * g p) (μ := μ))
  exact hAbs.trans (by
    simpa only [Real.rpow_two, sq_abs, Real.sqrt_eq_rpow, one_div] using hHolder)

theorem l2NormSq_sub_le {f g : Vec 2 → ℝ} (hf : MemL2On unitCube f) (hg : MemL2On unitCube g) :
    l2NormSq (fun x => f x - g x) ≤ 2 * l2NormSq f + 2 * l2NormSq g := by
  have hsub : MemL2On unitCube (fun x => f x - g x) := hf.sub hg
  have hleft : Integrable (fun x => (f x - g x) ^ 2) (volume.restrict unitCube) :=
    (memLp_two_iff_integrable_sq hsub.aestronglyMeasurable).1 hsub
  have hfi : Integrable (fun x => f x ^ 2) (volume.restrict unitCube) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hgi : Integrable (fun x => g x ^ 2) (volume.restrict unitCube) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).1 hg
  have hright : Integrable (fun x => 2 * f x ^ 2 + 2 * g x ^ 2) (volume.restrict unitCube) :=
    (hfi.const_mul 2).add (hgi.const_mul 2)
  have hmono := integral_mono_ae hleft hright (Filter.Eventually.of_forall fun x => by
    nlinarith [sq_nonneg (f x + g x)])
  change (∫ x in unitCube, (f x - g x) ^ 2) ≤ _
  have hsum : (∫ x in unitCube, 2 * f x ^ 2 + 2 * g x ^ 2) = 2 * l2NormSq f + 2 * l2NormSq g := by
    rw [integral_add (hfi.const_mul 2) (hgi.const_mul 2)]
    simp [l2NormSq, integral_const_mul]
  exact hmono.trans_eq hsum

/-- Bounded energy of the limit. -/
theorem limit_l2_bound {θ : ℕ → ℝ → Vec 2 → ℝ} {Θ : ℝ → Vec 2 → ℝ}
    (hmem : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (θ j t))
    (hbd : ∀ j, ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (θ j t) ≤ C)
    (hΘ : ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (Θ t))
    (hunif : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θ j t x - Θ t x)) ≤ η) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (Θ t) ≤ C := by
  obtain ⟨N, hN⟩ := hunif 1 one_pos
  obtain ⟨C, hC⟩ := hbd N
  refine ⟨2 * C + 2 * 1, fun t ht => ?_⟩
  have h1 : l2NormSq (fun x => θ N t x - Θ t x) ≤ 1 := by
    have := hN N le_rfl t ht
    rw [Real.sqrt_le_left zero_le_one] at this
    simpa using this
  have h2 : l2NormSq (fun x => θ N t x - (θ N t x - Θ t x)) ≤
      2 * l2NormSq (θ N t) + 2 * l2NormSq (fun x => θ N t x - Θ t x) :=
    l2NormSq_sub_le (hmem N t ht) ((hmem N t ht).sub (hΘ t ht))
  have h3 : (fun x => θ N t x - (θ N t x - Θ t x)) = Θ t := by
    funext x; ring
  rw [h3] at h2
  linarith [hC t ht]

/-- Weak continuity of the limit's pairings with smooth periodic functions. -/
theorem limit_weak_continuity {θ : ℕ → ℝ → Vec 2 → ℝ} {Θ : ℝ → Vec 2 → ℝ}
    (hmem : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (θ j t))
    (hΘ : ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (Θ t))
    (hcont : ∀ j, ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
      ContinuousOn (fun t => ∫ x in unitCube, θ j t x * ψ x) (Set.Icc (0 : ℝ) 1))
    (hunif : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θ j t x - Θ t x)) ≤ η)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : IsZ2Periodic ψ) :
    ContinuousOn (fun t => ∫ x in unitCube, Θ t x * ψ x) (Set.Icc (0 : ℝ) 1) := by
  have hψ2 : MemL2On unitCube ψ := weak_continuous_memL2On hψ.continuous
  set c := Real.sqrt (∫ x in unitCube, ψ x ^ 2) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hT : TendstoUniformlyOn (fun (j : ℕ) t => ∫ x in unitCube, θ j t x * ψ x)
      (fun t => ∫ x in unitCube, Θ t x * ψ x) atTop (Set.Icc (0 : ℝ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hunif (ε / (2 * (c + 1))) (by positivity)
    filter_upwards [eventually_ge_atTop N] with j hj t ht
    have hdiff : (∫ x in unitCube, Θ t x * ψ x) - ∫ x in unitCube, θ j t x * ψ x =
        -∫ x in unitCube, (θ j t x - Θ t x) * ψ x := by
      rw [← integral_neg, ← integral_sub (weak_product_integrable_cell (hΘ t ht) hψ2)
        (weak_product_integrable_cell (hmem j t ht) hψ2)]
      congr 1; funext x; ring
    rw [Real.dist_eq, hdiff, abs_neg]
    have hb := l2_pairing_bound (μ := volume.restrict unitCube)
      ((hmem j t ht).sub (hΘ t ht)) hψ2
    have hs := hN j hj t ht
    calc |∫ x in unitCube, (θ j t x - Θ t x) * ψ x|
        ≤ Real.sqrt (l2NormSq (fun x => θ j t x - Θ t x)) * c := hb
      _ ≤ ε / (2 * (c + 1)) * c := mul_le_mul_of_nonneg_right hs hc0
      _ ≤ ε / (2 * (c + 1)) * (c + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  exact hT.continuousOn (Eventually.of_forall fun j => hcont j ψ hψ hψp).frequently

end AVenhance.Infra.FullTheorem.TransportLimit
