/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredNd
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.DivergenceTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Cube
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusion

/-! # Splitting a centered term into its nondivergence part and a divergence -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff ENNReal

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

/-- The mean of the divergence of a smooth periodic field over the unit cube vanishes. -/
theorem sd_integral_vecDiv_eq_zero {F : Vec 2 → Vec 2} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : IsZ2Periodic F) : ∫ x in unitCube, vecDiv F x = 0 := by
  unfold vecDiv
  have hc (i : Fin 2) : Continuous (fun x => spaceGrad (fun y => F y i) x i) := by
    have hi : ContDiff ℝ (⊤ : ℕ∞) (fun y => F y i) := contDiff_pi.mp hF i
    exact (contDiff_pi.mp (Infra.Section4.iterate_gradient_smooth hi) i).continuous
  rw [integral_finsetSum _ fun i _ => LeftToShow.integrableOn_unitCube_of_continuous (hc i)]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun y => F y i) := contDiff_pi.mp hF i
  have hip : IsZ2Periodic (fun y => F y i) := fun n x => congrFun (hp n x) i
  have h := LeftToShow.integral_unitCube_mul_spaceGrad
    (f := fun _ : Vec 2 => (1 : ℝ)) (g := fun y => F y i) contDiff_const (hi.of_le (by simp))
    (fun _ _ => rfl) hip i
  simpa [spaceGrad] using h

theorem sd_vecDiv_continuous {F : Vec 2 → Vec 2} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (vecDiv F) := by
  unfold vecDiv
  refine continuous_finsetSum _ fun i _ => ?_
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun y => F y i) := contDiff_pi.mp hF i
  exact (contDiff_pi.mp (Infra.Section4.iterate_gradient_smooth hi) i).continuous

/-- **Centered split**: if `tw = Nd - div F` with `Nd` continuous and `F` smooth periodic, then
`‖center tw‖_{HDot⁻¹} ≤ ‖center Nd‖_{HDot⁻¹} + ‖F‖_{L²}`. -/
theorem sd_centered_split_bound {tw Nd : Vec 2 → ℝ} {F : Vec 2 → Vec 2}
    (hNd : Continuous Nd) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : IsZ2Periodic F)
    (h : ∀ x, tw x = Nd x - vecDiv F x) :
    hMinusOneNorm (Integration.centerCell tw) ≤
      hMinusOneNorm (Integration.centerCell Nd) + ENNReal.ofReal (Real.sqrt (gradNormSq F)) := by
  have hdc := sd_vecDiv_continuous hF
  have hmean := sd_integral_vecDiv_eq_zero hF hp
  have hNdL2 : MemL2On unitCube Nd := Integration.memL2On_unitCube_of_continuous hNd
  have hdL2 : MemL2On unitCube (fun x => -vecDiv F x) :=
    Integration.memL2On_unitCube_of_continuous hdc.neg
  have hint : ∫ x in unitCube, Nd x - vecDiv F x = (∫ x in unitCube, Nd x) - 0 := by
    rw [integral_sub (Integration.integrableOn_unitCube_of_memL2On hNdL2)
      (LeftToShow.integrableOn_unitCube_of_continuous hdc), hmean]
  have hcenter : Integration.centerCell tw = fun x =>
      Integration.centerCell Nd x + -vecDiv F x := by
    funext x
    have : tw = fun x => Nd x - vecDiv F x := funext h
    unfold Integration.centerCell
    rw [this, hint]
    ring
  rw [hcenter]
  refine (hMinusOneNorm_add_le (Integration.memL2On_centerCell hNdL2) hdL2).trans ?_
  refine add_le_add le_rfl ?_
  have := hMinusOneNorm_neg_vecDiv_le hF hp
  exact this

/-- **Centered divergence bound** (slots `twistie4`, `twistie5`): a pure divergence
`tw = -div F` of a smooth periodic flux has mean zero, so
`‖center tw‖_{HDot⁻¹} ≤ ‖F‖_{L²}`. -/
theorem sd_centered_div_bound {tw : Vec 2 → ℝ} {F : Vec 2 → Vec 2}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : IsZ2Periodic F) (h : ∀ x, tw x = -vecDiv F x) :
    hMinusOneNorm (Integration.centerCell tw) ≤ ENNReal.ofReal (Real.sqrt (gradNormSq F)) := by
  have hmean := sd_integral_vecDiv_eq_zero hF hp
  have htw : tw = fun x => -vecDiv F x := funext h
  have hcenter : Integration.centerCell tw = fun x => -vecDiv F x := by
    funext x
    unfold Integration.centerCell
    rw [htw]
    simp [integral_neg, hmean]
  rw [hcenter]
  exact hMinusOneNorm_neg_vecDiv_le hF hp

/-- The `L²` norm of a field bounded pointwise by a multiple of another one. -/
theorem sd_gradNormSq_le {F V : Vec 2 → Vec 2} (hF : Continuous F) (hV : Continuous V) {c : ℝ}
    (h : ∀ x, vecNormSq (F x) ≤ c ^ 2 * vecNormSq (V x)) :
    gradNormSq F ≤ c ^ 2 * gradNormSq V := by
  unfold gradNormSq
  have hFi := LeftToShow.integrableOn_unitCube_of_continuous
    (LeftToShow.continuous_vecNormSq_two.comp hF)
  have hVi := LeftToShow.integrableOn_unitCube_of_continuous
    (LeftToShow.continuous_vecNormSq_two.comp hV)
  calc ∫ x in unitCube, vecNormSq (F x) ≤ ∫ x in unitCube, c ^ 2 * vecNormSq (V x) :=
        integral_mono hFi (hVi.const_mul _) h
    _ = _ := integral_const_mul _ _

theorem sd_sqrt_comb_le {k₀ k₁ g₀ g₁ g₂ : ℝ} (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁) (h₀ : 0 ≤ g₀)
    (h₁ : 0 ≤ g₁) (h₂ : 0 ≤ g₂) :
    Real.sqrt (k₀ ^ 2 * g₀ + k₁ ^ 2 * (g₁ + g₂)) ≤
      k₀ * Real.sqrt g₀ + k₁ * Real.sqrt g₁ + k₁ * Real.sqrt g₂ := by
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have s0 := Real.sq_sqrt h₀
  have s1 := Real.sq_sqrt h₁
  have s2 := Real.sq_sqrt h₂
  have p0 := mul_nonneg hk₀ (Real.sqrt_nonneg g₀)
  have p1 := mul_nonneg hk₁ (Real.sqrt_nonneg g₁)
  have p2 := mul_nonneg hk₁ (Real.sqrt_nonneg g₂)
  nlinarith [mul_nonneg p0 p1, mul_nonneg p0 p2, mul_nonneg p1 p2]

end AVenhance.Infra.Section5.Contracts
end
