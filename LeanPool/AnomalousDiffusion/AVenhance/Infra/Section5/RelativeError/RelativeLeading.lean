/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeSpaceKill
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeSecondLast
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Assembly.SpaceKill
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Assembly.SecondLast
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters

/-! Amplitude-generic leading-energy estimates on the actual datum and T iterates.
The quadratic error has amplitude S squared; the base consumes only integrated gradients. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section5.LeftToShow

/-- `e.left.to.show` (8271–8293, proof 8294–8882), additive form, conditional on the §4
estimates for `T_{m-1} = T (Nstar β)` (proved elsewhere): `e.Tm.reg.upgrade` (n = 0),
`e.barf.cascade` (n = 0, ℓ = 1) and the composed analyticity `e.ass.f.anal.flows` of
`∂_iT_{m-1}∂_jT_{m-1} ∘ X_{m-1,l_k}` used for `l.flow.averages`; the constants `A`, `P` are those
estimates' constants (they depend on β only).  `hAn` is required only where `ξ_{m,k}(t) ≠ 0`
(the source flow bounds `e.Xm.bound.*` hold only on `supp ξ_{m,k}`, 7066–7075); every hypothesis
weakens as `A` grows, so `A` = max of the three upstream constants; `P = 2 + γ` suffices for the
Leibniz product of the `L²` bounds .  The bridge from the `L²_x` bounds on `T` to the `L¹`
bounds on `∂_iT ∂_jT ∘ X` is not written in the source (SOURCE_GAP-lite). -/
theorem relative_left_to_show_conditional (β C₀ A P : ℝ) (hA : 0 < A) (hP : 0 ≤ P) :
    ∃ C : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (S : ℝ) (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
        Real.sqrt (I.kappaSeq κ M (m - 1)) *
            Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (T (Nstar β) t) x)) ≤
          A * Real.sqrt (S ^ 2) →
        Real.sqrt (spaceTimeGradNormSq (materialGrad (streamVel (Φ (m - 1))) (T (Nstar β)))) ≤
          A * epsilon β I.Λ (m - 1) ^ (3 * delta β) * (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
            Real.sqrt (S ^ 2) * (tauP β I.Λ m)⁻¹ →
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ k : ℤ, Odd k → I.xiMK m k t ≠ 0 → ∀ i j : Fin 2,
          Infra.Ergodic.HasCoordinateAnalyticL1Bounds
            (fun y => ((spaceGrad (T (Nstar β) t) (I.xFlow hΦ m (lIdx β I.Λ m k) t y) i *
              spaceGrad (T (Nstar β) t) (I.xFlow hΦ m (lIdx β I.Λ m k) t y) j : ℝ) : ℂ))
            (A * epsilon β I.Λ (m - 1) ^ (-P) * S ^ 2)
            (epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) / A)) →
        |I.kappaSeq κ M m *
              spaceTimeGradNormSq (leadingGrad I hΦ m (I.kappaSeq κ M m) (T (Nstar β))) -
            I.kappaSeq κ M (m - 1) *
              spaceTimeGradNormSq (fun t x => spaceGrad (T (Nstar β) t) x)| ≤
          C * epsilon β I.Λ (m - 1) ^ (2 * delta β) * S ^ 2 := by
  obtain ⟨C1, h1⟩ := relative_ergodic_space_kill β C₀ A P hA hP
  obtain ⟨C2, h2⟩ := relative_ergodic_break_up_second_scaled β C₀ A P hA hP
  obtain ⟨C3, h3⟩ := relative_ergodic_break_up_last β C₀ A P hA hP
  refine ⟨|C1| + |C2| + |C3|, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm m hm hmM S θ₀ θprev T hTit hT0 hDt hAn
  have a1 := abs_nonneg C1
  have a2 := abs_nonneg C2
  have a3 := abs_nonneg C3
  have hΛ1 : C1 ≤ (I.Λ : ℝ) := by linarith [le_abs_self C1]
  have hΛ2 : C2 ≤ (I.Λ : ℝ) := by linarith [le_abs_self C2]
  have hΛ3 : C3 ≤ (I.Λ : ℝ) := by linarith [le_abs_self C3]
  have b1 := h1 I hz hx hh hΛ1 Φ hΦ κ hκ M hM hperm m hm hmM S θ₀ θprev T hTit hAn
  have b2 := h2 I hz hx hh hΛ2 Φ hΦ κ hκ M hM hperm m hm hmM S θ₀ θprev T hTit hT0
  have b3 := h3 I hz hx hh hΛ3 Φ hΦ κ hκ M hM hperm m hm hmM S θ₀ θprev T hTit hT0 hDt
  -- positivity of κ and the regularity of `T_{m-1}`
  have hβ := I.one_lt_beta
  have hβ' := I.beta_lt
  have he : 0 < epsilon β I.Λ M := Infra.Cutoff.epsilon_pos hβ hβ' I.two_pow_seven_le
  have hκpos : 0 < κ :=
    lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos he _)) (Set.mem_Icc.mp hperm).1
  have hκm : 0 < I.kappaSeq κ M m := kappaSeq_pos I hκpos M m
  have hN : 1 ≤ Nstar β := by
    have := Infra.Ingredients.Nstar_ge_256 hβ hβ'
    omega
  have hTsol := hTit.2 (Nstar β) hN le_rfl
  have hT := hTsol.1
  -- the exact break-up with `J = J_m^{κ_m}`
  have hJ : ∀ i j, Continuous fun t => I.flux (I.kappaSeq κ M m) m t i j :=
    fun i j => Infra.Section3.flux_entry_time_continuous I (by omega) _ i j
  have hid := ergodic_break_up I hΦ (m := m) (by omega) hκm (I.kappaSeq κ M (m - 1)) hT
    (fun t => I.flux (I.kappaSeq κ M m) m t) hJ
  -- fourth term vanishes
  have havg := timeAvgMat_flux_kappaSeq I κ (by omega : 1 ≤ m) hmM hκm
  have h4 : (∫ t in (0 : ℝ)..1, gradQuad (T (Nstar β))
        (timeAvgMat fun t => I.flux (I.kappaSeq κ M m) m t) t) -
      I.kappaSeq κ M (m - 1) * ∫ t in (0 : ℝ)..1, ∫ x in unitCube,
        vecNormSq (spaceGrad (T (Nstar β) t) x) = 0 := by
    rw [havg]
    simp only [gradQuad_smul_one]
    rw [intervalIntegral.integral_const_mul, sub_self]
  rw [h4, add_zero] at hid
  rw [hid]
  -- collect
  set e := epsilon β I.Λ (m - 1)
  set θ := S ^ 2
  have hθ : 0 ≤ θ := sq_nonneg S
  have hepos : 0 < e := Infra.Cutoff.epsilon_pos hβ hβ' I.two_pow_seven_le
  have hele : e ≤ 1 := Infra.Construction.epsilon_le_one hβ hβ' I.two_pow_seven_le
  have hδ := Infra.Ingredients.delta_le_one_sixteenth hβ hβ'
  have hpow : e ^ (500 : ℝ) ≤ e ^ (2 * delta β) :=
    Real.rpow_le_rpow_of_exponent_ge hepos hele (by linarith)
  have hp0 : 0 ≤ e ^ (500 : ℝ) := (Real.rpow_pos_of_pos hepos _).le
  have hq0 : 0 ≤ e ^ (2 * delta β) := (Real.rpow_pos_of_pos hepos _).le
  have c1 : C1 * e ^ (500 : ℝ) * θ ≤ |C1| * e ^ (2 * delta β) * θ := by
    apply mul_le_mul_of_nonneg_right _ hθ
    calc C1 * e ^ (500 : ℝ) ≤ |C1| * e ^ (500 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self C1) hp0
      _ ≤ |C1| * e ^ (2 * delta β) := mul_le_mul_of_nonneg_left hpow a1
  have c2 : C2 * e ^ (2 * delta β) * θ ≤ |C2| * e ^ (2 * delta β) * θ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C2) hq0) hθ
  have c3 : C3 * e ^ (2 * delta β) * θ ≤ |C3| * e ^ (2 * delta β) * θ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C3) hq0) hθ
  have hk1 : |I.kappaSeq κ M m * ∫ t in (0 : ℝ)..1,
        ((∫ x in unitCube, vecNormSq (leadingGrad I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x)) -
          gradQuad (T (Nstar β)) (leadingGramAvg I hΦ m (I.kappaSeq κ M m) t) t)| =
      I.kappaSeq κ M m * |∫ t in (0 : ℝ)..1,
        ((∫ x in unitCube, vecNormSq (leadingGrad I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x)) -
          gradQuad (T (Nstar β)) (leadingGramAvg I hΦ m (I.kappaSeq κ M m) t) t)| := by
    rw [abs_mul, abs_of_pos hκm]
  calc _ ≤ |I.kappaSeq κ M m * ∫ t in (0 : ℝ)..1,
          ((∫ x in unitCube,
              vecNormSq (leadingGrad I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x)) -
            gradQuad (T (Nstar β)) (leadingGramAvg I hΦ m (I.kappaSeq κ M m) t) t)| +
        |∫ t in (0 : ℝ)..1, gradQuad (T (Nstar β))
          (I.kappaSeq κ M m • leadingGramAvg I hΦ m (I.kappaSeq κ M m) t -
            I.flux (I.kappaSeq κ M m) m t) t| +
        |(∫ t in (0 : ℝ)..1, gradQuad (T (Nstar β)) (I.flux (I.kappaSeq κ M m) m t) t) -
          ∫ t in (0 : ℝ)..1, gradQuad (T (Nstar β))
            (timeAvgMat fun s => I.flux (I.kappaSeq κ M m) m s) t| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C1 * e ^ (500 : ℝ) * θ + C2 * e ^ (2 * delta β) * θ + C3 * e ^ (2 * delta β) * θ := by
        rw [hk1]
        exact add_le_add (add_le_add b1 b2) b3
    _ ≤ (|C1| + |C2| + |C3|) * e ^ (2 * delta β) * θ := by nlinarith only [c1, c2, c3]

end AVenhance.Infra.Section5.RelativeError
