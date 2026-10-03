/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredNormie3Time
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredNormie3Scale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredFinal
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredTime
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoffScalar
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs

/-! # `Normie3CenteredSourceContract`

In the corrected form, `normie3 = Σ_k ξ_k frob (F_kᵀ (𝒥 - C⁰_k)) ∇G_k` with `C⁰_k = cellFluxCell ∘
    Y_k`, whose
fast factor `𝒥 - cellFluxCell` has exact zero cell mean on `supp ξ_{m,k}`.  There is no divergence
part: the whole of `normie3` is a locally finite sum of fast-slow products, and the centered
ergodic estimate of `Contracts/TermCenteredNd.lean` bounds its `HDot⁻¹` norm at a fixed time.
Time integration (`sd_time_transfer`) and the scale arithmetic (`n3_arith_final`, `n3_scale1`,
`n3_exp_scale`; exponent identity `q(1 - γ) - 1 - γ/2 = 4δ`) give `C ε_{m-1}^δ √κ_m B`.  Inputs at
amplitude `B`: `TPositiveJetsContract`, `TGradientContract`, `FirstOrderGradJetContract`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff ENNReal

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
  AVenhance.Infra.Section5.RelativeError AVenhance.Infra.Ergodic

theorem normie3CenteredSource_contract (β C₀ A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      ∀ B : ℝ, 0 ≤ B → TPositiveJetsContract I m T A B →
        TGradientContract β (I.kappaSeq κ M (m - 1)) T A B →
        FirstOrderGradJetContract I m (I.kappaSeq κ M (m - 1)) T A B →
        Normie3CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C B) := by
  by_cases hb : 1 < β ∧ β < 4 / 3
  swap
  · exact ⟨0, le_rfl, 0, fun I => absurd ⟨I.one_lt_beta, I.beta_lt⟩ hb⟩
  obtain ⟨hβ, hβ'⟩ := hb
  obtain ⟨K, hK1, hK⟩ := LeftToShow.left_to_show_scales β C₀
  have hK0 : 0 < K := by linarith
  set A1 : ℝ := max A 1 with hA1def
  have hA1 : 1 ≤ A1 := le_max_right _ _
  have hAA1 : A ≤ A1 := le_max_left _ _
  obtain ⟨cA, c₂a, hcA, hc₂a, hAn⟩ := n3_slow_composed_bounds β A1 hA1
  have hδ := Infra.Ingredients.delta_pos hβ hβ'
  have hγ := Infra.Ingredients.gamma_pos hβ hβ'
  have hγ1 := gamma_lt_one_of_range hβ hβ'
  have hq1 := Infra.Ingredients.one_lt_q hβ hβ'
  have hexp := corrector_second_term_exponent hβ hβ'
  have hexp3 := n3_exponent hβ hβ'
  obtain ⟨Mx, hMx0, hMx⟩ := n3_exp_scale (γ := gamma β) (δ := delta β) hγ.le hγ1.le hδ
    (K := K) (c₂ := c₂a) hK1 hc₂a
  set tau : ℝ := min (1 / 4 : ℝ) (1 / (2 * c₂a * K)) with htaudef
  have htau : 0 < tau := lt_min (by norm_num) (by positivity)
  set M₁ : ℝ := (1 + K) * K with hM₁def
  have hM₁0 : 0 ≤ M₁ := by positivity
  set Cfin : ℝ := 1152 * sdCd * (2 ^ 22 * M₁ * Real.sqrt K * A1 +
    2 * 14 * M₁ * Real.sqrt K * A1 ^ 2 + cA * Mx * K) with hCfin
  refine ⟨Cfin, ?_, tau ^ (-(1 / (2 * delta β))), ?_⟩
  · have := sdCd_pos
    positivity
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ _ _ _ _ m hm hmM θprev T hθprev hT B hB
    hJets hTG hHess
  obtain ⟨hm2, hκm⟩ := onA7_basic I hperm hR hm
  obtain ⟨-, hmono, h3, h4, -, h6, h7⟩ := hK I hz hx hh κ hκ M hM hperm m hm2 hmM
  have hκp : 0 < I.kappaSeq κ M (m - 1) := hκm.trans_le hmono
  have hx0 : 0 < epsilon β I.Λ (m - 1) := epsilon_pos' I (m - 1)
  have hx1 : epsilon β I.Λ (m - 1) ≤ 1 := epsilon_le_one' I (m - 1)
  have hy0 : 0 < epsilon β I.Λ m := epsilon_pos' I m
  have hy1 : epsilon β I.Λ m ≤ 1 := epsilon_le_one' I m
  have hρ0 : 0 < epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) := Real.rpow_pos_of_pos hx0 _
  have hρx : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ epsilon β I.Λ (m - 1) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hx0 hx1
      (show (1 : ℝ) ≤ 1 + gamma β / 2 by linarith)
    simpa using h
  have hψ0 : 0 ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 := mul_nonneg (a_nonneg' I m) (sq_nonneg _)
  have hψκ : (a β I.Λ m * epsilon β I.Λ m ^ 2) ^ 2 ≤
      K * I.kappaSeq κ M m * I.kappaSeq κ M (m - 1) := by
    have h4' := (div_le_iff₀ hκm).1 h4
    calc (a β I.Λ m * epsilon β I.Λ m ^ 2) ^ 2
        = a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 := by ring
      _ ≤ K * I.kappaSeq κ M (m - 1) * I.kappaSeq κ M m := h4'
      _ = _ := by ring
  -- smallness of `ε^{2δ}` from the Λ-threshold
  have hC₁pos : 0 < tau ^ (-(1 / (2 * delta β))) := Real.rpow_pos_of_pos htau _
  have hxΛ : epsilon β I.Λ (m - 1) ≤ (I.Λ : ℝ)⁻¹ :=
    LeftToShow.epsilon_le_inv_Lambda hβ hβ' I.two_pow_seven_le (by omega)
  have hxC : epsilon β I.Λ (m - 1) ≤ tau ^ (1 / (2 * delta β)) := by
    refine hxΛ.trans ?_
    have := inv_anti₀ hC₁pos hΛ
    rwa [Real.rpow_neg htau.le, inv_inv] at this
  have hetau : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ tau := by
    calc epsilon β I.Λ (m - 1) ^ (2 * delta β)
        ≤ (tau ^ (1 / (2 * delta β))) ^ (2 * delta β) :=
          Real.rpow_le_rpow hx0.le hxC (by positivity)
      _ = tau := by
          rw [← Real.rpow_mul htau.le, one_div_mul_cancel (by positivity), Real.rpow_one]
  have hsmall1 : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 / 4 := hetau.trans (min_le_left _ _)
  have hsmall2 : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 / (2 * c₂a * K) :=
    hetau.trans (min_le_right _ _)
  have hNy : (ergodicFrequency β I.Λ m : ℝ) = (epsilon β I.Λ m)⁻¹ :=
    ergodicFrequency_cast β _ m
  obtain ⟨hZ, hrN⟩ := sd_rN_facts hx0 hx1 hy0 h7 hK1 hc₂a hexp hsmall2
  have hrN' : 2 ≤ epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) / c₂a *
      (ergodicFrequency β I.Λ m : ℝ) := by rwa [hNy]
  -- the two scale inequalities
  have hΛ₁ : epsilon β I.Λ m * (1 + a β I.Λ m * epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m) ≤
      M₁ * (epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) * epsilon β I.Λ (m - 1) ^ delta β) :=
    n3_scale1 hx0 hx1 hy0 hy1 h7 hK1 hγ.le hγ1.le h6 hexp3
  have hΛ₂ : (1 + a β I.Λ m * epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m) *
      (((epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) ^ 2)⁻¹ *
        Real.exp (-(epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) / c₂a) *
          (ergodicFrequency β I.Λ m : ℝ) / 4096)) ≤ Mx * epsilon β I.Λ (m - 1) ^ delta β := by
    rw [hNy]
    exact hMx _ _ _ hx0 hx1 hy0 hy1 h6 hZ
  -- the jet inputs at the constant `A1`
  have hJets1 : PositiveTemperatureJets A1 (epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) B
      (T (Nstar β)) := sd_jets_mono hA hAA1 hρ0 hB hJets
  have hTG1 : Real.sqrt (I.kappaSeq κ M (m - 1)) *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (T (Nstar β) s) x)) ≤ A1 * B :=
    hTG.trans (mul_le_mul_of_nonneg_right hAA1 hB)
  have hHess1 : ∀ i : Fin 2, Real.sqrt (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq
      (fun s => spaceGrad (Infra.Section4.iterateSpatialWord [i] (T (Nstar β) s)))) ≤
      A1 * (A1 / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) * B := fun i =>
    (hHess i).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul hAA1 (div_le_div_of_nonneg_right hAA1 hρ0.le) (div_nonneg hA hρ0.le)
        (by linarith)) hB)
  have hTs : ∀ t : ℝ, 0 ≤ t → ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) t) := fun t ht =>
    Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht
  have hTp : ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (T (Nstar β) t) := fun t ht =>
    Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht
  have hTjoint := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β) le_rfl
  -- the three energy fields
  let V : Fin 3 → ℝ → Vec 2 → Vec 2 := ![fun t x => spaceGrad (T (Nstar β) t) x,
    fun t x => spaceGrad (Infra.Section4.iterateSpatialWord [0] (T (Nstar β) t)) x,
    fun t x => spaceGrad (Infra.Section4.iterateSpatialWord [1] (T (Nstar β) t)) x]
  have hVj : ∀ (j : Fin 3) (i : Fin 2), ContinuousOn (fun p : ℝ × Vec 2 => V j p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    intro j i
    fin_cases j
    · exact sa_gradT_cont hTjoint i
    · exact sa_hess_cont hTjoint 0 i
    · exact sa_hess_cont hTjoint 1 i
  have hVc : ∀ (j : Fin 3) (t : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → Continuous (V j t) := by
    intro j t ht
    refine continuous_pi fun i => ?_
    exact (hVj j i).comp_continuous (Continuous.prodMk continuous_const continuous_id)
      (fun x => ⟨⟨ht.1.le, ht.2.le⟩, Set.mem_univ x⟩)
  have hd0 : 0 ≤ epsilon β I.Λ (m - 1) ^ delta β := (Real.rpow_pos_of_pos hx0 _).le
  have hCf0 : 0 ≤ cA * B * ((epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) ^ 2)⁻¹ := by positivity
  have hr0 : 0 < epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) / c₂a := div_pos hρ0 hc₂a
  have hxinv : 0 ≤ (2 : ℝ) ^ 22 * (epsilon β I.Λ (m - 1))⁻¹ := by positivity
  -- abbreviations of the coefficients
  set ψ : ℝ := a β I.Λ m * epsilon β I.Λ m ^ 2 with hψdef
  set Rr : ℝ := ψ / I.kappaSeq κ M m with hRr
  have hRr0 : 0 ≤ Rr := by positivity
  set E : ℝ := Real.exp (-(epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) / c₂a) *
    (ergodicFrequency β I.Λ m : ℝ) / 4096) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hCd := sdCd_pos
  have hP0 : 0 ≤ 144 * sdCd * epsilon β I.Λ m * (4 * ψ * (1 + Rr)) *
      (2 ^ 22 * (epsilon β I.Λ (m - 1))⁻¹) := by positivity
  have hP1 : 0 ≤ 144 * sdCd * epsilon β I.Λ m * (4 * ψ * (1 + Rr)) * 14 := by positivity
  have hP2 : 0 ≤ 144 * sdCd * (cA * B * ((epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) ^ 2)⁻¹) *
      (4 * ψ * (1 + Rr)) * E := by positivity
  have htime := sd_time_transfer (f := fun t x => Integration.centerCell
    (normie3 I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t) x) (V := V)
    (P := ![144 * sdCd * epsilon β I.Λ m * (4 * ψ * (1 + Rr)) *
        (2 ^ 22 * (epsilon β I.Λ (m - 1))⁻¹),
      144 * sdCd * epsilon β I.Λ m * (4 * ψ * (1 + Rr)) * 14,
      144 * sdCd * epsilon β I.Λ m * (4 * ψ * (1 + Rr)) * 14])
    (P₂ := 144 * sdCd * (cA * B * ((epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) ^ 2)⁻¹) *
      (4 * ψ * (1 + Rr)) * E)
    (by
      intro j
      fin_cases j
      · exact hP0
      · exact hP1
      · exact hP1) hP2 hVj (by
      intro t ht
      have hTt := hTs t ht.1.le
      have hTpt := hTp t ht.1.le
      have key := n3_time_bound I hΦ hm2 hκm (T (Nstar β)) hTt hTpt
        (Cf := cA * B * ((epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) ^ 2)⁻¹)
        (r := epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) / c₂a)
        (k₀ := 2 ^ 22 * (epsilon β I.Λ (m - 1))⁻¹) (k₁ := 14) hxinv (by norm_num)
        (V₀ := V 0 t) (V₁ := V 1 t) (V₂ := V 2 t) (hVc 0 t ht) (hVc 1 t ht) (hVc 2 t ht)
        (fun k p j x => n3_slow_pointwise I hΦ hm2 (T (Nstar β)) hTt k p j x) hCf0 hr0
        (fun k hk p j => hAn I hΦ hm2 hB (T (Nstar β)) hJets1 hTs hTp hsmall1 ht
          (k := k.1) hk p j)
        (fun k hk => sd_flow_nearIdentity I hΦ hm2 hsmall1 ht hk) hrN'
      refine key.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      have e1 : sdCd / (ergodicFrequency β I.Λ m : ℝ) = sdCd * epsilon β I.Λ m := by
        rw [hNy, div_inv_eq_mul]
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [e1]
      ring)
  refine htime.trans (ENNReal.ofReal_le_ofReal ?_)
  have hfin := n3_arith_final (x := epsilon β I.Λ (m - 1)) (y := epsilon β I.Λ m)
    (κ := I.kappaSeq κ M m) (ν := I.kappaSeq κ M (m - 1)) (ψ := ψ) (B := B) (A := A1)
    (K := K) (Cd := sdCd) (c₀ := 2 ^ 22) (c₁ := 14) (c₂ := cA) (M₁ := M₁) (M₂ := Mx)
    (ρ := epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2))
    (d := epsilon β I.Λ (m - 1) ^ delta β) (E := E)
    (D₀ := Real.sqrt (spaceTimeGradNormSq (V 0))) (D₁ := Real.sqrt (spaceTimeGradNormSq (V 1)))
    (D₂ := Real.sqrt (spaceTimeGradNormSq (V 2))) (R := Rr) hK1 hκm hκp h3 hψ0 hψκ hx0 hρ0 hρx
    hd0 hB (by linarith) hCd.le (by positivity) (by norm_num) hcA.le hM₁0 hMx0 hy0.le hRr0 hE0
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hTG1 (hHess1 0) (hHess1 1)
    hΛ₁ hΛ₂
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine le_of_eq_of_le (by ring) (hfin.trans (le_of_eq ?_))
  rw [hCfin]

end AVenhance.Infra.Section5.Contracts
end
