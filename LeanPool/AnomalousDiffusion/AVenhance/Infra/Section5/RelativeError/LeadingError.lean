/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ClassicalRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityHm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters

/-! # The relative leading-gradient error `e.leadingord`

Source: `enhance.tex` 8114–8269 (`e.grad.tildetheta.again` and the five displays before
`e.leadingord`).  The bound

`√κ_m ‖∇θTilde_m - F ∇T_{m-1}‖_{L²_{t,x}} ≤ C ε_{m-1}^{2δ} S`,  `S = √κ_{m-1}
    ‖∇θ_{m-1}‖_{L²_{t,x}}`,

is exactly the field `RelativeLeaves.hLeadingError`.  The proof is the exact decomposition
(`LeadingErrorAlgebra`), the pointwise bounds `LeadingErrorBoundsFields`/`...Error`, the
`L²` assembly `LeadingErrorBoundsAssembly`, and the scale package `left_to_show_scales`.
At the terminal scale `m = M` only the uniform bound
`a_m² ε_m⁴/κ_m ≤ K κ_{m-1}` (valid through `m = M`) is used, never the printed boundedness of
`√(κ_m/κ_{m-1}) ε_m^{-γ}`; the `HTilde_m` input is the uniform `ε^{4δ}` bound. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section5

/-- The number of iterates `N_*` is positive. -/
theorem one_le_Nstar {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) : 1 ≤ Nstar β := by
  have h := Infra.Ingredients.Nstar_ge_eight_add_div hβ hβ'
  have hq := Infra.Ingredients.one_lt_q hβ hβ'
  have hd : 0 ≤ 128 * q β ^ 2 / (q β - 1) :=
    div_nonneg (by positivity) (by linarith)
  have : (1 : ℝ) ≤ (Nstar β : ℝ) := by linarith
  exact_mod_cast this

/-- **`e.leadingord`**: the leading-gradient error of the ansatz, relative to the amplitude
`S = √κ_{m-1} ‖∇θ_{m-1}‖` (the field `RelativeLeaves.hLeadingError`). -/
theorem relative_leading_error (β C₀ A CH : ℝ) (hA : 1 ≤ A) (hCH : 0 ≤ CH) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ → ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
      let S := Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))
      -- (hT0) √ν ‖∇T‖ ≤ A S
      Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (T (Nstar β) s) x)) ≤ A * S →
      -- (hT1) the first-order word part of the coordinate energy profile
      (∀ i : Fin 2, Real.sqrt (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq
          (fun s => spaceGrad (Infra.Section4.iterateSpatialWord [i] (T (Nstar β) s)))) ≤
        A * (A / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) * S) →
      -- (hHgrad) S-normalised e.Hm.gradient.L2: √κ_m ‖∇HTilde_m‖ ≤ CH ε^{4δ} S
      Real.sqrt (I.kappaSeq κ M m) * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x)) ≤
        CH * epsilon β I.Λ (m - 1) ^ (4 * delta β) * S →
      Real.sqrt (I.kappaSeq κ M m) * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x -
            LeftToShow.leadingGrad I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s x)) ≤
        Ca * epsilon β I.Λ (m - 1) ^ (2 * delta β) * S := by
  obtain ⟨K, hK1, hK⟩ := LeftToShow.left_to_show_scales β C₀
  have hK0 : 0 ≤ K := by linarith
  have hA0 : 0 ≤ A := by linarith
  refine ⟨2 * (Real.sqrt K * (20 + 2 ^ 20 * K) * A + 8 * Real.sqrt K * K * A ^ 2 + CH),
    by positivity, ?_⟩
  intro I hz hx hh Φ hΦ κ hκ M hM hperm m hm hmM θ₀ θprev T hθprev hTit S hT0 hT1 hHg
  have hβ := I.one_lt_beta
  have hβ' := I.beta_lt
  obtain ⟨hκm, hmono, -, h4, -, -, h7⟩ := hK I hz hx hh κ hκ M hM hperm m hm hmM
  have hκp : 0 < I.kappaSeq κ M (m - 1) := hκm.trans_le hmono
  -- regularity of the last iterate
  have hN := one_le_Nstar hβ hβ'
  have hsol := hTit.2 (Nstar β) hN le_rfl
  have hTjoint := hsol.1
  have hTs : ∀ t, 0 < t → ContDiff ℝ ∞ (T (Nstar β) t) := fun t ht =>
    classicalSol_space_contDiff_of_nonneg hsol ht.le
  -- regularity of `HTilde_m` on the open half space
  have hHJ := Integration.Hm_contDiffOn_Ioi_top I hΦ (by omega : 1 ≤ m) hκm hθprev hTit
  have hH2 : ContDiffOn ℝ 2
      (fun p : ℝ × Vec 2 => I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := hHJ.of_le (by simp)
  have hHs : ∀ t, 0 < t → ContDiff ℝ ∞ (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t) :=
    fun t ht => Integration.Hm_slice_contDiff_pos I hΦ (by omega : 1 ≤ m) hκm hθprev hTit ht
  have hL2 := sqrt_leadingErr_le hΦ hm hκm hTjoint hTs hH2 hHs
  -- scalar bookkeeping
  have hε1 := epsilon_pos' I (m - 1)
  have hε1le := epsilon_le_one' I (m - 1)
  have hεm := epsilon_pos' I m
  have hδ := delta_pos' I
  have hγ := Infra.Ingredients.gamma_pos hβ hβ'
  have hexp := corrector_second_term_exponent hβ hβ'
  have hS : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  set sm := Real.sqrt (I.kappaSeq κ M m) with hsm
  set sp := Real.sqrt (I.kappaSeq κ M (m - 1)) with hsp
  set c := a β I.Λ m * epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m with hc
  set e := epsilon β I.Λ (m - 1) ^ (2 * delta β) with he
  have he0 : 0 ≤ e := (Real.rpow_pos_of_pos hε1 _).le
  have hcs : c * sm ≤ Real.sqrt K * sp :=
    corr_mul_sqrt_le (a_nonneg' I m) hκm hK0 hκp.le h4
  -- the two scale ratios
  have hr1 : epsilon β I.Λ m / epsilon β I.Λ (m - 1) ≤ K * e := by
    have := eps_ratio_le (s := 1) (d := 2 * delta β) hε1 hε1le hK0 h7
      (by linarith [hexp, hγ])
    rwa [Real.rpow_one] at this
  have hr2 : epsilon β I.Λ m / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ K * e :=
    eps_ratio_le hε1 hε1le hK0 h7 (by linarith [hexp])
  have hρ : 0 < epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) := Real.rpow_pos_of_pos hε1 _
  -- the four terms
  have t1 := gradient_term_le (c := c) (sm := sm) (sp := sp)
    (nT := Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (T (Nstar β) s) x)))
    (εm := epsilon β I.Λ m) (e₁ := epsilon β I.Λ (m - 1)) (e := e) (K := K) (A := A) (S := S)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hεm.le hε1 hK1 he0 hcs hT0 hr1
  have t2 := fun q : Fin 2 => hessian_term_le (c := c) (sm := sm) (sp := sp)
    (s := Real.sqrt (spaceTimeGradNormSq
      (fun s => spaceGrad (Infra.Section4.iterateSpatialWord [q] (T (Nstar β) s)))))
    (εm := epsilon β I.Λ m) (ρ := epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) (e := e) (K := K)
    (A := A) (S := S) (Real.sqrt_nonneg _) hεm.le hρ hK1 hS hcs (hT1 q) hr2
  have t3 : sm * Real.sqrt (spaceTimeGradNormSq (fun s x =>
      spaceGrad (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x)) ≤ CH * e * S :=
    hHg.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (rpow_four_le_two hε1 hε1le hδ.le) hCH) hS)
  have hnE : 0 ≤ sm := Real.sqrt_nonneg _
  calc sm * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x -
            LeftToShow.leadingGrad I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s x))
      ≤ sm * (2 * _) := mul_le_mul_of_nonneg_left hL2 hnE
    _ = 2 * (sm * ((20 * e * c + epsilon β I.Λ m * c * (16 * (2 ^ 16 * (epsilon β I.Λ (m -
        1))⁻¹))) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (T (Nstar β) s) x))) +
        sm * (4 * epsilon β I.Λ m * c *
          Real.sqrt (spaceTimeGradNormSq
            (fun s => spaceGrad (Infra.Section4.iterateSpatialWord [0] (T (Nstar β) s))))) +
        sm * (4 * epsilon β I.Λ m * c *
          Real.sqrt (spaceTimeGradNormSq
            (fun s => spaceGrad (Infra.Section4.iterateSpatialWord [1] (T (Nstar β) s))))) +
        sm * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x))) := by ring
    _ ≤ 2 * (Real.sqrt K * (20 + 2 ^ 20 * K) * A * e * S +
        4 * Real.sqrt K * K * A ^ 2 * e * S + 4 * Real.sqrt K * K * A ^ 2 * e * S +
        CH * e * S) := by
      have u0 := t2 0
      have u1 := t2 1
      linarith
    _ = _ := by ring

end AVenhance.Infra.Section5.RelativeError
