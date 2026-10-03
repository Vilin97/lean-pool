/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIAnsatzL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIAnsatzScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIAnsatzPointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityHm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TIterateSmooth

/-! # Part I: `‖θTilde_m - T_{m-1}‖_{L^∞((0,1];L²)} ≤ C ε_{m-1}^δ ‖θ₀‖_{L²}` (`e.tildethetam.to.Tm`)

Source: `enhance.tex` 8882-9133.  The theorem `section_four_ansatz_bound` is the `N`-normalised
form of `hSectionFourAnsatz` on `t ∈ (0,1]`, with the two inputs the proof in the source quotes:

* `hTjet`: the first-order `T` jet `‖∇T_{m-1}(s)‖_{L²} ≤ A_T ‖θ₀‖ ε_{m-1}^{-(1+γ/2)}`
  (`e.Tm.reg.upgrade`, `n = 0`);
* `hHsup`: `e.Hm.Linfty`, `‖HTilde_m(t)‖_{L²} ≤ C_H ε_{m-1}^δ ‖θ₀‖`.

The corrector part is bounded pointwise (`ansatz_sub_T_sub_Hm_abs_le`) by
`4 ‖Χ‖_∞ (|∂₁T| + |∂₂T|)` with `‖Χ‖_∞ = a ε_m³ /(2π κ_m)`, and the scale package
`left_to_show_scales` plus `q(1-γ) - 1 - γ/2 = 4δ` turn it into `K² ε_{m-1}^δ`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5
open AVenhance.Infra.Section5.LeftToShow

/-- **`e.tildethetam.to.Tm`** (`N`-normalised): the ansatz is within `C ε_{m-1}^δ ‖θ₀‖` of
`T_{m-1}` in `L²(𝕋²)` for every `t ∈ (0,1]`. -/
theorem section_four_ansatz_bound (β C₀ AT CHs : ℝ) (hAT : 0 ≤ AT) (hCHs : 0 ≤ CHs) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ → ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
        -- (hTjet) first-order T jet with amplitude ‖θ₀‖ (implied by the second conjunct of the
        -- `iterate_T_upgrade_of_theta_flow_material` with v = [i], N = 2‖θ₀‖)
        FirstOrderSliceJetContract I m T AT (Real.sqrt (l2NormSq θ₀)) →
        -- (hHsup) e.Hm.Linfty, N-normalised, for t ∈ (0,1]
        HmSupContract I hΦ m (I.kappaSeq κ M m) θ₀ T CHs →
        ∀ t ∈ Set.Ioc (0 : ℝ) 1,
          Real.sqrt (l2NormSq (fun x => I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x -
            T (Nstar β) t x)) ≤ Ca * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) := by
  obtain ⟨K, hK1, hK⟩ := left_to_show_scales β C₀
  refine ⟨8 * AT * K ^ 2 + CHs, by positivity, ?_⟩
  intro I hz hx hh Φ hΦ κ hκp M hM hperm m hm hmM θ₀ θprev T hθprev hT hjet hHsup t ht
  obtain ⟨hκpos, -, -, -, -, hA, hemK⟩ := hK I hz hx hh κ hκp M hM hperm m hm hmM
  have hm1 : 1 ≤ m := by omega
  set κm := I.kappaSeq κ M m with hκm
  set e := epsilon β I.Λ (m - 1) with he_def
  set em := epsilon β I.Λ m with hem_def
  set N := Real.sqrt (l2NormSq θ₀) with hN
  have he : 0 < e := RelativeError.epsilon_pos' I (m - 1)
  have he1 : e ≤ 1 := RelativeError.epsilon_le_one' I (m - 1)
  have hem : 0 < em := RelativeError.epsilon_pos' I m
  have ha : 0 < a β I.Λ m := Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le)
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  set Tn := T (Nstar β) with hTn
  have hTt : ContDiff ℝ (⊤ : ℕ∞) (Tn t) :=
    tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.1.le
  have hHt : ContDiff ℝ (⊤ : ℕ∞) (I.Hm hΦ m κm Tn t) :=
    Hm_slice_contDiff_pos I hΦ hm1 hκpos hθprev hT ht.1
  have hAt : ContDiff ℝ (⊤ : ℕ∞) (I.ansatz hΦ m κm Tn t) :=
    ansatz_slice_contDiff I hΦ m κm hTt hHt
  -- the corrector part `P = θTilde - T - HTilde`
  set P : Vec 2 → ℝ := fun x => I.ansatz hΦ m κm Tn t x - Tn t x - I.Hm hΦ m κm Tn t x with hP
  have hPc : Continuous P := (hAt.continuous.sub hTt.continuous).sub hHt.continuous
  have hg : ∀ i : Fin 2, Continuous (fun x => spaceGrad (Tn t) x i) := fun i =>
    (contDiff_spaceGrad_component hTt i).continuous
  have hBc : Continuous (fun x => |spaceGrad (Tn t) x 0| + |spaceGrad (Tn t) x 1|) :=
    (hg 0).abs.add (hg 1).abs
  set c4 : ℝ := 4 * chiSup I κm m with hc4
  have hc0 : 0 ≤ c4 := by
    have := chiSup_nonneg I hκpos m
    positivity
  have hPle : Real.sqrt (l2NormSq P) ≤
      c4 * (Real.sqrt (l2NormSq (fun x => spaceGrad (Tn t) x 0)) +
        Real.sqrt (l2NormSq (fun x => spaceGrad (Tn t) x 1))) := by
    calc Real.sqrt (l2NormSq P)
        ≤ Real.sqrt (l2NormSq (fun x => c4 *
            (|spaceGrad (Tn t) x 0| + |spaceGrad (Tn t) x 1|))) :=
          sqrt_l2NormSq_le_of_abs_le (continuous_const.mul hBc) fun x =>
            ansatz_sub_T_sub_Hm_abs_le I hΦ hm hκpos hTt x
      _ = c4 * Real.sqrt (l2NormSq (fun x =>
            |spaceGrad (Tn t) x 0| + |spaceGrad (Tn t) x 1|)) :=
          sqrt_l2NormSq_const_mul hc0 _
      _ ≤ _ := mul_le_mul_of_nonneg_left (sqrt_l2NormSq_abs_add_le (hg 0) (hg 1)) hc0
  have hts : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have hj0 := hjet 0 t hts
  have hj1 := hjet 1 t hts
  -- scale bound
  have hscale : chiSup I κm m * e ^ (-(1 + gamma β / 2)) ≤ K ^ 2 * e ^ delta β := by
    unfold chiSup
    rw [chi_const_eq ha hem hκpos]
    exact ansatz_scale_bound I.one_lt_beta I.beta_lt hK1 he he1 hem
      (by positivity) hA hemK
  have hPfinal : Real.sqrt (l2NormSq P) ≤ 8 * AT * K ^ 2 * e ^ delta β * N := by
    have hep : 0 ≤ e ^ (-(1 + gamma β / 2)) := Real.rpow_nonneg he.le _
    calc Real.sqrt (l2NormSq P)
        ≤ c4 * (AT * N * e ^ (-(1 + gamma β / 2)) + AT * N * e ^ (-(1 + gamma β / 2))) :=
          hPle.trans (mul_le_mul_of_nonneg_left (add_le_add hj0 hj1) hc0)
      _ = 8 * AT * N * (chiSup I κm m * e ^ (-(1 + gamma β / 2))) := by
          rw [hc4]; ring
      _ ≤ 8 * AT * N * (K ^ 2 * e ^ delta β) :=
          mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = 8 * AT * K ^ 2 * e ^ delta β * N := by ring
  -- triangle inequality
  have hsplit : (fun x => I.ansatz hΦ m κm Tn t x - Tn t x) = fun x => P x + I.Hm hΦ m κm Tn t x
      := by
    funext x
    simp only [hP]
    ring
  have hdelta : 0 ≤ e ^ delta β := Real.rpow_nonneg he.le _
  calc Real.sqrt (l2NormSq (fun x => I.ansatz hΦ m κm Tn t x - Tn t x))
      = Real.sqrt (l2NormSq (fun x => P x + I.Hm hΦ m κm Tn t x)) := by rw [hsplit]
    _ ≤ Real.sqrt (l2NormSq P) + Real.sqrt (l2NormSq (I.Hm hΦ m κm Tn t)) :=
        sqrt_l2NormSq_add_le_of_continuous hPc hHt.continuous
    _ ≤ 8 * AT * K ^ 2 * e ^ delta β * N + CHs * e ^ delta β * N :=
        add_le_add hPfinal (hHsup t ht)
    _ = (8 * AT * K ^ 2 + CHs) * e ^ delta β * N := by ring

end AVenhance.Infra.Section5.Integration
