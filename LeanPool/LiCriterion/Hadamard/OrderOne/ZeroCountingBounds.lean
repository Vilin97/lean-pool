/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import Mathlib.Data.Set.Card
import Mathlib.Analysis.Analytic.Order
import LeanPool.LiCriterion.Hadamard.ZeroCounting
import LeanPool.LiCriterion.Hadamard.ZeroSet

/-!
Zero counting bounds for a `ZeroSet` enumeration, in the order‑`≤ 1` regime.

This file bridges the Jensen/divisor-based counting lemma in
`LZC/HadamardFactorization/ZeroCounting.lean` to the `ZeroSet`-based canonical
product development.
-/

open scoped BigOperators

namespace Hadamard

open Complex Real Filter Metric MeromorphicOn

namespace OrderOne

/-! ### Relating `ZeroSet` enumerations to divisor support -/

lemma mem_divisor_support_of_simple_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} (_hR : 0 < R) {u : ℂ}
    (hu_mem : u ∈ closedBall (0 : ℂ) |R|)
    (hu0 : f u = 0) (hu' : deriv f u ≠ 0) :
    u ∈ (MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)).support := by
  -- Compute the divisor value at `u` via the (analytic) meromorphic order.
  have hmer : MeromorphicOn f (closedBall (0 : ℂ) |R|) := fun z _ =>
    (hf.analyticAt z).meromorphicAt
  have han : AnalyticAt ℂ f u := hf.analyticAt u
  have horder : analyticOrderAt f u = 1 := by
    -- `analyticOrderAt (f· - f u) u = 1` and `f u = 0`.
    simpa [hu0] using han.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hu'
  have hmerOrder : meromorphicOrderAt f u = (1 : WithTop ℤ) := by
    -- `meromorphicOrderAt = ENat.map Nat.cast (analyticOrderAt ...)`.
    simpa [horder] using han.meromorphicOrderAt_eq
  have hdiv :
      MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u = (meromorphicOrderAt f u).untop₀ :=
    MeromorphicOn.divisor_apply hmer hu_mem
  have : MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u = (1 : ℤ) := by
    simp [hdiv, hmerOrder, WithTop.untop₀]
  have hdiv_ne : MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u ≠ 0 := by
    simp [this]
  have : u ∈ Function.support (fun x : ℂ => MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) x) :=
    Function.mem_support.2 hdiv_ne
  simpa [Function.locallyFinsuppWithin.support] using this

lemma mem_divisor_support_of_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} {u : ℂ}
    (hu_mem : u ∈ closedBall (0 : ℂ) |R|)
    (hf0 : f 0 ≠ 0) (hu0 : f u = 0) :
    u ∈ (MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)).support := by
  -- Compute the divisor value at `u` via the meromorphic order.
  have hmer : MeromorphicOn f (closedBall (0 : ℂ) |R|) := fun z _ =>
    (hf.analyticAt z).meromorphicAt
  have han : AnalyticAt ℂ f u := hf.analyticAt u
  -- Use preconnectedness of the closed ball to rule out infinite order.
  have hf_an : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |R|) := by
    intro z _
    exact hf.analyticAt z
  have h0_mem : (0 : ℂ) ∈ closedBall (0 : ℂ) |R| := by
    simp [Metric.mem_closedBall, abs_nonneg R]
  have horder0 : analyticOrderAt f 0 = 0 :=
    (hf.analyticAt 0).analyticOrderAt_eq_zero.2 hf0
  have horder0_ne_top : analyticOrderAt f 0 ≠ ⊤ := by
    simp [horder0]
  have hpre : IsPreconnected (closedBall (0 : ℂ) |R|) :=
    (convex_closedBall (0 : ℂ) |R|).isPreconnected
  have horder_ne_top : analyticOrderAt f u ≠ ⊤ :=
    hf_an.analyticOrderAt_ne_top_of_isPreconnected hpre h0_mem hu_mem horder0_ne_top
  have hdiv :
      MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u = (meromorphicOrderAt f u).untop₀ :=
    MeromorphicOn.divisor_apply hmer hu_mem
  have hmerOrder : meromorphicOrderAt f u = (analyticOrderAt f u).map (↑) :=
    han.meromorphicOrderAt_eq
  have horder_ne0 : analyticOrderAt f u ≠ 0 := (han.analyticOrderAt_ne_zero).2 hu0
  -- Show the divisor value is nonzero.
  -- Show the divisor value is nonzero.
  have hdiv_ne : MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u ≠ 0 := by
    cases hAU : analyticOrderAt f u with
    | top =>
        cases (horder_ne_top (by simp [hAU]))
    | coe n =>
        have hn_ne0 : n ≠ 0 := by
          intro hn0
          apply horder_ne0
          simp [hAU, hn0]
        have : MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u = (n : ℤ) := by
          simp [hdiv, hmerOrder, hAU]
        simp [this, hn_ne0]
  have : u ∈ Function.support (fun x : ℂ => MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) x) :=
    Function.mem_support.2 hdiv_ne
  simpa [Function.locallyFinsuppWithin.support] using this

/-! ### Zero counting for the `ZeroSet` index type -/

theorem ncard_zeros_le_of_order_le_one
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f) (hf_order_le : order f ≤ 1)
    (Z : ZeroSet f) [Countable Z.Zero]
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_simple : ∀ ρ : Z.Zero, deriv f (Z.z ρ) ≠ 0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r →
        (({ρ : Z.Zero | ‖Z.z ρ‖ ≤ r} : Set Z.Zero).ncard : ℝ) ≤
          ((2 * r) ^ ((1 : ℝ) + ε) - Real.log ‖f 0‖) / Real.log 2 := by
  intro ε hε
  -- `f 0 ≠ 0` since all zeros are nonzero and `Z` enumerates all zeros.
  have hf0 : f 0 ≠ 0 := by
    intro hf0
    rcases (h_zeros_only 0).1 hf0 with ⟨ρ, hρ⟩
    exact (h_z_ne_zero ρ) (by simp [hρ])
  -- Growth bound on `maxModulus f R` from `order f ≤ 1`.
  obtain ⟨R₁, hmax⟩ :=
    Hadamard.ZeroCounting.maxModulus_le_exp_rpow_of_order_le_one f hf_finite hf_order_le ε hε
  refine ⟨max R₁ 1, ?_⟩
  intro r hr
  have hr_ge_R1 : R₁ ≤ 2 * r := by
    have hR1_le : R₁ ≤ r := le_trans (le_max_left _ _) hr
    have hr_pos : 0 < r :=
      lt_of_lt_of_le
        (by norm_num : (0 : ℝ) < 1)
        (le_trans (le_max_right R₁ 1) hr)
    calc
      R₁ ≤ r := hR1_le
      _ ≤ 2 * r := by nlinarith
  have hRpos : 0 < 2 * r := by
    have : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right R₁ 1) hr)
    linarith
  -- Apply Jensen zero-counting at radius `R = 2r`.
  have hdiv_bound :
      (({u : ℂ |
            u ∈ (MeromorphicOn.divisor f (closedBall (0 : ℂ) |(2 * r)|)).support ∧
              ‖u‖ ≤ (2 * r) / 2} : Set ℂ).ncard : ℝ)
        ≤ (Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖) / Real.log 2 := by
    -- Use the unconditional Jensen bound.
    simpa using
      Hadamard.ZeroCounting.card_zeros_le_of_max_one_maxModulus (f := f) (R := (2 * r))
        (by exact hRpos) hf_entire hf0
  -- Relate the divisor-support counting set to `{ρ | ‖Z.z ρ‖ ≤ r}`
  -- via `h_zeros_only` and injectivity.
  have himage :
      (Z.z '' ({ρ : Z.Zero | ‖Z.z ρ‖ ≤ r} : Set Z.Zero)) =
        {u : ℂ | f u = 0 ∧ ‖u‖ ≤ r} := by
    ext u
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      refine ⟨Z.isZero ρ, ?_⟩
      simpa [Set.mem_ofPred_eq] using hρ
    · rintro ⟨hu0, hur⟩
      rcases (h_zeros_only u).1 hu0 with ⟨ρ, rfl⟩
      refine ⟨ρ, ?_, rfl⟩
      simpa [Set.mem_ofPred_eq] using hur
  -- Every zero `u` with `‖u‖ ≤ r` lies in the divisor-support counting set for radius `2r`.
  have hzeros_subset :
      {u : ℂ | f u = 0 ∧ ‖u‖ ≤ r}
        ⊆ {u : ℂ |
            u ∈ (MeromorphicOn.divisor f (closedBall (0 : ℂ) |(2 * r)|)).support ∧
              ‖u‖ ≤ (2 * r) / 2} := by
    intro u hu
    have hu0' : f u = 0 := hu.1
    have hur : ‖u‖ ≤ r := hu.2
    have hu_mem : u ∈ closedBall (0 : ℂ) |(2 * r)| := by
      have : ‖u‖ ≤ 2 * r := le_trans hur (by linarith)
      -- `‖u‖ ≤ 2r` implies membership in the closed ball.
      simpa [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hRpos] using this
    -- Use `h_simple` via the `ZeroSet` witness.
    rcases (h_zeros_only u).1 hu0' with ⟨ρ, rfl⟩
    refine ⟨?_, ?_⟩
    · exact mem_divisor_support_of_simple_zero hf_entire hRpos hu_mem (Z.isZero ρ) (h_simple ρ)
    · simpa using hur
  have hfinite_div :
      ({u : ℂ |
            u ∈ (MeromorphicOn.divisor f (closedBall (0 : ℂ) |(2 * r)|)).support ∧
              ‖u‖ ≤ (2 * r) / 2} : Set ℂ).Finite := by
    -- Support of the divisor on a compact set is finite.
    have hD :
        ((MeromorphicOn.divisor f (closedBall (0 : ℂ) |(2 * r)|)).support : Set ℂ).Finite :=
      (MeromorphicOn.divisor f (closedBall (0 : ℂ) |(2 * r)|)).finiteSupport
        (isCompact_closedBall (0 : ℂ) |(2 * r)|)
    exact hD.subset (by intro u hu; exact hu.1)
  have hcard_zeros_le :
      (({u : ℂ | f u = 0 ∧ ‖u‖ ≤ r} : Set ℂ).ncard : ℝ)
        ≤ (({u : ℂ |
              u ∈ (MeromorphicOn.divisor f (closedBall (0 : ℂ) |(2 * r)|)).support ∧
                ‖u‖ ≤ (2 * r) / 2} : Set ℂ).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hzeros_subset hfinite_div
  have hcardZ :
      (({ρ : Z.Zero | ‖Z.z ρ‖ ≤ r} : Set Z.Zero).ncard : ℝ)
        = (({u : ℂ | f u = 0 ∧ ‖u‖ ≤ r} : Set ℂ).ncard : ℝ) := by
    -- `Z.z` is injective and identifies the two sets.
    have h :=
      Set.ncard_image_of_injective ({ρ : Z.Zero | ‖Z.z ρ‖ ≤ r} : Set Z.Zero) h_inj
    -- `h : (Z.z '' S).ncard = S.ncard`.
    -- Rewrite using `himage` and cast to `ℝ`.
    have : (({ρ : Z.Zero | ‖Z.z ρ‖ ≤ r} : Set Z.Zero).ncard : ℝ)
        = ((Z.z '' ({ρ : Z.Zero | ‖Z.z ρ‖ ≤ r} : Set Z.Zero)).ncard : ℝ) := by
      exact_mod_cast h.symm
    simpa [himage] using this
  -- Combine.
  have hbound1 :
      (({ρ : Z.Zero | ‖Z.z ρ‖ ≤ r} : Set Z.Zero).ncard : ℝ)
        ≤ (Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖) / Real.log 2 := by
    -- Use the chain: Z-card = zero-card ≤ divisor-card ≤ Jensen bound.
    have := le_trans (le_trans (le_of_eq hcardZ) hcard_zeros_le) hdiv_bound
    exact this
  -- Replace `log (max 1 (maxModulus f (2r)))` using the max-modulus growth bound.
  have hM_le : maxModulus f (2 * r) ≤ Real.exp ((2 * r) ^ ((1 : ℝ) + ε)) :=
    hmax (2 * r) hr_ge_R1
  have hexp_ge1 : (1 : ℝ) ≤ Real.exp ((2 * r) ^ ((1 : ℝ) + ε)) := by
    have : 0 ≤ (2 * r) ^ ((1 : ℝ) + ε) := Real.rpow_nonneg (le_of_lt hRpos) _
    simpa using Real.one_le_exp this
  have hmax1_le : max 1 (maxModulus f (2 * r)) ≤ Real.exp ((2 * r) ^ ((1 : ℝ) + ε)) :=
    max_le hexp_ge1 hM_le
  have hlog_le : Real.log (max 1 (maxModulus f (2 * r))) ≤ (2 * r) ^ ((1 : ℝ) + ε) := by
    have hpos : 0 < max 1 (maxModulus f (2 * r)) := by
      have : (0 : ℝ) < (1 : ℝ) := by norm_num
      exact lt_of_lt_of_le this (le_max_left _ _)
    have := Real.log_le_log hpos hmax1_le
    simpa [Real.log_exp] using this
  have hnum :
      Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖
        ≤ (2 * r) ^ ((1 : ℝ) + ε) - Real.log ‖f 0‖ :=
    sub_le_sub_right hlog_le _
  have hden : 0 ≤ Real.log 2 := by
    exact le_of_lt (by simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hfrac :
      (Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖) / Real.log 2
        ≤ ((2 * r) ^ ((1 : ℝ) + ε) - Real.log ‖f 0‖) / Real.log 2 :=
    div_le_div_of_nonneg_right hnum hden
  exact le_trans hbound1 hfrac

/-- Multiplicity-weighted zero counting for a `ZeroSet` enumeration, in the order-`≤ 1` regime.

This bounds `∑ ord_ρ(f)` over zeros `ρ` with `‖Z.z ρ‖ ≤ r`, where `ord_ρ(f)` is the vanishing order
(`analyticOrderNatAt f (Z.z ρ)`). -/
theorem sum_multiplicity_zeros_le_of_order_le_one
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f) (hf_order_le : order f ≤ 1)
    (Z : ZeroSet f) [Countable Z.Zero]
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r →
        (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0) ≤
          ((2 * r) ^ ((1 : ℝ) + ε) - Real.log ‖f 0‖) / Real.log 2 := by
  classical
  intro ε hε
  -- `f 0 ≠ 0` since all zeros are nonzero and `Z` enumerates all zeros.
  have hf0 : f 0 ≠ 0 := by
    intro hf0
    rcases (h_zeros_only 0).1 hf0 with ⟨ρ, hρ⟩
    exact (h_z_ne_zero ρ) (by simp [hρ])
  -- Growth bound on `maxModulus f R` from `order f ≤ 1`.
  obtain ⟨R₁, hmax⟩ :=
    Hadamard.ZeroCounting.maxModulus_le_exp_rpow_of_order_le_one f hf_finite hf_order_le ε hε
  refine ⟨max R₁ 1, ?_⟩
  intro r hr
  have hr_ge_R1 : R₁ ≤ 2 * r := by
    have hR1_le : R₁ ≤ r := le_trans (le_max_left _ _) hr
    have hr_pos : 0 < r :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans (le_max_right R₁ 1) hr)
    calc
      R₁ ≤ r := hR1_le
      _ ≤ 2 * r := by nlinarith
  have hRpos : 0 < 2 * r := by
    have : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right R₁ 1) hr)
    linarith
  -- Jensen bound on the sum of divisor weights in `‖u‖ ≤ r` for the divisor on `‖u‖ ≤ 2r`.
  have hdiv_bound :
      (∑ᶠ u : ℂ,
          if ‖u‖ ≤ r then
            ((MeromorphicOn.divisor f (closedBall (0 : ℂ) |(2 * r)|) u : ℤ) : ℝ)
          else 0)
        ≤ (Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖) / Real.log 2 := by
    -- Use the unconditional Jensen bound with multiplicities.
    simpa using
      Hadamard.ZeroCounting.sum_zeros_multiplicity_le_of_max_one_maxModulus (f := f)
        (R := (2 * r)) (by exact hRpos) hf_entire hf0
  -- Compare the multiplicity sum over `Z.Zero` to the divisor-weight sum over `ℂ`.
  have hbound1 :
      (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0)
        ≤ (Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖) / Real.log 2 := by
    -- Work with the divisor on the ball of radius `2r`.
    let U : Set ℂ := closedBall (0 : ℂ) |(2 * r)|
    let D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
    have hmer : MeromorphicOn f U := fun z _ => (hf_entire.analyticAt z).meromorphicAt
    have hD_fin : (D.support : Set ℂ).Finite :=
      D.finiteSupport (isCompact_closedBall (0 : ℂ) |(2 * r)|)
    have hD_nonneg : 0 ≤ D := by
      have hf_an : AnalyticOnNhd ℂ f U := by
        intro z _
        exact hf_entire.analyticAt z
      exact hf_an.divisor_nonneg
    let Sρ : Set Z.Zero := {ρ : Z.Zero | ‖Z.z ρ‖ ≤ r}
    -- Image of `Sρ` lies in the divisor support.
    have hImage : Z.z '' Sρ ⊆ D.support := by
      intro u hu
      rcases hu with ⟨ρ, hρ, rfl⟩
      have hu_mem : Z.z ρ ∈ U := by
        have : ‖Z.z ρ‖ ≤ 2 * r :=
          le_trans (by simpa [Sρ, Set.mem_ofPred_eq] using hρ) (by linarith)
        simpa [U, Metric.mem_closedBall, dist_eq_norm, abs_of_pos hRpos] using this
      -- A zero contributes positively to the divisor support.
      have : Z.z ρ ∈ (MeromorphicOn.divisor f U).support :=
        mem_divisor_support_of_zero
          (f := f) hf_entire (R := (2 * r)) (u := Z.z ρ) hu_mem hf0 (Z.isZero ρ)
      simpa [D, U] using this
    have hImageFinite : (Z.z '' Sρ).Finite := hD_fin.subset hImage
    have hSρ_fin : Sρ.Finite := Set.Finite.of_finite_image hImageFinite (h_inj.injOn)
    let sZ : Finset Z.Zero := hSρ_fin.toFinset
    let sU : Finset ℂ := sZ.image Z.z
    -- Rewrite the LHS finsum as a finite sum over `sZ`.
    have hLHS :
        (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0)
          = ∑ ρ ∈ sZ, (analyticOrderNatAt f (Z.z ρ) : ℝ) := by
      have hsupp :
          Function.support (fun ρ : Z.Zero =>
              if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0) ⊆ sZ := by
        intro ρ hρ
        have hne :
            (if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0) ≠ 0 :=
          Function.mem_support.1 hρ
        have hle : ‖Z.z ρ‖ ≤ r := by
          by_contra hle
          apply hne
          simp [hle]
        have : ρ ∈ Sρ := by
          simpa [Sρ, Set.mem_ofPred_eq] using hle
        exact hSρ_fin.mem_toFinset.2 this
      have :=
        (finsum_eq_sum_of_support_subset
          (f := fun ρ : Z.Zero =>
            if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0)
          (s := sZ) hsupp)
      have hsum_if :
          (∑ ρ ∈ sZ, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0) =
            ∑ ρ ∈ sZ, (analyticOrderNatAt f (Z.z ρ) : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro ρ hρ
        have hρS : ρ ∈ Sρ := hSρ_fin.mem_toFinset.1 hρ
        have hle : ‖Z.z ρ‖ ≤ r := by simpa [Sρ, Set.mem_ofPred_eq] using hρS
        simp [hle]
      simpa [hsum_if] using this
    -- Move the sum from `Z.Zero` to its image in `ℂ`.
    have hsum_image :
        (∑ ρ ∈ sZ, (analyticOrderNatAt f (Z.z ρ) : ℝ))
          = ∑ u ∈ sU, (analyticOrderNatAt f u : ℝ) := by
      -- `sU` is the image of `sZ` under the injective map `Z.z`.
      have hinjOn : Set.InjOn Z.z (sZ : Set Z.Zero) := h_inj.injOn
      -- `Finset.sum_image` rewrites the sum over the image.
      simpa [sU] using
        (Finset.sum_image (f := fun u : ℂ => (analyticOrderNatAt f u : ℝ))
          (s := sZ) (g := Z.z) hinjOn).symm
    -- Replace `analyticOrderNatAt` by the divisor values on `sU`.
    have hsum_divisor :
        (∑ u ∈ sU, (analyticOrderNatAt f u : ℝ))
          = ∑ u ∈ sU, (D u : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro u hu
      -- `u` lies in the closed ball `U`.
      have huU : u ∈ U := by
        rcases Finset.mem_image.1 hu with ⟨ρ, hρ, rfl⟩
        have hρS : ρ ∈ Sρ := hSρ_fin.mem_toFinset.1 hρ
        have hle : ‖Z.z ρ‖ ≤ r := by simpa [Sρ, Set.mem_ofPred_eq] using hρS
        have : ‖Z.z ρ‖ ≤ 2 * r := le_trans hle (by linarith)
        simpa [U, Metric.mem_closedBall, dist_eq_norm, abs_of_pos hRpos] using this
      -- Analytic order is finite throughout `U` since `f 0 ≠ 0`.
      have hf_anU : AnalyticOnNhd ℂ f U := by
        intro z _
        exact hf_entire.analyticAt z
      have h0U : (0 : ℂ) ∈ U := by
        simp [U, Metric.mem_closedBall]
      have hpreU : IsPreconnected U := (convex_closedBall (0 : ℂ) |(2 * r)|).isPreconnected
      have horder0 : analyticOrderAt f 0 = 0 :=
        (hf_entire.analyticAt 0).analyticOrderAt_eq_zero.2 hf0
      have horder0_ne_top : analyticOrderAt f 0 ≠ ⊤ := by simp [horder0]
      have horder_ne_top : analyticOrderAt f u ≠ ⊤ :=
        hf_anU.analyticOrderAt_ne_top_of_isPreconnected hpreU h0U huU horder0_ne_top
      -- Compute the divisor value at `u`.
      have hDu :
          MeromorphicOn.divisor f U u = (analyticOrderNatAt f u : ℤ) := by
        have han_u : AnalyticAt ℂ f u := hf_entire.analyticAt u
        have hdiv_apply :
            MeromorphicOn.divisor f U u = (meromorphicOrderAt f u).untop₀ :=
          MeromorphicOn.divisor_apply hmer huU
        have hmerOrder_u : meromorphicOrderAt f u = (analyticOrderAt f u).map (↑) :=
          han_u.meromorphicOrderAt_eq
        obtain ⟨n, hn : (n : ℕ∞) = analyticOrderAt f u⟩ := ENat.ne_top_iff_exists.mp horder_ne_top
        have hnNat : analyticOrderNatAt f u = n := by
          simp [analyticOrderNatAt, hn.symm]
        have : MeromorphicOn.divisor f U u = (n : ℤ) := by
          rw [hdiv_apply, hmerOrder_u, hn.symm]
          simp
        rw [hnNat]
        exact this
      -- Coerce to `ℝ`.
      have : (analyticOrderNatAt f u : ℝ) = (D u : ℝ) := by
        -- `D` is definitionally the divisor on `U`.
        -- Use `hDu` and cast to `ℝ`.
        have hDu' : D u = (analyticOrderNatAt f u : ℤ) := by simpa [D] using hDu
        -- Coerce and rewrite.
        exact_mod_cast hDu'.symm
      exact this
    -- `sU` is a subset of the divisor-support ball set,
    -- so its sum is bounded by the divisor finsum.
    let Su : Set ℂ := {u : ℂ | u ∈ D.support ∧ ‖u‖ ≤ r}
    have hSu_fin : Su.Finite := by
      refine hD_fin.subset ?_
      intro u hu
      exact hu.1
    let sSu : Finset ℂ := hSu_fin.toFinset
    have hsU_sub : sU ⊆ sSu := by
      intro u hu
      rcases Finset.mem_image.1 hu with ⟨ρ, hρ, rfl⟩
      have hρS : ρ ∈ Sρ := hSρ_fin.mem_toFinset.1 hρ
      have hle : ‖Z.z ρ‖ ≤ r := by simpa [Sρ, Set.mem_ofPred_eq] using hρS
      have hz_support : Z.z ρ ∈ D.support := by
        have hz_mem : Z.z ρ ∈ U := by
          have : ‖Z.z ρ‖ ≤ 2 * r := le_trans hle (by linarith)
          simpa [U, Metric.mem_closedBall, dist_eq_norm, abs_of_pos hRpos] using this
        have : Z.z ρ ∈ (MeromorphicOn.divisor f U).support :=
          mem_divisor_support_of_zero
            (f := f) hf_entire (R := (2 * r)) (u := Z.z ρ) hz_mem hf0 (Z.isZero ρ)
        simpa [D, U] using this
      have : (Z.z ρ) ∈ Su := ⟨hz_support, hle⟩
      exact hSu_fin.mem_toFinset.2 this
    have hSu_nonneg : ∀ u ∈ sSu, u ∉ sU → 0 ≤ (D u : ℝ) := by
      intro u hu _
      have hDu0 : (0 : ℤ) ≤ D u := hD_nonneg u
      exact_mod_cast hDu0
    have hsum_le :
        (∑ u ∈ sU, (D u : ℝ)) ≤ ∑ u ∈ sSu, (D u : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsU_sub hSu_nonneg
    have hsumSu_eq :
        (∑ᶠ u : ℂ, if ‖u‖ ≤ r then ((D u : ℤ) : ℝ) else 0) = ∑ u ∈ sSu, (D u : ℝ) := by
      have hsupp :
          Function.support (fun u : ℂ => if ‖u‖ ≤ r then ((D u : ℤ) : ℝ) else 0) ⊆ sSu := by
        intro u hu
        have hne : (if ‖u‖ ≤ r then ((D u : ℤ) : ℝ) else 0) ≠ 0 :=
          Function.mem_support.1 hu
        have hle : ‖u‖ ≤ r := by
          by_contra hle
          apply hne
          simp [hle]
        have hDu : D u ≠ 0 := by
          intro hDu0
          apply hne
          simp [hle, hDu0]
        have huS : u ∈ Su := by
          refine ⟨?_, hle⟩
          have : u ∈ Function.support (fun x : ℂ => D x) := Function.mem_support.2 hDu
          simpa [Function.locallyFinsuppWithin.support] using this
        exact hSu_fin.mem_toFinset.2 huS
      have :=
        (finsum_eq_sum_of_support_subset
          (f := fun u : ℂ => if ‖u‖ ≤ r then ((D u : ℤ) : ℝ) else 0)
          (s := sSu) hsupp)
      have hsum_if :
          (∑ u ∈ sSu, if ‖u‖ ≤ r then ((D u : ℤ) : ℝ) else 0) = ∑ u ∈ sSu, (D u : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro u hu
        have huS : u ∈ Su := hSu_fin.mem_toFinset.1 hu
        have hle : ‖u‖ ≤ r := huS.2
        simp [hle]
      simpa [hsum_if] using this
    -- Finish the comparison.
    have hcompare :
        (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0)
          ≤ (∑ᶠ u : ℂ, if ‖u‖ ≤ r then ((MeromorphicOn.divisor f U u : ℤ) : ℝ) else 0) := by
      -- Rewrite LHS, then compare sums over `sU` and `sSu`, then rewrite RHS.
      have hRHS : (∑ᶠ u : ℂ, if ‖u‖ ≤ r then ((MeromorphicOn.divisor f U u : ℤ) : ℝ) else 0) =
          (∑ᶠ u : ℂ, if ‖u‖ ≤ r then ((D u : ℤ) : ℝ) else 0) := by
        rfl
      calc
        (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0)
            = ∑ ρ ∈ sZ, (analyticOrderNatAt f (Z.z ρ) : ℝ) := hLHS
        _ = ∑ u ∈ sU, (analyticOrderNatAt f u : ℝ) := by simp [hsum_image]
        _ = ∑ u ∈ sU, (D u : ℝ) := hsum_divisor
        _ ≤ ∑ u ∈ sSu, (D u : ℝ) := hsum_le
        _ = (∑ᶠ u : ℂ, if ‖u‖ ≤ r then ((D u : ℤ) : ℝ) else 0) := by simp [hsumSu_eq]
        _ = (∑ᶠ u : ℂ, if ‖u‖ ≤ r then ((MeromorphicOn.divisor f U u : ℤ) : ℝ) else 0) := by rfl
    -- Combine with Jensen.
    have hdiv_bound' :
        (∑ᶠ u : ℂ, if ‖u‖ ≤ r then ((MeromorphicOn.divisor f U u : ℤ) : ℝ) else 0) ≤
          (Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖) / Real.log 2 := by
      simpa [U] using hdiv_bound
    exact le_trans hcompare hdiv_bound'
  -- Replace `log (max 1 (maxModulus f (2r)))` using the max-modulus growth bound.
  have hM_le : maxModulus f (2 * r) ≤ Real.exp ((2 * r) ^ ((1 : ℝ) + ε)) :=
    hmax (2 * r) hr_ge_R1
  have hexp_ge1 : (1 : ℝ) ≤ Real.exp ((2 * r) ^ ((1 : ℝ) + ε)) := by
    have : 0 ≤ (2 * r) ^ ((1 : ℝ) + ε) := Real.rpow_nonneg (le_of_lt hRpos) _
    simpa using Real.one_le_exp this
  have hmax1_le : max 1 (maxModulus f (2 * r)) ≤ Real.exp ((2 * r) ^ ((1 : ℝ) + ε)) :=
    max_le hexp_ge1 hM_le
  have hlog_le : Real.log (max 1 (maxModulus f (2 * r))) ≤ (2 * r) ^ ((1 : ℝ) + ε) := by
    have hpos : 0 < max 1 (maxModulus f (2 * r)) := by
      have : (0 : ℝ) < (1 : ℝ) := by norm_num
      exact lt_of_lt_of_le this (le_max_left _ _)
    have := Real.log_le_log hpos hmax1_le
    simpa [Real.log_exp] using this
  have hnum :
      Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖
        ≤ (2 * r) ^ ((1 : ℝ) + ε) - Real.log ‖f 0‖ :=
    sub_le_sub_right hlog_le _
  have hden : 0 ≤ Real.log 2 := by
    exact le_of_lt (by simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hfrac :
      (Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖) / Real.log 2
        ≤ ((2 * r) ^ ((1 : ℝ) + ε) - Real.log ‖f 0‖) / Real.log 2 :=
    div_le_div_of_nonneg_right hnum hden
  exact le_trans hbound1 hfrac

/-- **General-order multiplicity-weighted zero counting.**

This is the `order f ≤ lam` analogue of `sum_multiplicity_zeros_le_of_order_le_one`.
The proof is identical except we use the general max-modulus growth bound
`maxModulus_le_exp_rpow_of_order_le` instead of its order-1 specialization. -/
theorem sum_multiplicity_zeros_le_of_order_le
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f) {lam : ℝ} (hf_order_le : order f ≤ lam)
    (Z : ZeroSet f) [Countable Z.Zero]
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ R₀ : ℝ, ∀ r : ℝ, R₀ ≤ r →
        (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0) ≤
          ((2 * r) ^ (lam + ε) - Real.log ‖f 0‖) / Real.log 2 := by
  classical
  intro ε hε
  have hf0 : f 0 ≠ 0 := by
    intro hf0
    rcases (h_zeros_only 0).1 hf0 with ⟨ρ, hρ⟩
    exact (h_z_ne_zero ρ) (by simp [hρ])
  obtain ⟨R₁, hmax⟩ :=
    Hadamard.ZeroCounting.maxModulus_le_exp_rpow_of_order_le f hf_finite hf_order_le ε hε
  refine ⟨max R₁ 1, ?_⟩
  intro r hr
  have hr_ge_R1 : R₁ ≤ 2 * r := by
    have hR1_le : R₁ ≤ r := le_trans (le_max_left _ _) hr
    have hr_pos : 0 < r :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans (le_max_right R₁ 1) hr)
    calc
      R₁ ≤ r := hR1_le
      _ ≤ 2 * r := by nlinarith
  have hRpos : 0 < 2 * r := by
    have : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right R₁ 1) hr)
    linarith
  -- Jensen bound on the sum of divisor weights in `‖u‖ ≤ r` for the divisor on `‖u‖ ≤ 2r`.
  have hdiv_bound :
      (∑ᶠ u : ℂ,
          if ‖u‖ ≤ r then
            ((MeromorphicOn.divisor f (closedBall (0 : ℂ) |(2 * r)|) u : ℤ) : ℝ)
          else 0)
        ≤ (Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖) / Real.log 2 := by
    simpa using
      Hadamard.ZeroCounting.sum_zeros_multiplicity_le_of_max_one_maxModulus (f := f)
        (R := (2 * r)) (by exact hRpos) hf_entire hf0
  -- Compare the multiplicity sum over `Z.Zero` to the divisor-weight sum over `ℂ`.
  have hbound1 :
      (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0)
        ≤ (Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖) / Real.log 2 := by
    -- Same proof as in the `order ≤ 1` version; only the max-modulus bound changes.
    let U : Set ℂ := closedBall (0 : ℂ) |(2 * r)|
    let D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
    have hmer : MeromorphicOn f U := fun z _ => (hf_entire.analyticAt z).meromorphicAt
    have hD_fin : (D.support : Set ℂ).Finite :=
      D.finiteSupport (isCompact_closedBall (0 : ℂ) |(2 * r)|)
    have hD_nonneg : 0 ≤ D := by
      have hf_an : AnalyticOnNhd ℂ f U := by
        intro z _
        exact hf_entire.analyticAt z
      exact hf_an.divisor_nonneg
    let Sρ : Set Z.Zero := {ρ : Z.Zero | ‖Z.z ρ‖ ≤ r}
    have hImage : Z.z '' Sρ ⊆ D.support := by
      intro u hu
      rcases hu with ⟨ρ, hρ, rfl⟩
      have hu_mem : Z.z ρ ∈ U := by
        have : ‖Z.z ρ‖ ≤ 2 * r :=
          le_trans (by simpa [Sρ, Set.mem_ofPred_eq] using hρ) (by linarith)
        simpa [U, Metric.mem_closedBall, dist_eq_norm, abs_of_pos hRpos] using this
      have : Z.z ρ ∈ (MeromorphicOn.divisor f U).support :=
        mem_divisor_support_of_zero
          (f := f) hf_entire (R := (2 * r)) (u := Z.z ρ) hu_mem hf0 (Z.isZero ρ)
      simpa [D, U] using this
    have hImageFinite : (Z.z '' Sρ).Finite := hD_fin.subset hImage
    have hSρ_fin : Sρ.Finite := Set.Finite.of_finite_image hImageFinite (h_inj.injOn)
    let sZ : Finset Z.Zero := hSρ_fin.toFinset
    let sU : Finset ℂ := sZ.image Z.z
    have hLHS :
        (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0)
          = ∑ ρ ∈ sZ, (analyticOrderNatAt f (Z.z ρ) : ℝ) := by
      have hsupp :
          Function.support (fun ρ : Z.Zero =>
              if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0) ⊆ sZ := by
        intro ρ hρ
        have hne :
            (if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0) ≠ 0 :=
          Function.mem_support.1 hρ
        have hle : ‖Z.z ρ‖ ≤ r := by
          by_contra hle
          apply hne
          simp [hle]
        have : ρ ∈ Sρ := by
          simpa [Sρ, Set.mem_ofPred_eq] using hle
        exact hSρ_fin.mem_toFinset.2 this
      have :=
        (finsum_eq_sum_of_support_subset
          (f := fun ρ : Z.Zero =>
            if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0)
          (s := sZ) hsupp)
      have hsum_if :
          (∑ ρ ∈ sZ, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0) =
            ∑ ρ ∈ sZ, (analyticOrderNatAt f (Z.z ρ) : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro ρ hρ
        have hρS : ρ ∈ Sρ := hSρ_fin.mem_toFinset.1 hρ
        have hle : ‖Z.z ρ‖ ≤ r := by simpa [Sρ, Set.mem_ofPred_eq] using hρS
        simp [hle]
      simpa [hsum_if] using this
    have hsum_image :
        (∑ ρ ∈ sZ, (analyticOrderNatAt f (Z.z ρ) : ℝ))
          = ∑ u ∈ sU, (analyticOrderNatAt f u : ℝ) := by
      have hinjOn : Set.InjOn Z.z (sZ : Set Z.Zero) := h_inj.injOn
      simpa [sU] using (Finset.sum_image (f := fun u : ℂ => (analyticOrderNatAt f u : ℝ))
        (s := sZ) (g := Z.z) hinjOn).symm
    have hsum_divisor :
        (∑ u ∈ sU, (analyticOrderNatAt f u : ℝ))
          = ∑ u ∈ sU, (D u : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro u hu
      have huU : u ∈ U := by
        rcases Finset.mem_image.1 hu with ⟨ρ, hρ, rfl⟩
        have hρS : ρ ∈ Sρ := hSρ_fin.mem_toFinset.1 hρ
        have hle : ‖Z.z ρ‖ ≤ r := by simpa [Sρ, Set.mem_ofPred_eq] using hρS
        have : ‖Z.z ρ‖ ≤ 2 * r := le_trans hle (by linarith)
        simpa [U, Metric.mem_closedBall, dist_eq_norm, abs_of_pos hRpos] using this
      have hf_anU : AnalyticOnNhd ℂ f U := by
        intro z _
        exact hf_entire.analyticAt z
      have h0U : (0 : ℂ) ∈ U := by
        simp [U, Metric.mem_closedBall]
      have hpreU : IsPreconnected U := (convex_closedBall (0 : ℂ) |(2 * r)|).isPreconnected
      have horder0 : analyticOrderAt f 0 = 0 :=
        (hf_entire.analyticAt 0).analyticOrderAt_eq_zero.2 hf0
      have horder0_ne_top : analyticOrderAt f 0 ≠ ⊤ := by simp [horder0]
      have horder_ne_top : analyticOrderAt f u ≠ ⊤ :=
        hf_anU.analyticOrderAt_ne_top_of_isPreconnected hpreU h0U huU horder0_ne_top
      have hDu :
          MeromorphicOn.divisor f U u = (analyticOrderNatAt f u : ℤ) := by
        have han_u : AnalyticAt ℂ f u := hf_entire.analyticAt u
        have hdiv_apply :
            MeromorphicOn.divisor f U u = (meromorphicOrderAt f u).untop₀ :=
          MeromorphicOn.divisor_apply hmer huU
        have hmerOrder_u : meromorphicOrderAt f u = (analyticOrderAt f u).map (↑) :=
          han_u.meromorphicOrderAt_eq
        obtain ⟨n, hn : (n : ℕ∞) = analyticOrderAt f u⟩ := ENat.ne_top_iff_exists.mp horder_ne_top
        have hnNat : analyticOrderNatAt f u = n := by
          simp [analyticOrderNatAt, hn.symm]
        have : MeromorphicOn.divisor f U u = (n : ℤ) := by
          rw [hdiv_apply, hmerOrder_u, hn.symm]
          simp
        rw [hnNat]
        exact this
      have : (analyticOrderNatAt f u : ℝ) = (D u : ℝ) := by
        have hDu' : D u = (analyticOrderNatAt f u : ℤ) := by simpa [D] using hDu
        exact_mod_cast hDu'.symm
      exact this
    let Su : Set ℂ := {u : ℂ | u ∈ D.support ∧ ‖u‖ ≤ r}
    have hSu_fin : Su.Finite := by
      refine hD_fin.subset ?_
      intro u hu
      exact hu.1
    let sSu : Finset ℂ := hSu_fin.toFinset
    have hsU_sub : sU ⊆ sSu := by
      intro u hu
      rcases Finset.mem_image.1 hu with ⟨ρ, hρ, rfl⟩
      have hρS : ρ ∈ Sρ := hSρ_fin.mem_toFinset.1 hρ
      have hle : ‖Z.z ρ‖ ≤ r := by simpa [Sρ, Set.mem_ofPred_eq] using hρS
      have hz_support : Z.z ρ ∈ D.support := by
        have hz_mem : Z.z ρ ∈ U := by
          have : ‖Z.z ρ‖ ≤ 2 * r := le_trans hle (by linarith)
          simpa [U, Metric.mem_closedBall, dist_eq_norm, abs_of_pos hRpos] using this
        have : Z.z ρ ∈ (MeromorphicOn.divisor f U).support :=
          mem_divisor_support_of_zero
            (f := f) hf_entire (R := (2 * r)) (u := Z.z ρ) hz_mem hf0 (Z.isZero ρ)
        simpa [D, U] using this
      have : (Z.z ρ) ∈ Su := ⟨hz_support, hle⟩
      exact hSu_fin.mem_toFinset.2 this
    have hSu_nonneg : ∀ u ∈ sSu, u ∉ sU → 0 ≤ (D u : ℝ) := by
      intro u hu _
      have hDu0 : (0 : ℤ) ≤ D u := hD_nonneg u
      exact_mod_cast hDu0
    have hsum_le :
        (∑ u ∈ sU, (D u : ℝ)) ≤ ∑ u ∈ sSu, (D u : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsU_sub hSu_nonneg
    have hsumSu_eq :
        (∑ᶠ u : ℂ, if ‖u‖ ≤ r then ((D u : ℤ) : ℝ) else 0) = ∑ u ∈ sSu, (D u : ℝ) := by
      have hsupp :
          Function.support (fun u : ℂ => if ‖u‖ ≤ r then ((D u : ℤ) : ℝ) else 0) ⊆ sSu := by
        intro u hu
        have hne : (if ‖u‖ ≤ r then ((D u : ℤ) : ℝ) else 0) ≠ 0 :=
          Function.mem_support.1 hu
        have hle : ‖u‖ ≤ r := by
          by_contra hle
          apply hne
          simp [hle]
        have hDu : D u ≠ 0 := by
          intro hDu0
          apply hne
          simp [hle, hDu0]
        have huS : u ∈ Su := by
          refine ⟨?_, hle⟩
          have : u ∈ Function.support (fun x : ℂ => D x) := Function.mem_support.2 hDu
          simpa [Function.locallyFinsuppWithin.support] using this
        exact hSu_fin.mem_toFinset.2 huS
      have :=
        (finsum_eq_sum_of_support_subset
          (f := fun u : ℂ => if ‖u‖ ≤ r then ((D u : ℤ) : ℝ) else 0)
          (s := sSu) hsupp)
      have hsum_if :
          (∑ u ∈ sSu, if ‖u‖ ≤ r then ((D u : ℤ) : ℝ) else 0) = ∑ u ∈ sSu, (D u : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro u hu
        have huS : u ∈ Su := hSu_fin.mem_toFinset.1 hu
        have hle : ‖u‖ ≤ r := huS.2
        simp [hle]
      simpa [hsum_if] using this
    have hcompare :
        (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0)
          ≤ (∑ᶠ u : ℂ, if ‖u‖ ≤ r then ((MeromorphicOn.divisor f U u : ℤ) : ℝ) else 0) := by
      calc
        (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0)
            = ∑ ρ ∈ sZ, (analyticOrderNatAt f (Z.z ρ) : ℝ) := hLHS
        _ = ∑ u ∈ sU, (analyticOrderNatAt f u : ℝ) := by simp [hsum_image]
        _ = ∑ u ∈ sU, (D u : ℝ) := hsum_divisor
        _ ≤ ∑ u ∈ sSu, (D u : ℝ) := hsum_le
        _ = (∑ᶠ u : ℂ, if ‖u‖ ≤ r then ((D u : ℤ) : ℝ) else 0) := by simp [hsumSu_eq]
        _ = (∑ᶠ u : ℂ, if ‖u‖ ≤ r then ((MeromorphicOn.divisor f U u : ℤ) : ℝ) else 0) := by rfl
    have hdiv_bound' :
        (∑ᶠ u : ℂ, if ‖u‖ ≤ r then ((MeromorphicOn.divisor f U u : ℤ) : ℝ) else 0) ≤
          (Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖) / Real.log 2 := by
      simpa [U] using hdiv_bound
    exact le_trans hcompare hdiv_bound'
  -- Replace `log (max 1 (maxModulus f (2r)))` using the max-modulus growth bound (general order).
  have hM_le : maxModulus f (2 * r) ≤ Real.exp ((2 * r) ^ (lam + ε)) :=
    hmax (2 * r) hr_ge_R1
  have hexp_ge1 : (1 : ℝ) ≤ Real.exp ((2 * r) ^ (lam + ε)) := by
    have : 0 ≤ (2 * r) ^ (lam + ε) := Real.rpow_nonneg (le_of_lt hRpos) _
    simpa using Real.one_le_exp this
  have hmax1_le : max 1 (maxModulus f (2 * r)) ≤ Real.exp ((2 * r) ^ (lam + ε)) :=
    max_le hexp_ge1 hM_le
  have hlog_le : Real.log (max 1 (maxModulus f (2 * r))) ≤ (2 * r) ^ (lam + ε) := by
    have hpos : 0 < max 1 (maxModulus f (2 * r)) := by
      have : (0 : ℝ) < (1 : ℝ) := by norm_num
      exact lt_of_lt_of_le this (le_max_left _ _)
    have := Real.log_le_log hpos hmax1_le
    simpa [Real.log_exp] using this
  have hnum :
      Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖
        ≤ (2 * r) ^ (lam + ε) - Real.log ‖f 0‖ :=
    sub_le_sub_right hlog_le _
  have hden : 0 ≤ Real.log 2 := by
    exact le_of_lt (by simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hfrac :
      (Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖) / Real.log 2
        ≤ ((2 * r) ^ (lam + ε) - Real.log ‖f 0‖) / Real.log 2 :=
    div_le_div_of_nonneg_right hnum hden
  exact le_trans hbound1 hfrac

end OrderOne

end Hadamard
