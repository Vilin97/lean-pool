/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Vendored.CoramMvRestrictedNorm
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Vendored.CoramRestrictedIso
import LeanPool.UniformSheafyTateDomains.AdicSpaces.ExampleUnitDisc

/-!
# Restricted power series over an arbitrary variable index: completeness and support API

The vendored Coram stack (`Vendored/CoramMvRestricted*.lean`) provides
`MvPowerSeries.Restricted R c` with its Gauss norm for an **arbitrary** index type `σ`,
but proves `CompleteSpace` only for `σ = Fin n` (`Vendored/CoramRestrictedIso.lean`,
`MvRestricted.isCompleteSpace`, by induction on `n`).  The weighted-parity example
([WP] §6.1, eq:parity-algebra) needs countably many variables, so this file supplies:

* `MvRestricted.isCompleteSpace_general` — completeness for arbitrary `σ`, by the
  coefficientwise-Cauchy argument of the univariate proof
  (`Vendored/CoramRestrictedNorm.lean:257`), which is index-uniform;
* `NormOneClass` at radius one for arbitrary `σ` (generalizing
  `FJP/RestrictedGaussAdic.lean:44`);
* the radius-one coefficient API (`norm_coeff_le`, continuity of coefficient
  functionals, finiteness of superlevel sets — generalizing
  `FJP/RestrictedGaussAdic.lean:199,207`);
* the closed-support principle: a coefficient-vanishing condition cuts out a closed
  subset (the pattern behind `FJP/RestrictedLaurent.lean:765` and
  `FJP/Over/JetRings.lean:298`).
-/

@[expose] public section

namespace WeightedParity

open MvPowerSeries Filter Topology

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {σ : Type*}

/-- Radius one is strongly positive, for every index type. -/
instance strongPos_one (σ : Type*) : StrongPos (fun _ : σ => (1 : ℝ)) :=
  strongPos_of_forall_pos _ fun _ => one_pos

/-- The radius-one Gauss weight of every exponent is `1`. -/
theorem prod_one_weights (t : σ →₀ ℕ) :
    (t.prod fun _ k => (1 : ℝ) ^ k) = 1 := by
  simp [Finsupp.prod]

section General

variable (c : σ → ℝ) [StrongPos c]

/-- The Gauss weights are positive. -/
theorem prod_weights_pos (t : σ →₀ ℕ) : (0 : ℝ) < t.prod (c · ^ ·) := by
  refine Finset.prod_pos fun i _ => ?_
  exact pow_pos (StrongPos_pos c i) _

/-- **Completeness of restricted power series for an arbitrary variable index.**
Generalizes `Restricted.isCompleteSpace` (univariate,
`Vendored/CoramRestrictedNorm.lean:257`) and `MvRestricted.isCompleteSpace`
(`Fin (n+1)`, `Vendored/CoramRestrictedIso.lean:349`): the coefficientwise-Cauchy
argument never uses the index type.  ([WP] §6.1: "Its completion is 𝒜 = {…}",
eq:parity-algebra — the ambient ring must be complete.) -/
instance isCompleteSpace_general [CompleteSpace R] :
    CompleteSpace (MvPowerSeries.Restricted R c) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hcw : ∀ t : σ →₀ ℕ, (0 : ℝ) < t.prod (c · ^ ·) := prod_weights_pos c
  -- Step 1: the Gauss norm bounds each weighted coefficient.
  have coeff_le : ∀ (f g : MvPowerSeries.Restricted R c) (t : σ →₀ ℕ),
      ‖MvPowerSeries.coeff t f.1 - MvPowerSeries.coeff t g.1‖ * t.prod (c · ^ ·) ≤
        ‖f - g‖ := fun f g t => by
    have heq : MvPowerSeries.coeff t f.1 - MvPowerSeries.coeff t g.1 =
        MvPowerSeries.coeff t (f - g).1 := by
      show _ = MvPowerSeries.coeff t (f.1 - g.1)
      exact (map_sub _ _ _).symm
    rw [heq]
    exact MvPowerSeries.le_gaussNorm norm c (f - g).1
      (MvRestricted.hasGaussNorm c (f - g)) t
  -- Step 2: each coefficient net is Cauchy in `R`.
  have coeff_cauchy : ∀ t : σ →₀ ℕ,
      CauchySeq (fun i => MvPowerSeries.coeff t (u i).1) := fun t => by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε * t.prod (c · ^ ·))
      (mul_pos hε (hcw t))
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm]
    have h_uij : ‖u i - u j‖ < ε * t.prod (c · ^ ·) := by
      have := hN i hi j hj; rwa [dist_eq_norm] at this
    exact lt_of_mul_lt_mul_right ((coeff_le (u i) (u j) t).trans_lt h_uij) (hcw t).le
  -- Step 3: pointwise limits assemble into a candidate series.
  choose a ha using fun t => cauchySeq_tendsto_of_complete (coeff_cauchy t)
  set f : MvPowerSeries σ R := fun t => a t with hf_def
  have coeff_f : ∀ t, MvPowerSeries.coeff t f = a t := fun t => rfl
  -- Step 4: convergence uniform in the exponent.
  have unif_conv : ∀ ε > (0 : ℝ), ∃ N, ∀ i ≥ N, ∀ t : σ →₀ ℕ,
      ‖MvPowerSeries.coeff t (u i).1 - a t‖ * t.prod (c · ^ ·) ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun i hi t => ?_⟩
    have h_lim : Tendsto
        (fun j => ‖MvPowerSeries.coeff t (u i).1 -
          MvPowerSeries.coeff t (u j).1‖ * t.prod (c · ^ ·))
        atTop (𝓝 (‖MvPowerSeries.coeff t (u i).1 - a t‖ * t.prod (c · ^ ·))) :=
      ((tendsto_const_nhds.sub (ha t)).norm).mul_const _
    refine le_of_tendsto h_lim ?_
    filter_upwards [Filter.eventually_ge_atTop N] with j hj
    have h_dist := hN i hi j hj
    rw [dist_eq_norm] at h_dist
    exact ((coeff_le (u i) (u j) t).trans_lt h_dist).le
  -- Step 5: the candidate is restricted (ultrametric comparison with one term).
  have hf : MvPowerSeries.IsRestrictedGauss c f := by
    show Tendsto (fun t : σ →₀ ℕ => ‖MvPowerSeries.coeff t f‖ * t.prod (c · ^ ·))
      cofinite (𝓝 0)
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := unif_conv (ε / 2) (by linarith)
    have h_uN1 : Tendsto
        (fun t : σ →₀ ℕ => ‖MvPowerSeries.coeff t (u N₁).1‖ * t.prod (c · ^ ·))
        cofinite (𝓝 0) := (u N₁).2
    rw [Metric.tendsto_nhds] at h_uN1
    have h_uN1' := h_uN1 (ε / 2) (by linarith)
    rw [Filter.eventually_cofinite] at h_uN1' ⊢
    refine h_uN1'.subset fun t hn => ?_
    simp only [Set.mem_setOf_eq, dist_zero_right, Real.norm_eq_abs, not_lt] at hn ⊢
    rw [coeff_f] at hn
    have hp1 : 0 ≤ ‖a t‖ * t.prod (c · ^ ·) := mul_nonneg (norm_nonneg _) (hcw t).le
    have hp2 : 0 ≤ ‖MvPowerSeries.coeff t (u N₁).1‖ * t.prod (c · ^ ·) :=
      mul_nonneg (norm_nonneg _) (hcw t).le
    rw [abs_of_nonneg hp1] at hn
    rw [abs_of_nonneg hp2]
    have h1 : ‖MvPowerSeries.coeff t (u N₁).1 - a t‖ * t.prod (c · ^ ·) ≤ ε / 2 :=
      hN₁ N₁ le_rfl t
    have h_ultra : ‖a t‖ ≤
        max ‖MvPowerSeries.coeff t (u N₁).1 - a t‖
          ‖MvPowerSeries.coeff t (u N₁).1‖ := by
      have h2 : ‖(a t - MvPowerSeries.coeff t (u N₁).1) +
          MvPowerSeries.coeff t (u N₁).1‖ ≤
          max ‖a t - MvPowerSeries.coeff t (u N₁).1‖
            ‖MvPowerSeries.coeff t (u N₁).1‖ :=
        IsUltrametricDist.norm_add_le_max _ _
      rw [sub_add_cancel] at h2
      rwa [norm_sub_rev] at h2
    have h_max_bd : ‖a t‖ * t.prod (c · ^ ·) ≤
        max (‖MvPowerSeries.coeff t (u N₁).1 - a t‖ * t.prod (c · ^ ·))
            (‖MvPowerSeries.coeff t (u N₁).1‖ * t.prod (c · ^ ·)) := by
      rw [← max_mul_of_nonneg _ _ (hcw t).le]
      exact mul_le_mul_of_nonneg_right h_ultra (hcw t).le
    rcases le_max_iff.mp h_max_bd with h | h
    · linarith
    · linarith
  -- Step 6: convergence in the Gauss norm.
  set z : MvPowerSeries.Restricted R c := ⟨f, hf⟩ with hz
  refine ⟨z, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := unif_conv (ε / 2) (by linarith)
  refine ⟨N, fun i hi => ?_⟩
  rw [dist_eq_norm]
  show MvPowerSeries.gaussNorm norm c (u i - z).1 < ε
  have hdiff : ∀ t, MvPowerSeries.coeff t (u i - z).1 =
      MvPowerSeries.coeff t (u i).1 - a t := fun t => by
    show MvPowerSeries.coeff t ((u i).1 - f) = _
    rw [map_sub, coeff_f]
  have hbd : ∀ t : σ →₀ ℕ, ‖MvPowerSeries.coeff t (u i - z).1‖ * t.prod (c · ^ ·) ≤
      ε / 2 := fun t => by
    rw [hdiff]; exact hN i hi t
  have h_gauss_le : MvPowerSeries.gaussNorm norm c (u i - z).1 ≤ ε / 2 := by
    rw [MvPowerSeries.gaussNorm]
    exact ciSup_le hbd
  linarith

end General

/-- `NormOneClass` at radius one, arbitrary index (generalizes the `Fin k` instance of
`FJP/RestrictedGaussAdic.lean:44`; the proof via `t.prod (1 ^ ·) = 1` is
index-uniform). -/
noncomputable instance normOneClass_one {S : Type*} [NormedCommRing S]
    [IsUltrametricDist S] [NormOneClass S] {σ' : Type*} :
    NormOneClass (MvPowerSeries.Restricted S (fun _ : σ' => (1 : ℝ))) := by
  classical
  refine ⟨?_⟩
  have h1 : ((1 : MvPowerSeries.Restricted S (fun _ : σ' => (1 : ℝ))).1 :
      MvPowerSeries σ' S) = 1 := rfl
  rw [MvRestricted.norm_eq]
  apply le_antisymm
  · rw [MvPowerSeries.gaussNorm]
    refine ciSup_le fun t => ?_
    rw [prod_one_weights, mul_one, h1]
    rcases eq_or_ne t 0 with rfl | ht
    · simp [MvPowerSeries.coeff_zero_one]
    · rw [MvPowerSeries.coeff_one, if_neg ht]
      simp
  · have h := MvPowerSeries.le_gaussNorm (norm : S → ℝ) (fun _ : σ' => (1 : ℝ))
      (1 : MvPowerSeries.Restricted S (fun _ : σ' => (1 : ℝ))).1
      (MvRestricted.hasGaussNorm _ 1) 0
    rw [prod_one_weights, mul_one, h1, MvPowerSeries.coeff_zero_one, norm_one] at h
    exact h

section RadiusOne

variable (f : MvPowerSeries.Restricted R (fun _ : σ => (1 : ℝ))) (t : σ →₀ ℕ)

/-- Coefficient bound at radius one (generalizes
`FiniteJet.GraphKoszul.norm_coeff_le_gauss`, `FJP/RestrictedGaussAdic.lean:199`). -/
theorem norm_coeff_le_one_norm : ‖MvPowerSeries.coeff t f.1‖ ≤ ‖f‖ := by
  have h := MvPowerSeries.le_gaussNorm (norm : R → ℝ) (fun _ : σ => (1 : ℝ)) f.1
    (MvRestricted.hasGaussNorm _ f) t
  rw [prod_one_weights, mul_one] at h
  exact h

/-- The coefficient functionals are `1`-Lipschitz, hence continuous (the pattern of
`FiniteJetOver.continuous_qCoeff`, `FJP/Over/JetRings.lean:112`). -/
theorem lipschitzWith_coeff :
    LipschitzWith 1 (fun g : MvPowerSeries.Restricted R (fun _ : σ => (1 : ℝ)) =>
      MvPowerSeries.coeff t g.1) := by
  refine lipschitzWith_iff_dist_le_mul.mpr fun g₁ g₂ => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have heq : MvPowerSeries.coeff t g₁.1 - MvPowerSeries.coeff t g₂.1 =
      MvPowerSeries.coeff t (g₁ - g₂).1 := by
    show _ = MvPowerSeries.coeff t (g₁.1 - g₂.1)
    exact (map_sub _ _ _).symm
  rw [heq]
  exact norm_coeff_le_one_norm (g₁ - g₂) t

theorem continuous_coeff :
    Continuous (fun g : MvPowerSeries.Restricted R (fun _ : σ => (1 : ℝ)) =>
      MvPowerSeries.coeff t g.1) :=
  (lipschitzWith_coeff t).continuous

/-- Superlevel sets of a restricted series are finite (generalizes
`FiniteJet.GraphKoszul.finite_setOf_le_norm_coeff`, `FJP/RestrictedGaussAdic.lean:207`).
This is the "every nonzero restricted series attains its norm" input of
[WP] prop:parity-uniform-domain. -/
theorem finite_setOf_le_norm_coeff {ε : ℝ} (hε : 0 < ε) :
    {s : σ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff s f.1‖}.Finite := by
  have hf : Tendsto (fun s : σ →₀ ℕ => ‖MvPowerSeries.coeff s f.1‖) cofinite
      (𝓝 0) := by
    have h2 : Tendsto (fun s : σ →₀ ℕ =>
        ‖MvPowerSeries.coeff s f.1‖ * s.prod ((fun _ : σ => (1 : ℝ)) · ^ ·))
        cofinite (𝓝 0) := f.2
    refine h2.congr fun s => ?_
    rw [prod_one_weights, mul_one]
  rw [Metric.tendsto_nhds] at hf
  have := hf ε hε
  rw [Filter.eventually_cofinite] at this
  refine this.subset fun s hs => ?_
  simp only [Set.mem_setOf_eq, dist_zero_right, Real.norm_eq_abs, not_lt] at hs ⊢
  rw [abs_of_nonneg (norm_nonneg _)]
  exact hs

/-- **The closed-support principle**: the set of restricted series whose coefficients
vanish outside a prescribed set of exponents is closed (each condition is the kernel of
a continuous coefficient functional; the pattern of
`FiniteJet.RestrictedLaurent.isClosed_nonnegSubring`,
`FJP/RestrictedLaurent.lean:765`). -/
theorem isClosed_setOf_coeff_eq_zero (S : Set (σ →₀ ℕ)) :
    IsClosed {g : MvPowerSeries.Restricted R (fun _ : σ => (1 : ℝ)) |
      ∀ s ∉ S, MvPowerSeries.coeff s g.1 = 0} := by
  have : {g : MvPowerSeries.Restricted R (fun _ : σ => (1 : ℝ)) |
      ∀ s ∉ S, MvPowerSeries.coeff s g.1 = 0} =
      ⋂ (s : σ →₀ ℕ) (_ : s ∉ S),
        {g : MvPowerSeries.Restricted R (fun _ : σ => (1 : ℝ)) |
          MvPowerSeries.coeff s g.1 = 0} := by
    ext g
    simp [Set.mem_iInter]
  rw [this]
  refine isClosed_iInter fun s => isClosed_iInter fun _ => ?_
  exact isClosed_eq (continuous_coeff s) continuous_const

end RadiusOne

/-- Gauss-norm multiplicativity of the radius-one restricted ring over a normed ring
with multiplicative norm, for a linearly ordered index ([WP]
prop:parity-uniform-domain: "The Gauss norm on the countable restricted Tate algebra
`k⟨W,U_1,U_2,…⟩` is multiplicative").  Wrapper around the vendored
`MvRestricted.isAbsoluteValue` (`Vendored/CoramMvRestrictedNorm.lean:270`). -/
theorem norm_restricted_mul_general [LinearOrder σ] {S : Type*} [NormedCommRing S]
    [IsUltrametricDist S] (hnorm : ∀ a b : S, ‖a * b‖ = ‖a‖ * ‖b‖)
    (f g : MvPowerSeries.Restricted S (fun _ : σ => (1 : ℝ))) :
    ‖f * g‖ = ‖f‖ * ‖g‖ := by
  have h := (MvRestricted.isAbsoluteValue (c := fun _ : σ => (1 : ℝ)) hnorm).abv_mul' f g
  rw [MvRestricted.norm_eq, MvRestricted.norm_eq, MvRestricted.norm_eq]
  exact h

end WeightedParity
