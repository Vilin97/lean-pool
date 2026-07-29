/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.FunctionalEquation
public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.GRH
public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.MellinAgreement

/-!
# Existence of the completed Dedekind zeta function  (SP1-AGE-4, ε)

The final assembly: the abstract completed function of the Hecke theta pair, evaluated on
the real ray (`heckeFEPair_Λ_real`), matches `heckeAdjust · completedZetaPrefactor · ζ_K`
there (`Λ_half_eq_prefactor_mul_zeta`) — the place Γ-product splits into the Deligne
factors and the `β = 4^{r₂}/|Δ|` normalisation regroups exactly into `|Δ|^{s/2}` and the
`2^{r₂}`-adjustment, as predicted. The identity theorem then extends the agreement to the
half-plane `Re s > 1`, producing `completedDedekindZeta` and the inhabitation theorem
`exists_isCompletedDedekindZeta` — the statement that makes the GRH predicate non-vacuous.
-/

namespace DedekindResidue

@[expose] public section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory
open Filter Asymptotics Topology
open scoped nonZeroDivisors Real ENNReal NNReal

variable (K : Type*) [Field K] [NumberField K]


open scoped Classical in
/-- The place Γ-product splits into real and complex contributions. -/
theorem prod_place_gamma (σ : ℝ) :
    (∏ w : InfinitePlace K, π ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ))
      = (π ^ (-σ) * Real.Gamma σ) ^ (nrRealPlaces K)
        * (π ^ (-(2 * σ)) * Real.Gamma (2 * σ)) ^ (nrComplexPlaces K) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype IsReal (fun w : InfinitePlace K =>
    π ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ))]
  congr 1
  · rw [show (π ^ (-σ) * Real.Gamma σ) ^ (nrRealPlaces K)
      = ∏ _w : {w : InfinitePlace K // IsReal w}, (π ^ (-σ) * Real.Gamma σ) by
      rw [Finset.prod_const, Finset.card_univ]]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [show (mult (w : InfinitePlace K) : ℝ) = 1 by
      rw [mult, if_pos w.2]
      norm_num]
    norm_num
  · rw [show (π ^ (-(2 * σ)) * Real.Gamma (2 * σ)) ^ (nrComplexPlaces K)
      = ∏ _w : {w : InfinitePlace K // ¬ IsReal w},
          (π ^ (-(2 * σ)) * Real.Gamma (2 * σ)) by
      rw [Finset.prod_const, Finset.card_univ]
      congr 1
      exact ((Fintype.card_congr (Equiv.subtypeEquivRight
        (fun w : InfinitePlace K => not_isReal_iff_isComplex))).trans rfl).symm]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [show (mult (w : InfinitePlace K) : ℝ) = 2 by
      rw [mult, if_neg w.2]
      norm_num]

open scoped Classical in
/-- `Γℝ` at a real argument is real. -/
theorem Gammaℝ_ofReal (s : ℝ) :
    Complex.Gammaℝ (s : ℂ) = ((π ^ (-(s/2)) * Real.Gamma (s / 2) : ℝ) : ℂ) := by
  rw [Complex.Gammaℝ_def]
  rw [show (-(s : ℂ) / 2) = (((-(s/2) : ℝ)) : ℂ) by push_cast; ring,
    show ((s : ℂ) / 2) = (((s/2 : ℝ)) : ℂ) by push_cast; ring]
  rw [Complex.Gamma_ofReal, ← Complex.ofReal_cpow Real.pi_pos.le, ← Complex.ofReal_mul]

open scoped Classical in
/-- `Γℂ` at a real argument is real. -/
theorem Gammaℂ_ofReal (s : ℝ) :
    Complex.Gammaℂ (s : ℂ) = ((2 * (2 * π) ^ (-s) * Real.Gamma s : ℝ) : ℂ) := by
  rw [Complex.Gammaℂ_def]
  rw [show (-(s : ℂ)) = (((-s : ℝ)) : ℂ) by push_cast; ring]
  rw [show ((2 : ℂ) * (π : ℂ)) = (((2 * π : ℝ)) : ℂ) by push_cast; ring]
  rw [Complex.Gamma_ofReal, ← Complex.ofReal_cpow (by positivity)]
  push_cast
  ring

open scoped Classical in
/-- **The final adjustment constant** `heckeJacobian·2^{-r₂}` — positive and
`s`-independent, absorbed into the definition of the completed zeta function. -/
noncomputable def heckeAdjust : ℝ :=
  ((heckeJacobian K : ℝ≥0) : ℝ) * ((2 : ℝ) ^ (nrComplexPlaces K))⁻¹

theorem heckeAdjust_pos : 0 < heckeAdjust K := by
  rw [heckeAdjust]
  have hJ : (0:ℝ) < ((heckeJacobian K : ℝ≥0) : ℝ) := by
    exact_mod_cast heckeJacobian_pos K
  positivity

open scoped Classical in
/-- **The agreement on the real ray (e-vii)**: for real `s > 1`,
`Λ(s/2) = heckeAdjust · (prefactor · ζ_K)(s)`. -/
theorem Λ_half_eq_prefactor_mul_zeta {s : ℝ} (hs : 1 < s) :
    (heckeFEPair K).Λ (((s / 2 : ℝ)) : ℂ)
      = ((heckeAdjust K : ℝ) : ℂ)
        * (completedZetaPrefactor K (s : ℂ) * dedekindZeta K (s : ℂ)) := by
  have hσ : (1:ℝ)/2 < s/2 := by linarith
  rw [heckeFEPair_Λ_real K hσ]
  rw [dedekindZeta_real_eq K hs]
  -- prefactor at real s, ofReal-ified
  have hD : (|discr K| : ℝ) = (((discr K).natAbs : ℕ) : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  have hDpos := natAbs_discr_pos K
  have hpre : completedZetaPrefactor K (s : ℂ)
      = (((((discr K).natAbs : ℕ) : ℝ) ^ ((s:ℝ)/2)
          * ((π ^ (-(s/2)) * Real.Gamma (s / 2)) ^ (nrRealPlaces K)
            * (2 * (2 * π) ^ (-s) * Real.Gamma s) ^ (nrComplexPlaces K)) : ℝ) : ℂ) := by
    rw [completedZetaPrefactor, gammaFactor]
    rw [show ((s : ℂ) / 2) = (((s/2 : ℝ)) : ℂ) by push_cast; ring]
    rw [show ((|discr K| : ℝ) : ℂ) = ((((discr K).natAbs : ℕ) : ℝ) : ℂ) by rw [hD]]
    rw [← Complex.ofReal_cpow (by positivity), Gammaℝ_ofReal, Gammaℂ_ofReal]
    push_cast
    ring
  rw [hpre]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  -- the real identity
  have h2s : 2 * (s/2) = s := by ring
  rw [prod_place_gamma K (s/2), h2s]
  have hβsplit : (heckeBeta K) ^ (-(s/2))
      = ((2:ℝ) ^ (-s)) ^ (nrComplexPlaces K)
        * (((discr K).natAbs : ℕ) : ℝ) ^ ((s:ℝ)/2) := by
    rw [heckeBeta, Real.div_rpow (by positivity) hDpos.le]
    rw [div_eq_mul_inv, ← Real.rpow_neg hDpos.le]
    congr 1
    · -- (4^{r₂})^{-(s/2)} = (2^{-s})^{r₂}
      rw [← Real.rpow_natCast (4:ℝ) (nrComplexPlaces K), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast ((2:ℝ) ^ (-s)) (nrComplexPlaces K),
        ← Real.rpow_mul (by norm_num)]
      rw [show (4:ℝ) = (2:ℝ) ^ ((2:ℕ):ℝ) by
        rw [Real.rpow_natCast]
        norm_num]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
    · ring_nf
  rw [hβsplit, heckeAdjust]
  have h2π : ((2 * π) ^ (-s)) = (2:ℝ) ^ (-s) * π ^ (-s) :=
    Real.mul_rpow (by norm_num) Real.pi_pos.le
  rw [h2π]
  rw [show (2 * ((2:ℝ) ^ (-s) * π ^ (-s)) * Real.Gamma s)
    = (2 * (π ^ (-s) * Real.Gamma s)) * (2:ℝ) ^ (-s) by ring_nf]
  rw [mul_pow (2 * (π ^ (-s) * Real.Gamma s)) ((2:ℝ) ^ (-s)) (nrComplexPlaces K)]
  rw [mul_pow (2:ℝ) (π ^ (-s) * Real.Gamma s) (nrComplexPlaces K)]
  field_simp

open scoped Classical in
/-- **The completed Dedekind zeta function**, constructed: the (constant-adjusted)
abstract completed function of the Hecke theta pair at `s/2`. Genuine on all of `ℂ`
(junk only at the poles `s = 0, 1`, as it must be). -/
noncomputable def completedDedekindZeta (s : ℂ) : ℂ :=
  ((heckeAdjust K : ℝ) : ℂ)⁻¹ * (heckeFEPair K).Λ (s / 2)

open scoped Classical in
/-- The entire extension of `s(s-1)·Λ_K(s)`, from the abstract `Λ₀`. -/
noncomputable def completedDedekindZetaEntire (s : ℂ) : ℂ :=
  ((heckeAdjust K : ℝ) : ℂ)⁻¹
    * (s * (s - 1) * (heckeFEPair K).Λ₀ (s / 2)
        - 2 * (s - 1) * (heckeFEPair K).f₀ + 2 * s * (heckeFEPair K).g₀)

open scoped Classical in
theorem differentiable_completedDedekindZetaEntire :
    Differentiable ℂ (completedDedekindZetaEntire K) := by
  refine Differentiable.const_mul ?_ _
  refine Differentiable.add ?_ ?_
  · refine Differentiable.sub ?_ ?_
    · refine Differentiable.mul (by fun_prop) ?_
      exact ((heckeFEPair K).differentiable_Λ₀).comp (by fun_prop)
    · fun_prop
  · fun_prop

open scoped Classical in
theorem completedDedekindZetaEntire_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedDedekindZetaEntire K s = s * (s - 1) * completedDedekindZeta K s := by
  rw [completedDedekindZetaEntire, completedDedekindZeta]
  have hΛ : (heckeFEPair K).Λ (s / 2)
      = (heckeFEPair K).Λ₀ (s / 2) - (1 / (s / 2)) • (heckeFEPair K).f₀
        - (((heckeFEPair K).ε / ((((heckeFEPair K).k : ℂ)) - s / 2))
            • (heckeFEPair K).g₀) := rfl
  rw [hΛ]
  have hε : (heckeFEPair K).ε = 1 := rfl
  have hk : ((heckeFEPair K).k : ℂ) = 1/2 := by
    rw [show (heckeFEPair K).k = 1/2 from rfl]
    push_cast
    ring
  rw [hε, hk]
  have hs2 : s / 2 ≠ 0 := by
    simpa using hs0
  have hks : (1/2 : ℂ) - s / 2 ≠ 0 := by
    intro h
    apply hs1
    linear_combination (-2 : ℂ) * h
  rw [smul_eq_mul, smul_eq_mul]
  field_simp
  ring

open scoped Classical in
/-- Agreement on the real ray, in the form used for the identity theorem. -/
theorem completedDedekindZeta_real {x : ℝ} (hx : 1 < x) :
    completedDedekindZeta K (x : ℂ)
      = completedZetaPrefactor K (x : ℂ) * dedekindZeta K (x : ℂ) := by
  rw [completedDedekindZeta]
  rw [show ((x : ℂ) / 2) = (((x / 2 : ℝ)) : ℂ) by push_cast; ring]
  rw [Λ_half_eq_prefactor_mul_zeta K hx, ← mul_assoc]
  rw [show (((heckeAdjust K : ℝ) : ℂ))⁻¹ * ((heckeAdjust K : ℝ) : ℂ) = 1 by
    rw [inv_mul_cancel₀]
    exact_mod_cast (heckeAdjust_pos K).ne']
  rw [one_mul]

open scoped Classical in
/-- **The agreement on the half-plane** `Re s > 1`, by the identity theorem from the real
ray. -/
theorem completedDedekindZeta_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta K s = completedZetaPrefactor K s * dedekindZeta K s := by
  have hUopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected {z : ℂ | 1 < z.re} :=
    (convex_halfSpace_re_gt 1).isPreconnected
  -- the left side is analytic on the half-plane
  have hF₁ : AnalyticOnNhd ℂ (completedDedekindZeta K) {z : ℂ | 1 < z.re} := by
    refine DifferentiableOn.analyticOnNhd ?_ hUopen
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.const_mul ?_ _
    have hz2 : z / 2 ≠ 0 := by
      intro h
      have : z = 0 := by linear_combination (2:ℂ) * h
      rw [this] at hz
      norm_num [Set.mem_setOf_eq] at hz
    have hzk : z / 2 ≠ (((heckeFEPair K).k : ℝ) : ℂ) := by
      intro h
      rw [show (heckeFEPair K).k = 1/2 from rfl] at h
      have : z = 1 := by
        push_cast at h
        linear_combination (2:ℂ) * h
      rw [this] at hz
      norm_num [Set.mem_setOf_eq] at hz
    have hd := (heckeFEPair K).differentiableAt_Λ (Or.inl hz2) (Or.inl hzk)
    have hhalf : DifferentiableAt ℂ (fun w : ℂ => w / 2) z := by fun_prop
    exact DifferentiableAt.comp (𝕜 := ℂ) (g := (heckeFEPair K).Λ)
      (f := fun w : ℂ => w / 2) z hd hhalf
  -- the right side is analytic on the half-plane
  have hcoef : (fun n : ℕ => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℕ) : ℂ))
      = (fun n : ℕ => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) := by
    funext n
    push_cast
    rfl
  have habs : LSeries.abscissaOfAbsConv
      (fun n : ℕ => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℕ) : ℂ)) ≤ 1 := by
    rw [hcoef]
    exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => count_LSeriesSummable K hy)
  have hζat : ∀ z : ℂ, z ∈ {z : ℂ | 1 < z.re} → DifferentiableAt ℂ (dedekindZeta K) z := by
    intro z hz
    have hz' : LSeries.abscissaOfAbsConv
        (fun n : ℕ => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℕ) : ℂ))
        < (z.re : EReal) := lt_of_le_of_lt habs (by exact_mod_cast hz)
    show DifferentiableAt ℂ (LSeries (fun n : ℕ =>
      ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℕ) : ℂ))) z
    exact (LSeries_hasDerivAt hz').differentiableAt
  have hF₂ : AnalyticOnNhd ℂ
      (fun z => completedZetaPrefactor K z * dedekindZeta K z) {z : ℂ | 1 < z.re} := by
    refine DifferentiableOn.analyticOnNhd ?_ hUopen
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.mul ?_ (hζat z hz)
    -- the prefactor
    have hzre : (0:ℝ) < z.re := lt_trans one_pos hz
    have hD0 : ((|discr K| : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      have := discr_ne_zero K
      positivity
    refine DifferentiableAt.mul ?_ ?_
    · exact (differentiableAt_id.div_const 2).const_cpow (Or.inl hD0)
    · -- the Gamma factor
      show DifferentiableAt ℂ (fun z => Complex.Gammaℝ z ^ (nrRealPlaces K)
        * Complex.Gammaℂ z ^ (nrComplexPlaces K)) z
      have hΓℝ : DifferentiableAt ℂ Complex.Gammaℝ z := by
        show DifferentiableAt ℂ (fun z => (π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) z
        refine DifferentiableAt.mul ?_ ?_
        · refine DifferentiableAt.const_cpow (by fun_prop) (Or.inl ?_)
          simp only [ne_eq, Complex.ofReal_eq_zero]
          exact Real.pi_ne_zero
        · refine DifferentiableAt.comp (𝕜 := ℂ) (g := Complex.Gamma)
            (f := fun w : ℂ => w / 2) z ?_ (by fun_prop)
          refine Complex.differentiableAt_Gamma _ (fun m => ?_)
          intro h
          have hz2 : z = (-(2 * (m : ℂ))) := by linear_combination (2:ℂ) * h
          rw [hz2] at hzre
          rw [show (-(2 * (m : ℂ))).re = -(2 * (m : ℝ)) by simp] at hzre
          nlinarith [Nat.cast_nonneg (α := ℝ) m]
      have hΓℂ : DifferentiableAt ℂ Complex.Gammaℂ z := by
        show DifferentiableAt ℂ (fun z => 2 * (2 * π : ℂ) ^ (-z) * Complex.Gamma z) z
        refine DifferentiableAt.mul ?_ ?_
        · refine DifferentiableAt.const_mul ?_ _
          refine DifferentiableAt.const_cpow (by fun_prop) (Or.inl ?_)
          refine mul_ne_zero two_ne_zero ?_
          simp only [ne_eq, Complex.ofReal_eq_zero]
          exact Real.pi_ne_zero
        · refine Complex.differentiableAt_Gamma _ (fun m => ?_)
          intro h
          rw [h] at hzre
          simp only [Complex.neg_re, Complex.natCast_re] at hzre
          have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
          linarith
      exact (hΓℝ.pow _).mul (hΓℂ.pow _)
  -- frequently-agreement at 2 along the real sequence 2 + 1/(n+1)
  have h2mem : (2:ℂ) ∈ {z : ℂ | 1 < z.re} := by
    norm_num [Set.mem_setOf_eq]
  have hfreq : ∃ᶠ z in nhdsWithin (2:ℂ) {(2:ℂ)}ᶜ,
      completedDedekindZeta K z = completedZetaPrefactor K z * dedekindZeta K z := by
    have htend : Filter.Tendsto (fun n : ℕ => (((2 + (1:ℝ)/(n+1) : ℝ)) : ℂ))
        Filter.atTop (nhdsWithin (2:ℂ) {(2:ℂ)}ᶜ) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hre : Filter.Tendsto (fun n : ℕ => (2 + (1:ℝ)/(n+1) : ℝ))
            Filter.atTop (𝓝 (2:ℝ)) := by
          have h0 : Filter.Tendsto (fun n : ℕ => (1:ℝ)/(n+1)) Filter.atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have := Filter.Tendsto.const_add (2:ℝ) h0
          simpa using this
        have hcomp := (Complex.continuous_ofReal.tendsto (2:ℝ)).comp hre
        refine hcomp.congr (fun n => rfl) |>.mono_right ?_
        rw [show ((2:ℝ) : ℂ) = (2:ℂ) by norm_cast]
      · refine Filter.Eventually.of_forall (fun n => ?_)
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        have hreal : (2 + (1:ℝ)/(n+1) : ℝ) = 2 := by exact_mod_cast h
        have hpos : (0:ℝ) < (1:ℝ)/(n+1) := by positivity
        linarith
    refine htend.frequently (Filter.Frequently.of_forall (fun n => ?_))
    have hgt : (1:ℝ) < 2 + (1:ℝ)/(n+1) := by
      have hpos : (0:ℝ) < (1:ℝ)/(n+1) := by positivity
      linarith
    exact completedDedekindZeta_real K hgt
  have hEq := hF₁.eqOn_of_preconnected_of_frequently_eq hF₂ hUconn h2mem hfreq
  exact hEq hs

open scoped Classical in
/-- **Hecke's theorem — the completed Dedekind zeta function exists** (the inhabitation of
the characterisation, making `GeneralizedRiemannHypothesis K` non-vacuous). -/
theorem exists_isCompletedDedekindZeta :
    ∃ Λ : ℂ → ℂ, IsCompletedDedekindZeta K Λ :=
  ⟨completedDedekindZeta K,
    fun _s hs => completedDedekindZeta_eq_of_one_lt_re K hs,
    completedDedekindZetaEntire K, differentiable_completedDedekindZetaEntire K,
    fun _s hs0 hs1 => completedDedekindZetaEntire_eq K hs0 hs1⟩

open scoped Classical in
/-- The constructed function satisfies the characterisation (the existence witness,
named). -/
theorem isCompletedDedekindZeta_completedDedekindZeta :
    IsCompletedDedekindZeta K (completedDedekindZeta K) :=
  ⟨fun _s hs => completedDedekindZeta_eq_of_one_lt_re K hs,
    completedDedekindZetaEntire K, differentiable_completedDedekindZetaEntire K,
    fun _s hs0 hs1 => completedDedekindZetaEntire_eq K hs0 hs1⟩

open scoped Classical in
/-- **GRH through the constructed completed zeta**: now that the characterisation is
inhabited (`exists_isCompletedDedekindZeta`) and unique off the poles
(`IsCompletedDedekindZeta.eqOn`), the abstract GRH quantification is equivalent to
nonvanishing of the concrete function `completedDedekindZeta`. -/
theorem generalizedRiemannHypothesis_iff :
    GeneralizedRiemannHypothesis K
      ↔ ∀ s : ℂ, 1/2 < s.re → s ≠ 1 → completedDedekindZeta K s ≠ 0 := by
  constructor
  · intro hGRH s hs hs1
    exact hGRH (completedDedekindZeta K)
      (isCompletedDedekindZeta_completedDedekindZeta K) s hs hs1
  · intro hconc Λ hΛ s hs hs1
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0] at hs
      norm_num [Complex.zero_re] at hs
    rw [hΛ.eqOn (isCompletedDedekindZeta_completedDedekindZeta K) hs0 hs1]
    exact hconc s hs hs1

/-- The Hecke pair is self-dual: `f = g`, `f₀ = g₀`, and `ε = 1` is its own inverse. -/
theorem heckeFEPair_symm : (heckeFEPair K).symm = heckeFEPair K := by
  unfold WeakFEPair.symm heckeFEPair
  simp only [inv_one]

/-- **The functional equation** `Λ_K(1-s) = Λ_K(s)` for the completed Dedekind zeta
function (AC-A0). -/
theorem completedDedekindZeta_one_sub (s : ℂ) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  have hfe := (heckeFEPair K).functional_equation (s/2)
  rw [heckeFEPair_symm] at hfe
  have hk : ((heckeFEPair K).k : ℂ) = 1/2 := by norm_num [heckeFEPair]
  have hε : (heckeFEPair K).ε = 1 := rfl
  rw [hk, hε, one_smul] at hfe
  rw [completedDedekindZeta, completedDedekindZeta,
    show (1 - s)/2 = (1/2 : ℂ) - s/2 by ring, hfe]
end

end DedekindResidue
