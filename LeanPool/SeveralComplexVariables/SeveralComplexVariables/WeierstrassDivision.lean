/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticGerm
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.WeierstrassDivision.Picard

/-!
# Analytic Weierstrass division

A divisor of finite order in the distinguished scalar coordinate admits a unique quotient and a
polynomial remainder. We normalize the divisor by a nonvanishing leading factor, make the
remaining perturbation small, and apply the Picard iteration. Uniqueness holds on smaller
neighborhoods and hence for germs. The uniform statement applies to bounded numerators on a
common polydisc; the local statement applies to arbitrary analytic numerators.

This module also exports the supporting theory:

* `WeierstrassDivision.Basic`: division predicates and elementary properties;
* `WeierstrassDivision.CoordinatePower`: Cauchy division by a coordinate power;
* `WeierstrassDivision.Picard`: contraction estimates, limits, and uniqueness.

Reference: [Jakóbczak–Jarnicki][JakobczakJarnicki2021], §1.7, Theorem 1.7.3. These analytic
statements do not follow just from Mathlib's formal, adic division theorem.

## Main results

* `exists_coordinatePower_leadingFactor_ne_zero`: **Coordinate-power normalization with a
  nonvanishing leading factor.** A holomorphic function of finite order `d` in the distinguished
  coordinate decomposes, on some initial polydisc-ball, as `f1 * z.2 ^ d` plus a Weierstrass
  remainder whose coefficients vanish at the parameter origin; moreover `f1` itself is nonzero
  throughout a (possibly smaller) polydisc-ball.
* `exists_perturbation_bound_of_coordinatePower_leadingFactor`: **A uniformly small perturbation of
  the coordinate power.** Given a coordinate-power decomposition `f = f1 * z.2 ^ d +
  weierstrassRemainder c` with `f1` nonvanishing on a polydisc-ball of radius `ε₁`, the perturbation
  `weierstrassRemainder c / f1` is analytic there and, on a smaller polydisc-ball, uniformly bounded
  by `R₂ ^ d / (2 * (d + 1))`: small enough for the Picard iteration against the divisor `z ^ d` to
  contract in `exists_isWeierstrassDivisionOn_of_bounded`.
* `exists_isWeierstrassDivisionOn_of_bounded`: **Weierstrass division
  ([Jakóbczak–Jarnicki][JakobczakJarnicki2021] 1.7.3).** A divisor whose central scalar slice has
  finite order `d` admits division of every bounded holomorphic numerator on a fixed polydisc.
* `exists_isWeierstrassDivisionAt_of_finiteDimensional`: **Weierstrass division for analytic germs
  on any finite-dimensional parameter space.** Obtained by transporting the coordinate version along
  a basis; no choice of coordinates occurs in the statement.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public noncomputable section

open Complex Filter Finset Metric Set
open scoped Real Topology

namespace SeveralComplexVariables

open WeierstrassDivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {ι : Type*} [Fintype ι]

/-- **Coordinate-power normalization with a nonvanishing leading factor.** A holomorphic
function of finite order `d` in the distinguished coordinate decomposes, on some initial
polydisc-ball, as `f1 * z.2 ^ d` plus a Weierstrass remainder whose coefficients vanish at
the parameter origin; moreover `f1` itself is nonzero throughout a (possibly smaller)
polydisc-ball. This supplies the normalization in `exists_isWeierstrassDivisionOn_of_bounded`. -/
theorem exists_coordinatePower_leadingFactor_ne_zero {d : ℕ} {f : (ι → ℂ) × ℂ → ℂ}
    {U : Set ((ι → ℂ) × ℂ)} (hU : IsOpen U) (h0 : 0 ∈ U) (hf : DifferentiableOn ℂ f U)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    ∃ (f1 : (ι → ℂ) × ℂ → ℂ) (c : Fin d → (ι → ℂ) → ℂ) (ε₀ ε₁ : ℝ), 0 < ε₀ ∧ 0 < ε₁ ∧
      polydisc (0 : ι → ℂ) (fun _ => ε₀) ×ˢ ball (0 : ℂ) ε₀ ⊆ U ∧
      IsWeierstrassDivisionOn (fun z => z.2 ^ d) f f1 c
        (polydisc (0 : ι → ℂ) (fun _ => ε₀)) ε₀ ∧
      (∀ j, c j 0 = 0) ∧
      polydisc (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁ ⊆
        polydisc (0 : ι → ℂ) (fun _ => ε₀) ×ˢ ball (0 : ℂ) ε₀ ∧
      ∀ z ∈ polydisc (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁, f1 z ≠ 0 := by
  obtain ⟨ε₀, hε₀, hε₀U⟩ := exists_polydisc_ball_subset hU h0
  have hf0 : DifferentiableOn ℂ f (polydisc (0 : ι → ℂ) (fun _ => ε₀) ×ˢ ball 0 ε₀) :=
    hf.mono hε₀U
  obtain ⟨f1, c, hfdiv, hf1bound, hf1uniq⟩ :=
    coordinatePower_division d hε₀ hf0
  have hz0V : (0 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) (fun _ => ε₀) :=
    mem_polydisc.mpr fun i => by simpa using hε₀
  have hforder : AnalyticAt ℂ (fun w : ℂ => f (0, w)) 0 :=
    (differentiableOn_snd_slice hf0 hz0V).analyticOnNhd_of_finiteDimensional isOpen_ball
      0 (mem_ball_self hε₀)
  have hcj0 : ∀ j : Fin d, c j 0 = 0 := by
    intro j
    rw [coeff_eq_iteratedDeriv_of_coordinatePower_division hfdiv hε₀ hz0V j]
    have hle : (d : ℕ∞) ≤ analyticOrderAt (fun w : ℂ => f (0, w)) 0 := horder.ge
    rw [(natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hforder).mp hle (j : ℕ) j.isLt]
    simp
  have hf1_eq : ∀ ζ ∈ ball (0 : ℂ) ε₀, f (0, ζ) = f1 (0, ζ) * ζ ^ d := by
    intro ζ hζ
    have := hfdiv.eq (Set.mk_mem_prod hz0V hζ)
    simpa [weierstrassRemainder, hcj0, mul_comm] using this
  have hf1A0 : AnalyticAt ℂ (fun ζ : ℂ => f1 (0, ζ)) 0 :=
    (differentiableOn_snd_slice hfdiv.differentiableOn_quotient
      hz0V).analyticOnNhd_of_finiteDimensional
      isOpen_ball 0 (mem_ball_self hε₀)
  have horder' : analyticOrderAt (fun ζ : ℂ => f1 (0, ζ) * ζ ^ d) 0 = d := by
    rw [← analyticOrderAt_congr (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds
      (mem_ball_self hε₀)) hf1_eq)]
    exact horder
  have hf1ord0 : analyticOrderAt (fun ζ : ℂ => f1 (0, ζ)) 0 = 0 := by
    have hpow : AnalyticAt ℂ (fun ζ : ℂ => ζ ^ d) 0 := analyticAt_id.pow d
    have hpow' : analyticOrderAt (fun ζ : ℂ => ζ ^ d) 0 = d := by
      have h := analyticOrderAt_pow (analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))) d
      simpa [analyticOrderAt_id, Pi.pow_def] using h
    have hmul : analyticOrderAt (fun ζ : ℂ => f1 (0, ζ) * ζ ^ d) 0 =
        analyticOrderAt (fun ζ : ℂ => f1 (0, ζ)) 0 + analyticOrderAt (fun ζ : ℂ => ζ ^ d) 0 :=
      analyticOrderAt_mul hf1A0 hpow
    rw [hmul, hpow'] at horder'
    set y := analyticOrderAt (fun ζ : ℂ => f1 (0, ζ)) 0 with hy
    clear_value y
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      rw [show ((⊤ : ℕ∞) + (d : ℕ∞)) = ⊤ from rfl] at horder'
      exact absurd horder' (ENat.natCast_ne_top d).symm
    | coe n =>
      have hcast : ((n + d : ℕ) : ℕ∞) = ((d : ℕ) : ℕ∞) := horder'
      have hn : n + d = d := WithTop.coe_injective hcast
      have hn0 : n = 0 := by omega
      rw [hn0]
      rfl
  have hf1ne0 : f1 (0, 0) ≠ 0 := hf1A0.analyticOrderAt_eq_zero.mp hf1ord0
  have hz00 : ((0 : ι → ℂ), (0 : ℂ)) ∈
      polydisc (0 : ι → ℂ) (fun _ => ε₀) ×ˢ ball (0 : ℂ) ε₀ :=
    ⟨hz0V, mem_ball_self hε₀⟩
  have hf1contAt : ContinuousAt f1 (0, 0) :=
    ((hfdiv.differentiableOn_quotient.analyticOnNhd_of_finiteDimensional
      ((isOpen_polydisc _ _).prod isOpen_ball)) _ hz00).continuousAt
  have hf1ev : ∀ᶠ z in 𝓝 ((0 : ι → ℂ), (0 : ℂ)), f1 z ≠ 0 :=
    hf1contAt.eventually_ne hf1ne0
  obtain ⟨S, hSf1, hSopen, hS0⟩ := _root_.eventually_nhds_iff.mp hf1ev
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := exists_polydisc_ball_subset
    (hSopen.inter ((isOpen_polydisc (0 : ι → ℂ) (fun _ => ε₀)).prod isOpen_ball))
    ⟨hS0, hz00⟩
  have hε₁ε₀ : polydisc (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁ ⊆
      polydisc (0 : ι → ℂ) (fun _ => ε₀) ×ˢ ball (0 : ℂ) ε₀ :=
    fun z hz => (hε₁sub hz).2
  have hf1ne0' : ∀ z ∈ polydisc (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁, f1 z ≠ 0 :=
    fun z hz => hSf1 z (hε₁sub hz).1
  exact ⟨f1, c, ε₀, ε₁, hε₀, hε₁, hε₀U, hfdiv, hcj0, hε₁ε₀, hf1ne0'⟩

omit [Fintype ι] in
/-- Uniform coefficient bounds give a uniform bound for a Weierstrass remainder on a scalar disc,
including the empty remainder when `d = 0`. -/
private theorem norm_weierstrassRemainder_le {d : ℕ} {c : Fin d → (ι → ℂ) → ℂ}
    {w : ι → ℂ} {ζ : ℂ} {R ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ j, ‖c j w‖ ≤ ε) (hζ : ‖ζ‖ ≤ R) :
    ‖weierstrassRemainder c (w, ζ)‖ ≤ (d : ℝ) * ε * (max R 1) ^ d := by
  have hpow (j : Fin d) : ‖ζ‖ ^ (j : ℕ) ≤ (max R 1) ^ d :=
    (pow_le_pow_left₀ (norm_nonneg _) (hζ.trans (le_max_left _ _)) _).trans
      (pow_le_pow_right₀ (le_max_right _ _) j.isLt.le)
  calc
    ‖weierstrassRemainder c (w, ζ)‖ ≤ ∑ j : Fin d, ‖c j w * ζ ^ (j : ℕ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, ε * (max R 1) ^ d := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, norm_pow]
      exact mul_le_mul (hc j) (hpow j) (by positivity) hε
    _ = (d : ℝ) * ε * (max R 1) ^ d := by simp; ring

/-- If the remainder coefficients tend to zero and the leading factor is bounded away from zero,
shrinking only the parameter polydisc gives the contraction bound. The scalar radius and an
upper bound for the parameter radius can be prescribed. -/
private theorem exists_small_remainder_div {d : ℕ} {c : Fin d → (ι → ℂ) → ℂ}
    {f1 : (ι → ℂ) × ℂ → ℂ} {R δ r₀ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hr₀ : 0 < r₀)
    (hc : ∀ j, Tendsto (c j) (𝓝 0) (𝓝 0))
    (hlower : ∀ z ∈ polydisc (0 : ι → ℂ) (fun _ => r₀) ×ˢ ball (0 : ℂ) R,
      δ ≤ ‖f1 z‖) :
    ∃ r : ℝ, 0 < r ∧ r ≤ r₀ ∧
      ∀ z ∈ polydisc (0 : ι → ℂ) (fun _ => r) ×ˢ ball (0 : ℂ) R,
        ‖weierstrassRemainder c z / f1 z‖ ≤ R ^ d / (2 * (d + 1)) := by
  let ε := δ * R ^ d / (2 * (d + 1) * (d + 1) * (max R 1) ^ d)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hev : ∀ᶠ w in 𝓝 (0 : ι → ℂ), ∀ j, ‖c j w‖ < ε := by
    apply eventually_all.mpr
    intro j
    have ht : Tendsto (fun w => ‖c j w‖) (𝓝 0) (𝓝 0) := by simpa using (hc j).norm
    exact ht.eventually_lt_const hε
  obtain ⟨s, hs, hsmall⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min s r₀, lt_min hs hr₀, min_le_right _ _, ?_⟩
  rintro ⟨w, ζ⟩ ⟨hw, hζ⟩
  have hw' : ‖w‖ < min s r₀ := by
    simpa [pi_norm_lt_iff (lt_min hs hr₀), mem_polydisc] using hw
  have hcw : ∀ j, ‖c j w‖ ≤ ε := fun j =>
    (hsmall (by simpa [dist_zero_right] using hw'.trans_le (min_le_left s r₀)) j).le
  have hnum := norm_weierstrassRemainder_le hε.le hcw (mem_ball_zero_iff.mp hζ).le
  have hl := hlower (w, ζ) ⟨polydisc_mono _ (fun _ => min_le_right s r₀) hw, hζ⟩
  rw [norm_div]
  calc
    ‖weierstrassRemainder c (w, ζ)‖ / ‖f1 (w, ζ)‖ ≤
        ((d : ℝ) * ε * (max R 1) ^ d) / δ :=
      (div_le_div_of_nonneg_right hnum (hδ.trans_le hl).le).trans
        (div_le_div_of_nonneg_left (by positivity) hδ hl)
    _ = (d : ℝ) * R ^ d / (2 * (d + 1) * (d + 1)) := by dsimp [ε]; field_simp
    _ ≤ R ^ d / (2 * (d + 1)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos hR d]

/-- **A uniformly small perturbation of the coordinate power.** Given a coordinate-power
decomposition `f = f1 * z.2 ^ d + weierstrassRemainder c` with `f1` nonvanishing on a
polydisc-ball of radius `ε₁`, the perturbation `weierstrassRemainder c / f1` is analytic
there and, on a smaller polydisc-ball, uniformly bounded by `R₂ ^ d / (2 * (d + 1))`: small
enough for the Picard iteration against the divisor `z ^ d` to contract in
`exists_isWeierstrassDivisionOn_of_bounded`. The bound `δ` on `‖f1‖` over a fixed compact set is
also returned, since the germ-uniqueness argument reuses it at a further-shrunk radius. -/
theorem exists_perturbation_bound_of_coordinatePower_leadingFactor {d : ℕ} {f : (ι → ℂ) × ℂ → ℂ}
    {f1 : (ι → ℂ) × ℂ → ℂ} {c : Fin d → (ι → ℂ) → ℂ} {ε₀ ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (hε₁ε₀ : polydisc (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁ ⊆
      polydisc (0 : ι → ℂ) (fun _ => ε₀) ×ˢ ball (0 : ℂ) ε₀)
    (hfdiv : IsWeierstrassDivisionOn (fun z => z.2 ^ d) f f1 c
      (polydisc (0 : ι → ℂ) (fun _ => ε₀)) ε₀)
    (hcj0 : ∀ j, c j 0 = 0)
    (hf1ne0' : ∀ z ∈ polydisc (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁, f1 z ≠ 0) :
    ∃ R₂ δ r₃ : ℝ, 0 < R₂ ∧ R₂ < ε₁ ∧ 0 < δ ∧ 0 < r₃ ∧ r₃ ≤ ε₁ / 2 ∧
      DifferentiableOn ℂ (fun z => weierstrassRemainder c z / f1 z)
        (polydisc (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁) ∧
      (∀ j, Tendsto (c j) (𝓝 0) (𝓝 0)) ∧
      (∀ z ∈ closedPolydisc (0 : ι → ℂ) (fun _ => ε₁ / 2) ×ˢ closedBall (0 : ℂ) R₂,
        δ ≤ ‖f1 z‖) ∧
      ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => r₃), ∀ ζ ∈ ball (0 : ℂ) R₂,
        ‖weierstrassRemainder c (w, ζ) / f1 (w, ζ)‖ ≤ R₂ ^ d / (2 * (d + 1)) := by
  have hpoly1sub : polydisc (0 : ι → ℂ) (fun _ => ε₁) ⊆
      polydisc (0 : ι → ℂ) (fun _ => ε₀) :=
    fun z hz => (hε₁ε₀ (Set.mk_mem_prod hz (mem_ball_self hε₁))).1
  have hcA1 : ∀ j, DifferentiableOn ℂ (c j) (polydisc (0 : ι → ℂ) (fun _ => ε₁)) :=
    fun j => (hfdiv.differentiableOn_coeff j).mono hpoly1sub
  have hremA1 : DifferentiableOn ℂ (weierstrassRemainder c)
      (polydisc (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁) := by
    unfold weierstrassRemainder
    apply DifferentiableOn.fun_sum
    intro j _
    exact ((hcA1 j).comp differentiableOn_fst (fun z hz => hz.1)).mul
      (differentiableOn_snd.pow (j : ℕ))
  have hf1A1 : DifferentiableOn ℂ f1
      (polydisc (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁) :=
    hfdiv.differentiableOn_quotient.mono hε₁ε₀
  have hhA1 : DifferentiableOn ℂ (fun z => weierstrassRemainder c z / f1 z)
      (polydisc (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁) := by
    simp_rw [div_eq_mul_inv]
    exact hremA1.mul (hf1A1.inv hf1ne0')
  set R₂ : ℝ := ε₁ / 2 with hR₂def
  have hR₂pos : 0 < R₂ := by positivity
  have hR₂ε₁ : R₂ < ε₁ := by rw [hR₂def]; linarith
  set K : Set ((ι → ℂ) × ℂ) :=
    closedPolydisc (0 : ι → ℂ) (fun _ => ε₁ / 2) ×ˢ closedBall (0 : ℂ) R₂ with hKdef
  have hKsub : K ⊆ polydisc (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁ := by
    apply Set.prod_mono
    · exact closedPolydisc_subset_polydisc _ (fun _ => by linarith)
    · exact closedBall_subset_ball hR₂ε₁
  have hKcompact : IsCompact K :=
    (isCompact_closedPolydisc _ _).prod (isCompact_closedBall _ _)
  have hKne : K.Nonempty := ⟨(0, 0), by
    refine ⟨mem_closedPolydisc.mpr fun i => ?_, mem_closedBall_self hR₂pos.le⟩
    simpa using (half_pos hε₁).le⟩
  have hf1contK : ContinuousOn f1 K := (hf1A1.mono hKsub).continuousOn
  obtain ⟨zmin, hzminK, hzminmin⟩ := hKcompact.exists_isMinOn hKne hf1contK.norm
  set δ : ℝ := ‖f1 zmin‖ with hδdef
  have hδpos : 0 < δ := norm_pos_iff.mpr (hf1ne0' zmin (hKsub hzminK))
  have hδle : ∀ z ∈ K, δ ≤ ‖f1 z‖ := fun z hz => hzminmin hz
  have hcj0' : ∀ j : Fin d, Tendsto (c j) (𝓝 0) (𝓝 0) := fun j =>
    (hcj0 j) ▸ ((hcA1 j).continuousOn.continuousAt (isOpen_polydisc _ _ |>.mem_nhds
      (mem_polydisc.mpr fun i => by simpa using half_pos hε₁)))
  obtain ⟨r₃, hr₃pos, hr₃ε₁, hhbound⟩ :=
    exists_small_remainder_div hR₂pos hδpos (half_pos hε₁) hcj0'
      (fun z hz => hδle z ⟨mem_closedPolydisc.mpr (fun i => (mem_polydisc.mp
        hz.1 i).le),
        ball_subset_closedBall hz.2⟩)

  exact ⟨R₂, δ, r₃, hR₂pos, hR₂ε₁, hδpos, hr₃pos, hr₃ε₁, hhA1, hcj0', hδle,
    fun w hw ζ hζ => hhbound (w, ζ) ⟨hw, hζ⟩⟩

/-- Germ uniqueness for division by a normalized divisor. A fresh small-remainder estimate allows
comparison on any smaller neighborhood supporting the other decomposition; bounded fixed-point
uniqueness then identifies both germs. -/
private theorem normalized_division_germ_unique {d : ℕ} {r₃ R₂ δ : ℝ}
    {f f1 g S : (ι → ℂ) × ℂ → ℂ} {c aOut : Fin d → (ι → ℂ) → ℂ}
    (hr₃pos : 0 < r₃) (hR₂pos : 0 < R₂) (hδpos : 0 < δ)
    (hf1FINAL : DifferentiableOn ℂ f1
      (polydisc 0 (fun _ => r₃) ×ˢ ball 0 R₂))
    (hlower : ∀ z ∈ polydisc 0 (fun _ => r₃) ×ˢ ball 0 R₂, δ ≤ ‖f1 z‖)
    (hcj0' : ∀ j, Tendsto (c j) (𝓝 0) (𝓝 0))
    (hhFINAL : DifferentiableOn ℂ (fun z => weierstrassRemainder c z / f1 z)
      (polydisc 0 (fun _ => r₃) ×ˢ ball 0 R₂))
    (hf_eq2 : ∀ z ∈ polydisc 0 (fun _ => r₃) ×ˢ ball 0 R₂,
      f z = f1 z * (z.2 ^ d + weierstrassRemainder c z / f1 z))
    (hfixed : IsWeierstrassDivisionOn (fun z => z.2 ^ d)
      (g - (fun z => weierstrassRemainder c z / f1 z) * S) S aOut
      (polydisc 0 (fun _ => r₃)) R₂)
    {q' : (ι → ℂ) × ℂ → ℂ} {a' : Fin d → (ι → ℂ) → ℂ}
    (hdiv' : IsWeierstrassDivisionAt f g q' a') :
    (fun z => S z / f1 z) =ᶠ[𝓝 0] q' ∧ ∀ j, aOut j =ᶠ[𝓝 0] a' j := by
  let domFINAL := polydisc (0 : ι → ℂ) (fun _ => r₃) ×ˢ ball (0 : ℂ) R₂
  let hh := fun z => weierstrassRemainder c z / f1 z
  let q := fun z => S z / f1 z
  have hf1ne0FINAL : ∀ z ∈ domFINAL, f1 z ≠ 0 :=
    fun z hz => norm_pos_iff.mp (hδpos.trans_le (hlower z hz))
  have h00 : (0 : (ι → ℂ) × ℂ) ∈ domFINAL :=
    ⟨mem_polydisc.mpr fun i => by simpa using hr₃pos, mem_ball_self hR₂pos⟩
  obtain ⟨ρ₀, hρ₀pos, hρ₀sub, hlocal⟩ := hdiv'.exists_divisionOn
    ((isOpen_polydisc _ _).prod isOpen_ball) h00
  obtain ⟨ρ, hρpos, hρρ₀⟩ := exists_between hρ₀pos
  have hρsub : polydisc (0 : ι → ℂ) (fun _ => ρ) ×ˢ ball (0 : ℂ) ρ ⊆ domFINAL :=
    (Set.prod_mono (polydisc_mono _ (fun _ => hρρ₀.le))
      (ball_subset_ball hρρ₀.le)).trans hρ₀sub
  -- The same small-remainder lemma applies at this smaller scalar radius.
  obtain ⟨r₅, hr₅pos, hr₅ρ, hhb3⟩ :=
    exists_small_remainder_div hρpos hδpos hρpos hcj0'
      (fun z hz => hlower z (hρsub hz))
  have hdomsub5 : polydisc (0 : ι → ℂ) (fun _ => r₅) ×ˢ ball (0 : ℂ) ρ ⊆ domFINAL :=
    fun z hz => hρsub ⟨polydisc_mono _ (fun _ => hr₅ρ) hz.1, hz.2⟩
  set dom5 : Set ((ι → ℂ) × ℂ) := polydisc (0 : ι → ℂ) (fun _ => r₅) ×ˢ ball (0 : ℂ) ρ
    with hdom5def
  have hlocalSub : dom5 ⊆ polydisc 0 (fun _ => ρ₀) ×ˢ ball 0 ρ₀ :=
    Set.prod_mono (polydisc_mono _ (fun _ => hr₅ρ.trans hρρ₀.le))
      (ball_subset_ball hρρ₀.le)
  have hq'Adiff : DifferentiableOn ℂ q' dom5 := hlocal.differentiableOn_quotient.mono hlocalSub
  have ha'Adiff : ∀ j, DifferentiableOn ℂ (a' j) (polydisc 0 (fun _ => r₅)) :=
    fun j => (hlocal.differentiableOn_coeff j).mono
      (polydisc_mono _ (fun _ => hr₅ρ.trans hρρ₀.le))
  have hf1diff5 : DifferentiableOn ℂ f1 dom5 := hf1FINAL.mono hdomsub5
  set s' : (ι → ℂ) × ℂ → ℂ := fun z => q' z * f1 z with hs'def
  have hs'diff : DifferentiableOn ℂ s' dom5 := hq'Adiff.mul hf1diff5
  have hhFINAL5 : DifferentiableOn ℂ hh dom5 := hhFINAL.mono hdomsub5
  have hpoly53 : polydisc (0 : ι → ℂ) (fun _ => r₅) ⊆
      polydisc (0 : ι → ℂ) (fun _ => r₃) :=
    fun w hw => (hdomsub5 (⟨hw, mem_ball_self hρpos⟩ : (w, (0:ℂ)) ∈ dom5)).1
  have hdiv' : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (g - hh * s') s' a'
      (polydisc (0 : ι → ℂ) (fun _ => r₅)) ρ := by
    refine ⟨hs'diff, ha'Adiff, ?_⟩
    intro z hz
    have heqz : g z = q' z * f z + weierstrassRemainder a' z := hlocal.eq (hlocalSub hz)
    have heqf5 : f z = f1 z * (z.2 ^ d + hh z) := hf_eq2 z (hdomsub5 hz)
    show g z - hh z * s' z = s' z * z.2 ^ d + weierstrassRemainder a' z
    simp only [hs'def]
    rw [heqz, heqf5]
    ring
  have hSdiv : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (g - hh * S) S aOut
      (polydisc (0 : ι → ℂ) (fun _ => r₅)) ρ :=
    ⟨hfixed.differentiableOn_quotient.mono hdomsub5,
      fun j => (hfixed.differentiableOn_coeff j).mono hpoly53, fun _ hz => hfixed.eq (hdomsub5 hz)⟩
  -- Compact containment bounds the difference of the two fixed-point candidates.
  let K := closedPolydisc (0 : ι → ℂ) (fun _ => ρ) ×ˢ closedBall (0 : ℂ) ρ
  have hclosedsub : K ⊆ polydisc 0 (fun _ => ρ₀) ×ˢ ball 0 ρ₀ :=
    Set.prod_mono (closedPolydisc_subset_polydisc _ (fun _ => hρρ₀))
      (closedBall_subset_ball hρρ₀)
  have hKfinal := hclosedsub.trans hρ₀sub
  have hcompact : IsCompact K :=
    (isCompact_closedPolydisc _ _).prod (isCompact_closedBall _ _)
  have hcont : ContinuousOn (fun z => S z - s' z) K :=
    (hfixed.differentiableOn_quotient.continuousOn.mono hKfinal).sub
      ((hlocal.differentiableOn_quotient.continuousOn.mono hclosedsub).mul
        (hf1FINAL.continuousOn.mono hKfinal))
  obtain ⟨C1, hC1⟩ := hcompact.bddAbove_image hcont.norm
  have hM3b : ∀ z ∈ dom5, ‖S z - s' z‖ ≤ max C1 0 := by
    intro z hz
    apply (hC1 ⟨z, ?_, rfl⟩).trans (le_max_left _ _)
    exact ⟨mem_closedPolydisc.mpr fun i =>
      (mem_polydisc.mp hz.1 i).le.trans hr₅ρ, ball_subset_closedBall hz.2⟩
  obtain ⟨hSeqs', haOuteqa'⟩ := eqOn_of_isWeierstrassDivisionOn_selfPerturbed
    hρpos hh g S s' aOut a' hhFINAL5 hhb3 hSdiv hdiv' (max C1 0) (le_max_right _ _) hM3b
  have hqeqq' : EqOn q q' dom5 := by
    intro z hz
    show S z / f1 z = q' z
    rw [hSeqs' hz]
    show s' z / f1 z = q' z
    rw [hs'def]
    exact mul_div_cancel_right₀ _ (hf1ne0FINAL z (hdomsub5 hz))
  have h05 : (0 : (ι → ℂ) × ℂ) ∈ dom5 :=
    ⟨mem_polydisc.mpr fun i => by simpa using hr₅pos, mem_ball_self hρpos⟩
  have hnbhd : dom5 ∈ 𝓝 (0 : (ι → ℂ) × ℂ) :=
    (isOpen_polydisc _ _ |>.prod isOpen_ball).mem_nhds h05
  refine ⟨Filter.eventuallyEq_of_mem hnbhd hqeqq', fun j => Filter.eventuallyEq_of_mem
    ((isOpen_polydisc (0 : ι → ℂ) (fun _ => r₅)).mem_nhds
      (mem_polydisc.mpr fun i => by simpa using hr₅pos)) (haOuteqa' j)⟩

/-- Undoing the nonvanishing leading factor converts a normalized fixed-point division into division
by the original divisor. The remainder is unchanged. -/
private theorem divisionOn_div_leadingFactor {d : ℕ} {r : ι → ℝ} {R : ℝ}
    {f f1 g h S : (ι → ℂ) × ℂ → ℂ} {a : Fin d → (ι → ℂ) → ℂ}
    (hf1 : DifferentiableOn ℂ f1 (polydisc 0 r ×ˢ ball 0 R))
    (hne : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, f1 z ≠ 0)
    (heq : ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, f z = f1 z * (z.2 ^ d + h z))
    (hfixed : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (g - h * S) S a
      (polydisc 0 r) R) :
    IsWeierstrassDivisionOn f g (fun z => S z / f1 z) a (polydisc 0 r) R := by
  refine ⟨?_, hfixed.differentiableOn_coeff, ?_⟩
  · change DifferentiableOn ℂ (fun z => S z / f1 z) _
    simp_rw [div_eq_mul_inv]
    exact hfixed.differentiableOn_quotient.mul (hf1.inv hne)
  · intro z hz
    change g z = S z / f1 z * f z + weierstrassRemainder a z
    have hqf : S z / f1 z * f z = S z * (z.2 ^ d + h z) := by
      rw [heq z hz]
      field_simp [hne z hz]
    rw [hqf]
    have h := hfixed.eq hz
    dsimp only [Pi.sub_apply, Pi.mul_apply] at h
    linear_combination h

/-- **Weierstrass division ([Jakóbczak–Jarnicki][JakobczakJarnicki2021] 1.7.3).** A divisor whose
central
scalar slice has finite order `d` admits division of every bounded holomorphic numerator
on a fixed polydisc. The quotient bound is uniform in the numerator. Uniqueness is local,
so it also compares decompositions initially defined on smaller neighborhoods.
The proof combines normalization, the Picard limit, and local fixed-point uniqueness. -/
theorem exists_isWeierstrassDivisionOn_of_bounded {d : ℕ} {f : (ι → ℂ) × ℂ → ℂ}
    {U : Set ((ι → ℂ) × ℂ)} (hU : IsOpen U) (h0 : 0 ∈ U)
    (hf : DifferentiableOn ℂ f U)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    ∃ (r : ι → ℝ) (R C : ℝ), (∀ i, 0 < r i) ∧ 0 < R ∧ 0 < C ∧
      polydisc 0 r ×ˢ ball 0 R ⊆ U ∧
      ∀ (g : (ι → ℂ) × ℂ → ℂ),
        DifferentiableOn ℂ g (polydisc 0 r ×ˢ ball 0 R) →
        ∀ M : ℝ, 0 ≤ M → (∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖g z‖ ≤ M) →
        ∃ (q : (ι → ℂ) × ℂ → ℂ) (a : Fin d → (ι → ℂ) → ℂ),
          IsWeierstrassDivisionOn f g q a (polydisc 0 r) R ∧
          (∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖q z‖ ≤ C * M) ∧
          (∀ q' a', IsWeierstrassDivisionAt f g q' a' →
            q =ᶠ[𝓝 0] q' ∧ ∀ j, a j =ᶠ[𝓝 0] a' j) := by
  -- Normalize the divisor and choose a nonvanishing leading factor.
  obtain ⟨f1, c, ε₀, ε₁, hε₀, hε₁, hε₀U, hfdiv, hcj0, hε₁ε₀, hf1ne0'⟩ :=
    exists_coordinatePower_leadingFactor_ne_zero hU h0 hf horder
  -- Choose a domain on which the normalized perturbation contracts.
  obtain ⟨R₂, δ, r₃, hR₂pos, hR₂ε₁, hδpos, hr₃pos, hr₃ε₁, hhA1, hcj0', hδle, hhbound⟩ :=
    exists_perturbation_bound_of_coordinatePower_leadingFactor hε₁ hε₁ε₀ hfdiv hcj0 hf1ne0'
  set hh : (ι → ℂ) × ℂ → ℂ := fun z => weierstrassRemainder c z / f1 z with hhdef
  set K : Set ((ι → ℂ) × ℂ) :=
    closedPolydisc (0 : ι → ℂ) (fun _ => ε₁ / 2) ×ˢ closedBall (0 : ℂ) R₂ with hKdef
  -- Restrict to the common domain for all bounded numerators.
  have hr₃ε₁' : r₃ ≤ ε₁ := hr₃ε₁.trans (by linarith)
  have hR₂ε₁' : R₂ ≤ ε₁ := hR₂ε₁.le
  have hFINALsubε₁ : polydisc (0 : ι → ℂ) (fun _ => r₃) ×ˢ ball (0 : ℂ) R₂ ⊆
      polydisc (0 : ι → ℂ) (fun _ => ε₁) ×ˢ ball (0 : ℂ) ε₁ :=
    Set.prod_mono (polydisc_mono _ (fun _ => hr₃ε₁')) (ball_subset_ball hR₂ε₁')
  have hFINALsub : polydisc (0 : ι → ℂ) (fun _ => r₃) ×ˢ ball (0 : ℂ) R₂ ⊆ U :=
    hFINALsubε₁.trans (fun z hz => hε₀U (hε₁ε₀ hz))
  have hhFINAL : DifferentiableOn ℂ (fun z => weierstrassRemainder c z / f1 z)
      (polydisc (0 : ι → ℂ) (fun _ => r₃) ×ˢ ball (0 : ℂ) R₂) :=
    hhA1.mono hFINALsubε₁
  have hhboundFINAL : ∀ z ∈ polydisc (0 : ι → ℂ) (fun _ => r₃) ×ˢ ball (0 : ℂ) R₂,
      ‖weierstrassRemainder c z / f1 z‖ ≤ R₂ ^ d / (2 * (d + 1)) :=
    fun z hz => hhbound z.1 hz.1 z.2 hz.2
  refine ⟨fun _ => r₃, R₂, 2 * ((d : ℝ) + 1) / (R₂ ^ d * δ), fun _ => hr₃pos, hR₂pos,
    by positivity, hFINALsub, ?_⟩
  intro g hg M hM0 hMb
  set domFINAL : Set ((ι → ℂ) × ℂ) :=
    polydisc (0 : ι → ℂ) (fun _ => r₃) ×ˢ ball (0 : ℂ) R₂ with hdomFINALdef
  set sSeq := fun k => picardApprox d (fun _ => r₃) R₂ (fun _ => hr₃pos) hR₂pos hh g hg hhFINAL k
    with hsSeqdef
  set B : ℝ := ((d + 1 : ℕ) : ℝ) / R₂ ^ d * M with hBdef
  obtain ⟨S, hSanalytic, hSbound⟩ := exists_tendstoUniformlyOn_picardApprox d (fun _ => r₃) R₂
    (fun _ => hr₃pos) hR₂pos hh g hg hhFINAL M hM0 hMb hhboundFINAL
  obtain ⟨aOut, haFINAL, hkey⟩ := exists_weierstrassRemainder_eq_of_tendstoUniformlyOn_picardApprox
    d (fun _ => r₃) R₂ (fun _ => hr₃pos) hR₂pos hh g hg hhFINAL hhboundFINAL M hM0 S
    hSanalytic.differentiableOn hSbound
  -- Undo normalization, retaining the uniform quotient estimate.
  have hf1ne0FINAL : ∀ z ∈ domFINAL, f1 z ≠ 0 := fun z hz => hf1ne0' z (hFINALsubε₁ hz)
  have hf_eq2 : ∀ z ∈ domFINAL, f z = f1 z * (z.2 ^ d + hh z) := by
    intro z hz
    have hz0 : z ∈ polydisc (0 : ι → ℂ) (fun _ => ε₀) ×ˢ ball (0 : ℂ) ε₀ :=
      hε₁ε₀ (hFINALsubε₁ hz)
    have h1 : f z = f1 z * z.2 ^ d + weierstrassRemainder c z := hfdiv.eq hz0
    have h2 : weierstrassRemainder c z = hh z * f1 z := by
      show weierstrassRemainder c z = weierstrassRemainder c z / f1 z * f1 z
      rw [div_mul_cancel₀ _ (hf1ne0FINAL z hz)]
    rw [h2] at h1
    rw [h1]; ring
  set q : (ι → ℂ) × ℂ → ℂ := fun z => S z / f1 z with hqdef
  have hf1FINAL : DifferentiableOn ℂ f1 domFINAL :=
    hfdiv.differentiableOn_quotient.mono (hFINALsubε₁.trans hε₁ε₀)
  have hfixed : IsWeierstrassDivisionOn (fun z => z.2 ^ d) (g - hh * S) S aOut
      (polydisc 0 (fun _ => r₃)) R₂ := by
    refine ⟨hSanalytic.differentiableOn, haFINAL, ?_⟩
    intro z hz
    have h := hkey z.1 hz.1 z.2 hz.2
    dsimp only [Pi.sub_apply, Pi.mul_apply]
    linear_combination h
  have hdivision := divisionOn_div_leadingFactor hf1FINAL hf1ne0FINAL hf_eq2 hfixed
  have hdomFINALsubK : domFINAL ⊆ K := by
    apply Set.prod_mono
    · intro w hw
      exact mem_closedPolydisc.mpr fun i =>
        (mem_polydisc.mp hw i).le.trans hr₃ε₁
    · exact ball_subset_closedBall
  refine ⟨q, aOut, hdivision, ?_, ?_⟩
  · intro z hz
    have hS0eq : (sSeq 0).1 = 0 := rfl
    have hb0 := hSbound 0 z hz
    rw [hS0eq] at hb0
    have hSb : ‖S z‖ ≤ 2 * B := by
      have hthis : ‖(0:ℂ) - S z‖ ≤ B * (1/2)^0 / (1 - 1/2) := hb0
      rw [zero_sub, norm_neg] at hthis
      norm_num at hthis
      linarith
    have hf1ge : δ ≤ ‖f1 z‖ := hδle _ (hdomFINALsubK hz)
    have hf1pos' : 0 < ‖f1 z‖ := hδpos.trans_le hf1ge
    show ‖S z / f1 z‖ ≤ 2 * ((d:ℝ) + 1) / (R₂ ^ d * δ) * M
    rw [norm_div]
    calc ‖S z‖ / ‖f1 z‖ ≤ (2 * B) / ‖f1 z‖ := div_le_div_of_nonneg_right hSb hf1pos'.le
      _ ≤ (2 * B) / δ := div_le_div_of_nonneg_left (by positivity) hδpos hf1ge
      _ = 2 * ((d:ℝ) + 1) / (R₂ ^ d * δ) * M := by
          rw [hBdef]; push_cast; field_simp
  · intro q' a' hdiv'
    exact normalized_division_germ_unique hr₃pos hR₂pos hδpos hf1FINAL
      (fun z hz => hδle z (hdomFINALsubK hz)) hcj0' hhFINAL hf_eq2
      hfixed hdiv'

/-- Analytic Weierstrass division for arbitrary numerator germs. No boundedness assumption is needed
because the representatives can be restricted to a smaller neighborhood. The uniform division
theorem supplies the quotient and its germ uniqueness. -/
theorem exists_isWeierstrassDivisionAt {d : ℕ} {f g : (ι → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    ∃ (q : (ι → ℂ) × ℂ → ℂ) (a : Fin d → (ι → ℂ) → ℂ),
      IsWeierstrassDivisionAt f g q a ∧
      ∀ q' a', IsWeierstrassDivisionAt f g q' a' →
        q =ᶠ[𝓝 0] q' ∧ ∀ j, a j =ᶠ[𝓝 0] a' j := by
  have hb : ∀ᶠ z in 𝓝 0, ‖g z‖ < ‖g 0‖ + 1 :=
    hg.continuousAt.norm.eventually_lt_const (lt_add_one _)
  obtain ⟨U, hsub, hU, h0⟩ := _root_.eventually_nhds_iff.mp
    (hf.eventually_analyticAt.and (hg.eventually_analyticAt.and hb))
  obtain ⟨r, R, C, hr, hR, _, hPU, hdiv⟩ :=
    exists_isWeierstrassDivisionOn_of_bounded hU h0
      (fun z hz => (hsub z hz).1.differentiableAt.differentiableWithinAt)
      horder
  obtain ⟨q, a, hqa, _, huniq⟩ := hdiv g
    (fun z hz => (hsub z (hPU hz)).2.1.differentiableAt.differentiableWithinAt)
    (‖g 0‖ + 1) (by positivity) (fun z hz => (hsub z (hPU hz)).2.2.le)
  refine ⟨q, a, hqa.at_zero (isOpen_polydisc _ _) ?_ hR, huniq⟩
  simpa using hr

/-- Two local division decompositions agree as germs, including every remainder coefficient. This
follows from the uniform division theorem. -/
theorem IsWeierstrassDivisionAt.unique {d : ℕ} {f g q q' : (ι → ℂ) × ℂ → ℂ}
    {a a' : Fin d → (ι → ℂ) → ℂ}
    (h : IsWeierstrassDivisionAt f g q a) (h' : IsWeierstrassDivisionAt f g q' a')
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    q =ᶠ[𝓝 0] q' ∧ ∀ j, a j =ᶠ[𝓝 0] a' j := by
  obtain ⟨q₀, a₀, _, hu⟩ := exists_isWeierstrassDivisionAt hf hg horder
  exact ⟨(hu q a h).1.symm.trans (hu q' a' h').1,
    fun j => ((hu q a h).2 j).symm.trans ((hu q' a' h').2 j)⟩

/-- Local uniqueness extends to the whole product domain by the identity theorem. In particular this
gives uniqueness on the fixed polydisc in the bounded division theorem. -/
theorem IsWeierstrassDivisionOn.unique {d : ℕ} {f g q q' : (ι → ℂ) × ℂ → ℂ}
    {a a' : Fin d → (ι → ℂ) → ℂ} {V : Set (ι → ℂ)} {R : ℝ}
    (h : IsWeierstrassDivisionOn f g q a V R) (h' : IsWeierstrassDivisionOn f g q' a' V R)
    (hV : IsOpen V) (hconn : IsPreconnected V) (h0 : 0 ∈ V) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (V ×ˢ ball 0 R))
    (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R))
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    EqOn q q' (V ×ˢ ball 0 R) ∧ ∀ j, EqOn (a j) (a' j) V := by
  have hz : (0 : (ι → ℂ) × ℂ) ∈ V ×ˢ ball 0 R := ⟨h0, mem_ball_self hR⟩
  have ho : IsOpen (V ×ˢ ball (0 : ℂ) R) := hV.prod isOpen_ball
  obtain ⟨hq, ha⟩ := (h.at_zero hV h0 hR).unique (h'.at_zero hV h0 hR)
    ((hf.analyticOnNhd_of_finiteDimensional ho) _ hz)
    ((hg.analyticOnNhd_of_finiteDimensional ho) _ hz) horder
  exact ⟨DifferentiableOn.eqOn_of_preconnected_of_eventuallyEq ho
      (hconn.prod (convex_ball (0 : ℂ) R).isPreconnected)
      h.differentiableOn_quotient h'.differentiableOn_quotient hz hq,
    fun j => DifferentiableOn.eqOn_of_preconnected_of_eventuallyEq hV hconn
      (h.differentiableOn_coeff j) (h'.differentiableOn_coeff j) h0 (ha j)⟩

/-- Division transports along a continuous linear equivalence of the parameter space. -/
theorem IsWeierstrassDivisionAt.comp_equiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (φ : F ≃L[ℂ] E) {d : ℕ} {f g q : E × ℂ → ℂ} {a : Fin d → E → ℂ}
    (h : IsWeierstrassDivisionAt f g q a) :
    IsWeierstrassDivisionAt (fun z : F × ℂ => f (φ z.1, z.2)) (fun z : F × ℂ => g (φ z.1, z.2))
      (fun z : F × ℂ => q (φ z.1, z.2)) (fun j x => a j (φ x)) := by
  have hφ : AnalyticAt ℂ φ (0 : F) := φ.toContinuousLinearMap.analyticAt 0
  have hφmap : φ (0 : F) = 0 := φ.map_zero
  have hpair : AnalyticAt ℂ (fun z : F × ℂ => (φ z.1, z.2)) (0 : F × ℂ) :=
    (hφ.comp_of_eq analyticAt_fst rfl).prod analyticAt_snd
  have h0 : (fun z : F × ℂ => (φ z.1, z.2)) 0 = (0 : E × ℂ) := by simp [hφmap]
  have ht : Tendsto (fun z : F × ℂ => (φ z.1, z.2)) (𝓝 0) (𝓝 (0 : E × ℂ)) := by
    rw [← h0]; exact hpair.continuousAt.tendsto
  refine ⟨h.analyticAt_quotient.comp_of_eq hpair h0,
    fun j => (h.analyticAt_coeff j).comp_of_eq hφ hφmap,
    (h.eq.comp_tendsto ht).mono fun z hz => by
      simpa [weierstrassRemainder] using hz⟩

/-- **Weierstrass division for analytic germs on any finite-dimensional parameter space.**
Obtained by transporting the coordinate version along a basis; no choice of coordinates
occurs in the statement. -/
theorem exists_isWeierstrassDivisionAt_of_finiteDimensional [FiniteDimensional ℂ E] {d : ℕ}
    {f g : E × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    ∃ (q : E × ℂ → ℂ) (a : Fin d → E → ℂ),
      IsWeierstrassDivisionAt f g q a ∧
      ∀ q' a', IsWeierstrassDivisionAt f g q' a' →
        q =ᶠ[𝓝 0] q' ∧ ∀ j, a j =ᶠ[𝓝 0] a' j := by
  set e := (Module.finBasis ℂ E).equivFunL with he_def
  set fg : (Fin (Module.finrank ℂ E) → ℂ) × ℂ → ℂ := fun z => f (e.symm z.1, z.2) with hfg_def
  set gg : (Fin (Module.finrank ℂ E) → ℂ) × ℂ → ℂ := fun z => g (e.symm z.1, z.2) with hgg_def
  have hfg0 : (fun w : ℂ => fg (0, w)) = fun w : ℂ => f (0, w) := by funext w; simp [hfg_def]
  have hfgan : AnalyticAt ℂ fg 0 :=
    hf.comp_of_eq (((e.symm.toContinuousLinearMap.analyticAt 0).comp_of_eq analyticAt_fst rfl).prod
      analyticAt_snd) (by simp)
  have hggan : AnalyticAt ℂ gg 0 :=
    hg.comp_of_eq (((e.symm.toContinuousLinearMap.analyticAt 0).comp_of_eq analyticAt_fst rfl).prod
      analyticAt_snd) (by simp)
  have hfgorder : analyticOrderAt (fun w : ℂ => fg (0, w)) 0 = d := by rw [hfg0]; exact horder
  obtain ⟨q, a, Hq, huniqq⟩ := exists_isWeierstrassDivisionAt hfgan hggan hfgorder
  have hf_eq : f = fun z : E × ℂ => fg (e z.1, z.2) := by funext z; simp [hfg_def]
  have hg_eq : g = fun z : E × ℂ => gg (e z.1, z.2) := by funext z; simp [hgg_def]
  have Hf : IsWeierstrassDivisionAt f g (fun z : E × ℂ => q (e z.1, z.2))
      (fun j x => a j (e x)) := by
    rw [hf_eq, hg_eq]; exact Hq.comp_equiv e
  refine ⟨_, _, Hf, fun q' a' Hq' => ?_⟩
  have Hq'' : IsWeierstrassDivisionAt fg gg (fun z => q' (e.symm z.1, z.2))
      (fun j x => a' j (e.symm x)) := by
    rw [hfg_def, hgg_def]; exact Hq'.comp_equiv e.symm
  obtain ⟨huq, hab⟩ := huniqq _ _ Hq''
  have ht : Tendsto (fun z : E × ℂ => (e z.1, z.2)) (𝓝 0)
      (𝓝 (0 : (Fin (Module.finrank ℂ E) → ℂ) × ℂ)) := by
    have h0 : (fun z : E × ℂ => (e z.1, z.2)) 0 = (0 : (Fin (Module.finrank ℂ E) → ℂ) × ℂ) := by
      simp
    rw [← h0]
    exact (((e.toContinuousLinearMap.analyticAt 0).comp_of_eq analyticAt_fst rfl).prod
      analyticAt_snd).continuousAt.tendsto
  refine ⟨(huq.comp_tendsto ht).mono fun z hz => ?_, fun j => ?_⟩
  · simpa using hz
  · have htj : Tendsto e (𝓝 (0 : E)) (𝓝 (0 : Fin (Module.finrank ℂ E) → ℂ)) := by
      simpa using (e.toContinuousLinearMap.analyticAt 0).continuousAt.tendsto
    exact ((hab j).comp_tendsto htj).mono fun x hx => by simpa using hx

/-- A local division identity is an identity in the project's ring of analytic germs. -/
theorem IsWeierstrassDivisionAt.germ_eq {d : ℕ} {f g q : E × ℂ → ℂ}
    {a : Fin d → E → ℂ} (h : IsWeierstrassDivisionAt f g q a)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    AnalyticGerm.ofAnalyticAt g hg =
      AnalyticGerm.ofAnalyticAt q h.analyticAt_quotient * AnalyticGerm.ofAnalyticAt f hf +
      AnalyticGerm.ofAnalyticAt (weierstrassRemainder a)
        (analyticAt_weierstrassRemainder h.analyticAt_coeff) := by
  apply Subtype.ext
  exact Germ.coe_eq.mpr h.eq

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
