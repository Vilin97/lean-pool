/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SeparatedIntertwiner
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralSupport
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.ResolventOpen
public import Mathlib.Topology.UrysohnsLemma

/-!
# Rosenblum: an intertwiner of disjoint spectra vanishes

If `X : F →L[ℂ] E` intertwines two self-adjoint operators `A` and `B` whose
spectra are disjoint, then `X = 0`.

## Why this does not need a Borel functional calculus

The obvious route is to upgrade `SeparatedIntertwiner`'s continuous-symbol
intertwining to Borel symbols, then take `E_A(S) = 0` and `E_B(S) = 1` for a
Borel set `S` separating the spectra.  That upgrade is a monotone-class argument
through the diagonal measures and it is the expensive part.

It is avoidable.  The obstruction to a *continuous* separator is a single point:
both Cayley spectra contain `1` as soon as both operators are unbounded, so no
continuous symbol can be `0` on one and `1` on the other.  But `1` is a null
point for every diagonal measure (`diagMeasure_cayley_preimage_one`), so a
*sequence* of continuous symbols that vanish near `1` and separate elsewhere is
enough:

* `separator` — continuous on `ℝ`, `0` on `σ(A) ∩ ℝ`, `1` on `σ(B) ∩ ℝ`, valued
  in `[0,1]`.  Exists by Urysohn because both spectra are closed
  (`isClosed_realSpectrum`) and disjoint;
* `cayleySymbol n` — that separator pulled back along the inverse Cayley map and
  damped by `min 1 (n ‖w - 1‖)`, which is continuous **including at `1`**
  because the damping factor squeezes it to `0` there.

Then `cayleySymbol n → 0` a.e. for `A`'s diagonal measures and `→ 1` a.e. for
`B`'s — "a.e." being exactly `SpectralSupport`'s statement that the diagonal
measures live on the spectrum — and two dominated-convergence limits finish it:

* `‖cfcHom_A (g n) (X ξ)‖ → 0`;
* `‖cfcHom_B (g n) ξ - ξ‖ → 0`, so `‖X (cfcHom_B (g n) ξ)‖ → ‖X ξ‖`.

The intertwining says those two sequences are equal, so `‖X ξ‖ = 0`.

Only *diagonal* matrix elements appear, so `integral_diagMeasure` is the whole
measure-theoretic interface; no polarisation and no `pair` form is needed.

## Provenance

The theorem selection is Spectra's
(`Spectra.QuantumMechanics.SpectralTheory.generatorIntertwiner_eq_zero_of_disjoint_spectrum`);
the continuous-symbol half is
`ForTauCeti/Analysis/InnerProductSpace/SeparatedIntertwiner.lean`; the route past
the Cayley singularity is new.
-/

public section

open scoped InnerProductSpace
open Filter Topology MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace LinearPMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section Separator

/-- The scalar inverse Cayley map on all of `ℂ`, with junk value at `1`. -/
@[expose]
noncomputable def cayleyCoordFun (w : ℂ) : ℝ := (Complex.I * (1 + w) / (1 - w)).re

/-- The inverse Cayley map is continuous away from `w = 1`.  Only `ContinuousOn` is available: the
singularity at `1` is genuine, and removing it is what `damp` exists for. -/
theorem continuousOn_cayleyCoordFun : ContinuousOn cayleyCoordFun {w : ℂ | w ≠ 1} := by
  refine Complex.continuous_re.comp_continuousOn ?_
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro w hw
  exact sub_ne_zero.mpr (Ne.symm hw)

/-- The damping factor `min 1 (n ‖w - 1‖)`: continuous, valued in `[0,1]`,
zero at `w = 1`, and tending to `1` at every `w ≠ 1`. -/
noncomputable def damp (n : ℕ) (w : ℂ) : ℝ := min 1 ((n : ℝ) * ‖w - 1‖)

/-- The damping factor is continuous, including at `w = 1`. -/
theorem continuous_damp (n : ℕ) : Continuous (damp n) := by
  unfold damp; fun_prop

/-- The damping factor is nonnegative. -/
theorem damp_nonneg (n : ℕ) (w : ℂ) : 0 ≤ damp n w :=
  le_min zero_le_one (by positivity)

/-- The damping factor is at most `1`, so damping never increases a symbol's size. -/
theorem damp_le_one (n : ℕ) (w : ℂ) : damp n w ≤ 1 := min_le_left _ _

/-- The damping factor is at most `n ‖w - 1‖`.  This is the bound that forces it to `0` at the
singularity, which is what makes the damped symbol continuous there. -/
theorem damp_le (n : ℕ) (w : ℂ) : damp n w ≤ (n : ℝ) * ‖w - 1‖ := min_le_right _ _

/-- Away from the singularity the damping switches off in the limit -- eventually *equal* to `1`,
not merely convergent, since `min` saturates once `n ‖w - 1‖ ≥ 1`. -/
theorem tendsto_damp {w : ℂ} (hw : w ≠ 1) :
    Tendsto (fun n : ℕ => damp n w) atTop (nhds 1) := by
  have hpos : 0 < ‖w - 1‖ := by
    simpa [sub_eq_zero] using norm_pos_iff.mpr (sub_ne_zero.mpr hw)
  have hev : ∀ᶠ n : ℕ in atTop, damp n w = 1 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖w - 1‖)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hle : (1 : ℝ) ≤ (n : ℝ) * ‖w - 1‖ := by
      have hNn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      have : 1 / ‖w - 1‖ < (n : ℝ) := lt_of_lt_of_le hN hNn
      calc (1 : ℝ) = (1 / ‖w - 1‖) * ‖w - 1‖ := by field_simp
        _ ≤ (n : ℝ) * ‖w - 1‖ := by nlinarith
    exact min_eq_left hle
  exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)

/-- The damped, pulled-back separator as a scalar symbol on `ℂ`.  Continuous
**everywhere**, including at the Cayley singularity `w = 1`, where the damping
factor squeezes it to zero. -/
noncomputable def cayleySymbolFun (f : C(ℝ, ℝ)) (n : ℕ) (w : ℂ) : ℂ :=
  ((f (cayleyCoordFun w) * damp n w : ℝ) : ℂ)

/-- A damped separator symbol is bounded by `1` when the separator is, both factors lying in
`[0, 1]`. -/
theorem norm_cayleySymbolFun_le (f : C(ℝ, ℝ)) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (w : ℂ) : ‖cayleySymbolFun f n w‖ ≤ 1 := by
  rw [cayleySymbolFun, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have h1 : |f (cayleyCoordFun w)| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [(hf (cayleyCoordFun w)).1], (hf (cayleyCoordFun w)).2⟩
  have h2 : |damp n w| ≤ 1 := by
    rw [abs_of_nonneg (damp_nonneg n w)]
    exact damp_le_one n w
  nlinarith [abs_nonneg (f (cayleyCoordFun w)), abs_nonneg (damp n w)]

/-- **The damped symbol is continuous everywhere, including at `w = 1`.**  This is the point of the
construction: `cayleyCoordFun` alone is only `ContinuousOn {w ≠ 1}`, and the damping squeezes the
product to zero at the singularity so the two branches agree. -/
theorem continuous_cayleySymbolFun (f : C(ℝ, ℝ)) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) : Continuous (cayleySymbolFun f n) := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 1
  · -- at the singularity: the damping factor squeezes the symbol to zero
    subst hw
    have hval : cayleySymbolFun f n 1 = 0 := by
      simp [cayleySymbolFun, damp]
    rw [ContinuousAt, hval]
    refine squeeze_zero_norm (a := fun v : ℂ => (n : ℝ) * ‖v - 1‖) (fun v => ?_) ?_
    · rw [cayleySymbolFun, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have h1 : |f (cayleyCoordFun v)| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [(hf (cayleyCoordFun v)).1], (hf (cayleyCoordFun v)).2⟩
      have h2 : |damp n v| ≤ (n : ℝ) * ‖v - 1‖ := by
        rw [abs_of_nonneg (damp_nonneg n v)]
        exact damp_le n v
      nlinarith [abs_nonneg (f (cayleyCoordFun v)), abs_nonneg (damp n v),
        mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ)) (norm_nonneg (v - 1))]
    · have : Continuous fun v : ℂ => (n : ℝ) * ‖v - 1‖ := by fun_prop
      simpa using this.tendsto 1
  · -- away from the singularity: an ordinary product of continuous functions
    have hopen : IsOpen {v : ℂ | v ≠ 1} := isOpen_ne
    have hmem : w ∈ {v : ℂ | v ≠ 1} := hw
    have hcoord : ContinuousAt cayleyCoordFun w :=
      (continuousOn_cayleyCoordFun.continuousAt (hopen.mem_nhds hmem))
    have hprod : ContinuousAt (fun v : ℂ => (f (cayleyCoordFun v) * damp n v : ℝ)) w :=
      (f.continuous.continuousAt.comp hcoord).mul (continuous_damp n).continuousAt
    exact Complex.continuous_ofReal.continuousAt.comp hprod

/-- Off the singularity the damped symbols converge to the undamped one, so the damping is
recovered in the limit.  With the uniform bound this is what lets dominated convergence replace the
monotone-class argument. -/
theorem tendsto_cayleySymbolFun (f : C(ℝ, ℝ)) {w : ℂ} (hw : w ≠ 1) :
    Tendsto (fun n : ℕ => cayleySymbolFun f n w) atTop
      (nhds ((f (cayleyCoordFun w) : ℝ) : ℂ)) := by
  have h : Tendsto (fun n : ℕ => (f (cayleyCoordFun w) * damp n w : ℝ)) atTop
      (nhds (f (cayleyCoordFun w) * 1)) :=
    tendsto_const_nhds.mul (tendsto_damp hw)
  rw [mul_one] at h
  exact (Complex.continuous_ofReal.tendsto _).comp h

end Separator

section NormSquare

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H} (ha : IsStarNormal a)

/-- The norm of a continuous-calculus image, as an integral against the diagonal
measure.  This is the only measure-theoretic interface the Rosenblum argument
needs: everything is a *diagonal* matrix element, so no polarisation appears. -/
@[simp]
theorem norm_sq_cfcHom_apply (g : C(_root_.spectrum ℂ a, ℂ)) (v : H) :
    ((‖cfcHom ha g v‖ ^ 2 : ℝ) : ℂ)
      = ∫ w, (starRingEnd ℂ) (g w) * g w ∂(BorelCalculus.diagMeasure ha v) := by
  have hstar : (cfcHom ha g).adjoint = cfcHom ha (star g) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  have hfun : (fun w => (starRingEnd ℂ) (g w) * g w)
      = fun w => ((star g * g : C(_root_.spectrum ℂ a, ℂ)) w) := (rfl)
  have key : ⟪v, cfcHom ha (star g * g) v⟫_ℂ = ⟪cfcHom ha g v, cfcHom ha g v⟫_ℂ := by
    rw [map_mul]
    -- states the goal as the inner-product identity the structure lemma expects.
    change ⟪v, cfcHom ha (star g) (cfcHom ha g v)⟫_ℂ = _
    rw [← hstar, ContinuousLinearMap.adjoint_inner_right]
  rw [hfun, BorelCalculus.integral_diagMeasure, key, inner_self_eq_norm_sq_to_K]
  norm_cast

end NormSquare

section Rosenblum

variable {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)

/-- A continuous separator of the two real spectra: `0` on `A`'s, `1` on `B`'s,
valued in `[0,1]`.  Urysohn, using that both are closed and disjoint. -/
theorem exists_spectralSeparator (hdisj : Disjoint (spectrum A) (spectrum B)) :
    ∃ f : C(ℝ, ℝ), Set.EqOn f 0 (Complex.ofReal ⁻¹' spectrum A) ∧
      Set.EqOn f 1 (Complex.ofReal ⁻¹' spectrum B) ∧ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
  refine exists_continuous_zero_one_of_isClosed (isClosed_realSpectrum A)
    (isClosed_realSpectrum B) ?_
  refine Set.disjoint_left.mpr fun lam hlamA hlamB => ?_
  exact Set.disjoint_left.mp hdisj hlamA hlamB

/-- The diagonal measures of `A` live over the spectrum of `A`: almost every
point of the Cayley spectrum has its inverse-Cayley coordinate in the real
spectrum.  This is `SpectralSupport`, transported through the pushforward that
defines `spectralPVM`. -/
theorem ae_cayleyInv_mem_spectrum (v : E) :
    ∀ᵐ w ∂(BorelCalculus.diagMeasure (isStarNormal_cayley hA) v),
      ((cayleyInv hA w : ℝ) : ℂ) ∈ spectrum A := by
  have hmeas : MeasurableSet (Complex.ofReal ⁻¹' resolventSet A) :=
    ((isOpen_resolventSet A).preimage Complex.continuous_ofReal).measurableSet
  have hzero : (spectralPVM hA).diag v (Complex.ofReal ⁻¹' resolventSet A) = 0 :=
    diag_eq_zero_of_subset_resolventSet hA _ hmeas (fun _ h => h) v
  have hmap : (spectralPVM hA).diag v (Complex.ofReal ⁻¹' resolventSet A)
      = BorelCalculus.diagMeasure (isStarNormal_cayley hA) v
          (cayleyInv hA ⁻¹' (Complex.ofReal ⁻¹' resolventSet A)) := by
    rw [show (spectralPVM hA).diag v
        = Measure.map (cayleyInv hA) (BorelCalculus.diagMeasure (isStarNormal_cayley hA) v)
      from by
        rw [spectralPVM_def, BorelCalculus.toProjValMeasure_diag, BorelCalculus.specDiag_def],
      Measure.map_apply (measurable_cayleyInv hA) hmeas]
  rw [hmap] at hzero
  have := MeasureTheory.compl_mem_ae_iff.mpr hzero
  filter_upwards [this] with w hw
  exact hw

end Rosenblum

section Main

variable {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}

/-- On the `A` side the damped separator is **identically zero almost
everywhere, for every `n`** — no limit is needed there.  The separator vanishes
on `A`'s spectrum, and almost every point of the Cayley spectrum has its
coordinate in that spectrum. -/
theorem cfcHom_separator_eq_zero (hA : IsSelfAdjoint A) (f : C(ℝ, ℝ))
    (hfA : Set.EqOn f 0 (Complex.ofReal ⁻¹' spectrum A)) (n : ℕ)
    (g : C(_root_.spectrum ℂ (cayley hA), ℂ))
    (hgval : ∀ w, g w = cayleySymbolFun f n (w : ℂ)) :
    cfcHom (isStarNormal_cayley hA) g = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hae : ∀ᵐ w ∂(BorelCalculus.diagMeasure (isStarNormal_cayley hA) v),
      (starRingEnd ℂ) (g w) * g w = 0 := by
    filter_upwards [ae_cayleyInv_mem_spectrum hA v] with w hw
    have hf0 : f (cayleyInv hA w) = 0 := hfA hw
    have : g w = 0 := by
      rw [hgval w, cayleySymbolFun]
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      change ((f (cayleyInv hA w) * damp n (w : ℂ) : ℝ) : ℂ) = 0
      rw [hf0, zero_mul, Complex.ofReal_zero]
    rw [this, mul_zero]
  have hnorm := norm_sq_cfcHom_apply (isStarNormal_cayley hA) g v
  rw [MeasureTheory.integral_congr_ae hae, integral_zero] at hnorm
  have hz : ‖cfcHom (isStarNormal_cayley hA) g v‖ = 0 := by
    have h2 : (‖cfcHom (isStarNormal_cayley hA) g v‖ : ℝ) ^ 2 = 0 := by
      exact_mod_cast hnorm
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  simpa using norm_eq_zero.mp hz

/-- On the `B` side the damped separator converges strongly to the identity.
The separator is `1` on `B`'s spectrum, almost every Cayley point has its
coordinate there, and almost every Cayley point differs from the singularity
`1`, where the damping factor would otherwise kill the symbol. -/
theorem tendsto_cfcHom_separator (hB : IsSelfAdjoint B) (f : C(ℝ, ℝ))
    (hfB : Set.EqOn f 1 (Complex.ofReal ⁻¹' spectrum B))
    (hf01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (g : ℕ → C(_root_.spectrum ℂ (cayley hB), ℂ))
    (hgval : ∀ n w, g n w = cayleySymbolFun f n (w : ℂ)) (ξ : F) :
    Tendsto (fun n => cfcHom (isStarNormal_cayley hB) (g n) ξ) atTop (nhds ξ) := by
  set hU := isStarNormal_cayley hB with hhU
  set μ := BorelCalculus.diagMeasure hU ξ with hμ
  have hlim : Tendsto
      (fun n => ∫ w, (starRingEnd ℂ) ((g n - 1) w) * ((g n - 1) w) ∂μ) atTop (nhds 0) := by
    have hae : ∀ᵐ w ∂μ, Tendsto
        (fun n => (starRingEnd ℂ) ((g n - 1) w) * ((g n - 1) w)) atTop (nhds 0) := by
      filter_upwards [ae_cayleyInv_mem_spectrum hB ξ,
        MeasureTheory.compl_mem_ae_iff.mpr (diagMeasure_cayley_preimage_one hB ξ)]
        with w hw hw1
      have hfeq : f (cayleyCoordFun (w : ℂ)) = 1 := hfB hw
      have hne : (w : ℂ) ≠ 1 := fun hc => hw1 (by simpa using hc)
      have hconv : Tendsto (fun n => g n w) atTop (nhds 1) := by
        have h2 := tendsto_cayleySymbolFun f hne
        rw [hfeq, Complex.ofReal_one] at h2
        exact h2.congr fun n => (hgval n w).symm
      have hg : Tendsto (fun n => (g n - 1) w) atTop (nhds 0) := by
        have hd := hconv.sub (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop (α := ℕ)))
        rw [sub_self] at hd
        exact hd.congr fun n => by simp
      have hc := (Complex.continuous_conj.tendsto (0 : ℂ)).comp hg
      have hmul := hc.mul hg
      rw [map_zero, zero_mul] at hmul
      exact hmul
    have hbound : ∀ n, ∀ᵐ w ∂μ,
        ‖(starRingEnd ℂ) ((g n - 1) w) * ((g n - 1) w)‖ ≤ 4 := by
      intro n
      filter_upwards with w
      have hle1 : ‖g n w‖ ≤ 1 := by
        rw [hgval n w]; exact norm_cayleySymbolFun_le f hf01 n _
      have h1 : ‖(g n - 1) w‖ ≤ 2 := by
        have hval : (g n - 1) w = g n w - 1 := by simp
        rw [hval]
        calc ‖g n w - 1‖ ≤ ‖g n w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ 2 := by rw [norm_one]; linarith
      rw [norm_mul, RCLike.norm_conj]
      nlinarith [norm_nonneg ((g n - 1) w)]
    have hconv := MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := fun _ => (4 : ℝ))
      (fun n => (((g n - 1).continuous.star).mul (g n - 1).continuous).aestronglyMeasurable)
      (integrable_const _) hbound hae
    rw [integral_zero] at hconv
    exact hconv
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ n, ((‖cfcHom hU (g n) ξ - ξ‖ ^ 2 : ℝ) : ℂ)
      = ∫ w, (starRingEnd ℂ) ((g n - 1) w) * ((g n - 1) w) ∂μ := by
    intro n
    have hsub : cfcHom hU (g n) ξ - ξ = cfcHom hU (g n - 1) ξ := by
      rw [map_sub]
      simp
    rw [hsub]
    exact norm_sq_cfcHom_apply hU (g n - 1) ξ
  have hcx : Tendsto (fun n => ((‖cfcHom hU (g n) ξ - ξ‖ ^ 2 : ℝ) : ℂ)) atTop (nhds 0) := by
    exact hlim.congr fun n => (hsq n).symm
  have hreal : Tendsto (fun n => ‖cfcHom hU (g n) ξ - ξ‖ ^ 2) atTop (nhds 0) := by
    have hre := (Complex.continuous_re.tendsto (0 : ℂ)).comp hcx
    simpa [Function.comp_def, ← Complex.ofReal_pow, Complex.ofReal_re] using hre
  have hsqrt := hreal.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using hsqrt

/-- **Rosenblum's theorem for self-adjoint partial maps.**  A bounded operator
intertwining two self-adjoint operators with disjoint spectra is zero. -/
theorem eq_zero_of_intertwines_of_disjoint_spectrum
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {X : F →L[ℂ] E}
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y))
    (hdisj : Disjoint (spectrum A) (spectrum B)) :
    X = 0 := by
  obtain ⟨f, hfA, hfB, hf01⟩ := exists_spectralSeparator (A := A) (B := B) hdisj
  set K : Set ℂ := _root_.spectrum ℂ (cayley hA) ∪ _root_.spectrum ℂ (cayley hB) with hKdef
  have hKc : IsCompact K :=
    (spectrum.isCompact (cayley hA)).union (spectrum.isCompact (cayley hB))
  have huK : _root_.spectrum ℂ (cayley hA) ⊆ K := Set.subset_union_left
  have hvK : _root_.spectrum ℂ (cayley hB) ⊆ K := Set.subset_union_right
  have hcont : ∀ n : ℕ, Continuous fun w : K => cayleySymbolFun f n (w : ℂ) :=
    fun n => (continuous_cayleySymbolFun f hf01 n).comp continuous_subtype_val
  set G : ℕ → C(K, ℂ) := fun n => ⟨_, hcont n⟩ with hGdef
  refine ContinuousLinearMap.ext fun ξ => ?_
  -- the `A`-side calculus vanishes outright, for every `n`
  have hAzero : ∀ n, cfcHom (isStarNormal_cayley hA) (symbolRestrict huK (G n)) = 0 := fun n =>
    cfcHom_separator_eq_zero hA f hfA n _ (fun _ => rfl)
  -- so the intertwining kills the `B`-side image
  have hXzero : ∀ n,
      X (cfcHom (isStarNormal_cayley hB) (symbolRestrict hvK (G n)) ξ) = 0 := by
    intro n
    have h := cfcHom_cayley_intertwines hA hB hmaps hint hKc huK hvK (G n)
    have h2 := congrArg (fun T : F →L[ℂ] E => T ξ) h
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at h2
    rw [h2, hAzero n]
    simp
  -- while the `B`-side calculus converges strongly to the identity
  have hBlim := tendsto_cfcHom_separator hB f hfB hf01
    (fun n => symbolRestrict hvK (G n)) (fun _ _ => rfl) ξ
  have hXlim : Tendsto
      (fun n => X (cfcHom (isStarNormal_cayley hB) (symbolRestrict hvK (G n)) ξ))
      atTop (nhds (X ξ)) := (X.continuous.tendsto _).comp hBlim
  have hconst : Tendsto (fun _ : ℕ => (0 : E)) atTop (nhds (X ξ)) :=
    hXlim.congr fun n => hXzero n
  have hzero : X ξ = 0 := (tendsto_nhds_unique tendsto_const_nhds hconst).symm
  simpa using hzero

end Main

end LinearPMap
end TauCeti
