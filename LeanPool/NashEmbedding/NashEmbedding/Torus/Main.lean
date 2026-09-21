/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic
import LeanPool.NashEmbedding.NashEmbedding.Torus.Approximation.RealizeMetric
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.Main
import LeanPool.NashEmbedding.NashEmbedding.Torus.FreeEmbedding
import LeanPool.NashEmbedding.NashEmbedding.Torus.Assembly

/-!
# Nash's isometric-embedding theorem for the flat torus `𝕋ⁿ`

For every positive-definite smooth `2πℤⁿ`-periodic Riemannian metric `g` on `ℝⁿ`, there
is a smooth periodic injective embedding `u : ℝⁿ → ℝᴺ` (injective modulo `2πℤⁿ`, with
first partials linearly independent everywhere) such that `∂ᵢu · ∂ⱼu = gᵢⱼ` pointwise.

Following Wassermann §7, the proof combines:
* Theorem A (`realizable_approx_all_s`) — every smooth metric is an `H^s`-limit of realizable ones;
* Theorem B (`gunther_perturbation`) — a free embedding `u₀` can be perturbed to realize `∂u₀·∂u₀ +
  h`
  for small `h`;
* the closure/combining lemmas in `RealizableMetrics.lean` (`realizable_sum`,
  `realizable_nonneg_smul`, `injRealizable_promotion`, `flatTorusEmb_injRealizes`);
* the glue in `Assembly.lean` (`hSize` ↔ `sobolevNormSqDistrib` bridge, the splitting
  `exists_delta_posDef_sub`, `gramMetric_isPosDefSmoothMetric`);
* the free embedding `freeEmb n : ℝⁿ → ℝ^(n²+n)` from `FreeEmbedding.lean`.

The injective piece comes from adjoining a `√δ'`-scaled flat-torus embedding.

## Main statements

* `nashTorus` — Nash's theorem for the flat torus: every positive-definite smooth
  `2πℤⁿ`-periodic metric is injectively realizable.
-/

open scoped BigOperators ContDiff
open NashEmbedding.Sobolev Matrix

noncomputable section

namespace NashEmbedding

variable {n : ℕ}

/-! ## Positive scaling of `IsInjRealizable` -/

/-- Scaling by a positive constant preserves `IsInjRealizable`: if `u : ℝⁿ → ℝᴺ` is an
injective embedding realizing `g` and `t > 0`, then `√t · u` is an injective embedding
realizing `t • g`. -/
lemma injRealizable_pos_smul {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {t : ℝ} (hg : IsInjRealizable g) (ht : 0 < t) : IsInjRealizable (t • g) := by
  obtain ⟨N, u, ⟨hu_sp, hu_inj, hu_fr⟩, hu_r⟩ := hg
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_ne : Real.sqrt t ≠ 0 := hsqrt_pos.ne'
  refine ⟨N, fun x => Real.sqrt t • u x, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- SmoothPeriodic
    refine ⟨hu_sp.smooth.const_smul _, fun x k => ?_⟩
    show Real.sqrt t • u (x + periodicShift n k) = Real.sqrt t • u x
    rw [hu_sp.periodic x k]
  · -- IsInjectiveMod2Pi
    intro x y hxy
    exact hu_inj x y (smul_right_injective (Fin N → ℝ) hsqrt_ne hxy)
  · -- HasFullRankDeriv
    intro x
    have hpd : ∀ i, partialDeriv i (fun y => Real.sqrt t • u y) x
        = Real.sqrt t • partialDeriv i u x := by
      intro i
      have hdiff : DifferentiableAt ℝ u x :=
        (hu_sp.smooth.differentiable NashEmbedding.Sobolev.infty_ne_zero).differentiableAt
      have hhfa : HasFDerivAt (fun y => Real.sqrt t • u y)
          (Real.sqrt t • fderiv ℝ u x) x :=
        hdiff.hasFDerivAt.const_smul (Real.sqrt t)
      change fderiv ℝ (fun y => Real.sqrt t • u y) x (Pi.single i 1)
        = Real.sqrt t • fderiv ℝ u x (Pi.single i 1)
      rw [hhfa.fderiv]
      rfl
    have hpd_fn :
        (fun i : Fin n => partialDeriv i (fun y => Real.sqrt t • u y) x)
          = fun i => Real.sqrt t • partialDeriv i u x := funext hpd
    rw [hpd_fn]
    exact (hu_fr x).units_smul (fun _ => Units.mk0 (Real.sqrt t) hsqrt_ne)
  · -- Realizes (t • g)
    intro x i j
    have hpd : ∀ i, partialDeriv i (fun y => Real.sqrt t • u y) x
        = Real.sqrt t • partialDeriv i u x := by
      intro i
      have hdiff : DifferentiableAt ℝ u x :=
        (hu_sp.smooth.differentiable NashEmbedding.Sobolev.infty_ne_zero).differentiableAt
      have hhfa : HasFDerivAt (fun y => Real.sqrt t • u y)
          (Real.sqrt t • fderiv ℝ u x) x :=
        hdiff.hasFDerivAt.const_smul (Real.sqrt t)
      change fderiv ℝ (fun y => Real.sqrt t • u y) x (Pi.single i 1)
        = Real.sqrt t • fderiv ℝ u x (Pi.single i 1)
      rw [hhfa.fderiv]
      rfl
    rw [hpd i, hpd j, smul_dotProduct, dotProduct_smul, hu_r x i j]
    change Real.sqrt t * (Real.sqrt t * g x i j) = (t • g) x i j
    rw [show (t • g) x i j = t * g x i j from by
      simp [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]]
    rw [← mul_assoc, Real.mul_self_sqrt ht.le]

/-! ## Symmetry / smooth-periodic algebra bridges -/

/-- Real positive-definite matrices are symmetric. -/
lemma isSymm_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (h : A.PosDef) : A.IsSymm := by
  have hH : A.IsHermitian := h.1
  change Aᵀ = A
  ext i j
  have h1 : Aᴴ i j = A i j := congrFun (congrFun hH i) j
  simp only [Matrix.conjTranspose_apply, star_trivial] at h1
  exact h1

/-- Symmetry of a scalar-times-difference of symmetric matrices (over `ℝ`). -/
lemma isSymm_smul_sub_of_isSymm {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) (c : ℝ) : (c • (A - B)).IsSymm := by
  ext i j
  have hAij : A j i = A i j := congrFun (congrFun hA i) j
  have hBij : B j i = B i j := congrFun (congrFun hB i) j
  simp only [transpose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  rw [hAij, hBij]

/-- Smooth periodic scalar-times-difference of matrix-valued smooth periodic maps. -/
lemma smoothPeriodic_smul_sub_matrix {A B : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hA : SmoothPeriodic A) (hB : SmoothPeriodic B) (c : ℝ) :
    SmoothPeriodic (c • (A - B)) := by
  refine ⟨?_, ?_⟩
  · change ContDiff ℝ ∞ (fun y => c • (A y - B y))
    refine contDiff_matrix fun i j => ?_
    exact contDiff_const.mul (((contDiff_apply _ _ j).comp ((contDiff_apply _ _ i).comp
        (hA.smooth.sub hB.smooth))))
  · intro x k
    change c • (A (x + periodicShift n k) - B (x + periodicShift n k))
        = c • (A x - B x)
    rw [hA.periodic x k, hB.periodic x k]

/-- Adding two smooth periodic maps into a normed space stays smooth periodic. -/
lemma smoothPeriodic_add_pointwise {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u v : (Fin n → ℝ) → V} (hu : SmoothPeriodic u) (hv : SmoothPeriodic v) :
    SmoothPeriodic (u + v) := by
  refine ⟨hu.smooth.add hv.smooth, ?_⟩
  intro x k
  change u (x + periodicShift n k) + v (x + periodicShift n k) = u x + v x
  rw [hu.periodic x k, hv.periodic x k]

/-! ## Nash for `𝕋ⁿ` -/

/-- **Nash's isometric-embedding theorem for the flat torus `𝕋ⁿ`.**

For every positive-definite smooth `2πℤⁿ`-periodic Riemannian metric `g` on `ℝⁿ`, there is
a smooth periodic injective embedding `u : ℝⁿ → ℝᴺ` (injective modulo `2πℤⁿ`, with first
partials linearly independent everywhere) such that `∂ᵢu·∂ⱼu = gᵢⱼ` pointwise. -/
theorem nashTorus (hn : 0 < n) {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsPosDefSmoothMetric g) : IsInjRealizable g := by
  classical
  -- Free embedding u₀ and its Gram metric g₀.
  set u₀ : (Fin n → ℝ) → (Fin (freeDim n) → ℝ) := freeEmb n
  have hu₀_sp : SmoothPeriodic u₀ := freeEmb_smoothPeriodic n
  have hu₀_free : IsFree u₀ := freeEmb_isFree n
  set g₀ : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := gramMetric u₀
  have hg₀_sp : SmoothPeriodic g₀ := gramMetric_smoothPeriodic hu₀_sp
  have hg₀_symm : ∀ x, (g₀ x).IsSymm := fun x => gramMetric_symm u₀ x
  -- flatMetric is smooth periodic and symmetric.
  have hflat_sp : SmoothPeriodic (flatMetric n) :=
    flatMetric_isPosDefSmoothMetric.smoothPeriodic
  have hflat_symm : ∀ x, (flatMetric n x).IsSymm := fun _ => by
    change ((1 : Matrix (Fin n) (Fin n) ℝ)).IsSymm
    ext i j; simp [transpose_apply, Matrix.one_apply, eq_comm]
  -- Step 1: split off a bit of the flat metric.
  obtain ⟨δ', hδ'_pos, hg₁⟩ := exists_delta_posDef_sub hg hflat_sp hflat_symm
  set g₁ : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := g - δ' • flatMetric n
  -- Step 2: split off a bit of g₀ from g₁.
  obtain ⟨δ, hδ_pos, hg_res⟩ := exists_delta_posDef_sub hg₁ hg₀_sp hg₀_symm
  set g_res : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := g₁ - δ • g₀
  have hg_res_ism : IsSmoothMetric g_res := hg_res.toIsSmoothMetric
  have hg_res_sp : SmoothPeriodic g_res := hg_res.smoothPeriodic
  have hg_res_symm : ∀ x, (g_res x).IsSymm := fun x => isSymm_of_posDef (hg_res.posDef x)
  -- Step 3: get ε from Theorem B on u₀.
  obtain ⟨ε, hε_pos, hB⟩ := gunther_perturbation (n := n) hn hu₀_sp hu₀_free
  -- Step 4: choose η = δ · √ε / 2.
  set η : ℝ := δ * Real.sqrt ε / 2
  have hη_pos : 0 < η :=
    div_pos (mul_pos hδ_pos (Real.sqrt_pos.mpr hε_pos)) (by norm_num)
  -- Step 5: realizable_approx_all_s on g_res at s = bLevel n, with η.
  obtain ⟨N_A, u_A, hu_A_sp, hu_A_mem, hu_A_bound⟩ :=
    realizable_approx_all_s hn hg_res_ism ((bLevel n : ℕ) : ℝ) hη_pos
  -- Step 6: h := (1/δ) • (g_res - gramMetric u_A).
  set g_uA : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := gramMetric u_A
  have hg_uA_sp : SmoothPeriodic g_uA := gramMetric_smoothPeriodic hu_A_sp
  have hg_uA_symm : ∀ x, (g_uA x).IsSymm := fun x => gramMetric_symm u_A x
  set h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := (1 / δ) • (g_res - g_uA)
  have hh_sp : SmoothPeriodic h := smoothPeriodic_smul_sub_matrix hg_res_sp hg_uA_sp (1 / δ)
  have hh_symm : ∀ x, (h x).IsSymm := fun x =>
    isSymm_smul_sub_of_isSymm (hg_res_symm x) (hg_uA_symm x) (1 / δ)
  have hh_size : hSize n h < ε := by
    have hδ_ne : δ ≠ 0 := hδ_pos.ne'
    -- Step A: hSize n h = (1/δ)² · hSize n (g_res - g_uA).
    have h_A : hSize n h = (1 / δ) ^ 2 * hSize n (g_res - g_uA) := hSize_smul (1/δ) _
    -- Step B: hSize n (g_res - g_uA) = hSize n (g_uA - g_res)  (via (-1)² = 1).
    have h_B : hSize n (g_res - g_uA) = hSize n (g_uA - g_res) := by
      have hflip : g_uA - g_res = (-1 : ℝ) • (g_res - g_uA) := by
        ext x i j
        simp [Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [hflip, hSize_smul]; ring
    -- Step C: hSize n (g_uA - g_res) = ∑ᵢⱼ ‖gramDefect u_A g_res i j‖²_(bLevel n).
    -- The integrand `(g_uA - g_res) x i j = ∂ᵢu_A · ∂ⱼu_A - g_res x i j` matches gramDefect.
    have h_C : hSize n (g_uA - g_res) = ∑ i : Fin n, ∑ j : Fin n,
        sobolevNormSqDistrib n ((bLevel n : ℕ) : ℝ) (gramDefect n u_A g_res i j) := by
      rw [hSize_eq_sum_sobolevNormSqDistrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rfl
    rw [h_A, h_B, h_C]
    -- Now: (1/δ)² · (∑ ‖gramDefect‖²) < ε
    have hbnd : (1/δ)^2 * (∑ i : Fin n, ∑ j : Fin n,
          sobolevNormSqDistrib n ((bLevel n : ℕ) : ℝ) (gramDefect n u_A g_res i j))
        < (1/δ)^2 * η^2 :=
      mul_lt_mul_of_pos_left hu_A_bound (by positivity)
    have h_key : (1/δ)^2 * η^2 = ε / 4 := by
      change (1/δ)^2 * (δ * Real.sqrt ε / 2)^2 = ε / 4
      have hε_sq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε_pos.le
      field_simp
      nlinarith [hε_sq]
    linarith
  -- Step 7: apply Theorem B on u₀ with h.
  obtain ⟨v, hv_sp, hv_realize⟩ := hB h hh_sp hh_symm hh_size
  have h_uv_sp : SmoothPeriodic (u₀ + v) := smoothPeriodic_add_pointwise hu₀_sp hv_sp
  -- Step 8: gramMetric(u₀+v) = g₀ + h, so g₁ = δ • gramMetric(u₀+v) + gramMetric u_A.
  have h_uv_gram : gramMetric (u₀ + v) = g₀ + h := by
    funext x i j
    change pderiv i (u₀ + v) x ⬝ᵥ pderiv j (u₀ + v) x = g₀ x i j + h x i j
    exact hv_realize x i j
  have hg₁_eq : g₁ = δ • gramMetric (u₀ + v) + g_uA := by
    have hδ_ne : δ ≠ 0 := hδ_pos.ne'
    rw [h_uv_gram]
    ext x i j
    -- Goal: g₁ x i j = δ · (g₀ + h) x i j + g_uA x i j
    have hh_val : h x i j = (1 / δ) * (g_res x i j - g_uA x i j) := by
      change ((1 / δ) • (g_res - g_uA)) x i j = _
      simp [Pi.smul_apply, Matrix.smul_apply, Pi.sub_apply, Matrix.sub_apply, smul_eq_mul]
    have hg_res_val : g_res x i j = g₁ x i j - δ * g₀ x i j := by
      change (g₁ - δ • g₀) x i j = _
      simp [Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hh_val, hg_res_val]
    field_simp
    ring
  -- Step 9: build up realizability.
  have h_uA_r : IsRealizable g_uA := ⟨N_A, u_A, hu_A_sp, realizes_gramMetric u_A⟩
  have h_uv_r : IsRealizable (gramMetric (u₀ + v)) :=
    ⟨_, u₀ + v, h_uv_sp, realizes_gramMetric (u₀ + v)⟩
  have h_deluv_r : IsRealizable (δ • gramMetric (u₀ + v)) :=
    realizable_nonneg_smul h_uv_r hδ_pos.le
  have h_g1_r : IsRealizable g₁ := hg₁_eq ▸ realizable_sum h_deluv_r h_uA_r
  -- Step 10: adjoin the scaled flat piece for injectivity.
  have h_flat_inj_r : IsInjRealizable (δ' • flatMetric n) :=
    injRealizable_pos_smul flatTorusEmb_injRealizes hδ'_pos
  -- g = δ' • flatMetric + g₁, so IsInjRealizable g via injRealizable_promotion.
  have hg_eq : g = δ' • flatMetric n + g₁ := by
    change g = δ' • flatMetric n + (g - δ' • flatMetric n)
    ext x i j
    simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply]
  rw [hg_eq]
  exact injRealizable_promotion h_flat_inj_r h_g1_r

end NashEmbedding

end
