/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicCutoffEnergy
public import LeanPool.NavierStokesAndEuler.Euler.MeanVectorIdentities
public import LeanPool.NavierStokesAndEuler.Euler.LpSpatialCutoff

@[expose] public section

/-! Elliptic recovery for classical fields without assuming Sobolev regularity.

The localized identities below require only ordinary smoothness and a compactly
supported scalar cutoff. In particular, they do not assume that derivatives of
the velocity are globally square integrable.
-/

noncomputable section


namespace EulerComparatorRecovery

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal EulerMeanHarmonic EulerMeanVectorIdentities
  EulerMeanCutoffCurl EulerLpTranslation Filter
open scoped ContDiff Topology

/-- Fatou's lemma turns uniform integral bounds on nonnegative localizations
into integrability of the pointwise limit. -/
theorem integrable_and_integral_le_of_nonnegative_limit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : ℕ → X → ℝ) (f : X → ℝ) (C : ℝ)
    (hF : ∀ n, Integrable (F n) μ) (hf : AEStronglyMeasurable f μ)
    (hF0 : ∀ n x, 0 ≤ F n x) (hf0 : ∀ x, 0 ≤ f x)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, (∫ x, F n x ∂μ) ≤ C) : Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have heq (x : X) : liminf (fun n => ENNReal.ofReal (F n x)) atTop =
      ENNReal.ofReal (f x) :=
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim x)).liminf_eq
  have hi : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop := by
    simpa only [heq] using lintegral_liminf_le' (u := (atTop : Filter ℕ))
      (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hb : liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop ≤ ENNReal.ofReal C := by
    apply liminf_le_of_frequently_le'
    apply Frequently.of_forall
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Eventually.of_forall (hF0 n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hfin : HasFiniteIntegral f μ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0)).mpr
      ((hi.trans hb).trans_lt ENNReal.ofReal_lt_top)
  refine ⟨⟨hf, hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hf]
  calc
    _ ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hi.trans hb)
    _ = C := ENNReal.toReal_ofReal ((integral_nonneg (hF0 0)).trans (hbound 0))

/-- The source term retained in the localized Dirichlet identity. -/
theorem localized_dirichlet_identity (η h : Space → ℝ)
    (hcη : HasCompactSupport η) (hη : ContDiff ℝ ∞ η) (hh : ContDiff ℝ ∞ h) :
    (∫ x, ‖gradient (η * h) x‖ ^ 2) =
      (∫ x, h x ^ 2 * ‖gradient η x‖ ^ 2) -
        ∫ x, η x ^ 2 * (h x * Δ h x) := by
  have hcA : HasCompactSupport (fun x => ‖gradient (η * h) x‖ ^ 2) :=
    (compactSupport_gradient (hcη.mul_right (f' := h))).comp_left
      (g := fun v : Space => ‖v‖ ^ 2) (by simp)
  have hA : Integrable (fun x => ‖gradient (η * h) x‖ ^ 2) :=
    ((contDiff_gradient (hη.mul hh)).continuous.norm.pow 2).integrable_of_hasCompactSupport hcA
  have hC := integrable_square_gradient_cutoff η h hcη hη hh.continuous
  have hip := gradient_test_integration_by_parts (gradient h) (contDiff_gradient hh)
    (η * (η * h)) (hcη.mul_right (f' := η * h)) (hη.mul (hη.mul hh))
  simp only [Pi.mul_apply, divergence_gradient_eq_laplacian h hh] at hip
  have hrewrite : (fun x => ⟪gradient (η * (η * h)) x, gradient h x⟫_ℝ) =
      (fun x => ‖gradient (η * h) x‖ ^ 2 - h x ^ 2 * ‖gradient η x‖ ^ 2) := by
    funext x
    linarith [localized_gradient_identity η h hη hh x]
  have hsource : (fun x => η x * (η x * h x) * Δ h x) =
      (fun x => η x ^ 2 * (h x * Δ h x)) := by funext x; ring
  rw [hrewrite, integral_sub hA hC, hsource] at hip
  linarith

/-- Smoothness of the scalar Laplacian follows directly from coordinate
derivatives, with no global integrability premise. -/
theorem scalar_laplacian_smooth (h : Space → ℝ) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (Δ h) := by
  rw [show Δ h = fun x => ∑ i : Fin 3, partialDerivative (partialDerivative h i) i x from
    funext (laplacian_eq_coordinate_sum h hh)]
  exact ContDiff.sum (fun i _ => contDiff_partialDerivative _ (contDiff_partialDerivative h hh i) i)

/-- A smooth square-integrable function whose Laplacian has compact support
has square-integrable first derivatives. The proof first localizes and only
then invokes Fatou; no derivative integrability is assumed. -/
theorem gradient_energy_recovery (M : ℝ)
    (hgrad : ∀ n x, ‖gradient (cutoff n) x‖ ≤ M)
    (h : Space → ℝ) (hh : ContDiff ℝ ∞ h) (hL2 : MemLp h 2 volume)
    (hcΔ : HasCompactSupport (Δ h)) :
    MemLp (gradient h) 2 volume ∧
      (∫ x, ‖gradient h x‖ ^ 2) ≤
        M ^ 2 * (∫ x, h x ^ 2) + ∫ x, |h x * Δ h x| := by
  have hs : Integrable (fun x => |h x * Δ h x|) :=
    (hh.continuous.mul (scalar_laplacian_smooth h
      hh).continuous).abs.integrable_of_hasCompactSupport
      ((hcΔ.mul_left (f := h)).comp_left (g := abs) (abs_zero))
  have hs2 : Integrable (fun x => h x ^ 2) := hL2.integrable_sq
  let F (n : ℕ) (x : Space) : ℝ := ‖gradient (cutoff n * h) x‖ ^ 2
  have hF (n : ℕ) : Integrable (F n) := by
    have hc : HasCompactSupport (fun x => ‖gradient (cutoff n * h) x‖ ^ 2) :=
      (compactSupport_gradient ((cutoff_compact n).mul_right (f' := h))).comp_left
        (g := fun v : Space => ‖v‖ ^ 2) (by simp)
    exact ((contDiff_gradient ((cutoff_smooth n).mul hh)).continuous.norm.pow
      2).integrable_of_hasCompactSupport hc
  have hFbound (n : ℕ) : (∫ x, F n x) ≤ M ^ 2 * (∫ x, h x ^ 2) +
      ∫ x, |h x * Δ h x| := by
    have hcut := integrable_square_gradient_cutoff (cutoff n) h
      (cutoff_compact n) (cutoff_smooth n) hh.continuous
    have hsource : Integrable (fun x => cutoff n x ^ 2 * (h x * Δ h x)) := by
      have hc : HasCompactSupport (fun x => cutoff n x ^ 2 * (h x * Δ h x)) :=
        ((cutoff_compact n).comp_left (g := fun s : ℝ => s ^ 2) (by simp)).mul_right
          (f' := fun x => h x * Δ h x)
      exact (((cutoff_smooth n).continuous.pow 2).mul
        (hh.continuous.mul (scalar_laplacian_smooth h
          hh).continuous)).integrable_of_hasCompactSupport hc
    have hc : (∫ x, h x ^ 2 * ‖gradient (cutoff n) x‖ ^ 2) ≤
        M ^ 2 * ∫ x, h x ^ 2 := by
      rw [← integral_const_mul]
      apply integral_mono hcut (hs2.const_mul (M ^ 2))
      intro x
      have hp := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hgrad n x) 2) (sq_nonneg (h x))
      nlinarith
    have hp : -(∫ x, cutoff n x ^ 2 * (h x * Δ h x)) ≤ ∫ x, |h x * Δ h x| := by
      rw [← integral_neg]
      apply integral_mono hsource.neg hs
      intro x
      have hη := cutoff_bounds n x
      have hη2 : cutoff n x ^ 2 ≤ 1 := by nlinarith
      have hz := sq_nonneg (cutoff n x)
      have ha := neg_le_abs (h x * Δ h x)
      calc
        -(cutoff n x ^ 2 * (h x * Δ h x)) = cutoff n x ^ 2 * (-(h x * Δ h x)) := by ring
        _ ≤ cutoff n x ^ 2 * |h x * Δ h x| := mul_le_mul_of_nonneg_left ha hz
        _ ≤ |h x * Δ h x| := by nlinarith [abs_nonneg (h x * Δ h x)]
    change (∫ x, ‖gradient (cutoff n * h) x‖ ^ 2) ≤ _
    rw [localized_dirichlet_identity (cutoff n) h (cutoff_compact n) (cutoff_smooth n) hh]
    linarith
  have hlim (x : Space) : Tendsto (fun n => F n x) atTop (𝓝 (‖gradient h x‖ ^ 2)) := by
    have hd := cutoffField_fderiv_tendsto h hh x
    have he (n : ℕ) : cutoffField h n = cutoff n * h := by
      funext y
      simp only [cutoffField, smul_eq_mul, Pi.mul_apply]
    simp_rw [he] at hd
    have hg := (toDual ℝ Space).symm.continuous.continuousAt.tendsto.comp hd
    simpa only [F, gradient, Function.comp_def] using hg.norm.pow 2
  have hfatou := integrable_and_integral_le_of_nonnegative_limit volume F (fun x => ‖gradient h x‖
    ^ 2)
    (M ^ 2 * (∫ x, h x ^ 2) + ∫ x, |h x * Δ h x|) hF
    ((contDiff_gradient hh).continuous.norm.pow 2).aestronglyMeasurable
    (fun n x => sq_nonneg _) (fun x => sq_nonneg _) hlim hFbound
  exact ⟨(memLp_two_iff_integrable_sq_norm
    (contDiff_gradient hh).continuous.aestronglyMeasurable).mpr hfatou.1, hfatou.2⟩

/-- A single fixed cutoff constant works for every scalar field. -/
theorem exists_gradient_energy_bound : ∃ M : ℝ, 0 ≤ M ∧
    ∀ (h : Space → ℝ), ContDiff ℝ ∞ h → MemLp h 2 volume →
      HasCompactSupport (Δ h) →
      MemLp (gradient h) 2 volume ∧
        (∫ x, ‖gradient h x‖ ^ 2) ≤
          M ^ 2 * (∫ x, h x ^ 2) + ∫ x, |h x * Δ h x| := by
  obtain ⟨M, hM0, hM⟩ := cutoff_derivative_bound
  have hgrad (n : ℕ) (x : Space) : ‖gradient (cutoff n) x‖ ≤ M := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (hM n x).trans ((mul_le_mul_of_nonneg_left
        (EulerNoncompactTransport.cutoffScale_le_one n) hM0).trans_eq (mul_one M))
  exact ⟨M, hM0, fun h hh hL2 hcΔ => gradient_energy_recovery M hgrad h hh hL2 hcΔ⟩

theorem gradient_memLp_of_laplacian_compact (h : Space → ℝ)
    (hh : ContDiff ℝ ∞ h) (hL2 : MemLp h 2 volume) (hcΔ : HasCompactSupport (Δ h)) :
    MemLp (gradient h) 2 volume := by
  obtain ⟨M, _, hM⟩ := exists_gradient_energy_bound
  exact (hM h hh hL2 hcΔ).1

/-- A convenient quadratic estimate for uniform-in-time bootstrapping: the
constant is independent of the field and of the support of its Laplacian. -/
theorem exists_gradient_energy_square_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (h : Space → ℝ), ContDiff ℝ ∞ h → MemLp h 2 volume →
      HasCompactSupport (Δ h) →
        (∫ x, ‖gradient h x‖ ^ 2) ≤
          C * (∫ x, h x ^ 2) + ∫ x, (Δ h x) ^ 2 := by
  obtain ⟨M, _, hM⟩ := exists_gradient_energy_bound
  refine ⟨M ^ 2 + 1, by positivity, ?_⟩
  intro h hh hL2 hcΔ
  have hs : Integrable (fun x => |h x * Δ h x|) :=
    (hh.continuous.mul (scalar_laplacian_smooth h
      hh).continuous).abs.integrable_of_hasCompactSupport
      ((hcΔ.mul_left (f := h)).comp_left (g := abs) abs_zero)
  have hΔL2 : MemLp (Δ h) 2 volume :=
    (scalar_laplacian_smooth h hh).continuous.memLp_of_hasCompactSupport hcΔ
  have hb : (∫ x, |h x * Δ h x|) ≤ (∫ x, h x ^ 2) + ∫ x, (Δ h x) ^ 2 := by
    rw [← integral_add hL2.integrable_sq hΔL2.integrable_sq]
    apply integral_mono hs (hL2.integrable_sq.add hΔL2.integrable_sq)
    intro x
    change |h x * Δ h x| ≤ h x ^ 2 + (Δ h x) ^ 2
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (h x - Δ h x), sq_nonneg (h x + Δ h x)]
  linarith [(hM h hh hL2 hcΔ).2]

/-- Compact vorticity forces the Laplacian to be compactly supported. No
integrability hypothesis on derivatives of the velocity is used here. -/
theorem laplacian_compact_of_curl_compact (u : Space → Space)
    (hu : ContDiff ℝ ∞ u) (hdiv : ∀ x, divergence u x = 0)
    (hc : HasCompactSupport (vectorCurl u)) : HasCompactSupport (Δ u) := by
  have he : Δ u = -vectorCurl (vectorCurl u) := by
    have hi := vectorCurl_vectorCurl u hu
    have hg : gradient (divergence u) = 0 := by
      rw [show divergence u = (fun _ : Space => (0 : ℝ)) from funext hdiv]
      funext x
      exact gradient_fun_const x 0
    rw [hg, zero_sub] at hi
    rw [hi, neg_neg]
  rw [he]
  exact (vectorCurl_compact _ hc).neg

/-- The Laplacian commutes with every finite coordinate derivative word. -/
theorem laplacian_wordDerivative (word : List (Fin 3)) (h : Space → ℝ)
    (hh : ContDiff ℝ ∞ h) :
    Δ (wordDerivative word h) = wordDerivative word (Δ h) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    change Δ (partialDerivative (wordDerivative word h) i) =
      partialDerivative (wordDerivative word (Δ h)) i
    rw [show Δ (partialDerivative (wordDerivative word h) i) =
      partialDerivative (Δ (wordDerivative word h)) i from
        funext (laplacian_partialDerivative _ (wordDerivative_smooth word h hh) i)]
    rw [ih]

theorem wordDerivative_compact (word : List (Fin 3)) (h : Space → ℝ)
    (hc : HasCompactSupport h) : HasCompactSupport (wordDerivative word h) := by
  induction word with
  | nil => exact hc
  | cons i word ih => exact ih.fderiv_apply ℝ (EuclideanSpace.single i 1)

/-- Every coordinate derivative of a smooth L² scalar with compact Laplacian
is L², proved inductively from the noncircular first-derivative estimate. -/
theorem wordDerivative_memLp_of_laplacian_compact (h : Space → ℝ)
    (hh : ContDiff ℝ ∞ h) (hL2 : MemLp h 2 volume) (hcΔ : HasCompactSupport (Δ h))
    (word : List (Fin 3)) : MemLp (wordDerivative word h) 2 volume := by
  induction word with
  | nil => exact hL2
  | cons i word ih =>
    have hs := wordDerivative_smooth word h hh
    have hc : HasCompactSupport (Δ (wordDerivative word h)) := by
      rw [laplacian_wordDerivative word h hh]
      exact wordDerivative_compact word (Δ h) hcΔ
    have hg := gradient_memLp_of_laplacian_compact _ hs ih hc
    change MemLp (partialDerivative (wordDerivative word h) i) 2 volume
    apply hg.of_le (contDiff_partialDerivative _ hs i).continuous.aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      rw [← gradient_coordinate]
      exact PiLp.norm_apply_le _ i)

/-- Recursive bounds separate the original finite energy from compactly
supported derivatives of the Laplacian. -/
def wordEnergyBound (C : ℝ) (h : Space → ℝ) : List (Fin 3) → ℝ
  | [] => ∫ x, h x ^ 2
  | _ :: word => C * wordEnergyBound C h word +
      ∫ x, wordDerivative word (Δ h) x ^ 2

theorem wordDerivative_energy_le (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (f : Space → ℝ), ContDiff ℝ ∞ f → MemLp f 2 volume →
      HasCompactSupport (Δ f) →
      (∫ x, ‖gradient f x‖ ^ 2) ≤ C * (∫ x, f x ^ 2) + ∫ x, (Δ f x) ^ 2)
    (h : Space → ℝ) (hh : ContDiff ℝ ∞ h) (hL2 : MemLp h 2 volume)
    (hcΔ : HasCompactSupport (Δ h)) (word : List (Fin 3)) :
    (∫ x, wordDerivative word h x ^ 2) ≤ wordEnergyBound C h word := by
  induction word with
  | nil => exact le_rfl
  | cons i word ih =>
    have hs := wordDerivative_smooth word h hh
    have hm := wordDerivative_memLp_of_laplacian_compact h hh hL2 hcΔ word
    have hc : HasCompactSupport (Δ (wordDerivative word h)) := by
      rw [laplacian_wordDerivative word h hh]
      exact wordDerivative_compact word (Δ h) hcΔ
    have hg := gradient_memLp_of_laplacian_compact _ hs hm hc
    have hp := (wordDerivative_memLp_of_laplacian_compact h hh hL2 hcΔ (i :: word)).integrable_sq
    have hmono : (∫ x, wordDerivative (i :: word) h x ^ 2) ≤
        ∫ x, ‖gradient (wordDerivative word h) x‖ ^ 2 := by
      apply integral_mono hp ((memLp_two_iff_integrable_sq_norm
        (contDiff_gradient hs).continuous.aestronglyMeasurable).mp hg)
      intro x
      exact partialDerivative_sq_le_gradient_sq (wordDerivative word h) i x
    have hb := hC (wordDerivative word h) hs hm hc
    rw [laplacian_wordDerivative word h hh] at hb
    change (∫ x, wordDerivative (i :: word) h x ^ 2) ≤
      C * wordEnergyBound C h word + ∫ x, wordDerivative word (Δ h) x ^ 2
    have hi := mul_le_mul_of_nonneg_left ih hC0
    linarith

/-- Uniform finite energy and uniform energies of the compact Laplacian jets
give uniform energies of every velocity jet. The parameter set is arbitrary,
so this applies directly to a compact time interval. -/
theorem wordDerivative_energy_uniform {ι : Type*} (h : ι → Space → ℝ)
    (hs : ∀ t, ContDiff ℝ ∞ (h t)) (hL2 : ∀ t, MemLp (h t) 2 volume)
    (hcΔ : ∀ t, HasCompactSupport (Δ (h t)))
    (h0 : ∃ B : ℝ, ∀ t, (∫ x, h t x ^ 2) ≤ B)
    (hsource : ∀ word : List (Fin 3), ∃ B : ℝ,
      ∀ t, (∫ x, wordDerivative word (Δ (h t)) x ^ 2) ≤ B)
    (word : List (Fin 3)) :
    ∃ B : ℝ, ∀ t, (∫ x, wordDerivative word (h t) x ^ 2) ≤ B := by
  obtain ⟨C, hC0, hC⟩ := exists_gradient_energy_square_bound
  have hbounds (w : List (Fin 3)) : ∃ B : ℝ, ∀ t, wordEnergyBound C (h t) w ≤ B := by
    induction w with
    | nil => exact h0
    | cons i w ih =>
      obtain ⟨B, hB⟩ := ih
      obtain ⟨A, hA⟩ := hsource w
      refine ⟨C * B + A, ?_⟩
      intro t
      change C * wordEnergyBound C (h t) w + ∫ x, wordDerivative w (Δ (h t)) x ^ 2 ≤ C * B + A
      have hi := mul_le_mul_of_nonneg_left (hB t) hC0
      linarith [hA t]
  obtain ⟨B, hB⟩ := hbounds word
  exact ⟨B, fun t => (wordDerivative_energy_le C hC0 hC (h t) (hs t)
    (hL2 t) (hcΔ t) word).trans (hB t)⟩

/-- Every scalar coordinate derivative of a divergence-free smooth finite
energy velocity with compact vorticity is square integrable. -/
theorem component_wordDerivative_memLp (u : Space → Space)
    (hu : ContDiff ℝ ∞ u) (hL2 : MemLp u 2 volume)
    (hdiv : ∀ x, divergence u x = 0) (hc : HasCompactSupport (vectorCurl u))
    (j : Fin 3) (word : List (Fin 3)) :
    MemLp (wordDerivative word (fun x => u x j)) 2 volume := by
  have hs : ContDiff ℝ ∞ (fun x => u x j) := (contDiff_piLp 2).mp hu j
  have hcomp : MemLp (fun x => u x j) 2 volume :=
    hL2.of_le hs.continuous.aestronglyMeasurable (Eventually.of_forall (fun x => PiLp.norm_apply_le
      _ j))
  have hΔ : HasCompactSupport (Δ (fun x => u x j)) := by
    have he : Δ (fun x => u x j) = fun x => (Δ u x) j :=
      funext (fun x => (vector_laplacian_coordinate u hu x j).symm)
    rw [he]
    exact (laplacian_compact_of_curl_compact u hu hdiv hc).comp_left
      (g := fun v : Space => v j) rfl
  exact wordDerivative_memLp_of_laplacian_compact _ hs hcomp hΔ word

/-- Uniform velocity energy and uniform compact Laplacian-jet energies give
uniform bounds for every scalar coordinate jet of a divergence-free velocity. -/
theorem component_wordDerivative_energy_uniform {ι : Type*} (u : ι → Space → Space)
    (hu : ∀ t, ContDiff ℝ ∞ (u t)) (hL2 : ∀ t, MemLp (u t) 2 volume)
    (hdiv : ∀ t x, divergence (u t) x = 0)
    (hc : ∀ t, HasCompactSupport (vectorCurl (u t)))
    (h0 : ∃ B : ℝ, ∀ t, (∫ x, ‖u t x‖ ^ 2) ≤ B)
    (hsource : ∀ (j : Fin 3) (word : List (Fin 3)), ∃ B : ℝ,
      ∀ t, (∫ x, wordDerivative word (fun y => Δ (u t) y j) x ^ 2) ≤ B)
    (j : Fin 3) (word : List (Fin 3)) :
    ∃ B : ℝ, ∀ t, (∫ x, wordDerivative word (fun y => u t y j) x ^ 2) ≤ B := by
  let h (t : ι) (x : Space) : ℝ := u t x j
  have hs (t : ι) : ContDiff ℝ ∞ (h t) := (contDiff_piLp 2).mp (hu t) j
  have hm (t : ι) : MemLp (h t) 2 volume :=
    (hL2 t).of_le (hs t).continuous.aestronglyMeasurable
      (Eventually.of_forall (fun x => PiLp.norm_apply_le _ j))
  have he (t : ι) : Δ (h t) = fun x => Δ (u t) x j :=
    funext (fun x => (vector_laplacian_coordinate (u t) (hu t) x j).symm)
  have hΔ (t : ι) : HasCompactSupport (Δ (h t)) := by
    rw [he t]
    exact (laplacian_compact_of_curl_compact (u t) (hu t) (hdiv t) (hc t)).comp_left
      (g := fun v : Space => v j) rfl
  have hz : ∃ B : ℝ, ∀ t, (∫ x, h t x ^ 2) ≤ B := by
    obtain ⟨B, hB⟩ := h0
    refine ⟨B, fun t => le_trans ?_ (hB t)⟩
    apply integral_mono (hm t).integrable_sq
      ((memLp_two_iff_integrable_sq_norm (hu t).continuous.aestronglyMeasurable).mp (hL2 t))
    intro x
    simpa only [h, Real.norm_eq_abs, sq_abs] using
      pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (u t x) j) 2
  have hsrc (w : List (Fin 3)) : ∃ B : ℝ, ∀ t, (∫ x, wordDerivative w (Δ (h t)) x ^ 2) ≤ B := by
    simpa only [he] using hsource j w
  exact wordDerivative_energy_uniform h hs hm hΔ hz hsrc word

end EulerComparatorRecovery
