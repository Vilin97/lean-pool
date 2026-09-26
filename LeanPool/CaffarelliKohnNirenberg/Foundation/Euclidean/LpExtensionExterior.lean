/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZInputs
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionInputCast
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionPairingKernel
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondExterior
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtension

/-!
# Lp Extension Exterior

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology Convolution Pointwise
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN
open CKN.Foundation.Heat

/-- Negative second spatial derivative of the Newtonian kernel for the exterior representation. -/
def lpExtensionExteriorExteriorKernel (i j : Fin 3) : Vec3 → ℝ :=
  -spatialDeriv (spatialDeriv newtonianKernel i) j

private lemma mollify_support_subset {b : Vec3 → ℝ} {A : Set Vec3} {δ ε : ℝ}
    (hε : 0 < ε) (hbA : ∀ y ∉ A, b y = 0) (hεA : ε ≤ δ) :
    Function.support (mollify b ε hε) ⊆
      Metric.closedBall (0 : Vec3) δ + closure A := by
  exact _root_.CKN.mollify_support_subset hε hbA hεA

private lemma thickening_compact {A : Set Vec3} (hAb : Bornology.IsBounded A)
    {δ : ℝ} :
    IsCompact (Metric.closedBall (0 : Vec3) (δ / 12) + closure A) := by
  exact (isCompact_closedBall (0 : Vec3) (δ / 12)).add hAb.isCompact_closure

private lemma thickening_separated {A U : Set Vec3} {δ : ℝ}
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y))
    (hδ : 0 < δ) :
    ∀ x ∈ U, ∀ y ∈ Metric.closedBall (0 : Vec3) (δ / 12) + closure A,
      δ / 2 ≤ vec3EuclideanNorm (x - y) := by
  intro x hx y hy
  rcases Set.mem_add.mp hy with ⟨z, hz, a, ha, rfl⟩
  have hcl : ∀ a ∈ closure A, δ ≤ vec3EuclideanNorm (x - a) := by
    intro a ha
    have hcont : Continuous (fun a : Vec3 => vec3EuclideanNorm (x - a)) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact closure_minimal (hsep x hx) (isClosed_le continuous_const hcont) ha
  have hz' : ‖z‖ ≤ δ / 12 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hza : vec3EuclideanNorm z ≤ δ / 4 := by
    calc
      vec3EuclideanNorm z ≤ 3 * ‖z‖ := euclideanNorm_le_three_mul_space_norm z
      _ ≤ 3 * (δ / 12) := by gcongr
      _ = δ / 4 := by ring
  have htri : vec3EuclideanNorm (x - a) ≤
      vec3EuclideanNorm (x - (z + a)) + vec3EuclideanNorm z := by
    have hdecomp : x - a = (x - (z + a)) + z := by abel
    rw [hdecomp]
    exact vec3EuclideanNorm_triangle _ _
  have hmain : δ ≤ vec3EuclideanNorm (x - (z + a)) + δ / 4 :=
    (hcl a ha).trans (htri.trans (add_le_add_right hza _))
  linarith only [hδ, hmain]

private lemma exterior_kernel_continuous (i j : Fin 3) :
    ContinuousOn (lpExtensionExteriorExteriorKernel i j) {z : Vec3 | z ≠ 0} := by
  intro z hz
  exact (newtonianKernel_spatialDeriv_second_continuousAt hz i j).neg.continuousWithinAt

private lemma integral_norm_le_eLpNorm_of_zero_outside
    {p q : ℝ} (hpq : p.HolderConjugate q) {f : Vec3 → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) {K : Set Vec3} (hK : MeasurableSet K)
    (hKtop : volume K ≠ ⊤) (hzero : ∀ y ∉ K, f y = 0) :
    ∫ y, ‖f y‖ ≤
      (eLpNorm f (ENNReal.ofReal p) volume).toReal *
        (∫ y, ‖K.indicator (fun _ : Vec3 => (1 : ℝ)) y‖ ^ q) ^ (1 / q : ℝ) := by
  have hK' : MemLp (K.indicator (fun _ : Vec3 => (1 : ℝ)))
      (ENNReal.ofReal q) volume :=
    memLp_indicator_const _ hK 1 (Or.inr hKtop)
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := (volume : Measure Vec3))
    hpq hf hK'
  have hprod :
      ∫ y, ‖f y‖ * ‖K.indicator (fun _ : Vec3 => (1 : ℝ)) y‖ =
        ∫ y, ‖f y‖ := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ K
    · simp [Set.indicator_of_mem hy]
    · have hfy : f y = 0 := hzero y hy
      simp [Set.indicator_of_notMem hy, hfy]
  have hnorm := hf.eLpNorm_eq_integral_rpow_norm
    (ENNReal.ofReal_pos.mpr hpq.pos).ne' ENNReal.ofReal_ne_top
  have hnorm' : eLpNorm f (ENNReal.ofReal p) volume =
      ENNReal.ofReal ((∫ y, ‖f y‖ ^ p) ^ (1 / p : ℝ)) := by
    have hpreal : (ENNReal.ofReal p).toReal = p :=
      ENNReal.toReal_ofReal hpq.pos.le
    rw [hpreal] at hnorm
    simpa only [Real.norm_eq_abs, one_div] using hnorm
  calc
    ∫ y, ‖f y‖ =
        ∫ y, ‖f y‖ * ‖K.indicator (fun _ : Vec3 => (1 : ℝ)) y‖ := hprod.symm
    _ ≤ (∫ y, ‖f y‖ ^ p) ^ (1 / p : ℝ) *
        (∫ y, ‖K.indicator (fun _ : Vec3 => (1 : ℝ)) y‖ ^ q) ^
          (1 / q : ℝ) := hholder
    _ = (eLpNorm f (ENNReal.ofReal p) volume).toReal *
        (∫ y, ‖K.indicator (fun _ : Vec3 => (1 : ℝ)) y‖ ^ q) ^
          (1 / q : ℝ) := by
      rw [hnorm']
      rw [ENNReal.toReal_ofReal]
      positivity

private lemma lpExtension_exterior_hTsource_1 :
    ∀ {p C : ℝ},
      0 ≤ C →
        ∀ {h : Foundation.Euclidean.LpExtensionInput (ENNReal.ofReal p) C} {G : Vec3 → ℝ},
          MemLp (m0 := MeasureSpace.toMeasurableSpace) G (ENNReal.ofReal p) volume →
            ∀ (_ : Fact (1 ≤ ENNReal.ofReal p)) (Gₙ : ℕ → Vec3 → ℝ),
              (∀ (n : ℕ),
                  MemLp (m0 := MeasureSpace.toMeasurableSpace) (Gₙ n) (ENNReal.ofReal p) volume) →
                Tendsto
                    (fun (n : ℕ) =>
                      @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace (Gₙ n - G)
                        (ENNReal.ofReal p) volume)
                    atTop (𝓝 0) →
                  Tendsto
                    (fun (n : ℕ) =>
                      @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace
                        (Foundation.Euclidean.lpExtensionOperator ENNReal.ofReal_ne_top h (Gₙ n) -
                          Foundation.Euclidean.lpExtensionOperator ENNReal.ofReal_ne_top h G)
                        (ENNReal.ofReal p) volume)
                    atTop (𝓝 0)
    := by
  intro p C hC h G hG this Gₙ hGₙp hsource
  have hbound : ∀ n, eLpNorm
      (lpExtensionOperator (ENNReal.ofReal_ne_top) h (Gₙ n) -
        lpExtensionOperator (ENNReal.ofReal_ne_top) h G)
      (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (Gₙ n - G) (ENNReal.ofReal p) volume := by
    intro n
    have hdiff := (hGₙp n).sub hG
    have hmem := lpExtensionOperator_memLp (ENNReal.ofReal_ne_top) h hdiff
    have hadd := lpExtensionRepresentative_add_ae
      (ENNReal.ofReal_ne_top) h hdiff hG
    have hdiff_ae : lpExtensionOperator (ENNReal.ofReal_ne_top) h (Gₙ n) -
        lpExtensionOperator (ENNReal.ofReal_ne_top) h G =ᵐ[volume]
        lpExtensionOperator (ENNReal.ofReal_ne_top) h (Gₙ n - G) := by
      have hsum : lpExtensionOperator (ENNReal.ofReal_ne_top) h (Gₙ n) =ᵐ[volume]
          lpExtensionOperator (ENNReal.ofReal_ne_top) h (Gₙ n - G) +
            lpExtensionOperator (ENNReal.ofReal_ne_top) h G := by
        simpa only [lpExtensionOperator, sub_add_cancel] using hadd
      filter_upwards [hsum] with x hx
      have hx' : lpExtensionOperator (ENNReal.ofReal_ne_top) h (Gₙ n) x =
          lpExtensionOperator (ENNReal.ofReal_ne_top) h (Gₙ n - G) x +
            lpExtensionOperator (ENNReal.ofReal_ne_top) h G x := by
        exact hx
      calc
        lpExtensionOperator (ENNReal.ofReal_ne_top) h (Gₙ n) x -
            lpExtensionOperator (ENNReal.ofReal_ne_top) h G x =
            (lpExtensionOperator (ENNReal.ofReal_ne_top) h (Gₙ n - G) x +
              lpExtensionOperator (ENNReal.ofReal_ne_top) h G x) -
              lpExtensionOperator (ENNReal.ofReal_ne_top) h G x := by rw [hx']
        _ = lpExtensionOperator (ENNReal.ofReal_ne_top) h (Gₙ n - G) x := by ring
    rw [eLpNorm_congr_ae hdiff_ae]
    exact CKN.Core.Endgame.eLpNorm_le_of_toLp_norm_le hdiff hmem hC
      (lpExtensionOperator_toLp_bound (ENNReal.ofReal_ne_top) h hdiff)
  have hmul : Tendsto
      (fun n => ENNReal.ofReal C *
        eLpNorm (Gₙ n - G) (ENNReal.ofReal p) volume) atTop
      (nhds (ENNReal.ofReal C * 0)) :=
    ENNReal.Tendsto.const_mul hsource (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using hmul)
  · intro n
    exact bot_le
  · exact hbound

private lemma lpExtension_exterior_hkernel_tendsto_2 :
    ∀ {i j : Fin 3} {G : Vec3 → ℝ} {A U : Set Vec3},
      IsOpen U →
        ∀ {δ : ℝ},
          0 < δ →
            let Kset : Set Vec3 := Metric.closedBall 0 (δ / 12) + closure A;
            (∀ x ∈ U, ∀ y ∈ Kset, δ / 2 ≤ vec3EuclideanNorm (x - y)) →
              (∀ y ∉ Kset, G y = 0) →
                @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace G volume →
                  ∀ (Gₙ : ℕ → Vec3 → ℝ),
                    (∀ (n : ℕ), Function.support (Gₙ n) ⊆ Kset) →
                      (∀ (n : ℕ),
                          @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace (Gₙ n) volume) →
                        (∀ (n : ℕ),
                            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                              (fun (y : Vec3) => Gₙ n y - G y) volume) →
                          Tendsto
                              (fun (n : ℕ) =>
                                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                                  fun (y : Vec3) => ‖Gₙ n y - G y‖)
                              atTop (𝓝 0) →
                            ∀ x ∈ U,
                              Tendsto (β := ℝ)
                                (fun (n : ℕ) =>
                                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                                    fun (y : Vec3) =>
                                    Foundation.Euclidean.lpExtensionExteriorExteriorKernel i j
                                        (x - y) *
                                      Gₙ n y)
                                atTop
                                (𝓝
                                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                                    fun (y : Vec3) =>
                                    Foundation.Euclidean.lpExtensionExteriorExteriorKernel i j
                                        (x - y) *
                                      G y))
    := by
  intro i j G A U hU δ hδ Kset hsepK hGzeroK hGint Gₙ hGₙsupp hGₙint hGdiffint hL1 x hx
  have hbound : ∀ n, ‖(∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * Gₙ n y) -
      ∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * G y‖ ≤
      4 * (4 * Real.pi)⁻¹ * (((δ / 2) / 3) ^ 3)⁻¹ *
        ∫ y, ‖Gₙ n y - G y‖ := by
    intro n
    have hKbd : ∀ y ∈ Kset, ‖lpExtensionExteriorExteriorKernel i j (x - y)‖ ≤
        4 * (4 * Real.pi)⁻¹ * (((δ / 2) / 3) ^ 3)⁻¹ := by
      intro y hy
      have hnorm := euclideanNorm_le_three_mul_space_norm (x - y)
      have hnorm' : vec3EuclideanNorm (x - y) ≤ 3 * ‖x - y‖ := by
        simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using hnorm
      have hspace : (δ / 2) / 3 ≤ ‖x - y‖ := by
        linarith only [hsepK x hx y hy, hnorm']
      have hne : x - y ≠ 0 := by
        intro hzero
        rw [hzero] at hspace
        simp only [norm_zero] at hspace
        exact (not_lt_of_ge hspace) (by positivity)
      have hpow := inv_pow_le_inv_pow_of_le (by positivity : 0 < (δ / 2) / 3)
        hspace 3
      have hcoef : 0 ≤ 4 * (4 * Real.pi)⁻¹ := by positivity
      dsimp [lpExtensionExteriorExteriorKernel]
      rw [abs_neg]
      calc
        |spatialDeriv (spatialDeriv newtonianKernel i) j (x - y)| ≤
            4 * (4 * Real.pi)⁻¹ * (‖x - y‖ ^ 3)⁻¹ :=
          newtonianKernel_spatialDeriv_second_size_bound hne i j
        _ ≤ 4 * (4 * Real.pi)⁻¹ * (((δ / 2) / 3) ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_left hpow hcoef
    have hIntₙ := integrable_smul_kernel_shift (K := lpExtensionExteriorExteriorKernel i j)
      (g := Gₙ n) (A := Kset) (x := x) (exterior_kernel_continuous i j)
      (hGₙint n) (fun y hy => by
        by_contra hne
        exact hy (hGₙsupp n hne)) hKbd
    have hInt := integrable_smul_kernel_shift (K := lpExtensionExteriorExteriorKernel i j)
      (g := G) (A := Kset) (x := x) (exterior_kernel_continuous i j)
      hGint hGzeroK hKbd
    have hIntdiff := integrable_smul_kernel_shift (K := lpExtensionExteriorExteriorKernel i j)
      (g := fun y => Gₙ n y - G y) (A := Kset) (x := x)
      (exterior_kernel_continuous i j) (hGdiffint n)
      (fun y hy => by
        have h₁ : Gₙ n y = 0 := by
          by_contra hne
          exact hy (hGₙsupp n hne)
        rw [h₁, hGzeroK y hy, sub_zero]) hKbd
    have hsub' :
        (∫ y, Gₙ n y • lpExtensionExteriorExteriorKernel i j (x - y)) -
            ∫ y, G y • lpExtensionExteriorExteriorKernel i j (x - y) =
          ∫ y, (Gₙ n y - G y) • lpExtensionExteriorExteriorKernel i j (x - y) := by
      rw [← integral_sub hIntₙ hInt]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    have hsub :
        (∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * Gₙ n y) -
            ∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * G y =
          ∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * (Gₙ n y - G y) := by
      simpa [smul_eq_mul, mul_comm] using hsub'
    rw [hsub]
    have hpot := rieszSecondL2_exterior_potential_bound (i := i) (j := j)
      (hGdiffint n) hU (fun y hy => by
        have h₁ : Gₙ n y = 0 := by
          by_contra hne
          exact hy (hGₙsupp n hne)
        rw [h₁, hGzeroK y hy, sub_zero]) (δ := δ / 2) (by positivity) hsepK hx
    simpa only [Pi.sub_apply, lpExtensionExteriorExteriorKernel, smul_eq_mul, mul_sub] using hpot
  have hQ : Tendsto
      (fun n => 4 * (4 * Real.pi)⁻¹ * (((δ / 2) / 3) ^ 3)⁻¹ *
        ∫ y, ‖Gₙ n y - G y‖) atTop (nhds 0) := by
    simpa only [mul_assoc, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_const_nhds.mul
        (tendsto_const_nhds.mul hL1)))
  have hD : Tendsto
      (fun n => (∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * Gₙ n y) -
        ∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * G y) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa only [neg_zero] using hQ.neg) hQ
    · intro n
      have hn := hbound n
      simpa only [Real.norm_eq_abs] using neg_le_of_abs_le hn
    · intro n
      have hn := hbound n
      simpa only [Real.norm_eq_abs] using le_of_abs_le hn
  simpa only [sub_add_cancel, zero_add] using
    hD.add (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      ∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * G y) atTop
      (nhds (∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * G y)))

private theorem lpExtension_exterior_of_real
    {i j : Fin 3} {p q C : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hpq : p.HolderConjugate q)
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hL2 : RieszSecondL2Input i j)
    {h : LpExtensionInput (ENNReal.ofReal p) C}
    (hT : h.T = rieszSecondL2RawOperator hL2)
    {G : Vec3 → ℝ} (hG : MemLp G (ENNReal.ofReal p) volume)
    (hGc : HasCompactSupport G) {A U : Set Vec3} (hU : IsOpen U)
    (hGA : ∀ y ∉ A, G y = 0) (hAb : Bornology.IsBounded A) {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) :
    lpExtensionOperator (ENNReal.ofReal_ne_top) h G =ᵐ[volume.restrict U]
      (fun x => ∫ y, (-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y) * G y) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  have hp0 : 0 < p := hpq.pos
  let Kset : Set Vec3 := Metric.closedBall (0 : Vec3) (δ / 12) + closure A
  have hKcompact : IsCompact Kset := thickening_compact hAb
  have hKmeas : MeasurableSet Kset := hKcompact.measurableSet
  have hKtop : volume Kset ≠ ⊤ := hKcompact.measure_lt_top.ne
  have hsepK : ∀ x ∈ U, ∀ y ∈ Kset,
      δ / 2 ≤ vec3EuclideanNorm (x - y) :=
    thickening_separated hsep hδ
  have hGzeroK : ∀ y ∉ Kset, G y = 0 := by
    intro y hy
    have hycl : y ∉ closure A := by
      intro hycl
      apply hy
      exact ⟨0, by simp only [mem_closedBall, dist_self]; positivity, y, hycl, by simp⟩
    exact hGA y (fun hya => hycl (subset_closure hya))
  have hGint : Integrable G volume :=
    integrable_of_memLp_hasCompactSupport (ENNReal.one_le_ofReal.mpr hp) hG hGc
  let ε : ℕ → ℝ := fun n => δ / 12 * (1 / ((n : ℝ) + 1))
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hεzero : Tendsto ε atTop (nhds 0) := by
    simpa [ε] using
      (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  let Gₙ : ℕ → Vec3 → ℝ := fun n => mollify G (ε n) (hεpos n)
  have hGₙsupp : ∀ n, Function.support (Gₙ n) ⊆ Kset := by
    intro n
    exact mollify_support_subset (A := A) (δ := δ / 12) (ε := ε n)
      (hεpos n) hGA (by
        dsimp [ε]
        have hden : 0 < (n : ℝ) + 1 := by positivity
        have hone : 1 / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_iff₀ hden]
          norm_num
        simpa using
          (mul_le_mul_of_nonneg_left hone (show 0 ≤ δ / 12 by positivity)))
  have hGₙcontinuous : ∀ n, Continuous (Gₙ n) := by
    intro n
    exact mollify_continuous (hεpos n)
      (hG.locallyIntegrable (ENNReal.one_le_ofReal.mpr hp))
  have hGₙcomp : ∀ n, HasCompactSupport (Gₙ n) := by
    intro n
    exact HasCompactSupport.of_support_subset_isCompact hKcompact (hGₙsupp n)
  have hGₙp : ∀ n, MemLp (Gₙ n) (ENNReal.ofReal p) volume := by
    intro n
    exact (hGₙcontinuous n).memLp_of_hasCompactSupport (hGₙcomp n)
  have hGₙ₂ : ∀ n, MemLp (Gₙ n) (2 : ℝ≥0∞) volume := by
    intro n
    exact (hGₙcontinuous n).memLp_of_hasCompactSupport (hGₙcomp n)
  have hGₙint : ∀ n, Integrable (Gₙ n) volume := by
    intro n
    exact integrable_of_memLp_hasCompactSupport (ENNReal.one_le_ofReal.mpr hp)
      (hGₙp n) (hGₙcomp n)
  have hsource : Tendsto
      (fun n => eLpNorm (Gₙ n - G) (ENNReal.ofReal p) volume) atTop (nhds 0) := by
    change Tendsto (fun n => eLpNorm (fun x => Gₙ n x - G x)
      (ENNReal.ofReal p) volume) atTop (nhds 0)
    simpa [Gₙ] using
      (tendsto_eLpNorm_sub_zero_mollify (p := ENNReal.ofReal p)
        (ENNReal.one_le_ofReal.mpr hp) ENNReal.ofReal_ne_top hG hεzero hεpos)
  have hGdiffint : ∀ n, Integrable (fun y => Gₙ n y - G y) volume := by
    intro n
    change Integrable (Gₙ n - G) volume
    exact (hGₙint n).sub hGint
  have hL1bound : ∀ n, ∫ y, ‖Gₙ n y - G y‖ ≤
      (eLpNorm (Gₙ n - G) (ENNReal.ofReal p) volume).toReal *
        (∫ y, ‖Kset.indicator (fun _ : Vec3 => (1 : ℝ)) y‖ ^ q) ^
          (1 / q : ℝ) := by
    intro n
    have hzero : ∀ y ∉ Kset, Gₙ n y - G y = 0 := by
      intro y hy
      have h₁ : Gₙ n y = 0 := by
        by_contra hne
        exact hy (hGₙsupp n hne)
      rw [h₁, hGzeroK y hy, sub_zero]
    exact integral_norm_le_eLpNorm_of_zero_outside hpq
      ((hGₙp n).sub hG) hKmeas hKtop hzero
  have hL1 : Tendsto (fun n => ∫ y, ‖Gₙ n y - G y‖)
      atTop (nhds 0) := by
    let CK : ℝ :=
      (∫ y, ‖Kset.indicator (fun _ : Vec3 => (1 : ℝ)) y‖ ^ q) ^
        (1 / q : ℝ)
    have hreal : Tendsto
        (fun n => (eLpNorm (Gₙ n - G) (ENNReal.ofReal p) volume).toReal)
        atTop (nhds 0) := by
      apply (ENNReal.tendsto_toReal_zero_iff
        (fun n => ((hGₙp n).sub hG).eLpNorm_ne_top)).mpr
      exact hsource
    have hbound : ∀ n, ∫ y, ‖Gₙ n y - G y‖ ≤
        (eLpNorm (Gₙ n - G) (ENNReal.ofReal p) volume).toReal * CK := by
      intro n
      exact hL1bound n
    have hL1' : Tendsto (fun n => ∫ y, ‖Gₙ n y - G y‖)
        atTop (nhds (0 * CK)) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hreal.mul tendsto_const_nhds)
      · intro n
        simpa [CK] using (integral_nonneg (fun y => norm_nonneg (Gₙ n y - G y)))
      · exact hbound
    simpa only [zero_mul] using hL1'
  have hTsource := @lpExtension_exterior_hTsource_1 p C hC h G hG (by infer_instance) Gₙ hGₙp
    hsource
  have hkernel_tendsto := @lpExtension_exterior_hkernel_tendsto_2 i j G A U hU δ hδ hsepK hGzeroK
    hGint Gₙ hGₙsupp hGₙint hGdiffint hL1
  have hTn_kernel : ∀ n,
      lpExtensionOperator (ENNReal.ofReal_ne_top) h (Gₙ n) =ᵐ[
        volume.restrict U] (fun x =>
          ∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * Gₙ n y) := by
    intro n
    have hrep := lpExtensionRepresentative_ae_eq_T
      (ENNReal.ofReal_ne_top) h (hGₙp n) (hGₙ₂ n)
    rw [hT] at hrep
    have hraw := rieszSecondL2RawOperator_ae_eq hL2 (hGₙ₂ n)
    have hext := rieszSecondL2_exterior_representation hL2 (hGₙ₂ n)
      hU (fun y hy => by
        by_contra hne
        exact hy (hGₙsupp n hne)) hKcompact.isBounded (δ := δ / 2) (by positivity)
      hsepK
    filter_upwards [ae_restrict_of_ae hrep, ae_restrict_of_ae hraw,
      hext] with x hxrep hxraw hxext
    calc
      lpExtensionOperator (ENNReal.ofReal_ne_top) h (Gₙ n) x =
          rieszSecondL2RawOperator hL2 (Gₙ n) x := hxrep
      _ = rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp (Gₙ n) (hGₙ₂ n)) x := hxraw
      _ = ∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * Gₙ n y := hxext
  have hTn_all : ∀ᵐ x ∂volume.restrict U, ∀ n,
      lpExtensionOperator (ENNReal.ofReal_ne_top) h (Gₙ n) x =
        ∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * Gₙ n y := by
    exact ae_all_iff.mpr (fun n => hTn_kernel n)
  obtain ⟨ns, hnsmono, hTae⟩ :=
    ae_subsequence_of_eLpNorm_tendsto_zero (p := ENNReal.ofReal p)
      (ENNReal.ofReal_pos.mpr hpq.pos).ne' (f := fun n =>
        lpExtensionOperator (ENNReal.ofReal_ne_top) h (Gₙ n))
      (g := lpExtensionOperator (ENNReal.ofReal_ne_top) h G) hTsource
  have hIae : ∀ᵐ x ∂volume.restrict U, Tendsto
      (fun n => ∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * Gₙ (ns n) y) atTop
      (nhds (∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * G y)) := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact (hkernel_tendsto x hx).comp hnsmono.tendsto_atTop
  filter_upwards [ae_restrict_of_ae hTae, hTn_all, hIae] with x hxT hxall hxI
  have hxT' : Tendsto
      (fun n => ∫ y, lpExtensionExteriorExteriorKernel i j (x - y) * Gₙ (ns n) y) atTop
      (nhds (lpExtensionOperator (ENNReal.ofReal_ne_top) h G x)) := by
    apply hxT.congr'
    exact Eventually.of_forall (fun n => hxall (ns n))
  exact tendsto_nhds_unique hxT' hxI

theorem rieszSecondP1ExtensionOperator_agrees_exterior
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {G : Vec3 → ℝ} (hG : MemLp G (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hGc : HasCompactSupport G) {A U : Set Vec3} (hU : IsOpen U)
    (hGA : ∀ y ∉ A, G y = 0) (hAb : Bornology.IsBounded A) {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) :
    rieszSecondP1ExtensionOperator hL2 hWeak11 G =ᵐ[volume.restrict U]
      (fun x => ∫ y, (-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y) * G y) := by
  have : Fact (1 ≤ ENNReal.ofReal ((3 : ℝ) / 2)) := ⟨by norm_num⟩
  have hT : (rieszSecondP1ExtensionInput hL2 hWeak11).T =
      rieszSecondL2RawOperator hL2 := by
    simp only [rieszSecondP1ExtensionInput]
    dsimp only [czP1Constant, id]
    rw [CKN.Foundation.Euclidean.lpExtensionInput_mp_T (by norm_num [czP1Constant])]
    rfl
  have hC : 0 ≤ czP1Constant rieszSecondWeakTypeConstant 1 := by
    unfold czP1Constant
    positivity
  change lpExtensionOperator (p := ENNReal.ofReal ((3 : ℝ) / 2))
      (by norm_num) (rieszSecondP1ExtensionInput hL2 hWeak11) G =ᵐ[volume.restrict U] _
  exact lpExtension_exterior_of_real (i := i) (j := j) (p := (3 : ℝ) / 2) (q := 3)
      (C := czP1Constant rieszSecondWeakTypeConstant 1)
      (by rw [Real.holderConjugate_iff]; norm_num) (by norm_num) hC hL2 hT hG hGc
      hU hGA hAb hδ hsep

theorem rieszSecondGradientExtensionOperator_agrees_exterior
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {G : Vec3 → ℝ} (hG : MemLp G (ENNReal.ofReal ((6 : ℝ) / 5)) volume)
    (hGc : HasCompactSupport G) {A U : Set Vec3} (hU : IsOpen U)
    (hGA : ∀ y ∉ A, G y = 0) (hAb : Bornology.IsBounded A) {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) :
    rieszSecondGradientExtensionOperator hL2 hWeak11 G =ᵐ[volume.restrict U]
      (fun x => ∫ y, (-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y) * G y) := by
  have : Fact (1 ≤ ENNReal.ofReal ((6 : ℝ) / 5)) := ⟨by norm_num⟩
  have hT : (rieszSecondGradientExtensionInput hL2 hWeak11).T =
      rieszSecondL2RawOperator hL2 :=
    rieszSecondGradientExtensionInput_T hL2 hWeak11
  have hC : 0 ≤ czGradientComponentConstant rieszSecondWeakTypeConstant 1 := by
    unfold czGradientComponentConstant
    positivity
  change lpExtensionOperator (p := ENNReal.ofReal ((6 : ℝ) / 5))
      (by norm_num) (rieszSecondGradientExtensionInput hL2 hWeak11) G =ᵐ[volume.restrict U] _
  exact lpExtension_exterior_of_real (i := i) (j := j) (p := (6 : ℝ) / 5) (q := 6)
      (C := czGradientComponentConstant rieszSecondWeakTypeConstant 1)
      (by rw [Real.holderConjugate_iff]; norm_num) (by norm_num) hC hL2 hT hG hGc
      hU hGA hAb hδ hsep

theorem pressureSecondExtensionOperator_agrees_exterior
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j, ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hGc : ∀ i j, HasCompactSupport (G i j)) {A U : Set Vec3} (hU : IsOpen U)
    (hGA : ∀ i j y, y ∉ A → G i j y = 0) (hAb : Bornology.IsBounded A) {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) :
    pressureSecondExtensionOperator hL2 hWeak11 G =ᵐ[volume.restrict U]
      (fun x => ∑ i, ∑ j, ∫ y,
        (-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y) * G i j y) := by
  have hcomponent : ∀ i j,
      rieszSecondP1ExtensionOperator (hL2 i j) (hWeak11 i j) (G i j) =ᵐ[
        volume.restrict U] (fun x => ∫ y,
          (-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y) * G i j y) := by
    intro i j
    exact rieszSecondP1ExtensionOperator_agrees_exterior (hL2 i j) (hWeak11 i j)
      (hG i j) (hGc i j) hU (hGA i j) hAb hδ hsep
  have hAll : ∀ᵐ x ∂volume.restrict U, ∀ i j,
      rieszSecondP1ExtensionOperator (hL2 i j) (hWeak11 i j) (G i j) x =
        (fun x => ∫ y, (-spatialDeriv (spatialDeriv newtonianKernel i) j)
          (x - y) * G i j y) x := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact hcomponent i j
  filter_upwards [hAll] with x hx
  simp only [pressureSecondExtensionOperator, rieszSecondP1ExtensionTensorOperator,
    lpExtensionTensorOperator]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact hx i j

end CKN.Foundation.Euclidean
