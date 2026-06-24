/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.Schwinger.Defs
import LeanPool.OSforGFF.Measure.Construct
import LeanPool.OSforGFF.Measure.IsGaussian
import LeanPool.OSforGFF.Measure.GaussianFreeField -- For gaussian_satisfies_OS2
import LeanPool.OSforGFF.OS.OS2Invariance -- For CovarianceEuclideanInvariantℂ_μ_GFF
import LeanPool.OSforGFF.Covariance.Position  -- For freeCovarianceℂ_bilinear_symm
import LeanPool.OSforGFF.Covariance.Momentum
import LeanPool.OSforGFF.OS.Axioms
import LeanPool.OSforGFF.General.FunctionalAnalysis
import LeanPool.OSforGFF.Spacetime.ComplexTestFunction
import LeanPool.OSforGFF.General.QuantitativeDecay
  -- For schwartz_bilinear_translation_decay_polynomial_proof
import LeanPool.OSforGFF.Spacetime.TimeTranslation  -- For time translation on distributions
import LeanPool.OSforGFF.OS.OS4MGF  -- For shared OS4 infrastructure (no sorries)

/-!
# OS4 — Polynomial Clustering

Proves |𝔼[e^{⟨ω,f⟩+⟨T_s ω,g⟩}] − 𝔼[e^{⟨ω,f⟩}]·𝔼[e^{⟨ω,g⟩}]| ≤ c·(1+s)^{−α} for any α > 0.

The proof follows Steps 1–6 of §4.4.5:

1. Time-translation duality: ⟨T_s ω, g⟩ = ⟨ω, T_{−s}g⟩
2. Gaussian factorization: 𝔼[e^{⟨ω,f+T_{−s}g⟩}] = E_f · E_g · exp(S₂(f, T_{−s}g))
3. Subtract and bound: |…| ≤ |E_f|·|E_g|·|S₂(f,T_{−s}g)|·exp(|S₂(f,T_{−s}g)|)
4. S₂(f,T_{−s}g) = ∫∫ f(x) K(x−y) g(y−τ_s) dy dx with K = free covariance kernel
5. Quantitative decay: |∫∫ f(x) K(x−y) g(y−a) dy dx| ≤ c·(1+‖a‖)^{−α}
   via the convolution decay lemma (domain split at ‖y‖ = ‖x‖/2) applied to the
   exponentially decaying kernel |K(z)| ≤ C·e^{−m‖z‖}
6. Combine with |e^z−1| ≤ |z|·e^{|z|} to close.

## Main result

- `gaussianFreeField_satisfies_OS4`
-/

open MeasureTheory Complex
open scoped Real BigOperators SchwartzMap

noncomputable section

namespace QFT

/-! ## Gaussian Generating Functional Factorization -/

/-- Bilinearity expansion of the Schwinger 2-point function for sums.

    S₂(f+g, f+g) = S₂(f,f) + S₂(f,g) + S₂(g,f) + S₂(g,g)
                 = S₂(f,f) + 2·S₂(f,g) + S₂(g,g)  (by symmetry)

    This uses the bilinearity proved in Measure.IsGaussian.
-/
lemma schwinger2_sum_expansion (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
    SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) (f + g) (f + g) =
      SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f f +
      2 * SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f g +
      SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) g g := by
  -- Use bilinearity from covariance_bilinear_from_general
  have h_bilin := covariance_bilinear_from_general m
  have S2_add_left : ∀ a b c, SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) (a + b) c =
      SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) a c +
      SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) b c :=
    fun a b c => (h_bilin 1 a b c).2.1
  have S2_add_right : ∀ a b c, SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) a (b + c) =
      SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) a b +
      SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) a c :=
    fun a b c => (h_bilin 1 a c b).2.2.2
  -- Use symmetry: S₂(f,g) = S₂(g,f)
  have h_sym : SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) g f =
      SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f g := by
    -- Both equal freeCovarianceℂBilinear, which is symmetric
    rw [gff_two_point_equals_covarianceℂ_free, gff_two_point_equals_covarianceℂ_free]
    exact freeCovarianceℂ_bilinear_symm m g f
  -- Expand
  rw [S2_add_left, S2_add_right, S2_add_right, h_sym]
  ring

/-- For Gaussian measures, the generating functional of a sum factorizes
    up to a cross term:
    Z[f + g] = Z[f] · Z[g] · exp(-⟨f, Cg⟩)

    This follows from expanding ⟨f+g, C(f+g)⟩ = ⟨f,Cf⟩ + 2⟨f,Cg⟩ + ⟨g,Cg⟩.

    Compare with `gaussianFreeField_real_entry_factor` in OS.os3ReflectionPositivity which
    proves the analogous factorization for real test functions.
-/
lemma gff_generating_sum_factorization (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
    GJGeneratingFunctionalℂ (gaussianFreeFieldFree m) (f + g) =
      GJGeneratingFunctionalℂ (gaussianFreeFieldFree m) f *
      GJGeneratingFunctionalℂ (gaussianFreeFieldFree m) g *
      Complex.exp (-SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f g) := by
  -- Use the Gaussian form: Z[h] = exp(-½⟨h, Ch⟩) from gff_complex_generating
  rw [gff_complex_generating m (f + g), gff_complex_generating m f, gff_complex_generating m g]
  -- Apply the bilinear expansion
  rw [schwinger2_sum_expansion m f g]
  -- Algebra: exp(-½(a + 2b + c)) = exp(-½a) · exp(-½c) · exp(-b)
  set a := SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f f
  set b := SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f g
  set c := SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) g g
  have h_exp : Complex.exp (-(1/2 : ℂ) * (a + 2 * b + c)) =
      Complex.exp (-(1/2 : ℂ) * a) * Complex.exp (-(1/2 : ℂ) * c) * Complex.exp (-b) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  exact h_exp

/-! ## Cross Covariance Decay -/

/-! ## Translation as Euclidean Action -/

/-- The inverse of the identity linear isometry is itself. -/
lemma LinearIsometry_inv_one : LinearIsometry.inv (1 : O4) = 1 := by
  have h := LinearIsometry.comp_inv (1 : O4)
  simpa only [LinearIsometry.one_comp] using h

/-! ## Translation Invariance from OS2 -/

/-- For OS2-invariant measures, Z[euclideanAction g f] = Z[f] for any g ∈ E. -/
lemma generating_euclidean_invariant
    (dμ_config : ProbabilityMeasure FieldConfiguration)
    (h_inv : os2EuclideanInvariance dμ_config)
    (g : E) (f : TestFunctionℂ) :
    GJGeneratingFunctionalℂ dμ_config (euclideanAction g f) =
    GJGeneratingFunctionalℂ dμ_config f := (h_inv g f).symm

/-! ## GFF Generating Functional Norm Bound -/

/-- The GFF generating functional has norm at most 1 for **real** test functions.

    For Gaussian measures with positive definite covariance C and real test function f:
    Z[f] = exp(-½⟨f, Cf⟩)

    Since the covariance is positive definite on real functions (⟨f, Cf⟩ ≥ 0),
    we have |Z[f]| = exp(-½⟨f, Cf⟩) ≤ exp(0) = 1.

    NOTE: For complex test functions f = fRe + i*fIm, the bilinear form satisfies
    Re C_bilin(f,f) = C(fRe,fRe) - C(fIm,fIm), which can be negative!
    The bound |Z[f]| ≤ 1 does NOT hold for general complex f.
    Instead, use gff_generating_L2_bound from OS.os1Regularity for the general case.
-/
lemma gff_generating_norm_le_one_real (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    ‖GJGeneratingFunctionalℂ (gaussianFreeFieldFree m) (toComplex f)‖ ≤ 1 := by
  rw [gff_complex_generating m (toComplex f)]
  rw [Complex.norm_exp]
  have h_re : (-(1/2 : ℂ) * SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) (toComplex f) (toComplex
    f)).re =
      -(1/2) * (SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) (toComplex f) (toComplex f)).re := by
    simp [Complex.mul_re]
  rw [h_re, gff_two_point_equals_covarianceℂ_free]
  -- For real test functions, freeCovarianceℂBilinear = freeCovarianceℂ (no conjugation needed)
  have heq : freeCovarianceℂBilinear m (toComplex f) (toComplex f) =
             freeCovarianceℂ m (toComplex f) (toComplex f) := by
    unfold freeCovarianceℂBilinear freeCovarianceℂ
    congr 1; ext x; congr 1; ext y
    have : starRingEnd ℂ (toComplex f y) = toComplex f y := by simp [toComplex_apply]
    rw [this]
  rw [heq]
  have h_nonneg : 0 ≤ (freeCovarianceℂ m (toComplex f) (toComplex f)).re :=
    freeCovarianceℂ_positive m (toComplex f)
  calc Real.exp (-(1/2) * (freeCovarianceℂ m (toComplex f) (toComplex f)).re)
      ≤ Real.exp 0 := by apply Real.exp_le_exp.mpr; nlinarith
    _ = 1 := Real.exp_zero

/-! ## Technical Lemma for OS4 (Real Test Functions) -/

/-- Technical lemma: OS4 bound from cross-term decay for real test functions.

    Given that |S₂(f, T_a g)| < δ with δ ≤ 1, conclude
    |Z[f + T_a g] - Z[f]·Z[g]| < 2δ.

    Uses:
    - Factorization: Z[f + T_a g] = Z[f]·Z[T_a g]·exp(-S₂(f, T_a g))
    - Translation invariance: Z[T_a g] = Z[g] (from OS2)
    - Combined: Z[f + T_a g] = Z[f]·Z[g]·exp(-S₂(f, T_a g))
    - Therefore: Z[f + T_a g] - Z[f]·Z[g] = Z[f]·Z[g]·(exp(-S₂(f, T_a g)) - 1)
    - Real test function bound: |Z[f]| ≤ 1 for real f (positive definite covariance)
    - Exponential estimate: |exp(-z) - 1| ≤ 2|z| for |z| ≤ 1
-/
lemma GFF_OS4_from_small_decay_real (m : ℝ) [Fact (0 < m)]
    (f g : TestFunction) (a : SpaceTime) (δ : ℝ) (_hδ_pos : δ > 0) (hδ_small : δ ≤ 1)
    (h_decay : ‖SchwingerFunction₂ (gaussianFreeFieldFree m) f (g.translate a)‖ < δ) :
    ‖GJGeneratingFunctional (gaussianFreeFieldFree m) (f + g.translate a) -
     GJGeneratingFunctional (gaussianFreeFieldFree m) f *
     GJGeneratingFunctional (gaussianFreeFieldFree m) g‖ < 2 * δ := by
  -- For real test functions, use the Gaussian factorization in complex form
  -- then transfer back using the fact that generating functionals agree
  -- Convert to complex generating functional
  set fC := toComplex f
  set gC := toComplex g
  set T_a_gC := toComplex (g.translate a)
  -- The real generating functional equals the complex one on real test functions
  have h_eq_f : GJGeneratingFunctional (gaussianFreeFieldFree m) f =
                GJGeneratingFunctionalℂ (gaussianFreeFieldFree m) fC :=
    (GJGeneratingFunctionalℂ_toComplex (gaussianFreeFieldFree m) f).symm
  have h_eq_g : GJGeneratingFunctional (gaussianFreeFieldFree m) g =
                GJGeneratingFunctionalℂ (gaussianFreeFieldFree m) gC :=
    (GJGeneratingFunctionalℂ_toComplex (gaussianFreeFieldFree m) g).symm
  have h_eq_sum : GJGeneratingFunctional (gaussianFreeFieldFree m) (f + g.translate a) =
                  GJGeneratingFunctionalℂ (gaussianFreeFieldFree m) (fC + T_a_gC) := by
    rw [← GJGeneratingFunctionalℂ_toComplex, toComplex_add]
  -- Rewrite in terms of complex generating functional
  rw [h_eq_f, h_eq_g, h_eq_sum]
  -- Apply complex factorization
  have h_factor : GJGeneratingFunctionalℂ (gaussianFreeFieldFree m) (fC + T_a_gC) =
      GJGeneratingFunctionalℂ (gaussianFreeFieldFree m) fC *
      GJGeneratingFunctionalℂ (gaussianFreeFieldFree m) T_a_gC *
      Complex.exp (-SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) fC T_a_gC) :=
    gff_generating_sum_factorization m fC T_a_gC
  -- Translation invariance: Z[T_a g] = Z[g]
  have h_OS2 : os2EuclideanInvariance (gaussianFreeFieldFree m) := by
    have h_euc := CovarianceEuclideanInvariantℂ_μ_GFF m
    have h_gauss := isGaussianGJ_gaussianFreeField_free m
    exact gaussian_satisfies_OS2 (gaussianFreeFieldFree m) h_gauss h_euc
  -- T_a_gC = euclideanAction ⟨1, a⟩ gC for the translation
  have h_transl_eq : T_a_gC = euclideanAction ⟨1, a⟩ gC := by
    ext x
    simp only [euclideanAction, SchwartzMap.compCLM_apply,
               Function.comp_apply, euclideanPullback, act]
    simp only [QFT.inv_R, QFT.inv_t, LinearIsometry_inv_one, LinearIsometry.one_apply]
    rfl
  have h_transl : GJGeneratingFunctionalℂ (gaussianFreeFieldFree m) T_a_gC =
                  GJGeneratingFunctionalℂ (gaussianFreeFieldFree m) gC := by
    rw [h_transl_eq]
    exact generating_euclidean_invariant _ h_OS2 ⟨1, a⟩ gC
  -- Combine: Z[fC + T_a_gC] = Z[fC]·Z[gC]·exp(-S₂(fC, T_a_gC))
  set Z := GJGeneratingFunctionalℂ (gaussianFreeFieldFree m)
  set S₂ := SchwingerFunctionℂ₂ (gaussianFreeFieldFree m)
  have h_combined : Z (fC + T_a_gC) = Z fC * Z gC * Complex.exp (-S₂ fC T_a_gC) := by
    rw [h_factor, h_transl]
  have h_diff : Z (fC + T_a_gC) - Z fC * Z gC = Z fC * Z gC * (Complex.exp (-S₂ fC T_a_gC) - 1) :=
    by
    rw [h_combined]; ring
  -- The cross term decay: S₂ fC T_a_gC = ↑(SchwingerFunction₂ f (g.translate a))
  -- This follows from the real-complex correspondence of Schwinger functions
  have h_S2_eq : S₂ fC T_a_gC = ↑(SchwingerFunction₂ (gaussianFreeFieldFree m) f (g.translate a))
    := by
    -- Both are integrals of f(x) C(x,y) g(y) for real test functions
    -- SchwingerFunctionℂ₂ on toComplex gives the same as SchwingerFunction₂ cast to ℂ
    change SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) fC T_a_gC = _
    -- Use the definitions directly:
    -- SchwingerFunctionℂ₂ = ∫ (distributionPairingℂReal ω f) * (distributionPairingℂReal ω g) dμ
    -- For toComplex of real f, distributionPairingℂReal ω (toComplex f) = ↑(distributionPairing ω
    -- f)
    -- SchwingerFunction₂ = ∫ (distributionPairing ω f) * (distributionPairing ω g) dμ
    -- Both integrals agree: ∫ ↑(a * b) dμ = ↑(∫ a * b dμ) when integrable
    simp only [SchwingerFunctionℂ₂, SchwingerFunctionℂ, SchwingerFunction₂, SchwingerFunction,
               Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    -- Convert the integral of complex products to integral of real products cast to ℂ
    have h_fun_eq : (fun ω => distributionPairingℂReal ω fC * distributionPairingℂReal ω T_a_gC) =
        (fun x => (↑(distributionPairing x f * distributionPairing x (g.translate a)) : ℂ)) := by
      ext ω
      -- fC = toComplex f and T_a_gC = toComplex (g.translate a)
      change distributionPairingℂReal ω (toComplex f) * distributionPairingℂReal ω (toComplex
        (g.translate a)) = _
      rw [distributionPairingℂ_real_toComplex, distributionPairingℂ_real_toComplex,
        Complex.ofReal_mul]
    rw [h_fun_eq]
    exact integral_complex_ofReal
  have h_S2_norm : ‖S₂ fC T_a_gC‖ = |SchwingerFunction₂ (gaussianFreeFieldFree m) f (g.translate
    a)| := by
    rw [h_S2_eq, Complex.norm_real, Real.norm_eq_abs]
  have h_S2_small : ‖-S₂ fC T_a_gC‖ ≤ 1 := by
    rw [norm_neg, h_S2_norm, ← Real.norm_eq_abs]
    exact le_of_lt (lt_of_lt_of_le h_decay hδ_small)
  -- For real test functions, |Z[f]| ≤ 1
  have h_Zf_le : ‖Z fC‖ ≤ 1 := gff_generating_norm_le_one_real m f
  have h_Zg_le : ‖Z gC‖ ≤ 1 := gff_generating_norm_le_one_real m g
  -- Final calculation
  calc ‖Z (fC + T_a_gC) - Z fC * Z gC‖
      = ‖Z fC * Z gC * (Complex.exp (-S₂ fC T_a_gC) - 1)‖ := by rw [h_diff]
    _ = ‖Z fC‖ * ‖Z gC‖ * ‖Complex.exp (-S₂ fC T_a_gC) - 1‖ := by rw [norm_mul, norm_mul]
    _ ≤ 1 * 1 * ‖Complex.exp (-S₂ fC T_a_gC) - 1‖ := by
        gcongr
    _ = ‖Complex.exp (-S₂ fC T_a_gC) - 1‖ := by ring
    _ ≤ 2 * ‖-S₂ fC T_a_gC‖ := Complex.norm_exp_sub_one_le h_S2_small
    _ = 2 * |SchwingerFunction₂ (gaussianFreeFieldFree m) f (g.translate a)| := by
        simp [norm_neg, h_S2_norm]
    _ < 2 * δ := by
        apply mul_lt_mul_of_pos_left h_decay
        norm_num

/-! ## Main Theorem: OS4 for Gaussian Free Field -/

/-- Cross covariance decay for real Schwartz functions.

    The 2-point function S₂(f, T_a g) → 0 as |a| → ∞ for Schwartz functions.
    This follows from:
    - The kernel C(z) decays like 1/|z|² at large distances (freeCovarianceKernel_decay_bound)
    - Schwartz functions are L¹ integrable
    - `schwartz_bilinear_translation_decay`

    Uses the covariance representation:
    S₂(f, T_a g) = ∫∫ f(x) · C(x-y) · g(y-a) dx dy
-/
theorem schwartz_cross_covariance_decay_real (m : ℝ) [Fact (0 < m)]
    (f g : TestFunction) (ε : ℝ) (hε : ε > 0) :
    ∃ R > 0, ∀ a : SpaceTime, ‖a‖ > R →
      ‖SchwingerFunction₂ (gaussianFreeFieldFree m) f (g.translate a)‖ < ε := by
  -- Step 1: Get the kernel decay bound
  have hm : 0 < m := Fact.out
  obtain ⟨C, hC_pos, hK_decay⟩ := freeCovarianceKernel_decay_bound m hm
  -- Step 2: Convert the decay bound to the required form
  -- Need: |K(z)| ≤ C / ‖z‖^α for ‖z‖ ≥ R₀
  -- We have: |K(z)| ≤ C * ‖z‖^(-2) for all z
  have hK_decay' : ∀ z : SpaceTime, ‖z‖ ≥ 1 → |freeCovarianceKernel m z| ≤ C / ‖z‖ ^ (2 : ℝ) := by
    intro z hz
    have hbound := hK_decay z
    calc |freeCovarianceKernel m z| ≤ C * ‖z‖ ^ (-2 : ℝ) := hbound
      _ = C * (‖z‖ ^ (2 : ℝ))⁻¹ := by rw [Real.rpow_neg (norm_nonneg z)]
      _ = C / ‖z‖ ^ (2 : ℝ) := by ring
  -- Step 3: Apply the proven theorem for bilinear translation decay
  -- Note: measurability follows from continuity on {0}ᶜ
  have hK_meas : Measurable (freeCovarianceKernel m) :=
    measurable_of_continuousOn_compl_singleton 0 (freeCovarianceKernel_continuousOn m hm)
  -- LocallyIntegrable: follows from global integrability
  have hK_loc : MeasureTheory.LocallyIntegrable (freeCovarianceKernel m) MeasureTheory.volume :=
    (freeCovarianceKernel_integrable m hm).locallyIntegrable
  -- ContinuousOn outside the R₀-ball (where R₀ = 1): follows from ContinuousOn {z ≠ 0}
  have hK_cont : ContinuousOn (freeCovarianceKernel m) (Metric.closedBall (0 : SpaceTime) 1)ᶜ := by
    apply (freeCovarianceKernel_continuousOn m hm).mono
    intro z hz
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
    simp only [Set.mem_setOf_eq, ne_eq]
    exact norm_ne_zero_iff.mp (by linarith)
  have h_decay_tendsto : Filter.Tendsto
      (fun a => ∫ x : SpaceTime, ∫ y : SpaceTime,
        (toComplex f) x * (freeCovarianceKernel m (x - y) : ℂ) * (toComplex g) (y - a))
      (Filter.cocompact SpaceTime)
      (nhds 0) :=
    schwartz_bilinear_translation_decay_proof (toComplex f) (toComplex g)
      (freeCovarianceKernel m) hK_meas hK_loc 2 (by norm_num) C 1 hC_pos (by norm_num) hK_cont
         hK_decay'
  -- Step 4: Convert Filter.Tendsto to ε-δ form
  -- The definition: Tendsto f (cocompact X) (nhds 0) means
  -- for any ε > 0, {a | ‖f a‖ < ε} contains the complement of some compact set
  rw [Metric.tendsto_nhds] at h_decay_tendsto
  have h_eps := h_decay_tendsto ε hε
  -- Filter.Eventually p (cocompact X) means {x | p x} ∈ cocompact X
  rw [Filter.Eventually, Filter.mem_cocompact] at h_eps
  obtain ⟨K, hK_compact, hK_compl⟩ := h_eps
  -- Step 5: K is compact hence bounded; extract a radius R
  obtain ⟨R, hR_bound⟩ := hK_compact.isBounded.subset_ball 0
  use max R 1
  constructor
  · exact lt_max_of_lt_right one_pos
  intro a ha
  -- If ‖a‖ > max R 1, then a ∉ ball 0 R ⊇ K, so a ∈ Kᶜ
  have ha_not_in_K : a ∉ K := by
    intro ha_in
    have := hR_bound ha_in
    simp only [Metric.mem_ball, dist_zero_right] at this
    have : ‖a‖ ≤ R := le_of_lt this
    linarith [lt_of_le_of_lt (le_max_left R 1) ha]
  -- Apply the decay bound from cocompact membership
  have h_int_bound := hK_compl ha_not_in_K
  simp only [Set.mem_setOf_eq, dist_zero_right] at h_int_bound
  -- Step 6: Connect SchwingerFunction₂ to the double integral
  -- SchwingerFunction₂ (GFF) f g = freeCovarianceFormR m f g = ∫∫ f(x) C(x-y) g(y) dx dy
  -- For translated g, this becomes ∫∫ f(x) C(x-y) g(y-a) dx dy
  calc ‖SchwingerFunction₂ (gaussianFreeFieldFree m) f (g.translate a)‖
      = |SchwingerFunction₂ (gaussianFreeFieldFree m) f (g.translate a)| := Real.norm_eq_abs _
    _ = ‖(SchwingerFunction₂ (gaussianFreeFieldFree m) f (g.translate a) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖∫ x : SpaceTime, ∫ y : SpaceTime,
          (toComplex f) x * (freeCovarianceKernel m (x - y) : ℂ) * (toComplex g) (y - a)‖ := by
        -- Step 6a: SchwingerFunction₂ = ∫ ω, (ω f)(ω g') (by schwinger_eq_covariance)
        have h_schwinger1 : SchwingerFunction₂ (gaussianFreeFieldFree m) f (g.translate a)
            = ∫ ω, (distributionPairing ω f) * (distributionPairing ω (g.translate a))
              ∂(gaussianFreeFieldFree m).toMeasure :=
          schwinger_eq_covariance (gaussianFreeFieldFree m) f (g.translate a)
        -- Step 6b: ∫ ω, (ω f)(ω g') = freeCovarianceFormR (by schwinger_eq_covariance_real)
        have h_schwinger2 : ∫ ω, (ω f) * (ω (g.translate a)) ∂(gaussianFreeFieldFree m).toMeasure
            = freeCovarianceFormR m f (g.translate a) :=
          GFFIsGaussian.schwinger_eq_covariance_real m f (g.translate a)
        -- Combine: SchwingerFunction₂ = freeCovarianceFormR
        have h_schwinger : SchwingerFunction₂ (gaussianFreeFieldFree m) f (g.translate a)
            = freeCovarianceFormR m f (g.translate a) := by
          rw [h_schwinger1]
          simpa only [distributionPairing] using h_schwinger2
        -- Step 6c: freeCovarianceFormR uses freeCovariance = freeCovarianceKernel (x - y)
        -- freeCovarianceFormR m f h = ∫∫ f(x) freeCovariance(x,y) h(y) dx dy
        -- and (g.translate a)(y) = g(y - a)
        rw [h_schwinger]
        -- Convert the real integral to complex
        -- Key: freeCovarianceFormR = ∫∫ f(x) * freeCovariance(x,y) * h(y)
        -- and freeCovariance m x y = freeCovarianceKernel m (x - y)
        congr 1
        -- Show: (freeCovarianceFormR m f (g.translate a) : ℂ)
        --     = ∫∫ (toComplex f) x * (freeCovarianceKernel m (x-y) : ℂ) * (toComplex g) (y-a)
        unfold freeCovarianceFormR
        -- Now LHS = (∫∫ f(x) * freeCovariance(x,y) * (g.translate a)(y) : ℂ)
        -- Use translation invariance: freeCovariance m x y = freeCovarianceKernel m (x - y)
        have h_transl_inv : ∀ x y, freeCovariance m x y = freeCovarianceKernel m (x - y) := by
          intro x y
          unfold freeCovarianceKernel freeCovariance freeCovarianceBessel
          simp only [zero_sub, norm_neg]
        -- Use translate_apply: (g.translate a) y = g (y - a)
        simp_rw [SchwartzMap.translate_apply, h_transl_inv, toComplex_apply]
        -- Goal: ↑(∫ x, ∫ y, f x * K(x-y) * g(y-a)) = ∫ x, ∫ y, ↑(f x) * ↑(K(x-y)) * ↑(g(y-a))
        -- First, push ofReal inside the products on the RHS
        have h_prod : ∀ x y,
            (f x : ℂ) * (freeCovarianceKernel m (x - y) : ℂ) * (g (y - a) : ℂ) =
            ((f x * freeCovarianceKernel m (x - y) * g (y - a) : ℝ) : ℂ) := by
          intros; simp only [Complex.ofReal_mul]
        simp_rw [h_prod]
        -- Now both sides have ↑(real products)
        -- Transform using integral_ofReal twice
        have h_inner : ∀ x, (∫ y, (↑(f x * freeCovarianceKernel m (x - y) * g (y - a)) : ℂ))
            = ((∫ y, f x * freeCovarianceKernel m (x - y) * g (y - a) : ℝ) : ℂ) := by
          intro x; exact integral_ofReal
        simp_rw [h_inner]
        exact integral_ofReal.symm
    _ < ε := h_int_bound

/-- The Gaussian Free Field satisfies OS4 clustering.

    The proof combines:
    1. Gaussian factorization: Z[f + T_a g] = Z[f] · Z[T_a g] · exp(-S₂(f, T_a g))
    2. Translation invariance: Z[T_a g] = Z[g]  (from OS2)
    3. Cross term decay: S₂(f, T_a g) → 0 as |a| → ∞
    4. Continuity: exp(-z) → exp(0) = 1 as z → 0
    5. For real test functions: |Z[f]| ≤ 1 (positive definite covariance)
-/
theorem gaussianFreeField_satisfies_OS4 (m : ℝ) [Fact (0 < m)] :
    os4Clustering (gaussianFreeFieldFree m) := by
  intro f g ε hε
  -- Strategy: Use a small decay target δ = min(ε/2, 1/2).
  -- This ensures δ ≤ 1 so the exponential bound |exp(-z) - 1| ≤ 2|z| applies.
  -- Then |Z[f + T_a g] - Z[f]·Z[g]| < 2δ ≤ ε.
  -- Define the decay target
  set δ := min (ε / 2) (1 / 2) with hδ_def
  have hδ_pos : δ > 0 := by simp only [δ, lt_min_iff]; constructor <;> linarith
  have hδ_small : δ ≤ 1 := by
    rw [hδ_def]
    exact le_trans (min_le_right _ _) (by norm_num)
  have hδ_gives_ε : 2 * δ ≤ ε := by
    simp only [δ, min_def]
    split_ifs with h <;> linarith
  -- Get R from cross-covariance decay with target δ
  obtain ⟨R, hR_pos, hR_decay⟩ := schwartz_cross_covariance_decay_real m f g δ hδ_pos
  -- Use R as our bound
  use R, hR_pos
  intro a ha
  -- Apply the decay bound
  have h_S2_small : ‖SchwingerFunction₂ (gaussianFreeFieldFree m) f (g.translate a)‖ < δ :=
    hR_decay a ha
  -- Apply the technical lemma
  have h_bound := GFF_OS4_from_small_decay_real m f g a δ hδ_pos hδ_small h_S2_small
  -- Conclude: 2δ ≤ ε
  calc ‖GJGeneratingFunctional (gaussianFreeFieldFree m) (f + g.translate a) -
         GJGeneratingFunctional (gaussianFreeFieldFree m) f *
         GJGeneratingFunctional (gaussianFreeFieldFree m) g‖
      < 2 * δ := h_bound
    _ ≤ ε := hδ_gives_ε

/-! ## Alternative: Direct (ε-δ) Formulation

These are not used in the main OS4 proof path (which goes through `os4PolynomialClustering`),
but kept as an alternative qualitative formulation of clustering.
-/

/-- Covariance clustering property: the 2-point function decays at large separations. -/
def covarianceClusteringReal (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (f g : TestFunction) (ε : ℝ), ε > 0 →
    ∃ R > 0, ∀ a : SpaceTime, ‖a‖ > R →
      ‖SchwingerFunction₂ dμ_config f (g.translate a)‖ < ε

/-- The free covariance has the clustering property. -/
theorem freeCovarianceClustering_real (m : ℝ) [Fact (0 < m)] :
    covarianceClusteringReal (gaussianFreeFieldFree m) := by
  intro f g ε hε
  exact schwartz_cross_covariance_decay_real m f g ε hε

/-! ## OS4 Polynomial Clustering for GFF

The GFF satisfies polynomial clustering with any decay rate α > 0, because
the underlying covariance has exponential decay (from the mass gap).

The proof uses:
1. Time translation duality: ⟨T_s ω, g⟩ = ⟨ω, T_{-s} g⟩
2. Gaussian factorization: E[e^{⟨ω, f + T_{-s} g⟩}] = Z[f]·Z[g]·exp(-S₂(f, T_{-s} g))
3. The proved theorem `schwartz_bilinear_translation_decay_polynomial_proof` for polynomial bounds
-/

/-! ### Time Translation Infrastructure for Polynomial Clustering

For os4PolynomialClustering, we need to work with time translation of distributions.
The key duality is: ⟨T_s ω, g⟩ = ⟨ω, T_{-s} g⟩

This connects time translation of distributions to translation of test functions.
-/

/-- Time translation vector: shifts only the time coordinate by s.
    timeVector s = (s, 0, 0, 0) in coordinates.
-/
def timeVector (s : ℝ) : SpaceTime :=
  EuclideanSpace.equiv (Fin STDimension) ℝ |>.symm
    (fun i => if i = 0 then s else 0)

/-- Time duality for distribution pairing: ⟨T_s ω, g⟩ = ⟨ω, T_{-s} g⟩.
    This is the fundamental identity connecting time translation of distributions
    to time translation of test functions.

    Note: This uses the definition of timeTranslationDistribution from TimeTranslation.lean,
    which is defined by duality: (T_s ω)(f) = ω(T_{-s} f).

    The proof follows from:
    1. timeTranslationDistribution_apply: (T_s ω)(f) = ω(T_{-s} f) for real test functions
    2. Time translation commutes with taking real/imaginary parts of complex Schwartz functions
-/
lemma time_translation_pairing_duality (s : ℝ) (ω : FieldConfiguration) (g : TestFunctionℂ) :
    distributionPairingℂReal (TimeTranslation.timeTranslationDistribution s ω) g =
    distributionPairingℂReal ω (TimeTranslation.timeTranslationSchwartzℂ (-s) g) := by
  -- Use the proven lemma from OS4Ron
  exact OS4infra.timeTranslationDistribution_pairingℂ s ω g

/-! ### Key Lemmas for Connecting Bilinear Decay to Schwinger Function -/

/-- The time shift constant vector (s, 0, 0, 0) has norm |s|. -/
lemma timeShiftConst_norm (s : ℝ) : ‖TimeTranslation.timeShiftConst s‖ = |s| := by
  simp only [TimeTranslation.timeShiftConst, EuclideanSpace.norm_eq, STDimension, Fin.sum_univ_four,
    (by decide : (0 : Fin 4).val = 0), (by decide : (1 : Fin 4).val ≠ 0),
    (by decide : (2 : Fin 4).val ≠ 0), (by decide : (3 : Fin 4).val ≠ 0), ↓reduceIte,
    Real.norm_eq_abs, sq_abs, zero_pow (by norm_num : 2 ≠ 0), add_zero, Real.sqrt_sq_eq_abs]

/-- Time translation of Schwartz function at a point equals function evaluated at shifted point. -/
lemma timeTranslationSchwartzℂ_at_point (s : ℝ) (g : TestFunctionℂ) (y : SpaceTime) :
    TimeTranslation.timeTranslationSchwartzℂ s g y = g (TimeTranslation.timeShift s y) := by
  rfl

/-- Time shift by s equals adding the time shift constant. -/
lemma timeShift_eq_add (s : ℝ) (y : SpaceTime) :
    TimeTranslation.timeShift s y = y + TimeTranslation.timeShiftConst s := by
  exact TimeTranslation.timeShift_eq_add_const s y

/-- Time translation by -s gives g(y - timeShiftConst(s)). -/
lemma timeTranslationSchwartzℂ_neg_eq_sub (s : ℝ) (g : TestFunctionℂ) (y : SpaceTime) :
    TimeTranslation.timeTranslationSchwartzℂ (-s) g y = g (y - TimeTranslation.timeShiftConst s) :=
      by
  rw [timeTranslationSchwartzℂ_at_point, timeShift_eq_add]
  congr 1
  -- y + timeShiftConst(-s) = y - timeShiftConst(s)
  simp only [TimeTranslation.timeShiftConst]
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply]
  split_ifs <;> ring

/-- freeCovariance is translation-invariant: C(x,y) = C(0, x-y) = freeCovarianceKernel(x-y). -/
lemma freeCovariance_eq_kernel (m : ℝ) (x y : SpaceTime) :
    freeCovariance m x y = freeCovarianceKernel m (x - y) := by
  -- freeCovariance m x y = freeCovarianceBessel m x y = (m / (4π²r)) K₁(mr) where r = ‖x - y‖
  -- freeCovarianceKernel m z = freeCovariance m 0 z = freeCovarianceBessel m 0 z
  --   = (m / (4π²r')) K₁(mr') where r' = ‖0 - z‖ = ‖z‖
  -- For z = x - y: r' = ‖x - y‖ = r
  unfold freeCovarianceKernel freeCovariance freeCovarianceBessel
  -- Goal: ‖x - y‖ = ‖0 - (x - y)‖
  rw [zero_sub, norm_neg]

/-- The Schwinger 2-point function for time-translated test function equals
    the bilinear integral with translated argument.
-/
lemma schwinger2_time_translated_eq_bilinear (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) (s : ℝ) :
    SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f (TimeTranslation.timeTranslationSchwartzℂ (-s)
      g) =
    ∫ x : SpaceTime, ∫ y : SpaceTime,
      f x * (freeCovarianceKernel m (x - y) : ℂ) * g (y - TimeTranslation.timeShiftConst s) := by
  -- S₂(f, T_{-s} g) = freeCovarianceℂBilinear m f (T_{-s} g)
  rw [gff_two_point_equals_covarianceℂ_free]
  -- freeCovarianceℂBilinear m f g = ∫∫ f(x) · freeCovariance(x,y) · g(y) dx dy
  unfold freeCovarianceℂBilinear
  -- Expand T_{-s} g at point y and use kernel identity
  congr 1 with x
  congr 1 with y
  rw [timeTranslationSchwartzℂ_neg_eq_sub, freeCovariance_eq_kernel]

/-- The GFF satisfies OS4 polynomial clustering for any exponent α > 0.

    The proof uses:
    1. Time duality: ⟨T_s ω, g⟩ = ⟨ω, T_{-s} g⟩
    2. Gaussian factorization: E[e^{⟨ω, f⟩ + ⟨T_s ω, g⟩}] = Z[f]·Z[g]·exp(-S₂(f, T_{-s} g))
    3. Exponential covariance decay: |S₂(f, T_{-s} g)| ≤ c·e^{-ms} from mass gap
    4. Proved theorem: schwartz_bilinear_translation_decay_polynomial_proof for polynomial bound

    The mass gap m > 0 ensures exponential decay, which is stronger than any polynomial.
    Therefore the GFF satisfies os4PolynomialClustering for all α > 0.
-/
theorem gaussianFreeField_satisfies_OS4_PolynomialClustering (m : ℝ) [Fact (0 < m)]
    (α : ℝ) (hα : α > 0) :
    os4PolynomialClustering (gaussianFreeFieldFree m) α hα := by
  intro f g
  -- Step 1: Get kernel properties for applying the decay lemma
  have hm : 0 < m := Fact.out
  have hK_meas : Measurable (freeCovarianceKernel m) :=
    measurable_of_continuousOn_compl_singleton 0 (freeCovarianceKernel_continuousOn m hm)
  have hK_loc : MeasureTheory.LocallyIntegrable (freeCovarianceKernel m) MeasureTheory.volume :=
    (freeCovarianceKernel_integrable m hm).locallyIntegrable
  -- Step 2: Get exponential decay bound for the kernel
  -- From freeCovariance_exponential_bound': |C(u,v)| ≤ c·e^{-m‖u-v‖} for m‖u-v‖ ≥ 1
  -- The constant is C_exp = m^2 * (sinh 1 + 2) / (4 * π^2)
  let C_exp := m^2 * (Real.sinh 1 + 2) / (4 * Real.pi^2)
  have hC_exp_pos : C_exp > 0 := by
    simp only [C_exp]; positivity
  have hK_cont : ContinuousOn (freeCovarianceKernel m) (Metric.closedBall (0 : SpaceTime) (1/m))ᶜ :=
    (freeCovarianceKernel_continuousOn m hm).mono fun z hz => by
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by positivity) (le_of_lt hz)))
  -- Convert exponential bound from freeCovariance to freeCovarianceKernel
  have hK_decay : ∀ z : SpaceTime, ‖z‖ ≥ 1/m → |freeCovarianceKernel m z| ≤ C_exp * Real.exp (-m *
    ‖z‖) := by
    intro z hz
    have hmz : m * ‖z‖ ≥ 1 := by
      calc m * ‖z‖ ≥ m * (1/m) := mul_le_mul_of_nonneg_left hz (le_of_lt hm)
        _ = 1 := by field_simp
    have h_norm_eq : ‖(0 : SpaceTime) - z‖ = ‖z‖ := by simp
    have h := freeCovariance_exponential_bound m hm 0 z (by rw [h_norm_eq]; exact hmz)
    simp only [freeCovarianceKernel, freeCovariance, h_norm_eq] at h ⊢; exact h
  -- Step 3: Apply the quantitative decay lemma
  have ⟨c_decay, hc_nonneg, hBound⟩ := schwartz_bilinear_translation_decay_polynomial_proof
    f g (freeCovarianceKernel m)
    hK_meas hK_loc
    m hm C_exp (1/m) hC_exp_pos (by positivity)
    hK_cont hK_decay
    α hα
  -- Step 4: The bound gives us the polynomial decay for the bilinear integral
  -- Now we need to connect this to the os4PolynomialClustering statement
  -- The key steps:
  -- a) E[e^{⟨ω,f⟩ + ⟨T_s ω, g⟩}] = E[e^{⟨ω, f + T_{-s} g⟩}] by duality
  -- b) For Gaussian: = Z[f]·Z[g]·exp(-S₂(f, T_{-s} g))
  -- c) The cross term S₂(f, T_{-s} g) is bounded by the decay lemma
  -- Step 4: Define key quantities
  let Ef := ∫ ω, Complex.exp (distributionPairingℂReal ω f) ∂(gaussianFreeFieldFree m).toMeasure
  let Eg := ∫ ω, Complex.exp (distributionPairingℂReal ω g) ∂(gaussianFreeFieldFree m).toMeasure
  -- Step 5: The Schwinger function equals the bilinear integral (from
  -- schwinger2_time_translated_eq_bilinear)
  -- We need to bound |S₂(f, T_{-t}g)| for any t ≥ 0
  have h_S2_bound : ∀ t : ℝ, t ≥ 0 →
      ‖SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f (TimeTranslation.timeTranslationSchwartzℂ
        (-t) g)‖ ≤
        c_decay * (1 + t)^(-α) := by
    intro t ht
    -- Use schwinger2_time_translated_eq_bilinear to rewrite S₂
    rw [schwinger2_time_translated_eq_bilinear]
    -- The RHS is exactly the form of the decay lemma with a = timeShiftConst(t)
    have h_norm_bound := hBound (TimeTranslation.timeShiftConst t)
    -- ‖timeShiftConst(t)‖ = |t| = t for t ≥ 0
    rwa [timeShiftConst_norm, abs_of_nonneg ht] at h_norm_bound
  -- Step 6: Construct the final constant
  -- The bound is: |LHS - Ef·Eg| ≤ |Ef| · |Eg| · |e^{S₂} - 1|
  --             ≤ |Ef| · |Eg| · |S₂| · e^{|S₂|}  (by exp bound)
  --             ≤ |Ef| · |Eg| · c_decay · (1+s)^{-α} · e^{c_decay}
  -- (using (1+s)^{-α} ≤ 1 so |S₂| ≤ c_decay and e^{|S₂|} ≤ e^{c_decay})
  let final_c := ‖Ef‖ * ‖Eg‖ * c_decay * Real.exp c_decay
  refine ⟨final_c, by positivity, ?_⟩
  -- Step 7: Main proof
  -- The goal has `have μ := ...; ∀ s ≥ 0, ...` so we need to handle the let-binding
  change ∀ s : ℝ, s ≥ 0 →
    ‖∫ ω, Complex.exp (distributionPairingℂReal ω f +
          distributionPairingℂReal (TimeTranslation.timeTranslationDistribution s ω) g)
          ∂(gaussianFreeFieldFree m).toMeasure -
        (∫ ω, Complex.exp (distributionPairingℂReal ω f) ∂(gaussianFreeFieldFree m).toMeasure) *
        (∫ ω, Complex.exp (distributionPairingℂReal ω g) ∂(gaussianFreeFieldFree m).toMeasure)‖ ≤
      final_c * (1 + s)^(-α)
  intro t ht
  -- Abbreviation for the shifted g
  let g_t := TimeTranslation.timeTranslationSchwartzℂ (-t) g
  -- Step 7a: Use time duality to rewrite LHS
  have h_duality : ∀ ω, distributionPairingℂReal (TimeTranslation.timeTranslationDistribution t ω)
    g =
      distributionPairingℂReal ω g_t := fun ω => time_translation_pairing_duality t ω g
  -- Step 7b: Apply Gaussian factorization
  have h_gauss := OS4infra.gff_joint_mgf_factorization m f g_t
  have h_time_inv := OS4infra.gff_generating_time_invariant m (-t) g
  -- E[e^{⟨ω, T_{-t}g⟩}] = E[e^{⟨ω, g⟩}] = Eg
  have h_Eg_shifted : (∫ ω, Complex.exp (distributionPairingℂReal ω g_t)
      ∂(gaussianFreeFieldFree m).toMeasure) = Eg := h_time_inv
  -- Step 7c: Combine duality with Gaussian factorization
  have h_factored : ∫ ω, Complex.exp (distributionPairingℂReal ω f +
        distributionPairingℂReal (TimeTranslation.timeTranslationDistribution t ω) g)
        ∂(gaussianFreeFieldFree m).toMeasure =
      Ef * Eg * Complex.exp (SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f g_t) := by
    simp_rw [h_duality, h_gauss, h_Eg_shifted, Ef]
  -- Step 7d: Compute the difference
  have h_diff : ∫ ω, Complex.exp (distributionPairingℂReal ω f +
        distributionPairingℂReal (TimeTranslation.timeTranslationDistribution t ω) g)
        ∂(gaussianFreeFieldFree m).toMeasure - Ef * Eg =
      Ef * Eg * (Complex.exp (SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f g_t) - 1) := by
    rw [h_factored]; ring
  -- Step 7f: Bound the difference
  calc ‖∫ ω, Complex.exp (distributionPairingℂReal ω f +
        distributionPairingℂReal (TimeTranslation.timeTranslationDistribution t ω) g)
        ∂(gaussianFreeFieldFree m).toMeasure - Ef * Eg‖
      = ‖Ef * Eg * (Complex.exp (SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f g_t) - 1)‖ :=
        by rw [h_diff]
    _ = ‖Ef‖ * ‖Eg‖ * ‖Complex.exp (SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f g_t) - 1‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ ‖Ef‖ * ‖Eg‖ * (‖SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f g_t‖ *
        Real.exp ‖SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f g_t‖) := by
        apply mul_le_mul_of_nonneg_left
        · exact OS4infra.exp_sub_one_bound_general _
        · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    _ ≤ ‖Ef‖ * ‖Eg‖ * (c_decay * (1 + t)^(-α) * Real.exp (c_decay * (1 + t)^(-α))) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        have h_bound := h_S2_bound t ht
        apply mul_le_mul h_bound
        · apply Real.exp_le_exp.mpr h_bound
        · exact Real.exp_nonneg _
        · exact mul_nonneg hc_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ 1 + t) _)
    _ ≤ ‖Ef‖ * ‖Eg‖ * (c_decay * (1 + t)^(-α) * Real.exp c_decay) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc_nonneg (Real.rpow_nonneg (by linarith) _))
        apply Real.exp_le_exp.mpr
        calc c_decay * (1 + t)^(-α)
            ≤ c_decay * 1 := by
                apply mul_le_mul_of_nonneg_left _ hc_nonneg
                -- Use: for x ≥ 1 and z ≤ 0, x^z ≤ 1
                apply Real.rpow_le_one_of_one_le_of_nonpos
                · linarith  -- 1 ≤ 1 + t
                · linarith  -- -α ≤ 0
          _ = c_decay := by ring
    _ = final_c * (1 + t)^(-α) := by ring

end QFT

end
