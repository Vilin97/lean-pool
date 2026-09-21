/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Real
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Radial
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.HasLaw

/-!
# Gamma normalization and the Dirichlet distribution

Independent Gamma variables with positive shapes and a common positive rate are
normalized by their sum. The sum and the normalized vector have a product law:
Gamma with the total shape, and Dirichlet with the original shapes.

The main random-variable results are `iIndepFun.hasLaw_dirichlet_of_gamma`,
`iIndepFun.hasLaw_sum_gamma`, and `iIndepFun.indepFun_sum_simplexNormalize_gamma`.
Their common source is `map_sum_simplexNormalize_pi_gammaMeasure`.

The index type is finite and nonempty; the singleton case is included. Empty families
are excluded because their total is zero and the project's empty-index Dirichlet measure
is not a probability measure. The normalization denominator is almost surely positive.

The proof uses the elementary radial integration formula from `StdSimplexMeasure.Radial`;
neither complex Dirichlet measures nor analytic continuation is involved.
-/

@[expose] public noncomputable section

open MeasureTheory MeasureTheory.Measure Real Set
open scoped ENNReal Classical

namespace ProbabilityTheory

private theorem lintegral_fin_prod {n : ℕ} {μ : Fin n → Measure ℝ}
    [∀ i, SigmaFinite (μ i)] (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (measurePreserving_piFinSuccAbove μ 0).symm.lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    have hg : Measurable (fun x : Fin n → ℝ => ∏ i, f i.succ (x i)) := by fun_prop
    rw [lintegral_prod_mul (hf 0).aemeasurable hg.aemeasurable,
      ih _ (fun i => hf i.succ)]

private theorem lintegral_pi_prod {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ}
    [∀ i, SigmaFinite (μ i)] (f : ι → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod _ (fun i => hf (e i))

variable {ι : Type*} [Fintype ι]

/-- The finite product of Gamma measures has the product of their densities. -/
theorem pi_gammaMeasure_eq_withDensity {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    {r : ℝ} (hr : 0 < r) :
    Measure.pi (fun i => gammaMeasure (b i) r) =
      volume.withDensity (fun x : ι → ℝ => ∏ i, gammaPDF (b i) r (x i)) := by
  let : ∀ i, IsProbabilityMeasure (gammaMeasure (b i) r) :=
    fun i => isProbabilityMeasure_gammaMeasure (hb i) hr
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ x, ∏ i, gammaPDF (b i) r (x i)
    ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (Set.pi univ s)) = _
  have hf (i : ι) : Measurable (gammaPDF (b i) r) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal (b i) r)
  rw [Measure.restrict_pi_pi, lintegral_pi_prod _ hf]
  congr 1
  funext i
  exact (withDensity_apply _ (hs i)).symm

/-- The density factorization in radial coordinates. The Jacobian is the coordinate-simplex
factor `t^(card ι - 1)`, not an ambient Euclidean surface-area factor. -/
theorem gammaPDFReal_radial [Nonempty ι] {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) {u : ι → ℝ} (hu : u ∈ stdSimplexInterior) :
    t ^ (Fintype.card ι - 1) * (∏ i, gammaPDFReal (b i) r (t * u i)) =
      gammaPDFReal (∑ i, b i) r t * dirichletPdfReal b u := by
  have hB : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hG : Gamma (∑ i, b i) ≠ 0 := (Gamma_pos_of_pos hB).ne'
  have hterm (i : ι) : gammaPDFReal (b i) r (t * u i) =
      (r ^ b i / Gamma (b i)) * t ^ (b i - 1) * u i ^ (b i - 1) *
        exp (-(r * t) * u i) := by
    rw [gammaPDFReal, if_pos (mul_pos ht (hu.2 i)).le, mul_rpow ht.le (hu.2 i).le]
    congr 1
    · ring
    · congr 1; ring
  have hsum : ∑ i, -(r * t) * u i = -(r * t) := by
    rw [← Finset.mul_sum, hu.1.2, mul_one]
  have hexp : t ^ (Fintype.card ι - 1) * t ^ (∑ i, (b i - 1)) =
      t ^ ((∑ i, b i) - 1) := by
    rw [← rpow_natCast, ← rpow_add ht]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, Nat.cast_sub (Nat.succ_le_iff.mpr Fintype.card_pos)]
    simp
  simp_rw [hterm, Finset.prod_mul_distrib]
  rw [Finset.prod_div_distrib, ← rpow_sum_of_pos hr, ← rpow_sum_of_pos ht,
    ← exp_sum, hsum]
  rw [gammaPDFReal, if_pos ht.le, dirichletPdfReal, Set.indicator_of_mem hu, mvRealBeta]
  have hGp : (∏ i, Gamma (b i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (Gamma_pos_of_pos (hb i)).ne')
  calc
    _ = (r ^ (∑ i, b i) / ∏ i, Gamma (b i)) *
        (t ^ (Fintype.card ι - 1) * t ^ (∑ i, (b i - 1))) *
        (∏ i, u i ^ (b i - 1)) * exp (-(r * t)) := by ring
    _ = _ := by rw [hexp]; field_simp

/-- Normalize a vector by its coordinate sum. At sum zero this is the zero vector,
following Lean's convention for division by zero. -/
def simplexNormalize (x : ι → ℝ) : ι → ℝ := fun i => x i / ∑ j, x j

@[fun_prop] theorem measurable_simplexNormalize : Measurable (simplexNormalize (ι := ι)) := by
  unfold simplexNormalize
  fun_prop

/-- Radial coordinates recover a simplex point and its positive scale. -/
theorem sum_simplexNormalize_smul {t : ℝ} (ht : 0 < t) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    (∑ i, (t • u) i, simplexNormalize (t • u)) = (t, u) := by
  have hs : ∑ i, (t • u) i = t := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hu.2, mul_one]
  simp only [Prod.mk.injEq, hs, true_and]
  ext i
  change (t • u) i / (∑ j, (t • u) j) = u i
  rw [hs]
  exact mul_div_cancel_left₀ _ ht.ne'

/-- Gamma measure is concentrated on strictly positive values. -/
theorem ae_pos_gammaMeasure (a r : ℝ) : ∀ᵐ t ∂gammaMeasure a r, 0 < t := by
  rw [gammaMeasure, ae_withDensity_iff
    (show Measurable (gammaPDF a r) from
      ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a r))]
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
  intro h
  by_contra hn
  exact h (gammaPDF_of_neg (lt_of_le_of_ne (le_of_not_gt hn) ht))

/-- Nonnegative density factorization in radial coordinates. -/
theorem gammaPDF_radial [Nonempty ι] {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) {u : ι → ℝ} (hu : u ∈ stdSimplexInterior) :
    ENNReal.ofReal (t ^ (Fintype.card ι - 1)) * (∏ i, gammaPDF (b i) r (t * u i)) =
      gammaPDF (∑ i, b i) r t * dirichletPdf b u := by
  have hB : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  simpa only [ENNReal.ofReal_mul (pow_nonneg ht.le _),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => gammaPDFReal_nonneg (hb i) hr _),
    ENNReal.ofReal_mul (gammaPDFReal_nonneg hB hr _), gammaPDF, dirichletPdf] using
    congrArg ENNReal.ofReal (gammaPDFReal_radial hb hr ht hu)

/-- The joint law of the total and normalized coordinates under a product of Gamma measures. -/
theorem map_sum_simplexNormalize_pi_gammaMeasure [Nonempty ι] {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) {r : ℝ} (hr : 0 < r) :
    (Measure.pi (fun i => gammaMeasure (b i) r)).map
        (fun x => (∑ i, x i, simplexNormalize x)) =
      (gammaMeasure (∑ i, b i) r).prod (dirichletMeasure b) := by
  have hm : Measurable (fun x : ι → ℝ => (∑ i, x i, simplexNormalize x)) := by fun_prop
  have hp (i : ι) : Measurable (gammaPDF (b i) r) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal (b i) r)
  have hd : Measurable (dirichletPdf b) := measurable_dirichletPdf b
  have hB : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  let : IsProbabilityMeasure (gammaMeasure (∑ i, b i) r) :=
    isProbabilityMeasure_gammaMeasure hB hr
  let : IsProbabilityMeasure (dirichletMeasure b) := isProbabilityMeasure_dirichletMeasure hb
  apply Measure.ext_of_lintegral
  intro g hg
  have hgm : Measurable (fun x : ι → ℝ => g (∑ i, x i, simplexNormalize x)) := hg.comp hm
  rw [lintegral_map hg hm, pi_gammaMeasure_eq_withDensity hb hr,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hgm]
  change (∫⁻ x, (∏ i, gammaPDF (b i) r (x i)) * g (∑ i, x i, simplexNormalize x)) = _
  rw [lintegral_eq_radial_stdSimplex _ (by fun_prop) (by
    intro x hx
    obtain ⟨i, hi⟩ := not_forall.mp hx
    have hz : ∏ j, gammaPDF (b j) r (x j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (gammaPDF_of_neg (lt_of_not_ge hi))
    rw [hz, zero_mul])]
  rw [lintegral_prod _ hg.aemeasurable,
    ← Measure.restrict_eq_self_of_ae_mem (s := Ioi (0 : ℝ))
      (ae_pos_gammaMeasure (∑ i, b i) r)]
  rw [gammaMeasure, setLIntegral_withDensity_eq_setLIntegral_mul _
    (show Measurable (gammaPDF (∑ i, b i) r) from
      ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal _ _))
    (by fun_prop) measurableSet_Ioi]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only [Pi.mul_apply]
  rw [← dirichletMeasure_restrict b, dirichletMeasure,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_dirichletPdf b)
      (show Measurable (fun u => g (t, u)) from hg.comp (measurable_const.prodMk measurable_id))
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet]
  rw [← lintegral_const_mul _ (by fun_prop), ← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [ae_mem_stdSimplexInterior (ι := ι)] with u hu
  dsimp only [Pi.mul_apply]
  rw [sum_simplexNormalize_smul ht hu.1]
  simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using
    congrArg (fun z => z * g (t, u)) (gammaPDF_radial hb hr ht hu)

section RandomVariables

variable [Nonempty ι] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : ι → Ω → ℝ} {b : ι → ℝ} {r : ℝ}

/-- Independent Gamma variables with a common rate have independent total and normalized
vector, with the indicated Gamma and Dirichlet laws. -/
theorem iIndepFun.hasLaw_sum_simplexNormalize_gamma
    (h : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (gammaMeasure (b i) r) P)
    (hb : b ∈ mvRealBetaDomain) (hr : 0 < r) :
    HasLaw (fun ω => (∑ i, X i ω, simplexNormalize (fun i => X i ω)))
      ((gammaMeasure (∑ i, b i) r).prod (dirichletMeasure b)) P := by
  have hm : MeasurePreserving (fun x : ι → ℝ => (∑ i, x i, simplexNormalize x))
      (Measure.pi (fun i => gammaMeasure (b i) r))
      ((gammaMeasure (∑ i, b i) r).prod (dirichletMeasure b)) :=
    ⟨by fun_prop, map_sum_simplexNormalize_pi_gammaMeasure hb hr⟩
  exact hm.fun_comp_hasLaw (h.hasLaw_pi hX)

/-- The sum of independent Gamma variables with a common rate is Gamma-distributed,
with shape the sum of the shapes. -/
theorem iIndepFun.hasLaw_sum_gamma
    (h : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (gammaMeasure (b i) r) P)
    (hb : b ∈ mvRealBetaDomain) (hr : 0 < r) :
    HasLaw (fun ω => ∑ i, X i ω) (gammaMeasure (∑ i, b i) r) P := by
  let : IsProbabilityMeasure (dirichletMeasure b) := isProbabilityMeasure_dirichletMeasure hb
  exact measurePreserving_fst.fun_comp_hasLaw (h.hasLaw_sum_simplexNormalize_gamma hX hb hr)

/-- Gamma normalization constructs a Dirichlet random vector. In particular, take `r = 1`
for the unit-rate Gamma-ratio characterization. -/
theorem iIndepFun.hasLaw_dirichlet_of_gamma
    (h : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (gammaMeasure (b i) r) P)
    (hb : b ∈ mvRealBetaDomain) (hr : 0 < r) :
    HasLaw (fun ω i => X i ω / ∑ j, X j ω) (dirichletMeasure b) P := by
  let : IsProbabilityMeasure (dirichletMeasure b) := isProbabilityMeasure_dirichletMeasure hb
  have hB : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  let : IsProbabilityMeasure (gammaMeasure (∑ i, b i) r) :=
    isProbabilityMeasure_gammaMeasure hB hr
  exact measurePreserving_snd.fun_comp_hasLaw (h.hasLaw_sum_simplexNormalize_gamma hX hb hr)

/-- The total of independent Gamma variables is independent of their ratios to that total. -/
theorem iIndepFun.indepFun_sum_simplexNormalize_gamma
    (h : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (gammaMeasure (b i) r) P)
    (hb : b ∈ mvRealBetaDomain) (hr : 0 < r) :
    IndepFun (fun ω => ∑ i, X i ω) (fun ω i => X i ω / ∑ j, X j ω) P := by
  let : IsProbabilityMeasure (dirichletMeasure b) := isProbabilityMeasure_dirichletMeasure hb
  let : IsProbabilityMeasure P := (h.hasLaw_dirichlet_of_gamma hX hb hr).isProbabilityMeasure
  exact (indepFun_iff_hasLaw_prodMk_prod (h.hasLaw_sum_gamma hX hb hr)
    (h.hasLaw_dirichlet_of_gamma hX hb hr)).mpr
      (h.hasLaw_sum_simplexNormalize_gamma hX hb hr)

/-- The denominator in the Gamma-ratio construction is almost surely strictly positive. -/
theorem iIndepFun.ae_pos_sum_gamma
    (h : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (gammaMeasure (b i) r) P)
    (hb : b ∈ mvRealBetaDomain) (hr : 0 < r) :
    ∀ᵐ ω ∂P, 0 < ∑ i, X i ω := by
  exact ((h.hasLaw_sum_gamma hX hb hr).ae_iff (by fun_prop)).mpr
    (ae_pos_gammaMeasure (∑ i, b i) r)

end RandomVariables

end ProbabilityTheory

end
