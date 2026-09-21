/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.NonnegativeRicciBochner
public import LeanPool.PoincareGeometry.AlmostSchur.GradientL2
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyKernel

/-! # Sharp integrated curvature bound

The geometric Bochner step toward Lichnerowicz--Obata.  This file does not
assert spectral attainment or global Obata rigidity.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [LindelofSpace M] [T2Space M] [CompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))
local notation "ν" => (riemannianVolume (I := I) (M := M))
local notation "n" => (Module.finrank ℝ E : ℝ)

local instance (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

local instance : IsContinuousRiemannianBundle E TM :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- The dimension-weighted Ricci energy is bounded by the squared Laplacian.
All differential identities are inherited proved theorems, not hypotheses. -/
theorem integrated_ricci_le_laplacian
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    (hdim : Module.finrank ℝ E ≠ 0) :
    n * (∫ x, CovariantDerivative.ricciCurvatureAlmostSchur (cov := LC) x
      (gradient (I := I) f x) (gradient (I := I) f x) ∂ν) ≤
    (n - 1) * (∫ x, (laplacian LC f x) ^ 2 ∂ν) := by
  have hb := leviCivita_integratedBundledRicciBochner hf
  have ht := finrank_mul_integral_traceFreeHessianNormSq LC
    leviCivitaConnection_metricCompatible leviCivitaConnection_torsion hf hdim
  have hpos : 0 ≤ ∫ x, traceFreeHessianNormSq LC f x ∂ν :=
    integral_nonneg fun x => hilbertSchmidtSq_nonneg _
  have hn : 0 ≤ n := Nat.cast_nonneg _
  nlinarith [mul_nonneg hn hpos]

/-- The sharp integrated inequality under the genuine Ricci lower bound. -/
theorem integrated_laplacian_bound
    {K : ℝ} (hdim : 2 ≤ Module.finrank ℝ E)
    (hRic : ∀ (x : M) (v : TM x),
      (n - 1) * K * ‖v‖ ^ 2 ≤
        CovariantDerivative.ricciCurvatureAlmostSchur (cov := LC) x v v)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) :
    n * K * (∫ x, ‖gradient (I := I) f x‖ ^ 2 ∂ν) ≤
      ∫ x, (laplacian LC f x) ^ 2 ∂ν := by
  let : IsFiniteMeasure ν := ⟨(riemannianVolume_finite_positive (I := I)).2⟩
  have hg : Integrable (fun x => ‖gradient (I := I) f x‖ ^ 2) ν :=
    ((continuous_norm_gradient (hf.of_le (by norm_num))).pow 2).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have hr : Integrable (fun x => CovariantDerivative.ricciCurvatureAlmostSchur (cov := LC) x
      (gradient (I := I) f x) (gradient (I := I) f x)) ν := by
    have heq : (fun x => CovariantDerivative.ricciCurvatureAlmostSchur (cov := LC) x
        (gradient (I := I) f x) (gradient (I := I) f x)) = rawRicciGradient LC f := by
      funext x
      exact (rawRicciGradient_eq_ricciCurvature LC (hf x)).symm
    rw [heq]
    exact integrable_rawRicciGradient LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion hf
  have hlow := integral_mono (hg.const_mul ((n - 1) * K)) hr
    (fun x => hRic x (gradient (I := I) f x))
  rw [integral_const_mul] at hlow
  have hupper := integrated_ricci_le_laplacian hf (by omega)
  have hn : 2 ≤ n := by exact_mod_cast hdim
  have hcombined := (mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ n)).trans hupper
  have harr : (n - 1) * (n * K * (∫ x, ‖gradient (I := I) f x‖ ^ 2 ∂ν)) ≤
      (n - 1) * (∫ x, (laplacian LC f x) ^ 2 ∂ν) := by
    nlinarith only [hcombined]
  exact (mul_le_mul_iff_right₀ (by linarith : 0 < n - 1)).mp harr

omit [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- A nonconstant smooth function on the connected manifold has positive energy. -/
theorem gradient_energy_pos [PreconnectedSpace M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    (hnonconst : ∃ x y, f x ≠ f y) :
    0 < ∫ x, ‖gradient (I := I) f x‖ ^ 2 ∂ν := by
  have hnonneg : 0 ≤ ∫ x, ‖gradient (I := I) f x‖ ^ 2 ∂ν :=
    integral_nonneg fun x => sq_nonneg _
  apply lt_of_le_of_ne hnonneg
  intro heq
  have henergy : dirichletForm (I := I) f f = 0 := by
    rw [dirichletForm_self]
    exact heq.symm
  have hdf := (dirichletForm_self_eq_zero_iff_differential f hf).mp henergy
  obtain ⟨x, y, hxy⟩ := hnonconst
  exact hxy (eq_of_differential_eq_zero f hf hdf x y)

/-- Lichnerowicz's sharp lower bound for every nonconstant C³ eigenfunction
of the actual Laplace--Beltrami operator, with the `div grad` convention.
Existence of an eigenfunction attaining the first eigenvalue is a separate task. -/
theorem eigenvalue_lower_bound [PreconnectedSpace M]
    {K μ : ℝ} (hdim : 2 ≤ Module.finrank ℝ E)
    (hRic : ∀ (x : M) (v : TM x),
      (n - 1) * K * ‖v‖ ^ 2 ≤
        CovariantDerivative.ricciCurvatureAlmostSchur (cov := LC) x v v)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    (hnonconst : ∃ x y, f x ≠ f y)
    (heigen : ∀ x, laplacian LC f x = -μ * f x) : n * K ≤ μ := by
  have hg := gradient_energy_pos (hf.of_le (by norm_num)) hnonconst
  have hgreen := integral_mul_laplacian_self LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion f (hf.of_le (by norm_num))
  have hid : (∫ x, (laplacian LC f x) ^ 2 ∂ν) =
      μ * (∫ x, ‖gradient (I := I) f x‖ ^ 2 ∂ν) := by
    calc
      _ = ∫ x, -μ * (f x * laplacian LC f x) ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [heigen]
        ring
      _ = -μ * (∫ x, f x * laplacian LC f x ∂ν) := integral_const_mul _ _
      _ = _ := by rw [hgreen]; ring
  have hb := integrated_laplacian_bound hdim hRic hf
  rw [hid] at hb
  exact (mul_le_mul_iff_left₀ hg).mp hb

/-- Saturation of the integrated bound forces the trace-free Hessian to vanish
everywhere. Continuity and positivity of volume upgrade the integral conclusion. -/
theorem traceFreeHessian_eq_zero_of_equality
    {K : ℝ} (hdim : 2 ≤ Module.finrank ℝ E)
    (hRic : ∀ (x : M) (v : TM x),
      (n - 1) * K * ‖v‖ ^ 2 ≤
        CovariantDerivative.ricciCurvatureAlmostSchur (cov := LC) x v v)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    (heq : (∫ x, (laplacian LC f x) ^ 2 ∂ν) =
      n * K * (∫ x, ‖gradient (I := I) f x‖ ^ 2 ∂ν)) :
    ∀ x, traceFree (LC (gradient (I := I) f) x) = 0 := by
  let : IsFiniteMeasure ν := ⟨(riemannianVolume_finite_positive (I := I)).2⟩
  let : (riemannianVolume (I := I) (M := M)).IsOpenPosMeasure :=
    ⟨fun _ hs hne => ne_of_gt (riemannianVolume_open_pos (I := I) hs hne)⟩
  have hd : Module.finrank ℝ E ≠ 0 := by omega
  have hn : 2 ≤ n := by exact_mod_cast hdim
  have hg : Integrable (fun x => ‖gradient (I := I) f x‖ ^ 2) ν :=
    ((continuous_norm_gradient (hf.of_le (by norm_num))).pow 2).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have hr : Integrable (fun x => CovariantDerivative.ricciCurvatureAlmostSchur (cov := LC) x
      (gradient (I := I) f x) (gradient (I := I) f x)) ν := by
    have hraw := integrable_rawRicciGradient LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion hf
    exact hraw.congr (Filter.Eventually.of_forall fun x =>
      rawRicciGradient_eq_ricciCurvature LC (hf x))
  have hlow := integral_mono (hg.const_mul ((n - 1) * K)) hr
    (fun x => hRic x (gradient (I := I) f x))
  rw [integral_const_mul] at hlow
  have hb := leviCivita_integratedBundledRicciBochner hf
  have ht := finrank_mul_integral_traceFreeHessianNormSq LC
    leviCivitaConnection_metricCompatible leviCivitaConnection_torsion hf hd
  have hnonneg : ∀ x, 0 ≤ traceFreeHessianNormSq LC f x :=
    fun x => hilbertSchmidtSq_nonneg _
  have hint : (∫ x, traceFreeHessianNormSq LC f x ∂ν) = 0 := by
    have hscaled := mul_le_mul_of_nonneg_left hlow (by linarith : 0 ≤ n)
    have hpos : 0 ≤ ∫ x, traceFreeHessianNormSq LC f x ∂ν := integral_nonneg hnonneg
    nlinarith [mul_nonneg (by linarith : 0 ≤ n) hpos]
  have hi := integrable_traceFreeHessianNormSq LC
    leviCivitaConnection_metricCompatible leviCivitaConnection_torsion hf hd
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hi).mp hint
  have hc : Continuous (traceFreeHessianNormSq LC f) := by
    have hfun : traceFreeHessianNormSq LC f = fun x => hessianNormSq LC f x -
        (laplacian LC f x) ^ 2 / n := by
      funext x
      exact traceFreeHessianNormSq_eq LC f x hd
    rw [hfun]
    exact (contMDiff_hessianNormSq LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion hf).continuous.sub
        (((contMDiff_laplacian LC hf).continuous.pow 2).div_const _)
  have hevery := MeasureTheory.Measure.eq_of_ae_eq hae hc continuous_const
  intro x
  exact (hilbertSchmidtSq_eq_zero_iff _).mp (congrFun hevery x)

/-- An extremal eigenfunction satisfies Obata's actual covariant Hessian
equation. This is the analytic input to rigidity, not an assumed bridge. -/
theorem hessian_equation_of_extremal_eigenfunction
    {K : ℝ} (hdim : 2 ≤ Module.finrank ℝ E)
    (hRic : ∀ (x : M) (v : TM x),
      (n - 1) * K * ‖v‖ ^ 2 ≤
        CovariantDerivative.ricciCurvatureAlmostSchur (cov := LC) x v v)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    (heigen : ∀ x, laplacian LC f x = -(n * K) * f x) :
    ∀ (x : M) (v w : TM x),
      hessian LC f x v w = -K * f x * inner ℝ v w := by
  have hgreen := integral_mul_laplacian_self LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion f (hf.of_le (by norm_num))
  have hid : (∫ x, (laplacian LC f x) ^ 2 ∂ν) =
      n * K * (∫ x, ‖gradient (I := I) f x‖ ^ 2 ∂ν) := by
    calc
      _ = ∫ x, -(n * K) * (f x * laplacian LC f x) ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [heigen]
        ring
      _ = -(n * K) * (∫ x, f x * laplacian LC f x ∂ν) := integral_const_mul _ _
      _ = _ := by rw [hgreen]; ring
  have hz := traceFreeHessian_eq_zero_of_equality hdim hRic hf hid
  intro x v w
  have hA := sub_eq_zero.mp (hz x)
  have hrank := VectorBundle.finrank_eq ℝ E TM x
  have hn : n ≠ 0 := by exact_mod_cast (show Module.finrank ℝ E ≠ 0 by omega)
  have hscalar : LinearMap.trace ℝ (TM x)
      (LC (gradient (I := I) f) x).toLinearMap / Module.finrank ℝ (TM x) = -K * f x := by
    rw [hrank]
    change laplacian LC f x / n = _
    rw [heigen]
    field_simp
  rw [hscalar] at hA
  change inner ℝ (LC (gradient (I := I) f) x v) w = _
  rw [hA]
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_left]

end LichnerowiczObata
