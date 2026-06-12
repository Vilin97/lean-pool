/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.PhaseStability

/-! # Auxiliary -/


open scoped BigOperators

noncomputable section

namespace DimdPolyLEAN

/-!
# Auxiliary bridge for the showcase theorem

This file keeps the coefficient-level normalization and rescaling argument out of
`DimdPoly.lean`.  The public file deliberately restates the public definitions;
the lemmas here use equivalent explicit objects so the public file can unfold
only paper-facing definitions.
-/

/-- `explicitGaussianDensity`: explicit Gaussian Density. -/
def explicitGaussianDensity (d : Nat) (z : Fin d -> ℂ) : ℝ :=
  (1 / Real.pi ^ d) * Real.exp (-Finset.sum Finset.univ (fun q : Fin d => ‖z q‖ ^ 2))

/-- `explicitGamma`: explicit Gamma. -/
def explicitGamma (d : Nat) : MeasureTheory.Measure (Fin d -> ℂ) :=
  MeasureTheory.volume.withDensity fun z => ENNReal.ofReal (explicitGaussianDensity d z)

/-- `explicitComplexHermite`: explicit Complex Hermite. -/
def explicitComplexHermite (m n : Nat) (z : ℂ) : ℂ :=
  Finset.sum (Finset.range (min m n + 1)) fun j =>
    ((-1 : ℂ) ^ j) * (Nat.factorial j : ℂ) *
      (Nat.choose m j : ℂ) * (Nat.choose n j : ℂ) *
      z ^ (m - j) * (star z) ^ (n - j)

/-- `explicitPhi1D`: explicit Phi1 D. -/
def explicitPhi1D (k n : Nat) (z : ℂ) : ℂ :=
  (((Real.sqrt ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ))) : ℂ)⁻¹) *
    explicitComplexHermite n k z

/-- `explicitPhi`: explicit Phi. -/
def explicitPhi {d : Nat} (kappa alpha : Fin d -> Nat) (z : Fin d -> ℂ) : ℂ :=
  Finset.prod Finset.univ fun q : Fin d => explicitPhi1D (kappa q) (alpha q) (z q)

/-- `explicitPkappaNorm`: explicit Pkappa Norm. -/
def explicitPkappaNorm {d : Nat} (F : Finsupp (Fin d -> Nat) ℂ) : ℝ :=
  Real.sqrt (Finset.sum F.support fun alpha => ‖F alpha‖ ^ 2)

/-- `explicitEvalPkappa`: explicit Eval Pkappa. -/
def explicitEvalPkappa {d : Nat} (kappa : Fin d -> Nat) (F : Finsupp (Fin d -> Nat) ℂ) :
    (Fin d -> ℂ) -> ℂ :=
  fun z => F.sum fun alpha c => c * explicitPhi kappa alpha z

private theorem explicitPkappaNorm_sq_eq_integral
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (F : Finsupp (Fin d -> ℕ) ℂ) :
    explicitPkappaNorm F ^ 2 =
      ∫ z, ‖explicitEvalPkappa κ F z‖ ^ 2 ∂ explicitGamma d := by
  have h := evalPkappa_total_mass hd κ F
  exact h.symm

private theorem explicitPkappaNorm_smul
    {d : ℕ} (c : ℂ) (F : Finsupp (Fin d -> ℕ) ℂ) :
    explicitPkappaNorm (c • F) = ‖c‖ * explicitPkappaNorm F := by
  classical
  by_cases hc : c = 0
  · subst c
    simp [explicitPkappaNorm]
  · change
      Real.sqrt (Finset.sum (c • F).support (fun α => ‖(c • F) α‖ ^ 2)) =
        ‖c‖ * Real.sqrt (Finset.sum F.support (fun α => ‖F α‖ ^ 2))
    rw [Finsupp.support_smul_eq hc]
    have hsum :
        Finset.sum F.support (fun α => ‖(c • F) α‖ ^ 2) =
          ‖c‖ ^ 2 * Finset.sum F.support (fun α => ‖F α‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro α halpha
      simp [Finsupp.smul_apply, mul_pow]
    rw [hsum, Real.sqrt_mul (sq_nonneg ‖c‖), Real.sqrt_sq_eq_abs]
    simp [abs_of_nonneg (norm_nonneg _)]

private theorem explicitPkappaNorm_pos_of_ne_zero
    {d : ℕ} {F : Finsupp (Fin d -> ℕ) ℂ} (hF : F ≠ 0) :
    0 < explicitPkappaNorm F := by
  classical
  rw [explicitPkappaNorm]
  apply Real.sqrt_pos.mpr
  have hexists : ∃ α, F α ≠ 0 := by
    by_contra hnone
    apply hF
    ext α
    exact not_not.mp (not_exists.mp hnone α)
  rcases hexists with ⟨α, halpha⟩
  have halpha_mem : α ∈ F.support := F.mem_support_iff.mpr halpha
  have hterm_pos : 0 < ‖F α‖ ^ 2 := sq_pos_of_ne_zero (by simpa using halpha)
  have hterm_le :
      ‖F α‖ ^ 2 ≤ Finset.sum F.support (fun β => ‖F β‖ ^ 2) := by
    exact Finset.single_le_sum (fun β hbeta => sq_nonneg ‖F β‖) halpha_mem
  exact lt_of_lt_of_le hterm_pos hterm_le

private theorem explicitPkappaNorm_normalized
    {d : ℕ} {F : Finsupp (Fin d -> ℕ) ℂ} (hF : F ≠ 0) :
    explicitPkappaNorm (((explicitPkappaNorm F : ℂ)⁻¹) • F) = 1 := by
  have hpos : 0 < explicitPkappaNorm F := explicitPkappaNorm_pos_of_ne_zero hF
  rw [explicitPkappaNorm_smul]
  have hnorm_inv : ‖((explicitPkappaNorm F : ℂ)⁻¹)‖ = (explicitPkappaNorm F)⁻¹ := by
    rw [norm_inv]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
  rw [hnorm_inv]
  field_simp [ne_of_gt hpos]

private theorem explicitModulusDefect_smul_of_nonneg
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ) (a : ℝ) (ha : 0 ≤ a)
    (F Q : Finsupp (Fin d -> ℕ) ℂ) :
    modulusDefect κ ((a : ℂ) • F) ((a : ℂ) • Q) =
      a * modulusDefect κ F Q := by
  unfold modulusDefect
  have hintegral :
      (∫ z,
          (‖evalPkappa κ ((a : ℂ) • Q) z‖ -
                ‖evalPkappa κ ((a : ℂ) • F) z‖) ^ 2
            ∂ gammaD d) =
        a ^ 2 *
          ∫ z,
            (‖evalPkappa κ Q z‖ - ‖evalPkappa κ F z‖) ^ 2
              ∂ gammaD d := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    rw [congrFun (evalPkappa_smul hd κ (a : ℂ) Q) z,
      congrFun (evalPkappa_smul hd κ (a : ℂ) F) z, norm_mul, norm_mul,
      Complex.norm_of_nonneg ha]
    ring
  rw [hintegral, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg ha]

private theorem modulusDefect_sq_eq_integral_rev
    {d : ℕ} (κ : Fin d -> ℕ)
    (F Q : Finsupp (Fin d -> ℕ) ℂ) :
    modulusDefect κ F Q ^ 2 =
      ∫ z,
        (‖explicitEvalPkappa κ F z‖ - ‖explicitEvalPkappa κ Q z‖) ^ 2
          ∂ explicitGamma d := by
  unfold modulusDefect
  rw [Real.sq_sqrt]
  · apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    have hF :
        explicitEvalPkappa κ F z = evalPkappa κ F z := by
      simp [explicitEvalPkappa, explicitPhi, explicitPhi1D, explicitComplexHermite,
        evalPkappa, Phi, phi1D, complexHermite]
    have hQ :
        explicitEvalPkappa κ Q z = evalPkappa κ Q z := by
      simp [explicitEvalPkappa, explicitPhi, explicitPhi1D, explicitComplexHermite,
        evalPkappa, Phi, phi1D, complexHermite]
    rw [hF, hQ]
    ring
  · exact MeasureTheory.integral_nonneg fun z => sq_nonneg _

private theorem phase_stability_coefficients_of_ne_zero
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (F : Finsupp (Fin d -> ℕ) ℂ) (hF : F ≠ 0) :
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ Q : Finsupp (Fin d -> ℕ) ℂ,
        ∃ phase : ℂ, ‖phase‖ = 1 ∧
          explicitPkappaNorm (phase • Q - F) ≤ C_F * modulusDefect κ F Q := by
  let a : ℝ := (explicitPkappaNorm F)⁻¹
  have hnorm_pos : 0 < explicitPkappaNorm F := explicitPkappaNorm_pos_of_ne_zero hF
  have ha_pos : 0 < a := inv_pos.mpr hnorm_pos
  let Fn : Finsupp (Fin d -> ℕ) ℂ := (a : ℂ) • F
  have hFn_norm : explicitPkappaNorm Fn = 1 := by
    have hcast_inv : (a : ℂ) = ((explicitPkappaNorm F : ℂ)⁻¹) := by
      simp [a]
    change explicitPkappaNorm ((a : ℂ) • F) = 1
    rw [hcast_inv]
    exact explicitPkappaNorm_normalized hF
  let Fpk : Pkappa d κ := Fn
  have hFn_norm' : ‖Fpk‖ = 1 := by
    change explicitPkappaNorm Fn = 1
    exact hFn_norm
  rcases phaseStability hd κ Fpk hFn_norm' with ⟨C_F, hC_F_pos, hstable⟩
  refine ⟨C_F, hC_F_pos, ?_⟩
  intro Q
  let Qn : Finsupp (Fin d -> ℕ) ℂ := (a : ℂ) • Q
  let Qnpk : Pkappa d κ := Qn
  rcases hstable Qnpk with ⟨phase, hphase, hbound⟩
  refine ⟨phase, hphase, ?_⟩
  have hbound' :
      explicitPkappaNorm (phase • Qn - Fn) ≤ C_F * modulusDefect κ Fn Qn :=
    hbound
  have hcoeff :
      phase • Qn - Fn = (a : ℂ) • (phase • Q - F) := by
    ext α
    simp only [Qn, Fn, Finsupp.sub_apply, Finsupp.smul_apply]
    change phase * ((a : ℂ) * Q α) - (a : ℂ) * F α =
      (a : ℂ) * (phase * Q α - F α)
    ring
  have hleft_scale :
      explicitPkappaNorm (phase • Qn - Fn) =
        a * explicitPkappaNorm (phase • Q - F) := by
    rw [hcoeff, explicitPkappaNorm_smul, Complex.norm_of_nonneg (le_of_lt ha_pos)]
  have hdef_scale :
      modulusDefect κ Fn Qn = a * modulusDefect κ F Q := by
    simpa [Fn, Qn] using explicitModulusDefect_smul_of_nonneg hd κ a (le_of_lt ha_pos) F Q
  have hscaled :
      a * explicitPkappaNorm (phase • Q - F) ≤
        C_F * (a * modulusDefect κ F Q) := by
    simpa [hleft_scale, hdef_scale] using hbound'
  have hscaled' :
      a * explicitPkappaNorm (phase • Q - F) ≤
        a * (C_F * modulusDefect κ F Q) := by
    calc
      a * explicitPkappaNorm (phase • Q - F)
          ≤ C_F * (a * modulusDefect κ F Q) := hscaled
      _ = a * (C_F * modulusDefect κ F Q) := by ring
  exact (mul_le_mul_iff_of_pos_left ha_pos).mp hscaled'

theorem stablePhaseRetrievalCoefficients
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (F : Finsupp (Fin d -> ℕ) ℂ) (hF : F ≠ 0) :
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ Q : Finsupp (Fin d -> ℕ) ℂ,
        ∃ θ : ℂ, ‖θ‖ = 1 ∧
          ∫ z, ‖explicitEvalPkappa κ F z - θ * explicitEvalPkappa κ Q z‖ ^ 2
              ∂ explicitGamma d
            ≤ C_F ^ 2 *
              ∫ z, (‖explicitEvalPkappa κ F z‖ - ‖explicitEvalPkappa κ Q z‖) ^ 2
                ∂ explicitGamma d := by
  rcases phase_stability_coefficients_of_ne_zero hd κ F hF with ⟨C_F, hC_F_pos, hstable⟩
  refine ⟨C_F, hC_F_pos, ?_⟩
  intro Q
  rcases hstable Q with ⟨θ, htheta, hbound⟩
  refine ⟨θ, htheta, ?_⟩
  have hbound_sq :
      explicitPkappaNorm (θ • Q - F) ^ 2 ≤ C_F ^ 2 * modulusDefect κ F Q ^ 2 := by
    have hdist_nonneg : 0 ≤ explicitPkappaNorm (θ • Q - F) := Real.sqrt_nonneg _
    have hdef_nonneg : 0 ≤ modulusDefect κ F Q := Real.sqrt_nonneg _
    nlinarith [hbound, hC_F_pos, hdist_nonneg, hdef_nonneg]
  have hleft :
      ∫ z, ‖explicitEvalPkappa κ F z - θ * explicitEvalPkappa κ Q z‖ ^ 2
          ∂ explicitGamma d =
        explicitPkappaNorm (θ • Q - F) ^ 2 := by
    calc
      ∫ z, ‖explicitEvalPkappa κ F z - θ * explicitEvalPkappa κ Q z‖ ^ 2
          ∂ explicitGamma d
          = ∫ z, ‖explicitEvalPkappa κ (θ • Q - F) z‖ ^ 2 ∂ explicitGamma d := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with z
            have hsub := congrFun (evalPkappa_sub hd κ (θ • Q) F) z
            have hsmul := congrFun (evalPkappa_smul hd κ θ Q) z
            rw [hsmul] at hsub
            have heval :
                explicitEvalPkappa κ (θ • Q - F) z =
                  θ * explicitEvalPkappa κ Q z - explicitEvalPkappa κ F z := by
              simpa [explicitEvalPkappa, explicitPhi, explicitPhi1D, explicitComplexHermite,
                evalPkappa, Phi, phi1D, complexHermite] using hsub
            rw [heval, norm_sub_rev]
      _ = explicitPkappaNorm (θ • Q - F) ^ 2 := by
            rw [← explicitPkappaNorm_sq_eq_integral hd κ (θ • Q - F)]
  rw [hleft, ← modulusDefect_sq_eq_integral_rev κ F Q]
  exact hbound_sq

theorem stablePhaseRetrievalCoefficientsAll
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (F : Finsupp (Fin d -> ℕ) ℂ) :
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ Q : Finsupp (Fin d -> ℕ) ℂ,
        ∃ θ : ℂ, ‖θ‖ = 1 ∧
          ∫ z, ‖explicitEvalPkappa κ F z - θ * explicitEvalPkappa κ Q z‖ ^ 2
              ∂ explicitGamma d
            ≤ C_F ^ 2 *
              ∫ z, (‖explicitEvalPkappa κ F z‖ - ‖explicitEvalPkappa κ Q z‖) ^ 2
                ∂ explicitGamma d := by
  by_cases hF : F = 0
  · subst F
    refine ⟨1, by norm_num, ?_⟩
    intro Q
    refine ⟨1, by simp, ?_⟩
    simp [explicitEvalPkappa]
  · exact stablePhaseRetrievalCoefficients hd κ F hF

theorem stablePhaseRetrievalExplicitRange
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ Set.range (explicitEvalPkappa κ)) :
    ∃ C_P : ℝ, 0 < C_P ∧
      ∀ Q : (Fin d -> ℂ) -> ℂ, Q ∈ Set.range (explicitEvalPkappa κ) →
        ∃ θ : ℂ, ‖θ‖ = 1 ∧
          ∫ z, ‖P z - θ * Q z‖ ^ 2 ∂ explicitGamma d
            ≤ C_P ^ 2 *
              ∫ z, (‖P z‖ - ‖Q z‖) ^ 2 ∂ explicitGamma d := by
  rcases hP with ⟨F, rfl⟩
  rcases stablePhaseRetrievalCoefficientsAll hd κ F with ⟨C_P, hC_P_pos, hstable⟩
  refine ⟨C_P, hC_P_pos, ?_⟩
  intro Q hQ
  rcases hQ with ⟨G, rfl⟩
  exact hstable G

/-! ## Closure upgrade -/

/-- `explicitGaussianL2DistanceSq`: explicit Gaussian L2 Distance Sq. -/
def explicitGaussianL2DistanceSq
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ) : ℝ :=
  ∫ z, ‖P z - Q z‖ ^ 2 ∂ explicitGamma d

/-- `explicitModulusDistanceSq`: explicit Modulus Distance Sq. -/
def explicitModulusDistanceSq
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ) : ℝ :=
  ∫ z, (‖P z‖ - ‖Q z‖) ^ 2 ∂ explicitGamma d

private theorem explicitGaussianL2DistanceSq_nonneg
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ) :
    0 ≤ explicitGaussianL2DistanceSq P Q :=
  MeasureTheory.integral_nonneg fun _ => sq_nonneg _

private theorem explicitModulusDistanceSq_nonneg
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ) :
    0 ≤ explicitModulusDistanceSq P Q :=
  MeasureTheory.integral_nonneg fun _ => sq_nonneg _

private theorem sqrt_integral_norm_sq_eq_lpNorm
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (F : (Fin d -> ℂ) -> E)
    (hF : MeasureTheory.AEStronglyMeasurable F (explicitGamma d)) :
    Real.sqrt (∫ z, ‖F z‖ ^ 2 ∂ explicitGamma d) =
      MeasureTheory.lpNorm F 2 (explicitGamma d) := by
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  have hlp := MeasureTheory.lpNorm_nnreal_eq_integral_norm_rpow
    (μ := explicitGamma d) (p := (2 : NNReal)) (f := F) htwo hF
  change
    Real.sqrt (∫ z, ‖F z‖ ^ 2 ∂ explicitGamma d) =
      MeasureTheory.lpNorm F (↑(2 : NNReal)) (explicitGamma d)
  rw [hlp]
  change
    Real.sqrt (∫ z, ‖F z‖ ^ 2 ∂ explicitGamma d) =
      (∫ z, ‖F z‖ ^ (2 : ℝ) ∂ explicitGamma d) ^ ((2 : ℝ)⁻¹)
  rw [show (∫ z, ‖F z‖ ^ (2 : ℝ) ∂ explicitGamma d) =
      ∫ z, ‖F z‖ ^ 2 ∂ explicitGamma d by
    congr 1
    ext z
    exact Real.rpow_natCast ‖F z‖ 2]
  rw [Real.sqrt_eq_rpow]
  norm_num

private theorem sqrt_explicitGaussianL2DistanceSq_eq_lpNorm
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ)
    (hPQ : MeasureTheory.AEStronglyMeasurable (fun z => P z - Q z)
      (explicitGamma d)) :
    Real.sqrt (explicitGaussianL2DistanceSq P Q) =
      MeasureTheory.lpNorm (fun z => P z - Q z) 2 (explicitGamma d) := by
  simpa [explicitGaussianL2DistanceSq] using
    sqrt_integral_norm_sq_eq_lpNorm (d := d) (fun z => P z - Q z) hPQ

private theorem sqrt_explicitModulusDistanceSq_eq_lpNorm
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ)
    (hPQ : MeasureTheory.AEStronglyMeasurable
      (fun z => ‖P z‖ - ‖Q z‖) (explicitGamma d)) :
    Real.sqrt (explicitModulusDistanceSq P Q) =
      MeasureTheory.lpNorm (fun z => ‖P z‖ - ‖Q z‖) 2
        (explicitGamma d) := by
  simpa [explicitModulusDistanceSq, Real.norm_eq_abs, sq_abs] using
    sqrt_integral_norm_sq_eq_lpNorm (d := d)
      (fun z => ‖P z‖ - ‖Q z‖) hPQ

private theorem memLp_of_explicitHermitePoly
    {d : ℕ} (hd : 0 < d) {κ : Fin d -> ℕ} {Q : (Fin d -> ℂ) -> ℂ}
    (hQ : Q ∈ Set.range (explicitEvalPkappa κ)) :
    MeasureTheory.MemLp Q 2 (explicitGamma d) := by
  rcases hQ with ⟨F, rfl⟩
  have hmem := memLp_two_evalPkappa hd κ F
  exact hmem

/-- `UnitPhase`: Unit Phase. -/
def UnitPhase : Type :=
  { θ : ℂ // ‖θ‖ = 1 }

instance : TopologicalSpace UnitPhase :=
  inferInstanceAs (TopologicalSpace { θ : ℂ // ‖θ‖ = 1 })

instance : MetricSpace UnitPhase :=
  inferInstanceAs (MetricSpace { θ : ℂ // ‖θ‖ = 1 })

instance : CompactSpace UnitPhase := by
  change CompactSpace { θ : ℂ // ‖θ‖ = 1 }
  apply isCompact_iff_compactSpace.mp
  have h : IsCompact (Metric.sphere (0 : ℂ) 1) := isCompact_sphere (0 : ℂ) 1
  convert h using 1
  ext z
  change (‖z‖ = 1) ↔ z ∈ Metric.sphere (0 : ℂ) 1
  rw [Metric.mem_sphere, dist_zero_right]

instance : Inhabited UnitPhase :=
  ⟨⟨1, by simp⟩⟩

/-- `explicitPhaseOptimizedDistanceSq`: explicit Phase Optimized Distance Sq. -/
def explicitPhaseOptimizedDistanceSq
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ) : ℝ :=
  sInf (Set.range fun θ : UnitPhase =>
    explicitGaussianL2DistanceSq P (fun z => θ.1 * Q z))

private theorem explicitGaussianL2DistanceSq_phase_eq_l2_norm_sq
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ)
    (hP : MeasureTheory.MemLp P 2 (explicitGamma d))
    (hQ : MeasureTheory.MemLp Q 2 (explicitGamma d))
    (θ : UnitPhase) :
    explicitGaussianL2DistanceSq P (fun z => θ.1 * Q z) =
      ‖hP.toLp P - θ.1 • hQ.toLp Q‖ ^ 2 := by
  have hθQ : MeasureTheory.MemLp (fun z => θ.1 * Q z) 2 (explicitGamma d) := by
    refine MeasureTheory.MemLp.ae_eq ?_ (hQ.const_smul θ.1)
    filter_upwards with z
    simp only [Pi.smul_apply, smul_eq_mul]
  have hdiff : MeasureTheory.MemLp (fun z => P z - θ.1 * Q z) 2 (explicitGamma d) :=
    hP.sub hθQ
  have hsqrt :=
    sqrt_explicitGaussianL2DistanceSq_eq_lpNorm P (fun z => θ.1 * Q z) hdiff.1
  have hnorm :
      ‖(hP.sub hθQ).toLp (fun z => P z - θ.1 * Q z)‖ =
        MeasureTheory.lpNorm (fun z => P z - θ.1 * Q z) 2 (explicitGamma d) := by
    rw [MeasureTheory.Lp.norm_toLp]
    exact MeasureTheory.toReal_eLpNorm hdiff.1
  have htoLp :
      (hP.sub hθQ).toLp (fun z => P z - θ.1 * Q z) =
        hP.toLp P - θ.1 • hQ.toLp Q := by
    change (hP.sub hθQ).toLp (P - fun z => θ.1 * Q z) =
      hP.toLp P - θ.1 • hQ.toLp Q
    rw [MeasureTheory.MemLp.toLp_sub]
    change hP.toLp P - hθQ.toLp (θ.1 • Q) =
      hP.toLp P - θ.1 • hQ.toLp Q
    rw [MeasureTheory.MemLp.toLp_const_smul]
  rw [← Real.sq_sqrt (explicitGaussianL2DistanceSq_nonneg P (fun z => θ.1 * Q z))]
  rw [hsqrt]
  rw [← hnorm]
  rw [htoLp]

private theorem explicitPhaseOptimizedDistanceSq_attained
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ)
    (hP : MeasureTheory.MemLp P 2 (explicitGamma d))
    (hQ : MeasureTheory.MemLp Q 2 (explicitGamma d)) :
    ∃ θ : ℂ, ‖θ‖ = 1 ∧
      explicitGaussianL2DistanceSq P (fun z => θ * Q z) =
        explicitPhaseOptimizedDistanceSq P Q := by
  let objective : UnitPhase -> ℝ :=
    fun θ => ‖hP.toLp P - θ.1 • hQ.toLp Q‖ ^ 2
  have hcontinuous : Continuous objective := by
    dsimp [objective]
    fun_prop
  rcases isCompact_univ.exists_isMinOn
      (Set.univ_nonempty : (Set.univ : Set UnitPhase).Nonempty)
      hcontinuous.continuousOn with
    ⟨θ₀, _hθ₀_mem, hθ₀_min⟩
  have hobjective :
      ∀ θ : UnitPhase,
        explicitGaussianL2DistanceSq P (fun z => θ.1 * Q z) = objective θ := by
    intro θ
    exact explicitGaussianL2DistanceSq_phase_eq_l2_norm_sq P Q hP hQ θ
  refine ⟨θ₀.1, θ₀.2, ?_⟩
  have hbdd :
      BddBelow (Set.range fun θ : UnitPhase =>
        explicitGaussianL2DistanceSq P (fun z => θ.1 * Q z)) := by
    refine ⟨0, ?_⟩
    rintro r ⟨θ, rfl⟩
    exact explicitGaussianL2DistanceSq_nonneg P (fun z => θ.1 * Q z)
  have hle :
      explicitPhaseOptimizedDistanceSq P Q ≤
        explicitGaussianL2DistanceSq P (fun z => θ₀.1 * Q z) := by
    exact csInf_le hbdd ⟨θ₀, rfl⟩
  have hge :
      explicitGaussianL2DistanceSq P (fun z => θ₀.1 * Q z) ≤
        explicitPhaseOptimizedDistanceSq P Q := by
    unfold explicitPhaseOptimizedDistanceSq
    refine le_csInf (Set.range_nonempty _) ?_
    rintro r ⟨θ, rfl⟩
    change explicitGaussianL2DistanceSq P (fun z => θ₀.1 * Q z) ≤
      explicitGaussianL2DistanceSq P (fun z => θ.1 * Q z)
    rw [hobjective θ]
    rw [hobjective θ₀]
    exact hθ₀_min trivial
  exact le_antisymm hge hle

/-- `explicitHermiteLpPolys`: explicit Hermite Lp Polys. -/
def explicitHermiteLpPolys
    {d : ℕ} (κ : Fin d -> ℕ) :
    Set (MeasureTheory.Lp ℂ 2 (explicitGamma d)) :=
  { f |
    ∃ P : (Fin d -> ℂ) -> ℂ,
      P ∈ Set.range (explicitEvalPkappa κ) ∧
        ∃ hP : MeasureTheory.MemLp P 2 (explicitGamma d), hP.toLp P = f }

/-- `explicitClosureOfHermitePolys`: explicit Closure Of Hermite Polys. -/
def explicitClosureOfHermitePolys
    {d : ℕ} (κ : Fin d -> ℕ) : Set ((Fin d -> ℂ) -> ℂ) :=
  { Q |
    ∃ hQ : MeasureTheory.MemLp Q 2 (explicitGamma d),
      hQ.toLp Q ∈ closure (explicitHermiteLpPolys κ) }

private def explicitSequentialClosureOfHermitePolys
    {d : ℕ} (κ : Fin d -> ℕ) : Set ((Fin d -> ℂ) -> ℂ) :=
  { Q |
    MeasureTheory.MemLp Q 2 (explicitGamma d) ∧
      ∃ Qn : ℕ -> (Fin d -> ℂ) -> ℂ,
        (∀ n, Qn n ∈ Set.range (explicitEvalPkappa κ)) ∧
          Filter.Tendsto
            (fun n => explicitGaussianL2DistanceSq (Qn n) Q)
            Filter.atTop (nhds (0 : ℝ)) }

theorem explicitHermitePolys_subset_explicitClosure
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ) :
    Set.range (explicitEvalPkappa κ) ⊆ explicitClosureOfHermitePolys κ := by
  intro Q hQ
  rcases hQ with ⟨F, rfl⟩
  let hmem : MeasureTheory.MemLp (explicitEvalPkappa κ F) 2 (explicitGamma d) :=
    memLp_of_explicitHermitePoly hd ⟨F, rfl⟩
  refine ⟨hmem, subset_closure ?_⟩
  exact ⟨explicitEvalPkappa κ F, ⟨F, rfl⟩, hmem, rfl⟩

private theorem explicitClosure_subset_explicitSequentialClosure
    {d : ℕ} (κ : Fin d -> ℕ) :
    explicitClosureOfHermitePolys κ ⊆ explicitSequentialClosureOfHermitePolys κ := by
  classical
  intro Q hQ
  rcases hQ with ⟨hQ_mem, hQ_closure⟩
  refine ⟨hQ_mem, ?_⟩
  rw [mem_closure_iff_seq_limit] at hQ_closure
  rcases hQ_closure with ⟨fn, hfn_mem, hfn_lim⟩
  choose Qn hQn_poly hQn_tail using hfn_mem
  choose hQn_mem hQn_toLp using fun n => hQn_tail n
  refine ⟨Qn, hQn_poly, ?_⟩
  have hdist :
      Filter.Tendsto (fun n => dist (fn n) (hQ_mem.toLp Q))
        Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.mp hfn_lim
  have hsqrt :
      ∀ n, Real.sqrt (explicitGaussianL2DistanceSq (Qn n) Q) =
        dist (fn n) (hQ_mem.toLp Q) := by
    intro n
    rw [← hQn_toLp n]
    rw [MeasureTheory.Lp.dist_def]
    have hsub_mem : MeasureTheory.MemLp (fun z => Qn n z - Q z) 2 (explicitGamma d) :=
      (hQn_mem n).sub hQ_mem
    have hae :
        (⇑((hQn_mem n).toLp (Qn n)) - ⇑(hQ_mem.toLp Q) : (Fin d -> ℂ) -> ℂ)
          =ᵐ[explicitGamma d] fun z => Qn n z - Q z :=
      ((hQn_mem n).coeFn_toLp.sub hQ_mem.coeFn_toLp)
    have heLp :
        MeasureTheory.eLpNorm
            (⇑((hQn_mem n).toLp (Qn n)) - ⇑(hQ_mem.toLp Q)) 2 (explicitGamma d) =
          MeasureTheory.eLpNorm (fun z => Qn n z - Q z) 2 (explicitGamma d) :=
      MeasureTheory.eLpNorm_congr_ae hae
    rw [sqrt_explicitGaussianL2DistanceSq_eq_lpNorm (Qn n) Q hsub_mem.1,
      ← MeasureTheory.toReal_eLpNorm hsub_mem.1, heLp]
  have hsqrt_tendsto :
      Filter.Tendsto
        (fun n => Real.sqrt (explicitGaussianL2DistanceSq (Qn n) Q))
        Filter.atTop (nhds (0 : ℝ)) := by
    simpa [hsqrt] using hdist
  have hsq :
      (fun n => explicitGaussianL2DistanceSq (Qn n) Q) =
        fun n => (Real.sqrt (explicitGaussianL2DistanceSq (Qn n) Q)) ^ 2 := by
    funext n
    rw [Real.sq_sqrt (explicitGaussianL2DistanceSq_nonneg (Qn n) Q)]
  rw [hsq]
  simpa using hsqrt_tendsto.pow 2

private theorem stablePhaseRetrievalExplicitRange_phaseOptimized
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ Set.range (explicitEvalPkappa κ)) :
    ∃ C_P : ℝ, 0 < C_P ∧
      ∀ Q : (Fin d -> ℂ) -> ℂ, Q ∈ Set.range (explicitEvalPkappa κ) →
        explicitPhaseOptimizedDistanceSq P Q ≤
          C_P ^ 2 * explicitModulusDistanceSq P Q := by
  rcases stablePhaseRetrievalExplicitRange hd κ P hP with ⟨C_P, hC_P_pos, hstable⟩
  refine ⟨C_P, hC_P_pos, ?_⟩
  intro Q hQ
  rcases hstable Q hQ with ⟨θ, hθ, hbound⟩
  have hle :
      explicitPhaseOptimizedDistanceSq P Q ≤
        explicitGaussianL2DistanceSq P (fun z => θ * Q z) := by
    have hbdd :
        BddBelow (Set.range fun θ' : UnitPhase =>
          explicitGaussianL2DistanceSq P (fun z => θ'.1 * Q z)) := by
      refine ⟨0, ?_⟩
      rintro r ⟨θ', rfl⟩
      exact explicitGaussianL2DistanceSq_nonneg P (fun z => θ'.1 * Q z)
    exact csInf_le hbdd ⟨⟨θ, hθ⟩, rfl⟩
  change
    explicitGaussianL2DistanceSq P (fun z => θ * Q z) ≤
      C_P ^ 2 * explicitModulusDistanceSq P Q at hbound
  exact hle.trans hbound

private theorem explicitPhaseOptimized_bound_of_l2_closure
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (P Q : (Fin d -> ℂ) -> ℂ) (C_P : ℝ)
    (hC_P_pos : 0 < C_P)
    (hP_mem : MeasureTheory.MemLp P 2 (explicitGamma d))
    (hQ_mem : MeasureTheory.MemLp Q 2 (explicitGamma d))
    (Qn : ℕ -> (Fin d -> ℂ) -> ℂ)
    (hQn_poly : ∀ n, Qn n ∈ Set.range (explicitEvalPkappa κ))
    (hQn_lim :
      Filter.Tendsto
        (fun n => explicitGaussianL2DistanceSq (Qn n) Q)
        Filter.atTop (nhds (0 : ℝ)))
    (hfinite :
      ∀ n, ∃ θ : ℂ, ‖θ‖ = 1 ∧
        explicitGaussianL2DistanceSq P (fun z => θ * Qn n z) ≤
          C_P ^ 2 * explicitModulusDistanceSq P (Qn n)) :
    explicitPhaseOptimizedDistanceSq P Q ≤
      C_P ^ 2 * explicitModulusDistanceSq P Q := by
  let δ : ℕ -> ℝ := fun n => Real.sqrt (explicitGaussianL2DistanceSq (Qn n) Q)
  let M : ℝ := explicitModulusDistanceSq P Q
  have hM_nonneg : 0 ≤ M := by
    exact explicitModulusDistanceSq_nonneg P Q
  have hδ_tendsto : Filter.Tendsto δ Filter.atTop (nhds (0 : ℝ)) := by
    simpa [δ] using hQn_lim.sqrt
  have hbound_n :
      ∀ n,
        explicitPhaseOptimizedDistanceSq P Q ≤
          (C_P * (Real.sqrt M + δ n) + δ n) ^ 2 := by
    intro n
    rcases hfinite n with ⟨θ, hθ, hθ_bound⟩
    have hQn_mem : MeasureTheory.MemLp (Qn n) 2 (explicitGamma d) :=
      memLp_of_explicitHermitePoly hd (hQn_poly n)
    have hθQ_mem : MeasureTheory.MemLp (fun z => θ * Q z) 2 (explicitGamma d) := by
      refine MeasureTheory.MemLp.ae_eq ?_ (hQ_mem.const_smul θ)
      filter_upwards with z
      simp only [Pi.smul_apply, smul_eq_mul]
    have hθQn_mem :
        MeasureTheory.MemLp (fun z => θ * Qn n z) 2 (explicitGamma d) := by
      refine MeasureTheory.MemLp.ae_eq ?_ (hQn_mem.const_smul θ)
      filter_upwards with z
      simp only [Pi.smul_apply, smul_eq_mul]
    have hPQθ_mem : MeasureTheory.MemLp (fun z => P z - θ * Q z) 2
        (explicitGamma d) :=
      hP_mem.sub hθQ_mem
    have hPQnθ_mem : MeasureTheory.MemLp (fun z => P z - θ * Qn n z) 2
        (explicitGamma d) :=
      hP_mem.sub hθQn_mem
    have hQnQ_mem : MeasureTheory.MemLp (fun z => Qn n z - Q z) 2
        (explicitGamma d) :=
      hQn_mem.sub hQ_mem
    have hphase_tri :
        Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Q z)) ≤
          Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Qn n z)) +
            δ n := by
      rw [sqrt_explicitGaussianL2DistanceSq_eq_lpNorm P (fun z => θ * Q z)
          hPQθ_mem.1,
        sqrt_explicitGaussianL2DistanceSq_eq_lpNorm P (fun z => θ * Qn n z)
          hPQnθ_mem.1]
      have hdecomp :
          (fun z => P z - θ * Q z) =
            fun z => (P z - θ * Qn n z) + θ * (Qn n z - Q z) := by
        funext z
        ring
      rw [hdecomp]
      have htri :=
        MeasureTheory.lpNorm_add_le
          (p := (2 : ENNReal))
          (μ := explicitGamma d)
          (f := fun z => P z - θ * Qn n z)
          (g := fun z => θ * (Qn n z - Q z))
          hPQnθ_mem (by norm_num)
      have hscale :
          MeasureTheory.lpNorm (fun z => θ * (Qn n z - Q z)) 2
              (explicitGamma d) =
            MeasureTheory.lpNorm (fun z => Qn n z - Q z) 2
              (explicitGamma d) := by
        rw [show (fun z => θ * (Qn n z - Q z)) =
            θ • (fun z => Qn n z - Q z) by rfl]
        rw [MeasureTheory.lpNorm_const_smul]
        simp [hθ]
      rw [hscale] at htri
      have hδ_eq :
          MeasureTheory.lpNorm (fun z => Qn n z - Q z) 2 (explicitGamma d) =
            δ n := by
        rw [← sqrt_explicitGaussianL2DistanceSq_eq_lpNorm (Qn n) Q hQnQ_mem.1]
      rw [hδ_eq] at htri
      rw [show (fun z => P z - θ * Qn n z + θ * (Qn n z - Q z)) =
          (fun z => P z - θ * Qn n z) + fun z => θ * (Qn n z - Q z) from rfl]
      exact htri
    have hfinite_sqrt :
        Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Qn n z)) ≤
          C_P * Real.sqrt (explicitModulusDistanceSq P (Qn n)) := by
      have hsqrt := Real.sqrt_le_sqrt hθ_bound
      have hsimp :
          Real.sqrt (C_P ^ 2 * explicitModulusDistanceSq P (Qn n)) =
            C_P * Real.sqrt (explicitModulusDistanceSq P (Qn n)) := by
        rw [Real.sqrt_mul (sq_nonneg C_P), Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg (le_of_lt hC_P_pos)]
      simpa [hsimp] using hsqrt
    have hmod_tri :
        Real.sqrt (explicitModulusDistanceSq P (Qn n)) ≤ Real.sqrt M + δ n := by
      have hmodQ_mem :
          MeasureTheory.MemLp (fun z => ‖P z‖ - ‖Q z‖) 2
            (explicitGamma d) :=
        hP_mem.norm.sub hQ_mem.norm
      have hmodQn_mem :
          MeasureTheory.MemLp (fun z => ‖P z‖ - ‖Qn n z‖) 2
            (explicitGamma d) :=
        hP_mem.norm.sub hQn_mem.norm
      have hnormdiff_mem :
          MeasureTheory.MemLp (fun z => ‖Q z‖ - ‖Qn n z‖) 2
            (explicitGamma d) :=
        hQ_mem.norm.sub hQn_mem.norm
      rw [sqrt_explicitModulusDistanceSq_eq_lpNorm P (Qn n) hmodQn_mem.1,
        sqrt_explicitModulusDistanceSq_eq_lpNorm P Q hmodQ_mem.1]
      change
        MeasureTheory.lpNorm (fun z => ‖P z‖ - ‖Qn n z‖) 2 (explicitGamma d) ≤
          MeasureTheory.lpNorm (fun z => ‖P z‖ - ‖Q z‖) 2 (explicitGamma d) +
            δ n
      have hdecomp :
          (fun z => ‖P z‖ - ‖Qn n z‖) =
            fun z => (‖P z‖ - ‖Q z‖) + (‖Q z‖ - ‖Qn n z‖) := by
        funext z
        ring
      rw [hdecomp]
      have htri :=
        MeasureTheory.lpNorm_add_le
          (p := (2 : ENNReal))
          (μ := explicitGamma d)
          (f := fun z => ‖P z‖ - ‖Q z‖)
          (g := fun z => ‖Q z‖ - ‖Qn n z‖)
          hmodQ_mem (by norm_num)
      have hsecond :
          MeasureTheory.lpNorm (fun z => ‖Q z‖ - ‖Qn n z‖) 2
              (explicitGamma d) ≤
            MeasureTheory.lpNorm (fun z => Qn n z - Q z) 2 (explicitGamma d) := by
        calc
          MeasureTheory.lpNorm (fun z => ‖Q z‖ - ‖Qn n z‖) 2 (explicitGamma d)
              ≤ MeasureTheory.lpNorm (fun z => ‖Qn n z - Q z‖) 2
                  (explicitGamma d) := by
                refine MeasureTheory.lpNorm_mono_real hQnQ_mem.norm ?_
                intro z
                have h := abs_norm_sub_norm_le (Q z) (Qn n z)
                simpa [Real.norm_eq_abs, norm_sub_rev] using h
          _ = MeasureTheory.lpNorm (fun z => Qn n z - Q z) 2
                (explicitGamma d) := by
                rw [MeasureTheory.lpNorm_norm hQnQ_mem.1]
      have hδ_eq :
          MeasureTheory.lpNorm (fun z => Qn n z - Q z) 2 (explicitGamma d) =
            δ n := by
        rw [← sqrt_explicitGaussianL2DistanceSq_eq_lpNorm (Qn n) Q hQnQ_mem.1]
      rw [hδ_eq] at hsecond
      exact htri.trans (add_le_add_right hsecond _)
    have hsqrt_total :
        Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Q z)) ≤
          C_P * (Real.sqrt M + δ n) + δ n := by
      calc
        Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Q z))
            ≤ Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Qn n z)) +
                δ n :=
              hphase_tri
        _ ≤ C_P * Real.sqrt (explicitModulusDistanceSq P (Qn n)) + δ n := by
              exact add_le_add hfinite_sqrt le_rfl
        _ ≤ C_P * (Real.sqrt M + δ n) + δ n := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hmod_tri (le_of_lt hC_P_pos)) le_rfl
    have hphase_inf :
        explicitPhaseOptimizedDistanceSq P Q ≤
          explicitGaussianL2DistanceSq P (fun z => θ * Q z) := by
      have hbdd :
          BddBelow (Set.range fun θ' : UnitPhase =>
            explicitGaussianL2DistanceSq P (fun z => θ'.1 * Q z)) := by
        refine ⟨0, ?_⟩
        rintro r ⟨θ', rfl⟩
        exact explicitGaussianL2DistanceSq_nonneg P (fun z => θ'.1 * Q z)
      exact csInf_le hbdd ⟨⟨θ, hθ⟩, rfl⟩
    have htarget_sq :
        explicitGaussianL2DistanceSq P (fun z => θ * Q z) ≤
          (C_P * (Real.sqrt M + δ n) + δ n) ^ 2 := by
      let B : ℝ := C_P * (Real.sqrt M + δ n) + δ n
      have hB_nonneg : 0 ≤ B := by
        have hδ_nonneg : 0 ≤ δ n := Real.sqrt_nonneg _
        have hsqrtM_nonneg : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
        dsimp [B]
        nlinarith [hC_P_pos, hδ_nonneg, hsqrtM_nonneg]
      have hg_nonneg :
          0 ≤ explicitGaussianL2DistanceSq P (fun z => θ * Q z) :=
        explicitGaussianL2DistanceSq_nonneg P (fun z => θ * Q z)
      have habs :
          |Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Q z))| ≤ |B| := by
        simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hB_nonneg, B]
          using hsqrt_total
      have hsquares :
          Real.sqrt (explicitGaussianL2DistanceSq P (fun z => θ * Q z)) ^ 2 ≤
            B ^ 2 :=
        (sq_le_sq).2 habs
      simpa [B, Real.sq_sqrt hg_nonneg] using hsquares
    exact hphase_inf.trans htarget_sq
  have hlim_rhs :
      Filter.Tendsto
        (fun n => (C_P * (Real.sqrt M + δ n) + δ n) ^ 2)
        Filter.atTop (nhds (C_P ^ 2 * M)) := by
    have hinner :
        Filter.Tendsto (fun n => C_P * (Real.sqrt M + δ n) + δ n)
          Filter.atTop (nhds (C_P * (Real.sqrt M + 0) + 0)) := by
      exact (((tendsto_const_nhds.add hδ_tendsto).const_mul C_P).add hδ_tendsto)
    have hpow := hinner.pow 2
    convert hpow using 1
    ring_nf
    rw [Real.sq_sqrt hM_nonneg]
  have hconst :
      Filter.Tendsto (fun _ : ℕ => explicitPhaseOptimizedDistanceSq P Q)
        Filter.atTop (nhds (explicitPhaseOptimizedDistanceSq P Q)) :=
    tendsto_const_nhds
  exact le_of_tendsto_of_tendsto hconst hlim_rhs (Filter.Eventually.of_forall hbound_n)

theorem stablePhaseRetrievalExplicitClosure
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ Set.range (explicitEvalPkappa κ)) :
    ∃ C_P : ℝ, 0 < C_P ∧
      ∀ Q : (Fin d -> ℂ) -> ℂ, Q ∈ explicitClosureOfHermitePolys κ →
        explicitPhaseOptimizedDistanceSq P Q ≤
          C_P ^ 2 * explicitModulusDistanceSq P Q := by
  rcases stablePhaseRetrievalExplicitRange hd κ P hP with ⟨C_P, hC_P_pos, hfinite⟩
  have hP_mem : MeasureTheory.MemLp P 2 (explicitGamma d) :=
    memLp_of_explicitHermitePoly hd hP
  refine ⟨C_P, hC_P_pos, ?_⟩
  intro Q hQ
  have hQ_seq := explicitClosure_subset_explicitSequentialClosure κ hQ
  rcases hQ_seq with ⟨hQ_mem, Qn, hQn_poly, hQn_lim⟩
  exact explicitPhaseOptimized_bound_of_l2_closure hd κ P Q C_P hC_P_pos hP_mem
    hQ_mem Qn hQn_poly hQn_lim (fun n => by
      rcases hfinite (Qn n) (hQn_poly n) with ⟨θ, hθ, hbound⟩
      exact ⟨θ, hθ, by
        simpa [explicitGaussianL2DistanceSq, explicitModulusDistanceSq] using hbound⟩)

theorem stablePhaseRetrievalExplicitLpClosure
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ Set.range (explicitEvalPkappa κ)) :
    ∃ C_P : ℝ, 0 < C_P ∧
      ∀ Q : MeasureTheory.Lp ℂ 2 (explicitGamma d),
        Q ∈ closure (explicitHermiteLpPolys κ) →
          explicitPhaseOptimizedDistanceSq P (Q : (Fin d -> ℂ) -> ℂ) ≤
            C_P ^ 2 * explicitModulusDistanceSq P (Q : (Fin d -> ℂ) -> ℂ) := by
  rcases stablePhaseRetrievalExplicitClosure hd κ P hP with ⟨C_P, hC_P_pos, hbound⟩
  refine ⟨C_P, hC_P_pos, ?_⟩
  intro Q hQ
  have hQ_raw :
      (Q : (Fin d -> ℂ) -> ℂ) ∈ explicitClosureOfHermitePolys κ := by
    refine ⟨MeasureTheory.Lp.memLp Q, ?_⟩
    simpa [explicitClosureOfHermitePolys] using hQ
  exact hbound (Q : (Fin d -> ℂ) -> ℂ) hQ_raw

theorem stablePhaseRetrievalExplicitLpClosure_exists
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ Set.range (explicitEvalPkappa κ)) :
    ∃ C_P : ℝ, 0 < C_P ∧
      ∀ Q : MeasureTheory.Lp ℂ 2 (explicitGamma d),
        Q ∈ closure (explicitHermiteLpPolys κ) →
          ∃ θ : ℂ, ‖θ‖ = 1 ∧
            explicitGaussianL2DistanceSq P (fun z => θ * Q z) ≤
              C_P ^ 2 * explicitModulusDistanceSq P (Q : (Fin d -> ℂ) -> ℂ) := by
  rcases stablePhaseRetrievalExplicitLpClosure hd κ P hP with ⟨C_P, hC_P_pos, hbound⟩
  have hP_mem : MeasureTheory.MemLp P 2 (explicitGamma d) :=
    memLp_of_explicitHermitePoly hd hP
  refine ⟨C_P, hC_P_pos, ?_⟩
  intro Q hQ
  have hQ_mem : MeasureTheory.MemLp (Q : (Fin d -> ℂ) -> ℂ) 2 (explicitGamma d) :=
    MeasureTheory.Lp.memLp Q
  rcases explicitPhaseOptimizedDistanceSq_attained P (Q : (Fin d -> ℂ) -> ℂ)
      hP_mem hQ_mem with
    ⟨θ, hθ, hθ_eq⟩
  refine ⟨θ, hθ, ?_⟩
  rw [hθ_eq]
  exact hbound Q hQ

private theorem explicitHermiteLpPolys_eq_ae
    {d : ℕ} (κ : Fin d -> ℕ) :
    explicitHermiteLpPolys κ =
      { f : MeasureTheory.Lp ℂ 2 (explicitGamma d) |
        ∃ P ∈ Set.range (explicitEvalPkappa κ), f =ᵐ[explicitGamma d] P } := by
  ext f
  constructor
  · rintro ⟨P, hP, hP_mem, hP_toLp⟩
    subst f
    exact ⟨P, hP, hP_mem.coeFn_toLp⟩
  · rintro ⟨P, hP, hAe⟩
    have hf_mem : MeasureTheory.MemLp (f : (Fin d -> ℂ) -> ℂ) 2 (explicitGamma d) :=
      MeasureTheory.Lp.memLp f
    have hP_mem : MeasureTheory.MemLp P 2 (explicitGamma d) := by
      exact (MeasureTheory.memLp_congr_ae hAe).mp hf_mem
    refine ⟨P, hP, hP_mem, ?_⟩
    rw [← MeasureTheory.Lp.toLp_coeFn f hf_mem]
    exact (MeasureTheory.MemLp.toLp_eq_toLp_iff hP_mem hf_mem).2 hAe.symm

theorem stablePhaseRetrievalExplicitLpClosure_ae
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ Set.range (explicitEvalPkappa κ)) :
    ∃ C_P : ℝ, 0 < C_P ∧
      ∀ Q : MeasureTheory.Lp ℂ 2 (explicitGamma d),
        Q ∈ closure
          { f : MeasureTheory.Lp ℂ 2 (explicitGamma d) |
            ∃ P ∈ Set.range (explicitEvalPkappa κ), f =ᵐ[explicitGamma d] P } →
          ∃ θ : ℂ, ‖θ‖ = 1 ∧
            explicitGaussianL2DistanceSq P (fun z => θ * Q z) ≤
              C_P ^ 2 * explicitModulusDistanceSq P (Q : (Fin d -> ℂ) -> ℂ) := by
  rcases stablePhaseRetrievalExplicitLpClosure_exists hd κ P hP with
    ⟨C_P, hC_P_pos, hbound⟩
  refine ⟨C_P, hC_P_pos, ?_⟩
  intro Q hQ
  exact hbound Q (by simpa [explicitHermiteLpPolys_eq_ae κ] using hQ)

end DimdPolyLEAN
