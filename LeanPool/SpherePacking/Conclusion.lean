/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

module

public import LeanPool.SpherePacking.PackingBound
import all LeanPool.SpherePacking.PackingBound
public import LeanPool.SpherePacking.Foundations
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Conclusion

Sharp radial and unrestricted sphere-packing conclusions.
-/

section

open Filter
open scoped FourierTransform SchwartzMap Topology

namespace PackingBounds.RadialMain

private theorem exact_limit :
    Tendsto
      (fun d : ℕ =>
        CohnElkies.linearProgram d ^ ((d : ℝ)⁻¹))
      atTop
      (nhds (Real.sqrt (Real.exp 1 / (2 * Real.pi)))) := by
  simpa only [CohnElkies.SharpPackingRootAsymptotic, CohnElkies.criticalPackingBase] using!
    CohnElkies.sharpPackingRootAsymptotic

private theorem exact_binary_exponent :
    Tendsto
      (fun d : ℕ =>
        Real.logb 2 (CohnElkies.linearProgram d) / (d : ℝ))
      atTop
      (nhds (-(1 / 2 : ℝ) *
        Real.logb 2 (2 * Real.pi / Real.exp 1))) := by
  simpa only [one_div, neg_mul, CohnElkies.SharpBinaryLogAsymptotic,
    CohnElkies.criticalBinaryExponent] using!
    CohnElkies.sharpBinaryLogAsymptotic

end PackingBounds.RadialMain

end


section

open Filter MeasureTheory Metric
open scoped ENNReal FourierTransform SchwartzMap Topology

namespace PackingBounds.PackingBridge

private theorem volume_half_ball {d : ℕ} (hd : 0 < d) :
    volume (ball (0 : CohnElkies.Euclidean d) (1 / 2 : ℝ)) =
      ENNReal.ofReal (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, CohnElkies.sqrt_pi_pow_eq_rpow]
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [one_div, inv_pow, CohnElkies.unitBallVolume]
  ring

private theorem sphere_packing_le_admissible
    {d : ℕ} (hd : 0 < d) (f : CohnElkies.Admissible d) :
    SpherePackingConstant d ≤
      ENNReal.ofReal
        (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d * CohnElkies.quotient f) := by
  have hfne : f.function ≠ 0 := by
    intro hf
    have h := f.fourier_zero_pos
    rw [hf] at h
    simp only [FourierTransform.fourier_zero, zero_apply, Complex.zero_re, lt_self_iff_false] at h
  have hreal : ∀ x : CohnElkies.Euclidean d,
      ((f.function x).re : ℂ) = f.function x := by
    intro x
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im, f.real x]
  have hfourier : ∀ x : CohnElkies.Euclidean d,
      (((𝓕 f.function : CohnElkies.TestFunction d) x).re : ℂ) =
        (𝓕 f.function : CohnElkies.TestFunction d) x := by
    intro x
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im, f.fourier_real x]
  have h := LinearProgrammingBound hfne hreal hfourier
    (fun x hx => f.outside_nonpos x hx) f.fourier_nonneg hd
  rw [volume_half_ball hd] at h
  have horigin : 0 ≤ (f.function (0 : CohnElkies.Euclidean d)).re :=
    (CohnElkies.admissible_zero_pos f).le
  have hratio :
      ((f.function (0 : CohnElkies.Euclidean d)).re.toNNReal : ENNReal) /
          (((𝓕 f.function : CohnElkies.TestFunction d)
            (0 : CohnElkies.Euclidean d)).re.toNNReal : ENNReal) =
        ENNReal.ofReal (CohnElkies.quotient f) := by
    rw [← ENNReal.coe_div (Real.toNNReal_pos.mpr f.fourier_zero_pos).ne']
    simp only [CohnElkies.quotient, ENNReal.ofReal,
      Real.toNNReal_div horigin]
  change SpherePackingConstant d ≤
    ((f.function (0 : CohnElkies.Euclidean d)).re.toNNReal : ENNReal) /
      (((𝓕 f.function : CohnElkies.TestFunction d)
        (0 : CohnElkies.Euclidean d)).re.toNNReal : ENNReal) *
      ENNReal.ofReal (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d) at h
  rw [hratio] at h
  calc
    SpherePackingConstant d ≤
        ENNReal.ofReal (CohnElkies.quotient f) *
          ENNReal.ofReal (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d) := h
    _ = ENNReal.ofReal
        (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d * CohnElkies.quotient f) := by
          rw [ENNReal.ofReal_mul (CohnElkies.geometricFactor_pos d).le]
          exact mul_comm _ _

private theorem sphere_packing_le_radial_linear_program
    {d : ℕ} (hd : 0 < d) :
    (SpherePackingConstant d).toReal ≤ CohnElkies.linearProgram d := by
  have hfactor := CohnElkies.geometricFactor_pos d
  have hbound :
      (SpherePackingConstant d).toReal /
          (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d) ≤
        sInf (CohnElkies.quotientSet d) := by
    apply le_csInf (CohnElkies.quotientSet_nonempty d)
    rintro _ ⟨f, rfl⟩
    apply (div_le_iff₀ hfactor).2
    have hcost : 0 ≤
        CohnElkies.unitBallVolume d / (2 : ℝ) ^ d * CohnElkies.quotient f :=
      mul_nonneg hfactor.le (CohnElkies.quotient_pos f).le
    have h := ENNReal.toReal_le_of_le_ofReal hcost
      (sphere_packing_le_admissible hd f)
    simpa only [ge_iff_le, mul_comm] using! h
  unfold CohnElkies.linearProgram
  simpa only [mul_comm, ge_iff_le] using! (div_le_iff₀ hfactor).1 hbound

private theorem sphere_packing_le_radial_linear_program_ennreal
    {d : ℕ} (hd : 0 < d) :
    SpherePackingConstant d ≤ ENNReal.ofReal (CohnElkies.linearProgram d) := by
  have hfinite : SpherePackingConstant d ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    unfold SpherePackingConstant
    exact iSup_le fun P => SpherePacking.upper_packing_density_le_one P
  exact (ENNReal.le_ofReal_iff_toReal_le hfinite
    (CohnElkies.linearProgram_nonneg d)).2
      (sphere_packing_le_radial_linear_program hd)

public
theorem sphere_packing_sharp_asymptotic_upper :
    ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO atTop e (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ d : ℕ, 0 < d →
        SpherePackingConstant d ≤
          ENNReal.ofReal
            ((Real.sqrt (Real.exp 1 / (2 * Real.pi)) + e d) ^ d) := by
  obtain ⟨e, he, hformula⟩ := CohnElkies.exists_manuscriptPackingIsLittleO
  refine ⟨e, he, fun d hd => ?_⟩
  change SpherePackingConstant d ≤
    ENNReal.ofReal ((CohnElkies.criticalPackingBase + e d) ^ d)
  rw [← hformula d hd]
  exact sphere_packing_le_radial_linear_program_ennreal hd

end PackingBounds.PackingBridge

end

section


section

open Filter MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap Topology

namespace PackingBounds

/-- An unrestricted Cohn--Elkies auxiliary function in dimension `d`. -/
public
structure FullAdmissible (d : ℕ) where
  /-- The Schwartz auxiliary function. -/
  function : CohnElkies.TestFunction d
  /-- The auxiliary function is real-valued. -/
  real : ∀ x : CohnElkies.Euclidean d, (function x).im = 0
  /-- Its Fourier transform is real-valued. -/
  fourier_real :
    ∀ x : CohnElkies.Euclidean d, ((𝓕 function) x).im = 0
  /-- Its Fourier transform is nonnegative. -/
  fourier_nonneg :
    ∀ x : CohnElkies.Euclidean d, 0 ≤ ((𝓕 function) x).re
  /-- Its Fourier transform is positive at the origin. -/
  fourier_zero_pos :
    0 < ((𝓕 function) (0 : CohnElkies.Euclidean d)).re
  /-- The auxiliary function is nonpositive outside the unit ball. -/
  outside_nonpos :
    ∀ x : CohnElkies.Euclidean d, 1 ≤ ‖x‖ → (function x).re ≤ 0

/-- The Cohn--Elkies quotient of an unrestricted admissible function. -/
public
noncomputable def fullQuotient {d : ℕ} (f : FullAdmissible d) : ℝ :=
  (f.function (0 : CohnElkies.Euclidean d)).re /
    ((𝓕 f.function) (0 : CohnElkies.Euclidean d)).re

private noncomputable def fullQuotientSet (d : ℕ) : Set ℝ :=
  Set.range (fullQuotient (d := d))

/-- The unrestricted Cohn--Elkies linear program in dimension `d`. -/
public
noncomputable def fullLinearProgram (d : ℕ) : ℝ :=
  CohnElkies.unitBallVolume d / (2 : ℝ) ^ d *
    sInf (fullQuotientSet d)

private noncomputable def radialToFull {d : ℕ}
    (f : CohnElkies.Admissible d) : FullAdmissible d where
  function := f.function
  real := f.real
  fourier_real := f.fourier_real
  fourier_nonneg := f.fourier_nonneg
  fourier_zero_pos := f.fourier_zero_pos
  outside_nonpos := f.outside_nonpos

private theorem fullQuotient_radialToFull {d : ℕ}
    (f : CohnElkies.Admissible d) :
    fullQuotient (radialToFull f) = CohnElkies.quotient f := by
  rfl

private theorem fullQuotientSet_eq_radial_iff (d : ℕ) :
    fullQuotientSet d = CohnElkies.quotientSet d ↔
      ∀ f : FullAdmissible d,
        ∃ g : CohnElkies.Admissible d,
          CohnElkies.quotient g = fullQuotient f := by
  constructor
  · intro h f
    have hf : fullQuotient f ∈ fullQuotientSet d := ⟨f, rfl⟩
    rw [h] at hf
    exact hf
  · intro h
    apply Set.Subset.antisymm
    · rintro _ ⟨f, rfl⟩
      exact h f
    · rintro _ ⟨f, rfl⟩
      exact ⟨radialToFull f, fullQuotient_radialToFull f⟩

end PackingBounds

end

end

section

open scoped FourierTransform Real Topology

namespace SpherePacking.Alternative

private noncomputable abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

private noncomputable abbrev Schwartz (d : ℕ) := SchwartzMap (Ambient d) ℂ

private noncomputable def IsRealValued {d : ℕ} (f : Schwartz d) : Prop :=
  ∀ x, (f x).im = 0

private noncomputable def IsRadial {d : ℕ} (f : Schwartz d) : Prop :=
  ∀ x y : Ambient d, ‖x‖ = ‖y‖ → f x = f y

private noncomputable def fourierReal {d : ℕ} (f : Schwartz d) (x : Ambient d) : ℝ :=
  ((𝓕 f : Schwartz d) x).re

private structure IsAdmissible {d : ℕ} (f : Schwartz d) : Prop where
  real_valued : IsRealValued f
  radial : IsRadial f
  fourier_real_valued : IsRealValued (𝓕 f : Schwartz d)
  fourier_zero_pos : 0 < fourierReal f 0
  fourier_nonneg : ∀ x, 0 ≤ fourierReal f x
  eventually_nonpos : ∀ x : Ambient d, 1 ≤ ‖x‖ → (f x).re ≤ 0

private noncomputable def quotient {d : ℕ} (f : Schwartz d) : ℝ :=
  (f 0).re / fourierReal f 0

end SpherePacking.Alternative

end

section

open Set Matrix MeasureTheory

namespace SpherePacking.Alternative

private noncomputable abbrev OrthogonalGroup (d : ℕ) := Matrix.orthogonalGroup (Fin d) ℝ

private theorem orthogonal_entry_abs_le_one {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin d) ℝ) (i j : Fin d) :
    |A i j| ≤ (1 : ℝ) := by
  have hdiag := congrArg (fun B : Matrix (Fin d) (Fin d) ℝ => B i i)
    ((Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).mp hA)
  have hsum : (∑ k : Fin d, A i k * A i k) = (1 : ℝ) := by
    simpa only [Matrix.mul_apply, transpose_apply, one_apply_eq] using hdiag
  have hterm : A i j * A i j ≤ ∑ k : Fin d, A i k * A i k := by
    exact Finset.single_le_sum (fun k _ => mul_self_nonneg (A i k))
      (Finset.mem_univ j)
  exact (abs_le_one_iff_mul_self_le_one).2 (hterm.trans_eq hsum)

private theorem orthogonal_isCompact (d : ℕ) :
    IsCompact (Matrix.orthogonalGroup (Fin d) ℝ :
      Set (Matrix (Fin d) (Fin d) ℝ)) := by
  refine ((isCompact_Icc (a := (-1 : ℝ)) (b := (1 : ℝ))).matrix).of_isClosed_subset
    isClosed_unitary ?_
  intro A hA
  change ∀ i j, A i j ∈ Set.Icc (-1 : ℝ) 1
  intro i j
  exact abs_le.mp (orthogonal_entry_abs_le_one hA i j)

private noncomputable instance orthogonalGroupCompactSpace (d : ℕ) :
    CompactSpace (OrthogonalGroup d) :=
  isCompact_iff_compactSpace.mp (orthogonal_isCompact d)

private noncomputable instance orthogonalGroupMeasurableSpace (d : ℕ) :
    MeasurableSpace (OrthogonalGroup d) :=
  borel (OrthogonalGroup d)

private noncomputable instance orthogonalGroupBorelSpace (d : ℕ) :
    BorelSpace (OrthogonalGroup d) :=
  ⟨rfl⟩

private noncomputable def orthogonalAction {d : ℕ} (U : OrthogonalGroup d) (x : Ambient d) :
  Ambient d :=
  Matrix.toLpLin 2 2 (U : Matrix (Fin d) (Fin d) ℝ) x

@[simp] private theorem orthogonalAction_one {d : ℕ} (x : Ambient d) :
    orthogonalAction (1 : OrthogonalGroup d) x = x := by
  change Matrix.toLpLin 2 2 (1 : Matrix (Fin d) (Fin d) ℝ) x = x
  rw [Matrix.toLpLin_one]
  rfl

@[simp] private theorem orthogonalAction_mul {d : ℕ}
    (U V : OrthogonalGroup d) (x : Ambient d) :
    orthogonalAction (U * V) x = orthogonalAction U (orthogonalAction V x) := by
  change Matrix.toLpLin 2 2
    ((U : Matrix (Fin d) (Fin d) ℝ) * (V : Matrix (Fin d) (Fin d) ℝ)) x =
      Matrix.toLpLin 2 2 (U : Matrix (Fin d) (Fin d) ℝ)
        (Matrix.toLpLin 2 2 (V : Matrix (Fin d) (Fin d) ℝ) x)
  rw [Matrix.toLpLin_mul_same]
  rfl

@[simp] private theorem orthogonalAction_zero {d : ℕ} (U : OrthogonalGroup d) :
    orthogonalAction U (0 : Ambient d) = 0 := by
  exact map_zero (Matrix.toLpLin 2 2 (U : Matrix (Fin d) (Fin d) ℝ))

private noncomputable def orthogonalIsometryEquiv (d : ℕ) :
    OrthogonalGroup d ≃* (Ambient d ≃ₗᵢ[ℝ] Ambient d) :=
  (Unitary.mapEquiv (StarMulEquiv.ofClass
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)))).toMulEquiv.trans
      Unitary.linearIsometryEquiv

private noncomputable def orthogonalLinearIsometry {d : ℕ} (U : OrthogonalGroup d) :
    Ambient d ≃ₗᵢ[ℝ] Ambient d :=
  orthogonalIsometryEquiv d U

@[simp] private theorem orthogonalLinearIsometry_apply {d : ℕ}
    (U : OrthogonalGroup d) (x : Ambient d) :
    orthogonalLinearIsometry U x = orthogonalAction U x := by
  rfl

private theorem orthogonalAction_continuous {d : ℕ} (x : Ambient d) :
    Continuous (fun U : OrthogonalGroup d => orthogonalAction U x) := by
  change Continuous (fun U : OrthogonalGroup d =>
    WithLp.toLp 2 ((U : Matrix (Fin d) (Fin d) ℝ) *ᵥ WithLp.ofLp x))
  exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp
    (continuous_subtype_val.matrix_mulVec continuous_const)

private theorem continuous_orthogonalAction_apply {d : ℕ} (x : Ambient d) :
    Continuous (fun U : OrthogonalGroup d => orthogonalAction U x) :=
  orthogonalAction_continuous x

private theorem orthogonalAction_joint_continuous (d : ℕ) :
    Continuous (fun p : OrthogonalGroup d × Ambient d =>
      orthogonalAction p.1 p.2) := by
  change Continuous (fun p : OrthogonalGroup d × Ambient d =>
    WithLp.toLp 2
      (((p.1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ WithLp.ofLp p.2)))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
    ((continuous_subtype_val.comp continuous_fst).matrix_mulVec
      ((PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).comp continuous_snd))

private noncomputable def orthogonalMatrixOfIsometry {d : ℕ}
    (A : Ambient d ≃ₗᵢ[ℝ] Ambient d) : OrthogonalGroup d :=
  ⟨A.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis,
    A.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin d) ℝ)
      (EuclideanSpace.basisFun (Fin d) ℝ)⟩

@[simp] private theorem orthogonalMatrixOfIsometry_action {d : ℕ}
    (A : Ambient d ≃ₗᵢ[ℝ] Ambient d) (x : Ambient d) :
    orthogonalAction (orthogonalMatrixOfIsometry A) x = A x := by
  change (Matrix.toLpLin 2 2)
    ((LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
      A.toLinearEquiv.toLinearMap) x = A x
  rw [Matrix.toLpLin_eq_toLin]
  change (Matrix.toLin (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
      ((LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
        A.toLinearEquiv.toLinearMap) x = A x
  rw [Matrix.toLin_toMatrix]
  rfl

private theorem orthogonal_transitive {d : ℕ} {x y : Ambient d}
    (hxy : ‖x‖ = ‖y‖) :
    ∃ U : OrthogonalGroup d, orthogonalAction U x = y := by
  let A : Ambient d ≃ₗᵢ[ℝ] Ambient d :=
    Submodule.reflection (ℝ ∙ (x - y))ᗮ
  refine ⟨orthogonalMatrixOfIsometry A, ?_⟩
  rw [orthogonalMatrixOfIsometry_action]
  exact Submodule.reflection_sub hxy

private noncomputable def orthogonalPositiveCompacts (d : ℕ) :
    TopologicalSpace.PositiveCompacts (OrthogonalGroup d) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp only [interior_univ, univ_nonempty]⟩

private noncomputable def radialOrthogonalHaar (d : ℕ) : Measure (OrthogonalGroup d) :=
  Measure.haarMeasure (orthogonalPositiveCompacts d)

private theorem radialOrthogonalHaar_univ (d : ℕ) :
    radialOrthogonalHaar d Set.univ = 1 := by
  simpa only [radialOrthogonalHaar, orthogonalPositiveCompacts,
    TopologicalSpace.PositiveCompacts.coe_mk,
    TopologicalSpace.Compacts.coe_mk] using
    (Measure.haarMeasure_self (K₀ := orthogonalPositiveCompacts d))

private noncomputable instance radialOrthogonalHaar_probability (d : ℕ) :
    IsProbabilityMeasure (radialOrthogonalHaar d) :=
  ⟨radialOrthogonalHaar_univ d⟩

private noncomputable instance radialOrthogonalHaar_isHaar (d : ℕ) :
    (radialOrthogonalHaar d).IsHaarMeasure := by
  unfold radialOrthogonalHaar
  infer_instance

private noncomputable instance radialOrthogonalHaar_leftInvariant (d : ℕ) :
    (radialOrthogonalHaar d).IsMulLeftInvariant := by
  unfold radialOrthogonalHaar
  infer_instance

private noncomputable instance radialOrthogonalHaar_finite (d : ℕ) :
    IsFiniteMeasure (radialOrthogonalHaar d) := by
  infer_instance

end SpherePacking.Alternative

end

section

open Filter MeasureTheory
open scoped ContDiff Topology

namespace SpherePacking.Alternative

private noncomputable def radialIsometrySchwartzOrbit {d : ℕ}
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Schwartz d) : Schwartz d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    U.toContinuousLinearEquiv f

@[simp]
private theorem radialIsometrySchwartzOrbit_apply {d : ℕ}
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Schwartz d)
    (x : Ambient d) :
    radialIsometrySchwartzOrbit U f x = f (U x) := by
  rfl

@[simp]
private theorem radialIsometrySchwartzOrbit_symm_apply {d : ℕ}
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Schwartz d) :
    radialIsometrySchwartzOrbit U.symm
      (radialIsometrySchwartzOrbit U f) = f := by
  ext x
  simp only [radialIsometrySchwartzOrbit_apply, LinearIsometryEquiv.apply_symm_apply]

private theorem radialIsometrySchwartzOrbit_iteratedFDeriv_norm {d : ℕ}
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Schwartz d)
    (n : ℕ) (x : Ambient d) :
    ‖iteratedFDeriv ℝ n
        (radialIsometrySchwartzOrbit U f : Ambient d → ℂ) x‖ =
      ‖iteratedFDeriv ℝ n (f : Ambient d → ℂ) (U x)‖ := by
  change
    ‖iteratedFDeriv ℝ n
      ((f : Ambient d → ℂ) ∘ (U : Ambient d → Ambient d)) x‖ = _
  exact U.norm_iteratedFDeriv_comp_right (f : Ambient d → ℂ) x n

private theorem radialIsometrySchwartzOrbit_iteratedFDeriv {d : ℕ}
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Schwartz d)
    (n : ℕ) (x : Ambient d) :
    iteratedFDeriv ℝ n
        (radialIsometrySchwartzOrbit U f : Ambient d → ℂ) x =
      (iteratedFDeriv ℝ n (f : Ambient d → ℂ) (U x)).compContinuousLinearMap
        (fun _ ↦ U.toContinuousLinearMap) := by
  change
    iteratedFDeriv ℝ n
        ((f : Ambient d → ℂ) ∘ (U : Ambient d → Ambient d)) x = _
  exact U.toContinuousLinearMap.iteratedFDeriv_comp_right
    (f.smooth ⊤) x (mod_cast le_top)

private theorem radialIsometrySchwartzOrbit_weighted_iteratedFDeriv_le
    {d : ℕ} (U : Ambient d ≃ₗᵢ[ℝ] Ambient d)
    (f : Schwartz d) (k n : ℕ) (x : Ambient d) :
    ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (radialIsometrySchwartzOrbit U f : Ambient d → ℂ) x‖ ≤
      SchwartzMap.seminorm ℂ k n f := by
  rw [radialIsometrySchwartzOrbit_iteratedFDeriv_norm,
    ← U.norm_map x]
  exact SchwartzMap.le_seminorm ℂ k n f (U x)

private theorem radialIsometrySchwartzOrbit_seminorm_le {d : ℕ}
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Schwartz d)
    (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (radialIsometrySchwartzOrbit U f) ≤
      SchwartzMap.seminorm ℂ k n f := by
  apply SchwartzMap.seminorm_le_bound ℂ k n
    (radialIsometrySchwartzOrbit U f)
    (apply_nonneg (SchwartzMap.seminorm ℂ k n) f)
  exact radialIsometrySchwartzOrbit_weighted_iteratedFDeriv_le U f k n

private theorem radialIsometrySchwartzOrbit_seminorm_eq {d : ℕ}
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Schwartz d)
    (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (radialIsometrySchwartzOrbit U f) =
      SchwartzMap.seminorm ℂ k n f := by
  apply le_antisymm (radialIsometrySchwartzOrbit_seminorm_le U f k n)
  have h := radialIsometrySchwartzOrbit_seminorm_le U.symm
    (radialIsometrySchwartzOrbit U f) k n
  simpa only [ge_iff_le, radialIsometrySchwartzOrbit_symm_apply] using h

end SpherePacking.Alternative

end

section

open Filter MeasureTheory Set
open scoped ContDiff Real Topology

namespace SpherePacking.Alternative

private theorem orthogonalLinearIsometry_continuousLinearMap_continuous
    (d : ℕ) :
    Continuous (fun U : OrthogonalGroup d =>
      (orthogonalLinearIsometry U).toContinuousLinearMap) := by
  change Continuous (fun U : OrthogonalGroup d =>
    Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)
      (U : Matrix (Fin d) (Fin d) ℝ))
  exact
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap
      |>.continuous_of_finiteDimensional
      |>.comp continuous_subtype_val

private theorem orthogonalSchwartzIteratedFDeriv_continuous
    {d : ℕ} (f : Schwartz d) (n : ℕ) (x : Ambient d) :
    Continuous (fun U : OrthogonalGroup d =>
      iteratedFDeriv ℝ n
        (radialIsometrySchwartzOrbit
          (orthogonalLinearIsometry U) f : Ambient d → ℂ) x) := by
  have hderiv :
      Continuous (fun U : OrthogonalGroup d =>
        iteratedFDeriv ℝ n (f : Ambient d → ℂ)
          (orthogonalAction U x)) :=
    ((f.smooth ⊤).continuous_iteratedFDeriv
      (mod_cast le_top)).comp (orthogonalAction_continuous x)
  have hmaps :
      Continuous (fun U : OrthogonalGroup d =>
        fun _ : Fin n =>
          (orthogonalLinearIsometry U).toContinuousLinearMap) :=
    continuous_pi fun _ =>
      orthogonalLinearIsometry_continuousLinearMap_continuous d
  have hcomp :
      Continuous
        (fun p :
          ContinuousMultilinearMap ℝ
              (fun _ : Fin n => Ambient d) ℂ ×
            (Fin n → Ambient d →L[ℝ] Ambient d) =>
          p.1.compContinuousLinearMap p.2) := by
    exact continuous_iff_continuousAt.2 fun p =>
      (ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
        p).continuousAt
  have h := hcomp.comp (hderiv.prodMk hmaps)
  simpa only [radialIsometrySchwartzOrbit_iteratedFDeriv, orthogonalLinearIsometry_apply,
    Function.comp_def] using h

private theorem orthogonalSchwartzInverseIteratedFDeriv_continuous
    {d : ℕ} (f : Schwartz d) (n : ℕ) (x : Ambient d) :
    Continuous (fun U : OrthogonalGroup d =>
      iteratedFDeriv ℝ n
        (radialIsometrySchwartzOrbit
          (orthogonalLinearIsometry U⁻¹) f : Ambient d → ℂ) x) :=
  (orthogonalSchwartzIteratedFDeriv_continuous f n x).comp continuous_inv

private theorem orthogonalSchwartzInverseIteratedFDeriv_aestronglyMeasurable
    {d : ℕ} (f : Schwartz d) (n : ℕ) (x : Ambient d) :
    AEStronglyMeasurable
      (fun U : OrthogonalGroup d =>
        iteratedFDeriv ℝ n
          (radialIsometrySchwartzOrbit
            (orthogonalLinearIsometry U⁻¹) f : Ambient d → ℂ) x)
      (radialOrthogonalHaar d) :=
  (orthogonalSchwartzInverseIteratedFDeriv_continuous
    f n x).aestronglyMeasurable_of_compactSpace

end SpherePacking.Alternative

namespace SpherePacking.Alternative

section ProbabilityAverage

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α) [IsProbabilityMeasure μ]
variable {d : ℕ} (g : α → Schwartz d) (C : ℕ → ℕ → ℝ)

private theorem radialSchwartzParametricDerivativeIntegrable
    (hmeas : ∀ (n : ℕ) (x : Ambient d),
      AEStronglyMeasurable
        (fun a : α ↦ iteratedFDeriv ℝ n
          (g a : Ambient d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ),
      SchwartzMap.seminorm ℂ k n (g a) ≤ C k n)
    (n : ℕ) (x : Ambient d) :
    Integrable
      (fun a : α ↦ iteratedFDeriv ℝ n
        (g a : Ambient d → ℂ) x) μ := by
  apply Integrable.of_bound (hmeas n x) (C 0 n)
  filter_upwards [] with a
  exact
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (g a) n x).trans
      (hbound a 0 n)

private theorem radialSchwartzParametric_hasFDerivAt_iteratedIntegral
    (hmeas : ∀ (n : ℕ) (x : Ambient d),
      AEStronglyMeasurable
        (fun a : α ↦ iteratedFDeriv ℝ n
          (g a : Ambient d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ),
      SchwartzMap.seminorm ℂ k n (g a) ≤ C k n)
    (n : ℕ) (x : Ambient d) :
    HasFDerivAt
      (fun y : Ambient d ↦
        ∫ a : α, iteratedFDeriv ℝ n
          (g a : Ambient d → ℂ) y ∂μ)
      (∫ a : α, fderiv ℝ
        (iteratedFDeriv ℝ n (g a : Ambient d → ℂ)) x ∂μ)
      x := by
  have hderiv_meas :
      AEStronglyMeasurable
        (fun a : α ↦
          fderiv ℝ
            (iteratedFDeriv ℝ n (g a : Ambient d → ℂ)) x) μ := by
    have h :=
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) ↦ Ambient d) ℂ).continuous.comp_aestronglyMeasurable
          (hmeas (n + 1) x)
    simpa only [fderiv_iteratedFDeriv, Function.comp_apply] using h
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ)
    (F := fun y : Ambient d ↦ fun a : α ↦
      iteratedFDeriv ℝ n (g a : Ambient d → ℂ) y)
    (F' := fun y : Ambient d ↦ fun a : α ↦
      fderiv ℝ (iteratedFDeriv ℝ n (g a : Ambient d → ℂ)) y)
    (bound := fun _ : α ↦ C 0 (n + 1))
    (s := Set.univ)
    Filter.univ_mem
    (Filter.Eventually.of_forall (fun y ↦ hmeas n y))
    (radialSchwartzParametricDerivativeIntegrable μ g C
      hmeas hbound n x)
    hderiv_meas
    (by
      filter_upwards [] with a y _
      calc
        ‖fderiv ℝ
          (iteratedFDeriv ℝ n (g a : Ambient d → ℂ)) y‖ =
          ‖iteratedFDeriv ℝ (n + 1)
            (g a : Ambient d → ℂ) y‖ :=
            norm_fderiv_iteratedFDeriv
        _ ≤ SchwartzMap.seminorm ℂ 0 (n + 1) (g a) :=
          SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ
            (g a) (n + 1) y
        _ ≤ C 0 (n + 1) := hbound a 0 (n + 1))
    (integrable_const (C 0 (n + 1)))
  filter_upwards [] with a y _
  exact
    (((g a).smooth ⊤).differentiable_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop
        (le_refl _) n)).differentiableAt.hasFDerivAt

private theorem radialSchwartzParametric_iteratedFDeriv_integral
    (hmeas : ∀ (n : ℕ) (x : Ambient d),
      AEStronglyMeasurable
        (fun a : α ↦ iteratedFDeriv ℝ n
          (g a : Ambient d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ),
      SchwartzMap.seminorm ℂ k n (g a) ≤ C k n)
    (n : ℕ) (x : Ambient d) :
    iteratedFDeriv ℝ n
        (fun y : Ambient d ↦ ∫ a : α, (g a) y ∂μ) x =
      ∫ a : α, iteratedFDeriv ℝ n
        (g a : Ambient d → ℂ) x ∂μ := by
  induction n generalizing x with
  | zero =>
      ext v
      rw [ContinuousMultilinearMap.integral_apply
        (radialSchwartzParametricDerivativeIntegrable μ g C
          hmeas hbound 0 x)]
      simp only [iteratedFDeriv_zero_apply]
  | succ n ih =>
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      have hprevious :
          iteratedFDeriv ℝ n
              (fun y : Ambient d ↦ ∫ a : α, (g a) y ∂μ) =
            fun y : Ambient d ↦
              ∫ a : α, iteratedFDeriv ℝ n
                (g a : Ambient d → ℂ) y ∂μ := by
        funext y
        exact ih y
      rw [hprevious,
        (radialSchwartzParametric_hasFDerivAt_iteratedIntegral
          μ g C hmeas hbound n x).fderiv]
      calc
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (n + 1) ↦ Ambient d) ℂ).symm
            (∫ a : α, fderiv ℝ
              (iteratedFDeriv ℝ n (g a : Ambient d → ℂ)) x ∂μ) =
            ∫ a : α,
              (continuousMultilinearCurryLeftEquiv ℝ
                (fun _ : Fin (n + 1) ↦ Ambient d) ℂ).symm
                  (fderiv ℝ
                    (iteratedFDeriv ℝ n (g a : Ambient d → ℂ)) x)
                  ∂μ := by
              exact
                (LinearIsometry.integral_comp_comm
                  (𝕜 := ℝ)
                  (LinearIsometryEquiv.toLinearIsometry
                    ((continuousMultilinearCurryLeftEquiv ℝ
                      (fun _ : Fin (n + 1) ↦ Ambient d) ℂ).symm))
                  (fun a : α ↦ fderiv ℝ
                    (iteratedFDeriv ℝ n
                      (g a : Ambient d → ℂ)) x)).symm
        _ = ∫ a : α, iteratedFDeriv ℝ (n + 1)
              (g a : Ambient d → ℂ) x ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with a
              rw [iteratedFDeriv_succ_eq_comp_left]
              rfl

end ProbabilityAverage

end SpherePacking.Alternative

end

section

open MeasureTheory
open scoped Topology

namespace SpherePacking.Alternative

private noncomputable def radialSymmetrizationAverage {d : ℕ}
    (f : Schwartz d) (x : Ambient d) : ℂ :=
  ∫ U : OrthogonalGroup d,
    f (orthogonalAction U⁻¹ x) ∂radialOrthogonalHaar d

private theorem radialSymmetrizationAverage_integrable {d : ℕ}
    (f : Schwartz d) (x : Ambient d) :
    Integrable (fun U : OrthogonalGroup d ↦
      f (orthogonalAction U⁻¹ x)) (radialOrthogonalHaar d) := by
  have hcontinuous : Continuous
      (fun U : OrthogonalGroup d ↦ f (orthogonalAction U⁻¹ x)) :=
    f.continuous.comp ((continuous_orthogonalAction_apply x).comp continuous_inv)
  simpa only [integrableOn_univ] using hcontinuous.continuousOn.integrableOn_compact isCompact_univ

private theorem radialSymmetrizationAverage_comp_orthogonal {d : ℕ}
    (f : Schwartz d) (A : OrthogonalGroup d) (x : Ambient d) :
    radialSymmetrizationAverage f (orthogonalAction A x) =
      radialSymmetrizationAverage f x := by
  unfold radialSymmetrizationAverage
  calc
    (∫ U : OrthogonalGroup d,
        f (orthogonalAction U⁻¹ (orthogonalAction A x))
          ∂radialOrthogonalHaar d) =
      ∫ U : OrthogonalGroup d,
        f (orthogonalAction (A * U)⁻¹ (orthogonalAction A x))
          ∂radialOrthogonalHaar d :=
      (integral_mul_left_eq_self
        (μ := radialOrthogonalHaar d)
        (fun U : OrthogonalGroup d ↦
          f (orthogonalAction U⁻¹ (orthogonalAction A x))) A).symm
    _ = ∫ U : OrthogonalGroup d,
        f (orthogonalAction U⁻¹ x) ∂radialOrthogonalHaar d := by
      apply integral_congr_ae
      filter_upwards with U
      simp only [mul_inv_rev, orthogonalAction_mul]
      rw [← orthogonalAction_mul A⁻¹ A x]
      simp only [inv_mul_cancel, orthogonalAction_one]

private theorem radialSymmetrizationAverage_eq_of_norm_eq {d : ℕ}
    (f : Schwartz d) {x y : Ambient d} (hxy : ‖x‖ = ‖y‖) :
    radialSymmetrizationAverage f x = radialSymmetrizationAverage f y := by
  obtain ⟨A, hA⟩ := orthogonal_transitive hxy
  rw [← hA]
  exact (radialSymmetrizationAverage_comp_orthogonal f A x).symm

@[simp] private theorem radialSymmetrizationAverage_zero {d : ℕ}
    (f : Schwartz d) :
    radialSymmetrizationAverage f 0 = f 0 := by
  simp only [radialSymmetrizationAverage, orthogonalAction_zero, integral_const, probReal_univ,
    one_smul]

end SpherePacking.Alternative

end

section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace SpherePacking.Alternative

private theorem scalarProbabilityAverage_weighted_iteratedFDeriv_le
    {ι : Type*} [MeasurableSpace ι]
    (μ : Measure ι) [IsProbabilityMeasure μ]
    {d : ℕ} (F : ι → Schwartz d) (C : ℕ → ℕ → ℝ)
    (hbound : ∀ (k n : ℕ) (a : ι) (x : Ambient d),
      ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (fun y : Ambient d ↦ F a y) x‖ ≤ C k n)
    (hderiv : ∀ (n : ℕ) (x : Ambient d),
      iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ ∫ a, F a y ∂μ) x =
        ∫ a, iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ F a y) x ∂μ)
    (k n : ℕ) (x : Ambient d) :
    ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ ∫ a, F a y ∂μ) x‖ ≤ C k n := by
  rw [hderiv n x]
  calc
    ‖x‖ ^ k *
        ‖∫ a, iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ F a y) x ∂μ‖
        ≤ ‖x‖ ^ k *
          ∫ a, ‖iteratedFDeriv ℝ n
            (fun y : Ambient d ↦ F a y) x‖ ∂μ :=
          mul_le_mul_of_nonneg_left
            (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ a, ‖x‖ ^ k *
          ‖iteratedFDeriv ℝ n
            (fun y : Ambient d ↦ F a y) x‖ ∂μ := by
          rw [integral_const_mul]
    _ ≤ ∫ _a : ι, C k n ∂μ := by
          apply integral_mono_of_nonneg
          · exact Eventually.of_forall (fun _ ↦ by positivity)
          · exact integrable_const _
          · exact Eventually.of_forall (fun a ↦ hbound k n a x)
    _ = C k n := by simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

private noncomputable def scalarProbabilitySchwartzAverage
    {ι : Type*} [MeasurableSpace ι]
    (μ : Measure ι) [IsProbabilityMeasure μ]
    {d : ℕ} (F : ι → Schwartz d) (C : ℕ → ℕ → ℝ)
    (hsmooth : ContDiff ℝ ∞
      (fun x : Ambient d ↦ ∫ a, F a x ∂μ))
    (hderiv : ∀ (n : ℕ) (x : Ambient d),
      iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ ∫ a, F a y ∂μ) x =
        ∫ a, iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ F a y) x ∂μ)
    (hbound : ∀ (k n : ℕ) (a : ι) (x : Ambient d),
      ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (fun y : Ambient d ↦ F a y) x‖ ≤ C k n) :
    Schwartz d where
  toFun x := ∫ a, F a x ∂μ
  smooth' := hsmooth
  decay' k n :=
    ⟨C k n,
      scalarProbabilityAverage_weighted_iteratedFDeriv_le
        μ F C hbound hderiv k n⟩

private noncomputable def radialSymmetrization {d : ℕ}
    (f : Schwartz d) : Schwartz d := by
  let F : OrthogonalGroup d → Schwartz d :=
    fun U ↦ radialIsometrySchwartzOrbit
      (orthogonalLinearIsometry U⁻¹) f
  let C : ℕ → ℕ → ℝ :=
    fun k n ↦ SchwartzMap.seminorm ℂ k n f
  have hmeas : ∀ (n : ℕ) (x : Ambient d),
      AEStronglyMeasurable
        (fun U : OrthogonalGroup d ↦ iteratedFDeriv ℝ n
          (F U : Ambient d → ℂ) x)
        (radialOrthogonalHaar d) := by
    intro n x
    exact orthogonalSchwartzInverseIteratedFDeriv_aestronglyMeasurable
      f n x
  have hseminorm : ∀ (U : OrthogonalGroup d) (k n : ℕ),
      SchwartzMap.seminorm ℂ k n (F U) ≤ C k n := by
    intro U k n
    exact (radialIsometrySchwartzOrbit_seminorm_eq
      (orthogonalLinearIsometry U⁻¹) f k n).le
  have hderiv : ∀ (n : ℕ) (x : Ambient d),
      iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ ∫ U, F U y ∂radialOrthogonalHaar d) x =
        ∫ U, iteratedFDeriv ℝ n
          (fun y : Ambient d ↦ F U y) x ∂radialOrthogonalHaar d := by
    intro n x
    exact radialSchwartzParametric_iteratedFDeriv_integral
      (radialOrthogonalHaar d) F C hmeas hseminorm n x
  have hsmooth : ContDiff ℝ ∞
      (fun x : Ambient d ↦ ∫ U, F U x ∂radialOrthogonalHaar d) := by
    refine contDiff_of_differentiable_iteratedFDeriv ?_
    intro n _
    have heq := funext (hderiv n)
    rw [heq]
    intro x
    exact (radialSchwartzParametric_hasFDerivAt_iteratedIntegral
      (radialOrthogonalHaar d) F C hmeas hseminorm n x).differentiableAt
  have hweighted : ∀ (k n : ℕ) (U : OrthogonalGroup d)
      (x : Ambient d),
      ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (fun y : Ambient d ↦ F U y) x‖ ≤ C k n := by
    intro k n U x
    exact radialIsometrySchwartzOrbit_weighted_iteratedFDeriv_le
      (orthogonalLinearIsometry U⁻¹) f k n x
  exact scalarProbabilitySchwartzAverage
    (radialOrthogonalHaar d) F C hsmooth hderiv hweighted

@[simp]
private theorem radialSymmetrization_apply {d : ℕ}
    (f : Schwartz d) (x : Ambient d) :
    radialSymmetrization f x = radialSymmetrizationAverage f x := by
  rfl

end SpherePacking.Alternative

end

section

open MeasureTheory
open scoped FourierTransform Topology

namespace SpherePacking.Alternative

private noncomputable def orthogonalScalarAverage
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    (μ : Measure G)
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    (f : Schwartz d) (x : Ambient d) : ℂ :=
  ∫ U : G, f (A U x) ∂μ

private theorem orthogonalScalarAverage_im_eq_zero
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    {μ : Measure G}
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    {f : Schwartz d} (hf : IsRealValued f)
    (x : Ambient d)
    (hint : Integrable (fun U : G ↦ f (A U x)) μ) :
    (orthogonalScalarAverage μ A f x).im = 0 := by
  unfold orthogonalScalarAverage
  calc
    (∫ U : G, f (A U x) ∂μ).im =
        ∫ U : G, (f (A U x)).im ∂μ := (integral_im hint).symm
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with U
      exact hf (A U x)

private theorem orthogonalScalarAverage_re
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    {μ : Measure G}
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    (f : Schwartz d) (x : Ambient d)
    (hint : Integrable (fun U : G ↦ f (A U x)) μ) :
    (orthogonalScalarAverage μ A f x).re =
      ∫ U : G, (f (A U x)).re ∂μ := by
  unfold orthogonalScalarAverage
  exact (integral_re hint).symm

private theorem orthogonalScalarAverage_nonneg_of_nonneg
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    {μ : Measure G}
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    {f : Schwartz d}
    (hf : ∀ y : Ambient d, 0 ≤ (f y).re)
    (x : Ambient d)
    (hint : Integrable (fun U : G ↦ f (A U x)) μ) :
    0 ≤ (orthogonalScalarAverage μ A f x).re := by
  rw [orthogonalScalarAverage_re A f x hint]
  exact integral_nonneg (fun U ↦ hf (A U x))

private theorem orthogonalScalarAverage_nonpos_of_norm_ge
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    {μ : Measure G}
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    {f : Schwartz d} {R : ℝ}
    (hf : ∀ y : Ambient d, R ≤ ‖y‖ → (f y).re ≤ 0)
    {x : Ambient d} (hx : R ≤ ‖x‖)
    (hint : Integrable (fun U : G ↦ f (A U x)) μ) :
    (orthogonalScalarAverage μ A f x).re ≤ 0 := by
  rw [orthogonalScalarAverage_re A f x hint]
  apply integral_nonpos
  intro U
  apply hf (A U x)
  simpa only [(A U).norm_map] using hx

private theorem radialSymmetrizationAverage_eq_orthogonalScalarAverage
    {d : ℕ} (f : Schwartz d) (x : Ambient d) :
    radialSymmetrizationAverage f x =
      orthogonalScalarAverage (radialOrthogonalHaar d)
        (fun U : OrthogonalGroup d ↦ orthogonalLinearIsometry U⁻¹) f x := by
  rfl

private theorem radialSymmetrizationAverage_im_eq_zero
    {d : ℕ} {f : Schwartz d} (hf : IsRealValued f)
    (x : Ambient d) :
    (radialSymmetrizationAverage f x).im = 0 := by
  rw [radialSymmetrizationAverage_eq_orthogonalScalarAverage]
  exact orthogonalScalarAverage_im_eq_zero
    (fun U : OrthogonalGroup d ↦ orthogonalLinearIsometry U⁻¹)
    hf x (radialSymmetrizationAverage_integrable f x)

private theorem radialSymmetrizationAverage_nonneg_of_nonneg
    {d : ℕ} {f : Schwartz d}
    (hf : ∀ y : Ambient d, 0 ≤ (f y).re)
    (x : Ambient d) :
    0 ≤ (radialSymmetrizationAverage f x).re := by
  rw [radialSymmetrizationAverage_eq_orthogonalScalarAverage]
  exact orthogonalScalarAverage_nonneg_of_nonneg
    (fun U : OrthogonalGroup d ↦ orthogonalLinearIsometry U⁻¹)
    hf x (radialSymmetrizationAverage_integrable f x)

private theorem radialSymmetrizationAverage_nonpos_of_norm_ge
    {d : ℕ} {f : Schwartz d} {R : ℝ}
    (hf : ∀ y : Ambient d, R ≤ ‖y‖ → (f y).re ≤ 0)
    {x : Ambient d} (hx : R ≤ ‖x‖) :
    (radialSymmetrizationAverage f x).re ≤ 0 := by
  rw [radialSymmetrizationAverage_eq_orthogonalScalarAverage]
  exact orthogonalScalarAverage_nonpos_of_norm_ge
    (fun U : OrthogonalGroup d ↦ orthogonalLinearIsometry U⁻¹)
    hf hx (radialSymmetrizationAverage_integrable f x)

private theorem radialSymmetrizationAverage_nonpos_of_one_le_norm
    {d : ℕ} {f : Schwartz d}
    (hf : ∀ y : Ambient d, 1 ≤ ‖y‖ → (f y).re ≤ 0)
    {x : Ambient d} (hx : 1 ≤ ‖x‖) :
    (radialSymmetrizationAverage f x).re ≤ 0 :=
  radialSymmetrizationAverage_nonpos_of_norm_ge hf hx

end SpherePacking.Alternative

end

section

open MeasureTheory
open scoped FourierTransform Real Topology

namespace SpherePacking.Alternative

private theorem IsRadial.neg_apply {d : ℕ} {f : Schwartz d}
    (hf : IsRadial f) (x : Ambient d) : f (-x) = f x := by
  exact hf (-x) x (norm_neg x)

private theorem IsRealValued.fourier_conj {d : ℕ} {f : Schwartz d}
    (hf : IsRealValued f) (x : Ambient d) :
    (starRingEnd ℂ) ((𝓕 f : Schwartz d) x) =
      (𝓕 f : Schwartz d) (-x) := by
  change (starRingEnd ℂ) (𝓕 (f : Ambient d → ℂ) x) =
    𝓕 (f : Ambient d → ℂ) (-x)
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  apply integral_congr_ae
  filter_upwards with y
  have hy : (starRingEnd ℂ) (f y) = f y :=
    Complex.conj_eq_iff_im.mpr (hf y)
  simp only [neg_mul, real_inner_comm, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
    smul_eq_mul, map_mul, ← Complex.exp_conj, map_neg, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I, mul_neg, neg_neg,
    hy, inner_neg_right]

private theorem IsRadial.fourier_realValued {d : ℕ} {f : Schwartz d}
    (hradial : IsRadial f) (hreal : IsRealValued f) :
    IsRealValued (𝓕 f : Schwartz d) := by
  intro x
  apply Complex.conj_eq_iff_im.mp
  rw [hreal.fourier_conj x]
  change 𝓕 (f : Ambient d → ℂ) (-x) = 𝓕 (f : Ambient d → ℂ) x
  rw [Real.fourier_eq', Real.fourier_eq']
  have hneg :
      (fun y : Ambient d ↦
        Complex.exp ((↑(-2 * Real.pi * @inner ℝ _ _ y (-x)) : ℂ) * Complex.I) * f y) =
        (fun y : Ambient d ↦
          Complex.exp ((↑(-2 * Real.pi * @inner ℝ _ _ (-y) x) : ℂ) * Complex.I) *
            f (-y)) := by
    funext y
    rw [hradial.neg_apply y]
    congr 2
    simp only [neg_mul, inner_neg_right, mul_neg, neg_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
      inner_neg_left]
  simp only [smul_eq_mul]
  rw [hneg]
  exact (LinearIsometryEquiv.neg ℝ (E := Ambient d)).measurePreserving.integral_comp
    (LinearIsometryEquiv.neg ℝ (E := Ambient d)).toHomeomorph.measurableEmbedding
    (fun y : Ambient d ↦
      Complex.exp ((↑(-2 * Real.pi * @inner ℝ _ _ y x) : ℂ) * Complex.I) * f y)

end SpherePacking.Alternative

end

section

open Filter MeasureTheory
open scoped FourierTransform Real Topology

namespace SpherePacking.Alternative

private noncomputable def radialFourierCharacter {d : ℕ}
    (ξ x : Ambient d) : ℂ :=
  Complex.exp
    (((-2 * Real.pi * @inner ℝ _ _ x ξ : ℝ) : ℂ) * Complex.I)

private theorem radialFourierCharacter_continuous {d : ℕ} (ξ : Ambient d) :
    Continuous (radialFourierCharacter ξ) := by
  unfold radialFourierCharacter
  fun_prop

private theorem radialFourierCharacter_norm {d : ℕ}
    (ξ x : Ambient d) :
    ‖radialFourierCharacter ξ x‖ = 1 := by
  unfold radialFourierCharacter
  exact Complex.norm_exp_ofReal_mul_I _

private noncomputable def radialFourierOrbitAverage
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    (μ : Measure G)
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    (f : Schwartz d) (x : Ambient d) : ℂ :=
  ∫ g : G, f (A g x) ∂μ

private noncomputable def radialFourierOrbitKernel
    {d : ℕ} {G : Type*}
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    (f : Schwartz d) (ξ : Ambient d)
    (p : G × Ambient d) : ℂ :=
  radialFourierCharacter ξ p.2 * f (A p.1 p.2)

private theorem radialFourier_orthogonalOrbit_integrable
    {d : ℕ} (f : Schwartz d)
    (A : Ambient d ≃ₗᵢ[ℝ] Ambient d) :
    Integrable (fun x : Ambient d ↦ f (A x)) := by
  change Integrable ((f : Ambient d → ℂ) ∘ A)
  exact (A.measurePreserving.integrable_comp_emb
    A.toHomeomorph.measurableEmbedding).2 f.integrable

private theorem radialFourier_orthogonalCharacterOrbit_integrable
    {d : ℕ} (f : Schwartz d) (ξ : Ambient d)
    (A : Ambient d ≃ₗᵢ[ℝ] Ambient d) :
    Integrable
      (fun x : Ambient d ↦
        radialFourierCharacter ξ x * f (A x)) := by
  refine (radialFourier_orthogonalOrbit_integrable f A).bdd_mul
    (c := (1 : ℝ))
    (radialFourierCharacter_continuous ξ).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [radialFourierCharacter_norm]

private theorem radialFourier_orthogonalCharacterOrbit_integral_norm
    {d : ℕ} (f : Schwartz d) (ξ : Ambient d)
    (A : Ambient d ≃ₗᵢ[ℝ] Ambient d) :
    (∫ x : Ambient d,
      ‖radialFourierCharacter ξ x * f (A x)‖) =
      ∫ x : Ambient d, ‖f x‖ := by
  calc
    (∫ x : Ambient d,
      ‖radialFourierCharacter ξ x * f (A x)‖) =
        ∫ x : Ambient d, ‖f (A x)‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [norm_mul, radialFourierCharacter_norm, one_mul]
    _ = ∫ x : Ambient d, ‖f x‖ :=
      A.measurePreserving.integral_comp
        A.toHomeomorph.measurableEmbedding
        (fun x : Ambient d ↦ ‖f x‖)

private theorem radialFourier_orthogonalCharacterOrbit_integral
    {d : ℕ} (f : Schwartz d) (ξ : Ambient d)
    (A : Ambient d ≃ₗᵢ[ℝ] Ambient d) :
    (∫ x : Ambient d,
      radialFourierCharacter ξ x * f (A x)) =
      (𝓕 f : Schwartz d) (A ξ) := by
  rw [congrFun (SchwartzMap.fourier_coe f) (A ξ)]
  rw [← Real.fourier_comp_linearIsometry A
    (f : Ambient d → ℂ) ξ]
  rw [Real.fourier_eq']
  rfl

private theorem radialFourierOrbitKernel_integrable
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasure μ]
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    (f : Schwartz d) (ξ : Ambient d)
    (horbit :
      Measurable (fun p : G × Ambient d ↦ f (A p.1 p.2))) :
    Integrable (radialFourierOrbitKernel A f ξ)
      (μ.prod volume) := by
  have hcharacter :
      Measurable
        (fun p : G × Ambient d ↦
          radialFourierCharacter ξ p.2) :=
    (radialFourierCharacter_continuous ξ).measurable.comp
      measurable_snd
  have hmeas :
      AEStronglyMeasurable
        (radialFourierOrbitKernel A f ξ)
        (μ.prod volume) := by
    exact (hcharacter.mul horbit).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [] with g
    exact radialFourier_orthogonalCharacterOrbit_integrable
      f ξ (A g)
  · have hconstant :
        (fun g : G ↦
          ∫ x : Ambient d,
            ‖radialFourierOrbitKernel A f ξ (g, x)‖) =
          fun _ : G ↦ ∫ x : Ambient d, ‖f x‖ := by
      funext g
      exact radialFourier_orthogonalCharacterOrbit_integral_norm
        f ξ (A g)
    rw [hconstant]
    exact integrable_const _

private theorem radialFourierOrbitAverage_fourier
    {d : ℕ} {G : Type*} [MeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasure μ]
    (A : G → (Ambient d ≃ₗᵢ[ℝ] Ambient d))
    (f : Schwartz d) (ξ : Ambient d)
    (horbit :
      Measurable (fun p : G × Ambient d ↦ f (A p.1 p.2))) :
    (𝓕 (radialFourierOrbitAverage μ A f) : Ambient d → ℂ) ξ =
      ∫ g : G, (𝓕 f : Schwartz d) (A g ξ) ∂μ := by
  have hprod :=
    radialFourierOrbitKernel_integrable μ A f ξ horbit
  have hprod' :
      Integrable
        (Function.uncurry
          (fun g : G ↦ fun x : Ambient d ↦
            radialFourierCharacter ξ x * f (A g x)))
        (μ.prod volume) := hprod
  calc
    (𝓕 (radialFourierOrbitAverage μ A f) : Ambient d → ℂ) ξ =
        ∫ x : Ambient d,
          radialFourierCharacter ξ x *
            (∫ g : G, f (A g x) ∂μ) := by
      rw [Real.fourier_eq']
      rfl
    _ = ∫ x : Ambient d,
          ∫ g : G,
            radialFourierCharacter ξ x * f (A g x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [integral_const_mul]
    _ = ∫ g : G,
          (∫ x : Ambient d,
            radialFourierCharacter ξ x * f (A g x)) ∂μ := by
      exact (integral_integral_swap hprod').symm
    _ = ∫ g : G, (𝓕 f : Schwartz d) (A g ξ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      exact radialFourier_orthogonalCharacterOrbit_integral
        f ξ (A g)

private theorem radialOrthogonalHaarOrbit_measurable
    {d : ℕ} (f : Schwartz d) :
    Measurable
      (fun p : OrthogonalGroup d × Ambient d ↦
        f (orthogonalLinearIsometry (p.1⁻¹) p.2)) := by
  have hforward :
      Measurable
        (fun p : OrthogonalGroup d × Ambient d ↦
          f (orthogonalAction p.1 p.2)) :=
    (f.continuous.comp (orthogonalAction_joint_continuous d)).measurable
  have hinverse :
      Measurable
        (fun p : OrthogonalGroup d × Ambient d ↦
          (p.1⁻¹, p.2)) :=
    ((continuous_inv.comp continuous_fst).prodMk
      continuous_snd).measurable
  have hcomposed :
      Measurable
        ((fun p : OrthogonalGroup d × Ambient d ↦
            f (orthogonalAction p.1 p.2)) ∘
          (fun p : OrthogonalGroup d × Ambient d ↦
            (p.1⁻¹, p.2))) :=
    hforward.comp hinverse
  have heq :
      ((fun p : OrthogonalGroup d × Ambient d ↦
            f (orthogonalAction p.1 p.2)) ∘
          (fun p : OrthogonalGroup d × Ambient d ↦
            (p.1⁻¹, p.2))) =
        (fun p : OrthogonalGroup d × Ambient d ↦
          f (orthogonalLinearIsometry (p.1⁻¹) p.2)) := by
    funext p
    simp only [Function.comp_apply, orthogonalLinearIsometry_apply]
  rw [← heq]
  exact hcomposed

private theorem radialOrthogonalHaar_radialFourierOrbitAverage_eq
    {d : ℕ} (f : Schwartz d) :
    radialFourierOrbitAverage
        (radialOrthogonalHaar d)
        (fun U : OrthogonalGroup d ↦
          orthogonalLinearIsometry (U⁻¹)) f =
      fun x : Ambient d ↦
        ∫ U : OrthogonalGroup d,
          f (orthogonalAction (U⁻¹) x)
            ∂radialOrthogonalHaar d := by
  funext x
  simp only [radialFourierOrbitAverage,
    orthogonalLinearIsometry_apply]

private theorem radialOrthogonalHaar_fourier_average
    {d : ℕ} (f : Schwartz d) (ξ : Ambient d) :
    (𝓕 (fun x : Ambient d ↦
      ∫ U : OrthogonalGroup d,
        f (orthogonalAction (U⁻¹) x)
          ∂radialOrthogonalHaar d) : Ambient d → ℂ) ξ =
      ∫ U : OrthogonalGroup d,
        (𝓕 f : Schwartz d) (orthogonalAction (U⁻¹) ξ)
          ∂radialOrthogonalHaar d := by
  have h := radialFourierOrbitAverage_fourier
    (radialOrthogonalHaar d)
    (fun U : OrthogonalGroup d ↦ orthogonalLinearIsometry (U⁻¹))
    f ξ (radialOrthogonalHaarOrbit_measurable f)
  rw [radialOrthogonalHaar_radialFourierOrbitAverage_eq] at h
  simpa only [orthogonalLinearIsometry_apply] using h

private theorem fourier_radialSymmetrizationAverage
    {d : ℕ} (f : Schwartz d) (ξ : Ambient d) :
    (𝓕 (radialSymmetrizationAverage f) : Ambient d → ℂ) ξ =
      radialSymmetrizationAverage (𝓕 f : Schwartz d) ξ := by
  change
    (𝓕 (fun x : Ambient d ↦
      ∫ U : OrthogonalGroup d,
        f (orthogonalAction (U⁻¹) x)
          ∂radialOrthogonalHaar d) : Ambient d → ℂ) ξ =
      ∫ U : OrthogonalGroup d,
        (𝓕 f : Schwartz d) (orthogonalAction (U⁻¹) ξ)
          ∂radialOrthogonalHaar d
  exact radialOrthogonalHaar_fourier_average f ξ

end SpherePacking.Alternative

end

section

namespace CohnElkies

open Real

private theorem manuscript_pi_gt_d40 :
    (3.1415926535897932384626433832795028841971 : ℝ) < Real.pi := by
  pi_lower_bound [
    735361475704189444449261582374705033264205603/519979086093778969111063874274015566558335798,
    1614821575232605988709216844925630282861368192/873935138947824998568689940684460881617215487,
    656577935817689754327774835830964272273936545/334720529017192598890280584873839652366119323,
    988606023810882196459876585735687236751892707/496694732804374296058706410324658507725695065,
    1651831167639818239827787964208026071585604941/826911635098838176108984261014947012483672374,
    1755154679930232820263785896055424906833073974/877841729481728059293345630561450330393398391,
    2 - 79752583061956089944333925496586284889697/529578559130067173792567219683348143064410820,
    2 - 33578028749876676575324057253414810454419/891860101759478655835226554662632484009089330,
    2 - 2023347725461536275851288370301469261345/214966623026649846227138260963993675942277029,
    2 - 380666362037738892566128113113773132347/161772518244974281498999006942870931497546037,
    2 - 251046407591291149403479324978532177198/426750641818596804075471463319417463200870061,
    2 - 17315306189051452896527586926594829145/117736283560911906970692594678804476810243167,
    2 - 27907377984971801502612766014066156500/759030398147093798557642130232480057456819083,
    2 - 2733218175793841927608435860500580766/297354438176963679012339193982596158449108593,
    2 - 1037292406535850791771626211910383705/451399750411679965819001075988389198958582008,
    2 - 383753404709486344001837952766399826/667993672716155145330103580991570671665923771,
    2 - 44507605683707279921013884665630709/309894829528892083222521203142405007605307258,
    2 - 23561580395478464172815305141493120/656212512702781872380015327329460136094681669,
    2 - 8771864317040573691992116797987775/977219189535313506358048457167695800363495739,
    2 - 412307583058020647935707466896589/183730558336283575052453369562826705376838777,
    2 - 475086774834670308773605284009400/846823701384727188979626370746895670941323369,
    2 - 6973622552264526590076341756765/49720844061159399112765143738232888815228211,
    2 - 3186955676953953774593674190519/90889993002100255334812570424527051756032623,
    2 - 4375550972375884762729814599645/499151965162799191521774371691243901983241411,
    2 - 1772257618646811055661652109395/808698953532660250926135466132261140481448534,
    2 - 349757213473338141134005772451/638390919131392777951497334354505236135793351,
    2 - 72280955868919422410960110385/527720419483186549925790952520229083602745314,
    2 - 25257215036912345125862033732/737607739356847568184981921787132294843646957,
    2 - 2324341250967290575936039609/271518786709342497698200579680060636461095427,
    2 - 1061630290064446694733083483/496058946890397653337409495554235728792888595,
    2 - 442486281704336039732791711/827027190048904780667399013302533997104961654,
    2 - 82433206310005974378689695/616285799584080780936023628928240995696737692,
    2 - 30978652654901532434646773/926408401471875934314552525649109498545930380,
    2 - 5949112494974025801844681/711626533024603400661141506439715595438426398,
    2 - 1488645378333291753464333/712280731205802957601587489731363925875380583,
    2 - 311613299623885301012002/596397643495347974982662142013620277703762065,
    2 - 63072330278304091838905/482857300290369859425002505038023854988170907,
    2 - 32605808218565518555751/998469690955292120604834604188297664602699610,
    2 - 5663641555015948878471/693738292909227354863640966523341210443528992,
    2 - 1603199205058214183873/785502167753187813716964469784487075859456977,
    2 - 44825661393271397839/87850977181856875708959200359192810444967936,
    2 - 16712123733148509526/131012135023317745422814662893303915447412115,
    2 - 7140385192192506875/223903825475514836670954579146312854911781387,
    2 - 4160227356078390473/521815445414544909502154200808081979185363550,
    2 - 699108891373707226/350755654747986089749457002604645380644053897,
    2 - 497141281084142964/997699315231333805990357056984939405828893971,
    2 - 92888033870267334/745657874827459315134729234044062405590466049,
    2 - 10665263554519287/342461237478433816261148956467446703435302915,
    2 - 4236305380785542/544110466890662689837268986105222479944808103,
    2 - 568739137072179/292195098884918480899301001339344616600520732,
    2 - 181385748742031/372754560643267024821967034486762314848400139,
    2 - 47674565390365/391892126017424105724813755694867351547151423,
    2 - 5400864560618/177583688716374021873992688626359744424923661,
    2 - 4353452415089/572576579061074327256536572269398173074839437,
    2 - 826510067390/434818403256652567017102390033358512038607537,
    2 - 96176477778/202389803334583619135833712211760400508055511,
    2 - 28928898521/243507111826904771212880637097965274798624030,
    2 - 24139063429/812755952465356617792735761066305578964302993,
    2 - 6367069803/857510300243666595284348532136001675193759107,
    2 - 1639239443/883084213259843725279555829890113730634319291,
    2 - 449528216/968671837807799978038261085163266904926700999,
    2 - 76535949/659698018833096349363195216762459711821137560,
    2 - 27368039/943590108624480001162828822150932034770679532,
    2 - 6235781/859984344680080078244721278776482467699447003,
    2 - 1785710/985077984065614745945940843479880071089657287,
    2 - 397219/876495493114916585044381620545854549637103999,
    2 - 101968/900002189642910478540105131766805683689790157,
    2 - 6373/225000547410727619635026282941701420922445946
  ]

private theorem manuscript_pi_lt_d40 :
    Real.pi < (3.1415926535897932384626433832795028841972 : ℝ) := by
  pi_upper_bound [
    1039958172187557938222127748548031133116671596/735361475704189444449261582374705033264205603,
    478600201932118537014372129053837886122622977/259016562814844923225458149839934988405454400,
    1182498913955913611246998658806287670131286118/602832718630194264072038938933209267184190947,
    1139983240089622598367681070890702364436863257/572749565752289112691897652726420869483397158,
    674481014253471597715809997605373598022854036/337647217988004053604565193351470742340478365,
    269533488700628097187480932294978891806858111/134807345802484089306431186280444595624077023,
    420905580543923078565774113181648780392853312/210468638173333744382139020201544708917537687,
    2 - 31926845698391972653468048132858014902853/848003319835492629921682152249077132987676173,
    2 - 8108366808736375002249475328759402081624/861457578053143701596187469837317055705281751,
    2 - 2029306367992899893583901291970723460857/862398242081153303323095550851323422829390564,
    2 - 231101607182344170973682087493706072629/392846725578063437471774030332666574376227416,
    2 - 135315453494852624563540466067291440848/920084139945324285207090004477574497128390087,
    2 - 34044628036482554587150776276456079741/925952541554296651600453869089959260049677115,
    2 - 4052169822603481177168312692673824331/440846871160565874727106467869656774562246627,
    2 - 801922142447528620497602929069763587/348973397153566374832583919639342120400246079,
    2 - 481209055088791607609364415560704144/837633230371927058033366741151868934748925247,
    2 - 113054314109121052752837595887467637/787167650565777117853550453436049729117746205,
    2 - 14340425695331680726780260220166029/399394549126552515418368409320179336950126770,
    2 - 3019050454844383843500019861063084/336333752098505251371206631083595757042543133,
    2 - 1610246068693380262057771290784723/717550249902165056039428804346235182014784930,
    2 - 487734481880246629681327728136419/869367747360521469272727157390228771417681774,
    2 - 137242647445257253738871692029311/978518728397542913198239584143906449903230908,
    2 - 21288593117416659995434766323662/607137430074311094126890035131943120519883575,
    2 - 5857330264071901236134578919623/668189658942879462211683907427185023736732090,
    2 - 2132126319239785003961782198301/972910656457038550077219955056105607109522974,
    2 - 168942853109302073475588485888/308361283548905886801637537324565780491650037,
    2 - 75315778818612352219470484959/549877542626017186668561016006891803309628525,
    2 - 29671165285025041273006731466/866512048853593027811592443889978200306743183,
    2 - 8207314770350496977343044476/958740523862342596587563150141441205238118539,
    2 - 2106996854031980052849266081/984518480957279362976237003741885645208294518,
    2 - 399026005149600975072600235/745797936433699146277898488182552125370505008,
    2 - 95685947067243905811005714/715365725015338979873684473685166565426855403,
    2 - 33073566370724119432203115/989056241205785090258279708019330815863592041,
    2 - 3984038500980196147331973/476566464037162809315126170425177865990984692,
    2 - 1042168041131121032104528/498652147234220326353021612299768165554943531,
    2 - 350618556460258511634529/671049923385909816377109097197941893316019192,
    2 - 79028164771330370274248/605008981276109856817751151899493354536360527,
    2 - 4131057167700323562223/126503086379677319104240685793019008628153779,
    2 - 3286166430575333444773/402521852348496839241792808620760988972084265,
    2 - 956634030973735405145/468711625296155077873789265301216817301264231,
    2 - 483277038052230485720/947144084946281086629831373567881309173888721,
    2 - 113952896055717407583/893316280009203015109189852668480167576970194,
    2 - 25569069203407167573/801779211400377293212910706890228769506220562,
    2 - 5834153507919709911/731775249471387034816150077230941975121262313,
    2 - 1421965109039843353/713425775303792154982421860936484924627622640,
    2 - 85216225560508607/171018125275998454226342111284069679460535239,
    2 - 37093012248467561/297763829545266672883865946689942992746972732,
    2 - 30741359800390301/987103981556127176822113852828510585552191322,
    2 - 1804544974600881/231775502566157072957301476478860117147634601,
    2 - 1647741116704936/846542548506279747906539872767526287661823269,
    2 - 461099060868406/947575975726025446169145676561321977987258143,
    2 - 49163781692172/404133708878982793050423215175582405635492687,
    2 - 21881458565777/719475573399778575163850086037978793585812022,
    2 - 2094824291058/275516351608843520478868364472078908817430105,
    2 - 1681569257363/884656204807047798406922262871635855544343887,
    2 - 393715917389/828519498020983981957157855180512039240663501,
    2 - 105566259993/888597091195954639448027786400187331580333109,
    2 - 19159340368/645089979369049868235147149302222051991873987,
    2 - 5607517927/755214648178958075303519341119553451792278928,
    2 - 503785402/271397163652170674127158979142886913570521167,
    2 - 15501183/33402929761376817082750298554995233427377101,
    2 - 57160993/492696495298339981310941296919078409156330724,
    2 - 2664361/91861338161818176317937714259135608038765309,
    2 - 6903394/952055687195941732346620159941135907213796675,
    2 - 787336/434329963802792643606236891736102085809815933,
    2 - 390117/860824362096253989380565946398553793601962899,
    2 - 21941/193658285373402428307394934647099908852166227,
    2 - 24034/848527091867162656568056124936584332410178231
  ]

end CohnElkies

end


section

open Finset

namespace CohnElkies

private theorem criticalBinaryExponent_eq_log_div :
    criticalBinaryExponent =
      Real.log (2 * Real.pi / Real.exp 1) /
        (2 * Real.log 2) := by
  unfold criticalBinaryExponent Real.logb
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp

private theorem criticalBinaryExponent_eq_three_halves_sub_logFourDivPi :
    criticalBinaryExponent =
      (3 / 2 : ℝ) -
        (Real.log (4 / Real.pi) + 1) / (2 * Real.log 2) := by
  rw [criticalBinaryExponent_eq_log_div]
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hlogtwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul htwo htwo]
    ring
  have hleft :
      Real.log (2 * Real.pi / Real.exp 1) =
        Real.log 2 + Real.log Real.pi - 1 := by
    rw [Real.log_div (mul_ne_zero htwo hpi) (Real.exp_ne_zero _),
      Real.log_mul htwo hpi, Real.log_exp]
  have hright :
      Real.log (4 / Real.pi) =
        2 * Real.log 2 - Real.log Real.pi := by
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hpi, hfour]
  rw [hleft, hright]
  field_simp
  ring

private theorem baseTwo_log_two_gt_d36 :
    (0.693147180559945309417232121458176568 : ℝ) < Real.log 2 := by
  have h := Real.sum_range_le_log_div
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 42
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem baseTwo_log_two_lt_d36 :
    Real.log 2 <
      (0.693147180559945309417232121458176569 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 42
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem baseTwo_log_four_div_pi_gt_d36 :
    (0.241564475270490444691036891563294424 : ℝ) <
      Real.log (4 / Real.pi) := by
  have hs :
      (0.241564475270490444691036891563294424 : ℝ) <
        Real.log
          (4 / (3.1415926535897932384626433832795028841972 : ℝ)) := by
    have h := Real.sum_range_le_log_div
      (x := (2146018366025516903843391541801242789507 /
        17853981633974483096156608458198757210493 : ℝ))
      (by norm_num) (by norm_num) 20
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  calc
    (0.241564475270490444691036891563294424 : ℝ) <
        Real.log
          (4 / (3.1415926535897932384626433832795028841972 : ℝ)) := hs
    _ < Real.log (4 / Real.pi) := by
      apply Real.log_lt_log (by positivity)
      apply (div_lt_div_iff₀
        (by norm_num :
          (0 : ℝ) < 3.1415926535897932384626433832795028841972)
        Real.pi_pos).2
      linarith [manuscript_pi_lt_d40]

private theorem baseTwo_log_four_div_pi_lt_d36 :
    Real.log (4 / Real.pi) <
      (0.241564475270490444691036891563294425 : ℝ) := by
  have hs :
      Real.log
        (4 / (3.1415926535897932384626433832795028841971 : ℝ)) <
          (0.241564475270490444691036891563294425 : ℝ) := by
    have h := Real.log_div_le_sum_range_add
      (x := (8584073464102067615373566167204971158029 /
        71415926535897932384626433832795028841971 : ℝ))
      (by norm_num) (by norm_num) 20
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  calc
    Real.log (4 / Real.pi) <
        Real.log
          (4 / (3.1415926535897932384626433832795028841971 : ℝ)) := by
      apply Real.log_lt_log (by positivity)
      apply (div_lt_div_iff₀ Real.pi_pos
        (by norm_num :
          (0 : ℝ) < 3.1415926535897932384626433832795028841971)).2
      linarith [manuscript_pi_gt_d40]
    _ < (0.241564475270490444691036891563294425 : ℝ) := hs

private theorem criticalBinaryExponent_gt_d33 :
    (0.604400544291677695341677307053057 : ℝ) <
      criticalBinaryExponent := by
  rw [criticalBinaryExponent_eq_three_halves_sub_logFourDivPi]
  have hden : 0 < 2 * Real.log (2 : ℝ) := by positivity
  have hratio :
      (Real.log (4 / Real.pi) + 1) / (2 * Real.log 2) <
        (3 / 2 : ℝ) -
          0.604400544291677695341677307053057 := by
    apply (div_lt_iff₀ hden).2
    linarith [baseTwo_log_two_gt_d36,
      baseTwo_log_four_div_pi_lt_d36]
  linarith

private theorem criticalBinaryExponent_lt_d33 :
    criticalBinaryExponent <
      (0.604400544291677695341677307053058 : ℝ) := by
  rw [criticalBinaryExponent_eq_three_halves_sub_logFourDivPi]
  have hden : 0 < 2 * Real.log (2 : ℝ) := by positivity
  have hratio :
      (3 / 2 : ℝ) - 0.604400544291677695341677307053058 <
        (Real.log (4 / Real.pi) + 1) / (2 * Real.log 2) := by
    apply (lt_div_iff₀ hden).2
    linarith [baseTwo_log_two_lt_d36,
      baseTwo_log_four_div_pi_gt_d36]
  linarith

private theorem criticalBinaryExponent_gt_d30 :
    (0.604400544291677695341677307053 : ℝ) <
      criticalBinaryExponent := by
  linarith [criticalBinaryExponent_gt_d33]

private theorem criticalBinaryExponent_lt_d30 :
    criticalBinaryExponent <
      (0.604400544291677695341677307054 : ℝ) := by
  linarith [criticalBinaryExponent_lt_d33]

private theorem criticalBinaryExponent_mem_Ioo_d30 :
    criticalBinaryExponent ∈ Set.Ioo
      (0.604400544291677695341677307053 : ℝ)
      0.604400544291677695341677307054 :=
  ⟨criticalBinaryExponent_gt_d30, criticalBinaryExponent_lt_d30⟩

end CohnElkies

end

section

open Filter
open scoped Topology

namespace CohnElkies

private theorem manuscriptQuotientRootSet_eq_literal (d : ℕ) :
    manuscriptQuotientRootSet d =
      {q : ℝ | ∃ f : Admissible d,
        quotient f ^ ((d : ℝ)⁻¹) = q} := by
  ext q
  simp only [manuscriptQuotientRootSet, Set.mem_range, Set.mem_ofPred_eq]

private structure SharpCohnElkiesManuscriptConclusions : Prop where
  root_before_infimum :
    Tendsto
      (fun d : ℕ =>
        sInf {q : ℝ | ∃ f : Admissible d,
          quotient f ^ ((d : ℝ)⁻¹) = q} /
          Real.sqrt (d : ℝ))
      atTop (𝓝 (1 / Real.pi))
  root_before_infimum_vanishing_error :
    ∃ err : ℕ → ℝ,
      Tendsto err atTop (𝓝 0) ∧
      ∀ d : ℕ, 0 < d →
        sInf {q : ℝ | ∃ f : Admissible d,
          quotient f ^ ((d : ℝ)⁻¹) = q} =
          (1 / Real.pi + err d) * Real.sqrt (d : ℝ)
  linear_program_root :
    Tendsto
      (fun d : ℕ => (linearProgram d) ^ ((d : ℝ)⁻¹))
      atTop (𝓝 (Real.sqrt (Real.exp 1 / (2 * Real.pi))))
  natural_logarithmic_rate :
    Tendsto
      (fun d : ℕ => Real.log (linearProgram d) / (d : ℝ))
      atTop
      (𝓝 ((1 / 2 : ℝ) * Real.log (Real.exp 1 / (2 * Real.pi))))
  natural_vanishing_exponential_error :
    ∃ err : ℕ → ℝ,
      Tendsto err atTop (𝓝 0) ∧
      (∀ᶠ d : ℕ in atTop,
        linearProgram d =
          (Real.sqrt (Real.exp 1 / (2 * Real.pi)) + err d) ^ d)
  universal_nonnegative_delta :
    ∃ δ : ℕ → ℝ,
      Tendsto δ atTop (𝓝 0) ∧
      (∀ d : ℕ, 0 ≤ δ d) ∧
      (∀ᶠ d : ℕ in atTop, ∀ f : Admissible d,
        (2 : ℝ) ^ d / unitBallVolume d *
          (Real.sqrt (Real.exp 1 / (2 * Real.pi)) - δ d) ^ d ≤
            quotient f)
  base_two_exponent_positive :
    0 < (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1)
  base_two_decimal_certificate :
    (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1) ∈
      Set.Ioo
        (0.604400544291677695341677307053 : ℝ)
        0.604400544291677695341677307054
  base_two_logarithmic_rate :
    Tendsto
      (fun d : ℕ => Real.logb 2 (linearProgram d) / (d : ℝ))
      atTop
      (𝓝 (-((1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1))))
  base_two_vanishing_exponential_error :
    ∃ err : ℕ → ℝ,
      Tendsto err atTop (𝓝 0) ∧
      (∀ᶠ d : ℕ in atTop,
        linearProgram d =
          (2 : ℝ) ^
            (-((1 / 2 : ℝ) *
                Real.logb 2 (2 * Real.pi / Real.exp 1) + err d) *
              (d : ℝ)))

private theorem sharpCohnElkiesManuscriptConclusions :
    SharpCohnElkiesManuscriptConclusions := by
  refine
    { root_before_infimum := ?_
      root_before_infimum_vanishing_error := ?_
      linear_program_root := ?_
      natural_logarithmic_rate := ?_
      natural_vanishing_exponential_error := ?_
      universal_nonnegative_delta := ?_
      base_two_exponent_positive := ?_
      base_two_decimal_certificate := ?_
      base_two_logarithmic_rate := ?_
      base_two_vanishing_exponential_error := ?_ }
  · simp_rw [← manuscriptQuotientRootSet_eq_literal]
    simpa only [one_div] using
      (manuscriptQuotientRootInf_div_sqrt_tendsto
        sharpQuotientAsymptotic)
  · obtain ⟨err, herr, hformula⟩ :=
      exists_manuscriptQuotientRootIsLittleO
    refine ⟨err, (Asymptotics.isLittleO_one_iff ℝ).mp herr, ?_⟩
    intro d hd
    rw [← manuscriptQuotientRootSet_eq_literal]
    simpa only [one_div] using hformula d hd
  · simpa only [SharpPackingRootAsymptotic, criticalPackingBase] using
      sharpPackingRootAsymptotic
  · simpa only [one_div, SharpLogAsymptotic] using sharpLogAsymptotic
  · obtain ⟨err, herr, hformula⟩ := exists_manuscriptPackingIsLittleO
    refine ⟨err, (Asymptotics.isLittleO_one_iff ℝ).mp herr, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    simpa only [criticalPackingBase] using hformula d hd
  · obtain ⟨δ, hδ, hnonneg, hbound⟩ :=
      exists_manuscriptUniversalPackingIsLittleO
    refine ⟨δ, (Asymptotics.isLittleO_one_iff ℝ).mp hδ, hnonneg, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd f
    simpa only [criticalPackingBase] using hbound d hd f
  · simpa only [one_div, inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left,
    criticalBinaryExponent] using criticalBinaryExponent_pos
  · simpa only [one_div, Set.mem_Ioo, criticalBinaryExponent] using
      criticalBinaryExponent_mem_Ioo_d30
  · simpa only [one_div, SharpBinaryLogAsymptotic, criticalBinaryExponent] using
      sharpBinaryLogAsymptotic
  · obtain ⟨err, herr, hformula⟩ := exists_manuscriptBinaryIsLittleO
    refine ⟨err, (Asymptotics.isLittleO_one_iff ℝ).mp herr, ?_⟩
    simpa only [one_div, neg_add_rev, eventually_atTop, criticalBinaryExponent] using hformula

end CohnElkies

end

section

open MeasureTheory
open scoped FourierTransform Real Topology

namespace SpherePacking.Alternative

private structure IsUnrestrictedAdmissible {d : ℕ} (f : Schwartz d) : Prop where
  real_valued : IsRealValued f
  fourier_real_valued : IsRealValued (𝓕 f : Schwartz d)
  fourier_zero_pos : 0 < fourierReal f 0
  fourier_nonneg : ∀ x, 0 ≤ fourierReal f x
  eventually_nonpos : ∀ x : Ambient d, 1 ≤ ‖x‖ → (f x).re ≤ 0

end SpherePacking.Alternative

namespace SpherePacking.Alternative

private theorem quotient_eq_of_origin_and_fourier_origin
    {d : ℕ} {f g : Schwartz d}
    (horigin : g 0 = f 0)
    (hfourier : fourierReal g 0 = fourierReal f 0) :
    quotient g = quotient f := by
  simp only [quotient, horigin, hfourier]

private theorem IsUnrestrictedAdmissible.radialAdmissible_of_average_data
    {d : ℕ} {f g : Schwartz d}
    (hf : IsUnrestrictedAdmissible f)
    (hreal : IsRealValued g)
    (hradial : IsRadial g)
    (hfourier_zero : fourierReal g 0 = fourierReal f 0)
    (hfourier_nonneg : ∀ x : Ambient d, 0 ≤ fourierReal g x)
    (hexterior : ∀ x : Ambient d, 1 ≤ ‖x‖ → (g x).re ≤ 0) :
    IsAdmissible g where
  real_valued := hreal
  radial := hradial
  fourier_real_valued := hradial.fourier_realValued hreal
  fourier_zero_pos := hfourier_zero.symm ▸ hf.fourier_zero_pos
  fourier_nonneg := hfourier_nonneg
  eventually_nonpos := hexterior

private theorem radial_of_radialSymmetrizationAverage
    {d : ℕ} {f g : Schwartz d}
    (haverage : ∀ x : Ambient d,
      g x = radialSymmetrizationAverage f x) :
    IsRadial g := by
  intro x y hxy
  rw [haverage x, haverage y]
  exact radialSymmetrizationAverage_eq_of_norm_eq f hxy

private theorem radialSymmetrizationAverage_schwartz_zero
    {d : ℕ} {f g : Schwartz d}
    (haverage : ∀ x : Ambient d,
      g x = radialSymmetrizationAverage f x) :
    g 0 = f 0 := by
  rw [haverage 0, radialSymmetrizationAverage_zero]

private theorem radialSymmetrizationAverage_fourier_zero
    {d : ℕ} {f g : Schwartz d}
    (hfourier : ∀ x : Ambient d,
      (𝓕 g : Schwartz d) x =
        radialSymmetrizationAverage (𝓕 f : Schwartz d) x) :
    fourierReal g 0 = fourierReal f 0 := by
  unfold fourierReal
  rw [hfourier 0, radialSymmetrizationAverage_zero]

private theorem IsUnrestrictedAdmissible.radialAdmissible_of_radialSymmetrizationAverage
    {d : ℕ} {f g : Schwartz d}
    (hf : IsUnrestrictedAdmissible f)
    (haverage : ∀ x : Ambient d,
      g x = radialSymmetrizationAverage f x)
    (hfourier : ∀ x : Ambient d,
      (𝓕 g : Schwartz d) x =
        radialSymmetrizationAverage (𝓕 f : Schwartz d) x) :
    IsAdmissible g := by
  apply hf.radialAdmissible_of_average_data
  · intro x
    rw [haverage x]
    exact radialSymmetrizationAverage_im_eq_zero hf.real_valued x
  · exact radial_of_radialSymmetrizationAverage haverage
  · exact radialSymmetrizationAverage_fourier_zero hfourier
  · intro x
    change 0 ≤ ((𝓕 g : Schwartz d) x).re
    rw [hfourier x]
    apply radialSymmetrizationAverage_nonneg_of_nonneg
    intro y
    exact hf.fourier_nonneg y
  · intro x hx
    rw [haverage x]
    exact radialSymmetrizationAverage_nonpos_of_one_le_norm
      hf.eventually_nonpos hx

private theorem quotient_eq_of_radialSymmetrizationAverage
    {d : ℕ} {f g : Schwartz d}
    (haverage : ∀ x : Ambient d,
      g x = radialSymmetrizationAverage f x)
    (hfourier : ∀ x : Ambient d,
      (𝓕 g : Schwartz d) x =
        radialSymmetrizationAverage (𝓕 f : Schwartz d) x) :
    quotient g = quotient f := by
  exact quotient_eq_of_origin_and_fourier_origin
    (radialSymmetrizationAverage_schwartz_zero haverage)
    (radialSymmetrizationAverage_fourier_zero hfourier)

private theorem radialSymmetrization_fourier_average_apply_for_admissibility
    {d : ℕ} (f : Schwartz d) (x : Ambient d) :
    (𝓕 (radialSymmetrization f) : Schwartz d) x =
      radialSymmetrizationAverage (𝓕 f : Schwartz d) x := by
  have hfun : (radialSymmetrization f : Ambient d → ℂ) =
      radialSymmetrizationAverage f := by
    funext y
    exact radialSymmetrization_apply f y
  calc
    (𝓕 (radialSymmetrization f) : Schwartz d) x =
        (𝓕 (radialSymmetrization f : Ambient d → ℂ)) x :=
      congrFun (SchwartzMap.fourier_coe (radialSymmetrization f)) x
    _ = (𝓕 (radialSymmetrizationAverage f) : Ambient d → ℂ) x := by
      rw [hfun]
    _ = radialSymmetrizationAverage (𝓕 f : Schwartz d) x :=
      fourier_radialSymmetrizationAverage f x

private theorem IsUnrestrictedAdmissible.radialSymmetrization_admissible
    {d : ℕ} {f : Schwartz d}
    (hf : IsUnrestrictedAdmissible f) :
    IsAdmissible (radialSymmetrization f) := by
  exact hf.radialAdmissible_of_radialSymmetrizationAverage
    (radialSymmetrization_apply f)
    (radialSymmetrization_fourier_average_apply_for_admissibility f)

private theorem IsUnrestrictedAdmissible.quotient_radialSymmetrization
    {d : ℕ} {f : Schwartz d}
    (_hf : IsUnrestrictedAdmissible f) :
    quotient (radialSymmetrization f) = quotient f := by
  exact quotient_eq_of_radialSymmetrizationAverage
    (radialSymmetrization_apply f)
    (radialSymmetrization_fourier_average_apply_for_admissibility f)

end SpherePacking.Alternative

namespace SpherePacking.Alternative

end SpherePacking.Alternative

end

section

open Filter
open scoped FourierTransform SchwartzMap Topology

namespace PackingBounds

private theorem FullAdmissible.toAlternative {d : ℕ} (f : FullAdmissible d) :
    SpherePacking.Alternative.IsUnrestrictedAdmissible f.function where
  real_valued := f.real
  fourier_real_valued := f.fourier_real
  fourier_zero_pos := f.fourier_zero_pos
  fourier_nonneg := f.fourier_nonneg
  eventually_nonpos := f.outside_nonpos

private noncomputable def FullAdmissible.radialization {d : ℕ} (f : FullAdmissible d) :
    CohnElkies.Admissible d :=
  let hf := f.toAlternative
  let g := SpherePacking.Alternative.radialSymmetrization f.function
  let hg := hf.radialSymmetrization_admissible
  { function := g
    real := hg.real_valued
    radial := hg.radial
    fourier_real := hg.fourier_real_valued
    fourier_nonneg := hg.fourier_nonneg
    fourier_zero_pos := hg.fourier_zero_pos
    outside_nonpos := hg.eventually_nonpos }

private theorem FullAdmissible.quotient_radialization {d : ℕ}
    (f : FullAdmissible d) :
    CohnElkies.quotient f.radialization = fullQuotient f := by
  change
    SpherePacking.Alternative.quotient
        (SpherePacking.Alternative.radialSymmetrization f.function) =
      SpherePacking.Alternative.quotient f.function
  exact f.toAlternative.quotient_radialSymmetrization

private theorem exists_radial_admissible_of_full {d : ℕ}
    (f : FullAdmissible d) :
    ∃ g : CohnElkies.Admissible d,
      CohnElkies.quotient g = fullQuotient f := by
  exact ⟨f.radialization, f.quotient_radialization⟩

private theorem fullQuotientSet_eq_radial (d : ℕ) :
    fullQuotientSet d = CohnElkies.quotientSet d := by
  apply (fullQuotientSet_eq_radial_iff d).2
  exact exists_radial_admissible_of_full

private theorem fullLinearProgram_eq_radial (d : ℕ) :
    fullLinearProgram d = CohnElkies.linearProgram d := by
  simp only [fullLinearProgram, CohnElkies.linearProgram,
    fullQuotientSet_eq_radial]

namespace FullMain

public
theorem exact_limit :
    Tendsto
      (fun d : ℕ =>
        fullLinearProgram d ^ ((d : ℝ)⁻¹))
      atTop
      (nhds (Real.sqrt (Real.exp 1 / (2 * Real.pi)))) := by
  simpa only [fullLinearProgram_eq_radial] using
    RadialMain.exact_limit

public
theorem exact_binary_exponent :
    Tendsto
      (fun d : ℕ =>
        Real.logb 2 (fullLinearProgram d) / (d : ℝ))
      atTop
      (nhds (-(1 / 2 : ℝ) *
        Real.logb 2 (2 * Real.pi / Real.exp 1))) := by
  simpa only [fullLinearProgram_eq_radial] using
    RadialMain.exact_binary_exponent

end FullMain
end PackingBounds

end

section

open Filter
open scoped Topology

namespace PackingBounds

private theorem fullQuotientRootSet_eq_radial (d : ℕ) :
    {q : ℝ | ∃ f : FullAdmissible d,
      fullQuotient f ^ ((d : ℝ)⁻¹) = q} =
      {q : ℝ | ∃ f : CohnElkies.Admissible d,
        CohnElkies.quotient f ^ ((d : ℝ)⁻¹) = q} := by
  ext q
  constructor
  · rintro ⟨f, hq⟩
    have hf : fullQuotient f ∈ CohnElkies.quotientSet d := by
      rw [← fullQuotientSet_eq_radial d]
      exact ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := hf
    exact ⟨g, by simpa only [hg] using hq⟩
  · rintro ⟨f, hq⟩
    exact ⟨radialToFull f, by simpa only [fullQuotient_radialToFull] using hq⟩

/-- The complete sharp asymptotic conclusions for the unrestricted program. -/
public
structure SharpFullCohnElkiesManuscriptConclusions : Prop where
  /-- The normalized infimum of pointwise quotient roots tends to `1 / π`. -/
  root_before_infimum :
    Tendsto
      (fun d : ℕ =>
        sInf {q : ℝ | ∃ f : FullAdmissible d,
          fullQuotient f ^ ((d : ℝ)⁻¹) = q} /
          Real.sqrt (d : ℝ))
      atTop (𝓝 (1 / Real.pi))
  /-- The quotient-root infimum has a vanishing additive error. -/
  root_before_infimum_vanishing_error :
    ∃ err : ℕ → ℝ,
      Tendsto err atTop (𝓝 0) ∧
      ∀ d : ℕ, 0 < d →
        sInf {q : ℝ | ∃ f : FullAdmissible d,
          fullQuotient f ^ ((d : ℝ)⁻¹) = q} =
          (1 / Real.pi + err d) * Real.sqrt (d : ℝ)
  /-- The linear-program root has the sharp Cohn--Elkies limit. -/
  linear_program_root :
    Tendsto
      (fun d : ℕ => (fullLinearProgram d) ^ ((d : ℝ)⁻¹))
      atTop (𝓝 (Real.sqrt (Real.exp 1 / (2 * Real.pi))))
  /-- The natural-logarithmic rate has its sharp limit. -/
  natural_logarithmic_rate :
    Tendsto
      (fun d : ℕ => Real.log (fullLinearProgram d) / (d : ℝ))
      atTop
      (𝓝 ((1 / 2 : ℝ) * Real.log (Real.exp 1 / (2 * Real.pi))))
  /-- The linear program admits a vanishing root-error expansion. -/
  natural_vanishing_exponential_error :
    ∃ err : ℕ → ℝ,
      Tendsto err atTop (𝓝 0) ∧
      (∀ᶠ d : ℕ in atTop,
        fullLinearProgram d =
          (Real.sqrt (Real.exp 1 / (2 * Real.pi)) + err d) ^ d)
  /-- Every admissible function obeys a universal vanishing-error lower bound. -/
  universal_nonnegative_delta :
    ∃ δ : ℕ → ℝ,
      Tendsto δ atTop (𝓝 0) ∧
      (∀ d : ℕ, 0 ≤ δ d) ∧
      (∀ᶠ d : ℕ in atTop, ∀ f : FullAdmissible d,
        (2 : ℝ) ^ d / CohnElkies.unitBallVolume d *
          (Real.sqrt (Real.exp 1 / (2 * Real.pi)) - δ d) ^ d ≤
            fullQuotient f)
  /-- The sharp base-two exponent is positive. -/
  base_two_exponent_positive :
    0 < (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1)
  /-- A certified narrow decimal interval contains the base-two exponent. -/
  base_two_decimal_certificate :
    (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1) ∈
      Set.Ioo
        (0.604400544291677695341677307053 : ℝ)
        0.604400544291677695341677307054
  /-- The base-two logarithmic rate has its sharp limit. -/
  base_two_logarithmic_rate :
    Tendsto
      (fun d : ℕ => Real.logb 2 (fullLinearProgram d) / (d : ℝ))
      atTop
      (𝓝 (-((1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1))))
  /-- The linear program admits a vanishing base-two exponent error. -/
  base_two_vanishing_exponential_error :
    ∃ err : ℕ → ℝ,
      Tendsto err atTop (𝓝 0) ∧
      (∀ᶠ d : ℕ in atTop,
        fullLinearProgram d =
          (2 : ℝ) ^
            (-((1 / 2 : ℝ) *
                Real.logb 2 (2 * Real.pi / Real.exp 1) + err d) *
              (d : ℝ)))

private theorem SharpFullCohnElkiesManuscriptConclusions.ofRadial :
    SharpFullCohnElkiesManuscriptConclusions := by
  have hradial := CohnElkies.sharpCohnElkiesManuscriptConclusions
  refine
    { root_before_infimum := ?_
      root_before_infimum_vanishing_error := ?_
      linear_program_root := ?_
      natural_logarithmic_rate := ?_
      natural_vanishing_exponential_error := ?_
      universal_nonnegative_delta := ?_
      base_two_exponent_positive := hradial.base_two_exponent_positive
      base_two_decimal_certificate := hradial.base_two_decimal_certificate
      base_two_logarithmic_rate := ?_
      base_two_vanishing_exponential_error := ?_ }
  · simpa only [fullQuotientRootSet_eq_radial] using
      hradial.root_before_infimum
  · obtain ⟨err, herr, hformula⟩ :=
      hradial.root_before_infimum_vanishing_error
    exact ⟨err, herr, by simpa only [fullQuotientRootSet_eq_radial] using hformula⟩
  · simpa only [fullLinearProgram_eq_radial] using
      hradial.linear_program_root
  · simpa only [fullLinearProgram_eq_radial] using
      hradial.natural_logarithmic_rate
  · obtain ⟨err, herr, hformula⟩ :=
      hradial.natural_vanishing_exponential_error
    exact ⟨err, herr, by simpa only [fullLinearProgram_eq_radial] using hformula⟩
  · obtain ⟨δ, hδ, hnonneg, hbound⟩ :=
      hradial.universal_nonnegative_delta
    refine ⟨δ, hδ, hnonneg, ?_⟩
    filter_upwards [hbound] with d hd f
    have hf : fullQuotient f ∈ CohnElkies.quotientSet d := by
      rw [← fullQuotientSet_eq_radial d]
      exact ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := hf
    simpa only [ge_iff_le, hg] using hd g
  · simpa only [fullLinearProgram_eq_radial] using
      hradial.base_two_logarithmic_rate
  · obtain ⟨err, herr, hformula⟩ :=
      hradial.base_two_vanishing_exponential_error
    exact ⟨err, herr, by simpa only [fullLinearProgram_eq_radial] using hformula⟩

private theorem SharpFullCohnElkiesManuscriptConclusions.components :
    Tendsto
        (fun d : ℕ =>
          sInf {q : ℝ | ∃ f : FullAdmissible d,
            fullQuotient f ^ ((d : ℝ)⁻¹) = q} /
            Real.sqrt (d : ℝ))
        atTop (𝓝 (1 / Real.pi)) ∧
      (∃ err : ℕ → ℝ,
        Tendsto err atTop (𝓝 0) ∧
        ∀ d : ℕ, 0 < d →
          sInf {q : ℝ | ∃ f : FullAdmissible d,
            fullQuotient f ^ ((d : ℝ)⁻¹) = q} =
            (1 / Real.pi + err d) * Real.sqrt (d : ℝ)) ∧
      Tendsto
        (fun d : ℕ => (fullLinearProgram d) ^ ((d : ℝ)⁻¹))
        atTop (𝓝 (Real.sqrt (Real.exp 1 / (2 * Real.pi)))) ∧
      Tendsto
        (fun d : ℕ => Real.log (fullLinearProgram d) / (d : ℝ))
        atTop
        (𝓝 ((1 / 2 : ℝ) * Real.log (Real.exp 1 / (2 * Real.pi)))) ∧
      (∃ err : ℕ → ℝ,
        Tendsto err atTop (𝓝 0) ∧
        (∀ᶠ d : ℕ in atTop,
          fullLinearProgram d =
            (Real.sqrt (Real.exp 1 / (2 * Real.pi)) + err d) ^ d)) ∧
      (∃ δ : ℕ → ℝ,
        Tendsto δ atTop (𝓝 0) ∧
        (∀ d : ℕ, 0 ≤ δ d) ∧
        (∀ᶠ d : ℕ in atTop, ∀ f : FullAdmissible d,
          (2 : ℝ) ^ d / CohnElkies.unitBallVolume d *
            (Real.sqrt (Real.exp 1 / (2 * Real.pi)) - δ d) ^ d ≤
              fullQuotient f)) ∧
      0 < (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1) ∧
      (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1) ∈
        Set.Ioo
          (0.604400544291677695341677307053 : ℝ)
          0.604400544291677695341677307054 ∧
      Tendsto
        (fun d : ℕ => Real.logb 2 (fullLinearProgram d) / (d : ℝ))
        atTop
        (𝓝 (-((1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1)))) ∧
      (∃ err : ℕ → ℝ,
        Tendsto err atTop (𝓝 0) ∧
        (∀ᶠ d : ℕ in atTop,
          fullLinearProgram d =
            (2 : ℝ) ^
              (-((1 / 2 : ℝ) *
                  Real.logb 2 (2 * Real.pi / Real.exp 1) + err d) *
                (d : ℝ)))) :=
  ⟨SharpFullCohnElkiesManuscriptConclusions.ofRadial.root_before_infimum,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.root_before_infimum_vanishing_error,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.linear_program_root,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.natural_logarithmic_rate,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.natural_vanishing_exponential_error,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.universal_nonnegative_delta,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.base_two_exponent_positive,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.base_two_decimal_certificate,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.base_two_logarithmic_rate,
    SharpFullCohnElkiesManuscriptConclusions.ofRadial.base_two_vanishing_exponential_error⟩

public
theorem sharpFullCohnElkiesManuscriptConclusions :
    SharpFullCohnElkiesManuscriptConclusions :=
  { root_before_infimum :=
      SharpFullCohnElkiesManuscriptConclusions.components.1
    root_before_infimum_vanishing_error :=
      SharpFullCohnElkiesManuscriptConclusions.components.2.1
    linear_program_root :=
      SharpFullCohnElkiesManuscriptConclusions.components.2.2.1
    natural_logarithmic_rate :=
      SharpFullCohnElkiesManuscriptConclusions.components.2.2.2.1
    natural_vanishing_exponential_error :=
      SharpFullCohnElkiesManuscriptConclusions.components.2.2.2.2.1
    universal_nonnegative_delta :=
      SharpFullCohnElkiesManuscriptConclusions.components.2.2.2.2.2.1
    base_two_exponent_positive :=
      SharpFullCohnElkiesManuscriptConclusions.components.2.2.2.2.2.2.1
    base_two_decimal_certificate :=
      SharpFullCohnElkiesManuscriptConclusions.components.2.2.2.2.2.2.2.1
    base_two_logarithmic_rate :=
      SharpFullCohnElkiesManuscriptConclusions.components.2.2.2.2.2.2.2.2.1
    base_two_vanishing_exponential_error :=
      SharpFullCohnElkiesManuscriptConclusions.components.2.2.2.2.2.2.2.2.2 }

end PackingBounds

end
