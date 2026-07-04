import JL.NormPreservation
import JL.Projection

/-!
# Gaussian rotation invariance: the projection ↔ chi-squared link

This file closes the substantive gap between the abstract chi-squared concentration of
`JL.NormPreservation` and the *actual* Gaussian random projection `jlMap` of
`JL.Projection`.

The key probabilistic fact is **Gaussian rotation invariance**: if the entries of the
matrix `A : Matrix (Fin k) (Fin n) ℝ` are i.i.d. `N(0,1)`, then for a fixed unit vector
`u` (`∑ⱼ uⱼ² = 1`) the `k` row–vector products `Aᵢ · u` are themselves i.i.d. `N(0,1)`.
Concretely, the i.i.d. Gaussian matrix measure pushes forward under `A ↦ A.mulVec u` to
`gaussianVec k`:

`(gaussianMatrix k n).map (fun A i ↦ ∑ⱼ Aᵢⱼ uⱼ) = gaussianVec k`.

The single-coordinate version (`map_dotProduct_gaussianReal`) is proven through mathlib's
multivariate-Gaussian machinery (`ProbabilityTheory.stdGaussian`, its invariance and dual
variance lemmas); the `k`-fold independence is assembled with `Measure.pi_map_pi`.

Combining this with the deterministic identity `‖jlMap A x‖² = (1/k)·∑ᵢ(Aᵢ·x)²`
(`jlMap_sq_norm`) transports `jl_norm_preservation` to a genuine concentration bound on
the projected squared norm `∑ᵢ (jlMap A w i)²` of any fixed `w ≠ 0` (`jlMap_concentration`).
-/

open MeasureTheory ProbabilityTheory Real

namespace JL

/-! ## Single-coordinate rotation invariance -/

/-- **Single-coordinate Gaussian rotation invariance.** For a unit vector `u`
(`∑ⱼ uⱼ² = 1`), the linear form `row ↦ ∑ⱼ rowⱼ · uⱼ` pushes the i.i.d. standard Gaussian
product measure forward to the standard normal `N(0,1)`. -/
theorem map_dotProduct_gaussianReal {n : ℕ} (u : Fin n → ℝ) (hu : ∑ j, u j ^ 2 = 1) :
    (gaussianVec n).map (fun row : Fin n → ℝ => ∑ j, row j * u j) = gaussianReal 0 1 := by
  classical
  set y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 u with hy
  set L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ y with hL
  have htoLp : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by fun_prop
  have hLmeas : Measurable (⇑L) := L.continuous.measurable
  have hcomp : (fun row : Fin n → ℝ => ∑ j, row j * u j)
      = (⇑L) ∘ (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by
    funext row
    show ∑ j, row j * u j = L (WithLp.toLp 2 row)
    rw [hL, innerSL_apply_apply, hy, PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [RCLike.inner_apply, mul_comm]
  have hpiStd : (gaussianVec n).map (WithLp.toLp 2)
      = ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    have hpi : gaussianVec n = Measure.pi (fun _ : Fin n => gaussianReal 0 1) := rfl
    rw [hpi]; exact map_pi_eq_stdGaussian
  have hgl : HasGaussianLaw (⇑L) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    IsGaussian.hasGaussianLaw_id.map L
  have hLsq : ‖L‖ ^ 2 = 1 := by
    rw [hL, innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq]
    simpa [hy] using hu
  calc (gaussianVec n).map (fun row : Fin n → ℝ => ∑ j, row j * u j)
      = (gaussianVec n).map ((⇑L) ∘ (WithLp.toLp 2)) := by rw [hcomp]
    _ = ((gaussianVec n).map (WithLp.toLp 2)).map (⇑L) := (Measure.map_map hLmeas htoLp).symm
    _ = (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map (⇑L) := by rw [hpiStd]
    _ = gaussianReal 0 1 := by
        rw [hgl.map_eq_gaussianReal, integral_strongDual_stdGaussian L,
          variance_dual_stdGaussian L, hLsq, Real.toNNReal_one]

/-! ## The i.i.d. Gaussian matrix and the multi-row link -/

/-- The i.i.d. `N(0,1)` matrix measure on `Fin k → Fin n → ℝ`: every entry is an
independent standard Gaussian. -/
noncomputable def gaussianMatrix (k n : ℕ) : Measure (Fin k → Fin n → ℝ) :=
  Measure.pi (fun _ : Fin k => gaussianVec n)

instance (k n : ℕ) : IsProbabilityMeasure (gaussianMatrix k n) := by
  unfold gaussianMatrix; infer_instance

/-- **Projection ↔ chi-squared link.** For a unit vector `u`, the i.i.d. Gaussian matrix
pushes forward under `A ↦ A.mulVec u` to `gaussianVec k`: the `k` row–vector products are
i.i.d. `N(0,1)`. -/
theorem gaussianMatrix_map_dotProduct {k n : ℕ} (u : Fin n → ℝ) (hu : ∑ j, u j ^ 2 = 1) :
    (gaussianMatrix k n).map (fun A i => ∑ j, A i j * u j) = gaussianVec k := by
  have hAE : AEMeasurable (fun row : Fin n → ℝ => ∑ j, row j * u j) (gaussianVec n) :=
    (by fun_prop : Measurable (fun row : Fin n → ℝ => ∑ j, row j * u j)).aemeasurable
  have hrow := map_dotProduct_gaussianReal u hu
  haveI : IsProbabilityMeasure ((gaussianVec n).map (fun row : Fin n → ℝ => ∑ j, row j * u j)) := by
    rw [hrow]; infer_instance
  have e1 : (Measure.pi (fun _ : Fin k => gaussianVec n)).map
        (fun A i => (fun row : Fin n → ℝ => ∑ j, row j * u j) (A i))
      = Measure.pi (fun _ : Fin k => (gaussianVec n).map (fun row : Fin n → ℝ => ∑ j, row j * u j)) :=
    Measure.pi_map_pi (μ := fun _ : Fin k => gaussianVec n)
      (f := fun _ : Fin k => fun row : Fin n → ℝ => ∑ j, row j * u j) (fun _ => hAE)
  calc (gaussianMatrix k n).map (fun A i => ∑ j, A i j * u j)
      = Measure.pi (fun _ : Fin k => (gaussianVec n).map (fun row : Fin n → ℝ => ∑ j, row j * u j)) :=
        e1
    _ = Measure.pi (fun _ : Fin k => gaussianReal 0 1) := by simp only [hrow]
    _ = gaussianVec k := rfl

/-! ## Projection-level norm-preservation -/

/-- **Distributional norm preservation of the Gaussian projection.** For any fixed nonzero
vector `w`, the squared norm `∑ᵢ (jlMap A w i)²` of its Gaussian projection deviates from
`‖w‖² = ∑ⱼ wⱼ²` by a relative factor `ε` with probability at most
`2·exp(-(ε² - ε³) k / 4)`. This is `jl_norm_preservation` transported to the real
projection via Gaussian rotation invariance. -/
theorem jlMap_concentration {k n : ℕ} (hk : 0 < k) (w : Fin n → ℝ)
    (hw : ∑ j, w j ^ 2 ≠ 0) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (gaussianMatrix k n).real
        {A | ε * (∑ j, w j ^ 2) ≤ |(∑ i, (jlMap k n A w i) ^ 2) - (∑ j, w j ^ 2)|}
      ≤ 2 * rexp (-(ε ^ 2 - ε ^ 3) * (k : ℝ) / 4) := by
  classical
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  set Nw : ℝ := ∑ j, w j ^ 2 with hNw
  have hNwpos : 0 < Nw := lt_of_le_of_ne (by positivity) (Ne.symm hw)
  have hNwne : Nw ≠ 0 := hNwpos.ne'
  set u : Fin n → ℝ := fun j => (Real.sqrt Nw)⁻¹ * w j with hu_def
  have hu : ∑ j, u j ^ 2 = 1 := by
    simp only [hu_def, mul_pow]
    rw [← Finset.mul_sum, inv_pow, Real.sq_sqrt hNwpos.le, ← hNw, inv_mul_cancel₀ hNwne]
  set gmap : (Fin k → Fin n → ℝ) → (Fin k → ℝ) := fun A i => ∑ j, A i j * u j with hgmap
  have hrow_eq : ∀ (A : Fin k → Fin n → ℝ) (i : Fin k),
      gmap A i = (Real.sqrt Nw)⁻¹ * ∑ j, A i j * w j := by
    intro A i
    simp only [hgmap, hu_def, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hkey : ∀ A : Fin k → Fin n → ℝ,
      chiSq k (gmap A) = Nw⁻¹ * ∑ i, (∑ j, A i j * w j) ^ 2 := by
    intro A
    simp only [chiSq, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hrow_eq, mul_pow, inv_pow, Real.sq_sqrt hNwpos.le]
  have hPeq : ∀ A : Fin k → Fin n → ℝ,
      ∑ i, (∑ j, A i j * w j) ^ 2 = (k : ℝ) * ∑ i, (jlMap k n A w i) ^ 2 := by
    intro A
    rw [jlMap_sq_norm]
    field_simp
  have hchidiv : ∀ A : Fin k → Fin n → ℝ,
      chiSq k (gmap A) / (k : ℝ) = Nw⁻¹ * ∑ i, (jlMap k n A w i) ^ 2 := by
    intro A
    rw [hkey, hPeq]
    field_simp
  have hSmeas : MeasurableSet {ω : Fin k → ℝ | ε ≤ |chiSq k ω / (k : ℝ) - 1|} := by
    apply measurableSet_le measurable_const
    have : Measurable (fun ω : Fin k → ℝ => chiSq k ω) := by unfold chiSq; fun_prop
    fun_prop
  have hgmeas : Measurable gmap := by simp only [hgmap]; fun_prop
  have hsetEq : {A : Fin k → Fin n → ℝ | ε * Nw ≤ |(∑ i, (jlMap k n A w i) ^ 2) - Nw|}
      = gmap ⁻¹' {ω : Fin k → ℝ | ε ≤ |chiSq k ω / (k : ℝ) - 1|} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [hchidiv,
      show Nw⁻¹ * (∑ i, (jlMap k n A w i) ^ 2) - 1
          = ((∑ i, (jlMap k n A w i) ^ 2) - Nw) / Nw by field_simp,
      abs_div, abs_of_pos hNwpos, le_div_iff₀ hNwpos]
  have hreal : (gaussianMatrix k n).real
        {A | ε * Nw ≤ |(∑ i, (jlMap k n A w i) ^ 2) - Nw|}
      = (gaussianVec k).real {ω : Fin k → ℝ | ε ≤ |chiSq k ω / (k : ℝ) - 1|} := by
    rw [measureReal_def, measureReal_def, hsetEq, ← Measure.map_apply hgmeas hSmeas]
    simp only [hgmap]
    rw [gaussianMatrix_map_dotProduct u hu]
  rw [hreal]
  exact jl_norm_preservation k hk h0 h1

end JL
