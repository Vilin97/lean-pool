/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.CoordinateIntegration
public import LeanPool.Odlyzko.Theta.FourierCharacters

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Module MeasureTheory Set

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*} [Fintype ι]

/-- A coordinate fourier character used in the Odlyzko-bound argument. -/
noncomputable def coordinateFourierCharacter
    (n : ι → ℤ) (x : ι → ℝ) : ℂ :=
  UnitAddTorus.mFourier (-n) (torusQuotientMap x)

private theorem continuous_coordinateFourierCharacter (n : ι → ℤ) :
    Continuous (coordinateFourierCharacter n) := by
  unfold coordinateFourierCharacter
  exact (UnitAddTorus.mFourier (-n)).continuous.comp
    (continuous_pi fun i ↦
      continuous_quotient_mk'.comp (continuous_apply i))

theorem measurableSet_pi_Ioc {κ : Type*} [Finite κ] :
    MeasurableSet {x : κ → ℝ | ∀ i, x i ∈ Ioc 0 1} := by
  letI := Fintype.ofFinite κ
  rw [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have hi : Measurable (fun x : κ → ℝ ↦ x i) := measurable_pi_apply i
  exact measurableSet_Ioc.preimage hi

@[simp]
theorem norm_coordinateFourierCharacter
    (n : ι → ℤ) (x : ι → ℝ) :
    ‖coordinateFourierCharacter n x‖ = 1 :=
  norm_mFourier_torusQuotientMap (-n) x

/-- A coordinate fourier gaussian used in the Odlyzko-bound argument. -/
noncomputable def coordinateFourierGaussian
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n : ι → ℤ) (x : ι → ℝ) : ℂ :=
  coordinateFourierCharacter n x * coordinateGaussian L b a x

/-- A coordinate fourier gaussian translate used in the Odlyzko-bound argument. -/
noncomputable def coordinateFourierGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n k : ι → ℤ)
    (x : ι → ℝ) : ℂ :=
  coordinateFourierCharacter n x * coordinateGaussianTranslate L b a k x

theorem continuous_coordinateFourierGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n k : ι → ℤ) :
    Continuous (coordinateFourierGaussianTranslate L b a n k) := by
  classical
  exact (continuous_coordinateFourierCharacter n).mul
    (coordinateGaussianTranslate L b a k).continuous

private theorem coordinateFourierCharacter_add_intPi
    (n k : ι → ℤ) (x : ι → ℝ) :
    coordinateFourierCharacter n ((fun i ↦ (k i : ℝ)) + x) =
      coordinateFourierCharacter n x := by
  unfold coordinateFourierCharacter
  congr 1
  rw [add_comm]
  exact torusQuotientMap_add_intPi x k

theorem coordinateFourierGaussian_add_intPi
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n k : ι → ℤ) (x : ι → ℝ) :
    coordinateFourierGaussian L b a n
        ((fun i ↦ (k i : ℝ)) + x) =
      coordinateFourierGaussianTranslate L b a n k x := by
  classical
  rw [coordinateFourierGaussian,
    coordinateFourierGaussianTranslate,
    coordinateFourierCharacter_add_intPi]
  congr 1
  exact congrArg (coordinateGaussian L b a) (add_comm _ _)

theorem summable_integral_norm_coordinateFourierGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ) :
    Summable (fun k : ι → ℤ ↦
      ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
        ‖coordinateFourierGaussianTranslate L b a n k x‖) := by
  classical
  let S : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc 0 1}
  let K : TopologicalSpace.Compacts (ι → ℝ) :=
    ⟨Icc (0 : ι → ℝ) 1, isCompact_Icc⟩
  have hSK : S ⊆ K := by
    intro x hx
    exact ⟨fun i ↦ (hx i).1.le, fun i ↦ (hx i).2⟩
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_pi_Ioc
  have hKsum :=
    summable_norm_restrict_coordinateGaussianTranslate L b ha K
  have hmeasure : volume S < (⊤ : ENNReal) :=
    lt_of_le_of_lt (measure_mono hSK) K.2.measure_lt_top
  have hbound (k : ι → ℤ) :
      ∫ x in S,
          ‖coordinateFourierGaussianTranslate L b a n k x‖ ≤
        volume.real S *
          ‖(coordinateGaussianTranslate L b a k).restrict K‖ := by
    have hInt :
        IntegrableOn
          (fun x ↦ ‖coordinateFourierGaussianTranslate L b a n k x‖)
          S := by
      exact ((continuous_coordinateFourierGaussianTranslate
        L b a n k).norm.integrableOn_Icc).mono_set hSK
    have hConst :
        IntegrableOn (fun _ : ι → ℝ ↦
          ‖(coordinateGaussianTranslate L b a k).restrict K‖) S :=
      integrableOn_const (ne_of_lt hmeasure)
    calc
      ∫ x in S,
          ‖coordinateFourierGaussianTranslate L b a n k x‖ ≤
          ∫ _x in S,
            ‖(coordinateGaussianTranslate L b a k).restrict K‖ := by
        apply integral_mono_ae hInt hConst
        filter_upwards [ae_restrict_mem hS] with x hx
        rw [coordinateFourierGaussianTranslate, norm_mul,
          norm_coordinateFourierCharacter, one_mul]
        exact ContinuousMap.norm_coe_le_norm
          ((coordinateGaussianTranslate L b a k).restrict K) ⟨x, hSK hx⟩
      _ = volume.real S *
          ‖(coordinateGaussianTranslate L b a k).restrict K‖ := by simp
  apply Summable.of_nonneg_of_le
      (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) hbound
  exact hKsum.mul_left (volume.real S)

theorem integral_tsum_coordinateFourierGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ) :
    ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
        ∑' k : ι → ℤ,
          coordinateFourierGaussianTranslate L b a n k x =
      ∑' k : ι → ℤ,
        ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
          coordinateFourierGaussianTranslate L b a n k x := by
  classical
  symm
  apply integral_tsum_of_summable_integral_norm
  · intro k
    let S : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc 0 1}
    let K : Set (ι → ℝ) := Icc 0 1
    have hSK : S ⊆ K := fun x hx ↦
      ⟨fun i ↦ (hx i).1.le, fun i ↦ (hx i).2⟩
    exact ((continuous_coordinateFourierGaussianTranslate
      L b a n k).integrableOn_Icc).mono_set hSK
  · exact summable_integral_norm_coordinateFourierGaussianTranslate
      L b ha n

theorem mFourierCoeff_gaussianTorusPeriodization
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ)
    (hint : Integrable (coordinateFourierGaussian L b a n)) :
    UnitAddTorus.mFourierCoeff
        (gaussianTorusPeriodization L b a ha) n =
      ∫ x, coordinateFourierGaussian L b a n x := by
  classical
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ n 0]
  simp only [Pi.zero_apply, zero_add]
  have hpoint (x : ι → ℝ) :
      UnitAddTorus.mFourier (-n) (torusQuotientMap x) •
          gaussianTorusPeriodization L b a ha
            (torusQuotientMap x) =
        ∑' k : ι → ℤ,
          coordinateFourierGaussianTranslate L b a n k x := by
    rw [gaussianTorusPeriodization,
      torusPeriodization_apply_quotient]
    unfold intPeriodization coordinateFourierGaussianTranslate
      coordinateFourierCharacter
    rw [smul_eq_mul, tsum_mul_left]
    rfl
  change
    (∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
      UnitAddTorus.mFourier (-n) (torusQuotientMap x) •
        gaussianTorusPeriodization L b a ha (torusQuotientMap x)) =
      ∫ x, coordinateFourierGaussian L b a n x
  simp_rw [hpoint]
  rw [integral_tsum_coordinateFourierGaussianTranslate L b ha n]
  rw [integral_eq_tsum_integral_pi_Ioc
    (coordinateFourierGaussian L b a n) hint]
  apply tsum_congr
  intro k
  apply setIntegral_congr_fun measurableSet_pi_Ioc
  intro x hx
  exact (coordinateFourierGaussian_add_intPi L b a n k x).symm

end NumberField.Odlyzko
