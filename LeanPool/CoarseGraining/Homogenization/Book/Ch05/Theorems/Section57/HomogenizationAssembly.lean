/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.EllipticityFromMinimalScale
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.HomogenizationBlackBoxes

/-! # Homogenization Assembly -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal MatrixOrder

/-!
# First assembly tools for the public quenched homogenization theorem

This file begins Phase 4 of the public theorem plan.  The first result upgrades
the parent-cube finite-`q` homogenization-error estimate to the Ch3
depth-localized quantity `coarseGrainingHomogenizationErrorAtDepth`.
-/

noncomputable section

/-- The scalar constant-coefficient package used by the Ch3 deterministic
homogenization theorem. -/
def scalarConstantCoeffMatrix {d : ℕ} (σ : ℝ) (hσ : 0 < σ) :
    Ch03.ConstantCoeffMatrix d where
  matrix := scalarMatrix (d := d) σ
  isSymm := scalarMatrix_isSymm σ
  lam := σ
  Lam := σ
  lam_pos := hσ
  lam_le_Lam := le_rfl
  elliptic := isEllipticMatrix_scalarMatrix hσ

theorem scalarConstantCoeffMatrix_matrix
    {d : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    (scalarConstantCoeffMatrix (d := d) σ hσ).matrix =
      scalarMatrix (d := d) σ := rfl

theorem scalarConstantCoeffMatrix_isPositiveScalarMatrix
    {d : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    IsPositiveScalarMatrix
      (scalarConstantCoeffMatrix (d := d) σ hσ).matrix := by
  exact ⟨σ, hσ, rfl⟩

theorem sqrt_rpow_neg_div_mono_of_le
    {A X Y α : ℝ} (hA : 0 < A) (hX : 0 < X) (hY : 0 < Y)
    (hXY : X ≤ Y) (hα : 0 < α) :
    Real.sqrt ((A / X) ^ (-α)) ≤ Real.sqrt ((A / Y) ^ (-α)) := by
  exact Real.sqrt_le_sqrt
    (rpow_neg_div_mono_of_le hA hX hY hXY hα)

/-- Combine two already-collapsed random scales without making the stochastic
prefactor depend on the law. -/
theorem isBigO_gammaSigma_max_two_expLogSq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {η C₁ C₂ θ : ℝ} (hη : 0 < η) (hθ : 0 < θ)
    {X₁ X₂ : Ω → ℝ}
    (hX₁ : IsBigO μ (gammaSigma η) X₁
      (Real.exp (C₁ * (Real.log (2 + θ)) ^ (2 : ℕ))))
    (hX₂ : IsBigO μ (gammaSigma η) X₂
      (Real.exp (C₂ * (Real.log (2 + θ)) ^ (2 : ℕ)))) :
    let C : ℝ :=
      4 * max 0 (Real.log ((3 * Real.log (2 : ℝ)) ^ η⁻¹)) + max C₁ C₂
    IsBigO μ (gammaSigma η) (fun ω => max (X₁ ω) (X₂ ω))
      (Real.exp (C * (Real.log (2 + θ)) ^ (2 : ℕ))) := by
  dsimp only
  let Ksup : ℝ := (3 * Real.log (2 : ℝ)) ^ η⁻¹
  let L2 : ℝ := (Real.log (2 + θ)) ^ (2 : ℕ)
  let Ck : ℝ := 4 * max 0 (Real.log Ksup)
  let A₁ : ℝ := Real.exp (C₁ * L2)
  let A₂ : ℝ := Real.exp (C₂ * L2)
  have hKsup_pos : 0 < Ksup := by
    dsimp [Ksup]
    exact Real.rpow_pos_of_pos
      (mul_pos (by norm_num : (0 : ℝ) < 3)
        (Real.log_pos (by norm_num : (1 : ℝ) < 2))) _
  have hraw :
      IsBigO μ (gammaSigma η) (fun ω => max (X₁ ω) (X₂ ω))
        (Ksup * max A₁ A₂) := by
    simpa [Ksup, A₁, A₂, L2] using
      isBigO_gammaSigma_max_two_of_scales
        (μ := μ) (η := η) (AJ := A₁) (AU := A₂)
        hη hX₁ hX₂
  have hscale :
      Ksup * max A₁ A₂ ≤
        Real.exp ((Ck + max C₁ C₂) * L2) := by
    have hL2_nonneg : 0 ≤ L2 := by dsimp [L2]; positivity
    have hA₁_le : A₁ ≤ Real.exp ((max C₁ C₂) * L2) := by
      refine Real.exp_le_exp.mpr ?_
      exact mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hL2_nonneg
    have hA₂_le : A₂ ≤ Real.exp ((max C₁ C₂) * L2) := by
      refine Real.exp_le_exp.mpr ?_
      exact mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hL2_nonneg
    have hmax_le : max A₁ A₂ ≤ Real.exp ((max C₁ C₂) * L2) :=
      max_le hA₁_le hA₂_le
    have hK_le : Ksup ≤ Real.exp (Ck * L2) := by
      have hrawK :=
        const_mul_rpow_max_one_le_exp_logSq
          (A := Ksup) (θ := θ) (p := (0 : ℝ))
          hKsup_pos hθ.le (by norm_num)
      simpa [Ksup, Ck, L2] using hrawK
    calc
      Ksup * max A₁ A₂
          ≤ Ksup * Real.exp ((max C₁ C₂) * L2) :=
            mul_le_mul_of_nonneg_left hmax_le hKsup_pos.le
      _ ≤ Real.exp (Ck * L2) * Real.exp ((max C₁ C₂) * L2) :=
            mul_le_mul_of_nonneg_right hK_le (Real.exp_pos _).le
      _ = Real.exp ((Ck + max C₁ C₂) * L2) := by
            rw [← Real.exp_add]
            ring_nf
  exact IsBigO.mono_scale (μ := μ) (Ψ := gammaSigma η) hraw hscale

/-- A depth-`j` Ch3 homogenization-error envelope is controlled by the parent
cube's Ch2 `q = 1` homogenization error with the expected geometric depth
weight. -/
theorem coarseGrainingHomogenizationErrorAtDepth_le_depthWeight_mul_parent
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (a0 : Ch03.ConstantCoeffMatrix d) {s : ℝ} (hs : 0 < s) (j : ℕ) :
    Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 s j ≤
      Ch03.coarseGrainingDepthWeight s j *
        Ch02.HomogenizationErrorOnCube Q s
          Ch02.MultiscaleExponent.infinity (.finite 1) a a0.matrix := by
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hD : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty Q j
  refine Ch02.finsetSupReal_le D hD ?_
  intro R hR
  have hRdepth : R ∈ descendantsAtDepth Q j := by
    simpa [D] using hR
  let k : ℤ := Q.scale - (j : ℤ)
  have hRscale : R ∈ descendantsAtScale Q k := by
    simpa [k] using
      mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hRdepth
  have hfactor :
      Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) =
        Ch03.coarseGrainingDepthWeight s j := by
    have htoNat : Int.toNat (Q.scale - k) = j := by
      dsimp [k]
      have hsub : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by ring
      rw [hsub, Int.toNat_natCast]
    simp [Ch03.coarseGrainingDepthWeight, htoNat]
  have h :=
    Ch02.homogenizationErrorOnCube_infinity_one_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) a a0.matrix hs hRscale
  calc
    Ch02.HomogenizationErrorOnCube R s Ch02.MultiscaleExponent.infinity
        (.finite 1) a a0.matrix
        ≤ Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
            Ch02.HomogenizationErrorOnCube Q s
              Ch02.MultiscaleExponent.infinity (.finite 1) a a0.matrix :=
          h
    _ = Ch03.coarseGrainingDepthWeight s j *
            Ch02.HomogenizationErrorOnCube Q s
              Ch02.MultiscaleExponent.infinity (.finite 1) a a0.matrix := by
          rw [hfactor]

/-- Finite-`sigma` control of the Ch3 depth-localized homogenization-error
quantity above the same collapsed minimal-scale envelope. -/
theorem exists_coarseGrainingHomogenizationErrorAtDepth_interpolated_expLogSq
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ α : ℝ, 0 < α ∧
      ∀ {σ τ r : ℝ}, 0 < σ →
        max params.sUpper params.sLower < τ / 2 →
        α < τ / 2 →
        τ ≤ 1 →
        0 ≤ r →
        0 < r - τ / 2 →
        let ηJ : ℝ := finiteQuenchedTailExponent d σ τ
        let ηU : ℝ := finiteQuenchedTailExponent d σ (τ / 2)
        let η : ℝ := min ηJ ηU
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ᵐ aω ∂P,
                  ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω)
                    {m j : ℕ},
                    X aω ≤ (3 : ℝ) ^ m →
                    let F : Ch02.TriadicCoeffFamily d :=
                      Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
                        aω ha;
                    let σ0 : ℝ := barSigmaLimit hP hStruct;
                    let hσ0 : 0 < σ0 := hΓ.barSigmaLimit_pos;
                    let a0 : Ch03.ConstantCoeffMatrix d :=
                      scalarConstantCoeffMatrix σ0 hσ0;
                    let Cresp : ℝ :=
                      Real.sqrt
                        (4 * (Fintype.card (BlockCoord d) : ℝ) *
                          (Fintype.card (NormalizedProbeIndex d) : ℝ));
                    let Cneg : ℝ :=
                      (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
                        (2 * Real.sqrt
                          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)));
                    let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2);
                    let G : ℝ :=
                      Real.rpow
                        (Ch02.geometricDiscount r 1 *
                          (Ch02.geometricDiscount (r - τ / 2) 1)⁻¹)
                        (1 / (1 : ℝ));
                    Ch03.coarseGrainingHomogenizationErrorAtDepth
                        (originCube d ((m : ℕ) : ℤ)) F a0 r j ≤
                      Ch03.coarseGrainingDepthWeight r j *
                        (G * A *
                          Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α))) := by
  obtain ⟨α, hα_pos, _hαmax, hEbase⟩ :=
    exists_homogenizationErrorOnOriginCube_interpolated_expLogSq
      (d := d) params
  refine ⟨α, hα_pos, ?_⟩
  intro σ τ r hσ_pos hτ_half hατ_half hτ_le_one hr_nonneg hδ_pos
  dsimp only
  have hrq : 0 ≤ r * (1 : ℝ) := by simpa using hr_nonneg
  have hδq : 0 < (r - τ / 2) * (1 : ℝ) := by simpa using hδ_pos
  obtain ⟨Cscale, hCscale_pos, hlaw⟩ :=
    hEbase (σ := σ) (τ := τ) (r := r) (q := 1)
      hσ_pos hτ_half hατ_half hτ_le_one hrq hδq
      (by norm_num : (0 : ℝ) < 1)
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  obtain ⟨X, hXbigO, hXone, hEae⟩ :=
    hlaw hP hStruct hΓ hσ_eq hparams
  refine ⟨X, hXbigO, hXone, ?_⟩
  have hτ2_pos : 0 < τ / 2 :=
    (max_sUpper_sLower_pos params).trans hτ_half
  have hr_pos : 0 < r := by nlinarith
  filter_upwards [hEae] with aω hEpoint
  intro ha m j hXm
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField aω ha
  let σ0 : ℝ := barSigmaLimit hP hStruct
  let hσ0 : 0 < σ0 := hΓ.barSigmaLimit_pos
  let a0 : Ch03.ConstantCoeffMatrix d := scalarConstantCoeffMatrix σ0 hσ0
  let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ)
  let Cresp : ℝ :=
    Real.sqrt
      (4 * (Fintype.card (BlockCoord d) : ℝ) *
        (Fintype.card (NormalizedProbeIndex d) : ℝ))
  let Cneg : ℝ :=
    (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
      (2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)))
  let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2)
  let G : ℝ :=
    Real.rpow
      (Ch02.geometricDiscount r 1 *
        (Ch02.geometricDiscount (r - τ / 2) 1)⁻¹)
      (1 / (1 : ℝ))
  let R : ℝ := Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α))
  have hparent :
      Ch02.HomogenizationErrorOnCube Q r Ch02.MultiscaleExponent.infinity
          (.finite 1) F a0.matrix ≤ G * A * R := by
    simpa [Q, F, σ0, hσ0, a0, Cresp, Cneg, A, G, R,
      scalarConstantCoeffMatrix_matrix] using
      hEpoint ha (m := m) hXm
  have hdepth :=
    coarseGrainingHomogenizationErrorAtDepth_le_depthWeight_mul_parent
      (Q := Q) (a := F) (a0 := a0) (s := r) hr_pos j
  have hweight_nonneg : 0 ≤ Ch03.coarseGrainingDepthWeight r j := by
    dsimp [Ch03.coarseGrainingDepthWeight]
    positivity
  calc
    Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r j
        ≤ Ch03.coarseGrainingDepthWeight r j *
            Ch02.HomogenizationErrorOnCube Q r
              Ch02.MultiscaleExponent.infinity (.finite 1) F a0.matrix :=
          hdepth
    _ ≤ Ch03.coarseGrainingDepthWeight r j * (G * A * R) :=
          mul_le_mul_of_nonneg_left hparent hweight_nonneg

/-- The random coefficient family attached to an a.e. uniformly elliptic
coefficient field. -/
abbrev assemblyCoeffFamily {d : ℕ} (aω : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField aω) :
    Ch02.TriadicCoeffFamily d :=
  Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField aω ha

abbrev assemblyOriginCube (d : ℕ) (m : ℕ) : TriadicCube d :=
  originCube d ((m : ℕ) : ℤ)

/-- The scalar homogenized matrix used in the Ch3 comparison datum, with the
background scalar passed explicitly.  This is the sigma-agnostic Ch3 assembly
surface; finite-`sigma` and endpoint hypotheses only have to supply the scalar
and its positivity. -/
def assemblyConstantCoeffMatrixOfScalar {d : ℕ} [NeZero d]
    (σ0 : ℝ) (hσ0 : 0 < σ0) :
    Ch03.ConstantCoeffMatrix d :=
  scalarConstantCoeffMatrix σ0 hσ0

abbrev assemblyComparisonDatumOfScalar {d : ℕ} [NeZero d]
    (σ0 : ℝ) (hσ0 : 0 < σ0)
    (aω : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField aω)
    (m : ℕ) (g : Vec d → Vec d) : Type _ :=
  Ch03.CoarseGrainingComparisonDatum
    (assemblyOriginCube d m) (assemblyCoeffFamily aω ha)
    (assemblyConstantCoeffMatrixOfScalar σ0 hσ0) g

/-- Finite-`sigma` wrapper for the scalar homogenized matrix. -/
def assemblyConstantCoeffMatrix {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    Ch03.ConstantCoeffMatrix d :=
  assemblyConstantCoeffMatrixOfScalar (barSigmaLimit hP hStruct)
    hΓ.barSigmaLimit_pos

abbrev assemblyComparisonDatum {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (aω : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField aω)
    (m : ℕ) (g : Vec d → Vec d) : Type _ :=
  assemblyComparisonDatumOfScalar
    (barSigmaLimit hP hStruct) hΓ.barSigmaLimit_pos aω ha m g

noncomputable def assemblyResponseConstant (d : ℕ) : ℝ :=
  Real.sqrt
    (4 * (Fintype.card (BlockCoord d) : ℝ) *
      (Fintype.card (NormalizedProbeIndex d) : ℝ))

noncomputable def assemblyNegativeConstant (d : ℕ) (τ : ℝ) : ℝ :=
  (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
    (2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)))

noncomputable def assemblyAmplitude (d : ℕ) (τ : ℝ) : ℝ :=
  max (assemblyResponseConstant d) (assemblyNegativeConstant d τ) *
    Real.rpow (3 : ℝ) (τ / 2)

noncomputable def assemblyMinimalScaleDecay {d : ℕ}
    (α : ℝ) (X : RegCoeffField d → ℝ) (aω : RegCoeffField d) (m : ℕ) : ℝ :=
  Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α))

noncomputable def assemblyErrorDiscount (τ r : ℝ) : ℝ :=
  Real.rpow
    (Ch02.geometricDiscount r 1 *
      (Ch02.geometricDiscount (r - τ / 2) 1)⁻¹)
    (1 / (1 : ℝ))

noncomputable def assemblyEllipticityDiscount (τ r : ℝ) : ℝ :=
  Real.rpow
    (Ch02.geometricDiscount (r / 2) 2 *
      (Ch02.geometricDiscount (r / 2 - τ / 2) 2)⁻¹)
    (1 / 2 : ℝ)

noncomputable def assemblyErrorEnvelope {d : ℕ}
    (α τ r : ℝ) (X : RegCoeffField d → ℝ) (aω : RegCoeffField d)
    (m : ℕ) : ℝ :=
  assemblyErrorDiscount τ r * assemblyAmplitude d τ *
    assemblyMinimalScaleDecay α X aω m

noncomputable def assemblyEllipticityErrorEnvelope {d : ℕ}
    (α τ r : ℝ) (X : RegCoeffField d → ℝ) (aω : RegCoeffField d)
    (m : ℕ) : ℝ :=
  assemblyEllipticityDiscount τ r * assemblyAmplitude d τ *
    assemblyMinimalScaleDecay α X aω m

noncomputable def assemblyEllipticityEnvelope {d : ℕ}
    (α τ r : ℝ) (X : RegCoeffField d → ℝ) (aω : RegCoeffField d)
    (m : ℕ) : ℝ :=
  2 * (Fintype.card (Fin d) : ℝ) *
    ((assemblyEllipticityErrorEnvelope (d := d) α τ r X aω m) ^ (2 : ℕ) + 1)

/-- The controlled-factor conclusion used by the Phase 4 assembly theorem,
with the scalar background passed explicitly. -/
def assemblyControlledFactorsConclusionOfScalar {d : ℕ} [NeZero d]
    (σ0 : ℝ) (hσ0 : 0 < σ0)
    (Ccg α τ s r : ℝ) (X : RegCoeffField d → ℝ)
    (aω : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField aω)
    (m j : ℕ) (g : Vec d → Vec d)
    (w : assemblyComparisonDatumOfScalar σ0 hσ0 aω ha m g) : Prop :=
  let Q : TriadicCube d := assemblyOriginCube d m
  let F : Ch02.TriadicCoeffFamily d := assemblyCoeffFamily aω ha
  let a0 : Ch03.ConstantCoeffMatrix d :=
    assemblyConstantCoeffMatrixOfScalar σ0 hσ0
  let B₁ : ℝ := assemblyErrorEnvelope (d := d) α τ r X aω m
  let M : ℝ := assemblyEllipticityEnvelope (d := d) α τ r X aω m
  Ch03.homogenizationComparisonNegativeBesovLHS Q F a0 s w.u w.v ≤
      Ch03.generalCoarseGrainingL2TwoExponentRHS Ccg Q F a0 s r r j g w.u ∧
    Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r j ≤
      Ch03.coarseGrainingDepthWeight r j * B₁ ∧
    max (σ0⁻¹ * Ch02.LambdaSq Q (r / 2) (.finite 2) F)
        (σ0 * (Ch02.lambdaSq Q (r / 2) (.finite 2) F)⁻¹) ≤ M ∧
    (Ch02.lambdaSq Q (r / 2) (.finite 2) F)⁻¹ ≤ σ0⁻¹ * M ∧
    Real.sqrt (Ch02.LambdaSq Q (r / 2) (.finite 2) F) *
        Real.sqrt ((Ch02.lambdaSq Q (r / 2) (.finite 2) F)⁻¹) ≤ M

/-- Finite-`sigma` wrapper for the controlled-factor conclusion. -/
def assemblyControlledFactorsConclusion {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (Ccg α τ s r : ℝ) (X : RegCoeffField d → ℝ)
    (aω : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField aω)
    (m j : ℕ) (g : Vec d → Vec d)
    (w : assemblyComparisonDatum hP hStruct hΓ aω ha m g) : Prop :=
  assemblyControlledFactorsConclusionOfScalar
    (barSigmaLimit hP hStruct) hΓ.barSigmaLimit_pos
    Ccg α τ s r X aω ha m j g w

/-- Two-exponent controlled-factor conclusion for the repaired Ch3
coarse-graining estimate.  The response quantities are still localized at
exponent `r`, while the forcing is measured at the stronger exponent `r₂`. -/
def assemblyControlledFactorsTwoExponentConclusionOfScalar {d : ℕ} [NeZero d]
    (σ0 : ℝ) (hσ0 : 0 < σ0)
    (Ccg α τ s r r₂ : ℝ) (X : RegCoeffField d → ℝ)
    (aω : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField aω)
    (m j : ℕ) (g : Vec d → Vec d)
    (w : assemblyComparisonDatumOfScalar σ0 hσ0 aω ha m g) : Prop :=
  let Q : TriadicCube d := assemblyOriginCube d m
  let F : Ch02.TriadicCoeffFamily d := assemblyCoeffFamily aω ha
  let a0 : Ch03.ConstantCoeffMatrix d :=
    assemblyConstantCoeffMatrixOfScalar σ0 hσ0
  let B₁ : ℝ := assemblyErrorEnvelope (d := d) α τ r X aω m
  let M : ℝ := assemblyEllipticityEnvelope (d := d) α τ r X aω m
  Ch03.homogenizationComparisonNegativeBesovLHS Q F a0 s w.u w.v ≤
      Ch03.generalCoarseGrainingL2TwoExponentRHS Ccg Q F a0 s r r₂ j g w.u ∧
    Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r j ≤
      Ch03.coarseGrainingDepthWeight r j * B₁ ∧
    max (σ0⁻¹ * Ch02.LambdaSq Q (r / 2) (.finite 2) F)
        (σ0 * (Ch02.lambdaSq Q (r / 2) (.finite 2) F)⁻¹) ≤ M ∧
    (Ch02.lambdaSq Q (r / 2) (.finite 2) F)⁻¹ ≤ σ0⁻¹ * M ∧
    Real.sqrt (Ch02.LambdaSq Q (r / 2) (.finite 2) F) *
        Real.sqrt ((Ch02.lambdaSq Q (r / 2) (.finite 2) F)⁻¹) ≤ M

/-- Finite-`sigma` wrapper for the repaired two-exponent controlled-factor
conclusion. -/
def assemblyControlledFactorsTwoExponentConclusion {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (Ccg α τ s r r₂ : ℝ) (X : RegCoeffField d → ℝ)
    (aω : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField aω)
    (m j : ℕ) (g : Vec d → Vec d)
    (w : assemblyComparisonDatum hP hStruct hΓ aω ha m g) : Prop :=
  assemblyControlledFactorsTwoExponentConclusionOfScalar
    (barSigmaLimit hP hStruct) hΓ.barSigmaLimit_pos
    Ccg α τ s r r₂ X aω ha m j g w

/-- Finite-`sigma` assembly of the Ch3 comparison theorem with the collapsed
minimal-scale controls needed to bound every random coefficient in its RHS.

This is the internal Phase 4 handoff: one random scale `X` controls both the
depth-localized `q = 1` homogenization error and the `q = 2` ellipticity
factors appearing in the deterministic Ch3 theorem. -/
theorem exists_homogenizationComparison_controlledFactors_interpolated_expLogSq
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccg α : ℝ, 0 < Ccg ∧ 0 < α ∧
      α < max params.sUpper params.sLower ∧
      ∀ {σ τ s r : ℝ}, 0 < σ →
        max params.sUpper params.sLower < τ / 2 →
        α < τ / 2 →
        τ ≤ 1 →
        0 < s →
        0 < r →
        r < s / 2 →
        s < 1 →
        τ < r →
        let ηJ : ℝ := finiteQuenchedTailExponent d σ τ
        let ηU : ℝ := finiteQuenchedTailExponent d σ (τ / 2)
        let η : ℝ := min ηJ ηU
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ᵐ aω ∂P,
                  ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω)
                    {m j : ℕ} {g : Vec d → Vec d},
                    (w : assemblyComparisonDatum hP hStruct hΓ aω ha m g) →
                    X aω ≤ (3 : ℝ) ^ m →
                    Ch03.ForceBesovRegularity (assemblyOriginCube d m) r g →
                    assemblyControlledFactorsConclusion
                      hP hStruct hΓ Ccg α τ s r X aω ha m j g w := by
  obtain ⟨Ccg, hCcg_pos, hCcg⟩ :=
    (Ch03.generalCoarseGrainingL2TwoExponentTheory d).exists_constant
  obtain ⟨α, hα_pos, hαmax, hEbase⟩ :=
    exists_homogenizationErrorOnOriginCube_interpolated_expLogSq
      (d := d) params
  refine ⟨Ccg, α, hCcg_pos, hα_pos, hαmax, ?_⟩
  intro σ τ s r hσ_pos hτ_half hατ_half hτ_le_one hs_pos hr_pos
    hrs hs_lt_one hτr
  dsimp only
  have hτ2_pos : 0 < τ / 2 :=
    (max_sUpper_sLower_pos params).trans hτ_half
  have hτ_pos : 0 < τ := by linarith
  have hηJ_pos : 0 < finiteQuenchedTailExponent d σ τ :=
    finiteQuenchedTailExponent_pos (d := d) (σ := σ) (t := τ)
      hσ_pos hτ_pos
  have hηU_pos : 0 < finiteQuenchedTailExponent d σ (τ / 2) :=
    finiteQuenchedTailExponent_pos (d := d) (σ := σ) (t := τ / 2)
      hσ_pos hτ2_pos
  have hη_pos :
      0 < min (finiteQuenchedTailExponent d σ τ)
        (finiteQuenchedTailExponent d σ (τ / 2)) :=
    lt_min hηJ_pos hηU_pos
  have hrq₁ : 0 ≤ r * (1 : ℝ) := by nlinarith
  have hδq₁ : 0 < (r - τ / 2) * (1 : ℝ) := by nlinarith
  have hrq₂ : 0 ≤ (r / 2) * (2 : ℝ) := by nlinarith
  have hδq₂ : 0 < (r / 2 - τ / 2) * (2 : ℝ) := by nlinarith
  obtain ⟨C₁, hC₁_pos, hLaw₁⟩ :=
    hEbase (σ := σ) (τ := τ) (r := r) (q := 1)
      hσ_pos hτ_half hατ_half hτ_le_one hrq₁ hδq₁
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨C₂, hC₂_pos, hLaw₂⟩ :=
    hEbase (σ := σ) (τ := τ) (r := r / 2) (q := 2)
      hσ_pos hτ_half hατ_half hτ_le_one hrq₂ hδq₂
      (by norm_num : (0 : ℝ) < 2)
  let Cscale : ℝ :=
    4 * max 0
      (Real.log
        ((3 * Real.log (2 : ℝ)) ^
          (min (finiteQuenchedTailExponent d σ τ)
            (finiteQuenchedTailExponent d σ (τ / 2)))⁻¹)) +
      max C₁ C₂
  have hCscale_pos : 0 < Cscale := by
    dsimp [Cscale]
    have hnonneg :
        0 ≤ 4 * max 0
          (Real.log
            ((3 * Real.log (2 : ℝ)) ^
              (min (finiteQuenchedTailExponent d σ τ)
                (finiteQuenchedTailExponent d σ (τ / 2)))⁻¹)) := by
      positivity
    have hmax_pos : 0 < max C₁ C₂ := hC₁_pos.trans_le (le_max_left C₁ C₂)
    nlinarith
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  let : IsProbabilityMeasure P := hP.isProbability
  obtain ⟨X₁, hX₁O, hX₁_one, hX₁ae⟩ :=
    hLaw₁ hP hStruct hΓ hσ_eq hparams
  obtain ⟨X₂, hX₂O, hX₂_one, hX₂ae⟩ :=
    hLaw₂ hP hStruct hΓ hσ_eq hparams
  let X : RegCoeffField d → ℝ := fun aω => max (X₁ aω) (X₂ aω)
  have hXO :
      IsBigO P
        (gammaSigma
          (min (finiteQuenchedTailExponent d σ τ)
            (finiteQuenchedTailExponent d σ (τ / 2))))
        X
        (Real.exp
          (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) := by
    simpa [X, Cscale] using
      isBigO_gammaSigma_max_two_expLogSq
        (μ := P)
        (η := min (finiteQuenchedTailExponent d σ τ)
          (finiteQuenchedTailExponent d σ (τ / 2)))
        (C₁ := C₁) (C₂ := C₂) (θ := hΓ.thetaHat)
        hη_pos hΓ.thetaHat_pos hX₁O hX₂O
  refine ⟨X, hXO, ?_, ?_⟩
  · intro aω
    dsimp [X]
    exact (hX₁_one aω).trans (le_max_left _ _)
  filter_upwards [hX₁ae, hX₂ae] with aω hX₁point hX₂point
  intro ha m j g
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField aω ha
  let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ)
  let σ0 : ℝ := barSigmaLimit hP hStruct
  let hσ0 : 0 < σ0 := hΓ.barSigmaLimit_pos
  let a0 : Ch03.ConstantCoeffMatrix d := scalarConstantCoeffMatrix σ0 hσ0
  intro w hXm hg
  let Cresp : ℝ :=
    Real.sqrt
      (4 * (Fintype.card (BlockCoord d) : ℝ) *
        (Fintype.card (NormalizedProbeIndex d) : ℝ))
  let Cneg : ℝ :=
    (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
      (2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)))
  let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2)
  let R : ℝ := Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α))
  let G₁ : ℝ :=
    Real.rpow
      (Ch02.geometricDiscount r 1 *
        (Ch02.geometricDiscount (r - τ / 2) 1)⁻¹)
      (1 / (1 : ℝ))
  let G₂ : ℝ :=
    Real.rpow
      (Ch02.geometricDiscount (r / 2) 2 *
        (Ch02.geometricDiscount (r / 2 - τ / 2) 2)⁻¹)
      (1 / 2 : ℝ)
  let B₁ : ℝ := G₁ * A * R
  let B₂ : ℝ := G₂ * A * R
  let M : ℝ := 2 * (Fintype.card (Fin d) : ℝ) * (B₂ ^ (2 : ℕ) + 1)
  have hX₁_le_X : X₁ aω ≤ X aω := by
    dsimp [X]
    exact le_max_left _ _
  have hX₂_le_X : X₂ aω ≤ X aω := by
    dsimp [X]
    exact le_max_right _ _
  have hX₁m : X₁ aω ≤ (3 : ℝ) ^ m := hX₁_le_X.trans hXm
  have hX₂m : X₂ aω ≤ (3 : ℝ) ^ m := hX₂_le_X.trans hXm
  have hX₁_pos : 0 < X₁ aω :=
    lt_of_lt_of_le zero_lt_one (hX₁_one aω)
  have hX₂_pos : 0 < X₂ aω :=
    lt_of_lt_of_le zero_lt_one (hX₂_one aω)
  have hX_pos : 0 < X aω :=
    lt_of_lt_of_le hX₁_pos hX₁_le_X
  have hpowm_pos : 0 < (3 : ℝ) ^ m := by positivity
  have hR₁_le_R :
      Real.sqrt (((3 : ℝ) ^ m / X₁ aω) ^ (-α)) ≤ R := by
    dsimp [R]
    exact sqrt_rpow_neg_div_mono_of_le
      hpowm_pos hX₁_pos hX_pos hX₁_le_X hα_pos
  have hR₂_le_R :
      Real.sqrt (((3 : ℝ) ^ m / X₂ aω) ^ (-α)) ≤ R := by
    dsimp [R]
    exact sqrt_rpow_neg_div_mono_of_le
      hpowm_pos hX₂_pos hX_pos hX₂_le_X hα_pos
  have hdisc_r_nonneg : 0 ≤ Ch02.geometricDiscount r 1 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_nonneg hrq₁
  have hdisc_delta₁_pos : 0 < Ch02.geometricDiscount (r - τ / 2) 1 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_pos hδq₁
  have hG₁_nonneg : 0 ≤ G₁ := by
    dsimp [G₁]
    exact Real.rpow_nonneg
      (mul_nonneg hdisc_r_nonneg
        (inv_nonneg.mpr hdisc_delta₁_pos.le)) _
  have hdisc_r₂_nonneg : 0 ≤ Ch02.geometricDiscount (r / 2) 2 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_nonneg hrq₂
  have hdisc_delta₂_pos :
      0 < Ch02.geometricDiscount (r / 2 - τ / 2) 2 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_pos hδq₂
  have hG₂_nonneg : 0 ≤ G₂ := by
    dsimp [G₂]
    exact Real.rpow_nonneg
      (mul_nonneg hdisc_r₂_nonneg
        (inv_nonneg.mpr hdisc_delta₂_pos.le)) _
  have hdisc_tau_pos : 0 < Ch02.geometricDiscount (τ / 2) 1 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_pos
        (by nlinarith : 0 < (τ / 2) * (1 : ℝ))
  have hCresp_nonneg : 0 ≤ Cresp := by
    dsimp [Cresp]
    positivity
  have hCneg_nonneg : 0 ≤ Cneg := by
    dsimp [Cneg]
    exact mul_nonneg (inv_nonneg.mpr hdisc_tau_pos.le) (by positivity)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (hCresp_nonneg.trans (le_max_left Cresp Cneg))
      (by positivity)
  have hB₁_nonneg : 0 ≤ B₁ := by
    dsimp [B₁]
    exact mul_nonneg (mul_nonneg hG₁_nonneg hA_nonneg) (Real.sqrt_nonneg _)
  have hB₂_nonneg : 0 ≤ B₂ := by
    dsimp [B₂]
    exact mul_nonneg (mul_nonneg hG₂_nonneg hA_nonneg) (Real.sqrt_nonneg _)
  have hcomparison :
      Ch03.homogenizationComparisonNegativeBesovLHS Q F a0 s w.u w.v ≤
        Ch03.generalCoarseGrainingL2TwoExponentRHS
          Ccg Q F a0 s r r j g w.u := by
    exact
      hCcg (Q := Q) (a := F) (a0 := a0) (s := s) (r := r)
        (r₂ := r) (j := j) (g := g)
        (scalarConstantCoeffMatrix_isPositiveScalarMatrix hσ0) w
        hs_pos hr_pos hrs hs_lt_one le_rfl hg
  have hparent₁ :
      Ch02.HomogenizationErrorOnCube Q r
          Ch02.MultiscaleExponent.infinity (.finite 1) F a0.matrix ≤ B₁ := by
    have hraw :=
      hX₁point ha (m := m) hX₁m
    have hraw' :
        Ch02.HomogenizationErrorOnCube Q r
            Ch02.MultiscaleExponent.infinity (.finite 1) F a0.matrix ≤
          G₁ * A *
            Real.sqrt (((3 : ℝ) ^ m / X₁ aω) ^ (-α)) := by
      simpa [Q, F, σ0, hσ0, a0, Cresp, Cneg, A, G₁,
        scalarConstantCoeffMatrix_matrix] using hraw
    calc
      Ch02.HomogenizationErrorOnCube Q r
          Ch02.MultiscaleExponent.infinity (.finite 1) F a0.matrix
          ≤ G₁ * A *
              Real.sqrt (((3 : ℝ) ^ m / X₁ aω) ^ (-α)) := hraw'
      _ ≤ G₁ * A * R := by
          exact mul_le_mul_of_nonneg_left hR₁_le_R
            (mul_nonneg hG₁_nonneg hA_nonneg)
      _ = B₁ := rfl
  have hdepth_base :=
    coarseGrainingHomogenizationErrorAtDepth_le_depthWeight_mul_parent
      (Q := Q) (a := F) (a0 := a0) (s := r) hr_pos j
  have hdepth_weight_nonneg : 0 ≤ Ch03.coarseGrainingDepthWeight r j := by
    dsimp [Ch03.coarseGrainingDepthWeight]
    positivity
  have hdepth :
      Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r j ≤
        Ch03.coarseGrainingDepthWeight r j * B₁ := by
    calc
      Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r j
          ≤ Ch03.coarseGrainingDepthWeight r j *
              Ch02.HomogenizationErrorOnCube Q r
                Ch02.MultiscaleExponent.infinity (.finite 1) F a0.matrix :=
            hdepth_base
      _ ≤ Ch03.coarseGrainingDepthWeight r j * B₁ :=
            mul_le_mul_of_nonneg_left hparent₁ hdepth_weight_nonneg
  have hparent₂ :
      Ch02.HomogenizationErrorOnCube Q (r / 2)
          Ch02.MultiscaleExponent.infinity (.finite 2) F
          (scalarMatrix (d := d) σ0) ≤ B₂ := by
    have hraw :=
      hX₂point ha (m := m) hX₂m
    have hraw' :
        Ch02.HomogenizationErrorOnCube Q (r / 2)
            Ch02.MultiscaleExponent.infinity (.finite 2) F
            (scalarMatrix (d := d) σ0) ≤
          G₂ * A *
            Real.sqrt (((3 : ℝ) ^ m / X₂ aω) ^ (-α)) := by
      simpa [Q, F, σ0, Cresp, Cneg, A, G₂] using hraw
    calc
      Ch02.HomogenizationErrorOnCube Q (r / 2)
          Ch02.MultiscaleExponent.infinity (.finite 2) F
          (scalarMatrix (d := d) σ0)
          ≤ G₂ * A *
              Real.sqrt (((3 : ℝ) ^ m / X₂ aω) ^ (-α)) := hraw'
      _ ≤ G₂ * A * R := by
          exact mul_le_mul_of_nonneg_left hR₂_le_R
            (mul_nonneg hG₂_nonneg hA_nonneg)
      _ = B₂ := rfl
  have hr_half_pos : 0 < r / 2 := half_pos hr_pos
  have hweighted :
      max (σ0⁻¹ * Ch02.LambdaSq Q (r / 2) (.finite 2) F)
          (σ0 * (Ch02.lambdaSq Q (r / 2) (.finite 2) F)⁻¹) ≤ M := by
    simpa [M, B₂] using
      weightedEllipticity_finite_two_le_of_homogenizationError_bound
        (Q := Q) (a := F) (s := r / 2) (σ := σ0) (B := B₂)
        hr_half_pos hσ0 hparent₂
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hlambda_inv :
      (Ch02.lambdaSq Q (r / 2) (.finite 2) F)⁻¹ ≤ σ0⁻¹ * M := by
    exact
      lambdaSq_inv_le_inv_sigma_mul_of_weightedEllipticity_le
        (Q := Q) (a := F) (s := r / 2) (σ := σ0) (M := M)
        hσ0 hweighted
  have hsqrt_product :
      Real.sqrt (Ch02.LambdaSq Q (r / 2) (.finite 2) F) *
          Real.sqrt ((Ch02.lambdaSq Q (r / 2) (.finite 2) F)⁻¹) ≤ M := by
    exact
      sqrt_LambdaSq_mul_sqrt_lambdaSq_inv_le_of_weightedEllipticity_le
        (Q := Q) (a := F) (s := r / 2) (σ := σ0) (M := M)
        hr_half_pos hσ0 hM_nonneg hweighted
  exact ⟨hcomparison, hdepth, hweighted, hlambda_inv, hsqrt_product⟩

/-- Finite-`sigma` two-exponent assembly of the repaired Ch3 comparison
theorem.  The stochastic scale and local coefficient controls are inherited
from the one-exponent controlled-factor package; only the Ch3 comparison
conjunct is replaced by the scale-separated theorem. -/
theorem exists_homogenizationComparison_controlledFactors_twoExponent_interpolated_expLogSq
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccg α : ℝ, 0 < Ccg ∧ 0 < α ∧
      α < max params.sUpper params.sLower ∧
      ∀ {σ τ s r r₂ : ℝ}, 0 < σ →
        max params.sUpper params.sLower < τ / 2 →
        α < τ / 2 →
        τ ≤ 1 →
        0 < s →
        0 < r →
        r < s / 2 →
        s < 1 →
        τ < r →
        r ≤ r₂ →
        let ηJ : ℝ := finiteQuenchedTailExponent d σ τ
        let ηU : ℝ := finiteQuenchedTailExponent d σ (τ / 2)
        let η : ℝ := min ηJ ηU
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ᵐ aω ∂P,
                  ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω)
                    {m j : ℕ} {g : Vec d → Vec d},
                    (w : assemblyComparisonDatum hP hStruct hΓ aω ha m g) →
                    X aω ≤ (3 : ℝ) ^ m →
                    Ch03.ForceBesovRegularity (assemblyOriginCube d m) r₂ g →
                    assemblyControlledFactorsTwoExponentConclusion
                      hP hStruct hΓ Ccg α τ s r r₂ X aω ha m j g w := by
  obtain ⟨Ccg, hCcg_pos, hCcg⟩ :=
    (Ch03.generalCoarseGrainingL2TwoExponentTheory d).exists_constant
  obtain ⟨_, α, _, hα_pos, hαmax, hcontrolled⟩ :=
    exists_homogenizationComparison_controlledFactors_interpolated_expLogSq
      (d := d) params
  refine ⟨Ccg, α, hCcg_pos, hα_pos, hαmax, ?_⟩
  intro σ τ s r r₂ hσ_pos hτ_half hατ_half hτ_le_one hs_pos hr_pos
    hrs hs_lt_one hτr hr₂
  dsimp only
  obtain ⟨Cscale, hCscale, hlaw⟩ :=
    hcontrolled hσ_pos hτ_half hατ_half hτ_le_one hs_pos hr_pos
      hrs hs_lt_one hτr
  refine ⟨Cscale, hCscale, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  obtain ⟨X, hXO, hXone, hAE⟩ :=
    hlaw hP hStruct hΓ hσ_eq hparams
  refine ⟨X, hXO, hXone, ?_⟩
  filter_upwards [hAE] with aω hpoint
  intro ha m j g w hXm hg₂
  let Q : TriadicCube d := assemblyOriginCube d m
  let F : Ch02.TriadicCoeffFamily d := assemblyCoeffFamily aω ha
  let a0 : Ch03.ConstantCoeffMatrix d :=
    assemblyConstantCoeffMatrix hP hStruct hΓ
  have hg₁ : Ch03.ForceBesovRegularity Q r g := by
    dsimp [Q]
    exact hg₂.of_exponent_le hr₂
  have hlegacy :
      assemblyControlledFactorsConclusion
        hP hStruct hΓ _ α τ s r X aω ha m j g w :=
    hpoint ha w hXm (by simpa [Q] using hg₁)
  have hcomparison :
      Ch03.homogenizationComparisonNegativeBesovLHS Q F a0 s w.u w.v ≤
        Ch03.generalCoarseGrainingL2TwoExponentRHS
          Ccg Q F a0 s r r₂ j g w.u := by
    exact
      hCcg (Q := Q) (a := F) (a0 := a0) (s := s) (r := r)
        (r₂ := r₂) (j := j) (g := g)
        (by
          dsimp [a0, assemblyConstantCoeffMatrix,
            assemblyConstantCoeffMatrixOfScalar]
          exact scalarConstantCoeffMatrix_isPositiveScalarMatrix
            hΓ.barSigmaLimit_pos)
        w hs_pos hr_pos hrs hs_lt_one hr₂ hg₂
  dsimp [assemblyControlledFactorsTwoExponentConclusion,
    assemblyControlledFactorsTwoExponentConclusionOfScalar, Q, F, a0]
  dsimp [assemblyControlledFactorsConclusion,
    assemblyControlledFactorsConclusionOfScalar, Q, F, a0] at hlegacy
  rcases hlegacy with ⟨_, hdepth, hweighted, hlambda_inv, hsqrt_product⟩
  exact ⟨hcomparison, hdepth, hweighted, hlambda_inv, hsqrt_product⟩

end

end Section57
end Ch05
end Book
end Homogenization
