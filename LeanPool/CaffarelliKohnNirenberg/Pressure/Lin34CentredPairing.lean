/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairing
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredCorrection
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredSource

/-!
# Lin34 Centred Pairing

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

/-!
# The whole-space pairing identity for the centred first pressure potential

`prop:pressure-decomposition` of `paper/ckn.tex` produces, for a suitable weak
solution, the distributional identity pairing the leading potential `p₁` with
`Δψ` against the singly centred nonlinearity `U_ij = -u_i (u_j - c_j)` of
`eq:Uij`.  The oscillation estimate `prop:lin34` runs the same decomposition
with the doubly centred nonlinearity `Û_ij = -(u_i - c_i)(u_j - c_j)` of
`eq:Uhat`.  The two identities differ by the pairing of the correction
`U_ij - Û_ij = -c_i (u_j - c_j)`, which vanishes because `u` is weakly
divergence free and a constant vector field is divergence free.  This file
carries out that correction and produces the identification data consumed by
the Calderón--Zygmund estimate for the centred potential.
-/

/-- The spatial average `⨍_{B_ρ(x₀)} u(·, s)` of `eq:Chat`, seen as a
time-dependent constant vector. -/
def lin34MeanVelocity (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ : ℝ) :
    ℝ → Vec3 :=
  fun s j => MeasureTheory.average (volume.restrict (vec3Ball x₀ ρ))
    (fun z => u (z, s) j)

/-- The mean-free velocity of `eq:Uhat` is the velocity minus its spatial
average. -/
theorem lin34_centredVelocity_apply (u : ParabolicPoint → Vec3) (x₀ : Vec3)
    (ρ s : ℝ) (y : Vec3) (j : Fin 3) :
    lin34CentredVelocity u x₀ ρ ((y, s) : ParabolicPoint) j =
      u (y, s) j - lin34MeanVelocity u x₀ ρ s j := rfl

/-- The singly and doubly centred nonlinearities of `eq:Uij` and `eq:Uhat`
differ by the constant-vector correction `-c_i (u_j - c_j)`. -/
theorem lin34_pressureUTensor_sub_centred (u : ParabolicPoint → Vec3)
    (x₀ : Vec3) (ρ s : ℝ) (y : Vec3) (i j : Fin 3) :
    pressureUTensor u (lin34MeanVelocity u x₀ ρ) ((y, s) : ParabolicPoint) i j -
        pressureUTensor (lin34CentredVelocity u x₀ ρ) 0
          ((y, s) : ParabolicPoint) i j =
      -(lin34MeanVelocity u x₀ ρ s i *
        (u (y, s) j - lin34MeanVelocity u x₀ ρ s j)) := by
  simp only [pressureUTensor, lin34_centredVelocity_apply, Pi.zero_apply,
    sub_zero]
  ring

/-- The centred and singly centred leading potentials differ only through the
three tensor potentials `p₂, p₃, p₄` of `prop:pressure-decomposition`. -/
theorem lin34_centredP1_sub_pressureP1 (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3) (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (s : ℝ) (x : Vec3) :
    lin34CentredP1 u p f x₀ ρ hρ s x -
        pressureP1 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ)
          p f s x =
      (pressureP2 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x +
          pressureP3 (mollifiedBallCutoff x₀ hρ) u
            (lin34MeanVelocity u x₀ ρ) s x +
          pressureP4 (mollifiedBallCutoff x₀ hρ) u
            (lin34MeanVelocity u x₀ ρ) s x) -
        (pressureP2 (mollifiedBallCutoff x₀ hρ)
            (lin34CentredVelocity u x₀ ρ) 0 s x +
          pressureP3 (mollifiedBallCutoff x₀ hρ)
            (lin34CentredVelocity u x₀ ρ) 0 s x +
          pressureP4 (mollifiedBallCutoff x₀ hρ)
            (lin34CentredVelocity u x₀ ρ) 0 s x) := by
  simp only [lin34CentredP1, pressureP1]
  ring

/-! ## Integrability bookkeeping on the support of the cut-off -/

/-- A smooth factor supported in the support of the cut-off turns a slice datum
that is integrable there into a globally integrable function. -/
private lemma lin34_integrable_mul_of_tsupport_subset
    {η T m : Vec3 → ℝ} (hηc : HasCompactSupport η)
    (hT : IntegrableOn T (tsupport η) volume)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hmsub : tsupport m ⊆ tsupport η) :
    Integrable (fun y => T y * m y) volume := by
  have hmc : HasCompactSupport m :=
    HasCompactSupport.of_support_subset_isCompact hηc.isCompact
      (subset_closure.trans hmsub)
  have h := pressureCutoff_integrable_mul_of_tsupport_subset hm.continuous hmc
    hmsub hT
  exact h.congr (Filter.Eventually.of_forall fun y => mul_comm (m y) (T y))

private lemma lin34_tsupport_spatialDeriv {η : Vec3 → ℝ} (i : Fin 3) :
    tsupport (spatialDeriv η i) ⊆ tsupport η :=
  tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := η) (basisVec i)

private lemma lin34_tsupport_mixedSecond {η : Vec3 → ℝ} (i j : Fin 3) :
    tsupport (mixedSecond η i j) ⊆ tsupport η :=
  (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := spatialDeriv η j)
    (basisVec i)).trans (lin34_tsupport_spatialDeriv j)

/-- The tensor pairing of `prop:pressure-decomposition` written as a finite sum
of scalar pairings. -/
private lemma lin34_secondPairing_eq_sum
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {T : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hT : ∀ i j, IntegrableOn (T i j) (tsupport η) volume)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    pressureSecondPairing (fun i j x => η x * T i j x) ψ =
      ∑ i, ∑ j, ∫ x, T i j x * (η x * mixedSecond ψ i j x) := by
  classical
  have hmsub : ∀ i j : Fin 3,
      tsupport (fun x => η x * mixedSecond ψ i j x) ⊆ tsupport η := by
    intro i j
    exact tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)
  have hm : ∀ i j : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => η x * mixedSecond ψ i j x) :=
    fun i j => hη.mul (contDiff_mixedSecond_smooth hψ i j)
  have hint : ∀ i j : Fin 3,
      Integrable (fun x => T i j x * (η x * mixedSecond ψ i j x)) volume :=
    fun i j => lin34_integrable_mul_of_tsupport_subset hηc (hT i j)
      (hm i j) (hmsub i j)
  have hrow : ∀ i : Fin 3, Integrable
      (fun x => ∑ j, T i j x * (η x * mixedSecond ψ i j x)) volume := by
    intro i
    simpa only [Finset.sum_apply] using
      MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _ => hint i j)
  calc
    pressureSecondPairing (fun i j x => η x * T i j x) ψ =
        ∫ x, ∑ i, ∑ j, T i j x * (η x * mixedSecond ψ i j x) := by
      unfold pressureSecondPairing
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro x
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring
    _ = ∑ i, ∫ x, ∑ j, T i j x * (η x * mixedSecond ψ i j x) := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.univ)]
      intro i _
      exact hrow i
    _ = ∑ i, ∑ j, ∫ x, T i j x * (η x * mixedSecond ψ i j x) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [MeasureTheory.integral_finsetSum (s := Finset.univ)]
      intro j _
      exact hint i j

/-- The three tensor potentials of `prop:pressure-decomposition`, paired with
`Δψ`, written as one finite sum over the tensor indices. -/
private lemma lin34_P234_pairing
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {v : ParabolicPoint → Vec3} {d : ℝ → Vec3} {s : ℝ}
    (hT : ∀ i j : Fin 3, IntegrableOn
      (fun y : Vec3 => pressureUTensor v d (y, s) i j) (tsupport η) volume)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => (pressureP2 η v d s x + pressureP3 η v d s x +
        pressureP4 η v d s x) * spatialLaplacian ψ x) volume ∧
    ∫ x, (pressureP2 η v d s x + pressureP3 η v d s x + pressureP4 η v d s x) *
        spatialLaplacian ψ x =
      (∑ i, ∑ j, ∫ y, pressureUTensor v d (y, s) i j *
          (mixedSecond η i j y * ψ y)) +
        (∑ i, ∑ j, ∫ y, pressureUTensor v d (y, s) i j *
          (spatialDeriv η i y * spatialDeriv ψ j y)) +
        (∑ i, ∑ j, ∫ y, pressureUTensor v d (y, s) i j *
          (spatialDeriv η j y * spatialDeriv ψ i y)) := by
  classical
  have hmixed : ∀ i j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (mixedSecond η i j) :=
    fun i j => contDiff_mixedSecond_smooth hη i j
  have hderiv : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i) :=
    fun i => contDiff_spatialDeriv_smooth hη i
  have hmixedC : ∀ i j : Fin 3, HasCompactSupport (mixedSecond η i j) :=
    fun i j => HasCompactSupport.of_support_subset_isCompact hηc.isCompact
      (subset_closure.trans (lin34_tsupport_mixedSecond i j))
  have hderivC : ∀ i : Fin 3, HasCompactSupport (spatialDeriv η i) :=
    fun i => HasCompactSupport.of_support_subset_isCompact hηc.isCompact
      (subset_closure.trans (lin34_tsupport_spatialDeriv i))
  have hInt2 : ∀ i j : Fin 3, Integrable
      (fun y => mixedSecond η i j y * pressureUTensor v d (y, s) i j) volume := by
    intro i j
    have h := lin34_integrable_mul_of_tsupport_subset hηc (hT i j) (hmixed i j)
      (lin34_tsupport_mixedSecond i j)
    exact h.congr (Filter.Eventually.of_forall fun y => mul_comm _ _)
  have hSupp2 : ∀ i j : Fin 3, HasCompactSupport
      (fun y => mixedSecond η i j y * pressureUTensor v d (y, s) i j) :=
    fun i j => (hmixedC i j).mul_right
  have hInt3 : ∀ i j : Fin 3, Integrable
      (fun y => pressureUTensor v d (y, s) i j * spatialDeriv η i y) volume :=
    fun i j => lin34_integrable_mul_of_tsupport_subset hηc (hT i j) (hderiv i)
      (lin34_tsupport_spatialDeriv i)
  have hSupp3 : ∀ i j : Fin 3, HasCompactSupport
      (fun y => pressureUTensor v d (y, s) i j * spatialDeriv η i y) :=
    fun i j => (hderivC i).mul_left
  have hInt4 : ∀ i j : Fin 3, Integrable
      (fun y => pressureUTensor v d (y, s) i j * spatialDeriv η j y) volume :=
    fun i j => lin34_integrable_mul_of_tsupport_subset hηc (hT i j) (hderiv j)
      (lin34_tsupport_spatialDeriv j)
  have hSupp4 : ∀ i j : Fin 3, HasCompactSupport
      (fun y => pressureUTensor v d (y, s) i j * spatialDeriv η j y) :=
    fun i j => (hderivC j).mul_left
  have hlapC : HasCompactSupport (spatialLaplacian ψ) :=
    CKN.Foundation.Heat.laplacian_compact_support_global hψc
  have hlapCont : Continuous (spatialLaplacian ψ) :=
    (contDiff_spatialLaplacian_smooth hψ).continuous
  have hP2int : Integrable
      (fun x => pressureP2 η v d s x * spatialLaplacian ψ x) volume := by
    simpa only [smul_eq_mul] using
      (pressureP2_locallyIntegrable hInt2 hSupp2).integrable_smul_right_of_hasCompactSupport
        hlapCont hlapC
  have hP3int : Integrable
      (fun x => pressureP3 η v d s x * spatialLaplacian ψ x) volume := by
    simpa only [smul_eq_mul] using
      (pressureP3_locallyIntegrable hInt3 hSupp3).integrable_smul_right_of_hasCompactSupport
        hlapCont hlapC
  have hP4int : Integrable
      (fun x => pressureP4 η v d s x * spatialLaplacian ψ x) volume := by
    simpa only [smul_eq_mul] using
      (pressureP4_locallyIntegrable hInt4 hSupp4).integrable_smul_right_of_hasCompactSupport
        hlapCont hlapC
  have h234 : Integrable (fun x => (pressureP2 η v d s x * spatialLaplacian ψ x +
      pressureP3 η v d s x * spatialLaplacian ψ x) +
      pressureP4 η v d s x * spatialLaplacian ψ x) volume :=
    (hP2int.add hP3int).add hP4int
  refine ⟨h234.congr (Filter.Eventually.of_forall fun x => by ring), ?_⟩
  have hsplit : ∫ x, (pressureP2 η v d s x + pressureP3 η v d s x +
        pressureP4 η v d s x) * spatialLaplacian ψ x =
      (∫ x, pressureP2 η v d s x * spatialLaplacian ψ x) +
        (∫ x, pressureP3 η v d s x * spatialLaplacian ψ x) +
        ∫ x, pressureP4 η v d s x * spatialLaplacian ψ x := by
    rw [show (fun x => (pressureP2 η v d s x + pressureP3 η v d s x +
        pressureP4 η v d s x) * spatialLaplacian ψ x) =
      (fun x => (pressureP2 η v d s x * spatialLaplacian ψ x +
        pressureP3 η v d s x * spatialLaplacian ψ x) +
        pressureP4 η v d s x * spatialLaplacian ψ x) by funext x; ring]
    have h23 : Integrable (fun x => pressureP2 η v d s x * spatialLaplacian ψ x +
        pressureP3 η v d s x * spatialLaplacian ψ x) volume := hP2int.add hP3int
    rw [MeasureTheory.integral_add h23 hP4int,
      MeasureTheory.integral_add hP2int hP3int]
  have hpair2 := pressureP2_distributional_pairing hInt2 hSupp2 hψ hψc
  have hpair3 := pressureP3_distributional_pairing hInt3 hSupp3 hψ hψc
  have hpair4 := pressureP4_distributional_pairing hInt4 hSupp4 hψ hψc
  have hre2 : ∀ i j : Fin 3,
      (∫ y, mixedSecond η i j y * pressureUTensor v d (y, s) i j * ψ y) =
        ∫ y, pressureUTensor v d (y, s) i j * (mixedSecond η i j y * ψ y) := by
    intro i j
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y; ring
  have hre3 : ∀ i j : Fin 3,
      (∫ y, pressureUTensor v d (y, s) i j * spatialDeriv η i y *
          spatialDeriv ψ j y) =
        ∫ y, pressureUTensor v d (y, s) i j *
          (spatialDeriv η i y * spatialDeriv ψ j y) := by
    intro i j
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y; ring
  have hre4 : ∀ i j : Fin 3,
      (∫ y, pressureUTensor v d (y, s) i j * spatialDeriv η j y *
          spatialDeriv ψ i y) =
        ∫ y, pressureUTensor v d (y, s) i j *
          (spatialDeriv η j y * spatialDeriv ψ i y) := by
    intro i j
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y; ring
  rw [hsplit, hpair2, hpair3, hpair4]
  simp only [hre2, hre3, hre4]

/-- The Leibniz expansion `eq:leibniz-lap` of the Hessian of `η ψ`, summed
against a tensor that is integrable on the support of `η`. -/
private lemma lin34_hessian_sum_split
    {η ψ : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {T : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hT : ∀ i j : Fin 3, IntegrableOn (T i j) (tsupport η) volume) :
    (∑ i, ∑ j, ∫ y, T i j y * mixedSecond (fun w => η w * ψ w) i j y) =
      ((∑ i, ∑ j, ∫ y, T i j y * (mixedSecond η i j y * ψ y)) +
          (∑ i, ∑ j, ∫ y, T i j y *
            (spatialDeriv η i y * spatialDeriv ψ j y)) +
          (∑ i, ∑ j, ∫ y, T i j y *
            (spatialDeriv η j y * spatialDeriv ψ i y))) +
        ∑ i, ∑ j, ∫ y, T i j y * (η y * mixedSecond ψ i j y) := by
  classical
  have hmA : ∀ i j : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun y => mixedSecond η i j y * ψ y) :=
    fun i j => (contDiff_mixedSecond_smooth hη i j).mul hψ
  have hmB : ∀ i j : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
      (fun y => spatialDeriv η i y * spatialDeriv ψ j y) :=
    fun i j => (contDiff_spatialDeriv_smooth hη i).mul
      (contDiff_spatialDeriv_smooth hψ j)
  have hmC : ∀ i j : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
      (fun y => spatialDeriv η j y * spatialDeriv ψ i y) :=
    fun i j => (contDiff_spatialDeriv_smooth hη j).mul
      (contDiff_spatialDeriv_smooth hψ i)
  have hmD : ∀ i j : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun y => η y * mixedSecond ψ i j y) :=
    fun i j => hη.mul (contDiff_mixedSecond_smooth hψ i j)
  have hsA : ∀ i j : Fin 3,
      tsupport (fun y => mixedSecond η i j y * ψ y) ⊆ tsupport η :=
    fun i j => (tsupport_mul_subset_left (f := mixedSecond η i j)
      (g := ψ)).trans (lin34_tsupport_mixedSecond i j)
  have hsB : ∀ i j : Fin 3,
      tsupport (fun y => spatialDeriv η i y * spatialDeriv ψ j y) ⊆
        tsupport η :=
    fun i j => (tsupport_mul_subset_left (f := spatialDeriv η i)
      (g := spatialDeriv ψ j)).trans (lin34_tsupport_spatialDeriv i)
  have hsC : ∀ i j : Fin 3,
      tsupport (fun y => spatialDeriv η j y * spatialDeriv ψ i y) ⊆
        tsupport η :=
    fun i j => (tsupport_mul_subset_left (f := spatialDeriv η j)
      (g := spatialDeriv ψ i)).trans (lin34_tsupport_spatialDeriv j)
  have hsD : ∀ i j : Fin 3,
      tsupport (fun y => η y * mixedSecond ψ i j y) ⊆ tsupport η :=
    fun i j => tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)
  have hIA : ∀ i j : Fin 3, Integrable
      (fun y => T i j y * (mixedSecond η i j y * ψ y)) volume :=
    fun i j => lin34_integrable_mul_of_tsupport_subset hηc (hT i j)
      (hmA i j) (hsA i j)
  have hIB : ∀ i j : Fin 3, Integrable
      (fun y => T i j y * (spatialDeriv η i y * spatialDeriv ψ j y)) volume :=
    fun i j => lin34_integrable_mul_of_tsupport_subset hηc (hT i j)
      (hmB i j) (hsB i j)
  have hIC : ∀ i j : Fin 3, Integrable
      (fun y => T i j y * (spatialDeriv η j y * spatialDeriv ψ i y)) volume :=
    fun i j => lin34_integrable_mul_of_tsupport_subset hηc (hT i j)
      (hmC i j) (hsC i j)
  have hID : ∀ i j : Fin 3, Integrable
      (fun y => T i j y * (η y * mixedSecond ψ i j y)) volume :=
    fun i j => lin34_integrable_mul_of_tsupport_subset hηc (hT i j)
      (hmD i j) (hsD i j)
  have hterm : ∀ i j : Fin 3,
      (∫ y, T i j y * mixedSecond (fun w => η w * ψ w) i j y) =
        (∫ y, T i j y * (mixedSecond η i j y * ψ y)) +
          (∫ y, T i j y * (spatialDeriv η i y * spatialDeriv ψ j y)) +
          (∫ y, T i j y * (spatialDeriv η j y * spatialDeriv ψ i y)) +
          ∫ y, T i j y * (η y * mixedSecond ψ i j y) := by
    intro i j
    have hpt : ∀ y : Vec3, T i j y * mixedSecond (fun w => η w * ψ w) i j y =
        T i j y * (mixedSecond η i j y * ψ y) +
          T i j y * (spatialDeriv η i y * spatialDeriv ψ j y) +
          T i j y * (spatialDeriv η j y * spatialDeriv ψ i y) +
          T i j y * (η y * mixedSecond ψ i j y) := by
      intro y
      rw [spatialSecondDeriv_mul_smooth hη hψ i j y]
      ring
    have hAB : Integrable (fun y => T i j y * (mixedSecond η i j y * ψ y) +
        T i j y * (spatialDeriv η i y * spatialDeriv ψ j y)) volume :=
      (hIA i j).add (hIB i j)
    have hABC : Integrable (fun y => T i j y * (mixedSecond η i j y * ψ y) +
        T i j y * (spatialDeriv η i y * spatialDeriv ψ j y) +
        T i j y * (spatialDeriv η j y * spatialDeriv ψ i y)) volume :=
      hAB.add (hIC i j)
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_add hABC (hID i j),
      MeasureTheory.integral_add hAB (hIC i j),
      MeasureTheory.integral_add (hIA i j) (hIB i j)]
  simp only [hterm]
  simp [Finset.sum_add_distrib]

/-- **The whole-space pairing identity for the centred potential at one time
slice.**  The singly centred identity of `prop:pressure-decomposition` is
corrected by the constant-vector pairing, which vanishes by the weak
divergence-free condition; what remains is the identity for the doubly centred
nonlinearity `eq:Uhat`, which is the form `ext:CZ` consumes. -/
theorem lin34_centredP1_pairing_of_slice_data
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ}
    {Ω' : Set Vec3} (hηΩ' : tsupport (mollifiedBallCutoff x₀ hρ) ⊆ Ω')
    (hU : ∀ i j : Fin 3, IntegrableOn
      (fun y : Vec3 => pressureUTensor u (lin34MeanVelocity u x₀ ρ) ((y, s) : ParabolicPoint) i j)
      (tsupport (mollifiedBallCutoff x₀ hρ)) volume)
    (hUhat : ∀ i j : Fin 3, IntegrableOn
      (fun y : Vec3 => pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i
        j)
      (tsupport (mollifiedBallCutoff x₀ hρ)) volume)
    (hum : ∀ j : Fin 3, IntegrableOn (fun y : Vec3 => u (y, s) j) Ω' volume)
    (hdivΩ' : ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω' →
      ∫ x in Ω', ∑ i, u (x, s) i * (fderiv ℝ φ x) (basisVec i) = 0)
    (hP1 : ∀ χ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      Integrable (fun x => pressureP1 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) p f
        s x *
        spatialLaplacian χ x) volume →
      ∫ x, pressureP1 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) p f s x *
        spatialLaplacian χ x =
        pressureSecondPairing (fun i j x => (mollifiedBallCutoff x₀ hρ) x *
          pressureUTensor u (lin34MeanVelocity u x₀ ρ) ((x, s) : ParabolicPoint) i j) χ)
    (hP1Int : ∀ χ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      Integrable (fun x => pressureP1 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) p f
        s x *
        spatialLaplacian χ x) volume)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => lin34CentredP1 u p f x₀ ρ hρ s x *
        spatialLaplacian ψ x) volume ∧
      ∫ x, lin34CentredP1 u p f x₀ ρ hρ s x * spatialLaplacian ψ x =
        pressureSecondPairing (lin34CentredSource u x₀ hρ s) ψ := by
  classical
  have hη : ContDiff ℝ (⊤ : ℕ∞) (mollifiedBallCutoff x₀ hρ) := mollifiedBallCutoff_smooth x₀ hρ
  have hηc : HasCompactSupport (mollifiedBallCutoff x₀ hρ) :=
    mollifiedBallCutoff_hasCompactSupport x₀ hρ
  obtain ⟨hIntU, hAU⟩ := lin34_P234_pairing hη hηc hU hψ hψc
  obtain ⟨hIntH, hAH⟩ := lin34_P234_pairing hη hηc hUhat hψ hψc
  have hsplitU := lin34_hessian_sum_split (T := fun i j y => pressureUTensor u (lin34MeanVelocity
    u x₀ ρ) ((y, s) : ParabolicPoint) i j) hη hηc hψ hU
  have hsplitH := lin34_hessian_sum_split (T := fun i j y => pressureUTensor (lin34CentredVelocity
    u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j) hη hηc hψ hUhat
  have hSDU := lin34_secondPairing_eq_sum (T := fun i j y => pressureUTensor u (lin34MeanVelocity
    u x₀ ρ) ((y, s) : ParabolicPoint) i j) hη hηc hU hψ
  have hSDH := lin34_secondPairing_eq_sum (T := fun i j y => pressureUTensor (lin34CentredVelocity
    u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j) hη hηc hUhat hψ
  -- the correction pairing vanishes
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) := hη.mul hψ
  have hFc : HasCompactSupport (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) := hηc.mul_right (f'
    := ψ)
  have hFη : tsupport (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) ⊆ tsupport (mollifiedBallCutoff
    x₀ hρ) :=
    tsupport_mul_subset_left (f := mollifiedBallCutoff x₀ hρ) (g := ψ)
  have hFΩ : tsupport (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) ⊆ Ω' := hFη.trans hηΩ'
  have hint : ∀ j : Fin 3, IntegrableOn (fun x : Vec3 => u (x, s) j)
      (tsupport (fun y => mollifiedBallCutoff x₀ hρ y * ψ y)) volume := fun j => (hum j).mono_set
        hFΩ
  have hdivF : ∀ i : Fin 3,
      ∫ x in Ω', ∑ j, u (x, s) j * mixedSecond (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) j i x
        = 0 := by
    intro i
    have hφ := contDiff_spatialDeriv_smooth hF i
    have hφc : HasCompactSupport (spatialDeriv (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) i) :=
      hFc.fderiv_apply (𝕜 := ℝ) (basisVec i)
    have hφΩ : tsupport (spatialDeriv (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) i) ⊆ Ω' :=
      (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hFΩ
    have h := hdivΩ' _ hφ hφc hφΩ
    simpa only [mixedSecond, spatialDeriv] using h
  have hzero := lin34_constant_hessian_pairing_zero
    (b := lin34MeanVelocity u x₀ ρ s) hF hFc hFΩ hint hdivF
  -- the two Hessian pairings agree
  have hmc : ∀ i j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (mixedSecond (fun y => mollifiedBallCutoff x₀ hρ y
    * ψ y) i j) :=
    fun i j => contDiff_mixedSecond_smooth hF i j
  have hmsub : ∀ i j : Fin 3, tsupport (mixedSecond (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) i
    j) ⊆
      tsupport (mollifiedBallCutoff x₀ hρ) := fun i j => (lin34_tsupport_mixedSecond i j).trans hFη
  have hUm : ∀ i j : Fin 3, Integrable (fun y =>
      pressureUTensor u (lin34MeanVelocity u x₀ ρ) ((y, s) : ParabolicPoint) i j *
        mixedSecond (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) i j y) volume :=
    fun i j => lin34_integrable_mul_of_tsupport_subset hηc (hU i j) (hmc i j)
      (hmsub i j)
  have hUhm : ∀ i j : Fin 3, Integrable (fun y =>
      pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j *
        mixedSecond (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) i j y) volume :=
    fun i j => lin34_integrable_mul_of_tsupport_subset hηc (hUhat i j) (hmc i j)
      (hmsub i j)
  have hdiffInt : ∀ i j : Fin 3,
      (∫ y, pressureUTensor u (lin34MeanVelocity u x₀ ρ) ((y, s) : ParabolicPoint) i j *
          mixedSecond (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) i j y) -
        (∫ y, pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j *
          mixedSecond (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) i j y) =
      -(∫ y, (lin34MeanVelocity u x₀ ρ) s i * (u (y, s) j - (lin34MeanVelocity u x₀ ρ) s j) *
        mixedSecond (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) i j y) := by
    intro i j
    rw [← MeasureTheory.integral_sub (hUm i j) (hUhm i j),
      ← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    dsimp only
    rw [← sub_mul, lin34_pressureUTensor_sub_centred u x₀ ρ s y i j]
    ring
  have hsumeq : (∑ i, ∑ j, ∫ y,
        pressureUTensor u (lin34MeanVelocity u x₀ ρ) ((y, s) : ParabolicPoint) i j *
          mixedSecond (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) i j y) =
      ∑ i, ∑ j, ∫ y, pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j *
        mixedSecond (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) i j y := by
    have hcancel : (∑ i, ∑ j, ((∫ y,
          pressureUTensor u (lin34MeanVelocity u x₀ ρ) ((y, s) : ParabolicPoint) i j *
            mixedSecond (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) i j y) -
          ∫ y, pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j *
            mixedSecond (fun y => mollifiedBallCutoff x₀ hρ y * ψ y) i j y)) = 0 := by
      simp only [hdiffInt]
      simp only [Finset.sum_neg_distrib, hzero, neg_zero]
    simp only [Finset.sum_sub_distrib] at hcancel
    linarith only [hcancel]
  -- the pressure difference
  have hdiffI : Integrable (fun x => (pressureP2 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity
    u x₀ ρ) s x + pressureP3 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x +
    pressureP4 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x) * spatialLaplacian ψ
    x -
      (pressureP2 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x + pressureP3
        (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x + pressureP4
        (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x) * spatialLaplacian ψ x)
        volume := hIntU.sub hIntH
  have hpt : ∀ x : Vec3, lin34CentredP1 u p f x₀ ρ hρ s x *
        spatialLaplacian ψ x =
      pressureP1 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) p f s x *
        spatialLaplacian ψ x +
        ((pressureP2 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x + pressureP3
          (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x + pressureP4
          (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x) * spatialLaplacian ψ x -
          (pressureP2 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x + pressureP3
          (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x + pressureP4
          (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x) * spatialLaplacian ψ x)
          := by
    intro x
    have hx : lin34CentredP1 u p f x₀ ρ hρ s x =
        pressureP1 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) p f s x + ((pressureP2
          (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x + pressureP3
          (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x + pressureP4
          (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x) - (pressureP2
          (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x + pressureP3
          (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x + pressureP4
          (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x)) := by
      linarith only [lin34_centredP1_sub_pressureP1 u p f x₀ hρ s x]
    rw [hx]
    ring
  have hsumI : Integrable (fun x =>
      pressureP1 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) p f s x *
        spatialLaplacian ψ x +
        ((pressureP2 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x + pressureP3
          (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x + pressureP4
          (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x) * spatialLaplacian ψ x -
          (pressureP2 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x + pressureP3
          (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x + pressureP4
          (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x) * spatialLaplacian ψ x))
      volume := (hP1Int ψ hψ hψc).add hdiffI
  have hcI : Integrable (fun x => lin34CentredP1 u p f x₀ ρ hρ s x *
      spatialLaplacian ψ x) volume :=
    hsumI.congr (Filter.Eventually.of_forall fun x => (hpt x).symm)
  refine ⟨hcI, ?_⟩
  have hintval : (∫ x, lin34CentredP1 u p f x₀ ρ hρ s x *
        spatialLaplacian ψ x) =
      (∫ x, pressureP1 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) p f s x *
        spatialLaplacian ψ x) +
        ((∫ x, (pressureP2 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x +
          pressureP3 (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x + pressureP4
          (mollifiedBallCutoff x₀ hρ) u (lin34MeanVelocity u x₀ ρ) s x) * spatialLaplacian ψ x) -
          ∫ x, (pressureP2 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x +
            pressureP3 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x +
            pressureP4 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x) *
            spatialLaplacian ψ x) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_add (hP1Int ψ hψ hψc) hdiffI,
      MeasureTheory.integral_sub hIntU hIntH]
  have hsource : pressureSecondPairing (lin34CentredSource u x₀ hρ s) ψ =
      ∑ i, ∑ j, ∫ y, pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j *
        ((mollifiedBallCutoff x₀ hρ) y * mixedSecond ψ i j y) := hSDH
  have hP1val := hP1 ψ hψ hψc (hP1Int ψ hψ hψc)
  rw [← hSDU, ← hAU] at hsplitU
  rw [← hsource, ← hAH] at hsplitH
  rw [hintval, hP1val]
  linarith only [hsplitU, hsplitH, hsumeq]

end CKN
