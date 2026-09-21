/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.Sigma
import LeanPool.CoarseGraining.Homogenization.Probability.Source.AKL

/-!
# Regular-to-AKL quotient adapter

This module supplies the one-way bridge from regular coefficient fields with a
fixed a.e. ellipticity bound to the AKL a.e.-quotient carrier.  It deliberately
does not choose representatives in the reverse direction.
-/

namespace Homogenization.Source.AKL

open MeasureTheory

noncomputable section

variable {d : ℕ} {Θ : ℝ}

private instance instSecondCountableTopologyMat : SecondCountableTopology (Mat d) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))

/-- Regular coefficient fields satisfying the fixed a.e. ellipticity bound
required by the AKL quotient carrier. -/
def RegularAKLCarrier (d : ℕ) (Θ : ℝ) : Type _ :=
  {a : RegCoeffField d // ∀ᵐ x ∂volume, IsEllipticMatrix 1 Θ (a x)}
/-- The regular local sigma algebra pulled back to the fixed-contrast subtype. -/
def regularLocalSigma {d : ℕ} {Θ : ℝ} (U : BorelRegion d) :
    MeasurableSpace (RegularAKLCarrier d Θ) :=
  MeasurableSpace.comap Subtype.val (LocalSigmaR U.1)
/-- The regular global sigma algebra pulled back to the fixed-contrast subtype. -/
def regularGlobalSigma (d : ℕ) (Θ : ℝ) : MeasurableSpace (RegularAKLCarrier d Θ) :=
  regularLocalSigma (Θ := Θ) (⟨Set.univ, MeasurableSet.univ⟩ : BorelRegion d)

private theorem aestronglyMeasurable_regularField {d : ℕ} (a : RegCoeffField d) :
    AEStronglyMeasurable (fun x : Vec d => a x) volume := by
  have hmeas : @Measurable (Vec d) (Mat d) _ _ (fun x => a x) :=
    measurable_matrix_of_entries (fun i j => a.entry_measurable i j)
  exact hmeas.aestronglyMeasurable

private theorem ae_elliptic_aeeqFun_mk {d : ℕ} {Θ : ℝ}
    (a : RegularAKLCarrier d Θ) :
    ∀ᵐ x ∂volume, IsEllipticMatrix 1 Θ
      ((AEEqFun.mk (fun x : Vec d => a.1 x)
        (aestronglyMeasurable_regularField a.1)) x) := by
  filter_upwards [a.2,
    AEEqFun.coeFn_mk (fun x : Vec d => a.1 x)
      (aestronglyMeasurable_regularField a.1)] with x hx hmk
  rw [hmk]
  exact hx

/-- The canonical map from a regular a.e.-elliptic field to its AKL quotient
class. -/
def regularToAKL {d : ℕ} {Θ : ℝ} : RegularAKLCarrier d Θ → Carrier d Θ :=
  fun a => ⟨AEEqFun.mk (fun x : Vec d => a.1 x)
    (aestronglyMeasurable_regularField a.1), ae_elliptic_aeeqFun_mk a⟩

/-- The quotient realization agrees almost everywhere with the regular field. -/
theorem regularToAKL_ae_eq {d : ℕ} {Θ : ℝ} (a : RegularAKLCarrier d Θ) :
    (regularToAKL a).1 =ᵐ[volume] fun x => a.1 x :=
  AEEqFun.coeFn_mk _ (aestronglyMeasurable_regularField a.1)

/-- AKL generators on the quotient realization equal the corresponding regular
set integrals. -/
theorem generator_regularToAKL_eq_rawGenerator {d : ℕ} {Θ : ℝ}
    (U : BorelRegion d) (e e' : Vec d) (φ : Vec d → ℝ)
    (a : RegularAKLCarrier d Θ) :
    generator U e e' φ (regularToAKL a) = rawGenerator U e e' φ a.1 := by
  simpa [regularToAKL] using generator_mk_eq_raw U e e' φ (fun x : Vec d => a.1 x)
    (aestronglyMeasurable_regularField a.1) (ae_elliptic_aeeqFun_mk a)

private theorem support_indicator_subset {d : ℕ} (U : Set (Vec d)) (φ : Vec d → ℝ) :
    Function.support (U.indicator φ) ⊆ U := by
  intro x hx
  by_contra hxU
  have hzero : U.indicator φ x = 0 := Set.indicator_of_notMem hxU φ
  exact hx hzero

private theorem rawGenerator_eq_sum_entryTestR_indicator {d : ℕ}
    (U : BorelRegion d) (e e' : Vec d) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcompact : HasCompactSupport φ)
    (a : RegCoeffField d) :
    rawGenerator U e e' φ a =
      ∑ i, ∑ j, (e' i * e j) * entryTestR i j (U.1.indicator φ) a := by
  have hprobe : IsProbeR (U.1.indicator φ) :=
    (IsProbeR.of_smooth hφ hφcompact).indicator U.2
  have hpoint : ∀ x : Vec d,
      U.1.indicator (fun y => vecDot e' (matVecMul (a y) e) * φ y) x =
        ∑ i, ∑ j, (e' i * e j) * (a x i j * U.1.indicator φ x) := by
    intro x
    rw [Set.indicator_mul_right]
    unfold vecDot matVecMul
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold rawGenerator entryTestR
  rw [← integral_indicator U.2]
  rw [show (fun x => U.1.indicator (fun y => vecDot e' (matVecMul (a y) e) * φ y) x) =
      fun x => ∑ i, ∑ j, (e' i * e j) * (a x i j * U.1.indicator φ x) by
        funext x
        exact hpoint x]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
    · intro j _
      exact (integrable_entry_mul_probe i j hprobe a).const_mul (e' i * e j)
  · intro i _
    apply integrable_finsetSum
    intro j _
    exact (integrable_entry_mul_probe i j hprobe a).const_mul (e' i * e j)

/-- AKL integral generators pull back to finite sums of regular entry-test
generators with indicator-localized probes. -/
theorem generator_regularToAKL_eq_sum_entryTestR {d : ℕ} {Θ : ℝ}
    (U : BorelRegion d) (e e' : Vec d) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcompact : HasCompactSupport φ)
    (a : RegularAKLCarrier d Θ) :
    generator U e e' φ (regularToAKL a) =
      ∑ i, ∑ j, (e' i * e j) * entryTestR i j (U.1.indicator φ) a.1 := by
  rw [generator_regularToAKL_eq_rawGenerator]
  exact rawGenerator_eq_sum_entryTestR_indicator U e e' φ hφ hφcompact a.1

private theorem measurable_entryTestR_indicator_regularLocalSigma {d : ℕ} {Θ : ℝ}
    (U : BorelRegion d) (i j : Fin d) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcompact : HasCompactSupport φ) :
    @Measurable (RegularAKLCarrier d Θ) ℝ (regularLocalSigma U) _
      (fun a => entryTestR i j (U.1.indicator φ) a.1) := by
  have hprobe : IsProbeR (U.1.indicator φ) :=
    (IsProbeR.of_smooth hφ hφcompact).indicator U.2
  have hsupport : Function.support (U.1.indicator φ) ⊆ U.1 :=
    support_indicator_subset U.1 φ
  have hentry : @Measurable (RegCoeffField d) ℝ (LocalSigmaR U.1) _
      (entryTestR i j (U.1.indicator φ)) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨i, j, U.1.indicator φ, hprobe, hsupport, t, ht, rfl⟩
  exact hentry.comp (Measurable.of_comap_le le_rfl)

private theorem measurable_sum_entryTestR_indicator_localSigmaR {d : ℕ}
    (U : BorelRegion d) (e e' : Vec d) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcompact : HasCompactSupport φ) :
    @Measurable (RegCoeffField d) ℝ (LocalSigmaR U.1) _
      (fun a => ∑ i, ∑ j, (e' i * e j) * entryTestR i j (U.1.indicator φ) a) := by
  let : MeasurableSpace (RegCoeffField d) := LocalSigmaR U.1
  have hprobe : IsProbeR (U.1.indicator φ) :=
    (IsProbeR.of_smooth hφ hφcompact).indicator U.2
  have hsupport : Function.support (U.1.indicator φ) ⊆ U.1 :=
    support_indicator_subset U.1 φ
  have hentry : ∀ i j : Fin d,
      Measurable (entryTestR i j (U.1.indicator φ)) := by
    intro i j t ht
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨i, j, U.1.indicator φ, hprobe, hsupport, t, ht, rfl⟩
  apply (Finset.measurable_sum (s := Finset.univ) (f := fun i =>
    fun a => ∑ j, (e' i * e j) * entryTestR i j (U.1.indicator φ) a))
  intro i _
  apply (Finset.measurable_sum (s := Finset.univ) (f := fun j =>
    fun a => (e' i * e j) * entryTestR i j (U.1.indicator φ) a))
  intro j _
  exact (hentry i j).const_mul (e' i * e j)

/-- The quotient map is measurable from the regular local sigma algebra to the
AKL local sigma algebra.  This is the valid regular-to-quotient direction. -/
theorem regularToAKL_measurable_local {d : ℕ} {Θ : ℝ}
    (U : BorelRegion d) :
    @Measurable (RegularAKLCarrier d Θ) (Carrier d Θ)
      (regularLocalSigma U) (localSigma U) regularToAKL := by
  change @Measurable (RegularAKLCarrier d Θ) (Carrier d Θ) (regularLocalSigma U)
    (MeasurableSpace.generateFrom
      {s | ∃ (e e' : Vec d) (φ : Vec d → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
        ∃ t : Set ℝ, MeasurableSet t ∧ s = generator U e e' φ ⁻¹' t}) regularToAKL
  let : MeasurableSpace (RegularAKLCarrier d Θ) := regularLocalSigma U
  apply measurable_generateFrom
  rintro s ⟨e, e', φ, hφ, hφcompact, t, ht, rfl⟩
  have hfun : (fun a : RegularAKLCarrier d Θ =>
      generator U e e' φ (regularToAKL a)) =
      fun a => ∑ i, ∑ j, (e' i * e j) * entryTestR i j (U.1.indicator φ) a.1 := by
    funext a
    exact generator_regularToAKL_eq_sum_entryTestR U e e' φ hφ hφcompact a
  change MeasurableSet ((fun a : RegularAKLCarrier d Θ =>
    generator U e e' φ (regularToAKL a)) ⁻¹' t)
  rw [hfun]
  have hsum : Measurable (fun a : RegularAKLCarrier d Θ =>
      ∑ i, ∑ j, (e' i * e j) * entryTestR i j (U.1.indicator φ) a.1) :=
    (measurable_sum_entryTestR_indicator_localSigmaR U e e' φ hφ hφcompact).comp
      (Measurable.of_comap_le le_rfl)
  exact hsum ht

/-- Pulling back AKL local information along `regularToAKL` is no finer than
the regular subtype's pulled-back `LocalSigmaR` structure. -/
theorem comap_localSigma_regularToAKL_le_regularLocalSigma {d : ℕ} {Θ : ℝ}
    (U : BorelRegion d) :
    MeasurableSpace.comap (regularToAKL (d := d) (Θ := Θ)) (localSigma (Θ := Θ) U) ≤
      regularLocalSigma (Θ := Θ) U :=
  (regularToAKL_measurable_local (d := d) (Θ := Θ) U).comap_le

/-- At the whole space, the regular-to-AKL map is measurable into AKL's global
sigma algebra from the corresponding regular global local sigma algebra. -/
theorem regularToAKL_measurable_global {d : ℕ} {Θ : ℝ} :
    @Measurable (RegularAKLCarrier d Θ) (Carrier d Θ)
      (regularGlobalSigma d Θ) (globalSigma d Θ) regularToAKL := by
  simpa [regularGlobalSigma, globalSigma] using!
    (regularToAKL_measurable_local
      (d := d) (Θ := Θ) (⟨Set.univ, MeasurableSet.univ⟩ : BorelRegion d))

end

end Homogenization.Source.AKL
