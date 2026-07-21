/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.MonotonicityEuclidean

/-!
# Center translations

This module starts the passage from the origin-centered theorem to arbitrary
centers by isolating the translation identities needed for `weakTheta`.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Translate a scalar field by a domain point. -/
def translateScalar {n : ℕ} (a : Domain n) (f : Domain n → ℝ) : Domain n → ℝ :=
  fun x => f (a + x)

/-- Translate a weak gradient field by a domain point. -/
def translateGradient {n m : ℕ}
    (a : Domain n) (Du : Domain n → Gradient n m) : Domain n → Gradient n m :=
  fun x => Du (a + x)

/-- Translate a domain set to coordinates centered at `a`. -/
def centeredDomain {n : ℕ} (a : Domain n) (Ω : Set (Domain n)) : Set (Domain n) :=
  {x | a + x ∈ Ω}

/-- Move a test vector field from coordinates centered at `a` back to the
original coordinates. -/
def translateVectorFieldToOriginal {n : ℕ} (a : Domain n) (X : Domain n → Domain n) :
    Domain n → Domain n :=
  fun y => X (y - a)

/-- Move a target-valued test map from coordinates centered at `a` back to the
original coordinates. -/
def translateTargetTestToOriginal {n m : ℕ}
    (a : Domain n) (ψ : Domain n → Target m) : Domain n → Target m :=
  fun y => ψ (y - a)

/-- The Fréchet derivative of a translated test vector field is the translated
Fréchet derivative. -/
theorem fderiv_translateVectorFieldToOriginal_add
    {n : ℕ} (X : Domain n → Domain n) (a x : Domain n) :
    fderiv ℝ (translateVectorFieldToOriginal a X) (a + x) =
      fderiv ℝ X x := by
  change fderiv ℝ (fun y : Domain n => X (y - a)) (a + x) = fderiv ℝ X x
  simpa using fderiv_comp_sub (𝕜 := ℝ) (f := X) a (x := a + x)

/-- Coordinate derivatives are unchanged after translating a test vector field
back to the original coordinates. -/
theorem partialDerivative_translateVectorFieldToOriginal_add
    {n : ℕ} (X : Domain n → Domain n) (a x : Domain n) (i : Fin n) :
    partialDerivative (translateVectorFieldToOriginal a X) i (a + x) =
      partialDerivative X i x := by
  simp [partialDerivative, fderiv_translateVectorFieldToOriginal_add]

/-- The Fréchet derivative of a translated target-valued test map is the
translated Fréchet derivative. -/
theorem fderiv_translateTargetTestToOriginal_add
    {n m : ℕ} (ψ : Domain n → Target m) (a x : Domain n) :
    fderiv ℝ (translateTargetTestToOriginal a ψ) (a + x) =
      fderiv ℝ ψ x := by
  change fderiv ℝ (fun y : Domain n => ψ (y - a)) (a + x) = fderiv ℝ ψ x
  simpa using fderiv_comp_sub (𝕜 := ℝ) (f := ψ) a (x := a + x)

/-- Coordinate derivatives of target-valued test maps are unchanged after
translating them back to the original coordinates. -/
theorem partialDerivative_translateTargetTestToOriginal_add
    {n m : ℕ} (ψ : Domain n → Target m) (a x : Domain n) (i : Fin n) :
    partialDerivative (translateTargetTestToOriginal a ψ) i (a + x) =
      partialDerivative ψ i x := by
  simp [partialDerivative, fderiv_translateTargetTestToOriginal_add]

/-- Componentwise vector-field derivatives are unchanged after translating a
test vector field back to the original coordinates. -/
theorem vectorFieldPartial_translateVectorFieldToOriginal_add
    {n : ℕ} (X : Domain n → Domain n) (a x : Domain n) (i j : Fin n) :
    vectorFieldPartial (translateVectorFieldToOriginal a X) i j (a + x) =
      vectorFieldPartial X i j x := by
  simp [vectorFieldPartial, partialDerivative_translateVectorFieldToOriginal_add]

/-- Divergence is unchanged after translating a test vector field back to the
original coordinates. -/
theorem divergence_translateVectorFieldToOriginal_add
    {n : ℕ} (X : Domain n → Domain n) (a x : Domain n) :
    divergence (translateVectorFieldToOriginal a X) (a + x) =
      divergence X x := by
  simp [divergence, vectorFieldPartial_translateVectorFieldToOriginal_add]

/-- The weak stationarity integrand is compatible with recentering
coordinates. -/
theorem weakStationarityIntegrand_translateGradient_add
    {n m : ℕ} (Du : Domain n → Gradient n m) (X : Domain n → Domain n)
    (a x : Domain n) :
    weakStationarityIntegrand Du (translateVectorFieldToOriginal a X) (a + x) =
      weakStationarityIntegrand (translateGradient a Du) X x := by
  simp [weakStationarityIntegrand, weakEnergyDensity, translateGradient,
    divergence_translateVectorFieldToOriginal_add,
    vectorFieldPartial_translateVectorFieldToOriginal_add]

/-- Smoothness of compactly supported test vector fields is preserved when
moving them from centered coordinates back to the original coordinates. -/
theorem contDiff_translateVectorFieldToOriginal
    {n : ℕ} {X : Domain n → Domain n} {a : Domain n}
    (hX : ContDiff ℝ 1 X) :
    ContDiff ℝ 1 (translateVectorFieldToOriginal a X) := by
  have hsub : ContDiff ℝ 1 (fun y : Domain n => y - a) :=
    (contDiff_id (𝕜 := ℝ) (E := Domain n) (n := 1)).sub contDiff_const
  exact hX.comp hsub

/-- Compact support is preserved when moving a test vector field from centered
coordinates back to the original coordinates. -/
theorem hasCompactSupport_translateVectorFieldToOriginal
    {n : ℕ} {X : Domain n → Domain n} {a : Domain n}
    (hX : HasCompactSupport X) :
    HasCompactSupport (translateVectorFieldToOriginal a X) := by
  exact hX.comp_homeomorph (Homeomorph.subRight a)

/-- The topological support of a translated-back test field is the preimage of
the original topological support under `y ↦ y - a`. -/
theorem tsupport_translateVectorFieldToOriginal
    {n : ℕ} (X : Domain n → Domain n) (a : Domain n) :
    tsupport (translateVectorFieldToOriginal a X) =
      (fun y : Domain n => y - a) ⁻¹' tsupport X := by
  exact tsupport_comp_eq_preimage X (Homeomorph.subRight a)

/-- Smoothness of target-valued test maps is preserved when moving them from
centered coordinates back to the original coordinates. -/
theorem contDiff_translateTargetTestToOriginal
    {n m : ℕ} {ψ : Domain n → Target m} {a : Domain n}
    (hψ : ContDiff ℝ 1 ψ) :
    ContDiff ℝ 1 (translateTargetTestToOriginal a ψ) := by
  have hsub : ContDiff ℝ 1 (fun y : Domain n => y - a) :=
    (contDiff_id (𝕜 := ℝ) (E := Domain n) (n := 1)).sub contDiff_const
  exact hψ.comp hsub

/-- Compact support is preserved when moving a target-valued test map from
centered coordinates back to the original coordinates. -/
theorem hasCompactSupport_translateTargetTestToOriginal
    {n m : ℕ} {ψ : Domain n → Target m} {a : Domain n}
    (hψ : HasCompactSupport ψ) :
    HasCompactSupport (translateTargetTestToOriginal a ψ) := by
  exact hψ.comp_homeomorph (Homeomorph.subRight a)

/-- The topological support of a translated-back target-valued test map is the
preimage of the original topological support under `y ↦ y - a`. -/
theorem tsupport_translateTargetTestToOriginal
    {n m : ℕ} (ψ : Domain n → Target m) (a : Domain n) :
    tsupport (translateTargetTestToOriginal a ψ) =
      (fun y : Domain n => y - a) ⁻¹' tsupport ψ := by
  exact tsupport_comp_eq_preimage ψ (Homeomorph.subRight a)

/-- Left translation preserves Lebesgue measure on the domain. -/
theorem measurePreserving_add_left_volume {n : ℕ} (a : Domain n) :
    MeasurePreserving (fun x : Domain n => a + x)
      (volume : Measure (Domain n)) (volume : Measure (Domain n)) :=
  measurePreserving_add_left (volume : Measure (Domain n)) a

/-- Left translation is a measurable embedding. -/
theorem measurableEmbedding_add_left {n : ℕ} (a : Domain n) :
    MeasurableEmbedding (fun x : Domain n => a + x) :=
  (MeasurableEquiv.addLeft a).measurableEmbedding

/-- Full-space Lebesgue integration is invariant under right translation. -/
theorem integral_comp_add_right_volume {n : ℕ} (f : Domain n → ℝ) (a : Domain n) :
    (∫ x, f (x + a)) = ∫ x, f x := by
  simpa using
    (integral_add_right_eq_self (μ := (volume : Measure (Domain n))) f a)

/-- Full-space Lebesgue integration is invariant under left translation. -/
theorem integral_comp_add_left_volume {n : ℕ} (f : Domain n → ℝ) (a : Domain n) :
    (∫ x, f (a + x)) = ∫ x, f x := by
  simpa [add_comm] using integral_comp_add_right_volume (n := n) f a

/-- Set integrals are invariant under the change of variables `x ↦ a + x`. -/
theorem setIntegral_preimage_add_left_eq {n : ℕ}
    (f : Domain n → ℝ) (a : Domain n) {s : Set (Domain n)}
    (hs : MeasurableSet s) :
    (∫ x in (fun x : Domain n => a + x) ⁻¹' s, f (a + x))
      =
    ∫ x in s, f x := by
  have hpre : MeasurableSet ((fun x : Domain n => a + x) ⁻¹' s) :=
    hs.preimage (continuous_const.add continuous_id).measurable
  calc
    (∫ x in (fun x : Domain n => a + x) ⁻¹' s, f (a + x))
        =
      ∫ x, ((fun x : Domain n => a + x) ⁻¹' s).indicator
        (fun x : Domain n => f (a + x)) x := by
        rw [integral_indicator hpre]
    _ =
      ∫ x, s.indicator f (a + x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : a + x ∈ s
        · simp [hx]
        · simp [hx]
    _ = ∫ x, s.indicator f x :=
        integral_comp_add_left_volume (n := n) (s.indicator f) a
    _ = ∫ x in s, f x := by
        rw [integral_indicator hs]

/-- Weak stationarity is preserved by recentering coordinates. -/
theorem weakStationaryIn_centeredDomain {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {a : Domain n}
    (hstationary : WeakStationaryIn Du Ω)
    (hΩ_meas : MeasurableSet Ω) :
    WeakStationaryIn (translateGradient a Du) (centeredDomain a Ω) := by
  intro X hXdiff hXcompact hXsupport
  let Y : Domain n → Domain n := translateVectorFieldToOriginal a X
  have hYdiff : ContDiff ℝ 1 Y := by
    dsimp [Y]
    exact contDiff_translateVectorFieldToOriginal (a := a) hXdiff
  have hYcompact : HasCompactSupport Y := by
    dsimp [Y]
    exact hasCompactSupport_translateVectorFieldToOriginal (a := a) hXcompact
  have hYsupport : tsupport Y ⊆ Ω := by
    intro y hy
    change y ∈ tsupport (translateVectorFieldToOriginal a X) at hy
    rw [tsupport_translateVectorFieldToOriginal X a] at hy
    have hcenter : a + (y - a) ∈ Ω := hXsupport hy
    simpa [centeredDomain, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      hcenter
  have hzero : (∫ y in Ω, weakStationarityIntegrand Du Y y) = 0 :=
    hstationary Y hYdiff hYcompact hYsupport
  have hpre_meas :
      MeasurableSet ((fun x : Domain n => a + x) ⁻¹' Ω) :=
    hΩ_meas.preimage (continuous_const.add continuous_id).measurable
  have hcongr :
      (∫ x in centeredDomain a Ω,
          weakStationarityIntegrand (translateGradient a Du) X x)
        =
      ∫ x in (fun x : Domain n => a + x) ⁻¹' Ω,
        weakStationarityIntegrand Du Y (a + x) := by
    change
      (∫ x in (fun x : Domain n => a + x) ⁻¹' Ω,
          weakStationarityIntegrand (translateGradient a Du) X x)
        =
      ∫ x in (fun x : Domain n => a + x) ⁻¹' Ω,
        weakStationarityIntegrand Du Y (a + x)
    refine setIntegral_congr_fun hpre_meas ?_
    intro x hx
    dsimp [Y]
    exact (weakStationarityIntegrand_translateGradient_add Du X a x).symm
  have hchange :
      (∫ x in (fun x : Domain n => a + x) ⁻¹' Ω,
        weakStationarityIntegrand Du Y (a + x))
        =
      ∫ y in Ω, weakStationarityIntegrand Du Y y :=
    setIntegral_preimage_add_left_eq
      (n := n) (f := fun y : Domain n => weakStationarityIntegrand Du Y y)
      a hΩ_meas
  exact hcongr.trans (hchange.trans hzero)

/-- The weak-gradient integration-by-parts relation is preserved by recentering
coordinates. -/
theorem hasWeakGradientIn_centeredDomain {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n}
    (hweak : HasWeakGradientIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω) :
    HasWeakGradientIn
      (fun x : Domain n => u (a + x))
      (translateGradient a Du)
      (centeredDomain a Ω) := by
  intro i ψ hψdiff hψcompact hψsupport
  let η : Domain n → Target m := translateTargetTestToOriginal a ψ
  have hηdiff : ContDiff ℝ 1 η := by
    dsimp [η]
    exact contDiff_translateTargetTestToOriginal (a := a) hψdiff
  have hηcompact : HasCompactSupport η := by
    dsimp [η]
    exact hasCompactSupport_translateTargetTestToOriginal (a := a) hψcompact
  have hηsupport : tsupport η ⊆ Ω := by
    intro y hy
    change y ∈ tsupport (translateTargetTestToOriginal a ψ) at hy
    rw [tsupport_translateTargetTestToOriginal ψ a] at hy
    have hcenter : a + (y - a) ∈ Ω := hψsupport hy
    simpa [centeredDomain, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      hcenter
  have horig :
      (∫ y in Ω, inner ℝ (u y) (partialDerivative η i y))
        =
      -∫ y in Ω, inner ℝ (Du y i) (η y) :=
    hweak i η hηdiff hηcompact hηsupport
  have hpre_meas :
      MeasurableSet ((fun x : Domain n => a + x) ⁻¹' Ω) :=
    hΩ_meas.preimage (continuous_const.add continuous_id).measurable
  have hleft :
      (∫ x in centeredDomain a Ω,
          inner ℝ (u (a + x)) (partialDerivative ψ i x))
        =
      ∫ y in Ω, inner ℝ (u y) (partialDerivative η i y) := by
    calc
      (∫ x in centeredDomain a Ω,
          inner ℝ (u (a + x)) (partialDerivative ψ i x))
          =
        ∫ x in (fun x : Domain n => a + x) ⁻¹' Ω,
          inner ℝ (u (a + x)) (partialDerivative η i (a + x)) := by
          change
            (∫ x in (fun x : Domain n => a + x) ⁻¹' Ω,
                inner ℝ (u (a + x)) (partialDerivative ψ i x))
              =
            ∫ x in (fun x : Domain n => a + x) ⁻¹' Ω,
              inner ℝ (u (a + x)) (partialDerivative η i (a + x))
          refine setIntegral_congr_fun hpre_meas ?_
          intro x hx
          dsimp [η]
          rw [partialDerivative_translateTargetTestToOriginal_add]
      _ =
        ∫ y in Ω, inner ℝ (u y) (partialDerivative η i y) :=
          setIntegral_preimage_add_left_eq
            (n := n)
            (f := fun y : Domain n => inner ℝ (u y) (partialDerivative η i y))
            a hΩ_meas
  have hright :
      (∫ x in centeredDomain a Ω,
          inner ℝ ((translateGradient a Du) x i) (ψ x))
        =
      ∫ y in Ω, inner ℝ (Du y i) (η y) := by
    calc
      (∫ x in centeredDomain a Ω,
          inner ℝ ((translateGradient a Du) x i) (ψ x))
          =
        ∫ x in (fun x : Domain n => a + x) ⁻¹' Ω,
          inner ℝ (Du (a + x) i) (η (a + x)) := by
          change
            (∫ x in (fun x : Domain n => a + x) ⁻¹' Ω,
                inner ℝ ((translateGradient a Du) x i) (ψ x))
              =
            ∫ x in (fun x : Domain n => a + x) ⁻¹' Ω,
              inner ℝ (Du (a + x) i) (η (a + x))
          refine setIntegral_congr_fun hpre_meas ?_
          intro x hx
          simp [translateGradient, η, translateTargetTestToOriginal,
            sub_eq_add_neg, add_assoc]
      _ =
        ∫ y in Ω, inner ℝ (Du y i) (η y) :=
          setIntegral_preimage_add_left_eq
            (n := n) (f := fun y : Domain n => inner ℝ (Du y i) (η y))
            a hΩ_meas
  rw [hleft, hright]
  exact horig

/-- The preimage of a ball centered at `a` under `x ↦ a + x` is the
origin-centered ball of the same radius. -/
theorem preimage_add_left_ball_center {n : ℕ} (a : Domain n) (r : ℝ) :
    (fun x : Domain n => a + x) ⁻¹' Metric.ball a r =
      Metric.ball (0 : Domain n) r := by
  ext x
  simp [Metric.mem_ball, dist_eq_norm]

/-- The preimage of a closed ball centered at `a` under `x ↦ a + x` is the
origin-centered closed ball of the same radius. -/
theorem preimage_add_left_closedBall_center {n : ℕ} (a : Domain n) (r : ℝ) :
    (fun x : Domain n => a + x) ⁻¹' Metric.closedBall a r =
      Metric.closedBall (0 : Domain n) r := by
  ext x
  simp [Metric.mem_closedBall, dist_eq_norm]

/-- Measurability of a domain is preserved when recentering coordinates. -/
theorem measurableSet_centeredDomain {n : ℕ} {a : Domain n} {Ω : Set (Domain n)}
    (hΩ : MeasurableSet Ω) :
    MeasurableSet (centeredDomain a Ω) :=
  hΩ.preimage (continuous_const.add continuous_id).measurable

/-- A closed ball contained in `Ω` becomes an origin-centered closed ball
contained in the recentered domain. -/
theorem closedBall_subset_centeredDomain_of_closedBall_subset {n : ℕ}
    {a : Domain n} {Ω : Set (Domain n)} {R0 : ℝ}
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω) :
    Metric.closedBall (0 : Domain n) R0 ⊆ centeredDomain a Ω := by
  intro x hx
  exact hclosedBall_subset (by
    have hxpre :
        x ∈ (fun x : Domain n => a + x) ⁻¹' Metric.closedBall a R0 := by
      simpa [preimage_add_left_closedBall_center] using hx
    exact hxpre)

/-- Local scalar integrability is preserved by recentering coordinates. -/
theorem locallyIntegrableScalarIn_centeredDomain {n : ℕ}
    {f : Domain n → ℝ} {Ω : Set (Domain n)} {a : Domain n}
    (hf : LocallyIntegrableScalarIn f Ω) :
    LocallyIntegrableScalarIn (translateScalar a f) (centeredDomain a Ω) := by
  intro K hK hKΩ
  let e : Domain n → Domain n := fun x => a + x
  have hK_image_compact : IsCompact (e '' K) :=
    hK.image (continuous_const.add continuous_id)
  have hK_image_subset : e '' K ⊆ Ω := by
    intro y hy
    rcases hy with ⟨x, hxK, rfl⟩
    exact hKΩ hxK
  have h_original : IntegrableOn f (e '' K) volume :=
    hf (e '' K) hK_image_compact hK_image_subset
  have h_change :
      IntegrableOn (f ∘ e) K (volume : Measure (Domain n)) := by
    exact
      ((measurePreserving_add_left_volume (n := n) a).integrableOn_image
        (measurableEmbedding_add_left (n := n) a)
        (f := f) (s := K)).1 h_original
  exact h_change

/-- The `L²_loc` map part of `W^{1,2}_{loc}` is preserved by recentering. -/
theorem mapLocallyL2In_centeredDomain {n m : ℕ}
    {u : Domain n → Target m} {Ω : Set (Domain n)} {a : Domain n}
    (hu : MapLocallyL2In u Ω) :
    MapLocallyL2In (fun x : Domain n => u (a + x)) (centeredDomain a Ω) := by
  exact locallyIntegrableScalarIn_centeredDomain
      (n := n) (a := a) (f := fun x : Domain n => ‖u x‖ ^ 2)
      (Ω := Ω) hu

/-- The `L²_loc` gradient-energy part of `W^{1,2}_{loc}` is preserved by
recentering. -/
theorem gradientLocallyL2In_centeredDomain {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {a : Domain n}
    (hgrad : GradientLocallyL2In Du Ω) :
    GradientLocallyL2In (translateGradient a Du) (centeredDomain a Ω) := by
  exact locallyIntegrableScalarIn_centeredDomain
      (n := n) (a := a) (f := fun x : Domain n => weakEnergyDensity Du x)
      (Ω := Ω) hgrad

/-- A.e. strong measurability of the weak gradient is preserved by recentering. -/
theorem gradientAEStronglyMeasurableIn_centeredDomain {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {a : Domain n}
    (hDu : GradientAEStronglyMeasurableIn Du Ω) :
    GradientAEStronglyMeasurableIn (translateGradient a Du) (centeredDomain a Ω) := by
  let e : Domain n → Domain n := fun x => a + x
  have hmp :
      MeasurePreserving e
        ((volume : Measure (Domain n)).restrict (e ⁻¹' Ω))
        ((volume : Measure (Domain n)).restrict Ω) :=
    (measurePreserving_add_left_volume (n := n) a).restrict_preimage_emb
      (measurableEmbedding_add_left (n := n) a) Ω
  have hcomp : AEStronglyMeasurable (Du ∘ e)
      ((volume : Measure (Domain n)).restrict (e ⁻¹' Ω)) :=
    hDu.comp_measurePreserving hmp
  exact hcomp

/-- The concrete `W^{1,2}_{loc}` package is preserved by recentering
coordinates. -/
theorem w12LocIn_centeredDomain {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n}
    (hmap : W12LocIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω) :
    W12LocIn
      (fun x : Domain n => u (a + x))
      (translateGradient a Du)
      (centeredDomain a Ω) :=
  ⟨mapLocallyL2In_centeredDomain (a := a) hmap.map_locallyL2,
    gradientAEStronglyMeasurableIn_centeredDomain (a := a)
      hmap.gradient_aestronglyMeasurable,
    gradientLocallyL2In_centeredDomain (a := a) hmap.gradient_locallyL2,
    hasWeakGradientIn_centeredDomain (a := a) hmap.hasWeakGradient hΩ_meas⟩

/-- The full weak stationary map package is preserved by recentering
coordinates. -/
theorem weakStationaryMapIn_centeredDomain {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n}
    (hmap : WeakStationaryMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω) :
    WeakStationaryMapIn
      (fun x : Domain n => u (a + x))
      (translateGradient a Du)
      (centeredDomain a Ω) :=
  ⟨w12LocIn_centeredDomain (a := a) hmap.1 hΩ_meas,
    weakStationaryIn_centeredDomain (a := a) hmap.2 hΩ_meas⟩

/-- The weak ball energy centered at `a` is the origin-centered energy of the
translated gradient field. -/
theorem weakBallEnergy_translateGradient_zero
    {n m : ℕ} (Du : Domain n → Gradient n m) (a : Domain n) (r : ℝ) :
    weakBallEnergy (translateGradient a Du) (0 : Domain n) r =
      weakBallEnergy Du a r := by
  calc
    weakBallEnergy (translateGradient a Du) (0 : Domain n) r
        =
      ∫ x in Metric.ball (0 : Domain n) r,
        weakEnergyDensity Du (a + x) := by
        rfl
    _ =
      ∫ x in (fun x : Domain n => a + x) ⁻¹' Metric.ball a r,
        weakEnergyDensity Du (a + x) := by
        rw [preimage_add_left_ball_center]
    _ =
      weakBallEnergy Du a r := by
        simpa [weakBallEnergy] using
          setIntegral_preimage_add_left_eq
            (n := n) (f := fun x : Domain n => weakEnergyDensity Du x)
            a (measurableSet_ball : MeasurableSet (Metric.ball a r))

/-- The weak monotonicity quantity is unchanged after recentering coordinates. -/
theorem weakTheta_translateGradient_zero
    {n m : ℕ} (Du : Domain n → Gradient n m) (a : Domain n) (r : ℝ) :
    weakTheta (translateGradient a Du) (0 : Domain n) r =
      weakTheta Du a r := by
  simp [weakTheta, weakBallEnergy_translateGradient_zero]

/-- The weak radial derivative is unchanged by recentering coordinates. -/
theorem weakRadialDerivative_translateGradient_zero
    {n m : ℕ} (Du : Domain n → Gradient n m) (a x : Domain n) :
    weakRadialDerivative (translateGradient a Du) (0 : Domain n) x =
      weakRadialDerivative Du a (a + x) := by
  simp [weakRadialDerivative, translateGradient, sub_eq_add_neg, add_assoc]

/-- The weak radial-energy density is unchanged by recentering coordinates. -/
theorem weakRadialEnergyDensity_translateGradient_zero
    {n m : ℕ} (Du : Domain n → Gradient n m) (a x : Domain n) :
    weakRadialEnergyDensity (translateGradient a Du) (0 : Domain n) x =
      weakRadialEnergyDensity Du a (a + x) := by
  simp [weakRadialEnergyDensity, weakRadialDerivative_translateGradient_zero]

/-- The annular right-hand side in the weak monotonicity formula is unchanged
after recentering coordinates. -/
theorem weakMonotonicityRhs_translateGradient_zero
    {n m : ℕ} (Du : Domain n → Gradient n m) (a : Domain n) (s r : ℝ) :
    weakMonotonicityRhs (translateGradient a Du) (0 : Domain n) s r =
      weakMonotonicityRhs Du a s r := by
  let e : Domain n → Domain n := fun x => a + x
  let ann : Set (Domain n) := Metric.ball a r \ Metric.ball a s
  have hann_meas : MeasurableSet ann :=
    (Metric.isOpen_ball.measurableSet).diff Metric.isOpen_ball.measurableSet
  have hpre :
      e ⁻¹' ann = Metric.ball (0 : Domain n) r \ Metric.ball (0 : Domain n) s := by
    ext x
    simp [e, ann, Metric.mem_ball, dist_eq_norm]
  have hchange :
      (∫ x in e ⁻¹' ann,
          ‖a + x - a‖ ^ (2 - (n : ℤ)) *
            weakRadialEnergyDensity Du a (a + x))
        =
      ∫ x in ann,
          ‖x - a‖ ^ (2 - (n : ℤ)) * weakRadialEnergyDensity Du a x := by
    simpa [e, ann] using
      setIntegral_preimage_add_left_eq
        (n := n)
        (f := fun x : Domain n =>
          ‖x - a‖ ^ (2 - (n : ℤ)) * weakRadialEnergyDensity Du a x)
        a hann_meas
  calc
    weakMonotonicityRhs (translateGradient a Du) (0 : Domain n) s r
        =
      2 * ∫ x in Metric.ball (0 : Domain n) r \ Metric.ball (0 : Domain n) s,
          ‖x‖ ^ (2 - (n : ℤ)) *
            weakRadialEnergyDensity Du a (a + x) := by
        simp [weakMonotonicityRhs, weakRadialEnergyDensity_translateGradient_zero]
    _ =
      2 * ∫ x in e ⁻¹' ann,
          ‖a + x - a‖ ^ (2 - (n : ℤ)) *
            weakRadialEnergyDensity Du a (a + x) := by
        rw [hpre]
        simp [sub_eq_add_neg, add_assoc]
    _ =
      weakMonotonicityRhs Du a s r := by
        rw [hchange]
        simp [weakMonotonicityRhs, ann]

/-- Arbitrary-center Euclidean weak monotonicity, reduced to the origin-centered
theorem for the translated map and translated weak gradient. -/
theorem weakTheta_monotone_from_centered_W12Loc_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hmap_centered :
      WeakStationaryMapIn
        (fun x : Domain n => u (a + x))
        (translateGradient a Du)
        (centeredDomain a Ω))
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω) :
    MonotoneOn (weakTheta Du a) (Ioo (0 : ℝ) R0) := by
  have hmono :
      MonotoneOn (weakTheta (translateGradient a Du) (0 : Domain n))
        (Ioo (0 : ℝ) R0) :=
    weakTheta_monotone_from_W12Loc_euclidean
      (n := n) (m := m)
      (u := fun x : Domain n => u (a + x))
      (Du := translateGradient a Du)
      (Ω := centeredDomain a Ω) (R0 := R0)
      hR0_nonneg hmap_centered
      (measurableSet_centeredDomain (a := a) hΩ_meas)
      (closedBall_subset_centeredDomain_of_closedBall_subset
        (a := a) hclosedBall_subset)
  intro s hs r hr hsr
  simpa [weakTheta_translateGradient_zero (Du := Du) (a := a)] using
    hmono hs hr hsr

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
