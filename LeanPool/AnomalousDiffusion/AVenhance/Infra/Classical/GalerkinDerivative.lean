/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinGenerator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinEvolution

/-! Commutator forcing bounds for differentiated finite Fourier paths. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalDerivativeMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalDerivativeMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalDerivativeProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance classicalDerivativeProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

namespace AVenhance.Infra.Classical

/-- The finite list of scalar products in one component of the transport commutator. -/
def classicalWordCommutatorTerms (w : List (Fin 2)) (b u : Vec 2 → ℝ)
    (j : Fin 2) : List (Vec 2 → ℝ) :=
  (classicalWordCommutatorSplits w).map fun p =>
    classicalWordProductTerm p b (fun x => AVenhance.spaceGrad u x j)

theorem GalerkinDerivative.classicalWordDerivative_periodic (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (classicalWordDerivative w f) := by
  induction w with
  | nil => exact hper
  | cons i w ih => exact AVenhance.Infra.Classical.periodic_spaceGrad_component ih i

theorem GalerkinDerivative.classicalPeriodic_mul {f g : Vec 2 → ℝ}
    (hf : AVenhance.IsZ2Periodic f) (hg : AVenhance.IsZ2Periodic g) :
    AVenhance.IsZ2Periodic (fun x => f x * g x) := by
  intro k x
  change f (x + AVenhance.latticeShift k) * g (x + AVenhance.latticeShift k) = _
  rw [hf k x, hg k x]

theorem GalerkinDerivative.listMapSum_mono {α : Type} (L : List α) (f g : α → ℝ)
    (h : ∀ a ∈ L, f a ≤ g a) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have htail : ∀ z ∈ L, f z ≤ g z := by
        intro z hz
        exact h z (by simp [hz])
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h a (by simp)) (ih htail)

theorem GalerkinDerivative.derivativeListSum_continuous (L : List (Vec 2 → ℝ))
    (hL : ∀ f ∈ L, Continuous f) : Continuous L.sum := by
  induction L with
  | nil => exact continuous_const
  | cons f L ih =>
      have hf := hL f (by simp)
      have htail : ∀ g ∈ L, Continuous g := by
        intro g hg
        exact hL g (by simp [hg])
      change Continuous (fun x => f x + L.sum x)
      exact hf.add (ih htail)

theorem GalerkinDerivative.derivativeListSum_periodic (L : List (Vec 2 → ℝ))
    (hL : ∀ f ∈ L, AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic L.sum := by
  induction L with
  | nil => intro k x; rfl
  | cons f L ih =>
      have hf := hL f (by simp)
      have htail : ∀ g ∈ L, AVenhance.IsZ2Periodic g := by
        intro g hg
        exact hL g (by simp [hg])
      intro k x
      simp only [List.sum_cons]
      change f (x + AVenhance.latticeShift k) + L.sum (x + AVenhance.latticeShift k) = _
      rw [hf k x, ih htail k x]
      rfl

theorem GalerkinDerivative.classicalSpaceLap_contDiff (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceLap f x) := by
  unfold AVenhance.spaceLap
  apply ContDiff.sum
  intro i hi
  have hgrad : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad f x i) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ f x (Homogenization.basisVec i))
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => fderiv ℝ (fun y => AVenhance.spaceGrad f y i) x
      (Homogenization.basisVec i))
  exact (hgrad.fderiv_right (by simp)).clm_apply contDiff_const

theorem GalerkinDerivative.classicalSpaceLap_periodic {f : Vec 2 → ℝ}
    (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (fun x => AVenhance.spaceLap f x) := by
  intro k x
  unfold AVenhance.spaceLap
  apply Finset.sum_congr rfl
  intro i hi
  exact AVenhance.Infra.Classical.periodic_spaceGrad_component
    (AVenhance.Infra.Classical.periodic_spaceGrad_component hper i) i k x

theorem GalerkinDerivative.classicalTransport_contDiff (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) := by
  unfold classicalTransport
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => ∑ j : Fin 2, b x j * AVenhance.spaceGrad u x j)
  apply ContDiff.sum
  intro j hj
  have hbcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x => b x j) := (contDiff_pi.1 hb) j
  have hgrad : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad u x j) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ u x (Homogenization.basisVec j))
    exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
  exact hbcomp.mul hgrad

theorem GalerkinDerivative.classicalTransport_periodic (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hbp : AVenhance.IsZ2Periodic b) (hup : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic (classicalTransport b u) := by
  intro k x
  unfold classicalTransport
  change ∑ j : Fin 2, b (x + AVenhance.latticeShift k) j *
      AVenhance.spaceGrad u (x + AVenhance.latticeShift k) j = _
  apply Finset.sum_congr rfl
  intro j hj
  have hbval := congrFun (hbp k x) j
  have hgval := AVenhance.Infra.Classical.periodic_spaceGrad_component hup j k x
  change AVenhance.spaceGrad u (x + AVenhance.latticeShift k) j =
    AVenhance.spaceGrad u x j at hgval
  rw [hbval, hgval]

/-- The coefficient derivative map commutes with Fourier projection of a smooth periodic field. -/
theorem realFourierWordDerivativeMap_projection (N : ℕ) (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : AVenhance.IsZ2Periodic f) :
    realFourierWordDerivativeMap N w
        (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus f)) =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w f)) := by
  rw [realFourierWordDerivativeMap_apply]
  exact realFourierWordDerivativeCoefficients_projection N w f hf hper

theorem GalerkinDerivative.classicalWordCommutatorTerms_continuous (w : List (Fin 2))
    (b u : Vec 2 → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (j : Fin 2) :
    ∀ f ∈ classicalWordCommutatorTerms w b u j, Continuous f := by
  intro f hf
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
  unfold classicalWordProductTerm
  have hbj : ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative p.1 b) :=
    classicalWordDerivative_contDiff p.1 b hb
  have hgrad : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad u x j) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ u x (Homogenization.basisVec j))
    exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
  exact hbj.continuous.mul (classicalWordDerivative_contDiff p.2
    (fun x => AVenhance.spaceGrad u x j) hgrad).continuous

theorem GalerkinDerivative.classicalWordCommutatorTerms_periodic (w : List (Fin 2))
    (b u : Vec 2 → ℝ) (hbp : AVenhance.IsZ2Periodic b)
    (hup : AVenhance.IsZ2Periodic u) (j : Fin 2) :
    ∀ f ∈ classicalWordCommutatorTerms w b u j, AVenhance.IsZ2Periodic f := by
  intro f hf
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
  apply GalerkinDerivative.classicalPeriodic_mul
  · exact GalerkinDerivative.classicalWordDerivative_periodic p.1 b hbp
  · exact GalerkinDerivative.classicalWordDerivative_periodic p.2
      (fun x => AVenhance.spaceGrad u x j)
      (AVenhance.Infra.Classical.periodic_spaceGrad_component hup j)

/-- A component commutator projection is bounded by the uniform drift derivative bound times the
sum of the coefficient norms of the solution derivatives appearing in Leibniz's rule. -/
theorem classicalWordCommutatorExpansion_projection_norm_le (N : ℕ)
    (w : List (Fin 2)) (b : Vec 2 → ℝ)
    (c : Coefficients (RealFourierDimension N)) (j : Fin 2)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbp : AVenhance.IsZ2Periodic b)
    (hDb : ∀ p, p ∈ classicalWordCommutatorSplits w → ∀ x,
      |classicalWordDerivative p.1 b x| ≤ B) :
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (AVenhance.Infra.Torus.periodicToTorus
        (classicalWordCommutatorExpansion w b
          (fun x => AVenhance.spaceGrad
            (realFourierModeAmbientExpansion N c) x j)))‖ ≤
      ((classicalWordCommutatorSplits w).map fun p =>
        B * ‖realFourierWordDerivativeMap N (j :: p.2) c‖).sum := by
  let u := realFourierModeAmbientExpansion N c
  let terms := classicalWordCommutatorTerms w b u j
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u] using realFourierModeAmbientExpansion_contDiff N c
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have hup : AVenhance.IsZ2Periodic u := realFourierModeAmbientExpansion_periodic N c
  have hcont : ∀ f ∈ terms, Continuous f :=
    GalerkinDerivative.classicalWordCommutatorTerms_continuous w b u hb hu j
  have hper : ∀ f ∈ terms, AVenhance.IsZ2Periodic f :=
    GalerkinDerivative.classicalWordCommutatorTerms_periodic w b u hbp hup j
  have hsum : terms.sum = classicalWordCommutatorExpansion w b
      (fun x => AVenhance.spaceGrad u x j) := by
    simp [terms, classicalWordCommutatorTerms, classicalWordCommutatorExpansion]
  rw [← hsum]
  calc
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus terms.sum)‖ ≤
      (terms.map fun f => ‖modeProjectionCoefficients (RealFourierDimension N)
        (realFourierModeFin N) (AVenhance.Infra.Torus.periodicToTorus f)‖).sum :=
      realFourierProjectionCoefficients_listSum_norm_le N terms hcont hper
    _ ≤ ((classicalWordCommutatorSplits w).map fun p =>
          B * ‖realFourierWordDerivativeMap N (j :: p.2) c‖).sum := by
      change (((classicalWordCommutatorSplits w).map fun p =>
          classicalWordProductTerm p b (fun x => AVenhance.spaceGrad u x j)).map
          (fun f => ‖modeProjectionCoefficients (RealFourierDimension N)
            (realFourierModeFin N) (AVenhance.Infra.Torus.periodicToTorus f)‖)).sum ≤ _
      rw [List.map_map]
      apply GalerkinDerivative.listMapSum_mono
      intro p hp
      let d := realFourierWordDerivativeCoefficients N c (j :: p.2)
      have hword : classicalWordDerivative p.2
          (fun x => AVenhance.spaceGrad u x j) =
          classicalWordDerivative (j :: p.2) u := by
        simpa [classicalWordDerivative] using
          (classicalWordDerivative_commute_gradient p.2 u hu j)
      have hexp : classicalWordDerivative (j :: p.2) u =
          realFourierModeAmbientExpansion N d := by
        simpa [u, d] using
          classicalWordDerivative_realFourierModeAmbientExpansion N (j :: p.2) c
      have htermEq : classicalWordProductTerm p b
          (fun x => AVenhance.spaceGrad u x j) =
          fun x => classicalWordDerivative p.1 b x *
            realFourierModeAmbientExpansion N d x := by
        funext x
        simp only [classicalWordProductTerm]
        rw [congrFun hword x, congrFun hexp x]
      have hfirstCont : Continuous (classicalWordDerivative p.1 b) :=
        (classicalWordDerivative_contDiff p.1 b hb).continuous
      have hfirstBound : ∀ x,
          ‖classicalWordDerivative p.1 b x‖ ≤ B := by
        intro x
        simpa [Real.norm_eq_abs] using hDb p hp x
      have hproduct := realFourierProjection_product_norm_le N d
        (classicalWordDerivative p.1 b) hfirstCont hB hfirstBound
      simpa [d, realFourierWordDerivativeMap_apply, htermEq] using hproduct

/-- The full transport commutator is the sum over the two drift components. -/
def classicalWordTransportCommutatorExpansion (w : List (Fin 2))
    (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ) : Vec 2 → ℝ :=
  ∑ j : Fin 2, classicalWordCommutatorExpansion w (fun x => b x j)
    (fun x => AVenhance.spaceGrad u x j)

/-- Projection of the full transport commutator is bounded by the drift derivative bound times
the finite sum of all coefficient derivative norms in Leibniz's expansion. -/
theorem classicalWordTransportCommutatorExpansion_projection_norm_le (N : ℕ)
    (w : List (Fin 2)) (b : Vec 2 → Vec 2)
    (c : Coefficients (RealFourierDimension N)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbp : AVenhance.IsZ2Periodic b)
    (hDb : ∀ j p, p ∈ classicalWordCommutatorSplits w → ∀ x,
      |classicalWordDerivative p.1 (fun y => b y j) x| ≤ B) :
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (AVenhance.Infra.Torus.periodicToTorus
        (classicalWordTransportCommutatorExpansion w b
          (realFourierModeAmbientExpansion N c)))‖ ≤
      ∑ j : Fin 2, ((classicalWordCommutatorSplits w).map fun p =>
        B * ‖realFourierWordDerivativeMap N (j :: p.2) c‖).sum := by
  let u := realFourierModeAmbientExpansion N c
  let comm (j : Fin 2) : Vec 2 → ℝ :=
    classicalWordCommutatorExpansion w (fun x => b x j)
      (fun x => AVenhance.spaceGrad u x j)
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u] using realFourierModeAmbientExpansion_contDiff N c
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using realFourierModeAmbientExpansion_periodic N c
  have hcommCont (j : Fin 2) : Continuous (comm j) := by
    let terms := classicalWordCommutatorTerms w (fun x => b x j) u j
    have hbcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x => b x j) := (contDiff_pi.1 hb) j
    have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceGrad u x j) := by
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun x => fderiv ℝ u x (Homogenization.basisVec j))
      exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
    have hterms := GalerkinDerivative.classicalWordCommutatorTerms_continuous w
      (fun x => b x j) u hbcomp hu j
    have hsum : terms.sum = comm j := by
      simp [terms, comm, classicalWordCommutatorTerms,
        classicalWordCommutatorExpansion]
    rw [← hsum]
    exact GalerkinDerivative.derivativeListSum_continuous terms hterms
  have hcommPer (j : Fin 2) : AVenhance.IsZ2Periodic (comm j) := by
    let terms := classicalWordCommutatorTerms w (fun x => b x j) u j
    have hbper : AVenhance.IsZ2Periodic (fun x => b x j) := by
      intro k x
      exact congrFun (hbp k x) j
    have hterms := GalerkinDerivative.classicalWordCommutatorTerms_periodic w
      (fun x => b x j) u hbper hup j
    have hsum : terms.sum = comm j := by
      simp [terms, comm, classicalWordCommutatorTerms,
        classicalWordCommutatorExpansion]
    rw [← hsum]
    exact GalerkinDerivative.derivativeListSum_periodic terms hterms
  have hmem (j : Fin 2) : MemLp
      (AVenhance.Infra.Torus.periodicToTorus (comm j)) 2
        (volume : Measure Torus) :=
    memLp_periodicToTorus_real (hcommCont j) (hcommPer j)
  have htorusAdd : AVenhance.Infra.Torus.periodicToTorus
      (fun x => comm 0 x + comm 1 x) =
        AVenhance.Infra.Torus.periodicToTorus (comm 0) +
          AVenhance.Infra.Torus.periodicToTorus (comm 1) := by
    funext x
    rfl
  have hprojection :
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus
          (classicalWordTransportCommutatorExpansion w b u)) =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus (comm 0)) +
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus (comm 1)) := by
    rw [show classicalWordTransportCommutatorExpansion w b u =
      fun x => comm 0 x + comm 1 x by
        funext x
        simp [classicalWordTransportCommutatorExpansion, comm, Fin.sum_univ_two]]
    rw [htorusAdd, realFourierModeProjectionCoefficients_add N (hmem 0) (hmem 1)]
  have hbound0 := classicalWordCommutatorExpansion_projection_norm_le N w
    (fun x => b x 0) c 0 hB
    (((contDiff_pi.1 hb) 0).of_le (by simp))
    (fun k x => congrFun (hbp k x) 0)
    (fun p hp x => hDb 0 p hp x)
  have hbound1 := classicalWordCommutatorExpansion_projection_norm_le N w
    (fun x => b x 1) c 1 hB
    (((contDiff_pi.1 hb) 1).of_le (by simp))
    (fun k x => congrFun (hbp k x) 1)
    (fun p hp x => hDb 1 p hp x)
  have hnormEq :
      ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus
          (classicalWordTransportCommutatorExpansion w b
            (realFourierModeAmbientExpansion N c)))‖ =
      ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus (comm 0)) +
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus (comm 1))‖ := by
    simpa [u] using congrArg norm hprojection
  calc
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus
          (classicalWordTransportCommutatorExpansion w b
            (realFourierModeAmbientExpansion N c)))‖ =
      ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus (comm 0)) +
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus (comm 1))‖ := hnormEq
    _ ≤ _ := by
      calc
        _ ≤ ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
              (AVenhance.Infra.Torus.periodicToTorus (comm 0))‖ +
            ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
              (AVenhance.Infra.Torus.periodicToTorus (comm 1))‖ := norm_add_le _ _
        _ ≤ ((classicalWordCommutatorSplits w).map fun p =>
              B * ‖realFourierWordDerivativeMap N (0 :: p.2) c‖).sum +
            ((classicalWordCommutatorSplits w).map fun p =>
              B * ‖realFourierWordDerivativeMap N (1 :: p.2) c‖).sum :=
          add_le_add hbound0 hbound1
        _ = ∑ j : Fin 2, ((classicalWordCommutatorSplits w).map fun p =>
              B * ‖realFourierWordDerivativeMap N (j :: p.2) c‖).sum := by
          simp [Fin.sum_univ_two]

/-- A transformed forced Galerkin source is the projection of the differentiated forcing minus
the exact transport commutator. -/
theorem ForcedGalerkinData.transformedForcing_eq_wordResidual
    {N : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (D : ForcedGalerkinData (Coefficients (RealFourierDimension N)) G)
    (w : List (Fin 2)) (t κ : ℝ) (b : Vec 2 → Vec 2) (F : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbp : AVenhance.IsZ2Periodic b)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFper : AVenhance.IsZ2Periodic F)
    (hweak : ∀ c, D.weak.coefficient t c =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus
          (fun x => κ * AVenhance.spaceLap (realFourierModeAmbientExpansion N c) x -
            classicalTransport b (realFourierModeAmbientExpansion N c) x)))
    (hforce : D.forcing t = modeProjectionCoefficients
      (RealFourierDimension N) (realFourierModeFin N)
      (AVenhance.Infra.Torus.periodicToTorus F))
    (c : Coefficients (RealFourierDimension N)) :
    D.transformedForcing (realFourierWordDerivativeMap N w) (fun _ => c) t =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus
          (fun x => classicalWordDerivative w F x -
            classicalWordTransportCommutatorExpansion w b
              (realFourierModeAmbientExpansion N c) x)) := by
  let u := realFourierModeAmbientExpansion N c
  let L := realFourierWordDerivativeMap N w
  let gen (v : Coefficients (RealFourierDimension N)) : Vec 2 → ℝ :=
    fun x => κ * AVenhance.spaceLap (realFourierModeAmbientExpansion N v) x -
      classicalTransport b (realFourierModeAmbientExpansion N v) x
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u] using realFourierModeAmbientExpansion_contDiff N c
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using realFourierModeAmbientExpansion_periodic N c
  have hGenSmooth (v : Coefficients (RealFourierDimension N)) :
      ContDiff ℝ (⊤ : ℕ∞) (gen v) := by
    have hv0 : ContDiff ℝ ⊤ (realFourierModeAmbientExpansion N v) :=
      realFourierModeAmbientExpansion_contDiff N v
    have hv : ContDiff ℝ (⊤ : ℕ∞) (realFourierModeAmbientExpansion N v) :=
      hv0.of_le (by simp)
    have hlap := GalerkinDerivative.classicalSpaceLap_contDiff _ hv
    have htransport := GalerkinDerivative.classicalTransport_contDiff b _ hb hv
    exact (contDiff_const.mul hlap).sub htransport
  have hGenPeriodic (v : Coefficients (RealFourierDimension N)) :
      AVenhance.IsZ2Periodic (gen v) := by
    have hvper := realFourierModeAmbientExpansion_periodic N v
    intro k x
    simp only [gen]
    have hlap := GalerkinDerivative.classicalSpaceLap_periodic hvper k x
    have htransport := GalerkinDerivative.classicalTransport_periodic b _ hbp hvper k x
    change κ * (fun y => AVenhance.spaceLap
      (realFourierModeAmbientExpansion N v) y) (x + AVenhance.latticeShift k) -
      classicalTransport b (realFourierModeAmbientExpansion N v)
        (x + AVenhance.latticeShift k) = _
    rw [hlap, htransport]
  have hwordU : classicalWordDerivative w u =
      realFourierModeAmbientExpansion N (L c) := by
    simpa [u, L, realFourierWordDerivativeMap_apply] using
      classicalWordDerivative_realFourierModeAmbientExpansion N w c
  have hwordFproj := realFourierWordDerivativeMap_projection N w F hF hFper
  have hwordGenProj := realFourierWordDerivativeMap_projection N w (gen c)
    (hGenSmooth c) (hGenPeriodic c)
  have hmemF : MemLp
      (AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w F))
        2 (volume : Measure Torus) :=
    memLp_periodicToTorus_real
      (classicalWordDerivative_contDiff w F hF).continuous
      (GalerkinDerivative.classicalWordDerivative_periodic w F hFper)
  have hmemGen : MemLp
      (AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w (gen c)))
        2 (volume : Measure Torus) :=
    memLp_periodicToTorus_real
      (classicalWordDerivative_contDiff w (gen c) (hGenSmooth c)).continuous
      (GalerkinDerivative.classicalWordDerivative_periodic w (gen c) (hGenPeriodic c))
  have hmemGenW : MemLp (AVenhance.Infra.Torus.periodicToTorus (gen (L c)))
      2 (volume : Measure Torus) :=
    memLp_periodicToTorus_real (hGenSmooth (L c)).continuous (hGenPeriodic (L c))
  have hmemSum : MemLp
      (AVenhance.Infra.Torus.periodicToTorus
        (fun x => classicalWordDerivative w F x + classicalWordDerivative w (gen c) x))
      2 (volume : Measure Torus) := by
    have heq : (fun x : Torus =>
        AVenhance.Infra.Torus.periodicToTorus
          (fun x => classicalWordDerivative w F x + classicalWordDerivative w (gen c) x) x) =
        AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w F) +
          AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w (gen c)) := by
      funext x
      rfl
    exact (memLp_congr_ae (show
      (fun x : Torus => AVenhance.Infra.Torus.periodicToTorus
        (fun x => classicalWordDerivative w F x +
          classicalWordDerivative w (gen c) x) x) =ᵐ[volume]
        AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w F) +
          AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w (gen c)) by
          filter_upwards with x
          exact congrFun heq x)).1 (hmemF.add hmemGen)
  have hweakU := hweak c
  have hweakLU := hweak (L c)
  have htransformed : D.transformedForcing L (fun _ => c) t =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w F)) +
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w (gen c))) -
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus (gen (L c))) := by
    change L (D.forcing t) + L (D.weak.coefficient t c) -
      D.weak.coefficient t (L c) = _
    rw [hforce, hwordFproj, hweakU, hwordGenProj, hweakLU]
  have hlinear :
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus
            (fun x => classicalWordDerivative w F x + classicalWordDerivative w (gen c) x -
              gen (L c) x)) =
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
            (AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w F)) +
          modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
            (AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w (gen c))) -
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
            (AVenhance.Infra.Torus.periodicToTorus (gen (L c))) := by
    have hsub := realFourierModeProjectionCoefficients_sub N hmemSum hmemGenW
    have hsum := realFourierModeProjectionCoefficients_add N hmemF hmemGen
    have htorusSub : AVenhance.Infra.Torus.periodicToTorus
        (fun x => classicalWordDerivative w F x +
          classicalWordDerivative w (gen c) x - gen (L c) x) =
        AVenhance.Infra.Torus.periodicToTorus
          (fun x => classicalWordDerivative w F x + classicalWordDerivative w (gen c) x) -
          AVenhance.Infra.Torus.periodicToTorus (gen (L c)) := by
      funext x
      rfl
    have htorusSum : AVenhance.Infra.Torus.periodicToTorus
        (fun x => classicalWordDerivative w F x +
          classicalWordDerivative w (gen c) x) =
        AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w F) +
          AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w (gen c)) := by
      funext x
      rfl
    rw [htorusSub, hsub, htorusSum, hsum]
  have hsource :
      (fun x => classicalWordDerivative w F x + classicalWordDerivative w (gen c) x -
        gen (L c) x) =
      (fun x => classicalWordDerivative w F x -
        classicalWordTransportCommutatorExpansion w b u x) := by
    have hLap := classicalWordDerivative_spaceLap w u hu
    have htransport := classicalWordDerivative_transport_eq_commutatorExpansion
      w b u hb hu
    have hconst := classicalWordDerivative_const_mul w κ
      (fun x => AVenhance.spaceLap u x) (GalerkinDerivative.classicalSpaceLap_contDiff u hu)
    have hsub := classicalWordDerivative_sub w
      (fun x => κ * AVenhance.spaceLap u x) (classicalTransport b u)
      ((contDiff_const.mul (GalerkinDerivative.classicalSpaceLap_contDiff u hu)))
      (GalerkinDerivative.classicalTransport_contDiff b u hb hu)
    have hwordU' : classicalWordDerivative w u =
        realFourierModeAmbientExpansion N (L c) := hwordU
    funext x
    have hLapx := congrFun hLap x
    have hconstx := congrFun hconst x
    have hsubx := congrFun hsub x
    have htransportx := htransport x
    simp only [hwordU'] at hLapx hconstx hsubx
    have hT : classicalWordDerivative w (classicalTransport b u) x -
        classicalTransport b (classicalWordDerivative w u) x =
        classicalWordTransportCommutatorExpansion w b u x := by
      simpa [classicalWordTransportCommutatorExpansion, classicalTransport,
        Fin.sum_univ_two] using htransportx
    rw [hsubx, hconstx, hLapx]
    rw [show gen (L c) x = κ * AVenhance.spaceLap
        (classicalWordDerivative w u) x -
          classicalTransport b (classicalWordDerivative w u) x by
          simp [gen, ← hwordU']]
    have hlapEq : AVenhance.spaceLap
        (realFourierModeAmbientExpansion N (L c)) x =
        AVenhance.spaceLap (classicalWordDerivative w u) x :=
      (hLapx.symm.trans (congrFun hLap x))
    rw [hlapEq]
    linear_combination -hT
  rw [htransformed, ← hlinear, hsource]

end AVenhance.Infra.Classical

end
