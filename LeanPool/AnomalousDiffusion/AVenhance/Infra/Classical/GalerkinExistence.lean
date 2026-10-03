/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinProblem
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.TimeEnergy

/-! All-order forced Galerkin estimates and classical-limit construction. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalExistenceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalExistenceMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalExistenceProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance classicalExistenceProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

namespace AVenhance.Infra.Classical

/-- The total number of component commutator terms across all derivative words of order at most
`s`. -/
def classicalWordCommutatorCount (s : ℕ) : ℕ :=
  ∑ a : ClassicalDerivativeWordIndex s,
    2 * (classicalWordCommutatorSplits
      (classicalDerivativeWordOfIndex a)).length

theorem classicalWordCommutatorCount_bounds_word (s : ℕ)
    (w : List (Fin 2)) (hw : w.length ≤ s) :
    2 * (classicalWordCommutatorSplits w).length ≤ classicalWordCommutatorCount s := by
  classical
  let a := classicalDerivativeWordIndexOfList w hw
  let term : ClassicalDerivativeWordIndex s → ℕ := fun q =>
    2 * (classicalWordCommutatorSplits
      (classicalDerivativeWordOfIndex q)).length
  have hsingle : 2 * (classicalWordCommutatorSplits
      (classicalDerivativeWordOfIndex a)).length ≤
      ∑ q : ClassicalDerivativeWordIndex s,
        2 * (classicalWordCommutatorSplits
          (classicalDerivativeWordOfIndex q)).length :=
    by
      change term a ≤ ∑ q : ClassicalDerivativeWordIndex s, term q
      exact Finset.single_le_sum (f := term)
        (fun q hq => Nat.zero_le _) (Finset.mem_univ a)
  have hword := classicalDerivativeWordOfIndexOfList w hw
  simpa [classicalWordCommutatorCount, a, hword] using hsingle

theorem GalerkinExistence.classicalListMapSum_mono {α : Type*} (L : List α)
    (f g : α → ℝ) (h : ∀ a ∈ L, f a ≤ g a) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have htail : ∀ z ∈ L, f z ≤ g z := by
        intro z hz
        exact h z (by simp [hz])
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h a (by simp)) (ih htail)

theorem GalerkinExistence.classicalWordDerivative_periodic_local (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (classicalWordDerivative w f) := by
  induction w with
  | nil => exact hper
  | cons i w ih =>
      exact AVenhance.Infra.Classical.periodic_spaceGrad_component ih i

theorem GalerkinExistence.classicalTransport_smooth_local (b : Vec 2 → Vec 2)
    (u : Vec 2 → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
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

theorem GalerkinExistence.classicalTransport_periodic_local (b : Vec 2 → Vec 2)
    (u : Vec 2 → ℝ) (hb : AVenhance.IsZ2Periodic b)
    (hu : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic (classicalTransport b u) := by
  intro k x
  unfold classicalTransport
  change ∑ j : Fin 2, b (x + AVenhance.latticeShift k) j *
      AVenhance.spaceGrad u (x + AVenhance.latticeShift k) j = _
  apply Finset.sum_congr rfl
  intro j hj
  have hbval := congrFun (hb k x) j
  have hg := AVenhance.Infra.Classical.periodic_spaceGrad_component hu j k x
  change AVenhance.spaceGrad u (x + AVenhance.latticeShift k) j =
    AVenhance.spaceGrad u x j at hg
  rw [hbval, hg]

/-- A single transformed forcing component is bounded by the physical source derivative plus the
commutator multiplicity times the derivative-family state norm. -/
theorem classicalWordResidualProjection_norm_le
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (N s : ℕ) (w : List (Fin 2)) (hw : w.length ≤ s)
    (c : Coefficients (RealFourierDimension N)) {t BF BD Y : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hBF : 0 ≤ BF) (hBD : 0 ≤ BD) (hY : 0 ≤ Y)
    (hFbound : ∀ x, ‖classicalWordDerivative w (F t) x‖ ≤ BF)
    (hDbound : ∀ v, v.length ≤ s → ∀ j x,
      ‖classicalWordDerivative v (fun y => AVenhance.streamVel φ t y j) x‖ ≤ BD)
    (hcoeff : ∀ v, v.length ≤ s →
      ‖realFourierWordDerivativeMap N v c‖ ≤ Y) :
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (AVenhance.Infra.Torus.periodicToTorus
        (fun x => classicalWordDerivative w (F t) x -
          classicalWordTransportCommutatorExpansion w
            (fun x => AVenhance.streamVel φ t x)
            (realFourierModeAmbientExpansion N c) x))‖ ≤
      BF + (classicalWordCommutatorCount s : ℝ) * BD * Y := by
  let b : Vec 2 → Vec 2 := fun x => AVenhance.streamVel φ t x
  let u : Vec 2 → ℝ := realFourierModeAmbientExpansion N c
  have hb0 : ContDiff ℝ (⊤ : ℕ∞) b := by
    have hjoint := (streamVel_smoothPeriodic φ hφ).smooth
    have hsection : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => Function.uncurry (AVenhance.streamVel φ) (t, x)) :=
      hjoint.comp (contDiff_const.prodMk contDiff_id)
    simpa [b, Function.uncurry] using hsection
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := hb0
  have hbp : AVenhance.IsZ2Periodic b := by
    intro k x
    change AVenhance.streamVel φ t (x + AVenhance.latticeShift k) =
      AVenhance.streamVel φ t x
    simpa using (streamVel_smoothPeriodic φ hφ).periodic 0 k t x
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u] using realFourierModeAmbientExpansion_contDiff N c
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using realFourierModeAmbientExpansion_periodic N c
  have hFw : ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative w (F t)) :=
    classicalWordDerivative_contDiff w (F t)
      (AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hF ht.1)
  have hFwp : AVenhance.IsZ2Periodic (classicalWordDerivative w (F t)) :=
    GalerkinExistence.classicalWordDerivative_periodic_local w (F t) (hFper t ht.1)
  have hprojF := realFourierProjectionCoefficients_norm_le_uniform N
    (classicalWordDerivative w (F t)) hFw.continuous hFwp hBF hFbound
  have htransportSmooth := GalerkinExistence.classicalTransport_smooth_local b u hb hu
  have htransportPer := GalerkinExistence.classicalTransport_periodic_local b u hbp hup
  have hwordSmooth := classicalWordDerivative_contDiff w
    (classicalTransport b u) htransportSmooth
  have hwordPer := GalerkinExistence.classicalWordDerivative_periodic_local w
    (classicalTransport b u) htransportPer
  have htransportDerivSmooth := classicalWordDerivative_contDiff w u hu
  have htransportDerivPer := GalerkinExistence.classicalWordDerivative_periodic_local w u hup
  have hlastTransportSmooth := GalerkinExistence.classicalTransport_smooth_local b
    (classicalWordDerivative w u) hb htransportDerivSmooth
  have hlastTransportPer := GalerkinExistence.classicalTransport_periodic_local b
    (classicalWordDerivative w u) hbp htransportDerivPer
  have hcommEq : classicalWordTransportCommutatorExpansion w b u =
      fun x => classicalWordDerivative w (classicalTransport b u) x -
        classicalTransport b (classicalWordDerivative w u) x := by
    funext x
    have h := classicalWordDerivative_transport_eq_commutatorExpansion w b u hb hu x
    simpa [classicalWordTransportCommutatorExpansion, classicalTransport] using h.symm
  have hcommSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (classicalWordTransportCommutatorExpansion w b u) := by
    rw [hcommEq]
    exact hwordSmooth.sub hlastTransportSmooth
  have hcommPer : AVenhance.IsZ2Periodic
      (classicalWordTransportCommutatorExpansion w b u) := by
    rw [hcommEq]
    intro k x
    change classicalWordDerivative w (classicalTransport b u)
        (x + AVenhance.latticeShift k) -
        classicalTransport b (classicalWordDerivative w u)
          (x + AVenhance.latticeShift k) = _
    rw [hwordPer k x, hlastTransportPer k x]
  have hmemF : MemLp
      (AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w (F t)))
      2 (volume : Measure Torus) :=
    memLp_periodicToTorus_real hFw.continuous hFwp
  have hmemComm : MemLp
      (AVenhance.Infra.Torus.periodicToTorus
        (classicalWordTransportCommutatorExpansion w b u))
      2 (volume : Measure Torus) :=
    memLp_periodicToTorus_real hcommSmooth.continuous hcommPer
  have htorusSub : AVenhance.Infra.Torus.periodicToTorus
      (fun x => classicalWordDerivative w (F t) x -
        classicalWordTransportCommutatorExpansion w b u x) =
      AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w (F t)) -
        AVenhance.Infra.Torus.periodicToTorus
          (classicalWordTransportCommutatorExpansion w b u) := by
    funext x
    rfl
  have hprojectionSub := realFourierModeProjectionCoefficients_sub N hmemF hmemComm
  have hDboundSplit : ∀ j p, p ∈ classicalWordCommutatorSplits w → ∀ x,
      |classicalWordDerivative p.1 (fun y => b y j) x| ≤ BD := by
    intro j p hp x
    have hlen := classicalWordCommutatorSplits_length w hp
    have hword : p.1.length ≤ s := by omega
    have h := hDbound p.1 hword j x
    simpa [b, Real.norm_eq_abs] using h
  have hcommProjection := classicalWordTransportCommutatorExpansion_projection_norm_le
    N w b c hBD hb hbp hDboundSplit
  have htermBound (j : Fin 2) (p : List (Fin 2) × List (Fin 2))
      (hp : p ∈ classicalWordCommutatorSplits w) :
      ‖realFourierWordDerivativeMap N (j :: p.2) c‖ ≤ Y := by
    apply hcoeff
    have hlen := classicalWordCommutatorSplits_right_length_lt w hp
    simp only [List.length_cons]
    omega
  have hlistBound (j : Fin 2) :
      ((classicalWordCommutatorSplits w).map fun p =>
        BD * ‖realFourierWordDerivativeMap N (j :: p.2) c‖).sum ≤
        ((classicalWordCommutatorSplits w).length : ℝ) * BD * Y := by
    calc
      _ ≤ ((classicalWordCommutatorSplits w).map fun _ => BD * Y).sum :=
        GalerkinExistence.classicalListMapSum_mono _ _ _ (by
          intro p hp
          exact mul_le_mul_of_nonneg_left (htermBound j p hp) hBD)
      _ = ((classicalWordCommutatorSplits w).length : ℝ) * BD * Y := by
        simp [List.sum_replicate]
        ring
  have hcommSmall :
      (∑ j : Fin 2, ((classicalWordCommutatorSplits w).map fun p =>
        BD * ‖realFourierWordDerivativeMap N (j :: p.2) c‖).sum) ≤
        (classicalWordCommutatorCount s : ℝ) * BD * Y := by
    rw [Fin.sum_univ_two]
    have hcount := classicalWordCommutatorCount_bounds_word s w hw
    have hcountR : (2 : ℝ) * (classicalWordCommutatorSplits w).length ≤
        (classicalWordCommutatorCount s : ℝ) := by
      exact_mod_cast hcount
    calc
      _ ≤ ((classicalWordCommutatorSplits w).length : ℝ) * BD * Y +
          ((classicalWordCommutatorSplits w).length : ℝ) * BD * Y :=
        add_le_add (hlistBound 0) (hlistBound 1)
      _ = (2 * (classicalWordCommutatorSplits w).length : ℝ) * BD * Y := by
        ring
      _ ≤ (classicalWordCommutatorCount s : ℝ) * BD * Y := by
        calc
          (2 * (classicalWordCommutatorSplits w).length : ℝ) * BD * Y =
              (2 * (classicalWordCommutatorSplits w).length : ℝ) * (BD * Y) := by ring
          _ ≤ (classicalWordCommutatorCount s : ℝ) * (BD * Y) :=
            mul_le_mul_of_nonneg_right hcountR (mul_nonneg hBD hY)
          _ = (classicalWordCommutatorCount s : ℝ) * BD * Y := by ring
  calc
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus
          (fun x => classicalWordDerivative w (F t) x -
            classicalWordTransportCommutatorExpansion w b u x))‖ =
      ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w (F t))) -
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus
            (classicalWordTransportCommutatorExpansion w b u))‖ := by
      rw [htorusSub, hprojectionSub]
    _ ≤ ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w (F t)))‖ +
        ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus
            (classicalWordTransportCommutatorExpansion w b u))‖ := norm_sub_le _ _
    _ ≤ BF + (classicalWordCommutatorCount s : ℝ) * BD * Y := by
      exact add_le_add hprojF (hcommProjection.trans hcommSmall)

/-- The transformed source of a classical Galerkin path is the projected differentiated
forcing minus the transport commutator. -/
theorem classicalForcedGalerkinData_transformedForcing_eq_wordResidual
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (N : ℕ) (u : C(Icc (0 : ℝ) 1, Coefficients (RealFourierDimension N)))
    (w : List (Fin 2)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let D := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N
    D.transformedForcing (realFourierWordDerivativeMap N w)
      (AVenhance.Infra.ODE.extendCurve (by norm_num) u) t =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus
          (fun x => classicalWordDerivative w (F t) x -
            classicalWordTransportCommutatorExpansion w
              (fun x => AVenhance.streamVel φ t x)
              (realFourierModeAmbientExpansion N
                (AVenhance.Infra.ODE.extendCurve (by norm_num) u t)) x)) := by
  dsimp
  let D := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N
  let b : Vec 2 → Vec 2 := fun x => AVenhance.streamVel φ t x
  let c : Coefficients (RealFourierDimension N) :=
    AVenhance.Infra.ODE.extendCurve (by norm_num) u t
  have ht0 : 0 ≤ t := ht.1
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    have hjoint := (streamVel_smoothPeriodic φ hφ).smooth
    have hsection : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => Function.uncurry (AVenhance.streamVel φ) (t, x)) :=
      hjoint.comp (contDiff_const.prodMk contDiff_id)
    simpa [b, Function.uncurry] using hsection
  have hbp : AVenhance.IsZ2Periodic b := by
    intro k x
    change AVenhance.streamVel φ t (x + AVenhance.latticeShift k) =
      AVenhance.streamVel φ t x
    simpa using (streamVel_smoothPeriodic φ hφ).periodic 0 k t x
  have hFt : ContDiff ℝ (⊤ : ℕ∞) (F t) :=
    AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hF ht0
  have hweak : ∀ a, D.weak.coefficient t a =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus
          (fun x => κ * AVenhance.spaceLap
              (realFourierModeAmbientExpansion N a) x -
            classicalTransport b (realFourierModeAmbientExpansion N a) x)) := by
    intro a
    change frozenWeakFormCoefficient (fun s x => AVenhance.streamVel φ s x) κ
      (realFourierModeFin N) (realFourierModeGradFin N) t a = _
    exact frozenWeakFormCoefficient_eq_projectedGenerator N
      (fun s x => AVenhance.streamVel φ s x) κ t ht a (by
        have h := (streamVel_smoothPeriodic φ hφ).smooth.continuous
        exact h.comp (continuous_const.prodMk continuous_id))
  have hforce : D.forcing t = modeProjectionCoefficients
      (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus (F t)) := by
    change classicalForcingCoefficients N F t = _
    simp [classicalForcingCoefficients, max_eq_left ht0]
  have hword := ForcedGalerkinData.transformedForcing_eq_wordResidual
    D w t κ b (F t) hb hbp hFt (hFper t ht0) hweak hforce c
  simpa [b, c, D, ForcedGalerkinData.transformedForcing] using hword

/-- The forcing in the finite product of all derivative equations has linear growth in the
combined derivative state, with constants independent of the Fourier cutoff. -/
theorem classicalForcedGalerkinDerivativeFamily_forcing_bound
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (N s : ℕ) (u : C(Icc (0 : ℝ) 1, Coefficients (RealFourierDimension N)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {BF BD : ℝ} (hBF : 0 ≤ BF) (hBD : 0 ≤ BD)
    (hFbound : ∀ w, w.length ≤ s → ∀ x,
      ‖classicalWordDerivative w (F t) x‖ ≤ BF)
    (hDbound : ∀ w, w.length ≤ s → ∀ j x,
      ‖classicalWordDerivative w (fun y => AVenhance.streamVel φ t y j) x‖ ≤ BD) :
    let word : ClassicalDerivativeWordIndex s → List (Fin 2) :=
      classicalDerivativeWordOfIndex
    let V := energyFamilyPath (fun a : ClassicalDerivativeWordIndex s =>
      ForcedGalerkinData.mapPath (realFourierWordDerivativeMap N (word a)) u)
    let D := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N
    ‖(D.wordDerivativeFamilyData u word).forcing t‖ ≤
      ((Fintype.card (ClassicalDerivativeWordIndex s) : ℝ) *
          (classicalWordCommutatorCount s : ℝ) * BD) *
          ‖AVenhance.Infra.ODE.extendCurve (by norm_num) V t‖ +
        (Fintype.card (ClassicalDerivativeWordIndex s) : ℝ) * BF := by
  classical
  dsimp
  let word : ClassicalDerivativeWordIndex s → List (Fin 2) :=
    classicalDerivativeWordOfIndex
  let D := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N
  let V := energyFamilyPath (fun a : ClassicalDerivativeWordIndex s =>
    ForcedGalerkinData.mapPath (realFourierWordDerivativeMap N (word a)) u)
  let Y := AVenhance.Infra.ODE.extendCurve (by norm_num) V
  let c : Coefficients (RealFourierDimension N) :=
    AVenhance.Infra.ODE.extendCurve (by norm_num) u t
  let stateNorm : ℝ := ‖Y t‖
  let A₀ : ℝ := (classicalWordCommutatorCount s : ℝ) * BD
  have hstate : Y t = WithLp.toLp 2 (fun a : ClassicalDerivativeWordIndex s =>
      realFourierWordDerivativeMap N (word a) c) := by
    rw [show Y t = V ⟨t, ht⟩ from
      AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) V ht]
    ext a
    simp [V, energyFamilyPath, ForcedGalerkinData.mapPath, c,
      AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) u ht]
  have hcoefficientBound (v : List (Fin 2)) (hv : v.length ≤ s) :
      ‖realFourierWordDerivativeMap N v c‖ ≤ stateNorm := by
    let a := classicalDerivativeWordIndexOfList v hv
    have hcoord := PiLp.norm_apply_le (x := Y t) a
    have hcoord' : (Y t).ofLp a = realFourierWordDerivativeMap N v c := by
      rw [hstate]
      have hword : word a = v := by
        simpa [word, a] using classicalDerivativeWordOfIndexOfList v hv
      change realFourierWordDerivativeMap N (word a) c =
        realFourierWordDerivativeMap N v c
      rw [hword]
    change ‖(Y t).ofLp a‖ ≤ ‖Y t‖ at hcoord
    rw [hcoord'] at hcoord
    simpa [stateNorm] using hcoord
  have hBFsource (w : List (Fin 2)) (hw : w.length ≤ s) (x : Vec 2) :
      ‖classicalWordDerivative w (F t) x‖ ≤ BF := hFbound w hw x
  have hBDsource (w : List (Fin 2)) (hw : w.length ≤ s) (j : Fin 2) (x : Vec 2) :
      ‖classicalWordDerivative w
          (fun y => AVenhance.streamVel φ t y j) x‖ ≤ BD := hDbound w hw j x
  have hcomponent (a : ClassicalDerivativeWordIndex s) :
      ‖((D.wordDerivativeFamilyData u word).forcing t).ofLp a‖ ≤
        BF + A₀ * stateNorm := by
    change ‖D.transformedForcing (realFourierWordDerivativeMap N (word a))
      (AVenhance.Infra.ODE.extendCurve (by norm_num) u) t‖ ≤ _
    have hres := classicalForcedGalerkinData_transformedForcing_eq_wordResidual
      φ hφ κ hκ F hF hFper θ₀ hθ₀ N u (word a) ht
    have hresBound := classicalWordResidualProjection_norm_le φ hφ F hF hFper
      N s (word a) (classicalDerivativeWordOfIndex_length_le a)
      c ht hBF hBD (norm_nonneg _) (hBFsource (word a)
        (classicalDerivativeWordOfIndex_length_le a)) hBDsource
      hcoefficientBound
    rw [hres]
    simpa [A₀, c, stateNorm, word] using hresBound
  have hfamilySq :
      (∑ a : ClassicalDerivativeWordIndex s,
        ‖((D.wordDerivativeFamilyData u word).forcing t).ofLp a‖ ^ 2) ≤
      (∑ a : ClassicalDerivativeWordIndex s,
        ‖((D.wordDerivativeFamilyData u word).forcing t).ofLp a‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun a ha => norm_nonneg _
  have hsumNonneg : 0 ≤ ∑ a : ClassicalDerivativeWordIndex s,
      ‖((D.wordDerivativeFamilyData u word).forcing t).ofLp a‖ :=
    Finset.sum_nonneg fun a ha => norm_nonneg _
  have hsumComponent :
      (∑ a : ClassicalDerivativeWordIndex s,
        ‖((D.wordDerivativeFamilyData u word).forcing t).ofLp a‖) ≤
      (Fintype.card (ClassicalDerivativeWordIndex s) : ℝ) *
        (BF + A₀ * stateNorm) := by
    calc
      _ ≤ ∑ _a : ClassicalDerivativeWordIndex s, (BF + A₀ * stateNorm) := by
        apply Finset.sum_le_sum
        intro a ha
        exact hcomponent a
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  calc
    ‖(D.wordDerivativeFamilyData u word).forcing t‖ =
        Real.sqrt (∑ a : ClassicalDerivativeWordIndex s,
          ‖((D.wordDerivativeFamilyData u word).forcing t).ofLp a‖ ^ 2) := by
      rw [PiLp.norm_eq_of_L2]
    _ ≤ Real.sqrt ((∑ a : ClassicalDerivativeWordIndex s,
          ‖((D.wordDerivativeFamilyData u word).forcing t).ofLp a‖) ^ 2) :=
      Real.sqrt_le_sqrt hfamilySq
    _ = ∑ a : ClassicalDerivativeWordIndex s,
          ‖((D.wordDerivativeFamilyData u word).forcing t).ofLp a‖ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsumNonneg]
    _ ≤ (Fintype.card (ClassicalDerivativeWordIndex s) : ℝ) *
          (BF + A₀ * stateNorm) := hsumComponent
    _ = ((Fintype.card (ClassicalDerivativeWordIndex s) : ℝ) *
          (classicalWordCommutatorCount s : ℝ) * BD) * stateNorm +
        (Fintype.card (ClassicalDerivativeWordIndex s) : ℝ) * BF := by
      simp [A₀, stateNorm]
      ring

/-! Initial bounds for derivative families. -/

/-- The initial state in a finite derivative family is uniformly bounded by the sup norms of the
corresponding derivatives of the datum. -/
theorem classicalForcedGalerkinDerivativeFamily_initial_norm_le
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀)
    (N s : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ w, w.length ≤ s → ∀ x,
      ‖classicalWordDerivative w θ₀ x‖ ≤ B)
    (u : C(Icc (0 : ℝ) 1, Coefficients (RealFourierDimension N))) :
    ‖(classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).wordDerivativeFamilyData
        u (fun a : ClassicalDerivativeWordIndex s =>
          classicalDerivativeWordOfIndex a) |>.initial‖ ≤
      Real.sqrt (Fintype.card (ClassicalDerivativeWordIndex s) : ℝ) * B := by
  classical
  let word : ClassicalDerivativeWordIndex s → List (Fin 2) :=
    classicalDerivativeWordOfIndex
  let D := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N
  let Df := D.wordDerivativeFamilyData u word
  have hbase : D.initial = modeProjectionCoefficients (RealFourierDimension N)
      (realFourierModeFin N) (AVenhance.Infra.Torus.periodicToTorus θ₀) := by
    change ((classicalFrozenDriftProblem φ hφ κ hκ θ₀ hθ₀).galerkinData N).initial = _
    rfl
  have hcoord (a : ClassicalDerivativeWordIndex s) :
      ‖Df.initial.ofLp a‖ ≤ B := by
    have hcoordEq : Df.initial.ofLp a =
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus
            (classicalWordDerivative (word a) θ₀)) := by
      rw [show Df.initial.ofLp a =
        realFourierWordDerivativeMap N (word a) D.initial by
          simp [Df, word, ForcedGalerkinData.wordDerivativeFamilyData,
            ForcedGalerkinData.family]]
      rw [hbase]
      exact realFourierWordDerivativeMap_projection N (word a) θ₀ hθ₀ hθ₀per
    rw [hcoordEq]
    exact realFourierProjectionCoefficients_norm_le_uniform N
      (classicalWordDerivative (word a) θ₀)
      (classicalWordDerivative_contDiff (word a) θ₀ hθ₀).continuous
      (GalerkinExistence.classicalWordDerivative_periodic_local (word a) θ₀ hθ₀per)
      hB (hbound (word a) (classicalDerivativeWordOfIndex_length_le a))
  have hsum :
      (∑ a : ClassicalDerivativeWordIndex s, ‖Df.initial.ofLp a‖ ^ 2) ≤
        (Fintype.card (ClassicalDerivativeWordIndex s) : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _a : ClassicalDerivativeWordIndex s, (B ^ 2) := by
        apply Finset.sum_le_sum
        intro a ha
        exact (sq_le_sq₀ (norm_nonneg _) hB).2 (hcoord a)
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  calc
    ‖Df.initial‖ = Real.sqrt (∑ a : ClassicalDerivativeWordIndex s,
        ‖Df.initial.ofLp a‖ ^ 2) := by rw [PiLp.norm_eq_of_L2]
    _ ≤ Real.sqrt ((Fintype.card (ClassicalDerivativeWordIndex s) : ℝ) * B ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Fintype.card (ClassicalDerivativeWordIndex s) : ℝ) * B := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hB]

/-- Every fixed finite order of the differentiated Galerkin solution is bounded uniformly over
all frequency cutoffs and all times in `[0,1]`. -/
theorem classicalGalerkin_derivativeFamily_uniform_bound
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N t, t ∈ Icc (0 : ℝ) 1 →
      ‖AVenhance.Infra.ODE.extendCurve (by norm_num)
        (energyFamilyPath (fun a : ClassicalDerivativeWordIndex s =>
          ForcedGalerkinData.mapPath
            (realFourierWordDerivativeMap N (classicalDerivativeWordOfIndex a))
            (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N))) t‖ ≤ C := by
  let Fθ : ℝ → Vec 2 → ℝ := fun _ => θ₀
  have hFθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry Fθ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    change ContDiffOn ℝ (⊤ : ℕ∞) (θ₀ ∘ Prod.snd)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)
    exact (hθ₀.comp contDiff_snd).contDiffOn
  have hFθper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (Fθ t) :=
    fun _ _ => hθ₀per
  obtain ⟨Bθ, hBθ, hθboundT⟩ :=
    exists_classicalForcing_allWordDerivative_uniform_bound Fθ hFθ hFθper s
  have hθbound : ∀ w, w.length ≤ s → ∀ x,
      ‖classicalWordDerivative w θ₀ x‖ ≤ Bθ := by
    intro w hw x
    have h := hθboundT w hw 0 (by norm_num) x
    simpa [Fθ] using h
  obtain ⟨BF, hBF, hFbound⟩ :=
    exists_classicalForcing_allWordDerivative_uniform_bound F hF hFper s
  obtain ⟨BD, hBD, hDbound⟩ :=
    exists_streamVel_allWordDerivative_uniform_bound φ hφ s
  classical
  let word : ClassicalDerivativeWordIndex s → List (Fin 2) :=
    classicalDerivativeWordOfIndex
  let cardR : ℝ := Fintype.card (ClassicalDerivativeWordIndex s)
  let A : ℝ := cardR * (classicalWordCommutatorCount s : ℝ) * BD
  let G : ℝ := cardR * BF
  let E₀ : ℝ := Real.sqrt cardR * Bθ
  have hcard : 0 ≤ cardR := by positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg hcard (Nat.cast_nonneg _)) hBD
  have hG : 0 ≤ G := by dsimp [G]; exact mul_nonneg hcard hBF
  have hE₀ : 0 ≤ E₀ := by dsimp [E₀]; positivity
  let c : ℝ := (max (positiveCutoffDriftConstant (AVenhance.streamVel φ)
      (classicalFrozenDriftProblem φ hφ κ hκ θ₀ hθ₀).drift_bounded) 0 ^ 2 / κ) +
      2 * A + 1
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let K : ℝ := (E₀ ^ 2 + G ^ 2) * Real.exp c
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨Real.sqrt K, Real.sqrt_nonneg K, ?_⟩
  intro N t ht
  let u := classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N
  let D := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N
  let V := energyFamilyPath (fun a : ClassicalDerivativeWordIndex s =>
    ForcedGalerkinData.mapPath (realFourierWordDerivativeMap N (word a)) u)
  let Df := D.wordDerivativeFamilyData u word
  have hu : D.ode.IsSolution u :=
    classicalGalerkinCoefficientPath_isSolution φ hφ κ hκ F hF θ₀ hθ₀ N
  have hVsol : Df.ode.IsSolution V := by
    change (D.wordDerivativeFamilyData u word).ode.IsSolution
      (energyFamilyPath (fun a => ForcedGalerkinData.mapPath
        (realFourierWordDerivativeMap N (word a)) u))
    exact D.wordDerivativeFamilyPath_isSolution u hu word
  have hforcing' : ∀ t' ∈ Icc (0 : ℝ) 1,
      ‖Df.forcing t'‖ ≤ A * ‖AVenhance.Infra.ODE.extendCurve (by norm_num) V t'‖ + G := by
    intro t' ht'
    have hb := classicalForcedGalerkinDerivativeFamily_forcing_bound
      φ hφ κ hκ F hF hFper θ₀ hθ₀ N s u ht' hBF hBD
        (fun w hw x => hFbound w hw t' ht' x)
        (fun w hw j x => hDbound w hw j t' ht' x)
    simpa [A, G, cardR, V, Df, word] using hb
  have hEnergy := Df.uniformEnergyEstimateOfLinearGrowth V hVsol hA hG hforcing'
  have hinit := classicalForcedGalerkinDerivativeFamily_initial_norm_le
    φ hφ κ hκ F hF θ₀ hθ₀ hθ₀per N s hBθ hθbound u
  have hinit' : ‖Df.initial‖ ≤ E₀ := by
    simpa [Df, D, word, E₀, cardR] using hinit
  have hinitSq : ‖Df.initial‖ ^ 2 ≤ E₀ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hE₀).2 hinit'
  let cN : ℝ := max Df.weak.driftBound 0 ^ 2 / Df.weak.diffusivity + 2 * A + 1
  have hcN : cN = c := by
    let P := classicalFrozenDriftProblem φ hφ κ hκ θ₀ hθ₀
    have hpositive : 0 ≤ positiveCutoffDriftConstant (AVenhance.streamVel φ)
        P.drift_bounded :=
      positiveCutoffDriftForm_bound N (AVenhance.streamVel φ)
        P.drift_measurable P.drift_bounded |>.1
    have hdrift : Df.weak.driftBound =
        positiveCutoffDriftConstant (AVenhance.streamVel φ) P.drift_bounded := by
      change max D.weak.driftBound 0 = _
      have hDdrift : D.weak.driftBound =
          positiveCutoffDriftConstant (AVenhance.streamVel φ) P.drift_bounded := by
        change (P.galerkinData N).driftBound = _
        rfl
      rw [hDdrift]
      exact max_eq_left hpositive
    have hdiff : Df.weak.diffusivity = κ := by
      change D.weak.diffusivity = κ
      rfl
    change (max Df.weak.driftBound 0 ^ 2 / Df.weak.diffusivity + 2 * A + 1) =
      (max (positiveCutoffDriftConstant (AVenhance.streamVel φ) P.drift_bounded)
          0 ^ 2 / κ + 2 * A + 1)
    rw [hdrift, hdiff, max_eq_left hpositive]
  have hct : cN * t ≤ cN := by
    rw [hcN]
    exact mul_le_of_le_one_right hc ht.2
  have hexp : Real.exp (cN * t) ≤ Real.exp c := by
    rw [← hcN]
    exact Real.exp_le_exp.mpr hct
  have hfactor : 0 ≤ Real.exp (cN * t) := (Real.exp_pos _).le
  have hsumSq : ‖Df.initial‖ ^ 2 + G ^ 2 ≤ E₀ ^ 2 + G ^ 2 := by linarith
  have hnormSq :
      ‖AVenhance.Infra.ODE.extendCurve (by norm_num) V t‖ ^ 2 ≤ K := by
    have hbase := (hEnergy t ht).1
    have hbound := mul_le_mul hsumSq hexp (Real.exp_nonneg _) (by positivity)
    dsimp [K]
    calc
      ‖AVenhance.Infra.ODE.extendCurve (by norm_num) V t‖ ^ 2 ≤
        (‖Df.initial‖ ^ 2 + G ^ 2) * Real.exp (cN * t) := by
          simpa [cN] using hbase
      _ ≤ (E₀ ^ 2 + G ^ 2) * Real.exp c := hbound
  calc
    ‖AVenhance.Infra.ODE.extendCurve (by norm_num) V t‖ =
        Real.sqrt (‖AVenhance.Infra.ODE.extendCurve (by norm_num) V t‖ ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt K := Real.sqrt_le_sqrt hnormSq

end AVenhance.Infra.Classical

end
