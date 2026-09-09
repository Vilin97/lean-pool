/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothLoop
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothParameterIntegral
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# Jointly smooth rephasing by positive periodic densities

Each parameter supplies an actual `SmoothLoop.CircleDensity`. The inverse is
the globally defined monotone inverse already constructed there. Its joint
smoothness is proved with the inverse function theorem applied to the triangular
map `(p, θ) ↦ (p, Φ(p, θ))`; no smooth inverse is postulated.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Interval

namespace NavierStokes.ParametricRephase

open SmoothLoop

variable {E : Type*}

def familyRate (d : E → CircleDensity) (z : E × ℝ) : ℝ := (d z.1).rate z.2

def familyPhase (d : E → CircleDensity) (z : E × ℝ) : ℝ := phaseMap (d z.1) z.2

def inversePhase (d : E → CircleDensity) (z : E × ℝ) : ℝ :=
  (phaseHomeomorph (d z.1)).symm z.2

def forwardMap (d : E → CircleDensity) (z : E × ℝ) : E × ℝ :=
  (z.1, familyPhase d z)

def inverseMap (d : E → CircleDensity) (z : E × ℝ) : E × ℝ :=
  (z.1, inversePhase d z)

theorem inverseMap_forwardMap (d : E → CircleDensity) (z : E × ℝ) :
    inverseMap d (forwardMap d z) = z := by
  change (z.1, (phaseHomeomorph (d z.1)).symm (phaseHomeomorph (d z.1) z.2)) = z
  rw [(phaseHomeomorph (d z.1)).symm_apply_apply]

theorem forwardMap_inverseMap (d : E → CircleDensity) (z : E × ℝ) :
    forwardMap d (inverseMap d z) = z := by
  change (z.1, phaseHomeomorph (d z.1) ((phaseHomeomorph (d z.1)).symm z.2)) = z
  rw [(phaseHomeomorph (d z.1)).apply_symm_apply]

theorem forwardMap_bijective (d : E → CircleDensity) : Bijective (forwardMap d) :=
  ⟨Function.LeftInverse.injective (inverseMap_forwardMap d),
    Function.RightInverse.surjective (forwardMap_inverseMap d)⟩

theorem familyPhase_add_fullTurn (d : E → CircleDensity) (p : E) (θ : ℝ) :
    familyPhase d (p, θ + 2 * Real.pi) = familyPhase d (p, θ) + 1 :=
  phaseMap_add_fullTurn (d p) θ

theorem inversePhase_add_one (d : E → CircleDensity) (p : E) (φ : ℝ) :
    inversePhase d (p, φ + 1) = inversePhase d (p, φ) + 2 * Real.pi :=
  phaseInverse_add_one (d p) φ

theorem familyPhase_partial_hasDerivAt (d : E → CircleDensity) (p : E) (θ : ℝ) :
    HasDerivAt (fun t => familyPhase d (p, t)) (familyRate d (p, θ)) θ :=
  phaseMap_hasDerivAt (d p) θ

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The triangular derivative is a genuine continuous linear equivalence. Its
last diagonal entry is the strictly positive density, proved by the FTC. -/
theorem forwardMap_hasFDerivAt_equiv (d : E → CircleDensity) (z : E × ℝ)
    (hphase : DifferentiableAt ℝ (familyPhase d) z) :
    ∃ L : (E × ℝ) ≃L[ℝ] (E × ℝ), HasFDerivAt (forwardMap d) (L : (E × ℝ) →L[ℝ] (E × ℝ)) z := by
  let D : (E × ℝ) →L[ℝ] ℝ := fderiv ℝ (familyPhase d) z
  let B : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ
    (Units.mk0 (familyRate d z) (ne_of_gt ((d z.1).positive z.2)))
  let A : E →L[ℝ] ℝ := D.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let L : (E × ℝ) ≃L[ℝ] (E × ℝ) :=
    (ContinuousLinearEquiv.refl ℝ E).skewProd B A
  have hvertical₁ : HasFDerivAt (phaseMap (d z.1))
      (D.comp (ContinuousLinearMap.inr ℝ E ℝ)) z.2 := by
    change HasFDerivAt ((familyPhase d) ∘ fun t : ℝ => (z.1, t))
      (D.comp (ContinuousLinearMap.inr ℝ E ℝ)) z.2
    exact hphase.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  have hvertical₂ : HasFDerivAt (phaseMap (d z.1)) (B : ℝ →L[ℝ] ℝ) z.2 :=
    (phaseMap_hasDerivAt (d z.1) z.2).hasFDerivAt_equiv
      (ne_of_gt ((d z.1).positive z.2))
  have hvertical : D.comp (ContinuousLinearMap.inr ℝ E ℝ) = (B : ℝ →L[ℝ] ℝ) :=
    hvertical₁.unique hvertical₂
  have hL : (L : (E × ℝ) →L[ℝ] (E × ℝ)) =
      (ContinuousLinearMap.fst ℝ E ℝ).prod D := by
    apply ContinuousLinearMap.ext
    intro y
    apply Prod.ext
    · rfl
    · change B y.2 + D (y.1, 0) = D y
      have hv : D (0, y.2) = B y.2 := congrArg (fun f : ℝ →L[ℝ] ℝ => f y.2) hvertical
      rw [← hv, ← map_add]
      simp
  refine ⟨L, ?_⟩
  rw [hL]
  exact hasFDerivAt_fst.prodMk hphase.hasFDerivAt

section InverseSmoothness

variable [CompleteSpace E]

/-- Joint inverse smoothness is derived from the triangular inverse function
theorem, then identified with the global inverse using its exact inverse law. -/
theorem inverseMap_contDiffAt_of_phase (d : E → CircleDensity) (z : E × ℝ)
    (hphase : ContDiffAt ℝ ∞ (familyPhase d) (inverseMap d z)) :
    ContDiffAt ℝ ∞ (inverseMap d) z := by
  let a := inverseMap d z
  have hforward : ContDiffAt ℝ ∞ (forwardMap d) a :=
    contDiffAt_fst.prodMk hphase
  obtain ⟨L, hL⟩ := forwardMap_hasFDerivAt_equiv d a (hphase.differentiableAt (by simp))
  have hone : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hs := hforward.hasStrictFDerivAt' hL hone
  have heq : inverseMap d =ᶠ[𝓝 (forwardMap d a)] hforward.localInverse hL hone :=
    hs.localInverse_unique (Eventually.of_forall (inverseMap_forwardMap d))
  have hinv : ContDiffAt ℝ ∞ (inverseMap d) (forwardMap d a) :=
    (hforward.to_localInverse hL hone).congr_of_eventuallyEq heq
  simpa only [a, forwardMap_inverseMap] using hinv

theorem inversePhase_contDiffAt_of_phase (d : E → CircleDensity) (z : E × ℝ)
    (hphase : ContDiffAt ℝ ∞ (familyPhase d) (inverseMap d z)) :
    ContDiffAt ℝ ∞ (inversePhase d) z :=
  (inverseMap_contDiffAt_of_phase d z hphase).snd

theorem inverseMap_contDiffOn_of_phase (d : E → CircleDensity) (U : Set E)
    (hU : IsOpen U) (hphase : ContDiffOn ℝ ∞ (familyPhase d) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (inverseMap d) (U ×ˢ univ) := by
  intro z hz
  apply (inverseMap_contDiffAt_of_phase d z _).contDiffWithinAt
  apply hphase.contDiffAt
  exact (hU.prod isOpen_univ).mem_nhds ⟨hz.1, mem_univ _⟩

theorem inversePhase_contDiffOn_of_phase (d : E → CircleDensity) (U : Set E)
    (hU : IsOpen U) (hphase : ContDiffOn ℝ ∞ (familyPhase d) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (inversePhase d) (U ×ˢ univ) :=
  (inverseMap_contDiffOn_of_phase d U hU hphase).snd

theorem inversePhase_contDiff_of_phase (d : E → CircleDensity)
    (hphase : ContDiff ℝ ∞ (familyPhase d)) :
    ContDiff ℝ ∞ (inversePhase d) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact inversePhase_contDiffAt_of_phase d z hphase.contDiffAt

end InverseSmoothness

variable {V : Type*}

def rephaseFamily (d : E → CircleDensity) (f : E × ℝ → V) (z : E × ℝ) : V :=
  f (inverseMap d z)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem rephaseFamily_periodic (d : E → CircleDensity) (f : E × ℝ → V)
    (p : E) (hf : Function.Periodic (fun θ => f (p, θ)) (2 * Real.pi)) :
    Function.Periodic (fun φ => rephaseFamily d f (p, φ)) 1 := by
  intro φ
  change f (p, inversePhase d (p, φ + 1)) = f (p, inversePhase d (p, φ))
  rw [inversePhase_add_one]
  exact hf _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem rephaseFamily_forwardMap (d : E → CircleDensity) (f : E × ℝ → V) (z : E × ℝ) :
    rephaseFamily d f (forwardMap d z) = f z := by
  unfold rephaseFamily
  rw [inverseMap_forwardMap]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem rephaseFamily_integral (d : E → CircleDensity) (f : E × ℝ → ℝ) (p : E)
    (hf : Continuous (fun θ => f (p, θ))) :
    (∫ φ in (0 : ℝ)..1, rephaseFamily d f (p, φ)) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), f (p, θ) * familyRate d (p, θ) :=
  integral_rephase (d p) (fun θ => f (p, θ)) hf

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem rephaseFamily_contDiffOn_of_phase [CompleteSpace E]
    (d : E → CircleDensity) (f : E × ℝ → V) (U : Set E) (hU : IsOpen U)
    (hphase : ContDiffOn ℝ ∞ (familyPhase d) (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (rephaseFamily d f) (U ×ˢ univ) := by
  exact hf.comp (inverseMap_contDiffOn_of_phase d U hU hphase)
    (fun z hz => ⟨hz.1, mem_univ _⟩)

/-- Genuine iterated derivatives in the parameter while the last variable is
held fixed. This is not a separately postulated family of jets. -/
def parameterJet (F : E × ℝ → V) (k : ℕ) (z : E × ℝ) : E [×k]→L[ℝ] V :=
  iteratedFDeriv ℝ k (fun p : E => F (p, z.2)) z.1

/-- Joint smoothness implies joint smoothness of every genuine parameter jet.
This supplies the derivative continuity used in compact-interval integration. -/
theorem parameterJet_contDiffOn (F : E × ℝ → V) (U : Set E) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ)) (k : ℕ) :
    ContDiffOn ℝ ∞ (parameterJet F k) (U ×ˢ univ) := by
  induction k with
  | zero =>
      exact hF.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ E V).symm : V →L[ℝ] E [×0]→L[ℝ] V)
  | succ k ih =>
      intro z hz
      have hjet : ContDiffAt ℝ ∞ (parameterJet F k) z :=
        ih.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz)
      have hG : ContDiffAt ℝ ∞
          (fun w : (E × ℝ) × E => parameterJet F k (w.2, w.1.2)) (z, z.1) :=
        hjet.comp (z, z.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
      have hD : ContDiffAt ℝ ∞
          (fun w : E × ℝ => fderiv ℝ (fun p : E => parameterJet F k (p, w.2)) w.1) z :=
        hG.fderiv contDiffAt_fst (by simp)
      exact (hD.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) V).symm :
          (E →L[ℝ] E [×k]→L[ℝ] V) →L[ℝ] E [×(k + 1)]→L[ℝ] V)).contDiffWithinAt

/-- Integration over a fixed compact interval preserves joint smoothness.
All derivative domination is derived from compactness in the imported theorem. -/
theorem intervalIntegral_contDiffOn_of_joint [ProperSpace E] [CompleteSpace V]
    (F : E × ℝ → V) (U : Set E) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ)) (a b : ℝ) (hab : a ≤ b) :
    ContDiffOn ℝ ∞ (fun p => ∫ t in a..b, F (p, t)) U := by
  apply SmoothParameterIntegral.contDiffOn_intervalIntegral_of_continuous_jet hU hab
  · intro t _
    exact hF.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun p hp => ⟨hp, mem_univ _⟩)
  · intro k
    change ContinuousOn (parameterJet F k) (U ×ˢ Icc a b)
    exact (parameterJet_contDiffOn F U hU hF k).continuousOn.mono
      (Set.prod_mono Subset.rfl (subset_univ _))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem familyPhase_unit_interval (d : E → CircleDensity) (z : E × ℝ) :
    familyPhase d z = z.2 * ∫ t in (0 : ℝ)..1, familyRate d (z.1, z.2 * t) := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun t => familyRate d (z.1, t)) z.2 (a := 0) (b := 1)
  simpa only [familyPhase, familyRate, phaseMap, smul_eq_mul, mul_zero, mul_one] using h.symm

/-- The actual variable-endpoint cumulative integral is jointly smooth. No
regularity of that integral is assumed separately from regularity of the density. -/
theorem familyPhase_contDiffOn [FiniteDimensional ℝ E]
    (d : E → CircleDensity) (U : Set E) (hU : IsOpen U)
    (hrate : ContDiffOn ℝ ∞ (familyRate d) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (familyPhase d) (U ×ˢ univ) := by
  let F : (E × ℝ) × ℝ → ℝ := fun z => familyRate d (z.1.1, z.1.2 * z.2)
  have hF : ContDiffOn ℝ ∞ F ((U ×ˢ univ) ×ˢ univ) :=
    hrate.comp ((contDiff_fst.fst).prodMk ((contDiff_fst.snd).mul contDiff_snd)).contDiffOn
      (fun z hz => ⟨hz.1.1, mem_univ _⟩)
  have hi := intervalIntegral_contDiffOn_of_joint F (U ×ˢ univ)
    (hU.prod isOpen_univ) hF 0 1 (by norm_num)
  have heq : familyPhase d = (fun z => z.2 * ∫ t in (0 : ℝ)..1, F (z, t)) := by
    funext z
    exact familyPhase_unit_interval d z
  rw [heq]
  exact contDiff_snd.contDiffOn.mul hi

/-- Final density-only interface for the joint inverse on an open parameter set. -/
theorem inverseMap_contDiffOn [FiniteDimensional ℝ E]
    (d : E → CircleDensity) (U : Set E) (hU : IsOpen U)
    (hrate : ContDiffOn ℝ ∞ (familyRate d) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (inverseMap d) (U ×ˢ univ) :=
  inverseMap_contDiffOn_of_phase d U hU (familyPhase_contDiffOn d U hU hrate)

theorem inversePhase_contDiffOn [FiniteDimensional ℝ E]
    (d : E → CircleDensity) (U : Set E) (hU : IsOpen U)
    (hrate : ContDiffOn ℝ ∞ (familyRate d) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (inversePhase d) (U ×ˢ univ) :=
  (inverseMap_contDiffOn d U hU hrate).snd

theorem inversePhase_contDiff [FiniteDimensional ℝ E]
    (d : E → CircleDensity) (hrate : ContDiff ℝ ∞ (familyRate d)) :
    ContDiff ℝ ∞ (inversePhase d) := by
  have h := inversePhase_contDiffOn d univ isOpen_univ hrate.contDiffOn
  simpa only [univ_prod_univ, contDiffOn_univ] using h

/-- Smooth loops remain jointly smooth under the constructed parameter-dependent
phase inverse. Their period becomes one by `rephaseFamily_periodic`. -/
theorem rephaseFamily_contDiffOn [FiniteDimensional ℝ E]
    (d : E → CircleDensity) (f : E × ℝ → V) (U : Set E) (hU : IsOpen U)
    (hrate : ContDiffOn ℝ ∞ (familyRate d) (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (rephaseFamily d f) (U ×ˢ univ) :=
  rephaseFamily_contDiffOn_of_phase d f U hU (familyPhase_contDiffOn d U hU hrate) hf

theorem rephaseFamily_contDiff [FiniteDimensional ℝ E]
    (d : E → CircleDensity) (f : E × ℝ → V)
    (hrate : ContDiff ℝ ∞ (familyRate d)) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (rephaseFamily d f) := by
  have h := rephaseFamily_contDiffOn d f univ isOpen_univ hrate.contDiffOn hf.contDiffOn
  simpa only [univ_prod_univ, contDiffOn_univ] using h

end NavierStokes.ParametricRephase
