/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.Definitions

/-!
# Additional API for the fractional Sobolev seminorm

Reuse-surface lemmas that are not needed by the `W^{s,p}` versus `B^s_{p,p}`
comparison proofs themselves:

* the `p = ∞` Hölder-endpoint characterization;
* swap symmetry of the unnormalized `Set`-variant (the kernel is odd under
  the pair swap, the seminorm even);
* the cube/`Set` relation (the `⨍∫` normalization is a volume factor at
  power `1/p`);
* translation covariance along the triadic lattice (`translateCube`), via
  the translation pushforward of the product measure.

A.e.-congruence lemmas live in `CongruenceAE.lean`.
-/

@[expose] public section

namespace Homogenization
namespace Gagliardo

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At `p = ∞` the fractional Sobolev seminorm is the essential Hölder
`C^{0,s}` seminorm: the kernel exponent collapses to `s` and the `eLpNorm`
becomes an essential supremum. -/
theorem cubeGagliardoESeminorm_top (Q : TriadicCube d) (s : ℝ) (u : Vec d → E) :
    cubeGagliardoESeminorm Q s ∞ u =
      essSup (fun z : Vec d × Vec d =>
        ‖(dist z.1 z.2 ^ (-s)) • (u z.1 - u z.2)‖ₑ)
        (gagliardoCubeMeasure Q) := by
  simp only [cubeGagliardoESeminorm, integralLpSeminorm, ENNReal.top_ne_zero,
    if_false, if_true, eLpNormEssSup, gagliardoKernel, kernelExponent_top]

/-- Swap symmetry of the unnormalized seminorm: precomposing the kernel with
the pair swap changes nothing, since the kernel is odd under the swap and the
seminorm is even. -/
theorem gagliardoESeminormOn_comp_swap (A : Set (Vec d)) (s : ℝ) (p : ℝ≥0∞)
    (u : Vec d → E) :
    integralLpSeminorm (gagliardoKernel s p u ∘ Prod.swap) p
        ((MeasureTheory.volume.restrict A).prod
          (MeasureTheory.volume.restrict A)) =
      gagliardoESeminormOn A s p u := by
  have hswap : gagliardoKernel s p u ∘ Prod.swap =
      -(gagliardoKernel (d := d) s p u) := by
    funext z
    show gagliardoKernel s p u (z.2, z.1) = -(gagliardoKernel s p u z)
    rw [gagliardoKernel_apply, gagliardoKernel_apply]
    simp only [dist_comm z.2 z.1]
    rw [show u z.2 - u z.1 = -(u z.1 - u z.2) by abel, smul_neg]
  rw [hswap, gagliardoESeminormOn]
  exact integralLpSeminorm_neg _ _ _

/-- Relation between the cube-normalized seminorm and the unnormalized
`Set`-variant: the manuscript's `⨍∫` normalization contributes the volume
factor at power `1/p`. -/
theorem cubeGagliardoESeminorm_eq_smul_gagliardoESeminormOn
    (Q : TriadicCube d) (s : ℝ) {p : ℝ≥0∞} (hpt : p ≠ ∞) (u : Vec d → E) :
    cubeGagliardoESeminorm Q s p u =
      ENNReal.ofReal (cubeVolume Q)⁻¹ ^ (1 / p).toReal •
        gagliardoESeminormOn (Homogenization.cubeSet Q) s p u := by
  have : SFinite (MeasureTheory.volume.restrict (Homogenization.cubeSet Q)) :=
    inferInstance
  rw [cubeGagliardoESeminorm, gagliardoESeminormOn,
    gagliardoCubeMeasure, Homogenization.normalizedCubeMeasure,
    Homogenization.cubeMeasure, Measure.prod_smul_left,
    integralLpSeminorm_smul_measure _ hpt, smul_eq_mul]

section Translation

/-- The real translation vector realizing `translateCube shift Q`. -/
noncomputable def cubeShiftVector (shift : Fin d → ℤ) (Q : TriadicCube d) :
    Vec d :=
  fun i => (shift i : ℝ) * cubeScaleFactor Q

/-- Translation covariance of the fractional Sobolev seminorm: translating
the cube matches precomposing with the translation.  Stated for `p ≠ 0, ∞`
(the manuscript range); the `p = ∞` endpoint can be added via the `essSup`
characterization if ever needed. -/
theorem cubeGagliardoESeminorm_translate (shift : Fin d → ℤ)
    (Q : TriadicCube d) (s : ℝ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (u : Vec d → E) :
    cubeGagliardoESeminorm (translateCube shift Q) s p u =
      cubeGagliardoESeminorm Q s p
        (fun x => u (x + cubeShiftVector shift Q)) := by
  set v := cubeShiftVector shift Q with hv
  set T : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight v with hT
  have hTapp : ∀ x, T x = x + v := fun x => rfl
  -- volume is translation invariant
  have hmapT : Measure.map T MeasureTheory.volume = MeasureTheory.volume := by
    have hco : (⇑T : Vec d → Vec d) = (· + v) := rfl
    rw [hco]
    exact (measurePreserving_add_right MeasureTheory.volume v).map_eq
  -- the translated cube's restricted volume is the pushforward
  have hpre : (⇑T) ⁻¹' Homogenization.cubeSet (translateCube shift Q) =
      Homogenization.cubeSet Q := by
    ext x
    simp only [Set.mem_preimage, hTapp, mem_cubeSet_translateCube_iff]
    have : x + v - (fun i => (shift i : ℝ) * cubeScaleFactor Q) = x := by
      funext i
      simp [hv, cubeShiftVector]
    rw [this]
  have hres : MeasureTheory.volume.restrict
      (Homogenization.cubeSet (translateCube shift Q)) =
      Measure.map T (MeasureTheory.volume.restrict (Homogenization.cubeSet Q)) := by
    rw [← hpre, ← Measure.restrict_map T.measurable
      (Homogenization.measurableSet_cubeSet (translateCube shift Q)), hmapT]
  -- volumes agree
  have hvol : cubeVolume (translateCube shift Q) = cubeVolume Q := rfl
  -- the Gagliardo product measure is the pushforward under the pair translation
  have : SFinite (MeasureTheory.volume.restrict (Homogenization.cubeSet Q)) :=
    inferInstance
  have hprod : gagliardoCubeMeasure (translateCube shift Q) =
      Measure.map (Prod.map ⇑T ⇑T) (gagliardoCubeMeasure Q) := by
    rw [gagliardoCubeMeasure, gagliardoCubeMeasure,
      Homogenization.normalizedCubeMeasure, Homogenization.normalizedCubeMeasure,
      Homogenization.cubeMeasure, Homogenization.cubeMeasure, hvol, hres,
      Measure.prod_smul_left, Measure.prod_smul_left,
      Measure.map_prod_map _ _ T.measurable T.measurable,
      Measure.map_smul _ (T.measurable.prodMap T.measurable).aemeasurable]
  have hMP : MeasureTheory.MeasurePreserving (⇑(T.prodCongr T))
      (gagliardoCubeMeasure Q) (gagliardoCubeMeasure (translateCube shift Q)) := by
    refine ⟨(T.prodCongr T).measurable, ?_⟩
    rw [hprod]
    rfl
  -- kernel covariance under the pair translation
  have hker : ∀ z : Vec d × Vec d,
      gagliardoKernel s p u ((T.prodCongr T) z) =
        gagliardoKernel s p (fun x => u (x + v)) z := by
    intro z
    show gagliardoKernel s p u (T z.1, T z.2) = _
    rw [gagliardoKernel_apply, gagliardoKernel_apply, hTapp, hTapp,
      dist_add_right]
  -- conclude through the lintegral form
  rw [Internal.cubeGagliardoESeminorm_eq_lintegral hp0 hpt,
    Internal.cubeGagliardoESeminorm_eq_lintegral hp0 hpt]
  congr 1
  rw [MeasurePreserving.lintegral_map_equiv _ (T.prodCongr T) hMP]
  refine lintegral_congr fun z => ?_
  rw [hker]

end Translation

end

end Gagliardo
end Homogenization
