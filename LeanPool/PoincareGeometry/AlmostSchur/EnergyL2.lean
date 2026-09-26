/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.EnergySpace
public import LeanPool.PoincareGeometry.AlmostSchur.WeakChartLimit

/-! # The actual L2 realization of the C1 energy core

This file identifies representatives and proves algebraic injectivity on the
C1 core. Continuity and extension to the completion require Poincaré.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M]

local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- The canonical algebraic map sends a mean-zero C1 function to its actual L2 class. -/
def energyToL2Linear : EnergySpace (I := I) (M := M) →ₗ[ℝ]
    Lp ℝ 2 (riemannianVolume (I := I) (M := M)) where
  toFun f := (memLp_c1_riemannianVolume (I := I) f.property.1).toLp f.val
  map_add' f g := (memLp_c1_riemannianVolume (I := I) f.property.1).toLp_add
    (memLp_c1_riemannianVolume (I := I) g.property.1)
  map_smul' a f := (memLp_c1_riemannianVolume (I := I) f.property.1).toLp_const_smul a

/-- The core L2 map represents the original scalar function almost everywhere. -/
theorem energyToL2Linear_ae_eq (f : EnergySpace (I := I) (M := M)) :
    (energyToL2Linear f : M → ℝ) =ᵐ[riemannianVolume (I := I)] f.val :=
  (memLp_c1_riemannianVolume (I := I) f.property.1).coeFn_toLp

/-- Mean-zero is preserved by the actual core L2 realization. -/
theorem integral_energyToL2Linear (f : EnergySpace (I := I) (M := M)) :
    (∫ x, energyToL2Linear f x ∂riemannianVolume (I := I)) = 0 :=
  (integral_congr_ae (energyToL2Linear_ae_eq f)).trans f.property.2

/-- The core realization is injective because continuous AE-equal functions
agree everywhere for the positive-on-open-sets Riemannian volume. This theorem
does not assert injectivity of an extension to completed elements. -/
theorem energyToL2Linear_injective : Function.Injective (energyToL2Linear (I := I) (M := M)) := by
  let : (riemannianVolume (I := I) (M := M)).IsOpenPosMeasure :=
    ⟨fun V hV hne => ne_of_gt (riemannianVolume_open_pos (I := I) hV hne)⟩
  intro f g h
  apply Subtype.ext
  apply (f.property.1.continuous.ae_eq_iff_eq
    (riemannianVolume (I := I)) g.property.1.continuous).mp
  exact (energyToL2Linear_ae_eq f).symm.trans
    ((Filter.EventuallyEq.of_eq (congrArg (fun u : Lp ℝ 2 (riemannianVolume (I := I)) =>
      (u : M → ℝ)) h)).trans (energyToL2Linear_ae_eq g))

end AlmostSchur
