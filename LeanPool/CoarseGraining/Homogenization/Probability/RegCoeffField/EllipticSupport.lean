/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.SliceMeasurability

/-!
# Measurability of fixed-constant elliptic support events on the carrier

This file complements `SliceMeasurability.lean` (which treats the countable
quantitative slices with constants `((k+1)⁻¹, k+1)`) with the fixed-constant
support events used by the Examples layer:

* `isAEEllipticFieldOn_carrier_iff` — on a carrier element, the raw
  `IsAEEllipticFieldOn lam Lam U` predicate reduces to its spatial a.e.
  ellipticity conjunct (the two measurability conjuncts are free by type);
* `measurableSet_isAEEllipticFieldOn_of_isOpen` — for an *open* observation set
  the fixed-constant a.e.-ellipticity event is genuinely measurable for the
  canonical carrier σ-algebra (via the rational-ball intersection `slicePart`);
* `measurableSet_forall_openCubeSet_isAEEllipticFieldOn` — the uniform support
  event `{a | ∀ Q, IsAEEllipticFieldOn lam Lam (openCubeSet Q) a.toFun}`, a
  countable intersection over triadic cubes;
* `measurableSet_ae_isEllipticMatrix_univ` — the global (`Θ`-ellipticity class)
  event `{a | ∀ᵐ x, IsEllipticMatrix lam Lam (a x)}` (the case `U = univ`).

These are the measurable witness sets through which pushforward and Dirac laws
of honest fields verify `UniformEllipticityBounds` and `ThetaEllipticLaw`
(the paper, Armstrong–Kuusi–Loher, to appear).
-/

namespace Homogenization

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- On a carrier element, `IsAEEllipticFieldOn lam Lam U` reduces to its spatial
a.e.-ellipticity conjunct: the domain-measurability and entry-measurability
conjuncts are free by the carrier type (general-constants version of
`aeeQuantitativeEllipticSlice_carrier_iff`). -/
theorem isAEEllipticFieldOn_carrier_iff {U : Set (Vec d)} (hU : MeasurableSet U)
    (lam Lam : ℝ) (a : RegCoeffField d) :
    IsAEEllipticFieldOn lam Lam U a.toFun ↔
      ∀ᵐ x ∂(volumeMeasureOn U), IsEllipticMatrix lam Lam (a x) := by
  constructor
  · exact fun h => h.2.2
  · intro h
    exact ⟨hU, fun i j => aestronglyMeasurable_restrictCoeffField_carrier U hU a i j, h⟩

/-- **The fixed-constant a.e.-ellipticity event on an open set is genuinely
measurable** for the canonical carrier σ-algebra: it equals the countable
rational-ball intersection `slicePart U lam Lam`, which is
`LocalSigmaR U`-measurable. -/
theorem measurableSet_isAEEllipticFieldOn_of_isOpen {U : Set (Vec d)}
    (hUopen : IsOpen U) (lam Lam : ℝ) :
    MeasurableSet {a : RegCoeffField d | IsAEEllipticFieldOn lam Lam U a.toFun} := by
  have h1 : {a : RegCoeffField d | IsAEEllipticFieldOn lam Lam U a.toFun}
      = {a : RegCoeffField d |
          ∀ᵐ x ∂(volume.restrict U), IsEllipticMatrix lam Lam (a x)} := by
    ext a
    exact isAEEllipticFieldOn_carrier_iff hUopen.measurableSet lam Lam a
  rw [h1, setOf_aeRestrict_isEllipticMatrix_eq_slicePart hUopen lam Lam]
  exact LocalSigmaR_le U _ (measurableSet_slicePart lam Lam)

/-- **The uniform fixed-constant support event is genuinely measurable**: the
countable intersection over triadic cubes of the open-core a.e.-ellipticity
events. -/
theorem measurableSet_forall_openCubeSet_isAEEllipticFieldOn (lam Lam : ℝ) :
    MeasurableSet {a : RegCoeffField d |
      ∀ Q : TriadicCube d, IsAEEllipticFieldOn lam Lam (openCubeSet Q) a.toFun} := by
  have h1 : {a : RegCoeffField d |
        ∀ Q : TriadicCube d, IsAEEllipticFieldOn lam Lam (openCubeSet Q) a.toFun}
      = ⋂ Q : TriadicCube d,
          {a : RegCoeffField d | IsAEEllipticFieldOn lam Lam (openCubeSet Q) a.toFun} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h1]
  exact MeasurableSet.iInter fun Q =>
    measurableSet_isAEEllipticFieldOn_of_isOpen (isOpen_openCubeSet Q) lam Lam

/-- **The global a.e.-ellipticity event is genuinely measurable** (the case
`U = univ` of the rational-ball route): this is the membership event of the
`Θ`-ellipticity class `Ω_Θ` on the carrier. -/
theorem measurableSet_ae_isEllipticMatrix_univ (lam Lam : ℝ) :
    MeasurableSet {a : RegCoeffField d |
      ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix lam Lam (a x)} := by
  have h1 : {a : RegCoeffField d |
        ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix lam Lam (a x)}
      = {a : RegCoeffField d |
          ∀ᵐ x ∂(volume.restrict (Set.univ : Set (Vec d))),
            IsEllipticMatrix lam Lam (a x)} := by
    simp only [Measure.restrict_univ]
  rw [h1, setOf_aeRestrict_isEllipticMatrix_eq_slicePart isOpen_univ lam Lam]
  exact LocalSigmaR_le _ _ (measurableSet_slicePart lam Lam)

end

end Homogenization
