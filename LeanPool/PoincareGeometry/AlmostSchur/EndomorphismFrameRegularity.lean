/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.ConnectionCoordinates
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-! # Recovering regularity of an endomorphism from its frame evaluations -/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
local notation "TM" => (TangentSpace I : M → Type _)

/-- Regular frame evaluations determine a regular hom-bundle section, without
assuming regularity of the operator being reconstructed. -/
theorem contMDiffAt_endomorphism_of_localFrame
    (n : ℕ∞ω) [ContMDiffVectorBundle n E TM I]
    (A : Π y, TM y →L[ℝ] TM y) (x : M)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    (hA : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (T% (fun y ↦ A y ((trivializationAt E TM x).localFrame b i y))) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := fun z ↦ TM z →L[ℝ] TM z) y (A y)) x := by
  classical
  let e := trivializationAt E TM x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E TM x
  let W (i : ι) (y : M) := A y (e.localFrame b i y)
  have hC (i) := (e.contMDiffAt_section_iff hx).mp (hA i)
  have hsum : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) n
      (fun y ↦ ∑ i, ContinuousLinearMap.smulRightL ℝ E E (b.coord i).toContinuousLinearMap
        ((e ⟨y, W i y⟩).2)) x :=
    ContMDiffAt.sum (fun i _ ↦
      (ContinuousLinearMap.smulRightL ℝ E E (b.coord i).toContinuousLinearMap).contMDiff.contMDiffAt.comp x (hC i))
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, hsum.congr_of_eventuallyEq ?_⟩
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  apply ContinuousLinearMap.coe_injective
  apply b.ext
  intro j
  change ContinuousLinearMap.inCoordinates E TM E TM x y x y (A y) (b j) =
    (∑ i, ContinuousLinearMap.smulRightL ℝ E E (b.coord i).toContinuousLinearMap
      ((e ⟨y, W i y⟩).2)) (b j)
  simp only [sum_apply, ContinuousLinearMap.smulRightL_apply_apply]
  change _ = ∑ i, b.coord i (b j) • (e ⟨y, W i y⟩).2
  simp [Module.Basis.coord_apply, Finsupp.single_apply]
  rw [ContinuousLinearMap.inCoordinates_eq hy hy]
  simp only [ContinuousLinearMap.comp_apply]
  change (e ⟨y, A y (e.symm y (b j))⟩).2 = (e ⟨y, A y (e.localFrame b j y)⟩).2
  rw [e.localFrame_apply_of_mem_baseSet b hy]
  rfl

end AlmostSchur
