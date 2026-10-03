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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchi

/-! Canonical C³ extensions of a fiber basis give a local frame.
In particular an orthonormal basis can be supplied via `b.toBasis`; no
orthonormality away from the base point is asserted or required. -/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  {ι : Type*} [Fintype ι]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Transport a fiber basis to the model space using the canonical trivialization. -/
def schurModelBasis (x : M) (b : Module.Basis ι ℝ (TM x)) : Module.Basis ι ℝ E :=
  b.map ((trivializationAt E TM x).linearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt E TM x))

@[simp] theorem schurModelBasis_localFrame_at (x : M)
    (b : Module.Basis ι ℝ (TM x)) (i : ι) :
    (trivializationAt E TM x).localFrame (schurModelBasis x b) i x = b i := by
  rw [(trivializationAt E TM x).localFrame_apply_of_mem_baseSet
    (b := schurModelBasis x b) (FiberBundle.mem_baseSet_trivializationAt E TM x)]
  change ((trivializationAt E TM x).linearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt E TM x)).symm
      (((trivializationAt E TM x).linearEquivAt ℝ x
        (FiberBundle.mem_baseSet_trivializationAt E TM x)) (b i)) = b i
  exact LinearEquiv.symm_apply_apply _ _

/-- The actual global sections used by the section-facing Bianchi theorem. -/
def schurFrame (x : M) (b : Module.Basis ι ℝ (TM x)) (i : ι) : Π y : M, TM y :=
  smoothExtend (I := I) (F := E) (V := TM) x (b i)

@[simp] theorem schurFrame_at (x : M) (b : Module.Basis ι ℝ (TM x)) (i : ι) :
    schurFrame x b i x = b i := smoothExtend_apply x (b i)

theorem schurFrame_contMDiff_three (x : M) (b : Module.Basis ι ℝ (TM x)) (i : ι) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (schurFrame x b i)) :=
  smoothExtend_contMDiff_three x (b i)

/-- Simultaneous agreement on a neighborhood, not merely agreement of values at the center. -/
theorem schurFrame_eventuallyEq_localFrame (x : M) (b : Module.Basis ι ℝ (TM x)) :
    ∀ᶠ y in nhds x, ∀ i,
      schurFrame x b i y =
        (trivializationAt E TM x).localFrame (schurModelBasis x b) i y := by
  rw [Filter.eventually_all]
  intro i
  simpa [schurFrame] using smoothExtend_trivializationAt_localFrame_eventuallyEq
    (I := I) (F := E) (V := TM) (schurModelBasis x b) x i

/-- The global C³ canonical extensions form a basis at every sufficiently nearby point. -/
theorem schurFrame_eventually_basis (x : M) (b : Module.Basis ι ℝ (TM x)) :
    ∀ᶠ y in nhds x, ∃ B : Module.Basis ι ℝ (TM y), ∀ i, B i = schurFrame x b i y := by
  have hb := (trivializationAt E TM x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E TM x)
  filter_upwards [hb, schurFrame_eventuallyEq_localFrame x b] with y hy he
  refine ⟨(trivializationAt E TM x).basisAt (schurModelBasis x b) hy, ?_⟩
  intro i
  rw [he i, (trivializationAt E TM x).localFrame_apply_of_mem_baseSet
    (b := schurModelBasis x b) hy]

/-- Local coefficients in the transported model basis reconstruct every section. -/
theorem schurFrame_eventually_sum_coeff (x : M) (b : Module.Basis ι ℝ (TM x))
    (Z : Π y : M, TM y) :
    ∀ᶠ y in nhds x, Z y = ∑ i,
      (trivializationAt E TM x).localFrameCoeff I (schurModelBasis x b) i y (Z y) •
        schurFrame x b i y := by
  simpa [schurFrame] using
    eventually_eq_sum_smoothExtend_trivializationAt_localFrameCoeff_smul
      (I := I) (F := E) (V := TM) (schurModelBasis x b) Z x

/-- An actual open neighborhood carrying the canonical C³ local frame, together
with its identification with the transported trivialization frame. -/
theorem schurFrame_exists_open_localFrame (x : M) (b : Module.Basis ι ℝ (TM x)) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      U ⊆ (trivializationAt E TM x).baseSet ∧
      IsLocalFrameOn I E 3 (schurFrame x b) U ∧
      ∀ y ∈ U, ∀ i, schurFrame x b i y =
        (trivializationAt E TM x).localFrame (schurModelBasis x b) i y := by
  have hb := (trivializationAt E TM x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E TM x)
  have hn : {y | y ∈ (trivializationAt E TM x).baseSet ∧ ∀ i,
      schurFrame x b i y =
        (trivializationAt E TM x).localFrame (schurModelBasis x b) i y} ∈ nhds x :=
    Filter.Eventually.and hb (schurFrame_eventuallyEq_localFrame x b)
  obtain ⟨U, hUsub, hUopen, hx⟩ := mem_nhds_iff.mp hn
  have hbase : U ⊆ (trivializationAt E TM x).baseSet := fun y hy ↦ (hUsub hy).1
  refine ⟨U, hUopen, hx, hbase, ?_, fun y hy ↦ (hUsub hy).2⟩
  exact (((trivializationAt E TM x).isLocalFrameOn_localFrame_baseSet
    I 3 (schurModelBasis x b)).mono hbase).congr
      (fun i y hy ↦ ((hUsub hy).2 i).symm)

end CovariantDerivative
