/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyAlgebra
public import Mathlib.Analysis.InnerProductSpace.Completion

/-! # The mean-zero intrinsic energy space

Mean-zero C1 functions carry the actual Dirichlet inner product. Its positive
definiteness uses connectedness and the proved classical energy kernel. The
Hilbert completion is constructed here; embedding it into L2 and bounding
forcing functionals still require the quantitative Poincaré inequality.
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

local instance : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)

local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

local instance : IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

/-- Mean-zero C1 functions form a real vector space. -/
def meanZeroC1 : Submodule ℝ (M → ℝ) where
  carrier := {f | CMDiff 1 f ∧ (∫ x, f x ∂riemannianVolume (I := I)) = 0}
  zero_mem' := ⟨contMDiff_const, by simp⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, ?_⟩
    change (∫ x, f x + g x ∂riemannianVolume (I := I)) = 0
    rw [integral_add
      (hf.1.continuous.integrable_of_hasCompactSupport isClosed_closure.isCompact)
      (hg.1.continuous.integrable_of_hasCompactSupport isClosed_closure.isCompact),
      hf.2, hg.2, add_zero]
  smul_mem' := by
    intro a f hf
    refine ⟨?_, ?_⟩
    · change CMDiff 1 (fun x => a * f x)
      exact contMDiff_const.mul hf.1
    change (∫ x, a * f x ∂riemannianVolume (I := I)) = 0
    rw [integral_const_mul, hf.2, mul_zero]

/-- A type synonym keeps the energy norm separate from any function-space norm. -/
def EnergySpace := ↥(meanZeroC1 (I := I) (M := M))

instance energySpaceAddCommGroup : AddCommGroup (EnergySpace (I := I) (M := M)) :=
  inferInstanceAs (AddCommGroup ↥(meanZeroC1 (I := I) (M := M)))

instance energySpaceModule : Module ℝ (EnergySpace (I := I) (M := M)) :=
  inferInstanceAs (Module ℝ ↥(meanZeroC1 (I := I) (M := M)))

variable [PreconnectedSpace M]

/-- The inner product is intrinsic energy, not a transported chart norm. -/
@[instance_reducible]
def energyInnerProductCore : InnerProductSpace.Core ℝ (EnergySpace (I := I) (M := M)) where
  inner f g := dirichletForm (I := I) f.val g.val
  conj_inner_symm f g := dirichletForm_symm g.val f.val
  re_inner_nonneg f := dirichletForm_self_nonneg f.val
  add_left f g h := dirichletForm_add_left_of_contMDiff f.val g.val h.val
    f.property.1 g.property.1 h.property.1
  smul_left f g a := dirichletForm_const_mul_left_of_contMDiff a f.val g.val f.property.1
  definite f hf := Subtype.ext
    (eq_zero_of_mean_zero_of_dirichletForm_self_eq_zero f.val f.property.1 f.property.2 hf)

instance energySpaceNormedAddCommGroup : NormedAddCommGroup (EnergySpace (I := I) (M := M)) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ _ _ _ _ (energyInnerProductCore (I := I))

instance energySpaceInnerProductSpace : InnerProductSpace ℝ (EnergySpace (I := I) (M := M)) :=
  InnerProductSpace.ofCore (energyInnerProductCore (I := I)).toCore

/-- The energy-space inner product agrees definitionally with the Dirichlet form. -/
theorem energySpace_inner (f g : EnergySpace (I := I) (M := M)) :
    inner ℝ f g = dirichletForm (I := I) f.val g.val := rfl

/-- The energy-space norm is precisely the square-root Dirichlet energy. -/
theorem energySpace_norm (f : EnergySpace (I := I) (M := M)) :
    ‖f‖ = Real.sqrt (dirichletForm (I := I) f.val f.val) := rfl

/-- Hilbert completion of the actual mean-zero energy space. -/
def EnergyCompletion := UniformSpace.Completion (EnergySpace (I := I) (M := M))

instance energyCompletionNormedAddCommGroup :
    NormedAddCommGroup (EnergyCompletion (I := I) (M := M)) :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion (EnergySpace (I := I) (M := M))))

instance energyCompletionInnerProductSpace :
    InnerProductSpace ℝ (EnergyCompletion (I := I) (M := M)) :=
  inferInstanceAs (InnerProductSpace ℝ (UniformSpace.Completion (EnergySpace (I := I) (M := M))))

instance energyCompletionCompleteSpace : CompleteSpace (EnergyCompletion (I := I) (M := M)) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (EnergySpace (I := I) (M := M))))

/-- The canonical inclusion preserves the actual energy norm. -/
def energyToCompletion : EnergySpace (I := I) (M := M) →ₗᵢ[ℝ]
    EnergyCompletion (I := I) (M := M) := UniformSpace.Completion.toComplₗᵢ

/-- The Hilbert completion restricts to the actual Dirichlet form on C1 functions. -/
theorem energyCompletion_inner (f g : EnergySpace (I := I) (M := M)) :
    inner ℝ (energyToCompletion f) (energyToCompletion g) =
      dirichletForm (I := I) f.val g.val := by
  exact (energyToCompletion (I := I)).inner_map_map f g

/-- Smoothness is not asserted for completed elements; the C1 energy core is dense. -/
theorem denseRange_energyToCompletion : DenseRange (energyToCompletion (I := I) (M := M)) :=
  UniformSpace.Completion.denseRange_coe

/-- Riesz representation on the genuine Hilbert energy completion. An actual
PDE forcing functional must still be proved bounded before using this map. -/
def energyRiesz (L : EnergyCompletion (I := I) (M := M) →L[ℝ] ℝ) :
    EnergyCompletion (I := I) (M := M) :=
  (InnerProductSpace.toDual ℝ (EnergyCompletion (I := I) (M := M))).symm L

/-- The Riesz representative solves the completed energy-pairing equation. -/
theorem energyRiesz_inner (L : EnergyCompletion (I := I) (M := M) →L[ℝ] ℝ)
    (v : EnergyCompletion (I := I) (M := M)) : inner ℝ (energyRiesz L) v = L v :=
  InnerProductSpace.toDual_symm_apply

/-- Riesz representation is unique, without a Poisson solvability assumption. -/
theorem existsUnique_energyRiesz (L : EnergyCompletion (I := I) (M := M) →L[ℝ] ℝ) :
    ∃! u : EnergyCompletion (I := I) (M := M), ∀ v, inner ℝ u v = L v := by
  refine ⟨energyRiesz L, energyRiesz_inner L, ?_⟩
  intro u hu
  apply ext_inner_right ℝ
  intro v
  exact (hu v).trans (energyRiesz_inner L v).symm

/-- The Riesz map preserves the dual norm. -/
theorem norm_energyRiesz (L : EnergyCompletion (I := I) (M := M) →L[ℝ] ℝ) :
    ‖energyRiesz L‖ = ‖L‖ :=
  (InnerProductSpace.toDual ℝ (EnergyCompletion (I := I) (M := M))).symm.norm_map L

end AlmostSchur
