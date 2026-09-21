/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.ContinuousSection

/-!
# Riemannian metrics as bilinear-form sections

This file packages continuous and `C^n` Riemannian metrics as honest sections of
the hom bundle with fiber `F →L[ℝ] F →L[ℝ] ℝ`. This is the section-space side of
the metric data that later point-4 work needs: metrics can be fed directly into
continuous-section machinery instead of only being handled through ad hoc
structures.

It also adds extensionality lemmas for continuous and smooth Riemannian metrics,
so later arguments can reduce metric equality to pointwise equality of the
fiberwise bilinear forms.
-/

@[expose] public noncomputable section

open scoped Bundle Manifold ContDiff

namespace PoincareCurvature

/-!
The tangent fiber `TangentSpace I x` is definitionally the model vector space `F`, but the
class search path does not unfold it while synthesizing normed-space structure.  These low-priority
instances expose that structure for fiberwise continuous-linear constructions on tangent bilinear
forms.
-/

instance (priority := 70) instNormedAddCommGroupTangentSpace
    {M F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    (I : ModelWithCorners ℝ F H) [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    NormedAddCommGroup (TangentSpace I x) := by
  change NormedAddCommGroup F
  infer_instance

instance (priority := 100) instNormedSpaceTangentSpace
    {M F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    (I : ModelWithCorners ℝ F H) [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    NormedSpace ℝ (TangentSpace I x) := by
  change NormedSpace ℝ F
  infer_instance

instance (priority := 100) instIsTopologicalAddGroupTangentSpace
    {M F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    (I : ModelWithCorners ℝ F H) [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    IsTopologicalAddGroup (TangentSpace I x) := by
  change IsTopologicalAddGroup F
  infer_instance

instance (priority := 100) instT2SpaceTangentSpace
    {M F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    (I : ModelWithCorners ℝ F H) [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    T2Space (TangentSpace I x) := by
  change T2Space F
  infer_instance

end PoincareCurvature

namespace Bundle

/-- The bundle of real bilinear forms on the fibers of `V`. -/
abbrev BilinearFormBundle {B : Type*} {V : B → Type*}
    [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] :
    B → Type _ :=
  fun x : B ↦ V x →L[ℝ] V x →L[ℝ] ℝ

section Continuous

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

local notation "BilV" => BilinearFormBundle (V := V)

/-- Forget the positivity axioms and view a continuous Riemannian metric as a section of the
bilinear-form bundle. -/
def ContinuousRiemannianMetric.toSection (g : ContinuousRiemannianMetric F V) :
    Π x : B, BilV x :=
  g.inner

@[simp] theorem ContinuousRiemannianMetric.toSection_apply
    (g : ContinuousRiemannianMetric F V) (x : B) :
    g.toSection x = g.inner x :=
  rfl

/-- The section associated to a continuous Riemannian metric is continuous as a map to the total
space of the bilinear-form bundle. -/
lemma ContinuousRiemannianMetric.continuous_toSection (g : ContinuousRiemannianMetric F V) :
    Continuous
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g.toSection x)) := by
  simpa [ContinuousRiemannianMetric.toSection] using g.continuous

/-- A continuous Riemannian metric determines a bundled continuous section of the bilinear-form
bundle. -/
def ContinuousRiemannianMetric.toContinuousSection (g : ContinuousRiemannianMetric F V) :
    {s : Π x : B, BilV x //
      Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (s x))} :=
  ⟨g.toSection, g.continuous_toSection⟩

@[simp] theorem ContinuousRiemannianMetric.coe_toContinuousSection
    (g : ContinuousRiemannianMetric F V) :
    ((g.toContinuousSection : {s : Π x : B, BilV x //
      Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (s x))}).1) = g.toSection :=
  rfl

@[ext] theorem ContinuousRiemannianMetric.ext
    {g g' : ContinuousRiemannianMetric F V}
    (hinner : ∀ x : B, ∀ u v : V x, g.inner x u v = g'.inner x u v) :
    g = g' := by
  have hinner' : g.inner = g'.inner := by
    funext x
    ext u v
    exact hinner x u v
  cases g
  cases g'
  simp at hinner' ⊢
  exact hinner'

end Continuous

section Smooth

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

local notation "BilV" => BilinearFormBundle (V := V)

/-- Forget the positivity axioms and view a `C^n` Riemannian metric as a section of the
bilinear-form bundle. -/
def ContMDiffRiemannianMetric.toSection (g : ContMDiffRiemannianMetric IB n F V) :
    Π x : B, BilV x :=
  g.inner

@[simp] theorem ContMDiffRiemannianMetric.toSection_apply
    (g : ContMDiffRiemannianMetric IB n F V) (x : B) :
    g.toSection x = g.inner x :=
  rfl

/-- The section associated to a `C^n` Riemannian metric is `C^n` as a map to the total space of
the bilinear-form bundle. -/
lemma ContMDiffRiemannianMetric.contMDiff_toSection (g : ContMDiffRiemannianMetric IB n F V) :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g.toSection x)) := by
  simpa [ContMDiffRiemannianMetric.toSection] using g.contMDiff

/-- The section associated to a `C^n` Riemannian metric is continuous as a map to the total space
of the bilinear-form bundle. -/
lemma ContMDiffRiemannianMetric.continuous_toSection (g : ContMDiffRiemannianMetric IB n F V) :
    Continuous
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g.toSection x)) := by
  simpa [ContMDiffRiemannianMetric.toSection] using g.contMDiff.continuous

/-- A `C^n` Riemannian metric determines a bundled continuous section of the bilinear-form bundle. -/
def ContMDiffRiemannianMetric.toContinuousSection (g : ContMDiffRiemannianMetric IB n F V) :
    {s : Π x : B, BilV x //
      Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (s x))} :=
  ⟨g.toSection, g.continuous_toSection⟩

@[simp] theorem ContMDiffRiemannianMetric.coe_toContinuousSection
    (g : ContMDiffRiemannianMetric IB n F V) :
    ((g.toContinuousSection : {s : Π x : B, BilV x //
      Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (s x))}).1) = g.toSection :=
  rfl

@[ext] theorem ContMDiffRiemannianMetric.ext
    {g g' : ContMDiffRiemannianMetric IB n F V}
    (hinner : ∀ x : B, ∀ u v : V x, g.inner x u v = g'.inner x u v) :
    g = g' := by
  have hinner' : g.inner = g'.inner := by
    funext x
    ext u v
    exact hinner x u v
  cases g
  cases g'
  simp at hinner' ⊢
  exact hinner'

end Smooth

section FiberwisePositivity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ContinuousLinearMap

open Set

local notation "BilE" => (E →L[ℝ] E →L[ℝ] ℝ)

local instance bilENormedAddCommGroup : NormedAddCommGroup BilE :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))

local instance bilENormedSpace : NormedSpace ℝ BilE :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))

local instance bilEPseudoMetricSpace : PseudoMetricSpace BilE :=
  (inferInstance : PseudoMetricSpace (E →L[ℝ] E →L[ℝ] ℝ))

/-- The continuous linear involution that flips the arguments of a bilinear form. -/
noncomputable def flipBilinear : BilE →L[ℝ] BilE :=
  (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] lemma flipBilinear_apply_apply
    (B : BilE) (v w : E) :
    flipBilinear (E := E) B v w = B w v := by
  simp [flipBilinear, ContinuousLinearMap.flipₗᵢ, ContinuousLinearMap.flip_apply]

/-- A bilinear form is fixed by slot-flip exactly when it is symmetric. -/
lemma flipBilinear_eq_self_iff
    (B : BilE) :
    flipBilinear (E := E) B = B ↔ ∀ v w : E, B v w = B w v := by
  constructor
  · intro h v w
    have h' := congrArg (fun C : BilE => C v w) h
    have h'' : B w v = B v w := by
      simpa using h'
    exact h''.symm
  · intro h
    ext v w
    simpa using (h w v)

/-- Slot-flip preserves the pointwise positive-definite inequality because it leaves diagonal
values unchanged. -/
lemma flipBilinear_forall_pos_iff
    (B : BilE) :
    (∀ v : E, v ≠ 0 → 0 < flipBilinear (E := E) B v v) ↔
      ∀ v : E, v ≠ 0 → 0 < B v v := by
  simp

/-- Symmetrize a bilinear form by averaging it with its slot-flip. -/
noncomputable def symmetrizeBilinear : BilE →L[ℝ] BilE :=
  (2⁻¹ : ℝ) • ((ContinuousLinearMap.id ℝ BilE) + flipBilinear (E := E))

@[simp] lemma symmetrizeBilinear_apply_apply
    (B : BilE) (v w : E) :
    symmetrizeBilinear (E := E) B v w = (B v w + B w v) / 2 := by
  rw [symmetrizeBilinear]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, flipBilinear_apply_apply, div_eq_mul_inv, smul_eq_mul]
  ring_nf

@[simp] lemma symmetrizeBilinear_apply_self
    (B : BilE) (v : E) :
    symmetrizeBilinear (E := E) B v v = B v v := by
  rw [symmetrizeBilinear_apply_apply]
  ring

/-- Slot-flip preserves the operator norm of a bilinear form. -/
@[simp] lemma norm_flipBilinear
    (B : BilE) :
    ‖flipBilinear (E := E) B‖ = ‖B‖ := by
  simpa [flipBilinear] using
    (ContinuousLinearMap.opNorm_flip (𝕜 := ℝ) (E := E) (F := E) (G := ℝ) B)

/-- Applying symmetrization is the average of a bilinear form and its slot-flip. -/
lemma symmetrizeBilinear_apply
    (B : BilE) :
    symmetrizeBilinear (E := E) B = (2⁻¹ : ℝ) • (B + flipBilinear (E := E) B) := by
  ext v w
  rw [symmetrizeBilinear_apply_apply]
  simp [div_eq_mul_inv, smul_eq_mul]
  ring

/-- Symmetrization is norm non-increasing. -/
lemma norm_symmetrizeBilinear_le
    (B : BilE) :
    ‖symmetrizeBilinear (E := E) B‖ ≤ ‖B‖ := by
  rw [symmetrizeBilinear_apply]
  calc
    ‖(2⁻¹ : ℝ) • (B + flipBilinear (E := E) B)‖ =
        ‖(2⁻¹ : ℝ)‖ * ‖B + flipBilinear (E := E) B‖ := norm_smul _ _
    _ ≤ ‖(2⁻¹ : ℝ)‖ * (‖B‖ + ‖flipBilinear (E := E) B‖) := by
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = ‖B‖ := by
      simp
      ring

/-- Symmetrizing an approximant does not increase its distance from an already symmetric bilinear
form. -/
lemma dist_symmetrizeBilinear_le_of_symmetric
    {B C : BilE}
    (hB : ∀ v w : E, B v w = B w v) :
    dist (symmetrizeBilinear (E := E) C) B ≤ dist C B := by
  rw [dist_eq_norm, dist_eq_norm]
  have hdiff :
      symmetrizeBilinear (E := E) C - B =
        symmetrizeBilinear (E := E) (C - B) := by
    ext v w
    simp [symmetrizeBilinear_apply_apply, hB v w]
  rw [hdiff]
  exact norm_symmetrizeBilinear_le (E := E) (C - B)

/-- Symmetrization lands in the symmetric bilinear forms. -/
lemma symmetrizeBilinear_symm
    (B : BilE) :
    ∀ v w : E, symmetrizeBilinear (E := E) B v w =
      symmetrizeBilinear (E := E) B w v := by
  intro v w
  simp [symmetrizeBilinear_apply_apply, add_comm]

/-- Symmetrization preserves pointwise positive-definiteness, because it fixes diagonal values. -/
lemma symmetrizeBilinear_forall_pos_iff
    (B : BilE) :
    (∀ v : E, v ≠ 0 → 0 < symmetrizeBilinear (E := E) B v v) ↔
      ∀ v : E, v ≠ 0 → 0 < B v v := by
  constructor <;> intro h v hv <;> simpa using h v hv

/-- The antisymmetric defect of a bilinear form. It vanishes exactly on symmetric forms. -/
noncomputable def symmetryDefect : BilE →L[ℝ] BilE :=
  { toLinearMap := (ContinuousLinearMap.id ℝ BilE).toLinearMap - (flipBilinear (E := E)).toLinearMap
    cont := (ContinuousLinearMap.id ℝ BilE).continuous.sub (flipBilinear (E := E)).continuous }

@[simp] lemma symmetryDefect_apply_apply
    (B : BilE) (v w : E) :
    symmetryDefect (E := E) B v w = B v w - B w v := by
  simp [symmetryDefect, sub_eq_add_neg]

lemma symmetryDefect_eq_zero_iff
    (B : BilE) :
    symmetryDefect (E := E) B = 0 ↔ ∀ v w : E, B v w = B w v := by
  constructor
  · intro h v w
    have h' := congrArg (fun A : BilE => A v w) h
    exact sub_eq_zero.mp (by simpa [symmetryDefect] using h')
  · intro h
    ext v w
    simp [symmetryDefect, h v w]

/-- Symmetric bilinear forms on the model fiber form a convex subset. -/
lemma convex_setOf_forall_symmetric :
    Convex ℝ ({B : BilE | ∀ v w : E, B v w = B w v} : Set BilE) := by
  rw [convex_iff_forall_pos]
  intro B hB C hC a b _ _ _ v w
  simp [hB v w, hC v w]

/-- Positive-definite bilinear forms on the model fiber form a convex subset. -/
lemma convex_setOf_forall_pos :
    Convex ℝ ({B : BilE | ∀ v : E, v ≠ 0 → 0 < B v v} : Set BilE) := by
  rw [convex_iff_forall_pos]
  intro B hB C hC a b ha hb hab v hv
  have hleft : 0 < a * B v v := mul_pos ha (hB v hv)
  have hright : 0 ≤ b * C v v := mul_nonneg hb.le (le_of_lt (hC v hv))
  simpa [smul_eq_mul] using add_pos_of_pos_of_nonneg hleft hright

/-- Symmetric positive-definite bilinear forms on the model fiber form a convex subset. -/
lemma convex_setOf_forall_symmetric_and_pos :
    Convex ℝ
      ({B : BilE | (∀ v w : E, B v w = B w v) ∧
        ∀ v : E, v ≠ 0 → 0 < B v v} : Set BilE) := by
  rw [show ({B : BilE | (∀ v w : E, B v w = B w v) ∧
      ∀ v : E, v ≠ 0 → 0 < B v v} : Set BilE) =
      {B : BilE | ∀ v w : E, B v w = B w v} ∩
        {B : BilE | ∀ v : E, v ≠ 0 → 0 < B v v} by rfl]
  exact (convex_setOf_forall_symmetric (E := E)).inter
    (convex_setOf_forall_pos (E := E))

/-- A positive-definite continuous bilinear form on a finite-dimensional real normed space
uniformly dominates a positive multiple of the ambient norm squared. -/
lemma exists_pos_mul_sq_le_of_pos [FiniteDimensional ℝ E] [Nontrivial E]
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ c > 0, ∀ v : E, c * ‖v‖ ^ 2 ≤ B v v := by
  let f : E → ℝ := fun v ↦ B v v
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  letI : ProperSpace E := FiniteDimensional.proper_real E
  have hcompact : IsCompact (Metric.sphere (0 : E) 1) := by
    simpa using (isCompact_sphere (0 : E) 1)
  have hsphere : (Metric.sphere (0 : E) 1).Nonempty := by
    exact NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨u, hu, hmin⟩ := hcompact.exists_isMinOn hsphere hcont.continuousOn
  have hu_ne : u ≠ 0 := Metric.ne_of_mem_sphere hu one_ne_zero
  refine ⟨B u u, hpos u hu_ne, ?_⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · let w : E := ‖v‖⁻¹ • v
    have hw_norm : ‖w‖ = 1 := by
      dsimp [w]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    have hw_mem : w ∈ Metric.sphere (0 : E) 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm, w] using hw_norm
    have hminw : B u u ≤ B w w := (isMinOn_iff.mp hmin) w hw_mem
    have hscaled : B u u * ‖v‖ ^ 2 ≤ B w w * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hminw (sq_nonneg ‖v‖)
    have hw_eval : B w w * ‖v‖ ^ 2 = B v v := by
      dsimp [w]
      have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      simp [pow_two, mul_assoc]
      field_simp [hvn]
    simpa [mul_comm] using hscaled.trans_eq hw_eval

/-- The unit sublevel set of a positive-definite continuous bilinear form is von Neumann bounded.
This supplies the boundedness field needed to reify positive-definite bilinear-form sections as
continuous Riemannian metrics. -/
lemma isVonNBounded_sublevel_one_of_pos [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : E | B v v < 1} := by
  by_cases hsub : Subsingleton E
  · letI : Subsingleton E := hsub
    exact Bornology.IsVonNBounded.of_subsingleton
  · haveI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsub
    rcases exists_pos_mul_sq_le_of_pos (E := E) B hpos with ⟨c, hc, hc_le⟩
    refine NormedSpace.isVonNBounded_of_isBounded ℝ ((Metric.isBounded_iff_subset_ball 0).2 ?_)
    refine ⟨c⁻¹ + 1, ?_⟩
    intro v hv
    rw [Metric.mem_ball, dist_zero_right]
    have hc_inv_pos : 0 < c⁻¹ := inv_pos.mpr hc
    have hB_lt : c * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hc_le v) hv
    by_cases hn : ‖v‖ ≤ 1
    · linarith
    · have hn_gt : 1 < ‖v‖ := lt_of_not_ge hn
      have hsq_ge : ‖v‖ ≤ ‖v‖ ^ 2 := by
        nlinarith [hn_gt]
      have hmul_le : c * ‖v‖ ≤ c * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsq_ge (le_of_lt hc)
      have hmul_lt : c * ‖v‖ < 1 := lt_of_le_of_lt hmul_le hB_lt
      have hn_lt_inv : ‖v‖ < c⁻¹ := by
        have hn_lt_div : ‖v‖ < 1 / c := by
          exact (lt_div_iff₀ hc).2 (by simpa [mul_comm] using hmul_lt)
        simpa [one_div] using hn_lt_div
      linarith

/-- Transfer the von Neumann boundedness of the unit sublevel set of a positive-definite bilinear
form across a continuous linear equivalence to a finite-dimensional model space. -/
lemma isVonNBounded_sublevel_one_of_pos_of_continuousLinearEquiv
    {E' : Type*} [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
    [FiniteDimensional ℝ E]
    (e : E' ≃L[ℝ] E)
    (B : E' →L[ℝ] E' →L[ℝ] ℝ)
    (hpos : ∀ v : E', v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : E' | B v v < 1} := by
  let m : (E' →L[ℝ] E' →L[ℝ] ℝ) ≃L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
    e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
  let B' : E →L[ℝ] E →L[ℝ] ℝ := m B
  have hpos' : ∀ v : E, v ≠ 0 → 0 < B' v v := by
    intro v hv
    have hv' : e.symm v ≠ 0 := by
      intro hzero
      apply hv
      simpa using congrArg e hzero
    simpa [B', m] using hpos (e.symm v) hv'
  have hbounded_model :
      Bornology.IsVonNBounded ℝ {v : E | B' v v < 1} :=
    isVonNBounded_sublevel_one_of_pos (E := E) B' hpos'
  have hbounded_image :
      Bornology.IsVonNBounded ℝ
        ((e.symm : E →L[ℝ] E') '' {v : E | B' v v < 1}) :=
    Bornology.IsVonNBounded.image hbounded_model (e.symm : E →L[ℝ] E')
  refine Bornology.IsVonNBounded.subset ?_ hbounded_image
  intro v hv
  refine ⟨e v, ?_, ?_⟩
  · simpa [B', m] using hv
  · simp

/-- If a bilinear form is bounded below by a positive multiple of `‖v‖^2`, then every sufficiently
small perturbation in operator norm remains positive-definite. -/
lemma pos_of_norm_sub_lt
    {B C : E →L[ℝ] E →L[ℝ] ℝ} {c : ℝ}
    (hB : ∀ v : E, c * ‖v‖ ^ 2 ≤ B v v)
    (hBC : ‖C - B‖ < c) :
    ∀ v : E, v ≠ 0 → 0 < C v v := by
  intro v hv
  have hv_sq_pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hCv : ‖(C - B) v‖ ≤ ‖C - B‖ * ‖v‖ := ContinuousLinearMap.le_opNorm (C - B) v
  have hdiff_le : ‖(C - B) v v‖ ≤ ‖C - B‖ * ‖v‖ ^ 2 := by
    calc
      ‖(C - B) v v‖ ≤ ‖(C - B) v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm ((C - B) v) v
      _ ≤ (‖C - B‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right hCv (norm_nonneg v)
      _ = ‖C - B‖ * ‖v‖ ^ 2 := by ring
  have hdiff_lt : ‖(C - B) v v‖ < c * ‖v‖ ^ 2 := by
    exact lt_of_le_of_lt hdiff_le (by
      have := mul_lt_mul_of_pos_right hBC hv_sq_pos
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this)
  have hlower : -(c * ‖v‖ ^ 2) < (C - B) v v := by
    exact (abs_lt.mp (by simpa using hdiff_lt)).1
  have hBv : c * ‖v‖ ^ 2 ≤ B v v := hB v
  have hsum : 0 < B v v + (C - B) v v := by
    have hneg : -(B v v) ≤ -(c * ‖v‖ ^ 2) := neg_le_neg hBv
    have hlt : -(B v v) < (C - B) v v := lt_of_le_of_lt hneg hlower
    linarith
  have hrepr : B v v + (C - B) v v = C v v := by
    simpa [add_comm] using congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L v v) (sub_add_cancel C B)
  rw [hrepr] at hsum
  exact hsum

/-- Positive-definite continuous bilinear forms form an open subset of the operator-norm space of
all continuous bilinear forms on a finite-dimensional real normed space. -/
lemma exists_pos_ball_of_pos [FiniteDimensional ℝ E] [Nontrivial E]
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ ε > 0, ∀ C : E →L[ℝ] E →L[ℝ] ℝ, ‖C - B‖ < ε → ∀ v : E, v ≠ 0 → 0 < C v v := by
  obtain ⟨c, hc, hcoer⟩ := exists_pos_mul_sq_le_of_pos B hpos
  refine ⟨c, hc, ?_⟩
  intro C hC v hv
  exact pos_of_norm_sub_lt hcoer hC v hv

/-- A continuous family of positive-definite continuous bilinear forms over a compact space admits a
uniform pointwise perturbation radius that preserves positive-definiteness. -/
lemma exists_uniform_pos_ball_of_continuous
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (g : α → BilE) (hg : Continuous g)
    (hpos : ∀ x : α, ∀ v : E, v ≠ 0 → 0 < g x v v) :
    ∃ ε > 0, ∀ h : α → BilE, (∀ x : α, ‖h x - g x‖ < ε) →
      ∀ x : α, ∀ v : E, v ≠ 0 → 0 < h x v v := by
  classical
  by_cases hα : Nonempty α
  · letI := hα
    choose ε hεpos hεball using
      fun x : α => exists_pos_ball_of_pos (g x) (hpos x)
    let U : α → Set α := fun x => {y | ‖g y - g x‖ < ε x / 2}
    have hUo : ∀ x, IsOpen (U x) := by
      intro x
      have hcont : Continuous fun y : α => g y - g x := by
        exact hg.sub (continuous_const : Continuous fun _ : α => g x)
      exact isOpen_lt hcont.norm continuous_const
    have hcover : univ ⊆ ⋃ x, U x := by
      intro y hy
      refine mem_iUnion.2 ⟨y, ?_⟩
      change ‖g y - g y‖ < ε y / 2
      simpa using half_pos (hεpos y)
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo hcover
    have htne : t.Nonempty := by
      obtain ⟨x0⟩ := hα
      have hx0 : x0 ∈ ⋃ x ∈ t, U x := ht (by simp)
      rcases mem_iUnion₂.1 hx0 with ⟨i, hit, _⟩
      exact ⟨i, hit⟩
    let δ : ℝ := t.inf' htne (fun x => ε x / 2)
    have hδpos : 0 < δ := by
      have hmem : δ ∈ Ioi (0 : ℝ) := by
        refine Finset.inf'_mem (s := Ioi (0 : ℝ)) ?_ t htne (fun x => ε x / 2) ?_
        · intro a ha b hb
          simpa [mem_Ioi] using lt_min ha hb
        · intro x hx
          simpa [mem_Ioi] using half_pos (hεpos x)
      exact hmem
    refine ⟨δ, hδpos, ?_⟩
    intro h hh x v hv
    have hx : x ∈ ⋃ y ∈ t, U y := ht (by simp)
    rcases mem_iUnion₂.1 hx with ⟨i, hit, hix⟩
    have hδle : δ ≤ ε i / 2 := Finset.inf'_le (fun y => ε y / 2) hit
    have hgix : ‖g x - g i‖ < ε i / 2 := by
      simpa [U] using hix
    have hhix : ‖h x - g i‖ < ε i := by
      have hlt : ‖h x - g i‖ < δ + ε i / 2 := by
        calc
          ‖h x - g i‖ = ‖(h x - g x) + (g x - g i)‖ := by
            congr 1
            abel
          _ ≤ ‖h x - g x‖ + ‖g x - g i‖ := norm_add_le _ _
          _ < δ + ε i / 2 := add_lt_add_of_lt_of_lt (hh x) hgix
      have hbound : δ + ε i / 2 ≤ ε i := by
        linarith
      exact lt_of_lt_of_le hlt hbound
    exact hεball i (h x) hhix v hv
  · refine ⟨1, zero_lt_one, ?_⟩
    intro h hh x
    exact (hα ⟨x⟩).elim

/-- Positive-definite bounded continuous bilinear-form families form an open subset of the
sup-metric space of bounded continuous families on a compact base. -/
lemma exists_pos_ball_of_continuousMap
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (g : C(α, BilE))
    (hpos : ∀ x : α, ∀ v : E, v ≠ 0 → 0 < g x v v) :
    ∃ ε > 0, ∀ h : C(α, BilE), dist h g < ε →
      ∀ x : α, ∀ v : E, v ≠ 0 → 0 < h x v v := by
  obtain ⟨ε, hεpos, hε⟩ := exists_uniform_pos_ball_of_continuous g g.continuous hpos
  refine ⟨ε, hεpos, ?_⟩
  intro h hh x v hv
  have hpointwise : ∀ y : α, dist (h y) (g y) ≤ dist h g :=
    (ContinuousMap.dist_le (f := h) (g := g) (C := dist h g) dist_nonneg).1 le_rfl
  exact hε h
    (fun y => by
      have hy : dist (h y) (g y) < ε := lt_of_le_of_lt (hpointwise y) hh
      simpa [dist_eq_norm] using hy)
    x v hv

lemma isOpen_setOf_continuousMap_forall_pos
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [FiniteDimensional ℝ E] [Nontrivial E] :
    IsOpen {g : C(α, BilE) | ∀ x : α, ∀ v : E, v ≠ 0 → 0 < g x v v} := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  obtain ⟨ε, hεpos, hε⟩ := exists_pos_ball_of_continuousMap g hg
  refine Filter.mem_of_superset (Metric.ball_mem_nhds g hεpos) ?_
  intro h hh
  exact hε h (by simpa [Metric.mem_ball] using hh)

/-- Positive-definite bounded continuous bilinear-form families form an open subset of the
sup-metric space of bounded continuous families on a compact base. -/
lemma exists_pos_ball_of_boundedContinuousFunction
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (g : BoundedContinuousFunction α BilE)
    (hpos : ∀ x : α, ∀ v : E, v ≠ 0 → 0 < g x v v) :
    ∃ ε > 0, ∀ h : BoundedContinuousFunction α BilE, dist h g < ε →
      ∀ x : α, ∀ v : E, v ≠ 0 → 0 < h x v v := by
  obtain ⟨ε, hεpos, hε⟩ := exists_uniform_pos_ball_of_continuous g g.continuous hpos
  refine ⟨ε, hεpos, ?_⟩
  intro h hh x v hv
  exact hε h
    (fun y => by
      have hy : dist (h y) (g y) < ε := by
        exact lt_of_le_of_lt (BoundedContinuousFunction.dist_coe_le_dist y) hh
      simpa [dist_eq_norm] using hy)
    x v hv

lemma isOpen_setOf_boundedContinuousFunction_forall_pos
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [FiniteDimensional ℝ E] [Nontrivial E] :
    IsOpen {g : BoundedContinuousFunction α BilE | ∀ x : α, ∀ v : E, v ≠ 0 → 0 < g x v v} := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  obtain ⟨ε, hεpos, hε⟩ := exists_pos_ball_of_boundedContinuousFunction g hg
  refine Filter.mem_of_superset (Metric.ball_mem_nhds g hεpos) ?_
  intro h hh
  exact hε h (by simpa [Metric.mem_ball] using hh)

end ContinuousLinearMap

end FiberwisePositivity

end Bundle

namespace Bundle

/-- **Fiberwise slot-flip depends continuously on the map.**  If `x ↦ h x` is continuous at `x₀` into
the bilinear-map space `E →L[𝕜] Fₗ →L[𝕜] Gₗ`, then so is the pointwise slot-flip `x ↦ (h x).flip`.
This is the `ContinuousAt` companion of the fact that `ContinuousLinearMap.flip` is a linear isometric
equivalence (`ContinuousLinearMap.flipₗᵢ`), hence a continuous self-map of the bilinear-map space. -/
theorem _root_.ContinuousAt.clm_flip {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E Fₗ Gₗ : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Fₗ] [NormedSpace 𝕜 Fₗ] [NormedAddCommGroup Gₗ] [NormedSpace 𝕜 Gₗ]
    {X : Type*} [TopologicalSpace X] {h : X → E →L[𝕜] Fₗ →L[𝕜] Gₗ} {x₀ : X}
    (hh : ContinuousAt h x₀) :
    ContinuousAt (fun x ↦ (h x).flip) x₀ := by
  have hcont : Continuous (fun f : E →L[𝕜] Fₗ →L[𝕜] Gₗ ↦ f.flip) :=
    (ContinuousLinearMap.flipₗᵢ 𝕜 E Fₗ Gₗ).continuous
  exact hcont.continuousAt.comp hh

/-- **Operator-norm bound for a bilinear conjugation.**  Composing a continuous bilinear map
`f : E →L[𝕜] F →L[𝕜] G` with two continuous linear maps `gE : E' →L[𝕜] E`, `gF : F' →L[𝕜] F`
multiplies the operator norms: `‖f.bilinearComp gE gF‖ ≤ ‖f‖ * ‖gE‖ * ‖gF‖`.  Proved from
`bilinearComp = ((f.comp gE).flip.comp gF).flip` via `opNorm_flip` (isometric) and the submultiplicative
`opNorm_comp_le`.  This is the fiber-level size estimate consumed when packaging the fiberwise
bilinear-conjugation reaction operator as a bounded section-space operator. -/
theorem _root_.ContinuousLinearMap.norm_bilinearComp_le {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F G E' F' : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E'] [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']
    (f : E →L[𝕜] F →L[𝕜] G) (gE : E' →L[𝕜] E) (gF : F' →L[𝕜] F) :
    ‖f.bilinearComp gE gF‖ ≤ ‖f‖ * ‖gE‖ * ‖gF‖ := by
  rw [ContinuousLinearMap.bilinearComp, ContinuousLinearMap.opNorm_flip]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  rw [ContinuousLinearMap.opNorm_flip]
  exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)

section LocalCoordinatePositivity
variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "BilW" => BilinearFormBundle (V := W)

/-- In preferred local coordinates, a bundled bilinear form evaluates by pulling the model vectors
back through the inverse fiber trivialization. -/
lemma trivializationAt_bilinearFormBundle_apply_eq
    (x0 x : M) (hx : x ∈ (trivializationAt F W x0).baseSet)
    (B : BilW x) (u v : F) :
    ((trivializationAt BilF BilW x0 ⟨x, B⟩).2) u v =
      B (((trivializationAt F W x0).continuousLinearEquivAt ℝ x hx).symm u)
        (((trivializationAt F W x0).continuousLinearEquivAt ℝ x hx).symm v) := by
  let e : W x ≃L[ℝ] F := (trivializationAt F W x0).continuousLinearEquivAt ℝ x hx
  let eDual : (W x →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) :=
    ((trivializationAt (F →L[ℝ] ℝ) (fun y => W y →L[ℝ] ℝ) x0).continuousLinearEquivAt ℝ x
      (by simpa using hx) : (W x →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ))
  have hdual (φ : W x →L[ℝ] ℝ) :
      ((trivializationAt (F →L[ℝ] ℝ) (fun y => W y →L[ℝ] ℝ) x0 ⟨x, φ⟩).2) v =
        φ (e.symm v) := by
    have htrivDual := hom_trivializationAt_apply (σ := RingHom.id ℝ)
        (F₁ := F) (E₁ := W) (F₂ := ℝ) (E₂ := fun _ : M => ℝ) x0 ⟨x, φ⟩
    have hφ :
        (trivializationAt (F →L[ℝ] ℝ) (fun y => W y →L[ℝ] ℝ) x0 ⟨x, φ⟩).2 =
          φ.comp (e.symm : F →L[ℝ] W x) := by
      simpa [e, ContinuousLinearMap.inCoordinates_eq, hx] using congrArg Prod.snd htrivDual
    have hv := congrArg (fun ψ : F →L[ℝ] ℝ => ψ v) hφ
    simpa [e] using hv
  have htriv := hom_trivializationAt_apply (σ := RingHom.id ℝ)
      (F₁ := F) (E₁ := W) (F₂ := F →L[ℝ] ℝ) (E₂ := fun y => W y →L[ℝ] ℝ) x0 ⟨x, B⟩
  have hB :
      (trivializationAt BilF BilW x0 ⟨x, B⟩).2 =
        eDual.comp (B.comp (e.symm : F →L[ℝ] W x)) := by
    simpa [e, eDual, ContinuousLinearMap.inCoordinates_eq, hx] using congrArg Prod.snd htriv
  have hu := congrArg (fun ψ : F →L[ℝ] F →L[ℝ] ℝ => ψ u v) hB
  simpa [hdual, e, eDual] using hu

/-- Preferred bilinear-form bundle trivializations are fiberwise linear. This explicit instance
avoids typeclass-search ambiguity from the nested hom-bundle construction when using coordinate
changes for bilinear-form coordinates. -/
lemma trivializationAt_bilinearFormBundle_isLinear (x0 : M) :
    (trivializationAt BilF BilW x0).IsLinear ℝ where
  linear x hx := by
    have hxW : x ∈ (trivializationAt F W x0).baseSet := by
      simpa using hx
    refine ⟨?_, ?_⟩
    · intro B C
      ext u v
      rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W)
        x0 x hxW (B + C) u v]
      simp only [ContinuousLinearMap.add_apply]
      rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W)
        x0 x hxW B u v]
      rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W)
        x0 x hxW C u v]
    · intro c B
      ext u v
      rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W)
        x0 x hxW (c • B) u v]
      simp only [ContinuousLinearMap.smul_apply]
      rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W)
        x0 x hxW B u v]

/-- In preferred local coordinates, a bundled bilinear form evaluates by pulling the model vector
back through the inverse fiber trivialization. -/
lemma trivializationAt_bilinearFormBundle_apply_apply_eq
    (x0 x : M) (hx : x ∈ (trivializationAt F W x0).baseSet)
    (B : BilW x) (u : F) :
    ((trivializationAt BilF BilW x0 ⟨x, B⟩).2) u u =
      B (((trivializationAt F W x0).continuousLinearEquivAt ℝ x hx).symm u)
        (((trivializationAt F W x0).continuousLinearEquivAt ℝ x hx).symm u) := by
  simpa using trivializationAt_bilinearFormBundle_apply_eq
    (F := F) (W := W) x0 x hx B u u

/-- Preferred bilinear-form transition functions commute with model-fiber symmetrization. This is the
coordinate-level replacement for intrinsic tangent-fiber symmetrization: transition maps for the
bilinear-form bundle act by pulling both slots through the same linear equivalence, so averaging the
two slots can be done before or after changing coordinates. The statement is written in terms of the
trivialization action rather than `coordChangeL`, so it is usable before Lean has inferred linearity
instances for the induced hom-bundle trivializations. -/
lemma trivializationAt_bilinearFormBundle_transition_symmetrizeBilinear
    (x0 x1 x : M)
    (hx0 : x ∈ (trivializationAt F W x0).baseSet)
    (hx1 : x ∈ (trivializationAt F W x1).baseSet)
    (B : BilF) :
    ((trivializationAt BilF BilW x1)
        ⟨x, (trivializationAt BilF BilW x0).symm x
          (_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear (E := F) B)⟩).2 =
      _root_.Bundle.ContinuousLinearMap.symmetrizeBilinear (E := F)
        (((trivializationAt BilF BilW x1)
          ⟨x, (trivializationAt BilF BilW x0).symm x B⟩).2) := by
  let e0 := (trivializationAt F W x0).continuousLinearEquivAt ℝ x hx0
  let e1 := (trivializationAt F W x1).continuousLinearEquivAt ℝ x hx1
  let tb0 := trivializationAt BilF BilW x0
  have hcoord (C : BilF) (a b : W x) :
      tb0.symm x C a b = C (e0 a) (e0 b) := by
    have happly :
        (tb0 ⟨x, tb0.symm x C⟩).2 = C := by
      exact congrArg Prod.snd (tb0.apply_mk_symm (by simpa [tb0] using hx0) C)
    have hleft :
        (tb0 ⟨x, tb0.symm x C⟩).2 (e0 a) (e0 b) = tb0.symm x C a b := by
      rw [trivializationAt_bilinearFormBundle_apply_eq
        (F := F) (W := W) x0 x hx0 (tb0.symm x C) (e0 a) (e0 b)]
      simpa [e0] using
        congrArg₂ (fun p q : W x => tb0.symm x C p q)
          (e0.symm_apply_apply a) (e0.symm_apply_apply b)
    exact hleft.symm.trans (by simpa using congrArg (fun D : BilF => D (e0 a) (e0 b)) happly)
  ext u v
  rw [trivializationAt_bilinearFormBundle_apply_eq
    (F := F) (W := W) x1 x hx1
    (tb0.symm x (_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear (E := F) B)) u v]
  rw [hcoord (_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear (E := F) B)
    (e1.symm u) (e1.symm v)]
  rw [_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear_apply_apply]
  rw [_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear_apply_apply]
  rw [trivializationAt_bilinearFormBundle_apply_eq
    (F := F) (W := W) x1 x hx1 (tb0.symm x B) u v]
  rw [trivializationAt_bilinearFormBundle_apply_eq
    (F := F) (W := W) x1 x hx1 (tb0.symm x B) v u]
  rw [hcoord B (e1.symm u) (e1.symm v), hcoord B (e1.symm v) (e1.symm u)]

/-- If the preferred-coordinate representative of one fiber bilinear form is symmetric, then the
fiber bilinear form itself is symmetric. -/
lemma forall_symmetric_of_trivializationAt_bilinearFormBundle_forall_symmetric
    (x0 x : M) (hx : x ∈ (trivializationAt F W x0).baseSet)
    (B : BilW x)
    (hcoord : ∀ u v : F,
      ((trivializationAt BilF BilW x0 ⟨x, B⟩).2) u v =
        ((trivializationAt BilF BilW x0 ⟨x, B⟩).2) v u) :
    ∀ u v : W x, B u v = B v u := by
  intro u v
  let e := (trivializationAt F W x0).continuousLinearEquivAt ℝ x hx
  have h := hcoord (e u) (e v)
  have hleft :
      ((trivializationAt BilF BilW x0 ⟨x, B⟩).2) (e u) (e v) = B u v := by
    rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x0 x hx]
    change B (e.symm (e u)) (e.symm (e v)) = B u v
    simpa using congrArg₂ (fun a b => B a b) (e.symm_apply_apply u) (e.symm_apply_apply v)
  have hright :
      ((trivializationAt BilF BilW x0 ⟨x, B⟩).2) (e v) (e u) = B v u := by
    rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x0 x hx]
    change B (e.symm (e v)) (e.symm (e u)) = B v u
    simpa using congrArg₂ (fun a b => B a b) (e.symm_apply_apply v) (e.symm_apply_apply u)
  simpa [hleft, hright] using h

/-- If the preferred-coordinate representative of one fiber bilinear form is positive-definite, then
the fiber bilinear form itself is positive-definite. -/
lemma forall_pos_of_trivializationAt_bilinearFormBundle_forall_pos
    (x0 x : M) (hx : x ∈ (trivializationAt F W x0).baseSet)
    (B : BilW x)
    (hcoord : ∀ u : F, u ≠ 0 →
      0 < ((trivializationAt BilF BilW x0 ⟨x, B⟩).2) u u) :
    ∀ u : W x, u ≠ 0 → 0 < B u u := by
  intro u hu
  let e := (trivializationAt F W x0).continuousLinearEquivAt ℝ x hx
  have heu : e u ≠ 0 := by
    intro hzero
    exact hu (e.injective (by simpa using hzero))
  have h := hcoord (e u) heu
  have hdiag :
      ((trivializationAt BilF BilW x0 ⟨x, B⟩).2) (e u) (e u) = B u u := by
    rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x0 x hx]
    change B (e.symm (e u)) (e.symm (e u)) = B u u
    simpa using congrArg₂ (fun a b => B a b) (e.symm_apply_apply u) (e.symm_apply_apply u)
  simpa [hdiag] using h

end LocalCoordinatePositivity

section BilinearConjugation

/- A `BilinearFormBundle` over a vector bundle whose fibers are genuinely normed (the fiber topology
is the norm topology, so no instance diamond arises), the setting in which the fiberwise bilinear
conjugation `β ↦ β(P·, P·)` is available (`ContinuousLinearMap.bilinearComp` needs seminormed
domains).  This is exactly the tangent-bundle situation the geometric Ricci–DeTurck reaction operator
lives in. -/
variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [∀ x, SeminormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "BilW" => BilinearFormBundle (V := W)

/-- **Fiberwise bilinear conjugation preserves continuity of a `BilinearFormBundle` section.**
Given a continuous section `s` of the bilinear-form bundle `BilW` and a continuous section `P` of the
tangent endomorphism bundle `Hom(W, W)`, the pointwise conjugate `x ↦ (s x).bilinearComp (P x) (P x)`
— the bilinear form `(u, v) ↦ s x (P x u) (P x v)` — is again a continuous `BilinearFormBundle`
section.

This is the reaction-operator continuity input built **directly on sections via a tangent-bundle
endomorphism** `P`, avoiding the triple-nested hom bundle `Hom(BilW, BilW)` (whose `TotalSpace`
instances do not synthesize).  Proof: reduce to continuity of the trivialization readout via
`FiberBundle.continuousAt_totalSpace`; on the trivializing base set the readout of the conjugate
equals `(readout s).bilinearComp (readout P) (readout P)`, where `readout s` is the bilinear-form
readout of `s` and `readout P = inCoordinates F W F W x₀ x x₀ x (P x)` is the endomorphism readout of
`P` (both continuous, from the two section-continuity hypotheses), and `f ↦ b.bilinearComp f f`
is continuous through `ContinuousAt.clm_comp` / `ContinuousAt.clm_flip`
(`bilinearComp = ((·.comp ·).flip.comp ·).flip`).  The coordinate identity uses
`trivializationAt_bilinearFormBundle_apply_eq` together with `ContinuousLinearMap.inCoordinates_eq`. -/
theorem continuous_bilinearComp_section
    {s : Π x : M, BilW x}
    (hs : Continuous (fun x ↦ TotalSpace.mk' BilF (E := BilW) x (s x)))
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x))) :
    Continuous (fun x ↦ TotalSpace.mk' BilF (E := BilW) x
      (((s x).bilinearComp (P x) (P x) : BilW x))) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [FiberBundle.continuousAt_totalSpace BilF]
  refine ⟨continuousAt_id, ?_⟩
  -- Continuity of the bilinear-form readout of `s`.
  have hs_at := hs.continuousAt (x := x₀)
  rw [FiberBundle.continuousAt_totalSpace BilF] at hs_at
  have hbil : ContinuousAt
      (fun x ↦ (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2) x₀ := hs_at.2
  -- Continuity of the endomorphism readout of `P`.
  have hP_at := hP.continuousAt (x := x₀)
  rw [continuousAt_hom_bundle] at hP_at
  have hp : ContinuousAt
      (fun x ↦ ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)) x₀ := hP_at.2
  -- The bilinear conjugation of the two readouts is continuous.
  have hg : ContinuousAt (fun x ↦
      ((trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2).bilinearComp
        (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x))
        (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x))) x₀ := by
    have h1 := hbil.clm_comp hp
    have h2 := h1.clm_flip
    have h3 := h2.clm_comp hp
    exact h3.clm_flip
  -- On the trivializing base set the conjugate readout matches the conjugation of the readouts.
  refine hg.congr ?_
  filter_upwards [(trivializationAt F W x₀).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt F W x₀)] with x hx
  have hIC : ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)
      = ((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx : W x →L[ℝ] F).comp
          ((P x).comp
            (((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm : F →L[ℝ] W x)) :=
    ContinuousLinearMap.inCoordinates_eq hx hx
  have key : ∀ u : F,
      ((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm
          (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x) u)
        = P x (((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm u) := by
    intro u
    rw [hIC]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  ext u v
  rw [ContinuousLinearMap.bilinearComp_apply,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx (s x)
      (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x) u)
      (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x) v),
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx
      ((s x).bilinearComp (P x) (P x)) u v,
    ContinuousLinearMap.bilinearComp_apply, key u, key v]

/-- **Two-sided fiberwise bilinear composition preserves continuity of a `BilinearFormBundle`
section.**  Given a continuous section `s` of the bilinear-form bundle `BilW` and two continuous
sections `P`, `Q` of the tangent endomorphism bundle `Hom(W, W)`, the pointwise composite
`x ↦ (s x).bilinearComp (P x) (Q x)` — the bilinear form `(u, v) ↦ s x (P x u) (Q x v)` — is again a
continuous `BilinearFormBundle` section.

This generalises `continuous_bilinearComp_section` (the conjugation case `Q = P`) to two *different*
endomorphism sections.  It is the shape the intrinsic Ricci–DeTurck reaction (DeTurck-correction)
term needs: that term is the *derivation* `s(P·, ·) + s(·, P·)`, i.e. a sum of one-sided
compositions `(P, id)` and `(id, P)`, **not** a conjugation.  Proof is the two-section adaptation of
`continuous_bilinearComp_section`: the readout of the composite is the continuous `bilinearComp` of
the readout of `s` with the coordinate readouts of `P` and `Q`. -/
theorem continuous_bilinearComp₂_section
    {s : Π x : M, BilW x}
    (hs : Continuous (fun x ↦ TotalSpace.mk' BilF (E := BilW) x (s x)))
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    {Q : Π x : M, W x →L[ℝ] W x}
    (hQ : Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (Q x))) :
    Continuous (fun x ↦ TotalSpace.mk' BilF (E := BilW) x
      (((s x).bilinearComp (P x) (Q x) : BilW x))) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [FiberBundle.continuousAt_totalSpace BilF]
  refine ⟨continuousAt_id, ?_⟩
  -- Continuity of the bilinear-form readout of `s`.
  have hs_at := hs.continuousAt (x := x₀)
  rw [FiberBundle.continuousAt_totalSpace BilF] at hs_at
  have hbil : ContinuousAt
      (fun x ↦ (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2) x₀ := hs_at.2
  -- Continuity of the endomorphism readouts of `P` and `Q`.
  have hP_at := hP.continuousAt (x := x₀)
  rw [continuousAt_hom_bundle] at hP_at
  have hp : ContinuousAt
      (fun x ↦ ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)) x₀ := hP_at.2
  have hQ_at := hQ.continuousAt (x := x₀)
  rw [continuousAt_hom_bundle] at hQ_at
  have hq : ContinuousAt
      (fun x ↦ ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (Q x)) x₀ := hQ_at.2
  -- The two-sided bilinear composition of the readouts is continuous.
  have hg : ContinuousAt (fun x ↦
      ((trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2).bilinearComp
        (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x))
        (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (Q x))) x₀ := by
    have h1 := hbil.clm_comp hp
    have h2 := h1.clm_flip
    have h3 := h2.clm_comp hq
    exact h3.clm_flip
  -- On the trivializing base set the composite readout matches the composition of the readouts.
  refine hg.congr ?_
  filter_upwards [(trivializationAt F W x₀).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt F W x₀)] with x hx
  have hICp : ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)
      = ((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx : W x →L[ℝ] F).comp
          ((P x).comp
            (((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm : F →L[ℝ] W x)) :=
    ContinuousLinearMap.inCoordinates_eq hx hx
  have hICq : ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (Q x)
      = ((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx : W x →L[ℝ] F).comp
          ((Q x).comp
            (((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm : F →L[ℝ] W x)) :=
    ContinuousLinearMap.inCoordinates_eq hx hx
  have keyP : ∀ u : F,
      ((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm
          (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x) u)
        = P x (((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm u) := by
    intro u
    rw [hICp]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  have keyQ : ∀ v : F,
      ((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm
          (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (Q x) v)
        = Q x (((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm v) := by
    intro v
    rw [hICq]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  ext u v
  rw [ContinuousLinearMap.bilinearComp_apply,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx (s x)
      (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x) u)
      (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (Q x) v),
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx
      ((s x).bilinearComp (P x) (Q x)) u v,
    ContinuousLinearMap.bilinearComp_apply, keyP u, keyQ v]

/-- **The bilinear-form trivialization readout of a fiberwise two-sided composition is the
model-fibre `bilinearComp` of the readouts.**  On the trivializing base set of `x₀`, the
`BilinearFormBundle` coordinate readout of `(s x).bilinearComp (P x) (Q x)` equals the `bilinearComp`
of the coordinate readout of `s x` with the endomorphism readouts `inCoordinates F W F W x₀ x x₀ x
(P x)` and `… (Q x)` — an identity entirely inside the clean model fibre `BilF = F →L[ℝ] F →L[ℝ] ℝ`
(never the raw `BilW x` fibre).

This is the pointwise readout identity internal to `continuous_bilinearComp₂_section`, extracted as a
standalone reusable lemma.  Its purpose is the section-space Ricci–DeTurck reaction operator at the
tangent bundle `W := TangentSpace I`: there the raw fibre norms `‖BilW x‖ = ‖TM x →L[ℝ] TM x →L[ℝ] ℝ‖`
and `‖P x‖ = ‖TM x →L[ℝ] TM x‖` are not synthesizable (the transported-instance diamond / nested-CLM
`synthInstance` blow-up), so the reaction operator's Lipschitz/coordinate bound must be phrased through
the trivialization readout in the clean model fibre.  This lemma is exactly that reduction: it rewrites
the readout of the reaction's fibre value as a `bilinearComp` of clean-fibre readouts, whose operator
norm is controlled by `ContinuousLinearMap.norm_bilinearComp_le` over `BilF`/`F →L[ℝ] F` (no `BilW`
norm, no `RiemannianBundle`). -/
theorem trivializationAt_bilinearFormBundle_bilinearComp_readout_eq
    (s : Π x : M, BilW x) (P Q : Π x : M, W x →L[ℝ] W x)
    (x₀ x : M) (hx : x ∈ (trivializationAt F W x₀).baseSet) :
    (trivializationAt BilF BilW x₀
        (TotalSpace.mk' BilF x ((s x).bilinearComp (P x) (Q x)))).2
      = ((trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2).bilinearComp
          (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x))
          (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (Q x)) := by
  have hICp : ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)
      = ((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx : W x →L[ℝ] F).comp
          ((P x).comp
            (((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm : F →L[ℝ] W x)) :=
    ContinuousLinearMap.inCoordinates_eq hx hx
  have hICq : ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (Q x)
      = ((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx : W x →L[ℝ] F).comp
          ((Q x).comp
            (((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm : F →L[ℝ] W x)) :=
    ContinuousLinearMap.inCoordinates_eq hx hx
  have keyP : ∀ u : F,
      ((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm
          (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x) u)
        = P x (((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm u) := by
    intro u
    rw [hICp]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  have keyQ : ∀ v : F,
      ((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm
          (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (Q x) v)
        = Q x (((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm v) := by
    intro v
    rw [hICq]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  ext u v
  rw [ContinuousLinearMap.bilinearComp_apply,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx (s x)
      (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x) u)
      (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (Q x) v),
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx
      ((s x).bilinearComp (P x) (Q x)) u v,
    ContinuousLinearMap.bilinearComp_apply, keyP u, keyQ v]

/-- **The model-fibre readout norm bound for a fiberwise two-sided bilinear composition.**  The
operator norm of the `BilinearFormBundle` coordinate readout of `(s x).bilinearComp (P x) (Q x)` is
bounded by the product of the readout norm of `s x` and the model-fibre endomorphism readout norms
`‖inCoordinates F W F W x₀ x x₀ x (P x)‖`, `‖… (Q x)‖`.  A direct consequence of the readout identity
`trivializationAt_bilinearFormBundle_bilinearComp_readout_eq` and
`ContinuousLinearMap.norm_bilinearComp_le`.

Every norm on the right lives in the **clean model fibre** (`BilF = F →L[ℝ] F →L[ℝ] ℝ` and
`F →L[ℝ] F`); no `‖BilW x‖` or `‖W x →L[ℝ] W x‖` appears.  This is the exact fiber-level Lipschitz/size
estimate the section-space Ricci–DeTurck reaction operator needs, in a form that **elaborates at the
tangent bundle** `W := TangentSpace I` (where the raw fibre norms are un-synthesizable): the
endomorphism size datum enters only through its `E`-valued coordinate readout. -/
theorem norm_trivializationAt_bilinearFormBundle_bilinearComp_readout_le
    (s : Π x : M, BilW x) (P Q : Π x : M, W x →L[ℝ] W x)
    (x₀ x : M) (hx : x ∈ (trivializationAt F W x₀).baseSet) :
    ‖(trivializationAt BilF BilW x₀
        (TotalSpace.mk' BilF x ((s x).bilinearComp (P x) (Q x)))).2‖
      ≤ ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2‖
          * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)‖
          * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (Q x)‖ := by
  rw [trivializationAt_bilinearFormBundle_bilinearComp_readout_eq s P Q x₀ x hx]
  exact ContinuousLinearMap.norm_bilinearComp_le _ _ _

/-- **Additivity of the bilinear-form trivialization readout.**  On the trivializing base set the
`BilinearFormBundle` coordinate readout is additive in the fibre value: the readout of `b + c`
equals the sum of the readouts of `b` and `c`.  A direct consequence of the fiberwise linearity of
the trivialization (`trivializationAt_bilinearFormBundle_apply_eq`).

This is the readout-linearity input consumed by any coordinate difference/Lipschitz bound in the
continuous section space at the tangent bundle: it lets the readout of a sum of reaction summands
(such as the two halves of the DeTurck-correction derivation) be split before estimating, staying in
the clean model fibre `BilF = F →L[ℝ] F →L[ℝ] ℝ` throughout. -/
theorem trivializationAt_bilinearFormBundle_readout_add
    (x₀ x : M) (hx : x ∈ (trivializationAt F W x₀).baseSet) (b c : BilW x) :
    (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (b + c))).2
      = (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x b)).2
        + (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x c)).2 := by
  ext u v
  simp only [ContinuousLinearMap.add_apply]
  rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx (b + c) u v,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx b u v,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx c u v]
  simp [ContinuousLinearMap.add_apply]

/-- **Subtractivity of the bilinear-form trivialization readout.**  On the trivializing base set the
`BilinearFormBundle` coordinate readout is subtractive in the fibre value: the readout of `b - c`
equals the difference of the readouts of `b` and `c`.  A direct consequence of the fiberwise
linearity of the trivialization (`trivializationAt_bilinearFormBundle_apply_eq`).

This is the readout-linearity input consumed by the coordinate *Lipschitz* bound in the continuous
section space: the bridge's `hlip` obligation is stated as `dist (coord (A t s) i x)
(coord (A t s') i x) ≤ K · dist s s'`, and `dist` in the model fibre `BilF` is `‖· - ·‖`, so the two
readouts of the two states must be combined into the readout of their fibrewise difference before the
reaction size estimate is applied — all inside the clean model fibre. -/
theorem trivializationAt_bilinearFormBundle_readout_sub
    (x₀ x : M) (hx : x ∈ (trivializationAt F W x₀).baseSet) (b c : BilW x) :
    (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (b - c))).2
      = (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x b)).2
        - (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x c)).2 := by
  ext u v
  simp only [ContinuousLinearMap.sub_apply]
  rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx (b - c) u v,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx b u v,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx c u v]
  simp [ContinuousLinearMap.sub_apply]

/-- **The model-fibre readout of the identity endomorphism is the model identity.**  On the
trivializing base set, the endomorphism coordinate readout of `ContinuousLinearMap.id ℝ (W x)` is
`ContinuousLinearMap.id ℝ F` (the trivialization change of coordinates conjugates the identity to the
identity).  Consequence of `ContinuousLinearMap.inCoordinates_eq` and
`ContinuousLinearEquiv.coe_comp_coe_symm`. -/
theorem inCoordinates_id_eq_id
    (x₀ x : M) (hx : x ∈ (trivializationAt F W x₀).baseSet) :
    ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (ContinuousLinearMap.id ℝ (W x))
      = ContinuousLinearMap.id ℝ F := by
  rw [ContinuousLinearMap.inCoordinates_eq hx hx, ContinuousLinearMap.id_comp]
  exact ContinuousLinearEquiv.coe_comp_coe_symm _

/-- **The model-fibre readout of the identity endomorphism has norm at most `1`.**  Immediate from
`inCoordinates_id_eq_id` and `ContinuousLinearMap.norm_id_le`.  This is the fibre-level size datum
that lets the `‖id‖`-weighted slots of the DeTurck-correction derivation be absorbed into the
constant `2`. -/
theorem norm_inCoordinates_id_le
    (x₀ x : M) (hx : x ∈ (trivializationAt F W x₀).baseSet) :
    ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (ContinuousLinearMap.id ℝ (W x))‖ ≤ 1 := by
  rw [inCoordinates_id_eq_id (F := F) (W := W) x₀ x hx]
  exact ContinuousLinearMap.norm_id_le
/-- **The model-fibre readout norm bound for the two-sided DeTurck-correction derivation.**  The
operator norm of the `BilinearFormBundle` coordinate readout of the derivation value
`(s x).bilinearComp (P x) id + (s x).bilinearComp id (P x)` — the fibre value of the intrinsic
Ricci–DeTurck correction `(u, v) ↦ s x (P x u) v + s x u (P x v)` with the endomorphism coefficient
`P` frozen — is bounded by `2 · ‖readout (s x)‖ · ‖inCoordinates … (P x)‖`.

This is the exact fibre-level Lipschitz/size estimate for the *correct* DeTurck reaction shape (a
two-sided derivation, not a conjugation), stated entirely through the clean model-fibre readouts
`BilF = F →L[ℝ] F →L[ℝ] ℝ` and `F →L[ℝ] F`: no `‖BilW x‖` or `‖W x →L[ℝ] W x‖` appears, so it
**elaborates at the tangent bundle** `W := TangentSpace I` (where the raw fibre norms are
un-synthesizable).  Built from the plain composition readout bound
`norm_trivializationAt_bilinearFormBundle_bilinearComp_readout_le` on each of the two one-sided
summands, `norm_add_le` on the readout sum (via `trivializationAt_bilinearFormBundle_readout_add`),
and the `‖id‖`-slot bound `norm_inCoordinates_id_le`. -/
theorem norm_trivializationAt_bilinearFormBundle_deTurckDerivation_readout_le
    (s : Π x : M, BilW x) (P : Π x : M, W x →L[ℝ] W x)
    (x₀ x : M) (hx : x ∈ (trivializationAt F W x₀).baseSet) :
    ‖(trivializationAt BilF BilW x₀
        (TotalSpace.mk' BilF x
          ((s x).bilinearComp (P x) (ContinuousLinearMap.id ℝ (W x))
            + (s x).bilinearComp (ContinuousLinearMap.id ℝ (W x)) (P x)))).2‖
      ≤ 2 * ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2‖
          * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)‖ := by
  have hid : ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x
      (ContinuousLinearMap.id ℝ (W x))‖ ≤ 1 := norm_inCoordinates_id_le (F := F) (W := W) x₀ x hx
  rw [trivializationAt_bilinearFormBundle_readout_add (F := F) (W := W) x₀ x hx
    ((s x).bilinearComp (P x) (ContinuousLinearMap.id ℝ (W x)))
    ((s x).bilinearComp (ContinuousLinearMap.id ℝ (W x)) (P x))]
  refine (norm_add_le
    ((trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x
        ((s x).bilinearComp (P x) (ContinuousLinearMap.id ℝ (W x))))).2)
    ((trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x
        ((s x).bilinearComp (ContinuousLinearMap.id ℝ (W x)) (P x)))).2)).trans ?_
  have h₁ : ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x
        ((s x).bilinearComp (P x) (ContinuousLinearMap.id ℝ (W x))))).2‖
      ≤ ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2‖
          * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)‖ := by
    refine (norm_trivializationAt_bilinearFormBundle_bilinearComp_readout_le
      s P (fun y => ContinuousLinearMap.id ℝ (W y)) x₀ x hx).trans ?_
    calc ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2‖
            * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)‖
            * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (ContinuousLinearMap.id ℝ (W x))‖
          ≤ ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2‖
            * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)‖ * 1 := by gcongr
      _ = ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2‖
            * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)‖ := mul_one _
  have h₂ : ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x
        ((s x).bilinearComp (ContinuousLinearMap.id ℝ (W x)) (P x)))).2‖
      ≤ ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2‖
          * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)‖ := by
    refine (norm_trivializationAt_bilinearFormBundle_bilinearComp_readout_le
      s (fun y => ContinuousLinearMap.id ℝ (W y)) P x₀ x hx).trans ?_
    calc ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2‖
            * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (ContinuousLinearMap.id ℝ (W x))‖
            * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)‖
          ≤ ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2‖ * 1
            * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)‖ := by gcongr
      _ = ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2‖
            * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)‖ := by rw [mul_one]
  have hrw : 2 * ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2‖
        * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)‖
      = ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2‖
          * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)‖
        + ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2‖
          * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)‖ := by ring
  rw [hrw]
  exact add_le_add h₁ h₂
/-- **The coordinate Lipschitz bound for the frozen-coefficient DeTurck-correction reaction.**  The
model-fibre readout of the two-sided DeTurck-correction derivation is Lipschitz in the fibre value
with constant `2 · ‖inCoordinates … (P x)‖`: the difference of the readouts of the derivation at two
states `s x`, `s' x` (with a *common* frozen endomorphism `P`) is bounded by `2 · ‖inCoordinates …
(P x)‖` times the difference of the readouts of the two states.

This is **exactly the fibre content of the section-space Picard `hlip` obligation** for the
frozen-coefficient reaction operator: the bridge's Lipschitz hypothesis reads
`dist (coord (A t s) i x) (coord (A t s') i x) ≤ K · dist s s'`, and since the continuous-section
coordinate `coord σ i x` is definitionally the trivialization readout
`(trivializationAt BilF BilW (x0 i) (TotalSpace.mk' BilF x (σ x))).2` (`coordContinuousMap_apply`)
and `dist` in the model fibre is `‖· - ·‖`, this lemma supplies the pointwise constant `2 · ‖readout
P‖` for the DeTurck reaction `A t s = (u, v) ↦ s x (P x u) v + s x u (P x v)`.  Everything stays in
the clean model fibre `BilF = F →L[ℝ] F →L[ℝ] ℝ` / `F →L[ℝ] F`, so it **elaborates at the tangent
bundle** `W := TangentSpace I`.  Proof: combine the two state readouts into the readout of their
fibrewise difference (`trivializationAt_bilinearFormBundle_readout_sub`), use the additivity of the
derivation in the fibre value (`bilinearComp` is linear in its first slot), and apply the derivation
size bound `norm_trivializationAt_bilinearFormBundle_deTurckDerivation_readout_le` to the difference
section. -/
theorem norm_trivializationAt_bilinearFormBundle_deTurckDerivation_readout_sub_le
    (s s' : Π x : M, BilW x) (P : Π x : M, W x →L[ℝ] W x)
    (x₀ x : M) (hx : x ∈ (trivializationAt F W x₀).baseSet) :
    ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x
          ((s x).bilinearComp (P x) (ContinuousLinearMap.id ℝ (W x))
            + (s x).bilinearComp (ContinuousLinearMap.id ℝ (W x)) (P x)))).2
        - (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x
          ((s' x).bilinearComp (P x) (ContinuousLinearMap.id ℝ (W x))
            + (s' x).bilinearComp (ContinuousLinearMap.id ℝ (W x)) (P x)))).2‖
      ≤ 2 * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x (P x)‖
          * ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s x))).2
              - (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (s' x))).2‖ := by
  have hlin : (s x).bilinearComp (P x) (ContinuousLinearMap.id ℝ (W x))
          + (s x).bilinearComp (ContinuousLinearMap.id ℝ (W x)) (P x)
        - ((s' x).bilinearComp (P x) (ContinuousLinearMap.id ℝ (W x))
          + (s' x).bilinearComp (ContinuousLinearMap.id ℝ (W x)) (P x))
      = (s x - s' x).bilinearComp (P x) (ContinuousLinearMap.id ℝ (W x))
          + (s x - s' x).bilinearComp (ContinuousLinearMap.id ℝ (W x)) (P x) := by
    ext u v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.id_apply]
    ring
  rw [← trivializationAt_bilinearFormBundle_readout_sub (F := F) (W := W) x₀ x hx
      ((s x).bilinearComp (P x) (ContinuousLinearMap.id ℝ (W x))
        + (s x).bilinearComp (ContinuousLinearMap.id ℝ (W x)) (P x))
      ((s' x).bilinearComp (P x) (ContinuousLinearMap.id ℝ (W x))
        + (s' x).bilinearComp (ContinuousLinearMap.id ℝ (W x)) (P x)),
    hlin,
    ← trivializationAt_bilinearFormBundle_readout_sub (F := F) (W := W) x₀ x hx (s x) (s' x)]
  refine (norm_trivializationAt_bilinearFormBundle_deTurckDerivation_readout_le
    (fun y => s y - s' y) P x₀ x hx).trans (le_of_eq ?_)
  ring

end BilinearConjugation

section FiberwiseSymmetrization
variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "BilW" => BilinearFormBundle (V := W)

local instance bilFNormedAddCommGroup : NormedAddCommGroup BilF := inferInstance
local instance bilFNormedSpace : NormedSpace ℝ BilF := inferInstance

/-- Fiberwise slot-flip for bilinear-form sections. -/
noncomputable def flipBilinearSection (s : Π x : M, BilW x) : Π x : M, BilW x :=
  fun x ↦ ContinuousLinearMap.flipBilinear (E := W x) (s x)

@[simp] lemma flipBilinearSection_apply_apply
    (s : Π x : M, BilW x) (x : M) (u v : W x) :
    flipBilinearSection (W := W) s x u v = s x v u := by
  simp [flipBilinearSection]

/-- Fiberwise symmetrization for bilinear-form sections. -/
noncomputable def symmetrizeBilinearSection (s : Π x : M, BilW x) : Π x : M, BilW x :=
  fun x ↦ ContinuousLinearMap.symmetrizeBilinear (E := W x) (s x)

@[simp] lemma symmetrizeBilinearSection_apply_apply
    (s : Π x : M, BilW x) (x : M) (u v : W x) :
    symmetrizeBilinearSection (W := W) s x u v = (s x u v + s x v u) / 2 := by
  simp [symmetrizeBilinearSection]

@[simp] lemma symmetrizeBilinearSection_apply_self
    (s : Π x : M, BilW x) (x : M) (u : W x) :
    symmetrizeBilinearSection (W := W) s x u u = s x u u := by
  simp

lemma symmetrizeBilinearSection_forall_symmetric
    (s : Π x : M, BilW x) :
    ∀ x : M, ∀ u v : W x,
      symmetrizeBilinearSection (W := W) s x u v =
        symmetrizeBilinearSection (W := W) s x v u := by
  intro x u v
  simp [add_comm]

lemma symmetrizeBilinearSection_forall_pos_iff
    (s : Π x : M, BilW x) :
    (∀ x : M, ∀ u : W x, u ≠ 0 →
      0 < symmetrizeBilinearSection (W := W) s x u u) ↔
      ∀ x : M, ∀ u : W x, u ≠ 0 → 0 < s x u u := by
  constructor <;> intro h x u hu <;> simpa using h x u hu

/-- Preferred coordinates commute with fiberwise slot-flip. -/
lemma trivializationAt_bilinearFormBundle_flipSection_eq
    (s : Π x : M, BilW x) (x0 x : M)
    (hx : x ∈ (trivializationAt F W x0).baseSet) :
    (trivializationAt BilF BilW x0 ⟨x, flipBilinearSection (W := W) s x⟩).2 =
      ContinuousLinearMap.flipBilinear (E := F)
        ((trivializationAt BilF BilW x0 ⟨x, s x⟩).2) := by
  ext u v
  rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x0 x hx]
  simp [flipBilinearSection]
  rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x0 x hx]
  simp

/-- Preferred coordinates commute with fiberwise symmetrization. -/
lemma trivializationAt_bilinearFormBundle_symmetrizeSection_eq
    (s : Π x : M, BilW x) (x0 x : M)
    (hx : x ∈ (trivializationAt F W x0).baseSet) :
    (trivializationAt BilF BilW x0 ⟨x, symmetrizeBilinearSection (W := W) s x⟩).2 =
      ContinuousLinearMap.symmetrizeBilinear (E := F)
        ((trivializationAt BilF BilW x0 ⟨x, s x⟩).2) := by
  ext u v
  rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x0 x hx]
  simp [symmetrizeBilinearSection]
  rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x0 x hx]
  rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x0 x hx]
  simp

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
variable [ChartedSpace HB M]

/-- Fiberwise symmetrization preserves spatial smoothness of bilinear-form sections.  In local
preferred coordinates it is the fixed continuous linear symmetrization operator on the model fiber. -/
lemma contMDiff_symmetrizeBilinearSection
    {s : Π x : M, BilW x}
    (hs : ContMDiff IB (IB.prod 𝓘(ℝ, BilF)) n
      (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (s x))) :
    ContMDiff IB (IB.prod 𝓘(ℝ, BilF)) n
      (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x
        (_root_.Bundle.symmetrizeBilinearSection (W := W) s x)) := by
  intro x0
  have hsx := hs x0
  rw [Bundle.contMDiffAt_section (IB := IB) (F := BilF) (E := BilW) (s := s) x0] at hsx
  rw [Bundle.contMDiffAt_section (IB := IB) (F := BilF) (E := BilW)
      (s := _root_.Bundle.symmetrizeBilinearSection (W := W) s) x0]
  let L : BilF →L[ℝ] BilF := ContinuousLinearMap.symmetrizeBilinear (E := F)
  have hcomp : ContMDiffAt IB 𝓘(ℝ, BilF) n
      (fun x ↦ L ((trivializationAt BilF BilW x0 ⟨x, s x⟩).2)) x0 := by
    simpa [Function.comp_def, L] using
      (L.contMDiffAt (n := n)).comp x0 hsx
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [((trivializationAt F W x0).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt F W x0))] with x hx
  simpa [L] using
    (trivializationAt_bilinearFormBundle_symmetrizeSection_eq
      (W := W) s x0 x hx)

end FiberwiseSymmetrization

end Bundle

namespace PoincareCurvature

namespace Bundle.Trivialization

section CoordinatePositivity

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)

local instance bilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ))

local instance bilFPseudoMetricSpace : PseudoMetricSpace BilF :=
  (inferInstance : PseudoMetricSpace (F →L[ℝ] F →L[ℝ] ℝ))

variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilW" => _root_.Bundle.BilinearFormBundle (V := W)

local instance bilWAddCommGroup (x : M) : AddCommGroup (BilW x) := inferInstance
local instance bilWModule (x : M) : Module ℝ (BilW x) := inferInstance
local instance bilWIsTopologicalAddGroup (x : M) : IsTopologicalAddGroup (BilW x) :=
  inferInstance
local instance bilWContinuousSMul (x : M) : ContinuousSMul ℝ (BilW x) :=
  inferInstance
/-- Symmetric bilinear forms in a single bundle fiber form a convex subset. -/
lemma convex_fiber_setOf_forall_symmetric (x : M) :
    Convex ℝ ({B : BilW x | ∀ v w : W x, B v w = B w v} : Set (BilW x)) := by
  rw [convex_iff_forall_pos]
  intro B hB C hC a b _ _ _ v w
  simp [hB v w, hC v w]

/-- Positive-definite bilinear forms in a single bundle fiber form a convex subset. -/
lemma convex_fiber_setOf_forall_pos (x : M) :
    Convex ℝ ({B : BilW x | ∀ v : W x, v ≠ 0 → 0 < B v v} : Set (BilW x)) := by
  rw [convex_iff_forall_pos]
  intro B hB C hC a b ha hb hab v hv
  have hleft : 0 < a * B v v := mul_pos ha (hB v hv)
  have hright : 0 ≤ b * C v v := mul_nonneg hb.le (le_of_lt (hC v hv))
  simpa [smul_eq_mul] using add_pos_of_pos_of_nonneg hleft hright

/-- Symmetric positive-definite bilinear forms in a single bundle fiber form a convex subset. -/
lemma convex_fiber_setOf_forall_symmetric_and_pos (x : M) :
    Convex ℝ
      ({B : BilW x | (∀ v w : W x, B v w = B w v) ∧
        ∀ v : W x, v ≠ 0 → 0 < B v v} : Set (BilW x)) := by
  rw [show ({B : BilW x | (∀ v w : W x, B v w = B w v) ∧
      ∀ v : W x, v ≠ 0 → 0 < B v v} : Set (BilW x)) =
      {B : BilW x | ∀ v w : W x, B v w = B w v} ∩
        {B : BilW x | ∀ v : W x, v ≠ 0 → 0 < B v v} by rfl]
  exact (convex_fiber_setOf_forall_symmetric x).inter
    (convex_fiber_setOf_forall_pos x)

/-- Coordinatewise slot-flip on compact continuous families of model bilinear forms. This is the
compact-coordinate operator that must later be shown to preserve the finite-cover compatibility
kernel in order to produce the global section-space slot-swap map. -/
noncomputable def flipBilinearCoordContinuousLinearMap
    (K : TopologicalSpace.Compacts M) :
    C(K, BilF) →L[ℝ] C(K, BilF) :=
  (_root_.Bundle.ContinuousLinearMap.flipBilinear (E := F)).compLeftContinuous ℝ K

@[simp] lemma flipBilinearCoordContinuousLinearMap_apply_apply
    (K : TopologicalSpace.Compacts M) (u : C(K, BilF)) (x : K) (v w : F) :
    flipBilinearCoordContinuousLinearMap (M := M) (F := F) K u x v w = u x w v := by
  change (_root_.Bundle.ContinuousLinearMap.flipBilinear (E := F) (u x)) v w = u x w v
  rw [_root_.Bundle.ContinuousLinearMap.flipBilinear_apply_apply]

lemma flipBilinearCoordContinuousLinearMap_forall_pos_iff
    (K : TopologicalSpace.Compacts M) (u : C(K, BilF)) :
    (∀ x : K, ∀ v : F, v ≠ 0 →
      0 < flipBilinearCoordContinuousLinearMap (M := M) (F := F) K u x v v) ↔
      ∀ x : K, ∀ v : F, v ≠ 0 → 0 < u x v v := by
  simp

/-- Coordinatewise symmetrization on compact continuous families of model bilinear forms. -/
noncomputable def symmetrizeBilinearCoordContinuousLinearMap
    (K : TopologicalSpace.Compacts M) :
    C(K, BilF) →L[ℝ] C(K, BilF) :=
  (_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear (E := F)).compLeftContinuous ℝ K

@[simp] lemma symmetrizeBilinearCoordContinuousLinearMap_apply_apply
    (K : TopologicalSpace.Compacts M) (u : C(K, BilF)) (x : K) (v w : F) :
    symmetrizeBilinearCoordContinuousLinearMap (M := M) (F := F) K u x v w =
      (u x v w + u x w v) / 2 := by
  change (_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear (E := F) (u x)) v w =
    (u x v w + u x w v) / 2
  rw [_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear_apply_apply]

@[simp] lemma symmetrizeBilinearCoordContinuousLinearMap_apply_self
    (K : TopologicalSpace.Compacts M) (u : C(K, BilF)) (x : K) (v : F) :
    symmetrizeBilinearCoordContinuousLinearMap (M := M) (F := F) K u x v v =
      u x v v := by
  simp

lemma symmetrizeBilinearCoordContinuousLinearMap_forall_symmetric
    (K : TopologicalSpace.Compacts M) (u : C(K, BilF)) :
    ∀ x : K, ∀ v w : F,
      symmetrizeBilinearCoordContinuousLinearMap (M := M) (F := F) K u x v w =
        symmetrizeBilinearCoordContinuousLinearMap (M := M) (F := F) K u x w v := by
  intro x v w
  simp [symmetrizeBilinearCoordContinuousLinearMap_apply_apply, add_comm]

lemma symmetrizeBilinearCoordContinuousLinearMap_forall_pos_iff
    (K : TopologicalSpace.Compacts M) (u : C(K, BilF)) :
    (∀ x : K, ∀ v : F, v ≠ 0 →
      0 < symmetrizeBilinearCoordContinuousLinearMap (M := M) (F := F) K u x v v) ↔
      ∀ x : K, ∀ v : F, v ≠ 0 → 0 < u x v v := by
  constructor <;> intro h x v hv <;> simpa using h x v hv

/-- Coordinatewise symmetrization does not increase compact-map distance to a pointwise symmetric
coordinate map. -/
lemma dist_symmetrizeBilinearCoordContinuousLinearMap_le_of_forall_symmetric
    (K : TopologicalSpace.Compacts M) {u g : C(K, BilF)}
    (hg : ∀ x : K, ∀ v w : F, g x v w = g x w v) :
    dist (symmetrizeBilinearCoordContinuousLinearMap (M := M) (F := F) K u) g ≤
      dist u g := by
  rw [dist_eq_norm, dist_eq_norm]
  refine (ContinuousMap.norm_le (f :=
    symmetrizeBilinearCoordContinuousLinearMap (M := M) (F := F) K u - g)
    (norm_nonneg _)).mpr ?_
  intro x
  calc
    ‖(symmetrizeBilinearCoordContinuousLinearMap (M := M) (F := F) K u - g) x‖ =
        dist (_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear (E := F) (u x)) (g x) := by
      rw [dist_eq_norm]
      rfl
    _ ≤ dist (u x) (g x) :=
      _root_.Bundle.ContinuousLinearMap.dist_symmetrizeBilinear_le_of_symmetric (hg x)
    _ = ‖(u - g) x‖ := by
      rw [dist_eq_norm]
      rfl
    _ ≤ ‖u - g‖ := (u - g).norm_coe_le_norm x

/-- Coordinatewise slot-flip on the ambient finite product of compact bilinear-form coordinate
families. The next global section-space step is proving that this map preserves the finite-cover
compatibility kernel for preferred bilinear-form trivializations. -/
noncomputable def flipBilinearCoordFamilyContinuousLinearMap
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M) :
    CoordFamily (M := M) (F := BilF) Kc →L[ℝ]
      CoordFamily (M := M) (F := BilF) Kc :=
  ContinuousLinearMap.piMap fun i ↦ flipBilinearCoordContinuousLinearMap (M := M) (F := F) (Kc i)

@[simp] lemma flipBilinearCoordFamilyContinuousLinearMap_apply_apply
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M)
    (u : CoordFamily (M := M) (F := BilF) Kc)
    (i : κ) (x : Kc i) (v w : F) :
    flipBilinearCoordFamilyContinuousLinearMap Kc u i x v w =
      u i x w v := by
  rfl

lemma flipBilinearCoordFamilyContinuousLinearMap_forall_pos_iff
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M)
    (u : CoordFamily (M := M) (F := BilF) Kc) :
    (∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 →
      0 < flipBilinearCoordFamilyContinuousLinearMap Kc u i x v v) ↔
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v := by
  simp

lemma flipBilinearCoordFamilyContinuousLinearMap_eq_self_iff
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M)
    (u : CoordFamily (M := M) (F := BilF) Kc) :
    flipBilinearCoordFamilyContinuousLinearMap Kc u = u ↔
      ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v := by
  constructor
  · intro h i x v w
    have h' := congrArg (fun U : CoordFamily (M := M) (F := BilF) Kc => U i x v w) h
    have h'' : u i x w v = u i x v w := by
      simpa using h'
    exact h''.symm
  · intro h
    funext i
    ext x v w
    simpa using h i x w v

/-- Coordinatewise symmetrization on the ambient finite product of compact bilinear-form coordinate
families. -/
noncomputable def symmetrizeBilinearCoordFamilyContinuousLinearMap
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M) :
    CoordFamily (M := M) (F := BilF) Kc →L[ℝ]
      CoordFamily (M := M) (F := BilF) Kc :=
  ContinuousLinearMap.piMap fun i ↦
    symmetrizeBilinearCoordContinuousLinearMap (M := M) (F := F) (Kc i)

@[simp] lemma symmetrizeBilinearCoordFamilyContinuousLinearMap_apply_apply
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M)
    (u : CoordFamily (M := M) (F := BilF) Kc)
    (i : κ) (x : Kc i) (v w : F) :
    symmetrizeBilinearCoordFamilyContinuousLinearMap Kc u i x v w =
      (u i x v w + u i x w v) / 2 := by
  simp [symmetrizeBilinearCoordFamilyContinuousLinearMap]

@[simp] lemma symmetrizeBilinearCoordFamilyContinuousLinearMap_apply_self
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M)
    (u : CoordFamily (M := M) (F := BilF) Kc)
    (i : κ) (x : Kc i) (v : F) :
    symmetrizeBilinearCoordFamilyContinuousLinearMap Kc u i x v v =
      u i x v v := by
  simp

lemma symmetrizeBilinearCoordFamilyContinuousLinearMap_forall_symmetric
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M)
    (u : CoordFamily (M := M) (F := BilF) Kc) :
    ∀ i : κ, ∀ x : Kc i, ∀ v w : F,
      symmetrizeBilinearCoordFamilyContinuousLinearMap Kc u i x v w =
        symmetrizeBilinearCoordFamilyContinuousLinearMap Kc u i x w v := by
  intro i x v w
  simp [symmetrizeBilinearCoordFamilyContinuousLinearMap_apply_apply, add_comm]

lemma symmetrizeBilinearCoordFamilyContinuousLinearMap_forall_pos_iff
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M)
    (u : CoordFamily (M := M) (F := BilF) Kc) :
    (∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 →
      0 < symmetrizeBilinearCoordFamilyContinuousLinearMap Kc u i x v v) ↔
       ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v := by
  constructor <;> intro h i x v hv <;> simpa using h i x v hv

/-- For preferred bilinear-form trivializations, coordinatewise symmetrization preserves the finite
overlap compatibility equations. This is the key coordinate-level substitute for applying
fiberwise symmetrization directly to tangent-space bilinear forms, which would require unavailable
normed tangent-fiber instances. -/
lemma symmetrizeBilinearCoordFamilyContinuousLinearMap_mem_compatibleCoordFamilySubmodule
    {κ : Type*}
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    {u : CoordFamily (M := M) (F := BilF) Kc}
    (hu : u ∈ compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo) :
    symmetrizeBilinearCoordFamilyContinuousLinearMap (M := M) (F := F) Kc u ∈
      compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo := by
  letI : AddCommMonoid BilF := ContinuousLinearMap.addCommMonoid
  letI : Module ℝ BilF := ContinuousLinearMap.module
  letI : ∀ x : M, AddCommMonoid (BilW x) := fun _ => ContinuousLinearMap.addCommMonoid
  letI : ∀ x : M, Module ℝ (BilW x) := fun _ => ContinuousLinearMap.module
  letI : FiberBundle (F →L[ℝ] ℝ) (fun x : M => W x →L[ℝ] ℝ) := inferInstance
  letI : VectorBundle ℝ (F →L[ℝ] ℝ) (fun x : M => W x →L[ℝ] ℝ) := inferInstance
  letI : FiberBundle BilF BilW := inferInstance
  letI : VectorBundle ℝ BilF BilW := inferInstance
  rw [mem_compatibleCoordFamilySubmodule_iff]
  intro i j
  haveI : MemTrivializationAtlas (trivializationAt BilF BilW (x0 i)) := inferInstance
  haveI : MemTrivializationAtlas (trivializationAt BilF BilW (x0 j)) := inferInstance
  haveI : (trivializationAt BilF BilW (x0 i)).IsLinear ℝ :=
    _root_.Bundle.trivializationAt_bilinearFormBundle_isLinear (F := F) (W := W) (x0 i)
  haveI : (trivializationAt BilF BilW (x0 j)).IsLinear ℝ :=
    _root_.Bundle.trivializationAt_bilinearFormBundle_isLinear (F := F) (W := W) (x0 j)
  ext x p q
  let xi : Kc i := ⟨x.1, (hKo i j x.2).1⟩
  let xj : Kc j := ⟨x.1, (hKo i j x.2).2⟩
  have hbase :
      x.1 ∈ (trivializationAt BilF BilW (x0 i)).baseSet ∩
        (trivializationAt BilF BilW (x0 j)).baseSet :=
    ⟨hKc i xi.2, hKc j xj.2⟩
  have hx_i : x.1 ∈ (trivializationAt F W (x0 i)).baseSet := by
    simpa using hbase.1
  have hx_j : x.1 ∈ (trivializationAt F W (x0 j)).baseSet := by
    simpa using hbase.2
  have hucomp :=
    (mem_compatibleCoordFamilySubmodule_iff
      (𝕜 := ℝ) (F := BilF) (fun i => trivializationAt BilF BilW (x0 i))
      Kc hKc Ko hKo (u := u)).1 hu i j
  have hcomp_x :
      (trivializationAt BilF BilW (x0 i)).coordChangeL ℝ
          (trivializationAt BilF BilW (x0 j)) x.1 (u i xi) = u j xj := by
    have h := congrArg (fun f : C(Ko i j, BilF) => f x) hucomp
    change
      (trivializationAt BilF BilW (x0 i)).coordChangeL ℝ
          (trivializationAt BilF BilW (x0 j)) x.1
          (u i ⟨x.1, (hKo i j x.2).1⟩) =
        u j ⟨x.1, (hKo i j x.2).2⟩ at h
    simpa [xi, xj] using h
  have htrans :
      ((trivializationAt BilF BilW (x0 j)) ⟨x.1,
          (trivializationAt BilF BilW (x0 i)).symm x.1
          (_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear (E := F) (u i xi))⟩).2 =
        _root_.Bundle.ContinuousLinearMap.symmetrizeBilinear (E := F)
          (((trivializationAt BilF BilW (x0 j))
            ⟨x.1, (trivializationAt BilF BilW (x0 i)).symm x.1 (u i xi)⟩).2) :=
    _root_.Bundle.trivializationAt_bilinearFormBundle_transition_symmetrizeBilinear
      (F := F) (W := W) (x0 := x0 i) (x1 := x0 j) (x := x.1)
      hx_i hx_j (u i xi)
  have horig :
      ((trivializationAt BilF BilW (x0 j))
        ⟨x.1, (trivializationAt BilF BilW (x0 i)).symm x.1 (u i xi)⟩).2 = u j xj := by
    rw [← hcomp_x]
    exact ((trivializationAt BilF BilW (x0 i)).coordChangeL_apply (R := ℝ)
      (trivializationAt BilF BilW (x0 j)) hbase (u i xi)).symm
  simp only [coordChangeContinuousMap_apply, restrictToCompact_apply,
    symmetrizeBilinearCoordFamilyContinuousLinearMap_apply_apply]
  calc
    ((trivializationAt BilF BilW (x0 i)).coordChangeL ℝ
        (trivializationAt BilF BilW (x0 j)) x.1
        (_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear (E := F) (u i xi))) p q =
        ((trivializationAt BilF BilW (x0 j))
          ⟨x.1, (trivializationAt BilF BilW (x0 i)).symm x.1
          (_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear (E := F) (u i xi))⟩).2 p q := by
      rw [(trivializationAt BilF BilW (x0 i)).coordChangeL_apply (R := ℝ)
        (trivializationAt BilF BilW (x0 j)) hbase]
    _ =
        (_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear (E := F)
          (((trivializationAt BilF BilW (x0 j))
            ⟨x.1, (trivializationAt BilF BilW (x0 i)).symm x.1 (u i xi)⟩).2)) p q := by
      exact congrArg (fun B : BilF => B p q) htrans
    _ =
        (_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear (E := F) (u j xj)) p q := by
      rw [horig]
    _ = (((restrictToCompact (fun _ hx ↦ (hKo i j hx).2)
        ((symmetrizeBilinearCoordFamilyContinuousLinearMap (M := M) (F := F) Kc) u j)) x) p) q := by
      rw [_root_.Bundle.ContinuousLinearMap.symmetrizeBilinear_apply_apply]
      change
        (((u j xj) p q + (u j xj) q p) / 2) =
          symmetrizeBilinearCoordContinuousLinearMap (M := M) (F := F) (Kc j) (u j) xj p q
      rw [symmetrizeBilinearCoordContinuousLinearMap_apply_apply]

/-- Coordinatewise symmetrization as a continuous linear self-map of the preferred finite-cover
compatibility kernel. This packages the overlap-preservation theorem into the actual Banach carrier
used by section-space arguments. -/
noncomputable def symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo →L[ℝ]
      compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup (CoordFamily (M := M) (F := BilF) Kc) := inferInstance
  letI : NormedSpace ℝ (CoordFamily (M := M) (F := BilF) Kc) := inferInstance
  let A : CoordFamily (M := M) (F := BilF) Kc →L[ℝ]
      CoordFamily (M := M) (F := BilF) Kc :=
    symmetrizeBilinearCoordFamilyContinuousLinearMap (M := M) (F := F) Kc
  let S : Submodule ℝ (CoordFamily (M := M) (F := BilF) Kc) :=
    compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo
  refine LinearMap.mkContinuous
    { toFun := fun u => ⟨A u.1,
        symmetrizeBilinearCoordFamilyContinuousLinearMap_mem_compatibleCoordFamilySubmodule
          (M := M) (F := F) (W := W) x0 Kc hKc Ko hKo u.2⟩
      map_add' := by
        intro u v
        ext i x p q
        simp [A]
      map_smul' := by
        intro c u
        ext i x p q
        simp [A] }
    ‖A‖ ?_
  intro u
  change ‖A u.1‖ ≤ ‖A‖ * ‖u.1‖
  exact ContinuousLinearMap.le_opNorm A u.1

@[simp]
lemma symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap_apply
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo) :
    (symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap
        (M := M) (F := F) (W := W) x0 Kc hKc Ko hKo u).1 =
      symmetrizeBilinearCoordFamilyContinuousLinearMap (M := M) (F := F) Kc u.1 :=
  by
    ext i x p q
    change (symmetrizeBilinearCoordFamilyContinuousLinearMap
      (M := M) (F := F) Kc u.1) i x p q =
      (symmetrizeBilinearCoordFamilyContinuousLinearMap
        (M := M) (F := F) Kc u.1) i x p q
    rfl

lemma symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap_forall_symmetric
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo) :
    ∀ i : κ, ∀ x : Kc i, ∀ v w : F,
      (symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap
        (M := M) (F := F) (W := W) x0 Kc hKc Ko hKo u).1 i x v w =
      (symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap
        (M := M) (F := F) (W := W) x0 Kc hKc Ko hKo u).1 i x w v := by
  intro i x v w
  rw [symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap_apply]
  exact symmetrizeBilinearCoordFamilyContinuousLinearMap_forall_symmetric
    (M := M) (F := F) Kc u.1 i x v w

lemma symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap_forall_pos_iff
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo) :
    (∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 →
      0 <
        (symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap
          (M := M) (F := F) (W := W) x0 Kc hKc Ko hKo u).1 i x v v) ↔
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u.1 i x v v := by
  rw [show
    (∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 →
      0 <
        (symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap
          (M := M) (F := F) (W := W) x0 Kc hKc Ko hKo u).1 i x v v) =
    (∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 →
      0 < (symmetrizeBilinearCoordFamilyContinuousLinearMap
        (M := M) (F := F) Kc u.1) i x v v) by
      simp [symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap_apply]]
  exact symmetrizeBilinearCoordFamilyContinuousLinearMap_forall_pos_iff
    (M := M) (F := F) Kc u.1

/-- Coordinate-family symmetrization does not increase the finite-product compact norm distance to a
pointwise symmetric coordinate family. -/
lemma dist_symmetrizeBilinearCoordFamilyContinuousLinearMap_le_of_forall_symmetric
    {κ : Type*} [Fintype κ] (Kc : κ → TopologicalSpace.Compacts M)
    {u g : CoordFamily (M := M) (F := BilF) Kc}
    (hg : ∀ i : κ, ∀ x : Kc i, ∀ v w : F, g i x v w = g i x w v) :
    dist (symmetrizeBilinearCoordFamilyContinuousLinearMap (M := M) (F := F) Kc u) g ≤
      dist u g := by
  rw [dist_eq_norm, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
  intro i
  calc
    ‖(symmetrizeBilinearCoordFamilyContinuousLinearMap (M := M) (F := F) Kc u - g) i‖ =
        dist (symmetrizeBilinearCoordContinuousLinearMap (M := M) (F := F) (Kc i) (u i))
          (g i) := by
      rw [dist_eq_norm]
      rfl
    _ ≤ dist (u i) (g i) :=
      dist_symmetrizeBilinearCoordContinuousLinearMap_le_of_forall_symmetric
        (M := M) (F := F) (Kc i) (hg i)
    _ = ‖(u - g) i‖ := by
      rw [dist_eq_norm]
      rfl
    _ ≤ ‖u - g‖ := norm_le_pi_norm (u - g) i

lemma dist_symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap_le_of_forall_symmetric
    {κ : Type*} [Fintype κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    {u g : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo}
    (hg : ∀ i : κ, ∀ x : Kc i, ∀ v w : F, g.1 i x v w = g.1 i x w v) :
    dist (symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap
        (M := M) (F := F) (W := W) x0 Kc hKc Ko hKo u) g ≤
      dist u g := by
  classical
  change dist
      (symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap
        (M := M) (F := F) (W := W) x0 Kc hKc Ko hKo u).1 g.1 ≤
    dist u.1 g.1
  rw [symmetrizeBilinearCompatibleCoordFamilyContinuousLinearMap_apply
    (M := M) (F := F) (W := W) x0 Kc hKc Ko hKo u]
  exact dist_symmetrizeBilinearCoordFamilyContinuousLinearMap_le_of_forall_symmetric
    (M := M) (F := F) Kc hg

/-- Coordinatewise antisymmetric defect on compact continuous families of model bilinear forms. -/
noncomputable def symmetryDefectCoordContinuousLinearMap
    (K : TopologicalSpace.Compacts M) :
    C(K, BilF) →L[ℝ] C(K, BilF) :=
  (_root_.Bundle.ContinuousLinearMap.symmetryDefect (E := F)).compLeftContinuous ℝ K

@[simp] lemma symmetryDefectCoordContinuousLinearMap_apply_apply
    (K : TopologicalSpace.Compacts M) (u : C(K, BilF)) (x : K) (v w : F) :
    symmetryDefectCoordContinuousLinearMap (M := M) (F := F) K u x v w =
      u x v w - u x w v := by
  change (_root_.Bundle.ContinuousLinearMap.symmetryDefect (E := F) (u x)) v w =
    u x v w - u x w v
  rw [_root_.Bundle.ContinuousLinearMap.symmetryDefect_apply_apply]

/-- Coordinatewise antisymmetric defect on finite products of compact coordinate families. -/
noncomputable def symmetryDefectCoordFamilyContinuousLinearMap
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M) :
    CoordFamily (M := M) (F := BilF) Kc →L[ℝ]
      CoordFamily (M := M) (F := BilF) Kc :=
  ContinuousLinearMap.piMap fun i ↦ symmetryDefectCoordContinuousLinearMap (M := M) (F := F) (Kc i)

@[simp] lemma symmetryDefectCoordFamilyContinuousLinearMap_apply_apply
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M)
    (u : CoordFamily (M := M) (F := BilF) Kc)
    (i : κ) (x : Kc i) (v w : F) :
    symmetryDefectCoordFamilyContinuousLinearMap Kc u i x v w =
      u i x v w - u i x w v := by
  rfl

lemma symmetryDefectCoordFamilyContinuousLinearMap_eq_zero_iff
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M)
    (u : CoordFamily (M := M) (F := BilF) Kc) :
    symmetryDefectCoordFamilyContinuousLinearMap Kc u = 0 ↔
      ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v := by
  constructor
  · intro h i x v w
    have h' := congrArg
      (fun U : CoordFamily (M := M) (F := BilF) Kc => U i x v w) h
    exact sub_eq_zero.mp (by simpa using h')
  · intro h
    funext i
    ext x v w
    simp [h i x v w]

/-- If a bundled bilinear-form section is pointwise positive-definite, then its compact local
coordinate map in the preferred bilinear-form trivialization is pointwise positive-definite on the
model fiber. -/
lemma coordContinuousMap_forall_pos_of_forall_pos
    (x0 : M) (K : TopologicalSpace.Compacts M)
    (hK : (K : Set M) ⊆ (trivializationAt BilF BilW x0).baseSet)
    {s : Π x : M, BilW x}
    (hs : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (s x)))
    (hpos : ∀ x : M, ∀ v : W x, v ≠ 0 → 0 < s x v v) :
    ∀ y : K, ∀ u : F, u ≠ 0 →
      0 <
        coordContinuousMap (e := trivializationAt BilF BilW x0)
          K hK hs.continuousOn y u u := by
  intro y u hu
  have hyW : y.1 ∈ (trivializationAt F W x0).baseSet := by
    simpa using hK y.2
  let e := (trivializationAt F W x0).continuousLinearEquivAt ℝ y.1 hyW
  have huW :
      (e.symm u) ≠ 0 := by
    intro h
    apply hu
    have hu0 : u = e 0 := by
      simpa using congrArg e h
    exact hu0.trans (by simpa using map_zero e)
  rw [coordContinuousMap_apply]
  erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_apply_eq
    (x0 := x0) (x := y.1) hyW (s y.1) u]
  exact hpos y.1 _ huW

/-- Around the compact preferred-coordinate image of a pointwise positive bilinear-form section,
there is a sup-norm ball of coordinate maps that stays pointwise positive-definite. -/
lemma exists_pos_ball_of_coordContinuousMap_of_forall_pos
    (x0 : M) (K : TopologicalSpace.Compacts M)
    (hK : (K : Set M) ⊆ (trivializationAt BilF BilW x0).baseSet)
    {s : Π x : M, BilW x}
    (hs : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (s x)))
    (hpos : ∀ x : M, ∀ v : W x, v ≠ 0 → 0 < s x v v)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    ∃ ε > 0, ∀ h : C(K, BilF),
      dist h (coordContinuousMap (e := trivializationAt BilF BilW x0)
        K hK hs.continuousOn) < ε →
      ∀ y : K, ∀ u : F, u ≠ 0 → 0 < h y u u := by
  obtain ⟨ε, hεpos, hε⟩ :=
    _root_.Bundle.ContinuousLinearMap.exists_pos_ball_of_continuousMap
      (g := coordContinuousMap (e := trivializationAt BilF BilW x0)
        K hK hs.continuousOn)
      (hpos := coordContinuousMap_forall_pos_of_forall_pos
        (x0 := x0) (K := K) hK hs hpos)
  exact ⟨ε, hεpos, hε⟩

/-- Coordinate families of bilinear forms that are pointwise positive-definite on every compact
piece form an open subset of the ambient finite product of compact `ContinuousMap` spaces. -/
lemma isOpen_setOf_coordFamily_forall_pos
    {κ : Type*} [Finite κ] (Kc : κ → TopologicalSpace.Compacts M)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsOpen ({u : CoordFamily (M := M) (F := BilF) Kc |
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
        Set (CoordFamily (M := M) (F := BilF) Kc)) := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  have hA : ∀ i : κ,
      IsOpen ({u : CoordFamily (M := M) (F := BilF) Kc |
        ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
          Set (CoordFamily (M := M) (F := BilF) Kc)) := by
    intro i
    let S : Set (C(Kc i, BilF)) := {g | ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < g x v v}
    have hopen : IsOpen S := by
      simpa [S] using
        (_root_.Bundle.ContinuousLinearMap.isOpen_setOf_continuousMap_forall_pos
          (α := Kc i) (E := F))
    have hπi : Continuous (fun u : CoordFamily (M := M) (F := BilF) Kc => u i) := by
      simpa using
        (continuous_apply i :
          Continuous fun u : CoordFamily (M := M) (F := BilF) Kc => u i)
    have hpre : IsOpen ((fun u : CoordFamily (M := M) (F := BilF) Kc => u i) ⁻¹' S) :=
      hopen.preimage hπi
    change IsOpen ((fun u : CoordFamily (M := M) (F := BilF) Kc => u i) ⁻¹' S)
    exact hpre
  have hfin : ∀ s : Finset κ,
      IsOpen ({u : CoordFamily (M := M) (F := BilF) Kc |
        ∀ i ∈ s, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
          Set (CoordFamily (M := M) (F := BilF) Kc)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have hUniv :
        ({u : CoordFamily (M := M) (F := BilF) Kc |
            ∀ i ∈ (∅ : Finset κ), ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
            Set (CoordFamily (M := M) (F := BilF) Kc)) = Set.univ := by
          ext u
          simp
      rw [hUniv]
      exact isOpen_univ
    · intro a s _ hs
      have haOpen :
          IsOpen ({u : CoordFamily (M := M) (F := BilF) Kc |
            ∀ x : Kc a, ∀ v : F, v ≠ 0 → 0 < u a x v v} :
              Set (CoordFamily (M := M) (F := BilF) Kc)) := hA a
      have hsOpen :
          IsOpen ({u : CoordFamily (M := M) (F := BilF) Kc |
            ∀ i ∈ s, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
              Set (CoordFamily (M := M) (F := BilF) Kc)) := hs
      have hInsert :
          ({u : CoordFamily (M := M) (F := BilF) Kc |
              ∀ i ∈ insert a s, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
              Set (CoordFamily (M := M) (F := BilF) Kc)) =
            ({u : CoordFamily (M := M) (F := BilF) Kc |
                ∀ x : Kc a, ∀ v : F, v ≠ 0 → 0 < u a x v v} :
                Set (CoordFamily (M := M) (F := BilF) Kc)) ∩
            ({u : CoordFamily (M := M) (F := BilF) Kc |
                ∀ i ∈ s, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
                Set (CoordFamily (M := M) (F := BilF) Kc)) := by
          ext u
          simp
      rw [hInsert]
      exact haOpen.inter hsOpen
  have huniv : IsOpen ({u : CoordFamily (M := M) (F := BilF) Kc |
      ∀ i ∈ (Finset.univ : Finset κ), ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
        Set (CoordFamily (M := M) (F := BilF) Kc)) :=
    hfin (Finset.univ : Finset κ)
  have hAll :
      ({u : CoordFamily (M := M) (F := BilF) Kc |
          ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
          Set (CoordFamily (M := M) (F := BilF) Kc)) =
        ({u : CoordFamily (M := M) (F := BilF) Kc |
            ∀ i ∈ (Finset.univ : Finset κ), ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
            Set (CoordFamily (M := M) (F := BilF) Kc)) := by
    ext u
    simp
  rw [hAll]
  exact huniv

/-- Coordinate families of bilinear forms that are pointwise symmetric on every compact piece form a
closed subset of the ambient finite product of compact `ContinuousMap` spaces. -/
lemma isClosed_setOf_coordFamily_forall_symmetric
    {κ : Type*} [Finite κ] (Kc : κ → TopologicalSpace.Compacts M) :
    IsClosed ({u : CoordFamily (M := M) (F := BilF) Kc |
      ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
        Set (CoordFamily (M := M) (F := BilF) Kc)) := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  have hA : ∀ i : κ,
      IsClosed ({u : CoordFamily (M := M) (F := BilF) Kc |
        ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
          Set (CoordFamily (M := M) (F := BilF) Kc)) := by
    intro i
    let L : C(Kc i, BilF) →L[ℝ] C(Kc i, BilF) :=
      _root_.ContinuousLinearMap.compLeftContinuous (R := ℝ) (α := Kc i)
        (_root_.Bundle.ContinuousLinearMap.symmetryDefect (E := F))
    let S : Set (C(Kc i, BilF)) := {g | ∀ x : Kc i, ∀ v w : F, g x v w = g x w v}
    have hEqS : S = (L.ker : Set (C(Kc i, BilF))) := by
      ext g
      constructor
      · intro hg
        change L g = 0
        ext x v w
        exact sub_eq_zero.mpr (by simpa [L] using hg x v w)
      · intro hg
        have hg0 : L g = 0 := hg
        intro x v w
        have hx : _root_.Bundle.ContinuousLinearMap.symmetryDefect (E := F) (g x) = 0 := by
          have h' := congrArg (fun h : C(Kc i, BilF) => h x) hg0
          change _root_.Bundle.ContinuousLinearMap.symmetryDefect (E := F) (g x) = 0 at h'
          exact h'
        exact (_root_.Bundle.ContinuousLinearMap.symmetryDefect_eq_zero_iff (E := F) (g x)).1 hx v w
    have hclosedS : IsClosed S := by
      rw [hEqS]
      exact ContinuousLinearMap.isClosed_ker L
    have hπi : Continuous (fun u : CoordFamily (M := M) (F := BilF) Kc => u i) := by
      simpa using
        (continuous_apply i :
          Continuous fun u : CoordFamily (M := M) (F := BilF) Kc => u i)
    have hpre : IsClosed ((fun u : CoordFamily (M := M) (F := BilF) Kc => u i) ⁻¹' S) :=
      hclosedS.preimage hπi
    change IsClosed ((fun u : CoordFamily (M := M) (F := BilF) Kc => u i) ⁻¹' S)
    exact hpre
  have hfin : ∀ s : Finset κ,
      IsClosed ({u : CoordFamily (M := M) (F := BilF) Kc |
        ∀ i ∈ s, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
          Set (CoordFamily (M := M) (F := BilF) Kc)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have hUniv :
          ({u : CoordFamily (M := M) (F := BilF) Kc |
              ∀ i ∈ (∅ : Finset κ), ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
              Set (CoordFamily (M := M) (F := BilF) Kc)) = Set.univ := by
        ext u
        simp
      rw [hUniv]
      exact isClosed_univ
    · intro a s _ hs
      have haClosed :
          IsClosed ({u : CoordFamily (M := M) (F := BilF) Kc |
            ∀ x : Kc a, ∀ v w : F, u a x v w = u a x w v} :
              Set (CoordFamily (M := M) (F := BilF) Kc)) := hA a
      have hsClosed :
          IsClosed ({u : CoordFamily (M := M) (F := BilF) Kc |
            ∀ i ∈ s, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
              Set (CoordFamily (M := M) (F := BilF) Kc)) := hs
      have hInsert :
          ({u : CoordFamily (M := M) (F := BilF) Kc |
              ∀ i ∈ insert a s, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
              Set (CoordFamily (M := M) (F := BilF) Kc)) =
            ({u : CoordFamily (M := M) (F := BilF) Kc |
                ∀ x : Kc a, ∀ v w : F, u a x v w = u a x w v} :
                Set (CoordFamily (M := M) (F := BilF) Kc)) ∩
            ({u : CoordFamily (M := M) (F := BilF) Kc |
                ∀ i ∈ s, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
                Set (CoordFamily (M := M) (F := BilF) Kc)) := by
        ext u
        simp
      rw [hInsert]
      exact haClosed.inter hsClosed
  have huniv : IsClosed ({u : CoordFamily (M := M) (F := BilF) Kc |
      ∀ i ∈ (Finset.univ : Finset κ), ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
        Set (CoordFamily (M := M) (F := BilF) Kc)) :=
    hfin (Finset.univ : Finset κ)
  have hAll :
      ({u : CoordFamily (M := M) (F := BilF) Kc |
          ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
          Set (CoordFamily (M := M) (F := BilF) Kc)) =
        ({u : CoordFamily (M := M) (F := BilF) Kc |
            ∀ i ∈ (Finset.univ : Finset κ), ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
            Set (CoordFamily (M := M) (F := BilF) Kc)) := by
    ext u
    simp
  rw [hAll]
  exact huniv

/-- Coordinate families whose bilinear forms are pointwise symmetric on every compact piece form a
convex subset of the ambient finite product. -/
lemma convex_setOf_coordFamily_forall_symmetric
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M) :
    Convex ℝ ({u : CoordFamily (M := M) (F := BilF) Kc |
      ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
        Set (CoordFamily (M := M) (F := BilF) Kc)) := by
  letI : Module ℝ (CoordFamily (M := M) (F := BilF) Kc) := inferInstance
  rw [convex_iff_forall_pos]
  intro u hu v hv a b _ _ _ i x p q
  simp [hu i x p q, hv i x p q]

/-- Coordinate families whose bilinear forms are pointwise positive-definite on every compact piece
form a convex subset of the ambient finite product. -/
lemma convex_setOf_coordFamily_forall_pos
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M) :
    Convex ℝ ({u : CoordFamily (M := M) (F := BilF) Kc |
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
        Set (CoordFamily (M := M) (F := BilF) Kc)) := by
  letI : Module ℝ (CoordFamily (M := M) (F := BilF) Kc) := inferInstance
  rw [convex_iff_forall_pos]
  intro u hu v hv a b ha hb hab i x p hp
  have hleft : 0 < a * u i x p p := mul_pos ha (hu i x p hp)
  have hright : 0 ≤ b * v i x p p := mul_nonneg hb.le (le_of_lt (hv i x p hp))
  simpa [smul_eq_mul] using add_pos_of_pos_of_nonneg hleft hright

/-- Coordinate families that are pointwise symmetric and positive-definite on every compact piece
form a convex subset of the ambient finite product. -/
lemma convex_setOf_coordFamily_forall_symmetric_and_pos
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M) :
    Convex ℝ ({u : CoordFamily (M := M) (F := BilF) Kc |
      (∀ i : κ, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v) ∧
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
        Set (CoordFamily (M := M) (F := BilF) Kc)) := by
  rw [show ({u : CoordFamily (M := M) (F := BilF) Kc |
      (∀ i : κ, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v) ∧
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
      Set (CoordFamily (M := M) (F := BilF) Kc)) =
      {u : CoordFamily (M := M) (F := BilF) Kc |
        ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} ∩
      {u : CoordFamily (M := M) (F := BilF) Kc |
        ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} by rfl]
  exact (convex_setOf_coordFamily_forall_symmetric (M := M) (F := F) Kc).inter
    (convex_setOf_coordFamily_forall_pos (M := M) (F := F) Kc)

variable {V : M → Type*}
  [TopologicalSpace (_root_.Bundle.TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) V)] [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle (F →L[ℝ] F →L[ℝ] ℝ) V] [VectorBundle ℝ (F →L[ℝ] F →L[ℝ] ℝ) V]

/-- The pointwise positive-definite locus is open inside the closed compatibility kernel for compact
coordinate families of bilinear-form sections. -/
lemma isOpen_setOf_compatibleCoordFamilySubmodule_forall_pos
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsOpen {u : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo |
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u.1 i x v v} := by
  let S : Set (CoordFamily (M := M) (F := BilF) Kc) := {u |
    ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v}
  have hS : IsOpen S := isOpen_setOf_coordFamily_forall_pos (M := M) (F := F) Kc
  change IsOpen (Subtype.val ⁻¹' S)
  exact hS.preimage continuous_subtype_val

/-- The pointwise symmetric locus is closed inside the compatibility kernel for compact coordinate
families of bilinear-form sections. -/
lemma isClosed_setOf_compatibleCoordFamilySubmodule_forall_symmetric
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    IsClosed {u : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo |
      ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u.1 i x v w = u.1 i x w v} := by
  let S : Set (CoordFamily (M := M) (F := BilF) Kc) := {u |
    ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v}
  have hS : IsClosed S := isClosed_setOf_coordFamily_forall_symmetric (M := M) (F := F) Kc
  change IsClosed (Subtype.val ⁻¹' S)
  exact hS.preimage continuous_subtype_val

/-- Inside the compatibility kernel, coordinatewise symmetric bilinear-form families form a convex
subset. -/
lemma convex_setOf_compatibleCoordFamilySubmodule_forall_symmetric
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    Convex ℝ {u : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo |
      ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u.1 i x v w = u.1 i x w v} := by
  rw [convex_iff_forall_pos]
  intro u hu v hv a b _ _ _ i x p q
  simp [hu i x p q, hv i x p q]

/-- Inside the compatibility kernel, coordinatewise positive-definite bilinear-form families form a
convex subset. -/
lemma convex_setOf_compatibleCoordFamilySubmodule_forall_pos
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    Convex ℝ {u : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo |
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u.1 i x v v} := by
  rw [convex_iff_forall_pos]
  intro u hu v hv a b ha hb hab i x p hp
  have hleft : 0 < a * u.1 i x p p := mul_pos ha (hu i x p hp)
  have hright : 0 ≤ b * v.1 i x p p := mul_nonneg hb.le (le_of_lt (hv i x p hp))
  simpa [smul_eq_mul] using add_pos_of_pos_of_nonneg hleft hright

/-- Inside the compatibility kernel, coordinatewise symmetric positive-definite bilinear-form
families form a convex subset. -/
lemma convex_setOf_compatibleCoordFamilySubmodule_forall_symmetric_and_pos
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    Convex ℝ {u : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo |
      (∀ i : κ, ∀ x : Kc i, ∀ v w : F, u.1 i x v w = u.1 i x w v) ∧
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u.1 i x v v} := by
  rw [show ({u : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo |
      (∀ i : κ, ∀ x : Kc i, ∀ v w : F, u.1 i x v w = u.1 i x w v) ∧
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u.1 i x v v}) =
      {u : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo |
        ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u.1 i x v w = u.1 i x w v} ∩
      {u : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo |
        ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u.1 i x v v} by rfl]
  exact (convex_setOf_compatibleCoordFamilySubmodule_forall_symmetric
      (M := M) (F := F) (V := V) et Kc hKc Ko hKo).inter
    (convex_setOf_compatibleCoordFamilySubmodule_forall_pos
      (M := M) (F := F) (V := V) et Kc hKc Ko hKo)

namespace ContinuousSectionSpace

/-- After transporting the finite-cover compatibility kernel to the bundled continuous-section
wrapper, the coordinatewise pointwise positive-definite locus remains open. -/
lemma isOpen_setOf_coordwise_forall_pos
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsOpen {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := V)
        et Kc hKc Ko hKo hKoEq hcover |
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 →
        0 <
          ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
            et Kc hKc Ko hKo hKoEq hcover s).1 i x v v)} := by
  letI : Fintype κ := Fintype.ofFinite κ
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
    et Kc hKc Ko hKo hKoEq hcover
  let S :
      Set (compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo) := {u |
        ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u.1 i x v v}
  have hS : IsOpen S :=
    isOpen_setOf_compatibleCoordFamilySubmodule_forall_pos
      (M := M) (F := F) (V := V) et Kc hKc Ko hKo
  have hIso : Isometry e := by
    intro x y
    rfl
  change IsOpen (e ⁻¹' S)
  exact hS.preimage hIso.continuous

/-- After transporting the finite-cover compatibility kernel to the bundled continuous-section
wrapper, the coordinatewise pointwise symmetric locus remains closed. -/
lemma isClosed_setOf_coordwise_forall_symmetric
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    IsClosed {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := V)
        et Kc hKc Ko hKo hKoEq hcover |
      ∀ i : κ, ∀ x : Kc i, ∀ v w : F,
        ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
            et Kc hKc Ko hKo hKoEq hcover s).1 i x v w) =
          ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
            et Kc hKc Ko hKo hKoEq hcover s).1 i x w v)} := by
  letI : Fintype κ := Fintype.ofFinite κ
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
    et Kc hKc Ko hKo hKoEq hcover
  let S :
      Set (compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo) := {u |
        ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u.1 i x v w = u.1 i x w v}
  have hS : IsClosed S :=
    isClosed_setOf_compatibleCoordFamilySubmodule_forall_symmetric
      (M := M) (F := F) (V := V) et Kc hKc Ko hKo
  have hIso : Isometry e := by
    intro x y
    rfl
  change IsClosed (e ⁻¹' S)
  exact hS.preimage hIso.continuous

/-- The transported continuous-linear coordinatewise antisymmetric-defect map on bundled
continuous sections. Its codomain is the ambient finite coordinate-family product, so it does not
require proving that the defect or slot-flip preserves the compatibility kernel. -/
noncomputable def coordwiseSymmetryDefectContinuousLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := V)
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ]
      CoordFamily (M := M) (F := BilF) Kc :=
  letI : Fintype κ := Fintype.ofFinite κ
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
    et Kc hKc Ko hKo hKoEq hcover
  let D : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo →L[ℝ]
      CoordFamily (M := M) (F := BilF) Kc :=
    (symmetryDefectCoordFamilyContinuousLinearMap (M := M) (F := F) Kc).comp
      (compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo).subtypeL
  { toFun := fun s ↦ D (e s)
    map_add' := by
      intro s t
      change D (e (s + t)) = D (e s) + D (e t)
      have he : e (s + t) = e s + e t := by
        apply e.symm.injective
        change e.symm (e (e.symm (e s + e t))) = e.symm (e s + e t)
        simp
      rw [he, map_add]
    map_smul' := by
      intro c s
      change D (e (c • s)) = c • D (e s)
      have he : e (c • s) = c • e s := by
        apply e.symm.injective
        change e.symm (e (e.symm (c • e s))) = e.symm (c • e s)
        simp
      rw [he, map_smul]
    cont := by
      have hIso : Isometry e := by
        intro s t
        rfl
      exact D.continuous.comp hIso.continuous }

section PreferredTrivializations

/-- On a finite compact cover by preferred bilinear-form trivializations, an actually
positive-definite bilinear-form section has positive-definite compact coordinate maps on every
covering piece. -/
lemma coordwise_forall_pos_of_forall_pos
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hpos : ∀ x : M, ∀ v : W x, v ≠ 0 → 0 < s x v v) :
    ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 →
      0 <
        coordContinuousMap
          (e := et i)
          (Kc i) (hKc i) s.continuous_toFun.continuousOn x v v := by
  intro i x v hv
  have hKpref :
      (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet := by
    simpa [het i] using hKc i
  simpa [het i] using
    coordContinuousMap_forall_pos_of_forall_pos
      (x0 := x0 i) (K := Kc i) (hK := hKpref)
      (s := fun y ↦ s y) s.continuous_toFun hpos x v hv

/-- Conversely, if all compact preferred-coordinate maps of a bilinear-form section are
positive-definite, then the section itself is pointwise positive-definite. -/
lemma forall_pos_of_coordwise_forall_pos
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hcoord : ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 →
      0 <
        coordContinuousMap
          (e := et i)
          (Kc i) (hKc i) s.continuous_toFun.continuousOn x v v) :
    ∀ x : M, ∀ v : W x, v ≠ 0 → 0 < s x v v := by
  intro x v hv
  have hxcover : x ∈ ⋃ i, (Kc i : Set M) := by
    simpa [hcover]
  rcases Set.mem_iUnion.mp hxcover with ⟨i, hxi⟩
  let xK : Kc i := ⟨x, hxi⟩
  have hKpref :
      (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet := by
    simpa [het i] using hKc i
  have hxbase : x ∈ (trivializationAt F W (x0 i)).baseSet := by
    simpa using hKpref hxi
  let e := (trivializationAt F W (x0 i)).continuousLinearEquivAt ℝ x hxbase
  have hu : e v ≠ 0 := by
    intro h
    apply hv
    apply e.injective
    simpa using h
  have hcoord' : 0 <
      coordContinuousMap
        (e := trivializationAt BilF BilW (x0 i))
        (Kc i) hKpref s.continuous_toFun.continuousOn xK (e v) (e v) := by
    simpa [het i] using hcoord i xK (e v) hu
  have hEq :
      coordContinuousMap
          (e := trivializationAt BilF BilW (x0 i))
          (Kc i) hKpref s.continuous_toFun.continuousOn xK (e v) (e v) = s x v v := by
    rw [coordContinuousMap_apply]
    erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_apply_eq
      (x0 := x0 i) (x := x) hxbase (s x) (e v)]
    have hvEq :
        e.symm (e v) = v := by
      simpa using e.symm_apply_apply v
    rw [hvEq]
  exact hEq ▸ hcoord'

/-- On a finite compact cover by preferred bilinear-form trivializations, an actually symmetric
bilinear-form section has symmetric compact coordinate maps on every covering piece. -/
lemma coordwise_forall_symmetric_of_forall_symmetric
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hsymm : ∀ x : M, ∀ v w : W x, s x v w = s x w v) :
    ∀ i : κ, ∀ x : Kc i, ∀ v w : F,
      coordContinuousMap
          (e := et i)
          (Kc i) (hKc i) s.continuous_toFun.continuousOn x v w =
        coordContinuousMap
          (e := et i)
          (Kc i) (hKc i) s.continuous_toFun.continuousOn x w v := by
  intro i x v w
  have hKpref :
      (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet := by
    simpa [het i] using hKc i
  have hpref :
      coordContinuousMap
          (e := trivializationAt BilF BilW (x0 i))
          (Kc i) hKpref s.continuous_toFun.continuousOn x v w =
        coordContinuousMap
          (e := trivializationAt BilF BilW (x0 i))
          (Kc i) hKpref s.continuous_toFun.continuousOn x w v := by
    have hxbase : x.1 ∈ (trivializationAt F W (x0 i)).baseSet := by
      simpa using hKpref x.2
    erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
      (x0 := x0 i) (x := x.1) hxbase (s x.1) v w]
    erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
      (x0 := x0 i) (x := x.1) hxbase (s x.1) w v]
    exact hsymm x.1 _ _
  simpa [het i] using hpref

/-- Conversely, if all compact preferred-coordinate maps of a bilinear-form section are symmetric,
then the section itself is pointwise symmetric. -/
lemma forall_symmetric_of_coordwise_forall_symmetric
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hcoord : ∀ i : κ, ∀ x : Kc i, ∀ v w : F,
      coordContinuousMap
          (e := et i)
          (Kc i) (hKc i) s.continuous_toFun.continuousOn x v w =
        coordContinuousMap
          (e := et i)
          (Kc i) (hKc i) s.continuous_toFun.continuousOn x w v) :
    ∀ x : M, ∀ v w : W x, s x v w = s x w v := by
  intro x v w
  have hxcover : x ∈ ⋃ i, (Kc i : Set M) := by
    simpa [hcover]
  rcases Set.mem_iUnion.mp hxcover with ⟨i, hxi⟩
  let xK : Kc i := ⟨x, hxi⟩
  have hKpref :
      (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet := by
    simpa [het i] using hKc i
  have hxbase : x ∈ (trivializationAt F W (x0 i)).baseSet := by
    simpa using hKpref hxi
  let e := (trivializationAt F W (x0 i)).continuousLinearEquivAt ℝ x hxbase
  have hcoord' :
      coordContinuousMap
          (e := trivializationAt BilF BilW (x0 i))
          (Kc i) hKpref s.continuous_toFun.continuousOn xK (e v) (e w) =
        coordContinuousMap
          (e := trivializationAt BilF BilW (x0 i))
          (Kc i) hKpref s.continuous_toFun.continuousOn xK (e w) (e v) := by
    simpa [het i] using hcoord i xK (e v) (e w)
  have hEqLeft :
      coordContinuousMap
          (e := trivializationAt BilF BilW (x0 i))
          (Kc i) hKpref s.continuous_toFun.continuousOn xK (e v) (e w) =
        s x v w := by
    rw [coordContinuousMap_apply]
    erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
      (x0 := x0 i) (x := x) hxbase (s x) (e v) (e w)]
    change s x (e.symm (e v)) (e.symm (e w)) = s x v w
    simpa using congrArg₂ (fun a b => s x a b) (e.symm_apply_apply v) (e.symm_apply_apply w)
  have hEqRight :
      coordContinuousMap
          (e := trivializationAt BilF BilW (x0 i))
          (Kc i) hKpref s.continuous_toFun.continuousOn xK (e w) (e v) =
        s x w v := by
    rw [coordContinuousMap_apply]
    erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
      (x0 := x0 i) (x := x) hxbase (s x) (e w) (e v)]
    change s x (e.symm (e w)) (e.symm (e v)) = s x w v
    simpa using congrArg₂ (fun a b => s x a b) (e.symm_apply_apply w) (e.symm_apply_apply v)
  calc
    s x v w =
        coordContinuousMap
            (e := trivializationAt BilF BilW (x0 i))
            (Kc i) hKpref s.continuous_toFun.continuousOn xK (e v) (e w) := hEqLeft.symm
    _ =
        coordContinuousMap
            (e := trivializationAt BilF BilW (x0 i))
            (Kc i) hKpref s.continuous_toFun.continuousOn xK (e w) (e v) := hcoord'
    _ = s x w v := hEqRight

/-- The actual pointwise positive-definite locus inside a bundled continuous-section space of
bilinear forms. -/
def positiveDefiniteLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :=
  {s | ∀ x : M, ∀ v : W x, v ≠ 0 → 0 < s x v v}

/-- The pointwise symmetric locus inside a bundled continuous-section space of bilinear forms. -/
def symmetricLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :=
  {s | ∀ x : M, ∀ v w : W x, s x v w = s x w v}

/-- On preferred finite-cover coordinates, the transported coordinatewise antisymmetric-defect map
cuts out exactly the actual pointwise symmetric locus of bundled bilinear-form sections. -/
lemma coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :
    coordwiseSymmetryDefectContinuousLinearMap (F := F) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover s = 0 ↔
      s ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover := by
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
    et Kc hKc Ko hKo hKoEq hcover
  change
    symmetryDefectCoordFamilyContinuousLinearMap (M := M) (F := F) Kc (e s).1 = 0 ↔
      s ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover
  constructor
  · intro h
    have hcoord :=
      (symmetryDefectCoordFamilyContinuousLinearMap_eq_zero_iff (M := M) (F := F)
        Kc (e s).1).1 h
    exact forall_symmetric_of_coordwise_forall_symmetric
      (M := M) (F := F) (W := W)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) s (by
        intro i x v w
        have h' := hcoord i x v w
        change
          (et i ((T% s) x.1)).2 v w = (et i ((T% s) x.1)).2 w v at h'
        exact h')
  · intro hs
    have hcoord := coordwise_forall_symmetric_of_forall_symmetric
      (M := M) (F := F) (W := W)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) s hs
    exact
      (symmetryDefectCoordFamilyContinuousLinearMap_eq_zero_iff (M := M) (F := F)
        Kc (e s).1).2 (by
          intro i x v w
          have h' := hcoord i x v w
          change
            (et i ((T% s) x.1)).2 v w = (et i ((T% s) x.1)).2 w v at h'
          change
            (et i ((T% s) x.1)).2 v w = (et i ((T% s) x.1)).2 w v
          exact h')

/-- The symmetric positive-definite locus inside the bundled continuous-section space of bilinear
forms. This is the most faithful finite-cover section-space model of continuous metric data
currently available in the repo. -/
def symmetricPositiveDefiniteLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :=
  symmetricLocus (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover ∩
    positiveDefiniteLocus (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover

lemma mem_symmetricLocus_of_continuousRiemannianMetric
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : _root_.Bundle.ContinuousRiemannianMetric F W) :
    (⟨g.toSection, g.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover) ∈
      symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover := by
  intro x v w
  simpa [_root_.Bundle.ContinuousRiemannianMetric.toSection] using g.symm x v w

lemma mem_positiveDefiniteLocus_of_continuousRiemannianMetric
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : _root_.Bundle.ContinuousRiemannianMetric F W) :
    (⟨g.toSection, g.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover) ∈
      positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover := by
  intro x v hv
  simpa [_root_.Bundle.ContinuousRiemannianMetric.toSection] using g.pos x v hv

lemma mem_symmetricPositiveDefiniteLocus_of_continuousRiemannianMetric
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : _root_.Bundle.ContinuousRiemannianMetric F W) :
    (⟨g.toSection, g.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover) ∈
      symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover := by
  exact ⟨mem_symmetricLocus_of_continuousRiemannianMetric
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g,
    mem_positiveDefiniteLocus_of_continuousRiemannianMetric
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g⟩

/-- Reify a continuous bilinear-form section in the symmetric positive-definite finite-cover locus
as a bundled continuous Riemannian metric. -/
def _root_.Bundle.ContinuousRiemannianMetric.ofContinuousSectionSpace
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hs : s ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) :
    _root_.Bundle.ContinuousRiemannianMetric F W where
  inner := s
  symm := hs.1
  pos := hs.2
  isVonNBounded x := by
    let e : W x ≃L[ℝ] F :=
      _root_.Bundle.Trivialization.continuousLinearEquivAt ℝ
        (trivializationAt F W x) _ (FiberBundle.mem_baseSet_trivializationAt' x)
    exact
      _root_.Bundle.ContinuousLinearMap.isVonNBounded_sublevel_one_of_pos_of_continuousLinearEquiv
        (E := F) e (s x) (hs.2 x)
  continuous := s.continuous_toFun

@[simp] theorem _root_.Bundle.ContinuousRiemannianMetric.ofContinuousSectionSpace_inner
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hs : s ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (_root_.Bundle.ContinuousRiemannianMetric.ofContinuousSectionSpace
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover s hs).inner x = s x := rfl

/-- Reify a `C^n` bilinear-form section in the symmetric positive-definite finite-cover locus as a
bundled `C^n` Riemannian metric. This is the smooth analogue of
`ContinuousRiemannianMetric.ofContinuousSectionSpace` and is the section-space bridge needed to turn
spatially smooth Banach metric-section curves into actual smooth Riemannian metrics. -/
def _root_.Bundle.ContMDiffRiemannianMetric.ofContinuousSectionSpace
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    {H₀ : Type*} [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
    {n : WithTop ℕ∞} [ChartedSpace H₀ M]
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    [∀ x : M, IsTopologicalAddGroup (W x)] [∀ x : M, ContinuousConstSMul ℝ (W x)]
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hs : s ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hsmooth : ContMDiff I₀ (I₀.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (s x))) :
    _root_.Bundle.ContMDiffRiemannianMetric I₀ n F W where
  inner := s
  symm := hs.1
  pos := hs.2
  isVonNBounded x := by
    let e : W x ≃L[ℝ] F :=
      _root_.Bundle.Trivialization.continuousLinearEquivAt ℝ
        (trivializationAt F W x) _ (FiberBundle.mem_baseSet_trivializationAt' x)
    exact
      _root_.Bundle.ContinuousLinearMap.isVonNBounded_sublevel_one_of_pos_of_continuousLinearEquiv
        (E := F) e (s x) (hs.2 x)
  contMDiff := hsmooth

@[simp] theorem _root_.Bundle.ContMDiffRiemannianMetric.ofContinuousSectionSpace_inner
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    {H₀ : Type*} [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
    {n : WithTop ℕ∞} [ChartedSpace H₀ M]
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    [∀ x : M, IsTopologicalAddGroup (W x)] [∀ x : M, ContinuousConstSMul ℝ (W x)]
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hs : s ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hsmooth : ContMDiff I₀ (I₀.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (s x)))
    (x : M) :
    (_root_.Bundle.ContMDiffRiemannianMetric.ofContinuousSectionSpace
      (M := M) (F := F) (W := W) (I₀ := I₀) et Kc hKc Ko hKo hKoEq hcover
      s hs hsmooth).inner x = s x := rfl

/-- Read one scalar component of a bilinear-form coordinate chart as a continuous linear map on the
bundled finite-cover continuous-section space. -/
noncomputable def coordBilinearFormReadoutContinuousLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (i : κ) (x : Kc i) (u v : F) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ] ℝ :=
  ((ContinuousLinearMap.apply ℝ ℝ v).comp
    (ContinuousLinearMap.apply ℝ (F →L[ℝ] ℝ) u)).comp
      (coordReadoutContinuousLinearMap
        (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover i x)

@[simp]
lemma coordBilinearFormReadoutContinuousLinearMap_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (i : κ) (x : Kc i) (u v : F)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :
    coordBilinearFormReadoutContinuousLinearMap
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover i x u v s =
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover s).1 i x u v := by
  simp [coordBilinearFormReadoutContinuousLinearMap]

/-- Read one actual fibrewise bilinear-form value from a preferred compact coordinate chart as a
continuous linear map on the finite-cover continuous-section space. -/
noncomputable def pointBilinearFormReadoutContinuousLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (i : κ) (x : Kc i) (u v : W x.1) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ] ℝ :=
  coordBilinearFormReadoutContinuousLinearMap
    (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover i x
      ((trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1 u)
      ((trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1 v)

@[simp]
lemma pointBilinearFormReadoutContinuousLinearMap_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (i : κ) (x : Kc i) (u v : W x.1)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :
    pointBilinearFormReadoutContinuousLinearMap
        (M := M) (F := F) (W := W) x0 et Kc hKc Ko hKo hKoEq hcover i x u v s =
      s x.1 u v := by
  have hKpref :
      (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet := by
    simpa [het i] using hKc i
  have hxbase : x.1 ∈ (trivializationAt F W (x0 i)).baseSet := by
    simpa using hKpref x.2
  let e := (trivializationAt F W (x0 i)).continuousLinearEquivAt ℝ x.1 hxbase
  have hEq :
      coordBilinearFormReadoutContinuousLinearMap
          (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
          i x (e u) (e v) s =
        s x.1 u v := by
    rw [coordBilinearFormReadoutContinuousLinearMap_apply]
    change (et i ⟨x.1, s x.1⟩).2 (e u) (e v) = s x.1 u v
    rw [het i]
    erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
      (x0 := x0 i) (x := x.1) hxbase (s x.1) (e u) (e v)]
    rw [show e.symm (e u) = u from e.symm_apply_apply u,
      show e.symm (e v) = v from e.symm_apply_apply v]
  change
    coordBilinearFormReadoutContinuousLinearMap
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover i x
        ((trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1 u)
        ((trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1 v) s =
      s x.1 u v
  have huCoord :
      (trivializationAt F W (x0 i)).linearMapAt ℝ x.1 u = e u := by
    rw [Bundle.Trivialization.linearMapAt_apply, if_pos hxbase]
    rfl
  have hvCoord :
      (trivializationAt F W (x0 i)).linearMapAt ℝ x.1 v = e v := by
    rw [Bundle.Trivialization.linearMapAt_apply, if_pos hxbase]
    rfl
  have huCoord' :
      (trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1 u = e u := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply]
    exact huCoord
  have hvCoord' :
      (trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1 v = e v := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply]
    exact hvCoord
  rw [huCoord', hvCoord']
  exact hEq

/-- Two bilinear-form section states are equal when all scalar finite-cover bilinear coordinate
readouts agree. -/
theorem eq_of_coordBilinearFormReadout_eq
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s t : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover}
    (hcoord : ∀ i (x : Kc i) (u v : F),
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover s).1 i x u v =
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover t).1 i x u v) :
    s = t := by
  apply eq_of_coordReadout_eq
  intro i x
  ext u v
  exact hcoord i x u v

/-- The finite-cover coordinate family of the fiberwise symmetrized section is the coordinatewise
symmetrization of the original finite-cover coordinate family. -/
lemma equivCompatibleCoordFamilySubmodule_symmetrizeBilinearSection
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s v : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hv : ∀ x (p q : W x), v x p q = (s x p q + s x q p) / 2) :
    (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover v).1 =
      symmetrizeBilinearCoordFamilyContinuousLinearMap (M := M) (F := F) Kc
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover s).1 := by
  ext i x u w
  have hKpref : (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet := by
    simpa [het i] using hKc i
  have hxbase : x.1 ∈ (trivializationAt F W (x0 i)).baseSet := by
    simpa using hKpref x.2
  have hxBil : x.1 ∈ (trivializationAt BilF BilW (x0 i)).baseSet := hKpref x.2
  change (et i ((T% v) x.1)).2 u w = _
  rw [symmetrizeBilinearCoordFamilyContinuousLinearMap_apply_apply]
  change
    (et i ((T% v) x.1)).2 u w =
      ((et i ((T% s) x.1)).2 u w + (et i ((T% s) x.1)).2 w u) / 2
  rw [het i]
  rw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
    (F := F) (W := W) (x0 i) x.1 hxbase (v x.1) u w]
  rw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
    (F := F) (W := W) (x0 i) x.1 hxbase (s x.1) u w]
  rw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
    (F := F) (W := W) (x0 i) x.1 hxbase (s x.1) w u]
  exact hv x.1 _ _

/-- Fiberwise symmetrizing an approximant does not increase its finite-cover section-space distance
to an already symmetric section. -/
lemma dist_symmetrizeBilinearSection_le_of_symmetric
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s u v : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hs : s ∈ symmetricLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (hv : ∀ x (p q : W x), v x p q = (u x p q + u x q p) / 2) :
    dist s v ≤ dist s u := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  let e := equivCompatibleCoordFamilySubmodule
    (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
  have hvcoord :
      (e v).1 = symmetrizeBilinearCoordFamilyContinuousLinearMap (M := M) (F := F) Kc
        (e u).1 :=
    equivCompatibleCoordFamilySubmodule_symmetrizeBilinearSection
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover u v hv
  have hscoord : ∀ i : κ, ∀ x : Kc i, ∀ p q : F, (e s).1 i x p q = (e s).1 i x q p := by
    have hcoord := coordwise_forall_symmetric_of_forall_symmetric
      (M := M) (F := F) (W := W) (x0 := x0) (et := et) (het := het)
      (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
      (hKoEq := hKoEq) (hcover := hcover) s hs
    intro i x p q
    change
      (et i ((T% s) x.1)).2 p q = (et i ((T% s) x.1)).2 q p
    have hcoord' := hcoord i x p q
    change
      (et i ((T% s) x.1)).2 p q = (et i ((T% s) x.1)).2 q p at hcoord'
    exact hcoord'
  calc
    dist s v = dist (e s) (e v) := rfl
    _ = dist (e s).1 (e v).1 := rfl
    _ = dist (e v).1 (e s).1 := by rw [dist_comm]
    _ = dist (symmetrizeBilinearCoordFamilyContinuousLinearMap (M := M) (F := F) Kc (e u).1)
        (e s).1 := by rw [hvcoord]
    _ ≤ dist (e u).1 (e s).1 :=
      dist_symmetrizeBilinearCoordFamilyContinuousLinearMap_le_of_forall_symmetric
        (M := M) (F := F) Kc hscoord
    _ = dist (e u) (e s) := rfl
    _ = dist u s := rfl
    _ = dist s u := by rw [dist_comm]

/-- A continuous Riemannian metric determines a point of the closed symmetric section space. -/
def _root_.Bundle.ContinuousRiemannianMetric.toSymmetricSectionSpace
    {κ : Type*} [Finite κ] [T2Space M]
    (g : _root_.Bundle.ContinuousRiemannianMetric F W)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :=
  (⟨⟨g.toSection, g.continuous_toSection⟩,
      mem_symmetricLocus_of_continuousRiemannianMetric
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g⟩ :
    {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover //
      s ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover})

section
/-- For a finite compact cover by preferred bilinear-form trivializations, the actual
positive-definite locus of bundled bilinear-form sections is open in the transported
`ContinuousSectionSpace`. -/
lemma isOpen_setOf_forall_pos
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsOpen (positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) := by
  let S : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := {s |
        ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 →
          0 <
            ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
                et Kc hKc Ko hKo hKoEq hcover s).1 i x v v)}
  have hS : IsOpen S :=
    isOpen_setOf_coordwise_forall_pos
      (M := M) (F := F) (V := BilW)
      (et := et)
      Kc hKc Ko hKo hKoEq hcover
  have hEq :
      positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover = S := by
    ext s
    constructor
    · intro hs
      intro i x v hv
      have hs' := coordwise_forall_pos_of_forall_pos
        (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
        (hKoEq := hKoEq) (hcover := hcover) s hs i x v hv
      change 0 <
        ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
            et Kc hKc Ko hKo hKoEq hcover s).1 i x v v)
      change 0 < (et i ((T% s) x.1)).2 v v
      change 0 < (et i ((T% s) x.1)).2 v v at hs'
      exact hs'
    · intro hs
      exact forall_pos_of_coordwise_forall_pos
        (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
        (hKoEq := hKoEq) (hcover := hcover) s (by
          intro i x v hv
          have hs' := hs i x v hv
          change 0 < (et i ((T% s) x.1)).2 v v
          change 0 < (et i ((T% s) x.1)).2 v v at hs'
          exact hs')
  rw [hEq]
  exact hS

/-- Membership in the positive-definite locus has a metric neighborhood inside the locus.  This is
the neighborhood form of `isOpen_setOf_forall_pos`, useful when smooth approximation produces a
nearby bilinear-form section and positivity must be retained by choosing the approximation radius
small enough. -/
lemma exists_dist_lt_subset_positiveDefiniteLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover}
    (hs : s ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover,
        dist u s < ε →
          u ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
            et Kc hKc Ko hKo hKoEq hcover := by
  obtain ⟨ε, hεpos, hεsub⟩ :=
    (Metric.isOpen_iff.mp
      (isOpen_setOf_forall_pos
        (M := M) (F := F) (W := W) x0 et het Kc hKc Ko hKo hKoEq hcover)) s hs
  refine ⟨ε, hεpos, ?_⟩
  intro u hu
  exact hεsub (by simpa [Metric.mem_ball] using hu)

/-- Membership in the positive-definite locus has a *closed* metric ball neighbourhood inside the
locus, with a positive `ℝ≥0` radius.  This is the closed-ball companion of
`exists_dist_lt_subset_positiveDefiniteLocus`, packaged in exactly the shape consumed by the
closed-ball Banach-solution bridge (`hsub : Metric.closedBall x₀ (a : ℝ) ⊆ locus`): from a section
lying in the open positive-definite locus one extracts a Picard radius `a > 0` whose whole closed
ball stays positive-definite.  Combined with the monotonicity of closed balls in the radius, this
lets a Ricci–DeTurck chart choose its Picard radius inside the positivity margin of the state. -/
lemma exists_pos_closedBall_subset_positiveDefiniteLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover}
    (hs : s ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) :
    ∃ a : NNReal, 0 < a ∧
      Metric.closedBall s (a : ℝ) ⊆
        positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  obtain ⟨ε, hεpos, hεsub⟩ :=
    (Metric.isOpen_iff.mp
      (isOpen_setOf_forall_pos
        (M := M) (F := F) (W := W) x0 et het Kc hKc Ko hKo hKoEq hcover)) s hs
  refine ⟨(ε / 2).toNNReal, Real.toNNReal_pos.mpr (by positivity), ?_⟩
  have hcoe : ((ε / 2).toNNReal : ℝ) = ε / 2 := Real.coe_toNNReal _ (by positivity)
  rw [hcoe]
  exact (Metric.closedBall_subset_ball (by linarith)).trans hεsub

/-- The section of a genuine continuous Riemannian metric has a positive Picard radius whose whole
closed ball stays inside the positive-definite locus — the geometric a-priori positivity
containment that discharges the closed-ball Banach-solution bridge's `hsub` hypothesis for the
initial metric of a Ricci–DeTurck initial value problem. -/
lemma _root_.Bundle.ContinuousRiemannianMetric.exists_pos_closedBall_toSection_subset_positiveDefiniteLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (g : _root_.Bundle.ContinuousRiemannianMetric F W)
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    ∃ a : NNReal, 0 < a ∧
      Metric.closedBall
        (⟨g.toSection, g.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover) (a : ℝ) ⊆
        positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover :=
  exists_pos_closedBall_subset_positiveDefiniteLocus
    (M := M) (F := F) (W := W) x0 et het Kc hKc Ko hKo hKoEq hcover
    (mem_positiveDefiniteLocus_of_continuousRiemannianMetric
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g)

/-- For a finite compact cover by preferred bilinear-form trivializations, the actual pointwise
symmetric locus of bundled bilinear-form sections is closed in the transported
`ContinuousSectionSpace`. -/
lemma isClosed_symmetricLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    IsClosed (symmetricLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) := by
  let S : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := {s |
        ∀ i : κ, ∀ x : Kc i, ∀ v w : F,
          ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
              et Kc hKc Ko hKo hKoEq hcover s).1 i x v w) =
            ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
              et Kc hKc Ko hKo hKoEq hcover s).1 i x w v)}
  have hS : IsClosed S :=
    isClosed_setOf_coordwise_forall_symmetric
      (M := M) (F := F) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
  have hEq :
      symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover = S := by
    ext s
    constructor
    · intro hs
      intro i x v w
      have hs' := coordwise_forall_symmetric_of_forall_symmetric
        (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
        (hKoEq := hKoEq) (hcover := hcover) s hs i x v w
      change (et i ((T% s) x.1)).2 v w = (et i ((T% s) x.1)).2 w v
      change (et i ((T% s) x.1)).2 v w = (et i ((T% s) x.1)).2 w v at hs'
      exact hs'
    · intro hs
      exact forall_symmetric_of_coordwise_forall_symmetric
        (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
        (hKoEq := hKoEq) (hcover := hcover) s (by
          intro i x v w
          have hs' := hs i x v w
          change (et i ((T% s) x.1)).2 v w = (et i ((T% s) x.1)).2 w v
          change (et i ((T% s) x.1)).2 v w = (et i ((T% s) x.1)).2 w v at hs'
          exact hs')
  rw [hEq]
  exact hS

/-- The pointwise symmetric bilinear-form sections, represented as the kernel of the transported
coordinatewise antisymmetric-defect map. Unlike the set-subtype
`SymmetricSectionSpace`, this is an actual closed submodule of the continuous-section Banach
space, so Picard-Lindelöf arguments can use it as their Banach carrier. -/
noncomputable def symmetricSectionSubmodule
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Submodule ℝ (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :=
  (coordwiseSymmetryDefectContinuousLinearMap (F := F) (V := BilW)
    et Kc hKc Ko hKo hKoEq hcover).ker

instance instNormedAddCommGroupSymmetricSectionSubmodule
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    NormedAddCommGroup (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :=
  Submodule.normedAddCommGroup
    (𝕜 := ℝ)
    (E := ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (s := symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)

instance instNormedSpaceSymmetricSectionSubmodule
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    NormedSpace ℝ (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) := by
  letI : NormedAddCommGroup
      (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :=
    instNormedAddCommGroupSymmetricSectionSubmodule
      et Kc hKc Ko hKo hKoEq hcover
  exact Submodule.normedSpace
    (𝕜 := ℝ) (R := ℝ)
    (E := ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (s := symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)

instance instCompleteSpaceSymmetricSectionSubmodule
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)] :
    CompleteSpace (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) := by
  change CompleteSpace
    ((coordwiseSymmetryDefectContinuousLinearMap (F := F) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover).ker)
  infer_instance

lemma mem_symmetricSectionSubmodule_iff
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :
    s ∈ symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover ↔
      s ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover := by
  simpa [symmetricSectionSubmodule, LinearMap.mem_ker] using
    coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
      (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover s

/-- Elements of the symmetric submodule coerce to genuinely pointwise symmetric sections. -/
lemma symmetricSectionSubmodule_coe_mem_symmetricLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) ∈
      symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover :=
  (mem_symmetricSectionSubmodule_iff
    x0 et het Kc hKc Ko hKo hKoEq hcover s.1).1 s.2

/-- A continuous Riemannian metric determines a point of the symmetric submodule Banach carrier. -/
def _root_.Bundle.ContinuousRiemannianMetric.toSymmetricSectionSubmodule
    {κ : Type*} [Finite κ] [T2Space M]
    (g : _root_.Bundle.ContinuousRiemannianMetric F W)
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover :=
  ⟨⟨g.toSection, g.continuous_toSection⟩, by
    rw [mem_symmetricSectionSubmodule_iff
      x0 et het Kc hKc Ko hKo hKoEq hcover]
    exact mem_symmetricLocus_of_continuousRiemannianMetric
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g⟩

/-- The bundled section space restricted to pointwise symmetric bilinear-form sections. This is the
closed symmetric locus of the ambient bilinear-form section space, viewed as a subtype. -/
abbrev SymmetricSectionSpace
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) : Type _ :=
  {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover //
    s ∈ symmetricLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover}

lemma instCompleteSpaceSymmetricSectionSpace
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)] :
    CompleteSpace (SymmetricSectionSpace (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) := by
  letI : IsClosed
      (symmetricLocus (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover) :=
    isClosed_symmetricLocus (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover
  infer_instance

/-- The finite-cover metric locus inside the closed symmetric section space. Since symmetry is
already built into the ambient subtype, only positivity needs to be imposed here. -/
def riemannianMetricLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Set (SymmetricSectionSpace (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) :=
  {s | s.1 ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
    et Kc hKc Ko hKo hKoEq hcover}

/-- The finite-cover metric locus inside the symmetric submodule. This is the Banach-carrier
version of `riemannianMetricLocus`: the ambient space is a closed submodule, so autonomous ODE
existence can be applied without leaving the pointwise symmetric bilinear-form sections. -/
def riemannianMetricLocusSubmodule
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Set (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :=
  {s | s.1 ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
    et Kc hKc Ko hKo hKoEq hcover}

/-- Membership in the submodule metric locus is equivalent to membership of the coerced section in
the ambient symmetric positive-definite locus. -/
lemma mem_riemannianMetricLocusSubmodule_iff
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
    s ∈ riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover ↔
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover) ∈
        symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover := by
  constructor
  · intro hpos
    exact ⟨symmetricSectionSubmodule_coe_mem_symmetricLocus
      (M := M) (F := F) (W := W) x0 et het Kc hKc Ko hKo hKoEq hcover s, hpos⟩
  · intro h
    exact h.2

/-- Inside the closed symmetric section space, the symmetric positive-definite locus is open. This
packages the usual heuristic that Riemannian metrics form an open subset of symmetric bilinear
forms in the transported finite-cover model. -/
lemma isOpen_symmetricPositiveDefiniteLocus_in_symmetricSectionSpace
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsOpen {s : SymmetricSectionSpace (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover |
      s.1 ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover} := by
  let T : Set (SymmetricSectionSpace (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) := {s |
        s.1 ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover}
  have hT : IsOpen T := by
    change IsOpen (Subtype.val ⁻¹' positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    exact (isOpen_setOf_forall_pos (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover).preimage continuous_subtype_val
  have hEq :
      {s : SymmetricSectionSpace (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover |
        s.1 ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover} = T := by
    ext s
    constructor
    · intro hs
      exact hs.2
    · intro hs
      exact ⟨s.2, hs⟩
  rw [hEq]
  exact hT

/-- The metric locus is open inside the closed symmetric section space. -/
lemma isOpen_riemannianMetricLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsOpen (riemannianMetricLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) := by
  change IsOpen (Subtype.val ⁻¹' positiveDefiniteLocus (M := M) (F := F) (W := W)
    et Kc hKc Ko hKo hKoEq hcover)
  exact (isOpen_setOf_forall_pos (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover).preimage continuous_subtype_val

/-- The metric locus is open inside the symmetric submodule Banach carrier. -/
lemma isOpen_riemannianMetricLocusSubmodule
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsOpen (riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) := by
  change IsOpen (Subtype.val ⁻¹' positiveDefiniteLocus (M := M) (F := F) (W := W)
    et Kc hKc Ko hKo hKoEq hcover)
  exact (isOpen_setOf_forall_pos (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover).preimage continuous_subtype_val

/-- Genuine continuous Riemannian metrics land in the open metric locus of the closed symmetric
section space. -/
lemma _root_.Bundle.ContinuousRiemannianMetric.mem_riemannianMetricLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (g : _root_.Bundle.ContinuousRiemannianMetric F W)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    g.toSymmetricSectionSpace et Kc hKc Ko hKo hKoEq hcover ∈
      riemannianMetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover := by
  show (g.toSymmetricSectionSpace et Kc hKc Ko hKo hKoEq hcover).1 ∈
      positiveDefiniteLocus (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
  exact mem_positiveDefiniteLocus_of_continuousRiemannianMetric
    (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g

/-- Genuine continuous Riemannian metrics land in the open metric locus of the symmetric
submodule Banach carrier. -/
lemma _root_.Bundle.ContinuousRiemannianMetric.mem_riemannianMetricLocusSubmodule
    {κ : Type*} [Finite κ] [T2Space M]
    (g : _root_.Bundle.ContinuousRiemannianMetric F W)
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    g.toSymmetricSectionSubmodule x0 et het Kc hKc Ko hKo hKoEq hcover ∈
      riemannianMetricLocusSubmodule (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover := by
  show (g.toSymmetricSectionSubmodule x0 et het Kc hKc Ko hKo hKoEq hcover).1 ∈
      positiveDefiniteLocus (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
  exact mem_positiveDefiniteLocus_of_continuousRiemannianMetric
    (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g

end

end PreferredTrivializations

end ContinuousSectionSpace

end CoordinatePositivity

namespace ContinuousSectionSpace

section PreferredBilinearNormControl

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, SeminormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "BilW" => _root_.Bundle.BilinearFormBundle (V := W)

local instance bilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ))
local instance bilFNormedSpace : NormedSpace ℝ BilF :=
  (inferInstance : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ))
local instance bilWSeminormedAddCommGroup (x : M) : SeminormedAddCommGroup (BilW x) :=
  inferInstance
local instance bilWNormedSpace (x : M) : NormedSpace ℝ (BilW x) :=
  inferInstance
/-- Preferred bilinear-form trivialization maps are bounded by the square of the norm of the
underlying inverse vector-bundle trivialization. This is the concrete operator estimate behind the
finite-cover bilinear coordinate Lipschitz bound. -/
theorem preferredBilinear_trivialization_opNorm_le_of_symmL_opNorm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).symmL ℝ x.1‖ ≤ C) :
    ∀ i (x : Kc i),
      ‖(trivializationAt BilF BilW (x0 i)).continuousLinearMapAt ℝ x.1‖ ≤ C * C := by
  intro i x
  have hxBil : x.1 ∈ (trivializationAt BilF BilW (x0 i)).baseSet := hKc i x.2
  have hxW : x.1 ∈ (trivializationAt F W (x0 i)).baseSet := by
    simpa using hxBil
  let S : F →L[ℝ] W x.1 := (trivializationAt F W (x0 i)).symmL ℝ x.1
  let A : BilW x.1 →L[ℝ] BilF :=
    (trivializationAt BilF BilW (x0 i)).continuousLinearMapAt ℝ x.1
  have hS : ‖S‖ ≤ C := by
    simpa [S] using hC i x
  have hCC : 0 ≤ C * C := mul_nonneg hC0 hC0
  have hA : ‖A‖ ≤ C * C := by
    refine ContinuousLinearMap.opNorm_le_bound A hCC ?_
    intro B
    have hCB : 0 ≤ (C * C) * ‖B‖ := mul_nonneg hCC (norm_nonneg B)
    refine ContinuousLinearMap.opNorm_le_bound (A B) hCB ?_
    intro u
    have hCBu : 0 ≤ ((C * C) * ‖B‖) * ‖u‖ := mul_nonneg hCB (norm_nonneg u)
    refine ContinuousLinearMap.opNorm_le_bound ((A B) u) hCBu ?_
    intro v
    have hSu : ‖S u‖ ≤ C * ‖u‖ := by
      exact (ContinuousLinearMap.le_opNorm S u).trans
        (mul_le_mul_of_nonneg_right hS (norm_nonneg u))
    have hSv : ‖S v‖ ≤ C * ‖v‖ := by
      exact (ContinuousLinearMap.le_opNorm S v).trans
        (mul_le_mul_of_nonneg_right hS (norm_nonneg v))
    have hAuv : (A B) u v = B (S u) (S v) := by
      dsimp [A, S]
      simp only [Bundle.Trivialization.continuousLinearMapAt_apply]
      rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hxBil]
      change ((trivializationAt BilF BilW (x0 i) ⟨x.1, B⟩).2) u v = _
      rw [← Bundle.Trivialization.symm_continuousLinearEquivAt_eq' _ hxW]
      exact _root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
        (F := F) (W := W) (x0 := x0 i) (x := x.1) hxW B u v
    calc
      ‖(A B) u v‖ = ‖B (S u) (S v)‖ := by rw [hAuv]
      _ ≤ ‖B‖ * ‖S u‖ * ‖S v‖ :=
        ContinuousLinearMap.le_opNorm₂ B (S u) (S v)
      _ ≤ ‖B‖ * (C * ‖u‖) * (C * ‖v‖) := by
        gcongr
      _ = (((C * C) * ‖B‖) * ‖u‖) * ‖v‖ := by ring
  simpa [A] using hA

/-- Preferred bilinear-form coordinate readouts inherit fiberwise Lipschitz control from a uniform
operator-norm bound on the preferred bilinear-form trivializations. This is the bilinear-bundle
specialization of the finite-cover norm bridge, ready to feed smooth-density arguments. -/
theorem preferredBilinear_coord_dist_le_of_trivialization_opNorm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {L : ℝ}
    (hL : ∀ i (x : Kc i),
      ‖(trivializationAt BilF BilW (x0 i)).continuousLinearMapAt ℝ x.1‖ ≤ L)
    (s t : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    ∀ i (x : Kc i),
      dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW)
            (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover s).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW)
            (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover t).1 i x)
        ≤ L * dist (ContinuousSectionSpace.toFun s x.1)
          (ContinuousSectionSpace.toFun t x.1) := by
  simpa only using
    coord_dist_le_of_trivialization_opNorm_le
    (𝕜 := ℝ) (F := BilF) (V := BilW)
    (et := fun i => trivializationAt BilF BilW (x0 i))
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) hL s t

/-- Preferred bilinear-form coordinate readouts are Lipschitz with the square of a uniform bound on
the underlying inverse vector-bundle trivializations. -/
theorem preferredBilinear_coord_dist_le_of_symmL_opNorm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).symmL ℝ x.1‖ ≤ C)
    (s t : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    ∀ i (x : Kc i),
      dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW)
            (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover s).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW)
            (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover t).1 i x)
        ≤ (C * C) * dist (ContinuousSectionSpace.toFun s x.1)
          (ContinuousSectionSpace.toFun t x.1) :=
  preferredBilinear_coord_dist_le_of_trivialization_opNorm_le
    (M := M) (F := F) (W := W) (x0 := x0)
    (hL := preferredBilinear_trivialization_opNorm_le_of_symmL_opNorm_le
      (M := M) (F := F) (W := W) (x0 := x0) (hKc := hKc) hC0 hC)
    s t

/-- Fiberwise approximation of preferred bilinear-form sections upgrades to approximation in the
transported finite-cover section norm when the inverse vector-bundle trivializations are uniformly
bounded on the cover. -/
theorem exists_dist_lt_of_forall_fiber_dist_lt_preferredBilinear_of_symmL_opNorm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    {P : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover → Prop}
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).symmL ℝ x.1‖ ≤ C)
    (happrox : ∀ η > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover,
        P u ∧ ∀ x : M, dist (s x) (u x) < η) :
    ∀ ε > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover,
        P u ∧ dist s u < ε := by
  refine exists_dist_lt_of_forall_fiber_dist_lt_of_coord_lipschitz
    (𝕜 := ℝ) (F := BilF) (V := BilW)
    (et := fun i => trivializationAt BilF BilW (x0 i))
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover)
    (s := s) (P := P) (L := C * C) (mul_pos hCpos hCpos) happrox ?_
  intro u _huP
  exact preferredBilinear_coord_dist_le_of_symmL_opNorm_le
    (M := M) (F := F) (W := W) (x0 := x0)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover)
    (C := C) hCpos.le hC s u

/-- A preferred bilinear-form section-space vector field is Lipschitz in the transported
finite-cover norm once its fibrewise values are Lipschitz and the preferred inverse
trivializations are uniformly bounded.  The resulting section-space Lipschitz constant is the
fibrewise constant multiplied by the square of the trivialization bound. -/
theorem preferredBilinear_lipschitzOnWith_of_forall_fiber_dist_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)}
    {A : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).symmL ℝ x.1‖ ≤ C)
    {K : NNReal}
    (hfiber : ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet → ∀ x : M,
      dist ((A s) x) ((A t) x) ≤ (K : ℝ) * dist s t) :
    LipschitzOnWith
      ⟨(C * C) * (K : ℝ), mul_nonneg (mul_nonneg hC0 hC0) (NNReal.coe_nonneg K)⟩
      A stateSet := by
  let Ksection : NNReal :=
    ⟨(C * C) * (K : ℝ), mul_nonneg (mul_nonneg hC0 hC0) (NNReal.coe_nonneg K)⟩
  change LipschitzOnWith Ksection A stateSet
  refine lipschitzOnWith_of_forall_coord_dist_le
    (𝕜 := ℝ) (F := BilF) (V := BilW)
    (et := fun i => trivializationAt BilF BilW (x0 i))
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover)
    (stateSet := stateSet) (A := A) (L := Ksection) ?_
  intro s hs t ht i x
  calc
    dist
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover (A s)).1 i x)
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover (A t)).1 i x)
        ≤ (C * C) * dist ((A s) x.1) ((A t) x.1) :=
          preferredBilinear_coord_dist_le_of_symmL_opNorm_le
            (M := M) (F := F) (W := W) (x0 := x0)
            (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
            (hKoEq := hKoEq) (hcover := hcover)
            (C := C) hC0 hC (A s) (A t) i x
    _ ≤ (C * C) * ((K : ℝ) * dist s t) :=
          mul_le_mul_of_nonneg_left (hfiber hs ht x.1) (mul_nonneg hC0 hC0)
    _ = (Ksection : ℝ) * dist s t := by
          change C * C * ((K : ℝ) * dist s t) = ((C * C) * (K : ℝ)) * dist s t
          ring

/-- Time-parameterized preferred-bilinear version of
`preferredBilinear_lipschitzOnWith_of_forall_fiber_dist_le`. -/
theorem preferredBilinear_lipschitzOnWith_family_of_forall_fiber_dist_le
    {κ : Type*} [Finite κ] [T2Space M]
    {τ : Type*} {timeSet : Set τ}
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)}
    {A : τ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).symmL ℝ x.1‖ ≤ C)
    {K : NNReal}
    (hfiber : ∀ τ, τ ∈ timeSet → ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet →
      ∀ x : M, dist ((A τ s) x) ((A τ t) x) ≤ (K : ℝ) * dist s t) :
    ∀ τ ∈ timeSet,
      LipschitzOnWith
        ⟨(C * C) * (K : ℝ), mul_nonneg (mul_nonneg hC0 hC0) (NNReal.coe_nonneg K)⟩
        (A τ) stateSet := by
  intro τ hτ
  exact preferredBilinear_lipschitzOnWith_of_forall_fiber_dist_le
    (M := M) (F := F) (W := W) (x0 := x0)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover)
    (stateSet := stateSet) (A := A τ)
    (C := C) hC0 hC (K := K)
    (fun s hs t ht x => hfiber τ hτ hs ht x)

/-- Version of `preferredBilinear_lipschitzOnWith_of_forall_fiber_dist_le` for a cover `et`
known pointwise to be the preferred bilinear-form trivialization cover.  This is the shape carried
by the Ricci-DeTurck Banach-chart records. -/
theorem preferredBilinear_lipschitzOnWith_of_forall_fiber_dist_le_of_eq_trivializationAt
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {A : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).symmL ℝ x.1‖ ≤ C)
    {K : NNReal}
    (hfiber : ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet → ∀ x : M,
      dist ((A s) x) ((A t) x) ≤ (K : ℝ) * dist s t) :
    LipschitzOnWith
      ⟨(C * C) * (K : ℝ), mul_nonneg (mul_nonneg hC0 hC0) (NNReal.coe_nonneg K)⟩
      A stateSet := by
  have het_fun : et = fun i => trivializationAt BilF BilW (x0 i) := funext het
  subst et
  exact preferredBilinear_lipschitzOnWith_of_forall_fiber_dist_le
    (M := M) (F := F) (W := W) (x0 := x0)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover)
    (stateSet := stateSet) (A := A)
    (C := C) hC0 hC (K := K) hfiber

/-- Time-family version of
`preferredBilinear_lipschitzOnWith_of_forall_fiber_dist_le_of_eq_trivializationAt`. -/
theorem preferredBilinear_lipschitzOnWith_family_of_forall_fiber_dist_le_of_eq_trivializationAt
    {κ : Type*} [Finite κ] [T2Space M]
    {τ : Type*} {timeSet : Set τ}
    (x0 : κ → M)
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {A : τ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).symmL ℝ x.1‖ ≤ C)
    {K : NNReal}
    (hfiber : ∀ τ, τ ∈ timeSet → ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet →
      ∀ x : M, dist ((A τ s) x) ((A τ t) x) ≤ (K : ℝ) * dist s t) :
    ∀ τ ∈ timeSet,
      LipschitzOnWith
        ⟨(C * C) * (K : ℝ), mul_nonneg (mul_nonneg hC0 hC0) (NNReal.coe_nonneg K)⟩
        (A τ) stateSet := by
  have het_fun : et = fun i => trivializationAt BilF BilW (x0 i) := funext het
  subst et
  exact preferredBilinear_lipschitzOnWith_family_of_forall_fiber_dist_le
    (M := M) (F := F) (W := W) (x0 := x0)
    (timeSet := timeSet) (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover)
    (stateSet := stateSet) (A := A)
    (C := C) hC0 hC (K := K) hfiber

/-- The fiberwise bilinear-conjugation operator on the transported bilinear-form section space, as an
`ℝ`-linear map: for a continuous tangent-endomorphism section `P` of `Hom(W, W)` it sends a section
`s` of the bilinear-form bundle to the conjugate `x ↦ (s x).bilinearComp (P x) (P x)` (continuous by
`Bundle.continuous_bilinearComp_section`).  This is the non-scalar zeroth-order reaction generator
built directly on sections — the geometric shape a linearised Ricci–DeTurck curvature term takes —
generalising `smulField`/`endoField` past the triple-nested `Hom(BilW, BilW)` bundle wall. -/
noncomputable def bilinearConjFieldLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x))) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover →ₗ[ℝ]
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover where
  toFun s := ⟨fun x ↦ ((s x).bilinearComp (P x) (P x) : BilW x),
    _root_.Bundle.continuous_bilinearComp_section s.continuous_toFun hP⟩
  map_add' s t := by
    refine ContinuousSectionSpace.ext (fun x ↦ ?_)
    rw [add_apply]
    show (((s + t) x).bilinearComp (P x) (P x) : BilW x)
      = (s x).bilinearComp (P x) (P x) + (t x).bilinearComp (P x) (P x)
    rw [add_apply]
    ext u v
    simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.add_apply]
  map_smul' c s := by
    refine ContinuousSectionSpace.ext (fun x ↦ ?_)
    rw [smul_apply]
    show (((c • s) x).bilinearComp (P x) (P x) : BilW x)
      = c • ((s x).bilinearComp (P x) (P x))
    rw [smul_apply]
    ext u v
    simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.smul_apply]

@[simp]
theorem bilinearConjFieldLinearMap_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (bilinearConjFieldLinearMap et Kc hKc Ko hKo hKoEq hcover hP s) x
      = (s x).bilinearComp (P x) (P x) :=
  rfl

/-- **The fiberwise bilinear-conjugation operator packaged as a bounded section-space operator.**
For a continuous tangent-endomorphism section `P` of `Hom(W, W)` whose section-space operator size is
controlled on the finite cover by the trivialization-distorted, `‖P‖²`-weighted bound
`‖(et i).continuousLinearMapAt ℝ x‖ · ‖(et i).symmL ℝ x‖ · ‖P x‖ · ‖P x‖ ≤ C`, the conjugation
`s ↦ (x ↦ (s x).bilinearComp (P x) (P x))` is a `ContinuousSectionSpace →L[ℝ] ContinuousSectionSpace`
of operator norm at most `C`.  This is a genuine non-scalar zeroth-order reaction generator on the
transported bilinear-form section space — the `L t : CSS →L[ℝ] CSS` shape the section-space Picard
`picard` field consumes — built through `mkContinuousOfForallCoordNormLe`: the coordinate readout of
the image is `(et i).continuousLinearMapAt ℝ x ((s x).bilinearComp (P x) (P x))`, whose norm is bounded
via `ContinuousLinearMap.norm_bilinearComp_le` (giving the `‖P x‖²` factor) after writing `s x` back
through `(et i).symmL ℝ x`.  Avoids `endoField`'s triple-nested `Hom(BilW, BilW)` bundle. -/
noncomputable def bilinearConjField
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖(et i).symmL ℝ x.1‖ * ‖P x.1‖ * ‖P x.1‖ ≤ C) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover →L[ℝ]
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover :=
  mkContinuousOfForallCoordNormLe
    (bilinearConjFieldLinearMap et Kc hKc Ko hKo hKoEq hcover hP) C hC
    (fun s i x => by
      rw [coord_apply]
      show ‖(et i).continuousLinearMapAt ℝ x.1
          ((s x.1).bilinearComp (P x.1) (P x.1) : BilW x.1)‖ ≤ C * ‖s‖
      have hsx : ‖s x.1‖ ≤ ‖(et i).symmL ℝ x.1‖ * ‖s‖ := by
        rw [apply_eq_symmL_coord s x.2]
        refine le_trans (((et i).symmL ℝ x.1).le_opNorm _) ?_
        exact mul_le_mul_of_nonneg_left (coord_norm_le_norm s i _) (norm_nonneg _)
      calc ‖(et i).continuousLinearMapAt ℝ x.1
              ((s x.1).bilinearComp (P x.1) (P x.1) : BilW x.1)‖
          ≤ ‖(et i).continuousLinearMapAt ℝ x.1‖
              * ‖((s x.1).bilinearComp (P x.1) (P x.1) : BilW x.1)‖ :=
            ((et i).continuousLinearMapAt ℝ x.1).le_opNorm _
        _ ≤ ‖(et i).continuousLinearMapAt ℝ x.1‖ * (‖s x.1‖ * ‖P x.1‖ * ‖P x.1‖) :=
            mul_le_mul_of_nonneg_left
              (ContinuousLinearMap.norm_bilinearComp_le _ _ _) (norm_nonneg _)
        _ ≤ ‖(et i).continuousLinearMapAt ℝ x.1‖
              * (‖(et i).symmL ℝ x.1‖ * ‖s‖ * ‖P x.1‖ * ‖P x.1‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hsx (norm_nonneg _)) (norm_nonneg _))
              (norm_nonneg _)
        _ = ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖(et i).symmL ℝ x.1‖
              * ‖P x.1‖ * ‖P x.1‖ * ‖s‖ := by ring
        _ ≤ C * ‖s‖ := mul_le_mul_of_nonneg_right (hbound i x) (norm_nonneg s))

@[simp]
theorem bilinearConjField_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖(et i).symmL ℝ x.1‖ * ‖P x.1‖ * ‖P x.1‖ ≤ C)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (bilinearConjField et Kc hKc Ko hKo hKoEq hcover hP C hC hbound s) x
      = (s x).bilinearComp (P x) (P x) :=
  rfl

/-- The fiberwise bilinear-conjugation operator has operator norm at most the trivialization-distorted,
`‖P‖²`-weighted fiber bound `C`. -/
theorem bilinearConjField_norm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖(et i).symmL ℝ x.1‖ * ‖P x.1‖ * ‖P x.1‖ ≤ C) :
    ‖bilinearConjField et Kc hKc Ko hKo hKoEq hcover hP C hC hbound‖ ≤ C :=
  mkContinuousOfForallCoordNormLe_norm_le _ C hC _

/-- The two-sided fiberwise bilinear-composition operator on the transported bilinear-form section
space, as an `ℝ`-linear map: for two continuous tangent-endomorphism sections `P`, `Q` of `Hom(W, W)`
it sends a section `s` to `x ↦ (s x).bilinearComp (P x) (Q x)` (the bilinear form
`(u, v) ↦ s x (P x u) (Q x v)`, continuous by `Bundle.continuous_bilinearComp₂_section`).  This is
the general non-scalar zeroth-order reaction generator built directly on sections; taking `Q = P`
recovers `bilinearConjField`, while the one-sided cases `(P, id)` and `(id, P)` are the two summands
of the intrinsic Ricci–DeTurck DeTurck-correction derivation `s(P·, ·) + s(·, P·)`. -/
noncomputable def bilinearCompFieldLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    {Q : Π x : M, W x →L[ℝ] W x}
    (hQ : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (Q x))) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover →ₗ[ℝ]
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover where
  toFun s := ⟨fun x ↦ ((s x).bilinearComp (P x) (Q x) : BilW x),
    _root_.Bundle.continuous_bilinearComp₂_section s.continuous_toFun hP hQ⟩
  map_add' s t := by
    refine ContinuousSectionSpace.ext (fun x ↦ ?_)
    rw [add_apply]
    show (((s + t) x).bilinearComp (P x) (Q x) : BilW x)
      = (s x).bilinearComp (P x) (Q x) + (t x).bilinearComp (P x) (Q x)
    rw [add_apply]
    ext u v
    simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.add_apply]
  map_smul' c s := by
    refine ContinuousSectionSpace.ext (fun x ↦ ?_)
    rw [smul_apply]
    show (((c • s) x).bilinearComp (P x) (Q x) : BilW x)
      = c • ((s x).bilinearComp (P x) (Q x))
    rw [smul_apply]
    ext u v
    simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.smul_apply]

@[simp]
theorem bilinearCompFieldLinearMap_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    {Q : Π x : M, W x →L[ℝ] W x}
    (hQ : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (Q x)))
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (bilinearCompFieldLinearMap et Kc hKc Ko hKo hKoEq hcover hP hQ s) x
      = (s x).bilinearComp (P x) (Q x) :=
  rfl

/-- **The two-sided fiberwise bilinear-composition operator packaged as a bounded section-space
operator.**  For two continuous tangent-endomorphism sections `P`, `Q` of `Hom(W, W)` whose combined
section-space operator size is controlled on the finite cover by the trivialization-distorted,
`‖P‖·‖Q‖`-weighted bound
`‖(et i).continuousLinearMapAt ℝ x‖ · ‖(et i).symmL ℝ x‖ · ‖P x‖ · ‖Q x‖ ≤ C`, the composition
`s ↦ (x ↦ (s x).bilinearComp (P x) (Q x))` is a `ContinuousSectionSpace →L[ℝ] ContinuousSectionSpace`
of operator norm at most `C`.  This generalises `bilinearConjField` (the `Q = P` conjugation) to two
different endomorphisms; the one-sided instances `(P, id)`/`(id, P)` are the summands of the intrinsic
Ricci–DeTurck reaction derivation.  Built through `mkContinuousOfForallCoordNormLe`, the coordinate
readout norm being bounded via `ContinuousLinearMap.norm_bilinearComp_le` (the `‖P x‖·‖Q x‖` factor)
after writing `s x` back through `(et i).symmL ℝ x`. -/
noncomputable def bilinearCompField
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    {Q : Π x : M, W x →L[ℝ] W x}
    (hQ : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (Q x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖(et i).symmL ℝ x.1‖ * ‖P x.1‖ * ‖Q x.1‖ ≤ C) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover →L[ℝ]
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover :=
  mkContinuousOfForallCoordNormLe
    (bilinearCompFieldLinearMap et Kc hKc Ko hKo hKoEq hcover hP hQ) C hC
    (fun s i x => by
      rw [coord_apply]
      show ‖(et i).continuousLinearMapAt ℝ x.1
          ((s x.1).bilinearComp (P x.1) (Q x.1) : BilW x.1)‖ ≤ C * ‖s‖
      have hsx : ‖s x.1‖ ≤ ‖(et i).symmL ℝ x.1‖ * ‖s‖ := by
        rw [apply_eq_symmL_coord s x.2]
        refine le_trans (((et i).symmL ℝ x.1).le_opNorm _) ?_
        exact mul_le_mul_of_nonneg_left (coord_norm_le_norm s i _) (norm_nonneg _)
      calc ‖(et i).continuousLinearMapAt ℝ x.1
              ((s x.1).bilinearComp (P x.1) (Q x.1) : BilW x.1)‖
          ≤ ‖(et i).continuousLinearMapAt ℝ x.1‖
              * ‖((s x.1).bilinearComp (P x.1) (Q x.1) : BilW x.1)‖ :=
            ((et i).continuousLinearMapAt ℝ x.1).le_opNorm _
        _ ≤ ‖(et i).continuousLinearMapAt ℝ x.1‖ * (‖s x.1‖ * ‖P x.1‖ * ‖Q x.1‖) :=
            mul_le_mul_of_nonneg_left
              (ContinuousLinearMap.norm_bilinearComp_le _ _ _) (norm_nonneg _)
        _ ≤ ‖(et i).continuousLinearMapAt ℝ x.1‖
              * (‖(et i).symmL ℝ x.1‖ * ‖s‖ * ‖P x.1‖ * ‖Q x.1‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hsx (norm_nonneg _)) (norm_nonneg _))
              (norm_nonneg _)
        _ = ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖(et i).symmL ℝ x.1‖
              * ‖P x.1‖ * ‖Q x.1‖ * ‖s‖ := by ring
        _ ≤ C * ‖s‖ := mul_le_mul_of_nonneg_right (hbound i x) (norm_nonneg s))

@[simp]
theorem bilinearCompField_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    {Q : Π x : M, W x →L[ℝ] W x}
    (hQ : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (Q x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖(et i).symmL ℝ x.1‖ * ‖P x.1‖ * ‖Q x.1‖ ≤ C)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (bilinearCompField et Kc hKc Ko hKo hKoEq hcover hP hQ C hC hbound s) x
      = (s x).bilinearComp (P x) (Q x) :=
  rfl

/-- The two-sided fiberwise bilinear-composition operator has operator norm at most the
trivialization-distorted, `‖P‖·‖Q‖`-weighted fiber bound `C`. -/
theorem bilinearCompField_norm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    {Q : Π x : M, W x →L[ℝ] W x}
    (hQ : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (Q x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖(et i).symmL ℝ x.1‖ * ‖P x.1‖ * ‖Q x.1‖ ≤ C) :
    ‖bilinearCompField et Kc hKc Ko hKo hKoEq hcover hP hQ C hC hbound‖ ≤ C :=
  mkContinuousOfForallCoordNormLe_norm_le _ C hC _

/-- **The frozen-coefficient intrinsic Ricci–DeTurck reaction (DeTurck-correction) operator, packaged
as a bounded section-space operator.**  For a continuous tangent-endomorphism section `P` of
`Hom(W, W)` whose section-space operator size is controlled on the finite cover by the
trivialization-distorted bound `‖(et i).continuousLinearMapAt ℝ x‖ · ‖(et i).symmL ℝ x‖ · ‖P x‖ ≤ C`,
the *derivation* `s ↦ (x ↦ (s x).bilinearComp (P x) id + (s x).bilinearComp id (P x))` —
pointwise `(u, v) ↦ s x (P x u) v + s x u (P x v)` — is a
`ContinuousSectionSpace →L[ℝ] ContinuousSectionSpace` of operator norm at most `2 · C`.

This is exactly the shape of the intrinsic DeTurck correction
`intrinsicDeTurckCorrection g background t x u v = (g t).inner x (∇W u) v + (g t).inner x u (∇W v)`
(with `P = ∇W` the covariant derivative of the DeTurck vector field, a continuous `Hom(TM, TM)`
section), read as a bounded operator on the transported bilinear-form section space by *freezing* the
endomorphism coefficient `P`.  It is the sum of the two one-sided `bilinearCompField` instances
`(P, id)` and `(id, P)`; the `‖id‖ ≤ 1` folding turns the single `‖P‖`-weighted bound into the two
`bilinearCompField` bounds.  This is the `L t : CSS →L[ℝ] CSS` zeroth-order geometric reaction the
frozen-coefficient section-space Picard route consumes. -/
noncomputable def bilinearDerivationField
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖(et i).symmL ℝ x.1‖ * ‖P x.1‖ ≤ C) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover →L[ℝ]
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover :=
  bilinearCompField et Kc hKc Ko hKo hKoEq hcover hP
      (continuous_id_endo_section (𝕜 := ℝ) (F := F) (V := W)) C hC
      (fun i x => (mul_le_of_le_one_right
        (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
        ContinuousLinearMap.norm_id_le).trans (hbound i x))
    + bilinearCompField et Kc hKc Ko hKo hKoEq hcover
      (continuous_id_endo_section (𝕜 := ℝ) (F := F) (V := W)) hP C hC
      (fun i x => (mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          ContinuousLinearMap.norm_id_le)
        (norm_nonneg _)).trans (hbound i x))

@[simp]
theorem bilinearDerivationField_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖(et i).symmL ℝ x.1‖ * ‖P x.1‖ ≤ C)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (bilinearDerivationField et Kc hKc Ko hKo hKoEq hcover hP C hC hbound s) x
      = (s x).bilinearComp (P x) (ContinuousLinearMap.id ℝ (W x))
        + (s x).bilinearComp (ContinuousLinearMap.id ℝ (W x)) (P x) := by
  simp only [bilinearDerivationField, ContinuousLinearMap.add_apply, add_apply,
    bilinearCompField_apply]

/-- The frozen-coefficient DeTurck reaction operator, evaluated fiberwise on a tangent pair, is the
symmetrized composition `s x (P x u) v + s x u (P x v)` — the exact pointwise form of the intrinsic
DeTurck correction term. -/
theorem bilinearDerivationField_apply_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖(et i).symmL ℝ x.1‖ * ‖P x.1‖ ≤ C)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover)
    (x : M) (u v : W x) :
    (bilinearDerivationField et Kc hKc Ko hKo hKoEq hcover hP C hC hbound s) x u v
      = s x (P x u) v + s x u (P x v) := by
  rw [bilinearDerivationField_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply]

/-- The frozen-coefficient DeTurck reaction operator has operator norm at most `2 · C`, twice the
`‖P‖`-weighted trivialization-distorted fiber bound (one `C` for each one-sided slot). -/
theorem bilinearDerivationField_norm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt ℝ x.1‖ * ‖(et i).symmL ℝ x.1‖ * ‖P x.1‖ ≤ C) :
    ‖bilinearDerivationField et Kc hKc Ko hKo hKoEq hcover hP C hC hbound‖ ≤ 2 * C := by
  unfold bilinearDerivationField
  refine (norm_add_le _ _).trans ?_
  rw [two_mul]
  exact add_le_add
    (bilinearCompField_norm_le et Kc hKc Ko hKo hKoEq hcover hP _ C hC _)
    (bilinearCompField_norm_le et Kc hKc Ko hKo hKoEq hcover _ hP C hC _)

/-- **The frozen-coefficient DeTurck-correction reaction as an unbundled `ℝ`-linear map on the
section space.**  Unlike `bilinearDerivationField` (which packages the derivation as a bounded
`ContinuousSectionSpace →L[ℝ] ContinuousSectionSpace` and therefore needs the raw fiber-norm bound
`hbound` — the estimate that is *un-elaborable* at `W := TangentSpace I` because `‖P x‖ =
‖TM x →L[ℝ] TM x‖` is not synthesizable), this variant is the plain `LinearMap` `s ↦ (x ↦ (s x)
.bilinearComp (P x) id + (s x).bilinearComp id (P x))`, whose only analytic input is the *continuity*
of the two summands (`bilinearCompFieldLinearMap`, discharged by `continuous_bilinearComp₂_section`).
This is exactly the shape `A t s` the section-space Picard bridge consumes as a plain
`ℝ → ContinuousSectionSpace → ContinuousSectionSpace` map, freezing the endomorphism coefficient
`P` (e.g. `∇W` about the initial metric).  Its coordinate readout Lipschitz control is supplied — in
the clean model fibre — by `norm_trivializationAt_bilinearFormBundle_deTurckDerivation_readout_sub_le`,
so the operator never needs the raw fiber-norm `hbound` at all. -/
noncomputable def bilinearDerivationFieldLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x))) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover →ₗ[ℝ]
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover :=
  bilinearCompFieldLinearMap et Kc hKc Ko hKo hKoEq hcover hP
      (continuous_id_endo_section (𝕜 := ℝ) (F := F) (V := W))
    + bilinearCompFieldLinearMap et Kc hKc Ko hKo hKoEq hcover
      (continuous_id_endo_section (𝕜 := ℝ) (F := F) (V := W)) hP

@[simp]
theorem bilinearDerivationFieldLinearMap_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (bilinearDerivationFieldLinearMap et Kc hKc Ko hKo hKoEq hcover hP s) x
      = (s x).bilinearComp (P x) (ContinuousLinearMap.id ℝ (W x))
        + (s x).bilinearComp (ContinuousLinearMap.id ℝ (W x)) (P x) := by
  simp only [bilinearDerivationFieldLinearMap, LinearMap.add_apply, add_apply,
    bilinearCompFieldLinearMap_apply]

/-- **The compact coordinate readout of a bilinear-form section is the `trivializationAt` readout.**
When the trivialization family is chosen to be the canonical `trivializationAt BilF BilW (x0 i)`, the
continuous-section-space coordinate `(coord σ).1 i x` (`equivCompatibleCoordFamilySubmodule`) equals
the raw fibre readout `(trivializationAt BilF BilW (x0 i) ⟨x, σ x⟩).2`.  This is the bridge between
the two languages used on either side of the section-space Picard `hlip`/`hcenter` obligations: the
bridge states them in the `coord` language, while the model-fibre estimates
(`norm_trivializationAt_bilinearFormBundle_deTurckDerivation_readout_*`) are proved in the
`trivializationAt`-readout language.  Combines the general `coord_apply`
(`(coord σ).1 i x = (et i).continuousLinearMapAt ℝ x (σ x)`) with the trivialization identity
`continuousLinearMapAt = (e ⟨x, ·⟩).2` on the base set (`coe_linearMapAt_of_mem`). -/
theorem bilinearFormBundle_coord_eq_trivializationAt_readout
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (σ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover σ).1 i x
      = (trivializationAt BilF BilW (x0 i)
          (_root_.Bundle.TotalSpace.mk' BilF x.1 (σ x.1))).2 := by
  haveI hlin : (trivializationAt BilF BilW (x0 i)).IsLinear ℝ :=
    _root_.Bundle.trivializationAt_bilinearFormBundle_isLinear (F := F) (W := W) (x0 i)
  rw [coord_apply σ i x]
  simp only [_root_.Bundle.Trivialization.continuousLinearMapAt_apply,
    _root_.Bundle.Trivialization.coe_linearMapAt_of_mem _ (hKc i x.2)]

/-- **The section-space Picard `hlip` coordinate-Lipschitz bound for the frozen-coefficient
DeTurck-correction reaction, at the canonical bilinear-form trivialization family.**  For the plain
operator `bilinearDerivationFieldLinearMap` (the derivation `s ↦ (x ↦ (s x).bilinearComp (P x) id +
(s x).bilinearComp id (P x))`), the section-space coordinate distance is controlled by
`2·Kp·dist s s'`, where `Kp` is any uniform bound on the model-fibre endomorphism readout
`‖inCoordinates F W F W (x0 i) x (x0 i) x (P x)‖` over the finite cover.  This is *exactly* the shape
of the `hlip` hypothesis of
`sectionSpace_banachEvolutionLocalSolutionIn_exists_of_forall_coord_centerBound`, with
`K := 2·Kp`.  The proof passes through the coordinate-readout bridge
`bilinearFormBundle_coord_eq_trivializationAt_readout` (translating the `coord` language of the Picard
bridge into the `trivializationAt`-readout language) and applies the clean-model-fibre estimate
`norm_trivializationAt_bilinearFormBundle_deTurckDerivation_readout_sub_le`, whose Lipschitz constant
`2‖inCoord P‖` is finally bounded by `2·Kp` and whose readout-difference is bounded by the
section distance via `coord_dist_le_dist` — every norm in the clean model fibre, so it elaborates at
`W := TangentSpace I` where the raw fibre norms are un-synthesizable. -/
theorem bilinearDerivationFieldLinearMap_coord_dist_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (Kp : ℝ)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates F W F W (x0 i) x.1 (x0 i) x.1 (P x.1)‖ ≤ Kp)
    (s s' : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) :
    dist
      ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
        (bilinearDerivationFieldLinearMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s)).1 i x)
      ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
        (bilinearDerivationFieldLinearMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s')).1 i x)
      ≤ 2 * Kp * dist s s' := by
  have hxW : x.1 ∈ (trivializationAt F W (x0 i)).baseSet := by simpa using hKc i x.2
  have hKp0 : (0 : ℝ) ≤ Kp := le_trans (norm_nonneg _) (hKp i x)
  rw [dist_eq_norm,
    bilinearFormBundle_coord_eq_trivializationAt_readout x0 Kc hKc Ko hKo hKoEq hcover _ i x,
    bilinearFormBundle_coord_eq_trivializationAt_readout x0 Kc hKc Ko hKo hKoEq hcover _ i x,
    bilinearDerivationFieldLinearMap_apply, bilinearDerivationFieldLinearMap_apply]
  refine (_root_.Bundle.norm_trivializationAt_bilinearFormBundle_deTurckDerivation_readout_sub_le
      (fun y => s y) (fun y => s' y) P (x0 i) x.1 hxW).trans ?_
  have hcoord : ‖(trivializationAt BilF BilW (x0 i)
        (_root_.Bundle.TotalSpace.mk' BilF x.1 (s x.1))).2
      - (trivializationAt BilF BilW (x0 i)
        (_root_.Bundle.TotalSpace.mk' BilF x.1 (s' x.1))).2‖ ≤ dist s s' := by
    rw [← bilinearFormBundle_coord_eq_trivializationAt_readout x0 Kc hKc Ko hKo hKoEq hcover s i x,
      ← bilinearFormBundle_coord_eq_trivializationAt_readout x0 Kc hKc Ko hKo hKoEq hcover s' i x,
      ← dist_eq_norm]
    exact coord_dist_le_dist s s' i x
  refine mul_le_mul (mul_le_mul_of_nonneg_left (hKp i x) (by norm_num)) hcoord
    (norm_nonneg _) (mul_nonneg (by norm_num) hKp0)

/-- **The section-space Picard `hcenter` coordinate-norm bound for the frozen-coefficient
DeTurck-correction reaction, at the canonical bilinear-form trivialization family.**  For the plain
operator `bilinearDerivationFieldLinearMap`, the section-space coordinate norm of the reaction applied
to a section `σ` is controlled by `2·Kp·‖σ‖`, where `Kp` uniformly bounds the model-fibre endomorphism
readout `‖inCoordinates F W F W (x0 i) x (x0 i) x (P x)‖` over the finite cover.  Applied at the
initial-metric section `σ = x0`, this is exactly the `hcenter` datum `‖(coord (A t x0)) i x‖ ≤ Mc`
(with `Mc := 2·Kp·‖x0‖`) that the section-space Picard bridge
`sectionSpace_banachEvolutionLocalSolutionIn_exists_of_forall_coord_centerBound` consumes for the
reaction summand.  Companion of `bilinearDerivationFieldLinearMap_coord_dist_le`: same route through
`bilinearFormBundle_coord_eq_trivializationAt_readout` and the clean-model-fibre size bound
`norm_trivializationAt_bilinearFormBundle_deTurckDerivation_readout_le`, closing with
`coord_norm_le_norm`. -/
theorem bilinearDerivationFieldLinearMap_coord_norm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (Kp : ℝ)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates F W F W (x0 i) x.1 (x0 i) x.1 (P x.1)‖ ≤ Kp)
    (σ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) :
    ‖(equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
        (bilinearDerivationFieldLinearMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP σ)).1 i x‖
      ≤ 2 * Kp * ‖σ‖ := by
  have hxW : x.1 ∈ (trivializationAt F W (x0 i)).baseSet := by simpa using hKc i x.2
  have hKp0 : (0 : ℝ) ≤ Kp := le_trans (norm_nonneg _) (hKp i x)
  rw [bilinearFormBundle_coord_eq_trivializationAt_readout x0 Kc hKc Ko hKo hKoEq hcover _ i x,
    bilinearDerivationFieldLinearMap_apply]
  refine (_root_.Bundle.norm_trivializationAt_bilinearFormBundle_deTurckDerivation_readout_le
      (fun y => σ y) P (x0 i) x.1 hxW).trans ?_
  have hσ : ‖(trivializationAt BilF BilW (x0 i)
        (_root_.Bundle.TotalSpace.mk' BilF x.1 (σ x.1))).2‖ ≤ ‖σ‖ := by
    rw [← bilinearFormBundle_coord_eq_trivializationAt_readout x0 Kc hKc Ko hKo hKoEq hcover σ i x]
    exact coord_norm_le_norm σ i x
  calc 2 * ‖(trivializationAt BilF BilW (x0 i)
          (_root_.Bundle.TotalSpace.mk' BilF x.1 (σ x.1))).2‖
        * ‖ContinuousLinearMap.inCoordinates F W F W (x0 i) x.1 (x0 i) x.1 (P x.1)‖
      ≤ 2 * ‖σ‖ * Kp := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hσ (by norm_num)) (hKp i x)
          (norm_nonneg _) (by positivity)
    _ = 2 * Kp * ‖σ‖ := by ring

/-- **Affine-operator coordinate Lipschitz bound (`hlip`) for the frozen DeTurck reaction plus a
fixed source.**  For the affine section-space operator `s ↦ bilinearDerivationFieldLinearMap … s + b`
(the frozen two-sided derivation `L` plus a fixed source `b`), the section-space coordinate distance
is controlled by `2·Kp·dist s s'` — *the same constant as the linear reaction alone*, because the
fixed source `b` contributes the identical coordinate summand `coord b i x` to both `A s` and `A s'`,
which cancels in the coordinate distance (`coord_add_apply` + `add_sub_add_right_eq_sub`).  This is
exactly the `hlip` datum the section-space Picard bridge consumes for the *affine* chart operator
`A t s = L s + b` at the metric state, with `K := 2·Kp`. -/
theorem bilinearDerivationFieldLinearMap_add_source_coord_dist_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (Kp : ℝ)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates F W F W (x0 i) x.1 (x0 i) x.1 (P x.1)‖ ≤ Kp)
    (b s s' : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) :
    dist
      ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
        (bilinearDerivationFieldLinearMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s + b)).1 i x)
      ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
        (bilinearDerivationFieldLinearMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s' + b)).1 i x)
      ≤ 2 * Kp * dist s s' := by
  rw [dist_eq_norm,
    coord_add_apply (bilinearDerivationFieldLinearMap (fun i => trivializationAt BilF BilW (x0 i))
      Kc hKc Ko hKo hKoEq hcover hP s) b i x,
    coord_add_apply (bilinearDerivationFieldLinearMap (fun i => trivializationAt BilF BilW (x0 i))
      Kc hKc Ko hKo hKoEq hcover hP s') b i x,
    add_sub_add_right_eq_sub, ← dist_eq_norm]
  exact bilinearDerivationFieldLinearMap_coord_dist_le
    x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp s s' i x

/-- **Affine-operator coordinate norm bound (`hcenter`) for the frozen DeTurck reaction plus a fixed
source.**  For the affine section-space operator `σ ↦ bilinearDerivationFieldLinearMap … σ + b`, the
section-space coordinate norm is controlled by `2·Kp·‖σ‖ + ‖b‖`: the reaction summand contributes
`2·Kp·‖σ‖` (`bilinearDerivationFieldLinearMap_coord_norm_le`) and the fixed source `b` contributes at
most `‖b‖` (`coord_norm_le_norm`), combined through `coord_add_apply` and the triangle inequality.
Applied at the initial-metric section `σ = σ0`, this is exactly the `hcenter` datum
`‖coord (A t σ0) i x‖ ≤ Mc` (with `Mc := 2·Kp·‖σ0‖ + ‖b‖`) that the section-space Picard bridge
consumes for the affine chart operator `A t s = L s + b`. -/
theorem bilinearDerivationFieldLinearMap_add_source_coord_norm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (Kp : ℝ)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates F W F W (x0 i) x.1 (x0 i) x.1 (P x.1)‖ ≤ Kp)
    (b σ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) :
    ‖(equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
        (bilinearDerivationFieldLinearMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP σ + b)).1 i x‖
      ≤ 2 * Kp * ‖σ‖ + ‖b‖ := by
  rw [coord_add_apply (bilinearDerivationFieldLinearMap (fun i => trivializationAt BilF BilW (x0 i))
    Kc hKc Ko hKo hKoEq hcover hP σ) b i x]
  refine (norm_add_le _ _).trans ?_
  exact add_le_add
    (bilinearDerivationFieldLinearMap_coord_norm_le x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp σ i x)
    (coord_norm_le_norm b i x)

end PreferredBilinearNormControl

end ContinuousSectionSpace

end Bundle.Trivialization

end PoincareCurvature
