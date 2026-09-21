/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchi

/-! Unrestricted evaluation of curvature on smooth tangent fields.
The right section is localized by a bump equal to one near the evaluation point;
its frame coefficients are then globally smooth, as required by the existing API. -/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
/-- Bump localization supplies global coefficient regularity without an extension hypothesis. -/
lemma curvatureEvaluation_bump_coeff_contMDiff
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (x : M) {Z : Π y : M, TM y}
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z)) (i : ι) :
    ContMDiff I 𝓘(ℝ) 2 (fun y ↦
      (trivializationAt E TM x).localFrameCoeff I b i y
        ((smoothExtendBump (I := I) (F := E) (V := TM) x : M → ℝ) y • Z y)) := by
  let e := trivializationAt E TM x
  let φ := smoothExtendBump (I := I) (F := E) (V := TM) x
  have hφ : ContMDiff I 𝓘(ℝ) 2 (φ : M → ℝ) :=
    φ.contMDiff.of_le (WithTop.coe_le_coe.2 le_top)
  have hs := hφ.smul_section hZ
  have hb := contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b)
    (t := e.baseSet) (k := (2 : WithTop ℕ∞))
    e.open_baseSet (subset_refl _) hs.contMDiffOn i
  have hc : ContMDiffOn I 𝓘(ℝ) 2
      (fun y ↦ e.localFrameCoeff I b i y ((φ : M → ℝ) y • Z y))
      (tsupport φ)ᶜ := by
    refine (contMDiff_const.contMDiffOn : ContMDiffOn I 𝓘(ℝ) 2
      (fun _ : M ↦ (0 : ℝ)) (tsupport φ)ᶜ).congr ?_
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  have hcover : e.baseSet ∪ (tsupport φ)ᶜ = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    by_cases hy : y ∈ e.baseSet
    · exact Or.inl hy
    · exact Or.inr fun h ↦ hy
        (tsupport_smoothExtendBump_subset (I := I) (F := E) (V := TM) x h)
  exact contMDiff_of_contMDiffOn_union_of_isOpen hb hc hcover e.open_baseSet
    (isOpen_compl_iff.mpr (isClosed_tsupport φ))

/-- Actual raw curvature agrees with the bundled tensor on arbitrary globally smooth fields.
Only C¹ regularity in the first two fields and C² in the third is needed. -/
theorem curvatureAux_eq_curvatureTensor_apply_of_contMDiff
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {X Y Z : Π y : M, TM y}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z)) (x : M) :
    cov.curvatureAux X Y Z x = cov.curvatureTensor x (X x) (Y x) (Z x) := by
  classical
  let φ := smoothExtendBump (I := I) (F := E) (V := TM) x
  let Z' : Π y : M, TM y := fun y ↦ (φ : M → ℝ) y • Z y
  have hφ : ContMDiff I 𝓘(ℝ) 2 (φ : M → ℝ) :=
    φ.contMDiff.of_le (WithTop.coe_le_coe.2 le_top)
  have hZ' : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z') := hφ.smul_section hZ
  have heq : ∀ᶠ y in nhds x, Z y = Z' y := by
    filter_upwards [φ.eventuallyEq_one] with y hy
    simp [Z', hy]
  have hx : Z' x = Z x := (heq.self_of_nhds).symm
  rw [cov.curvatureAux_eq_of_eventuallyEq_right_apply hX hY hZ hZ' heq]
  exact cov.curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_localFrameCoeff_right
    (Module.finBasis ℝ E) hX hY hZ' rfl rfl
    (fun i ↦ curvatureEvaluation_bump_coeff_contMDiff (Module.finBasis ℝ E) x hZ i)
    (fun i ↦ by rw [hx])

/-- C³ specialization for the section-facing contracted Bianchi identity. -/
theorem curvatureAux_eq_curvatureTensor_apply_of_contMDiff_three
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {X Y Z : Π y : M, TM y}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% Z)) (x : M) :
    cov.curvatureAux X Y Z x = cov.curvatureTensor x (X x) (Y x) (Z x) :=
  curvatureAux_eq_curvatureTensor_apply_of_contMDiff cov
    (hX.of_le (by norm_num)) (hY.of_le (by norm_num)) (hZ.of_le (by norm_num)) x

end CovariantDerivative
