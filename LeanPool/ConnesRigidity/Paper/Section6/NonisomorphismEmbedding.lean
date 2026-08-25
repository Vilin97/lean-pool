/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Concrete §6 embedding of Zhou's nonsplit finite correction into the full
second kernel. This closes the semisimplicity obstruction for every quotient
automorphism. Paper: §6.
-/
import LeanPool.ConnesRigidity.Paper.Section6.NonisomorphismProofs
import LeanPool.ConnesRigidity.Construction.PaperActionInstances

/-!
The nonisomorphism embedding component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperNonisomorphism

open Construction
open Construction.PaperKernel

noncomputable section

/--
The `paperDTwoEmbeddingLinear` construction used in the Connes rigidity formalization.
-/
def paperDTwoEmbeddingLinear : PaperEll →ₗ[k] PaperKernel.D where
  toFun p :=
    (a0 ⊗ₜ[k] p.1, p.2 • PaperKernel.diagonal a0)
  map_add' p r := by
    apply Prod.ext
    · change a0 ⊗ₜ[k] (p.1 + r.1) =
        a0 ⊗ₜ[k] p.1 + a0 ⊗ₜ[k] r.1
      rw [TensorProduct.tmul_add]
    · simp [add_smul]
  map_smul' a p := by
    apply Prod.ext
    · change a0 ⊗ₜ[k] (a • p.1) =
        a • (a0 ⊗ₜ[k] p.1)
      rw [TensorProduct.tmul_smul]
    · change (a * p.2) • PaperKernel.diagonal a0 =
        a • (p.2 • PaperKernel.diagonal a0)
      rw [smul_smul]

/--
The `paperDTwoEmbeddingIntertwining` construction used in the Connes rigidity formalization.
-/
def paperDTwoEmbeddingIntertwining :
    Representation.IntertwiningMap paperEllRepresentation
      (qRepresentationTwo) :=
  paperDTwoEmbeddingLinear.intertwiningMap_of_isIntertwiningMap
    paperEllRepresentation (qRepresentationTwo) (by
      intro q p
      change
        (a0 ⊗ₜ[k]
            (qVStarActionHom q p.1 +
              p.2 • OpenAIPort.quadraticDefectLinear q),
          p.2 • PaperKernel.diagonal a0) =
          thetaTwoLinearMap ((1 : SpecialLinear.SL3), q)
            (a0 ⊗ₜ[k] p.1, p.2 • PaperKernel.diagonal a0)
      have hc : sl3CAction (1 : SpecialLinear.SL3) = LinearMap.id := by
        have hm := sl3CActionHom.map_one
        change sl3CActionEquiv (1 : SpecialLinear.SL3) =
          LinearEquiv.refl k PaperKernel.C at hm
        exact congrArg LinearEquiv.toLinearMap hm
      apply Prod.ext
      · change a0 ⊗ₜ[k]
            (qVStarActionHom q p.1 +
              p.2 • OpenAIPort.quadraticDefectLinear q) =
          avStarAction (1 : SpecialLinear.SL3) q
              (a0 ⊗ₜ[k] p.1) +
            PaperKernel.delta (sl3CAction (1 : SpecialLinear.SL3)
              (p.2 • PaperKernel.diagonal a0)) ⊗ₜ[k]
              OpenAIPort.quadraticDefectLinear q
        rw [avStar_q_action, hc]
        rw [LinearMap.id_apply, map_smul, PaperKernel.delta_diagonal]
        rw [TensorProduct.tmul_add]
        rw [TensorProduct.smul_tmul]
      · change p.2 • PaperKernel.diagonal a0 =
          sl3CAction (1 : SpecialLinear.SL3)
            (p.2 • PaperKernel.diagonal a0)
        rw [hc]
        rfl)

theorem paperDTwoEmbedding_injective :
    Function.Injective paperDTwoEmbeddingLinear := by
  intro p r h
  have hfirst := congrArg Prod.fst h
  have hsecond := congrArg Prod.snd h
  change a0 ⊗ₜ[k] p.1 = a0 ⊗ₜ[k] r.1 at hfirst
  change p.2 • PaperKernel.diagonal a0 =
    r.2 • PaperKernel.diagonal a0 at hsecond
  have hdiag : PaperKernel.diagonal a0 ≠ 0 := by
    intro hzero
    apply a0_ne_zero
    have hdelta := congrArg PaperKernel.delta hzero
    rw [PaperKernel.delta_diagonal] at hdelta
    exact hdelta
  have hscalar : p.2 = r.2 :=
    (smul_left_injective k (m := PaperKernel.diagonal a0) hdiag) hsecond
  have hfunctional : ∀ v : PaperKernel.PaperV, p.1 v = r.1 v := by
    intro v
    have hcontract := congrArg
      (contractStar (LinearMap.applyₗ (R := k) v)) hfirst
    rw [contractStar_tmul, contractStar_tmul] at hcontract
    exact (smul_left_injective k a0_ne_zero) hcontract
  apply Prod.ext
  · apply LinearMap.ext
    intro v
    exact hfunctional v
  · exact hscalar

/--
The `paperDTwoEmbedding` construction used in the Connes rigidity formalization.
-/
def paperDTwoEmbedding :
    paperEllRepresentation.asModule →ₗ[Ring]
      (qRepresentationTwo).asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule
    paperEllRepresentation (qRepresentationTwo)).toFun
    paperDTwoEmbeddingIntertwining

theorem paperDTwoEmbedding_module_injective :
    Function.Injective paperDTwoEmbedding := by
  intro p r h
  apply paperDTwoEmbedding_injective
  exact h

theorem paper_moduleTwo_not_semisimple :
    ¬ moduleTwoSemisimple := by
  intro h
  let _ : IsSemisimpleModule Ring
      (qRepresentationTwo).asModule := h
  have hE : IsSemisimpleModule Ring paperEllRepresentation.asModule :=
    IsSemisimpleModule.of_injective paperDTwoEmbedding
      paperDTwoEmbedding_module_injective
  exact paperEll_not_semisimple hE

/--
The `paperEllRepresentationAlong` construction used in the Connes rigidity formalization.
-/
def paperEllRepresentationAlong (σ : PaperKernel.Q ≃* PaperKernel.Q) :
    Representation k PaperKernel.Q PaperEll :=
  paperEllRepresentation.comp σ

/--
The `paperDTwoEmbeddingIntertwiningAlong` construction used in the Connes rigidity formalization.
-/
def paperDTwoEmbeddingIntertwiningAlong
    (σ : PaperKernel.Q ≃* PaperKernel.Q) :
    Representation.IntertwiningMap
      (paperEllRepresentationAlong σ)
      (qRepresentationTwoAlong σ) :=
  paperDTwoEmbeddingLinear.intertwiningMap_of_isIntertwiningMap
    (paperEllRepresentationAlong σ)
    (qRepresentationTwoAlong σ) (by
      intro q p
      change paperDTwoEmbeddingLinear
          (paperEllRepresentation (σ q) p) =
        (qRepresentationTwo (σ q))
          (paperDTwoEmbeddingLinear p)
      have h := Representation.IntertwiningMap.isIntertwining
        paperEllRepresentation
          (qRepresentationTwo)
          paperDTwoEmbeddingIntertwining (σ q) p
      change paperDTwoEmbeddingLinear
          (paperEllRepresentation (σ q) p) =
        (qRepresentationTwo (σ q))
          (paperDTwoEmbeddingLinear p) at h
      exact h)

/--
The `paperDTwoEmbeddingAlong` construction used in the Connes rigidity formalization.
-/
def paperDTwoEmbeddingAlong
    (σ : PaperKernel.Q ≃* PaperKernel.Q) :
      (paperEllRepresentationAlong σ).asModule →ₗ[Ring]
      (qRepresentationTwoAlong σ).asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule
    (paperEllRepresentationAlong σ)
    (qRepresentationTwoAlong σ)).toFun
    (paperDTwoEmbeddingIntertwiningAlong σ)

theorem paperDTwoEmbeddingAlong_injective
    (σ : PaperKernel.Q ≃* PaperKernel.Q) :
    Function.Injective (paperDTwoEmbeddingAlong σ) := by
  intro p r h
  apply paperDTwoEmbedding_injective
  exact h

/--
The `paperEllVStarRepresentationAlong` construction used in the Connes rigidity formalization.
-/
def paperEllVStarRepresentationAlong
    (σ : PaperKernel.Q ≃* PaperKernel.Q) :
    Representation k PaperKernel.Q PaperKernel.VStar :=
  paperEllVStarRepresentation.comp σ

/--
The `paperEllScalarRepresentationAlong` construction used in the Connes rigidity formalization.
-/
def paperEllScalarRepresentationAlong
    (σ : PaperKernel.Q ≃* PaperKernel.Q) :
    Representation k PaperKernel.Q k :=
  paperEllScalarRepresentation.comp σ

/--
The `paperEllInclusionIntertwiningAlong` construction used in the Connes rigidity formalization.
-/
def paperEllInclusionIntertwiningAlong
    (σ : PaperKernel.Q ≃* PaperKernel.Q) :
    Representation.IntertwiningMap
      (paperEllVStarRepresentationAlong σ)
      (paperEllRepresentationAlong σ) :=
  paperEllInclusionLinear.intertwiningMap_of_isIntertwiningMap
    (paperEllVStarRepresentationAlong σ)
    (paperEllRepresentationAlong σ) (by
      intro q f
      have h := Representation.IntertwiningMap.isIntertwining
        paperEllVStarRepresentation paperEllRepresentation
        paperEllInclusionIntertwining (σ q) f
      change paperEllInclusionLinear
          (paperEllVStarRepresentation (σ q) f) =
        (paperEllRepresentation (σ q))
          (paperEllInclusionLinear f) at h
      exact h)

/--
The `paperEllProjectionIntertwiningAlong` construction used in the Connes rigidity formalization.
-/
def paperEllProjectionIntertwiningAlong
    (σ : PaperKernel.Q ≃* PaperKernel.Q) :
    Representation.IntertwiningMap
      (paperEllRepresentationAlong σ)
      (paperEllScalarRepresentationAlong σ) :=
  paperEllProjectionLinear.intertwiningMap_of_isIntertwiningMap
    (paperEllRepresentationAlong σ)
    (paperEllScalarRepresentationAlong σ) (by
      intro q p
      have h := Representation.IntertwiningMap.isIntertwining
        paperEllRepresentation paperEllScalarRepresentation
        paperEllProjectionIntertwining (σ q) p
      change paperEllProjectionLinear
          (paperEllRepresentation (σ q) p) =
        (paperEllScalarRepresentation (σ q))
          (paperEllProjectionLinear p) at h
      exact h)

/--
The `paperEllInclusionAlong` construction used in the Connes rigidity formalization.
-/
def paperEllInclusionAlong
    (σ : PaperKernel.Q ≃* PaperKernel.Q) :
    (paperEllVStarRepresentationAlong σ).asModule →ₗ[Ring]
      (paperEllRepresentationAlong σ).asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule
    (paperEllVStarRepresentationAlong σ)
    (paperEllRepresentationAlong σ)).toFun
    (paperEllInclusionIntertwiningAlong σ)

/--
The `paperEllProjectionAlong` construction used in the Connes rigidity formalization.
-/
def paperEllProjectionAlong
    (σ : PaperKernel.Q ≃* PaperKernel.Q) :
    (paperEllRepresentationAlong σ).asModule →ₗ[Ring]
      (paperEllScalarRepresentationAlong σ).asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule
    (paperEllRepresentationAlong σ)
    (paperEllScalarRepresentationAlong σ)).toFun
    (paperEllProjectionIntertwiningAlong σ)

theorem paperEllProjectionAlong_surjective
    (σ : PaperKernel.Q ≃* PaperKernel.Q) :
    Function.Surjective (paperEllProjectionAlong σ) := by
  intro s
  refine ⟨(0, s), ?_⟩
  rfl

theorem paperEllExactAlong (σ : PaperKernel.Q ≃* PaperKernel.Q) :
    Function.Exact (paperEllInclusionAlong σ)
      (paperEllProjectionAlong σ) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · ext p
    rfl
  · intro p hp
    refine ⟨p.1, ?_⟩
    apply Prod.ext
    · rfl
    · change p.2 = 0 at hp
      exact hp.symm

theorem paperEllExtensionAlong_not_splits
    (σ : PaperKernel.Q ≃* PaperKernel.Q) :
    ¬ ∃ section_ : (paperEllScalarRepresentationAlong σ).asModule →ₗ[Ring]
        (paperEllRepresentationAlong σ).asModule,
      (paperEllProjectionAlong σ).comp section_ = LinearMap.id := by
  rintro ⟨section_, projection_section⟩
  refine finiteCocycle_not_linearCoboundary ?_
  let oneScalar : (paperEllScalarRepresentationAlong σ).asModule :=
    (paperEllScalarRepresentationAlong σ).asModuleEquiv.symm (1 : k)
  let lambda : PaperKernel.VStar :=
    ((paperEllRepresentationAlong σ).asModuleEquiv
      (section_ oneScalar)).1
  refine ⟨lambda, ?_⟩
  intro q v
  let q0 := σ.symm q
  have hq := section_.map_smul
    (MonoidAlgebra.of k PaperKernel.Q q0)
    oneScalar
  have hsource_fixed :
      (paperEllScalarRepresentationAlong σ).asModuleEquiv.symm
          ((paperEllScalarRepresentationAlong σ) q0 (1 : k)) = oneScalar := by
    simp [paperEllScalarRepresentationAlong,
      paperEllScalarRepresentation, oneScalar]
  have hqsource :
      (MonoidAlgebra.of k PaperKernel.Q q0) • oneScalar =
        (paperEllScalarRepresentationAlong σ).asModuleEquiv.symm
          ((paperEllScalarRepresentationAlong σ) q0 (1 : k)) := by
    change
      (MonoidAlgebra.of k PaperKernel.Q q0) •
        (paperEllScalarRepresentationAlong σ).asModuleEquiv.symm (1 : k) =
        (paperEllScalarRepresentationAlong σ).asModuleEquiv.symm
          ((paperEllScalarRepresentationAlong σ) q0 (1 : k))
    exact (Representation.asModuleEquiv_symm_map_rho
      (ρ := paperEllScalarRepresentationAlong σ) q0 (1 : k)).symm
  have hqcodomain :
      (MonoidAlgebra.of k PaperKernel.Q q0) • section_ oneScalar =
        (paperEllRepresentationAlong σ).asModuleEquiv.symm
          ((paperEllRepresentationAlong σ) q0
            ((paperEllRepresentationAlong σ).asModuleEquiv
              (section_ oneScalar))) := by
    exact
      (Representation.asModuleEquiv_symm_map_rho
        (ρ := paperEllRepresentationAlong σ) q0
          ((paperEllRepresentationAlong σ).asModuleEquiv
            (section_ oneScalar))).symm
  rw [hqsource, hsource_fixed, hqcodomain] at hq
  have hq' := congrArg (paperEllRepresentationAlong σ).asModuleEquiv hq
  rw [LinearEquiv.apply_symm_apply] at hq'
  have hfirst := congrArg Prod.fst hq'
  have hsection :=
    LinearMap.congr_fun projection_section oneScalar
  have hsection' :=
    congrArg (paperEllScalarRepresentationAlong σ).asModuleEquiv hsection
  change ((paperEllRepresentationAlong σ).asModuleEquiv
      (section_ oneScalar)).2 = 1 at hsection'
  have hxsecond :
      ((paperEllRepresentationAlong σ).asModuleEquiv
        (section_ oneScalar)).2 = 1 := by
    exact hsection'
  have hfirst' :
      lambda = qVStarActionHom (σ q0) lambda +
        ((paperEllRepresentationAlong σ).asModuleEquiv
          (section_ oneScalar)).2 •
          OpenAIPort.quadraticDefectLinear (σ q0) := by
    simpa [lambda, paperEllRepresentationAlong,
      paperEllRepresentation, paperEllMap] using hfirst
  rw [hxsecond, one_smul] at hfirst'
  have hquad :
      OpenAIPort.quadraticDefectLinear (σ q0) =
        qVStarActionHom (σ q0) lambda + lambda := by
    have hself : qVStarActionHom (σ q0) lambda +
        qVStarActionHom (σ q0) lambda = 0 := by
      rw [← two_smul k (qVStarActionHom (σ q0) lambda),
        show (2 : k) = 0 by rfl, zero_smul]
    calc
      OpenAIPort.quadraticDefectLinear (σ q0) =
          OpenAIPort.quadraticDefectLinear (σ q0) + 0 := (add_zero _).symm
      _ = OpenAIPort.quadraticDefectLinear (σ q0) +
          (qVStarActionHom (σ q0) lambda +
            qVStarActionHom (σ q0) lambda) := by rw [hself]
      _ = qVStarActionHom (σ q0) lambda +
          (qVStarActionHom (σ q0) lambda +
            OpenAIPort.quadraticDefectLinear (σ q0)) := by abel
      _ = qVStarActionHom (σ q0) lambda + lambda := by rw [← hfirst']
  change OpenAIPort.quadraticDefectLinear q v =
    lambda (q⁻¹ • v) + lambda v
  rw [show σ q0 = q from σ.apply_symm_apply q] at hquad
  have hv := congrArg (fun f : PaperKernel.VStar => f v) hquad
  change OpenAIPort.quadraticDefectLinear q v =
    (qVStarActionHom q lambda) v + lambda v at hv
  have hdual : (qVStarActionHom q lambda) v = lambda (q⁻¹ • v) := by
    rfl
  rw [hdual] at hv
  exact hv

theorem paperEllAlong_not_semisimple
    (σ : PaperKernel.Q ≃* PaperKernel.Q) :
    ¬ IsSemisimpleModule Ring
      (paperEllRepresentationAlong σ).asModule := by
  intro hE
  let _ : IsSemisimpleModule Ring
      (paperEllRepresentationAlong σ).asModule := hE
  obtain ⟨section_, hsection⟩ :=
    IsSemisimpleModule.lifting_property
      (M := (paperEllRepresentationAlong σ).asModule)
      (N := (paperEllScalarRepresentationAlong σ).asModule)
      (P := (paperEllScalarRepresentationAlong σ).asModule)
      (paperEllProjectionAlong σ) (paperEllProjectionAlong_surjective σ)
        (LinearMap.id :
          (paperEllScalarRepresentationAlong σ).asModule →ₗ[Ring]
          (paperEllScalarRepresentationAlong σ).asModule)
  apply paperEllExtensionAlong_not_splits σ
  refine ⟨section_, ?_⟩
  change paperEllProjectionAlong σ ∘ₗ section_ = LinearMap.id at hsection
  exact hsection

theorem paper_moduleTwoAlong_not_semisimple
    (σ : PaperKernel.Q ≃* PaperKernel.Q) :
    ¬ moduleTwoSemisimpleAlong σ := by
  intro h
  let _ : IsSemisimpleModule Ring
      (qRepresentationTwoAlong σ).asModule := h
  have hE : IsSemisimpleModule Ring
      (paperEllRepresentationAlong σ).asModule :=
    IsSemisimpleModule.of_injective (paperDTwoEmbeddingAlong σ)
      (paperDTwoEmbeddingAlong_injective σ)
  exact paperEllAlong_not_semisimple σ hE

end
end PaperNonisomorphism
end Connes
