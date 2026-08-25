/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Concrete §6 module obstruction for Zhou's nonsplit finite correction. The
extension is proved over the actual finite group algebra; the remaining
embedding into the full second kernel is handled in the companion action
file. The construction follows the paper's E_ell argument.
-/
import LeanPool.ConnesRigidity.Paper.Section6.Nonisomorphism
import Mathlib.Algebra.Exact.Basic

/-!
The nonisomorphism proofs component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperNonisomorphism

open Construction
open Construction.PaperKernel

noncomputable section

/--
The `PaperEll` construction used in the Connes rigidity formalization.
-/
abbrev PaperEll := PaperKernel.VStar × k

/--
The `paperEllMap` construction used in the Connes rigidity formalization.
-/
def paperEllMap (q : PaperKernel.Q) : PaperEll →ₗ[k] PaperEll where
  toFun p :=
    (qVStarActionHom q p.1 + p.2 • OpenAIPort.quadraticDefectLinear q, p.2)
  map_add' p r := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
      abel
    · rfl
  map_smul' a p := by
    apply Prod.ext
    · simp [smul_add, smul_smul]
    · simp

/--
The `paperEllRepresentation` construction used in the Connes rigidity formalization.
-/
def paperEllRepresentation : Representation k PaperKernel.Q PaperEll where
  toFun := paperEllMap
  map_one' := by
    have hq : OpenAIPort.quadraticDefectLinear (1 : PaperKernel.Q) = 0 := by
      apply LinearMap.ext
      intro v
      simp [OpenAIPort.quadraticDefectLinear, CharTwo.add_self_eq_zero]
    apply LinearMap.ext
    rintro ⟨f, s⟩
    apply Prod.ext
    · simp [paperEllMap, hq]
    · rfl
  map_mul' p q := by
    apply LinearMap.ext
    rintro ⟨f, s⟩
    apply Prod.ext
    · change qVStarActionHom (p * q) f +
          s • OpenAIPort.quadraticDefectLinear (p * q) =
        qVStarActionHom p
            (qVStarActionHom q f + s • OpenAIPort.quadraticDefectLinear q) +
          s • OpenAIPort.quadraticDefectLinear p
      rw [map_mul, PaperKernel.quadraticDefectLinear_cocycle]
      simp only [LinearEquiv.mul_apply, map_add, map_smul, smul_add]
      abel
    · rfl

/--
The `paperEllVStarRepresentation` construction used in the Connes rigidity formalization.
-/
def paperEllVStarRepresentation : Representation k PaperKernel.Q PaperKernel.VStar :=
  { toFun := fun q => (qVStarActionHom q).toLinearMap
    map_one' := by
      apply LinearMap.ext
      intro f
      exact congrArg (fun e : PaperKernel.VStar ≃ₗ[k] PaperKernel.VStar => e f)
        qVStarActionHom.map_one
    map_mul' := by
      intro p q
      apply LinearMap.ext
      intro f
      exact congrArg (fun e : PaperKernel.VStar ≃ₗ[k] PaperKernel.VStar => e f)
        (qVStarActionHom.map_mul p q) }

/--
The `paperEllScalarRepresentation` construction used in the Connes rigidity formalization.
-/
def paperEllScalarRepresentation : Representation k PaperKernel.Q k :=
  Representation.trivial k PaperKernel.Q k

/--
The `paperEllInclusionLinear` construction used in the Connes rigidity formalization.
-/
def paperEllInclusionLinear : PaperKernel.VStar →ₗ[k] PaperEll where
  toFun f := (f, 0)
  map_add' f g := by simp
  map_smul' a f := by simp

/--
The `paperEllInclusionIntertwining` construction used in the Connes rigidity formalization.
-/
def paperEllInclusionIntertwining :
    Representation.IntertwiningMap paperEllVStarRepresentation paperEllRepresentation :=
  paperEllInclusionLinear.intertwiningMap_of_isIntertwiningMap
    paperEllVStarRepresentation paperEllRepresentation (by
      intro q f
      apply Prod.ext
      · simp [paperEllInclusionLinear, paperEllVStarRepresentation,
          paperEllRepresentation, paperEllMap]
      · rfl)

/--
The `paperEllProjectionLinear` construction used in the Connes rigidity formalization.
-/
def paperEllProjectionLinear : PaperEll →ₗ[k] k where
  toFun p := p.2
  map_add' p q := by simp
  map_smul' a p := by simp

/--
The `paperEllProjectionIntertwining` construction used in the Connes rigidity formalization.
-/
def paperEllProjectionIntertwining :
    Representation.IntertwiningMap paperEllRepresentation paperEllScalarRepresentation :=
  paperEllProjectionLinear.intertwiningMap_of_isIntertwiningMap
    paperEllRepresentation paperEllScalarRepresentation (by
      intro q p
      rfl)

/--
The `paperEllInclusion` construction used in the Connes rigidity formalization.
-/
def paperEllInclusion :
    paperEllVStarRepresentation.asModule →ₗ[Ring]
      paperEllRepresentation.asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule
    paperEllVStarRepresentation paperEllRepresentation).toFun paperEllInclusionIntertwining

/--
The `paperEllProjection` construction used in the Connes rigidity formalization.
-/
def paperEllProjection :
    paperEllRepresentation.asModule →ₗ[Ring]
      paperEllScalarRepresentation.asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule
    paperEllRepresentation paperEllScalarRepresentation).toFun paperEllProjectionIntertwining

theorem paperEll_projection_surjective : Function.Surjective paperEllProjection := by
  intro s
  refine ⟨(0, s), ?_⟩
  rfl

theorem paperEll_exact : Function.Exact paperEllInclusion paperEllProjection := by
  apply LinearMap.exact_of_comp_of_mem_range
  · ext p
    rfl
  · intro p hp
    refine ⟨p.1, ?_⟩
    apply Prod.ext
    · rfl
    · change p.2 = 0 at hp
      exact hp.symm

theorem paperEll_extension_not_splits :
    ¬ ∃ section_ : paperEllScalarRepresentation.asModule →ₗ[Ring]
        paperEllRepresentation.asModule,
      paperEllProjection.comp section_ = LinearMap.id := by
  rintro ⟨section_, projection_section⟩
  refine finiteCocycle_not_linearCoboundary ?_
  let oneScalar : paperEllScalarRepresentation.asModule :=
    paperEllScalarRepresentation.asModuleEquiv.symm (1 : k)
  let lambda : PaperKernel.VStar :=
    (paperEllRepresentation.asModuleEquiv
      (section_ oneScalar)).1
  refine ⟨lambda, ?_⟩
  intro q v
  have hq := section_.map_smul
    (MonoidAlgebra.of k PaperKernel.Q q)
    oneScalar
  have hsource_fixed :
      paperEllScalarRepresentation.asModuleEquiv.symm
          (paperEllScalarRepresentation q (1 : k)) = oneScalar := by
    simp [paperEllScalarRepresentation, oneScalar]
  have hqsource :
      (MonoidAlgebra.of k PaperKernel.Q q) • oneScalar =
        paperEllScalarRepresentation.asModuleEquiv.symm
          (paperEllScalarRepresentation q (1 : k)) := by
    change
      (MonoidAlgebra.of k PaperKernel.Q q) •
          paperEllScalarRepresentation.asModuleEquiv.symm (1 : k) =
        paperEllScalarRepresentation.asModuleEquiv.symm
          (paperEllScalarRepresentation q (1 : k))
    exact (Representation.asModuleEquiv_symm_map_rho
      (ρ := paperEllScalarRepresentation) q (1 : k)).symm
  have hqcodomain :
      (MonoidAlgebra.of k PaperKernel.Q q) • section_ oneScalar =
        paperEllRepresentation.asModuleEquiv.symm
          (paperEllRepresentation q
            (paperEllRepresentation.asModuleEquiv (section_ oneScalar))) := by
    exact
      (Representation.asModuleEquiv_symm_map_rho
        (ρ := paperEllRepresentation) q
          (paperEllRepresentation.asModuleEquiv (section_ oneScalar))).symm
  rw [hqsource, hsource_fixed, hqcodomain] at hq
  have hq' := congrArg paperEllRepresentation.asModuleEquiv hq
  rw [LinearEquiv.apply_symm_apply] at hq'
  have hfirst := congrArg Prod.fst hq'
  have hsection :=
    LinearMap.congr_fun projection_section oneScalar
  have hsection' :=
    congrArg paperEllScalarRepresentation.asModuleEquiv hsection
  change (paperEllRepresentation.asModuleEquiv
      (section_ oneScalar)).2 = 1 at hsection'
  have hxsecond :
      (paperEllRepresentation.asModuleEquiv (section_ oneScalar)).2 = 1 := by
    exact hsection'
  have hfirst' :
      lambda = qVStarActionHom q lambda +
        (paperEllRepresentation.asModuleEquiv
          (section_ oneScalar)).2 •
          OpenAIPort.quadraticDefectLinear q := by
    simpa [lambda, paperEllRepresentation, paperEllMap] using hfirst
  rw [hxsecond, one_smul] at hfirst'
  have hquad :
      OpenAIPort.quadraticDefectLinear q =
        qVStarActionHom q lambda + lambda := by
    have hself :
        qVStarActionHom q lambda + qVStarActionHom q lambda = 0 := by
      rw [← two_smul k (qVStarActionHom q lambda),
        show (2 : k) = 0 by rfl, zero_smul]
    calc
      OpenAIPort.quadraticDefectLinear q =
          OpenAIPort.quadraticDefectLinear q + 0 := (add_zero _).symm
      _ = OpenAIPort.quadraticDefectLinear q +
          (qVStarActionHom q lambda + qVStarActionHom q lambda) := by
            rw [hself]
      _ = qVStarActionHom q lambda +
          (qVStarActionHom q lambda +
            OpenAIPort.quadraticDefectLinear q) := by abel
      _ = qVStarActionHom q lambda + lambda := by rw [← hfirst']
  change OpenAIPort.quadraticDefectLinear q v =
    lambda (q⁻¹ • v) + lambda v
  rw [hquad]
  rfl

theorem paperEll_not_semisimple :
    ¬ IsSemisimpleModule Ring paperEllRepresentation.asModule := by
  intro hE
  let _ : IsSemisimpleModule Ring paperEllRepresentation.asModule := hE
  obtain ⟨section_, hsection⟩ :=
    IsSemisimpleModule.lifting_property
      (M := paperEllRepresentation.asModule)
      (N := paperEllScalarRepresentation.asModule)
      (P := paperEllScalarRepresentation.asModule)
      paperEllProjection paperEll_projection_surjective
        (LinearMap.id : paperEllScalarRepresentation.asModule →ₗ[Ring]
          paperEllScalarRepresentation.asModule)
  apply paperEll_extension_not_splits
  refine ⟨section_, ?_⟩
  change paperEllProjection ∘ₗ section_ = LinearMap.id at hsection
  exact hsection

end
end PaperNonisomorphism
end Connes
