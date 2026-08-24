/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Concrete semisimplicity of the first quotient module in Zhou §6.
The proof decomposes the actual action into the tensor summand and the
trivial `C` summand, rather than treating the paper input as an opaque field.
-/
import Mathlib.Data.FunLike.Fintype
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.PicardGroup
import LeanPool.ConnesRigidity.Paper.Section6.Nonisomorphism

/-!
The module semisimple component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperModuleSemisimple

open Construction
open Construction.PaperKernel
open PaperNonisomorphism

noncomputable section

/--
The `Q` construction used in the Connes rigidity formalization.
-/
abbrev Q := PaperKernel.Q
/--
The `W` construction used in the Connes rigidity formalization.
-/
abbrev W := PaperKernel.VStar

/- The symplectic pairing identifies the finite dual with the defining module. Paper: §6.
-/
/--
The `pairing` construction used in the Connes rigidity formalization.
-/
def pairing : PaperV →ₗ[k] W where
  toFun := OpenAIPort.symplecticFunctional
  map_add' d e := by
    apply LinearMap.ext
    intro v
    simp [OpenAIPort.symplecticFunctional,
      OpenAIPort.modTwoSymplecticForm_add_left]
  map_smul' a d := by
    apply LinearMap.ext
    intro v
    simp [OpenAIPort.symplecticFunctional, OpenAIPort.modTwoSymplecticForm]
    ring

/-- The symplectic pairing has trivial kernel. Paper: §6. -/
theorem pairing_injective : Function.Injective pairing := by
  intro d e h
  apply OpenAIPort.modTwoSymplecticForm_nondegenerate
  intro v
  exact congrArg (fun f : W => f v) h

/- Equal finite dimensions turn the pairing injection into an equivalence. Paper: §6. -/
theorem pairing_surjective : Function.Surjective pairing := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank k PaperV = Module.finrank k W by
      rw [Subspace.dual_finrank_eq])).mp
  exact pairing_injective

/- The pairing intertwines the quotient action. Paper: §6. -/
theorem pairing_smul (q : Q) (d : PaperV) :
    qVStarActionHom q (pairing d) = pairing (q • d) := by
  apply LinearMap.ext
  intro v
  change OpenAIPort.modTwoSymplecticForm d (q⁻¹ • v) =
    OpenAIPort.modTwoSymplecticForm (q • d) v
  rw [OpenAIPort.modTwoSymplecticForm_smul_left]

/- The finite quotient acts transitively on nonzero vectors. Paper: §6. -/
theorem qV_transitive_on_nonzero_test :
    ∀ v : PaperV, v ≠ 0 → ∀ w : PaperV, w ≠ 0 → ∃ q : Q,
      q • v = w := by
  exact Sp4.transitive_on_nonzero_vectors

/- The finite dual quotient action is transitive on nonzero functionals. Paper: §6. -/
theorem qVStar_transitive_on_nonzero_test :
    ∀ f : W, f ≠ 0 → ∀ g : W, g ≠ 0 → ∃ q : Q,
      qVStarActionHom q f = g := by
  intro f hf g hg
  obtain ⟨d, rfl⟩ := pairing_surjective f
  obtain ⟨e, heq⟩ := pairing_surjective g
  have hd : d ≠ 0 := by
    intro hd
    apply hf
    rw [hd]
    exact map_zero pairing
  have he : e ≠ 0 := by
    intro he
    apply hg
    calc
      g = pairing e := heq.symm
      _ = pairing 0 := by rw [he]
      _ = 0 := map_zero pairing
  obtain ⟨q, hq⟩ := qV_transitive_on_nonzero_test d hd e he
  refine ⟨q, ?_⟩
  rw [pairing_smul, hq, heq]

/- The finite dual action is packaged as a group representation. Paper: §6.
-/
/--
The `qVStarRepresentation` construction used in the Connes rigidity formalization.
-/
def qVStarRepresentation : Representation k Q W where
  toFun q := (qVStarActionHom q).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro f
    change qVStarActionHom 1 f = f
    exact congrArg (fun e : W ≃ₗ[k] W => e f)
      (qVStarActionHom.map_one)
  map_mul' p q := by
    apply LinearMap.ext
    intro f
    change qVStarActionHom (p * q) f =
      qVStarActionHom p (qVStarActionHom q f)
    exact congrArg (fun e : W ≃ₗ[k] W => e f)
      (qVStarActionHom.map_mul p q)

/-- The finite dual representation is nontrivial. Paper: §6. -/
theorem qVStar_nontrivial : Nontrivial W := by
  let d : PaperV := OpenAIPort.modTwoBasis (Sum.inl 0)
  have hd : d ≠ 0 := by
    intro h
    have h0 := congr_fun h (Sum.inl 0)
    simp [d, OpenAIPort.modTwoBasis] at h0
  have hpd : pairing d ≠ 0 := by
    intro h
    apply hd
    apply pairing_injective
    simpa using h
  exact ⟨⟨0, pairing d, hpd.symm⟩⟩

/- Transitivity makes the finite dual representation simple. Paper: §6. -/
theorem qVStar_simple : IsSimpleModule Ring qVStarRepresentation.asModule := by
  apply (isSimpleModule_iff_toSpanSingleton_surjective
    (R := Ring) (M := qVStarRepresentation.asModule)).2
  refine ⟨qVStar_nontrivial, ?_⟩
  intro f hf g
  by_cases hg : g = 0
  · exact ⟨0, by simp [hg]⟩
  · obtain ⟨q, hq⟩ := qVStar_transitive_on_nonzero_test f hf g hg
    refine ⟨MonoidAlgebra.of k Q q, ?_⟩
    change (MonoidAlgebra.of k Q q) •
        qVStarRepresentation.asModuleEquiv.symm f =
      qVStarRepresentation.asModuleEquiv.symm g
    rw [← qVStarRepresentation.asModuleEquiv_symm_map_rho q f]
    exact congrArg qVStarRepresentation.asModuleEquiv.symm hq

/--
The `I` construction used in the Connes rigidity formalization.
-/
abbrev I := PaperKernel.OrderedBasisIndex
/--
The `AV` construction used in the Connes rigidity formalization.
-/
abbrev AV := PaperKernel.AVStar
/--
The `DS` construction used in the Connes rigidity formalization.
-/
abbrev DS := DirectSum I (fun _ => W)

/- The quotient action on `AVStar` is recorded as a representation. Paper: §6.
-/
/--
The `avStarActionQEquivHom` construction used in the Connes rigidity formalization.
-/
def avStarActionQEquivHom : Q →* (AV ≃ₗ[k] AV) :=
  PaperKernel.avStarActionHom.comp qToH

/-- The tensor summand carries the actual quotient action. Paper: §6.
-/
def avStarRepresentation : Representation k Q AV :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    avStarActionQEquivHom

/-- The direct sum of copies of the finite dual representation is explicit. Paper: §6.
-/
def directSumRepresentation : Representation k Q DS :=
  Representation.directSum (fun _ : I => qVStarRepresentation)

/-- The direct sum is identified with its finitely supported coordinate model. Paper: §6.
-/
noncomputable def directSumFinsuppEquiv :
    (I →₀ qVStarRepresentation.asModule) ≃ₗ[k] DS := by
  classical
  let _ : ∀ m : qVStarRepresentation.asModule, Decidable (m ≠ 0) :=
    fun m => Classical.propDecidable (m ≠ 0)
  exact finsuppLequivDFinsupp k

/-- The ordered tensor basis identifies `AVStar` with the direct sum coordinates. Paper: §6.
-/
def tensorDirectSumEquiv : AV ≃ₗ[k] DS :=
  (TensorProduct.equivFinsuppOfBasisLeft
      (M := Construction.A) (N := PaperKernel.VStar) PaperKernel.orderedBasis).trans
    (finsuppLequivDFinsupp k)

/-- The tensor coordinate equivalence respects the quotient representations. Paper: §6. -/
theorem tensorDirectSumEquiv_intertwines (q : Q) (x : AV) :
    tensorDirectSumEquiv (avStarRepresentation q x) =
      directSumRepresentation q (tensorDirectSumEquiv x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [tensorDirectSumEquiv, avStarRepresentation,
      directSumRepresentation]
  · intro a f
    apply DirectSum.ext
    intro i
    change
      (TensorProduct.equivFinsuppOfBasisLeft
          (M := Construction.A) (N := PaperKernel.VStar)
          PaperKernel.orderedBasis
          (PaperKernel.avStarAction (1 : SpecialLinear.SL3) q (a ⊗ₜ[k] f))) i =
        qVStarActionHom q
          ((TensorProduct.equivFinsuppOfBasisLeft
            (M := Construction.A) (N := PaperKernel.VStar)
            PaperKernel.orderedBasis (a ⊗ₜ[k] f)) i)
    simp [PaperKernel.avStarAction]
  · intro x y hx hy
    simp only [map_add, hx, hy]

/- The tensor equivalence becomes a group-algebra linear map. Paper: §6.
-/
/--
The `tensorDirectSumEquivRep` construction used in the Connes rigidity formalization.
-/
def tensorDirectSumEquivRep :
    Representation.IntertwiningMap avStarRepresentation directSumRepresentation :=
  tensorDirectSumEquiv.intertwiningMap_of_isIntertwiningMap
    avStarRepresentation directSumRepresentation tensorDirectSumEquiv_intertwines

/-- The direct sum action and its pointwise finitely supported action agree. Paper: §6.
-/
def directSumPointwiseEquiv :
    directSumRepresentation.asModule ≃ₗ[Ring]
      (I →₀ qVStarRepresentation.asModule) where
  toFun x := directSumFinsuppEquiv.symm
    (directSumRepresentation.asModuleEquiv x)
  invFun x := directSumRepresentation.asModuleEquiv.symm
    (directSumFinsuppEquiv x)
  left_inv x := by
    exact directSumRepresentation.asModuleEquiv.injective
      (directSumFinsuppEquiv.apply_symm_apply _)
  right_inv x := by
    change directSumFinsuppEquiv.symm
      (directSumRepresentation.asModuleEquiv
        (directSumRepresentation.asModuleEquiv.symm
          (directSumFinsuppEquiv x))) = x
    rw [directSumRepresentation.asModuleEquiv.apply_symm_apply,
      directSumFinsuppEquiv.symm_apply_apply]
  map_add' x y := by
    simp only [directSumRepresentation.asModuleEquiv.map_add,
      directSumFinsuppEquiv.symm.map_add]
  map_smul' r x := by
    classical
    let _ : ∀ m : qVStarRepresentation.asModule, Decidable (m ≠ 0) :=
      fun m => Classical.propDecidable (m ≠ 0)
    induction r using MonoidAlgebra.induction_linear with
    | zero =>
        simp only [zero_smul, RingHom.id_apply,
          directSumRepresentation.asModuleEquiv.map_zero,
          directSumFinsuppEquiv.symm.map_zero]
    | add a b ha hb =>
        simp only [RingHom.id_apply]
        rw [add_smul, directSumRepresentation.asModuleEquiv.map_add,
          directSumFinsuppEquiv.symm.map_add, add_smul, ha, hb]
        simp only [RingHom.id_apply]
    | single g a =>
        ext i
        have hcoord (y : DS) : directSumFinsuppEquiv.symm y i = y i := by
          rfl
        change directSumFinsuppEquiv.symm
            (directSumRepresentation.asModuleEquiv
              (MonoidAlgebra.single g a • x)) i =
          (MonoidAlgebra.single g a) •
            (directSumFinsuppEquiv.symm
              (directSumRepresentation.asModuleEquiv x)) i
        rw [hcoord, Representation.asModuleEquiv_map_smul,
          Representation.asAlgebraHom_single]
        have hsingle (v : qVStarRepresentation.asModule) :
            (MonoidAlgebra.single g a) • v =
              a • qVStarRepresentation g v := by
          apply qVStarRepresentation.asModuleEquiv.injective
          rw [Representation.asModuleEquiv_map_smul,
            Representation.asAlgebraHom_single]
          rfl
        rw [hsingle]
        change a • qVStarRepresentation g
            (directSumRepresentation.asModuleEquiv x i) =
          a • qVStarRepresentation g
            (directSumRepresentation.asModuleEquiv x i)
        rfl

/-- The tensor summand is semisimple over the finite group algebra. Paper: §6. -/
theorem avStar_semisimple :
    IsSemisimpleModule Ring avStarRepresentation.asModule := by
  let _ : AddCommGroup avStarRepresentation.asModule :=
    inferInstanceAs (AddCommGroup AV)
  let _ : AddCommGroup directSumRepresentation.asModule :=
    inferInstanceAs (AddCommGroup DS)
  let _ : IsSimpleModule Ring qVStarRepresentation.asModule := qVStar_simple
  let _ : ∀ _ : I, IsSemisimpleModule Ring qVStarRepresentation.asModule :=
    fun _ => inferInstance
  let _ : IsSemisimpleModule Ring (I →₀ qVStarRepresentation.asModule) := by
    infer_instance
  have hDS : IsSemisimpleModule Ring directSumRepresentation.asModule :=
    IsSemisimpleModule.congr directSumPointwiseEquiv
  let f : avStarRepresentation.asModule →ₗ[Ring]
      directSumRepresentation.asModule :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      avStarRepresentation directSumRepresentation).toFun
      tensorDirectSumEquivRep
  have hf : Function.Bijective f := by
    change Function.Bijective tensorDirectSumEquiv
    exact tensorDirectSumEquiv.bijective
  exact (LinearMap.isSemisimpleModule_iff_of_bijective (l := f) hf).mpr hDS

/- The one-dimensional trivial quotient representation is simple. Paper: §6.
-/
/--
The `scalarRepresentation` construction used in the Connes rigidity formalization.
-/
def scalarRepresentation : Representation k Q k :=
  Representation.trivial k Q k

/-- The trivial scalar module is simple over the group algebra. Paper: §6. -/
theorem scalar_simple : IsSimpleModule Ring scalarRepresentation.asModule := by
  apply (isSimpleModule_iff_toSpanSingleton_surjective
    (R := Ring) (M := scalarRepresentation.asModule)).2
  refine ⟨?_, ?_⟩
  · refine ⟨⟨0, scalarRepresentation.asModuleEquiv.symm 1, ?_⟩⟩
    intro h
    have h' := congrArg scalarRepresentation.asModuleEquiv h
    simp at h'
  · intro x hx y
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy]⟩
    · refine ⟨algebraMap k Ring
          (scalarRepresentation.asModuleEquiv y /
            scalarRepresentation.asModuleEquiv x), ?_⟩
      change algebraMap k Ring
          (scalarRepresentation.asModuleEquiv y /
            scalarRepresentation.asModuleEquiv x) •
          scalarRepresentation.asModuleEquiv.symm
            (scalarRepresentation.asModuleEquiv x) =
        scalarRepresentation.asModuleEquiv.symm
          (scalarRepresentation.asModuleEquiv y)
      rw [← Representation.asModuleEquiv_symm_map_smul]
      change (scalarRepresentation.asModuleEquiv y /
        scalarRepresentation.asModuleEquiv x) •
          scalarRepresentation.asModuleEquiv x =
        scalarRepresentation.asModuleEquiv y
      have hx' : scalarRepresentation.asModuleEquiv x ≠ 0 := by
        intro h
        apply hx
        apply scalarRepresentation.asModuleEquiv.injective
        simp [h]
      rw [smul_eq_mul]
      field_simp [hx']

/--
The `CI` construction used in the Connes rigidity formalization.
-/
abbrev CI := Module.Free.ChooseBasisIndex k PaperKernel.C

/- A free basis turns the trivial `C` summand into coordinate copies. Paper: §6.
-/
/--
The `cBasis` construction used in the Connes rigidity formalization.
-/
noncomputable def cBasis : Module.Basis CI k PaperKernel.C :=
  Module.Free.chooseBasis k PaperKernel.C

/-- The quotient action on `C` is trivial in the first module. Paper: §6.
-/
def cRepresentation : Representation k Q PaperKernel.C :=
  Representation.trivial k Q PaperKernel.C

/-- The coordinate representation on the `C` basis is trivial. Paper: §6.
-/
def cFinsuppRepresentation : Representation k Q (CI →₀ k) :=
  Representation.trivial k Q (CI →₀ k)

/-- The coordinate copies form a semisimple module. Paper: §6. -/
theorem cFinsupp_pointwise_semisimple :
    IsSemisimpleModule Ring (CI →₀ scalarRepresentation.asModule) := by
  let _ : IsSimpleModule Ring scalarRepresentation.asModule := scalar_simple
  infer_instance

/- The coordinate type-synonym modules are linearly equivalent over the group algebra. Paper: §6.
-/
/--
The `cPointwiseEquiv` construction used in the Connes rigidity formalization.
-/
def cPointwiseEquiv :
    cFinsuppRepresentation.asModule ≃ₗ[Ring]
      (CI →₀ scalarRepresentation.asModule) where
  toFun x := x
  invFun x := x
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' r x := by
    induction r using MonoidAlgebra.induction_linear with
    | zero =>
        ext i
        rfl
    | add a b ha hb =>
        simp only [RingHom.id_apply, add_smul, ha, hb]
        exact (@add_smul Ring (CI →₀ scalarRepresentation.asModule)
          _ _ _ a b
          (x : CI →₀ scalarRepresentation.asModule)).symm
    | single q a =>
        ext i
        change scalarRepresentation.asModuleEquiv.symm
            ((cFinsuppRepresentation.asModuleEquiv
              ((MonoidAlgebra.single q a) • x)) i) =
          (MonoidAlgebra.single q a) •
            scalarRepresentation.asModuleEquiv.symm
              ((cFinsuppRepresentation.asModuleEquiv x) i)
        apply scalarRepresentation.asModuleEquiv.injective
        simp only [scalarRepresentation.asModuleEquiv.apply_symm_apply]
        rw [Representation.asModuleEquiv_map_smul scalarRepresentation,
          Representation.asAlgebraHom_single scalarRepresentation]
        rw [Representation.asModuleEquiv_map_smul cFinsuppRepresentation,
          Representation.asAlgebraHom_single cFinsuppRepresentation]
        rw [scalarRepresentation.asModuleEquiv.apply_symm_apply]
        simp [cFinsuppRepresentation, scalarRepresentation]

/-- The trivial coordinate representation is semisimple. Paper: §6. -/
theorem cFinsupp_semisimple :
    IsSemisimpleModule Ring cFinsuppRepresentation.asModule := by
  let _ : IsSemisimpleModule Ring
      (CI →₀ scalarRepresentation.asModule) :=
    cFinsupp_pointwise_semisimple
  exact IsSemisimpleModule.congr cPointwiseEquiv

/- The `C` summand is semisimple by transport through its chosen basis. Paper: §6.
-/
/--
The `cBasisIntertwining` construction used in the Connes rigidity formalization.
-/
def cBasisIntertwining :
    Representation.IntertwiningMap cRepresentation cFinsuppRepresentation :=
  cBasis.repr.intertwiningMap_of_isIntertwiningMap
    cRepresentation cFinsuppRepresentation (by
      intro q c
      simp [cRepresentation, cFinsuppRepresentation])

/-- The actual trivial `C` representation is semisimple. Paper: §6. -/
theorem cRepresentation_semisimple :
    IsSemisimpleModule Ring cRepresentation.asModule := by
  let f : cRepresentation.asModule →ₗ[Ring]
      cFinsuppRepresentation.asModule :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      cRepresentation cFinsuppRepresentation).toFun cBasisIntertwining
  have hf : Function.Bijective f := by
    change Function.Bijective cBasis.repr
    exact cBasis.repr.bijective
  exact (LinearMap.isSemisimpleModule_iff_of_bijective (l := f) hf).mpr
    cFinsupp_semisimple

/- The first quotient representation is the product of the tensor and `C` actions. Paper: §6.
-/
/--
The `firstProductRepresentation` construction used in the Connes rigidity formalization.
-/
def firstProductRepresentation : Representation k Q (AV × PaperKernel.C) :=
  avStarRepresentation.prod cRepresentation

/-- The tensor summand embeds as a group-algebra submodule of the product. Paper: §6.
-/
def firstProductInl : avStarRepresentation.asModule →ₗ[Ring]
    firstProductRepresentation.asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule
    avStarRepresentation firstProductRepresentation).toFun
    (Representation.IntertwiningMap.inl k avStarRepresentation cRepresentation)

/-- The `C` summand embeds as a group-algebra submodule of the product. Paper: §6.
-/
def firstProductInr : cRepresentation.asModule →ₗ[Ring]
    firstProductRepresentation.asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule
    cRepresentation firstProductRepresentation).toFun
    (Representation.IntertwiningMap.inr k avStarRepresentation cRepresentation)

@[simp] theorem firstProductInl_apply (x : avStarRepresentation.asModule) :
    firstProductInl x = (x, 0) := rfl

@[simp] theorem firstProductInr_apply (x : cRepresentation.asModule) :
    firstProductInr x = (0, x) := rfl

/- The concrete first quotient module is semisimple. Paper: §6. -/
theorem firstProduct_semisimple :
    IsSemisimpleModule Ring firstProductRepresentation.asModule := by
  let _ : AddCommGroup avStarRepresentation.asModule :=
    inferInstanceAs (AddCommGroup AV)
  let _ : AddCommGroup cRepresentation.asModule :=
    inferInstanceAs (AddCommGroup PaperKernel.C)
  let _ : AddCommGroup firstProductRepresentation.asModule :=
    inferInstanceAs (AddCommGroup (AV × PaperKernel.C))
  let _ : IsSemisimpleModule Ring avStarRepresentation.asModule := avStar_semisimple
  let _ : IsSemisimpleModule Ring cRepresentation.asModule :=
    cRepresentation_semisimple
  apply isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun b : Bool => match b with
      | false => LinearMap.range firstProductInl
      | true => LinearMap.range firstProductInr)
  · intro b
    cases b with
    | false =>
        exact IsSemisimpleModule.range firstProductInl
    | true =>
        exact IsSemisimpleModule.range firstProductInr
  · rw [iSup_bool_eq]
    change LinearMap.range firstProductInr ⊔
      LinearMap.range firstProductInl = ⊤
    apply top_unique
    rintro ⟨u, c⟩ -
    have hu : (u, 0) ∈ LinearMap.range firstProductInl :=
      ⟨u, rfl⟩
    have hc : (0, c) ∈ LinearMap.range firstProductInr :=
      ⟨c, rfl⟩
    have hc' : (0, c) ∈
        LinearMap.range firstProductInr ⊔ LinearMap.range firstProductInl :=
      (show LinearMap.range firstProductInr ≤
          LinearMap.range firstProductInr ⊔ LinearMap.range firstProductInl
        from le_sup_left) hc
    have hu' : (u, 0) ∈
        LinearMap.range firstProductInr ⊔ LinearMap.range firstProductInl :=
      (show LinearMap.range firstProductInl ≤
          LinearMap.range firstProductInr ⊔ LinearMap.range firstProductInl
        from le_sup_right) hu
    have hadd := Submodule.add_mem _ hc' hu'
    rw [show (u, c) = (0, c) + (u, 0) by ext <;> simp [add_comm]]
    exact hadd

end
end PaperModuleSemisimple
end Connes
