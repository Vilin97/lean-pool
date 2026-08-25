/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Construction.PaperActionInstances
import LeanPool.ConnesRigidity.Construction.SquareSpan
import LeanPool.ConnesRigidity.Paper.Section5.ICC

/-!
Concrete orbit and displacement proofs for Zhou's semidirect products. The
finite quotient detector is checked by kernel computation over the public
finite carrier. Paper: §5.
-/

namespace Connes
namespace PaperICC

open Construction
open Construction.PaperKernel

noncomputable section

/-- Coordinate basis for the finite symplectic module. Paper: §2. -/
noncomputable def paperVBasis : Module.Basis PaperKernel.SymplecticIndex
    k PaperKernel.PaperV :=
  Pi.basisFun k PaperKernel.SymplecticIndex

/-- Dual coordinate basis for the finite symplectic module. Paper: §2. -/
noncomputable def paperVStarBasis : Module.Basis PaperKernel.SymplecticIndex
    k PaperKernel.VStar :=
  paperVBasis.dualBasis

lemma paper_avStar_coeff_sl3 (s : SpecialLinear.SL3) (u : PaperKernel.AVStar)
    (i : PaperKernel.SymplecticIndex) :
    (TensorProduct.equivFinsuppOfBasisRight paperVStarBasis
      (avStarAction s (1 : PaperKernel.Q) u)) i =
      sl3AAction s
        ((TensorProduct.equivFinsuppOfBasisRight paperVStarBasis u) i) := by
  refine TensorProduct.induction_on u ?_ ?_ ?_
  · simp
  · intro a f
    simp [avStarAction, paperVStarBasis]
  · intro x y hx hy
    simp only [map_add, hx, hy, Finsupp.add_apply]

lemma paper_avStar_coeff_exists (u : PaperKernel.AVStar) (hu : u ≠ 0) :
    ∃ i : PaperKernel.SymplecticIndex,
      (TensorProduct.equivFinsuppOfBasisRight paperVStarBasis u) i ≠ 0 := by
  let e : PaperKernel.AVStar ≃ₗ[k]
      (PaperKernel.SymplecticIndex →₀ A) :=
    TensorProduct.equivFinsuppOfBasisRight paperVStarBasis
  have he : e u ≠ 0 := by
    intro hzero
    apply hu
    exact (e.map_eq_zero_iff).mp hzero
  by_contra h
  apply he
  apply Finsupp.ext
  intro i
  simpa [e] using not_ne_iff.mp (not_exists.mp h i)

lemma paper_ordered_coord_transvection_invariant
    {p : PaperKernel.OrderedBasisIndex}
    {i j : Fin 3} (hij : i ≠ j)
    (hr : i ≠ (ofLex p).1)
    (a : SpecialLinear.R) (x : A) :
    orderedBasis.coord p
        (sl3AAction (Matrix.SpecialLinearGroup.transvection hij a) x) =
      Construction.PaperKernel.orderedBasis.coord p x := by
  let ij := ofLex p
  have hp : p = toLex ij :=
    (toLex.apply_symm_apply p).symm
  have hr' : i ≠ ij.1 := by simpa [ij] using hr
  rw [hp]
  rcases ij with ⟨r, n⟩
  change i ≠ r at hr'
  have hmap : Function.Injective
      (toLex ∘ ⇑(Equiv.sigmaEquivProd (Fin 3) ℕ)) :=
    toLex.injective.comp (Equiv.sigmaEquivProd (Fin 3) ℕ).injective
  simp only [orderedBasis, Module.Basis.coord_apply,
    Module.Basis.repr_reindex_apply]
  simp only [Pi.basis_repr]
  simp only [Equiv.symm_trans_apply, Equiv.symm_apply_apply,
    Equiv.sigmaEquivProd_symm_apply]
  have hrow : sl3AAction
      (Matrix.SpecialLinearGroup.transvection hij a) x r = x r :=
    transvection_action_apply_of_ne_target hij (Ne.symm hr') a x
  rw [hrow]

lemma paper_A_transvection_injective {i j : Fin 3} (hij : i ≠ j)
    (x : A) (hj : x j ≠ 0) :
    Function.Injective (fun a : SpecialLinear.R =>
      sl3AAction (Matrix.SpecialLinearGroup.transvection hij a) x) := by
  intro a b hab
  have hcoord := congrArg (fun y : A => y i) hab
  change sl3AAction (Matrix.SpecialLinearGroup.transvection hij a) x i =
    sl3AAction (Matrix.SpecialLinearGroup.transvection hij b) x i at hcoord
  rw [transvection_action_apply_target hij a x,
    transvection_action_apply_target hij b x] at hcoord
  exact mul_right_cancel₀ hj (add_left_cancel hcoord)

lemma paper_A_transvection_injective_avoiding (x : A) (hx : x ≠ 0)
    (r : Fin 3) :
    ∃ (i j : Fin 3) (hij : i ≠ j), i ≠ r ∧
      Function.Injective (fun a : SpecialLinear.R =>
        sl3AAction (Matrix.SpecialLinearGroup.transvection hij a) x) := by
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, x j ≠ 0 := by
    by_contra h
    apply hx
    funext j
    exact not_ne_iff.mp (not_exists.mp h j)
  fin_cases j <;> fin_cases r
  all_goals first
  | exact ⟨1, 0, by decide, by decide,
      paper_A_transvection_injective (i := 1) (j := 0) (by decide) x hj⟩
  | exact ⟨2, 0, by decide, by decide,
      paper_A_transvection_injective (i := 2) (j := 0) (by decide) x hj⟩
  | exact ⟨2, 1, by decide, by decide,
      paper_A_transvection_injective (i := 2) (j := 1) (by decide) x hj⟩
  | exact ⟨0, 1, by decide, by decide,
      paper_A_transvection_injective (i := 0) (j := 1) (by decide) x hj⟩
  | exact ⟨1, 2, by decide, by decide,
      paper_A_transvection_injective (i := 1) (j := 2) (by decide) x hj⟩
  | exact ⟨0, 2, by decide, by decide,
      paper_A_transvection_injective (i := 0) (j := 2) (by decide) x hj⟩

/--
The `paperContractRight` construction used in the Connes rigidity formalization.
-/
noncomputable def paperContractRight (φ : A →ₗ[k] k) :
    PaperKernel.TensorAA →ₗ[k] A :=
  TensorProduct.lift (LinearMap.mk₂ k (fun a b => φ b • a)
    (by intros; rw [smul_add])
    (by intros; rw [smul_smul, smul_smul, mul_comm])
    (by intros; rw [map_add, add_smul])
    (by intros; rw [map_smul, smul_smul, smul_eq_mul]))

@[simp] lemma paperContractRight_tmul (φ : A →ₗ[k] k) (a b : A) :
    paperContractRight φ (a ⊗ₜ[k] b) = φ b • a := by
  rfl

lemma paperContractRight_basisCoord
    (p : PaperKernel.OrderedBasisIndex) (x : PaperKernel.TensorAA) :
    paperContractRight (PaperKernel.orderedBasis.coord p) x =
      (TensorProduct.equivFinsuppOfBasisRight PaperKernel.orderedBasis x) p := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      simp [Module.Basis.coord_apply]
  | add x y hx hy =>
      simp only [map_add, hx, hy, Finsupp.add_apply]

lemma paperContractRight_equivariant
    {p : PaperKernel.OrderedBasisIndex} {i j : Fin 3} (hij : i ≠ j)
    (hr : (ofLex p).1 ≠ i)
    (a : SpecialLinear.R) (x : PaperKernel.TensorAA) :
    paperContractRight (PaperKernel.orderedBasis.coord p)
      (sl3TensorAction (Matrix.SpecialLinearGroup.transvection hij a) x) =
      sl3AAction (Matrix.SpecialLinearGroup.transvection hij a)
        (paperContractRight (PaperKernel.orderedBasis.coord p) x) := by
  let φ := PaperKernel.orderedBasis.coord p
  have hφ : ∀ b : A, φ
      (sl3AAction (Matrix.SpecialLinearGroup.transvection hij a) b) = φ b := by
    intro b
    exact paper_ordered_coord_transvection_invariant hij (Ne.symm hr) a b
  induction x using TensorProduct.induction_on with
  | zero => simp [paperContractRight]
  | tmul u v =>
      have hv := hφ v
      change (orderedBasis.repr
          (sl3AAction (Matrix.SpecialLinearGroup.transvection hij a) v)) p =
        (orderedBasis.repr v) p at hv
      simp [paperContractRight, sl3TensorAction, hv]
  | add x y hx hy =>
      simp only [map_add, hx, hy, (sl3AAction _).map_add]

/-- Infinite orbit of a nonzero fixed tensor. Paper: §5. -/
theorem paper_C_orbit_infinite (c : PaperKernel.C) (hc : c ≠ 0) :
    (Set.range fun s : SpecialLinear.SL3 => sl3CAction s c).Infinite := by
  have hc' : (c : PaperKernel.TensorAA) ≠ 0 := by
    intro hzero
    apply hc
    apply Subtype.ext
    exact hzero
  let e : PaperKernel.TensorAA ≃ₗ[k]
      (PaperKernel.OrderedBasisIndex →₀ A) :=
    TensorProduct.equivFinsuppOfBasisRight PaperKernel.orderedBasis
  have he : e (c : PaperKernel.TensorAA) ≠ 0 := by
    intro hzero
    apply hc'
    exact (e.map_eq_zero_iff).mp hzero
  obtain ⟨p, hp⟩ : ∃ p : PaperKernel.OrderedBasisIndex,
      e (c : PaperKernel.TensorAA) p ≠ 0 := by
    by_contra h
    apply he
    apply Finsupp.ext
    intro p
    exact not_ne_iff.mp (not_exists.mp h p)
  have hcoord : paperContractRight (PaperKernel.orderedBasis.coord p)
      (c : PaperKernel.TensorAA) ≠ 0 := by
    rw [paperContractRight_basisCoord]
    exact hp
  obtain ⟨i, j, hij, hir, hinj⟩ :=
    paper_A_transvection_injective_avoiding
      (paperContractRight (PaperKernel.orderedBasis.coord p) (c : PaperKernel.TensorAA))
      hcoord (ofLex p).1
  let lift : SpecialLinear.R → SpecialLinear.SL3 :=
    fun a => Matrix.SpecialLinearGroup.transvection hij a
  have hinjC : Function.Injective (fun a : SpecialLinear.R =>
      sl3CAction (lift a) c) := by
    intro a b hab
    have hproj := congrArg (fun z : PaperKernel.C =>
      paperContractRight (PaperKernel.orderedBasis.coord p) (z : PaperKernel.TensorAA)) hab
    change paperContractRight (PaperKernel.orderedBasis.coord p)
        (sl3TensorAction (lift a) (c : PaperKernel.TensorAA)) =
      paperContractRight (PaperKernel.orderedBasis.coord p)
        (sl3TensorAction (lift b) (c : PaperKernel.TensorAA)) at hproj
    rw [paperContractRight_equivariant hij (Ne.symm hir) a (c : PaperKernel.TensorAA),
      paperContractRight_equivariant hij (Ne.symm hir) b (c : PaperKernel.TensorAA)] at hproj
    simp only [paperContractRight_basisCoord] at hproj
    apply hinj
    change sl3AAction (Matrix.SpecialLinearGroup.transvection hij a)
        (paperContractRight (PaperKernel.orderedBasis.coord p)
          (c : PaperKernel.TensorAA)) =
      sl3AAction (Matrix.SpecialLinearGroup.transvection hij b)
        (paperContractRight (PaperKernel.orderedBasis.coord p)
          (c : PaperKernel.TensorAA))
    rw [paperContractRight_basisCoord]
    exact hproj
  apply (Set.infinite_range_of_injective hinjC).mono
  rintro _ ⟨a, rfl⟩
  exact ⟨lift a, rfl⟩

/-- Infinite orbit of a nonzero tensor-dual element. Paper: §5. -/
theorem paper_AVStar_orbit_infinite (u : PaperKernel.AVStar) (hu : u ≠ 0) :
    (Set.range fun s : SpecialLinear.SL3 =>
      avStarAction s (1 : PaperKernel.Q) u).Infinite := by
  obtain ⟨p, hp⟩ := paper_avStar_coeff_exists u hu
  let x := (TensorProduct.equivFinsuppOfBasisRight paperVStarBasis u) p
  have hx : x ≠ 0 := hp
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, x j ≠ 0 := by
    by_contra h
    apply hx
    funext j
    exact not_ne_iff.mp (not_exists.mp h j)
  fin_cases j
  · let i : Fin 3 := 1
    have hij : i ≠ 0 := by decide
    let lift : SpecialLinear.R → SpecialLinear.SL3 :=
      fun a => Matrix.SpecialLinearGroup.transvection hij a
    have hinj : Function.Injective (fun a : SpecialLinear.R =>
        avStarAction (lift a) (1 : PaperKernel.Q) u) := by
      intro a b hab
      have hcoord := congrArg (fun z : PaperKernel.AVStar =>
        (TensorProduct.equivFinsuppOfBasisRight paperVStarBasis z) p) hab
      rw [paper_avStar_coeff_sl3, paper_avStar_coeff_sl3] at hcoord
      exact paper_A_transvection_injective hij x hj (by simpa [lift] using hcoord)
    apply (Set.infinite_range_of_injective hinj).mono
    rintro _ ⟨a, rfl⟩
    exact ⟨lift a, rfl⟩
  · let i : Fin 3 := 0
    have hij : i ≠ 1 := by decide
    let lift : SpecialLinear.R → SpecialLinear.SL3 :=
      fun a => Matrix.SpecialLinearGroup.transvection hij a
    have hinj : Function.Injective (fun a : SpecialLinear.R =>
        avStarAction (lift a) (1 : PaperKernel.Q) u) := by
      intro a b hab
      have hcoord := congrArg (fun z : PaperKernel.AVStar =>
        (TensorProduct.equivFinsuppOfBasisRight paperVStarBasis z) p) hab
      rw [paper_avStar_coeff_sl3, paper_avStar_coeff_sl3] at hcoord
      exact paper_A_transvection_injective hij x hj (by simpa [lift] using hcoord)
    apply (Set.infinite_range_of_injective hinj).mono
    rintro _ ⟨a, rfl⟩
    exact ⟨lift a, rfl⟩
  · let i : Fin 3 := 0
    have hij : i ≠ 2 := by decide
    let lift : SpecialLinear.R → SpecialLinear.SL3 :=
      fun a => Matrix.SpecialLinearGroup.transvection hij a
    have hinj : Function.Injective (fun a : SpecialLinear.R =>
        avStarAction (lift a) (1 : PaperKernel.Q) u) := by
      intro a b hab
      have hcoord := congrArg (fun z : PaperKernel.AVStar =>
        (TensorProduct.equivFinsuppOfBasisRight paperVStarBasis z) p) hab
      rw [paper_avStar_coeff_sl3, paper_avStar_coeff_sl3] at hcoord
      exact paper_A_transvection_injective hij x hj (by simpa [lift] using hcoord)
    apply (Set.infinite_range_of_injective hinj).mono
    rintro _ ⟨a, rfl⟩
    exact ⟨lift a, rfl⟩

/-- Infinite kernel orbit for the first action in additive coordinates. Paper: §5. -/
theorem paper_D_orbit_one (d : PaperKernel.D) (hd : d ≠ 0) :
    (Set.range fun s : SpecialLinear.SL3 =>
      paperThetaOneLinear (s, (1 : PaperKernel.Q)) d).Infinite := by
  rcases d with ⟨u, c⟩
  by_cases hu : u ≠ 0
  · apply Set.Infinite.of_image (fun z : PaperKernel.D => z.1)
    apply (paper_AVStar_orbit_infinite u hu).mono
    rintro y ⟨s, rfl⟩
    refine ⟨paperThetaOneLinear (s, (1 : PaperKernel.Q)) (u, c),
      ⟨s, rfl⟩, ?_⟩
    rfl
  · have hc : c ≠ 0 := by
      have hu0 : u = 0 := not_ne_iff.mp hu
      intro hc
      apply hd
      simp [hu0, hc]
    apply Set.Infinite.of_image (fun z : PaperKernel.D => z.2)
    apply (paper_C_orbit_infinite c hc).mono
    rintro y ⟨s, rfl⟩
    refine ⟨paperThetaOneLinear (s, (1 : PaperKernel.Q)) (u, c),
      ⟨s, rfl⟩, ?_⟩
    rfl

/-- Infinite kernel orbit for the second action in additive coordinates. Paper: §5. -/
theorem paper_D_orbit_two (d : PaperKernel.D) (hd : d ≠ 0) :
    (Set.range fun s : SpecialLinear.SL3 =>
      thetaTwoLinearMap (s, (1 : PaperKernel.Q)) d).Infinite := by
  rcases d with ⟨u, c⟩
  by_cases hu : u ≠ 0
  · apply Set.Infinite.of_image (fun z : PaperKernel.D => z.1)
    apply (paper_AVStar_orbit_infinite u hu).mono
    rintro y ⟨s, rfl⟩
    refine ⟨thetaTwoLinearMap (s, (1 : PaperKernel.Q)) (u, c),
      ⟨s, rfl⟩, ?_⟩
    simp only [PaperKernel.thetaTwoLinearMap_sl3]
  · have hc : c ≠ 0 := by
      have hu0 : u = 0 := not_ne_iff.mp hu
      intro hc
      apply hd
      simp [hu0, hc]
    apply Set.Infinite.of_image (fun z : PaperKernel.D => z.2)
    apply (paper_C_orbit_infinite c hc).mono
    rintro y ⟨s, rfl⟩
    refine ⟨thetaTwoLinearMap (s, (1 : PaperKernel.Q)) (u, c),
      ⟨s, rfl⟩, ?_⟩
    simp only [PaperKernel.thetaTwoLinearMap_sl3]

/--
The `paperCoordStar` construction used in the Connes rigidity formalization.
-/
def paperCoordStar (p : PaperKernel.SymplecticIndex) : PaperKernel.VStar where
  toFun v := v p
  map_add' v w := by simp
  map_smul' a v := by simp

/-- Infinite multiplicative kernel orbit for the first action. Paper: §5. -/
theorem paper_kernel_orbit_one (a : PaperICC.N) (ha : a ≠ 1) :
    (Set.range fun s : SpecialLinear.SL3 =>
      paperThetaOneHom (s, (1 : PaperKernel.Q)) a).Infinite := by
  have hd : a.toAdd ≠ 0 := by
    intro hzero
    apply ha
    exact Multiplicative.ext hzero
  apply Set.Infinite.of_image Multiplicative.ofAdd
  apply (paper_D_orbit_one a.toAdd hd).mono
  rintro y ⟨s, rfl⟩
  refine ⟨paperThetaOneHom (s, (1 : PaperKernel.Q)) a, ⟨s, rfl⟩, ?_⟩
  rfl

/-- Infinite multiplicative kernel orbit for the second action. Paper: §5. -/
theorem paper_kernel_orbit_two (a : PaperICC.N) (ha : a ≠ 1) :
    (Set.range fun s : SpecialLinear.SL3 =>
      paperThetaTwoHom (s, (1 : PaperKernel.Q)) a).Infinite := by
  have hd : a.toAdd ≠ 0 := by
    intro hzero
    apply ha
    exact Multiplicative.ext hzero
  apply Set.Infinite.of_image Multiplicative.ofAdd
  apply (paper_D_orbit_two a.toAdd hd).mono
  rintro y ⟨s, rfl⟩
  refine ⟨paperThetaTwoHom (s, (1 : PaperKernel.Q)) a, ⟨s, rfl⟩, ?_⟩
  rfl

lemma paper_tmul_star_ne_zero (f : PaperKernel.VStar)
    (hf : f ≠ 0) : (a0 ⊗ₜ[k] f : PaperKernel.AVStar) ≠ 0 := by
  obtain ⟨v, hv⟩ : ∃ v : PaperKernel.PaperV, f v ≠ 0 := by
    by_contra h
    apply hf
    apply LinearMap.ext
    intro v
    exact not_ne_iff.mp (not_exists.mp h v)
  intro hzero
  have hcontract := congrArg (contractStar (LinearMap.applyₗ (R := k) v)) hzero
  rw [map_zero, contractStar_tmul] at hcontract
  change f v • a0 = 0 at hcontract
  have hmul : f v * (1 : k) = 0 := by
    simpa [a0, smul_eq_mul] using congrFun hcontract (0 : Fin 3)
  exact hv (by simpa using hmul)

lemma paper_q_moved_coord (q : PaperKernel.Q) (hq : q ≠ 1) :
    ∃ p : PaperKernel.SymplecticIndex,
      qVStarActionHom q (paperCoordStar p) ≠ paperCoordStar p := by
  by_contra h
  push Not at h
  apply hq
  have hqinv : q⁻¹ = 1 := by
    apply Subtype.ext
    apply Matrix.ext_of_mulVec_single
    intro j
    funext i
    have hcoord := congrArg
      (fun f : PaperKernel.VStar => f (Pi.single j (1 : k))) (h i)
    change (Matrix.mulVec (((q⁻¹ : PaperKernel.Q) :
        Matrix PaperKernel.SymplecticIndex PaperKernel.SymplecticIndex k))
          (Pi.single j 1 : PaperKernel.PaperV) i) =
            (Pi.single j 1 : PaperKernel.PaperV) i at hcoord
    simpa [Matrix.mulVec_single_one, Matrix.one_apply,
      Pi.single_apply] using hcoord
  have hinv := congrArg Inv.inv hqinv
  simpa using hinv

lemma paper_q_coord_difference_ne_zero (q : PaperKernel.Q) (hq : q ≠ 1) :
    ∃ f : PaperKernel.VStar, f ≠ 0 ∧
      ∃ p : PaperKernel.SymplecticIndex,
        f = qVStarActionHom q (paperCoordStar p) + paperCoordStar p := by
  obtain ⟨p, hp⟩ := paper_q_moved_coord q hq
  let f := qVStarActionHom q (paperCoordStar p) + paperCoordStar p
  have hf : f ≠ 0 := by
    intro hzero
    apply hp
    have hself : paperCoordStar p + paperCoordStar p = 0 := by
      rw [← two_smul k (paperCoordStar p), show (2 : k) = 0 by rfl,
        zero_smul]
    calc
      qVStarActionHom q (paperCoordStar p) =
          qVStarActionHom q (paperCoordStar p) + 0 := (add_zero _).symm
      _ = qVStarActionHom q (paperCoordStar p) +
          (paperCoordStar p + paperCoordStar p) := by rw [hself]
      _ = (qVStarActionHom q (paperCoordStar p) + paperCoordStar p) +
          paperCoordStar p := (add_assoc _ _ _).symm
      _ = f + paperCoordStar p := rfl
      _ = 0 + paperCoordStar p := by rw [hzero]
      _ = paperCoordStar p := zero_add _
  exact ⟨f, hf, p, rfl⟩

lemma paper_thetaOne_q_zero (q : PaperKernel.Q) (u : PaperKernel.AVStar) :
    paperThetaOneLinear ((1 : SpecialLinear.SL3), q) (u, (0 : PaperKernel.C)) =
      (avStarAction (1 : SpecialLinear.SL3) q u, 0) := by
  rfl

lemma paper_thetaTwo_q_zero (q : PaperKernel.Q) (u : PaperKernel.AVStar) :
    thetaTwoLinearMap ((1 : SpecialLinear.SL3), q) (u, (0 : PaperKernel.C)) =
      (avStarAction (1 : SpecialLinear.SL3) q u, 0) := by
  simp [thetaTwoLinearMap]

theorem paper_q_displacement_one (q : PaperKernel.Q) (hq : q ≠ 1) :
    ∃ d : PaperKernel.D,
      d + paperThetaOneLinear ((1 : SpecialLinear.SL3), q) d ≠ 0 := by
  obtain ⟨p, hp⟩ := paper_q_moved_coord q hq
  let f : PaperKernel.VStar := paperCoordStar p
  have hf : f ≠ 0 := by
    intro hzero
    have h := congrArg (fun z : PaperKernel.VStar =>
      z (Pi.single p (1 : k))) hzero
    simp [f, paperCoordStar] at h
  have hdiff : qVStarActionHom q f + f ≠ 0 := by
    intro hzero
    apply hp
    have hself : f + f = 0 := by
      rw [← two_smul k f, show (2 : k) = 0 by rfl, zero_smul]
    have hfix : qVStarActionHom q f = f := by
      calc
        qVStarActionHom q f = qVStarActionHom q f + 0 := (add_zero _).symm
        _ = qVStarActionHom q f + (f + f) := by rw [hself]
        _ = (qVStarActionHom q f + f) + f := by rw [← add_assoc]
        _ = 0 + f := by rw [hzero]
        _ = f := zero_add _
    simpa [f] using hfix
  let d : PaperKernel.D := (a0 ⊗ₜ[k] f, 0)
  refine ⟨d, ?_⟩
  intro hzero
  have hfirst := congrArg Prod.fst hzero
  have hstar : a0 ⊗ₜ[k]
      (qVStarActionHom q f + f) = 0 := by
    rw [TensorProduct.tmul_add]
    simpa [d, paper_thetaOne_q_zero, avStar_q_action, add_comm] using hfirst
  exact paper_tmul_star_ne_zero _ hdiff hstar

theorem paper_q_displacement_two (q : PaperKernel.Q) (hq : q ≠ 1) :
    ∃ d : PaperKernel.D,
      d + thetaTwoLinearMap ((1 : SpecialLinear.SL3), q) d ≠ 0 := by
  obtain ⟨p, hp⟩ := paper_q_moved_coord q hq
  let f : PaperKernel.VStar := paperCoordStar p
  have hf : f ≠ 0 := by
    intro hzero
    have h := congrArg (fun z : PaperKernel.VStar =>
      z (Pi.single p (1 : k))) hzero
    simp [f, paperCoordStar] at h
  have hdiff : qVStarActionHom q f + f ≠ 0 := by
    intro hzero
    apply hp
    have hself : f + f = 0 := by
      rw [← two_smul k f, show (2 : k) = 0 by rfl, zero_smul]
    have hfix : qVStarActionHom q f = f := by
      calc
        qVStarActionHom q f = qVStarActionHom q f + 0 := (add_zero _).symm
        _ = qVStarActionHom q f + (f + f) := by rw [hself]
        _ = (qVStarActionHom q f + f) + f := by rw [← add_assoc]
        _ = 0 + f := by rw [hzero]
        _ = f := zero_add _
    simpa [f] using hfix
  let d : PaperKernel.D := (a0 ⊗ₜ[k] f, 0)
  refine ⟨d, ?_⟩
  intro hzero
  have hfirst := congrArg Prod.fst hzero
  have hstar : a0 ⊗ₜ[k]
      (qVStarActionHom q f + f) = 0 := by
    rw [TensorProduct.tmul_add]
    simpa [d, paper_thetaTwo_q_zero, avStar_q_action, add_comm] using hfirst
  exact paper_tmul_star_ne_zero _ hdiff hstar

lemma paper_neg_eq_self (d : PaperKernel.D) : -d = d := by
  have hadd : d + d = 0 := by
    rw [← two_smul k d, show (2 : k) = 0 by rfl, zero_smul]
  calc
    -d = -d + (d + d) := by rw [hadd, add_zero]
    _ = d := by abel

/-- Nontrivial quotient displacement for the first action. Paper: §5. -/
theorem paper_q_mul_displacement_one (q : PaperKernel.Q) (hq : q ≠ 1) :
    ∃ a : PaperICC.N,
      a * (paperThetaOneHom ((1 : SpecialLinear.SL3), q) a)⁻¹ ≠ 1 ∧
        (Set.range fun s : SpecialLinear.SL3 =>
          paperThetaOneHom (s, (1 : PaperKernel.Q))
            (a * (paperThetaOneHom ((1 : SpecialLinear.SL3), q) a)⁻¹)).Infinite := by
  obtain ⟨d, hd⟩ := paper_q_displacement_one q hq
  let a : PaperICC.N := Multiplicative.ofAdd d
  let displacement : PaperICC.N :=
    a * (paperThetaOneHom ((1 : SpecialLinear.SL3), q) a)⁻¹
  have hdisp : displacement ≠ 1 := by
    intro h
    apply hd
    have h' := congrArg Multiplicative.toAdd h
    change d + -paperThetaOneLinear ((1 : SpecialLinear.SL3), q) d = 0 at h'
    rw [paper_neg_eq_self] at h'
    exact h'
  refine ⟨a, hdisp, ?_⟩
  have hdisp_add : displacement.toAdd ≠ 0 := by
    intro h
    apply hdisp
    exact Multiplicative.ext h
  have horbit := paper_D_orbit_one displacement.toAdd hdisp_add
  apply Set.Infinite.of_image Multiplicative.ofAdd
  apply horbit.mono
  rintro y ⟨s, rfl⟩
  refine ⟨paperThetaOneHom (s, (1 : PaperKernel.Q)) displacement,
    ⟨s, rfl⟩, ?_⟩
  rfl

/-- Nontrivial quotient displacement for the second action. Paper: §5. -/
theorem paper_q_mul_displacement_two (q : PaperKernel.Q) (hq : q ≠ 1) :
    ∃ a : PaperICC.N,
      a * (paperThetaTwoHom ((1 : SpecialLinear.SL3), q) a)⁻¹ ≠ 1 ∧
        (Set.range fun s : SpecialLinear.SL3 =>
          paperThetaTwoHom (s, (1 : PaperKernel.Q))
            (a * (paperThetaTwoHom ((1 : SpecialLinear.SL3), q) a)⁻¹)).Infinite := by
  obtain ⟨d, hd⟩ := paper_q_displacement_two q hq
  let a : PaperICC.N := Multiplicative.ofAdd d
  let displacement : PaperICC.N :=
    a * (paperThetaTwoHom ((1 : SpecialLinear.SL3), q) a)⁻¹
  have hdisp : displacement ≠ 1 := by
    intro h
    apply hd
    have h' := congrArg Multiplicative.toAdd h
    change d + -thetaTwoLinearMap ((1 : SpecialLinear.SL3), q) d = 0 at h'
    rw [paper_neg_eq_self] at h'
    exact h'
  refine ⟨a, hdisp, ?_⟩
  have hdisp_add : displacement.toAdd ≠ 0 := by
    intro h
    apply hdisp
    exact Multiplicative.ext h
  have horbit := paper_D_orbit_two displacement.toAdd hdisp_add
  apply Set.Infinite.of_image Multiplicative.ofAdd
  apply horbit.mono
  rintro y ⟨s, rfl⟩
  refine ⟨paperThetaTwoHom (s, (1 : PaperKernel.Q)) displacement,
    ⟨s, rfl⟩, ?_⟩
  rfl

/-- ICC orbit data for the first Zhou action. Paper: §5. -/
theorem paper_actionData_one : PaperICC.ActionData paperThetaOneHom where
  kernel_orbit := paper_kernel_orbit_one
  q_displacement := paper_q_mul_displacement_one

/-- ICC orbit data for the second Zhou action. Paper: §5. -/
theorem paper_actionData_two : PaperICC.ActionData paperThetaTwoHom where
  kernel_orbit := paper_kernel_orbit_two
  q_displacement := paper_q_mul_displacement_two

/-- The first concrete Zhou group is ICC. This is the public §5 endpoint. -/
theorem paper_gammaOne_icc :
    IsICC PaperKernel.paperGammaOne := by
  exact PaperICC.isICC_of_product_quotient
    PaperKernel.paperThetaOneHom paper_actionData_one

/-- The second concrete Zhou group is ICC. This is the public §5 endpoint. -/
theorem paper_gammaTwo_icc :
    IsICC PaperKernel.paperGammaTwo := by
  exact PaperICC.isICC_of_product_quotient
    PaperKernel.paperThetaTwoHom paper_actionData_two

end
end PaperICC
end Connes
