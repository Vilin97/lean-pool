/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Concrete Zhou action instances on the paper kernel. Paper: §§2--4.
-/
import LeanPool.ConnesRigidity.Construction.SquareSpan

/-!
The paper action instances component of the Connes rigidity formalization.
-/

namespace Connes
namespace Construction
namespace PaperKernel

noncomputable section

open Connes.OpenAIPort

/-- Target-coordinate formula for an elementary `SL₃` transvection. Paper: §2. -/
lemma transvection_action_apply_target {i j : Fin 3} (hij : i ≠ j)
    (a : SpecialLinear.R) (x : Construction.A) :
    sl3AAction (Matrix.SpecialLinearGroup.transvection hij a) x i =
      x i + a * x j := by
  change (Matrix.mulVec (Matrix.transvection i j a) x) i = x i + a * x j
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]
  simp

/-- Off-target coordinates are fixed by an elementary `SL₃` transvection. Paper: §2. -/
lemma transvection_action_apply_of_ne_target {i j r : Fin 3} (hij : i ≠ j)
    (hri : r ≠ i) (a : SpecialLinear.R) (x : A) :
    sl3AAction (Matrix.SpecialLinearGroup.transvection hij a) x r = x r := by
  change (Matrix.mulVec (Matrix.transvection i j a) x) r = x r
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]
  simp [hri]

/-- The linear action on the first summand of the paper kernel. Paper: §2. -/
def avStarAction (l : SpecialLinear.SL3) (q : Q) : AVStar ≃ₗ[k] AVStar :=
  TensorProduct.congr (sl3AAction l) (qVStarActionHom q)

/-- The first-summand action is a homomorphism. Paper: §2. -/
def avStarActionHom : H →* (AVStar ≃ₗ[k] AVStar) where
  toFun h := avStarAction h.1 h.2
  map_one' := by
    apply LinearEquiv.ext
    intro u
    refine TensorProduct.induction_on u ?_ ?_ ?_
    · simp [avStarAction]
    · intro a f
      simp [avStarAction]
    · intro x y hx hy
      simp only [map_add, hx, hy]
  map_mul' h h' := by
    apply LinearEquiv.ext
    intro u
    refine TensorProduct.induction_on u ?_ ?_ ?_
    · simp [avStarAction]
    · intro a f
      simp [avStarAction]
    · intro x y hx hy
      simp only [map_add, hx, hy]

/-- The SL₃ action on the fixed tensor module is invertible. Paper: §2. -/
theorem sl3TensorAction_mul (l m : SpecialLinear.SL3) :
    sl3TensorAction (l * m) =
      (sl3TensorAction l).comp (sl3TensorAction m) := by
  apply LinearMap.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a b
    simp [sl3TensorAction]
  · intro x y hx hy
    simp only [map_add, hx, hy]

/-- The identity law for the diagonal tensor action. Paper: §2. -/
theorem sl3TensorAction_one :
    sl3TensorAction (1 : SpecialLinear.SL3) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a b
    simp [sl3TensorAction]
  · intro x y hx hy
    simp only [map_add, hx, hy]

/-- The diagonal tensor action has inverse given by the inverse matrix. Paper: §2. -/
theorem sl3TensorAction_inv_comp (l : SpecialLinear.SL3) :
    (sl3TensorAction l⁻¹).comp (sl3TensorAction l) = LinearMap.id := by
  rw [← sl3TensorAction_mul]
  simpa using sl3TensorAction_one

/-- The inverse diagonal tensor action has the reverse composition law. Paper: §2. -/
theorem sl3TensorAction_comp_inv (l : SpecialLinear.SL3) :
    (sl3TensorAction l).comp (sl3TensorAction l⁻¹) = LinearMap.id := by
  rw [← sl3TensorAction_mul]
  simpa using sl3TensorAction_one

/-- The fixed-tensor action has inverse given by the inverse matrix. Paper: §2. -/
theorem sl3CAction_inv_comp (l : SpecialLinear.SL3) :
    (sl3CAction l⁻¹).comp (sl3CAction l) = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change ((sl3TensorAction l⁻¹).comp (sl3TensorAction l)) (c : TensorAA) =
    (LinearMap.id : TensorAA →ₗ[k] TensorAA) (c : TensorAA)
  exact congrArg (fun f : TensorAA →ₗ[k] TensorAA => f (c : TensorAA))
    (sl3TensorAction_inv_comp l)

/-- The reverse fixed-tensor action composition is the identity. Paper: §2. -/
theorem sl3CAction_comp_inv (l : SpecialLinear.SL3) :
    (sl3CAction l).comp (sl3CAction l⁻¹) = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change ((sl3TensorAction l).comp (sl3TensorAction l⁻¹)) (c : TensorAA) =
    (LinearMap.id : TensorAA →ₗ[k] TensorAA) (c : TensorAA)
  exact congrArg (fun f : TensorAA →ₗ[k] TensorAA => f (c : TensorAA))
    (sl3TensorAction_comp_inv l)

/-- The SL₃ action on the fixed tensor module is invertible. Paper: §2. -/
def sl3CActionEquiv (l : SpecialLinear.SL3) : C ≃ₗ[k] C :=
  { toFun := sl3CAction l
    invFun := sl3CAction l⁻¹
    left_inv := by
      intro c
      apply Subtype.ext
      change sl3TensorAction l⁻¹ (sl3TensorAction l (c : TensorAA)) = c
      have h := congrArg (fun f : TensorAA →ₗ[k] TensorAA => f (c : TensorAA))
        (sl3TensorAction_inv_comp l)
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
    right_inv := by
      intro c
      apply Subtype.ext
      change sl3TensorAction l (sl3TensorAction l⁻¹ (c : TensorAA)) = c
      have h := congrArg (fun f : TensorAA →ₗ[k] TensorAA => f (c : TensorAA))
        (sl3TensorAction_comp_inv l)
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
    map_add' := by
      intro c d
      exact (sl3CAction l).map_add c d
    map_smul' := by
      intro a c
      exact (sl3CAction l).map_smul a c }

/-- The fixed-tensor action is a homomorphism. Paper: §2. -/
def sl3CActionHom : SpecialLinear.SL3 →* (C ≃ₗ[k] C) where
  toFun := sl3CActionEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro c
    apply Subtype.ext
    have h := congrArg (fun f : TensorAA →ₗ[k] TensorAA => f (c : TensorAA))
      sl3TensorAction_one
    change sl3TensorAction (1 : SpecialLinear.SL3) (c : TensorAA) = c
    simpa using h
  map_mul' l m := by
    apply LinearEquiv.ext
    intro c
    apply Subtype.ext
    have h := congrArg (fun f : TensorAA →ₗ[k] TensorAA => f (c : TensorAA))
      (sl3TensorAction_mul l m)
    change sl3TensorAction (l * m) (c : TensorAA) =
      sl3TensorAction l (sl3TensorAction m (c : TensorAA))
    simpa using h

/-- The first Zhou action as a linear equivalence of the kernel. Paper: §2. -/
def paperThetaOneLinear (h : H) : D ≃ₗ[k] D :=
  (avStarAction h.1 h.2).prodCongr (sl3CActionEquiv h.1)

/-- Pointwise form of the first Zhou action on the kernel splitting. -/
@[simp] theorem paperThetaOneLinear_apply (h : H) (d : D) :
    paperThetaOneLinear h d =
      (avStarAction h.1 h.2 d.1, sl3CAction h.1 d.2) := rfl

/-- Reinterpret a linear kernel equivalence as a multiplicative automorphism. Paper: §2. -/
def additiveEquivToMulAut (e : D ≃ₗ[k] D) : MulAut (Multiplicative D) :=
  e.toAddEquiv.toMultiplicative

/-- The first Zhou action as a linear homomorphism. Paper: §2. -/
def paperThetaOneLinearHom : H →* (D ≃ₗ[k] D) where
  toFun := paperThetaOneLinear
  map_one' := by
    apply LinearEquiv.ext
    rintro ⟨u, c⟩
    apply Prod.ext
    · have hm := avStarActionHom.map_one
      change avStarAction (1 : SpecialLinear.SL3) (1 : Q) =
        LinearEquiv.refl k AVStar at hm
      exact congrArg (fun e : AVStar ≃ₗ[k] AVStar => e u) hm
    · have hm := sl3CActionHom.map_one
      change sl3CActionEquiv (1 : SpecialLinear.SL3) =
        LinearEquiv.refl k C at hm
      exact congrArg (fun e : C ≃ₗ[k] C => e c) hm
  map_mul' h h' := by
    apply LinearEquiv.ext
    rintro ⟨u, c⟩
    apply Prod.ext
    · have hm := avStarActionHom.map_mul h h'
      change avStarAction (h.1 * h'.1) (h.2 * h'.2) =
        (avStarAction h.1 h.2) * (avStarAction h'.1 h'.2) at hm
      exact congrArg (fun e : AVStar ≃ₗ[k] AVStar => e u) hm
    · have hm := sl3CActionHom.map_mul h.1 h'.1
      change sl3CActionEquiv (h.1 * h'.1) =
        (sl3CActionEquiv h.1) * (sl3CActionEquiv h'.1) at hm
      exact congrArg (fun e : C ≃ₗ[k] C => e c) hm

/-- The first Zhou action on the multiplicative kernel. Paper: §2. -/
def paperThetaOneHom : H →* MulAut (Multiplicative D) where
  toFun h := additiveEquivToMulAut (paperThetaOneLinearHom h)
  map_one' := by
    apply MulEquiv.ext
    intro d
    change paperThetaOneLinearHom 1 d.toAdd = d.toAdd
    simp
  map_mul' h h' := by
    apply MulEquiv.ext
    intro d
    change paperThetaOneLinearHom (h * h') d.toAdd =
      paperThetaOneLinearHom h (paperThetaOneLinearHom h' d.toAdd)
    simp

/-- The finite quadratic-defect functional obeys the paper cocycle law. Paper: §2. -/
theorem quadraticDefectLinear_cocycle (p q : Q) :
    quadraticDefectLinear (p * q) =
      (qVStarActionHom p) (quadraticDefectLinear q) +
        quadraticDefectLinear p := by
  apply LinearMap.ext
  intro v
  change (quadraticDefectLinear (p * q)) v =
    (qVStarActionHom p (quadraticDefectLinear q)) v +
      (quadraticDefectLinear p) v
  have hdual (f : VStar) (w : PaperV) :
      (qVStarActionHom p f) w = f (p⁻¹ • w) := by
    rfl
  rw [hdual]
  change standardQuadraticForm ((p * q)⁻¹ • v) + standardQuadraticForm v =
    (quadraticDefectLinear q) (p⁻¹ • v) +
      (quadraticDefectLinear p) v
  change standardQuadraticForm ((p * q)⁻¹ • v) + standardQuadraticForm v =
    (standardQuadraticForm (q⁻¹ • (p⁻¹ • v)) +
      standardQuadraticForm (p⁻¹ • v)) +
        (standardQuadraticForm (p⁻¹ • v) + standardQuadraticForm v)
  rw [mul_inv_rev, mul_smul]
  have hcancel :
      standardQuadraticForm (p⁻¹ • v) + standardQuadraticForm (p⁻¹ • v) = 0 :=
    CharTwo.add_self_eq_zero _
  rw [← add_zero
    (standardQuadraticForm (q⁻¹ • p⁻¹ • v) + standardQuadraticForm v),
    ← hcancel]
  abel

/-- The correction term in the second Zhou action. Paper: §2. -/
def thetaTwoTermMap (h : H) : C →ₗ[k] AVStar where
  toFun c := delta (sl3CAction h.1 c) ⊗ₜ[k] quadraticDefectLinear h.2
  map_add' c d := by
    simp only [map_add]
    rw [TensorProduct.add_tmul]
  map_smul' a c := by
    simp only [map_smul]
    rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    simp

@[simp] theorem thetaTwoTermMap_apply (h : H) (c : C) :
    thetaTwoTermMap h c = delta (sl3CAction h.1 c) ⊗ₜ[k] quadraticDefectLinear h.2 :=
  rfl

/-- The second Zhou action as a linear map. Paper: §2. -/
def thetaTwoLinearMap (h : H) : D →ₗ[k] D where
  toFun d := (avStarAction h.1 h.2 d.1 + thetaTwoTermMap h d.2,
    sl3CAction h.1 d.2)
  map_add' d e := by
    apply Prod.ext
    · change avStarAction h.1 h.2 (d.1 + e.1) +
          delta (sl3CAction h.1 (d.2 + e.2)) ⊗ₜ[k] quadraticDefectLinear h.2 =
        (avStarAction h.1 h.2 d.1 +
          delta (sl3CAction h.1 d.2) ⊗ₜ[k] quadraticDefectLinear h.2) +
          (avStarAction h.1 h.2 e.1 +
            delta (sl3CAction h.1 e.2) ⊗ₜ[k] quadraticDefectLinear h.2)
      simp only [map_add]
      rw [TensorProduct.add_tmul]
      abel
    · simp
  map_smul' a d := by
    apply Prod.ext
    · change avStarAction h.1 h.2 (a • d.1) +
          delta (sl3CAction h.1 (a • d.2)) ⊗ₜ[k] quadraticDefectLinear h.2 =
        a • (avStarAction h.1 h.2 d.1 +
          delta (sl3CAction h.1 d.2) ⊗ₜ[k] quadraticDefectLinear h.2)
      simp only [map_smul]
      rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
      simp
    · simp

/-- The second Zhou linear map composes according to the group law. Paper: §2. -/
theorem thetaTwoLinearMap_mul (h h' : H) :
    thetaTwoLinearMap (h * h') =
      (thetaTwoLinearMap h).comp (thetaTwoLinearMap h') := by
  apply LinearMap.ext
  rintro ⟨u, c⟩
  apply Prod.ext
  · change avStarAction (h.1 * h'.1) (h.2 * h'.2) u +
        thetaTwoTermMap (h * h') c =
      avStarAction h.1 h.2
          (avStarAction h'.1 h'.2 u + thetaTwoTermMap h' c) +
        thetaTwoTermMap h (sl3CAction h'.1 c)
    have huv : avStarAction (h.1 * h'.1) (h.2 * h'.2) u =
        avStarAction h.1 h.2 (avStarAction h'.1 h'.2 u) := by
      have hm := avStarActionHom.map_mul h h'
      change avStarAction (h.1 * h'.1) (h.2 * h'.2) =
        (avStarAction h.1 h.2) * (avStarAction h'.1 h'.2) at hm
      exact congrArg (fun e : AVStar ≃ₗ[k] AVStar => e u) hm
    have hc : sl3CAction (h.1 * h'.1) c =
        sl3CAction h.1 (sl3CAction h'.1 c) := by
      have hm := sl3CActionHom.map_mul h.1 h'.1
      change sl3CActionEquiv (h.1 * h'.1) =
        (sl3CActionEquiv h.1) * (sl3CActionEquiv h'.1) at hm
      exact congrArg (fun e : C ≃ₗ[k] C => e c) hm
    have hd : delta (sl3CAction h.1 (sl3CAction h'.1 c)) =
        sl3AAction h.1 (sl3AAction h'.1 (delta c)) := by
      rw [delta_equivariant_of_squareSpanData h.1 concreteSquareSpanData]
      rw [delta_equivariant_of_squareSpanData h'.1 concreteSquareSpanData]
    have hd' : delta (sl3CAction h'.1 c) = sl3AAction h'.1 (delta c) :=
      delta_equivariant_of_squareSpanData h'.1 concreteSquareSpanData c
    have hterm : avStarAction h.1 h.2 (thetaTwoTermMap h' c) =
        sl3AAction h.1 (delta (sl3CAction h'.1 c)) ⊗ₜ[k]
          (qVStarActionHom h.2) (quadraticDefectLinear h'.2) := by
      simp [thetaTwoTermMap, avStarAction]
    rw [hd'] at hterm
    rw [huv, map_add, hterm]
    change
      avStarAction h.1 h.2 (avStarAction h'.1 h'.2 u) +
          delta (sl3CAction (h.1 * h'.1) c) ⊗ₜ[k]
            quadraticDefectLinear (h.2 * h'.2) =
        avStarAction h.1 h.2 (avStarAction h'.1 h'.2 u) +
          (sl3AAction h.1 (sl3AAction h'.1 (delta c)) ⊗ₜ[k]
            (qVStarActionHom h.2) (quadraticDefectLinear h'.2)) +
          thetaTwoTermMap h (sl3CAction h'.1 c)
    rw [hc, hd]
    rw [show quadraticDefectLinear (h.2 * h'.2) =
        (qVStarActionHom h.2) (quadraticDefectLinear h'.2) +
          quadraticDefectLinear h.2 from
      quadraticDefectLinear_cocycle h.2 h'.2]
    rw [thetaTwoTermMap_apply, hd, TensorProduct.tmul_add, add_assoc]
  · change sl3CAction (h.1 * h'.1) c =
      sl3CAction h.1 (sl3CAction h'.1 c)
    have hm := sl3CActionHom.map_mul h.1 h'.1
    change sl3CActionEquiv (h.1 * h'.1) =
      (sl3CActionEquiv h.1) * (sl3CActionEquiv h'.1) at hm
    exact congrArg (fun e : C ≃ₗ[k] C => e c) hm

/-- The identity law for the second Zhou linear map. Paper: §2. -/
theorem thetaTwoLinearMap_one : thetaTwoLinearMap (1 : H) = LinearMap.id := by
  have hq : quadraticDefectLinear (1 : Q) = 0 := by
    apply LinearMap.ext
    intro v
    simp [quadraticDefectLinear, CharTwo.add_self_eq_zero]
  have ha : avStarAction (1 : SpecialLinear.SL3) (1 : Q) =
      LinearEquiv.refl k AVStar := by
    have hm := avStarActionHom.map_one
    change avStarAction (1 : SpecialLinear.SL3) (1 : Q) =
      LinearEquiv.refl k AVStar at hm
    exact hm
  have hc : sl3CAction (1 : SpecialLinear.SL3) = LinearMap.id := by
    have hm := sl3CActionHom.map_one
    change sl3CActionEquiv (1 : SpecialLinear.SL3) =
      LinearEquiv.refl k C at hm
    exact congrArg LinearEquiv.toLinearMap hm
  have hterm (c : C) : thetaTwoTermMap (1 : H) c = 0 := by
    rw [thetaTwoTermMap_apply]
    change delta (sl3CAction (1 : SpecialLinear.SL3) c) ⊗ₜ[k]
      quadraticDefectLinear (1 : Q) = 0
    rw [hc]
    simp [hq]
  apply LinearMap.ext
  rintro ⟨u, c⟩
  apply Prod.ext
  · change avStarAction (1 : SpecialLinear.SL3) (1 : Q) u +
      thetaTwoTermMap (1 : H) c = u
    rw [hterm c]
    simpa using congrArg (fun e : AVStar ≃ₗ[k] AVStar => e u) ha
  · change sl3CAction (1 : SpecialLinear.SL3) c = c
    exact congrArg (fun e : C →ₗ[k] C => e c) hc

/-- The second Zhou action as a linear equivalence. Paper: §2. -/
def paperThetaTwoLinearEquiv (h : H) : D ≃ₗ[k] D :=
  { toFun := thetaTwoLinearMap h
    invFun := thetaTwoLinearMap h⁻¹
    left_inv := by
      intro d
      have hm := congrArg (fun f : D →ₗ[k] D => f d)
        (thetaTwoLinearMap_mul h⁻¹ h)
      change thetaTwoLinearMap h⁻¹ (thetaTwoLinearMap h d) = d
      calc
        thetaTwoLinearMap h⁻¹ (thetaTwoLinearMap h d) =
            thetaTwoLinearMap (h⁻¹ * h) d := by
          simpa only [LinearMap.comp_apply] using hm.symm
        _ = d := by
          rw [inv_mul_cancel]
          simpa only [LinearMap.id_apply] using
            congrArg (fun f : D →ₗ[k] D => f d) thetaTwoLinearMap_one
    right_inv := by
      intro d
      have hm := congrArg (fun f : D →ₗ[k] D => f d)
        (thetaTwoLinearMap_mul h h⁻¹)
      change thetaTwoLinearMap h (thetaTwoLinearMap h⁻¹ d) = d
      calc
        thetaTwoLinearMap h (thetaTwoLinearMap h⁻¹ d) =
            thetaTwoLinearMap (h * h⁻¹) d := by
          simpa only [LinearMap.comp_apply] using hm.symm
        _ = d := by
          rw [mul_inv_cancel]
          simpa only [LinearMap.id_apply] using
            congrArg (fun f : D →ₗ[k] D => f d) thetaTwoLinearMap_one
    map_add' := by
      intro x y
      exact (thetaTwoLinearMap h).map_add x y
    map_smul' := by
      intro a x
      exact (thetaTwoLinearMap h).map_smul a x }

/-- The second Zhou action as a linear homomorphism. Paper: §2. -/
def paperThetaTwoLinearHom : H →* (D ≃ₗ[k] D) where
  toFun := paperThetaTwoLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro d
    simp [paperThetaTwoLinearEquiv, thetaTwoLinearMap_one]
  map_mul' h h' := by
    apply LinearEquiv.ext
    intro d
    simpa [paperThetaTwoLinearEquiv] using
      congrArg (fun e : D →ₗ[k] D => e d)
        (thetaTwoLinearMap_mul h h')

/-- The second Zhou action on the multiplicative kernel. Paper: §2. -/
def paperThetaTwoHom : H →* MulAut (Multiplicative D) where
  toFun h := additiveEquivToMulAut (paperThetaTwoLinearHom h)
  map_one' := by
    apply MulEquiv.ext
    intro d
    change paperThetaTwoLinearHom 1 d.toAdd = d.toAdd
    simp
  map_mul' h h' := by
    apply MulEquiv.ext
    intro d
    change paperThetaTwoLinearHom (h * h') d.toAdd =
      paperThetaTwoLinearHom h (paperThetaTwoLinearHom h' d.toAdd)
    simp

/-- Contract the finite-dual factor of `A ⊗ V⋆`. Paper: §2. -/
def contractStar (ψ : VStar →ₗ[k] k) : AVStar →ₗ[k] A :=
  TensorProduct.lift (LinearMap.mk₂ k (fun a f => ψ f • a)
    (by intros; rw [smul_add])
    (by intros; rw [smul_smul, smul_smul, mul_comm])
    (by intros; rw [map_add, add_smul])
    (by intros; rw [map_smul, smul_smul, smul_eq_mul]))

@[simp] theorem contractStar_tmul (ψ : VStar →ₗ[k] k) (a : A) (f : VStar) :
    contractStar ψ (a ⊗ₜ[k] f) = ψ f • a := by
  rfl

/-- The constant-one polynomial used in the §4 detector and §§5–6 witnesses. -/
def a0 : A := fun _ => 1

theorem a0_ne_zero : a0 ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 3)
  simp [a0] at h0

/-- The finite quotient acts only on the dual tensor factor of `a0 ⊗ f`. -/
theorem avStar_q_action (q : Q) (f : VStar) :
    avStarAction (1 : SpecialLinear.SL3) q (a0 ⊗ₜ[k] f) =
      a0 ⊗ₜ[k] qVStarActionHom q f := by
  simp [avStarAction]

/-- The two Zhou actions agree on the `SL₃` factor. This is part of the
action construction, used independently by the §4 detector and §5 orbit
arguments. Paper: §2. -/
theorem thetaTwoLinearMap_sl3 (s : SpecialLinear.SL3) (d : D) :
    thetaTwoLinearMap (s, (1 : Q)) d =
      (avStarAction s (1 : Q) d.1, sl3CAction s d.2) := by
  rcases d with ⟨u, c⟩
  apply Prod.ext
  · change avStarAction s (1 : Q) u + thetaTwoTermMap (s, (1 : Q)) c =
      avStarAction s (1 : Q) u
    rw [thetaTwoTermMap_apply]
    have hq : OpenAIPort.quadraticDefectLinear (1 : Q) = 0 := by
      ext w
      simp [OpenAIPort.quadraticDefectLinear, CharTwo.add_self_eq_zero]
    rw [hq]
    simp
  · rfl

/-- Zhou's first concrete semidirect-product group. Paper: §2. -/
noncomputable abbrev paperGammaOne : CountableDiscreteGroup :=
  paperGammaOf paperThetaOneHom

/-- Zhou's second concrete semidirect-product group. Paper: §2. -/
noncomputable abbrev paperGammaTwo : CountableDiscreteGroup :=
  paperGammaOf paperThetaTwoHom

end
end PaperKernel
end Construction
end Connes
