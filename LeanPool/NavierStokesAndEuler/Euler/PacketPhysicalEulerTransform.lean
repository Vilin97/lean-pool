/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.GraphPullback
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Lagrangian
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Measurability.Init

/-! Actual differentiation through the oscillating phase graph and a parent
flow. These identities convert the normalized lifted equation into the
ordinary Euler momentum residual of the physical perturbation. -/

@[expose] public section


noncomputable section

namespace EulerPacketPhysicalTransform

open Set InnerProductSpace ContinuousLinearMap EulerGraphPullback EulerLagrangian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Space time graph, given by `(fst ℝ ℝ E).prod ((graphMap k m).comp (snd ℝ ℝ E))`. -/
def spaceTimeGraph (k : ℝ) (m : E) : (ℝ × E) →L[ℝ] (ℝ × (E × ℝ)) :=
  (fst ℝ ℝ E).prod ((graphMap k m).comp (snd ℝ ℝ E))

theorem spaceTimeGraph_apply (k : ℝ) (m : E) (q : ℝ × E) :
    spaceTimeGraph k m q = (q.1,(q.2,k*⟪m,q.2⟫_ℝ)) := rfl

/-- Graph velocity, given by `κ • F q (z (spaceTimeGraph k m q))`. -/
def graphVelocity (κ k : ℝ) (m : E) (F : ℝ × E → E →L[ℝ] E)
    (z : ℝ × (E × ℝ) → E) (q : ℝ × E) : E :=
  κ • F q (z (spaceTimeGraph k m q))

theorem graphVelocity_hasFDerivAt (κ k : ℝ) (m : E)
    (F : ℝ × E → E →L[ℝ] E) (z : ℝ × (E × ℝ) → E) (q : ℝ × E)
    (DF : (ℝ × E) →L[ℝ] (E →L[ℝ] E)) (Dz : (ℝ × (E × ℝ)) →L[ℝ] E)
    (hF : HasFDerivAt F DF q) (hz : HasFDerivAt z Dz (spaceTimeGraph k m q)) :
    HasFDerivAt (graphVelocity κ k m F z)
      (κ • ((F q).comp (Dz.comp (spaceTimeGraph k m)) +
        DF.flip (z (spaceTimeGraph k m q)))) q :=
  (hF.clm_apply (hz.comp q (spaceTimeGraph k m).hasFDerivAt)).const_smul κ

theorem graphVelocity_fderiv (κ k : ℝ) (m : E)
    (F : ℝ × E → E →L[ℝ] E) (z : ℝ × (E × ℝ) → E) (q : ℝ × E)
    (DF : (ℝ × E) →L[ℝ] (E →L[ℝ] E)) (Dz : (ℝ × (E × ℝ)) →L[ℝ] E)
    (hF : HasFDerivAt F DF q) (hz : HasFDerivAt z Dz (spaceTimeGraph k m q)) (v : ℝ × E) :
    fderiv ℝ (graphVelocity κ k m F z) q v =
      κ • (DF v (z (spaceTimeGraph k m q)) + F q (Dz (spaceTimeGraph k m v))) := by
  rw [(graphVelocity_hasFDerivAt κ k m F z q DF Dz hF hz).fderiv]
  simp only [smul_apply,add_apply,comp_apply,flip_apply]
  rw [add_comm]

/-- The normalized equation is exactly the ordinary Lagrangian perturbation
equation after evaluation on the phase graph, with its actual derivatives. -/
theorem graph_residual_identity (κ k : ℝ) (hκ : k * κ = 1) (m : E)
    (F : ℝ × E → E →L[ℝ] E) (z : ℝ × (E × ℝ) → E) (q : ℝ × E)
    (DF : (ℝ × E) →L[ℝ] (E →L[ℝ] E)) (Dz : (ℝ × (E × ℝ)) →L[ℝ] E)
    (hF : HasFDerivAt F DF q) (hz : HasFDerivAt z Dz (spaceTimeGraph k m q))
    (A : E ≃L[ℝ] E) (hA : F q = A.toContinuousLinearMap) (p : E) :
    fderiv ℝ (graphVelocity κ k m F z) q (1,0) +
      DF (1,0) (A.symm (graphVelocity κ k m F z q)) +
      fderiv ℝ (graphVelocity κ k m F z) q (0,A.symm (graphVelocity κ k m F z q)) +
      A.symm.toContinuousLinearMap.adjoint (κ • p) =
    κ • A (Dz (1,(0,0)) +
      (2 : ℝ) • A.symm (DF (1,0) (z (spaceTimeGraph k m q))) +
      Dz (0,(κ • z (spaceTimeGraph k m q),⟪m,z (spaceTimeGraph k m q)⟫_ℝ)) +
      κ • A.symm (DF (0,z (spaceTimeGraph k m q)) (z (spaceTimeGraph k m q))) +
      A.symm (A.symm.toContinuousLinearMap.adjoint p)) := by
  have hv : A.symm (graphVelocity κ k m F z q) = κ • z (spaceTimeGraph k m q) := by
    simp only [graphVelocity,hA,map_smul,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  have ht : spaceTimeGraph k m (1,0) = (1,(0,0)) := by
    simp only [spaceTimeGraph_apply,inner_zero_right,mul_zero]
  have hs : spaceTimeGraph k m (0,κ • z (spaceTimeGraph k m q)) =
      (0,(κ • z (spaceTimeGraph k m q),⟪m,z (spaceTimeGraph k m q)⟫_ℝ)) := by
    simp only [spaceTimeGraph_apply,real_inner_smul_right,← mul_assoc,hκ,one_mul]
  have ha : ((0 : ℝ),κ • z (spaceTimeGraph k m q)) = κ • (0,z (spaceTimeGraph k m q)) := by
    simp only [Prod.smul_mk,smul_zero]
  rw [hv,graphVelocity_fderiv κ k m F z q DF Dz hF hz,
    graphVelocity_fderiv κ k m F z q DF Dz hF hz,ht,hs,ha]
  simp only [hA,map_smul,smul_apply,map_add,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  module

/-- A literal pullback identity determines the physical momentum residual.
The hypotheses are genuine derivatives of the parent flow and the two fields. -/
theorem euler_residual_of_pullback
    (u w : ℝ × E → E) (p q : ℝ × E → ℝ)
    (X G : ℝ × E → E) (Q : ℝ × E → ℝ) (t : ℝ) (x : E)
    (A : E ≃L[ℝ] E) (Du Dw DG : (ℝ × E) →L[ℝ] E)
    (hXtime : HasDerivAt (fun s => X (s, x)) (u (t, X (t, x))) t)
    (hXspace : HasFDerivAt (fun y => X (t, y)) A.toContinuousLinearMap x)
    (hu : HasFDerivAt u Du (t, X (t, x))) (hw : HasFDerivAt w Dw (t, X (t, x)))
    (hG : HasFDerivAt G DG (t, x))
    (hp : DifferentiableAt ℝ (fun y => p (t, y)) (X (t, x)))
    (hq : DifferentiableAt ℝ (fun y => q (t, y)) (X (t, x)))
    (hwX : ∀ s y, w (s, X (s, y)) = G (s, y))
    (hqX : ∀ y, q (t, X (t, y)) = Q (t, y))
    (hparent : momentumResidual u p (t, X (t, x)) = 0) :
    momentumResidual (fun y => u y+w y) (fun y => p y+q y) (t,X (t,x)) =
      DG (1,0) + Du (0,G (t,x)) + DG (0,A.symm (G (t,x))) +
        A.symm.toContinuousLinearMap.adjoint (gradient (fun y => Q (t,y)) x) := by
  have htime : HasDerivAt (fun s => w (s,X (s,x))) (DG (1,0)) t := by
    have he : (fun s => w (s,X (s,x))) = fun s => G (s,x) := funext (fun s => hwX s x)
    rw [he]
    exact hG.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hspace := hw.comp x ((hasFDerivAt_const t x).prodMk hXspace)
  have he : (fun y => w (t,X (t,y))) = fun y => G (t,y) := funext (hwX t)
  change HasFDerivAt (fun y => w (t,X (t,y))) _ x at hspace
  rw [he] at hspace
  have hgs := hG.comp x (hasFDerivAt_prodMk_right t x)
  have hadv : Dw (0,G (t,x)) = DG (0,A.symm (G (t,x))) := by
    have h := congrArg (fun L : E →L[ℝ] E => L (A.symm (G (t,x)))) (hspace.unique hgs)
    simpa only [comp_apply,prod_apply,zero_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply,inr_apply] using h
  have hpress : gradient (fun y => q (t,y)) (X (t,x)) =
      A.symm.toContinuousLinearMap.adjoint (gradient (fun y => Q (t,y)) x) := by
    have h := gradient_pullback_inverse (fun y => q (t,y)) (fun y => X (t,y)) A x hXspace hq
    have heq : (fun y => q (t,X (t,y))) = fun y => Q (t,y) := funext hqX
    simpa only [Function.comp_def,heq] using h
  rw [euler_perturbation_along_flow u w p q (fun s => X (s,x)) t Du Dw (DG (1,0))
    hXtime hu hw htime hp hq hparent,hwX t x,hadv,hpress]

/-- Inverse coordinates, given by `(q.1,Y q)`. -/
def inverseCoordinates (Y : ℝ × E → E) (q : ℝ × E) : ℝ × E := (q.1,Y q)

/-- Physical velocity, defined pointwise by `graphVelocity κ k m F z (inverseCoordinates Y q)`. -/
def physicalVelocity (κ k : ℝ) (m : E) (F : ℝ × E → E →L[ℝ] E)
    (z : ℝ × (E × ℝ) → E) (Y : ℝ × E → E) : ℝ × E → E :=
  fun q => graphVelocity κ k m F z (inverseCoordinates Y q)

/-- Physical pressure, defined pointwise by `Q (inverseCoordinates Y q)`. -/
def physicalPressure (Q : ℝ × E → ℝ) (Y : ℝ × E → E) : ℝ × E → ℝ :=
  fun q => Q (inverseCoordinates Y q)

/-- The physical perturbation is defined by the actual inverse flow. The
normalized lifted equation, rather than a physical PDE hypothesis, forces
its Euler momentum residual to vanish. -/
theorem physical_euler_momentum
    (κ k : ℝ) (hκ : k * κ = 1) (m : E)
    (F : ℝ × E → E →L[ℝ] E) (z : ℝ × (E × ℝ) → E)
    (u : ℝ × E → E) (p Q : ℝ × E → ℝ) (X Y : ℝ × E → E)
    (t : ℝ) (x : E) (A : E ≃L[ℝ] E)
    (DF : (ℝ × E) →L[ℝ] (E →L[ℝ] E)) (Dz : (ℝ × (E × ℝ)) →L[ℝ] E)
    (Du : (ℝ × E) →L[ℝ] E) (P : E)
    (hleft : ∀ s y, Y (s, X (s, y)) = y)
    (hY : DifferentiableAt ℝ (inverseCoordinates Y) (t, X (t, x)))
    (hXtime : HasDerivAt (fun s => X (s, x)) (u (t, X (t, x))) t)
    (hXspace : HasFDerivAt (fun y => X (t, y)) A.toContinuousLinearMap x)
    (hF : HasFDerivAt F DF (t, x)) (hz : HasFDerivAt z Dz (spaceTimeGraph k m (t, x)))
    (hA : F (t, x) = A.toContinuousLinearMap)
    (hu : HasFDerivAt u Du (t, X (t, x)))
    (hp : DifferentiableAt ℝ (fun y => p (t, y)) (X (t, x)))
    (hQ : DifferentiableAt ℝ (fun y => Q (t, y)) x)
    (hstrain : ∀ v, Du (0, v) = DF (1, 0) (A.symm v))
    (hQgradient : gradient (fun y => Q (t, y)) x = κ • P)
    (hparent : momentumResidual u p (t, X (t, x)) = 0)
    (hlift : Dz (1, (0, 0)) +
      (2 : ℝ) • A.symm (DF (1, 0) (z (spaceTimeGraph k m (t, x)))) +
      Dz (0, (κ • z (spaceTimeGraph k m (t, x)), ⟪m, z (spaceTimeGraph k m (t, x))⟫_ℝ)) +
      κ • A.symm (DF (0, z (spaceTimeGraph k m (t, x))) (z (spaceTimeGraph k m (t, x)))) +
      A.symm (A.symm.toContinuousLinearMap.adjoint P) = 0) :
    momentumResidual (fun q => u q+physicalVelocity κ k m F z Y q)
      (fun q => p q+physicalPressure Q Y q) (t,X (t,x)) = 0 := by
  let G := graphVelocity κ k m F z
  have hG := graphVelocity_hasFDerivAt κ k m F z (t,x) DF Dz hF hz
  have hyx : inverseCoordinates Y (t,X (t,x)) = (t,x) := by
    simp only [inverseCoordinates,hleft]
  have hw : DifferentiableAt ℝ (physicalVelocity κ k m F z Y) (t,X (t,x)) := by
    apply DifferentiableAt.comp _ _ hY
    rw [hyx]
    exact hG.differentiableAt
  have hq : DifferentiableAt ℝ (fun y => physicalPressure Q Y (t,y)) (X (t,x)) := by
    have hy := hY.snd.comp (X (t,x)) (hasFDerivAt_prodMk_right t (X (t,x))).differentiableAt
    change DifferentiableAt ℝ (fun y => Y (t,y)) (X (t,x)) at hy
    have hQ' : DifferentiableAt ℝ (fun y => Q (t,y)) (Y (t,X (t,x))) := by
      rw [hleft]
      exact hQ
    change DifferentiableAt ℝ (fun y => Q (t,Y (t,y))) (X (t,x))
    have hcomp := hQ'.comp (X (t,x)) hy
    exact hcomp
  have hphys := euler_residual_of_pullback u (physicalVelocity κ k m F z Y) p
    (physicalPressure Q Y) X G Q t x A Du (fderiv ℝ (physicalVelocity κ k m F z Y) (t,X (t,x)))
    (fderiv ℝ G (t,x)) hXtime hXspace hu hw.hasFDerivAt hG.differentiableAt.hasFDerivAt hp hq
    (fun s y => by simp only [physicalVelocity,inverseCoordinates,hleft]; rfl)
    (fun y => by simp only [physicalPressure,inverseCoordinates,hleft]) hparent
  rw [hstrain,hQgradient] at hphys
  have he := graph_residual_identity κ k hκ m F z (t,x) DF Dz hF hz A hA P
  rw [hlift,map_zero,smul_zero] at he
  exact hphys.trans he

end EulerPacketPhysicalTransform
