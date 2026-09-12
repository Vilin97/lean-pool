/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerMaximal
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteLifespan
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerRestriction
import LeanPool.NavierStokesAndEuler.Euler.ParentOrdinaryEvolution
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerDifference
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Norms
public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryOperator
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerStability
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerVaryingHorizon
public import LeanPool.NavierStokesAndEuler.Euler.PacketInfiniteConstruction
import LeanPool.NavierStokesAndEuler.Euler.BaseFirstPacketSupport
import LeanPool.NavierStokesAndEuler.Euler.PacketFirstStageSupport
import LeanPool.NavierStokesAndEuler.Euler.ParentChoiceInitialSupport
public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffCurlBound
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import LeanPool.NavierStokesAndEuler.Euler.PacketPressureSeries
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerState
import LeanPool.NavierStokesAndEuler.Euler.ParentPacketHessianSymmetry
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Uniformly compact vorticity of the canonical packet solution

All finite packet horizons contain the maximal open lifespan. H³ stability
therefore passes their common vorticity support to every shorter ordinary
Euler evolution, and hence to the canonical maximal field itself.
-/

section

/-! Zero initial vorticity remains zero along every genuine finite-stage
particle trajectory. The proof uses the conserved antisymmetric pairing
of the particle frame and its time derivative. -/

section

/-! Conservation of the antisymmetric frame pairing for a particle flow
whose acceleration gradient is a symmetric operator. -/

@[expose] public section

noncomputable section

open Set InnerProductSpace
open scoped Topology

namespace Euler.ComparatorBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem frame_wronskian_constant
    (F G H B : ℝ → E →L[ℝ] E) (T : ℝ) (hT : 0 < T)
    (hF : ∀ t ∈ Icc 0 T, HasDerivWithinAt F (G t) (Icc 0 T) t)
    (hG : ∀ t ∈ Icc 0 T, HasDerivWithinAt G (H t) (Icc 0 T) t)
    (hH : ∀ t ∈ Icc 0 T, ∀ v, H t v = -(B t (F t v)))
    (hB : ∀ t ∈ Icc 0 T, (B t).IsSymmetric)
    (v w : E) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ⟪G t v, F t w⟫_ℝ - ⟪F t v, G t w⟫_ℝ =
      ⟪G 0 v, F 0 w⟫_ℝ - ⟪F 0 v, G 0 w⟫_ℝ := by
  let q : ℝ → ℝ := fun r => ⟪G r v, F r w⟫_ℝ - ⟪F r v, G r w⟫_ℝ
  have hd (r : ℝ) (hr : r ∈ Icc 0 T) :
      HasDerivWithinAt q 0 (Icc 0 T) r := by
    have hfv := (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp_hasDerivWithinAt r (hF r hr)
    have hfw := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp_hasDerivWithinAt r (hF r hr)
    have hgv := (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp_hasDerivWithinAt r (hG r hr)
    have hgw := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp_hasDerivWithinAt r (hG r hr)
    have hh := (hgv.inner ℝ hfw).sub (hfv.inner ℝ hgw)
    convert! hh using 1
    change 0 = (⟪G r v, G r w⟫_ℝ + ⟪H r v, F r w⟫_ℝ) -
      (⟪F r v, H r w⟫_ℝ + ⟪G r v, G r w⟫_ℝ)
    have hb : ⟪B r (F r v), F r w⟫_ℝ = ⟪F r v, B r (F r w)⟫_ℝ := hB r hr _ _
    rw [hH r hr v, hH r hr w, inner_neg_left, inner_neg_right, hb]
    ring
  exact constant_of_derivWithin_zero
    (fun r hr => (hd r hr).differentiableWithinAt)
    (fun r hr => (hd r ⟨hr.1, hr.2.le⟩).derivWithin
      (uniqueDiffOn_Icc hT r ⟨hr.1, hr.2.le⟩)) t ht

/-- An initially symmetric Eulerian velocity gradient stays symmetric.
The two frame identities identify that gradient as `G * F⁻¹`. -/
theorem strain_symmetric_of_frame_wronskian
    (F G H B S J : ℝ → E →L[ℝ] E) (T : ℝ) (hT : 0 < T)
    (hF : ∀ t ∈ Icc 0 T, HasDerivWithinAt F (G t) (Icc 0 T) t)
    (hG : ∀ t ∈ Icc 0 T, HasDerivWithinAt G (H t) (Icc 0 T) t)
    (hH : ∀ t ∈ Icc 0 T, ∀ v, H t v = -(B t (F t v)))
    (hB : ∀ t ∈ Icc 0 T, (B t).IsSymmetric)
    (hS : ∀ t ∈ Icc 0 T, ∀ v, G t v = S t (F t v))
    (hJ : ∀ t ∈ Icc 0 T, ∀ v, F t (J t v) = v)
    (hzero : (S 0).IsSymmetric)
    (t : ℝ) (ht : t ∈ Icc 0 T) : (S t).IsSymmetric := by
  intro v w
  have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hh := frame_wronskian_constant F G H B T hT hF hG hH hB (J t v) (J t w) t ht
  rw [hS t ht, hS t ht, hJ t ht, hJ t ht, hS 0 hz, hS 0 hz] at hh
  have hs : ⟪S 0 (F 0 (J t v)), F 0 (J t w)⟫_ℝ =
      ⟪F 0 (J t v), S 0 (F 0 (J t w))⟫_ℝ := hzero _ _
  rw [hs] at hh
  exact sub_eq_zero.mp (hh.trans (sub_self _))

end Euler.ComparatorBridge

end
end

end

section

/-!
# Curl Matrix Symmetry
-/

@[expose] public section

noncomputable section

open EulerSmoothLimit
open scoped RealInnerProductSpace

namespace EulerMeanBoundary

/-- The curl vanishes precisely when the real derivative matrix is symmetric. -/
theorem curlMatrix_eq_zero_iff_isSymmetric (A : Space →L[ℝ] Space) :
    curlMatrix A = 0 ↔ A.IsSymmetric := by
  constructor
  · intro h
    have hc (i : Fin 3) :
        (A (EuclideanSpace.single (i+1) 1)) (i+2) -
          (A (EuclideanSpace.single (i+2) 1)) (i+1) = 0 := by
      exact congrArg (fun v : Space => v i) h
    have h0 := hc 0
    have h1 := hc 1
    have h2 := hc 2
    change (A (EuclideanSpace.single 1 1)) 2 - (A (EuclideanSpace.single 2 1)) 1 = 0 at h0
    change (A (EuclideanSpace.single 2 1)) 0 - (A (EuclideanSpace.single 0 1)) 2 = 0 at h1
    change (A (EuclideanSpace.single 0 1)) 1 - (A (EuclideanSpace.single 1 1)) 0 = 0 at h2
    have heq (i j : Fin 3) :
        (A (EuclideanSpace.single i 1)) j = (A (EuclideanSpace.single j 1)) i := by
      fin_cases i <;> fin_cases j <;>
        first | rfl | exact sub_eq_zero.mp h0 | exact sub_eq_zero.mp h1 |
          exact sub_eq_zero.mp h2 | exact (sub_eq_zero.mp h0).symm |
          exact (sub_eq_zero.mp h1).symm | exact (sub_eq_zero.mp h2).symm
    intro x y
    have hx := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
    have hy := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr y
    rw [← hx, ← hy]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      inner_smul_right, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_right, map_one, one_mul, PiLp.smul_apply, smul_eq_mul,
          starRingEnd_apply, star_trivial]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact heq j i
  · intro h
    ext i
    have hi := h (EuclideanSpace.single (i+1) 1) (EuclideanSpace.single (i+2) 1)
    simpa [curlMatrix, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_right, sub_eq_zero] using hi

end EulerMeanBoundary

end
end

end

section

/-! The scalar pressure of a finite packet evolution is spatially smooth
because its actual gradient is smooth. Its curvature operator is therefore
symmetric, as required by the particle-map vorticity transport argument. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set InnerProductSpace EulerSmoothLimit
open scoped ContDiff

variable {A : Parent} (E : Evolution A)

theorem pressure_contDiff (t : Icc (0 : ℝ) A.T) :
    ContDiff ℝ ∞ (fun x => E.pressure (t,x)) := by
  apply contDiff_infty_iff_fderiv.mpr
  refine ⟨E.pressure_differentiable t,?_⟩
  have he : fderiv ℝ (fun x => E.pressure (t,x)) = (toDual ℝ Space) ∘ E.force t := by
    funext x
    rw [Function.comp_apply,← E.pressure_gradient t x,toDual_gradient]
  rw [he]
  exact (toDual ℝ Space).contDiff.comp (E.force_smooth t)

include E in
theorem curvature_symmetric (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.curvature.field t x).IsSymmetric := by
  rw [E.curvature_eq]
  have hf : E.force t = gradient (fun y => E.pressure (t,y)) :=
    funext (fun y => (E.pressure_gradient t y).symm)
  rw [hf]
  exact hessian_isSymmetric _ ((E.pressure_contDiff t).of_le (by simp)) _

end EulerParentPacketFrames.Evolution

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set InnerProductSpace EulerSmoothLimit EulerMeanBoundary EulerVectorCalculus
    EulerMeanCutoffCurl
  EulerVolterraConvolution EulerPacketCofactor Euler.ComparatorBridge
open scoped ContDiff

variable {A : Parent} (E : Evolution A)

include E in
theorem strain_symmetric_along_label (x : Space)
    (hzero : (A.strain.field A.zeroTime x).IsSymmetric)
    (t : Icc (0 : ℝ) A.T) : (A.strain.field t x).IsSymmetric := by
  let F : ℝ → EndSpace := fun r => A.frame.field (projIcc 0 A.T A.T_pos.le r) x
  let G : ℝ → EndSpace := fun r => A.first.field (projIcc 0 A.T A.T_pos.le r) x
  let H : ℝ → EndSpace := fun r => A.second.field (projIcc 0 A.T A.T_pos.le r) x
  let B : ℝ → EndSpace := fun r => A.curvature.field (projIcc 0 A.T A.T_pos.le r) x
  let S : ℝ → EndSpace := fun r => A.strain.field (projIcc 0 A.T A.T_pos.le r) x
  let J : ℝ → EndSpace := fun r => A.inverse.field (projIcc 0 A.T A.T_pos.le r) x
  have hF (r : ℝ) (hr : r ∈ Icc 0 A.T) :
      HasDerivWithinAt F (G r) (Icc 0 A.T) r := by
    simpa only [F,G,SmoothTimeField.realField,extendPath,
      projIcc_of_mem A.T_pos.le hr] using A.frame_time ⟨r,hr⟩ x
  have hG (r : ℝ) (hr : r ∈ Icc 0 A.T) :
      HasDerivWithinAt G (H r) (Icc 0 A.T) r := by
    simpa only [G,H,SmoothTimeField.realField,extendPath,
      projIcc_of_mem A.T_pos.le hr] using A.first_time ⟨r,hr⟩ x
  have hh := strain_symmetric_of_frame_wronskian F G H B S J A.T A.T_pos hF hG
    (fun r _ v => A.second_equation (projIcc 0 A.T A.T_pos.le r) x v)
    (fun r _ => E.curvature_symmetric (projIcc 0 A.T A.T_pos.le r) x)
    (fun r _ v => A.strain_equation (projIcc 0 A.T A.T_pos.le r) x v)
    (fun r _ v => A.inverse_right (projIcc 0 A.T A.T_pos.le r) x v)
    (by
      intro v w
      simpa only [S,Parent.zeroTime,projIcc_of_mem A.T_pos.le (show (0 : ℝ) ∈ Icc 0 A.T from
        ⟨le_rfl,A.T_pos.le⟩)] using hzero v w) t t.property
  intro v w
  simpa only [S,projIcc_of_mem A.T_pos.le t.property] using hh v w

/-- This statement needs only the actual parent Euler evolution, with no
additional Sobolev regularity or support hypotheses. -/
theorem curl_eq_zero_along_position (a : Space)
    (hzero : vectorCurl (fun x => E.velocity (0, x)) a = 0)
    (t : Icc (0 : ℝ) A.T) :
    vectorCurl (fun x => E.velocity (t,x)) (A.position t a) = 0 := by
  have hscale : A.ell • (A.ell⁻¹ • a) = a := by
    rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  have hinit : (A.strain.field A.zeroTime (A.ell⁻¹ • a)).IsSymmetric := by
    rw [E.strain_eq,hscale,A.position_initial]
    apply (curlMatrix_eq_zero_iff_isSymmetric _).mp
    rw [← vectorCurl_eq_matrix _ a ((E.velocity_smooth A.zeroTime).differentiable (by simp) a)]
    exact hzero
  have hsym := E.strain_symmetric_along_label (A.ell⁻¹ • a) hinit t
  rw [E.strain_eq,hscale] at hsym
  rw [vectorCurl_eq_matrix _ _ ((E.velocity_smooth t).differentiable (by simp) _)]
  exact (curlMatrix_eq_zero_iff_isSymmetric _).mpr hsym

end EulerParentPacketFrames.Evolution

end
end

end

section

/-!
# Uniform confinement of the constructed particle maps

Each selected successor retains the proved quarter-power displacement bound
for its change of particle labels. Composition adds displacements without a
factor involving the parent derivative. The scale construction already bounds
the sum of these quarter-power costs. Thus all stages carry every fixed ball
of initial labels into one fixed ball of physical positions.

This is a statement about the actual selected packet family, not an assumed
bound on its velocity or velocity gradients. Vorticity confinement additionally
requires its transport identity along these particle maps.
-/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerGraphInvariantFlow

variable (A : EulerParentPacketFrames.Parent)
  {P : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P A.T)
  (k : ℝ) (m : Vector3) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

theorem child_displacement_norm_le {M δ : ℝ}
    (hparent : ∀ (t : Icc (0 : ℝ) A.T) (x : Space), ‖A.displacement.field t x‖ ≤ M)
    (hsmall : ∀ (t : Icc (0 : ℝ) A.T) (x : Space),
      ‖(G.displacementField k m A.ell A.ell_pos t).field x‖ ≤ δ)
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    ‖(A.child G k m hgraph nextEll hnext hnext1).displacement.field t x‖ ≤ M + δ := by
  change ‖(EulerChildParticleTime.displacement A.displacement
    (G.physicalDisplacementCoefficient k m A.ell)).field t x‖ ≤ M + δ
  simp only [EulerChildParticleTime.displacement_apply,
    G.physicalDisplacementCoefficient_eq k m A.ell A.ell_pos]
  exact (norm_add_le _ _).trans (add_le_add (hparent t _) (hsmall t x))

end EulerParentPacketFrames.Parent

namespace EulerPacketInduction.Stage

open Set Finset EulerSmoothLimit EulerParentPacketFrames EulerPacketInductionScales
  EulerPacketSourceScaleSequence EulerPacketLowConstants EulerParentNeighborThreshold
  EulerTimeIntervalRestriction

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B}

theorem forwardNext_displacement_norm_le (P : Stage S 0)
    (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)
    {M : ℝ}
    (hparent : ∀ (t : Icc (0 : ℝ) P.parent.T) (x : Space),
      ‖P.parent.displacement.field t x‖ ≤ M)
    (t : Icc (0 : ℝ) (P.forwardNext hq hB).parent.T) (x : Space) :
    ‖(P.forwardNext hq hB).parent.displacement.field t x‖ ≤
      M + (frequency S.J S.X 0)^(-(1/4 : ℝ)) := by
  let F := P.chooseForward hq hB
  exact P.restrictedParent.child_displacement_norm_le F.flow (frequency S.J S.X 0)
    (P.forwardInput hq hB).normal F.graph (supportScale S.J S.X 1)
    (S.support_pos 1) (S.support_one 1)
    (fun s y => hparent (initialInclusion P.parent.T P.nextHorizon P.nextHorizon_le s) y)
    F.displacement_bound t x

theorem joinedNext_displacement_norm_le {n : ℕ} (P : Stage S n) (hn : n ≠ 0)
    (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)
    {M : ℝ}
    (hparent : ∀ (t : Icc (0 : ℝ) P.parent.T) (x : Space),
      ‖P.parent.displacement.field t x‖ ≤ M)
    (t : Icc (0 : ℝ) (P.joinedNext hn hq hB).parent.T) (x : Space) :
    ‖(P.joinedNext hn hq hB).parent.displacement.field t x‖ ≤
      M + (frequency S.J S.X n)^(-(1/4 : ℝ)) := by
  let F := P.chooseJoined hn hq hB
  exact P.restrictedParent.child_displacement_norm_le F.flow (frequency S.J S.X n)
    (P.joinedInput hn hq hB).normal F.graph (supportScale S.J S.X (n+1))
    (S.support_pos (n+1)) (S.support_one (n+1))
    (fun s y => hparent (initialInclusion P.parent.T P.nextHorizon P.nextHorizon_le s) y)
    F.displacement_bound t x

theorem successor_displacement_norm_le {n : ℕ} (P : Stage S n)
    (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)
    {M : ℝ}
    (hparent : ∀ (t : Icc (0 : ℝ) P.parent.T) (x : Space),
      ‖P.parent.displacement.field t x‖ ≤ M)
    (t : Icc (0 : ℝ) (P.successor hq hB).parent.T) (x : Space) :
    ‖(P.successor hq hB).parent.displacement.field t x‖ ≤
      M + (frequency S.J S.X n)^(-(1/4 : ℝ)) := by
  cases n with
  | zero => exact P.forwardNext_displacement_norm_le hq hB hparent t x
  | succ n => exact P.joinedNext_displacement_norm_le (Nat.succ_ne_zero n) hq hB hparent t x

end EulerPacketInduction.Stage

namespace EulerPacketInduction

open Set Finset EulerSmoothLimit EulerParentPacketFrames EulerPacketInductionScales
  EulerPacketSourceScaleSequence EulerPacketLowConstants EulerParentNeighborThreshold

variable {q : ℕ} {B : ℝ} (S : Scales (q : ℝ) B) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)

theorem stages_displacement_norm_le_partial_sum (n : ℕ) :
    ∀ (t : Icc (0 : ℝ) (stages S hq hB n).parent.T) (x : Space),
      ‖(stages S hq hB n).parent.displacement.field t x‖ ≤
        ‖(stages S hq hB 0).parent.displacement.field‖ +
          ∑ i ∈ range n, (frequency S.J S.X i)^(-(1/4 : ℝ)) := by
  induction n with
  | zero =>
    intro t x
    simpa only [range_zero,sum_empty,add_zero] using
      (BoundedContinuousFunction.norm_coe_le_norm
        ((stages S hq hB 0).parent.displacement.field t) x).trans
          (ContinuousMap.norm_coe_le_norm (stages S hq hB 0).parent.displacement.field t)
  | succ n ih =>
    intro t x
    rw [sum_range_succ, ← add_assoc]
    exact (stages S hq hB n).successor_displacement_norm_le hq hB ih t x

/-- Particle displacement cap, given by `‖(stages S hq hB 0).parent.displacement.field‖ + S.δ`. -/
def particleDisplacementCap : ℝ := ‖(stages S hq hB 0).parent.displacement.field‖ + S.δ

theorem stages_displacement_norm_le (n : ℕ)
    (t : Icc (0 : ℝ) (stages S hq hB n).parent.T) (x : Space) :
    ‖(stages S hq hB n).parent.displacement.field t x‖ ≤ particleDisplacementCap S hq hB := by
  exact (stages_displacement_norm_le_partial_sum S hq hB n t x).trans
    (add_le_add le_rfl (EulerPacketPressureScale.finite_sum_le S.correction_series n))

theorem stages_position_mapsTo_closedBall (R : ℝ) (n : ℕ)
    (t : Icc (0 : ℝ) (stages S hq hB n).parent.T) :
    MapsTo ((stages S hq hB n).parent.position t) (Metric.closedBall 0 R)
      (Metric.closedBall 0 (R + particleDisplacementCap S hq hB)) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  exact (norm_add_le _ _).trans
    (add_le_add hx (stages_displacement_norm_le S hq hB n t x))

theorem packets_position_mapsTo_closedBall (R : ℝ) (n : ℕ)
    (t : Icc (0 : ℝ) (packets n).parent.T) :
    MapsTo ((packets n).parent.position t) (Metric.closedBall 0 R)
      (Metric.closedBall 0 (R + particleDisplacementCap constructionScales le_rfl le_rfl)) :=
  stages_position_mapsTo_closedBall constructionScales le_rfl le_rfl R n t

end EulerPacketInduction

end
end

end

section

/-!
# Confinement by summable changes of particle labels

The packet construction composes particle maps as `Xₙ₊₁ = Xₙ ∘ Yₙ`.
Bounding the displacement of this composition costs the sum of the two
displacements, without a derivative bound on `Xₙ`. Consequently summable
changes of labels confine the images of every fixed initial ball uniformly
over all stages, including when the velocity gradients are unbounded.

The horizon predicate permits the time intervals to shrink with the stage.
The hypotheses below are explicit: this file does not yet assert their
instantiation for the packet choices made by the development.
-/

@[expose] public section

namespace Euler.ComparatorBridge

open Finset Set

variable {E : Type*} [NormedAddCommGroup E]

theorem displacement_comp_le (X Y : E → E) {M δ : ℝ}
    (hX : ∀ x, ‖X x - x‖ ≤ M) (hY : ∀ x, ‖Y x - x‖ ≤ δ) (x : E) :
    ‖X (Y x) - x‖ ≤ M + δ := by
  calc
    ‖X (Y x) - x‖ = ‖(X (Y x) - Y x) + (Y x - x)‖ := by
      rw [sub_add_sub_cancel]
    _ ≤ ‖X (Y x) - Y x‖ + ‖Y x - x‖ := norm_add_le _ _
    _ ≤ M + δ := add_le_add (hX _) (hY _)

omit [NormedAddCommGroup E] in
/-- A transported quantity that starts supported in `K` remains supported in
the region containing its transported labels. Only preservation of zero is
needed; the transported quantity need not be constant along trajectories. -/
theorem support_subset_of_transport {F : Type*} [Zero F]
    (X Y : E → E) (w₀ w : E → F) {K L : Set E}
    (hright : ∀ x, X (Y x) = x) (hmap : MapsTo X K L)
    (hinitial : Function.support w₀ ⊆ K)
    (htransport : ∀ a, w₀ a = 0 → w (X a) = 0) :
    Function.support w ⊆ L := by
  classical
  intro x hx
  by_contra houtside
  have ha : Y x ∉ K := fun hy => houtside (hright x ▸ hmap hy)
  have hzero : w₀ (Y x) = 0 := by
    by_contra hne
    exact ha (hinitial (Function.mem_support.mpr hne))
  have h := htransport (Y x) hzero
  rw [hright x] at h
  exact (Function.mem_support.mp hx) h

variable {Time : Type*} (H : ℕ → Time → Prop)
  (X Y : ℕ → Time → E → E) (M : ℝ) (δ : ℕ → ℝ)
  (hbase : ∀ t, H 0 t → ∀ x, ‖X 0 t x - x‖ ≤ M)
  (hnest : ∀ n t, H (n + 1) t → H n t)
  (hstep : ∀ n t, H (n + 1) t → ∀ x, X (n + 1) t x = X n t (Y n t x))
  (hsmall : ∀ n t, H (n + 1) t → ∀ x, ‖Y n t x - x‖ ≤ δ n)

include hbase hnest hstep hsmall in
theorem stage_displacement_le_partial_sum (n : ℕ) (t : Time) (ht : H n t) (x : E) :
    ‖X n t x - x‖ ≤ M + ∑ i ∈ range n, δ i := by
  induction n generalizing x with
  | zero => simpa using hbase t ht x
  | succ n ih =>
    rw [hstep n t ht, sum_range_succ, ← add_assoc]
    exact displacement_comp_le (X n t) (Y n t)
      (fun y => ih (hnest n t ht) y) (hsmall n t ht) x

include hbase hnest hstep hsmall in
theorem stage_displacement_le_of_partial_sums {C : ℝ}
    (hC : ∀ n, ∑ i ∈ range n, δ i ≤ C)
    (n : ℕ) (t : Time) (ht : H n t) (x : E) :
    ‖X n t x - x‖ ≤ M + C := by
  exact (stage_displacement_le_partial_sum H X Y M δ hbase hnest hstep hsmall n t ht x).trans
    (add_le_add le_rfl (hC n))

include hbase hnest hstep hsmall in
theorem stage_mapsTo_closedBall_of_partial_sums {C : ℝ}
    (hC : ∀ n, ∑ i ∈ range n, δ i ≤ C)
    (R : ℝ) (n : ℕ) (t : Time) (ht : H n t) :
    MapsTo (X n t) (Metric.closedBall 0 R) (Metric.closedBall 0 (R + M + C)) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  calc
    ‖X n t x‖ = ‖x + (X n t x - x)‖ := by rw [add_comm x, sub_add_cancel]
    _ ≤ ‖x‖ + ‖X n t x - x‖ := norm_add_le _ _
    _ ≤ R + (M + C) := add_le_add hx
      (stage_displacement_le_of_partial_sums H X Y M δ hbase hnest hstep hsmall hC n t ht x)
    _ = R + M + C := (add_assoc _ _ _).symm

include hbase hnest hstep hsmall in
theorem stage_displacement_le_tsum (hδ : Summable δ) (hδ0 : ∀ n, 0 ≤ δ n)
    (n : ℕ) (t : Time) (ht : H n t) (x : E) :
    ‖X n t x - x‖ ≤ M + ∑' i, δ i := by
  exact (stage_displacement_le_partial_sum H X Y M δ hbase hnest hstep hsmall n t ht x).trans
    (add_le_add le_rfl (hδ.sum_le_tsum (range n) (fun i _ => hδ0 i)))

include hbase hnest hstep hsmall in
theorem stage_mapsTo_closedBall (hδ : Summable δ) (hδ0 : ∀ n, 0 ≤ δ n)
    (R : ℝ) (n : ℕ) (t : Time) (ht : H n t) :
    MapsTo (X n t) (Metric.closedBall 0 R) (Metric.closedBall 0 (R + M + ∑' i, δ i)) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  calc
    ‖X n t x‖ = ‖x + (X n t x - x)‖ := by rw [add_comm x, sub_add_cancel]
    _ ≤ ‖x‖ + ‖X n t x - x‖ := norm_add_le _ _
    _ ≤ R + (M + ∑' i, δ i) := add_le_add hx
      (stage_displacement_le_tsum H X Y M δ hbase hnest hstep hsmall hδ hδ0 n t ht x)
    _ = R + M + ∑' i, δ i := (add_assoc _ _ _).symm

end Euler.ComparatorBridge

end

end

section

/-!
# Common initial support of every constructed packet stage

The selected forward and joined corrections retain the common initial
support. Therefore every finite stage has initial velocity, all its spatial
derivatives, and initial vorticity supported in the closed ball of radius two.
-/

section

/-! The curl of a differentiable field has support inside the support of that
field. This elementary locality fact does not assume spatial norm bounds. -/

@[expose] public section

namespace EulerMeanCutoffCurl

open EulerSmoothLimit EulerMeanBoundary

theorem tsupport_vectorCurl_subset (f : Space → Space) (hf : Differentiable ℝ f) :
    tsupport (vectorCurl f) ⊆ tsupport f := by
  have hcurl : vectorCurl f = curlMatrix ∘ fderiv ℝ f :=
    funext (fun x => vectorCurl_eq_matrix f x (hf x))
  have hzero : curlMatrix 0 = 0 := by
    ext i
    simp [curlMatrix]
  rw [hcurl]
  exact (tsupport_comp_subset hzero (fderiv ℝ f)).trans (tsupport_fderiv_subset ℝ)

end EulerMeanCutoffCurl

end

end

@[expose] public section

noncomputable section

namespace EulerPacketInduction.Stage

open Set EulerSmoothLimit EulerParentPacketFrames EulerPacketSupport
  EulerPacketInductionScales EulerPacketLowConstants EulerParentNeighborThreshold
  EulerPacketSourceScaleSequence

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B}

theorem joinedNext_initial_support {n : ℕ} (P : Stage S n) (hn : n ≠ 0)
    (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)
    (hP : tsupport (fun x => P.state.evolution.velocity (0, x)) ⊆ Metric.closedBall 0 2) :
    tsupport (fun x => (P.joinedNext hn hq hB).state.evolution.velocity (0, x)) ⊆
      Metric.closedBall 0 2 :=
  GeometryJoinedChoice.initial_support (P.joinedInput hn hq hB) P.restrictedState
    (frequency S.J S.X n) (S.normal_frequency n) (supportScale S.J S.X (n+1))
    (S.support_pos (n+1)) (S.support_one (n+1)) (P.chooseJoined hn hq hB) symmetric hP

theorem successor_initial_support {n : ℕ} (P : Stage S n)
    (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)
    (hP : tsupport (fun x => P.state.evolution.velocity (0, x)) ⊆ Metric.closedBall 0 2) :
    tsupport (fun x => (P.successor hq hB).state.evolution.velocity (0, x)) ⊆
      Metric.closedBall 0 2 := by
  cases n with
  | zero => exact P.forwardNext_initial_support hq hB hP
  | succ n => exact P.joinedNext_initial_support (Nat.succ_ne_zero n) hq hB hP

end EulerPacketInduction.Stage

namespace EulerPacketInduction

open Set EulerSmoothLimit EulerParentPacketFrames EulerPacketInductionScales
  EulerPacketLowConstants EulerParentNeighborThreshold EulerMeanCutoffCurl

variable {q : ℕ} {B : ℝ} (S : Scales (q : ℝ) B) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)

theorem stages_initial_support (n : ℕ) :
    tsupport (fun x => (stages S hq hB n).state.evolution.velocity (0,x)) ⊆
      Metric.closedBall 0 2 := by
  induction n with
  | zero => exact S.firstStage_initial_support
  | succ n ih => exact (stages S hq hB n).successor_initial_support hq hB ih

theorem stages_initial_derivatives_support (n m : ℕ) :
    tsupport (iteratedFDeriv ℝ m (fun x => (stages S hq hB n).state.evolution.velocity (0,x))) ⊆
      Metric.closedBall 0 2 :=
  (tsupport_iteratedFDeriv_subset m).trans (stages_initial_support S hq hB n)

theorem stages_initial_curl_support (n : ℕ) :
    tsupport (vectorCurl (fun x => (stages S hq hB n).state.evolution.velocity (0,x))) ⊆
      Metric.closedBall 0 2 := by
  apply (tsupport_vectorCurl_subset _ ?_).trans (stages_initial_support S hq hB n)
  exact ((stages S hq hB n).state.evolution.velocity_smooth
    (stages S hq hB n).parent.zeroTime).differentiable (by simp)

theorem packets_initial_support (n : ℕ) :
    tsupport (fun x => (packets n).state.evolution.velocity (0,x)) ⊆ Metric.closedBall 0 2 :=
  stages_initial_support constructionScales le_rfl le_rfl n

theorem packets_initial_curl_support (n : ℕ) :
    tsupport (vectorCurl (fun x => (packets n).state.evolution.velocity (0,x))) ⊆
      Metric.closedBall 0 2 :=
  stages_initial_curl_support constructionScales le_rfl le_rfl n

end EulerPacketInduction

end
end

end

section

/-!
# Every packet horizon covers the canonical lifespan

The horizons of the actual recursive family decrease. If its limiting
datum had an evolution through any one of those horizons, comparison
with the tail of the packet family would bound the divergent activation
gradients. This applies the proved varying-horizon H³ stability theorem.
-/

@[expose] public section

noncomputable section

namespace EulerPacketInduction

open Set Filter EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPhysicalL2Scaling EulerOrdinarySobolev EulerSmoothL2Series
  EulerPacketSourceScaleSequence
open scoped Topology

theorem packets_horizon_succ (n : ℕ) :
    (packets (n+1)).parent.T = (packets n).nextHorizon := by
  rw [(packets (n+1)).horizon_eq]
  have ht : (packets (n+1)).time = (packets n).nextTime :=
    stages_time constructionScales le_rfl le_rfl n
  rw [ht]
  rfl

theorem packets_horizon_antitone : Antitone (fun n => (packets n).parent.T) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [packets_horizon_succ]
  exact (packets n).nextHorizon_le

theorem initialDatum_no_packet_horizon (N : ℕ) :
    ¬ HasEulerEvolution initialDatum (packets N).parent.T := by
  rintro ⟨hT,U,hU₀⟩
  let durations : ℕ → ℝ := fun n => (packets (n+N)).parent.T
  let hD : ∀ n, 0 ≤ durations n := fun n => (packets (n+N)).parent.T_pos.le
  let hDT : ∀ n, durations n ≤ (packets N).parent.T :=
    fun n => packets_horizon_antitone (by omega)
  let V : ∀ n, Evolution (durations n) (hD n) :=
    fun n => (packets (n+N)).state.regularity.ordinaryEvolution
  let times : ∀ n, Icc (0 : ℝ) (durations n) :=
    fun n => ⟨(packets (n+N)).time,(packets (n+N)).time_nonneg,
      (packets (n+N)).time_lt.le⟩
  have hfield (n : ℕ) :
      (((U.restrictTime (durations n) (hD n) (hDT n)).difference (V n))
        ⟨0,le_rfl,hD n⟩).field =
      (fun x => (packets (n+N)).state.evolution.velocity (0,x))-initialDatum.field := by
    funext x
    rw [Evolution.difference,fieldSub_field]
    change ((packets (n+N)).state.regularity.velocity
      ⟨0,le_rfl,(packets (n+N)).parent.T_pos.le⟩).field x -
        (U.velocity ⟨0,le_rfl,hT.le⟩).field x = _
    rw [hU₀,← (packets (n+N)).state.regularity.velocity_match
      ⟨0,le_rfl,(packets (n+N)).parent.T_pos.le⟩ x]
    rfl
  have hnorm (n : ℕ) :
      tensorNorm 3 ((U.restrictTime (durations n) (hD n) (hDT n)).difference
        (V n) ⟨0,le_rfl,hD n⟩) =
      derivativeSum 3 ((fun x => (packets (n+N)).state.evolution.velocity (0,x)) -
        initialDatum.field) := by
    rw [tensorNorm_eq_derivativeSum,hfield]
  have hlim : Tendsto (fun n => tensorNorm 3
      ((U.restrictTime (durations n) (hD n) (hDT n)).difference (V n)
        ⟨0,le_rfl,hD n⟩)) atTop (𝓝 0) := by
    simpa only [hnorm, Function.comp_def] using
      (initialDatum_Hm 3).comp (tendsto_add_atTop_nat N)
  apply U.no_gradient_escape_of_initial_tendsto_varying durations hD hDT V hlim times
  have hactual (n : ℕ) : ((V n).velocity (times n)).field =
      fun x => (packets (n+N)).state.evolution.velocity ((packets (n+N)).time,x) :=
    funext (fun x => ((packets (n+N)).state.regularity.velocity_match (times n) x).symm)
  have heq : (fun n => ‖fderiv ℝ ((V n).velocity (times n)).field 0‖) =
      fun n => (packets (n+N)).activationGradient := by
    funext n
    rw [hactual]
    rfl
  rw [heq]
  exact packets_gradient_atTop.comp (tendsto_add_atTop_nat N)

theorem lifespan_le_packet_horizon (n : ℕ) :
    lifespan.duration ≤ (packets n).parent.T := by
  by_contra h
  exact initialDatum_no_packet_horizon n
    (lifespan.shorter (packets n).parent.T (packets n).parent.T_pos (lt_of_not_ge h))

end EulerPacketInduction

end
end

end

section

/-! Convergence of ordinary Euler velocities in the initial H³ norm gives
pointwise convergence of their curls at every time in their common interval. -/

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev.Evolution

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerSmoothSobolev EulerMeanBoundary EulerMeanCutoffCurl
open scoped ContDiff Topology

variable {T : ℝ} {hT : 0 ≤ T}

theorem sampled_h3_tendsto_of_initial_h3 (U : Evolution T hT)
    (V : ℕ → Evolution T hT)
    (hinit : Tendsto
      (fun n => tensorNorm 3 (U.difference (V n) ⟨0, le_rfl, hT⟩)) atTop (𝓝 0))
    (times : ℕ → Icc (0 : ℝ) T) :
    Tendsto (fun n => tensorNorm 3 (U.difference (V n) (times n))) atTop (𝓝 0) := by
  let ε : ℕ → ℝ := fun n =>
    tensorNorm 3 (U.difference (V n) ⟨0, le_rfl, hT⟩) + 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := by
    intro n
    exact add_pos_of_nonneg_of_pos (tensorNorm_nonneg 3 _) (by positivity)
  have hlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [add_zero] using
      hinit.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply U.sampled_h3_tendsto_zero V ε hε hlim _ times
  intro n
  exact le_add_of_nonneg_right (by positivity)

theorem curl_tendsto_of_initial_h3 (U : Evolution T hT) (V : ℕ → Evolution T hT)
    (hinit : Tendsto
      (fun n => tensorNorm 3 (U.difference (V n) ⟨0, le_rfl, hT⟩)) atTop (𝓝 0))
    (t : Icc (0 : ℝ) T) (x : Space) :
    Tendsto (fun n => vectorCurl ((V n).velocity t).field x) atTop
      (𝓝 (vectorCurl (U.velocity t).field x)) := by
  have h3 := U.sampled_h3_tendsto_of_initial_h3 V hinit (fun _ => t)
  have hgrad : Tendsto (fun n => fderiv ℝ ((V n).velocity t).field x) atTop
      (𝓝 (fderiv ℝ (U.velocity t).field x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (show Tendsto (fun n => (9 * smoothEmbeddingConstant) *
        tensorNorm 3 (U.difference (V n) t)) atTop (𝓝 0) from by
          simpa only [mul_zero] using h3.const_mul (9 * smoothEmbeddingConstant))
    have hb := real_smooth_fderiv_le_H3 3 (U.difference (V n) t).field
      (U.difference (V n) t).smooth (fun j _ => (U.difference (V n) t).integrable j) x
    have hf : (U.difference (V n) t).field =
        ((V n).velocity t).field - (U.velocity t).field :=
      funext (fieldSub_field _ _)
    rw [hf, fderiv_sub (((V n).velocity t).smooth.differentiable (by simp) x)
      ((U.velocity t).smooth.differentiable (by simp) x)] at hb
    rw [tensorNorm_eq, hf]
    exact hb
  let C : (Space →L[ℝ] Space) →ₗ[ℝ] Space :=
    { toFun := curlMatrix
      map_add' := curlMatrix_add
      map_smul' := curlMatrix_smul }
  have hcurl := (C.toContinuousLinearMap.continuous.tendsto
    (fderiv ℝ (U.velocity t).field x)).comp hgrad
  change Tendsto (fun n => curlMatrix (fderiv ℝ ((V n).velocity t).field x)) atTop
    (𝓝 (curlMatrix (fderiv ℝ (U.velocity t).field x))) at hcurl
  rw [vectorCurl_eq_matrix _ x ((U.velocity t).smooth.differentiable (by simp) x)]
  exact hcurl.congr (fun n =>
    (vectorCurl_eq_matrix _ x (((V n).velocity t).smooth.differentiable (by simp) x)).symm)

end EulerOrdinarySobolev.Evolution

end
end

end

section

/-! Every selected finite packet has vorticity supported in one fixed ball
throughout its horizon. Initial support, the actual vorticity transport law,
and the summable particle-map displacement bound supply the three ingredients. -/

@[expose] public section

noncomputable section

namespace EulerPacketInduction

open Set EulerSmoothLimit EulerMeanCutoffCurl Euler.ComparatorBridge

theorem packets_vorticity_support (n : ℕ)
    (t : Icc (0 : ℝ) (packets n).parent.T) :
    tsupport (vectorCurl (fun x => (packets n).state.evolution.velocity (t,x))) ⊆
      Metric.closedBall 0 (2 + particleDisplacementCap constructionScales le_rfl le_rfl) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  exact support_subset_of_transport ((packets n).parent.position t)
    ((packets n).state.evolution.inverse.field t)
    (vectorCurl (fun x => (packets n).state.evolution.velocity (0,x)))
    (vectorCurl (fun x => (packets n).state.evolution.velocity (t,x)))
    ((packets n).state.evolution.inverse.right_inverse t)
    (packets_position_mapsTo_closedBall 2 n t)
    ((subset_tsupport _).trans (packets_initial_curl_support n))
    (fun a ha => (packets n).state.evolution.curl_eq_zero_along_position a ha t)

end EulerPacketInduction

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketInduction

open Set Filter EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPhysicalL2Scaling EulerOrdinarySobolev EulerMeanCutoffCurl EulerSmoothL2Series
open scoped Topology

/-- Canonical vorticity ball, given by `Metric.closedBall 0 (2 + particleDisplacementCap
constructionScales le_rfl le_rfl)`. -/
def canonicalVorticityBall : Set Space :=
  Metric.closedBall 0 (2 + particleDisplacementCap constructionScales le_rfl le_rfl)

theorem canonicalVorticityBall_compact : IsCompact canonicalVorticityBall :=
  isCompact_closedBall _ _

theorem evolution_vorticity_support (S : ℝ) (hS : 0 < S) (hSL : S < lifespan.duration)
    (t : Icc (0 : ℝ) S) :
    tsupport (vectorCurl ((lifespan.evolution S hS hSL).velocity t).field) ⊆
      canonicalVorticityBall := by
  let U := lifespan.evolution S hS hSL
  let hST : ∀ n, S ≤ (packets n).parent.T :=
    fun n => hSL.le.trans (lifespan_le_packet_horizon n)
  let V : ℕ → Evolution S hS.le := fun n =>
    (packets n).state.regularity.ordinaryEvolution.restrictTime S hS.le (hST n)
  have hfield (n : ℕ) (s : Icc (0 : ℝ) S) : ((V n).velocity s).field =
      fun x => (packets n).state.evolution.velocity (s,x) := by
    funext x
    exact ((packets n).state.regularity.velocity_match
      ⟨s,s.property.1,s.property.2.trans (hST n)⟩ x).symm
  have hnorm (n : ℕ) : tensorNorm 3 (U.difference (V n) ⟨0,le_rfl,hS.le⟩) =
      derivativeSum 3 ((fun x => (packets n).state.evolution.velocity (0,x)) -
        initialDatum.field) := by
    rw [tensorNorm_eq_derivativeSum]
    congr 1
    funext x
    rw [Evolution.difference,fieldSub_field]
    change ((V n).velocity ⟨0,le_rfl,hS.le⟩).field x -
      ((lifespan.evolution S hS hSL).velocity ⟨0,le_rfl,hS.le⟩).field x = _
    rw [hfield,lifespan.evolution_initial S hS hSL]
    rfl
  have hinit : Tendsto (fun n => tensorNorm 3
      (U.difference (V n) ⟨0,le_rfl,hS.le⟩)) atTop (𝓝 0) := by
    simpa only [hnorm] using initialDatum_Hm 3
  have hsupport (n : ℕ) : tsupport (vectorCurl ((V n).velocity t).field) ⊆
      canonicalVorticityBall := by
    rw [hfield]
    exact packets_vorticity_support n ⟨t,t.property.1,t.property.2.trans (hST n)⟩
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hout
  have hz (n : ℕ) : vectorCurl ((V n).velocity t).field x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hout (hsupport n hm))
  have hzero : Tendsto (fun n => vectorCurl ((V n).velocity t).field x) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Space)) atTop (𝓝 0))
  exact hx (tendsto_nhds_unique (U.curl_tendsto_of_initial_h3 V hinit t x) hzero)

theorem canonical_vorticity_support (t : lifespan.Time) :
    tsupport (vectorCurl (lifespan.maximalVelocity t)) ⊆ canonicalVorticityBall :=
  evolution_vorticity_support (lifespan.intermediateHorizon t)
    (lifespan.intermediateHorizon_pos t) (lifespan.intermediateHorizon_lt t)
    (lifespan.intermediateTime t)

theorem canonical_vorticity_eq_zero_outside (t : lifespan.Time) (x : Space)
    (hx : x ∉ canonicalVorticityBall) : vectorCurl (lifespan.maximalVelocity t) x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun hm => hx (canonical_vorticity_support t hm))

theorem canonical_vorticity_hasCompactSupport (t : lifespan.Time) :
    HasCompactSupport (vectorCurl (lifespan.maximalVelocity t)) :=
  canonicalVorticityBall_compact.of_isClosed_subset (isClosed_tsupport _)
    (canonical_vorticity_support t)

end EulerPacketInduction
