/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle002
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.Separation.Hausdorff
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartC.Semantics.Batch001`.
-/

public section

noncomputable section

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartC.Definitions`.
* `KernelOnly.PartC.Parameters`.
* `KernelOnly.PartC.ContactAlgebra`.
* `KernelOnly.PartC.GlobalSupport`.
* `KernelOnly.PartC.BaseGeometry`.
* `KernelOnly.PartC.TopologySpec`.
* `KernelOnly.PartC.GeometrySpec`.
* `KernelOnly.PartC.Stage2.MeshFacts`.
* `KernelOnly.PartC.Stage2.EnvelopeAlgebra`.
* `KernelOnly.PartC.Stage2.NoHiddenCore`.
* `KernelOnly.PartC.Stage2.SupportPhaseDerivatives`.
* `KernelOnly.PartC.Stage3.SupportDirect`.
* `KernelOnly.PartC.Stage3.FinalClosureDirect`.
* `KernelOnly.PartC.Stage4.PathDifferential`.
* `KernelOnly.PartC.Stage4.ExactGeometryFacts`.
* `KernelOnly.PartC.Stage4.NoHiddenMatchFacts`.
* `KernelOnly.PartC.Stage4.NoHiddenContinuityFacts`.
* `KernelOnly.PartC.Stage4.NoHiddenSignFacts`.
* `KernelOnly.PartC.Stage4.NoHiddenTurningFacts`.
* `KernelOnly.PartC.Stage4.NoHiddenDifferentialFacts`.
* `KernelOnly.PartC.Stage4.NoHiddenReflectionFacts`.
* `KernelOnly.PartC.Stage4.NoHiddenDirect`.
* `KernelOnly.PartC.Stage4.NicheEnvelopeSupport`.
* `KernelOnly.PartC.Stage4.SofaConvexityFacts`.
* `KernelOnly.PartC.Stage4.VerticalFillTopology`.
* `KernelOnly.PartC.Stage4.WallGraphs`.
* `KernelOnly.PartC.Stage4.NicheMembershipFacts`.
* `KernelOnly.PartC.Stage4.NicheFrontierTopology`.
* `KernelOnly.PartC.Stage4.NicheConnectedDirect`.
* `KernelOnly.PartC.Stage4.SofaFiberTopology`.
* `KernelOnly.PartC.Stage4.SofaTopologyDirect`.
* `KernelOnly.PartC.Stage4.FinalTopologyClosure`.
-/

public section

noncomputable section

section

/-!
# Part C concrete objects

This file fixes the exact objects used throughout Part C.  The numerical root,
regularity and global two-variable support margins are inherited from the
closed Parts A and B.  No alternative parameter vector or geometric set is
introduced here.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC

/-- The certified twenty-two dimensional Gerver parameter vector. -/
abbrev params : Romik.Params := PartB.params

/-- Physical terminal angle. -/
@[expose]
def T : ℝ := Real.pi / 2

/-- Reflected switching angles. -/
@[expose]
def eta : ℝ := T - params.theta
/-- The reflected switching angle `π/2 - φ` for the certified parameters. -/
@[expose]
def tau : ℝ := T - params.phi

/-- The concrete cap, fixed sofa, reconstructed Romik set and frame. -/
abbrev K : Set Point := Romik.K0 params
/-- The fixed Gerver sofa at the certified Romik parameters. -/
abbrev G : Set Point := Romik.sofa params
/-- The reconstructed contact-curve set at the certified parameters. -/
abbrev Sx : Set Point := Romik.reconstructedSet params
/-- The rigid frame path determined by the certified Romik parameters. -/
abbrev frame : ℝ → SE2 := Romik.frame params

/-- Endpoint support point used for the direct nonemptiness proof. -/
@[expose]
def anchor : Point := (1, 0)

/-- Piecewise body-frame derivative coefficients.  This definition is local to
Part C so that the geometric layer does not import the later Part D article
claims. -/
@[expose]
def alphaBetaAt (t : ℝ) : Point :=
  if t ≤ params.phi then Romik.alphaBeta1 params t
  else if t ≤ params.theta then Romik.alphaBeta2 params t
  else if t ≤ eta then Romik.alphaBeta3 params t
  else if t ≤ tau then Romik.alphaBeta4 params t
  else Romik.alphaBeta5 params t

/-- The horizontal body-frame velocity coefficient. -/
@[expose]
def alpha (t : ℝ) : ℝ := (alphaBetaAt t).1
/-- The vertical body-frame velocity coefficient. -/
@[expose]
def beta (t : ℝ) : ℝ := (alphaBetaAt t).2

/-- The four standard contact curves. -/
@[expose]
def A (t : ℝ) : Point :=
  let x := Romik.path params t
  let a := alpha t
  (x.1 + a * (v t).1 + (u t).1,
   x.2 + a * (v t).2 + (u t).2)

/-- The inner contact curve `x + α v`. -/
@[expose]
def B (t : ℝ) : Point :=
  let x := Romik.path params t
  let a := alpha t
  (x.1 + a * (v t).1,
   x.2 + a * (v t).2)

/-- The outer contact curve `x - β u + v`. -/
@[expose]
def C (t : ℝ) : Point :=
  let x := Romik.path params t
  let b := beta t
  (x.1 - b * (u t).1 + (v t).1,
   x.2 - b * (u t).2 + (v t).2)

/-- The inner contact curve `x - β u`. -/
@[expose]
def D (t : ℝ) : Point :=
  let x := Romik.path params t
  let b := beta t
  (x.1 - b * (u t).1,
   x.2 - b * (u t).2)

/-- Image of a parametrized curve over a time set. -/
def curveImage (f : ℝ → Point) (I : Set ℝ) : Set Point := f '' I

/-- A closed line segment, written without depending on a specialized convex
geometry API. -/
def lineSegment (a b : Point) : Set Point :=
  {q | ∃ r ∈ Set.Icc (0 : ℝ) 1,
    q = ((1 - r) * a.1 + r * b.1,
         (1 - r) * a.2 + r * b.2)}

/-- Set-valued form of the niche boundary described in the manuscript. -/
def claimedNicheBoundary : Set Point :=
  lineSegment (D 0) (B T) ∪
  curveImage B (Set.Icc eta T) ∪
  curveImage (Romik.path params) (Set.Icc params.phi tau) ∪
  curveImage D (Set.Icc 0 params.theta)

end PartC
end GerverSofa

end

end

end

section

/-!
# Frozen parameter and endpoint consequences for Part C
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC

theorem params_mem : params ∈ Romik.box := PartB.params_mem

theorem params_equations : Romik.Equations params := PartB.params_equations

theorem switchOrder : Romik.SwitchOrder params := PartB.params_switchOrder

theorem pathContinuous : Continuous (Romik.path params) := PartB.continuous_path

theorem frameContinuous : SE2.ContinuousPath frame := PartB.continuous_frame

theorem pathZero : Romik.path params 0 = (0, 0) := PartB.path_zero

theorem pathEndYZero : (Romik.path params T).2 = 0 := by
  simpa [T] using
    (Romik.path_end_y_zero_of_mem_box_and_equations params_mem params_equations)

theorem phi_bounds :
    ((1958868239504182093160893749 : ℝ) /
      50000000000000000000000000000) ≤ params.phi ∧
    params.phi ≤
      ((78354729580167283726435751 : ℝ) /
        2000000000000000000000000000) :=
  PartB.phi_bounds

theorem theta_bounds :
    ((34065075469136244723692787727 : ℝ) /
      50000000000000000000000000000) ≤ params.theta ∧
    params.theta ≤
      ((34065075469136244723692787983 : ℝ) /
        50000000000000000000000000000) :=
  PartB.theta_bounds

end PartC
end GerverSofa

end

end

end

section

/-!
# Exact contact-curve algebra

These identities are independent of every interval estimate.  They record
that `A` and `C` lie on the two outer supporting lines, while `B` and `D` lie
on the corresponding inner-wall lines.  Later geometric work only has to prove
that the relevant contact points belong to the cap and that no hidden crossing
changes the boundary envelope.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC

/-- `A(t)` lies on the first outer support line. -/
theorem A_support_identity (t : ℝ) :
    dot (A t) (u t) = dot (Romik.path params t) (u t) + 1 := by
  simp only [A, dot, u, v]
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- `C(t)` lies on the second outer support line. -/
theorem C_support_identity (t : ℝ) :
    dot (C t) (v t) = dot (Romik.path params t) (v t) + 1 := by
  simp only [C, dot, u, v]
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- `B(t)` lies on the first inner wall through the corner path. -/
theorem B_inner_u_identity (t : ℝ) :
    dot (B t - Romik.path params t) (u t) = 0 := by
  change
    ((B t).1 - (Romik.path params t).1) * Real.cos t +
      ((B t).2 - (Romik.path params t).2) * Real.sin t = 0
  simp [B, v]; ring

/-- `D(t)` lies on the second inner wall through the corner path. -/
theorem D_inner_v_identity (t : ℝ) :
    dot (D t - Romik.path params t) (v t) = 0 := by
  change
    ((D t).1 - (Romik.path params t).1) * (-Real.sin t) +
      ((D t).2 - (Romik.path params t).2) * Real.cos t = 0
  simp [D, u]; ring

end PartC
end GerverSofa

end

end

end

section

/-!
# Consequences of the certified Part B continuum margins

The two strict inequalities already certified on the complete square imply
that every point of the Gerver rotation path satisfies every outer supporting
half-plane inequality.  This is one of the main bridges from Part B into the
global geometry of Part C.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC

theorem Gu_positive {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    0 < PartB.Gu s t := by
  have h := PartB.global_half_plane_margins.1 s (by simpa [T] using hs)
    t (by simpa [T] using ht)
  linarith

theorem Gv_positive {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    0 < PartB.Gv s t := by
  have h := PartB.global_half_plane_margins.2 s (by simpa [T] using hs)
    t (by simpa [T] using ht)
  linarith

/-- Every path point lies in every first outer supporting half-plane. -/
theorem path_mem_supportHalfU {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Romik.path params t ∈ supportHalfU params s := by
  have h := Gu_positive hs ht
  change dot (Romik.path params t) (u s) ≤
    dot (Romik.path params s) (u s) + 1
  dsimp [PartB.Gu, dot] at h ⊢
  linarith

/-- Every path point lies in every second outer supporting half-plane. -/
theorem path_mem_supportHalfV {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Romik.path params t ∈ supportHalfV params s := by
  have h := Gv_positive hs ht
  change dot (Romik.path params t) (v s) ≤
    dot (Romik.path params s) (v s) + 1
  dsimp [PartB.Gv, dot] at h ⊢
  linarith

theorem path_mem_outer_supports {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Romik.path params t ∈
      supportHalfU params s ∩ supportHalfV params s :=
  ⟨path_mem_supportHalfU hs ht, path_mem_supportHalfV hs ht⟩

end PartC
end GerverSofa

end

end

end

section

/-!
# Part C geometric consequences already closed by the existing source

Closedness, supporting-hallway containment, endpoint arms, motion continuity
and the set-theoretic identification with Romik's reconstruction require no new
numerical replay.  They are collected here for the concrete certified
parameter vector.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC

theorem closed_G : IsClosed G := Romik.isClosed_sofa params

theorem G_subset_hallway :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, G ⊆ Romik.hallwayAt params s :=
  Romik.sofa_subset_hallwayAt params pathZero pathEndYZero

theorem initialArm : ((frame 0).inv.act '' G) ⊆ horizontalArm :=
  Romik.initial_arm_of_path_zero params pathZero

theorem finalArm : ((frame 1).inv.act '' G) ⊆ verticalArm :=
  Romik.final_arm_of_path_end_y_zero params pathEndYZero

theorem G_eq_Sx : G = Sx :=
  Romik.sofa_eq_reconstructedSet params pathZero pathEndYZero

end PartC
end GerverSofa

end

end

end

section

/-!
# Exact topology target for the concrete Gerver set

This file states, but does not postulate, the two genuinely remaining
set-theoretic obligations.  A later concrete proof must construct a value of
`TopologyCertificate`; until then Part C cannot close.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC

/-- Direct topology certificate with the manuscript's explicit endpoint
support witness, rather than an anonymous existential. -/
structure TopologyCertificate : Prop where
  anchor_mem : anchor ∈ G
  connected : IsConnected G

namespace TopologyCertificate

theorem nonempty (cert : TopologyCertificate) : G.Nonempty :=
  ⟨anchor, cert.anchor_mem⟩

end TopologyCertificate
end PartC
end GerverSofa

end

end

end

section

/-!
# Global support and niche-topology certificate interfaces

The statements here encode the exact Part C geometry that is not allowed to be
hidden inside an arbitrary `connected` field: contact support, the two
no-hidden-crossing inequalities, and the claimed boundary of the niche.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC

/-- First no-hidden-crossing inequality from the manuscript. -/
def NoHiddenCrossingU : Prop :=
  ∀ r ∈ Set.Icc params.phi T,
    ∀ t ∈ Set.Icc r T,
      0 ≤ dot (Romik.path params r - Romik.path params t) (u t)

/-- Reflected no-hidden-crossing inequality. -/
def NoHiddenCrossingV : Prop :=
  ∀ t ∈ Set.Icc 0 tau,
    ∀ r ∈ Set.Icc t tau,
      0 ≤ dot (Romik.path params r - Romik.path params t) (v t)

/-- Proof-carrying niche topology.  The boundary equality is set-valued; the
orientation and eighteen-piece count belong to the later Part D boundary
certificate. -/
structure NicheTopologyCertificate : Prop where
  noHiddenU : NoHiddenCrossingU
  noHiddenV : NoHiddenCrossingV
  boundary_eq : frontier (Romik.niche params) = claimedNicheBoundary
  niche_connected : IsConnected (Romik.niche params)

/-- Complete genuinely new geometry required in Part C. -/
structure GlobalGeometryCertificate : Prop where
  supportA : ∀ t ∈ Set.Icc (0 : ℝ) T, A t ∈ K
  supportC : ∀ t ∈ Set.Icc (0 : ℝ) T, C t ∈ K
  nicheTopology : NicheTopologyCertificate
  topology : TopologyCertificate

namespace GlobalGeometryCertificate

theorem nonempty (cert : GlobalGeometryCertificate) : G.Nonempty :=
  cert.topology.nonempty

theorem connected (cert : GlobalGeometryCertificate) : IsConnected G :=
  cert.topology.connected

end GlobalGeometryCertificate
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C Stage 2 public mesh and branch facts

This module exposes the switch-cell classification already used internally in
Part B.  It is deliberately proved again from the frozen angle boxes so that
Part C contact and no-hidden-crossing certificates can reuse the exact 64-cell
mesh without depending on private declarations.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage2

open RatInterval

theorem node1_lt_phi : PartB.nodeTime 1 < params.phi := by
  have hpi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) :=
    ExactReplay.piI_contains_pi.2
  have hp := phi_bounds.1
  unfold PartB.nodeTime PartB.nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

theorem phi_lt_node2 : params.phi < PartB.nodeTime 2 := by
  have hpi : (ExactReplay.piI.lo : ℝ) ≤ Real.pi :=
    ExactReplay.piI_contains_pi.1
  have hp := phi_bounds.2
  unfold PartB.nodeTime PartB.nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

theorem node27_lt_theta : PartB.nodeTime 27 < params.theta := by
  have hpi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) :=
    ExactReplay.piI_contains_pi.2
  have hp := theta_bounds.1
  unfold PartB.nodeTime PartB.nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

theorem theta_lt_node28 : params.theta < PartB.nodeTime 28 := by
  have hpi : (ExactReplay.piI.lo : ℝ) ≤ Real.pi :=
    ExactReplay.piI_contains_pi.1
  have hp := theta_bounds.2
  unfold PartB.nodeTime PartB.nodeCoeff
  norm_num [ExactReplay.piI, ExactReplay.q] at hpi hp ⊢
  nlinarith

theorem node36_lt_eta : PartB.nodeTime 36 < eta := by
  change PartB.nodeTime 36 < Real.pi / 2 - params.theta
  have h := theta_lt_node28
  unfold PartB.nodeTime PartB.nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

theorem eta_lt_node37 : eta < PartB.nodeTime 37 := by
  change Real.pi / 2 - params.theta < PartB.nodeTime 37
  have h := node27_lt_theta
  unfold PartB.nodeTime PartB.nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

theorem node62_lt_tau : PartB.nodeTime 62 < tau := by
  change PartB.nodeTime 62 < Real.pi / 2 - params.phi
  have h := phi_lt_node2
  unfold PartB.nodeTime PartB.nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

theorem tau_lt_node63 : tau < PartB.nodeTime 63 := by
  change Real.pi / 2 - params.phi < PartB.nodeTime 63
  have h := node1_lt_phi
  unfold PartB.nodeTime PartB.nodeCoeff at h ⊢
  norm_num at h ⊢
  linarith

theorem phase1_cell {i : PartB.Cell} {t : ℝ}
    (ht : t ∈ PartB.cellSet i) (hphase : t ≤ params.phi) : i.1 ≤ 1 := by
  by_contra hnot
  have hi : 2 ≤ i.1 := by omega
  have h2i : PartB.nodeTime 2 ≤ PartB.nodeTime i.1 :=
    PartB.nodeTime_mono hi
  linarith [phi_lt_node2, ht.1]

theorem phase2_cell {i : PartB.Cell} {t : ℝ}
    (ht : t ∈ PartB.cellSet i)
    (hlo : params.phi < t) (hhi : t ≤ params.theta) :
    1 ≤ i.1 ∧ i.1 ≤ 27 := by
  constructor
  · by_contra hnot
    have hi : i.1 + 1 ≤ 1 := by omega
    have hend : PartB.nodeTime (i.1 + 1) ≤ PartB.nodeTime 1 :=
      PartB.nodeTime_mono hi
    linarith [node1_lt_phi, ht.2]
  · by_contra hnot
    have hi : 28 ≤ i.1 := by omega
    have h28i : PartB.nodeTime 28 ≤ PartB.nodeTime i.1 :=
      PartB.nodeTime_mono hi
    linarith [theta_lt_node28, ht.1]

theorem phase3_cell {i : PartB.Cell} {t : ℝ}
    (ht : t ∈ PartB.cellSet i)
    (hlo : params.theta < t) (hhi : t ≤ eta) :
    27 ≤ i.1 ∧ i.1 ≤ 36 := by
  constructor
  · by_contra hnot
    have hi : i.1 + 1 ≤ 27 := by omega
    have hend : PartB.nodeTime (i.1 + 1) ≤ PartB.nodeTime 27 :=
      PartB.nodeTime_mono hi
    linarith [node27_lt_theta, ht.2]
  · by_contra hnot
    have hi : 37 ≤ i.1 := by omega
    have h37i : PartB.nodeTime 37 ≤ PartB.nodeTime i.1 :=
      PartB.nodeTime_mono hi
    linarith [eta_lt_node37, ht.1]

theorem phase4_cell {i : PartB.Cell} {t : ℝ}
    (ht : t ∈ PartB.cellSet i)
    (hlo : eta < t) (hhi : t ≤ tau) :
    36 ≤ i.1 ∧ i.1 ≤ 62 := by
  constructor
  · by_contra hnot
    have hi : i.1 + 1 ≤ 36 := by omega
    have hend : PartB.nodeTime (i.1 + 1) ≤ PartB.nodeTime 36 :=
      PartB.nodeTime_mono hi
    linarith [node36_lt_eta, ht.2]
  · by_contra hnot
    have hi : 63 ≤ i.1 := by omega
    have h63i : PartB.nodeTime 63 ≤ PartB.nodeTime i.1 :=
      PartB.nodeTime_mono hi
    linarith [tau_lt_node63, ht.1]

theorem phase5_cell {i : PartB.Cell} {t : ℝ}
    (ht : t ∈ PartB.cellSet i) (hlo : tau < t) : 62 ≤ i.1 := by
  by_contra hnot
  have hi : i.1 + 1 ≤ 62 := by omega
  have hend : PartB.nodeTime (i.1 + 1) ≤ PartB.nodeTime 62 :=
    PartB.nodeTime_mono hi
  linarith [node62_lt_tau, ht.2]

theorem phi_nonneg : 0 ≤ params.phi :=
  (Romik.phi_pos_of_mem_box params_mem).le

theorem tau_le_T : tau ≤ T := by
  unfold tau
  linarith [phi_nonneg]

theorem zero_le_theta : 0 ≤ params.theta := by
  linarith [phi_nonneg, switchOrder.phi_le_theta]

theorem eta_le_tau : eta ≤ tau := by
  simpa [eta, tau, T] using switchOrder.eta_le_tau

theorem theta_le_eta : params.theta ≤ eta := by
  simpa [eta, T] using switchOrder.theta_le_eta

end Stage2
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C Stage 2 redesign: exact envelope algebra

The first 64x64 contact-box attempt was intentionally fail-closed but too
coarse at contact/equality cells: interval dependency destroys exact
cancellation.  This module switches to the analytic envelope coefficients.

For the outer `u`-contact curve `A`, the phasewise velocity is a nonnegative
scalar multiple of `v`; for the outer `v`-contact curve `C`, the velocity is a
nonpositive scalar multiple of `u`.  The scalar coefficients below are the
five exact algebraic pieces.  No numerical root is recomputed here.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage2

/-- Phasewise scalar multiplying `v(t)` in the derivative of `A`. -/
@[expose]
def rhoA (t : ℝ) : ℝ :=
  if t ≤ params.phi then 0
  else if t ≤ params.theta then
    -(1 / 4 : ℝ) * t * t + params.b1 * t + params.b2 + 1 / 2
  else if t ≤ eta then
    1 + params.c1 - t
  else if t ≤ tau then
    params.d1 - t / 2
  else
    1 / 2

/-- Phasewise nonnegative scalar for `C'(t) = -rhoC(t) * u(t)`. -/
@[expose]
def rhoC (t : ℝ) : ℝ :=
  if t ≤ params.phi then 1 / 2
  else if t ≤ params.theta then
    t / 2 - params.b1
  else if t ≤ eta then
    1 + params.c2 + t
  else if t ≤ tau then
    -(1 / 4 : ℝ) * t * t + params.d1 * t + params.d2 + 1 / 2
  else
    0

private theorem b1_lower : (-53 / 100 : ℝ) ≤ params.b1 := by
  have hp := params_mem
  dsimp [Romik.box, qR] at hp
  have h :
      ((-52762459802678462416060380937 : ℝ) /
        100000000000000000000000000000) ≤ params.b1 := by
    aesop
  norm_num at h ⊢
  linarith

private theorem b1_upper : params.b1 ≤ (-1 / 2 : ℝ) := by
  have hp := params_mem
  dsimp [Romik.box, qR] at hp
  have h : params.b1 ≤
      ((-52762459802678462416040380937 : ℝ) /
        100000000000000000000000000000) := by
    aesop
  norm_num at h ⊢
  linarith

private theorem b2_lower : (9 / 10 : ℝ) ≤ params.b2 := by
  have hp := params_mem
  dsimp [Romik.box, qR] at hp
  have h :
      ((92025838516063762289360579501 : ℝ) /
        100000000000000000000000000000) ≤ params.b2 := by
    aesop
  norm_num at h ⊢
  linarith

private theorem c1_lower : (3 / 5 : ℝ) ≤ params.c1 := by
  have hp := params_mem
  dsimp [Romik.box, qR] at hp
  have h :
      ((313022761424232933776114655193 : ℝ) /
        500000000000000000000000000000) ≤ params.c1 := by
    aesop
  norm_num at h ⊢
  linarith

private theorem c2_lower : (-1 : ℝ) ≤ params.c2 := by
  have hp := params_mem
  dsimp [Romik.box, qR] at hp
  have h :
      ((-151160128631428920268654781 : ℝ) /
        160000000000000000000000000) ≤ params.c2 := by
    aesop
  norm_num at h ⊢
  linarith

private theorem d1_lower : (13 / 10 : ℝ) ≤ params.d1 := by
  have hp := params_mem
  dsimp [Romik.box, qR] at hp
  have h :
      ((1641278451780291167220080819 : ℝ) /
        1250000000000000000000000000) ≤ params.d1 := by
    aesop
  norm_num at h ⊢
  linarith

private theorem d2_lower : (-53 / 100 : ℝ) ≤ params.d2 := by
  have hp := params_mem
  dsimp [Romik.box, qR] at hp
  have h :
      ((-105076534082910887440587258861 : ℝ) /
        200000000000000000000000000000) ≤ params.d2 := by
    aesop
  norm_num at h ⊢
  linarith

private theorem theta_lower_crude : (2 / 3 : ℝ) ≤ params.theta := by
  have h := theta_bounds.1
  norm_num at h ⊢
  linarith

private theorem theta_upper_crude : params.theta ≤ (7 / 10 : ℝ) := by
  have h := theta_bounds.2
  norm_num at h ⊢
  linarith

private theorem T_lt_two : T < 2 := by
  have hpi := ExactReplay.piI_contains_pi
  have hhi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) := hpi.2
  have hfour : (ExactReplay.piI.hi : ℝ) < 4 := by
    norm_num [ExactReplay.piI, ExactReplay.q]
  dsimp [T]
  linarith

private theorem three_halves_lt_T : (3 / 2 : ℝ) < T := by
  have hpi := ExactReplay.piI_contains_pi
  have hlo : (ExactReplay.piI.lo : ℝ) ≤ Real.pi := hpi.1
  have hthree : (3 : ℝ) < (ExactReplay.piI.lo : ℝ) := by
    norm_num [ExactReplay.piI, ExactReplay.q]
  dsimp [T]
  linarith

private theorem eta_lt_four_thirds : eta < (4 / 3 : ℝ) := by
  dsimp [eta]
  nlinarith [T_lt_two, theta_lower_crude]

private theorem four_fifths_lt_eta : (4 / 5 : ℝ) < eta := by
  dsimp [eta]
  nlinarith [three_halves_lt_T, theta_upper_crude]

private theorem rhoA_phase2_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (htθ : t ≤ params.theta) :
    0 ≤ -(1 / 4 : ℝ) * t * t + params.b1 * t + params.b2 + 1 / 2 := by
  have ht07 : t ≤ (7 / 10 : ℝ) := le_trans htθ theta_upper_crude
  have ht1 : t ≤ 1 := by linarith
  have hbt : (-53 / 100 : ℝ) * t ≤ params.b1 * t :=
    mul_le_mul_of_nonneg_right b1_lower ht0
  have hquad : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
  nlinarith [b2_lower]

private theorem rhoA_phase3_nonneg
    {t : ℝ} (_ht0 : 0 ≤ t) (htη : t ≤ eta) :
    0 ≤ 1 + params.c1 - t := by
  have ht : t < (4 / 3 : ℝ) := lt_of_le_of_lt htη eta_lt_four_thirds
  nlinarith [c1_lower]

private theorem rhoA_phase4_nonneg
    {t : ℝ} (_ht0 : 0 ≤ t) (htτ : t ≤ tau) :
    0 ≤ params.d1 - t / 2 := by
  have htT : t ≤ T := le_trans htτ tau_le_T
  have ht2 : t < 2 := lt_of_le_of_lt htT T_lt_two
  nlinarith [d1_lower]

private theorem rhoC_phase2_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) :
    0 ≤ t / 2 - params.b1 := by
  nlinarith [b1_upper]

private theorem rhoC_phase3_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) :
    0 ≤ 1 + params.c2 + t := by
  nlinarith [c2_lower]

private theorem rhoC_phase4_nonneg
    {t : ℝ} (hηt : eta ≤ t) (htτ : t ≤ tau) :
    0 ≤ -(1 / 4 : ℝ) * t * t + params.d1 * t + params.d2 + 1 / 2 := by
  have ht0 : 0 ≤ t := by
    have : (0 : ℝ) < eta := lt_trans (by norm_num) four_fifths_lt_eta
    linarith
  have htT : t ≤ T := le_trans htτ tau_le_T
  have ht2 : t < 2 := lt_of_le_of_lt htT T_lt_two
  have hmul : (13 / 10 : ℝ) * t ≤ params.d1 * t :=
    mul_le_mul_of_nonneg_right d1_lower ht0
  have hquad : 0 ≤ t * (2 - t) := mul_nonneg ht0 (by linarith)
  nlinarith [d2_lower, four_fifths_lt_eta]

/-- The `A` envelope coefficient is nonnegative on the full physical range. -/
theorem rhoA_nonneg {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    0 ≤ rhoA t := by
  unfold rhoA
  split_ifs with hφ hθ hη hτ
  · norm_num
  · exact rhoA_phase2_nonneg ht.1 hθ
  · exact rhoA_phase3_nonneg ht.1 hη
  · exact rhoA_phase4_nonneg ht.1 hτ
  · norm_num

/-- The reflected `C` envelope coefficient is nonnegative on the full physical range. -/
theorem rhoC_nonneg {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    0 ≤ rhoC t := by
  unfold rhoC
  split_ifs with hφ hθ hη hτ
  · norm_num
  · exact rhoC_phase2_nonneg ht.1
  · exact rhoC_phase3_nonneg ht.1
  · have hηt : eta ≤ t := le_of_lt (lt_of_not_ge hη)
    exact rhoC_phase4_nonneg hηt hτ
  · norm_num

/-- The first outer contact starts at the exact fan endpoint `(1,0)`. -/
theorem A_zero_eq_anchor : A 0 = anchor := by
  have hφ : (0 : ℝ) ≤ params.phi := le_of_lt (Romik.phi_pos_of_mem_box params_mem)
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  have halpha0 : alpha 0 = 0 := by
    unfold alpha alphaBetaAt
    simp [hφ, Romik.alphaBeta1, ha2]; norm_num
  simp [A, anchor, pathZero, halpha0, u, v]

/-- The second outer contact ends exactly on the fan boundary. -/
theorem C_T_snd_zero : (C T).2 = 0 := by
  have hφpos : 0 < params.phi := Romik.phi_pos_of_mem_box params_mem
  have hτT : tau < T := by
    dsimp [tau]
    linarith
  have hητ : eta ≤ tau := switchOrder.eta_le_tau
  have hθη : params.theta ≤ eta := switchOrder.theta_le_eta
  have hφθ : params.phi ≤ params.theta := switchOrder.phi_le_theta
  have hφT : params.phi < T := lt_of_le_of_lt (le_trans hφθ (le_trans hθη hητ)) hτT
  have hθT : params.theta < T := lt_of_le_of_lt (le_trans hθη hητ) hτT
  have hηT : eta < T := lt_of_le_of_lt hητ hτT
  have he2 := Romik.e2_eq_quarter_of_equations params_equations
  have hABT : alphaBetaAt T = Romik.alphaBeta5 params T := by
    unfold alphaBetaAt
    rw [ite_eq_right (not_le.mpr hφT)]
    rw [ite_eq_right (not_le.mpr hθT)]
    rw [ite_eq_right (not_le.mpr hηT)]
    rw [ite_eq_right (not_le.mpr hτT)]
  have hbetaT : beta T = 0 := by
    rw [beta, hABT]
    simp [Romik.alphaBeta5, T, he2]; norm_num
  change (Romik.path params T).2 - beta T * (u T).2 + (v T).2 = 0
  rw [pathEndYZero, hbetaT]
  simp [u, v, T]

end Stage2
end PartC
end GerverSofa

end

end

end

section

/-!
# Exact cell reduction of the two no-hidden-crossing inequalities

Off-diagonal mesh cells are reduced to executable upper bounds for the already
sound Part B intervals `Gu` and `Gv`.  The only analytic remainder after all
128 row certificates pass is the ordered triangle inside each single mesh
cell, named `SameCellU` and `SameCellV` below.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage2

/-- Manuscript `U(r,t)` in the orientation used by `NoHiddenCrossingU`. -/
def UValue (r t : ℝ) : ℝ :=
  dot (Romik.path params r - Romik.path params t) (u t)

/-- Reflected manuscript `V(t,r)`. -/
def VValue (t r : ℝ) : ℝ :=
  dot (Romik.path params r - Romik.path params t) (v t)

end Stage2
end PartC
end GerverSofa

end

end

end

section

/-!
# C10: source-clean phase derivative identities — residual batch fix

This revision keeps the C09 no-`convert` architecture and fixes the complete residual class from the
C09 clean build.
It uses eta-expanded derivative combinators (`fun_add`, `fun_sub`, `fun_mul`,
`fun_neg`, `fun_smul`) so the function carried by `HasDerivAt` is in the desired
shape from the start.  The proof remains organized in body coordinates and the
accompanying runner forces a fresh build of this module.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage2

/-- Phase-local outer `A` contact, written in vector form. -/
@[expose]
def phaseA1 (t : ℝ) : Point :=
  Romik.path1 params t + (Romik.alphaBeta1 params t).1 • v t + u t

/-- The phase 2 formula for the outer A contact curve. -/
@[expose]
def phaseA2 (t : ℝ) : Point :=
  Romik.path2 params t + (Romik.alphaBeta2 params t).1 • v t + u t

/-- The phase 3 formula for the outer A contact curve. -/
@[expose]
def phaseA3 (t : ℝ) : Point :=
  Romik.path3 params t + (Romik.alphaBeta3 params t).1 • v t + u t

/-- The phase 4 formula for the outer A contact curve. -/
@[expose]
def phaseA4 (t : ℝ) : Point :=
  Romik.path4 params t + (Romik.alphaBeta4 params t).1 • v t + u t

/-- The phase 5 formula for the outer A contact curve. -/
@[expose]
def phaseA5 (t : ℝ) : Point :=
  Romik.path5 params t + (Romik.alphaBeta5 params t).1 • v t + u t

/-- Phase-local outer `C` contact, written in vector form. -/
@[expose]
def phaseC1 (t : ℝ) : Point :=
  Romik.path1 params t - (Romik.alphaBeta1 params t).2 • u t + v t

/-- The phase 2 formula for the outer C contact curve. -/
@[expose]
def phaseC2 (t : ℝ) : Point :=
  Romik.path2 params t - (Romik.alphaBeta2 params t).2 • u t + v t

/-- The phase 3 formula for the outer C contact curve. -/
@[expose]
def phaseC3 (t : ℝ) : Point :=
  Romik.path3 params t - (Romik.alphaBeta3 params t).2 • u t + v t

/-- The phase 4 formula for the outer C contact curve. -/
@[expose]
def phaseC4 (t : ℝ) : Point :=
  Romik.path4 params t - (Romik.alphaBeta4 params t).2 • u t + v t

/-- The phase 5 formula for the outer C contact curve. -/
@[expose]
def phaseC5 (t : ℝ) : Point :=
  Romik.path5 params t - (Romik.alphaBeta5 params t).2 • u t + v t

/-- The vertical frame vector scaled by the contact coefficient `r`. -/
def vecA (r t : ℝ) : Point :=
  (-r * Real.sin t, r * Real.cos t)

/-- The negative horizontal frame vector scaled by the contact coefficient `r`. -/
def vecC (r t : ℝ) : Point :=
  (-r * Real.cos t, -r * Real.sin t)

/-- Derivative of the scalar square in the additive form used by the phase formulas. -/
theorem square_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => s * s) (t + t) t := by
  have h := (hasDerivAt_id t).fun_mul (hasDerivAt_id t)
  simpa only [id_eq, one_mul, mul_one] using h

/-- The horizontal frame vector has derivative equal to the vertical frame vector. -/
theorem u_hasDerivAt (t : ℝ) : HasDerivAt u (v t) t := by
  change HasDerivAt (fun s : ℝ => (Real.cos s, Real.sin s))
    (-Real.sin t, Real.cos t) t
  exact (Real.hasDerivAt_cos t).prodMk (Real.hasDerivAt_sin t)

/-- The vertical frame vector has derivative equal to the negative horizontal vector. -/
theorem v_hasDerivAt (t : ℝ) : HasDerivAt v (-u t) t := by
  change HasDerivAt (fun s : ℝ => (-Real.sin s, Real.cos s))
    (-Real.cos t, -Real.sin t) t
  exact (Real.hasDerivAt_sin t).fun_neg.prodMk (Real.hasDerivAt_cos t)

/-- Derivative of `addK (rot t (z1 t,z2 t))` in body coordinates. -/
theorem rotAddK_hasDerivAt
    {z1 z2 : ℝ → ℝ} {z1' z2' k1 k2 : ℝ} (t : ℝ)
    (hz1 : HasDerivAt z1 z1' t) (hz2 : HasDerivAt z2 z2' t) :
    HasDerivAt
      (fun s => Romik.addK (Romik.rot s (z1 s, z2 s)) k1 k2)
      (Romik.rot t (z1' - z2 t, z2' + z1 t)) t := by
  apply HasDerivAt.prodMk
  · change HasDerivAt
      (fun s => Real.cos s * z1 s - Real.sin s * z2 s + k1)
      (Real.cos t * (z1' - z2 t) - Real.sin t * (z2' + z1 t)) t
    have h1 := (Real.hasDerivAt_cos t).fun_mul hz1
    have h2 := (Real.hasDerivAt_sin t).fun_mul hz2
    have h := (h1.fun_sub h2).fun_add (hasDerivAt_const t k1)
    exact h.congr_deriv (by ring)
  · change HasDerivAt
      (fun s => Real.sin s * z1 s + Real.cos s * z2 s + k2)
      (Real.sin t * (z1' - z2 t) + Real.cos t * (z2' + z1 t)) t
    have h1 := (Real.hasDerivAt_sin t).fun_mul hz1
    have h2 := (Real.hasDerivAt_cos t).fun_mul hz2
    have h := (h1.fun_add h2).fun_add (hasDerivAt_const t k2)
    exact h.congr_deriv (by ring)

/-- The phase 1 path has the specified velocity in the rotating frame. -/
theorem path1_hasDerivAt (t : ℝ) :
    HasDerivAt (Romik.path1 params)
      (Romik.rot t (Romik.alphaBeta1 params t)) t := by
  let z1 : ℝ → ℝ := fun s =>
    params.a1 * Real.cos s + params.a2 * Real.sin s - 1
  let z2 : ℝ → ℝ := fun s =>
    -params.a2 * Real.cos s + params.a1 * Real.sin s - 1 / 2
  have hz1 : HasDerivAt z1
      (-params.a1 * Real.sin t + params.a2 * Real.cos t) t := by
    have h1 := HasDerivAt.const_mul params.a1 (Real.hasDerivAt_cos t)
    have h2 := HasDerivAt.const_mul params.a2 (Real.hasDerivAt_sin t)
    have h := (h1.fun_add h2).fun_sub (hasDerivAt_const t (1 : ℝ))
    dsimp [z1]
    exact h.congr_deriv (by ring)
  have hz2 : HasDerivAt z2
      (params.a2 * Real.sin t + params.a1 * Real.cos t) t := by
    have h1 := HasDerivAt.const_mul (-params.a2) (Real.hasDerivAt_cos t)
    have h2 := HasDerivAt.const_mul params.a1 (Real.hasDerivAt_sin t)
    have h := (h1.fun_add h2).fun_sub (hasDerivAt_const t (1 / 2 : ℝ))
    dsimp [z2]
    exact h.congr_deriv (by ring)
  change HasDerivAt
    (fun s => Romik.addK (Romik.rot s (z1 s, z2 s)) params.k11 params.k12)
    (Romik.rot t (Romik.alphaBeta1 params t)) t
  have h := rotAddK_hasDerivAt (k1 := params.k11) (k2 := params.k12) t hz1 hz2
  refine h.congr_deriv ?_
  apply congrArg (Romik.rot t)
  ext <;> dsimp [z1, z2, Romik.alphaBeta1] <;> ring

/-- The phase 2 path has the specified velocity in the rotating frame. -/
theorem path2_hasDerivAt (t : ℝ) :
    HasDerivAt (Romik.path2 params)
      (Romik.rot t (Romik.alphaBeta2 params t)) t := by
  let z1 : ℝ → ℝ := fun s =>
    -(1 / 4 : ℝ) * s * s + params.b1 * s + params.b2
  let z2 : ℝ → ℝ := fun s =>
    (1 / 2 : ℝ) * s - params.b1 - 1
  have hz1 : HasDerivAt z1 (-(1 / 2 : ℝ) * t + params.b1) t := by
    have h1 := HasDerivAt.const_mul (-(1 / 4 : ℝ)) (square_hasDerivAt t)
    have h2 := HasDerivAt.const_mul params.b1 (hasDerivAt_id t)
    have hraw := (h1.fun_add h2).fun_add (hasDerivAt_const t params.b2)
    have heq : (-(1 / 4 : ℝ)) * (t + t) + params.b1 * 1 + 0 =
        -(1 / 2 : ℝ) * t + params.b1 := by ring
    rw [← heq]
    simpa only [z1, id_eq, mul_assoc] using hraw
  have hz2 : HasDerivAt z2 (1 / 2 : ℝ) t := by
    have h1 := HasDerivAt.const_mul (1 / 2 : ℝ) (hasDerivAt_id t)
    have h := (h1.fun_sub (hasDerivAt_const t params.b1)).fun_sub
      (hasDerivAt_const t (1 : ℝ))
    dsimp [z2]
    exact h.congr_deriv (by ring)
  change HasDerivAt
    (fun s => Romik.addK (Romik.rot s (z1 s, z2 s)) params.k21 params.k22)
    (Romik.rot t (Romik.alphaBeta2 params t)) t
  have h := rotAddK_hasDerivAt (k1 := params.k21) (k2 := params.k22) t hz1 hz2
  refine h.congr_deriv ?_
  apply congrArg (Romik.rot t)
  ext <;> dsimp [z1, z2, Romik.alphaBeta2] <;> ring

/-- The phase 3 path has the specified velocity in the rotating frame. -/
theorem path3_hasDerivAt (t : ℝ) :
    HasDerivAt (Romik.path3 params)
      (Romik.rot t (Romik.alphaBeta3 params t)) t := by
  let z1 : ℝ → ℝ := fun s => params.c1 - s
  let z2 : ℝ → ℝ := fun s => params.c2 + s
  have hz1 : HasDerivAt z1 (-1) t := by
    have h := (hasDerivAt_const t params.c1).fun_sub (hasDerivAt_id t)
    dsimp [z1]
    exact h.congr_deriv (by ring)
  have hz2 : HasDerivAt z2 1 t := by
    have h := (hasDerivAt_const t params.c2).fun_add (hasDerivAt_id t)
    dsimp [z2]
    exact h.congr_deriv (by ring)
  change HasDerivAt
    (fun s => Romik.addK (Romik.rot s (z1 s, z2 s)) params.k31 params.k32)
    (Romik.rot t (Romik.alphaBeta3 params t)) t
  have h := rotAddK_hasDerivAt (k1 := params.k31) (k2 := params.k32) t hz1 hz2
  refine h.congr_deriv ?_
  apply congrArg (Romik.rot t)
  ext <;> dsimp [z1, z2, Romik.alphaBeta3] <;> ring

/-- The phase 4 path has the specified velocity in the rotating frame. -/
theorem path4_hasDerivAt (t : ℝ) :
    HasDerivAt (Romik.path4 params)
      (Romik.rot t (Romik.alphaBeta4 params t)) t := by
  let z1 : ℝ → ℝ := fun s => -(1 / 2 : ℝ) * s + params.d1 - 1
  let z2 : ℝ → ℝ := fun s =>
    -(1 / 4 : ℝ) * s * s + params.d1 * s + params.d2
  have hz1 : HasDerivAt z1 (-(1 / 2 : ℝ)) t := by
    have h1 := HasDerivAt.const_mul (-(1 / 2 : ℝ)) (hasDerivAt_id t)
    have h := (h1.fun_add (hasDerivAt_const t params.d1)).fun_sub
      (hasDerivAt_const t (1 : ℝ))
    dsimp [z1]
    exact h.congr_deriv (by ring)
  have hz2 : HasDerivAt z2 (-(1 / 2 : ℝ) * t + params.d1) t := by
    have h1 := HasDerivAt.const_mul (-(1 / 4 : ℝ)) (square_hasDerivAt t)
    have h2 := HasDerivAt.const_mul params.d1 (hasDerivAt_id t)
    have hraw := (h1.fun_add h2).fun_add (hasDerivAt_const t params.d2)
    have heq : (-(1 / 4 : ℝ)) * (t + t) + params.d1 * 1 + 0 =
        -(1 / 2 : ℝ) * t + params.d1 := by ring
    rw [← heq]
    simpa only [z2, id_eq, mul_assoc] using hraw
  change HasDerivAt
    (fun s => Romik.addK (Romik.rot s (z1 s, z2 s)) params.k41 params.k42)
    (Romik.rot t (Romik.alphaBeta4 params t)) t
  have h := rotAddK_hasDerivAt (k1 := params.k41) (k2 := params.k42) t hz1 hz2
  refine h.congr_deriv ?_
  apply congrArg (Romik.rot t)
  ext <;> dsimp [z1, z2, Romik.alphaBeta4] <;> ring

/-- The phase 5 path has the specified velocity in the rotating frame. -/
theorem path5_hasDerivAt (t : ℝ) :
    HasDerivAt (Romik.path5 params)
      (Romik.rot t (Romik.alphaBeta5 params t)) t := by
  let z1 : ℝ → ℝ := fun s =>
    params.e1 * Real.cos s + params.e2 * Real.sin s - 1 / 2
  let z2 : ℝ → ℝ := fun s =>
    -params.e2 * Real.cos s + params.e1 * Real.sin s - 1
  have hz1 : HasDerivAt z1
      (-params.e1 * Real.sin t + params.e2 * Real.cos t) t := by
    have h1 := HasDerivAt.const_mul params.e1 (Real.hasDerivAt_cos t)
    have h2 := HasDerivAt.const_mul params.e2 (Real.hasDerivAt_sin t)
    have h := (h1.fun_add h2).fun_sub (hasDerivAt_const t (1 / 2 : ℝ))
    dsimp [z1]
    exact h.congr_deriv (by ring)
  have hz2 : HasDerivAt z2
      (params.e2 * Real.sin t + params.e1 * Real.cos t) t := by
    have h1 := HasDerivAt.const_mul (-params.e2) (Real.hasDerivAt_cos t)
    have h2 := HasDerivAt.const_mul params.e1 (Real.hasDerivAt_sin t)
    have h := (h1.fun_add h2).fun_sub (hasDerivAt_const t (1 : ℝ))
    dsimp [z2]
    exact h.congr_deriv (by ring)
  change HasDerivAt
    (fun s => Romik.addK (Romik.rot s (z1 s, z2 s)) params.k51 params.k52)
    (Romik.rot t (Romik.alphaBeta5 params t)) t
  have h := rotAddK_hasDerivAt (k1 := params.k51) (k2 := params.k52) t hz1 hz2
  refine h.congr_deriv ?_
  apply congrArg (Romik.rot t)
  ext <;> dsimp [z1, z2, Romik.alphaBeta5] <;> ring

/-- Generic outer-A envelope identity from `x'=R_t(alpha,beta)`. -/
private theorem contactA_hasDerivAt
    {x : ℝ → Point} {ab : ℝ → Point} {a' : ℝ} (t : ℝ)
    (hx : HasDerivAt x (Romik.rot t (ab t)) t)
    (ha : HasDerivAt (fun s => (ab s).1) a' t) :
    HasDerivAt
      (fun s => x s + (ab s).1 • v s + u s)
      (vecA ((ab t).2 + a' + 1) t) t := by
  have hscaled := ha.fun_smul (v_hasDerivAt t)
  have h := (hx.fun_add hscaled).fun_add (u_hasDerivAt t)
  refine h.congr_deriv ?_
  ext <;> simp [Romik.rot, u, v, vecA] <;> ring

/-- Generic outer-C envelope identity from `x'=R_t(alpha,beta)`. -/
private theorem contactC_hasDerivAt
    {x : ℝ → Point} {ab : ℝ → Point} {b' : ℝ} (t : ℝ)
    (hx : HasDerivAt x (Romik.rot t (ab t)) t)
    (hb : HasDerivAt (fun s => (ab s).2) b' t) :
    HasDerivAt
      (fun s => x s - (ab s).2 • u s + v s)
      (vecC (b' + 1 - (ab t).1) t) t := by
  have hscaled := hb.fun_smul (u_hasDerivAt t)
  have h := (hx.fun_sub hscaled).fun_add (v_hasDerivAt t)
  refine h.congr_deriv ?_
  ext <;> simp [Romik.rot, u, v, vecC] <;> ring

private theorem alpha1_fst_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta1 params s).1)
      (-2 * params.a1 * Real.cos t - 2 * params.a2 * Real.sin t) t := by
  have h1 := HasDerivAt.const_mul (-2 * params.a1) (Real.hasDerivAt_sin t)
  have h2 := HasDerivAt.const_mul (2 * params.a2) (Real.hasDerivAt_cos t)
  have h := (h1.fun_add h2).fun_add (hasDerivAt_const t (1 / 2 : ℝ))
  dsimp [Romik.alphaBeta1]
  exact h.congr_deriv (by ring)

private theorem alpha2_fst_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta2 params s).1) (-1) t := by
  have h := (hasDerivAt_const t (1 + 2 * params.b1)).fun_sub (hasDerivAt_id t)
  dsimp [Romik.alphaBeta2]
  exact h.congr_deriv (by ring)

private theorem alpha3_fst_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta3 params s).1) (-1) t := by
  have h := (hasDerivAt_const t (-1 - params.c2)).fun_sub (hasDerivAt_id t)
  dsimp [Romik.alphaBeta3]
  exact h.congr_deriv (by ring)

private theorem alpha4_fst_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta4 params s).1)
      ((1 / 2 : ℝ) * t - params.d1) t := by
  have h1 := HasDerivAt.const_mul (1 / 4 : ℝ) (square_hasDerivAt t)
  have h2 := HasDerivAt.const_mul params.d1 (hasDerivAt_id t)
  have hraw := (((h1.fun_sub h2).fun_sub (hasDerivAt_const t params.d2)).fun_sub
    (hasDerivAt_const t (1 / 2 : ℝ)))
  have heq : (1 / 4 : ℝ) * (t + t) - params.d1 * 1 - 0 - 0 =
      (1 / 2 : ℝ) * t - params.d1 := by ring
  rw [← heq]
  simpa only [Romik.alphaBeta4, id_eq, mul_assoc] using hraw

private theorem alpha5_fst_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta5 params s).1)
      (-2 * params.e1 * Real.cos t - 2 * params.e2 * Real.sin t) t := by
  have h1 := HasDerivAt.const_mul (2 * params.e1) (Real.hasDerivAt_sin t)
  have h2 := HasDerivAt.const_mul (2 * params.e2) (Real.hasDerivAt_cos t)
  have h := ((hasDerivAt_const t (1 : ℝ)).fun_sub h1).fun_add h2
  dsimp [Romik.alphaBeta5]
  exact h.congr_deriv (by ring)

private theorem beta1_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta1 params s).2)
      (-2 * params.a1 * Real.sin t + 2 * params.a2 * Real.cos t) t := by
  have h1 := HasDerivAt.const_mul (2 * params.a1) (Real.hasDerivAt_cos t)
  have h2 := HasDerivAt.const_mul (2 * params.a2) (Real.hasDerivAt_sin t)
  have h := (h1.fun_add h2).fun_sub (hasDerivAt_const t (1 : ℝ))
  dsimp [Romik.alphaBeta1]
  exact h.congr_deriv (by ring)

private theorem beta2_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta2 params s).2)
      (-(1 / 2 : ℝ) * t + params.b1) t := by
  have h1 := HasDerivAt.const_mul (-(1 / 4 : ℝ)) (square_hasDerivAt t)
  have h2 := HasDerivAt.const_mul params.b1 (hasDerivAt_id t)
  have hraw := ((h1.fun_add h2).fun_add (hasDerivAt_const t params.b2)).fun_add
    (hasDerivAt_const t (1 / 2 : ℝ))
  have heq : (-(1 / 4 : ℝ)) * (t + t) + params.b1 * 1 + 0 + 0 =
      -(1 / 2 : ℝ) * t + params.b1 := by ring
  rw [← heq]
  simpa only [Romik.alphaBeta2, id_eq, mul_assoc] using hraw

private theorem beta3_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta3 params s).2) (-1) t := by
  have h := (hasDerivAt_const t (1 + params.c1)).fun_sub (hasDerivAt_id t)
  dsimp [Romik.alphaBeta3]
  exact h.congr_deriv (by ring)

private theorem beta4_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta4 params s).2) (-1) t := by
  have h := (hasDerivAt_const t (2 * params.d1 - 1)).fun_sub (hasDerivAt_id t)
  dsimp [Romik.alphaBeta4]
  exact h.congr_deriv (by ring)

private theorem beta5_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta5 params s).2)
      (-2 * params.e1 * Real.sin t + 2 * params.e2 * Real.cos t) t := by
  have h1 := HasDerivAt.const_mul (2 * params.e1) (Real.hasDerivAt_cos t)
  have h2 := HasDerivAt.const_mul (2 * params.e2) (Real.hasDerivAt_sin t)
  have h := (h1.fun_add h2).fun_sub (hasDerivAt_const t (1 / 2 : ℝ))
  dsimp [Romik.alphaBeta5]
  exact h.congr_deriv (by ring)

/-- Phase 1: `A' = 0 * v`. -/
theorem A1_hasDerivAt (t : ℝ) :
    HasDerivAt phaseA1 (vecA 0 t) t := by
  change HasDerivAt
    (fun s => Romik.path1 params s + (Romik.alphaBeta1 params s).1 • v s + u s)
    (vecA 0 t) t
  have h := contactA_hasDerivAt t (path1_hasDerivAt t) (alpha1_fst_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecA r t)
  dsimp [Romik.alphaBeta1]
  ring

/-- Phase 2: `A' = beta_2 * v`. -/
theorem A2_hasDerivAt (t : ℝ) :
    HasDerivAt phaseA2
      (vecA (-(1 / 4 : ℝ) * t * t + params.b1 * t + params.b2 + 1 / 2) t) t := by
  change HasDerivAt
    (fun s => Romik.path2 params s + (Romik.alphaBeta2 params s).1 • v s + u s)
    (vecA (-(1 / 4 : ℝ) * t * t + params.b1 * t + params.b2 + 1 / 2) t) t
  have h := contactA_hasDerivAt t (path2_hasDerivAt t) (alpha2_fst_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecA r t)
  dsimp [Romik.alphaBeta2]
  ring

/-- Phase 3: `A' = beta_3 * v`. -/
theorem A3_hasDerivAt (t : ℝ) :
    HasDerivAt phaseA3 (vecA (1 + params.c1 - t) t) t := by
  change HasDerivAt
    (fun s => Romik.path3 params s + (Romik.alphaBeta3 params s).1 • v s + u s)
    (vecA (1 + params.c1 - t) t) t
  have h := contactA_hasDerivAt t (path3_hasDerivAt t) (alpha3_fst_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecA r t)
  dsimp [Romik.alphaBeta3]
  ring

/-- Phase 4: `A' = (d1-t/2) * v`. -/
theorem A4_hasDerivAt (t : ℝ) :
    HasDerivAt phaseA4 (vecA (params.d1 - t / 2) t) t := by
  change HasDerivAt
    (fun s => Romik.path4 params s + (Romik.alphaBeta4 params s).1 • v s + u s)
    (vecA (params.d1 - t / 2) t) t
  have h := contactA_hasDerivAt t (path4_hasDerivAt t) (alpha4_fst_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecA r t)
  dsimp [Romik.alphaBeta4]
  ring

/-- Phase 5: `A' = (1/2) * v`. -/
theorem A5_hasDerivAt (t : ℝ) :
    HasDerivAt phaseA5 (vecA (1 / 2 : ℝ) t) t := by
  change HasDerivAt
    (fun s => Romik.path5 params s + (Romik.alphaBeta5 params s).1 • v s + u s)
    (vecA (1 / 2 : ℝ) t) t
  have h := contactA_hasDerivAt t (path5_hasDerivAt t) (alpha5_fst_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecA r t)
  dsimp [Romik.alphaBeta5]
  ring

/-- Phase 1: `C' = -(1/2) * u`. -/
theorem C1_hasDerivAt (t : ℝ) :
    HasDerivAt phaseC1 (vecC (1 / 2 : ℝ) t) t := by
  change HasDerivAt
    (fun s => Romik.path1 params s - (Romik.alphaBeta1 params s).2 • u s + v s)
    (vecC (1 / 2 : ℝ) t) t
  have h := contactC_hasDerivAt t (path1_hasDerivAt t) (beta1_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecC r t)
  dsimp [Romik.alphaBeta1]
  ring

/-- Phase 2: `C' = -(t/2-b1) * u`. -/
theorem C2_hasDerivAt (t : ℝ) :
    HasDerivAt phaseC2 (vecC (t / 2 - params.b1) t) t := by
  change HasDerivAt
    (fun s => Romik.path2 params s - (Romik.alphaBeta2 params s).2 • u s + v s)
    (vecC (t / 2 - params.b1) t) t
  have h := contactC_hasDerivAt t (path2_hasDerivAt t) (beta2_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecC r t)
  dsimp [Romik.alphaBeta2]
  ring

/-- Phase 3: `C' = -(1+c2+t) * u`. -/
theorem C3_hasDerivAt (t : ℝ) :
    HasDerivAt phaseC3 (vecC (1 + params.c2 + t) t) t := by
  change HasDerivAt
    (fun s => Romik.path3 params s - (Romik.alphaBeta3 params s).2 • u s + v s)
    (vecC (1 + params.c2 + t) t) t
  have h := contactC_hasDerivAt t (path3_hasDerivAt t) (beta3_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecC r t)
  dsimp [Romik.alphaBeta3]
  ring

/-- Phase 4: `C' = -rhoC_4 * u`. -/
theorem C4_hasDerivAt (t : ℝ) :
    HasDerivAt phaseC4
      (vecC (-(1 / 4 : ℝ) * t * t + params.d1 * t + params.d2 + 1 / 2) t) t := by
  change HasDerivAt
    (fun s => Romik.path4 params s - (Romik.alphaBeta4 params s).2 • u s + v s)
    (vecC (-(1 / 4 : ℝ) * t * t + params.d1 * t + params.d2 + 1 / 2) t) t
  have h := contactC_hasDerivAt t (path4_hasDerivAt t) (beta4_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecC r t)
  dsimp [Romik.alphaBeta4]
  ring

/-- Phase 5: `C' = 0 * u`. -/
theorem C5_hasDerivAt (t : ℝ) :
    HasDerivAt phaseC5 (vecC 0 t) t := by
  change HasDerivAt
    (fun s => Romik.path5 params s - (Romik.alphaBeta5 params s).2 • u s + v s)
    (vecC 0 t) t
  have h := contactC_hasDerivAt t (path5_hasDerivAt t) (beta5_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecC r t)
  dsimp [Romik.alphaBeta5]
  ring

/-! ## Public derivative shapes for downstream Part C closure

The source-clean phase proofs above use private `vecA`/`vecC` helpers.
These public lemmas expose exactly the stable geometric derivative shapes used
by the direct support proof.  The transport is derivative-only: the function
itself is unchanged, and the remaining pair equality is elementary algebra.
-/

theorem A1_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseA1 ((0 : ℝ) • v t) t := by
  refine (A1_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecA, v]

theorem A2_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseA2
      ((-(1 / 4 : ℝ) * t * t + params.b1 * t + params.b2 + 1 / 2) • v t) t := by
  refine (A2_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecA, v]; ring

theorem A3_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseA3 ((1 + params.c1 - t) • v t) t := by
  refine (A3_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecA, v]; ring

theorem A4_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseA4 ((params.d1 - t / 2) • v t) t := by
  refine (A4_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecA, v]; ring

theorem A5_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseA5 ((1 / 2 : ℝ) • v t) t := by
  refine (A5_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecA, v]

theorem C1_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseC1 ((-(1 / 2 : ℝ)) • u t) t := by
  refine (C1_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecC, u]

theorem C2_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseC2 ((-(t / 2 - params.b1)) • u t) t := by
  refine (C2_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecC, u]

theorem C3_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseC3 ((-(1 + params.c2 + t)) • u t) t := by
  refine (C3_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecC, u]

theorem C4_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseC4
      ((-(-(1 / 4 : ℝ) * t * t + params.d1 * t + params.d2 + 1 / 2)) • u t) t := by
  refine (C4_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecC, u]

theorem C5_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseC5 ((0 : ℝ) • u t) t := by
  refine (C5_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecC, u]

end Stage2
end PartC
end GerverSofa

end

end

end

section

/-!
# Direct outer-support closure for Part C

This proof uses the five source-clean phase derivative identities and glues
monotonicity across the four certified switching times.  It does not require a
globally differentiable contact parametrisation at the speed-change junctions.
-/

public section

noncomputable section

open Set

namespace GerverSofa
namespace PartC
namespace Stage3

open Stage2

private theorem T_nonneg : (0 : ℝ) ≤ T := by
  dsimp [T]
  positivity

private theorem T_le_pi : T ≤ Real.pi := by
  dsimp [T]
  nlinarith [Real.pi_pos]

private theorem cos_nonneg_physical {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) T) (hy : y ∈ Icc (0 : ℝ) T) :
    0 ≤ Real.cos (x - y) := by
  rcases hx with ⟨hx0, hxT⟩
  rcases hy with ⟨hy0, hyT⟩
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
  · dsimp [T] at hxT hyT ⊢
    linarith
  · dsimp [T] at hxT hyT ⊢
    linarith

private theorem sin_nonneg_diff {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) T) (hy : y ∈ Icc (0 : ℝ) T) (hxy : x ≤ y) :
    0 ≤ Real.sin (y - x) := by
  rcases hx with ⟨hx0, hxT⟩
  rcases hy with ⟨hy0, hyT⟩
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · linarith
  · have hT : y - x ≤ T := by linarith
    exact le_trans hT T_le_pi

private theorem dot_hasDerivAt_fixed {f : ℝ → Point} {df : Point} {t : ℝ}
    (h : HasDerivAt f df t) (w : Point) :
    HasDerivAt (fun s => dot (f s) w) (dot df w) t := by
  have h1 := HasDerivAt.const_mul w.1 h.fst
  have h2 := HasDerivAt.const_mul w.2 h.snd
  have hs := h1.fun_add h2
  simpa [dot, mul_comm] using hs

private theorem glue_mono {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : MonotoneOn f (Icc a b)) (h2 : MonotoneOn f (Icc b c)) :
    MonotoneOn f (Icc a c) := by
  intro x hx y hy hxy
  by_cases hyb : y ≤ b
  · exact h1 ⟨hx.1, le_trans hxy hyb⟩ ⟨hy.1, hyb⟩ hxy
  by_cases hbx : b ≤ x
  · exact h2 ⟨hbx, le_trans hxy hy.2⟩ ⟨le_trans hbx hxy, hy.2⟩ hxy
  · have hxb : x ≤ b := le_of_not_ge hbx
    have hby : b ≤ y := le_of_lt (lt_of_not_ge hyb)
    exact le_trans
      (h1 ⟨hx.1, hxb⟩ ⟨hab, le_rfl⟩ hxb)
      (h2 ⟨le_rfl, hbc⟩ ⟨hby, hy.2⟩ hby)

private theorem glue_anti {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : AntitoneOn f (Icc a b)) (h2 : AntitoneOn f (Icc b c)) :
    AntitoneOn f (Icc a c) := by
  intro x hx y hy hxy
  by_cases hyb : y ≤ b
  · exact h1 ⟨hx.1, le_trans hxy hyb⟩ ⟨hy.1, hyb⟩ hxy
  by_cases hbx : b ≤ x
  · exact h2 ⟨hbx, le_trans hxy hy.2⟩ ⟨le_trans hbx hxy, hy.2⟩ hxy
  · have hxb : x ≤ b := le_of_not_ge hbx
    have hby : b ≤ y := le_of_lt (lt_of_not_ge hyb)
    exact le_trans
      (h2 ⟨le_rfl, hbc⟩ ⟨hby, hy.2⟩ hby)
      (h1 ⟨hx.1, hxb⟩ ⟨hab, le_rfl⟩ hxb)

private theorem restrict_mono {f : ℝ → ℝ} {a b c d : ℝ}
    (h : MonotoneOn f (Icc a b)) (hac : a ≤ c) (hdb : d ≤ b) :
    MonotoneOn f (Icc c d) := by
  intro x hx y hy hxy
  exact h ⟨le_trans hac hx.1, le_trans hx.2 hdb⟩
    ⟨le_trans hac hy.1, le_trans hy.2 hdb⟩ hxy

private def a1c (_t : ℝ) : ℝ := 0
private def a2c (t : ℝ) : ℝ := -(1 / 4 : ℝ) * t * t + params.b1 * t + params.b2 + 1 / 2
private def a3c (t : ℝ) : ℝ := 1 + params.c1 - t
private def a4c (t : ℝ) : ℝ := params.d1 - t / 2
private def a5c (_t : ℝ) : ℝ := 1 / 2

private def c1c (_t : ℝ) : ℝ := 1 / 2
private def c2c (t : ℝ) : ℝ := t / 2 - params.b1
private def c3c (t : ℝ) : ℝ := 1 + params.c2 + t
private def c4c (t : ℝ) : ℝ := -(1 / 4 : ℝ) * t * t + params.d1 * t + params.d2 + 1 / 2
private def c5c (_t : ℝ) : ℝ := 0

private theorem a1_nonneg (t : ℝ) : 0 ≤ a1c t := by simp [a1c]
private theorem a2_nonneg {t : ℝ} (ht : t ∈ Ioo params.phi params.theta) : 0 ≤ a2c t := by
  have hp : t ∈ Icc (0 : ℝ) T := by
    exact ⟨le_trans phi_nonneg (le_of_lt ht.1),
      le_trans (le_of_lt ht.2) (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T))⟩
  have h := rhoA_nonneg hp
  simpa [rhoA, a2c, not_le.mpr ht.1, le_of_lt ht.2] using h
private theorem a3_nonneg {t : ℝ} (ht : t ∈ Ioo params.theta eta) : 0 ≤ a3c t := by
  have hp : t ∈ Icc (0 : ℝ) T := ⟨le_trans zero_le_theta (le_of_lt ht.1),
    le_trans (le_of_lt ht.2) (le_trans eta_le_tau tau_le_T)⟩
  have h := rhoA_nonneg hp
  have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta ht.1
  simpa [rhoA, a3c, not_le.mpr hphi, not_le.mpr ht.1, le_of_lt ht.2] using h
private theorem a4_nonneg {t : ℝ} (ht : t ∈ Ioo eta tau) : 0 ≤ a4c t := by
  have hp : t ∈ Icc (0 : ℝ) T := ⟨le_trans (le_trans zero_le_theta theta_le_eta) (le_of_lt ht.1),
    le_trans (le_of_lt ht.2) tau_le_T⟩
  have h := rhoA_nonneg hp
  have htheta : params.theta < t := lt_of_le_of_lt theta_le_eta ht.1
  have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
  simpa [rhoA, a4c, not_le.mpr hphi, not_le.mpr htheta, not_le.mpr ht.1,
    le_of_lt ht.2] using h
private theorem a5_nonneg (t : ℝ) : 0 ≤ a5c t := by norm_num [a5c]

private theorem c1_nonneg (t : ℝ) : 0 ≤ c1c t := by norm_num [c1c]
private theorem c2_nonneg {t : ℝ} (ht : t ∈ Ioo params.phi params.theta) : 0 ≤ c2c t := by
  have hp : t ∈ Icc (0 : ℝ) T := ⟨le_trans phi_nonneg (le_of_lt ht.1),
    le_trans (le_of_lt ht.2) (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T))⟩
  have h := rhoC_nonneg hp
  simpa [rhoC, c2c, not_le.mpr ht.1, le_of_lt ht.2] using h
private theorem c3_nonneg {t : ℝ} (ht : t ∈ Ioo params.theta eta) : 0 ≤ c3c t := by
  have hp : t ∈ Icc (0 : ℝ) T := ⟨le_trans zero_le_theta (le_of_lt ht.1),
    le_trans (le_of_lt ht.2) (le_trans eta_le_tau tau_le_T)⟩
  have h := rhoC_nonneg hp
  have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta ht.1
  simpa [rhoC, c3c, not_le.mpr hphi, not_le.mpr ht.1, le_of_lt ht.2] using h
private theorem c4_nonneg {t : ℝ} (ht : t ∈ Ioo eta tau) : 0 ≤ c4c t := by
  have hp : t ∈ Icc (0 : ℝ) T := ⟨le_trans (le_trans zero_le_theta theta_le_eta) (le_of_lt ht.1),
    le_trans (le_of_lt ht.2) tau_le_T⟩
  have h := rhoC_nonneg hp
  have htheta : params.theta < t := lt_of_le_of_lt theta_le_eta ht.1
  have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
  simpa [rhoC, c4c, not_le.mpr hphi, not_le.mpr htheta, not_le.mpr ht.1,
    le_of_lt ht.2] using h
private theorem c5_nonneg (t : ℝ) : 0 ≤ c5c t := by simp [c5c]

/-- The horizontal rotating-frame projection recovers the first body coordinate. -/
theorem rot_dot_u (t : ℝ) (z : Point) : dot (Romik.rot t z) (u t) = z.1 := by
  dsimp [dot, Romik.rot, u]
  calc
    (Real.cos t * z.1 - Real.sin t * z.2) * Real.cos t +
        (Real.sin t * z.1 + Real.cos t * z.2) * Real.sin t
        = z.1 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
    _ = z.1 := by rw [Real.sin_sq_add_cos_sq]; ring

/-- The vertical rotating-frame projection recovers the second body coordinate. -/
theorem rot_dot_v (t : ℝ) (z : Point) : dot (Romik.rot t z) (v t) = z.2 := by
  dsimp [dot, Romik.rot, v]
  calc
    (Real.cos t * z.1 - Real.sin t * z.2) * (-Real.sin t) +
        (Real.sin t * z.1 + Real.cos t * z.2) * Real.cos t
        = z.2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
    _ = z.2 := by rw [Real.sin_sq_add_cos_sq]; ring

/-- Rotation in body coordinates is injective. -/
theorem rot_injective (t : ℝ) : Function.Injective (Romik.rot t) := by
  intro x y h
  have hu := congrArg (fun z => dot z (u t)) h
  have hv := congrArg (fun z => dot z (v t)) h
  rw [rot_dot_u, rot_dot_u] at hu
  rw [rot_dot_v, rot_dot_v] at hv
  exact Prod.ext hu hv

private theorem pathPrime1_eq_rot (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime1 p t = Romik.rot t (Romik.alphaBeta1 p t) := rfl
private theorem pathPrime2_eq_rot (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime2 p t = Romik.rot t (Romik.alphaBeta2 p t) := rfl
private theorem pathPrime3_eq_rot (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime3 p t = Romik.rot t (Romik.alphaBeta3 p t) := rfl

private theorem matchPrime12 : Romik.pathPrime1 params params.phi = Romik.pathPrime2 params
  params.phi := by
  have h10 := congrFun params_equations (10 : Fin 22)
  have h11 := congrFun params_equations (11 : Fin 22)
  simp [Romik.system] at h10 h11
  apply Prod.ext <;> linarith
private theorem matchPrime23 : Romik.pathPrime2 params params.theta = Romik.pathPrime3 params
  params.theta := by
  have h14 := congrFun params_equations (14 : Fin 22)
  have h15 := congrFun params_equations (15 : Fin 22)
  simp [Romik.system] at h14 h15
  apply Prod.ext <;> linarith
private theorem matchAB12 : Romik.alphaBeta1 params params.phi = Romik.alphaBeta2 params
  params.phi := by
  apply rot_injective params.phi
  simpa [pathPrime1_eq_rot, pathPrime2_eq_rot] using matchPrime12
private theorem matchAB23 : Romik.alphaBeta2 params params.theta = Romik.alphaBeta3 params
  params.theta := by
  apply rot_injective params.theta
  simpa [pathPrime2_eq_rot, pathPrime3_eq_rot] using matchPrime23

private def reflAB (z : Point) : Point := (-z.2, -z.1)
private theorem ab4_reflect_ab2 (t : ℝ) : Romik.alphaBeta4 params (T - t) = reflAB
  (Romik.alphaBeta2 params t) := by
  dsimp [T, reflAB, Romik.alphaBeta4, Romik.alphaBeta2]
  rw [Romik.d1_eq_quarterPi_sub_b1_of_equations params_equations,
      Romik.d2_eq_b2_add_quarterPi_correction_of_equations params_equations]
  ring_nf
private theorem ab3_reflect (t : ℝ) : Romik.alphaBeta3 params (T - t) = reflAB (Romik.alphaBeta3
  params t) := by
  dsimp [T, reflAB, Romik.alphaBeta3]
  rw [Romik.c2_eq_c1_sub_halfPi_of_equations params_equations]
  ring_nf
private theorem ab5_reflect_ab1 (t : ℝ) : Romik.alphaBeta5 params (T - t) = reflAB
  (Romik.alphaBeta1 params t) := by
  dsimp [T, reflAB, Romik.alphaBeta5, Romik.alphaBeta1]
  rw [Romik.e1_eq_a1_of_equations params_equations,
      Romik.e2_eq_neg_a2_of_equations params_equations]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring_nf
private theorem matchAB34 : Romik.alphaBeta3 params eta = Romik.alphaBeta4 params eta := by
  have h3 := ab3_reflect params.theta
  have h4 := ab4_reflect_ab2 params.theta
  have hm := congrArg reflAB matchAB23
  simpa [eta] using h3.trans (hm.symm.trans h4.symm)
private theorem matchAB45 : Romik.alphaBeta4 params tau = Romik.alphaBeta5 params tau := by
  have h4 := ab4_reflect_ab2 params.phi
  have h5 := ab5_reflect_ab1 params.phi
  have hm := congrArg reflAB matchAB12
  simpa [tau] using h4.trans (hm.symm.trans h5.symm)

private theorem A_eq_phase1 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) params.phi) : A t = phaseA1 t := by
  apply Prod.ext <;> simp [A, alpha, alphaBetaAt, Romik.path, phaseA1, ht.2]

private theorem A_eq_phase2 {t : ℝ} (ht : t ∈ Icc params.phi params.theta) : A t = phaseA2 t := by
  by_cases h : t = params.phi
  · subst t
    calc
      A params.phi = phaseA1 params.phi := A_eq_phase1 ⟨phi_nonneg, le_rfl⟩
      _ = phaseA2 params.phi := by
        unfold phaseA1 phaseA2
        rw [PartB.match12, matchAB12]
  · have hp : params.phi < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    apply Prod.ext <;> simp [A, alpha, alphaBetaAt, Romik.path, phaseA2, not_le.mpr hp, ht.2]

private theorem A_eq_phase3 {t : ℝ} (ht : t ∈ Icc params.theta eta) : A t = phaseA3 t := by
  by_cases h : t = params.theta
  · subst t
    calc
      A params.theta = phaseA2 params.theta := A_eq_phase2 ⟨switchOrder.phi_le_theta, le_rfl⟩
      _ = phaseA3 params.theta := by
        unfold phaseA2 phaseA3
        rw [PartB.match23, matchAB23]
  · have htheta : params.theta < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
    have hηraw : t ≤ Real.pi / 2 - params.theta := by
      simpa [eta, T] using ht.2
    apply Prod.ext <;> simp [A, alpha, alphaBetaAt, Romik.path, phaseA3, not_le.mpr hphi,
      not_le.mpr htheta, hηraw, eta, T]

private theorem A_eq_phase4 {t : ℝ} (ht : t ∈ Icc eta tau) : A t = phaseA4 t := by
  by_cases h : t = eta
  · subst t
    have hm : Romik.path3 params eta = Romik.path4 params eta := by
      simpa [eta, T] using PartB.match34
    calc
      A eta = phaseA3 eta := A_eq_phase3 ⟨theta_le_eta, le_rfl⟩
      _ = phaseA4 eta := by
        unfold phaseA3 phaseA4
        rw [hm, matchAB34]
  · have he : eta < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have htheta : params.theta < t := lt_of_le_of_lt theta_le_eta he
    have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
    have hηraw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using he
    have hτraw : t ≤ Real.pi / 2 - params.phi := by
      simpa [tau, T] using ht.2
    apply Prod.ext <;> simp [A, alpha, alphaBetaAt, Romik.path, phaseA4, not_le.mpr hphi,
      not_le.mpr htheta, not_le.mpr hηraw, hτraw, eta, tau, T]

private theorem A_eq_phase5 {t : ℝ} (ht : t ∈ Icc tau T) : A t = phaseA5 t := by
  by_cases h : t = tau
  · subst t
    have hm : Romik.path4 params tau = Romik.path5 params tau := by
      simpa [tau, T] using PartB.match45
    calc
      A tau = phaseA4 tau := A_eq_phase4 ⟨eta_le_tau, le_rfl⟩
      _ = phaseA5 tau := by
        unfold phaseA4 phaseA5
        rw [hm, matchAB45]
  · have htau : tau < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have heta : eta < t := lt_of_le_of_lt eta_le_tau htau
    have htheta : params.theta < t := lt_of_le_of_lt theta_le_eta heta
    have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
    have hηraw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using heta
    have hτraw : Real.pi / 2 - params.phi < t := by
      simpa [tau, T] using htau
    apply Prod.ext <;> simp [A, alpha, alphaBetaAt, Romik.path, phaseA5, not_le.mpr hphi,
      not_le.mpr htheta, not_le.mpr hηraw, not_le.mpr hτraw, eta, tau, T]

private theorem C_eq_phase1 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) params.phi) : C t = phaseC1 t := by
  apply Prod.ext <;> simp [C, beta, alphaBetaAt, Romik.path, phaseC1, ht.2]

private theorem C_eq_phase2 {t : ℝ} (ht : t ∈ Icc params.phi params.theta) : C t = phaseC2 t := by
  by_cases h : t = params.phi
  · subst t
    calc
      C params.phi = phaseC1 params.phi := C_eq_phase1 ⟨phi_nonneg, le_rfl⟩
      _ = phaseC2 params.phi := by
        unfold phaseC1 phaseC2
        rw [PartB.match12, matchAB12]
  · have hp : params.phi < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    apply Prod.ext <;> simp [C, beta, alphaBetaAt, Romik.path, phaseC2, not_le.mpr hp, ht.2]

private theorem C_eq_phase3 {t : ℝ} (ht : t ∈ Icc params.theta eta) : C t = phaseC3 t := by
  by_cases h : t = params.theta
  · subst t
    calc
      C params.theta = phaseC2 params.theta := C_eq_phase2 ⟨switchOrder.phi_le_theta, le_rfl⟩
      _ = phaseC3 params.theta := by
        unfold phaseC2 phaseC3
        rw [PartB.match23, matchAB23]
  · have htheta : params.theta < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
    have hηraw : t ≤ Real.pi / 2 - params.theta := by
      simpa [eta, T] using ht.2
    apply Prod.ext <;> simp [C, beta, alphaBetaAt, Romik.path, phaseC3, not_le.mpr hphi,
      not_le.mpr htheta, hηraw, eta, T]

private theorem C_eq_phase4 {t : ℝ} (ht : t ∈ Icc eta tau) : C t = phaseC4 t := by
  by_cases h : t = eta
  · subst t
    have hm : Romik.path3 params eta = Romik.path4 params eta := by
      simpa [eta, T] using PartB.match34
    calc
      C eta = phaseC3 eta := C_eq_phase3 ⟨theta_le_eta, le_rfl⟩
      _ = phaseC4 eta := by
        unfold phaseC3 phaseC4
        rw [hm, matchAB34]
  · have he : eta < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have htheta : params.theta < t := lt_of_le_of_lt theta_le_eta he
    have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
    have hηraw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using he
    have hτraw : t ≤ Real.pi / 2 - params.phi := by
      simpa [tau, T] using ht.2
    apply Prod.ext <;> simp [C, beta, alphaBetaAt, Romik.path, phaseC4, not_le.mpr hphi,
      not_le.mpr htheta, not_le.mpr hηraw, hτraw, eta, tau, T]

private theorem C_eq_phase5 {t : ℝ} (ht : t ∈ Icc tau T) : C t = phaseC5 t := by
  by_cases h : t = tau
  · subst t
    have hm : Romik.path4 params tau = Romik.path5 params tau := by
      simpa [tau, T] using PartB.match45
    calc
      C tau = phaseC4 tau := C_eq_phase4 ⟨eta_le_tau, le_rfl⟩
      _ = phaseC5 tau := by
        unfold phaseC4 phaseC5
        rw [hm, matchAB45]
  · have htau : tau < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have heta : eta < t := lt_of_le_of_lt eta_le_tau htau
    have htheta : params.theta < t := lt_of_le_of_lt theta_le_eta heta
    have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
    have hηraw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using heta
    have hτraw : Real.pi / 2 - params.phi < t := by
      simpa [tau, T] using htau
    apply Prod.ext <;> simp [C, beta, alphaBetaAt, Romik.path, phaseC5, not_le.mpr hphi,
      not_le.mpr htheta, not_le.mpr hηraw, not_le.mpr hτraw, eta, tau, T]

private theorem C5_hasDerivAt_coeff (t : ℝ) :
    HasDerivAt phaseC5 ((-(c5c t)) • u t) t := by
  simpa [c5c] using C5_hasDerivAt_public t

private theorem transfer_mono_A {F : ℝ → Point} {a b : ℝ} {w : Point}
    (heq : ∀ t ∈ Icc a b, A t = F t)
    (hm : MonotoneOn (fun t => dot (F t) w) (Icc a b)) :
    MonotoneOn (fun t => dot (A t) w) (Icc a b) := by
  intro x hx y hy hxy
  simpa [heq x hx, heq y hy] using hm hx hy hxy
private theorem transfer_anti_A {F : ℝ → Point} {a b : ℝ} {w : Point}
    (heq : ∀ t ∈ Icc a b, A t = F t)
    (hm : AntitoneOn (fun t => dot (F t) w) (Icc a b)) :
    AntitoneOn (fun t => dot (A t) w) (Icc a b) := by
  intro x hx y hy hxy
  simpa [heq x hx, heq y hy] using hm hx hy hxy
private theorem transfer_mono_C {F : ℝ → Point} {a b : ℝ} {w : Point}
    (heq : ∀ t ∈ Icc a b, C t = F t)
    (hm : MonotoneOn (fun t => dot (F t) w) (Icc a b)) :
    MonotoneOn (fun t => dot (C t) w) (Icc a b) := by
  intro x hx y hy hxy
  simpa [heq x hx, heq y hy] using hm hx hy hxy
private theorem transfer_anti_C {F : ℝ → Point} {a b : ℝ} {w : Point}
    (heq : ∀ t ∈ Icc a b, C t = F t)
    (hm : AntitoneOn (fun t => dot (F t) w) (Icc a b)) :
    AntitoneOn (fun t => dot (C t) w) (Icc a b) := by
  intro x hx y hy hxy
  simpa [heq x hx, heq y hy] using hm hx hy hxy

private theorem phase_A_own_mono {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ t, HasDerivAt F ((r t) • v t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (ha0 : 0 ≤ a) (hbs : b ≤ s) (hsT : s ≤ T) :
    MonotoneOn (fun t => dot (F t) (u s)) (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => dot ((r t) • v t) (u s))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (u s)).continuousAt.continuousWithinAt
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (u s)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have hrt := hr t hi
    have ht0 : 0 ≤ t := le_trans ha0 (le_of_lt hi.1)
    have hsin := sin_nonneg_diff ⟨ht0, le_trans (le_of_lt hi.2) (le_trans hbs hsT)⟩
      ⟨le_trans ht0 (le_trans (le_of_lt hi.2) hbs), hsT⟩ (le_trans (le_of_lt hi.2) hbs)
    have heq : dot ((r t) • v t) (u s) = r t * Real.sin (s - t) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonneg hrt hsin

private theorem phase_A_own_anti {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ t, HasDerivAt F ((r t) • v t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (hs0 : 0 ≤ s) (hsa : s ≤ a) (hbT : b ≤ T) :
    AntitoneOn (fun t => dot (F t) (u s)) (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => dot ((r t) • v t) (u s))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (u s)).continuousAt.continuousWithinAt
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (u s)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have hrt := hr t hi
    have htT : t ≤ T := le_trans (le_of_lt hi.2) hbT
    have hsin0 : Real.sin (s - t) ≤ 0 := by
      have hnon : s - t ≤ 0 := by linarith [hsa, hi.1]
      have hnegpi : -Real.pi ≤ s - t := by
        have : t - s ≤ T := by linarith
        nlinarith [T_le_pi]
      exact Real.sin_nonpos_of_nonpos_of_neg_pi_le hnon hnegpi
    have heq : dot ((r t) • v t) (u s) = r t * Real.sin (s - t) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos hrt hsin0

private theorem phase_C_own_mono {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ t, HasDerivAt F ((-(r t)) • u t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (ha0 : 0 ≤ a) (hbs : b ≤ s) (hsT : s ≤ T) :
    MonotoneOn (fun t => dot (F t) (v s)) (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => dot ((-(r t)) • u t) (v s))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (v s)).continuousAt.continuousWithinAt
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (v s)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have hrt := hr t hi
    have ht0 : 0 ≤ t := le_trans ha0 (le_of_lt hi.1)
    have hsin := sin_nonneg_diff ⟨ht0, le_trans (le_of_lt hi.2) (le_trans hbs hsT)⟩
      ⟨le_trans ht0 (le_trans (le_of_lt hi.2) hbs), hsT⟩ (le_trans (le_of_lt hi.2) hbs)
    have heq : dot ((-(r t)) • u t) (v s) = r t * Real.sin (s - t) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonneg hrt hsin

private theorem phase_C_own_anti {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ t, HasDerivAt F ((-(r t)) • u t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (hs0 : 0 ≤ s) (hsa : s ≤ a) (hbT : b ≤ T) :
    AntitoneOn (fun t => dot (F t) (v s)) (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => dot ((-(r t)) • u t) (v s))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (v s)).continuousAt.continuousWithinAt
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (v s)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have hrt := hr t hi
    have hsin0 : Real.sin (s - t) ≤ 0 := by
      have hnon : s - t ≤ 0 := by linarith [hsa, hi.1]
      have hnegpi : -Real.pi ≤ s - t := by
        have : t - s ≤ T := by linarith [hbT, hi.2, hs0]
        nlinarith [T_le_pi]
      exact Real.sin_nonpos_of_nonpos_of_neg_pi_le hnon hnegpi
    have heq : dot ((-(r t)) • u t) (v s) = r t * Real.sin (s - t) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos hrt hsin0

private theorem phase_A_cross_mono {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ t, HasDerivAt F ((r t) • v t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (ha0 : 0 ≤ a) (hbT : b ≤ T) (hs : s ∈ Icc (0 : ℝ) T) :
    MonotoneOn (fun t => dot (F t) (v s)) (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => dot ((r t) • v t) (v s))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (v s)).continuousAt.continuousWithinAt
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (v s)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have hp : t ∈ Icc (0 : ℝ) T := ⟨le_trans ha0 (le_of_lt hi.1), le_trans (le_of_lt hi.2) hbT⟩
    have hc := cos_nonneg_physical hp hs
    have heq : dot ((r t) • v t) (v s) = r t * Real.cos (t - s) := by
      simp [dot, v, Real.cos_sub]
      ring
    rw [heq]
    exact mul_nonneg (hr t hi) hc

private theorem phase_C_cross_anti {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ t, HasDerivAt F ((-(r t)) • u t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (ha0 : 0 ≤ a) (hbT : b ≤ T) (hs : s ∈ Icc (0 : ℝ) T) :
    AntitoneOn (fun t => dot (F t) (u s)) (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => dot ((-(r t)) • u t) (u s))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (u s)).continuousAt.continuousWithinAt
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (u s)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have hp : t ∈ Icc (0 : ℝ) T := ⟨le_trans ha0 (le_of_lt hi.1), le_trans (le_of_lt hi.2) hbT⟩
    have hc := cos_nonneg_physical hp hs
    have heq : dot ((-(r t)) • u t) (u s) = -(r t * Real.cos (t - s)) := by
      simp [dot, u, Real.cos_sub]
      ring
    rw [heq]
    exact neg_nonpos.mpr (mul_nonneg (hr t hi) hc)

private theorem phase_A_y_mono {F : ℝ → Point} {r : ℝ → ℝ} {a b : ℝ}
    (hder : ∀ t, HasDerivAt F ((r t) • v t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (ha0 : 0 ≤ a) (hbT : b ≤ T) :
    MonotoneOn (fun t => dot (F t) (0, 1)) (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun t => dot ((r t) • v t) (0, 1))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht
    exact (dot_hasDerivAt_fixed (hder t) (0, 1)).continuousAt.continuousWithinAt
  · intro t ht
    exact (dot_hasDerivAt_fixed (hder t) (0, 1)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have ht0 : 0 ≤ t := le_trans ha0 (le_of_lt hi.1)
    have htT : t ≤ T := le_trans (le_of_lt hi.2) hbT
    have hc : 0 ≤ Real.cos t := by
      apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      · nlinarith [Real.pi_pos, ht0]
      · simpa [T] using htT
    have heq : dot ((r t) • v t) (0, 1) = r t * Real.cos t := by
      simp [dot, v]
    rw [heq]
    exact mul_nonneg (hr t hi) hc

private theorem phase_C_y_anti {F : ℝ → Point} {r : ℝ → ℝ} {a b : ℝ}
    (hder : ∀ t, HasDerivAt F ((-(r t)) • u t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (ha0 : 0 ≤ a) (hbT : b ≤ T) :
    AntitoneOn (fun t => dot (F t) (0, 1)) (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun t => dot ((-(r t)) • u t) (0, 1))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht
    exact (dot_hasDerivAt_fixed (hder t) (0, 1)).continuousAt.continuousWithinAt
  · intro t ht
    exact (dot_hasDerivAt_fixed (hder t) (0, 1)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have ht0 : 0 ≤ t := le_trans ha0 (le_of_lt hi.1)
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht0
        (le_trans (le_trans (le_of_lt hi.2) hbT) T_le_pi)
    have heq : dot ((-(r t)) • u t) (0, 1) = -(r t * Real.sin t) := by
      simp [dot, u]
    rw [heq]
    exact neg_nonpos.mpr (mul_nonneg (hr t hi) hsin)

-- Full physical-phase monotonicities for cross supports and vertical coordinates.
private theorem A_v_global_mono (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    MonotoneOn (fun t => dot (A t) (v s)) (Icc (0 : ℝ) T) := by
  have h1 := transfer_mono_A (w:=v s) (fun t ht => A_eq_phase1 ht)
    (phase_A_cross_mono (r:=a1c) A1_hasDerivAt_public (fun t ht => a1_nonneg t)
      (by rfl) (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau
        tau_le_T))) hs)
  have h2 := transfer_mono_A (w:=v s) (fun t ht => A_eq_phase2 ht)
    (phase_A_cross_mono (r:=a2c) A2_hasDerivAt_public (fun t ht => a2_nonneg ht)
      phi_nonneg (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)) hs)
  have h3 := transfer_mono_A (w:=v s) (fun t ht => A_eq_phase3 ht)
    (phase_A_cross_mono (r:=a3c) A3_hasDerivAt_public (fun t ht => a3_nonneg ht)
      zero_le_theta (le_trans eta_le_tau tau_le_T) hs)
  have h4 := transfer_mono_A (w:=v s) (fun t ht => A_eq_phase4 ht)
    (phase_A_cross_mono (r:=a4c) A4_hasDerivAt_public (fun t ht => a4_nonneg ht)
      (le_trans zero_le_theta theta_le_eta) tau_le_T hs)
  have h5 := transfer_mono_A (w:=v s) (fun t ht => A_eq_phase5 ht)
    (phase_A_cross_mono (r:=a5c) A5_hasDerivAt_public (fun t ht => a5_nonneg t)
      (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) (by rfl) hs)
  have h12 := glue_mono phi_nonneg switchOrder.phi_le_theta h1 h2
  have h123 := glue_mono zero_le_theta theta_le_eta h12 h3
  have h1234 := glue_mono (le_trans zero_le_theta theta_le_eta) eta_le_tau h123 h4
  exact glue_mono
    (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) tau_le_T h1234 h5

private theorem C_u_global_anti (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    AntitoneOn (fun t => dot (C t) (u s)) (Icc (0 : ℝ) T) := by
  have h1 := transfer_anti_C (w:=u s) (fun t ht => C_eq_phase1 ht)
    (phase_C_cross_anti (r:=c1c) C1_hasDerivAt_public (fun t ht => c1_nonneg t)
      (by rfl) (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau
        tau_le_T))) hs)
  have h2 := transfer_anti_C (w:=u s) (fun t ht => C_eq_phase2 ht)
    (phase_C_cross_anti (r:=c2c) C2_hasDerivAt_public (fun t ht => c2_nonneg ht)
      phi_nonneg (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)) hs)
  have h3 := transfer_anti_C (w:=u s) (fun t ht => C_eq_phase3 ht)
    (phase_C_cross_anti (r:=c3c) C3_hasDerivAt_public (fun t ht => c3_nonneg ht)
      zero_le_theta (le_trans eta_le_tau tau_le_T) hs)
  have h4 := transfer_anti_C (w:=u s) (fun t ht => C_eq_phase4 ht)
    (phase_C_cross_anti (r:=c4c) C4_hasDerivAt_public (fun t ht => c4_nonneg ht)
      (le_trans zero_le_theta theta_le_eta) tau_le_T hs)
  have h5 := transfer_anti_C (w:=u s) (fun t ht => C_eq_phase5 ht)
    (phase_C_cross_anti (r:=c5c) C5_hasDerivAt_coeff (fun t ht => c5_nonneg t)
      (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) (by rfl) hs)
  have h12 := glue_anti phi_nonneg switchOrder.phi_le_theta h1 h2
  have h123 := glue_anti zero_le_theta theta_le_eta h12 h3
  have h1234 := glue_anti (le_trans zero_le_theta theta_le_eta) eta_le_tau h123 h4
  exact glue_anti
    (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) tau_le_T h1234 h5

private theorem A_y_global_mono :
    MonotoneOn (fun t => dot (A t) (0, 1)) (Icc (0 : ℝ) T) := by
  have h1 := transfer_mono_A (w:=(0,1)) (fun t ht => A_eq_phase1 ht)
    (phase_A_y_mono (r:=a1c) A1_hasDerivAt_public (fun t ht => a1_nonneg t)
      (by rfl) (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau
        tau_le_T))))
  have h2 := transfer_mono_A (w:=(0,1)) (fun t ht => A_eq_phase2 ht)
    (phase_A_y_mono (r:=a2c) A2_hasDerivAt_public (fun t ht => a2_nonneg ht)
      phi_nonneg (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)))
  have h3 := transfer_mono_A (w:=(0,1)) (fun t ht => A_eq_phase3 ht)
    (phase_A_y_mono (r:=a3c) A3_hasDerivAt_public (fun t ht => a3_nonneg ht)
      zero_le_theta (le_trans eta_le_tau tau_le_T))
  have h4 := transfer_mono_A (w:=(0,1)) (fun t ht => A_eq_phase4 ht)
    (phase_A_y_mono (r:=a4c) A4_hasDerivAt_public (fun t ht => a4_nonneg ht)
      (le_trans zero_le_theta theta_le_eta) tau_le_T)
  have h5 := transfer_mono_A (w:=(0,1)) (fun t ht => A_eq_phase5 ht)
    (phase_A_y_mono (r:=a5c) A5_hasDerivAt_public (fun t ht => a5_nonneg t)
      (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) (by rfl))
  have h12 := glue_mono phi_nonneg switchOrder.phi_le_theta h1 h2
  have h123 := glue_mono zero_le_theta theta_le_eta h12 h3
  have h1234 := glue_mono (le_trans zero_le_theta theta_le_eta) eta_le_tau h123 h4
  exact glue_mono
    (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) tau_le_T h1234 h5

private theorem C_y_global_anti :
    AntitoneOn (fun t => dot (C t) (0, 1)) (Icc (0 : ℝ) T) := by
  have h1 := transfer_anti_C (w:=(0,1)) (fun t ht => C_eq_phase1 ht)
    (phase_C_y_anti (r:=c1c) C1_hasDerivAt_public (fun t ht => c1_nonneg t)
      (by rfl) (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau
        tau_le_T))))
  have h2 := transfer_anti_C (w:=(0,1)) (fun t ht => C_eq_phase2 ht)
    (phase_C_y_anti (r:=c2c) C2_hasDerivAt_public (fun t ht => c2_nonneg ht)
      phi_nonneg (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)))
  have h3 := transfer_anti_C (w:=(0,1)) (fun t ht => C_eq_phase3 ht)
    (phase_C_y_anti (r:=c3c) C3_hasDerivAt_public (fun t ht => c3_nonneg ht)
      zero_le_theta (le_trans eta_le_tau tau_le_T))
  have h4 := transfer_anti_C (w:=(0,1)) (fun t ht => C_eq_phase4 ht)
    (phase_C_y_anti (r:=c4c) C4_hasDerivAt_public (fun t ht => c4_nonneg ht)
      (le_trans zero_le_theta theta_le_eta) tau_le_T)
  have h5 := transfer_anti_C (w:=(0,1)) (fun t ht => C_eq_phase5 ht)
    (phase_C_y_anti (r:=c5c) C5_hasDerivAt_coeff (fun t ht => c5_nonneg t)
      (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) (by rfl))
  have h12 := glue_anti phi_nonneg switchOrder.phi_le_theta h1 h2
  have h123 := glue_anti zero_le_theta theta_le_eta h12 h3
  have h1234 := glue_anti (le_trans zero_le_theta theta_le_eta) eta_le_tau h123 h4
  exact glue_anti
    (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) tau_le_T h1234 h5

private theorem A_u_left_mono (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    MonotoneOn (fun t => dot (A t) (u s)) (Icc (0 : ℝ) s) := by
  by_cases h1 : s ≤ params.phi
  · apply transfer_mono_A (w := u s)
    · intro t ht
      exact A_eq_phase1 ⟨ht.1, le_trans ht.2 h1⟩
    · exact phase_A_own_mono (r := a1c) A1_hasDerivAt_public
        (fun t _ => a1_nonneg t) (by rfl) (by rfl) hs.2
  have hphi : params.phi ≤ s := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : s ≤ params.theta
  · have m1 : MonotoneOn (fun t => dot (A t) (u s)) (Icc (0 : ℝ) params.phi) :=
      transfer_mono_A (w := u s) (fun t ht => A_eq_phase1 ht)
        (phase_A_own_mono (r := a1c) A1_hasDerivAt_public
          (fun t _ => a1_nonneg t) (by rfl) hphi hs.2)
    have m2 : MonotoneOn (fun t => dot (A t) (u s)) (Icc params.phi s) := by
      apply transfer_mono_A (w := u s)
      · intro t ht
        exact A_eq_phase2 ⟨ht.1, le_trans ht.2 h2⟩
      · exact phase_A_own_mono (r := a2c) A2_hasDerivAt_public
          (fun t ht => a2_nonneg ⟨ht.1, lt_of_lt_of_le ht.2 h2⟩)
          phi_nonneg (by rfl) hs.2
    exact glue_mono phi_nonneg hphi m1 m2
  have htheta : params.theta ≤ s := le_of_lt (lt_of_not_ge h2)
  by_cases h3 : s ≤ eta
  · have m12 : MonotoneOn (fun t => dot (A t) (u s)) (Icc (0 : ℝ) params.theta) := by
      have m1 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase1 ht)
        (phase_A_own_mono (r := a1c) A1_hasDerivAt_public
          (fun t _ => a1_nonneg t) (by rfl) (le_trans switchOrder.phi_le_theta htheta) hs.2)
      have m2 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase2 ht)
        (phase_A_own_mono (r := a2c) A2_hasDerivAt_public
          (fun t ht => a2_nonneg ht) phi_nonneg htheta hs.2)
      exact glue_mono phi_nonneg switchOrder.phi_le_theta m1 m2
    have m3 : MonotoneOn (fun t => dot (A t) (u s)) (Icc params.theta s) := by
      apply transfer_mono_A (w := u s)
      · intro t ht
        exact A_eq_phase3 ⟨ht.1, le_trans ht.2 h3⟩
      · exact phase_A_own_mono (r := a3c) A3_hasDerivAt_public
          (fun t ht => a3_nonneg ⟨ht.1, lt_of_lt_of_le ht.2 h3⟩)
          zero_le_theta (by rfl) hs.2
    exact glue_mono zero_le_theta htheta m12 m3
  have heta : eta ≤ s := le_of_lt (lt_of_not_ge h3)
  by_cases h4 : s ≤ tau
  · have m123 : MonotoneOn (fun t => dot (A t) (u s)) (Icc (0 : ℝ) eta) := by
      have m1 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase1 ht)
        (phase_A_own_mono (r := a1c) A1_hasDerivAt_public
          (fun t _ => a1_nonneg t) (by rfl)
          (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta heta)) hs.2)
      have m2 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase2 ht)
        (phase_A_own_mono (r := a2c) A2_hasDerivAt_public
          (fun t ht => a2_nonneg ht) phi_nonneg (le_trans theta_le_eta heta) hs.2)
      have m3 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase3 ht)
        (phase_A_own_mono (r := a3c) A3_hasDerivAt_public
          (fun t ht => a3_nonneg ht) zero_le_theta heta hs.2)
      have m12 := glue_mono phi_nonneg switchOrder.phi_le_theta m1 m2
      exact glue_mono zero_le_theta theta_le_eta m12 m3
    have m4 : MonotoneOn (fun t => dot (A t) (u s)) (Icc eta s) := by
      apply transfer_mono_A (w := u s)
      · intro t ht
        exact A_eq_phase4 ⟨ht.1, le_trans ht.2 h4⟩
      · exact phase_A_own_mono (r := a4c) A4_hasDerivAt_public
          (fun t ht => a4_nonneg ⟨ht.1, lt_of_lt_of_le ht.2 h4⟩)
          (le_trans zero_le_theta theta_le_eta) (by rfl) hs.2
    exact glue_mono (le_trans zero_le_theta theta_le_eta) heta m123 m4
  have htau : tau ≤ s := le_of_lt (lt_of_not_ge h4)
  have mpre : MonotoneOn (fun t => dot (A t) (u s)) (Icc (0 : ℝ) tau) := by
    have m1 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase1 ht)
      (phase_A_own_mono (r := a1c) A1_hasDerivAt_public
        (fun t _ => a1_nonneg t) (by rfl)
        (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau htau))) hs.2)
    have m2 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase2 ht)
      (phase_A_own_mono (r := a2c) A2_hasDerivAt_public
        (fun t ht => a2_nonneg ht) phi_nonneg
        (le_trans theta_le_eta (le_trans eta_le_tau htau)) hs.2)
    have m3 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase3 ht)
      (phase_A_own_mono (r := a3c) A3_hasDerivAt_public
        (fun t ht => a3_nonneg ht) zero_le_theta (le_trans eta_le_tau htau) hs.2)
    have m4 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase4 ht)
      (phase_A_own_mono (r := a4c) A4_hasDerivAt_public
        (fun t ht => a4_nonneg ht) (le_trans zero_le_theta theta_le_eta) htau hs.2)
    have m12 := glue_mono phi_nonneg switchOrder.phi_le_theta m1 m2
    have m123 := glue_mono zero_le_theta theta_le_eta m12 m3
    exact glue_mono (le_trans zero_le_theta theta_le_eta) eta_le_tau m123 m4
  have m5 : MonotoneOn (fun t => dot (A t) (u s)) (Icc tau s) := by
    apply transfer_mono_A (w := u s)
    · intro t ht
      exact A_eq_phase5 ⟨ht.1, le_trans ht.2 hs.2⟩
    · exact phase_A_own_mono (r := a5c) A5_hasDerivAt_public
        (fun t _ => a5_nonneg t) (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau)
        (by rfl) hs.2
  exact glue_mono (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) htau mpre m5

private theorem A_u_right_anti (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    AntitoneOn (fun t => dot (A t) (u s)) (Icc s T) := by
  by_cases h1 : s ≤ params.phi
  · have m1 : AntitoneOn (fun t => dot (A t) (u s)) (Icc s params.phi) := by
      apply transfer_anti_A (w := u s)
      · intro t ht
        exact A_eq_phase1 ⟨le_trans hs.1 ht.1, ht.2⟩
      · exact phase_A_own_anti (r := a1c) A1_hasDerivAt_public
          (fun t _ => a1_nonneg t) hs.1 (by rfl)
          (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)))
    have m2 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase2 ht)
      (phase_A_own_anti (r := a2c) A2_hasDerivAt_public
        (fun t ht => a2_nonneg ht) hs.1 h1
        (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)))
    have m3 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase3 ht)
      (phase_A_own_anti (r := a3c) A3_hasDerivAt_public
        (fun t ht => a3_nonneg ht) hs.1 (le_trans h1 switchOrder.phi_le_theta)
        (le_trans eta_le_tau tau_le_T))
    have m4 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase4 ht)
      (phase_A_own_anti (r := a4c) A4_hasDerivAt_public
        (fun t ht => a4_nonneg ht) hs.1
        (le_trans (le_trans h1 switchOrder.phi_le_theta) theta_le_eta) tau_le_T)
    have m5 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase5 ht)
      (phase_A_own_anti (r := a5c) A5_hasDerivAt_public
        (fun t _ => a5_nonneg t) hs.1
        (le_trans (le_trans (le_trans h1 switchOrder.phi_le_theta) theta_le_eta) eta_le_tau)
        (by rfl))
    have m23 := glue_anti switchOrder.phi_le_theta theta_le_eta m2 m3
    have m234 := glue_anti (le_trans switchOrder.phi_le_theta theta_le_eta) eta_le_tau m23 m4
    have m2345 := glue_anti
      (le_trans (le_trans switchOrder.phi_le_theta theta_le_eta) eta_le_tau) tau_le_T m234 m5
    exact glue_anti h1
      (le_trans (le_trans (le_trans switchOrder.phi_le_theta theta_le_eta) eta_le_tau) tau_le_T)
      m1 m2345
  have hphi : params.phi ≤ s := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : s ≤ params.theta
  · have m2 : AntitoneOn (fun t => dot (A t) (u s)) (Icc s params.theta) := by
      apply transfer_anti_A (w := u s)
      · intro t ht
        exact A_eq_phase2 ⟨le_trans hphi ht.1, ht.2⟩
      · exact phase_A_own_anti (r := a2c) A2_hasDerivAt_public
          (fun t ht => a2_nonneg ⟨lt_of_le_of_lt hphi ht.1, ht.2⟩)
          hs.1 (by rfl) (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T))
    have m3 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase3 ht)
      (phase_A_own_anti (r := a3c) A3_hasDerivAt_public
        (fun t ht => a3_nonneg ht) hs.1 h2 (le_trans eta_le_tau tau_le_T))
    have m4 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase4 ht)
      (phase_A_own_anti (r := a4c) A4_hasDerivAt_public
        (fun t ht => a4_nonneg ht) hs.1 (le_trans h2 theta_le_eta) tau_le_T)
    have m5 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase5 ht)
      (phase_A_own_anti (r := a5c) A5_hasDerivAt_public
        (fun t _ => a5_nonneg t) hs.1 (le_trans (le_trans h2 theta_le_eta) eta_le_tau) (by rfl))
    have m34 := glue_anti theta_le_eta eta_le_tau m3 m4
    have m345 := glue_anti (le_trans theta_le_eta eta_le_tau) tau_le_T m34 m5
    exact glue_anti h2
      (le_trans (le_trans theta_le_eta eta_le_tau) tau_le_T) m2 m345
  have htheta : params.theta ≤ s := le_of_lt (lt_of_not_ge h2)
  by_cases h3 : s ≤ eta
  · have m3 : AntitoneOn (fun t => dot (A t) (u s)) (Icc s eta) := by
      apply transfer_anti_A (w := u s)
      · intro t ht
        exact A_eq_phase3 ⟨le_trans htheta ht.1, ht.2⟩
      · exact phase_A_own_anti (r := a3c) A3_hasDerivAt_public
          (fun t ht => a3_nonneg ⟨lt_of_le_of_lt htheta ht.1, ht.2⟩)
          hs.1 (by rfl) (le_trans eta_le_tau tau_le_T)
    have m4 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase4 ht)
      (phase_A_own_anti (r := a4c) A4_hasDerivAt_public
        (fun t ht => a4_nonneg ht) hs.1 h3 tau_le_T)
    have m5 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase5 ht)
      (phase_A_own_anti (r := a5c) A5_hasDerivAt_public
        (fun t _ => a5_nonneg t) hs.1 (le_trans h3 eta_le_tau) (by rfl))
    have m45 := glue_anti eta_le_tau tau_le_T m4 m5
    exact glue_anti h3 (le_trans eta_le_tau tau_le_T) m3 m45
  have heta : eta ≤ s := le_of_lt (lt_of_not_ge h3)
  by_cases h4 : s ≤ tau
  · have m4 : AntitoneOn (fun t => dot (A t) (u s)) (Icc s tau) := by
      apply transfer_anti_A (w := u s)
      · intro t ht
        exact A_eq_phase4 ⟨le_trans heta ht.1, ht.2⟩
      · exact phase_A_own_anti (r := a4c) A4_hasDerivAt_public
          (fun t ht => a4_nonneg ⟨lt_of_le_of_lt heta ht.1, ht.2⟩)
          hs.1 (by rfl) tau_le_T
    have m5 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase5 ht)
      (phase_A_own_anti (r := a5c) A5_hasDerivAt_public
        (fun t _ => a5_nonneg t) hs.1 h4 (by rfl))
    exact glue_anti h4 tau_le_T m4 m5
  have htau : tau ≤ s := le_of_lt (lt_of_not_ge h4)
  apply transfer_anti_A (w := u s)
  · intro t ht
    exact A_eq_phase5 ⟨le_trans htau ht.1, ht.2⟩
  · exact phase_A_own_anti (r := a5c) A5_hasDerivAt_public
      (fun t _ => a5_nonneg t) hs.1 (by rfl) (by rfl)

private theorem C_v_left_mono (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    MonotoneOn (fun t => dot (C t) (v s)) (Icc (0 : ℝ) s) := by
  by_cases h1 : s ≤ params.phi
  · apply transfer_mono_C (w := v s)
    · intro t ht
      exact C_eq_phase1 ⟨ht.1, le_trans ht.2 h1⟩
    · exact phase_C_own_mono (r := c1c) C1_hasDerivAt_public
        (fun t _ => c1_nonneg t) (by rfl) (by rfl) hs.2
  have hphi : params.phi ≤ s := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : s ≤ params.theta
  · have m1 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase1 ht)
      (phase_C_own_mono (r := c1c) C1_hasDerivAt_public
        (fun t _ => c1_nonneg t) (by rfl) hphi hs.2)
    have m2 : MonotoneOn (fun t => dot (C t) (v s)) (Icc params.phi s) := by
      apply transfer_mono_C (w := v s)
      · intro t ht
        exact C_eq_phase2 ⟨ht.1, le_trans ht.2 h2⟩
      · exact phase_C_own_mono (r := c2c) C2_hasDerivAt_public
          (fun t ht => c2_nonneg ⟨ht.1, lt_of_lt_of_le ht.2 h2⟩)
          phi_nonneg (by rfl) hs.2
    exact glue_mono phi_nonneg hphi m1 m2
  have htheta : params.theta ≤ s := le_of_lt (lt_of_not_ge h2)
  by_cases h3 : s ≤ eta
  · have m12 : MonotoneOn (fun t => dot (C t) (v s)) (Icc (0 : ℝ) params.theta) := by
      have m1 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase1 ht)
        (phase_C_own_mono (r := c1c) C1_hasDerivAt_public
          (fun t _ => c1_nonneg t) (by rfl) (le_trans switchOrder.phi_le_theta htheta) hs.2)
      have m2 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase2 ht)
        (phase_C_own_mono (r := c2c) C2_hasDerivAt_public
          (fun t ht => c2_nonneg ht) phi_nonneg htheta hs.2)
      exact glue_mono phi_nonneg switchOrder.phi_le_theta m1 m2
    have m3 : MonotoneOn (fun t => dot (C t) (v s)) (Icc params.theta s) := by
      apply transfer_mono_C (w := v s)
      · intro t ht
        exact C_eq_phase3 ⟨ht.1, le_trans ht.2 h3⟩
      · exact phase_C_own_mono (r := c3c) C3_hasDerivAt_public
          (fun t ht => c3_nonneg ⟨ht.1, lt_of_lt_of_le ht.2 h3⟩)
          zero_le_theta (by rfl) hs.2
    exact glue_mono zero_le_theta htheta m12 m3
  have heta : eta ≤ s := le_of_lt (lt_of_not_ge h3)
  by_cases h4 : s ≤ tau
  · have m123 : MonotoneOn (fun t => dot (C t) (v s)) (Icc (0 : ℝ) eta) := by
      have m1 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase1 ht)
        (phase_C_own_mono (r := c1c) C1_hasDerivAt_public
          (fun t _ => c1_nonneg t) (by rfl)
          (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta heta)) hs.2)
      have m2 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase2 ht)
        (phase_C_own_mono (r := c2c) C2_hasDerivAt_public
          (fun t ht => c2_nonneg ht) phi_nonneg (le_trans theta_le_eta heta) hs.2)
      have m3 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase3 ht)
        (phase_C_own_mono (r := c3c) C3_hasDerivAt_public
          (fun t ht => c3_nonneg ht) zero_le_theta heta hs.2)
      have m12 := glue_mono phi_nonneg switchOrder.phi_le_theta m1 m2
      exact glue_mono zero_le_theta theta_le_eta m12 m3
    have m4 : MonotoneOn (fun t => dot (C t) (v s)) (Icc eta s) := by
      apply transfer_mono_C (w := v s)
      · intro t ht
        exact C_eq_phase4 ⟨ht.1, le_trans ht.2 h4⟩
      · exact phase_C_own_mono (r := c4c) C4_hasDerivAt_public
          (fun t ht => c4_nonneg ⟨ht.1, lt_of_lt_of_le ht.2 h4⟩)
          (le_trans zero_le_theta theta_le_eta) (by rfl) hs.2
    exact glue_mono (le_trans zero_le_theta theta_le_eta) heta m123 m4
  have htau : tau ≤ s := le_of_lt (lt_of_not_ge h4)
  have mpre : MonotoneOn (fun t => dot (C t) (v s)) (Icc (0 : ℝ) tau) := by
    have m1 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase1 ht)
      (phase_C_own_mono (r := c1c) C1_hasDerivAt_public
        (fun t _ => c1_nonneg t) (by rfl)
        (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau htau))) hs.2)
    have m2 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase2 ht)
      (phase_C_own_mono (r := c2c) C2_hasDerivAt_public
        (fun t ht => c2_nonneg ht) phi_nonneg
        (le_trans theta_le_eta (le_trans eta_le_tau htau)) hs.2)
    have m3 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase3 ht)
      (phase_C_own_mono (r := c3c) C3_hasDerivAt_public
        (fun t ht => c3_nonneg ht) zero_le_theta (le_trans eta_le_tau htau) hs.2)
    have m4 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase4 ht)
      (phase_C_own_mono (r := c4c) C4_hasDerivAt_public
        (fun t ht => c4_nonneg ht) (le_trans zero_le_theta theta_le_eta) htau hs.2)
    have m12 := glue_mono phi_nonneg switchOrder.phi_le_theta m1 m2
    have m123 := glue_mono zero_le_theta theta_le_eta m12 m3
    exact glue_mono (le_trans zero_le_theta theta_le_eta) eta_le_tau m123 m4
  have m5 : MonotoneOn (fun t => dot (C t) (v s)) (Icc tau s) := by
    apply transfer_mono_C (w := v s)
    · intro t ht
      exact C_eq_phase5 ⟨ht.1, le_trans ht.2 hs.2⟩
    · exact phase_C_own_mono (r := c5c) C5_hasDerivAt_coeff
        (fun t _ => c5_nonneg t) (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau)
        (by rfl) hs.2
  exact glue_mono (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) htau mpre m5

private theorem C_v_right_anti (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    AntitoneOn (fun t => dot (C t) (v s)) (Icc s T) := by
  by_cases h1 : s ≤ params.phi
  · have m1 : AntitoneOn (fun t => dot (C t) (v s)) (Icc s params.phi) := by
      apply transfer_anti_C (w := v s)
      · intro t ht
        exact C_eq_phase1 ⟨le_trans hs.1 ht.1, ht.2⟩
      · exact phase_C_own_anti (r := c1c) C1_hasDerivAt_public
          (fun t _ => c1_nonneg t) hs.1 (by rfl)
          (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)))
    have m2 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase2 ht)
      (phase_C_own_anti (r := c2c) C2_hasDerivAt_public
        (fun t ht => c2_nonneg ht) hs.1 h1
        (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)))
    have m3 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase3 ht)
      (phase_C_own_anti (r := c3c) C3_hasDerivAt_public
        (fun t ht => c3_nonneg ht) hs.1 (le_trans h1 switchOrder.phi_le_theta)
        (le_trans eta_le_tau tau_le_T))
    have m4 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase4 ht)
      (phase_C_own_anti (r := c4c) C4_hasDerivAt_public
        (fun t ht => c4_nonneg ht) hs.1
        (le_trans (le_trans h1 switchOrder.phi_le_theta) theta_le_eta) tau_le_T)
    have m5 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase5 ht)
      (phase_C_own_anti (r := c5c) C5_hasDerivAt_coeff
        (fun t _ => c5_nonneg t) hs.1
        (le_trans (le_trans (le_trans h1 switchOrder.phi_le_theta) theta_le_eta) eta_le_tau)
        (by rfl))
    have m23 := glue_anti switchOrder.phi_le_theta theta_le_eta m2 m3
    have m234 := glue_anti (le_trans switchOrder.phi_le_theta theta_le_eta) eta_le_tau m23 m4
    have m2345 := glue_anti
      (le_trans (le_trans switchOrder.phi_le_theta theta_le_eta) eta_le_tau) tau_le_T m234 m5
    exact glue_anti h1
      (le_trans (le_trans (le_trans switchOrder.phi_le_theta theta_le_eta) eta_le_tau) tau_le_T)
      m1 m2345
  have hphi : params.phi ≤ s := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : s ≤ params.theta
  · have m2 : AntitoneOn (fun t => dot (C t) (v s)) (Icc s params.theta) := by
      apply transfer_anti_C (w := v s)
      · intro t ht
        exact C_eq_phase2 ⟨le_trans hphi ht.1, ht.2⟩
      · exact phase_C_own_anti (r := c2c) C2_hasDerivAt_public
          (fun t ht => c2_nonneg ⟨lt_of_le_of_lt hphi ht.1, ht.2⟩)
          hs.1 (by rfl) (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T))
    have m3 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase3 ht)
      (phase_C_own_anti (r := c3c) C3_hasDerivAt_public
        (fun t ht => c3_nonneg ht) hs.1 h2 (le_trans eta_le_tau tau_le_T))
    have m4 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase4 ht)
      (phase_C_own_anti (r := c4c) C4_hasDerivAt_public
        (fun t ht => c4_nonneg ht) hs.1 (le_trans h2 theta_le_eta) tau_le_T)
    have m5 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase5 ht)
      (phase_C_own_anti (r := c5c) C5_hasDerivAt_coeff
        (fun t _ => c5_nonneg t) hs.1 (le_trans (le_trans h2 theta_le_eta) eta_le_tau) (by rfl))
    have m34 := glue_anti theta_le_eta eta_le_tau m3 m4
    have m345 := glue_anti (le_trans theta_le_eta eta_le_tau) tau_le_T m34 m5
    exact glue_anti h2
      (le_trans (le_trans theta_le_eta eta_le_tau) tau_le_T) m2 m345
  have htheta : params.theta ≤ s := le_of_lt (lt_of_not_ge h2)
  by_cases h3 : s ≤ eta
  · have m3 : AntitoneOn (fun t => dot (C t) (v s)) (Icc s eta) := by
      apply transfer_anti_C (w := v s)
      · intro t ht
        exact C_eq_phase3 ⟨le_trans htheta ht.1, ht.2⟩
      · exact phase_C_own_anti (r := c3c) C3_hasDerivAt_public
          (fun t ht => c3_nonneg ⟨lt_of_le_of_lt htheta ht.1, ht.2⟩)
          hs.1 (by rfl) (le_trans eta_le_tau tau_le_T)
    have m4 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase4 ht)
      (phase_C_own_anti (r := c4c) C4_hasDerivAt_public
        (fun t ht => c4_nonneg ht) hs.1 h3 tau_le_T)
    have m5 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase5 ht)
      (phase_C_own_anti (r := c5c) C5_hasDerivAt_coeff
        (fun t _ => c5_nonneg t) hs.1 (le_trans h3 eta_le_tau) (by rfl))
    have m45 := glue_anti eta_le_tau tau_le_T m4 m5
    exact glue_anti h3 (le_trans eta_le_tau tau_le_T) m3 m45
  have heta : eta ≤ s := le_of_lt (lt_of_not_ge h3)
  by_cases h4 : s ≤ tau
  · have m4 : AntitoneOn (fun t => dot (C t) (v s)) (Icc s tau) := by
      apply transfer_anti_C (w := v s)
      · intro t ht
        exact C_eq_phase4 ⟨le_trans heta ht.1, ht.2⟩
      · exact phase_C_own_anti (r := c4c) C4_hasDerivAt_public
          (fun t ht => c4_nonneg ⟨lt_of_le_of_lt heta ht.1, ht.2⟩)
          hs.1 (by rfl) tau_le_T
    have m5 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase5 ht)
      (phase_C_own_anti (r := c5c) C5_hasDerivAt_coeff
        (fun t _ => c5_nonneg t) hs.1 h4 (by rfl))
    exact glue_anti h4 tau_le_T m4 m5
  have htau : tau ≤ s := le_of_lt (lt_of_not_ge h4)
  apply transfer_anti_C (w := v s)
  · intro t ht
    exact C_eq_phase5 ⟨le_trans htau ht.1, ht.2⟩
  · exact phase_C_own_anti (r := c5c) C5_hasDerivAt_coeff
      (fun t _ => c5_nonneg t) hs.1 (by rfl) (by rfl)

theorem A_own_max (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    ∀ t ∈ Icc (0 : ℝ) T, dot (A t) (u s) ≤ dot (A s) (u s) := by
  intro t ht
  by_cases hts : t ≤ s
  · exact A_u_left_mono s hs ⟨ht.1, hts⟩ ⟨hs.1, le_rfl⟩ hts
  · have hst : s ≤ t := le_of_lt (lt_of_not_ge hts)
    exact A_u_right_anti s hs ⟨le_rfl, hs.2⟩ ⟨hst, ht.2⟩ hst

theorem C_own_max (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    ∀ t ∈ Icc (0 : ℝ) T, dot (C t) (v s) ≤ dot (C s) (v s) := by
  intro t ht
  by_cases hts : t ≤ s
  · exact C_v_left_mono s hs ⟨ht.1, hts⟩ ⟨hs.1, le_rfl⟩ hts
  · have hst : s ≤ t := le_of_lt (lt_of_not_ge hts)
    exact C_v_right_anti s hs ⟨le_rfl, hs.2⟩ ⟨hst, ht.2⟩ hst

private theorem a1_lower : (6 / 5 : ℝ) ≤ params.a1 := by
  have h := Romik.a1_lower_bound_of_mem_box params_mem
  norm_num at h ⊢
  linarith

private theorem k51_lower : (-11 / 10 : ℝ) ≤ params.k51 := by
  have hp := params_mem
  dsimp [Romik.box] at hp
  have hlo :
      qR (-20344080735756291713874857283) 20000000000000000000000000000 ≤ params.k51 := by
    aesop
  norm_num [qR] at hlo ⊢
  linarith

private theorem endpointGap_nonneg : 0 ≤ 3 * params.a1 + params.k51 - 1 := by
  nlinarith [a1_lower, k51_lower]

private theorem path5_fst_formula (p : Romik.Params) (t : ℝ) :
    (Romik.path5 p t).1 =
      Real.cos t * (p.e1 * Real.cos t + p.e2 * Real.sin t - 1 / 2) -
        Real.sin t * (-p.e2 * Real.cos t + p.e1 * Real.sin t - 1) + p.k51 := by
  rfl

private theorem C_zero_formula : C 0 = (1 - 2 * params.a1, 1) := by
  have hphi : (0 : ℝ) ≤ params.phi := phi_nonneg
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  change
    ((Romik.path params 0).1 - beta 0 * (u 0).1 + (v 0).1,
     (Romik.path params 0).2 - beta 0 * (u 0).2 + (v 0).2) =
      (1 - 2 * params.a1, 1)
  rw [pathZero]
  apply Prod.ext <;> simp [beta, alphaBetaAt, hphi, Romik.alphaBeta1, u, v, ha2]

private theorem A_T_formula : A T = (params.a1 + params.k51, 1) := by
  have he1 := Romik.e1_eq_a1_of_equations params_equations
  have he2 := Romik.e2_eq_quarter_of_equations params_equations
  have hphase : A T = phaseA5 T := A_eq_phase5 ⟨tau_le_T, le_rfl⟩
  rw [hphase]
  apply Prod.ext
  · simp [phaseA5, path5_fst_formula, Romik.alphaBeta5, u, v, T, he1, he2]; ring
  · have hpath : Romik.path params T = Romik.path5 params T := by
      simpa [T] using Romik.path_halfPi_eq_path5_of_mem_box params_mem
    have hy : (Romik.path5 params T).2 = 0 := by
      rw [← hpath]
      exact pathEndYZero
    have hyHalfPi : (Romik.path5 params (Real.pi / 2)).2 = 0 := by
      simpa [T] using hy
    simp [phaseA5, hyHalfPi, Romik.alphaBeta5, u, v, T, he1, he2]

private theorem endpoint_relation : A T = C 0 + (3 * params.a1 + params.k51 - 1) • (1, 0) := by
  rw [A_T_formula, C_zero_formula]
  apply Prod.ext <;> simp; ring

private theorem A_T_v_le_C_zero_v (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    dot (A T) (v s) ≤ dot (C 0) (v s) := by
  rw [endpoint_relation]
  have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (le_trans hs.2 T_le_pi)
  simp [dot, v]
  nlinarith [endpointGap_nonneg]

private theorem C_zero_u_le_A_T_u (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    dot (C 0) (u s) ≤ dot (A T) (u s) := by
  rw [endpoint_relation]
  rcases hs with ⟨hs0, hsT⟩
  have hc : 0 ≤ Real.cos s := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · dsimp [T] at hsT ⊢
      nlinarith [Real.pi_pos]
    · simpa [T] using hsT
  simp [dot, u]
  nlinarith [endpointGap_nonneg]

theorem A_base_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ (A t).2 := by
  intro t ht
  have hm := A_y_global_mono ⟨le_rfl, T_nonneg⟩ ht ht.1
  have h0 : dot (A 0) (0, 1) = 0 := by
    rw [A_zero_eq_anchor]
    simp [dot, anchor]
  have ht' : dot (A t) (0, 1) = (A t).2 := by simp [dot]
  change dot (A 0) (0, 1) ≤ dot (A t) (0, 1) at hm
  rw [h0, ht'] at hm
  exact hm

theorem C_base_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ (C t).2 := by
  intro t ht
  have hm := C_y_global_anti ht ⟨T_nonneg, le_rfl⟩ ht.2
  have hT : dot (C T) (0, 1) = 0 := by
    simp [dot, C_T_snd_zero]
  have ht' : dot (C t) (0, 1) = (C t).2 := by simp [dot]
  change dot (C T) (0, 1) ≤ dot (C t) (0, 1) at hm
  rw [hT, ht'] at hm
  exact hm

theorem supportA_direct : ∀ t ∈ Icc (0 : ℝ) T, A t ∈ K := by
  intro t ht
  rw [Romik.mem_K0]
  refine ⟨A_base_nonneg t ht, ?_⟩
  intro s hs
  have hsT : s ∈ Icc (0 : ℝ) T := by simpa [T] using hs
  constructor
  · change dot (A t) (u s) ≤ dot (Romik.path params s) (u s) + 1
    have hmax := A_own_max s hsT t ht
    rw [A_support_identity] at hmax
    exact hmax
  · change dot (A t) (v s) ≤ dot (Romik.path params s) (v s) + 1
    have hmono := A_v_global_mono s hsT ht ⟨T_nonneg, le_rfl⟩ ht.2
    have hsep := A_T_v_le_C_zero_v s hsT
    have hmax := C_own_max s hsT 0 ⟨le_rfl, T_nonneg⟩
    have hid := C_support_identity s
    linarith

theorem supportC_direct : ∀ t ∈ Icc (0 : ℝ) T, C t ∈ K := by
  intro t ht
  rw [Romik.mem_K0]
  refine ⟨C_base_nonneg t ht, ?_⟩
  intro s hs
  have hsT : s ∈ Icc (0 : ℝ) T := by simpa [T] using hs
  constructor
  · change dot (C t) (u s) ≤ dot (Romik.path params s) (u s) + 1
    have hanti := C_u_global_anti s hsT ⟨le_rfl, T_nonneg⟩ ht ht.1
    have hsep := C_zero_u_le_A_T_u s hsT
    have hmax := A_own_max s hsT T ⟨T_nonneg, le_rfl⟩
    have hid := A_support_identity s
    linarith
  · change dot (C t) (v s) ≤ dot (Romik.path params s) (v s) + 1
    have hmax := C_own_max s hsT t ht
    rw [C_support_identity] at hmax
    exact hmax

end Stage3
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C direct final assembly

This module bypasses the earlier conditional calculus/branch certificate layers.
The two outer-support fields are now concrete theorems.  What remains here is
exactly the six substantive topology/no-hidden facts; no additional certificate
wrapper is introduced.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage3

/-- Direct global geometry from the concrete support proof and the six exact
remaining topology/no-hidden statements. -/
theorem globalGeometryDirect
    (hU : NoHiddenCrossingU)
    (hV : NoHiddenCrossingV)
    (hboundary : frontier (Romik.niche params) = claimedNicheBoundary)
    (hniche : IsConnected (Romik.niche params))
    (hanchor : anchor ∈ G)
    (hG : IsConnected G) : GlobalGeometryCertificate :=
  { supportA := supportA_direct
    supportC := supportC_direct
    nicheTopology :=
      { noHiddenU := hU
        noHiddenV := hV
        boundary_eq := hboundary
        niche_connected := hniche }
    topology :=
      { anchor_mem := hanchor
        connected := hG } }

end Stage3
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C Stage 4: public path differential layer

Source-clean phase derivatives of the five Gerver path pieces.  These are
provided here as compatibility wrappers around the shared Stage 2 proofs.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

theorem path1_hasDerivAt_public (t : ℝ) :
    HasDerivAt (Romik.path1 params)
      (Romik.rot t (Romik.alphaBeta1 params t)) t :=
  Stage2.path1_hasDerivAt t

theorem path2_hasDerivAt_public (t : ℝ) :
    HasDerivAt (Romik.path2 params)
      (Romik.rot t (Romik.alphaBeta2 params t)) t :=
  Stage2.path2_hasDerivAt t

theorem path3_hasDerivAt_public (t : ℝ) :
    HasDerivAt (Romik.path3 params)
      (Romik.rot t (Romik.alphaBeta3 params t)) t :=
  Stage2.path3_hasDerivAt t

theorem path4_hasDerivAt_public (t : ℝ) :
    HasDerivAt (Romik.path4 params)
      (Romik.rot t (Romik.alphaBeta4 params t)) t :=
  Stage2.path4_hasDerivAt t

theorem path5_hasDerivAt_public (t : ℝ) :
    HasDerivAt (Romik.path5 params)
      (Romik.rot t (Romik.alphaBeta5 params t)) t :=
  Stage2.path5_hasDerivAt t

/-! The five public phase derivative theorems above are the complete differential
interface used by Stage 4.  We intentionally do not assert a global `HasDerivAt`
for the nested-if path at switching times: such a theorem requires a separate
matching-of-derivatives argument and is neither needed nor used by the Part C
closure. -/

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C Stage 4: concrete geometry facts

C21: source-clean root closure.  In particular, branch decisions for the
literal nested-if path are made before endpoint abbreviations are unfolded.
The core-path nonnegativity statement is transported from the already sound
Part B cell enclosure instead of being reproved by a large transcendental
`nlinarith` call.
-/

public section

noncomputable section

open Set

namespace GerverSofa
namespace PartC
namespace Stage4

open Stage2

private theorem T_nonneg : (0 : ℝ) ≤ T := by
  dsimp [T]
  positivity

private theorem T_le_pi : T ≤ Real.pi := by
  dsimp [T]
  nlinarith [Real.pi_pos]

private theorem rat_nonneg_cast {q : ℚ} (h : 0 ≤ q) : (0 : ℝ) ≤ (q : ℝ) := by
  exact_mod_cast h

private theorem rat_pos_cast {q : ℚ} (h : 0 < q) : (0 : ℝ) < (q : ℝ) := by
  exact_mod_cast h

theorem phi_pos : 0 < params.phi := Romik.phi_pos_of_mem_box params_mem

theorem phi_lt_theta : params.phi < params.theta := by
  have hphi := phi_bounds.2
  have htheta := theta_bounds.1
  norm_num at hphi htheta ⊢
  linarith

theorem theta_pos : 0 < params.theta := lt_trans phi_pos phi_lt_theta

theorem theta_lt_eta : params.theta < eta := by
  have htheta := theta_bounds.2
  norm_num at htheta
  dsimp [eta, T]
  nlinarith [Real.pi_gt_three]

theorem eta_lt_tau : eta < tau := by
  dsimp [eta, tau]
  linarith [phi_lt_theta]

theorem eta_lt_T : eta < T := by
  dsimp [eta]
  linarith [theta_pos]

theorem tau_lt_T : tau < T := by
  dsimp [tau]
  linarith [phi_pos]

theorem theta_lt_T : params.theta < T := lt_trans theta_lt_eta eta_lt_T

theorem phi_lt_T : params.phi < T := lt_trans phi_lt_theta theta_lt_T

theorem phi_lt_eta : params.phi < eta := lt_trans phi_lt_theta theta_lt_eta

theorem theta_lt_tau : params.theta < tau :=
  lt_trans theta_lt_eta eta_lt_tau

private theorem path_at_phi :
    Romik.path params params.phi = Romik.path1 params params.phi := by
  simp only [Romik.path, ite_eq_left (le_refl params.phi)]

private theorem path_at_theta :
    Romik.path params params.theta = Romik.path2 params params.theta := by
  simp only [Romik.path, ite_eq_right (not_le.mpr phi_lt_theta),
    ite_eq_left (le_refl params.theta)]

private theorem path_at_eta :
    Romik.path params eta = Romik.path3 params eta := by
  have hraw : eta ≤ Real.pi / 2 - params.theta := by
    rfl
  simp only [Romik.path, ite_eq_right (not_le.mpr phi_lt_eta),
    ite_eq_right (not_le.mpr theta_lt_eta), ite_eq_left hraw]

private theorem path_at_tau :
    Romik.path params tau = Romik.path4 params tau := by
  have hphi : ¬ tau ≤ params.phi := not_le.mpr (lt_trans phi_lt_theta theta_lt_tau)
  have htheta : ¬ tau ≤ params.theta := not_le.mpr theta_lt_tau
  have heta : ¬ tau ≤ Real.pi / 2 - params.theta := by
    simpa [eta, T] using (not_le.mpr eta_lt_tau)
  have htau : tau ≤ Real.pi / 2 - params.phi := by
    rfl
  simp only [Romik.path, ite_eq_right hphi, ite_eq_right htheta, ite_eq_right heta, ite_eq_left
    htau]

/-! ## C23: minimal exact reflection bridge

C22 tried to replace the whole scalar layer at once and regressed badly.  C23
rolls back to the stable C21 file and cherry-picks only the reflection bridge
needed for `D_theta_eq_path_tau`. -/

private def hReflect (z : Point) : Point :=
  (2 * params.k31 - z.1, z.2)

private theorem hReflect_involutive (z : Point) : hReflect (hReflect z) = z := by
  ext <;> simp [hReflect]

private theorem phase24_horizontal_reflection (t : ℝ) :
    (Romik.path4 params (T - t)).1 + (Romik.path2 params t).1 =
      params.k41 + params.k21 := by
  have hd1 := Romik.d1_eq_quarterPi_sub_b1_of_equations params_equations
  have hd2 := Romik.d2_eq_b2_add_quarterPi_correction_of_equations params_equations
  dsimp [T, Romik.path4, Romik.path2, Romik.rot, Romik.addK]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, hd1, hd2]
  ring

private theorem phase3_horizontal_reflection (t : ℝ) :
    (Romik.path3 params (T - t)).1 + (Romik.path3 params t).1 =
      2 * params.k31 := by
  have hc2 := Romik.c2_eq_c1_sub_halfPi_of_equations params_equations
  dsimp [T, Romik.path3, Romik.rot, Romik.addK]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, hc2]
  ring

private theorem k41_add_k21_eq_two_k31 :
    params.k41 + params.k21 = 2 * params.k31 := by
  have h24 := phase24_horizontal_reflection params.theta
  have h33 := phase3_horizontal_reflection params.theta
  have h23 := congrArg Prod.fst PartB.match23
  have h34 := congrArg Prod.fst PartB.match34
  simp only [T] at h24 h33 h34
  linarith

private theorem phase24_reflect (t : ℝ) :
    Romik.path4 params (T - t) = hReflect (Romik.path2 params t) := by
  apply Prod.ext
  · have h := phase24_horizontal_reflection t
    rw [k41_add_k21_eq_two_k31] at h
    dsimp [hReflect]
    linarith
  · have h := Romik.phase24_vertical_reflection_of_equations params_equations t
    have hk := Romik.k42_eq_k22_of_equations params_equations
    rw [hk] at h
    have h' : (Romik.path4 params (T - t)).2 = (Romik.path2 params t).2 := by
      dsimp [T] at ⊢
      linarith [h]
    simpa [hReflect] using h'

private theorem phase3_reflect (t : ℝ) :
    Romik.path3 params (T - t) = hReflect (Romik.path3 params t) := by
  apply Prod.ext
  · have h := phase3_horizontal_reflection t
    dsimp [hReflect]
    linarith
  · have h := Romik.phase3_vertical_reflection_of_equations params_equations t
    simpa [T, hReflect] using h

private theorem rot_dot_u (t : ℝ) (z : Point) :
    dot (Romik.rot t z) (u t) = z.1 :=
  Stage3.rot_dot_u t z

private theorem rot_dot_v (t : ℝ) (z : Point) :
    dot (Romik.rot t z) (v t) = z.2 :=
  Stage3.rot_dot_v t z

private theorem rot_injective (t : ℝ) : Function.Injective (Romik.rot t) :=
  Stage3.rot_injective t

private theorem matchPrime23 :
    Romik.pathPrime2 params params.theta =
      Romik.pathPrime3 params params.theta := by
  have h14 := congrFun params_equations (14 : Fin 22)
  have h15 := congrFun params_equations (15 : Fin 22)
  simp [Romik.system] at h14 h15
  apply Prod.ext <;> linarith

private theorem pathPrime2_eq_rot (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime2 p t = Romik.rot t (Romik.alphaBeta2 p t) := rfl

private theorem pathPrime3_eq_rot (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime3 p t = Romik.rot t (Romik.alphaBeta3 p t) := rfl

private theorem matchAB23 :
    Romik.alphaBeta2 params params.theta =
      Romik.alphaBeta3 params params.theta := by
  apply rot_injective params.theta
  simpa [pathPrime2_eq_rot, pathPrime3_eq_rot] using matchPrime23

private def reflAB (z : Point) : Point := (-z.2, -z.1)

private theorem ab3_reflect (t : ℝ) :
    Romik.alphaBeta3 params (T - t) = reflAB (Romik.alphaBeta3 params t) := by
  dsimp [T, reflAB, Romik.alphaBeta3]
  rw [Romik.c2_eq_c1_sub_halfPi_of_equations params_equations]
  ring_nf

/-- Equation pair 20--21 is exactly the first niche contact. -/
theorem B_eta_eq_path_phi : B eta = Romik.path params params.phi := by
  have h20 := congrFun params_equations (20 : Fin 22)
  have h21 := congrFun params_equations (21 : Fin 22)
  simp only [Romik.system, one_div, Fin.isValue, Matrix.cons_val, Pi.zero_apply] at h20 h21
  have h20' :
      (Romik.path1 params params.phi).1 -
          ((Romik.path3 params eta).1 -
            (Romik.alphaBeta3 params eta).1 * Real.sin eta) = 0 := by
    simpa [eta, T] using h20
  have h21' :
      (Romik.path1 params params.phi).2 -
          ((Romik.path3 params eta).2 +
            (Romik.alphaBeta3 params eta).1 * Real.cos eta) = 0 := by
    simpa [eta, T] using h21
  rw [path_at_phi]
  apply Prod.ext
  · change (Romik.path params eta).1 + alpha eta * (v eta).1 =
      (Romik.path1 params params.phi).1
    rw [path_at_eta]
    have ha : alpha eta = (Romik.alphaBeta3 params eta).1 := by
      simp only [alpha, alphaBetaAt, ite_eq_right (not_le.mpr phi_lt_eta),
        ite_eq_right (not_le.mpr theta_lt_eta), ite_eq_left (le_refl eta)]
    rw [ha]
    simp only [v]
    linarith
  · change (Romik.path params eta).2 + alpha eta * (v eta).2 =
      (Romik.path1 params params.phi).2
    rw [path_at_eta]
    have ha : alpha eta = (Romik.alphaBeta3 params eta).1 := by
      simp only [alpha, alphaBetaAt, ite_eq_right (not_le.mpr phi_lt_eta),
        ite_eq_right (not_le.mpr theta_lt_eta), ite_eq_left (le_refl eta)]
    rw [ha]
    simp only [v]
    linarith

/-- Reflected contact at the other end of the core. -/
theorem D_theta_eq_path_tau : D params.theta = Romik.path params tau := by
  have hb : beta params.theta = (Romik.alphaBeta2 params params.theta).2 := by
    simp only [beta, alphaBetaAt, ite_eq_right (not_le.mpr phi_lt_theta),
      ite_eq_left (le_refl params.theta)]
  have ha : alpha eta = (Romik.alphaBeta3 params eta).1 := by
    simp only [alpha, alphaBetaAt, ite_eq_right (not_le.mpr phi_lt_eta),
      ite_eq_right (not_le.mpr theta_lt_eta), ite_eq_left (le_refl eta)]
  have h3 : Romik.path3 params eta = hReflect (Romik.path2 params params.theta) := by
    calc
      Romik.path3 params eta = hReflect (Romik.path3 params params.theta) := by
        simpa [eta] using phase3_reflect params.theta
      _ = hReflect (Romik.path2 params params.theta) := by
        exact congrArg hReflect PartB.match23.symm
  have hab0 : (Romik.alphaBeta3 params eta).1 =
      -(Romik.alphaBeta3 params params.theta).2 := by
    have h := congrArg Prod.fst (ab3_reflect params.theta)
    simpa [eta, reflAB] using h
  have hab : (Romik.alphaBeta3 params eta).1 =
      -(Romik.alphaBeta2 params params.theta).2 := by
    calc
      (Romik.alphaBeta3 params eta).1 =
          -(Romik.alphaBeta3 params params.theta).2 := hab0
      _ = -(Romik.alphaBeta2 params params.theta).2 := by
        rw [← congrArg Prod.snd matchAB23]
  have hDB : hReflect (D params.theta) = B eta := by
    rw [D, B, path_at_theta, path_at_eta, hb, ha, h3, hab]
    apply Prod.ext
    · simp [hReflect, u, v, eta, T, Real.sin_pi_div_two_sub,
        Real.cos_pi_div_two_sub]
      ring
    · simp [hReflect, u, v, eta, T, Real.sin_pi_div_two_sub,
        Real.cos_pi_div_two_sub]
      ring
  have hTau : Romik.path params tau = hReflect (Romik.path params params.phi) := by
    rw [path_at_tau, path_at_phi]
    calc
      Romik.path4 params tau = hReflect (Romik.path2 params params.phi) := by
        simpa [tau] using phase24_reflect params.phi
      _ = hReflect (Romik.path1 params params.phi) := by
        exact congrArg hReflect PartB.match12.symm
  have hDB' := congrArg hReflect hDB
  rw [hReflect_involutive] at hDB'
  calc
    D params.theta = hReflect (B eta) := hDB'
    _ = hReflect (Romik.path params params.phi) := congrArg hReflect B_eta_eq_path_phi
    _ = Romik.path params tau := hTau.symm

/-- The two base endpoints of the claimed niche boundary lie on `y=0`. -/
theorem B_T_y_zero : (B T).2 = 0 := by
  change (Romik.path params T).2 + alpha T * Real.cos T = 0
  have hEnd : (Romik.path params T).2 = 0 := by
    simpa [T] using pathEndYZero
  rw [hEnd]
  simp [T]

theorem D_zero_y_zero : (D 0).2 = 0 := by
  change (Romik.path params 0).2 - beta 0 * Real.sin 0 = 0
  rw [pathZero]
  norm_num

/-! Exact mesh transport for the literal core path.  Cells 1--62 are uniformly
above the base.  Cells 0 and 63 are intentionally excluded: their interval
hulls contain the terminal base contacts and have a tiny negative lower hull. -/
private theorem core_path_cell_lo_nonneg :
    ∀ i : PartB.Cell, 1 ≤ i.1 → i.1 ≤ 62 →
      (0 : ℚ) ≤ (PartB.cellPathInterval i).2.lo := by
  decide +kernel

/-! C30 strengthens the already kernel-checked cell statement from nonnegativity
to strict positivity on every core cell.  The computation is the same finite
exact-rational decision problem; only the target relation is stronger. -/
private theorem core_path_cell_lo_pos :
    ∀ i : PartB.Cell, 1 ≤ i.1 → i.1 ≤ 62 →
      (0 : ℚ) < (PartB.cellPathInterval i).2.lo := by
  decide +kernel
private theorem cell1_path_y_lo_pos :
    (0 : ℚ) < (PartB.cellPathInterval (1 : PartB.Cell)).2.lo := by
  decide +kernel

/-- The first core contact is strictly above the base. -/
theorem B_eta_y_pos : 0 < (B eta).2 := by
  rw [B_eta_eq_path_phi]
  have hcell : params.phi ∈ PartB.cellSet (1 : PartB.Cell) :=
    ⟨Stage2.node1_lt_phi.le, Stage2.phi_lt_node2.le⟩
  have hphys : params.phi ∈ PartB.physicalInterval := by
    constructor
    · exact phi_pos.le
    · simpa [PartB.physicalInterval, T] using phi_lt_T.le
  have hcontains := PartB.cellPath_contains hcell hphys
  exact lt_of_lt_of_le (rat_pos_cast cell1_path_y_lo_pos) hcontains.2.1

/-- The reflected core contact has the same strictly positive height. -/
theorem D_theta_y_pos : 0 < (D params.theta).2 := by
  rw [D_theta_eq_path_tau, path_at_tau]
  have h24 := Romik.phase24_vertical_reflection_of_equations params_equations params.phi
  have h24' :
      (Romik.path4 params tau).2 - params.k42 =
        (Romik.path2 params params.phi).2 - params.k22 := by
    simpa [tau, T] using h24
  have hk := Romik.k42_eq_k22_of_equations params_equations
  have hm12y := congrArg Prod.snd PartB.match12
  have h := B_eta_y_pos
  rw [B_eta_eq_path_phi, path_at_phi] at h
  nlinarith

/-- Nonnegativity of the literal Gerver path on the core interval, transported
from the already proved Part B interval semantics. -/
theorem path_core_y_nonneg {t : ℝ} (ht : t ∈ Icc params.phi tau) :
    0 ≤ (Romik.path params t).2 := by
  have htPhys : t ∈ PartB.physicalInterval := by
    constructor
    · exact le_trans phi_pos.le ht.1
    · have htT : t ≤ T := le_trans ht.2 tau_lt_T.le
      simpa [PartB.physicalInterval, T] using htT
  rcases PartB.exists_cell_cover htPhys with ⟨i, hi⟩
  have hi1 : 1 ≤ i.1 := by
    by_contra hnot
    have hend : PartB.nodeTime (i.1 + 1) ≤ PartB.nodeTime 1 :=
      PartB.nodeTime_mono (by omega)
    linarith [Stage2.node1_lt_phi, hi.2, ht.1]
  have hi62 : i.1 ≤ 62 := by
    by_contra hnot
    have h63 : 63 ≤ i.1 := by omega
    have hstart : PartB.nodeTime 63 ≤ PartB.nodeTime i.1 :=
      PartB.nodeTime_mono h63
    linarith [Stage2.tau_lt_node63, hstart, hi.1, ht.2]
  have hcontains := PartB.cellPath_contains hi htPhys
  exact le_trans (rat_nonneg_cast (core_path_cell_lo_nonneg i hi1 hi62)) hcontains.2.1

/-- Strict positivity of the literal Gerver path height on the complete core
interval `[phi,tau]`.  C30 transports the exact strict lower hull proved above
through the existing Part B interval-containment theorem. -/
theorem path_core_y_pos {t : ℝ} (ht : t ∈ Icc params.phi tau) :
    0 < (Romik.path params t).2 := by
  have htPhys : t ∈ PartB.physicalInterval := by
    constructor
    · exact le_trans phi_pos.le ht.1
    · have htT : t ≤ T := le_trans ht.2 tau_lt_T.le
      simpa [PartB.physicalInterval, T] using htT
  rcases PartB.exists_cell_cover htPhys with ⟨i, hi⟩
  have hi1 : 1 ≤ i.1 := by
    by_contra hnot
    have hend : PartB.nodeTime (i.1 + 1) ≤ PartB.nodeTime 1 :=
      PartB.nodeTime_mono (by omega)
    linarith [Stage2.node1_lt_phi, hi.2, ht.1]
  have hi62 : i.1 ≤ 62 := by
    by_contra hnot
    have h63 : 63 ≤ i.1 := by omega
    have hstart : PartB.nodeTime 63 ≤ PartB.nodeTime i.1 :=
      PartB.nodeTime_mono h63
    linarith [Stage2.tau_lt_node63, hstart, hi.1, ht.2]
  have hcontains := PartB.cellPath_contains hi htPhys
  exact lt_of_lt_of_le (rat_pos_cast (core_path_cell_lo_pos i hi1 hi62)) hcontains.2.1

/-! A compact phase-2 lower bound for the reflected contact `D`.  It is also
used, by the exact phase-2/phase-4 reflection, to control the late `B` arc. -/
private theorem b1_lower_crude : (-53 / 100 : ℝ) ≤ params.b1 := by
  have hb := PartB.b1_contains.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at hb ⊢
  linarith

private theorem theta_upper_crude : params.theta ≤ (7 / 10 : ℝ) := by
  have h := theta_bounds.2
  norm_num at h ⊢
  linarith

private theorem k22_sub_b1_sub_one_nonneg :
    0 ≤ params.k22 - params.b1 - 1 := by
  have hk := PartB.k22_contains.1
  have hb := PartB.b1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at hk hb ⊢
  linarith

private theorem phase2_D_y_nonneg {t : ℝ}
    (ht0 : 0 ≤ t) (htθ : t ≤ params.theta) :
    0 ≤ (Romik.path2 params t).2 -
      (Romik.alphaBeta2 params t).2 * Real.sin t := by
  have hz : t / 2 - params.b1 - 1 ≤ 0 := by
    nlinarith [b1_lower_crude, theta_upper_crude]
  have hzc : t / 2 - params.b1 - 1 ≤
      (t / 2 - params.b1 - 1) * Real.cos t := by
    have hprod : 0 ≤
        (t / 2 - params.b1 - 1) * (Real.cos t - 1) :=
      mul_nonneg_of_nonpos_of_nonpos hz (sub_nonpos.mpr (Real.cos_le_one t))
    nlinarith
  have hs : Real.sin t ≤ t := Real.sin_le ht0
  simp [Romik.path2, Romik.rot, Romik.addK, Romik.alphaBeta2]
  nlinarith [hzc, hs, k22_sub_b1_sub_one_nonneg]

/-- Nonnegative height of the reflected early contact arc. -/
theorem D_y_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) params.theta) : 0 ≤ (D t).2 := by
  by_cases hphi : t ≤ params.phi
  · have hpath : Romik.path params t = Romik.path1 params t := by
      simp only [Romik.path, ite_eq_left hphi]
    have hb : beta t = (Romik.alphaBeta1 params t).2 := by
      simp only [beta, alphaBetaAt, ite_eq_left hphi]
    change 0 ≤ (Romik.path params t).2 - beta t * Real.sin t
    rw [hpath, hb]
    have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
    have hk12 := Romik.k12_eq_quarter_of_equations params_equations
    simp [Romik.path1, Romik.rot, Romik.addK, Romik.alphaBeta1, ha2, hk12]
    nlinarith [Real.sin_sq_add_cos_sq t, Real.cos_le_one t]
  · have hphi' : params.phi < t := lt_of_not_ge hphi
    have hpath : Romik.path params t = Romik.path2 params t := by
      simp only [Romik.path, ite_eq_right hphi, ite_eq_left ht.2]
    have hb : beta t = (Romik.alphaBeta2 params t).2 := by
      simp only [beta, alphaBetaAt, ite_eq_right hphi, ite_eq_left ht.2]
    change 0 ≤ (Romik.path params t).2 - beta t * Real.sin t
    rw [hpath, hb]
    exact phase2_D_y_nonneg ht.1 ht.2

/-- Nonnegative height of the reflected late contact arc. -/
theorem B_y_nonneg {t : ℝ} (ht : t ∈ Icc eta T) : 0 ≤ (B t).2 := by
  by_cases hetaEq : t = eta
  · subst t
    exact B_eta_y_pos.le
  have hetaT : eta < t := lt_of_le_of_ne ht.1 (Ne.symm hetaEq)
  by_cases htau : t ≤ tau
  · have hphiT : params.phi < t := lt_trans phi_lt_eta hetaT
    have hthetaT : params.theta < t := lt_trans theta_lt_eta hetaT
    have hpath : Romik.path params t = Romik.path4 params t := by
      have hetaRaw : ¬ t ≤ Real.pi / 2 - params.theta := by
        simpa [eta, T] using (not_le.mpr hetaT)
      have htauRaw : t ≤ Real.pi / 2 - params.phi := by
        simpa [tau, T] using htau
      simp only [Romik.path, ite_eq_right (not_le.mpr hphiT),
        ite_eq_right (not_le.mpr hthetaT), ite_eq_right hetaRaw, ite_eq_left htauRaw]
    have ha : alpha t = (Romik.alphaBeta4 params t).1 := by
      simp only [alpha, alphaBetaAt, ite_eq_right (not_le.mpr hphiT),
        ite_eq_right (not_le.mpr hthetaT), ite_eq_right (not_le.mpr hetaT), ite_eq_left htau]
    change 0 ≤ (Romik.path params t).2 + alpha t * Real.cos t
    rw [hpath, ha]
    let s : ℝ := T - t
    have hs0 : 0 ≤ s := by dsimp [s]; linarith [ht.2]
    have hsθ : s ≤ params.theta := by
      dsimp [s, eta] at *
      linarith
    have hD2 := phase2_D_y_nonneg hs0 hsθ
    have hd1 := Romik.d1_eq_quarterPi_sub_b1_of_equations params_equations
    have hk42 := Romik.k42_eq_k22_of_equations params_equations
    have hreflect :
        (Romik.path4 params t).2 +
            (Romik.alphaBeta4 params t).1 * Real.cos t =
          (Romik.path2 params s).2 -
            (Romik.alphaBeta2 params s).2 * Real.sin s := by
      dsimp [s, T]
      simp [Romik.path4, Romik.path2, Romik.rot, Romik.addK,
        Romik.alphaBeta4, Romik.alphaBeta2, hd1, hk42,
        Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
      ring
    rw [hreflect]
    exact hD2
  · have htauT : tau < t := lt_of_not_ge htau
    have hphiT : params.phi < t := lt_trans (lt_trans phi_lt_theta theta_lt_tau) htauT
    have hthetaT : params.theta < t := lt_trans theta_lt_tau htauT
    have hetaT' : eta < t := lt_trans eta_lt_tau htauT
    have hpath : Romik.path params t = Romik.path5 params t := by
      have hetaRaw : ¬ t ≤ Real.pi / 2 - params.theta := by
        simpa [eta, T] using (not_le.mpr hetaT')
      have htauRaw : ¬ t ≤ Real.pi / 2 - params.phi := by
        simpa [tau, T] using (not_le.mpr htauT)
      simp only [Romik.path, ite_eq_right (not_le.mpr hphiT),
        ite_eq_right (not_le.mpr hthetaT), ite_eq_right hetaRaw, ite_eq_right htauRaw]
    have ha : alpha t = (Romik.alphaBeta5 params t).1 := by
      simp only [alpha, alphaBetaAt, ite_eq_right (not_le.mpr hphiT),
        ite_eq_right (not_le.mpr hthetaT), ite_eq_right (not_le.mpr hetaT'), ite_eq_right htau]
    change 0 ≤ (Romik.path params t).2 + alpha t * Real.cos t
    rw [hpath, ha]
    have he2 := Romik.e2_eq_quarter_of_equations params_equations
    have hk52 := Romik.k52_eq_quarter_of_equations params_equations
    simp [Romik.path5, Romik.rot, Romik.addK, Romik.alphaBeta5, he2, hk52]
    nlinarith [Real.sin_sq_add_cos_sq t, Real.sin_le_one t]

/-! C31: strict positivity on the two open contact tails.  The base endpoints
`D 0` and `B T` have height exactly zero, so the natural domains are `Ioc`
and `Ico`.  These statements are used only for topology of the strict vertical
fills; the existing closed-interval nonnegativity theorems remain unchanged. -/
private theorem k22_sub_b1_sub_one_pos :
    0 < params.k22 - params.b1 - 1 := by
  have hk := PartB.k22_contains.1
  have hb := PartB.b1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at hk hb ⊢
  linarith

private theorem phase2_D_y_pos {t : ℝ}
    (ht0 : 0 ≤ t) (htθ : t ≤ params.theta) :
    0 < (Romik.path2 params t).2 -
      (Romik.alphaBeta2 params t).2 * Real.sin t := by
  have hz : t / 2 - params.b1 - 1 ≤ 0 := by
    nlinarith [b1_lower_crude, theta_upper_crude]
  have hzc : t / 2 - params.b1 - 1 ≤
      (t / 2 - params.b1 - 1) * Real.cos t := by
    have hprod : 0 ≤
        (t / 2 - params.b1 - 1) * (Real.cos t - 1) :=
      mul_nonneg_of_nonpos_of_nonpos hz (sub_nonpos.mpr (Real.cos_le_one t))
    nlinarith
  have hs : Real.sin t ≤ t := Real.sin_le ht0
  simp [Romik.path2, Romik.rot, Romik.addK, Romik.alphaBeta2]
  nlinarith [hzc, hs, k22_sub_b1_sub_one_pos]

/-- Strict height of the early reflected contact arc away from its base endpoint. -/
theorem D_y_pos {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) params.theta) :
    0 < (D t).2 := by
  by_cases hphi : t ≤ params.phi
  · have hpath : Romik.path params t = Romik.path1 params t := by
      simp only [Romik.path, ite_eq_left hphi]
    have hb : beta t = (Romik.alphaBeta1 params t).2 := by
      simp only [beta, alphaBetaAt, ite_eq_left hphi]
    change 0 < (Romik.path params t).2 - beta t * Real.sin t
    rw [hpath, hb]
    have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
    have hk12 := Romik.k12_eq_quarter_of_equations params_equations
    have hcos : Real.cos t < 1 := by
      have hc := Real.cos_lt_cos_of_nonneg_of_le_pi
        (x := (0 : ℝ)) (y := t) (by norm_num)
        (le_trans ht.2 (le_trans theta_lt_T.le (by
          dsimp [T]
          linarith [Real.pi_pos]))) ht.1
      simpa using hc
    simp [Romik.path1, Romik.rot, Romik.addK, Romik.alphaBeta1, ha2, hk12]
    nlinarith [Real.sin_sq_add_cos_sq t, hcos]
  · have hpath : Romik.path params t = Romik.path2 params t := by
      simp only [Romik.path, ite_eq_right hphi, ite_eq_left ht.2]
    have hb : beta t = (Romik.alphaBeta2 params t).2 := by
      simp only [beta, alphaBetaAt, ite_eq_right hphi, ite_eq_left ht.2]
    change 0 < (Romik.path params t).2 - beta t * Real.sin t
    rw [hpath, hb]
    exact phase2_D_y_pos ht.1.le ht.2

/-- Strict height of the late contact arc away from its base endpoint. -/
theorem B_y_pos {t : ℝ} (ht : t ∈ Ico eta T) :
    0 < (B t).2 := by
  by_cases hetaEq : t = eta
  · subst t
    exact B_eta_y_pos
  have hetaT : eta < t := lt_of_le_of_ne ht.1 (Ne.symm hetaEq)
  by_cases htau : t ≤ tau
  · have hphiT : params.phi < t := lt_trans phi_lt_eta hetaT
    have hthetaT : params.theta < t := lt_trans theta_lt_eta hetaT
    have hpath : Romik.path params t = Romik.path4 params t := by
      have hetaRaw : ¬ t ≤ Real.pi / 2 - params.theta := by
        simpa [eta, T] using (not_le.mpr hetaT)
      have htauRaw : t ≤ Real.pi / 2 - params.phi := by
        simpa [tau, T] using htau
      simp only [Romik.path, ite_eq_right (not_le.mpr hphiT),
        ite_eq_right (not_le.mpr hthetaT), ite_eq_right hetaRaw, ite_eq_left htauRaw]
    have ha : alpha t = (Romik.alphaBeta4 params t).1 := by
      simp only [alpha, alphaBetaAt, ite_eq_right (not_le.mpr hphiT),
        ite_eq_right (not_le.mpr hthetaT), ite_eq_right (not_le.mpr hetaT), ite_eq_left htau]
    change 0 < (Romik.path params t).2 + alpha t * Real.cos t
    rw [hpath, ha]
    let s : ℝ := T - t
    have hs0 : 0 ≤ s := by
      dsimp [s]
      exact sub_nonneg.mpr ht.2.le
    have hsθ : s ≤ params.theta := by
      dsimp [s, eta] at *
      linarith
    have hD2 := phase2_D_y_pos hs0 hsθ
    have hd1 := Romik.d1_eq_quarterPi_sub_b1_of_equations params_equations
    have hk42 := Romik.k42_eq_k22_of_equations params_equations
    have hreflect :
        (Romik.path4 params t).2 +
            (Romik.alphaBeta4 params t).1 * Real.cos t =
          (Romik.path2 params s).2 -
            (Romik.alphaBeta2 params s).2 * Real.sin s := by
      dsimp [s, T]
      simp [Romik.path4, Romik.path2, Romik.rot, Romik.addK,
        Romik.alphaBeta4, Romik.alphaBeta2, hd1, hk42,
        Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
      ring
    rw [hreflect]
    exact hD2
  · have htauT : tau < t := lt_of_not_ge htau
    have hphiT : params.phi < t := lt_trans (lt_trans phi_lt_theta theta_lt_tau) htauT
    have hthetaT : params.theta < t := lt_trans theta_lt_tau htauT
    have hetaT' : eta < t := lt_trans eta_lt_tau htauT
    have hpath : Romik.path params t = Romik.path5 params t := by
      have hetaRaw : ¬ t ≤ Real.pi / 2 - params.theta := by
        simpa [eta, T] using (not_le.mpr hetaT')
      have htauRaw : ¬ t ≤ Real.pi / 2 - params.phi := by
        simpa [tau, T] using (not_le.mpr htauT)
      simp only [Romik.path, ite_eq_right (not_le.mpr hphiT),
        ite_eq_right (not_le.mpr hthetaT), ite_eq_right hetaRaw, ite_eq_right htauRaw]
    have ha : alpha t = (Romik.alphaBeta5 params t).1 := by
      simp only [alpha, alphaBetaAt, ite_eq_right (not_le.mpr hphiT),
        ite_eq_right (not_le.mpr hthetaT), ite_eq_right (not_le.mpr hetaT'), ite_eq_right htau]
    change 0 < (Romik.path params t).2 + alpha t * Real.cos t
    rw [hpath, ha]
    have he2 := Romik.e2_eq_quarter_of_equations params_equations
    have hk52 := Romik.k52_eq_quarter_of_equations params_equations
    have hsin : Real.sin t < 1 := by
      have hs := Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (x := t) (y := T)
        (by
          have ht0 : 0 ≤ t :=
            le_trans theta_pos.le (le_trans theta_lt_eta.le ht.1)
          nlinarith [Real.pi_pos])
        (by simp [T]) ht.2
      simpa [T] using hs
    simp [Romik.path5, Romik.rot, Romik.addK, Romik.alphaBeta5, he2, hk52]
    nlinarith [Real.sin_sq_add_cos_sq t, hsin]

/-! ## C24: fixed-endpoint separation by a phase-2 Taylor bound and contact monotonicity

C23 reduced the root gate to four scalar `U(phi,t)` residuals.  This replacement
removes the large raw `nlinarith` calls.  Phase 2 is reduced to one variable
`d=t-phi` and certified by low-order alternating Taylor bounds.  Phases 3--5
use the exact contact identity `B(eta)=path(phi)` and the sign of the derivative
of the phase-local `B` contact projected on the fixed normal `u(t)`.
-/

private theorem phi_lower_crude : (39 / 1000 : ℝ) ≤ params.phi := by
  have h := phi_bounds.1
  norm_num at h ⊢
  linarith

private theorem phi_upper_crude : params.phi ≤ (1 / 20 : ℝ) := by
  have h := phi_bounds.2
  norm_num at h ⊢
  linarith

private theorem theta_upper_689 : params.theta ≤ (689 / 1000 : ℝ) := by
  have h := theta_bounds.2
  norm_num at h ⊢
  linarith

private theorem b1_upper_crude : params.b1 ≤ (-527 / 1000 : ℝ) := by
  have h := PartB.b1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem b2_lower_crude : (9 / 10 : ℝ) ≤ params.b2 := by
  have h := PartB.b2_contains.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem b2_upper_921 : params.b2 ≤ (921 / 1000 : ℝ) := by
  have h := PartB.b2_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

open scoped BigOperators
open Filter Finset

private theorem sin_taylor5_upper {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have hanti : Antitone (ExactReplay.sinMagnitude x) :=
    ExactReplay.antitone_sinMagnitude hx0 hx1
  have htendRaw := (Real.hasSum_sin x).tendsto_sum_nat
  have htendMag :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ i * ExactReplay.sinMagnitude x i)
        Filter.atTop (nhds (Real.sin x)) := by
    simpa only [ExactReplay.sinMagnitude, mul_div_assoc] using htendRaw
  have hupper := Antitone.tendsto_le_alternating_series htendMag hanti 1
  have h3 : (2 * 1 + 1 : ℕ) = 3 := by norm_num
  rw [h3] at hupper
  have hsum :
      (∑ i ∈ Finset.range 3,
          (-1 : ℝ) ^ i * ExactReplay.sinMagnitude x i) =
        x - x ^ 3 / 6 + x ^ 5 / 120 := by
    norm_num [ExactReplay.sinMagnitude, Finset.sum_range_succ]; ring
  rw [hsum] at hupper
  exact hupper

private theorem cos_taylor6_lower {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have hanti : Antitone (ExactReplay.cosMagnitude x) :=
    ExactReplay.antitone_cosMagnitude hx0 hx1
  have htendRaw := (Real.hasSum_cos x).tendsto_sum_nat
  have htendMag :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ i * ExactReplay.cosMagnitude x i)
        Filter.atTop (nhds (Real.cos x)) := by
    simpa only [ExactReplay.cosMagnitude, mul_div_assoc] using htendRaw
  have hlower := Antitone.alternating_series_le_tendsto htendMag hanti 2
  have h4 : (2 * 2 : ℕ) = 4 := by norm_num
  rw [h4] at hlower
  have hsum :
      (∑ i ∈ Finset.range 4,
          (-1 : ℝ) ^ i * ExactReplay.cosMagnitude x i) =
        1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 := by
    norm_num [ExactReplay.cosMagnitude, Finset.sum_range_succ]; ring
  rw [hsum] at hlower
  exact hlower

private theorem phase2_U_phi_formula {t : ℝ}
    (hphiT : params.phi < t) (htheta : t ≤ params.theta) :
    Stage2.UValue params.phi t =
      (-(1 / 4 : ℝ) * params.phi * params.phi +
          params.b1 * params.phi + params.b2) *
        (Real.cos (t - params.phi) - 1) +
      (params.phi / 2 - params.b1 - 1) * Real.sin (t - params.phi) +
      (params.phi / 2 - params.b1) * (t - params.phi) +
      (t - params.phi) * (t - params.phi) / 4 := by
  have hPhi2 : Romik.path params params.phi =
      Romik.path2 params params.phi := path_at_phi.trans PartB.match12
  have hPathT : Romik.path params t = Romik.path2 params t := by
    simp only [Romik.path, ite_eq_right (not_le.mpr hphiT), ite_eq_left htheta]
  unfold Stage2.UValue
  rw [hPhi2, hPathT]
  simp [dot, u, Romik.path2, Romik.rot, Romik.addK,
    Real.cos_sub, Real.sin_sub]
  ring_nf
  have hunit : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hb1collapse :
      params.b1 * Real.cos t ^ 2 * t + params.b1 * t * Real.sin t ^ 2 =
        params.b1 * t := by
    calc
      params.b1 * Real.cos t ^ 2 * t + params.b1 * t * Real.sin t ^ 2 =
          params.b1 * t * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
      _ = params.b1 * t := by rw [hunit]; ring
  have hb2collapse :
      params.b2 * Real.cos t ^ 2 + params.b2 * Real.sin t ^ 2 =
        params.b2 := by
    calc
      params.b2 * Real.cos t ^ 2 + params.b2 * Real.sin t ^ 2 =
          params.b2 * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
      _ = params.b2 := by rw [hunit]; ring
  have ht2collapse :
      Real.cos t ^ 2 * t ^ 2 * (1 / 4 : ℝ) +
          t ^ 2 * Real.sin t ^ 2 * (1 / 4 : ℝ) =
        t ^ 2 * (1 / 4 : ℝ) := by
    calc
      Real.cos t ^ 2 * t ^ 2 * (1 / 4 : ℝ) +
          t ^ 2 * Real.sin t ^ 2 * (1 / 4 : ℝ) =
          t ^ 2 * (1 / 4 : ℝ) * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
      _ = t ^ 2 * (1 / 4 : ℝ) := by rw [hunit]; ring
  linarith [hb1collapse, hb2collapse, ht2collapse]
private theorem phase2_U_phi_nonneg {t : ℝ}
    (ht : t ∈ Icc params.phi params.theta) :
    0 ≤ Stage2.UValue params.phi t := by
  by_cases heq : t = params.phi
  · subst t
    simp [Stage2.UValue, dot]
  have hphiT : params.phi < t := lt_of_le_of_ne ht.1 (Ne.symm heq)
  let d : ℝ := t - params.phi
  let z1 : ℝ :=
    -(1 / 4 : ℝ) * params.phi * params.phi +
      params.b1 * params.phi + params.b2
  let z2 : ℝ := params.phi / 2 - params.b1 - 1
  let c : ℝ := params.phi / 2 - params.b1
  have hd0 : 0 ≤ d := by dsimp [d]; linarith
  have hdA : d ≤ (13 / 20 : ℝ) := by
    dsimp [d]
    linarith [theta_upper_689, phi_lower_crude, ht.2]
  have hd1 : d ≤ 1 := by linarith
  have hp0 : 0 ≤ params.phi := phi_pos.le
  have hb1lo := b1_lower_crude
  have hb1hi := b1_upper_crude
  have hz1nonneg : 0 ≤ z1 := by
    have hbp : 0 ≤ (params.b1 + 53 / 100) * params.phi :=
      mul_nonneg (by linarith) hp0
    have hpp : 0 ≤ params.phi * (1 / 20 - params.phi) :=
      mul_nonneg hp0 (by linarith [phi_upper_crude])
    dsimp [z1]
    nlinarith [b2_lower_crude, hbp, hpp]
  have hz1le : z1 ≤ (91 / 100 : ℝ) := by
    have hbp : params.b1 * params.phi ≤ (-527 / 1000 : ℝ) * (39 / 1000 : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right b1_upper_crude hp0
      have h2 := mul_le_mul_of_nonpos_left phi_lower_crude (by norm_num : (-527 / 1000 : ℝ) ≤ 0)
      exact le_trans h1 h2
    have hsquare : 0 ≤ params.phi * params.phi := mul_self_nonneg _
    dsimp [z1]
    nlinarith only [b2_upper_921, hbp, hsquare]
  have hz2lo : (-227 / 500 : ℝ) ≤ z2 := by
    dsimp [z2]
    linarith [phi_lower_crude, b1_upper_crude]
  have hz2hi : z2 ≤ 0 := by
    dsimp [z2]
    linarith [phi_upper_crude, hb1lo]
  have hclo : (273 / 500 : ℝ) ≤ c := by
    dsimp [c]
    linarith [phi_lower_crude, b1_upper_crude]
  have hsinU := sin_taylor5_upper hd0 hd1
  have hcosL := cos_taylor6_lower hd0 hd1
  let SU : ℝ := d - d ^ 3 / 6 + d ^ 5 / 120
  let CL : ℝ := -(d ^ 2) / 2 + d ^ 4 / 24 - d ^ 6 / 720
  have hd2le1 : d ^ 2 ≤ 1 := by
    have hprod : 0 ≤ d * (1 - d) := mul_nonneg hd0 (sub_nonneg.mpr hd1)
    nlinarith only [hprod, hd1]
  have hSU0 : 0 ≤ SU := by
    have hcube : d ^ 3 ≤ d := by
      have hprod : 0 ≤ d * (1 - d ^ 2) :=
        mul_nonneg hd0 (sub_nonneg.mpr hd2le1)
      nlinarith only [hprod]
    have hd5 : 0 ≤ d ^ 5 := by positivity
    dsimp [SU]
    nlinarith only [hcube, hd5, hd0]
  have hCL0 : CL ≤ 0 := by
    have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
    have hd4le : d ^ 4 ≤ d ^ 2 := by
      have h := mul_nonneg hd2 (sub_nonneg.mpr hd2le1)
      nlinarith
    dsimp [CL]
    nlinarith only [sq_nonneg (d ^ 3), hd4le, hd2]
  have hcosm1 : CL ≤ Real.cos d - 1 := by
    dsimp [CL]
    linarith only [hcosL]
  have hsinSU : Real.sin d ≤ SU := by
    dsimp [SU]
    exact hsinU
  have hz1CL : (91 / 100 : ℝ) * CL ≤ z1 * CL := by
    exact mul_le_mul_of_nonpos_right hz1le hCL0
  have hz1cos : z1 * CL ≤ z1 * (Real.cos d - 1) := by
    exact mul_le_mul_of_nonneg_left hcosm1 hz1nonneg
  have hz2sin : z2 * SU ≤ z2 * Real.sin d := by
    exact mul_le_mul_of_nonpos_left hsinSU hz2hi
  have hz2SU : (-227 / 500 : ℝ) * SU ≤ z2 * SU := by
    exact mul_le_mul_of_nonneg_right hz2lo hSU0
  have hcD : (273 / 500 : ℝ) * d ≤ c * d := by
    exact mul_le_mul_of_nonneg_right hclo hd0
  let Q : ℝ :=
    (23 / 250 : ℝ) - (41 / 200) * d + (227 / 3000) * d ^ 2 +
      (91 / 2400) * d ^ 3 - (227 / 60000) * d ^ 4 -
      (91 / 72000) * d ^ 5
  let R : ℝ :=
    (14560000 * d ^ 4 + 53048000 * d ^ 3 - 402318800 * d ^ 2 -
      1133187220 * d + 1625028307 : ℝ) / 11520000000
  have hd2A : d ^ 2 ≤ (13 / 20 : ℝ) ^ 2 := by nlinarith
  have hR : 0 ≤ R := by
    dsimp [R]
    have h3 : 0 ≤ d ^ 3 := by positivity
    have h4 : 0 ≤ d ^ 4 := by positivity
    nlinarith only [hdA, hd2A, h3, h4]
  have hQend : 0 < (71432009 / 230400000000 : ℝ) := by norm_num
  have hQfactor :
      Q - (71432009 / 230400000000 : ℝ) = ((13 / 20 : ℝ) - d) * R := by
    dsimp [Q, R]
    ring
  have hQ : 0 ≤ Q := by
    have hprod : 0 ≤ ((13 / 20 : ℝ) - d) * R :=
      mul_nonneg (sub_nonneg.mpr hdA) hR
    linarith only [hprod, hQfactor, hQend]
  have hL :
      0 ≤ (91 / 100 : ℝ) * CL + (-227 / 500 : ℝ) * SU +
        (273 / 500 : ℝ) * d + d * d / 4 := by
    have hid :
        (91 / 100 : ℝ) * CL + (-227 / 500 : ℝ) * SU +
            (273 / 500 : ℝ) * d + d * d / 4 = d * Q := by
      dsimp [CL, SU, Q]
      ring
    rw [hid]
    exact mul_nonneg hd0 hQ
  have hformula' :
      Stage2.UValue params.phi t =
        z1 * (Real.cos d - 1) + z2 * Real.sin d + c * d + d * d / 4 := by
    simpa [d, z1, z2, c] using phase2_U_phi_formula hphiT ht.2
  rw [hformula']
  linarith only [hL, hz1CL, hz1cos, hz2sin, hz2SU, hcD]

private theorem pathPrime1_eq_rot (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime1 p t = Romik.rot t (Romik.alphaBeta1 p t) := rfl

private theorem matchPrime12 :
    Romik.pathPrime1 params params.phi = Romik.pathPrime2 params params.phi := by
  have h10 := congrFun params_equations (10 : Fin 22)
  have h11 := congrFun params_equations (11 : Fin 22)
  simp [Romik.system] at h10 h11
  apply Prod.ext <;> linarith

private theorem matchAB12 :
    Romik.alphaBeta1 params params.phi = Romik.alphaBeta2 params params.phi := by
  apply rot_injective params.phi
  simpa [pathPrime1_eq_rot, pathPrime2_eq_rot] using matchPrime12

private theorem ab4_reflect_ab2 (t : ℝ) :
    Romik.alphaBeta4 params (T - t) = reflAB (Romik.alphaBeta2 params t) := by
  dsimp [T, reflAB, Romik.alphaBeta4, Romik.alphaBeta2]
  rw [Romik.d1_eq_quarterPi_sub_b1_of_equations params_equations,
      Romik.d2_eq_b2_add_quarterPi_correction_of_equations params_equations]
  ring_nf

private theorem ab5_reflect_ab1 (t : ℝ) :
    Romik.alphaBeta5 params (T - t) = reflAB (Romik.alphaBeta1 params t) := by
  dsimp [T, reflAB, Romik.alphaBeta5, Romik.alphaBeta1]
  rw [Romik.e1_eq_a1_of_equations params_equations,
      Romik.e2_eq_neg_a2_of_equations params_equations]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring_nf

private theorem matchAB34 :
    Romik.alphaBeta3 params eta = Romik.alphaBeta4 params eta := by
  have h3 := ab3_reflect params.theta
  have h4 := ab4_reflect_ab2 params.theta
  have hm := congrArg reflAB matchAB23
  simpa [eta] using h3.trans (hm.symm.trans h4.symm)

private theorem matchAB45 :
    Romik.alphaBeta4 params tau = Romik.alphaBeta5 params tau := by
  have h4 := ab4_reflect_ab2 params.phi
  have h5 := ab5_reflect_ab1 params.phi
  have hm := congrArg reflAB matchAB12
  simpa [tau] using h4.trans (hm.symm.trans h5.symm)

private def phaseB3 (t : ℝ) : Point :=
  Romik.path3 params t + (Romik.alphaBeta3 params t).1 • v t
private def phaseB4_m71dda23 (t : ℝ) : Point :=
  Romik.path4 params t + (Romik.alphaBeta4 params t).1 • v t
private def phaseB5_m71dda23 (t : ℝ) : Point :=
  Romik.path5 params t + (Romik.alphaBeta5 params t).1 • v t

private theorem u_hasDerivAt_local (t : ℝ) : HasDerivAt u (v t) t :=
  Stage2.u_hasDerivAt t

private theorem phaseB3_eq_A3_sub_u (t : ℝ) :
    phaseB3 t = Stage2.phaseA3 t - u t := by
  apply Prod.ext <;> simp [phaseB3, Stage2.phaseA3]

private theorem phaseB4_eq_A4_sub_u (t : ℝ) :
    phaseB4_m71dda23 t = Stage2.phaseA4 t - u t := by
  apply Prod.ext <;> simp [phaseB4_m71dda23, Stage2.phaseA4]

private theorem phaseB5_eq_A5_sub_u (t : ℝ) :
    phaseB5_m71dda23 t = Stage2.phaseA5 t - u t := by
  apply Prod.ext <;> simp [phaseB5_m71dda23, Stage2.phaseA5]

private theorem B_eq_phaseB3 {t : ℝ} (ht : t ∈ Icc params.theta eta) :
    B t = phaseB3 t := by
  by_cases h : t = params.theta
  · subst t
    rw [B, path_at_theta]
    have ha : alpha params.theta = (Romik.alphaBeta2 params params.theta).1 := by
      simp only [alpha, alphaBetaAt, ite_eq_right (not_le.mpr phi_lt_theta),
        ite_eq_left (le_refl params.theta)]
    rw [ha]
    have hm := PartB.match23
    rw [hm, matchAB23]
    apply Prod.ext <;> simp [phaseB3, v]
  · have htheta : params.theta < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have hphi : params.phi < t := lt_trans phi_lt_theta htheta
    have hetaRaw : t ≤ Real.pi / 2 - params.theta := by
      simpa [eta, T] using ht.2
    apply Prod.ext <;> simp [B, alpha, alphaBetaAt, Romik.path, phaseB3,
      not_le.mpr hphi, not_le.mpr htheta, hetaRaw, eta, T]

private theorem B_eq_phaseB4 {t : ℝ} (ht : t ∈ Icc eta tau) :
    B t = phaseB4_m71dda23 t := by
  by_cases h : t = eta
  · subst t
    have hB3 := B_eq_phaseB3 (t := eta) ⟨theta_lt_eta.le, le_rfl⟩
    have hm : Romik.path3 params eta = Romik.path4 params eta := by
      simpa [eta, T] using PartB.match34
    calc
      B eta = phaseB3 eta := hB3
      _ = phaseB4_m71dda23 eta := by
        unfold phaseB3 phaseB4_m71dda23
        rw [hm, matchAB34]
  · have hetaT : eta < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have htheta : params.theta < t := lt_trans theta_lt_eta hetaT
    have hphi : params.phi < t := lt_trans phi_lt_theta htheta
    have hetaRaw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using hetaT
    have htauRaw : t ≤ Real.pi / 2 - params.phi := by
      simpa [tau, T] using ht.2
    apply Prod.ext <;> simp [B, alpha, alphaBetaAt, Romik.path, phaseB4_m71dda23,
      not_le.mpr hphi, not_le.mpr htheta, not_le.mpr hetaRaw, htauRaw,
      eta, tau, T]

private theorem B_eq_phaseB5 {t : ℝ} (ht : t ∈ Icc tau T) :
    B t = phaseB5_m71dda23 t := by
  by_cases h : t = tau
  · subst t
    have hB4 := B_eq_phaseB4 (t := tau) ⟨eta_lt_tau.le, le_rfl⟩
    have hm : Romik.path4 params tau = Romik.path5 params tau := by
      simpa [tau, T] using PartB.match45
    calc
      B tau = phaseB4_m71dda23 tau := hB4
      _ = phaseB5_m71dda23 tau := by
        unfold phaseB4_m71dda23 phaseB5_m71dda23
        rw [hm, matchAB45]
  · have htauT : tau < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have hetaT : eta < t := lt_trans eta_lt_tau htauT
    have htheta : params.theta < t := lt_trans theta_lt_eta hetaT
    have hphi : params.phi < t := lt_trans phi_lt_theta htheta
    have hetaRaw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using hetaT
    have htauRaw : Real.pi / 2 - params.phi < t := by
      simpa [tau, T] using htauT
    apply Prod.ext <;> simp [B, alpha, alphaBetaAt, Romik.path, phaseB5_m71dda23,
      not_le.mpr hphi, not_le.mpr htheta, not_le.mpr hetaRaw,
      not_le.mpr htauRaw, eta, tau, T]

private theorem c1_le_theta : params.c1 ≤ params.theta := by
  have hc := PartB.c1_contains.2
  have ht := theta_bounds.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at hc ht ⊢
  linarith

private theorem eta_lower_four_fifths : (4 / 5 : ℝ) ≤ eta := by
  dsimp [eta, T]
  nlinarith [Real.pi_gt_three, theta_upper_crude]

private theorem d1_upper_33_25 : params.d1 ≤ (33 / 25 : ℝ) := by
  have hd := PartB.d1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at hd ⊢
  linarith

private theorem phaseB3_coeff_nonpos {q : ℝ} (hq : params.theta ≤ q) :
    params.c1 - q ≤ 0 := by linarith [c1_le_theta]

private theorem phaseB4_coeff_nonpos {q : ℝ} (hq : eta ≤ q) :
    params.d1 - q / 2 - 1 ≤ 0 := by
  nlinarith [d1_upper_33_25, eta_lower_four_fifths]

private theorem dot_hasDerivAt_fixed_local {f : ℝ → Point} {df : Point} {t : ℝ}
    (h : HasDerivAt f df t) (w : Point) :
    HasDerivAt (fun s => dot (f s) w) (dot df w) t := by
  have h1 := HasDerivAt.const_mul w.1 h.fst
  have h2 := HasDerivAt.const_mul w.2 h.snd
  have hs := h1.fun_add h2
  simpa [dot, mul_comm] using hs

private theorem phaseB3_dot_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun q => dot (phaseB3 q) (u s))
      (dot ((params.c1 - t) • v t) (u s)) t := by
  have h := (Stage2.A3_hasDerivAt_public t).fun_sub (u_hasDerivAt_local t)
  have hd : ((1 + params.c1 - t) • v t) - v t =
      (params.c1 - t) • v t := by
    apply Prod.ext <;> simp [v] <;> ring
  rw [hd] at h
  have hdot := dot_hasDerivAt_fixed_local h (u s)
  simpa only [phaseB3_eq_A3_sub_u] using hdot

private theorem phaseB4_dot_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun q => dot (phaseB4_m71dda23 q) (u s))
      (dot ((params.d1 - t / 2 - 1) • v t) (u s)) t := by
  have h := (Stage2.A4_hasDerivAt_public t).fun_sub (u_hasDerivAt_local t)
  have hd : ((params.d1 - t / 2) • v t) - v t =
      (params.d1 - t / 2 - 1) • v t := by
    apply Prod.ext <;> simp [v] <;> ring
  rw [hd] at h
  have hdot := dot_hasDerivAt_fixed_local h (u s)
  simpa only [phaseB4_eq_A4_sub_u] using hdot

private theorem phaseB5_dot_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun q => dot (phaseB5_m71dda23 q) (u s))
      (dot ((-(1 / 2 : ℝ)) • v t) (u s)) t := by
  have h := (Stage2.A5_hasDerivAt_public t).fun_sub (u_hasDerivAt_local t)
  have hd : ((1 / 2 : ℝ) • v t) - v t = (-(1 / 2 : ℝ)) • v t := by
    apply Prod.ext <;> simp [v] <;> ring
  rw [hd] at h
  have hdot := dot_hasDerivAt_fixed_local h (u s)
  simpa only [phaseB5_eq_A5_sub_u] using hdot

private theorem phaseB_mono_left
    {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ q,
      HasDerivAt (fun x => dot (F x) (u s))
        (dot ((r q) • v q) (u s)) q)
    (hr : ∀ q ∈ Ioo a b, r q ≤ 0)
    (hs0 : 0 ≤ s) (hsa : s ≤ a) (hbT : b ≤ T) :
    MonotoneOn (fun q => dot (F q) (u s)) (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun q => dot ((r q) • v q) (u s)) (convex_Icc a b) ?_ ?_ ?_
  · intro q hq
    exact (hder q).continuousAt.continuousWithinAt
  · intro q hq
    exact (hder q).hasDerivWithinAt
  · intro q hq
    have hi : q ∈ Ioo a b := by simpa only [interior_Icc] using hq
    have hsin : Real.sin (s - q) ≤ 0 := by
      have hnon : s - q ≤ 0 := by linarith [hsa, hi.1]
      have hnegpi : -Real.pi ≤ s - q := by
        have hqT : q ≤ T := le_trans (le_of_lt hi.2) hbT
        have hqs : q - s ≤ T := by linarith
        nlinarith [T_le_pi]
      exact Real.sin_nonpos_of_nonpos_of_neg_pi_le hnon hnegpi
    have heq : dot ((r q) • v q) (u s) = r q * Real.sin (s - q) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonneg_of_nonpos_of_nonpos (hr q hi) hsin

private theorem phaseB_anti_right
    {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ q,
      HasDerivAt (fun x => dot (F x) (u s))
        (dot ((r q) • v q) (u s)) q)
    (hr : ∀ q ∈ Ioo a b, r q ≤ 0)
    (ha0 : 0 ≤ a) (hbs : b ≤ s) (hsT : s ≤ T) :
    AntitoneOn (fun q => dot (F q) (u s)) (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun q => dot ((r q) • v q) (u s)) (convex_Icc a b) ?_ ?_ ?_
  · intro q hq
    exact (hder q).continuousAt.continuousWithinAt
  · intro q hq
    exact (hder q).hasDerivWithinAt
  · intro q hq
    have hi : q ∈ Ioo a b := by simpa only [interior_Icc] using hq
    have hq0 : 0 ≤ q := le_trans ha0 (le_of_lt hi.1)
    have hdelta0 : 0 ≤ s - q := by linarith [hi.2, hbs]
    have hdeltaPi : s - q ≤ Real.pi := by
      have : s - q ≤ T := by linarith [hsT, hq0]
      exact le_trans this T_le_pi
    have hsin : 0 ≤ Real.sin (s - q) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hdelta0 hdeltaPi
    have heq : dot ((r q) • v q) (u s) = r q * Real.sin (s - q) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonpos_of_nonpos_of_nonneg (hr q hi) hsin

private theorem criticalU_eq_Bdiff (t : ℝ) :
    Stage2.UValue params.phi t = dot (B eta - B t) (u t) := by
  unfold Stage2.UValue
  rw [← B_eta_eq_path_phi]
  have hinner := B_inner_u_identity t
  unfold dot at hinner ⊢
  dsimp at hinner ⊢
  linarith

private theorem phase3_U_phi_nonneg {t : ℝ}
    (ht : t ∈ Icc params.theta eta) :
    0 ≤ Stage2.UValue params.phi t := by
  have hm := phaseB_mono_left (F := phaseB3)
    (r := fun q => params.c1 - q) (a := t) (b := eta) (s := t)
    (phaseB3_dot_hasDerivAt t)
    (by intro q hq; exact phaseB3_coeff_nonpos (le_trans ht.1 (le_of_lt hq.1)))
    (le_trans theta_pos.le ht.1) (le_rfl) eta_lt_T.le
  have hcomp := hm ⟨le_rfl, ht.2⟩ ⟨ht.2, le_rfl⟩ ht.2
  have hBt := B_eq_phaseB3 ht
  have hBe := B_eq_phaseB3 (t := eta) ⟨theta_lt_eta.le, le_rfl⟩
  rw [criticalU_eq_Bdiff, hBt, hBe]
  unfold dot at hcomp ⊢
  dsimp at hcomp ⊢
  linarith

private theorem phase4_U_phi_nonneg {t : ℝ}
    (ht : t ∈ Icc eta tau) :
    0 ≤ Stage2.UValue params.phi t := by
  have hm := phaseB_anti_right (F := phaseB4_m71dda23)
    (r := fun q => params.d1 - q / 2 - 1) (a := eta) (b := t) (s := t)
    (phaseB4_dot_hasDerivAt t)
    (by intro q hq; exact phaseB4_coeff_nonpos (le_of_lt hq.1))
    (le_trans theta_pos.le theta_lt_eta.le) (le_rfl) (le_trans ht.2 tau_lt_T.le)
  have hcomp := hm ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
  have hBt := B_eq_phaseB4 ht
  have hBe := B_eq_phaseB4 (t := eta) ⟨le_rfl, eta_lt_tau.le⟩
  rw [criticalU_eq_Bdiff, hBt, hBe]
  unfold dot at hcomp ⊢
  dsimp at hcomp ⊢
  linarith

private theorem phase5_U_phi_nonneg {t : ℝ}
    (ht : t ∈ Icc tau T) :
    0 ≤ Stage2.UValue params.phi t := by
  have hm4 := phaseB_anti_right (F := phaseB4_m71dda23)
    (r := fun q => params.d1 - q / 2 - 1) (a := eta) (b := tau) (s := t)
    (phaseB4_dot_hasDerivAt t)
    (by intro q hq; exact phaseB4_coeff_nonpos (le_of_lt hq.1))
    (le_trans theta_pos.le theta_lt_eta.le) ht.1 ht.2
  have h4 := hm4 ⟨le_rfl, eta_lt_tau.le⟩ ⟨eta_lt_tau.le, le_rfl⟩ eta_lt_tau.le
  have hm5 := phaseB_anti_right (F := phaseB5_m71dda23)
    (r := fun _ => (-(1 / 2 : ℝ))) (a := tau) (b := t) (s := t)
    (phaseB5_dot_hasDerivAt t)
    (by intro q hq; norm_num)
    (le_trans theta_pos.le (lt_trans theta_lt_eta eta_lt_tau).le) (le_rfl) ht.2
  have h5 := hm5 ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
  have hBetaEta := B_eq_phaseB4 (t := eta) ⟨le_rfl, eta_lt_tau.le⟩
  have hBetaTau4 := B_eq_phaseB4 (t := tau) ⟨eta_lt_tau.le, le_rfl⟩
  have hBetaTau5 := B_eq_phaseB5 (t := tau) ⟨le_rfl, tau_lt_T.le⟩
  have hBetaT := B_eq_phaseB5 ht
  rw [criticalU_eq_Bdiff, hBetaEta, hBetaT]
  have hmatch : phaseB4_m71dda23 tau = phaseB5_m71dda23 tau := by
    rw [← hBetaTau4, ← hBetaTau5]
  change dot (phaseB4_m71dda23 tau) (u t) ≤ dot (phaseB4_m71dda23 eta) (u t) at h4
  rw [hmatch] at h4
  unfold dot at h4 h5 ⊢
  dsimp at h4 h5 ⊢
  linarith

/-- Fixed-endpoint separation required by the direct no-hidden-crossing proof. -/
theorem U_phi_nonneg {t : ℝ} (ht : t ∈ Icc params.phi T) :
    0 ≤ Stage2.UValue params.phi t := by
  by_cases h2 : t ≤ params.theta
  · exact phase2_U_phi_nonneg ⟨ht.1, h2⟩
  have htheta : params.theta < t := lt_of_not_ge h2
  by_cases h3 : t ≤ eta
  · exact phase3_U_phi_nonneg ⟨htheta.le, h3⟩
  have hetaT : eta < t := lt_of_not_ge h3
  by_cases h4 : t ≤ tau
  · exact phase4_U_phi_nonneg ⟨hetaT.le, h4⟩
  · exact phase5_U_phi_nonneg ⟨(lt_of_not_ge h4).le, ht.2⟩

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part C / Stage4 / No Hidden Match Facts
-/

public section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

noncomputable section

/-- Reflection on the `(alpha,beta)` coefficient plane induced by `t ↦ T-t`. -/
def noHiddenReflAB (z : Point) : Point := (-z.2, -z.1)

private theorem rot_dot_u_noHidden (t : ℝ) (z : Point) :
    dot (Romik.rot t z) (u t) = z.1 :=
  Stage3.rot_dot_u t z

private theorem rot_dot_v_noHidden (t : ℝ) (z : Point) :
    dot (Romik.rot t z) (v t) = z.2 :=
  Stage3.rot_dot_v t z

private theorem rot_injective_noHidden (t : ℝ) {z w : Point}
    (h : Romik.rot t z = Romik.rot t w) : z = w :=
  Stage3.rot_injective t h

private theorem matchPrime12_noHidden :
    Romik.pathPrime1 params params.phi = Romik.pathPrime2 params params.phi := by
  have h10 := congrFun params_equations (10 : Fin 22)
  have h11 := congrFun params_equations (11 : Fin 22)
  simp [Romik.system] at h10 h11
  exact Prod.ext (by linarith) (by linarith)

private theorem matchPrime23_noHidden :
    Romik.pathPrime2 params params.theta = Romik.pathPrime3 params params.theta := by
  have h14 := congrFun params_equations (14 : Fin 22)
  have h15 := congrFun params_equations (15 : Fin 22)
  simp [Romik.system] at h14 h15
  exact Prod.ext (by linarith) (by linarith)

private theorem pathPrime1_eq_rot_noHidden (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime1 p t = Romik.rot t (Romik.alphaBeta1 p t) := rfl

private theorem pathPrime2_eq_rot_noHidden (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime2 p t = Romik.rot t (Romik.alphaBeta2 p t) := rfl

private theorem pathPrime3_eq_rot_noHidden (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime3 p t = Romik.rot t (Romik.alphaBeta3 p t) := rfl

/-- Exact matching of the coefficient pair at the first switch. -/
theorem alphaBeta_match12_direct :
    Romik.alphaBeta1 params params.phi = Romik.alphaBeta2 params params.phi := by
  apply rot_injective_noHidden params.phi
  simpa [pathPrime1_eq_rot_noHidden, pathPrime2_eq_rot_noHidden] using matchPrime12_noHidden

/-- Exact matching of the coefficient pair at the second switch. -/
theorem alphaBeta_match23_direct :
    Romik.alphaBeta2 params params.theta = Romik.alphaBeta3 params params.theta := by
  apply rot_injective_noHidden params.theta
  simpa [pathPrime2_eq_rot_noHidden, pathPrime3_eq_rot_noHidden] using matchPrime23_noHidden

/-- Phase four is the reflected phase two coefficient pair. -/
theorem alphaBeta4_reflect2_direct (s : ℝ) :
    Romik.alphaBeta4 params (T - s) = noHiddenReflAB (Romik.alphaBeta2 params s) := by
  dsimp [T, noHiddenReflAB, Romik.alphaBeta4, Romik.alphaBeta2]
  rw [Romik.d1_eq_quarterPi_sub_b1_of_equations params_equations,
      Romik.d2_eq_b2_add_quarterPi_correction_of_equations params_equations]
  ring_nf

/-- Phase three has the same coefficient reflection symmetry. -/
theorem alphaBeta3_reflect_direct (s : ℝ) :
    Romik.alphaBeta3 params (T - s) = noHiddenReflAB (Romik.alphaBeta3 params s) := by
  dsimp [T, noHiddenReflAB, Romik.alphaBeta3]
  rw [Romik.c2_eq_c1_sub_halfPi_of_equations params_equations]
  ring_nf

/-- Phase five is the reflected phase one coefficient pair. -/
theorem alphaBeta5_reflect1_direct (s : ℝ) :
    Romik.alphaBeta5 params (T - s) = noHiddenReflAB (Romik.alphaBeta1 params s) := by
  dsimp [T, noHiddenReflAB, Romik.alphaBeta5, Romik.alphaBeta1]
  rw [Romik.e1_eq_a1_of_equations params_equations,
      Romik.e2_eq_neg_a2_of_equations params_equations]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring_nf

/-- Exact matching of the coefficient pair at the third switch. -/
theorem alphaBeta_match34_direct :
    Romik.alphaBeta3 params eta = Romik.alphaBeta4 params eta := by
  have h3 := alphaBeta3_reflect_direct params.theta
  have h4 := alphaBeta4_reflect2_direct params.theta
  have hm := congrArg noHiddenReflAB alphaBeta_match23_direct
  simpa [eta] using h3.trans (hm.symm.trans h4.symm)

/-- Exact matching of the coefficient pair at the fourth switch. -/
theorem alphaBeta_match45_direct :
    Romik.alphaBeta4 params tau = Romik.alphaBeta5 params tau := by
  have h4 := alphaBeta4_reflect2_direct params.phi
  have h5 := alphaBeta5_reflect1_direct params.phi
  have hm := congrArg noHiddenReflAB alphaBeta_match12_direct
  simpa [tau] using h4.trans (hm.symm.trans h5.symm)

end

end Stage4
end PartC
end GerverSofa

end

end

section

/-!
# Part C Stage 4: continuity of the matched velocity coefficients

This file turns the five exact coefficient matching statements into a public
continuity interface for `alphaBetaAt`, `alpha`, `beta`, `B`, and `D`.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

private theorem alphaBeta1_continuous :
    Continuous (Romik.alphaBeta1 params) := by
  unfold Romik.alphaBeta1
  fun_prop

private theorem alphaBeta2_continuous :
    Continuous (Romik.alphaBeta2 params) := by
  unfold Romik.alphaBeta2
  fun_prop

private theorem alphaBeta3_continuous :
    Continuous (Romik.alphaBeta3 params) := by
  unfold Romik.alphaBeta3
  fun_prop

private theorem alphaBeta4_continuous :
    Continuous (Romik.alphaBeta4 params) := by
  unfold Romik.alphaBeta4
  fun_prop

private theorem alphaBeta5_continuous :
    Continuous (Romik.alphaBeta5 params) := by
  unfold Romik.alphaBeta5
  fun_prop

/-- The literal nested-if velocity coefficient is continuous across all four
switches. -/
theorem alphaBetaAt_continuous : Continuous alphaBetaAt := by
  have h45 : Continuous
      (fun t : ℝ =>
        if t ≤ tau then Romik.alphaBeta4 params t
        else Romik.alphaBeta5 params t) := by
    exact alphaBeta4_continuous.if_le alphaBeta5_continuous
      continuous_id continuous_const (by
        intro t ht
        subst t
        exact alphaBeta_match45_direct)
  have h345 : Continuous
      (fun t : ℝ =>
        if t ≤ eta then Romik.alphaBeta3 params t
        else if t ≤ tau then Romik.alphaBeta4 params t
        else Romik.alphaBeta5 params t) := by
    exact alphaBeta3_continuous.if_le h45
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [ite_eq_left eta_lt_tau.le]
        exact alphaBeta_match34_direct)
  have h2345 : Continuous
      (fun t : ℝ =>
        if t ≤ params.theta then Romik.alphaBeta2 params t
        else if t ≤ eta then Romik.alphaBeta3 params t
        else if t ≤ tau then Romik.alphaBeta4 params t
        else Romik.alphaBeta5 params t) := by
    exact alphaBeta2_continuous.if_le h345
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [ite_eq_left theta_lt_eta.le]
        exact alphaBeta_match23_direct)
  have h12345 : Continuous
      (fun t : ℝ =>
        if t ≤ params.phi then Romik.alphaBeta1 params t
        else if t ≤ params.theta then Romik.alphaBeta2 params t
        else if t ≤ eta then Romik.alphaBeta3 params t
        else if t ≤ tau then Romik.alphaBeta4 params t
        else Romik.alphaBeta5 params t) := by
    exact alphaBeta1_continuous.if_le h2345
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [ite_eq_left phi_lt_theta.le]
        exact alphaBeta_match12_direct)
  unfold alphaBetaAt
  exact h12345

theorem alpha_continuous : Continuous alpha := by
  unfold alpha
  exact continuous_fst.comp alphaBetaAt_continuous

theorem beta_continuous : Continuous beta := by
  unfold beta
  exact continuous_snd.comp alphaBetaAt_continuous

private theorem u_continuous : Continuous u := by
  unfold u
  fun_prop

private theorem v_continuous : Continuous v := by
  unfold v
  fun_prop

/-- Public continuity of the early reflected contact curve. -/
theorem D_continuous : Continuous D := by
  have hx := pathContinuous
  have hfirst := (continuous_fst.comp hx).sub
    (beta_continuous.mul (continuous_fst.comp u_continuous))
  have hsecond := (continuous_snd.comp hx).sub
    (beta_continuous.mul (continuous_snd.comp u_continuous))
  change Continuous (fun t : ℝ =>
    ((Romik.path params t).1 - beta t * (u t).1,
     (Romik.path params t).2 - beta t * (u t).2))
  exact hfirst.prodMk hsecond

/-- Public continuity of the late reflected contact curve. -/
theorem B_continuous : Continuous B := by
  have hx := pathContinuous
  have hfirst := (continuous_fst.comp hx).add
    (alpha_continuous.mul (continuous_fst.comp v_continuous))
  have hsecond := (continuous_snd.comp hx).add
    (alpha_continuous.mul (continuous_snd.comp v_continuous))
  change Continuous (fun t : ℝ =>
    ((Romik.path params t).1 + alpha t * (v t).1,
     (Romik.path params t).2 + alpha t * (v t).2))
  exact hfirst.prodMk hsecond

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part C / Stage4 / No Hidden Sign Facts
-/

public section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

noncomputable section

private theorem phi_upper_twentieth : params.phi ≤ (1 / 20 : ℝ) := by
  have h := phi_bounds.2
  norm_num at h ⊢
  linarith

private theorem a1_lower_six_fifths : (6 / 5 : ℝ) ≤ params.a1 := by
  have h := Romik.a1_lower_bound_of_mem_box params_mem
  norm_num at h ⊢
  linarith

private theorem b1_upper_neg_half : params.b1 ≤ (-1 / 2 : ℝ) := by
  have h := PartB.b1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem d1_lower_thirteen_tenths : (13 / 10 : ℝ) ≤ params.d1 := by
  have h := PartB.d1_contains.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem T_lt_eight_fifths : T < (8 / 5 : ℝ) := by
  have hp := ExactReplay.piI_contains_pi
  have hhi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) := hp.2
  have h32 : (ExactReplay.piI.hi : ℝ) < (16 / 5 : ℝ) := by
    norm_num [ExactReplay.piI, ExactReplay.q]
  dsimp [T]
  linarith

private theorem alphaBeta1_fst_nonpos_small {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    (Romik.alphaBeta1 params s).1 ≤ 0 := by
  have hpi : s ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hsinLower := Real.sin_ge_sub_cube hs0
  have hcosLower : 1 - s ^ 2 / 2 ≤ Real.cos s :=
    Real.one_sub_sq_div_two_le_cos
  have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) :=
    mul_nonneg hs0 (sub_nonneg.mpr hs20)
  have hcube : 0 ≤ s ^ 2 * ((1 / 20 : ℝ) - s) :=
    mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs20)
  have hcoef : (12 / 5 : ℝ) ≤ 2 * params.a1 := by
    nlinarith [a1_lower_six_fifths]
  have hmul : (12 / 5 : ℝ) * Real.sin s ≤ 2 * params.a1 * Real.sin s :=
    mul_le_mul_of_nonneg_right hcoef hsin0
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith [hsinLower, hcosLower, hquad, hcube, hmul]

private theorem alphaBeta1_snd_nonneg_small {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    0 ≤ (Romik.alphaBeta1 params s).2 := by
  have hpi : s ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hsinUpper := Real.sin_le hs0
  have hcosLower : 1 - s ^ 2 / 2 ≤ Real.cos s :=
    Real.one_sub_sq_div_two_le_cos
  have hcos0 : 0 ≤ Real.cos s := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_gt_three]
  have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) :=
    mul_nonneg hs0 (sub_nonneg.mpr hs20)
  have hcoef : (12 / 5 : ℝ) ≤ 2 * params.a1 := by
    nlinarith [a1_lower_six_fifths]
  have hmul : (12 / 5 : ℝ) * Real.cos s ≤ 2 * params.a1 * Real.cos s :=
    mul_le_mul_of_nonneg_right hcoef hcos0
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith [hsinUpper, hcosLower, hquad, hmul]

private theorem alphaBeta5_fst_nonpos_tail {t : ℝ}
    (ht : t ∈ Icc tau T) :
    (Romik.alphaBeta5 params t).1 ≤ 0 := by
  let s : ℝ := T - t
  have hs0 : 0 ≤ s := by
    dsimp [s]
    linarith [ht.2]
  have hsphi : s ≤ params.phi := by
    have hTtau : T - tau = params.phi := by
      dsimp [tau]
      ring
    dsimp [s]
    rw [← hTtau]
    linarith [ht.1]
  have hs20 : s ≤ (1 / 20 : ℝ) := le_trans hsphi phi_upper_twentieth
  have hb := alphaBeta1_snd_nonneg_small hs0 hs20
  have href := congrArg Prod.fst (alphaBeta5_reflect1_direct s)
  have hTs : T - s = t := by
    dsimp [s]
    ring
  rw [hTs] at href
  have heq : (Romik.alphaBeta5 params t).1 = -(Romik.alphaBeta1 params s).2 := by
    simpa [noHiddenReflAB] using href
  rw [heq]
  exact neg_nonpos.mpr hb

private theorem alphaBeta5_snd_nonneg_tail {t : ℝ}
    (ht : t ∈ Icc tau T) :
    0 ≤ (Romik.alphaBeta5 params t).2 := by
  let s : ℝ := T - t
  have hs0 : 0 ≤ s := by
    dsimp [s]
    linarith [ht.2]
  have hsphi : s ≤ params.phi := by
    have hTtau : T - tau = params.phi := by
      dsimp [tau]
      ring
    dsimp [s]
    rw [← hTtau]
    linarith [ht.1]
  have hs20 : s ≤ (1 / 20 : ℝ) := le_trans hsphi phi_upper_twentieth
  have ha := alphaBeta1_fst_nonpos_small hs0 hs20
  have href := congrArg Prod.snd (alphaBeta5_reflect1_direct s)
  have hTs : T - s = t := by
    dsimp [s]
    ring
  rw [hTs] at href
  have heq : (Romik.alphaBeta5 params t).2 = -(Romik.alphaBeta1 params s).1 := by
    simpa [noHiddenReflAB] using href
  rw [heq]
  exact neg_nonneg.mpr ha

/-- The `u_t` coefficient of the Gerver velocity is nonpositive on the
entire no-hidden `U` domain. -/
theorem alpha_nonpos {t : ℝ} (ht : t ∈ Icc params.phi T) :
    alpha t ≤ 0 := by
  have htPhysical : t ∈ Icc (0 : ℝ) T :=
    ⟨le_trans phi_nonneg ht.1, ht.2⟩
  by_cases hphi : t ≤ params.phi
  · have heq : t = params.phi := le_antisymm hphi ht.1
    subst t
    have h := alphaBeta1_fst_nonpos_small phi_nonneg phi_upper_twentieth
    simpa [alpha, alphaBetaAt] using h
  · by_cases htheta : t ≤ params.theta
    · simp only [alpha, alphaBetaAt, ite_eq_right hphi, ite_eq_left htheta]
      dsimp [Romik.alphaBeta2]
      have ht0 : 0 ≤ t := le_trans phi_nonneg ht.1
      have hb : 1 + 2 * params.b1 ≤ 0 := by
        nlinarith [b1_upper_neg_half]
      nlinarith
    · by_cases heta : t ≤ eta
      · have hrho := Stage2.rhoC_nonneg htPhysical
        unfold Stage2.rhoC at hrho
        rw [ite_eq_right hphi, ite_eq_right htheta, ite_eq_left heta] at hrho
        simp only [alpha, alphaBetaAt, ite_eq_right hphi, ite_eq_right htheta, ite_eq_left heta]
        dsimp [Romik.alphaBeta3]
        nlinarith
      · by_cases htau : t ≤ tau
        · have hrho := Stage2.rhoC_nonneg htPhysical
          unfold Stage2.rhoC at hrho
          rw [ite_eq_right hphi, ite_eq_right htheta, ite_eq_right heta, ite_eq_left htau] at hrho
          simp only [alpha, alphaBetaAt, ite_eq_right hphi, ite_eq_right htheta, ite_eq_right
            heta, ite_eq_left htau]
          dsimp [Romik.alphaBeta4]
          nlinarith
        · have ht5 : t ∈ Icc tau T := ⟨le_of_lt (lt_of_not_ge htau), ht.2⟩
          have h5 := alphaBeta5_fst_nonpos_tail ht5
          simpa [alpha, alphaBetaAt, hphi, htheta, heta, htau] using h5

/-- The `v_t` coefficient of the Gerver velocity is nonnegative on the
entire no-hidden `U` domain. -/
theorem beta_nonneg {t : ℝ} (ht : t ∈ Icc params.phi T) :
    0 ≤ beta t := by
  have htPhysical : t ∈ Icc (0 : ℝ) T :=
    ⟨le_trans phi_nonneg ht.1, ht.2⟩
  by_cases hphi : t ≤ params.phi
  · have heq : t = params.phi := le_antisymm hphi ht.1
    subst t
    have h := alphaBeta1_snd_nonneg_small phi_nonneg phi_upper_twentieth
    simpa [beta, alphaBetaAt] using h
  · by_cases htheta : t ≤ params.theta
    · have hrho := Stage2.rhoA_nonneg htPhysical
      unfold Stage2.rhoA at hrho
      rw [ite_eq_right hphi, ite_eq_left htheta] at hrho
      simp only [beta, alphaBetaAt, ite_eq_right hphi, ite_eq_left htheta]
      dsimp [Romik.alphaBeta2]
      exact hrho
    · by_cases heta : t ≤ eta
      · have hrho := Stage2.rhoA_nonneg htPhysical
        unfold Stage2.rhoA at hrho
        rw [ite_eq_right hphi, ite_eq_right htheta, ite_eq_left heta] at hrho
        simp only [beta, alphaBetaAt, ite_eq_right hphi, ite_eq_right htheta, ite_eq_left heta]
        dsimp [Romik.alphaBeta3]
        exact hrho
      · by_cases htau : t ≤ tau
        · simp only [beta, alphaBetaAt, ite_eq_right hphi, ite_eq_right htheta, ite_eq_right heta,
          ite_eq_left htau]
          dsimp [Romik.alphaBeta4]
          nlinarith [d1_lower_thirteen_tenths, T_lt_eight_fifths, ht.2]
        · have ht5 : t ∈ Icc tau T := ⟨le_of_lt (lt_of_not_ge htau), ht.2⟩
          have h5 := alphaBeta5_snd_nonneg_tail ht5
          simpa [beta, alphaBetaAt, hphi, htheta, heta, htau] using h5

end

end Stage4
end PartC
end GerverSofa

end

end

section

/-!
# Part C Stage 4: positive turning determinant on phases 2--5

The determinant is the signed turning numerator of the nonzero path velocity.
These phasewise facts are the analytic input for the remaining one-turn chord
argument; they do not assert the no-hidden conclusion by themselves.
-/

public section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

noncomputable section

private theorem b1_upper_neg_half_turn : params.b1 ≤ (-1 / 2 : ℝ) := by
  have h := PartB.b1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem d1_lower_thirteen_tenths_turn : (13 / 10 : ℝ) ≤ params.d1 := by
  have h := PartB.d1_contains.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem T_lt_eight_fifths_turn : T < (8 / 5 : ℝ) := by
  have hp := ExactReplay.piI_contains_pi
  have hhi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) := hp.2
  have h32 : (ExactReplay.piI.hi : ℝ) < (16 / 5 : ℝ) := by
    norm_num [ExactReplay.piI, ExactReplay.q]
  dsimp [T]
  linarith

/-! The next six statements expose the coefficient-derivative signs used in
the manuscript's tangent-angle argument.  They are deliberately stated for
the explicit smooth-phase formulae; no derivative is assigned at a switch. -/

theorem phase2_betaPrime_neg {r : ℝ}
    (hr : r ∈ Ioo params.phi params.theta) :
    -(1 / 2 : ℝ) * r + params.b1 < 0 := by
  have hr0 : 0 ≤ r := le_trans phi_nonneg hr.1.le
  nlinarith [b1_upper_neg_half_turn]

theorem phase4_alphaPrime_neg {r : ℝ} (hr : r ∈ Ioo eta tau) :
    (1 / 2 : ℝ) * r - params.d1 < 0 := by
  have hrT : r < T := lt_trans hr.2 tau_lt_T
  nlinarith [d1_lower_thirteen_tenths_turn, T_lt_eight_fifths_turn]

private theorem a1_lower_six_fifths_turn : (6 / 5 : ℝ) ≤ params.a1 := by
  have h := Romik.a1_lower_bound_of_mem_box params_mem
  norm_num at h ⊢
  linarith

private theorem phi_upper_twentieth_turn : params.phi ≤ (1 / 20 : ℝ) := by
  have h := phi_bounds.2
  norm_num at h ⊢
  linarith

private theorem alpha1_prime_nonpos_small_turn {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    -2 * params.a1 * Real.cos s - 2 * params.a2 * Real.sin s ≤ 0 := by
  have hsinUpper := Real.sin_le hs0
  have hcosLower : 1 - s ^ 2 / 2 ≤ Real.cos s :=
    Real.one_sub_sq_div_two_le_cos
  have hcos0 : 0 ≤ Real.cos s := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_gt_three]
  have hcoef : (12 / 5 : ℝ) ≤ 2 * params.a1 := by
    nlinarith [a1_lower_six_fifths_turn]
  have hmul : (12 / 5 : ℝ) * Real.cos s ≤ 2 * params.a1 * Real.cos s :=
    mul_le_mul_of_nonneg_right hcoef hcos0
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  rw [ha2]
  have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) :=
    mul_nonneg hs0 (sub_nonneg.mpr hs20)
  nlinarith [hsinUpper, hcosLower, hmul, hquad]

private theorem beta1_prime_nonpos_small_turn {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    -2 * params.a1 * Real.sin s + 2 * params.a2 * Real.cos s ≤ 0 := by
  have hpi : s ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hcos0 : 0 ≤ Real.cos s := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_gt_three]
  have ha1 : 0 ≤ params.a1 := le_trans (by norm_num : (0 : ℝ) ≤ 6 / 5)
    a1_lower_six_fifths_turn
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  rw [ha2]
  nlinarith [mul_nonneg ha1 hsin0, hcos0]

private theorem phase5_derivative_signs_turn {t : ℝ}
    (ht : t ∈ Ioo tau T) :
    (-2 * params.e1 * Real.cos t - 2 * params.e2 * Real.sin t ≤ 0) ∧
    (-2 * params.e1 * Real.sin t + 2 * params.e2 * Real.cos t ≤ 0) := by
  let s : ℝ := T - t
  have hs0 : 0 ≤ s := by dsimp [s]; linarith [ht.2]
  have hsphi : s ≤ params.phi := by
    have hTtau : T - tau = params.phi := by
      dsimp [tau]
      ring
    dsimp [s]
    rw [← hTtau]
    linarith [ht.1]
  have hs20 : s ≤ (1 / 20 : ℝ) := le_trans hsphi phi_upper_twentieth_turn
  have hap1 := alpha1_prime_nonpos_small_turn hs0 hs20
  have hbp1 := beta1_prime_nonpos_small_turn hs0 hs20
  have he1 := Romik.e1_eq_a1_of_equations params_equations
  have he2 := Romik.e2_eq_neg_a2_of_equations params_equations
  have hsin := Real.sin_pi_div_two_sub s
  have hcos := Real.cos_pi_div_two_sub s
  have hts : t = T - s := by dsimp [s]; ring
  constructor
  · rw [hts]
    dsimp [T]
    rw [he1, he2, hcos, hsin]
    simpa [mul_add, add_mul] using hbp1
  · rw [hts]
    dsimp [T]
    rw [he1, he2, hsin, hcos]
    simpa [mul_add, add_mul] using hap1

/-- Phase-five coefficient derivatives are nonpositive.  This is the exact
formula-level input used below; strict turning follows from the strict
nonvanishing of the first coefficient. -/
theorem phase5_coefficientPrime_nonpos {t : ℝ}
    (ht : t ∈ Ioo tau T) :
    (-2 * params.e1 * Real.cos t - 2 * params.e2 * Real.sin t ≤ 0) ∧
    (-2 * params.e1 * Real.sin t + 2 * params.e2 * Real.cos t ≤ 0) :=
  phase5_derivative_signs_turn ht

end

end Stage4
end PartC
end GerverSofa

end

end

section

/-!
# Part C Stage 4: global path derivative and one-turn velocity monotonicity

The path derivative is glued across the four switches using equality of both
the path values and the body-frame velocity coefficients.  The coefficient
derivatives themselves need not match at a switch.  Consequently the fixed
projection is proved antitone phase by phase and then glued order-theoretically.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

private theorem hasDerivAt_if_le_point
    {f g f' g' : ℝ → Point} {c x : ℝ}
    (hf : HasDerivAt f (f' x) x)
    (hg : HasDerivAt g (g' x) x)
    (hvalue : f c = g c)
    (hderiv : f' c = g' c) :
    HasDerivAt (fun y => if y ≤ c then f y else g y)
      (if x ≤ c then f' x else g' x) x := by
  rcases lt_trichotomy x c with hxc | hxc | hxc
  · rw [ite_eq_left hxc.le]
    apply hf.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hxc] with y hy
    have hyc : y < c := show y < c from hy
    simp [hyc.le]
  · subst x
    rw [ite_eq_left le_rfl]
    have hleft : HasDerivWithinAt
        (fun y => if y ≤ c then f y else g y) (f' c) (Iic c) c := by
      exact hf.hasDerivWithinAt.congr
        (by
          intro y hy
          have hyc : y ≤ c := show y ≤ c from hy
          simp [hyc])
        (by simp)
    have hright : HasDerivWithinAt
        (fun y => if y ≤ c then f y else g y) (f' c) (Ici c) c := by
      have hg' : HasDerivWithinAt g (f' c) (Ici c) c :=
        hg.hasDerivWithinAt.congr_deriv hderiv.symm
      exact hg'.congr
        (by
          intro y hy
          have hcy : c ≤ y := show c ≤ y from hy
          rcases hcy.eq_or_lt with h | h
          · subst y
            simpa using hvalue
          · simp [not_le.mpr h])
        (by simpa using hvalue)
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using
      hleft.union hright
  · rw [ite_eq_right (not_le.mpr hxc)]
    apply hg.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hxc] with y hy
    have hcy : c < y := show c < y from hy
    simp [not_le.mpr hcy]

/-- The literal five-piece Gerver path is differentiable at the switches as
well as in the phase interiors. -/
theorem path_hasDerivAt_noHidden (x : ℝ) :
    HasDerivAt (Romik.path params)
      (Romik.rot x (alphaBetaAt x)) x := by
  let p45 : ℝ → Point := fun y =>
    if y ≤ tau then Romik.path4 params y else Romik.path5 params y
  let d45 : ℝ → Point := fun y =>
    if y ≤ tau then Romik.rot y (Romik.alphaBeta4 params y)
    else Romik.rot y (Romik.alphaBeta5 params y)
  have hp45 (y : ℝ) : HasDerivAt p45 (d45 y) y := by
    apply hasDerivAt_if_le_point
      (path4_hasDerivAt_public y) (path5_hasDerivAt_public y)
    · simpa [tau, T] using PartB.match45
    · exact congrArg (Romik.rot tau) alphaBeta_match45_direct
  let p345 : ℝ → Point := fun y =>
    if y ≤ eta then Romik.path3 params y else p45 y
  let d345 : ℝ → Point := fun y =>
    if y ≤ eta then Romik.rot y (Romik.alphaBeta3 params y) else d45 y
  have hp345 (y : ℝ) : HasDerivAt p345 (d345 y) y := by
    apply hasDerivAt_if_le_point (path3_hasDerivAt_public y) (hp45 y)
    · simp only [p45, ite_eq_left eta_lt_tau.le]
      simpa [eta, T] using PartB.match34
    · simp only [d45, ite_eq_left eta_lt_tau.le]
      exact congrArg (Romik.rot eta) alphaBeta_match34_direct
  let p2345 : ℝ → Point := fun y =>
    if y ≤ params.theta then Romik.path2 params y else p345 y
  let d2345 : ℝ → Point := fun y =>
    if y ≤ params.theta then Romik.rot y (Romik.alphaBeta2 params y)
    else d345 y
  have hp2345 (y : ℝ) : HasDerivAt p2345 (d2345 y) y := by
    apply hasDerivAt_if_le_point (path2_hasDerivAt_public y) (hp345 y)
    · simp only [p345, ite_eq_left theta_lt_eta.le]
      exact PartB.match23
    · simp only [d345, ite_eq_left theta_lt_eta.le]
      exact congrArg (Romik.rot params.theta) alphaBeta_match23_direct
  let p12345 : ℝ → Point := fun y =>
    if y ≤ params.phi then Romik.path1 params y else p2345 y
  let d12345 : ℝ → Point := fun y =>
    if y ≤ params.phi then Romik.rot y (Romik.alphaBeta1 params y)
    else d2345 y
  have hp12345 : HasDerivAt p12345 (d12345 x) x := by
    apply hasDerivAt_if_le_point (path1_hasDerivAt_public x) (hp2345 x)
    · simp only [p2345, ite_eq_left phi_lt_theta.le]
      exact PartB.match12
    · simp only [d2345, ite_eq_left phi_lt_theta.le]
      exact congrArg (Romik.rot params.phi) alphaBeta_match12_direct
  have hpEq : p12345 = Romik.path params := by
    funext y
    simp only [p45, p345, p2345, p12345, Romik.path, eta, tau, T]
    rfl
  have hdEq : d12345 x = Romik.rot x (alphaBetaAt x) := by
    simp only [d45, d345, d2345, d12345, alphaBetaAt]
    by_cases h1 : x ≤ params.phi
    · simp only [ite_eq_left h1]
    · by_cases h2 : x ≤ params.theta
      · simp only [ite_eq_right h1, ite_eq_left h2]
      · by_cases h3 : x ≤ eta
        · simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
        · by_cases h4 : x ≤ tau
          · simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
          · simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
  rw [hpEq] at hp12345
  exact hp12345.congr_deriv hdEq

/-- Scalar projection of the corner velocity on the fixed vector `u(t)`. -/
def uVelocity (t r : ℝ) : ℝ :=
  alpha r * Real.cos (t - r) + beta r * Real.sin (t - r)

private def uVelocityPiece (ab : ℝ → Point) (t r : ℝ) : ℝ :=
  (ab r).1 * Real.cos (t - r) + (ab r).2 * Real.sin (t - r)

private theorem square_hasDerivAt_noHidden (r : ℝ) :
    HasDerivAt (fun s : ℝ => s * s) (r + r) r :=
  Stage2.square_hasDerivAt r

private theorem alpha2_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta2 params s).1) (-1) r := by
  dsimp [Romik.alphaBeta2]
  have h := (hasDerivAt_const r (1 + 2 * params.b1)).fun_sub
    (hasDerivAt_id r)
  exact h.congr_deriv (by ring)

private theorem beta2_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta2 params s).2)
      (-(1 / 2 : ℝ) * r + params.b1) r := by
  dsimp [Romik.alphaBeta2]
  have hsq := HasDerivAt.const_mul (-(1 / 4 : ℝ))
    (square_hasDerivAt_noHidden r)
  have hlin := HasDerivAt.const_mul params.b1 (hasDerivAt_id r)
  have hraw := (((hsq.fun_add hlin).fun_add (hasDerivAt_const r params.b2)).fun_add
    (hasDerivAt_const r (1 / 2 : ℝ)))
  simpa only [id_eq, mul_assoc] using hraw.congr_deriv (by ring)

private theorem alpha3_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta3 params s).1) (-1) r := by
  dsimp [Romik.alphaBeta3]
  have h := (hasDerivAt_const r (-1 - params.c2)).fun_sub
    (hasDerivAt_id r)
  exact h.congr_deriv (by ring)

private theorem beta3_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta3 params s).2) (-1) r := by
  dsimp [Romik.alphaBeta3]
  have h := (hasDerivAt_const r (1 + params.c1)).fun_sub
    (hasDerivAt_id r)
  exact h.congr_deriv (by ring)

private theorem alpha4_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta4 params s).1)
      ((1 / 2 : ℝ) * r - params.d1) r := by
  dsimp [Romik.alphaBeta4]
  have hsq := HasDerivAt.const_mul (1 / 4 : ℝ)
    (square_hasDerivAt_noHidden r)
  have hlin := HasDerivAt.const_mul params.d1 (hasDerivAt_id r)
  have hraw := (((hsq.fun_sub hlin).fun_sub (hasDerivAt_const r params.d2)).fun_sub
    (hasDerivAt_const r (1 / 2 : ℝ)))
  simpa only [id_eq, mul_assoc] using hraw.congr_deriv (by ring)

private theorem beta4_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta4 params s).2) (-1) r := by
  dsimp [Romik.alphaBeta4]
  have h := (hasDerivAt_const r (2 * params.d1 - 1)).fun_sub
    (hasDerivAt_id r)
  exact h.congr_deriv (by ring)

private theorem alpha5_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta5 params s).1)
      (-2 * params.e1 * Real.cos r - 2 * params.e2 * Real.sin r) r := by
  dsimp [Romik.alphaBeta5]
  have hsin := HasDerivAt.const_mul (2 * params.e1)
    (Real.hasDerivAt_sin r)
  have hcos := HasDerivAt.const_mul (2 * params.e2)
    (Real.hasDerivAt_cos r)
  have hraw := ((hasDerivAt_const r (1 : ℝ)).fun_sub hsin).fun_add hcos
  exact hraw.congr_deriv (by ring)

private theorem beta5_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta5 params s).2)
      (-2 * params.e1 * Real.sin r + 2 * params.e2 * Real.cos r) r := by
  dsimp [Romik.alphaBeta5]
  have hcos := HasDerivAt.const_mul (2 * params.e1)
    (Real.hasDerivAt_cos r)
  have hsin := HasDerivAt.const_mul (2 * params.e2)
    (Real.hasDerivAt_sin r)
  have hraw := (hcos.fun_add hsin).fun_sub
    (hasDerivAt_const r (1 / 2 : ℝ))
  exact hraw.congr_deriv (by ring)

private theorem alphaBetaAt_eq_piece2 {r : ℝ}
    (hr : r ∈ Icc params.phi params.theta) :
    alphaBetaAt r = Romik.alphaBeta2 params r := by
  by_cases hphi : r ≤ params.phi
  · have hrphi : r = params.phi := le_antisymm hphi hr.1
    subst r
    simpa [alphaBetaAt] using alphaBeta_match12_direct
  · simp [alphaBetaAt, hphi, hr.2]

private theorem alphaBetaAt_eq_piece3 {r : ℝ}
    (hr : r ∈ Icc params.theta eta) :
    alphaBetaAt r = Romik.alphaBeta3 params r := by
  by_cases htheta : r ≤ params.theta
  · have hrtheta : r = params.theta := le_antisymm htheta hr.1
    subst r
    simp only [alphaBetaAt, ite_eq_right (not_le.mpr phi_lt_theta), ite_eq_left le_rfl]
    exact alphaBeta_match23_direct
  · have hphi : ¬ r ≤ params.phi :=
      not_le.mpr (lt_trans phi_lt_theta (lt_of_not_ge htheta))
    simp [alphaBetaAt, hphi, htheta, hr.2]

private theorem alphaBetaAt_eq_piece4 {r : ℝ}
    (hr : r ∈ Icc eta tau) :
    alphaBetaAt r = Romik.alphaBeta4 params r := by
  by_cases heta : r ≤ eta
  · have hreta : r = eta := le_antisymm heta hr.1
    subst r
    simp only [alphaBetaAt, ite_eq_right (not_le.mpr phi_lt_eta),
      ite_eq_right (not_le.mpr theta_lt_eta), ite_eq_left le_rfl]
    exact alphaBeta_match34_direct
  · have htheta : ¬ r ≤ params.theta :=
      not_le.mpr (lt_trans theta_lt_eta (lt_of_not_ge heta))
    have hphi : ¬ r ≤ params.phi :=
      not_le.mpr (lt_trans phi_lt_theta (lt_of_not_ge htheta))
    simp [alphaBetaAt, hphi, htheta, heta, hr.2]

private theorem alphaBetaAt_eq_piece5 {r : ℝ}
    (hr : r ∈ Icc tau T) :
    alphaBetaAt r = Romik.alphaBeta5 params r := by
  by_cases htau : r ≤ tau
  · have hrtau : r = tau := le_antisymm htau hr.1
    subst r
    simp only [alphaBetaAt, ite_eq_right (not_le.mpr
      (lt_trans phi_lt_theta (lt_trans theta_lt_eta eta_lt_tau))),
      ite_eq_right (not_le.mpr (lt_trans theta_lt_eta eta_lt_tau)),
      ite_eq_right (not_le.mpr eta_lt_tau), ite_eq_left le_rfl]
    exact alphaBeta_match45_direct
  · have heta : ¬ r ≤ eta :=
      not_le.mpr (lt_trans eta_lt_tau (lt_of_not_ge htau))
    have htheta : ¬ r ≤ params.theta :=
      not_le.mpr (lt_trans theta_lt_eta (lt_of_not_ge heta))
    have hphi : ¬ r ≤ params.phi :=
      not_le.mpr (lt_trans phi_lt_theta (lt_of_not_ge htheta))
    simp [alphaBetaAt, hphi, htheta, heta, htau]

private theorem uVelocityPiece_hasDerivAt
    {a b : ℝ → ℝ} {ap bp t r : ℝ}
    (ha : HasDerivAt a ap r) (hb : HasDerivAt b bp r) :
    HasDerivAt
      (fun s => a s * Real.cos (t - s) + b s * Real.sin (t - s))
      ((ap - b r) * Real.cos (t - r) +
        (a r + bp) * Real.sin (t - r)) r := by
  have hsub : HasDerivAt (fun s : ℝ => t - s) (-1) r :=
    by simpa only [id_eq, zero_sub] using
      ((hasDerivAt_const r t).fun_sub (hasDerivAt_id r))
  have hcos : HasDerivAt (fun s : ℝ => Real.cos (t - s))
      (Real.sin (t - r)) r := by
    have h := (Real.hasDerivAt_cos (t - r)).comp r hsub
    exact h.congr_deriv (by ring)
  have hsin : HasDerivAt (fun s : ℝ => Real.sin (t - s))
      (-Real.cos (t - r)) r := by
    have h := (Real.hasDerivAt_sin (t - r)).comp r hsub
    exact h.congr_deriv (by ring)
  have h := (ha.fun_mul hcos).fun_add (hb.fun_mul hsin)
  exact h.congr_deriv (by ring)

private theorem uVelocity_eq_piece2 {t r : ℝ}
    (hr : r ∈ Icc params.phi params.theta) :
    uVelocity t r = uVelocityPiece (Romik.alphaBeta2 params) t r := by
  unfold uVelocity uVelocityPiece
  have h := alphaBetaAt_eq_piece2 hr
  simp only [alpha, beta, h]

private theorem uVelocity_eq_piece3 {t r : ℝ}
    (hr : r ∈ Icc params.theta eta) :
    uVelocity t r = uVelocityPiece (Romik.alphaBeta3 params) t r := by
  unfold uVelocity uVelocityPiece
  have h := alphaBetaAt_eq_piece3 hr
  simp only [alpha, beta, h]

private theorem uVelocity_eq_piece4 {t r : ℝ}
    (hr : r ∈ Icc eta tau) :
    uVelocity t r = uVelocityPiece (Romik.alphaBeta4 params) t r := by
  unfold uVelocity uVelocityPiece
  have h := alphaBetaAt_eq_piece4 hr
  simp only [alpha, beta, h]

private theorem uVelocity_eq_piece5 {t r : ℝ}
    (hr : r ∈ Icc tau T) :
    uVelocity t r = uVelocityPiece (Romik.alphaBeta5 params) t r := by
  unfold uVelocity uVelocityPiece
  have h := alphaBetaAt_eq_piece5 hr
  simp only [alpha, beta, h]

private theorem piece_signs
    {ab : ℝ → Point} {r : ℝ} (hrT : r ∈ Icc params.phi T)
    (heq : alphaBetaAt r = ab r) :
    (ab r).1 ≤ 0 ∧ 0 ≤ (ab r).2 := by
  have ha := alpha_nonpos hrT
  have hb := beta_nonneg hrT
  change (alphaBetaAt r).1 ≤ 0 at ha
  change 0 ≤ (alphaBetaAt r).2 at hb
  rw [heq] at ha hb
  exact ⟨ha, hb⟩

private theorem uVelocity_continuous (t : ℝ) : Continuous (uVelocity t) := by
  unfold uVelocity
  have hsub : Continuous (fun r : ℝ => t - r) :=
    continuous_const.sub continuous_id
  have ha : Continuous alpha := alpha_continuous
  have hb : Continuous beta := beta_continuous
  exact (ha.mul (Real.continuous_cos.comp hsub)).add
    (hb.mul (Real.continuous_sin.comp hsub))

private theorem uVelocity_hasDerivAt_phase2 {t r : ℝ}
    (hr : r ∈ Ioo params.phi params.theta) :
    HasDerivAt (uVelocity t)
      (((-1 : ℝ) - (Romik.alphaBeta2 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta2 params r).1 +
        (-(1/2 : ℝ) * r + params.b1)) * Real.sin (t-r)) r := by
  have hd := uVelocityPiece_hasDerivAt (t := t)
    (alpha2_hasDerivAt r) (beta2_hasDerivAt r)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  exact uVelocity_eq_piece2 (t := t) ⟨hs.1.le, hs.2.le⟩

private theorem uVelocity_hasDerivAt_phase3 {t r : ℝ}
    (hr : r ∈ Ioo params.theta eta) :
    HasDerivAt (uVelocity t)
      (((-1 : ℝ) - (Romik.alphaBeta3 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta3 params r).1 - 1) * Real.sin (t-r)) r := by
  have hd := uVelocityPiece_hasDerivAt (t := t)
    (alpha3_hasDerivAt r) (beta3_hasDerivAt r)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  exact uVelocity_eq_piece3 (t := t) ⟨hs.1.le, hs.2.le⟩

private theorem uVelocity_hasDerivAt_phase4 {t r : ℝ}
    (hr : r ∈ Ioo eta tau) :
    HasDerivAt (uVelocity t)
      ((((1/2 : ℝ) * r - params.d1) -
        (Romik.alphaBeta4 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta4 params r).1 - 1) * Real.sin (t-r)) r := by
  have hd := uVelocityPiece_hasDerivAt (t := t)
    (alpha4_hasDerivAt r) (beta4_hasDerivAt r)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  exact uVelocity_eq_piece4 (t := t) ⟨hs.1.le, hs.2.le⟩

private theorem uVelocity_hasDerivAt_phase5 {t r : ℝ}
    (hr : r ∈ Ioo tau T) :
    HasDerivAt (uVelocity t)
      (((-2 * params.e1 * Real.cos r - 2 * params.e2 * Real.sin r) -
          (Romik.alphaBeta5 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta5 params r).1 +
          (-2 * params.e1 * Real.sin r + 2 * params.e2 * Real.cos r)) *
        Real.sin (t-r)) r := by
  have hd := uVelocityPiece_hasDerivAt (t := t)
    (alpha5_hasDerivAt r) (beta5_hasDerivAt r)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  exact uVelocity_eq_piece5 (t := t) ⟨hs.1.le, hs.2.le⟩

private theorem uVelocity_phase2_anti {t hi : ℝ}
    (hhi : hi ∈ Icc params.phi params.theta) (hit : hi ≤ t) (htT : t ≤ T) :
    AntitoneOn (uVelocity t) (Icc params.phi hi) := by
  let f' : ℝ → ℝ := fun r =>
    (((-1 : ℝ) - (Romik.alphaBeta2 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta2 params r).1 +
        (-(1/2 : ℝ) * r + params.b1)) * Real.sin (t-r))
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := f') (convex_Icc params.phi hi)
  · exact (uVelocity_continuous t).continuousOn
  · intro r hr
    have hir : r ∈ Ioo params.phi hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo params.phi params.theta :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    exact (uVelocity_hasDerivAt_phase2 (t := t) hrphase).hasDerivWithinAt
  · intro r hr
    have hir : r ∈ Ioo params.phi hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo params.phi params.theta :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    have hs := piece_signs
      (show r ∈ Icc params.phi T from
        ⟨hir.1.le, le_trans (le_trans hir.2.le hhi.2) theta_lt_T.le⟩)
      (alphaBetaAt_eq_piece2 ⟨hir.1.le,
        le_trans hir.2.le hhi.2⟩)
    have hbp := (phase2_betaPrime_neg hrphase).le
    have hr0 : 0 ≤ r := le_trans phi_pos.le hir.1.le
    have hd0 : 0 ≤ t-r := by linarith [hir.2, hit]
    have hdT : t-r ≤ T := by linarith [htT, hr0]
    have hsin : 0 ≤ Real.sin (t-r) := Real.sin_nonneg_of_nonneg_of_le_pi hd0
      (le_trans hdT (by dsimp [T]; linarith [Real.pi_pos]))
    have hcos : 0 ≤ Real.cos (t-r) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hd0], by simpa only [T] using hdT⟩
    dsimp only [f']
    exact add_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.2]) hcos)
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.1, hbp]) hsin)

private theorem uVelocity_phase3_anti {t hi : ℝ}
    (hhi : hi ∈ Icc params.theta eta) (hit : hi ≤ t) (htT : t ≤ T) :
    AntitoneOn (uVelocity t) (Icc params.theta hi) := by
  let f' : ℝ → ℝ := fun r =>
    (((-1 : ℝ) - (Romik.alphaBeta3 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta3 params r).1 - 1) * Real.sin (t-r))
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := f') (convex_Icc params.theta hi)
  · exact (uVelocity_continuous t).continuousOn
  · intro r hr
    have hir : r ∈ Ioo params.theta hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo params.theta eta :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    exact (uVelocity_hasDerivAt_phase3 (t := t) hrphase).hasDerivWithinAt
  · intro r hr
    have hir : r ∈ Ioo params.theta hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo params.theta eta :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    have hs := piece_signs
      (show r ∈ Icc params.phi T from
        ⟨(lt_trans phi_lt_theta hir.1).le,
          le_trans (le_trans hir.2.le hhi.2) eta_lt_T.le⟩)
      (alphaBetaAt_eq_piece3 ⟨hir.1.le, le_trans hir.2.le hhi.2⟩)
    have hr0 : 0 ≤ r := le_trans theta_pos.le hir.1.le
    have hd0 : 0 ≤ t-r := by linarith [hir.2, hit]
    have hdT : t-r ≤ T := by linarith [htT, hr0]
    have hsin : 0 ≤ Real.sin (t-r) := Real.sin_nonneg_of_nonneg_of_le_pi hd0
      (le_trans hdT (by dsimp [T]; linarith [Real.pi_pos]))
    have hcos : 0 ≤ Real.cos (t-r) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hd0], by simpa only [T] using hdT⟩
    dsimp only [f']
    exact add_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.2]) hcos)
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.1]) hsin)

private theorem uVelocity_phase4_anti {t hi : ℝ}
    (hhi : hi ∈ Icc eta tau) (hit : hi ≤ t) (htT : t ≤ T) :
    AntitoneOn (uVelocity t) (Icc eta hi) := by
  let f' : ℝ → ℝ := fun r =>
    ((((1/2 : ℝ) * r - params.d1) -
        (Romik.alphaBeta4 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta4 params r).1 - 1) * Real.sin (t-r))
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := f') (convex_Icc eta hi)
  · exact (uVelocity_continuous t).continuousOn
  · intro r hr
    have hir : r ∈ Ioo eta hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo eta tau :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    exact (uVelocity_hasDerivAt_phase4 (t := t) hrphase).hasDerivWithinAt
  · intro r hr
    have hir : r ∈ Ioo eta hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo eta tau :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    have hs := piece_signs
      (show r ∈ Icc params.phi T from
        ⟨(lt_trans phi_lt_eta hir.1).le,
          le_trans (le_trans hir.2.le hhi.2) tau_lt_T.le⟩)
      (alphaBetaAt_eq_piece4 ⟨hir.1.le, le_trans hir.2.le hhi.2⟩)
    have hap := (phase4_alphaPrime_neg hrphase).le
    have hr0 : 0 ≤ r := le_trans theta_pos.le (lt_trans theta_lt_eta hir.1).le
    have hd0 : 0 ≤ t-r := by linarith [hir.2, hit]
    have hdT : t-r ≤ T := by linarith [htT, hr0]
    have hsin : 0 ≤ Real.sin (t-r) := Real.sin_nonneg_of_nonneg_of_le_pi hd0
      (le_trans hdT (by dsimp [T]; linarith [Real.pi_pos]))
    have hcos : 0 ≤ Real.cos (t-r) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hd0], by simpa only [T] using hdT⟩
    dsimp only [f']
    exact add_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.2, hap]) hcos)
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.1]) hsin)

private theorem uVelocity_phase5_anti {t hi : ℝ}
    (hhi : hi ∈ Icc tau T) (hit : hi ≤ t) (htT : t ≤ T) :
    AntitoneOn (uVelocity t) (Icc tau hi) := by
  let f' : ℝ → ℝ := fun r =>
    (((-2 * params.e1 * Real.cos r - 2 * params.e2 * Real.sin r) -
        (Romik.alphaBeta5 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta5 params r).1 +
        (-2 * params.e1 * Real.sin r + 2 * params.e2 * Real.cos r)) *
        Real.sin (t-r))
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := f') (convex_Icc tau hi)
  · exact (uVelocity_continuous t).continuousOn
  · intro r hr
    have hir : r ∈ Ioo tau hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo tau T :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    exact (uVelocity_hasDerivAt_phase5 (t := t) hrphase).hasDerivWithinAt
  · intro r hr
    have hir : r ∈ Ioo tau hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo tau T :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    have hs := piece_signs
      (show r ∈ Icc params.phi T from
        ⟨(lt_trans (lt_trans phi_lt_eta eta_lt_tau) hir.1).le,
          le_trans hir.2.le hhi.2⟩)
      (alphaBetaAt_eq_piece5 ⟨hir.1.le, le_trans hir.2.le hhi.2⟩)
    obtain ⟨hap, hbp⟩ := phase5_coefficientPrime_nonpos hrphase
    have hr0 : 0 ≤ r := le_trans phi_pos.le
      (lt_trans (lt_trans phi_lt_eta eta_lt_tau) hir.1).le
    have hd0 : 0 ≤ t-r := by linarith [hir.2, hit]
    have hdT : t-r ≤ T := by linarith [htT, hr0]
    have hsin : 0 ≤ Real.sin (t-r) := Real.sin_nonneg_of_nonneg_of_le_pi hd0
      (le_trans hdT (by dsimp [T]; linarith [Real.pi_pos]))
    have hcos : 0 ≤ Real.cos (t-r) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hd0], by simpa only [T] using hdT⟩
    dsimp only [f']
    exact add_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.2, hap]) hcos)
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.1, hbp]) hsin)

private theorem antitoneOn_Icc_glue {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b)
    (hleft : AntitoneOn f (Icc a b))
    (hright : AntitoneOn f (Icc b c)) :
    AntitoneOn f (Icc a c) := by
  intro x hx y hy hxy
  by_cases hyb : y ≤ b
  · exact hleft ⟨hx.1, le_trans hxy hyb⟩ ⟨hy.1, hyb⟩ hxy
  by_cases hbx : b ≤ x
  · exact hright ⟨hbx, le_trans hxy hy.2⟩ ⟨le_trans hbx hxy, hy.2⟩ hxy
  have hxb : x ≤ b := le_of_not_ge hbx
  have hby : b ≤ y := le_of_not_ge hyb
  exact le_trans
    (hright ⟨le_rfl, le_trans hby hy.2⟩ ⟨hby, hy.2⟩ hby)
    (hleft ⟨hx.1, hxb⟩ ⟨hab, le_rfl⟩ hxb)

/-- For fixed terminal time, the projected path velocity is antitone on the
complete ordered no-hidden interval. -/
theorem uVelocity_antitone {t : ℝ} (ht : t ∈ Icc params.phi T) :
    AntitoneOn (uVelocity t) (Icc params.phi t) := by
  by_cases h2 : t ≤ params.theta
  · exact uVelocity_phase2_anti ⟨ht.1, h2⟩ le_rfl ht.2
  have ht2 : params.theta ≤ t := (lt_of_not_ge h2).le
  have hphase2 := uVelocity_phase2_anti
    (t := t) (hi := params.theta) ⟨phi_lt_theta.le, le_rfl⟩ ht2 ht.2
  by_cases h3 : t ≤ eta
  · exact antitoneOn_Icc_glue phi_lt_theta.le hphase2
      (uVelocity_phase3_anti ⟨ht2, h3⟩ le_rfl ht.2)
  have ht3 : eta ≤ t := (lt_of_not_ge h3).le
  have hphase3 := uVelocity_phase3_anti
    (t := t) (hi := eta) ⟨theta_lt_eta.le, le_rfl⟩ ht3 ht.2
  have h23 := antitoneOn_Icc_glue phi_lt_theta.le
    hphase2 hphase3
  by_cases h4 : t ≤ tau
  · exact antitoneOn_Icc_glue phi_lt_eta.le h23
      (uVelocity_phase4_anti ⟨ht3, h4⟩ le_rfl ht.2)
  have ht4 : tau ≤ t := (lt_of_not_ge h4).le
  have hphase4 := uVelocity_phase4_anti
    (t := t) (hi := tau) ⟨eta_lt_tau.le, le_rfl⟩ ht4 ht.2
  have h234 := antitoneOn_Icc_glue phi_lt_eta.le h23 hphase4
  exact antitoneOn_Icc_glue
    (lt_trans phi_lt_eta eta_lt_tau).le h234
    (uVelocity_phase5_anti ⟨ht4, ht.2⟩ le_rfl ht.2)

private theorem dot_fixed_hasDerivAt {f : ℝ → Point} {f' : Point}
    {r : ℝ} (hf : HasDerivAt f f' r) (w : Point) :
    HasDerivAt (fun s => dot (f s) w) (dot f' w) r := by
  have h1 := HasDerivAt.const_mul w.1 hf.fst
  have h2 := HasDerivAt.const_mul w.2 hf.snd
  simpa [dot, mul_comm] using h1.fun_add h2

/-- Derivative of `U(r,t)` in its first variable. -/
theorem UValue_hasDerivAt_noHidden (r t : ℝ) :
    HasDerivAt (fun s => Stage2.UValue s t) (uVelocity t r) r := by
  have hpRaw := (path_hasDerivAt_noHidden r).fun_sub
    (hasDerivAt_const r (Romik.path params t))
  have hp : HasDerivAt
      (fun s => Romik.path params s - Romik.path params t)
      (Romik.rot r (alphaBetaAt r)) r := by
    exact hpRaw.congr_deriv (by simp)
  have hd := dot_fixed_hasDerivAt hp (u t)
  have hrot : dot (Romik.rot r (alphaBetaAt r)) (u t) = uVelocity t r := by
    dsimp [dot, Romik.rot, u, uVelocity, alpha, beta]
    rw [Real.cos_sub, Real.sin_sub]
    ring
  exact hd.congr_deriv hrot

/-- Concavity form of the manuscript's one-turn tangent argument. -/
theorem U_concave_on (t : ℝ) (ht : t ∈ Icc params.phi T) :
    ConcaveOn ℝ (Icc params.phi t) (fun r => Stage2.UValue r t) := by
  have hanti := uVelocity_antitone ht
  have hantiDeriv : AntitoneOn
      (deriv (fun r => Stage2.UValue r t)) (interior (Icc params.phi t)) := by
    intro x hx y hy hxy
    rw [(UValue_hasDerivAt_noHidden x t).deriv,
      (UValue_hasDerivAt_noHidden y t).deriv]
    exact hanti (interior_subset hx) (interior_subset hy) hxy
  exact hantiDeriv.concaveOn_of_deriv (convex_Icc params.phi t)
    (by
      intro r hr
      exact (UValue_hasDerivAt_noHidden r t).continuousAt.continuousWithinAt)
    (by
      intro r hr
      exact (UValue_hasDerivAt_noHidden r t).differentiableAt.differentiableWithinAt)

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C Stage 4: exact reflection bridge for the second no-hidden inequality

The affine reflection is derived phase by phase from the certified matching
equations.  No global symmetry hypothesis is introduced.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

/-- Reflect a point horizontally about the axis `x = k31`. -/
def noHiddenHReflect (z : Point) : Point :=
  (2 * params.k31 - z.1, z.2)

@[simp] theorem noHiddenHReflect_involutive (z : Point) :
    noHiddenHReflect (noHiddenHReflect z) = z := by
  ext <;> simp [noHiddenHReflect]

private theorem phase24_horizontal_reflection_noHidden (s : ℝ) :
    (Romik.path4 params (T - s)).1 + (Romik.path2 params s).1 =
      params.k41 + params.k21 := by
  have hd1 := Romik.d1_eq_quarterPi_sub_b1_of_equations params_equations
  have hd2 :=
    Romik.d2_eq_b2_add_quarterPi_correction_of_equations params_equations
  dsimp [T, Romik.path4, Romik.path2, Romik.rot, Romik.addK]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, hd1, hd2]
  ring

private theorem phase3_horizontal_reflection_noHidden (s : ℝ) :
    (Romik.path3 params (T - s)).1 + (Romik.path3 params s).1 =
      2 * params.k31 := by
  have hc2 := Romik.c2_eq_c1_sub_halfPi_of_equations params_equations
  dsimp [T, Romik.path3, Romik.rot, Romik.addK]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, hc2]
  ring

private theorem k41_add_k21_eq_two_k31_noHidden :
    params.k41 + params.k21 = 2 * params.k31 := by
  have h24 := phase24_horizontal_reflection_noHidden params.theta
  have h33 := phase3_horizontal_reflection_noHidden params.theta
  have h23 := congrArg Prod.fst PartB.match23
  have h34 := congrArg Prod.fst PartB.match34
  simp only [T] at h24 h33 h34
  linarith

private theorem phase24_reflect_noHidden (s : ℝ) :
    Romik.path4 params (T - s) =
      noHiddenHReflect (Romik.path2 params s) := by
  apply Prod.ext
  · have h := phase24_horizontal_reflection_noHidden s
    rw [k41_add_k21_eq_two_k31_noHidden] at h
    dsimp [noHiddenHReflect]
    linarith
  · have h :=
      Romik.phase24_vertical_reflection_of_equations params_equations s
    have hk := Romik.k42_eq_k22_of_equations params_equations
    rw [hk] at h
    dsimp [T] at h ⊢
    dsimp [noHiddenHReflect]
    linarith

private theorem phase42_reflect_noHidden (s : ℝ) :
    Romik.path2 params (T - s) =
      noHiddenHReflect (Romik.path4 params s) := by
  have h := congrArg noHiddenHReflect
    (phase24_reflect_noHidden (T - s))
  have hT : T - (T - s) = s := by ring
  rw [hT, noHiddenHReflect_involutive] at h
  exact h.symm

private theorem phase3_reflect_noHidden (s : ℝ) :
    Romik.path3 params (T - s) =
      noHiddenHReflect (Romik.path3 params s) := by
  apply Prod.ext
  · have h := phase3_horizontal_reflection_noHidden s
    dsimp [noHiddenHReflect]
    linarith
  · have h :=
      Romik.phase3_vertical_reflection_of_equations params_equations s
    simpa [T, noHiddenHReflect] using h

private theorem phase15_horizontal_reflection_noHidden (s : ℝ) :
    (Romik.path5 params (T - s)).1 + (Romik.path1 params s).1 =
      params.k51 + params.k11 := by
  have he1 := Romik.e1_eq_a1_of_equations params_equations
  have he2 := Romik.e2_eq_neg_a2_of_equations params_equations
  dsimp [T, Romik.path5, Romik.path1, Romik.rot, Romik.addK]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, he1, he2]
  ring

private theorem k51_add_k11_eq_two_k31_noHidden :
    params.k51 + params.k11 = 2 * params.k31 := by
  have h15 := phase15_horizontal_reflection_noHidden params.phi
  have h24 := phase24_horizontal_reflection_noHidden params.phi
  have h12 := congrArg Prod.fst PartB.match12
  have h45 := congrArg Prod.fst PartB.match45
  rw [k41_add_k21_eq_two_k31_noHidden] at h24
  simp only [T] at h15 h24 h45
  linarith

private theorem phase15_reflect_noHidden (s : ℝ) :
    Romik.path5 params (T - s) =
      noHiddenHReflect (Romik.path1 params s) := by
  apply Prod.ext
  · have h := phase15_horizontal_reflection_noHidden s
    rw [k51_add_k11_eq_two_k31_noHidden] at h
    dsimp [noHiddenHReflect]
    linarith
  · have h :=
      Romik.phase15_vertical_reflection_of_equations params_equations s
    have hk := Romik.k52_eq_k12_of_equations params_equations
    rw [hk] at h
    dsimp [T] at h ⊢
    dsimp [noHiddenHReflect]
    linarith

private theorem phase51_reflect_noHidden (s : ℝ) :
    Romik.path1 params (T - s) =
      noHiddenHReflect (Romik.path5 params s) := by
  have h := congrArg noHiddenHReflect
    (phase15_reflect_noHidden (T - s))
  have hT : T - (T - s) = s := by ring
  rw [hT, noHiddenHReflect_involutive] at h
  exact h.symm

private theorem path_eq_phase1_noHidden {s : ℝ} (hs : s ≤ params.phi) :
    Romik.path params s = Romik.path1 params s := by
  simp only [Romik.path, ite_eq_left hs]

private theorem path_eq_phase2_noHidden {s : ℝ}
    (hphi : params.phi < s) (hs : s ≤ params.theta) :
    Romik.path params s = Romik.path2 params s := by
  simp only [Romik.path, ite_eq_right (not_le.mpr hphi), ite_eq_left hs]

private theorem path_eq_phase3_noHidden {s : ℝ}
    (htheta : params.theta < s) (hs : s ≤ eta) :
    Romik.path params s = Romik.path3 params s := by
  have hphi : params.phi < s := lt_trans phi_lt_theta htheta
  simpa only [eta, T] using
    (show Romik.path params s = Romik.path3 params s by
      simp only [Romik.path, ite_eq_right (not_le.mpr hphi),
        ite_eq_right (not_le.mpr htheta), ite_eq_left (by simpa [eta, T] using hs)])

private theorem path_eq_phase4_noHidden {s : ℝ}
    (heta : eta < s) (hs : s ≤ tau) :
    Romik.path params s = Romik.path4 params s := by
  have htheta : params.theta < s := lt_trans theta_lt_eta heta
  have hphi : params.phi < s := lt_trans phi_lt_theta htheta
  have hnotEta : ¬ s ≤ Real.pi / 2 - params.theta := by
    apply not_le.mpr
    simpa only [eta, T] using heta
  have hleTau : s ≤ Real.pi / 2 - params.phi := by
    simpa only [tau, T] using hs
  simp only [Romik.path, ite_eq_right (not_le.mpr hphi),
    ite_eq_right (not_le.mpr htheta),
    ite_eq_right hnotEta, ite_eq_left hleTau]

private theorem path_eq_phase5_noHidden {s : ℝ} (hs : tau < s) :
    Romik.path params s = Romik.path5 params s := by
  have heta : eta < s := lt_trans eta_lt_tau hs
  have htheta : params.theta < s := lt_trans theta_lt_eta heta
  have hphi : params.phi < s := lt_trans phi_lt_theta htheta
  have hnotEta : ¬ s ≤ Real.pi / 2 - params.theta := by
    apply not_le.mpr
    simpa only [eta, T] using heta
  have hnotTau : ¬ s ≤ Real.pi / 2 - params.phi := by
    apply not_le.mpr
    simpa only [tau, T] using hs
  simp only [Romik.path, ite_eq_right (not_le.mpr hphi),
    ite_eq_right (not_le.mpr htheta),
    ite_eq_right hnotEta, ite_eq_right hnotTau]

/-- Exact global horizontal reflection of the literal five-piece path. -/
theorem path_reflect_noHidden {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    Romik.path params (T - s) =
      noHiddenHReflect (Romik.path params s) := by
  by_cases h1 : s ≤ params.phi
  · by_cases he : s = params.phi
    · subst s
      rw [show T - params.phi = tau by rfl,
        path_eq_phase4_noHidden eta_lt_tau le_rfl,
        path_eq_phase1_noHidden le_rfl]
      exact (phase24_reflect_noHidden params.phi).trans
        (congrArg noHiddenHReflect PartB.match12.symm)
    · have hsphi : s < params.phi := lt_of_le_of_ne h1 he
      have href : tau < T - s := by dsimp [tau]; linarith
      rw [path_eq_phase5_noHidden href, path_eq_phase1_noHidden h1]
      exact phase15_reflect_noHidden s
  · have hphi : params.phi < s := lt_of_not_ge h1
    by_cases h2 : s ≤ params.theta
    · by_cases he : s = params.theta
      · subst s
        rw [show T - params.theta = eta by rfl,
          path_eq_phase3_noHidden theta_lt_eta le_rfl,
          path_eq_phase2_noHidden phi_lt_theta le_rfl]
        exact (phase3_reflect_noHidden params.theta).trans
          (congrArg noHiddenHReflect PartB.match23.symm)
      · have hstheta : s < params.theta := lt_of_le_of_ne h2 he
        have hetaRef : eta < T - s := by dsimp [eta]; linarith
        have htauRef : T - s ≤ tau := by dsimp [tau]; linarith
        rw [path_eq_phase4_noHidden hetaRef htauRef,
          path_eq_phase2_noHidden hphi h2]
        exact phase24_reflect_noHidden s
    · have htheta : params.theta < s := lt_of_not_ge h2
      by_cases h3 : s ≤ eta
      · by_cases he : s = eta
        · subst s
          rw [show T - eta = params.theta by
                dsimp [eta]; ring,
            path_eq_phase2_noHidden phi_lt_theta le_rfl,
            path_eq_phase3_noHidden theta_lt_eta le_rfl]
          have h := congrArg noHiddenHReflect
            (phase3_reflect_noHidden params.theta)
          rw [noHiddenHReflect_involutive] at h
          simpa [eta] using (PartB.match23.trans h.symm)
        · have hseta : s < eta := lt_of_le_of_ne h3 he
          have hthetaRef : params.theta < T - s := by
            dsimp [eta] at hseta
            linarith
          have hetaRef : T - s ≤ eta := by dsimp [eta]; linarith
          rw [path_eq_phase3_noHidden hthetaRef hetaRef,
            path_eq_phase3_noHidden htheta h3]
          exact phase3_reflect_noHidden s
      · have hetaS : eta < s := lt_of_not_ge h3
        by_cases h4 : s ≤ tau
        · by_cases he : s = tau
          · subst s
            rw [show T - tau = params.phi by
                  dsimp [tau]; ring,
              path_eq_phase1_noHidden le_rfl,
              path_eq_phase4_noHidden eta_lt_tau le_rfl]
            have h := congrArg noHiddenHReflect
              (phase24_reflect_noHidden params.phi)
            rw [noHiddenHReflect_involutive] at h
            simpa [tau] using (PartB.match12.trans h.symm)
          · have hstau : s < tau := lt_of_le_of_ne h4 he
            have hphiRef : params.phi < T - s := by
              dsimp [tau] at hstau
              linarith
            have hthetaRef : T - s ≤ params.theta := by
              dsimp [eta] at hetaS
              linarith
            rw [path_eq_phase2_noHidden hphiRef hthetaRef,
              path_eq_phase4_noHidden hetaS h4]
            exact phase42_reflect_noHidden s
        · have htauS : tau < s := lt_of_not_ge h4
          have href0 : 0 ≤ T - s := by linarith [hs.2]
          have hrefphi : T - s ≤ params.phi := by
            dsimp [tau] at htauS
            linarith
          rw [path_eq_phase1_noHidden hrefphi,
            path_eq_phase5_noHidden htauS]
          exact phase51_reflect_noHidden s

/-- Reflection transports the second no-hidden scalar to the first one. -/
theorem VValue_eq_reflected_UValue {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (hr : r ∈ Icc (0 : ℝ) T) :
    Stage2.VValue t r = Stage2.UValue (T-r) (T-t) := by
  rw [Stage2.VValue, Stage2.UValue,
    path_reflect_noHidden hr, path_reflect_noHidden ht]
  dsimp [dot, noHiddenHReflect, u, v, T]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C Stage 4: direct no-hidden-crossing closure

The first inequality follows from concavity and the two endpoint values.  The
second is its exact phase-derived horizontal reflection.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

/-- Concrete first no-hidden-crossing theorem. -/
theorem noHiddenU_direct : NoHiddenCrossingU := by
  intro r hr t ht
  change 0 ≤ Stage2.UValue r t
  have htPhys : t ∈ Icc params.phi T :=
    ⟨le_trans hr.1 ht.1, ht.2⟩
  have hconc := U_concave_on t htPhys
  have hphi := U_phi_nonneg htPhys
  have htt : Stage2.UValue t t = 0 := by
    simp [Stage2.UValue, dot]
  by_cases hrt : r = t
  · subst r
    exact le_of_eq htt.symm
  · have hrtlt : r < t := lt_of_le_of_ne ht.1 hrt
    have hphit : params.phi < t := lt_of_le_of_lt hr.1 hrtlt
    let a : ℝ := (t-r) / (t-params.phi)
    let b : ℝ := (r-params.phi) / (t-params.phi)
    have ha : 0 ≤ a := by
      dsimp [a]
      exact div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hphit.le)
    have hb : 0 ≤ b := by
      dsimp [b]
      exact div_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hphit.le)
    have hab : a + b = 1 := by
      dsimp [a, b]
      field_simp [sub_ne_zero.mpr (ne_of_gt hphit)]
      ring
    have hrcomb : a • params.phi + b • t = r := by
      dsimp [a, b]
      field_simp [sub_ne_zero.mpr (ne_of_gt hphit)]
      ring
    have hJ := hconc.2
      (show params.phi ∈ Icc params.phi t from ⟨le_rfl, hphit.le⟩)
      (show t ∈ Icc params.phi t from ⟨hphit.le, le_rfl⟩)
      ha hb hab
    rw [hrcomb] at hJ
    change a • Stage2.UValue params.phi t + b • Stage2.UValue t t ≤
      Stage2.UValue r t at hJ
    rw [htt] at hJ
    simp only [smul_eq_mul, mul_zero, add_zero] at hJ
    nlinarith

/-- Concrete reflected no-hidden-crossing theorem. -/
theorem noHiddenV_direct : NoHiddenCrossingV := by
  intro t ht r hr
  change 0 ≤ Stage2.VValue t r
  have htT : t ∈ Icc (0 : ℝ) T :=
    ⟨ht.1, le_trans ht.2 Stage2.tau_le_T⟩
  have hrT : r ∈ Icc (0 : ℝ) T :=
    ⟨le_trans ht.1 hr.1, le_trans hr.2 Stage2.tau_le_T⟩
  have hleft : T-r ∈ Icc params.phi T := by
    constructor
    · dsimp [tau] at hr
      linarith [hr.2]
    · linarith [hrT.1]
  have hright : T-t ∈ Icc (T-r) T := by
    constructor
    · linarith [hr.1]
    · linarith [ht.1]
  have hU := noHiddenU_direct (T-r) hleft (T-t) hright
  change 0 ≤ Stage2.UValue (T-r) (T-t) at hU
  rw [← VValue_eq_reflected_UValue htT hrT] at hU
  exact hU

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part C / Stage4 / Niche Envelope Support
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set

private theorem phi_le_one_twentieth_diag :
    params.phi ≤ (1 / 20 : ℝ) := by
  have h := phi_bounds.2
  norm_num at h ⊢
  linarith

private theorem a1_lower_diag : (6 / 5 : ℝ) ≤ params.a1 := by
  have h := Romik.a1_lower_bound_of_mem_box params_mem
  norm_num at h ⊢
  linarith

private theorem a1_upper_diag : params.a1 ≤ (5 / 4 : ℝ) := by
  have h := PartB.a1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem phase1_alpha_lower {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    (-1 / 8 : ℝ) ≤ (Romik.alphaBeta1 params s).1 := by
  have hpi : s ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hsinUpper := Real.sin_le hs0
  have hcosUpper := Real.cos_le_one s
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  have hmul : 2 * params.a1 * Real.sin s ≤ (1 / 8 : ℝ) := by
    have h1 : 2 * params.a1 ≤ (5 / 2 : ℝ) := by
      nlinarith [a1_upper_diag]
    have h2 : Real.sin s ≤ (1 / 20 : ℝ) :=
      le_trans hsinUpper hs20
    nlinarith [mul_nonneg hsin0 (sub_nonneg.mpr h1),
      mul_nonneg (sub_nonneg.mpr h2) (show 0 ≤ (5 / 2 : ℝ) by norm_num)]
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith

private theorem phase1_alpha_nonpos_diag {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    (Romik.alphaBeta1 params s).1 ≤ 0 := by
  have hpi : s ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hsinLower := Real.sin_ge_sub_cube hs0
  have hcosLower : 1 - s ^ 2 / 2 ≤ Real.cos s :=
    Real.one_sub_sq_div_two_le_cos
  have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) :=
    mul_nonneg hs0 (sub_nonneg.mpr hs20)
  have hcube : 0 ≤ s ^ 2 * ((1 / 20 : ℝ) - s) :=
    mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs20)
  have hcoef : (12 / 5 : ℝ) ≤ 2 * params.a1 := by
    nlinarith [a1_lower_diag]
  have hmul : (12 / 5 : ℝ) * Real.sin s ≤
      2 * params.a1 * Real.sin s :=
    mul_le_mul_of_nonneg_right hcoef hsin0
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith [hsinLower, hcosLower, hquad, hcube, hmul]

private theorem phase1_beta_lower {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    (13 / 10 : ℝ) ≤ (Romik.alphaBeta1 params s).2 := by
  have hpi : s ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hsinUpper := Real.sin_le hs0
  have hcosLower : 1 - s ^ 2 / 2 ≤ Real.cos s :=
    Real.one_sub_sq_div_two_le_cos
  have hcosCrude : (799 / 800 : ℝ) ≤ Real.cos s := by
    nlinarith [hcosLower, sq_nonneg s,
      mul_nonneg hs0 (sub_nonneg.mpr hs20)]
  have hcos0 : 0 ≤ Real.cos s := by linarith
  have hcoef : (12 / 5 : ℝ) ≤ 2 * params.a1 := by
    nlinarith [a1_lower_diag]
  have hmul : (12 / 5 : ℝ) * Real.cos s ≤
      2 * params.a1 * Real.cos s :=
    mul_le_mul_of_nonneg_right hcoef hcos0
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith [hsinUpper, hmul]

private theorem dot_rot_phase1_diag (s t : ℝ) :
    dot (Romik.rot s (Romik.alphaBeta1 params s)) (u t + v t) =
      (Romik.alphaBeta1 params s).1 *
          (Real.cos (s - t) + Real.sin (s - t)) +
      (Romik.alphaBeta1 params s).2 *
          (Real.cos (s - t) - Real.sin (s - t)) := by
  simp [dot, Romik.rot, u, v, Real.cos_sub, Real.sin_sub]
  ring

private theorem phase1_diag_deriv_nonneg {t s : ℝ}
    (ht0 : 0 ≤ t) (hts : t ≤ s) (hsphi : s ≤ params.phi) :
    0 ≤ dot (Romik.rot s (Romik.alphaBeta1 params s)) (u t + v t) := by
  have hs0 : 0 ≤ s := le_trans ht0 hts
  have hs20 : s ≤ (1 / 20 : ℝ) :=
    le_trans hsphi phi_le_one_twentieth_diag
  have hd0 : 0 ≤ s - t := sub_nonneg.mpr hts
  have hd20 : s - t ≤ (1 / 20 : ℝ) := by linarith
  have hdpi : s - t ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin (s - t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hd0 hdpi
  have hsinUpper := Real.sin_le hd0
  have hcosLower : 1 - (s - t) ^ 2 / 2 ≤ Real.cos (s - t) :=
    Real.one_sub_sq_div_two_le_cos
  have hcosUpper := Real.cos_le_one (s - t)
  have hdiff : (9 / 10 : ℝ) ≤
      Real.cos (s - t) - Real.sin (s - t) := by
    nlinarith [hcosLower, hsinUpper, sq_nonneg (s - t),
      mul_nonneg hd0 (sub_nonneg.mpr hd20)]
  have hsum0 : 0 ≤ Real.cos (s - t) + Real.sin (s - t) := by
    nlinarith
  have hsumUpper : Real.cos (s - t) + Real.sin (s - t) ≤ (21 / 20 : ℝ) := by
    nlinarith
  have haLo := phase1_alpha_lower hs0 hs20
  have haHi := phase1_alpha_nonpos_diag hs0 hs20
  have hbLo := phase1_beta_lower hs0 hs20
  have haProd : (-21 / 160 : ℝ) ≤
      (Romik.alphaBeta1 params s).1 *
        (Real.cos (s - t) + Real.sin (s - t)) := by
    have hmul1 := mul_le_mul_of_nonpos_left hsumUpper haHi
    have hmul2 := mul_le_mul_of_nonneg_right haLo
      (show 0 ≤ (21 / 20 : ℝ) by norm_num)
    nlinarith
  have hbProd : (117 / 100 : ℝ) ≤
      (Romik.alphaBeta1 params s).2 *
        (Real.cos (s - t) - Real.sin (s - t)) := by
    have hdiff0 : 0 ≤ Real.cos (s - t) - Real.sin (s - t) := by linarith
    have hb0 : 0 ≤ (Romik.alphaBeta1 params s).2 := by linarith
    nlinarith [mul_nonneg
      ((show 0 ≤ (Romik.alphaBeta1 params s).2 - 13 / 10 by linarith)) hdiff0,
      mul_nonneg (show 0 ≤ (13 / 10 : ℝ) by norm_num)
        (show 0 ≤ Real.cos (s - t) - Real.sin (s - t) - 9 / 10 by linarith)]
  rw [dot_rot_phase1_diag]
  linarith

private theorem dot_path1_diag_hasDerivAt (t s : ℝ) :
    HasDerivAt (fun r => dot (Romik.path1 params r) (u t + v t))
      (dot (Romik.rot s (Romik.alphaBeta1 params s)) (u t + v t)) s := by
  have h := path1_hasDerivAt_public s
  have h1 := HasDerivAt.const_mul (u t + v t).1 h.fst
  have h2 := HasDerivAt.const_mul (u t + v t).2 h.snd
  simpa [dot, mul_comm] using h1.fun_add h2

theorem early_endpoint_diagonal_nonneg {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) :
    0 ≤ dot (Romik.path params params.phi - Romik.path params t) (u t + v t) := by
  have hmono : MonotoneOn
      (fun s => dot (Romik.path1 params s) (u t + v t))
      (Icc t params.phi) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun s => dot (Romik.rot s (Romik.alphaBeta1 params s)) (u t + v t))
      (convex_Icc t params.phi) ?_ ?_ ?_
    · intro s hs
      exact (dot_path1_diag_hasDerivAt t s).continuousAt.continuousWithinAt
    · intro s hs
      exact (dot_path1_diag_hasDerivAt t s).hasDerivWithinAt
    · intro s hs
      have hi : s ∈ Ioo t params.phi := by
        simpa only [interior_Icc] using hs
      exact phase1_diag_deriv_nonneg ht.1 hi.1.le hi.2.le
  have hle := hmono
    (show t ∈ Icc t params.phi from ⟨le_rfl, ht.2⟩)
    (show params.phi ∈ Icc t params.phi from ⟨ht.2, le_rfl⟩) ht.2
  have hpathT : Romik.path params t = Romik.path1 params t := by
    simp only [Romik.path, ite_eq_left ht.2]
  have hpathPhi : Romik.path params params.phi =
      Romik.path1 params params.phi := by
    simp only [Romik.path, ite_eq_left le_rfl]
  rw [hpathT, hpathPhi]
  unfold dot at hle ⊢
  dsimp at hle ⊢
  linarith

private def diagPhaseB4 (r : ℝ) : Point :=
  Stage2.phaseA4 r - u r

private def diagPhaseB5 (r : ℝ) : Point :=
  Stage2.phaseA5 r - u r

private theorem u_hasDerivAt_diag (r : ℝ) : HasDerivAt u (v r) r :=
  Stage2.u_hasDerivAt r

private theorem diagPhaseB4_hasDerivAt (r : ℝ) :
    HasDerivAt diagPhaseB4 ((params.d1 - r / 2 - 1) • v r) r := by
  have h := (Stage2.A4_hasDerivAt_public r).fun_sub (u_hasDerivAt_diag r)
  refine h.congr_deriv ?_
  apply Prod.ext <;> simp [v] <;> ring

private theorem diagPhaseB5_hasDerivAt (r : ℝ) :
    HasDerivAt diagPhaseB5 ((-(1 / 2 : ℝ)) • v r) r := by
  have h := (Stage2.A5_hasDerivAt_public r).fun_sub (u_hasDerivAt_diag r)
  refine h.congr_deriv ?_
  apply Prod.ext <;> simp [v] <;> ring

private theorem diagPhaseB4_eq_B {r : ℝ} (hr : r ∈ Icc eta tau) :
    diagPhaseB4 r = B r := by
  rcases hr.1.eq_or_lt with h | h
  · subst r
    have hm : Romik.path3 params eta = Romik.path4 params eta := by
      simpa [eta, T] using PartB.match34
    have hdiag : diagPhaseB4 eta =
        Romik.path4 params eta +
          (Romik.alphaBeta4 params eta).1 • v eta := by
      apply Prod.ext <;> simp [diagPhaseB4, Stage2.phaseA4]
    have hetaRaw : eta ≤ Real.pi / 2 - params.theta := by rfl
    have hB : B eta = Romik.path3 params eta +
        (Romik.alphaBeta3 params eta).1 • v eta := by
      apply Prod.ext <;>
        simp [B, alpha, alphaBetaAt, Romik.path,
          not_le.mpr phi_lt_eta, not_le.mpr theta_lt_eta, hetaRaw]
    calc
      diagPhaseB4 eta = Romik.path4 params eta +
          (Romik.alphaBeta4 params eta).1 • v eta := hdiag
      _ = Romik.path3 params eta +
          (Romik.alphaBeta3 params eta).1 • v eta := by
            rw [hm, alphaBeta_match34_direct]
      _ = B eta := hB.symm
  · have hetaRaw : Real.pi / 2 - params.theta < r := by
      simpa [eta, T] using h
    have htauRaw : r ≤ Real.pi / 2 - params.phi := by
      simpa [tau, T] using hr.2
    apply Prod.ext <;>
      simp [diagPhaseB4, Stage2.phaseA4, B, alpha, alphaBetaAt,
        Romik.path, not_le.mpr (lt_trans phi_lt_eta h),
        not_le.mpr (lt_trans theta_lt_eta h), not_le.mpr hetaRaw, htauRaw, eta, tau, T]

private theorem diagPhaseB5_eq_B {r : ℝ} (hr : r ∈ Icc tau T) :
    diagPhaseB5 r = B r := by
  rcases hr.1.eq_or_lt with h | h
  · subst r
    have hm : Romik.path4 params tau = Romik.path5 params tau := by
      simpa [tau, T] using PartB.match45
    have hdiag : diagPhaseB5 tau =
        Romik.path5 params tau +
          (Romik.alphaBeta5 params tau).1 • v tau := by
      apply Prod.ext <;> simp [diagPhaseB5, Stage2.phaseA5]
    have htauRaw : tau ≤ Real.pi / 2 - params.phi := by rfl
    have hetaRaw : ¬ tau ≤ Real.pi / 2 - params.theta := by
      exact not_le.mpr (by simpa [eta, T] using eta_lt_tau)
    have hB : B tau = Romik.path4 params tau +
        (Romik.alphaBeta4 params tau).1 • v tau := by
      apply Prod.ext <;>
        simp [B, alpha, alphaBetaAt, Romik.path,
          not_le.mpr (lt_trans phi_lt_eta eta_lt_tau),
          not_le.mpr (lt_trans theta_lt_eta eta_lt_tau),
          not_le.mpr eta_lt_tau, hetaRaw, htauRaw]
    calc
      diagPhaseB5 tau = Romik.path5 params tau +
          (Romik.alphaBeta5 params tau).1 • v tau := hdiag
      _ = Romik.path4 params tau +
          (Romik.alphaBeta4 params tau).1 • v tau := by
            rw [hm, alphaBeta_match45_direct]
      _ = B tau := hB.symm
  · have hetaRaw : Real.pi / 2 - params.theta < r := by
      simpa [eta, T] using lt_trans eta_lt_tau h
    have htauRaw : Real.pi / 2 - params.phi < r := by
      simpa [tau, T] using h
    apply Prod.ext <;>
      simp [diagPhaseB5, Stage2.phaseA5, B, alpha, alphaBetaAt,
        Romik.path,
        not_le.mpr (lt_trans (lt_trans phi_lt_eta eta_lt_tau) h),
        not_le.mpr (lt_trans (lt_trans theta_lt_eta eta_lt_tau) h),
        not_le.mpr hetaRaw, not_le.mpr htauRaw, eta, tau, T]

private theorem theta_upper_diag : params.theta ≤ (689 / 1000 : ℝ) := by
  have h := theta_bounds.2
  norm_num at h ⊢
  linarith

private theorem halfT_le_eta_sub_phi : T / 2 ≤ eta - params.phi := by
  have hp : (157 / 50 : ℝ) < Real.pi := by
    have h := Real.pi_gt_d2
    norm_num at h ⊢
    exact h
  dsimp [eta, T]
  nlinarith [theta_upper_diag, phi_le_one_twentieth_diag]

private theorem d1_upper_diag : params.d1 ≤ (33 / 25 : ℝ) := by
  have h := PartB.d1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem eta_lower_diag : (4 / 5 : ℝ) ≤ eta := by
  dsimp [eta, T]
  nlinarith [Real.pi_gt_three, theta_upper_diag]

private theorem phaseB4_coeff_nonpos_diag {r : ℝ} (hr : eta ≤ r) :
    params.d1 - r / 2 - 1 ≤ 0 := by
  nlinarith [d1_upper_diag, eta_lower_diag]

private theorem late_cos_sub_sin_nonpos {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) (hr : r ∈ Icc eta T) :
    Real.cos (r - t) - Real.sin (r - t) ≤ 0 := by
  have hhalf : T / 2 ≤ r - t := by
    nlinarith [halfT_le_eta_sub_phi, ht.2, hr.1]
  have hdeltaT : r - t ≤ T := by linarith [hr.2, ht.1]
  have hlo : -(Real.pi / 2) ≤ T - (r - t) := by
    dsimp [T] at hdeltaT ⊢
    nlinarith [Real.pi_pos]
  have hhi : r - t ≤ Real.pi / 2 := by simpa [T] using hdeltaT
  have horder : T - (r - t) ≤ r - t := by linarith
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two hlo hhi horder
  have htrig : Real.sin (T - (r - t)) = Real.cos (r - t) := by
    change Real.sin (Real.pi / 2 - (r - t)) = Real.cos (r - t)
    exact Real.sin_pi_div_two_sub (r - t)
  rw [htrig] at hs
  linarith

private theorem dot_fixed_hasDerivAt_diag
    {f : ℝ → Point} {df w : Point} {r : ℝ}
    (h : HasDerivAt f df r) :
    HasDerivAt (fun s => dot (f s) w) (dot df w) r := by
  have h1 := HasDerivAt.const_mul w.1 h.fst
  have h2 := HasDerivAt.const_mul w.2 h.snd
  simpa [dot, mul_comm] using h1.fun_add h2

private theorem phaseB4_diag_monotone (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) params.phi) :
    MonotoneOn (fun r => dot (diagPhaseB4 r) (u t + v t)) (Icc eta tau) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun r => dot ((params.d1 - r / 2 - 1) • v r) (u t + v t))
    (convex_Icc eta tau) ?_ ?_ ?_
  · intro r hr
    exact (dot_fixed_hasDerivAt_diag (w := u t + v t)
      (diagPhaseB4_hasDerivAt r)).continuousAt.continuousWithinAt
  · intro r hr
    exact (dot_fixed_hasDerivAt_diag (w := u t + v t)
      (diagPhaseB4_hasDerivAt r)).hasDerivWithinAt
  · intro r hr
    have hi : r ∈ Ioo eta tau := by simpa only [interior_Icc] using hr
    have hcoef := phaseB4_coeff_nonpos_diag hi.1.le
    have htrig := late_cos_sub_sin_nonpos ht
      ⟨hi.1.le, le_trans hi.2.le tau_lt_T.le⟩
    have heq :
        dot ((params.d1 - r / 2 - 1) • v r) (u t + v t) =
          (params.d1 - r / 2 - 1) *
            (Real.cos (r - t) - Real.sin (r - t)) := by
      simp [dot, u, v, Real.cos_sub, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonneg_of_nonpos_of_nonpos hcoef htrig

private theorem phaseB5_diag_monotone (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) params.phi) :
    MonotoneOn (fun r => dot (diagPhaseB5 r) (u t + v t)) (Icc tau T) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun r => dot ((-(1 / 2 : ℝ)) • v r) (u t + v t))
    (convex_Icc tau T) ?_ ?_ ?_
  · intro r hr
    exact (dot_fixed_hasDerivAt_diag (w := u t + v t)
      (diagPhaseB5_hasDerivAt r)).continuousAt.continuousWithinAt
  · intro r hr
    exact (dot_fixed_hasDerivAt_diag (w := u t + v t)
      (diagPhaseB5_hasDerivAt r)).hasDerivWithinAt
  · intro r hr
    have hi : r ∈ Ioo tau T := by simpa only [interior_Icc] using hr
    have htrig := late_cos_sub_sin_nonpos ht
      ⟨le_trans eta_lt_tau.le hi.1.le, hi.2.le⟩
    have heq : dot ((-(1 / 2 : ℝ)) • v r) (u t + v t) =
        (-(1 / 2 : ℝ)) *
          (Real.cos (r - t) - Real.sin (r - t)) := by
      simp [dot, u, v, Real.cos_sub, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonneg_of_nonpos_of_nonpos (by norm_num) htrig

private theorem B_diag_mono_from_eta {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) (hr : r ∈ Icc eta T) :
    dot (B eta) (u t + v t) ≤ dot (B r) (u t + v t) := by
  by_cases hrtau : r ≤ tau
  · have hm := phaseB4_diag_monotone t ht
    have heta : eta ∈ Icc eta tau := ⟨le_rfl, eta_lt_tau.le⟩
    have hrr : r ∈ Icc eta tau := ⟨hr.1, hrtau⟩
    have h := hm heta hrr hr.1
    change dot (diagPhaseB4 eta) (u t + v t) ≤
      dot (diagPhaseB4 r) (u t + v t) at h
    rw [diagPhaseB4_eq_B heta, diagPhaseB4_eq_B hrr] at h
    exact h
  · have htaur : tau ≤ r := le_of_lt (lt_of_not_ge hrtau)
    have heta : eta ∈ Icc eta tau := ⟨le_rfl, eta_lt_tau.le⟩
    have htau4 : tau ∈ Icc eta tau := ⟨eta_lt_tau.le, le_rfl⟩
    have htau5 : tau ∈ Icc tau T := ⟨le_rfl, tau_lt_T.le⟩
    have hrr : r ∈ Icc tau T := ⟨htaur, hr.2⟩
    have h4 := phaseB4_diag_monotone t ht heta htau4 eta_lt_tau.le
    have h5 := phaseB5_diag_monotone t ht htau5 hrr htaur
    change dot (diagPhaseB4 eta) (u t + v t) ≤
      dot (diagPhaseB4 tau) (u t + v t) at h4
    change dot (diagPhaseB5 tau) (u t + v t) ≤
      dot (diagPhaseB5 r) (u t + v t) at h5
    rw [diagPhaseB4_eq_B heta, diagPhaseB4_eq_B htau4] at h4
    rw [diagPhaseB5_eq_B htau5, diagPhaseB5_eq_B hrr] at h5
    exact le_trans h4 h5

theorem B_early_diagonal_nonneg {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) (hr : r ∈ Icc eta T) :
    0 ≤ dot (B r - Romik.path params t) (u t + v t) := by
  have hstart := early_endpoint_diagonal_nonneg ht
  have hmono := B_diag_mono_from_eta ht hr
  rw [B_eta_eq_path_phi] at hmono
  unfold dot at hstart hmono ⊢
  dsimp at hstart hmono ⊢
  linarith

theorem B_early_boundary_outside {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) (hr : r ∈ Icc eta T) :
    0 ≤ dot (B r - Romik.path params t) (u t) ∨
      0 ≤ dot (B r - Romik.path params t) (v t) := by
  have hdiag := B_early_diagonal_nonneg ht hr
  by_contra h
  push Not at h
  have hadd :
      dot (B r - Romik.path params t) (u t + v t) =
        dot (B r - Romik.path params t) (u t) +
          dot (B r - Romik.path params t) (v t) := by
    unfold dot
    dsimp [u, v]
    ring
  rw [hadd] at hdiag
  linarith

private theorem T_le_pi_diag : T ≤ Real.pi := by
  dsimp [T]
  nlinarith [Real.pi_pos]

private theorem contact_u_mono_after
    {F : ℝ → Point} {c : ℝ → ℝ} {a b t : ℝ}
    (hder : ∀ q, HasDerivAt F ((c q) • v q) q)
    (hc : ∀ q ∈ Ioo a b, c q ≤ 0)
    (ht0 : 0 ≤ t) (hta : t ≤ a) (hbT : b ≤ T) :
    MonotoneOn (fun q => dot (F q) (u t)) (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun q => dot ((c q) • v q) (u t))
    (convex_Icc a b) ?_ ?_ ?_
  · intro q hq
    exact (dot_fixed_hasDerivAt_diag (w := u t) (hder q)).continuousAt.continuousWithinAt
  · intro q hq
    exact (dot_fixed_hasDerivAt_diag (w := u t) (hder q)).hasDerivWithinAt
  · intro q hq
    have hi : q ∈ Ioo a b := by simpa only [interior_Icc] using hq
    have hsin : Real.sin (t - q) ≤ 0 := by
      apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
      · linarith [hta, hi.1]
      · have hqT : q ≤ T := le_trans hi.2.le hbT
        have : q - t ≤ T := by linarith
        nlinarith [T_le_pi_diag]
    have heq : dot ((c q) • v q) (u t) = c q * Real.sin (t - q) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonneg_of_nonpos_of_nonpos (hc q hi) hsin

private theorem contact_u_anti_before
    {F : ℝ → Point} {c : ℝ → ℝ} {a b t : ℝ}
    (hder : ∀ q, HasDerivAt F ((c q) • v q) q)
    (hc : ∀ q ∈ Ioo a b, c q ≤ 0)
    (ha0 : 0 ≤ a) (hbt : b ≤ t) (htT : t ≤ T) :
    AntitoneOn (fun q => dot (F q) (u t)) (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun q => dot ((c q) • v q) (u t))
    (convex_Icc a b) ?_ ?_ ?_
  · intro q hq
    exact (dot_fixed_hasDerivAt_diag (w := u t) (hder q)).continuousAt.continuousWithinAt
  · intro q hq
    exact (dot_fixed_hasDerivAt_diag (w := u t) (hder q)).hasDerivWithinAt
  · intro q hq
    have hi : q ∈ Ioo a b := by simpa only [interior_Icc] using hq
    have hsin : 0 ≤ Real.sin (t - q) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · linarith [hi.2, hbt]
      · have hq0 : 0 ≤ q := le_trans ha0 hi.1.le
        have : t - q ≤ T := by linarith
        exact le_trans this T_le_pi_diag
    have heq : dot ((c q) • v q) (u t) = c q * Real.sin (t - q) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonpos_of_nonpos_of_nonneg (hc q hi) hsin

private theorem phase4_u_mono_after {a b t : ℝ}
    (ha : eta ≤ a) (hb : b ≤ tau) (ht0 : 0 ≤ t) (hta : t ≤ a) :
    MonotoneOn (fun q => dot (diagPhaseB4 q) (u t)) (Icc a b) := by
  exact contact_u_mono_after
    (F := diagPhaseB4) (c := fun q => params.d1 - q / 2 - 1)
    diagPhaseB4_hasDerivAt
    (by intro q hq; exact phaseB4_coeff_nonpos_diag (le_trans ha hq.1.le))
    ht0 hta (le_trans hb tau_lt_T.le)

private theorem phase4_u_anti_before {a b t : ℝ}
    (ha : eta ≤ a) (hbt : b ≤ t) (htT : t ≤ T) :
    AntitoneOn (fun q => dot (diagPhaseB4 q) (u t)) (Icc a b) := by
  exact contact_u_anti_before
    (F := diagPhaseB4) (c := fun q => params.d1 - q / 2 - 1)
    diagPhaseB4_hasDerivAt
    (by intro q hq; exact phaseB4_coeff_nonpos_diag (le_trans ha hq.1.le))
    (le_trans (by norm_num : (0 : ℝ) ≤ 4 / 5)
      (le_trans eta_lower_diag ha)) hbt htT

private theorem phase5_u_mono_after {a b t : ℝ}
    (hb : b ≤ T) (ht0 : 0 ≤ t) (hta : t ≤ a) :
    MonotoneOn (fun q => dot (diagPhaseB5 q) (u t)) (Icc a b) := by
  exact contact_u_mono_after
    (F := diagPhaseB5) (c := fun _ => (-(1 / 2 : ℝ)))
    diagPhaseB5_hasDerivAt (by intro q hq; norm_num)
    ht0 hta hb

private theorem phase5_u_anti_before {a b t : ℝ}
    (ha : tau ≤ a) (hbt : b ≤ t) (htT : t ≤ T) :
    AntitoneOn (fun q => dot (diagPhaseB5 q) (u t)) (Icc a b) := by
  exact contact_u_anti_before
    (F := diagPhaseB5) (c := fun _ => (-(1 / 2 : ℝ)))
    diagPhaseB5_hasDerivAt (by intro q hq; norm_num)
    (le_trans (by norm_num : (0 : ℝ) ≤ 4 / 5)
      (le_trans eta_lower_diag (le_trans eta_lt_tau.le ha))) hbt htT

private theorem B_u_ge_eta {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) eta) (hr : r ∈ Icc eta T) :
    dot (B eta) (u t) ≤ dot (B r) (u t) := by
  by_cases hrtau : r ≤ tau
  · have heta : eta ∈ Icc eta r := ⟨le_rfl, hr.1⟩
    have hrr : r ∈ Icc eta r := ⟨hr.1, le_rfl⟩
    have hm := phase4_u_mono_after (a := eta) (b := r) (t := t)
      le_rfl hrtau ht.1 ht.2
    have h := hm heta hrr hr.1
    change dot (diagPhaseB4 eta) (u t) ≤ dot (diagPhaseB4 r) (u t) at h
    rw [diagPhaseB4_eq_B ⟨le_rfl, eta_lt_tau.le⟩,
      diagPhaseB4_eq_B ⟨hr.1, hrtau⟩] at h
    exact h
  · have htaur : tau ≤ r := le_of_lt (lt_of_not_ge hrtau)
    have heta4 : eta ∈ Icc eta tau := ⟨le_rfl, eta_lt_tau.le⟩
    have htau4 : tau ∈ Icc eta tau := ⟨eta_lt_tau.le, le_rfl⟩
    have htau5 : tau ∈ Icc tau r := ⟨le_rfl, htaur⟩
    have hrr5 : r ∈ Icc tau r := ⟨htaur, le_rfl⟩
    have h4 := (phase4_u_mono_after (a := eta) (b := tau) (t := t)
      le_rfl le_rfl ht.1 ht.2)
      heta4 htau4 eta_lt_tau.le
    have h5 := (phase5_u_mono_after (a := tau) (b := r) (t := t)
      hr.2 ht.1 (le_trans ht.2 eta_lt_tau.le))
      htau5 hrr5 htaur
    change dot (diagPhaseB4 eta) (u t) ≤ dot (diagPhaseB4 tau) (u t) at h4
    change dot (diagPhaseB5 tau) (u t) ≤ dot (diagPhaseB5 r) (u t) at h5
    rw [diagPhaseB4_eq_B heta4, diagPhaseB4_eq_B htau4] at h4
    rw [diagPhaseB5_eq_B ⟨le_rfl, tau_lt_T.le⟩,
      diagPhaseB5_eq_B ⟨htaur, hr.2⟩] at h5
    exact le_trans h4 h5

private theorem B_u_global_min {t r : ℝ}
    (ht : t ∈ Icc eta T) (hr : r ∈ Icc eta T) :
    dot (B t) (u t) ≤ dot (B r) (u t) := by
  have ht0 : 0 ≤ t := by nlinarith [eta_lower_diag, ht.1]
  by_cases httau : t ≤ tau
  · have ht4 : t ∈ Icc eta tau := ⟨ht.1, httau⟩
    by_cases hrtau : r ≤ tau
    · have hr4 : r ∈ Icc eta tau := ⟨hr.1, hrtau⟩
      by_cases hrt : r ≤ t
      · have hrr : r ∈ Icc r t := ⟨le_rfl, hrt⟩
        have htt : t ∈ Icc r t := ⟨hrt, le_rfl⟩
        have ha := phase4_u_anti_before (a := r) (b := t) (t := t)
          hr.1 le_rfl ht.2
        have h := ha hrr htt hrt
        change dot (diagPhaseB4 t) (u t) ≤ dot (diagPhaseB4 r) (u t) at h
        rw [diagPhaseB4_eq_B hr4, diagPhaseB4_eq_B ht4] at h
        exact h
      · have htr : t ≤ r := le_of_lt (lt_of_not_ge hrt)
        have htt : t ∈ Icc t r := ⟨le_rfl, htr⟩
        have hrr : r ∈ Icc t r := ⟨htr, le_rfl⟩
        have hm := phase4_u_mono_after (a := t) (b := r) (t := t)
          ht.1 hrtau ht0 le_rfl
        have h := hm htt hrr htr
        change dot (diagPhaseB4 t) (u t) ≤ dot (diagPhaseB4 r) (u t) at h
        rw [diagPhaseB4_eq_B ht4, diagPhaseB4_eq_B hr4] at h
        exact h
    · have htaur : tau ≤ r := le_of_lt (lt_of_not_ge hrtau)
      have htt4 : t ∈ Icc t tau := ⟨le_rfl, httau⟩
      have htau4' : tau ∈ Icc t tau := ⟨httau, le_rfl⟩
      have h4 := (phase4_u_mono_after (a := t) (b := tau) (t := t)
        ht.1 le_rfl ht0 le_rfl)
        htt4 htau4' httau
      have htau5' : tau ∈ Icc tau r := ⟨le_rfl, htaur⟩
      have hrr5 : r ∈ Icc tau r := ⟨htaur, le_rfl⟩
      have h5 := (phase5_u_mono_after (a := tau) (b := r) (t := t)
        hr.2 ht0 httau)
        htau5' hrr5 htaur
      change dot (diagPhaseB4 t) (u t) ≤ dot (diagPhaseB4 tau) (u t) at h4
      change dot (diagPhaseB5 tau) (u t) ≤ dot (diagPhaseB5 r) (u t) at h5
      rw [diagPhaseB4_eq_B ht4,
        diagPhaseB4_eq_B ⟨eta_lt_tau.le, le_rfl⟩] at h4
      rw [diagPhaseB5_eq_B ⟨le_rfl, tau_lt_T.le⟩,
        diagPhaseB5_eq_B ⟨htaur, hr.2⟩] at h5
      exact le_trans h4 h5
  · have htaut : tau ≤ t := le_of_lt (lt_of_not_ge httau)
    have ht5 : t ∈ Icc tau T := ⟨htaut, ht.2⟩
    by_cases hrtau : r ≤ tau
    · have hr4 : r ∈ Icc eta tau := ⟨hr.1, hrtau⟩
      have hrr4 : r ∈ Icc r tau := ⟨le_rfl, hrtau⟩
      have htau4' : tau ∈ Icc r tau := ⟨hrtau, le_rfl⟩
      have h4 := (phase4_u_anti_before (a := r) (b := tau) (t := t)
        hr.1 htaut ht.2) hrr4 htau4' hrtau
      have htau5' : tau ∈ Icc tau t := ⟨le_rfl, htaut⟩
      have htt5 : t ∈ Icc tau t := ⟨htaut, le_rfl⟩
      have h5 := (phase5_u_anti_before (a := tau) (b := t) (t := t)
        le_rfl le_rfl ht.2) htau5' htt5 htaut
      change dot (diagPhaseB4 tau) (u t) ≤ dot (diagPhaseB4 r) (u t) at h4
      change dot (diagPhaseB5 t) (u t) ≤ dot (diagPhaseB5 tau) (u t) at h5
      rw [diagPhaseB4_eq_B hr4,
        diagPhaseB4_eq_B ⟨eta_lt_tau.le, le_rfl⟩] at h4
      rw [diagPhaseB5_eq_B ⟨le_rfl, tau_lt_T.le⟩,
        diagPhaseB5_eq_B ht5] at h5
      exact le_trans h5 h4
    · have htaur : tau ≤ r := le_of_lt (lt_of_not_ge hrtau)
      have hr5 : r ∈ Icc tau T := ⟨htaur, hr.2⟩
      by_cases hrt : r ≤ t
      · have hrr : r ∈ Icc r t := ⟨le_rfl, hrt⟩
        have htt : t ∈ Icc r t := ⟨hrt, le_rfl⟩
        have ha := phase5_u_anti_before (a := r) (b := t) (t := t)
          htaur le_rfl ht.2
        have h := ha hrr htt hrt
        change dot (diagPhaseB5 t) (u t) ≤ dot (diagPhaseB5 r) (u t) at h
        rw [diagPhaseB5_eq_B hr5, diagPhaseB5_eq_B ht5] at h
        exact h
      · have htr : t ≤ r := le_of_lt (lt_of_not_ge hrt)
        have htt : t ∈ Icc t r := ⟨le_rfl, htr⟩
        have hrr : r ∈ Icc t r := ⟨htr, le_rfl⟩
        have hm := phase5_u_mono_after (a := t) (b := r) (t := t)
          hr.2 ht0 le_rfl
        have h := hm htt hrr htr
        change dot (diagPhaseB5 t) (u t) ≤ dot (diagPhaseB5 r) (u t) at h
        rw [diagPhaseB5_eq_B ht5, diagPhaseB5_eq_B hr5] at h
        exact h

theorem B_late_u_nonneg {t r : ℝ}
    (ht : t ∈ Icc params.phi T) (hr : r ∈ Icc eta T) :
    0 ≤ dot (B r - Romik.path params t) (u t) := by
  by_cases hteta : t ≤ eta
  · have hstart := U_phi_nonneg ht
    have hmono := B_u_ge_eta
      (show t ∈ Icc (0 : ℝ) eta from ⟨le_trans phi_pos.le ht.1, hteta⟩) hr
    rw [B_eta_eq_path_phi] at hmono
    unfold Stage2.UValue at hstart
    unfold dot at hstart hmono ⊢
    dsimp at hstart hmono ⊢
    linarith
  · have heta : eta ≤ t := le_of_lt (lt_of_not_ge hteta)
    have hmin := B_u_global_min (show t ∈ Icc eta T from ⟨heta, ht.2⟩) hr
    have hcontact := B_inner_u_identity t
    unfold dot at hmin hcontact ⊢
    dsimp at hmin hcontact ⊢
    linarith

theorem B_boundary_outside {t r : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) (hr : r ∈ Icc eta T) :
    0 ≤ dot (B r - Romik.path params t) (u t) ∨
      0 ≤ dot (B r - Romik.path params t) (v t) := by
  by_cases htphi : t ≤ params.phi
  · exact B_early_boundary_outside ⟨ht.1.le, htphi⟩ hr
  · exact Or.inl (B_late_u_nonneg
      ⟨le_of_lt (lt_of_not_ge htphi), ht.2.le⟩ hr)

private theorem phase1_beta_upper {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    (Romik.alphaBeta1 params s).2 ≤ (3 / 2 : ℝ) := by
  have hpi : s ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hcosUpper := Real.cos_le_one s
  have hcos0 : 0 ≤ Real.cos s := by
    have hlow := Real.one_sub_sq_div_two_le_cos (x := s)
    nlinarith [hlow, sq_nonneg s, mul_nonneg hs0 (sub_nonneg.mpr hs20)]
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  have hmul : 2 * params.a1 * Real.cos s ≤ (5 / 2 : ℝ) := by
    have hc := mul_le_mul_of_nonneg_left hcosUpper
      (show 0 ≤ 2 * params.a1 by nlinarith [a1_lower_diag])
    have ha : 2 * params.a1 ≤ (5 / 2 : ℝ) := by nlinarith [a1_upper_diag]
    nlinarith
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith

private theorem path1_fst_antitone :
    AntitoneOn (fun s => (Romik.path1 params s).1)
      (Icc (0 : ℝ) params.phi) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun s => (Romik.rot s (Romik.alphaBeta1 params s)).1)
    (convex_Icc (0 : ℝ) params.phi) ?_ ?_ ?_
  · intro s hs
    have h := dot_fixed_hasDerivAt_diag (w := ((1 : ℝ), 0))
      (path1_hasDerivAt_public s)
    simpa [dot] using h.continuousAt.continuousWithinAt
  · intro s hs
    have h := dot_fixed_hasDerivAt_diag (w := ((1 : ℝ), 0))
      (path1_hasDerivAt_public s)
    simpa [dot] using h.hasDerivWithinAt
  · intro s hs
    have hi : s ∈ Ioo (0 : ℝ) params.phi := by
      simpa only [interior_Icc] using hs
    have hs20 := le_trans hi.2.le phi_le_one_twentieth_diag
    have ha := phase1_alpha_nonpos_diag hi.1.le hs20
    have hb := phase1_beta_lower hi.1.le hs20
    have hsin : 0 ≤ Real.sin s := by
      exact Real.sin_nonneg_of_nonneg_of_le_pi hi.1.le
        (by nlinarith [Real.pi_gt_three, hs20])
    have hcos : 0 ≤ Real.cos s := by
      have hlow := Real.one_sub_sq_div_two_le_cos (x := s)
      nlinarith [hlow, sq_nonneg s,
        mul_nonneg hi.1.le (sub_nonneg.mpr hs20)]
    dsimp [Romik.rot]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg ha hcos,
      mul_nonneg (show 0 ≤ (Romik.alphaBeta1 params s).2 by linarith) hsin]

private theorem path1_snd_slope_upper :
    AntitoneOn (fun s => (Romik.path1 params s).2 - (3 / 2 : ℝ) * s)
      (Icc (0 : ℝ) params.phi) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun s => (Romik.rot s (Romik.alphaBeta1 params s)).2 - 3 / 2)
    (convex_Icc (0 : ℝ) params.phi) ?_ ?_ ?_
  · intro s hs
    have hp := dot_fixed_hasDerivAt_diag (w := ((0 : ℝ), 1))
      (path1_hasDerivAt_public s)
    have h := hp.fun_sub
      (HasDerivAt.const_mul (3 / 2 : ℝ) (hasDerivAt_id s))
    simpa [dot] using h.continuousAt.continuousWithinAt
  · intro s hs
    have hp := dot_fixed_hasDerivAt_diag (w := ((0 : ℝ), 1))
      (path1_hasDerivAt_public s)
    have h := hp.fun_sub
      (HasDerivAt.const_mul (3 / 2 : ℝ) (hasDerivAt_id s))
    simpa [dot] using h.hasDerivWithinAt
  · intro s hs
    have hi : s ∈ Ioo (0 : ℝ) params.phi := by
      simpa only [interior_Icc] using hs
    have hs20 := le_trans hi.2.le phi_le_one_twentieth_diag
    have ha := phase1_alpha_nonpos_diag hi.1.le hs20
    have hbLo := phase1_beta_lower hi.1.le hs20
    have hbHi := phase1_beta_upper hi.1.le hs20
    have hsin : 0 ≤ Real.sin s := by
      exact Real.sin_nonneg_of_nonneg_of_le_pi hi.1.le
        (by nlinarith [Real.pi_gt_three, hs20])
    have hcos0 : 0 ≤ Real.cos s := by
      have hlow := Real.one_sub_sq_div_two_le_cos (x := s)
      nlinarith [hlow, sq_nonneg s,
        mul_nonneg hi.1.le (sub_nonneg.mpr hs20)]
    have hcos1 := Real.cos_le_one s
    dsimp [Romik.rot]
    have haSin := mul_nonpos_of_nonpos_of_nonneg ha hsin
    have hbCos : (Romik.alphaBeta1 params s).2 * Real.cos s ≤ 3 / 2 := by
      have h1 := mul_le_mul_of_nonneg_right hbHi hcos0
      have h2 := mul_le_mul_of_nonneg_left hcos1
        (show 0 ≤ (3 / 2 : ℝ) by norm_num)
      nlinarith
    nlinarith

private theorem phase1_path_x_nonpos {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) :
    (Romik.path params t).1 ≤ 0 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) params.phi := ⟨le_rfl, phi_pos.le⟩
  have h := path1_fst_antitone h0 ht ht.1
  have hp0 := congrArg Prod.fst pathZero
  have hpt : Romik.path params t = Romik.path1 params t := by
    simp [Romik.path, ht.2]
  have hzero : Romik.path params 0 = Romik.path1 params 0 := by
    simp [Romik.path, phi_pos.le]
  change (Romik.path1 params t).1 ≤ (Romik.path1 params 0).1 at h
  rw [← congrArg Prod.fst hzero, ← congrArg Prod.fst hpt] at h
  simpa [hp0] using h

private theorem phase1_path_y_upper {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) :
    (Romik.path params t).2 ≤ (3 / 40 : ℝ) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) params.phi := ⟨le_rfl, phi_pos.le⟩
  have h := path1_snd_slope_upper h0 ht ht.1
  have hp0 := congrArg Prod.snd pathZero
  have hpt : Romik.path params t = Romik.path1 params t := by
    simp [Romik.path, ht.2]
  have hzero : Romik.path params 0 = Romik.path1 params 0 := by
    simp [Romik.path, phi_pos.le]
  change (Romik.path1 params t).2 - 3 / 2 * t ≤
    (Romik.path1 params 0).2 - 3 / 2 * 0 at h
  rw [← congrArg Prod.snd hzero, ← congrArg Prod.snd hpt] at h
  nlinarith [phi_le_one_twentieth_diag, ht.2, hp0]

private theorem B_T_x_formula : (B T).1 = params.k51 + params.e1 := by
  have hetaRaw : ¬ T ≤ Real.pi / 2 - params.theta := by
    exact not_le.mpr (by simpa [eta, T] using eta_lt_T)
  have htauRaw : ¬ T ≤ Real.pi / 2 - params.phi := by
    exact not_le.mpr (by simpa [tau, T] using tau_lt_T)
  have hpath : Romik.path params T = Romik.path5 params T := by
    simp only [Romik.path, ite_eq_right (not_le.mpr phi_lt_T),
      ite_eq_right (not_le.mpr theta_lt_T), ite_eq_right hetaRaw, ite_eq_right htauRaw]
  have halpha : alpha T = (Romik.alphaBeta5 params T).1 := by
    simp only [alpha, alphaBetaAt, ite_eq_right (not_le.mpr phi_lt_T),
      ite_eq_right (not_le.mpr theta_lt_T), ite_eq_right (not_le.mpr eta_lt_T),
      ite_eq_right (not_le.mpr tau_lt_T)]
  rw [B, hpath, halpha]
  simp [Romik.path5, Romik.alphaBeta5, Romik.rot, Romik.addK,
    v, T]
  ring

private theorem B_T_x_lower : (19 / 100 : ℝ) ≤ (B T).1 := by
  have hk := PartB.k51_contains.1
  have he := PartB.e1_contains.1
  rw [B_T_x_formula]
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at hk he ⊢
  linarith

theorem B_T_u_nonneg_early {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) :
    0 ≤ dot (B T - Romik.path params t) (u t) := by
  have hx := phase1_path_x_nonpos ht
  have hy := phase1_path_y_upper ht
  have hBTx := B_T_x_lower
  have hBTy := B_T_y_zero
  have ht20 := le_trans ht.2 phi_le_one_twentieth_diag
  have hsin0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi
    ht.1 (by nlinarith [Real.pi_gt_three, ht20])
  have hsin1 := Real.sin_le ht.1
  have hcosLower : (799 / 800 : ℝ) ≤ Real.cos t := by
    have h := Real.one_sub_sq_div_two_le_cos (x := t)
    nlinarith [h, sq_nonneg t, mul_nonneg ht.1 (sub_nonneg.mpr ht20)]
  have hcos0 : 0 ≤ Real.cos t := by linarith
  have hdx : (19 / 100 : ℝ) ≤ (B T).1 - (Romik.path params t).1 := by
    linarith
  have hdxCos : (19 / 100 : ℝ) * (799 / 800) ≤
      ((B T).1 - (Romik.path params t).1) * Real.cos t := by
    have h1 := mul_le_mul_of_nonneg_right hdx hcos0
    have h2 := mul_le_mul_of_nonneg_left hcosLower
      (show 0 ≤ (19 / 100 : ℝ) by norm_num)
    exact le_trans h2 h1
  have hySin : (Romik.path params t).2 * Real.sin t ≤
      (3 / 40 : ℝ) * (1 / 20) := by
    have h1 := mul_le_mul_of_nonneg_right hy hsin0
    have h2 : (3 / 40 : ℝ) * Real.sin t ≤ (3 / 40) * (1 / 20) := by
      apply mul_le_mul_of_nonneg_left
      · exact le_trans hsin1 ht20
      · norm_num
    exact le_trans h1 h2
  unfold dot
  dsimp [u]
  rw [hBTy]
  nlinarith

theorem B_T_u_nonneg {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    0 ≤ dot (B T - Romik.path params t) (u t) := by
  by_cases htphi : t ≤ params.phi
  · exact B_T_u_nonneg_early ⟨ht.1.le, htphi⟩
  · exact B_late_u_nonneg
      ⟨le_of_lt (lt_of_not_ge htphi), ht.2.le⟩
      ⟨eta_lt_T.le, le_rfl⟩

/-! ## Exact reflected forms

Only the early half of the coefficient reflection is needed here.  Its image
under `r ↦ T-r` is exactly the late `B` interval.  Keeping the endpoint cases
explicit avoids relying on definitional reduction across the four switching
equalities of `alphaBetaAt`.
-/

private theorem alpha_reflect_beta_early {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) params.theta) :
    alpha (T - r) = -beta r := by
  by_cases hrphi : r < params.phi
  · have hsphi : ¬ T - r ≤ params.phi := by
      have hphiTau := lt_trans phi_lt_eta eta_lt_tau
      exact not_le.mpr (by
        dsimp [T, tau] at hphiTau ⊢
        nlinarith [hrphi])
    have hstheta : ¬ T - r ≤ params.theta := by
      exact not_le.mpr (lt_trans theta_lt_tau (by dsimp [tau]; linarith))
    have hseta : ¬ T - r ≤ eta := by
      exact not_le.mpr (by dsimp [eta]; linarith [hrphi, phi_lt_theta])
    have hstau : ¬ T - r ≤ tau := by
      exact not_le.mpr (by dsimp [tau]; linarith)
    have href := congrArg Prod.fst (alphaBeta5_reflect1_direct r)
    simpa [alpha, beta, alphaBetaAt, noHiddenReflAB, hrphi.le,
      hsphi, hstheta, hseta, hstau] using href
  · have hphir : params.phi ≤ r := le_of_not_gt hrphi
    by_cases hre : r = params.phi
    · subst r
      have href := congrArg Prod.fst
        (alphaBeta4_reflect2_direct params.phi)
      have hmatch := congrArg Prod.snd alphaBeta_match12_direct
      have hTphi : T - params.phi = tau := by
        rfl
      rw [hTphi] at href
      rw [hTphi]
      simp only [alpha, beta, alphaBetaAt,
        ite_eq_right (not_le.mpr (lt_trans phi_lt_eta eta_lt_tau)),
        ite_eq_right (not_le.mpr theta_lt_tau),
        ite_eq_right (not_le.mpr eta_lt_tau),
        ite_eq_left le_rfl]
      dsimp [noHiddenReflAB] at href
      rw [hmatch]
      exact href
    · have hphir' : params.phi < r := lt_of_le_of_ne hphir (Ne.symm hre)
      by_cases hretheta : r = params.theta
      · subst r
        have href := congrArg Prod.fst
          (alphaBeta3_reflect_direct params.theta)
        have hmatch := congrArg Prod.snd alphaBeta_match23_direct
        simp only [alpha, beta, alphaBetaAt,
          ite_eq_right (not_le.mpr phi_lt_theta), show T - params.theta = eta by rfl,
          ite_eq_right (not_le.mpr phi_lt_eta),
          ite_eq_right (not_le.mpr theta_lt_eta), ite_eq_left le_rfl]
        dsimp [eta] at href ⊢
        dsimp [noHiddenReflAB] at href
        rw [hmatch]
        exact href
      · have hrtheta : r < params.theta :=
          lt_of_le_of_ne hr.2 hretheta
        have hsphi : ¬ T - r ≤ params.phi := by
          have hthetaTau := theta_lt_tau
          exact not_le.mpr (by
            dsimp [T, tau] at hthetaTau ⊢
            linarith [hrtheta])
        have hstheta : ¬ T - r ≤ params.theta := by
          have hthetaEta := theta_lt_eta
          exact not_le.mpr (by
            dsimp [T, eta] at hthetaEta ⊢
            linarith [hrtheta])
        have hseta : ¬ T - r ≤ eta := by
          exact not_le.mpr (by dsimp [eta]; linarith)
        have hstau : T - r ≤ tau := by
          dsimp [tau]
          linarith
        have href := congrArg Prod.fst (alphaBeta4_reflect2_direct r)
        simpa [alpha, beta, alphaBetaAt, noHiddenReflAB,
          not_le.mpr hphir', hrtheta.le,
          hsphi, hstheta, hseta, hstau] using href

/-- The late `B` contact arc is the exact horizontal reflection of the early
`D` contact arc. -/
theorem B_reflect_D {r : ℝ} (hr : r ∈ Icc (0 : ℝ) params.theta) :
    B (T - r) = noHiddenHReflect (D r) := by
  have hp := path_reflect_noHidden
    (show r ∈ Icc (0 : ℝ) T from
      ⟨hr.1, le_trans hr.2 theta_lt_T.le⟩)
  have ha := alpha_reflect_beta_early hr
  rw [B, D, hp, ha]
  apply Prod.ext
  · dsimp [noHiddenHReflect, u, v, T]
    rw [Real.sin_pi_div_two_sub]
    ring
  · dsimp [noHiddenHReflect, u, v, T]
    rw [Real.cos_pi_div_two_sub]
    ring

private theorem B_reflect_u_dot_eq_D_v {r t : ℝ}
    (hr : r ∈ Icc (0 : ℝ) params.theta)
    (ht : t ∈ Icc (0 : ℝ) T) :
    dot (B (T - r) - Romik.path params (T - t)) (u (T - t)) =
      dot (D r - Romik.path params t) (v t) := by
  rw [B_reflect_D hr, path_reflect_noHidden ht]
  dsimp [dot, noHiddenHReflect, u, v, T]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

private theorem B_reflect_v_dot_eq_D_u {r t : ℝ}
    (hr : r ∈ Icc (0 : ℝ) params.theta)
    (ht : t ∈ Icc (0 : ℝ) T) :
    dot (B (T - r) - Romik.path params (T - t)) (v (T - t)) =
      dot (D r - Romik.path params t) (u t) := by
  rw [B_reflect_D hr, path_reflect_noHidden ht]
  dsimp [dot, noHiddenHReflect, u, v, T]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

/-- Every point of the early `D` contact arc lies outside at least one of the
two moving inner walls. -/
theorem D_boundary_outside {t r : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hr : r ∈ Icc (0 : ℝ) params.theta) :
    0 ≤ dot (D r - Romik.path params t) (u t) ∨
      0 ≤ dot (D r - Romik.path params t) (v t) := by
  have htRef : T - t ∈ Ioo (0 : ℝ) T := by
    have ht0 := ht.1
    have htT := ht.2
    constructor <;> dsimp [T] at ht0 htT ⊢ <;> linarith
  have hrRef : T - r ∈ Icc eta T := by
    constructor
    · dsimp [eta]
      linarith [hr.2]
    · linarith [hr.1]
  have htClosed : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  rcases B_boundary_outside htRef hrRef with hu | hv
  · right
    rw [B_reflect_u_dot_eq_D_v hr htClosed] at hu
    exact hu
  · left
    rw [B_reflect_v_dot_eq_D_u hr htClosed] at hv
    exact hv

/-- Reflected endpoint separator used for the strict lower horizontal range of
the niche. -/
theorem D_zero_v_nonneg {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    0 ≤ dot (D 0 - Romik.path params t) (v t) := by
  have htRef : T - t ∈ Ioo (0 : ℝ) T := by
    have ht0 := ht.1
    have htT := ht.2
    constructor <;> dsimp [T] at ht0 htT ⊢ <;> linarith
  have h := B_T_u_nonneg htRef
  have htransport := B_reflect_u_dot_eq_D_v
    (t := t) (r := 0)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) params.theta from
      ⟨le_rfl, theta_pos.le⟩)
    (show t ∈ Icc (0 : ℝ) T from ⟨ht.1.le, ht.2.le⟩)
  have htransport' :
      dot (B T - Romik.path params (T - t)) (u (T - t)) =
        dot (D 0 - Romik.path params t) (v t) := by
    simpa using htransport
  rw [htransport'] at h
  exact h

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C Stage 4: independent cap convexity and anchor foundation

This module separates the already direct cap geometry from the later theorem
that removing the downward niche preserves connectedness.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set

/-- The concrete endpoint anchor belongs to the reconstructed cap. -/
theorem anchor_mem_K_direct : anchor ∈ K := by
  have hA0 : A 0 = anchor := Stage2.A_zero_eq_anchor
  rw [← hA0]
  exact Stage3.supportA_direct 0 (by
    constructor
    · norm_num
    · dsimp [T]
      positivity)

/-- Convexity of the literal cap follows directly from its half-plane
definition. -/
theorem K_convex_direct : Convex ℝ K := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · change 0 ≤ a * x.2 + b * y.2
    exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  · intro t ht
    constructor
    · change dot (a • x + b • y) (u t) ≤
        dot (Romik.path params t) (u t) + 1
      have hxU := (hx.2 t ht).1
      have hyU := (hy.2 t ht).1
      dsimp [supportHalfU, dot] at hxU hyU ⊢
      have hax := mul_le_mul_of_nonneg_left hxU ha
      have hby := mul_le_mul_of_nonneg_left hyU hb
      calc
        (a * x.1 + b * y.1) * (u t).1 +
            (a * x.2 + b * y.2) * (u t).2 =
            a * (x.1 * (u t).1 + x.2 * (u t).2) +
              b * (y.1 * (u t).1 + y.2 * (u t).2) := by ring
        _ ≤ a * ((Romik.path params t).1 * (u t).1 +
              (Romik.path params t).2 * (u t).2 + 1) +
            b * ((Romik.path params t).1 * (u t).1 +
              (Romik.path params t).2 * (u t).2 + 1) := add_le_add hax hby
        _ = (Romik.path params t).1 * (u t).1 +
              (Romik.path params t).2 * (u t).2 + 1 := by
            rw [← add_mul, hab]
            ring
    · change dot (a • x + b • y) (v t) ≤
        dot (Romik.path params t) (v t) + 1
      have hxV := (hx.2 t ht).2
      have hyV := (hy.2 t ht).2
      dsimp [supportHalfV, dot] at hxV hyV ⊢
      have hax := mul_le_mul_of_nonneg_left hxV ha
      have hby := mul_le_mul_of_nonneg_left hyV hb
      calc
        (a * x.1 + b * y.1) * (v t).1 +
            (a * x.2 + b * y.2) * (v t).2 =
            a * (x.1 * (v t).1 + x.2 * (v t).2) +
              b * (y.1 * (v t).1 + y.2 * (v t).2) := by ring
        _ ≤ a * ((Romik.path params t).1 * (v t).1 +
              (Romik.path params t).2 * (v t).2 + 1) +
            b * ((Romik.path params t).1 * (v t).1 +
              (Romik.path params t).2 * (v t).2 + 1) := add_le_add hax hby
        _ = (Romik.path params t).1 * (v t).1 +
              (Romik.path params t).2 * (v t).2 + 1 := by
            rw [← add_mul, hab]
            ring

/-- The nonempty convex cap is connected. -/
theorem K_connected_direct : IsConnected K :=
  K_convex_direct.isConnected ⟨anchor, anchor_mem_K_direct⟩

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C Stage 4: independent vertical-fill topology

This module isolates the connectedness half of the niche argument from the
upper-envelope/frontier equality.  It can therefore be kernel-built even while
the boundary module is still under repair.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set

/-- Vertical fill below a parametrized graph. -/
@[expose]
def verticalFill (f : ℝ → Point) (I : Set ℝ) : Set Point :=
  {q | ∃ t ∈ I, q.1 = (f t).1 ∧ 0 ≤ q.2 ∧ q.2 < (f t).2}

/-- The three certified upper-envelope pieces as strict vertical fills. -/
@[expose]
def certifiedNicheRegion : Set Point :=
  verticalFill D (Icc (0 : ℝ) params.theta) ∪
  verticalFill (Romik.path params) (Icc params.phi tau) ∪
  verticalFill B (Icc eta T)

/-- Consecutive endpoint incidences of the three graph pieces. -/
theorem niche_piece_endpoints :
    B eta = Romik.path params params.phi ∧
    D params.theta = Romik.path params tau ∧
    (B T).2 = 0 ∧ (D 0).2 = 0 :=
  ⟨B_eta_eq_path_phi, D_theta_eq_path_tau,
    B_T_y_zero, D_zero_y_zero⟩

/-- A strict positive vertical fill is a continuous image of a connected
product. -/
theorem verticalFill_strict_isConnected
    {f : ℝ → Point} {I : Set ℝ}
    (hI : IsConnected I)
    (hf : ContinuousOn f I)
    (hy : ∀ t ∈ I, 0 < (f t).2) :
    IsConnected (verticalFill f I) := by
  let P : Set (ℝ × ℝ) := I ×ˢ Ico (0 : ℝ) 1
  have hP : IsConnected P := by
    dsimp [P]
    exact hI.prod (isConnected_Ico (by norm_num))
  let F : (ℝ × ℝ) → Point := fun z =>
    ((f z.1).1, z.2 * (f z.1).2)
  have hfcomp : ContinuousOn (fun z : ℝ × ℝ => f z.1) P := by
    exact hf.comp continuous_fst.continuousOn (by
      intro z hz
      exact hz.1)
  have hF : ContinuousOn F P := by
    dsimp [F]
    exact hfcomp.fst.prodMk (continuous_snd.continuousOn.mul hfcomp.snd)
  have himage : F '' P = verticalFill f I := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hlt := mul_lt_mul_of_pos_right hz.2.2 (hy z.1 hz.1)
      exact ⟨z.1, hz.1, rfl,
        mul_nonneg hz.2.1 (hy z.1 hz.1).le, by simpa [F] using hlt⟩
    · rintro ⟨t, ht, hx, hy0, hylt⟩
      have htop := hy t ht
      let s : ℝ := q.2 / (f t).2
      have hs : s ∈ Ico (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg hy0 htop.le
        · exact (div_lt_one htop).2 hylt
      refine ⟨(t, s), ⟨ht, hs⟩, ?_⟩
      apply Prod.ext
      · simpa [F] using hx.symm
      · dsimp [F, s]
        field_simp [ne_of_gt htop]
  rw [← himage]
  exact hP.image F hF

theorem D_fill_Icc_eq_Ioc :
    verticalFill D (Icc (0 : ℝ) params.theta) =
      verticalFill D (Ioc (0 : ℝ) params.theta) := by
  ext q
  constructor
  · rintro ⟨t, ht, hx, hy0, hylt⟩
    have htpos : 0 < t := by
      by_contra hnot
      have ht0 : t = 0 := le_antisymm (le_of_not_gt hnot) ht.1
      subst t
      rw [D_zero_y_zero] at hylt
      linarith
    exact ⟨t, ⟨htpos, ht.2⟩, hx, hy0, hylt⟩
  · rintro ⟨t, ht, hx, hy0, hylt⟩
    exact ⟨t, ⟨ht.1.le, ht.2⟩, hx, hy0, hylt⟩

theorem B_fill_Icc_eq_Ico :
    verticalFill B (Icc eta T) = verticalFill B (Ico eta T) := by
  ext q
  constructor
  · rintro ⟨t, ht, hx, hy0, hylt⟩
    have htlt : t < T := by
      by_contra hnot
      have htT : t = T := le_antisymm ht.2 (le_of_not_gt hnot)
      subst t
      rw [B_T_y_zero] at hylt
      linarith
    exact ⟨t, ⟨ht.1, htlt⟩, hx, hy0, hylt⟩
  · rintro ⟨t, ht, hx, hy0, hylt⟩
    exact ⟨t, ⟨ht.1, ht.2.le⟩, hx, hy0, hylt⟩

private theorem D_fill_connected :
    IsConnected (verticalFill D (Ioc (0 : ℝ) params.theta)) := by
  exact verticalFill_strict_isConnected
    (isConnected_Ioc theta_pos) D_continuous.continuousOn
    (by intro t ht; exact D_y_pos ht)

private theorem path_fill_connected :
    IsConnected
      (verticalFill (Romik.path params) (Icc params.phi tau)) := by
  exact verticalFill_strict_isConnected
    (isConnected_Icc (le_trans phi_lt_theta.le
      (le_trans theta_lt_eta.le eta_lt_tau.le)))
    pathContinuous.continuousOn (by
      intro t ht
      exact path_core_y_pos ht)

private theorem B_fill_connected :
    IsConnected (verticalFill B (Ico eta T)) := by
  exact verticalFill_strict_isConnected
    (isConnected_Ico eta_lt_T) B_continuous.continuousOn
    (by intro t ht; exact B_y_pos ht)

theorem niche_fills_overlap :
    (verticalFill D (Ioc (0 : ℝ) params.theta) ∩
      verticalFill (Romik.path params) (Icc params.phi tau)).Nonempty ∧
    (verticalFill (Romik.path params) (Icc params.phi tau) ∩
      verticalFill B (Ico eta T)).Nonempty := by
  refine ⟨?_, ?_⟩
  · let q : Point := ((D params.theta).1, (D params.theta).2 / 2)
    have hy0 : 0 ≤ q.2 := by
      dsimp [q]
      nlinarith [D_theta_y_pos]
    have hylt : q.2 < (D params.theta).2 := by
      dsimp [q]
      nlinarith [D_theta_y_pos]
    refine ⟨q, ?_, ?_⟩
    · exact ⟨params.theta, ⟨theta_pos, le_rfl⟩, rfl, hy0, hylt⟩
    · refine ⟨tau, ⟨?_, le_rfl⟩, ?_, ?_, ?_⟩
      · exact le_trans phi_lt_theta.le (le_trans theta_lt_eta.le eta_lt_tau.le)
      · dsimp [q]
        rw [← D_theta_eq_path_tau]
      · exact hy0
      · simpa [D_theta_eq_path_tau] using hylt
  · let q : Point := ((B eta).1, (B eta).2 / 2)
    have hy0 : 0 ≤ q.2 := by
      dsimp [q]
      nlinarith [B_eta_y_pos]
    have hylt : q.2 < (B eta).2 := by
      dsimp [q]
      nlinarith [B_eta_y_pos]
    refine ⟨q, ?_, ?_⟩
    · refine ⟨params.phi, ⟨le_rfl, ?_⟩, ?_, ?_, ?_⟩
      · exact le_trans phi_lt_theta.le (le_trans theta_lt_eta.le eta_lt_tau.le)
      · dsimp [q]
        rw [← B_eta_eq_path_phi]
      · exact hy0
      · simpa [B_eta_eq_path_phi] using hylt
    · exact ⟨eta, ⟨le_rfl, eta_lt_T⟩, rfl, hy0, hylt⟩

/-- Connectedness of the certified three-piece vertical-fill region. -/
theorem certifiedNicheRegion_connected : IsConnected certifiedNicheRegion := by
  unfold certifiedNicheRegion
  rw [D_fill_Icc_eq_Ioc, B_fill_Icc_eq_Ico]
  rcases niche_fills_overlap with ⟨hDX, hXB⟩
  have hDXc := D_fill_connected.union hDX path_fill_connected
  exact hDXc.union (by
    rcases hXB with ⟨q, hqX, hqB⟩
    exact ⟨q, Or.inr hqX, hqB⟩) B_fill_connected

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C Stage 4: inner-wall graph identities
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set

/-- First inner wall as a graph over horizontal coordinate. -/
def bRoof (t X : ℝ) : ℝ :=
  (dot (Romik.path params t) (u t) - X * Real.cos t) / Real.sin t

/-- Second inner wall as a graph over horizontal coordinate. -/
def dRoof (t X : ℝ) : ℝ :=
  (dot (Romik.path params t) (v t) + X * Real.sin t) / Real.cos t

/-- Vertical roof of one instantaneous open inner quadrant. -/
def instantRoof (t X : ℝ) : ℝ := min (bRoof t X) (dRoof t X)

/-- A point of nonnegative height is in the instantaneous inner quadrant iff it
lies strictly below both graph roofs. -/
theorem mem_innerQuadrant_iff_roofs {t X Y : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    (X,Y) ∈ Romik.innerQuadrantAt params t ↔
      Y < bRoof t X ∧ Y < dRoof t X := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (lt_trans ht.2 (by
    dsimp [T]; linarith [Real.pi_pos]))
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by
    linarith [Real.pi_pos, ht.1], by simpa [T] using ht.2⟩
  simp only [Romik.innerQuadrantAt, dot, u, v, mul_neg, neg_add_lt_iff_lt_add, add_zero,
    mem_ofPred_eq, bRoof, dRoof]
  constructor
  · rintro ⟨hu,hv⟩
    constructor
    · apply (lt_div_iff₀ hs).2
      linarith
    · apply (lt_div_iff₀ hc).2
      linarith
  · rintro ⟨hb,hd⟩
    constructor
    · have := (lt_div_iff₀ hs).1 hb
      linarith
    · have := (lt_div_iff₀ hc).1 hd
      linarith

/-- The two walls agree at their apex. -/
theorem roofs_at_path (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    bRoof t (Romik.path params t).1 = (Romik.path params t).2 ∧
    dRoof t (Romik.path params t).1 = (Romik.path params t).2 := by
  have hs : Real.sin t ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 (lt_trans ht.2 (by
    dsimp [T]; linarith [Real.pi_pos])))
  have hc : Real.cos t ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by
    linarith [Real.pi_pos, ht.1], by simpa [T] using ht.2⟩)
  constructor <;> simp [bRoof, dRoof, dot, u, v, hs, hc]

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C Stage 4: direct membership of the certified vertical fills

These are the three concrete reverse-inclusion facts needed to identify the
literal niche with its certified vertical-fill region.  They are proved from
the literal open-quadrant definition, not assumed through a Stage 2 API.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

private theorem sin_pos_physical {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    0 < Real.sin t :=
  Real.sin_pos_of_pos_of_lt_pi ht.1
    (lt_trans ht.2 (by dsimp [T]; linarith [Real.pi_pos]))

private theorem cos_pos_physical {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    0 < Real.cos t :=
  Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], by simpa [T] using ht.2⟩

private theorem phi_upper_twentieth_membership :
    params.phi ≤ (1 / 20 : ℝ) := by
  have h := phi_bounds.2
  norm_num at h ⊢
  linarith

private theorem a1_lower_six_fifths_membership :
    (6 / 5 : ℝ) ≤ params.a1 := by
  have h := Romik.a1_lower_bound_of_mem_box params_mem
  norm_num at h ⊢
  linarith

private theorem alphaBeta1_snd_nonneg_early {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    0 ≤ (Romik.alphaBeta1 params s).2 := by
  have hpi : s ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hsinUpper := Real.sin_le hs0
  have hcosLower : 1 - s ^ 2 / 2 ≤ Real.cos s :=
    Real.one_sub_sq_div_two_le_cos
  have hcos0 : 0 ≤ Real.cos s := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_gt_three]
  have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) :=
    mul_nonneg hs0 (sub_nonneg.mpr hs20)
  have hcoef : (12 / 5 : ℝ) ≤ 2 * params.a1 := by
    nlinarith [a1_lower_six_fifths_membership]
  have hmul : (12 / 5 : ℝ) * Real.cos s ≤
      2 * params.a1 * Real.cos s :=
    mul_le_mul_of_nonneg_right hcoef hcos0
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith [hsinUpper, hcosLower, hquad, hmul]

private theorem beta_nonneg_early {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.theta) : 0 ≤ beta t := by
  by_cases hphi : t ≤ params.phi
  · have hs20 : t ≤ (1 / 20 : ℝ) :=
      le_trans hphi phi_upper_twentieth_membership
    have h := alphaBeta1_snd_nonneg_early ht.1 hs20
    simpa [beta, alphaBetaAt, hphi] using h
  · have htPhysical : t ∈ Icc (0 : ℝ) T :=
      ⟨ht.1, le_trans ht.2 (le_trans theta_lt_eta.le
        (le_trans eta_lt_tau.le tau_le_T))⟩
    have hrho := Stage2.rhoA_nonneg htPhysical
    unfold Stage2.rhoA at hrho
    rw [ite_eq_right hphi, ite_eq_left ht.2] at hrho
    simp only [beta, alphaBetaAt, ite_eq_right hphi, ite_eq_left ht.2]
    dsimp [Romik.alphaBeta2]
    exact hrho

private theorem B_bRoof_eq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    bRoof t (B t).1 = (B t).2 := by
  have hs0 : Real.sin t ≠ 0 := ne_of_gt (sin_pos_physical ht)
  have hcontact := B_inner_u_identity t
  unfold bRoof
  apply (div_eq_iff hs0).2
  dsimp [dot, u] at hcontact ⊢
  nlinarith

private theorem B_le_dRoof {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) (htPhi : t ∈ Icc params.phi T) :
    (B t).2 ≤ dRoof t (B t).1 := by
  have hc := cos_pos_physical ht
  have ha := alpha_nonpos htPhi
  have hv : dot (B t - Romik.path params t) (v t) = alpha t := by
    simp only [B, dot, v]
    simp
    nlinarith [Real.sin_sq_add_cos_sq t]
  unfold dRoof
  apply (le_div_iff₀ hc).2
  dsimp [dot, v] at hv ⊢
  nlinarith

private theorem D_dRoof_eq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    dRoof t (D t).1 = (D t).2 := by
  have hc0 : Real.cos t ≠ 0 := ne_of_gt (cos_pos_physical ht)
  have hcontact := D_inner_v_identity t
  unfold dRoof
  apply (div_eq_iff hc0).2
  dsimp [dot, v] at hcontact ⊢
  nlinarith

private theorem D_le_bRoof {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T)
    (htTheta : t ∈ Icc (0 : ℝ) params.theta) :
    (D t).2 ≤ bRoof t (D t).1 := by
  have hs := sin_pos_physical ht
  have hb := beta_nonneg_early htTheta
  have hu : dot (D t - Romik.path params t) (u t) = -beta t := by
    simp only [D, dot, u]
    simp
    nlinarith [Real.sin_sq_add_cos_sq t]
  unfold bRoof
  apply (le_div_iff₀ hs).2
  dsimp [dot, u] at hu ⊢
  nlinarith

/-- Every strict vertical point below a core-path point belongs to the literal
niche. -/
theorem vertical_below_path_mem_niche {r Y : ℝ}
    (hr : r ∈ Icc params.phi tau) (hY0 : 0 ≤ Y)
    (hY : Y < (Romik.path params r).2) :
    ((Romik.path params r).1, Y) ∈ Romik.niche params := by
  have hrIoo : r ∈ Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le phi_pos hr.1,
      lt_of_le_of_lt hr.2 tau_lt_T⟩
  refine ⟨by simpa [capFan] using hY0, ⟨r, hrIoo, ?_⟩⟩
  apply (mem_innerQuadrant_iff_roofs hrIoo).2
  have hroof := roofs_at_path r hrIoo
  rw [hroof.1, hroof.2]
  exact ⟨hY, hY⟩

/-- Every strict vertical point below the late `B` contact belongs to the
literal niche. -/
theorem vertical_below_B_mem_niche {r Y : ℝ}
    (hr : r ∈ Icc eta T) (hY0 : 0 ≤ Y) (hY : Y < (B r).2) :
    ((B r).1, Y) ∈ Romik.niche params := by
  have hrlt : r < T := by
    by_contra hnot
    have hrT : r = T := le_antisymm hr.2 (le_of_not_gt hnot)
    subst r
    rw [B_T_y_zero] at hY
    linarith
  have hrIoo : r ∈ Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le (lt_trans theta_pos theta_lt_eta) hr.1, hrlt⟩
  have hrPhi : r ∈ Icc params.phi T :=
    ⟨le_trans (le_trans phi_lt_theta.le theta_lt_eta.le) hr.1, hr.2⟩
  refine ⟨by simpa [capFan] using hY0, ⟨r, hrIoo, ?_⟩⟩
  apply (mem_innerQuadrant_iff_roofs hrIoo).2
  refine ⟨?_, ?_⟩
  · rw [B_bRoof_eq hrIoo]
    exact hY
  · exact lt_of_lt_of_le hY (B_le_dRoof hrIoo hrPhi)

/-- Every strict vertical point below the early `D` contact belongs to the
literal niche. -/
theorem vertical_below_D_mem_niche {r Y : ℝ}
    (hr : r ∈ Icc (0 : ℝ) params.theta) (hY0 : 0 ≤ Y)
    (hY : Y < (D r).2) :
    ((D r).1, Y) ∈ Romik.niche params := by
  have hrpos : 0 < r := by
    by_contra hnot
    have hr0 : r = 0 := le_antisymm (le_of_not_gt hnot) hr.1
    subst r
    rw [D_zero_y_zero] at hY
    linarith
  have hrIoo : r ∈ Ioo (0 : ℝ) T :=
    ⟨hrpos, lt_of_le_of_lt hr.2 theta_lt_T⟩
  refine ⟨by simpa [capFan] using hY0, ⟨r, hrIoo, ?_⟩⟩
  apply (mem_innerQuadrant_iff_roofs hrIoo).2
  refine ⟨?_, ?_⟩
  · exact lt_of_lt_of_le hY (D_le_bRoof hrIoo hr)
  · rw [D_dRoof_eq hrIoo]
    exact hY

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C Stage 4: frontier of a strict vertical subgraph

This file contains the topological calculation used by the concrete Gerver
niche.  The generic lemma is intentionally independent of the old Stage 2
topology sketches: it computes the closure and the interior of a strict
vertical subgraph directly.
-/

/-! ## The three Gerver roof arcs are graphs over horizontal position -/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set

private theorem u_hasDerivAt_frontier (t : ℝ) : HasDerivAt u (v t) t :=
  Stage2.u_hasDerivAt t

private theorem v_hasDerivAt_frontier (t : ℝ) : HasDerivAt v (-u t) t :=
  Stage2.v_hasDerivAt t

private theorem square_hasDerivAt_frontier (t : ℝ) :
    HasDerivAt (fun s : ℝ => s * s) (t + t) t :=
  Stage2.square_hasDerivAt t

private theorem beta1_hasDerivAt_frontier (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta1 params s).2)
      (-2 * params.a1 * Real.sin t + 2 * params.a2 * Real.cos t) t := by
  have h1 := HasDerivAt.const_mul (2 * params.a1) (Real.hasDerivAt_cos t)
  have h2 := HasDerivAt.const_mul (2 * params.a2) (Real.hasDerivAt_sin t)
  have h := (h1.fun_add h2).fun_sub (hasDerivAt_const t (1 : ℝ))
  refine h.congr_deriv ?_
  ring

private theorem beta2_hasDerivAt_frontier (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta2 params s).2)
      (-(1 / 2 : ℝ) * t + params.b1) t :=
  beta2_hasDerivAt t

private theorem alpha4_hasDerivAt_frontier (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta4 params s).1)
      ((1 / 2 : ℝ) * t - params.d1) t :=
  alpha4_hasDerivAt t

private theorem alpha5_hasDerivAt_frontier (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta5 params s).1)
      (-2 * params.e1 * Real.cos t - 2 * params.e2 * Real.sin t) t :=
  alpha5_hasDerivAt t

private theorem contactD_hasDerivAt
    {x : ℝ → Point} {ab : ℝ → Point} {bp : ℝ} (t : ℝ)
    (hx : HasDerivAt x (Romik.rot t (ab t)) t)
    (hb : HasDerivAt (fun s => (ab s).2) bp t) :
    HasDerivAt (fun s => x s - (ab s).2 • u s)
      (((ab t).1 - bp) • u t) t := by
  have h := hx.fun_sub (hb.fun_smul (u_hasDerivAt_frontier t))
  refine h.congr_deriv ?_
  ext <;> simp [Romik.rot, u, v] <;> ring

private theorem contactB_hasDerivAt
    {x : ℝ → Point} {ab : ℝ → Point} {ap : ℝ} (t : ℝ)
    (hx : HasDerivAt x (Romik.rot t (ab t)) t)
    (ha : HasDerivAt (fun s => (ab s).1) ap t) :
    HasDerivAt (fun s => x s + (ab s).1 • v s)
      (((ab t).2 + ap) • v t) t := by
  have h := hx.fun_add (ha.fun_smul (v_hasDerivAt_frontier t))
  refine h.congr_deriv ?_
  ext <;> simp [Romik.rot, u, v] <;> ring

private def phaseD1 (t : ℝ) : Point :=
  Romik.path1 params t - (Romik.alphaBeta1 params t).2 • u t

private def phaseD2 (t : ℝ) : Point :=
  Romik.path2 params t - (Romik.alphaBeta2 params t).2 • u t

private def phaseB4_m421765a (t : ℝ) : Point :=
  Romik.path4 params t + (Romik.alphaBeta4 params t).1 • v t

private def phaseB5_m421765a (t : ℝ) : Point :=
  Romik.path5 params t + (Romik.alphaBeta5 params t).1 • v t

private theorem phaseD1_hasDerivAt (t : ℝ) :
    HasDerivAt phaseD1 ((1 / 2 : ℝ) • u t) t := by
  have h := contactD_hasDerivAt t (path1_hasDerivAt_public t)
    (beta1_hasDerivAt_frontier t)
  exact h.congr_deriv (by
    apply congrArg (fun c : ℝ => c • u t)
    dsimp [Romik.alphaBeta1]
    ring)

private theorem phaseD2_hasDerivAt (t : ℝ) :
    HasDerivAt phaseD2 ((1 + params.b1 - t / 2) • u t) t := by
  have h := contactD_hasDerivAt t (path2_hasDerivAt_public t)
    (beta2_hasDerivAt_frontier t)
  exact h.congr_deriv (by
    apply congrArg (fun c : ℝ => c • u t)
    dsimp [Romik.alphaBeta2]
    ring)

private theorem phaseB4_hasDerivAt (t : ℝ) :
    HasDerivAt phaseB4_m421765a ((params.d1 - 1 - t / 2) • v t) t := by
  have h := contactB_hasDerivAt t (path4_hasDerivAt_public t)
    (alpha4_hasDerivAt_frontier t)
  exact h.congr_deriv (by
    apply congrArg (fun c : ℝ => c • v t)
    dsimp [Romik.alphaBeta4]
    ring)

private theorem phaseB5_hasDerivAt (t : ℝ) :
    HasDerivAt phaseB5_m421765a ((-(1 / 2 : ℝ)) • v t) t := by
  have h := contactB_hasDerivAt t (path5_hasDerivAt_public t)
    (alpha5_hasDerivAt_frontier t)
  exact h.congr_deriv (by
    apply congrArg (fun c : ℝ => c • v t)
    dsimp [Romik.alphaBeta5]
    ring)

private theorem phaseD1_continuous : Continuous phaseD1 := by
  exact continuous_iff_continuousAt.2 fun t => (phaseD1_hasDerivAt t).continuousAt

private theorem phaseD2_continuous : Continuous phaseD2 := by
  exact continuous_iff_continuousAt.2 fun t => (phaseD2_hasDerivAt t).continuousAt

private theorem phaseB4_continuous : Continuous phaseB4_m421765a := by
  exact continuous_iff_continuousAt.2 fun t => (phaseB4_hasDerivAt t).continuousAt

private theorem phaseB5_continuous : Continuous phaseB5_m421765a := by
  exact continuous_iff_continuousAt.2 fun t => (phaseB5_hasDerivAt t).continuousAt

private theorem dot_fixed_hasDerivAt_frontier
    {f : ℝ → Point} {df w : Point} {t : ℝ}
    (h : HasDerivAt f df t) :
    HasDerivAt (fun s => dot (f s) w) (dot df w) t :=
  dot_fixed_hasDerivAt h w

private theorem b1_lower_frontier : (-53 / 100 : ℝ) ≤ params.b1 := by
  have h := PartB.b1_contains.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem theta_upper_frontier : params.theta ≤ (689 / 1000 : ℝ) := by
  have h := theta_bounds.2
  norm_num at h ⊢
  linarith

private theorem d1_lower_frontier : (13 / 10 : ℝ) ≤ params.d1 := by
  have h := PartB.d1_contains.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem d1_upper_frontier : params.d1 ≤ (33 / 25 : ℝ) := by
  have h := PartB.d1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem eta_lower_frontier : (4 / 5 : ℝ) ≤ eta := by
  dsimp [eta, T]
  nlinarith [Real.pi_gt_three, theta_upper_frontier]

private theorem T_upper_frontier : T < (8 / 5 : ℝ) := by
  have hp := ExactReplay.piI_contains_pi
  have hhi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) := hp.2
  have h32 : (ExactReplay.piI.hi : ℝ) < (16 / 5 : ℝ) := by
    norm_num [ExactReplay.piI, ExactReplay.q]
  dsimp [T]
  linarith

private theorem phaseD1_fst_strictMono :
    StrictMonoOn (fun t => (phaseD1 t).1) (Icc (0 : ℝ) params.phi) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) phaseD1_continuous.fst.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  have hder : HasDerivAt (fun s => (phaseD1 s).1)
      (((1 / 2 : ℝ) • u t).1) t := by
    have h := dot_fixed_hasDerivAt_frontier (w := ((1 : ℝ), 0))
      (phaseD1_hasDerivAt t)
    simpa [dot] using h
  rw [hder.deriv]
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], by
      have htT : t < T := lt_trans ht.2 phi_lt_T
      simpa [T] using htT⟩
  simpa [u] using mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hc

private theorem phaseD2_fst_strictMono :
    StrictMonoOn (fun t => (phaseD2 t).1) (Icc params.phi params.theta) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) phaseD2_continuous.fst.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  have hder : HasDerivAt (fun s => (phaseD2 s).1)
      (((1 + params.b1 - t / 2) • u t).1) t := by
    have h := dot_fixed_hasDerivAt_frontier (w := ((1 : ℝ), 0))
      (phaseD2_hasDerivAt t)
    simpa [dot] using h
  rw [hder.deriv]
  have hcoef : 0 < 1 + params.b1 - t / 2 := by
    nlinarith [b1_lower_frontier, theta_upper_frontier, ht.2]
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, phi_pos, ht.1], by
      have htT : t < T := lt_trans ht.2 theta_lt_T
      simpa [T] using htT⟩
  simpa [u] using mul_pos hcoef hc

private theorem phaseB4_fst_strictMono :
    StrictMonoOn (fun t => (phaseB4_m421765a t).1) (Icc eta tau) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) phaseB4_continuous.fst.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  have hder : HasDerivAt (fun s => (phaseB4_m421765a s).1)
      (((params.d1 - 1 - t / 2) • v t).1) t := by
    have h := dot_fixed_hasDerivAt_frontier (w := ((1 : ℝ), 0))
      (phaseB4_hasDerivAt t)
    simpa [dot] using h
  rw [hder.deriv]
  have hcoef : params.d1 - 1 - t / 2 < 0 := by
    nlinarith [d1_upper_frontier, eta_lower_frontier, ht.1]
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (lt_trans (lt_trans theta_pos theta_lt_eta) ht.1)
    (lt_trans (lt_trans ht.2 tau_lt_T) (by
      dsimp [T]; nlinarith [Real.pi_pos]))
  have hm : 0 < (params.d1 - 1 - t / 2) * (-Real.sin t) :=
    mul_pos_of_neg_of_neg hcoef (neg_neg_of_pos hs)
  simpa [v] using hm

private theorem phaseB5_fst_strictMono :
    StrictMonoOn (fun t => (phaseB5_m421765a t).1) (Icc tau T) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) phaseB5_continuous.fst.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  have hder : HasDerivAt (fun s => (phaseB5_m421765a s).1)
      (((-(1 / 2 : ℝ)) • v t).1) t := by
    have h := dot_fixed_hasDerivAt_frontier (w := ((1 : ℝ), 0))
      (phaseB5_hasDerivAt t)
    simpa [dot] using h
  rw [hder.deriv]
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (lt_trans (lt_trans (lt_trans theta_pos theta_lt_eta) eta_lt_tau) ht.1)
    (lt_trans ht.2 (by dsimp [T]; nlinarith [Real.pi_pos]))
  simpa [v] using mul_pos_of_neg_of_neg (by norm_num : (-(1 / 2 : ℝ)) < 0)
    (neg_neg_of_pos hs)

private theorem phaseD1_eq_D {t : ℝ} (ht : t ∈ Icc (0 : ℝ) params.phi) :
    phaseD1 t = D t := by
  apply Prod.ext <;>
    simp [phaseD1, D, beta, alphaBetaAt, Romik.path, ht.2]

private theorem phaseD2_eq_D {t : ℝ} (ht : t ∈ Icc params.phi params.theta) :
    phaseD2 t = D t := by
  rcases ht.1.eq_or_lt with h | h
  · subst t
    apply Prod.ext <;>
      simp [phaseD2, D, beta, alphaBetaAt, Romik.path, PartB.match12, alphaBeta_match12_direct]
  · apply Prod.ext <;>
      simp [phaseD2, D, beta, alphaBetaAt, Romik.path, not_le.mpr h, ht.2]

private theorem phaseB4_eq_B {t : ℝ} (ht : t ∈ Icc eta tau) :
    phaseB4_m421765a t = B t := by
  rcases ht.1.eq_or_lt with h | h
  · subst t
    have hm : Romik.path3 params eta = Romik.path4 params eta := by
      simpa [eta, T] using PartB.match34
    have hphase : phaseB4_m421765a eta = Romik.path4 params eta +
        (Romik.alphaBeta4 params eta).1 • v eta := by
      rfl
    have hetaRaw : eta ≤ Real.pi / 2 - params.theta := by rfl
    have hB : B eta = Romik.path3 params eta +
        (Romik.alphaBeta3 params eta).1 • v eta := by
      apply Prod.ext <;>
        simp [B, alpha, alphaBetaAt, Romik.path,
          not_le.mpr phi_lt_eta, not_le.mpr theta_lt_eta, hetaRaw]
    calc
      phaseB4_m421765a eta = Romik.path4 params eta +
          (Romik.alphaBeta4 params eta).1 • v eta := hphase
      _ = Romik.path3 params eta +
          (Romik.alphaBeta3 params eta).1 • v eta := by
            rw [hm, alphaBeta_match34_direct]
      _ = B eta := hB.symm
  · have hetaRaw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using h
    have htauRaw : t ≤ Real.pi / 2 - params.phi := by
      simpa [tau, T] using ht.2
    apply Prod.ext <;>
      simp [phaseB4_m421765a, B, alpha, alphaBetaAt, Romik.path,
        not_le.mpr (lt_trans phi_lt_eta h),
        not_le.mpr (lt_trans theta_lt_eta h), not_le.mpr hetaRaw, htauRaw, eta, tau, T]

private theorem phaseB5_eq_B {t : ℝ} (ht : t ∈ Icc tau T) :
    phaseB5_m421765a t = B t := by
  rcases ht.1.eq_or_lt with h | h
  · subst t
    have hm : Romik.path4 params tau = Romik.path5 params tau := by
      simpa [tau, T] using PartB.match45
    have hphase : phaseB5_m421765a tau = Romik.path5 params tau +
        (Romik.alphaBeta5 params tau).1 • v tau := by
      rfl
    have htauRaw : tau ≤ Real.pi / 2 - params.phi := by rfl
    have hetaRaw : ¬ tau ≤ Real.pi / 2 - params.theta := by
      exact not_le.mpr (by simpa [eta, T] using eta_lt_tau)
    have hB : B tau = Romik.path4 params tau +
        (Romik.alphaBeta4 params tau).1 • v tau := by
      apply Prod.ext <;>
        simp [B, alpha, alphaBetaAt, Romik.path,
          not_le.mpr (lt_trans phi_lt_eta eta_lt_tau),
          not_le.mpr (lt_trans theta_lt_eta eta_lt_tau),
          not_le.mpr eta_lt_tau, hetaRaw, htauRaw]
    calc
      phaseB5_m421765a tau = Romik.path5 params tau +
          (Romik.alphaBeta5 params tau).1 • v tau := hphase
      _ = Romik.path4 params tau +
          (Romik.alphaBeta4 params tau).1 • v tau := by
            rw [hm, alphaBeta_match45_direct]
      _ = B tau := hB.symm
  · have hetaRaw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using lt_trans eta_lt_tau h
    have htauRaw : Real.pi / 2 - params.phi < t := by
      simpa [tau, T] using h
    apply Prod.ext <;>
      simp [phaseB5_m421765a, B, alpha, alphaBetaAt, Romik.path,
        not_le.mpr (lt_trans (lt_trans phi_lt_eta eta_lt_tau) h),
        not_le.mpr (lt_trans (lt_trans theta_lt_eta eta_lt_tau) h),
        not_le.mpr hetaRaw, not_le.mpr htauRaw, eta, tau, T]

/-- The early contact arc has strictly increasing horizontal projection. -/
theorem D_fst_strictMono :
    StrictMonoOn (fun t => (D t).1) (Icc (0 : ℝ) params.theta) := by
  intro x hx y hy hxy
  by_cases hyphi : y ≤ params.phi
  · have hxphi : x ∈ Icc (0 : ℝ) params.phi :=
      ⟨hx.1, le_trans hxy.le hyphi⟩
    have hyphi' : y ∈ Icc (0 : ℝ) params.phi := ⟨hy.1, hyphi⟩
    simpa [phaseD1_eq_D hxphi, phaseD1_eq_D hyphi'] using
      phaseD1_fst_strictMono hxphi hyphi' hxy
  · have hphiy : params.phi < y := lt_of_not_ge hyphi
    by_cases hxphi : x ≤ params.phi
    · have hx1 : x ∈ Icc (0 : ℝ) params.phi := ⟨hx.1, hxphi⟩
      have hphi1 : params.phi ∈ Icc (0 : ℝ) params.phi :=
        ⟨phi_pos.le, le_rfl⟩
      have hphi2 : params.phi ∈ Icc params.phi params.theta :=
        ⟨le_rfl, phi_lt_theta.le⟩
      have hy2 : y ∈ Icc params.phi params.theta :=
        ⟨hphiy.le, hy.2⟩
      have hleft := phaseD1_fst_strictMono.monotoneOn hx1 hphi1 hxphi
      have hright := phaseD2_fst_strictMono hphi2 hy2 hphiy
      calc
        (D x).1 = (phaseD1 x).1 := congrArg Prod.fst (phaseD1_eq_D hx1).symm
        _ ≤ (phaseD1 params.phi).1 := hleft
        _ = (D params.phi).1 := congrArg Prod.fst (phaseD1_eq_D hphi1)
        _ = (phaseD2 params.phi).1 := congrArg Prod.fst (phaseD2_eq_D hphi2).symm
        _ < (phaseD2 y).1 := hright
        _ = (D y).1 := congrArg Prod.fst (phaseD2_eq_D hy2)
    · have hphix : params.phi < x := lt_of_not_ge hxphi
      have hx2 : x ∈ Icc params.phi params.theta := ⟨hphix.le, hx.2⟩
      have hy2 : y ∈ Icc params.phi params.theta := ⟨hphiy.le, hy.2⟩
      simpa [phaseD2_eq_D hx2, phaseD2_eq_D hy2] using
        phaseD2_fst_strictMono hx2 hy2 hxy

/-- The late contact arc has strictly increasing horizontal projection. -/
theorem B_fst_strictMono :
    StrictMonoOn (fun t => (B t).1) (Icc eta T) := by
  intro x hx y hy hxy
  by_cases hytau : y ≤ tau
  · have hx4 : x ∈ Icc eta tau := ⟨hx.1, le_trans hxy.le hytau⟩
    have hy4 : y ∈ Icc eta tau := ⟨hy.1, hytau⟩
    simpa [phaseB4_eq_B hx4, phaseB4_eq_B hy4] using
      phaseB4_fst_strictMono hx4 hy4 hxy
  · have htauy : tau < y := lt_of_not_ge hytau
    by_cases hxtau : x ≤ tau
    · have hx4 : x ∈ Icc eta tau := ⟨hx.1, hxtau⟩
      have htau4 : tau ∈ Icc eta tau := ⟨eta_lt_tau.le, le_rfl⟩
      have htau5 : tau ∈ Icc tau T := ⟨le_rfl, tau_lt_T.le⟩
      have hy5 : y ∈ Icc tau T := ⟨htauy.le, hy.2⟩
      have hleft := phaseB4_fst_strictMono.monotoneOn hx4 htau4 hxtau
      have hright := phaseB5_fst_strictMono htau5 hy5 htauy
      calc
        (B x).1 = (phaseB4_m421765a x).1 := congrArg Prod.fst (phaseB4_eq_B hx4).symm
        _ ≤ (phaseB4_m421765a tau).1 := hleft
        _ = (B tau).1 := congrArg Prod.fst (phaseB4_eq_B htau4)
        _ = (phaseB5_m421765a tau).1 := congrArg Prod.fst (phaseB5_eq_B htau5).symm
        _ < (phaseB5_m421765a y).1 := hright
        _ = (B y).1 := congrArg Prod.fst (phaseB5_eq_B hy5)
    · have htaux : tau < x := lt_of_not_ge hxtau
      have hx5 : x ∈ Icc tau T := ⟨htaux.le, hx.2⟩
      have hy5 : y ∈ Icc tau T := ⟨htauy.le, hy.2⟩
      simpa [phaseB5_eq_B hx5, phaseB5_eq_B hy5] using
        phaseB5_fst_strictMono hx5 hy5 hxy

private theorem b1_upper_frontier : params.b1 ≤ (-527 / 1000 : ℝ) := by
  have h := PartB.b1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem c2_lower_frontier : (-1 : ℝ) ≤ params.c2 := by
  have h := PartB.c2_contains.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem path_fst_deriv_neg {t : ℝ} (ht : t ∈ Ioo params.phi tau) :
    deriv (fun s => (Romik.path params s).1) t < 0 := by
  have hder : HasDerivAt (fun s => (Romik.path params s).1)
      ((Romik.rot t (alphaBetaAt t)).1) t := by
    have h := dot_fixed_hasDerivAt_frontier (w := ((1 : ℝ), 0))
      (path_hasDerivAt_noHidden t)
    simpa [dot] using h
  rw [hder.deriv]
  have htPhys : t ∈ Icc params.phi T := ⟨ht.1.le, le_trans ht.2.le tau_lt_T.le⟩
  have ha := alpha_nonpos htPhys
  have hb := beta_nonneg htPhys
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (lt_trans phi_pos ht.1) (lt_trans (lt_trans ht.2 tau_lt_T)
      (by dsimp [T]; nlinarith [Real.pi_pos]))
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, phi_pos, ht.1], by
      have htT := lt_trans ht.2 tau_lt_T
      simpa [T] using htT⟩
  by_cases htheta : t ≤ params.theta
  · have hphi : ¬ t ≤ params.phi := not_le.mpr ht.1
    have has : alpha t < 0 := by
      simp only [alpha, alphaBetaAt, ite_eq_right hphi, ite_eq_left htheta]
      dsimp [Romik.alphaBeta2]
      nlinarith [b1_upper_frontier, ht.1, phi_pos]
    dsimp [Romik.rot]
    change Real.cos t * alpha t - Real.sin t * beta t < 0
    nlinarith [mul_neg_of_neg_of_pos has hc, mul_nonneg hb hs.le]
  · by_cases heta : t ≤ eta
    · have hphi : ¬ t ≤ params.phi := not_le.mpr ht.1
      have has : alpha t < 0 := by
        simp only [alpha, alphaBetaAt, ite_eq_right hphi, ite_eq_right htheta, ite_eq_left heta]
        dsimp [Romik.alphaBeta3]
        nlinarith [c2_lower_frontier, theta_pos, lt_of_not_ge htheta]
      dsimp [Romik.rot]
      change Real.cos t * alpha t - Real.sin t * beta t < 0
      nlinarith [mul_neg_of_neg_of_pos has hc, mul_nonneg hb hs.le]
    · have hphi : ¬ t ≤ params.phi := not_le.mpr ht.1
      have hbp : 0 < beta t := by
        simp only [beta, alphaBetaAt, ite_eq_right hphi, ite_eq_right htheta, ite_eq_right heta,
          ite_eq_left ht.2.le]
        dsimp [Romik.alphaBeta4]
        nlinarith [d1_lower_frontier, T_upper_frontier,
          lt_trans ht.2 tau_lt_T]
      dsimp [Romik.rot]
      change Real.cos t * alpha t - Real.sin t * beta t < 0
      nlinarith [mul_nonpos_of_nonpos_of_nonneg ha hc.le,
        mul_pos hbp hs]

/-- The core path runs strictly from right to left in horizontal projection. -/
theorem core_path_fst_strictAnti :
    StrictAntiOn (fun t => (Romik.path params t).1) (Icc params.phi tau) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) pathContinuous.fst.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  exact path_fst_deriv_neg ht

/-! ## A single left-to-right parametrization of the three roof arcs -/

/-- The affine reversal which runs through the core path from `tau` to `phi`
while the auxiliary parameter runs from `theta` to `eta`. -/
@[expose]
def coreReverseTime (s : ℝ) : ℝ :=
  tau - ((tau - params.phi) / (eta - params.theta)) *
    (s - params.theta)

private theorem coreReverseTime_theta :
    coreReverseTime params.theta = tau := by
  simp [coreReverseTime]

private theorem coreReverseTime_eta : coreReverseTime eta = params.phi := by
  have hne : eta - params.theta ≠ 0 := sub_ne_zero.mpr theta_lt_eta.ne'
  dsimp [coreReverseTime]
  field_simp [hne]
  ring

private theorem coreReverseTime_strictAnti : StrictAnti coreReverseTime := by
  intro x y hxy
  have hc : 0 < (tau - params.phi) / (eta - params.theta) :=
    div_pos (sub_pos.mpr (lt_trans phi_lt_theta
      (lt_trans theta_lt_eta eta_lt_tau))) (sub_pos.mpr theta_lt_eta)
  have hprod := mul_pos hc (sub_pos.mpr hxy)
  dsimp [coreReverseTime]
  nlinarith [hprod]

private theorem coreReverseTime_mem {s : ℝ}
    (hs : s ∈ Icc params.theta eta) :
    coreReverseTime s ∈ Icc params.phi tau := by
  constructor
  · rw [← coreReverseTime_eta]
    exact coreReverseTime_strictAnti.antitone hs.2
  · rw [← coreReverseTime_theta]
    exact coreReverseTime_strictAnti.antitone hs.1

private theorem coreReverseTime_continuous : Continuous coreReverseTime := by
  unfold coreReverseTime
  fun_prop

/-- A single continuous parametrization of the complete upper niche arc. -/
@[expose]
def nicheTopArc (s : ℝ) : Point :=
  if s ≤ params.theta then D s
  else if s ≤ eta then Romik.path params (coreReverseTime s)
  else B s

private theorem nicheTopArc_of_le_theta {s : ℝ} (hs : s ≤ params.theta) :
    nicheTopArc s = D s := by
  simp [nicheTopArc, hs]

private theorem nicheTopArc_of_middle {s : ℝ}
    (hθ : params.theta < s) (hη : s ≤ eta) :
    nicheTopArc s = Romik.path params (coreReverseTime s) := by
  simp [nicheTopArc, not_le.mpr hθ, hη]

private theorem nicheTopArc_of_late {s : ℝ} (hη : eta < s) :
    nicheTopArc s = B s := by
  simp [nicheTopArc, not_le.mpr (lt_trans theta_lt_eta hη),
    not_le.mpr hη]

theorem nicheTopArc_continuous : Continuous nicheTopArc := by
  have hcore : Continuous
      (fun s : ℝ => Romik.path params (coreReverseTime s)) :=
    pathContinuous.comp coreReverseTime_continuous
  have hcoreB : Continuous (fun s : ℝ =>
      if s ≤ eta then Romik.path params (coreReverseTime s) else B s) := by
    exact hcore.if_le B_continuous continuous_id continuous_const (by
      intro s hs
      subst s
      rw [coreReverseTime_eta]
      exact B_eta_eq_path_phi.symm)
  exact D_continuous.if_le hcoreB continuous_id continuous_const (by
    intro s hs
    subst s
    rw [ite_eq_left theta_lt_eta.le, coreReverseTime_theta]
    exact D_theta_eq_path_tau)

/-- Horizontal projection of the complete upper arc is strictly increasing. -/
theorem nicheTopArc_fst_strictMono :
    StrictMonoOn (fun s => (nicheTopArc s).1) (Icc (0 : ℝ) T) := by
  intro x hx y hy hxy
  change (nicheTopArc x).1 < (nicheTopArc y).1
  by_cases hyθ : y ≤ params.theta
  · have hxD : x ∈ Icc (0 : ℝ) params.theta :=
      ⟨hx.1, le_trans hxy.le hyθ⟩
    have hyD : y ∈ Icc (0 : ℝ) params.theta := ⟨hy.1, hyθ⟩
    rw [nicheTopArc_of_le_theta hxD.2, nicheTopArc_of_le_theta hyθ]
    exact D_fst_strictMono hxD hyD hxy
  · have hθy : params.theta < y := lt_of_not_ge hyθ
    by_cases hxθ : x ≤ params.theta
    · have hxD : x ∈ Icc (0 : ℝ) params.theta := ⟨hx.1, hxθ⟩
      have hθD : params.theta ∈ Icc (0 : ℝ) params.theta :=
        ⟨theta_pos.le, le_rfl⟩
      have hleft := D_fst_strictMono.monotoneOn hxD hθD hxθ
      rw [nicheTopArc_of_le_theta hxθ]
      by_cases hyη : y ≤ eta
      · have hyM : y ∈ Icc params.theta eta := ⟨hθy.le, hyη⟩
        have hcy := coreReverseTime_mem hyM
        have hcytau : coreReverseTime y < tau := by
          rw [← coreReverseTime_theta]
          exact coreReverseTime_strictAnti hθy
        have hright := core_path_fst_strictAnti hcy
          (right_mem_Icc.2 (lt_trans phi_lt_theta
            (lt_trans theta_lt_eta eta_lt_tau)).le) hcytau
        rw [nicheTopArc_of_middle hθy hyη]
        calc
          (D x).1 ≤ (D params.theta).1 := hleft
          _ = (Romik.path params tau).1 := congrArg Prod.fst D_theta_eq_path_tau
          _ < (Romik.path params (coreReverseTime y)).1 := hright
      · have hηy : eta < y := lt_of_not_ge hyη
        have hyB : y ∈ Icc eta T := ⟨hηy.le, hy.2⟩
        have hηB : eta ∈ Icc eta T := ⟨le_rfl, eta_lt_T.le⟩
        have hB := B_fst_strictMono hηB hyB hηy
        have hcore := core_path_fst_strictAnti
          (left_mem_Icc.2 (lt_trans phi_lt_theta
            (lt_trans theta_lt_eta eta_lt_tau)).le)
          (right_mem_Icc.2 (lt_trans phi_lt_theta
            (lt_trans theta_lt_eta eta_lt_tau)).le)
          (lt_trans phi_lt_theta (lt_trans theta_lt_eta eta_lt_tau))
        rw [nicheTopArc_of_late hηy]
        calc
          (D x).1 ≤ (D params.theta).1 := hleft
          _ = (Romik.path params tau).1 := congrArg Prod.fst D_theta_eq_path_tau
          _ < (Romik.path params params.phi).1 := hcore
          _ = (B eta).1 := congrArg Prod.fst B_eta_eq_path_phi.symm
          _ < (B y).1 := hB
    · have hθx : params.theta < x := lt_of_not_ge hxθ
      by_cases hyη : y ≤ eta
      · have hxM : x ∈ Icc params.theta eta :=
          ⟨hθx.le, le_trans hxy.le hyη⟩
        have hyM : y ∈ Icc params.theta eta := ⟨hθy.le, hyη⟩
        have hcyx : coreReverseTime y < coreReverseTime x :=
          coreReverseTime_strictAnti hxy
        rw [nicheTopArc_of_middle hθx hxM.2,
          nicheTopArc_of_middle hθy hyη]
        exact core_path_fst_strictAnti (coreReverseTime_mem hyM)
          (coreReverseTime_mem hxM) hcyx
      · have hηy : eta < y := lt_of_not_ge hyη
        rw [nicheTopArc_of_late hηy]
        by_cases hxη : x ≤ eta
        · have hxM : x ∈ Icc params.theta eta := ⟨hθx.le, hxη⟩
          have hcx := coreReverseTime_mem hxM
          have hpath : (Romik.path params (coreReverseTime x)).1 ≤
              (Romik.path params params.phi).1 :=
            core_path_fst_strictAnti.antitoneOn
              (left_mem_Icc.2 (lt_trans phi_lt_theta
                (lt_trans theta_lt_eta eta_lt_tau)).le)
              hcx hcx.1
          have hyB : y ∈ Icc eta T := ⟨hηy.le, hy.2⟩
          have hB := B_fst_strictMono
            (left_mem_Icc.2 eta_lt_T.le) hyB hηy
          rw [nicheTopArc_of_middle hθx hxη]
          calc
            (Romik.path params (coreReverseTime x)).1 ≤
                (Romik.path params params.phi).1 := hpath
            _ = (B eta).1 := congrArg Prod.fst B_eta_eq_path_phi.symm
            _ < (B y).1 := hB
        · have hηx : eta < x := lt_of_not_ge hxη
          have hxB : x ∈ Icc eta T := ⟨hηx.le, hx.2⟩
          have hyB : y ∈ Icc eta T := ⟨hηy.le, hy.2⟩
          rw [nicheTopArc_of_late hηx]
          exact B_fst_strictMono hxB hyB hxy

theorem nicheTopArc_y_nonneg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    0 ≤ (nicheTopArc s).2 := by
  by_cases hθ : s ≤ params.theta
  · rw [nicheTopArc_of_le_theta hθ]
    exact D_y_nonneg ⟨hs.1, hθ⟩
  · have hθs : params.theta < s := lt_of_not_ge hθ
    by_cases hη : s ≤ eta
    · rw [nicheTopArc_of_middle hθs hη]
      exact path_core_y_nonneg (coreReverseTime_mem ⟨hθs.le, hη⟩)
    · have hηs : eta < s := lt_of_not_ge hη
      rw [nicheTopArc_of_late hηs]
      exact B_y_nonneg ⟨hηs.le, hs.2⟩

theorem nicheTopArc_y_pos {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) :
    0 < (nicheTopArc s).2 := by
  by_cases hθ : s ≤ params.theta
  · rw [nicheTopArc_of_le_theta hθ]
    exact D_y_pos ⟨hs.1, hθ⟩
  · have hθs : params.theta < s := lt_of_not_ge hθ
    by_cases hη : s ≤ eta
    · rw [nicheTopArc_of_middle hθs hη]
      exact path_core_y_pos (coreReverseTime_mem ⟨hθs.le, hη⟩)
    · have hηs : eta < s := lt_of_not_ge hη
      rw [nicheTopArc_of_late hηs]
      exact B_y_pos ⟨hηs.le, hs.2⟩

theorem nicheTopArc_zero : nicheTopArc 0 = D 0 := by
  exact nicheTopArc_of_le_theta theta_pos.le

theorem nicheTopArc_T : nicheTopArc T = B T := by
  exact nicheTopArc_of_late eta_lt_T

theorem coreReverseTime_image :
    coreReverseTime '' Icc params.theta eta = Icc params.phi tau := by
  simpa [coreReverseTime_theta, coreReverseTime_eta] using
    coreReverseTime_continuous.continuousOn.image_Icc_of_antitoneOn
      theta_lt_eta.le
      (coreReverseTime_strictAnti.antitone.antitoneOn (Icc params.theta eta))

/-- The glued arc has exactly the three curve images, with no additional
points introduced by the reparametrization. -/
theorem nicheTopArc_image :
    curveImage nicheTopArc (Icc (0 : ℝ) T) =
      curveImage D (Icc (0 : ℝ) params.theta) ∪
      curveImage (Romik.path params) (Icc params.phi tau) ∪
      curveImage B (Icc eta T) := by
  classical
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    by_cases hθ : s ≤ params.theta
    · left; left
      exact ⟨s, ⟨hs.1, hθ⟩, (nicheTopArc_of_le_theta hθ).symm⟩
    · have hθs : params.theta < s := lt_of_not_ge hθ
      by_cases hη : s ≤ eta
      · left; right
        exact ⟨coreReverseTime s, coreReverseTime_mem ⟨hθs.le, hη⟩,
          (nicheTopArc_of_middle hθs hη).symm⟩
      · right
        have hηs : eta < s := lt_of_not_ge hη
        exact ⟨s, ⟨hηs.le, hs.2⟩, (nicheTopArc_of_late hηs).symm⟩
  · rintro ((⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨s, hs, rfl⟩)
    · exact ⟨s, ⟨hs.1, le_trans hs.2 theta_lt_T.le⟩,
        nicheTopArc_of_le_theta hs.2⟩
    · rw [← coreReverseTime_image] at ht
      rcases ht with ⟨s, hs, rfl⟩
      by_cases hst : s = params.theta
      · subst s
        refine ⟨params.theta, ⟨theta_pos.le, theta_lt_T.le⟩, ?_⟩
        rw [nicheTopArc_of_le_theta le_rfl, coreReverseTime_theta]
        exact D_theta_eq_path_tau
      · have hθs : params.theta < s := lt_of_le_of_ne hs.1 (Ne.symm hst)
        exact ⟨s, ⟨le_trans theta_pos.le hs.1,
          le_trans hs.2 eta_lt_T.le⟩,
          nicheTopArc_of_middle hθs hs.2⟩
    · by_cases hse : s = eta
      · subst s
        refine ⟨eta, ⟨le_trans theta_pos.le theta_lt_eta.le, eta_lt_T.le⟩, ?_⟩
        rw [nicheTopArc_of_middle theta_lt_eta le_rfl, coreReverseTime_eta]
        exact B_eta_eq_path_phi.symm
      · have hηs : eta < s := lt_of_le_of_ne hs.1 (Ne.symm hse)
        exact ⟨s, ⟨le_trans (le_trans theta_pos.le theta_lt_eta.le) hs.1, hs.2⟩,
          nicheTopArc_of_late hηs⟩

/-- A vertically filled strict subgraph over a compact interval. -/
def strictSubgraphRegion (a b : ℝ) (H : ℝ → ℝ) : Set Point :=
  {p | p.1 ∈ Icc a b ∧ 0 ≤ p.2 ∧ p.2 < H p.1}

/-- The closed vertical fill associated with `strictSubgraphRegion`. -/
def closedSubgraphRegion (a b : ℝ) (H : ℝ → ℝ) : Set Point :=
  {p | p.1 ∈ Icc a b ∧ 0 ≤ p.2 ∧ p.2 ≤ H p.1}

/-- The base together with the graph of the roof. -/
def strictSubgraphBoundary (a b : ℝ) (H : ℝ → ℝ) : Set Point :=
  {p | p.1 ∈ Icc a b ∧ (p.2 = 0 ∨ p.2 = H p.1)}

private theorem strictSubgraphRegion_as_image
    {a b : ℝ} {H : ℝ → ℝ}
    (hHpos : ∀ x ∈ Ioo a b, 0 < H x)
    (ha : H a = 0) (hb : H b = 0) :
    (fun z : ℝ × ℝ => (z.1, z.2 * H z.1)) ''
        (Ioo a b ×ˢ Ico (0 : ℝ) 1) =
      strictSubgraphRegion a b H := by
  classical
  ext p
  constructor
  · rintro ⟨z, ⟨hzx, hzs⟩, rfl⟩
    have htop := hHpos z.1 hzx
    refine ⟨⟨hzx.1.le, hzx.2.le⟩, ?_, ?_⟩
    · exact mul_nonneg hzs.1 htop.le
    · exact mul_lt_of_lt_one_left htop hzs.2
  · rintro ⟨hx, hy0, hy⟩
    have hxa : a < p.1 := by
      rcases hx.1.eq_or_lt with h | h
      · rw [← h, ha] at hy
        linarith
      · exact h
    have hxb : p.1 < b := by
      rcases hx.2.eq_or_lt with h | h
      · rw [h, hb] at hy
        linarith
      · exact h
    have htop := hHpos p.1 ⟨hxa, hxb⟩
    let s : ℝ := p.2 / H p.1
    have hs : s ∈ Ico (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg hy0 htop.le
      · exact (div_lt_one htop).2 hy
    refine ⟨(p.1, s), ⟨⟨hxa, hxb⟩, hs⟩, ?_⟩
    apply Prod.ext
    · rfl
    · dsimp [s]
      field_simp [ne_of_gt htop]

private theorem closedSubgraphRegion_as_image
    {a b : ℝ} {H : ℝ → ℝ}
    (hHnonneg : ∀ x ∈ Icc a b, 0 ≤ H x) :
    (fun z : ℝ × ℝ => (z.1, z.2 * H z.1)) ''
        (Icc a b ×ˢ Icc (0 : ℝ) 1) =
      closedSubgraphRegion a b H := by
  classical
  ext p
  constructor
  · rintro ⟨z, ⟨hzx, hzs⟩, rfl⟩
    have htop := hHnonneg z.1 hzx
    refine ⟨hzx, mul_nonneg hzs.1 htop, ?_⟩
    exact mul_le_of_le_one_left htop hzs.2
  · rintro ⟨hx, hy0, hy⟩
    have htop := hHnonneg p.1 hx
    by_cases hzero : H p.1 = 0
    · have hpy : p.2 = 0 := by linarith
      refine ⟨(p.1, 0), ⟨hx, by norm_num⟩, ?_⟩
      apply Prod.ext
      · rfl
      · simpa only [zero_mul] using hpy.symm
    · have htop' : 0 < H p.1 := lt_of_le_of_ne htop (Ne.symm hzero)
      let s : ℝ := p.2 / H p.1
      have hs : s ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg hy0 htop'.le
        · exact (div_le_one htop').2 hy
      refine ⟨(p.1, s), ⟨hx, hs⟩, ?_⟩
      apply Prod.ext
      · rfl
      · dsimp [s]
        field_simp [hzero]

theorem closure_strictSubgraphRegion
    {a b : ℝ} {H : ℝ → ℝ} (hab : a < b)
    (hH : Continuous H)
    (hHnonneg : ∀ x ∈ Icc a b, 0 ≤ H x)
    (hHpos : ∀ x ∈ Ioo a b, 0 < H x)
    (ha : H a = 0) (hb : H b = 0) :
    closure (strictSubgraphRegion a b H) = closedSubgraphRegion a b H := by
  let P : Set (ℝ × ℝ) := Ioo a b ×ˢ Ico (0 : ℝ) 1
  let Q : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (0 : ℝ) 1
  let F : ℝ × ℝ → Point := fun z => (z.1, z.2 * H z.1)
  have hclP : closure P = Q := by
    simp only [P, Q, closure_prod_eq, closure_Ioo hab.ne,
      closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
  have hQcompact : IsCompact Q := by
    exact isCompact_Icc.prod isCompact_Icc
  have hF : Continuous F := by
    dsimp [F]
    exact continuous_fst.prodMk (continuous_snd.mul (hH.comp continuous_fst))
  have hPcompact : IsCompact (closure P) := by
    rw [hclP]
    exact hQcompact
  calc
    closure (strictSubgraphRegion a b H) = closure (F '' P) := by
      rw [strictSubgraphRegion_as_image hHpos ha hb]
    _ = F '' closure P :=
      (image_closure_of_isCompact hPcompact hF.continuousOn).symm
    _ = F '' Q := by rw [hclP]
    _ = closedSubgraphRegion a b H :=
      closedSubgraphRegion_as_image hHnonneg

theorem interior_strictSubgraphRegion
    {a b : ℝ} {H : ℝ → ℝ} (hH : Continuous H) :
    interior (strictSubgraphRegion a b H) =
      {p | p.1 ∈ Ioo a b ∧ 0 < p.2 ∧ p.2 < H p.1} := by
  let O : Set Point := {p | p.1 ∈ Ioo a b ∧ 0 < p.2 ∧ p.2 < H p.1}
  have hOopen : IsOpen O := by
    dsimp [O]
    exact (isOpen_Ioo.preimage continuous_fst).inter
      ((isOpen_Ioi.preimage continuous_snd).inter
        (isOpen_lt continuous_snd (hH.comp continuous_fst)))
  apply Set.Subset.antisymm
  · intro p hp
    have hpS := interior_subset hp
    have hxmono : strictSubgraphRegion a b H ⊆ Icc a b ×ˢ (Set.univ : Set ℝ) := by
      intro q hq
      exact ⟨hq.1, Set.mem_univ _⟩
    have hymono : strictSubgraphRegion a b H ⊆ (Set.univ : Set ℝ) ×ˢ Ici 0 := by
      intro q hq
      exact ⟨Set.mem_univ _, hq.2.1⟩
    have hx := interior_mono hxmono hp
    have hy := interior_mono hymono hp
    rw [interior_prod_eq, interior_Icc, interior_univ] at hx
    rw [interior_prod_eq, interior_univ, interior_Ici] at hy
    exact ⟨hx.1, hy.2, hpS.2.2⟩
  · apply interior_maximal
    · intro p hp
      exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2.1.le, hp.2.2⟩
    · exact hOopen

/-- The frontier of a positive strict vertical subgraph consists exactly of
its roof and its base. -/
theorem frontier_strictSubgraphRegion
    {a b : ℝ} {H : ℝ → ℝ} (hab : a < b)
    (hH : Continuous H)
    (hHnonneg : ∀ x ∈ Icc a b, 0 ≤ H x)
    (hHpos : ∀ x ∈ Ioo a b, 0 < H x)
    (ha : H a = 0) (hb : H b = 0) :
    frontier (strictSubgraphRegion a b H) = strictSubgraphBoundary a b H := by
  rw [frontier, closure_strictSubgraphRegion hab hH hHnonneg hHpos ha hb,
    interior_strictSubgraphRegion hH]
  ext p
  simp only [Set.mem_sdiff, closedSubgraphRegion, strictSubgraphBoundary,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hx, hy0, hyH⟩, hnot⟩
    refine ⟨hx, ?_⟩
    by_cases hya : p.2 = 0
    · exact Or.inl hya
    right
    by_contra hyne
    apply hnot
    refine ⟨?_, lt_of_le_of_ne hy0 (Ne.symm hya), lt_of_le_of_ne hyH hyne⟩
    constructor
    · apply lt_of_le_of_ne hx.1
      intro heq
      have hp0 : p.2 = 0 := by
        rw [← heq, ha] at hyH
        linarith
      exact hya hp0
    · apply lt_of_le_of_ne hx.2
      intro heq
      have hp0 : p.2 = 0 := by
        rw [heq, hb] at hyH
        linarith
      exact hya hp0
  · rintro ⟨hx, hbase | hroof⟩
    · refine ⟨⟨hx, ?_, ?_⟩, ?_⟩
      · simp [hbase]
      · simpa [hbase] using hHnonneg p.1 hx
      · intro hstrict
        rw [hbase] at hstrict
        exact (lt_irrefl (0 : ℝ)) hstrict.2.1
    · refine ⟨⟨hx, ?_, hroof.le⟩, ?_⟩
      · rw [hroof]
        exact hHnonneg p.1 hx
      · intro hstrict
        exact (lt_irrefl (H p.1)) (hroof ▸ hstrict.2.2)

/-! ## Turning a monotone roof arc into a global continuous graph -/

/-- Identify a strictly horizontally increasing arc with its horizontal coordinate interval. -/
noncomputable def horizontalOrderIso
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) :
    Icc a b ≃o Icc (γ a).1 (γ b).1 := by
  have himage :
      (fun t ↦ (γ t).1) '' Icc a b = Icc (γ a).1 (γ b).1 :=
    hγ.fst.image_Icc_of_monotoneOn hab.le hx.monotoneOn
  exact
    (StrictMonoOn.orderIso (fun t ↦ (γ t).1) (Icc a b) hx).trans
      (Set.orderIsoOfEq _ _ himage)

@[simp]
theorem horizontalOrderIso_apply_val
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b))
    (t : Icc a b) :
    ((horizontalOrderIso γ hab hγ hx t : Icc (γ a).1 (γ b).1) : ℝ) =
      (γ t.1).1 := by
  rfl

/-- Express the arc’s vertical coordinate as a function of its horizontal coordinate. -/
noncomputable def roofOnHorizontalRange
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) :
    Icc (γ a).1 (γ b).1 → ℝ :=
  fun X ↦ (γ ((horizontalOrderIso γ hab hγ hx).symm X).1).2

theorem continuous_roofOnHorizontalRange
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) :
    Continuous (roofOnHorizontalRange γ hab hγ hx) := by
  exact continuous_snd.comp
    (hγ.domRestrict.comp (horizontalOrderIso γ hab hγ hx).symm.continuous)

theorem horizontal_endpoints_le
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) :
    (γ a).1 ≤ (γ b).1 :=
  (hx (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab).le

/-- Extend the roof graph to the real line by clamping to its endpoint interval. -/
noncomputable def monotoneCurveRoof
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) : ℝ → ℝ :=
  Set.IccExtend (horizontal_endpoints_le γ hab hx)
    (roofOnHorizontalRange γ hab hγ hx)

theorem continuous_monotoneCurveRoof
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) :
    Continuous (monotoneCurveRoof γ hab hγ hx) := by
  exact (continuous_roofOnHorizontalRange γ hab hγ hx).Icc_extend'

private theorem horizontal_mem_range
    (γ : ℝ → Point) {a b t : ℝ} (hab : a < b)
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b))
    (ht : t ∈ Icc a b) :
    (γ t).1 ∈ Icc (γ a).1 (γ b).1 := by
  exact ⟨hx.monotoneOn (left_mem_Icc.2 hab.le) ht ht.1,
    hx.monotoneOn ht (right_mem_Icc.2 hab.le) ht.2⟩

theorem monotoneCurveRoof_at
    (γ : ℝ → Point) {a b t : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b))
    (ht : t ∈ Icc a b) :
    monotoneCurveRoof γ hab hγ hx (γ t).1 = (γ t).2 := by
  let e := horizontalOrderIso γ hab hγ hx
  have htr := horizontal_mem_range γ hab hx ht
  have heq : e ⟨t, ht⟩ = ⟨(γ t).1, htr⟩ := by
    apply Subtype.ext
    rfl
  have hinv : e.symm ⟨(γ t).1, htr⟩ = ⟨t, ht⟩ := by
    rw [← heq, e.symm_apply_apply]
  rw [monotoneCurveRoof, Set.IccExtend_of_mem _ _ htr]
  change (γ (e.symm ⟨(γ t).1, htr⟩).1).2 = (γ t).2
  rw [hinv]

theorem verticalFill_eq_strictSubgraphRegion
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) :
    verticalFill γ (Icc a b) =
      strictSubgraphRegion (γ a).1 (γ b).1
        (monotoneCurveRoof γ hab hγ hx) := by
  ext p
  constructor
  · rintro ⟨t, ht, hxt, hy0, hy⟩
    have htr := horizontal_mem_range γ hab hx ht
    refine ⟨?_, hy0, ?_⟩
    · simpa [hxt] using htr
    · rw [hxt, monotoneCurveRoof_at γ hab hγ hx ht]
      exact hy
  · rintro ⟨hpx, hy0, hy⟩
    let e := horizontalOrderIso γ hab hγ hx
    let ts : Icc a b := e.symm ⟨p.1, hpx⟩
    have heval := congrArg Subtype.val
      ((horizontalOrderIso γ hab hγ hx).apply_symm_apply ⟨p.1, hpx⟩)
    have hxt : (γ ts.1).1 = p.1 := by
      change
        (γ ((horizontalOrderIso γ hab hγ hx).symm ⟨p.1, hpx⟩).1).1 = p.1
      simpa only [horizontalOrderIso_apply_val] using heval
    refine ⟨ts.1, ts.2, hxt.symm, hy0, ?_⟩
    rw [← hxt, monotoneCurveRoof_at γ hab hγ hx ts.2] at hy
    exact hy

theorem curveImage_eq_roofGraph
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) :
    curveImage γ (Icc a b) =
      {p | p.1 ∈ Icc (γ a).1 (γ b).1 ∧
        p.2 = monotoneCurveRoof γ hab hγ hx p.1} := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨horizontal_mem_range γ hab hx ht,
      (monotoneCurveRoof_at γ hab hγ hx ht).symm⟩
  · rintro ⟨hpx, hpy⟩
    let e := horizontalOrderIso γ hab hγ hx
    let ts : Icc a b := e.symm ⟨p.1, hpx⟩
    have heval := congrArg Subtype.val
      ((horizontalOrderIso γ hab hγ hx).apply_symm_apply ⟨p.1, hpx⟩)
    have hxt : (γ ts.1).1 = p.1 := by
      change
        (γ ((horizontalOrderIso γ hab hγ hx).symm ⟨p.1, hpx⟩).1).1 = p.1
      simpa only [horizontalOrderIso_apply_val] using heval
    refine ⟨ts.1, ts.2, ?_⟩
    apply Prod.ext
    · exact hxt
    · calc
        (γ ts.1).2 = monotoneCurveRoof γ hab hγ hx (γ ts.1).1 :=
          (monotoneCurveRoof_at γ hab hγ hx ts.2).symm
        _ = monotoneCurveRoof γ hab hγ hx p.1 := by rw [hxt]
        _ = p.2 := hpy.symm

theorem T_pos_frontier : 0 < T := by
  dsimp [T]
  nlinarith [Real.pi_pos]

/-- The continuous roof function determined by the complete niche top arc. -/
noncomputable def nicheRoof : ℝ → ℝ :=
  monotoneCurveRoof nicheTopArc T_pos_frontier
    nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono

theorem nicheRoof_continuous : Continuous nicheRoof :=
  continuous_monotoneCurveRoof nicheTopArc T_pos_frontier
    nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono

theorem nicheRoof_at_topArc {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    nicheRoof (nicheTopArc s).1 = (nicheTopArc s).2 :=
  monotoneCurveRoof_at nicheTopArc T_pos_frontier
    nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono hs

theorem nicheRoof_nonneg {X : ℝ}
    (hX : X ∈ Icc (D 0).1 (B T).1) : 0 ≤ nicheRoof X := by
  have hends : Icc (D 0).1 (B T).1 =
      Icc (nicheTopArc 0).1 (nicheTopArc T).1 := by
    rw [nicheTopArc_zero, nicheTopArc_T]
  rw [hends] at hX
  let e := horizontalOrderIso nicheTopArc T_pos_frontier
    nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono
  let s : Icc (0 : ℝ) T := e.symm ⟨X, hX⟩
  have heval := congrArg Subtype.val
    ((horizontalOrderIso nicheTopArc T_pos_frontier
      nicheTopArc_continuous.continuousOn
      nicheTopArc_fst_strictMono).apply_symm_apply ⟨X, hX⟩)
  have hxarc : (nicheTopArc s.1).1 = X := by
    change
      (nicheTopArc ((horizontalOrderIso nicheTopArc T_pos_frontier
        nicheTopArc_continuous.continuousOn
        nicheTopArc_fst_strictMono).symm ⟨X, hX⟩).1).1 = X
    simpa only [horizontalOrderIso_apply_val] using heval
  rw [← hxarc, nicheRoof_at_topArc s.2]
  exact nicheTopArc_y_nonneg s.2

theorem nicheRoof_pos {X : ℝ}
    (hX : X ∈ Ioo (D 0).1 (B T).1) : 0 < nicheRoof X := by
  have hends : Ioo (D 0).1 (B T).1 =
      Ioo (nicheTopArc 0).1 (nicheTopArc T).1 := by
    rw [nicheTopArc_zero, nicheTopArc_T]
  rw [hends] at hX
  let e := horizontalOrderIso nicheTopArc T_pos_frontier
    nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono
  have hXcc : X ∈ Icc (nicheTopArc 0).1 (nicheTopArc T).1 :=
    ⟨hX.1.le, hX.2.le⟩
  let s : Icc (0 : ℝ) T := e.symm ⟨X, hXcc⟩
  have heval := congrArg Subtype.val
    ((horizontalOrderIso nicheTopArc T_pos_frontier
      nicheTopArc_continuous.continuousOn
      nicheTopArc_fst_strictMono).apply_symm_apply ⟨X, hXcc⟩)
  have hxarc : (nicheTopArc s.1).1 = X := by
    change
      (nicheTopArc ((horizontalOrderIso nicheTopArc T_pos_frontier
        nicheTopArc_continuous.continuousOn
        nicheTopArc_fst_strictMono).symm ⟨X, hXcc⟩).1).1 = X
    simpa only [horizontalOrderIso_apply_val] using heval
  have hs0 : 0 < s.1 := by
    by_contra hn
    have hszero : s.1 = 0 := le_antisymm (le_of_not_gt hn) s.2.1
    have hxzero : (nicheTopArc 0).1 = X := by
      simpa [hszero] using hxarc
    exact (ne_of_lt hX.1) hxzero
  have hsT : s.1 < T := by
    by_contra hn
    have hsT' : s.1 = T := le_antisymm s.2.2 (le_of_not_gt hn)
    have hxT : (nicheTopArc T).1 = X := by
      simpa [hsT'] using hxarc
    exact (ne_of_gt hX.2) hxT
  rw [← hxarc, nicheRoof_at_topArc s.2]
  exact nicheTopArc_y_pos ⟨hs0, hsT⟩

theorem nicheRoof_left : nicheRoof (D 0).1 = 0 := by
  rw [← nicheTopArc_zero, nicheRoof_at_topArc (left_mem_Icc.2 T_pos_frontier.le),
    nicheTopArc_zero]
  exact D_zero_y_zero

theorem nicheRoof_right : nicheRoof (B T).1 = 0 := by
  rw [← nicheTopArc_T, nicheRoof_at_topArc (right_mem_Icc.2 T_pos_frontier.le),
    nicheTopArc_T]
  exact B_T_y_zero

private theorem nicheTopArc_verticalFill :
    verticalFill nicheTopArc (Icc (0 : ℝ) T) = certifiedNicheRegion := by
  classical
  ext q
  constructor
  · rintro ⟨s, hs, hx, hy0, hy⟩
    have htop : nicheTopArc s ∈
        curveImage D (Icc (0 : ℝ) params.theta) ∪
        curveImage (Romik.path params) (Icc params.phi tau) ∪
        curveImage B (Icc eta T) := by
      rw [← nicheTopArc_image]
      exact ⟨s, hs, rfl⟩
    rcases htop with (⟨r, hr, her⟩ | ⟨r, hr, her⟩) | ⟨r, hr, her⟩
    · exact Or.inl (Or.inl ⟨r, hr, by simpa [her] using hx,
        hy0, by simpa [her] using hy⟩)
    · exact Or.inl (Or.inr ⟨r, hr, by simpa [her] using hx,
        hy0, by simpa [her] using hy⟩)
    · exact Or.inr ⟨r, hr, by simpa [her] using hx,
        hy0, by simpa [her] using hy⟩
  · intro hq
    rcases hq with (⟨r, hr, hx, hy0, hy⟩ | ⟨r, hr, hx, hy0, hy⟩) |
      ⟨r, hr, hx, hy0, hy⟩
    · have htop : D r ∈ curveImage nicheTopArc (Icc (0 : ℝ) T) := by
        rw [nicheTopArc_image]
        exact Or.inl (Or.inl ⟨r, hr, rfl⟩)
      rcases htop with ⟨s, hs, her⟩
      exact ⟨s, hs, by simpa [her] using hx,
        hy0, by simpa [her] using hy⟩
    · have htop : Romik.path params r ∈
          curveImage nicheTopArc (Icc (0 : ℝ) T) := by
        rw [nicheTopArc_image]
        exact Or.inl (Or.inr ⟨r, hr, rfl⟩)
      rcases htop with ⟨s, hs, her⟩
      exact ⟨s, hs, by simpa [her] using hx,
        hy0, by simpa [her] using hy⟩
    · have htop : B r ∈ curveImage nicheTopArc (Icc (0 : ℝ) T) := by
        rw [nicheTopArc_image]
        exact Or.inr ⟨r, hr, rfl⟩
      rcases htop with ⟨s, hs, her⟩
      exact ⟨s, hs, by simpa [her] using hx,
        hy0, by simpa [her] using hy⟩

/-- The three certified fills form one strict subgraph. -/
theorem certifiedNicheRegion_eq_strictSubgraph :
    certifiedNicheRegion =
      strictSubgraphRegion (D 0).1 (B T).1 nicheRoof := by
  rw [← nicheTopArc_verticalFill,
    verticalFill_eq_strictSubgraphRegion nicheTopArc T_pos_frontier
      nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono,
    nicheTopArc_zero, nicheTopArc_T]
  rfl

private theorem lineSegment_horizontal
    {a b : Point} (hab : a.1 < b.1) (ha : a.2 = 0) (hb : b.2 = 0) :
    lineSegment a b = {p | p.1 ∈ Icc a.1 b.1 ∧ p.2 = 0} := by
  classical
  ext p
  constructor
  · rintro ⟨r, hr, rfl⟩
    constructor
    · have hba : 0 ≤ b.1 - a.1 := sub_nonneg.mpr hab.le
      constructor
      · have hmul : 0 ≤ r * (b.1 - a.1) := mul_nonneg hr.1 hba
        nlinarith [hmul]
      · have hmul : 0 ≤ (1 - r) * (b.1 - a.1) :=
          mul_nonneg (sub_nonneg.mpr hr.2) hba
        nlinarith [hmul]
    · simp [ha, hb]
  · rintro ⟨hx, hy⟩
    let r : ℝ := (p.1 - a.1) / (b.1 - a.1)
    have hden : 0 < b.1 - a.1 := sub_pos.mpr hab
    have hr : r ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hx.1) hden.le
      · exact (div_le_one hden).2 (by linarith [hx.2])
    refine ⟨r, hr, ?_⟩
    apply Prod.ext
    · dsimp [r]
      field_simp [ne_of_gt hden]
      ring
    · simp [ha, hb, hy]

private theorem niche_horizontal_endpoints : (D 0).1 < (B T).1 := by
  have h := nicheTopArc_fst_strictMono
    (left_mem_Icc.2 T_pos_frontier.le)
    (right_mem_Icc.2 T_pos_frontier.le) T_pos_frontier
  simpa [nicheTopArc_zero, nicheTopArc_T] using h

theorem claimedNicheBoundary_eq_subgraphBoundary :
    claimedNicheBoundary =
      strictSubgraphBoundary (D 0).1 (B T).1 nicheRoof := by
  have hbase := lineSegment_horizontal niche_horizontal_endpoints
    D_zero_y_zero B_T_y_zero
  have hroof := curveImage_eq_roofGraph nicheTopArc T_pos_frontier
    nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono
  rw [nicheTopArc_zero, nicheTopArc_T] at hroof
  ext p
  constructor
  · intro hp
    change p ∈ lineSegment (D 0) (B T) ∪
      curveImage B (Icc eta T) ∪
      curveImage (Romik.path params) (Icc params.phi tau) ∪
      curveImage D (Icc 0 params.theta) at hp
    have hp' : p ∈ lineSegment (D 0) (B T) ∨
        p ∈ curveImage nicheTopArc (Icc (0 : ℝ) T) := by
      rw [nicheTopArc_image]
      rcases hp with ((hb | hB) | hpath) | hD
      · exact Or.inl hb
      · exact Or.inr (Or.inr hB)
      · exact Or.inr (Or.inl (Or.inr hpath))
      · exact Or.inr (Or.inl (Or.inl hD))
    rcases hp' with hb | hr
    · rw [hbase] at hb
      exact ⟨hb.1, Or.inl hb.2⟩
    · rw [hroof] at hr
      exact ⟨hr.1, Or.inr hr.2⟩
  · rintro ⟨hx, hbase' | hroof'⟩
    · have hb : p ∈ lineSegment (D 0) (B T) := by
        rw [hbase]
        exact ⟨hx, hbase'⟩
      change p ∈ lineSegment (D 0) (B T) ∪
        curveImage B (Icc eta T) ∪
        curveImage (Romik.path params) (Icc params.phi tau) ∪
        curveImage D (Icc 0 params.theta)
      exact Or.inl (Or.inl (Or.inl hb))
    · have hr : p ∈ curveImage nicheTopArc (Icc (0 : ℝ) T) := by
        rw [hroof]
        exact ⟨hx, hroof'⟩
      rw [nicheTopArc_image] at hr
      change p ∈ lineSegment (D 0) (B T) ∪
        curveImage B (Icc eta T) ∪
        curveImage (Romik.path params) (Icc params.phi tau) ∪
        curveImage D (Icc 0 params.theta)
      rcases hr with (hD | hpath) | hB
      · exact Or.inr hD
      · exact Or.inl (Or.inr hpath)
      · exact Or.inl (Or.inl (Or.inr hB))

/-- Direct frontier calculation for the certified three-fill region. -/
theorem frontier_certifiedNicheRegion :
    frontier certifiedNicheRegion = claimedNicheBoundary := by
  rw [certifiedNicheRegion_eq_strictSubgraph,
    frontier_strictSubgraphRegion niche_horizontal_endpoints nicheRoof_continuous
      (by intro X hX; exact nicheRoof_nonneg hX)
      (by intro X hX; exact nicheRoof_pos hX)
      nicheRoof_left nicheRoof_right,
    ← claimedNicheBoundary_eq_subgraphBoundary]

/-! ## Literal instantaneous wedges lie below the certified graph -/

private theorem sin_pos_frontier {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    0 < Real.sin t :=
  Real.sin_pos_of_pos_of_lt_pi ht.1
    (lt_trans ht.2 (by dsimp [T]; nlinarith [Real.pi_pos]))

private theorem cos_pos_frontier {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    0 < Real.cos t :=
  Real.cos_pos_of_mem_Ioo
    ⟨by nlinarith [Real.pi_pos, ht.1], by simpa [T] using ht.2⟩

private theorem instantRoof_le_of_u_outside {t X Y : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hu : 0 ≤ dot ((X, Y) - Romik.path params t) (u t)) :
    instantRoof t X ≤ Y := by
  apply le_trans (min_le_left _ _)
  unfold bRoof
  apply (div_le_iff₀ (sin_pos_frontier ht)).2
  dsimp [dot, u] at hu ⊢
  nlinarith

private theorem instantRoof_le_of_v_outside {t X Y : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hv : 0 ≤ dot ((X, Y) - Romik.path params t) (v t)) :
    instantRoof t X ≤ Y := by
  apply le_trans (min_le_right _ _)
  unfold dRoof
  apply (div_le_iff₀ (cos_pos_frontier ht)).2
  dsimp [dot, v] at hv ⊢
  nlinarith

/-- A core path point dominates every instantaneous roof at its horizontal
coordinate.  This is the exact geometric content of the two no-hidden
inequalities. -/
theorem core_is_upper_envelope {r : ℝ} (hr : r ∈ Icc params.phi tau) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      instantRoof t (Romik.path params r).1 ≤ (Romik.path params r).2 := by
  intro t ht
  by_cases htr : r ≤ t
  · have hU : 0 ≤ dot (Romik.path params r - Romik.path params t) (u t) :=
      noHiddenU_direct r ⟨hr.1, le_trans hr.2 tau_lt_T.le⟩ t
        ⟨htr, ht.2.le⟩
    exact instantRoof_le_of_u_outside ht hU
  · have htr' : t ≤ r := le_of_not_ge htr
    have hV : 0 ≤ dot (Romik.path params r - Romik.path params t) (v t) :=
      noHiddenV_direct t ⟨ht.1.le, le_trans htr' hr.2⟩ r ⟨htr', hr.2⟩
    exact instantRoof_le_of_v_outside ht hV

/-- Every point of the glued certified roof dominates every instantaneous
wall roof at its horizontal coordinate. -/
theorem nicheTopArc_is_upper_envelope {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (ht : t ∈ Ioo (0 : ℝ) T) :
    instantRoof t (nicheTopArc s).1 ≤ (nicheTopArc s).2 := by
  by_cases hθ : s ≤ params.theta
  · rw [nicheTopArc_of_le_theta hθ]
    rcases D_boundary_outside ht ⟨hs.1, hθ⟩ with hu | hv
    · exact instantRoof_le_of_u_outside ht hu
    · exact instantRoof_le_of_v_outside ht hv
  · have hθs : params.theta < s := lt_of_not_ge hθ
    by_cases hη : s ≤ eta
    · rw [nicheTopArc_of_middle hθs hη]
      exact core_is_upper_envelope (coreReverseTime_mem ⟨hθs.le, hη⟩) t ht
    · have hηs : eta < s := lt_of_not_ge hη
      rw [nicheTopArc_of_late hηs]
      rcases B_boundary_outside ht ⟨hηs.le, hs.2⟩ with hu | hv
      · exact instantRoof_le_of_u_outside ht hu
      · exact instantRoof_le_of_v_outside ht hv

private theorem niche_point_horizontal_range {q : Point}
    (hq : q ∈ Romik.niche params) : q.1 ∈ Ioo (D 0).1 (B T).1 := by
  rcases hq with ⟨hqFan, t, ht, hquad⟩
  have hq0 : 0 ≤ q.2 := by simpa [capFan] using hqFan
  have hwalls := hquad
  change
    dot (q - Romik.path params t) (u t) < 0 ∧
      dot (q - Romik.path params t) (v t) < 0 at hwalls
  have hBT := B_T_u_nonneg ht
  have hqBT : dot (q - B T) (u t) < 0 := by
    unfold dot at hwalls hBT ⊢
    dsimp [u] at hwalls hBT ⊢
    linarith
  have hright : q.1 < (B T).1 := by
    by_contra hn
    have hdx : 0 ≤ q.1 - (B T).1 := sub_nonneg.mpr (le_of_not_gt hn)
    have hxterm : 0 ≤ (q.1 - (B T).1) * Real.cos t :=
      mul_nonneg hdx (cos_pos_frontier ht).le
    have hyterm : 0 ≤ (q.2 - (B T).2) * Real.sin t := by
      rw [B_T_y_zero]
      simpa using mul_nonneg hq0 (sin_pos_frontier ht).le
    dsimp [dot, u] at hqBT
    linarith
  have hD := D_zero_v_nonneg ht
  have hqD : dot (q - D 0) (v t) < 0 := by
    unfold dot at hwalls hD ⊢
    dsimp [v] at hwalls hD ⊢
    linarith
  have hleft : (D 0).1 < q.1 := by
    by_contra hn
    have hdx : q.1 - (D 0).1 ≤ 0 := sub_nonpos.mpr (le_of_not_gt hn)
    have hxterm : 0 ≤ (q.1 - (D 0).1) * (-Real.sin t) :=
      mul_nonneg_of_nonpos_of_nonpos hdx (neg_nonpos.mpr (sin_pos_frontier ht).le)
    have hyterm : 0 ≤ (q.2 - (D 0).2) * Real.cos t := by
      rw [D_zero_y_zero]
      simpa using mul_nonneg hq0 (cos_pos_frontier ht).le
    dsimp [dot, v] at hqD
    linarith
  exact ⟨hleft, hright⟩

private theorem niche_subset_certifiedNicheRegion :
    Romik.niche params ⊆ certifiedNicheRegion := by
  intro q hq
  rcases hq with ⟨hqFan, t, ht, hquad⟩
  have hqAll : q ∈ Romik.niche params := ⟨hqFan, t, ht, hquad⟩
  have hXopen := niche_point_horizontal_range hqAll
  have hX : q.1 ∈ Icc (nicheTopArc 0).1 (nicheTopArc T).1 := by
    simpa [nicheTopArc_zero, nicheTopArc_T] using
      (show q.1 ∈ Icc (D 0).1 (B T).1 from ⟨hXopen.1.le, hXopen.2.le⟩)
  let e := horizontalOrderIso nicheTopArc T_pos_frontier
    nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono
  let s : Icc (0 : ℝ) T := e.symm ⟨q.1, hX⟩
  have heval := congrArg Subtype.val
    ((horizontalOrderIso nicheTopArc T_pos_frontier
      nicheTopArc_continuous.continuousOn
      nicheTopArc_fst_strictMono).apply_symm_apply ⟨q.1, hX⟩)
  have hxarc : (nicheTopArc s.1).1 = q.1 := by
    change
      (nicheTopArc ((horizontalOrderIso nicheTopArc T_pos_frontier
        nicheTopArc_continuous.continuousOn
        nicheTopArc_fst_strictMono).symm ⟨q.1, hX⟩).1).1 = q.1
    simpa only [horizontalOrderIso_apply_val] using heval
  have hinstant : q.2 < instantRoof t q.1 := by
    have hw := (mem_innerQuadrant_iff_roofs ht).1 hquad
    simpa [instantRoof, lt_min_iff] using hw
  have hupper := nicheTopArc_is_upper_envelope s.2 ht
  have hroofAt := nicheRoof_at_topArc s.2
  have hq0 : 0 ≤ q.2 := by simpa [capFan] using hqFan
  rw [certifiedNicheRegion_eq_strictSubgraph]
  refine ⟨by simpa [nicheTopArc_zero, nicheTopArc_T] using hX, hq0, ?_⟩
  calc
    q.2 < instantRoof t q.1 := hinstant
    _ ≤ (nicheTopArc s.1).2 := by simpa [hxarc] using hupper
    _ = nicheRoof q.1 := by rw [← hroofAt, hxarc]

private theorem certifiedNicheRegion_subset_niche :
    certifiedNicheRegion ⊆ Romik.niche params := by
  intro q hq
  rcases hq with (⟨r, hr, hx, hy0, hy⟩ | ⟨r, hr, hx, hy0, hy⟩) |
    ⟨r, hr, hx, hy0, hy⟩
  · have hmem := vertical_below_D_mem_niche hr hy0 hy
    have heq : q = ((D r).1, q.2) := by
      apply Prod.ext
      · exact hx
      · rfl
    rw [heq]
    exact hmem
  · have hmem := vertical_below_path_mem_niche hr hy0 hy
    have heq : q = ((Romik.path params r).1, q.2) := by
      apply Prod.ext
      · exact hx
      · rfl
    rw [heq]
    exact hmem
  · have hmem := vertical_below_B_mem_niche hr hy0 hy
    have heq : q = ((B r).1, q.2) := by
      apply Prod.ext
      · exact hx
      · rfl
    rw [heq]
    exact hmem

/-- Literal niche equals the three concrete strict vertical fills. -/
theorem niche_eq_certifiedNicheRegion :
    Romik.niche params = certifiedNicheRegion :=
  Set.Subset.antisymm niche_subset_certifiedNicheRegion
    certifiedNicheRegion_subset_niche

/-- Final exact set-valued boundary equality required by Part C. -/
theorem niche_frontier_direct :
    frontier (Romik.niche params) = claimedNicheBoundary := by
  rw [niche_eq_certifiedNicheRegion]
  exact frontier_certifiedNicheRegion

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C Stage 4: connectedness of the literal niche

The independent vertical-fill module proves connectedness of the certified
three-piece region.  Once the boundary layer identifies that region with the
literal niche, connectedness is immediate.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set

/-- Concrete connectedness of the literal niche. -/
theorem niche_connected_direct : IsConnected (Romik.niche params) := by
  rw [niche_eq_certifiedNicheRegion]
  exact certifiedNicheRegion_connected

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C Stage 4: vertical-fibre topology of the fixed sofa

The argument in this file is independent of any Jordan-curve theorem.  The
cap is compact and convex.  Its removed niche is a strict vertical subgraph.
Consequently every nonempty vertical section of the complement is an interval.
Moreover, a highest point of each cap section survives: if it belonged to the
strict subgraph, one of the certified graph points would be a still higher cap
point.  Thus the horizontal projections of the cap and sofa agree.  A compact
map with connected fibres over that connected projection closes connectedness.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

private theorem physical_cos_diff_nonneg {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T) :
    0 ≤ Real.cos (t - s) := by
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
  · have hsT := hs.2
    have ht0 := ht.1
    dsimp [T] at hsT
    linarith
  · have hs0 := hs.1
    have htT := ht.2
    dsimp [T] at htT
    linarith

private theorem phi_upper_twentieth_fiber :
    params.phi ≤ (1 / 20 : ℝ) := by
  have h := phi_bounds.2
  norm_num at h ⊢
  linarith

private theorem a1_lower_six_fifths_fiber :
    (6 / 5 : ℝ) ≤ params.a1 := by
  have h := Romik.a1_lower_bound_of_mem_box params_mem
  norm_num at h ⊢
  linarith

private theorem alphaBeta1_snd_nonneg_fiber {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    0 ≤ (Romik.alphaBeta1 params s).2 := by
  have hpi : s ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hsinUpper := Real.sin_le hs0
  have hcosLower : 1 - s ^ 2 / 2 ≤ Real.cos s :=
    Real.one_sub_sq_div_two_le_cos
  have hcos0 : 0 ≤ Real.cos s := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_gt_three]
  have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) :=
    mul_nonneg hs0 (sub_nonneg.mpr hs20)
  have hcoef : (12 / 5 : ℝ) ≤ 2 * params.a1 := by
    nlinarith [a1_lower_six_fifths_fiber]
  have hmul : (12 / 5 : ℝ) * Real.cos s ≤
      2 * params.a1 * Real.cos s :=
    mul_le_mul_of_nonneg_right hcoef hcos0
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith [hsinUpper, hcosLower, hquad, hmul]

/-- The early inner-contact coefficient is nonnegative on the whole `D`
parameter interval. -/
theorem beta_nonneg_on_D {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.theta) : 0 ≤ beta t := by
  by_cases hphi : t ≤ params.phi
  · have hs20 : t ≤ (1 / 20 : ℝ) :=
      le_trans hphi phi_upper_twentieth_fiber
    have h := alphaBeta1_snd_nonneg_fiber ht.1 hs20
    simpa [beta, alphaBetaAt, hphi] using h
  · have htPhysical : t ∈ Icc (0 : ℝ) T :=
      ⟨ht.1, le_trans ht.2 (le_trans theta_lt_eta.le
        (le_trans eta_lt_tau.le tau_le_T))⟩
    have hrho := Stage2.rhoA_nonneg htPhysical
    unfold Stage2.rhoA at hrho
    rw [ite_eq_right hphi, ite_eq_left ht.2] at hrho
    simp only [beta, alphaBetaAt, ite_eq_right hphi, ite_eq_left ht.2]
    dsimp [Romik.alphaBeta2]
    exact hrho

/-- Core path points are cap points. -/
theorem core_path_mem_K {t : ℝ} (ht : t ∈ Icc params.phi tau) :
    Romik.path params t ∈ K := by
  rw [Romik.mem_K0]
  refine ⟨path_core_y_nonneg ht, ?_⟩
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) T := by simpa [T] using hs
  have ht' : t ∈ Icc (0 : ℝ) T :=
    ⟨le_trans phi_pos.le ht.1, le_trans ht.2 tau_le_T⟩
  exact path_mem_outer_supports hs' ht'

/-- Every certified early `D` roof point lies in the cap. -/
theorem D_mem_K {t : ℝ} (ht : t ∈ Icc (0 : ℝ) params.theta) :
    D t ∈ K := by
  rw [Romik.mem_K0]
  refine ⟨D_y_nonneg ht, ?_⟩
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) T := by simpa [T] using hs
  have ht' : t ∈ Icc (0 : ℝ) T :=
    ⟨ht.1, le_trans ht.2 (le_trans theta_lt_eta.le
      (le_trans eta_lt_tau.le tau_le_T))⟩
  have hcos := physical_cos_diff_nonneg hs' ht'
  have hbeta := beta_nonneg_on_D ht
  have hp := path_mem_outer_supports hs' ht'
  have hC := Stage3.supportC_direct t ht'
  constructor
  · have hpU := hp.1
    change dot (D t) (u s) ≤ dot (Romik.path params s) (u s) + 1
    change dot (Romik.path params t) (u s) ≤
      dot (Romik.path params s) (u s) + 1 at hpU
    have hrel : dot (D t) (u s) =
        dot (Romik.path params t) (u s) - beta t * Real.cos (t - s) := by
      simp [D, dot, u, Real.cos_sub]
      ring
    rw [hrel]
    nlinarith [mul_nonneg hbeta hcos]
  · have hCV := (hC.2 s hs).2
    change dot (D t) (v s) ≤ dot (Romik.path params s) (v s) + 1
    change dot (C t) (v s) ≤ dot (Romik.path params s) (v s) + 1 at hCV
    have hrel : dot (C t) (v s) =
        dot (D t) (v s) + Real.cos (t - s) := by
      simp [C, D, dot, u, v, Real.cos_sub]
      ring
    rw [hrel] at hCV
    linarith

/-- Every certified late `B` roof point lies in the cap. -/
theorem B_mem_K {t : ℝ} (ht : t ∈ Icc eta T) : B t ∈ K := by
  rw [Romik.mem_K0]
  refine ⟨B_y_nonneg ht, ?_⟩
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) T := by simpa [T] using hs
  have ht' : t ∈ Icc (0 : ℝ) T :=
    ⟨le_trans phi_pos.le (le_trans phi_lt_eta.le ht.1), ht.2⟩
  have hcos := physical_cos_diff_nonneg hs' ht'
  have halpha := alpha_nonpos ⟨le_trans phi_lt_eta.le ht.1, ht.2⟩
  have hp := path_mem_outer_supports hs' ht'
  have hA := Stage3.supportA_direct t ht'
  constructor
  · have hAU := (hA.2 s hs).1
    change dot (B t) (u s) ≤ dot (Romik.path params s) (u s) + 1
    change dot (A t) (u s) ≤ dot (Romik.path params s) (u s) + 1 at hAU
    have hrel : dot (A t) (u s) =
        dot (B t) (u s) + Real.cos (t - s) := by
      simp [A, B, dot, u, v, Real.cos_sub]
      ring
    rw [hrel] at hAU
    linarith
  · have hpV := hp.2
    change dot (B t) (v s) ≤ dot (Romik.path params s) (v s) + 1
    change dot (Romik.path params t) (v s) ≤
      dot (Romik.path params s) (v s) + 1 at hpV
    have hrel : dot (B t) (v s) =
        dot (Romik.path params t) (v s) + alpha t * Real.cos (t - s) := by
      simp [B, dot, v, Real.cos_sub]
      ring
    rw [hrel]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg halpha hcos]

/-- Every graph which forms the certified strict niche roof consists of cap
points. -/
theorem certified_roof_mem_K :
    (∀ t ∈ Icc (0 : ℝ) params.theta, D t ∈ K) ∧
    (∀ t ∈ Icc params.phi tau, Romik.path params t ∈ K) ∧
    (∀ t ∈ Icc eta T, B t ∈ K) :=
  ⟨fun _ ht => D_mem_K ht,
    fun _ ht => core_path_mem_K ht,
    fun _ ht => B_mem_K ht⟩

/-- Strict vertical fills are downward closed along every nonnegative fibre. -/
theorem verticalFill_downward
    {f : ℝ → Point} {I : Set ℝ} {p q : Point}
    (hx : p.1 = q.1) (hp0 : 0 ≤ p.2) (hy : p.2 ≤ q.2)
    (hq : q ∈ verticalFill f I) : p ∈ verticalFill f I := by
  rcases hq with ⟨t, ht, hqx, hq0, hqtop⟩
  exact ⟨t, ht, hx.trans hqx, hp0, lt_of_le_of_lt hy hqtop⟩

/-- The union of the three strict graph fills is downward closed in each
nonnegative vertical fibre. -/
theorem certifiedNicheRegion_downward {p q : Point}
    (hx : p.1 = q.1) (hp0 : 0 ≤ p.2) (hy : p.2 ≤ q.2)
    (hq : q ∈ certifiedNicheRegion) : p ∈ certifiedNicheRegion := by
  rcases hq with (hD | hP) | hB
  · exact Or.inl (Or.inl (verticalFill_downward hx hp0 hy hD))
  · exact Or.inl (Or.inr (verticalFill_downward hx hp0 hy hP))
  · exact Or.inr (verticalFill_downward hx hp0 hy hB)

/-- The Gerver cap is compact. -/
theorem K_compact_direct : IsCompact K := by
  let box : Set Point :=
    Icc ((Romik.path params T).1 - 1) 1 ×ˢ Icc (0 : ℝ) 1
  have hbox : IsCompact box := isCompact_Icc.prod isCompact_Icc
  apply hbox.of_isClosed_subset (Romik.isClosed_K0 params)
  intro q hq
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · exact le_rfl
    · positivity
  have hT : T ∈ Icc (0 : ℝ) (Real.pi / 2) := by
    exact ⟨by dsimp [T]; positivity, by dsimp [T]; exact le_rfl⟩
  have hs0 := hq.2 0 h0
  have hsT := hq.2 T hT
  have hxhi : q.1 ≤ 1 := by
    have h := hs0.1
    simpa [supportHalfU, dot, u, pathZero] using h
  have hyhi : q.2 ≤ 1 := by
    have h := hs0.2
    simpa [supportHalfV, dot, v, pathZero] using h
  have hxlo : (Romik.path params T).1 - 1 ≤ q.1 := by
    have h := hsT.2
    simp [supportHalfV, dot, v, T] at h
    dsimp [T] at ⊢
    linarith
  exact ⟨⟨hxlo, hxhi⟩, ⟨hq.1, hyhi⟩⟩

/-- The fixed sofa is compact, as the difference of the compact cap and the
open union of forbidden quadrants. -/
theorem G_compact_direct : IsCompact G := by
  change IsCompact (Romik.sofa params)
  rw [Romik.sofa_eq_K0_diff_innerUnion]
  exact K_compact_direct.diff (Romik.isOpen_innerUnion params)

private def KVerticalSection (x : ℝ) : Set Point :=
  K ∩ {q | q.1 = x}

private theorem KVerticalSection_compact (x : ℝ) :
    IsCompact (KVerticalSection x) := by
  apply K_compact_direct.inter_right
  exact isClosed_singleton.preimage continuous_fst

/-- Every cap fibre has a highest point, and that point survives removal of
the strict niche. -/
theorem exists_G_point_over_K {q : Point} (hq : q ∈ K) :
    ∃ p ∈ G, p.1 = q.1 := by
  let F := KVerticalSection q.1
  have hFcompact : IsCompact F := KVerticalSection_compact q.1
  have hFne : F.Nonempty := ⟨q, hq, rfl⟩
  rcases hFcompact.exists_isMaxOn hFne continuous_snd.continuousOn with
    ⟨p, hpF, hpmax⟩
  have hpK : p ∈ K := hpF.1
  have hpx : p.1 = q.1 := hpF.2
  refine ⟨p, ⟨hpK, ?_⟩, hpx⟩
  intro hpN
  rw [niche_eq_certifiedNicheRegion] at hpN
  rcases hpN with (hD | hP) | hB
  · rcases hD with ⟨t, ht, hx, _hy0, hylt⟩
    have hwK := D_mem_K ht
    have hwF : D t ∈ F := ⟨hwK, hx.symm.trans hpx⟩
    exact (not_lt_of_ge (hpmax hwF)) hylt
  · rcases hP with ⟨t, ht, hx, _hy0, hylt⟩
    have hwK := core_path_mem_K ht
    have hwF : Romik.path params t ∈ F := ⟨hwK, hx.symm.trans hpx⟩
    exact (not_lt_of_ge (hpmax hwF)) hylt
  · rcases hB with ⟨t, ht, hx, _hy0, hylt⟩
    have hwK := B_mem_K ht
    have hwF : B t ∈ F := ⟨hwK, hx.symm.trans hpx⟩
    exact (not_lt_of_ge (hpmax hwF)) hylt

/-- Removing the strict niche does not change the horizontal projection. -/
theorem fst_image_G_eq_fst_image_K :
    Prod.fst '' G = Prod.fst '' K := by
  apply Set.Subset.antisymm
  · rintro x ⟨q, hq, rfl⟩
    exact ⟨q, hq.1, rfl⟩
  · rintro x ⟨q, hq, rfl⟩
    rcases exists_G_point_over_K hq with ⟨p, hp, hpx⟩
    exact ⟨p, hp, hpx⟩

/-- A vertical section of the fixed sofa. -/
def GVerticalSection (x : ℝ) : Set Point :=
  {q | q ∈ G ∧ q.1 = x}

/-- Every vertical section of `G` is convex. -/
theorem GVerticalSection_convex (x : ℝ) :
    Convex ℝ (GVerticalSection x) := by
  intro p hp q hq a b ha hb hab
  have hpK : p ∈ K := hp.1.1
  have hqK : q ∈ K := hq.1.1
  have hzK := K_convex_direct hpK hqK ha hb hab
  have hzx : (a • p + b • q).1 = x := by
    change a * p.1 + b * q.1 = x
    rw [hp.2, hq.2]
    calc
      a * x + b * x = (a + b) * x := by ring
      _ = x := by rw [hab, one_mul]
  refine ⟨⟨hzK, ?_⟩, hzx⟩
  intro hzN
  have hzR : a • p + b • q ∈ certifiedNicheRegion := by
    rw [← niche_eq_certifiedNicheRegion]
    exact hzN
  rcases le_total p.2 q.2 with hpq | hqp
  · have hpz : p.2 ≤ (a • p + b • q).2 := by
      change p.2 ≤ a * p.2 + b * q.2
      calc
        p.2 = a * p.2 + b * p.2 := by
          calc
            p.2 = (a + b) * p.2 := by rw [hab, one_mul]
            _ = a * p.2 + b * p.2 := by ring
        _ ≤ a * p.2 + b * q.2 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hpq hb)
    have hpR := certifiedNicheRegion_downward
      (hp.2.trans hzx.symm) hpK.1 hpz hzR
    exact hp.1.2 (by
      rw [niche_eq_certifiedNicheRegion]
      exact hpR)
  · have hqz : q.2 ≤ (a • p + b • q).2 := by
      change q.2 ≤ a * p.2 + b * q.2
      calc
        q.2 = a * q.2 + b * q.2 := by
          calc
            q.2 = (a + b) * q.2 := by rw [hab, one_mul]
            _ = a * q.2 + b * q.2 := by ring
        _ ≤ a * p.2 + b * q.2 :=
          add_le_add (mul_le_mul_of_nonneg_left hqp ha) le_rfl
    have hqR := certifiedNicheRegion_downward
      (hq.2.trans hzx.symm) hqK.1 hqz hzR
    exact hq.1.2 (by
      rw [niche_eq_certifiedNicheRegion]
      exact hqR)

/-- Each nonempty vertical section is connected. -/
theorem GVerticalSection_connected {x : ℝ}
    (hne : (GVerticalSection x).Nonempty) :
    IsConnected (GVerticalSection x) :=
  (GVerticalSection_convex x).isConnected hne

private def GProjection : Set ℝ := Prod.fst '' G

private def projectG : G → GProjection := fun q =>
  ⟨q.1.1, ⟨q.1, q.2, rfl⟩⟩

private theorem projectG_continuous : Continuous projectG := by
  exact (continuous_fst.comp continuous_subtype_val).subtype_mk _

private theorem projectG_surjective : Function.Surjective projectG := by
  rintro ⟨x, q, hq, hqx⟩
  refine ⟨⟨q, hq⟩, ?_⟩
  apply Subtype.ext
  exact hqx

private theorem projectG_fiber_connected (x : GProjection) :
    IsConnected (projectG ⁻¹' {x}) := by
  have hsectionNe : (GVerticalSection x.1).Nonempty := by
    rcases x.2 with ⟨q, hq, hqx⟩
    exact ⟨q, hq, hqx⟩
  have hsection := GVerticalSection_connected hsectionNe
  have : ConnectedSpace (GVerticalSection x.1) :=
    isConnected_iff_connectedSpace.mp hsection
  let e : GVerticalSection x.1 → G := fun q => ⟨q.1, q.2.1⟩
  have he : Continuous e := by
    exact continuous_subtype_val.subtype_mk _
  have hrange : Set.range e = projectG ⁻¹' {x} := by
    ext q
    constructor
    · rintro ⟨z, rfl⟩
      apply Set.mem_preimage.mpr
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      exact z.2.2
    · intro hq
      have hx : q.1.1 = x.1 := by
        have := Set.mem_singleton_iff.mp hq
        exact congrArg Subtype.val this
      exact ⟨⟨q.1, q.2, hx⟩, rfl⟩
  rw [← hrange]
  exact isConnected_range he

/-- Connectedness of the fixed Gerver sofa by compact connected fibres. -/
theorem G_connected_by_vertical_fibers : IsConnected G := by
  have hprojK : IsConnected (Prod.fst '' K) :=
    K_connected_direct.image Prod.fst continuous_fst.continuousOn
  have hproj : IsConnected GProjection := by
    simpa [GProjection, fst_image_G_eq_fst_image_K] using hprojK
  have : CompactSpace G := isCompact_iff_compactSpace.mp G_compact_direct
  have : ConnectedSpace GProjection := isConnected_iff_connectedSpace.mp hproj
  have hquot : Topology.IsQuotientMap projectG :=
    Topology.IsQuotientMap.of_surjective_continuous
      projectG_surjective projectG_continuous
  have hpre : IsConnected (projectG ⁻¹' (Set.univ : Set GProjection)) :=
    Topology.IsCoinducing.isConnected_preimage_of_isClosed
      projectG_fiber_connected hquot.isCoinducing isClosed_univ isConnected_univ
  have huniv : IsConnected (Set.univ : Set G) := by simpa using hpre
  have hspace : ConnectedSpace G := connectedSpace_iff_univ.mpr huniv
  exact isConnected_iff_connectedSpace.mpr hspace

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C Stage 4: topology of the concrete fixed set

No new certificate structure is introduced here.  This file is intended to
close the two literal topology fields left by `RemainingTopologyTarget`.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set

/-- The right endpoint of the niche roof still satisfies the zero-angle
horizontal support inequality of the cap. -/
private theorem B_T_fst_le_one : (B T).1 ≤ 1 := by
  have hBTK : B T ∈ K := B_mem_K ⟨eta_lt_T.le, le_rfl⟩
  rw [Romik.mem_K0] at hBTK
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · exact le_rfl
    · positivity
  have h := (hBTK.2 0 h0).1
  simpa [supportHalfU, dot, u, pathZero] using h

/-- The left endpoint of the zero-angle support face is the concrete anchor
and it is not removed by the niche. -/
theorem anchor_mem_direct : anchor ∈ G := by
  have hA0 : A 0 = anchor := Stage2.A_zero_eq_anchor
  have hK : anchor ∈ K := by
    rw [← hA0]
    exact Stage3.supportA_direct 0 (by
      constructor
      · norm_num
      · dsimp [T]; positivity)
  refine ⟨hK, ?_⟩
  intro hn
  rw [niche_eq_certifiedNicheRegion] at hn
  rcases hn with (hD | hx) | hB
  · rcases hD with ⟨t, ht, hx1, _hy0, _hylt⟩
    have htT : t < T := lt_of_le_of_lt ht.2 (lt_trans theta_lt_eta eta_lt_T)
    have htPhysical : t ∈ Icc (0 : ℝ) T := ⟨ht.1, htT.le⟩
    have hroof := nicheTopArc_fst_strictMono htPhysical
      (right_mem_Icc.2 (show (0 : ℝ) ≤ T by dsimp [T]; positivity)) htT
    have hleft : nicheTopArc t = D t := by
      simp [nicheTopArc, ht.2]
    change (nicheTopArc t).1 < (nicheTopArc T).1 at hroof
    rw [hleft, nicheTopArc_T] at hroof
    change (1 : ℝ) = (D t).1 at hx1
    linarith [B_T_fst_le_one]
  · rcases hx with ⟨t, ht, hx1, _hy0, _hylt⟩
    have hpath : (Romik.path params t).1 ≤
        (Romik.path params params.phi).1 :=
      core_path_fst_strictAnti.antitoneOn
        (left_mem_Icc.2 (lt_trans phi_lt_theta
          (lt_trans theta_lt_eta eta_lt_tau)).le)
        ht ht.1
    have hlate : (B eta).1 < (B T).1 :=
      B_fst_strictMono (left_mem_Icc.2 eta_lt_T.le)
        (right_mem_Icc.2 eta_lt_T.le) eta_lt_T
    have hroof : (Romik.path params t).1 < (B T).1 := by
      calc
        (Romik.path params t).1 ≤
            (Romik.path params params.phi).1 := hpath
        _ = (B eta).1 := congrArg Prod.fst B_eta_eq_path_phi.symm
        _ < (B T).1 := hlate
    change (1 : ℝ) = (Romik.path params t).1 at hx1
    linarith [B_T_fst_le_one]
  · rcases hB with ⟨t, ht, hx1, _hy0, _hylt⟩
    by_cases hT : t = T
    · subst t
      change (0 : ℝ) < (B T).2 at _hylt
      rw [B_T_y_zero] at _hylt
      exact (lt_irrefl 0 _hylt)
    · have htT : t < T := lt_of_le_of_ne ht.2 hT
      have hroof : (B t).1 < (B T).1 :=
        B_fst_strictMono ht (right_mem_Icc.2 eta_lt_T.le) htT
      change (1 : ℝ) = (B t).1 at hx1
      linarith [B_T_fst_le_one]

/-- Direct connectedness of the cap-minus-niche set, obtained from the
compact connected horizontal projection and the connected vertical fibres. -/
theorem G_connected_direct : IsConnected G :=
  G_connected_by_vertical_fibers

end Stage4
end PartC
end GerverSofa

end

end

end

section

/-!
# Part C final unconditional closure

This is the only terminal assembly for Part C.  It contains no payload and no
new certificate interface.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

/-- Concrete global geometry certificate. -/
theorem globalGeometryCertificate : GlobalGeometryCertificate :=
  Stage3.globalGeometryDirect
    noHiddenU_direct noHiddenV_direct
    niche_frontier_direct niche_connected_direct
    anchor_mem_direct G_connected_direct

end Stage4
end PartC
end GerverSofa

end

end

end

end

end

end
