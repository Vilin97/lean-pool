/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Exact differential calculus on the auxiliary graph

The physical variables are `(r,t)` and the auxiliary variable is in `ℝ²`.
The graph is `Y(r,t) = r^d • vr + t • vt`, as in Definition 8.1 of the
candidate manuscript. The radial formulas below are stated away from `r = 0`.
All differential operators use Mathlib's actual Fréchet derivatives.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.GraphCalculus

/-- Plane: an abbreviation for `ℝ × ℝ`. -/
abbrev Plane := ℝ × ℝ
/-- Lift: an abbreviation for `Plane × Plane`. -/
abbrev Lift := Plane × Plane

/-- The radial coefficient in the exact graph derivative. -/
def radialSpeed (d r : ℝ) : ℝ := d * r ^ (d - 1)

/-- Embed physical radial/time coordinates in the auxiliary lift. -/
def graph (d : ℝ) (vr vt : Plane) (q : Plane) : Lift :=
  (q, q.1 ^ d • vr + q.2 • vt)

/-- Pullback, defined pointwise by `F (graph d vr vt q)`. -/
def pullback (d : ℝ) (vr vt : Plane) (F : Lift → ℝ) : Plane → ℝ :=
  fun q => F (graph d vr vt q)

/-- Radial vector, given by `((1, 0), radialSpeed d p.1.1 • vr)`. -/
def radialVector (d : ℝ) (vr : Plane) (p : Lift) : Lift :=
  ((1, 0), radialSpeed d p.1.1 • vr)

/-- Time vector, given by `((0, 1), vt)`. -/
def timeVector (vt : Plane) : Lift := ((0, 1), vt)

/-- Differentiation along a vector field, defined by the genuine derivative. -/
def along (V : Lift → Lift) (F : Lift → ℝ) (p : Lift) : ℝ :=
  fderiv ℝ F p (V p)

/-- Radial op, given by `along (radialVector d vr) F`. -/
def radialOp (d : ℝ) (vr : Plane) (F : Lift → ℝ) : Lift → ℝ :=
  along (radialVector d vr) F

/-- Time op, given by `along (fun _ => timeVector vt) F`. -/
def timeOp (vt : Plane) (F : Lift → ℝ) : Lift → ℝ :=
  along (fun _ => timeVector vt) F

/-- Partial R, given by `deriv (fun r => u (r, q.2)) q.1`. -/
def partialR (u : Plane → ℝ) (q : Plane) : ℝ :=
  deriv (fun r => u (r, q.2)) q.1

/-- Partial T, given by `deriv (fun t => u (q.1, t)) q.2`. -/
def partialT (u : Plane → ℝ) (q : Plane) : ℝ :=
  deriv (fun t => u (q.1, t)) q.2

/-- A general commutator identity when both cross derivatives of the vector
fields vanish. The regularity assumption is ordinary `C²` regularity. -/
theorem along_comm_of_cross_zero (F : Lift → ℝ) (V W : Lift → Lift) (p : Lift)
    (hF : ContDiffAt ℝ 2 F p)
    (hV : DifferentiableAt ℝ V p) (hW : DifferentiableAt ℝ W p)
    (hVW : fderiv ℝ V p (W p) = 0)
    (hWV : fderiv ℝ W p (V p) = 0) :
    along V (along W F) p = along W (along V F) p := by
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) p :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold along
  rw [fderiv_clm_apply hDF hW, fderiv_clm_apply hDF hV]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, hVW, hWV, map_zero, zero_add]
  exact (hF.isSymmSndFDerivAt (by simp)).eq (V p) (W p)

/-- Exact derivative of the graph along a radial coordinate line. -/
theorem hasDerivAt_graph_radial (d : ℝ) (vr vt : Plane) (r t : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s => graph d vr vt (s, t))
      (radialVector d vr (graph d vr vt (r, t))) r := by
  have hp := (Real.hasDerivAt_rpow_const (p := d) (Or.inl hr)).smul_const vr
  have hb := hp.add (hasDerivAt_const r (t • vt))
  have hq := (hasDerivAt_id r).prodMk (hasDerivAt_const r t)
  simpa [graph, radialVector, radialSpeed] using hq.prodMk hb

/-- The time direction has constant graph velocity. -/
theorem hasDerivAt_graph_time (d : ℝ) (vr vt : Plane) (r t : ℝ) :
    HasDerivAt (fun s => graph d vr vt (r, s)) (timeVector vt) t := by
  have hb := (hasDerivAt_const t (r ^ d • vr)).add ((hasDerivAt_id t).smul_const vt)
  have hq := (hasDerivAt_const t r).prodMk (hasDerivAt_id t)
  simpa [graph, timeVector] using hq.prodMk hb

/-- First radial derivative of the physical pullback equals the exact graph operator. -/
theorem partialR_pullback (d : ℝ) (vr vt : Plane) (F : Lift → ℝ) (q : Plane)
    (hr : q.1 ≠ 0) (hF : DifferentiableAt ℝ F (graph d vr vt q)) :
    partialR (pullback d vr vt F) q = radialOp d vr F (graph d vr vt q) := by
  exact (hF.hasFDerivAt.comp_hasDerivAt q.1
    (hasDerivAt_graph_radial d vr vt q.1 q.2 hr)).deriv

/-- First time derivative of the physical pullback equals the exact graph operator. -/
theorem partialT_pullback (d : ℝ) (vr vt : Plane) (F : Lift → ℝ) (q : Plane)
    (hF : DifferentiableAt ℝ F (graph d vr vt q)) :
    partialT (pullback d vr vt F) q = timeOp vt F (graph d vr vt q) := by
  exact (hF.hasFDerivAt.comp_hasDerivAt q.2
    (hasDerivAt_graph_time d vr vt q.1 q.2)).deriv

/-- The coordinate map is smooth to every order away from the axis. -/
theorem contDiffAt_graph {n : WithTop ℕ∞} (d : ℝ) (vr vt : Plane) (q : Plane)
    (hr : q.1 ≠ 0) : ContDiffAt ℝ n (graph d vr vt) q := by
  unfold graph
  exact contDiffAt_id.prodMk
    (((contDiffAt_fst.rpow_const_of_ne hr).smul contDiffAt_const).add
      (contDiffAt_snd.smul contDiffAt_const))

private def radiusProjection : Lift →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane Plane)

/-- This form keeps the exponent arithmetic of the derivative explicit. -/
def radialAcceleration (d r : ℝ) : ℝ :=
  d * ((d - 1) * r ^ (d - 1 - 1))

private theorem hasFDerivAt_radialVector (d : ℝ) (vr : Plane) (p : Lift)
    (hr : p.1.1 ≠ 0) :
    HasFDerivAt (radialVector d vr)
      ((0 : Lift →L[ℝ] Plane).prod
        (((radialAcceleration d p.1.1) • radiusProjection).smulRight vr)) p := by
  have hrad : HasFDerivAt (fun z : Lift => z.1.1) radiusProjection p :=
    radiusProjection.hasFDerivAt
  have hpow := hrad.rpow_const (p := d - 1) (Or.inl hr)
  have hs : HasFDerivAt (fun z : Lift => radialSpeed d z.1.1)
      (radialAcceleration d p.1.1 • radiusProjection) p := by
    simpa only [radialSpeed, radialAcceleration, Pi.smul_apply, smul_eq_mul, smul_smul] using
      hpow.fun_const_smul d
  exact (hasFDerivAt_const (1, 0) p).prodMk (hs.smul_const vr)

theorem differentiableAt_radialVector (d : ℝ) (vr : Plane) (p : Lift)
    (hr : p.1.1 ≠ 0) : DifferentiableAt ℝ (radialVector d vr) p :=
  (hasFDerivAt_radialVector d vr p hr).differentiableAt

/-- The radial graph coefficient is independent of both time and the
auxiliary coordinates. Its derivative in the time graph direction is zero. -/
theorem fderiv_radialVector_timeVector (d : ℝ) (vr vt : Plane) (p : Lift)
    (hr : p.1.1 ≠ 0) :
    fderiv ℝ (radialVector d vr) p (timeVector vt) = 0 := by
  rw [(hasFDerivAt_radialVector d vr p hr).fderiv]
  simp [radiusProjection, timeVector]

/-- The actual radial and time graph operators commute on every `C²` lift,
away from the radial axis. This proves the relevant assertion of §8.1. -/
theorem radialOp_timeOp_comm (d : ℝ) (vr vt : Plane) (F : Lift → ℝ) (p : Lift)
    (hr : p.1.1 ≠ 0) (hF : ContDiffAt ℝ 2 F p) :
    radialOp d vr (timeOp vt F) p = timeOp vt (radialOp d vr F) p := by
  apply along_comm_of_cross_zero F (radialVector d vr) (fun _ => timeVector vt) p hF
    (differentiableAt_radialVector d vr p hr) (differentiableAt_const _)
  · exact fderiv_radialVector_timeVector d vr vt p hr
  · simp

theorem differentiableAt_timeOp (vt : Plane) (F : Lift → ℝ) (p : Lift)
    (hF : ContDiffAt ℝ 2 F p) : DifferentiableAt ℝ (timeOp vt F) p := by
  exact ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
    (differentiableAt_const (timeVector vt))

theorem differentiableAt_radialOp (d : ℝ) (vr : Plane) (F : Lift → ℝ) (p : Lift)
    (hr : p.1.1 ≠ 0) (hF : ContDiffAt ℝ 2 F p) :
    DifferentiableAt ℝ (radialOp d vr F) p := by
  exact ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
    (differentiableAt_radialVector d vr p hr)

/-- Restriction to the graph preserves each differentiability order away
from the axis, in particular `C∞` when the order is `∞`. -/
theorem contDiffAt_pullback {n : WithTop ℕ∞} (d : ℝ) (vr vt : Plane)
    (F : Lift → ℝ) (q : Plane) (hr : q.1 ≠ 0)
    (hF : ContDiffAt ℝ n F (graph d vr vt q)) :
    ContDiffAt ℝ n (pullback d vr vt F) q :=
  hF.comp q (contDiffAt_graph d vr vt q hr)

/-- Differentiate the restricted time derivative in the radial direction. -/
theorem partialR_partialT_pullback (d : ℝ) (vr vt : Plane) (F : Lift → ℝ)
    (q : Plane) (hr : q.1 ≠ 0) (hF : ContDiff ℝ 2 F) :
    partialR (partialT (pullback d vr vt F)) q =
      radialOp d vr (timeOp vt F) (graph d vr vt q) := by
  have ht : partialT (pullback d vr vt F) = pullback d vr vt (timeOp vt F) := by
    funext z
    exact partialT_pullback d vr vt F z (hF.differentiable (by norm_num) _)
  rw [ht]
  exact partialR_pullback d vr vt (timeOp vt F) q hr
    (differentiableAt_timeOp vt F _ hF.contDiffAt)

/-- Differentiate the restricted radial derivative in the time direction. -/
theorem partialT_partialR_pullback (d : ℝ) (vr vt : Plane) (F : Lift → ℝ)
    (q : Plane) (hr : q.1 ≠ 0) (hF : ContDiff ℝ 2 F) :
    partialT (partialR (pullback d vr vt F)) q =
      timeOp vt (radialOp d vr F) (graph d vr vt q) := by
  have hrline :
      (fun t => partialR (pullback d vr vt F) (q.1, t)) =
        (fun t => pullback d vr vt (radialOp d vr F) (q.1, t)) := by
    funext t
    exact partialR_pullback d vr vt F (q.1, t) hr
      (hF.differentiable (by norm_num) _)
  unfold partialT
  rw [hrline]
  exact partialT_pullback d vr vt (radialOp d vr F) q
    (differentiableAt_radialOp d vr F _ hr hF.contDiffAt)

/-- The mixed physical derivatives commute, and both orders coincide with
the corresponding iterated exact graph operators. -/
theorem mixed_partial_pullback_comm (d : ℝ) (vr vt : Plane) (F : Lift → ℝ)
    (q : Plane) (hr : q.1 ≠ 0) (hF : ContDiff ℝ 2 F) :
    partialR (partialT (pullback d vr vt F)) q =
      partialT (partialR (pullback d vr vt F)) q := by
  rw [partialR_partialT_pullback d vr vt F q hr hF,
    partialT_partialR_pullback d vr vt F q hr hF]
  exact radialOp_timeOp_comm d vr vt F _ hr hF.contDiffAt

/-- A derivative in an auxiliary direction is the ordinary dot product
with the two auxiliary partial derivatives. -/
theorem auxiliary_directional_eq (F : Lift → ℝ) (p : Lift) (v : Plane) :
    fderiv ℝ F p ((0, 0), v) =
      v.1 * fderiv ℝ F p ((0, 0), (1, 0)) +
        v.2 * fderiv ℝ F p ((0, 0), (0, 1)) := by
  have hv : ((0, 0), v) =
      v.1 • (((0, 0), (1, 0)) : Lift) + v.2 • (((0, 0), (0, 1)) : Lift) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  rfl

/-- This is exactly `∂r + d r^(d-1) (vr · ∂Y)`. -/
theorem radialOp_expanded (d : ℝ) (vr : Plane) (F : Lift → ℝ) (p : Lift) :
    radialOp d vr F p = fderiv ℝ F p ((1, 0), (0, 0)) +
      radialSpeed d p.1.1 *
        (vr.1 * fderiv ℝ F p ((0, 0), (1, 0)) +
          vr.2 * fderiv ℝ F p ((0, 0), (0, 1))) := by
  change fderiv ℝ F p (radialVector d vr p) = _
  have hv : radialVector d vr p =
      (((1, 0), (0, 0)) : Lift) + radialSpeed d p.1.1 • (((0, 0), vr) : Lift) := by
    ext <;> simp [radialVector]
  rw [hv, map_add, map_smul, auxiliary_directional_eq]
  rfl

/-- This is exactly `∂t + vt · ∂Y`. -/
theorem timeOp_expanded (vt : Plane) (F : Lift → ℝ) (p : Lift) :
    timeOp vt F p = fderiv ℝ F p ((0, 1), (0, 0)) +
      (vt.1 * fderiv ℝ F p ((0, 0), (1, 0)) +
        vt.2 * fderiv ℝ F p ((0, 0), (0, 1))) := by
  change fderiv ℝ F p (timeVector vt) = _
  have hv : timeVector vt =
      (((0, 1), (0, 0)) : Lift) + (((0, 0), vt) : Lift) := by
    ext <;> simp [timeVector]
  rw [hv, map_add, auxiliary_directional_eq]

end NavierStokes.GraphCalculus
