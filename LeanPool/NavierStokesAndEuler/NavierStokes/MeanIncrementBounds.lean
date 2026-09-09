/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedClasses
public import LeanPool.NavierStokesAndEuler.NavierStokes.PressureStream
public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanMomentBounds

@[expose] public section

/-!
# Changes of the literal mean equations under an actual mean increment

The differential operators below are genuine graph derivatives.  The
nonlinear fields are the products in equation (32), including every old/new
mean cross term.  The unchanged wave covariance and virtual flux cancel
only after an exact residual-difference identity.
-/

noncomputable section

namespace NavierStokes.MeanIncrementBounds

open Set Filter WeightedClasses
open scoped ContDiff Topology

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

abbrev Field (D : Type) := ℕ → D → ℝ

structure Triple (D : Type) where
  radial : Field D
  angular : Field D
  axial : Field D

noncomputable def updated (m h : Triple D) : Triple D :=
  ⟨m.radial + h.radial, m.angular + h.angular, m.axial + h.axial⟩

structure Operators (D : Type) where
  epsilon : ℕ → ℝ
  radialFrequency : ℕ → ℝ
  fastCoefficient : ℕ → ℝ
  radius : D → ℝ
  radialProfile : D → ℝ
  eR : D
  eZ : D
  eT : D
  vR : D
  vT : D

namespace Operators

noncomputable def invRadius (o : Operators D) : Field D := fun _ x => (o.radius x)⁻¹

noncomputable def dr (o : Operators D) (f : Field D) : Field D :=
  graphDerivative o.radialFrequency o.radialProfile o.eR o.vR f

noncomputable def dz (o : Operators D) (f : Field D) : Field D :=
  fun n x => o.epsilon n * fderiv ℝ (f n) x o.eZ

noncomputable def slowTime (o : Operators D) (f : Field D) : Field D :=
  fun n x => -(o.epsilon n * fderiv ℝ (f n) x o.eT)

noncomputable def fastTime (o : Operators D) (f : Field D) : Field D :=
  fun n x => o.fastCoefficient n * fderiv ℝ (f n) x o.vT

noncomputable def time (o : Operators D) (f : Field D) : Field D :=
  o.slowTime f + o.fastTime f

noncomputable def radialDiv (o : Operators D) (c : ℝ) (f : Field D) : Field D :=
  o.dr f + c • (o.invRadius * f)

/-- The connection parameter is one for radial/angular velocity, zero axially. -/
noncomputable def viscosity (o : Operators D) (c : ℝ) (f : Field D) : Field D :=
  fun n x => o.epsilon n *
    (o.dr (o.dr f) n x + o.invRadius n x * o.dr f n x +
      o.dz (o.dz f) n x - c * (o.invRadius n x * (o.invRadius n x * f n x)))

end Operators

def SmoothOn (U : Set D) (f : Field D) : Prop := ∀ n, ContDiffOn ℝ ∞ (f n) U
def Agree (U : Set D) (f g : Field D) : Prop := ∀ n, EqOn (f n) (g n) U

namespace SmoothOn
variable {U : Set D} {f g : Field D}

theorem add (hf : SmoothOn U f) (hg : SmoothOn U g) : SmoothOn U (f + g) :=
  fun n => (hf n).add (hg n)

theorem mul (hf : SmoothOn U f) (hg : SmoothOn U g) : SmoothOn U (f * g) :=
  fun n => (hf n).mul (hg n)

theorem neg (hf : SmoothOn U f) : SmoothOn U (-f) := fun n => (hf n).neg

theorem sub (hf : SmoothOn U f) (hg : SmoothOn U g) : SmoothOn U (f - g) :=
  hf.add hg.neg

theorem smul (hf : SmoothOn U f) (c : ℝ) : SmoothOn U (c • f) :=
  fun n => (hf n).const_smul c

theorem directional (hf : SmoothOn U f) (hU : IsOpen U) (v : D) :
    SmoothOn U (fun n x => fderiv ℝ (f n) x v) := by
  intro n
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp (hf n)).2.clm_apply contDiffOn_const

theorem at_point (hf : SmoothOn U f) (hU : IsOpen U) (n : ℕ) {x : D} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (f n) x := (hf n).contDiffAt (hU.mem_nhds hx)

theorem dr (hf : SmoothOn U f) (hU : IsOpen U) (o : Operators D)
    (ha : ContDiffOn ℝ ∞ o.radialProfile U) : SmoothOn U (o.dr f) := by
  intro n
  exact ((hf.directional hU o.eR) n).add
    ((ha.mul ((hf.directional hU o.vR) n)).const_smul (o.radialFrequency n))

theorem dz (hf : SmoothOn U f) (hU : IsOpen U) (o : Operators D) :
    SmoothOn U (o.dz f) := fun n => ((hf.directional hU o.eZ) n).const_smul (o.epsilon n)

end SmoothOn

theorem agree_fderiv {U : Set D} (hU : IsOpen U) {f g : Field D} (h : Agree U f g)
    (n : ℕ) {x : D} (hx : x ∈ U) : fderiv ℝ (f n) x = fderiv ℝ (g n) x := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact h n hy

theorem class_congr {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ} {f g : Field D}
    (hf : MemClass s w α f) (h : Agree s.domain g f) : MemClass s w α g := by
  refine ⟨hf.weight_nonneg, fun n => (hf.smooth n).congr (h n), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have he : iteratedFDeriv ℝ j (g n) x = iteratedFDeriv ℝ j (f n) x := by
    rw [← iteratedFDerivWithin_of_isOpen j s.isOpen_domain hx,
      ← iteratedFDerivWithin_of_isOpen j s.isOpen_domain hx]
    exact iteratedFDerivWithin_congr (h n) hx j
  rw [he]
  exact hb n x hx j hj

namespace Operators

theorem dr_congr {U : Set D} (hU : IsOpen U) (o : Operators D)
    {f g : Field D} (h : Agree U f g) : Agree U (o.dr f) (o.dr g) := by
  intro n x hx
  simp only [dr, graphDerivative, agree_fderiv hU h n hx]

theorem dr_add {U : Set D} (hU : IsOpen U) (o : Operators D)
    {f g : Field D} (hf : SmoothOn U f) (hg : SmoothOn U g) :
    Agree U (o.dr (f + g)) (o.dr f + o.dr g) := by
  intro n x hx
  have hd := fderiv_fun_add ((hf.at_point hU n hx).differentiableAt (by simp))
    ((hg.at_point hU n hx).differentiableAt (by simp))
  change fderiv ℝ (f n + g n) x = _ at hd
  simp only [dr, graphDerivative, Pi.add_apply, hd, _root_.add_apply,
    smul_eq_mul]
  ring

theorem dz_add {U : Set D} (hU : IsOpen U) (o : Operators D)
    {f g : Field D} (hf : SmoothOn U f) (hg : SmoothOn U g) :
    Agree U (o.dz (f + g)) (o.dz f + o.dz g) := by
  intro n x hx
  have hd := fderiv_fun_add ((hf.at_point hU n hx).differentiableAt (by simp))
    ((hg.at_point hU n hx).differentiableAt (by simp))
  change fderiv ℝ (f n + g n) x = _ at hd
  simp only [dz, Pi.add_apply, hd, _root_.add_apply]
  ring

theorem dz_congr {U : Set D} (hU : IsOpen U) (o : Operators D)
    {f g : Field D} (h : Agree U f g) : Agree U (o.dz f) (o.dz g) := by
  intro n x hx
  simp only [dz, agree_fderiv hU h n hx]

theorem time_add {U : Set D} (hU : IsOpen U) (o : Operators D)
    {f g : Field D} (hf : SmoothOn U f) (hg : SmoothOn U g) :
    Agree U (o.time (f + g)) (o.time f + o.time g) := by
  intro n x hx
  have hd := fderiv_fun_add ((hf.at_point hU n hx).differentiableAt (by simp))
    ((hg.at_point hU n hx).differentiableAt (by simp))
  change fderiv ℝ (f n + g n) x = _ at hd
  simp only [time, slowTime, fastTime, Pi.add_apply, hd, _root_.add_apply]
  ring

theorem radialDiv_add {U : Set D} (hU : IsOpen U) (o : Operators D) (c : ℝ)
    {f g : Field D} (hf : SmoothOn U f) (hg : SmoothOn U g) :
    Agree U (o.radialDiv c (f + g)) (o.radialDiv c f + o.radialDiv c g) := by
  intro n x hx
  simp only [radialDiv, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    o.dr_add hU hf hg n hx]
  ring

theorem viscosity_add {U : Set D} (hU : IsOpen U) (o : Operators D)
    (ha : ContDiffOn ℝ ∞ o.radialProfile U) (c : ℝ)
    {f g : Field D} (hf : SmoothOn U f) (hg : SmoothOn U g) :
    Agree U (o.viscosity c (f + g)) (o.viscosity c f + o.viscosity c g) := by
  intro n x hx
  have hrr := o.dr_congr hU (o.dr_add hU hf hg) n hx
  rw [o.dr_add hU (hf.dr hU o ha) (hg.dr hU o ha) n hx] at hrr
  have hzz := o.dz_congr hU (o.dz_add hU hf hg) n hx
  rw [o.dz_add hU (hf.dz hU o) (hg.dz hU o) n hx] at hzz
  simp only [viscosity, Pi.add_apply, hrr, hzz, o.dr_add hU hf hg n hx]
  ring

end Operators

structure OperatorBounds (s : StripData D) (o : Operators D) (κ : ℝ) : Prop where
  epsilon_eq : o.epsilon = s.epsilon
  radialProfile : UnweightedClass s 0 (fun _ => o.radialProfile)
  invRadius : UnweightedClass s 0 o.invRadius
  radialFrequency : BandBound s (-κ) o.radialFrequency
  fastCoefficient : BandBound s 0 o.fastCoefficient
  kappa_nonneg : 0 ≤ κ
  weight_le_one : ∀ x ∈ s.domain, s.zeta x ≤ 1

namespace Class

theorem neg {s : StripData D} {α : ℝ} {f : Field D} (hf : MeanClass s α f) :
    MeanClass s α (-f) := by
  have h := hf.map (-ContinuousLinearMap.id ℝ ℝ)
  simp only [_root_.neg_apply, ContinuousLinearMap.id_apply] at h
  exact h

theorem sub {s : StripData D} {α : ℝ} {f g : Field D}
    (hf : MeanClass s α f) (hg : MeanClass s α g) : MeanClass s α (f - g) := by
  have h := hf.add (neg hg)
  simp only [sub_eq_add_neg] at h ⊢
  exact h

theorem smul {s : StripData D} {α : ℝ} {f : Field D} (hf : MeanClass s α f) (c : ℝ) :
    MeanClass s α (c • f) := by
  have h := hf.map (c • ContinuousLinearMap.id ℝ ℝ)
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply] at h
  exact h

theorem product {s : StripData D} {α β : ℝ} {f g : Field D}
    (hf : MeanClass s α f) (hg : MeanClass s β g)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) : MeanClass s (α + β) (f * g) := by
  exact hf.bilinear hg hζ (ContinuousLinearMap.lsmul ℝ ℝ)

theorem coefficient_mul {s : StripData D} {α β : ℝ} {f g : Field D}
    (hf : UnweightedClass s α f) (hg : MeanClass s β g) :
    MeanClass s (α + β) (f * g) := by
  have h := hf.mul hg
  simp only [one_mul] at h
  exact h

theorem mul_coefficient {s : StripData D} {α β : ℝ} {f g : Field D}
    (hf : MeanClass s α f) (hg : UnweightedClass s β g) :
    MeanClass s (α + β) (f * g) := by
  have h := hf.mul hg
  simp only [mul_one] at h
  exact h

end Class

namespace OperatorBounds
variable {s : StripData D} {o : Operators D} {κ α : ℝ}

theorem epsilon (ho : OperatorBounds s o κ) : BandBound s 1 o.epsilon := by
  rw [ho.epsilon_eq]
  simpa only [Real.rpow_one] using bandBound_rpow s 1

theorem dr (ho : OperatorBounds s o κ) {f : Field D} (hf : MeanClass s α f) :
    MeanClass s (α - κ) (o.dr f) :=
  hf.graphDerivative ho.radialProfile ho.radialFrequency ho.kappa_nonneg o.eR o.vR

theorem dz (ho : OperatorBounds s o κ) {f : Field D} (hf : MeanClass s α f) :
    MeanClass s (α + 1) (o.dz f) := by
  have h := (hf.directional o.eZ).band_smul ho.epsilon
  simp only [smul_eq_mul] at h
  exact h

theorem slowTime (ho : OperatorBounds s o κ) {f : Field D} (hf : MeanClass s α f) :
    MeanClass s (α + 1) (o.slowTime f) := by
  have h := Class.neg ((hf.directional o.eT).band_smul ho.epsilon)
  simp only [smul_eq_mul] at h
  exact h

theorem fastTime (ho : OperatorBounds s o κ) {f : Field D} (hf : MeanClass s α f) :
    MeanClass s α (o.fastTime f) := by
  have h := (hf.directional o.vT).band_smul ho.fastCoefficient
  simp only [smul_eq_mul, add_zero] at h
  exact h

theorem time (ho : OperatorBounds s o κ) {f : Field D} (hf : MeanClass s α f) :
    MeanClass s α (o.time f) :=
  ((ho.slowTime hf).mono_exponent (by linarith)).add (ho.fastTime hf)

theorem inv_mul (ho : OperatorBounds s o κ) {f : Field D} (hf : MeanClass s α f) :
    MeanClass s α (o.invRadius * f) := by
  simpa only [zero_add] using Class.coefficient_mul ho.invRadius hf

theorem radialDiv (ho : OperatorBounds s o κ) {f : Field D} (hf : MeanClass s α f) (c : ℝ) :
    MeanClass s (α - κ) (o.radialDiv c f) :=
  (ho.dr hf).add ((Class.smul (ho.inv_mul hf) c).mono_exponent
    (sub_le_self α ho.kappa_nonneg))

theorem viscosity (ho : OperatorBounds s o κ) {f : Field D} (hf : MeanClass s α f) (c : ℝ) :
    MeanClass s (α + 1 - 2 * κ) (o.viscosity c f) := by
  have hrr : MeanClass s (α - 2 * κ) (o.dr (o.dr f)) := by
    convert! ho.dr (ho.dr hf) using 1
    ring
  have hr : MeanClass s (α - 2 * κ) (o.invRadius * o.dr f) :=
    (ho.inv_mul (ho.dr hf)).mono_exponent (by linarith [ho.kappa_nonneg])
  have hzz : MeanClass s (α - 2 * κ) (o.dz (o.dz f)) :=
    (ho.dz (ho.dz hf)).mono_exponent (by linarith [ho.kappa_nonneg])
  have hc : MeanClass s (α - 2 * κ) (c • (o.invRadius * (o.invRadius * f))) :=
    (Class.smul (ho.inv_mul (ho.inv_mul hf)) c).mono_exponent
      (by linarith [ho.kappa_nonneg])
  have hb := (Class.sub ((hrr.add hr).add hzz) hc).band_smul ho.epsilon
  convert! hb using 1
  ring

end OperatorBounds

noncomputable def thetaRadial (b m : Triple D) : Field D :=
  b.radial * m.angular + m.radial * b.angular + m.radial * m.angular

noncomputable def thetaAxial (b m : Triple D) : Field D :=
  b.axial * m.angular + b.angular * m.axial + m.axial * m.angular

noncomputable def axialRadial (b m : Triple D) : Field D :=
  b.radial * m.axial + m.radial * b.axial + m.radial * m.axial

noncomputable def axialAxial (b m : Triple D) : Field D :=
  (2 : ℝ) • (b.axial * m.axial) + m.axial * m.axial

noncomputable def radialRadial (b m : Triple D) : Field D :=
  (2 : ℝ) • (b.radial * m.radial) + m.radial * m.radial

noncomputable def radialAngular (b m : Triple D) : Field D :=
  (2 : ℝ) • (b.angular * m.angular) + m.angular * m.angular

noncomputable def thetaResidual (o : Operators D) (b m : Triple D)
    (W : Fin 3 → Fin 3 → Field D) (T : Field D) : Field D :=
  o.time m.angular + o.radialDiv 2 (thetaRadial b m + W 0 1) +
    o.dz (thetaAxial b m + W 2 1) - o.viscosity 1 m.angular - o.radialDiv 2 T

noncomputable def axialResidual (o : Operators D) (b m : Triple D)
    (W : Fin 3 → Fin 3 → Field D) (p T : Field D) : Field D :=
  o.time m.axial + o.radialDiv 1 (axialRadial b m + W 0 2) +
    o.dz (axialAxial b m + W 2 2 + p) - o.viscosity 0 m.axial - o.radialDiv 1 T

noncomputable def gr (o : Operators D) (b m : Triple D)
    (W : Fin 3 → Fin 3 → Field D) : Field D :=
  -(o.time m.radial + o.radialDiv 1 (radialRadial b m + W 0 0) +
    o.dz (axialRadial b m + W 2 0) -
    o.invRadius * (radialAngular b m + W 1 1) - o.viscosity 1 m.radial)

noncomputable def deltaThetaRadial (b m h : Triple D) : Field D :=
  b.radial * h.angular + h.radial * b.angular + m.radial * h.angular +
    h.radial * m.angular + h.radial * h.angular

noncomputable def deltaThetaAxial (b m h : Triple D) : Field D :=
  b.axial * h.angular + b.angular * h.axial + m.axial * h.angular +
    h.axial * m.angular + h.axial * h.angular

noncomputable def deltaAxialRadial (b m h : Triple D) : Field D :=
  b.radial * h.axial + h.radial * b.axial + m.radial * h.axial +
    h.radial * m.axial + h.radial * h.axial

noncomputable def deltaAxialAxial (b m h : Triple D) : Field D :=
  (2 : ℝ) • (b.axial * h.axial) + (2 : ℝ) • (m.axial * h.axial) + h.axial * h.axial

noncomputable def deltaRadialRadial (b m h : Triple D) : Field D :=
  (2 : ℝ) • (b.radial * h.radial) + (2 : ℝ) • (m.radial * h.radial) + h.radial * h.radial

noncomputable def radialAngularRemainder (m h : Triple D) : Field D :=
  (2 : ℝ) • (m.angular * h.angular) + h.angular * h.angular

noncomputable def leadingRadial (o : Operators D) (b h : Triple D) : Field D :=
  o.invRadius * ((2 : ℝ) • (b.angular * h.angular))

noncomputable def radialRemainder (o : Operators D) (b m h : Triple D) : Field D :=
  -o.time h.radial - o.radialDiv 1 (deltaRadialRadial b m h) -
    o.dz (deltaAxialRadial b m h) + o.invRadius * radialAngularRemainder m h +
    o.viscosity 1 h.radial

noncomputable def thetaRemainder (o : Operators D) (b m h : Triple D) : Field D :=
  o.slowTime h.angular + o.radialDiv 2 (deltaThetaRadial b m h) +
    o.dz (deltaThetaAxial b m h) - o.viscosity 1 h.angular

noncomputable def axialRemainder (o : Operators D) (b m h : Triple D)
    (δp : Field D) : Field D :=
  o.slowTime h.axial + o.radialDiv 1 (deltaAxialRadial b m h) +
    o.dz (deltaAxialAxial b m h + δp) - o.viscosity 0 h.axial

structure BaseBounds (s : StripData D) (b : Triple D) : Prop where
  radial : UnweightedClass s 1 b.radial
  angular : UnweightedClass s 0 b.angular
  axial : UnweightedClass s 0 b.axial

structure CumulativeBounds (s : StripData D) (m : Triple D) : Prop where
  radial : MeanClass s (19 / 10) m.radial
  angular : MeanClass s (9 / 10) m.angular
  axial : MeanClass s (9 / 10) m.axial

structure IncrementBounds (s : StripData D) (H : ℝ) (h : Triple D) : Prop where
  radial : MeanClass s (H + 1) h.radial
  angular : MeanClass s H h.angular
  axial : MeanClass s H h.axial

section Bounds
variable {s : StripData D} {o : Operators D} {κ H : ℝ} {b m h : Triple D}
  (ho : OperatorBounds s o κ) (hb : BaseBounds s b) (hm : CumulativeBounds s m)
  (hh : IncrementBounds s H h) (hH : 9 / 10 ≤ H)

include ho hb hm hh hH in
theorem deltaThetaRadial_mem : MeanClass s (H + 1) (deltaThetaRadial b m h) := by
  have h1 := (Class.coefficient_mul hb.radial hh.angular).mono_exponent (show H + 1 ≤ 1 + H by
    linarith)
  have h2 := (Class.mul_coefficient hh.radial hb.angular).mono_exponent (show H + 1 ≤ (H + 1) + 0
    by simp)
  have h3 := (Class.product hm.radial hh.angular ho.weight_le_one).mono_exponent
    (show H + 1 ≤ 19 / 10 + H by linarith)
  have h4 := (Class.product hh.radial hm.angular ho.weight_le_one).mono_exponent
    (show H + 1 ≤ (H + 1) + 9 / 10 by linarith)
  have h5 := (Class.product hh.radial hh.angular ho.weight_le_one).mono_exponent
    (show H + 1 ≤ (H + 1) + H by linarith)
  exact (((h1.add h2).add h3).add h4).add h5

include ho hb hm hh hH in
theorem deltaThetaAxial_mem : MeanClass s H (deltaThetaAxial b m h) := by
  have h1 := (Class.coefficient_mul hb.axial hh.angular).mono_exponent (show H ≤ 0 + H by simp)
  have h2 := (Class.coefficient_mul hb.angular hh.axial).mono_exponent (show H ≤ 0 + H by simp)
  have h3 := (Class.product hm.axial hh.angular ho.weight_le_one).mono_exponent
    (show H ≤ 9 / 10 + H by linarith)
  have h4 := (Class.product hh.axial hm.angular ho.weight_le_one).mono_exponent
    (show H ≤ H + 9 / 10 by linarith)
  have h5 := (Class.product hh.axial hh.angular ho.weight_le_one).mono_exponent
    (show H ≤ H + H by linarith)
  exact (((h1.add h2).add h3).add h4).add h5

include ho hb hm hh hH in
theorem deltaAxialRadial_mem : MeanClass s (H + 1) (deltaAxialRadial b m h) := by
  have h1 := (Class.coefficient_mul hb.radial hh.axial).mono_exponent (show H + 1 ≤ 1 + H by
    linarith)
  have h2 := (Class.mul_coefficient hh.radial hb.axial).mono_exponent (show H + 1 ≤ (H + 1) + 0 by
    simp)
  have h3 := (Class.product hm.radial hh.axial ho.weight_le_one).mono_exponent
    (show H + 1 ≤ 19 / 10 + H by linarith)
  have h4 := (Class.product hh.radial hm.axial ho.weight_le_one).mono_exponent
    (show H + 1 ≤ (H + 1) + 9 / 10 by linarith)
  have h5 := (Class.product hh.radial hh.axial ho.weight_le_one).mono_exponent
    (show H + 1 ≤ (H + 1) + H by linarith)
  exact (((h1.add h2).add h3).add h4).add h5

include ho hb hm hh hH in
theorem deltaAxialAxial_mem : MeanClass s H (deltaAxialAxial b m h) := by
  have h1 := Class.smul ((Class.coefficient_mul hb.axial hh.axial).mono_exponent
    (show H ≤ 0 + H by simp)) 2
  have h2 := Class.smul ((Class.product hm.axial hh.axial ho.weight_le_one).mono_exponent
    (show H ≤ 9 / 10 + H by linarith)) 2
  have h3 := (Class.product hh.axial hh.axial ho.weight_le_one).mono_exponent
    (show H ≤ H + H by linarith)
  exact (h1.add h2).add h3

include ho hb hm hh hH in
theorem deltaRadialRadial_mem : MeanClass s (H + 2) (deltaRadialRadial b m h) := by
  have h1 := Class.smul ((Class.coefficient_mul hb.radial hh.radial).mono_exponent
    (show H + 2 ≤ 1 + (H + 1) by linarith)) 2
  have h2 := Class.smul ((Class.product hm.radial hh.radial ho.weight_le_one).mono_exponent
    (show H + 2 ≤ 19 / 10 + (H + 1) by linarith)) 2
  have h3 := (Class.product hh.radial hh.radial ho.weight_le_one).mono_exponent
    (show H + 2 ≤ (H + 1) + (H + 1) by linarith)
  exact (h1.add h2).add h3

include ho hm hh hH in
theorem radialAngularRemainder_mem : MeanClass s (H + 9 / 10) (radialAngularRemainder m h) := by
  have h1 := Class.smul ((Class.product hm.angular hh.angular ho.weight_le_one).mono_exponent
    (show H + 9 / 10 ≤ 9 / 10 + H by linarith)) 2
  have h2 := (Class.product hh.angular hh.angular ho.weight_le_one).mono_exponent
    (show H + 9 / 10 ≤ H + H by linarith)
  exact h1.add h2

include ho hb hh in
theorem leadingRadial_mem : MeanClass s H (leadingRadial o b h) := by
  apply ho.inv_mul
  exact Class.smul ((Class.coefficient_mul hb.angular hh.angular).mono_exponent
    (show H ≤ 0 + H by simp)) 2

include ho hb hm hh hH in
/-- Every non-leading term of the actual radial pressure-source change has
the stronger defect exponent. This includes fast time on the radial stream. -/
theorem radialRemainder_mem :
    MeanClass s (H + 9 / 10 - 2 * κ) (radialRemainder o b m h) := by
  have h1 := (ho.time hh.radial).mono_exponent
    (show H + 9 / 10 - 2 * κ ≤ H + 1 by linarith [ho.kappa_nonneg])
  have h2 := (ho.radialDiv (deltaRadialRadial_mem ho hb hm hh hH) 1).mono_exponent
    (show H + 9 / 10 - 2 * κ ≤ (H + 2) - κ by linarith [ho.kappa_nonneg])
  have h3 := (ho.dz (deltaAxialRadial_mem ho hb hm hh hH)).mono_exponent
    (show H + 9 / 10 - 2 * κ ≤ (H + 1) + 1 by linarith [ho.kappa_nonneg])
  have h4 := (ho.inv_mul (radialAngularRemainder_mem ho hm hh hH)).mono_exponent
    (show H + 9 / 10 - 2 * κ ≤ H + 9 / 10 by linarith [ho.kappa_nonneg])
  have h5 := (ho.viscosity hh.radial 1).mono_exponent
    (show H + 9 / 10 - 2 * κ ≤ (H + 1) + 1 - 2 * κ by linarith)
  exact ((Class.sub (Class.sub (Class.neg h1) h2) h3).add h4).add h5

include ho hb hm hh hH in
theorem thetaRemainder_mem : MeanClass s (H + 1 - 2 * κ) (thetaRemainder o b m h) := by
  have h1 := (ho.slowTime hh.angular).mono_exponent
    (show H + 1 - 2 * κ ≤ H + 1 by linarith [ho.kappa_nonneg])
  have h2 := (ho.radialDiv (deltaThetaRadial_mem ho hb hm hh hH) 2).mono_exponent
    (show H + 1 - 2 * κ ≤ (H + 1) - κ by linarith [ho.kappa_nonneg])
  have h3 := (ho.dz (deltaThetaAxial_mem ho hb hm hh hH)).mono_exponent
    (show H + 1 - 2 * κ ≤ H + 1 by linarith [ho.kappa_nonneg])
  exact Class.sub ((h1.add h2).add h3) (ho.viscosity hh.angular 1)

include ho hb hm hh hH in
theorem axialRemainder_mem {δp : Field D} (hp : MeanClass s H δp) :
    MeanClass s (H + 1 - 2 * κ) (axialRemainder o b m h δp) := by
  have h1 := (ho.slowTime hh.axial).mono_exponent
    (show H + 1 - 2 * κ ≤ H + 1 by linarith [ho.kappa_nonneg])
  have h2 := (ho.radialDiv (deltaAxialRadial_mem ho hb hm hh hH) 1).mono_exponent
    (show H + 1 - 2 * κ ≤ (H + 1) - κ by linarith [ho.kappa_nonneg])
  have h3 := (ho.dz ((deltaAxialAxial_mem ho hb hm hh hH).add hp)).mono_exponent
    (show H + 1 - 2 * κ ≤ H + 1 by linarith [ho.kappa_nonneg])
  exact Class.sub ((h1.add h2).add h3) (ho.viscosity hh.axial 0)

end Bounds

structure SmoothTriple (U : Set D) (b : Triple D) : Prop where
  radial : SmoothOn U b.radial
  angular : SmoothOn U b.angular
  axial : SmoothOn U b.axial

theorem BaseBounds.smooth {s : StripData D} {b : Triple D} (h : BaseBounds s b) :
    SmoothTriple s.domain b := ⟨h.radial.smooth, h.angular.smooth, h.axial.smooth⟩

theorem CumulativeBounds.smooth {s : StripData D} {b : Triple D}
    (h : CumulativeBounds s b) : SmoothTriple s.domain b :=
  ⟨h.radial.smooth, h.angular.smooth, h.axial.smooth⟩

theorem IncrementBounds.smooth {s : StripData D} {H : ℝ} {b : Triple D}
    (h : IncrementBounds s H b) : SmoothTriple s.domain b :=
  ⟨h.radial.smooth, h.angular.smooth, h.axial.smooth⟩

namespace SmoothTriple
variable {U : Set D} {b m h : Triple D}

theorem thetaRadial (hb : SmoothTriple U b) (hm : SmoothTriple U m) :
    SmoothOn U (thetaRadial b m) :=
  ((hb.radial.mul hm.angular).add (hm.radial.mul hb.angular)).add
    (hm.radial.mul hm.angular)

theorem thetaAxial (hb : SmoothTriple U b) (hm : SmoothTriple U m) :
    SmoothOn U (thetaAxial b m) :=
  ((hb.axial.mul hm.angular).add (hb.angular.mul hm.axial)).add
    (hm.axial.mul hm.angular)

theorem axialRadial (hb : SmoothTriple U b) (hm : SmoothTriple U m) :
    SmoothOn U (axialRadial b m) :=
  ((hb.radial.mul hm.axial).add (hm.radial.mul hb.axial)).add
    (hm.radial.mul hm.axial)

theorem axialAxial (hb : SmoothTriple U b) (hm : SmoothTriple U m) :
    SmoothOn U (axialAxial b m) :=
  ((hb.axial.mul hm.axial).smul 2).add (hm.axial.mul hm.axial)

theorem radialRadial (hb : SmoothTriple U b) (hm : SmoothTriple U m) :
    SmoothOn U (radialRadial b m) :=
  ((hb.radial.mul hm.radial).smul 2).add (hm.radial.mul hm.radial)

theorem deltaThetaRadial (hb : SmoothTriple U b) (hm : SmoothTriple U m)
    (hh : SmoothTriple U h) : SmoothOn U (deltaThetaRadial b m h) :=
  ((((hb.radial.mul hh.angular).add (hh.radial.mul hb.angular)).add
    (hm.radial.mul hh.angular)).add (hh.radial.mul hm.angular)).add
      (hh.radial.mul hh.angular)

theorem deltaThetaAxial (hb : SmoothTriple U b) (hm : SmoothTriple U m)
    (hh : SmoothTriple U h) : SmoothOn U (deltaThetaAxial b m h) :=
  ((((hb.axial.mul hh.angular).add (hb.angular.mul hh.axial)).add
    (hm.axial.mul hh.angular)).add (hh.axial.mul hm.angular)).add
      (hh.axial.mul hh.angular)

theorem deltaAxialRadial (hb : SmoothTriple U b) (hm : SmoothTriple U m)
    (hh : SmoothTriple U h) : SmoothOn U (deltaAxialRadial b m h) :=
  ((((hb.radial.mul hh.axial).add (hh.radial.mul hb.axial)).add
    (hm.radial.mul hh.axial)).add (hh.radial.mul hm.axial)).add
      (hh.radial.mul hh.axial)

theorem deltaAxialAxial (hb : SmoothTriple U b) (hm : SmoothTriple U m)
    (hh : SmoothTriple U h) : SmoothOn U (deltaAxialAxial b m h) :=
  (((hb.axial.mul hh.axial).smul 2).add ((hm.axial.mul hh.axial).smul 2)).add
    (hh.axial.mul hh.axial)

theorem deltaRadialRadial (hb : SmoothTriple U b) (hm : SmoothTriple U m)
    (hh : SmoothTriple U h) : SmoothOn U (deltaRadialRadial b m h) :=
  (((hb.radial.mul hh.radial).smul 2).add ((hm.radial.mul hh.radial).smul 2)).add
    (hh.radial.mul hh.radial)

end SmoothTriple

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem thetaRadial_updated (b m h : Triple D) :
    thetaRadial b (updated m h) = thetaRadial b m + deltaThetaRadial b m h := by
  ext n x
  simp only [thetaRadial, updated, deltaThetaRadial, Pi.add_apply, Pi.mul_apply]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem thetaAxial_updated (b m h : Triple D) :
    thetaAxial b (updated m h) = thetaAxial b m + deltaThetaAxial b m h := by
  ext n x
  simp only [thetaAxial, updated, deltaThetaAxial, Pi.add_apply, Pi.mul_apply]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem axialRadial_updated (b m h : Triple D) :
    axialRadial b (updated m h) = axialRadial b m + deltaAxialRadial b m h := by
  ext n x
  simp only [axialRadial, updated, deltaAxialRadial, Pi.add_apply, Pi.mul_apply]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem axialAxial_updated (b m h : Triple D) :
    axialAxial b (updated m h) = axialAxial b m + deltaAxialAxial b m h := by
  ext n x
  simp only [axialAxial, updated, deltaAxialAxial, Pi.add_apply, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem radialRadial_updated (b m h : Triple D) :
    radialRadial b (updated m h) = radialRadial b m + deltaRadialRadial b m h := by
  ext n x
  simp only [radialRadial, updated, deltaRadialRadial, Pi.add_apply, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem radialAngular_updated (b m h : Triple D) :
    radialAngular b (updated m h) = radialAngular b m +
      (2 : ℝ) • (b.angular * h.angular) + radialAngularRemainder m h := by
  ext n x
  simp only [radialAngular, updated, radialAngularRemainder, Pi.add_apply, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

section ExactChanges
variable {U : Set D} (hU : IsOpen U) (o : Operators D)
  (ha : ContDiffOn ℝ ∞ o.radialProfile U) {b m h : Triple D}
  (hb : SmoothTriple U b) (hm : SmoothTriple U m) (hh : SmoothTriple U h)
  (W : Fin 3 → Fin 3 → Field D) (hW : ∀ i j, SmoothOn U (W i j))

include hU ha hb hm hh hW in
theorem thetaResidual_change (T : Field D) :
    Agree U (thetaResidual o b (updated m h) W T - thetaResidual o b m W T)
      (o.fastTime h.angular + thetaRemainder o b m h) := by
  have hr : thetaRadial b (updated m h) + W 0 1 =
      (thetaRadial b m + W 0 1) + deltaThetaRadial b m h := by
    rw [thetaRadial_updated]; abel
  have hz : thetaAxial b (updated m h) + W 2 1 =
      (thetaAxial b m + W 2 1) + deltaThetaAxial b m h := by
    rw [thetaAxial_updated]; abel
  intro n x hx
  simp only [thetaResidual, Pi.sub_apply, Pi.add_apply]
  rw [hr, hz]
  simp only [updated]
  rw [o.time_add hU hm.angular hh.angular n hx,
    o.radialDiv_add hU 2 ((hb.thetaRadial hm).add (hW 0 1))
      (hb.deltaThetaRadial hm hh) n hx,
    o.dz_add hU ((hb.thetaAxial hm).add (hW 2 1)) (hb.deltaThetaAxial hm hh) n hx,
    o.viscosity_add hU ha 1 hm.angular hh.angular n hx]
  simp only [thetaRemainder, Operators.time, Pi.add_apply, Pi.sub_apply]
  ring

include hU ha hb hm hh hW in
theorem axialResidual_change (p δp T : Field D) (hp : SmoothOn U p)
    (hδp : SmoothOn U δp) :
    Agree U (axialResidual o b (updated m h) W (p + δp) T - axialResidual o b m W p T)
      (o.fastTime h.axial + axialRemainder o b m h δp) := by
  have hr : axialRadial b (updated m h) + W 0 2 =
      (axialRadial b m + W 0 2) + deltaAxialRadial b m h := by
    rw [axialRadial_updated]; abel
  have hz : axialAxial b (updated m h) + W 2 2 + (p + δp) =
      (axialAxial b m + W 2 2 + p) + (deltaAxialAxial b m h + δp) := by
    rw [axialAxial_updated]; abel
  intro n x hx
  simp only [axialResidual, Pi.sub_apply, Pi.add_apply]
  rw [hr, hz]
  simp only [updated]
  rw [o.time_add hU hm.axial hh.axial n hx,
    o.radialDiv_add hU 1 ((hb.axialRadial hm).add (hW 0 2))
      (hb.deltaAxialRadial hm hh) n hx,
    o.dz_add hU (((hb.axialAxial hm).add (hW 2 2)).add hp)
      ((hb.deltaAxialAxial hm hh).add hδp) n hx,
    o.viscosity_add hU ha 0 hm.axial hh.axial n hx]
  simp only [axialRemainder, Operators.time, Pi.add_apply, Pi.sub_apply]
  ring

include hU ha hb hm hh hW in
theorem gr_change :
    Agree U (gr o b (updated m h) W - gr o b m W)
      (leadingRadial o b h + radialRemainder o b m h) := by
  have hr : radialRadial b (updated m h) + W 0 0 =
      (radialRadial b m + W 0 0) + deltaRadialRadial b m h := by
    rw [radialRadial_updated]; abel
  have hz : axialRadial b (updated m h) + W 2 0 =
      (axialRadial b m + W 2 0) + deltaAxialRadial b m h := by
    rw [axialRadial_updated]; abel
  intro n x hx
  simp only [gr, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.mul_apply]
  rw [hr, hz, radialAngular_updated]
  simp only [updated]
  rw [o.time_add hU hm.radial hh.radial n hx,
    o.radialDiv_add hU 1 ((hb.radialRadial hm).add (hW 0 0))
      (hb.deltaRadialRadial hm hh) n hx,
    o.dz_add hU ((hb.axialRadial hm).add (hW 2 0)) (hb.deltaAxialRadial hm hh) n hx,
    o.viscosity_add hU ha 1 hm.radial hh.radial n hx]
  simp only [leadingRadial, radialRemainder, Pi.add_apply, Pi.sub_apply,
    Pi.neg_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

end ExactChanges

theorem cumulative_updated {s : StripData D} {H : ℝ} {m h : Triple D}
    (hm : CumulativeBounds s m) (hh : IncrementBounds s H h) (hH : 9 / 10 ≤ H) :
    CumulativeBounds s (updated m h) :=
  ⟨hm.radial.add (hh.radial.mono_exponent (by linarith)),
    hm.angular.add (hh.angular.mono_exponent hH),
    hm.axial.add (hh.axial.mono_exponent hH)⟩

section ActualBounds
variable {s : StripData D} {o : Operators D} {κ H : ℝ} {b m h : Triple D}
  (ho : OperatorBounds s o κ) (hb : BaseBounds s b) (hm : CumulativeBounds s m)
  (hh : IncrementBounds s H h) (hH : 9 / 10 ≤ H)
  (W : Fin 3 → Fin 3 → Field D) (hW : ∀ i j, SmoothOn s.domain (W i j))

include ho hb hm hh hH hW in
theorem thetaResidual_change_sub_fast_mem (T : Field D) :
    MeanClass s (H + 1 - 2 * κ)
      (thetaResidual o b (updated m h) W T - thetaResidual o b m W T -
        o.fastTime h.angular) := by
  apply class_congr (thetaRemainder_mem ho hb hm hh hH)
  intro n x hx
  have he := thetaResidual_change s.isOpen_domain o (ho.radialProfile.smooth 0)
    hb.smooth hm.smooth hh.smooth W hW T n hx
  simp only [Pi.sub_apply, Pi.add_apply] at he ⊢
  linarith

include ho hb hm hh hH hW in
theorem axialResidual_change_sub_fast_mem (p δp T : Field D)
    (hp : SmoothOn s.domain p) (hδp : MeanClass s H δp) :
    MeanClass s (H + 1 - 2 * κ)
      (axialResidual o b (updated m h) W (p + δp) T - axialResidual o b m W p T -
        o.fastTime h.axial) := by
  apply class_congr (axialRemainder_mem ho hb hm hh hH hδp)
  intro n x hx
  have he := axialResidual_change s.isOpen_domain o (ho.radialProfile.smooth 0)
    hb.smooth hm.smooth hh.smooth W hW p δp T hp hδp.smooth n hx
  simp only [Pi.sub_apply, Pi.add_apply] at he ⊢
  linarith

include ho hb hm hh hH hW in
/-- The actual radial source change retains the leading centrifugal term. -/
theorem gr_change_sub_leading_mem :
    MeanClass s (H + 9 / 10 - 2 * κ)
      (gr o b (updated m h) W - gr o b m W - leadingRadial o b h) := by
  apply class_congr (radialRemainder_mem ho hb hm hh hH)
  intro n x hx
  have he := gr_change s.isOpen_domain o (ho.radialProfile.smooth 0)
    hb.smooth hm.smooth hh.smooth W hW n hx
  simp only [Pi.sub_apply, Pi.add_apply] at he ⊢
  linarith

include ho hb hm hh hH hW in
theorem gr_change_mem (hκ : 2 * κ ≤ 9 / 10) :
    MeanClass s H (gr o b (updated m h) W - gr o b m W) := by
  apply class_congr ((leadingRadial_mem ho hb hh).add
    ((radialRemainder_mem ho hb hm hh hH).mono_exponent (by linarith)))
  exact gr_change s.isOpen_domain o (ho.radialProfile.smooth 0)
    hb.smooth hm.smooth hh.smooth W hW

include ho hb hm hh hH hW in
theorem thetaResidual_change_slow_mem (T : Field D)
    (hslow : ∀ n x, x ∈ s.domain → fderiv ℝ (h.angular n) x o.vT = 0) :
    MeanClass s (H + 1 - 2 * κ)
      (thetaResidual o b (updated m h) W T - thetaResidual o b m W T) := by
  apply class_congr (thetaResidual_change_sub_fast_mem ho hb hm hh hH W hW T)
  intro n x hx
  simp only [Pi.sub_apply, Operators.fastTime, hslow n x hx, mul_zero, sub_zero]

include ho hb hm hh hH hW in
theorem axialResidual_change_slow_mem (p δp T : Field D)
    (hp : SmoothOn s.domain p) (hδp : MeanClass s H δp)
    (hslow : ∀ n x, x ∈ s.domain → fderiv ℝ (h.axial n) x o.vT = 0) :
    MeanClass s (H + 1 - 2 * κ)
      (axialResidual o b (updated m h) W (p + δp) T - axialResidual o b m W p T) := by
  apply class_congr (axialResidual_change_sub_fast_mem ho hb hm hh hH W hW p δp T hp hδp)
  intro n x hx
  simp only [Pi.sub_apply, Operators.fastTime, hslow n x hx, mul_zero, sub_zero]

end ActualBounds

/-- Independence along an actual affine line removes its Fréchet derivative. -/
theorem directional_zero_of_line_const {f : D → ℝ} {x v : D}
    (hf : DifferentiableAt ℝ f x) (hline : ∀ t : ℝ, f (x + t • v) = f x) :
    fderiv ℝ f x v = 0 := by
  have hd : HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 := by
    apply hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    · simpa only [one_smul, id_eq] using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x)
    · simp
  have he : (fun t : ℝ => f (x + t • v)) = fun _ => f x := funext hline
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 (f x))

/-- A field depending only on the slow projection has no fast derivative. -/
theorem directional_zero_of_factor {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (π : D →L[ℝ] P) {f : P → ℝ} {x v : D}
    (hf : DifferentiableAt ℝ f (π x)) (hv : π v = 0) :
    fderiv ℝ (fun y => f (π y)) x v = 0 := by
  change fderiv ℝ (f ∘ π) x v = 0
  rw [(hf.hasFDerivAt.comp x π.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply, hv, map_zero]

section PressureReconstruction

open MeasureTheory Function WeightedRadialPrimitive
open scoped Interval

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem radialSupport_sub {a b : ℝ} {f g : ℝ × P → ℝ}
    (hf : RadialAlias.RadiallySupported a b f)
    (hg : RadialAlias.RadiallySupported a b g) :
    RadialAlias.RadiallySupported a b (fun x => f x - g x) :=
  (support_sub f g).trans (union_subset hf hg)

/-- An interior radial cutoff belongs to the same flat mean class. The
constant comes from its actual jets and the positive weight on its support. -/
theorem interior_cutoff_meanClass
    {a b cL cR l r : ℝ} (ha : 0 < a) (hal : a < l) (hrb : r < b)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hs : support χ ⊆ Icc l r) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) 0
      (fun _ (x : ℝ × P) => χ x.1) := by
  have hlog : ContinuousOn (fun x : ℝ => logPosition a x) (Icc l r) :=
    (continuousOn_id.div_const a).log (fun x hx =>
      (div_pos (ha.trans (hal.trans_le hx.1)) ha).ne')
  obtain ⟨d, hd, hmargin⟩ := UniformCone.positive_uniform_margin isCompact_Icc
    ((zeta_continuous hcL hcR (logLength a b)).comp_continuousOn hlog)
    (fun x (hx : x ∈ Icc l r) => zeta_pos cL cR
      (logPosition_mem ha ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩))
  have hsupport : RadialAlias.RadiallySupported l r (fun x : ℝ × P => χ x.1) :=
    fun _ hx => hs hx
  refine ⟨fun _ x hx => (zeta_pos cL cR (logPosition_mem ha hx)).le,
    fun _ => (hχ.comp contDiff_fst).contDiffOn, ?_⟩
  intro m
  obtain ⟨B, hB, hbound⟩ := cutoff_finiteJet_bound (E := P) a b χ hχ m
  refine ⟨B / d, div_nonneg hB hd.le, 0, ?_⟩
  intro n x hx j hj
  rw [logStrip_majorant_eq ha hcL hcR ε S hε hεone hS 0 (B / d) 0 n x hx]
  simp only [Real.rpow_zero, pow_zero, mul_one, logWeight, weight, div_one]
  by_cases hm : x.1 ∈ Icc l r
  · calc
      _ ≤ B := hbound j hj x ⟨hx.1.le, hx.2.le⟩
      _ = (B / d) * d := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmargin x.1 hm) (div_nonneg hB hd.le)
  · have hz : iteratedFDeriv ℝ j (fun x : ℝ × P => χ x.1) x = 0 := by
      by_contra hn
      exact hm ((TransportPrimitive.iteratedFDeriv_supported hsupport j) hn)
    rw [hz, norm_zero]
    exact mul_nonneg (div_nonneg hB hd.le) (zeta_pos cL cR (logPosition_mem ha hx)).le

/-- The density in (33) is the actual normalized bump, not an assumed
flat multiplier. -/
theorem rho_meanClass
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) 0
      (fun _ (x : ℝ × P) => PressureStream.rho a b hab x.1) := by
  apply interior_cutoff_meanClass ha (show a < (3 * a + b) / 4 by linarith)
    (show (a + 3 * b) / 4 < b by linarith) hcL hcR ε S hε hεone hS
    _ (PressureStream.rho_contDiff a b hab)
  intro x hx
  rw [PressureStream.rho, ContDiffBump.support_normed_eq] at hx
  change dist x ((a + b) / 2) < (b - a) / 4 at hx
  rw [Real.dist_eq, abs_lt] at hx
  constructor <;> linarith [hx.1, hx.2]

theorem pressureMass_sub {a b : ℝ} {f g : PressureStream.Lift P → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hsf : RadialAlias.RadiallySupported a b f)
    (hsg : RadialAlias.RadiallySupported a b g) :
    PressureStream.pressureMass (fun x => f x - g x) =
      fun p => PressureStream.pressureMass f p - PressureStream.pressureMass g p := by
  funext p
  simp only [PressureStream.pressureMass, PressureStream.torusAverage_sub hf.continuous
    hg.continuous]
  exact integral_sub (PressureStream.torusAverage_slice_integrable hf hsf p)
    (PressureStream.torusAverage_slice_integrable hg hsg p)

theorem pressureSource_sub {a b : ℝ} (hab : a < b) {f g : PressureStream.Lift P → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hsf : RadialAlias.RadiallySupported a b f)
    (hsg : RadialAlias.RadiallySupported a b g) :
    PressureStream.pressureSource a b hab (fun x => f x - g x) =
      fun x => PressureStream.pressureSource a b hab f x -
        PressureStream.pressureSource a b hab g x := by
  funext x
  simp only [PressureStream.pressureSource, pressureMass_sub hf hg hsf hsg]
  ring

theorem compactIntegral_sub {a b M : ℝ} {v : P} {f g : ℝ × P → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hsf : RadialAlias.RadiallySupported a b f)
    (hsg : RadialAlias.RadiallySupported a b g) (χ : ℝ → ℝ) (z : ℝ × P) :
    TransportPrimitive.compactIntegral χ M v (fun x => f x - g x) z =
      TransportPrimitive.compactIntegral χ M v f z -
        TransportPrimitive.compactIntegral χ M v g z := by
  have hp : TransportPrimitive.pastIntegral M v (fun x => f x - g x) z =
      TransportPrimitive.pastIntegral M v f z - TransportPrimitive.pastIntegral M v g z :=
    integral_sub (TransportPrimitive.shifted_integrable hf hsf z).integrableOn
      (TransportPrimitive.shifted_integrable hg hsg z).integrableOn
  have ht : TransportPrimitive.totalIntegral M v (fun x => f x - g x) z =
      TransportPrimitive.totalIntegral M v f z - TransportPrimitive.totalIntegral M v g z :=
    integral_sub (TransportPrimitive.shifted_integrable hf hsf z)
      (TransportPrimitive.shifted_integrable hg hsg z)
  simp only [TransportPrimitive.compactIntegral, hp, ht, smul_sub]
  abel

theorem physicalCompact_sub {a b d : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    {f g : ℝ × P → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hsf : RadialAlias.RadiallySupported a b f)
    (hsg : RadialAlias.RadiallySupported a b g) (M : ℝ) (v : P) :
    RadialPullback.physicalCompact d a b M v (fun x => f x - g x) =
      fun x => RadialPullback.physicalCompact d a b M v f x -
        RadialPullback.physicalCompact d a b M v g x := by
  have hn : RadialPullback.normalizeSource d a (fun x => f x - g x) =
      fun x => RadialPullback.normalizeSource d a f x - RadialPullback.normalizeSource d a g x := by
    funext x
    simp only [RadialPullback.normalizeSource, smul_sub]
  funext x
  simp only [RadialPullback.physicalCompact, RadialPullback.pullback, Function.comp_apply, hn]
  exact compactIntegral_sub (RadialPullback.normalizeSource_contDiff ha hd hf).continuous
    (RadialPullback.normalizeSource_contDiff ha hd hg).continuous
    (RadialPullback.normalizeSource_supported ha hab hd hsf)
    (RadialPullback.normalizeSource_supported ha hab hd hsg) _ _

/-- Recomputing (33) after an update is exactly applying its linear integral
operator to the actual radial source difference. -/
theorem meanPressure_sub {a b d : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    {f g : PressureStream.Lift P → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hsf : RadialAlias.RadiallySupported a b f)
    (hsg : RadialAlias.RadiallySupported a b g) (M : ℝ) (v : PressureStream.Plane) :
    PressureStream.meanPressure d a b M hab v (fun x => f x - g x) =
      fun x => PressureStream.meanPressure d a b M hab v f x -
        PressureStream.meanPressure d a b M hab v g x := by
  rw [PressureStream.meanPressure, pressureSource_sub hab hf hg hsf hsg]
  exact physicalCompact_sub ha hab hd
    (PressureStream.pressureSource_contDiff hab hf hsf)
    (PressureStream.pressureSource_contDiff hab hg hsg)
    (PressureStream.pressureSource_supported hab hsf)
    (PressureStream.pressureSource_supported hab hsg) M (0, v)

theorem meanClass_pressureSource
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {α : ℝ} {f : ℕ → PressureStream.Lift P → ℝ}
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n))
    (hclass : MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α f) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α
      (fun n => PressureStream.pressureSource a b hab (f n)) := by
  have hmass := MeanMomentBounds.meanClass_pressureMass_lift ha hab hcL hcR
    ε S hε hεone hS hf hs hclass
  have hρ := rho_meanClass (P := P × PressureStream.Plane) ha hab hcL hcR ε S hε hεone hS
  have hproduct := Class.mul_coefficient hρ hmass
  simp only [zero_add] at hproduct
  exact Class.sub hclass hproduct

/-- The actual normalized shifted pressure primitive preserves every
fixed-jet mean class, uniformly over its radial and torus shifts. -/
theorem meanClass_meanPressure
    {a b d cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {α : ℝ} {f : ℕ → PressureStream.Lift P → ℝ}
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n))
    (hclass : MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α
      (fun n => PressureStream.meanPressure d a b (M n) hab (v n) (f n)) := by
  exact RadialPullback.meanClass_physicalCompact ha hab hd hcL hcR ε S hε hεone hS
    α M (fun n => (0, v n)) _
    (fun n => PressureStream.pressureSource_contDiff hab (hf n) (hs n))
    (fun n => PressureStream.pressureSource_supported hab (hs n))
    (meanClass_pressureSource ha hab hcL hcR ε S hε hεone hS hf hs hclass)

theorem meanClass_meanPressure_change
    {a b d cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {α : ℝ} {f g : ℕ → PressureStream.Lift P → ℝ}
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hg : ∀ n, ContDiff ℝ ∞ (g n))
    (hsf : ∀ n, RadialAlias.RadiallySupported a b (f n))
    (hsg : ∀ n, RadialAlias.RadiallySupported a b (g n))
    (hclass : MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α (f - g))
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α
      (fun n x => PressureStream.meanPressure d a b (M n) hab (v n) (f n) x -
        PressureStream.meanPressure d a b (M n) hab (v n) (g n) x) := by
  apply class_congr (meanClass_meanPressure ha hab hd hcL hcR ε S hε hεone hS
    (fun n => (hf n).sub (hg n)) (fun n => radialSupport_sub (hsf n) (hsg n)) hclass M v)
  intro n x _
  exact (congrFun (meanPressure_sub ha hab hd (hf n) (hg n) (hsf n) (hsg n) (M n) (v n)) x).symm

noncomputable def reconstructedPressure (d a b : ℝ) (hab : a < b)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) (o : Operators (PressureStream.Lift P))
    (base mean : Triple (PressureStream.Lift P))
    (W : Fin 3 → Fin 3 → Field (PressureStream.Lift P)) : Field (PressureStream.Lift P) :=
  fun n => PressureStream.meanPressure d a b (M n) hab (v n) (gr o base mean W n)

/-- Pressure is recomputed from the literal `gr`; its change class is a
conclusion, obtained from the centrifugal term and the exact remainder. -/
theorem reconstructedPressure_change_mem
    {a b d cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {κ H : ℝ}
    {o : Operators (PressureStream.Lift P)} {base mean inc : Triple (PressureStream.Lift P)}
    (ho : OperatorBounds (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) o κ)
    (hb : BaseBounds (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) base)
    (hm : CumulativeBounds (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) mean)
    (hh : IncrementBounds (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) H inc)
    (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10)
    (W : Fin 3 → Fin 3 → Field (PressureStream.Lift P))
    (hW : ∀ i j, SmoothOn (logStripData a b cL cR ha hcL hcR ε S hε hεone hS).domain (W i j))
    (hf : ∀ n, ContDiff ℝ ∞ (gr o base (updated mean inc) W n))
    (hg : ∀ n, ContDiff ℝ ∞ (gr o base mean W n))
    (hsf : ∀ n, RadialAlias.RadiallySupported a b (gr o base (updated mean inc) W n))
    (hsg : ∀ n, RadialAlias.RadiallySupported a b (gr o base mean W n))
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) H
      (reconstructedPressure d a b hab M v o base (updated mean inc) W -
        reconstructedPressure d a b hab M v o base mean W) := by
  exact meanClass_meanPressure_change ha hab hd hcL hcR ε S hε hεone hS hf hg hsf hsg
    (gr_change_mem ho hb hm hh hH W hW hκ) M v

section ReconstructedTangential

variable {a b d cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
  (hcL : 0 < cL) (hcR : 0 < cR)
  (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
  (hS : ∀ n, 1 ≤ S n) {κ H : ℝ}
  {o : Operators (PressureStream.Lift P)} {base mean inc : Triple (PressureStream.Lift P)}
  (ho : OperatorBounds (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) o κ)
  (hb : BaseBounds (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) base)
  (hm : CumulativeBounds (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) mean)
  (hh : IncrementBounds (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) H inc)
  (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10)
  (W : Fin 3 → Fin 3 → Field (PressureStream.Lift P))
  (hW : ∀ i j, SmoothOn (logStripData a b cL cR ha hcL hcR ε S hε hεone hS).domain (W i j))
  (hf : ∀ n, ContDiff ℝ ∞ (gr o base (updated mean inc) W n))
  (hg : ∀ n, ContDiff ℝ ∞ (gr o base mean W n))
  (hsf : ∀ n, RadialAlias.RadiallySupported a b (gr o base (updated mean inc) W n))
  (hsg : ∀ n, RadialAlias.RadiallySupported a b (gr o base mean W n))

include hd ho hb hm hh hH hκ hW hf hg hsf hsg in
/-- Every tangential effect beyond the actual fast derivative has the
claimed exponent, including the recomputed axial pressure contribution. -/
theorem tangential_recomputedPressure_change_mem
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane)
    (Tθ Tz : Field (PressureStream.Lift P)) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) (H + 1 - 2 * κ)
      (thetaResidual o base (updated mean inc) W Tθ - thetaResidual o base mean W Tθ -
        o.fastTime inc.angular) ∧
    MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) (H + 1 - 2 * κ)
      (axialResidual o base (updated mean inc) W
          (reconstructedPressure d a b hab M v o base (updated mean inc) W) Tz -
        axialResidual o base mean W (reconstructedPressure d a b hab M v o base mean W) Tz -
        o.fastTime inc.axial) := by
  refine ⟨thetaResidual_change_sub_fast_mem ho hb hm hh hH W hW Tθ, ?_⟩
  let p0 := reconstructedPressure d a b hab M v o base mean W
  let p1 := reconstructedPressure d a b hab M v o base (updated mean inc) W
  have hδ : MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) H (p1 - p0) :=
    reconstructedPressure_change_mem ha hab hd hcL hcR ε S hε hεone hS
      ho hb hm hh hH hκ W hW hf hg hsf hsg M v
  have hp0 : SmoothOn (logStripData a b cL cR ha hcL hcR ε S hε hεone hS).domain p0 :=
    fun n => (PressureStream.meanPressure_contDiff ha hab hd (v n) (hg n) (hsg n)).contDiffOn
  have he : p0 + (p1 - p0) = p1 := by abel
  simpa only [he] using
    axialResidual_change_sub_fast_mem ho hb hm hh hH W hW p0 (p1 - p0) Tz hp0 hδ

include hd ho hb hm hh hH hκ hW hf hg hsf hsg in
/-- In the slow rank update the fast derivatives vanish, so the estimates
hold directly for the full changes of the tangential residuals. -/
theorem tangential_recomputedPressure_slow_change_mem
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane)
    (Tθ Tz : Field (PressureStream.Lift P))
    (hslowθ : ∀ n x, x ∈ (logStripData a b cL cR ha hcL hcR ε S hε hεone hS).domain →
      fderiv ℝ (inc.angular n) x o.vT = 0)
    (hslowz : ∀ n x, x ∈ (logStripData a b cL cR ha hcL hcR ε S hε hεone hS).domain →
      fderiv ℝ (inc.axial n) x o.vT = 0) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) (H + 1 - 2 * κ)
      (thetaResidual o base (updated mean inc) W Tθ - thetaResidual o base mean W Tθ) ∧
    MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) (H + 1 - 2 * κ)
      (axialResidual o base (updated mean inc) W
          (reconstructedPressure d a b hab M v o base (updated mean inc) W) Tz -
        axialResidual o base mean W (reconstructedPressure d a b hab M v o base mean W) Tz) := by
  obtain ⟨hθ, hz⟩ := tangential_recomputedPressure_change_mem ha hab hd hcL hcR ε S hε hεone hS
    ho hb hm hh hH hκ W hW hf hg hsf hsg M v Tθ Tz
  constructor
  · apply class_congr hθ
    intro n x hx
    simp only [Pi.sub_apply, Operators.fastTime, hslowθ n x hx, mul_zero, sub_zero]
  · apply class_congr hz
    intro n x hx
    simp only [Pi.sub_apply, Operators.fastTime, hslowz n x hx, mul_zero, sub_zero]

end ReconstructedTangential

end PressureReconstruction

section PhysicalIdentification

open ProblemStatement

/-- The physical-coordinate instance identifies the chart expressions above
with the already formalized equation (32). The slow time direction is `-∂t`
because the chart's slow time term has a minus sign. -/
noncomputable def physicalOperators : Operators SpaceTime where
  epsilon := fun _ => 1
  radialFrequency := fun _ => 0
  fastCoefficient := fun _ => 0
  radius := MeanResidual.radius
  radialProfile := fun _ => 0
  eR := (0, coordinateVector 0)
  eZ := (0, coordinateVector 2)
  eT := -(1, 0)
  vR := 0
  vT := 0

noncomputable def physicalField (f : MeanResidual.Scalar) : Field SpaceTime := fun _ => f

noncomputable def physicalTriple (b : MeanResidual.Components) : Triple SpaceTime :=
  ⟨physicalField (b 0), physicalField (b 1), physicalField (b 2)⟩

noncomputable def physicalCovariance (w : MeanResidual.Components) :
    Fin 3 → Fin 3 → Field SpaceTime := fun i j => physicalField (MeanResidual.covariance w i j)

theorem physical_dr (f : Field SpaceTime) :
    physicalOperators.dr f = fun n => MeanResidual.dr (f n) := by
  ext n q
  simp only [Operators.dr, graphDerivative, physicalOperators, zero_smul, add_zero,
    MeanResidual.dr, MeanResidual.direction]

theorem physical_dz (f : Field SpaceTime) :
    physicalOperators.dz f = fun n => MeanResidual.dz (f n) := by
  ext n q
  simp only [Operators.dz, physicalOperators, one_mul, MeanResidual.dz, MeanResidual.direction]

theorem physical_time (f : Field SpaceTime) :
    physicalOperators.time f = fun n => MeanResidual.dt (f n) := by
  ext n q
  simp only [Operators.time, Operators.slowTime, Operators.fastTime, physicalOperators,
    Pi.add_apply, zero_mul, add_zero, one_mul, map_neg, neg_neg,
    MeanResidual.dt, MeanResidual.direction]

theorem physical_radialDiv (c : ℝ) (f : Field SpaceTime) :
    physicalOperators.radialDiv c f = fun n => MeanResidual.radialDivergence c (f n) := by
  ext n q
  simp only [Operators.radialDiv, physical_dr]
  simp only [Operators.invRadius, physicalOperators,
    Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, MeanResidual.radialDivergence,
    div_eq_mul_inv]
  ring

theorem physical_viscosity (c : ℝ) (f : Field SpaceTime) (n : ℕ) (q : SpaceTime) :
    physicalOperators.viscosity c f n q =
      MeanResidual.meanLaplacian (f n) q - c * (f n q / MeanResidual.radius q ^ 2) := by
  simp only [Operators.viscosity, physical_dr, physical_dz]
  simp only [Operators.invRadius, physicalOperators, one_mul, MeanResidual.meanLaplacian,
    div_eq_mul_inv]
  ring

private theorem physical_thetaRadial (b m w : MeanResidual.Components) :
    thetaRadial (physicalTriple b) (physicalTriple m) + physicalCovariance w 0 1 =
      physicalField (MeanResidual.fluxDifference b m w 0 1) := by
  ext n q
  simp only [thetaRadial, physicalTriple, physicalField, physicalCovariance,
    MeanResidual.fluxDifference, Pi.add_apply, Pi.mul_apply]

private theorem physical_thetaAxial (b m w : MeanResidual.Components) :
    thetaAxial (physicalTriple b) (physicalTriple m) + physicalCovariance w 2 1 =
      physicalField (MeanResidual.fluxDifference b m w 2 1) := by
  ext n q
  simp only [thetaAxial, physicalTriple, physicalField, physicalCovariance,
    MeanResidual.fluxDifference, Pi.add_apply, Pi.mul_apply]
  ring

private theorem physical_axialRadial (b m w : MeanResidual.Components) :
    axialRadial (physicalTriple b) (physicalTriple m) + physicalCovariance w 0 2 =
      physicalField (MeanResidual.fluxDifference b m w 0 2) := by
  ext n q
  simp only [axialRadial, physicalTriple, physicalField, physicalCovariance,
    MeanResidual.fluxDifference, Pi.add_apply, Pi.mul_apply]

private theorem physical_axialAxial (b m w : MeanResidual.Components) :
    axialAxial (physicalTriple b) (physicalTriple m) + physicalCovariance w 2 2 =
      physicalField (MeanResidual.fluxDifference b m w 2 2) := by
  ext n q
  simp only [axialAxial, physicalTriple, physicalField, physicalCovariance,
    MeanResidual.fluxDifference, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem physical_radialRadial (b m w : MeanResidual.Components) :
    radialRadial (physicalTriple b) (physicalTriple m) + physicalCovariance w 0 0 =
      physicalField (MeanResidual.fluxDifference b m w 0 0) := by
  ext n q
  simp only [radialRadial, physicalTriple, physicalField, physicalCovariance,
    MeanResidual.fluxDifference, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem physical_radialAxial (b m w : MeanResidual.Components) :
    axialRadial (physicalTriple b) (physicalTriple m) + physicalCovariance w 2 0 =
      physicalField (MeanResidual.fluxDifference b m w 2 0) := by
  ext n q
  simp only [axialRadial, physicalTriple, physicalField, physicalCovariance,
    MeanResidual.fluxDifference, Pi.add_apply, Pi.mul_apply]
  ring

private theorem physical_radialAngular (b m w : MeanResidual.Components) :
    radialAngular (physicalTriple b) (physicalTriple m) + physicalCovariance w 1 1 =
      physicalField (MeanResidual.fluxDifference b m w 1 1) := by
  ext n q
  simp only [radialAngular, physicalTriple, physicalField, physicalCovariance,
    MeanResidual.fluxDifference, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem thetaResidual_eq_MeanResidual (b m w : MeanResidual.Components)
    (T : MeanResidual.Scalar) (n : ℕ) (q : SpaceTime) :
    thetaResidual physicalOperators (physicalTriple b) (physicalTriple m)
      (physicalCovariance w) (physicalField T) n q = MeanResidual.Etheta b m w T q := by
  unfold thetaResidual
  rw [physical_thetaRadial, physical_thetaAxial]
  simp only [
    Pi.sub_apply, Pi.add_apply, physical_time, physical_radialDiv, physical_dz,
    physical_viscosity, physicalTriple, physicalField, MeanResidual.Etheta, one_mul]
  ring

theorem axialResidual_eq_MeanResidual (b m w : MeanResidual.Components)
    (p T : MeanResidual.Scalar) (n : ℕ) (q : SpaceTime) :
    axialResidual physicalOperators (physicalTriple b) (physicalTriple m)
      (physicalCovariance w) (physicalField p) (physicalField T) n q =
        MeanResidual.Ez b m w p T q := by
  unfold axialResidual
  rw [physical_axialRadial, physical_axialAxial]
  simp only [
    Pi.sub_apply, Pi.add_apply, physical_time, physical_radialDiv, physical_dz,
    physical_viscosity, physicalTriple, physicalField, MeanResidual.Ez, zero_mul, sub_zero]
  rfl

theorem gr_eq_MeanResidual (b m w : MeanResidual.Components) (n : ℕ) (q : SpaceTime) :
    gr physicalOperators (physicalTriple b) (physicalTriple m) (physicalCovariance w) n q =
      MeanResidual.gr b m w q := by
  unfold gr
  rw [physical_radialRadial, physical_radialAxial, physical_radialAngular]
  simp only [
    Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
    physical_time, physical_radialDiv, physical_dz, physical_viscosity]
  simp only [Operators.invRadius, physicalOperators, physicalTriple, physicalField,
    MeanResidual.gr, div_eq_mul_inv, one_mul]
  ring

end PhysicalIdentification

end NavierStokes.MeanIncrementBounds
