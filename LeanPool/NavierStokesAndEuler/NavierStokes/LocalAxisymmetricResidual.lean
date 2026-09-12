/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisymmetricResidual
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Local Cartesian residual formulas for axisymmetric profiles

Only regularity at the evaluated profile point is required. The second
derivative formulas use equality of germs of first derivatives, so they do
not impose any condition on an unrelated profile point such as the axis.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.LocalAxisymmetricResidual

open ProblemStatement Filter
open AxisymmetricFields (Profile ProfilePoint profilePoint partialS partialZ radialEnergy
  projection hasFDerivAt_profile_composition profileDerivative_apply contDiff_profilePoint_slice)
open AxisymmetricResidual
open scoped BigOperators ContDiff Topology

theorem contDiffAt_direction {g : Space → ℝ} {x : Space} {m n : WithTop ℕ∞}
    (hg : ContDiffAt ℝ n g x) (hmn : m + 1 ≤ n) (i : Fin 3) :
    ContDiffAt ℝ m (fun y => direction g i y) x :=
  (hg.fderiv_right hmn).clm_apply contDiffAt_const

theorem direction_congr {a b : Space → ℝ} {x : Space}
    (h : a =ᶠ[𝓝 x] b) (i : Fin 3) : direction a i x = direction b i x := by
  unfold direction
  rw [h.fderiv_eq]

theorem direction_add {a b : Space → ℝ} {x : Space}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) (i : Fin 3) :
    direction (fun y => a y + b y) i x = direction a i x + direction b i x := by
  unfold direction
  rw [fderiv_fun_add ha hb]
  rfl

theorem direction_sub {a b : Space → ℝ} {x : Space}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) (i : Fin 3) :
    direction (fun y => a y - b y) i x = direction a i x - direction b i x := by
  unfold direction
  rw [fderiv_fun_sub ha hb]
  rfl

theorem scalarLaplacian_add {a b : Space → ℝ} {x : Space}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x) :
    scalarLaplacian (fun y => a y + b y) x = scalarLaplacian a x + scalarLaplacian b x := by
  unfold scalarLaplacian
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun y => direction (fun z => a z + b z) i y) =ᶠ[𝓝 x]
      (fun y => direction a i y + direction b i y) := by
    filter_upwards [ha.eventually (by norm_num), hb.eventually (by norm_num)] with y hay hby
    exact direction_add (hay.differentiableAt (by norm_num))
      (hby.differentiableAt (by norm_num)) i
  rw [direction_congr heq i]
  exact direction_add
    ((contDiffAt_direction ha (m := 1) (by norm_num) i).differentiableAt (by norm_num))
    ((contDiffAt_direction hb (m := 1) (by norm_num) i).differentiableAt (by norm_num)) i

theorem scalarLaplacian_sub {a b : Space → ℝ} {x : Space}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x) :
    scalarLaplacian (fun y => a y - b y) x = scalarLaplacian a x - scalarLaplacian b x := by
  unfold scalarLaplacian
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun y => direction (fun z => a z - b z) i y) =ᶠ[𝓝 x]
      (fun y => direction a i y - direction b i y) := by
    filter_upwards [ha.eventually (by norm_num), hb.eventually (by norm_num)] with y hay hby
    exact direction_sub (hay.differentiableAt (by norm_num))
      (hby.differentiableAt (by norm_num)) i
  rw [direction_congr heq i]
  exact direction_sub
    ((contDiffAt_direction ha (m := 1) (by norm_num) i).differentiableAt (by norm_num))
    ((contDiffAt_direction hb (m := 1) (by norm_num) i).differentiableAt (by norm_num)) i

theorem direction_coord_mul {g : Space → ℝ} {x : Space}
    (hg : DifferentiableAt ℝ g x) (i j : Fin 3) :
    direction (fun y => y i * g y) j x =
      (coordinateVector j) i * g x + x i * direction g j x := by
  unfold direction
  change (fderiv ℝ (fun y => projection i y * g y) x) (coordinateVector j) = _
  rw [fderiv_fun_mul (projection i).differentiableAt hg]
  simp only [AxisymmetricFields.projection_apply, ContinuousLinearMap.fderiv, add_apply, smul_apply,
    smul_eq_mul]
  ring

theorem second_direction_coord_mul {g : Space → ℝ} {x : Space}
    (hg : ContDiffAt ℝ 2 g x) (i j : Fin 3) :
    direction (fun y => direction (fun z => z i * g z) j y) j x =
      2 * (coordinateVector j) i * direction g j x +
        x i * direction (fun y => direction g j y) j x := by
  have hd := hg.differentiableAt (by norm_num)
  have hdg := (contDiffAt_direction hg (m := 1) (by norm_num) j).differentiableAt (by norm_num)
  have heq : (fun y => direction (fun z => z i * g z) j y) =ᶠ[𝓝 x]
      (fun y => (coordinateVector j) i * g y + y i * direction g j y) := by
    filter_upwards [hg.eventually (by norm_num)] with y hy
    exact direction_coord_mul (hy.differentiableAt (by norm_num)) i j
  rw [direction_congr heq j]
  change (fderiv ℝ (fun y => (coordinateVector j) i * g y +
    projection i y * direction g j y) x) (coordinateVector j) = _
  rw [fderiv_fun_add (hd.const_mul ((coordinateVector j) i))
    ((projection i).differentiableAt.fun_mul hdg)]
  rw [fderiv_const_mul hd, fderiv_fun_mul (projection i).differentiableAt hdg]
  simp only [AxisymmetricFields.projection_apply, direction, ContinuousLinearMap.fderiv, add_apply,
      smul_apply,
    smul_eq_mul]
  ring

theorem scalarLaplacian_coord_mul {g : Space → ℝ} {x : Space}
    (hg : ContDiffAt ℝ 2 g x) (i : Fin 3) :
    scalarLaplacian (fun y => y i * g y) x =
      x i * scalarLaplacian g x + 2 * direction g i x := by
  unfold scalarLaplacian
  simp_rw [second_direction_coord_mul hg]
  fin_cases i <;> simp only [coordinateVector, Fin.zero_eta, Fin.isValue, PiLp.single_apply,
      mul_ite, mul_one, mul_zero,
                    ite_mul, zero_mul, Fin.sum_univ_three, ↓reduceIte, zero_ne_one, zero_add,
                        Fin.reduceEq, Fin.mk_one, Fin.reduceFinMk, one_ne_zero] <;> ring

theorem vectorLaplacian_pack {a b c : Space → ℝ} {x : Space}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x) (hc : ContDiffAt ℝ 2 c x) :
    vectorLaplacian (fun y => pack (a y) (b y) (c y)) x =
      pack (scalarLaplacian a x) (scalarLaplacian b x) (scalarLaplacian c x) := by
  have hterm (i : Fin 3) :
      fderiv ℝ (fun y => fderiv ℝ (fun z => pack (a z) (b z) (c z)) y
        (coordinateVector i)) x (coordinateVector i) =
      pack (direction (fun y => direction a i y) i x)
        (direction (fun y => direction b i y) i x)
        (direction (fun y => direction c i y) i x) := by
    have heq : (fun y => fderiv ℝ (fun z => pack (a z) (b z) (c z)) y
        (coordinateVector i)) =ᶠ[𝓝 x]
        (fun y => pack (direction a i y) (direction b i y) (direction c i y)) := by
      filter_upwards [ha.eventually (by norm_num), hb.eventually (by norm_num),
        hc.eventually (by norm_num)] with y hay hby hcy
      exact fderiv_pack_apply (hay.differentiableAt (by norm_num))
        (hby.differentiableAt (by norm_num)) (hcy.differentiableAt (by norm_num))
        (coordinateVector i)
    rw [heq.fderiv_eq]
    exact fderiv_pack_apply
      ((contDiffAt_direction ha (m := 1) (by norm_num) i).differentiableAt (by norm_num))
      ((contDiffAt_direction hb (m := 1) (by norm_num) i).differentiableAt (by norm_num))
      ((contDiffAt_direction hc (m := 1) (by norm_num) i).differentiableAt (by norm_num))
      (coordinateVector i)
  unfold vectorLaplacian
  simp_rw [hterm]
  simp only [pack, direction, Finset.sum_add_distrib, ← Finset.sum_smul, scalarLaplacian]

theorem contDiffAt_lift {G : Profile} {t : ℝ} {x : Space} {n : WithTop ℕ∞}
    (hG : ContDiffAt ℝ n G (profilePoint t x)) : ContDiffAt ℝ n (lift G t) x :=
  hG.comp x (contDiff_profilePoint_slice t).contDiffAt

theorem fderiv_lift_apply {G : Profile} {t : ℝ} {x : Space}
    (hG : DifferentiableAt ℝ G (profilePoint t x)) (v : Space) :
    fderiv ℝ (lift G t) x v =
      (x 0 * v 0 + x 1 * v 1) * partialS G (profilePoint t x) +
        v 2 * partialZ G (profilePoint t x) := by
  change (fderiv ℝ (fun y => G (profilePoint t y)) x) v = _
  rw [(hasFDerivAt_profile_composition G t x hG).fderiv]
  exact profileDerivative_apply G t x v

theorem direction_lift_zero {G : Profile} {t : ℝ} {x : Space}
    (hG : DifferentiableAt ℝ G (profilePoint t x)) :
    direction (lift G t) 0 x = x 0 * lift (partialS G) t x := by
  unfold direction
  rw [fderiv_lift_apply hG]
  simp only [Fin.isValue, coordinateVector, PiLp.single_eq_same, mul_one, ne_eq, one_ne_zero,
      not_false_eq_true,
    PiLp.single_eq_of_ne, mul_zero, add_zero, Fin.reduceEq, zero_mul, lift]

theorem direction_lift_one {G : Profile} {t : ℝ} {x : Space}
    (hG : DifferentiableAt ℝ G (profilePoint t x)) :
    direction (lift G t) 1 x = x 1 * lift (partialS G) t x := by
  unfold direction
  rw [fderiv_lift_apply hG]
  simp only [Fin.isValue, coordinateVector, ne_eq, zero_ne_one, not_false_eq_true,
      PiLp.single_eq_of_ne,
    mul_zero, PiLp.single_eq_same, mul_one, zero_add, Fin.reduceEq, zero_mul, add_zero, lift]

theorem direction_lift_two {G : Profile} {t : ℝ} {x : Space}
    (hG : DifferentiableAt ℝ G (profilePoint t x)) :
    direction (lift G t) 2 x = lift (partialZ G) t x := by
  unfold direction
  rw [fderiv_lift_apply hG]
  simp only [Fin.isValue, coordinateVector, ne_eq, Fin.reduceEq, not_false_eq_true,
      PiLp.single_eq_of_ne,
    mul_zero, add_zero, zero_mul, PiLp.single_eq_same, one_mul, zero_add, lift]

theorem scalarLaplacian_lift {G : Profile} {t : ℝ} {x : Space}
    (hG : ContDiffAt ℝ 2 G (profilePoint t x)) :
    scalarLaplacian (lift G t) x = laplaceScalar G (profilePoint t x) := by
  have hs : DifferentiableAt ℝ (partialS G) (profilePoint t x) :=
    (((hG.fderiv_right (m := 1) (by
        norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num))
  have hz : DifferentiableAt ℝ (partialZ G) (profilePoint t x) :=
    (((hG.fderiv_right (m := 1) (by
        norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num))
  have hls : DifferentiableAt ℝ (lift (partialS G) t) x :=
    (hasFDerivAt_profile_composition (partialS G) t x hs).differentiableAt
  have hnear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 G (profilePoint t y) :=
    (contDiff_profilePoint_slice t (n := 0)).continuous.continuousAt
      (hG.eventually (by norm_num))
  have he0 : (fun y => direction (lift G t) 0 y) =ᶠ[𝓝 x]
      (fun y => y 0 * lift (partialS G) t y) := by
    filter_upwards [hnear] with y hy
    exact direction_lift_zero (hy.differentiableAt (by norm_num))
  have he1 : (fun y => direction (lift G t) 1 y) =ᶠ[𝓝 x]
      (fun y => y 1 * lift (partialS G) t y) := by
    filter_upwards [hnear] with y hy
    exact direction_lift_one (hy.differentiableAt (by norm_num))
  have he2 : (fun y => direction (lift G t) 2 y) =ᶠ[𝓝 x] lift (partialZ G) t := by
    filter_upwards [hnear] with y hy
    exact direction_lift_two (hy.differentiableAt (by norm_num))
  unfold scalarLaplacian
  rw [Fin.sum_univ_three, direction_congr he0 0, direction_congr he1 1, direction_congr he2 2]
  rw [direction_coord_mul hls, direction_coord_mul hls]
  rw [direction_lift_zero hs, direction_lift_one hs, direction_lift_two hz]
  simp only [Fin.isValue, coordinateVector, PiLp.single_eq_same, lift, profilePoint, radialEnergy,
      one_mul,
    laplaceScalar, add_left_inj]
  ring

theorem scalarLaplacian_weighted_zero {G : Profile} {t : ℝ} {x : Space}
    (hG : ContDiffAt ℝ 2 G (profilePoint t x)) :
    scalarLaplacian (fun y => y 0 * lift G t y) x =
      x 0 * laplaceWeighted G (profilePoint t x) := by
  rw [scalarLaplacian_coord_mul (contDiffAt_lift hG), scalarLaplacian_lift hG,
    direction_lift_zero (hG.differentiableAt (by norm_num))]
  unfold lift laplaceScalar laplaceWeighted
  ring

theorem scalarLaplacian_weighted_one {G : Profile} {t : ℝ} {x : Space}
    (hG : ContDiffAt ℝ 2 G (profilePoint t x)) :
    scalarLaplacian (fun y => y 1 * lift G t y) x =
      x 1 * laplaceWeighted G (profilePoint t x) := by
  rw [scalarLaplacian_coord_mul (contDiffAt_lift hG), scalarLaplacian_lift hG,
    direction_lift_one (hG.differentiableAt (by norm_num))]
  unfold lift laplaceScalar laplaceWeighted
  ring

/-- The spatial Jacobian uses derivatives only at the evaluated profile point. -/
theorem hasFDerivAt_velocity {B F U : Profile} {t : ℝ} {x : Space}
    (hB : DifferentiableAt ℝ B (profilePoint t x))
    (hF : DifferentiableAt ℝ F (profilePoint t x))
    (hU : DifferentiableAt ℝ U (profilePoint t x)) :
    HasFDerivAt (fun y => velocity B F U (t, y)) (velocityJacobian B F U t x) x := by
  have hb := hasFDerivAt_profile_composition B t x hB
  have hf := hasFDerivAt_profile_composition F t x hF
  have hu := hasFDerivAt_profile_composition U t x hU
  exact hasFDerivAt_pack
    ((((projection 0).hasFDerivAt.mul hb).add ((projection 1).hasFDerivAt.mul hf)).neg)
    (((projection 0).hasFDerivAt.mul hf).sub ((projection 1).hasFDerivAt.mul hb)) hu

theorem advection_velocity {B F U : Profile} {t : ℝ} {x : Space}
    (hB : DifferentiableAt ℝ B (profilePoint t x))
    (hF : DifferentiableAt ℝ F (profilePoint t x))
    (hU : DifferentiableAt ℝ U (profilePoint t x)) :
    advection (velocity B F U) t x =
      pack (x 0 * advectionRadial B F U (profilePoint t x) +
        x 1 * advectionAngular B F U (profilePoint t x))
      (x 1 * advectionRadial B F U (profilePoint t x) -
        x 0 * advectionAngular B F U (profilePoint t x))
      (advectionAxial B U (profilePoint t x)) := by
  change (fderiv ℝ (fun y => velocity B F U (t, y)) x) (velocity B F U (t, x)) = _
  rw [(hasFDerivAt_velocity hB hF hU).fderiv]
  simp only [velocityJacobian, packDerivative_apply]
  ext i
  fin_cases i <;> simp only [pack, Fin.isValue, lift, profilePoint, radialEnergy, neg_add_rev,
      velocity, componentX,
                    coordinateVector, componentY, add_apply, neg_apply, smul_apply,
                        AxisymmetricFields.projection_apply, PiLp.add_apply,
                    PiLp.smul_apply, ne_eq, one_ne_zero, not_false_eq_true, PiLp.single_eq_of_ne,
                        smul_eq_mul, mul_zero,
                    PiLp.single_eq_same, mul_one, zero_add, Fin.reduceEq, add_zero,
                        profileDerivative_apply, zero_ne_one, sub_apply,
                    Fin.zero_eta, advectionRadial, advectionAngular, advectionAxial, neg_mul] <;>
                        ring

theorem divergence_velocity {B F U : Profile} {t : ℝ} {x : Space}
    (hB : DifferentiableAt ℝ B (profilePoint t x))
    (hF : DifferentiableAt ℝ F (profilePoint t x))
    (hU : DifferentiableAt ℝ U (profilePoint t x)) :
    spatialDivergence (velocity B F U) t x =
      partialZ U (profilePoint t x) - 2 * B (profilePoint t x) -
        2 * radialEnergy x * partialS B (profilePoint t x) := by
  unfold spatialDivergence spatialDerivative
  rw [(hasFDerivAt_velocity hB hF hU).fderiv, Fin.sum_univ_three]
  simp only [velocityJacobian, Fin.isValue, lift, profilePoint, radialEnergy, neg_add_rev,
      coordinateVector,
    packDerivative_apply, add_apply, neg_apply, smul_apply, AxisymmetricFields.projection_apply,
        ne_eq, one_ne_zero,
    not_false_eq_true, PiLp.single_eq_of_ne, smul_eq_mul, mul_zero, neg_zero,
        profileDerivative_apply,
    PiLp.single_eq_same, mul_one, add_zero, Fin.reduceEq, zero_mul, zero_add, sub_apply, pack_zero,
        zero_ne_one,
    pack_one, one_mul, pack_two]
  ring

/-- The physical vector Laplacian is local in all three profiles. In
particular this applies to a radial quotient at any point where it is C². -/
theorem spatialLaplacian_velocity {B F U : Profile} {t : ℝ} {x : Space}
    (hB : ContDiffAt ℝ 2 B (profilePoint t x))
    (hF : ContDiffAt ℝ 2 F (profilePoint t x))
    (hU : ContDiffAt ℝ 2 U (profilePoint t x)) :
    spatialLaplacian (velocity B F U) t x =
      pack (-x 0 * laplaceWeighted B (profilePoint t x) -
        x 1 * laplaceWeighted F (profilePoint t x))
      (-x 1 * laplaceWeighted B (profilePoint t x) +
        x 0 * laplaceWeighted F (profilePoint t x))
      (laplaceScalar U (profilePoint t x)) := by
  have hb := contDiffAt_lift hB
  have hf := contDiffAt_lift hF
  have hu := contDiffAt_lift hU
  have h0b : ContDiffAt ℝ 2 (fun y : Space => y 0 * lift B t y) x :=
    (projection 0).contDiff.contDiffAt.mul hb
  have h1b : ContDiffAt ℝ 2 (fun y : Space => y 1 * lift B t y) x :=
    (projection 1).contDiff.contDiffAt.mul hb
  have h0f : ContDiffAt ℝ 2 (fun y : Space => y 0 * lift F t y) x :=
    (projection 0).contDiff.contDiffAt.mul hf
  have h1f : ContDiffAt ℝ 2 (fun y : Space => y 1 * lift F t y) x :=
    (projection 1).contDiff.contDiffAt.mul hf
  have hx : ContDiffAt ℝ 2 (componentX B F t) x := (h0b.add h1f).neg
  have hy : ContDiffAt ℝ 2 (componentY B F t) x := h0f.sub h1b
  change vectorLaplacian (fun y => pack (componentX B F t y) (componentY B F t y)
    (lift U t y)) x = _
  rw [vectorLaplacian_pack hx hy hu]
  unfold componentX componentY
  rw [scalarLaplacian_neg, scalarLaplacian_add h0b h1f, scalarLaplacian_sub h0f h1b]
  rw [scalarLaplacian_weighted_zero hB, scalarLaplacian_weighted_one hF,
    scalarLaplacian_weighted_zero hF, scalarLaplacian_weighted_one hB, scalarLaplacian_lift hU]
  ext i
  fin_cases i <;> simp only [pack, Fin.isValue, neg_add_rev, coordinateVector, Fin.zero_eta,
      PiLp.add_apply, PiLp.smul_apply,
                    PiLp.single_eq_same, smul_eq_mul, mul_one, ne_eq, zero_ne_one,
                        not_false_eq_true, PiLp.single_eq_of_ne, mul_zero,
                    add_zero, Fin.reduceEq, neg_mul] <;> ring

theorem pressureGradient_pressure {P : Profile} {t : ℝ} {x : Space}
    (hP : DifferentiableAt ℝ P (profilePoint t x)) :
    pressureGradient (pressure P) t x =
      pack (x 0 * partialS P (profilePoint t x)) (x 1 * partialS P (profilePoint t x))
        (partialZ P (profilePoint t x)) := by
  change (∑ i : Fin 3, fderiv ℝ (lift P t) x (coordinateVector i) • coordinateVector i) = _
  simp_rw [fderiv_lift_apply hP]
  rw [Fin.sum_univ_three]
  simp only [Fin.isValue, coordinateVector, PiLp.single_eq_same, mul_one, ne_eq, one_ne_zero,
      not_false_eq_true,
    PiLp.single_eq_of_ne, mul_zero, add_zero, Fin.reduceEq, zero_mul, zero_ne_one, zero_add,
        one_mul, pack]

/-- Joint profile differentiability provides the time derivative at the
point, with no hypothesis about any other point of the spatial slice. -/
theorem hasFDerivAt_time_lift {G : Profile} {t : ℝ} {x : Space}
    (hG : DifferentiableAt ℝ G (profilePoint t x)) :
    HasFDerivAt (fun s => lift G s x) (timeProfileDerivative G (profilePoint t x)) t := by
  have hp : HasFDerivAt (fun s => profilePoint s x) timeProfileJacobian t :=
    (hasFDerivAt_id t).prodMk (hasFDerivAt_const (radialEnergy x, x 2) t)
  exact hG.hasFDerivAt.comp t hp

theorem temporalDerivative_velocity {B F U : Profile} {t : ℝ} {x : Space}
    (hB : DifferentiableAt ℝ B (profilePoint t x))
    (hF : DifferentiableAt ℝ F (profilePoint t x))
    (hU : DifferentiableAt ℝ U (profilePoint t x)) :
    temporalDerivative (velocity B F U) t x =
      pack (-x 0 * partialT B (profilePoint t x) - x 1 * partialT F (profilePoint t x))
        (-x 1 * partialT B (profilePoint t x) + x 0 * partialT F (profilePoint t x))
        (partialT U (profilePoint t x)) := by
  have hb := hasFDerivAt_time_lift hB
  have hf := hasFDerivAt_time_lift hF
  have hu := hasFDerivAt_time_lift hU
  have hv := hasFDerivAt_pack (((hb.const_mul (x 0)).fun_add (hf.const_mul (x 1))).fun_neg)
    ((hf.const_mul (x 0)).fun_sub (hb.const_mul (x 1))) hu
  change (fderiv ℝ (fun s => pack (-(x 0 * lift B s x + x 1 * lift F s x))
    (x 0 * lift F s x - x 1 * lift B s x) (lift U s x)) t) 1 = _
  rw [hv.fderiv]
  simp only [Fin.isValue, neg_add_rev, packDerivative_apply, add_apply, neg_apply, smul_apply,
    timeProfileDerivative_one, smul_eq_mul, sub_apply, neg_mul]
  ext i
  fin_cases i <;> simp only [pack, Fin.isValue, coordinateVector, Fin.zero_eta, PiLp.add_apply,
      PiLp.smul_apply,
                    PiLp.single_eq_same, smul_eq_mul, mul_one, ne_eq, zero_ne_one,
                        not_false_eq_true, PiLp.single_eq_of_ne, mul_zero,
                    add_zero, Fin.reduceEq] <;> ring

/-- The exact physical residual at viscosity one, from regularity only at
the evaluated joint profile point. No `SliceC2` or `SliceDifferentiable`
hypothesis occurs. This does not assert that a radial quotient is smooth
at a point where its denominator vanishes. -/
theorem navierStokesResidual_velocity {B F U P : Profile} {t : ℝ} {x : Space}
    (hB : ContDiffAt ℝ 2 B (profilePoint t x))
    (hF : ContDiffAt ℝ 2 F (profilePoint t x))
    (hU : ContDiffAt ℝ 2 U (profilePoint t x))
    (hP : DifferentiableAt ℝ P (profilePoint t x)) :
    navierStokesResidual (velocity B F U) (pressure P) t x =
      pack (x 0 * residualRadial B F U P (profilePoint t x) +
        x 1 * residualAngular B F U (profilePoint t x))
      (x 1 * residualRadial B F U P (profilePoint t x) -
        x 0 * residualAngular B F U (profilePoint t x))
      (residualAxial B U P (profilePoint t x)) := by
  have hb := hB.differentiableAt (by norm_num)
  have hf := hF.differentiableAt (by norm_num)
  have hu := hU.differentiableAt (by norm_num)
  unfold navierStokesResidual
  rw [temporalDerivative_velocity hb hf hu, advection_velocity hb hf hu,
    spatialLaplacian_velocity hB hF hU, pressureGradient_pressure hP]
  ext i
  fin_cases i <;> simp only [pack, Fin.isValue, neg_mul, coordinateVector, Fin.zero_eta,
      PiLp.add_apply, PiLp.sub_apply,
                    PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul, mul_one, ne_eq, zero_ne_one,
                        not_false_eq_true,
                    PiLp.single_eq_of_ne, mul_zero, add_zero, Fin.reduceEq, residualRadial,
                        residualAngular, residualAxial] <;> ring

/-- The three local coefficient equations imply the actual Cartesian PDE. -/
theorem navierStokesResidual_eq_zero {B F U P : Profile} {t : ℝ} {x : Space}
    (hB : ContDiffAt ℝ 2 B (profilePoint t x))
    (hF : ContDiffAt ℝ 2 F (profilePoint t x))
    (hU : ContDiffAt ℝ 2 U (profilePoint t x))
    (hP : DifferentiableAt ℝ P (profilePoint t x))
    (hr : residualRadial B F U P (profilePoint t x) = 0)
    (ha : residualAngular B F U (profilePoint t x) = 0)
    (hz : residualAxial B U P (profilePoint t x) = 0) :
    navierStokesResidual (velocity B F U) (pressure P) t x = 0 := by
  rw [navierStokesResidual_velocity hB hF hU hP]
  simp only [pack, Fin.isValue, hr, mul_zero, ha, add_zero, zero_smul, sub_self, hz]

end NavierStokes.LocalAxisymmetricResidual
