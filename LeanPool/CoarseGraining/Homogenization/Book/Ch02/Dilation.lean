/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.NormScaling
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.HomogenizationError
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1Dilation

/-! # Dilation -/

@[expose] public section

open scoped Pointwise

namespace Homogenization
namespace Book
namespace Ch02

/-!
# Public dilation package after the Chapter 2.5 definitions

This file freezes the note-facing dilation vocabulary used by later Chapter 3
arguments.  The statements are deliberately phrased with the public `CoeffOn`
and `TriadicCoeffFamily` interfaces: coefficient representatives are compared
only almost everywhere on the dilated cube.

The geometric convention is that dilation by `3^k` sends a triadic cube
`Q = 3^m (z + [-1/2,1/2]^d)` to the cube with the same integer index and scale
`m + k`.
-/

noncomputable section

/-- The positive dilation factor `3^k`. -/
def triadicDilationFactor (k : ℤ) : ℝ :=
  (3 : ℝ) ^ k

theorem triadicDilationFactor_pos (k : ℤ) :
    0 < triadicDilationFactor k := by
  simpa [triadicDilationFactor] using
    (zpow_pos (show (0 : ℝ) < 3 by norm_num) k)

theorem triadicDilationFactor_ne_zero (k : ℤ) :
    triadicDilationFactor k ≠ 0 :=
  (triadicDilationFactor_pos k).ne'

/-- Dilation of a vector by `3^k`. -/
def dilateVec {d : ℕ} (k : ℤ) (x : Vec d) : Vec d :=
  triadicDilationFactor k • x

/-- Pullback map associated with dilation by `3^k`. -/
def undilateVec {d : ℕ} (k : ℤ) (x : Vec d) : Vec d :=
  (triadicDilationFactor k)⁻¹ • x

/-- Representative-level pullback of a coefficient field under dilation by
`3^k`.  Public coefficient objects use `CoeffOn.IsCubeDilation` below, which
records this relation only a.e. on the target cube. -/
def dilateCoeffField {d : ℕ} (k : ℤ) (a : CoeffField d) : CoeffField d :=
  fun x => a (undilateVec k x)

@[simp] theorem dilateCoeffField_apply {d : ℕ} (k : ℤ) (a : CoeffField d)
    (x : Vec d) :
    dilateCoeffField k a x = a (undilateVec k x) :=
  rfl

/-- Dilation of a triadic cube by `3^k`: the scale is shifted by `k`, while the
integer index is unchanged. -/
def dilateCube {d : ℕ} (k : ℤ) (Q : TriadicCube d) : TriadicCube d :=
  { scale := Q.scale + k
    index := Q.index }

@[simp] theorem dilateCube_scale {d : ℕ} (k : ℤ) (Q : TriadicCube d) :
    (dilateCube k Q).scale = Q.scale + k :=
  rfl

@[simp] theorem dilateCube_index {d : ℕ} (k : ℤ) (Q : TriadicCube d) :
    (dilateCube k Q).index = Q.index :=
  rfl

theorem cubeScaleFactor_dilateCube {d : ℕ} (k : ℤ) (Q : TriadicCube d) :
    cubeScaleFactor (dilateCube k Q) =
      triadicDilationFactor k * cubeScaleFactor Q := by
  simp only [cubeScaleFactor, dilateCube, triadicDilationFactor]
  rw [zpow_add₀ (show (3 : ℝ) ≠ 0 by norm_num)]
  ring_nf

theorem openCubeSet_dilateCube {d : ℕ} (k : ℤ) (Q : TriadicCube d) :
    openCubeSet (dilateCube k Q) =
      triadicDilationFactor k • openCubeSet Q := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_smul_set]
    refine ⟨undilateVec k x, ?_, ?_⟩
    · intro i
      have hxi := hx i
      have hs_pos := triadicDilationFactor_pos k
      have hscale := cubeScaleFactor_dilateCube k Q
      constructor
      · have hlo_mul :
            (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) *
                triadicDilationFactor k < x i := by
          simpa [hscale, mul_assoc, mul_left_comm, mul_comm] using hxi.1
        have hlo_div :
            (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) <
              x i / triadicDilationFactor k :=
          (lt_div_iff₀ hs_pos).2 hlo_mul
        simpa [undilateVec, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv,
          mul_comm] using hlo_div
      · have hhi_mul :
            x i < (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) *
                triadicDilationFactor k := by
          simpa [hscale, mul_assoc, mul_left_comm, mul_comm] using hxi.2
        have hhi_div :
            x i / triadicDilationFactor k <
              (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) :=
          (div_lt_iff₀ hs_pos).2 hhi_mul
        simpa [undilateVec, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv,
          mul_comm] using hhi_div
    · ext i
      simp [undilateVec, triadicDilationFactor_ne_zero k]
  · rintro ⟨y, hy, rfl⟩
    intro i
    have hyi := hy i
    have hs_pos := triadicDilationFactor_pos k
    have hscale := cubeScaleFactor_dilateCube k Q
    constructor
    · have h := mul_lt_mul_of_pos_left hyi.1 hs_pos
      simpa [Pi.smul_apply, smul_eq_mul, hscale, mul_assoc, mul_left_comm,
        mul_comm] using h
    · have h := mul_lt_mul_of_pos_left hyi.2 hs_pos
      simpa [Pi.smul_apply, smul_eq_mul, hscale, mul_assoc, mul_left_comm,
        mul_comm] using h

theorem IsSolenoidalOn.dilateSet {d : ℕ} {U V : Set (Vec d)} {r : ℝ}
    (hr : 0 < r) (hV : V = r • U) {g : Vec d → Vec d}
    (hg : IsSolenoidalOn U g) :
    IsSolenoidalOn V (fun x => g (r⁻¹ • x)) := by
  subst V
  intro φ
  let ψ : H10Function U := φ.unscale hr
  have htest := hg ψ
  have hscaled :
      r * ∫ y in U,
          vecDot (g y) (φ.toH1Function.grad (r • y)) ∂MeasureTheory.volume = 0 := by
    have hfun :
        (fun y : Vec d =>
            vecDot (g y) (ψ.toH1Function.grad y)) =
          fun y => r * vecDot (g y) (φ.toH1Function.grad (r • y)) := by
      funext y
      simp [ψ, vecDot_smul_right]
    simpa [hfun, MeasureTheory.integral_const_mul] using htest
  have hbase :
      ∫ y in U, vecDot (g y) (φ.toH1Function.grad (r • y))
        ∂MeasureTheory.volume = 0 := by
    exact (mul_eq_zero.mp hscaled).resolve_left hr.ne'
  have hchange :
      ∫ y in U, vecDot (g y) (φ.toH1Function.grad (r • y))
          ∂MeasureTheory.volume =
        (r ^ d)⁻¹ * ∫ x in r • U,
          vecDot (g (r⁻¹ • x)) (φ.toH1Function.grad x)
            ∂MeasureTheory.volume := by
    simpa [smul_smul, hr.ne'] using
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume)
        (f := fun x : Vec d =>
          vecDot (g (r⁻¹ • x)) (φ.toH1Function.grad x))
        (s := U) hr)
  calc
    ∫ x in r • U, vecDot (g (r⁻¹ • x)) (φ.toH1Function.grad x)
        ∂MeasureTheory.volume
        = (r ^ d) * ∫ y in U,
            vecDot (g y) (φ.toH1Function.grad (r • y))
              ∂MeasureTheory.volume := by
          have hpos : (r ^ d) ≠ 0 := (pow_pos hr d).ne'
          rw [hchange]
          field_simp [hpos]
    _ = 0 := by
          rw [hbase]
          simp

theorem IsSolenoidalOn.congr_ae {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hfg : f =ᵐ[volumeMeasureOn U] g)
    (hf : IsSolenoidalOn U f) :
    IsSolenoidalOn U g := by
  intro φ
  calc
    ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume
        = ∫ x in U, vecDot (f x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae ?_
          exact hfg.symm.mono fun x hx => by
            simp [hx]
    _ = 0 := hf φ

theorem IsSolenoidalOn.undilateSet {d : ℕ} {U V : Set (Vec d)} {r : ℝ}
    (hr : 0 < r) (hV : V = r • U) {g : Vec d → Vec d}
    (hg : IsSolenoidalOn V g) :
    IsSolenoidalOn U (fun x => g (r • x)) := by
  have hU : U = r⁻¹ • V := by
    rw [hV]
    ext x
    simp [hr.ne']
  have h := IsSolenoidalOn.dilateSet (inv_pos.mpr hr) hU hg
  simpa using h

namespace CoeffOn

/-- Public a.e. relation saying that `b` is the dilation by `3^k` of a
coefficient field `a` from `Q` to `3^k Q`.

The lower/upper ellipticity constants are required to be the same named
constants, and the representatives agree a.e. with the pullback
`a(3^{-k} ·)` on the target cube. -/
def IsCubeDilation {d : ℕ} (k : ℤ) {Q : TriadicCube d}
    (a : CoeffOn (cubeDomain Q))
    (b : CoeffOn (cubeDomain (dilateCube k Q))) : Prop :=
  b.lam = a.lam ∧
    b.Lam = a.Lam ∧
      b.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet (dilateCube k Q))]
        dilateCoeffField k a.toCoeffField

namespace IsCubeDilation

theorem lam_eq {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (h : IsCubeDilation k a b) :
    b.lam = a.lam :=
  h.1

theorem Lam_eq {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (h : IsCubeDilation k a b) :
    b.Lam = a.Lam :=
  h.2.1

theorem coeff_ae_eq {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (h : IsCubeDilation k a b) :
    b.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet (dilateCube k Q))]
      dilateCoeffField k a.toCoeffField :=
  h.2.2

theorem transpose {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (h : IsCubeDilation k a b) :
    IsCubeDilation k a.transpose b.transpose := by
  refine ⟨h.lam_eq, h.Lam_eq, ?_⟩
  exact h.coeff_ae_eq.mono fun x hx => by
    ext i j
    simp [dilateCoeffField, hx, matTranspose]

end IsCubeDilation
end CoeffOn

namespace TriadicCoeffFamily

/-- A triadic coefficient family `b` is the dilation by `3^k` of `a` if, on
every original cube `Q`, the coefficient object on the dilated cube `3^k Q`
is the public a.e. dilation of the coefficient object on `Q`. -/
def IsDilation {d : ℕ} (k : ℤ) (a b : TriadicCoeffFamily d) : Prop :=
  ∀ Q : TriadicCube d,
    CoeffOn.IsCubeDilation k (a.coeffOn Q) (b.coeffOn (dilateCube k Q))

end TriadicCoeffFamily

namespace Solution

/-- Data expressing that `v` is the dilation of a Chapter 2 solution `u` from
`Q` to `3^k Q`.

The function is scaled by `3^k`, so its gradient and flux pull back without an
extra scalar.  This is the normalization under which response quantities and
coarse matrices are scale invariant. -/
structure IsCubeDilation {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b)
    (u : Solution (cubeDomain Q) a)
    (v : Solution (cubeDomain (dilateCube k Q)) b) : Prop where
  value_ae_eq :
    v.toH1.toFun =ᵐ[volumeMeasureOn (openCubeSet (dilateCube k Q))]
      fun x => triadicDilationFactor k * u.toH1.toFun (undilateVec k x)
  grad_ae_eq :
    v.toH1.grad =ᵐ[volumeMeasureOn (openCubeSet (dilateCube k Q))]
      fun x => u.toH1.grad (undilateVec k x)
  flux_ae_eq :
    (fun x => matVecMul (b.toCoeffField x) (v.toH1.grad x))
      =ᵐ[volumeMeasureOn (openCubeSet (dilateCube k Q))]
      fun x =>
        matVecMul (a.toCoeffField (undilateVec k x))
          (u.toH1.grad (undilateVec k x))

/-- A packaged dilated solution.  The `toSolution` field is the public lemma's
conclusion: it is an actual solution of the dilated equation. -/
structure CubeDilation {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b)
    (u : Solution (cubeDomain Q) a) where
  toSolution : Solution (cubeDomain (dilateCube k Q)) b
  isDilation : IsCubeDilation hCoeff u toSolution

/-- Dilation of a public Chapter 2 solution.  The function is normalized as
`v(x) = 3^k u(3^{-k}x)`, so its weak gradient and flux are plain pullbacks. -/
noncomputable def dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b)
    (u : Solution (cubeDomain Q) a) : CubeDilation hCoeff u := by
  let s : ℝ := triadicDilationFactor k
  have hs : 0 < s := triadicDilationFactor_pos k
  have hset :
      ((cubeDomain (dilateCube k Q) : Domain d) : Set (Vec d)) =
        s • ((cubeDomain Q : Domain d) : Set (Vec d)) := by
    simpa [s, cubeDomain_coe] using openCubeSet_dilateCube k Q
  let vH1 : H1Function ((cubeDomain (dilateCube k Q) : Domain d) : Set (Vec d)) :=
    u.toH1.dilateSet hs hset
  let sourceFlux : Vec d → Vec d :=
    fun y => matVecMul (a.toCoeffField y) (u.toH1.grad y)
  let v : Solution (cubeDomain (dilateCube k Q)) b :=
    { toH1 := vH1
      isHarmonic := by
        refine ⟨vH1.isPotentialOn, ?_⟩
        have hsolPull :
            IsSolenoidalOn ((cubeDomain (dilateCube k Q) : Domain d) : Set (Vec d))
              (fun x => sourceFlux (s⁻¹ • x)) := by
          simpa [sourceFlux, s, undilateVec] using
            IsSolenoidalOn.dilateSet hs hset u.isHarmonic.2
        refine IsSolenoidalOn.congr_ae ?_ hsolPull
        exact hCoeff.coeff_ae_eq.mono fun x hx => by
          simp only [sourceFlux, vH1, s, undilateVec, dilateCoeffField, hx]
          rfl }
  exact
    { toSolution := v
      isDilation :=
        { value_ae_eq := Filter.Eventually.of_forall fun x => by
            simp only [v, vH1, s, undilateVec]
            rfl
          grad_ae_eq := Filter.Eventually.of_forall fun x => by
            simp only [v, vH1, s, undilateVec]
            rfl
          flux_ae_eq := hCoeff.coeff_ae_eq.mono fun x hx => by
            simp only [v, vH1, s, undilateVec, dilateCoeffField, hx]
            rfl } }

/-- Inverse transport for a dilated public solution.  This is used to show
that dilation identifies the whole response value set, not just one chosen
solution. -/
noncomputable def undilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b)
    (v : Solution (cubeDomain (dilateCube k Q)) b) :
    Solution (cubeDomain Q) a := by
  let s : ℝ := triadicDilationFactor k
  have hs : 0 < s := triadicDilationFactor_pos k
  have hset :
      ((cubeDomain (dilateCube k Q) : Domain d) : Set (Vec d)) =
        s • ((cubeDomain Q : Domain d) : Set (Vec d)) := by
    simpa [s, cubeDomain_coe] using openCubeSet_dilateCube k Q
  let wH1 : H1Function ((cubeDomain Q : Domain d) : Set (Vec d)) :=
    v.toH1.undilateSet hs hset
  exact
    { toH1 := wH1
      isHarmonic := by
        refine ⟨wH1.isPotentialOn, ?_⟩
        have htarget :
            IsSolenoidalOn
              ((cubeDomain (dilateCube k Q) : Domain d) : Set (Vec d))
              (fun x =>
                matVecMul (dilateCoeffField k a.toCoeffField x) (v.toH1.grad x)) := by
          refine IsSolenoidalOn.congr_ae
            (f := fun x => matVecMul (b.toCoeffField x) (v.toH1.grad x)) ?_ ?_
          · exact hCoeff.coeff_ae_eq.mono fun x hx => by
              simp [hx]
          exact v.isHarmonic.2
        have hpull :
            IsSolenoidalOn ((cubeDomain Q : Domain d) : Set (Vec d))
              (fun y =>
                matVecMul (dilateCoeffField k a.toCoeffField (s • y))
                  (v.toH1.grad (s • y))) :=
          IsSolenoidalOn.undilateSet hs hset htarget
        have hfun :
            (fun x : Vec d => matVecMul (a.toCoeffField x) (wH1.grad x)) =
              fun y =>
                matVecMul (dilateCoeffField k a.toCoeffField (s • y))
                  (v.toH1.grad (s • y)) := by
          funext y
          have hcoeff : a.toCoeffField y = dilateCoeffField k a.toCoeffField (s • y) := by
            simp only [dilateCoeffField, undilateVec, s, smul_smul,
              inv_mul_cancel₀ (triadicDilationFactor_ne_zero k), one_smul]
          have hgrad : wH1.grad y = v.toH1.grad (s • y) := by
            simp only [wH1]
            exact H1Function.undilateSet_grad hs hset v.toH1 y
          rw [hcoeff, hgrad]
        rw [hfun]
        exact hpull }

theorem undilate_isDilation {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b)
    (v : Solution (cubeDomain (dilateCube k Q)) b) :
    IsCubeDilation hCoeff (undilate hCoeff v) v := by
  let s : ℝ := triadicDilationFactor k
  have hs : 0 < s := triadicDilationFactor_pos k
  have hset :
      ((cubeDomain (dilateCube k Q) : Domain d) : Set (Vec d)) =
        s • ((cubeDomain Q : Domain d) : Set (Vec d)) := by
    simpa [s, cubeDomain_coe] using openCubeSet_dilateCube k Q
  have hToH1 : (undilate hCoeff v).toH1 = v.toH1.undilateSet hs hset := rfl
  have hgrad : ∀ x : Vec d, (undilate hCoeff v).toH1.grad x = v.toH1.grad (s • x) := by
    intro x
    rw [hToH1]
    exact H1Function.undilateSet_grad hs hset v.toH1 x
  have hval : ∀ x : Vec d,
      (undilate hCoeff v).toH1.toFun x = s⁻¹ * v.toH1.toFun (s • x) := by
    intro x
    rw [hToH1]
    exact H1Function.undilateSet_toFun hs hset v.toH1 x
  have hcancel_smul : ∀ x : Vec d, s • (s⁻¹ • x) = x := by
    intro x
    rw [smul_smul, mul_inv_cancel₀ (triadicDilationFactor_ne_zero k), one_smul]
  have hcancel_mul : ∀ t : ℝ, s * (s⁻¹ * t) = t := by
    intro t
    rw [← mul_assoc, mul_inv_cancel₀ (triadicDilationFactor_ne_zero k), one_mul]
  refine
    { value_ae_eq := Filter.Eventually.of_forall fun x => ?_
      grad_ae_eq := Filter.Eventually.of_forall fun x => ?_
      flux_ae_eq := hCoeff.coeff_ae_eq.mono fun x hx => ?_ }
  · show v.toH1.toFun x = s * (undilate hCoeff v).toH1.toFun (s⁻¹ • x)
    rw [hval (s⁻¹ • x), hcancel_smul x, hcancel_mul (v.toH1.toFun x)]
  · show v.toH1.grad x = (undilate hCoeff v).toH1.grad (s⁻¹ • x)
    rw [hgrad (s⁻¹ • x), hcancel_smul x]
  · have hx' : b.toCoeffField x = a.toCoeffField (s⁻¹ • x) := hx
    show matVecMul (b.toCoeffField x) (v.toH1.grad x) =
        matVecMul (a.toCoeffField (s⁻¹ • x)) ((undilate hCoeff v).toH1.grad (s⁻¹ • x))
    rw [hx', hgrad (s⁻¹ • x), hcancel_smul x]

theorem CubeDilation.is_solution {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    {hCoeff : CoeffOn.IsCubeDilation k a b}
    {u : Solution (cubeDomain Q) a}
    (v : CubeDilation hCoeff u) :
    IsAHarmonicGradient b.toCoeffField
      (openCubeSet (dilateCube k Q)) v.toSolution.toH1.grad :=
  v.toSolution.isHarmonic

theorem CubeDilation.grad_ae_eq {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    {hCoeff : CoeffOn.IsCubeDilation k a b}
    {u : Solution (cubeDomain Q) a}
    (v : CubeDilation hCoeff u) :
    v.toSolution.toH1.grad
      =ᵐ[volumeMeasureOn (openCubeSet (dilateCube k Q))]
      fun x => u.toH1.grad (undilateVec k x) :=
  v.isDilation.grad_ae_eq

theorem CubeDilation.flux_ae_eq {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    {hCoeff : CoeffOn.IsCubeDilation k a b}
    {u : Solution (cubeDomain Q) a}
    (v : CubeDilation hCoeff u) :
    (fun x => matVecMul (b.toCoeffField x) (v.toSolution.toH1.grad x))
      =ᵐ[volumeMeasureOn (openCubeSet (dilateCube k Q))]
      fun x =>
        matVecMul (a.toCoeffField (undilateVec k x))
          (u.toH1.grad (undilateVec k x)) :=
  v.isDilation.flux_ae_eq

end Solution

theorem average_eq_of_ae_eq {d : ℕ} {U : Domain d} {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volumeMeasureOn ((U : Domain d) : Set (Vec d))] g) :
    average U f = average U g := by
  unfold average
  congr 1
  exact MeasureTheory.integral_congr_ae hfg

theorem averageVec_eq_of_ae_eq {d : ℕ} {U : Domain d} {f g : Vec d → Vec d}
    (hfg : f =ᵐ[volumeMeasureOn ((U : Domain d) : Set (Vec d))] g) :
    averageVec U f = averageVec U g := by
  ext i
  exact average_eq_of_ae_eq (hfg.mono fun x hx => congrArg (fun y : Vec d => y i) hx)

theorem average_dilate_comp_undilate {d : ℕ} (k : ℤ) (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    average (cubeDomain (dilateCube k Q)) (fun x => f (undilateVec k x)) =
      average (cubeDomain Q) f := by
  change
    volumeAverage (openCubeSet (dilateCube k Q)) (fun x => f (undilateVec k x)) =
      volumeAverage (openCubeSet Q) f
  rw [openCubeSet_dilateCube]
  have h :=
    Ch01.volumeAverage_smul_set_comp_smul_of_pos
      (d := d) (triadicDilationFactor_pos k) (openCubeSet Q)
      (fun x => f (undilateVec k x))
  simpa [undilateVec, smul_smul, triadicDilationFactor_ne_zero k] using h

theorem averageVec_dilate_comp_undilate {d : ℕ} (k : ℤ) (Q : TriadicCube d)
    (F : Vec d → Vec d) :
    averageVec (cubeDomain (dilateCube k Q)) (fun x => F (undilateVec k x)) =
      averageVec (cubeDomain Q) F := by
  ext i
  exact average_dilate_comp_undilate k Q (fun x => F x i)

theorem responseIntegrand_dilate_ae {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    {hCoeff : CoeffOn.IsCubeDilation k a b}
    {u : Solution (cubeDomain Q) a}
    {v : Solution (cubeDomain (dilateCube k Q)) b}
    (hDilation : Solution.IsCubeDilation hCoeff u v) (p q : Vec d) :
    responseIntegrand (cubeDomain (dilateCube k Q)) b p q v
      =ᵐ[volumeMeasureOn (openCubeSet (dilateCube k Q))]
      fun x => responseIntegrand (cubeDomain Q) a p q u (undilateVec k x) := by
  filter_upwards [hDilation.grad_ae_eq, hCoeff.coeff_ae_eq] with x hgrad hcoeff
  simp [responseIntegrand, hgrad, hcoeff, dilateCoeffField]

theorem variationEnergyIntegrand_dilate_ae {d : ℕ} {k : ℤ}
    {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    {hCoeff : CoeffOn.IsCubeDilation k a b}
    {u : Solution (cubeDomain Q) a}
    {v : Solution (cubeDomain (dilateCube k Q)) b}
    (hDilation : Solution.IsCubeDilation hCoeff u v) :
    variationEnergyIntegrand (cubeDomain (dilateCube k Q)) b v
      =ᵐ[volumeMeasureOn (openCubeSet (dilateCube k Q))]
      fun x => variationEnergyIntegrand (cubeDomain Q) a u (undilateVec k x) := by
  filter_upwards [hDilation.grad_ae_eq, hCoeff.coeff_ae_eq] with x hgrad hcoeff
  simp [variationEnergyIntegrand, hgrad, hcoeff, dilateCoeffField]

theorem responseValue_dilate_of_isCubeDilation {d : ℕ} {k : ℤ}
    {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b)
    {u : Solution (cubeDomain Q) a}
    {v : Solution (cubeDomain (dilateCube k Q)) b}
    (hDilation : Solution.IsCubeDilation hCoeff u v) (p q : Vec d) :
    responseValue (cubeDomain (dilateCube k Q)) b p q v =
      responseValue (cubeDomain Q) a p q u := by
  unfold responseValue
  calc
    average (cubeDomain (dilateCube k Q))
        (responseIntegrand (cubeDomain (dilateCube k Q)) b p q v)
        =
      average (cubeDomain (dilateCube k Q))
        (fun x => responseIntegrand (cubeDomain Q) a p q u (undilateVec k x)) := by
        exact average_eq_of_ae_eq (responseIntegrand_dilate_ae hDilation p q)
    _ = average (cubeDomain Q) (responseIntegrand (cubeDomain Q) a p q u) :=
        average_dilate_comp_undilate k Q
          (responseIntegrand (cubeDomain Q) a p q u)

theorem variationEnergyValue_dilate_of_isCubeDilation {d : ℕ} {k : ℤ}
    {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b)
    {u : Solution (cubeDomain Q) a}
    {v : Solution (cubeDomain (dilateCube k Q)) b}
    (hDilation : Solution.IsCubeDilation hCoeff u v) :
    variationEnergyValue (cubeDomain (dilateCube k Q)) b v =
      variationEnergyValue (cubeDomain Q) a u := by
  unfold variationEnergyValue
  calc
    average (cubeDomain (dilateCube k Q))
        (variationEnergyIntegrand (cubeDomain (dilateCube k Q)) b v)
        =
      average (cubeDomain (dilateCube k Q))
        (fun x => variationEnergyIntegrand (cubeDomain Q) a u (undilateVec k x)) := by
        exact average_eq_of_ae_eq (variationEnergyIntegrand_dilate_ae hDilation)
    _ = average (cubeDomain Q) (variationEnergyIntegrand (cubeDomain Q) a u) :=
        average_dilate_comp_undilate k Q
          (variationEnergyIntegrand (cubeDomain Q) a u)

theorem averageGradient_dilate_of_isCubeDilation {d : ℕ} {k : ℤ}
    {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b)
    {u : Solution (cubeDomain Q) a}
    {v : Solution (cubeDomain (dilateCube k Q)) b}
    (hDilation : Solution.IsCubeDilation hCoeff u v) :
    averageGradient (cubeDomain (dilateCube k Q)) b v =
      averageGradient (cubeDomain Q) a u := by
  unfold averageGradient
  calc
    averageVec (cubeDomain (dilateCube k Q)) v.toH1.grad =
      averageVec (cubeDomain (dilateCube k Q))
        (fun x => u.toH1.grad (undilateVec k x)) := by
        exact averageVec_eq_of_ae_eq hDilation.grad_ae_eq
    _ = averageVec (cubeDomain Q) u.toH1.grad :=
        averageVec_dilate_comp_undilate k Q u.toH1.grad

theorem averageFlux_dilate_of_isCubeDilation {d : ℕ} {k : ℤ}
    {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b)
    {u : Solution (cubeDomain Q) a}
    {v : Solution (cubeDomain (dilateCube k Q)) b}
    (hDilation : Solution.IsCubeDilation hCoeff u v) :
    averageFlux (cubeDomain (dilateCube k Q)) b v =
      averageFlux (cubeDomain Q) a u := by
  unfold averageFlux
  calc
    averageVec (cubeDomain (dilateCube k Q))
        (fun x => matVecMul (b.toCoeffField x) (v.toH1.grad x)) =
      averageVec (cubeDomain (dilateCube k Q))
        (fun x =>
          matVecMul (a.toCoeffField (undilateVec k x))
            (u.toH1.grad (undilateVec k x))) := by
        exact averageVec_eq_of_ae_eq hDilation.flux_ae_eq
    _ = averageVec (cubeDomain Q)
        (fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x)) :=
        averageVec_dilate_comp_undilate k Q
          (fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x))

theorem responseValueSet_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) (p q : Vec d) :
    responseValueSet (cubeDomain (dilateCube k Q)) b p q =
      responseValueSet (cubeDomain Q) a p q := by
  ext m
  constructor
  · rintro ⟨v, rfl⟩
    exact
      ⟨Solution.undilate hCoeff v,
        responseValue_dilate_of_isCubeDilation hCoeff
          (Solution.undilate_isDilation hCoeff v) p q⟩
  · rintro ⟨u, rfl⟩
    let v := Solution.dilate hCoeff u
    exact
      ⟨v.toSolution,
        (responseValue_dilate_of_isCubeDilation hCoeff v.isDilation p q).symm⟩

theorem responseJ_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) (p q : Vec d) :
    responseJ (cubeDomain (dilateCube k Q)) b p q =
      responseJ (cubeDomain Q) a p q := by
  unfold responseJ
  rw [responseValueSet_dilate hCoeff p q]

theorem sigmaStarInvEntry_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) (i j : Fin d) :
    sigmaStarInvEntry (cubeDomain (dilateCube k Q)) b i j =
      sigmaStarInvEntry (cubeDomain Q) a i j := by
  by_cases hij : i = j
  · simp [sigmaStarInvEntry, hij, responseJ_dilate hCoeff]
  · simp [sigmaStarInvEntry, hij, responseJ_dilate hCoeff]

theorem sigmaStarInvCoarse_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) :
    sigmaStarInvCoarse (cubeDomain (dilateCube k Q)) b =
      sigmaStarInvCoarse (cubeDomain Q) a := by
  ext i j
  exact sigmaStarInvEntry_dilate hCoeff i j

theorem sigmaStarCoarse_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) :
    sigmaStarCoarse (cubeDomain (dilateCube k Q)) b =
      sigmaStarCoarse (cubeDomain Q) a := by
  simp [sigmaStarCoarse, sigmaStarInvCoarse_dilate hCoeff]

theorem mixedResponse_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) (p q : Vec d) :
    mixedResponse (cubeDomain (dilateCube k Q)) b p q =
      mixedResponse (cubeDomain Q) a p q := by
  simp [mixedResponse, responseJ_dilate hCoeff]

theorem sigmaStarInvKappaCoarse_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) :
    sigmaStarInvKappaCoarse (cubeDomain (dilateCube k Q)) b =
      sigmaStarInvKappaCoarse (cubeDomain Q) a := by
  ext i j
  exact mixedResponse_dilate hCoeff (Pi.single j 1) (Pi.single i 1)

theorem kappaCoarse_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) :
    kappaCoarse (cubeDomain (dilateCube k Q)) b =
      kappaCoarse (cubeDomain Q) a := by
  simp [kappaCoarse, sigmaStarCoarse_dilate hCoeff,
    sigmaStarInvKappaCoarse_dilate hCoeff]

theorem canonicalSigmaCorrectedResponse_dilate {d : ℕ} {k : ℤ}
    {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) (p : Vec d) :
    canonicalSigmaCorrectedResponse (cubeDomain (dilateCube k Q)) b p =
      canonicalSigmaCorrectedResponse (cubeDomain Q) a p := by
  simp [canonicalSigmaCorrectedResponse, responseJ_dilate hCoeff,
    sigmaStarInvCoarse_dilate hCoeff, kappaCoarse_dilate hCoeff]

theorem sigmaEntry_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) (i j : Fin d) :
    sigmaEntry (cubeDomain (dilateCube k Q)) b i j =
      sigmaEntry (cubeDomain Q) a i j := by
  by_cases hij : i = j
  · simp [sigmaEntry, hij, canonicalSigmaCorrectedResponse_dilate hCoeff]
  · simp [sigmaEntry, hij, canonicalSigmaCorrectedResponse_dilate hCoeff]

theorem sigmaCoarse_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) :
    sigmaCoarse (cubeDomain (dilateCube k Q)) b =
      sigmaCoarse (cubeDomain Q) a := by
  ext i j
  exact sigmaEntry_dilate hCoeff i j

theorem coarseMatrices_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) :
    coarseMatrices (cubeDomain (dilateCube k Q)) b =
      coarseMatrices (cubeDomain Q) a := by
  ext <;>
    simp [coarseMatrices, sigmaCoarse_dilate hCoeff,
      sigmaStarInvCoarse_dilate hCoeff, kappaCoarse_dilate hCoeff]

theorem bCoarse_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) :
    bCoarse (cubeDomain (dilateCube k Q)) b =
      bCoarse (cubeDomain Q) a := by
  unfold bCoarse
  rw [coarseMatrices_dilate hCoeff]

theorem aCoarse_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) :
    aCoarse (cubeDomain (dilateCube k Q)) b =
      aCoarse (cubeDomain Q) a := by
  unfold aCoarse
  rw [coarseMatrices_dilate hCoeff]

theorem aStarCoarse_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) :
    aStarCoarse (cubeDomain (dilateCube k Q)) b =
      aStarCoarse (cubeDomain Q) a := by
  simp [aStarCoarse, sigmaStarCoarse_dilate hCoeff, kappaCoarse_dilate hCoeff]

/-- One-cube public dilation statements.  These are the Chapter 3-facing facts:
solutions dilate to solutions, scalar and doubled response values are
unchanged, and all canonical one-cube coarse matrices are unchanged. -/
structure CubeDilationTheory (d : ℕ) : Prop where
  solution_dilation_exists :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      ∀ hCoeff : CoeffOn.IsCubeDilation k a b,
        ∀ u : Solution (cubeDomain Q) a,
          Nonempty (Solution.CubeDilation hCoeff u)
  responseValue_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))}
      (hCoeff : CoeffOn.IsCubeDilation k a b)
      {u : Solution (cubeDomain Q) a}
      {v : Solution (cubeDomain (dilateCube k Q)) b},
      Solution.IsCubeDilation hCoeff u v →
        ∀ p q : Vec d,
          responseValue (cubeDomain (dilateCube k Q)) b p q v =
            responseValue (cubeDomain Q) a p q u
  variationEnergyValue_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))}
      (hCoeff : CoeffOn.IsCubeDilation k a b)
      {u : Solution (cubeDomain Q) a}
      {v : Solution (cubeDomain (dilateCube k Q)) b},
      Solution.IsCubeDilation hCoeff u v →
        variationEnergyValue (cubeDomain (dilateCube k Q)) b v =
          variationEnergyValue (cubeDomain Q) a u
  averageGradient_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))}
      (hCoeff : CoeffOn.IsCubeDilation k a b)
      {u : Solution (cubeDomain Q) a}
      {v : Solution (cubeDomain (dilateCube k Q)) b},
      Solution.IsCubeDilation hCoeff u v →
        averageGradient (cubeDomain (dilateCube k Q)) b v =
          averageGradient (cubeDomain Q) a u
  averageFlux_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))}
      (hCoeff : CoeffOn.IsCubeDilation k a b)
      {u : Solution (cubeDomain Q) a}
      {v : Solution (cubeDomain (dilateCube k Q)) b},
      Solution.IsCubeDilation hCoeff u v →
        averageFlux (cubeDomain (dilateCube k Q)) b v =
          averageFlux (cubeDomain Q) a u
  responseJ_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        ∀ p q : Vec d,
          responseJ (cubeDomain (dilateCube k Q)) b p q =
            responseJ (cubeDomain Q) a p q
  doubledMu_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        ∀ P : BlockVec d,
          doubledMu (cubeDomain (dilateCube k Q)) b P =
            doubledMu (cubeDomain Q) a P
  doubledResponseJ_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        ∀ P R : BlockVec d,
          doubledResponseJ (cubeDomain (dilateCube k Q)) b P R =
            doubledResponseJ (cubeDomain Q) a P R
  sigmaCoarse_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        sigmaCoarse (cubeDomain (dilateCube k Q)) b =
          sigmaCoarse (cubeDomain Q) a
  sigmaStarInvCoarse_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        sigmaStarInvCoarse (cubeDomain (dilateCube k Q)) b =
          sigmaStarInvCoarse (cubeDomain Q) a
  sigmaStarCoarse_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        sigmaStarCoarse (cubeDomain (dilateCube k Q)) b =
          sigmaStarCoarse (cubeDomain Q) a
  kappaCoarse_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        kappaCoarse (cubeDomain (dilateCube k Q)) b =
          kappaCoarse (cubeDomain Q) a
  coarseMatrices_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        coarseMatrices (cubeDomain (dilateCube k Q)) b =
          coarseMatrices (cubeDomain Q) a
  bCoarse_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        bCoarse (cubeDomain (dilateCube k Q)) b =
          bCoarse (cubeDomain Q) a
  aCoarse_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        aCoarse (cubeDomain (dilateCube k Q)) b =
          aCoarse (cubeDomain Q) a
  aStarCoarse_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        aStarCoarse (cubeDomain (dilateCube k Q)) b =
          aStarCoarse (cubeDomain Q) a

/-- Chapter 2.5 multiscale dilation statements.  A dilation shifts every scale
index by `k`; the normalized multiscale quantities themselves do not change. -/
structure MultiscaleDilationTheory (d : ℕ) [NeZero d] : Prop where
  coarseBMatrixNorm_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ Q : TriadicCube d,
          coarseBMatrixNorm (dilateCube k Q) b =
            coarseBMatrixNorm Q a
  coarseSigmaStarInvMatrixNorm_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ Q : TriadicCube d,
          coarseSigmaStarInvMatrixNorm (dilateCube k Q) b =
            coarseSigmaStarInvMatrixNorm Q a
  maxDescendantBMatrixNormAtScale_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (n : ℤ),
          maxDescendantBMatrixNormAtScale (dilateCube k Q) (n + k) b =
            maxDescendantBMatrixNormAtScale Q n a
  maxDescendantSigmaStarInvMatrixNormAtScale_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (n : ℤ),
          maxDescendantSigmaStarInvMatrixNormAtScale (dilateCube k Q) (n + k) b =
            maxDescendantSigmaStarInvMatrixNormAtScale Q n a
  LambdaSq_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (s : ℝ) (q : MultiscaleExponent),
          LambdaSq (dilateCube k Q) s q b =
            LambdaSq Q s q a
  lambdaSq_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (s : ℝ) (q : MultiscaleExponent),
          lambdaSq (dilateCube k Q) s q b =
            lambdaSq Q s q a
  LambdaS_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (s : ℝ),
          LambdaS (dilateCube k Q) s b = LambdaS Q s a
  lambdaS_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (s : ℝ),
          lambdaS (dilateCube k Q) s b = lambdaS Q s a
  ThetaRatio_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (s t : ℝ),
          ThetaRatio (dilateCube k Q) s t b = ThetaRatio Q s t a
  maxDescendantUpperEllipticityAtScale_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (n : ℤ) (s : ℝ) (q : MultiscaleExponent),
          maxDescendantUpperEllipticityAtScale (dilateCube k Q) (n + k) s q b =
            maxDescendantUpperEllipticityAtScale Q n s q a
  maxDescendantLowerEllipticityInvAtScale_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (n : ℤ) (s : ℝ) (q : MultiscaleExponent),
          maxDescendantLowerEllipticityInvAtScale (dilateCube k Q) (n + k) s q b =
            maxDescendantLowerEllipticityInvAtScale Q n s q a
  normalizedBlockResponseMax_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (a0 : Mat d),
          normalizedBlockResponseMax (dilateCube k Q) b a0 =
            normalizedBlockResponseMax Q a a0
  maxDescendantNormalizedBlockResponseAtScale_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (n : ℤ) (a0 : Mat d),
          maxDescendantNormalizedBlockResponseAtScale (dilateCube k Q) (n + k) b a0 =
            maxDescendantNormalizedBlockResponseAtScale Q n a a0
  scaleResponseAtScale_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (n : ℤ) (p : MultiscaleExponent) (a0 : Mat d),
          scaleResponseAtScale (dilateCube k Q) (n + k) p b a0 =
            scaleResponseAtScale Q n p a a0
  HomogenizationError_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (n : ℤ) (s : ℝ)
          (p q : MultiscaleExponent) (a0 : Mat d),
          HomogenizationError (dilateCube k Q) (n + k) s p q b a0 =
            HomogenizationError Q n s p q a a0
  HomogenizationErrorOnCube_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (s : ℝ)
          (p q : MultiscaleExponent) (a0 : Mat d),
          HomogenizationErrorOnCube (dilateCube k Q) s p q b a0 =
            HomogenizationErrorOnCube Q s p q a a0

/-- Aggregate public dilation theorem package for Chapter 2 / 2.5, intended to
be imported by Chapter 3 scale-normalization arguments. -/
structure DilationTheory (d : ℕ) [NeZero d] : Prop where
  cube : CubeDilationTheory d
  multiscale : MultiscaleDilationTheory d

end

end Ch02
end Book
end Homogenization
