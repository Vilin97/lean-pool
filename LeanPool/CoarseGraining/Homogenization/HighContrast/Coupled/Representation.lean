/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.WeakForm
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CubeMinimizer

/-!
# Coupled representation (Proposition 3.1, existence direction)

Formalization of the EXISTENCE direction of `p.coupled.representation`
(the high-moment paper (Armstrong–Kuusi–Loher, to appear), §3.1) for the
pair constructed from the block minimizer, on the centered open triadic
cube `U = openCubeSet (originCube d m)`.

The converse (weak solution ⟹ minimizer) and uniqueness-mod-constants are out of
scope.

The weak-form predicate `CoupledWeakForm` (G0) and all algebraic scaffolding live
in `Coupled/WeakForm.lean`.  This file assembles the existence package `G1`:
`exists_coupledRepresentation`.

Vectors are `Vec d = Fin d → ℝ`; no `EuclideanSpace`.
-/

@[expose] public section

namespace Homogenization

open Homogenization
open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d] {m : ℤ} {Θ : ℝ} {a : CoeffField d}

/-! ## Weak-gradient uniqueness under a.e.-equal values -/

omit [NeZero d] in
/-- Weak partial derivatives are unique a.e. even when the scalar
representatives agree only a.e. on the open domain (Sobolev-level restatement,
avoiding the heavier `Book.Ch03` bridge import). -/
private theorem hasWeakPartial_ae_eq_of_toFun_ae_eq {U : Set (Vec d)} (hU : IsOpen U)
    {i : Fin d} {u v gi hi : Vec d → ℝ}
    (huv : u =ᵐ[volume.restrict U] v)
    (hgiLoc : MeasureTheory.LocallyIntegrableOn gi U volume)
    (hhiLoc : MeasureTheory.LocallyIntegrableOn hi U volume)
    (hgi : HasWeakPartialDerivOn U i u gi)
    (hhi : HasWeakPartialDerivOn U i v hi) :
    gi =ᵐ[volume.restrict U] hi := by
  refine HasWeakPartialDerivOn.ae_eq hU hgiLoc hhiLoc hgi ?_
  intro φ hφ_smooth hφ_compact hφ_sub
  calc
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume
        = ∫ x in U, v x * (fderiv ℝ φ x) (basisVec i) ∂volume :=
          MeasureTheory.integral_congr_ae (huv.mono fun x hx => by simp [hx])
    _ = -∫ x in U, hi x * φ x ∂volume := hhi φ hφ_smooth hφ_compact hφ_sub

omit [NeZero d] in
/-- On an open domain, two `H¹` representatives with a.e.-equal values have
a.e.-equal weak gradients. -/
private theorem h1grad_ae_eq_of_toFun_ae_eq {U : Set (Vec d)} (hU : IsOpen U)
    {u v : H1Function U}
    (huv : u.toFun =ᵐ[volume.restrict U] v.toFun) :
    u.grad =ᵐ[volume.restrict U] v.grad := by
  have hcoord : ∀ i : Fin d,
      (fun x => u.grad x i) =ᵐ[volume.restrict U] fun x => v.grad x i := by
    intro i
    exact hasWeakPartial_ae_eq_of_toFun_ae_eq hU huv
      (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
        ((u.gradMemL2 i).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)))
      (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
        ((v.gradMemL2 i).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)))
      (u.hasWeakGradient i) (v.hasWeakGradient i)
  have hall : ∀ᵐ x ∂volume.restrict U, ∀ i : Fin d, u.grad x i = v.grad x i :=
    MeasureTheory.ae_all_iff.mpr hcoord
  filter_upwards [hall] with x hx
  ext i; exact hx i

/-! ## Solenoidality of the constructed field `h = a∇v + aᵀ∇v*` -/

omit [NeZero d] in
/-- The field `h`, being (a.e.) the first component of `𝐁 Z`, is solenoidal:
pairing against potential-zero-trace test fields via `BlockResponseSpace`. -/
private theorem isSolenoidalOn_of_eq_fst
    {Z : BlockState d}
    (hRespO : BlockResponseSpace a (openCubeSet (originCube d m)) Z)
    {hfield : Vec d → Vec d}
    (hfield_eq : ∀ x,
      hfield x = (blockMatVecMul (blockCoeffField a x) (Z.eval x)).1) :
    IsSolenoidalOn (openCubeSet (originCube d m)) hfield := by
  intro φ0
  have hYtest :
      IsBlockTestOn (openCubeSet (originCube d m))
        { potential := φ0.toH1Function.grad, flux := 0 } :=
    ⟨φ0.isPotentialZeroTraceOn, isSolenoidalZeroNormalTraceOn_zero⟩
  have hint := hRespO.2.2 { potential := φ0.toH1Function.grad, flux := 0 } hYtest
  have hfun :
      (fun x => vecDot (hfield x) (φ0.toH1Function.grad x)) =
        (fun x =>
          blockVecDot
            (({ potential := φ0.toH1Function.grad, flux := 0 } : BlockState d).eval x)
            (blockMatVecMul (blockCoeffField a x) (Z.eval x))) := by
    funext x
    have hval :
        blockVecDot
            (({ potential := φ0.toH1Function.grad, flux := 0 } : BlockState d).eval x)
            (blockMatVecMul (blockCoeffField a x) (Z.eval x)) =
          vecDot (φ0.toH1Function.grad x) (hfield x) := by
      rw [hfield_eq]
      simp [BlockState.eval, blockVecDot, vecDot_zero_left]
    rw [hval, vecDot_comm]
  rw [hfun]; exact hint

/-! ## Mean-zero of `H¹₀` gradients paired with a constant -/

/-- For an `H¹₀` function on the open cube, the pairing of its gradient against
any constant vector integrates to zero (the C0(i) mean-zero fact). -/
private theorem integral_vecDot_grad_const_eq_zero
    (α10 : H10Function (openCubeSet (originCube d m))) (c : Vec d) :
    ∫ x in openCubeSet (originCube d m),
        vecDot (α10.toH1Function.grad x) c ∂volume = 0 := by
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  have hmz :
      (fun i => ∫ x in openCubeSet (originCube d m),
        α10.toH1Function.grad x i ∂volume) = 0 :=
    IsPotentialZeroTraceOn.integral_eq_zero_openCubeSet_originCube
      α10.isPotentialZeroTraceOn
  have hInt : ∀ i : Fin d,
      MeasureTheory.Integrable (fun x => α10.toH1Function.grad x i * c i)
        (volume.restrict (openCubeSet (originCube d m))) := by
    intro i
    exact ((α10.toH1Function.gradMemL2 i).integrable (by norm_num)).mul_const (c i)
  calc
    ∫ x in openCubeSet (originCube d m), vecDot (α10.toH1Function.grad x) c ∂volume
        = ∫ x in openCubeSet (originCube d m),
            ∑ i, α10.toH1Function.grad x i * c i ∂volume := rfl
    _ = ∑ i, ∫ x in openCubeSet (originCube d m),
            α10.toH1Function.grad x i * c i ∂volume :=
          MeasureTheory.integral_finsetSum _ (fun i _ => hInt i)
    _ = ∑ i, (∫ x in openCubeSet (originCube d m),
            α10.toH1Function.grad x i ∂volume) * c i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [MeasureTheory.integral_mul_const]
    _ = 0 := by
          have hz : ∀ i, (∫ x in openCubeSet (originCube d m),
              α10.toH1Function.grad x i ∂volume) = 0 :=
            fun i => congrFun hmz i
          simp [hz]

/-! ## The weak form of the constructed pair -/

/-- The constructed pair `(v, v*)` satisfies the weak form of the coupled
problem.  The proof is the paper's `α/β` split:
`α := ½(φ+φ*) ∈ H¹₀` pairs to zero against the solenoidal field
`h = a∇v + aᵀ∇v*`, `β := ½(φ−φ*)` pairs against `j − q` (admissibility), and the
constant `q` integrates to zero against `∇α`. -/
private theorem coupledWeakForm_aux {P : BlockVec d}
    {Z : BlockState d} {v vstar : H1Function (openCubeSet (originCube d m))}
    (hEllO : IsEllipticFieldOn 1 Θ (openCubeSet (originCube d m)) a)
    (hAdmO : IsBlockMuAdmissible (openCubeSet (originCube d m)) P Z)
    (hRespO : BlockResponseSpace a (openCubeSet (originCube d m)) Z)
    (hf_fst : ∀ x,
      matVecMul (a x) (v.grad x) + matVecMul (matTranspose (a x)) (vstar.grad x) =
        (blockMatVecMul (blockCoeffField a x) (Z.eval x)).1)
    (hj_flux : ∀ x, x ∈ openCubeSet (originCube d m) →
      matVecMul (a x) (v.grad x) - matVecMul (matTranspose (a x)) (vstar.grad x) =
        Z.flux x) :
    CoupledWeakForm a (openCubeSet (originCube d m)) P.2 v vstar := by
  intro φ φstar hMemSum
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  -- abbreviations
  set Av : Vec d → Vec d := fun x => matVecMul (a x) (v.grad x) with hAv
  set As : Vec d → Vec d := fun x => matVecMul (matTranspose (a x)) (vstar.grad x) with hAs
  set hf : Vec d → Vec d := fun x => Av x + As x with hhf
  set jf : Vec d → Vec d := fun x => Av x - As x with hjf
  set αg : Vec d → Vec d := fun x => (1 / 2 : ℝ) • (φ.grad x + φstar.grad x) with hαg
  set βg : Vec d → Vec d := fun x => (1 / 2 : ℝ) • (φ.grad x - φstar.grad x) with hβg
  -- L² memberships
  have hvgL2 : MemVectorL2 (openCubeSet (originCube d m)) v.grad := v.grad_memVectorL2
  have hvsgL2 : MemVectorL2 (openCubeSet (originCube d m)) vstar.grad := vstar.grad_memVectorL2
  have hφgL2 : MemVectorL2 (openCubeSet (originCube d m)) φ.grad := φ.grad_memVectorL2
  have hφsgL2 : MemVectorL2 (openCubeSet (originCube d m)) φstar.grad := φstar.grad_memVectorL2
  have hAvL2 : MemVectorL2 (openCubeSet (originCube d m)) Av := memVectorL2_matVecMul_of_isEllipticFieldOn hEllO hvgL2
  have hAsL2 : MemVectorL2 (openCubeSet (originCube d m)) As := by
    have heq : As = fun x => matVecMul (symmPart (a x)) (vstar.grad x) -
        matVecMul (skewPart (a x)) (vstar.grad x) := by
      funext x; exact matVecMul_matTranspose_eq (a x) (vstar.grad x)
    rw [heq]
    exact (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEllO hvsgL2).sub
      (memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEllO hvsgL2)
  have hfL2 : MemVectorL2 (openCubeSet (originCube d m)) hf := hAvL2.add hAsL2
  have hjfL2 : MemVectorL2 (openCubeSet (originCube d m)) jf := hAvL2.sub hAsL2
  have hαgL2 : MemVectorL2 (openCubeSet (originCube d m)) αg := (hφgL2.add hφsgL2).const_smul (1 / 2 : ℝ)
  have hβgL2 : MemVectorL2 (openCubeSet (originCube d m)) βg := (hφgL2.sub hφsgL2).const_smul (1 / 2 : ℝ)
  have hZfluxL2 : MemVectorL2 (openCubeSet (originCube d m)) Z.flux := by
    have h := (memVectorL2_const (U := (openCubeSet (originCube d m))) P.2).add hAdmO.fluxCorrection_memL2
    have heq : ((fun _ : Vec d => P.2) + fun x => Z.flux x - P.2) = Z.flux := by
      funext x; simp only [Pi.add_apply]; abel
    rwa [heq] at h
  -- integrability shortcuts
  have hInt : ∀ {f g : Vec d → Vec d}, MemVectorL2 (openCubeSet (originCube d m)) f → MemVectorL2 (openCubeSet (originCube d m)) g →
      MeasureTheory.IntegrableOn (fun x => vecDot (f x) (g x)) (openCubeSet (originCube d m)) :=
    fun hf hg => integrableOn_vecDot_of_memVectorL2 hf hg
  -- α as an H¹₀ competitor (via the trace hypothesis)
  obtain ⟨w0, hw0⟩ := hMemSum
  set α10 : H10Function (openCubeSet (originCube d m)) := (1 / 2 : ℝ) • w0 with hα10
  have hα10grad_ae : α10.toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))] αg := by
    have hgrad_w0 : w0.toH1Function.grad =ᵐ[volume.restrict (openCubeSet (originCube d m))]
        (fun x => φ.grad x + φstar.grad x) := by
      have htoFun : w0.toH1Function.toFun =ᵐ[volume.restrict (openCubeSet (originCube d m))] (φ + φstar).toFun := by
        rw [hw0]
        exact MeasureTheory.ae_of_all _ (fun x => rfl)
      have := h1grad_ae_eq_of_toFun_ae_eq (isOpen_openCubeSet _) htoFun
      simpa using this
    have hα10grad : α10.toH1Function.grad = fun x => (1 / 2 : ℝ) • w0.toH1Function.grad x := rfl
    rw [hα10grad]
    filter_upwards [hgrad_w0] with x hx
    show (1 / 2 : ℝ) • w0.toH1Function.grad x = αg x
    rw [hx]
  -- pointwise α/β split of the integrand
  have hsplit : ∀ x,
      vecDot (φ.grad x) (Av x) + vecDot (φstar.grad x) (As x) =
        vecDot (αg x) (hf x) + vecDot (βg x) (jf x) := by
    intro x
    exact vecDot_alpha_beta_split (φ.grad x) (φstar.grad x) (Av x) (As x)
  -- h is solenoidal
  have hSol : IsSolenoidalOn (openCubeSet (originCube d m)) hf :=
    isSolenoidalOn_of_eq_fst (hfield := hf) hRespO (fun x => hf_fst x)
  -- ∫ ∇α·h = 0
  have hIhf : ∫ x in (openCubeSet (originCube d m)), vecDot (αg x) (hf x) ∂volume = 0 := by
    have hae : (fun x => vecDot (αg x) (hf x)) =ᵐ[volume.restrict (openCubeSet (originCube d m))]
        (fun x => vecDot (hf x) (α10.toH1Function.grad x)) := by
      filter_upwards [hα10grad_ae] with x hx
      rw [← hx, vecDot_comm]
    rw [MeasureTheory.integral_congr_ae hae]
    exact hSol α10
  -- ∫ ∇β·j = ∫ ∇β·q
  have hIjf : ∫ x in (openCubeSet (originCube d m)), vecDot (βg x) (jf x) ∂volume =
      ∫ x in (openCubeSet (originCube d m)), vecDot (βg x) P.2 ∂volume := by
    have hjf_flux : (fun x => vecDot (βg x) (jf x)) =ᵐ[volume.restrict (openCubeSet (originCube d m))]
        (fun x => vecDot (βg x) (Z.flux x)) := by
      have hmemU : ∀ᵐ x ∂volume.restrict (openCubeSet (originCube d m)), x ∈ (openCubeSet (originCube d m)) :=
        MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet _)
      filter_upwards [hmemU] with x hx
      show vecDot (βg x) (jf x) = vecDot (βg x) (Z.flux x)
      have hjx : jf x = Z.flux x := hj_flux x hx
      rw [hjx]
    rw [MeasureTheory.integral_congr_ae hjf_flux]
    -- admissibility: ∫ (Z.flux − q)·∇β = 0
    set β : H1Function (openCubeSet (originCube d m)) := (1 / 2 : ℝ) • (φ - φstar) with hβ
    have hβgrad : ∀ x, β.grad x = βg x := by
      intro x
      show (1 / 2 : ℝ) • ((φ - φstar).grad x) = βg x
      rw [hβg, Homogenization.H1Function.sub_grad]
    have hadm := hAdmO.isSolenoidalZeroNormalTrace β
    have hexp : (fun x => vecDot ((fun y => Z.flux y - P.2) x) (β.grad x)) =
        (fun x => vecDot (Z.flux x) (βg x) - vecDot P.2 (βg x)) := by
      funext x
      rw [hβgrad x]
      show vecDot (Z.flux x - P.2) (βg x) = vecDot (Z.flux x) (βg x) - vecDot P.2 (βg x)
      rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]
    rw [hexp] at hadm
    have hsub := MeasureTheory.integral_sub
      (hInt hZfluxL2 hβgL2) (hInt (memVectorL2_const (U := (openCubeSet (originCube d m))) P.2) hβgL2)
    rw [hsub] at hadm
    have : ∫ x in (openCubeSet (originCube d m)), vecDot (Z.flux x) (βg x) ∂volume =
        ∫ x in (openCubeSet (originCube d m)), vecDot P.2 (βg x) ∂volume := by linarith [hadm]
    calc
      ∫ x in (openCubeSet (originCube d m)), vecDot (βg x) (Z.flux x) ∂volume
          = ∫ x in (openCubeSet (originCube d m)), vecDot (Z.flux x) (βg x) ∂volume := by
            apply MeasureTheory.integral_congr_ae; apply MeasureTheory.ae_of_all
            intro x; exact vecDot_comm _ _
      _ = ∫ x in (openCubeSet (originCube d m)), vecDot P.2 (βg x) ∂volume := this
      _ = ∫ x in (openCubeSet (originCube d m)), vecDot (βg x) P.2 ∂volume := by
            apply MeasureTheory.integral_congr_ae; apply MeasureTheory.ae_of_all
            intro x; exact vecDot_comm _ _
  -- ∫ ∇α·q = 0
  have hIαq : ∫ x in (openCubeSet (originCube d m)), vecDot (αg x) P.2 ∂volume = 0 := by
    have hae : (fun x => vecDot (αg x) P.2) =ᵐ[volume.restrict (openCubeSet (originCube d m))]
        (fun x => vecDot (α10.toH1Function.grad x) P.2) := by
      filter_upwards [hα10grad_ae] with x hx
      rw [hx]
    rw [MeasureTheory.integral_congr_ae hae]
    exact integral_vecDot_grad_const_eq_zero α10 P.2
  -- assemble
  have hLHS : (∫ x in (openCubeSet (originCube d m)), vecDot (φ.grad x) (Av x) ∂volume) +
      (∫ x in (openCubeSet (originCube d m)), vecDot (φstar.grad x) (As x) ∂volume) =
        ∫ x in (openCubeSet (originCube d m)), vecDot (βg x) P.2 ∂volume := by
    rw [← MeasureTheory.integral_add (hInt hφgL2 hAvL2) (hInt hφsgL2 hAsL2)]
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hsplit)]
    rw [MeasureTheory.integral_add (hInt hαgL2 hfL2) (hInt hβgL2 hjfL2)]
    rw [hIhf, hIjf, zero_add]
  have hRHS : (∫ x in (openCubeSet (originCube d m)), vecDot P.2 (φ.grad x) ∂volume) =
      ∫ x in (openCubeSet (originCube d m)), vecDot (βg x) P.2 ∂volume := by
    have hφ : (fun x => vecDot P.2 (φ.grad x)) =ᵐ[volume.restrict (openCubeSet (originCube d m))]
        (fun x => vecDot (αg x) P.2 + vecDot (βg x) P.2) := by
      apply MeasureTheory.ae_of_all
      intro x
      show vecDot P.2 (φ.grad x) = vecDot (αg x) P.2 + vecDot (βg x) P.2
      rw [vecDot_comm P.2 (φ.grad x), ← vecDot_add_left]
      congr 1
      show φ.grad x = αg x + βg x
      rw [hαg, hβg]; module
    rw [MeasureTheory.integral_congr_ae hφ]
    rw [MeasureTheory.integral_add (hInt hαgL2 (memVectorL2_const (U := (openCubeSet (originCube d m))) P.2))
        (hInt hβgL2 (memVectorL2_const (U := (openCubeSet (originCube d m))) P.2))]
    rw [hIαq, zero_add]
  rw [hLHS, hRHS]

/-! ## G1 — the coupled representation existence package -/

/-- **G1.**  Existence direction of the coupled representation
(`p.coupled.representation`) on the centered open triadic cube.

For `P = (p, q)` there exist the block minimizer `Z` (transferred to the
open cube) and `H¹` functions `v, v*` such that:

* **(i)** `Z` is admissible for `P`, energy-realizing, and in the block response
  space;
* **(ii)** trace: `v + v* − p·x ∈ H¹₀(U)`;
* **(iii)** gradient dictionary a.e.: `Z.potential = ∇v + ∇v*` and
  `Z.flux = a∇v − aᵗ∇v*`;
* **(iv)** the weak form `CoupledWeakForm`;
* **(v)** energy identity a.e.:
  `Z·𝐁 Z = 2∇v·s∇v + 2∇v*·s∇v*`. -/
theorem exists_coupledRepresentation
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) (P : BlockVec d) :
    ∃ (Z : BlockState d) (v vstar : H1Function (openCubeSet (originCube d m))),
      IsBlockMuAdmissible (openCubeSet (originCube d m)) P Z ∧
        Mu (openCubeSet (originCube d m)) P a =
          blockEnergyAverage (openCubeSet (originCube d m)) a Z ∧
        BlockResponseSpace a (openCubeSet (originCube d m)) Z ∧
        MemH10 (openCubeSet (originCube d m))
          (fun x => v.toFun x + vstar.toFun x - vecDot P.1 x) ∧
        Z.potential =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
          (fun x => v.grad x + vstar.grad x) ∧
        Z.flux =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
          (fun x => matVecMul (a x) (v.grad x) -
            matVecMul (matTranspose (a x)) (vstar.grad x)) ∧
        CoupledWeakForm a (openCubeSet (originCube d m)) P.2 v vstar ∧
        (fun x => blockVecDot (Z.eval x)
            (blockMatVecMul (blockCoeffField a x) (Z.eval x))) =ᵐ[volumeMeasureOn
              (openCubeSet (originCube d m))]
          (fun x => 2 * vecDot (v.grad x) (matVecMul (symmPart (a x)) (v.grad x)) +
            2 * vecDot (vstar.grad x) (matVecMul (symmPart (a x)) (vstar.grad x))) := by
  classical
  set U := openCubeSet (originCube d m) with hUdef
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  have hUopen : IsOpen U := isOpen_openCubeSet (originCube d m)
  -- Ellipticity transferred to the open cube.
  have hEllO : IsEllipticFieldOn 1 Θ U a :=
    hEll.mono (measurableSet_openCubeSet (originCube d m))
      (openCubeSet_subset_cubeSet (originCube d m))
  -- The block minimizer, transferred to the open cube.
  obtain ⟨Z, hAdmC, hEnergyC, hRespC⟩ := exists_cubeBlockMinimizer hEll P
  have hAdmO : IsBlockMuAdmissible U P Z :=
    (isBlockMuAdmissible_cubeSet_originCube_iff_openCubeSet).1 hAdmC
  have hRespO : BlockResponseSpace a U Z :=
    (blockResponseSpace_cubeSet_originCube_iff_openCubeSet).1 hRespC
  have hEnergyO : Mu U P a = blockEnergyAverage U a Z := by
    rw [← Mu_cubeSet_originCube_eq_openCubeSet (d := d) m P a, hEnergyC]
    unfold blockEnergyAverage
    exact volumeAverage_cubeSet_originCube_eq_openCubeSet (d := d) m (blockEnergyDensity a Z)
  -- L² memberships of the minimizer fields.
  have hPotL2 : MemVectorL2 U Z.potential := by
    have h := (memVectorL2_const (U := U) P.1).add hAdmO.potentialCorrection_memL2
    have heq : ((fun _ : Vec d => P.1) + fun x => Z.potential x - P.1) = Z.potential := by
      funext x; simp only [Pi.add_apply]; abel
    rwa [heq] at h
  have hFluxL2 : MemVectorL2 U Z.flux := by
    have h := (memVectorL2_const (U := U) P.2).add hAdmO.fluxCorrection_memL2
    have heq : ((fun _ : Vec d => P.2) + fun x => Z.flux x - P.2) = Z.flux := by
      funext x; simp only [Pi.add_apply]; abel
    rwa [heq] at h
  -- τ := second component of `𝐁 Z`.
  set τ : Vec d → Vec d :=
    fun x => matVecMul ((symmPart (a x))⁻¹)
      (Z.flux x - matVecMul (skewPart (a x)) (Z.potential x)) with hτdef
  have hsnd : ∀ x, (blockMatVecMul (blockCoeffField a x) (Z.eval x)).2 = τ x := fun x =>
    blockMatVecMul_blockMatrixOfCoeff_snd (a x) (Z.potential x) (Z.flux x)
  have hfst : ∀ x, (blockMatVecMul (blockCoeffField a x) (Z.eval x)).1 =
      matVecMul (symmPart (a x)) (Z.potential x) + matVecMul (skewPart (a x)) (τ x) := fun x =>
    blockMatVecMul_blockMatrixOfCoeff_fst (a x) (Z.potential x) (Z.flux x)
  -- τ ∈ L².
  have hτL2 : MemVectorL2 U τ := by
    have hk : MemVectorL2 U (fun x => matVecMul (skewPart (a x)) (Z.potential x)) :=
      memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEllO hPotL2
    exact memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn hEllO (hFluxL2.sub hk)
  -- Hodge converse: τ is a potential field.
  have hτorth : ∀ {g : Vec d → Vec d}, MemVectorL2 U g →
      IsSolenoidalZeroNormalTraceOn U g →
        ∫ x in U, vecDot (g x) (τ x) ∂volume = 0 := by
    intro g hgL2 hgSol
    have hYtest : IsBlockTestOn U { potential := 0, flux := g } :=
      ⟨isPotentialZeroTraceOn_zero, hgSol⟩
    have hint := hRespO.2.2 { potential := 0, flux := g } hYtest
    have hfun : (fun x => vecDot (g x) (τ x)) =
        (fun x => blockVecDot (({ potential := 0, flux := g } : BlockState d).eval x)
          (blockMatVecMul (blockCoeffField a x) (Z.eval x))) := by
      funext x
      rw [show (({ potential := 0, flux := g } : BlockState d).eval x) = (0, g x) from rfl]
      simp only [blockVecDot, vecDot_zero_left, zero_add]
      rw [hsnd x]
    rw [hfun]; exact hint
  have hpotτ : IsPotentialOn U τ :=
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet (originCube d m))) hτL2 hτorth
  obtain ⟨ψ, hψ⟩ := hpotτ
  -- The `H¹₀` potential witness `w`; the affine part; `u := w + p·x`.
  obtain ⟨w, hw⟩ := hAdmO.isPotentialZeroTrace
  set u : H1Function U := w.toH1Function + affineH1 m P.1 with hudef
  have hugrad : ∀ x, u.grad x = Z.potential x := by
    intro x
    show w.toH1Function.grad x + (affineH1 m P.1).grad x = Z.potential x
    rw [hw, affineH1_grad]
    show (Z.potential x - P.1) + P.1 = Z.potential x
    abel
  have hutoFun : ∀ x, u.toFun x = w.toH1Function.toFun x + vecDot P.1 x := by
    intro x
    show w.toH1Function.toFun x + (affineH1 m P.1).toFun x =
      w.toH1Function.toFun x + vecDot P.1 x
    rw [affineH1_toFun]
  -- The pair `v = (u+ψ)/2`, `v* = (u−ψ)/2`.
  set v : H1Function U := (1 / 2 : ℝ) • (u + ψ) with hvdef
  set vstar : H1Function U := (1 / 2 : ℝ) • (u - ψ) with hvsdef
  have hvg : ∀ x, v.grad x = (1 / 2 : ℝ) • (Z.potential x + τ x) := by
    intro x
    have hstep : v.grad x = (1 / 2 : ℝ) • (u.grad x + ψ.grad x) := by
      show ((1 / 2 : ℝ) • (u + ψ)).grad x = (1 / 2 : ℝ) • (u.grad x + ψ.grad x)
      rw [Homogenization.H1Function.smul_grad, Homogenization.H1Function.add_grad]
    rw [hstep, hugrad, hψ]
  have hvsg : ∀ x, vstar.grad x = (1 / 2 : ℝ) • (Z.potential x - τ x) := by
    intro x
    have hstep : vstar.grad x = (1 / 2 : ℝ) • (u.grad x - ψ.grad x) := by
      show ((1 / 2 : ℝ) • (u - ψ)).grad x = (1 / 2 : ℝ) • (u.grad x - ψ.grad x)
      rw [Homogenization.H1Function.smul_grad, Homogenization.H1Function.sub_grad]
    rw [hstep, hugrad, hψ]
  have hsumg : ∀ x, v.grad x + vstar.grad x = Z.potential x := by
    intro x; rw [hvg, hvsg]; module
  have hdiffg : ∀ x, v.grad x - vstar.grad x = τ x := by
    intro x; rw [hvg, hvsg]; module
  -- The two flux identities.
  have hf_fst : ∀ x, matVecMul (a x) (v.grad x) +
      matVecMul (matTranspose (a x)) (vstar.grad x) =
        (blockMatVecMul (blockCoeffField a x) (Z.eval x)).1 := by
    intro x
    rw [matVecMul_add_matTranspose_eq, hsumg x, hdiffg x, hfst x]
  have hj_flux : ∀ x, x ∈ U → matVecMul (a x) (v.grad x) -
      matVecMul (matTranspose (a x)) (vstar.grad x) = Z.flux x := by
    intro x hx
    rw [matVecMul_sub_matTranspose_eq, hsumg x, hdiffg x]
    have hdet : IsUnit (symmPart (a x)).det :=
      isUnit_det_symmPart_of_isEllipticMatrix (hEllO.2 x hx)
    have hsτ : matVecMul (symmPart (a x)) (τ x) =
        Z.flux x - matVecMul (skewPart (a x)) (Z.potential x) := by
      show matVecMul (symmPart (a x)) (matVecMul ((symmPart (a x))⁻¹)
        (Z.flux x - matVecMul (skewPart (a x)) (Z.potential x))) = _
      rw [matVecMul_mul, Matrix.mul_nonsing_inv _ hdet, matVecMul_one]
    rw [hsτ]; abel
  -- assemble the package
  refine ⟨Z, v, vstar, hAdmO, hEnergyO, hRespO, ?_, ?_, ?_, ?_, ?_⟩
  · -- (ii) trace
    refine ⟨w, ?_⟩
    funext x
    show w.toH1Function.toFun x = v.toFun x + vstar.toFun x - vecDot P.1 x
    have hvtf : v.toFun x + vstar.toFun x = u.toFun x := by
      show ((1 / 2 : ℝ) • (u + ψ)).toFun x + ((1 / 2 : ℝ) • (u - ψ)).toFun x = u.toFun x
      rw [Homogenization.H1Function.smul_toFun, Homogenization.H1Function.smul_toFun,
        Homogenization.H1Function.add_toFun, Homogenization.H1Function.sub_toFun]
      ring
    rw [hvtf, hutoFun x]; ring
  · -- (iii-a) potential dictionary
    exact MeasureTheory.ae_of_all _ (fun x => (hsumg x).symm)
  · -- (iii-b) flux dictionary
    refine (MeasureTheory.ae_restrict_iff' (measurableSet_openCubeSet _)).2 ?_
    exact MeasureTheory.ae_of_all _ (fun x hx => (hj_flux x hx).symm)
  · -- (iv) weak form
    exact coupledWeakForm_aux hEllO hAdmO hRespO hf_fst hj_flux
  · -- (v) energy identity
    refine (MeasureTheory.ae_restrict_iff' (measurableSet_openCubeSet _)).2 ?_
    refine MeasureTheory.ae_of_all _ (fun x hx => ?_)
    have hdet : IsUnit (symmPart (a x)).det :=
      isUnit_det_symmPart_of_isEllipticMatrix (hEllO.2 x hx)
    show blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)) =
      2 * vecDot (v.grad x) (matVecMul (symmPart (a x)) (v.grad x)) +
        2 * vecDot (vstar.grad x) (matVecMul (symmPart (a x)) (vstar.grad x))
    rw [hvg x, hvsg x]
    have hLHS : blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)) =
        vecDot (Z.potential x) (matVecMul (symmPart (a x)) (Z.potential x)) +
          vecDot (τ x) (matVecMul (symmPart (a x)) (τ x)) := by
      show blockVecDot (Z.potential x, Z.flux x)
        (blockMatVecMul (blockMatrixOfCoeff (a x)) (Z.potential x, Z.flux x)) = _
      rw [blockEnergy_pointwise_eq hdet]
    rw [hLHS, ← two_vecDot_symmPart_half_add_sub (symmPart (a x)) (Z.potential x) (τ x)]

end

end Homogenization
