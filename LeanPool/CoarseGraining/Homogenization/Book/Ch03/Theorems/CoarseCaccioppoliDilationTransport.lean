/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoli.Interface
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.Dilation

/-! # Coarse Caccioppoli Dilation Transport -/

@[expose] public section

open scoped Pointwise ENNReal

namespace Homogenization
namespace Book
namespace Ch03

noncomputable section

/-!
# Dilation transport proof for coarse Caccioppoli

The scale-zero coarse Caccioppoli theorem and public arbitrary-scale target are
imported from `CoarseCaccioppoli.Interface`.  This file proves the concrete
normalization witnesses and closes the public arbitrary-scale theorem directly,
without exporting an intermediate bridge package.

The intended source of the witnesses below is the public Chapter 2 dilation
package, together with the Chapter 1 norm-scaling lemmas.  The interface fixes
the normalized cube to `Ch02.dilateCube (-Q.scale) Q`, so downstream code cannot
drift to a different normalization convention.
-/

/-- The center of a dilated triadic cube is the dilation of its center. -/
theorem cubeCenter_dilateCube {d : ℕ} (k : ℤ) (Q : TriadicCube d) :
    cubeCenter (Ch02.dilateCube k Q) = Ch02.dilateVec k (cubeCenter Q) := by
  ext i
  simp [cubeCenter, Ch02.dilateVec, Ch02.cubeScaleFactor_dilateCube,
    Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]

/-- A triadic open window dilates with its center and scale. -/
theorem openCubeAtScale_dilateVec {d : ℕ} (k m : ℤ) (x : Vec d) :
    openCubeAtScale (Ch02.dilateVec k x) (m + k) =
      Ch02.triadicDilationFactor k • openCubeAtScale x m := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_smul_set]
    refine ⟨Ch02.undilateVec k y, ?_, ?_⟩
    · intro i
      let r : ℝ := Ch02.triadicDilationFactor k
      have hr : 0 < r := by
        dsimp [r]
        exact Ch02.triadicDilationFactor_pos k
      have hri : r ≠ 0 := hr.ne'
      have hyi := hy i
      have hrad :
          (3 : ℝ) ^ (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) / 2 =
            r * ((3 : ℝ) ^ m / 2) := by
        calc
          (3 : ℝ) ^ (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) / 2 =
              (Real.rpow (3 : ℝ) (((m : ℤ) : ℝ)) *
                Real.rpow (3 : ℝ) (((k : ℤ) : ℝ))) / 2 := by
            exact congrArg (fun z : ℝ => z / 2)
              (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
                (((m : ℤ) : ℝ)) (((k : ℤ) : ℝ)))
          _ = r * (Real.rpow (3 : ℝ) (((m : ℤ) : ℝ)) / 2) := by
            have hk :
                Real.rpow (3 : ℝ) (((k : ℤ) : ℝ)) = r := by
              dsimp [r, Ch02.triadicDilationFactor]
              exact Real.rpow_intCast (3 : ℝ) k
            rw [hk]
            ring
          _ = r * ((3 : ℝ) ^ m / 2) := by
            exact congrArg (fun z : ℝ => r * (z / 2))
              (Real.rpow_intCast (3 : ℝ) m)
      have hscaled :
          |y i - r * x i| <
            r * ((3 : ℝ) ^ m / 2) := by
        have hyi' :
            |y i - r * x i| <
              (3 : ℝ) ^ (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) / 2 := by
          simpa [Ch02.dilateVec, Pi.smul_apply, smul_eq_mul,
            Int.cast_add, r] using hyi
        simpa [hrad] using hyi'
      have hdiv :
          |(y i - r * x i) / r| <
            (3 : ℝ) ^ m / 2 := by
        rw [abs_div, abs_of_pos hr]
        exact (div_lt_iff₀ hr).2 (by simpa [mul_comm] using hscaled)
      have hcoord :
        (Ch02.undilateVec k y) i - x i = (y i - r * x i) / r := by
        have hri' : Ch02.triadicDilationFactor k ≠ 0 :=
          Ch02.triadicDilationFactor_ne_zero k
        simp [Ch02.undilateVec, r, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
        field_simp [hri']
      simpa [hcoord, Real.rpow_intCast] using hdiv
    · ext i
      simp [Ch02.undilateVec, Pi.smul_apply, smul_eq_mul,
        Ch02.triadicDilationFactor_ne_zero k]
  · rintro ⟨z, hz, rfl⟩
    intro i
    let r : ℝ := Ch02.triadicDilationFactor k
    have hr : 0 < r := by
      dsimp [r]
      exact Ch02.triadicDilationFactor_pos k
    have hrad :
        (3 : ℝ) ^ (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) / 2 =
          r * ((3 : ℝ) ^ m / 2) := by
      calc
        (3 : ℝ) ^ (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) / 2 =
            (Real.rpow (3 : ℝ) (((m : ℤ) : ℝ)) *
              Real.rpow (3 : ℝ) (((k : ℤ) : ℝ))) / 2 := by
          exact congrArg (fun z : ℝ => z / 2)
            (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
              (((m : ℤ) : ℝ)) (((k : ℤ) : ℝ)))
        _ = r * (Real.rpow (3 : ℝ) (((m : ℤ) : ℝ)) / 2) := by
          have hk :
              Real.rpow (3 : ℝ) (((k : ℤ) : ℝ)) = r := by
            dsimp [r, Ch02.triadicDilationFactor]
            exact Real.rpow_intCast (3 : ℝ) k
          rw [hk]
          ring
        _ = r * ((3 : ℝ) ^ m / 2) := by
          exact congrArg (fun z : ℝ => r * (z / 2))
            (Real.rpow_intCast (3 : ℝ) m)
    have hz_i := hz i
    have hmul := mul_lt_mul_of_pos_left hz_i hr
    have hcoord :
        |(r • z) i - (Ch02.dilateVec k x) i| =
          r * |z i - x i| := by
      have hsub :
          (r • z) i - (Ch02.dilateVec k x) i =
            r * (z i - x i) := by
        simp [Ch02.dilateVec, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hsub, abs_mul, abs_of_pos hr]
    have hmul' :
        r * |z i - x i| <
          (3 : ℝ) ^ (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) / 2 := by
      simpa [hrad] using hmul
    have hgoal :
        |(r • z) i - (Ch02.dilateVec k x) i| <
          (3 : ℝ) ^ (((m : ℤ) : ℝ) + ((k : ℤ) : ℝ)) / 2 := by
      rw [hcoord]
      exact hmul'
    simpa [openCubeAtScale, Ch02.dilateVec, Pi.smul_apply,
      smul_eq_mul, Int.cast_add, r] using hgoal

/-- Dilation commutes with the Caccioppoli core set. -/
theorem caccioppoliCoreSet_dilateCube {d : ℕ} (k : ℤ)
    (Q : TriadicCube d) (x : Vec d) :
    caccioppoliCoreSet (Ch02.dilateCube k Q) (Ch02.dilateVec k x) =
      Ch02.triadicDilationFactor k • caccioppoliCoreSet Q x := by
  let r : ℝ := Ch02.triadicDilationFactor k
  have hscale :
      (Ch02.dilateCube k Q).scale - 2 = (Q.scale - 2) + k := by
    simp [Ch02.dilateCube]
    ring
  rw [caccioppoliCoreSet, Ch02.openCubeSet_dilateCube k Q,
    hscale, openCubeAtScale_dilateVec k (Q.scale - 2) x, caccioppoliCoreSet]
  ext y
  constructor
  · rintro ⟨hyQ, hyx⟩
    rcases hyQ with ⟨zQ, hzQ, rfl⟩
    rcases hyx with ⟨zx, hzx, hzx_eq⟩
    have hz_eq : zQ = zx := by
      ext i
      have hr_ne : Ch02.triadicDilationFactor k ≠ 0 :=
        Ch02.triadicDilationFactor_ne_zero k
      have hi := congrArg (fun y : Vec d => y i) hzx_eq
      simp only [Pi.smul_apply, smul_eq_mul] at hi
      exact (mul_left_cancel₀ hr_ne hi).symm
    refine ⟨zQ, ⟨hzQ, ?_⟩, rfl⟩
    simpa [hz_eq] using hzx
  · rintro ⟨z, ⟨hzQ, hzlocal⟩, rfl⟩
    exact ⟨Set.smul_mem_smul_set hzQ, Set.smul_mem_smul_set hzlocal⟩

/-- Dilation commutes with the boundary Caccioppoli localization window. -/
theorem boundaryPatchWindow_dilateCube {d : ℕ} (k : ℤ)
    (Q : TriadicCube d) (x : Vec d) :
    openCubeAtScale (Ch02.dilateVec k x) ((Ch02.dilateCube k Q).scale - 1) =
      Ch02.triadicDilationFactor k • openCubeAtScale x (Q.scale - 1) := by
  have hscale :
      (Ch02.dilateCube k Q).scale - 1 = (Q.scale - 1) + k := by
    simp [Ch02.dilateCube]
    ring
  rw [hscale, openCubeAtScale_dilateVec]

/-- Cast an `H¹₀` function across definitional set equality. -/
private noncomputable def H10Function.castDomain {d : ℕ}
    {U V : Set (Vec d)} (hUV : U = V) (u : H10Function U) : H10Function V :=
  hUV ▸ u

@[simp] private theorem H10Function.castDomain_toFun {d : ℕ}
    {U V : Set (Vec d)} (hUV : U = V) (u : H10Function U) :
    (H10Function.castDomain hUV u).toH1Function.toFun =
      u.toH1Function.toFun := by
  subst V
  rfl

@[simp] private theorem H10Function.castDomain_apply {d : ℕ}
    {U V : Set (Vec d)} (hUV : U = V) (u : H10Function U) (x : Vec d) :
    (H10Function.castDomain hUV u) x = u x := by
  subst V
  rfl

/-- Localized zero trace is transported by positive dilations, with the
solution normalization `v(y) = r u(r^{-1} y)`. -/
theorem localizedZeroTraceFunctionOn_dilate {d : ℕ} {Ω V Ω' V' : Set (Vec d)}
    {u v : Vec d → ℝ} {r : ℝ} (hr : 0 < r)
    (hΩ' : Ω' = r • Ω) (hV' : V' = r • V)
    (hv : ∀ y : Vec d, v y = r * u (r⁻¹ • y))
    (hu : LocalizedZeroTraceFunctionOn Ω V u) :
    LocalizedZeroTraceFunctionOn Ω' V' v := by
  intro η hη hη_compact hη_sub
  let ζ : Vec d → ℝ := fun x => η (r • x)
  have hζ_smooth : ContDiff ℝ (⊤ : ℕ∞) ζ := by
    simpa [ζ] using! hη.comp (contDiff_const_smul r)
  have hζ_compact : HasCompactSupport ζ := by
    have hr_ne : r ≠ 0 := hr.ne'
    show HasCompactSupport (η ∘ Homeomorph.smulOfNeZero r hr_ne)
    simpa [ζ, Function.comp] using
      hη_compact.comp_homeomorph (Homeomorph.smulOfNeZero r hr_ne)
  have hζ_sub : tsupport ζ ⊆ V := by
    intro x hx
    have hr_ne : r ≠ 0 := hr.ne'
    have hxη : r • x ∈ tsupport η := by
      rw [show ζ = η ∘ Homeomorph.smulOfNeZero r hr_ne by rfl,
        tsupport_comp_eq_preimage η (Homeomorph.smulOfNeZero r hr_ne)] at hx
      exact hx
    have hxV' : r • x ∈ V' := hη_sub hxη
    rw [hV'] at hxV'
    rcases hxV' with ⟨z, hzV, hz⟩
    have hz_eq : z = x := by
      ext i
      have hi := congrArg (fun y : Vec d => y i) hz
      simp only [Pi.smul_apply, smul_eq_mul] at hi
      exact mul_left_cancel₀ hr_ne hi
    simpa [hz_eq] using hzV
  rcases hu ζ hζ_smooth hζ_compact hζ_sub with ⟨w, hw⟩
  have hpre : r⁻¹ • Ω' = Ω := by
    rw [hΩ']
    ext x
    constructor
    · rintro ⟨y, ⟨z, hzΩ, rfl⟩, hxy⟩
      have hx_eq : x = z := by
        simpa [smul_smul, hr.ne'] using hxy.symm
      simpa [hx_eq] using hzΩ
    · intro hx
      refine ⟨r • x, ⟨x, hx, rfl⟩, ?_⟩
      ext i
      simp [Pi.smul_apply, smul_eq_mul, hr.ne']
  let wpre : H10Function (r⁻¹ • Ω') :=
    H10Function.castDomain hpre.symm w
  let wtarget : H10Function Ω' := wpre.unscale (inv_pos.mpr hr)
  have htarget_mem :
      MemH10 Ω' (fun y => η y * u (r⁻¹ • y)) := by
    refine ⟨wtarget, ?_⟩
    funext y
    have hy : r * (r⁻¹) = 1 := by field_simp [hr.ne']
    calc
      wtarget.toH1Function.toFun y =
          wpre.toH1Function.toFun (r⁻¹ • y) := by
        simp [wtarget]
      _ = w.toH1Function.toFun (r⁻¹ • y) := by
        exact congrFun (H10Function.castDomain_toFun hpre.symm w) (r⁻¹ • y)
      _ = ζ (r⁻¹ • y) * u (r⁻¹ • y) := by
        exact congrFun hw (r⁻¹ • y)
      _ = η y * u (r⁻¹ • y) := by
        simp [ζ, smul_smul, hy]
  have hscaled := memH10_smul r htarget_mem
  simpa [hv, mul_assoc, mul_comm, mul_left_comm] using hscaled

/-- Normalized averages are insensitive to a.e. changes of representative. -/
private theorem volumeAverage_eq_of_ae_eq {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volumeMeasureOn U] g) :
    volumeAverage U f = volumeAverage U g := by
  unfold volumeAverage
  congr 1
  exact MeasureTheory.integral_congr_ae hfg

/-- The localized coefficient energy is invariant under the public solution
dilation normalization `v(x) = r u(r^{-1}x)`. -/
theorem localizedCoeffEnergyValue_dilate_eq {d : ℕ} {k : ℤ}
    {Q : TriadicCube d}
    {a : Ch02.CoeffOn (Ch02.cubeDomain Q)}
    {b : Ch02.CoeffOn (Ch02.cubeDomain (Ch02.dilateCube k Q))}
    (hCoeff : Ch02.CoeffOn.IsCubeDilation k a b)
    {u : Ch02.Solution (Ch02.cubeDomain Q) a}
    {v : Ch02.Solution (Ch02.cubeDomain (Ch02.dilateCube k Q)) b}
    (hDilation : Ch02.Solution.IsCubeDilation hCoeff u v)
    {V : Set (Vec d)} (hVsub : V ⊆ openCubeSet Q) :
    localizedCoeffEnergyValue (Ch02.triadicDilationFactor k • V) b v.toH1 =
      localizedCoeffEnergyValue V a u.toH1 := by
  let r : ℝ := Ch02.triadicDilationFactor k
  have hr : 0 < r := by
    dsimp [r]
    exact Ch02.triadicDilationFactor_pos k
  have htarget_subset :
      r • V ⊆ openCubeSet (Ch02.dilateCube k Q) := by
    rw [Ch02.openCubeSet_dilateCube k Q]
    intro y hy
    rcases hy with ⟨z, hzV, rfl⟩
    exact ⟨z, hVsub hzV, rfl⟩
  have hgrad :
      v.toH1.grad =ᵐ[volumeMeasureOn (r • V)]
        fun x => u.toH1.grad (Ch02.undilateVec k x) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset htarget_subset
      hDilation.grad_ae_eq
  have hcoeff :
      b.toCoeffField =ᵐ[volumeMeasureOn (r • V)]
        Ch02.dilateCoeffField k a.toCoeffField :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset htarget_subset
      hCoeff.coeff_ae_eq
  have henergy :
      (fun x : Vec d =>
          vecDot (v.toH1.grad x)
            (matVecMul (symmPart (b.toCoeffField x)) (v.toH1.grad x)))
        =ᵐ[volumeMeasureOn (r • V)]
      fun x =>
          vecDot (u.toH1.grad (Ch02.undilateVec k x))
            (matVecMul
              (symmPart (a.toCoeffField (Ch02.undilateVec k x)))
              (u.toH1.grad (Ch02.undilateVec k x))) := by
    filter_upwards [hgrad, hcoeff] with x hgradx hcoeffx
    simp [hgradx, hcoeffx, Ch02.dilateCoeffField]
  calc
    localizedCoeffEnergyValue (Ch02.triadicDilationFactor k • V) b v.toH1 =
        volumeAverage (r • V)
          (fun x : Vec d =>
            vecDot (v.toH1.grad x)
              (matVecMul (symmPart (b.toCoeffField x)) (v.toH1.grad x))) := by
          simp [localizedCoeffEnergyValue, normalizedSetAverage, r]
    _ =
        volumeAverage (r • V)
          (fun x =>
            vecDot (u.toH1.grad (Ch02.undilateVec k x))
              (matVecMul
                (symmPart (a.toCoeffField (Ch02.undilateVec k x)))
                (u.toH1.grad (Ch02.undilateVec k x)))) :=
          volumeAverage_eq_of_ae_eq henergy
    _ =
        volumeAverage V
          (fun x =>
            vecDot (u.toH1.grad x)
              (matVecMul (symmPart (a.toCoeffField x)) (u.toH1.grad x))) := by
          rw [Ch01.volumeAverage_smul_set_comp_smul_of_pos (d := d) hr V]
          congr 1
          funext x
          simp [Ch02.undilateVec, r, smul_smul, Ch02.triadicDilationFactor_ne_zero k]
    _ = localizedCoeffEnergyValue V a u.toH1 := by
          simp [localizedCoeffEnergyValue, normalizedSetAverage]

/-- Under solution dilation, normalized scalar `L²` on a dilated set gains the
square of the amplitude factor. -/
theorem normalizedL2SqOnSet_dilate_eq {d : ℕ} {k : ℤ}
    {Q : TriadicCube d}
    {a : Ch02.CoeffOn (Ch02.cubeDomain Q)}
    {b : Ch02.CoeffOn (Ch02.cubeDomain (Ch02.dilateCube k Q))}
    {hCoeff : Ch02.CoeffOn.IsCubeDilation k a b}
    {u : Ch02.Solution (Ch02.cubeDomain Q) a}
    {v : Ch02.Solution (Ch02.cubeDomain (Ch02.dilateCube k Q)) b}
    (hDilation : Ch02.Solution.IsCubeDilation hCoeff u v)
    {V : Set (Vec d)} (hVsub : V ⊆ openCubeSet Q) :
    normalizedL2SqOnSet (Ch02.triadicDilationFactor k • V) v.toH1.toFun =
      (Ch02.triadicDilationFactor k) ^ (2 : ℕ) *
        normalizedL2SqOnSet V u.toH1.toFun := by
  let r : ℝ := Ch02.triadicDilationFactor k
  have hr : 0 < r := by
    dsimp [r]
    exact Ch02.triadicDilationFactor_pos k
  have htarget_subset :
      r • V ⊆ openCubeSet (Ch02.dilateCube k Q) := by
    rw [Ch02.openCubeSet_dilateCube k Q]
    intro y hy
    rcases hy with ⟨z, hzV, rfl⟩
    exact ⟨z, hVsub hzV, rfl⟩
  have hvalue :
      v.toH1.toFun =ᵐ[volumeMeasureOn (r • V)]
        fun x => r * u.toH1.toFun (Ch02.undilateVec k x) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset htarget_subset
      (by simpa [r] using! hDilation.value_ae_eq)
  have hsquares :
      (fun x : Vec d => v.toH1.toFun x ^ (2 : ℕ))
        =ᵐ[volumeMeasureOn (r • V)]
      fun x => (r * u.toH1.toFun (Ch02.undilateVec k x)) ^ (2 : ℕ) := by
    exact hvalue.mono fun x hx => by simp [hx]
  calc
    normalizedL2SqOnSet (Ch02.triadicDilationFactor k • V) v.toH1.toFun =
        volumeAverage (r • V) (fun x : Vec d => v.toH1.toFun x ^ (2 : ℕ)) := by
          simp [normalizedL2SqOnSet, normalizedSetAverage, r]
    _ =
        volumeAverage (r • V)
          (fun x => (r * u.toH1.toFun (Ch02.undilateVec k x)) ^ (2 : ℕ)) :=
          volumeAverage_eq_of_ae_eq hsquares
    _ =
        volumeAverage V (fun x => (r * u.toH1.toFun x) ^ (2 : ℕ)) := by
          rw [Ch01.volumeAverage_smul_set_comp_smul_of_pos (d := d) hr V]
          congr 1
          funext x
          simp [Ch02.undilateVec, r, smul_smul, Ch02.triadicDilationFactor_ne_zero k]
    _ = r ^ (2 : ℕ) *
        volumeAverage V (fun x => u.toH1.toFun x ^ (2 : ℕ)) := by
          calc
            volumeAverage V (fun x => (r * u.toH1.toFun x) ^ (2 : ℕ)) =
                volumeAverage V
                  ((r ^ (2 : ℕ)) • fun x => u.toH1.toFun x ^ (2 : ℕ)) := by
              congr 1
              funext x
              simp [Pi.smul_apply, smul_eq_mul]
              ring
            _ = r ^ (2 : ℕ) *
                volumeAverage V (fun x => u.toH1.toFun x ^ (2 : ℕ)) :=
              volumeAverage_smul V (r ^ (2 : ℕ))
                (fun x => u.toH1.toFun x ^ (2 : ℕ))
    _ =
        (Ch02.triadicDilationFactor k) ^ (2 : ℕ) *
          normalizedL2SqOnSet V u.toH1.toFun := by
          simp [normalizedL2SqOnSet, normalizedSetAverage, r]

/-- The solution-amplitude square for normalization by `-Q.scale` is exactly
the explicit scale factor in the public Caccioppoli RHS. -/
theorem triadicDilationFactor_neg_scale_sq {d : ℕ} (Q : TriadicCube d) :
    (Ch02.triadicDilationFactor (-Q.scale)) ^ (2 : ℕ) =
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) := by
  have hcast : (((-2 * Q.scale : ℤ) : ℝ)) =
      -2 * (((Q.scale : ℤ) : ℝ)) := by
    norm_num
  have hrpow :
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) =
        (3 : ℝ) ^ (-2 * Q.scale) := by
    rw [← hcast]
    exact Real.rpow_intCast (3 : ℝ) (-2 * Q.scale)
  rw [hrpow]
  simp [Ch02.triadicDilationFactor]
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  ring

/-- The public normalized cube average can be evaluated on the open cube:
the half-open boundary is null. -/
private theorem normalizedAverage_eq_volumeAverage_open {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    Ch01.Legacy.normalizedAverage Q f = volumeAverage (openCubeSet Q) f := by
  calc
    Ch01.Legacy.normalizedAverage Q f = volumeAverage (cubeSet Q) f := by
      rw [Ch01.Legacy.normalizedAverage]
      exact (volumeAverage_cubeSet_eq_cubeAverage Q f).symm
    _ = volumeAverage (openCubeSet Q) f :=
      ScalarCanonicalMaximizer.volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube Q f

/-- The cube average of a dilated solution scales by the solution-amplitude
factor. -/
theorem normalizedAverage_dilate_solution_eq {d : ℕ} {k : ℤ}
    {Q : TriadicCube d}
    {a : Ch02.CoeffOn (Ch02.cubeDomain Q)}
    {b : Ch02.CoeffOn (Ch02.cubeDomain (Ch02.dilateCube k Q))}
    {hCoeff : Ch02.CoeffOn.IsCubeDilation k a b}
    {u : Ch02.Solution (Ch02.cubeDomain Q) a}
    {v : Ch02.Solution (Ch02.cubeDomain (Ch02.dilateCube k Q)) b}
    (hDilation : Ch02.Solution.IsCubeDilation hCoeff u v) :
    Ch01.Legacy.normalizedAverage (Ch02.dilateCube k Q) v.toH1.toFun =
      Ch02.triadicDilationFactor k * Ch01.Legacy.normalizedAverage Q u.toH1.toFun := by
  let r : ℝ := Ch02.triadicDilationFactor k
  have hr : 0 < r := by
    dsimp [r]
    exact Ch02.triadicDilationFactor_pos k
  calc
    Ch01.Legacy.normalizedAverage (Ch02.dilateCube k Q) v.toH1.toFun =
        volumeAverage (openCubeSet (Ch02.dilateCube k Q)) v.toH1.toFun :=
      normalizedAverage_eq_volumeAverage_open (Ch02.dilateCube k Q) v.toH1.toFun
    _ =
        volumeAverage (openCubeSet (Ch02.dilateCube k Q))
          (fun x => r * u.toH1.toFun (Ch02.undilateVec k x)) := by
          exact volumeAverage_eq_of_ae_eq (by simpa [r] using hDilation.value_ae_eq)
    _ =
        volumeAverage (r • openCubeSet Q)
          (fun x => r * u.toH1.toFun (Ch02.undilateVec k x)) := by
          rw [Ch02.openCubeSet_dilateCube]
    _ =
        volumeAverage (openCubeSet Q) (fun x => r * u.toH1.toFun x) := by
          rw [Ch01.volumeAverage_smul_set_comp_smul_of_pos (d := d) hr]
          congr 1
          funext x
          simp [Ch02.undilateVec, r, smul_smul, Ch02.triadicDilationFactor_ne_zero k]
    _ = r * volumeAverage (openCubeSet Q) u.toH1.toFun := by
          simpa [smul_eq_mul] using!
            volumeAverage_smul (openCubeSet Q) r u.toH1.toFun
    _ = Ch02.triadicDilationFactor k *
        Ch01.Legacy.normalizedAverage Q u.toH1.toFun := by
          rw [normalizedAverage_eq_volumeAverage_open Q u.toH1.toFun]

/-- The centered parent `L²` oscillation scales with the same amplitude-square
factor as the uncentered parent `L²` term. -/
theorem interiorCaccioppoliParentOscillationL2Sq_dilate_eq {d : ℕ} {k : ℤ}
    {Q : TriadicCube d} {A B : CoeffFamily d}
    {hCoeff : Ch02.CoeffOn.IsCubeDilation k (A.coeffOn Q)
      (B.coeffOn (Ch02.dilateCube k Q))}
    {u : CubeSolution Q A}
    {v : CubeSolution (Ch02.dilateCube k Q) B}
    (hDilation : Ch02.Solution.IsCubeDilation hCoeff u v) :
    interiorCaccioppoliParentOscillationL2Sq (Ch02.dilateCube k Q) B v =
      (Ch02.triadicDilationFactor k) ^ (2 : ℕ) *
        interiorCaccioppoliParentOscillationL2Sq Q A u := by
  let r : ℝ := Ch02.triadicDilationFactor k
  have hr : 0 < r := by
    dsimp [r]
    exact Ch02.triadicDilationFactor_pos k
  have havg :
      Ch01.Legacy.normalizedAverage (Ch02.dilateCube k Q) v.toH1.toFun =
        r * Ch01.Legacy.normalizedAverage Q u.toH1.toFun := by
    simpa [r] using normalizedAverage_dilate_solution_eq hDilation
  have hvalue :
      v.toH1.toFun =ᵐ[volumeMeasureOn (openCubeSet (Ch02.dilateCube k Q))]
        fun x => r * u.toH1.toFun (Ch02.undilateVec k x) := by
    simpa [r] using hDilation.value_ae_eq
  have hsquares :
      (fun x : Vec d =>
          (v.toH1.toFun x -
            Ch01.Legacy.normalizedAverage (Ch02.dilateCube k Q) v.toH1.toFun) ^ (2 : ℕ))
        =ᵐ[volumeMeasureOn (openCubeSet (Ch02.dilateCube k Q))]
      fun x =>
          (r * (u.toH1.toFun (Ch02.undilateVec k x) -
            Ch01.Legacy.normalizedAverage Q u.toH1.toFun)) ^ (2 : ℕ) := by
    filter_upwards [hvalue] with x hx
    rw [hx, havg]
    ring
  calc
    interiorCaccioppoliParentOscillationL2Sq (Ch02.dilateCube k Q) B v =
        volumeAverage (openCubeSet (Ch02.dilateCube k Q))
          (fun x : Vec d =>
            (v.toH1.toFun x -
              Ch01.Legacy.normalizedAverage (Ch02.dilateCube k Q) v.toH1.toFun) ^ (2 : ℕ)) := by
          simp [interiorCaccioppoliParentOscillationL2Sq,
            normalizedL2SqOnSet, normalizedSetAverage]
    _ =
        volumeAverage (openCubeSet (Ch02.dilateCube k Q))
          (fun x =>
            (r * (u.toH1.toFun (Ch02.undilateVec k x) -
              Ch01.Legacy.normalizedAverage Q u.toH1.toFun)) ^ (2 : ℕ)) :=
          volumeAverage_eq_of_ae_eq hsquares
    _ =
        volumeAverage (r • openCubeSet Q)
          (fun x =>
            (r * (u.toH1.toFun (Ch02.undilateVec k x) -
              Ch01.Legacy.normalizedAverage Q u.toH1.toFun)) ^ (2 : ℕ)) := by
          rw [Ch02.openCubeSet_dilateCube]
    _ =
        volumeAverage (openCubeSet Q)
          (fun x =>
            (r * (u.toH1.toFun x -
              Ch01.Legacy.normalizedAverage Q u.toH1.toFun)) ^ (2 : ℕ)) := by
          rw [Ch01.volumeAverage_smul_set_comp_smul_of_pos (d := d) hr]
          congr 1
          funext x
          simp [Ch02.undilateVec, r, smul_smul, Ch02.triadicDilationFactor_ne_zero k]
    _ =
        r ^ (2 : ℕ) *
          volumeAverage (openCubeSet Q)
            (fun x =>
              (u.toH1.toFun x -
                Ch01.Legacy.normalizedAverage Q u.toH1.toFun) ^ (2 : ℕ)) := by
          calc
            volumeAverage (openCubeSet Q)
              (fun x =>
                (r * (u.toH1.toFun x -
                  Ch01.Legacy.normalizedAverage Q u.toH1.toFun)) ^ (2 : ℕ)) =
                volumeAverage (openCubeSet Q)
                  ((r ^ (2 : ℕ)) • fun x =>
                    (u.toH1.toFun x -
                      Ch01.Legacy.normalizedAverage Q u.toH1.toFun) ^ (2 : ℕ)) := by
              congr 1
              funext x
              simp [Pi.smul_apply, smul_eq_mul]
              ring
            _ =
                r ^ (2 : ℕ) *
                  volumeAverage (openCubeSet Q)
                    (fun x =>
                      (u.toH1.toFun x -
                        Ch01.Legacy.normalizedAverage Q u.toH1.toFun) ^ (2 : ℕ)) :=
              volumeAverage_smul (openCubeSet Q) (r ^ (2 : ℕ))
                (fun x =>
                  (u.toH1.toFun x -
                  Ch01.Legacy.normalizedAverage Q u.toH1.toFun) ^ (2 : ℕ))
    _ =
        (Ch02.triadicDilationFactor k) ^ (2 : ℕ) *
          interiorCaccioppoliParentOscillationL2Sq Q A u := by
          simp [interiorCaccioppoliParentOscillationL2Sq,
            normalizedL2SqOnSet, normalizedSetAverage, r]

/-- The Caccioppoli scalar prefactor under normalization to scale zero.

The multiscale quantities are invariant under the public Chapter 2 dilation
relation, while the explicit `3^{-2m}` factor is exactly the scale conversion
left in the note-facing statement. -/
theorem caccioppoliPrefactor_dilate_neg_scale {d : ℕ} [NeZero d]
    (hmulti : Ch02.MultiscaleDilationTheory d)
    {Q : TriadicCube d} {a b : CoeffFamily d} {C s t : ℝ}
    (hFam : Ch02.TriadicCoeffFamily.IsDilation (-Q.scale) a b) :
    caccioppoliPrefactor C Q a s t =
      Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
        caccioppoliPrefactor C (Ch02.dilateCube (-Q.scale) Q) b s t := by
  unfold caccioppoliPrefactor
  rw [hmulti.ThetaRatio_dilate hFam Q s t,
    hmulti.LambdaS_dilate hFam Q s]
  have hscale0 :
      Real.rpow (3 : ℝ)
          (-2 * ((((Ch02.dilateCube (-Q.scale) Q).scale : ℤ) : ℝ))) =
        1 := by
    simp
  rw [hscale0]
  ring

/-- A boundary datum transported to the normalized scale-zero cube.

The inequalities are intentionally oriented for the Caccioppoli reduction:
the old core energy is controlled by the normalized core energy, and the
normalized RHS is controlled by the original public RHS. -/
private structure BoundaryCaccioppoliDilationWitness {d : ℕ} [NeZero d]
    {Q : TriadicCube d} {a : CoeffFamily d} {x : Vec d}
    (u : BoundaryCaccioppoliDatum Q a x) where
  normalizedCoeff : CoeffFamily d
  coeff_isDilation :
    Ch02.TriadicCoeffFamily.IsDilation (-Q.scale) a normalizedCoeff
  normalizedDatum :
    BoundaryCaccioppoliDatum (Ch02.dilateCube (-Q.scale) Q) normalizedCoeff
      (Ch02.dilateVec (-Q.scale) x)
  coreEnergy_le :
    boundaryCaccioppoliCoreEnergy u ≤
      boundaryCaccioppoliCoreEnergy normalizedDatum
  rhs_le :
    ∀ {C s t : ℝ}, 0 < C → 0 < s → 0 < t → s + t < 1 →
      boundaryCaccioppoliRHS C s t normalizedDatum ≤
        boundaryCaccioppoliRHS C s t u

/-- An interior solution transported to the normalized scale-zero cube. -/
private structure InteriorCaccioppoliDilationWitness {d : ℕ} [NeZero d]
    {Q : TriadicCube d} {a : CoeffFamily d}
    (u : CubeSolution Q a) where
  normalizedCoeff : CoeffFamily d
  coeff_isDilation :
    Ch02.TriadicCoeffFamily.IsDilation (-Q.scale) a normalizedCoeff
  normalizedSolution :
    CubeSolution (Ch02.dilateCube (-Q.scale) Q) normalizedCoeff
  coreEnergy_le :
    interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
      interiorCaccioppoliCoreEnergy (Ch02.dilateCube (-Q.scale) Q)
        normalizedCoeff (cubeCenter (Ch02.dilateCube (-Q.scale) Q))
        normalizedSolution
  rhs_le :
    ∀ {C s t : ℝ}, 0 < C → 0 < s → 0 < t → s + t < 1 →
      interiorCaccioppoliRHS C (Ch02.dilateCube (-Q.scale) Q)
          normalizedCoeff s t normalizedSolution ≤
        interiorCaccioppoliRHS C Q a s t u

/-- Boundary Caccioppoli data have a concrete normalized dilation witness. -/
private noncomputable def boundaryCaccioppoliDilationWitness {d : ℕ} [NeZero d]
    {Q : TriadicCube d} {a : CoeffFamily d} {x : Vec d}
    (u : BoundaryCaccioppoliDatum Q a x) :
    BoundaryCaccioppoliDilationWitness u := by
  let k : ℤ := -Q.scale
  let r : ℝ := Ch02.triadicDilationFactor k
  let b : CoeffFamily d := Ch02.TriadicCoeffFamily.dilate k a
  have hr : 0 < r := by
    dsimp [r, k]
    exact Ch02.triadicDilationFactor_pos (-Q.scale)
  have hFam : Ch02.TriadicCoeffFamily.IsDilation k a b :=
    Ch02.TriadicCoeffFamily.isDilation_dilate k a
  have hCoeff :
      Ch02.CoeffOn.IsCubeDilation k (a.coeffOn Q)
        (b.coeffOn (Ch02.dilateCube k Q)) :=
    hFam Q
  let uSol : Ch02.Solution (Ch02.cubeDomain Q) (a.coeffOn Q) :=
    { toH1 := u.toH1
      isHarmonic := u.isHarmonic }
  let vPack := Ch02.Solution.dilate hCoeff uSol
  let vSol : Ch02.Solution (Ch02.cubeDomain (Ch02.dilateCube k Q))
      (b.coeffOn (Ch02.dilateCube k Q)) := vPack.toSolution
  have hvalue_pointwise :
      ∀ y : Vec d, vSol.toH1.toFun y =
        r * u.toH1.toFun (r⁻¹ • y) := by
    intro y
    simp [vSol, vPack, uSol, Ch02.Solution.dilate, H1Function.dilateSet,
      r, k]
  let vDatum : BoundaryCaccioppoliDatum (Ch02.dilateCube k Q) b
      (Ch02.dilateVec k x) :=
    { toH1 := vSol.toH1
      isHarmonic := vSol.isHarmonic
      zeroTraceOnBoundaryPatch := by
        have hΩ :
            (Ch02.cubeDomain (Ch02.dilateCube k Q) : Set (Vec d)) =
              r • (Ch02.cubeDomain Q : Set (Vec d)) := by
          simpa [Ch02.cubeDomain_coe, r] using Ch02.openCubeSet_dilateCube k Q
        have hV :
            openCubeAtScale (Ch02.dilateVec k x)
                ((Ch02.dilateCube k Q).scale - 1) =
              r • openCubeAtScale x (Q.scale - 1) := by
          simpa [r] using boundaryPatchWindow_dilateCube k Q x
        exact
          localizedZeroTraceFunctionOn_dilate
            (Ω := (Ch02.cubeDomain Q : Set (Vec d)))
            (V := openCubeAtScale x (Q.scale - 1))
            (Ω' := (Ch02.cubeDomain (Ch02.dilateCube k Q) : Set (Vec d)))
            (V' := openCubeAtScale (Ch02.dilateVec k x)
              ((Ch02.dilateCube k Q).scale - 1))
            (u := u.toH1.toFun) (v := vSol.toH1.toFun)
            hr hΩ hV hvalue_pointwise u.zeroTraceOnBoundaryPatch }
  refine
    { normalizedCoeff := b
      coeff_isDilation := by
        simpa [k, b] using hFam
      normalizedDatum := by
        simpa [k, b] using vDatum
      coreEnergy_le := ?_
      rhs_le := ?_ }
  · have hcore_sub : caccioppoliCoreSet Q x ⊆ openCubeSet Q := fun y hy => hy.1
    have henergy :=
      localizedCoeffEnergyValue_dilate_eq hCoeff vPack.isDilation
        (V := caccioppoliCoreSet Q x) hcore_sub
    have hcore_geom :
        caccioppoliCoreSet (Ch02.dilateCube k Q) (Ch02.dilateVec k x) =
          r • caccioppoliCoreSet Q x := by
      simpa [r] using caccioppoliCoreSet_dilateCube k Q x
    have heq :
        boundaryCaccioppoliCoreEnergy vDatum =
          boundaryCaccioppoliCoreEnergy u := by
      simpa [boundaryCaccioppoliCoreEnergy, vDatum, uSol, vSol, r, hcore_geom]
        using henergy
    simpa [vDatum, k, b] using le_of_eq heq.symm
  · intro C s t hC hs ht hst
    have hparent :=
      normalizedL2SqOnSet_dilate_eq vPack.isDilation
        (V := openCubeSet Q) (fun y hy => hy)
    have hopen :
        openCubeSet (Ch02.dilateCube k Q) = r • openCubeSet Q := by
      simpa [r] using Ch02.openCubeSet_dilateCube k Q
    have hparent_eq :
        boundaryCaccioppoliParentL2Sq vDatum =
          r ^ (2 : ℕ) * boundaryCaccioppoliParentL2Sq u := by
      simpa [boundaryCaccioppoliParentL2Sq, normalizedL2SqOnSet,
        normalizedSetAverage, vDatum, uSol, vSol, r, hopen] using hparent
    have hpref :=
      caccioppoliPrefactor_dilate_neg_scale (Ch02.multiscaleDilationTheory d)
        (Q := Q) (a := a) (b := b) (C := C) (s := s) (t := t)
        (by simpa [k, b] using hFam)
    have hsq :
        r ^ (2 : ℕ) =
          Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) := by
      simpa [r, k] using triadicDilationFactor_neg_scale_sq Q
    have heq :
        boundaryCaccioppoliRHS C s t vDatum =
          boundaryCaccioppoliRHS C s t u := by
      unfold boundaryCaccioppoliRHS
      rw [hparent_eq, hsq]
      rw [hpref]
      ring
    simpa [vDatum, k, b] using le_of_eq heq

private theorem interiorCaccioppoliRHS_dilate_eq_of_parentOscillation
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a b : CoeffFamily d}
    (u : CubeSolution Q a) (v : CubeSolution (Ch02.dilateCube (-Q.scale) Q) b)
    (hFam : Ch02.TriadicCoeffFamily.IsDilation (-Q.scale) a b)
    (hosc : interiorCaccioppoliParentOscillationL2Sq (Ch02.dilateCube (-Q.scale) Q) b v =
      (Ch02.triadicDilationFactor (-Q.scale)) ^ (2 : ℕ) *
        interiorCaccioppoliParentOscillationL2Sq Q a u)
    (C s t : ℝ) :
    interiorCaccioppoliRHS C (Ch02.dilateCube (-Q.scale) Q) b s t v =
      interiorCaccioppoliRHS C Q a s t u := by
  have hpref :=
    caccioppoliPrefactor_dilate_neg_scale (Ch02.multiscaleDilationTheory d)
      (Q := Q) (a := a) (b := b) (C := C) (s := s) (t := t) hFam
  have hsq := triadicDilationFactor_neg_scale_sq Q
  unfold interiorCaccioppoliRHS
  rw [hosc, hsq]
  rw [hpref]
  ring

/-- Interior cube solutions have a concrete normalized dilation witness. -/
private noncomputable def interiorCaccioppoliDilationWitness {d : ℕ} [NeZero d]
    {Q : TriadicCube d} {a : CoeffFamily d} (u : CubeSolution Q a) :
    InteriorCaccioppoliDilationWitness u := by
  let k : ℤ := -Q.scale
  let r : ℝ := Ch02.triadicDilationFactor k
  let b : CoeffFamily d := Ch02.TriadicCoeffFamily.dilate k a
  have hFam : Ch02.TriadicCoeffFamily.IsDilation k a b :=
    Ch02.TriadicCoeffFamily.isDilation_dilate k a
  have hCoeff :
      Ch02.CoeffOn.IsCubeDilation k (a.coeffOn Q)
        (b.coeffOn (Ch02.dilateCube k Q)) :=
    hFam Q
  let vPack := Ch02.Solution.dilate hCoeff u
  let vSol : CubeSolution (Ch02.dilateCube k Q) b := vPack.toSolution
  refine
    { normalizedCoeff := b
      coeff_isDilation := by
        simpa [k, b] using hFam
      normalizedSolution := by
        simpa [k, b] using vSol
      coreEnergy_le := ?_
      rhs_le := ?_ }
  · have hcore_sub :
        caccioppoliCoreSet Q (cubeCenter Q) ⊆ openCubeSet Q := fun y hy => hy.1
    have henergy :=
      localizedCoeffEnergyValue_dilate_eq hCoeff vPack.isDilation
        (V := caccioppoliCoreSet Q (cubeCenter Q)) hcore_sub
    have hcenter :
        cubeCenter (Ch02.dilateCube k Q) = Ch02.dilateVec k (cubeCenter Q) :=
      cubeCenter_dilateCube k Q
    have hcore_geom :
        caccioppoliCoreSet (Ch02.dilateCube k Q)
            (cubeCenter (Ch02.dilateCube k Q)) =
          r • caccioppoliCoreSet Q (cubeCenter Q) := by
      rw [hcenter]
      simpa [r] using caccioppoliCoreSet_dilateCube k Q (cubeCenter Q)
    have heq :
        interiorCaccioppoliCoreEnergy (Ch02.dilateCube k Q) b
            (cubeCenter (Ch02.dilateCube k Q)) vSol =
          interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u := by
      simpa [interiorCaccioppoliCoreEnergy, vSol, r, hcore_geom]
        using henergy
    simpa [vSol, k, b] using le_of_eq heq.symm
  · intro C s t hC hs ht hst
    have hosc :=
      interiorCaccioppoliParentOscillationL2Sq_dilate_eq
        (A := a) (B := b) (Q := Q) vPack.isDilation
    have heq := interiorCaccioppoliRHS_dilate_eq_of_parentOscillation
      u vSol (by simpa [k, b] using hFam) hosc C s t
    simpa [vSol, k, b] using le_of_eq heq

/-- Fully proved public coarse Caccioppoli theorem package for arbitrary
triadic scales.  The scale normalization is discharged internally by concrete
dilation witnesses, so no transport bridge appears in the public API. -/
theorem coarseCaccioppoliTheory
    (d : ℕ) [NeZero d] : CoarseCaccioppoliTheory d := by
  rcases (coarseCaccioppoliScaleZeroTheory d).exists_constant with
    ⟨C, hCpos, hboundary₀, hinterior₀⟩
  refine ⟨⟨C, hCpos, ?_, ?_⟩⟩
  · intro Q a s t x u hs ht hst hx
    let w := boundaryCaccioppoliDilationWitness u
    have hscale0 : (Ch02.dilateCube (-Q.scale) Q).scale = 0 := by simp
    have hx0 :
        Ch02.dilateVec (-Q.scale) x ∈
          openCubeSet (Ch02.dilateCube (-Q.scale) Q) :=
      Ch02.dilateVec_mem_openCubeSet_dilateCube (-Q.scale) hx
    exact
      w.coreEnergy_le.trans
        ((hboundary₀ w.normalizedDatum hs ht hst hx0 hscale0).trans
          (w.rhs_le hCpos hs ht hst))
  · intro Q a s t u hs ht hst
    let w := interiorCaccioppoliDilationWitness u
    have hscale0 : (Ch02.dilateCube (-Q.scale) Q).scale = 0 := by simp
    exact
      w.coreEnergy_le.trans
        ((hinterior₀ w.normalizedSolution hs ht hst hscale0).trans
          (w.rhs_le hCpos hs ht hst))

end

end Ch03
end Book
end Homogenization
