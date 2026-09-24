/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZInputs
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.RawCZBridge
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionInputCast

/-! # Distributional pairing for the completed pressure operator

Continuous dual pairings extend the L² identity from the dense intersection
to every L^(3/2) input. Compact support is required only of the test function,
not of a chosen representative of an Lp class.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Endgame

def lpPairingWith {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q]
    (g : Lp ℝ q (volume : Measure Vec3)) :
    Lp ℝ p (volume : Measure Vec3) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ g).comp
    (ContinuousLinearMap.lpPairing volume p q (ContinuousLinearMap.mul ℝ ℝ))

private lemma lpPairingWith_apply {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q]
    (g : Lp ℝ q (volume : Measure Vec3)) (f : Lp ℝ p (volume : Measure Vec3)) :
    lpPairingWith g f = ∫ x, f x * g x := by
  change (ContinuousLinearMap.lpPairing volume p q (ContinuousLinearMap.mul ℝ ℝ) f) g = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  rfl

/-- A distributional pairing on the L² intersection extends to every Lp input. -/
theorem lpExtension_pairing_of_l2_identity
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C)
    {lap rhs : Vec3 → ℝ} (hlap : MemLp lap q volume) (hrhs : MemLp rhs q volume)
    (hidentity : ∀ v : Lp ℝ p (volume : Measure Vec3),
      MemLp (v : Vec3 → ℝ) (2 : ℝ≥0∞) volume →
      ∫ x, h.T (v : Vec3 → ℝ) x * lap x = ∫ x, (v : Vec3 → ℝ) x * rhs x)
    {f : Vec3 → ℝ} (hf : MemLp f p volume) :
    ∫ x, lpExtensionRepresentative hp h f x * lap x =
      ∫ x, f x * rhs x := by
  let s : Set (Lp ℝ p (volume : Measure Vec3)) :=
    {v | MemLp (v : Vec3 → ℝ) (2 : ℝ≥0∞) volume}
  have hs : Dense s := by
    apply (MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (F := ℝ) (p := p) (μ := (volume : Measure Vec3)) hp).mono
    rintro v ⟨F, hvF, hFc, hF⟩
    exact (memLp_congr_ae hvF).mpr (hF.continuous.memLp_of_hasCompactSupport hFc)
  let lapLp : Lp ℝ q (volume : Measure Vec3) := hlap.toLp lap
  let rhsLp : Lp ℝ q (volume : Measure Vec3) := hrhs.toLp rhs
  let left : Lp ℝ p (volume : Measure Vec3) →L[ℝ] ℝ :=
    (lpPairingWith (p := p) (q := q) lapLp).comp (lpExtensionCore hp h)
  let right : Lp ℝ p (volume : Measure Vec3) →L[ℝ] ℝ :=
    lpPairingWith (p := p) (q := q) rhsLp
  have hEq : left = right := by
    apply ContinuousLinearMap.ext
    intro u
    have hfun : (fun v : Lp ℝ p (volume : Measure Vec3) => left v) =
        (fun v => right v) := by
      apply Continuous.ext_on hs
        left.continuous right.continuous
      intro v hv
      have hv₂ : MemLp (v : Vec3 → ℝ) (2 : ℝ≥0∞) volume := hv
      have hTae : (lpExtensionCore hp h v : Vec3 → ℝ) =ᵐ[volume]
          h.T (v : Vec3 → ℝ) := by
        have hcore := lpExtensionRepresentative_ae_eq_core hp h (Lp.memLp v)
        rw [Lp.toLp_coeFn] at hcore
        exact hcore.symm.trans (lpExtensionRepresentative_ae_eq_T hp h (Lp.memLp v) hv₂)
      have hleft : left v = ∫ x, h.T (v : Vec3 → ℝ) x * lap x := by
        change (lpPairingWith lapLp) (lpExtensionCore hp h v) = _
        rw [lpPairingWith_apply]
        apply integral_congr_ae
        filter_upwards [hTae, hlap.coeFn_toLp] with x hx hy
        rw [hx, hy]
      have hright : right v = ∫ x, (v : Vec3 → ℝ) x * rhs x := by
        change (lpPairingWith rhsLp) v = _
        rw [lpPairingWith_apply]
        apply integral_congr_ae
        filter_upwards [hrhs.coeFn_toLp] with x hx
        rw [hx]
      rw [hleft, hright]
      exact hidentity v hv
    exact congrFun hfun u
  have hpair : left (hf.toLp f) = right (hf.toLp f) := by rw [hEq]
  have hpair' : (lpPairingWith lapLp) (lpExtensionCore hp h (hf.toLp f)) =
      (lpPairingWith rhsLp) (hf.toLp f) := hpair
  have hrep : lpExtensionRepresentative hp h f =ᵐ[volume]
      (lpExtensionCore hp h (hf.toLp f) : Vec3 → ℝ) :=
    lpExtensionRepresentative_ae_eq_core hp h hf
  calc
    ∫ x, lpExtensionRepresentative hp h f x * lap x =
        ∫ x, (lpExtensionCore hp h (hf.toLp f) : Vec3 → ℝ) x * lap x := by
      apply integral_congr_ae
      filter_upwards [hrep] with x hx
      rw [hx]
    _ = (lpPairingWith lapLp) (lpExtensionCore hp h (hf.toLp f)) := by
      rw [lpPairingWith_apply]
      apply integral_congr_ae
      filter_upwards [hlap.coeFn_toLp] with x hx
      rw [hx]
    _ = (lpPairingWith rhsLp) (hf.toLp f) := hpair'
    _ = ∫ x, (hf.toLp f : Vec3 → ℝ) x * rhs x := by
      rw [lpPairingWith_apply]
      apply integral_congr_ae
      filter_upwards [hrhs.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x, f x * rhs x := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]

private theorem derivative_compact {f : Vec3 → ℝ}
    (hf : HasCompactSupport f) (i : Fin 3) : HasCompactSupport (spatialDeriv f i) := by
  exact hf.fderiv_apply (𝕜 := ℝ) (basisVec i)

/-- The actual completed pressure operator satisfies the distributional
Hessian identity for every L^(3/2) input and smooth compactly supported test. -/
theorem rieszSecondP1Extension_distributional_identity {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {f ψ : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, rieszSecondP1ExtensionOperator hL2 hWeak11 f x * spatialLaplacian ψ x) =
      ∫ x, f x * mixedSecond ψ i j x := by
  let : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  let : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩
  let : ENNReal.HolderConjugate (ENNReal.ofReal (3 / 2 : ℝ)) (ENNReal.ofReal 3) :=
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      Real.HolderConjugate (3 / 2 : ℝ) 3).ennrealOfReal
  have hlapc : HasCompactSupport (spatialLaplacian ψ) := by
    change HasCompactSupport (fun x => ∑ k : Fin 3, spatialDeriv (spatialDeriv ψ k) k x)
    convert
      ((derivative_compact (derivative_compact hψc 0) 0).add
        ((derivative_compact (derivative_compact hψc 1) 1).add
          (derivative_compact (derivative_compact hψc 2) 2))) using 1
    funext x
    simp [Fin.sum_univ_succ, Pi.add_apply]
  have hlap : MemLp (spatialLaplacian ψ) (ENNReal.ofReal (3 : ℝ)) volume :=
    (contDiff_spatialLaplacian_smooth hψ).continuous.memLp_of_hasCompactSupport hlapc
  have hrhs : MemLp (mixedSecond ψ i j) (ENNReal.ofReal (3 : ℝ)) volume :=
    (contDiff_mixedSecond_smooth hψ i j).continuous.memLp_of_hasCompactSupport
      (derivative_compact (derivative_compact hψc j) i)
  apply lpExtension_pairing_of_l2_identity (by norm_num)
    (rieszSecondP1ExtensionInput hL2 hWeak11) hlap hrhs ?_ hf
  intro v hv
  simp only [rieszSecondP1ExtensionInput]
  dsimp only [czP1Constant, id]
  rw [CKN.Foundation.Euclidean.lpExtensionInput_mp_T (by norm_num [czP1Constant])]
  exact raw_rieszSecond_distributional_identity hL2 hv hψ hψc


end CKN.Core.Endgame
