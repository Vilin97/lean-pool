/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LeviConvexity.Independence
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LeviConvexity.Necessity

/-!
# Peak functions at strictly Levi convex boundary points

A boundary point `p` of an open set `U` is strictly Levi pseudoconvex if the Levi form of a
local defining function is positive definite on the complex tangent space. Adding a multiple of
the square of the defining function makes the Levi form positive definite on the whole space at
`p`, by a compactness argument on the unit sphere. The Levi polynomial of the modified defining
function `\tilde ρ` is the holomorphic quadratic function `F(z) = ∂\tilde ρ(p)(z - p) + Q(z -
p)`, where `Q` is the complex quadratic part of the real Hessian; the second-order Taylor
expansion gives `Re F(z) = \tilde ρ(z) - Lev \tilde ρ(p, z - p) + o(‖z - p‖²)`, so `Re F < 0` on
the domain near `p`, except at `p` where `F` vanishes. The reciprocal `1 / F` is then
holomorphic on the domain near `p` and unbounded at `p`: a local holomorphic blow-up function.
Exponentiating `F` gives a normalized local peak function with value one at `p` and modulus less
than one elsewhere on the closed side.

References: [Range][Range1986] (1986), Chapter II, Lemma 2.13, Proposition 2.16 and Theorem
2.15; [Fritzsche–Grauert][FritzscheGrauert2002] (2002), Chapter II, Section 4.

## Main definitions

* `IsStrictlyLeviPseudoconvexAt`: The strict Levi condition at a boundary point: the Levi form of
  every local defining function is positive definite on the complex tangent space.
* `leviBilinear`: The complex bilinear part of a real bilinear form on a complex space.

## Main results

* `exists_leviForm_add_normSq_ge`: **Positive definiteness after modification.** If the Levi form is
  positive definite on the complex tangent space at `p`, then adding a large multiple of the squared
  modulus of the complex-linear part of the derivative makes it positive definite on the whole
  space.
* `IsLocalDefiningFunction.exists_holomorphic_support`: **Levi polynomial as a peak function
  ([Range][Range1986], Proposition 2.16).** At a boundary point with positive definite Levi form on
  the complex tangent space there is an entire holomorphic function `F` vanishing at `p` whose real
  part is negative at all nearby points where the defining function is nonpositive, except at `p`.
* `IsLocalDefiningFunction.exists_peak`: **Normalized local peak function.** Exponentiating a
  holomorphic supporting function has value one at the boundary point and modulus strictly less than
  one at every other nearby point on the closed side of the defining function.
* `IsLocalDefiningFunction.exists_tendsto_norm_atTop`: **Local holomorphic blow-up.** At a strictly
  Levi convex boundary point of an open set there is a holomorphic function on the set near the
  point whose modulus tends to infinity at the point.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
-/

public noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section StrictDefinition

/-- The strict Levi condition at a boundary point: the Levi form of every local defining function is
positive definite on the complex tangent space. -/
@[expose] def IsStrictlyLeviPseudoconvexAt (U : Set E) (p : E) : Prop :=
  ∀ (ρ : E → ℝ) (V : Set E), IsLocalDefiningFunction U p ρ V →
    ∀ w, IsComplexTangent ρ p w → w ≠ 0 → 0 < leviForm ρ p w

/-- The strict Levi condition can be checked on one defining function. -/
theorem isStrictlyLeviPseudoconvexAt_iff_of_defining {U : Set E} {p : E} {ρ : E → ℝ} {V : Set E}
    (h : IsLocalDefiningFunction U p ρ V) :
    IsStrictlyLeviPseudoconvexAt U p ↔ ∀ w, IsComplexTangent ρ p w → w ≠ 0 → 0 < leviForm ρ p w :=
      by
  constructor
  · intro hL w hw hw0
    exact hL ρ V h w hw hw0
  · intro hL ρ' V' h' w hw hw0
    obtain ⟨c, hc, hlev⟩ := h'.exists_leviForm_eq h
    have hw' : IsComplexTangent ρ p w := (h'.isComplexTangent_iff h w).mp hw
    rw [hlev w hw']
    exact mul_pos hc (hL w hw' hw0)

end StrictDefinition

section Bilinear

/-- The complex bilinear part of a real bilinear form on a complex space. -/
def leviBilinear (B : E →L[ℝ] E →L[ℝ] ℝ) (q : E × E) : ℂ :=
  (((B q.1 q.2 - B (I • q.1) (I • q.2)) / 4 : ℝ) : ℂ) -
    I / 4 * (((B q.1 (I • q.2) + B (I • q.1) q.2) : ℝ) : ℂ)

/-- Multiplying the first argument by `I` multiplies the complex bilinear part by `I`. -/
theorem leviBilinear_I_smul_left (B : E →L[ℝ] E →L[ℝ] ℝ) (k k' : E) :
    leviBilinear B (I • k, k') = I * leviBilinear B (k, k') := by
  simp only [leviBilinear, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg,
    neg_apply]
  apply Complex.ext <;> simp <;> ring

/-- Multiplying the second argument by `I` multiplies the complex bilinear part by `I`. -/
theorem leviBilinear_I_smul_right (B : E →L[ℝ] E →L[ℝ] ℝ) (k k' : E) :
    leviBilinear B (k, I • k') = I * leviBilinear B (k, k') := by
  simp only [leviBilinear, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
  apply Complex.ext <;> simp <;> ring

/-- The complex bilinear part is a bounded complex bilinear map. -/
theorem isBoundedBilinearMap_leviBilinear (B : E →L[ℝ] E →L[ℝ] ℝ) :
    IsBoundedBilinearMap ℂ (leviBilinear B) := by
  have hre : ∀ (r : ℝ) (k k' : E), leviBilinear B (r • k, k') = (r : ℂ) * leviBilinear B (k, k')
    := by
    intro r k k'
    have h1 : I • r • k = r • I • k := smul_comm I r k
    simp only [leviBilinear, h1, map_smul]
    apply Complex.ext <;> simp <;> ring
  have hre' : ∀ (r : ℝ) (k k' : E), leviBilinear B (k, r • k') = (r : ℂ) * leviBilinear B (k, k')
    := by
    intro r k k'
    have h1 : I • r • k' = r • I • k' := smul_comm I r k'
    simp only [leviBilinear, h1, map_smul]
    apply Complex.ext <;> simp <;> ring
  refine ⟨fun k₁ k₂ k' => ?_, fun c k k' => ?_, fun k k₁' k₂' => ?_, fun c k k' => ?_, ?_⟩
  · simp only [leviBilinear, smul_add, map_add]
    apply Complex.ext <;> simp <;> ring
  · rw [Complex.smul_eq_re_smul_add_im_smul c k]
    have h1 : leviBilinear B (c.re • k + c.im • I • k, k') =
        leviBilinear B (c.re • k, k') + leviBilinear B (c.im • I • k, k') := by
      simp only [leviBilinear, smul_add, map_add]
      apply Complex.ext <;> simp <;> ring
    rw [h1, hre, hre, leviBilinear_I_smul_left, smul_eq_mul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  · simp only [leviBilinear, smul_add, map_add]
    apply Complex.ext <;> simp <;> ring
  · rw [Complex.smul_eq_re_smul_add_im_smul c k']
    have h1 : leviBilinear B (k, c.re • k' + c.im • I • k') =
        leviBilinear B (k, c.re • k') + leviBilinear B (k, c.im • I • k') := by
      simp only [leviBilinear, smul_add, map_add]
      apply Complex.ext <;> simp <;> ring
    rw [h1, hre', hre', leviBilinear_I_smul_right, smul_eq_mul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  · refine ⟨‖B‖ + 1, by positivity, fun k k' => ?_⟩
    have hB : ∀ x y : E, |B x y| ≤ ‖B‖ * ‖x‖ * ‖y‖ := fun x y => by
      have := B.le_opNorm₂ x y
      rwa [Real.norm_eq_abs] at this
    have hI : ∀ x : E, ‖I • x‖ = ‖x‖ := fun x => by rw [norm_smul, Complex.norm_I, one_mul]
    have h1 : |B k k' - B (I • k) (I • k')| ≤ 2 * (‖B‖ * ‖k‖ * ‖k'‖) := by
      calc |B k k' - B (I • k) (I • k')| ≤ |B k k'| + |B (I • k) (I • k')| := abs_sub _ _
        _ ≤ ‖B‖ * ‖k‖ * ‖k'‖ + ‖B‖ * ‖I • k‖ * ‖I • k'‖ := add_le_add (hB _ _) (hB _ _)
        _ = 2 * (‖B‖ * ‖k‖ * ‖k'‖) := by rw [hI, hI]; ring
    have h2 : |B k (I • k') + B (I • k) k'| ≤ 2 * (‖B‖ * ‖k‖ * ‖k'‖) := by
      calc |B k (I • k') + B (I • k) k'| ≤ |B k (I • k')| + |B (I • k) k'| := abs_add_le _ _
        _ ≤ ‖B‖ * ‖k‖ * ‖I • k'‖ + ‖B‖ * ‖I • k‖ * ‖k'‖ := add_le_add (hB _ _) (hB _ _)
        _ = 2 * (‖B‖ * ‖k‖ * ‖k'‖) := by rw [hI, hI]; ring
    have hnn : 0 ≤ ‖B‖ * ‖k‖ * ‖k'‖ := by positivity
    calc ‖leviBilinear B (k, k')‖
        ≤ ‖(((B k k' - B (I • k) (I • k')) / 4 : ℝ) : ℂ)‖ +
          ‖I / 4 * (((B k (I • k') + B (I • k) k') : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ = |B k k' - B (I • k) (I • k')| / 4 + |B k (I • k') + B (I • k) k'| / 4 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 4),
            norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
          norm_num
          ring
      _ ≤ 2 * (‖B‖ * ‖k‖ * ‖k'‖) / 4 + 2 * (‖B‖ * ‖k‖ * ‖k'‖) / 4 := by gcongr
      _ = ‖B‖ * ‖k‖ * ‖k'‖ := by ring
      _ ≤ (‖B‖ + 1) * ‖k‖ * ‖k'‖ := by gcongr; linarith

/-- On the diagonal, the complex bilinear part of a symmetric form is the complex quadratic
coefficient of `LeviConvexity.Necessity`. -/
theorem leviBilinear_self (B : E →L[ℝ] E →L[ℝ] ℝ) {k : E} (hsymm : B k (I • k) = B (I • k) k) :
    leviBilinear B (k, k) = leviQuadratic B k := by
  simp only [leviBilinear, leviQuadratic, hsymm]
  apply Complex.ext
  · simp
  · simp
    ring

end Bilinear

section Modification

variable {ρ : E → ℝ} {p : E}

/-- The Levi form of `ρ + A ρ ^ 2` at a zero of `ρ` adds `A / 2` times the squared modulus of the
complex-linear part of the derivative. -/
theorem leviForm_add_mul_sq (hρ : ContDiffAt ℝ 2 ρ p) (hρ0 : ρ p = 0) (A : ℝ) (w : E) :
    leviForm (fun z => ρ z + A * ρ z ^ 2) p w =
      leviForm ρ p w + A / 2 * ‖complexPart (fderiv ℝ ρ p) w‖ ^ 2 := by
  have hev : ∀ᶠ y in 𝓝 p, HasFDerivAt ρ (fderiv ℝ ρ y) y := by
    filter_upwards [hρ.eventually (by simp)] with y hy
    exact (hy.differentiableAt (by norm_num)).hasFDerivAt
  have hD2 : HasFDerivAt (fderiv ℝ ρ) (fderiv ℝ (fderiv ℝ ρ) p) p :=
    ((hρ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  -- first derivative of the modified function
  have hD1 : (fun y => fderiv ℝ (fun z => ρ z + A * ρ z ^ 2) y) =ᶠ[𝓝 p]
      fun y => fderiv ℝ ρ y + (A * (2 * ρ y)) • fderiv ℝ ρ y := by
    filter_upwards [hev] with y hy
    have h := hy.add ((hy.pow 2).const_mul A)
    refine h.fderiv.trans ?_
    ext v
    simp
    ring
  -- second derivative at `p`
  have hℓ : HasFDerivAt ρ (fderiv ℝ ρ p) p := (hρ.differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasFDerivAt (fun y => A * (2 * ρ y)) ((A * 2) • fderiv ℝ ρ p) p := by
    have h := (hℓ.const_mul (2 : ℝ)).const_mul A
    convert h using 1
    ext v
    simp
    ring
  have hsm := hc.smul hD2
  have hsum : HasFDerivAt (fun y => fderiv ℝ ρ y + (A * (2 * ρ y)) • fderiv ℝ ρ y) _ p :=
    hD2.add hsm
  rw [leviForm_eq_fderiv, leviForm_eq_fderiv, hD1.fderiv_eq, hsum.fderiv]
  have hn : ‖complexPart (fderiv ℝ ρ p) w‖ ^ 2 =
      fderiv ℝ ρ p w ^ 2 + fderiv ℝ ρ p (I • w) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [complexPart_apply]
    ring
  rw [hn]
  simp [hρ0, add_apply, smul_apply, smul_eq_mul]
  ring

end Modification

section Compactness

variable {ρ : E → ℝ} {p : E}

/-- The Levi form is homogeneous of degree two under real scaling. -/
theorem leviForm_smul_real (f : E → ℝ) (p : E) (t : ℝ) (w : E) :
    leviForm f p (t • w) = t ^ 2 * leviForm f p w := by
  have h1 : I • t • w = t • I • w := smul_comm I t w
  simp only [leviForm_eq_fderiv, h1, map_smul, smul_apply, smul_eq_mul]
  ring

/-- The Levi form is continuous in the direction. -/
theorem continuous_leviForm (f : E → ℝ) (p : E) : Continuous fun w => leviForm f p w := by
  simp only [leviForm_eq_fderiv]
  have hB := (fderiv ℝ (fderiv ℝ f) p).isBoundedBilinearMap.continuous
  fun_prop

/-- Real scaling of the complex-linear part. -/
theorem complexPart_real_smul (ℓ : E →L[ℝ] ℝ) (r : ℝ) (w : E) :
    complexPart ℓ (r • w) = (r : ℂ) * complexPart ℓ w := by
  rw [← Complex.coe_smul, map_smul, smul_eq_mul]

/-- A vector is complex tangent exactly when the complex-linear part of the derivative vanishes on
it. -/
theorem isComplexTangent_iff_complexPart_eq_zero (w : E) :
    IsComplexTangent ρ p w ↔ complexPart (fderiv ℝ ρ p) w = 0 := by
  simp only [IsComplexTangent, complexPart_apply, Complex.ext_iff]
  simp

/-- **Positive definiteness after modification.** If the Levi form is positive definite on
the complex tangent space at `p`, then adding a large multiple of the squared modulus of the
complex-linear part of the derivative makes it positive definite on the whole space. -/
theorem exists_leviForm_add_normSq_ge [FiniteDimensional ℂ E]
    (hstrict : ∀ w, IsComplexTangent ρ p w → w ≠ 0 → 0 < leviForm ρ p w) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ c : ℝ, 0 < c ∧ ∀ w,
      c * ‖w‖ ^ 2 ≤ leviForm ρ p w + A / 2 * ‖complexPart (fderiv ℝ ρ p) w‖ ^ 2 := by
  set ℓ := fderiv ℝ ρ p with hℓ
  by_contra hcon
  push Not at hcon
  -- a sequence of bad unit vectors
  have hbad : ∀ n : ℕ, ∃ u : E, ‖u‖ = 1 ∧
      leviForm ρ p u + (n : ℝ) / 2 * ‖complexPart ℓ u‖ ^ 2 < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨w, hw⟩ := hcon n (Nat.cast_nonneg n) (1 / ((n : ℝ) + 1)) (by positivity)
    have hw0 : w ≠ 0 := by
      rintro rfl
      have h0 : leviForm ρ p 0 = 0 := by simp [leviForm_eq_fderiv]
      have h1 : complexPart ℓ 0 = 0 := by simp [complexPart_apply]
      rw [h0, h1] at hw
      simp at hw
    have hn0 : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    refine ⟨‖w‖⁻¹ • w, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn0.ne'], ?_⟩
    rw [leviForm_smul_real, complexPart_real_smul, norm_mul, Complex.norm_real, norm_inv, norm_norm,
      mul_pow]
    have h2 : 0 < ‖w‖ ^ 2 := by positivity
    have hinv : (‖w‖⁻¹) ^ 2 = (‖w‖ ^ 2)⁻¹ := by rw [inv_pow]
    rw [hinv]
    rw [← sub_pos] at hw ⊢
    have : (‖w‖ ^ 2)⁻¹ * (1 / ((n : ℝ) + 1) * ‖w‖ ^ 2 -
        (leviForm ρ p w + (n : ℝ) / 2 * ‖complexPart ℓ w‖ ^ 2)) > 0 := by positivity
    convert this using 1
    field_simp
  choose u hu using hbad
  have huS : ∀ n, u n ∈ sphere (0 : E) 1 := fun n => by simpa using (hu n).1
  -- bound on the Levi form over the unit sphere
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn
    (continuous_leviForm ρ p).continuousOn
  have hM' : ∀ n, -M ≤ leviForm ρ p (u n) := fun n => by
    have := hM _ (huS n)
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (leviForm ρ p (u n))]
  -- the complex parts tend to zero
  have hpart : ∀ n : ℕ, (n : ℝ) / 2 * ‖complexPart ℓ (u n)‖ ^ 2 ≤ M + 1 := fun n => by
    have h1 := (hu n).2
    have h2 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith [hM' n]
  -- a convergent subsequence
  obtain ⟨v, hvS, φ, hφ, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq huS
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hvS
  -- the limit is complex tangent
  have hcp : Tendsto (fun n => ‖complexPart ℓ (u (φ n))‖ ^ 2) atTop (𝓝 (‖complexPart ℓ v‖ ^ 2)) :=
    (((complexPart ℓ).continuous.norm.pow 2).continuousAt.tendsto.comp hlim)
  have hφtop : Tendsto (fun n => (φ n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  have hcp0 : ‖complexPart ℓ v‖ ^ 2 = 0 := by
    apply le_antisymm _ (by positivity)
    have hg : Tendsto (fun n => 2 * (M + 1) / (φ n : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (2 * (M + 1))).comp hφ.tendsto_atTop
    refine le_of_tendsto_of_tendsto hcp hg ?_
    filter_upwards [hφtop.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    have h := hpart (φ n)
    rw [le_div_iff₀ hn]
    linarith
  have hv_tan : IsComplexTangent ρ p v := by
    rw [isComplexTangent_iff_complexPart_eq_zero]
    have : ‖complexPart ℓ v‖ = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hcp0
    exact norm_eq_zero.mp this
  -- the limit has nonpositive Levi form
  have hlev : leviForm ρ p v ≤ 0 := by
    have hl : Tendsto (fun n => leviForm ρ p (u (φ n))) atTop (𝓝 (leviForm ρ p v)) :=
      (continuous_leviForm ρ p).continuousAt.tendsto.comp hlim
    have hg : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    refine le_of_tendsto_of_tendsto hl hg (Filter.Eventually.of_forall fun n => ?_)
    have := (hu (φ n)).2
    have hnn : 0 ≤ ((φ n : ℕ) : ℝ) / 2 * ‖complexPart ℓ (u (φ n))‖ ^ 2 := by positivity
    linarith
  exact absurd (hstrict v hv_tan hv0) (not_lt.mpr hlev)

end Compactness

section PeakFunction

variable [FiniteDimensional ℂ E] {U : Set E} {p : E} {ρ : E → ℝ} {V : Set E}

/-- **Levi polynomial as a peak function ([Range][Range1986], Proposition 2.16).** At a boundary
point with
positive definite Levi form on the complex tangent space there is an entire holomorphic function
`F` vanishing at `p` whose real part is negative at all nearby points where the defining
function is nonpositive, except at `p`. -/
theorem IsLocalDefiningFunction.exists_holomorphic_support (h : IsLocalDefiningFunction U p ρ V)
    (hstrict : ∀ w, IsComplexTangent ρ p w → w ≠ 0 → 0 < leviForm ρ p w) :
    ∃ W ∈ 𝓝 p, ∃ F : E → ℂ, AnalyticOnNhd ℂ F univ ∧ F p = 0 ∧
      ∀ z ∈ W, z ≠ p → ρ z ≤ 0 → (F z).re < 0 := by
  set ℓ := fderiv ℝ ρ p with hℓ
  have hρc : ContDiffAt ℝ 2 ρ p := h.contDiffOn.contDiffAt (h.isOpen.mem_nhds h.mem)
  obtain ⟨A, hA, c, hc, hpos⟩ := exists_leviForm_add_normSq_ge hstrict
  -- the modified defining function
  set σ : E → ℝ := fun z => ρ z + A * ρ z ^ 2 with hσ
  have hσc : ContDiffAt ℝ 2 σ p := hρc.add (contDiffAt_const.mul (hρc.pow 2))
  have hσ0 : σ p = 0 := by simp [hσ, h.eq_zero]
  have hσlev : ∀ w, c * ‖w‖ ^ 2 ≤ leviForm σ p w := fun w => by
    rw [hσ, leviForm_add_mul_sq hρc h.eq_zero]
    exact hpos w
  have hd : HasFDerivAt ρ ℓ p := (hρc.differentiableAt (by norm_num)).hasFDerivAt
  have hσℓ : fderiv ℝ σ p = ℓ := by
    have := hd.add ((hd.pow 2).const_mul A)
    refine this.fderiv.trans ?_
    ext v
    simp [h.eq_zero]
  set B := fderiv ℝ (fderiv ℝ σ) p with hB
  have hev : ∀ᶠ y in 𝓝 p, HasFDerivAt σ (fderiv ℝ σ y) y := by
    filter_upwards [hσc.eventually (by simp)] with y hy
    exact (hy.differentiableAt (by norm_num)).hasFDerivAt
  have hBd : HasFDerivAt (fderiv ℝ σ) B p :=
    ((hσc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hsymm : ∀ v v', B v v' = B v' v := second_derivative_symmetric_of_eventually hev hBd
  -- the Levi polynomial
  set F : E → ℂ := fun z => complexPart ℓ (z - p) + leviBilinear B (z - p, z - p) with hF
  have hFd : Differentiable ℂ F := by
    have h1 : Differentiable ℂ (complexPart ℓ) := fun x =>
      (complexPart ℓ).differentiableAt
    have h2 : Differentiable ℂ (leviBilinear B) := fun q =>
      (isBoundedBilinearMap_leviBilinear B).differentiableAt q
    have hsub : Differentiable ℂ (fun z : E => z - p) := differentiable_id.sub_const p
    exact (h1.comp hsub).add (h2.comp (hsub.prodMk hsub))
  have hFan : AnalyticOnNhd ℂ F univ := hFd.analyticOnNhd_of_finiteDimensional
  have hF0 : F p = 0 := by simp [hF, leviBilinear]
  -- Taylor expansion of the modified defining function
  obtain ⟨δ, hδ, htaylor⟩ := exists_taylor_bound hσc (ε := c / 2) (by positivity)
  have hsmall : ∀ᶠ z in 𝓝 p, |ρ z| < 1 / (A + 1) := by
    have hcont : ContinuousAt (fun z => |ρ z|) p := hρc.continuousAt.abs
    exact hcont.eventually (eventually_lt_nhds (by
      show |ρ p| < 1 / (A + 1)
      rw [h.eq_zero, abs_zero]
      positivity))
  refine ⟨ball p δ ∩ {z | |ρ z| < 1 / (A + 1)}, inter_mem (ball_mem_nhds p hδ) hsmall, F, hFan,
    hF0, ?_⟩
  rintro z ⟨hzδ, hzρ⟩ hzp hρz
  have hzρ' : |ρ z| < 1 / (A + 1) := hzρ
  set k := z - p with hk
  have hk0 : k ≠ 0 := sub_ne_zero.mpr hzp
  have hkδ : ‖k‖ < δ := by rw [hk, ← dist_eq_norm]; exact mem_ball.mp hzδ
  have ht := htaylor k hkδ
  have hpk : p + k = z := by rw [hk]; abel
  rw [hpk, hσ0, sub_zero, hσℓ] at ht
  -- the real part of the Levi polynomial
  have hlin : ℓ k = (complexPart ℓ k).re := by
    have := apply_smul_eq_re_mul_complexPart ℓ 1 k
    simpa using this
  have hquad : (1 / 2 : ℝ) * B k k = leviForm σ p k + (leviQuadratic B k).re := by
    have := bilinear_smul_smul_eq B (hsymm k (I • k)) 1
    simpa [leviForm_eq_fderiv, leviQuadratic] using this
  have hFre : (F z).re = ℓ k + (leviQuadratic B k).re := by
    simp only [hF, Complex.add_re]
    rw [← hk, hlin, leviBilinear_self B (hsymm k (I • k))]
  -- the modified function is nonpositive at `z`
  have hσz : σ z ≤ 0 := by
    have h1 : 0 < 1 + A * ρ z := by
      have hlow := (abs_lt.mp hzρ').1
      have : A * (1 / (A + 1)) < 1 := by
        rw [mul_one_div, div_lt_one (by positivity)]
        linarith
      nlinarith
    have : σ z = (1 + A * ρ z) * ρ z := by simp only [hσ]; ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos h1.le hρz
  have hknorm : 0 < c / 2 * ‖k‖ ^ 2 := by positivity
  have h1 := (abs_le.mp ht).1
  rw [hFre]
  linarith [hσlev k]

/-- **Normalized local peak function.** Exponentiating a holomorphic supporting function
has value one at the boundary point and modulus strictly less than one at every other nearby
point on the closed side of the defining function. -/
theorem IsLocalDefiningFunction.exists_peak
    (h : IsLocalDefiningFunction U p ρ V)
    (hstrict : ∀ w, IsComplexTangent ρ p w → w ≠ 0 → 0 < leviForm ρ p w) :
    ∃ W ∈ 𝓝 p, ∃ f : E → ℂ, AnalyticOnNhd ℂ f univ ∧ f p = 1 ∧
      ∀ z ∈ W, z ≠ p → ρ z ≤ 0 → ‖f z‖ < 1 := by
  obtain ⟨W, hW, F, hF, hFp, hneg⟩ := h.exists_holomorphic_support hstrict
  refine ⟨W, hW, fun z => Complex.exp (F z), ?_, by simp [hFp], ?_⟩
  · exact fun z hz => (hF z hz).cexp
  · intro z hz hzp hρ
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    exact hneg z hz hzp hρ

/-- On the domain near a strictly Levi convex boundary point, the Levi polynomial has negative real
part. -/
theorem IsLocalDefiningFunction.exists_holomorphic_support_of_mem (hU : IsOpen U) (hp : p ∈
  frontier U)
    (h : IsLocalDefiningFunction U p ρ V)
    (hstrict : ∀ w, IsComplexTangent ρ p w → w ≠ 0 → 0 < leviForm ρ p w) :
    ∃ W ∈ 𝓝 p, ∃ F : E → ℂ, AnalyticOnNhd ℂ F univ ∧ F p = 0 ∧ ∀ z ∈ W ∩ U, (F z).re < 0 := by
  obtain ⟨W, hW, F, hFan, hF0, hneg⟩ := h.exists_holomorphic_support hstrict
  refine ⟨W ∩ V, inter_mem hW (h.isOpen.mem_nhds h.mem), F, hFan, hF0, ?_⟩
  rintro z ⟨⟨hzW, hzV⟩, hzU⟩
  have hzp : z ≠ p := fun hzp => hU.notMem_of_mem_frontier hp (hzp ▸ hzU)
  exact hneg z hzW hzp (h.neg_of_mem hzV hzU).le

/-- **Local holomorphic blow-up.** At a strictly Levi convex boundary point of an open set there is
a
holomorphic function on the set near the point whose modulus tends to infinity at the point. -/
theorem IsLocalDefiningFunction.exists_tendsto_norm_atTop (hU : IsOpen U) (hp : p ∈ frontier U)
    (h : IsLocalDefiningFunction U p ρ V)
    (hstrict : ∀ w, IsComplexTangent ρ p w → w ≠ 0 → 0 < leviForm ρ p w) :
    ∃ W ∈ 𝓝 p, ∃ f : E → ℂ, AnalyticOnNhd ℂ f (W ∩ U) ∧
      Tendsto (fun z => ‖f z‖) (𝓝[U] p) atTop := by
  obtain ⟨W, hW, F, hFan, hF0, hneg⟩ := h.exists_holomorphic_support_of_mem hU hp hstrict
  have hFne : ∀ z ∈ W ∩ U, F z ≠ 0 := fun z hz hzero => by
    have := hneg z hz
    rw [hzero, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨W, hW, fun z => (F z)⁻¹, fun z hz => (hFan z (mem_univ z)).inv (hFne z hz), ?_⟩
  have hF : Tendsto (fun z => ‖F z‖) (𝓝[U] p) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have := ((hFan p (mem_univ p)).continuousAt.norm).tendsto
      rw [hF0, norm_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [nhdsWithin_le_nhds hW, self_mem_nhdsWithin] with z hzW hzU
      exact norm_pos_iff.mpr (hFne z ⟨hzW, hzU⟩)
  have := tendsto_inv_nhdsGT_zero.comp hF
  simpa [Function.comp_def, norm_inv] using this

end PeakFunction

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
