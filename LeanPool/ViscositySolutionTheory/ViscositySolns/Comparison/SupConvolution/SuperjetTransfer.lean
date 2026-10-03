/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Semijets.Closure

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Sup-convolution declarations (SuperjetTransfer)

Part of the compact-set sup-convolution development used in the appendix
proof of the maximum principle for semicontinuous functions. Split from
`SupConvolution.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat}

/--
The function whose supremum defines the sup-convolution at `ξ`.

In standard mathematical notation this is

`x ↦ u(x) - (λ / 2) ∑ i, (x_i - ξ_i)^2`.
-/
def supConvolutionKernel (lambda : Real) (u : Point n -> Real) (ξ x : Point n) :
    Real :=
  u x - (lambda / 2) * dotProduct (x - ξ) (x - ξ)

/--
The compact-set sup-convolution value.

In standard mathematical notation this is

`sup { u(x) - (λ / 2) ∑ i, (x_i - ξ_i)^2 | x ∈ K }`.

This declaration is intended for compact nonempty `K`; the accompanying
maximum-existence theorem supplies a point where the displayed supremum is
attained under upper semicontinuity.
-/
def compactSupConvolution (lambda : Real) (K : Set (Point n))
    (u : Point n -> Real) (ξ : Point n) : Real :=
  sSup ((fun x : Point n => supConvolutionKernel lambda u ξ x) '' K)

/--
If `u` is upper semicontinuous on `K`, then the sup-convolution kernel is
upper semicontinuous on `K`.

In quantified mathematical form, for every real number `λ` and point `ξ`, if
`u` is upper semicontinuous on `K`, then
`x ↦ u x - (λ / 2) * ∑ i, (x i - ξ i)^2` is upper semicontinuous on `K`.
-/
theorem upperSemicontinuousOn_supConvolutionKernel
    {K : Set (Point n)} {u : Point n -> Real} {lambda : Real} {ξ : Point n}
    (hu : UpperSemicontinuousOn u K) :
    UpperSemicontinuousOn (fun x : Point n => supConvolutionKernel lambda u ξ x) K := by
  have hpen :
      ContinuousOn
        (fun x : Point n => (lambda / 2) * dotProduct (x - ξ) (x - ξ)) K := by
    have hdiff : Continuous fun x : Point n => x - ξ :=
      continuous_id.sub continuous_const
    exact (continuous_const.mul (hdiff.dotProduct hdiff)).continuousOn
  have hnegpen :
      UpperSemicontinuousOn
        (fun x : Point n => -((lambda / 2) * dotProduct (x - ξ) (x - ξ))) K :=
    (continuousOn_iff_lower_upperSemicontinuousOn.mp hpen.neg).2
  simpa [supConvolutionKernel, sub_eq_add_neg] using hu.add hnegpen

/--
On a nonempty compact set, the sup-convolution kernel attains a maximum.

In quantified mathematical form, if `K` is nonempty and compact and `u` is
upper semicontinuous on `K`, then for every `λ` and `ξ` there exists
`x ∈ K` such that for every `y ∈ K`,

`u y - (λ / 2) * ∑ i, (y i - ξ i)^2 ≤
 u x - (λ / 2) * ∑ i, (x i - ξ i)^2`.
-/
theorem exists_isMaxOn_supConvolutionKernel_of_isCompact
    {K : Set (Point n)} {u : Point n -> Real} {lambda : Real} {ξ : Point n}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hu : UpperSemicontinuousOn u K) :
    ∃ x ∈ K, IsMaxOn (fun y : Point n => supConvolutionKernel lambda u ξ y) K x :=
  UpperSemicontinuousOn.exists_isMaxOn hKne hKcompact
    (upperSemicontinuousOn_supConvolutionKernel hu)

/--
If the sup-convolution kernel has a maximum point `y` on `K`, then the compact
sup-convolution is the kernel value at `y`.

In quantified mathematical form, if `y ∈ K` and for every `z ∈ K`,

`u z - (lambda / 2) * ∑ i, (z i - ξ i)^2 ≤
 u y - (lambda / 2) * ∑ i, (y i - ξ i)^2`,

then

`compactSupConvolution lambda K u ξ =
 u y - (lambda / 2) * ∑ i, (y i - ξ i)^2`.
-/
theorem compactSupConvolution_eq_of_isMaxOn
    {K : Set (Point n)} {u : Point n -> Real} {lambda : Real} {ξ y : Point n}
    (hy : y ∈ K)
    (hmax : IsMaxOn (fun z : Point n => supConvolutionKernel lambda u ξ z) K y) :
    compactSupConvolution lambda K u ξ = supConvolutionKernel lambda u ξ y := by
  let f : Point n -> Real := fun z => supConvolutionKernel lambda u ξ z
  have hgreatest : IsGreatest (f '' K) (f y) := by
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro r ⟨z, hz, rfl⟩
    exact hmax hz
  simpa [compactSupConvolution, f] using hgreatest.csSup_eq

/--
If the sup-convolution kernel attains a maximum on `K` at every `ξ`, then each
kernel value is bounded above by the compact sup-convolution value.

In quantified mathematical form, suppose that for every `ξ` there exists
`y ∈ K` such that `y` is a maximum point on `K` of
`z ↦ u z - (lambda / 2) * ∑ i, (z i - ξ i)^2`. Then for every `z ∈ K` and every
`ξ`,

`u z - (lambda / 2) * ∑ i, (z i - ξ i)^2
  ≤ compactSupConvolution lambda K u ξ`.
-/
theorem supConvolutionKernel_le_compactSupConvolution_of_exists_isMaxOn
    {K : Set (Point n)} {u : Point n -> Real} {lambda : Real}
    (hmax_exists : ∀ ξ : Point n,
      ∃ y ∈ K, IsMaxOn (fun z : Point n => supConvolutionKernel lambda u ξ z) K y)
    {z ξ : Point n} (hz : z ∈ K) :
    supConvolutionKernel lambda u ξ z <= compactSupConvolution lambda K u ξ := by
  rcases hmax_exists ξ with ⟨y, hy, hmax⟩
  rw [compactSupConvolution_eq_of_isMaxOn hy hmax]
  exact hmax hz

/--
The superjet transfer lemma for a function majorized by sup-convolution
kernels.

In quantified mathematical form, let `vhat : Point n -> Real` be a function
such that for every `z ∈ K` and every `ξ`,

`v z - (lambda / 2) * ∑ i, (z i - ξ i)^2 ≤ vhat ξ`.

Suppose that equality holds at the pair `(η, y)`, namely

`vhat η = v y - (lambda / 2) * ∑ i, (y i - η i)^2`.

If `(q, Y)` belongs to the superjet of `vhat` at `η` relative to all of
`R^n`, then `(q, Y)` belongs to the superjet of `v` at `y` relative to `K`.
-/
theorem superjet_of_superjet_supConvolutionMajorant
    {K : Set (Point n)} {v vhat : Point n -> Real}
    {lambda : Real} {η y q : Point n} {Y : Hessian n}
    (hmajor : ∀ z : Point n, z ∈ K -> ∀ ξ : Point n,
      supConvolutionKernel lambda v ξ z <= vhat ξ)
    (hvalue : vhat η = supConvolutionKernel lambda v η y)
    (hJ : ({ gradient := q, hessian := Y } : Jet n) ∈ Superjet Set.univ vhat η) :
    ({ gradient := q, hessian := Y } : Jet n) ∈ Superjet K v y := by
  rcases hJ with ⟨rho, hrho, hineq⟩
  let T : Point n -> Point n := fun x => x - y + η
  have hT_tendsto : Tendsto T (nhdsWithin y K) (nhdsWithin η Set.univ) := by
    have hcont : Continuous T := by
      dsimp [T]
      exact (continuous_id.sub continuous_const).add continuous_const
    have hmap : Tendsto T (nhdsWithin y K) (nhds (T y)) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hTy : T y = η := by
      ext i
      simp [T]
    simpa [hTy] using hmap
  have hrho_comp :
      SemijetRemainder K y (fun x : Point n => rho (T x)) := by
    have hcomp := hrho.comp_tendsto hT_tendsto
    change (fun x : Point n => rho (T x)) =o[nhdsWithin y K]
      (fun x : Point n => ‖x - y‖ ^ 2)
    convert hcomp using 1
    all_goals ext x; simp [T]
  refine ⟨fun x : Point n => rho (T x), hrho_comp, ?_⟩
  have hineq_comp :
      ∀ᶠ x in nhdsWithin y K,
        vhat (T x) <=
          quadraticModel η (vhat η) q Y (T x) + rho (T x) :=
    hT_tendsto hineq
  filter_upwards [hineq_comp, self_mem_nhdsWithin] with x hxineq hxK
  have hmajor_x : supConvolutionKernel lambda v (T x) x <= vhat (T x) :=
    hmajor x hxK (T x)
  have hxi_eta : T x - η = x - y := by
    ext i
    simp [T]
  have hx_xi : x - T x = y - η := by
    ext i
    simp [T]
    ring
  calc
    v x <= vhat (T x) + (lambda / 2) * dotProduct (y - η) (y - η) := by
      dsimp [supConvolutionKernel] at hmajor_x
      rw [hx_xi] at hmajor_x
      linarith
    _ <= quadraticModel η (vhat η) q Y (T x) + rho (T x) +
        (lambda / 2) * dotProduct (y - η) (y - η) := by
      linarith
    _ = quadraticModel y (v y) q Y x + rho (T x) := by
      rw [hvalue]
      dsimp [supConvolutionKernel, quadraticModel]
      rw [hxi_eta]
      ring

/--
The gradient component of a superjet of a function majorizing all
sup-convolution kernels is determined by a kernel value where equality holds.

In quantified mathematical form, let `vhat : Point n -> Real` satisfy

`v z - (lambda / 2) * ∑ i, (z i - ξ i)^2 ≤ vhat ξ`

for every `z ∈ K` and every `ξ`. Suppose that `y ∈ K` and that equality holds
at `(η, y)`, namely

`vhat η = v y - (lambda / 2) * ∑ i, (y i - η i)^2`.

If `(q, Y) ∈ J^{2,+}_{R^n} vhat(η)`, then

`q = lambda • (y - η)`.
-/
theorem superjet_gradient_eq_of_supConvolutionMajorant
    {K : Set (Point n)} {v vhat : Point n -> Real}
    {lambda : Real} {η y q : Point n} {Y : Hessian n}
    (hmajor : ∀ z : Point n, z ∈ K -> ∀ ξ : Point n,
      supConvolutionKernel lambda v ξ z <= vhat ξ)
    (hy : y ∈ K)
    (hvalue : vhat η = supConvolutionKernel lambda v η y)
    (hJ : ({ gradient := q, hessian := Y } : Jet n) ∈ Superjet Set.univ vhat η) :
    q = lambda • (y - η) := by
  have hsecond :
      SecondOrderNonposWithin Set.univ η
        (SuperjetExcess vhat η ({ gradient := q, hessian := Y } : Jet n)) :=
    superjetExcess_secondOrderNonposWithin hJ
  let a : Point n := lambda • (y - η) - q
  have hdot_nonpos : ∀ d : Point n, dotProduct a d <= 0 := by
    intro d
    let A : Real := dotProduct a d
    let B : Real :=
      (lambda / 2) * dotProduct d d +
        (1 / 2 : Real) * dotProduct (Matrix.mulVec Y d) d + ‖d‖ ^ 2
    have hline :
        Tendsto (fun t : Real => η + t • d)
          (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhdsWithin η Set.univ) := by
      have hcont : Continuous fun t : Real => η + t • d :=
        continuous_const.add (continuous_id.smul continuous_const)
      have htend : Tendsto (fun t : Real => η + t • d)
          (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (η + (0 : Real) • d)) :=
        (hcont.continuousAt (x := (0 : Real))).tendsto.mono_left nhdsWithin_le_nhds
      simpa using htend
    have hso_event :
        ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
          SuperjetExcess vhat η ({ gradient := q, hessian := Y } : Jet n)
              (η + t • d) <= ‖η + t • d - η‖ ^ 2 :=
      by
        have hraw := hline (hsecond (1 : Real) zero_lt_one)
        filter_upwards [hraw] with t ht
        simpa using ht
    have hineq_event :
        ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0), A <= t * B := by
      filter_upwards [hso_event, self_mem_nhdsWithin] with t htso htpos
      have htpos' : 0 < t := htpos
      have hmajor_t :
          supConvolutionKernel lambda v (η + t • d) y <= vhat (η + t • d) :=
        hmajor y hy (η + t • d)
      have hkernel_model :
          supConvolutionKernel lambda v (η + t • d) y -
              supConvolutionKernel lambda v η y <=
            quadraticModel η (vhat η) q Y (η + t • d) - vhat η +
              ‖η + t • d - η‖ ^ 2 := by
        rw [← hvalue]
        unfold SuperjetExcess at htso
        linarith
      have halg :
          supConvolutionKernel lambda v (η + t • d) y -
              supConvolutionKernel lambda v η y -
            (quadraticModel η (vhat η) q Y (η + t • d) - vhat η) =
          t * A -
            t ^ 2 *
              ((lambda / 2) * dotProduct d d +
                (1 / 2 : Real) * dotProduct (Matrix.mulVec Y d) d) := by
        let b : Point n := y - η
        have hleft : y - (η + t • d) = b - t • d := by
          ext i
          simp [b]
          ring_nf
        have hright : η + t • d - η = t • d := by
          ext i
          simp
        have hkernel :
            supConvolutionKernel lambda v (η + t • d) y -
                supConvolutionKernel lambda v η y =
              t * dotProduct (lambda • b) d -
                t ^ 2 * ((lambda / 2) * dotProduct d d) := by
          simp only [supConvolutionKernel]
          rw [hleft]
          change
              (v y - (lambda / 2) * dotProduct (b - t • d) (b - t • d)) -
                  (v y - (lambda / 2) * dotProduct b b) =
                t * dotProduct (lambda • b) d -
                  t ^ 2 * ((lambda / 2) * dotProduct d d)
          simp only [dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul]
          rw [dotProduct_comm d b]
          ring
        have hmodel :
            quadraticModel η (vhat η) q Y (η + t • d) - vhat η =
              t * dotProduct q d +
                t ^ 2 * ((1 / 2 : Real) * dotProduct (Matrix.mulVec Y d) d) := by
          simp only [quadraticModel]
          rw [hright]
          simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
          ring
        rw [hkernel, hmodel]
        simp only [a, A, b, sub_dotProduct]
        simp only [smul_dotProduct]
        ring
      have hpre :
          t * A <=
            t ^ 2 *
              ((lambda / 2) * dotProduct d d +
                (1 / 2 : Real) * dotProduct (Matrix.mulVec Y d) d) +
              ‖η + t • d - η‖ ^ 2 := by
        have := hkernel_model
        rw [← sub_le_iff_le_add'] at this
        rw [halg] at this
        linarith
      have hnorm_line : ‖η + t • d - η‖ ^ 2 = t ^ 2 * ‖d‖ ^ 2 := by
        have hdiff : η + t • d - η = t • d := by
          ext i
          simp
        rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos htpos']
        ring
      have hdiv :
          A <=
            t *
              ((lambda / 2) * dotProduct d d +
                (1 / 2 : Real) * dotProduct (Matrix.mulVec Y d) d + ‖d‖ ^ 2) := by
        have hpre' :
            t * A <=
              t ^ 2 *
                ((lambda / 2) * dotProduct d d +
                  (1 / 2 : Real) * dotProduct (Matrix.mulVec Y d) d + ‖d‖ ^ 2) := by
          rw [hnorm_line] at hpre
          nlinarith
        have ht_nonneg : 0 <= t := htpos'.le
        have hpre'' :
            t * A <=
              t *
                (t *
                  ((lambda / 2) * dotProduct d d +
                    (1 / 2 : Real) * dotProduct (Matrix.mulVec Y d) d + ‖d‖ ^ 2)) := by
          nlinarith
        exact le_of_mul_le_mul_left hpre'' htpos'
      simpa [B] using hdiv
    have htend_zero :
        Tendsto (fun t : Real => t * B) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 0) := by
      have ht : Tendsto (fun t : Real => t) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using ht.mul tendsto_const_nhds
    exact le_of_tendsto_of_tendsto
      (f := fun _ : Real => A) (g := fun t : Real => t * B)
      (b := nhdsWithin (0 : Real) (Set.Ioi 0)) tendsto_const_nhds htend_zero hineq_event
  have hdot_zero : dotProduct a a = 0 := by
    have hle : dotProduct a a <= 0 := hdot_nonpos a
    have hnorm_le : ‖a‖ ^ 2 <= dotProduct a a := norm_sq_le_dotProduct_self a
    have hnorm_nonneg : 0 <= ‖a‖ ^ 2 := sq_nonneg _
    linarith
  have ha_zero : a = 0 := by
    have hnorm_zero : ‖a‖ = 0 := by
      have hnorm_sq_zero : ‖a‖ ^ 2 = 0 := by
        have hnorm_le : ‖a‖ ^ 2 <= dotProduct a a := norm_sq_le_dotProduct_self a
        have hnorm_nonneg : 0 <= ‖a‖ ^ 2 := sq_nonneg _
        linarith
      exact sq_eq_zero_iff.mp hnorm_sq_zero
    exact norm_eq_zero.mp hnorm_zero
  have : lambda • (y - η) - q = 0 := ha_zero
  exact sub_eq_zero.mp this |>.symm

/--
The gradient component of a superjet of a compact sup-convolution is
determined by any point where the defining supremum is attained.

In quantified mathematical form, suppose that for every `ξ` the function

`z ↦ v z - (lambda / 2) * ∑ i, (z i - ξ i)^2`

has a maximum point on `K`. Suppose also that `y ∈ K` and that `y` is a
maximum point on `K` for the parameter `η`. If

`(q, Y) ∈ J^{2,+}_{R^n} (ξ ↦ compactSupConvolution lambda K v ξ)(η)`,

then `q = lambda • (y - η)`.
-/
theorem superjet_gradient_eq_of_compactSupConvolution_of_isMaxOn
    {K : Set (Point n)} {v : Point n -> Real}
    {lambda : Real} {η y q : Point n} {Y : Hessian n}
    (hmax_exists : ∀ ξ : Point n,
      ∃ z ∈ K, IsMaxOn (fun x : Point n => supConvolutionKernel lambda v ξ x) K z)
    (hy : y ∈ K)
    (hmaxη : IsMaxOn (fun z : Point n => supConvolutionKernel lambda v η z) K y)
    (hJ : ({ gradient := q, hessian := Y } : Jet n) ∈
      Superjet Set.univ (fun ξ : Point n => compactSupConvolution lambda K v ξ) η) :
    q = lambda • (y - η) := by
  refine superjet_gradient_eq_of_supConvolutionMajorant
    (K := K) (v := v)
    (vhat := fun ξ : Point n => compactSupConvolution lambda K v ξ)
    (lambda := lambda) (η := η) (y := y) (q := q) (Y := Y)
    ?_ hy ?_ hJ
  · intro z hz ξ
    exact supConvolutionKernel_le_compactSupConvolution_of_exists_isMaxOn
      (K := K) (u := v) (lambda := lambda) hmax_exists hz
  · exact compactSupConvolution_eq_of_isMaxOn hy hmaxη

/--
The compact-set superjet transfer lemma for the compact sup-convolution.

In quantified mathematical form, suppose that for every `ξ` the function
`z ↦ v z - (lambda / 2) * ∑ i, (z i - ξ i)^2` has a maximum point on `K`, and suppose
that the maximum at `η` is attained at `y`. If `(q, Y)` belongs to the
superjet of `ξ ↦ compactSupConvolution lambda K v ξ` at `η` relative to all
of `R^n`, then `(q, Y)` belongs to the superjet of `v` at `y` relative to
`K`.
-/
theorem superjet_of_superjet_compactSupConvolution_of_isMaxOn
    {K : Set (Point n)} {v : Point n -> Real}
    {lambda : Real} {η y q : Point n} {Y : Hessian n}
    (hmax_exists : ∀ ξ : Point n,
      ∃ z ∈ K, IsMaxOn (fun x : Point n => supConvolutionKernel lambda v ξ x) K z)
    (hy : y ∈ K)
    (hmaxη : IsMaxOn (fun z : Point n => supConvolutionKernel lambda v η z) K y)
    (hJ : ({ gradient := q, hessian := Y } : Jet n) ∈
      Superjet Set.univ (fun ξ : Point n => compactSupConvolution lambda K v ξ) η) :
    ({ gradient := q, hessian := Y } : Jet n) ∈ Superjet K v y := by
  refine superjet_of_superjet_supConvolutionMajorant
    (lambda := lambda)
    (vhat := fun ξ : Point n => compactSupConvolution lambda K v ξ)
    ?_ ?_ hJ
  · intro z hz ξ
    exact supConvolutionKernel_le_compactSupConvolution_of_exists_isMaxOn
      (K := K) (u := v) (lambda := lambda) hmax_exists hz
  · exact compactSupConvolution_eq_of_isMaxOn hy hmaxη

/--
Compactness and upper semicontinuity supply the maximum points required by the
compact-set superjet transfer lemma.

In quantified mathematical form, let `K` be nonempty and compact, and let `v`
be upper semicontinuous on `K`. If `y ∈ K` is a maximum point on `K` of
`z ↦ v z - (lambda / 2) * ∑ i, (z i - η i)^2`, and if `(q, Y)` belongs to the
superjet of `ξ ↦ compactSupConvolution lambda K v ξ` at `η` relative to all
of `R^n`, then `(q, Y)` belongs to the superjet of `v` at `y` relative to
`K`.
-/
theorem superjet_of_superjet_compactSupConvolution_of_isCompact
    {K : Set (Point n)} {v : Point n -> Real}
    {lambda : Real} {η y q : Point n} {Y : Hessian n}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hv : UpperSemicontinuousOn v K)
    (hy : y ∈ K)
    (hmaxη : IsMaxOn (fun z : Point n => supConvolutionKernel lambda v η z) K y)
    (hJ : ({ gradient := q, hessian := Y } : Jet n) ∈
      Superjet Set.univ (fun ξ : Point n => compactSupConvolution lambda K v ξ) η) :
    ({ gradient := q, hessian := Y } : Jet n) ∈ Superjet K v y := by
  refine superjet_of_superjet_compactSupConvolution_of_isMaxOn
    (K := K) (v := v) (lambda := lambda) (η := η) (y := y)
    ?_ hy hmaxη hJ
  intro ξ
  exact exists_isMaxOn_supConvolutionKernel_of_isCompact hKne hKcompact hv

/--
The point selected by the formal sup-convolution transfer map.

In the source proof, an ordinary superjet `(q, Y)` of the sup-convolution at
`ξ` is transferred to the original function at `ξ + q / λ`. Since
`Point n` is a real vector space, this declaration writes that point as
`ξ + λ⁻¹ • q`.
-/
def supConvolutionTransferPoint (lambda : Real) (ξ : Point n) (J : Jet n) :
    Point n :=
  ξ + lambda⁻¹ • J.gradient

/--
If `lambda ≠ 0`, the formal transfer point of a superjet of a compact
sup-convolution equals any point where the defining supremum is attained.

In quantified mathematical form, under the hypotheses of
`superjet_gradient_eq_of_compactSupConvolution_of_isMaxOn`, if `lambda ≠ 0`,
then

`η + lambda⁻¹ • q = y`.
-/
theorem supConvolutionTransferPoint_eq_of_compactSupConvolution_of_isMaxOn
    {K : Set (Point n)} {v : Point n -> Real}
    {lambda : Real} {η y q : Point n} {Y : Hessian n}
    (hlambda : lambda ≠ 0)
    (hmax_exists : ∀ ξ : Point n,
      ∃ z ∈ K, IsMaxOn (fun x : Point n => supConvolutionKernel lambda v ξ x) K z)
    (hy : y ∈ K)
    (hmaxη : IsMaxOn (fun z : Point n => supConvolutionKernel lambda v η z) K y)
    (hJ : ({ gradient := q, hessian := Y } : Jet n) ∈
      Superjet Set.univ (fun ξ : Point n => compactSupConvolution lambda K v ξ) η) :
    supConvolutionTransferPoint lambda η ({ gradient := q, hessian := Y } : Jet n) = y := by
  have hq :
      q = lambda • (y - η) :=
    superjet_gradient_eq_of_compactSupConvolution_of_isMaxOn
      (K := K) (v := v) (lambda := lambda) (η := η) (y := y)
      hmax_exists hy hmaxη hJ
  ext i
  simp [supConvolutionTransferPoint, hq, smul_sub, smul_smul, hlambda]

end ViscositySolns
