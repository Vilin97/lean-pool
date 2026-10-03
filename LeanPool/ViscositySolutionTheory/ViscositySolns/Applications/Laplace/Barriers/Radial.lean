/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Geometry
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Semijets.Calculus.QuadraticControl
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Radial test functions for Laplace barriers

This file collects the analytic ingredients of the exterior-sphere barriers for
the Laplace operator.

* Euclidean geometry on `Point n` (which carries the sup norm): the square root
  of `eucSq` is the `EuclideanSpace` distance, so it satisfies the triangle
  inequality, and `eucSq` is comparable to the sup norm.
* A scalar Peano form of Taylor's theorem of order two.
* The second-order expansion of a radial function `x ↦ G (eucSq x c)`: if `G`
  has the expansion `G s₀ + G₁ (s - s₀) + G₂ (s - s₀)² / 2 + o((s - s₀)²)` at
  `s₀ = |x̂ - c|²`, then `x ↦ G (eucSq x c)` has the jet
  `(2 G₁ z, 2 G₁ I + 4 G₂ z zᵀ)` at `x̂`, where `z = x̂ - c`.
* The exponential profile `s ↦ a - k exp (-α (s - ρ))`, whose radial Hessian
  has trace `2 k α e (n - 2 α s₀)`.
* Trace comparison: a subjet and a superjet of the same function at an interior
  point have ordered traces.
-/

@[expose] public noncomputable section

open Filter Topology Asymptotics
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/-! ### Euclidean geometry on `Point n` -/

/-- The square root of `eucSq` is the distance in `EuclideanSpace`. -/
theorem sqrt_eucSq_eq_dist (x y : Point n) :
    Real.sqrt (eucSq x y) =
      dist (WithLp.toLp 2 x : EuclideanSpace Real (Fin n)) (WithLp.toLp 2 y) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  simp [eucSq, dotProduct, Real.dist_eq, sq]

/-- Triangle inequality for the Euclidean distance `√(eucSq x y)`. -/
theorem sqrt_eucSq_triangle (x y z : Point n) :
    Real.sqrt (eucSq x z) <= Real.sqrt (eucSq x y) + Real.sqrt (eucSq y z) := by
  simp only [sqrt_eucSq_eq_dist]
  exact dist_triangle _ _ _

theorem eucSq_eq_sqrt_sq (x y : Point n) : eucSq x y = Real.sqrt (eucSq x y) ^ 2 :=
  (Real.sq_sqrt (eucSq_nonneg x y)).symm

theorem eucSq_pos_of_ne {x y : Point n} (h : x ≠ y) : 0 < eucSq x y := by
  rcases (eucSq_nonneg x y).lt_or_eq with h' | h'
  · exact h'
  · exfalso
    apply h
    funext i
    have hsum : ∑ j, (x j - y j) * (x j - y j) = 0 := by
      simpa [eucSq, dotProduct] using h'.symm
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg (x j - y j))).mp hsum i (Finset.mem_univ _)
    have := mul_self_eq_zero.mp hi
    linarith

/-- The sup norm is dominated by the Euclidean distance. -/
theorem norm_sub_le_sqrt_eucSq (x y : Point n) : ‖x - y‖ <= Real.sqrt (eucSq x y) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  have h := Finset.single_le_sum (f := fun j => (x - y) j * (x - y) j)
    (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
  simpa [eucSq, dotProduct, sq] using h

/-- The Euclidean distance is dominated by `n` times the sup norm (squared). -/
theorem eucSq_le_card_mul_norm_sq (x y : Point n) : eucSq x y <= n * ‖x - y‖ ^ 2 := by
  have h : ∀ i, (x - y) i * (x - y) i <= ‖x - y‖ ^ 2 := fun i => by
    have h1 : |(x - y) i| <= ‖x - y‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (x - y) i
    have h2 : (x - y) i * (x - y) i = |(x - y) i| ^ 2 := by rw [sq_abs, sq]
    rw [h2]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc
    eucSq x y = ∑ i, (x - y) i * (x - y) i := rfl
    _ <= ∑ _i : Fin n, ‖x - y‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = n * ‖x - y‖ ^ 2 := by simp

theorem abs_dotProduct_le (a b : Point n) : |dotProduct a b| <= n * (‖a‖ * ‖b‖) := by
  calc
    |dotProduct a b| = |∑ i, a i * b i| := rfl
    _ <= ∑ i, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _i : Fin n, ‖a‖ * ‖b‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm a i)
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm b i) (abs_nonneg _)
          (norm_nonneg _)
    _ = n * (‖a‖ * ‖b‖) := by simp

/--
Squared distance to the midpoint `(x₀ + y) / 2`:
`|x - (x₀ + y)/2|² = |x₀ - y|²/4 + |x - x₀|²/2 + (|x - y|² - |x₀ - y|²)/2`.
-/
theorem eucSq_midpoint (x x₀ y : Point n) :
    eucSq x ((1 / 2 : Real) • (x₀ + y)) =
      eucSq x₀ y / 4 + eucSq x x₀ / 2 + (eucSq x y - eucSq x₀ y) / 2 := by
  simp only [eucSq, dotProduct, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Expansion of `eucSq` around a base point. -/
theorem eucSq_sub_eucSq_base (x x₀ c : Point n) :
    eucSq x c - eucSq x₀ c =
      2 * dotProduct (x₀ - c) (x - x₀) + dotProduct (x - x₀) (x - x₀) := by
  simp only [eucSq, dotProduct, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### Trace comparison of semijets -/

theorem trace_eq_sum_quadraticForm (M : Hessian n) :
    Matrix.trace M =
      ∑ i, dotProduct (Matrix.mulVec M (Pi.single i 1)) (Pi.single i 1) := by
  simp [Matrix.trace, dotProduct_single]

/-- A full-neighbourhood superjet of the zero function has nonnegative trace. -/
theorem trace_nonneg_of_mem_superjet_zero_univ {x : Point n} {K : Jet n}
    (hK : K ∈ Superjet Set.univ (fun _ : Point n => (0 : Real)) x) :
    0 <= Matrix.trace K.hessian := by
  have hgrad := superjet_zero_univ_gradient_eq_zero hK
  rw [trace_eq_sum_quadraticForm]
  exact Finset.sum_nonneg fun i _ =>
    superjet_zero_univ_quadraticForm_nonneg_of_gradient_eq_zero hK hgrad _

/--
At an interior point, the trace of any subjet is at most the trace of any
superjet of the same function.
-/
theorem trace_hessian_le_of_mem_subjet_of_mem_superjet {C : Set (Point n)}
    {u : Point n -> Real} {x : Point n} {J K : Jet n} (hx : x ∈ interior C)
    (hJ : J ∈ Subjet C u x) (hK : K ∈ Superjet C u x) :
    Matrix.trace J.hessian <= Matrix.trace K.hessian := by
  have hKJ : K - J ∈ Superjet Set.univ (fun _ : Point n => (0 : Real)) x := by
    rw [← superjet_eq_univ_of_mem_interior hx]
    rcases hJ with ⟨rho, hrho, hJ⟩
    rcases hK with ⟨sigma, hsigma, hK⟩
    refine ⟨fun y => sigma y - rho y, semijetRemainder_sub hsigma hrho, ?_⟩
    filter_upwards [hJ, hK] with y hy1 hy2
    have hqsub := quadraticModel_sub x (u x) (u x) K.gradient J.gradient
      K.hessian J.hessian y
    rw [sub_self] at hqsub
    simp only [Jet.sub_gradient, Jet.sub_hessian]
    rw [hqsub]
    linarith
  have h := trace_nonneg_of_mem_superjet_zero_univ hKJ
  rw [Jet.sub_hessian, Matrix.trace_sub] at h
  linarith

/-! ### Scalar Taylor expansion -/

/--
Peano form of the second-order Taylor expansion of a scalar function whose
derivative is differentiable at the base point.
-/
theorem isLittleO_taylor_two_of_hasDerivAt {G G' : Real -> Real} {s₀ G₂ : Real}
    (hG : ∀ s, HasDerivAt G (G' s) s) (hG' : HasDerivAt G' G₂ s₀) :
    (fun s => G s - (G s₀ + G' s₀ * (s - s₀) + G₂ / 2 * (s - s₀) ^ 2)) =o[𝓝 s₀]
      fun s => (s - s₀) ^ 2 := by
  have hR : ∀ s ∈ (Set.univ : Set Real),
      HasDerivWithinAt
        (fun s => G s - (G s₀ + G' s₀ * (s - s₀) + G₂ / 2 * (s - s₀) ^ 2))
        (G' s - (G' s₀ + G₂ * (s - s₀))) Set.univ s := by
    intro s _
    have hlin : HasDerivAt (fun s => s - s₀) 1 s := (hasDerivAt_id s).sub_const s₀
    have hmodel : HasDerivAt
        (fun s => G s₀ + G' s₀ * (s - s₀) + G₂ / 2 * (s - s₀) ^ 2)
        (G' s₀ + G₂ * (s - s₀)) s := by
      have h := ((hlin.const_mul (G' s₀)).const_add (G s₀)).add
        ((hlin.pow 2).const_mul (G₂ / 2))
      convert h using 1
      simp only [Nat.cast_ofNat, mul_one]
      ring
    exact ((hG s).sub hmodel).hasDerivWithinAt
  have hR' : (fun s => G' s - (G' s₀ + G₂ * (s - s₀))) =o[𝓝[Set.univ] s₀]
      fun s => (s - s₀) ^ 1 := by
    rw [nhdsWithin_univ]
    refine (hasDerivAt_iff_isLittleO.mp hG').congr (fun s => ?_) (fun s => ?_)
    · simp only [smul_eq_mul]
      ring
    · ring
  have h := Convex.isLittleO_pow_succ_real convex_univ (Set.mem_univ s₀) hR hR'
  rw [nhdsWithin_univ] at h
  simpa using h

/-! ### Radial functions -/

/-- The second-order jet of `x ↦ G (eucSq x c)` at a point with `z = x̂ - c`. -/
def radialJet (G₁ G₂ : Real) (z : Point n) : Jet n :=
  ⟨(2 * G₁) • z, (2 * G₁) • (1 : Hessian n) + (4 * G₂) • Matrix.vecMulVec z z⟩

theorem trace_radialJet_hessian (G₁ G₂ : Real) (z : Point n) :
    Matrix.trace (radialJet G₁ G₂ z).hessian =
      2 * G₁ * n + 4 * G₂ * dotProduct z z := by
  simp [radialJet, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    Matrix.trace_vecMulVec]

theorem quadraticModel_radialJet (x₀ : Point n) (r G₁ G₂ : Real) (z x : Point n) :
    quadraticModel x₀ r (radialJet G₁ G₂ z).gradient (radialJet G₁ G₂ z).hessian x =
      r + G₁ * (2 * dotProduct z (x - x₀) + dotProduct (x - x₀) (x - x₀)) +
        2 * G₂ * dotProduct z (x - x₀) ^ 2 := by
  have hvv : dotProduct (Matrix.mulVec (Matrix.vecMulVec z z) (x - x₀)) (x - x₀) =
      dotProduct z (x - x₀) ^ 2 := by
    rw [Matrix.vecMulVec_mulVec]
    rw [op_smul_eq_smul, smul_dotProduct, smul_eq_mul]
    ring
  simp only [quadraticModel, radialJet, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, add_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [hvv]
  ring

/--
Second-order expansion of a radial function `x ↦ G (eucSq x c)` from a scalar
second-order Peano expansion of `G` at `s₀ = eucSq x̂ c`.
-/
theorem hasSecondOrderExpansionWithin_comp_eucSq {C : Set (Point n)}
    {G : Real -> Real} {G₁ G₂ : Real} {c x₀ : Point n}
    (hG : (fun s => G s - (G (eucSq x₀ c) + G₁ * (s - eucSq x₀ c) +
        G₂ / 2 * (s - eucSq x₀ c) ^ 2)) =o[𝓝 (eucSq x₀ c)]
      fun s => (s - eucSq x₀ c) ^ 2) :
    HasSecondOrderExpansionWithin C (fun x => G (eucSq x c)) x₀
      (radialJet G₁ G₂ (x₀ - c)) := by
  set s₀ := eucSq x₀ c with hs₀
  set z := x₀ - c with hz
  set E : Real -> Real := fun s => G s - (G s₀ + G₁ * (s - s₀) + G₂ / 2 * (s - s₀) ^ 2)
    with hE
  have key : ∀ S d1 d2 GS : Real, S - s₀ = 2 * d1 + d2 ->
      GS - (G s₀ + G₁ * (2 * d1 + d2) + 2 * G₂ * d1 ^ 2) =
        (GS - (G s₀ + G₁ * (S - s₀) + G₂ / 2 * (S - s₀) ^ 2)) +
          G₂ / 2 * (d2 * (d2 + 4 * d1)) := by
    intro S d1 d2 GS h
    rw [h]
    ring
  have hrem : ∀ x : Point n,
      G (eucSq x c) - quadraticModel x₀ (G s₀) (radialJet G₁ G₂ z).gradient
          (radialJet G₁ G₂ z).hessian x =
        E (eucSq x c) + G₂ / 2 * (dotProduct (x - x₀) (x - x₀) *
          (dotProduct (x - x₀) (x - x₀) + 4 * dotProduct z (x - x₀))) := by
    intro x
    rw [quadraticModel_radialJet]
    exact key _ _ _ _ (eucSq_sub_eucSq_base x x₀ c)
  refine ⟨fun x => G (eucSq x c) - quadraticModel x₀ (G s₀) (radialJet G₁ G₂ z).gradient
    (radialJet G₁ G₂ z).hessian x, ?_, Eventually.of_forall fun x => by ring⟩
  -- The remainder is `o(‖x - x₀‖²)` on the full neighbourhood filter.
  have hcont : Tendsto (fun x : Point n => eucSq x c) (𝓝 x₀) (𝓝 s₀) :=
    ((continuous_eucSq.comp (continuous_id.prodMk continuous_const)).tendsto x₀)
  have hSO : (fun x : Point n => eucSq x c - s₀) =O[𝓝 x₀] fun x => ‖x - x₀‖ := by
    refine IsBigO.of_bound (2 * n * ‖z‖ + n) ?_
    filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    have hd : ‖x - x₀‖ <= 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      exact hx.le
    have h1 := abs_dotProduct_le z (x - x₀)
    have h2 := abs_dotProduct_le (x - x₀) (x - x₀)
    rw [eucSq_sub_eucSq_base, Real.norm_eq_abs, norm_norm]
    set t := ‖x - x₀‖
    have ht : 0 <= t := norm_nonneg _
    have hz0 : 0 <= ‖z‖ := norm_nonneg _
    have hn0 : (0 : Real) <= n := Nat.cast_nonneg n
    calc
      |2 * dotProduct (x₀ - c) (x - x₀) + dotProduct (x - x₀) (x - x₀)|
          <= 2 * |dotProduct z (x - x₀)| + |dotProduct (x - x₀) (x - x₀)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_two]
      _ <= 2 * (n * (‖z‖ * t)) + n * (t * t) := by linarith
      _ <= (2 * n * ‖z‖ + n) * t := by nlinarith [mul_le_mul_of_nonneg_left hd ht]
  have hE' : (fun x : Point n => E (eucSq x c)) =o[𝓝 x₀] fun x => ‖x - x₀‖ ^ 2 :=
    (hG.comp_tendsto hcont).trans_isBigO (hSO.pow 2)
  have hpoly : (fun x : Point n => G₂ / 2 * (dotProduct (x - x₀) (x - x₀) *
      (dotProduct (x - x₀) (x - x₀) + 4 * dotProduct z (x - x₀)))) =o[𝓝 x₀]
      fun x => ‖x - x₀‖ ^ 2 := by
    have hO : (fun x : Point n => dotProduct (x - x₀) (x - x₀)) =O[𝓝 x₀]
        fun x => ‖x - x₀‖ ^ 2 := by
      refine IsBigO.of_bound n (Eventually.of_forall fun x => ?_)
      have h2 := abs_dotProduct_le (x - x₀) (x - x₀)
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity : (0 : Real) <= ‖x - x₀‖ ^ 2), sq]
      linarith
    have ho : (fun x : Point n => dotProduct (x - x₀) (x - x₀) +
        4 * dotProduct z (x - x₀)) =o[𝓝 x₀] fun _ => (1 : Real) := by
      rw [isLittleO_one_iff]
      have hc : Continuous fun x : Point n => dotProduct (x - x₀) (x - x₀) +
          4 * dotProduct z (x - x₀) := by fun_prop
      simpa using hc.tendsto x₀
    have h := (hO.mul_isLittleO ho).const_mul_left (G₂ / 2)
    simpa using h
  have htot := (hE'.add hpoly).mono (nhdsWithin_le_nhds (s := C))
  exact htot.congr_left fun x => (hrem x).symm

/-! ### The exponential profile -/

/-- The exponential radial profile `s ↦ a - k exp (-α (s - ρ))`. -/
def expProfile (a k α ρ s : Real) : Real :=
  a - k * Real.exp (-(α * (s - ρ)))

theorem hasDerivAt_expProfile (a k α ρ s : Real) :
    HasDerivAt (expProfile a k α ρ) (k * α * Real.exp (-(α * (s - ρ)))) s := by
  have h1 : HasDerivAt (fun s => -(α * (s - ρ))) (-(α * 1)) s :=
    (((hasDerivAt_id s).sub_const ρ).const_mul α).neg
  have h := (h1.exp.const_mul k).const_sub a
  change HasDerivAt (fun s => a - k * Real.exp (-(α * (s - ρ)))) _ s
  convert h using 1
  ring

theorem hasDerivAt_expProfile_deriv (k α ρ s : Real) :
    HasDerivAt (fun s => k * α * Real.exp (-(α * (s - ρ))))
      (-(k * α ^ 2 * Real.exp (-(α * (s - ρ))))) s := by
  have h1 : HasDerivAt (fun s => -(α * (s - ρ))) (-(α * 1)) s :=
    (((hasDerivAt_id s).sub_const ρ).const_mul α).neg
  have h := h1.exp.const_mul (k * α)
  convert h using 1
  ring

/-- The radial jet of the exponential profile at `x₀`. -/
def expProfileJet (k α ρ : Real) (c x₀ : Point n) : Jet n :=
  radialJet (k * α * Real.exp (-(α * (eucSq x₀ c - ρ))))
    (-(k * α ^ 2 * Real.exp (-(α * (eucSq x₀ c - ρ))))) (x₀ - c)

theorem hasSecondOrderExpansionWithin_expProfile (C : Set (Point n))
    (a k α ρ : Real) (c x₀ : Point n) :
    HasSecondOrderExpansionWithin C (fun x => expProfile a k α ρ (eucSq x c)) x₀
      (expProfileJet k α ρ c x₀) :=
  hasSecondOrderExpansionWithin_comp_eucSq
    (isLittleO_taylor_two_of_hasDerivAt (hasDerivAt_expProfile a k α ρ)
      (hasDerivAt_expProfile_deriv k α ρ _))

theorem trace_expProfileJet_hessian (k α ρ : Real) (c x₀ : Point n) :
    Matrix.trace (expProfileJet k α ρ c x₀).hessian =
      2 * k * α * Real.exp (-(α * (eucSq x₀ c - ρ))) * (n - 2 * α * eucSq x₀ c) := by
  rw [expProfileJet, trace_radialJet_hessian]
  change _ + _ * eucSq x₀ c = _
  ring

/-- Radial superharmonicity of the exponential profile when `k ≥ 0`. -/
theorem trace_expProfileJet_hessian_nonpos {k α ρ : Real} (hk : 0 <= k) (hα : 0 <= α)
    {c x₀ : Point n} (hs : (n : Real) <= 2 * α * eucSq x₀ c) :
    Matrix.trace (expProfileJet k α ρ c x₀).hessian <= 0 := by
  rw [trace_expProfileJet_hessian]
  have he := Real.exp_pos (-(α * (eucSq x₀ c - ρ)))
  have h1 : 0 <= 2 * k * α * Real.exp (-(α * (eucSq x₀ c - ρ))) := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos h1 (by linarith)

/-! ### Scalar inequalities for the barrier profile -/

/-- Concavity of the square root: `√a ≤ √b + (a - b) / (2 √b)`. -/
theorem sqrt_le_sqrt_add_div {a b : Real} (ha : 0 <= a) (hb : 0 < b) :
    Real.sqrt a <= Real.sqrt b + (a - b) / (2 * Real.sqrt b) := by
  set t := Real.sqrt a
  set u := Real.sqrt b
  have hu : 0 < u := Real.sqrt_pos.2 hb
  have hat : a = t ^ 2 := (Real.sq_sqrt ha).symm
  have hbu : b = u ^ 2 := (Real.sq_sqrt hb.le).symm
  have hid : u + (a - b) / (2 * u) - t = (t - u) ^ 2 / (2 * u) := by
    rw [hat, hbu]
    field_simp
    ring
  have : 0 <= (t - u) ^ 2 / (2 * u) := by positivity
  linarith

theorem one_sub_exp_neg_le (u : Real) : 1 - Real.exp (-u) <= u := by
  linarith [Real.add_one_le_exp (-u)]

theorem mul_exp_neg_le_one_sub_exp_neg (u : Real) :
    u * Real.exp (-u) <= 1 - Real.exp (-u) := by
  have h := Real.add_one_le_exp u
  have he : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-u)
  nlinarith

end ViscositySolns
