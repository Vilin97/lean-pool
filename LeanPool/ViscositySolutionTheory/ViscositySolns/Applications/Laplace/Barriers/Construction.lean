/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Barriers.Radial
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Comparison
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Envelopes

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Exterior-sphere barriers for the Laplace operator

Let `C` be a bounded open set satisfying the uniform exterior sphere condition
with radius `R`, and let `g` be `L`-Lipschitz on `closure C` for the Euclidean
distance. We build a Perron barrier pair for `-Δu = 0` with boundary data `g`.

*Parameter set.* `P` consists of all pairs `(x₀, y)` with `x₀ ∈ frontier C` and
`y` the centre of an admissible exterior sphere of radius `R` at `x₀`. It is
compact, and using all admissible centres avoids choosing `y` continuously.

*Profile.* For `p = (x₀, y) ∈ P` let `c = (x₀ + y)/2` and
`τ(x) = |x - c|² - R²/4`. On `closure C` one has `τ ≥ |x - x₀|²/2` and
`τ ≤ |x - x₀|² + R |x - x₀|`. The profile is
`Φ_p(x) = √(1 - exp (-α τ(x)))` with `α = 2 (n + 1) / R²`, which is comparable
to `|x - x₀|` from below and to `|x - x₀|^{1/2}` from above.

*Upper barrier.* `U_g(x) = inf_{p ∈ P} (g x₀ + A Φ_p(x))`. At a point of `C`
the infimum is attained at some `p̂`; by concavity of the square root, the
branch at `p̂` lies below the exponential radial function
`W = const - k exp (-α τ)`, which touches it at the point and has
nonpositive Laplacian because `2 α |x - c|² ≥ n + 1`. Hence every subjet of
`U_g` has nonnegative `-trace`.

*Lower barrier.* `-U_{-g}`, using that the Laplace operator is self-dual.
-/

@[expose] public noncomputable section

open Filter Topology

namespace ViscositySolns

variable {n : Nat}

/-! ### The parameter set -/

/-- Frontier points of `C` together with all admissible exterior-sphere centres. -/
def exteriorSphereParams (C : Set (Point n)) (R : Real) : Set (Point n × Point n) :=
  {p | p.1 ∈ frontier C ∧ eucSq p.1 p.2 = R ^ 2 ∧ ∀ x ∈ closure C, R ^ 2 <= eucSq x p.2}

/-- The midpoint `(x₀ + y) / 2` of a frontier point and a sphere centre. -/
def sphereMidpoint (p : Point n × Point n) : Point n :=
  (1 / 2 : Real) • (p.1 + p.2)

theorem isClosed_exteriorSphereParams (C : Set (Point n)) (R : Real) :
    IsClosed (exteriorSphereParams C R) := by
  have h1 : IsClosed {p : Point n × Point n | p.1 ∈ frontier C} :=
    isClosed_frontier.preimage continuous_fst
  have h2 : IsClosed {p : Point n × Point n | eucSq p.1 p.2 = R ^ 2} :=
    isClosed_eq continuous_eucSq continuous_const
  have h3 : IsClosed {p : Point n × Point n | ∀ x ∈ closure C, R ^ 2 <= eucSq x p.2} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_le continuous_const
        (continuous_eucSq.comp (continuous_const.prodMk continuous_snd))
  exact h1.inter (h2.inter h3)

theorem isCompact_exteriorSphereParams {C : Set (Point n)}
    (hCbdd : Bornology.IsBounded C) (R : Real) :
    IsCompact (exteriorSphereParams C R) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_exteriorSphereParams C R) ?_
  obtain ⟨M, hM⟩ := hCbdd.closure.exists_norm_le
  refine isBounded_iff_forall_norm_le.2 ⟨M + |R|, fun p hp => ?_⟩
  have h1 : ‖p.1‖ <= M := hM _ (frontier_subset_closure hp.1)
  have h2 : ‖p.1 - p.2‖ <= |R| := by
    have h := norm_sub_le_sqrt_eucSq p.1 p.2
    rwa [hp.2.1, Real.sqrt_sq_eq_abs] at h
  have h3 : ‖p.2‖ <= ‖p.1‖ + ‖p.1 - p.2‖ := by
    have h := norm_sub_le p.1 (p.1 - p.2)
    rwa [sub_sub_cancel] at h
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩ <;> linarith [abs_nonneg R]

theorem nonempty_exteriorSphereParams {C : Set (Point n)} {R : Real}
    (hext : UniformExteriorSphereSq C R) {x₀ : Point n} (hx₀ : x₀ ∈ frontier C) :
    ∃ y, (x₀, y) ∈ exteriorSphereParams C R := by
  obtain ⟨y, hy, hyC⟩ := hext.2 x₀ hx₀
  exact ⟨y, hx₀, hy, hyC⟩

/-- The squared distance from the midpoint, shifted by `R²/4`, controls
`|x - x₀|²/2` from above on `closure C`. -/
theorem half_eucSq_le_eucSq_sphereMidpoint {C : Set (Point n)} {R : Real}
    {p : Point n × Point n} (hp : p ∈ exteriorSphereParams C R) {x : Point n}
    (hx : x ∈ closure C) :
    eucSq x p.1 / 2 <= eucSq x (sphereMidpoint p) - R ^ 2 / 4 := by
  rw [sphereMidpoint, eucSq_midpoint, hp.2.1]
  have := hp.2.2 x hx
  linarith

theorem eucSq_sphereMidpoint_le {C : Set (Point n)} {R : Real} (hR : 0 < R)
    {p : Point n × Point n} (hp : p ∈ exteriorSphereParams C R) (x : Point n) :
    eucSq x (sphereMidpoint p) - R ^ 2 / 4 <=
      eucSq x p.1 + R * Real.sqrt (eucSq x p.1) := by
  rw [sphereMidpoint, eucSq_midpoint, hp.2.1]
  have htri := sqrt_eucSq_triangle x p.1 p.2
  rw [hp.2.1, Real.sqrt_sq hR.le] at htri
  have h1 : eucSq x p.2 <= (Real.sqrt (eucSq x p.1) + R) ^ 2 := by
    rw [eucSq_eq_sqrt_sq x p.2]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) htri 2
  have h2 := eucSq_eq_sqrt_sq x p.1
  generalize eucSq x p.2 = e' at h1 ⊢
  generalize Real.sqrt (eucSq x p.1) = δ at h1 h2 ⊢
  generalize eucSq x p.1 = e at h2 ⊢
  nlinarith

theorem eucSq_sphereMidpoint_self {C : Set (Point n)} {R : Real}
    {p : Point n × Point n} (hp : p ∈ exteriorSphereParams C R) :
    eucSq p.1 (sphereMidpoint p) = R ^ 2 / 4 := by
  rw [sphereMidpoint, eucSq_midpoint, hp.2.1, eucSq_self]
  ring

/-! ### The barrier profile -/

/-- The exponential rate `α = 2 (n + 1) / R²` of the barrier profile. -/
def laplaceBarrierRate (n : Nat) (R : Real) : Real :=
  2 * (n + 1) / R ^ 2

theorem laplaceBarrierRate_pos {R : Real} (hR : 0 < R) : 0 < laplaceBarrierRate n R := by
  unfold laplaceBarrierRate
  positivity

theorem two_mul_laplaceBarrierRate_mul {R : Real} (hR : 0 < R) :
    2 * laplaceBarrierRate n R * (R ^ 2 / 4) = n + 1 := by
  unfold laplaceBarrierRate
  field_simp
  ring

/-- The profile `Φ_p(x) = √(1 - exp (-α (|x - c_p|² - R²/4)))`. -/
def laplaceBarrierProfile (α R : Real) (p : Point n × Point n) (x : Point n) : Real :=
  Real.sqrt (1 - Real.exp (-(α * (eucSq x (sphereMidpoint p) - R ^ 2 / 4))))

theorem Continuous.laplaceBarrierProfile {X : Type*} [TopologicalSpace X] (α R : Real)
    {f : X -> Point n × Point n} {h : X -> Point n} (hf : Continuous f) (hh : Continuous h) :
    Continuous fun t => laplaceBarrierProfile α R (f t) (h t) := by
  have hm : Continuous fun t => sphereMidpoint (f t) := by
    unfold sphereMidpoint
    fun_prop
  have he : Continuous fun t => eucSq (h t) (sphereMidpoint (f t)) :=
    continuous_eucSq.comp (hh.prodMk hm)
  exact Real.continuous_sqrt.comp (continuous_const.sub
    (Real.continuous_exp.comp ((continuous_const.mul (he.sub continuous_const)).neg)))

theorem laplaceBarrierProfile_self {C : Set (Point n)} {R α : Real}
    {p : Point n × Point n} (hp : p ∈ exteriorSphereParams C R) :
    laplaceBarrierProfile α R p p.1 = 0 := by
  simp [laplaceBarrierProfile, eucSq_sphereMidpoint_self hp]

theorem sqrt_mul_sqrt_le_sqrt_one_sub_exp {α T τ e : Real} (hα : 0 < α)
    (hτ : e / 2 <= τ) (hτT : τ <= T) (he : 0 <= e) :
    Real.sqrt (α * Real.exp (-(α * T)) / 2) * Real.sqrt e <=
      Real.sqrt (1 - Real.exp (-(α * τ))) := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hτ0 : 0 <= τ := by linarith
  have h1 : Real.exp (-(α * T)) <= Real.exp (-(α * τ)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h2 := mul_exp_neg_le_one_sub_exp_neg (α * τ)
  calc
    α * Real.exp (-(α * T)) / 2 * e = α * Real.exp (-(α * T)) * (e / 2) := by ring
    _ <= α * Real.exp (-(α * T)) * τ := mul_le_mul_of_nonneg_left hτ (by positivity)
    _ = α * τ * Real.exp (-(α * T)) := by ring
    _ <= α * τ * Real.exp (-(α * τ)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ <= _ := h2

theorem sqrt_one_sub_exp_le_sqrt_mul_sqrt {α R Δ δ τ : Real} (hα : 0 <= α)
    (hR : 0 <= R) (hδ : 0 <= δ) (hδΔ : δ <= Δ) (hτ : τ <= δ ^ 2 + R * δ) :
    Real.sqrt (1 - Real.exp (-(α * τ))) <= Real.sqrt (α * (Δ + R)) * Real.sqrt δ := by
  have hΔ : 0 <= Δ := hδ.trans hδΔ
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  calc
    1 - Real.exp (-(α * τ)) <= α * τ := one_sub_exp_neg_le _
    _ <= α * (δ ^ 2 + R * δ) := mul_le_mul_of_nonneg_left hτ hα
    _ <= α * ((Δ + R) * δ) := mul_le_mul_of_nonneg_left (by nlinarith) hα
    _ = α * (Δ + R) * δ := by ring

/-- The lower constant `c` with `√c |x - x₀| ≤ Φ_p(x)` on `closure C`. -/
def laplaceBarrierLowerConst (n : Nat) (R D : Real) : Real :=
  laplaceBarrierRate n R * Real.exp (-(laplaceBarrierRate n R * (D + R * Real.sqrt D))) / 2

theorem laplaceBarrierLowerConst_pos {R : Real} (hR : 0 < R) (D : Real) :
    0 < laplaceBarrierLowerConst n R D := by
  unfold laplaceBarrierLowerConst
  have := laplaceBarrierRate_pos (n := n) hR
  positivity

/-- The profile grows at least linearly in the Euclidean distance to `x₀`. -/
theorem sqrt_lowerConst_mul_le_laplaceBarrierProfile {C : Set (Point n)} {R D : Real}
    (hR : 0 < R) (hD : ∀ x ∈ closure C, ∀ y ∈ closure C, eucSq x y <= D)
    {p : Point n × Point n} (hp : p ∈ exteriorSphereParams C R) {x : Point n}
    (hx : x ∈ closure C) :
    Real.sqrt (laplaceBarrierLowerConst n R D) * Real.sqrt (eucSq x p.1) <=
      laplaceBarrierProfile (laplaceBarrierRate n R) R p x := by
  have hp1 : p.1 ∈ closure C := frontier_subset_closure hp.1
  have hτ := half_eucSq_le_eucSq_sphereMidpoint hp hx
  have hτT := eucSq_sphereMidpoint_le hR hp x
  have hδD : Real.sqrt (eucSq x p.1) <= Real.sqrt D := Real.sqrt_le_sqrt (hD x hx _ hp1)
  have heD := hD x hx _ hp1
  have hT : eucSq x (sphereMidpoint p) - R ^ 2 / 4 <= D + R * Real.sqrt D := by
    nlinarith [mul_le_mul_of_nonneg_left hδD hR.le]
  exact sqrt_mul_sqrt_le_sqrt_one_sub_exp (laplaceBarrierRate_pos hR) hτ hT
    (eucSq_nonneg _ _)

/-- The profile is Hölder-`1/2` in the Euclidean distance to `x₀`. -/
theorem laplaceBarrierProfile_le {C : Set (Point n)} {R D : Real}
    (hR : 0 < R) (hD : ∀ x ∈ closure C, ∀ y ∈ closure C, eucSq x y <= D)
    {p : Point n × Point n} (hp : p ∈ exteriorSphereParams C R) {x : Point n}
    (hx : x ∈ closure C) :
    laplaceBarrierProfile (laplaceBarrierRate n R) R p x <=
      Real.sqrt (laplaceBarrierRate n R * (Real.sqrt D + R)) *
        Real.sqrt (Real.sqrt (eucSq x p.1)) := by
  have hp1 : p.1 ∈ closure C := frontier_subset_closure hp.1
  have hδD : Real.sqrt (eucSq x p.1) <= Real.sqrt D := Real.sqrt_le_sqrt (hD x hx _ hp1)
  have hτ := eucSq_sphereMidpoint_le hR hp x
  unfold laplaceBarrierProfile
  refine sqrt_one_sub_exp_le_sqrt_mul_sqrt (laplaceBarrierRate_pos hR).le hR.le
    (Real.sqrt_nonneg _) hδD ?_
  rw [← eucSq_eq_sqrt_sq]
  exact hτ

/-! ### The upper barrier -/

/-- One branch `g x₀ + A Φ_p` of the upper barrier. -/
def laplaceBarrierBranch (R A : Real) (g : Point n -> Real) (p : Point n × Point n)
    (x : Point n) : Real :=
  g p.1 + A * laplaceBarrierProfile (laplaceBarrierRate n R) R p x

/-- The upper barrier `U_g = inf_{p ∈ P} (g x₀ + A Φ_p)`. -/
def laplaceUpperBarrier (C : Set (Point n)) (R A : Real) (g : Point n -> Real)
    (x : Point n) : Real :=
  sInf ((fun p => laplaceBarrierBranch R A g p x) '' exteriorSphereParams C R)

section UpperBarrier

variable {C : Set (Point n)} {R A : Real} {g : Point n -> Real}

theorem continuousOn_laplaceBarrierBranch (hgc : ContinuousOn g (closure C)) (x : Point n) :
    ContinuousOn (fun p => laplaceBarrierBranch R A g p x) (exteriorSphereParams C R) := by
  have h1 : ContinuousOn (fun p : Point n × Point n => g p.1) (exteriorSphereParams C R) :=
    hgc.comp continuous_fst.continuousOn fun p hp => frontier_subset_closure hp.1
  have h2 : Continuous fun p : Point n × Point n =>
      laplaceBarrierProfile (laplaceBarrierRate n R) R p x :=
    Continuous.laplaceBarrierProfile _ R (f := fun p => p) (h := fun _ => x) continuous_id
      continuous_const
  exact h1.add (continuous_const.mul h2).continuousOn

theorem continuous_laplaceUpperBarrier (hCbdd : Bornology.IsBounded C)
    (hgc : ContinuousOn g (closure C)) :
    Continuous (laplaceUpperBarrier C R A g) := by
  have hPc := isCompact_exteriorSphereParams hCbdd (n := n) R
  have : CompactSpace (exteriorSphereParams C R) := isCompact_iff_compactSpace.mp hPc
  have h1 : Continuous fun q : Point n × exteriorSphereParams C R => g q.2.1.1 :=
    hgc.comp_continuous (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
      fun q => frontier_subset_closure q.2.2.1
  have h2 : Continuous fun q : Point n × exteriorSphereParams C R =>
      laplaceBarrierProfile (laplaceBarrierRate n R) R q.2.1 q.1 :=
    Continuous.laplaceBarrierProfile _ R
      (f := fun q : Point n × exteriorSphereParams C R => q.2.1) (h := fun q => q.1)
      (continuous_subtype_val.comp continuous_snd) continuous_fst
  have hf : Continuous fun q : Point n × exteriorSphereParams C R =>
      laplaceBarrierBranch R A g q.2.1 q.1 :=
    h1.add (continuous_const.mul h2)
  have h := isCompact_univ.continuous_sInf
    (f := fun x (q : exteriorSphereParams C R) => laplaceBarrierBranch R A g q.1 x) hf
  have himg : ∀ x : Point n,
      (fun p => laplaceBarrierBranch R A g p x) '' exteriorSphereParams C R =
        (fun q : exteriorSphereParams C R => laplaceBarrierBranch R A g q.1 x) '' Set.univ := by
    intro x
    rw [Set.image_univ, Set.image_eq_range]
  have hfun : laplaceUpperBarrier C R A g = fun x => sInf
      ((fun q : exteriorSphereParams C R => laplaceBarrierBranch R A g q.1 x) '' Set.univ) := by
    funext x
    rw [← himg]
    rfl
  rw [hfun]
  exact h

theorem laplaceUpperBarrier_le (hCbdd : Bornology.IsBounded C)
    (hgc : ContinuousOn g (closure C)) {p : Point n × Point n}
    (hp : p ∈ exteriorSphereParams C R) (x : Point n) :
    laplaceUpperBarrier C R A g x <= laplaceBarrierBranch R A g p x :=
  csInf_le ((isCompact_exteriorSphereParams hCbdd R).image_of_continuousOn
    (continuousOn_laplaceBarrierBranch hgc x)).bddBelow (Set.mem_image_of_mem _ hp)

theorem le_laplaceUpperBarrier {x₀ : Point n} (hx₀ : x₀ ∈ frontier C)
    (hext : UniformExteriorSphereSq C R) {b : Real} (x : Point n)
    (hb : ∀ p ∈ exteriorSphereParams C R, b <= laplaceBarrierBranch R A g p x) :
    b <= laplaceUpperBarrier C R A g x := by
  obtain ⟨y, hy⟩ := nonempty_exteriorSphereParams hext hx₀
  refine le_csInf ⟨_, Set.mem_image_of_mem _ hy⟩ ?_
  rintro _ ⟨p, hp, rfl⟩
  exact hb p hp

theorem exists_laplaceUpperBarrier_eq (hCbdd : Bornology.IsBounded C)
    (hgc : ContinuousOn g (closure C)) {x₀ : Point n} (hx₀ : x₀ ∈ frontier C)
    (hext : UniformExteriorSphereSq C R) (x : Point n) :
    ∃ p ∈ exteriorSphereParams C R,
      laplaceBarrierBranch R A g p x = laplaceUpperBarrier C R A g x := by
  obtain ⟨y, hy⟩ := nonempty_exteriorSphereParams hext hx₀
  have h := ((isCompact_exteriorSphereParams hCbdd R).image_of_continuousOn
    (continuousOn_laplaceBarrierBranch (A := A) hgc x)).sInf_mem
    ⟨_, Set.mem_image_of_mem _ hy⟩
  exact h

/-- Scalar form of the touching inequality: by concavity of `√`, the branch
`gp + A √(1 - e)` lies below the affine function of `e` tangent at `e₀`. -/
theorem add_mul_sqrt_one_sub_le {gp A e₀ e : Real} (hA : 0 <= A) (he₀ : e₀ < 1)
    (he : e <= 1) :
    gp + A * Real.sqrt (1 - e) <=
      gp + A * Real.sqrt (1 - e₀) + A / (2 * Real.sqrt (1 - e₀)) * e₀ -
        A / (2 * Real.sqrt (1 - e₀)) * e := by
  have hsq := sqrt_le_sqrt_add_div (a := 1 - e) (b := 1 - e₀) (by linarith) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hsq hA
  have hid : A * (Real.sqrt (1 - e₀) + (1 - e - (1 - e₀)) / (2 * Real.sqrt (1 - e₀))) =
      A * Real.sqrt (1 - e₀) + A / (2 * Real.sqrt (1 - e₀)) * e₀ -
        A / (2 * Real.sqrt (1 - e₀)) * e := by
    ring
  linarith

/-- The upper barrier is a viscosity supersolution of `-Δu = 0` on `C`. -/
theorem viscositySupersolution_laplaceUpperBarrier (hCopen : IsOpen C)
    (hCbdd : Bornology.IsBounded C) (hext : UniformExteriorSphereSq C R) (hA : 0 <= A)
    (hgc : ContinuousOn g (closure C)) {x₀ : Point n} (hx₀ : x₀ ∈ frontier C) :
    ViscositySupersolution C laplaceOperator (laplaceUpperBarrier C R A g) := by
  have hR := hext.1
  refine ⟨(continuous_laplaceUpperBarrier hCbdd hgc).continuousOn.lowerSemicontinuousOn,
    fun x hx J hJ => ?_⟩
  obtain ⟨p, hp, hpx⟩ := exists_laplaceUpperBarrier_eq (A := A) hCbdd hgc hx₀ hext x
  have hα : 0 < laplaceBarrierRate n R := laplaceBarrierRate_pos hR
  have hxC : x ∈ closure C := subset_closure hx
  have hne : x ≠ p.1 := by
    intro hxp
    have h := hp.1
    rw [hCopen.frontier_eq, ← hxp] at h
    exact h.2 hx
  have hτx : 0 < eucSq x (sphereMidpoint p) - R ^ 2 / 4 := by
    have h1 := half_eucSq_le_eucSq_sphereMidpoint hp hxC
    have h2 := eucSq_pos_of_ne hne
    linarith
  obtain ⟨E, hE⟩ : ∃ E : Point n -> Real, E = fun y =>
      Real.exp (-(laplaceBarrierRate n R * (eucSq y (sphereMidpoint p) - R ^ 2 / 4))) :=
    ⟨_, rfl⟩
  have hbranch : ∀ y, laplaceBarrierBranch R A g p y = g p.1 + A * Real.sqrt (1 - E y) :=
    fun y => by rw [hE]; rfl
  have hE_le : ∀ y ∈ closure C, E y <= 1 := by
    intro y hy
    have h1 := half_eucSq_le_eucSq_sphereMidpoint hp hy
    have h2 := eucSq_nonneg y p.1
    have hτ : 0 <= eucSq y (sphereMidpoint p) - R ^ 2 / 4 := by linarith
    rw [hE, ← Real.exp_zero]
    exact Real.exp_le_exp.2 (neg_nonpos.2 (mul_nonneg hα.le hτ))
  have hEx : E x < 1 := by
    rw [hE, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (neg_neg_of_pos (mul_pos hα hτx))
  -- The touching exponential radial function.
  let k : Real := A / (2 * Real.sqrt (1 - E x))
  let a : Real := g p.1 + A * Real.sqrt (1 - E x) + k * E x
  have hWE : ∀ y, expProfile a k (laplaceBarrierRate n R) (R ^ 2 / 4)
      (eucSq y (sphereMidpoint p)) = a - k * E y := fun y => by rw [hE]; rfl
  have hW_ge : ∀ y ∈ closure C, laplaceBarrierBranch R A g p y <=
      expProfile a k (laplaceBarrierRate n R) (R ^ 2 / 4) (eucSq y (sphereMidpoint p)) := by
    intro y hy
    rw [hbranch, hWE]
    exact add_mul_sqrt_one_sub_le hA hEx (hE_le y hy)
  have hW_eq : expProfile a k (laplaceBarrierRate n R) (R ^ 2 / 4)
      (eucSq x (sphereMidpoint p)) = laplaceUpperBarrier C R A g x := by
    rw [hWE, ← hpx, hbranch]
    ring
  have htouch : TouchesAboveOn C (laplaceUpperBarrier C R A g)
      (fun y => expProfile a k (laplaceBarrierRate n R) (R ^ 2 / 4)
        (eucSq y (sphereMidpoint p))) x := by
    unfold TouchesAboveOn
    filter_upwards [self_mem_nhdsWithin] with y hy
    have h1 := laplaceUpperBarrier_le (A := A) hCbdd hgc hp y
    have h2 := hW_ge y (subset_closure hy)
    rw [hW_eq, sub_self]
    linarith
  have hK := superjet_of_touchesAbove_hasSecondOrderExpansionWithin htouch
    (hasSecondOrderExpansionWithin_expProfile C a k (laplaceBarrierRate n R) (R ^ 2 / 4)
      (sphereMidpoint p) x)
  have hxint : x ∈ interior C := mem_interior_iff_mem_nhds.2 (hCopen.mem_nhds hx)
  have htr := trace_hessian_le_of_mem_subjet_of_mem_superjet hxint hJ hK
  have hs : (n : Real) <= 2 * laplaceBarrierRate n R * eucSq x (sphereMidpoint p) := by
    have h1 := two_mul_laplaceBarrierRate_mul (n := n) hR
    have h2 := mul_le_mul_of_nonneg_left (le_of_lt (sub_pos.1 hτx))
      (by positivity : (0 : Real) <= 2 * laplaceBarrierRate n R)
    linarith
  have hk : 0 <= k := by positivity
  have hneg := trace_expProfileJet_hessian_nonpos (ρ := R ^ 2 / 4) hk hα.le hs
  rw [laplaceOperator_apply]
  linarith

end UpperBarrier

end ViscositySolns
