import Mathlib.Analysis.ODE.Gronwall

/-!
# Forward Euler Method

We implement the explicit Euler method for ODEs and prove its
convergence.

## Generic infrastructure

- `piecewiseLinear`, `piecewiseConst`: Piecewise linear/constant
  interpolation on a regular grid.
- `locallyFinite_Icc_grid`: The regular grid is locally finite.
- `ContinuousOn.of_Icc_grid`: Cell-wise continuity implies
  continuity on `[a, ∞)`.

## Euler method

- `ODE.EulerMethod.step`, `ODE.EulerMethod.point`,
  `ODE.EulerMethod.slope`: The Euler iteration.
- `ODE.EulerMethod.path`, `ODE.EulerMethod.deriv`: Piecewise
  linear/constant interpolation of the Euler points.
- `ODE.EulerMethod.dist_deriv_le`: Global bound on the local
  truncation error.
- `ODE.EulerMethod.dist_path_le`: Error bound via Gronwall's
  inequality.
- `ODE.EulerMethod.tendsto_path`: Convergence as `h → 0⁺`.
-/

open Set Filter

/-! ## Grid helpers -/

variable {α : Type*} [Field α] [LinearOrder α] [FloorSemiring α] [IsStrictOrderedRing α]

/-- If `t ∈ [a + n * h, a + (n + 1) * h)` and `0 < h`, then `⌊(t - a) / h⌋₊ = n`. -/
theorem Nat.floor_div_eq_of_mem_Ico {h : α} (hh : 0 < h) {a : α}
    {n : ℕ} {t : α} (ht : t ∈ Ico (a + n * h) (a + (n + 1) * h)) :
    ⌊(t - a) / h⌋₊ = n := by
  refine Nat.floor_eq_on_Ico n _ ⟨?_, ?_⟩ <;>
    (first | rw [le_div_iff₀ hh] | rw [div_lt_iff₀ hh]) <;> linarith [ht.1, ht.2]

/-- If `0 < h` and `a ≤ t`, then `t` lies in the floor interval
`[a + ⌊(t - a) / h⌋₊ * h, a + (⌊(t - a) / h⌋₊ + 1) * h)`. -/
theorem mem_Ico_Nat_floor_div {h : α} (hh : 0 < h) {a t : α} (hat : a ≤ t) :
    t ∈ Ico (a + ⌊(t - a) / h⌋₊ * h) (a + (↑⌊(t - a) / h⌋₊ + 1) * h) := by
  constructor <;> nlinarith [Nat.floor_le (div_nonneg (sub_nonneg.mpr hat) hh.le),
    Nat.lt_floor_add_one ((t - a) / h), mul_div_cancel₀ (t - a) hh.ne']

/-! ## Piecewise linear interpolation -/

/-- The piecewise linear interpolation of a sequence `y` with slopes `c` on a regular grid
with step size `h` starting at `a`. On `[a + n * h, a + (n + 1) * h)`, the value is
`y n + (t - (a + n * h)) • c n`. -/
noncomputable def piecewiseLinear {E : Type*} [AddCommGroup E] [Module α E]
    (y : ℕ → E) (c : ℕ → E) (h : α) (a : α) (t : α) : E :=
  let n := ⌊(t - a) / h⌋₊
  y n + (t - (a + n * h)) • c n

/-- The piecewise constant function taking value `c n` on `[a + n * h, a + (n + 1) * h)`. -/
noncomputable def piecewiseConst {E : Type*} (c : ℕ → E) (h : α) (a : α) (t : α) : E :=
  c ⌊(t - a) / h⌋₊

/-- The piecewise constant function equals `c n` on `[a + n * h, a + (n + 1) * h)`. -/
theorem piecewiseConst_eq_on_Ico {E : Type*} {c : ℕ → E} {h : α} {a : α}
    (hh : 0 < h) {n : ℕ} {t : α}
    (ht : t ∈ Ico (a + n * h) (a + (n + 1) * h)) :
    piecewiseConst c h a t = c n := by
  simp [piecewiseConst, Nat.floor_div_eq_of_mem_Ico hh ht]

variable [TopologicalSpace α] [OrderTopology α]

/-- The regular grid of closed intervals `[a + n * h, a + (n + 1) * h]` is locally finite. -/
theorem locallyFinite_Icc_grid {h : α} (hh : 0 < h) (a : α) :
    LocallyFinite fun n : ℕ => Icc (a + n * h) (a + (↑n + 1) * h) := by
  intro x
  refine ⟨Ioo (x - h) (x + h), Ioo_mem_nhds (by linarith) (by linarith),
    (finite_Icc (⌊(x - h - a) / h⌋₊) (⌈(x + h - a) / h⌉₊)).subset ?_⟩
  rintro n ⟨z, ⟨hz1, hz2⟩, hz3, hz4⟩
  refine ⟨Nat.lt_add_one_iff.mp ((Nat.floor_lt' (by linarith)).mpr ?_),
    Nat.cast_le.mp ((?_ : (n : α) ≤ _).trans (Nat.le_ceil _))⟩ <;>
    (first | rw [div_lt_iff₀ hh] | rw [le_div_iff₀ hh]) <;> push_cast <;> nlinarith

/-- A function continuous on each cell `[a + n * h, a + (n + 1) * h]` is continuous
on `[a, ∞)`. -/
theorem ContinuousOn.of_Icc_grid {F : Type*} [TopologicalSpace F]
    {f : α → F} {h : α} (hh : 0 < h) {a : α}
    (hf : ∀ n : ℕ, ContinuousOn f (Icc (a + n * h) (a + (n + 1) * h))) :
    ContinuousOn f (Ici a) :=
  ((locallyFinite_Icc_grid hh a).continuousOn_iUnion (fun _ => isClosed_Icc) (hf ·)).mono
    fun t (hat : a ≤ t) =>
      mem_iUnion.mpr ⟨_, Ico_subset_Icc_self (mem_Ico_Nat_floor_div hh hat)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {y : ℕ → E} {c : ℕ → E} {h : ℝ} {a : ℝ}

/-- The piecewise linear interpolation at a grid point `a + n * h` equals `y n`. -/
theorem piecewiseLinear_apply_grid (hh : 0 < h) (a : ℝ) (n : ℕ) :
    piecewiseLinear y c h a (a + n * h) = y n := by
  simp [piecewiseLinear, hh.ne']

/-- The piecewise linear interpolation equals `y n + (t - (a + n * h)) • c n`
on `[a + n * h, a + (n + 1) * h)`. -/
theorem piecewiseLinear_eq_on_Ico (hh : 0 < h) {n : ℕ} {t : ℝ}
    (ht : t ∈ Ico (a + n * h) (a + (n + 1) * h)) :
    piecewiseLinear y c h a t = y n + (t - (a + n * h)) • c n := by
  simp [piecewiseLinear, Nat.floor_div_eq_of_mem_Ico hh ht]

/-- A piecewise linear function whose grid values satisfy `y (n + 1) = y n + h • c n`
is continuous on `[a, ∞)`. -/
theorem piecewiseLinear_continuousOn (hh : 0 < h)
    (hstep : ∀ n, y (n + 1) = y n + h • c n) :
    ContinuousOn (piecewiseLinear y c h a) (Ici a) := by
  apply ContinuousOn.of_Icc_grid hh; intro n
  apply (show ContinuousOn (fun t => y n + (t - (a + n * h)) • c n) _ by fun_prop).congr
  intro t ht; rcases eq_or_lt_of_le ht.2 with rfl | h_lt
  · norm_cast
    rw [piecewiseLinear_apply_grid hh a (n + 1), hstep]
    module
  · exact piecewiseLinear_eq_on_Ico hh ⟨ht.1, h_lt⟩

/-- The right derivative of a piecewise linear function is the piecewise constant slope. -/
theorem piecewiseLinear_hasDerivWithinAt (hh : 0 < h) {t : ℝ} (hat : a ≤ t) :
    HasDerivWithinAt (piecewiseLinear y c h a)
      (piecewiseConst c h a t) (Ici t) t := by
  set n := ⌊(t - a) / h⌋₊; set tn := a + n * h
  obtain ⟨h1, h2⟩ := mem_Ico_Nat_floor_div hh hat
  simp only [piecewiseConst]
  exact hasDerivWithinAt_Ioi_iff_Ici.mp
    (((hasDerivAt_id t |>.sub_const tn |>.smul_const (c n)
      |>.const_add (y n)).hasDerivWithinAt.congr_of_eventuallyEq (by
        filter_upwards [Ioo_mem_nhdsGT h2] with x hx
        exact piecewiseLinear_eq_on_Ico hh ⟨h1.trans hx.1.le, hx.2⟩)
      (by simp [piecewiseLinear, n, tn])).congr_deriv (one_smul _ _))

/-! ## Euler method -/

namespace ODE.EulerMethod

/-- A single step of the explicit Euler method: `y + h • v(t, y)`. -/
def step {𝕜 : Type*} {E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (v : 𝕜 → E → E) (h : 𝕜) (t : 𝕜) (y : E) : E :=
  y + h • v t y

/-- The sequence of Euler points, defined recursively:
`point v h t₀ y₀ 0 = y₀` and `point v h t₀ y₀ (n+1) = step v h (t₀ + n*h) (point v h t₀ y₀ n)`.
-/
def point {𝕜 : Type*} {E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (v : 𝕜 → E → E) (h : 𝕜) (t₀ : 𝕜) (y₀ : E) : ℕ → E
  | 0 => y₀
  | n + 1 => step v h (t₀ + n * h) (point v h t₀ y₀ n)

/-- The slope of the Euler method on the `n`-th cell: `v(t₀ + n * h, yₙ)`. -/
noncomputable def slope (v : ℝ → E → E) (h : ℝ) (t₀ : ℝ) (y₀ : E) (n : ℕ) : E :=
  v (t₀ + n * h) (point v h t₀ y₀ n)

/-- The piecewise linear Euler path, interpolating the Euler points with Euler slopes. -/
noncomputable def path (v : ℝ → E → E) (h : ℝ) (t₀ : ℝ) (y₀ : E) : ℝ → E :=
  piecewiseLinear (point v h t₀ y₀) (slope v h t₀ y₀) h t₀

/-- The piecewise constant right derivative of the Euler path. -/
noncomputable def deriv (v : ℝ → E → E) (h : ℝ) (t₀ : ℝ) (y₀ : E) : ℝ → E :=
  piecewiseConst (slope v h t₀ y₀) h t₀

variable {v : ℝ → E → E} {K L : NNReal} {M : ℝ}
  (hv : ∀ t, LipschitzWith K (v t))
  (hvt : ∀ y, LipschitzWith L (fun t => v t y))
  (hM : ∀ t y, ‖v t y‖ ≤ M)
include hv hvt hM

/-- Global bound on the difference between the Euler derivative and the vector field
along the Euler path. -/
theorem dist_deriv_le (hh : 0 < h) {t : ℝ} (ht₀ : t₀ ≤ t) :
    dist (deriv v h t₀ y₀ t) (v t (path v h t₀ y₀ t)) ≤ h * (L + K * M) := by
  obtain ⟨ht1, ht2⟩ := mem_Ico_Nat_floor_div hh ht₀; set n := ⌊(t - t₀) / h⌋₊
  have h1 : dist (v (t₀ + n * h) (point v h t₀ y₀ n)) (v t (point v h t₀ y₀ n)) ≤
      L * (t - (t₀ + n * h)) :=
    ((hvt _).dist_le_mul _ _).trans
      (by rw [dist_eq_norm, Real.norm_of_nonpos (by grind)]; grind)
  have h2 : dist (point v h t₀ y₀ n) (path v h t₀ y₀ t) ≤ h * M := by
    rw [show path v h t₀ y₀ t = _ from piecewiseLinear_eq_on_Ico hh ⟨ht1, ht2⟩, dist_eq_norm]
    simp +decide only [sub_add_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg (sub_nonneg.2 ht1)]
    exact mul_le_mul (by grind) (hM _ _) (norm_nonneg _) (by grind)
  calc dist (deriv v h t₀ y₀ t) (v t (path v h t₀ y₀ t))
      = dist (v (t₀ + n * h) (point v h t₀ y₀ n)) (v t (path v h t₀ y₀ t)) := by
          simp only [deriv, piecewiseConst_eq_on_Ico hh ⟨ht1, ht2⟩, slope]
    _ ≤ L * (t - (t₀ + n * h)) + K * (h * M) :=
          (dist_triangle _ _ _).trans
            (add_le_add h1 (((hv t).dist_le_mul _ _).trans (by gcongr)))
    _ ≤ h * (L + K * M) := by
          nlinarith [NNReal.coe_nonneg K, NNReal.coe_nonneg L, hM t₀ y₀]

/-- Error bound for the Euler method via Gronwall's inequality. -/
theorem dist_path_le (hh : 0 < h) {T : ℝ}
    {sol : ℝ → E} (hsol : ContinuousOn sol (Icc t₀ T))
    (hsol' : ∀ t ∈ Ico t₀ T, HasDerivWithinAt sol (v t (sol t)) (Ici t) t)
    (hsol₀ : sol t₀ = y₀) :
    ∀ t ∈ Icc t₀ T,
      dist (path v h t₀ y₀ t) (sol t) ≤ gronwallBound 0 K (h * (L + K * M)) (t - t₀) := by
  intro t ht
  have := dist_le_of_approx_trajectories_ODE (δ := 0) (εg := 0)
    (f' := deriv v h t₀ y₀) (g' := fun t => v t (sol t)) hv
    ((piecewiseLinear_continuousOn hh fun n => by simp [point, step, slope]).mono
      Icc_subset_Ici_self)
    (fun t ht => piecewiseLinear_hasDerivWithinAt hh ht.1)
    (fun t ht => dist_deriv_le hv hvt hM hh ht.1)
    hsol hsol' (fun _ _ => (dist_self _).le)
    (by simp [piecewiseLinear, point, hsol₀]) t ht
  simpa using this

/-- The Euler method converges to the true solution as `h → 0⁺`. -/
theorem tendsto_path {T : ℝ}
    {sol : ℝ → E} (hsol : ContinuousOn sol (Icc t₀ T))
    (hsol' : ∀ t ∈ Ico t₀ T, HasDerivWithinAt sol (v t (sol t)) (Ici t) t)
    (hsol₀ : sol t₀ = y₀) :
    ∀ t ∈ Icc t₀ T, Tendsto (fun δ => path v δ t₀ y₀ t)
      (nhdsWithin 0 (Ioi 0)) (nhds (sol t)) := fun t ht =>
  tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero_norm'
    (by have := fun x (hx : (0 : ℝ) < x) =>
          dist_path_le hv hvt hM hx hsol hsol' hsol₀ t ht
        simpa using eventually_of_mem self_mem_nhdsWithin this)
    (tendsto_nhdsWithin_of_tendsto_nhds <|
      Continuous.tendsto' ((gronwallBound_continuous_ε 0 K (t - t₀)).comp
        (continuous_id.mul continuous_const)) 0 0 (by grind [gronwallBound_ε0_δ0])))

end ODE.EulerMethod
