/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Star
import Mathlib.Tactic

/-!
# The scaffold interface

This file implements blueprint nodes S01, S02 and S03 of
`docs/nikodym_construction_lean_blueprint.md`.

* S01: the `Prop`-valued structure `Nikodym.Scaffold b σ φ K₀ K₁` abstracting the arithmetic
  input of the construction (a commutative ring `R` with a `ℤ`-basis `b`, finitely many ring
  homomorphisms `σ i : R →+* ℝ`, a reduction map `φ : R →+* F` to a finite field, and two real
  constants), together with the sup-box `Scaffold.box σ T`, the trace `Scaffold.trace σ x` and
  the Euclidean embedding `Scaffold.emb σ : R →+ EuclideanSpace ℝ ι`.
* S02: `‖emb σ x‖ ^ 2 = trace σ (x ^ 2)`, homogeneity of the norm, the bound
  `‖emb σ x‖ ≤ √n * T` on `box σ T`, injectivity of `emb σ`, and the unit gap
  `x ≠ 0 → 1 ≤ ‖emb σ x‖`.
* S03: closure properties of boxes, finiteness of boxes (`Scaffold.box_finite`,
  `Scaffold.boxFinset`) and the lattice count
  `(T / (n * K₀)) ^ n ≤ #(boxFinset h T)`.

Throughout, `n` denotes `Fintype.card ι`.
-/

namespace Nikodym

/-- Blueprint S01: the scaffold interface. `R` is a commutative ring with a `ℤ`-basis `b` indexed
by `κ`, `σ i : R →+* ℝ` (`i : ι`) are "real embeddings", `φ : R →+* F` is a reduction map to a
finite field, `K₀` bounds the embeddings of basis vectors and `K₁` controls the coordinates in
terms of the embeddings. The five axioms are all that the combinatorial construction uses. -/
structure Scaffold {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
    (b : Module.Basis κ ℤ R) (σ : ι → R →+* ℝ) (φ : R →+* F) (K₀ K₁ : ℝ) : Prop where
  /-- The number of embeddings equals the rank. -/
  card_eq : Fintype.card ι = Fintype.card κ
  /-- Every embedding of every basis vector is bounded by `K₀`. -/
  basis_bound : ∀ i k, |σ i (b k)| ≤ K₀
  /-- Coordinates are controlled by the embeddings. -/
  coord_bound : ∀ (x : R) (T : ℝ), (∀ i, |σ i x| ≤ T) → ∀ k, |(b.repr x k : ℝ)| ≤ K₁ * T
  /-- The trace `∑ i, σ i x` is an integer. -/
  trace_int : ∀ x, ∃ z : ℤ, ∑ i, σ i x = z
  /-- Small elements of the kernel of `φ` vanish. -/
  small_ker : ∀ x, φ x = 0 → ∏ i, |σ i x| < Fintype.card F → x = 0

namespace Scaffold

/-! ### Blueprint S01: boxes and the Euclidean embedding

These definitions and the closure properties of boxes do not need finiteness of `ι`. -/

section Box

variable {R ι : Type*} [CommRing R]

/-- Blueprint S01: the sup-box of radius `T`, `{x | ∀ i, |σ i x| ≤ T}`. -/
def box (σ : ι → R →+* ℝ) (T : ℝ) : Set R := {x | ∀ i, |σ i x| ≤ T}

/-- Blueprint S01: the Euclidean embedding `x ↦ (σ i x)_i`, as an additive group homomorphism
into `EuclideanSpace ℝ ι`. -/
def emb (σ : ι → R →+* ℝ) : R →+ EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 fun i ↦ σ i x
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

variable (σ : ι → R →+* ℝ)

/-- Blueprint S01: membership in a box. -/
@[simp] theorem mem_box {x : R} {T : ℝ} : x ∈ box σ T ↔ ∀ i, |σ i x| ≤ T := Iff.rfl

/-- Blueprint S01: coordinates of the Euclidean embedding. -/
@[simp] theorem emb_apply (x : R) (i : ι) : emb σ x i = σ i x := rfl

/-- Blueprint S02: `emb` is additive. -/
theorem emb_add (x y : R) : emb σ (x + y) = emb σ x + emb σ y := map_add _ x y

/-- Blueprint S02: `emb` respects subtraction. -/
theorem emb_sub (x y : R) : emb σ (x - y) = emb σ x - emb σ y := map_sub _ x y

/-- Blueprint S02: `emb` respects negation. -/
theorem emb_neg (x : R) : emb σ (-x) = -emb σ x := map_neg _ x

/-- Blueprint S02: `emb 0 = 0`. -/
theorem emb_zero : emb σ (0 : R) = 0 := map_zero _

/-- Blueprint S02: `emb` is `ℤ`-linear. -/
theorem emb_zsmul (z : ℤ) (x : R) : emb σ (z • x) = z • emb σ x := map_zsmul _ z x

/-- Blueprint S02: `emb` respects `ℕ`-scalars. -/
theorem emb_nsmul (n : ℕ) (x : R) : emb σ (n • x) = n • emb σ x := map_nsmul _ n x

variable {σ}

/-- Blueprint S03: boxes are monotone in the radius. -/
theorem box_mono {S T : ℝ} (hST : S ≤ T) : box σ S ⊆ box σ T :=
  fun _ hx i ↦ (hx i).trans hST

/-- Blueprint S03: `0` lies in every box of nonnegative radius. -/
theorem zero_mem_box {T : ℝ} (hT : 0 ≤ T) : (0 : R) ∈ box σ T :=
  fun i ↦ by simp [hT]

/-- Blueprint S03: boxes are closed under negation. -/
theorem box_neg {x : R} {T : ℝ} (hx : x ∈ box σ T) : -x ∈ box σ T :=
  fun i ↦ by rw [map_neg, abs_neg]; exact hx i

/-- Blueprint S03: boxes are closed under negation (iff form). -/
 theorem neg_mem_box_iff {x : R} {T : ℝ} : -x ∈ box σ T ↔ x ∈ box σ T :=
  ⟨fun hx ↦ by simpa using box_neg hx, box_neg⟩

/-- Blueprint S03: `box S + box T ⊆ box (S + T)`. -/
theorem box_add {x y : R} {S T : ℝ} (hx : x ∈ box σ S) (hy : y ∈ box σ T) :
    x + y ∈ box σ (S + T) :=
  fun i ↦ by rw [map_add]; exact (abs_add_le _ _).trans (add_le_add (hx i) (hy i))

/-- Blueprint S03: `box S - box T ⊆ box (S + T)`. -/
theorem box_sub {x y : R} {S T : ℝ} (hx : x ∈ box σ S) (hy : y ∈ box σ T) :
    x - y ∈ box σ (S + T) :=
  sub_eq_add_neg x y ▸ box_add hx (box_neg hy)

/-- Blueprint S03: `box S * box T ⊆ box (S * T)`, coordinatewise form. -/
theorem box_mul_le {x y : R} {S T : ℝ} (hx : ∀ i, |σ i x| ≤ S) (hy : ∀ i, |σ i y| ≤ T) :
    ∀ i, |σ i (x * y)| ≤ S * T :=
  fun i ↦ by
    rw [map_mul, abs_mul]
    exact mul_le_mul (hx i) (hy i) (abs_nonneg _) ((abs_nonneg _).trans (hx i))

/-- Blueprint S03: `box S * box T ⊆ box (S * T)`. -/
theorem mul_mem_box {x y : R} {S T : ℝ} (hx : x ∈ box σ S) (hy : y ∈ box σ T) :
    x * y ∈ box σ (S * T) :=
  box_mul_le hx hy

/-- Blueprint S03: scaling by an integer scales the box radius by `|z|` (coordinatewise form). -/
theorem box_intCast_smul {x : R} {T : ℝ} (hx : ∀ i, |σ i x| ≤ T) (z : ℤ) :
    ∀ i, |σ i (z • x)| ≤ |z| * T :=
  fun i ↦ by
    rw [map_zsmul, zsmul_eq_mul, abs_mul, Int.cast_abs]
    exact mul_le_mul_of_nonneg_left (hx i) (abs_nonneg _)

/-- Blueprint S03: `z • box T ⊆ box (|z| * T)`. -/
theorem zsmul_mem_box {x : R} {T : ℝ} (hx : x ∈ box σ T) (z : ℤ) : z • x ∈ box σ (|z| * T) :=
  box_intCast_smul hx z

/-- Blueprint S03: `(z : R) * box T ⊆ box (|z| * T)`. -/
theorem intCast_mul_mem_box {x : R} {T : ℝ} (hx : x ∈ box σ T) (z : ℤ) :
    (z : R) * x ∈ box σ (|z| * T) := by
  have := zsmul_mem_box hx z
  rwa [zsmul_eq_mul] at this

/-- Blueprint S03: `n • box T ⊆ box (n * T)`. -/
theorem nsmul_mem_box {x : R} {T : ℝ} (hx : x ∈ box σ T) (n : ℕ) : n • x ∈ box σ (n * T) := by
  simpa using zsmul_mem_box hx n

/-- Blueprint S03: `(n : R) * box T ⊆ box (n * T)`. -/
theorem natCast_mul_mem_box {x : R} {T : ℝ} (hx : x ∈ box σ T) (n : ℕ) :
    (n : R) * x ∈ box σ (n * T) := by
  have := nsmul_mem_box hx n
  rwa [nsmul_eq_mul] at this

end Box

/-! ### Blueprint S01/S02: the trace and the Euclidean norm -/

section Trace

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- Blueprint S01: the trace `∑ i, σ i x`. -/
def trace (σ : ι → R →+* ℝ) (x : R) : ℝ := ∑ i, σ i x

variable (σ : ι → R →+* ℝ)

/-- Blueprint S02: the trace is additive. -/
theorem trace_add (x y : R) : trace σ (x + y) = trace σ x + trace σ y := by
  simp [trace, Finset.sum_add_distrib]

/-- Blueprint S02: the trace respects subtraction. -/
theorem trace_sub (x y : R) : trace σ (x - y) = trace σ x - trace σ y := by
  simp [trace, Finset.sum_sub_distrib]

/-- Blueprint S02: the trace respects negation. -/
theorem trace_neg (x : R) : trace σ (-x) = -trace σ x := by
  simp [trace, Finset.sum_neg_distrib]

/-- Blueprint S02: `trace 0 = 0`. -/
theorem trace_zero : trace σ (0 : R) = 0 := by simp [trace]

/-- Blueprint S02: the trace is `ℤ`-linear. -/
theorem trace_zsmul (z : ℤ) (x : R) : trace σ (z • x) = z * trace σ x := by
  simp [trace, Finset.mul_sum]

/-- Blueprint S02: the trace respects `ℕ`-scalars. -/
theorem trace_nsmul (n : ℕ) (x : R) : trace σ (n • x) = n * trace σ x := by
  simp [trace, Finset.mul_sum]

/-- Blueprint S02: `trace ((z : R) * x) = z * trace x`. -/
theorem trace_intCast_mul (z : ℤ) (x : R) : trace σ ((z : R) * x) = z * trace σ x := by
  simp [trace, Finset.mul_sum]

/-- Blueprint S02: `trace ((n : R) * x) = n * trace x`. -/
theorem trace_natCast_mul (n : ℕ) (x : R) : trace σ ((n : R) * x) = n * trace σ x := by
  simp [trace, Finset.mul_sum]

/-- Blueprint S02: the trace of an integer constant. -/
theorem trace_intCast (z : ℤ) : trace σ (z : R) = Fintype.card ι * z := by
  simp [trace]

/-- Blueprint S02: the trace of a product is symmetric. -/
theorem trace_mul_comm (x y : R) : trace σ (x * y) = trace σ (y * x) := by
  rw [mul_comm]

/-- Blueprint S02: `trace (x ^ 2) ≥ 0`. -/
theorem trace_sq_nonneg (x : R) : 0 ≤ trace σ (x ^ 2) :=
  Finset.sum_nonneg fun i _ ↦ by rw [map_pow]; positivity

/-- Blueprint S03: on the box of radius `T` the trace is bounded by `n * T`. -/
theorem abs_trace_le {x : R} {T : ℝ} (hx : ∀ i, |σ i x| ≤ T) :
    |trace σ x| ≤ Fintype.card ι * T := by
  calc |trace σ x| ≤ ∑ i, |σ i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, T := Finset.sum_le_sum fun i _ ↦ hx i
    _ = Fintype.card ι * T := by simp

variable {σ}

/-- Blueprint S02: `‖emb σ x‖ ^ 2 = trace σ (x ^ 2)`. -/
theorem norm_emb_sq (x : R) : ‖emb σ x‖ ^ 2 = trace σ (x ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [trace, map_pow]

/-- Blueprint S02: `‖emb σ (z • x)‖ = |z| * ‖emb σ x‖` for `z : ℤ`. -/
theorem norm_emb_zsmul (z : ℤ) (x : R) : ‖emb σ (z • x)‖ = |z| * ‖emb σ x‖ := by
  rw [map_zsmul, norm_zsmul ℝ, Real.norm_eq_abs, Int.cast_abs]

/-- Blueprint S02: `‖emb σ (n • x)‖ = n * ‖emb σ x‖` for `n : ℕ`. -/
theorem norm_emb_nsmul (n : ℕ) (x : R) : ‖emb σ (n • x)‖ = n * ‖emb σ x‖ := by
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]

/-- Blueprint S02: `‖emb σ ((z : R) * x)‖ = |z| * ‖emb σ x‖` for `z : ℤ`. -/
theorem norm_emb_intCast_mul (z : ℤ) (x : R) : ‖emb σ ((z : R) * x)‖ = |z| * ‖emb σ x‖ := by
  rw [← zsmul_eq_mul, norm_emb_zsmul]

/-- Blueprint S02: `‖emb σ ((n : R) * x)‖ = n * ‖emb σ x‖` for `n : ℕ`. -/
theorem norm_emb_natCast_mul (n : ℕ) (x : R) : ‖emb σ ((n : R) * x)‖ = n * ‖emb σ x‖ := by
  rw [← nsmul_eq_mul, norm_emb_nsmul]

/-- Blueprint S02: on the box of radius `T`, `‖emb σ x‖ ≤ √n * T`. -/
theorem norm_emb_le {x : R} {T : ℝ} (hx : ∀ i, |σ i x| ≤ T) :
    ‖emb σ x‖ ≤ Real.sqrt (Fintype.card ι) * T := by
  have hsq : ‖emb σ x‖ ^ 2 ≤ Fintype.card ι * T ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i, (emb σ x i) ^ 2 ≤ ∑ _i : ι, T ^ 2 := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [emb_apply, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
      _ = Fintype.card ι * T ^ 2 := by simp
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : emb σ x = 0 := by ext i; exact hι.elim i
    simp [this]
  · have hT : 0 ≤ T := (abs_nonneg _).trans (hx (Classical.arbitrary ι))
    have : ‖emb σ x‖ ≤ Real.sqrt (Fintype.card ι * T ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hT] at this

end Trace

/-! ### Blueprint S02/S03: consequences of the scaffold axioms -/

section WithScaffold

variable {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
variable {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ : ℝ}

/-- Blueprint S02: `emb σ` is injective (joint injectivity of the embeddings). -/
theorem emb_injective (h : Scaffold b σ φ K₀ K₁) : Function.Injective (emb σ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hσ : ∀ i, |σ i x| ≤ 0 := fun i ↦ by
    have := congrArg (fun v : EuclideanSpace ℝ ι ↦ v i) hx
    simp only [emb_apply, PiLp.zero_apply] at this
    simp [this]
  rw [b.ext_elem_iff]
  intro k
  have hk := h.coord_bound x 0 hσ k
  rw [mul_zero] at hk
  have : (b.repr x k : ℝ) = 0 := abs_nonpos_iff.mp hk
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact_mod_cast this

/-- Blueprint S02: `emb σ x ≠ 0` for `x ≠ 0`. -/
theorem emb_ne_zero (h : Scaffold b σ φ K₀ K₁) {x : R} (hx : x ≠ 0) : emb σ x ≠ 0 :=
  fun h0 ↦ hx (h.emb_injective (h0.trans (map_zero _).symm))

/-- Blueprint S02: the unit gap `x ≠ 0 → 1 ≤ ‖emb σ x‖`. -/
theorem one_le_norm_emb (h : Scaffold b σ φ K₀ K₁) {x : R} (hx : x ≠ 0) : 1 ≤ ‖emb σ x‖ := by
  obtain ⟨z, hz⟩ := h.trace_int (x ^ 2)
  have hz' : ‖emb σ x‖ ^ 2 = z := by rw [norm_emb_sq]; exact hz
  have hpos : 0 < ‖emb σ x‖ ^ 2 := by
    have := norm_pos_iff.mpr (h.emb_ne_zero hx)
    positivity
  have hz1 : (1 : ℝ) ≤ z := by
    rw [hz'] at hpos
    exact_mod_cast (Int.cast_pos.mp hpos : 0 < z)
  rw [← one_le_sq_iff₀ (norm_nonneg _), hz']
  exact hz1

/-- Blueprint S03: boxes are finite (from `coord_bound`). -/
theorem box_finite (h : Scaffold b σ φ K₀ K₁) (T : ℝ) : (box σ T).Finite := by
  classical
  set N : ℤ := ⌈K₁ * T⌉ with hN
  have hfin : ((Fintype.piFinset fun _ : κ ↦ Finset.Icc (-N) N : Finset (κ → ℤ)) :
      Set (κ → ℤ)).Finite := Finset.finite_toSet _
  refine (hfin.image fun c ↦ ∑ k, c k • b k).subset ?_
  intro x hx
  refine ⟨fun k ↦ b.repr x k, ?_, b.sum_repr x⟩
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro k
  have hk := h.coord_bound x T hx k
  rw [abs_le] at hk
  have hceil := Int.le_ceil (K₁ * T)
  rw [Finset.mem_Icc]
  constructor
  · have : ((-N : ℤ) : ℝ) ≤ (b.repr x k : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : ((b.repr x k : ℤ) : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast this

/-- Blueprint S03: the box of radius `T` as a `Finset`. -/
noncomputable def boxFinset (h : Scaffold b σ φ K₀ K₁) (T : ℝ) : Finset R :=
  (h.box_finite T).toFinset

/-- Blueprint S03: membership in `boxFinset`. -/
@[simp] theorem mem_boxFinset (h : Scaffold b σ φ K₀ K₁) {T : ℝ} {x : R} :
    x ∈ h.boxFinset T ↔ ∀ i, |σ i x| ≤ T :=
  Set.Finite.mem_toFinset _

/-- Blueprint S03: `boxFinset` coerces to `box`. -/
@[simp] theorem coe_boxFinset (h : Scaffold b σ φ K₀ K₁) (T : ℝ) :
    (h.boxFinset T : Set R) = box σ T :=
  Set.Finite.coe_toFinset _

/-- Blueprint S03: the lattice count `(T / (n * K₀)) ^ n ≤ #(box T)` for `K₀ > 0`, `T ≥ 0`. -/
theorem le_card_boxFinset (h : Scaffold b σ φ K₀ K₁) (hK₀ : 0 < K₀) {T : ℝ} (hT : 0 ≤ T) :
    (T / (Fintype.card ι * K₀)) ^ Fintype.card ι ≤ ((h.boxFinset T).card : ℝ) := by
  classical
  set n := Fintype.card ι with hn
  set m : ℕ := ⌊T / (n * K₀)⌋₊ with hm
  set C : Finset (κ → ℤ) := Fintype.piFinset fun _ : κ ↦ Finset.Icc (-(m : ℤ)) m with hC
  -- the coefficient vectors map into the box
  have hmaps : Set.MapsTo (fun c : κ → ℤ ↦ ∑ k, c k • b k) C (h.boxFinset T) := by
    intro c hc
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hc
    rw [Finset.mem_coe, h.mem_boxFinset]
    intro i
    have hc' : ∀ k, |(c k : ℝ)| ≤ m := fun k ↦ by
      have := hc k
      rw [Finset.mem_Icc] at this
      rw [abs_le]
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2
    calc |σ i (∑ k, c k • b k)| = |∑ k, (c k : ℝ) * σ i (b k)| := by
          simp [map_sum, zsmul_eq_mul]
      _ ≤ ∑ k, |(c k : ℝ)| * |σ i (b k)| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          simp [abs_mul]
      _ ≤ ∑ _k : κ, (m : ℝ) * K₀ :=
          Finset.sum_le_sum fun k _ ↦
            mul_le_mul (hc' k) (h.basis_bound i k) (abs_nonneg _) (Nat.cast_nonneg _)
      _ = n * K₀ * m := by simp [h.card_eq, hn]; ring
      _ ≤ T := by
          rcases Nat.eq_zero_or_pos n with h0 | hpos
          · simp [h0, hT]
          · have hnK : 0 < (n : ℝ) * K₀ := by positivity
            have := Nat.floor_le (div_nonneg hT hnK.le)
            rw [← hm, le_div_iff₀ hnK] at this
            linarith
  -- the coefficient map is injective
  have hinj : Set.InjOn (fun c : κ → ℤ ↦ ∑ k, c k • b k) C := by
    intro c _ c' _ hcc
    have := congrArg (fun y ↦ (b.repr y : κ → ℤ)) hcc
    simpa only [Module.Basis.repr_sum_self] using this
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  -- count the coefficient vectors
  have hC_card : C.card = (2 * m + 1) ^ n := by
    rw [hC, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, ← h.card_eq, Int.card_Icc]
    congr 1
    omega
  -- compare with the real bound
  have hle : T / (n * K₀) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (T / (n * K₀))
    rw [← hm] at this
    push_cast
    linarith
  calc (T / (n * K₀)) ^ n ≤ ((2 * m + 1 : ℕ) : ℝ) ^ n :=
        pow_le_pow_left₀ (div_nonneg hT (by positivity)) hle n
    _ = (C.card : ℝ) := by rw [hC_card]; push_cast; ring
    _ ≤ ((h.boxFinset T).card : ℝ) := by exact_mod_cast hcard

end WithScaffold

end Scaffold

end Nikodym

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
