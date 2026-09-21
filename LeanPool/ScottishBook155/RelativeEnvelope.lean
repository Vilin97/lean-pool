/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import Mathlib.Analysis.Normed.Module.HahnBanach
import LeanPool.ScottishBook155.AdjunctionFormula
import LeanPool.ScottishBook155.KuratowskiCoordinate

/-!
# The dual-evaluation model of the relative Banach envelope

The paper describes the relative Lipschitz-free envelope as a quotient of an
`ℓ₁`-sum.  For the metric estimates it is equivalent, and technically more
direct, to use its dual unit ball as the coordinates of an `ℓ∞` space.

An admissible functional consists of a norm-at-most-one linear functional on
the old normed space together with a one-Lipschitz extension to the attached
metric space.  Evaluation at all such functionals gives the relative
coordinate.  This file establishes the boundedness and nonexpansiveness of
that coordinate.  McShane extension and Hahn--Banach then supply enough
admissible functionals to prove that the induced linear copy of the old space
is isometric.
-/

namespace ScottishBook155

open ENNReal lp WithLp

universe u v

/-- A dual-unit-ball functional on `N` together with a one-Lipschitz extension
along the distinguished map `j : N → P`. -/
structure RelativeFunctional (P : Type u) (N : Type v) [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) where
  /-- The continuous linear functional on the distinguished target space. -/
  linear : N →L[ℝ] ℝ
  norm_le_one : ‖linear‖ ≤ 1
  /-- The one-Lipschitz extension of the functional to the ambient metric space. -/
  value : P → ℝ
  lipschitz : LipschitzWith 1 value
  agree : ∀ n, value (j n) = linear n

/-- Evaluation on all admissible relative functionals, normalized at `j 0`. -/
noncomputable def relativeEvaluation {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) (p : P) :
    ℓ^∞(RelativeFunctional P N j, ℝ) :=
  ⟨fun φ => φ.value p - φ.value (j 0), by
    apply memℓp_infty
    use dist p (j 0)
    rintro - ⟨φ, rfl⟩
    simpa [Real.dist_eq] using φ.lipschitz.dist_le_mul p (j 0)⟩

theorem relativeEvaluation_apply {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) (p : P)
    (φ : RelativeFunctional P N j) :
    relativeEvaluation j p φ = φ.value p - φ.value (j 0) := rfl

theorem relativeEvaluation_base {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) :
    relativeEvaluation j (j 0) = 0 := by
  ext φ
  simp [relativeEvaluation_apply]

/-- The relative evaluation coordinate is nonexpansive. -/
theorem relativeEvaluation_dist_le {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) (p q : P) :
    dist (relativeEvaluation j p) (relativeEvaluation j q) ≤ dist p q := by
  rw [dist_eq_norm]
  refine lp.norm_le_of_forall_le dist_nonneg fun φ => ?_
  simp only [lp.coeFn_sub, Pi.sub_apply, relativeEvaluation_apply]
  calc
    ‖(φ.value p - φ.value (j 0)) - (φ.value q - φ.value (j 0))‖ =
        |φ.value p - φ.value q| := by
      rw [Real.norm_eq_abs]
      congr 1
      ring
    _ ≤ dist p q := by
      simpa [Real.dist_eq] using φ.lipschitz.dist_le_mul p q

/-- On a distinguished old-space point, evaluation is exactly the underlying
linear functional. -/
theorem relativeEvaluation_target_apply {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) (n : N)
    (φ : RelativeFunctional P N j) :
    relativeEvaluation j (j n) φ = φ.linear n := by
  simp [relativeEvaluation_apply, φ.agree]

/-- The distinguished old space maps linearly into the relative coordinate. -/
noncomputable def relativeTargetLinear {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) :
    N →ₗ[ℝ] ℓ^∞(RelativeFunctional P N j, ℝ) where
  toFun n := relativeEvaluation j (j n)
  map_add' n m := by
    ext φ
    simp [relativeEvaluation_target_apply]
  map_smul' c n := by
    ext φ
    simp [relativeEvaluation_target_apply]

theorem relativeTargetLinear_apply {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) (n : N) :
    relativeTargetLinear j n = relativeEvaluation j (j n) := rfl

/-- Every admissible functional has norm at most one, so the linear copy of
the old space is contractive. -/
theorem norm_relativeTargetLinear_le {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) (n : N) :
    ‖relativeTargetLinear j n‖ ≤ ‖n‖ := by
  refine lp.norm_le_of_forall_le (norm_nonneg n) fun φ => ?_
  rw [relativeTargetLinear_apply, relativeEvaluation_target_apply]
  calc
    ‖φ.linear n‖ ≤ ‖φ.linear‖ * ‖n‖ := φ.linear.le_opNorm n
    _ ≤ 1 * ‖n‖ := mul_le_mul_of_nonneg_right φ.norm_le_one (norm_nonneg n)
    _ = ‖n‖ := one_mul _

/-- A contractive linear functional on the old space admits an admissible
one-Lipschitz extension whenever the distinguished map is an isometry.  This
is the McShane extension step in the dual model. -/
theorem exists_relativeFunctional_of_isometry {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P)
    (hj : Isometry j) (L : N →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    ∃ φ : RelativeFunctional P N j, φ.linear = L := by
  let seed : P → ℝ :=
    Function.extend j (fun n : N => L n) (fun _ : P => (0 : ℝ))
  have hseed : LipschitzOnWith 1 seed (Set.range j) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rcases hx with ⟨a, rfl⟩
    rcases hy with ⟨b, rfl⟩
    simp only [seed, hj.injective.extend_apply]
    rw [hj.dist_eq]
    simpa [dist_eq_norm, ← map_sub] using
      (L.le_opNorm (a - b)).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg (a - b)))
  obtain ⟨g, hg, hagree⟩ := hseed.extend_real
  refine ⟨{
    linear := L
    norm_le_one := hL
    value := g
    lipschitz := hg
    agree := fun n => ?_ }, rfl⟩
  rw [← hagree (Set.mem_range_self n)]
  exact hj.injective.extend_apply (fun n : N => L n) (fun _ : P => (0 : ℝ)) n

/-- Hahn--Banach and McShane supply a coordinate attaining the norm of every
old-space vector. -/
theorem exists_relativeFunctional_norming {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P)
    (hj : Isometry j) (n : N) :
    ∃ φ : RelativeFunctional P N j, φ.linear n = ‖n‖ := by
  obtain ⟨L, hL, hLn⟩ := exists_dual_vector'' ℝ n
  obtain ⟨φ, rfl⟩ := exists_relativeFunctional_of_isometry j hj L hL
  exact ⟨φ, hLn⟩

/-- Under an isometric distinguished map, the old space has exactly its
original norm in the relative coordinate. -/
theorem norm_relativeTargetLinear_eq {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) (hj : Isometry j)
    (n : N) : ‖relativeTargetLinear j n‖ = ‖n‖ := by
  apply le_antisymm (norm_relativeTargetLinear_le j n)
  obtain ⟨φ, hφ⟩ := exists_relativeFunctional_norming j hj n
  have heval := lp.norm_apply_le_norm ENNReal.top_ne_zero (relativeTargetLinear j n) φ
  rw [relativeTargetLinear_apply, relativeEvaluation_target_apply, hφ] at heval
  change ‖n‖ ≤ ‖relativeEvaluation j (j n)‖
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg n)] using heval

/-- The old Banach space embeds linearly and isometrically into the dual
evaluation model of the relative envelope. -/
noncomputable def relativeTargetLinearIsometry {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P)
    (hj : Isometry j) : N →ₗᵢ[ℝ] ℓ^∞(RelativeFunctional P N j, ℝ) where
  toLinearMap := relativeTargetLinear j
  norm_map' := norm_relativeTargetLinear_eq j hj

theorem relativeEvaluation_target_dist_eq {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P)
    (hj : Isometry j) (n m : N) :
    dist (relativeEvaluation j (j n)) (relativeEvaluation j (j m)) = dist n m := by
  simpa [relativeTargetLinearIsometry, relativeTargetLinear_apply] using
    (relativeTargetLinearIsometry j hj).isometry.dist_eq n m

/-- Extend a prescribed one-Lipschitz seed which already agrees with a
contractive old-space functional on every distinguished target point.  This
is the reusable McShane interface for the two short-distance cases. -/
theorem exists_relativeFunctional_extending {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P)
    (L : N →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (s : Set P) (seed : P → ℝ)
    (htargets : Set.range j ⊆ s) (hseed : LipschitzOnWith 1 seed s)
    (hagree : ∀ n, seed (j n) = L n) :
    ∃ φ : RelativeFunctional P N j,
      φ.linear = L ∧ Set.EqOn seed φ.value s := by
  obtain ⟨g, hg, hext⟩ := hseed.extend_real
  refine ⟨{
    linear := L
    norm_le_one := hL
    value := g
    lipschitz := hg
    agree := fun n => ?_ }, rfl, hext⟩
  rw [← hext]
  · exact hagree n
  · exact htargets (Set.mem_range_self n)

/-- A single admissible functional attaining the ambient distance gives the
reverse norm inequality, hence exact distance preservation by evaluation. -/
theorem relativeEvaluation_dist_eq_of_attains {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P)
    (p q : P) (φ : RelativeFunctional P N j)
    (hφ : φ.value p - φ.value q = dist p q) :
    dist (relativeEvaluation j p) (relativeEvaluation j q) = dist p q := by
  apply le_antisymm (relativeEvaluation_dist_le j p q)
  rw [dist_eq_norm]
  have heval := lp.norm_apply_le_norm ENNReal.top_ne_zero
    (relativeEvaluation j p - relativeEvaluation j q) φ
  simp only [lp.coeFn_sub, Pi.sub_apply, relativeEvaluation_apply] at heval
  calc
    dist p q = |φ.value p - φ.value q| := by rw [hφ, abs_of_nonneg dist_nonneg]
    _ = ‖(φ.value p - φ.value (j 0)) - (φ.value q - φ.value (j 0))‖ := by
      rw [Real.norm_eq_abs]
      congr 1
      ring
    _ ≤ ‖relativeEvaluation j p - relativeEvaluation j q‖ := heval

/-- A one-Lipschitz seed on a subset, agreeing with a contractive old-space
functional and attaining the distance of two points in that subset, certifies
that the relative coordinate preserves that pair's distance. -/
theorem relativeEvaluation_dist_eq_of_lipschitzOn {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P)
    (L : N →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (s : Set P) (seed : P → ℝ)
    (htargets : Set.range j ⊆ s) (hseed : LipschitzOnWith 1 seed s)
    (hagree : ∀ n, seed (j n) = L n)
    {p q : P} (hp : p ∈ s) (hq : q ∈ s)
    (hpair : seed p - seed q = dist p q) :
    dist (relativeEvaluation j p) (relativeEvaluation j q) = dist p q := by
  obtain ⟨φ, -, hext⟩ :=
    exists_relativeFunctional_extending j L hL s seed htargets hseed hagree
  apply relativeEvaluation_dist_eq_of_attains j p q φ
  rw [← hext hp, ← hext hq]
  exact hpair

/-- The explicit McShane formula for data which vanish on `T` and take the
values `c₀,c₁` at `p,q`. -/
noncomputable def zeroTargetPairSeed {P : Type u} [MetricSpace P]
    (T : Set P) (p q : P) (c₀ c₁ : ℝ) (z : P) : ℝ :=
  min (c₀ + dist z p) (min (c₁ + dist z q) (Metric.infDist z T))

theorem zeroTargetPairSeed_lipschitz {P : Type u} [MetricSpace P]
    (T : Set P) (p q : P) (c₀ c₁ : ℝ) :
    LipschitzWith 1 (zeroTargetPairSeed T p q c₀ c₁) := by
  have hp : LipschitzWith 1 (fun z : P => c₀ + dist z p) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa [Real.dist_eq] using (LipschitzWith.dist_left p).dist_le_mul x y
  have hq : LipschitzWith 1 (fun z : P => c₁ + dist z q) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa [Real.dist_eq] using (LipschitzWith.dist_left q).dist_le_mul x y
  change LipschitzWith 1 (fun z : P =>
    min (c₀ + dist z p) (min (c₁ + dist z q) (Metric.infDist z T)))
  simpa using hp.min (hq.min (Metric.lipschitz_infDist_pt T))

theorem zeroTargetPairSeed_of_mem {P : Type u} [MetricSpace P]
    {T : Set P} {p q z : P} {c₀ c₁ : ℝ}
    (hc₀ : |c₀| ≤ Metric.infDist p T) (hc₁ : |c₁| ≤ Metric.infDist q T)
    (hz : z ∈ T) : zeroTargetPairSeed T p q c₀ c₁ z = 0 := by
  have h₀ : 0 ≤ c₀ + dist z p := by
    have hinf := Metric.infDist_le_dist_of_mem hz (x := p)
    have hneg : -c₀ ≤ |c₀| := neg_le_abs c₀
    rw [dist_comm p z] at hinf
    linarith
  have h₁ : 0 ≤ c₁ + dist z q := by
    have hinf := Metric.infDist_le_dist_of_mem hz (x := q)
    have hneg : -c₁ ≤ |c₁| := neg_le_abs c₁
    rw [dist_comm q z] at hinf
    linarith
  simp [zeroTargetPairSeed, Metric.infDist_zero_of_mem hz, min_eq_right h₀,
    min_eq_right h₁]

theorem zeroTargetPairSeed_at_left {P : Type u} [MetricSpace P]
    {T : Set P} {p q : P} {c₀ c₁ : ℝ}
    (hc₀ : |c₀| ≤ Metric.infDist p T)
    (hpq : |c₀ - c₁| ≤ dist p q) :
    zeroTargetPairSeed T p q c₀ c₁ p = c₀ := by
  rw [zeroTargetPairSeed, dist_self, add_zero, min_eq_left]
  exact le_min (by have := le_abs_self (c₀ - c₁); linarith)
    ((le_abs_self c₀).trans hc₀)

theorem zeroTargetPairSeed_at_right {P : Type u} [MetricSpace P]
    {T : Set P} {p q : P} {c₀ c₁ : ℝ}
    (hc₁ : |c₁| ≤ Metric.infDist q T)
    (hpq : |c₀ - c₁| ≤ dist p q) :
    zeroTargetPairSeed T p q c₀ c₁ q = c₁ := by
  rw [zeroTargetPairSeed, dist_self, add_zero,
    min_eq_left ((le_abs_self c₁).trans hc₁), min_eq_right]
  rw [dist_comm]
  have := neg_le_abs (c₀ - c₁)
  linarith

/-- If `d ≤ a₀+a₁`, one can choose signed endpoint values bounded by the two
legs and having difference exactly `d`. -/
theorem exists_signed_values {d a₀ a₁ : ℝ} (hd : 0 ≤ d)
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hle : d ≤ a₀ + a₁) :
    ∃ c₀ c₁ : ℝ, |c₀| ≤ a₀ ∧ |c₁| ≤ a₁ ∧ c₀ - c₁ = d := by
  let c₀ := min d a₀
  let c₁ := c₀ - d
  have hc₀_nonneg : 0 ≤ c₀ := by simp [c₀, hd, ha₀]
  have hc₀_le_a₀ : c₀ ≤ a₀ := min_le_right _ _
  have hc₀_le_d : c₀ ≤ d := min_le_left _ _
  have hc₁_nonpos : c₁ ≤ 0 := by simp only [c₁]; linarith
  have hc₁_lower : -a₁ ≤ c₁ := by
    simp only [c₁, c₀]
    rcases le_total d a₀ with hda | had
    · rw [min_eq_left hda]
      linarith
    · rw [min_eq_right had]
      linarith
  refine ⟨c₀, c₁, ?_, ?_, by simp [c₁]⟩
  · rw [abs_of_nonneg hc₀_nonneg]
    exact hc₀_le_a₀
  · rw [abs_of_nonpos hc₁_nonpos]
    linarith

/-- First short-distance case from the relative-envelope proof: if the direct
distance is at most the sum of the distances to the old target, a functional
vanishing on the old target attains that distance. -/
theorem relativeEvaluation_dist_eq_of_dist_le_infDist_add {P : Type u}
    {N : Type v} [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (p q : P)
    (hle : dist p q ≤ Metric.infDist p (Set.range j) +
      Metric.infDist q (Set.range j)) :
    dist (relativeEvaluation j p) (relativeEvaluation j q) = dist p q := by
  obtain ⟨c₀, c₁, hc₀, hc₁, hdiff⟩ := exists_signed_values dist_nonneg
    Metric.infDist_nonneg Metric.infDist_nonneg hle
  let φ : RelativeFunctional P N j := {
    linear := 0
    norm_le_one := by simp
    value := zeroTargetPairSeed (Set.range j) p q c₀ c₁
    lipschitz := zeroTargetPairSeed_lipschitz (Set.range j) p q c₀ c₁
    agree := fun n => by
      rw [zeroTargetPairSeed_of_mem hc₀ hc₁ (Set.mem_range_self n)]
      simp }
  apply relativeEvaluation_dist_eq_of_attains j p q φ
  change zeroTargetPairSeed (Set.range j) p q c₀ c₁ p -
      zeroTargetPairSeed (Set.range j) p q c₀ c₁ q = dist p q
  have habs : |c₀ - c₁| ≤ dist p q := by
    rw [hdiff, abs_of_nonneg dist_nonneg]
  rw [zeroTargetPairSeed_at_left hc₀ habs,
    zeroTargetPairSeed_at_right hc₁ habs, hdiff]

/-- A norming functional can be chosen for the difference of two old-space
vectors. -/
theorem exists_norming_difference {N : Type v} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (n₀ n₁ : N) :
    ∃ L : N →L[ℝ] ℝ, ‖L‖ ≤ 1 ∧ L n₀ - L n₁ = ‖n₀ - n₁‖ := by
  obtain ⟨L, hL, hdiff⟩ := exists_dual_vector'' ℝ (n₀ - n₁)
  refine ⟨L, hL, ?_⟩
  rw [← map_sub]
  simpa using hdiff

/-- Signed vertical endpoint values bounded by `|sᵢ|` can be chosen with
difference `|s₀-s₁|`. -/
theorem exists_vertical_signed_values (s₀ s₁ : ℝ) :
    ∃ c₀ c₁ : ℝ,
      |c₀| ≤ |s₀| ∧ |c₁| ≤ |s₁| ∧ c₀ - c₁ = |s₀ - s₁| := by
  apply exists_signed_values (abs_nonneg (s₀ - s₁)) (abs_nonneg s₀) (abs_nonneg s₁)
  exact abs_sub s₀ s₁

/-- The algebraic data for the collar case jointly attain the sum of the
horizontal norm difference and the vertical absolute difference. -/
theorem exists_collar_endpoint_data {N : Type v} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (n₀ n₁ : N) (s₀ s₁ : ℝ) :
    ∃ (L : N →L[ℝ] ℝ) (c₀ c₁ : ℝ),
      ‖L‖ ≤ 1 ∧ |c₀| ≤ |s₀| ∧ |c₁| ≤ |s₁| ∧
        (L n₀ + c₀) - (L n₁ + c₁) = ‖n₀ - n₁‖ + |s₀ - s₁| := by
  obtain ⟨L, hL, hhorizontal⟩ := exists_norming_difference n₀ n₁
  obtain ⟨c₀, c₁, hc₀, hc₁, hvertical⟩ := exists_vertical_signed_values s₀ s₁
  refine ⟨L, c₀, c₁, hL, hc₀, hc₁, ?_⟩
  linarith

/-- Compatible values on the old target and two selected points extend to an
admissible relative functional.  The proof uses a possibly noninjective map
from `N ⊕ Bool`; metric compatibility forces the prescribed values to agree
at every collision. -/
theorem exists_relativeFunctional_with_two_values {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (hj : Isometry j) (L : N →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (p q : P) (b₀ b₁ : ℝ)
    (h₀ : ∀ n, dist b₀ (L n) ≤ dist p (j n))
    (h₁ : ∀ n, dist b₁ (L n) ≤ dist q (j n))
    (hpair : dist b₀ b₁ ≤ dist p q) :
    ∃ φ : RelativeFunctional P N j,
      φ.linear = L ∧ φ.value p = b₀ ∧ φ.value q = b₁ := by
  let k : N ⊕ Bool → P
    | Sum.inl n => j n
    | Sum.inr false => p
    | Sum.inr true => q
  let val : N ⊕ Bool → ℝ
    | Sum.inl n => L n
    | Sum.inr false => b₀
    | Sum.inr true => b₁
  have hcompat (x y : N ⊕ Bool) : dist (val x) (val y) ≤ dist (k x) (k y) := by
    cases x with
    | inl n =>
        cases y with
        | inl m =>
            change dist (L n) (L m) ≤ dist (j n) (j m)
            rw [hj.dist_eq]
            rw [Real.dist_eq, ← map_sub]
            calc
              ‖L (n - m)‖ ≤ ‖L‖ * ‖n - m‖ := L.le_opNorm (n - m)
              _ ≤ 1 * ‖n - m‖ :=
                mul_le_mul_of_nonneg_right hL (norm_nonneg (n - m))
              _ = dist n m := by simp [dist_eq_norm]
        | inr b =>
            cases b <;> change dist (L n) _ ≤ dist (j n) _
            · simpa only [val, k, dist_comm] using h₀ n
            · simpa only [val, k, dist_comm] using h₁ n
    | inr b =>
        cases y with
        | inl n =>
            cases b <;> change dist _ (L n) ≤ dist _ (j n)
            · exact h₀ n
            · exact h₁ n
        | inr c =>
            cases b <;> cases c
            · simp [val, k]
            · simpa only [val, k] using hpair
            · simpa only [val, k, dist_comm] using hpair
            · simp [val, k]
  have hfactor : val.FactorsThrough k := by
    intro x y hxy
    apply dist_eq_zero.mp
    have hle := hcompat x y
    rw [hxy, dist_self] at hle
    exact le_antisymm hle dist_nonneg
  let seed : P → ℝ := Function.extend k val (fun _ => 0)
  have hseed : LipschitzOnWith 1 seed (Set.range k) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rcases hx with ⟨i, rfl⟩
    rcases hy with ⟨l, rfl⟩
    simpa [seed, hfactor.extend_apply] using hcompat i l
  have htargets : Set.range j ⊆ Set.range k := by
    rintro _ ⟨n, rfl⟩
    exact ⟨Sum.inl n, rfl⟩
  have hagree (n : N) : seed (j n) = L n := by
    change seed (k (Sum.inl n)) = val (Sum.inl n)
    exact hfactor.extend_apply (fun _ => 0) (Sum.inl n)
  obtain ⟨φ, hφL, hext⟩ :=
    exists_relativeFunctional_extending j L hL (Set.range k) seed
      htargets hseed hagree
  refine ⟨φ, hφL, ?_, ?_⟩
  · rw [← hext ⟨Sum.inr false, rfl⟩]
    change seed (k (Sum.inr false)) = val (Sum.inr false)
    exact hfactor.extend_apply (fun _ => 0) (Sum.inr false)
  · rw [← hext ⟨Sum.inr true, rfl⟩]
    change seed (k (Sum.inr true)) = val (Sum.inr true)
    exact hfactor.extend_apply (fun _ => 0) (Sum.inr true)

/-- In the protected collar, the algebraic endpoint data and the exact
source--target formula produce an admissible functional attaining the distance
of a short source pair. -/
theorem relativeEvaluation_adjunctionSource_dist_eq_of_collar
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {N : Type v} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V : M → N} {a : M} {y : N} {H r : ℝ}
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hr : 0 < r) (hH : 2 * r + dist (V a) y < H)
    (hshort : PreservesUpTo r V)
    (m₀ m₁ : M) {s₀ s₁ : ℝ} (hs₀ : |s₀| < r) (hs₁ : |s₁| < r)
    (hd : dist (toLp 1 (m₀, s₀) : OneSum M) (toLp 1 (m₁, s₁)) ≤ r) :
    let j := adjunctionTargetMk V a y H hattach
    let p₀ := adjunctionSourceMk V a y H hattach (toLp 1 (m₀, s₀))
    let p₁ := adjunctionSourceMk V a y H hattach (toLp 1 (m₁, s₁))
    dist (relativeEvaluation j p₀) (relativeEvaluation j p₁) = dist p₀ p₁ := by
  dsimp only
  let j := adjunctionTargetMk V a y H hattach
  let p₀ := adjunctionSourceMk V a y H hattach (toLp 1 (m₀, s₀))
  let p₁ := adjunctionSourceMk V a y H hattach (toLp 1 (m₁, s₁))
  obtain ⟨L, c₀, c₁, hL, hc₀, hc₁, hend⟩ :=
    exists_collar_endpoint_data (V m₀) (V m₁) s₀ s₁
  have hLdist (n₀ n₁ : N) : dist (L n₀) (L n₁) ≤ dist n₀ n₁ := by
    rw [Real.dist_eq, dist_eq_norm, ← map_sub]
    simpa using (L.le_opNorm (n₀ - n₁)).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg (n₀ - n₁)))
  have h₀ (n : N) : dist (L (V m₀) + c₀) (L n) ≤ dist p₀ (j n) := by
    rw [show dist p₀ (j n) = |s₀| + dist (V m₀) n by
      simpa [p₀, j] using
        dist_adjunctionSourceMk_targetMk_eq_collar hattach hr hH hshort m₀ hs₀ n]
    calc
      dist (L (V m₀) + c₀) (L n) ≤
          dist (L (V m₀) + c₀) (L (V m₀)) + dist (L (V m₀)) (L n) :=
        dist_triangle _ _ _
      _ = |c₀| + dist (L (V m₀)) (L n) := by simp [Real.dist_eq]
      _ ≤ |s₀| + dist (V m₀) n := add_le_add hc₀ (hLdist _ _)
  have h₁ (n : N) : dist (L (V m₁) + c₁) (L n) ≤ dist p₁ (j n) := by
    rw [show dist p₁ (j n) = |s₁| + dist (V m₁) n by
      simpa [p₁, j] using
        dist_adjunctionSourceMk_targetMk_eq_collar hattach hr hH hshort m₁ hs₁ n]
    calc
      dist (L (V m₁) + c₁) (L n) ≤
          dist (L (V m₁) + c₁) (L (V m₁)) + dist (L (V m₁)) (L n) :=
        dist_triangle _ _ _
      _ = |c₁| + dist (L (V m₁)) (L n) := by simp [Real.dist_eq]
      _ ≤ |s₁| + dist (V m₁) n := add_le_add hc₁ (hLdist _ _)
  have hhorizontal : dist (V m₀) (V m₁) = dist m₀ m₁ := by
    apply hshort
    calc
      dist m₀ m₁ ≤ dist (toLp 1 (m₀, s₀) : OneSum M) (toLp 1 (m₁, s₁)) := by
        rw [oneSum_dist_eq]
        exact le_add_of_nonneg_right (abs_nonneg (s₀ - s₁))
      _ ≤ r := hd
  have hpdist : dist p₀ p₁ = dist m₀ m₁ + |s₀ - s₁| := by
    rw [show dist p₀ p₁ =
        dist (toLp 1 (m₀, s₀) : OneSum M) (toLp 1 (m₁, s₁)) by
      exact dist_adjunctionSourceMk_of_short hattach hr
        (by have : 0 ≤ dist (V a) y := dist_nonneg; linarith) hshort hd]
    exact oneSum_dist_eq _ _
  have hpair : dist (L (V m₀) + c₀) (L (V m₁) + c₁) ≤ dist p₀ p₁ := by
    rw [Real.dist_eq, hend, abs_of_nonneg]
    · rw [hpdist, ← hhorizontal, dist_eq_norm]
    · positivity
  obtain ⟨φ, -, hφ₀, hφ₁⟩ :=
    exists_relativeFunctional_with_two_values j
      (adjunctionTargetMk_isometry V a y H hattach) L hL p₀ p₁
      (L (V m₀) + c₀) (L (V m₁) + c₁) h₀ h₁ hpair
  apply relativeEvaluation_dist_eq_of_attains j p₀ p₁ φ
  rw [hφ₀, hφ₁, hend, hpdist, ← hhorizontal, dist_eq_norm]

/-- The two cases combine to show that the relative evaluation coordinate
preserves every protected short source distance. -/
theorem relativeEvaluation_adjunctionSource_dist_eq_of_short
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {N : Type v} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V : M → N} {a : M} {y : N} {H r : ℝ}
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hr : 0 < r) (hH : 2 * r + dist (V a) y < H)
    (hshort : PreservesUpTo r V) (m₀ m₁ : M) {s₀ s₁ : ℝ}
    (hd : dist (toLp 1 (m₀, s₀) : OneSum M) (toLp 1 (m₁, s₁)) ≤ r) :
    let j := adjunctionTargetMk V a y H hattach
    let p₀ := adjunctionSourceMk V a y H hattach (toLp 1 (m₀, s₀))
    let p₁ := adjunctionSourceMk V a y H hattach (toLp 1 (m₁, s₁))
    dist (relativeEvaluation j p₀) (relativeEvaluation j p₁) = dist p₀ p₁ := by
  dsimp only
  let j := adjunctionTargetMk V a y H hattach
  let x₀ : OneSum M := toLp 1 (m₀, s₀)
  let x₁ : OneSum M := toLp 1 (m₁, s₁)
  let p₀ := adjunctionSourceMk V a y H hattach x₀
  let p₁ := adjunctionSourceMk V a y H hattach x₁
  have hpdist : dist p₀ p₁ = dist x₀ x₁ := by
    exact dist_adjunctionSourceMk_of_short hattach hr
      (by have : 0 ≤ dist (V a) y := dist_nonneg; linarith) hshort hd
  by_cases hcase : dist p₀ p₁ ≤
      Metric.infDist p₀ (Set.range j) + Metric.infDist p₁ (Set.range j)
  · exact relativeEvaluation_dist_eq_of_dist_le_infDist_add j p₀ p₁ hcase
  · have hfar : Metric.infDist x₀ (attachmentSet a H) +
        Metric.infDist x₁ (attachmentSet a H) < dist x₀ x₁ := by
      have hlt := lt_of_not_ge hcase
      rw [infDist_adjunctionTarget_range_eq_attachmentSet V a y H hattach x₀,
        infDist_adjunctionTarget_range_eq_attachmentSet V a y H hattach x₁,
        hpdist] at hlt
      exact hlt
    have hHtwo : 2 * r < H := by
      have : 0 ≤ dist (V a) y := dist_nonneg
      linarith
    obtain ⟨hs₀, hs₁⟩ := abs_lt_of_infDist_add_lt a m₀ m₁ hr hHtwo hd hfar
    exact relativeEvaluation_adjunctionSource_dist_eq_of_collar hattach hr hH hshort
      m₀ m₁ hs₀ hs₁ hd

end ScottishBook155
