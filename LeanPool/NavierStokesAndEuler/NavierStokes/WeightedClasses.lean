/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.JetBounds
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Indexed weighted classes of actual stripped derivatives

The index is a band, not a differentiable variable.  Every derivative below is
Mathlib's `iteratedFDeriv` of the actual coefficient on an open domain.
Constants and polynomial degrees are chosen before the band and point.

The statements hold on real normed spaces, in particular on the Euclidean
strips used by the construction.  Radiality of the prescribed smooth weight
is not needed for these closure results.
-/

namespace NavierStokes.WeightedClasses

noncomputable section

open scoped BigOperators ContDiff

variable {D E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Geometry and positive indexed scales for a stripped coefficient family.
`epsilon` may in particular be `Q n ^ h`. -/
structure StripData (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D] where
  domain : Set D
  isOpen_domain : IsOpen domain
  epsilon : ℕ → ℝ
  epsilon_pos : ∀ n, 0 < epsilon n
  epsilon_le_one : ∀ n, epsilon n ≤ 1
  slow : ℕ → ℝ
  one_le_slow : ∀ n, 1 ≤ slow n
  delta : D → ℝ
  delta_pos : ∀ x ∈ domain, 0 < delta x
  zeta : D → ℝ
  zeta_smooth : ContDiffOn ℝ ∞ zeta domain
  zeta_nonneg : ∀ x ∈ domain, 0 ≤ zeta x

abbrev EuclideanStripData (d : ℕ) := StripData (EuclideanSpace ℝ (Fin d))

/-- A common polynomial degree in `S` and the inverse edge distance is enough:
separate finite degrees can always be increased to their sum.  The maximum
permits arbitrary positive `delta`, agreeing with `delta⁻¹` when `delta ≤ 1`. -/
def StripData.growth (s : StripData D) (n : ℕ) (x : D) : ℝ :=
  s.slow n * max 1 (s.delta x)⁻¹

theorem StripData.one_le_growth (s : StripData D) (n : ℕ) (x : D) :
    1 ≤ s.growth n x :=
  one_le_mul_of_one_le_of_one_le (s.one_le_slow n) (le_max_left _ _)

theorem StripData.growth_nonneg (s : StripData D) (n : ℕ) (x : D) :
    0 ≤ s.growth n x := le_trans zero_le_one (s.one_le_growth n x)

theorem StripData.slow_le_growth (s : StripData D) (n : ℕ) (x : D) :
    s.slow n ≤ s.growth n x := by
  exact le_mul_of_one_le_right ((zero_le_one.trans (s.one_le_slow n)))
    (le_max_left _ _)

theorem StripData.separate_powers_le_growth (s : StripData D) (p q n : ℕ) (x : D) :
    s.slow n ^ p * (max 1 (s.delta x)⁻¹) ^ q ≤ s.growth n x ^ (p + q) := by
  have he0 : 0 ≤ max 1 (s.delta x)⁻¹ := zero_le_one.trans (le_max_left _ _)
  have he : max 1 (s.delta x)⁻¹ ≤ s.growth n x := by
    calc
      _ = 1 * max 1 (s.delta x)⁻¹ := (one_mul _).symm
      _ ≤ s.slow n * max 1 (s.delta x)⁻¹ :=
        mul_le_mul_of_nonneg_right (s.one_le_slow n) he0
  rw [pow_add]
  exact mul_le_mul
    (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x) p)
    (pow_le_pow_left₀ he0 he q) (pow_nonneg he0 q) (pow_nonneg (s.growth_nonneg n x) p)

def majorant (s : StripData D) (w : ℕ → D → ℝ) (α C : ℝ) (p n : ℕ) (x : D) : ℝ :=
  C * s.epsilon n ^ α * s.growth n x ^ p * w n x

theorem majorant_nonneg (s : StripData D) (w : ℕ → D → ℝ) (α : ℝ)
    {C : ℝ} (hC : 0 ≤ C) (p n : ℕ) (x : D) (hw : 0 ≤ w n x) :
    0 ≤ majorant s w α C p n x := by
  unfold majorant
  exact mul_nonneg (mul_nonneg (mul_nonneg hC
    (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le)
    (pow_nonneg (s.growth_nonneg n x) p)) hw

theorem majorant_mono_degree (s : StripData D) (w : ℕ → D → ℝ) (α : ℝ)
    {C : ℝ} (hC : 0 ≤ C) {p q : ℕ} (hpq : p ≤ q) (n : ℕ) (x : D)
    (hw : 0 ≤ w n x) :
    majorant s w α C p n x ≤ majorant s w α C q n x := by
  apply mul_le_mul_of_nonneg_right _ hw
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (s.one_le_growth n x) hpq)
    (mul_nonneg hC (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le)

theorem majorant_mul (s : StripData D) (w v : ℕ → D → ℝ)
    (α β A B : ℝ) (p q n : ℕ) (x : D) :
    majorant s w α A p n x * majorant s v β B q n x =
      majorant s (fun n x => w n x * v n x) (α + β) (A * B) (p + q) n x := by
  unfold majorant
  rw [Real.rpow_add (s.epsilon_pos n), pow_add]
  ring

/-- Actual all-order bounds, uniform in band and point. The finite prefix in
the last quantifier is useful for the higher Leibniz inequality. -/
structure MemClass (s : StripData D) (w : ℕ → D → ℝ) (α : ℝ)
    (f : ℕ → D → E) : Prop where
  weight_nonneg : ∀ n x, x ∈ s.domain → 0 ≤ w n x
  smooth : ∀ n, ContDiffOn ℝ ∞ (f n) s.domain
  bounds : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
    ∀ n x, x ∈ s.domain → ∀ j : ℕ, j ≤ m →
      ‖iteratedFDeriv ℝ j (f n) x‖ ≤ majorant s w α C p n x

abbrev MeanClass (s : StripData D) (α : ℝ) (f : ℕ → D → E) : Prop :=
  MemClass s (fun _ x => s.zeta x) α f

abbrev WaveClass (s : StripData D) (P : ℕ → D → ℝ) (α : ℝ)
    (f : ℕ → D → E) : Prop :=
  MemClass s (fun n x => Real.sqrt (s.zeta x) * P n x) α f

abbrev UnweightedClass (s : StripData D) (α : ℝ) (f : ℕ → D → E) : Prop :=
  MemClass s (fun _ _ => 1) α f

/-- Stage constants are deliberately not uniform in the stage index. -/
def StageClasses (s : StripData D) (w : ℕ → D → ℝ) (α : ℕ → ℝ)
    (f : ℕ → ℕ → D → E) : Prop := ∀ stage, MemClass s w (α stage) (f stage)

/-- A bound on a band-dependent scalar. There is no spatial derivative of
the discrete band index. -/
def BandBound (s : StripData D) (β : ℝ) (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
    ∀ n, ‖a n‖ ≤ C * s.epsilon n ^ β * s.slow n ^ p

namespace MemClass

variable {s : StripData D} {w v : ℕ → D → ℝ} {α β : ℝ}
  {f g : ℕ → D → E}

theorem contDiffAt (hf : MemClass s w α f) (n : ℕ) {x : D}
    (hx : x ∈ s.domain) (m : ℕ) : ContDiffAt ℝ m (f n) x :=
  ((hf.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)

/-- The common-degree definition accepts the manuscript's separate
logarithmic and inverse-edge polynomial degrees. -/
theorem of_separate_bounds
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hsmooth : ∀ n, ContDiffOn ℝ ∞ (f n) s.domain)
    (hb : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p q : ℕ,
      ∀ n x, x ∈ s.domain → ∀ j : ℕ, j ≤ m →
        ‖iteratedFDeriv ℝ j (f n) x‖ ≤
          C * s.epsilon n ^ α * s.slow n ^ p * (max 1 (s.delta x)⁻¹) ^ q * w n x) :
    MemClass s w α f := by
  refine ⟨hw, hsmooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, q, h⟩ := hb m
  refine ⟨C, hC, p + q, ?_⟩
  intro n x hx j hj
  apply (h n x hx j hj).trans
  calc
    _ = (C * s.epsilon n ^ α) *
        (s.slow n ^ p * (max 1 (s.delta x)⁻¹) ^ q) * w n x := by ring
    _ ≤ (C * s.epsilon n ^ α) * s.growth n x ^ (p + q) * w n x :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (s.separate_powers_le_growth p q n x)
          (mul_nonneg hC (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le)) (hw n x hx)
    _ = _ := rfl

theorem zero (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x) :
    MemClass s w α (fun _ _ => (0 : E)) := by
  refine ⟨hw, fun _ => contDiffOn_const, ?_⟩
  intro m
  refine ⟨0, le_rfl, 0, ?_⟩
  intro n x hx j hj
  simp [majorant]

theorem mono_weight (hf : MemClass s w α f)
    (hv : ∀ n x, x ∈ s.domain → 0 ≤ v n x)
    (hwv : ∀ n x, x ∈ s.domain → w n x ≤ v n x) : MemClass s v α f := by
  refine ⟨hv, hf.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, h⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  apply (h n x hx j hj).trans
  apply mul_le_mul_of_nonneg_left (hwv n x hx)
  exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le)
    (pow_nonneg (s.growth_nonneg n x) p)

theorem mono_exponent (hf : MemClass s w α f) (hβα : β ≤ α) :
    MemClass s w β f := by
  refine ⟨hf.weight_nonneg, hf.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, h⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  apply (h n x hx j hj).trans
  apply mul_le_mul_of_nonneg_right _ (hf.weight_nonneg n x hx)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (s.growth_nonneg n x) p)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (s.epsilon_pos n) (s.epsilon_le_one n) hβα) hC

theorem add (hf : MemClass s w α f) (hg : MemClass s w α g) :
    MemClass s w α (fun n x => f n x + g n x) := by
  refine ⟨hf.weight_nonneg, fun n => (hf.smooth n).add (hg.smooth n), ?_⟩
  intro m
  obtain ⟨A, hA, p, ha⟩ := hf.bounds m
  obtain ⟨B, hB, q, hb⟩ := hg.bounds m
  refine ⟨A + B, add_nonneg hA hB, p + q, ?_⟩
  intro n x hx j hj
  rw [fun_iteratedFDeriv_add_apply (hf.contDiffAt n hx j) (hg.contDiffAt n hx j)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f n) x‖ + ‖iteratedFDeriv ℝ j (g n) x‖ := norm_add_le _ _
    _ ≤ majorant s w α A p n x + majorant s w α B q n x :=
      add_le_add (ha n x hx j hj) (hb n x hx j hj)
    _ ≤ majorant s w α A (p + q) n x + majorant s w α B (p + q) n x :=
      add_le_add (majorant_mono_degree s w α hA (Nat.le_add_right p q) n x
        (hf.weight_nonneg n x hx))
        (majorant_mono_degree s w α hB (Nat.le_add_left q p) n x
          (hf.weight_nonneg n x hx))
    _ = _ := by unfold majorant; ring

theorem add_min (hf : MemClass s w α f) (hg : MemClass s w β g) :
    MemClass s w (min α β) (fun n x => f n x + g n x) :=
  (hf.mono_exponent (min_le_left _ _)).add (hg.mono_exponent (min_le_right _ _))

theorem fderiv (hf : MemClass s w α f) :
    MemClass s w α (fun n => _root_.fderiv ℝ (f n)) := by
  refine ⟨hf.weight_nonneg, ?_, ?_⟩
  · intro n
    exact (contDiffOn_infty_iff_fderiv_of_isOpen s.isOpen_domain).mp (hf.smooth n) |>.2
  · intro m
    obtain ⟨C, hC, p, h⟩ := hf.bounds (m + 1)
    refine ⟨C, hC, p, ?_⟩
    intro n x hx j hj
    rw [norm_iteratedFDeriv_fderiv]
    exact h n x hx (j + 1) (Nat.add_le_add_right hj 1)

theorem map (hf : MemClass s w α f) (L : E →L[ℝ] F) :
    MemClass s w α (fun n x => L (f n x)) := by
  refine ⟨hf.weight_nonneg, fun n => (hf.smooth n).continuousLinearMap_comp L, ?_⟩
  intro m
  obtain ⟨C, hC, p, h⟩ := hf.bounds m
  refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, p, ?_⟩
  intro n x hx j hj
  change ‖iteratedFDeriv ℝ j (L ∘ f n) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_left (hf.contDiffAt n hx j) le_rfl]
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (f n) x‖ :=
      L.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖L‖ * majorant s w α C p n x :=
      mul_le_mul_of_nonneg_left (h n x hx j hj) (norm_nonneg _)
    _ = _ := by unfold majorant; ring

theorem directional (hf : MemClass s w α f) (v : D) :
    MemClass s w α (fun n x => _root_.fderiv ℝ (f n) x v) :=
  hf.fderiv.map (ContinuousLinearMap.apply ℝ E v)

private theorem bilinear_bound_at (L : E →L[ℝ] F →L[ℝ] G)
    {u : D → E} {v : D → F} {A B : ℝ} {m j : ℕ} {x : D}
    (hx : x ∈ s.domain) (hu : ContDiffOn ℝ ∞ u s.domain)
    (hv : ContDiffOn ℝ ∞ v s.domain) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hju : ∀ i ≤ m, ‖iteratedFDeriv ℝ i u x‖ ≤ A)
    (hjv : ∀ i ≤ m, ‖iteratedFDeriv ℝ i v x‖ ≤ B) (hjm : j ≤ m) :
    ‖iteratedFDeriv ℝ j (fun y => L (u y) (v y)) x‖ ≤
      ‖L‖ * (2 : ℝ) ^ m * A * B := by
  have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i u x‖ * ‖iteratedFDeriv ℝ (j - i) v x‖) ≤
      (2 : ℝ) ^ m * A * B := by
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hju i (hij.trans hjm)) (Nat.cast_nonneg _)
        · exact hjv (j - i) ((Nat.sub_le _ _).trans hjm)
        · exact norm_nonneg _
        · exact mul_nonneg (Nat.cast_nonneg _) hA
      _ = (2 : ℝ) ^ j * A * B := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hc : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [hc]
      _ ≤ (2 : ℝ) ^ m * A * B :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hjm) hA) hB
  calc
    _ ≤ ‖L‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i u x‖ * ‖iteratedFDeriv ℝ (j - i) v x‖ :=
      JetBounds.norm_iteratedFDeriv_bilinear_le_on L s.isOpen_domain hu hv hx
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
    _ ≤ ‖L‖ * ((2 : ℝ) ^ m * A * B) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg L)
    _ = _ := by ring

/-- Actual higher Leibniz estimates add the two decay exponents. -/
theorem bilinear {u : ℕ → D → F} (hf : MemClass s w α f)
    (hu : MemClass s v β u) (L : E →L[ℝ] F →L[ℝ] G) :
    MemClass s (fun n x => w n x * v n x) (α + β)
      (fun n x => L (f n x) (u n x)) := by
  refine ⟨fun n x hx => mul_nonneg (hf.weight_nonneg n x hx) (hu.weight_nonneg n x hx),
    fun n => (L.contDiff.comp_contDiffOn (hf.smooth n)).clm_apply (hu.smooth n), ?_⟩
  intro m
  obtain ⟨A, hA, p, ha⟩ := hf.bounds m
  obtain ⟨B, hB, q, hb⟩ := hu.bounds m
  refine ⟨‖L‖ * (2 : ℝ) ^ m * A * B, by positivity, p + q, ?_⟩
  intro n x hx j hj
  calc
    _ ≤ ‖L‖ * (2 : ℝ) ^ m * majorant s w α A p n x * majorant s v β B q n x :=
      bilinear_bound_at L hx (hf.smooth n) (hu.smooth n)
        (majorant_nonneg s w α hA p n x (hf.weight_nonneg n x hx))
        (majorant_nonneg s v β hB q n x (hu.weight_nonneg n x hx))
        (fun i hi => ha n x hx i hi) (fun i hi => hb n x hx i hi) hj
    _ = (‖L‖ * (2 : ℝ) ^ m) *
        (majorant s w α A p n x * majorant s v β B q n x) := by ring
    _ = _ := by
      rw [majorant_mul]
      unfold majorant
      ring

theorem smul {a : ℕ → D → ℝ} (ha : MemClass s v β a)
    (hf : MemClass s w α f) :
    MemClass s (fun n x => v n x * w n x) (β + α)
      (fun n x => a n x • f n x) :=
  ha.bilinear hf (ContinuousLinearMap.lsmul ℝ ℝ)

theorem mul {a b : ℕ → D → ℝ} (ha : MemClass s w α a)
    (hb : MemClass s v β b) :
    MemClass s (fun n x => w n x * v n x) (α + β)
      (fun n x => a n x * b n x) := by
  simpa only [smul_eq_mul] using ha.smul hb

theorem band_smul {a : ℕ → ℝ} (hf : MemClass s w α f) (ha : BandBound s β a) :
    MemClass s w (α + β) (fun n x => a n • f n x) := by
  obtain ⟨A, hA, p, ha⟩ := ha
  refine ⟨hf.weight_nonneg, fun n => (hf.smooth n).const_smul (a n), ?_⟩
  intro m
  obtain ⟨B, hB, q, hb⟩ := hf.bounds m
  refine ⟨A * B, mul_nonneg hA hB, p + q, ?_⟩
  intro n x hx j hj
  have han : ‖a n‖ ≤ majorant s (fun _ _ => 1) β A p n x := by
    apply (ha n).trans
    simp only [majorant, mul_one]
    apply mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x) p)
    exact mul_nonneg hA (Real.rpow_pos_of_pos (s.epsilon_pos n) β).le
  rw [iteratedFDeriv_const_smul_apply' (hf.contDiffAt n hx j)]
  rw [norm_smul (a n) (iteratedFDeriv ℝ j (f n) x)]
  calc
    _ ≤ majorant s (fun _ _ => 1) β A p n x * majorant s w α B q n x :=
      mul_le_mul han (hb n x hx j hj) (norm_nonneg _)
        (majorant_nonneg s (fun _ _ => 1) β hA p n x (by norm_num))
    _ = majorant s (fun n x => 1 * w n x) (β + α) (A * B) (p + q) n x :=
      majorant_mul s (fun _ _ => 1) w β α A B p q n x
    _ = _ := by simp only [majorant, one_mul, add_comm β α]

theorem sum {ι : Type*} (t : Finset ι) (u : ι → ℕ → D → E)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hu : ∀ i ∈ t, MemClass s w α (u i)) :
    MemClass s w α (fun n x => ∑ i ∈ t, u i n x) := by
  classical
  revert hu
  induction t using Finset.induction_on with
  | empty =>
      intro _
      simpa using (zero (s := s) (α := α) (E := E) hw)
  | @insert i t hit ih =>
      intro hu
      have hi := hu i (Finset.mem_insert_self i t)
      have ht := ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hit] using hi.add ht

end MemClass

/-- Constant coefficients give nonzero examples of the unweighted class. -/
theorem unweighted_const (s : StripData D) (c : E) :
    UnweightedClass s 0 (fun _ _ => c) := by
  refine ⟨fun _ _ _ => zero_le_one, fun _ => contDiffOn_const, ?_⟩
  intro m
  refine ⟨‖c‖, norm_nonneg c, 0, ?_⟩
  intro n x hx j hj
  by_cases hj0 : j = 0
  · subst j
    simp [majorant, norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne hj0]
    simp [majorant]

/-- A fixed coefficient with uniform finite jet bounds is an order-zero
unweighted coefficient. This connects the class directly to `JetBounds`. -/
theorem unweighted_of_finiteJetBounds (s : StripData D) (a : D → E)
    (ha : ContDiffOn ℝ ∞ a s.domain)
    (hb : ∀ m : ℕ, ∃ C : ℝ, JetBounds.FiniteJetBound m a s.domain C) :
    UnweightedClass s 0 (fun _ => a) := by
  refine ⟨fun _ _ _ => zero_le_one, fun _ => ha, ?_⟩
  intro m
  obtain ⟨C, hC⟩ := hb m
  refine ⟨max C 0, le_max_right _ _, 0, ?_⟩
  intro n x hx j hj
  simpa only [majorant, Real.rpow_zero, pow_zero, mul_one] using
    (hC j hj x hx).trans (le_max_left C 0)

theorem bandBound_rpow (s : StripData D) (β : ℝ) :
    BandBound s β (fun n => s.epsilon n ^ β) := by
  refine ⟨1, zero_le_one, 0, ?_⟩
  intro n
  simp [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (s.epsilon_pos n) β)]

/-- Wave products have the mean weight. This uses the actual Leibniz estimate
on coefficients, followed by `(sqrt ζ * P)^2 ≤ ζ`; no derivative identity for
the envelope `P` is postulated. -/
theorem WaveClass.bilinear_mean {s : StripData D} {P : ℕ → D → ℝ}
    {α β : ℝ} {f : ℕ → D → E} {g : ℕ → D → F}
    (hf : WaveClass s P α f) (hg : WaveClass s P β g)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1)
    (L : E →L[ℝ] F →L[ℝ] G) :
    MeanClass s (α + β) (fun n x => L (f n x) (g n x)) := by
  apply (MemClass.bilinear hf hg L).mono_weight (fun _ x hx => s.zeta_nonneg x hx)
  intro n x hx
  have hP2 : P n x * P n x ≤ 1 := by
    nlinarith [hP0 n x hx, hP1 n x hx]
  calc
    _ = (Real.sqrt (s.zeta x)) ^ 2 * (P n x * P n x) := by ring
    _ = s.zeta x * (P n x * P n x) := by rw [Real.sq_sqrt (s.zeta_nonneg x hx)]
    _ ≤ s.zeta x * 1 := mul_le_mul_of_nonneg_left hP2 (s.zeta_nonneg x hx)
    _ = _ := mul_one _

theorem WaveClass.mul_mean {s : StripData D} {P : ℕ → D → ℝ}
    {α β : ℝ} {f g : ℕ → D → ℝ}
    (hf : WaveClass s P α f) (hg : WaveClass s P β g)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    MeanClass s (α + β) (fun n x => f n x * g n x) := by
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    hf.bilinear_mean hg hP0 hP1 (ContinuousLinearMap.lsmul ℝ ℝ)

/-- A normalized bounded radial weight makes the mean class an algebra. -/
theorem MeanClass.bilinear {s : StripData D} {α β : ℝ}
    {f : ℕ → D → E} {g : ℕ → D → F}
    (hf : MeanClass s α f) (hg : MeanClass s β g)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) (L : E →L[ℝ] F →L[ℝ] G) :
    MeanClass s (α + β) (fun n x => L (f n x) (g n x)) := by
  apply (MemClass.bilinear hf hg L).mono_weight (fun _ x hx => s.zeta_nonneg x hx)
  intro n x hx
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (hζ x hx) (s.zeta_nonneg x hx)

theorem MeanClass.bilinear_wave {s : StripData D} {P : ℕ → D → ℝ}
    {α β : ℝ} {f : ℕ → D → E} {g : ℕ → D → F}
    (hf : MeanClass s α f) (hg : WaveClass s P β g)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) (L : E →L[ℝ] F →L[ℝ] G) :
    WaveClass s P (α + β) (fun n x => L (f n x) (g n x)) := by
  apply (MemClass.bilinear hf hg L).mono_weight hg.weight_nonneg
  intro n x hx
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (hζ x hx) (hg.weight_nonneg n x hx)

/-- An explicit radial graph operator with a band coefficient `M` and a
spatial coefficient `a`. The two directions can be radial and auxiliary. -/
noncomputable def graphDerivative (M : ℕ → ℝ) (a : D → ℝ) (e v : D)
    (f : ℕ → D → E) : ℕ → D → E :=
  fun n x => fderiv ℝ (f n) x e + M n • (a x • fderiv ℝ (f n) x v)

/-- The expanded operator really is differentiation along its graph vector. -/
theorem graphDerivative_eq_along (M : ℕ → ℝ) (a : D → ℝ) (e v : D)
    (f : ℕ → D → E) (n : ℕ) (x : D) :
    graphDerivative M a e v f n x =
      fderiv ℝ (f n) x (e + M n • (a x • v)) := by
  simp [graphDerivative]

/-- One explicit graph derivative loses at most `κ` in the band exponent.
The coefficient hypothesis is an actual all-jet bound on `a`, not a claim
about the desired output. -/
theorem MemClass.graphDerivative {s : StripData D} {w : ℕ → D → ℝ}
    {α κ : ℝ} {f : ℕ → D → E} {M : ℕ → ℝ} {a : D → ℝ}
    (hf : MemClass s w α f) (ha : UnweightedClass s 0 (fun _ => a))
    (hM : BandBound s (-κ) M) (hκ : 0 ≤ κ) (e v : D) :
    MemClass s w (α - κ) (graphDerivative M a e v f) := by
  have he : MemClass s w (α - κ) (fun n x => _root_.fderiv ℝ (f n) x e) :=
    (hf.directional e).mono_exponent (sub_le_self α hκ)
  have hv : MemClass s w α (fun n x => a x • _root_.fderiv ℝ (f n) x v) := by
    simpa only [zero_add, one_mul] using MemClass.smul ha (hf.directional v)
  have hmv : MemClass s w (α - κ)
      (fun n x => M n • (a x • _root_.fderiv ℝ (f n) x v)) := by
    simpa only [sub_eq_add_neg] using hv.band_smul hM
  exact he.add hmv

noncomputable def graphIterate (M : ℕ → ℝ) (a : D → ℝ) (e v : D)
    (f : ℕ → D → E) : ℕ → ℕ → D → E
  | 0 => f
  | j + 1 => graphDerivative M a e v (graphIterate M a e v f j)

/-- Every finite number of explicit graph derivatives has its finite loss.
Arbitrarily high *additional stripped jets* are still controlled at the same
resulting exponent, as recorded by `MemClass`. -/
theorem MemClass.graphIterate {s : StripData D} {w : ℕ → D → ℝ}
    {α κ : ℝ} {f : ℕ → D → E} {M : ℕ → ℝ} {a : D → ℝ}
    (hf : MemClass s w α f) (ha : UnweightedClass s 0 (fun _ => a))
    (hM : BandBound s (-κ) M) (hκ : 0 ≤ κ) (e v : D) (j : ℕ) :
    MemClass s w (α - (j : ℝ) * κ) (graphIterate M a e v f j) := by
  induction j with
  | zero =>
    unfold WeightedClasses.graphIterate
    simpa only [Nat.cast_zero, zero_mul, sub_zero] using hf
  | succ j ih =>
      have h := ih.graphDerivative ha hM hκ e v
      have he : (α - (j : ℝ) * κ) - κ = α - ((j + 1 : ℕ) : ℝ) * κ := by
        push_cast
        ring
      rw [he] at h
      exact h

end

end NavierStokes.WeightedClasses
