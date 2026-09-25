/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.Birkhoff
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic

/-! # Entropy -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-- A probability vector on a finite type. -/
def IsProbabilityVector
    {ι : Type*} [Fintype ι] (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- A probability vector with full support. -/
def IsStrictProbabilityVector
    {ι : Type*} [Fintype ι] (p : ι → ℝ) : Prop :=
  IsProbabilityVector p ∧ ∀ i, 0 < p i

theorem IsStrictProbabilityVector.probability
    {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : IsStrictProbabilityVector p) :
    IsProbabilityVector p :=
  hp.1

theorem IsStrictProbabilityVector.positive
    {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : IsStrictProbabilityVector p) (i : ι) :
    0 < p i :=
  hp.2 i

theorem IsProbabilityVector.nonnegative
    {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : IsProbabilityVector p) (i : ι) :
    0 ≤ p i :=
  hp.1 i

theorem IsProbabilityVector.sum_eq_one
    {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : IsProbabilityVector p) :
    ∑ i, p i = 1 :=
  hp.2

theorem IsProbabilityVector.le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (hp : IsProbabilityVector p) (i : ι) :
    p i ≤ 1 := by
  rw [← hp.sum_eq_one]
  exact Finset.single_le_sum
    (fun j _ ↦ hp.nonnegative j) (Finset.mem_univ i)

theorem IsDoublyStochastic.row_probability
    {n : Type*} [Fintype n] {X : Matrix n n ℝ}
    (hX : IsDoublyStochastic X) (i : n) :
    IsProbabilityVector (X i) := by
  exact ⟨hX.nonnegative i, hX.row_sum i⟩

/-- Shannon entropy with the convention `0 log 0 = 0`. -/
noncomputable def shannonEntropy
    {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

theorem shannonEntropy_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (hp : IsProbabilityVector p) :
    0 ≤ shannonEntropy p := by
  apply Finset.sum_nonneg
  intro i _
  exact Real.negMulLog_nonneg (hp.nonnegative i) (hp.le_one i)

/-- Entropy is at most the logarithm of the support size. -/
theorem shannonEntropy_le_log_card
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {p : ι → ℝ} (hp : IsProbabilityVector p) :
    shannonEntropy p ≤ Real.log (Fintype.card ι) := by
  let N : ℝ := Fintype.card ι
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  have hweights : ∑ _i : ι, (1 / N : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp [N]
    field_simp
  have hJ := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := fun _i : ι ↦ 1 / N) (p := p)
    (fun _ _ ↦ by positivity) hweights
    (fun i _ ↦ hp.nonnegative i)
  have havg :
      (1 / N) * shannonEntropy p ≤ Real.negMulLog (1 / N) := by
    simpa only [smul_eq_mul, shannonEntropy, ← Finset.mul_sum,
      hp.sum_eq_one, mul_one] using hJ
  have hmul := mul_le_mul_of_nonneg_left havg hN.le
  have hleft : N * ((1 / N) * shannonEntropy p) = shannonEntropy p := by
    field_simp
  have hright : N * Real.negMulLog (1 / N) = Real.log N := by
    rw [Real.negMulLog_def]
    field_simp
    simp [Real.log_inv]
  rw [hleft, hright] at hmul
  simpa [N] using hmul

/-- Total row entropy of a doubly stochastic matrix. -/
noncomputable def totalRowEntropy
    {n : Type*} [Fintype n] (X : Matrix n n ℝ) : ℝ :=
  ∑ i, shannonEntropy (X i)

theorem totalRowEntropy_nonneg
    {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℝ} (hX : IsDoublyStochastic X) :
    0 ≤ totalRowEntropy X := by
  exact Finset.sum_nonneg fun i _ ↦
    shannonEntropy_nonneg (hX.row_probability i)

theorem totalRowEntropy_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {X : Matrix n n ℝ} (hX : IsDoublyStochastic X) :
    totalRowEntropy X ≤
      Fintype.card n * Real.log (Fintype.card n) := by
  rw [totalRowEntropy]
  calc
    ∑ i, shannonEntropy (X i)
        ≤ ∑ _i : n, Real.log (Fintype.card n) :=
          Finset.sum_le_sum fun i _ ↦
            shannonEntropy_le_log_card (hX.row_probability i)
    _ = Fintype.card n * Real.log (Fintype.card n) := by
      simp [nsmul_eq_mul]

/-- Binary entropy, again with the continuous boundary convention. -/
noncomputable def binaryEntropy (t : ℝ) : ℝ :=
  Real.negMulLog t + Real.negMulLog (1 - t)

theorem binaryEntropy_symm (t : ℝ) :
    binaryEntropy (1 - t) = binaryEntropy t := by
  rw [binaryEntropy, binaryEntropy]
  ring_nf

/-- Exact entropy loss when two positive atoms of masses `u` and `v` are
merged.  This is the scalar identity used in paper (26). -/
theorem entropy_loss_merge_two {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Real.negMulLog u + Real.negMulLog v - Real.negMulLog (u + v) =
      (u + v) * binaryEntropy (u / (u + v)) := by
  have hs : u + v ≠ 0 := (add_pos hu hv).ne'
  have hratio : 1 - u / (u + v) = v / (u + v) := by
    field_simp
    ring
  rw [binaryEntropy, hratio]
  simp only [Real.negMulLog_def]
  rw [Real.log_div hu.ne' hs, Real.log_div hv.ne' hs]
  field_simp
  ring

/-- Finite log-sum inequality with strictly positive weights.  This is the
one-sided, certificate-producing half of the entropy duality for capacity. -/
theorem log_sum_inequality
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {θ w : ι → ℝ}
    (hθ : ∀ i, 0 < θ i) (hθsum : ∑ i, θ i = 1)
    (hw : ∀ i, 0 < w i) :
    ∑ i, θ i * Real.log (w i / θ i) ≤ Real.log (∑ i, w i) := by
  let r : ι → ℝ := fun i ↦ w i / θ i
  have hr : ∀ i, 0 < r i := fun i ↦ div_pos (hw i) (hθ i)
  have hAM := Real.geom_mean_le_arith_mean_weighted
    Finset.univ θ r
    (fun i _ ↦ (hθ i).le) hθsum
    (fun i _ ↦ (hr i).le)
  have harith : ∑ i, θ i * r i = ∑ i, w i := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [r]
    field_simp [(hθ i).ne']
  rw [harith] at hAM
  have hprod : 0 < ∏ i, (r i) ^ (θ i) :=
    Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hr i) _
  have hlog := Real.log_le_log hprod hAM
  rw [Real.log_prod (fun i _ ↦ (Real.rpow_pos_of_pos (hr i) _).ne')] at hlog
  simp_rw [Real.log_rpow (hr _) ] at hlog
  simpa [r] using hlog

/-- Log-sum with zero weights allowed.  Terms of weight zero use Lean's
continuous convention `0 * log 0 = 0`; the proof restricts to the positive
support before applying the strict version. -/
theorem log_sum_inequality_nonnegative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {θ w : ι → ℝ}
    (hθ : ∀ i, 0 ≤ θ i) (hθsum : ∑ i, θ i = 1)
    (hw : ∀ i, 0 < w i) :
    ∑ i, θ i * Real.log (w i / θ i) ≤ Real.log (∑ i, w i) := by
  let s : Finset ι := Finset.univ.filter fun i ↦ 0 < θ i
  have hs : s.Nonempty := by
    by_contra hempty
    have hzero : ∀ i, θ i = 0 := by
      intro i
      have hnot : ¬0 < θ i := by
        intro hi
        exact hempty ⟨i, by simp [s, hi]⟩
      exact le_antisymm (le_of_not_gt hnot) (hθ i)
    have : (∑ i, θ i) = 0 := by simp [hzero]
    linarith
  letI : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  let θs : s → ℝ := fun i ↦ θ i
  let ws : s → ℝ := fun i ↦ w i
  have hθs : ∀ i, 0 < θs i := by
    intro i
    exact (Finset.mem_filter.mp i.property).2
  have hθsSum : ∑ i, θs i = 1 := by
    have hsupport : (∑ i ∈ s, θ i) = ∑ i, θ i := by
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      have hnot : ¬0 < θ i := by
        intro hpos
        exact hi (by simp [s, hpos])
      exact le_antisymm (le_of_not_gt hnot) (hθ i)
    calc
      (∑ i : s, θs i) = ∑ i ∈ s, θ i := by
        simpa [θs] using Finset.sum_coe_sort s (fun i ↦ θ i)
      _ = 1 := by rw [hsupport, hθsum]
  have hstrict := log_sum_inequality hθs hθsSum (fun i ↦ hw i)
  have hleft : (∑ i : s, θs i * Real.log (ws i / θs i)) =
      ∑ i, θ i * Real.log (w i / θ i) := by
    have hsupport :
        (∑ i ∈ s, θ i * Real.log (w i / θ i)) =
          ∑ i, θ i * Real.log (w i / θ i) := by
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      have hnot : ¬0 < θ i := by
        intro hpos
        exact hi (by simp [s, hpos])
      have hzero : θ i = 0 := le_antisymm (le_of_not_gt hnot) (hθ i)
      simp [hzero]
    calc
      (∑ i : s, θs i * Real.log (ws i / θs i)) =
          ∑ i ∈ s, θ i * Real.log (w i / θ i) := by
        simpa [θs, ws] using Finset.sum_coe_sort s
          (fun i ↦ θ i * Real.log (w i / θ i))
      _ = ∑ i, θ i * Real.log (w i / θ i) := hsupport
  have hrightSupport : (∑ i : s, ws i) = ∑ i ∈ s, w i := by
    simpa [ws] using Finset.sum_coe_sort s (fun i ↦ w i)
  have hsupportPos : 0 < ∑ i : s, ws i :=
    Finset.sum_pos (fun i _ ↦ hw i) Finset.univ_nonempty
  have hallPos : 0 < ∑ i, w i :=
    Finset.sum_pos (fun i _ ↦ hw i) (hs.mono (Finset.subset_univ s))
  have hsumLe : (∑ i : s, ws i) ≤ ∑ i, w i := by
    rw [hrightSupport]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun i _ _ ↦ (hw i).le)
  rw [hleft] at hstrict
  exact hstrict.trans (Real.log_le_log hsupportPos hsumLe)

/-- Entropy bound for a nonnegative vector of total mass `ρ`.  This is the
scaled form used for the outside mass in paper (60). -/
theorem shannonEntropy_of_mass_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : ι → ℝ} {ρ : ℝ}
    (hα : ∀ i, 0 ≤ α i) (hρ : 0 < ρ) (hsum : ∑ i, α i = ρ) :
    shannonEntropy α ≤ ρ * Real.log (Fintype.card ι / ρ) := by
  let q : ι → ℝ := fun i ↦ α i / ρ
  have hq : IsProbabilityVector q := by
    constructor
    · intro i
      exact div_nonneg (hα i) hρ.le
    · dsimp [q]
      rw [← Finset.sum_div, hsum, div_self hρ.ne']
  have hscale : shannonEntropy α =
      ρ * shannonEntropy q - ρ * Real.log ρ := by
    calc
      shannonEntropy α =
          ∑ i, (ρ * Real.negMulLog (q i) - α i * Real.log ρ) := by
            rw [shannonEntropy]
            apply Finset.sum_congr rfl
            intro i _
            by_cases hzero : α i = 0
            · simp [hzero, q]
            · simp only [Real.negMulLog_def]
              rw [Real.log_div hzero hρ.ne']
              dsimp [q]
              field_simp
              ring
      _ = ρ * shannonEntropy q - (∑ i, α i) * Real.log ρ := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
              ← Finset.sum_mul, shannonEntropy]
      _ = ρ * shannonEntropy q - ρ * Real.log ρ := by rw [hsum]
  have hentropy := shannonEntropy_le_log_card hq
  have hmul := mul_le_mul_of_nonneg_left hentropy hρ.le
  rw [hscale]
  rw [Real.log_div (by exact_mod_cast Fintype.card_ne_zero) hρ.ne']
  linarith

/-- Probability mass induced on the values of a deterministic map. -/
noncomputable def pushforwardMass
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : α → ℝ) (f : α → β) (y : β) : ℝ :=
  ∑ x, if f x = y then μ x else 0

theorem pushforwardMass_isProbabilityVector
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : α → ℝ) (hμ : IsProbabilityVector μ) (f : α → β) :
    IsProbabilityVector (pushforwardMass μ f) := by
  classical
  constructor
  · intro y
    exact Finset.sum_nonneg (fun x _ ↦ by
      by_cases h : f x = y
      · simp only [ite_eq_left h]
        exact hμ.nonnegative x
      · simp only [ite_eq_right h]
        exact le_rfl)
  · simp only [pushforwardMass]
    calc
      (∑ y, ∑ x, if f x = y then μ x else 0) =
          ∑ x, ∑ y, if f x = y then μ x else 0 := Finset.sum_comm
      _ = ∑ x, μ x := by simp
      _ = 1 := hμ.sum_eq_one

theorem pushforwardMass_comp
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ]
    (μ : α → ℝ) (f : α → β) (g : β → γ) (z : γ) :
    pushforwardMass (pushforwardMass μ f) g z =
      pushforwardMass μ (g ∘ f) z := by
  classical
  calc
    pushforwardMass (pushforwardMass μ f) g z =
        ∑ y, ∑ x, if g y = z ∧ f x = y then μ x else 0 := by
      unfold pushforwardMass
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : g y = z
      · simp [hy]
      · simp [hy]
    _ = ∑ x, ∑ y, if g y = z ∧ f x = y then μ x else 0 :=
      Finset.sum_comm
    _ = pushforwardMass μ (g ∘ f) z := by
      unfold pushforwardMass
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : g (f x) = z
      · simp only [Function.comp_apply, ite_eq_left hx]
        rw [Finset.sum_eq_single (f x)]
        · simp [hx]
        · intro y _ hy
          simp [Ne.symm hy]
        · simp
      · simp only [Function.comp_apply, ite_eq_right hx]
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : f x = y
        · subst y
          simp [hx]
        · simp [hy]

theorem pushforwardMass_equiv_apply
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : α → ℝ) (e : α ≃ β) (y : β) :
    pushforwardMass μ e y = μ (e.symm y) := by
  classical
  unfold pushforwardMass
  rw [Finset.sum_eq_single (e.symm y)]
  · simp
  · intro x _ hx
    have hne : e x ≠ y := by
      intro h
      apply hx
      exact e.injective (h.trans (e.apply_symm_apply y).symm)
    simp [hne]
  · simp

theorem shannonEntropy_pushforward_equiv
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : α → ℝ) (e : α ≃ β) :
    shannonEntropy (pushforwardMass μ e) = shannonEntropy μ := by
  simp_rw [shannonEntropy, pushforwardMass_equiv_apply]
  exact e.symm.sum_comp (fun x ↦ Real.negMulLog (μ x))

/-- The first marginal of a probability mass on a finite product. -/
noncomputable def firstMarginal
    {α β : Type*} [Fintype β] (μ : α × β → ℝ) (x : α) : ℝ :=
  ∑ y, μ (x, y)

/-- The second marginal of a probability mass on a finite product. -/
noncomputable def secondMarginal
    {α β : Type*} [Fintype α] (μ : α × β → ℝ) (y : β) : ℝ :=
  ∑ x, μ (x, y)

/-- Conditional second-coordinate mass.  It is set to zero on a zero-mass
first-coordinate fiber, using Lean's division convention. -/
noncomputable def conditionalSecond
    {α β : Type*} [Fintype β] (μ : α × β → ℝ) (x : α) (y : β) : ℝ :=
  μ (x, y) / firstMarginal μ x

theorem firstMarginal_isProbabilityVector
    {α β : Type*} [Fintype α] [Fintype β]
    {μ : α × β → ℝ} (hμ : IsProbabilityVector μ) :
    IsProbabilityVector (firstMarginal μ) := by
  constructor
  · intro x
    exact Finset.sum_nonneg fun y _ ↦ hμ.nonnegative (x, y)
  · change (∑ x, ∑ y, μ (x, y)) = 1
    rw [← Finset.sum_product]
    exact hμ.sum_eq_one

theorem secondMarginal_isProbabilityVector
    {α β : Type*} [Fintype α] [Fintype β]
    {μ : α × β → ℝ} (hμ : IsProbabilityVector μ) :
    IsProbabilityVector (secondMarginal μ) := by
  constructor
  · intro y
    exact Finset.sum_nonneg fun x _ ↦ hμ.nonnegative (x, y)
  · change (∑ y, ∑ x, μ (x, y)) = 1
    rw [Finset.sum_comm, ← Finset.sum_product]
    exact hμ.sum_eq_one

theorem firstMarginal_eq_pushforward_fst
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (μ : α × β → ℝ) :
    firstMarginal μ = pushforwardMass μ Prod.fst := by
  funext x
  unfold firstMarginal pushforwardMass
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x]
  · simp
  · intro z _ hzx
    simp [hzx]
  · simp

theorem secondMarginal_eq_pushforward_snd
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : α × β → ℝ) :
    secondMarginal μ = pushforwardMass μ Prod.snd := by
  funext y
  unfold secondMarginal pushforwardMass
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hzy
    simp [hzy]
  · simp

theorem joint_eq_firstMarginal_mul_conditionalSecond
    {α β : Type*} [Fintype β]
    {μ : α × β → ℝ} (hμ : ∀ z, 0 ≤ μ z) (x : α) (y : β) :
    μ (x, y) = firstMarginal μ x * conditionalSecond μ x y := by
  by_cases hx : firstMarginal μ x = 0
  · have hxy : μ (x, y) = 0 := by
      have hle : μ (x, y) ≤ firstMarginal μ x := by
        rw [firstMarginal]
        exact Finset.single_le_sum (fun z _ ↦ hμ (x, z)) (Finset.mem_univ y)
      exact le_antisymm (hle.trans_eq hx) (hμ (x, y))
    simp [conditionalSecond, hx, hxy]
  · rw [conditionalSecond]
    field_simp

theorem sum_conditionalSecond
    {α β : Type*} [Fintype β]
    {μ : α × β → ℝ} {x : α} (hx : firstMarginal μ x ≠ 0) :
    ∑ y, conditionalSecond μ x y = 1 := by
  change (∑ y, μ (x, y) / firstMarginal μ x) = 1
  rw [← Finset.sum_div]
  change firstMarginal μ x / firstMarginal μ x = 1
  exact div_self hx

theorem weighted_conditionalSecond_sum
    {α β : Type*} [Fintype α] [Fintype β]
    {μ : α × β → ℝ} (hμ : ∀ z, 0 ≤ μ z) (y : β) :
    ∑ x, firstMarginal μ x * conditionalSecond μ x y =
      secondMarginal μ y := by
  simp_rw [← joint_eq_firstMarginal_mul_conditionalSecond hμ]
  rfl

theorem conditionalSecond_nonnegative
    {α β : Type*} [Fintype β]
    {μ : α × β → ℝ} (hμ : ∀ z, 0 ≤ μ z) (x : α) (y : β) :
    0 ≤ conditionalSecond μ x y := by
  exact div_nonneg (hμ (x, y))
    (Finset.sum_nonneg fun z _ ↦ hμ (x, z))

/-- Chain-rule decomposition of the entropy of a finite pair.  The
conditional term is written with the zero-fiber convention used by
`conditionalSecond`. -/
theorem jointEntropy_eq_first_add_conditional
    {α β : Type*} [Fintype α] [Fintype β]
    {μ : α × β → ℝ} (hμ : IsProbabilityVector μ) :
    shannonEntropy μ =
      shannonEntropy (firstMarginal μ) +
        ∑ x, firstMarginal μ x * shannonEntropy (conditionalSecond μ x) := by
  rw [shannonEntropy, Fintype.sum_prod_type]
  calc
    (∑ x, ∑ y, Real.negMulLog (μ (x, y))) =
        ∑ x, (Real.negMulLog (firstMarginal μ x) +
          firstMarginal μ x * shannonEntropy (conditionalSecond μ x)) := by
      apply Finset.sum_congr rfl
      intro x _
      have hfactor : ∀ y, μ (x, y) =
          firstMarginal μ x * conditionalSecond μ x y :=
        joint_eq_firstMarginal_mul_conditionalSecond hμ.nonnegative x
      calc
        (∑ y, Real.negMulLog (μ (x, y))) =
            ∑ y, Real.negMulLog
              (firstMarginal μ x * conditionalSecond μ x y) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hfactor y]
        _ = ∑ y, (conditionalSecond μ x y *
              Real.negMulLog (firstMarginal μ x) +
            firstMarginal μ x * Real.negMulLog (conditionalSecond μ x y)) := by
          apply Finset.sum_congr rfl
          intro y _
          exact Real.negMulLog_mul _ _
        _ = (∑ y, conditionalSecond μ x y) *
              Real.negMulLog (firstMarginal μ x) +
            firstMarginal μ x *
              ∑ y, Real.negMulLog (conditionalSecond μ x y) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
        _ = Real.negMulLog (firstMarginal μ x) +
            firstMarginal μ x * shannonEntropy (conditionalSecond μ x) := by
          by_cases hx : firstMarginal μ x = 0
          · simp [hx, shannonEntropy]
          · rw [sum_conditionalSecond hx, one_mul, shannonEntropy]
    _ = shannonEntropy (firstMarginal μ) +
        ∑ x, firstMarginal μ x * shannonEntropy (conditionalSecond μ x) := by
      rw [Finset.sum_add_distrib, shannonEntropy]

/-- Concavity of `-x log x` bounds the averaged conditional entropy by the
entropy of the second marginal. -/
theorem conditionalEntropy_le_secondMarginalEntropy
    {α β : Type*} [Fintype α] [Fintype β]
    {μ : α × β → ℝ} (hμ : IsProbabilityVector μ) :
    (∑ x, firstMarginal μ x * shannonEntropy (conditionalSecond μ x)) ≤
      shannonEntropy (secondMarginal μ) := by
  simp_rw [shannonEntropy, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro y _
  have hfirst := firstMarginal_isProbabilityVector hμ
  have hJ := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := firstMarginal μ)
    (p := fun x ↦ conditionalSecond μ x y)
    (fun x _ ↦ hfirst.nonnegative x) hfirst.sum_eq_one
    (fun x _ ↦ conditionalSecond_nonnegative hμ.nonnegative x y)
  simpa only [smul_eq_mul, weighted_conditionalSecond_sum hμ.nonnegative y] using hJ

/-- Subadditivity of Shannon entropy for a finite pair. -/
theorem jointEntropy_le_sum_marginals
    {α β : Type*} [Fintype α] [Fintype β]
    {μ : α × β → ℝ} (hμ : IsProbabilityVector μ) :
    shannonEntropy μ ≤
      shannonEntropy (firstMarginal μ) +
        shannonEntropy (secondMarginal μ) := by
  rw [jointEntropy_eq_first_add_conditional hμ]
  linarith [conditionalEntropy_le_secondMarginalEntropy hμ]

/-- Subadditivity for a finite vector, in exactly the form used to pass from
the entropy of the paper's joint core encoding to the sum of its rowwise
entropies. -/
theorem functionEntropy_le_sum_coordinateEntropies
    {β : Type*} [Fintype β] [DecidableEq β] :
    ∀ {n : ℕ} {μ : (Fin n → β) → ℝ}, IsProbabilityVector μ →
      shannonEntropy μ ≤
        ∑ i, shannonEntropy (pushforwardMass μ fun y ↦ y i) := by
  intro n
  induction n with
  | zero =>
      intro μ hμ
      have hupper := shannonEntropy_le_log_card hμ
      simpa using hupper
  | succ n ih =>
      intro μ hμ
      let e : (Fin (n + 1) → β) ≃ β × (Fin n → β) :=
        (Fin.consEquiv (fun _ : Fin (n + 1) ↦ β)).symm
      let μ' : (β × (Fin n → β)) → ℝ := pushforwardMass μ e
      have hμ' : IsProbabilityVector μ' :=
        pushforwardMass_isProbabilityVector μ hμ e
      have hpair := jointEntropy_le_sum_marginals hμ'
      have htailProb : IsProbabilityVector (secondMarginal μ') :=
        secondMarginal_isProbabilityVector hμ'
      have htail := ih htailProb
      have hhead : firstMarginal μ' =
          pushforwardMass μ (fun y ↦ y 0) := by
        rw [firstMarginal_eq_pushforward_fst]
        funext y
        rw [pushforwardMass_comp]
        congr 1
      have htailDist : secondMarginal μ' =
          pushforwardMass μ (fun y ↦ Fin.tail y) := by
        rw [secondMarginal_eq_pushforward_snd]
        funext y
        rw [pushforwardMass_comp]
        congr 1
      have hcoord (i : Fin n) :
          pushforwardMass (secondMarginal μ') (fun y ↦ y i) =
            pushforwardMass μ (fun y ↦ y i.succ) := by
        rw [htailDist]
        funext y
        rw [pushforwardMass_comp]
        congr 1
      calc
        shannonEntropy μ = shannonEntropy μ' := by
          exact (shannonEntropy_pushforward_equiv μ e).symm
        _ ≤ shannonEntropy (firstMarginal μ') +
            shannonEntropy (secondMarginal μ') := hpair
        _ ≤ shannonEntropy (pushforwardMass μ fun y ↦ y 0) +
            ∑ i, shannonEntropy
              (pushforwardMass (secondMarginal μ') fun y ↦ y i) := by
          rw [hhead]
          linarith
        _ = ∑ i, shannonEntropy (pushforwardMass μ fun y ↦ y i) := by
          simp_rw [hcoord]
          rw [Fin.sum_univ_succ]

theorem entropy_on_finset_of_mass_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) {μ : α → ℝ} {ρ : ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hρ : 0 < ρ)
    (hsum : ∑ x ∈ s, μ x = ρ) :
    (∑ x ∈ s, Real.negMulLog (μ x)) ≤
      ρ * Real.log ((s.card : ℝ) / ρ) := by
  let q : s → ℝ := fun x ↦ μ x
  letI : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  have hqsum : ∑ x, q x = ρ := by
    calc
      ∑ x, q x = ∑ x ∈ s.attach, μ x := by rfl
      _ = ∑ x ∈ s, μ x := Finset.sum_attach s μ
      _ = ρ := hsum
  have hbound := shannonEntropy_of_mass_le
    (α := q) (ρ := ρ) (fun x ↦ hμ x) hρ hqsum
  have hcard : Fintype.card s = s.card := Fintype.card_coe s
  rw [shannonEntropy, hcard] at hbound
  change (∑ x ∈ s.attach, Real.negMulLog (μ x)) ≤ _ at hbound
  rw [← Finset.sum_attach s (fun x ↦ Real.negMulLog (μ x))]
  exact hbound

/-- Entropy within one fiber of a deterministic map is bounded by the fiber
mass times the logarithm of the maximum fiber size. -/
theorem fiber_entropy_bound
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {μ : α → ℝ} (hμ : IsProbabilityVector μ) (f : α → β)
    (K : ℕ) (hK : 1 ≤ K)
    (hfiber : ∀ y, (Finset.univ.filter fun x ↦ f x = y).card ≤ K)
    (y : β) :
    (∑ x ∈ Finset.univ.filter (fun x ↦ f x = y),
        Real.negMulLog (μ x)) ≤
      Real.negMulLog (pushforwardMass μ f y) +
        pushforwardMass μ f y * Real.log K := by
  let s := Finset.univ.filter fun x ↦ f x = y
  change (∑ x ∈ s, Real.negMulLog (μ x)) ≤ _
  have hqnonneg := (pushforwardMass_isProbabilityVector μ hμ f).nonnegative y
  by_cases hqzero : pushforwardMass μ f y = 0
  · have hsumzero : ∑ x ∈ s, μ x = 0 := by
      rw [Finset.sum_filter]
      simpa [s, pushforwardMass] using hqzero
    have htermzero : ∀ x ∈ s, μ x = 0 := by
      exact Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ ↦ hμ.nonnegative x) |>.mp hsumzero
    simp only [hqzero, Real.negMulLog_zero, zero_mul, add_zero]
    exact (Finset.sum_eq_zero (fun x hx ↦ by
      rw [htermzero x hx, Real.negMulLog_zero])).le
  · have hqpos : 0 < pushforwardMass μ f y :=
      lt_of_le_of_ne hqnonneg (Ne.symm hqzero)
    have hs : s.Nonempty := by
      by_contra hempty
      have hzero : ∑ x ∈ s, μ x = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
        simp
      have : pushforwardMass μ f y = 0 := by
        rw [← hzero]
        unfold pushforwardMass
        rw [← Finset.sum_filter]
      exact hqzero this
    have hsum : ∑ x ∈ s, μ x = pushforwardMass μ f y := by
      rw [Finset.sum_filter]
      simp [s, pushforwardMass]
    have hscaled := entropy_on_finset_of_mass_le s hs
      hμ.nonnegative hqpos hsum
    have hcardpos : (0 : ℝ) < s.card := by
      exact_mod_cast hs.card_pos
    have hKpos : (0 : ℝ) < K := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
    have hcardle : (s.card : ℝ) ≤ K := by exact_mod_cast hfiber y
    have hlogle : Real.log (s.card : ℝ) ≤ Real.log K :=
      Real.log_le_log hcardpos hcardle
    have hmul := mul_le_mul_of_nonneg_left hlogle hqpos.le
    rw [Real.log_div hcardpos.ne' hqpos.ne'] at hscaled
    simp only [Real.negMulLog_def]
    have hrewrite :
        pushforwardMass μ f y *
            (Real.log (s.card : ℝ) - Real.log (pushforwardMass μ f y)) =
          -pushforwardMass μ f y * Real.log (pushforwardMass μ f y) +
            pushforwardMass μ f y * Real.log (s.card : ℝ) := by ring
    rw [hrewrite] at hscaled
    exact hscaled.trans (by
      simpa [add_comm] using
        add_le_add_left hmul
          (-pushforwardMass μ f y * Real.log (pushforwardMass μ f y)))

/-- Generic finite-fiber encoding inequality.  This is the entropy-theoretic
part of paper Lemma 9, independent of the cycle combinatorics used to bound
the fibers. -/
theorem entropy_le_pushforward_add_log_fiberBound
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {μ : α → ℝ} (hμ : IsProbabilityVector μ) (f : α → β)
    (K : ℕ) (hK : 1 ≤ K)
    (hfiber : ∀ y, (Finset.univ.filter fun x ↦ f x = y).card ≤ K) :
    shannonEntropy μ ≤
      shannonEntropy (pushforwardMass μ f) + Real.log K := by
  have hpoint := fun y ↦ fiber_entropy_bound hμ f K hK hfiber y
  have hsum :
      (∑ y, ∑ x ∈ Finset.univ.filter (fun x ↦ f x = y),
        Real.negMulLog (μ x)) ≤
      ∑ y, (Real.negMulLog (pushforwardMass μ f y) +
        pushforwardMass μ f y * Real.log K) := by
    exact Finset.sum_le_sum (fun y _ ↦ hpoint y)
  have hpartition : shannonEntropy μ =
      ∑ y, ∑ x ∈ Finset.univ.filter (fun x ↦ f x = y),
        Real.negMulLog (μ x) := by
    rw [shannonEntropy]
    calc
      (∑ x, Real.negMulLog (μ x)) =
          ∑ x, ∑ y, if f x = y then Real.negMulLog (μ x) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        simp
      _ = ∑ y, ∑ x, if f x = y then Real.negMulLog (μ x) else 0 :=
        Finset.sum_comm
      _ = ∑ y, ∑ x ∈ Finset.univ.filter (fun x ↦ f x = y),
          Real.negMulLog (μ x) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.sum_filter]
  have hright :
      (∑ y, (Real.negMulLog (pushforwardMass μ f y) +
        pushforwardMass μ f y * Real.log K)) =
        shannonEntropy (pushforwardMass μ f) + Real.log K := by
    rw [Finset.sum_add_distrib, shannonEntropy, ← Finset.sum_mul,
      (pushforwardMass_isProbabilityVector μ hμ f).sum_eq_one, one_mul]
  rw [hpartition, ← hright]
  exact hsum

/-- Kullback--Leibler divergence on a finite type. -/
noncomputable def finiteKL
    {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)

theorem finiteKL_nonneg
    {ι : Type*} [Fintype ι]
    {p q : ι → ℝ}
    (hp : IsProbabilityVector p) (hq : IsProbabilityVector q)
    (hppos : ∀ i, 0 < p i) (hqpos : ∀ i, 0 < q i) :
    0 ≤ finiteKL p q := by
  have hterm : ∀ i,
      p i * Real.log (q i / p i) ≤ q i - p i := by
    intro i
    have hratio : 0 < q i / p i := div_pos (hqpos i) (hppos i)
    have hlog := Real.log_le_sub_one_of_pos hratio
    have hmul := mul_le_mul_of_nonneg_left hlog (hp.nonnegative i)
    have hsimplify : p i * (q i / p i - 1) = q i - p i := by
      field_simp [(hppos i).ne']
    rw [hsimplify] at hmul
    exact hmul
  have hsum : (∑ i, p i * Real.log (q i / p i)) ≤
      ∑ i, (q i - p i) :=
    Finset.sum_le_sum fun i _ ↦ hterm i
  rw [Finset.sum_sub_distrib, hq.sum_eq_one, hp.sum_eq_one, sub_self] at hsum
  have hrewrite : finiteKL p q = -∑ i, p i * Real.log (q i / p i) := by
    rw [finiteKL, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.log_div (hppos i).ne' (hqpos i).ne',
      Real.log_div (hqpos i).ne' (hppos i).ne']
    ring
  rw [hrewrite]
  linarith

theorem finiteKL_eq_neg_entropy_sub
    {ι : Type*} [Fintype ι]
    {p q : ι → ℝ} (hppos : ∀ i, 0 < p i) (hqpos : ∀ i, 0 < q i) :
    finiteKL p q =
      -shannonEntropy p - ∑ i, p i * Real.log (q i) := by
  rw [finiteKL, shannonEntropy, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.negMulLog_def,
    Real.log_div (hppos i).ne' (hqpos i).ne']
  ring

/-- Uniform average of a real-valued function on a finite type. -/
noncomputable def uniformAverage
    {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ :=
  (∑ i, f i) / Fintype.card ι

/-- Suffix mass seen by coordinate `j` in the ordering `π`.  An ordering is a
permutation whose value at a position is the coordinate occupying it. -/
noncomputable def suffixMass {m : ℕ}
    (p : Fin m → ℝ) (π : Equiv.Perm (Fin m)) (j : Fin m) : ℝ :=
  ∑ k, if π.symm j ≤ π.symm k then p k else 0

theorem le_suffixMass {m : ℕ} {p : Fin m → ℝ}
    (hp : IsProbabilityVector p) (π : Equiv.Perm (Fin m)) (j : Fin m) :
    p j ≤ suffixMass p π j := by
  rw [suffixMass]
  have hterm :
      p j = if π.symm j ≤ π.symm j then p j else 0 := by simp
  rw [hterm]
  exact Finset.single_le_sum
    (f := fun k ↦ if π.symm j ≤ π.symm k then p k else 0)
    (fun k _ ↦ by
      by_cases h : π.symm j ≤ π.symm k
      · simpa [h] using hp.nonnegative k
      · simp [h])
    (Finset.mem_univ j)

theorem suffixMass_le_one {m : ℕ} {p : Fin m → ℝ}
    (hp : IsProbabilityVector p) (π : Equiv.Perm (Fin m)) (j : Fin m) :
    suffixMass p π j ≤ 1 := by
  rw [suffixMass, ← hp.sum_eq_one]
  apply Finset.sum_le_sum
  intro k _
  split_ifs
  · rfl
  · exact hp.nonnegative k

theorem suffixMass_pos {m : ℕ} {p : Fin m → ℝ}
    (hp : IsProbabilityVector p) {j : Fin m} (hj : 0 < p j)
    (π : Equiv.Perm (Fin m)) :
    0 < suffixMass p π j :=
  hj.trans_le (le_suffixMass hp π j)

/-- The averaged suffix score `T(p)` from paper (13). -/
noncomputable def rowT {m : ℕ} (p : Fin m → ℝ) : ℝ :=
  uniformAverage fun π : Equiv.Perm (Fin m) ↦
    ∑ j, p j * Real.log (suffixMass p π j)

/-- The one-row correction `g(p)` from paper (14). -/
noncomputable def rowCorrection {m : ℕ} (p : Fin m → ℝ) : ℝ :=
  rowT p - ∑ j, (1 - p j) * Real.log (1 - p j)

/-- Deficit from the sharp one-row inequality, paper (15). -/
noncomputable def rowDeficit {m : ℕ} (p : Fin m → ℝ) : ℝ :=
  Real.log 2 / 2 - rowCorrection p

/-- Exact source-level interface for the sharp one-row theorem of
Anari--Rezaei.  It is a proposition passed as an argument, not a Lean axiom. -/
def AnariRezaeiRowInequality : Prop :=
  ∀ {m : ℕ}, 2 ≤ m → ∀ p : Fin m → ℝ,
    IsProbabilityVector p → 0 ≤ rowDeficit p

end BeyondBethe
