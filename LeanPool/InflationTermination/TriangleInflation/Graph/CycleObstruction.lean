/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/
module


public import LeanPool.InflationTermination.TriangleInflation.Graph.Cycles
public import LeanPool.InflationTermination.TriangleInflation.Graph.CycleWitness

/-!
# Cycle witnesses at every order, incompatibility and distance

AUDIT-NOTES A5 / Theorem `thm:cycle`: the parity witness `cycle_witness` (from
`CycleWitness.lean`), the incompatibility of the cycle target (`cycle_not_compatible`) and
the distance bound `q/10 ≤ d_TV` (`cycle_distance`), the last two through the quantitative
parity rigidity `CycleModelAux.quant_rigidity` (Lemma `lem:quantrigidity`). Everything here
is proved.
-/

@[expose] public section

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

/-- AUDIT-NOTES A5, the cycle witness. With `N = mt` auxiliary signs `s_{v,i}` carrying the
positive density `H_{N,q}(s) = 2^{−N} ∑_{|S| even} (−q)^{|S|/2} ∏_S s`, and copied
observations `O_v^{ij} = s_{v−1,i} s_{v,j}`, the target `P_{m,q}` with moments
`(−q)^{|∂F|/2}` passes every AI prescription at order `t`, for `q = 1/(4m²t²)`: the
boundaries of ancestrally disjoint injectable blocks are disjoint, so their moments
multiply. -/
theorem cycle_witness (m t : ℕ) (hm : 3 ≤ m) (ht : 1 ≤ t) (q : ℝ)
    (hq : q = 1 / (4 * (m : ℝ) ^ 2 * (t : ℝ) ^ 2)) :
    GAIFeasible (cycle m hm) t (cycleTarget m q) :=
  cycle_witness' m t hm ht q hq

/-- The same witness passes the recursively expressible test, by AUDIT-NOTES A2. -/
theorem cycle_exp_witness (m t : ℕ) (hm : 3 ≤ m) (ht : 1 ≤ t) (q : ℝ)
    (hq : q = 1 / (4 * (m : ℝ) ^ 2 * (t : ℝ) ^ 2)) :
    GExpFeasible (cycle m hm) t (cycleTarget m q) :=
  (gExpFeasible_iff_gAIFeasible (cycle m hm) t (cycleTarget m q)).2
    (cycle_witness m t hm ht q hq)

/-! ## Auxiliary material for the cycle arcs

Nothing in this namespace changes the two statements below, which appear in their original
form. -/

namespace CycleModelAux



section Av
variable {X : Type*} [Fintype X] {μ f g : X → ℝ}

/-- Weighted average of a function over a finite latent alphabet. -/
def av {X : Type*} [Fintype X] (μ f : X → ℝ) : ℝ := ∑ x, μ x * f x

theorem av_mono (hμ : ∀ x, 0 ≤ μ x) (h : ∀ x, f x ≤ g x) : av μ f ≤ av μ g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hμ x)

theorem av_const (hμ : IsLaw μ) (k : ℝ) : av μ (fun _ => k) = k := by
  simp only [av, ← Finset.sum_mul, hμ.2, one_mul]

theorem av_sub (μ f g : X → ℝ) : av μ (fun x => f x - g x) = av μ f - av μ g := by
  simp only [av, mul_sub, Finset.sum_sub_distrib]

theorem av_add (μ f g : X → ℝ) : av μ (fun x => f x + g x) = av μ f + av μ g := by
  simp only [av, mul_add, Finset.sum_add_distrib]

theorem av_abs_le (hμ : ∀ x, 0 ≤ μ x) (f : X → ℝ) : |av μ f| ≤ av μ (fun x => |f x|) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul, abs_of_nonneg (hμ x)]

theorem abs_av_le (hμ : IsLaw μ) {f : X → ℝ} {k : ℝ} (h : ∀ x, |f x| ≤ k) : |av μ f| ≤ k := by
  refine le_trans (av_abs_le hμ.1 f) ?_
  calc av μ (fun x => |f x|) ≤ av μ (fun _ => k) := av_mono hμ.1 h
    _ = k := av_const hμ k

theorem av_mul_left (μ f : X → ℝ) (k : ℝ) : av μ (fun x => k * f x) = k * av μ f := by
  simp only [av, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem av_mul_av {Y : Type*} [Fintype Y] (μ : X → ℝ) (ν : Y → ℝ) (F : X → ℝ) (G : Y → ℝ) :
    av μ F * av ν G = av μ (fun x => av ν (fun y => F x * G y)) := by
  simp only [av]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem av_nonneg (hμ : ∀ x, 0 ≤ μ x) (h : ∀ x, 0 ≤ f x) : 0 ≤ av μ f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (h x)

theorem av_one_sub (hμ : IsLaw μ) (f : X → ℝ) : av μ (fun x => 1 - f x) = 1 - av μ f := by
  rw [av_sub μ (fun _ => 1) f, av_const hμ]

theorem exists_le_of_av (hμ : IsLaw μ) {c : ℝ} (hf : av μ f = c) :
    ∃ x, 0 < μ x ∧ f x ≤ c := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x0, hx0⟩ := exists_pos_of_isLaw μ hμ
  have hlt : (∑ x, μ x * c) < ∑ x, μ x * f x := by
    refine Finset.sum_lt_sum (fun x _ => ?_) ⟨x0, Finset.mem_univ _, ?_⟩
    · rcases eq_or_lt_of_le (hμ.1 x) with h | h
      · rw [← h]; simp
      · exact le_of_lt (mul_lt_mul_of_pos_left (hcon x h) h)
    · exact mul_lt_mul_of_pos_left (hcon x0 hx0) hx0
  rw [← Finset.sum_mul, hμ.2, one_mul] at hlt
  rw [av] at hf
  linarith

end Av

section Av2
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

theorem av2_sub (μ : A → ℝ) (ν : B → ℝ) (f g : A → B → ℝ) :
    av μ (fun p => av ν (fun q => f p q)) - av μ (fun p => av ν (fun q => g p q))
      = av μ (fun p => av ν (fun q => f p q - g p q)) := by
  rw [← av_sub]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact congrArg _ (av_sub ν (fun q => f p q) (fun q => g p q)).symm

theorem abs_av2_le_av2 {μ : A → ℝ} {ν : B → ℝ} (hμ : ∀ p, 0 ≤ μ p) (hν : ∀ q, 0 ≤ ν q)
    (f : A → B → ℝ) :
    |av μ (fun p => av ν (fun q => f p q))| ≤ av μ (fun p => av ν (fun q => |f p q|)) :=
  le_trans (av_abs_le hμ _) (av_mono hμ fun _ => av_abs_le hν _)

theorem abs_av3_le_av3 {μ : A → ℝ} {ν : B → ℝ} {ρ : C → ℝ} (hμ : ∀ p, 0 ≤ μ p)
    (hν : ∀ q, 0 ≤ ν q) (hρ : ∀ s, 0 ≤ ρ s) (f : A → B → C → ℝ) :
    |av μ (fun p => av ν (fun q => av ρ (fun s => f p q s)))|
      ≤ av μ (fun p => av ν (fun q => av ρ (fun s => |f p q s|))) :=
  le_trans (av_abs_le hμ _) (av_mono hμ fun _ => abs_av2_le_av2 hν hρ _)

theorem av3_sub (μ : A → ℝ) (ν : B → ℝ) (ρ : C → ℝ) (f g : A → B → C → ℝ) :
    av μ (fun p => av ν (fun q => av ρ (fun s => f p q s)))
      - av μ (fun p => av ν (fun q => av ρ (fun s => g p q s)))
      = av μ (fun p => av ν (fun q => av ρ (fun s => f p q s - g p q s))) := by
  rw [← av_sub]
  refine Finset.sum_congr rfl fun p _ => ?_
  dsimp only
  exact congrArg _ (av2_sub ν ρ (fun q s => f p q s) (fun q s => g p q s))

theorem av3_const_inner (μ : A → ℝ) (ν : B → ℝ) {ρ : C → ℝ} (hρ : IsLaw ρ) (f : A → B → ℝ) :
    av μ (fun p => av ν (fun q => av ρ (fun _ => f p q)))
      = av μ (fun p => av ν (fun q => f p q)) := by
  refine Finset.sum_congr rfl fun p _ => ?_
  refine congrArg _ (Finset.sum_congr rfl fun q _ => ?_)
  exact congrArg _ (av_const hρ (f p q))

end Av2

theorem abs_sub_le_one_sub_mul {p r : ℝ} (hp : |p| ≤ 1) (hr : |r| ≤ 1) :
    |p - r| ≤ 1 - p * r := by
  rw [abs_le] at hp hr
  rw [abs_le]
  constructor <;> nlinarith [hp.1, hp.2, hr.1, hr.2]

theorem two_mul_le_abs_add {u w : ℝ} (hu : |u| ≤ 1) (hw : |w| ≤ 1) :
    2 * (u * w) ≤ |u + w| := by
  rw [abs_le] at hu hw
  rcases le_or_gt (u * w) 0 with h1 | h1
  · linarith [abs_nonneg (u + w)]
  · rcases le_or_gt 0 u with h2 | h2
    · have hw0 : 0 < w := by nlinarith
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u + w)]
      nlinarith [mul_nonneg h2 (sub_nonneg.2 hw.2), mul_nonneg hw0.le (sub_nonneg.2 hu.2)]
    · have hw0 : w < 0 := by nlinarith
      rw [abs_of_nonpos (by linarith : u + w ≤ (0:ℝ))]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -u) (by linarith : (0:ℝ) ≤ 1 + w),
        mul_nonneg (by linarith : (0:ℝ) ≤ -w) (by linarith : (0:ℝ) ≤ 1 + u)]

theorem abs_mul2_le_one {p q : ℝ} (hp : |p| ≤ 1) (hq : |q| ≤ 1) : |p * q| ≤ 1 := by
  rw [abs_mul]
  calc |p| * |q| ≤ 1 * 1 := mul_le_mul hp hq (abs_nonneg q) zero_le_one
    _ = 1 := by norm_num

theorem abs_mul3_le_one {p q s : ℝ} (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hs : |s| ≤ 1) :
    |p * q * s| ≤ 1 := abs_mul2_le_one (abs_mul2_le_one hp hq) hs

theorem av2_one_sub {A B : Type*} [Fintype A] [Fintype B] {μ : A → ℝ} {ν : B → ℝ}
    (hμ : IsLaw μ) (hν : IsLaw ν) (f : A → B → ℝ) :
    av μ (fun p => av ν (fun q => 1 - f p q))
      = 1 - av μ (fun p => av ν (fun q => f p q)) := by
  rw [← av_one_sub hμ (fun p => av ν (fun q => f p q))]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact congrArg _ (av_one_sub hν (fun q => f p q))

theorem av3_one_sub {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    {μ : A → ℝ} {ν : B → ℝ} {ρ : C → ℝ} (hμ : IsLaw μ) (hν : IsLaw ν) (hρ : IsLaw ρ)
    (f : A → B → C → ℝ) :
    av μ (fun p => av ν (fun q => av ρ (fun s => 1 - f p q s)))
      = 1 - av μ (fun p => av ν (fun q => av ρ (fun s => f p q s))) := by
  rw [← av_one_sub hμ (fun p => av ν (fun q => av ρ (fun s => f p q s)))]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact congrArg _ (av2_one_sub hν hρ (fun q s => f p q s))

section Rigidity
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- **Quantitative parity rigidity for the triangle pattern.** -/
theorem quant_rigidity (μX : X → ℝ) (μY : Y → ℝ) (μZ : Z → ℝ)
    (hX : IsLaw μX) (hY : IsLaw μY) (hZ : IsLaw μZ)
    (a : X → Z → ℝ) (b : X → Y → ℝ) (c : Z → Y → ℝ)
    (ha : ∀ x z, |a x z| ≤ 1) (hb : ∀ x y, |b x y| ≤ 1) (hc : ∀ z y, |c z y| ≤ 1)
    (r : ℝ)
    (hAr : av μX (fun x => av μZ (fun z => a x z)) ≤ r)
    (hBr : av μY (fun y => av μX (fun x => b x y)) ≤ r)
    (hCr : av μY (fun y => av μZ (fun z => c z y)) ≤ r) :
    -4 * (1 - av μY (fun y => av μX (fun x => av μZ (fun z => a x z * b x y * c z y)))) ≤ r := by
  classical
  by_contra hcon
  push Not at hcon
  set W := av μY (fun y => av μX (fun x => av μZ (fun z => a x z * b x y * c z y))) with hWdef
  have habc : ∀ x y z, |a x z * b x y * c z y| ≤ 1 :=
    fun x y z => abs_mul3_le_one (ha x z) (hb x y) (hc z y)
  have hW1 : W ≤ 1 := by
    have hW : |W| ≤ 1 := by
      rw [hWdef]
      exact abs_av_le hY fun y => abs_av_le hX fun x => abs_av_le hZ fun z => habc x y z
    exact (abs_le.1 hW).2
  set ε := 1 - W with hεdef
  have hε0 : (0:ℝ) ≤ ε := by rw [hεdef]; linarith
  -- Step 1: a good value of the third source
  have hDav : av μY (fun y => av μX (fun x => av μZ (fun z => 1 - a x z * b x y * c z y))) = ε := by
    rw [av3_one_sub hY hX hZ, ← hWdef, hεdef]
  obtain ⟨y₀, -, hy₀⟩ := exists_le_of_av hY hDav
  -- Step 2: the pair (b(·,y₀), c(·,y₀)) approximates a
  have hbc1 : ∀ x z, |b x y₀ * c z y₀| ≤ 1 :=
    fun x z => abs_mul2_le_one (hb x y₀) (hc z y₀)
  set D := av μX (fun x => av μZ (fun z => |a x z - b x y₀ * c z y₀|)) with hDdef
  have hDle : D ≤ ε := by
    refine le_trans (av_mono hX.1 fun x => av_mono hZ.1 fun z => ?_) hy₀
    rw [mul_assoc]
    exact abs_sub_le_one_sub_mul (ha x z) (hbc1 x z)
  have hD0 : (0:ℝ) ≤ D := av_nonneg hX.1 fun x => av_nonneg hZ.1 fun z => abs_nonneg _
  set σ := av μX (fun x => b x y₀) with hσdef
  set τ := av μZ (fun z => c z y₀) with hτdef
  have hAστ : |av μX (fun x => av μZ (fun z => a x z)) - σ * τ| ≤ D := by
    have e1 : σ * τ = av μX (fun x => av μZ (fun z => b x y₀ * c z y₀)) :=
      av_mul_av μX μZ (fun x => b x y₀) (fun z => c z y₀)
    rw [e1, av2_sub μX μZ (fun x z => a x z) (fun x z => b x y₀ * c z y₀), hDdef]
    exact abs_av2_le_av2 hX.1 hZ.1 _
  -- Step 3: the conditional means
  set u : Y → ℝ := fun y => av μX (fun x => b x y₀ * b x y) with hudef
  set w : Y → ℝ := fun y => av μZ (fun z => c z y₀ * c z y) with hwdef
  have hu1 : ∀ y, |u y| ≤ 1 :=
    fun y => abs_av_le hX fun x => abs_mul2_le_one (hb x y₀) (hb x y)
  have hw1 : ∀ y, |w y| ≤ 1 :=
    fun y => abs_av_le hZ fun z => abs_mul2_le_one (hc z y₀) (hc z y)
  have huw : W - D ≤ av μY (fun y => u y * w y) := by
    have e2 : av μY (fun y => u y * w y)
        = av μY (fun y => av μX (fun x =>
            av μZ (fun z => b x y₀ * b x y * (c z y₀ * c z y)))) :=
      Finset.sum_congr rfl fun y _ =>
        congrArg _ (av_mul_av μX μZ (fun x => b x y₀ * b x y) (fun z => c z y₀ * c z y))
    have e3 : W - av μY (fun y => av μX (fun x =>
            av μZ (fun z => b x y₀ * b x y * (c z y₀ * c z y))))
        = av μY (fun y => av μX (fun x => av μZ (fun z =>
            a x z * b x y * c z y - b x y₀ * b x y * (c z y₀ * c z y)))) := by
      rw [hWdef]
      exact av3_sub μY μX μZ _ _
    have e4 : |av μY (fun y => av μX (fun x => av μZ (fun z =>
            a x z * b x y * c z y - b x y₀ * b x y * (c z y₀ * c z y))))| ≤ D := by
      refine le_trans (abs_av3_le_av3 hY.1 hX.1 hZ.1 _) ?_
      have hstep : av μY (fun y => av μX (fun x => av μZ (fun z =>
            |a x z * b x y * c z y - b x y₀ * b x y * (c z y₀ * c z y)|)))
          ≤ av μY (fun _ => av μX (fun x => av μZ (fun z => |a x z - b x y₀ * c z y₀|))) := by
        refine av_mono hY.1 fun y => av_mono hX.1 fun x => av_mono hZ.1 fun z => ?_
        have hid : a x z * b x y * c z y - b x y₀ * b x y * (c z y₀ * c z y)
            = (a x z - b x y₀ * c z y₀) * (b x y * c z y) := by ring
        have h1 : |b x y * c z y| ≤ 1 := abs_mul2_le_one (hb x y) (hc z y)
        rw [hid, abs_mul]
        nlinarith [abs_nonneg (a x z - b x y₀ * c z y₀), abs_nonneg (b x y * c z y)]
      refine le_trans hstep ?_
      rw [hDdef]
      exact le_of_eq (av_const hY _)
    rw [e2]
    have := (abs_le.1 e4).2
    linarith [e3]
  -- Step 4: rounding the conditional means
  set υ : Y → ℝ := fun y => if 0 ≤ u y + w y then (1:ℝ) else -1 with hυdef
  have hυabs : ∀ y, |υ y| = 1 := by
    intro y
    rw [hυdef]
    by_cases h : 0 ≤ u y + w y <;> simp [h]
  have hυmul : ∀ y, υ y * (u y + w y) = |u y + w y| := by
    intro y
    rw [hυdef]
    dsimp only
    by_cases h : 0 ≤ u y + w y
    · simp only [ite_eq_left h, one_mul, abs_of_nonneg h]
    · rw [ite_eq_right h, abs_of_neg (not_le.1 h)]; ring
  have hnn1 : ∀ y, 0 ≤ 1 - υ y * u y := by
    intro y
    have h1 := abs_le.1 (hu1 y)
    rw [hυdef]
    dsimp only
    by_cases h : 0 ≤ u y + w y
    · simp only [ite_eq_left h, one_mul]; linarith [h1.2]
    · rw [ite_eq_right h]; nlinarith [h1.1]
  have hnn2 : ∀ y, 0 ≤ 1 - υ y * w y := by
    intro y
    have h1 := abs_le.1 (hw1 y)
    rw [hυdef]
    dsimp only
    by_cases h : 0 ≤ u y + w y
    · simp only [ite_eq_left h, one_mul]; linarith [h1.2]
    · rw [ite_eq_right h]; nlinarith [h1.1]
  have hsum : av μY (fun y => (1 - υ y * u y) + (1 - υ y * w y)) ≤ 2 * ε + 2 * D := by
    have e1 : ∀ y, (1 - υ y * u y) + (1 - υ y * w y) ≤ 2 - 2 * (u y * w y) := by
      intro y
      have h := two_mul_le_abs_add (hu1 y) (hw1 y)
      have h2 := hυmul y
      nlinarith [h, h2]
    refine le_trans (av_mono hY.1 e1) ?_
    have e2 : av μY (fun y => 2 - 2 * (u y * w y)) = 2 - 2 * av μY (fun y => u y * w y) := by
      rw [av_sub μY (fun _ => (2:ℝ)) (fun y => 2 * (u y * w y)), av_const hY,
        av_mul_left μY (fun y => u y * w y) 2]
    rw [e2, hεdef]
    linarith [huw]
  have hbu : av μY (fun y => 1 - υ y * u y) ≤ 2 * ε + 2 * D := by
    have h2 := av_nonneg hY.1 hnn2
    have e := av_add μY (fun y => 1 - υ y * u y) (fun y => 1 - υ y * w y)
    linarith [hsum, e]
  have hbw : av μY (fun y => 1 - υ y * w y) ≤ 2 * ε + 2 * D := by
    have h2 := av_nonneg hY.1 hnn1
    have e := av_add μY (fun y => 1 - υ y * u y) (fun y => 1 - υ y * w y)
    linarith [hsum, e]
  set vb := av μY υ with hvbdef
  -- Step 5 and 6: the other two means
  have hBσ : |av μY (fun y => av μX (fun x => b x y)) - σ * vb|
      ≤ av μY (fun y => 1 - υ y * u y) := by
    have e1 : σ * vb = av μY (fun y => av μX (fun x => υ y * b x y₀)) := by
      rw [mul_comm]
      exact av_mul_av μY μX υ (fun x => b x y₀)
    rw [e1, av2_sub μY μX (fun y x => b x y) (fun y x => υ y * b x y₀)]
    refine le_trans (abs_av2_le_av2 hY.1 hX.1 _) ?_
    refine av_mono hY.1 fun y => ?_
    have step : ∀ x, |b x y - υ y * b x y₀| ≤ 1 - b x y * (υ y * b x y₀) := by
      intro x
      refine abs_sub_le_one_sub_mul (hb x y) ?_
      rw [abs_mul, hυabs y, one_mul]
      exact hb x y₀
    refine le_trans (av_mono hX.1 step) ?_
    refine le_of_eq ?_
    rw [av_one_sub hX (fun x => b x y * (υ y * b x y₀))]
    congr 1
    rw [hudef, ← av_mul_left μX (fun x => b x y₀ * b x y) (υ y)]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hCτ : |av μY (fun y => av μZ (fun z => c z y)) - τ * vb|
      ≤ av μY (fun y => 1 - υ y * w y) := by
    have e1 : τ * vb = av μY (fun y => av μZ (fun z => υ y * c z y₀)) := by
      rw [mul_comm]
      exact av_mul_av μY μZ υ (fun z => c z y₀)
    rw [e1, av2_sub μY μZ (fun y z => c z y) (fun y z => υ y * c z y₀)]
    refine le_trans (abs_av2_le_av2 hY.1 hZ.1 _) ?_
    refine av_mono hY.1 fun y => ?_
    have step : ∀ z, |c z y - υ y * c z y₀| ≤ 1 - c z y * (υ y * c z y₀) := by
      intro z
      refine abs_sub_le_one_sub_mul (hc z y) ?_
      rw [abs_mul, hυabs y, one_mul]
      exact hc z y₀
    refine le_trans (av_mono hZ.1 step) ?_
    refine le_of_eq ?_
    rw [av_one_sub hZ (fun z => c z y * (υ y * c z y₀))]
    congr 1
    rw [hwdef, ← av_mul_left μZ (fun z => c z y₀ * c z y) (υ y)]
    exact Finset.sum_congr rfl fun z _ => by ring
  -- Step 7: the sign obstruction
  have k1 : σ * τ < 0 := by
    have h := (abs_le.1 hAστ).1
    linarith
  have k2 : σ * vb < 0 := by
    have h := (abs_le.1 hBσ).1
    linarith
  have k3 : τ * vb < 0 := by
    have h := (abs_le.1 hCτ).1
    linarith
  have hpos : 0 < σ * τ * (σ * vb) := mul_pos_of_neg_of_neg k1 k2
  have hneg : σ * τ * (σ * vb) * (τ * vb) < 0 := mul_neg_of_pos_of_neg hpos k3
  have hsq : σ * τ * (σ * vb) * (τ * vb) = (σ * τ * vb) ^ 2 := by ring
  rw [hsq] at hneg
  exact absurd hneg (not_lt.2 (sq_nonneg _))

end Rigidity



theorem sum_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] (g : ∀ i, β i → ℝ) :
    (∑ x : (∀ i, β i), ∏ i, g i (x i)) = ∏ i, ∑ s : β i, g i s := by
  have h := Finset.prod_univ_sum (fun i => (Finset.univ : Finset (β i))) g
  rw [Fintype.piFinset_univ] at h
  exact h.symm


/-- The sign response of a model at a vertex: `E[sgn O_v | sources]`. -/
def sResp (M : GModel Γ) (v : Γ.V) (x : ∀ e : Γ.Edge, M.L e) : ℝ :=
  2 * M.resp v (fun e => x e.1) - 1

theorem sResp_congr (M : GModel Γ) (v : Γ.V) {x x' : ∀ e : Γ.Edge, M.L e}
    (h : ∀ e ∈ Γ.inc v, x e = x' e) : sResp M v x = sResp M v x' := by
  have hf : (fun e : Γ.inc v => x e.1) = (fun e : Γ.inc v => x' e.1) :=
    funext fun e => h e.1 e.2
  simp only [sResp, hf]

theorem sResp_bound (M : GModel Γ) (hM : M.Valid) (v : Γ.V) (x : ∀ e : Γ.Edge, M.L e) :
    -1 ≤ sResp M v x ∧ sResp M v x ≤ 1 := by
  obtain ⟨h1, h2⟩ := hM.2 v (fun e => x e.1)
  exact ⟨by simp only [sResp]; linarith, by simp only [sResp]; linarith⟩

/-- The latent measure of a model. -/
def lat (M : GModel Γ) (x : ∀ e : Γ.Edge, M.L e) : ℝ := ∏ e, M.μ e (x e)

theorem lat_nonneg (M : GModel Γ) (hM : M.Valid) (x : ∀ e : Γ.Edge, M.L e) : 0 ≤ lat M x :=
  Finset.prod_nonneg fun e _ => (hM.1 e).1 _

theorem lat_sum (M : GModel Γ) (hM : M.Valid) : (∑ x : (∀ e : Γ.Edge, M.L e), lat M x) = 1 := by
  simp only [lat]
  rw [sum_pi_prod (fun e => M.μ e)]
  exact Finset.prod_eq_one fun e _ => (hM.1 e).2

theorem lat_isLaw (M : GModel Γ) (hM : M.Valid) : IsLaw (lat M) :=
  ⟨lat_nonneg M hM, lat_sum M hM⟩

/-- The Walsh moments of the observed law of a model. -/
theorem moment_eq (M : GModel Γ) (F : Finset Γ.V) :
    (∑ w : Γ.V → Bool, M.law w * ∏ v ∈ F, sgn (w v))
      = ∑ x : (∀ e : Γ.Edge, M.L e), lat M x * ∏ v ∈ F, sResp M v x := by
  have key : ∀ x : (∀ e : Γ.Edge, M.L e),
      (∑ w : Γ.V → Bool,
          (∏ v : Γ.V, respMass (M.resp v (fun e => x e.1)) (w v)) * ∏ v ∈ F, sgn (w v))
        = ∏ v ∈ F, sResp M v x := by
    intro x
    have e1 : ∀ w : Γ.V → Bool,
        (∏ v : Γ.V, respMass (M.resp v (fun e => x e.1)) (w v)) * ∏ v ∈ F, sgn (w v)
          = ∏ v : Γ.V, ((if v ∈ F then sgn (w v) else 1) *
              respMass (M.resp v (fun e => x e.1)) (w v)) := by
      intro w
      rw [Finset.prod_mul_distrib, prod_sgn_eq_prod_univ F w]
      ring
    simp only [e1]
    rw [sum_pi_prod (β := fun _ : Γ.V => Bool)
      (fun v β => (if v ∈ F then sgn β else 1) * respMass (M.resp v (fun e => x e.1)) β)]
    have e2 : ∀ v : Γ.V,
        (∑ β : Bool, (if v ∈ F then sgn β else 1) * respMass (M.resp v (fun e => x e.1)) β)
          = if v ∈ F then sResp M v x else 1 := by
      intro v
      by_cases h : v ∈ F <;> (simp [h, respMass, sgn, sResp]; try ring)
    simp only [e2]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  simp only [GModel.law, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have : ∀ w : Γ.V → Bool,
      (lat M x * ∏ v : Γ.V, respMass (M.resp v (fun e => x e.1)) (w v)) * ∏ v ∈ F, sgn (w v)
        = lat M x * ((∏ v : Γ.V, respMass (M.resp v (fun e => x e.1)) (w v)) *
            ∏ v ∈ F, sgn (w v)) := fun w => by ring
  simp only [lat] at this ⊢
  rw [Finset.sum_congr rfl fun w _ => this w, ← Finset.mul_sum, key x]




theorem lat_update (M : GModel Γ) (e₀ : Γ.Edge) (x : ∀ e : Γ.Edge, M.L e) (s : M.L e₀) :
    lat M (Function.update x e₀ s) * M.μ e₀ (x e₀) = lat M x * M.μ e₀ s := by
  have h1 : lat M (Function.update x e₀ s)
      = M.μ e₀ s * ∏ e ∈ Finset.univ.erase e₀, M.μ e (x e) := by
    rw [lat, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e₀)]
    congr 1
    · simp
    · exact Finset.prod_congr rfl fun e he => by
        rw [Function.update_of_ne (Finset.mem_erase.1 he).1]
  have h2 : lat M x = M.μ e₀ (x e₀) * ∏ e ∈ Finset.univ.erase e₀, M.μ e (x e) :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e₀)).symm
  rw [h1, h2]; ring

/-- Re-randomizing one source coordinate does not change a latent average. -/
theorem rerand (M : GModel Γ) (hM : M.Valid) (e₀ : Γ.Edge) (f : (∀ e : Γ.Edge, M.L e) → ℝ) :
    (∑ s : M.L e₀, ∑ x : (∀ e : Γ.Edge, M.L e),
        M.μ e₀ s * (lat M x * f (Function.update x e₀ s)))
      = ∑ x : (∀ e : Γ.Edge, M.L e), lat M x * f x := by
  classical
  set Ψ : M.L e₀ × (∀ e : Γ.Edge, M.L e) → M.L e₀ × (∀ e : Γ.Edge, M.L e) :=
    fun p => (p.2 e₀, Function.update p.2 e₀ p.1) with hΨ
  have hinv : Function.Involutive Ψ := by
    intro p
    simp only [hΨ, Function.update_self, Function.update_idem, Function.update_eq_self]
  have hbij : Function.Bijective Ψ := hinv.bijective
  set g : M.L e₀ × (∀ e : Γ.Edge, M.L e) → ℝ :=
    fun p => M.μ e₀ p.1 * (lat M p.2 * f (Function.update p.2 e₀ p.1)) with hg
  have h1 : (∑ p : M.L e₀ × (∀ e : Γ.Edge, M.L e), g p)
      = ∑ p : M.L e₀ × (∀ e : Γ.Edge, M.L e), g (Ψ p) :=
    (Fintype.sum_bijective Ψ hbij _ _ (fun _ => rfl)).symm
  have h2 : ∀ p : M.L e₀ × (∀ e : Γ.Edge, M.L e),
      g (Ψ p) = M.μ e₀ p.1 * (lat M p.2 * f p.2) := by
    intro p
    simp only [hg, hΨ]
    rw [Function.update_idem, Function.update_eq_self]
    linear_combination (f p.2) * lat_update M e₀ p.2 p.1
  rw [Fintype.sum_prod_type] at h1
  simp only [h2] at h1
  rw [h1]
  have h3 : ∀ s : M.L e₀,
      (∑ x : (∀ e : Γ.Edge, M.L e), M.μ e₀ s * (lat M x * f x))
        = M.μ e₀ s * ∑ x : (∀ e : Γ.Edge, M.L e), lat M x * f x := by
    intro s; rw [Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  simp only [h3, ← Finset.sum_mul, (hM.1 e₀).2, one_mul]



section CycleGraph

variable {m : ℕ}

theorem cycleNext_val' (v : Fin m) :
    (cycleNext v).val = if v.val + 1 = m then 0 else v.val + 1 := by
  change (v.val + 1) % m = _
  by_cases h : v.val + 1 = m
  · rw [ite_eq_left h, h, Nat.mod_self]
  · rw [ite_eq_right h, Nat.mod_eq_of_lt (by omega : v.val + 1 < m)]

theorem cycleNext_ne (hm : 2 ≤ m) (v : Fin m) : v ≠ cycleNext v :=
  (CycleWitnessAux.cycleNext_ne hm v).symm

theorem cycle_adj_next (hm : 3 ≤ m) (i : Fin m) : (cycleAdj m).Adj i (cycleNext i) :=
  CycleWitnessAux.cycleAdj_next (le_trans (by decide : 2 ≤ 3) hm) i

theorem mem_edgeFinset_cycle (hm : 3 ≤ m) {a b : Fin m} (h : (cycleAdj m).Adj a b) :
    s(a, b) ∈ (cycle m hm).G.edgeFinset := by
  have h2 : s(a, b) ∈ (cycleAdj m).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact h
  exact h2

theorem adj_of_mem_edgeFinset (hm : 3 ≤ m) {a b : Fin m}
    (h : s(a, b) ∈ (cycle m hm).G.edgeFinset) : (cycleAdj m).Adj a b := by
  have h2 : s(a, b) ∈ (cycleAdj m).edgeFinset := h
  rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h2

/-- The edge of the cycle recorded by its lower endpoint. -/
def cEdge (m : ℕ) (hm : 3 ≤ m) (i : Fin m) : (cycle m hm).Edge :=
  CycleWitnessAux.ce hm i

theorem cEdge_val (hm : 3 ≤ m) (i : Fin m) :
    ((cEdge m hm i).1 : Sym2 (Fin m)) = s(i, cycleNext i) := rfl

theorem mem_inc {hm : 3 ≤ m} (v : (cycle m hm).V) (e : (cycle m hm).Edge) :
    e ∈ (cycle m hm).inc v ↔ v ∈ (e.1 : Sym2 (cycle m hm).V) :=
  CycleWitnessAux.mem_inc_iff v e

/-- Every source incident to `v` is recorded either by `v` or by a predecessor of `v`. -/
theorem inc_cases (hm : 3 ≤ m) (v : Fin m) (e : (cycle m hm).Edge)
    (h : e ∈ (cycle m hm).inc v) :
    e = cEdge m hm v ∨ ∃ p : Fin m, cycleNext p = v ∧ e = cEdge m hm p := by
  rcases (CycleWitnessAux.mem_inc_cycle hm v e).mp h with hprev | hself
  · exact Or.inr ⟨CycleWitnessAux.cyclePrev v,
      CycleWitnessAux.cycleNext_cyclePrev v, hprev⟩
  · exact Or.inl hself

/-! ### The three arcs `{0}`, `{1}` and `{2,…,m-1}` -/

variable (m)

/-- The vertex `0` of the cycle. -/
def cv0 (hm : 3 ≤ m) : Fin m := ⟨0, by omega⟩
/-- The vertex `1` of the cycle. -/
def cv1 (hm : 3 ≤ m) : Fin m := ⟨1, by omega⟩
/-- The vertex `m-1` of the cycle. -/
def cvl (hm : 3 ≤ m) : Fin m := ⟨m - 1, by omega⟩

variable {m}

theorem cycleNext_cv0 (hm : 3 ≤ m) : cycleNext (cv0 m hm) = cv1 m hm := by
  refine Fin.ext ?_
  change (0 + 1) % m = 1
  exact Nat.mod_eq_of_lt (by omega)

theorem cycleNext_cv1 (hm : 3 ≤ m) : (cycleNext (cv1 m hm)).val = 2 := by
  change (1 + 1) % m = 2
  exact Nat.mod_eq_of_lt (by omega)

theorem cycleNext_cvl (hm : 3 ≤ m) : cycleNext (cvl m hm) = cv0 m hm := by
  refine Fin.ext ?_
  change (m - 1 + 1) % m = 0
  rw [show m - 1 + 1 = m by omega, Nat.mod_self]

/-- Membership in the incidence set of the source recorded by `i`. -/
theorem mem_cEdge_iff (hm : 3 ≤ m) (v i : Fin m) :
    cEdge m hm i ∈ (cycle m hm).inc v ↔ (v = i ∨ v = cycleNext i) :=
  CycleWitnessAux.mem_inc_ce hm v i

/-- The sources incident to vertex `0` are those recorded by `m-1` and by `0`. -/
theorem inc_cv0 (hm : 3 ≤ m) (e : (cycle m hm).Edge) (h : e ∈ (cycle m hm).inc (cv0 m hm)) :
    e = cEdge m hm (cv0 m hm) ∨ e = cEdge m hm (cvl m hm) := by
  rcases inc_cases hm _ e h with h1 | ⟨p, hp, h1⟩
  · exact Or.inl h1
  · right
    have hval := congrArg Fin.val hp
    rw [cycleNext_val'] at hval
    have hp2 := p.isLt
    have hcv : (cv0 m hm).val = 0 := rfl
    rw [hcv] at hval
    have hpv : p = cvl m hm := by
      refine Fin.ext ?_
      change p.val = m - 1
      split_ifs at hval with hif
      omega
    rw [h1, hpv]

/-- The sources incident to vertex `1` are those recorded by `0` and by `1`. -/
theorem inc_cv1 (hm : 3 ≤ m) (e : (cycle m hm).Edge) (h : e ∈ (cycle m hm).inc (cv1 m hm)) :
    e = cEdge m hm (cv1 m hm) ∨ e = cEdge m hm (cv0 m hm) := by
  rcases inc_cases hm _ e h with h1 | ⟨p, hp, h1⟩
  · exact Or.inl h1
  · right
    have hval := congrArg Fin.val hp
    rw [cycleNext_val'] at hval
    have hp2 := p.isLt
    have hcv : (cv1 m hm).val = 1 := rfl
    rw [hcv] at hval
    have hpv : p = cv0 m hm := by
      refine Fin.ext ?_
      change p.val = 0
      split_ifs at hval with hif
      omega
    rw [h1, hpv]

/-- The source `{0,1}` meets no vertex of the long arc. -/
theorem cEdge_cv0_not_mem_inc (hm : 3 ≤ m) (v : Fin m) (hv : 2 ≤ v.val) :
    cEdge m hm (cv0 m hm) ∉ (cycle m hm).inc v := by
  intro h
  have h1 := (mem_cEdge_iff hm v (cv0 m hm)).1 h
  rw [cycleNext_cv0 hm] at h1
  have e0 : (cv0 m hm).val = 0 := rfl
  have e1 : (cv1 m hm).val = 1 := rfl
  rcases h1 with h1 | h1
  · have := congrArg Fin.val h1; omega
  · have := congrArg Fin.val h1; omega

/-- The source `{1,2}` does not meet the vertex `0`. -/
theorem cEdge_cv1_not_mem_inc_cv0 (hm : 3 ≤ m) :
    cEdge m hm (cv1 m hm) ∉ (cycle m hm).inc (cv0 m hm) := by
  intro h
  have h1 := (mem_cEdge_iff hm (cv0 m hm) (cv1 m hm)).1 h
  have h2 := cycleNext_cv1 hm
  have e0 : (cv0 m hm).val = 0 := rfl
  have e1 : (cv1 m hm).val = 1 := rfl
  rcases h1 with h1 | h1
  · have := congrArg Fin.val h1; omega
  · have := congrArg Fin.val h1; omega

theorem cEdge_cv0_ne_cv1 (hm : 3 ≤ m) : cEdge m hm (cv0 m hm) ≠ cEdge m hm (cv1 m hm) := by
  intro h
  refine cEdge_cv1_not_mem_inc_cv0 hm ?_
  rw [← h]
  exact (mem_cEdge_iff hm (cv0 m hm) (cv0 m hm)).2 (Or.inl rfl)

/-! ### The boundaries of the three arcs -/

theorem boundary_card_two (_hm : 3 ≤ m) (F : Finset (Fin m)) (p q : Fin m)
    (hpq : p.val ≠ q.val)
    (h : ∀ v : Fin m, (¬((v ∈ F) ↔ (cycleNext v ∈ F))) ↔ (v.val = p.val ∨ v.val = q.val)) :
    (cycleBoundary m F).card = 2 := by
  have he : cycleBoundary m F = {p, q} := by
    ext v
    rw [mem_cycleBoundary, h v, Finset.mem_insert, Finset.mem_singleton]
    exact or_congr Fin.val_inj Fin.val_inj
  rw [he, Finset.card_pair (fun hc => hpq (congrArg Fin.val hc))]

theorem mem_arcA (hm : 3 ≤ m) (u : Fin m) : u ∈ ({cv0 m hm} : Finset (Fin m)) ↔ u.val = 0 := by
  rw [Finset.mem_singleton]
  exact Fin.val_inj.symm

theorem mem_arcB (hm : 3 ≤ m) (u : Fin m) : u ∈ ({cv1 m hm} : Finset (Fin m)) ↔ u.val = 1 := by
  rw [Finset.mem_singleton]
  exact Fin.val_inj.symm

theorem mem_pair01 (hm : 3 ≤ m) (u : Fin m) :
    u ∈ ({cv0 m hm, cv1 m hm} : Finset (Fin m)) ↔ (u.val = 0 ∨ u.val = 1) := by
  rw [Finset.mem_insert, Finset.mem_singleton]
  exact or_congr Fin.val_inj.symm Fin.val_inj.symm

theorem boundary_arcA (hm : 3 ≤ m) : (cycleBoundary m {cv0 m hm}).card = 2 := by
  refine boundary_card_two hm _ (cv0 m hm) (cvl m hm) (by change (0:ℕ) ≠ m - 1; omega) ?_
  intro v
  have hv := v.isLt
  have hnv := cycleNext_val' v
  rw [mem_arcA hm v, mem_arcA hm (cycleNext v)]
  change _ ↔ (v.val = 0 ∨ v.val = m - 1)
  by_cases hif : v.val + 1 = m
  · rw [ite_eq_left hif] at hnv; rw [hnv]; omega
  · rw [ite_eq_right hif] at hnv; rw [hnv]; omega

theorem boundary_arcB (hm : 3 ≤ m) : (cycleBoundary m {cv1 m hm}).card = 2 := by
  refine boundary_card_two hm _ (cv0 m hm) (cv1 m hm) (by change (0:ℕ) ≠ 1; omega) ?_
  intro v
  have hv := v.isLt
  have hnv := cycleNext_val' v
  rw [mem_arcB hm v, mem_arcB hm (cycleNext v)]
  change _ ↔ (v.val = 0 ∨ v.val = 1)
  by_cases hif : v.val + 1 = m
  · rw [ite_eq_left hif] at hnv; rw [hnv]; omega
  · rw [ite_eq_right hif] at hnv; rw [hnv]; omega

theorem boundary_arcC (hm : 3 ≤ m) :
    (cycleBoundary m ({cv0 m hm, cv1 m hm} : Finset (Fin m))ᶜ).card = 2 := by
  rw [cycleBoundary_compl]
  refine boundary_card_two hm _ (cv1 m hm) (cvl m hm) (by change (1:ℕ) ≠ m - 1; omega) ?_
  intro v
  have hv := v.isLt
  have hnv := cycleNext_val' v
  rw [mem_pair01 hm v, mem_pair01 hm (cycleNext v)]
  change _ ↔ (v.val = 1 ∨ v.val = m - 1)
  by_cases hif : v.val + 1 = m
  · rw [ite_eq_left hif] at hnv; rw [hnv]; omega
  · rw [ite_eq_right hif] at hnv; rw [hnv]; omega

end CycleGraph

/-! ### Re-randomization in the average form -/

theorem av_def {X : Type*} [Fintype X] (μ f : X → ℝ) : av μ f = ∑ x, μ x * f x := rfl

theorem av_rerand (M : GModel Γ) (hM : M.Valid) (e₀ : Γ.Edge)
    (f : (∀ e : Γ.Edge, M.L e) → ℝ) :
    av (M.μ e₀) (fun s => av (lat M) (fun x => f (Function.update x e₀ s))) = av (lat M) f := by
  have key : av (M.μ e₀) (fun s => av (lat M) (fun x => f (Function.update x e₀ s)))
      = ∑ s : M.L e₀, ∑ x : (∀ e : Γ.Edge, M.L e),
          M.μ e₀ s * (lat M x * f (Function.update x e₀ s)) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    dsimp only
    rw [av_def, Finset.mul_sum]
  rw [key, rerand M hM e₀ f]
  rfl

/-! ### The Walsh moments of a model of the cycle -/

theorem cycle_moment {m : ℕ} (hm : 3 ≤ m) (q : ℝ) (M : GModel (cycle m hm))
    (hlaw : M.law = cycleTarget m q) (F : Finset (Fin m)) :
    av (lat M) (fun x => ∏ v ∈ F, sResp M v x) = (-q) ^ ((cycleBoundary m F).card / 2) := by
  have h1 := moment_eq M F
  rw [hlaw] at h1
  exact h1.symm.trans (cycleTarget_moment m q F)

/-! ### Reduction of a model to the triangle pattern

Two sources `eX`, `eY` and three groups of vertices: `v0`, which does not see `eY`; `v1`,
which sees only `eX` and `eY`; and a block `S`, no vertex of which sees `eX`. -/

theorem tri_reduction (M : GModel Γ) (hM : M.Valid)
    (eX eY : Γ.Edge) (hXY : eX ≠ eY) (v0 v1 : Γ.V) (S : Finset Γ.V)
    (hprodsplit : ∀ y : (∀ e : Γ.Edge, M.L e),
      sResp M v0 y * sResp M v1 y * ∏ v ∈ S, sResp M v y = ∏ v : Γ.V, sResp M v y)
    (hv0 : eY ∉ Γ.inc v0)
    (hv1 : ∀ e ∈ Γ.inc v1, e = eX ∨ e = eY)
    (hS : ∀ v ∈ S, eX ∉ Γ.inc v)
    (r : ℝ)
    (hA : av (lat M) (fun x => sResp M v0 x) ≤ r)
    (hB : av (lat M) (fun x => sResp M v1 x) ≤ r)
    (hC : av (lat M) (fun x => ∏ v ∈ S, sResp M v x) ≤ r) :
    -4 * (1 - av (lat M) (fun x => ∏ v : Γ.V, sResp M v x)) ≤ r := by
  classical
  obtain ⟨x₀⟩ : Nonempty (∀ e : Γ.Edge, M.L e) :=
    ⟨fun e => (exists_pos_of_isLaw _ (hM.1 e)).choose⟩
  have hbnd : ∀ (v : Γ.V) (x : ∀ e : Γ.Edge, M.L e), |sResp M v x| ≤ 1 :=
    fun v x => abs_le.2 (sResp_bound M hM v x)
  -- `v1` sees only the two distinguished sources
  have hb2 : ∀ (t : M.L eY) (s : M.L eX) (x : ∀ e : Γ.Edge, M.L e),
      sResp M v1 (Function.update (Function.update x₀ eX s) eY t)
        = sResp M v1 (Function.update (Function.update x eX s) eY t) := by
    intro t s x
    refine sResp_congr M _ fun e he => ?_
    rcases hv1 e he with h | h
    · subst h
      rw [Function.update_of_ne hXY, Function.update_self,
        Function.update_of_ne hXY, Function.update_self]
    · subst h
      rw [Function.update_self, Function.update_self]
  -- `v0` does not see `eY`
  have ha2 : ∀ (t : M.L eY) (s : M.L eX) (x : ∀ e : Γ.Edge, M.L e),
      sResp M v0 (Function.update x eX s)
        = sResp M v0 (Function.update (Function.update x eX s) eY t) := by
    intro t s x
    refine sResp_congr M _ fun e he => ?_
    have hne : e ≠ eY := by
      intro h
      exact hv0 (h ▸ he)
    rw [Function.update_of_ne hne]
  -- no vertex of the block sees `eX`
  have hc2 : ∀ (t : M.L eY) (s : M.L eX) (x : ∀ e : Γ.Edge, M.L e) (v : Γ.V), v ∈ S →
      sResp M v (Function.update x eY t)
        = sResp M v (Function.update (Function.update x eX s) eY t) := by
    intro t s x v hv
    refine sResp_congr M _ fun e he => ?_
    have hne : e ≠ eX := by
      intro h
      exact hS v hv (h ▸ he)
    by_cases hY : e = eY
    · rw [hY, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hY, Function.update_of_ne hY, Function.update_of_ne hne]
  -- the three means
  have hAr : av (M.μ eX) (fun s => av (lat M)
      (fun x => sResp M v0 (Function.update x eX s))) ≤ r := by
    refine le_trans (le_of_eq ?_) hA
    exact av_rerand M hM eX (fun x => sResp M v0 x)
  have hBstep : ∀ t : M.L eY,
      av (M.μ eX) (fun s =>
          sResp M v1 (Function.update (Function.update x₀ eX s) eY t))
        = av (lat M) (fun x => sResp M v1 (Function.update x eY t)) := by
    intro t
    have e1 : av (M.μ eX) (fun s =>
          sResp M v1 (Function.update (Function.update x₀ eX s) eY t))
        = av (M.μ eX) (fun s => av (lat M) (fun x =>
            sResp M v1 (Function.update (Function.update x eX s) eY t))) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      refine congrArg _ ?_
      dsimp only
      rw [(av_const (lat_isLaw M hM)
        (sResp M v1 (Function.update (Function.update x₀ eX s) eY t))).symm]
      refine Finset.sum_congr rfl fun x _ => ?_
      refine congrArg _ ?_
      exact hb2 t s x
    rw [e1]
    exact av_rerand M hM eX (fun y => sResp M v1 (Function.update y eY t))
  have hBr : av (M.μ eY) (fun t => av (M.μ eX) (fun s =>
      sResp M v1 (Function.update (Function.update x₀ eX s) eY t))) ≤ r := by
    refine le_trans (le_of_eq ?_) hB
    have e2 : av (M.μ eY) (fun t => av (M.μ eX) (fun s =>
          sResp M v1 (Function.update (Function.update x₀ eX s) eY t)))
        = av (M.μ eY) (fun t => av (lat M)
            (fun x => sResp M v1 (Function.update x eY t))) := by
      refine Finset.sum_congr rfl fun t _ => ?_
      exact congrArg _ (hBstep t)
    rw [e2]
    exact av_rerand M hM eY (fun x => sResp M v1 x)
  have hCr : av (M.μ eY) (fun t => av (lat M)
      (fun x => ∏ v ∈ S, sResp M v (Function.update x eY t))) ≤ r := by
    refine le_trans (le_of_eq ?_) hC
    exact av_rerand M hM eY (fun x => ∏ v ∈ S, sResp M v x)
  -- the parity moment
  have inner : ∀ (t : M.L eY) (s : M.L eX) (x : ∀ e : Γ.Edge, M.L e),
      sResp M v0 (Function.update x eX s) *
          sResp M v1 (Function.update (Function.update x₀ eX s) eY t) *
          ∏ v ∈ S, sResp M v (Function.update x eY t)
        = ∏ v : Γ.V, sResp M v (Function.update (Function.update x eX s) eY t) := by
    intro t s x
    rw [ha2 t s x, hb2 t s x,
      ← hprodsplit (Function.update (Function.update x eX s) eY t)]
    congr 1
    exact Finset.prod_congr rfl fun v hv => hc2 t s x v hv
  have hWeq : av (M.μ eY) (fun t => av (M.μ eX) (fun s => av (lat M) (fun x =>
        sResp M v0 (Function.update x eX s) *
          sResp M v1 (Function.update (Function.update x₀ eX s) eY t) *
          ∏ v ∈ S, sResp M v (Function.update x eY t))))
      = av (lat M) (fun x => ∏ v : Γ.V, sResp M v x) := by
    have e1 : ∀ t : M.L eY,
        av (M.μ eX) (fun s => av (lat M) (fun x =>
          sResp M v0 (Function.update x eX s) *
            sResp M v1 (Function.update (Function.update x₀ eX s) eY t) *
            ∏ v ∈ S, sResp M v (Function.update x eY t)))
          = av (lat M) (fun x => ∏ v : Γ.V, sResp M v (Function.update x eY t)) := by
      intro t
      have e2 : av (M.μ eX) (fun s => av (lat M) (fun x =>
            sResp M v0 (Function.update x eX s) *
              sResp M v1 (Function.update (Function.update x₀ eX s) eY t) *
              ∏ v ∈ S, sResp M v (Function.update x eY t)))
          = av (M.μ eX) (fun s => av (lat M) (fun x =>
              ∏ v : Γ.V, sResp M v (Function.update (Function.update x eX s) eY t))) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        refine congrArg _ ?_
        refine Finset.sum_congr rfl fun x _ => ?_
        refine congrArg _ ?_
        exact inner t s x
      rw [e2]
      exact av_rerand M hM eX (fun y => ∏ v : Γ.V, sResp M v (Function.update y eY t))
    have e3 : av (M.μ eY) (fun t => av (M.μ eX) (fun s => av (lat M) (fun x =>
          sResp M v0 (Function.update x eX s) *
            sResp M v1 (Function.update (Function.update x₀ eX s) eY t) *
            ∏ v ∈ S, sResp M v (Function.update x eY t))))
        = av (M.μ eY) (fun t => av (lat M)
            (fun x => ∏ v : Γ.V, sResp M v (Function.update x eY t))) := by
      refine Finset.sum_congr rfl fun t _ => ?_
      exact congrArg _ (e1 t)
    rw [e3]
    exact av_rerand M hM eY (fun x => ∏ v : Γ.V, sResp M v x)
  have key := quant_rigidity (M.μ eX) (M.μ eY) (lat M) (hM.1 eX) (hM.1 eY)
    (lat_isLaw M hM)
    (fun s x => sResp M v0 (Function.update x eX s))
    (fun s t => sResp M v1 (Function.update (Function.update x₀ eX s) eY t))
    (fun x t => ∏ v ∈ S, sResp M v (Function.update x eY t))
    (fun s x => hbnd _ _) (fun s t => hbnd _ _)
    (fun x t => by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun v _ => abs_nonneg _) (fun v _ => hbnd _ _))
    r hAr hBr hCr
  rwa [hWeq] at key

/-! ### The cycle case of the reduction -/

theorem cycle_arc_bound {m : ℕ} (hm : 3 ≤ m) (M : GModel (cycle m hm)) (hM : M.Valid) (r : ℝ)
    (hA : av (lat M) (fun x => sResp M (cv0 m hm) x) ≤ r)
    (hB : av (lat M) (fun x => sResp M (cv1 m hm) x) ≤ r)
    (hC : av (lat M) (fun x => ∏ v ∈ ({cv0 m hm, cv1 m hm} : Finset (Fin m))ᶜ, sResp M v x) ≤ r) :
    -4 * (1 - av (lat M) (fun x => ∏ v : Fin m, sResp M v x)) ≤ r := by
  have h01 : cv0 m hm ≠ cv1 m hm := by
    intro h
    have h2 := congrArg Fin.val h
    simp only [cv0, cv1] at h2
    omega
  refine tri_reduction M hM (cEdge m hm (cv0 m hm)) (cEdge m hm (cv1 m hm))
    (cEdge_cv0_ne_cv1 hm) (cv0 m hm) (cv1 m hm)
    (({cv0 m hm, cv1 m hm} : Finset (Fin m))ᶜ) ?_ (cEdge_cv1_not_mem_inc_cv0 hm) ?_ ?_
    r hA hB hC
  · intro y
    have h := Finset.prod_mul_prod_compl ({cv0 m hm, cv1 m hm} : Finset (Fin m))
      (fun v => sResp M v y)
    rw [Finset.prod_pair h01] at h
    exact h
  · intro e he
    rcases inc_cv1 hm e he with h | h
    · exact Or.inr h
    · exact Or.inl h
  · intro v hv
    have hv1 : ¬ (v ∈ ({cv0 m hm, cv1 m hm} : Finset (Fin m))) := Finset.mem_compl.1 hv
    have hv2 : 2 ≤ v.val := by
      by_contra hcon
      exact hv1 ((mem_pair01 hm v).2 (by omega))
    exact cEdge_cv0_not_mem_inc hm v hv2

/-! ### Transfer of moments along total variation -/

theorem moment_transfer {α : Type*} [Fintype α] (P Q f : α → ℝ) (hf : ∀ a, |f a| ≤ 1) :
    |(∑ a, P a * f a) - ∑ a, Q a * f a| ≤ 2 * dTV P Q := by
  have e : (∑ a, P a * f a) - ∑ a, Q a * f a = ∑ a, (P a - Q a) * f a := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hstep : ∀ a, |(P a - Q a) * f a| ≤ |P a - Q a| := by
    intro a
    rw [abs_mul]
    nlinarith [abs_nonneg (P a - Q a), hf a, abs_nonneg (f a)]
  refine le_trans (Finset.sum_le_sum fun a _ => hstep a) ?_
  rw [dTV]
  linarith

theorem abs_prod_sgn {α : Type*} (F : Finset α) (w : α → Bool) :
    |∏ v ∈ F, sgn (w v)| ≤ 1 := by
  classical
  rw [Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun v _ => abs_nonneg _) (fun v _ => ?_)
  cases w v <;> simp [sgn]

/-! ### The compatible set is nonempty -/

theorem exists_gCompatible (Γ : PairGraph) : ∃ Q, GCompatible Γ Q := by
  classical
  refine ⟨GModel.law ⟨fun _ => Unit, fun _ => inferInstance, fun _ _ => 1, fun _ _ => 1 / 2⟩, ?_⟩
  refine ⟨_, ⟨fun e => ⟨fun _ => zero_le_one, ?_⟩, fun v c => ⟨by norm_num, by norm_num⟩⟩, rfl⟩
  simp

end CycleModelAux

open CycleModelAux in
/-- AUDIT-NOTES A5, incompatibility of the cycle target. Partition the cycle into three
nonempty contiguous arcs and output the product of the signs in each arc: a compatible cycle
law induces a compatible triangle law, parity-perfect, whose three means are all `-q`, and
`(-q)^3 < 0` contradicts `parity_rigidity`. (The proof below uses the quantitative form
`CycleModelAux.quant_rigidity` of rigidity, which subsumes the exact one.) -/
theorem cycle_not_compatible (m : ℕ) (hm : 3 ≤ m) (q : ℝ) (hq0 : 0 < q) :
    ¬ GCompatible (cycle m hm) (cycleTarget m q) := by
  rintro ⟨M, hM, hlaw⟩
  have hA : av (lat M) (fun x => sResp M (cv0 m hm) x) = -q := by
    have h := cycle_moment hm q M hlaw {cv0 m hm}
    rw [boundary_arcA hm] at h
    simpa using h
  have hB : av (lat M) (fun x => sResp M (cv1 m hm) x) = -q := by
    have h := cycle_moment hm q M hlaw {cv1 m hm}
    rw [boundary_arcB hm] at h
    simpa using h
  have hC : av (lat M)
      (fun x => ∏ v ∈ ({cv0 m hm, cv1 m hm} : Finset (Fin m))ᶜ, sResp M v x) = -q := by
    have h := cycle_moment hm q M hlaw ({cv0 m hm, cv1 m hm} : Finset (Fin m))ᶜ
    rw [boundary_arcC hm] at h
    simpa using h
  have hW : av (lat M) (fun x => ∏ v : Fin m, sResp M v x) = 1 := by
    have h := cycle_moment hm q M hlaw Finset.univ
    rw [cycleBoundary_univ] at h
    simpa using h
  have key := cycle_arc_bound hm M hM (-q) (le_of_eq hA) (le_of_eq hB) (le_of_eq hC)
  rw [hW] at key
  norm_num at key
  linarith

open CycleModelAux in
/-- AUDIT-NOTES A5, the quantitative form: parity repair (a compatible law with parity error
`η` is within `5η` of a parity-perfect compatible law) turns the rigidity contradiction into
`d_TV(P_{m,q}, C_{C_m}) ≥ q/12`. The proof below replaces the repair construction by the
moment form `CycleModelAux.quant_rigidity`, which gives the sharper constant `q/10`; the
hypothesis `m² q ≤ 1/4` (which makes `cycleTarget` a law) is not needed for the bound. -/
theorem cycle_distance (m : ℕ) (hm : 3 ≤ m) (q : ℝ) (hq0 : 0 < q) :
    q / 12 ≤ distToCompatible (cycle m hm) (cycleTarget m q) := by
  have hset : distToCompatible (cycle m hm) (cycleTarget m q)
      = sInf {d : ℝ | ∃ Q : GTarget (cycle m hm), GCompatible (cycle m hm) Q ∧
          d = dTV (cycleTarget m q) Q} := rfl
  rw [hset]
  obtain ⟨Q₀, hQ₀⟩ := exists_gCompatible (cycle m hm)
  refine le_csInf ⟨dTV (cycleTarget m q) Q₀, Q₀, hQ₀, rfl⟩ ?_
  rintro d ⟨Q, ⟨M, hM, rfl⟩, rfl⟩
  set dd := dTV (cycleTarget m q) M.law with hdd
  have htrans : ∀ F : Finset (Fin m),
      |(-q) ^ ((cycleBoundary m F).card / 2)
        - av (lat M) (fun x => ∏ v ∈ F, sResp M v x)| ≤ 2 * dd := by
    intro F
    have h1 : (∑ w : Fin m → Bool, cycleTarget m q w * ∏ v ∈ F, sgn (w v))
        = (-q) ^ ((cycleBoundary m F).card / 2) := cycleTarget_moment m q F
    have h2 : (∑ w : Fin m → Bool, M.law w * ∏ v ∈ F, sgn (w v))
        = av (lat M) (fun x => ∏ v ∈ F, sResp M v x) := moment_eq M F
    have h3 := moment_transfer (cycleTarget m q) (M.law : (Fin m → Bool) → ℝ)
      (fun w => ∏ v ∈ F, sgn (w v)) (fun w => abs_prod_sgn F w)
    rw [h1, h2] at h3
    exact h3
  have harc : ∀ F : Finset (Fin m), (cycleBoundary m F).card = 2 →
      av (lat M) (fun x => ∏ v ∈ F, sResp M v x) ≤ -q + 2 * dd := by
    intro F hF
    have h := htrans F
    rw [hF, show (2 : ℕ) / 2 = 1 from rfl, pow_one] at h
    linarith [(abs_le.1 h).1]
  have hA : av (lat M) (fun x => sResp M (cv0 m hm) x) ≤ -q + 2 * dd := by
    simpa using harc {cv0 m hm} (boundary_arcA hm)
  have hB : av (lat M) (fun x => sResp M (cv1 m hm) x) ≤ -q + 2 * dd := by
    simpa using harc {cv1 m hm} (boundary_arcB hm)
  have hC := harc ({cv0 m hm, cv1 m hm} : Finset (Fin m))ᶜ (boundary_arcC hm)
  have hWle : 1 - av (lat M) (fun x => ∏ v : Fin m, sResp M v x) ≤ 2 * dd := by
    have h := htrans Finset.univ
    rw [cycleBoundary_univ] at h
    simp only [Finset.card_empty, Nat.zero_div, pow_zero] at h
    linarith [(abs_le.1 h).2]
  have key := cycle_arc_bound hm M hM (-q + 2 * dd) hA hB hC
  linarith

end TriangleInflation.Graph
