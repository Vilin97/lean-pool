/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development001
/-!
# Moving sofa: related mathematical developments

* `Gerver.Foundations.Development001`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Gerver.AreaCertificate`.
* `Gerver.Area.TrigEnclosure`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Exact rational certificate for the Gerver cap and niche areas

This module carries the finite, kernel-checkable part of the rational area bounds for
Gerver's sofa: integer interval arithmetic at scale `M = 10 ^ 30`, certified enclosures of
the twenty-two direct parameters and of `π`, interval sine and cosine by the Taylor
recurrence, the grid of rotation angles, the five phase formulas, the support-contact fan
of the cap and the rectangle cover of the niche.

Everything here is computable and `decide +kernel`-checkable; the two closed numeric
conclusions `capOK_true` and `nicheOK_true` are the only facts the analytic layer in
`MovingSofa.Gerver.Area` needs from this module.
-/

/-! ### Integer interval arithmetic at scale `10 ^ 30`

The kernel accelerates `Int` arithmetic but not `Rat` arithmetic, so the whole finite
calculation is carried out on pairs of integers denoting the interval `[lo / M, hi / M]`.
-/

public section

namespace MovingSofa.GerverAreaCert

/-- The common denominator of every interval endpoint. -/
def M : ℤ := 10 ^ 30

/-- `⟨lo, hi⟩` denotes the real interval `[lo / M, hi / M]`. -/
structure SI where
  /-- The scaled integer lower endpoint. -/
  lo : ℤ
  /-- The scaled integer upper endpoint. -/
  hi : ℤ
  deriving DecidableEq

namespace SI

/-- Kernel-cheap `min` on `ℤ`. -/
def imin (a b : ℤ) : ℤ := if a ≤ b then a else b
/-- Kernel-cheap `max` on `ℤ`. -/
def imax (a b : ℤ) : ℤ := if a ≤ b then b else a

/-- Outward enclosure of `a / b` for `0 < b`. -/
def ratI (a b : ℤ) : SI := ⟨(a * M) / b, -((-(a * M)) / b)⟩

/-- The exact interval `[0, 0]`. -/
@[expose]
def zero : SI := ⟨0, 0⟩
/-- The exact interval `[1, 1]`. -/
def one : SI := ⟨M, M⟩

/-- Interval addition. -/
@[expose]
def add (x y : SI) : SI := ⟨x.lo + y.lo, x.hi + y.hi⟩
/-- Interval negation. -/
def neg (x : SI) : SI := ⟨-x.hi, -x.lo⟩
/-- Interval subtraction. -/
@[expose]
def sub (x y : SI) : SI := ⟨x.lo - y.hi, x.hi - y.lo⟩

/-- Interval multiplication: the extreme endpoint products, rounded outward. -/
def mul (x y : SI) : SI :=
  let p₁ := x.lo * y.lo
  let p₂ := x.lo * y.hi
  let p₃ := x.hi * y.lo
  let p₄ := x.hi * y.hi
  ⟨imin (imin p₁ p₂) (imin p₃ p₄) / M,
    -((-(imax (imax p₁ p₂) (imax p₃ p₄))) / M)⟩

/-- Division by a positive integer. -/
@[expose]
def divn (x : SI) (b : ℤ) : SI := ⟨x.lo / b, -((-x.hi) / b)⟩

/-- Multiplication by an integer. -/
def imul (k : ℤ) (x : SI) : SI :=
  ⟨imin (k * x.lo) (k * x.hi), imax (k * x.lo) (k * x.hi)⟩

/-! #### Real semantics and soundness -/

/-- `z` denotes the real interval `[z.lo / M, z.hi / M]`. -/
@[expose]
def Contains (z : SI) (x : ℝ) : Prop :=
  (z.lo : ℝ) ≤ (M : ℝ) * x ∧ (M : ℝ) * x ≤ (z.hi : ℝ)

/-- `imin` is `min`. -/
theorem imin_eq_min (a b : ℤ) : imin a b = min a b := by
  simp only [imin, min_def]

/-- `imax` is `max`. -/
theorem imax_eq_max (a b : ℤ) : imax a b = max a b := by
  rcases le_total a b with h | h
  · simp [imax, h]
  · rcases eq_or_lt_of_le h with rfl | hlt
    · simp [imax]
    · simp [imax, not_le.mpr hlt, max_eq_left h]

/-- The scale is positive. -/
theorem Mpos : (0 : ℝ) < (M : ℝ) := by
  have : (M : ℤ) = 10 ^ 30 := rfl
  rw [this]
  norm_num

private theorem mul_ediv_le (p : ℤ) {b : ℤ} (hb : 0 < b) : b * (p / b) ≤ p := by
  have h := Int.mul_ediv_add_emod p b
  have h2 : 0 ≤ p % b := Int.emod_nonneg p hb.ne'
  linarith

private theorem le_mul_neg_ediv (p : ℤ) {b : ℤ} (hb : 0 < b) : p ≤ b * -((-p) / b) := by
  have h := mul_ediv_le (-p) hb
  rw [mul_neg]
  linarith

/-- Integer floor division rounds down in the reals. -/
theorem ediv_le_of_le {p : ℤ} {b : ℤ} (hb : 0 < b) {r : ℝ} (h : (p : ℝ) ≤ (b : ℝ) * r) :
    ((p / b : ℤ) : ℝ) ≤ r := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h1 : ((b : ℝ)) * ((p / b : ℤ) : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast mul_ediv_le p hb
  have := h1.trans h
  exact le_of_mul_le_mul_left this hbR

/-- Integer ceiling division rounds up in the reals. -/
theorem le_neg_ediv_of_le {p : ℤ} {b : ℤ} (hb : 0 < b) {r : ℝ} (h : (b : ℝ) * r ≤ (p : ℝ)) :
    r ≤ ((-((-p) / b) : ℤ) : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h1 : (p : ℝ) ≤ (b : ℝ) * ((-((-p) / b) : ℤ) : ℝ) := by
    exact_mod_cast le_mul_neg_ediv p hb
  exact le_of_mul_le_mul_left (h.trans h1) hbR

private theorem min_mul_le_mul {l h u v : ℝ} (hl : l ≤ u) (hu : u ≤ h) :
    min (l * v) (h * v) ≤ u * v := by
  rcases le_total 0 v with hv | hv
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

private theorem mul_le_max_mul {l h u v : ℝ} (hl : l ≤ u) (hu : u ≤ h) :
    u * v ≤ max (l * v) (h * v) := by
  rcases le_total 0 v with hv | hv
  · exact le_trans (by nlinarith) (le_max_right _ _)
  · exact le_trans (by nlinarith) (le_max_left _ _)

private theorem min_four_le_mul {l₁ h₁ l₂ h₂ u v : ℝ}
    (h1 : l₁ ≤ u) (h2 : u ≤ h₁) (h3 : l₂ ≤ v) (h4 : v ≤ h₂) :
    min (min (l₁ * l₂) (l₁ * h₂)) (min (h₁ * l₂) (h₁ * h₂)) ≤ u * v := by
  have hA : min (min (l₁ * l₂) (l₁ * h₂)) (min (h₁ * l₂) (h₁ * h₂)) ≤ min (l₁ * l₂) (h₁ * l₂) :=
    le_min ((min_le_left _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_left _ _))
  have hB : min (min (l₁ * l₂) (l₁ * h₂)) (min (h₁ * l₂) (h₁ * h₂)) ≤ min (l₁ * h₂) (h₁ * h₂) :=
    le_min ((min_le_left _ _).trans (min_le_right _ _))
      ((min_le_right _ _).trans (min_le_right _ _))
  have h5 : min (min (l₁ * l₂) (l₁ * h₂)) (min (h₁ * l₂) (h₁ * h₂)) ≤ u * l₂ :=
    hA.trans (min_mul_le_mul h1 h2)
  have h6 : min (min (l₁ * l₂) (l₁ * h₂)) (min (h₁ * l₂) (h₁ * h₂)) ≤ u * h₂ :=
    hB.trans (min_mul_le_mul h1 h2)
  have h7 : min (u * l₂) (u * h₂) ≤ u * v := by
    simpa [mul_comm] using min_mul_le_mul (l := l₂) (h := h₂) (u := v) (v := u) h3 h4
  exact (le_min h5 h6).trans h7

private theorem mul_le_max_four {l₁ h₁ l₂ h₂ u v : ℝ}
    (h1 : l₁ ≤ u) (h2 : u ≤ h₁) (h3 : l₂ ≤ v) (h4 : v ≤ h₂) :
    u * v ≤ max (max (l₁ * l₂) (l₁ * h₂)) (max (h₁ * l₂) (h₁ * h₂)) := by
  have hA : max (l₁ * l₂) (h₁ * l₂) ≤ max (max (l₁ * l₂) (l₁ * h₂)) (max (h₁ * l₂) (h₁ * h₂)) :=
    max_le ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_left _ _).trans (le_max_right _ _))
  have hB : max (l₁ * h₂) (h₁ * h₂) ≤ max (max (l₁ * l₂) (l₁ * h₂)) (max (h₁ * l₂) (h₁ * h₂)) :=
    max_le ((le_max_right _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_right _ _))
  have h7 : u * v ≤ max (u * l₂) (u * h₂) := by
    simpa [mul_comm] using mul_le_max_mul (l := l₂) (h := h₂) (u := v) (v := u) h3 h4
  exact h7.trans (max_le ((mul_le_max_mul h1 h2).trans hA) ((mul_le_max_mul h1 h2).trans hB))

/-- Interval addition is sound. -/
theorem contains_add {x y : SI} {a b : ℝ} (hx : Contains x a) (hy : Contains y b) :
    Contains (add x y) (a + b) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩ <;> push_cast [add] <;> nlinarith [Mpos]

/-- Interval negation is sound. -/
theorem contains_neg {x : SI} {a : ℝ} (hx : Contains x a) : Contains (neg x) (-a) := by
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨?_, ?_⟩ <;> push_cast [neg] <;> nlinarith [Mpos]

/-- Interval subtraction is sound. -/
theorem contains_sub {x y : SI} {a b : ℝ} (hx : Contains x a) (hy : Contains y b) :
    Contains (sub x y) (a - b) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩ <;> push_cast [sub] <;> nlinarith [Mpos]

/-- Interval multiplication is sound. -/
theorem contains_mul {x y : SI} {a b : ℝ} (hx : Contains x a) (hy : Contains y b) :
    Contains (mul x y) (a * b) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hM := Mpos
  have hprod : (M : ℝ) * ((M : ℝ) * (a * b)) = ((M : ℝ) * a) * ((M : ℝ) * b) := by ring
  refine ⟨?_, ?_⟩
  · simp only [mul, imin_eq_min, imax_eq_max]
    refine ediv_le_of_le (b := M) (by exact_mod_cast hM) ?_
    push_cast
    rw [hprod]
    exact min_four_le_mul hx1 hx2 hy1 hy2
  · simp only [mul, imin_eq_min, imax_eq_max]
    refine le_neg_ediv_of_le (b := M) (by exact_mod_cast hM) ?_
    push_cast
    rw [hprod]
    exact mul_le_max_four hx1 hx2 hy1 hy2

/-- Interval division by a positive integer is sound. -/
theorem contains_divn {x : SI} {a : ℝ} {b : ℤ} (hb : 0 < b) (hx : Contains x a) :
    Contains (divn x b) (a / (b : ℝ)) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hkey : (b : ℝ) * ((M : ℝ) * (a / (b : ℝ))) = (M : ℝ) * a := by
    field_simp
  refine ⟨ediv_le_of_le hb ?_, le_neg_ediv_of_le hb ?_⟩
  · rw [hkey]; exact hx1
  · rw [hkey]; exact hx2

/-- Interval multiplication by an integer is sound. -/
theorem contains_imul {x : SI} {a : ℝ} (k : ℤ) (hx : Contains x a) :
    Contains (imul k x) ((k : ℝ) * a) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hkey : (M : ℝ) * ((k : ℝ) * a) = (k : ℝ) * ((M : ℝ) * a) := by ring
  refine ⟨?_, ?_⟩ <;> simp only [imul, imin_eq_min, imax_eq_max] <;> push_cast <;> rw [hkey]
  · simpa [mul_comm] using min_mul_le_mul (l := (x.lo : ℝ)) (h := (x.hi : ℝ))
      (u := (M : ℝ) * a) (v := (k : ℝ)) hx1 hx2
  · simpa [mul_comm] using mul_le_max_mul (l := (x.lo : ℝ)) (h := (x.hi : ℝ))
      (u := (M : ℝ) * a) (v := (k : ℝ)) hx1 hx2

/-- The outward enclosure of a rational is sound. -/
theorem contains_ratI {a b : ℤ} (hb : 0 < b) : Contains (ratI a b) ((a : ℝ) / (b : ℝ)) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hkey : (b : ℝ) * ((M : ℝ) * ((a : ℝ) / (b : ℝ))) = ((a * M : ℤ) : ℝ) := by
    push_cast
    field_simp
  refine ⟨ediv_le_of_le hb ?_, le_neg_ediv_of_le hb ?_⟩
  · rw [hkey]
  · rw [hkey]

/-- `zero` encloses `0`. -/
theorem contains_zero : Contains zero 0 := by
  constructor <;> simp [zero]

/-- `one` encloses `1`. -/
theorem contains_one : Contains one 1 := by
  constructor <;> simp [one]

/-- A left fold of exact interval additions over an initial segment encloses the
corresponding real sum. -/
theorem contains_foldl_range {f : ℕ → SI} {g : ℕ → ℝ} (n : ℕ)
    (hfg : ∀ i < n, Contains (f i) (g i)) :
    Contains ((List.range n).foldl (fun acc i => add acc (f i)) zero)
      (∑ i ∈ Finset.range n, g i) := by
  induction n with
  | zero => simpa using contains_zero
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ]
    exact contains_add (ih fun i hi => hfg i (by omega)) (hfg n (by omega))

/-- A left fold of integer additions over an initial segment is the corresponding sum. -/
theorem foldl_range_int (f : ℕ → ℤ) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]; simp

end SI

open SI

/-! ### Certified enclosures of the twenty-two parameters and of `π` -/

/-- Enclosure of the direct parameter `k₁₁`. -/
def k11Z : SI := ⟨-210322422072688751416285718490, -210322422072688751416085718490⟩
/-- Enclosure of the direct parameter `k₁₂`. -/
def k12Z : SI := ⟨249999999999999999999900000000, 250000000000000000000100000000⟩
/-- Enclosure of the direct parameter `k₂₁`. -/
def k21Z : SI := ⟨-919179292771593322274796102890, -919179292771593322274596102890⟩
/-- Enclosure of the direct parameter `k₂₂`. -/
def k22Z : SI := ⟨472406619750805465181660762512, 472406619750805465181860762512⟩
/-- Enclosure of the direct parameter `k₃₁`. -/
def k31Z : SI := ⟨-613763229430251668555014291320, -613763229430251668554814291320⟩
/-- Enclosure of the direct parameter `k₃₂`. -/
def k32Z : SI := ⟨889626479003221860726943050050, 889626479003221860727143050050⟩
/-- Enclosure of the direct parameter `k₄₁`. -/
def k41Z : SI := ⟨-308347166088910014835232479740, -308347166088910014835032479740⟩
/-- Enclosure of the direct parameter `k₄₂`. -/
def k42Z : SI := ⟨472406619750805465181660762512, 472406619750805465181860762512⟩
/-- Enclosure of the direct parameter `k₅₁`. -/
def k51Z : SI := ⟨-1017204036787814585693742864150, -1017204036787814585693542864150⟩
/-- Enclosure of the direct parameter `k₅₂`. -/
def k52Z : SI := ⟨249999999999999999999900000000, 250000000000000000000100000000⟩
/-- Enclosure of the direct parameter `a₁`. -/
def a1Z : SI := ⟨1210322422072688751416085718500, 1210322422072688751416285718500⟩
/-- Enclosure of the direct parameter `a₂`. -/
def a2Z : SI := ⟨-250000000000000000000100000000, -249999999999999999999900000000⟩
/-- Enclosure of the direct parameter `b₁`. -/
def b1Z : SI := ⟨-527624598026784624160603809370, -527624598026784624160403809370⟩
/-- Enclosure of the direct parameter `b₂`. -/
def b2Z : SI := ⟨920258385160637622893605795010, 920258385160637622893805795010⟩
/-- Enclosure of the direct parameter `c₁`. -/
def c1Z : SI := ⟨626045522848465867552229310386, 626045522848465867552429310386⟩
/-- Enclosure of the direct parameter `c₂`. -/
def c2Z : SI := ⟨-944750803946430751679092381250, -944750803946430751678892381250⟩
/-- Enclosure of the direct parameter `d₁`. -/
def d1Z : SI := ⟨1313022761424232933776064655200, 1313022761424232933776264655200⟩
/-- Enclosure of the direct parameter `d₂`. -/
def d2Z : SI := ⟨-525382670414554437202936294305, -525382670414554437202736294305⟩
/-- Enclosure of the direct parameter `e₁`. -/
def e1Z : SI := ⟨1210322422072688751416085718500, 1210322422072688751416285718500⟩
/-- Enclosure of the direct parameter `e₂`. -/
def e2Z : SI := ⟨249999999999999999999900000000, 250000000000000000000100000000⟩
/-- Enclosure of the first stage angle `φ`. -/
@[expose]
def phiZ : SI := ⟨39177364790083641863217874980, 39177364790083641863217875500⟩
/-- Enclosure of the second stage angle `θ`. -/
@[expose]
def thetaZ : SI := ⟨681301509382724894473855754540, 681301509382724894473855759660⟩

/-- The integer enclosure of `π`, from the certified Machin arctangent sums. -/
def piZ : SI := ⟨3141592653589793238462643383279, 3141592653589793238462643383280⟩

/-- The integer enclosure of `π / 2`. -/
@[expose]
def piHalfZ : SI := divn piZ 2

/-! #### The parameter enclosures are the certified box rows -/

private theorem le_M_mul {c n : ℤ} {d : ℕ} (hd : 0 < (d : ℤ)) (hc : c * (d : ℤ) = n * M)
    {x : ℝ} (h : (n : ℝ) / (d : ℝ) ≤ x) : (c : ℝ) ≤ (M : ℝ) * x := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcR : (c : ℝ) * (d : ℝ) = (n : ℝ) * (M : ℝ) := by exact_mod_cast hc
  rw [div_le_iff₀ hdR] at h
  nlinarith [SI.Mpos, h, hcR]

private theorem M_mul_le {c n : ℤ} {d : ℕ} (hd : 0 < (d : ℤ)) (hc : c * (d : ℤ) = n * M)
    {x : ℝ} (h : x ≤ (n : ℝ) / (d : ℝ)) : (M : ℝ) * x ≤ (c : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcR : (c : ℝ) * (d : ℝ) = (n : ℝ) * (M : ℝ) := by exact_mod_cast hc
  rw [le_div_iff₀ hdR] at h
  nlinarith [SI.Mpos, h, hcR]

/-- Every one of the twenty-two integer enclosures contains the corresponding certified
Gerver parameter. -/
theorem contains_params :
      SI.Contains k11Z GerverSofa.PartB.params.k11 ∧
      SI.Contains k12Z GerverSofa.PartB.params.k12 ∧
      SI.Contains k21Z GerverSofa.PartB.params.k21 ∧
      SI.Contains k22Z GerverSofa.PartB.params.k22 ∧
      SI.Contains k31Z GerverSofa.PartB.params.k31 ∧
      SI.Contains k32Z GerverSofa.PartB.params.k32 ∧
      SI.Contains k41Z GerverSofa.PartB.params.k41 ∧
      SI.Contains k42Z GerverSofa.PartB.params.k42 ∧
      SI.Contains k51Z GerverSofa.PartB.params.k51 ∧
      SI.Contains k52Z GerverSofa.PartB.params.k52 ∧
      SI.Contains a1Z GerverSofa.PartB.params.a1 ∧
      SI.Contains a2Z GerverSofa.PartB.params.a2 ∧
      SI.Contains b1Z GerverSofa.PartB.params.b1 ∧
      SI.Contains b2Z GerverSofa.PartB.params.b2 ∧
      SI.Contains c1Z GerverSofa.PartB.params.c1 ∧
      SI.Contains c2Z GerverSofa.PartB.params.c2 ∧
      SI.Contains d1Z GerverSofa.PartB.params.d1 ∧
      SI.Contains d2Z GerverSofa.PartB.params.d2 ∧
      SI.Contains e1Z GerverSofa.PartB.params.e1 ∧
      SI.Contains e2Z GerverSofa.PartB.params.e2 ∧
      SI.Contains phiZ GerverSofa.PartB.params.phi ∧
      SI.Contains thetaZ GerverSofa.PartB.params.theta := by
  have hbox := GerverSofa.PartB.params_mem
  dsimp only [GerverSofa.Romik.box, GerverSofa.qR, Set.mem_ofPred_eq] at hbox
  obtain ⟨hk11lo, hk11hi, hk12lo, hk12hi, hk21lo, hk21hi, hk22lo, hk22hi, hk31lo, hk31hi,
      hk32lo, hk32hi, hk41lo, hk41hi, hk42lo, hk42hi, hk51lo, hk51hi, hk52lo, hk52hi,
      ha1lo, ha1hi, ha2lo, ha2hi, hb1lo, hb1hi, hb2lo, hb2hi, hc1lo, hc1hi, hc2lo, hc2hi,
      hd1lo, hd1hi, hd2lo, hd2hi, he1lo, he1hi, he2lo, he2hi, hphilo, hphihi, hthetalo,
      hthetahi⟩ := hbox
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k11Z]) hk11lo,
    M_mul_le (by norm_num) (by norm_num [M, k11Z]) hk11hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k12Z]) hk12lo,
    M_mul_le (by norm_num) (by norm_num [M, k12Z]) hk12hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k21Z]) hk21lo,
    M_mul_le (by norm_num) (by norm_num [M, k21Z]) hk21hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k22Z]) hk22lo,
    M_mul_le (by norm_num) (by norm_num [M, k22Z]) hk22hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k31Z]) hk31lo,
    M_mul_le (by norm_num) (by norm_num [M, k31Z]) hk31hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k32Z]) hk32lo,
    M_mul_le (by norm_num) (by norm_num [M, k32Z]) hk32hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k41Z]) hk41lo,
    M_mul_le (by norm_num) (by norm_num [M, k41Z]) hk41hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k42Z]) hk42lo,
    M_mul_le (by norm_num) (by norm_num [M, k42Z]) hk42hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k51Z]) hk51lo,
    M_mul_le (by norm_num) (by norm_num [M, k51Z]) hk51hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k52Z]) hk52lo,
    M_mul_le (by norm_num) (by norm_num [M, k52Z]) hk52hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, a1Z]) ha1lo,
    M_mul_le (by norm_num) (by norm_num [M, a1Z]) ha1hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, a2Z]) ha2lo,
    M_mul_le (by norm_num) (by norm_num [M, a2Z]) ha2hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, b1Z]) hb1lo,
    M_mul_le (by norm_num) (by norm_num [M, b1Z]) hb1hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, b2Z]) hb2lo,
    M_mul_le (by norm_num) (by norm_num [M, b2Z]) hb2hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, c1Z]) hc1lo,
    M_mul_le (by norm_num) (by norm_num [M, c1Z]) hc1hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, c2Z]) hc2lo,
    M_mul_le (by norm_num) (by norm_num [M, c2Z]) hc2hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, d1Z]) hd1lo,
    M_mul_le (by norm_num) (by norm_num [M, d1Z]) hd1hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, d2Z]) hd2lo,
    M_mul_le (by norm_num) (by norm_num [M, d2Z]) hd2hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, e1Z]) he1lo,
    M_mul_le (by norm_num) (by norm_num [M, e1Z]) he1hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, e2Z]) he2lo,
    M_mul_le (by norm_num) (by norm_num [M, e2Z]) he2hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, phiZ]) hphilo,
    M_mul_le (by norm_num) (by norm_num [M, phiZ]) hphihi⟩, ?_⟩
  exact ⟨le_M_mul (by norm_num) (by norm_num [M, thetaZ]) hthetalo,
    M_mul_le (by norm_num) (by norm_num [M, thetaZ]) hthetahi⟩

/-- The integer enclosure of `π`. -/
theorem contains_piZ : SI.Contains piZ Real.pi := by
  obtain ⟨h1, h2⟩ := GerverSofa.ExactReplay.piI_contains_pi
  have hM := SI.Mpos
  refine ⟨?_, ?_⟩
  · have hnum : ((piZ.lo : ℤ) : ℝ) ≤ (M : ℝ) * ((GerverSofa.ExactReplay.piI.lo : ℚ) : ℝ) := by
      norm_num [piZ, M, GerverSofa.ExactReplay.piI, GerverSofa.ExactReplay.q]
    nlinarith [h1]
  · have hnum : (M : ℝ) * ((GerverSofa.ExactReplay.piI.hi : ℚ) : ℝ) ≤ ((piZ.hi : ℤ) : ℝ) := by
      norm_num [piZ, M, GerverSofa.ExactReplay.piI, GerverSofa.ExactReplay.q]
    nlinarith [h2]

/-- The integer enclosure of `π / 2`. -/
theorem contains_piHalfZ : SI.Contains piHalfZ (Real.pi / 2) := by
  change SI.Contains (SI.divn piZ 2) (Real.pi / 2)
  simpa using SI.contains_divn (b := 2) (by norm_num) contains_piZ

/-! ### Sine and cosine by the degree-41/40 Taylor recurrence -/

/-- `trigIter z t n = (Sₙ, Cₙ, ∑_{k ≤ n} Sₖ, ∑_{k ≤ n} Cₖ)` where `Sₖ` and `Cₖ` enclose the
`k`-th signed sine and cosine Taylor terms and `z` encloses `t ^ 2`. -/
def trigIter (z t : SI) : ℕ → SI × SI × SI × SI
  | 0 => (t, one, t, one)
  | n + 1 =>
    let st := trigIter z t n
    let sterm := neg (divn (mul st.1 z) (((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ))
    let cterm := neg (divn (mul st.2.1 z) (((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ))
    (sterm, cterm, add st.2.2.1 sterm, add st.2.2.2 cterm)

/-- Sine and cosine enclosures of every real number in the argument interval.
Valid for arguments in `[0, 2]`. -/
def trigZ (t : SI) : SI × SI :=
  let st := trigIter (mul t t) t 20
  (⟨st.2.2.1.lo - 1, st.2.2.1.hi + 1⟩, ⟨st.2.2.2.lo - 1, st.2.2.2.hi + 1⟩)

/-! ### Stage endpoints and the uniform grid -/

/-- Number of subintervals per analytic stage. -/
@[expose]
def NN : ℕ := 64

/-- Integer enclosures of the six stage endpoints `0, φ, θ, η, τ, π / 2`, constant past `5`. -/
@[expose]
def endZ : ℕ → SI
  | 0 => zero
  | 1 => phiZ
  | 2 => thetaZ
  | 3 => sub piHalfZ thetaZ
  | 4 => sub piHalfZ phiZ
  | _ => piHalfZ

/-- The `m`-th grid angle, `0 ≤ m ≤ 5 * NN`. -/
@[expose]
def ttZ (m : ℕ) : SI :=
  divn (add (imul ((NN - m % NN : ℕ) : ℤ) (endZ (m / NN)))
    (imul ((m % NN : ℕ) : ℤ) (endZ (m / NN + 1)))) (NN : ℤ)

/-- The analytic branch that the piecewise definitions select at the `m`-th grid angle. -/
@[expose]
def stageOf (m : ℕ) : ℕ := if m % NN = 0 then max 1 (m / NN) else m / NN + 1

/-! ### The five phase formulas and the four contact curves -/

/-- `kind`: `0` the path, `1` `A`, `2` `B`, `3` `C`, `4` `D`. -/
@[expose]
def evalZ (stage : ℕ) (t : SI) (kind : ℕ) : SI × SI :=
  let sc := trigZ t
  let s := sc.1
  let c := sc.2
  let data : SI × SI × SI × SI × SI × SI :=
    if stage = 1 then
      (add (add (mul a1Z c) (mul a2Z s)) (ratI (-1) 1),
        add (add (mul (neg a2Z) c) (mul a1Z s)) (ratI (-1) 2),
        add (add (mul (imul (-2) a1Z) s) (mul (imul 2 a2Z) c)) (ratI 1 2),
        add (add (mul (imul 2 a1Z) c) (mul (imul 2 a2Z) s)) (ratI (-1) 1),
        k11Z, k12Z)
    else if stage = 2 then
      let f := add (add (divn (neg (mul t t)) 4) (mul b1Z t)) b2Z
      (f, add (add (divn t 2) (neg b1Z)) (ratI (-1) 1),
        add (add (ratI 1 1) (imul 2 b1Z)) (neg t),
        add f (ratI 1 2), k21Z, k22Z)
    else if stage = 3 then
      let f := sub c1Z t
      let g := add c2Z t
      (f, g, add (ratI (-1) 1) (neg g), add (ratI 1 1) f, k31Z, k32Z)
    else if stage = 4 then
      let g := add (add (divn (neg (mul t t)) 4) (mul d1Z t)) d2Z
      (add (add (neg (divn t 2)) d1Z) (ratI (-1) 1), g,
        add (neg g) (ratI (-1) 2),
        add (add (imul 2 d1Z) (ratI (-1) 1)) (neg t), k41Z, k42Z)
    else
      (add (add (mul e1Z c) (mul e2Z s)) (ratI (-1) 2),
        add (add (mul (neg e2Z) c) (mul e1Z s)) (ratI (-1) 1),
        add (add (ratI 1 1) (mul (imul (-2) e1Z) s)) (mul (imul 2 e2Z) c),
        add (add (mul (imul 2 e1Z) c) (mul (imul 2 e2Z) s)) (ratI (-1) 2),
        k51Z, k52Z)
  let f := data.1
  let g := data.2.1
  let al := data.2.2.1
  let be := data.2.2.2.1
  let kx := data.2.2.2.2.1
  let ky := data.2.2.2.2.2
  let x0 := add (sub (mul c f) (mul s g)) kx
  let y0 := add (add (mul s f) (mul c g)) ky
  let x1 := if kind = 1 ∨ kind = 2 then sub x0 (mul al s) else x0
  let y1 := if kind = 1 ∨ kind = 2 then add y0 (mul al c) else y0
  let x2 := if kind = 1 then add x1 c else x1
  let y2 := if kind = 1 then add y1 s else y1
  let x3 := if kind = 3 ∨ kind = 4 then sub x2 (mul be c) else x2
  let y3 := if kind = 3 ∨ kind = 4 then sub y2 (mul be s) else y2
  (if kind = 3 then sub x3 s else x3, if kind = 3 then add y3 c else y3)

/-- The contact point at grid index `m`, evaluated on the branch the definitions select. -/
@[expose]
def contactZ (m kind : ℕ) : SI × SI := evalZ (stageOf m) (ttZ m) kind

/-! ### Cap: the ordered support contacts and their fan shoelace sum -/

/-- Number of listed support contacts feeding the fan, excluding the anchor. -/
@[expose]
def fanCount : ℕ := 10 * NN

/-- Contact kind at fan position `i`: `A` for `i ≤ 5 * NN`, otherwise `C`. -/
@[expose]
def fanKind (i : ℕ) : ℕ := if i ≤ 5 * NN then 1 else 3

/-- Grid index at fan position `i`. -/
@[expose]
def fanIdx (i : ℕ) : ℕ := if i ≤ 5 * NN then i else i - 5 * NN

/-- Both coordinates of the contact listed at fan position `i`. -/
@[expose]
def fanZ (i : ℕ) : SI × SI := contactZ (fanIdx i) (fanKind i)

/-- The fan anchor `L = C (π / 2)`. -/
@[expose]
def anchorZ : SI × SI := contactZ (5 * NN) 3

/-- The `i`-th fan determinant over the anchor. -/
@[expose]
def crossZ (i : ℕ) : SI :=
  sub (mul (sub (fanZ i).1 anchorZ.1) (sub (fanZ (i + 1)).2 anchorZ.2))
    (mul (sub (fanZ i).2 anchorZ.2) (sub (fanZ (i + 1)).1 anchorZ.1))

/-- Twice the signed area of the fan polygon: the shoelace sum of the listed contacts over
the anchor. -/
@[expose]
def capDoubledZ : SI :=
  (List.range (fanCount - 1)).foldl (fun acc i => add acc (crossZ i)) zero

/-! ### Niche: the seven roof pieces and their covering rectangles -/

/-- The seven roof pieces as `(kind, stage, traversed forwards?)`. -/
@[expose]
def rowData : ℕ → ℕ × ℕ × Bool
  | 0 => (4, 1, true)
  | 1 => (4, 2, true)
  | 2 => (0, 4, false)
  | 3 => (0, 3, false)
  | 4 => (0, 2, false)
  | 5 => (2, 4, true)
  | _ => (2, 5, true)

/-- Contact kind traced by roof piece `r`. -/
@[expose]
def rowKind (r : ℕ) : ℕ := (rowData r).1
/-- Analytic stage traced by roof piece `r`. -/
@[expose]
def rowStage (r : ℕ) : ℕ := (rowData r).2.1
/-- Whether roof piece `r` is traversed in increasing time. -/
@[expose]
def rowFwd (r : ℕ) : Bool := (rowData r).2.2

/-- Grid index of the left end of the `j`-th subinterval of row `r`. -/
@[expose]
def rowBase (r j : ℕ) : ℕ := (rowStage r - 1) * NN + j

/-- Left horizontal bound of the covering rectangle of `(r, j)`. -/
@[expose]
def rectLoZ (r j : ℕ) : ℤ :=
  if rowFwd r then (contactZ (rowBase r j) (rowKind r)).1.lo
  else (contactZ (rowBase r j + 1) (rowKind r)).1.lo

/-- Right horizontal bound of the covering rectangle of `(r, j)`. -/
@[expose]
def rectHiZ (r j : ℕ) : ℤ :=
  if rowFwd r then (contactZ (rowBase r j + 1) (rowKind r)).1.hi
  else (contactZ (rowBase r j) (rowKind r)).1.hi

/-- Height bound of the covering rectangle of `(r, j)`: the branch evaluation over the
whole subinterval, widened to cover the left endpoint, which sits on the previous branch. -/
@[expose]
def rectHZ (r j : ℕ) : ℤ :=
  imax (evalZ (stageOf (rowBase r j + 1))
      ⟨(ttZ (rowBase r j)).lo, (ttZ (rowBase r j + 1)).hi⟩ (rowKind r)).2.hi
    (contactZ (rowBase r j) (rowKind r)).2.hi

/-- Area of the covering rectangle of `(r, j)`, in units of `1 / M ^ 2`. -/
@[expose]
def rectAreaZ (r j : ℕ) : ℤ :=
  imax 0 (rectHiZ r j - rectLoZ r j) * imax 0 (rectHZ r j)

/-- Total covering area of row `r`, in units of `1 / M ^ 2`. -/
@[expose]
def rowSumZ (r : ℕ) : ℤ := (List.range NN).foldl (fun acc j => acc + rectAreaZ r j) 0

/-- Total covering area of the `7 * NN` rectangles, in units of `1 / M ^ 2`. -/
@[expose]
def nicheSumZ : ℤ := (List.range 7).foldl (fun acc r => acc + rowSumZ r) 0

/-! ### The two decidable numeric conclusions -/

/-- The closed numeric cap check: `2 * 28609 / 10000 ≤ capDoubledZ.lo / M`. -/
@[expose]
def capOK : Bool := 2 * 28609 * M ≤ 10000 * capDoubledZ.lo
/-- The closed numeric niche check: `nicheSumZ / M ^ 2 ≤ 3301 / 5000`. -/
@[expose]
def nicheOK : Bool := 5000 * nicheSumZ ≤ 3301 * M * M

/-- The niche check passes, by kernel reduction. -/
theorem nicheOK_true : nicheOK = true := by decide +kernel

/-- The cap check passes, by kernel reduction. -/
theorem capOK_true : capOK = true := by decide +kernel

end MovingSofa.GerverAreaCert

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Interval enclosures of the sine and cosine at scale `M`

The certificate evaluates the sine and the cosine by the interval Taylor recurrence
`GerverAreaCert.trigIter`, truncated at degree 41 and 40 and widened by one unit at scale
`M = 10 ^ 30`.  `trigZ_sound` is the soundness statement of that evaluator on `[0, 2]`: the
recurrence encloses the signed Taylor terms and their partial sums (`contains_trigIter`),
the alternating brackets of `Real.sin` and `Real.cos` control the truncation error by the
first omitted term, and `2 ^ 41 * 10 ^ 30 ≤ 41!` and `2 ^ 40 * 10 ^ 30 ≤ 40!` justify the
one-unit widening.
-/

/-! ### Sine and cosine enclosures -/

public section

namespace MovingSofa

open GerverAreaCert

/-- The integer term recurrence encloses the signed Taylor terms and their partial
sums.  Pure interval arithmetic: an induction on `n` using the `SI` soundness lemmas. -/
theorem contains_trigIter {z t : SI} {x : ℝ} (hz : SI.Contains z (x * x))
    (ht : SI.Contains t x) (n : ℕ) :
    SI.Contains (trigIter z t n).1
        ((-1 : ℝ) ^ n * x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) ∧
      SI.Contains (trigIter z t n).2.1
        ((-1 : ℝ) ^ n * x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) ∧
      SI.Contains (trigIter z t n).2.2.1
        (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)) ∧
      SI.Contains (trigIter z t n).2.2.2
        (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) := by
  induction n with
  | zero =>
    refine ⟨by simpa [trigIter] using ht, by simpa [trigIter] using SI.contains_one,
      by simpa [trigIter] using ht, ?_⟩
    simpa [trigIter] using SI.contains_one
  | succ n ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    have hfac1 : (Nat.factorial (2 * n + 1) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hfac2 : (Nat.factorial (2 * n) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hd1 : (0 : ℤ) < (((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) := by positivity
    have hd2 : (0 : ℤ) < (((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) := by positivity
    have hd1' : ((((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < ((((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) : ℝ) := by exact_mod_cast hd1
      exact ne_of_gt this
    have hd2' : ((((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < ((((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) : ℝ) := by exact_mod_cast hd2
      exact ne_of_gt this
    have e1 : (Nat.factorial (2 * (n + 1) + 1) : ℝ) =
        (Nat.factorial (2 * n + 1) : ℝ) * ((((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) : ℝ) := by
      have h : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by ring
      rw [h, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have e2 : (Nat.factorial (2 * (n + 1)) : ℝ) =
        (Nat.factorial (2 * n) : ℝ) * ((((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) : ℝ) := by
      have h : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [h, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have v1 : -((((-1 : ℝ) ^ n * x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) * (x * x)) /
          ((((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) : ℝ)) =
        (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1) + 1) /
          (Nat.factorial (2 * (n + 1) + 1) : ℝ) := by
      rw [e1, show x ^ (2 * (n + 1) + 1) = x ^ (2 * n + 1) * (x * x) by ring]
      field_simp
      ring
    have v2 : -((((-1 : ℝ) ^ n * x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) * (x * x)) /
          ((((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) : ℝ)) =
        (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) / (Nat.factorial (2 * (n + 1)) : ℝ) := by
      rw [e2, show x ^ (2 * (n + 1)) = x ^ (2 * n) * (x * x) by ring]
      field_simp
      ring
    have hs : SI.Contains
        (SI.neg (SI.divn (SI.mul (trigIter z t n).1 z) (((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ)))
        ((-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1) + 1) /
          (Nat.factorial (2 * (n + 1) + 1) : ℝ)) := by
      rw [← v1]
      exact SI.contains_neg (SI.contains_divn hd1 (SI.contains_mul ih1 hz))
    have hc : SI.Contains
        (SI.neg (SI.divn (SI.mul (trigIter z t n).2.1 z) (((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ)))
        ((-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) / (Nat.factorial (2 * (n + 1)) : ℝ)) := by
      rw [← v2]
      exact SI.contains_neg (SI.contains_divn hd2 (SI.contains_mul ih2 hz))
    refine ⟨hs, hc, ?_, ?_⟩
    · rw [Finset.sum_range_succ]
      exact SI.contains_add ih3 hs
    · rw [Finset.sum_range_succ]
      exact SI.contains_add ih4 hc

/-- The degree-41 sine Taylor polynomial overshoots by at most `1 / M` on `[0, 2]`. -/
private theorem sin_taylor_bracket {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    (∑ k ∈ Finset.range 21,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)) -
        1 / (M : ℝ) ≤ Real.sin x ∧
      Real.sin x ≤ ∑ k ∈ Finset.range 21,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ) := by
  obtain ⟨hlow, hhigh⟩ := Real.sin_mem_Icc_taylor_sums 10 hx0 (by push_cast; nlinarith)
  simp only [show (2 * 10 + 1 : ℕ) = 21 from rfl, show (2 * 10 : ℕ) = 20 from rfl] at hlow hhigh
  refine ⟨?_, hhigh⟩
  have hsplit : (∑ k ∈ Finset.range 21,
      (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ))
      = (∑ k ∈ Finset.range 20,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ))
        + x ^ 41 / (Nat.factorial 41 : ℝ) := by
    rw [show (21 : ℕ) = 20 + 1 from rfl, Finset.sum_range_succ]
    norm_num
  have htail : x ^ 41 / (Nat.factorial 41 : ℝ) ≤ 1 / (M : ℝ) := by
    have hMv : ((M : ℤ) : ℝ) = 10 ^ 30 := by norm_num [M]
    rw [hMv]
    calc x ^ 41 / (Nat.factorial 41 : ℝ) ≤ (2 : ℝ) ^ 41 / (Nat.factorial 41 : ℝ) := by gcongr
      _ ≤ 1 / 10 ^ 30 := by norm_num [Nat.factorial]
  rw [hsplit]
  linarith

/-- The degree-40 cosine Taylor polynomial overshoots by at most `1 / M` on `[0, 2]`. -/
private theorem cos_taylor_bracket {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    (∑ k ∈ Finset.range 21,
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) -
        1 / (M : ℝ) ≤ Real.cos x ∧
      Real.cos x ≤ ∑ k ∈ Finset.range 21,
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) := by
  obtain ⟨hlow, hhigh⟩ := Real.cos_mem_Icc_taylor_sums 10 hx0 (by push_cast; nlinarith)
  simp only [show (2 * 10 + 1 : ℕ) = 21 from rfl, show (2 * 10 : ℕ) = 20 from rfl] at hlow hhigh
  refine ⟨?_, hhigh⟩
  have hsplit : (∑ k ∈ Finset.range 21,
      (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))
      = (∑ k ∈ Finset.range 20,
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))
        + x ^ 40 / (Nat.factorial 40 : ℝ) := by
    rw [show (21 : ℕ) = 20 + 1 from rfl, Finset.sum_range_succ]
    norm_num
  have htail : x ^ 40 / (Nat.factorial 40 : ℝ) ≤ 1 / (M : ℝ) := by
    have hMv : ((M : ℤ) : ℝ) = 10 ^ 30 := by norm_num [M]
    rw [hMv]
    calc x ^ 40 / (Nat.factorial 40 : ℝ) ≤ (2 : ℝ) ^ 40 / (Nat.factorial 40 : ℝ) := by gcongr
      _ ≤ 1 / 10 ^ 30 := by norm_num [Nat.factorial]
  rw [hsplit]
  linarith

/-- Soundness of the executable sine/cosine enclosure on `[0, 2]`. -/
theorem trigZ_sound {t : SI} {x : ℝ} (ht : SI.Contains t x) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    SI.Contains (trigZ t).1 (Real.sin x) ∧ SI.Contains (trigZ t).2 (Real.cos x) := by
  have hM : (0 : ℝ) < (M : ℝ) := SI.Mpos
  have hMinv : (M : ℝ) * (1 / (M : ℝ)) = 1 := by field_simp
  have hwiden : ∀ (S : SI) (y v : ℝ), SI.Contains S v → v - 1 / (M : ℝ) ≤ y → y ≤ v →
      SI.Contains (⟨S.lo - 1, S.hi + 1⟩ : SI) y := by
    intro S y v hS h1 h2
    obtain ⟨ha, hb⟩ := hS
    have hlow : (M : ℝ) * v - 1 ≤ (M : ℝ) * y := by
      have h := mul_le_mul_of_nonneg_left h1 hM.le
      nlinarith [hMinv]
    have hhigh : (M : ℝ) * y ≤ (M : ℝ) * v := mul_le_mul_of_nonneg_left h2 hM.le
    refine ⟨?_, ?_⟩ <;> push_cast <;> linarith
  have h20 : (20 : ℕ) + 1 = 21 := by norm_num
  have hz : SI.Contains (SI.mul t t) (x * x) := SI.contains_mul ht ht
  obtain ⟨-, -, hS, hC⟩ := contains_trigIter hz ht 20
  rw [h20] at hS hC
  obtain ⟨hs1, hs2⟩ := sin_taylor_bracket hx0 hx2
  obtain ⟨hc1, hc2⟩ := cos_taylor_bracket hx0 hx2
  exact ⟨hwiden _ (Real.sin x) _ hS hs1 hs2, hwiden _ (Real.cos x) _ hC hc1 hc2⟩

end MovingSofa

end

end

end

end

end
