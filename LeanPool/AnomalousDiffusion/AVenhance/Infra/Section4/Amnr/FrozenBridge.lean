/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.Induction

/-! Infrastructure for the AMNR tensors: bridge from the recursion to the actual flow data. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- zero-level identity in primitive multiplier form. This is an
identity for the actual finite cutoff sum, not an assumption about A. -/
theorem Amnr_zero_factors {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (n : ℕ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) (i j k : Fin 2) :
    I.Amnr hΦ m κ n T 0 t x i j k =
      ∑ p : Fin 2,
        amnrSeedMultiplierA0Plus I hΦ m κ n j k i p (t, x) *
        AVenhance.spaceGrad (T t) x p := by
  classical
  let s := (I.hatXiML_support_finite hm t).toFinset
  have hz (l : ℤ) (hl : l ∉ s) : I.hatXiML m l t = 0 := by
    by_contra hne
    exact hl ((Set.Finite.mem_toFinset _).mpr hne)
  have hsum (f : ℤ → ℝ) : (∑' l, I.hatXiML m l t * f l) =
      ∑ l ∈ s, I.hatXiML m l t * f l :=
    tsum_eq_sum (fun l hl => by rw [hz l hl, zero_mul])
  unfold AVenhance.Ingredients.Amnr
  dsimp [amnrSeedMultiplierA0Plus, amnrSeedMultiplierGen,
    amnrFlowAverageA0Plus, amnrFlowAverageGen]
  rw [hsum]
  simp_rw [hsum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The primitive multiplier of the seed; it contains the memory
coefficient and both flow factors inside the cutoff average. -/
def amnrSeedMultiplier {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (n : ℕ) (j k i p : Fin 2) (z : AmnrSpace) : ℝ :=
  amnrSeedMultiplierA0Plus I hΦ m κ n j k i p z

/-- Coordinate derivative of one velocity component at a time-space point. -/
def amnrVelocityGradient (b : AmnrSpace → Vec 2) (i p : Fin 2) (z : AmnrSpace) : ℝ :=
  AVenhance.spaceGrad (fun y => b (z.1, y) i) z.2 p

/-- Coordinate derivative of the temperature at a time-space point. -/
def amnrTGradient (T : ℝ → Vec 2 → ℝ) (p : Fin 2) (z : AmnrSpace) : ℝ :=
  AVenhance.spaceGrad (T z.1) z.2 p

/-- Regularity of the actual recursion, derived before replacing its
partial time and spatial derivatives by the joint material direction. -/
theorem Amnr_contDiffOn_of_factors {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (n : ℕ) (T : ℝ → Vec 2 → ℝ)
    {U : Set AmnrSpace} (hU : IsOpen U) {N : ℕ} (j k : Fin 2)
    (hb : ContDiffOn ℝ N (fun z : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) U)
    (hB : ∀ i p, ContDiffOn ℝ N
      (amnrVelocityGradient (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) i p) U)
    (hf : ∀ i p, ContDiffOn ℝ N (amnrSeedMultiplier I hΦ m κ n j k i p) U)
    (hg : ∀ p, ContDiffOn ℝ N (amnrTGradient T p) U)
    {r a : ℕ} (hr : a + r ≤ N) (i : Fin 2) :
    ContDiffOn ℝ a (fun z : AmnrSpace => I.Amnr hΦ m κ n T r z.1 z.2 i j k) U := by
  induction r generalizing a i with
  | zero =>
    apply (ContDiffOn.sum (s := Finset.univ) (fun p _ =>
      ((hf i p).mul (hg p)).of_le (by exact_mod_cast (by omega : a ≤ N)))).congr
    intro z _
    exact Amnr_zero_factors I hΦ hm κ n T z.1 z.2 i j k
  | succ r ih =>
    have hprev := ih (a := a + 1) (by omega) i
    have hmat := (amnrWord_contDiffOn hU
      (hb.of_le (by exact_mod_cast (by omega : a + 1 ≤ N))) hprev [none]
      (n := a) (by simp)).sub (ContDiffOn.sum (s := Finset.univ) (fun p _ =>
        ((hB i p).of_le (by exact_mod_cast (by omega : a ≤ N))).mul
          (ih (a := a) (by omega) p)))
    apply hmat.congr
    intro z hz
    have hdiff := (hprev.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
    have hmaterial := amnrOp_material (b := fun z : AmnrSpace =>
      AVenhance.streamVel (Φ (m - 1)) z.1 z.2) hdiff
    rw [Amnr_succ]
    simp only [amnrWord]
    rw [hmaterial]
    rfl

/-- The higher mixed-derivative induction for the actual tensor.
Its inputs are bounds on the primitive seed multiplier, gradient of T and
velocity gradient, never bounds on A. The constant is uniform over r ≤ Jcut.
Discharging the primitive mixed bounds from the paper's preceding estimates
is a separate dependency from this contraction induction. -/
theorem Amnr_mixed_induction_of_factors {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (n : ℕ) (T : ℝ → Vec 2 → ℝ)
    {U : Set AmnrSpace} (hU : IsOpen U) {μ : Measure AmnrSpace}
    (hμ : μ ≪ volume.restrict U) (j k : Fin 2)
    (hb : ContDiffOn ℝ (AVenhance.Nstar β)
      (fun z : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) U)
    (hB : ∀ i p, ContDiffOn ℝ (AVenhance.Nstar β)
      (amnrVelocityGradient (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) i p) U)
    (hf : ∀ i p, ContDiffOn ℝ (AVenhance.Nstar β)
      (amnrSeedMultiplier I hΦ m κ n j k i p) U)
    (hg : ∀ p, ContDiffOn ℝ (AVenhance.Nstar β) (amnrTGradient T p) U)
    {S H F G Cb : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hF : 0 ≤ F) (hG : 0 ≤ G) (hCb : 0 ≤ Cb)
    (hfb : ∀ i p w, IsAmnrMixedWord w → amnrBudget w ≤ AVenhance.Nstar β → ∀ z ∈ U,
      |amnrWord (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) w
        (amnrSeedMultiplier I hΦ m κ n j k i p) z| ≤ F * amnrWeight S H w)
    (hgb : ∀ p w, IsAmnrMixedWord w → amnrBudget w ≤ AVenhance.Nstar β →
      eLpNorm (amnrWord (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) w
        (amnrTGradient T p)) 2 μ ≤ ENNReal.ofReal (G * amnrWeight S H w))
    (hBb : ∀ i p w, IsAmnrMixedWord w → amnrBudget w + 2 ≤ AVenhance.Nstar β → ∀ z ∈ U,
      |amnrWord (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) w
        (amnrVelocityGradient (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) i p) z| ≤
          Cb * H * amnrWeight S H w)
    (r : ℕ) (hr : r ≤ AVenhance.Jcut β) (α : List (Fin 2)) (ℓ : ℕ)
    (hbudget : α.length + 2 * ℓ ≤ AVenhance.Nstar β - 2 * r)
    (i : Fin 2) :
    eLpNorm (amnrWord (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2)
      (amnrMixedWord α ℓ) (fun z => I.Amnr hΦ m κ n T r z.1 z.2 i j k)) 2 μ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (AVenhance.Nstar β + 1) * F * G *
        (1 + 2 ^ (AVenhance.Nstar β + 1) * Cb) ^ AVenhance.Jcut β *
          S ^ α.length * H ^ (ℓ + r)) := by
  let b := fun z : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) z.1 z.2
  let A := fun (r : ℕ) (i : Fin 2) (z : AmnrSpace) => I.Amnr hΦ m κ n T r z.1 z.2 i j k
  have hzero (i : Fin 2) : Set.EqOn (A 0 i)
      (fun z => ∑ p, amnrSeedMultiplier I hΦ m κ n j k i p z * amnrTGradient T p z) U := by
    intro z _
    exact Amnr_zero_factors I hΦ hm κ n T z.1 z.2 i j k
  have hrec (q : ℕ) (hq : q < AVenhance.Nstar β) (i : Fin 2) :
      Set.EqOn (A (q + 1) i)
        (fun z => amnrOp b none (A q i) z - ∑ p, amnrVelocityGradient b i p z * A q p z) U := by
    intro z hz
    have hreg := Amnr_contDiffOn_of_factors I hΦ hm κ n T hU j k hb hB hf hg
      (r := q) (a := 1) (by omega) i
    have hdiff := (hreg.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
    have hmaterial := amnrOp_material (b := b) hdiff
    change I.Amnr hΦ m κ n T (q + 1) z.1 z.2 i j k = _
    rw [Amnr_succ]
    dsimp [A]
    rw [hmaterial]
    rfl
  have hJ : 2 * AVenhance.Jcut β ≤ AVenhance.Nstar β := by
    unfold AVenhance.Jcut
    omega
  have hNr : 2 * r ≤ AVenhance.Nstar β := (Nat.mul_le_mul_left 2 hr).trans hJ
  have hwb : amnrBudget (amnrMixedWord α ℓ) + 2 * r ≤ AVenhance.Nstar β := by
    rw [amnrMixedWord_budget]
    omega
  have hh := amnrRec_mixed_L2_le hU hμ hb hB hf hg hzero hrec hS hH hF hG hCb
    hfb hgb hBb r (amnrMixedWord α ℓ) (amnrMixedWord_mixed α ℓ) hwb i
  rw [amnrMixedWord_weight] at hh
  refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
  have hR : 1 ≤ 1 + (2 : ℝ) ^ (AVenhance.Nstar β + 1) * Cb := by
    have : 0 ≤ (2 : ℝ) ^ (AVenhance.Nstar β + 1) * Cb := by positivity
    linarith
  have hp := pow_le_pow_right₀ hR hr
  have hrest : 0 ≤ (2 : ℝ) ^ (AVenhance.Nstar β + 1) * F * G := by positivity
  have hweights : 0 ≤ H ^ r * (S ^ α.length * H ^ ℓ) := by positivity
  have hx := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hrest) hweights
  convert hx using 1 <;> rw [pow_add] <;> ring

end AVenhance.Infra.Section4
