/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerProof

@[expose] public section

/-! External derivative blocks with a fixed Sobolev index. -/

noncomputable section

namespace EulerH6Pressure

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerJetProductBounds EulerPressureJetIdentities EulerPressureSpatialRegularity
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]
variable {directions : Fin 4 → LiftTangent}

namespace SpatialJet

variable {period}

/-- Retain any prescribed lower order of an actual strong derivative jet. -/
def restrict {s : ℕ} {f : LiftL2 period} (J : EulerSpatialSobolevInverse.SpatialJet period
  directions s f)
    (q : ℕ) (hq : q ≤ s) : EulerSpatialSobolevInverse.SpatialJet period directions q f :=
  match q, J, hq with
  | 0, _, _ => .zero f
  | _ + 1, .zero _, h => False.elim (by omega)
  | q + 1, .succ df lower hd, h =>
      .succ df (fun i => restrict (lower i) q (by omega)) hd
termination_by s

theorem norm_unique {s : ℕ} {f g : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (K : EulerSpatialSobolevInverse.SpatialJet period directions s g) (hfg : f = g) :
    J.sobolevNorm = K.sobolevNorm := by
  rw [EulerSpatialSobolevInverse.SpatialJet.sobolevNorm_eq_sum_words,
    EulerSpatialSobolevInverse.SpatialJet.sobolevNorm_eq_sum_words]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro w _
  rw [EulerPressureJetIdentities.SpatialJet.word_unique J K hfg
    (by have := Finset.mem_range.mp hn; omega) (by have := Finset.mem_range.mp hn; omega) w]

/-- A derivative word carries the remaining genuine Sobolev jet. -/
def wordJet {q n : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions (q + n) f)
    (w : Fin n → Fin 4) :
    EulerSpatialSobolevInverse.SpatialJet period directions q (J.word w) :=
  match n, J, w with
  | 0, J, w => by simpa only [Nat.add_zero, EulerSpatialSobolevInverse.SpatialJet.word_zero] using J
  | n + 1, .succ _ lower _, w => by
      simpa only [EulerSpatialSobolevInverse.SpatialJet.word_succ] using
        wordJet (lower (w (Fin.last n))) (Fin.init w)
termination_by n

end SpatialJet

/-- The strong Sobolev norm of an L² field, set to zero off the Sobolev domain.
Every use below supplies an actual derivative jet, so its value is the genuine jet norm. -/
def sobolevSize (q : ℕ) (f : LiftL2 period) : ℝ := by
  classical
  exact if h : Nonempty (EulerSpatialSobolevInverse.SpatialJet period directions q f) then
    (Classical.choice h).sobolevNorm else 0

theorem sobolevSize_eq {q : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions q f) :
    sobolevSize period (directions := directions) q f = J.sobolevNorm := by
  unfold sobolevSize
  rw [dite_eq_left (show Nonempty (EulerSpatialSobolevInverse.SpatialJet period directions q f)
    from ⟨J⟩)]
  exact SpatialJet.norm_unique _ J rfl

/-- The external order-n block with a fixed base Sobolev index q. -/
def blockNorm {s : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f) (q n : ℕ) : ℝ :=
  Finset.sum (Finset.range (q + 1)) (fun r => levelNorm period J (n + r))

/-- Fixed-order coefficient multiplier blocks; the factor 2^q bounds the base Leibniz sums. -/
def coefficientBlock {s : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period directions s A) (q n : ℕ) : ℝ :=
  2 ^ q * Finset.sum (Finset.range (q + 1)) (fun r => boundLevel period K (n + r))

variable {period}

namespace CoefficientJet

/-- Retain the prescribed base order of an actual coefficient derivative tree. -/
def restrict {s : ℕ} {A : SmoothCoefficient period} (K : EulerSpatialSobolevInverse.CoefficientJet
  period directions s A)
    (q : ℕ) (hq : q ≤ s) : EulerSpatialSobolevInverse.CoefficientJet period directions q A :=
  match q, K, hq with
  | 0, _, _ => .zero A
  | _ + 1, .zero _, h => False.elim (by omega)
  | q + 1, .succ dA lower hd, h =>
      .succ dA (fun i => restrict (lower i) q (by omega)) hd
termination_by s

end CoefficientJet

namespace SpatialJet

/-- The fixed-order strong jet of any valid external derivative word. -/
def derivativeJet {s q n : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (w : Fin n → Fin 4) (h : n + q ≤ s) :
    EulerSpatialSobolevInverse.SpatialJet period directions q (J.word w) := by
  let K := restrict J (q + n) (by omega)
  have hw : K.word w = J.word w :=
    EulerPressureJetIdentities.SpatialJet.word_unique K J rfl (by omega) (by omega) w
  exact hw ▸ wordJet K w

end SpatialJet

theorem sobolevSize_nonneg (q : ℕ) (f : LiftL2 period) :
    0 ≤ sobolevSize period (directions := directions) q f := by
  classical
  unfold sobolevSize
  split
  · exact EulerSpatialSobolevInverse.SpatialJet.nonneg _
  · exact le_rfl

theorem sobolevSize_add_le {q : ℕ} {f g : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions q f)
    (K : EulerSpatialSobolevInverse.SpatialJet period directions q g) :
    sobolevSize period (directions := directions) q (f + g) ≤
      sobolevSize period (directions := directions) q f + sobolevSize period (directions :=
        directions) q g := by
  rw [sobolevSize_eq period (J.add K), sobolevSize_eq period J, sobolevSize_eq period K]
  exact J.add_norm_le K

theorem sobolevSize_sub_le {q : ℕ} {f g : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions q f)
    (K : EulerSpatialSobolevInverse.SpatialJet period directions q g) :
    sobolevSize period (directions := directions) q (f - g) ≤
      sobolevSize period (directions := directions) q f + sobolevSize period (directions :=
        directions) q g := by
  rw [sobolevSize_eq period (J.sub K), sobolevSize_eq period J, sobolevSize_eq period K]
  exact J.sub_norm_le K

theorem blockNorm_nonneg {s q n : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f) : 0 ≤ blockNorm period J q n
      :=
  Finset.sum_nonneg (fun _ _ => levelNorm_nonneg J)

omit [Fact (0 < period)] in
theorem coefficientBlock_nonneg {s q n : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A) :
    0 ≤ coefficientBlock period K q n := by
  unfold coefficientBlock
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => boundLevel_nonneg K))

theorem blockNorm_truncate {s q n : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions (s + 1) f) (h : n + q ≤ s) :
    blockNorm period J.truncate q n = blockNorm period J q n := by
  apply Finset.sum_congr rfl
  intro r hr
  exact levelNorm_truncate J (by have := Finset.mem_range.mp hr; omega)

omit [Fact (0 < period)] in
theorem coefficientBlock_truncate {s q n : ℕ} {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions (s + 1) A) (h : n + q ≤ s) :
    coefficientBlock period K.truncate q n = coefficientBlock period K q n := by
  unfold coefficientBlock
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  exact boundLevel_truncate K (by have := Finset.mem_range.mp hr; omega)

theorem blockNorm_succ {s : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions (s + 1) f) (q n : ℕ) :
    blockNorm period J q (n + 1) =
      match J with
      | .succ _ lower _ => ∑ i, blockNorm period (lower i) q n := by
  cases J with
  | succ df lower hd =>
    unfold blockNorm
    have hi (r : ℕ) : n + 1 + r = (n + r) + 1 := by omega
    simp_rw [hi, levelNorm]
    rw [Finset.sum_comm]

omit [Fact (0 < period)] in
theorem coefficientBlock_succ {s : ℕ} {A : SmoothCoefficient period}
    (dA : Fin 4 → SmoothCoefficient period)
    (lower : ∀ i, EulerSpatialSobolevInverse.CoefficientJet period directions s (dA i))
    (hd : ∀ i x, (dA i).coefficient x = EulerTransportDerivatives.fieldDerivative period
      (directions i) A.coefficient x)
    (q n : ℕ) :
    coefficientBlock period (EulerSpatialSobolevInverse.CoefficientJet.succ (A := A) dA lower hd) q
      (n + 1) = ∑ i, coefficientBlock period (lower i) q n := by
  unfold coefficientBlock
  have hi (r : ℕ) : n + 1 + r = (n + r) + 1 := by omega
  simp_rw [hi, boundLevel]
  rw [Finset.sum_comm, Finset.mul_sum]

theorem blockNorm_zero_eq_size {s q : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f) (h : q ≤ s) :
    blockNorm period J q 0 = sobolevSize period (directions := directions) q f := by
  rw [sobolevSize_eq period (SpatialJet.restrict J q h),
    EulerSpatialSobolevInverse.SpatialJet.sobolevNorm_eq_sum_words]
  unfold blockNorm
  apply Finset.sum_congr rfl
  intro r hr
  rw [Nat.zero_add, levelNorm_eq_words]
  apply Finset.sum_congr rfl
  intro w _
  rw [EulerPressureJetIdentities.SpatialJet.word_unique J (SpatialJet.restrict J q h)
    rfl (by have := Finset.mem_range.mp hr; omega) (by have := Finset.mem_range.mp hr; omega) w]

/-- A fixed-index block is exactly the sum of the Sobolev norms of the external words. -/
theorem blockNorm_eq_word_sizes {s q n : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f) (h : n + q ≤ s) :
    blockNorm period J q n = ∑ w : Fin n → Fin 4,
      sobolevSize period (directions := directions) q (J.word w) := by
  induction n generalizing s f with
  | zero =>
    rw [blockNorm_zero_eq_size J (by omega)]
    simp
  | succ n ih =>
    cases J with
    | zero => omega
    | succ df lower hd =>
      have heq : (∑ w : Fin (n + 1) → Fin 4, sobolevSize period (directions := directions) q
          ((EulerSpatialSobolevInverse.SpatialJet.succ df lower hd).word w)) =
          ∑ v : Fin 4 × (Fin n → Fin 4), sobolevSize period (directions := directions) q
            ((lower v.1).word v.2) :=
        Fintype.sum_equiv (EulerSpatialSobolevInverse.SpatialJet.wordSnocEquiv n)
          (fun w => sobolevSize period (directions := directions) q
            ((EulerSpatialSobolevInverse.SpatialJet.succ df lower hd).word w))
          (fun v => sobolevSize period (directions := directions) q ((lower v.1).word v.2))
          (fun _ => by rw [EulerSpatialSobolevInverse.SpatialJet.word_succ]; rfl)
      rw [Fintype.sum_prod_type] at heq
      rw [blockNorm_succ, heq]
      exact Finset.sum_congr rfl (fun i _ => ih (lower i) (by omega))

/-- The nonnegative lower-triangular convolution is bounded by the full product of sums. -/
theorem triangle_sum_le_product (q : ℕ) (A B : ℕ → ℝ)
    (hA : ∀ n, 0 ≤ A n) (hB : ∀ n, 0 ≤ B n) :
    (∑ r ∈ Finset.range (q + 1), ∑ l ∈ Finset.range (r + 1), A l * B (r - l)) ≤
      (∑ l ∈ Finset.range (q + 1), A l) * (∑ j ∈ Finset.range (q + 1), B j) := by
  let e : (Σ _r : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2, p.1 - p.2)
  have hi : Set.InjOn e ((Finset.range (q + 1)).sigma (fun r => Finset.range (r + 1))) := by
    rintro ⟨r, l⟩ hx ⟨r', l'⟩ hy he
    have hx' := Finset.mem_sigma.mp hx
    have hy' := Finset.mem_sigma.mp hy
    have hl := Finset.mem_range.mp hx'.2
    have hl' := Finset.mem_range.mp hy'.2
    change l < r + 1 at hl
    change l' < r' + 1 at hl'
    have heq : l = l' ∧ r - l = r' - l' := Prod.mk.inj he
    have hll : l = l' := heq.1
    have hrr : r = r' := by omega
    subst l'
    subst r'
    rfl
  have himg : Finset.image e ((Finset.range (q + 1)).sigma (fun r => Finset.range (r + 1))) ⊆
      (Finset.range (q + 1)) ×ˢ (Finset.range (q + 1)) := by
    intro p hp
    obtain ⟨⟨r, l⟩, hx, rfl⟩ := Finset.mem_image.mp hp
    have hx' := Finset.mem_sigma.mp hx
    have hr := Finset.mem_range.mp hx'.1
    have hl := Finset.mem_range.mp hx'.2
    change r < q + 1 at hr
    change l < r + 1 at hl
    simp only [e, Finset.mem_product, Finset.mem_range]
    omega
  calc
    _ = ∑ p ∈ (Finset.range (q + 1)).sigma (fun r => Finset.range (r + 1)),
        A p.2 * B (p.1 - p.2) := Finset.sum_sigma' _ _ _
    _ ≤ ∑ p ∈ (Finset.range (q + 1)) ×ˢ (Finset.range (q + 1)), A p.1 * B p.2 :=
      Finset.sum_le_sum_of_injOn e hi himg (fun _ _ => le_rfl)
        (fun p _ _ => mul_nonneg (hA p.1) (hB p.2))
    _ = _ := by rw [Finset.sum_product, ← Finset.sum_mul_sum]

/-- The fixed base-order Leibniz estimate has a constant independent of all external orders. -/
theorem base_convolution_bound (q : ℕ) (A B : ℕ → ℝ)
    (hA : ∀ n, 0 ≤ A n) (hB : ∀ n, 0 ≤ B n) :
    (∑ r ∈ Finset.range (q + 1), leibnizConvolution A B r) ≤
      (2 : ℝ) ^ q * (∑ l ∈ Finset.range (q + 1), A l) *
        (∑ j ∈ Finset.range (q + 1), B j) := by
  calc
    _ ≤ ∑ r ∈ Finset.range (q + 1), ∑ l ∈ Finset.range (r + 1),
        (2 : ℝ) ^ q * (A l * B (r - l)) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro l _
      have hc : (r.choose l : ℝ) ≤ (2 : ℝ) ^ q := by
        have hcr : (r.choose l : ℝ) ≤ (2 : ℝ) ^ r := by exact_mod_cast Nat.choose_le_two_pow r l
        exact hcr.trans (pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hr; omega))
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (mul_nonneg (hA l) (hB (r - l)))
    _ = (2 : ℝ) ^ q * (∑ r ∈ Finset.range (q + 1), ∑ l ∈ Finset.range (r + 1),
        A l * B (r - l)) := by simp only [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ q * ((∑ l ∈ Finset.range (q + 1), A l) *
        (∑ j ∈ Finset.range (q + 1), B j)) :=
      mul_le_mul_of_nonneg_left (triangle_sum_le_product q A B hA hB) (by positivity)
    _ = _ := by ring

theorem blockNorm_add_le {s q n : ℕ} {f g : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (K : EulerSpatialSobolevInverse.SpatialJet period directions s g) :
    blockNorm period (J.add K) q n ≤ blockNorm period J q n + blockNorm period K q n := by
  unfold blockNorm
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun r _ => levelNorm_add_le J K)

/-- Multiplication is bounded at the fixed base Sobolev order q. -/
theorem multiply_base_block_bound {s q : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f) (h : q ≤ s) :
    blockNorm period (EulerSpatialSobolevInverse.SpatialJet.multiply K J) q 0 ≤
      coefficientBlock period K q 0 * blockNorm period J q 0 := by
  unfold blockNorm coefficientBlock
  simp only [Nat.zero_add]
  calc
    _ ≤ ∑ r ∈ Finset.range (q + 1), leibnizConvolution (boundLevel period K) (levelNorm period J) r
      :=
      Finset.sum_le_sum (fun r hr => multiply_levelNorm_le K J (by have := Finset.mem_range.mp hr;
        omega))
    _ ≤ _ := base_convolution_bound q (boundLevel period K) (levelNorm period J)
      (fun _ => boundLevel_nonneg K) (fun _ => levelNorm_nonneg J)

/-- Leibniz in external derivative order, with all fixed Sobolev derivatives inside the blocks. -/
theorem multiply_blockNorm_bound {s q n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f) (h : n + q ≤ s) :
    blockNorm period (EulerSpatialSobolevInverse.SpatialJet.multiply K J) q n ≤
      leibnizConvolution (coefficientBlock period K q) (blockNorm period J q) n := by
  induction n generalizing s A f with
  | zero =>
    simpa [leibnizConvolution] using multiply_base_block_bound K J (by omega : q ≤ s)
  | succ n ih =>
    cases s with
    | zero => omega
    | succ s =>
      cases K with
      | succ dA lowerA hA =>
        cases J with
        | succ df lowerF hF =>
          let K := EulerSpatialSobolevInverse.CoefficientJet.succ dA lowerA hA
          let J := EulerSpatialSobolevInverse.SpatialJet.succ (f := f) df lowerF hF
          have ht : ∀ i,
              blockNorm period ((EulerSpatialSobolevInverse.SpatialJet.multiply K.truncate (lowerF
                i)).add
                (EulerSpatialSobolevInverse.SpatialJet.multiply (lowerA i) J.truncate)) q n ≤
              leibnizConvolution (coefficientBlock period K q) (blockNorm period (lowerF i) q) n +
                leibnizConvolution (coefficientBlock period (lowerA i) q) (blockNorm period J q) n
                  := by
            intro i
            have hleft := ih K.truncate (lowerF i) (by omega : n + q ≤ s)
            have hright := ih (lowerA i) J.truncate (by omega : n + q ≤ s)
            have heqL : leibnizConvolution (coefficientBlock period K.truncate q)
                (blockNorm period (lowerF i) q) n =
                leibnizConvolution (coefficientBlock period K q) (blockNorm period (lowerF i) q) n
                  :=
              leibnizConvolution_congr _ _ _ _ n
                (fun l hl => coefficientBlock_truncate K (by omega)) (fun _ _ => rfl)
            have heqR : leibnizConvolution (coefficientBlock period (lowerA i) q)
                (blockNorm period J.truncate q) n =
                leibnizConvolution (coefficientBlock period (lowerA i) q) (blockNorm period J q) n
                  :=
              leibnizConvolution_congr _ _ _ _ n
                (fun _ _ => rfl) (fun l hl => blockNorm_truncate J (by omega))
            rw [heqL] at hleft
            rw [heqR] at hright
            exact (blockNorm_add_le _ _).trans (add_le_add hleft hright)
          rw [EulerSpatialSobolevInverse.SpatialJet.multiply, blockNorm_succ]
          calc
            _ ≤ ∑ i, (leibnizConvolution (coefficientBlock period K q) (blockNorm period (lowerF i)
              q) n +
                leibnizConvolution (coefficientBlock period (lowerA i) q) (blockNorm period J q) n)
                  :=
              Finset.sum_le_sum (fun i _ => ht i)
            _ = leibnizConvolution (coefficientBlock period K q)
                  (fun l => ∑ i, blockNorm period (lowerF i) q l) n +
                leibnizConvolution (fun l => ∑ i, coefficientBlock period (lowerA i) q l)
                  (blockNorm period J q) n := by
              rw [Finset.sum_add_distrib, sum_leibnizConvolution_right, sum_leibnizConvolution_left]
            _ = leibnizConvolution (coefficientBlock period K q) (blockNorm period J q) (n + 1) :=
              by
              rw [leibnizConvolution_succ]
              congr 2
              · funext l; exact (blockNorm_succ J q l).symm
              · funext l; exact (coefficientBlock_succ dA lowerA hA q l).symm

end EulerH6Pressure
