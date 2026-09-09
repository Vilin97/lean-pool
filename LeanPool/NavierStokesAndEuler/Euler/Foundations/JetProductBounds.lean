/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SpatialSobolevInverse
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PressureJetIdentities

/-! Sharp order-by-order Leibniz bounds for actual cylinder Sobolev jets. -/

@[expose] public section

noncomputable section

namespace EulerJetProductBounds

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerPressureSpatialRegularity EulerSpatialSobolevInverse
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The sum of the L² norms of all actual derivative words of one order. -/
def levelNorm {directions : Fin 4 → LiftTangent} {s : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (n : ℕ) : ℝ :=
  match n, J with
  | 0, _ => ‖f‖
  | _ + 1, .zero _ => 0
  | n + 1, .succ _ lower _ => ∑ i, levelNorm (lower i) n
termination_by s

/-- The sum of the uniform bounds of all coefficient derivatives of one order. -/
def boundLevel {directions : Fin 4 → LiftTangent} {s : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period directions s A) (n : ℕ) : ℝ :=
  match n, K with
  | 0, _ => A.bound
  | _ + 1, .zero _ => 0
  | n + 1, .succ _ lower _ => ∑ i, boundLevel (lower i) n
termination_by s

variable {period} {directions : Fin 4 → LiftTangent}

theorem levelNorm_nonneg {s n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions s f) :
    0 ≤ levelNorm period J n := by
  induction J generalizing n with
  | zero => cases n <;> simp [levelNorm]
  | succ df lower hd ih =>
    cases n with
    | zero => rw [levelNorm]; exact norm_nonneg _
    | succ n =>
      rw [levelNorm]
      exact Finset.sum_nonneg fun i _ => ih i

omit [Fact (0 < period)] in
theorem boundLevel_nonneg {s n : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period directions s A) : 0 ≤ boundLevel period K n := by
  induction K generalizing n with
  | zero => cases n <;> simp [boundLevel]
  | succ dA lower hd ih =>
    cases n with
    | zero => rw [boundLevel]; exact NNReal.coe_nonneg _
    | succ n =>
      rw [boundLevel]
      exact Finset.sum_nonneg fun i _ => ih i

/-- The recursive level norm is exactly the finite sum over coordinate words. -/
theorem levelNorm_eq_words {s n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions s f) :
    levelNorm period J n = ∑ w : Fin n → Fin 4, ‖J.word w‖ := by
  induction J generalizing n with
  | zero f => cases n <;> simp [levelNorm, SpatialJet.word]
  | succ df lower hd ih =>
    cases n with
    | zero => simp [levelNorm]
    | succ n =>
      rw [levelNorm, SpatialJet.sum_word_succ]
      exact Finset.sum_congr rfl fun i _ => ih i

theorem levelNorm_truncate {s n : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions (s + 1) f) (hn : n ≤ s) :
    levelNorm period J.truncate n = levelNorm period J n := by
  induction s generalizing f n with
  | zero =>
    have hn0 : n = 0 := by omega
    subst n
    simp only [levelNorm]
  | succ s ih =>
    cases n with
    | zero => simp only [levelNorm]
    | succ n =>
      cases J with
      | succ df lower hd =>
        simp only [SpatialJet.truncate, levelNorm]
        exact Finset.sum_congr rfl fun i _ => ih (lower i) (by omega)

omit [Fact (0 < period)] in
theorem boundLevel_truncate {s n : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period directions (s + 1) A) (hn : n ≤ s) :
    boundLevel period K.truncate n = boundLevel period K n := by
  induction s generalizing A n with
  | zero =>
    have hn0 : n = 0 := by omega
    subst n
    simp only [boundLevel]
  | succ s ih =>
    cases n with
    | zero => simp only [boundLevel]
    | succ n =>
      cases K with
      | succ dA lower hd =>
        simp only [CoefficientJet.truncate, boundLevel]
        exact Finset.sum_congr rfl fun i _ => ih (lower i) (by omega)

theorem levelNorm_add_le {s n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions s f) (K : SpatialJet period directions s g) :
    levelNorm period (J.add K) n ≤ levelNorm period J n + levelNorm period K n := by
  induction s generalizing f g n with
  | zero => cases J; cases K; cases n <;> simp [SpatialJet.add, levelNorm, norm_add_le]
  | succ s ih =>
    cases J with
    | succ df lower hd =>
      cases K with
      | succ dg lowerG hG =>
        cases n with
        | zero => simp only [levelNorm]; exact norm_add_le _ _
        | succ n =>
          rw [SpatialJet.add, levelNorm, levelNorm, levelNorm, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun i _ => ih (lower i) (lowerG i)

/-- Binomial convolution of nonnegative derivative-order bounds. -/
def leibnizConvolution (A B : ℕ → ℝ) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (n + 1)) (fun l => (n.choose l : ℝ) * A l * B (n - l))

theorem leibnizConvolution_succ (A B : ℕ → ℝ) (n : ℕ) :
    leibnizConvolution A B (n + 1) =
      leibnizConvolution A (fun k => B (k + 1)) n +
      leibnizConvolution (fun k => A (k + 1)) B n := by
  simp only [leibnizConvolution, mul_assoc]
  rw [Finset.sum_choose_succ_mul (fun l r => A l * B r) n]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have hln : l ≤ n := by simpa using Finset.mem_range.mp hl
  rw [show n + 1 - l = n - l + 1 by omega]

theorem leibnizConvolution_congr (A B C D : ℕ → ℝ) (n : ℕ)
    (hA : ∀ l ≤ n, A l = C l) (hB : ∀ l ≤ n, B l = D l) :
    leibnizConvolution A B n = leibnizConvolution C D n := by
  apply Finset.sum_congr rfl
  intro l hl
  have hl : l ≤ n := by simpa using Finset.mem_range.mp hl
  rw [hA l hl, hB (n - l) (by omega)]

theorem sum_leibnizConvolution_right (A : ℕ → ℝ) (B : Fin 4 → ℕ → ℝ) (n : ℕ) :
    (∑ i, leibnizConvolution A (B i) n) = leibnizConvolution A (fun l => ∑ i, B i l) n := by
  simp only [leibnizConvolution]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => (Finset.mul_sum ..).symm

theorem sum_leibnizConvolution_left (A : Fin 4 → ℕ → ℝ) (B : ℕ → ℝ) (n : ℕ) :
    (∑ i, leibnizConvolution (A i) B n) = leibnizConvolution (fun l => ∑ i, A i l) B n := by
  simp only [leibnizConvolution]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- Sharp binomial Leibniz estimate for the actual product jet, at every finite derivative order. -/
theorem multiply_levelNorm_le {s n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (hn : n ≤ s) :
    levelNorm period (SpatialJet.multiply K J) n ≤
      leibnizConvolution (boundLevel period K) (levelNorm period J) n := by
  induction n generalizing s A f with
  | zero =>
    simpa [levelNorm, leibnizConvolution, boundLevel] using A.operator_norm f
  | succ n ih =>
    cases s with
    | zero => omega
    | succ s =>
      cases K with
      | succ dA lowerA hA =>
        cases J with
        | succ df lowerF hF =>
          let K := CoefficientJet.succ dA lowerA hA
          let J := SpatialJet.succ df lowerF hF
          have hterm : ∀ i,
              levelNorm period ((SpatialJet.multiply K.truncate (lowerF i)).add
                (SpatialJet.multiply (lowerA i) J.truncate)) n ≤
              leibnizConvolution (boundLevel period K) (levelNorm period (lowerF i)) n +
              leibnizConvolution (boundLevel period (lowerA i)) (levelNorm period J) n := by
            intro i
            have hleft := ih K.truncate (lowerF i) (by omega : n ≤ s)
            have hright := ih (lowerA i) J.truncate (by omega : n ≤ s)
            have heqL : leibnizConvolution (boundLevel period K.truncate)
                (levelNorm period (lowerF i)) n =
                leibnizConvolution (boundLevel period K) (levelNorm period (lowerF i)) n :=
              leibnizConvolution_congr _ _ _ _ n
                (fun l hl => boundLevel_truncate K (by omega)) (fun _ _ => rfl)
            have heqR : leibnizConvolution (boundLevel period (lowerA i))
                (levelNorm period J.truncate) n =
                leibnizConvolution (boundLevel period (lowerA i)) (levelNorm period J) n :=
              leibnizConvolution_congr _ _ _ _ n
                (fun _ _ => rfl) (fun l hl => levelNorm_truncate J (by omega))
            rw [heqL] at hleft
            rw [heqR] at hright
            exact (levelNorm_add_le _ _).trans (add_le_add hleft hright)
          rw [SpatialJet.multiply, levelNorm]
          calc
            _ ≤ ∑ i, (leibnizConvolution (boundLevel period K) (levelNorm period (lowerF i)) n +
                leibnizConvolution (boundLevel period (lowerA i)) (levelNorm period J) n) :=
              Finset.sum_le_sum fun i _ => hterm i
            _ = leibnizConvolution (boundLevel period K)
                  (fun l => ∑ i, levelNorm period (lowerF i) l) n +
                leibnizConvolution (fun l => ∑ i, boundLevel period (lowerA i) l)
                  (levelNorm period J) n := by
              rw [Finset.sum_add_distrib, sum_leibnizConvolution_right, sum_leibnizConvolution_left]
            _ = leibnizConvolution (boundLevel period K) (levelNorm period J) (n + 1) := by
              rw [leibnizConvolution_succ]
              congr 2 <;> funext l <;> simp only [K, J, levelNorm, boundLevel]

theorem word_add {s n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions s f) (K : SpatialJet period directions s g)
    (w : Fin n → Fin 4) : (J.add K).word w = J.word w + K.word w := by
  induction s generalizing f g n with
  | zero => cases J; cases K; cases n <;> simp [SpatialJet.add, SpatialJet.word]
  | succ s ih =>
    cases J with
    | succ df lower hd =>
      cases K with
      | succ dg lowerG hG =>
        cases n with
        | zero => simp
        | succ n =>
          simp only [SpatialJet.add, SpatialJet.word_succ]
          exact ih (lower _) (lowerG _) _

/-- Binomial derivative convolution with its undifferentiated-coefficient term removed. -/
def commutatorConvolution (A B : ℕ → ℝ) (n : ℕ) : ℝ :=
  leibnizConvolution A B n - A 0 * B n

theorem commutatorConvolution_eq_sum (A B : ℕ → ℝ) (n : ℕ) :
    commutatorConvolution A B n =
      ∑ l ∈ Finset.range n, (n.choose (l + 1) : ℝ) * A (l + 1) * B (n - (l + 1)) := by
  rw [commutatorConvolution, leibnizConvolution, Finset.sum_range_succ']
  simp

theorem commutatorConvolution_congr (A B C D : ℕ → ℝ) (n : ℕ)
    (hA : ∀ l ≤ n, A l = C l) (hB : ∀ l ≤ n, B l = D l) :
    commutatorConvolution A B n = commutatorConvolution C D n := by
  rw [commutatorConvolution, commutatorConvolution, leibnizConvolution_congr A B C D n hA hB,
    hA 0 (Nat.zero_le n), hB n le_rfl]

theorem commutatorConvolution_succ (A B : ℕ → ℝ) (n : ℕ) :
    commutatorConvolution A B (n + 1) =
      commutatorConvolution A (fun k => B (k + 1)) n +
      leibnizConvolution (fun k => A (k + 1)) B n := by
  rw [commutatorConvolution, leibnizConvolution_succ, commutatorConvolution]
  ring

theorem sum_commutatorConvolution_right (A : ℕ → ℝ) (B : Fin 4 → ℕ → ℝ) (n : ℕ) :
    (∑ i, commutatorConvolution A (B i) n) =
      commutatorConvolution A (fun l => ∑ i, B i l) n := by
  simp only [commutatorConvolution]
  rw [Finset.sum_sub_distrib, sum_leibnizConvolution_right, Finset.mul_sum]

/-- The actual product commutator at one derivative order, summed over coordinate words. -/
def commutatorLevel {s : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin 4, ‖(SpatialJet.multiply K J).word w - A.operator (J.word w)‖

theorem sum_word_snoc (n : ℕ) (F : (Fin (n + 1) → Fin 4) → ℝ) :
    (∑ w, F w) = ∑ i, ∑ w : Fin n → Fin 4, F (Fin.snoc w i) := by
  calc
    _ = ∑ v : Fin 4 × (Fin n → Fin 4), F ((SpatialJet.wordSnocEquiv n).symm v) :=
      ((SpatialJet.wordSnocEquiv n).symm.sum_comp F).symm
    _ = _ := Fintype.sum_prod_type _

theorem multiply_word_snoc {s n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (dA : Fin 4 → SmoothCoefficient period)
    (lowerA : ∀ i, CoefficientJet period directions s (dA i))
    (hA : ∀ i x, (dA i).coefficient x = EulerTransportDerivatives.fieldDerivative period
      (directions i) A.coefficient x)
    (df : Fin 4 → LiftL2 period) (lowerF : ∀ i, SpatialJet period directions s (df i))
    (hF : ∀ i, HasDerivAt (fun t => translation period (translationPath period (directions i) t) f)
      (df i) 0) (i : Fin 4) (w : Fin n → Fin 4) :
    (SpatialJet.multiply (CoefficientJet.succ dA lowerA hA) (SpatialJet.succ df lowerF hF)).word
        (Fin.snoc w i) =
      (SpatialJet.multiply (CoefficientJet.succ dA lowerA hA).truncate (lowerF i)).word w +
      (SpatialJet.multiply (lowerA i) (SpatialJet.succ df lowerF hF).truncate).word w := by
  rw [SpatialJet.multiply, SpatialJet.word_succ]
  simp only [Fin.init_snoc, word_add, Fin.snoc, Fin.val_last, cast_eq]
  generalize hval : (if h : n < n then w ((Fin.last n).castLT h) else i) = j
  have hj : j = i := hval.symm.trans (dite_eq_right (Nat.lt_irrefl n))
  clear hval
  subst j
  rfl

theorem commutatorLevel_succ_le {s n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (dA : Fin 4 → SmoothCoefficient period)
    (lowerA : ∀ i, CoefficientJet period directions s (dA i))
    (hA : ∀ i x, (dA i).coefficient x = EulerTransportDerivatives.fieldDerivative period
      (directions i) A.coefficient x)
    (df : Fin 4 → LiftL2 period) (lowerF : ∀ i, SpatialJet period directions s (df i))
    (hF : ∀ i, HasDerivAt (fun t => translation period (translationPath period (directions i) t) f)
      (df i) 0) :
    commutatorLevel (CoefficientJet.succ dA lowerA hA) (SpatialJet.succ df lowerF hF) (n + 1) ≤
      ∑ i, (commutatorLevel (CoefficientJet.succ dA lowerA hA).truncate (lowerF i) n +
        levelNorm period (SpatialJet.multiply (lowerA i) (SpatialJet.succ df lowerF hF).truncate)
            n) := by
  rw [commutatorLevel, sum_word_snoc]
  apply Finset.sum_le_sum
  intro i _
  rw [commutatorLevel, levelNorm_eq_words, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  rw [multiply_word_snoc]
  simp only [SpatialJet.word_succ, Fin.init_snoc]
  simp only [Fin.snoc, Fin.val_last, cast_eq]
  generalize hval : (if h : n < n then w ((Fin.last n).castLT h) else i) = j
  have hj : j = i := hval.symm.trans (dite_eq_right (Nat.lt_irrefl n))
  clear hval
  subst j
  have heq : (SpatialJet.multiply (CoefficientJet.succ dA lowerA hA).truncate (lowerF i)).word w +
      (SpatialJet.multiply (lowerA i) (SpatialJet.succ df lowerF hF).truncate).word w -
      A.operator ((lowerF i).word w) =
      ((SpatialJet.multiply (CoefficientJet.succ dA lowerA hA).truncate (lowerF i)).word w -
        A.operator ((lowerF i).word w)) +
        (SpatialJet.multiply (lowerA i) (SpatialJet.succ df lowerF hF).truncate).word w := by abel
  rw [heq]
  exact norm_add_le _ _
/-- Sharp all-order commutator estimate, with only positive coefficient derivative orders. -/
theorem commutatorLevel_le {s n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (hn : n ≤ s) :
    commutatorLevel K J n ≤
      commutatorConvolution (boundLevel period K) (levelNorm period J) n := by
  induction n generalizing s A f with
  | zero => simp [commutatorLevel, commutatorConvolution_eq_sum]
  | succ n ih =>
    cases s with
    | zero => omega
    | succ s =>
      cases K with
      | succ dA lowerA hA =>
        cases J with
        | succ df lowerF hF =>
          let K := CoefficientJet.succ dA lowerA hA
          let J := SpatialJet.succ df lowerF hF
          have hterm : ∀ i,
              commutatorLevel K.truncate (lowerF i) n +
                levelNorm period (SpatialJet.multiply (lowerA i) J.truncate) n ≤
              commutatorConvolution (boundLevel period K) (levelNorm period (lowerF i)) n +
                leibnizConvolution (boundLevel period (lowerA i)) (levelNorm period J) n := by
            intro i
            have hleft := ih K.truncate (lowerF i) (by omega : n ≤ s)
            have hright := multiply_levelNorm_le (lowerA i) J.truncate (by omega : n ≤ s)
            have heqL := commutatorConvolution_congr (boundLevel period K.truncate)
              (levelNorm period (lowerF i)) (boundLevel period K) (levelNorm period (lowerF i)) n
              (fun l hl => boundLevel_truncate K (by omega)) (fun _ _ => rfl)
            have heqR := leibnizConvolution_congr (boundLevel period (lowerA i))
              (levelNorm period J.truncate) (boundLevel period (lowerA i)) (levelNorm period J) n
              (fun _ _ => rfl) (fun l hl => levelNorm_truncate J (by omega))
            rw [heqL] at hleft
            rw [heqR] at hright
            exact add_le_add hleft hright
          calc
            _ ≤ ∑ i, (commutatorLevel K.truncate (lowerF i) n +
                levelNorm period (SpatialJet.multiply (lowerA i) J.truncate) n) :=
              commutatorLevel_succ_le dA lowerA hA df lowerF hF
            _ ≤ ∑ i, (commutatorConvolution (boundLevel period K) (levelNorm period (lowerF i)) n +
                leibnizConvolution (boundLevel period (lowerA i)) (levelNorm period J) n) :=
              Finset.sum_le_sum fun i _ => hterm i
            _ = commutatorConvolution (boundLevel period K)
                  (fun l => ∑ i, levelNorm period (lowerF i) l) n +
                leibnizConvolution (fun l => ∑ i, boundLevel period (lowerA i) l)
                  (levelNorm period J) n := by
              rw [Finset.sum_add_distrib, sum_commutatorConvolution_right,
                  sum_leibnizConvolution_left]
            _ = commutatorConvolution (boundLevel period K) (levelNorm period J) (n + 1) := by
              rw [commutatorConvolution_succ]
              congr 2 <;> funext l <;> simp only [K, J, levelNorm, boundLevel]

/-- The all-order pressure recurrence for actual L² derivative words, with the entire
positive-order coefficient convolution derived from the product rule. -/
theorem pressure_level_recurrence {s n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (hn : n ≤ s) :
    levelNorm period (J.solvePressure K κ m c hc hpos) n ≤ c⁻¹ *
      (levelNorm period J n + ∑ l ∈ Finset.range n,
        (n.choose (l + 1) : ℝ) * boundLevel period K (l + 1) *
          levelNorm period (J.solvePressure K κ m c hc hpos) (n - (l + 1))) := by
  let P := J.solvePressure K κ m c hc hpos
  have hw := fun w : Fin n → Fin 4 =>
    EulerPressureJetIdentities.SpatialJet.pressure_word_norm_le K J κ m c hc hpos hn w
  calc
    _ = ∑ w : Fin n → Fin 4, ‖P.word w‖ := levelNorm_eq_words P
    _ ≤ ∑ w : Fin n → Fin 4, c⁻¹ * (‖J.word w‖ +
        ‖(SpatialJet.multiply K P).word w - A.operator (P.word w)‖) :=
      Finset.sum_le_sum fun w _ => hw w
    _ = c⁻¹ * (levelNorm period J n + commutatorLevel K P n) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← levelNorm_eq_words]
      rfl
    _ ≤ c⁻¹ * (levelNorm period J n +
        commutatorConvolution (boundLevel period K) (levelNorm period P) n) :=
      mul_le_mul_of_nonneg_left (add_le_add_right (commutatorLevel_le K P hn) _)
        (inv_nonneg.mpr hc.le)
    _ = _ := by rw [commutatorConvolution_eq_sum]

/-- A finite jet has no stored derivatives above its order. -/
theorem levelNorm_eq_zero_of_lt {s n : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (hn : s < n) : levelNorm period J n = 0 := by
  induction s generalizing f n with
  | zero =>
    cases J
    cases n with
    | zero => omega
    | succ n => rw [levelNorm]
  | succ s ih =>
    cases J with
    | succ df lower hd =>
      cases n with
      | zero => omega
      | succ n =>
        rw [levelNorm]
        apply Finset.sum_eq_zero
        intro i _
        exact ih (lower i) (by omega)

end EulerJetProductBounds
