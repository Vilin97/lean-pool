/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisCoefficientSpace
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Actual bounded operators on the compatible natural-axis coefficient space

The numerical bounds come from `AxisWeightEstimates`. This module additionally
proves compatibility of the output jets, so its operators act on actual smooth
coefficient functions in the complete space, not just unrelated arrays.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.AxisOperators

open Finset Finset.Nat Set
open AxisWeightEstimates AxisCoefficientSpace
open scoped BigOperators Topology BoundedContinuousFunction

/-- Cache the standard `NormedAddCommGroup (AxisSpace I ε)` instance to shorten typeclass
synthesis. -/
local instance instAxisOperators1 (I : Window) (ε : ℝ) : NormedAddCommGroup (AxisSpace I ε) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (AxisSpace I ε)` instance to shorten typeclass synthesis. -/
local instance instAxisOperators2 (I : Window) (ε : ℝ) : NormedSpace ℝ (AxisSpace I ε) :=
    inferInstance

/-- The finite Leibniz sum for one parameter derivative order. -/
def leibnizSum (f g : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ kl ∈ antidiagonal m, (m.choose kl.1 : ℝ) * f kl.1 * g kl.2

theorem leibniz_boundary (f g : ℕ → ℝ) (m : ℕ) :
    (∑ kl ∈ antidiagonal m, (m.choose kl.1 : ℝ) * f kl.1 * g (kl.2 + 1)) =
      f 0 * g (m + 1) +
        ∑ kl ∈ antidiagonal m, (m.choose (kl.1 + 1) : ℝ) * f (kl.1 + 1) * g kl.2 := by
  cases m with
  | zero => simp
  | succ m =>
      conv_lhs => rw [sum_antidiagonal_succ]
      conv_rhs => rhs; rw [sum_antidiagonal_succ']
      simp

/-- Pascal's identity is exactly the derivative recurrence for the Leibniz sum. -/
theorem leibnizSum_succ (f g : ℕ → ℝ) (m : ℕ) :
    leibnizSum f g (m + 1) =
      leibnizSum (fun k => f (k + 1)) g m +
        leibnizSum f (fun l => g (l + 1)) m := by
  unfold leibnizSum
  rw [sum_antidiagonal_succ]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul,
    Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib]
  rw [leibniz_boundary]
  ring

theorem continuousOn_leibnizSum (I : Window) (f g : ℕ → ℝ → ℝ)
    (hf : ∀ k, ContinuousOn (f k) I.interval)
    (hg : ∀ k, ContinuousOn (g k) I.interval) (m : ℕ) :
    ContinuousOn (fun x => leibnizSum (fun k => f k x) (fun k => g k x) m) I.interval := by
  apply continuousOn_finsetSum
  intro kl hkl
  exact (continuousOn_const.mul (hf kl.1)).mul (hg kl.2)

/-- Genuine first derivatives of the finite Leibniz sum reproduce the next jet. -/
theorem hasDerivWithinAt_leibnizSum (I : Window) (f g : ℕ → ℝ → ℝ)
    (hf : ∀ k x, x ∈ I.interval → HasDerivWithinAt (f k) (f (k + 1) x) I.interval x)
    (hg : ∀ k x, x ∈ I.interval → HasDerivWithinAt (g k) (g (k + 1) x) I.interval x)
    (m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    HasDerivWithinAt
      (fun y => leibnizSum (fun k => f k y) (fun k => g k y) m)
      (leibnizSum (fun k => f k x) (fun k => g k x) (m + 1)) I.interval x := by
  have h := HasDerivWithinAt.fun_sum (u := antidiagonal m) (fun kl _ =>
    (((hf kl.1 x hx).const_mul (m.choose kl.1 : ℝ)).fun_mul (hg kl.2 x hx)))
  convert! h using 1
  rw [leibnizSum_succ]
  unfold leibnizSum
  simp only [← Finset.sum_add_distrib]

/-- Actual compatible input jets, with the indices in coefficient-first order. -/
abbrev inputJet (I : Window) (ε : ℝ) (A : AxisSpace I ε) (n m : ℕ) : ℝ → ℝ :=
  jet I (weight ε) A.1 n m

theorem inputJet_bound (I : Window) {ε : ℝ} (hε : 0 < ε) (A : AxisSpace I ε)
    (n m : ℕ) (x : ℝ) :
    |inputJet I ε A n m x| ≤ ‖A‖ * weight ε n m := by
  simpa only [abs_of_pos (weight_pos hε n m), mul_comm] using
    abs_jet_le I (weight ε) A n m x

/-- Product jets are finite radial convolutions of the actual Leibniz sums. -/
def productFamily (I : Window) (ε : ℝ) (A B : AxisSpace I ε) (n m : ℕ) (x : ℝ) : ℝ :=
  jetProduct (fun i k => inputJet I ε A i k x) (fun j l => inputJet I ε B j l x) n m

theorem productFamily_eq (I : Window) (ε : ℝ) (A B : AxisSpace I ε)
    (n m : ℕ) (x : ℝ) :
    productFamily I ε A B n m x =
      ∑ ij ∈ antidiagonal n,
        leibnizSum (fun k => inputJet I ε A ij.1 k x)
          (fun l => inputJet I ε B ij.2 l x) m := rfl

theorem productFamily_continuous (I : Window) (ε : ℝ) (A B : AxisSpace I ε) (n m : ℕ) :
    ContinuousOn (productFamily I ε A B n m) I.interval := by
  change ContinuousOn (fun x => ∑ ij ∈ antidiagonal n,
    leibnizSum (fun k => inputJet I ε A ij.1 k x) (fun l => inputJet I ε B ij.2 l x) m) I.interval
  apply continuousOn_finsetSum
  intro ij hij
  exact continuousOn_leibnizSum I _ _
    (fun k => (continuous_jet I (weight ε) A.1 ij.1 k).continuousOn)
    (fun l => (continuous_jet I (weight ε) B.1 ij.2 l).continuousOn) m

theorem productFamily_deriv (I : Window) (ε : ℝ) (A B : AxisSpace I ε)
    (n m : ℕ) (x : ℝ) (hx : x ∈ I.interval) :
    HasDerivWithinAt (productFamily I ε A B n m)
      (productFamily I ε A B n (m + 1) x) I.interval x := by
  exact HasDerivWithinAt.fun_sum (u := antidiagonal n) (fun ij _ =>
    hasDerivWithinAt_leibnizSum I _ _
      (fun k y hy => hasDerivWithinAt_jet I (weight ε) A ij.1 k hy)
      (fun l y hy => hasDerivWithinAt_jet I (weight ε) B ij.2 l hy) m hx)

theorem productFamily_bound (I : Window) {ε : ℝ} (hε : 0 < ε) (A B : AxisSpace I ε)
    (n m : ℕ) (x : ℝ) :
    |productFamily I ε A B n m x| ≤ (64 * ‖A‖ * ‖B‖) * weight ε n m :=
  jetProduct_bound hε (norm_nonneg A) (norm_nonneg B) _ _
    (fun i k => inputJet_bound I hε A i k x)
    (fun j l => inputJet_bound I hε B j l x) n m

/-- Data for a genuine linear operation on compatible coefficient jets. -/
structure BoundedLinearJetFamily (I : Window) (ε : ℝ) where
  /-- Value of `BoundedLinearJetFamily`, of type `AxisSpace I ε → ℕ → ℕ → ℝ → ℝ`. -/
  value : AxisSpace I ε → ℕ → ℕ → ℝ → ℝ
  /-- Bound constant of `BoundedLinearJetFamily`, of type `ℝ`. -/
  boundConstant : ℝ
  bound_nonneg : 0 ≤ boundConstant
  cont : ∀ A n m, ContinuousOn (value A n m) I.interval
  deriv : ∀ A n m x, x ∈ I.interval →
    HasDerivWithinAt (value A n m) (value A n (m + 1) x) I.interval x
  add : ∀ A B n m x, value (A + B) n m x = value A n m x + value B n m x
  smul : ∀ c A n m x, value (c • A) n m x = c * value A n m x
  bound : ∀ A n m x, x ∈ I.interval →
    |value A n m x| ≤ (boundConstant * ‖A‖) * weight ε n m

/-- Linear value, constructed using `ofJetFamily`. -/
def linearValue (I : Window) {ε : ℝ} (hε : 0 < ε)
    (F : BoundedLinearJetFamily I ε) (A : AxisSpace I ε) : AxisSpace I ε :=
  ofJetFamily I (weight ε) (weight_pos hε) (F.value A) (F.cont A) (F.deriv A)
    (F.boundConstant * ‖A‖) (mul_nonneg F.bound_nonneg (norm_nonneg A)) (F.bound A)

theorem jet_linearValue (I : Window) {ε : ℝ} (hε : 0 < ε)
    (F : BoundedLinearJetFamily I ε) (A : AxisSpace I ε) (n m : ℕ)
    {x : ℝ} (hx : x ∈ I.interval) :
    inputJet I ε (linearValue I hε F A) n m x = F.value A n m x := by
  unfold linearValue inputJet
  apply jet_ofJetFamily
  exact hx

theorem norm_linearValue_le (I : Window) {ε : ℝ} (hε : 0 < ε)
    (F : BoundedLinearJetFamily I ε) (A : AxisSpace I ε) :
    ‖linearValue I hε F A‖ ≤ F.boundConstant * ‖A‖ := by
  unfold linearValue
  apply norm_ofJetFamily_le

/-- Linear value map, bundling `toFun`, `map_add`, `apply`, `map_smul` and the required
compatibility proofs. -/
def linearValueMap (I : Window) {ε : ℝ} (hε : 0 < ε)
    (F : BoundedLinearJetFamily I ε) : AxisSpace I ε →ₗ[ℝ] AxisSpace I ε where
  toFun := linearValue I hε F
  map_add' := by
    intro A B
    apply coefficient_ext I (weight ε) (fun n m => (weight_pos hε n m).ne')
    intro n x hx
    change inputJet I ε (linearValue I hε F (A + B)) n 0 x =
      inputJet I ε (linearValue I hε F A + linearValue I hε F B) n 0 x
    simp only [inputJet, Submodule.coe_add, jet_add]
    change inputJet I ε (linearValue I hε F (A + B)) n 0 x =
      inputJet I ε (linearValue I hε F A) n 0 x + inputJet I ε (linearValue I hε F B) n 0 x
    rw [jet_linearValue I hε F (A + B) n 0 hx,
      jet_linearValue I hε F A n 0 hx, jet_linearValue I hε F B n 0 hx]
    exact F.add A B n 0 x
  map_smul' := by
    intro c A
    apply coefficient_ext I (weight ε) (fun n m => (weight_pos hε n m).ne')
    intro n x hx
    change inputJet I ε (linearValue I hε F (c • A)) n 0 x =
      inputJet I ε (c • linearValue I hε F A) n 0 x
    simp only [inputJet, Submodule.coe_smul, jet_smul]
    change inputJet I ε (linearValue I hε F (c • A)) n 0 x =
      c * inputJet I ε (linearValue I hε F A) n 0 x
    rw [jet_linearValue I hε F (c • A) n 0 hx, jet_linearValue I hε F A n 0 hx]
    exact F.smul c A n 0 x

/-- Linear lift, given by `(linearValueMap I hε F).mkContinuous F.boundConstant
(norm_linearValue_le I hε F)`. -/
def linearLift (I : Window) {ε : ℝ} (hε : 0 < ε)
    (F : BoundedLinearJetFamily I ε) : AxisSpace I ε →L[ℝ] AxisSpace I ε :=
  (linearValueMap I hε F).mkContinuous F.boundConstant (norm_linearValue_le I hε F)

theorem jet_linearLift (I : Window) {ε : ℝ} (hε : 0 < ε)
    (F : BoundedLinearJetFamily I ε) (A : AxisSpace I ε) (n m : ℕ)
    {x : ℝ} (hx : x ∈ I.interval) :
    inputJet I ε (linearLift I hε F A) n m x = F.value A n m x :=
  jet_linearValue I hε F A n m hx

theorem norm_linearLift_le (I : Window) {ε : ℝ} (hε : 0 < ε)
    (F : BoundedLinearJetFamily I ε) : ‖linearLift I hε F‖ ≤ F.boundConstant :=
  LinearMap.mkContinuous_norm_le _ F.bound_nonneg _

/-- Data for a genuine bilinear operation, including its derivative compatibility. -/
structure BoundedBilinearJetFamily (I : Window) (ε : ℝ) where
  /-- Value of `BoundedBilinearJetFamily`, of type `AxisSpace I ε → AxisSpace I ε → ℕ → ℕ → ℝ →
  ℝ`. -/
  value : AxisSpace I ε → AxisSpace I ε → ℕ → ℕ → ℝ → ℝ
  /-- Bound constant of `BoundedBilinearJetFamily`, of type `ℝ`. -/
  boundConstant : ℝ
  bound_nonneg : 0 ≤ boundConstant
  cont : ∀ A B n m, ContinuousOn (value A B n m) I.interval
  deriv : ∀ A B n m x, x ∈ I.interval →
    HasDerivWithinAt (value A B n m) (value A B n (m + 1) x) I.interval x
  add_left : ∀ A B C n m x, value (A + B) C n m x = value A C n m x + value B C n m x
  smul_left : ∀ c A B n m x, value (c • A) B n m x = c * value A B n m x
  add_right : ∀ A B C n m x, value A (B + C) n m x = value A B n m x + value A C n m x
  smul_right : ∀ c A B n m x, value A (c • B) n m x = c * value A B n m x
  bound : ∀ A B n m x, x ∈ I.interval →
    |value A B n m x| ≤ (boundConstant * ‖A‖ * ‖B‖) * weight ε n m

/-- Bilinear value, constructed using `ofJetFamily`. -/
def bilinearValue (I : Window) {ε : ℝ} (hε : 0 < ε)
    (F : BoundedBilinearJetFamily I ε) (A B : AxisSpace I ε) : AxisSpace I ε :=
  ofJetFamily I (weight ε) (weight_pos hε) (F.value A B) (F.cont A B) (F.deriv A B)
    (F.boundConstant * ‖A‖ * ‖B‖)
    (mul_nonneg (mul_nonneg F.bound_nonneg (norm_nonneg A)) (norm_nonneg B)) (F.bound A B)

theorem jet_bilinearValue (I : Window) {ε : ℝ} (hε : 0 < ε)
    (F : BoundedBilinearJetFamily I ε) (A B : AxisSpace I ε) (n m : ℕ)
    {x : ℝ} (hx : x ∈ I.interval) :
    inputJet I ε (bilinearValue I hε F A B) n m x = F.value A B n m x := by
  unfold bilinearValue inputJet
  apply jet_ofJetFamily
  exact hx

theorem norm_bilinearValue_le (I : Window) {ε : ℝ} (hε : 0 < ε)
    (F : BoundedBilinearJetFamily I ε) (A B : AxisSpace I ε) :
    ‖bilinearValue I hε F A B‖ ≤ F.boundConstant * ‖A‖ * ‖B‖ := by
  unfold bilinearValue
  apply norm_ofJetFamily_le

/-- Bilinear value map, constructed using `LinearMap.mk₂`. -/
def bilinearValueMap (I : Window) {ε : ℝ} (hε : 0 < ε)
    (F : BoundedBilinearJetFamily I ε) : AxisSpace I ε →ₗ[ℝ] AxisSpace I ε →ₗ[ℝ] AxisSpace I ε :=
  LinearMap.mk₂ ℝ (bilinearValue I hε F)
    (by
      intro A B C
      apply coefficient_ext I (weight ε) (fun n m => (weight_pos hε n m).ne')
      intro n x hx
      simp only [coefficient, Submodule.coe_add, jet_add]
      change inputJet I ε (bilinearValue I hε F (A + B) C) n 0 x =
        inputJet I ε (bilinearValue I hε F A C) n 0 x +
        inputJet I ε (bilinearValue I hε F B C) n 0 x
      rw [jet_bilinearValue I hε F (A + B) C n 0 hx,
        jet_bilinearValue I hε F A C n 0 hx, jet_bilinearValue I hε F B C n 0 hx]
      exact F.add_left A B C n 0 x)
    (by
      intro c A B
      apply coefficient_ext I (weight ε) (fun n m => (weight_pos hε n m).ne')
      intro n x hx
      simp only [coefficient, Submodule.coe_smul, jet_smul]
      change inputJet I ε (bilinearValue I hε F (c • A) B) n 0 x =
        c * inputJet I ε (bilinearValue I hε F A B) n 0 x
      rw [jet_bilinearValue I hε F (c • A) B n 0 hx, jet_bilinearValue I hε F A B n 0 hx]
      exact F.smul_left c A B n 0 x)
    (by
      intro A B C
      apply coefficient_ext I (weight ε) (fun n m => (weight_pos hε n m).ne')
      intro n x hx
      simp only [coefficient, Submodule.coe_add, jet_add]
      change inputJet I ε (bilinearValue I hε F A (B + C)) n 0 x =
        inputJet I ε (bilinearValue I hε F A B) n 0 x +
        inputJet I ε (bilinearValue I hε F A C) n 0 x
      rw [jet_bilinearValue I hε F A (B + C) n 0 hx,
        jet_bilinearValue I hε F A B n 0 hx, jet_bilinearValue I hε F A C n 0 hx]
      exact F.add_right A B C n 0 x)
    (by
      intro c A B
      apply coefficient_ext I (weight ε) (fun n m => (weight_pos hε n m).ne')
      intro n x hx
      simp only [coefficient, Submodule.coe_smul, jet_smul]
      change inputJet I ε (bilinearValue I hε F A (c • B)) n 0 x =
        c * inputJet I ε (bilinearValue I hε F A B) n 0 x
      rw [jet_bilinearValue I hε F A (c • B) n 0 hx, jet_bilinearValue I hε F A B n 0 hx]
      exact F.smul_right c A B n 0 x)

/-- Bilinear lift, given by `(bilinearValueMap I hε F).mkContinuous₂ F.boundConstant
(norm_bilinearValue_le I hε F)`. -/
def bilinearLift (I : Window) {ε : ℝ} (hε : 0 < ε)
    (F : BoundedBilinearJetFamily I ε) :
    AxisSpace I ε →L[ℝ] AxisSpace I ε →L[ℝ] AxisSpace I ε :=
  (bilinearValueMap I hε F).mkContinuous₂ F.boundConstant (norm_bilinearValue_le I hε F)

theorem jet_bilinearLift (I : Window) {ε : ℝ} (hε : 0 < ε)
    (F : BoundedBilinearJetFamily I ε) (A B : AxisSpace I ε) (n m : ℕ)
    {x : ℝ} (hx : x ∈ I.interval) :
    inputJet I ε (bilinearLift I hε F A B) n m x = F.value A B n m x :=
  jet_bilinearValue I hε F A B n m hx

theorem norm_bilinearLift_le (I : Window) {ε : ℝ} (hε : 0 < ε)
    (F : BoundedBilinearJetFamily I ε) : ‖bilinearLift I hε F‖ ≤ F.boundConstant :=
  LinearMap.mkContinuous₂_norm_le _ F.bound_nonneg _

/-- Product data, bundling `value`, `boundConstant`, `bound_nonneg`, `cont` and the required
compatibility proofs. -/
def productData (I : Window) {ε : ℝ} (hε : 0 < ε) : BoundedBilinearJetFamily I ε where
  value := productFamily I ε
  boundConstant := 64
  bound_nonneg := by norm_num
  cont := productFamily_continuous I ε
  deriv := productFamily_deriv I ε
  add_left := by
    intro A B C n m x
    simp only [productFamily, jetProduct, inputJet, Submodule.coe_add, jet_add,
      add_mul, mul_add, Finset.sum_add_distrib]
  smul_left := by
    intro c A B n m x
    simp only [productFamily, jetProduct, inputJet, Submodule.coe_smul, jet_smul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    apply Finset.sum_congr rfl
    intro kl hkl
    ring
  add_right := by
    intro A B C n m x
    simp only [productFamily, jetProduct, inputJet, Submodule.coe_add, jet_add, mul_add,
        Finset.sum_add_distrib]
  smul_right := by
    intro c A B n m x
    simp only [productFamily, jetProduct, inputJet, Submodule.coe_smul, jet_smul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    apply Finset.sum_congr rfl
    intro kl hkl
    ring
  bound := by
    intro A B n m x hx
    exact productFamily_bound I hε A B n m x

/-- Actual continuous bilinear multiplication of coefficient functions. -/
def product (I : Window) {ε : ℝ} (hε : 0 < ε) :
    AxisSpace I ε →L[ℝ] AxisSpace I ε →L[ℝ] AxisSpace I ε :=
  bilinearLift I hε (productData I hε)

theorem norm_product_le (I : Window) {ε : ℝ} (hε : 0 < ε) : ‖product I hε‖ ≤ 64 :=
  norm_bilinearLift_le I hε (productData I hε)

theorem jet_product (I : Window) {ε : ℝ} (hε : 0 < ε) (A B : AxisSpace I ε)
    (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    inputJet I ε (product I hε A B) n m x =
      jetProduct (fun i k => inputJet I ε A i k x) (fun j l => inputJet I ε B j l x) n m :=
  jet_bilinearLift I hε (productData I hε) A B n m hx

theorem coefficient_product (I : Window) {ε : ℝ} (hε : 0 < ε) (A B : AxisSpace I ε)
    (n : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    coefficient I (weight ε) (product I hε A B) n x =
      ∑ ij ∈ antidiagonal n,
        coefficient I (weight ε) A ij.1 x * coefficient I (weight ε) B ij.2 x := by
  simpa only [jetProduct, antidiagonal_zero, Finset.sum_singleton, Prod.fst, Prod.snd,
    Nat.choose_zero_right, Nat.cast_one, one_mul, coefficient] using jet_product I hε A B n 0 hx

/-- A scalar multiple of a shifted coefficient/derivative row. This generic
construction is instantiated below with explicit verified weight bounds. -/
def rowData (I : Window) {ε : ℝ} (hε : 0 < ε) (c : ℕ → ℝ) (source : ℕ → ℕ)
    (offset : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hweight : ∀ n m, |c n| * weight ε (source n) (offset + m) ≤ K * weight ε n m) :
    BoundedLinearJetFamily I ε where
  value := fun A n m x => c n * inputJet I ε A (source n) (offset + m) x
  boundConstant := K
  bound_nonneg := hK
  cont := by
    intro A n m
    exact continuousOn_const.mul (continuous_jet I (weight ε) A.1 (source n) (offset +
        m)).continuousOn
  deriv := by
    intro A n m x hx
    simpa only [Nat.add_assoc] using
      (hasDerivWithinAt_jet I (weight ε) A (source n) (offset + m) hx).const_mul (c n)
  add := by
    intro A B n m x
    simp only [inputJet, Submodule.coe_add, jet_add, mul_add]
  smul := by
    intro a A n m x
    simp only [inputJet, Submodule.coe_smul, jet_smul]
    ring
  bound := by
    intro A n m x hx
    rw [abs_mul]
    calc
      _ ≤ |c n| * (‖A‖ * weight ε (source n) (offset + m)) :=
        mul_le_mul_of_nonneg_left (inputJet_bound I hε A _ _ x) (abs_nonneg _)
      _ = ‖A‖ * (|c n| * weight ε (source n) (offset + m)) := by ring
      _ ≤ ‖A‖ * (K * weight ε n m) := mul_le_mul_of_nonneg_left (hweight n m) (norm_nonneg A)
      _ = _ := by ring

/-- Primitive scale as an element of `ℕ → ℝ | 0 => 0 | n + 1 => 1 / ((n : ℝ) + 1)`. -/
def primitiveScale : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 / ((n : ℝ) + 1)

/-- Inverse scale as an element of `ℕ → ℝ | 0 => 0 | n + 1 => 1 / radialDivisor r n`. -/
def inverseScale (r : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 / radialDivisor r n

/-- Multiply Y scale as an element of `ℕ → ℝ | 0 => 0 | _ + 1 => 1`. -/
def multiplyYScale : ℕ → ℝ
  | 0 => 0
  | _ + 1 => 1

theorem average_row_bound {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    |1 / ((n : ℝ) + 1)| * weight ε n (0 + m) ≤ 1 * weight ε n m := by
  rw [Nat.zero_add, one_mul, abs_of_pos (by positivity : 0 < 1 / ((n : ℝ) + 1))]
  have hden : (1 : ℝ) ≤ n + 1 := by
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using div_le_self (weight_pos hε n m).le
      hden

theorem primitive_row_bound {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    |primitiveScale n| * weight ε n.pred (0 + m) ≤ 80 * weight ε n m := by
  cases n with
  | zero =>
      simp only [primitiveScale, abs_zero, zero_mul]
      exact mul_nonneg (by norm_num) (weight_pos hε 0 m).le
  | succ n =>
      simp only [primitiveScale, Nat.pred_succ, Nat.zero_add]
      simpa only [Nat.zero_add, one_mul] using
        (average_row_bound hε n m).trans (by simpa only [one_mul] using weight_radial_shift hε n m)

theorem inverse_row_bound {ε : ℝ} (hε : 0 < ε) {r : ℕ} (hr : 1 ≤ r) (n m : ℕ) :
    |inverseScale r n| * weight ε n.pred (0 + m) ≤ 80 * weight ε n m := by
  cases n with
  | zero =>
      simp only [inverseScale, abs_zero, zero_mul]
      exact mul_nonneg (by norm_num) (weight_pos hε 0 m).le
  | succ n =>
      rw [inverseScale, Nat.pred_succ, Nat.zero_add,
        abs_of_pos (one_div_pos.mpr (radialDivisor_pos hr n))]
      have hdiv := div_le_self (weight_pos hε n m).le (radialDivisor_ge_one hr n)
      have hsmall : (1 / radialDivisor r n) * weight ε n m ≤ weight ε n m := by
        simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hdiv
      exact hsmall.trans (weight_radial_shift hε n m)

theorem parameter_primitive_row_bound {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    |primitiveScale n| * weight ε n.pred (1 + m) ≤ (80 / ε) * weight ε n m := by
  cases n with
  | zero =>
      simp only [primitiveScale, abs_zero, zero_mul]
      exact mul_nonneg (by positivity) (weight_pos hε 0 m).le
  | succ n =>
      rw [primitiveScale, Nat.pred_succ, abs_of_pos (by positivity : 0 < 1 / ((n : ℝ) + 1))]
      have hdiv : weight ε n (m + 1) / ((n : ℝ) + 1) ≤ (80 / ε) * weight ε (n + 1) m := by
        apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
        convert! weight_parameter_radial_shift hε n m using 1; ring
      simpa only [Nat.add_comm 1 m, one_div, div_eq_mul_inv, one_mul, mul_comm] using hdiv

theorem multiplyY_row_bound {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    |multiplyYScale n| * weight ε n.pred (0 + m) ≤ 80 * weight ε n m := by
  cases n with
  | zero =>
      simp only [multiplyYScale, abs_zero, zero_mul]
      exact mul_nonneg (by norm_num) (weight_pos hε 0 m).le
  | succ n =>
      simpa only [multiplyYScale, abs_one, one_mul, Nat.pred_succ, Nat.zero_add] using
        weight_radial_shift hε n m

/-- Average data, given by `rowData I hε (fun n => 1 / ((n : ℝ) + 1)) id 0 1 (by norm_num)
(average_row_bound hε)`. -/
def averageData (I : Window) {ε : ℝ} (hε : 0 < ε) : BoundedLinearJetFamily I ε :=
  rowData I hε (fun n => 1 / ((n : ℝ) + 1)) id 0 1 (by norm_num) (average_row_bound hε)

/-- Primitive data, given by `rowData I hε primitiveScale Nat.pred 0 80 (by norm_num)
(primitive_row_bound hε)`. -/
def primitiveData (I : Window) {ε : ℝ} (hε : 0 < ε) : BoundedLinearJetFamily I ε :=
  rowData I hε primitiveScale Nat.pred 0 80 (by norm_num) (primitive_row_bound hε)

/-- Inverse data, given by `rowData I hε (inverseScale r) Nat.pred 0 80 (by norm_num)
(inverse_row_bound hε hr)`. -/
def inverseData (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r) :
    BoundedLinearJetFamily I ε :=
  rowData I hε (inverseScale r) Nat.pred 0 80 (by norm_num) (inverse_row_bound hε hr)

/-- Parameter primitive data, given by `rowData I hε primitiveScale Nat.pred 1 (80 / ε) (by
positivity) (parameter_primitive_row_bound hε)`. -/
def parameterPrimitiveData (I : Window) {ε : ℝ} (hε : 0 < ε) : BoundedLinearJetFamily I ε :=
  rowData I hε primitiveScale Nat.pred 1 (80 / ε) (by positivity) (parameter_primitive_row_bound hε)

/-- Multiply Y data, given by `rowData I hε multiplyYScale Nat.pred 0 80 (by norm_num)
(multiplyY_row_bound hε)`. -/
def multiplyYData (I : Window) {ε : ℝ} (hε : 0 < ε) : BoundedLinearJetFamily I ε :=
  rowData I hε multiplyYScale Nat.pred 0 80 (by norm_num) (multiplyY_row_bound hε)

/-- Average, given by `linearLift I hε (averageData I hε)`. -/
def average (I : Window) {ε : ℝ} (hε : 0 < ε) : AxisSpace I ε →L[ℝ] AxisSpace I ε :=
  linearLift I hε (averageData I hε)

/-- Primitive, given by `linearLift I hε (primitiveData I hε)`. -/
def primitive (I : Window) {ε : ℝ} (hε : 0 < ε) : AxisSpace I ε →L[ℝ] AxisSpace I ε :=
  linearLift I hε (primitiveData I hε)

/-- Regular inverse, given by `linearLift I hε (inverseData I hε r hr)`. -/
def regularInverse (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r) :
    AxisSpace I ε →L[ℝ] AxisSpace I ε := linearLift I hε (inverseData I hε r hr)

/-- Parameter primitive, given by `linearLift I hε (parameterPrimitiveData I hε)`. -/
def parameterPrimitive (I : Window) {ε : ℝ} (hε : 0 < ε) : AxisSpace I ε →L[ℝ] AxisSpace I ε :=
  linearLift I hε (parameterPrimitiveData I hε)

/-- Mul Y, given by `linearLift I hε (multiplyYData I hε)`. -/
def mulY (I : Window) {ε : ℝ} (hε : 0 < ε) : AxisSpace I ε →L[ℝ] AxisSpace I ε :=
  linearLift I hε (multiplyYData I hε)

theorem norm_average_le (I : Window) {ε : ℝ} (hε : 0 < ε) : ‖average I hε‖ ≤ 1 :=
  norm_linearLift_le I hε (averageData I hε)

theorem norm_primitive_le (I : Window) {ε : ℝ} (hε : 0 < ε) : ‖primitive I hε‖ ≤ 80 :=
  norm_linearLift_le I hε (primitiveData I hε)

theorem norm_regularInverse_le (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r) :
    ‖regularInverse I hε r hr‖ ≤ 80 := norm_linearLift_le I hε (inverseData I hε r hr)

theorem norm_parameterPrimitive_le (I : Window) {ε : ℝ} (hε : 0 < ε) :
    ‖parameterPrimitive I hε‖ ≤ 80 / ε := norm_linearLift_le I hε (parameterPrimitiveData I hε)

theorem norm_mulY_le (I : Window) {ε : ℝ} (hε : 0 < ε) : ‖mulY I hε‖ ≤ 80 :=
  norm_linearLift_le I hε (multiplyYData I hε)

theorem jet_regularInverse_zero (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A : AxisSpace I ε) (m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    inputJet I ε (regularInverse I hε r hr A) 0 m x = 0 := by
  change inputJet I ε (linearLift I hε (inverseData I hε r hr) A) 0 m x = 0
  rw [jet_linearLift I hε (inverseData I hε r hr) A 0 m hx]
  exact zero_mul _

theorem jet_regularInverse_succ (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A : AxisSpace I ε) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    inputJet I ε (regularInverse I hε r hr A) (n + 1) m x =
      inputJet I ε A n m x / radialDivisor r n := by
  change inputJet I ε (linearLift I hε (inverseData I hε r hr) A) (n + 1) m x = _
  rw [jet_linearLift I hε (inverseData I hε r hr) A (n + 1) m hx]
  simp only [inverseData, rowData, inverseScale, Nat.pred_succ, Nat.zero_add]
  ring

/-- A radial inverse applied to a finite product with a fixed parameter shift
on the first factor and radial multiplier `d` on the second. -/
def differentialFamily (I : Window) (ε : ℝ) (r p : ℕ) (d : ℕ → ℝ)
    (A B : AxisSpace I ε) : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 0
  | n + 1, m, x =>
      ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        ((d ij.2 / radialDivisor r n) * (m.choose kl.1 : ℝ)) *
          inputJet I ε A ij.1 (p + kl.1) x * inputJet I ε B ij.2 kl.2 x

theorem differentialFamily_succ_eq (I : Window) (ε : ℝ) (r p : ℕ) (d : ℕ → ℝ)
    (A B : AxisSpace I ε) (n m : ℕ) (x : ℝ) :
    differentialFamily I ε r p d A B (n + 1) m x =
      ∑ ij ∈ antidiagonal n, (d ij.2 / radialDivisor r n) *
        leibnizSum (fun k => inputJet I ε A ij.1 (p + k) x)
          (fun l => inputJet I ε B ij.2 l x) m := by
  simp only [differentialFamily, leibnizSum, Finset.mul_sum, mul_assoc]

theorem differentialFamily_continuous (I : Window) (ε : ℝ) (r p : ℕ) (d : ℕ → ℝ)
    (A B : AxisSpace I ε) (n m : ℕ) :
    ContinuousOn (differentialFamily I ε r p d A B n m) I.interval := by
  cases n with
  | zero => exact continuousOn_const
  | succ n =>
      simp_rw [show differentialFamily I ε r p d A B (n + 1) m = _ from
        funext (differentialFamily_succ_eq I ε r p d A B n m)]
      apply continuousOn_finsetSum
      intro ij hij
      apply continuousOn_const.mul
      exact continuousOn_leibnizSum I _ _
        (fun k => (continuous_jet I (weight ε) A.1 ij.1 (p + k)).continuousOn)
        (fun l => (continuous_jet I (weight ε) B.1 ij.2 l).continuousOn) m

theorem differentialFamily_deriv (I : Window) (ε : ℝ) (r p : ℕ) (d : ℕ → ℝ)
    (A B : AxisSpace I ε) (n m : ℕ) (x : ℝ) (hx : x ∈ I.interval) :
    HasDerivWithinAt (differentialFamily I ε r p d A B n m)
      (differentialFamily I ε r p d A B n (m + 1) x) I.interval x := by
  cases n with
  | zero => exact hasDerivWithinAt_const x I.interval 0
  | succ n =>
      have h := HasDerivWithinAt.fun_sum (u := antidiagonal n) (fun ij _ =>
        (hasDerivWithinAt_leibnizSum I _ _
          (fun k y hy => by
            simpa only [Nat.add_assoc] using
              hasDerivWithinAt_jet I (weight ε) A ij.1 (p + k) hy)
          (fun l y hy => hasDerivWithinAt_jet I (weight ε) B ij.2 l hy) m hx).const_mul
            (d ij.2 / radialDivisor r n))
      convert! h using 1
      · funext y
        exact differentialFamily_succ_eq I ε r p d A B n m y
      · exact differentialFamily_succ_eq I ε r p d A B n (m + 1) x

theorem shifted_kernel_weight_le (D d a b C w w' v : ℝ)
    (hD : 0 < D) (hd : 0 ≤ d) (ha : 0 ≤ a) (_hb : 0 ≤ b) (hC : 0 ≤ C)
    (hw' : 0 ≤ w') (hv : 0 ≤ v) (hshift : w ≤ C * b * w') (hfactor : b * d ≤ D) :
    ((d / D) * a) * w * v ≤ C * (a * w' * v) := by
  have hratio : b * d / D ≤ 1 := (div_le_iff₀ hD).2 (by simpa using hfactor)
  have hcoef : 0 ≤ (d / D) * a := mul_nonneg (div_nonneg hd hD.le) ha
  calc
    _ ≤ ((d / D) * a) * (C * b * w') * v :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hshift hcoef) hv
    _ = (C * (a * w' * v)) * (b * d / D) := by ring
    _ ≤ (C * (a * w' * v)) * 1 :=
      mul_le_mul_of_nonneg_left hratio (mul_nonneg hC (mul_nonneg (mul_nonneg ha hw') hv))
    _ = _ := mul_one _

/-- The mixed estimate is proved with the derivative shift and the radial
inverse together; the separate derivative need not be bounded. -/
theorem differentialFamily_bound (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r p : ℕ) (hr : 1 ≤ r) (d b : ℕ → ℝ) (C : ℝ)
    (hd : ∀ j, 0 ≤ d j) (hb : ∀ i, 0 ≤ b i) (hC : 0 ≤ C)
    (hshift : ∀ i k, weight ε i (p + k) ≤ C * b i * weight ε (i + 1) k)
    (hfactor : ∀ n i j, i + j = n → b i * d j ≤ radialDivisor r n)
    (A B : AxisSpace I ε) (n m : ℕ) (x : ℝ) :
    |differentialFamily I ε r p d A B n m x| ≤
      ((64 * C) * ‖A‖ * ‖B‖) * weight ε n m := by
  cases n with
  | zero =>
      simp only [differentialFamily, abs_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC)
        (norm_nonneg A)) (norm_nonneg B)) (weight_pos hε 0 m).le
  | succ n =>
      have hD := radialDivisor_pos hr n
      have hsum : |differentialFamily I ε r p d A B (n + 1) m x| ≤
          ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
            (‖A‖ * ‖B‖) * (C * ((m.choose kl.1 : ℝ) *
              weight ε (ij.1 + 1) kl.1 * weight ε ij.2 kl.2)) := by
        apply abs_double_sum_le
        intro ij hij kl hkl
        have hcoef : 0 ≤ (d ij.2 / radialDivisor r n) * (m.choose kl.1 : ℝ) :=
          mul_nonneg (div_nonneg (hd _) hD.le) (Nat.cast_nonneg _)
        have habs := abs_bilinear_term_le _ _ _ _ _ ‖A‖ ‖B‖ hcoef (norm_nonneg A) (norm_nonneg B)
          (weight_pos hε _ _).le (weight_pos hε _ _).le
          (inputJet_bound I hε A ij.1 (p + kl.1) x) (inputJet_bound I hε B ij.2 kl.2 x)
        have hw := shifted_kernel_weight_le (radialDivisor r n) (d ij.2)
          (m.choose kl.1 : ℝ) (b ij.1) C (weight ε ij.1 (p + kl.1))
          (weight ε (ij.1 + 1) kl.1) (weight ε ij.2 kl.2) hD (hd ij.2) (Nat.cast_nonneg _)
          (hb ij.1) hC (weight_pos hε (ij.1 + 1) kl.1).le (weight_pos hε ij.2 kl.2).le
          (hshift ij.1 kl.1) (hfactor n ij.1 ij.2 (mem_antidiagonal.mp hij))
        exact habs.trans (mul_le_mul_of_nonneg_left hw (mul_nonneg (norm_nonneg A) (norm_nonneg B)))
      have heq :
          (∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
            (‖A‖ * ‖B‖) * (C * ((m.choose kl.1 : ℝ) *
              weight ε (ij.1 + 1) kl.1 * weight ε ij.2 kl.2))) =
          ((‖A‖ * ‖B‖) * C) * shiftedProductWeightSum ε n m := by
        simp only [shiftedProductWeightSum, Finset.mul_sum, mul_assoc]
      rw [heq] at hsum
      calc
        _ ≤ ((‖A‖ * ‖B‖) * C) * shiftedProductWeightSum ε n m := hsum
        _ ≤ ((‖A‖ * ‖B‖) * C) * (64 * weight ε (n + 1) m) :=
          mul_le_mul_of_nonneg_left (shiftedProductWeightSum_le hε n m)
            (mul_nonneg (mul_nonneg (norm_nonneg A) (norm_nonneg B)) hC)
        _ = _ := by ring

/-- Differential data, bundling `value`, `boundConstant`, `bound_nonneg`, `cont` and the
required compatibility proofs. -/
def differentialData (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r p : ℕ) (hr : 1 ≤ r) (d b : ℕ → ℝ) (C : ℝ)
    (hd : ∀ j, 0 ≤ d j) (hb : ∀ i, 0 ≤ b i) (hC : 0 ≤ C)
    (hshift : ∀ i k, weight ε i (p + k) ≤ C * b i * weight ε (i + 1) k)
    (hfactor : ∀ n i j, i + j = n → b i * d j ≤ radialDivisor r n) :
    BoundedBilinearJetFamily I ε where
  value := differentialFamily I ε r p d
  boundConstant := 64 * C
  bound_nonneg := mul_nonneg (by norm_num) hC
  cont := differentialFamily_continuous I ε r p d
  deriv := differentialFamily_deriv I ε r p d
  add_left := by
    intro A B E n m x
    cases n <;> simp only [differentialFamily, inputJet, Submodule.coe_add, jet_add,
      add_mul, mul_add, Finset.sum_add_distrib, zero_add]
  smul_left := by
    intro c A B n m x
    cases n with
    | zero => simp [differentialFamily]
    | succ n =>
        simp only [differentialFamily, inputJet, Submodule.coe_smul, jet_smul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ij hij
        apply Finset.sum_congr rfl
        intro kl hkl
        ring
  add_right := by
    intro A B E n m x
    cases n <;> simp only [differentialFamily, inputJet, Submodule.coe_add, jet_add, mul_add,
        Finset.sum_add_distrib, zero_add]
  smul_right := by
    intro c A B n m x
    cases n with
    | zero => simp [differentialFamily]
    | succ n =>
        simp only [differentialFamily, inputJet, Submodule.coe_smul, jet_smul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ij hij
        apply Finset.sum_congr rfl
        intro kl hkl
        ring
  bound := fun A B n m x _ => differentialFamily_bound I hε r p hr d b C hd hb hC hshift hfactor A
      B n m x

theorem radial_index_le_divisor {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (n : ℝ) + 1 ≤ radialDivisor r n := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h : (1 : ℝ) ≤ n + r := by linarith
  simpa only [mul_one, radialDivisor] using
    mul_le_mul_of_nonneg_left h (show 0 ≤ (n : ℝ) + 1 by positivity)

/-- Inverse mixed data, constructed using `differentialData`. -/
def inverseMixedData (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r) :
    BoundedBilinearJetFamily I ε :=
  differentialData I hε r 1 hr (fun j => (j : ℝ)) (fun i => (i : ℝ) + 1) (80 / ε)
    (fun j => Nat.cast_nonneg j) (fun i => by positivity) (by positivity)
    (fun i k => by simpa only [Nat.add_comm 1 k] using weight_parameter_radial_shift hε i k)
    (fun n i j hij => mixed_factors_le_divisor hr hij)

/-- Inverse param product data, constructed using `differentialData`. -/
def inverseParamProductData (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r) :
    BoundedBilinearJetFamily I ε :=
  differentialData I hε r 1 hr (fun _ => 1) (fun i => (i : ℝ) + 1) (80 / ε)
    (fun _ => by norm_num) (fun i => by positivity) (by positivity)
    (fun i k => by simpa only [Nat.add_comm 1 k] using weight_parameter_radial_shift hε i k)
    (by
      intro n i j hij
      have hi : (i : ℝ) + 1 ≤ (n : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (show i ≤ n by omega)
      simpa only [mul_one] using hi.trans (radial_index_le_divisor hr n))

/-- Inverse dot product data, constructed using `differentialData`. -/
def inverseDotProductData (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r) :
    BoundedBilinearJetFamily I ε :=
  differentialData I hε r 0 hr (fun j => (j : ℝ)) (fun _ => 1) 80
    (fun j => Nat.cast_nonneg j) (fun _ => by norm_num) (by norm_num)
    (fun i k => by simpa only [Nat.zero_add, mul_one] using weight_radial_shift hε i k)
    (by
      intro n i j hij
      have hj : (j : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast (show j ≤ n + 1 by omega)
      simpa only [one_mul] using hj.trans (radial_index_le_divisor hr n))

/-- `J_r ((∂η f) D_Y g)`, formed and estimated without either unbounded
derivative as a standalone operator on the coefficient space. -/
def inverseMixed (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r) :
    AxisSpace I ε →L[ℝ] AxisSpace I ε →L[ℝ] AxisSpace I ε :=
  bilinearLift I hε (inverseMixedData I hε r hr)

/-- `J_r ((∂η f) g)` with the parameter derivative on the first argument. -/
def inverseParamProduct (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r) :
    AxisSpace I ε →L[ℝ] AxisSpace I ε →L[ℝ] AxisSpace I ε :=
  bilinearLift I hε (inverseParamProductData I hε r hr)

/-- `J_r (f D_Y g)` with the radial dot on the second argument. -/
def inverseDotProduct (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r) :
    AxisSpace I ε →L[ℝ] AxisSpace I ε →L[ℝ] AxisSpace I ε :=
  bilinearLift I hε (inverseDotProductData I hε r hr)

theorem norm_inverseMixed_le (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r) :
    ‖inverseMixed I hε r hr‖ ≤ 5120 / ε := by
  have h := norm_bilinearLift_le I hε (inverseMixedData I hε r hr)
  change ‖inverseMixed I hε r hr‖ ≤ 64 * (80 / ε) at h
  convert! h using 1; ring

theorem norm_inverseParamProduct_le (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r) :
    ‖inverseParamProduct I hε r hr‖ ≤ 5120 / ε := by
  have h := norm_bilinearLift_le I hε (inverseParamProductData I hε r hr)
  change ‖inverseParamProduct I hε r hr‖ ≤ 64 * (80 / ε) at h
  convert! h using 1; ring

theorem norm_inverseDotProduct_le (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r) :
    ‖inverseDotProduct I hε r hr‖ ≤ 5120 := by
  have h := norm_bilinearLift_le I hε (inverseDotProductData I hε r hr)
  change ‖inverseDotProduct I hε r hr‖ ≤ 64 * 80 at h
  norm_num at h ⊢
  exact h

theorem jet_inverseMixed (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A B : AxisSpace I ε) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    inputJet I ε (inverseMixed I hε r hr A B) n m x =
      differentialFamily I ε r 1 (fun j => (j : ℝ)) A B n m x :=
  jet_bilinearLift I hε (inverseMixedData I hε r hr) A B n m hx

theorem jet_inverseParamProduct (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A B : AxisSpace I ε) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    inputJet I ε (inverseParamProduct I hε r hr A B) n m x =
      differentialFamily I ε r 1 (fun _ => 1) A B n m x :=
  jet_bilinearLift I hε (inverseParamProductData I hε r hr) A B n m hx

theorem jet_inverseDotProduct (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A B : AxisSpace I ε) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    inputJet I ε (inverseDotProduct I hε r hr A B) n m x =
      differentialFamily I ε r 0 (fun j => (j : ℝ)) A B n m x :=
  jet_bilinearLift I hε (inverseDotProductData I hε r hr) A B n m hx

end NavierStokes.AxisOperators

end
