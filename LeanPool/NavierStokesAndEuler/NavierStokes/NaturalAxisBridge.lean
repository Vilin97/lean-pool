/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisEvaluation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Contracting
public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisCoefficientSpace
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# From the coefficient fixed point to actual natural-axis profiles

This bridge uses ordinary real derivatives of the evaluated functions. The
fixed input data must still be supplied as members of the coefficient space;
their construction from the outgoing schedule is a separate obligation.
-/

section

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

end

end

section

/-!
# The nonlinear natural-axis fixed point

The local bounds below are computed from bounded linear and bilinear
operations. In particular, the nonlinear remainders' Lipschitz estimates
are conclusions, not assumptions.
-/

section

/-!
# The natural-axis resolvent from factorial decay of radial shifts

The inverse is constructed by a norm-convergent alternating series. No
small-operator-norm hypothesis is used. The generic Banach-ring lemmas isolate
the analytic implication of the factorial estimate from its radial proof.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.AxisResolvent

open scoped BigOperators Topology
open Filter

/-- Cache the standard `NormedAddCommGroup (AxisCoefficientSpace.AxisSpace I ε)` instance to
shorten typeclass synthesis. -/
local instance instAxisResolvent1 (I : AxisCoefficientSpace.Window) (ε : ℝ) :
    NormedAddCommGroup (AxisCoefficientSpace.AxisSpace I ε) := inferInstance
/-- Cache the standard `NormedSpace ℝ (AxisCoefficientSpace.AxisSpace I ε)` instance to shorten
typeclass synthesis. -/
local instance instAxisResolvent2 (I : AxisCoefficientSpace.Window) (ε : ℝ) :
    NormedSpace ℝ (AxisCoefficientSpace.AxisSpace I ε) := inferInstance

/-- The majorant produced by `k` applications of the regular radial inverse. -/
def factorialMajorant (K : ℝ) (k : ℕ) : ℝ :=
  K ^ k / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))

theorem factorialMajorant_nonneg {K : ℝ} (hK : 0 ≤ K) (k : ℕ) :
    0 ≤ factorialMajorant K k := by
  unfold factorialMajorant
  positivity

theorem factorialMajorant_le_exp_term {K : ℝ} (hK : 0 ≤ K) (k : ℕ) :
    factorialMajorant K k ≤ K ^ k / (k.factorial : ℝ) := by
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hk1 : (1 : ℝ) ≤ ((k + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k + 1)
  apply div_le_div_of_nonneg_left (pow_nonneg hK k) hk
  nlinarith

theorem summable_factorialMajorant {K : ℝ} (hK : 0 ≤ K) :
    Summable (factorialMajorant K) := by
  apply Summable.of_norm_bounded
    (Real.summable_pow_div_factorial K)
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (factorialMajorant_nonneg hK k)]
  exact factorialMajorant_le_exp_term hK k

@[simp] theorem factorialMajorant_zero (K : ℝ) : factorialMajorant K 0 = 1 := by
  norm_num [factorialMajorant]

theorem factorialMajorant_succ (K : ℝ) (k : ℕ) :
    factorialMajorant K (k + 1) =
      (K / (((k : ℝ) + 1) * ((k : ℝ) + 2))) * factorialMajorant K k := by
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h₁ : (k : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (k : ℝ) + 2 ≠ 0 := by positivity
  simp only [factorialMajorant, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  field_simp; ring

section RadialJets

open AxisWeightEstimates

/-- All parameter jets below a prescribed radial degree vanish. -/
def JetVanishesBelow (f : ℕ → ℕ → ℝ) (k : ℕ) : Prop :=
  ∀ n, n < k → ∀ m, f n m = 0

theorem jetProduct_vanishesBelow_right (f g : ℕ → ℕ → ℝ) (k : ℕ)
    (hg : JetVanishesBelow g k) : JetVanishesBelow (jetProduct f g) k := by
  intro n hn m
  unfold jetProduct
  apply Finset.sum_eq_zero
  intro ij hij
  apply Finset.sum_eq_zero
  intro kl _
  have hij' := Finset.mem_antidiagonal.mp hij
  rw [hg ij.2 (by omega) kl.2, mul_zero]

theorem regularInverseJet_vanishesBelow (f : ℕ → ℕ → ℝ) (k : ℕ)
    (hf : JetVanishesBelow f k) :
    JetVanishesBelow (regularInverseJet 2 f) (k + 1) := by
  intro n hn m
  cases n with
  | zero => rfl
  | succ n =>
      change f n m / radialDivisor 2 n = 0
      rw [hf n (by omega) m, zero_div]

theorem radialDivisor_two_mono {k n : ℕ} (hkn : k ≤ n) :
    radialDivisor 2 k ≤ radialDivisor 2 n := by
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  unfold radialDivisor
  norm_num
  gcongr

/-- A radial inverse has a better norm bound on profiles whose first `k`
radial coefficients vanish. This is the source of the two factorials. -/
theorem regularInverseJet_bound_on_order {ε F : ℝ} (hε : 0 < ε) (hF : 0 ≤ F)
    (f : ℕ → ℕ → ℝ) (k : ℕ) (hz : JetVanishesBelow f k)
    (hf : ∀ n m, |f n m| ≤ F * weight ε n m) (n m : ℕ) :
    |regularInverseJet 2 f n m| ≤
      (80 / radialDivisor 2 k) * F * weight ε n m := by
  have hd : 0 < radialDivisor 2 k := radialDivisor_pos (by norm_num) k
  cases n with
  | zero =>
      simp only [regularInverseJet, abs_zero]
      exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hd.le) hF)
        (weight_pos hε 0 m).le
  | succ n =>
      by_cases hn : n < k
      · simp only [regularInverseJet, hz n hn m, zero_div, abs_zero]
        exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hd.le) hF)
          (weight_pos hε (n + 1) m).le
      · have hkn : k ≤ n := by omega
        rw [regularInverseJet, abs_div,
          abs_of_pos (radialDivisor_pos (by norm_num : 1 ≤ 2) n)]
        calc
          |f n m| / radialDivisor 2 n ≤ |f n m| / radialDivisor 2 k :=
            div_le_div_of_nonneg_left (abs_nonneg _) hd (radialDivisor_two_mono hkn)
          _ ≤ (F * weight ε n m) / radialDivisor 2 k :=
            div_le_div_of_nonneg_right (hf n m) hd.le
          _ ≤ (F * (80 * weight ε (n + 1) m)) / radialDivisor 2 k :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (weight_radial_shift hε n m) hF) hd.le
          _ = _ := by ring

end RadialJets

section BanachRing

variable {R : Type*} [NormedRing R]

theorem norm_neg_pow_eq (Q : R) (k : ℕ) : ‖(-Q) ^ k‖ = ‖Q ^ k‖ := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_pow]
  · rw [hk.neg_pow, norm_neg]

/-- The alternating series itself, as an element of the ambient Banach ring. -/
def alternatingResolvent (Q : R) : R := ∑' k : ℕ, (-Q) ^ k

/-- A summable geometric family gives an exact left inverse, even when the
norm of its ratio is not less than one. -/
theorem one_sub_mul_tsum_pow {Q : R} (hs : Summable (fun k : ℕ => Q ^ k)) :
    (1 - Q) * (∑' k : ℕ, Q ^ k) = 1 := by
  have h := hs.hasSum.mul_left (1 - Q)
  refine tendsto_nhds_unique h.tendsto_sum_nat ?_
  have hz : Tendsto (fun k : ℕ => 1 - Q ^ k) atTop (𝓝 (1 : R)) := by
    simpa using tendsto_const_nhds.sub hs.tendsto_atTop_zero
  convert! ← hz using 1
  funext k
  rw [← mul_neg_geom_sum, Finset.mul_sum]

/-- The same convergent series is also a right inverse in a possibly
noncommutative ring. -/
theorem tsum_pow_mul_one_sub {Q : R} (hs : Summable (fun k : ℕ => Q ^ k)) :
    (∑' k : ℕ, Q ^ k) * (1 - Q) = 1 := by
  have h := hs.hasSum.mul_right (1 - Q)
  refine tendsto_nhds_unique h.tendsto_sum_nat ?_
  have hz : Tendsto (fun k : ℕ => 1 - Q ^ k) atTop (𝓝 (1 : R)) := by
    simpa using tendsto_const_nhds.sub hs.tendsto_atTop_zero
  convert! ← hz using 1
  funext k
  rw [← geom_sum_mul_neg, Finset.sum_mul]

theorem summable_norm_neg_pow_of_factorial_bound (Q : R) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) :
    Summable (fun k : ℕ => ‖(-Q) ^ k‖) := by
  apply Summable.of_norm_bounded (summable_factorialMajorant hK)
  intro k
  simpa only [norm_norm, norm_neg_pow_eq] using hQ k

variable [CompleteSpace R]

theorem summable_neg_pow_of_factorial_bound (Q : R) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) :
    Summable (fun k : ℕ => (-Q) ^ k) :=
  (summable_norm_neg_pow_of_factorial_bound Q hK hQ).of_norm

theorem hasSum_alternatingResolvent (Q : R) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) :
    HasSum (fun k : ℕ => (-Q) ^ k) (alternatingResolvent Q) :=
  (summable_neg_pow_of_factorial_bound Q hK hQ).hasSum

theorem one_add_mul_alternatingResolvent (Q : R) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) :
    (1 + Q) * alternatingResolvent Q = 1 := by
  simpa only [alternatingResolvent, sub_neg_eq_add] using
    one_sub_mul_tsum_pow (summable_neg_pow_of_factorial_bound Q hK hQ)

theorem alternatingResolvent_mul_one_add (Q : R) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) :
    alternatingResolvent Q * (1 + Q) = 1 := by
  simpa only [alternatingResolvent, sub_neg_eq_add] using
    tsum_pow_mul_one_sub (summable_neg_pow_of_factorial_bound Q hK hQ)

omit [CompleteSpace R] in
theorem norm_alternatingResolvent_le (Q : R) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) :
    ‖alternatingResolvent Q‖ ≤ ∑' k : ℕ, factorialMajorant K k := by
  apply (norm_tsum_le_tsum_norm
    (summable_norm_neg_pow_of_factorial_bound Q hK hQ)).trans
  apply Summable.tsum_le_tsum
    (fun k => by simpa only [norm_neg_pow_eq] using hQ k)
    (summable_norm_neg_pow_of_factorial_bound Q hK hQ)
    (summable_factorialMajorant hK)

end BanachRing

section BanachOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Iteration through the radial-degree filtration gives a factorial bound
for the actual operator powers. No bound less than one is assumed. -/
theorem pow_bound_of_filtration (Q : E →L[ℝ] E) (P : ℕ → E → Prop)
    {K : ℝ} (hK : 0 ≤ K) (hzero : ∀ x, P 0 x)
    (hstep : ∀ k x, P k x → P (k + 1) (Q x))
    (hbound : ∀ k x, P k x →
      ‖Q x‖ ≤ (K / (((k : ℝ) + 1) * ((k : ℝ) + 2))) * ‖x‖) :
    ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k := by
  have hp : ∀ k x, P k ((Q ^ k) x) ∧
      ‖(Q ^ k) x‖ ≤ factorialMajorant K k * ‖x‖ := by
    intro k
    induction k with
    | zero =>
        intro x
        simpa using And.intro (hzero x) (le_refl ‖x‖)
    | succ k ih =>
        intro x
        rw [pow_succ', _root_.mul_apply_eq_comp]
        refine ⟨hstep k _ (ih x).1, ?_⟩
        calc
          ‖Q ((Q ^ k) x)‖ ≤
              (K / (((k : ℝ) + 1) * ((k : ℝ) + 2))) * ‖(Q ^ k) x‖ :=
            hbound k _ (ih x).1
          _ ≤ (K / (((k : ℝ) + 1) * ((k : ℝ) + 2))) *
              (factorialMajorant K k * ‖x‖) :=
            mul_le_mul_of_nonneg_left (ih x).2 (by positivity)
          _ = factorialMajorant K (k + 1) * ‖x‖ := by
            rw [factorialMajorant_succ]
            ring
  intro k
  exact ContinuousLinearMap.opNorm_le_bound _ (factorialMajorant_nonneg hK k)
    (fun x => (hp k x).2)

/-- Pointwise form of the inverse equation used in the nonlinear fixed-point map. -/
theorem one_add_apply_alternatingResolvent (Q : E →L[ℝ] E) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) (x : E) :
    (1 + Q) (alternatingResolvent Q x) = x := by
  have h := congrArg (fun T : E →L[ℝ] E => T x)
    (one_add_mul_alternatingResolvent Q hK hQ)
  simpa only [_root_.mul_apply_eq_comp, _root_.one_apply_eq_self] using h

theorem alternatingResolvent_apply_one_add (Q : E →L[ℝ] E) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) (x : E) :
    alternatingResolvent Q ((1 + Q) x) = x := by
  have h := congrArg (fun T : E →L[ℝ] E => T x)
    (alternatingResolvent_mul_one_add Q hK hQ)
  simpa only [_root_.mul_apply_eq_comp, _root_.one_apply_eq_self] using h

theorem alternatingResolvent_equation (Q : E →L[ℝ] E) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) (x : E) :
    alternatingResolvent Q x + Q (alternatingResolvent Q x) = x := by
  simpa only [_root_.add_apply, _root_.one_apply_eq_self] using
    one_add_apply_alternatingResolvent Q hK hQ x

/-- The inverse gives the unique solution of the integrated linear equation. -/
theorem alternatingResolvent_unique (Q : E →L[ℝ] E) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k)
    {x b : E} (hx : x + Q x = b) : x = alternatingResolvent Q b := by
  calc
    x = alternatingResolvent Q ((1 + Q) x) :=
      (alternatingResolvent_apply_one_add Q hK hQ x).symm
    _ = alternatingResolvent Q b := by
      exact congrArg (fun y => alternatingResolvent Q y)
        (by simpa only [_root_.add_apply, _root_.one_apply_eq_self] using hx)

/-- Both continuous directions are constructed explicitly from the series. -/
def oneAddEquiv (Q : E →L[ℝ] E) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) : E ≃L[ℝ] E where
  toLinearEquiv :=
    { (1 + Q).toLinearMap with
      invFun := fun x => alternatingResolvent Q x
      left_inv := alternatingResolvent_apply_one_add Q hK hQ
      right_inv := one_add_apply_alternatingResolvent Q hK hQ }
  continuous_toFun := (1 + Q).continuous
  continuous_invFun := (alternatingResolvent Q).continuous

end BanachOperators

section AxisOperators

open AxisCoefficientSpace AxisWeightEstimates

/-- Radial order in the actual compatible coefficient space. -/
def AxisVanishesBelow (I : Window) (ε : ℝ) (A : AxisSpace I ε) (k : ℕ) : Prop :=
  ∀ x : I.interval, JetVanishesBelow (fun n m => jet I (weight ε) A.1 n m x) k

theorem axis_abs_jet_le (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) (x : ℝ) :
    |jet I (weight ε) A.1 n m x| ≤ ‖A‖ * weight ε n m := by
  simpa only [abs_of_pos (weight_pos hε n m), mul_comm] using
    abs_jet_le I (weight ε) A n m x

theorem axis_norm_le_of_jet_bound (I : Window) {ε C : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (hC : 0 ≤ C)
    (hA : ∀ n m (x : I.interval), |jet I (weight ε) A.1 n m x| ≤ C * weight ε n m) :
    ‖A‖ ≤ C := by
  apply (axisSpace_norm_le_iff I hε A C hC).2
  intro n m x
  rw [iteratedDerivWithin_coefficient I (weight ε) A n m x.property]
  exact (div_le_iff₀ (weight_pos hε n m)).2 (hA n m x)

/-- The concrete jet identity for `(1/2) J₂ Mχ`. This records the operation,
not any inverse or spectral property. It allows the estimate to be applied to
any compatible construction of the two bounded operators. -/
def IsAxisLinearOperator (I : Window) (ε : ℝ) (χ : AxisSpace I ε)
    (Q : AxisSpace I ε →L[ℝ] AxisSpace I ε) : Prop :=
  ∀ A n m (x : I.interval),
    jet I (weight ε) (Q A).1 n m x = (1 / 2 : ℝ) *
      regularInverseJet 2
        (jetProduct (fun i j => jet I (weight ε) χ.1 i j x)
          (fun i j => jet I (weight ε) A.1 i j x)) n m

theorem axisLinearOperator_increases_order (I : Window) {ε : ℝ}
    (χ : AxisSpace I ε) (Q : AxisSpace I ε →L[ℝ] AxisSpace I ε)
    (hQ : IsAxisLinearOperator I ε χ Q) (k : ℕ) (A : AxisSpace I ε)
    (hA : AxisVanishesBelow I ε A k) : AxisVanishesBelow I ε (Q A) (k + 1) := by
  intro x n hn m
  change jet I (weight ε) (Q A).1 n m x = 0
  rw [hQ A n m x]
  have hz := regularInverseJet_vanishesBelow
    (jetProduct (fun i j => jet I (weight ε) χ.1 i j x)
      (fun i j => jet I (weight ε) A.1 i j x)) k
    (jetProduct_vanishesBelow_right
      (fun i j => jet I (weight ε) χ.1 i j x)
      (fun i j => jet I (weight ε) A.1 i j x) k (hA x))
  rw [hz n hn m, mul_zero]

theorem axisLinearOperator_bound_on_order (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (Q : AxisSpace I ε →L[ℝ] AxisSpace I ε)
    (hQ : IsAxisLinearOperator I ε χ Q) (k : ℕ) (A : AxisSpace I ε)
    (hA : AxisVanishesBelow I ε A k) :
    ‖Q A‖ ≤ (2560 * ‖χ‖ / radialDivisor 2 k) * ‖A‖ := by
  have hd : 0 < radialDivisor 2 k := radialDivisor_pos (by norm_num) k
  apply axis_norm_le_of_jet_bound I hε (Q A) (by positivity)
  intro n m x
  let f : ℕ → ℕ → ℝ := fun i j => jet I (weight ε) χ.1 i j x
  let g : ℕ → ℕ → ℝ := fun i j => jet I (weight ε) A.1 i j x
  have hp : ∀ i j, |jetProduct f g i j| ≤
      (64 * ‖χ‖ * ‖A‖) * weight ε i j :=
    jetProduct_bound hε (norm_nonneg χ) (norm_nonneg A) f g
      (fun i j => axis_abs_jet_le I hε χ i j x)
      (fun i j => axis_abs_jet_le I hε A i j x)
  have hz : JetVanishesBelow (jetProduct f g) k :=
    jetProduct_vanishesBelow_right f g k (hA x)
  have hj := regularInverseJet_bound_on_order hε
    (show 0 ≤ 64 * ‖χ‖ * ‖A‖ by positivity) (jetProduct f g) k hz hp n m
  rw [hQ A n m x, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  change (1 / 2 : ℝ) * |regularInverseJet 2 (jetProduct f g) n m| ≤ _
  calc
    (1 / 2 : ℝ) * |regularInverseJet 2 (jetProduct f g) n m| ≤
        (1 / 2 : ℝ) * ((80 / radialDivisor 2 k) *
          (64 * ‖χ‖ * ‖A‖) * weight ε n m) :=
      mul_le_mul_of_nonneg_left hj (by norm_num)
    _ = _ := by ring

/-- The actual weighted radial estimate: any operator with the stated
`(1/2) J₂ Mχ` coefficients has factorial-decaying powers. The multiplier may
even depend on the radial variable; the natural-axis multiplier is a special case. -/
theorem axisLinearOperator_pow_bound (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (Q : AxisSpace I ε →L[ℝ] AxisSpace I ε)
    (hQ : IsAxisLinearOperator I ε χ Q) :
    ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant (2560 * ‖χ‖) k := by
  apply pow_bound_of_filtration Q (fun k A => AxisVanishesBelow I ε A k)
    (by positivity)
  · intro A x n hn
    omega
  · exact axisLinearOperator_increases_order I χ Q hQ
  · intro k A hA
    simpa only [radialDivisor, Nat.cast_ofNat] using
      axisLinearOperator_bound_on_order I hε χ Q hQ k A hA

theorem axisLinearOperator_resolvent_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (Q : AxisSpace I ε →L[ℝ] AxisSpace I ε)
    (hQ : IsAxisLinearOperator I ε χ Q) (A : AxisSpace I ε) :
    alternatingResolvent Q A + Q (alternatingResolvent Q A) = A :=
  alternatingResolvent_equation Q (by positivity)
    (axisLinearOperator_pow_bound I hε χ Q hQ) A

/-- The exact bounded operator in the natural angular equation. -/
def naturalOperator (I : Window) {ε : ℝ} (hε : 0 < ε) (χ : AxisSpace I ε) :
    AxisSpace I ε →L[ℝ] AxisSpace I ε :=
  (1 / 2 : ℝ) • ((AxisOperators.regularInverse I hε 2 (by norm_num)).comp
    (AxisOperators.product I hε χ))

theorem naturalOperator_isAxisLinearOperator (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) : IsAxisLinearOperator I ε χ (naturalOperator I hε χ) := by
  intro A n m x
  simp only [naturalOperator, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    Submodule.coe_smul, jet_smul]
  cases n with
  | zero =>
      have hz := AxisOperators.jet_regularInverse_zero I hε 2 (by norm_num)
        (AxisOperators.product I hε χ A) m x.property
      dsimp only [AxisOperators.inputJet] at hz
      rw [hz]
      rfl
  | succ n =>
      have hs := AxisOperators.jet_regularInverse_succ I hε 2 (by norm_num)
        (AxisOperators.product I hε χ A) n m x.property
      have hp := AxisOperators.jet_product I hε χ A n m x.property
      dsimp only [AxisOperators.inputJet] at hs hp
      rw [hs, hp]
      rfl

/-- The operator norm has factorial decay with an explicit constant. -/
theorem naturalOperator_pow_bound (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (k : ℕ) :
    ‖naturalOperator I hε χ ^ k‖ ≤ factorialMajorant (2560 * ‖χ‖) k :=
  axisLinearOperator_pow_bound I hε χ _ (naturalOperator_isAxisLinearOperator I hε χ) k

/-- The linear resolvent used in the nonlinear natural-axis contraction. -/
def naturalResolvent (I : Window) {ε : ℝ} (hε : 0 < ε) (χ : AxisSpace I ε) :
    AxisSpace I ε →L[ℝ] AxisSpace I ε := alternatingResolvent (naturalOperator I hε χ)

theorem naturalResolvent_hasSum (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) :
    HasSum (fun k : ℕ => (-naturalOperator I hε χ) ^ k) (naturalResolvent I hε χ) :=
  hasSum_alternatingResolvent _ (by positivity) (naturalOperator_pow_bound I hε χ)

theorem naturalResolvent_norm_le (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) :
    ‖naturalResolvent I hε χ‖ ≤ ∑' k : ℕ, factorialMajorant (2560 * ‖χ‖) k :=
  norm_alternatingResolvent_le _ (by positivity) (naturalOperator_pow_bound I hε χ)

theorem one_add_mul_naturalResolvent (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) :
    (1 + naturalOperator I hε χ) * naturalResolvent I hε χ = 1 :=
  one_add_mul_alternatingResolvent _ (by positivity) (naturalOperator_pow_bound I hε χ)

theorem naturalResolvent_mul_one_add (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) :
    naturalResolvent I hε χ * (1 + naturalOperator I hε χ) = 1 :=
  alternatingResolvent_mul_one_add _ (by positivity) (naturalOperator_pow_bound I hε χ)

theorem one_add_apply_naturalResolvent (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) :
    (1 + naturalOperator I hε χ) (naturalResolvent I hε χ A) = A :=
  one_add_apply_alternatingResolvent _ (by positivity) (naturalOperator_pow_bound I hε χ) A

theorem naturalResolvent_apply_one_add (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) :
    naturalResolvent I hε χ ((1 + naturalOperator I hε χ) A) = A :=
  alternatingResolvent_apply_one_add _ (by positivity) (naturalOperator_pow_bound I hε χ) A

theorem naturalResolvent_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) :
    naturalResolvent I hε χ A + naturalOperator I hε χ (naturalResolvent I hε χ A) = A :=
  alternatingResolvent_equation _ (by positivity) (naturalOperator_pow_bound I hε χ) A

theorem naturalResolvent_unique (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) {A b : AxisSpace I ε}
    (hA : A + naturalOperator I hε χ A = b) : A = naturalResolvent I hε χ b :=
  alternatingResolvent_unique _ (by positivity) (naturalOperator_pow_bound I hε χ) hA

/-- In particular, the reference angular profile is obtained by applying this
map to the constant coefficient representing `1`. -/
def naturalEquationEquiv (I : Window) {ε : ℝ} (hε : 0 < ε) (χ : AxisSpace I ε) :
    AxisSpace I ε ≃L[ℝ] AxisSpace I ε :=
  oneAddEquiv _ (by positivity) (naturalOperator_pow_bound I hε χ)

end AxisOperators

end NavierStokes.AxisResolvent

end

end

end

@[expose] public section

noncomputable section

namespace NavierStokes.AxisContraction

open Set Metric
open scoped NNReal ContDiff

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A function with explicit bounds on a fixed norm ball. -/
structure Controlled (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F]
    (R : ℝ) where
  /-- Eval of `Controlled`, of type `E → F`. -/
  eval : E → F
  /-- Bound of `Controlled`, of type `ℝ`. -/
  bound : ℝ
  /-- Lip of `Controlled`, of type `ℝ`. -/
  lip : ℝ
  bound_nonneg : 0 ≤ bound
  lip_nonneg : 0 ≤ lip
  norm_le : ∀ x, ‖x‖ ≤ R → ‖eval x‖ ≤ bound
  sub_le : ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
    ‖eval x - eval y‖ ≤ lip * ‖x - y‖

namespace Controlled

variable {R : ℝ}

/-- Const bound, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility
proofs. -/
noncomputable def constBound (a : F) (B : ℝ) (hB : 0 ≤ B) (ha : ‖a‖ ≤ B) :
    Controlled E F R where
  eval := fun _ => a
  bound := B
  lip := 0
  bound_nonneg := hB
  lip_nonneg := le_rfl
  norm_le := fun _ _ => ha
  sub_le := by intro x y hx hy; simp

/-- Const, given by `constBound a ‖a‖ (norm_nonneg a) le_rfl`. -/
noncomputable def const (a : F) : Controlled E F R :=
  constBound a ‖a‖ (norm_nonneg a) le_rfl

/-- Fst, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility proofs. -/
noncomputable def fst (hR : 0 ≤ R) : Controlled (E × F) E R where
  eval := Prod.fst
  bound := R
  lip := 1
  bound_nonneg := hR
  lip_nonneg := by norm_num
  norm_le := fun x hx => (norm_fst_le x).trans hx
  sub_le := by
    intro x y hx hy
    simpa only [one_mul, Prod.fst_sub] using norm_fst_le (x - y)

/-- Snd, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility proofs. -/
noncomputable def snd (hR : 0 ≤ R) : Controlled (E × F) F R where
  eval := Prod.snd
  bound := R
  lip := 1
  bound_nonneg := hR
  lip_nonneg := by norm_num
  norm_le := fun x hx => (norm_snd_le x).trans hx
  sub_le := by
    intro x y hx hy
    simpa only [one_mul, Prod.snd_sub] using norm_snd_le (x - y)

/-- Add, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility proofs. -/
noncomputable def add (f g : Controlled E F R) : Controlled E F R where
  eval := fun x => f.eval x + g.eval x
  bound := f.bound + g.bound
  lip := f.lip + g.lip
  bound_nonneg := add_nonneg f.bound_nonneg g.bound_nonneg
  lip_nonneg := add_nonneg f.lip_nonneg g.lip_nonneg
  norm_le := by
    intro x hx
    exact (norm_add_le _ _).trans (add_le_add (f.norm_le x hx) (g.norm_le x hx))
  sub_le := by
    intro x y hx hy
    have hid : f.eval x + g.eval x - (f.eval y + g.eval y) =
        (f.eval x - f.eval y) + (g.eval x - g.eval y) := by abel
    rw [hid, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (f.sub_le x y hx hy) (g.sub_le x y hx hy))

/-- Neg, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility proofs. -/
noncomputable def neg (f : Controlled E F R) : Controlled E F R where
  eval := fun x => -f.eval x
  bound := f.bound
  lip := f.lip
  bound_nonneg := f.bound_nonneg
  lip_nonneg := f.lip_nonneg
  norm_le := by intro x hx; simpa using f.norm_le x hx
  sub_le := by
    intro x y hx hy
    simpa only [neg_sub_neg, norm_sub_rev] using f.sub_le x y hx hy

/-- Sub, given by `add f (neg g)`. -/
noncomputable def sub (f g : Controlled E F R) : Controlled E F R := add f (neg g)

/-- Scaling by a scalar of absolute value at most one keeps the same upper
bounds, making the final bounds uniform in the parameter inverse. -/
noncomputable def unitSmul (c : ℝ) (hc : |c| ≤ 1) (f : Controlled E F R) :
    Controlled E F R where
  eval := fun x => c • f.eval x
  bound := f.bound
  lip := f.lip
  bound_nonneg := f.bound_nonneg
  lip_nonneg := f.lip_nonneg
  norm_le := by
    intro x hx
    calc
      ‖c • f.eval x‖ = |c| * ‖f.eval x‖ := norm_smul _ _
      _ ≤ 1 * f.bound := mul_le_mul hc (f.norm_le x hx) (norm_nonneg _) (by norm_num)
      _ = f.bound := one_mul _
  sub_le := by
    intro x y hx hy
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    calc
      |c| * ‖f.eval x - f.eval y‖ ≤
          1 * (f.lip * ‖x - y‖) :=
        mul_le_mul hc (f.sub_le x y hx hy) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _

/-- Linear, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility
proofs. -/
noncomputable def linear (L : F →L[ℝ] G) (f : Controlled E F R) : Controlled E G R where
  eval := fun x => L (f.eval x)
  bound := ‖L‖ * f.bound
  lip := ‖L‖ * f.lip
  bound_nonneg := mul_nonneg (norm_nonneg _) f.bound_nonneg
  lip_nonneg := mul_nonneg (norm_nonneg _) f.lip_nonneg
  norm_le := by
    intro x hx
    exact (L.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (f.norm_le x hx) (norm_nonneg _))
  sub_le := by
    intro x y hx hy
    rw [← L.map_sub]
    exact (L.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left (f.sub_le x y hx hy) (norm_nonneg _)).trans_eq
        (mul_assoc _ _ _).symm)

/-- Bilinear, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility
proofs. -/
noncomputable def bilinear (B : F →L[ℝ] G →L[ℝ] H)
    (f : Controlled E F R) (g : Controlled E G R) : Controlled E H R where
  eval := fun x => B (f.eval x) (g.eval x)
  bound := ‖B‖ * f.bound * g.bound
  lip := ‖B‖ * (f.lip * g.bound + f.bound * g.lip)
  bound_nonneg := mul_nonneg (mul_nonneg (norm_nonneg B) f.bound_nonneg) g.bound_nonneg
  lip_nonneg := mul_nonneg (norm_nonneg B)
    (add_nonneg (mul_nonneg f.lip_nonneg g.bound_nonneg)
      (mul_nonneg f.bound_nonneg g.lip_nonneg))
  norm_le := by
    intro x hx
    calc
      ‖B (f.eval x) (g.eval x)‖ ≤ ‖B‖ * ‖f.eval x‖ * ‖g.eval x‖ :=
        B.le_opNorm₂ _ _
      _ ≤ ‖B‖ * f.bound * g.bound :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (f.norm_le x hx) (norm_nonneg B))
          (g.norm_le x hx) (norm_nonneg _)
          (mul_nonneg (norm_nonneg B) f.bound_nonneg)
  sub_le := by
    intro x y hx hy
    have hid : B (f.eval x) (g.eval x) - B (f.eval y) (g.eval y) =
        B (f.eval x - f.eval y) (g.eval x) +
          B (f.eval y) (g.eval x - g.eval y) := by
      simp only [map_sub, _root_.sub_apply]
      abel
    rw [hid]
    calc
      ‖B (f.eval x - f.eval y) (g.eval x) +
          B (f.eval y) (g.eval x - g.eval y)‖ ≤
          ‖B (f.eval x - f.eval y) (g.eval x)‖ +
            ‖B (f.eval y) (g.eval x - g.eval y)‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ‖f.eval x - f.eval y‖ * ‖g.eval x‖ +
          ‖B‖ * ‖f.eval y‖ * ‖g.eval x - g.eval y‖ :=
        add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
      _ ≤ ‖B‖ * (f.lip * ‖x - y‖) * g.bound +
          ‖B‖ * f.bound * (g.lip * ‖x - y‖) :=
        add_le_add
          (mul_le_mul
            (mul_le_mul_of_nonneg_left (f.sub_le x y hx hy) (norm_nonneg B))
            (g.norm_le x hx) (norm_nonneg _)
            (mul_nonneg (norm_nonneg B) (mul_nonneg f.lip_nonneg (norm_nonneg _))))
          (mul_le_mul
            (mul_le_mul_of_nonneg_left (f.norm_le y hy) (norm_nonneg B))
            (g.sub_le x y hx hy) (norm_nonneg _)
            (mul_nonneg (norm_nonneg B) f.bound_nonneg))
      _ = (‖B‖ * (f.lip * g.bound + f.bound * g.lip)) * ‖x - y‖ := by ring

/-- Pair, bundling `eval`, `bound`, `lip`, `bound_nonneg` and the required compatibility proofs. -/
noncomputable def pair (f : Controlled E F R) (g : Controlled E G R) : Controlled E (F × G) R where
  eval := fun x => (f.eval x, g.eval x)
  bound := f.bound + g.bound
  lip := f.lip + g.lip
  bound_nonneg := add_nonneg f.bound_nonneg g.bound_nonneg
  lip_nonneg := add_nonneg f.lip_nonneg g.lip_nonneg
  norm_le := by
    intro x hx
    apply (norm_prod_le_iff).mpr
    exact ⟨(f.norm_le x hx).trans (le_add_of_nonneg_right g.bound_nonneg),
      (g.norm_le x hx).trans (le_add_of_nonneg_left f.bound_nonneg)⟩
  sub_le := by
    intro x y hx hy
    apply (norm_prod_le_iff).mpr
    constructor
    · exact (f.sub_le x y hx hy).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right g.lip_nonneg) (norm_nonneg _))
    · exact (g.sub_le x y hx hy).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left f.lip_nonneg) (norm_nonneg _))

end Controlled

/-- The complete-subset fixed point step used after constructing, rather
than assuming, the remainder's local estimates. -/
theorem exists_fixedPoint_of_controlled [CompleteSpace E]
    (x₀ : E) (f : Controlled E E (‖x₀‖ + 1))
    (s : ℝ) (hs : 0 ≤ s) (hbound : s * f.bound ≤ 1)
    (hlip : s * f.lip ≤ 1 / 2) :
    ∃ x : E, ‖x - x₀‖ ≤ 1 ∧
      x₀ + s • f.eval x = x ∧
      ‖x - x₀‖ ≤ s * f.bound ∧
      ∀ y : E, ‖y - x₀‖ ≤ 1 → x₀ + s • f.eval y = y → y = x := by
  let F : E → E := fun x => x₀ + s • f.eval x
  have hnorm {x : E} (hx : x ∈ closedBall x₀ 1) : ‖x‖ ≤ ‖x₀‖ + 1 := by
    have hxn : ‖x - x₀‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hx
    calc
      ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
      _ ≤ 1 + ‖x₀‖ := add_le_add_left hxn _
      _ = ‖x₀‖ + 1 := add_comm _ _
  have herr {x : E} (hx : x ∈ closedBall x₀ 1) :
      ‖F x - x₀‖ ≤ s * f.bound := by
    have heq : F x - x₀ = s • f.eval x := by dsimp [F]; abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left (f.norm_le x (hnorm hx)) hs
  have hmaps : MapsTo F (closedBall x₀ 1) (closedBall x₀ 1) := by
    intro x hx
    simpa only [mem_closedBall, dist_eq_norm] using (herr hx).trans hbound
  have hdiff {x y : E} (hx : x ∈ closedBall x₀ 1) (hy : y ∈ closedBall x₀ 1) :
      ‖F x - F y‖ ≤ (1 / 2 : ℝ) * ‖x - y‖ := by
    have heq : F x - F y = s • (f.eval x - f.eval y) := by
      dsimp [F]
      rw [smul_sub]
      abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
    calc
      s * ‖f.eval x - f.eval y‖ ≤ s * (f.lip * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (f.sub_le x y (hnorm hx) (hnorm hy)) hs
      _ = (s * f.lip) * ‖x - y‖ := (mul_assoc _ _ _).symm
      _ ≤ (1 / 2) * ‖x - y‖ := mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
  have hc : ContractingWith (1 / 2 : ℝ≥0)
      (hmaps.restrict F (closedBall x₀ 1) (closedBall x₀ 1)) := by
    refine ⟨one_half_lt_one, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (F x.1) (F y.1) ≤ (↑(1 / 2 : ℝ≥0) : ℝ) * dist x.1 y.1
    simpa only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
      hdiff x.property y.property
  obtain ⟨x, hx, hfix, _, _⟩ :=
    ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete hmaps hc
      (x := x₀) (by simp) (edist_ne_top _ _)
  refine ⟨x, by simpa only [mem_closedBall, dist_eq_norm] using hx,
    hfix, ?_, ?_⟩
  · simpa only [hfix.eq] using herr hx
  · intro y hy hyfix
    have hym : y ∈ closedBall x₀ 1 := by
      simpa only [mem_closedBall, dist_eq_norm] using hy
    have h := hdiff hym hx
    change ‖F y - F x‖ ≤ (1 / 2 : ℝ) * ‖y - x‖ at h
    rw [show F y = y from hyfix, hfix.eq] at h
    have : ‖y - x‖ = 0 := by linarith [norm_nonneg (y - x)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Actual bounded coefficient operators, later instantiated by AxisOperators.
The derivative operators occur only after their regular radial inverses. -/
structure NaturalOperators (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- Product of `NaturalOperators`, of type `V →L[ℝ] V →L[ℝ] V`. -/
  product : V →L[ℝ] V →L[ℝ] V
  /-- Average of `NaturalOperators`, of type `V →L[ℝ] V`. -/
  average : V →L[ℝ] V
  /-- Primitive of `NaturalOperators`, of type `V →L[ℝ] V`. -/
  primitive : V →L[ℝ] V
  /-- Parameter primitive of `NaturalOperators`, of type `V →L[ℝ] V`. -/
  parameterPrimitive : V →L[ℝ] V
  /-- Mul Y of `NaturalOperators`, of type `V →L[ℝ] V`. -/
  mulY : V →L[ℝ] V
  /-- J1 of `NaturalOperators`, of type `V →L[ℝ] V`. -/
  j1 : V →L[ℝ] V
  /-- J2 of `NaturalOperators`, of type `V →L[ℝ] V`. -/
  j2 : V →L[ℝ] V
  /-- Param1 of `NaturalOperators`, of type `V →L[ℝ] V →L[ℝ] V`. -/
  param1 : V →L[ℝ] V →L[ℝ] V
  /-- Param2 of `NaturalOperators`, of type `V →L[ℝ] V →L[ℝ] V`. -/
  param2 : V →L[ℝ] V →L[ℝ] V
  /-- Dot1 of `NaturalOperators`, of type `V →L[ℝ] V →L[ℝ] V`. -/
  dot1 : V →L[ℝ] V →L[ℝ] V
  /-- Dot2 of `NaturalOperators`, of type `V →L[ℝ] V →L[ℝ] V`. -/
  dot2 : V →L[ℝ] V →L[ℝ] V
  /-- Mixed1 of `NaturalOperators`, of type `V →L[ℝ] V →L[ℝ] V`. -/
  mixed1 : V →L[ℝ] V →L[ℝ] V
  /-- Mixed2 of `NaturalOperators`, of type `V →L[ℝ] V →L[ℝ] V`. -/
  mixed2 : V →L[ℝ] V →L[ℝ] V

/-- Fixed analytic coefficient data. In the manuscript all entries have
radial degree zero. The normalized gradient is ξ₀/Λ, independent of Λ. -/
structure AxisData (V : Type*) where
  /-- A of `AxisData`, of type `ℝ`. -/
  A : ℝ
  /-- Domain data of `AxisData`, of type `ℝ`. -/
  D : ℝ
  /-- Step-size parameter of `AxisData`, of type `ℝ`. -/
  h : ℝ
  /-- One of `AxisData`, of type `V`. -/
  one : V
  /-- Eta of `AxisData`, of type `V`. -/
  eta : V
  /-- D of `AxisData`, of type `V`. -/
  d : V
  /-- Inverse L of `AxisData`, of type `V`. -/
  inverseL : V
  /-- U star of `AxisData`, of type `V`. -/
  uStar : V
  /-- U star eta of `AxisData`, of type `V`. -/
  uStarEta : V
  /-- W star of `AxisData`, of type `V`. -/
  wStar : V
  /-- H star of `AxisData`, of type `V`. -/
  hStar : V
  /-- Normalized gradient of `AxisData`, of type `V`. -/
  normalizedGradient : V
  /-- Z star of `AxisData`, of type `V`. -/
  zStar : V

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Angular linear coefficient, given by `d.wStar + d.h • d.one - (2 * d.h) • O.product d.eta
d.uStar`. -/
def angularLinearCoefficient (O : NaturalOperators V) (d : AxisData V) : V :=
  d.wStar + d.h • d.one - (2 * d.h) • O.product d.eta d.uStar

/-- Angular quadratic coefficient, given by `O.product d.d d.normalizedGradient`. -/
def angularQuadraticCoefficient (O : NaturalOperators V) (d : AxisData V) : V :=
  O.product d.d d.normalizedGradient

/-- Average coefficient, given by `(2 * d.D) • d.eta`. -/
def averageCoefficient (d : AxisData V) : V := (2 * d.D) • d.eta

/-- Angular slow coefficient, given by `(2 * d.h) • d.eta`. -/
def angularSlowCoefficient (d : AxisData V) : V := (2 * d.h) • d.eta

/-- Axial linear coefficient, given by `d.A • d.one - (4 * d.A) • O.product d.eta d.uStar +
O.product d.d d.uStarEta`. -/
def axialLinearCoefficient (O : NaturalOperators V) (d : AxisData V) : V :=
  d.A • d.one - (4 * d.A) • O.product d.eta d.uStar + O.product d.d d.uStarEta

/-- Axial quadratic coefficient, given by `(2 * d.A) • d.eta`. -/
def axialQuadraticCoefficient (d : AxisData V) : V := (2 * d.A) • d.eta

/-- The exact expanded, radially integrated nonlinear remainders.
The first component also includes the bounded angular resolvent.
Here t is Λ⁻¹ and a is φ*/C. -/
def naturalRemainder (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (t : ℝ) (a : V) (x : V × V) : V × V :=
  let φ := x.1
  let u := x.2
  let bu := O.average u
  let lin1 := O.j2 (O.product (angularLinearCoefficient O d) φ) +
    O.dot2 d.wStar φ + O.param2 φ d.hStar
  let quad1 := O.j2 (O.product (O.product (angularQuadraticCoefficient O d) u) φ)
  let slow1 := O.j2 (O.product
      (O.product (averageCoefficient d) bu + O.product (angularSlowCoefficient d) u) φ) +
    O.param2 bu (O.product d.d φ) +
    O.dot2 (O.product (averageCoefficient d) bu) φ +
    O.product d.d (O.mixed2 bu φ) -
    O.param2 φ (O.product d.d u)
  let lin2 := O.j1 (O.product (axialLinearCoefficient O d) u) +
    O.dot1 d.wStar u + O.param1 u d.hStar
  let slow2 := O.j1 (O.product (axialQuadraticCoefficient d) (O.product u u)) +
    O.dot1 (O.product (averageCoefficient d) bu) u +
    O.product d.d (O.mixed1 bu u) -
    O.param1 u (O.product d.d u)
  let source := O.product (O.product a a) (O.product φ φ)
  let pressure := O.j1
    (-O.product ((4 * d.A) • d.eta) (O.primitive source) +
      O.product d.d (O.parameterPrimitive source) -
      O.product ((2 : ℝ) • d.eta) (O.mulY source))
  (S (O.product d.inverseL (lin1 + quad1 - t • slow1)),
    O.product d.inverseL (lin2 - t • slow2 + pressure))

/-- The reference pair about which the nonlinear iteration is performed. -/
def referencePair (O : NaturalOperators V) (d : AxisData V) (S : V →L[ℝ] V) : V × V :=
  (S d.one, -(1 / 2 : ℝ) • O.j1 (O.product d.inverseL d.zStar))

/-- Scalar check of the angular grouping used before applying the actual
linear radial inverse. No derivative terms are omitted in the expansion. -/
theorem angular_remainder_expansion
    (t h D η d U W H κ φ u bu buη φdot φη : ℝ) :
    ((W + h - 2 * h * η * U) * φ + W * φdot + H * φη) +
        d * κ * u * φ -
        t * (((2 * D * η) * bu + (2 * h * η) * u) * φ +
          d * buη * φ + (2 * D * η) * bu * φdot +
          d * buη * φdot - d * u * φη) =
      ((W - t * ((2 * D * η) * bu + d * buη)) +
          h * (1 - 2 * η * (U + t * u)) + d * u * κ) * φ +
        (W - t * ((2 * D * η) * bu + d * buη)) * φdot +
        (H + t * d * u) * φη := by ring

/-- Scalar check of the axial grouping, including the pressure terms. -/
theorem axial_remainder_expansion
    (t A D η d U Uη W H u bu buη udot uη P Pη Pdot : ℝ) :
    ((A - 4 * A * η * U + d * Uη) * u + W * udot + H * uη) -
        t * ((2 * A * η) * (u * u) + (2 * D * η) * bu * udot +
          d * buη * udot - d * u * uη) +
        (-4 * A * η * P + d * Pη - 2 * η * Pdot) =
      A * (1 - 4 * η * U) * u - 2 * A * η * t * (u * u) +
        (W - t * ((2 * D * η) * bu + d * buη)) * udot +
        H * uη + d * Uη * u + t * d * u * uη -
        4 * A * η * P + d * Pη - 2 * η * Pdot := by ring

/-- Explicit propagation of local bounds through every term in the actual
integrated remainders. Its numerical fields do not depend on t or a,
only on the uniform upper bound M for the norm of a. -/
def controlledRemainder (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) (a : V) (ha : ‖a‖ ≤ M) :
    Controlled (V × V) (V × V) R :=
  let c : V → Controlled (V × V) V R := Controlled.const
  let mul := Controlled.bilinear O.product
  let add := Controlled.add
  let sub := Controlled.sub
  let φ : Controlled (V × V) V R := Controlled.fst hR
  let u : Controlled (V × V) V R := Controlled.snd hR
  let bu := Controlled.linear O.average u
  let j1 := Controlled.linear O.j1
  let j2 := Controlled.linear O.j2
  let p1 := Controlled.bilinear O.param1
  let p2 := Controlled.bilinear O.param2
  let q1 := Controlled.bilinear O.dot1
  let q2 := Controlled.bilinear O.dot2
  let m1 := Controlled.bilinear O.mixed1
  let m2 := Controlled.bilinear O.mixed2
  let lin1 := add
    (add (j2 (mul (c (angularLinearCoefficient O d)) φ)) (q2 (c d.wStar) φ))
    (p2 φ (c d.hStar))
  let quad1 := j2 (mul (mul (c (angularQuadraticCoefficient O d)) u) φ)
  let slow1 := sub
    (add
      (add
        (add
          (j2 (mul (add (mul (c (averageCoefficient d)) bu)
            (mul (c (angularSlowCoefficient d)) u)) φ))
          (p2 bu (mul (c d.d) φ)))
        (q2 (mul (c (averageCoefficient d)) bu) φ))
      (mul (c d.d) (m2 bu φ)))
    (p2 φ (mul (c d.d) u))
  let lin2 := add
    (add (j1 (mul (c (axialLinearCoefficient O d)) u)) (q1 (c d.wStar) u))
    (p1 u (c d.hStar))
  let slow2 := sub
    (add
      (add (j1 (mul (c (axialQuadraticCoefficient d)) (mul u u)))
        (q1 (mul (c (averageCoefficient d)) bu) u))
      (mul (c d.d) (m1 bu u)))
    (p1 u (mul (c d.d) u))
  let ac : Controlled (V × V) V R := Controlled.constBound a M hM ha
  let source := mul (mul ac ac) (mul φ φ)
  let pressure := j1 (sub
    (add
      (Controlled.neg (mul (c ((4 * d.A) • d.eta)) (Controlled.linear O.primitive source)))
      (mul (c d.d) (Controlled.linear O.parameterPrimitive source)))
    (mul (c ((2 : ℝ) • d.eta)) (Controlled.linear O.mulY source)))
  Controlled.pair
    (Controlled.linear S (mul (c d.inverseL)
      (sub (add lin1 quad1) (Controlled.unitSmul t ht slow1))))
    (mul (c d.inverseL) (add (sub lin2 (Controlled.unitSmul t ht slow2)) pressure))

@[simp] theorem controlledRemainder_eval (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) (a : V) (ha : ‖a‖ ≤ M) (x : V × V) :
    (controlledRemainder O d S R M hR hM t ht a ha).eval x =
      naturalRemainder O d S t a x := by
  simp only [controlledRemainder, naturalRemainder, Controlled.const, Controlled.constBound,
    Controlled.fst, Controlled.snd, Controlled.linear, Controlled.bilinear,
    Controlled.add, Controlled.sub, Controlled.neg, Controlled.unitSmul, Controlled.pair,
    sub_eq_add_neg]

/-- An explicit expression in the fixed operator norms, coefficient norms,
ball radius, and upper bound for the pressure amplitude. -/
def remainderBound (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) : ℝ :=
  (controlledRemainder O d S R M hR hM 0 (by simp) 0 (by simpa using hM)).bound

/-- Remainder lip, given by `(controlledRemainder O d S R M hR hM 0 (by simp) 0 (by simpa using
hM)).lip`. -/
def remainderLip (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) : ℝ :=
  (controlledRemainder O d S R M hR hM 0 (by simp) 0 (by simpa using hM)).lip

theorem controlledRemainder_bound_eq (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) (a : V) (ha : ‖a‖ ≤ M) :
    (controlledRemainder O d S R M hR hM t ht a ha).bound =
      remainderBound O d S R M hR hM := by rfl

theorem controlledRemainder_lip_eq (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) (a : V) (ha : ‖a‖ ≤ M) :
    (controlledRemainder O d S R M hR hM t ht a ha).lip =
      remainderLip O d S R M hR hM := by rfl

theorem remainderBound_nonneg (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) :
    0 ≤ remainderBound O d S R M hR hM :=
  (controlledRemainder O d S R M hR hM 0 (by simp) 0 (by simpa using hM)).bound_nonneg

theorem remainderLip_nonneg (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) :
    0 ≤ remainderLip O d S R M hR hM :=
  (controlledRemainder O d S R M hR hM 0 (by simp) 0 (by simpa using hM)).lip_nonneg

/-- The actual remainder is bounded uniformly in both the small parameter
and every normalized angular amplitude with norm at most M. -/
theorem norm_naturalRemainder_le (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) (a : V) (ha : ‖a‖ ≤ M)
    (x : V × V) (hx : ‖x‖ ≤ R) :
    ‖naturalRemainder O d S t a x‖ ≤ remainderBound O d S R M hR hM := by
  have h := (controlledRemainder O d S R M hR hM t ht a ha).norm_le x hx
  simpa only [controlledRemainder_eval, controlledRemainder_bound_eq] using h

/-- The local Lipschitz estimate is derived term by term from the actual
polynomial operators, including the mixed and pressure terms. -/
theorem naturalRemainder_sub_le (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (t : ℝ) (ht : |t| ≤ 1) (a : V) (ha : ‖a‖ ≤ M)
    (x y : V × V) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖naturalRemainder O d S t a x - naturalRemainder O d S t a y‖ ≤
      remainderLip O d S R M hR hM * ‖x - y‖ := by
  have h := (controlledRemainder O d S R M hR hM t ht a ha).sub_le x y hx hy
  simpa only [controlledRemainder_eval, controlledRemainder_lip_eq] using h

/-- A finite threshold depending only on fixed operator/coefficient data,
the reference pair, and the uniform norm bound M. In particular it does
not depend on the normalized amplitude a. -/
def contractionThreshold (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (x₀ : V × V) (M : ℝ) (hM : 0 ≤ M) : ℝ :=
  1 + remainderBound O d S (‖x₀‖ + 1) M (by positivity) hM +
    remainderLip O d S (‖x₀‖ + 1) M (by positivity) hM

theorem contractionThreshold_pos (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (x₀ : V × V) (M : ℝ) (hM : 0 ≤ M) :
    0 < contractionThreshold O d S x₀ M hM := by
  have hb := remainderBound_nonneg O d S (‖x₀‖ + 1) M (by positivity) hM
  have hl := remainderLip_nonneg O d S (‖x₀‖ + 1) M (by positivity) hM
  unfold contractionThreshold
  linarith

/-- Existence, uniqueness in the reference ball, and an explicit
O(Λ⁻¹) norm error for the actual polynomial remainders.
The two remainder estimates used here were proved above term by term. -/
theorem exists_unique_natural_fixedPoint [CompleteSpace V]
    (O : NaturalOperators V) (d : AxisData V) (S : V →L[ℝ] V)
    (x₀ : V × V) (M : ℝ) (hM : 0 ≤ M)
    (Λ : ℝ) (hΛ : contractionThreshold O d S x₀ M hM ≤ Λ)
    (a : V) (ha : ‖a‖ ≤ M) :
    ∃ x : V × V, ‖x - x₀‖ ≤ 1 ∧
      x₀ + (1 / (2 * Λ)) • naturalRemainder O d S (1 / Λ) a x = x ∧
      ‖x - x₀‖ ≤ remainderBound O d S (‖x₀‖ + 1) M (by positivity) hM / (2 * Λ) ∧
      ∀ y : V × V, ‖y - x₀‖ ≤ 1 →
        x₀ + (1 / (2 * Λ)) • naturalRemainder O d S (1 / Λ) a y = y → y = x := by
  let R := ‖x₀‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let B := remainderBound O d S R M hR hM
  let L := remainderLip O d S R M hR hM
  have hB : 0 ≤ B := remainderBound_nonneg O d S R M hR hM
  have hL : 0 ≤ L := remainderLip_nonneg O d S R M hR hM
  have htotal : 1 + B + L ≤ Λ := hΛ
  have hΛ1 : 1 ≤ Λ := by linarith
  have hBΛ : B ≤ Λ := by linarith
  have hLΛ : L ≤ Λ := by linarith
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ1
  have hden : 0 < 2 * Λ := by positivity
  have ht : |1 / Λ| ≤ 1 := by
    rw [abs_of_pos (one_div_pos.mpr hΛpos)]
    exact (div_le_one hΛpos).mpr hΛ1
  have hs : 0 ≤ 1 / (2 * Λ) := by positivity
  let f := controlledRemainder O d S R M hR hM (1 / Λ) ht a ha
  have hb : (1 / (2 * Λ)) * f.bound ≤ 1 := by
    change (1 / (2 * Λ)) * B ≤ 1
    rw [show (1 / (2 * Λ)) * B = B / (2 * Λ) by ring]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hl : (1 / (2 * Λ)) * f.lip ≤ 1 / 2 := by
    change (1 / (2 * Λ)) * L ≤ 1 / 2
    rw [show (1 / (2 * Λ)) * L = L / (2 * Λ) by ring]
    apply (div_le_iff₀ hden).mpr
    linarith
  obtain ⟨x, hx, hfixed, herr, huniq⟩ :=
    exists_fixedPoint_of_controlled x₀ f (1 / (2 * Λ)) hs hb hl
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · simpa only [f, controlledRemainder_eval] using hfixed
  · change ‖x - x₀‖ ≤ B / (2 * Λ)
    change ‖x - x₀‖ ≤ (1 / (2 * Λ)) * B at herr
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using herr
  · intro y hy hyfixed
    apply huniq y hy
    simpa only [f, controlledRemainder_eval] using hyfixed

/-- The same threshold works for every admissible a = φ*/C; the
normalization hypothesis is a norm bound on the actual coefficient input,
not a hypothesis about the nonlinear map's Lipschitz constant. -/
theorem uniform_natural_fixedPoint [CompleteSpace V]
    (O : NaturalOperators V) (d : AxisData V) (S : V →L[ℝ] V)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ → ∀ a : V, ‖a‖ ≤ M →
      ∃ x : V × V,
        ‖x - referencePair O d S‖ ≤ 1 ∧
        referencePair O d S +
          (1 / (2 * Λ)) • naturalRemainder O d S (1 / Λ) a x = x ∧
        ‖x - referencePair O d S‖ ≤
          remainderBound O d S (‖referencePair O d S‖ + 1) M (by positivity) hM / (2 * Λ) ∧
        ∀ y : V × V, ‖y - referencePair O d S‖ ≤ 1 →
          referencePair O d S +
            (1 / (2 * Λ)) • naturalRemainder O d S (1 / Λ) a y = y → y = x := by
  refine ⟨contractionThreshold O d S (referencePair O d S) M hM,
    contractionThreshold_pos O d S (referencePair O d S) M hM, ?_⟩
  intro Λ hΛ a ha
  exact exists_unique_natural_fixedPoint O d S (referencePair O d S) M hM Λ hΛ a ha

theorem naturalRemainder_fst_resolvent (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (t : ℝ) (a : V) (x : V × V) :
    (naturalRemainder O d S t a x).1 =
      S ((naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).1) := rfl

theorem naturalRemainder_snd_resolvent (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (t : ℝ) (a : V) (x : V × V) :
    (naturalRemainder O d S t a x).2 =
      (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).2 := rfl

/-- Undoing the actual angular resolvent turns the fixed point into the
two integrated natural equations. The only extra hypothesis is the
resolvent identity, independently proved in AxisResolvent. -/
theorem fixedPoint_integrated_equations (O : NaturalOperators V) (d : AxisData V)
    (S Q : V →L[ℝ] V) (hS : ∀ y : V, S y + Q (S y) = y)
    (t s : ℝ) (a : V) (x : V × V)
    (hfixed : referencePair O d S + s • naturalRemainder O d S t a x = x) :
    x.1 + Q x.1 =
        d.one + s • (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).1 ∧
      x.2 = -(1 / 2 : ℝ) • O.j1 (O.product d.inverseL d.zStar) +
        s • (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).2 := by
  have hφ := congrArg Prod.fst hfixed
  have hu := congrArg Prod.snd hfixed
  change S d.one + s • (naturalRemainder O d S t a x).1 = x.1 at hφ
  change -(1 / 2 : ℝ) • O.j1 (O.product d.inverseL d.zStar) +
    s • (naturalRemainder O d S t a x).2 = x.2 at hu
  rw [naturalRemainder_fst_resolvent] at hφ
  rw [naturalRemainder_snd_resolvent] at hu
  constructor
  · have hlin : S (d.one +
        s • (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).1) = x.1 := by
      simpa only [map_add, map_smul] using hφ
    have h := hS (d.one +
      s • (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).1)
    rwa [hlin] at h
  · exact hu.symm

/-- With the left resolvent identity, the two integrated equations also
imply the nonlinear fixed-point equation. -/
theorem integrated_equations_fixedPoint (O : NaturalOperators V) (d : AxisData V)
    (S Q : V →L[ℝ] V) (hS : ∀ y : V, S (y + Q y) = y)
    (t s : ℝ) (a : V) (x : V × V)
    (hφ : x.1 + Q x.1 =
      d.one + s • (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).1)
    (hu : x.2 = -(1 / 2 : ℝ) • O.j1 (O.product d.inverseL d.zStar) +
      s • (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).2) :
    referencePair O d S + s • naturalRemainder O d S t a x = x := by
  apply Prod.ext
  · change S d.one + s • (naturalRemainder O d S t a x).1 = x.1
    rw [naturalRemainder_fst_resolvent]
    calc
      S d.one + s • S ((naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).1) =
          S (d.one + s • (naturalRemainder O d (ContinuousLinearMap.id ℝ V) t a x).1) := by
        rw [map_add, map_smul]
      _ = S (x.1 + Q x.1) := congrArg S hφ.symm
      _ = x.1 := hS x.1
  · change -(1 / 2 : ℝ) • O.j1 (O.product d.inverseL d.zStar) +
      s • (naturalRemainder O d S t a x).2 = x.2
    rw [naturalRemainder_snd_resolvent]
    exact hu.symm

/-- A single coefficient-space norm error controls every angular parameter
jet uniformly on the full real parameter interval. -/
theorem axis_angular_jet_error (I : AxisCoefficientSpace.Window) (ε : ℝ)
    (x x₀ : AxisCoefficientSpace.AxisSpace I ε × AxisCoefficientSpace.AxisSpace I ε)
    (B : ℝ) (hB : ‖x - x₀‖ ≤ B) (n m : ℕ) (η : ℝ) :
    |AxisCoefficientSpace.jet I (AxisWeightEstimates.weight ε) x.1.1 n m η -
      AxisCoefficientSpace.jet I (AxisWeightEstimates.weight ε) x₀.1.1 n m η| ≤
        |AxisWeightEstimates.weight ε n m| * B := by
  have hcomponent : ‖x.1 - x₀.1‖ ≤ B := (norm_fst_le (x - x₀)).trans hB
  exact (AxisCoefficientSpace.abs_jet_sub_le I (AxisWeightEstimates.weight ε)
    x.1 x₀.1 n m η).trans
      (mul_le_mul_of_nonneg_left hcomponent (abs_nonneg _))

/-- The same uniform control for every axial parameter jet. -/
theorem axis_axial_jet_error (I : AxisCoefficientSpace.Window) (ε : ℝ)
    (x x₀ : AxisCoefficientSpace.AxisSpace I ε × AxisCoefficientSpace.AxisSpace I ε)
    (B : ℝ) (hB : ‖x - x₀‖ ≤ B) (n m : ℕ) (η : ℝ) :
    |AxisCoefficientSpace.jet I (AxisWeightEstimates.weight ε) x.2.1 n m η -
      AxisCoefficientSpace.jet I (AxisWeightEstimates.weight ε) x₀.2.1 n m η| ≤
        |AxisWeightEstimates.weight ε n m| * B := by
  have hcomponent : ‖x.2 - x₀.2‖ ≤ B := (norm_snd_le (x - x₀)).trans hB
  exact (AxisCoefficientSpace.abs_jet_sub_le I (AxisWeightEstimates.weight ε)
    x.2 x₀.2 n m η).trans
      (mul_le_mul_of_nonneg_left hcomponent (abs_nonneg _))

/-- The coefficient fixed-point error controls actual mixed derivatives
of the evaluated functions, uniformly on every smaller radial interval. -/
theorem evaluated_mixed_error (I : AxisCoefficientSpace.Window)
    {ε R : ℝ} (hε : 0 < ε) (hR : 1 ≤ R) (hR20 : R < 20)
    (A B : AxisCoefficientSpace.AxisSpace I ε) (K : ℝ) (hK : ‖A - B‖ ≤ K)
    (k m : ℕ) {Y η : ℝ} (hY : |Y| ≤ R) (hη : η ∈ Ioo I.left I.right) :
    ‖iteratedDeriv m
        (fun z => iteratedDeriv k (fun y => AxisEvaluation.profile I ε A (y, z)) Y) η -
      iteratedDeriv m
        (fun z => iteratedDeriv k (fun y => AxisEvaluation.profile I ε B (y, z)) Y) η‖ ≤
        AxisEvaluation.jetBound ε R k m * K := by
  have hY20 : Y ∈ Ioo (-20 : ℝ) 20 := abs_lt.mp (hY.trans_lt hR20)
  rw [AxisEvaluation.mixed_derivative_profile I hε A k m hY20 hη,
    AxisEvaluation.mixed_derivative_profile I hε B k m hY20 hη]
  change ‖AxisEvaluation.mixedSeries I ε A k m (Y, η) -
    AxisEvaluation.mixedSeries I ε B k m (Y, η)‖ ≤ _
  exact (AxisEvaluation.mixedSeries_sub_bound I hε hR hR20 A B k m hY).trans
    (mul_le_mul_of_nonneg_left hK (AxisEvaluation.jetBound_nonneg hε hR k m))

/-- Concrete instantiation by the genuine coefficient product, radial
averages/inverses, and derivative composites constructed in AxisOperators. -/
def coefficientOperators (I : AxisCoefficientSpace.Window) {ε : ℝ} (hε : 0 < ε) :
    NaturalOperators (AxisCoefficientSpace.AxisSpace I ε) where
  product := AxisOperators.product I hε
  average := AxisOperators.average I hε
  primitive := AxisOperators.primitive I hε
  parameterPrimitive := AxisOperators.parameterPrimitive I hε
  mulY := AxisOperators.mulY I hε
  j1 := AxisOperators.regularInverse I hε 1 (by norm_num)
  j2 := AxisOperators.regularInverse I hε 2 (by norm_num)
  param1 := AxisOperators.inverseParamProduct I hε 1 (by norm_num)
  param2 := AxisOperators.inverseParamProduct I hε 2 (by norm_num)
  dot1 := AxisOperators.inverseDotProduct I hε 1 (by norm_num)
  dot2 := AxisOperators.inverseDotProduct I hε 2 (by norm_num)
  mixed1 := AxisOperators.inverseMixed I hε 1 (by norm_num)
  mixed2 := AxisOperators.inverseMixed I hε 2 (by norm_num)

/-- The nonlinear map on the actual complete smooth coefficient space
has a single threshold valid for all normalized angular data in a fixed
norm ball. No remainder bound is supplied as a hypothesis. -/
theorem coefficient_fixedPoint
    (I : AxisCoefficientSpace.Window) {ε : ℝ} (hε : 0 < ε)
    (d : AxisData (AxisCoefficientSpace.AxisSpace I ε))
    (S : AxisCoefficientSpace.AxisSpace I ε →L[ℝ] AxisCoefficientSpace.AxisSpace I ε)
    (M : ℝ) (hM : 0 ≤ M) :
    let O := coefficientOperators I hε
    ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
      ∀ a : AxisCoefficientSpace.AxisSpace I ε, ‖a‖ ≤ M →
      ∃ x : AxisCoefficientSpace.AxisSpace I ε × AxisCoefficientSpace.AxisSpace I ε,
        ‖x - referencePair O d S‖ ≤ 1 ∧
        referencePair O d S +
          (1 / (2 * Λ)) • naturalRemainder O d S (1 / Λ) a x = x ∧
        ‖x - referencePair O d S‖ ≤
          remainderBound O d S (‖referencePair O d S‖ + 1) M (by positivity) hM / (2 * Λ) ∧
        ∀ y, ‖y - referencePair O d S‖ ≤ 1 →
          referencePair O d S +
            (1 / (2 * Λ)) • naturalRemainder O d S (1 / Λ) a y = y → y = x :=
  uniform_natural_fixedPoint (coefficientOperators I hε) d S M hM

/-- Existence of actual smooth coefficient profiles for the natural
integrated system, with the constructed angular resolvent and uniform
large-Λ estimate. The initial analytic coefficient data remain explicit. -/
theorem natural_axis_profiles
    (I : AxisCoefficientSpace.Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisCoefficientSpace.AxisSpace I ε)
    (d : AxisData (AxisCoefficientSpace.AxisSpace I ε))
    (M : ℝ) (hM : 0 ≤ M) :
    let O := coefficientOperators I hε
    let S := AxisResolvent.naturalResolvent I hε χ
    let Q := AxisResolvent.naturalOperator I hε χ
    let x₀ := referencePair O d S
    ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
      ∀ a : AxisCoefficientSpace.AxisSpace I ε, ‖a‖ ≤ M →
      ∃ x : AxisCoefficientSpace.AxisSpace I ε × AxisCoefficientSpace.AxisSpace I ε,
        ‖x - x₀‖ ≤ 1 ∧
        ‖x - x₀‖ ≤ remainderBound O d S (‖x₀‖ + 1) M (by positivity) hM / (2 * Λ) ∧
        x.1 + Q x.1 = d.one + (1 / (2 * Λ)) •
          (naturalRemainder O d (ContinuousLinearMap.id ℝ _) (1 / Λ) a x).1 ∧
        x.2 = -(1 / 2 : ℝ) • O.j1 (O.product d.inverseL d.zStar) +
          (1 / (2 * Λ)) • (naturalRemainder O d (ContinuousLinearMap.id ℝ _) (1 / Λ) a x).2 ∧
        ContDiffOn ℝ ∞ (AxisEvaluation.profile I ε x.1) (AxisEvaluation.strip I 20) ∧
        ContDiffOn ℝ ∞ (AxisEvaluation.profile I ε x.2) (AxisEvaluation.strip I 20) := by
  dsimp only
  obtain ⟨Λ₀, hΛ₀, hexists⟩ :=
    coefficient_fixedPoint I hε d (AxisResolvent.naturalResolvent I hε χ) M hM
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ a ha
  obtain ⟨x, hball, hfixed, herr, _⟩ := hexists Λ hΛ a ha
  have heq := fixedPoint_integrated_equations (coefficientOperators I hε) d
    (AxisResolvent.naturalResolvent I hε χ) (AxisResolvent.naturalOperator I hε χ)
    (AxisResolvent.naturalResolvent_equation I hε χ) (1 / Λ) (1 / (2 * Λ)) a x hfixed
  exact ⟨x, hball, herr, heq.1, heq.2,
    AxisEvaluation.profile_smooth I hε x.1, AxisEvaluation.profile_smooth I hε x.2⟩

end NavierStokes.AxisContraction

end
end

end

section

/-!
# Actual profile equations for the coefficient operators

The identities here combine the convergent, smooth evaluation of `AxisSpace`
with the exact compatible coefficient operators of `AxisOperators`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisWeightEstimates
open NavierStokes.AxisEvaluation NavierStokes.AxisOperators

namespace NavierStokes.AxisEvaluationAlgebra

theorem powerSeries_mul {f g : ℕ → ℝ} {Y : ℝ}
    (hf : Summable (fun n => ‖Y ^ n * f n‖))
    (hg : Summable (fun n => ‖Y ^ n * g n‖)) :
    (∑' n : ℕ, Y ^ n * f n) * (∑' n : ℕ, Y ^ n * g n) =
      ∑' n : ℕ, Y ^ n * ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2 := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  apply tsum_congr
  intro n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [← Finset.mem_antidiagonal.mp hij, pow_add]
  ring

theorem profile_series_norm_summable (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) :
    Summable (fun n => ‖Y ^ n * coefficient I (weight ε) A n η‖) := by
  simpa only [Real.norm_eq_abs] using (profile_hasSum I hε A (p := (Y, η)) hY).summable.abs

/-- Multiplication in the coefficient space evaluates to pointwise multiplication. -/
theorem profile_product (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A B : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    profile I ε (product I hε A B) (Y, η) =
      profile I ε A (Y, η) * profile I ε B (Y, η) := by
  rw [profile, profile, profile, powerSeries_mul
    (profile_series_norm_summable I hε A hY) (profile_series_norm_summable I hε B hY)]
  apply tsum_congr
  intro n
  rw [coefficient_product I hε A B n hη]

theorem profile_axis (I : Window) (ε : ℝ) (A : AxisSpace I ε) (η : ℝ) :
    profile I ε A (0, η) = coefficient I (weight ε) A 0 η := by
  unfold profile
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

theorem profile_deriv_Y (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    deriv (fun y => profile I ε A (y, η)) Y = mixedSeries I ε A 1 0 (Y, η) := by
  have hd := mixedSeries_hasDerivAt_Y I hε A 0 0 hY hη
  rw [mixedSeries_zero] at hd
  exact hd.deriv

theorem profile_deriv_eta (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    deriv (fun x => profile I ε A (Y, x)) η = mixedSeries I ε A 0 1 (Y, η) := by
  have hd := mixedSeries_hasDerivAt_eta I hε A 0 0 hY hη
  rw [mixedSeries_zero] at hd
  exact hd.deriv

theorem profile_iteratedDeriv_Y (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k : ℕ) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    iteratedDeriv k (fun y => profile I ε A (y, η)) Y = mixedSeries I ε A k 0 (Y, η) := by
  simpa only [mixedSeries_zero, Nat.zero_add] using iteratedDeriv_Y I hε A 0 0 k hY hη

/-- Radial value, given by `p.1 * mixedSeries I ε A 2 0 p + (r : ℝ) * mixedSeries I ε A 1 0 p`. -/
def radialValue (I : Window) (ε : ℝ) (r : ℕ) (A : AxisSpace I ε) (p : ℝ × ℝ) : ℝ :=
  p.1 * mixedSeries I ε A 2 0 p + (r : ℝ) * mixedSeries I ε A 1 0 p

theorem radialValue_eq_derivatives (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    radialValue I ε r A (Y, η) =
      Y * iteratedDeriv 2 (fun y => profile I ε A (y, η)) Y +
        (r : ℝ) * deriv (fun y => profile I ε A (y, η)) Y := by
  rw [profile_iteratedDeriv_Y I hε A 2 hY hη, profile_deriv_Y I hε A hY hη]
  rfl

theorem polynomialJet_radial (r n : ℕ) (Y : ℝ) :
    Y * polynomialJet (n + 1) 2 Y + (r : ℝ) * polynomialJet (n + 1) 1 Y =
      radialDivisor r n * Y ^ n := by
  cases n with
  | zero => simp [polynomialJet, radialDivisor, Nat.descFactorial_succ]
  | succ n =>
      have he : n + 1 + 1 - 2 = n := by omega
      simp only [polynomialJet, Nat.descFactorial_succ, Nat.descFactorial_zero,
        Nat.sub_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      simp only [Nat.add_sub_cancel, he]
      unfold radialDivisor
      push_cast
      rw [pow_succ]
      ring

/-- Coefficient formula for the actual regular radial differential operator. -/
theorem radialValue_series (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) :
    radialValue I ε r A (Y, η) =
      ∑' n : ℕ, radialDivisor r n * Y ^ n * coefficient I (weight ε) A (n + 1) η := by
  have h₂ := mixedSeries_summable I hε A 2 0 (p := (Y, η)) hY
  have h₁ := mixedSeries_summable I hε A 1 0 (p := (Y, η)) hY
  have hs := (h₂.mul_left Y).add (h₁.mul_left (r : ℝ))
  calc
    _ = ∑' n : ℕ, (Y * term I ε A 2 0 n (Y, η) +
        (r : ℝ) * term I ε A 1 0 n (Y, η)) := by
      rw [Summable.tsum_add (h₂.mul_left Y) (h₁.mul_left (r : ℝ)), tsum_mul_left, tsum_mul_left]
      rfl
    _ = ∑' n : ℕ, (Y * term I ε A 2 0 (n + 1) (Y, η) +
        (r : ℝ) * term I ε A 1 0 (n + 1) (Y, η)) := by
      rw [hs.tsum_eq_zero_add]
      simp [term, polynomialJet]
    _ = _ := by
      apply tsum_congr
      intro n
      calc
        _ = (Y * polynomialJet (n + 1) 2 Y + (r : ℝ) * polynomialJet (n + 1) 1 Y) *
            coefficient I (weight ε) A (n + 1) η := by unfold term coefficient; ring
        _ = _ := by rw [polynomialJet_radial]

/-- The regular inverse is a genuine right inverse on evaluated profiles. -/
theorem regularInverse_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A : AxisSpace I ε) {Y η : ℝ}
    (hY : |Y| < 20) (hη : η ∈ I.interval) :
    radialValue I ε r (regularInverse I hε r hr A) (Y, η) = profile I ε A (Y, η) := by
  rw [radialValue_series I hε r _ hY]
  unfold profile
  apply tsum_congr
  intro n
  change radialDivisor r n * Y ^ n * inputJet I ε (regularInverse I hε r hr A) (n + 1) 0 η = _
  rw [jet_regularInverse_succ I hε r hr A n 0 hη]
  change radialDivisor r n * Y ^ n * (coefficient I (weight ε) A n η / radialDivisor r n) = _
  field_simp [(radialDivisor_pos hr n).ne']

theorem regularInverse_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (regularInverse I hε r hr A) (0, η) = 0 := by
  rw [profile_axis]
  exact jet_regularInverse_zero I hε r hr A 0 hη

theorem derivativeSeries (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) :
    mixedSeries I ε A 1 0 (Y, η) =
      ∑' n : ℕ, ((n : ℝ) + 1) * Y ^ n * coefficient I (weight ε) A (n + 1) η := by
  have hs := mixedSeries_summable I hε A 1 0 (p := (Y, η)) hY
  unfold mixedSeries
  rw [hs.tsum_eq_zero_add]
  simp only [term, polynomialJet, Nat.zero_descFactorial_succ, Nat.cast_zero,
    zero_mul, zero_add]
  apply tsum_congr
  intro n
  simp [coefficient]

theorem jet_average_eval (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    inputJet I ε (average I hε A) n m η = inputJet I ε A n m η / ((n : ℝ) + 1) := by
  change inputJet I ε (linearLift I hε (averageData I hε) A) n m η = _
  rw [jet_linearLift I hε (averageData I hε) A n m hη]
  change (1 / ((n : ℝ) + 1)) * inputJet I ε A n (0 + m) η = _
  rw [Nat.zero_add]
  ring

theorem jet_primitive_eval (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    inputJet I ε (primitive I hε A) n m η = primitiveScale n * inputJet I ε A n.pred m η := by
  change inputJet I ε (linearLift I hε (primitiveData I hε) A) n m η = _
  rw [jet_linearLift I hε (primitiveData I hε) A n m hη]
  change primitiveScale n * inputJet I ε A n.pred (0 + m) η = _
  rw [Nat.zero_add]

theorem jet_parameterPrimitive_eval (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    inputJet I ε (parameterPrimitive I hε A) n m η =
      primitiveScale n * inputJet I ε A n.pred (1 + m) η := by
  change inputJet I ε (linearLift I hε (parameterPrimitiveData I hε) A) n m η = _
  exact jet_linearLift I hε (parameterPrimitiveData I hε) A n m hη

theorem jet_mulY_eval (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    inputJet I ε (mulY I hε A) n m η = multiplyYScale n * inputJet I ε A n.pred m η := by
  change inputJet I ε (linearLift I hε (multiplyYData I hε) A) n m η = _
  rw [jet_linearLift I hε (multiplyYData I hε) A n m hη]
  change multiplyYScale n * inputJet I ε A n.pred (0 + m) η = _
  rw [Nat.zero_add]

theorem primitive_Y_value (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    mixedSeries I ε (primitive I hε A) 1 0 (Y, η) = profile I ε A (Y, η) := by
  rw [derivativeSeries I hε _ hY]
  unfold profile
  apply tsum_congr
  intro n
  change ((n : ℝ) + 1) * Y ^ n * inputJet I ε (primitive I hε A) (n + 1) 0 η = _
  rw [jet_primitive_eval I hε A (n + 1) 0 hη]
  simp only [primitiveScale, Nat.pred_succ]
  change ((n : ℝ) + 1) * Y ^ n * (1 / ((n : ℝ) + 1) * coefficient I (weight ε) A n η) = _
  field_simp

theorem primitive_hasDerivAt (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    HasDerivAt (fun y => profile I ε (primitive I hε A) (y, η)) (profile I ε A (Y, η)) Y := by
  have hd := mixedSeries_hasDerivAt_Y I hε (primitive I hε A) 0 0 hY hη
  rw [mixedSeries_zero, primitive_Y_value I hε A (abs_lt.mpr hY) ⟨hη.1.le, hη.2.le⟩] at hd
  exact hd

theorem primitive_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (primitive I hε A) (0, η) = 0 := by
  rw [profile_axis]
  change inputJet I ε (primitive I hε A) 0 0 η = _
  rw [jet_primitive_eval I hε A 0 0 hη]
  simp [primitiveScale]

theorem profile_mulY (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    profile I ε (mulY I hε A) (Y, η) = Y * profile I ε A (Y, η) := by
  have hs := (profile_hasSum I hε (mulY I hε A) (p := (Y, η)) hY).summable
  unfold profile
  rw [hs.tsum_eq_zero_add]
  have hzero : coefficient I (weight ε) (mulY I hε A) 0 η = 0 := by
    change inputJet I ε (mulY I hε A) 0 0 η = _
    rw [jet_mulY_eval I hε A 0 0 hη]
    simp [multiplyYScale]
  rw [hzero, mul_zero, zero_add, ← tsum_mul_left]
  apply tsum_congr
  intro n
  change Y ^ (n + 1) * inputJet I ε (mulY I hε A) (n + 1) 0 η = _
  rw [jet_mulY_eval I hε A (n + 1) 0 hη]
  simp only [multiplyYScale, Nat.pred_succ, one_mul, pow_succ]
  change Y ^ n * Y * coefficient I (weight ε) A n η = _
  ring

theorem primitive_eq_mulY_average (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) : primitive I hε A = mulY I hε (average I hε A) := by
  apply coefficient_ext I (weight ε) (fun n m => (weight_pos hε n m).ne')
  intro n η hη
  change inputJet I ε (primitive I hε A) n 0 η = inputJet I ε (mulY I hε (average I hε A)) n 0 η
  rw [jet_primitive_eval I hε A n 0 hη, jet_mulY_eval I hε (average I hε A) n 0 hη,
    jet_average_eval I hε A n.pred 0 hη]
  cases n <;> simp [primitiveScale, multiplyYScale, div_eq_mul_inv, mul_comm]

theorem average_times_Y (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    Y * profile I ε (average I hε A) (Y, η) = profile I ε (primitive I hε A) (Y, η) := by
  rw [primitive_eq_mulY_average, profile_mulY I hε _ hY hη]

theorem parameterSeries (I : Window) (ε : ℝ) (A : AxisSpace I ε)
    (m : ℕ) (Y η : ℝ) :
    mixedSeries I ε A 0 m (Y, η) = ∑' n : ℕ, Y ^ n * inputJet I ε A n m η := by
  simp only [mixedSeries, term, polynomialJet, Nat.descFactorial_zero, Nat.cast_one,
    Nat.sub_zero, one_mul, inputJet]

theorem parameterSeries_norm_summable (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (m : ℕ) {Y η : ℝ} (hY : |Y| < 20) :
    Summable (fun n : ℕ => ‖Y ^ n * inputJet I ε A n m η‖) := by
  simpa only [term, polynomialJet, Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero,
    one_mul, Prod.fst, Prod.snd, inputJet, Real.norm_eq_abs] using
    (mixedSeries_summable I hε A 0 m (p := (Y, η)) hY).abs

theorem polynomialJet_dot (n : ℕ) (Y : ℝ) :
    Y * polynomialJet n 1 Y = (n : ℝ) * Y ^ n := by
  cases n with
  | zero => simp [polynomialJet]
  | succ n =>
      simp only [polynomialJet, Nat.descFactorial_one, Nat.add_sub_cancel,
        Nat.cast_add, Nat.cast_one, pow_succ]
      ring

theorem dotSeries (I : Window) (ε : ℝ) (A : AxisSpace I ε) (Y η : ℝ) :
    Y * mixedSeries I ε A 1 0 (Y, η) =
      ∑' n : ℕ, Y ^ n * ((n : ℝ) * inputJet I ε A n 0 η) := by
  rw [mixedSeries, ← tsum_mul_left]
  apply tsum_congr
  intro n
  change Y * (polynomialJet n 1 Y * inputJet I ε A n 0 η) = _
  rw [← mul_assoc, polynomialJet_dot]
  ring

theorem dotSeries_norm_summable (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) :
    Summable (fun n : ℕ => ‖Y ^ n * ((n : ℝ) * inputJet I ε A n 0 η)‖) := by
  have hs := ((mixedSeries_summable I hε A 1 0 (p := (Y, η)) hY).mul_left Y).abs
  convert! hs using 1
  funext n
  change |Y ^ n * ((n : ℝ) * inputJet I ε A n 0 η)| =
    |Y * (polynomialJet n 1 Y * inputJet I ε A n 0 η)|
  have he : Y * (polynomialJet n 1 Y * inputJet I ε A n 0 η) =
      Y ^ n * ((n : ℝ) * inputJet I ε A n 0 η) := by
    rw [← mul_assoc, polynomialJet_dot]
    ring
  rw [he]

theorem radialValue_of_convolution (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (C : AxisSpace I ε) (f g : ℕ → ℝ) {Y η : ℝ} (hY : |Y| < 20)
    (hf : Summable (fun n => ‖Y ^ n * f n‖))
    (hg : Summable (fun n => ‖Y ^ n * g n‖))
    (hC : ∀ n, radialDivisor r n * inputJet I ε C (n + 1) 0 η =
      ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2) :
    radialValue I ε r C (Y, η) = (∑' n, Y ^ n * f n) * (∑' n, Y ^ n * g n) := by
  rw [radialValue_series I hε r C hY, powerSeries_mul hf hg]
  apply tsum_congr
  intro n
  change radialDivisor r n * Y ^ n * inputJet I ε C (n + 1) 0 η = _
  calc
    _ = Y ^ n * (radialDivisor r n * inputJet I ε C (n + 1) 0 η) := by ring
    _ = _ := by rw [hC n]

theorem differentialFamily_cancel (I : Window) (ε : ℝ) (r p : ℕ) (hr : 1 ≤ r)
    (d : ℕ → ℝ) (A B : AxisSpace I ε) (n : ℕ) (η : ℝ) :
    radialDivisor r n * differentialFamily I ε r p d A B (n + 1) 0 η =
      ∑ ij ∈ Finset.antidiagonal n, inputJet I ε A ij.1 p η *
        (d ij.2 * inputJet I ε B ij.2 0 η) := by
  simp only [differentialFamily, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
    Nat.choose_zero_right, Nat.cast_one, mul_one,
    Nat.add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  field_simp [(radialDivisor_pos hr n).ne']

/-- The parameter derivative is on the first factor and the radial dot is
on the second factor, as required by the manuscript's mixed estimate. -/
theorem inverseMixed_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {Y η : ℝ}
    (hY : |Y| < 20) (hη : η ∈ I.interval) :
    radialValue I ε r (inverseMixed I hε r hr A B) (Y, η) =
      mixedSeries I ε A 0 1 (Y, η) * (Y * mixedSeries I ε B 1 0 (Y, η)) := by
  rw [parameterSeries, dotSeries]
  apply radialValue_of_convolution I hε r _ _ _ hY
    (parameterSeries_norm_summable I hε A 1 hY) (dotSeries_norm_summable I hε B hY)
  intro n
  rw [jet_inverseMixed I hε r hr A B (n + 1) 0 hη]
  exact differentialFamily_cancel I ε r 1 hr (fun j => (j : ℝ)) A B n η

theorem inverseParamProduct_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {Y η : ℝ}
    (hY : |Y| < 20) (hη : η ∈ I.interval) :
    radialValue I ε r (inverseParamProduct I hε r hr A B) (Y, η) =
      mixedSeries I ε A 0 1 (Y, η) * profile I ε B (Y, η) := by
  rw [parameterSeries]
  change radialValue I ε r (inverseParamProduct I hε r hr A B) (Y, η) =
    (∑' n, Y ^ n * inputJet I ε A n 1 η) * (∑' n, Y ^ n * inputJet I ε B n 0 η)
  apply radialValue_of_convolution I hε r _ _ _ hY
    (parameterSeries_norm_summable I hε A 1 hY) (parameterSeries_norm_summable I hε B 0 hY)
  intro n
  rw [jet_inverseParamProduct I hε r hr A B (n + 1) 0 hη]
  simpa only [one_mul] using differentialFamily_cancel I ε r 1 hr (fun _ => 1) A B n η

theorem inverseDotProduct_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {Y η : ℝ}
    (hY : |Y| < 20) (hη : η ∈ I.interval) :
    radialValue I ε r (inverseDotProduct I hε r hr A B) (Y, η) =
      profile I ε A (Y, η) * (Y * mixedSeries I ε B 1 0 (Y, η)) := by
  rw [dotSeries]
  change radialValue I ε r (inverseDotProduct I hε r hr A B) (Y, η) =
    (∑' n : ℕ, Y ^ n * inputJet I ε A n 0 η) *
      (∑' n : ℕ, Y ^ n * ((n : ℝ) * inputJet I ε B n 0 η))
  apply radialValue_of_convolution I hε r _ _ _ hY
    (parameterSeries_norm_summable I hε A 0 hY) (dotSeries_norm_summable I hε B hY)
  intro n
  rw [jet_inverseDotProduct I hε r hr A B (n + 1) 0 hη]
  exact differentialFamily_cancel I ε r 0 hr (fun j => (j : ℝ)) A B n η

theorem inverseMixed_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (inverseMixed I hε r hr A B) (0, η) = 0 := by
  rw [profile_axis]
  exact jet_inverseMixed I hε r hr A B 0 0 hη

theorem inverseParamProduct_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (inverseParamProduct I hε r hr A B) (0, η) = 0 := by
  rw [profile_axis]
  exact jet_inverseParamProduct I hε r hr A B 0 0 hη

theorem inverseDotProduct_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (inverseDotProduct I hε r hr A B) (0, η) = 0 := by
  rw [profile_axis]
  exact jet_inverseDotProduct I hε r hr A B 0 0 hη

theorem parameterPrimitive_eta_value (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (Y : ℝ) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (parameterPrimitive I hε A) (Y, η) =
      mixedSeries I ε (primitive I hε A) 0 1 (Y, η) := by
  rw [parameterSeries]
  unfold profile
  apply tsum_congr
  intro n
  change Y ^ n * inputJet I ε (parameterPrimitive I hε A) n 0 η = _
  rw [jet_parameterPrimitive_eval I hε A n 0 hη, jet_primitive_eval I hε A n 1 hη]

/-- The pressure parameter primitive is the actual parameter derivative
of the radial primitive. -/
theorem parameterPrimitive_eq_deriv_eta (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    profile I ε (parameterPrimitive I hε A) (Y, η) =
      deriv (fun x => profile I ε (primitive I hε A) (Y, x)) η := by
  rw [profile_deriv_eta I hε _ hY hη]
  exact parameterPrimitive_eta_value I hε A Y ⟨hη.1.le, hη.2.le⟩

theorem parameterPrimitive_Y_value (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    mixedSeries I ε (parameterPrimitive I hε A) 1 0 (Y, η) =
      mixedSeries I ε A 0 1 (Y, η) := by
  rw [derivativeSeries I hε _ hY, parameterSeries]
  apply tsum_congr
  intro n
  change ((n : ℝ) + 1) * Y ^ n * inputJet I ε (parameterPrimitive I hε A) (n + 1) 0 η = _
  rw [jet_parameterPrimitive_eval I hε A (n + 1) 0 hη]
  simp only [primitiveScale, Nat.pred_succ, Nat.add_zero]
  field_simp

theorem parameterPrimitive_hasDerivAt (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    HasDerivAt (fun y => profile I ε (parameterPrimitive I hε A) (y, η))
      (deriv (fun x => profile I ε A (Y, x)) η) Y := by
  have hd := mixedSeries_hasDerivAt_Y I hε (parameterPrimitive I hε A) 0 0 hY hη
  rw [mixedSeries_zero, parameterPrimitive_Y_value I hε A (abs_lt.mpr hY) ⟨hη.1.le, hη.2.le⟩] at hd
  rwa [profile_deriv_eta I hε A hY hη]

theorem parameterPrimitive_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (parameterPrimitive I hε A) (0, η) = 0 := by
  rw [profile_axis]
  change inputJet I ε (parameterPrimitive I hε A) 0 0 η = _
  rw [jet_parameterPrimitive_eval I hε A 0 0 hη]
  simp [primitiveScale]

theorem radial_segment_mem {Y y : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hy : y ∈ uIcc (0 : ℝ) Y) : y ∈ Ioo (-20 : ℝ) 20 := by
  rcases le_total (0 : ℝ) Y with h | h
  · rw [uIcc_of_le h] at hy
    exact ⟨lt_of_lt_of_le (by norm_num) hy.1, hy.2.trans_lt hY.2⟩
  · rw [uIcc_of_ge h] at hy
    exact ⟨hY.1.trans_le hy.1, lt_of_le_of_lt hy.2 (by norm_num)⟩

/-- The coefficient primitive equals the ordinary oriented integral. -/
theorem primitive_integral (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    profile I ε (primitive I hε A) (Y, η) =
      ∫ y in (0 : ℝ)..Y, profile I ε A (y, η) := by
  have hcont : ContinuousOn (fun y => profile I ε A (y, η)) (uIcc (0 : ℝ) Y) := by
    intro y hy
    have hd := mixedSeries_hasDerivAt_Y I hε A 0 0 (radial_segment_mem hY hy) hη
    rw [mixedSeries_zero] at hd
    exact hd.continuousAt.continuousWithinAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => primitive_hasDerivAt I hε A (radial_segment_mem hY hy) hη)
    hcont.intervalIntegrable
  rw [primitive_axis_zero I hε A ⟨hη.1.le, hη.2.le⟩, sub_zero] at hi
  exact hi.symm

theorem average_integral (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : Y ∈ Ioo (-20 : ℝ) 20)
    (hη : η ∈ Ioo I.left I.right) :
    Y * profile I ε (average I hε A) (Y, η) =
      ∫ y in (0 : ℝ)..Y, profile I ε A (y, η) := by
  rw [average_times_Y I hε A (abs_lt.mpr hY) ⟨hη.1.le, hη.2.le⟩]
  exact primitive_integral I hε A hY hη

theorem regularInverse_actual_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A : AxisSpace I ε) {Y η : ℝ}
    (hY : Y ∈ Ioo (-20 : ℝ) 20) (hη : η ∈ Ioo I.left I.right) :
    Y * iteratedDeriv 2 (fun y => profile I ε (regularInverse I hε r hr A) (y, η)) Y +
      (r : ℝ) * deriv (fun y => profile I ε (regularInverse I hε r hr A) (y, η)) Y =
      profile I ε A (Y, η) := by
  rw [← radialValue_eq_derivatives I hε r _ hY hη]
  exact regularInverse_equation I hε r hr A (abs_lt.mpr hY) ⟨hη.1.le, hη.2.le⟩

theorem inverseMixed_actual_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε) {Y η : ℝ}
    (hY : Y ∈ Ioo (-20 : ℝ) 20) (hη : η ∈ Ioo I.left I.right) :
    Y * iteratedDeriv 2 (fun y => profile I ε (inverseMixed I hε r hr A B) (y, η)) Y +
      (r : ℝ) * deriv (fun y => profile I ε (inverseMixed I hε r hr A B) (y, η)) Y =
      deriv (fun x => profile I ε A (Y, x)) η *
        (Y * deriv (fun y => profile I ε B (y, η)) Y) := by
  rw [← radialValue_eq_derivatives I hε r _ hY hη,
    profile_deriv_eta I hε A hY hη, profile_deriv_Y I hε B hY hη]
  exact inverseMixed_equation I hε r hr A B (abs_lt.mpr hY) ⟨hη.1.le, hη.2.le⟩

theorem average_axis (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    profile I ε (average I hε A) (0, η) = profile I ε A (0, η) := by
  rw [profile_axis, profile_axis]
  change inputJet I ε (average I hε A) 0 0 η = inputJet I ε A 0 0 η
  rw [jet_average_eval I hε A 0 0 hη]
  norm_num

theorem average_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y η : ℝ} (hY : |Y| < 20) (hη : η ∈ I.interval) :
    profile I ε (average I hε A) (Y, η) +
      Y * mixedSeries I ε (average I hε A) 1 0 (Y, η) = profile I ε A (Y, η) := by
  have hs := (parameterSeries_norm_summable I hε (average I hε A) 0 (η := η) hY).of_norm
  have hd := (dotSeries_norm_summable I hε (average I hε A) (η := η) hY).of_norm
  change (∑' n : ℕ, Y ^ n * inputJet I ε (average I hε A) n 0 η) +
    Y * mixedSeries I ε (average I hε A) 1 0 (Y, η) =
    ∑' n : ℕ, Y ^ n * inputJet I ε A n 0 η
  rw [dotSeries, ← hs.tsum_add hd]
  apply tsum_congr
  intro n
  rw [jet_average_eval I hε A n 0 hη]
  field_simp; ring

end NavierStokes.AxisEvaluationAlgebra

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.NaturalAxisBridge

/-- Cache the standard `NormedAddCommGroup (AxisCoefficientSpace.AxisSpace I ε)` instance to
shorten typeclass synthesis. -/
local instance instNaturalAxisBridge1 (I : AxisCoefficientSpace.Window) (ε : ℝ) :
    NormedAddCommGroup (AxisCoefficientSpace.AxisSpace I ε) := inferInstance
/-- Cache the standard `NormedSpace ℝ (AxisCoefficientSpace.AxisSpace I ε)` instance to shorten
typeclass synthesis. -/
local instance instNaturalAxisBridge2 (I : AxisCoefficientSpace.Window) (ε : ℝ) :
    NormedSpace ℝ (AxisCoefficientSpace.AxisSpace I ε) := inferInstance

open Set Filter
open scoped Topology ContDiff
open AxisCoefficientSpace AxisWeightEstimates

/-- Ordinary radial partial derivative of an actual function. -/
def partialY (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun Y => F (Y, p.2)) p.1

/-- Ordinary parameter partial derivative of an actual function. -/
def partialEta (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun η => F (p.1, η)) p.2

/-- Actual mixed derivative, with the order used by the manuscript's jet bounds. -/
def mixedDerivative (k m : ℕ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedDeriv m (fun η => iteratedDeriv k (fun Y => F (Y, η)) p.1) p.2

/-- The singular radial differential expression, evaluated without division by `Y`. -/
def radialDifferential (r : ℕ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * iteratedDeriv 2 (fun Y => F (Y, p.2)) p.1 + (r : ℝ) * partialY F p

/-- The same expression in terms of the rigorously differentiated sums. -/
def radialEvaluation (I : Window) (ε : ℝ) (r : ℕ) (A : AxisSpace I ε) (p : ℝ × ℝ) : ℝ :=
  p.1 * AxisEvaluation.mixedSeries I ε A 2 0 p +
    (r : ℝ) * AxisEvaluation.mixedSeries I ε A 1 0 p

theorem partialY_profile (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    partialY (AxisEvaluation.profile I ε A) p = AxisEvaluation.mixedSeries I ε A 1 0 p := by
  simpa only [partialY, AxisEvaluation.mixedSeries_zero] using
    (AxisEvaluation.mixedSeries_hasDerivAt_Y I hε A 0 0 hp.1 hp.2).deriv

theorem partialEta_profile (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    partialEta (AxisEvaluation.profile I ε A) p = AxisEvaluation.mixedSeries I ε A 0 1 p := by
  simpa only [partialEta, AxisEvaluation.mixedSeries_zero] using
    (AxisEvaluation.mixedSeries_hasDerivAt_eta I hε A 0 0 hp.1 hp.2).deriv

theorem mixedDerivative_profile (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (k m : ℕ) {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    mixedDerivative k m (AxisEvaluation.profile I ε A) p =
      AxisEvaluation.mixedSeries I ε A k m p := by
  simpa only [mixedDerivative, AxisEvaluation.mixedSeries, AxisEvaluation.term,
    AxisEvaluation.polynomialJet] using
    AxisEvaluation.mixed_derivative_profile I hε A k m hp.1 hp.2

theorem radialEvaluation_eq (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A : AxisSpace I ε) {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε r A p = radialDifferential r (AxisEvaluation.profile I ε A) p := by
  have h2 := AxisEvaluation.iteratedDeriv_Y I hε A 0 0 2 hp.1 hp.2
  simp only [AxisEvaluation.mixedSeries_zero, Nat.zero_add] at h2
  rw [radialEvaluation, radialDifferential, partialY_profile I hε A hp, h2]

theorem profile_add (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A B : AxisSpace I ε) {p : ℝ × ℝ} (hp : |p.1| < 20) :
    AxisEvaluation.profile I ε (A + B) p =
      AxisEvaluation.profile I ε A p + AxisEvaluation.profile I ε B p := by
  simpa only [AxisEvaluation.mixedSeries_zero] using
    AxisEvaluation.mixedSeries_add I hε A B 0 0 hp

theorem profile_smul (I : Window) (ε c : ℝ) (A : AxisSpace I ε) (p : ℝ × ℝ) :
    AxisEvaluation.profile I ε (c • A) p = c * AxisEvaluation.profile I ε A p := by
  simpa only [AxisEvaluation.mixedSeries_zero] using
    AxisEvaluation.mixedSeries_smul I ε c A 0 0 p

theorem profile_sub (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A B : AxisSpace I ε) {p : ℝ × ℝ} (hp : |p.1| < 20) :
    AxisEvaluation.profile I ε (A - B) p =
      AxisEvaluation.profile I ε A p - AxisEvaluation.profile I ε B p := by
  simpa only [AxisEvaluation.mixedSeries_zero] using
    AxisEvaluation.mixedSeries_sub I hε A B 0 0 hp

theorem profile_zero (I : Window) (ε : ℝ) (p : ℝ × ℝ) :
    AxisEvaluation.profile I ε (0 : AxisSpace I ε) p = 0 := by
  simp [AxisEvaluation.profile, coefficient]

theorem radialEvaluation_add (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A B : AxisSpace I ε) {p : ℝ × ℝ} (hp : |p.1| < 20) :
    radialEvaluation I ε r (A + B) p =
      radialEvaluation I ε r A p + radialEvaluation I ε r B p := by
  simp only [radialEvaluation, AxisEvaluation.mixedSeries_add I hε A B _ _ hp]
  ring

theorem radialEvaluation_sub (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A B : AxisSpace I ε) {p : ℝ × ℝ} (hp : |p.1| < 20) :
    radialEvaluation I ε r (A - B) p =
      radialEvaluation I ε r A p - radialEvaluation I ε r B p := by
  simp only [radialEvaluation, AxisEvaluation.mixedSeries_sub I hε A B _ _ hp]
  ring

theorem radialEvaluation_smul (I : Window) (ε c : ℝ)
    (r : ℕ) (A : AxisSpace I ε) (p : ℝ × ℝ) :
    radialEvaluation I ε r (c • A) p = c * radialEvaluation I ε r A p := by
  simp only [radialEvaluation, AxisEvaluation.mixedSeries_smul]
  ring

/-- Fixed axis data have radial degree zero; parameter dependence remains unrestricted. -/
def RadiallyConstant (I : Window) (ε : ℝ) (A : AxisSpace I ε) : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∀ η : ℝ, η ∈ I.interval → coefficient I (weight ε) A n η = 0

theorem profile_radiallyConstant (I : Window) (ε : ℝ) (A : AxisSpace I ε)
    (hA : RadiallyConstant I ε A) (Y : ℝ) {η : ℝ} (hη : η ∈ I.interval) :
    AxisEvaluation.profile I ε A (Y, η) = coefficient I (weight ε) A 0 η := by
  unfold AxisEvaluation.profile
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp only [hA n hn η hη, mul_zero]

theorem radialEvaluation_constant (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A : AxisSpace I ε) (hA : RadiallyConstant I ε A)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε r A p = 0 := by
  rw [radialEvaluation_eq I hε r A hp]
  have hfun : (fun Y => AxisEvaluation.profile I ε A (Y, p.2)) =
      fun _ : ℝ => coefficient I (weight ε) A 0 p.2 := by
    funext Y
    exact profile_radiallyConstant I ε A hA Y ⟨hp.2.1.le, hp.2.2.le⟩
  simp only [radialDifferential, partialY, hfun]
  norm_num [iteratedDeriv_succ, iteratedDeriv_zero]

theorem coefficient_product_constant (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A B : AxisSpace I ε) (hA : RadiallyConstant I ε A)
    (n : ℕ) {η : ℝ} (hη : η ∈ I.interval) :
    coefficient I (weight ε) (AxisOperators.product I hε A B) n η =
      coefficient I (weight ε) A 0 η * coefficient I (weight ε) B n η := by
  classical
  rw [AxisOperators.coefficient_product I hε A B n hη]
  apply Finset.sum_eq_single (0, n)
  · intro ij hij hne
    have hi : ij.1 ≠ 0 := by
      intro hi
      have hs := Finset.mem_antidiagonal.mp hij
      apply hne
      apply Prod.ext
      · exact hi
      · simpa only [hi, zero_add] using hs
    simp only [hA ij.1 hi η hη, zero_mul]
  · simp

/-- A fixed parameter multiplier commutes with the radial differential expression. -/
theorem radialEvaluation_product_constant (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (A B : AxisSpace I ε) (hA : RadiallyConstant I ε A)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε r (AxisOperators.product I hε A B) p =
      AxisEvaluation.profile I ε A p * radialEvaluation I ε r B p := by
  have hη : p.2 ∈ I.interval := ⟨hp.2.1.le, hp.2.2.le⟩
  have hY : |p.1| < 20 := abs_lt.mpr hp.1
  change AxisEvaluationAlgebra.radialValue I ε r (AxisOperators.product I hε A B) p =
    AxisEvaluation.profile I ε A p * AxisEvaluationAlgebra.radialValue I ε r B p
  rw [AxisEvaluationAlgebra.radialValue_series I hε r _ hY,
    AxisEvaluationAlgebra.radialValue_series I hε r _ hY,
    profile_radiallyConstant I ε A hA p.1 hη, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [coefficient_product_constant I hε A B hA (n + 1) hη]
  ring

theorem profile_neg (I : Window) (ε : ℝ) (A : AxisSpace I ε) (p : ℝ × ℝ) :
    AxisEvaluation.profile I ε (-A) p = -AxisEvaluation.profile I ε A p := by
  simpa only [neg_one_smul, neg_one_mul] using profile_smul I ε (-1) A p

theorem radialEvaluation_regularInverse (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A : AxisSpace I ε)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε r (AxisOperators.regularInverse I hε r hr A) p =
      AxisEvaluation.profile I ε A p :=
  AxisEvaluationAlgebra.regularInverse_equation I hε r hr A
    (abs_lt.mpr hp.1) ⟨hp.2.1.le, hp.2.2.le⟩

theorem radialEvaluation_param (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε r (AxisOperators.inverseParamProduct I hε r hr A B) p =
      partialEta (AxisEvaluation.profile I ε A) p * AxisEvaluation.profile I ε B p := by
  rw [partialEta_profile I hε A hp]
  exact AxisEvaluationAlgebra.inverseParamProduct_equation I hε r hr A B
    (abs_lt.mpr hp.1) ⟨hp.2.1.le, hp.2.2.le⟩

theorem radialEvaluation_dot (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε r (AxisOperators.inverseDotProduct I hε r hr A B) p =
      AxisEvaluation.profile I ε A p * (p.1 * partialY (AxisEvaluation.profile I ε B) p) := by
  rw [partialY_profile I hε B hp]
  exact AxisEvaluationAlgebra.inverseDotProduct_equation I hε r hr A B
    (abs_lt.mpr hp.1) ⟨hp.2.1.le, hp.2.2.le⟩

theorem radialEvaluation_mixed (I : Window) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r) (A B : AxisSpace I ε)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε r (AxisOperators.inverseMixed I hε r hr A B) p =
      partialEta (AxisEvaluation.profile I ε A) p *
        (p.1 * partialY (AxisEvaluation.profile I ε B) p) := by
  rw [partialEta_profile I hε A hp, partialY_profile I hε B hp]
  exact AxisEvaluationAlgebra.inverseMixed_equation I hε r hr A B
    (abs_lt.mpr hp.1) ⟨hp.2.1.le, hp.2.2.le⟩

/-- Fixed parameter functions appearing in the scaled natural equations. -/
structure ParameterData where
  /-- A of `ParameterData`, of type `ℝ`. -/
  A : ℝ
  /-- Domain data of `ParameterData`, of type `ℝ`. -/
  D : ℝ
  /-- Step-size parameter of `ParameterData`, of type `ℝ`. -/
  h : ℝ
  /-- Chi of `ParameterData`, of type `ℝ → ℝ`. -/
  chi : ℝ → ℝ
  /-- D of `ParameterData`, of type `ℝ → ℝ`. -/
  d : ℝ → ℝ
  /-- Inverse L of `ParameterData`, of type `ℝ → ℝ`. -/
  inverseL : ℝ → ℝ
  /-- U star of `ParameterData`, of type `ℝ → ℝ`. -/
  uStar : ℝ → ℝ
  /-- U star eta of `ParameterData`, of type `ℝ → ℝ`. -/
  uStarEta : ℝ → ℝ
  /-- W star of `ParameterData`, of type `ℝ → ℝ`. -/
  wStar : ℝ → ℝ
  /-- H star of `ParameterData`, of type `ℝ → ℝ`. -/
  hStar : ℝ → ℝ
  /-- Kappa of `ParameterData`, of type `ℝ → ℝ`. -/
  kappa : ℝ → ℝ
  /-- Z star of `ParameterData`, of type `ℝ → ℝ`. -/
  zStar : ℝ → ℝ

/-- The actual parameter function represented by the zeroth radial coefficient. -/
def inputValue (I : Window) (ε : ℝ) (A : AxisSpace I ε) : ℝ → ℝ :=
  coefficient I (weight ε) A 0

/-- The fixed fields of the integrated system, interpreted as actual functions. -/
def parameters (I : Window) (ε : ℝ) (χ : AxisSpace I ε)
    (d : AxisContraction.AxisData (AxisSpace I ε)) : ParameterData where
  A := d.A
  D := d.D
  h := d.h
  chi := inputValue I ε χ
  d := inputValue I ε d.d
  inverseL := inputValue I ε d.inverseL
  uStar := inputValue I ε d.uStar
  uStarEta := inputValue I ε d.uStarEta
  wStar := inputValue I ε d.wStar
  hStar := inputValue I ε d.hStar
  kappa := inputValue I ε d.normalizedGradient
  zStar := inputValue I ε d.zStar

/-- Fixed analytic input data are independent of the radial coordinate.
These hypotheses concern only the given inputs, never the unknown profiles. -/
structure CompatibleData (I : Window) (ε : ℝ) (χ : AxisSpace I ε)
    (d : AxisContraction.AxisData (AxisSpace I ε)) : Prop where
  chi_radial : RadiallyConstant I ε χ
  one_radial : RadiallyConstant I ε d.one
  eta_radial : RadiallyConstant I ε d.eta
  d_radial : RadiallyConstant I ε d.d
  inverseL_radial : RadiallyConstant I ε d.inverseL
  uStar_radial : RadiallyConstant I ε d.uStar
  uStarEta_radial : RadiallyConstant I ε d.uStarEta
  wStar_radial : RadiallyConstant I ε d.wStar
  hStar_radial : RadiallyConstant I ε d.hStar
  gradient_radial : RadiallyConstant I ε d.normalizedGradient
  zStar_radial : RadiallyConstant I ε d.zStar
  one_value : ∀ η ∈ I.interval, inputValue I ε d.one η = 1
  eta_value : ∀ η ∈ I.interval, inputValue I ε d.eta η = η
  uStarEta_value : ∀ η ∈ Ioo I.left I.right,
    inputValue I ε d.uStarEta η = deriv (inputValue I ε d.uStar) η

/-- The pressure source in the complete coefficient space. -/
def pressureSource (I : Window) {ε : ℝ} (hε : 0 < ε)
    (a Φ : AxisSpace I ε) : AxisSpace I ε :=
  AxisOperators.product I hε (AxisOperators.product I hε a a)
    (AxisOperators.product I hε Φ Φ)

/-- Pressure coefficient, given by `AxisOperators.primitive I hε (pressureSource I hε a Φ)`. -/
def pressureCoefficient (I : Window) {ε : ℝ} (hε : 0 < ε)
    (a Φ : AxisSpace I ε) : AxisSpace I ε :=
  AxisOperators.primitive I hε (pressureSource I hε a Φ)

/-- The reconstructed axial profile `U=U*+Λ⁻¹u`. -/
def reconstructedU (d : ParameterData) (t : ℝ) (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  d.uStar p.2 + t * u p

/-- The actual transport coefficient using the regular radial average. -/
def reconstructedW (d : ParameterData) (t : ℝ) (B : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  d.wStar p.2 - t * ((2 * d.D * p.2) * B p + d.d p.2 * partialEta B p)

/-- Reconstructed H, given by `d.hStar p.2 + t * d.d p.2 * u p`. -/
def reconstructedH (d : ParameterData) (t : ℝ) (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  d.hStar p.2 + t * d.d p.2 * u p

/-- The first remainder in equation (17), using ordinary derivatives of
actual functions and `κ=ξ₀/Λ`. -/
def angularRemainder (d : ParameterData) (t : ℝ)
    (Φ u B : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  d.inverseL p.2 *
    ((reconstructedW d t B p + d.h * (1 - 2 * p.2 * reconstructedU d t u p) +
        d.d p.2 * u p * d.kappa p.2) * Φ p +
      reconstructedW d t B p * (p.1 * partialY Φ p) +
      reconstructedH d t u p * partialEta Φ p)

/-- The expanded second remainder in equation (17), including all pressure
terms and the actual parameter derivative of the pressure correction. -/
def axialRemainder (d : ParameterData) (t : ℝ)
    (u B P : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  d.inverseL p.2 *
    (d.A * (1 - 4 * p.2 * d.uStar p.2) * u p -
      2 * d.A * p.2 * t * (u p) ^ 2 +
      reconstructedW d t B p * (p.1 * partialY u p) +
      d.hStar p.2 * partialEta u p + d.d p.2 * d.uStarEta p.2 * u p +
      t * d.d p.2 * u p * partialEta u p -
      4 * d.A * p.2 * P p + d.d p.2 * partialEta P p -
      2 * p.2 * (p.1 * partialY P p))

/-- The target is an equation for actual smooth profiles, together with the
regular-average and pressure identities that determine its auxiliary fields. -/
structure IsScaledSolution (I : Window) (d : ParameterData) (t : ℝ) (a : ℝ → ℝ)
    (Φ u B P : ℝ × ℝ → ℝ) : Prop where
  phi_smooth : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip I 20)
  u_smooth : ContDiffOn ℝ ∞ u (AxisEvaluation.strip I 20)
  average_smooth : ContDiffOn ℝ ∞ B (AxisEvaluation.strip I 20)
  pressure_smooth : ContDiffOn ℝ ∞ P (AxisEvaluation.strip I 20)
  phi_axis : ∀ η ∈ Ioo I.left I.right, Φ (0, η) = 1
  u_axis : ∀ η ∈ Ioo I.left I.right, u (0, η) = 0
  average_axis : ∀ η ∈ Ioo I.left I.right, B (0, η) = u (0, η)
  pressure_axis : ∀ η ∈ Ioo I.left I.right, P (0, η) = 0
  average_equation : ∀ p ∈ AxisEvaluation.strip I 20,
    B p + p.1 * partialY B p = u p
  pressure_equation : ∀ p ∈ AxisEvaluation.strip I 20,
    partialY P p = (a p.2) ^ 2 * (Φ p) ^ 2
  average_integral : ∀ p ∈ AxisEvaluation.strip I 20,
    p.1 * B p = ∫ y in (0 : ℝ)..p.1, u (y, p.2)
  pressure_integral : ∀ p ∈ AxisEvaluation.strip I 20,
    P p = ∫ y in (0 : ℝ)..p.1, (a p.2) ^ 2 * (Φ (y, p.2)) ^ 2
  angular_equation : ∀ p ∈ AxisEvaluation.strip I 20,
    2 * radialDifferential 2 Φ p = -d.chi p.2 * Φ p + t * angularRemainder d t Φ u B p
  axial_equation : ∀ p ∈ AxisEvaluation.strip I 20,
    2 * radialDifferential 1 u p = -d.inverseL p.2 * d.zStar p.2 + t * axialRemainder d t u B P p

theorem profile_inputValue (I : Window) (ε : ℝ) (A : AxisSpace I ε)
    (hA : RadiallyConstant I ε A) {p : ℝ × ℝ} (hη : p.2 ∈ I.interval) :
    AxisEvaluation.profile I ε A p = inputValue I ε A p.2 :=
  profile_radiallyConstant I ε A hA p.1 hη

/-- Differentiating the actual first integrated remainder gives precisely
the first scaled differential remainder, including the mixed term. -/
theorem angular_remainder_evaluation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) (t : ℝ) (a : AxisSpace I ε)
    (x : AxisSpace I ε × AxisSpace I ε) {p : ℝ × ℝ}
    (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε 2
        (AxisContraction.naturalRemainder (AxisContraction.coefficientOperators I hε)
          d (ContinuousLinearMap.id ℝ _) t a x).1 p =
      angularRemainder (parameters I ε χ d) t
        (AxisEvaluation.profile I ε x.1) (AxisEvaluation.profile I ε x.2)
        (AxisEvaluation.profile I ε (AxisOperators.average I hε x.2)) p := by
  have hY : |p.1| < 20 := abs_lt.mpr hp.1
  have hη : p.2 ∈ I.interval := ⟨hp.2.1.le, hp.2.2.le⟩
  have radd := fun A B => radialEvaluation_add I hε 2 A B hY
  have rsub := fun A B => radialEvaluation_sub I hε 2 A B hY
  have rsmul := fun c A => radialEvaluation_smul I ε c 2 A p
  have rj := fun A => radialEvaluation_regularInverse I hε 2 (by norm_num) A hp
  have rp := fun A B => radialEvaluation_param I hε 2 (by norm_num) A B hp
  have rd := fun A B => radialEvaluation_dot I hε 2 (by norm_num) A B hp
  have rm := fun A B => radialEvaluation_mixed I hε 2 (by norm_num) A B hp
  have rfactor := fun A => radialEvaluation_product_constant I hε 2 d.d A hd.d_radial hp
  have rinv := fun A => radialEvaluation_product_constant I hε 2 d.inverseL A hd.inverseL_radial hp
  have pmul := fun A B => AxisEvaluationAlgebra.profile_product I hε A B hY hη
  have padd := fun A B => profile_add I hε A B hY
  have psub := fun A B => profile_sub I hε A B hY
  have psmul := fun c A => profile_smul I ε c A p
  have pbase := fun A hA => profile_inputValue I ε A hA hη
  dsimp only [AxisContraction.naturalRemainder, AxisContraction.coefficientOperators,
    ContinuousLinearMap.id_apply]
  simp only [rinv, radd, rsub, rsmul, rj, rp, rd, rm, rfactor]
  simp only [AxisContraction.angularLinearCoefficient,
    AxisContraction.angularQuadraticCoefficient, AxisContraction.averageCoefficient,
    AxisContraction.angularSlowCoefficient,
    pmul, padd, psub, psmul]
  simp only [pbase d.one hd.one_radial, pbase d.eta hd.eta_radial,
    pbase d.d hd.d_radial, pbase d.inverseL hd.inverseL_radial,
    pbase d.uStar hd.uStar_radial, pbase d.wStar hd.wStar_radial,
    pbase d.hStar hd.hStar_radial, pbase d.normalizedGradient hd.gradient_radial,
    hd.one_value p.2 hη, hd.eta_value p.2 hη]
  simp only [angularRemainder, reconstructedW, reconstructedU, reconstructedH, parameters]
  ring

/-- Differentiating the second integrated remainder gives the complete
axial differential remainder, with the actual pressure derivatives. -/
theorem axial_remainder_evaluation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) (t : ℝ) (a : AxisSpace I ε)
    (x : AxisSpace I ε × AxisSpace I ε) {p : ℝ × ℝ}
    (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε 1
        (AxisContraction.naturalRemainder (AxisContraction.coefficientOperators I hε)
          d (ContinuousLinearMap.id ℝ _) t a x).2 p =
      axialRemainder (parameters I ε χ d) t
        (AxisEvaluation.profile I ε x.2)
        (AxisEvaluation.profile I ε (AxisOperators.average I hε x.2))
        (AxisEvaluation.profile I ε (pressureCoefficient I hε a x.1)) p := by
  have hY : |p.1| < 20 := abs_lt.mpr hp.1
  have hη : p.2 ∈ I.interval := ⟨hp.2.1.le, hp.2.2.le⟩
  have radd := fun A B => radialEvaluation_add I hε 1 A B hY
  have rsub := fun A B => radialEvaluation_sub I hε 1 A B hY
  have rsmul := fun c A => radialEvaluation_smul I ε c 1 A p
  have rj := fun A => radialEvaluation_regularInverse I hε 1 (by norm_num) A hp
  have rp := fun A B => radialEvaluation_param I hε 1 (by norm_num) A B hp
  have rd := fun A B => radialEvaluation_dot I hε 1 (by norm_num) A B hp
  have rm := fun A B => radialEvaluation_mixed I hε 1 (by norm_num) A B hp
  have rfactor := fun A => radialEvaluation_product_constant I hε 1 d.d A hd.d_radial hp
  have rinv := fun A => radialEvaluation_product_constant I hε 1 d.inverseL A hd.inverseL_radial hp
  have pmul := fun A B => AxisEvaluationAlgebra.profile_product I hε A B hY hη
  have padd := fun A B => profile_add I hε A B hY
  have psub := fun A B => profile_sub I hε A B hY
  have psmul := fun c A => profile_smul I ε c A p
  have pneg := fun A => profile_neg I ε A p
  have pbase := fun A hA => profile_inputValue I ε A hA hη
  have pparam := fun A => AxisEvaluationAlgebra.parameterPrimitive_eq_deriv_eta
    I hε A hp.1 hp.2
  have pmy (A : AxisSpace I ε) :
      AxisEvaluation.profile I ε (AxisOperators.mulY I hε A) p =
        p.1 * partialY (AxisEvaluation.profile I ε (AxisOperators.primitive I hε A)) p := by
    rw [AxisEvaluationAlgebra.profile_mulY I hε A hY hη,
      partialY_profile I hε _ hp, AxisEvaluationAlgebra.primitive_Y_value I hε A hY hη]
  dsimp only [AxisContraction.naturalRemainder, AxisContraction.coefficientOperators]
  simp only [rinv, radd, rsub, rsmul, rj, rp, rd, rm, rfactor]
  simp only [AxisContraction.axialLinearCoefficient, AxisContraction.axialQuadraticCoefficient,
    AxisContraction.averageCoefficient,
    pmul, padd, psub, psmul, pneg, pparam, pmy]
  simp only [pbase d.one hd.one_radial, pbase d.eta hd.eta_radial,
    pbase d.d hd.d_radial, pbase d.inverseL hd.inverseL_radial,
    pbase d.uStar hd.uStar_radial, pbase d.uStarEta hd.uStarEta_radial,
    pbase d.wStar hd.wStar_radial, pbase d.hStar hd.hStar_radial,
    hd.one_value p.2 hη, hd.eta_value p.2 hη]
  simp only [axialRemainder, reconstructedW, parameters, pressureCoefficient, pressureSource,
    partialEta]
  ring

/-- Both integrated remainders have exactly zero axis value. -/
theorem remainder_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (d : AxisContraction.AxisData (AxisSpace I ε)) (t : ℝ) (a : AxisSpace I ε)
    (x : AxisSpace I ε × AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    AxisEvaluation.profile I ε
        (AxisContraction.naturalRemainder (AxisContraction.coefficientOperators I hε)
          d (ContinuousLinearMap.id ℝ _) t a x).1 (0, η) = 0 ∧
      AxisEvaluation.profile I ε
        (AxisContraction.naturalRemainder (AxisContraction.coefficientOperators I hε)
          d (ContinuousLinearMap.id ℝ _) t a x).2 (0, η) = 0 := by
  have hY : |(0 : ℝ)| < 20 := by norm_num
  have padd := fun A B => profile_add I hε A B (p := (0, η)) hY
  have psub := fun A B => profile_sub I hε A B (p := (0, η)) hY
  have psmul := fun c A => profile_smul I ε c A (0, η)
  have pmul := fun A B => AxisEvaluationAlgebra.profile_product I hε A B hY hη
  have pj := fun r hr A => AxisEvaluationAlgebra.regularInverse_axis_zero I hε r hr A hη
  have pp := fun r hr A B => AxisEvaluationAlgebra.inverseParamProduct_axis_zero I hε r hr A B hη
  have pd := fun r hr A B => AxisEvaluationAlgebra.inverseDotProduct_axis_zero I hε r hr A B hη
  have pm := fun r hr A B => AxisEvaluationAlgebra.inverseMixed_axis_zero I hε r hr A B hη
  constructor <;>
    dsimp only [AxisContraction.naturalRemainder, AxisContraction.coefficientOperators,
      ContinuousLinearMap.id_apply] <;>
    simp only [padd, psub, psmul, pmul, pj, pp, pd, pm, mul_zero,
      add_zero, sub_zero]

theorem naturalOperator_axis_zero (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) {η : ℝ} (hη : η ∈ I.interval) :
    AxisEvaluation.profile I ε (AxisResolvent.naturalOperator I hε χ A) (0, η) = 0 := by
  simp only [AxisResolvent.naturalOperator, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, profile_smul,
    AxisEvaluationAlgebra.regularInverse_axis_zero I hε _ _ _ hη, mul_zero]

theorem radialEvaluation_naturalOperator (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) (hχ : RadiallyConstant I ε χ)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    radialEvaluation I ε 2 (AxisResolvent.naturalOperator I hε χ A) p =
      (1 / 2 : ℝ) * inputValue I ε χ p.2 * AxisEvaluation.profile I ε A p := by
  simp only [AxisResolvent.naturalOperator, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, radialEvaluation_smul]
  rw [radialEvaluation_regularInverse I hε 2 (by norm_num) _ hp,
    AxisEvaluationAlgebra.profile_product I hε χ A (abs_lt.mpr hp.1) ⟨hp.2.1.le, hp.2.2.le⟩,
    profile_inputValue I ε χ hχ ⟨hp.2.1.le, hp.2.2.le⟩]
  ring

theorem pressure_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (a Φ : AxisSpace I ε) (ha : RadiallyConstant I ε a)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    partialY (AxisEvaluation.profile I ε (pressureCoefficient I hε a Φ)) p =
      (inputValue I ε a p.2) ^ 2 * (AxisEvaluation.profile I ε Φ p) ^ 2 := by
  have hY : |p.1| < 20 := abs_lt.mpr hp.1
  have hη : p.2 ∈ I.interval := ⟨hp.2.1.le, hp.2.2.le⟩
  rw [pressureCoefficient, partialY_profile I hε _ hp,
    AxisEvaluationAlgebra.primitive_Y_value I hε _ hY hη]
  simp only [pressureSource, AxisEvaluationAlgebra.profile_product I hε _ _ hY hη,
    profile_inputValue I ε a ha hη]
  ring

/-- The pressure field is the ordinary integral from the axis, rather
than merely a formal coefficient primitive. -/
theorem pressure_integral (I : Window) {ε : ℝ} (hε : 0 < ε)
    (a Φ : AxisSpace I ε) (ha : RadiallyConstant I ε a)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip I 20) :
    AxisEvaluation.profile I ε (pressureCoefficient I hε a Φ) p =
      ∫ y in (0 : ℝ)..p.1,
        (inputValue I ε a p.2) ^ 2 * (AxisEvaluation.profile I ε Φ (y, p.2)) ^ 2 := by
  rw [pressureCoefficient, AxisEvaluationAlgebra.primitive_integral I hε _ hp.1 hp.2]
  apply intervalIntegral.integral_congr
  intro y hy
  have hY : |y| < 20 := abs_lt.mpr (AxisEvaluationAlgebra.radial_segment_mem hp.1 hy)
  have hη : p.2 ∈ I.interval := ⟨hp.2.1.le, hp.2.2.le⟩
  simp only [pressureSource, AxisEvaluationAlgebra.profile_product I hε _ _ hY hη,
    profile_inputValue I ε a ha (p := (y, p.2)) hη]
  ring

/-- The integrated coefficient equations give the literal scaled equations
for actual smooth functions on the open real strip. -/
theorem integrated_solution (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) (t s : ℝ) (hst : 2 * s = t)
    (a : AxisSpace I ε) (ha : RadiallyConstant I ε a)
    (x : AxisSpace I ε × AxisSpace I ε)
    (hφ : x.1 + AxisResolvent.naturalOperator I hε χ x.1 =
      d.one + s • (AxisContraction.naturalRemainder
        (AxisContraction.coefficientOperators I hε) d (ContinuousLinearMap.id ℝ _) t a x).1)
    (hu : x.2 = -(1 / 2 : ℝ) • AxisOperators.regularInverse I hε 1 (by norm_num)
        (AxisOperators.product I hε d.inverseL d.zStar) +
      s • (AxisContraction.naturalRemainder
        (AxisContraction.coefficientOperators I hε) d (ContinuousLinearMap.id ℝ _) t a x).2) :
    IsScaledSolution I (parameters I ε χ d) t (inputValue I ε a)
      (AxisEvaluation.profile I ε x.1) (AxisEvaluation.profile I ε x.2)
      (AxisEvaluation.profile I ε (AxisOperators.average I hε x.2))
      (AxisEvaluation.profile I ε (pressureCoefficient I hε a x.1)) := by
  refine {
    phi_smooth := AxisEvaluation.profile_smooth I hε x.1
    u_smooth := AxisEvaluation.profile_smooth I hε x.2
    average_smooth := AxisEvaluation.profile_smooth I hε _
    pressure_smooth := AxisEvaluation.profile_smooth I hε _
    phi_axis := ?_
    u_axis := ?_
    average_axis := ?_
    pressure_axis := ?_
    average_equation := ?_
    pressure_equation := fun p hp => pressure_equation I hε a x.1 ha hp
    average_integral := ?_
    pressure_integral := fun p hp => pressure_integral I hε a x.1 ha hp
    angular_equation := ?_
    axial_equation := ?_ }
  · intro η hη
    have hηc : η ∈ I.interval := ⟨hη.1.le, hη.2.le⟩
    have h0 : |(0 : ℝ)| < 20 := by norm_num
    have he := congrArg (fun A => AxisEvaluation.profile I ε A (0, η)) hφ
    simp only [profile_add I hε _ _ (p := (0, η)) h0,
      naturalOperator_axis_zero I hε χ x.1 hηc,
      profile_smul, (remainder_axis_zero I hε d t a x hηc).1,
      profile_inputValue I ε d.one hd.one_radial (p := (0, η)) hηc,
      hd.one_value η hηc] at he
    simpa only [add_zero, mul_zero] using he
  · intro η hη
    have hηc : η ∈ I.interval := ⟨hη.1.le, hη.2.le⟩
    have h0 : |(0 : ℝ)| < 20 := by norm_num
    have he := congrArg (fun A => AxisEvaluation.profile I ε A (0, η)) hu
    simp only [profile_add I hε _ _ (p := (0, η)) h0, profile_smul,
      AxisEvaluationAlgebra.regularInverse_axis_zero I hε 1 (by norm_num) _ hηc,
      (remainder_axis_zero I hε d t a x hηc).2] at he
    simpa only [mul_zero, add_zero] using he
  · intro η hη
    exact AxisEvaluationAlgebra.average_axis I hε x.2 ⟨hη.1.le, hη.2.le⟩
  · intro η hη
    exact AxisEvaluationAlgebra.primitive_axis_zero I hε _ ⟨hη.1.le, hη.2.le⟩
  · intro p hp
    rw [partialY_profile I hε _ hp]
    exact AxisEvaluationAlgebra.average_equation I hε x.2 (abs_lt.mpr hp.1)
      ⟨hp.2.1.le, hp.2.2.le⟩
  · intro p hp
    exact AxisEvaluationAlgebra.average_integral I hε x.2 hp.1 hp.2
  · intro p hp
    have hY : |p.1| < 20 := abs_lt.mpr hp.1
    have he := congrArg (fun A => radialEvaluation I ε 2 A p) hφ
    simp only [radialEvaluation_add I hε 2 _ _ hY,
      radialEvaluation_naturalOperator I hε χ x.1 hd.chi_radial hp,
      radialEvaluation_constant I hε 2 d.one hd.one_radial hp,
      radialEvaluation_smul, angular_remainder_evaluation I hε χ d hd t a x hp,
      radialEvaluation_eq I hε 2 x.1 hp] at he
    change 2 * radialDifferential 2 (AxisEvaluation.profile I ε x.1) p =
      -inputValue I ε χ p.2 * AxisEvaluation.profile I ε x.1 p + _
    calc
      _ = -inputValue I ε χ p.2 * AxisEvaluation.profile I ε x.1 p +
          (2 * s) * angularRemainder (parameters I ε χ d) t
            (AxisEvaluation.profile I ε x.1) (AxisEvaluation.profile I ε x.2)
            (AxisEvaluation.profile I ε (AxisOperators.average I hε x.2)) p := by
        linarith only [he]
      _ = _ := by rw [hst]
  · intro p hp
    have hY : |p.1| < 20 := abs_lt.mpr hp.1
    have hη : p.2 ∈ I.interval := ⟨hp.2.1.le, hp.2.2.le⟩
    have he := congrArg (fun A => radialEvaluation I ε 1 A p) hu
    simp only [radialEvaluation_add I hε 1 _ _ hY,
      radialEvaluation_smul,
      radialEvaluation_regularInverse I hε 1 (by norm_num) _ hp,
      axial_remainder_evaluation I hε χ d hd t a x hp,
      AxisEvaluationAlgebra.profile_product I hε d.inverseL d.zStar hY hη,
      profile_inputValue I ε d.inverseL hd.inverseL_radial hη,
      profile_inputValue I ε d.zStar hd.zStar_radial hη,
      radialEvaluation_eq I hε 1 x.2 hp] at he
    change 2 * radialDifferential 1 (AxisEvaluation.profile I ε x.2) p =
      -inputValue I ε d.inverseL p.2 * inputValue I ε d.zStar p.2 + _
    calc
      _ = -inputValue I ε d.inverseL p.2 * inputValue I ε d.zStar p.2 +
          (2 * s) * axialRemainder (parameters I ε χ d) t
            (AxisEvaluation.profile I ε x.2)
            (AxisEvaluation.profile I ε (AxisOperators.average I hε x.2))
            (AxisEvaluation.profile I ε (pressureCoefficient I hε a x.1)) p := by
        linarith only [he]
      _ = _ := by rw [hst]

/-- The leading pair defined using the proved angular resolvent. -/
def referenceCoefficients (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε)) :
    AxisSpace I ε × AxisSpace I ε :=
  AxisContraction.referencePair (AxisContraction.coefficientOperators I hε) d
    (AxisResolvent.naturalResolvent I hε χ)

/-- The limiting system is stated directly for actual functions. -/
structure IsLeadingSolution (I : Window) (d : ParameterData)
    (Φ u : ℝ × ℝ → ℝ) : Prop where
  phi_smooth : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip I 20)
  u_smooth : ContDiffOn ℝ ∞ u (AxisEvaluation.strip I 20)
  phi_axis : ∀ η ∈ Ioo I.left I.right, Φ (0, η) = 1
  u_axis : ∀ η ∈ Ioo I.left I.right, u (0, η) = 0
  angular_equation : ∀ p ∈ AxisEvaluation.strip I 20,
    2 * radialDifferential 2 Φ p = -d.chi p.2 * Φ p
  axial_equation : ∀ p ∈ AxisEvaluation.strip I 20,
    2 * radialDifferential 1 u p = -d.inverseL p.2 * d.zStar p.2

/-- The profiles used in the error estimate really solve the regular
leading equations with the prescribed axis data. -/
theorem reference_isLeadingSolution (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) :
    IsLeadingSolution I (parameters I ε χ d)
      (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1)
      (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).2) := by
  have hzero : RadiallyConstant I ε (0 : AxisSpace I ε) := by
    intro n hn η hη
    simp [coefficient]
  have hφ : (referenceCoefficients I hε χ d).1 +
      AxisResolvent.naturalOperator I hε χ (referenceCoefficients I hε χ d).1 =
      d.one + (0 : ℝ) • (AxisContraction.naturalRemainder
        (AxisContraction.coefficientOperators I hε) d (ContinuousLinearMap.id ℝ _) 0 0
          (referenceCoefficients I hε χ d)).1 := by
    simpa only [referenceCoefficients, AxisContraction.referencePair, zero_smul, add_zero] using
      AxisResolvent.naturalResolvent_equation I hε χ d.one
  have hu : (referenceCoefficients I hε χ d).2 =
      -(1 / 2 : ℝ) • AxisOperators.regularInverse I hε 1 (by norm_num)
        (AxisOperators.product I hε d.inverseL d.zStar) +
      (0 : ℝ) • (AxisContraction.naturalRemainder
        (AxisContraction.coefficientOperators I hε) d (ContinuousLinearMap.id ℝ _) 0 0
          (referenceCoefficients I hε χ d)).2 := by
    simp only [zero_smul, add_zero]
    rfl
  have hs := integrated_solution I hε χ d hd 0 0 (by norm_num) 0 hzero
    (referenceCoefficients I hε χ d) hφ hu
  refine ⟨hs.phi_smooth, hs.u_smooth, hs.phi_axis, hs.u_axis, ?_, ?_⟩
  · intro p hp
    simpa only [zero_mul, add_zero] using hs.angular_equation p hp
  · intro p hp
    simpa only [zero_mul, add_zero] using hs.axial_equation p hp

/-- A fixed finite constant computed from the input norms and the genuine
bounded operators. It is independent of `Λ` and of the amplitude in its norm ball. -/
def errorConstant (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (M : ℝ) (hM : 0 ≤ M) : ℝ :=
  AxisContraction.remainderBound (AxisContraction.coefficientOperators I hε) d
    (AxisResolvent.naturalResolvent I hε χ)
    (‖referenceCoefficients I hε χ d‖ + 1) M (by positivity) hM

theorem errorConstant_nonneg (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (M : ℝ) (hM : 0 ≤ M) : 0 ≤ errorConstant I hε χ d M hM :=
  AxisContraction.remainderBound_nonneg _ _ _ _ _ _ _

/-- Simultaneous estimates for every ordinary mixed derivative, uniform on
each smaller radial interval and on the whole open parameter interval. -/
def UniformMixedError (I : Window) (ε K : ℝ)
    (Φ u Φ₀ u₀ : ℝ × ℝ → ℝ) : Prop :=
  ∀ R : ℝ, 1 ≤ R → R < 20 → ∀ k m : ℕ, ∀ p : ℝ × ℝ,
    |p.1| ≤ R → p.2 ∈ Ioo I.left I.right →
      |mixedDerivative k m Φ p - mixedDerivative k m Φ₀ p| ≤
          AxisEvaluation.jetBound ε R k m * K ∧
        |mixedDerivative k m u p - mixedDerivative k m u₀ p| ≤
          AxisEvaluation.jetBound ε R k m * K

theorem uniformMixedError_of_norm (I : Window) {ε : ℝ} (hε : 0 < ε)
    (x x₀ : AxisSpace I ε × AxisSpace I ε) (K : ℝ) (hK : ‖x - x₀‖ ≤ K) :
    UniformMixedError I ε K
      (AxisEvaluation.profile I ε x.1) (AxisEvaluation.profile I ε x.2)
      (AxisEvaluation.profile I ε x₀.1) (AxisEvaluation.profile I ε x₀.2) := by
  intro R hR hR20 k m p hY hη
  constructor
  · simpa only [mixedDerivative, Real.norm_eq_abs] using
      AxisContraction.evaluated_mixed_error I hε hR hR20 x.1 x₀.1 K
        ((norm_fst_le (x - x₀)).trans hK) k m hY hη
  · simpa only [mixedDerivative, Real.norm_eq_abs] using
      AxisContraction.evaluated_mixed_error I hε hR hR20 x.2 x₀.2 K
        ((norm_snd_le (x - x₀)).trans hK) k m hY hη

/-- Actual smooth natural-axis profiles exist for every sufficiently large
`Λ`, uniformly over all radially constant angular amplitudes in a fixed norm
ball. The conclusion is a differential/integral system for real functions,
and its error estimate concerns their ordinary derivatives of every order. -/
theorem exists_scaled_profiles (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (d : AxisContraction.AxisData (AxisSpace I ε))
    (hd : CompatibleData I ε χ d) (M : ℝ) (hM : 0 ≤ M) :
    ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
      ∀ a : AxisSpace I ε, ‖a‖ ≤ M → RadiallyConstant I ε a →
      ∃ Φ u B P : ℝ × ℝ → ℝ,
        IsScaledSolution I (parameters I ε χ d) (1 / Λ) (inputValue I ε a) Φ u B P ∧
        UniformMixedError I ε (errorConstant I hε χ d M hM / (2 * Λ))
          Φ u (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).1)
          (AxisEvaluation.profile I ε (referenceCoefficients I hε χ d).2) := by
  obtain ⟨Λ₀, hΛ₀, hexists⟩ := AxisContraction.natural_axis_profiles I hε χ d M hM
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ a ha harad
  obtain ⟨x, _, herr, hφ, hu, _, _⟩ := hexists Λ hΛ a ha
  have hscale : 2 * (1 / (2 * Λ)) = 1 / Λ := by
    field_simp [(hΛ₀.trans_le hΛ).ne']
  refine ⟨AxisEvaluation.profile I ε x.1, AxisEvaluation.profile I ε x.2,
    AxisEvaluation.profile I ε (AxisOperators.average I hε x.2),
    AxisEvaluation.profile I ε (pressureCoefficient I hε a x.1),
    integrated_solution I hε χ d hd (1 / Λ) (1 / (2 * Λ)) hscale a harad x hφ hu, ?_⟩
  exact uniformMixedError_of_norm I hε x (referenceCoefficients I hε χ d)
    (errorConstant I hε χ d M hM / (2 * Λ)) herr

end NavierStokes.NaturalAxisBridge

end
