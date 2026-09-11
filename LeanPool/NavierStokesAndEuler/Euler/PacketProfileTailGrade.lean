/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailActual
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieceBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailFields
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderLinearTermBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderConvolution
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientBounds

/-! Uniform profile budgets bound each literal residual grade of the finite packet. -/

section

/-! Bounds for the actual advection products in the surviving finite packet tail. -/

section

/-! Uniform bounds on the actual finite velocity jets, including the terminal corrector. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic

theorem KnownPiece.profile_le_coarse {K : Type*} [TopologicalSpace K]
    (k : KnownPiece) (S : Scales K) (i : ℕ) (hi : 1 ≤ i) (t : K) :
    k.profile S i t ≤ S.H0^(2*i) := by
  apply (k.profile_le_envelope S i t).trans
  cases k <;> first | exact S.high_le_coarse i hi t | exact S.mean_le_coarse i t

namespace PrefixBound

variable {P T : ℝ} [Fact (0 < P)] {p : ℕ} {a : ℕ → Profile}
  {F : PrefixFields P T p a} {hT : 0 ≤ T} {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (B : PrefixBound F hT S R)

include B

theorem piece_unnormalized (hR : 1 ≤ R) (k : KnownPiece) (i : ℕ) (hi : 1 ≤ i) :
    (F.piece k i).WordBound 6 R (S.H0^(2*i)) (highShift i) := by
  have h := (B.piece (zero_le_one.trans hR) k i).remove_profile hT (k.profile S i) (k.profile_pos S
      i)
    (S.H0^(2*i)) (pow_nonneg S.H0_pos.le _) (k.profile_le_coarse S i hi)
  have h' : (F.piece k i).WordBound 6 R (S.H0^(2*i)) (k.shift i) := by simpa only [mul_one] using h
  exact h'.mono_shift hR (pow_nonneg S.H0_pos.le _) (k.shift_le_high i)

theorem knownJet_bound (O : Operators) (hp : 2 ≤ p) (hR : 1 ≤ R)
    (hc : (a 0).corrector = 0) (hb : (a 1).mean = 0) (i : ℕ) :
    (F.knownJet O (by omega) i).field.WordBound 6 R (3*S.H0^(2*i)) (highShift i) := by
  let J := F.knownJet O (by omega) i
  by_cases hi0 : i = 0
  · subst i
    have hz : ∀ (t : Icc (0 : ℝ) T) x θ, J.raw (t,(x,θ)) = 0 := by
      intro t x θ
      have hj := (J.value_eq t x θ).symm
      change J.raw (t,(x,θ)) = _ at hj
      rw [hj]
      simp [knownJets,history,velocityJet,show 0 < p by omega]
    exact (Field.wordBound_of_zero J.field hz 6 R (highShift 0)).mono_amplitude
      (zero_le_one.trans hR) (by norm_num : (0 : ℝ) ≤ 3*S.H0^(2*0))
  · have hi : 1 ≤ i := by omega
    have hhi := B.piece_unnormalized hR .high i hi
    have hme := B.piece_unnormalized hR .mean i hi
    have hco := B.piece_unnormalized hR .corrector i hi
    have hs := (hhi.add hme).add hco
    have he : S.H0^(2*i)+S.H0^(2*i)+S.H0^(2*i) = 3*S.H0^(2*i) := by ring
    rw [he] at hs
    apply hs.ofRawEq J.field
    intro t x θ
    exact (J.value_eq t x θ).symm.trans
      (congrArg Prod.fst (knownJets_eq_pieces O p hp a hc hb (t,(x,θ)) i))

end PrefixBound
end EulerPacketCylinderField

end
end

end

section

/-! The literal advection fields obey the same fixed coefficient costs before the final tail split.
-/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.CoefficientBudget

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerParameterWordGevrey EulerCylinderScalarPrimitive

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {C : CoefficientData P T O}
  (BC : CoefficientBudget C) {J K : Domain → VectorJet}
  (G : SpatialJetField P T J) (H : SpatialJetField P T K)

theorem slow_unnormalized_bound {R A B : ℝ} {d e : ℕ}
    (hG : G.field.WordBound 6 R A d) (hH : H.field.WordBound 6 R B e)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R) :
    (SpatialJetField.slowAdvection C.inverse G H).WordBound 6 R (BC.slowCost*A*B) (d+e+1) := by
  have hm := hG.multiply C.inverse BC.Rc BC.amplitude BC.Rc_nonneg BC.amplitude_nonneg hA hRc
      BC.inverse_bound
  have ham : 0 ≤ 3*sobolevCoefficientAmplitude (Fin 4) 6 BC.Rc BC.amplitude*A :=
    mul_nonneg BC.multiplierCost_nonneg hA
  have hs := (hm.spatialTransport hH hR ham hB).of_path_eq
    (SpatialJetField.slowAdvection C.inverse G H) rfl
  have he : 9*EulerCylinderPathProduct.productBlockConstant P *
      (3*sobolevCoefficientAmplitude (Fin 4) 6 BC.Rc BC.amplitude*A)*B = BC.slowCost*A*B := by
    unfold slowCost multiplierCost
    ring
  simpa only [he] using hs

theorem fast_unnormalized_bound {R A B : ℝ} {d e : ℕ}
    (hG : G.field.WordBound 6 R A d) (hH : H.field.WordBound 6 R B e)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R) :
    (SpatialJetField.fastAdvection C.normal G H).WordBound 6 R (BC.fastCost*A*B) (d+e+1) := by
  have hm := hG.multiply C.normal.normalMatrix BC.Rc BC.amplitude BC.Rc_nonneg BC.amplitude_nonneg
      hA hRc
    (C.normal.normalMatrix_bound BC.Rc BC.amplitude BC.normal_bound)
  have hd := hH.derivative 0
  have ham : 0 ≤ 3*sobolevCoefficientAmplitude (Fin 4) 6 BC.Rc BC.amplitude*A :=
    mul_nonneg BC.multiplierCost_nonneg hA
  have hs := (hm.scalarProduct hd scalarProject (le_of_eq scalarProject_norm) hR ham hB).of_path_eq
    (SpatialJetField.fastAdvection C.normal G H) rfl
  have he : 3*EulerCylinderPathProduct.productBlockConstant P *
      (3*sobolevCoefficientAmplitude (Fin 4) 6 BC.Rc BC.amplitude*A)*B = BC.fastCost*A*B := by
    unfold fastCost multiplierCost
    ring
  simpa only [he,Nat.add_assoc] using hs

end EulerPacketCylinderField.CoefficientBudget

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic EulerParameterWordGevrey

theorem tail_product_amplitude (H c C : ℝ) (hH : 1 ≤ H) (hc : 0 ≤ c) (hcC : c ≤ C)
    (i j n : ℕ) (hij : i + j ≤ n + 1) :
    c*(3*H^(2*i))*(3*H^(2*j)) ≤ 9*C*H^(2*n+2) := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hC : 0 ≤ C := hc.trans hcC
  calc
    _ = 9*c*H^(2*(i+j)) := by rw [Nat.mul_add,pow_add]; ring
    _ ≤ 9*C*H^(2*(i+j)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcC (by norm_num)) (pow_nonneg hH0 _)
    _ ≤ 9*C*H^(2*n+2) := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hH (by omega)) (mul_nonneg (by norm_num) hC)

theorem tail_product_shift (i j n : ℕ) (hij : i + j ≤ n + 1) :
    highShift i+highShift j+1 ≤ 110*(n+1) := by
  unfold highShift
  omega

namespace PrefixBound

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile}
  {F : PrefixFields P T (N + 1) a} {hT : 0 ≤ T}
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} (B : PrefixBound F hT S R)
  {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)

include B

theorem tail_slow_product_bound (hN : 1 ≤ N) (hR : 1 ≤ R)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (hc : (a 0).corrector = 0) (hb : (a 1).mean = 0)
    (i j n : ℕ) (hij : i + j = n) :
    (SpatialJetField.slowAdvection C.inverse (F.knownJet O (by omega) i)
      (F.knownJet O (by omega) j)).WordBound 6 R
      (9*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) := by
  have hi := B.knownJet_bound O (by omega) hR hc hb i
  have hj := B.knownJet_bound O (by omega) hR hc hb j
  have hi0 : 0 ≤ 3*S.H0^(2*i) := mul_nonneg (by norm_num) (pow_nonneg S.H0_pos.le _)
  have hj0 : 0 ≤ 3*S.H0^(2*j) := mul_nonneg (by norm_num) (pow_nonneg S.H0_pos.le _)
  have h := BC.slow_unnormalized_bound _ _ hi hj (zero_le_one.trans hR) hi0 hj0 hRc
  have h0 := mul_nonneg (mul_nonneg BC.slowCost_nonneg hi0) hj0
  have hs := h.mono_shift hR h0 (tail_product_shift i j n (by omega))
  exact hs.mono_amplitude (zero_le_one.trans hR)
    (tail_product_amplitude S.H0 BC.slowCost BC.termCost S.H0_one_le BC.slowCost_nonneg
      BC.slowCost_le i j n (by omega))

theorem tail_fast_product_bound (hN : 1 ≤ N) (hR : 1 ≤ R)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (hc : (a 0).corrector = 0) (hb : (a 1).mean = 0)
    (i j n : ℕ) (hij : i + j = n + 1) :
    (SpatialJetField.fastAdvection C.normal (F.knownJet O (by omega) i)
      (F.knownJet O (by omega) j)).WordBound 6 R
      (9*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) := by
  have hi := B.knownJet_bound O (by omega) hR hc hb i
  have hj := B.knownJet_bound O (by omega) hR hc hb j
  have hi0 : 0 ≤ 3*S.H0^(2*i) := mul_nonneg (by norm_num) (pow_nonneg S.H0_pos.le _)
  have hj0 : 0 ≤ 3*S.H0^(2*j) := mul_nonneg (by norm_num) (pow_nonneg S.H0_pos.le _)
  have h := BC.fast_unnormalized_bound _ _ hi hj (zero_le_one.trans hR) hi0 hj0 hRc
  have h0 := mul_nonneg (mul_nonneg BC.fastCost_nonneg hi0) hj0
  have hs := h.mono_shift hR h0 (tail_product_shift i j n (by omega))
  exact hs.mono_amplitude (zero_le_one.trans hR)
    (tail_product_amplitude S.H0 BC.fastCost BC.termCost S.H0_one_le BC.fastCost_nonneg
      BC.fastCost_le i j n (by omega))

end PrefixBound
end EulerPacketCylinderField

end
end

end

section

/-! The complete nonlinear tail is bounded using its actual finite convolution. -/

section

/-! Fixed-radius word bounds for the actual finite grade convolution. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.Field

open Set Finset EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)]

theorem wordBound_convolution (M n : ℕ) (f : ℕ → ℕ → VectorField)
    (G : ∀ i j, Field P T (f i j)) (q : ℕ) (R A : ℝ) (d : ℕ)
    (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hG : ∀ i ∈ range (M + 1), ∀ j ∈ range (M + 1), i + j = n → (G i j).WordBound q R A d) :
    (Field.convolution M n f G).WordBound q R (((M+1 : ℕ) : ℝ)^2*A) d := by
  classical
  let K : ∀ i j, Field P T (if i+j=n then f i j else 0) := fun i j => by
    by_cases hij : i+j=n
    · exact (G i j).congr (fun _ _ _ => by rw [ite_eq_left hij])
    · exact (Field.zero P T).congr (fun _ _ _ => by rw [ite_eq_right hij])
  have hK : ∀ i ∈ range (M+1), ∀ j ∈ range (M+1), (K i j).WordBound q R A d := by
    intro i hi j hj
    by_cases hij : i+j=n
    · exact (hG i hi j hj hij).ofRawEq (K i j) (fun _ _ _ => by rw [ite_eq_left hij])
    · exact (wordBound_of_zero (K i j) (fun _ _ _ => by
        rw [ite_eq_right hij]; rfl) q R d).mono_amplitude hR hA
  let row : (i : ℕ) → Field P T (∑ j ∈ range (M+1), if i+j=n then f i j else 0) := fun i =>
    Field.finsetSum (range (M+1)) (fun j => if i+j=n then f i j else 0) (K i)
  have hr : ∀ i ∈ range (M+1), (row i).WordBound q R (((M+1 : ℕ) : ℝ)*A) d := by
    intro i hi
    have h := wordBound_finsetSum (range (M+1)) (fun j => if i+j=n then f i j else 0) (K i)
      (fun _ => A) (hK i hi)
    simpa only [sum_const,card_range,nsmul_eq_mul] using h
  have ht := wordBound_finsetSum (range (M+1))
    (fun i => ∑ j ∈ range (M+1), if i+j=n then f i j else 0) row
    (fun _ => ((M+1 : ℕ) : ℝ)*A) hr
  have he : ∑ _i ∈ range (M+1), ((M+1 : ℕ) : ℝ)*A = ((M+1 : ℕ) : ℝ)^2*A := by
    simp only [sum_const,card_range,nsmul_eq_mul]
    ring
  rw [he] at ht
  apply ht.ofRawEq (Field.convolution M n f G)
  intro t x θ
  simp only [Finset.sum_apply,ite_apply,Pi.zero_apply]

end EulerPacketCylinderField.Field

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.PrefixBound

open Set Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerParameterWordGevrey

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile}
  {F : PrefixFields P T (N + 1) a} {hT : 0 ≤ T}
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} (B : PrefixBound F hT S R)
  {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)

include B

theorem tail_nonlinear_bound (hN : 1 ≤ N) (hR : 1 ≤ R)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (hc : (a 0).corrector = 0) (hb : (a 1).mean = 0) (n : ℕ) :
    (F.tailNonlinearField C n).WordBound 6 R
      (18*((N+2 : ℕ) : ℝ)^2*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) := by
  let J := F.knownJet O (by omega)
  have hA : 0 ≤ 9*BC.termCost*S.H0^(2*n+2) :=
    mul_nonneg (mul_nonneg (by norm_num) BC.termCost_nonneg) (pow_nonneg S.H0_pos.le _)
  have hS := Field.wordBound_convolution (N+1) n
    (fun i j z => slowAdvection (O.inverseFrame z) (knownJets O (N+1) a z i) (knownJets O (N+1) a z
        j))
    (fun i j => SpatialJetField.slowAdvection C.inverse (J i) (J j))
    6 R (9*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) (zero_le_one.trans hR) hA
    (fun i _ j _ hij => B.tail_slow_product_bound BC hN hR hRc hc hb i j n hij)
  have hH := Field.wordBound_convolution (N+1) (n+1)
    (fun i j z => fastAdvection (O.normal z) (knownJets O (N+1) a z i) (knownJets O (N+1) a z j))
    (fun i j => SpatialJetField.fastAdvection C.normal (J i) (J j))
    6 R (9*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) (zero_le_one.trans hR) hA
    (fun i _ j _ hij => B.tail_fast_product_bound BC hN hR hRc hc hb i j n hij)
  have hs := hS.add hH
  have he : ((N+1+1 : ℕ) : ℝ)^2*(9*BC.termCost*S.H0^(2*n+2)) +
      ((N+1+1 : ℕ) : ℝ)^2*(9*BC.termCost*S.H0^(2*n+2)) =
      18*((N+2 : ℕ) : ℝ)^2*BC.termCost*S.H0^(2*n+2) := by
    push_cast
    ring
  rw [he] at hs
  exact hs.ofRawEq (F.tailNonlinearField C n) (fun _ _ _ => rfl)

end EulerPacketCylinderField.PrefixBound

end
end

end

section

/-! The only surviving linear tail grade has the same fixed coefficient budget. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic EulerParameterWordGevrey

theorem CoefficientBudget.linear_and_pressure_le {P T : ℝ} [Fact (0 < P)]
    {O : Operators} {C : CoefficientData P T O} (B : CoefficientBudget C) :
    B.linearCost+B.multiplierCost ≤ B.termCost := by
  have hs := B.slowCost_nonneg
  unfold CoefficientBudget.linearCost CoefficientBudget.termCost
  linarith

namespace PrefixBound

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile}
  {F : PrefixFields P T (N + 1) a} {hT : 0 ≤ T}
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} (B : PrefixBound F hT S R)
  {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)

include B

theorem tail_linear_bound (hTime : 0 < T) (hN : 1 ≤ N) (hR : 1 ≤ R)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    {correctorT : VectorField} (Ct : Field P T correctorT)
    (hCt : TimeDerivative hTime.le (F.corrector N (by omega)) Ct)
    (pressure : Field P T (pressureGradient (a N).highPressure))
    (hCtB : (Ct.normalized hT (S.high N) (S.high_pos N)).WordBound 6 R 1 (highShift N))
    (hpB : (pressure.normalized hT (S.high N) (S.high_pos N)).WordBound 6 R 1 (highShift N))
    (n : ℕ) :
    (F.tailLinearField C hTime Ct hCt pressure n).WordBound 6 R
      (BC.termCost*S.H0^(2*n+2)) (110*(n+1)) := by
  by_cases hn : n=N+1
  · have hC := B.corrector N (by omega) hN
    have hL := BC.previousLinear_bound hTime S (N+1) (S.high N) (S.high_pos N)
      (F.corrector N (by omega)) Ct hCt
      (by simpa only [Field.WordBound,Field.normalized_path,Nat.add_sub_cancel] using hC)
      (by
          simpa only [Field.WordBound,Field.normalized_path,Nat.add_sub_cancel] using hCtB) hRc (by
              simp)
    have hQ := BC.previousPressure_bound hTime S (N+1) (S.high N) (S.high_pos N)
      (a N).highPressure pressure
      (by
          simpa only [Field.WordBound,Field.normalized_path,Nat.add_sub_cancel] using hpB) hRc (by
              simp)
    have hL' := hL.remove_profile hTime.le (S.high N) (S.high_pos N)
      (S.H0^(2*N)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse N hN)
    have hQ' := hQ.remove_profile hTime.le (S.high N) (S.high_pos N)
      (S.H0^(2*N)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse N hN)
    have hs := hL'.add hQ'
    have ha : S.H0^(2*N)*BC.linearCost+S.H0^(2*N)*BC.multiplierCost ≤
        BC.termCost*S.H0^(2*n+2) := by
      calc
        _ = (BC.linearCost+BC.multiplierCost)*S.H0^(2*N) := by ring
        _ ≤ BC.termCost*S.H0^(2*N) :=
          mul_le_mul_of_nonneg_right BC.linear_and_pressure_le (pow_nonneg S.H0_pos.le _)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ S.H0_one_le (by omega)) BC.termCost_nonneg
    have hs' := (hs.mono_amplitude (zero_le_one.trans hR) ha).mono_shift hR
      (mul_nonneg BC.termCost_nonneg (pow_nonneg S.H0_pos.le _))
      (show highShift (N+1-1) ≤ 110*(n+1) by unfold highShift; omega)
    apply hs'.ofRawEq (F.tailLinearField C hTime Ct hCt pressure n)
    intro t x θ
    simp only [ite_eq_left hn]
    rfl
  · exact (Field.wordBound_of_zero (F.tailLinearField C hTime Ct hCt pressure n)
      (fun _ _ _ => by rw [ite_eq_right hn]) 6 R (110*(n+1))).mono_amplitude
      (zero_le_one.trans hR) (mul_nonneg BC.termCost_nonneg (pow_nonneg S.H0_pos.le _))

end PrefixBound
end EulerPacketCylinderField

end
end

end

section

/-! Each surviving grade of the literal packet residual has a fixed-radius estimate. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.PrefixBound

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic EulerParameterWordGevrey

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile}
  {F : PrefixFields P T (N + 1) a} {hT : 0 ≤ T}
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} (B : PrefixBound F hT S R)
  {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)

include B

theorem tail_grade_bound (hTime : 0 < T) (hN : 1 ≤ N) (hR : 1 ≤ R)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    {correctorT : VectorField} (Ct : Field P T correctorT)
    (hCt : TimeDerivative hTime.le (F.corrector N (Nat.lt_succ_self N)) Ct)
    (pressure : Field P T (pressureGradient (a N).highPressure))
    (hCtB : (Ct.normalized hT (S.high N) (S.high_pos N)).WordBound 6 R 1 (highShift N))
    (hpB : (pressure.normalized hT (S.high N) (S.high_pos N)).WordBound 6 R 1 (highShift N))
    (ha : a 0 = 0) (hb : (a 1).mean = 0) (n : ℕ) (hn : N + 1 ≤ n) :
    (F.tailGradeField C hTime Ct hCt pressure ha n hn).WordBound 6 R
      ((1+18*((N+2 : ℕ) : ℝ)^2)*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) := by
  have hc : (a 0).corrector=0 := by rw [ha]; rfl
  have hL := B.tail_linear_bound BC hTime hN hR hRc Ct hCt pressure hCtB hpB n
  have hQ := B.tail_nonlinear_bound BC hN hR hRc hc hb n
  have hs := hL.add hQ
  have he : BC.termCost*S.H0^(2*n+2)+18*((N+2 : ℕ) : ℝ)^2*BC.termCost*S.H0^(2*n+2) =
      (1+18*((N+2 : ℕ) : ℝ)^2)*BC.termCost*S.H0^(2*n+2) := by ring
  rw [he] at hs
  exact hs.of_path_eq (F.tailGradeField C hTime Ct hCt pressure ha n hn)
    (F.tailGradeField_path C hTime Ct hCt pressure ha n hn)

end EulerPacketCylinderField.PrefixBound

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.ProfileRegularity

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile} {support : Set Space}
  (hT : 0 < T) (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le support (a i))
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}

theorem prefixThrough_bound
    (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i) :
    PrefixBound (prefixThrough hT G) hT.le S R where
  high i hi hip := (hG i (by omega) hip).high
  mean i hi hip := (hG i (by omega) (by omega)).mean
  corrector i hi hip := (hG i (by omega) hip).corrector

variable {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)

theorem tail_grade_bound
    (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (ha : a 0 = 0) (hb : (a 1).mean = 0) (n : ℕ) (hn : N + 1 ≤ n) :
    (tailGradeField hT G C ha n hn).WordBound 6 R
      ((1+18*((N+2 : ℕ) : ℝ)^2)*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) :=
  (prefixThrough_bound hT G hG).tail_grade_bound BC hT hN hR hRc
    (G N le_rfl).correctorDerivative (G N le_rfl).corrector_time (G N le_rfl).pressure
    (hG N le_rfl hN).correctorDerivative (hG N le_rfl hN).pressure ha hb n hn

theorem literal_tail_grade_bound
    (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (ha : a 0 = 0) (hb : (a 1).mean = 0) (n : ℕ) (hn : N + 1 ≤ n) :
    (literalTailGradeField hT G C ha n hn).WordBound 6 R
      ((1+18*((N+2 : ℕ) : ℝ)^2)*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) :=
  (tail_grade_bound hT G BC hG hN hR hRc ha hb n hn).of_path_eq
    (literalTailGradeField hT G C ha n hn) (literalTailGradeField_path hT G C ha n hn)

end EulerPacketCylinderField.ProfileRegularity
