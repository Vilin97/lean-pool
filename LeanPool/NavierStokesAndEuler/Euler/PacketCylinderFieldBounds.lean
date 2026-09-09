/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetOperations
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathBilinearBounds
public import LeanPool.NavierStokesAndEuler.Euler.CylinderConstantMapBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift

@[expose] public section

/-! Same-radius word bounds on the actual raw-field witnesses used by the packet recursion. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set Finset ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerCylinderSobolev EulerLpCylinderTranslation
  EulerCylinderPathProduct EulerCylinderConstantMap EulerLpCylinderRectangular
  EulerParameterWordGevrey EulerGevrey EulerPacketProfileRecursion
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] {raw raw' : VectorField}

def WordBound (G : Field P T raw) (q : ℕ) (R A : ℝ) (d : ℕ) : Prop :=
  ∀ n, block standardDirection q (fun a : LiftTangent => pathTranslate P a G.path) n 0 ≤
    A*majorant R d n

variable {G : Field P T raw} {H : Field P T raw'} {q d e : ℕ} {R A B : ℝ}

theorem WordBound.transfer (h : G.WordBound q R A d) (H : Field P T raw) : H.WordBound q R A d := by
  unfold WordBound at *
  rw [← G.path_eq_of_same_raw H]
  exact h

theorem WordBound.congr (h : G.WordBound q R A d)
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, raw' (t,(x,θ)) = raw (t,(x,θ))) :
    (G.congr he).WordBound q R A d := h

theorem WordBound.mono_amplitude (h : G.WordBound q R A d) (hR : 0 ≤ R) (hAB : A ≤ B) :
    G.WordBound q R B d := fun n => (h n).trans
  (mul_le_mul_of_nonneg_right hAB (majorant_nonneg R hR d n))

theorem WordBound.mono_shift (h : G.WordBound q R A d) (hR : 1 ≤ R) (hA : 0 ≤ A) (hde : d ≤ e) :
    G.WordBound q R A e := fun n => (h n).trans
  (mul_le_mul_of_nonneg_left (majorant_mono_shift R hR d e n hde) hA)

theorem wordBound_zero (P T : ℝ) [Fact (0 < P)] (q : ℕ) (R : ℝ) (d : ℕ) :
    (Field.zero P T).WordBound q R 0 d := by
  intro n
  change block standardDirection q (fun a : LiftTangent => pathTranslate P a (0 : C(Icc (0 : ℝ)
    T,LiftL2 P))) n 0 ≤ _
  simp only [map_zero,block_zero_function,zero_mul,le_refl]

theorem WordBound.add (hG : G.WordBound q R A d) (hH : H.WordBound q R B d) :
    (G.add H).WordBound q R (A+B) d := by
  intro n
  change block standardDirection q (fun a : LiftTangent => pathTranslate P a (G.path+H.path)) n 0 ≤
    _
  simp only [map_add]
  exact (block_add_le standardDirection q _ _ G.orbit H.orbit n 0).trans
    ((add_le_add (hG n) (hH n)).trans_eq (by ring))

theorem WordBound.sub (hG : G.WordBound q R A d) (hH : H.WordBound q R B d) :
    (G.sub H).WordBound q R (A+B) d := by
  intro n
  change block standardDirection q (fun a : LiftTangent => pathTranslate P a (G.path+ -H.path)) n 0
    ≤ _
  simp only [map_add,map_neg]
  have h := block_sub_le standardDirection q
    (fun a : LiftTangent => pathTranslate P a G.path)
    (fun a : LiftTangent => pathTranslate P a H.path) G.orbit H.orbit n 0
  have hb := h.trans ((add_le_add (hG n) (hH n)).trans_eq
    (show A*majorant R d n+B*majorant R d n=(A+B)*majorant R d n by ring))
  have he : ((fun a : LiftTangent => pathTranslate P a G.path) -
      (fun a : LiftTangent => pathTranslate P a H.path)) =
      fun a : LiftTangent => pathTranslate P a G.path + -pathTranslate P a H.path := by
    funext a
    exact sub_eq_add_neg _ _
  rw [he] at hb
  exact hb

theorem WordBound.smul (hG : G.WordBound q R A d) (c : ℝ) :
    (G.smul c).WordBound q R (|c| * A) d := by
  intro n
  change block standardDirection q (fun a : LiftTangent => pathTranslate P a (c • G.path)) n 0 ≤ _
  simp only [map_smul]
  exact (block_smul_le standardDirection q c _ G.orbit n 0).trans
    ((mul_le_mul_of_nonneg_left (hG n) (abs_nonneg c)).trans_eq (by ring))

theorem WordBound.neg (hG : G.WordBound q R A d) : (G.neg).WordBound q R A d := by
  intro n
  have h := block_smul_le standardDirection q (-1) _ G.orbit n 0
  simp only [neg_one_smul,abs_neg,abs_one,one_mul] at h
  change block standardDirection q (fun a : LiftTangent => pathTranslate P a (-G.path)) n 0 ≤ _
  simpa only [map_neg] using h.trans (hG n)

theorem WordBound.derivative (hG : G.WordBound q R A d) (i : Fin 4) :
    (G.derivative i).WordBound q R A (d+1) :=
  derivativePath_majorant P G.path G.orbit i q R A d hG

theorem WordBound.map (hG : G.WordBound q R A d) (L : Space →L[ℝ] Space) :
    (G.map L).WordBound q R (‖L‖*A) d := by
  intro n
  exact (pathMap_block_bound P standardDirection q L G.path G.orbit n 0).trans
    ((mul_le_mul_of_nonneg_left (hG n) (norm_nonneg L)).trans_eq (by ring))

theorem wordBound_finsetSum {ι : Type*} (s : Finset ι) (f : ι → VectorField)
    (G : ∀ i, Field P T (f i)) (A : ι → ℝ)
    (h : ∀ i ∈ s, (G i).WordBound q R (A i) d) :
    (Field.finsetSum s f G).WordBound q R (∑ i ∈ s,A i) d := by
  intro n
  have he : (fun a : LiftTangent => pathTranslate P a (Field.finsetSum s f G).path) =
      ∑ i ∈ s, (fun a : LiftTangent => pathTranslate P a (G i).path) := by
    funext a
    change pathTranslate P a (∑ i ∈ s,(G i).path) = _
    simp only [map_sum,Finset.sum_apply]
  rw [he]
  exact (block_finset_sum_le standardDirection q s _ (fun i _ => (G i).orbit) n 0).trans
    ((sum_le_sum (fun i hi => h i hi n)).trans_eq (Finset.sum_mul s A (majorant R d n)).symm)

theorem WordBound.scalarProduct (hG : G.WordBound 6 R A d) (hH : H.WordBound 6 R B e)
    (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (G.scalarProduct H L hL).WordBound 6 R (3*productBlockConstant P*A*B) (d+e) :=
  scalarProductPath_majorant P L hL G.path H.path G.orbit H.orbit R A B hR hA hB d e 0 hG hH

theorem WordBound.bilinear (hG : G.WordBound 6 R A d) (hH : H.WordBound 6 R B e)
    (L : Space →L[ℝ] Space →L[ℝ] Space) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (G.bilinear H L).WordBound 6 R (9*productBlockConstant P*‖L‖*A*B) (d+e) :=
  bilinearProductPath_majorant P L G.path H.path G.orbit H.orbit R A B hR hA hB d e 0 hG hH

theorem WordBound.spatialTransport (hG : G.WordBound 6 R A d) (hH : H.WordBound 6 R B e)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (G.spatialTransport H).WordBound 6 R (9*productBlockConstant P*A*B) (d+e+1) :=
  advectionPath_majorant P G.path H.path G.orbit H.orbit R A B hR hA hB d e 0 hG hH

theorem WordBound.multiply (hG : G.WordBound q R A d)
    {coef : EulerPacketPointJets.Domain → Space →L[ℝ] Space} (K : MatrixCoefficient T coef)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hK : ∀ n a, ‖iteratedFDeriv ℝ n (EulerMeanCoefficients.translateCoefficientPath K.path) a‖ ≤
      C*majorant Rc 0 n) :
    (K.multiply G).WordBound q R (3*sobolevCoefficientAmplitude (Fin 4) q Rc C*A) d :=
  product_orbit_block_bound P K.path K.orbit standardDirection
    (fun i => by cases i using Fin.cases <;> simp [Prod.norm_def]) q
    G.path G.orbit Rc C R A hRc hC hA hR hK d hG

end EulerPacketCylinderField.Field
