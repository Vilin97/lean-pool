/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Separation.Calculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Separation.Pointwise

/-! # Commutator pairings of first and second order

For a smooth periodic drift `b` with `|∂_i b_k| ≤ Lu` and a smooth periodic `f`:

* `|∑_i ∫ ∂_i f (∂_i b·∇f)| ≤ 2 Lu ∑_i ‖∂_i f‖²`;
* `|∑_{j,i} C_{[j,i]}| ≤ (κ/2) ‖∇³f‖² + 4 (Lu²/κ) ‖∇f‖² + 2 Lu ‖∇²f‖²`, where the second derivative
  of `b` is integrated by parts onto `f` once (this corrects the stated form of the bound). -/

@[expose] public section

open Homogenization MeasureTheory
open AVenhance.Infra.Section4

noncomputable section

namespace AVenhance.Infra.FullTheorem.Separation

open AVenhance

/-- The commutator pairing `∫ ∂^wf (∂^w(b·∇f) - b·∇∂^wf)`. -/
def commPair (w : List (Fin 2)) (b : Vec 2 → Vec 2) (f : Vec 2 → ℝ) : ℝ :=
  ∫ x in unitCube, classicalWordDerivative w f x *
    (classicalWordDerivative w (classicalTransport b f) x -
      vecDot (b x) (spaceGrad (classicalWordDerivative w f) x))

theorem comm_one_eq {b : Vec 2 → Vec 2} {f : Vec 2 → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    classicalWordDerivative [i] (classicalTransport b f) x -
        vecDot (b x) (spaceGrad (classicalWordDerivative [i] f) x) =
      ∑ k : Fin 2, spaceGrad (fun y => b y k) x i * spaceGrad f x k := by
  rw [classicalWordDerivative_transport_eq_commutatorExpansion [i] b f hb hf x]
  apply Finset.sum_congr rfl
  intro k _
  simp [classicalWordCommutatorExpansion,
    Classical.classicalWordCommutatorExpansion, Classical.classicalWordCommutatorSplits,
    Classical.classicalWordSplits, Classical.classicalWordProductTerm,
    Classical.classicalWordDerivative]

theorem comm_two_eq {b : Vec 2 → Vec 2} {f : Vec 2 → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j i : Fin 2) (x : Vec 2) :
    classicalWordDerivative [j, i] (classicalTransport b f) x -
        vecDot (b x) (spaceGrad (classicalWordDerivative [j, i] f) x) =
      ∑ k : Fin 2, (spaceGrad (fun y => spaceGrad (fun z => b z k) y i) x j * spaceGrad f x k +
        spaceGrad (fun y => b y k) x j * spaceGrad (fun y => spaceGrad f y k) x i +
        spaceGrad (fun y => b y k) x i * spaceGrad (fun y => spaceGrad f y k) x j) := by
  rw [classicalWordDerivative_transport_eq_commutatorExpansion [j, i] b f hb hf x]
  apply Finset.sum_congr rfl
  intro k _
  simp [classicalWordCommutatorExpansion,
    Classical.classicalWordCommutatorExpansion, Classical.classicalWordCommutatorSplits,
    Classical.classicalWordSplits, Classical.classicalWordProductTerm,
    Classical.classicalWordDerivative]
  ring

theorem commPair_nil (b : Vec 2 → Vec 2) (f : Vec 2 → ℝ) : commPair [] b f = 0 := by
  unfold commPair
  simp [classicalWordDerivative,
    Classical.classicalWordDerivative, classicalTransport,
    Classical.classicalTransport]

section first

variable {b : Vec 2 → Vec 2} {f : Vec 2 → ℝ} {Lu : ℝ}

theorem commPair_one_abs_le (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hLu : ∀ x i k, |spaceGrad (fun y => b y k) x i| ≤ Lu) :
    |∑ i : Fin 2, commPair [i] b f| ≤ 2 * Lu * ∑ i : Fin 2, en [i] f := by
  have hbk : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (fun y => b y k) := fun k => contDiff_pi.mp hb k
  have ca : ∀ i, Continuous (fun x => spaceGrad f x i) := fun i => cont_word [i] hf
  have cm : ∀ i k, Continuous (fun x => spaceGrad (fun y => b y k) x i) :=
    fun i k => cont_word [i] (hbk k)
  have hφ : ∀ i k, Continuous (fun x => spaceGrad f x i *
      (spaceGrad (fun y => b y k) x i * spaceGrad f x k)) :=
    fun i k => (ca i).mul ((cm i k).mul (ca k))
  have e1 : ∀ i, commPair [i] b f = ∑ k : Fin 2, ∫ x in unitCube,
      spaceGrad f x i * (spaceGrad (fun y => b y k) x i * spaceGrad f x k) := by
    intro i
    unfold commPair
    have : (fun x => classicalWordDerivative [i] f x *
        (classicalWordDerivative [i] (classicalTransport b f) x -
          vecDot (b x) (spaceGrad (classicalWordDerivative [i] f) x))) = fun x =>
        ∑ k : Fin 2, spaceGrad f x i *
          (spaceGrad (fun y => b y k) x i * spaceGrad f x k) := by
      funext x
      rw [comm_one_eq hb hf i x, Finset.mul_sum]
      rfl
    rw [this, integral_finsetSum]
    intro k _
    exact intOn (hφ i k)
  rw [Finset.sum_congr rfl (fun i _ => e1 i)]
  have e2 : (∑ i : Fin 2, ∑ k : Fin 2, ∫ x in unitCube,
      spaceGrad f x i * (spaceGrad (fun y => b y k) x i * spaceGrad f x k)) =
      ∫ x in unitCube, ∑ i : Fin 2, ∑ k : Fin 2,
        spaceGrad f x i * (spaceGrad (fun y => b y k) x i * spaceGrad f x k) :=
    (int_sum_sum hφ).symm
  rw [e2]
  have hq : Continuous (fun x => 2 * Lu * ∑ i : Fin 2, spaceGrad f x i ^ 2) :=
    continuous_const.mul (continuous_finsetSum _ (fun i _ => (ca i).pow 2))
  have hF : Continuous (fun x => ∑ i : Fin 2, ∑ k : Fin 2,
      spaceGrad f x i * (spaceGrad (fun y => b y k) x i * spaceGrad f x k)) :=
    continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun k _ => hφ i k))
  refine (abs_integral_le_of hF hq (fun x => ?_)).trans ?_
  · exact abs_quadForm_le (fun i k => spaceGrad (fun y => b y k) x i)
      (fun i => spaceGrad f x i) (fun i k => hLu x i k)
  · have hq2 : (∫ x in unitCube, ∑ i : Fin 2, spaceGrad f x i ^ 2) =
        ∑ i : Fin 2, en [i] f := by
      rw [int_sum2 (φ := fun i x => spaceGrad f x i ^ 2) (fun i => (ca i).pow 2)]
      rfl
    rw [integral_const_mul, hq2]

end first

section second

variable {b : Vec 2 → Vec 2} {f : Vec 2 → ℝ} {κ Lu : ℝ}

theorem commPair_two_abs_le (hκ : 0 < κ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbp : IsZ2Periodic b) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfp : IsZ2Periodic f)
    (hLu : ∀ x i k, |spaceGrad (fun y => b y k) x i| ≤ Lu) :
    |∑ j : Fin 2, ∑ i : Fin 2, commPair [j, i] b f| ≤
      κ / 2 * (∑ l : Fin 2, ∑ j : Fin 2, ∑ i : Fin 2, en [l, j, i] f) +
        4 * (Lu ^ 2 / κ) * (∑ k : Fin 2, en [k] f) +
        2 * Lu * (∑ j : Fin 2, ∑ i : Fin 2, en [j, i] f) := by
  have hbk : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (fun y => b y k) := fun k => contDiff_pi.mp hb k
  have hbkp : ∀ k, IsZ2Periodic (fun y => b y k) := fun k n x =>
    congrFun (hbp n x) k
  -- smooth periodic atoms
  have sF2 : ∀ j i, ContDiff ℝ (⊤ : ℕ∞) (fun x => spaceGrad (fun y => spaceGrad f y i) x j) :=
    fun j i => contDiff_word [j, i] hf
  have pF2 : ∀ j i, IsZ2Periodic (fun x => spaceGrad (fun y => spaceGrad f y i) x j) :=
    fun j i => classicalWordDerivative_periodic [j, i] hf hfp
  have sFk : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (fun x => spaceGrad f x k) := fun k => contDiff_word [k] hf
  have pFk : ∀ k, IsZ2Periodic (fun x => spaceGrad f x k) :=
    fun k => classicalWordDerivative_periodic [k] hf hfp
  have sm : ∀ i k, ContDiff ℝ (⊤ : ℕ∞) (fun x => spaceGrad (fun y => b y k) x i) :=
    fun i k => contDiff_word [i] (hbk k)
  have pm : ∀ i k, IsZ2Periodic (fun x => spaceGrad (fun y => b y k) x i) :=
    fun i k => classicalWordDerivative_periodic [i] (hbk k) (hbkp k)
  have cFik : ∀ i k, Continuous (fun x => spaceGrad (fun y => spaceGrad f y k) x i) :=
    fun i k => cont_word [i, k] hf
  have cF3 : ∀ l j i, Continuous
      (fun x => spaceGrad (fun y => spaceGrad (fun z => spaceGrad f z i) y j) x l) :=
    fun l j i => cont_word [l, j, i] hf
  -- Step 1: per-index identity
  have e1 : ∀ j i, commPair [j, i] b f = ∑ k : Fin 2, ∫ x in unitCube,
      (-(spaceGrad (fun y => b y k) x i *
          spaceGrad (fun y => spaceGrad (fun z => spaceGrad f z i) y j) x j * spaceGrad f x k) +
        spaceGrad (fun y => spaceGrad f y i) x j * spaceGrad (fun y => b y k) x j *
          spaceGrad (fun y => spaceGrad f y k) x i) := by
    intro j i
    unfold commPair
    have hint : ∀ k, Continuous (fun x => spaceGrad (fun y => spaceGrad f y i) x j *
        (spaceGrad (fun y => spaceGrad (fun z => b z k) y i) x j * spaceGrad f x k +
          spaceGrad (fun y => b y k) x j * spaceGrad (fun y => spaceGrad f y k) x i +
          spaceGrad (fun y => b y k) x i * spaceGrad (fun y => spaceGrad f y k) x j)) := by
      intro k
      exact (sF2 j i).continuous.mul
        ((((cont_word [j, i] (hbk k)).mul (sFk k).continuous).add
          ((cont_word [j] (hbk k)).mul (cFik i k))).add
          ((cont_word [i] (hbk k)).mul (cFik j k)))
    have : (fun x => classicalWordDerivative [j, i] f x *
        (classicalWordDerivative [j, i] (classicalTransport b f) x -
          vecDot (b x) (spaceGrad (classicalWordDerivative [j, i] f) x))) = fun x =>
        ∑ k : Fin 2, spaceGrad (fun y => spaceGrad f y i) x j *
          (spaceGrad (fun y => spaceGrad (fun z => b z k) y i) x j * spaceGrad f x k +
          spaceGrad (fun y => b y k) x j * spaceGrad (fun y => spaceGrad f y k) x i +
          spaceGrad (fun y => b y k) x i * spaceGrad (fun y => spaceGrad f y k) x j) := by
      funext x
      rw [comm_two_eq hb hf j i x, Finset.mul_sum]
      rfl
    rw [this, integral_finsetSum _ (fun k _ => intOn (hint k))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact triple_identity (sF2 j i) (sFk k) (sm i k) (pF2 j i) (pFk k) (pm i k)
      (cont_word [j] (hbk k)) (cFik i k) j
  -- Step 2: sum over indices and bound pointwise
  have hg : ∀ j i k, Continuous (fun x =>
      (-(spaceGrad (fun y => b y k) x i *
          spaceGrad (fun y => spaceGrad (fun z => spaceGrad f z i) y j) x j * spaceGrad f x k) +
        spaceGrad (fun y => spaceGrad f y i) x j * spaceGrad (fun y => b y k) x j *
          spaceGrad (fun y => spaceGrad f y k) x i)) := by
    intro j i k
    exact (((cont_word [i] (hbk k)).mul (cF3 j j i) |>.mul (sFk k).continuous).neg).add
      (((sF2 j i).continuous.mul (cont_word [j] (hbk k))).mul (cFik i k))
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => e1 j i))]
  rw [← int_sum_sum_sum hg]
  have cP : Continuous (fun x => ∑ l : Fin 2, ∑ j : Fin 2, ∑ i : Fin 2,
      (spaceGrad (fun y => spaceGrad (fun z => spaceGrad f z i) y j) x l) ^ 2) :=
    continuous_finsetSum _ (fun l _ => continuous_finsetSum _
      (fun j _ => continuous_finsetSum _ (fun i _ => (cF3 l j i).pow 2)))
  have cA : Continuous (fun x => ∑ k : Fin 2, (spaceGrad f x k) ^ 2) :=
    continuous_finsetSum _ (fun k _ => (sFk k).continuous.pow 2)
  have cT : Continuous (fun x => ∑ j : Fin 2, ∑ i : Fin 2,
      (spaceGrad (fun y => spaceGrad f y i) x j) ^ 2) :=
    continuous_finsetSum _ (fun j _ => continuous_finsetSum _
      (fun i _ => (sF2 j i).continuous.pow 2))
  have hF : Continuous (fun x => ∑ j : Fin 2, ∑ i : Fin 2, ∑ k : Fin 2,
      (-(spaceGrad (fun y => b y k) x i *
          spaceGrad (fun y => spaceGrad (fun z => spaceGrad f z i) y j) x j * spaceGrad f x k) +
        spaceGrad (fun y => spaceGrad f y i) x j * spaceGrad (fun y => b y k) x j *
          spaceGrad (fun y => spaceGrad f y k) x i)) :=
    continuous_finsetSum _ (fun j _ => continuous_finsetSum _
      (fun i _ => continuous_finsetSum _ (fun k _ => hg j i k)))
  have hq : Continuous (fun x => κ / 2 * (∑ l : Fin 2, ∑ j : Fin 2, ∑ i : Fin 2,
      (spaceGrad (fun y => spaceGrad (fun z => spaceGrad f z i) y j) x l) ^ 2) +
      4 * (Lu ^ 2 / κ) * (∑ k : Fin 2, (spaceGrad f x k) ^ 2) +
      2 * Lu * (∑ j : Fin 2, ∑ i : Fin 2, (spaceGrad (fun y => spaceGrad f y i) x j) ^ 2)) :=
    ((continuous_const.mul cP).add (continuous_const.mul cA)).add (continuous_const.mul cT)
  refine (abs_integral_le_of hF hq (fun x => ?_)).trans ?_
  · exact abs_secondForm_le hκ (m := fun i k => spaceGrad (fun y => b y k) x i)
      (p := fun l j i => spaceGrad (fun y => spaceGrad (fun z => spaceGrad f z i) y j) x l)
      (t2 := fun j i => spaceGrad (fun y => spaceGrad f y i) x j)
      (a := fun k => spaceGrad f x k) (fun i k => hLu x i k)
  · have hP : (∫ x in unitCube, ∑ l : Fin 2, ∑ j : Fin 2, ∑ i : Fin 2,
        (spaceGrad (fun y => spaceGrad (fun z => spaceGrad f z i) y j) x l) ^ 2) =
        ∑ l : Fin 2, ∑ j : Fin 2, ∑ i : Fin 2, en [l, j, i] f :=
      int_sum_sum_sum (φ := fun l j i x =>
        (spaceGrad (fun y => spaceGrad (fun z => spaceGrad f z i) y j) x l) ^ 2)
        (fun l j i => (cF3 l j i).pow 2)
    have hA : (∫ x in unitCube, ∑ k : Fin 2, (spaceGrad f x k) ^ 2) =
        ∑ k : Fin 2, en [k] f :=
      int_sum2 (φ := fun k x => (spaceGrad f x k) ^ 2) (fun k => (sFk k).continuous.pow 2)
    have hT : (∫ x in unitCube, ∑ j : Fin 2, ∑ i : Fin 2,
        (spaceGrad (fun y => spaceGrad f y i) x j) ^ 2) =
        ∑ j : Fin 2, ∑ i : Fin 2, en [j, i] f :=
      int_sum_sum (φ := fun j i x => (spaceGrad (fun y => spaceGrad f y i) x j) ^ 2)
        (fun j i => (sF2 j i).continuous.pow 2)
    have iP := intOn cP
    have iA := intOn cA
    have iT := intOn cT
    have i1 : IntegrableOn (fun x => κ / 2 * (∑ l : Fin 2, ∑ j : Fin 2, ∑ i : Fin 2,
        (spaceGrad (fun y => spaceGrad (fun z => spaceGrad f z i) y j) x l) ^ 2)) unitCube :=
      iP.const_mul _
    have i2 : IntegrableOn (fun x => 4 * (Lu ^ 2 / κ) *
        (∑ k : Fin 2, (spaceGrad f x k) ^ 2)) unitCube := iA.const_mul _
    have i3 : IntegrableOn (fun x => 2 * Lu * (∑ j : Fin 2, ∑ i : Fin 2,
        (spaceGrad (fun y => spaceGrad f y i) x j) ^ 2)) unitCube := iT.const_mul _
    have i12 : IntegrableOn (fun x => κ / 2 * (∑ l : Fin 2, ∑ j : Fin 2, ∑ i : Fin 2,
        (spaceGrad (fun y => spaceGrad (fun z => spaceGrad f z i) y j) x l) ^ 2) +
        4 * (Lu ^ 2 / κ) * (∑ k : Fin 2, (spaceGrad f x k) ^ 2)) unitCube := i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul, hP, hA, hT]

end second

end AVenhance.Infra.FullTheorem.Separation
