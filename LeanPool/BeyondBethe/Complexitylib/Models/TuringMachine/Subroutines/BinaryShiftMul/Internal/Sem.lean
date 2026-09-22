/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.ForBinaryWork
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul.Internal.Pure
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany

/-!
# Width-driven binary shift-and-add multiplication -- composed semantics

This file composes the width-linear copy and ripple-add primitives through a
bit-driven work-tape loop. The multiplier cursor is preserved by every body
phase and advanced only by the loopback seam.
-/


@[expose] public section

namespace Complexity

namespace TM

private def binaryShiftMulNatTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

private theorem binaryShiftMulNatTape_hasBinaryNat (value : ℕ) :
    (binaryShiftMulNatTape value).HasBinaryNat value := by
  simpa [binaryShiftMulNatTape] using Tape.init_move_right_hasBinaryNat value

private theorem hasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : Parked t :=
  ⟨by rw [h.2.1], h.2.hasBinaryContent.cells_ne_start⟩

private theorem binaryShiftMulExactFrame_transition {n : ℕ}
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    ∀ inp work out,
      (inp = inp₀ ∧ work = work₀ ∧ out = out₀) →
      transitionInput inp = inp₀ ∧
        (fun i => transitionTape (work i)) = work₀ ∧
        transitionTape out = out₀ := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hworkEq, hout⟩
  subst inp
  subst work
  subst out
  exact phaseTransition_eq_self_of_reads_ne_start hinput.read_ne_start
    (fun i => (hwork i).read_ne_start) houtput.read_ne_start

private def binaryShiftMulUpdateTime (acc shift : ℕ) : ℕ :=
  binaryRippleAddTime acc shift + 1 +
    binaryCopyTime (acc + shift) acc + 1 +
      resetBinaryWorkTime 1 (acc + shift).size

private def binaryShiftMulUpdatePost {n : ℕ} (abi : BinaryShiftMulABI n)
    (acc shift : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (out₀ : Tape) : TapePred n :=
  fun inp work out =>
    inp = inp₀ ∧
    (work abi.acc).HasBinaryNat (acc + shift) ∧
    (work abi.shift).HasBinaryNat shift ∧
    (work abi.tmp).HasBinaryNat 0 ∧
    (work abi.dbl).HasBinaryNat 0 ∧
    (∀ i, i ≠ abi.acc → i ≠ abi.shift → i ≠ abi.tmp → i ≠ abi.dbl →
      work i = work₀ i) ∧
    out = out₀

private theorem binaryShiftMulUpdateTM_hoareTime_frame {n : ℕ}
    (abi : BinaryShiftMulABI n) (acc shift : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hacc : (work₀ abi.acc).HasBinaryNat acc)
    (hshift : (work₀ abi.shift).HasBinaryNat shift)
    (htmp : (work₀ abi.tmp).HasBinaryNat 0)
    (hdbl : (work₀ abi.dbl).HasBinaryNat 0)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryShiftMulUpdateTM abi).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (binaryShiftMulUpdatePost abi acc shift inp₀ work₀ out₀)
      (binaryShiftMulUpdateTime acc shift) := by
  have hdistinctAdd : BinaryRippleAddDistinct abi.acc abi.shift abi.tmp :=
    ⟨abi.acc_ne_shift, abi.acc_ne_tmp, abi.shift_ne_tmp⟩
  have hadd := binaryRippleAddTM_hoareTime_frame abi.acc abi.shift abi.tmp
    hdistinctAdd acc shift inp₀ work₀ out₀ hacc hshift htmp hinput
    (fun i _ _ _ => hwork i) houtput
  let AddPost : TapePred n := fun inp work out =>
    inp = inp₀ ∧
    (work abi.acc).HasBinaryNat acc ∧
    (work abi.shift).HasBinaryNat shift ∧
    (work abi.tmp).HasBinaryNat (acc + shift) ∧
    (∀ i, i ≠ abi.acc → i ≠ abi.shift → i ≠ abi.tmp →
      work i = work₀ i) ∧
    out = out₀
  have hadd' : (binaryRippleAddTM abi.acc abi.shift abi.tmp).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      AddPost (binaryRippleAddTime acc shift) := by
    simpa only [AddPost] using hadd
  have htail :
      (seqTM (binaryCopyIntoTM abi.tmp abi.acc abi.dbl)
        (resetBinaryWorkTM abi.tmp)).HoareTime
        AddPost (binaryShiftMulUpdatePost abi acc shift inp₀ work₀ out₀)
        (binaryCopyTime (acc + shift) acc + 1 +
          resetBinaryWorkTime 1 (acc + shift).size) := by
    intro inp work out hpre
    rcases hpre with ⟨hinp, haccNow, hshiftNow, htmpNow, hframe, hout⟩
    have hworkNow : ∀ i, Parked (work i) := by
      intro i
      by_cases haccIdx : i = abi.acc
      · subst i
        exact hasBinaryNat_parked haccNow
      by_cases hshiftIdx : i = abi.shift
      · subst i
        exact hasBinaryNat_parked hshiftNow
      by_cases htmpIdx : i = abi.tmp
      · subst i
        exact hasBinaryNat_parked htmpNow
      rw [hframe i haccIdx hshiftIdx htmpIdx]
      exact hwork i
    have hdblNow : (work abi.dbl).HasBinaryNat 0 := by
      rw [hframe abi.dbl abi.acc_ne_dbl.symm abi.shift_ne_dbl.symm
        abi.tmp_ne_dbl.symm]
      exact hdbl
    have hcopy := binaryCopyIntoTM_hoareTime_frame abi.tmp abi.acc abi.dbl
      abi.acc_ne_tmp.symm abi.tmp_ne_dbl abi.acc_ne_dbl
      (acc + shift) acc inp work out htmpNow haccNow hdblNow
      (hinp.symm ▸ hinput) (fun i _ _ _ => hworkNow i)
      (hout.symm ▸ houtput)
    let work₂ := Function.update work abi.acc
      (binaryShiftMulNatTape (acc + shift))
    have hcopy' : (binaryCopyIntoTM abi.tmp abi.acc abi.dbl).HoareTime
        (fun inp' work' out' => inp' = inp ∧ work' = work ∧ out' = out)
        (fun inp' work' out' => inp' = inp ∧ work' = work₂ ∧ out' = out)
        (binaryCopyTime (acc + shift) acc) := by
      simpa only [work₂, binaryShiftMulNatTape] using hcopy
    have hwork₂ : ∀ i, Parked (work₂ i) := by
      intro i
      by_cases hi : i = abi.acc
      · subst i
        simp only [work₂, Function.update_self]
        exact hasBinaryNat_parked
          (binaryShiftMulNatTape_hasBinaryNat (acc + shift))
      simp only [work₂, Function.update_of_ne hi]
      exact hworkNow i
    have htmp₂ : (work₂ abi.tmp).HasBinaryNat (acc + shift) := by
      simpa only [work₂, Function.update_of_ne abi.acc_ne_tmp.symm] using
        htmpNow
    have hreset := resetBinaryWorkTM_hoareTime_frame abi.tmp
      (acc + shift).bits 1 inp work₂ out htmp₂.2.hasBinaryContent htmp₂.1
      ⟨by rw [htmp₂.2.1], by rw [htmp₂.2.1]⟩ (hinp.symm ▸ hinput)
      (fun i _ => hwork₂ i) (hout.symm ▸ houtput)
    have htransition : ∀ inp' work' out',
        (inp' = inp ∧ work' = work₂ ∧ out' = out) →
        (transitionInput inp' = inp ∧
          (fun i => transitionTape (work' i)) = work₂ ∧
          transitionTape out' = out) := by
      rintro _ _ _ ⟨rfl, rfl, rfl⟩
      exact phaseTransition_eq_self_of_reads_ne_start
        ((hinp.symm ▸ hinput).read_ne_start)
        (fun i => (hwork₂ i).read_ne_start)
        ((hout.symm ▸ houtput).read_ne_start)
    have hrun := seqTM_hoareTime
      (binaryCopyIntoTM abi.tmp abi.acc abi.dbl)
      (resetBinaryWorkTM abi.tmp) hcopy' htransition hreset
    obtain ⟨c', time, htime, hreach, hhalt, hfinalInput, hfinalWork,
        hfinalOutput⟩ := hrun inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨c', time, (by simpa [Nat.size_eq_bits_len] using htime),
      hreach, hhalt, ?_⟩
    refine ⟨hfinalInput.trans hinp, ?_, ?_, ?_, ?_, ?_,
      hfinalOutput.trans hout⟩
    · rw [hfinalWork]
      simp only [Function.update_of_ne abi.acc_ne_tmp,
        work₂, Function.update_self]
      exact binaryShiftMulNatTape_hasBinaryNat (acc + shift)
    · rw [hfinalWork]
      simp only [Function.update_of_ne abi.shift_ne_tmp,
        work₂, Function.update_of_ne abi.acc_ne_shift.symm]
      exact hshiftNow
    · rw [hfinalWork, Function.update_self]
      exact binaryShiftMulNatTape_hasBinaryNat 0
    · rw [hfinalWork]
      simp only [Function.update_of_ne abi.tmp_ne_dbl.symm,
        work₂, Function.update_of_ne abi.acc_ne_dbl.symm]
      exact hdblNow
    · intro i haccIdx hshiftIdx htmpIdx hdblIdx
      rw [hfinalWork, Function.update_of_ne htmpIdx]
      simp only [work₂, Function.update_of_ne haccIdx]
      exact hframe i haccIdx hshiftIdx htmpIdx
  have htransition : ∀ inp work out, AddPost inp work out →
      AddPost (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out) := by
    intro inp work out hpost
    rcases hpost with ⟨hinp, haccNow, hshiftNow, htmpNow, hframe, hout⟩
    have hreads : ∀ i, (work i).read ≠ Γ.start := by
      intro i
      by_cases haccIdx : i = abi.acc
      · subst i
        exact (hasBinaryNat_parked haccNow).read_ne_start
      by_cases hshiftIdx : i = abi.shift
      · subst i
        exact (hasBinaryNat_parked hshiftNow).read_ne_start
      by_cases htmpIdx : i = abi.tmp
      · subst i
        exact (hasBinaryNat_parked htmpNow).read_ne_start
      rw [hframe i haccIdx hshiftIdx htmpIdx]
      exact (hwork i).read_ne_start
    obtain ⟨hinputTransition, hworkTransition, houtputTransition⟩ :=
      phaseTransition_eq_self_of_reads_ne_start
        (hinp.symm ▸ hinput.read_ne_start) hreads
        (hout.symm ▸ houtput.read_ne_start)
    rw [hinputTransition, hworkTransition, houtputTransition]
    exact ⟨hinp, haccNow, hshiftNow, htmpNow, hframe, hout⟩
  have hrun := seqTM_hoareTime
    (binaryRippleAddTM abi.acc abi.shift abi.tmp)
    (seqTM (binaryCopyIntoTM abi.tmp abi.acc abi.dbl)
      (resetBinaryWorkTM abi.tmp)) hadd' htransition htail
  simpa [binaryShiftMulUpdateTM, binaryShiftMulUpdateTime,
    Nat.add_assoc] using hrun

private def binaryShiftMulDoubleTime (shift : ℕ) : ℕ :=
  binaryCopyTime shift 0 + 1 +
    binaryRippleAddTime shift shift + 1 +
      resetBinaryWorkTime 1 shift.size + 1 +
        binaryCopyTime (shift + shift) shift + 1 +
          resetBinaryWorkTime 1 (shift + shift).size

private def binaryShiftMulDoublePost {n : ℕ} (abi : BinaryShiftMulABI n)
    (shift : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (out₀ : Tape) : TapePred n :=
  fun inp work out =>
    inp = inp₀ ∧
    (work abi.shift).HasBinaryNat (2 * shift) ∧
    (work abi.tmp).HasBinaryNat 0 ∧
    (work abi.dbl).HasBinaryNat 0 ∧
    (∀ i, i ≠ abi.shift → i ≠ abi.tmp → i ≠ abi.dbl →
      work i = work₀ i) ∧
    out = out₀

private theorem binaryShiftMulDoubleTM_hoareTime_frame {n : ℕ}
    (abi : BinaryShiftMulABI n) (shift : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hshift : (work₀ abi.shift).HasBinaryNat shift)
    (htmp : (work₀ abi.tmp).HasBinaryNat 0)
    (hdbl : (work₀ abi.dbl).HasBinaryNat 0)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryShiftMulDoubleTM abi).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (binaryShiftMulDoublePost abi shift inp₀ work₀ out₀)
      (binaryShiftMulDoubleTime shift) := by
  have hcopy₁ := binaryCopyIntoTM_hoareTime_frame abi.shift abi.tmp abi.dbl
    abi.shift_ne_tmp abi.shift_ne_dbl abi.tmp_ne_dbl shift 0
    inp₀ work₀ out₀ hshift htmp hdbl hinput (fun i _ _ _ => hwork i)
    houtput
  let work₁ := Function.update work₀ abi.tmp (binaryShiftMulNatTape shift)
  have hcopy₁' : (binaryCopyIntoTM abi.shift abi.tmp abi.dbl).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
      (binaryCopyTime shift 0) := by
    simpa only [work₁, binaryShiftMulNatTape] using hcopy₁
  have hwork₁ : ∀ i, Parked (work₁ i) := by
    intro i
    by_cases hi : i = abi.tmp
    · subst i
      simp only [work₁, Function.update_self]
      exact hasBinaryNat_parked (binaryShiftMulNatTape_hasBinaryNat shift)
    simp only [work₁, Function.update_of_ne hi]
    exact hwork i
  have hshift₁ : (work₁ abi.shift).HasBinaryNat shift := by
    simpa only [work₁, Function.update_of_ne abi.shift_ne_tmp] using hshift
  have htmp₁ : (work₁ abi.tmp).HasBinaryNat shift := by
    simp only [work₁, Function.update_self]
    exact binaryShiftMulNatTape_hasBinaryNat shift
  have hdbl₁ : (work₁ abi.dbl).HasBinaryNat 0 := by
    simpa only [work₁, Function.update_of_ne abi.tmp_ne_dbl.symm] using hdbl
  let AddPost : TapePred n := fun inp work out =>
    inp = inp₀ ∧
    (work abi.shift).HasBinaryNat shift ∧
    (work abi.tmp).HasBinaryNat shift ∧
    (work abi.dbl).HasBinaryNat (shift + shift) ∧
    (∀ i, i ≠ abi.shift → i ≠ abi.tmp → i ≠ abi.dbl →
      work i = work₁ i) ∧
    out = out₀
  have hdistinctAdd : BinaryRippleAddDistinct abi.shift abi.tmp abi.dbl :=
    ⟨abi.shift_ne_tmp, abi.shift_ne_dbl, abi.tmp_ne_dbl⟩
  have hadd := binaryRippleAddTM_hoareTime_frame abi.shift abi.tmp abi.dbl
    hdistinctAdd shift shift inp₀ work₁ out₀ hshift₁ htmp₁ hdbl₁
    hinput (fun i _ _ _ => hwork₁ i) houtput
  have hadd' : (binaryRippleAddTM abi.shift abi.tmp abi.dbl).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
      AddPost (binaryRippleAddTime shift shift) := by
    simpa only [AddPost] using hadd
  have hfinish :
      (seqTM (resetBinaryWorkTM abi.tmp)
        (seqTM (binaryCopyIntoTM abi.dbl abi.shift abi.tmp)
          (resetBinaryWorkTM abi.dbl))).HoareTime
        AddPost (binaryShiftMulDoublePost abi shift inp₀ work₀ out₀)
        (resetBinaryWorkTime 1 shift.size + 1 +
          (binaryCopyTime (shift + shift) shift + 1 +
            resetBinaryWorkTime 1 (shift + shift).size)) := by
    intro inp work out hpre
    rcases hpre with ⟨hinp, hshiftNow, htmpNow, hdblNow, hframe, hout⟩
    have hworkNow : ∀ i, Parked (work i) := by
      intro i
      by_cases hshiftIdx : i = abi.shift
      · subst i
        exact hasBinaryNat_parked hshiftNow
      by_cases htmpIdx : i = abi.tmp
      · subst i
        exact hasBinaryNat_parked htmpNow
      by_cases hdblIdx : i = abi.dbl
      · subst i
        exact hasBinaryNat_parked hdblNow
      rw [hframe i hshiftIdx htmpIdx hdblIdx]
      exact hwork₁ i
    have hresetTmp := resetBinaryWorkTM_hoareTime_frame abi.tmp shift.bits 1
      inp work out htmpNow.2.hasBinaryContent htmpNow.1
      ⟨by rw [htmpNow.2.1], by rw [htmpNow.2.1]⟩
      (hinp.symm ▸ hinput) (fun i _ => hworkNow i)
      (hout.symm ▸ houtput)
    let work₂ := Function.update work abi.tmp (binaryShiftMulNatTape 0)
    have hresetTmp' : (resetBinaryWorkTM abi.tmp).HoareTime
        (fun inp' work' out' => inp' = inp ∧ work' = work ∧ out' = out)
        (fun inp' work' out' => inp' = inp ∧ work' = work₂ ∧ out' = out)
        (resetBinaryWorkTime 1 shift.size) := by
      simpa only [work₂, binaryShiftMulNatTape,
        Nat.size_eq_bits_len] using! hresetTmp
    have hwork₂ : ∀ i, Parked (work₂ i) := by
      intro i
      by_cases hi : i = abi.tmp
      · subst i
        simp only [work₂, Function.update_self]
        exact hasBinaryNat_parked (binaryShiftMulNatTape_hasBinaryNat 0)
      simp only [work₂, Function.update_of_ne hi]
      exact hworkNow i
    have hdbl₂ : (work₂ abi.dbl).HasBinaryNat (shift + shift) := by
      simpa only [work₂, Function.update_of_ne abi.tmp_ne_dbl.symm] using
        hdblNow
    have hshift₂ : (work₂ abi.shift).HasBinaryNat shift := by
      simpa only [work₂, Function.update_of_ne abi.shift_ne_tmp] using
        hshiftNow
    have htmp₂ : (work₂ abi.tmp).HasBinaryNat 0 := by
      simp only [work₂, Function.update_self]
      exact binaryShiftMulNatTape_hasBinaryNat 0
    have hcopy₂ := binaryCopyIntoTM_hoareTime_frame abi.dbl abi.shift abi.tmp
      abi.shift_ne_dbl.symm abi.tmp_ne_dbl.symm abi.shift_ne_tmp
      (shift + shift) shift inp work₂ out hdbl₂ hshift₂ htmp₂
      (hinp.symm ▸ hinput) (fun i _ _ _ => hwork₂ i)
      (hout.symm ▸ houtput)
    let work₃ := Function.update work₂ abi.shift
      (binaryShiftMulNatTape (shift + shift))
    have hcopy₂' : (binaryCopyIntoTM abi.dbl abi.shift abi.tmp).HoareTime
        (fun inp' work' out' => inp' = inp ∧ work' = work₂ ∧ out' = out)
        (fun inp' work' out' => inp' = inp ∧ work' = work₃ ∧ out' = out)
        (binaryCopyTime (shift + shift) shift) := by
      simpa only [work₃, binaryShiftMulNatTape] using hcopy₂
    have hwork₃ : ∀ i, Parked (work₃ i) := by
      intro i
      by_cases hi : i = abi.shift
      · subst i
        simp only [work₃, Function.update_self]
        exact hasBinaryNat_parked
          (binaryShiftMulNatTape_hasBinaryNat (shift + shift))
      simp only [work₃, Function.update_of_ne hi]
      exact hwork₂ i
    have hdbl₃ : (work₃ abi.dbl).HasBinaryNat (shift + shift) := by
      simpa only [work₃, Function.update_of_ne abi.shift_ne_dbl.symm] using
        hdbl₂
    have hresetDbl := resetBinaryWorkTM_hoareTime_frame abi.dbl
      (shift + shift).bits 1 inp work₃ out hdbl₃.2.hasBinaryContent hdbl₃.1
      ⟨by rw [hdbl₃.2.1], by rw [hdbl₃.2.1]⟩
      (hinp.symm ▸ hinput) (fun i _ => hwork₃ i)
      (hout.symm ▸ houtput)
    have hcopyTail := seqTM_hoareTime
      (binaryCopyIntoTM abi.dbl abi.shift abi.tmp)
      (resetBinaryWorkTM abi.dbl) hcopy₂'
      (binaryShiftMulExactFrame_transition inp work₃ out
        (hinp.symm ▸ hinput) hwork₃ (hout.symm ▸ houtput)) hresetDbl
    have hresetTail := seqTM_hoareTime (resetBinaryWorkTM abi.tmp)
      (seqTM (binaryCopyIntoTM abi.dbl abi.shift abi.tmp)
        (resetBinaryWorkTM abi.dbl)) hresetTmp'
      (binaryShiftMulExactFrame_transition inp work₂ out
        (hinp.symm ▸ hinput) hwork₂ (hout.symm ▸ houtput)) hcopyTail
    obtain ⟨c', time, htime, hreach, hhalt, hfinalInput, hfinalWork,
        hfinalOutput⟩ := hresetTail inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨c', time, (by
      simpa [Nat.size_eq_bits_len, Nat.add_assoc] using htime),
      hreach, hhalt, ?_⟩
    refine ⟨hfinalInput.trans hinp, ?_, ?_, ?_, ?_,
      hfinalOutput.trans hout⟩
    · rw [hfinalWork]
      simp only [Function.update_of_ne abi.shift_ne_dbl,
        work₃, Function.update_self]
      simpa [two_mul] using
        binaryShiftMulNatTape_hasBinaryNat (shift + shift)
    · rw [hfinalWork]
      simp only [Function.update_of_ne abi.tmp_ne_dbl,
        work₃, Function.update_of_ne abi.shift_ne_tmp.symm,
        work₂, Function.update_self]
      exact binaryShiftMulNatTape_hasBinaryNat 0
    · rw [hfinalWork, Function.update_self]
      exact binaryShiftMulNatTape_hasBinaryNat 0
    · intro i hshiftIdx htmpIdx hdblIdx
      rw [hfinalWork, Function.update_of_ne hdblIdx]
      simp only [work₃, Function.update_of_ne hshiftIdx,
        work₂, Function.update_of_ne htmpIdx]
      exact (hframe i hshiftIdx htmpIdx hdblIdx).trans (by
        simp only [work₁, Function.update_of_ne htmpIdx])
  have haddTail := seqTM_hoareTime
    (binaryRippleAddTM abi.shift abi.tmp abi.dbl)
    (seqTM (resetBinaryWorkTM abi.tmp)
      (seqTM (binaryCopyIntoTM abi.dbl abi.shift abi.tmp)
        (resetBinaryWorkTM abi.dbl))) hadd'
    (by
      intro inp work out hpost
      rcases hpost with ⟨hinp, hshiftNow, htmpNow, hdblNow, hframe, hout⟩
      have hreads : ∀ i, (work i).read ≠ Γ.start := by
        intro i
        by_cases hshiftIdx : i = abi.shift
        · subst i
          exact (hasBinaryNat_parked hshiftNow).read_ne_start
        by_cases htmpIdx : i = abi.tmp
        · subst i
          exact (hasBinaryNat_parked htmpNow).read_ne_start
        by_cases hdblIdx : i = abi.dbl
        · subst i
          exact (hasBinaryNat_parked hdblNow).read_ne_start
        rw [hframe i hshiftIdx htmpIdx hdblIdx]
        exact (hwork₁ i).read_ne_start
      obtain ⟨hi, hw, ho⟩ := phaseTransition_eq_self_of_reads_ne_start
        (hinp.symm ▸ hinput.read_ne_start) hreads
        (hout.symm ▸ houtput.read_ne_start)
      rw [hi, hw, ho]
      exact ⟨hinp, hshiftNow, htmpNow, hdblNow, hframe, hout⟩)
    hfinish
  have hrun := seqTM_hoareTime
    (binaryCopyIntoTM abi.shift abi.tmp abi.dbl)
    (seqTM (binaryRippleAddTM abi.shift abi.tmp abi.dbl)
      (seqTM (resetBinaryWorkTM abi.tmp)
        (seqTM (binaryCopyIntoTM abi.dbl abi.shift abi.tmp)
          (resetBinaryWorkTM abi.dbl)))) hcopy₁'
    (binaryShiftMulExactFrame_transition inp₀ work₁ out₀ hinput hwork₁
      houtput) haddTail
  simpa [binaryShiftMulDoubleTM, binaryShiftMulDoubleTime,
    Nat.add_assoc] using hrun

private def binaryShiftMulOneTime (acc shift : ℕ) : ℕ :=
  binaryShiftMulUpdateTime acc shift + 1 + binaryShiftMulDoubleTime shift

private def binaryShiftMulOnePost {n : ℕ} (abi : BinaryShiftMulABI n)
    (acc shift : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (out₀ : Tape) : TapePred n :=
  fun inp work out =>
    inp = inp₀ ∧
    (work abi.acc).HasBinaryNat (acc + shift) ∧
    (work abi.shift).HasBinaryNat (2 * shift) ∧
    (work abi.tmp).HasBinaryNat 0 ∧
    (work abi.dbl).HasBinaryNat 0 ∧
    (∀ i, i ≠ abi.acc → i ≠ abi.shift → i ≠ abi.tmp → i ≠ abi.dbl →
      work i = work₀ i) ∧
    out = out₀

private theorem binaryShiftMulOneTM_hoareTime_frame {n : ℕ}
    (abi : BinaryShiftMulABI n) (acc shift : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hacc : (work₀ abi.acc).HasBinaryNat acc)
    (hshift : (work₀ abi.shift).HasBinaryNat shift)
    (htmp : (work₀ abi.tmp).HasBinaryNat 0)
    (hdbl : (work₀ abi.dbl).HasBinaryNat 0)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryShiftMulOneTM abi).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (binaryShiftMulOnePost abi acc shift inp₀ work₀ out₀)
      (binaryShiftMulOneTime acc shift) := by
  have hupdate := binaryShiftMulUpdateTM_hoareTime_frame abi acc shift
    inp₀ work₀ out₀ hacc hshift htmp hdbl hinput hwork houtput
  have hdouble : (binaryShiftMulDoubleTM abi).HoareTime
      (binaryShiftMulUpdatePost abi acc shift inp₀ work₀ out₀)
      (binaryShiftMulOnePost abi acc shift inp₀ work₀ out₀)
      (binaryShiftMulDoubleTime shift) := by
    intro inp work out hpre
    rcases hpre with ⟨hinp, haccNow, hshiftNow, htmpNow, hdblNow,
      hframe, hout⟩
    have hworkNow : ∀ i, Parked (work i) := by
      intro i
      by_cases haccIdx : i = abi.acc
      · subst i
        exact hasBinaryNat_parked haccNow
      by_cases hshiftIdx : i = abi.shift
      · subst i
        exact hasBinaryNat_parked hshiftNow
      by_cases htmpIdx : i = abi.tmp
      · subst i
        exact hasBinaryNat_parked htmpNow
      by_cases hdblIdx : i = abi.dbl
      · subst i
        exact hasBinaryNat_parked hdblNow
      rw [hframe i haccIdx hshiftIdx htmpIdx hdblIdx]
      exact hwork i
    have hrun := binaryShiftMulDoubleTM_hoareTime_frame abi shift
      inp work out hshiftNow htmpNow hdblNow (hinp.symm ▸ hinput)
      hworkNow (hout.symm ▸ houtput)
    obtain ⟨c', time, htime, hreach, hhalt, hfinalInput, hfinalShift,
        hfinalTmp, hfinalDbl, hfinalFrame, hfinalOutput⟩ :=
      hrun inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨c', time, htime, hreach, hhalt, ?_⟩
    refine ⟨hfinalInput.trans hinp, ?_, hfinalShift, hfinalTmp, hfinalDbl,
      ?_, hfinalOutput.trans hout⟩
    · rw [hfinalFrame abi.acc abi.acc_ne_shift abi.acc_ne_tmp
        abi.acc_ne_dbl]
      exact haccNow
    · intro i haccIdx hshiftIdx htmpIdx hdblIdx
      exact (hfinalFrame i hshiftIdx htmpIdx hdblIdx).trans
        (hframe i haccIdx hshiftIdx htmpIdx hdblIdx)
  have htransition : ∀ inp work out,
      binaryShiftMulUpdatePost abi acc shift inp₀ work₀ out₀ inp work out →
      binaryShiftMulUpdatePost abi acc shift inp₀ work₀ out₀
        (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out) := by
    intro inp work out hpost
    rcases hpost with ⟨hinp, haccNow, hshiftNow, htmpNow, hdblNow,
      hframe, hout⟩
    have hreads : ∀ i, (work i).read ≠ Γ.start := by
      intro i
      by_cases haccIdx : i = abi.acc
      · subst i
        exact (hasBinaryNat_parked haccNow).read_ne_start
      by_cases hshiftIdx : i = abi.shift
      · subst i
        exact (hasBinaryNat_parked hshiftNow).read_ne_start
      by_cases htmpIdx : i = abi.tmp
      · subst i
        exact (hasBinaryNat_parked htmpNow).read_ne_start
      by_cases hdblIdx : i = abi.dbl
      · subst i
        exact (hasBinaryNat_parked hdblNow).read_ne_start
      rw [hframe i haccIdx hshiftIdx htmpIdx hdblIdx]
      exact (hwork i).read_ne_start
    obtain ⟨hi, hw, ho⟩ := phaseTransition_eq_self_of_reads_ne_start
      (hinp.symm ▸ hinput.read_ne_start) hreads
      (hout.symm ▸ houtput.read_ne_start)
    rw [hi, hw, ho]
    exact ⟨hinp, haccNow, hshiftNow, htmpNow, hdblNow, hframe, hout⟩
  have hrun := seqTM_hoareTime (binaryShiftMulUpdateTM abi)
    (binaryShiftMulDoubleTM abi) hupdate htransition hdouble
  simpa [binaryShiftMulOneTM, binaryShiftMulOneTime] using hrun

private def binaryShiftMulBodyTime (bit : Bool) (acc shift : ℕ) : ℕ :=
  (if bit then binaryShiftMulOneTime acc shift
    else binaryShiftMulDoubleTime shift) + 1

private theorem binaryShiftMulUpdateTime_le (acc shift width : ℕ)
    (hacc : acc.size ≤ width) (hshift : shift.size ≤ width) :
    binaryShiftMulUpdateTime acc shift ≤ 13 * width + 50 := by
  have haddSize := binaryRippleAdd_sum_size_le acc shift
  have hsum : (acc + shift).size ≤ width + 1 := by
    exact haddSize.trans (Nat.add_le_add_right (max_le hacc hshift) 1)
  have haddTime := binaryRippleAddTime_le acc shift
  have hcopyTime := binaryCopyTime_le (acc + shift) acc
  simp only [binaryShiftMulUpdateTime, resetBinaryWorkTime,
    clearWorkTimeBound]
  omega

private theorem binaryShiftMulDoubleTime_le (shift width : ℕ)
    (hshift : shift.size ≤ width) :
    binaryShiftMulDoubleTime shift ≤ 20 * width + 110 := by
  have hdoubleSize := binaryRippleAdd_sum_size_le shift shift
  have hsum : (shift + shift).size ≤ width + 1 := by
    exact hdoubleSize.trans
      (Nat.add_le_add_right (max_le hshift hshift) 1)
  have hcopy₁ := binaryCopyTime_le shift 0
  simp only [Nat.size_zero, Nat.mul_zero, Nat.add_zero] at hcopy₁
  have hadd := binaryRippleAddTime_le shift shift
  have hcopy₂ := binaryCopyTime_le (shift + shift) shift
  simp only [binaryShiftMulDoubleTime, resetBinaryWorkTime,
    clearWorkTimeBound]
  omega

private theorem binaryShiftMulBodyTime_le (bit : Bool) (acc shift width : ℕ)
    (hacc : acc.size ≤ width) (hshift : shift.size ≤ width) :
    binaryShiftMulBodyTime bit acc shift ≤ 33 * width + 162 := by
  have hupdate := binaryShiftMulUpdateTime_le acc shift width hacc hshift
  have hdouble := binaryShiftMulDoubleTime_le shift width hshift
  cases bit <;>
    simp only [binaryShiftMulBodyTime, binaryShiftMulOneTime,
      Bool.false_eq_true, ite_false, if_true] <;>
    omega

private theorem forBinaryWorkLoopTime_le
    (bodyTime : ℕ → ℕ) (total bound : ℕ)
    (hbody : ∀ i, i < total → bodyTime i ≤ bound) :
    ∀ count value, value + count = total →
      forBinaryWorkLoopTime bodyTime value count ≤ count * (bound + 2) + 1 := by
  intro count
  induction count with
  | zero =>
      intro value _
      simp [forBinaryWorkLoopTime]
  | succ count ih =>
      intro value htotal
      have hvalue : value < total := by omega
      have htail := ih (value + 1) (by omega)
      have hhead := hbody value hvalue
      simp only [forBinaryWorkLoopTime]
      rw [Nat.succ_mul]
      omega

private def binaryShiftMulBodyPost {n : ℕ} (abi : BinaryShiftMulABI n)
    (bit : Bool) (acc shift : ℕ) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (out₀ : Tape) : TapePred n :=
  fun inp work out =>
    inp = inp₀ ∧
    (work abi.acc).HasBinaryNat (BinaryShiftMul.step bit acc shift).1 ∧
    (work abi.shift).HasBinaryNat (BinaryShiftMul.step bit acc shift).2 ∧
    (work abi.tmp).HasBinaryNat 0 ∧
    (work abi.dbl).HasBinaryNat 0 ∧
    (∀ i, i ≠ abi.acc → i ≠ abi.shift → i ≠ abi.tmp → i ≠ abi.dbl →
      work i = work₀ i) ∧
    out = out₀

private theorem binaryShiftMulBitBodyTM_hoareTime_frame {n : ℕ}
    (abi : BinaryShiftMulABI n) (bit : Bool) (acc shift : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hbit : (work₀ abi.rhs).read = Γ.ofBool bit)
    (hacc : (work₀ abi.acc).HasBinaryNat acc)
    (hshift : (work₀ abi.shift).HasBinaryNat shift)
    (htmp : (work₀ abi.tmp).HasBinaryNat 0)
    (hdbl : (work₀ abi.dbl).HasBinaryNat 0)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryShiftMulBitBodyTM abi).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (binaryShiftMulBodyPost abi bit acc shift inp₀ work₀ out₀)
      (binaryShiftMulBodyTime bit acc shift) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hworkEq, hout⟩
  subst inp
  subst work
  subst out
  cases bit with
  | false =>
      have hrun := binaryShiftMulDoubleTM_hoareTime_frame abi shift
        inp₀ work₀ out₀ hshift htmp hdbl hinput hwork houtput
        inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩
      obtain ⟨c', time, htime, hreach, hhalt, hfinalInput, hfinalShift,
          hfinalTmp, hfinalDbl, hfinalFrame, hfinalOutput⟩ := hrun
      have hne : (work₀ abi.rhs).read ≠ Γ.one := by
        rw [hbit]
        decide
      obtain ⟨C, hbranch, hbranchHalt, hinputEq, hworkEq, houtputEq⟩ :=
        branchWorkSymbolTM_reachesIn_different_frame abi.rhs Γ.one
          (binaryShiftMulOneTM abi) (binaryShiftMulDoubleTM abi)
          inp₀ work₀ out₀ hne hinput.read_ne_start
          (fun i => (hwork i).read_ne_start) houtput.read_ne_start
          hreach hhalt
      refine ⟨C, time + 1, ?_, hbranch, hbranchHalt, ?_⟩
      · simpa [binaryShiftMulBodyTime] using Nat.add_le_add_right htime 1
      · refine ⟨hinputEq.trans hfinalInput, ?_, ?_, ?_, ?_, ?_,
          houtputEq.trans hfinalOutput⟩
        · rw [hworkEq, hfinalFrame abi.acc abi.acc_ne_shift abi.acc_ne_tmp
            abi.acc_ne_dbl]
          simpa [BinaryShiftMul.step] using hacc
        · rw [hworkEq]
          simpa [BinaryShiftMul.step] using hfinalShift
        · rw [hworkEq]
          exact hfinalTmp
        · rw [hworkEq]
          exact hfinalDbl
        · intro i haccIdx hshiftIdx htmpIdx hdblIdx
          rw [hworkEq, hfinalFrame i hshiftIdx htmpIdx hdblIdx]
  | true =>
      have hrun := binaryShiftMulOneTM_hoareTime_frame abi acc shift
        inp₀ work₀ out₀ hacc hshift htmp hdbl hinput hwork houtput
        inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩
      obtain ⟨c', time, htime, hreach, hhalt, hfinalInput, hfinalAcc,
          hfinalShift, hfinalTmp, hfinalDbl, hfinalFrame,
          hfinalOutput⟩ := hrun
      have heq : (work₀ abi.rhs).read = Γ.one := by
        simpa using! hbit
      obtain ⟨C, hbranch, hbranchHalt, hinputEq, hworkEq, houtputEq⟩ :=
        branchWorkSymbolTM_reachesIn_equal_frame abi.rhs Γ.one
          (binaryShiftMulOneTM abi) (binaryShiftMulDoubleTM abi)
          inp₀ work₀ out₀ heq hinput.read_ne_start
          (fun i => (hwork i).read_ne_start) houtput.read_ne_start
          hreach hhalt
      refine ⟨C, time + 1, ?_, hbranch, hbranchHalt, ?_⟩
      · simpa [binaryShiftMulBodyTime] using Nat.add_le_add_right htime 1
      · refine ⟨hinputEq.trans hfinalInput, ?_, ?_, ?_, ?_, ?_,
          houtputEq.trans hfinalOutput⟩
        · rw [hworkEq]
          simpa [BinaryShiftMul.step] using hfinalAcc
        · rw [hworkEq]
          simpa [BinaryShiftMul.step] using hfinalShift
        · rw [hworkEq]
          exact hfinalTmp
        · rw [hworkEq]
          exact hfinalDbl
        · intro i haccIdx hshiftIdx htmpIdx hdblIdx
          rw [hworkEq, hfinalFrame i haccIdx hshiftIdx htmpIdx hdblIdx]

private def binaryShiftMulBitAt (rhs i : ℕ) : Bool :=
  (rhs.bits[i]?).getD false

private theorem binaryShiftMulBitAt_eq_get (rhs i : ℕ) (hi : i < rhs.size) :
    binaryShiftMulBitAt rhs i =
      rhs.bits.get ⟨i, by simpa [Nat.size_eq_bits_len] using hi⟩ := by
  simp [binaryShiftMulBitAt,
    show i < rhs.bits.length by simpa [Nat.size_eq_bits_len] using hi]

private def binaryShiftMulCursorTape (tape : Tape) (index : ℕ) : Tape :=
  { head := index + 1, cells := tape.cells }

private def binaryShiftMulLoopWork {n : ℕ} (abi : BinaryShiftMulABI n)
    (work₀ : Fin n → Tape) (index acc shift : ℕ) : Fin n → Tape :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update work₀ abi.rhs
            (binaryShiftMulCursorTape (work₀ abi.rhs) index))
          abi.acc (binaryShiftMulNatTape acc))
        abi.shift (binaryShiftMulNatTape shift))
      abi.tmp (binaryShiftMulNatTape 0))
    abi.dbl (binaryShiftMulNatTape 0)

private theorem binaryShiftMulLoopWork_rhs {n : ℕ}
    (abi : BinaryShiftMulABI n) (work₀ : Fin n → Tape)
    (index acc shift : ℕ) :
    binaryShiftMulLoopWork abi work₀ index acc shift abi.rhs =
      binaryShiftMulCursorTape (work₀ abi.rhs) index := by
  simp [binaryShiftMulLoopWork]

private theorem binaryShiftMulLoopWork_acc {n : ℕ}
    (abi : BinaryShiftMulABI n) (work₀ : Fin n → Tape)
    (index acc shift : ℕ) :
    binaryShiftMulLoopWork abi work₀ index acc shift abi.acc =
      binaryShiftMulNatTape acc := by
  simp [binaryShiftMulLoopWork]

private theorem binaryShiftMulLoopWork_shift {n : ℕ}
    (abi : BinaryShiftMulABI n) (work₀ : Fin n → Tape)
    (index acc shift : ℕ) :
    binaryShiftMulLoopWork abi work₀ index acc shift abi.shift =
      binaryShiftMulNatTape shift := by
  simp [binaryShiftMulLoopWork]

private theorem binaryShiftMulLoopWork_tmp {n : ℕ}
    (abi : BinaryShiftMulABI n) (work₀ : Fin n → Tape)
    (index acc shift : ℕ) :
    binaryShiftMulLoopWork abi work₀ index acc shift abi.tmp =
      binaryShiftMulNatTape 0 := by
  simp [binaryShiftMulLoopWork]

private theorem binaryShiftMulLoopWork_dbl {n : ℕ}
    (abi : BinaryShiftMulABI n) (work₀ : Fin n → Tape)
    (index acc shift : ℕ) :
    binaryShiftMulLoopWork abi work₀ index acc shift abi.dbl =
      binaryShiftMulNatTape 0 := by
  simp [binaryShiftMulLoopWork]

private theorem binaryShiftMulLoopWork_other {n : ℕ}
    (abi : BinaryShiftMulABI n) (work₀ : Fin n → Tape)
    (index acc shift : ℕ) (i : Fin n)
    (hrhs : i ≠ abi.rhs) (hacc : i ≠ abi.acc)
    (hshift : i ≠ abi.shift) (htmp : i ≠ abi.tmp)
    (hdbl : i ≠ abi.dbl) :
    binaryShiftMulLoopWork abi work₀ index acc shift i = work₀ i := by
  simp [binaryShiftMulLoopWork, hrhs, hacc, hshift, htmp, hdbl]

private theorem binaryShiftMulCursorTape_parked {tape : Tape}
    (h : Parked tape) (index : ℕ) :
    Parked (binaryShiftMulCursorTape tape index) := by
  exact ⟨by simp [binaryShiftMulCursorTape], by
    simpa [binaryShiftMulCursorTape] using h.2⟩

private theorem binaryShiftMulLoopWork_parked {n : ℕ}
    (abi : BinaryShiftMulABI n) (work₀ : Fin n → Tape)
    (index acc shift : ℕ) (hwork : ∀ i, Parked (work₀ i)) :
    ∀ i, Parked (binaryShiftMulLoopWork abi work₀ index acc shift i) := by
  intro i
  by_cases hrhs : i = abi.rhs
  · subst i
    rw [binaryShiftMulLoopWork_rhs]
    exact binaryShiftMulCursorTape_parked (hwork abi.rhs) index
  by_cases hacc : i = abi.acc
  · subst i
    rw [binaryShiftMulLoopWork_acc]
    exact hasBinaryNat_parked (binaryShiftMulNatTape_hasBinaryNat acc)
  by_cases hshift : i = abi.shift
  · subst i
    rw [binaryShiftMulLoopWork_shift]
    exact hasBinaryNat_parked (binaryShiftMulNatTape_hasBinaryNat shift)
  by_cases htmp : i = abi.tmp
  · subst i
    rw [binaryShiftMulLoopWork_tmp]
    exact hasBinaryNat_parked (binaryShiftMulNatTape_hasBinaryNat 0)
  by_cases hdbl : i = abi.dbl
  · subst i
    rw [binaryShiftMulLoopWork_dbl]
    exact hasBinaryNat_parked (binaryShiftMulNatTape_hasBinaryNat 0)
  rw [binaryShiftMulLoopWork_other abi work₀ index acc shift i hrhs hacc
    hshift htmp hdbl]
  exact hwork i

private theorem binaryShiftMulLoopWork_read_bit {n : ℕ}
    (abi : BinaryShiftMulABI n) (work₀ : Fin n → Tape)
    (rhs index acc shift : ℕ) (hrhs : (work₀ abi.rhs).HasBinaryNat rhs)
    (hi : index < rhs.size) :
    (binaryShiftMulLoopWork abi work₀ index acc shift abi.rhs).read =
      Γ.ofBool (binaryShiftMulBitAt rhs index) := by
  rw [binaryShiftMulLoopWork_rhs, Tape.read]
  simp only [binaryShiftMulCursorTape]
  rw [binaryShiftMulBitAt_eq_get rhs index hi]
  exact hrhs.2.2.1 index (by simpa [Nat.size_eq_bits_len] using hi)

private theorem binaryShiftMulLoopWork_read_blank {n : ℕ}
    (abi : BinaryShiftMulABI n) (work₀ : Fin n → Tape)
    (rhs acc shift : ℕ) (hrhs : (work₀ abi.rhs).HasBinaryNat rhs) :
    (binaryShiftMulLoopWork abi work₀ rhs.size acc shift abi.rhs).read =
      Γ.blank := by
  rw [binaryShiftMulLoopWork_rhs, Tape.read]
  simp only [binaryShiftMulCursorTape]
  exact hrhs.2.2.2 rhs.size (by simp [Nat.size_eq_bits_len])

private theorem binaryShiftMulLoopWork_advance {n : ℕ}
    (abi : BinaryShiftMulABI n) (work₀ : Fin n → Tape)
    (index acc shift : ℕ) :
    (fun i => if i = abi.rhs then
      (binaryShiftMulLoopWork abi work₀ index acc shift i).move Dir3.right
      else binaryShiftMulLoopWork abi work₀ index acc shift i) =
    binaryShiftMulLoopWork abi work₀ (index + 1) acc shift := by
  funext i
  by_cases hrhs : i = abi.rhs
  · subst i
    simp only [ite_eq_left, binaryShiftMulLoopWork_rhs]
    simp [binaryShiftMulCursorTape, Tape.move]
  · rw [ite_eq_right hrhs]
    by_cases hacc : i = abi.acc
    · subst i
      rw [binaryShiftMulLoopWork_acc, binaryShiftMulLoopWork_acc]
    by_cases hshift : i = abi.shift
    · subst i
      rw [binaryShiftMulLoopWork_shift, binaryShiftMulLoopWork_shift]
    by_cases htmp : i = abi.tmp
    · subst i
      rw [binaryShiftMulLoopWork_tmp, binaryShiftMulLoopWork_tmp]
    by_cases hdbl : i = abi.dbl
    · subst i
      rw [binaryShiftMulLoopWork_dbl, binaryShiftMulLoopWork_dbl]
    rw [binaryShiftMulLoopWork_other abi work₀ index acc shift i hrhs hacc
      hshift htmp hdbl,
      binaryShiftMulLoopWork_other abi work₀ (index + 1) acc shift i hrhs
        hacc hshift htmp hdbl]

private def binaryShiftMulPartialWork {n : ℕ} (abi : BinaryShiftMulABI n)
    (work₀ : Fin n → Tape) (lhs rhs index : ℕ) : Fin n → Tape :=
  binaryShiftMulLoopWork abi work₀ index
    (BinaryShiftMul.partialAcc lhs rhs index)
    (BinaryShiftMul.partialShift lhs index)

private def binaryShiftMulBodyDoneWork {n : ℕ}
    (abi : BinaryShiftMulABI n) (work₀ : Fin n → Tape)
    (lhs rhs index : ℕ) : Fin n → Tape :=
  binaryShiftMulLoopWork abi work₀ index
    (BinaryShiftMul.partialAcc lhs rhs (index + 1))
    (BinaryShiftMul.partialShift lhs (index + 1))

private def binaryShiftMulScanCfg {n : ℕ} (abi : BinaryShiftMulABI n)
    (lhs rhs index : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (out₀ : Tape) :
    Cfg n (forBinaryWorkTM abi.rhs (binaryShiftMulBitBodyTM abi)).Q :=
  { state := .inl .scan
    input := inp₀
    work := binaryShiftMulPartialWork abi work₀ lhs rhs index
    output := out₀ }

private def binaryShiftMulBodyStartCfg {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs index : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape) :
    Cfg n (forBinaryWorkTM abi.rhs (binaryShiftMulBitBodyTM abi)).Q :=
  { state := .inr (binaryShiftMulBitBodyTM abi).qstart
    input := inp₀
    work := binaryShiftMulPartialWork abi work₀ lhs rhs index
    output := out₀ }

private def binaryShiftMulBodyDoneCfg {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs index : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape) :
    Cfg n (forBinaryWorkTM abi.rhs (binaryShiftMulBitBodyTM abi)).Q :=
  { state := .inr (binaryShiftMulBitBodyTM abi).qhalt
    input := inp₀
    work := binaryShiftMulBodyDoneWork abi work₀ lhs rhs index
    output := out₀ }

private def binaryShiftMulDoneCfg {n : ℕ} (abi : BinaryShiftMulABI n)
    (lhs rhs : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (out₀ : Tape) :
    Cfg n (forBinaryWorkTM abi.rhs (binaryShiftMulBitBodyTM abi)).Q :=
  { state := .inl .done
    input := inp₀
    work := binaryShiftMulPartialWork abi work₀ lhs rhs rhs.size
    output := out₀ }

private theorem binaryShiftMulBody_run {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs index : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hrhs : (work₀ abi.rhs).HasBinaryNat rhs)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) (hi : index < rhs.size) :
    ∃ time,
      time ≤ binaryShiftMulBodyTime (binaryShiftMulBitAt rhs index)
        (BinaryShiftMul.partialAcc lhs rhs index)
        (BinaryShiftMul.partialShift lhs index) ∧
      (binaryShiftMulBitBodyTM abi).reachesIn time
        { state := (binaryShiftMulBitBodyTM abi).qstart
          input := inp₀
          work := binaryShiftMulPartialWork abi work₀ lhs rhs index
          output := out₀ }
        { state := (binaryShiftMulBitBodyTM abi).qhalt
          input := inp₀
          work := binaryShiftMulBodyDoneWork abi work₀ lhs rhs index
          output := out₀ } := by
  let acc := BinaryShiftMul.partialAcc lhs rhs index
  let shift := BinaryShiftMul.partialShift lhs index
  let work := binaryShiftMulPartialWork abi work₀ lhs rhs index
  have hworkParked : ∀ i, Parked (work i) := by
    exact binaryShiftMulLoopWork_parked abi work₀ index acc shift hwork
  have hacc : (work abi.acc).HasBinaryNat acc := by
    rw [show work = binaryShiftMulLoopWork abi work₀ index acc shift by rfl,
      binaryShiftMulLoopWork_acc]
    exact binaryShiftMulNatTape_hasBinaryNat acc
  have hshift : (work abi.shift).HasBinaryNat shift := by
    rw [show work = binaryShiftMulLoopWork abi work₀ index acc shift by rfl,
      binaryShiftMulLoopWork_shift]
    exact binaryShiftMulNatTape_hasBinaryNat shift
  have htmp : (work abi.tmp).HasBinaryNat 0 := by
    rw [show work = binaryShiftMulLoopWork abi work₀ index acc shift by rfl,
      binaryShiftMulLoopWork_tmp]
    exact binaryShiftMulNatTape_hasBinaryNat 0
  have hdbl : (work abi.dbl).HasBinaryNat 0 := by
    rw [show work = binaryShiftMulLoopWork abi work₀ index acc shift by rfl,
      binaryShiftMulLoopWork_dbl]
    exact binaryShiftMulNatTape_hasBinaryNat 0
  have hbit : (work abi.rhs).read =
      Γ.ofBool (binaryShiftMulBitAt rhs index) := by
    exact binaryShiftMulLoopWork_read_bit abi work₀ rhs index acc shift
      hrhs hi
  have hrun := binaryShiftMulBitBodyTM_hoareTime_frame abi
    (binaryShiftMulBitAt rhs index) acc shift inp₀ work out₀ hbit hacc
    hshift htmp hdbl hinput hworkParked houtput
    inp₀ work out₀ ⟨rfl, rfl, rfl⟩
  obtain ⟨c', time, htime, hreach, hhalt, hfinalInput, hfinalAcc,
      hfinalShift, hfinalTmp, hfinalDbl, hfinalFrame, hfinalOutput⟩ := hrun
  have hstep := BinaryShiftMul.step_partial_internal lhs rhs index hi
  rw [← binaryShiftMulBitAt_eq_get rhs index hi] at hstep
  have hfinalAcc' : (c'.work abi.acc).HasBinaryNat
      (BinaryShiftMul.partialAcc lhs rhs (index + 1)) := by
    simpa [acc, shift, hstep] using hfinalAcc
  have hfinalShift' : (c'.work abi.shift).HasBinaryNat
      (BinaryShiftMul.partialShift lhs (index + 1)) := by
    simpa [acc, shift, hstep] using hfinalShift
  have hfinalWork : c'.work =
      binaryShiftMulBodyDoneWork abi work₀ lhs rhs index := by
    funext i
    by_cases haccIdx : i = abi.acc
    · subst i
      rw [binaryShiftMulBodyDoneWork, binaryShiftMulLoopWork_acc]
      exact hfinalAcc'.eq_init_move_right
    by_cases hshiftIdx : i = abi.shift
    · subst i
      rw [binaryShiftMulBodyDoneWork, binaryShiftMulLoopWork_shift]
      exact hfinalShift'.eq_init_move_right
    by_cases htmpIdx : i = abi.tmp
    · subst i
      rw [binaryShiftMulBodyDoneWork, binaryShiftMulLoopWork_tmp]
      exact hfinalTmp.eq_init_move_right
    by_cases hdblIdx : i = abi.dbl
    · subst i
      rw [binaryShiftMulBodyDoneWork, binaryShiftMulLoopWork_dbl]
      exact hfinalDbl.eq_init_move_right
    rw [hfinalFrame i haccIdx hshiftIdx htmpIdx hdblIdx]
    simp [work, binaryShiftMulPartialWork, binaryShiftMulBodyDoneWork,
      binaryShiftMulLoopWork, haccIdx, hshiftIdx, htmpIdx, hdblIdx]
  refine ⟨time, htime, ?_⟩
  have hc : c' =
      { state := (binaryShiftMulBitBodyTM abi).qhalt
        input := inp₀
        work := binaryShiftMulBodyDoneWork abi work₀ lhs rhs index
        output := out₀ } := by
    exact Cfg.ext hhalt hfinalInput hfinalWork hfinalOutput
  simpa [work, hc] using hreach

private def binaryShiftMulLoopBound (lhs rhs : ℕ) : ℕ :=
  rhs.size * (33 * binaryShiftMulWidth lhs rhs + 164) + 1

private def binaryShiftMulLoopPost {n : ℕ} (abi : BinaryShiftMulABI n)
    (lhs rhs : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (out₀ : Tape) : TapePred n :=
  fun inp work out =>
    inp = inp₀ ∧
    (work abi.lhs).HasBinaryNat lhs ∧
    (work abi.rhs).HasBinaryContent rhs.bits ∧
    (work abi.rhs).cells 0 = Γ.start ∧
    (work abi.rhs).head = rhs.size + 1 ∧
    (work abi.acc).HasBinaryNat (lhs * rhs) ∧
    (work abi.shift).HasBinaryNat (lhs * 2 ^ rhs.size) ∧
    (work abi.tmp).HasBinaryNat 0 ∧
    (work abi.dbl).HasBinaryNat 0 ∧
    (∀ i, i ≠ abi.lhs → i ≠ abi.rhs → i ≠ abi.acc →
      i ≠ abi.shift → i ≠ abi.tmp → i ≠ abi.dbl → work i = work₀ i) ∧
    out = out₀

private theorem binaryShiftMulLoopTM_hoareTime_frame {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ abi.lhs).HasBinaryNat lhs)
    (hrhs : (work₀ abi.rhs).HasBinaryNat rhs)
    (hacc : (work₀ abi.acc).HasBinaryNat 0)
    (hshift : (work₀ abi.shift).HasBinaryNat lhs)
    (htmp : (work₀ abi.tmp).HasBinaryNat 0)
    (hdbl : (work₀ abi.dbl).HasBinaryNat 0)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryShiftMulLoopTM abi).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (binaryShiftMulLoopPost abi lhs rhs inp₀ work₀ out₀)
      (binaryShiftMulLoopBound lhs rhs) := by
  classical
  let body := binaryShiftMulBitBodyTM abi
  have hbodyExists : ∀ index, ∃ time, index < rhs.size →
      time ≤ binaryShiftMulBodyTime (binaryShiftMulBitAt rhs index)
        (BinaryShiftMul.partialAcc lhs rhs index)
        (BinaryShiftMul.partialShift lhs index) ∧
      body.reachesIn time
        { state := body.qstart
          input := inp₀
          work := binaryShiftMulPartialWork abi work₀ lhs rhs index
          output := out₀ }
        { state := body.qhalt
          input := inp₀
          work := binaryShiftMulBodyDoneWork abi work₀ lhs rhs index
          output := out₀ } := by
    intro index
    by_cases hi : index < rhs.size
    · obtain ⟨time, htime, hrun⟩ := binaryShiftMulBody_run abi lhs rhs
        index inp₀ work₀ out₀ hrhs hinput hwork houtput hi
      exact ⟨time, fun _ => ⟨htime, hrun⟩⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose bodyTime hbody using hbodyExists
  let spec : ForBinaryWorkLoopSpec abi.rhs body bodyTime rhs.size :=
    { scanCfg := fun index =>
        binaryShiftMulScanCfg abi lhs rhs index inp₀ work₀ out₀
      bodyStartCfg := fun index =>
        binaryShiftMulBodyStartCfg abi lhs rhs index inp₀ work₀ out₀
      bodyDoneCfg := fun index =>
        binaryShiftMulBodyDoneCfg abi lhs rhs index inp₀ work₀ out₀
      doneCfg := binaryShiftMulDoneCfg abi lhs rhs inp₀ work₀ out₀
      scanStep := by
        intro index hi
        apply forBinaryWorkTM_step_scan_bit_internal abi.rhs body
          (binaryShiftMulBitAt rhs index)
        · rfl
        · exact binaryShiftMulLoopWork_read_bit abi work₀ rhs index
            (BinaryShiftMul.partialAcc lhs rhs index)
            (BinaryShiftMul.partialShift lhs index) hrhs hi
        · exact hinput.read_ne_start
        · exact fun i => (binaryShiftMulLoopWork_parked abi work₀ index
            (BinaryShiftMul.partialAcc lhs rhs index)
            (BinaryShiftMul.partialShift lhs index) hwork i).read_ne_start
        · exact houtput.read_ne_start
      bodyRun := by
        intro index hi
        exact forBinaryWorkTM_body_reachesIn_internal abi.rhs body
          (hbody index hi).2
      loopbackStep := by
        intro index hi
        let acc := BinaryShiftMul.partialAcc lhs rhs (index + 1)
        let shift := BinaryShiftMul.partialShift lhs (index + 1)
        let work := binaryShiftMulBodyDoneWork abi work₀ lhs rhs index
        have hworkParked : ∀ i, Parked (work i) := by
          exact binaryShiftMulLoopWork_parked abi work₀ index acc shift
            hwork
        have hstep := forBinaryWorkTM_step_body_halt_internal abi.rhs body
          ({ state := body.qhalt
             input := inp₀
             work := work
             output := out₀ } : Cfg n body.Q) rfl hinput.read_ne_start
          (fun i => (hworkParked i).read_ne_start) houtput.read_ne_start
        have hadvance := binaryShiftMulLoopWork_advance abi work₀ index
          acc shift
        simpa [binaryShiftMulBodyDoneCfg, binaryShiftMulScanCfg,
          binaryShiftMulPartialWork, work, acc, shift,
          binaryShiftMulBodyDoneWork, body, hadvance] using! hstep
      stopStep := by
        apply forBinaryWorkTM_step_scan_blank_internal abi.rhs body
        · rfl
        · exact binaryShiftMulLoopWork_read_blank abi work₀ rhs
            (BinaryShiftMul.partialAcc lhs rhs rhs.size)
            (BinaryShiftMul.partialShift lhs rhs.size) hrhs
        · exact hinput.read_ne_start
        · exact fun i => (binaryShiftMulLoopWork_parked abi work₀ rhs.size
            (BinaryShiftMul.partialAcc lhs rhs rhs.size)
            (BinaryShiftMul.partialShift lhs rhs.size) hwork i).read_ne_start
        · exact houtput.read_ne_start }
  have hbodyBound : ∀ index, index < rhs.size →
      bodyTime index ≤ 33 * binaryShiftMulWidth lhs rhs + 162 := by
    intro index hi
    have hwidths := BinaryShiftMul.partial_widths_le_internal lhs rhs index
      (Nat.le_of_lt hi)
    exact (hbody index hi).1.trans
      (binaryShiftMulBodyTime_le (binaryShiftMulBitAt rhs index)
        (BinaryShiftMul.partialAcc lhs rhs index)
        (BinaryShiftMul.partialShift lhs index)
        (binaryShiftMulWidth lhs rhs) hwidths.1 hwidths.2)
  have hloop := spec.reachesIn (count := rhs.size) (value := 0) (by simp)
  have hloopTime := forBinaryWorkLoopTime_le bodyTime rhs.size
    (33 * binaryShiftMulWidth lhs rhs + 162) hbodyBound rhs.size 0 (by simp)
  have hinitialWork : binaryShiftMulPartialWork abi work₀ lhs rhs 0 = work₀ := by
    funext i
    by_cases hrhsIdx : i = abi.rhs
    · subst i
      rw [binaryShiftMulPartialWork, binaryShiftMulLoopWork_rhs]
      apply Tape.ext
      · simpa [binaryShiftMulCursorTape] using hrhs.2.1.symm
      · rfl
    by_cases haccIdx : i = abi.acc
    · subst i
      rw [binaryShiftMulPartialWork, binaryShiftMulLoopWork_acc]
      simpa [BinaryShiftMul.partialAcc] using! hacc.eq_init_move_right.symm
    by_cases hshiftIdx : i = abi.shift
    · subst i
      rw [binaryShiftMulPartialWork, binaryShiftMulLoopWork_shift]
      simpa [BinaryShiftMul.partialShift] using! hshift.eq_init_move_right.symm
    by_cases htmpIdx : i = abi.tmp
    · subst i
      rw [binaryShiftMulPartialWork, binaryShiftMulLoopWork_tmp]
      exact htmp.eq_init_move_right.symm
    by_cases hdblIdx : i = abi.dbl
    · subst i
      rw [binaryShiftMulPartialWork, binaryShiftMulLoopWork_dbl]
      exact hdbl.eq_init_move_right.symm
    exact binaryShiftMulLoopWork_other abi work₀ 0
      (BinaryShiftMul.partialAcc lhs rhs 0)
      (BinaryShiftMul.partialShift lhs 0) i hrhsIdx haccIdx hshiftIdx
      htmpIdx hdblIdx
  intro inp work out hpre
  rcases hpre with ⟨hinp, hworkEq, hout⟩
  subst inp
  subst work
  subst out
  let doneWork := binaryShiftMulPartialWork abi work₀ lhs rhs rhs.size
  let doneCfg := binaryShiftMulDoneCfg abi lhs rhs inp₀ work₀ out₀
  have hreach : (binaryShiftMulLoopTM abi).reachesIn
      (forBinaryWorkLoopTime bodyTime 0 rhs.size)
      { state := (binaryShiftMulLoopTM abi).qstart
        input := inp₀
        work := work₀
        output := out₀ } doneCfg := by
    simpa [binaryShiftMulLoopTM, spec, binaryShiftMulScanCfg,
      hinitialWork, doneCfg, body] using! hloop
  refine ⟨doneCfg, forBinaryWorkLoopTime bodyTime 0 rhs.size,
    (by simpa [binaryShiftMulLoopBound] using hloopTime), hreach, rfl, ?_⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · rw [show doneCfg.work = doneWork by rfl]
    dsimp only [doneWork]
    rw [binaryShiftMulPartialWork,
      binaryShiftMulLoopWork_other abi work₀ rhs.size
        (BinaryShiftMul.partialAcc lhs rhs rhs.size)
        (BinaryShiftMul.partialShift lhs rhs.size) abi.lhs
        abi.lhs_ne_rhs abi.lhs_ne_acc abi.lhs_ne_shift abi.lhs_ne_tmp
        abi.lhs_ne_dbl]
    exact hlhs
  · rw [show doneCfg.work = doneWork by rfl]
    dsimp only [doneWork]
    rw [binaryShiftMulPartialWork,
      binaryShiftMulLoopWork_rhs]
    simpa [binaryShiftMulCursorTape, Tape.HasBinaryContent] using
      hrhs.2.hasBinaryContent
  · rw [show doneCfg.work = doneWork by rfl]
    dsimp only [doneWork]
    rw [binaryShiftMulPartialWork,
      binaryShiftMulLoopWork_rhs]
    simpa [binaryShiftMulCursorTape] using hrhs.1
  · rw [show doneCfg.work = doneWork by rfl]
    dsimp only [doneWork]
    rw [binaryShiftMulPartialWork,
      binaryShiftMulLoopWork_rhs]
    simp [binaryShiftMulCursorTape]
  · rw [show doneCfg.work = doneWork by rfl]
    dsimp only [doneWork]
    rw [binaryShiftMulPartialWork,
      binaryShiftMulLoopWork_acc,
      BinaryShiftMul.partialAcc_full_internal]
    exact binaryShiftMulNatTape_hasBinaryNat (lhs * rhs)
  · rw [show doneCfg.work = doneWork by rfl]
    dsimp only [doneWork]
    rw [binaryShiftMulPartialWork,
      binaryShiftMulLoopWork_shift,
      BinaryShiftMul.partialShift_full_internal]
    exact binaryShiftMulNatTape_hasBinaryNat (lhs * 2 ^ rhs.size)
  · rw [show doneCfg.work = doneWork by rfl]
    dsimp only [doneWork]
    rw [binaryShiftMulPartialWork,
      binaryShiftMulLoopWork_tmp]
    exact binaryShiftMulNatTape_hasBinaryNat 0
  · rw [show doneCfg.work = doneWork by rfl]
    dsimp only [doneWork]
    rw [binaryShiftMulPartialWork,
      binaryShiftMulLoopWork_dbl]
    exact binaryShiftMulNatTape_hasBinaryNat 0
  · intro i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx hdblIdx
    rw [show doneCfg.work = doneWork by rfl]
    dsimp only [doneWork]
    rw [binaryShiftMulPartialWork,
      binaryShiftMulLoopWork_other abi work₀ rhs.size
        (BinaryShiftMul.partialAcc lhs rhs rhs.size)
        (BinaryShiftMul.partialShift lhs rhs.size) i hrhsIdx haccIdx
        hshiftIdx htmpIdx hdblIdx]

private def binaryShiftMulCleanupBits {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs : ℕ) (i : Fin n) : List Bool :=
  if i = abi.shift then (lhs * 2 ^ rhs.size).bits else []

private def binaryShiftMulCleanupHead {n : ℕ} (_abi : BinaryShiftMulABI n)
    (_i : Fin n) : ℕ :=
  1

private def binaryShiftMulCleanupTime {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs : ℕ) : ℕ :=
  rhs.size + 3 + 1 +
    resetBinaryWorkManyTime (binaryShiftMulCleanupBits abi lhs rhs)
      (binaryShiftMulCleanupHead abi) [abi.shift, abi.tmp, abi.dbl]

private def binaryShiftMulCleanupMid {n : ℕ} (abi : BinaryShiftMulABI n)
    (lhs rhs : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (out₀ : Tape) : TapePred n :=
  fun inp work out =>
    inp = inp₀ ∧
    (work abi.lhs).HasBinaryNat lhs ∧
    (work abi.rhs).HasBinaryNat rhs ∧
    (work abi.acc).HasBinaryNat (lhs * rhs) ∧
    (work abi.shift).HasBinaryNat (lhs * 2 ^ rhs.size) ∧
    (work abi.tmp).HasBinaryNat 0 ∧
    (work abi.dbl).HasBinaryNat 0 ∧
    (∀ i, i ≠ abi.lhs → i ≠ abi.rhs → i ≠ abi.acc →
      i ≠ abi.shift → i ≠ abi.tmp → i ≠ abi.dbl → work i = work₀ i) ∧
    out = out₀

/-- Postcondition for completed shift-and-add binary multiplication. -/
def binaryShiftMulPost {n : ℕ} (abi : BinaryShiftMulABI n)
    (lhs rhs : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (out₀ : Tape) : TapePred n :=
  fun inp work out =>
    inp = inp₀ ∧
    (work abi.lhs).HasBinaryNat lhs ∧
    (work abi.rhs).HasBinaryNat rhs ∧
    (work abi.acc).HasBinaryNat (lhs * rhs) ∧
    (work abi.shift).HasBinaryNat 0 ∧
    (work abi.tmp).HasBinaryNat 0 ∧
    (work abi.dbl).HasBinaryNat 0 ∧
    (∀ i, i ≠ abi.lhs → i ≠ abi.rhs → i ≠ abi.acc →
      i ≠ abi.shift → i ≠ abi.tmp → i ≠ abi.dbl → work i = work₀ i) ∧
    out = out₀

private theorem binaryShiftMulRewindTM_hoareTime_frame {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (rewindWorkTM abi.rhs).HoareTime
      (binaryShiftMulLoopPost abi lhs rhs inp₀ work₀ out₀)
      (binaryShiftMulCleanupMid abi lhs rhs inp₀ work₀ out₀)
      (rhs.size + 3) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hlhs, hrhsContent, hrhsStart, hrhsHead,
    hacc, hshift, htmp, hdbl, hframe, hout⟩
  have hworkParked : ∀ i, Parked (work i) := by
    intro i
    by_cases hlhsIdx : i = abi.lhs
    · subst i
      exact hasBinaryNat_parked hlhs
    by_cases hrhsIdx : i = abi.rhs
    · subst i
      exact ⟨by rw [hrhsHead]; omega, hrhsContent.cells_ne_start⟩
    by_cases haccIdx : i = abi.acc
    · subst i
      exact hasBinaryNat_parked hacc
    by_cases hshiftIdx : i = abi.shift
    · subst i
      exact hasBinaryNat_parked hshift
    by_cases htmpIdx : i = abi.tmp
    · subst i
      exact hasBinaryNat_parked htmp
    by_cases hdblIdx : i = abi.dbl
    · subst i
      exact hasBinaryNat_parked hdbl
    rw [hframe i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx hdblIdx]
    exact hwork i
  have hrewind := rewindBinaryWorkTM_hoareTime_frame abi.rhs rhs.bits
    (rhs.size + 1) inp work out hrhsContent hrhsStart
    ⟨by rw [hrhsHead]; omega, by rw [hrhsHead]⟩
    (hinp.symm ▸ hinput) (fun i _ => hworkParked i) (hout.symm ▸ houtput)
  obtain ⟨c', time, htime, hreach, hhalt, hfinalInput, hfinalRhs,
      hfinalOther, hfinalOutput⟩ :=
    hrewind inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨c', time, (by simpa using htime), hreach, hhalt, ?_⟩
  refine ⟨hfinalInput.trans hinp, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hfinalOutput.trans hout⟩
  · rw [hfinalOther abi.lhs abi.lhs_ne_rhs]
    exact hlhs
  · rw [hfinalRhs]
    exact Tape.init_move_right_hasBinaryNat rhs
  · rw [hfinalOther abi.acc (Ne.symm abi.rhs_ne_acc)]
    exact hacc
  · rw [hfinalOther abi.shift (Ne.symm abi.rhs_ne_shift)]
    exact hshift
  · rw [hfinalOther abi.tmp (Ne.symm abi.rhs_ne_tmp)]
    exact htmp
  · rw [hfinalOther abi.dbl (Ne.symm abi.rhs_ne_dbl)]
    exact hdbl
  · intro i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx hdblIdx
    exact (hfinalOther i hrhsIdx).trans
      (hframe i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx hdblIdx)

private theorem binaryShiftMulResetTM_hoareTime_frame {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (resetBinaryWorkManyTM [abi.shift, abi.tmp, abi.dbl]).HoareTime
      (binaryShiftMulCleanupMid abi lhs rhs inp₀ work₀ out₀)
      (binaryShiftMulPost abi lhs rhs inp₀ work₀ out₀)
      (resetBinaryWorkManyTime (binaryShiftMulCleanupBits abi lhs rhs)
        (binaryShiftMulCleanupHead abi) [abi.shift, abi.tmp, abi.dbl]) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hlhs, hrhs, hacc, hshift, htmp, hdbl,
    hframe, hout⟩
  have hworkParked : ∀ i, Parked (work i) := by
    intro i
    by_cases hlhsIdx : i = abi.lhs
    · subst i
      exact hasBinaryNat_parked hlhs
    by_cases hrhsIdx : i = abi.rhs
    · subst i
      exact hasBinaryNat_parked hrhs
    by_cases haccIdx : i = abi.acc
    · subst i
      exact hasBinaryNat_parked hacc
    by_cases hshiftIdx : i = abi.shift
    · subst i
      exact hasBinaryNat_parked hshift
    by_cases htmpIdx : i = abi.tmp
    · subst i
      exact hasBinaryNat_parked htmp
    by_cases hdblIdx : i = abi.dbl
    · subst i
      exact hasBinaryNat_parked hdbl
    rw [hframe i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx hdblIdx]
    exact hwork i
  have htargets : [abi.shift, abi.tmp, abi.dbl].Nodup := by
    simp
  have htarget : ∀ i, i ∈ [abi.shift, abi.tmp, abi.dbl] →
      (work i).HasBinaryContent (binaryShiftMulCleanupBits abi lhs rhs i) := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · simpa [binaryShiftMulCleanupBits] using hshift.2.hasBinaryContent
    · simpa [binaryShiftMulCleanupBits, Ne.symm abi.shift_ne_tmp] using
        htmp.2.hasBinaryContent
    · simpa [binaryShiftMulCleanupBits, Ne.symm abi.shift_ne_dbl] using
        hdbl.2.hasBinaryContent
  have htargetStart : ∀ i, i ∈ [abi.shift, abi.tmp, abi.dbl] →
      (work i).cells 0 = Γ.start := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact hshift.1
    · exact htmp.1
    · exact hdbl.1
  have htargetHead : ∀ i, i ∈ [abi.shift, abi.tmp, abi.dbl] →
      (work i).head ≤ binaryShiftMulCleanupHead abi i := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · simpa [binaryShiftMulCleanupHead] using hshift.2.1.le
    · simpa [binaryShiftMulCleanupHead] using htmp.2.1.le
    · simpa [binaryShiftMulCleanupHead] using hdbl.2.1.le
  have hreset := resetBinaryWorkManyTM_hoareTime_frame
    [abi.shift, abi.tmp, abi.dbl] (binaryShiftMulCleanupBits abi lhs rhs)
    (binaryShiftMulCleanupHead abi) inp work out htargets htarget
    htargetStart htargetHead (hinp.symm ▸ hinput) hworkParked
    (hout.symm ▸ houtput)
  obtain ⟨c', time, htime, hreach, hhalt, hfinalInput, hfinalWork,
      hfinalOutput⟩ := hreset inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨c', time, htime, hreach, hhalt, ?_⟩
  refine ⟨hfinalInput.trans hinp, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hfinalOutput.trans hout⟩
  · rw [hfinalWork, resetBinaryWorkManyResult_eq_of_not_mem]
    · exact hlhs
    · simp
  · rw [hfinalWork, resetBinaryWorkManyResult_eq_of_not_mem]
    · exact hrhs
    · simp
  · rw [hfinalWork, resetBinaryWorkManyResult_eq_of_not_mem]
    · exact hacc
    · simp
  · rw [hfinalWork,
      resetBinaryWorkManyResult_eq_blank_of_mem work _ abi.shift (by simp)]
    simpa [resetBinaryBlank] using Tape.init_move_right_hasBinaryNat 0
  · rw [hfinalWork,
      resetBinaryWorkManyResult_eq_blank_of_mem work _ abi.tmp (by simp)]
    simpa [resetBinaryBlank] using Tape.init_move_right_hasBinaryNat 0
  · rw [hfinalWork,
      resetBinaryWorkManyResult_eq_blank_of_mem work _ abi.dbl (by simp)]
    simpa [resetBinaryBlank] using Tape.init_move_right_hasBinaryNat 0
  · intro i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx hdblIdx
    rw [hfinalWork, resetBinaryWorkManyResult_eq_of_not_mem]
    · exact hframe i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx hdblIdx
    · simp [hshiftIdx, htmpIdx, hdblIdx]

private theorem binaryShiftMulCleanupTM_hoareTime_frame {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryShiftMulCleanupTM abi).HoareTime
      (binaryShiftMulLoopPost abi lhs rhs inp₀ work₀ out₀)
      (binaryShiftMulPost abi lhs rhs inp₀ work₀ out₀)
      (binaryShiftMulCleanupTime abi lhs rhs) := by
  have hrewind := binaryShiftMulRewindTM_hoareTime_frame abi lhs rhs
    inp₀ work₀ out₀ hinput hwork houtput
  have hreset := binaryShiftMulResetTM_hoareTime_frame abi lhs rhs
    inp₀ work₀ out₀ hinput hwork houtput
  have htransition : ∀ inp work out,
      binaryShiftMulCleanupMid abi lhs rhs inp₀ work₀ out₀ inp work out →
      binaryShiftMulCleanupMid abi lhs rhs inp₀ work₀ out₀
        (transitionInput inp) (fun i => transitionTape (work i))
          (transitionTape out) := by
    intro inp work out hmid
    rcases hmid with ⟨hinp, hlhs, hrhs, hacc, hshift, htmp, hdbl,
      hframe, hout⟩
    have hreads : ∀ i, (work i).read ≠ Γ.start := by
      intro i
      by_cases hlhsIdx : i = abi.lhs
      · subst i
        exact (hasBinaryNat_parked hlhs).read_ne_start
      by_cases hrhsIdx : i = abi.rhs
      · subst i
        exact (hasBinaryNat_parked hrhs).read_ne_start
      by_cases haccIdx : i = abi.acc
      · subst i
        exact (hasBinaryNat_parked hacc).read_ne_start
      by_cases hshiftIdx : i = abi.shift
      · subst i
        exact (hasBinaryNat_parked hshift).read_ne_start
      by_cases htmpIdx : i = abi.tmp
      · subst i
        exact (hasBinaryNat_parked htmp).read_ne_start
      by_cases hdblIdx : i = abi.dbl
      · subst i
        exact (hasBinaryNat_parked hdbl).read_ne_start
      rw [hframe i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx hdblIdx]
      exact (hwork i).read_ne_start
    obtain ⟨hi, hw, ho⟩ := phaseTransition_eq_self_of_reads_ne_start
      (hinp.symm ▸ hinput.read_ne_start) hreads
      (hout.symm ▸ houtput.read_ne_start)
    rw [hi, hw, ho]
    exact ⟨hinp, hlhs, hrhs, hacc, hshift, htmp, hdbl, hframe, hout⟩
  have hrun := seqTM_hoareTime (rewindWorkTM abi.rhs)
    (resetBinaryWorkManyTM [abi.shift, abi.tmp, abi.dbl])
    hrewind htransition hreset
  simpa [binaryShiftMulCleanupTM, binaryShiftMulCleanupTime] using hrun

private def binaryShiftMulInitPost {n : ℕ} (abi : BinaryShiftMulABI n)
    (lhs rhs : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (out₀ : Tape) : TapePred n :=
  fun inp work out =>
    inp = inp₀ ∧
    (work abi.lhs).HasBinaryNat lhs ∧
    (work abi.rhs).HasBinaryNat rhs ∧
    (work abi.acc).HasBinaryNat 0 ∧
    (work abi.shift).HasBinaryNat lhs ∧
    (work abi.tmp).HasBinaryNat 0 ∧
    (work abi.dbl).HasBinaryNat 0 ∧
    (∀ i, i ≠ abi.lhs → i ≠ abi.rhs → i ≠ abi.acc →
      i ≠ abi.shift → i ≠ abi.tmp → i ≠ abi.dbl → work i = work₀ i) ∧
    out = out₀

private theorem binaryShiftMulInitTM_hoareTime_frame {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ abi.lhs).HasBinaryNat lhs)
    (hrhs : (work₀ abi.rhs).HasBinaryNat rhs)
    (hacc : (work₀ abi.acc).HasBinaryNat 0)
    (hshift : (work₀ abi.shift).HasBinaryNat 0)
    (htmp : (work₀ abi.tmp).HasBinaryNat 0)
    (hdbl : (work₀ abi.dbl).HasBinaryNat 0)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryShiftMulInitTM abi).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (binaryShiftMulInitPost abi lhs rhs inp₀ work₀ out₀)
      (binaryCopyTime lhs 0) := by
  have hcopy := binaryCopyIntoTM_hoareTime_frame abi.lhs abi.shift abi.acc
    abi.lhs_ne_shift abi.lhs_ne_acc (Ne.symm abi.acc_ne_shift) lhs 0
    inp₀ work₀ out₀ hlhs hshift hacc hinput (fun i _ _ _ => hwork i)
    houtput
  unfold binaryShiftMulInitTM
  apply hcopy.strengthen_post
  intro inp work out hpost
  rcases hpost with ⟨hinp, hworkEq, hout⟩
  refine ⟨hinp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hout⟩
  · rw [hworkEq, Function.update_of_ne abi.lhs_ne_shift]
    exact hlhs
  · rw [hworkEq, Function.update_of_ne abi.rhs_ne_shift]
    exact hrhs
  · rw [hworkEq, Function.update_of_ne abi.acc_ne_shift]
    exact hacc
  · rw [hworkEq, Function.update_self]
    exact binaryShiftMulNatTape_hasBinaryNat lhs
  · rw [hworkEq, Function.update_of_ne (Ne.symm abi.shift_ne_tmp)]
    exact htmp
  · rw [hworkEq, Function.update_of_ne (Ne.symm abi.shift_ne_dbl)]
    exact hdbl
  · intro i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx hdblIdx
    rw [hworkEq, Function.update_of_ne hshiftIdx]

private theorem binaryShiftMulLoopTM_hoareTime_from_init {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryShiftMulLoopTM abi).HoareTime
      (binaryShiftMulInitPost abi lhs rhs inp₀ work₀ out₀)
      (binaryShiftMulLoopPost abi lhs rhs inp₀ work₀ out₀)
      (binaryShiftMulLoopBound lhs rhs) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hlhs, hrhs, hacc, hshift, htmp, hdbl,
    hframe, hout⟩
  have hworkParked : ∀ i, Parked (work i) := by
    intro i
    by_cases hlhsIdx : i = abi.lhs
    · subst i
      exact hasBinaryNat_parked hlhs
    by_cases hrhsIdx : i = abi.rhs
    · subst i
      exact hasBinaryNat_parked hrhs
    by_cases haccIdx : i = abi.acc
    · subst i
      exact hasBinaryNat_parked hacc
    by_cases hshiftIdx : i = abi.shift
    · subst i
      exact hasBinaryNat_parked hshift
    by_cases htmpIdx : i = abi.tmp
    · subst i
      exact hasBinaryNat_parked htmp
    by_cases hdblIdx : i = abi.dbl
    · subst i
      exact hasBinaryNat_parked hdbl
    rw [hframe i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx hdblIdx]
    exact hwork i
  have hloop := binaryShiftMulLoopTM_hoareTime_frame abi lhs rhs
    inp work out hlhs hrhs hacc hshift htmp hdbl (hinp.symm ▸ hinput)
    hworkParked (hout.symm ▸ houtput)
  obtain ⟨c', time, htime, hreach, hhalt, hfinalInput, hfinalLhs,
      hfinalRhsContent, hfinalRhsStart, hfinalRhsHead, hfinalAcc,
      hfinalShift, hfinalTmp, hfinalDbl, hfinalFrame, hfinalOutput⟩ :=
    hloop inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨c', time, htime, hreach, hhalt, ?_⟩
  refine ⟨hfinalInput.trans hinp, hfinalLhs, hfinalRhsContent,
    hfinalRhsStart, hfinalRhsHead, hfinalAcc, hfinalShift, hfinalTmp,
    hfinalDbl, ?_, hfinalOutput.trans hout⟩
  intro i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx hdblIdx
  exact (hfinalFrame i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx
    hdblIdx).trans
      (hframe i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx hdblIdx)

private theorem binaryShiftMulInitPost_transition {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    ∀ inp work out,
      binaryShiftMulInitPost abi lhs rhs inp₀ work₀ out₀ inp work out →
      binaryShiftMulInitPost abi lhs rhs inp₀ work₀ out₀
        (transitionInput inp) (fun i => transitionTape (work i))
          (transitionTape out) := by
  intro inp work out hpost
  rcases hpost with ⟨hinp, hlhs, hrhs, hacc, hshift, htmp, hdbl,
    hframe, hout⟩
  have hreads : ∀ i, (work i).read ≠ Γ.start := by
    intro i
    by_cases hlhsIdx : i = abi.lhs
    · subst i
      exact (hasBinaryNat_parked hlhs).read_ne_start
    by_cases hrhsIdx : i = abi.rhs
    · subst i
      exact (hasBinaryNat_parked hrhs).read_ne_start
    by_cases haccIdx : i = abi.acc
    · subst i
      exact (hasBinaryNat_parked hacc).read_ne_start
    by_cases hshiftIdx : i = abi.shift
    · subst i
      exact (hasBinaryNat_parked hshift).read_ne_start
    by_cases htmpIdx : i = abi.tmp
    · subst i
      exact (hasBinaryNat_parked htmp).read_ne_start
    by_cases hdblIdx : i = abi.dbl
    · subst i
      exact (hasBinaryNat_parked hdbl).read_ne_start
    rw [hframe i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx hdblIdx]
    exact (hwork i).read_ne_start
  obtain ⟨hi, hw, ho⟩ := phaseTransition_eq_self_of_reads_ne_start
    (hinp.symm ▸ hinput.read_ne_start) hreads
    (hout.symm ▸ houtput.read_ne_start)
  rw [hi, hw, ho]
  exact ⟨hinp, hlhs, hrhs, hacc, hshift, htmp, hdbl, hframe, hout⟩

private theorem binaryShiftMulLoopPost_transition {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    ∀ inp work out,
      binaryShiftMulLoopPost abi lhs rhs inp₀ work₀ out₀ inp work out →
      binaryShiftMulLoopPost abi lhs rhs inp₀ work₀ out₀
        (transitionInput inp) (fun i => transitionTape (work i))
          (transitionTape out) := by
  intro inp work out hpost
  rcases hpost with ⟨hinp, hlhs, hrhsContent, hrhsStart, hrhsHead,
    hacc, hshift, htmp, hdbl, hframe, hout⟩
  have hreads : ∀ i, (work i).read ≠ Γ.start := by
    intro i
    by_cases hlhsIdx : i = abi.lhs
    · subst i
      exact (hasBinaryNat_parked hlhs).read_ne_start
    by_cases hrhsIdx : i = abi.rhs
    · subst i
      exact hrhsContent.cells_ne_start _ (by rw [hrhsHead]; omega)
    by_cases haccIdx : i = abi.acc
    · subst i
      exact (hasBinaryNat_parked hacc).read_ne_start
    by_cases hshiftIdx : i = abi.shift
    · subst i
      exact (hasBinaryNat_parked hshift).read_ne_start
    by_cases htmpIdx : i = abi.tmp
    · subst i
      exact (hasBinaryNat_parked htmp).read_ne_start
    by_cases hdblIdx : i = abi.dbl
    · subst i
      exact (hasBinaryNat_parked hdbl).read_ne_start
    rw [hframe i hlhsIdx hrhsIdx haccIdx hshiftIdx htmpIdx hdblIdx]
    exact (hwork i).read_ne_start
  obtain ⟨hi, hw, ho⟩ := phaseTransition_eq_self_of_reads_ne_start
    (hinp.symm ▸ hinput.read_ne_start) hreads
    (hout.symm ▸ houtput.read_ne_start)
  rw [hi, hw, ho]
  exact ⟨hinp, hlhs, hrhsContent, hrhsStart, hrhsHead, hacc, hshift,
    htmp, hdbl, hframe, hout⟩

private theorem binaryShiftMulCleanupTime_le {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs : ℕ) :
    binaryShiftMulCleanupTime abi lhs rhs ≤
      3 * binaryShiftMulWidth lhs rhs + 35 := by
  have hshift := (BinaryShiftMul.partial_widths_le_internal lhs rhs
    rhs.size le_rfl).2
  have hshiftBits : (lhs * 2 ^ rhs.size).bits.length ≤
      binaryShiftMulWidth lhs rhs := by
    simpa [BinaryShiftMul.partialShift, Nat.size_eq_bits_len,
      binaryShiftMulWidth] using hshift
  have hrhs : rhs.size ≤ binaryShiftMulWidth lhs rhs := by
    simp [binaryShiftMulWidth]
  simp only [binaryShiftMulCleanupTime, resetBinaryWorkManyTime,
    binaryShiftMulCleanupBits, binaryShiftMulCleanupHead,
    resetBinaryWorkTime, clearWorkTimeBound, ite_eq_left]
  simp only [ite_eq_right (Ne.symm abi.shift_ne_tmp),
    ite_eq_right (Ne.symm abi.shift_ne_dbl), List.length_nil]
  omega

/-- The concrete shift-and-add multiplier preserves both operands, writes
their product to the accumulator, clears all three scratch tapes, and
preserves the complete external frame. -/
theorem binaryShiftMulTM_hoareTime_frame_internal {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ abi.lhs).HasBinaryNat lhs)
    (hrhs : (work₀ abi.rhs).HasBinaryNat rhs)
    (hacc : (work₀ abi.acc).HasBinaryNat 0)
    (hshift : (work₀ abi.shift).HasBinaryNat 0)
    (htmp : (work₀ abi.tmp).HasBinaryNat 0)
    (hdbl : (work₀ abi.dbl).HasBinaryNat 0)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryShiftMulTM abi).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (binaryShiftMulPost abi lhs rhs inp₀ work₀ out₀)
      (binaryShiftMulTime lhs rhs) := by
  have hinit := binaryShiftMulInitTM_hoareTime_frame abi lhs rhs
    inp₀ work₀ out₀ hlhs hrhs hacc hshift htmp hdbl hinput hwork houtput
  have hloop := binaryShiftMulLoopTM_hoareTime_from_init abi lhs rhs
    inp₀ work₀ out₀ hinput hwork houtput
  have hcleanup := binaryShiftMulCleanupTM_hoareTime_frame abi lhs rhs
    inp₀ work₀ out₀ hinput hwork houtput
  have htail := seqTM_hoareTime (binaryShiftMulLoopTM abi)
    (binaryShiftMulCleanupTM abi) hloop
    (binaryShiftMulLoopPost_transition abi lhs rhs inp₀ work₀ out₀
      hinput hwork houtput)
    hcleanup
  have hrun := seqTM_hoareTime (binaryShiftMulInitTM abi)
    (seqTM (binaryShiftMulLoopTM abi) (binaryShiftMulCleanupTM abi))
    hinit
    (binaryShiftMulInitPost_transition abi lhs rhs inp₀ work₀ out₀
      hinput hwork houtput)
    htail
  unfold binaryShiftMulTM
  apply hrun.mono_bound
  have hinitBound := binaryCopyTime_le lhs 0
  simp only [Nat.size_zero, Nat.mul_zero, Nat.add_zero] at hinitBound
  have hlhsWidth : lhs.size ≤ binaryShiftMulWidth lhs rhs := by
    simp [binaryShiftMulWidth]
  have hloopBound : binaryShiftMulLoopBound lhs rhs ≤
      33 * binaryShiftMulWidth lhs rhs ^ 2 +
        164 * binaryShiftMulWidth lhs rhs + 1 := by
    have hrhsWidth : rhs.size ≤ binaryShiftMulWidth lhs rhs := by
      simp [binaryShiftMulWidth]
    unfold binaryShiftMulLoopBound
    calc
      rhs.size * (33 * binaryShiftMulWidth lhs rhs + 164) + 1 ≤
          binaryShiftMulWidth lhs rhs *
              (33 * binaryShiftMulWidth lhs rhs + 164) + 1 := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_right _ hrhsWidth) 1
      _ = 33 * binaryShiftMulWidth lhs rhs ^ 2 +
          164 * binaryShiftMulWidth lhs rhs + 1 := by ring
  have hcleanupBound := binaryShiftMulCleanupTime_le abi lhs rhs
  simp only [binaryShiftMulTime]
  omega

/-- Coarse all-prefix auxiliary-space contract inherited from the concrete
quadratic time envelope. -/
theorem binaryShiftMulTM_hoareTimeSpace_frame_internal {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ abi.lhs).HasBinaryNat lhs)
    (hrhs : (work₀ abi.rhs).HasBinaryNat rhs)
    (hacc : (work₀ abi.acc).HasBinaryNat 0)
    (hshift : (work₀ abi.shift).HasBinaryNat 0)
    (htmp : (work₀ abi.tmp).HasBinaryNat 0)
    (hdbl : (work₀ abi.dbl).HasBinaryNat 0)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀)
    (hinitial :
      ({ state := (binaryShiftMulTM abi).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (binaryShiftMulTM abi).Q).WithinAuxSpace
          inputLength initialSpace) :
    (binaryShiftMulTM abi).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (binaryShiftMulPost abi lhs rhs inp₀ work₀ out₀)
      (binaryShiftMulTime lhs rhs) inputLength
      (initialSpace + binaryShiftMulTime lhs rhs) := by
  apply (binaryShiftMulTM_hoareTime_frame_internal abi lhs rhs inp₀ work₀
    out₀ hlhs hrhs hacc hshift htmp hdbl hinput hwork houtput).toHoareTimeSpace
  rintro inp work out ⟨hinp, hworkEq, hout⟩
  subst inp
  subst work
  subst out
  exact hinitial

end TM

end Complexity
