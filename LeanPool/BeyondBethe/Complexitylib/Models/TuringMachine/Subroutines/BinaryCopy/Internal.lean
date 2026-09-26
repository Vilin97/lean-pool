/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ClearWork

/-!
# Copying canonical binary naturals -- proof internals

The copy machine first clears its destination and then invokes width-linear
ripple addition with the source and zero counter as preserved operands. These
proofs compose the public literal-frame and all-prefix contracts of both
phases, then recover the original literal copy frame from canonicality.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Canonical parked tape encoding of a natural for binary copying. -/
def binaryCopyNatTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

private theorem binaryCopyNatTape_hasBinaryNat (value : ℕ) :
    (binaryCopyNatTape value).HasBinaryNat value :=
  Tape.init_move_right_hasBinaryNat value

private theorem binaryCopyHasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : Parked t := by
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem binaryCopyNatTape_parked (value : ℕ) :
    Parked (binaryCopyNatTape value) :=
  binaryCopyHasBinaryNat_parked (binaryCopyNatTape_hasBinaryNat value)

private theorem binaryCopyInitialWork_parked
    (srcIdx dstIdx counterIdx : Fin n) (srcValue dstValue : ℕ)
    (work₀ : Fin n → Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i)) :
    ∀ i, Parked (work₀ i) := by
  intro i
  by_cases hsrcIdx : i = srcIdx
  · subst i
    exact binaryCopyHasBinaryNat_parked hsrc
  by_cases hdstIdx : i = dstIdx
  · subst i
    exact binaryCopyHasBinaryNat_parked hdst
  by_cases hcounterIdx : i = counterIdx
  · subst i
    exact binaryCopyHasBinaryNat_parked hcounter
  exact hother i hsrcIdx hdstIdx hcounterIdx

private def binaryCopyMidWork (work₀ : Fin n → Tape) (dstIdx : Fin n) :
    Fin n → Tape :=
  Function.update work₀ dstIdx (binaryCopyNatTape 0)

private theorem binaryCopyMidWork_parked
    (work₀ : Fin n → Tape) (dstIdx : Fin n)
    (hwork : ∀ i, Parked (work₀ i)) :
    ∀ i, Parked (binaryCopyMidWork work₀ dstIdx i) := by
  intro i
  by_cases hi : i = dstIdx
  · subst i
    simp only [binaryCopyMidWork, Function.update_self]
    exact binaryCopyNatTape_parked 0
  · rw [binaryCopyMidWork, Function.update_of_ne hi]
    exact hwork i

private theorem binaryCopyFrame_transition
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀) :
    ∀ inp work out,
      (inp = inp₀ ∧ work = work₀ ∧ out = out₀) →
      transitionInput inp = inp₀ ∧
        (fun i => transitionTape (work i)) = work₀ ∧
        transitionTape out = out₀ := by
  rintro _ _ _ ⟨rfl, rfl, rfl⟩
  refine ⟨hinp.transitionInput_eq_self, ?_, hout.transitionTape_eq_self⟩
  funext i
  exact (hwork i).transitionTape_eq_self

private theorem binaryCopyDistinct
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx) :
    BinaryRippleAddDistinct srcIdx counterIdx dstIdx :=
  ⟨hsrcCounter, hsrcDst, hdstCounter.symm⟩

private theorem binaryCopyRipplePost_eq
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue : ℕ) (work₀ work : Fin n → Tape)
    (hsrc₀ : (work₀ srcIdx).HasBinaryNat srcValue)
    (hcounter₀ : (work₀ counterIdx).HasBinaryNat 0)
    (hsrc : (work srcIdx).HasBinaryNat srcValue)
    (hcounter : (work counterIdx).HasBinaryNat 0)
    (hdst : (work dstIdx).HasBinaryNat srcValue)
    (hother : ∀ i, i ≠ srcIdx → i ≠ counterIdx → i ≠ dstIdx →
      work i = binaryCopyMidWork work₀ dstIdx i) :
    work = Function.update work₀ dstIdx (binaryCopyNatTape srcValue) := by
  funext i
  by_cases hdstIdx : i = dstIdx
  · subst i
    rw [Function.update_self]
    simpa [binaryCopyNatTape] using hdst.eq_init_move_right
  by_cases hsrcIdx : i = srcIdx
  · subst i
    rw [Function.update_of_ne hsrcDst]
    exact hsrc.eq_init_move_right.trans hsrc₀.eq_init_move_right.symm
  by_cases hcounterIdx : i = counterIdx
  · subst i
    rw [Function.update_of_ne hdstCounter.symm]
    exact hcounter.eq_init_move_right.trans hcounter₀.eq_init_move_right.symm
  rw [Function.update_of_ne hdstIdx]
  simpa [binaryCopyMidWork, hdstIdx] using
    hother i hsrcIdx hcounterIdx hdstIdx

theorem binaryCopyTime_le_internal (srcValue dstValue : ℕ) :
    binaryCopyTime srcValue dstValue ≤
      3 * srcValue.size + 2 * dstValue.size + 20 := by
  have hadd := binaryRippleAddTime_le srcValue 0
  have hadd' : binaryRippleAddTime srcValue 0 ≤
      3 * srcValue.size + 14 := by
    simpa using hadd
  simp only [binaryCopyTime, clearWorkTimeBound]
  omega

theorem binaryCopyIntoTM_hoareTime_frame_internal
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryCopyIntoTM srcIdx dstIdx counterIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ dstIdx (binaryCopyNatTape srcValue) ∧
        out = out₀)
      (binaryCopyTime srcValue dstValue) := by
  let midWork := binaryCopyMidWork work₀ dstIdx
  have hwork := binaryCopyInitialWork_parked srcIdx dstIdx counterIdx
    srcValue dstValue work₀ hsrc hdst hcounter hother
  have hmidWork : ∀ i, Parked (midWork i) := by
    exact binaryCopyMidWork_parked work₀ dstIdx hwork
  have hclear := clearWorkTM_hoareTime_frame dstIdx dstValue.bits
    inp₀ work₀ out₀ hdst.eq_init_move_right hinp
    (fun i _ => hwork i) hout
  have hclear' : (clearWorkTM dstIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = midWork ∧ out = out₀)
      (clearWorkTimeBound dstValue.size) := by
    simpa [midWork, binaryCopyMidWork, binaryCopyNatTape,
      Nat.size_eq_bits_len] using hclear
  have hmidSrc : (midWork srcIdx).HasBinaryNat srcValue := by
    simpa [midWork, binaryCopyMidWork, hsrcDst] using hsrc
  have hmidDst : (midWork dstIdx).HasBinaryNat 0 := by
    simpa [midWork, binaryCopyMidWork] using
      binaryCopyNatTape_hasBinaryNat 0
  have hmidCounter : (midWork counterIdx).HasBinaryNat 0 := by
    simpa [midWork, binaryCopyMidWork, hdstCounter.symm] using hcounter
  have hdistinct := binaryCopyDistinct srcIdx dstIdx counterIdx
    hsrcDst hsrcCounter hdstCounter
  have hadd := binaryRippleAddTM_hoareTime_frame
    srcIdx counterIdx dstIdx hdistinct srcValue 0 inp₀ midWork out₀
    hmidSrc hmidCounter hmidDst hinp
    (fun i _ _ _ => hmidWork i) hout
  have hseq := seqTM_hoareTime (clearWorkTM dstIdx)
    (binaryRippleAddTM srcIdx counterIdx dstIdx) hclear'
    (binaryCopyFrame_transition inp₀ midWork out₀ hinp hmidWork hout)
    hadd
  apply hseq.consequence (b' := binaryCopyTime srcValue dstValue)
  · intro _inp _work _out hpre
    exact hpre
  · rintro inp work out ⟨hinput, hfinalSrc, hfinalCounter, hfinalDst,
      hfinalOther, houtput⟩
    exact ⟨hinput, binaryCopyRipplePost_eq srcIdx dstIdx counterIdx
      hsrcDst hdstCounter srcValue work₀ work hsrc hcounter
      hfinalSrc hfinalCounter (by simpa using hfinalDst) (by
        intro i hiSrc hiCounter hiDst
        exact hfinalOther i hiSrc hiCounter hiDst), houtput⟩
  · simp [binaryCopyTime]

theorem binaryCopyIntoTM_hoareTimeSpace_frame_internal
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryCopyIntoTM srcIdx dstIdx counterIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ dstIdx (binaryCopyNatTape srcValue) ∧
        out = out₀)
      (binaryCopyTime srcValue dstValue) inputLength
      (binaryCopySpace initialSpace srcValue dstValue) := by
  let midWork := binaryCopyMidWork work₀ dstIdx
  have hwork := binaryCopyInitialWork_parked srcIdx dstIdx counterIdx
    srcValue dstValue work₀ hsrc hdst hcounter hother
  have hmidWork : ∀ i, Parked (midWork i) := by
    exact binaryCopyMidWork_parked work₀ dstIdx hwork
  have hinitial :
      ({ state := (clearWorkTM dstIdx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (clearWorkTM dstIdx).Q).WithinAuxSpace
          inputLength initialSpace :=
    ⟨hworkSpace, hinputSpace⟩
  have hclear := clearWorkTM_hoareTimeSpace_frame dstIdx dstValue.bits
    inputLength initialSpace inp₀ work₀ out₀
    hdst.eq_init_move_right hinp (fun i _ => hwork i) hout hinitial
  have hclear' : (clearWorkTM dstIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = midWork ∧ out = out₀)
      (clearWorkTimeBound dstValue.size) inputLength
      (initialSpace + clearWorkTimeBound dstValue.size) := by
    simpa [midWork, binaryCopyMidWork, binaryCopyNatTape,
      Nat.size_eq_bits_len] using hclear
  have hmidSrc : (midWork srcIdx).HasBinaryNat srcValue := by
    simpa [midWork, binaryCopyMidWork, hsrcDst] using hsrc
  have hmidDst : (midWork dstIdx).HasBinaryNat 0 := by
    simpa [midWork, binaryCopyMidWork] using
      binaryCopyNatTape_hasBinaryNat 0
  have hmidCounter : (midWork counterIdx).HasBinaryNat 0 := by
    simpa [midWork, binaryCopyMidWork, hdstCounter.symm] using hcounter
  have hone : 1 ≤ initialSpace := by
    have h := hworkSpace srcIdx
    rw [hsrc.2.1] at h
    exact h
  have hmidWorkSpace : ∀ i, (midWork i).head ≤ initialSpace := by
    intro i
    by_cases hi : i = dstIdx
    · subst i
      simpa [midWork, binaryCopyMidWork, binaryCopyNatTape, Tape.move]
        using hone
    · simpa [midWork, binaryCopyMidWork, hi] using hworkSpace i
  have hdistinct := binaryCopyDistinct srcIdx dstIdx counterIdx
    hsrcDst hsrcCounter hdstCounter
  have haddInitial :
      ({ state := (binaryRippleAddTM srcIdx counterIdx dstIdx).qstart
         input := inp₀
         work := midWork
         output := out₀ } :
        Cfg n (binaryRippleAddTM srcIdx counterIdx dstIdx).Q).WithinAuxSpace
          inputLength initialSpace :=
    ⟨hmidWorkSpace, hinputSpace⟩
  have hadd := binaryRippleAddTM_hoareTimeSpace_frame
    srcIdx counterIdx dstIdx hdistinct srcValue 0 inputLength initialSpace
    inp₀ midWork out₀ hmidSrc hmidCounter hmidDst hinp
    (fun i _ _ _ => hmidWork i) hout haddInitial
  have hseq := seqTM_hoareTimeSpace (clearWorkTM dstIdx)
    (binaryRippleAddTM srcIdx counterIdx dstIdx) hclear'
    (binaryCopyFrame_transition inp₀ midWork out₀ hinp hmidWork hout)
    hadd
  apply hseq.consequence
    (time' := binaryCopyTime srcValue dstValue)
    (inputLength' := inputLength)
    (space' := binaryCopySpace initialSpace srcValue dstValue)
  · intro _inp _work _out hpre
    exact hpre
  · rintro inp work out ⟨hfinalInput, hfinalSrc, hfinalCounter,
      hfinalDst, hfinalOther, hfinalOutput⟩
    exact ⟨hfinalInput, binaryCopyRipplePost_eq srcIdx dstIdx counterIdx
      hsrcDst hdstCounter srcValue work₀ work hsrc hcounter
      hfinalSrc hfinalCounter (by simpa using hfinalDst) (by
        intro i hiSrc hiCounter hiDst
        exact hfinalOther i hiSrc hiCounter hiDst), hfinalOutput⟩
  · simp [binaryCopyTime]
  · exact le_rfl
  · simp [binaryCopySpace]

theorem binaryCopyIntoTM_isTransducer_internal
    (srcIdx dstIdx counterIdx : Fin n) :
    (binaryCopyIntoTM srcIdx dstIdx counterIdx).IsTransducer := by
  exact (clearWorkTM_isTransducer dstIdx).seqTM
    (binaryRippleAddTM_isTransducer srcIdx counterIdx dstIdx)

end TM

end Complexity
