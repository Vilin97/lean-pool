/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Composition.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.CopyWorkOutput
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.RetargetCompute

/-!
# Sequential-composition tail pipeline

This module verifies the pipeline after the first function computation has
placed its raw output on the dedicated work tape. The pipeline rewinds that
tape, copies its delimited `HasOutput` value onto a fresh canonical tape,
rewinds the fresh tape, and runs the placed started-input wrapper for the
second machine. Its final output contract may describe either a computed string
or a decision verdict.

The phase-expanded bound is
`(B + 2) + 1 + (|y| + 1) + 1 + (|y| + 1 + 2) + 1 + G(|y|)`,
which simplifies to `B + 2 * |y| + 9 + G(|y|)`.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- A start-invariant tape at a positive head does not read `▷`. -/
private theorem read_ne_start_of_startInvariant {t : Tape}
    (hinv : Tape.StartInvariant t) (hhead : 1 ≤ t.head) :
    t.read ≠ Γ.start := by
  show t.cells t.head ≠ Γ.start
  exact hinv.2 t.head hhead

/-- A start-invariant tape at a positive head is unchanged by a `seqTM`
boundary. -/
private theorem transitionTape_eq_of_startInvariant {t : Tape}
    (hinv : Tape.StartInvariant t) (hhead : 1 ≤ t.head) :
    transitionTape t = t :=
  transitionTape_eq_self (read_ne_start_of_startInvariant hinv hhead)

/-- Boundary contract consumed only by the proof-internal composition tail. -/
def CompositionTailPre (nf ng : ℕ) (y : List Bool) (B : ℕ)
    (inp : Tape) (work : Fin (compositionTapeCount nf ng) → Tape)
    (out : Tape) : Prop :=
  (work (compositionRawOutputIdx nf ng)).HasOutput y ∧
  Tape.StartInvariant (work (compositionRawOutputIdx nf ng)) ∧
  (work (compositionRawOutputIdx nf ng)).head ≤ B ∧
  work (compositionVirtualInputIdx nf ng) = (Tape.init []).move Dir3.right ∧
  (∀ j : Fin ng, work (compositionSecondWorkIdx nf ng j) =
    (Tape.init []).move Dir3.right) ∧
  out = (Tape.init []).move Dir3.right ∧
  Tape.StartInvariant inp ∧ 1 ≤ inp.head ∧
  (∀ i : Fin nf, Tape.StartInvariant (work (compositionPrefixIdx nf ng i)) ∧
    1 ≤ (work (compositionPrefixIdx nf ng i)).head)

/-- Generic post-first-computation tail driven by a virtual-input run contract.

The prefix tapes are arbitrary stable frame tapes. The raw tape may initially
have any head up to `B`, and cells after its first output delimiter may contain
arbitrary junk. The virtual-input tape, second-machine scratch block, and real
output begin in their canonical parked blank shapes. -/
private theorem compositionTailTM_hoareTime_of_virtualRun_internal
    {nf ng : ℕ} (tmG : TM ng) {G : ℕ → ℕ}
    (y : List Bool) (B : ℕ) (P : Tape → Prop)
    (hG : ∀ realInput : Tape,
      ∃ (c' : Cfg (ng + 1) tmG.Q) (t : ℕ),
        t ≤ G y.length ∧
        (retargetInputStarted tmG).reachesIn t
          (retargetInputStartedCfg tmG y realInput) c' ∧
        (retargetInputStarted tmG).halted c' ∧ P c'.output) :
    (compositionTailTM nf ng tmG).HoareTime
      (CompositionTailPre nf ng y B)
      (fun _inp _work out => P out)
      ((B + 2) + 1 + ((y.length + 1) + 1 +
        ((y.length + 1 + 2) + 1 + G y.length))) := by
  intro inp work out hpre
  rcases hpre with
    ⟨hrawOutput, hrawInv, hrawBound, hvinBlank, hgBlank, houtBlank,
      hinv, hinputHead, hprefix⟩
  let raw := compositionRawOutputIdx nf ng
  let vin := compositionVirtualInputIdx nf ng
  change (work raw).HasOutput y at hrawOutput
  change Tape.StartInvariant (work raw) at hrawInv
  change (work raw).head ≤ B at hrawBound
  change work vin = (Tape.init []).move Dir3.right at hvinBlank
  have hrawVin : raw ≠ vin := compositionRawOutputIdx_ne_virtualInputIdx nf ng
  have houtInv : Tape.StartInvariant out := by
    rw [houtBlank]
    exact Tape.StartInvariant.init_nil.move Dir3.right
  have houtHead : 1 ≤ out.head := by rw [houtBlank]; simp [Tape.move]
  have hvinInv : Tape.StartInvariant (work vin) := by
    rw [hvinBlank]
    exact Tape.StartInvariant.init_nil.move Dir3.right
  have hvinHead : 1 ≤ (work vin).head := by
    rw [hvinBlank]
    simp [Tape.move]
  have hotherStable : ∀ i, i ≠ raw →
      Tape.StartInvariant (work i) ∧ 1 ≤ (work i).head := by
    intro i hiRaw
    by_cases hiPrefix : i.val < nf
    · let j : Fin nf := ⟨i.val, hiPrefix⟩
      have hidx : compositionPrefixIdx nf ng j = i := by
        apply Fin.ext
        rfl
      rw [← hidx]
      exact hprefix j
    by_cases hiVin : i = vin
    · subst i
      exact ⟨hvinInv, hvinHead⟩
    · have hiLower : nf + 1 ≤ i.val := by
        have hneVal : i.val ≠ nf := by
          intro heq
          apply hiRaw
          apply Fin.ext
          simpa [raw] using heq
        omega
      have hiUpper : i.val < nf + 1 + ng := by
        have hlt := i.isLt
        have hneVinVal : i.val ≠ nf + 1 + ng := by
          intro heq
          apply hiVin
          apply Fin.ext
          simpa [vin] using heq
        simp only [compositionTapeCount] at hlt
        omega
      let j : Fin ng := ⟨i.val - (nf + 1), by omega⟩
      have hidx : compositionSecondWorkIdx nf ng j = i := by
        apply Fin.ext
        simp [compositionSecondWorkIdx, placeWorkIdx, j]
        omega
      rw [← hidx, hgBlank j]
      exact ⟨Tape.StartInvariant.init_nil.move Dir3.right, by simp [Tape.move]⟩
  let FrameRaw : TapePred (compositionTapeCount nf ng) :=
    fun inp' work' out' =>
      (work' raw).cells = (work raw).cells ∧
      inp' = inp ∧ out' = out ∧ ∀ i, i ≠ raw → work' i = work i
  have hrewRaw := rewindWorkTM_hoareTime_frame raw B
    (P := FrameRaw) (by
      intro inp₀ work₀ out₀ inp' work' out' hframe hcells _hhead hother hinp'
        houtCells houtHead'
      rcases hframe with ⟨hrawCells₀, hinp₀, hout₀, hwork₀⟩
      have hout' : out' = out₀ := Tape.ext houtHead' houtCells
      exact ⟨hcells.trans hrawCells₀, hinp'.trans hinp₀,
        hout'.trans hout₀, fun i hi => (hother i hi).trans (hwork₀ i hi)⟩)
  have hrewPre :
      (work raw).cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → (work raw).cells j ≠ Γ.start) ∧
      (work raw).head ≤ B ∧ inp.read ≠ Γ.start ∧
      out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
      (∀ i, i ≠ raw → (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
      FrameRaw inp work out := by
    refine ⟨hrawInv.1, hrawInv.2, hrawBound,
      read_ne_start_of_startInvariant hinv hinputHead,
      read_ne_start_of_startInvariant houtInv houtHead, houtHead, ?_, ?_⟩
    · intro i hi
      exact ⟨read_ne_start_of_startInvariant (hotherStable i hi).1
        (hotherStable i hi).2, (hotherStable i hi).2⟩
    · exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  obtain ⟨c₁, t₁, ht₁, hreach₁, hhalt₁, hc₁Head, hc₁Frame⟩ :=
    hrewRaw inp work out hrewPre
  rcases hc₁Frame with ⟨hc₁RawCells, hc₁Input, hc₁Output, hc₁Other⟩
  let source : Tape := { head := 1, cells := (work raw).cells }
  have hc₁Raw : c₁.work raw = source := Tape.ext hc₁Head hc₁RawCells
  have hsourceInv : Tape.StartInvariant source := by
    exact ⟨by simpa [source] using hrawInv.1,
      by intro j hj; simpa [source] using hrawInv.2 j hj⟩
  have hsourceOutput : source.HasOutput y := by
    exact (Tape.hasOutput_congr (by rfl) y).mpr hrawOutput
  have hc₁WorkStable : ∀ i, Tape.StartInvariant (c₁.work i) ∧
      1 ≤ (c₁.work i).head := by
    intro i
    by_cases hi : i = raw
    · subst i
      rw [hc₁Raw]
      exact ⟨hsourceInv, by simp [source]⟩
    · rw [hc₁Other i hi]
      exact hotherStable i hi
  have hc₁InputTr : transitionInput c₁.input = c₁.input := by
    rw [hc₁Input]
    exact transitionInput_eq_self (read_ne_start_of_startInvariant hinv hinputHead)
  have hc₁OutputTr : transitionTape c₁.output = c₁.output := by
    rw [hc₁Output]
    exact transitionTape_eq_of_startInvariant houtInv houtHead
  have hc₁WorkTr : ∀ i, transitionTape (c₁.work i) = c₁.work i := by
    intro i
    exact transitionTape_eq_of_startInvariant (hc₁WorkStable i).1
      (hc₁WorkStable i).2
  let FrameCopy : TapePred (compositionTapeCount nf ng) :=
    fun inp' work' out' =>
      inp' = inp ∧ out' = out ∧
      ∀ i, i ≠ raw → i ≠ vin → work' i = work i
  have hcopy := copyWorkToWorkTM_hoareTime_frame_of_hasOutput raw vin hrawVin y source
    (P := FrameCopy) (by
      intro inp₀ work₀ out₀ inp' work' out' hframe _hsrcCells _hsrcHead
        _hsrcOutput _hdstPrefix _hdst0 hinp' hout' hother
      rcases hframe with ⟨hinp₀, hout₀, hwork₀⟩
      exact ⟨hinp'.trans hinp₀, hout'.trans hout₀,
        fun i hiRaw hiVin => (hother i hiRaw hiVin).trans (hwork₀ i hiRaw hiVin)⟩)
  have hcopyPre :
      (fun i => transitionTape (c₁.work i)) raw = source ∧
      source.head = 1 ∧ source.HasOutput y ∧
      (fun i => transitionTape (c₁.work i)) vin =
        (Tape.init []).move Dir3.right ∧
      (transitionInput c₁.input).read ≠ Γ.start ∧
      (transitionTape c₁.output).read ≠ Γ.start ∧
      1 ≤ (transitionTape c₁.output).head ∧
      (∀ i, i ≠ raw → i ≠ vin →
        ((fun i => transitionTape (c₁.work i)) i).read ≠ Γ.start ∧
        1 ≤ ((fun i => transitionTape (c₁.work i)) i).head) ∧
      FrameCopy (transitionInput c₁.input)
        (fun i => transitionTape (c₁.work i)) (transitionTape c₁.output) := by
    refine ⟨?_, rfl, hsourceOutput, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change transitionTape (c₁.work raw) = source
      rw [hc₁WorkTr raw, hc₁Raw]
    · change transitionTape (c₁.work vin) = (Tape.init []).move Dir3.right
      rw [hc₁WorkTr vin, hc₁Other vin hrawVin.symm, hvinBlank]
    · rw [hc₁InputTr, hc₁Input]
      exact read_ne_start_of_startInvariant hinv hinputHead
    · rw [hc₁OutputTr, hc₁Output]
      exact read_ne_start_of_startInvariant houtInv houtHead
    · rw [hc₁OutputTr, hc₁Output]
      exact houtHead
    · intro i hiRaw hiVin
      change (transitionTape (c₁.work i)).read ≠ Γ.start ∧
        1 ≤ (transitionTape (c₁.work i)).head
      rw [hc₁WorkTr i, hc₁Other i hiRaw]
      exact ⟨read_ne_start_of_startInvariant (hotherStable i hiRaw).1
        (hotherStable i hiRaw).2, (hotherStable i hiRaw).2⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hc₁InputTr, hc₁Input]
      · rw [hc₁OutputTr, hc₁Output]
      · intro i hiRaw hiVin
        change transitionTape (c₁.work i) = work i
        rw [hc₁WorkTr i, hc₁Other i hiRaw]
  obtain ⟨c₂, t₂, ht₂, hreach₂, hhalt₂, hc₂RawCells,
    hc₂RawHead, hc₂RawOutput, hc₂VinPrefix, hc₂Vin0, hc₂Frame⟩ :=
    hcopy (transitionInput c₁.input) (fun i => transitionTape (c₁.work i))
      (transitionTape c₁.output) hcopyPre
  rcases hc₂Frame with ⟨hc₂Input, hc₂Output, hc₂Other⟩
  have hc₂VinCells : (c₂.work vin).cells =
      (Tape.init (y.map Γ.ofBool)).cells :=
    hc₂VinPrefix.cells_eq_init hc₂Vin0
  have hc₂RawInv : Tape.StartInvariant (c₂.work raw) := by
    refine ⟨?_, ?_⟩
    · rw [hc₂RawCells]
      exact hsourceInv.1
    · intro j hj
      rw [hc₂RawCells]
      exact hsourceInv.2 j hj
  have hc₂VinInv : Tape.StartInvariant (c₂.work vin) := by
    refine ⟨?_, ?_⟩
    · rw [hc₂VinCells]
      rfl
    · intro j hj
      rw [hc₂VinCells]
      exact Tape.init_ofBool_cells_ne_start y j hj
  have hc₂WorkStable : ∀ i, Tape.StartInvariant (c₂.work i) ∧
      1 ≤ (c₂.work i).head := by
    intro i
    by_cases hiRaw : i = raw
    · subst i
      exact ⟨hc₂RawInv, by omega⟩
    by_cases hiVin : i = vin
    · subst i
      refine ⟨hc₂VinInv, ?_⟩
      rw [hc₂VinPrefix.1]
      omega
    · rw [hc₂Other i hiRaw hiVin]
      exact hotherStable i hiRaw
  have hc₂InputTr : transitionInput c₂.input = c₂.input := by
    rw [hc₂Input]
    exact transitionInput_eq_self (read_ne_start_of_startInvariant hinv hinputHead)
  have hc₂OutputTr : transitionTape c₂.output = c₂.output := by
    rw [hc₂Output]
    exact transitionTape_eq_of_startInvariant houtInv houtHead
  have hc₂WorkTr : ∀ i, transitionTape (c₂.work i) = c₂.work i := by
    intro i
    exact transitionTape_eq_of_startInvariant (hc₂WorkStable i).1
      (hc₂WorkStable i).2
  let FrameVin : TapePred (compositionTapeCount nf ng) :=
    fun inp' work' out' =>
      (work' vin).cells = (Tape.init (y.map Γ.ofBool)).cells ∧
      inp' = inp ∧ out' = out ∧ ∀ i, i ≠ vin → work' i = c₂.work i
  have hrewVin := rewindWorkTM_hoareTime_frame vin (y.length + 1)
    (P := FrameVin) (by
      intro inp₀ work₀ out₀ inp' work' out' hframe hcells _hhead hother hinp'
        houtCells houtHead'
      rcases hframe with ⟨hvinCells₀, hinp₀, hout₀, hwork₀⟩
      have hout' : out' = out₀ := Tape.ext houtHead' houtCells
      exact ⟨hcells.trans hvinCells₀, hinp'.trans hinp₀,
        hout'.trans hout₀, fun i hi => (hother i hi).trans (hwork₀ i hi)⟩)
  have hrewVinPre :
      ((fun i => transitionTape (c₂.work i)) vin).cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → ((fun i => transitionTape (c₂.work i)) vin).cells j ≠
        Γ.start) ∧
      ((fun i => transitionTape (c₂.work i)) vin).head ≤ y.length + 1 ∧
      (transitionInput c₂.input).read ≠ Γ.start ∧
      (transitionTape c₂.output).read ≠ Γ.start ∧
      (transitionTape c₂.output).head ≥ 1 ∧
      (∀ i, i ≠ vin →
        ((fun i => transitionTape (c₂.work i)) i).read ≠ Γ.start ∧
        ((fun i => transitionTape (c₂.work i)) i).head ≥ 1) ∧
      FrameVin (transitionInput c₂.input)
        (fun i => transitionTape (c₂.work i)) (transitionTape c₂.output) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change (transitionTape (c₂.work vin)).cells 0 = Γ.start
      rw [hc₂WorkTr vin]
      exact hc₂VinInv.1
    · intro j hj
      change (transitionTape (c₂.work vin)).cells j ≠ Γ.start
      rw [hc₂WorkTr vin]
      exact hc₂VinInv.2 j hj
    · change (transitionTape (c₂.work vin)).head ≤ y.length + 1
      rw [hc₂WorkTr vin, hc₂VinPrefix.1]
    · rw [hc₂InputTr, hc₂Input]
      exact read_ne_start_of_startInvariant hinv hinputHead
    · rw [hc₂OutputTr, hc₂Output]
      exact read_ne_start_of_startInvariant houtInv houtHead
    · rw [hc₂OutputTr, hc₂Output]
      exact houtHead
    · intro i hi
      change (transitionTape (c₂.work i)).read ≠ Γ.start ∧
        (transitionTape (c₂.work i)).head ≥ 1
      rw [hc₂WorkTr i]
      exact ⟨read_ne_start_of_startInvariant (hc₂WorkStable i).1
        (hc₂WorkStable i).2, (hc₂WorkStable i).2⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · change (transitionTape (c₂.work vin)).cells =
          (Tape.init (y.map Γ.ofBool)).cells
        rw [hc₂WorkTr vin]
        exact hc₂VinCells
      · rw [hc₂InputTr, hc₂Input]
      · rw [hc₂OutputTr, hc₂Output]
      · intro i hi
        change transitionTape (c₂.work i) = c₂.work i
        rw [hc₂WorkTr i]
  obtain ⟨c₃, t₃, ht₃, hreach₃, hhalt₃, hc₃VinHead, hc₃Frame⟩ :=
    hrewVin (transitionInput c₂.input) (fun i => transitionTape (c₂.work i))
      (transitionTape c₂.output) hrewVinPre
  rcases hc₃Frame with ⟨hc₃VinCells, hc₃Input, hc₃Output, hc₃Other⟩
  have hc₃Vin : c₃.work vin =
      (Tape.init (y.map Γ.ofBool)).move Dir3.right := by
    exact Tape.ext hc₃VinHead hc₃VinCells
  have hc₃WorkStable : ∀ i, Tape.StartInvariant (c₃.work i) ∧
      1 ≤ (c₃.work i).head := by
    intro i
    by_cases hi : i = vin
    · subst i
      rw [hc₃Vin]
      exact ⟨Tape.StartInvariant.init_ofBool y |>.move Dir3.right, by simp [Tape.move]⟩
    · rw [hc₃Other i hi]
      exact hc₂WorkStable i
  have hc₃InputTr : transitionInput c₃.input = c₃.input := by
    rw [hc₃Input]
    exact transitionInput_eq_self (read_ne_start_of_startInvariant hinv hinputHead)
  have hc₃OutputTr : transitionTape c₃.output = c₃.output := by
    rw [hc₃Output]
    exact transitionTape_eq_of_startInvariant houtInv houtHead
  have hc₃WorkTr : ∀ i, transitionTape (c₃.work i) = c₃.work i := by
    intro i
    exact transitionTape_eq_of_startInvariant (hc₃WorkStable i).1
      (hc₃WorkStable i).2
  let secondPre := 0 + (nf + 1)
  let extras : Fin (secondPre + (ng + 1) + 0) → Tape :=
    fun i => transitionTape (c₃.work i)
  let realInput := transitionInput c₃.input
  have hextrasInv : ∀ i, ¬placeWorkInMiddle secondPre (ng + 1) i →
      Tape.StartInvariant (extras i) := by
    intro i _hi
    rw [show extras i = c₃.work i from hc₃WorkTr i]
    exact (hc₃WorkStable i).1
  have hextrasHead : ∀ i, ¬placeWorkInMiddle secondPre (ng + 1) i →
      1 ≤ (extras i).head := by
    intro i _hi
    rw [show extras i = c₃.work i from hc₃WorkTr i]
    exact (hc₃WorkStable i).2
  obtain ⟨c₄, t₄, ht₄, hreachSource₄, hhaltSource₄, hout₄⟩ := hG realInput
  let C₄ := placeWorkCfg (retargetInputStarted tmG) secondPre 0 extras c₄
  have hreach₄ :
      (placeWorkTM secondPre 0 (retargetInputStarted tmG)).reachesIn t₄
        (placeWorkCfg (retargetInputStarted tmG) secondPre 0 extras
          (retargetInputStartedCfg tmG y realInput)) C₄ := by
    apply placeWorkTM_reachesIn_placeWorkCfg_stable_internal
      (retargetInputStarted tmG) secondPre 0 extras hreachSource₄
    intro i hi
    show (extras i).cells (extras i).head ≠ Γ.start
    exact (hextrasInv i hi).2 (extras i).head (hextrasHead i hi)
  have hhalt₄ :
      (placeWorkTM secondPre 0 (retargetInputStarted tmG)).halted C₄ := by
    show c₄.state = (retargetInputStarted tmG).qhalt
    exact hhaltSource₄
  let gEntry : Cfg (compositionTapeCount nf ng) (compositionSecondTM nf tmG).Q :=
    { state := (compositionSecondTM nf tmG).qstart
      input := transitionInput c₃.input
      work := fun i => transitionTape (c₃.work i)
      output := transitionTape c₃.output }
  have hEntry :
      placeWorkCfg (retargetInputStarted tmG) secondPre 0 extras
          (retargetInputStartedCfg tmG y realInput) = gEntry := by
    refine Cfg.ext rfl rfl ?_ ?_
    · funext i
      by_cases hmid : placeWorkInMiddle secondPre (ng + 1) i
      · let j := placeWorkCoord secondPre (ng + 1) i hmid
        have hphys : placeWorkIdx secondPre 0 j = i :=
          placeWorkIdx_placeWorkCoord i hmid
        by_cases hj : j.val < ng
        · let jG : Fin ng := ⟨j.val, hj⟩
          have hjcast : Fin.castSucc jG = j := by
            apply Fin.ext
            rfl
          have hiVal : i.val = secondPre + j.val := by
            have hv := congrArg Fin.val hphys
            simp only [placeWorkIdx_val] at hv
            omega
          have hiRaw : i ≠ raw := by
            change i ≠ compositionRawOutputIdx nf ng
            intro heq
            have hv := congrArg Fin.val heq
            simp only [compositionRawOutputIdx_val] at hv
            dsimp only [secondPre] at hiVal
            omega
          have hiVin : i ≠ vin := by
            change i ≠ compositionVirtualInputIdx nf ng
            intro heq
            have hv := congrArg Fin.val heq
            simp only [compositionVirtualInputIdx_val] at hv
            dsimp only [secondPre] at hiVal
            omega
          have hblank : c₃.work i = (Tape.init []).move Dir3.right := by
            calc
              c₃.work i = c₂.work i := hc₃Other i hiVin
              _ = work i := hc₂Other i hiRaw hiVin
              _ = (Tape.init []).move Dir3.right := by
                rw [← hphys, ← hjcast]
                exact hgBlank jG
          change
            (placeWorkCfg (retargetInputStarted tmG) secondPre 0 extras
              (retargetInputStartedCfg tmG y realInput)).work i =
              transitionTape (c₃.work i)
          calc
            _ = (retargetInputStartedCfg tmG y realInput).work j := by
              rw [← hphys, placeWorkCfg_work_middle]
            _ = (Tape.init []).move Dir3.right := by
              exact retargetInputStartedCfg_work_lt tmG y realInput j hj
            _ = transitionTape (c₃.work i) := by
              rw [hc₃WorkTr i, hblank]
        · have hjval : j.val = ng := by
            have := j.isLt
            omega
          have hjlast : j = Fin.last ng := by
            apply Fin.ext
            simpa using hjval
          have hiVin : i = vin := by
            rw [← hphys, hjlast]
            exact (compositionVirtualInputIdx_eq_secondPlacedLast nf ng).symm
          change
            (placeWorkCfg (retargetInputStarted tmG) secondPre 0 extras
              (retargetInputStartedCfg tmG y realInput)).work i =
              transitionTape (c₃.work i)
          calc
            _ = (retargetInputStartedCfg tmG y realInput).work j := by
              rw [← hphys, placeWorkCfg_work_middle]
            _ = (Tape.init (y.map Γ.ofBool)).move Dir3.right := by
              rw [hjlast]
              simp [Fin.last]
            _ = transitionTape (c₃.work i) := by
              rw [hiVin, hc₃WorkTr vin, hc₃Vin]
      · change
          (placeWorkCfg (retargetInputStarted tmG) secondPre 0 extras
            (retargetInputStartedCfg tmG y realInput)).work i =
            transitionTape (c₃.work i)
        rw [placeWorkCfg_work_extra _ _ _ _ _ i hmid]
    · change (retargetInputStartedCfg tmG y realInput).output =
          transitionTape c₃.output
      rw [retargetInputStartedCfg_output, hc₃OutputTr, hc₃Output, houtBlank]
  have hreach₄' : (compositionSecondTM nf tmG).reachesIn t₄ gEntry C₄ := by
    change (placeWorkTM secondPre 0 (retargetInputStarted tmG)).reachesIn t₄ gEntry C₄
    rw [← hEntry]
    exact hreach₄
  let tm₃ := rewindWorkTM vin
  let tm₂ := copyWorkToWorkTM raw vin
  let tm₁ := rewindWorkTM raw
  let c₃₄ := phase2Wrap tm₃ (compositionSecondTM nf tmG) C₄
  have hreach₃₄ : (seqTM tm₃ (compositionSecondTM nf tmG)).reachesIn
      (t₃ + 1 + t₄)
      (phase1Wrap tm₃ (compositionSecondTM nf tmG)
        { state := tm₃.qstart, input := transitionInput c₂.input,
          work := fun i => transitionTape (c₂.work i),
          output := transitionTape c₂.output }) c₃₄ := by
    exact seqTM_reachesIn_of_reachesIn tm₃ (compositionSecondTM nf tmG)
      hreach₃ hhalt₃ hreach₄'
  let tm₃₄ := seqTM tm₃ (compositionSecondTM nf tmG)
  let c₂₃₄ := phase2Wrap tm₂ tm₃₄ c₃₄
  have hreach₂₃₄ : (seqTM tm₂ tm₃₄).reachesIn
      (t₂ + 1 + (t₃ + 1 + t₄))
      (phase1Wrap tm₂ tm₃₄
        { state := tm₂.qstart, input := transitionInput c₁.input,
          work := fun i => transitionTape (c₁.work i),
          output := transitionTape c₁.output }) c₂₃₄ := by
    exact seqTM_reachesIn_of_reachesIn tm₂ tm₃₄ hreach₂ hhalt₂ hreach₃₄
  let tm₂₃₄ := seqTM tm₂ tm₃₄
  let cFinal := phase2Wrap tm₁ tm₂₃₄ c₂₃₄
  have hreachFinal : (compositionTailTM nf ng tmG).reachesIn
      (t₁ + 1 + (t₂ + 1 + (t₃ + 1 + t₄)))
      { state := (compositionTailTM nf ng tmG).qstart,
        input := inp, work := work, output := out } cFinal := by
    change (seqTM tm₁ tm₂₃₄).reachesIn _ _ _
    exact seqTM_reachesIn_of_reachesIn tm₁ tm₂₃₄
      hreach₁ hhalt₁ hreach₂₃₄
  refine ⟨cFinal, t₁ + 1 + (t₂ + 1 + (t₃ + 1 + t₄)), ?_,
    hreachFinal, ?_, ?_⟩
  · omega
  · change (seqTM tm₁ tm₂₃₄).halted cFinal
    rw [phase2Wrap_halted_iff, phase2Wrap_halted_iff, phase2Wrap_halted_iff]
    exact hhalt₄
  · show P C₄.output
    exact hout₄

/-- The post-first-computation tail correctly runs the second function. -/
theorem compositionTailTM_hoareTime_internal {nf ng : ℕ} (tmG : TM ng)
    {g : List Bool → List Bool} {G : ℕ → ℕ}
    (hG : tmG.ComputesInTime g G) (y : List Bool) (B : ℕ) :
    (compositionTailTM nf ng tmG).HoareTime
      (CompositionTailPre nf ng y B)
      (fun _inp _work out => out.HasOutput (g y))
      ((B + 2) + 1 + ((y.length + 1) + 1 +
        ((y.length + 1 + 2) + 1 + G y.length))) := by
  apply compositionTailTM_hoareTime_of_virtualRun_internal tmG y B
    (fun out => out.HasOutput (g y))
  intro realInput
  exact retargetInputStarted_computesVirtual tmG hG y realInput

/-- The same tail pipeline retains a second machine's decision verdict. -/
theorem compositionTailTM_decides_hoareTime_internal {nf ng : ℕ} (tmG : TM ng)
    {L : Language} {G : ℕ → ℕ}
    (hG : tmG.DecidesInTime L G) (y : List Bool) (B : ℕ) :
    (compositionTailTM nf ng tmG).HoareTime
      (CompositionTailPre nf ng y B)
      (fun _inp _work out =>
        (y ∈ L → out.cells 1 = Γ.one) ∧
        (y ∉ L → out.cells 1 = Γ.zero))
      ((B + 2) + 1 + ((y.length + 1) + 1 +
        ((y.length + 1 + 2) + 1 + G y.length))) := by
  apply compositionTailTM_hoareTime_of_virtualRun_internal tmG y B
    (fun out =>
      (y ∈ L → out.cells 1 = Γ.one) ∧
      (y ∉ L → out.cells 1 = Γ.zero))
  intro realInput
  exact retargetInputStarted_decidesVirtual tmG hG y realInput

end TM

end Complexity
