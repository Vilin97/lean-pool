/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.Generated.GenusFourRow095FaceData
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow095Positive
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConfigurations
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ConnectedCheckFast
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedFaceDispatch
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreVertexCutGenusFour
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionCoreSupport

/-!
# A readable closed-face proof for cubic genus-four row 095

The positive face is the symbolic signed-window proof transcribed from the
Atanasov--Ranganathan argument.  The twenty-four proper nonloopy forest faces
are dispatched by their exact zero sets:

* rows 031, 032, 034, and 068 use contractions of the readable closed row-097
  proof;
* rows 029 and 069 use checked `(2,2)` vertex cuts;
* rows 002, 009, and 010 use the core-cardinality criterion.

The repetitive contraction witnesses are isolated as passive checked data in
`LowGenus.Generated.GenusFourRow095FaceData`.
-/

@[expose] public section
namespace AtanasovRanganathan.GenusFourRow095Closed

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ClosedFaceCensus
open Utilities.Certificate.ClosedFaceDispatch
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.CoreVertexCut
open Utilities.Certificate.CoreVertexCut.Data
open Utilities.Certificate.ReorientContraction
open Utilities.Subdivision.SubdivisionCoreSupport
open AtanasovRanganathan.Configurations
open AtanasovRanganathan.Generated.GenusFourRow095FaceData
open AtanasovRanganathan.GenusFourCubicAtlas

/-! ## The exact 25-face ledger -/

/-- The 25 explicitly enumerated zero-slot sets that are nonloopy forests in row 095, including
the empty face and all valid lower-dimensional contractions. -/
def validFaces : List (Finset (Fin 9)) :=
  [∅,
    {0}, {3}, {5}, {8}, {4},
    {0, 4}, {3, 4}, {4, 5}, {4, 8},
    {0, 8}, {3, 5}, {0, 3}, {5, 8}, {0, 5}, {3, 8},
    {0, 3, 4}, {3, 4, 5}, {0, 4, 8}, {4, 5, 8},
    {0, 3, 5}, {0, 3, 8}, {0, 5, 8}, {3, 5, 8},
    {0, 3, 5, 8}]
/-- Kernel enumeration: these are exactly all nonloopy forest zero sets of
row 095.  The theorem is used only to turn the semantic face hypotheses into
the displayed readable disjunction. -/
theorem validFaces_complete (F : Finset (Fin 9))
    (hForest : IsForest LowGenus.GenusFourRow095.core F)
    (hNotLoopy : ¬ IsLoopy LowGenus.GenusFourRow095.core F) :
    F ∈ validFaces := by
  revert F
  decide +kernel

/-! ## The nine quotient types -/

private theorem core002_connected : core002.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast
    (core := core002) (by decide)
private theorem core009_connected : core009.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast
    (core := core009) (by decide)
private theorem core010_connected : core010.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast
    (core := core010) (by decide)
private theorem core029_connected : core029.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast
    (core := core029) (by decide)
private theorem core069_connected : core069.Connected :=
  ExplicitPotential.Core.connected_of_connectedCheckFast
    (core := core069) (by decide)

/-- The vertex cut of contraction core 029 at glue vertex 3, with left vertex set `{0, 3}`; both
pieces have genus two. -/
def cut029 : CoreVertexCut.Data core029 where
  glue := 3
  left := {0, 3}

/-- The vertex cut of contraction core 069 at glue vertex 3, with left vertex set `{0, 3, 4}`;
both pieces have genus two. -/
def cut069 : CoreVertexCut.Data core069 where
  glue := 3
  left := {0, 3, 4}

private theorem cut029_leftGenus : cut029.leftGenus = 2 := by decide
private theorem cut029_rightGenus : cut029.rightGenus = 2 := by decide
private theorem cut069_leftGenus : cut069.leftGenus = 2 := by decide
private theorem cut069_rightGenus : cut069.rightGenus = 2 := by decide

theorem bnExists029 (s : SubdivisionGraph.Spec 4 7) (hCore : s.core = core029) :
    BNExists s.graph 1 3 := by
  rcases s with ⟨sCore, length, hn, hLoopless, hPositive⟩
  dsimp only at hCore ⊢
  subst sCore
  exact cut029.bnExists_one_three_of_genusFourRankOneConditions
    ⟨core029, length, hn, hLoopless, hPositive⟩
    ⟨cut029.check_eq_true_iff.mp (by decide), core029_connected,
      Or.inl ⟨cut029_leftGenus, cut029_rightGenus⟩⟩

theorem bnExists069 (s : SubdivisionGraph.Spec 5 8) (hCore : s.core = core069) :
    BNExists s.graph 1 3 := by
  rcases s with ⟨sCore, length, hn, hLoopless, hPositive⟩
  dsimp only at hCore ⊢
  subst sCore
  exact cut069.bnExists_one_three_of_genusFourRankOneConditions
    ⟨core069, length, hn, hLoopless, hPositive⟩
    ⟨cut069.check_eq_true_iff.mp (by decide), core069_connected,
      Or.inl ⟨cut069_leftGenus, cut069_rightGenus⟩⟩

theorem bnExists002 (s : SubdivisionGraph.Spec 2 5) (hCore : s.core = core002) :
    BNExists s.graph 1 3 := by
  apply bnExists_of_coreVertexCount_le_degree_of_coreConnected s 3
  · rw [hCore]
    exact core002_connected
  · norm_num

theorem bnExists009 (s : SubdivisionGraph.Spec 3 6) (hCore : s.core = core009) :
    BNExists s.graph 1 3 := by
  apply bnExists_of_coreVertexCount_le_degree_of_coreConnected s 3
  · rw [hCore]
    exact core009_connected
  · norm_num

theorem bnExists010 (s : SubdivisionGraph.Spec 3 6) (hCore : s.core = core010) :
    BNExists s.graph 1 3 := by
  apply bnExists_of_coreVertexCount_le_degree_of_coreConnected s 3
  · rw [hCore]
    exact core010_connected
  · norm_num

/-! ## Generic one-line use of a ledger entry -/

private theorem dispatch {n' p' : ℕ}
    {targetCore : ExplicitPotential.Core n' p'}
    (rev : Fin p' → Bool)
    (data : ClosedContraction.ContractionData LowGenus.GenusFourRow095.core
      (ReorientContraction.Core.reorient targetCore rev))
    (length : Fin 9 → ℕ)
    (hForest : IsForest LowGenus.GenusFourRow095.core (zeroSet length))
    (hNotLoopy : ¬ IsLoopy LowGenus.GenusFourRow095.core (zeroSet length))
    (hZero : zeroSet length = data.F) (hn' : 0 < n')
    (hTarget : ∀ s : SubdivisionGraph.Spec n' p', s.core = targetCore →
      BNExists s.graph 1 3) :
    BNExists (censusSpec LowGenus.GenusFourRow095.core (by norm_num)
      length hForest hNotLoopy).graph 1 3 :=
  bnExists_censusSpec_of_exact_contraction data (by norm_num) hn' length
    hForest hNotLoopy hZero 3
    (fun s hCore => bnExists_spec_of_reoriented_core rev 3 hTarget s hCore)

/-! ## The closed theorem -/

/-- Every subdivision and every equal-genus proper face of public cubic row
095 carries a degree-three rank-one divisor.  Its conclusion exactly matches
the row-095 obligation in `GenusFourCubicCoverage.RowClosedCoverage`. -/
theorem row095_closed
    (length : Fin 9 → ℕ)
    (hForest : IsForest row095.core (zeroSlots length))
    (hNotLoopy : ¬ IsLoopy row095.core (zeroSlots length)) :
    BNExists (faceSpec row095.core (by norm_num) length hForest hNotLoopy).graph 1 3 := by
  change BNExists (censusSpec LowGenus.GenusFourRow095.core (by norm_num)
    length hForest hNotLoopy).graph 1 3
  have hFace := validFaces_complete (zeroSet length) hForest hNotLoopy
  simp only [validFaces, List.mem_cons] at hFace
  rcases hFace with hEmpty | h0 | h3 | h5 | h8 | h4 |
      h04 | h34 | h45 | h48 | h08 | h35 | h03 | h58 | h05 | h38 |
      h034 | h345 | h048 | h458 | h035 | h038 | h058 | h358 | h0358
  · have hPos : ∀ edge : Fin 9, 0 < length edge := by
      intro edge
      have hNe : length edge ≠ 0 := by
        intro hZero
        have : edge ∈ zeroSet length := (mem_zeroSet length edge).2 hZero
        rw [hEmpty] at this
        simp at this
      omega
    let d := censusSpec LowGenus.GenusFourRow095.core (by norm_num)
      length hForest hNotLoopy
    have hPositive : BNExists (LowGenus.GenusFourRow095.Spec length hPos).graph 1 3 :=
      LowGenus.GenusFourRow095.bnExists_one_three length hPos
    have hToSpec : d.toSpec hPos = LowGenus.GenusFourRow095.Spec length hPos := rfl
    rw [← hToSpec] at hPositive
    exact (d.bnExists_toSpec_iff hPos 1 3).mp hPositive
  · exact dispatch rev0 data0 length hForest hNotLoopy (by simpa [data0] using h0)
      (by norm_num) LowGenus.GenusFourRow097Contractions.bnExists068
  · exact dispatch rev3 data3 length hForest hNotLoopy (by simpa [data3] using h3)
      (by norm_num) LowGenus.GenusFourRow097Contractions.bnExists068
  · exact dispatch rev5 data5 length hForest hNotLoopy (by simpa [data5] using h5)
      (by norm_num) LowGenus.GenusFourRow097Contractions.bnExists068
  · exact dispatch rev8 data8 length hForest hNotLoopy (by simpa [data8] using h8)
      (by norm_num) LowGenus.GenusFourRow097Contractions.bnExists068
  · exact dispatch rev4 data4 length hForest hNotLoopy (by simpa [data4] using h4)
      (by norm_num) bnExists069
  · exact dispatch rev04 data04 length hForest hNotLoopy (by simpa [data04] using h04)
      (by norm_num) bnExists029
  · exact dispatch rev34 data34 length hForest hNotLoopy (by simpa [data34] using h34)
      (by norm_num) bnExists029
  · exact dispatch rev45 data45 length hForest hNotLoopy (by simpa [data45] using h45)
      (by norm_num) bnExists029
  · exact dispatch rev48 data48 length hForest hNotLoopy (by simpa [data48] using h48)
      (by norm_num) bnExists029
  · exact dispatch rev08 data08 length hForest hNotLoopy (by simpa [data08] using h08)
      (by norm_num) LowGenus.GenusFourRow097Contractions.bnExists031
  · exact dispatch rev35 data35 length hForest hNotLoopy (by simpa [data35] using h35)
      (by norm_num) LowGenus.GenusFourRow097Contractions.bnExists031
  · exact dispatch rev03 data03 length hForest hNotLoopy (by simpa [data03] using h03)
      (by norm_num) LowGenus.GenusFourRow097Contractions.bnExists032
  · exact dispatch rev58 data58 length hForest hNotLoopy (by simpa [data58] using h58)
      (by norm_num) LowGenus.GenusFourRow097Contractions.bnExists032
  · exact dispatch rev05 data05 length hForest hNotLoopy (by simpa [data05] using h05)
      (by norm_num) LowGenus.GenusFourRow097Contractions.bnExists034
  · exact dispatch rev38 data38 length hForest hNotLoopy (by simpa [data38] using h38)
      (by norm_num) LowGenus.GenusFourRow097Contractions.bnExists034
  · exact dispatch rev034 data034 length hForest hNotLoopy
      (by simpa [data034] using h034) (by norm_num) bnExists009
  · exact dispatch rev345 data345 length hForest hNotLoopy
      (by simpa [data345] using h345) (by norm_num) bnExists009
  · exact dispatch rev048 data048 length hForest hNotLoopy
      (by simpa [data048] using h048) (by norm_num) bnExists009
  · exact dispatch rev458 data458 length hForest hNotLoopy
      (by simpa [data458] using h458) (by norm_num) bnExists009
  · exact dispatch rev035 data035 length hForest hNotLoopy
      (by simpa [data035] using h035) (by norm_num) bnExists010
  · exact dispatch rev038 data038 length hForest hNotLoopy
      (by simpa [data038] using h038) (by norm_num) bnExists010
  · exact dispatch rev058 data058 length hForest hNotLoopy
      (by simpa [data058] using h058) (by norm_num) bnExists010
  · exact dispatch rev358 data358 length hForest hNotLoopy
      (by simpa [data358] using h358) (by norm_num) bnExists010
  · exact dispatch rev0358 data0358 length hForest hNotLoopy
      (by simpa [data0358] using h0358) (by norm_num) bnExists002

end AtanasovRanganathan.GenusFourRow095Closed
