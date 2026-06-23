/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Hilbert.K
import LeanPool.Incompleteness.Foundation.Modal.Entailment.Grz

/-! # WellKnown -/


namespace LO
namespace Modal

open Entailment

namespace Hilbert

section «lp_section_1»

open Deduction

variable {H : Hilbert α}
variable [DecidableEq α]


/-- Imported declaration from the Incompleteness formalization. -/
class HasT (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_T : Axioms.T (.atom p) ∈ H.axioms := by tauto;

instance [hT : H.HasT] : Entailment.HasAxiomT H where
  T φ :=
    maxm ⟨Axioms.T (.atom hT.p), hT.mem_T, (fun b => if hT.p = b then φ else (.atom b)), by simp⟩

/-- Imported declaration from the Incompleteness formalization. -/
class HasB (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_B : Axioms.B (.atom p) ∈ H.axioms := by tauto;

instance [hB : H.HasB] : Entailment.HasAxiomB H where
  B φ :=
    maxm ⟨Axioms.B (.atom hB.p), hB.mem_B, (fun b => if hB.p = b then φ else (.atom b)), by simp⟩

/-- Imported declaration from the Incompleteness formalization. -/
class HasD (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_D : Axioms.D (.atom p) ∈ H.axioms := by tauto;

instance [hD : H.HasD] : Entailment.HasAxiomD H where
  D φ :=
    maxm ⟨Axioms.D (.atom hD.p), hD.mem_D, (fun b => if hD.p = b then φ else (.atom b)), by simp⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasFour (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_Four : Axioms.Four (.atom p) ∈ H.axioms := by tauto;

instance [hFour : H.HasFour] : Entailment.HasAxiomFour H where
  Four φ :=
    maxm ⟨Axioms.Four (.atom hFour.p), hFour.mem_Four,
      (fun b => if hFour.p = b then φ else (.atom b)), by simp⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasFive (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_Five : Axioms.Five (.atom p) ∈ H.axioms := by tauto;

instance [hFive : H.HasFive] : Entailment.HasAxiomFive H where
  Five φ :=
    maxm ⟨Axioms.Five (.atom hFive.p), hFive.mem_Five,
      (fun b => if hFive.p = b then φ else (.atom b)), by simp⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasDot2 (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_Dot2 : Axioms.Dot2 (.atom p) ∈ H.axioms := by tauto;

instance [hDot2 : H.HasDot2] : Entailment.HasAxiomDot2 H where
  Dot2 φ :=
    maxm ⟨Axioms.Dot2 (.atom hDot2.p), hDot2.mem_Dot2,
      (fun b => if hDot2.p = b then φ else (.atom b)), by simp⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasDot3 (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  /-- Imported declaration from the Incompleteness formalization. -/
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_Dot3 : Axioms.Dot3 (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [hDot3 : H.HasDot3] : Entailment.HasAxiomDot3 H where
  Dot3 φ ψ :=
    maxm ⟨Axioms.Dot3 (.atom hDot3.p) (.atom hDot3.q), hDot3.mem_Dot3,
      (fun b => if hDot3.p = b then φ else if hDot3.q = b then ψ else (.atom b)),
      by simp [hDot3.ne_pq]⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasL (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_L : Axioms.L (.atom p) ∈ H.axioms := by tauto;

instance [hL : H.HasL] : Entailment.HasAxiomL H where
  L φ :=
    maxm ⟨Axioms.L (.atom hL.p), hL.mem_L, (fun b => if hL.p = b then φ else (.atom b)), by simp⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasGrz (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_Grz : Axioms.Grz (.atom p) ∈ H.axioms := by tauto;

instance [hGrz : H.HasGrz] : Entailment.HasAxiomGrz H where
  Grz φ :=
    maxm ⟨Axioms.Grz (.atom hGrz.p), hGrz.mem_Grz,
      (fun b => if hGrz.p = b then φ else (.atom b)), by simp⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasTc (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_Tc : Axioms.Tc (.atom p) ∈ H.axioms := by tauto;

instance [hTc : H.HasTc] : Entailment.HasAxiomTc H where
  Tc φ :=
    maxm ⟨Axioms.Tc (.atom hTc.p), hTc.mem_Tc,
      (fun b => if hTc.p = b then φ else (.atom b)), by simp⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasVer (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_Ver : Axioms.Ver (.atom p) ∈ H.axioms := by tauto;

instance [hVer : H.HasVer] : Entailment.HasAxiomVer H where
  Ver φ :=
    maxm ⟨Axioms.Ver (.atom hVer.p), hVer.mem_Ver,
      (fun b => if hVer.p = b then φ else (.atom b)), by simp⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasH (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_H : Axioms.H (.atom p) ∈ H.axioms := by tauto;

instance [hH : H.HasH] : Entailment.HasAxiomH H where
  H φ :=
    maxm ⟨Axioms.H (.atom hH.p), hH.mem_H, (fun b => if hH.p = b then φ else (.atom b)), by simp⟩

end «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KT : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0)}⟩
instance : (Hilbert.KT).HasK where p := 0; q := 1;
instance : (Hilbert.KT).HasT where p := 0
instance : Entailment.KT (Hilbert.KT) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0)}⟩
instance : (Hilbert.KD).HasK where p := 0; q := 1;
instance : (Hilbert.KD).HasD where p := 0
instance : Entailment.KD (Hilbert.KD) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KB : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0)}⟩
instance : (Hilbert.KB).HasK where p := 0; q := 1;
instance : (Hilbert.KB).HasB where p := 0
instance : Entailment.KB (Hilbert.KB) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KDB : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.B (.atom 0)}⟩
instance : (Hilbert.KDB).HasK where p := 0; q := 1;
instance : (Hilbert.KDB).HasD where p := 0
instance : (Hilbert.KDB).HasB where p := 0
instance : Entailment.KDB (Hilbert.KDB) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KTB : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.B (.atom 0)}⟩
instance : (Hilbert.KTB).HasK where p := 0; q := 1;
instance : (Hilbert.KTB).HasT where p := 0
instance : (Hilbert.KTB).HasB where p := 0
instance : Entailment.KTB (Hilbert.KTB) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩
instance : (Hilbert.K4).HasK where p := 0; q := 1;
instance : (Hilbert.K4).HasFour where p := 0
instance : Entailment.K4 (Hilbert.K4) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KT4B : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.B (.atom 0)}⟩
instance : (Hilbert.KT4B).HasK where p := 0; q := 1;
instance : (Hilbert.KT4B).HasT where p := 0
instance : (Hilbert.KT4B).HasFour where p := 0


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K45 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Five (.atom 0)}⟩
instance : (Hilbert.K45).HasK where p := 0; q := 1;
instance : (Hilbert.K45).HasFour where p := 0
instance : (Hilbert.K45).HasFive where p := 0
instance : Entailment.K45 (Hilbert.K45) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD4 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0)}⟩
instance : (Hilbert.KD4).HasK where p := 0; q := 1;
instance : (Hilbert.KD4).HasD where p := 0
instance : (Hilbert.KD4).HasFour where p := 0
instance : Entailment.KD4 (Hilbert.KD4) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD5 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Five (.atom 0)}⟩
instance : (Hilbert.KD5).HasK where p := 0; q := 1;
instance : (Hilbert.KD5).HasD where p := 0
instance : (Hilbert.KD5).HasFive where p := 0
instance : Entailment.KD5 (Hilbert.KD5) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD45 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0), Axioms.Five (.atom 0)}⟩
instance : (Hilbert.KD45).HasK where p := 0; q := 1;
instance : (Hilbert.KD45).HasD where p := 0
instance : (Hilbert.KD45).HasFour where p := 0
instance : (Hilbert.KD45).HasFive where p := 0
instance : Entailment.KD45 (Hilbert.KD45) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KB4 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0), Axioms.Four (.atom 0)}⟩
instance : (Hilbert.KB4).HasK where p := 0; q := 1;
instance : (Hilbert.KB4).HasB where p := 0
instance : (Hilbert.KB4).HasFour where p := 0
instance : Entailment.KB4 (Hilbert.KB4) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KB5 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0), Axioms.Five (.atom 0)}⟩
instance : (Hilbert.KB5).HasK where p := 0; q := 1;
instance : (Hilbert.KB5).HasB where p := 0
instance : (Hilbert.KB5).HasFive where p := 0
instance : Entailment.KB5 (Hilbert.KB5) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S4 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0)}⟩
instance : (Hilbert.S4).HasK where p := 0; q := 1;
instance : (Hilbert.S4).HasT where p := 0
instance : (Hilbert.S4).HasFour where p := 0
instance : Entailment.S4 (Hilbert.S4) where

lemma K4_weakerThan_S4 : Hilbert.K4 wkn Hilbert.S4 := weakerThan_of_dominate_axioms <| by simp;

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S4Dot2 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dot2 (.atom 0)}⟩
instance : (Hilbert.S4Dot2).HasK where p := 0; q := 1;
instance : (Hilbert.S4Dot2).HasT where p := 0
instance : (Hilbert.S4Dot2).HasFour where p := 0
instance : (Hilbert.S4Dot2).HasDot2 where p := 0
instance : Entailment.S4Dot2 (Hilbert.S4Dot2) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S4Dot3 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0),
    Axioms.Dot3 (.atom 0) (.atom 1)}⟩
instance : (Hilbert.S4Dot3).HasK where p := 0; q := 1;
instance : (Hilbert.S4Dot3).HasT where p := 0
instance : (Hilbert.S4Dot3).HasFour where p := 0
instance : (Hilbert.S4Dot3).HasDot3 where p := 0; q := 1;
instance : Entailment.S4Dot3 (Hilbert.S4Dot3) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Five (.atom 0)}⟩
instance : (Hilbert.K5).HasK where p := 0; q := 1;
instance : (Hilbert.K5).HasFive where p := 0
instance : Entailment.K5 (Hilbert.K5) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S5 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0)}⟩
instance : (Hilbert.S5).HasK where p := 0; q := 1;
instance : (Hilbert.S5).HasT where p := 0
instance : (Hilbert.S5).HasFive where p := 0
instance : Entailment.S5 (Hilbert.S5) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev GL : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0)}⟩
instance : (Hilbert.GL).HasK where p := 0; q := 1;
instance : (Hilbert.GL).HasL where p := 0
instance : Entailment.GL (Hilbert.GL) where

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KH : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.H (.atom 0)}⟩
instance : (Hilbert.KH).HasK where p := 0; q := 1;
instance : (Hilbert.KH).HasH where p := 0

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Grz : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0)}⟩
instance : (Hilbert.Grz).HasK where p := 0; q := 1;
instance : (Hilbert.Grz).HasGrz where p := 0
instance : Entailment.Grz (Hilbert.Grz) where

lemma KT_weakerThan_Grz : Hilbert.KT wkn Hilbert.Grz := weakerThan_of_dominate_axioms <| by simp;


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Ver : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Ver (.atom 0)}⟩
instance : (Hilbert.Ver).HasK where p := 0; q := 1;
instance : (Hilbert.Ver).HasVer where p := 0
instance : Entailment.Ver (Hilbert.Ver) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Triv : Hilbert ℕ :=
  ⟨{ Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Tc (.atom 0)}⟩
instance : (Hilbert.Triv).HasK where p := 0; q := 1;
instance : (Hilbert.Triv).HasT where p := 0
instance : (Hilbert.Triv).HasTc where p := 0
instance : Entailment.Triv (Hilbert.Triv) where

lemma K4_weakerThan_Triv : Hilbert.K4 wkn Hilbert.Triv := weakerThan_of_dominate_axioms <| by simp;

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev N : Hilbert ℕ := ⟨{}⟩

end Hilbert

end Modal
end LO
