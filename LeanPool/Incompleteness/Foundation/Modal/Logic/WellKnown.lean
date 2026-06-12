/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Hilbert.Maximal.Unprovability
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.GL.MDP
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Grz.Completeness
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.K4
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.K45
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.K5
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KB
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KB4
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KB5
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KD
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KD4
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KD45
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KD5
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KDB
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KT
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KTB
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.S4
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.S4Dot2
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.S4Dot3
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.S5
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Triv
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Ver
import LeanPool.Incompleteness.Foundation.Modal.Hilbert.S5Grz
import LeanPool.Incompleteness.Foundation.Modal.Logic.Basic
import LeanPool.Incompleteness.Foundation.Modal.Entailment.KT
import LeanPool.Incompleteness.Foundation.Modal.Kripke.KHIncompleteness

/-! # WellKnown -/


namespace LO
namespace Modal

namespace Logic

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K4 : Logic := Hilbert.K4.logic
lemma _root_.LO.Modal.Logic.K4.eq_TransitiveKripkeFrameClass_Logic :
    Logic.K4 = Kripke.TransitiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K45 : Logic := Hilbert.K45.logic
lemma _root_.LO.Modal.Logic.K45.eq_TransitiveEuclideanKripkeFrameClass_Logic :
    Logic.K45 = Kripke.TransitiveEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K5 : Logic := Hilbert.K5.logic
lemma _root_.LO.Modal.Logic.K5.eq_EuclideanKripkeFrameClass_Logic :
    Logic.K5 = Kripke.EuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KB : Logic := Hilbert.KB.logic
lemma _root_.LO.Modal.Logic.KB.eq_SymmetricKripkeFrameClass_Logic :
    Logic.KB = Kripke.SymmetricFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KB4 : Logic := Hilbert.KB4.logic
lemma _root_.LO.Modal.Logic.KB4.eq_ReflexiveTransitiveKripkeFrameClass_Logic :
    Logic.KB4 = Kripke.SymmetricTransitiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KB5 : Logic := Hilbert.KB5.logic
lemma _root_.LO.Modal.Logic.KB5.eq_ReflexiveEuclideanKripkeFrameClass_Logic :
    Logic.KB5 = Kripke.SymmetricEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD : Logic := Hilbert.KD.logic
lemma _root_.LO.Modal.Logic.KD.eq_SerialKripkeFrameClass_Logic :
    Logic.KD = Kripke.SerialFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD4 : Logic := Hilbert.KD4.logic
lemma _root_.LO.Modal.Logic.KD4.eq_SerialTransitiveKripkeFrameClass_Logic :
    Logic.KD4 = Kripke.SerialTransitiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD45 : Logic := Hilbert.KD45.logic
lemma _root_.LO.Modal.Logic.KD45.eq_SerialTransitiveEuclideanKripkeFrameClass_Logic :
    Logic.KD45 = Kripke.SerialTransitiveEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD5 : Logic := Hilbert.KD5.logic
lemma _root_.LO.Modal.Logic.KD5.eq_SerialEuclideanKripkeFrameClass_Logic :
    Logic.KD5 = Kripke.SerialEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KDB : Logic := Hilbert.KDB.logic
lemma _root_.LO.Modal.Logic.KDB.eq_SerialSymmetricKripkeFrameClass_Logic :
    Logic.KDB = Kripke.SerialSymmetricFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KT : Logic := Hilbert.KT.logic
lemma _root_.LO.Modal.Logic.KT.eq_ReflexiveKripkeFrameClass_Logic :
    Logic.KT = Kripke.ReflexiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KTB : Logic := Hilbert.KTB.logic
lemma _root_.LO.Modal.Logic.KTB.eq_ReflexiveSymmetricKripkeFrameClass_Logic :
    Logic.KTB = Kripke.ReflexiveSymmetricFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S4 : Logic := Hilbert.S4.logic
lemma _root_.LO.Modal.Logic.S4.eq_ReflexiveTransitiveKripkeFrameClass_Logic :
    Logic.S4 = Kripke.ReflexiveTransitiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S4Dot2 : Logic := Hilbert.S4Dot2.logic
lemma _root_.LO.Modal.Logic.S4Dot2.eq_ReflexiveTransitiveConfluentKripkeFrameClass_Logic :
    Logic.S4Dot2 = Kripke.ReflexiveTransitiveConfluentFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S4Dot3 : Logic := Hilbert.S4Dot3.logic
lemma _root_.LO.Modal.Logic.S4Dot3.eq_ReflexiveTransitiveConnectedKripkeFrameClass_Logic :
    Logic.S4Dot3 = Kripke.ReflexiveTransitiveConnectedFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S5 : Logic := Hilbert.S5.logic
lemma _root_.LO.Modal.Logic.S5.eq_ReflexiveEuclideanKripkeFrameClass_Logic :
    Logic.S5 = Kripke.ReflexiveEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic
lemma _root_.LO.Modal.Logic.S5.eq_UniversalKripkeFrameClass_Logic :
    Logic.S5 = Kripke.UniversalFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S5Grz : Logic := Hilbert.S5Grz.logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev GL : Logic := Hilbert.GL.logic
lemma _root_.LO.Modal.Logic.GL.eq_TransitiveIrreflexiveFiniteKripkeFrameClass_Logic :
    Logic.GL = Kripke.TransitiveIrreflexiveFiniteFrameClass.logic
  := eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic
instance : (Logic.GL).Unnecessitation := inferInstance


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KH : Logic := Hilbert.KH.logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Grz : Logic := Hilbert.Grz.logic
lemma _root_.LO.Modal.Logic.Grz.eq_ReflexiveTransitiveAntiSymmetricFiniteKripkeFrameClass_Logic :
    Logic.Grz = Kripke.ReflexiveTransitiveAntiSymmetricFiniteFrameClass.logic
  := eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Triv : Logic := Hilbert.Triv.logic
lemma _root_.LO.Modal.Logic.Triv.eq_EqualityKripkeFrameClass_Logic :
    Logic.Triv = Kripke.EqualityFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Ver : Logic := Hilbert.Ver.logic
instance : (Logic.Ver).Normal := Hilbert.normal
lemma _root_.LO.Modal.Logic.Ver.eq_IsolatedFrameClass_Logic :
    Logic.Ver = Kripke.IsolatedFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

end Logic

end Modal
end LO
