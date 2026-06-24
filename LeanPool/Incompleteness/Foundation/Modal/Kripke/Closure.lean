/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Vorspiel.BinaryRelations
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Basic

/-! # Closure -/


namespace LO
namespace Modal

namespace Kripke

variable {F : Frame} {x y z : F.World}

open Relation


section «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.RelReflTransGen : _root_.Rel F.World F.World :=
  ReflTransGen (· ≺ ·)
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ≺^* " => Frame.RelReflTransGen

namespace Frame
namespace RelReflTransGen

@[simp] lemma single (hxy : x ≺ y) : x ≺^* y := ReflTransGen.single hxy

@[simp] lemma reflexive : Std.Refl F.RelReflTransGen := ⟨fun _ => ReflTransGen.refl⟩

@[simp] lemma refl {x : F.World} : x ≺^* x := reflexive.refl x

@[simp] lemma transitive : IsTrans F.World F.RelReflTransGen :=
  ⟨fun _ _ _ hxy hyz => ReflTransGen.trans hxy hyz⟩

@[simp] lemma symmetric : IsSymmetric F.Rel → IsSymmetric F.RelReflTransGen := fun h => by
  letI : Std.Symm F.Rel := ⟨fun _ _ => @h _ _⟩
  exact fun _ _ hxy => Std.Symm.symm (r := F.RelReflTransGen) _ _ hxy

end RelReflTransGen
end Frame


/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.TransitiveReflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^* ·)
/-- Imported declaration from the Incompleteness formalization. -/
postfix:95 "^*" => Frame.TransitiveReflexiveClosure

namespace Frame
namespace TransitiveReflexiveClosure

lemma single (hxy : x ≺ y) : F^*.Rel x y := ReflTransGen.single hxy

lemma rel_reflexive : Std.Refl (F^*.Rel) := ⟨fun _ => ReflTransGen.refl⟩

lemma rel_transitive : IsTrans (F^*) (F^*.Rel) := ⟨fun _ _ _ hxy hyz => ReflTransGen.trans hxy hyz⟩

lemma rel_symmetric : IsSymmetric F.Rel → IsSymmetric (F^*) := fun h => by
  letI : Std.Symm F.Rel := ⟨fun _ _ => @h _ _⟩
  exact fun _ _ hxy => Std.Symm.symm (r := F^*.Rel) _ _ hxy

end TransitiveReflexiveClosure
end Frame

end «lp_section_1»


section «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.RelTransGen {F : Frame} : _root_.Rel F.World F.World :=
  TransGen (· ≺ ·)
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ≺^+ " => Frame.RelTransGen

namespace Frame
namespace RelTransGen

@[simp] lemma single (hxy : x ≺ y) : x ≺^+ y := TransGen.single hxy

@[simp]
lemma transitive : IsTrans F.World F.RelTransGen := ⟨fun _ _ _ => TransGen.trans⟩

@[simp]
lemma symmetric (hSymm : IsSymmetric F.Rel) : IsSymmetric F.RelTransGen := by
  intro x y rxy;
  induction rxy with
  | single h => exact TransGen.single <| hSymm h;
  | tail _ hyz ih => exact TransGen.trans (TransGen.single <| hSymm hyz) ih

end RelTransGen
end Frame


/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.TransitiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^+ ·)
/-- Imported declaration from the Incompleteness formalization. -/
postfix:95 "^+" => Frame.TransitiveClosure

namespace Frame
namespace TransitiveClosure

lemma single (hxy : x ≺ y) : F^+.Rel x y := TransGen.single hxy

lemma rel_transitive : IsTrans (F^+) (F^+.Rel) := ⟨fun _ _ _ => TransGen.trans⟩

lemma rel_symmetric (hSymm : IsSymmetric F.Rel) : IsSymmetric (F^+) := by simp_all

end TransitiveClosure
end Frame

end «lp_section_2»


section «lp_section_3»

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev _root_.LO.Modal.Kripke.Frame.RelReflGen : _root_.Rel F.World F.World :=
  ReflGen (· ≺ ·)
/-- Imported declaration from the Incompleteness formalization. -/
scoped infix:45 " ≺^= " => Frame.RelReflGen

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.ReflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^= ·)
/-- Imported declaration from the Incompleteness formalization. -/
postfix:95 "^=" => Frame.ReflexiveClosure

end «lp_section_3»


section «lp_section_4»

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev _root_.LO.Modal.Kripke.Frame.RelIrreflGen : _root_.Rel F.World F.World :=
  IrreflGen (· ≺ ·)
/-- Imported declaration from the Incompleteness formalization. -/
scoped infix:45 " ≺^≠ " => Frame.RelIrreflGen

namespace Frame
namespace RelIrreflGen

@[simp] lemma rel_irreflexive : Std.Irrefl F.RelIrreflGen := by exact ⟨fun x h => h.1 rfl⟩

end RelIrreflGen
end Frame


/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.IrreflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^≠ ·)
/-- Imported declaration from the Incompleteness formalization. -/
postfix:95 "^≠" => Frame.IrreflexiveClosure

namespace Frame
namespace IrreflexiveClosure

lemma rel_irreflexive : Std.Irrefl (F^≠.Rel) := by exact ⟨fun x h => h.1 rfl⟩

end IrreflexiveClosure
end Frame

end «lp_section_4»


end Kripke

end Modal
end LO
