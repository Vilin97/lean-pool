/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import LeanPool.Circuitlib.Circuit.Category.Combinational
public import LeanPool.Circuitlib.Circuit.Basic

@[expose] public section

/-! # Combinational circuits

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

open CategoryTheory
open MonoidalCategory
open OfNat

abbrev CombinationalCircuit := CombinationalCircuitCategory BelnapLevel BelnapGate

namespace CombinationalCircuit

abbrev and := Circuit.and (C:=CombinationalCircuit)

@[simp]
lemma and_def (x y : Bool) : and.val #v[↑x, ↑y] = #v[↑(x && y)] := by cases x <;> cases y <;> rfl

abbrev or := Circuit.or (C:=CombinationalCircuit)

@[simp]
lemma or_def (x y : Bool) : or.val #v[↑x, ↑y] = #v[↑(x || y)] := by cases x <;> cases y <;> rfl

abbrev not := Circuit.not (C:=CombinationalCircuit)

@[simp]
lemma not_def (x : Bool) : not.val #v[↑x] = #v[↑(!x)] := by cases x <;> rfl

abbrev nand := Circuit.nand (C:=CombinationalCircuit)

@[simp]
lemma nand_def (x y : Bool) : nand.val #v[↑x, ↑y] = #v[↑!((x && y))] := by
  cases x <;> cases y <;> rfl

abbrev nor := Circuit.nor (C:=CombinationalCircuit)

@[simp]
lemma nor_def (x y : Bool) : nor.val #v[↑x, ↑y] = #v[↑(!(x || y))] := by cases x <;> cases y <;> rfl

abbrev fork := CircuitCategory.fork (C:=CombinationalCircuit)

@[simp]
lemma fork_def (x : Bool) : fork.val #v[↑x] = #v[↑x, ↑x] := by cases x <;> rfl

def fork₂ := fork ⊗ₘ fork

@[simp]
lemma fork₂_def (x y : Bool) : fork₂.val #v[↑x, ↑y] = #v[↑x, ↑x, ↑y, ↑y] :=
  by cases x <;> cases y <;> simp <;> rfl

def copy : (ofNat 2 : CombinationalCircuit) ⟶ 4 := fork₂ ≫ (1 ◁ ((β_ 1 1).hom ▷ 1))

@[simp]
lemma copy_def (x y : Bool) : copy.val #v[↑x, ↑y] = #v[↑x, ↑y, ↑x, ↑y] := by
  cases x <;> cases y <;> rfl

def xor : (ofNat 2 : CombinationalCircuit) ⟶ 1 := copy ≫ (and ⊗ₘ or) ≫ (not ⊗ₘ 𝟙 1) ≫ and

@[simp]
lemma xor_def (x y : Bool) : xor.val #v[↑x, ↑y] = #v[↑((x && !y) || (!x && y))] := by
  cases x <;> cases y <;> rfl

def xnor : (ofNat 2 : CombinationalCircuit) ⟶ 1 := xor ≫ not

@[simp]
lemma xnor_def (x y : Bool) : xnor.val #v[↑x, ↑y] = #v[↑((x && y) || (!x && !y))] := by
  cases x <;> cases y <;> rfl

def halfAdder : (ofNat 2 : CombinationalCircuit) ⟶ 2 := copy ≫ (xor ⊗ₘ and)

@[simp]
lemma halfAdder_def
    (x y : Bool) :
    halfAdder.val #v[↑x, ↑y] = #v[↑((x && !y) || (!x && y)), ↑(x && y)] := by
  cases x <;> cases y <;> rfl

def adder : (ofNat 3 : CombinationalCircuit) ⟶ 2 :=
  (halfAdder ⊗ₘ 𝟙 1) ≫
  (1 ◁ (β_ 1 1).hom) ⊗≫
  (halfAdder ⊗ₘ 𝟙 1) ≫
  (𝟙 1 ⊗ₘ or)

@[simp]
lemma adder_def (x y z : Bool) :
    adder.val #v[↑x, ↑y, ↑z] =
      #v[↑((((x && !y) || (!x && y)) && !z) || (!(((x && !y) || (!x && y))) && z)),
         ↑((x && y) || (((x && !y) || (!x && y)) && z))] := by
  cases x <;> cases y <;> cases z <;> rfl

end CombinationalCircuit

end Circuit
