/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/
import LeanPool.LowWeightPauliDynamics.Pauli.LayerFlow
import LeanPool.LowWeightPauliDynamics.Pauli.Discard

/-!
# A nonzero discarded coefficient of weight above `w* k_h^Γ` in a second-order step

`Pauli/LayerWitness.lean` shows that on an 8-qubit brickwork with `k_h = 2`, `Γ = 2` and the
weight-one input `Z₃` (so `w* = 1`), the Pauli string `P₆` of weight `6` is *reachable* under the
four layers `L₁, L₂, L₂, L₁` of a second-order product-formula step (`apd:eq:suzuki`).
Reachability ignores the rotation angles, so by itself it does not show that `P₆` occurs in the
conjugated operator. This file supplies that step. It computes the coefficient of `P₆` after the
literal four-layer word in closed form,

  `coeff (pf2Output θ) (cls P₆) = -(sin θ)^3 (sin 2θ)^2`,

which is nonzero for `0 < θ < π/2`, and shows that the same coefficient survives in the operator
discarded by the truncation at `w* = 1`, the component `Õ^{(d)}_{≥w*+1}` of
`apd:eq:step_component`. Hence
the exponent `ΥΓ` in the weight bound `w* k_h^{ΥΓ}` on the discarded component
(`apd:thm:lightcone`) cannot be replaced by `Γ`: here `w* k_h^Γ = 4 < 6`.

## Main definitions

* `pf2Rotations θ`: the rotation word `L₁ ++ L₂ ++ L₂ ++ L₁`, every rotation with the same
  conjugation angle `θ`.
* `pf2Output θ`: the matrix obtained by conjugating `Z₃` with that word (`layerConj`).
* `pf2Discard θ`: what the truncation at weight `1` removes from `pf2Output θ`.

## Main results

* `pf2_coeff_polynomial`, `pf2_coeff_sines`: the coefficient of `pf2Output θ` at `cls P₆` is
  `-4 (cos θ)^2 (sin θ)^5 = -(sin θ)^3 (sin 2θ)^2`.
* `pf2_named_P6_component`: the corresponding operator component is
  `((sin θ)^3 (sin 2θ)^2) • P₆`. The sign changes because the canonical representative is
  `herm (cls P₆) = phaseMul 2 P₆` (`herm_P6_sign`), whose matrix is `-P₆`.
* `pf2Output_eq_four_layers`: `pf2Output θ` is the nested conjugation by the four layers.
* `pf2_coeff_ne_zero`: the coefficient is nonzero whenever `0 < θ` and `2 * θ < π`.
* `pf2Discard_coeff`, `actual_discard_exceeds_gamma_bound`: the discarded operator has a nonzero
  coefficient at a Pauli class of weight greater than `w* k_h^Γ = 4`.

## Method

`coeffVec_layerConj` turns the matrix conjugation into the coefficient action `layerAct`, and
`rotAct_apply` gives a two-term recurrence for one rotation. The recurrence is unfolded backwards
from the target class through the fourteen rotations of the word. Only 23 coefficient nodes are
expanded; every other branch the recurrence meets is shown to vanish by the sound support test
`backwardReaches` (`coeff_zero_of_not_backward`), and every sign is computed exactly from
`partnerSign`. Nothing is evaluated numerically.
-/

namespace Lean4LPD.LayerCounterexample

open PauliString LayerWitness Finset

/-- The rotation word of one second-order product-formula step (`apd:eq:suzuki`) on the
brickwork of `LayerWitness`: the four layers `L₁, L₂, L₂, L₁`, every rotation with the same
half-step conjugation angle `θ`. -/
noncomputable def pf2Rotations (θ : ℝ) : List (PauliString 8 × ℝ) :=
  (L₁ ++ L₂ ++ L₂ ++ L₁).map fun G => (G, θ)

/-- The conjugated operator before truncation: the matrix of `Z₃` conjugated by the whole word
`pf2Rotations θ`. It is defined by matrix conjugation (`layerConj`), not as a member of a
reachable set; its high-weight part is the discarded component of `apd:eq:step_component`. -/
noncomputable def pf2Output (θ : ℝ) : Matrix (Bits 8) (Bits 8) ℂ :=
  layerConj (pf2Rotations θ) (toMatrix (Z 3))

/-- Every generator of the word is a Hermitian Pauli string, by `isSelfAdjoint_L₁` and
`isSelfAdjoint_L₂`. This is the hypothesis under which `coeffVec_layerConj` turns the matrix
conjugation into the coefficient action `layerAct`. -/
theorem pf2Rotations_hermitian (θ : ℝ) : ∀ g ∈ pf2Rotations θ, IsSelfAdjoint g.1 := by
  intro g hg
  obtain ⟨G, hG, rfl⟩ := List.mem_map.1 hg
  simp only [List.mem_append] at hG
  rcases hG with ((hG | hG) | hG) | hG
  · exact isSelfAdjoint_L₁ G hG
  · exact isSelfAdjoint_L₂ G hG
  · exact isSelfAdjoint_L₂ G hG
  · exact isSelfAdjoint_L₁ G hG

/-- The input `Z₃` is the canonical Hermitian representative `herm` of its own class, so its
coefficient vector can be read off directly (`input_coeffVec`). -/
theorem herm_input : herm (cls (Z (3 : Fin 8))) = Z 3 := by decide

/-- The coefficient vector of the input `Z₃` is the unit vector at its class `cls (Z 3)`. -/
theorem input_coeffVec : coeffVec (toMatrix (Z (3 : Fin 8))) =
    WithLp.toLp 2 (Pi.single (cls (Z (3 : Fin 8))) (1 : ℂ)) := by
  ext p
  rw [coeffVec_apply, ← herm_input, coeff_toMatrix_herm]
  simp [Pi.single_apply]

/-- A backward support test for the coefficient recurrence `rotAct_apply`. Starting from the
class `p` and running through the generators of `L` in order, it follows the stay branch and,
when the generator anticommutes with the current class, also the `partner` branch, and reports
whether the class `q` can be reached at the end of the list. It is used only to prove that
coefficients vanish (`coeff_zero_of_not_backward`), never to infer a nonzero coefficient from
reachability. -/
private def backwardReaches {n : ℕ} :
    List (PauliString n) → PauliIndex n → PauliIndex n → Bool
  | [], p, q => decide (p = q)
  | G :: L, p, q =>
      if sympForm G (herm p) = 0 then backwardReaches L p q
      else backwardReaches L p q || backwardReaches L (partner G p) q

/-- If the backward support test fails, the coefficient is zero: the `p`-coefficient of
`layerAct` applied to the unit vector at `q` vanishes whenever `backwardReaches L p q = false`.
This sound pruning lemma follows from `rotAct_apply` by induction on `L`. Its converse is not
asserted: angles or cancellations can make a coefficient vanish even when the test succeeds. -/
private theorem coeff_zero_of_not_backward {n : ℕ} (L : List (PauliString n)) (θ : ℝ)
    (p q : PauliIndex n) (h : backwardReaches L p q = false) :
    (layerAct (L.map fun G => (G, θ))
      (WithLp.toLp 2 (Pi.single q (1 : ℂ)))).ofLp p = 0 := by
  induction L generalizing p with
  | nil =>
      have hpq : p ≠ q := by simpa [backwardReaches] using h
      simp [layerAct, hpq]
  | cons G L ih =>
      by_cases hp : sympForm G (herm p) = 0
      · have ht : backwardReaches L p q = false := by simpa [backwardReaches, hp] using h
        simp only [List.map_cons, layerAct, rotAct_apply, hp, ↓reduceIte]
        exact ih p ht
      · have ht : backwardReaches L p q = false ∧ backwardReaches L (partner G p) q = false := by
          simpa [backwardReaches, hp] using h
        simp only [List.map_cons, layerAct, rotAct_apply, hp, ↓reduceIte]
        rw [ih p ht.1, ih (partner G p) ht.2, mul_zero, mul_zero, mul_zero, sub_self]

/-- Binary notation for Pauli classes on eight qubits, used only by the finite coefficient
certificates below: bit `i` of `x` (resp. `z`) is the `X`-part (resp. `Z`-part) at qubit `i`.
Every identity stated in this notation is checked by `decide` against the actual Pauli
operations, not against an assumed simulator. -/
private def bitIndex (x z : ℕ) : PauliIndex 8 :=
  (fun i => if x.testBit i.val then 1 else 0, fun i => if z.testBit i.val then 1 else 0)

/-- The seven generators of `L₁` (indices `0`–`3`) and `L₂` (indices `4`–`6`), indexed for the
finite coefficient calculation. -/
private def generator : Fin 7 → PauliString 8 :=
  ![X 0 * Z 1, X 2 * X 3, Z 4 * X 5, X 6 * X 7,
    X 1 * Z 2, X 3 * X 4, X 5 * X 6]

/-- One explicit step of the coefficient recurrence along the word: if the suffix of
`pf2Rotations θ` starting at position `i` has head `(generator g, θ)`, then the `p`-coefficient
after that suffix is given by `rotAct_apply` in terms of the coefficients after the suffix
starting at `i + 1`. The list-head equation is proved by reflexivity at each concrete use. -/
private theorem suffix_coeff_step (θ : ℝ) (i : ℕ) (g : Fin 7)
    (v : EuclideanSpace ℂ (PauliIndex 8)) (p : PauliIndex 8)
    (h : (pf2Rotations θ).drop i = (generator g, θ) :: (pf2Rotations θ).drop (i + 1)) :
    (layerAct ((pf2Rotations θ).drop i) v).ofLp p =
      if sympForm (generator g) (herm p) = 0 then
        (layerAct ((pf2Rotations θ).drop (i + 1)) v).ofLp p
      else (Real.cos θ : ℂ) * (layerAct ((pf2Rotations θ).drop (i + 1)) v).ofLp p
        - (Real.sin θ : ℂ) * (partnerSign (generator g) p *
          (layerAct ((pf2Rotations θ).drop (i + 1)) v).ofLp (partner (generator g) p)) := by
  rw [h, layerAct, rotAct_apply]

-- Prevent the elaborator from unfolding a whole remaining circuit while checking a
-- single scalar certificate. Each needed head step is explicitly rewritten above;
-- this local reducibility setting changes elaboration only, never kernel conversion.
attribute [local irreducible] layerAct

-- Each suffix identity is checked independently, keeping the scalar certificates small.
private noncomputable abbrev coefficientSeed : EuclideanSpace ℂ (PauliIndex 8) :=
  WithLp.toLp 2 (Pi.single (bitIndex 0 8) (1 : ℂ))

private theorem suffixCoefficient_14_0_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 14) coefficientSeed).ofLp
    (bitIndex 0 8) = 1 := by
  rw [show (pf2Rotations θ).drop 14 = [] by rfl, layerAct]
  exact Pi.single_eq_same (M := fun _ : PauliIndex 8 => ℂ) (bitIndex 0 8) (1 : ℂ)

private theorem suffixCoefficient_13_0_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 13) coefficientSeed).ofLp
    (bitIndex 0 8) = 1 := by
  rw [suffix_coeff_step θ 13 3
    coefficientSeed (bitIndex 0 8) (by rfl),
    ite_eq_left (by decide)]
  all_goals exact (suffixCoefficient_14_0_8 θ)

private theorem suffixCoefficient_12_0_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 12) coefficientSeed).ofLp
    (bitIndex 0 8) = 1 := by
  rw [suffix_coeff_step θ 12 2
    coefficientSeed (bitIndex 0 8) (by rfl),
    ite_eq_left (by decide)]
  all_goals exact (suffixCoefficient_13_0_8 θ)

private theorem suffixCoefficient_11_12_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 11) coefficientSeed).ofLp
    (bitIndex 12 8) = (Real.sin θ : ℂ) := by
  rw [suffix_coeff_step θ 11 1
    coefficientSeed (bitIndex 12 8) (by rfl),
    ite_eq_right (by decide)]
  have h_12_12_8 :
    (layerAct ((pf2Rotations θ).drop 12) coefficientSeed).ofLp
      (bitIndex 12 8) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 12) θ
      (bitIndex 12 8) (bitIndex 0 8) (by decide)
  have hp : partner (generator 1) (bitIndex 12 8) = bitIndex 0 8 := by decide
  have hs : partnerSign (generator 1) (bitIndex 12 8) = (-1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 1) * herm (bitIndex 12 8))).phase
        - (herm (partner (generator 1) (bitIndex 12 8))).phase = 2 by decide]
    all_goals exact iPow_two
  rw [hp, hs, h_12_12_8, (suffixCoefficient_12_0_8 θ)]
  ring

private theorem suffixCoefficient_10_12_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 10) coefficientSeed).ofLp
    (bitIndex 12 8) = (Real.sin θ : ℂ) := by
  rw [suffix_coeff_step θ 10 0
    coefficientSeed (bitIndex 12 8) (by rfl),
    ite_eq_left (by decide)]
  all_goals exact (suffixCoefficient_11_12_8 θ)

private theorem suffixCoefficient_9_12_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 9) coefficientSeed).ofLp
    (bitIndex 12 8) = (Real.sin θ : ℂ) := by
  rw [suffix_coeff_step θ 9 6
    coefficientSeed (bitIndex 12 8) (by rfl),
    ite_eq_left (by decide)]
  all_goals exact (suffixCoefficient_10_12_8 θ)

private theorem suffixCoefficient_8_20_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 8) coefficientSeed).ofLp
    (bitIndex 20 8) = -(Real.sin θ : ℂ) ^ 2 := by
  rw [suffix_coeff_step θ 8 5
    coefficientSeed (bitIndex 20 8) (by rfl),
    ite_eq_right (by decide)]
  have h_9_20_8 :
    (layerAct ((pf2Rotations θ).drop 9) coefficientSeed).ofLp
      (bitIndex 20 8) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 9) θ
      (bitIndex 20 8) (bitIndex 0 8) (by decide)
  have hp : partner (generator 5) (bitIndex 20 8) = bitIndex 12 8 := by decide
  have hs : partnerSign (generator 5) (bitIndex 20 8) = (1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 5) * herm (bitIndex 20 8))).phase
        - (herm (partner (generator 5) (bitIndex 20 8))).phase = 0 by decide]
    all_goals exact iPow_zero
  rw [hp, hs, h_9_20_8, (suffixCoefficient_9_12_8 θ)]
  ring

private theorem suffixCoefficient_8_12_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 8) coefficientSeed).ofLp
    (bitIndex 12 8) = (Real.cos θ : ℂ) * (Real.sin θ : ℂ) := by
  rw [suffix_coeff_step θ 8 5
    coefficientSeed (bitIndex 12 8) (by rfl),
    ite_eq_right (by decide)]
  have h_9_20_8 :
    (layerAct ((pf2Rotations θ).drop 9) coefficientSeed).ofLp
      (bitIndex 20 8) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 9) θ
      (bitIndex 20 8) (bitIndex 0 8) (by decide)
  have hp : partner (generator 5) (bitIndex 12 8) = bitIndex 20 8 := by decide
  have hs : partnerSign (generator 5) (bitIndex 12 8) = (-1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 5) * herm (bitIndex 12 8))).phase
        - (herm (partner (generator 5) (bitIndex 12 8))).phase = 2 by decide]
    all_goals exact iPow_two
  rw [hp, hs, (suffixCoefficient_9_12_8 θ), h_9_20_8]
  ring

private theorem suffixCoefficient_7_22_12 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 7) coefficientSeed).ofLp
    (bitIndex 22 12) = (Real.sin θ : ℂ) ^ 3 := by
  rw [suffix_coeff_step θ 7 4
    coefficientSeed (bitIndex 22 12) (by rfl),
    ite_eq_right (by decide)]
  have h_8_22_12 :
    (layerAct ((pf2Rotations θ).drop 8) coefficientSeed).ofLp
      (bitIndex 22 12) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 8) θ
      (bitIndex 22 12) (bitIndex 0 8) (by decide)
  have hp : partner (generator 4) (bitIndex 22 12) = bitIndex 20 8 := by decide
  have hs : partnerSign (generator 4) (bitIndex 22 12) = (1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 4) * herm (bitIndex 22 12))).phase
        - (herm (partner (generator 4) (bitIndex 22 12))).phase = 0 by decide]
    all_goals exact iPow_zero
  rw [hp, hs, h_8_22_12, (suffixCoefficient_8_20_8 θ)]
  ring

private theorem suffixCoefficient_7_20_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 7) coefficientSeed).ofLp
    (bitIndex 20 8) = -(Real.cos θ : ℂ) * (Real.sin θ : ℂ) ^ 2 := by
  rw [suffix_coeff_step θ 7 4
    coefficientSeed (bitIndex 20 8) (by rfl),
    ite_eq_right (by decide)]
  have h_8_22_12 :
    (layerAct ((pf2Rotations θ).drop 8) coefficientSeed).ofLp
      (bitIndex 22 12) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 8) θ
      (bitIndex 22 12) (bitIndex 0 8) (by decide)
  have hp : partner (generator 4) (bitIndex 20 8) = bitIndex 22 12 := by decide
  have hs : partnerSign (generator 4) (bitIndex 20 8) = (-1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 4) * herm (bitIndex 20 8))).phase
        - (herm (partner (generator 4) (bitIndex 20 8))).phase = 2 by decide]
    all_goals exact iPow_two
  rw [hp, hs, (suffixCoefficient_8_20_8 θ), h_8_22_12]
  ring

private theorem suffixCoefficient_7_14_12 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 7) coefficientSeed).ofLp
    (bitIndex 14 12) = (Real.cos θ : ℂ) * (Real.sin θ : ℂ) ^ 2 := by
  rw [suffix_coeff_step θ 7 4
    coefficientSeed (bitIndex 14 12) (by rfl),
    ite_eq_right (by decide)]
  have h_8_14_12 :
    (layerAct ((pf2Rotations θ).drop 8) coefficientSeed).ofLp
      (bitIndex 14 12) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 8) θ
      (bitIndex 14 12) (bitIndex 0 8) (by decide)
  have hp : partner (generator 4) (bitIndex 14 12) = bitIndex 12 8 := by decide
  have hs : partnerSign (generator 4) (bitIndex 14 12) = (-1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 4) * herm (bitIndex 14 12))).phase
        - (herm (partner (generator 4) (bitIndex 14 12))).phase = 2 by decide]
    all_goals exact iPow_two
  rw [hp, hs, h_8_14_12, (suffixCoefficient_8_12_8 θ)]
  ring

private theorem suffixCoefficient_7_12_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 7) coefficientSeed).ofLp
    (bitIndex 12 8) = (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) := by
  rw [suffix_coeff_step θ 7 4
    coefficientSeed (bitIndex 12 8) (by rfl),
    ite_eq_right (by decide)]
  have h_8_14_12 :
    (layerAct ((pf2Rotations θ).drop 8) coefficientSeed).ofLp
      (bitIndex 14 12) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 8) θ
      (bitIndex 14 12) (bitIndex 0 8) (by decide)
  have hp : partner (generator 4) (bitIndex 12 8) = bitIndex 14 12 := by decide
  have hs : partnerSign (generator 4) (bitIndex 12 8) = (1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 4) * herm (bitIndex 12 8))).phase
        - (herm (partner (generator 4) (bitIndex 12 8))).phase = 0 by decide]
    all_goals exact iPow_zero
  rw [hp, hs, (suffixCoefficient_8_12_8 θ), h_8_14_12]
  ring

private theorem suffixCoefficient_6_22_12 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 6) coefficientSeed).ofLp
    (bitIndex 22 12) = (Real.sin θ : ℂ) ^ 3 := by
  rw [suffix_coeff_step θ 6 6
    coefficientSeed (bitIndex 22 12) (by rfl),
    ite_eq_left (by decide)]
  all_goals exact (suffixCoefficient_7_22_12 θ)

private theorem suffixCoefficient_6_20_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 6) coefficientSeed).ofLp
    (bitIndex 20 8) = -(Real.cos θ : ℂ) * (Real.sin θ : ℂ) ^ 2 := by
  rw [suffix_coeff_step θ 6 6
    coefficientSeed (bitIndex 20 8) (by rfl),
    ite_eq_left (by decide)]
  all_goals exact (suffixCoefficient_7_20_8 θ)

private theorem suffixCoefficient_6_14_12 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 6) coefficientSeed).ofLp
    (bitIndex 14 12) = (Real.cos θ : ℂ) * (Real.sin θ : ℂ) ^ 2 := by
  rw [suffix_coeff_step θ 6 6
    coefficientSeed (bitIndex 14 12) (by rfl),
    ite_eq_left (by decide)]
  all_goals exact (suffixCoefficient_7_14_12 θ)

private theorem suffixCoefficient_6_12_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 6) coefficientSeed).ofLp
    (bitIndex 12 8) = (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) := by
  rw [suffix_coeff_step θ 6 6
    coefficientSeed (bitIndex 12 8) (by rfl),
    ite_eq_left (by decide)]
  all_goals exact (suffixCoefficient_7_12_8 θ)

private theorem suffixCoefficient_5_22_12 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 5) coefficientSeed).ofLp
    (bitIndex 22 12) = 2 * (Real.cos θ : ℂ) * (Real.sin θ : ℂ) ^ 3 := by
  rw [suffix_coeff_step θ 5 5
    coefficientSeed (bitIndex 22 12) (by rfl),
    ite_eq_right (by decide)]
  have hp : partner (generator 5) (bitIndex 22 12) = bitIndex 14 12 := by decide
  have hs : partnerSign (generator 5) (bitIndex 22 12) = (-1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 5) * herm (bitIndex 22 12))).phase
        - (herm (partner (generator 5) (bitIndex 22 12))).phase = 2 by decide]
    all_goals exact iPow_two
  rw [hp, hs, (suffixCoefficient_6_22_12 θ), (suffixCoefficient_6_14_12 θ)]
  ring

private theorem suffixCoefficient_5_20_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 5) coefficientSeed).ofLp
    (bitIndex 20 8) = -2 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2 := by
  rw [suffix_coeff_step θ 5 5
    coefficientSeed (bitIndex 20 8) (by rfl),
    ite_eq_right (by decide)]
  have hp : partner (generator 5) (bitIndex 20 8) = bitIndex 12 8 := by decide
  have hs : partnerSign (generator 5) (bitIndex 20 8) = (1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 5) * herm (bitIndex 20 8))).phase
        - (herm (partner (generator 5) (bitIndex 20 8))).phase = 0 by decide]
    all_goals exact iPow_zero
  rw [hp, hs, (suffixCoefficient_6_20_8 θ), (suffixCoefficient_6_12_8 θ)]
  ring

private theorem suffixCoefficient_4_22_12 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 4) coefficientSeed).ofLp
    (bitIndex 22 12) = 4 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 3 := by
  rw [suffix_coeff_step θ 4 4
    coefficientSeed (bitIndex 22 12) (by rfl),
    ite_eq_right (by decide)]
  have hp : partner (generator 4) (bitIndex 22 12) = bitIndex 20 8 := by decide
  have hs : partnerSign (generator 4) (bitIndex 22 12) = (1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 4) * herm (bitIndex 22 12))).phase
        - (herm (partner (generator 4) (bitIndex 22 12))).phase = 0 by decide]
    all_goals exact iPow_zero
  rw [hp, hs, (suffixCoefficient_5_22_12 θ), (suffixCoefficient_5_20_8 θ)]
  ring

private theorem suffixCoefficient_3_22_12 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 3) coefficientSeed).ofLp
    (bitIndex 22 12) = 4 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 3 := by
  rw [suffix_coeff_step θ 3 3
    coefficientSeed (bitIndex 22 12) (by rfl),
    ite_eq_left (by decide)]
  all_goals exact (suffixCoefficient_4_22_12 θ)

private theorem suffixCoefficient_2_54_28 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 2) coefficientSeed).ofLp
    (bitIndex 54 28) = 4 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 4 := by
  rw [suffix_coeff_step θ 2 2
    coefficientSeed (bitIndex 54 28) (by rfl),
    ite_eq_right (by decide)]
  have h_3_54_28 :
    (layerAct ((pf2Rotations θ).drop 3) coefficientSeed).ofLp
      (bitIndex 54 28) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 3) θ
      (bitIndex 54 28) (bitIndex 0 8) (by decide)
  have hp : partner (generator 2) (bitIndex 54 28) = bitIndex 22 12 := by decide
  have hs : partnerSign (generator 2) (bitIndex 54 28) = (-1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 2) * herm (bitIndex 54 28))).phase
        - (herm (partner (generator 2) (bitIndex 54 28))).phase = 2 by decide]
    all_goals exact iPow_two
  rw [hp, hs, h_3_54_28, (suffixCoefficient_3_22_12 θ)]
  ring

private theorem suffixCoefficient_1_54_28 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 1) coefficientSeed).ofLp
    (bitIndex 54 28) = 4 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 4 := by
  rw [suffix_coeff_step θ 1 1
    coefficientSeed (bitIndex 54 28) (by rfl),
    ite_eq_left (by decide)]
  all_goals exact (suffixCoefficient_2_54_28 θ)

private theorem suffixCoefficient_0_55_30 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 0) coefficientSeed).ofLp
    (bitIndex 55 30) = -4 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 5 := by
  rw [suffix_coeff_step θ 0 0
    coefficientSeed (bitIndex 55 30) (by rfl),
    ite_eq_right (by decide)]
  have h_1_55_30 :
    (layerAct ((pf2Rotations θ).drop 1) coefficientSeed).ofLp
      (bitIndex 55 30) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 1) θ
      (bitIndex 55 30) (bitIndex 0 8) (by decide)
  have hp : partner (generator 0) (bitIndex 55 30) = bitIndex 54 28 := by decide
  have hs : partnerSign (generator 0) (bitIndex 55 30) = (1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 0) * herm (bitIndex 55 30))).phase
        - (herm (partner (generator 0) (bitIndex 55 30))).phase = 0 by decide]
    all_goals exact iPow_zero
  rw [hp, hs, h_1_55_30, (suffixCoefficient_1_54_28 θ)]
  ring

/-- **The coefficient of `P₆` as a polynomial in `cos θ` and `sin θ`.** The coefficient of
`pf2Output θ` at the weight-six class `cls P₆` equals `-4 (cos θ)^2 (sin θ)^5`, obtained by
unfolding the coefficient recurrence `rotAct_apply` through the fourteen rotations of the literal
second-order word. The sign refers to the canonical representative `herm (cls P₆)`; see
`pf2_named_P6_component` for the component on `P₆` itself. -/
theorem pf2_coeff_polynomial (θ : ℝ) :
    coeff (pf2Output θ) (cls P₆) =
      -4 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 5 := by
  change (coeffVec (pf2Output θ)).ofLp (cls P₆) = _
  rw [pf2Output, coeffVec_layerConj _ (pf2Rotations_hermitian θ), input_coeffVec]
  have hseed : cls (Z (3 : Fin 8)) = bitIndex 0 8 := by decide
  have htarget : cls P₆ = bitIndex 55 30 := by decide
  rw [hseed, htarget]
  simpa only [List.drop_zero] using suffixCoefficient_0_55_30 θ

/-- Conjugation by a concatenated rotation word is nested conjugation:
`layerConj (L ++ M) O = layerConj L (layerConj M O)`. This is the grouping identity used to
split the second-order word into its four layers. -/
private theorem conj_append {n : ℕ} (L M : List (PauliString n × ℝ))
    (O : Matrix (Bits n) (Bits n) ℂ) :
    layerConj (L ++ M) O = layerConj L (layerConj M O) := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    rcases g with ⟨G, θ⟩
    simp only [List.cons_append, layerConj, ih]

/-- The computed output is the literal four-layer `L₁,L₂,L₂,L₁` second-order formula of
`apd:eq:suzuki`: the nested conjugation of `Z₃` by the four layers, with the two adjacent `L₂`
half-steps kept separate and the same angle in every layer, not a merged or angle-rescaled
circuit. -/
theorem pf2Output_eq_four_layers (θ : ℝ) :
    pf2Output θ = layerConj (L₁.map fun G => (G, θ))
      (layerConj (L₂.map fun G => (G, θ))
        (layerConj (L₂.map fun G => (G, θ))
          (layerConj (L₁.map fun G => (G, θ)) (toMatrix (Z 3))))) := by
  simp only [pf2Output, pf2Rotations, List.map_append, conj_append]

/-- **The coefficient in product form, `-(sin θ)^3 (sin 2θ)^2`.** This is
`pf2_coeff_polynomial` rewritten with `sin 2θ = 2 sin θ cos θ`; in this form it is evident that
the coefficient is nonzero at every small angle (`pf2_coeff_ne_zero`). The minus sign is that of
the canonical representative `herm (cls P₆)`, not of the tensor product `P₆` itself
(`herm_P6_sign`). This upgrades the reachability witness `LayerWitness.P₆_mem_reachable_unmerged`
to an actual coefficient. -/
theorem pf2_coeff_sines (θ : ℝ) :
    coeff (pf2Output θ) (cls P₆) =
      -(Real.sin θ : ℂ) ^ 3 * (Real.sin (2 * θ) : ℂ) ^ 2 := by
  rw [pf2_coeff_polynomial, Real.sin_two_mul]
  push_cast
  ring

/-- The named witness `P₆` has three `Y` sites and carries the phase `3 = #{Y-sites} mod 4`,
whereas `herm` records only the parity of the number of `Y` sites (phase `1`). The two
representatives of the class differ by the phase `2`, that is by the factor `i^2 = -1`, which
accounts for the sign in `pf2_coeff_sines`. -/
theorem herm_P6_sign : herm (cls P₆) = phaseMul 2 P₆ := by decide

/-- On the **named positive tensor `P₆`**, the amplitude is `sin³θ sin²(2θ)`.
This is an operator-component identity, with `coeff • toMatrix (herm (cls P₆))` on the left, not
an identification of classes up to an unspecified phase. -/
theorem pf2_named_P6_component (θ : ℝ) :
    coeff (pf2Output θ) (cls P₆) • toMatrix (herm (cls P₆)) =
      ((Real.sin θ : ℂ) ^ 3 * (Real.sin (2 * θ) : ℂ) ^ 2) • toMatrix P₆ := by
  rw [pf2_coeff_sines, herm_P6_sign, toMatrix_phaseMul, iPow_two, smul_smul]
  congr 1
  ring

/-- The input `Z₃` satisfies the weight-one cutoff: its coefficients at all classes of weight
greater than `1` vanish. So the step starts from an operator of weight at most `w* = 1`, as the
truncated input in `apd:eq:step_component` does, rather than from a large initial observable. -/
theorem input_local : ∀ p : PauliIndex 8, 1 < wt p → coeff (toMatrix (Z 3)) p = 0 := by
  intro p hp
  rw [← herm_input]
  exact coeff_toMatrix_herm_eq_zero (by simpa only [wt_cls, weight_Z_three] using hp)

/-- The coefficient is nonzero throughout `0<θ<π/2`, so the witness works at arbitrarily
small angles, not only in a large-angle regime. -/
theorem pf2_coeff_ne_zero {θ : ℝ} (hθ : 0 < θ) (hθπ : 2 * θ < Real.pi) :
    coeff (pf2Output θ) (cls P₆) ≠ 0 := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith)
  have hs2 : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by positivity) hθπ
  have hsC : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  have hs2C : (Real.sin (2 * θ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs2
  rw [pf2_coeff_sines]
  exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 3 hsC)) (pow_ne_zero 2 hs2C)

/-- The operator discarded after this second-order step by the truncation at `w* = 1`:
`pf2Output θ` minus its part on classes of weight at most one. This is the discarded component
`Õ^{(d)}_{≥w*+1}` of `apd:eq:step_component` for this step, not the part that is retained. -/
noncomputable def pf2Discard (θ : ℝ) : Matrix (Bits 8) (Bits 8) ℂ :=
  pf2Output θ - truncOp (highSet 8 1)ᶜ (pf2Output θ)

/-- The weight-six coefficient is preserved in the discarded operator: `pf2Discard θ` and
`pf2Output θ` have the same coefficient at `cls P₆`, because `wt (cls P₆) = 6 > 1` puts that
class outside the retained set. This is the truncation step that a reachability argument alone
does not provide. -/
theorem pf2Discard_coeff (θ : ℝ) :
    coeff (pf2Discard θ) (cls P₆) = coeff (pf2Output θ) (cls P₆) := by
  rw [pf2Discard, coeff_sub, coeff_truncOp,
    ite_eq_right (by simp [Finset.mem_compl, mem_highSet, weight_P₆]), sub_zero]

/-- **The exponent `ΥΓ` cannot be replaced by `Γ`.** For every `0<θ<π/2`, the two-local
disjoint-support layers `L₁`, `L₂` of `LayerWitness` (so `k_h = 2`, `Γ = 2`) produce, after one
second-order step from the weight-one input `Z₃`, a discarded operator `X₁` at cutoff `w* = 1`
(`apd:eq:step_component`) with a nonzero coefficient at a Pauli class of weight greater than
`w* k_h^Γ = 1 * 2 ^ 2 = 4`; the witness is `cls P₆`, of weight `6`. The weight bound
`w* k_h^{ΥΓ}` of `apd:thm:lightcone`, which for the `ΥΓ = 4` layers of this step equals `16`,
is compatible with this witness. -/
theorem actual_discard_exceeds_gamma_bound {θ : ℝ} (hθ : 0 < θ) (hθπ : 2 * θ < Real.pi) :
    ∃ p : PauliIndex 8, coeff (pf2Discard θ) p ≠ 0 ∧ (1 * 2 ^ 2 : ℕ) < wt p := by
  refine ⟨cls P₆, ?_, ?_⟩
  · rw [pf2Discard_coeff]
    exact pf2_coeff_ne_zero hθ hθπ
  · simp [weight_P₆]

end Lean4LPD.LayerCounterexample
