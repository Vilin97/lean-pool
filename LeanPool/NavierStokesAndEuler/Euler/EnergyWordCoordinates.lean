/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyDifferentiatedEquation
public import LeanPool.NavierStokesAndEuler.Euler.RegularizedEnergyFamily
public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordBlockCoordinates

@[expose] public section

/-! Exact concatenated coordinates connecting energy regularization to the actual external/base
  Gevrey forcing. -/

noncomputable section

namespace EulerEnergyWordCoordinates

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevWordBlocks EulerSobolevWordLevel
  EulerMildTopWord EulerGevreyDifferentiatedEquation EulerGevreyMetricComparison EulerBaseWordMetric
  EulerRegularizedEnergyFamily EulerRegularizedWordEquation EulerH6Pressure

variable (period : ℝ) [Fact (0 < period)]

/-- A derivative of a genuine word-at-level block is the literal concatenated strong derivative. -/
theorem wordAtLevel_word {s : ℕ} (q n : ℕ) (w : Fin n → Fin 4) (h : n+q ≤ s)
    (u : SobolevSpace period s) {m : ℕ} (hm : m ≤ q) (v : Fin m → Fin 4) :
    word period (wordAtLevel period q n w h u) hm v =
      word period u (by omega : m+n ≤ s) (Fin.append v w) := by
  change word period (wordBlock period q n w (restrictOperator period (by omega : q+n ≤ s) u)) hm v
    = _
  rw [wordBlock_word]
  rfl

/-- Bounded word blocks and the spatial-estimate word-at-level operator are the same genuine map. -/
theorem boundedWordBlock_eq_wordAtLevel {s : ℕ} (q n : ℕ) (h : q+n ≤ s) (w : Fin n → Fin 4) :
    boundedWordBlock period q n h w = wordAtLevel period q n w (by omega : n+q ≤ s) := rfl

/-- Two actual Sobolev word blocks compose by literal word concatenation. -/
theorem wordAtLevel_comp {s p q n m : ℕ} (w : Fin n → Fin 4) (v : Fin m → Fin 4)
    (h : n+q ≤ s) (h' : m+p ≤ q) (u : SobolevSpace period s) :
    wordAtLevel period p m v h' (wordAtLevel period q n w h u) =
      wordAtLevel period p (m+n) (Fin.append v w) (by omega : m+n+p ≤ s) u := by
  apply value_injective period
  rw [wordAtLevel_value, toJet_word period _ (by omega : m ≤ q), wordAtLevel_word,
    wordAtLevel_value, toJet_word period _ (by omega : m+n ≤ s)]

/-- The total derivative length in one external/base energy component. -/
def energyLength {N q : ℕ} (I : ExternalWord N) (a : BaseWord q) : ℕ := a.1.val+I.1.val

/-- The literal base-then-external concatenated derivative word of an energy component. -/
def energyWord {N q : ℕ} (I : ExternalWord N) (a : BaseWord q) : Fin (energyLength I a) → Fin 4 :=
  Fin.append a.2 I.2

/-- Every total energy word stays below the advertised external-plus-base cutoff. -/
theorem energyLength_le {s N q : ℕ} (h : N+q ≤ s) (I : ExternalWord N) (a : BaseWord q) :
    energyLength I a ≤ s := by
  have := I.1.isLt
  have := a.1.isLt
  dsimp [energyLength]
  omega

/-- The actual external/base metric-energy coordinate is exactly its concatenated strong derivative. -/
theorem energyValues_eq_word {s : ℕ} (q N : ℕ) (hN : N+q ≤ s)
    (I : ExternalWord N) (a : BaseWord q) (u : SobolevSpace period s) :
    energyValues period q N hN u I a = word period u (energyLength_le hN I a) (energyWord I a) := by
  rw [← energyWordOperator_apply]
  change value period (wordAtLevel period 0 a.1.val a.2 (by have := a.1.isLt; omega)
    (wordAtLevel period q I.1.val I.2 (by have := I.1.isLt; omega) u)) = _
  rw [wordAtLevel_value, toJet_word period _ (by have := a.1.isLt; omega), wordAtLevel_word]
  rfl

/-- The actual continuous energy family used by regularization is exactly the spatial Gevrey energy family. -/
theorem energyValueFamily_eq {s : ℕ} (q N : ℕ) (hN : N+q ≤ s+1) (T : ℝ)
    (u : C(Set.Icc (0 : ℝ) T, SobolevSpace period (s+1)))
    (I : ExternalWord N) (t : Set.Icc (0 : ℝ) T) :
    energyValueFamily period energyLength energyWord (energyLength_le hN) T u I t =
      energyValues period q N hN (u t) I := by
  funext a
  change value period (boundedWordBlock period 0 (energyLength I a) (by have := energyLength_le hN
    I a; omega)
    (energyWord I a) (u t)) = _
  rw [boundedWordBlock_value, energyValues_eq_word]

/-- The H¹ concatenated word is exactly the twice-blocked derivative used by the actual top transport. -/
theorem topTransport_block {s N : ℕ} (hN : N+6 ≤ s) (I : ExternalWord N) (a : BaseWord 6)
    (u : SobolevSpace period (s+1)) :
    boundedWordBlock period 1 (energyLength I a) (by have := energyLength_le hN I a; omega)
      (energyWord I a) u =
      wordAtLevel period 1 a.1.val a.2 (by have := a.1.isLt; omega)
        (wordAtLevel period 7 I.1.val I.2 (by have := I.1.isLt; omega) u) := by
  rw [wordAtLevel_comp, boundedWordBlock_eq_wordAtLevel]
  rfl

end EulerEnergyWordCoordinates
