/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage8Main.MainExecution
public import LeanPool.ParameterFreeGradient.V7.MainStatement

/-!
The completed runtime satisfies the parameter-free main rate in all exponent regimes.
-/

@[expose] public section

namespace V7.Stage8Main

/-- The universal constant combining initialization, anchor search, and Euclidean trial costs. -/
noncomputable def universalMainConstant : ℝ :=
  1 + O3.anchorLogConstant + euclideanConstant * amortUniversal

theorem universalMainConstant_pos : 0 < universalMainConstant := by
  have hproduct := mul_pos euclideanConstant_pos amortUniversal_pos
  have hanchor := O3.anchorLogConstant_pos
  unfold universalMainConstant
  positivity

theorem universalMainConstant_one : 1 ≤ universalMainConstant := by
  have hproduct := mul_pos euclideanConstant_pos amortUniversal_pos
  have hanchor := O3.anchorLogConstant_pos
  unfold universalMainConstant
  linarith

theorem universalMainConstant_anchor :
    1 + O3.anchorLogConstant ≤ universalMainConstant := by
  have hproduct := mul_pos euclideanConstant_pos amortUniversal_pos
  unfold universalMainConstant
  linarith

/-- The exponent-dependent constant combining anchor and non-Euclidean trial costs. -/
noncomputable def regimeMainConstant (p : ℝ) (hp : 1 < p) : ℝ :=
  if hp2 : p < 2 then
    1 + O3.anchorLogConstant +
      (4 / Real.sqrt (p - 1) + 2) * amortFor p hp
  else if heq : p = 2 then 1
  else
    1 + O3.anchorLogConstant +
      aboveConstant p (lt_of_le_of_ne (le_of_not_gt hp2) (Ne.symm heq)) *
        amortFor p hp

theorem regimeMainConstant_pos (p : ℝ) (hp : 1 < p) :
    0 < regimeMainConstant p hp := by
  by_cases hp2 : p < 2
  · have hsqrt : 0 < Real.sqrt (p - 1) := Real.sqrt_pos.2 (by linarith)
    have hcoeff : 0 < 4 / Real.sqrt (p - 1) + 2 := by positivity
    simp [regimeMainConstant, hp2]
    nlinarith [mul_pos hcoeff (amortFor_pos p hp), O3.anchorLogConstant_pos]
  · by_cases heq : p = 2
    · simp [regimeMainConstant, heq]
    · have habove : 2 < p := lt_of_le_of_ne (le_of_not_gt hp2) (Ne.symm heq)
      have hproduct := mul_pos (aboveConstant_pos p habove) (amortFor_pos p hp)
      simp [regimeMainConstant, hp2, heq]
      nlinarith [hproduct, O3.anchorLogConstant_pos]

theorem regimeMainConstant_one_below (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    1 ≤ regimeMainConstant p hp := by
  have hsqrt : 0 < Real.sqrt (p - 1) := Real.sqrt_pos.2 (by linarith)
  have hcoeff : 0 < 4 / Real.sqrt (p - 1) + 2 := by positivity
  have hproduct := mul_pos hcoeff (amortFor_pos p hp)
  have hanchor := O3.anchorLogConstant_pos
  simp [regimeMainConstant, hp2]
  linarith

theorem regimeMainConstant_anchor_below (p : ℝ) (hp : 1 < p)
    (hp2 : p < 2) :
    1 + O3.anchorLogConstant ≤ regimeMainConstant p hp := by
  have hsqrt : 0 < Real.sqrt (p - 1) := Real.sqrt_pos.2 (by linarith)
  have hcoeff : 0 < 4 / Real.sqrt (p - 1) + 2 := by positivity
  have hproduct := mul_pos hcoeff (amortFor_pos p hp)
  simp [regimeMainConstant, hp2]
  linarith

theorem regimeMainConstant_one_above (p : ℝ) (hp : 1 < p) (hp2 : 2 < p) :
    1 ≤ regimeMainConstant p hp := by
  have hnot : ¬p < 2 := not_lt_of_ge hp2.le
  have hne : p ≠ 2 := ne_of_gt hp2
  have hproduct := mul_pos (aboveConstant_pos p hp2) (amortFor_pos p hp)
  have hanchor := O3.anchorLogConstant_pos
  simp [regimeMainConstant, hnot, hne]
  linarith

theorem regimeMainConstant_anchor_above (p : ℝ) (hp : 1 < p)
    (hp2 : 2 < p) :
    1 + O3.anchorLogConstant ≤ regimeMainConstant p hp := by
  have hnot : ¬p < 2 := not_lt_of_ge hp2.le
  have hne : p ≠ 2 := ne_of_gt hp2
  have hproduct := mul_pos (aboveConstant_pos p hp2) (amortFor_pos p hp)
  simp [regimeMainConstant, hnot, hne]
  linarith

theorem main : V7.MainStatement := by
  refine ⟨currentMethodFamily, universalMainConstant,
    universalMainConstant_pos, ?_⟩
  intro p hp
  by_cases hpBelow : p < 2
  · let Cp := regimeMainConstant p hp
    refine ⟨Cp, regimeMainConstant_pos p hp, ?_⟩
    intro d input hip heps hM0 inst hsec hM0L
    subst p
    have hlocal : ∀ data : RuntimeData d, data.input = input →
        runtimeCoefficient data * selectedAmort data.input.p data.hp ≤ Cp := by
      intro data hdata
      have hpData : data.input.p = input.p := congrArg MethodInput.p hdata
      have hne : input.p ≠ 2 := ne_of_lt hpBelow
      have hprod : 0 ≤ (4 / Real.sqrt (input.p - 1) + 2) *
          amortFor input.p hp := by
        exact (mul_pos (by
          have hs : 0 < Real.sqrt (input.p - 1) := Real.sqrt_pos.2 (by linarith)
          positivity) (amortFor_pos input.p hp)).le
      simp [runtimeCoefficient, selectedAmort, hpData, hpBelow, hne, Cp,
        regimeMainConstant]
      linarith [O3.anchorLogConstant_pos]
    obtain ⟨run, hexec, htrace, hnonempty, hhead, hqueried, hgradient, hbound⟩ :=
      currentExecution input hp heps hM0 inst hsec hM0L Cp
        (regimeMainConstant_one_below input.p hp hpBelow)
        (regimeMainConstant_anchor_below input.p hp hpBelow) hlocal
    refine ⟨run, hexec, htrace, hnonempty, hhead, hqueried, hgradient, ?_⟩
    simpa [CurrentMainRate, hpBelow, Cp,
      V7.Stage2Resume.localCostExponent_eq_half_of_le_two hpBelow.le] using hbound
  · by_cases hpAbove : 2 < p
    · let Cp := regimeMainConstant p hp
      refine ⟨Cp, regimeMainConstant_pos p hp, ?_⟩
      intro d input hip heps hM0 inst hsec hM0L
      subst p
      have hne : input.p ≠ 2 := ne_of_gt hpAbove
      have hlocal : ∀ data : RuntimeData d, data.input = input →
          runtimeCoefficient data * selectedAmort data.input.p data.hp ≤ Cp := by
        intro data hdata
        have hpData : data.input.p = input.p := congrArg MethodInput.p hdata
        have hprod : 0 ≤ aboveConstant input.p hpAbove * amortFor input.p hp :=
          (mul_pos (aboveConstant_pos input.p hpAbove)
            (amortFor_pos input.p hp)).le
        simp [runtimeCoefficient, selectedAmort, hpData, hpBelow, hne, Cp,
          regimeMainConstant]
        linarith [O3.anchorLogConstant_pos]
      obtain ⟨run, hexec, htrace, hnonempty, hhead, hqueried, hgradient, hbound⟩ :=
        currentExecution input hp heps hM0 inst hsec hM0L Cp
          (regimeMainConstant_one_above input.p hp hpAbove)
          (regimeMainConstant_anchor_above input.p hp hpAbove) hlocal
      refine ⟨run, hexec, htrace, hnonempty, hhead, hqueried, hgradient, ?_⟩
      simpa [CurrentMainRate, hpBelow, hne, Cp,
        V7.Stage2Resume.localCostExponent_eq_above hpAbove] using hbound
    · have hpEq : p = 2 := by linarith
      subst p
      refine ⟨1, by norm_num, ?_⟩
      intro d input hip heps hM0 inst hsec hM0L
      rcases input with ⟨pInput, eps, x0, z0, M0⟩
      dsimp only [MethodInput.p, MethodInput.eps, MethodInput.x0,
        MethodInput.z0, MethodInput.M0] at hip heps hM0 inst hsec hM0L ⊢
      subst pInput
      let input : MethodInput d := ⟨2, eps, x0, z0, M0⟩
      have hpInput : 1 < input.p := by norm_num [input]
      have hlocal : ∀ data : RuntimeData d, data.input = input →
          runtimeCoefficient data * selectedAmort data.input.p data.hp ≤
            universalMainConstant := by
        intro data hdata
        have hpData : data.input.p = 2 := by simpa [input] using congrArg MethodInput.p hdata
        simp [runtimeCoefficient, selectedAmort, hpData, universalMainConstant]
        linarith [O3.anchorLogConstant_pos]
      obtain ⟨run, hexec, htrace, hnonempty, hhead, hqueried, hgradient, hbound⟩ :=
        currentExecution input hpInput heps hM0 inst hsec hM0L
          universalMainConstant universalMainConstant_one
          universalMainConstant_anchor hlocal
      refine ⟨run, hexec, htrace, hnonempty, hhead, hqueried, ?_, ?_⟩
      · simpa [input] using hgradient
      · simpa [CurrentMainRate, input,
          V7.Stage2Resume.localCostExponent_eq_half_of_le_two
            (show input.p ≤ 2 by norm_num [input])] using hbound

end V7.Stage8Main

namespace V7

theorem main : V7.MainStatement := Stage8Main.main

end V7
