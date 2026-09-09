/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCoefficientTower
public import LeanPool.NavierStokesAndEuler.Euler.CoefficientPathPressureBounds

@[expose] public section

/-! Quantitative bounds for the actual packet coefficient towers. -/

noncomputable section

namespace EulerPacketCylinderField.MatrixCoefficient

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients EulerCoefficientPath
  EulerJetProductBounds EulerParameterWordGevrey EulerGevrey EulerSobolevGevreyOperators
  EulerCoefficientJetPressureBounds
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {raw : EulerPacketPointJets.Domain → Space →L[ℝ] Space}
  (A : MatrixCoefficient T raw) (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
  (hb : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath A.path) x‖ ≤ C*majorant Rc 0 n)

include hRc hC hb

theorem toCoefficientTower_block_bound (s q n : ℕ) (t : Icc (0 : ℝ) T) :
    EulerH6Pressure.coefficientBlock P ((A.toCoefficientTower P).jet s t) q n ≤
      sobolevCoefficientAmplitude (Fin 4) q Rc C * majorant (sobolevCoefficientRadius (Fin 4) Rc) 0
        n :=
  coefficientJet_block_bound P A.path A.orbit s q Rc C hRc hC hb n t

theorem toCoefficientTower_base_bound (s q r : ℕ) (hr : r ≤ q) (t : Icc (0 : ℝ) T) :
    boundLevel P ((A.toCoefficientTower P).jet s t) r ≤ sobolevCoefficientAmplitude (Fin 4) q Rc C
      :=
  coefficientJet_base_bound P A.path A.orbit Rc C hRc hC hb s q r hr t

theorem toCoefficientTower_normalized_block (s q : ℕ) (R : ℝ)
    (hR : normalizedCoefficientRadius q Rc C ≤ R) (n : ℕ) (hn : 1 ≤ n) (t : Icc (0 : ℝ) T) :
    EulerH6Pressure.coefficientBlock P ((A.toCoefficientTower P).jet s t) q n ≤ R^n*(n.factorial :
      ℝ)^2 :=
  coefficientJet_block_normalized P A.path A.orbit s q Rc C hRc hC hb R hR n hn t

theorem toCoefficientTower_weighted_bound (s q N : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (hsmall : ρ*sobolevCoefficientRadius (Fin 4) Rc ≤ 1/2) (t : Icc (0 : ℝ) T) :
    weightedCoefficient P ((A.toCoefficientTower P).jet s t) q N ρ ≤
      2*sobolevCoefficientAmplitude (Fin 4) q Rc C :=
  coefficientJet_weighted_bound P A.path A.orbit s q N Rc C hRc hC hb ρ hρ hsmall t

theorem toCoefficientTower_pressure_bound (s q b : ℕ) (hq : q ≤ s) (hqb : q ≤ b)
    (c : ℝ) (hc : 0 < c) (t : Icc (0 : ℝ) T) :
    (EulerH6Pressure.CoefficientJet.restrict ((A.toCoefficientTower P).jet s t) q
      hq).pressureConstant c ≤
      pressureCost c (sobolevCoefficientAmplitude (Fin 4) b Rc C) q :=
  coefficientJet_restrictedPressure_bound P A.path A.orbit Rc C hRc hC hb s q b hq hqb c hc t

end EulerPacketCylinderField.MatrixCoefficient
