/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ChildParticleFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphFlowBounds
public import LeanPool.NavierStokesAndEuler.Euler.SobolevSourceExponent
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceFrequency
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2GevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.PacketUniformFrequencyMargin
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowCoefficientPaths
import Mathlib.Analysis.Normed.Operator.Prod
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowTimeGevrey
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteFrequencyBounds

/-! Related estimates used together by the same construction modules. -/

section

/-! Source (21) for the actual physical graph change of labels. The
arbitrary small frequency losses are absorbed before the child estimate,
and the resulting exponent is exactly 10(s+2). -/

section

/-! Applying the child composition estimate to the actual physical
graph flow. The input fields are the concrete displacement, velocity and
acceleration constructed from the periodic corrected packet. -/

@[expose] public section

noncomputable section

namespace EulerPhysicalChildFields

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerPacketParentLabelBounds EulerGevrey
  EulerSmoothBanachFlow EulerSmoothFlowGevrey EulerGraphInvariantFlow
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P T)
  (k : ℝ) (m : Vector3) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)
  (ell : ℝ) (hell : 0 < ell)
  (D V W : Icc (0 : ℝ) T → SmoothL2Field Space)
  (K : ℝ) (hK : 1 ≤ K)
  (hD : ∀ t, HasLabelBound K (D t)) (hV : ∀ t, HasLabelBound K (V t)) (hW : ∀ t, HasLabelBound K (W
      t))
  (M R : ℝ) (hM : 1 ≤ M) (hR : 1 ≤ R)
  (hd : ∀ t, (G.displacementField k m ell hell t).HasJetBound M R)
  (hv : ∀ t, (G.velocityField k m ell hell t).HasJetBound M R)
  (hw : ∀ t, (G.accelerationFieldL2 k m ell hell t).HasJetBound M R)
  (hds : ∀ t, HasSupBound (G.displacementField k m ell hell t).field M R)
  (hvs : ∀ t, HasSupBound (G.velocityField k m ell hell t).field M R)

include hgraph in
theorem inner_eq_forward (t : Icc (0 : ℝ) T) :
    (fun x => x+(G.displacementField k m ell hell t).field x) =
      (flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t := by
  funext x
  rw [G.displacementField_eq k m hgraph,displacement_eq]
  abel

/-- Data, bundling `parentDisplacement`, `parentVelocity`, `parentAcceleration`, `K` and the
required compatibility proofs. -/
def data (t : Icc (0 : ℝ) T) : EulerChildParticleFieldBounds.Data where
  parentDisplacement := D t
  parentVelocity := V t
  parentAcceleration := W t
  K := K
  K_one := hK
  parentDisplacement_bound := hD t
  parentVelocity_bound := hV t
  parentAcceleration_bound := hW t
  displacement := G.displacementField k m ell hell t
  velocity := G.velocityField k m ell hell t
  acceleration := G.accelerationFieldL2 k m ell hell t
  amp := M
  rad := R
  amp_one := hM
  rad_one := hR
  displacement_bound := hd t
  velocity_bound := hv t
  acceleration_bound := hw t
  displacement_sup := hds t
  velocity_sup := hvs t
  volume_preserving := by
    rw [inner_eq_forward G k m hgraph ell hell t]
    exact physical_forward_measurePreserving k m T G.time_nonneg G.A hgraph G.divergence ell
        hell.ne' t

include hgraph hK hD hV hW hM hR hd hv hw hds hvs in
theorem data_inner (t : Icc (0 : ℝ) T) :
    (data G k m hgraph ell hell D V W K hK hD hV hW M R hM hR hd hv hw hds hvs t).inner =
      (flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t :=
  inner_eq_forward G k m hgraph ell hell t

omit G k m hgraph ell hell D V W K hK hD hV hW M R hM hR hd hv hw hds hvs in
/-- Child amplitude, given by
`K+M+9*((embeddingCost*K)*K)*M+9*(((embeddingCost*K)*K)*(4*K))*M^2`. -/
def childAmplitude (K M : ℝ) : ℝ :=
  K+M+9*((embeddingCost*K)*K)*M+9*(((embeddingCost*K)*K)*(4*K))*M^2

omit G k m hgraph ell hell D V W K hK hD hV hW M R hM hR hd hv hw hds hvs in
/-- Child radius, given by `(1+R)*((1+M)*(16*K)+2)+R`. -/
def childRadius (K M R : ℝ) : ℝ := (1+R)*((1+M)*(16*K)+2)+R

include hgraph hK hD hV hW hM hR hd hv hw hds hvs in
theorem fields_jet_bound (t : Icc (0 : ℝ) T) :
    let E := data G k m hgraph ell hell D V W K hK hD hV hW M R hM hR hd hv hw hds hvs t
    E.childDisplacement.HasJetBound (childAmplitude K M) (childRadius K M R) ∧
    E.childVelocity.HasJetBound (childAmplitude K M) (childRadius K M R) ∧
    E.childAcceleration.HasJetBound (childAmplitude K M) (childRadius K M R) := by
  let E := data G k m hgraph ell hell D V W K hK hD hV hW M R hM hR hd hv hw hds hvs t
  exact ⟨E.childDisplacement_bound,E.childVelocity_bound,E.childAcceleration_bound⟩

include hgraph hK hD hV hW hM hR hd hv hw hds hvs in
theorem fields_label_bound (J : ℝ)
    (ha : EulerParameterWordGevrey.sobolevCoefficientAmplitude (Fin 3) 6
      (childRadius K M R) (childAmplitude K M) ≤ J)
    (hr : EulerParameterWordGevrey.sobolevCoefficientRadius (Fin 3) (childRadius K M R) ≤ J)
    (t : Icc (0 : ℝ) T) :
    let E := data G k m hgraph ell hell D V W K hK hD hV hW M R hM hR hd hv hw hds hvs t
    HasLabelBound J E.childDisplacement ∧ HasLabelBound J E.childVelocity ∧ HasLabelBound J
        E.childAcceleration :=
  (data G k m hgraph ell hell D V W K hK hD hV hW M R hM hR hd hv hw hds hvs t).child_label_bounds
      J ha hr

end EulerPhysicalChildFields

end
end

end

section

/-! The explicit polynomial losses of child composition fit the
manuscript's C*=10(s+2). This includes the sum of the three actual
physical-label Hs word norms, not just a separate bound for each field. -/

@[expose] public section

noncomputable section

namespace EulerChildParticleFieldBounds.Data

open EulerPacketParentLabelBounds EulerSobolevSourceExponent EulerMeanClassicalWordBounds

variable (G : Data)

theorem amplitude_le_power (k : ℝ) (hk1 : 1 ≤ k)
    (hbig : 2 + 45 * embeddingCost ≤ k) (hK : G.K ≤ k) (hM : G.amp ≤ k) :
    G.amplitude ≤ k^6 := by
  have hk0 : 0 ≤ k := zero_le_one.trans hk1
  have hk15 : k ≤ k^5 := by simpa using pow_le_pow_right₀ hk1 (show 1 ≤ 5 by omega)
  have hk35 : k^3 ≤ k^5 := pow_le_pow_right₀ hk1 (by omega)
  have hprod3 : G.K^2*G.amp ≤ k^3 := by
    have h := mul_le_mul (pow_le_pow_left₀ G.K_nonneg hK 2) hM G.amp_nonneg (pow_nonneg hk0 2)
    exact h.trans_eq (by ring)
  have hprod5 : G.K^3*G.amp^2 ≤ k^5 := by
    have h := mul_le_mul (pow_le_pow_left₀ G.K_nonneg hK 3)
      (pow_le_pow_left₀ G.amp_nonneg hM 2) (sq_nonneg G.amp) (pow_nonneg hk0 3)
    exact h.trans_eq (by ring)
  have h3 : 9*embeddingCost*(G.K^2*G.amp) ≤ 9*embeddingCost*k^5 :=
    mul_le_mul_of_nonneg_left (hprod3.trans hk35) (mul_nonneg (by norm_num) embeddingCost_nonneg)
  have h5 : 36*embeddingCost*(G.K^3*G.amp^2) ≤ 36*embeddingCost*k^5 :=
    mul_le_mul_of_nonneg_left hprod5 (mul_nonneg (by norm_num) embeddingCost_nonneg)
  have hs := add_le_add (add_le_add (add_le_add (hK.trans hk15) (hM.trans hk15)) h3) h5
  have he : G.amplitude = G.K+G.amp+9*embeddingCost*(G.K^2*G.amp) +
      36*embeddingCost*(G.K^3*G.amp^2) := by
    unfold amplitude secondAmplitude firstAmplitude
    ring
  calc
    G.amplitude ≤ (2+45*embeddingCost)*k^5 := by rw [he]; nlinarith [hs]
    _ ≤ k*k^5 := mul_le_mul_of_nonneg_right hbig (pow_nonneg hk0 5)
    _ = k^6 := by ring

theorem radius_le_power (k : ℝ) (hk : 69 ≤ k)
    (hK : G.K ≤ k) (hM : G.amp ≤ k) (hR : G.rad ≤ k ^ 2) : G.radius ≤ k^5 := by
  have hk0 : 0 ≤ k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hk2 : (1 : ℝ) ≤ k^2 := one_le_pow₀ hk1
  have hrad : 1+G.rad ≤ 2*k^2 := by linarith
  have hamp : 1+G.amp ≤ 2*k := by linarith
  have h16 : 16*G.K ≤ 16*k := mul_le_mul_of_nonneg_left hK (by norm_num)
  have hm := mul_le_mul hamp h16 (mul_nonneg (by
      norm_num) G.K_nonneg) (mul_nonneg (by norm_num) hk0)
  have hinner : (1+G.amp)*(16*G.K)+2 ≤ 34*k^2 := by nlinarith [hm]
  have hinner0 : 0 ≤ (1+G.amp)*(16*G.K)+2 := by
    have := G.amp_nonneg
    have := G.K_nonneg
    positivity
  have hprod := mul_le_mul hrad hinner hinner0 (mul_nonneg (by norm_num) (sq_nonneg k))
  have hk24 : k^2 ≤ k^4 := pow_le_pow_right₀ hk1 (by omega)
  have hsum := add_le_add hprod (hR.trans hk24)
  calc
    G.radius ≤ 69*k^4 := by unfold radius compositionRadius; nlinarith [hsum]
    _ ≤ k*k^4 := mul_le_mul_of_nonneg_right hk (pow_nonneg hk0 4)
    _ = k^5 := by ring

theorem source_physical_label_bound (q : ℕ) (k : ℝ) (hk : 69 ≤ k)
    (hbig : 2 + 45 * embeddingCost ≤ k) (hcost : fixedCost q ≤ k)
    (hK : G.K ≤ k) (hM : G.amp ≤ k) (hR : G.rad ≤ k ^ 2) (n : ℕ) :
    classicalBlockSize direction q G.childDisplacement.toLp
        G.childDisplacement.translation_contDiff n +
      classicalBlockSize direction q G.childVelocity.toLp G.childVelocity.translation_contDiff n +
      classicalBlockSize direction q G.childAcceleration.toLp
          G.childAcceleration.translation_contDiff n ≤
        (k^(10*(q+2)))^(n+1)*(n.factorial : ℝ)^2 :=
  source_triple_classical_bound q G.childDisplacement G.childVelocity G.childAcceleration k
      G.amplitude G.radius
    (by linarith) hcost G.amplitude_nonneg G.radius_nonneg
    (G.amplitude_le_power k (by linarith) hbig hK hM) (G.radius_le_power k hk hK hM hR)
    G.childDisplacement_bound G.childVelocity_bound G.childAcceleration_bound n

end EulerChildParticleFieldBounds.Data

end
end

end

@[expose] public section

noncomputable section

namespace EulerPhysicalChildFields

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerPacketParentLabelBounds EulerGevrey
  EulerSmoothBanachFlow EulerGraphInvariantFlow EulerMeanClassicalWordBounds
  EulerSobolevSourceExponent
open scoped ContDiff

theorem coarsen_graph_bounds (k ell : ℝ) (hk : 1 ≤ k) (hell : 0 < ell)
    (hi : ell⁻¹ ≤ k ^ (3 / 4 : ℝ)) (A B C : SmoothL2Field Space)
    (ha : A.HasJetBound (k ^ (-(1 / 2 : ℝ) + 1 / 4)) (ell⁻¹ * k ^ (1 + (1 / 4 : ℝ))))
    (hb : B.HasJetBound (k ^ (-(1 / 2 : ℝ) + 1 / 4)) (ell⁻¹ * k ^ (1 + (1 / 4 : ℝ))))
    (hc : C.HasJetBound (k ^ (1 / 4 : ℝ)) (ell⁻¹ * k ^ (1 + (1 / 4 : ℝ))))
    (has : HasSupBound A.field (k ^ (-(1 / 2 : ℝ) + 1 / 4)) (ell⁻¹ * k ^ (1 + (1 / 4 : ℝ))))
    (hbs : HasSupBound B.field (k ^ (-(1 / 2 : ℝ) + 1 / 4)) (ell⁻¹ * k ^ (1 + (1 / 4 : ℝ)))) :
    A.HasJetBound k (k^2) ∧ B.HasJetBound k (k^2) ∧ C.HasJetBound k (k^2) ∧
      HasSupBound A.field k (k^2) ∧ HasSupBound B.field k (k^2) := by
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hsmall : k^(-(1/2 : ℝ)+1/4) ≤ k := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hk
      (by norm_num : -(1/2 : ℝ)+1/4 ≤ 1)
  have hlarge : k^(1/4 : ℝ) ≤ k := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hk (by
        norm_num : (1/4 : ℝ) ≤ 1)
  have hr : ell⁻¹*k^(1+(1/4 : ℝ)) ≤ k^2 := by
    calc
      _ ≤ k^(3/4 : ℝ)*k^(1+(1/4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hi (Real.rpow_nonneg hk0 _)
      _ = k^2 := by rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hk)]; norm_num
  have hr0 : 0 ≤ ell⁻¹*k^(1+(1/4 : ℝ)) := mul_nonneg (inv_nonneg.mpr hell.le) (Real.rpow_nonneg hk0
      _)
  exact ⟨ha.mono (Real.rpow_nonneg hk0 _) hr0 hsmall hr,
    hb.mono (Real.rpow_nonneg hk0 _) hr0 hsmall hr,
    hc.mono (Real.rpow_nonneg hk0 _) hr0 hlarge hr,
    has.mono (Real.rpow_nonneg hk0 _) hr0 hsmall hr,
    hbs.mono (Real.rpow_nonneg hk0 _) hr0 hsmall hr⟩

variable {P T : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P T)
  (k : ℝ) (m : Vector3) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)
  (ell : ℝ) (hell : 0 < ell)
  (D V W : Icc (0 : ℝ) T → SmoothL2Field Space)
  (K : ℝ) (hK : 1 ≤ K)
  (hD : ∀ t, HasLabelBound K (D t)) (hV : ∀ t, HasLabelBound K (V t)) (hW : ∀ t, HasLabelBound K (W
      t))

include hgraph hK hD hV hW in
theorem exists_source_child_fields (q : ℕ) (hk : 69 ≤ k) (hKk : K ≤ k)
    (hbig : 2 + 45 * embeddingCost ≤ k) (hcost : fixedCost q ≤ k)
    (hb : ∀ t : Icc (0 : ℝ) T,
      (G.displacementField k m ell hell t).HasJetBound k (k^2) ∧
      (G.velocityField k m ell hell t).HasJetBound k (k^2) ∧
      (G.accelerationFieldL2 k m ell hell t).HasJetBound k (k^2) ∧
      HasSupBound (G.displacementField k m ell hell t).field k (k^2) ∧
      HasSupBound (G.velocityField k m ell hell t).field k (k^2)) :
    ∃ E : Icc (0 : ℝ) T → EulerChildParticleFieldBounds.Data,
      (∀ t, (E t).parentDisplacement=D t ∧ (E t).parentVelocity=V t ∧ (E t).parentAcceleration=W t ∧
        (E t).displacement=G.displacementField k m ell hell t ∧
        (E t).velocity=G.velocityField k m ell hell t ∧
        (E t).acceleration=G.accelerationFieldL2 k m ell hell t ∧
        (E t).inner=(flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t) ∧
      (∀ t n, classicalBlockSize direction q (E t).childDisplacement.toLp (E
          t).childDisplacement.translation_contDiff n +
        classicalBlockSize direction q (E t).childVelocity.toLp (E
            t).childVelocity.translation_contDiff n +
        classicalBlockSize direction q (E t).childAcceleration.toLp (E
            t).childAcceleration.translation_contDiff n ≤
          (k^(10*(q+2)))^(n+1)*(n.factorial : ℝ)^2) := by
  have hk1 : 1 ≤ k := by linarith
  let E := data G k m hgraph ell hell D V W K hK hD hV hW k (k^2) hk1 (one_le_pow₀ hk1)
    (fun t => (hb t).1) (fun t => (hb t).2.1) (fun t => (hb t).2.2.1)
    (fun t => (hb t).2.2.2.1) (fun t => (hb t).2.2.2.2)
  refine ⟨E,?_,?_⟩
  · intro t
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,inner_eq_forward G k m hgraph ell hell t⟩
  · intro t n
    exact (E t).source_physical_label_bound q k hk hbig hcost hKk le_rfl le_rfl n

end EulerPhysicalChildFields

end
end

end

section

/-! The quarter-power physical-flow bounds follow from the same tiny-power
source comparison and one parent-independent numerical margin. -/

section

/-! Frequency arithmetic for the genuine graph-flow estimates. Fixed
source constants affect only the frequency threshold. The power losses
can be made arbitrarily small, independently of any truncation order. -/

@[expose] public section

noncomputable section

namespace EulerPacketGraphFlowFrequency

open Filter Real EulerSmoothFlowGevrey

/-- Input exponent, given by `min (ε/6) (1/4)`. -/
def inputExponent (ε : ℝ) : ℝ := min (ε/6) (1/4)

theorem inputExponent_pos (ε : ℝ) (hε : 0 < ε) : 0 < inputExponent ε := by
  unfold inputExponent
  positivity

theorem inputExponent_le_quarter (ε : ℝ) : inputExponent ε ≤ 1/4 := min_le_right _ _

theorem six_inputExponent_le (ε : ℝ) : 6*inputExponent ε ≤ ε := by
  have h := min_le_left (ε/6) (1/4 : ℝ)
  dsimp [inputExponent]
  linarith

private theorem flow_radius_polynomial (B R T w : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hT : 0 ≤ T) (hw : 71 ≤ w)
    (hRw : R ≤ w) (hTw : T ≤ w) (hsmall : B * w ≤ 1) :
    1+flowRadius B R T R ≤ w^3 ∧ 1+flowRadius B R T (6*R) ≤ w^3 := by
  have hw0 : 0 ≤ w := by linarith
  have hBT : B*T ≤ 1 := (mul_le_mul_of_nonneg_left hTw hB).trans hsmall
  have hleft : 4*R+1 ≤ 5*w := by linarith
  have hright : (1+B*T)*(6*R)+2 ≤ 14*w := by
    have h := mul_le_mul_of_nonneg_right (show 1+B*T ≤ 2 by linarith) (by positivity : 0 ≤ 6*R)
    linarith
  have hlarge : flowRadius B R T (6*R) ≤ 70*w^2 := by
    have h := mul_le_mul hleft hright (by
        positivity : 0 ≤ (1+B*T)*(6*R)+2) (by positivity : 0 ≤ 5*w)
    simpa only [flowRadius] using h.trans_eq (by ring)
  have hsmallR : flowRadius B R T R ≤ flowRadius B R T (6*R) := by
    unfold flowRadius
    gcongr
    linarith
  have hsq : 1 ≤ w^2 := by nlinarith
  have h71 : 71*w^2 ≤ w^3 := by
    have h := mul_le_mul_of_nonneg_right hw (sq_nonneg w)
    linarith
  have hb : 1+flowRadius B R T (6*R) ≤ w^3 := by linarith
  exact ⟨(add_le_add le_rfl hsmallR).trans hb,hb⟩

private theorem physical_polynomial_bounds (K B R T C1 k ell w : ℝ)
    (_hK : 0 ≤ K) (hB : 0 ≤ B) (hR : 0 ≤ R) (hT : 0 ≤ T) (hC1 : 0 ≤ C1)
    (hk : 1 ≤ k) (hell : 0 < ell) (hw : 71 ≤ w)
    (hKw : K ≤ w) (hRw : R ≤ w) (hTw : T ≤ w) (hCw : C1 ≤ w)
    (hsmall : B * w ≤ 1) :
    K*(T*B)*(1+flowRadius B R T R) ≤ B*w^5 ∧
    K*B*(1+flowRadius B R T R) ≤ B*w^5 ∧
    K*(C1+3*B^2*R)*(1+flowRadius B R T (6*R)) ≤ w^6 ∧
    ell⁻¹*(4*flowRadius B R T R*(1+k)) ≤ ell⁻¹*k*w^4 ∧
    ell⁻¹*(4*flowRadius B R T (6*R)*(1+k)) ≤ ell⁻¹*k*w^4 := by
  have hw0 : 0 ≤ w := by linarith
  have hB1 : B ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ w by linarith) hB
    linarith
  have hBT : 0 ≤ T*B := mul_nonneg hT hB
  obtain ⟨hv,ha⟩ := flow_radius_polynomial B R T w hB hR hT hw hRw hTw hsmall
  have hVr : 0 ≤ flowRadius B R T R := by unfold flowRadius; positivity
  have hAr : 0 ≤ flowRadius B R T (6*R) := by unfold flowRadius; positivity
  have hd : K*(T*B)*(1+flowRadius B R T R) ≤ B*w^5 := by
    calc
      _ ≤ w*(w*B)*w^3 := by gcongr
      _ = _ := by ring
  have hvb : K*B*(1+flowRadius B R T R) ≤ B*w^5 := by
    calc
      _ ≤ w*B*w^3 := by gcongr
      _ ≤ (w*B*w^3)*w := le_mul_of_one_le_right (by positivity) (by linarith)
      _ = _ := by ring
  have hb2 : B^2 ≤ 1 := by nlinarith
  have hac : C1+3*B^2*R ≤ 4*w := by
    have h := mul_le_mul_of_nonneg_right hb2 hR
    linarith
  have hab : K*(C1+3*B^2*R)*(1+flowRadius B R T (6*R)) ≤ w^6 := by
    calc
      _ ≤ w*(4*w)*w^3 := by gcongr
      _ = 4*w^5 := by ring
      _ ≤ w*w^5 := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hw0 5)
      _ = _ := by ring
  have hradius (r : ℝ) (hr : 0 ≤ r) (hrw : 1+r ≤ w^3) :
      ell⁻¹*(4*r*(1+k)) ≤ ell⁻¹*k*w^4 := by
    have hk0 : 0 ≤ k := by linarith
    have hi : 0 ≤ ell⁻¹ := inv_nonneg.mpr hell.le
    have hrw' : r ≤ w^3 := by linarith
    calc
      _ ≤ ell⁻¹*(4*w^3*(2*k)) := by gcongr; linarith
      _ = ell⁻¹*k*(8*w^3) := by ring
      _ ≤ ell⁻¹*k*(w*w^3) := by gcongr; linarith
      _ = _ := by ring
  exact ⟨hd,hvb,hab,hradius _ hVr hv,hradius _ hAr ha⟩

theorem physical_bounds_of_power (ε η K k B R T C1 ell : ℝ)
    (hη : 0 < η) (_hηq : η ≤ 1 / 4) (hηε : 6 * η ≤ ε)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hR : 0 ≤ R) (hT : 0 ≤ T) (hC1 : 0 ≤ C1)
    (hk : 1 ≤ k) (hell : 0 < ell)
    (hw : 71 ≤ k ^ η) (hKw : K ≤ k ^ η) (hRw : R ≤ k ^ η)
    (hTw : T ≤ k ^ η) (hCw : C1 ≤ k ^ η)
    (hroot : 2 ≤ k ^ (1 / 2 - η)) (hsmall : B ≤ 2 * k ^ (-(1 / 2 : ℝ))) :
    K*(T*B)*(1+flowRadius B R T R) ≤ k^(-(1/2 : ℝ)+ε) ∧
    K*B*(1+flowRadius B R T R) ≤ k^(-(1/2 : ℝ)+ε) ∧
    K*(C1+3*B^2*R)*(1+flowRadius B R T (6*R)) ≤ k^ε ∧
    ell⁻¹*(4*flowRadius B R T R*(1+k)) ≤ ell⁻¹*k^(1+ε) ∧
    ell⁻¹*(4*flowRadius B R T (6*R)*(1+k)) ≤ ell⁻¹*k^(1+ε) := by
  have hk0 : 0 < k := by linarith
  have hw0 : 0 ≤ k^η := Real.rpow_nonneg hk0.le _
  have hBw : B*k^η ≤ 1 := by
    have hp : 0 < k^(1/2-η) := Real.rpow_pos_of_pos hk0 _
    calc
      _ ≤ (2*k^(-(1/2 : ℝ)))*k^η := mul_le_mul_of_nonneg_right hsmall hw0
      _ = 2/k^(1/2-η) := by
        rw [mul_assoc, ← Real.rpow_add hk0]
        have he : -(1/2 : ℝ)+η = -(1/2-η) := by ring
        rw [he, Real.rpow_neg hk0.le]
        ring
      _ ≤ 1 := (div_le_one hp).mpr hroot
  obtain ⟨hd,hv,ha,hr,hr1⟩ := physical_polynomial_bounds K B R T C1 k ell (k^η)
    hK hB hR hT hC1 hk hell hw hKw hRw hTw hCw hBw
  have h6 : (k^η)^6 ≤ k^ε := by
    rw [← Real.rpow_mul_natCast hk0.le]
    exact Real.rpow_le_rpow_of_exponent_le hk (by norm_num; linarith)
  have hdisp : B*(k^η)^5 ≤ k^(-(1/2 : ℝ)+ε) := by
    calc
      _ ≤ (2*k^(-(1/2 : ℝ)))*(k^η)^5 :=
        mul_le_mul_of_nonneg_right hsmall (pow_nonneg hw0 5)
      _ ≤ (k^η*k^(-(1/2 : ℝ)))*(k^η)^5 := by gcongr; linarith
      _ = k^(-(1/2 : ℝ))*(k^η)^6 := by ring
      _ ≤ k^(-(1/2 : ℝ))*k^ε := mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg hk0.le _)
      _ = _ := (Real.rpow_add hk0 _ _).symm
  have hrad : ell⁻¹*k*(k^η)^4 ≤ ell⁻¹*k^(1+ε) := by
    have h4 : (k^η)^4 ≤ k^ε := by
      rw [← Real.rpow_mul_natCast hk0.le]
      exact Real.rpow_le_rpow_of_exponent_le hk (by norm_num; linarith)
    calc
      _ ≤ ell⁻¹*k*k^ε := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = ell⁻¹*(k^(1 : ℝ)*k^ε) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hk0]
  exact ⟨hd.trans hdisp,hv.trans hdisp,ha.trans h6,hr.trans hrad,hr1.trans hrad⟩

theorem physical_bounds_eventually (ε K : ℝ) (hε : 0 < ε) (hK : 0 ≤ K) :
    ∀ᶠ k : ℝ in atTop, ∀ B R T C1 ell : ℝ,
      0 ≤ B → 0 ≤ R → 0 ≤ T → 0 ≤ C1 → 0 < ell →
      R ≤ k^(inputExponent ε) → T ≤ k^(inputExponent ε) → C1 ≤ k^(inputExponent ε) →
      B ≤ 2*k^(-(1/2 : ℝ)) →
      K*(T*B)*(1+flowRadius B R T R) ≤ k^(-(1/2 : ℝ)+ε) ∧
      K*B*(1+flowRadius B R T R) ≤ k^(-(1/2 : ℝ)+ε) ∧
      K*(C1+3*B^2*R)*(1+flowRadius B R T (6*R)) ≤ k^ε ∧
      ell⁻¹*(4*flowRadius B R T R*(1+k)) ≤ ell⁻¹*k^(1+ε) ∧
      ell⁻¹*(4*flowRadius B R T (6*R)*(1+k)) ≤ ell⁻¹*k^(1+ε) := by
  have hη := inputExponent_pos ε hε
  have hηq := inputExponent_le_quarter ε
  have hroot : 0 < 1/2-inputExponent ε := by linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (_root_.tendsto_rpow_atTop hη).eventually_ge_atTop 71,
    (_root_.tendsto_rpow_atTop hη).eventually_ge_atTop K,
    (_root_.tendsto_rpow_atTop hroot).eventually_ge_atTop 2] with k hk hw hKw hr
  intro B R T C1 ell hB hR hT hC1 hell hRw hTw hCw hsmall
  exact physical_bounds_of_power ε (inputExponent ε) K k B R T C1 ell
    hη hηq (six_inputExponent_le ε) hK hB hR hT hC1 hk hell hw hKw hRw hTw hCw hr hsmall

end EulerPacketGraphFlowFrequency

end
end

end

section

/-! Uniform bounds needed for composition with the physical graph flow.
The small lifted displacement controls positive derivatives of the
physical coordinate change without a physical-frequency Grönwall bound. -/

@[expose] public section

noncomputable section

namespace EulerPhysicalGraphFlowBounds.Data

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace EulerSmoothBanachFlow
  EulerSmoothFlowGevrey EulerGraphInvariantFlow EulerPhysicalGraphGevrey
  EulerCylinderGraphGevrey EulerGevrey
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (G : Data P T)

theorem displacement_sup_bound (k : ℝ) (m : Vector3) (ell : ℝ)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (t : Icc (0 : ℝ) T) :
    HasSupBound (G.displacementField k m ell hell t).field (G.B*T)
      (ell⁻¹*(4*G.R*graphFactor k m)) := by
  intro n x
  apply physicalField_sup_bound P _ _ _ k m (T*G.C) G.velocityRadius
    (mul_nonneg G.time_nonneg G.C_nonneg) G.velocityRadius_nonneg _ _ ell hell hell1
    (fst ℝ Vector3 ℝ) (norm_fst_le ..) (G.B*T) (4*G.R)
  intro j z
  have he : (fun y => displacementFamily T G.time_nonneg G.A y t) =
      displacement T G.time_nonneg G.A t := by
    funext y
    simp only [displacement,EulerVolterraConvolution.extendPath,projIcc_of_mem G.time_nonneg
        t.property]
  rw [← he]
  exact displacementFamily_jet_bound T G.time_nonneg G.A G.B G.R G.B_nonneg G.R_pos G.small
    G.sup_bound j t z

theorem velocity_sup_bound (k : ℝ) (m : Vector3) (ell : ℝ)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (t : Icc (0 : ℝ) T) :
    HasSupBound (G.velocityField k m ell hell t).field G.B
      (ell⁻¹*(flowRadius G.B G.R T G.R*graphFactor k m)) := by
  intro n x
  apply physicalField_sup_bound P _ _ _ k m G.C G.velocityRadius
    G.C_nonneg G.velocityRadius_nonneg _ _ ell hell hell1
    (fst ℝ Vector3 ℝ) (norm_fst_le ..) G.B (flowRadius G.B G.R T G.R)
  exact fun j z => materialVelocity_bound T G.time_nonneg G.A G.B G.R
    G.B_nonneg G.R_pos G.small G.sup_bound j t z

variable (k : ℝ) (m : Vector3) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)

include hgraph in
theorem physical_positive_bound (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) T) (n : ℕ) (hn : 0 < n) (x : Vector3) :
    ‖iteratedFDeriv ℝ n ((flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t)
        x‖ ≤
      (1+G.B*T)*(1+ell⁻¹*(4*G.R*graphFactor k m))^n*(n.factorial : ℝ)^2 := by
  have he : (flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t =
      fun y => y+(G.displacementField k m ell hell t).field y := by
    funext y
    rw [G.displacementField_eq k m hgraph,displacement_eq]
    abel
  rw [he]
  exact positive_id_add_bound _ (G.displacementField k m ell hell t).smooth
    (G.B*T) (ell⁻¹*(4*G.R*graphFactor k m)) (mul_nonneg G.B_nonneg G.time_nonneg)
    (mul_nonneg (inv_nonneg.mpr hell.le)
      (mul_nonneg (by linarith [G.R_pos]) (graphFactor_nonneg k m)))
    (G.displacement_sup_bound k m ell hell hell1 t) n hn x

end EulerPhysicalGraphFlowBounds.Data

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketGraphFlowFrequency

open Real EulerSmoothFlowGevrey EulerPacketSourceFrequency

theorem physical_bounds_of_costs (K B R T C1 k ell : ℝ)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hR : 0 ≤ R) (hT : 0 ≤ T) (hC1 : 0 ≤ C1)
    (hk : 1 ≤ k) (hell : 0 < ell)
    (hw : max 71 K ≤ k ^ (1 / 24 : ℝ)) (hroot : 16 ≤ k ^ (1 / 4 : ℝ))
    (hRk : R ≤ smallPower k) (hTk : T ≤ smallPower k) (hCk : C1 ≤ smallPower k)
    (hsmall : B ≤ 2 * k ^ (-(1 / 2 : ℝ))) :
    K*(T*B)*(1+flowRadius B R T R) ≤ k^(-(1/4 : ℝ)) ∧
    K*B*(1+flowRadius B R T R) ≤ k^(-(1/4 : ℝ)) ∧
    K*(C1+3*B^2*R)*(1+flowRadius B R T (6*R)) ≤ k^(1/4 : ℝ) ∧
    ell⁻¹*(4*flowRadius B R T R*(1+k)) ≤ ell⁻¹*k^(5/4 : ℝ) ∧
    ell⁻¹*(4*flowRadius B R T (6*R)*(1+k)) ≤ ell⁻¹*k^(5/4 : ℝ) := by
  have hs := smallPower_le_power k (1/24) hk (by norm_num [theta])
  have hr : 2 ≤ k^(1/2-(1/24 : ℝ)) :=
    (show 2 ≤ k^(1/4 : ℝ) by linarith).trans
      (Real.rpow_le_rpow_of_exponent_le hk (by norm_num))
  simpa only [show -(1/2 : ℝ)+1/4=-(1/4) by norm_num,
    show (1 : ℝ)+1/4=5/4 by norm_num] using
    physical_bounds_of_power (1/4) (1/24) K k B R T C1 ell
      (by norm_num) (by norm_num) (by norm_num) hK hB hR hT hC1 hk hell
      ((le_max_left _ _).trans hw) ((le_max_right _ _).trans hw)
      (hRk.trans hs) (hTk.trans hs) (hCk.trans hs) hr hsmall

end EulerPacketGraphFlowFrequency

namespace EulerPhysicalGraphFlowBounds

open Set Real EulerLiftedGradientSpace EulerSmoothFlowGevrey
  EulerPacketGraphFlowFrequency EulerPacketSourceFrequency EulerCylinderGraphGevrey
  EulerLpTranslation.SmoothL2Field EulerGevrey

variable (P T : ℝ) [Fact (0 < P)]

theorem data_field_bounds_explicit (G : Data P T) (k : ℝ)
    (hC : G.C = G.B) (hS : G.S = G.R) (hS1 : G.S₁ = G.R)
    (hk : 1 ≤ k) (hw : max 71 (Real.sqrt (2 / P + 2 * P)) ≤ k ^ (1 / 24 : ℝ))
    (hroot : 16 ≤ k ^ (1 / 4 : ℝ)) (hB : G.B ≤ 2 * k ^ (-(1 / 2 : ℝ)))
    (hR : G.R ≤ smallPower k) (hC1 : G.C₁ ≤ smallPower k) (hT : T ≤ smallPower k)
    (m : Vector3) (hm : ‖m‖ = 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) T) :
    (G.displacementField k m ell hell t).HasJetBound (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) ∧
    (G.velocityField k m ell hell t).HasJetBound (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) ∧
    (G.accelerationFieldL2 k m ell hell t).HasJetBound (k^(1/4 : ℝ)) (ell⁻¹*k^(5/4 : ℝ)) := by
  have hn := physical_bounds_of_costs (Real.sqrt (2/P+2*P)) G.B G.R T G.C₁ k ell
    (Real.sqrt_nonneg _) G.B_nonneg G.R_pos.le G.time_nonneg G.C₁_nonneg hk hell
    hw hroot hR hT hC1 hB
  have hvr : G.velocityRadius=flowRadius G.B G.R T G.R := by rw [Data.velocityRadius,hS]
  have har : G.accelerationRadius=flowRadius G.B G.R T (6*G.R) := by
    rw [Data.accelerationRadius,hS,hS1]
    congr 1
    ring
  have haa : G.accelerationAmplitude=G.C₁+3*G.B^2*G.R := by rw [Data.accelerationAmplitude,hC]; ring
  have hgf : graphFactor k m=1+k := by
    rw [graphFactor,hm,abs_of_nonneg (zero_le_one.trans hk),mul_one]
  have hv0 := G.velocityRadius_nonneg
  have ha0 := G.accelerationRadius_nonneg
  have hc0 := G.C_nonneg
  have ht0 := G.time_nonneg
  have hac0 := G.accelerationAmplitude_nonneg
  have hg0 := graphFactor_nonneg k m
  refine ⟨?_,?_,?_⟩
  · apply (G.displacementField_bound k m ell hell hell1 t).mono
    · positivity
    · positivity
    · simpa only [hC,hvr] using hn.1
    · simpa only [hvr,hgf] using hn.2.2.2.1
  · apply (G.velocityField_bound k m ell hell hell1 t).mono
    · positivity
    · positivity
    · simpa only [hC,hvr] using hn.2.1
    · simpa only [hvr,hgf] using hn.2.2.2.1
  · apply (G.accelerationField_bound k m ell hell hell1 t).mono
    · positivity
    · positivity
    · simpa only [haa,har] using hn.2.2.1
    · simpa only [har,hgf] using hn.2.2.2.2

theorem data_sup_bounds_explicit (G : Data P T) (k : ℝ)
    (hk : 1 ≤ k) (hw : 71 ≤ k ^ (1 / 24 : ℝ)) (hroot : 16 ≤ k ^ (1 / 4 : ℝ))
    (hB : G.B ≤ 2 * k ^ (-(1 / 2 : ℝ))) (hR : G.R ≤ smallPower k) (hT : T ≤ smallPower k)
    (m : Vector3) (hm : ‖m‖ = 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) T) :
    HasSupBound (G.displacementField k m ell hell t).field (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) ∧
    HasSupBound (G.velocityField k m ell hell t).field (k^(-(1/4 : ℝ))) (ell⁻¹*k^(5/4 : ℝ)) := by
  have hk0 := zero_le_one.trans hk
  have hn := physical_bounds_of_costs 1 G.B G.R T 0 k ell zero_le_one
    G.B_nonneg G.R_pos.le G.time_nonneg le_rfl hk hell
    (by simpa only [max_eq_left (by norm_num : (1 : ℝ) ≤ 71)] using hw)
    hroot hR hT (Real.rpow_nonneg hk0 _) hB
  have hgf : graphFactor k m=1+k := by rw [graphFactor,hm,abs_of_nonneg hk0,mul_one]
  have hB0 := G.B_nonneg
  have hT0 := G.time_nonneg
  have hR0 := G.R_pos.le
  have hf0 : 0 ≤ flowRadius G.B G.R T G.R := by unfold flowRadius; positivity
  have hrad := hn.2.2.2.1
  have hg0 := graphFactor_nonneg k m
  have hdisp : G.B*T ≤ k^(-(1/4 : ℝ)) := by
    apply (show G.B*T ≤ T*G.B*(1+flowRadius G.B G.R T G.R) by
      linarith [mul_nonneg (mul_nonneg hB0 hT0) hf0]).trans
    simpa only [one_mul] using hn.1
  have hvel : G.B ≤ k^(-(1/4 : ℝ)) := by
    apply (show G.B ≤ G.B*(1+flowRadius G.B G.R T G.R) by linarith [mul_nonneg hB0 hf0]).trans
    simpa only [one_mul] using hn.2.1
  have hRflow : G.R ≤ flowRadius G.B G.R T G.R := by
    have hleft : (1 : ℝ) ≤ 4*G.R+1 := by linarith
    have hright : G.R ≤ (1+G.B*T)*G.R+2 := by linarith [mul_nonneg (mul_nonneg hB0 hT0) hR0]
    have h := mul_le_mul hleft hright hR0 (by positivity : 0 ≤ 4*G.R+1)
    simpa only [one_mul,flowRadius] using h
  constructor
  · apply (G.displacement_sup_bound k m ell hell hell1 t).mono (mul_nonneg hB0 hT0) (by
      positivity) hdisp
    rw [hgf]
    apply le_trans _ hrad
    gcongr
  · apply (G.velocity_sup_bound k m ell hell hell1 t).mono hB0 (by positivity) hvel
    rw [hgf]
    apply le_trans _ hrad
    gcongr
    linarith

end EulerPhysicalGraphFlowBounds

end
end

end

section

/-! Fixed smooth matrix coefficients preserve the finite packet's
inverse-frequency normalization with an explicit, frequency-independent
cost. This also applies to the actual inverse-frame time derivative. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.MatrixCoefficient

open EulerSmoothLimit EulerPacketProfileRecursion EulerParameterWordGevrey
  EulerPacketFiniteFrequency EulerMeanCoefficients EulerGevrey
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)]
  {coef : EulerPacketPointJets.Domain → Space →L[ℝ] Space}
  (K : MatrixCoefficient T coef) {raw : VectorField} (G : Field P T raw)

theorem normalized_approximation_bound (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hK : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath K.path) a‖ ≤ C * majorant Rc 0 n)
    {R k B C₁ C₂ : ℝ}
    (hG : G.WordBound 6 R (k⁻¹ * C₁ + (k⁻¹) ^ 2 * C₂ + 2 * B * (k⁻¹ * B) ^ 3) 0)
    (hR : 0 ≤ R) (hKR : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hk : 4 ≤ k) (hB0 : 0 ≤ B) (hB : B ≤ k ^ (1 / 100 : ℝ))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ((K.multiply G).smul k).WordBound 6 R
      ((3*sobolevCoefficientAmplitude (Fin 4) 6 Rc C)*(C₁+C₂+1)) 0 := by
  have hk0 : 0 ≤ k := by linarith
  have hi : 0 ≤ k⁻¹ := inv_nonneg.mpr hk0
  have hA : 0 ≤ k⁻¹*C₁+(k⁻¹)^2*C₂+2*B*(k⁻¹*B)^3 := by positivity
  have h := (hG.multiply K Rc C hRc hC hA hKR hK).smul k
  rw [abs_of_nonneg hk0] at h
  have hc : 0 ≤ 3*sobolevCoefficientAmplitude (Fin 4) 6 Rc C :=
    mul_nonneg (by norm_num) (sobolevCoefficientAmplitude_nonneg 6 Rc C hRc hC)
  have hb4 := fourth_power_le_frequency k B (by linarith) hB0 hB
  have hs := mul_le_mul_of_nonneg_left (normalized_low_high_le k B C₁ C₂ (by linarith) hC₂ hb4) hc
  exact h.mono_amplitude hR (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hs)

end EulerPacketCylinderField.MatrixCoefficient

end
end

end
