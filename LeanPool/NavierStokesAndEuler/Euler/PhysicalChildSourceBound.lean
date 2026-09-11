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
