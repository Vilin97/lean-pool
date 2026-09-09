/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PhysicalChildFields
public import LeanPool.NavierStokesAndEuler.Euler.ChildParticleSourceBound

@[expose] public section

/-! Source (21) for the actual physical graph change of labels. The
arbitrary small frequency losses are absorbed before the child estimate,
and the resulting exponent is exactly 10(s+2). -/

noncomputable section

namespace EulerPhysicalChildFields

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerPacketParentLabelBounds EulerGevrey
  EulerSmoothBanachFlow EulerGraphInvariantFlow EulerMeanClassicalWordBounds
  EulerSobolevSourceExponent
open scoped ContDiff

theorem coarsen_graph_bounds (k ell : ℝ) (hk : 1 ≤ k) (hell : 0 < ell)
    (hi : ell⁻¹ ≤ k^(3/4 : ℝ)) (A B C : SmoothL2Field Space)
    (ha : A.HasJetBound (k^(-(1/2 : ℝ)+1/4)) (ell⁻¹*k^(1+(1/4 : ℝ))))
    (hb : B.HasJetBound (k^(-(1/2 : ℝ)+1/4)) (ell⁻¹*k^(1+(1/4 : ℝ))))
    (hc : C.HasJetBound (k^(1/4 : ℝ)) (ell⁻¹*k^(1+(1/4 : ℝ))))
    (has : HasSupBound A.field (k^(-(1/2 : ℝ)+1/4)) (ell⁻¹*k^(1+(1/4 : ℝ))))
    (hbs : HasSupBound B.field (k^(-(1/2 : ℝ)+1/4)) (ell⁻¹*k^(1+(1/4 : ℝ)))) :
    A.HasJetBound k (k^2) ∧ B.HasJetBound k (k^2) ∧ C.HasJetBound k (k^2) ∧
      HasSupBound A.field k (k^2) ∧ HasSupBound B.field k (k^2) := by
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hsmall : k^(-(1/2 : ℝ)+1/4) ≤ k := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hk
      (by norm_num : -(1/2 : ℝ)+1/4 ≤ 1)
  have hlarge : k^(1/4 : ℝ) ≤ k := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hk (by norm_num : (1/4 : ℝ) ≤
      1)
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
  (k : ℝ) (m : Vector3) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z)=0)
  (ell : ℝ) (hell : 0 < ell)
  (D V W : Icc (0 : ℝ) T → SmoothL2Field Space)
  (K : ℝ) (hK : 1 ≤ K)
  (hD : ∀ t, HasLabelBound K (D t)) (hV : ∀ t, HasLabelBound K (V t)) (hW : ∀ t, HasLabelBound K (W
    t))

include hgraph hK hD hV hW in
theorem exists_source_child_fields (q : ℕ) (hk : 69 ≤ k) (hKk : K ≤ k)
    (hbig : 2+45*embeddingCost ≤ k) (hcost : fixedCost q ≤ k)
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
        t).childDisplacement.translation_contDiff n+
        classicalBlockSize direction q (E t).childVelocity.toLp (E
          t).childVelocity.translation_contDiff n+
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
