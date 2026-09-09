/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownTermFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique

@[expose] public section

/-!
Exact mean and high forcing sums.  Periodic BA/BC terms are absent from the
mean force, and the angle-constant BB term is absent from the high force.
Every summand is the genuine continuous cylinder L² path already constructed.
-/

noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)]

theorem angleMean_congr_at (P : ℝ) (f g : VectorField) (t : ℝ) (x : Space)
    (h : ∀ θ : ℝ, f (t,(x,θ)) = g (t,(x,θ))) (θ : ℝ) :
    angleMean P f (t,(x,θ)) = angleMean P g (t,(x,θ)) := by
  unfold angleMean
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  exact h s

theorem angleMean_neg_finsetSum {ι : Type*} (s : Finset ι) (raw : ι → VectorField)
    (G : ∀ i, Field P T (raw i)) (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    angleMean P (fun z => -(∑ i ∈ s, raw i z)) (t,(x,θ)) =
      -(∑ i ∈ s, angleMean P (raw i) (t,(x,θ))) := by
  unfold angleMean
  rw [intervalIntegral.integral_neg,
    intervalIntegral.integral_finsetSum (fun i _ => ((G i).raw_angle_continuous t
      x).intervalIntegrable 0 P)]
  simp only [smul_neg, Finset.smul_sum]

variable {O : Operators} {p : ℕ} {a : ℕ → Profile}

theorem PrefixFields.knownForce_decomposition (F : PrefixFields P T p a)
    (hp : 2 ≤ p) (hc : (a 0).corrector = 0) (hB₁ : (a 1).mean = 0)
    (hA : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x θ,
      inner ℝ (O.normal (t,(x,θ))) ((a i).high (t,(x,θ))) = 0)
    (hB : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x θ,
      (a i).mean (t,(x,θ)) = (a i).mean (t,(x,0)))
    (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    EulerPacketProfileRecursion.knownForce O p a (t,(x,θ)) =
      -(∑ q ∈ knownTermIndices p, q.1.raw O p a q.2.1 q.2.2 (t,(x,θ))) :=
  knownForce_eq_term_sum O p hp a hc hB₁ (t,(x,θ))
    (fun i => KnownPiece.high_tangent hA i t x θ)
    (fun i => (F.meanPiece_angleIndependent hB i t x).angular θ)

variable (F : PrefixFields P T p a) (C : CoefficientData P T O)
    (hp : 2 ≤ p) (hT : 0 < T) {corrector_t : VectorField}
    (Ct : Field P T corrector_t)
    (hCt : TimeDerivative hT.le (F.corrector (p-1) (by omega)) Ct)
    (pressure : Field P T (pressureGradient (a (p-1)).highPressure))
    (hc : (a 0).corrector = 0) (hB₁ : (a 1).mean = 0)
    (hA : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x θ,
      inner ℝ (O.normal (t,(x,θ))) ((a i).high (t,(x,θ))) = 0)
    (hB : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x θ,
      (a i).mean (t,(x,θ)) = (a i).mean (t,(x,0)))

include C hp hT Ct hCt pressure hc hB₁ hA hB in
theorem PrefixFields.meanForce_decomposition (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    EulerPacketProfileRecursion.meanForce O p a (t,(x,θ)) =
      -(∑ q ∈ knownTermIndices p, q.1.meanRaw O p a q.2.1 q.2.2 (t,(x,θ))) := by
  calc
    _ = angleMean P (fun z => -(∑ q ∈ knownTermIndices p,
        q.1.raw O p a q.2.1 q.2.2 z)) (t,(x,θ)) := by
      unfold EulerPacketProfileRecursion.meanForce
      rw [C.period_eq]
      exact angleMean_congr_at P _ _ t x (F.knownForce_decomposition hp hc hB₁ hA hB t x) θ
    _ = -(∑ q ∈ knownTermIndices p, angleMean P (q.1.raw O p a q.2.1 q.2.2) (t,(x,θ))) :=
      angleMean_neg_finsetSum (knownTermIndices p)
        (fun q => q.1.raw O p a q.2.1 q.2.2)
        (fun q => F.termField C (by omega) hT Ct hCt pressure q.1 q.2.1 q.2.2) t x θ
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro q _
      rw [KnownTerm.meanRaw_eq F C hB, C.period_eq]

include C hp hT Ct hCt pressure hc hB₁ hA hB in
theorem PrefixFields.highForce_decomposition (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    EulerPacketProfileRecursion.highForce O p a (t,(x,θ)) =
      -(∑ q ∈ knownTermIndices p, q.1.highRaw O p a q.2.1 q.2.2 (t,(x,θ))) -
        fastAdvection (O.normal (t,(x,θ)))
          (slicedJet O.interval (meanResult O p a).1 (t,(x,θ)))
          (slicedJet O.interval (a 1).high (t,(x,θ))) := by
  have he : (∑ q ∈ knownTermIndices p, q.1.highRaw O p a q.2.1 q.2.2 (t,(x,θ))) =
      (∑ q ∈ knownTermIndices p, q.1.raw O p a q.2.1 q.2.2 (t,(x,θ))) -
      (∑ q ∈ knownTermIndices p, q.1.meanRaw O p a q.2.1 q.2.2 (t,(x,θ))) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro q _
    rw [KnownTerm.highRaw_eq F C hB, KnownTerm.meanRaw_eq F C hB]
  unfold EulerPacketProfileRecursion.highForce
  rw [F.knownForce_decomposition hp hc hB₁ hA hB,
    F.meanForce_decomposition C hp hT Ct hCt pressure hc hB₁ hA hB, he]
  abel

include hc hB₁ hA hB in
theorem PrefixFields.knownForce_term_path :
    (F.knownForce C (by omega) hT Ct hCt pressure).path =
      -(∑ q ∈ knownTermIndices p, (F.termField C (by omega) hT Ct hCt pressure
        q.1 q.2.1 q.2.2).path) := by
  let G := Field.finsetSum (knownTermIndices p) _
    (fun q => F.termField C (by omega) hT Ct hCt pressure q.1 q.2.1 q.2.2)
  change (F.knownForce C (by omega) hT Ct hCt pressure).path = G.neg.path
  apply Field.path_eq_of_raw_eq
  intro t x θ
  simpa only [Pi.neg_apply, Finset.sum_apply] using
    (F.knownForce_decomposition hp hc hB₁ hA hB t x θ).symm

include hc hB₁ hA hB in
theorem PrefixFields.meanForce_term_path :
    (F.meanForce C (by omega) hT Ct hCt pressure).path =
      -(∑ q ∈ knownTermIndices p, (F.meanTermField C (by omega) hT Ct hCt pressure
        q.1 q.2.1 q.2.2).path) := by
  let G := Field.finsetSum (knownTermIndices p) _
    (fun q => F.meanTermField C (by omega) hT Ct hCt pressure q.1 q.2.1 q.2.2)
  change (F.meanForce C (by omega) hT Ct hCt pressure).path = G.neg.path
  apply Field.path_eq_of_raw_eq
  intro t x θ
  simpa only [Pi.neg_apply, Finset.sum_apply] using
    (F.meanForce_decomposition C hp hT Ct hCt pressure hc hB₁ hA hB t x θ).symm

include hc hB₁ hA hB in
theorem PrefixFields.highForce_term_path (newMean : Field P T (meanResult O p a).1) :
    (F.highForce C hp hT Ct hCt pressure newMean).path =
      -(∑ q ∈ knownTermIndices p, (F.highTermField C (by omega) hT Ct hCt pressure
        q.1 q.2.1 q.2.2).path) -
      (SpatialJetField.fastAdvection C.normal (SpatialJetField.ofField O.interval newMean)
        (SpatialJetField.ofField O.interval (F.high 1 (by omega)))).path := by
  let G := Field.finsetSum (knownTermIndices p) _
    (fun q => F.highTermField C (by omega) hT Ct hCt pressure q.1 q.2.1 q.2.2)
  let A := SpatialJetField.fastAdvection C.normal (SpatialJetField.ofField O.interval newMean)
    (SpatialJetField.ofField O.interval (F.high 1 (by omega)))
  rw [sub_eq_add_neg]
  change (F.highForce C hp hT Ct hCt pressure newMean).path = (G.neg.sub A).path
  apply Field.path_eq_of_raw_eq
  intro t x θ
  simpa only [Pi.sub_apply, Pi.neg_apply, Finset.sum_apply] using
    (F.highForce_decomposition C hp hT Ct hCt pressure hc hB₁ hA hB t x θ).symm

end EulerPacketCylinderField
