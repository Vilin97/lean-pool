/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieces

@[expose] public section

/-!
Exact finite A/B/C decomposition of the known force.  The only fast products
retained are BA, BC, CA and CC.  This is raw algebra on the actual sliced jets.
-/

noncomputable section

namespace EulerPacketCylinderField

open Set Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion EulerFiniteGrades

theorem sum_knownPiece {E : Type*} [AddCommMonoid E] (f : KnownPiece → E) :
    ∑ k, f k = f .high + f .mean + f .corrector := by
  have hu : (univ : Finset KnownPiece) = {.high, .mean, .corrector} := by decide
  rw [hu]
  simp [add_assoc]

/-- Fifteen named summand kinds before the final new-mean/primary interaction. -/
inductive KnownTerm where
  | previousLinear
  | previousPressure
  | slow (left right : KnownPiece)
  | fastMeanHigh
  | fastMeanCorrector
  | fastCorrectorHigh
  | fastCorrectorCorrector
  deriving DecidableEq, Fintype

theorem card_knownTerm : Fintype.card KnownTerm = 15 := by decide

theorem sum_knownTerm {E : Type*} [AddCommMonoid E] (f : KnownTerm → E) :
    ∑ k, f k = f .previousLinear + f .previousPressure +
      (∑ l : KnownPiece, ∑ r : KnownPiece, f (.slow l r)) +
      f .fastMeanHigh + f .fastMeanCorrector + f .fastCorrectorHigh + f .fastCorrectorCorrector :=
        by
  have hu : (univ : Finset KnownTerm) =
      {.previousLinear, .previousPressure, .slow .high .high, .slow .high .mean,
       .slow .high .corrector, .slow .mean .high, .slow .mean .mean, .slow .mean .corrector,
       .slow .corrector .high, .slow .corrector .mean, .slow .corrector .corrector,
       .fastMeanHigh, .fastMeanCorrector, .fastCorrectorHigh, .fastCorrectorCorrector} := by decide
  rw [hu]
  simp [sum_knownPiece, add_assoc]

namespace KnownTerm

def raw (k : KnownTerm) (O : Operators) (p : ℕ) (a : ℕ → Profile)
    (i j : ℕ) : VectorField := fun z =>
  match k with
  | .previousLinear => if i=0 ∧ j=0 then
      linearPart (O.strain z) (slicedJet O.interval (a (p-1)).corrector z) else 0
  | .previousPressure => if i=0 ∧ j=0 then
      slowPressure (O.inverseFrame z) (pressureJet (a (p-1)).highPressure z) else 0
  | .slow l r => if i+j=p then
      slowAdvection (O.inverseFrame z) (l.jet O p a z i) (r.jet O p a z j) else 0
  | .fastMeanHigh => if i+j=p+1 then
      fastAdvection (O.normal z) (KnownPiece.mean.jet O p a z i) (KnownPiece.high.jet O p a z j)
        else 0
  | .fastMeanCorrector => if i+j=p+1 then
      fastAdvection (O.normal z) (KnownPiece.mean.jet O p a z i) (KnownPiece.corrector.jet O p a z
        j) else 0
  | .fastCorrectorHigh => if i+j=p+1 then
      fastAdvection (O.normal z) (KnownPiece.corrector.jet O p a z i) (KnownPiece.high.jet O p a z
        j) else 0
  | .fastCorrectorCorrector => if i+j=p+1 then
      fastAdvection (O.normal z) (KnownPiece.corrector.jet O p a z i) (KnownPiece.corrector.jet O p
        a z j) else 0

/-- These two families have zero angular mean by periodicity. -/
def zeroMean (k : KnownTerm) : Bool :=
  match k with
  | .fastMeanHigh | .fastMeanCorrector => true
  | _ => false

/-- The pure mean slow product is constant in angle. -/
def meanOnly (k : KnownTerm) : Bool :=
  match k with
  | .slow .mean .mean => true
  | _ => false

end KnownTerm

abbrev KnownTermIndex := KnownTerm × (ℕ × ℕ)

def knownTermIndices (p : ℕ) : Finset KnownTermIndex :=
  Finset.univ.product ((Finset.range (p+2)).product (Finset.range (p+2)))

theorem knownTermIndices_card (p : ℕ) :
    (knownTermIndices p).card = 15*(p+2)^2 := by
  have h₁ := Finset.card_product (Finset.univ : Finset KnownTerm)
    ((Finset.range (p+2)).product (Finset.range (p+2)))
  have h₂ := Finset.card_product (Finset.range (p+2)) (Finset.range (p+2))
  change (knownTermIndices p).card = _ at h₁
  change ((Finset.range (p+2)).product (Finset.range (p+2))).card = _ at h₂
  rw [h₁, h₂, Finset.card_univ, card_knownTerm, Finset.card_range]
  ring

theorem knownTermIndices_card_room (p : ℕ) :
    (knownTermIndices p).card+1 ≤ 100*(p+2)^2 := by
  rw [knownTermIndices_card]
  have hs : 0 < (p+2)^2 := by positivity
  omega

theorem sum_knownTerm_raw (O : Operators) (p : ℕ) (a : ℕ → Profile) (z : Domain) :
    (∑ q ∈ knownTermIndices p, q.1.raw O p a q.2.1 q.2.2 z) =
      linearPart (O.strain z) (slicedJet O.interval (a (p-1)).corrector z) +
      slowPressure (O.inverseFrame z) (pressureJet (a (p-1)).highPressure z) +
      (∑ l : KnownPiece, ∑ r : KnownPiece,
        convolution (p+1) (slowAdvection (O.inverseFrame z))
          (l.jet O p a z) (r.jet O p a z) p) +
      convolution (p+1) (fastAdvection (O.normal z))
        (KnownPiece.mean.jet O p a z) (KnownPiece.high.jet O p a z) (p+1) +
      convolution (p+1) (fastAdvection (O.normal z))
        (KnownPiece.mean.jet O p a z) (KnownPiece.corrector.jet O p a z) (p+1) +
      convolution (p+1) (fastAdvection (O.normal z))
        (KnownPiece.corrector.jet O p a z) (KnownPiece.high.jet O p a z) (p+1) +
      convolution (p+1) (fastAdvection (O.normal z))
        (KnownPiece.corrector.jet O p a z) (KnownPiece.corrector.jet O p a z) (p+1) := by
  simp [knownTermIndices, sum_product, sum_knownTerm, KnownTerm.raw, ite_and, convolution]

private theorem convolution_sum_pieces (M n : ℕ)
    (B : VectorJet →ₗ[ℝ] VectorJet →ₗ[ℝ] Space) (u : KnownPiece → ℕ → VectorJet) :
    convolution M B (fun i => ∑ k, u k i) (fun i => ∑ k, u k i) n =
      ∑ l : KnownPiece, ∑ r : KnownPiece, convolution M B (u l) (u r) n := by
  simp only [sum_knownPiece]
  unfold convolution
  simp only [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  split_ifs <;> simp only [map_add, LinearMap.add_apply, add_zero]
  abel

private theorem fast_pieces_reduced (M n : ℕ) (m : Space)
    (u : KnownPiece → ℕ → VectorJet)
    (ha : ∀ i, inner ℝ m (u .high i).1 = 0)
    (hb : ∀ i, (u .mean i).2 angleDirection = 0) :
    (∑ l : KnownPiece, ∑ r : KnownPiece, convolution M (fastAdvection m) (u l) (u r) n) =
      convolution M (fastAdvection m) (u .mean) (u .high) n +
      convolution M (fastAdvection m) (u .mean) (u .corrector) n +
      convolution M (fastAdvection m) (u .corrector) (u .high) n +
      convolution M (fastAdvection m) (u .corrector) (u .corrector) n := by
  have hl (r : KnownPiece) : convolution M (fastAdvection m) (u .high) (u r) n = 0 := by
    unfold convolution
    apply sum_eq_zero
    intro i _
    apply sum_eq_zero
    intro j _
    simp only [fastAdvection_tangent_left m _ _ (ha i), ite_self]
  have hr (l : KnownPiece) : convolution M (fastAdvection m) (u l) (u .mean) n = 0 := by
    unfold convolution
    apply sum_eq_zero
    intro i _
    apply sum_eq_zero
    intro j _
    simp only [fastAdvection_angleConstant_right m _ _ (hb j), ite_self]
  simp only [sum_knownPiece, hl, hr, zero_add, add_zero]
  abel

/-- Exact raw known force, with all identically zero fast interactions removed. -/
theorem knownForce_eq_term_sum (O : Operators) (p : ℕ) (hp : 2 ≤ p)
    (a : ℕ → Profile) (hc : (a 0).corrector = 0) (hB₁ : (a 1).mean = 0)
    (z : Domain)
    (ha : ∀ i, inner ℝ (O.normal z) (KnownPiece.high.jet O p a z i).1 = 0)
    (hb : ∀ i, (KnownPiece.mean.jet O p a z i).2 angleDirection = 0) :
    knownForce O p a z = -(∑ q ∈ knownTermIndices p, q.1.raw O p a q.2.1 q.2.2 z) := by
  have hu : knownJets O p a z = fun i => ∑ k : KnownPiece, k.jet O p a z i := by
    funext i
    rw [sum_knownPiece]
    exact knownJets_eq_pieces O p hp a hc hB₁ z i
  rw [sum_knownTerm_raw]
  unfold knownForce nonlinearGrade
  rw [hu, convolution_sum_pieces, convolution_sum_pieces,
    fast_pieces_reduced _ _ _ _ ha hb]
  abel

end EulerPacketCylinderField
