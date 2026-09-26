/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.ProtectedEnvelope
public import LeanPool.ScottishBook155.NormedDirectLimit


/-!
# Cardinal bounds for the transfinite construction

The estimates are stated against one ambient infinite cardinal `θ`.  The
successor target is controlled by its explicit dense set of finite linear
combinations, followed by the generic sequence encoding of metric closure.
-/

@[expose] public section

namespace ScottishBook155

universe u

namespace CardinalControl

open scoped DirectSum


/-- The underlying metric adjunction has no more points than the source and
target used to generate it. -/
theorem adjunctionSpace_mk_le
    {M N : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [PseudoMetricSpace N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (θ : Cardinal.{u}) (hθ : Cardinal.aleph0 ≤ θ)
    (hM : Cardinal.mk M ≤ θ) (hN : Cardinal.mk N ≤ θ)
    (hR : Cardinal.lift.{u} (Cardinal.mk ℝ) ≤ θ) :
    Cardinal.mk (AdjunctionSpace V a y H hattach) ≤ θ := by
  have hOneSum : Cardinal.mk (OneSum M) ≤ θ := by
    calc
      Cardinal.mk (OneSum M) = Cardinal.mk (M × ℝ) :=
        Cardinal.mk_congr (WithLp.linearEquiv 1 ℝ (M × ℝ)).toEquiv
      _ = Cardinal.mk M * Cardinal.lift.{u} (Cardinal.mk ℝ) := by
        rw [Cardinal.mk_prod]
        simp
      _ ≤ max (max (Cardinal.mk M)
          (Cardinal.lift.{u} (Cardinal.mk ℝ))) Cardinal.aleph0 :=
        Cardinal.mul_le_max _ _
      _ ≤ θ := max_le (max_le hM hR) hθ
  have hsum : Cardinal.mk (OneSum M ⊕ N) ≤ θ := by
    rw [Cardinal.mk_sum]
    simp only [Cardinal.lift_id]
    exact (Cardinal.add_le_max _ _).trans
      (max_le (max_le hOneSum hN) hθ)
  exact (Cardinal.mk_le_of_surjective Quotient.mk''_surjective).trans hsum

/-- A family whose index and every fiber have size at most `θ` has a sigma
type of size at most `θ`. -/
theorem sigma_mk_le
    {ι : Type u} {G : ι → Type u} (θ : Cardinal.{u})
    (hθ : Cardinal.aleph0 ≤ θ)
    (hι : Cardinal.mk ι ≤ θ) (hG : ∀ i, Cardinal.mk (G i) ≤ θ) :
    Cardinal.mk (Sigma G) ≤ θ := by
  let e : ∀ i, G i ↪ θ.out := fun i =>
    Classical.choice (Cardinal.lift_mk_le'.mp (by
      simpa [Cardinal.mk_out] using hG i))
  let E : Sigma G ↪ ι × θ.out :=
    ⟨fun z => (z.1, e z.1 z.2), by
      rintro ⟨i, x⟩ ⟨j, y⟩ hxy
      have hij : i = j := congrArg Prod.fst hxy
      subst j
      have hv : e i x = e i y := congrArg Prod.snd hxy
      exact Sigma.ext rfl (heq_of_eq ((e i).injective hv))⟩
  calc
    Cardinal.mk (Sigma G) ≤ Cardinal.mk (ι × θ.out) :=
      Cardinal.mk_le_of_injective E.injective
    _ = Cardinal.mk ι * θ := by rw [Cardinal.mk_prod, Cardinal.mk_out]; simp
    _ ≤ max (max (Cardinal.mk ι) θ) Cardinal.aleph0 :=
      Cardinal.mul_le_max _ _
    _ ≤ θ := max_le (max_le hι le_rfl) hθ

/-- The algebraic normed direct limit is no larger than the sigma type of its
components, because every direct-limit point has a one-component
representative. -/
theorem directLimitCarrier_mk_le
    {ι : Type u} [LinearOrder ι] [Nonempty ι]
    (G : ι → Type u)
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →ₗᵢ[ℝ] G j)
    [DirectedSystem G (f · · ·)]
    (θ : Cardinal.{u}) (hθ : Cardinal.aleph0 ≤ θ)
    (hι : Cardinal.mk ι ≤ θ) (hG : ∀ i, Cardinal.mk (G i) ≤ θ) :
    Cardinal.mk (NormedDirectLimit.Carrier G f) ≤ θ := by
  let q : Sigma G → NormedDirectLimit.Carrier G f := fun z =>
    NormedDirectLimit.of G f z.1 z.2
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨i, x, hx⟩ := Module.DirectLimit.exists_of z
    exact ⟨⟨i, x⟩, hx⟩
  exact (Cardinal.mk_le_of_surjective hq).trans
    (sigma_mk_le θ hθ hι hG)

/-- Completing a normed direct limit preserves the bound `θ` whenever `θ` is
closed under countable powers. -/
theorem completedDirectLimit_mk_le
    {ι : Type u} [LinearOrder ι] [Nonempty ι]
    (G : ι → Type u)
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →ₗᵢ[ℝ] G j)
    [DirectedSystem G (f · · ·)]
    (θ : Cardinal.{u}) (hθ : Cardinal.aleph0 ≤ θ)
    (hι : Cardinal.mk ι ≤ θ) (hG : ∀ i, Cardinal.mk (G i) ≤ θ)
    (hpow : θ ^ Cardinal.aleph0 = θ) :
    Cardinal.mk (NormedDirectLimit.CompletedCarrier G f) ≤ θ := by
  let A := NormedDirectLimit.Carrier G f
  have hA : Cardinal.mk A ≤ θ :=
    directLimitCarrier_mk_le G f θ hθ hι hG
  let e : NormedDirectLimit.CompletedCarrier G f ↪ (ℕ → A) :=
    DenseSequenceCardinal.sequenceEmbedding
      ((↑) : A → NormedDirectLimit.CompletedCarrier G f)
      UniformSpace.Completion.denseRange_coe
  calc
    Cardinal.mk (NormedDirectLimit.CompletedCarrier G f) ≤
        Cardinal.mk (ℕ → A) := Cardinal.mk_le_of_injective e.injective
    _ = Cardinal.mk A ^ Cardinal.aleph0 := by
      rw [Cardinal.mk_arrow]
      simp
    _ ≤ θ ^ Cardinal.aleph0 := Cardinal.power_le_power_right hA
    _ = θ := hpow

/-- The protected envelope has cardinality at most `θ` when its two generating
types do and `θ` is closed under countable powers. -/
theorem protectedEnvelope_mk_le
    {P N : Type u} [MetricSpace P] [Nonempty P]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (θ : Cardinal.{u})
    (hθ : Cardinal.aleph0 ≤ θ)
    (hN : Cardinal.mk N ≤ θ) (hP : Cardinal.mk P ≤ θ)
    (hR : Cardinal.lift.{u} (Cardinal.mk ℝ) ≤ θ)
    (hpow : θ ^ Cardinal.aleph0 = θ) :
    Cardinal.mk (ProtectedEnvelope P N j) ≤ θ := by
  let I := N × P
  have hI : Cardinal.mk I ≤ θ := by
    change Cardinal.mk (N × P) ≤ θ
    rw [Cardinal.mk_prod]
    simpa only [Cardinal.lift_id, Cardinal.lift_id'.{0, u}] using
      (Cardinal.mul_le_max (Cardinal.mk N) (Cardinal.mk P)).trans
        (max_le (max_le hN hP) hθ)
  have hIR : Cardinal.mk (I × ℝ) ≤ θ := by
    rw [Cardinal.mk_prod]
    simpa only [Cardinal.lift_id, Cardinal.lift_id'.{0, u}] using
      (Cardinal.mul_le_max (Cardinal.mk I)
        (Cardinal.lift.{u} (Cardinal.mk ℝ))).trans
          (max_le (max_le hI hR) hθ)
  have hfs : Cardinal.mk (I →₀ ℝ) ≤ θ := by
    calc
      Cardinal.mk (I →₀ ℝ) ≤ Cardinal.mk (Finset (I × ℝ)) :=
        Cardinal.mk_le_of_injective (Finsupp.graph_injective I ℝ)
      _ = Cardinal.mk (I × ℝ) := Cardinal.mk_finset_of_infinite _
      _ ≤ θ := hIR
  calc
    Cardinal.mk (ProtectedEnvelope P N j) ≤
        Cardinal.mk (ℕ → (I →₀ ℝ)) :=
      Cardinal.mk_le_of_injective (protectedEnvelopeSequenceEmbedding j).injective
    _ = Cardinal.mk (I →₀ ℝ) ^ Cardinal.aleph0 := by
      rw [Cardinal.mk_arrow]
      simp
    _ ≤ θ ^ Cardinal.aleph0 := Cardinal.power_le_power_right hfs
    _ = θ := hpow

end CardinalControl

end ScottishBook155
