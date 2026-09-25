/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.TraceCyclic
public import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinIdeal

/-!
# Zero negligibles: nondegeneracy of the trace pairing

The accompanying paper's Lemma 3.6: the trace closure of `x`
against a test fragment differs from the defining connection
pairing only by the fixed
transpose relabeling of the open ends — a bijection on fragments —
so the two test families coincide, and an element all of whose
traces vanish lies in the pairing kernel.
-/

@[expose] public section

namespace RS

/-- The trace of a composition is the connection pairing against
the transposed test fragment: the trace closure is the defining
pairing up to a relabeling. -/
theorem fragTrace_compose_eq_pairing (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {t u : ℕ} (F : Fragment (Fin (t + u)))
    (G : Fragment (Fin (u + t))) :
    fragTrace f (F.compose G) =
      connectionPairing f (t + u) F
        (G.relabel (transposeEquiv u t)) :=
  hf _ _ ((pairCloseComposeRotate F G (strandBundle t)).trans
    (pairCloseCongr (Fragment.Equiv.refl F)
      (composeStrandBundleLeft t u
        (G.relabel (transposeEquiv u t)))))

/-- Every connection row is a family of traces: the row of `x` at
the test fragment `H` is the trace of `x` composed with the
un-transposed `H`. -/
theorem connectionMap_eq_trace_row (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {t u : ℕ} (x : Fragment (Fin (t + u)) →₀ ℂ)
    (H : Fragment (Fin (t + u))) :
    connectionMap f (t + u) x H =
      traceFunctional f t (composeFinsupp t u t x
        (Finsupp.single
          (H.relabel (transposeEquiv u t).symm) 1)) := by
  induction x using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, map_zero, LinearMap.zero_apply, map_zero]
    rfl
  | add y z hy hz =>
    rw [map_add]
    change connectionMap f (t + u) y H +
      connectionMap f (t + u) z H = _
    rw [hy, hz, map_add, LinearMap.add_apply, map_add]
  | single F c =>
    rw [composeFinsupp_single, mul_one, connectionMap_single]
    have h1 : (Finsupp.single
        (F.compose (H.relabel (transposeEquiv u t).symm)) c) =
        c • Finsupp.single
          (F.compose (H.relabel (transposeEquiv u t).symm))
          (1 : ℂ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h1, map_smul, traceFunctional_single, smul_eq_mul,
      fragTrace_compose_eq_pairing f hf]
    have h2 : connectionPairing f (t + u) F
        ((H.relabel (transposeEquiv u t).symm).relabel
          (transposeEquiv u t)) =
        connectionPairing f (t + u) F H :=
      hf _ _ (pairCloseCongr (Fragment.Equiv.refl F)
        ((Fragment.Equiv.relabelTrans H
            (transposeEquiv u t).symm (transposeEquiv u t)).trans
          ((Fragment.Equiv.relabelEq H
              (_root_.Equiv.symm_trans_self
                (transposeEquiv u t))).trans
            (Fragment.Equiv.relabelRefl H))))
    rw [h2]

/-- **Zero negligibles** (accompanying paper, Lemma 3.6): an element
all of whose composition traces vanish lies in the pairing
kernel. -/
theorem mem_ker_of_traces_vanish (f : ClosedFragment → ℂ)
    (hf : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    {t u : ℕ} (x : Fragment (Fin (t + u)) →₀ ℂ)
    (hx : ∀ G : Fragment (Fin (u + t)),
      traceFunctional f t
        (composeFinsupp t u t x (Finsupp.single G 1)) = 0) :
    x ∈ LinearMap.ker (connectionMap f (t + u)) := by
  rw [LinearMap.mem_ker]
  funext H
  rw [connectionMap_eq_trace_row f hf x H, hx]
  rfl

end RS
