/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.Band.Subset
public import LeanPool.ACMax.Counting.V9DischargeSharp

/-!
# The SUM tier-9 kill at the bulk-credited moat (`starved_v9_kill_ahl_sum_sharp`)

`Band.Kill`'s `starved_v9_kill_ahl_sum` fires the moat through `v9_girth`, whose obligation is
`9·L ≤ n + 8`.  With the bulk-credited ledger of `Counting.MoatSharp` the obligation weakens to
`12·L + X ≤ 2n`, so the very same AHL SUM wrapper may be run at the longer girth target

  `L = ⌊(2n − X)/12⌋`   instead of   `L = ⌊(n + 8)/9⌋`.

Everything below is `starved_v9_kill_ahl_sum` verbatim with that one hypothesis swapped and
`v9_girth` replaced by `v9_girth_sharp`.

The EDGE companion (`starved_v9_kill_ahl_edge`) has no sharp counterpart here because it is no
longer needed: at the longer target the SUM disjunct alone covers every cell of the region on
`55 ≤ n ≤ 122` (the EDGE disjunct was load-bearing exactly on `77 ≤ n ≤ 81` at the old target).
-/

@[expose] public section

namespace ACMax

open Finset

open Classical in
/-- **The SUM tier-9 kill, bulk-credited.**  A never-firing starved census (`m = 2(n−2)`,
`δ ≥ 3`, `¬ algConn ≤ 2`) on `48 ≤ n` with the positivity window `hpos` (`X + 3h + 4 ≤ n`) and the
pure-ℕ SUM Moore side condition at `S = V₉`, `t = t₉ = n − 4 − X − 3h`, `ℓ = ⌊L/2⌋`, cannot exist —
now at the bulk-credited moat obligation `12·L + X ≤ 2n` rather than `9·L ≤ n + 8`. -/
theorem starved_v9_kill_ahl_sum_sharp {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hlo : 48 ≤ n) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (hnf : ¬ algConn G ≤ 2)
    (hpos : excessX n G + 3 * (v9Set G)ᶜ.card + 4 ≤ n)
    (L : ℕ) (hL6 : 6 ≤ L) (hLn : 12 * L + excessX n G ≤ 2 * n)
    (hside : (n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card) * ((v9Set G).card - 1)
          * (v9Set G).card ^ (L / 2)
        < ((v9Set G).card + (n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card))
          * (((v9Set G).card + 2 * (n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card)) ^ (L / 2)
            - (v9Set G).card ^ (L / 2))) : False := by
  set t9 : ℕ := n - 4 - excessX n G - 3 * (v9Set G)ᶜ.card with ht9def
  have hRsub : (v9Set G)ᶜ ⊆ Finset.univ.filter (fun w => 5 ≤ G.degree w) := by
    intro v hv
    rw [Finset.mem_compl, mem_v9Set] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
  have hRcard : (v9Set G)ᶜ.card ≤ excessX n G :=
    le_trans (Finset.card_le_card hRsub) (heavy_le_excess G)
  have hexc : 2 * (v9Set G).card + 2 * t9 ≤ v9Pairs G := by
    have hq := v9_density_row_quant G (by omega) hm
    rw [ht9def]
    omega
  have hne : (v9Set G).Nonempty := by
    rw [← Finset.card_pos]
    have hsize := v9_size_row G
    omega
  obtain ⟨k, hk3, hkL, c, hcinj, hadj, hmem⟩ :=
    ahl_ball_girth_subset G (v9Set G) t9 L hne hL6 hexc hside
  have : NeZero k := ⟨by omega⟩
  exact v9_girth_sharp G hm h3 hnf hk3 (by omega) (by omega) c hcinj hadj hmem

end ACMax
