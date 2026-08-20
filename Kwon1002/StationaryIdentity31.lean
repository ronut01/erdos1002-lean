import Kwon1002.CarryGraph
import Kwon1002.V5Identity31

/-!
# Identity (31) on the stationary Gauss--torus cocycle

This file transports the algebraic reduction proved in `V5Identity31` from
the one-sided `theta` sequence to the two-sided stationary cocycle.  The
pointwise statement is made on `CarryGraph.GoodT`, where `hatS` and
`hatSinv` are genuine inverses.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Kwon1002
namespace StationaryIdentity31

noncomputable section

/-- Integer powers advance by one application of `hatS` on the good set. -/
lemma hatSzpow_succ {z : NatExtTorus} (hz : z ∈ CarryGraph.GoodT) (t : ℤ) :
    hatSzpow (t + 1) z = hatS (hatSzpow t z) := by
  cases t with
  | ofNat n =>
      change hatSzpow ((n : ℤ) + 1) z = hatS (hatSzpow (n : ℤ) z)
      have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.ofNat_zero_le n
      have hn1 : (0 : ℤ) ≤ (n : ℤ) + 1 := by linarith
      rw [hatSzpow, if_pos hn1, hatSzpow, if_pos hn0]
      norm_num
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  | negSucc n =>
      cases n with
      | zero => simpa [hatSzpow] using (CarryGraph.hatS_hatSinv hz).symm
      | succ k =>
          have hcancel := CarryGraph.hatS_iterate_hatSinv_iterate hz 1 (k + 2)
            (by omega : 1 ≤ k + 2)
          simp only [Function.iterate_one] at hcancel
          simpa [hatSzpow] using hcancel.symm

/-- The first torus coordinate at time `t` is the second coordinate at
time `t-1`. -/
lemma hatSzpow_fst_torus {z : NatExtTorus} (hz : z ∈ CarryGraph.GoodT) (t : ℤ) :
    (hatSzpow t z).2.1 = (hatSzpow (t - 1) z).2.2 := by
  have h := congrArg (fun q : NatExtTorus => q.2.1) (hatSzpow_succ hz (t - 1))
  simpa using h

/-- The stationary torus coordinates satisfy the continued-fraction
recursion, modulo the integer removed by `Int.fract`. -/
lemma stationary_theta_succ {z : NatExtTorus} (hz : z ∈ CarryGraph.GoodT) (t : ℤ) :
    ∃ m : ℤ,
      (hatSzpow (t + 1) z).2.2
        = (hatSzpow (t - 1) z).2.2
          - (digit (hatSzpow t z).1.1 0 : ℝ) * (hatSzpow t z).2.2 + (m : ℝ) := by
  have hs := hatSzpow_succ hz t
  have hp := hatSzpow_fst_torus hz t
  refine ⟨-⌊(hatSzpow t z).2.1
      - (digit (hatSzpow t z).1.1 0 : ℝ) * (hatSzpow t z).2.2⌋, ?_⟩
  rw [hs]
  change Int.fract ((hatSzpow t z).2.1
      - (digit (hatSzpow t z).1.1 0 : ℝ) * (hatSzpow t z).2.2) = _
  rw [Int.fract, hp]
  push_cast
  ring

/-! ## The digit word carried by a two-sided orbit -/

/-- The past coordinate of the natural extension advances under
`natExtInv` by the Gauss map. -/
lemma natExtInv_iterate_snd (m : ℕ) (p : ℝ × ℝ) :
    (natExtInv^[m] p).2 = gaussIter p.2 m := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, ih, natExtInv]
      simp [gaussIter, Function.iterate_succ_apply]

/-- The leading digit after `d+1` backward steps is the `d`-th digit of
the original past coordinate. -/
lemma digit_natExtInv_iterate_fst {p : ℝ × ℝ} (hp : p ∈ natExtGood) (d : ℕ) :
    digit ((natExtInv^[d + 1] p).1) 0 = digit p.2 d := by
  rw [show d + 1 = Nat.succ d by omega, Function.iterate_succ_apply']
  have hgood := natExtInv_iterate_mem_good hp d
  change digit (((digit (natExtInv^[d] p).2 0 : ℕ) : ℝ)
      + (natExtInv^[d] p).1)⁻¹ 0 = _
  rw [digit_inv_natCast_add (Ioo_subset_Ico_self hgood.1), natExtInv_iterate_snd]
  simp [digit]

/-- The finite natural-extension word is exactly the block of leading
digits along the two-sided orbit, with offsets `-R, ..., R-1`. -/
lemma wordFn_natExtWord {z : NatExtTorus} (hz : z ∈ CarryGraph.GoodT)
    (R t : ℕ) (ht : t < 2 * R) :
    wordFn R (natExtWord R z.1) t
      = digit (hatSzpow ((t : ℤ) - (R : ℤ)) z).1.1 0 := by
  have hb : z.1 ∈ natExtGood := hz.1
  by_cases htr : t < R
  · have hd : 1 ≤ R - t := by omega
    rw [wordFn, dif_pos ht, natExtWord, if_pos (by simpa using htr)]
    have hoff : (t : ℤ) - (R : ℤ) = -((R - t : ℕ) : ℤ) := by omega
    rw [hoff, hatSzpow, if_neg (by omega)]
    have hto : (-(-((R - t : ℕ) : ℤ))).toNat = R - t := by omega
    rw [hto, Lemma62.hatSinv_iterate_fst,
      show R - t = (R - 1 - t) + 1 by omega,
      digit_natExtInv_iterate_fst hb]
  · have hnonneg : (0 : ℤ) ≤ (t : ℤ) - (R : ℤ) := by omega
    rw [wordFn, dif_pos ht, natExtWord, if_neg (by simpa using htr),
      hatSzpow, if_pos hnonneg]
    have hto : ((t : ℤ) - (R : ℤ)).toNat = t - R := by omega
    rw [hto, Lemma62.hatS_iterate_fst, Lemma62.natExtMap_iterate_fst]
    simp [digit]

/-! ## The coefficient recursions on the stationary cocycle -/

/-- Forward reduction of the stationary torus coordinate to the central
pair at times `0` and `-1`. -/
lemma up_stationary {z : NatExtTorus} (hz : z ∈ CarryGraph.GoodT) (R : ℕ)
    (v : ℕ → ℕ)
    (hv : ∀ t, t < 2 * R →
      v t = digit (hatSzpow ((t : ℤ) - (R : ℤ)) z).1.1 0) :
    ∀ t, t ≤ R → ∃ m : ℤ,
      (hatSzpow (t : ℤ) z).2.2
        = ((upC R v t).1 : ℝ) * z.2.2
          + ((upC R v t).2 : ℝ) * (hatSzpow (-1) z).2.2 + (m : ℝ) := by
  have key : ∀ t : ℕ,
      (t ≤ R → ∃ m : ℤ,
        (hatSzpow (t : ℤ) z).2.2
          = ((upC R v t).1 : ℝ) * z.2.2
            + ((upC R v t).2 : ℝ) * (hatSzpow (-1) z).2.2 + (m : ℝ)) ∧
      (t + 1 ≤ R → ∃ m : ℤ,
        (hatSzpow ((t + 1 : ℕ) : ℤ) z).2.2
          = ((upC R v (t + 1)).1 : ℝ) * z.2.2
            + ((upC R v (t + 1)).2 : ℝ) * (hatSzpow (-1) z).2.2 + (m : ℝ)) := by
    intro t
    induction t with
    | zero =>
      constructor
      · intro _
        refine ⟨0, ?_⟩
        simp [hatSzpow, upC]
      · intro ht
        obtain ⟨m, hm⟩ := stationary_theta_succ hz 0
        have hvR : v R = digit z.1.1 0 := by
          rw [hv R (by omega)]
          simp [hatSzpow]
        have hm' := hm
        have hzero : hatSzpow 0 z = z := by simp [hatSzpow]
        rw [hzero, ← hvR] at hm'
        refine ⟨m, ?_⟩
        rw [show ((0 + 1 : ℕ) : ℤ) = (1 : ℤ) by norm_num,
          show (1 : ℤ) = 0 + 1 by norm_num, hm']
        simp [hatSzpow, upC]
        ring
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      intro hR
      obtain ⟨m1, hm1⟩ := ih.1 (by omega)
      obtain ⟨m2, hm2⟩ := ih.2 (by omega)
      obtain ⟨m0, hm0⟩ := stationary_theta_succ hz ((t : ℤ) + 1)
      have hvIdx : v (R + t + 1)
          = digit (hatSzpow ((t : ℤ) + 1) z).1.1 0 := by
        rw [hv (R + t + 1) (by omega)]
        have hoff : (((R + t + 1 : ℕ) : ℤ) - (R : ℤ)) = (t : ℤ) + 1 := by omega
        rw [hoff]
      have hc : upC R v (t + 1 + 1)
          = ((upC R v t).1 - (v (R + t + 1) : ℤ) * (upC R v (t + 1)).1,
             (upC R v t).2 - (v (R + t + 1) : ℤ) * (upC R v (t + 1)).2) := rfl
      refine ⟨m1 - (v (R + t + 1) : ℤ) * m2 + m0, ?_⟩
      rw [← hvIdx] at hm0
      have htminus : (t : ℤ) + 1 - 1 = (t : ℤ) := by omega
      rw [htminus] at hm0
      have hm2' : (hatSzpow ((t : ℤ) + 1) z).2.2
          = ((upC R v (t + 1)).1 : ℝ) * z.2.2
            + ((upC R v (t + 1)).2 : ℝ) * (hatSzpow (-1) z).2.2 + (m2 : ℝ) := by
        simpa using hm2
      rw [show ((t + 1 + 1 : ℕ) : ℤ) = (t : ℤ) + 1 + 1 by omega,
        hm0, hm1, hm2', hc]
      push_cast
      ring
  exact fun t ht => (key t).1 ht

/-- Backward reduction, including the extra depth `R+1` required by the
v9 range `-R-1, ..., R`. -/
lemma down_stationary {z : NatExtTorus} (hz : z ∈ CarryGraph.GoodT) (R : ℕ)
    (v : ℕ → ℕ)
    (hv : ∀ t, t < 2 * R →
      v t = digit (hatSzpow ((t : ℤ) - (R : ℤ)) z).1.1 0) :
    ∀ d, d ≤ R + 1 → ∃ m : ℤ,
      (hatSzpow (-(d : ℤ)) z).2.2
        = ((downC R v d).1 : ℝ) * z.2.2
          + ((downC R v d).2 : ℝ) * (hatSzpow (-1) z).2.2 + (m : ℝ) := by
  have key : ∀ d : ℕ,
      (d ≤ R + 1 → ∃ m : ℤ,
        (hatSzpow (-(d : ℤ)) z).2.2
          = ((downC R v d).1 : ℝ) * z.2.2
            + ((downC R v d).2 : ℝ) * (hatSzpow (-1) z).2.2 + (m : ℝ)) ∧
      (d + 1 ≤ R + 1 → ∃ m : ℤ,
        (hatSzpow (-((d + 1 : ℕ) : ℤ)) z).2.2
          = ((downC R v (d + 1)).1 : ℝ) * z.2.2
            + ((downC R v (d + 1)).2 : ℝ) * (hatSzpow (-1) z).2.2 + (m : ℝ)) := by
    intro d
    induction d with
    | zero =>
      constructor
      · intro _
        refine ⟨0, ?_⟩
        simp [hatSzpow, downC]
      · intro _
        refine ⟨0, ?_⟩
        simp [downC]
    | succ d ih =>
      refine ⟨ih.2, ?_⟩
      intro hR
      obtain ⟨m1, hm1⟩ := ih.1 (by omega)
      obtain ⟨m2, hm2⟩ := ih.2 (by omega)
      obtain ⟨m0, hm0⟩ := stationary_theta_succ hz (-((d : ℤ) + 1))
      have hvIdx : v (R - d - 1)
          = digit (hatSzpow (-((d : ℤ) + 1)) z).1.1 0 := by
        rw [hv (R - d - 1) (by omega)]
        have hoff : (((R - d - 1 : ℕ) : ℤ) - (R : ℤ)) = -((d : ℤ) + 1) := by omega
        rw [hoff]
      have hc : downC R v (d + 1 + 1)
          = ((downC R v d).1 + (v (R - d - 1) : ℤ) * (downC R v (d + 1)).1,
             (downC R v d).2 + (v (R - d - 1) : ℤ) * (downC R v (d + 1)).2) := rfl
      refine ⟨m1 + (v (R - d - 1) : ℤ) * m2 - m0, ?_⟩
      rw [← hvIdx] at hm0
      have hplus : -((d : ℤ) + 1) + 1 = -(d : ℤ) := by omega
      have hminus : -((d : ℤ) + 1) - 1 = -((d : ℤ) + 2) := by omega
      rw [hplus, hminus] at hm0
      have hm2' : (hatSzpow (-((d : ℤ) + 1)) z).2.2
          = ((downC R v (d + 1)).1 : ℝ) * z.2.2
            + ((downC R v (d + 1)).2 : ℝ) * (hatSzpow (-1) z).2.2 + (m2 : ℝ) := by
        simpa using hm2
      have hstep : (hatSzpow (-((d : ℤ) + 2)) z).2.2
          = (hatSzpow (-(d : ℤ)) z).2.2
            + (v (R - d - 1) : ℝ) * (hatSzpow (-((d : ℤ) + 1)) z).2.2
            - (m0 : ℝ) := by
        rw [hm0]
        ring
      rw [show -((d + 1 + 1 : ℕ) : ℤ) = -((d : ℤ) + 2) by omega,
        hstep, hm1, hm2', hc]
      push_cast
      ring
  exact fun d hd => (key d).1 hd

/-! ## Stationary identity (31) -/

/-- The additive, modulo-an-integer form of identity (31) on a stationary
two-sided orbit.  The coefficient functions are exactly the manuscript-v9
`winA1` and `winB1`, evaluated on `natExtWord R z.1`. -/
theorem stationary_character_reduction_mod (R : ℕ)
    (c : Fin (2 * R + 2) → ℤ) {z : NatExtTorus}
    (hz : z ∈ CarryGraph.GoodT) :
    ∃ m : ℤ,
      (∑ i : Fin (2 * R + 2), (c i : ℝ) *
          (hatSzpow ((i : ℤ) - (R : ℤ) - 1) z).2.2)
        = (V5Identity31.winA1 R c (natExtWord R z.1) : ℝ) * z.2.2
          + (V5Identity31.winB1 R c (natExtWord R z.1) : ℝ) *
              (hatSzpow (-1) z).2.2 + (m : ℝ) := by
  let v := wordFn R (natExtWord R z.1)
  have hv : ∀ t, t < 2 * R →
      v t = digit (hatSzpow ((t : ℤ) - (R : ℤ)) z).1.1 0 :=
    fun t ht => wordFn_natExtWord hz R t ht
  have hterm : ∀ i : Fin (2 * R + 2), ∃ m : ℤ,
      (hatSzpow ((i : ℤ) - (R : ℤ) - 1) z).2.2
        = ((V5Identity31.winC1 R v (i : ℕ)).1 : ℝ) * z.2.2
          + ((V5Identity31.winC1 R v (i : ℕ)).2 : ℝ) *
              (hatSzpow (-1) z).2.2 + (m : ℝ) := by
    intro i
    have hi := i.isLt
    by_cases h : R + 1 ≤ (i : ℕ)
    · obtain ⟨m, hm⟩ := up_stationary hz R v hv ((i : ℕ) - (R + 1)) (by omega)
      refine ⟨m, ?_⟩
      rw [show (i : ℤ) - (R : ℤ) - 1 = (((i : ℕ) - (R + 1) : ℕ) : ℤ) by omega,
        hm, V5Identity31.winC1, if_pos h]
    · obtain ⟨m, hm⟩ := down_stationary hz R v hv (R + 1 - (i : ℕ)) (by omega)
      refine ⟨m, ?_⟩
      rw [show (i : ℤ) - (R : ℤ) - 1 = -((R + 1 - (i : ℕ) : ℕ) : ℤ) by omega,
        hm, V5Identity31.winC1, if_neg h]
  choose m hm using hterm
  refine ⟨∑ i : Fin (2 * R + 2), c i * m i, ?_⟩
  calc
    (∑ i : Fin (2 * R + 2), (c i : ℝ) *
        (hatSzpow ((i : ℤ) - (R : ℤ) - 1) z).2.2)
        = ∑ i : Fin (2 * R + 2),
            ((c i : ℝ) * ((V5Identity31.winC1 R v (i : ℕ)).1 : ℝ) * z.2.2
              + (c i : ℝ) * ((V5Identity31.winC1 R v (i : ℕ)).2 : ℝ) *
                  (hatSzpow (-1) z).2.2
              + (c i : ℝ) * (m i : ℝ)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hm i]
          ring
    _ = (V5Identity31.winA1 R c (natExtWord R z.1) : ℝ) * z.2.2
          + (V5Identity31.winB1 R c (natExtWord R z.1) : ℝ) *
              (hatSzpow (-1) z).2.2
          + ((∑ i : Fin (2 * R + 2), c i * m i : ℤ) : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.sum_mul]
        simp only [V5Identity31.winA1, V5Identity31.winB1, v]
        push_cast
        ring

/-- Character-valued identity (31).  In the `(r,s)` convention used by
`WindowSymbol`, the central modes are `(B_w,A_w)`, hence the displayed
order `B_w θ_{-1} + A_w θ_0`. -/
theorem stationary_character_reduction (R : ℕ)
    (c : Fin (2 * R + 2) → ℤ) {z : NatExtTorus}
    (hz : z ∈ CarryGraph.GoodT) :
    torusChar (∑ i : Fin (2 * R + 2), (c i : ℝ) *
        (hatSzpow ((i : ℤ) - (R : ℤ) - 1) z).2.2)
      = torusChar
          ((V5Identity31.winB1 R c (natExtWord R z.1) : ℝ) *
              (hatSzpow (-1) z).2.2
            + (V5Identity31.winA1 R c (natExtWord R z.1) : ℝ) * z.2.2) := by
  obtain ⟨m, hm⟩ := stationary_character_reduction_mod R c hz
  rw [hm]
  have hreorder :
      (V5Identity31.winA1 R c (natExtWord R z.1) : ℝ) * z.2.2
          + (V5Identity31.winB1 R c (natExtWord R z.1) : ℝ) *
              (hatSzpow (-1) z).2.2 + (m : ℝ)
        = (V5Identity31.winB1 R c (natExtWord R z.1) : ℝ) *
              (hatSzpow (-1) z).2.2
          + (V5Identity31.winA1 R c (natExtWord R z.1) : ℝ) * z.2.2
          + (m : ℝ) := by ring
  rw [hreorder, torusChar_add_int]

end

end StationaryIdentity31
end Kwon1002
