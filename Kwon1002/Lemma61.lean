import Kwon1002.Section4

/-!
# Lemma 6.1 of v5: the endpoint-controlled continuant recurrence

This file proves `lemma_6_1_endpoint_recurrence`, the first statement of
Section 6 of `manuscript/erdos1002_cauchy_limit_revision_v5.tex` (v5 lines
1050 onward), as it is stated in `Kwon1002/Section6Skeleton.lean`.

## The statement proved, and how it differs from the published wording

v5 line 1063 asks only that the integer sequence be "not identically zero".
Read literally that hypothesis is too weak and the lemma is false as stated:
the recurrence `z_{i+2} = a_{i+1} z_{i+1} + z_i` only constrains the indices
`0 ≤ i ≤ m+1`, so taking `z 0 = z 1 = 0` forces `z i = 0` for every
`i ≤ m+1`, whatever `m` is, while the sequence may be nonzero at some index
beyond `m+1`.  All four endpoint values are then `0`, hence bounded by any
`K ≥ 0`, and the conclusion `m ≤ C log (2K)` fails for large `m`.  The
hypothesis intended by the proof, and the one used here, is that the
solution does not vanish identically on the range the recurrence governs,
`∃ i ≤ m + 1, z i ≠ 0`.  By the recurrence this is equivalent to
`(z 0, z 1) ≠ (0, 0)`.

No hypothesis `K ≥ 1` is needed either: the non-vanishing hypothesis and the
endpoint bounds force `K ≥ 1` (Lemma `hK1` inside the proof).

## The proof

Write `b i = |z i|` and `S i = b i + b (i+1)`.  Call an index `i` *aligned*
if `z i * z (i+1) ≥ 0`.

* Alignment propagates forward, because
  `z_{i+1} z_{i+2} = a_{i+1} z_{i+1}^2 + z_i z_{i+1}`.
* At an aligned index the recurrence adds magnitudes,
  `b (i+2) ≥ b (i+1) + b i`, so `S (i+2) ≥ 2 S i`.
* At a non aligned index the recurrence read backwards,
  `z_i = z_{i+2} - a_{i+1} z_{i+1}`, again adds magnitudes, so
  `b i ≥ b (i+1) + b (i+2)` and `S i ≥ 2 S (i+2)`.

Both doubling steps are instances of one inequality, `abs_add_le_abs_linear`.
Since alignment propagates forward, the range `[0, m]` splits into a non
aligned prefix `[0, t)` and an aligned suffix `[t, m]`, where `t` is the
first aligned index; if no index is aligned the whole range is the prefix.
Then `S 0 ≥ 2^{⌊(t-1)/2⌋}` by the backward doubling along the prefix, and
`S m ≥ 2^{⌊(m-t)/2⌋}` by the forward doubling along the suffix, using that
`S i ≥ 1` for `i ≤ m`, which is exactly the non vanishing of the pair
`(z i, z (i+1))`.  Both `S 0` and `S m` are at most `2K`, so
`m ≤ 2⌊(t-1)/2⌋ + 2⌊(m-t)/2⌋ + 3 ≤ 4 log (2K) / log 2 + 3`, and `K ≥ 1`
absorbs the additive constant.  The constant delivered is `C = 7 / log 2`.

This is the Lame bound of the informal proof, with the two Euclidean runs and
the Fibonacci run replaced by the single quantity `S` and a factor two per
two steps, which is all the exponential growth the conclusion needs.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Kwon1002

noncomputable section

/-- If `u` and `v` have the same sign (`0 ≤ u * v`) and `c ≥ 1`, then the
combination `c * v + u` has magnitude at least `|v| + |u|`.  This is the one
arithmetic step behind both directions of Lemma 6.1: applied to
`(c, v, u) = (a_{i+1}, z_{i+1}, z_i)` it says the recurrence adds magnitudes
at an aligned index, and applied to `(c, v, u) = (a_{i+1}, -z_{i+1}, z_{i+2})`
it says the backward recurrence adds magnitudes at a non aligned index. -/
theorem abs_add_le_abs_linear {c u v : ℤ} (hc : 1 ≤ c) (h : 0 ≤ u * v) :
    |v| + |u| ≤ |c * v + u| := by
  rcases le_or_gt 0 v with hv | hv
  · rcases le_or_gt 0 u with hu | hu
    · have hcv : 0 ≤ c * v := mul_nonneg (by linarith) hv
      rw [abs_of_nonneg hv, abs_of_nonneg hu, abs_of_nonneg (by linarith)]
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ c - 1) hv]
    · have hv0 : v = 0 := by
        rcases hv.lt_or_eq with h' | h'
        · exfalso; nlinarith
        · exact h'.symm
      rw [hv0]
      simp
  · rcases le_or_gt 0 u with hu | hu
    · have hu0 : u = 0 := by
        rcases hu.lt_or_eq with h' | h'
        · exfalso; nlinarith
        · exact h'.symm
      rw [hu0, add_zero, abs_zero, add_zero, abs_mul,
        abs_of_nonneg (by linarith : (0:ℤ) ≤ c)]
      nlinarith [abs_nonneg v]
    · have hc' : (0:ℤ) ≤ c - 1 := by linarith
      have hv' : (0:ℤ) ≤ -v := by linarith
      have hcv : c * v ≤ v := by nlinarith [mul_nonneg hc' hv']
      rw [abs_of_nonpos hv.le, abs_of_nonpos hu.le, abs_of_nonpos (by linarith)]
      linarith

/-- **Lemma 6.1** (v5 lines 1060-1068).  Let `a_i ≥ 1` and let an integer
sequence, not identically zero on `0 ≤ i ≤ m+1`, satisfy
`z_{i+2} = a_{i+1} z_{i+1} + z_i` for `0 ≤ i < m`.  If
`max(|z_0|,|z_1|,|z_m|,|z_{m+1}|) ≤ K` then `m ≤ C log(2K)` for an
absolute constant `C`.

See reading 1 of the module docstring for the non-vanishing hypothesis. -/
theorem lemma_6_1_endpoint_recurrence :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (a : ℕ → ℕ) (z : ℕ → ℤ) (K : ℝ),
        (∀ i, 1 ≤ a i) →
        (∃ i ≤ m + 1, z i ≠ 0) →
        (∀ i < m, z (i + 2) = (a (i + 1) : ℤ) * z (i + 1) + z i) →
        |(z 0 : ℝ)| ≤ K → |(z 1 : ℝ)| ≤ K →
        |(z m : ℝ)| ≤ K → |(z (m + 1) : ℝ)| ≤ K →
        (m : ℝ) ≤ C * Real.log (2 * K) := by
  classical
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨7 / Real.log 2, div_pos (by norm_num) hl2, ?_⟩
  intro m a z K ha hnz hrec h0 h1 hm hm1
  have hac : ∀ i, (0:ℤ) ≤ (a i : ℤ) := fun i => Int.natCast_nonneg _
  have ha1 : ∀ i, (1:ℤ) ≤ (a i : ℤ) := fun i => by exact_mod_cast ha i
  -- Step 1: the pair `(z i, z (i+1))` never vanishes on `0 ≤ i ≤ m`.
  have hpair : ∀ i, i ≤ m → ¬ (z i = 0 ∧ z (i + 1) = 0) := by
    have hbase : ¬ (z 0 = 0 ∧ z 1 = 0) := by
      rintro ⟨e0, e1⟩
      have hzero : ∀ i, i ≤ m → z i = 0 ∧ z (i + 1) = 0 := by
        intro i
        induction i with
        | zero => intro _; exact ⟨e0, e1⟩
        | succ i ih =>
          intro hi
          obtain ⟨u, v⟩ := ih (by omega)
          refine ⟨v, ?_⟩
          have h2 := hrec i (by omega)
          rw [show i + 1 + 1 = i + 2 by omega, h2, u, v]
          ring
      obtain ⟨i, hi, hzi⟩ := hnz
      rcases Nat.lt_or_ge i (m + 1) with h | h
      · exact hzi (hzero i (by omega)).1
      · have him : i = m + 1 := by omega
        subst him
        exact hzi (hzero m le_rfl).2
    intro i
    induction i with
    | zero => intro _; exact hbase
    | succ i ih =>
      intro hi hcon
      obtain ⟨e1, e2⟩ := hcon
      rw [show i + 1 + 1 = i + 2 by omega] at e2
      have h2 := hrec i (by omega)
      rw [e2, e1] at h2
      have hzi : z i = 0 := by linarith
      exact ih (by omega) ⟨hzi, e1⟩
  have hS1 : ∀ i, i ≤ m → (1:ℤ) ≤ |z i| + |z (i + 1)| := by
    intro i hi
    rcases eq_or_ne (z i) 0 with h | h
    · have h' : z (i + 1) ≠ 0 := fun hc => hpair i hi ⟨h, hc⟩
      have hb := Int.one_le_abs h'
      have hb' := abs_nonneg (z i)
      linarith
    · have hb := Int.one_le_abs h
      have hb' := abs_nonneg (z (i + 1))
      linarith
  -- Step 2: the three local moves.
  have hgrow : ∀ i, i < m → 0 ≤ z i * z (i + 1) → |z (i + 1)| + |z i| ≤ |z (i + 2)| := by
    intro i hi hg
    have h := abs_add_le_abs_linear (c := (a (i + 1) : ℤ)) (u := z i) (v := z (i + 1))
      (ha1 _) hg
    rwa [← hrec i hi] at h
  have hprop : ∀ i, i < m → 0 ≤ z i * z (i + 1) → 0 ≤ z (i + 1) * z (i + 2) := by
    intro i hi hg
    rw [hrec i hi]
    nlinarith [mul_nonneg (hac (i + 1)) (mul_self_nonneg (z (i + 1))), hg]
  have hshrink : ∀ i, i < m → z (i + 1) * z (i + 2) < 0 →
      |z (i + 1)| + |z (i + 2)| ≤ |z i| := by
    intro i hi hb
    have h := abs_add_le_abs_linear (c := (a (i + 1) : ℤ)) (u := z (i + 2))
      (v := -z (i + 1)) (ha1 _) (by nlinarith)
    have he : (a (i + 1) : ℤ) * (-z (i + 1)) + z (i + 2) = z i := by
      rw [hrec i hi]; ring
    rw [he, abs_neg] at h
    linarith
  -- Step 3: the two doubling steps.
  have hdblF : ∀ i, i + 2 ≤ m → 0 ≤ z i * z (i + 1) →
      2 * (|z i| + |z (i + 1)|) ≤ |z (i + 2)| + |z (i + 3)| := by
    intro i hi hg
    have g1 : |z (i + 1)| + |z i| ≤ |z (i + 2)| := hgrow i (by omega) hg
    have hg1 : 0 ≤ z (i + 1) * z (i + 1 + 1) := by
      rw [show i + 1 + 1 = i + 2 by omega]; exact hprop i (by omega) hg
    have g2 := hgrow (i + 1) (by omega) hg1
    rw [show i + 1 + 1 = i + 2 by omega, show i + 1 + 2 = i + 3 by omega] at g2
    linarith [abs_nonneg (z (i + 1))]
  have hdblB : ∀ i, i + 2 ≤ m → z (i + 1) * z (i + 2) < 0 → z (i + 2) * z (i + 3) < 0 →
      2 * (|z (i + 2)| + |z (i + 3)|) ≤ |z i| + |z (i + 1)| := by
    intro i hi hb1 hb2
    have s1 : |z (i + 1)| + |z (i + 2)| ≤ |z i| := hshrink i (by omega) hb1
    have hb2' : z (i + 1 + 1) * z (i + 1 + 2) < 0 := by
      rw [show i + 1 + 1 = i + 2 by omega, show i + 1 + 2 = i + 3 by omega]; exact hb2
    have s2 := hshrink (i + 1) (by omega) hb2'
    rw [show i + 1 + 1 = i + 2 by omega, show i + 1 + 2 = i + 3 by omega] at s2
    linarith [abs_nonneg (z (i + 2)), abs_nonneg (z (i + 3))]
  -- Step 4: iterate the doubling steps.
  have hFwd : ∀ k i, i + 2 * k ≤ m → 0 ≤ z i * z (i + 1) →
      2 ^ k * (|z i| + |z (i + 1)|) ≤ |z (i + 2 * k)| + |z (i + 2 * k + 1)| := by
    intro k
    induction k with
    | zero => intro i _ _; simp
    | succ k ih =>
      intro i hle hg
      have hd : 2 * (|z i| + |z (i + 1)|) ≤ |z (i + 2)| + |z (i + 3)| :=
        hdblF i (by omega) hg
      have hg1 : 0 ≤ z (i + 1) * z (i + 1 + 1) := by
        rw [show i + 1 + 1 = i + 2 by omega]; exact hprop i (by omega) hg
      have hg2' := hprop (i + 1) (by omega) hg1
      have hg2 : 0 ≤ z (i + 2) * z (i + 2 + 1) := by
        rw [show i + 2 + 1 = i + 3 by omega]
        rw [show i + 1 + 1 = i + 2 by omega, show i + 1 + 2 = i + 3 by omega] at hg2'
        exact hg2'
      have hIH := ih (i + 2) (by omega) hg2
      rw [show i + 2 + 2 * k = i + 2 * (k + 1) by omega,
        show i + 2 + 1 = i + 3 by omega] at hIH
      have h2k : (0:ℤ) ≤ 2 ^ k := by positivity
      calc 2 ^ (k + 1) * (|z i| + |z (i + 1)|)
          = 2 ^ k * (2 * (|z i| + |z (i + 1)|)) := by ring
        _ ≤ 2 ^ k * (|z (i + 2)| + |z (i + 3)|) := mul_le_mul_of_nonneg_left hd h2k
        _ ≤ |z (i + 2 * (k + 1))| + |z (i + 2 * (k + 1) + 1)| := hIH
  have hBack : ∀ k i, i + 2 * k ≤ m →
      (∀ j, i ≤ j → j ≤ i + 2 * k → z j * z (j + 1) < 0) →
      2 ^ k * (|z (i + 2 * k)| + |z (i + 2 * k + 1)|) ≤ |z i| + |z (i + 1)| := by
    intro k
    induction k with
    | zero => intro i _ _; simp
    | succ k ih =>
      intro i hle hbad
      have hb1 : z (i + 1) * z (i + 2) < 0 := by
        have h := hbad (i + 1) (by omega) (by omega)
        rwa [show i + 1 + 1 = i + 2 by omega] at h
      have hb2 : z (i + 2) * z (i + 3) < 0 := by
        have h := hbad (i + 2) (by omega) (by omega)
        rwa [show i + 2 + 1 = i + 3 by omega] at h
      have hd : 2 * (|z (i + 2)| + |z (i + 3)|) ≤ |z i| + |z (i + 1)| :=
        hdblB i (by omega) hb1 hb2
      have hIH := ih (i + 2) (by omega) (fun j hj1 hj2 => hbad j (by omega) (by omega))
      rw [show i + 2 + 2 * k = i + 2 * (k + 1) by omega,
        show i + 2 + 1 = i + 3 by omega] at hIH
      have h2k : (0:ℤ) ≤ 2 ^ k := by positivity
      calc 2 ^ (k + 1) * (|z (i + 2 * (k + 1))| + |z (i + 2 * (k + 1) + 1)|)
          = 2 * (2 ^ k * (|z (i + 2 * (k + 1))| + |z (i + 2 * (k + 1) + 1)|)) := by ring
        _ ≤ 2 * (|z (i + 2)| + |z (i + 3)|) := by linarith
        _ ≤ |z i| + |z (i + 1)| := hd
  -- Step 5: split the range at the first aligned index.
  obtain ⟨kb, kf, hmk, hb, hf⟩ :
      ∃ kb kf : ℕ, m ≤ 2 * kb + 2 * kf + 3 ∧
        (2:ℤ) ^ kb ≤ |z 0| + |z 1| ∧ (2:ℤ) ^ kf ≤ |z m| + |z (m + 1)| := by
    by_cases hex : ∃ i, i ≤ m ∧ 0 ≤ z i * z (i + 1)
    · have hfm : Nat.find hex ≤ m := (Nat.find_spec hex).1
      obtain ⟨t, htm, htg, hbadlt⟩ :
          ∃ t, t ≤ m ∧ 0 ≤ z t * z (t + 1) ∧ ∀ j, j < t → z j * z (j + 1) < 0 := by
        refine ⟨Nat.find hex, hfm, (Nat.find_spec hex).2, ?_⟩
        intro j hj
        have h := Nat.find_min hex hj
        push_neg at h
        exact h (by omega)
      -- the aligned suffix
      have hgoodup : ∀ d, t + d ≤ m → 0 ≤ z (t + d) * z (t + d + 1) := by
        intro d
        induction d with
        | zero => intro _; simpa using htg
        | succ d ihd =>
          intro hd
          have h := hprop (t + d) (by omega) (ihd (by omega))
          rw [show t + d + 1 = t + (d + 1) by omega,
            show t + d + 2 = t + (d + 1) + 1 by omega] at h
          exact h
      obtain ⟨kf, hkf1, hkf2⟩ : ∃ k : ℕ, t + 2 * k ≤ m ∧ m ≤ t + 2 * k + 1 :=
        ⟨(m - t) / 2, by omega, by omega⟩
      have hmid : (2:ℤ) ^ kf ≤ |z (t + 2 * kf)| + |z (t + 2 * kf + 1)| := by
        have hgf := hFwd kf t hkf1 htg
        have hSt := hS1 t htm
        have h2 := mul_le_mul_of_nonneg_left hSt (show (0:ℤ) ≤ 2 ^ kf by positivity)
        rw [mul_one] at h2
        linarith
      have hfinal : (2:ℤ) ^ kf ≤ |z m| + |z (m + 1)| := by
        rcases (show m = t + 2 * kf ∨ m = t + 2 * kf + 1 by omega) with he | he
        · rw [he]; exact hmid
        · have hg' : 0 ≤ z (t + 2 * kf) * z (t + 2 * kf + 1) := hgoodup (2 * kf) (by omega)
          have hgr := hgrow (t + 2 * kf) (by omega) hg'
          rw [show t + 2 * kf + 2 = t + 2 * kf + 1 + 1 by omega] at hgr
          rw [he]
          have hn := abs_nonneg (z (t + 2 * kf))
          have hn' := abs_nonneg (z (t + 2 * kf + 1))
          linarith
      -- the non aligned prefix
      obtain ⟨kb, hkb1, hkb2⟩ : ∃ kb : ℕ, t ≤ 2 * kb + 2 ∧ (2:ℤ) ^ kb ≤ |z 0| + |z 1| := by
        rcases Nat.eq_zero_or_pos t with ht0 | ht0
        · refine ⟨0, by omega, ?_⟩
          simpa using hS1 0 (Nat.zero_le m)
        · refine ⟨(t - 1) / 2, by omega, ?_⟩
          have hle : 0 + 2 * ((t - 1) / 2) ≤ m := by omega
          have hB := hBack ((t - 1) / 2) 0 hle (fun j _ hj => hbadlt j (by omega))
          have hone := hS1 (0 + 2 * ((t - 1) / 2)) (by omega)
          simp only [Nat.zero_add] at hB hone
          have h2 := mul_le_mul_of_nonneg_left hone
            (show (0:ℤ) ≤ 2 ^ ((t - 1) / 2) by positivity)
          rw [mul_one] at h2
          linarith
      exact ⟨kb, kf, by omega, hkb2, hfinal⟩
    · have hall : ∀ j, j ≤ m → z j * z (j + 1) < 0 := by
        intro j hj
        by_contra hc
        exact hex ⟨j, hj, not_lt.mp hc⟩
      refine ⟨m / 2, 0, by omega, ?_, by simpa using hS1 m le_rfl⟩
      have hle : 0 + 2 * (m / 2) ≤ m := by omega
      have hB := hBack (m / 2) 0 hle (fun j _ hj => hall j (by omega))
      have hone := hS1 (0 + 2 * (m / 2)) (by omega)
      simp only [Nat.zero_add] at hB hone
      have h2 := mul_le_mul_of_nonneg_left hone (show (0:ℤ) ≤ 2 ^ (m / 2) by positivity)
      rw [mul_one] at h2
      linarith
  -- Step 6: pass to the reals and take logarithms.
  have hK1 : (1:ℝ) ≤ K := by
    have h1z : (1:ℤ) ≤ |z 0| ∨ (1:ℤ) ≤ |z 1| := by
      rcases eq_or_ne (z 0) 0 with e | e
      · exact Or.inr (Int.one_le_abs (fun hc => hpair 0 (Nat.zero_le m) ⟨e, hc⟩))
      · exact Or.inl (Int.one_le_abs e)
    rcases h1z with h | h
    · have hc : (1:ℝ) ≤ |(z 0 : ℝ)| := by exact_mod_cast h
      linarith
    · have hc : (1:ℝ) ≤ |(z 1 : ℝ)| := by exact_mod_cast h
      linarith
  have hb' : (2:ℝ) ^ kb ≤ 2 * K := by
    have hcast : ((2:ℤ) ^ kb : ℝ) ≤ ((|z 0| + |z 1| : ℤ) : ℝ) := by exact_mod_cast hb
    push_cast at hcast
    linarith
  have hf' : (2:ℝ) ^ kf ≤ 2 * K := by
    have hcast : ((2:ℤ) ^ kf : ℝ) ≤ ((|z m| + |z (m + 1)| : ℤ) : ℝ) := by exact_mod_cast hf
    push_cast at hcast
    linarith
  have hlog : ∀ k : ℕ, (2:ℝ) ^ k ≤ 2 * K → (k : ℝ) * Real.log 2 ≤ Real.log (2 * K) := by
    intro k hk
    have h2 : (0:ℝ) < (2:ℝ) ^ k := by positivity
    have h := Real.log_le_log h2 hk
    rwa [Real.log_pow] at h
  have hbl := hlog kb hb'
  have hfl := hlog kf hf'
  have hKlog : Real.log 2 ≤ Real.log (2 * K) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hmr : (m : ℝ) ≤ 2 * (kb : ℝ) + 2 * (kf : ℝ) + 3 := by exact_mod_cast hmk
  rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
  have hstep : (m : ℝ) * Real.log 2 ≤ (2 * (kb : ℝ) + 2 * (kf : ℝ) + 3) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hmr hl2.le
  nlinarith [hbl, hfl, hKlog, hstep]

end

end Kwon1002
