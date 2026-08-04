/-
Scratch file (BV agent, ATTACK (a), DIRECT).

Target: a **Lasota-Yorke inequality for the Gauss transfer operator on
functions of bounded variation**, the missing ingredient gating Kwon §4
(§4's observables are digit indicators: `BV`, provably *not* Lipschitz, so
Wang's Lipschitz contraction `gaussTransfer_strict_lipschitz_contraction`
cannot see them).

The inequality proved here is

    eVariationOn (gaussTransfer f) [0,1]
      ≤ (3/4) * eVariationOn f [0,1]  +  ∫_0^1 |f| dLebesgue.

Both constants are explicit and the contraction factor is `3/4 < 1`, so
iterating gives `Var(L^n f) ≤ (3/4)^n Var f + 4‖f‖₁`, which is exactly the
Lasota-Yorke form.

API choice: Mathlib's `eVariationOn : (α → E) → Set α → ℝ≥0∞`
(`Mathlib/Topology/EMetricSpace/BoundedVariation.lean`).  It is the only
variation API Mathlib has, and it is the one Kwon's `BV(0,1)` class is
already encoded with in this tree (`Kwon1002.Prop41`, and
`Kwon1002.TransferIdentity.BVBoundedBy'`).  Working in `ℝ≥0∞` also means no
side condition is needed for the statement to typecheck when the variation
is infinite (the inequality is then vacuously true, as it should be).

Mathlib has *no* algebraic lemmas for `eVariationOn` (no subadditivity in
the function argument, no product rule, no quantitative Lipschitz bound);
Part 1 below supplies them.
-/
import Erdos1002.GaussTransferContraction
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace Kwon1002.BVLasotaYorke

open Erdos1002

noncomputable section

/-! ## Part 1.  An `eVariationOn` toolkit

None of these five statements exists in Mathlib. -/

/-- Variation is subadditive in the function argument. -/
theorem eVariationOn_add_le (f g : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  refine iSup_le ?_
  rintro ⟨n, ⟨u, hu, us⟩⟩
  have key : ∀ i : ℕ, edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))
      ≤ edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i)) := by
    intro i
    simp only [edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc |f (u (i + 1)) + g (u (i + 1)) - (f (u i) + g (u i))|
        = |(f (u (i + 1)) - f (u i)) + (g (u (i + 1)) - g (u i))| := by ring_nf
      _ ≤ |f (u (i + 1)) - f (u i)| + |g (u (i + 1)) - g (u i)| := abs_add_le _ _
  calc (∑ i ∈ Finset.range n,
          edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i)))
      ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => key i
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
          + ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le f n hu us) (eVariationOn.sum_le g n hu us)

/-- Finite-sum version of subadditivity. -/
theorem eVariationOn_finsum_le (F : ℕ → ℝ → ℝ) (s : Set ℝ) (N : ℕ) :
    eVariationOn (fun x => ∑ i ∈ Finset.range N, F i x) s
      ≤ ∑ i ∈ Finset.range N, eVariationOn (F i) s := by
  induction N with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      refine le_of_eq (eVariationOn.constant_on ?_)
      rintro a ⟨x, _, rfl⟩ b ⟨y, _, rfl⟩
      rfl
  | succ m ih =>
      simp only [Finset.sum_range_succ]
      exact le_trans (eVariationOn_add_le _ _ s) (add_le_add ih le_rfl)

/-- Product rule for the variation. -/
theorem eVariationOn_mul_le {u v : ℝ → ℝ} {s : Set ℝ} {Mu Mv : ℝ}
    (hMu : 0 ≤ Mu) (hMv : 0 ≤ Mv)
    (hu : ∀ x ∈ s, |u x| ≤ Mu) (hv : ∀ x ∈ s, |v x| ≤ Mv) :
    eVariationOn (fun x => u x * v x) s
      ≤ ENNReal.ofReal Mu * eVariationOn v s + ENNReal.ofReal Mv * eVariationOn u s := by
  refine iSup_le ?_
  rintro ⟨n, ⟨w, hw, ws⟩⟩
  have key : ∀ i : ℕ, edist (u (w (i + 1)) * v (w (i + 1))) (u (w i) * v (w i))
      ≤ ENNReal.ofReal Mu * edist (v (w (i + 1))) (v (w i))
        + ENNReal.ofReal Mv * edist (u (w (i + 1))) (u (w i)) := by
    intro i
    simp only [edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_mul hMu, ← ENNReal.ofReal_mul hMv,
      ← ENNReal.ofReal_add (mul_nonneg hMu (abs_nonneg _)) (mul_nonneg hMv (abs_nonneg _))]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : u (w (i + 1)) * v (w (i + 1)) - u (w i) * v (w i)
        = u (w (i + 1)) * (v (w (i + 1)) - v (w i))
          + v (w i) * (u (w (i + 1)) - u (w i)) := by ring
    calc |u (w (i + 1)) * v (w (i + 1)) - u (w i) * v (w i)|
        ≤ |u (w (i + 1)) * (v (w (i + 1)) - v (w i))|
            + |v (w i) * (u (w (i + 1)) - u (w i))| := by
          rw [h1]; exact abs_add_le _ _
      _ = |u (w (i + 1))| * |v (w (i + 1)) - v (w i)|
            + |v (w i)| * |u (w (i + 1)) - u (w i)| := by rw [abs_mul, abs_mul]
      _ ≤ Mu * |v (w (i + 1)) - v (w i)| + Mv * |u (w (i + 1)) - u (w i)| := by
          gcongr
          · exact hu _ (ws (i + 1))
          · exact hv _ (ws i)
  calc (∑ i ∈ Finset.range n, edist (u (w (i + 1)) * v (w (i + 1))) (u (w i) * v (w i)))
      ≤ ∑ i ∈ Finset.range n,
          (ENNReal.ofReal Mu * edist (v (w (i + 1))) (v (w i))
            + ENNReal.ofReal Mv * edist (u (w (i + 1))) (u (w i))) :=
        Finset.sum_le_sum fun i _ => key i
    _ = ENNReal.ofReal Mu * (∑ i ∈ Finset.range n, edist (v (w (i + 1))) (v (w i)))
          + ENNReal.ofReal Mv * ∑ i ∈ Finset.range n, edist (u (w (i + 1))) (u (w i)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ ENNReal.ofReal Mu * eVariationOn v s + ENNReal.ofReal Mv * eVariationOn u s := by
        gcongr
        · exact eVariationOn.sum_le v n hw ws
        · exact eVariationOn.sum_le u n hw ws

/-- A quantitative Lipschitz bound on the variation (telescoping). -/
theorem eVariationOn_le_of_lipschitz {f : ℝ → ℝ} {s : Set ℝ} {K a b : ℝ}
    (hK : 0 ≤ K) (hs : s ⊆ Icc a b)
    (hf : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ K * |x - y|) :
    eVariationOn f s ≤ ENNReal.ofReal (K * (b - a)) := by
  refine iSup_le ?_
  rintro ⟨n, ⟨u, hu, us⟩⟩
  have hmono : ∀ i : ℕ, u i ≤ u (i + 1) := fun i => hu (Nat.le_succ i)
  have key : ∀ i : ℕ, edist (f (u (i + 1))) (f (u i))
      ≤ ENNReal.ofReal (K * (u (i + 1) - u i)) := by
    intro i
    rw [edist_dist, Real.dist_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hf _ (us (i + 1)) _ (us i)
    have habs : |u (i + 1) - u i| = u (i + 1) - u i :=
      abs_of_nonneg (by linarith [hmono i])
    rwa [habs] at h
  calc (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (K * (u (i + 1) - u i)) :=
        Finset.sum_le_sum fun i _ => key i
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, K * (u (i + 1) - u i)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        exact mul_nonneg hK (by linarith [hmono i])
    _ = ENNReal.ofReal (K * (u n - u 0)) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub fun i => u i]
    _ ≤ ENNReal.ofReal (K * (b - a)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := (hs (us n)).2
        have h2 := (hs (us 0)).1
        exact mul_le_mul_of_nonneg_left (by linarith) hK

/-- Lower semicontinuity of the variation under pointwise limits, in the
form needed to pass from partial sums to the `tsum` defining
`gaussTransfer`. -/
theorem eVariationOn_le_of_tendsto {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {s : Set ℝ} {B : ℝ≥0∞}
    (hF : ∀ x ∈ s, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hB : ∀ n, eVariationOn (F n) s ≤ B) : eVariationOn f s ≤ B := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨n, hn⟩ := (eVariationOn.lowerSemicontinuous_aux hF hcon).exists
  exact absurd (hB n) (not_le.mpr hn)

/-! ## Part 2.  Geometry of the inverse branches

`gaussInverseBranch q y = 1/(q+y)` maps `[0,1]` antitonically onto the
cylinder `I_q = [1/(q+1), 1/q]`, and the `I_q` tile `(0,1]`. -/

theorem gaussInverseBranch_image_Icc {q : ℕ} (hq : 1 ≤ q) :
    gaussInverseBranch q '' Icc (0 : ℝ) 1 = Icc (1 / ((q : ℝ) + 1)) (1 / (q : ℝ)) := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy0 : (0 : ℝ) ≤ y := hy.1
    have hy1 : y ≤ 1 := hy.2
    unfold gaussInverseBranch
    exact ⟨one_div_le_one_div_of_le (by linarith) (by linarith),
      one_div_le_one_div_of_le (by linarith) (by linarith)⟩
  · intro hx
    have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by linarith
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by positivity) hx.1
    have hlow : (q : ℝ) ≤ 1 / x := by
      have h := one_div_le_one_div_of_le hx0 hx.2
      rwa [one_div_one_div] at h
    have hhigh : 1 / x ≤ (q : ℝ) + 1 := by
      have h := one_div_le_one_div_of_le (by positivity) hx.1
      rwa [one_div_one_div] at h
    refine ⟨1 / x - (q : ℝ), ⟨by linarith, by linarith⟩, ?_⟩
    unfold gaussInverseBranch
    have hrw : (q : ℝ) + (1 / x - (q : ℝ)) = 1 / x := by ring
    rw [hrw, one_div_one_div]

/-- The variations over the branch cylinders `I_q` add up to at most the
variation over `[0,1]`.  (`I_{n+1} = [1/(n+2), 1/(n+1)]`.) -/
theorem sum_eVariationOn_branch_le (f : ℝ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
        eVariationOn f (Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))))
      ≤ eVariationOn f (Icc (0 : ℝ) 1) := by
  have step : ∀ M : ℕ,
      (∑ n ∈ Finset.range M,
          eVariationOn f (Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))))
        ≤ eVariationOn f (Icc (1 / ((M : ℝ) + 1)) 1) := by
    intro M
    induction M with
    | zero => simp
    | succ m ih =>
        have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
        have hle1 : 1 / ((m : ℝ) + 2) ≤ 1 / ((m : ℝ) + 1) :=
          one_div_le_one_div_of_le hm1 (by linarith)
        have hle2 : 1 / ((m : ℝ) + 1) ≤ 1 := by rw [div_le_one hm1]; linarith
        have hunion :
            Icc (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 1)) ∪ Icc (1 / ((m : ℝ) + 1)) 1
              = Icc (1 / ((m : ℝ) + 2)) 1 := Set.Icc_union_Icc_eq_Icc hle1 hle2
        have hsplit :
            eVariationOn f (Icc (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 1)))
                + eVariationOn f (Icc (1 / ((m : ℝ) + 1)) 1)
              ≤ eVariationOn f (Icc (1 / ((m : ℝ) + 2)) 1) := by
          rw [← hunion]
          exact eVariationOn.add_le_union f fun x hx y hy => le_trans hx.2 hy.1
        have hcast : ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by push_cast; ring
        rw [hcast]
        calc (∑ n ∈ Finset.range (m + 1),
                eVariationOn f (Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))))
            = (∑ n ∈ Finset.range m,
                eVariationOn f (Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))))
              + eVariationOn f (Icc (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 1))) := by
              rw [Finset.sum_range_succ]
          _ ≤ eVariationOn f (Icc (1 / ((m : ℝ) + 1)) 1)
              + eVariationOn f (Icc (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 1))) := by gcongr
          _ = eVariationOn f (Icc (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 1)))
              + eVariationOn f (Icc (1 / ((m : ℝ) + 1)) 1) := by rw [add_comm]
          _ ≤ eVariationOn f (Icc (1 / ((m : ℝ) + 2)) 1) := hsplit
  refine le_trans (step N) (eVariationOn.mono f ?_)
  intro x hx
  exact ⟨le_trans (by positivity) hx.1, hx.2⟩

/-- The Lebesgue mass of `|f|` over the branch cylinders adds up to at most
its mass over `[0,1]`. -/
theorem sum_integral_branch_le {f : ℝ → ℝ}
    (hint : IntegrableOn f (Icc (0 : ℝ) 1) volume) (N : ℕ) :
    (∑ n ∈ Finset.range N, ∫ t in Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)), |f t|)
      ≤ ∫ t in Icc (0 : ℝ) 1, |f t| := by
  have habs : IntegrableOn (fun t => |f t|) (Icc (0 : ℝ) 1) volume := hint.abs
  have hII : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable (fun t => |f t|) volume a b := by
    intro a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact habs.mono_set fun x hx => ⟨le_trans ha hx.1.le, le_trans hx.2 hb⟩
  have hconv : ∀ a b : ℝ, a ≤ b → (∫ t in Icc a b, |f t|) = ∫ t in a..b, |f t| := by
    intro a b hab
    rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  have step : ∀ M : ℕ,
      (∑ n ∈ Finset.range M, ∫ t in Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)), |f t|)
        = ∫ t in (1 / ((M : ℝ) + 1))..1, |f t| := by
    intro M
    induction M with
    | zero => simp
    | succ m ih =>
        have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        have hle1 : 1 / ((m : ℝ) + 2) ≤ 1 / ((m : ℝ) + 1) :=
          one_div_le_one_div_of_le hm1 (by linarith)
        have hle2 : 1 / ((m : ℝ) + 1) ≤ 1 := by rw [div_le_one hm1]; linarith
        have hpos1 : (0 : ℝ) ≤ 1 / ((m : ℝ) + 2) := by positivity
        have hcast : ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by push_cast; ring
        rw [Finset.sum_range_succ, ih, hconv _ _ hle1, hcast, add_comm]
        exact intervalIntegral.integral_add_adjacent_intervals
          (hII _ _ hpos1 hle1 hle2) (hII _ _ (le_trans hpos1 hle1) hle2 le_rfl)
  rw [step N, hconv 0 1 (by norm_num)]
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hc0 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  have hc1 : 1 / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hNpos]
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hII 0 (1 / ((N : ℝ) + 1)) le_rfl hc0 hc1) (hII (1 / ((N : ℝ) + 1)) 1 hc0 hc1 le_rfl)
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..(1 / ((N : ℝ) + 1)), |f t| :=
    intervalIntegral.integral_nonneg hc0 fun x _ => abs_nonneg _
  linarith

/-! ## Part 3.  Branch weight bounds

For each digit `q ≥ 1` we package a sup bound `S` and a variation bound `V`
for the normalized branch weight `ρ_q(y) = (1+y)/((q+y)(q+y+1))`, with

  * `S + V ≤ 3/4`               (this becomes the contraction factor), and
  * `V ≤ 1/(q(q+1)) = |I_q|`    (this makes the `L¹` constant uniform in `q`).

The extremal branch is `q = 1`, where `S = 1/2` and `V ≤ 1/4`. -/

theorem monotoneOn_gaussBranchRatio {q : ℕ} (hq : 3 ≤ q) :
    MonotoneOn (gaussBranchRatio q) (Icc (0 : ℝ) 1) := by
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  intro y hy z hz hyz
  have hy0 : (0 : ℝ) ≤ y := hy.1
  have hy1 : y ≤ 1 := hy.2
  have hz0 : (0 : ℝ) ≤ z := hz.1
  have hz1 : z ≤ 1 := hz.2
  have hdy : (0 : ℝ) < ((q : ℝ) + y) * ((q : ℝ) + y + 1) := by nlinarith
  have hdz : (0 : ℝ) < ((q : ℝ) + z) * ((q : ℝ) + z + 1) := by nlinarith
  unfold gaussBranchRatio
  rw [div_le_div_iff₀ hdy hdz]
  have hkey : (0 : ℝ) ≤ (q : ℝ) ^ 2 - (q : ℝ) - 1 - (y + z) - y * z := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (q : ℝ) - 3)
      (by linarith : (0 : ℝ) ≤ (q : ℝ) + 2), mul_nonneg hy0 hz0]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ z - y) hkey]

/-- The branch-weight package. -/
theorem gaussBranchRatio_bounds {q : ℕ} (hq : 1 ≤ q) :
    ∃ S V : ℝ, 0 ≤ S ∧ 0 ≤ V ∧ S + V ≤ 3 / 4 ∧
      V ≤ 1 / ((q : ℝ) * ((q : ℝ) + 1)) ∧
      (∀ y ∈ Icc (0 : ℝ) 1, |gaussBranchRatio q y| ≤ S) ∧
      eVariationOn (gaussBranchRatio q) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal V := by
  by_cases h1 : q = 1
  · subst h1
    refine ⟨1 / 2, 1 / 4, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · intro y hy
      have hpos : 0 < gaussBranchRatio 1 y := gaussBranchRatio_pos (by norm_num) hy
      rw [abs_of_pos hpos]
      have hy0 : (0 : ℝ) ≤ y := hy.1
      unfold gaussBranchRatio
      rw [div_le_div_iff₀ (by push_cast; nlinarith) (by norm_num : (0 : ℝ) < 2)]
      push_cast
      nlinarith
    · have h := eVariationOn_le_of_lipschitz (f := gaussBranchRatio 1)
        (s := Icc (0 : ℝ) 1) (K := 1 / 4) (a := 0) (b := 1) (by norm_num) subset_rfl
        (fun x hx y hy => abs_gaussBranchRatio_one_sub_le hx hy)
      simpa using h
  · by_cases h2 : q = 2
    · subst h2
      refine ⟨1 / 3, 1 / 18, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
      · intro y hy
        have hpos : 0 < gaussBranchRatio 2 y := gaussBranchRatio_pos (by norm_num) hy
        rw [abs_of_pos hpos]
        have h := gaussBranchRatio_le_two_div_digit_mul_succ (q := 2) (by norm_num) hy
        norm_num at h ⊢
        linarith
      · have h := eVariationOn_le_of_lipschitz (f := gaussBranchRatio 2)
          (s := Icc (0 : ℝ) 1) (K := 1 / 18) (a := 0) (b := 1) (by norm_num) subset_rfl
          (fun x hx y hy => abs_gaussBranchRatio_two_sub_le hx hy)
        simpa using h
    · have hq3 : 3 ≤ q := by omega
      have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
      have hprod : (0 : ℝ) < (q : ℝ) * ((q : ℝ) + 1) := by nlinarith
      refine ⟨2 / ((q : ℝ) * ((q : ℝ) + 1)), 1 / ((q : ℝ) * ((q : ℝ) + 1)),
        by positivity, by positivity, ?_, le_rfl, ?_, ?_⟩
      · rw [← add_div, div_le_iff₀ hprod]
        nlinarith
      · intro y hy
        have hpos : 0 < gaussBranchRatio q y := gaussBranchRatio_pos (by omega) hy
        rw [abs_of_pos hpos]
        exact gaussBranchRatio_le_two_div_digit_mul_succ (by omega) hy
      · have hmono := monotoneOn_gaussBranchRatio hq3
        have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
        have h1' : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
        have hle := hmono.eVariationOn_le h0 h1'
        rw [Set.inter_self] at hle
        refine le_trans hle (ENNReal.ofReal_le_ofReal ?_)
        unfold gaussBranchRatio
        rw [show (1 + (0 : ℝ)) = 1 by ring, show ((q : ℝ) + 0) = (q : ℝ) by ring,
          show (1 + (1 : ℝ)) = 2 by ring,
          show ((q : ℝ) + 1 + 1) = (q : ℝ) + 2 by ring]
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) hprod]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (q : ℝ)) (sq_nonneg ((q : ℝ) + 1))]

/-! ## Part 4.  The mean-value trick

On an interval, the sup of `|f|` is controlled by the variation plus the
mean of `|f|`.  This is what converts the boundary/oscillation terms of the
branch decomposition into an `L¹` term rather than an `L^∞` one. -/

theorem abs_le_var_add_mean {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hint : IntegrableOn f (Icc a b) volume)
    (hvar : eVariationOn f (Icc a b) ≠ ⊤) {x : ℝ} (hx : x ∈ Icc a b) :
    |f x| ≤ (eVariationOn f (Icc a b)).toReal
      + (b - a)⁻¹ * ∫ t in Icc a b, |f t| := by
  have hmeas : (volume (Icc a b)) = ENNReal.ofReal (b - a) := Real.volume_Icc
  have hne : (volume (Icc a b)) ≠ 0 := by
    rw [hmeas]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have htop : (volume (Icc a b)) ≠ ∞ := by rw [hmeas]; exact ENNReal.ofReal_ne_top
  obtain ⟨x₀, hx₀, hx₀le⟩ :=
    MeasureTheory.exists_le_setAverage (μ := volume) (s := Icc a b)
      (f := fun t => |f t|) hne htop hint.abs
  have havg : (⨍ t in Icc a b, |f t|) = (b - a)⁻¹ * ∫ t in Icc a b, |f t| := by
    rw [setAverage_eq, measureReal_def, hmeas, ENNReal.toReal_ofReal (by linarith),
      smul_eq_mul]
  rw [havg] at hx₀le
  have hdist : dist (f x) (f x₀) ≤ (eVariationOn f (Icc a b)).toReal :=
    BoundedVariationOn.dist_le hvar hx hx₀
  rw [Real.dist_eq] at hdist
  have hsplit : |f x| ≤ |f x₀| + |f x - f x₀| := by
    calc |f x| = |f x₀ + (f x - f x₀)| := by congr 1; ring
      _ ≤ |f x₀| + |f x - f x₀| := abs_add_le _ _
  linarith

/-! ## Part 5.  The one-branch Lasota-Yorke estimate -/

theorem branch_eVariationOn_le {q : ℕ} (hq : 1 ≤ q) {f : ℝ → ℝ}
    (hint : IntegrableOn f (Icc (0 : ℝ) 1) volume)
    (hvar : eVariationOn f (Icc (0 : ℝ) 1) ≠ ⊤) :
    eVariationOn (fun y => gaussBranchRatio q y * f (gaussInverseBranch q y))
        (Icc (0 : ℝ) 1)
      ≤ ENNReal.ofReal (3 / 4)
          * eVariationOn f (Icc (1 / ((q : ℝ) + 1)) (1 / (q : ℝ)))
        + ENNReal.ofReal (∫ t in Icc (1 / ((q : ℝ) + 1)) (1 / (q : ℝ)), |f t|) := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  set a : ℝ := 1 / ((q : ℝ) + 1) with ha
  set b : ℝ := 1 / (q : ℝ) with hb
  have hab : a < b := by
    rw [ha, hb]; exact one_div_lt_one_div_of_lt hqpos (by linarith)
  have hbapos : (0 : ℝ) < b - a := by linarith
  have hJsub : Icc a b ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    refine ⟨le_trans (by rw [ha]; positivity) hx.1, le_trans hx.2 ?_⟩
    rw [hb, div_le_one hqpos]; linarith
  have hvarJ : eVariationOn f (Icc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top hvar (eVariationOn.mono f hJsub)
  have hintJ : IntegrableOn f (Icc a b) volume := hint.mono_set hJsub
  have hIpos : (0 : ℝ) ≤ ∫ t in Icc a b, |f t| :=
    integral_nonneg fun x => abs_nonneg _
  obtain ⟨S, V, hS0, hV0, hSV, hVle, hsup, hvarρ⟩ := gaussBranchRatio_bounds hq
  have hba : b - a = 1 / ((q : ℝ) * ((q : ℝ) + 1)) := by
    rw [ha, hb]; field_simp; ring
  have hVba : V ≤ b - a := by rw [hba]; exact hVle
  set M : ℝ := (eVariationOn f (Icc a b)).toReal + (b - a)⁻¹ * ∫ t in Icc a b, |f t|
    with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have h1 : (0 : ℝ) ≤ (eVariationOn f (Icc a b)).toReal := ENNReal.toReal_nonneg
    have h2 : (0 : ℝ) ≤ (b - a)⁻¹ := inv_nonneg.mpr hbapos.le
    nlinarith
  have himg : gaussInverseBranch q '' Icc (0 : ℝ) 1 = Icc a b :=
    gaussInverseBranch_image_Icc hq
  have hanti : AntitoneOn (gaussInverseBranch q) (Icc (0 : ℝ) 1) :=
    antitoneOn_gaussInverseBranch_of_subset_unit (by omega) subset_rfl
  have hcomp : eVariationOn (fun y => f (gaussInverseBranch q y)) (Icc (0 : ℝ) 1)
      = eVariationOn f (Icc a b) := by
    have h := eVariationOn.comp_eq_of_antitoneOn f (gaussInverseBranch q) hanti
    rw [himg] at h
    exact h
  have hvbound : ∀ y ∈ Icc (0 : ℝ) 1, |f (gaussInverseBranch q y)| ≤ M := by
    intro y hy
    have hmem : gaussInverseBranch q y ∈ Icc a b := by
      rw [← himg]; exact ⟨y, hy, rfl⟩
    exact abs_le_var_add_mean hab hintJ hvarJ hmem
  have hmain := eVariationOn_mul_le (u := gaussBranchRatio q)
      (v := fun y => f (gaussInverseBranch q y)) (s := Icc (0 : ℝ) 1)
      hS0 hM0 hsup hvbound
  rw [hcomp] at hmain
  refine le_trans hmain ?_
  have hV1 : V * (b - a)⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hVba (inv_nonneg.mpr hbapos.le)
    rwa [mul_inv_cancel₀ (ne_of_gt hbapos)] at h
  have hreal : M * V ≤ V * (eVariationOn f (Icc a b)).toReal + ∫ t in Icc a b, |f t| := by
    have hexp : M * V = V * (eVariationOn f (Icc a b)).toReal
        + (V * (b - a)⁻¹) * (∫ t in Icc a b, |f t|) := by rw [hM]; ring
    rw [hexp]
    have h := mul_le_mul_of_nonneg_right hV1 hIpos
    linarith
  have h2 : ENNReal.ofReal M * eVariationOn (gaussBranchRatio q) (Icc (0 : ℝ) 1)
      ≤ ENNReal.ofReal V * eVariationOn f (Icc a b)
        + ENNReal.ofReal (∫ t in Icc a b, |f t|) := by
    have hstep : ENNReal.ofReal M * eVariationOn (gaussBranchRatio q) (Icc (0 : ℝ) 1)
        ≤ ENNReal.ofReal M * ENNReal.ofReal V := by gcongr
    refine le_trans hstep ?_
    rw [← ENNReal.ofReal_mul hM0]
    refine le_trans (ENNReal.ofReal_le_ofReal hreal) ?_
    rw [ENNReal.ofReal_add (mul_nonneg hV0 ENNReal.toReal_nonneg) hIpos,
      ENNReal.ofReal_mul hV0, ENNReal.ofReal_toReal hvarJ]
  calc ENNReal.ofReal S * eVariationOn f (Icc a b)
          + ENNReal.ofReal M * eVariationOn (gaussBranchRatio q) (Icc (0 : ℝ) 1)
      ≤ ENNReal.ofReal S * eVariationOn f (Icc a b)
          + (ENNReal.ofReal V * eVariationOn f (Icc a b)
            + ENNReal.ofReal (∫ t in Icc a b, |f t|)) := by gcongr
    _ = (ENNReal.ofReal S + ENNReal.ofReal V) * eVariationOn f (Icc a b)
          + ENNReal.ofReal (∫ t in Icc a b, |f t|) := by rw [add_mul, add_assoc]
    _ ≤ ENNReal.ofReal (3 / 4) * eVariationOn f (Icc a b)
          + ENNReal.ofReal (∫ t in Icc a b, |f t|) := by
        gcongr
        rw [← ENNReal.ofReal_add hS0 hV0]
        exact ENNReal.ofReal_le_ofReal hSV

/-! ## Part 6.  The BV Lasota-Yorke inequality for the Gauss transfer operator -/

theorem gaussTransfer_bv_lasotaYorke {f : ℝ → ℝ}
    (hint : IntegrableOn f (Icc (0 : ℝ) 1) volume)
    (hvar : eVariationOn f (Icc (0 : ℝ) 1) ≠ ⊤) :
    eVariationOn (gaussTransfer f) (Icc (0 : ℝ) 1)
      ≤ ENNReal.ofReal (3 / 4) * eVariationOn f (Icc (0 : ℝ) 1)
        + ENNReal.ofReal (∫ t in Icc (0 : ℝ) 1, |f t|) := by
  obtain ⟨Mf, hMf⟩ : ∃ Mf : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ Mf := by
    refine ⟨|f 0| + (eVariationOn f (Icc (0 : ℝ) 1)).toReal, fun x hx => ?_⟩
    have hd : dist (f x) (f 0) ≤ (eVariationOn f (Icc (0 : ℝ) 1)).toReal :=
      BoundedVariationOn.dist_le hvar hx (by norm_num)
    rw [Real.dist_eq] at hd
    have h1 : |f x| ≤ |f 0| + |f x - f 0| := by
      calc |f x| = |f 0 + (f x - f 0)| := by congr 1; ring
        _ ≤ |f 0| + |f x - f 0| := abs_add_le _ _
    linarith
  have hmem : ∀ (n : ℕ) (y : ℝ), y ∈ Icc (0 : ℝ) 1 →
      gaussInverseBranch (n + 1) y ∈ Icc (0 : ℝ) 1 := by
    intro n y hy
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hd : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + y := by push_cast; linarith [hy.1]
    unfold gaussInverseBranch
    refine ⟨(one_div_pos.mpr hd).le, ?_⟩
    rw [div_le_one hd]
    push_cast
    linarith [hy.1]
  have htend : ∀ y ∈ Icc (0 : ℝ) 1,
      Tendsto (fun N => gaussTransferPartial N f y) atTop (𝓝 (gaussTransfer f y)) := by
    intro y hy
    have hρ : Summable (fun n : ℕ => gaussBranchRatio (n + 1) y) :=
      (hasSum_gaussBranchRatio y hy).summable
    have hsum : Summable (fun n : ℕ =>
        gaussBranchRatio (n + 1) y * f (gaussInverseBranch (n + 1) y)) := by
      refine Summable.of_norm_bounded (hρ.mul_left Mf) ?_
      intro n
      have hpos : 0 < gaussBranchRatio (n + 1) y := gaussBranchRatio_pos (by omega) hy
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos, mul_comm]
      exact mul_le_mul_of_nonneg_right (hMf _ (hmem n y hy)) hpos.le
    simpa only [gaussTransferPartial, gaussTransfer] using hsum.hasSum.tendsto_sum_nat
  refine eVariationOn_le_of_tendsto htend ?_
  intro N
  have hEq : gaussTransferPartial N f
      = fun y => ∑ n ∈ Finset.range N,
          gaussBranchRatio (n + 1) y * f (gaussInverseBranch (n + 1) y) := rfl
  rw [hEq]
  refine le_trans (eVariationOn_finsum_le
      (fun n y => gaussBranchRatio (n + 1) y * f (gaussInverseBranch (n + 1) y))
      (Icc (0 : ℝ) 1) N) ?_
  have hterm : ∀ n ∈ Finset.range N,
      eVariationOn (fun y => gaussBranchRatio (n + 1) y * f (gaussInverseBranch (n + 1) y))
          (Icc (0 : ℝ) 1)
        ≤ ENNReal.ofReal (3 / 4)
            * eVariationOn f (Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)))
          + ENNReal.ofReal (∫ t in Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)), |f t|) := by
    intro n _
    have h := branch_eVariationOn_le (q := n + 1) (by omega) hint hvar
    have hc1 : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    have hc2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hc1, hc2] at h
    exact h
  calc (∑ n ∈ Finset.range N,
          eVariationOn
            (fun y => gaussBranchRatio (n + 1) y * f (gaussInverseBranch (n + 1) y))
            (Icc (0 : ℝ) 1))
      ≤ ∑ n ∈ Finset.range N,
          (ENNReal.ofReal (3 / 4)
              * eVariationOn f (Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)))
            + ENNReal.ofReal (∫ t in Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)), |f t|)) :=
        Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (3 / 4)
          * (∑ n ∈ Finset.range N,
              eVariationOn f (Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))))
        + ∑ n ∈ Finset.range N,
            ENNReal.ofReal (∫ t in Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)), |f t|) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ENNReal.ofReal (3 / 4) * eVariationOn f (Icc (0 : ℝ) 1)
          + ENNReal.ofReal (∫ t in Icc (0 : ℝ) 1, |f t|) := by
        gcongr
        · exact sum_eVariationOn_branch_le f N
        · rw [← ENNReal.ofReal_sum_of_nonneg
              (fun n _ => integral_nonneg fun x => abs_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (sum_integral_branch_le hint N)

end

end Kwon1002.BVLasotaYorke


/-
## What this file establishes, and what it does not

PROVED OUTRIGHT (no `sorry`; every theorem's axiom set is exactly
`[propext, Classical.choice, Quot.sound]`):

  `gaussTransfer_bv_lasotaYorke` -
     Var_{[0,1]}(L f) ≤ (3/4)·Var_{[0,1]}(f) + ∫_{[0,1]} |f| dLeb,
  for every `f` that is Lebesgue-integrable and of bounded variation on
  `[0,1]`.  `L = Erdos1002.gaussTransfer` is the *Gauss-normalized*
  transfer operator, `L f(y) = Σ_{q≥1} ρ_q(y) f(1/(q+y))` with
  `ρ_q(y) = (1+y)/((q+y)(q+y+1))`, i.e. the adjoint of the Gauss map on
  `L²(gaussMeasure)`, the same operator Wang's Lipschitz contraction acts
  on.  The `L¹` term is with respect to *Lebesgue* measure; since
  `1/(2 log 2) ≤ dGauss/dLeb ≤ 1/log 2` on `[0,1]`, it converts to the
  Gauss-measure `L¹` norm at the cost of a factor `≤ 2`.

Where the constants come from (branch `q`, cylinder `I_q = [1/(q+1),1/q]`,
`S_q = sup_{[0,1]} ρ_q`, `V_q = Var_{[0,1]} ρ_q`):

  * contraction factor  = max_q (S_q + V_q) ≤ 3/4, attained at `q = 1`
    (`S_1 = 1/2`, and `V_1 ≤ 1/4` via Wang's branch-1 Lipschitz constant;
    the true `V_1` is `1/6`, so `2/3` is achievable with a sharper input);
  * `L¹` constant       = max_q V_q/|I_q| ≤ 1, since `V_q ≤ 1/(q(q+1)) = |I_q|`.

NOT DONE HERE (deliberately, and each is a separate piece of work):

  * Iteration.  Getting `Var(L^n f) ≤ (3/4)^n Var f + 4‖f‖₁` needs, in
    addition, that `L f` is again integrable and BV on `[0,1]`, the BV
    part is immediate from the theorem, the integrability part needs the
    adjoint identity (`Erdos1002.GaussTransferAdjoint`) and is not proved
    here.
  * `‖L f‖_{L¹} ≤ ‖f‖_{L¹}`, the second half of the Lasota-Yorke package.
  * Quasi-compactness / spectral gap on BV, which is what §4 ultimately
    consumes.  That is Ionescu-Tulcea-Marinescu on top of this inequality
    plus the compact embedding BV ↪ L¹, neither is in Mathlib.

No sorried result from any other file is consumed.
-/
