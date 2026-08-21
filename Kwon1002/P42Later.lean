import Kwon1002.CylinderSum

/-!
# P42Later: case 2 of the proof of Proposition 4.2

"Assume the later mode `(r₂,s₂)` is nonzero."  This file carries out the
manuscript's argument (v9, lines ≈ 723-760) on the complete depth-`(k+R)`
prefix cylinders, with every analytic input taken from the tree:

* the oscillatory form (33) for a monomial pair
  (`PhaseBounds.monoAt_mul_oscillatory`) and the freezing of the combined
  frequency at depth `max j k` (`PhaseBounds.Qpair_congr`, here in its word
  form `QpairWord`);
* Lemma 3.3 (`AntiConcentration.shrinking_anti_concentration`) to discard the
  depth-`k` cylinders on which `|Q_k(r₂,s₂)| < e^{-H}q_k`;
* the Fibonacci domination `|Q| ≥ ½e^{-H}q_k`
  (`Prop42.later_frequency_dominates`);
* display (20) (`LargeDeviation.display20_of_pos`) through the three-cut
  retained family `StationaryReplace.retainedWords n k (k+R) t₋ 1`, whose
  discarded mass is `O(e^{-c₀√L})`;
* the retained-descendant exponent
  (`PhaseBounds.retained_descendant_bound_at_cut`), giving
  `q_{t₋}² ≤ 2e^{-H}·n|Q|` on every retained descendant;
* display (22) (`Kwon1002.descendant_cylinder_estimate_core`) at prefix depth
  `k+R`, descendant depth `t₋` and `ε = 2e^{-H}`;
* the cylinder-summation glue of `Kwon1002/CylinderSum.lean`.

The section-by-section split is: §1 the word-level frequencies, §2 the
per-cylinder identity, §3 the estimate at a fixed `n` with every eventual
fact supplied as a hypothesis, §4 the `∀ᶠ n` wrapper, token-identical to
`MonomialCore.laterMode_phase_bound`.
-/

open MeasureTheory Set Filter

open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace P42Later

open RetainedCut StationaryReplace CylinderSum

noncomputable section

/-! ## 1. The word-level frequencies -/

/-- The continuant frequency `Q_k(r,s)` of (33), read off a word. -/
def QwordAt (u : List ℕ) (k : ℕ) (r s : ℤ) : ℤ :=
  s * (wordDenom (u.take k) : ℤ) - r * (wordDenom (u.take (k - 1)) : ℤ)

/-- The combined frequency of a monomial pair, read off a word. -/
def QpairWord (u : List ℕ) (j k : ℕ) (r₁ s₁ r₂ s₂ : ℤ) : ℤ :=
  (-1) ^ j * QwordAt u j r₁ s₁ + (-1) ^ k * QwordAt u k r₂ s₂

lemma QwordAt_take {u : List ℕ} {d i : ℕ} (h : i ≤ d) (r s : ℤ) :
    QwordAt (u.take d) i r s = QwordAt u i r s := by
  unfold QwordAt
  rw [List.take_take, List.take_take, min_eq_left h,
    min_eq_left (le_trans (Nat.sub_le i 1) h)]

lemma QpairWord_take {u : List ℕ} {d j k : ℕ} (hj : j ≤ d) (hk : k ≤ d)
    (r₁ s₁ r₂ s₂ : ℤ) :
    QpairWord (u.take d) j k r₁ s₁ r₂ s₂ = QpairWord u j k r₁ s₁ r₂ s₂ := by
  unfold QpairWord
  rw [QwordAt_take hj, QwordAt_take hk]

/-- On the cylinder of a positive word, the continuant frequency is the word
frequency. -/
lemma Qfreq_eq_QwordAt {u : List ℕ} {d : ℕ} (hlen : u.length = d)
    (hpos : ∀ a ∈ u, 0 < a) {α : ℝ}
    (hα : α ∈ Erdos1002.gaussHalfOpenPrefixCylinder u) (hirr : Irrational α)
    (hd0 : 0 < d) {i : ℕ} (hi : i ≤ d) (r s : ℤ) :
    Qfreq α i r s = QwordAt u i r s := by
  have h1 := denom_eq_wordDenom_take hlen hpos hα hirr hd0 hi
  have h2 := denom_eq_wordDenom_take hlen hpos hα hirr hd0
    (le_trans (Nat.sub_le i 1) hi)
  have e1 : denom α i = wordDenom (u.take i) := by exact_mod_cast h1
  have e2 : denom α (i - 1) = wordDenom (u.take (i - 1)) := by exact_mod_cast h2
  unfold Qfreq QwordAt
  rw [e1, e2]

lemma Qpair_eq_QpairWord {u : List ℕ} {d : ℕ} (hlen : u.length = d)
    (hpos : ∀ a ∈ u, 0 < a) {α : ℝ}
    (hα : α ∈ Erdos1002.gaussHalfOpenPrefixCylinder u) (hirr : Irrational α)
    (hd0 : 0 < d) {j k : ℕ} (hj : j ≤ d) (hk : k ≤ d) (r₁ s₁ r₂ s₂ : ℤ) :
    PhaseBounds.Qpair α j k r₁ s₁ r₂ s₂ = QpairWord u j k r₁ s₁ r₂ s₂ := by
  unfold PhaseBounds.Qpair QpairWord
  rw [Qfreq_eq_QwordAt hlen hpos hα hirr hd0 hj,
    Qfreq_eq_QwordAt hlen hpos hα hirr hd0 hk]

/-! ## 2. The per-cylinder identity -/

/-- The `§4` character and the substrate's oscillatory phase are the same
function. -/
lemma torusChar_eq_oscillatoryPhase (K x : ℝ) :
    torusChar (K * x) = Erdos1002.oscillatoryPhase K x := by
  unfold torusChar Erdos1002.oscillatoryPhase
  congr 1
  push_cast
  ring

/-- **The two-block integrand is constant times a pure phase on a deep
cylinder.**  On the cylinder of a positive word `u` reaching depth `k + R`,
both window indicators and the combined frequency are functions of `u`, so
the integrand of (33) is the per-cylinder constant `c` times the pure phase
at the frozen integer frequency. -/
lemma integrand_eq_on_cylinder {R j k : ℕ} (hR1 : 1 ≤ R) (hRj : R ≤ j) (hRk : R ≤ k)
    (hj1 : 1 ≤ j) (hk1 : 1 ≤ k) {u : List ℕ} {t : ℕ} (hlen : u.length = t)
    (hpos : ∀ a ∈ u, 0 < a) (hjt : j + R ≤ t) (hkt : k + R ≤ t)
    (w w' : Fin (2 * R) → ℕ) (r₁ s₁ r₂ s₂ : ℤ) (n : ℕ)
    {α : ℝ} (hα : α ∈ Erdos1002.gaussHalfOpenPrefixCylinder u)
    (hirr : Irrational α) :
    Prop42.monoAt R w r₁ s₁ α n j * Prop42.monoAt R w' r₂ s₂ α n k
      = (if windowOfWord R u j = w ∧ windowOfWord R u k = w' then (1 : ℂ) else 0)
        * Erdos1002.oscillatoryPhase
            ((n : ℝ) * ((QpairWord u j k r₁ s₁ r₂ s₂ : ℤ) : ℝ)) α := by
  classical
  have ht0 : 0 < t := by omega
  have hune : u ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    simp at hlen
    omega
  have hαIoo : α ∈ Ioo (0 : ℝ) 1 := ZeroMode.mem_Ioo_of_mem_halfOpen hune hpos hα hirr
  rw [PhaseBounds.monoAt_mul_oscillatory hαIoo hirr R w w' r₁ s₁ r₂ s₂ n hj1 hk1]
  have hwj : windowWord R α j = windowOfWord R u j :=
    windowWord_eq_windowOfWord hpos hRj (by rw [hlen]; exact hjt) hα hirr
  have hwk : windowWord R α k = windowOfWord R u k :=
    windowWord_eq_windowOfWord hpos hRk (by rw [hlen]; exact hkt) hα hirr
  have hQ : PhaseBounds.Qpair α j k r₁ s₁ r₂ s₂ = QpairWord u j k r₁ s₁ r₂ s₂ :=
    Qpair_eq_QpairWord hlen hpos hα hirr ht0 (by omega) (by omega) r₁ s₁ r₂ s₂
  have hind : (P42Cases.cyl R w j ∩ P42Cases.cyl R w' k).indicator (fun _ => (1 : ℂ)) α
      = (if windowOfWord R u j = w ∧ windowOfWord R u k = w'
          then (1 : ℂ) else 0) := by
    rw [Set.indicator_apply]
    by_cases hc : windowOfWord R u j = w ∧ windowOfWord R u k = w'
    · rw [if_pos hc, if_pos ⟨show windowWord R α j = w by rw [hwj]; exact hc.1,
        show windowWord R α k = w' by rw [hwk]; exact hc.2⟩]
    · rw [if_neg hc, if_neg ?_]
      rintro ⟨h1, h2⟩
      exact hc ⟨by rw [← hwj]; exact h1, by rw [← hwk]; exact h2⟩
  rw [hind, hQ]
  congr 1
  rw [show ((QpairWord u j k r₁ s₁ r₂ s₂ : ℤ) : ℝ) * (n : ℝ) * α
      = ((n : ℝ) * ((QpairWord u j k r₁ s₁ r₂ s₂ : ℤ) : ℝ)) * α by ring]
  exact torusChar_eq_oscillatoryPhase _ _


/-- The cylinder integral in terms of the oriented interval integral of
display (22). -/
lemma setIntegral_eq_intervalIntegral {u : List ℕ} (hpos : ∀ a ∈ u, 0 < a)
    (g : ℝ → ℂ) :
    (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, g α)
      = (-1 : ℂ) ^ u.length
          * ∫ α in (Erdos1002.gaussInverseWord u 0)..(Erdos1002.gaussInverseWord u 1),
              g α := by
  rw [CylinderSum.intervalIntegral_eq_cylinder hpos g, ← mul_assoc, ← mul_pow]
  norm_num

/-! ## 3. The estimate at a fixed `n` -/

set_option maxHeartbeats 1600000 in
/-- **Case 2 of the proof of Proposition 4.2, at a fixed `n`.**  Every fact
that the manuscript takes "for all sufficiently large `n`" is a hypothesis
here; §4 supplies them. -/
theorem later_case_fixed
    {n : ℕ} (hn1 : 1 ≤ n) {R : ℕ} (hR1 : 1 ≤ R)
    {j k : ℕ} (hjb : j ∈ bulkJ n) (hkb : k ∈ bulkJ n)
    (hRj : R ≤ j) (hjk : j < k)
    (w w' : Fin (2 * R) → ℕ) {r₁ s₁ r₂ s₂ : ℤ}
    {Kc : ℝ} (hmode : |(r₁ : ℝ)| + |(s₁ : ℝ)| ≤ Kc)
    {m : ℕ} (hgap : j + 2 * m ≤ k)
    (hm : 2 * Kc ≤ Real.exp (-Hscale n) * 2 ^ m)
    (hdt : k + R < (Prop41.kMinus n k).toNat)
    {C₀ c₀ : ℝ}
    (h20 : ∀ i : ℕ, i ≤ 2 * mIndex n →
      volume.real {α ∈ Ioo (0 : ℝ) 1 |
          ¬ (Real.exp (lyapunov * (i : ℝ) - 1 * Hscale n) ≤ (denom α i : ℝ)
              ∧ (denom α i : ℝ) ≤ Real.exp (lyapunov * (i : ℝ) + 1 * Hscale n))}
        ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)))
    {Cac : ℝ}
    (hac : (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
        |(s₂ : ℝ) * (denom α k : ℝ) - (r₂ : ℝ) * (denom α (k - 1) : ℝ)|
          < Real.exp (-Hscale n) * (denom α k : ℝ)}).toReal ≤ Cac) :
    ‖∫ α in Ioo (0 : ℝ) 1,
        Prop42.monoAt R w r₁ s₁ α n j * Prop42.monoAt R w' r₂ s₂ α n k‖
      ≤ 3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) + Cac
          + 28 * Real.exp (-Hscale n) := by
  classical
  set H : ℝ := Hscale n with hHdef
  set η : ℝ := Real.exp (-H) with hηdef
  have hη0 : (0 : ℝ) < η := Real.exp_pos _
  set d : ℕ := k + R with hddef
  set t : ℕ := (Prop41.kMinus n k).toNat with htdef
  have hj1 : 1 ≤ j := le_trans hR1 hRj
  have hRk : R ≤ k := le_trans hRj hjk.le
  have hk1 : 1 ≤ k := by omega
  have hd0 : 0 < d := by omega
  have hdt' : d < t := hdt
  have ht0 : 0 < t := by omega
  have hkd : k ≤ d := by omega
  have hjd : j ≤ d := by omega
  have hdt2 : d ≤ t := hdt'.le
  have hjt : j + R ≤ t := by omega
  have hkt : k + R ≤ t := by omega
  have ht2m : t ≤ 2 * mIndex n := PhaseBounds.kMinus_toNat_le_two_mIndex_of_bulk hkb
  -- the retained family and its prefixes
  set T : Finset (List ℕ) := StationaryReplace.retainedWords n k d t 1 with hTdef
  have hTshape : ∀ u ∈ T, u.length = t ∧ ∀ a ∈ u, 0 < a := fun u hu =>
    StationaryReplace.retainedWords_shape u hu
  set Z : Finset (List ℕ) := T.image (fun u => u.take d) with hZdef
  set Pgood : List ℕ → Prop := fun z =>
    η * (wordDenom (z.take k) : ℝ) ≤ |((QwordAt z k r₂ s₂ : ℤ) : ℝ)| with hPdef
  set G : Finset (List ℕ) := Z.filter Pgood with hGdef
  set B : Finset (List ℕ) := Z.filter (fun z => ¬ Pgood z) with hBdef
  -- the integrand
  set f : ℝ → ℂ := fun α =>
    Prop42.monoAt R w r₁ s₁ α n j * Prop42.monoAt R w' r₂ s₂ α n k with hfdef
  have hfm : Measurable f :=
    (Prop42.measurable_monoAt R w r₁ s₁ n j).mul (Prop42.measurable_monoAt R w' r₂ s₂ n k)
  have hf1 : ∀ α, ‖f α‖ ≤ 1 := by
    intro α
    rw [hfdef, norm_mul]
    have h1 := Prop42.norm_monoAt_le R w r₁ s₁ α n j
    have h2 := Prop42.norm_monoAt_le R w' r₂ s₂ α n k
    nlinarith [norm_nonneg (Prop42.monoAt R w r₁ s₁ α n j),
      norm_nonneg (Prop42.monoAt R w' r₂ s₂ α n k)]
  -- ### shape of the prefix family
  have hZshape : ∀ z ∈ Z, z.length = d ∧ ∀ a ∈ z, 0 < a := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨by rw [List.length_take, (hTshape u hu).1, min_eq_left hdt2],
      fun a ha => (hTshape u hu).2 a (List.mem_of_mem_take ha)⟩
  have hZorig : ∀ z ∈ Z, ∃ u ∈ T, z = u.take d := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨u, hu, rfl⟩
  -- ### step 1: the complete prefix partition at depth `t`
  have hstep1 : ‖(∫ α in Ioo (0 : ℝ) 1, f α)
        - ∑ u ∈ T, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α‖
      ≤ 3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) := by
    refine le_trans (CylinderSum.norm_integral_sub_sum_le ht0 T hTshape hfm hf1) ?_
    rw [hTdef]
    exact StationaryReplace.volume_discarded_retainedWords_le n h20 hkd hdt2 ht2m
  -- ### the fiberwise splitting
  have hmaps : ∀ u ∈ T, u.take d ∈ Z := fun u hu => Finset.mem_image_of_mem _ hu
  have hfib : ∑ z ∈ Z, ∑ u ∈ T.filter (fun u => u.take d = z),
        (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α)
      = ∑ u ∈ T, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  have hsplit : ∑ z ∈ Z, ∑ u ∈ T.filter (fun u => u.take d = z),
        (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α)
      = (∑ z ∈ G, ∑ u ∈ T.filter (fun u => u.take d = z),
          ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α)
        + ∑ z ∈ B, ∑ u ∈ T.filter (fun u => u.take d = z),
            ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α := by
    rw [hGdef, hBdef]
    exact (Finset.sum_filter_add_sum_filter_not Z Pgood _).symm
  -- ### step 2: the anti-concentration discard
  set T' : Finset (List ℕ) := T.filter (fun u => ¬ Pgood (u.take d)) with hT'def
  have hT'maps : ∀ u ∈ T', u.take d ∈ B := by
    intro u hu
    rw [hT'def, Finset.mem_filter] at hu
    rw [hBdef, Finset.mem_filter]
    exact ⟨hmaps u hu.1, hu.2⟩
  have hfil : ∀ z ∈ B, T'.filter (fun u => u.take d = z)
      = T.filter (fun u => u.take d = z) := by
    intro z hz
    rw [hBdef, Finset.mem_filter] at hz
    ext u
    simp only [hT'def, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hu, -⟩, he⟩
      exact ⟨hu, he⟩
    · rintro ⟨hu, he⟩
      exact ⟨⟨hu, by rw [he]; exact hz.2⟩, he⟩
  have hbadsum : ∑ z ∈ B, ∑ u ∈ T.filter (fun u => u.take d = z),
        ‖∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α‖
      = ∑ u ∈ T', ‖∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α‖ := by
    rw [← Finset.sum_fiberwise_of_maps_to hT'maps
      (fun u => ‖∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α‖)]
    exact Finset.sum_congr rfl (fun z hz => by rw [hfil z hz])
  set BadAC : Set ℝ := {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      |(s₂ : ℝ) * (denom α k : ℝ) - (r₂ : ℝ) * (denom α (k - 1) : ℝ)|
        < η * (denom α k : ℝ)} with hBadACdef
  have hT'mem : ∀ u ∈ T', u ∈ T ∧ ¬ Pgood (u.take d) := by
    intro u hu
    rw [hT'def, Finset.mem_filter] at hu
    exact hu
  have hT'sub : ∀ u ∈ T', u ∈ T := fun u hu => (hT'mem u hu).1
  have hcover : (⋃ u ∈ T', Erdos1002.gaussHalfOpenPrefixCylinder u)
      ⊆ BadAC ∪ {α : ℝ | ¬ Irrational α} := by
    intro α hα
    obtain ⟨u, hu, hαu⟩ := Set.mem_iUnion₂.mp hα
    by_cases hirr : Irrational α
    · left
      have huT : u ∈ T := hT'sub u hu
      have hlen := (hTshape u huT).1
      have hpos := (hTshape u huT).2
      have hune : u ≠ [] := by
        intro hnil
        rw [hnil] at hlen
        simp at hlen
        omega
      have hαIoo : α ∈ Ioo (0 : ℝ) 1 :=
        ZeroMode.mem_Ioo_of_mem_halfOpen hune hpos hαu hirr
      have hqk : (denom α k : ℝ) = (wordDenom (u.take k) : ℝ) :=
        StationaryReplace.denom_eq_wordDenom_take hlen hpos hαu hirr ht0 (by omega)
      have hQeq : Qfreq α k r₂ s₂ = QwordAt u k r₂ s₂ :=
        Qfreq_eq_QwordAt hlen hpos hαu hirr ht0 (by omega) r₂ s₂
      have hnotP : ¬ Pgood (u.take d) := (hT'mem u hu).2
      rw [hPdef] at hnotP
      simp only [not_le] at hnotP
      rw [List.take_take, min_eq_left hkd, QwordAt_take hkd] at hnotP
      refine ⟨hαIoo, ?_⟩
      have hcast : |((QwordAt u k r₂ s₂ : ℤ) : ℝ)|
          = |(s₂ : ℝ) * (denom α k : ℝ) - (r₂ : ℝ) * (denom α (k - 1) : ℝ)| := by
        rw [← hQeq]
        unfold Qfreq
        push_cast
        ring_nf
      rw [hcast, hqk] at hnotP
      rw [hqk]
      exact hnotP
    · right
      exact hirr
  have hnullQ : volume {α : ℝ | ¬ Irrational α} = 0 := by
    have hset : {α : ℝ | ¬ Irrational α} = Set.range ((↑) : ℚ → ℝ) := by
      ext x
      simp [Irrational]
    rw [hset]
    exact (Set.countable_range _).measure_zero volume
  have hdisjT' : (T' : Set (List ℕ)).PairwiseDisjoint
      (fun u => Erdos1002.gaussHalfOpenPrefixCylinder u) := by
    intro x hx y hy hxy
    have hx1 := hT'sub x (Finset.mem_coe.1 hx)
    have hy1 := hT'sub y (Finset.mem_coe.1 hy)
    exact Erdos1002.disjoint_gaussHalfOpenPrefixCylinder_of_sameLength
      (by rw [(hTshape x hx1).1, (hTshape y hy1).1]) (hTshape x hx1).2 (hTshape y hy1).2 hxy
  have hbadvol : ∑ u ∈ T', ‖∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α‖
      ≤ Cac := by
    have hterm : ∀ u ∈ T', ‖∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α‖
        ≤ (volume (Erdos1002.gaussHalfOpenPrefixCylinder u)).toReal := by
      intro u hu
      have hpos := (hTshape u (hT'sub u hu)).2
      have hlt : volume (Erdos1002.gaussHalfOpenPrefixCylinder u) < ⊤ :=
        lt_top_iff_ne_top.2 (CylinderSum.volume_halfOpen_ne_top hpos)
      have hb := norm_setIntegral_le_of_norm_le_const (μ := volume)
        (s := Erdos1002.gaussHalfOpenPrefixCylinder u) (f := f) (C := 1) hlt
        (fun x _ => hf1 x)
      simpa using hb
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hfin : ∀ u ∈ T', volume (Erdos1002.gaussHalfOpenPrefixCylinder u) ≠ ⊤ :=
      fun u hu => CylinderSum.volume_halfOpen_ne_top (hTshape u (hT'sub u hu)).2
    have hsum : ∑ u ∈ T', volume (Erdos1002.gaussHalfOpenPrefixCylinder u)
        = volume (⋃ u ∈ T', Erdos1002.gaussHalfOpenPrefixCylinder u) :=
      (measure_biUnion_finset hdisjT'
        (fun u _ => Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder u)).symm
    have hBadfin : volume BadAC ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
      rw [Real.volume_Ioo]
      simp
    calc ∑ u ∈ T', (volume (Erdos1002.gaussHalfOpenPrefixCylinder u)).toReal
        = (∑ u ∈ T', volume (Erdos1002.gaussHalfOpenPrefixCylinder u)).toReal :=
          (ENNReal.toReal_sum hfin).symm
      _ = (volume (⋃ u ∈ T', Erdos1002.gaussHalfOpenPrefixCylinder u)).toReal := by
          rw [hsum]
      _ ≤ (volume BadAC).toReal := by
          refine ENNReal.toReal_mono hBadfin ?_
          calc volume (⋃ u ∈ T', Erdos1002.gaussHalfOpenPrefixCylinder u)
              ≤ volume (BadAC ∪ {α : ℝ | ¬ Irrational α}) := measure_mono hcover
            _ ≤ volume BadAC + volume {α : ℝ | ¬ Irrational α} := measure_union_le _ _
            _ = volume BadAC := by rw [hnullQ, add_zero]
      _ ≤ Cac := hac
  have hbad : ‖∑ z ∈ B, ∑ u ∈ T.filter (fun u => u.take d = z),
        ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α‖ ≤ Cac := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun z _ => norm_sum_le _ _)) ?_
    rw [hbadsum]
    exact hbadvol
  -- ### step 3: display (22) on the good prefixes
  have hGmem : ∀ z ∈ G, z ∈ Z ∧ Pgood z := by
    intro z hz
    rw [hGdef, Finset.mem_filter] at hz
    exact hz
  set Sf : List ℕ → Finset (List ℕ) := fun z =>
    (T.filter (fun u => u.take d = z)).image (fun u => u.drop d) with hSfdef
  set Qf : List ℕ → ℤ := fun z => QpairWord z j k r₁ s₁ r₂ s₂ with hQfdef
  set Rf : List ℕ → ℝ := fun _ => Real.exp (lyapunov * (t : ℝ) + 1 * H) with hRfdef
  set cf : List ℕ → List ℕ → ℂ := fun z v =>
    if windowOfWord R (z ++ v) j = w ∧ windowOfWord R (z ++ v) k = w'
      then (1 : ℂ) else 0 with hcfdef
  -- the frequency lower bound on a good prefix
  have hkey : ∀ z ∈ G, ∃ qk : ℝ, Real.exp (lyapunov * (k : ℝ) - 1 * H) ≤ qk
      ∧ (1 / 2) * η * qk ≤ |((Qf z : ℤ) : ℝ)| ∧ 0 < qk := by
    intro z hz
    obtain ⟨hzZ, hzP⟩ := hGmem z hz
    obtain ⟨u, huT, hzeq⟩ := hZorig z hzZ
    have hlen := (hTshape u huT).1
    have hpos := (hTshape u huT).2
    have hune : u ≠ [] := by
      intro hnil
      rw [hnil] at hlen
      simp at hlen
      omega
    have hmemT : u ∈ StationaryReplace.retainedWords n k d t 1 := by rw [← hTdef]; exact huT
    have hwin := (StationaryReplace.mem_retainedWords_iff.mp hmemT).2.1
    refine ⟨(wordDenom (u.take k) : ℝ), hwin.1, ?_,
      lt_of_lt_of_le (Real.exp_pos _) hwin.1⟩
    obtain ⟨α, hαu, hirr⟩ := StationaryReplace.exists_irrational_mem_halfOpen hpos
    have hαIoo : α ∈ Ioo (0 : ℝ) 1 :=
      ZeroMode.mem_Ioo_of_mem_halfOpen hune hpos hαu hirr
    have hdk : (denom α k : ℝ) = (wordDenom (u.take k) : ℝ) :=
      StationaryReplace.denom_eq_wordDenom_take hlen hpos hαu hirr ht0 (by omega)
    have hQk : Qfreq α k r₂ s₂ = QwordAt u k r₂ s₂ :=
      Qfreq_eq_QwordAt hlen hpos hαu hirr ht0 (by omega) r₂ s₂
    have hlow : η * (denom α k : ℝ) ≤ |((Qfreq α k r₂ s₂ : ℤ) : ℝ)| := by
      rw [hdk, hQk]
      have hp := hzP
      rw [hPdef] at hp
      rw [hzeq, List.take_take, min_eq_left hkd, QwordAt_take hkd] at hp
      exact hp
    have hdom := Prop42.later_frequency_dominates hαIoo hirr hj1 hgap hmode hlow hm
    have hQp : PhaseBounds.Qpair α j k r₁ s₁ r₂ s₂ = Qf z := by
      show PhaseBounds.Qpair α j k r₁ s₁ r₂ s₂ = QpairWord z j k r₁ s₁ r₂ s₂
      rw [hzeq, QpairWord_take hjd hkd]
      exact Qpair_eq_QpairWord hlen hpos hαu hirr ht0 (by omega) (by omega) r₁ s₁ r₂ s₂
    have hcast : |((Qf z : ℤ) : ℝ)|
        = |(-1 : ℝ) ^ j * ((Qfreq α j r₁ s₁ : ℤ) : ℝ)
            + (-1 : ℝ) ^ k * ((Qfreq α k r₂ s₂ : ℤ) : ℝ)| := by
      rw [← hQp]
      unfold PhaseBounds.Qpair
      push_cast
      ring_nf
    rw [hcast, ← hdk]
    exact hdom
  have hGshape : ∀ z ∈ G, z.length = d ∧ ∀ a ∈ z, 0 < a :=
    fun z hz => hZshape z (hGmem z hz).1
  have hQne : ∀ z ∈ G, Qf z ≠ 0 := by
    intro z hz h0
    obtain ⟨qk, hqkl, hQlow, hqk0⟩ := hkey z hz
    rw [h0] at hQlow
    simp only [Int.cast_zero, abs_zero] at hQlow
    nlinarith
  have hnn : Real.exp (Lnorm n) ≤ (n : ℝ) := by
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    rw [Lnorm, Real.exp_log hn0]
  have hled : 2 * (1 : ℝ) + 3 * 1 < 80 * lyapunov := by
    have h := Prop42.eighty_lyapunov_bounds.1
    linarith
  have hRbd : ∀ z ∈ G, (Rf z) ^ 2 ≤ (2 * η) * (n : ℝ) * |((Qf z : ℤ) : ℝ)| := by
    intro z hz
    obtain ⟨qk, hqkl, hQlow, hqk0⟩ := hkey z hz
    have hQlow' : (1 / 2) * Real.exp (-1 * H) * qk ≤ |((Qf z : ℤ) : ℝ)| := by
      rw [neg_one_mul, ← hηdef]
      exact hQlow
    have hres := PhaseBounds.retained_descendant_bound_at_cut (n := n) (k := k) hkb
      (del := 1) (cc := 1) hled (le_of_lt (Real.exp_pos _)) (le_refl (Rf z))
      hqkl hQlow' hnn
    calc (Rf z) ^ 2 ≤ 2 * Real.exp (-1 * H) * ((n : ℝ) * |((Qf z : ℤ) : ℝ)|) := hres
      _ = (2 * η) * (n : ℝ) * |((Qf z : ℤ) : ℝ)| := by
          rw [neg_one_mul, ← hηdef]; ring
  have hSspec : ∀ z ∈ G, ∀ v ∈ Sf z, v.length = t - d ∧ (∀ a ∈ v, 0 < a)
      ∧ ((Erdos1002.cfTerminalDenominator (z ++ v) : ℕ) : ℝ) ≤ Rf z := by
    intro z hz v hv
    rw [hSfdef] at hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    rw [Finset.mem_filter] at hu
    obtain ⟨huT, hutake⟩ := hu
    have hlen := (hTshape u huT).1
    have hpos := (hTshape u huT).2
    have hcat : z ++ u.drop d = u := by rw [← hutake, List.take_append_drop]
    have hmemT : u ∈ StationaryReplace.retainedWords n k d t 1 := by rw [← hTdef]; exact huT
    refine ⟨by rw [List.length_drop, hlen], fun a ha => hpos a (List.mem_of_mem_drop ha), ?_⟩
    rw [hcat, ← StationaryReplace.wordDenom_eq_cfTerminalDenominator]
    exact (StationaryReplace.mem_retainedWords_iff.mp hmemT).2.2.2.2
  have hcbd : ∀ z v, ‖cf z v‖ ≤ 1 := by
    intro z v
    rw [hcfdef]
    by_cases hc : windowOfWord R (z ++ v) j = w ∧ windowOfWord R (z ++ v) k = w'
    · simp [hc]
    · simp [hc]
  have hcore := Kwon1002.descendant_cylinder_estimate_core (ε := 2 * η)
    (by positivity) (n := n) (d := d) (k := t) (by omega) hdt'
    G Qf Rf Sf cf hGshape hQne hRbd hSspec hcbd
  -- the per-prefix identity
  have hzid : ∀ z ∈ G, ∑ u ∈ T.filter (fun u => u.take d = z),
        (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α)
      = (-1 : ℂ) ^ t * ∑ v ∈ Sf z, cf z v *
          ∫ α in (Erdos1002.gaussInverseWord (z ++ v) 0)..
            (Erdos1002.gaussInverseWord (z ++ v) 1),
            Erdos1002.oscillatoryPhase ((n : ℝ) * ((Qf z : ℤ) : ℝ)) α := by
    intro z hz
    have hinj : ∀ x ∈ T.filter (fun u => u.take d = z),
        ∀ y ∈ T.filter (fun u => u.take d = z), x.drop d = y.drop d → x = y := by
      intro x hx y hy hxy
      rw [Finset.mem_filter] at hx hy
      calc x = x.take d ++ x.drop d := (List.take_append_drop d x).symm
        _ = y.take d ++ y.drop d := by rw [hx.2, hy.2, hxy]
        _ = y := List.take_append_drop d y
    rw [hSfdef, Finset.mul_sum, Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have hu' := hu
    rw [Finset.mem_filter] at hu'
    obtain ⟨huT, hutake⟩ := hu'
    have hlen := (hTshape u huT).1
    have hpos := (hTshape u huT).2
    have hcat : z ++ u.drop d = u := by rw [← hutake, List.take_append_drop]
    have hQz : Qf z = QpairWord u j k r₁ s₁ r₂ s₂ := by
      show QpairWord z j k r₁ s₁ r₂ s₂ = QpairWord u j k r₁ s₁ r₂ s₂
      rw [← hutake, QpairWord_take hjd hkd]
    have hpt : (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α)
        = cf z (u.drop d) * ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u,
            Erdos1002.oscillatoryPhase ((n : ℝ) * ((Qf z : ℤ) : ℝ)) α := by
      rw [← integral_const_mul]
      refine setIntegral_congr_ae
        (Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder u) ?_
      filter_upwards [LargeDeviation.ae_irrational_volume] with α hirr hαu
      have hval : cf z (u.drop d)
          = (if windowOfWord R u j = w ∧ windowOfWord R u k = w'
              then (1 : ℂ) else 0) := by
        show (if windowOfWord R (z ++ u.drop d) j = w
                ∧ windowOfWord R (z ++ u.drop d) k = w' then (1 : ℂ) else 0) = _
        rw [hcat]
      show Prop42.monoAt R w r₁ s₁ α n j * Prop42.monoAt R w' r₂ s₂ α n k
          = cf z (u.drop d) * Erdos1002.oscillatoryPhase ((n : ℝ) * ((Qf z : ℤ) : ℝ)) α
      rw [hval, hQz]
      exact integrand_eq_on_cylinder hR1 hRj hRk hj1 hk1 hlen hpos hjt hkt
        w w' r₁ s₁ r₂ s₂ n hαu hirr
    rw [hpt, setIntegral_eq_intervalIntegral hpos, hlen, hcat]
    ring
  have hgood : ‖∑ z ∈ G, ∑ u ∈ T.filter (fun u => u.take d = z),
        ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α‖ ≤ 28 * η := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ z ∈ G, ‖∑ u ∈ T.filter (fun u => u.take d = z),
          (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α)‖
        = ‖∑ v ∈ Sf z, cf z v *
            ∫ α in (Erdos1002.gaussInverseWord (z ++ v) 0)..
              (Erdos1002.gaussInverseWord (z ++ v) 1),
              Erdos1002.oscillatoryPhase ((n : ℝ) * ((Qf z : ℤ) : ℝ)) α‖ := by
      intro z hz
      rw [hzid z hz, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [Finset.sum_congr rfl hterm]
    linarith [hcore]
  -- ### assembly
  have hsumT : ∑ u ∈ T, (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α)
      = (∑ z ∈ G, ∑ u ∈ T.filter (fun u => u.take d = z),
          ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α)
        + ∑ z ∈ B, ∑ u ∈ T.filter (fun u => u.take d = z),
            ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α := by
    rw [← hfib, hsplit]
  have hTnorm : ‖∑ u ∈ T, (∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α)‖
      ≤ 28 * η + Cac := by
    rw [hsumT]
    exact le_trans (norm_add_le _ _) (add_le_add hgood hbad)
  calc ‖∫ α in Ioo (0 : ℝ) 1, f α‖
      = ‖((∫ α in Ioo (0 : ℝ) 1, f α)
          - ∑ u ∈ T, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α)
          + ∑ u ∈ T, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α‖ := by
        congr 1
        ring
    _ ≤ ‖(∫ α in Ioo (0 : ℝ) 1, f α)
          - ∑ u ∈ T, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α‖
        + ‖∑ u ∈ T, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, f α‖ :=
        norm_add_le _ _
    _ ≤ 3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) + (28 * η + Cac) :=
        add_le_add hstep1 hTnorm
    _ = 3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) + Cac
          + 28 * Real.exp (-Hscale n) := by rw [hηdef, hHdef]; ring

end

end P42Later

end Kwon1002
