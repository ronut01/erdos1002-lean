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
* Lemma 3.3 (`Kwon1002.shrinking_anti_concentration`) to discard the
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
per-cylinder identity, §3 the oscillatory prefix estimate at a fixed `n` with
every eventual fact supplied as a hypothesis, §4 the two `∀ᶠ n` consumers.

§3's `oscillatory_prefix_bound` is stated with the anti-concentration depth
`a`, the mode `(r_A,s_A)` it is applied to, and the resulting lower bound on
the *combined* frequency (`hdom`) left as parameters, because that is exactly
where cases 2 and 3 differ.  Both consumers are then §4:

* `laterMode_phase_bound''`, case 2, token-identical to
  `MonomialCore.laterMode_phase_bound`: `a = k`, `(r_A,s_A)` the later mode,
  and `hdom` is `Prop42.later_frequency_dominates`;
* `earlierMode_subResonance_bound`, the `k < t₀ − 100H` branch of case 3:
  `a = j`, `(r_A,s_A)` the earlier mode, and `hdom` holds because the later
  mode is zero, so `Q_k(0,0) = 0` and the combined frequency *is* `±Q_j`.

The remaining `k > t₀ + 100H` branch of case 3 is not here; see
`Kwon1002/Prop42Unconditional.lean` for its statement and the exact list of
proved inputs its assembly still has to combine.
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
lemma integrand_eq_on_cylinder {R j k : ℕ} (hRj : R ≤ j) (hRk : R ≤ k)
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
/-- **The oscillatory prefix estimate at a fixed `n`.**  This is the common
engine of the two nonzero-mode cases: the depth-`a` anti-concentration cut,
the display-(20) retained family at `a`, `k+R` and `t₋ = ⌊(m_n+a)/2 − 40H⌋`,
and display (22) at prefix depth `k+R`.  `hdom` is the only case-dependent
input — the lower bound it asserts for the combined frequency comes from
Fibonacci domination in case 2 and from the vanishing of the later mode in
the sub-resonance branch of case 3.  Every fact the manuscript takes "for all
sufficiently large `n`" is a hypothesis here; §4 supplies them. -/
theorem oscillatory_prefix_bound
    {n : ℕ} (hn1 : 1 ≤ n) {R : ℕ}
    {j k a : ℕ} (hab : a ∈ bulkJ n)
    (hj1 : 1 ≤ j) (hRj : R ≤ j) (hjk : j < k) (had : a ≤ k + R)
    (w w' : Fin (2 * R) → ℕ) {r₁ s₁ r₂ s₂ rA sA : ℤ}
    (hdt : k + R < (Prop41.kMinus n a).toNat)
    (hdom : ∀ u : List ℕ, u.length = (Prop41.kMinus n a).toNat → (∀ x ∈ u, 0 < x) →
      ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder u, Irrational α →
      Real.exp (-Hscale n) * (denom α a : ℝ) ≤ |((Qfreq α a rA sA : ℤ) : ℝ)| →
      (1 / 2) * Real.exp (-Hscale n) * (denom α a : ℝ)
        ≤ |((PhaseBounds.Qpair α j k r₁ s₁ r₂ s₂ : ℤ) : ℝ)|)
    {C₀ c₀ : ℝ}
    (h20 : ∀ i : ℕ, i ≤ 2 * mIndex n →
      volume.real {α ∈ Ioo (0 : ℝ) 1 |
          ¬ (Real.exp (lyapunov * (i : ℝ) - 1 * Hscale n) ≤ (denom α i : ℝ)
              ∧ (denom α i : ℝ) ≤ Real.exp (lyapunov * (i : ℝ) + 1 * Hscale n))}
        ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)))
    {Cac : ℝ}
    (hac : (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
        |(sA : ℝ) * (denom α a : ℝ) - (rA : ℝ) * (denom α (a - 1) : ℝ)|
          < Real.exp (-Hscale n) * (denom α a : ℝ)}).toReal ≤ Cac) :
    ‖∫ α in Ioo (0 : ℝ) 1,
        Prop42.monoAt R w r₁ s₁ α n j * Prop42.monoAt R w' r₂ s₂ α n k‖
      ≤ 3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) + Cac
          + 28 * Real.exp (-Hscale n) := by
  classical
  set H : ℝ := Hscale n with hHdef
  set η : ℝ := Real.exp (-H) with hηdef
  have hη0 : (0 : ℝ) < η := Real.exp_pos _
  set d : ℕ := k + R with hddef
  set t : ℕ := (Prop41.kMinus n a).toNat with htdef
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
  have ht2m : t ≤ 2 * mIndex n := PhaseBounds.kMinus_toNat_le_two_mIndex_of_bulk hab
  -- the retained family and its prefixes
  set T : Finset (List ℕ) := StationaryReplace.retainedWords n a d t 1 with hTdef
  have hTshape : ∀ u ∈ T, u.length = t ∧ ∀ a ∈ u, 0 < a := fun u hu =>
    StationaryReplace.retainedWords_shape u hu
  set Z : Finset (List ℕ) := T.image (fun u => u.take d) with hZdef
  set Pgood : List ℕ → Prop := fun z =>
    η * (wordDenom (z.take a) : ℝ) ≤ |((QwordAt z a rA sA : ℤ) : ℝ)| with hPdef
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
    exact StationaryReplace.volume_discarded_retainedWords_le n h20 had hdt2 ht2m
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
      |(sA : ℝ) * (denom α a : ℝ) - (rA : ℝ) * (denom α (a - 1) : ℝ)|
        < η * (denom α a : ℝ)} with hBadACdef
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
      have hqk : (denom α a : ℝ) = (wordDenom (u.take a) : ℝ) :=
        StationaryReplace.denom_eq_wordDenom_take hlen hpos hαu hirr ht0 (by omega)
      have hQeq : Qfreq α a rA sA = QwordAt u a rA sA :=
        Qfreq_eq_QwordAt hlen hpos hαu hirr ht0 (by omega) rA sA
      have hnotP : ¬ Pgood (u.take d) := (hT'mem u hu).2
      rw [hPdef] at hnotP
      simp only [not_le] at hnotP
      rw [List.take_take, min_eq_left had, QwordAt_take had] at hnotP
      refine ⟨hαIoo, ?_⟩
      have hcast : |((QwordAt u a rA sA : ℤ) : ℝ)|
          = |(sA : ℝ) * (denom α a : ℝ) - (rA : ℝ) * (denom α (a - 1) : ℝ)| := by
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
  have hkey : ∀ z ∈ G, ∃ qk : ℝ, Real.exp (lyapunov * (a : ℝ) - 1 * H) ≤ qk
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
    have hmemT : u ∈ StationaryReplace.retainedWords n a d t 1 := by rw [← hTdef]; exact huT
    have hwin := (StationaryReplace.mem_retainedWords_iff.mp hmemT).2.1
    refine ⟨(wordDenom (u.take a) : ℝ), hwin.1, ?_,
      lt_of_lt_of_le (Real.exp_pos _) hwin.1⟩
    obtain ⟨α, hαu, hirr⟩ := StationaryReplace.exists_irrational_mem_halfOpen hpos
    have hαIoo : α ∈ Ioo (0 : ℝ) 1 :=
      ZeroMode.mem_Ioo_of_mem_halfOpen hune hpos hαu hirr
    have hdk : (denom α a : ℝ) = (wordDenom (u.take a) : ℝ) :=
      StationaryReplace.denom_eq_wordDenom_take hlen hpos hαu hirr ht0 (by omega)
    have hQk : Qfreq α a rA sA = QwordAt u a rA sA :=
      Qfreq_eq_QwordAt hlen hpos hαu hirr ht0 (by omega) rA sA
    have hlow : η * (denom α a : ℝ) ≤ |((Qfreq α a rA sA : ℤ) : ℝ)| := by
      rw [hdk, hQk]
      have hp := hzP
      rw [hPdef] at hp
      rw [hzeq, List.take_take, min_eq_left had, QwordAt_take had] at hp
      exact hp
    have hdomu := hdom u hlen hpos α hαu hirr hlow
    have hQp : PhaseBounds.Qpair α j k r₁ s₁ r₂ s₂ = Qf z := by
      show PhaseBounds.Qpair α j k r₁ s₁ r₂ s₂ = QpairWord z j k r₁ s₁ r₂ s₂
      rw [hzeq, QpairWord_take hjd hkd]
      exact Qpair_eq_QpairWord hlen hpos hαu hirr ht0 (by omega) (by omega) r₁ s₁ r₂ s₂
    rw [← hQp, ← hdk]
    exact hdomu
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
    have hres := PhaseBounds.retained_descendant_bound_at_cut (n := n) (k := a) hab
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
    have hmemT : u ∈ StationaryReplace.retainedWords n a d t 1 := by rw [← hTdef]; exact huT
    refine ⟨by rw [List.length_drop, hlen], fun x hx => hpos x (List.mem_of_mem_drop hx), ?_⟩
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
      exact integrand_eq_on_cylinder hRj hRk hj1 hk1 hlen hpos hjt hkt
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

/-! ## 4. The `∀ᶠ n` wrapper -/

/-- **The Fibonacci exponent.**  `2^m ≥ 2K_c e^{H}` is achieved at
`m = ⌈(H + log 2K_c)/log 2⌉`, which is `O(H)`. -/
lemma exists_fib_exponent {Kc H : ℝ} (hKc : 1 ≤ Kc) (hH : 0 ≤ H) :
    ∃ m : ℕ, 2 * Kc ≤ Real.exp (-H) * 2 ^ m
      ∧ (m : ℝ) ≤ (H + Real.log (2 * Kc)) / Real.log 2 + 1 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set A : ℝ := Real.log (2 * Kc) with hAdef
  have hA0 : 0 ≤ A := Real.log_nonneg (by linarith)
  set x : ℝ := (H + A) / Real.log 2 with hxdef
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hlog2.le
  refine ⟨⌈x⌉₊, ?_, ?_⟩
  · have hmx : x ≤ ((⌈x⌉₊ : ℕ) : ℝ) := Nat.le_ceil x
    have hval : (2 : ℝ) ^ x = Real.exp (H + A) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hxdef]
      congr 1
      field_simp
    have h2 : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ ((⌈x⌉₊ : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hmx
    rw [hval, Real.rpow_natCast] at h2
    have hexpA : Real.exp A = 2 * Kc := Real.exp_log (by linarith)
    calc 2 * Kc = Real.exp (-H) * Real.exp (H + A) := by
          rw [← Real.exp_add, show -H + (H + A) = A by ring, hexpA]
      _ ≤ Real.exp (-H) * (2 : ℝ) ^ (⌈x⌉₊ : ℕ) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  · exact (Nat.ceil_lt_add_one hx0).le

set_option maxHeartbeats 1600000 in
/-- **Case 2 of the proof of Proposition 4.2**, token-identical to
`Kwon1002.MonomialCore.laterMode_phase_bound`, proved. -/
theorem laterMode_phase_bound'' (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ Prop42.modeBox K, ∀ w' ∈ Wv, ∀ m' ∈ Prop42.modeBox K, m' ≠ (0, 0) →
      ∀ p ∈ bulkPairs n, C * Hscale n < (p.2 : ℝ) - (p.1 : ℝ) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w m.1 m.2 α n p.1 * Prop42.monoAt R w' m'.1 m'.2 α n p.2)‖
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) := by
  classical
  obtain ⟨C20, c20, hC20, hc20, h20⟩ := LargeDeviation.display20_of_pos 1 one_pos
  obtain ⟨C3, c3, hc3, hAC⟩ := Kwon1002.shrinking_anti_concentration
  set C3' : ℝ := max C3 0 with hC3'def
  have hC3'0 : (0 : ℝ) ≤ C3' := le_max_right _ _
  have hC3C3' : C3 ≤ C3' := le_max_left _ _
  set Kc : ℝ := 2 * (K : ℝ) + 1 with hKcdef
  have hKc1 : (1 : ℝ) ≤ Kc := by
    have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    rw [hKcdef]; linarith
  set c : ℝ := min 1 (min c20 (200 * c3)) with hcdef
  have hc0 : 0 < c := lt_min one_pos (lt_min hc20 (by linarith))
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcc20 : c ≤ c20 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hcc3 : c ≤ 200 * c3 := le_trans (min_le_right _ _) (min_le_right _ _)
  set C : ℝ := max 10 (max (3 * C20) (2 * C3' + 28)) with hCdef
  have hC10 : (10 : ℝ) ≤ C := le_max_left _ _
  have hC0 : 0 < C := by linarith
  have hCA : 3 * C20 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCB : 2 * C3' + 28 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, c, 1 / 2, hC0, hc0, by norm_num, by norm_num, ?_⟩
  set M : ℝ := max 1 (max ((R : ℝ) / 200)
    ((3 * Real.log (2 * Kc) + 2) / 7)) with hMdef
  filter_upwards [h20, PhaseBounds.eventually_prefix_lt_kMinus R,
    P42Cases.tendsto_Hscale.eventually_ge_atTop M, eventually_ge_atTop 1]
    with n h20n hpref hHM hn1
  intro w hw m hm w' hw' m' hm' hm'0 p hp hgapC
  set H : ℝ := Hscale n with hHdef
  have hH1 : (1 : ℝ) ≤ H := le_trans (le_max_left _ _) hHM
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hHR : (R : ℝ) / 200 ≤ H := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hHM
  have hHlog : (3 * Real.log (2 * Kc) + 2) / 7 ≤ H :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hHM
  -- the pair
  have hjb : p.1 ∈ bulkJ n := MonomialCore.mem_bulkPairs_fst hp
  have hkb : p.2 ∈ bulkJ n := PhaseBounds.mem_bulkPairs_snd hp
  have hjk : p.1 < p.2 := MonomialCore.mem_bulkPairs_lt hp
  have hjlo : 200 * H ≤ (p.1 : ℝ) := ((Finset.mem_filter.1 hjb).2).1
  have hklo : 200 * H ≤ (p.2 : ℝ) := ((Finset.mem_filter.1 hkb).2).1
  have hRj : R ≤ p.1 := by
    have : (R : ℝ) ≤ (p.1 : ℝ) := by linarith
    exact_mod_cast this
  have hj1 : 1 ≤ p.1 := by
    have : (1 : ℝ) ≤ (p.1 : ℝ) := by linarith
    exact_mod_cast this
  have hk1 : 1 ≤ p.2 := by omega
  -- the Fibonacci exponent
  obtain ⟨mm, hmm1, hmm2⟩ := exists_fib_exponent hKc1 hH0
  have hlog2 : (2 : ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hgap : p.1 + 2 * mm ≤ p.2 := by
    have hA0 : (0 : ℝ) ≤ Real.log (2 * Kc) := Real.log_nonneg (by linarith)
    have hdiv : (H + Real.log (2 * Kc)) / Real.log 2
        ≤ (H + Real.log (2 * Kc)) / (2 / 3) :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) hlog2.le
    have hmmR : (mm : ℝ) ≤ (3 / 2) * (H + Real.log (2 * Kc)) + 1 := by
      have : (H + Real.log (2 * Kc)) / (2 / 3) = (3 / 2) * (H + Real.log (2 * Kc)) := by
        field_simp
      linarith [hmm2, hdiv, this ▸ hdiv]
    have h10 : (10 : ℝ) * H ≤ C * H := mul_le_mul_of_nonneg_right hC10 hH0
    have h2mm : (2 : ℝ) * (mm : ℝ) ≤ (p.2 : ℝ) - (p.1 : ℝ) := by
      have h7 : 3 * Real.log (2 * Kc) + 2 ≤ 7 * H := by linarith
      linarith
    have hcast : ((p.1 + 2 * mm : ℕ) : ℝ) ≤ ((p.2 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast hcast
  -- the modes
  have hmode : |((m.1 : ℤ) : ℝ)| + |((m.2 : ℤ) : ℝ)| ≤ Kc := by
    rw [Prop42.modeBox, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hm
    have h1 : |((m.1 : ℤ) : ℝ)| ≤ (K : ℝ) := by
      rw [abs_le]
      constructor
      · exact_mod_cast hm.1.1
      · exact_mod_cast hm.1.2
    have h2 : |((m.2 : ℤ) : ℝ)| ≤ (K : ℝ) := by
      rw [abs_le]
      constructor
      · exact_mod_cast hm.2.1
      · exact_mod_cast hm.2.2
    rw [hKcdef]; linarith
  -- anti-concentration at `η = e^{-H}`
  have hη0 : (0 : ℝ) < Real.exp (-H) := Real.exp_pos _
  have hη2 : Real.exp (-H) < 1 / 2 := by
    have h1 : Real.exp (-H) ≤ Real.exp (-1 : ℝ) := Real.exp_le_exp.2 (by linarith)
    have he : (2 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    have hp : (0 : ℝ) < Real.exp (-1 : ℝ) := Real.exp_pos _
    have hid : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have hacn := hAC m'.1 m'.2 (by rw [Prod.mk.eta]; exact hm'0) p.2 hk1
    (Real.exp (-H)) hη0 hη2
  have hdt : p.2 + R < (Prop41.kMinus n p.2).toNat := (hpref p hp).2
  have hdom : ∀ u : List ℕ, u.length = (Prop41.kMinus n p.2).toNat → (∀ x ∈ u, 0 < x) →
      ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder u, Irrational α →
      Real.exp (-Hscale n) * (denom α p.2 : ℝ) ≤ |((Qfreq α p.2 m'.1 m'.2 : ℤ) : ℝ)| →
      (1 / 2) * Real.exp (-Hscale n) * (denom α p.2 : ℝ)
        ≤ |((PhaseBounds.Qpair α p.1 p.2 m.1 m.2 m'.1 m'.2 : ℤ) : ℝ)| := by
    intro u hulen hupos α hαu hirr hlow
    have hune : u ≠ [] := by
      intro hnil
      rw [hnil] at hulen
      simp at hulen
      omega
    have hαIoo : α ∈ Ioo (0 : ℝ) 1 :=
      ZeroMode.mem_Ioo_of_mem_halfOpen hune hupos hαu hirr
    have hd := Prop42.later_frequency_dominates hαIoo hirr hj1 hgap hmode hlow hmm1
    have hcast : |((PhaseBounds.Qpair α p.1 p.2 m.1 m.2 m'.1 m'.2 : ℤ) : ℝ)|
        = |(-1 : ℝ) ^ p.1 * ((Qfreq α p.1 m.1 m.2 : ℤ) : ℝ)
            + (-1 : ℝ) ^ p.2 * ((Qfreq α p.2 m'.1 m'.2 : ℤ) : ℝ)| := by
      unfold PhaseBounds.Qpair
      push_cast
      ring_nf
    rw [hcast]
    exact hd
  have hmain := oscillatory_prefix_bound hn1 hkb hj1 hRj hjk (Nat.le_add_right _ _)
    w w' hdt hdom (C₀ := C20) (c₀ := c20) h20n
    (Cac := C3 * (Real.exp (-H) + Real.exp (-c3 * (p.2 : ℝ)))) hacn
  refine le_trans hmain ?_
  -- the error shape
  have hLsq : (0 : ℝ) ≤ Real.sqrt (Lnorm n) := Real.sqrt_nonneg _
  have e1 : Real.exp (-c20 * Real.sqrt (Lnorm n))
      ≤ Real.exp (-c * Real.sqrt (Lnorm n)) := Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-H) ≤ Real.exp (-c * H) := Real.exp_le_exp.2 (by nlinarith)
  have e3 : Real.exp (-c3 * (p.2 : ℝ)) ≤ Real.exp (-c * H) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hp1 : (0 : ℝ) < Real.exp (-H) := Real.exp_pos _
  have hp2 : (0 : ℝ) < Real.exp (-c3 * (p.2 : ℝ)) := Real.exp_pos _
  have hp3 : (0 : ℝ) < Real.exp (-c * H) := Real.exp_pos _
  have hp4 : (0 : ℝ) < Real.exp (-c20 * Real.sqrt (Lnorm n)) := Real.exp_pos _
  have hp5 : (0 : ℝ) < Real.exp (-c * Real.sqrt (Lnorm n)) := Real.exp_pos _
  have hρ0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (c * H) := Real.rpow_nonneg (by norm_num) _
  have hC3b : C3 * (Real.exp (-H) + Real.exp (-c3 * (p.2 : ℝ)))
      ≤ 2 * C3' * Real.exp (-c * H) := by
    have hstep1 : C3 * (Real.exp (-H) + Real.exp (-c3 * (p.2 : ℝ)))
        ≤ C3' * (Real.exp (-H) + Real.exp (-c3 * (p.2 : ℝ))) :=
      mul_le_mul_of_nonneg_right hC3C3' (by linarith)
    have hstep2 : C3' * (Real.exp (-H) + Real.exp (-c3 * (p.2 : ℝ)))
        ≤ C3' * (2 * Real.exp (-c * H)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC3'0
    linarith
  have hAterm : 3 * (C20 * Real.exp (-c20 * Real.sqrt (Lnorm n)))
      ≤ C * Real.exp (-c * Real.sqrt (Lnorm n)) := by
    have h1 : 3 * (C20 * Real.exp (-c20 * Real.sqrt (Lnorm n)))
        ≤ 3 * (C20 * Real.exp (-c * Real.sqrt (Lnorm n))) := by nlinarith
    nlinarith
  have hBterm : 2 * C3' * Real.exp (-c * H) + 28 * Real.exp (-H)
      ≤ C * Real.exp (-c * H) := by nlinarith
  nlinarith [hAterm, hBterm, hC3b, hρ0, hC0, hp3, hp5]

set_option maxHeartbeats 1600000 in
/-- **The sub-resonance branch of case 3 of the proof of Proposition 4.2.**
"If `k < t₀ − 100H`, the whole two-block amplitude is measurable before depth
`t₋`."  The later mode is zero, so the combined frequency of (33) is `±Q_j`;
the anti-concentration cut, the retained family and the descendant cut are
all taken at the *earlier* index `j`, and the complete prefixes are still of
depth `k + R`, which `PhaseBounds.subResonance_prefix_lt_kMinus_toNat` places
below the cut. -/
theorem earlierMode_subResonance_bound (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ Prop42.modeBox K, m ≠ (0, 0) → ∀ w' ∈ Wv,
      ∀ p ∈ bulkPairs n,
        (p.2 : ℝ) < Prop41.resonanceTime n p.1 - 100 * Hscale n →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w m.1 m.2 α n p.1 * Prop42.monoAt R w' 0 0 α n p.2)‖
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) := by
  classical
  obtain ⟨C20, c20, hC20, hc20, h20⟩ := LargeDeviation.display20_of_pos 1 one_pos
  obtain ⟨C3, c3, hc3, hAC⟩ := Kwon1002.shrinking_anti_concentration
  set C3' : ℝ := max C3 0 with hC3'def
  have hC3'0 : (0 : ℝ) ≤ C3' := le_max_right _ _
  have hC3C3' : C3 ≤ C3' := le_max_left _ _
  set c : ℝ := min 1 (min c20 (200 * c3)) with hcdef
  have hc0 : 0 < c := lt_min one_pos (lt_min hc20 (by linarith))
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcc20 : c ≤ c20 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hcc3 : c ≤ 200 * c3 := le_trans (min_le_right _ _) (min_le_right _ _)
  set C : ℝ := max 1 (max (3 * C20) (2 * C3' + 28)) with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hC0 : 0 < C := by linarith
  have hCA : 3 * C20 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCB : 2 * C3' + 28 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, c, 1 / 2, hC0, hc0, by norm_num, by norm_num, ?_⟩
  filter_upwards [h20,
    (P42Cases.tendsto_Hscale.const_mul_atTop
      (by norm_num : (0 : ℝ) < 60)).eventually_ge_atTop ((R : ℝ) + 1),
    P42Cases.tendsto_Hscale.eventually_ge_atTop (max 1 ((R : ℝ) / 200)),
    eventually_ge_atTop 1] with n h20n hH60 hHM hn1
  intro w hw m hm hm0 w' hw' p hp hres
  set H : ℝ := Hscale n with hHdef
  have hH1 : (1 : ℝ) ≤ H := le_trans (le_max_left _ _) hHM
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hHR : (R : ℝ) / 200 ≤ H := le_trans (le_max_right _ _) hHM
  have hjb : p.1 ∈ bulkJ n := MonomialCore.mem_bulkPairs_fst hp
  have hjk : p.1 < p.2 := MonomialCore.mem_bulkPairs_lt hp
  have hjlo : 200 * H ≤ (p.1 : ℝ) := ((Finset.mem_filter.1 hjb).2).1
  have hRj : R ≤ p.1 := by
    have : (R : ℝ) ≤ (p.1 : ℝ) := by linarith
    exact_mod_cast this
  have hj1 : 1 ≤ p.1 := by
    have : (1 : ℝ) ≤ (p.1 : ℝ) := by linarith
    exact_mod_cast this
  -- anti-concentration at the earlier index
  have hη0 : (0 : ℝ) < Real.exp (-H) := Real.exp_pos _
  have hη2 : Real.exp (-H) < 1 / 2 := by
    have h1 : Real.exp (-H) ≤ Real.exp (-1 : ℝ) := Real.exp_le_exp.2 (by linarith)
    have he : (2 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    have hp' : (0 : ℝ) < Real.exp (-1 : ℝ) := Real.exp_pos _
    have hid : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have hacn := hAC m.1 m.2 (by rw [Prod.mk.eta]; exact hm0) p.1 hj1
    (Real.exp (-H)) hη0 hη2
  have hdt : p.2 + R < (Prop41.kMinus n p.1).toNat :=
    PhaseBounds.subResonance_prefix_lt_kMinus_toNat hres hH60
  -- the later mode is zero, so the combined frequency is the earlier one
  have hdom : ∀ u : List ℕ, u.length = (Prop41.kMinus n p.1).toNat → (∀ x ∈ u, 0 < x) →
      ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder u, Irrational α →
      Real.exp (-Hscale n) * (denom α p.1 : ℝ) ≤ |((Qfreq α p.1 m.1 m.2 : ℤ) : ℝ)| →
      (1 / 2) * Real.exp (-Hscale n) * (denom α p.1 : ℝ)
        ≤ |((PhaseBounds.Qpair α p.1 p.2 m.1 m.2 0 0 : ℤ) : ℝ)| := by
    intro u _ _ α _ _ hlow
    have hz : Qfreq α p.2 (0 : ℤ) (0 : ℤ) = 0 := by
      unfold Qfreq; ring
    have hQ : PhaseBounds.Qpair α p.1 p.2 m.1 m.2 0 0
        = (-1) ^ p.1 * Qfreq α p.1 m.1 m.2 := by
      unfold PhaseBounds.Qpair
      rw [hz]
      ring
    rw [hQ]
    push_cast
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hq0 : (0 : ℝ) ≤ (denom α p.1 : ℝ) := Nat.cast_nonneg _
    have hexp : (0 : ℝ) < Real.exp (-Hscale n) := Real.exp_pos _
    nlinarith
  have hmain := oscillatory_prefix_bound hn1 hjb hj1 hRj hjk
    (le_trans hjk.le (Nat.le_add_right _ _)) w w' hdt hdom
    (C₀ := C20) (c₀ := c20) h20n
    (Cac := C3 * (Real.exp (-H) + Real.exp (-c3 * (p.1 : ℝ)))) hacn
  refine le_trans hmain ?_
  -- the error shape
  have hLsq : (0 : ℝ) ≤ Real.sqrt (Lnorm n) := Real.sqrt_nonneg _
  have e1 : Real.exp (-c20 * Real.sqrt (Lnorm n))
      ≤ Real.exp (-c * Real.sqrt (Lnorm n)) := Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-H) ≤ Real.exp (-c * H) := Real.exp_le_exp.2 (by nlinarith)
  have e3 : Real.exp (-c3 * (p.1 : ℝ)) ≤ Real.exp (-c * H) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hp1 : (0 : ℝ) < Real.exp (-H) := Real.exp_pos _
  have hp2 : (0 : ℝ) < Real.exp (-c3 * (p.1 : ℝ)) := Real.exp_pos _
  have hp3 : (0 : ℝ) < Real.exp (-c * H) := Real.exp_pos _
  have hp4 : (0 : ℝ) < Real.exp (-c20 * Real.sqrt (Lnorm n)) := Real.exp_pos _
  have hp5 : (0 : ℝ) < Real.exp (-c * Real.sqrt (Lnorm n)) := Real.exp_pos _
  have hρ0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (c * H) := Real.rpow_nonneg (by norm_num) _
  have hC3b : C3 * (Real.exp (-H) + Real.exp (-c3 * (p.1 : ℝ)))
      ≤ 2 * C3' * Real.exp (-c * H) := by
    have hstep1 : C3 * (Real.exp (-H) + Real.exp (-c3 * (p.1 : ℝ)))
        ≤ C3' * (Real.exp (-H) + Real.exp (-c3 * (p.1 : ℝ))) :=
      mul_le_mul_of_nonneg_right hC3C3' (by linarith)
    have hstep2 : C3' * (Real.exp (-H) + Real.exp (-c3 * (p.1 : ℝ)))
        ≤ C3' * (2 * Real.exp (-c * H)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC3'0
    linarith
  have hAterm : 3 * (C20 * Real.exp (-c20 * Real.sqrt (Lnorm n)))
      ≤ C * Real.exp (-c * Real.sqrt (Lnorm n)) := by
    have h1 : 3 * (C20 * Real.exp (-c20 * Real.sqrt (Lnorm n)))
        ≤ 3 * (C20 * Real.exp (-c * Real.sqrt (Lnorm n))) := by nlinarith
    nlinarith
  have hBterm : 2 * C3' * Real.exp (-c * H) + 28 * Real.exp (-H)
      ≤ C * Real.exp (-c * H) := by nlinarith
  nlinarith [hAterm, hBterm, hC3b, hρ0, hC0, hp3, hp5]

end

end P42Later

end Kwon1002
