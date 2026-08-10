import Kwon1002.DigitLaw
import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# Ergodicity of the Gauss-torus cocycle, recurrence to the reset set, and
# the invariant carry graph

The Layer-5 consequences of Lemma 6.2 (v5 lines 1269-1287): with the
mixing of `(Ω̂ × T², μ̂₀, S)` in hand (`Lemma62.lemma_6_2_gauss_torus_mixing`),

* `hatS_ergodic`: the cocycle is ergodic.  Mathlib has no mixing
  predicate and no mixing-implies-ergodic lemma, so the implication is
  carried out here: a strictly invariant set has constant correlation
  sequence, so its mass solves `x = x²`.
* `noResetProb_tendsto_zero`: `p_R = μ̂₀(⋂_{t<R} S⁻ᵗ Rᶜ) → 0`
  (v5 lines 1286-1287).  The never-reset set `B_∞` satisfies
  `B_∞ ∩ S⁻ᵐ B_∞ = B_∞` **exactly** (a forward orbit that never visits
  the reset set keeps never visiting it), so mixing forces
  `μ̂₀(B_∞) = μ̂₀(B_∞)²`; the value `1` is impossible because `B_∞` misses
  the reset set, which has positive mass (`resetSet_measure_pos`), and
  continuity from above finishes.  Ergodicity is not needed for this
  route, only mixing itself.
* `exists_carry_graph`, **(56)** (v5 lines 1269-1279): a measurable
  invariant graph `d_*` with `0 ≤ d_* ≤ D` and
  `d_*(Sz) = φ_z(d_*(z))` a.e.  The construction is the manuscript's:
  follow the backward orbit to its most recent visit to the reset set
  (a.e. finite by the recurrence statement above, transported backward
  through the measure-preserving `hatSinv`), restart the carry at `0`
  one step after that visit, and push it forward with the carry map (53).
  The absolute bound is `D = 9`: one step gives
  `c' < x(c+1) + 1`, two steps give
  `c'' < x' x (c+1) + 2x' + 1 ≤ (c+1)/2 + 3` because consecutive Gauss
  iterates satisfy `x · Tx ≤ 1/2` (`mul_gaussMap_le_half`), and
  `c ≤ 9 → c'' ≤ 7` closes the two-step induction.  The reset property
  `carryMap_eq_zero_of_mem_resetSet` (with `D = 9 ≥` every trajectory
  value) makes the graph equation hold across resets.

## Naming

`Kwon1002.Section6Skeleton` already *declares* (sorried)
`Kwon1002.noResetProb_tendsto_zero` and `Kwon1002.exists_carry_graph`,
and this module sits downstream of that file, so re-declaring those
fully-qualified names would silently shadow — the exact hazard recorded
in the skeleton's docstring for Lemma 6.1.  The proofs here therefore
live in the namespace `Kwon1002.CarryGraph`, with `example` guards
checking that each statement is token-identical to the skeleton's.

## Pointwise exactness

The two cocycle maps are mutually inverse only on the invariant region
`GoodT` (base pair in `natExtGood`, torus pair in `[0,1)²`), which
carries full `μ̂₀`-measure (`hatMu0_ae_goodT`).  `hatSinv_hatS` and
`hatS_hatSinv` are proved *pointwise on that region*, not almost
everywhere, so they can be iterated along orbits.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Kwon1002

namespace CarryGraph

noncomputable section

/-! ## Measurability of the reset sets -/

theorem measurableSet_resetSet (D : ℕ) : MeasurableSet (resetSet D) := by
  rw [resetSet, Set.setOf_and, Set.setOf_and]
  exact (measurableSet_lt measurable_fst.fst measurable_const).inter
    ((measurableSet_lt measurable_const measurable_snd.snd).inter
      (measurableSet_lt measurable_snd.snd measurable_const))

theorem noResetSet_eq_iInter (D R : ℕ) :
    noResetSet D R = ⋂ (t : ℕ), ⋂ (_ : t < R), hatS^[t] ⁻¹' (resetSet D)ᶜ := by
  ext z
  simp [noResetSet, Set.mem_iInter]

theorem measurableSet_noResetSet (D R : ℕ) : MeasurableSet (noResetSet D R) := by
  rw [noResetSet_eq_iInter]
  exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ =>
    (measurable_hatS.iterate t) (measurableSet_resetSet D).compl

theorem noResetSet_antitone (D : ℕ) : Antitone (fun R => noResetSet D R) := by
  intro R R' h z hz t ht
  exact hz t (lt_of_lt_of_le ht h)

/-- The forward orbit never visits the reset set. -/
def neverResetSet (D : ℕ) : Set NatExtTorus := {z | ∀ t : ℕ, hatS^[t] z ∉ resetSet D}

theorem iInter_noResetSet (D : ℕ) : ⋂ R, noResetSet D R = neverResetSet D := by
  ext z
  simp only [mem_iInter, mem_setOf_eq, neverResetSet, noResetSet]
  constructor
  · intro h t
    exact h (t + 1) t (Nat.lt_succ_self t)
  · intro h R t _
    exact h t

theorem measurableSet_neverResetSet (D : ℕ) : MeasurableSet (neverResetSet D) := by
  rw [← iInter_noResetSet]
  exact MeasurableSet.iInter fun R => measurableSet_noResetSet D R

/-! ## Mixing forces the never-reset set to be null -/

/-- The never-reset set is contained in every pullback of itself: a
forward orbit that avoids the reset set forever keeps avoiding it after
any number of steps.  This is an exact set inclusion, no measure
theory. -/
theorem neverResetSet_subset_preimage (D : ℕ) (m : ℕ) :
    neverResetSet D ⊆ hatS^[m] ⁻¹' neverResetSet D := by
  intro z hz t
  rw [← Function.iterate_add_apply]
  exact hz (t + m)

theorem neverResetSet_null (D : ℕ) : hatMu0 (neverResetSet D) = 0 := by
  have hmeas := measurableSet_neverResetSet D
  have hcorr : ∀ m : ℕ, hatMu0.real (neverResetSet D ∩ hatS^[m] ⁻¹' neverResetSet D)
      = hatMu0.real (neverResetSet D) := fun m => by
    rw [Set.inter_eq_self_of_subset_left (neverResetSet_subset_preimage D m)]
  have hmix := Lemma62.lemma_6_2_gauss_torus_mixing _ _ hmeas hmeas
  have heq : hatMu0.real (neverResetSet D)
      = hatMu0.real (neverResetSet D) * hatMu0.real (neverResetSet D) :=
    tendsto_nhds_unique (Tendsto.congr hcorr hmix) tendsto_const_nhds |>.symm
  -- the mass is `< 1`, because the reset set is missed and has positive mass
  have hlt : hatMu0.real (neverResetSet D) < 1 := by
    by_contra hcon
    push_neg at hcon
    have hle1 : hatMu0.real (neverResetSet D) ≤ 1 := by
      rw [measureReal_def]
      calc (hatMu0 (neverResetSet D)).toReal
          ≤ (hatMu0 Set.univ).toReal :=
            ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
        _ = 1 := by rw [measure_univ]; rfl
    have hB1 : hatMu0.real (neverResetSet D) = 1 := le_antisymm hle1 hcon
    have hμB : hatMu0 (neverResetSet D) = 1 := by
      rw [measureReal_def] at hB1
      exact (ENNReal.toReal_eq_one_iff _).mp hB1
    have hcompl : hatMu0 (neverResetSet D)ᶜ = 0 := by
      rw [measure_compl hmeas (measure_ne_top _ _), hμB, measure_univ, tsub_self]
    have hsub : resetSet D ⊆ (neverResetSet D)ᶜ := by
      intro z hz hcon2
      exact (hcon2 0) (by simpa using hz)
    have hzero : hatMu0 (resetSet D) = 0 := measure_mono_null hsub hcompl
    have hpos := resetSet_measure_pos D
    rw [measureReal_def, hzero] at hpos
    simp at hpos
  have hnn : 0 ≤ hatMu0.real (neverResetSet D) := measureReal_nonneg
  have hzero : hatMu0.real (neverResetSet D) = 0 := by nlinarith
  rw [measureReal_def] at hzero
  rcases (ENNReal.toReal_eq_zero_iff _).mp hzero with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

/-- Ergodicity and `μ̂₀(R) > 0` give `p_R → 0` (v5 lines 1286-1287);
mixing is used directly in place of ergodicity.  Statement
token-identical to `Kwon1002.noResetProb_tendsto_zero` in
`Section6Skeleton.lean`, which this module cannot fill in place (it
sits downstream); the `example` guard below keeps the two in sync. -/
theorem noResetProb_tendsto_zero (D : ℕ) :
    Tendsto (fun R => noResetProb D R) atTop (𝓝 0) := by
  have htend : Tendsto (fun R => hatMu0 (noResetSet D R)) atTop
      (𝓝 (hatMu0 (⋂ R, noResetSet D R))) := by
    have h := MeasureTheory.tendsto_measure_iInter_atTop (μ := hatMu0)
      (s := fun R => noResetSet D R)
      (fun R => (measurableSet_noResetSet D R).nullMeasurableSet)
      (noResetSet_antitone D) ⟨0, measure_ne_top _ _⟩
    exact h
  rw [iInter_noResetSet, neverResetSet_null] at htend
  have h0 : Tendsto (fun R => (hatMu0 (noResetSet D R)).toReal) atTop
      (𝓝 ((0 : ℝ≥0∞).toReal)) :=
    (ENNReal.tendsto_toReal (by simp)).comp htend
  simpa [noResetProb, measureReal_def] using h0

/-- Guard: the statement above is token-identical to the skeleton's
`Kwon1002.noResetProb_tendsto_zero`. -/
example : ∀ D : ℕ, Tendsto (fun R => noResetProb D R) atTop (𝓝 0) :=
  noResetProb_tendsto_zero

/-! ## Mixing implies ergodicity -/

/-- **`hatS` is ergodic for `μ̂₀`.**  Mathlib has `Ergodic` but no mixing
predicate and no mixing-to-ergodicity implication; the implication is
inlined: a strictly invariant measurable set `s` has
`s ∩ S⁻ᵐ s = s` for every `m`, so by Lemma 6.2 its mass satisfies
`μ̂₀(s) = μ̂₀(s)²`, hence is `0` or `1`. -/
theorem hatS_ergodic : Ergodic hatS hatMu0 := by
  refine ⟨Lemma62.hatS_measurePreserving, ⟨fun s hs hinv => ?_⟩⟩
  rw [eventuallyConst_set']
  have hiter : ∀ m : ℕ, hatS^[m] ⁻¹' s = s := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ', Set.preimage_comp, hinv, ih]
  have hcorr : ∀ m : ℕ, hatMu0.real (s ∩ hatS^[m] ⁻¹' s) = hatMu0.real s := fun m => by
    rw [hiter m, Set.inter_self]
  have hmix := Lemma62.lemma_6_2_gauss_torus_mixing s s hs hs
  have heq : hatMu0.real s = hatMu0.real s * hatMu0.real s :=
    (tendsto_nhds_unique (Tendsto.congr hcorr hmix) tendsto_const_nhds).symm
  have hcases : hatMu0.real s = 0 ∨ hatMu0.real s = 1 := by
    rcases mul_eq_zero.mp (show hatMu0.real s * (hatMu0.real s - 1) = 0 by nlinarith) with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hcases with h0 | h1
  · left
    rw [ae_eq_empty]
    rw [measureReal_def] at h0
    rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h | h
    · exact h
    · exact absurd h (measure_ne_top _ _)
  · right
    rw [ae_eq_univ]
    have hμ1 : hatMu0 s = 1 := by
      rw [measureReal_def] at h1
      exact (ENNReal.toReal_eq_one_iff _).mp h1
    rw [measure_compl hs (measure_ne_top _ _), hμ1, measure_univ, tsub_self]

/-! ## The invariant region of the full cocycle -/

/-- The region on which `hatS` and `hatSinv` are exactly mutually
inverse: base pair in `natExtGood`, torus pair represented in `[0,1)`. -/
def GoodT : Set NatExtTorus :=
  {z | z.1 ∈ natExtGood ∧ z.2.1 ∈ Ico (0 : ℝ) 1 ∧ z.2.2 ∈ Ico (0 : ℝ) 1}

theorem hatS_mem_goodT {z : NatExtTorus} (hz : z ∈ GoodT) : hatS z ∈ GoodT := by
  obtain ⟨hb, h1, h2⟩ := hz
  exact ⟨natExtMap_mem_good hb, h2, Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem hatSinv_mem_goodT {z : NatExtTorus} (hz : z ∈ GoodT) : hatSinv z ∈ GoodT := by
  obtain ⟨hb, h1, h2⟩ := hz
  exact ⟨natExtInv_mem_good hb, ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, h1⟩

theorem hatS_iterate_mem_goodT {z : NatExtTorus} (hz : z ∈ GoodT) (k : ℕ) :
    hatS^[k] z ∈ GoodT := by
  induction k with
  | zero => simpa using hz
  | succ k ih => rw [Function.iterate_succ_apply']; exact hatS_mem_goodT ih

theorem hatSinv_iterate_mem_goodT {z : NatExtTorus} (hz : z ∈ GoodT) (k : ℕ) :
    hatSinv^[k] z ∈ GoodT := by
  induction k with
  | zero => simpa using hz
  | succ k ih => rw [Function.iterate_succ_apply']; exact hatSinv_mem_goodT ih

theorem fract_fract_add (x y : ℝ) : Int.fract (Int.fract x + y) = Int.fract (x + y) := by
  have h : Int.fract x + y = x + y + ((-⌊x⌋ : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [h, Int.fract_add_intCast]

theorem fract_fract_sub (x y : ℝ) : Int.fract (Int.fract x - y) = Int.fract (x - y) := by
  have h : Int.fract x - y = x - y + ((-⌊x⌋ : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [h, Int.fract_add_intCast]

/-- On the good region the inverse cocycle undoes the cocycle exactly. -/
theorem hatSinv_hatS {z : NatExtTorus} (hz : z ∈ GoodT) : hatSinv (hatS z) = z := by
  obtain ⟨hb, h1, h2⟩ := hz
  have hdig : digit ((hatS z).1.2) 0 = digit z.1.1 0 := by
    show digit (((digit z.1.1 0 : ℕ) : ℝ) + z.1.2)⁻¹ 0 = digit z.1.1 0
    exact digit_inv_natCast_add (Ioo_subset_Ico_self hb.2.1)
  have hbase : natExtInv (hatS z).1 = z.1 := natExtInv_natExtMap_of_good hb
  have htor : Int.fract (Int.fract (z.2.1 - ((digit z.1.1 0 : ℕ) : ℝ) * z.2.2)
      + ((digit z.1.1 0 : ℕ) : ℝ) * z.2.2) = z.2.1 := by
    rw [fract_fract_add,
      show z.2.1 - ((digit z.1.1 0 : ℕ) : ℝ) * z.2.2 + ((digit z.1.1 0 : ℕ) : ℝ) * z.2.2
        = z.2.1 from by ring]
    exact Int.fract_eq_self.mpr ⟨h1.1, h1.2⟩
  show ((natExtInv (hatS z).1),
      Int.fract ((hatS z).2.2 + ((digit ((hatS z).1.2) 0 : ℕ) : ℝ) * (hatS z).2.1),
      (hatS z).2.1) = z
  rw [hdig]
  show (natExtInv (hatS z).1,
      Int.fract (Int.fract (z.2.1 - ((digit z.1.1 0 : ℕ) : ℝ) * z.2.2)
        + ((digit z.1.1 0 : ℕ) : ℝ) * z.2.2), z.2.2) = z
  rw [hbase, htor]

/-- On the good region the cocycle undoes the inverse cocycle exactly. -/
theorem hatS_hatSinv {z : NatExtTorus} (hz : z ∈ GoodT) : hatS (hatSinv z) = z := by
  obtain ⟨hb, h1, h2⟩ := hz
  have hdig : digit ((hatSinv z).1.1) 0 = digit z.1.2 0 := by
    show digit (((digit z.1.2 0 : ℕ) : ℝ) + z.1.1)⁻¹ 0 = digit z.1.2 0
    exact digit_inv_natCast_add (Ioo_subset_Ico_self hb.1)
  have hbase : natExtMap (hatSinv z).1 = z.1 := natExtMap_natExtInv_of_good hb
  have htor : Int.fract (Int.fract (z.2.2 + ((digit z.1.2 0 : ℕ) : ℝ) * z.2.1)
      - ((digit z.1.2 0 : ℕ) : ℝ) * z.2.1) = z.2.2 := by
    rw [fract_fract_sub,
      show z.2.2 + ((digit z.1.2 0 : ℕ) : ℝ) * z.2.1 - ((digit z.1.2 0 : ℕ) : ℝ) * z.2.1
        = z.2.2 from by ring]
    exact Int.fract_eq_self.mpr ⟨h2.1, h2.2⟩
  show ((natExtMap (hatSinv z).1), (hatSinv z).2.2,
      Int.fract ((hatSinv z).2.1 - ((digit ((hatSinv z).1.1) 0 : ℕ) : ℝ) * (hatSinv z).2.2)) = z
  rw [hdig]
  show (natExtMap (hatSinv z).1, z.2.1,
      Int.fract (Int.fract (z.2.2 + ((digit z.1.2 0 : ℕ) : ℝ) * z.2.1)
        - ((digit z.1.2 0 : ℕ) : ℝ) * z.2.1)) = z
  rw [hbase, htor]

/-- Forward iterates cancel backward iterates on the good region:
`S^j (S⁻ᵗ z) = S^{-(t-j)} z` for `j ≤ t`. -/
theorem hatS_iterate_hatSinv_iterate {z : NatExtTorus} (hz : z ∈ GoodT) :
    ∀ j t : ℕ, j ≤ t → hatS^[j] (hatSinv^[t] z) = hatSinv^[t - j] z := by
  intro j
  induction j with
  | zero => intro t _; simp
  | succ j ih =>
      intro t hjt
      have hj : j ≤ t := Nat.le_of_succ_le hjt
      rw [Function.iterate_succ_apply', ih t hj]
      have hsplit : t - j = (t - (j + 1)) + 1 := by omega
      rw [hsplit, Function.iterate_succ_apply',
        hatS_hatSinv (hatSinv_iterate_mem_goodT hz _)]

/-- Backward iterates of `S z` are backward iterates of `z`, one step
shorter, on the good region. -/
theorem hatSinv_iterate_hatS {z : NatExtTorus} (hz : z ∈ GoodT) (t : ℕ) (ht : 1 ≤ t) :
    hatSinv^[t] (hatS z) = hatSinv^[t - 1] z := by
  have hsplit : t = (t - 1) + 1 := by omega
  rw [hsplit, Function.iterate_succ_apply, hatSinv_hatS hz]
  congr 1

/-- `μ̂₀`-almost every point lies in the good region. -/
theorem hatMu0_ae_goodT : ∀ᵐ z ∂hatMu0, z ∈ GoodT := by
  have h1 := hatMu0_ae_natExtGood
  have hac : hatMu0 ≪ volume.restrict
      (((Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
        Set ((ℝ × ℝ) × ℝ × ℝ)) := by
    rw [hatMu0]
    exact withDensity_absolutelyContinuous _ _
  have h2 : ∀ᵐ z : NatExtTorus ∂hatMu0,
      z ∈ ((Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :=
    hac.ae_le (ae_restrict_mem Prop42.measurableSet_hatBox)
  filter_upwards [h1, h2] with z hzg hzb
  exact ⟨hzg, Ioo_subset_Ico_self hzb.2.1, Ioo_subset_Ico_self hzb.2.2⟩

/-! ## The consecutive-iterate contraction of the Gauss map -/

/-- `x · Tx ≤ 1/2` on `(0,1)`: either the first digit is `1`, and then
`x > 1/2` with `x · Tx = 1 - x < 1/2`, or the digit is at least `2`,
and then `x ≤ 1/2` already.  No irrationality is needed. -/
theorem mul_gaussMap_le_half {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    x * gaussMap x ≤ 1 / 2 := by
  have hx0 : 0 < x := hx.1
  have hinv1 : 1 < x⁻¹ := (one_lt_inv_iff₀).mpr ⟨hx0, hx.2⟩
  have hfl1 : 1 ≤ ⌊x⁻¹⌋ := by
    rw [Int.le_floor]
    exact_mod_cast hinv1.le
  rcases eq_or_lt_of_le hfl1 with h1 | h2
  · -- digit `1`: `x > 1/2`, product `= 1 - x`
    have hlt : x⁻¹ < 2 := by
      have h := Int.lt_floor_add_one x⁻¹
      rw [← h1] at h
      norm_num at h
      linarith
    have hg : gaussMap x = x⁻¹ - 1 := by
      rw [gaussMap, Int.fract, ← h1]
      norm_num
    have hxhalf : 1 / 2 < x := by
      have h2x : 2 * x > x⁻¹ * x := by
        exact mul_lt_mul_of_pos_right hlt hx0
      rw [inv_mul_cancel₀ (ne_of_gt hx0)] at h2x
      linarith
    rw [hg, mul_sub, mul_inv_cancel₀ (ne_of_gt hx0), mul_one]
    linarith
  · -- digit at least `2`: `x ≤ 1/2` and the fractional part is below `1`
    have hle2 : (2 : ℝ) ≤ x⁻¹ := by
      have h2' : (2 : ℤ) ≤ ⌊x⁻¹⌋ := h2
      calc (2 : ℝ) = ((2 : ℤ) : ℝ) := by norm_num
        _ ≤ (⌊x⁻¹⌋ : ℝ) := by exact_mod_cast h2'
        _ ≤ x⁻¹ := Int.floor_le _
    have hx2 : x ≤ 1 / 2 := by
      have h := mul_le_mul_of_nonneg_right hle2 hx0.le
      rw [inv_mul_cancel₀ (ne_of_gt hx0)] at h
      linarith
    calc x * gaussMap x ≤ x * 1 :=
          mul_le_mul_of_nonneg_left (Int.fract_lt_one _).le hx0.le
      _ = x := mul_one x
      _ ≤ 1 / 2 := hx2

/-! ## The stationary carry iteration and its absolute bound -/

/-- Push the carry forward `k` steps along the stationary orbit of `w`,
starting from `0`: the stationary analogue of `carryFrom`. -/
def iterCarry (w : NatExtTorus) : ℕ → ℤ
  | 0 => 0
  | k + 1 => carryMap (hatS^[k] w).1.1 (hatS^[k] w).2.1 (hatS^[k] w).2.2 (iterCarry w k)

theorem measurable_iterCarry (k : ℕ) : Measurable fun w => iterCarry w k := by
  induction k with
  | zero =>
      simp only [iterCarry]
      exact measurable_const
  | succ k ih =>
      have hcast : Measurable fun w : NatExtTorus => ((iterCarry w k : ℤ) : ℝ) :=
        (measurable_from_top (f := fun m : ℤ => (m : ℝ))).comp ih
      have hS : Measurable (hatS^[k]) := measurable_hatS.iterate k
      have hexpr : Measurable fun w : NatExtTorus =>
          (hatS^[k] w).1.1 * (((iterCarry w k : ℤ) : ℝ) + (hatS^[k] w).2.1)
            - (hatS^[k] w).2.2 :=
        ((hS.fst.fst).mul (hcast.add hS.snd.fst)).sub hS.snd.snd
      simpa [iterCarry, carryMap] using hexpr.ceil

/-- One-step lower bound: the carry map never goes negative from a
nonnegative carry when the torus coordinates are canonical. -/
theorem carryMap_nonneg {x r s : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) (hs : s < 1) {d : ℤ}
    (hd : 0 ≤ d) : 0 ≤ carryMap x r s d := by
  have harg : (-1 : ℝ) < x * ((d : ℝ) + r) - s := by
    have hd' : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have h := Int.le_ceil (x * ((d : ℝ) + r) - s)
  rw [carryMap]
  by_contra hcon
  push_neg at hcon
  have hle : (⌈x * ((d : ℝ) + r) - s⌉ : ℝ) ≤ -1 := by
    have : ⌈x * ((d : ℝ) + r) - s⌉ ≤ -1 := by omega
    exact_mod_cast this
  linarith

/-- One-step upper bound: `c' < x (c + 1) + 1`, real form. -/
theorem carryMap_lt {x r s : ℝ} (hx : 0 < x) (hr : r < 1) (hs : 0 ≤ s) (d : ℤ) :
    (carryMap x r s d : ℝ) < x * ((d : ℝ) + 1) + 1 := by
  have h := Int.ceil_lt_add_one (x * ((d : ℝ) + r) - s)
  rw [carryMap]
  have harg : x * ((d : ℝ) + r) - s ≤ x * ((d : ℝ) + 1) := by nlinarith
  linarith

/-- **The absolute carry bound along stationary orbits**: from carry `0`
the trajectory stays in `[0, 9]`.  Two steps contract by `1/2`
(`mul_gaussMap_le_half`), which beats the `+3` additive drift. -/
theorem iterCarry_bounds {w : NatExtTorus} (hw : w ∈ GoodT) (k : ℕ) :
    0 ≤ iterCarry w k ∧ iterCarry w k ≤ 9 := by
  -- coordinates along the orbit
  have hxk : ∀ j : ℕ, (hatS^[j] w).1.1 ∈ Ioo (0 : ℝ) 1 := fun j =>
    (hatS_iterate_mem_goodT hw j).1.1
  have hrk : ∀ j : ℕ, (hatS^[j] w).2.1 ∈ Ico (0 : ℝ) 1 := fun j =>
    (hatS_iterate_mem_goodT hw j).2.1
  have hsk : ∀ j : ℕ, (hatS^[j] w).2.2 ∈ Ico (0 : ℝ) 1 := fun j =>
    (hatS_iterate_mem_goodT hw j).2.2
  have hstep : ∀ j : ℕ, (hatS^[j + 1] w).1.1 = gaussMap ((hatS^[j] w).1.1) := fun j => by
    rw [Function.iterate_succ_apply']
    rfl
  -- the two-step induction, carried as `P k ∧ P (k+1)`
  have hlow : ∀ j : ℕ, 0 ≤ iterCarry w j → 0 ≤ iterCarry w (j + 1) := fun j hj =>
    carryMap_nonneg (hxk j).1.le (hrk j).1 (hsk j).2 hj
  have hup : ∀ j : ℕ, (iterCarry w (j + 1) : ℝ)
      < (hatS^[j] w).1.1 * ((iterCarry w j : ℝ) + 1) + 1 := fun j =>
    carryMap_lt (hxk j).1 (hrk j).2 (hsk j).1 _
  have hQ : ∀ k : ℕ, (0 ≤ iterCarry w k ∧ iterCarry w k ≤ 9)
      ∧ (0 ≤ iterCarry w (k + 1) ∧ iterCarry w (k + 1) ≤ 9) := by
    intro k
    induction k with
    | zero =>
        have hP0 : 0 ≤ iterCarry w 0 ∧ iterCarry w 0 ≤ 9 := by
          show (0 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 9
          norm_num
        refine ⟨hP0, hlow 0 hP0.1, ?_⟩
        have h1 := hup 0
        have hx1 := hxk 0
        have h00 : iterCarry w 0 = 0 := rfl
        rw [h00] at h1
        have hlt : (iterCarry w (0 + 1) : ℝ) < 2 := by
          push_cast at h1
          nlinarith [hx1.2, hx1.1]
        have hle : iterCarry w (0 + 1) < 2 := by exact_mod_cast hlt
        omega
    | succ k ih =>
        obtain ⟨hPk, hPk1⟩ := ih
        refine ⟨hPk1, hlow (k + 1) hPk1.1, ?_⟩
        -- the two raw inequalities
        have h1 := hup k
        have h2 := hup (k + 1)
        have hprod : (hatS^[k + 1] w).1.1 * (hatS^[k] w).1.1 ≤ 1 / 2 := by
          rw [hstep k, mul_comm]
          exact mul_gaussMap_le_half (hxk k)
        have hx1 := hxk k
        have hx2 := hxk (k + 1)
        have hc0 : (0 : ℝ) ≤ (iterCarry w k : ℝ) := by exact_mod_cast hPk.1
        have hc9 : (iterCarry w k : ℝ) ≤ 9 := by exact_mod_cast hPk.2
        have hc10 : (0 : ℝ) ≤ (iterCarry w (k + 1) : ℝ) := by exact_mod_cast hPk1.1
        have hmul1 : (hatS^[k + 1] w).1.1 * (iterCarry w (k + 1) : ℝ)
            ≤ (hatS^[k + 1] w).1.1
              * ((hatS^[k] w).1.1 * ((iterCarry w k : ℝ) + 1) + 1) :=
          mul_le_mul_of_nonneg_left h1.le hx2.1.le
        have hmul2 : ((hatS^[k + 1] w).1.1 * (hatS^[k] w).1.1) * ((iterCarry w k : ℝ) + 1)
            ≤ (1 / 2) * ((iterCarry w k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hprod (by linarith)
        -- chain: c_{k+2} < x'(c_{k+1}+1)+1 ≤ x'x(c_k+1) + 2x' + 1 ≤ (c_k+1)/2 + 2x' + 1 < 8
        have hfin : (iterCarry w (k + 1 + 1) : ℝ) < 8 := by
          nlinarith [h2, hmul1, hmul2, hx2.2, hx2.1.le, hc9]
        have hle7 : iterCarry w (k + 1 + 1) < 8 := by exact_mod_cast hfin
        omega
  exact (hQ k).1

/-! ## The backward hitting time and the carry graph -/

/-- The backward orbit hits the reset set at time `n + 1`. -/
def hitPred (z : NatExtTorus) (n : ℕ) : Prop := hatSinv^[n + 1] z ∈ resetSet 9

theorem measurableSet_hitPred (n : ℕ) : MeasurableSet {z : NatExtTorus | hitPred z n} :=
  (measurable_hatSinv.iterate (n + 1)) (measurableSet_resetSet 9)

open scoped Classical in
/-- The raw carry graph: restart the carry at `0` one step after the most
recent backward visit to the reset set, and push it forward to the
present.  Junk value `0` on the (null) set of points whose backward
orbit never resets. -/
def rawD (z : NatExtTorus) : ℤ :=
  if h : ∃ n, hitPred z n then iterCarry (hatSinv^[Nat.find h] z) (Nat.find h) else 0

open scoped Classical in
theorem measurable_rawD : Measurable rawD := by
  have hFmeas : ∀ n : ℕ, Measurable fun z => iterCarry (hatSinv^[n] z) n := fun n =>
    (measurable_iterCarry n).comp (measurable_hatSinv.iterate n)
  apply measurable_to_countable'
  intro d
  show MeasurableSet {z : NatExtTorus | rawD z = d}
  have hdecomp : {z : NatExtTorus | rawD z = d}
      = ((⋂ n : ℕ, {z | hitPred z n}ᶜ) ∩ {_z : NatExtTorus | (0 : ℤ) = d})
        ∪ ⋃ n : ℕ, (({z | hitPred z n} ∩ ⋂ m : ℕ, ⋂ _ : m < n, {z | hitPred z m}ᶜ)
            ∩ {z | iterCarry (hatSinv^[n] z) n = d}) := by
    ext z
    simp only [mem_union, mem_inter_iff, mem_iInter, mem_iUnion, mem_setOf_eq,
      mem_compl_iff]
    by_cases h : ∃ n, hitPred z n
    · rw [show rawD z = iterCarry (hatSinv^[Nat.find h] z) (Nat.find h) from dif_pos h]
      constructor
      · intro hd
        exact Or.inr ⟨Nat.find h, ⟨Nat.find_spec h, fun m hm => Nat.find_min h hm⟩, hd⟩
      · rintro (⟨hno, _⟩ | ⟨n, ⟨hn, hmin⟩, hd⟩)
        · obtain ⟨n, hn⟩ := h
          exact absurd hn (hno n)
        · have heq : Nat.find h = n :=
            (Nat.find_eq_iff h).mpr ⟨hn, fun m hm => hmin m hm⟩
          rw [heq]
          exact hd
    · rw [show rawD z = 0 from dif_neg h]
      push_neg at h
      constructor
      · intro hd
        exact Or.inl ⟨fun n => h n, hd⟩
      · rintro (⟨_, hd⟩ | ⟨n, ⟨hn, _⟩, _⟩)
        · exact hd
        · exact absurd hn (h n)
  rw [hdecomp]
  refine MeasurableSet.union ?_ (MeasurableSet.iUnion fun n => ?_)
  · exact (MeasurableSet.iInter fun n => (measurableSet_hitPred n).compl).inter
      (MeasurableSet.const _)
  · exact ((measurableSet_hitPred n).inter
      (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
        (measurableSet_hitPred m).compl)).inter
      ((hFmeas n) (measurableSet_singleton d))

/-- The clamped carry graph: `rawD` truncated into `[0, 9]`, so the
global bound holds at every point, not merely almost everywhere. -/
def dstar (z : NatExtTorus) : ℤ := max 0 (min 9 (rawD z))

theorem measurable_dstar : Measurable dstar :=
  (measurable_from_top (f := fun d : ℤ => max 0 (min 9 d))).comp measurable_rawD

theorem dstar_bounds (z : NatExtTorus) : 0 ≤ dstar z ∧ dstar z ≤ 9 :=
  ⟨le_max_left 0 _, max_le (by norm_num) (min_le_left 9 _)⟩

open scoped Classical in
/-- On the good region, wherever the backward orbit resets, the raw graph
value is the stationary carry from the reset, so it obeys the absolute
bound. -/
theorem rawD_bounds {z : NatExtTorus} (hz : z ∈ GoodT) (hhit : ∃ n, hitPred z n) :
    0 ≤ rawD z ∧ rawD z ≤ 9 := by
  rw [show rawD z = iterCarry (hatSinv^[Nat.find hhit] z) (Nat.find hhit) from dif_pos hhit]
  exact iterCarry_bounds (hatSinv_iterate_mem_goodT hz _) _

open scoped Classical in
theorem dstar_eq_rawD {z : NatExtTorus} (hz : z ∈ GoodT) (hhit : ∃ n, hitPred z n) :
    dstar z = rawD z := by
  obtain ⟨h0, h9⟩ := rawD_bounds hz hhit
  rw [dstar, min_eq_right h9, max_eq_right h0]

open scoped Classical in
/-- The good region passes the backward hitting property forward. -/
theorem hitPred_hatS {z : NatExtTorus} (hz : z ∈ GoodT) (hhit : ∃ n, hitPred z n) :
    ∃ n, hitPred (hatS z) n := by
  by_cases hzR : z ∈ resetSet 9
  · refine ⟨0, ?_⟩
    show hatSinv^[1] (hatS z) ∈ resetSet 9
    rw [show hatSinv^[1] (hatS z) = hatSinv (hatS z) from rfl, hatSinv_hatS hz]
    exact hzR
  · obtain ⟨n, hn⟩ := hhit
    refine ⟨n + 1, ?_⟩
    show hatSinv^[n + 1 + 1] (hatS z) ∈ resetSet 9
    rw [hatSinv_iterate_hatS hz (n + 1 + 1) (by omega),
      show n + 1 + 1 - 1 = n + 1 from by omega]
    exact hn

open scoped Classical in
/-- **The graph equation for the raw carry graph**, pointwise on the good
region with a backward reset: `rawD (S z) = φ_z (rawD z)`. -/
theorem rawD_succ {z : NatExtTorus} (hz : z ∈ GoodT) (hhit : ∃ n, hitPred z n) :
    rawD (hatS z) = carryMap z.1.1 z.2.1 z.2.2 (rawD z) := by
  have hhitS : ∃ n, hitPred (hatS z) n := hitPred_hatS hz hhit
  by_cases hzR : z ∈ resetSet 9
  · -- the carry resets: both sides are `0`
    have hfind0 : Nat.find hhitS = 0 := by
      rw [Nat.find_eq_zero]
      show hatSinv^[1] (hatS z) ∈ resetSet 9
      rw [show hatSinv^[1] (hatS z) = hatSinv (hatS z) from rfl, hatSinv_hatS hz]
      exact hzR
    have hlhs : rawD (hatS z) = 0 := by
      rw [show rawD (hatS z)
          = iterCarry (hatSinv^[Nat.find hhitS] (hatS z)) (Nat.find hhitS) from
          dif_pos hhitS, hfind0]
      rfl
    have hrhs : carryMap z.1.1 z.2.1 z.2.2 (rawD z) = 0 := by
      obtain ⟨h0, h9⟩ := rawD_bounds hz hhit
      exact carryMap_eq_zero_of_mem_resetSet 9 z hzR hz.1.1.1.le hz.2.1.1 hz.2.1.2
        (rawD z) h0 h9
    rw [hlhs, hrhs]
  · -- no reset between `z` and `S z`: the hitting time advances by one
    set n₀ := Nat.find hhit with hn₀
    have hfindS : Nat.find hhitS = n₀ + 1 := by
      rw [Nat.find_eq_iff]
      constructor
      · show hatSinv^[n₀ + 2] (hatS z) ∈ resetSet 9
        rw [hatSinv_iterate_hatS hz (n₀ + 2) (by omega),
          show n₀ + 2 - 1 = n₀ + 1 from by omega]
        exact Nat.find_spec hhit
      · intro m hm
        rcases Nat.eq_zero_or_pos m with hm0 | hm1
        · subst hm0
          show ¬ hatSinv^[1] (hatS z) ∈ resetSet 9
          rw [show hatSinv^[1] (hatS z) = hatSinv (hatS z) from rfl, hatSinv_hatS hz]
          exact hzR
        · show ¬ hatSinv^[m + 1] (hatS z) ∈ resetSet 9
          rw [hatSinv_iterate_hatS hz (m + 1) (by omega),
            show m + 1 - 1 = m from by omega]
          have hmlt : m - 1 < n₀ := by omega
          have hnot := Nat.find_min hhit hmlt
          intro hcon
          apply hnot
          show hatSinv^[m - 1 + 1] z ∈ resetSet 9
          rw [show m - 1 + 1 = m from by omega]
          exact hcon
    have hlhs : rawD (hatS z)
        = iterCarry (hatSinv^[n₀] z) (n₀ + 1) := by
      rw [show rawD (hatS z)
          = iterCarry (hatSinv^[Nat.find hhitS] (hatS z)) (Nat.find hhitS) from
          dif_pos hhitS, hfindS,
        hatSinv_iterate_hatS hz (n₀ + 1) (by omega),
        show n₀ + 1 - 1 = n₀ from by omega]
    have hcarry : iterCarry (hatSinv^[n₀] z) (n₀ + 1)
        = carryMap z.1.1 z.2.1 z.2.2 (iterCarry (hatSinv^[n₀] z) n₀) := by
      have hret : hatS^[n₀] (hatSinv^[n₀] z) = z :=
        hatS_iterate_hatSinv_iterate hz n₀ n₀ le_rfl |>.trans (by simp)
      show carryMap (hatS^[n₀] (hatSinv^[n₀] z)).1.1 (hatS^[n₀] (hatSinv^[n₀] z)).2.1
          (hatS^[n₀] (hatSinv^[n₀] z)).2.2 (iterCarry (hatSinv^[n₀] z) n₀)
        = carryMap z.1.1 z.2.1 z.2.2 (iterCarry (hatSinv^[n₀] z) n₀)
      rw [hret]
    have hraw : rawD z = iterCarry (hatSinv^[n₀] z) n₀ := dif_pos hhit
    rw [hlhs, hcarry, hraw]

/-- Almost every point has a backward reset time: the never-reset event
of the *backward* orbit is carried onto the forward no-reset sets by the
measure-preserving inverse cocycle, and those have vanishing measure. -/
theorem ae_hitPred : ∀ᵐ z ∂hatMu0, ∃ n, hitPred z n := by
  rw [ae_iff]
  set N : Set NatExtTorus := {z | ¬ ∃ n, hitPred z n} with hN
  have hkey : ∀ R : ℕ, N ∩ GoodT ⊆ hatSinv^[R] ⁻¹' noResetSet 9 R := by
    intro R z hz
    obtain ⟨hzN, hzG⟩ := hz
    intro t ht
    rw [hatS_iterate_hatSinv_iterate hzG t R ht.le]
    have hR : R - t = (R - t - 1) + 1 := by omega
    rw [hR]
    rw [hN, mem_setOf_eq] at hzN
    push_neg at hzN
    exact hzN (R - t - 1)
  have hbound : ∀ R : ℕ, hatMu0 (N ∩ GoodT) ≤ hatMu0 (noResetSet 9 R) := by
    intro R
    calc hatMu0 (N ∩ GoodT) ≤ hatMu0 (hatSinv^[R] ⁻¹' noResetSet 9 R) :=
          measure_mono (hkey R)
      _ = hatMu0 (noResetSet 9 R) :=
          (hatSinv_measurePreserving.iterate R).measure_preimage
            (measurableSet_noResetSet 9 R).nullMeasurableSet
  have htend : Tendsto (fun R => hatMu0 (noResetSet 9 R)) atTop (𝓝 0) := by
    have h := MeasureTheory.tendsto_measure_iInter_atTop (μ := hatMu0)
      (s := fun R => noResetSet 9 R)
      (fun R => (measurableSet_noResetSet 9 R).nullMeasurableSet)
      (noResetSet_antitone 9) ⟨0, measure_ne_top _ _⟩
    rw [iInter_noResetSet, neverResetSet_null] at h
    exact h
  have hNG : hatMu0 (N ∩ GoodT) = 0 := by
    have hle : hatMu0 (N ∩ GoodT) ≤ 0 :=
      ge_of_tendsto htend (Eventually.of_forall hbound)
    exact le_antisymm hle (zero_le _)
  have hGc : hatMu0 GoodTᶜ = 0 := by
    have h := hatMu0_ae_goodT
    rwa [ae_iff] at h
  have hcover : N ⊆ (N ∩ GoodT) ∪ GoodTᶜ := by
    intro z hz
    by_cases hg : z ∈ GoodT
    · exact Or.inl ⟨hz, hg⟩
    · exact Or.inr hg
  refine le_antisymm ?_ (zero_le _)
  calc hatMu0 N ≤ hatMu0 ((N ∩ GoodT) ∪ GoodTᶜ) := measure_mono hcover
    _ ≤ hatMu0 (N ∩ GoodT) + hatMu0 GoodTᶜ := measure_union_le _ _
    _ = 0 := by rw [hNG, hGc, add_zero]

/-- **(56)** The stationary carry extension is a measurable invariant
graph `d_*` with `d_*(Sz) = φ_z(d_*(z))` (v5 lines 1269-1279).
Statement token-identical to `Kwon1002.exists_carry_graph` in
`Section6Skeleton.lean`; the `example` guard below keeps them in sync. -/
theorem exists_carry_graph :
    ∃ D : ℕ, ∃ dstar : NatExtTorus → ℤ, Measurable dstar ∧
      (∀ z, 0 ≤ dstar z ∧ dstar z ≤ (D : ℤ)) ∧
      (∀ᵐ z ∂hatMu0, dstar (hatS z) = carryMap z.1.1 z.2.1 z.2.2 (dstar z)) := by
  refine ⟨9, dstar, measurable_dstar, fun z => ?_, ?_⟩
  · have h := dstar_bounds z
    exact ⟨h.1, by exact_mod_cast h.2⟩
  · filter_upwards [hatMu0_ae_goodT, ae_hitPred] with z hzG hzH
    rw [dstar_eq_rawD (hatS_mem_goodT hzG) (hitPred_hatS hzG hzH),
      dstar_eq_rawD hzG hzH]
    exact rawD_succ hzG hzH

/-- Guard: the statement above is token-identical to the skeleton's
`Kwon1002.exists_carry_graph`. -/
example : ∃ D : ℕ, ∃ dstar : NatExtTorus → ℤ, Measurable dstar ∧
    (∀ z, 0 ≤ dstar z ∧ dstar z ≤ (D : ℤ)) ∧
    (∀ᵐ z ∂hatMu0, dstar (hatS z) = carryMap z.1.1 z.2.1 z.2.2 (dstar z)) :=
  exists_carry_graph

end

end CarryGraph

end Kwon1002
