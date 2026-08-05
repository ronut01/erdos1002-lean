import Kwon1002.Section6Skeleton
import Kwon1002.TupleInputs
import Kwon1002.P42Cases
import Kwon1002.V5Identity31
import Kwon1002.V5Lemma33
import Kwon1002.DigitTail
import Kwon1002.AntiConcentration

/-!
# Lemma 6.3 of manuscript version 5: the selection step, and a defect in its
current rendering

Targets of this pass, all four taken from `Kwon1002/Section6Skeleton.lean` and
reproduced here token for token (each reproduction is machine-checked against
the skeleton by an `example`, see the "statement identity" blocks):

* `exists_admissible_kappa_delta`        (skeleton line 327), **proved**;
* `lemma_6_3_good_cylinder_selection`    (skeleton line 347), **refuted**:
  the statement as written is false for every `κ` and every `δ`, see
  `not_goodCylinderSelection`, and corrected statements are supplied and
  proved;
* `lemma_6_3_cylinder_character_step`    (skeleton line 361), reduced to a
  pure phase sum by `eval_actualWindow_phase` (proved), otherwise open;
* `lemma_6_3_full_state_transfer`        (skeleton line 371), open.

Version 5 lines 1176-1245.

## Finding: `lemma_6_3_good_cylinder_selection` is false as stated

The skeleton renders the selection step of version 5 lines 1186-1196 as

```
∃ C c, 0 < C ∧ 0 < c ∧ ∀ᶠ n, ∀ j ∈ J_n,
  ∃ E, MeasurableSet E ∧ P(E) ≤ C e^{-cH} ∧
    ∀ α ∈ (0,1) \ E, Irrational α →
      e^{λj-δH} ≤ q_j ∧ ∀ A B : ℤ, (A,B) ≠ (0,0) → e^{-κH} q_j ≤ |A q_j - B q_{j-1}|
```

The exceptional set `E` is chosen **before** the pair `(A, B)`, so the
conclusion asks for one set of small measure off which the anti-concentration
bound holds *simultaneously for every* nonzero integer pair.  No such set
exists, and the failure is not delicate: take

`(A, B) = (q_{j-1}, q_j)`,

which is a nonzero pair whenever `q_j ≥ 1`, that is for every irrational
`α ∈ (0,1)`.  For that pair `A q_j - B q_{j-1} = q_{j-1} q_j - q_j q_{j-1} = 0`,
so the required bound reads `e^{-κH} q_j ≤ 0`, which is false.  Hence the
complement `(0,1) \ E` contains no irrational number at all, `E` has full
measure `1`, and `1 ≤ C e^{-cH}` for all large `n`, contradicting `c > 0`.
`not_goodCylinderSelection` is exactly this argument, machine-checked; it needs
no hypothesis on `κ`, `δ`, so in particular the compatibility constraint
`κ + 3δ < 80λ` is not what fails.

The manuscript is not making this claim.  Version 5 line 1191 says only that
"the bound there is uniform in the nonzero pair `(A_w, B_w)`", and the pairs it
ranges over are the finitely many values `(A_w, B_w)` attached to the finitely
many local words `w` in the support of the test, one union of complete
cylinders being removed for each.  Uniformity there is a statement about the
*constants* in the measure bound, not about a single exceptional set.  The
corrected renderings are

* `good_cylinder_selection_antiConc`, one nonzero pair at a time, and
* `good_cylinder_selection_finite`, a finite family `S` of nonzero pairs with
  the measure bound scaling as `#S`,

both proved outright here from `V5Lemma33.shrinking_anti_concentration_v5_exp`.

## Second, softer finding: the shape of the measure bound

Version 5 discards two unions in this step.  The anti-concentration union has
mass `O(e^{-κH} + F_{j+1}^{-2}) = O(e^{-cH})` (line 1193), but the union coming
from the local `q`-estimate has mass `O(e^{-c_δ L^{1/2}})` (line 1201).  Since
`H = L^{3/4}`, `e^{-c L^{1/2}}` is much larger than `e^{-cH}`, so a total bound
of the form `C e^{-cH}` is strictly stronger than what version 5's proof
yields.  The honest shape is `C (e^{-cH} + e^{-c L^{1/2}})`, which is what
`lemma_6_3_good_cylinder_selection_corrected` carries.  Only the
anti-concentration half is proved unconditionally; the `q`-estimate half is the
manuscript's display (20), recorded in the tree as the predicate
`Kwon1002.P42Cases.Display20` and, as documented there, absent from this
development and from the vendored substrate.  It is therefore carried as a
hypothesis rather than assumed.

## Inputs consumed

Proved results used as inputs, none of them reproved:

* `Kwon1002.V5Lemma33.shrinking_anti_concentration_v5_exp` (Lemma 3.3 at the
  version 5 constants, uniform in the nonzero pair, no restriction on `η`);
* `Kwon1002.V5Identity31.window_character_phase_v5` (identity (31) at the full
  version 5 range `t = -R-1, …, R`, with the version 5 phase formula);
* `Kwon1002.denom_pos_AC`, `Kwon1002.P42Cases.tendsto_Hscale`,
  `Kwon1002.TupleInputs.eventually_good`, `Kwon1002.TupleInputs.bulkJ_eq_Ico`,
  `Kwon1002.TupleInputs.aIdx_le_bIdx`, `Kwon1002.TupleInputs.Hscale_ge_one`.

Sorried results consumed: **none** in any proof.  The `example`s marked
"statement identity" elaborate the skeleton's sorried theorems as *terms*,
purely to check that the reproductions here have the same elaborated `Prop`;
nothing below depends on them.

Measurability of `α ↦ q_j(α)` is nowhere needed: every discarded set is
replaced by its measurable hull `toMeasurable`, which has the same measure and
only enlarges the set, hence only strengthens the retained conclusion.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace Lemma63

noncomputable section

/-! ## Target 1: the compatibility constraint `κ + 3δ < 80λ` -/

/-- The compatibility constraint `κ + 3δ < 80λ` of v5 line 1190 is
satisfiable.  (`80λ ≈ 94.9`, so there is a great deal of room; the
constraint only becomes binding through the constants of Lemma 3.3 and
of the local `q`-estimate, which are not part of this statement.) -/
theorem exists_admissible_kappa_delta :
    ∃ κ δ : ℝ, 0 < κ ∧ 0 < δ ∧ κ + 3 * δ < 80 * lyapunov := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlam : 0 < lyapunov := by
    unfold lyapunov
    have hp : 0 < Real.pi ^ 2 := by positivity
    exact div_pos hp (by linarith)
  exact ⟨lyapunov, lyapunov, hlam, hlam, by linarith⟩

/-- Statement identity: the reproduction above is the skeleton's statement. -/
example : @_root_.Kwon1002.exists_admissible_kappa_delta
    = @exists_admissible_kappa_delta := rfl

/-! ## Shared measure bookkeeping -/

/-- Any subset of the unit interval has Lebesgue measure at most `1`. -/
lemma volume_le_one_of_subset_unit {S : Set ℝ} (hS : S ⊆ Ioo (0 : ℝ) 1) :
    volume S ≤ 1 := by
  have h : volume S ≤ volume (Ioo (0 : ℝ) 1) := measure_mono hS
  rwa [Real.volume_Ioo, show (1 : ℝ) - 0 = 1 by ring, ENNReal.ofReal_one] at h

/-- The restricted measure of any set is at most `1`. -/
lemma restrict_le_one (t : Set ℝ) : volume.restrict (Ioo (0 : ℝ) 1) t ≤ 1 := by
  calc volume.restrict (Ioo (0 : ℝ) 1) t
      ≤ volume.restrict (Ioo (0 : ℝ) 1) univ := measure_mono (subset_univ t)
    _ = volume (Ioo (0 : ℝ) 1) := Measure.restrict_apply_univ _
    _ = 1 := by rw [Real.volume_Ioo, show (1 : ℝ) - 0 = 1 by ring, ENNReal.ofReal_one]

lemma restrict_ne_top (t : Set ℝ) : volume.restrict (Ioo (0 : ℝ) 1) t ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (restrict_le_one t)

/-- Repackaging of a real bound on the restricted measure as an `ℝ≥0∞` bound. -/
lemma restrict_le_ofReal {t : Set ℝ} {b : ℝ}
    (hb : (volume.restrict (Ioo (0 : ℝ) 1)).real t ≤ b) :
    volume.restrict (Ioo (0 : ℝ) 1) t ≤ ENNReal.ofReal b := by
  rw [← ENNReal.ofReal_toReal (restrict_ne_top t)]
  exact ENNReal.ofReal_le_ofReal (by rw [← measureReal_def]; exact hb)

/-- Transport of a Lebesgue bound on a subset of `(0,1)` to the measurable hull
and to the restricted measure. -/
lemma restrict_real_toMeasurable_le {S : Set ℝ} (hS : S ⊆ Ioo (0 : ℝ) 1) {b : ℝ}
    (hb : (volume S).toReal ≤ b) :
    (volume.restrict (Ioo (0 : ℝ) 1)).real (toMeasurable volume S) ≤ b := by
  have hne : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (volume_le_one_of_subset_unit hS)
  have h2 : volume (toMeasurable volume S ∩ Ioo (0 : ℝ) 1) ≤ volume S := by
    calc volume (toMeasurable volume S ∩ Ioo (0 : ℝ) 1)
        ≤ volume (toMeasurable volume S) := measure_mono Set.inter_subset_left
      _ = volume S := measure_toMeasurable S
  rw [measureReal_def, Measure.restrict_apply (measurableSet_toMeasurable volume S)]
  exact (ENNReal.toReal_mono hne h2).trans hb

/-- Subadditivity of the restricted measure on a union of two sets. -/
lemma restrict_real_union_le {E₁ E₂ : Set ℝ} {b₁ b₂ : ℝ} (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hE₁ : (volume.restrict (Ioo (0 : ℝ) 1)).real E₁ ≤ b₁)
    (hE₂ : (volume.restrict (Ioo (0 : ℝ) 1)).real E₂ ≤ b₂) :
    (volume.restrict (Ioo (0 : ℝ) 1)).real (E₁ ∪ E₂) ≤ b₁ + b₂ := by
  have hchain : volume.restrict (Ioo (0 : ℝ) 1) (E₁ ∪ E₂) ≤ ENNReal.ofReal (b₁ + b₂) := by
    rw [ENNReal.ofReal_add hb₁ hb₂]
    exact (measure_union_le _ _).trans
      (add_le_add (restrict_le_ofReal hE₁) (restrict_le_ofReal hE₂))
  have h := ENNReal.toReal_mono (by simp) hchain
  rw [measureReal_def]
  rwa [ENNReal.toReal_ofReal (by linarith)] at h

/-- The bulk index `j` is at least `1` and dominates the scale `H`. -/
lemma bulk_index_bounds {n j : ℕ} (hL : (1 : ℝ) ≤ Lnorm n) (hj : j ∈ bulkJ n) :
    1 ≤ j ∧ Hscale n ≤ (j : ℝ) := by
  have hH1 : (1 : ℝ) ≤ Hscale n := TupleInputs.Hscale_ge_one hL
  have hjH : 200 * Hscale n ≤ (j : ℝ) := by
    simp only [bulkJ, Finset.mem_filter, Finset.mem_range] at hj
    exact hj.2.1
  refine ⟨?_, by linarith⟩
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    norm_num at hjH
    linarith
  · exact h

/-! ## Target 2: the good cylinder selection

First the skeleton's statement, reproduced token for token as a `Prop`, then
its refutation, then the corrected forms. -/

/-- Token-identical reproduction of the conclusion of
`Kwon1002.lemma_6_3_good_cylinder_selection`. -/
def GoodCylinderSelection (κ δ : ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
    ∃ E : Set ℝ, MeasurableSet E ∧
      (volume.restrict (Ioo (0 : ℝ) 1)).real E ≤ C * Real.exp (-c * Hscale n) ∧
      ∀ α ∈ Ioo (0 : ℝ) 1 \ E, Irrational α →
        Real.exp (lyapunov * j - δ * Hscale n) ≤ (denom α j : ℝ) ∧
        ∀ A B : ℤ, (A, B) ≠ (0, 0) →
          Real.exp (-κ * Hscale n) * (denom α j : ℝ) ≤ |(Qfreq α j B A : ℝ)|

/-- Statement identity: `GoodCylinderSelection` is the skeleton's statement.
This `example` elaborates the skeleton's sorried theorem as a term; it is a
type check only, and nothing below uses it. -/
example : ∀ (κ δ : ℝ), 0 < κ → 0 < δ → κ + 3 * δ < 80 * lyapunov →
    GoodCylinderSelection κ δ :=
  _root_.Kwon1002.lemma_6_3_good_cylinder_selection

/-- The defeating pair.  `Q_j` of (33) at `(A, B) = (q_{j-1}, q_j)` is
`q_{j-1} q_j - q_j q_{j-1} = 0`; recall `Qfreq α j r s = s q_j - r q_{j-1}`,
so the manuscript's pair `(A, B)` enters as `Qfreq α j B A`. -/
lemma qfreq_denom_pair (α : ℝ) (j : ℕ) :
    Qfreq α j (denom α j : ℤ) (denom α (j - 1) : ℤ) = 0 := by
  simp only [Qfreq]
  ring

/-- **The finding.**  The skeleton's rendering of the selection step of
Lemma 6.3 is false, for every `κ` and every `δ`.  See the module docstring:
the exceptional set is quantified before the pair `(A, B)`, and the pair
`(q_{j-1}, q_j)` kills the conclusion at every irrational `α ∈ (0,1)`. -/
theorem not_goodCylinderSelection (κ δ : ℝ) : ¬ GoodCylinderSelection κ δ := by
  rintro ⟨C, c, hC, hc, hev⟩
  have hHtop : Tendsto (fun n : ℕ => Hscale n) atTop atTop := P42Cases.tendsto_Hscale
  have hexp : Tendsto (fun n : ℕ => C * Real.exp (-c * Hscale n)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => c * Hscale n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc hHtop
    have h1 : Tendsto (fun n : ℕ => -c * Hscale n) atTop atBot := by
      have h3 : Tendsto ((fun x : ℝ => -x) ∘ fun n : ℕ => c * Hscale n) atTop atBot :=
        tendsto_neg_atTop_atBot.comp h2
      simp only [Function.comp_def] at h3
      simpa only [neg_mul] using h3
    have h3 : Tendsto (fun n : ℕ => Real.exp (-c * Hscale n)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h1
    simpa using h3.const_mul C
  have hsmall : ∀ᶠ n : ℕ in atTop, C * Real.exp (-c * Hscale n) < 1 :=
    Filter.Tendsto.eventually_lt_const (by norm_num) hexp
  obtain ⟨n, ⟨hn1, hn2⟩, hn3⟩ := ((hev.and hsmall).and TupleInputs.eventually_good).exists
  -- the bulk is a nonempty integer interval for this `n`
  have hab : TupleInputs.aIdx n ≤ TupleInputs.bIdx n :=
    TupleInputs.aIdx_le_bIdx hn3.1 hn3.2
  have hj : TupleInputs.aIdx n ∈ bulkJ n := by
    rw [TupleInputs.bulkJ_eq_Ico hn3.1 hn3.2]
    exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  set j : ℕ := TupleInputs.aIdx n with hjdef
  obtain ⟨E, hEmeas, hEbound, hEgood⟩ := hn1 j hj
  -- every irrational point of `(0,1)` must lie in `E`
  have hsub : Ioo (0 : ℝ) 1 \ Set.range ((↑) : ℚ → ℝ) ⊆ E ∩ Ioo (0 : ℝ) 1 := by
    rintro α ⟨hα, hirr⟩
    refine ⟨?_, hα⟩
    by_contra hαE
    obtain ⟨-, h2⟩ := hEgood α ⟨hα, hαE⟩ hirr
    have hqj : 0 < denom α j := denom_pos_AC hα hirr j
    have hqjR : (0 : ℝ) < (denom α j : ℝ) := by exact_mod_cast hqj
    have hne : (((denom α (j - 1) : ℤ)), ((denom α j : ℤ))) ≠ ((0 : ℤ), (0 : ℤ)) := by
      intro h
      rw [Prod.mk.injEq] at h
      have h0 : (denom α j : ℤ) = 0 := h.2
      omega
    have h3 := h2 (denom α (j - 1) : ℤ) (denom α j : ℤ) hne
    rw [qfreq_denom_pair] at h3
    simp only [Int.cast_zero, abs_zero] at h3
    nlinarith [Real.exp_pos (-κ * Hscale n), hqjR]
  -- hence `E` has full measure inside `(0,1)`
  have hQ : volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
    Set.Countable.measure_zero (Set.countable_range _) volume
  have hdiff : volume (Ioo (0 : ℝ) 1 \ Set.range ((↑) : ℚ → ℝ)) = 1 := by
    rw [measure_diff_null hQ, Real.volume_Ioo, show (1 : ℝ) - 0 = 1 by ring,
      ENNReal.ofReal_one]
  have hle : (1 : ℝ≥0∞) ≤ volume (E ∩ Ioo (0 : ℝ) 1) := by
    calc (1 : ℝ≥0∞) = volume (Ioo (0 : ℝ) 1 \ Set.range ((↑) : ℚ → ℝ)) := hdiff.symm
      _ ≤ volume (E ∩ Ioo (0 : ℝ) 1) := measure_mono hsub
  have hupper : volume (E ∩ Ioo (0 : ℝ) 1) ≤ 1 :=
    volume_le_one_of_subset_unit Set.inter_subset_right
  have heq : volume (E ∩ Ioo (0 : ℝ) 1) = 1 := le_antisymm hupper hle
  have hone : (volume.restrict (Ioo (0 : ℝ) 1)).real E = 1 := by
    rw [measureReal_def, Measure.restrict_apply hEmeas, heq]
    simp
  rw [hone] at hEbound
  linarith

/-- **The selection step, corrected: one nonzero pair at a time.**  This is
v5 lines 1189-1193 for a single pair `(A, B)`, with the exceptional set
quantified *after* the pair, which is how the manuscript uses it.  The measure
bound is uniform in the pair, which is the sense in which v5 line 1191 calls
Lemma 3.3 uniform.  Proved from
`V5Lemma33.shrinking_anti_concentration_v5_exp` at `η = e^{-κH}`. -/
theorem good_cylinder_selection_antiConc (κ : ℝ) (hκ : 0 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ∀ A B : ℤ, (A, B) ≠ (0, 0) →
        ∃ E : Set ℝ, MeasurableSet E ∧
          (volume.restrict (Ioo (0 : ℝ) 1)).real E ≤ C * Real.exp (-c * Hscale n) ∧
          ∀ α ∈ Ioo (0 : ℝ) 1 \ E,
            Real.exp (-κ * Hscale n) * (denom α j : ℝ) ≤ |(Qfreq α j B A : ℝ)| := by
  have hlogphi : 0 < Real.log V5Lemma33.phi := Real.log_pos V5Lemma33.one_lt_phi
  have hc₀ : 0 < 2 * Real.log V5Lemma33.phi := by linarith
  refine ⟨22, min κ (2 * Real.log V5Lemma33.phi), by norm_num, lt_min hκ hc₀, ?_⟩
  filter_upwards [TupleInputs.eventually_good] with n hn
  intro j hj A B hAB
  have hH1 : (1 : ℝ) ≤ Hscale n := TupleInputs.Hscale_ge_one hn.1
  obtain ⟨hj1, hHj⟩ := bulk_index_bounds hn.1 hj
  have hmκ : min κ (2 * Real.log V5Lemma33.phi) ≤ κ := min_le_left _ _
  have hmc : min κ (2 * Real.log V5Lemma33.phi) ≤ 2 * Real.log V5Lemma33.phi :=
    min_le_right _ _
  have hη : (0 : ℝ) < Real.exp (-κ * Hscale n) := Real.exp_pos _
  have hBA : ((B, A) : ℤ × ℤ) ≠ (0, 0) := by
    intro h
    rw [Prod.mk.injEq] at h
    exact hAB (by rw [Prod.mk.injEq]; exact ⟨h.2, h.1⟩)
  have hmain := V5Lemma33.shrinking_anti_concentration_v5_exp B A hBA j hj1
    (Real.exp (-κ * Hscale n)) hη
  set S : Set ℝ := {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
      |(A : ℝ) * denom α j - (B : ℝ) * denom α (j - 1)|
        < Real.exp (-κ * Hscale n) * denom α j} with hSdef
  have hSsub : S ⊆ Ioo (0 : ℝ) 1 := fun α hα => hα.1
  have hbound : (volume S).toReal
      ≤ 22 * Real.exp (-min κ (2 * Real.log V5Lemma33.phi) * Hscale n) := by
    refine hmain.trans ?_
    have h1 : Real.exp (-κ * Hscale n)
        ≤ Real.exp (-min κ (2 * Real.log V5Lemma33.phi) * Hscale n) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hstep : min κ (2 * Real.log V5Lemma33.phi) * Hscale n
        ≤ (2 * Real.log V5Lemma33.phi) * (j : ℝ) := by
      calc min κ (2 * Real.log V5Lemma33.phi) * Hscale n
          ≤ (2 * Real.log V5Lemma33.phi) * Hscale n :=
            mul_le_mul_of_nonneg_right hmc (by linarith)
        _ ≤ (2 * Real.log V5Lemma33.phi) * (j : ℝ) :=
            mul_le_mul_of_nonneg_left hHj (by linarith)
    have h2 : Real.exp (-(2 * Real.log V5Lemma33.phi) * (j : ℝ))
        ≤ Real.exp (-min κ (2 * Real.log V5Lemma33.phi) * Hscale n) := by
      apply Real.exp_le_exp.mpr
      linarith
    linarith
  refine ⟨toMeasurable volume S, measurableSet_toMeasurable _ _,
    restrict_real_toMeasurable_le hSsub hbound, ?_⟩
  intro α hα
  have hαS : α ∉ S := fun h => hα.2 (subset_toMeasurable volume S h)
  have hge : Real.exp (-κ * Hscale n) * (denom α j : ℝ)
      ≤ |(A : ℝ) * denom α j - (B : ℝ) * denom α (j - 1)| :=
    not_lt.mp (fun h => hαS ⟨hα.1, h⟩)
  refine hge.trans (le_of_eq ?_)
  congr 1
  simp only [Qfreq]
  push_cast
  ring

/-- **The selection step, corrected: a finite family of nonzero pairs.**  This
is the form v5 line 1191 actually uses, the family being the finitely many
pairs `(A_w, B_w)` attached to the finitely many local words in the support of
the test.  The discarded mass grows linearly in the number of pairs, which is
harmless because the family is fixed before `n` is sent to infinity. -/
theorem good_cylinder_selection_finite (κ : ℝ) (hκ : 0 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ∀ S : Finset (ℤ × ℤ), ((0 : ℤ), (0 : ℤ)) ∉ S →
        ∃ E : Set ℝ, MeasurableSet E ∧
          (volume.restrict (Ioo (0 : ℝ) 1)).real E
              ≤ (S.card : ℝ) * (C * Real.exp (-c * Hscale n)) ∧
          ∀ α ∈ Ioo (0 : ℝ) 1 \ E, ∀ p ∈ S,
            Real.exp (-κ * Hscale n) * (denom α j : ℝ) ≤ |(Qfreq α j p.2 p.1 : ℝ)| := by
  classical
  obtain ⟨C, c, hC, hc, hev⟩ := good_cylinder_selection_antiConc κ hκ
  refine ⟨C, c, hC, hc, ?_⟩
  filter_upwards [hev] with n hn
  intro j hj S hS
  have hb : (0 : ℝ) ≤ C * Real.exp (-c * Hscale n) := by positivity
  have hpair : ∀ p : ℤ × ℤ, ∃ E : Set ℝ, MeasurableSet E ∧
      (p ∈ S → (volume.restrict (Ioo (0 : ℝ) 1)).real E ≤ C * Real.exp (-c * Hscale n)) ∧
      (p ∈ S → ∀ α ∈ Ioo (0 : ℝ) 1 \ E,
        Real.exp (-κ * Hscale n) * (denom α j : ℝ) ≤ |(Qfreq α j p.2 p.1 : ℝ)|) := by
    intro p
    by_cases hp : p ∈ S
    · have hp0 : (p.1, p.2) ≠ ((0 : ℤ), (0 : ℤ)) := by
        intro h
        rw [Prod.mk.injEq] at h
        exact hS (by rwa [show p = ((0 : ℤ), (0 : ℤ)) from Prod.ext h.1 h.2] at hp)
      obtain ⟨E, h1, h2, h3⟩ := hn j hj p.1 p.2 hp0
      exact ⟨E, h1, fun _ => h2, fun _ => h3⟩
    · exact ⟨∅, MeasurableSet.empty, fun h => absurd h hp, fun h => absurd h hp⟩
  choose E hEmeas hEbound hEgood using hpair
  refine ⟨⋃ p ∈ S, E p, Finset.measurableSet_biUnion S (fun p _ => hEmeas p), ?_, ?_⟩
  · have hchain : volume.restrict (Ioo (0 : ℝ) 1) (⋃ p ∈ S, E p)
        ≤ (S.card : ℝ≥0∞) * ENNReal.ofReal (C * Real.exp (-c * Hscale n)) := by
      calc volume.restrict (Ioo (0 : ℝ) 1) (⋃ p ∈ S, E p)
          ≤ ∑ p ∈ S, volume.restrict (Ioo (0 : ℝ) 1) (E p) :=
            measure_biUnion_finset_le S E
        _ ≤ ∑ _p ∈ S, ENNReal.ofReal (C * Real.exp (-c * Hscale n)) :=
            Finset.sum_le_sum (fun p hp => restrict_le_ofReal (hEbound p hp))
        _ = (S.card : ℝ≥0∞) * ENNReal.ofReal (C * Real.exp (-c * Hscale n)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hfin : ((S.card : ℝ≥0∞) * ENNReal.ofReal (C * Real.exp (-c * Hscale n))) ≠ ⊤ := by
      simp [ENNReal.mul_eq_top]
    have h := ENNReal.toReal_mono hfin hchain
    rw [measureReal_def]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hb] at h
    simpa using h
  · intro α hα p hp
    exact hEgood p hp α ⟨hα.1, fun h => hα.2 (Set.mem_biUnion hp h)⟩

/-- **The selection step of v5 lines 1189-1201, corrected and complete**,
conditionally on the manuscript's display (20).  Both halves of the selection
appear: the local `q`-estimate half is exactly what `Display20` supplies, and
the anti-concentration half is `good_cylinder_selection_antiConc`.  The measure
bound carries both scales, `e^{-cH}` from the anti-concentration union and
`e^{-c₀ L^{1/2}}` from the `q`-estimate union; see the second finding in the
module docstring for why the single scale `e^{-cH}` of the skeleton is not the
right shape.

`Display20` is an input, not an assumption of this development: it is the one
analytic ingredient of §4-§6 that neither `Kwon1002` nor the vendored substrate
contains, as recorded at `Kwon1002/P42Cases.lean`. -/
theorem lemma_6_3_good_cylinder_selection_corrected (κ δ : ℝ) (hκ : 0 < κ) (_hδ : 0 < δ)
    (C₀ c₀ : ℝ) (hC₀ : 0 < C₀) (h20 : P42Cases.Display20 C₀ δ c₀) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ∀ A B : ℤ, (A, B) ≠ (0, 0) →
        ∃ E : Set ℝ, MeasurableSet E ∧
          (volume.restrict (Ioo (0 : ℝ) 1)).real E
              ≤ C * Real.exp (-c * Hscale n)
                + C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)) ∧
          ∀ α ∈ Ioo (0 : ℝ) 1 \ E,
            Real.exp (lyapunov * j - δ * Hscale n) ≤ (denom α j : ℝ) ∧
            Real.exp (-κ * Hscale n) * (denom α j : ℝ) ≤ |(Qfreq α j B A : ℝ)| := by
  obtain ⟨C, c, hC, hc, hev⟩ := good_cylinder_selection_antiConc κ hκ
  refine ⟨C, c, hC, hc, ?_⟩
  filter_upwards [hev, h20] with n hn h20n
  intro j hj A B hAB
  obtain ⟨E₁, hE₁meas, hE₁bound, hE₁good⟩ := hn j hj A B hAB
  -- the `q`-estimate half, moved to a measurable hull
  set T : Set ℝ := {α ∈ Ioo (0 : ℝ) 1 |
      ¬ (Real.exp (lyapunov * (j : ℝ) - δ * Hscale n) ≤ (denom α j : ℝ)
          ∧ (denom α j : ℝ) ≤ Real.exp (lyapunov * (j : ℝ) + δ * Hscale n))} with hTdef
  have hTsub : T ⊆ Ioo (0 : ℝ) 1 := fun α hα => hα.1
  have hTbound : (volume T).toReal ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)) := by
    have := h20n j hj
    rwa [measureReal_def] at this
  refine ⟨E₁ ∪ toMeasurable volume T,
    hE₁meas.union (measurableSet_toMeasurable volume T), ?_, ?_⟩
  · exact restrict_real_union_le (by positivity) (by positivity) hE₁bound
      (restrict_real_toMeasurable_le hTsub hTbound)
  · intro α hα
    have hα1 : α ∈ Ioo (0 : ℝ) 1 \ E₁ := ⟨hα.1, fun h => hα.2 (Or.inl h)⟩
    have hαT : α ∉ T := fun h =>
      hα.2 (Or.inr (subset_toMeasurable volume T h))
    refine ⟨?_, hE₁good α hα1⟩
    by_contra hlow
    exact hαT ⟨hα.1, fun hcon => hlow hcon.1⟩

/-! ## Target 3: the cylinder-character step

The first move of v5 lines 1180-1196 is to place a cylinder-character test on
the actual window and read the torus factor as a single phase through identity
(31).  That move is carried out here.  What remains open afterwards is the
analytic part: the descendant estimate of Lemma 3.4 applied to those phases,
and the uniform Gauss mixing used when the reduced pair vanishes. -/

/-- **The character reduction on the test class.**  Placing a cylinder-character
test of radius `R` on the actual window `W^{(R)}_{n,j}` turns its torus factor
into the single phase `e(n (-1)^j Q_j α)` of v5 line 623, where
`Q_j = A_w q_j - B_w q_{j-1} = Qfreq α j B_w A_w` and `(A_w, B_w)` depend only
on the radius-`R` word `w = (a_{j-R+1}, …, a_{j+R})`.

The second conclusion is the split of v5 line 1191: on the cylinders where the
reduced pair vanishes there is no phase left at all, and the test is a pure
digit-cylinder amplitude, which is the case handed to uniform Gauss mixing.

Proved from `V5Identity31.window_character_phase_v5`, that is from identity
(31) at the full v5 range `t = -R-1, …, R`. -/
theorem eval_actualWindow_phase (R : ℕ) (T : CylinderCharacterTest R) :
    ∃ A B : (Fin (2 * R) → ℕ) → ℤ,
      ∀ α : ℝ, Irrational α → α ∈ Ioo (0 : ℝ) 1 → ∀ n j : ℕ, R + 1 ≤ j →
        T.eval (actualWindow R α n j)
            = T.amp (fun i => digit α (j + (i : ℕ) - R))
              * torusChar ((n : ℝ) * (-1 : ℝ) ^ j
                  * ((Qfreq α j (B (windowWord R α j)) (A (windowWord R α j)) : ℤ) : ℝ)
                  * α)
          ∧ (A (windowWord R α j) = 0 → B (windowWord R α j) = 0 →
              T.eval (actualWindow R α n j)
                = T.amp (fun i => digit α (j + (i : ℕ) - R))) := by
  obtain ⟨A, B, hAB⟩ := V5Identity31.window_character_phase_v5 R T.c
  refine ⟨A, B, ?_⟩
  intro α hirr hα n j hRj
  have hshift : ∀ i : Fin (2 * R + 2),
      (actualWindow R α n j).2.2 i = theta α n (j + (i : ℕ) - (R + 1)) := fun _ => rfl
  have heval : T.eval (actualWindow R α n j)
      = T.amp (fun i => digit α (j + (i : ℕ) - R))
        * torusChar (∑ i : Fin (2 * R + 2), (T.c i : ℝ)
            * theta α n (j + (i : ℕ) - (R + 1))) := by
    simp only [CylinderCharacterTest.eval, hshift]
    rfl
  have hmain : T.eval (actualWindow R α n j)
      = T.amp (fun i => digit α (j + (i : ℕ) - R))
        * torusChar ((n : ℝ) * (-1 : ℝ) ^ j
            * ((Qfreq α j (B (windowWord R α j)) (A (windowWord R α j)) : ℤ) : ℝ) * α) := by
    rw [heval, hAB α hirr hα n j hRj]
    rfl
  refine ⟨hmain, ?_⟩
  intro hA0 hB0
  rw [hmain, hA0, hB0]
  have hq : Qfreq α j (0 : ℤ) (0 : ℤ) = 0 := by simp only [Qfreq]; ring
  rw [hq]
  simp [torusChar]

/-- Token-identical reproduction of the conclusion of
`Kwon1002.lemma_6_3_cylinder_character_step`. -/
def CylinderCharacterStep (R : ℕ) (T : CylinderCharacterTest R) : Prop :=
  ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
    ‖(∫ w, T.eval w ∂(actualWindowLaw R n j)) - ∫ w, T.eval w ∂(windowLaw R)‖ < ε

/-- Statement identity, type check only. -/
example : ∀ (R : ℕ) (T : CylinderCharacterTest R), CylinderCharacterStep R T :=
  _root_.Kwon1002.lemma_6_3_cylinder_character_step

/-- **Open.**  The one-block step of Lemma 6.3, v5 lines 1180-1216.

Obstruction, precisely.  `eval_actualWindow_phase` above discharges the
algebraic half: after partitioning into complete depth-`d` cylinders over the
finitely many words of `T.words`, the integrand against `actualWindowLaw` is
`amp(w)` times the single phase `e(n(-1)^j Q_j α)` with `Q_j` constant on the
cylinder.  Three inputs are then still missing.

1. **The local `q`-estimate**, display (20) of the manuscript
   (`Kwon1002.P42Cases.Display20`): it is what makes the retained union
   `q_j ≥ e^{λj-δH}`, `q_t ≤ e^{λt+δH}` have full mass up to
   `O(e^{-c_δ L^{1/2}})`, and it is absent from this development and from the
   vendored substrate.  Without it the exponent comparison
   `log(q_t²/(n|Q_j|)) ≤ -(80λ-κ-3δ)H + O(1)` of v5 line 1206 cannot be run.
   `lemma_6_3_good_cylinder_selection_corrected` isolates exactly this
   dependence.
2. **Lemma 3.4 in the form used here**: `descendant_cylinder_estimate` (22) and
   `descendant_phase_small` (23) are proved in the tree, but at prefix depth
   `d` for the *fixed* window word; transporting them to the depth
   `d ≤ j + R + M` of the truncated tests, uniformly in `j`, has not been done.
3. **Uniform Gauss mixing on the vanishing-pair cylinders**, the `A_w = B_w = 0`
   branch of v5 line 1189.  `Bridge.good_tuple_multiblock_mixing'` and
   `MixingBV.lem_3_2_conditional_multiblock_mixing'` are the available forms;
   neither is yet stated against `windowLaw R`, which needs
   `measurable_stationaryWindow` and the invariance of `hatMu0` under `hatS`,
   both open in `Section6Skeleton`. -/
theorem lemma_6_3_cylinder_character_step (R : ℕ) (T : CylinderCharacterTest R) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ‖(∫ w, T.eval w ∂(actualWindowLaw R n j)) - ∫ w, T.eval w ∂(windowLaw R)‖ < ε := by
  sorry

/-! ## Target 4: uniform full-state transfer -/

/-- Token-identical reproduction of the conclusion of
`Kwon1002.lemma_6_3_full_state_transfer`. -/
def FullStateTransfer (R : ℕ) (G : WindowSpace R → ℂ) : Prop :=
  ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
    ‖(∫ w, G w ∂(actualWindowLaw R n j)) - ∫ w, G w ∂(windowLaw R)‖ < ε

/-- Statement identity, type check only. -/
example : ∀ (R : ℕ) (G : WindowSpace R → ℂ) (C : ℝ), Measurable G → (∀ w, ‖G w‖ ≤ C) →
    windowLaw R {w | ¬ ContinuousAt G w} = 0 → FullStateTransfer R G :=
  _root_.Kwon1002.lemma_6_3_full_state_transfer

/-- **Open.**  Lemma 6.3, v5 lines 1166-1179.

Obstruction, precisely.  Beyond `lemma_6_3_cylinder_character_step` above, the
passage from the test class to a general bounded almost-everywhere continuous
`G` needs four things that are not in the tree.

1. **Digit truncation**, v5 lines 1218-1226.  `digit_tail_product` (3.1(ii)) is
   proved and gives the `O_R(1/K)` tail bound for the actual law; the same
   bound for the stationary law `windowLaw R` is not available, because
   `windowLaw` is defined by pushing `hatMu0` forward along
   `stationaryWindow R` and `measurable_stationaryWindow` is open.
2. **Complete-quotient truncation**, v5 lines 1227-1233: replacing `x_{j+t}` by
   its first `M` future digits costs `O_R(F_M^{-2})` in each coordinate, so
   `ω_G(C_R F_M^{-2})` in the test value.  This needs the continued-fraction
   contraction estimate on `WindowSpace R`, which has no statement here.
3. **Stone-Weierstrass and tightness**, v5 lines 1235-1242.  Mathlib has
   `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`,
   but `WindowSpace R` is not compact (the digit block is `ℕ`-valued), so the
   argument has to run on each compact digit truncation and be glued by the
   tightness statement; neither the truncation nor the tightness is stated.
4. **Portmanteau**, v5 lines 1242-1245.  Mathlib's
   `MeasureTheory.tendsto_measure_of_tendsto_...` portmanteau family applies to
   bounded almost-everywhere continuous functions, which is the right shape,
   but it needs the weak convergence of `actualWindowLaw R n j` along a
   subsequence, hence the tightness of item 3. -/
theorem lemma_6_3_full_state_transfer (R : ℕ) (G : WindowSpace R → ℂ) (C : ℝ)
    (hGmeas : Measurable G) (hGbdd : ∀ w, ‖G w‖ ≤ C)
    (hGcont : windowLaw R {w | ¬ ContinuousAt G w} = 0) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ‖(∫ w, G w ∂(actualWindowLaw R n j)) - ∫ w, G w ∂(windowLaw R)‖ < ε := by
  sorry

end

end Lemma63

end Kwon1002
