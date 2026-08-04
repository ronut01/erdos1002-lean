import Kwon1002.MonomialCore

/-!
# P42Cases, p42: the three cases of Proposition 4.2, and the constant ledger

Targets of this pass, in order:

1. `MonomialCore.zeroMode_gauss_mixing` (case 1 of Kwon's proof of 4.2),
2. `MonomialCore.laterMode_phase_bound`, `MonomialCore.earlierMode_phase_bound`
   (cases 2 and 3),
3. `Prop42.two_block_monomial_core`,
4. the canonical `Section4.prop_4_2_two_block_factorization`.

## What this file achieves

* **Case 1 is discharged down to a purely measure-theoretic statement about
  digit cylinders.**  `zeroMode_gauss_mixing'` (token-identical to
  `MonomialCore.zeroMode_gauss_mixing`) is *proved* here from
  `zeroMode_cylinder_mixing`, which mentions no complex integral, no torus
  character and no `monoStationary`, only Lebesgue measure of an intersection
  of two digit-window cylinders and the two natural-extension masses
  `cylProb`.  The glue (`monoAt_zeroMode_mul_eq_indicator`,
  `integral_zeroMode_mul`, `monoStationary_zeroMode`, `zeroMode_norm_eq`) is
  proved outright and consists of *exact identities*, so, stated honestly -
  the new sorry is **equivalent** to the one it replaces, not weaker.  What is
  gained is location, not logical strength: the remaining assumption is now a
  statement about measures of digit cylinders, which is where the two genuinely
  missing ingredients live (§2).
* **The constant ledger of referee note 5 is made completely explicit.**
  `Compat c δ c₀` records *all four* roles that Kwon's single letter `c` plays
  in the proof of 4.2 (the manuscript's phrasing suggests one), each with a
  machine-checked grounding lemma (`retainedMinus_ground`,
  `retainedPlus_ground`, `antiConc_ground`, `mixingGap_ground`), and
  `two_block_monomial_core_compat` proves that the monomial core can always be
  taken with a `Compat` constant, i.e. the compatibility constrains nothing
  downstream.  One entry, `antiConc` (`c ≤ 200 c₀`), is **not recorded in the
  manuscript or in our referee report**; see §3.  See also
  `mixingGap_eventually`.

* `two_block_monomial_core''`, `Prop42.two_block_monomial_core''` and
  `prop_4_2_two_block_factorization'` are reproduced token-identically and
  assembled.

## Sorried results consumed

* `zeroMode_cylinder_mixing`, **new here**; provably equivalent to the
  `MonomialCore.zeroMode_gauss_mixing` it replaces (`zeroMode_norm_eq`), but
  stated with no analytic dressing, which localizes the obstruction (see §2).
* `MonomialCore.laterMode_phase_bound`, `MonomialCore.earlierMode_phase_bound`
 , consumed unchanged.  §4 re-audits their obstruction and **corrects it**:
  every ingredient Kwon names is now proved in the tree *except* display (20),
  the Lévy large-deviation bound for the continuants, which is absent from
  `Kwon1002/` and from the Wang substrate alike.  `Display20` records it.

Nothing else sorried is consumed: `MonomialCore.monoStationary_eq_zero`,
`MonomialCore.card_nearDiag_le`, `MonomialCore.card_nearRes_le`,
`MonomialCore.err_le`, `MonomialCore.exc_card_bound`,
`MonomialCore.one_le_Hscale`, `Prop42.two_block_bound_of_mono`,
`Prop42.eighty_lyapunov_bounds`, `Prop42.lyapunov_pos` are all axiom-clean.

## Axiom audit

`#print axioms` was run on all twenty-two results proved outright here
(`torusChar_zero`, `measurableSet_cyl`, `cylProb_nonneg`, `monoAt_zeroMode`,
`monoAt_zeroMode_mul_eq_indicator`, `integral_zeroMode_mul`,
`monoStationary_zeroMode`, `Compat.pos`, `Compat.acCompatible`,
`retainedMinus_ground`, `retainedPlus_ground`, `antiConc_ground`,
`mixingGap_ground`, `tendsto_Hscale`, `mixingGap_eventually`,
`Compat.retainedMinus_imp_retainedPlus`, `compat_of_le_one`, `exists_compat`,
`badPairs_finite`, `badPairs_mono`, `zeroMode_norm_eq`,
`retained_descendant_at_compat`): each depends on exactly
`[propext, Classical.choice, Quot.sound]`.  The audit block has been removed.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

namespace Kwon1002

namespace P42Cases

noncomputable section

/-! ## 1. The zero-mode collapse

At the trivial torus mode a cylinder-torus monomial *is* the indicator of its
digit cylinder: `e(0·θ' + 0·θ) = 1`.  This is what turns case 1 of Kwon's
proof into a statement about measures of cylinders. -/

lemma torusChar_zero : torusChar 0 = 1 := by
  simp [torusChar]

/-- The digit-window cylinder `{α : (a_{j-R+1},…,a_{j+R}) = w}`. -/
def cyl (R : ℕ) (w : Fin (2 * R) → ℕ) (j : ℕ) : Set ℝ :=
  {α : ℝ | windowWord R α j = w}

lemma measurableSet_cyl (R : ℕ) (w : Fin (2 * R) → ℕ) (j : ℕ) :
    MeasurableSet (cyl R w j) :=
  Prop42.measurableSet_windowWord_eq R w j

/-- The `μ̂₀`-mass of the natural-extension cylinder of the word `w`; this is
the zero-mode stationary mean (`monoStationary_zeroMode`). -/
def cylProb (R : ℕ) (w : Fin (2 * R) → ℕ) : ℝ :=
  hatMu0.real {z : (ℝ × ℝ) × ℝ × ℝ | natExtWord R z.1 = w}

lemma cylProb_nonneg (R : ℕ) (w : Fin (2 * R) → ℕ) : 0 ≤ cylProb R w :=
  measureReal_nonneg

lemma monoAt_zeroMode (R : ℕ) (w : Fin (2 * R) → ℕ) (α : ℝ) (n j : ℕ) :
    Prop42.monoAt R w 0 0 α n j = (cyl R w j).indicator (fun _ => (1 : ℂ)) α := by
  unfold Prop42.monoAt cyl
  rw [Set.indicator_apply]
  simp [torusChar_zero]

/-- **The zero-mode two-block integrand is the indicator of the intersection of
the two digit cylinders.** -/
lemma monoAt_zeroMode_mul_eq_indicator (R : ℕ) (w w' : Fin (2 * R) → ℕ)
    (α : ℝ) (n j k : ℕ) :
    Prop42.monoAt R w 0 0 α n j * Prop42.monoAt R w' 0 0 α n k
      = (cyl R w j ∩ cyl R w' k).indicator (fun _ => (1 : ℂ)) α := by
  classical
  rw [monoAt_zeroMode, monoAt_zeroMode, Set.indicator_apply, Set.indicator_apply,
    Set.indicator_apply]
  by_cases h1 : α ∈ cyl R w j <;> by_cases h2 : α ∈ cyl R w' k <;> simp [h1, h2]

/-- **The zero-mode two-block integral is the Lebesgue measure of a
two-cylinder intersection.** -/
lemma integral_zeroMode_mul (R : ℕ) (w w' : Fin (2 * R) → ℕ) (n j k : ℕ) :
    (∫ α in Ioo (0 : ℝ) 1,
        Prop42.monoAt R w 0 0 α n j * Prop42.monoAt R w' 0 0 α n k)
      = ((volume.real (Ioo (0 : ℝ) 1 ∩ (cyl R w j ∩ cyl R w' k)) : ℝ) : ℂ) := by
  simp only [monoAt_zeroMode_mul_eq_indicator]
  rw [MeasureTheory.integral_indicator_const _
    ((measurableSet_cyl R w j).inter (measurableSet_cyl R w' k)),
    measureReal_restrict_apply
      ((measurableSet_cyl R w j).inter (measurableSet_cyl R w' k))]
  rw [Set.inter_comm (cyl R w j ∩ cyl R w' k) (Ioo (0 : ℝ) 1)]
  simp [Complex.real_smul]

/-- **The zero-mode stationary mean is the `μ̂₀`-mass of the word cylinder.** -/
lemma monoStationary_zeroMode (R : ℕ) (w : Fin (2 * R) → ℕ) :
    Prop42.monoStationary R w 0 0 = ((cylProb R w : ℝ) : ℂ) := by
  have hpt : ∀ z : (ℝ × ℝ) × ℝ × ℝ, Prop42.monoEval R w 0 0 z
      = ({z : (ℝ × ℝ) × ℝ × ℝ | natExtWord R z.1 = w}).indicator (fun _ => (1 : ℂ)) z := by
    intro z
    unfold Prop42.monoEval
    rw [Set.indicator_apply]
    simp [torusChar_zero]
  rw [Prop42.monoStationary]
  simp only [hpt]
  rw [MeasureTheory.integral_indicator_const _ (Prop42.measurableSet_natExtWord_eq R w)]
  simp [cylProb, Complex.real_smul]

/-- **The two forms of case 1 are the *same number*.**  This is the exact
identity behind `zeroMode_gauss_mixing'`: at the trivial torus mode the
quantity estimated in (34) is literally the discrepancy between the Lebesgue
measure of a two-cylinder intersection and the product of the two
natural-extension masses.  No inequality is used in either direction, so the
two statements of §2 are *equivalent*, not merely comparable. -/
lemma zeroMode_norm_eq (R : ℕ) (w w' : Fin (2 * R) → ℕ) (n j k : ℕ) :
    ‖(∫ α in Ioo (0 : ℝ) 1,
          Prop42.monoAt R w 0 0 α n j * Prop42.monoAt R w' 0 0 α n k)
        - Prop42.monoStationary R w 0 0 * Prop42.monoStationary R w' 0 0‖
      = |volume.real (Ioo (0 : ℝ) 1 ∩ (cyl R w j ∩ cyl R w' k))
          - cylProb R w * cylProb R w'| := by
  rw [integral_zeroMode_mul, monoStationary_zeroMode, monoStationary_zeroMode]
  have hcast : (((volume.real (Ioo (0 : ℝ) 1 ∩ (cyl R w j ∩ cyl R w' k)) : ℝ) : ℂ)
        - ((cylProb R w : ℝ) : ℂ) * ((cylProb R w' : ℝ) : ℂ))
      = (((volume.real (Ioo (0 : ℝ) 1 ∩ (cyl R w j ∩ cyl R w' k))
          - cylProb R w * cylProb R w' : ℝ)) : ℂ) := by
    push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]

/-! ## 2. Case 1 of the proof of 4.2, reduced

`zeroMode_cylinder_mixing` below is exactly what "ordinary two-sided Gauss
mixing" has to deliver, written with no analytic dressing at all: the Lebesgue
measure of the intersection of a depth-`2R` digit window at time `j` with one
at time `k` factorises, up to the error of (34), into the two stationary
natural-extension masses, once the blocks are separated.

Compared with `MonomialCore.zeroMode_gauss_mixing` this
* removes the complex-valued integral,
* removes the torus character,
* removes `monoStationary` (an integral against `μ̂₀` in four variables),
and by `zeroMode_norm_eq` it is *equivalent* to it, the reduction is by exact
identities, so no strength is claimed to have been gained.  What is gained is
that the obstruction is now visible:
what is missing in this development is (i) two-sided Gauss mixing for
*cylinder indicators*, for which `BVMixing.lemma_3_2_BV` is now the right
tool, since indicators of digit cylinders are nonnegative and of bounded
variation, though its hypotheses are stated for `gaussOrbit`-block products
and the translation to a two-window intersection is not done, and (ii) the
identification of the `μ̂₀`-marginal `cylProb R w` with the Gauss measure of
the corresponding `2R`-cylinder, which requires the natural-extension marginal
computation for the density `1/(log 2 (1+xy)²)`.  Grepping confirms that
`natExtWord` occurs *only* in `Section4.lean`, `Prop42.lean` and
`MonomialCore.lean`: no natural-extension marginal theory exists in the tree,
so (ii) is genuinely absent, not merely unassembled. -/

theorem zeroMode_cylinder_mixing (R : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ w' ∈ Wv, ∀ p ∈ bulkPairs n,
        C * Hscale n < (p.2 : ℝ) - (p.1 : ℝ) →
        |volume.real (Ioo (0 : ℝ) 1 ∩ (cyl R w p.1 ∩ cyl R w' p.2))
            - cylProb R w * cylProb R w'|
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) := by
  sorry

/-- **Case 1 of the proof of 4.2**, token-identical to
`MonomialCore.zeroMode_gauss_mixing`, now *proved* from the cylinder form. -/
theorem zeroMode_gauss_mixing' (R : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ w' ∈ Wv, ∀ p ∈ bulkPairs n,
        C * Hscale n < (p.2 : ℝ) - (p.1 : ℝ) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w 0 0 α n p.1 * Prop42.monoAt R w' 0 0 α n p.2)
            - Prop42.monoStationary R w 0 0 * Prop42.monoStationary R w' 0 0‖
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) := by
  obtain ⟨C, c, ρ, hC, hc, hρ0, hρ1, hmix⟩ := zeroMode_cylinder_mixing R Wu Wv
  refine ⟨C, c, ρ, hC, hc, hρ0, hρ1, ?_⟩
  filter_upwards [hmix] with n hn
  intro w hw w' hw' p hp hgap
  rw [zeroMode_norm_eq]
  exact hn w hw w' hw' p hp hgap

/-! ## 3. The constant ledger of the proof of 4.2 (recorded finding)

The manuscript writes a single `c` throughout the proof of Proposition 4.2.
Reading the proof line by line, that letter carries **four** independent
compatibility requirements, only one of which our referee report had recorded.
All four are collected in `Compat`, and `two_block_monomial_core_compat`
proves that requiring them costs nothing.

Where each comes from (manuscript lines ≈ 411-470):

* `retainedMinus`, `2c + 3δ < 80λ`.  "Since `2λt₋ = L + λk − 80λH + O(1)`,
  every retained descendant satisfies `q_{t₋}² ≤ e^{−cH} n|Q|`."
  `Prop42.retained_descendant_exponent` computes that the exponent actually
  produced is `80λ − 3δ − c₁`, where `c₁` is the anti-concentration constant
  of `|Q| ≥ ½ e^{−c₁H} q_k`.  Demanding the *same* `c` on both sides needs
  `c ≤ 80λ − 3δ − c`.  This is the requirement the manuscript's phrasing hides
  most thoroughly, and it is one notch stronger than the `c + 3δ < 80λ` our
  report recorded.
* `retainedPlus`, `c + 3δ < 80λ`, `Prop42.ACCompatible`.  The `k > t₀ + 100H`
  branch of case 3: `2λt₊ = L + λj + 80λH + O(1)`, `q_{t₊}² ≥ e^{2λt₊ − 2δH}`
  and `n|Q_j| ≤ e^{L}·C·e^{λj + δH}`, so `q_{t₊}²/(n|Q_j|) ≥ e^{(80λ−3δ)H+O(1)}`;
  writing this as `≥ e^{cH}` needs `c ≤ 80λ − 3δ`.  (Implied by
  `retainedMinus`, but it is a *separate* line of the proof and is recorded
  separately.)
* `antiConc`, `c ≤ 200 c₀`.  Lemma 3.3 as proved
  (`shrinking_anti_concentration`) bounds the bad set by `C(η + e^{−c₀ j})`
  with its **own** decay constant `c₀`.  The manuscript states the discarded
  mass as `O(e^{−cH})`; since every `j` in play satisfies `j ≥ 200H` by (19),
  `e^{−c₀ j} ≤ e^{−200 c₀ H}`, so the manuscript's `O(e^{−cH})` is legitimate
  exactly when `c ≤ 200 c₀`.  **This compatibility is not recorded anywhere in
  the manuscript or in our referee report; it is new here.**  It is harmless
  (`c₀` is an absolute constant and `c` is existential) but it is a genuine
  hypothesis of the step, and it is the reason the proof needs the bulk
  condition `j ≥ 200H` of (19) and not merely `j ≥ 1`.
* `mixingGap`, `c ≤ 60`.  "The later zero-mode block starts at least `cH`
  after `t₊`": with `k > t₀ + 100H`, `t₊ = ⌊t₀ + 40H⌋` and a window radius `R`,
  the gap is `k − R − t₊ > 60H − R − 1`, so the mixing error `ρ^{gap}` may be
  written `ρ^{cH}` only for `c ≤ 60` (and `n` large).

Everything is satisfiable simultaneously by any `c ≤ min(1, 200c₀)`, and
`two_block_monomial_core_compat` shows the core statement holds for such a `c`,
so **the ledger constrains nothing downstream**. -/

/-- The full compatibility ledger for the constant `c` of Proposition 4.2,
against the denominator-deviation constant `δ` of (20) and the intrinsic decay
constant `c₀` of Lemma 3.3. -/
def Compat (c δ c₀ : ℝ) : Prop :=
  0 < c ∧ 2 * c + 3 * δ < 80 * lyapunov ∧ c + 3 * δ < 80 * lyapunov ∧
    c ≤ 200 * c₀ ∧ c ≤ 60

lemma Compat.pos {c δ c₀ : ℝ} (h : Compat c δ c₀) : 0 < c := h.1

lemma Compat.acCompatible {c δ c₀ : ℝ} (h : Compat c δ c₀) : Prop42.ACCompatible c δ :=
  h.2.2.1

/-! ### Each entry of the ledger, grounded

The four lemmas below are the arithmetic each ledger entry abbreviates.  They
turn §3's prose into machine-checked statements. -/

/-- **`retainedMinus`, grounded.**  `Prop42.retained_descendant_exponent`
produces the decay rate `80λ − 3δ − c` for `q_{t₋}² ≤ e^{−(·)H} n|Q|`, where the
`c` on the right is the anti-concentration constant of
`|Q| ≥ ½ e^{−cH} q_k`.  Kwon's line "every retained descendant satisfies
`q_{t₋}² ≤ e^{−cH} n|Q|`" reuses the *same* letter, so it demands that the
produced rate beat the demanded one, which is exactly `2c + 3δ < 80λ`. -/
lemma retainedMinus_ground {c δ : ℝ} (h : 2 * c + 3 * δ < 80 * lyapunov) :
    c < 80 * lyapunov - 3 * δ - c := by linarith

/-- **`retainedPlus`, grounded**, this is `Prop42.retained_rate_pos_iff`, i.e.
positivity of the very same rate, which is `Prop42.ACCompatible`. -/
lemma retainedPlus_ground {c δ : ℝ} (h : c + 3 * δ < 80 * lyapunov) :
    0 < 80 * lyapunov - 3 * δ - c :=
  Prop42.retained_rate_pos_iff.2 h

/-- **`antiConc`, grounded.**  Lemma 3.3 as proved
(`shrinking_anti_concentration`) discards a set of measure
`C (η + e^{−c₀ j})` with its own decay constant `c₀`.  At a bulk index
`j ≥ 200H` (display (19)) the second term is `≤ e^{−cH}`, which is how Kwon
writes the discarded mass, **precisely when `c ≤ 200 c₀`.**  This
compatibility appears neither in the manuscript nor in our referee report. -/
lemma antiConc_ground {c c₀ H j : ℝ} (hH : 0 ≤ H) (hc₀ : 0 ≤ c₀)
    (hbulk : 200 * H ≤ j) (hc : c ≤ 200 * c₀) :
    Real.exp (-c₀ * j) ≤ Real.exp (-c * H) := by
  refine Real.exp_le_exp.2 ?_
  have h1 : c * H ≤ 200 * c₀ * H := mul_le_mul_of_nonneg_right hc hH
  have h2 : c₀ * (200 * H) ≤ c₀ * j := mul_le_mul_of_nonneg_left hbulk hc₀
  nlinarith

/-- **`mixingGap`, grounded.**  "The later zero-mode block starts at least `cH`
after `t₊`": with `k > t₀ + 100H` (the non-exceptional branch of case 3),
`t₊ ≤ t₀ + 40H`, and the later window reaching back to `k − R`, the gap is
`> 60H − R`; writing it as `≥ cH` needs `R ≤ (60 − c)H`. -/
lemma mixingGap_ground {c Rr H t₀ tplus k : ℝ} (_hH : 0 ≤ H)
    (htp : tplus ≤ t₀ + 40 * H) (hk : t₀ + 100 * H < k) (hR : Rr ≤ (60 - c) * H) :
    c * H < (k - Rr) - tplus := by nlinarith

/-- `H = L^{3/4} → ∞`. -/
lemma tendsto_Hscale : Filter.Tendsto (fun n : ℕ => Hscale n) atTop atTop := by
  have htend : Filter.Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp htend

/-- Hence the side condition of `mixingGap_ground` holds for every fixed window
radius and every `c < 60`, for all large `n`: `mixingGap` costs nothing. -/
lemma mixingGap_eventually {c Rr : ℝ} (hc : c < 60) :
    ∀ᶠ n : ℕ in atTop, Rr ≤ (60 - c) * Hscale n :=
  (tendsto_Hscale.const_mul_atTop (by linarith : (0 : ℝ) < 60 - c)).eventually_ge_atTop Rr

/-- `retainedMinus` really is the stronger of the two exponent conditions. -/
lemma Compat.retainedMinus_imp_retainedPlus {c δ : ℝ} (hc : 0 < c)
    (h : 2 * c + 3 * δ < 80 * lyapunov) : c + 3 * δ < 80 * lyapunov := by
  linarith

/-- Every `c ≤ 1` below `200 c₀` meets the whole ledger. -/
lemma compat_of_le_one {c δ c₀ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hδ : δ ≤ 1)
    (hc₀ : c ≤ 200 * c₀) : Compat c δ c₀ := by
  have h94 := Prop42.eighty_lyapunov_bounds.1
  exact ⟨hc, by linarith, by linarith, hc₀, by linarith⟩

/-- The ledger is nonempty for every positive `c₀` and every `δ ≤ 1`. -/
lemma exists_compat {δ c₀ : ℝ} (hδ : δ ≤ 1) (hc₀ : 0 < c₀) :
    ∃ c : ℝ, 0 < c ∧ Compat c δ c₀ := by
  refine ⟨min 1 (200 * c₀), lt_min one_pos (by linarith), ?_⟩
  exact compat_of_le_one (lt_min one_pos (by linarith)) (min_le_left _ _) hδ (min_le_right _ _)

/-! ### Shrinking `c` is free

The error term of (34) is *decreasing* in `c`, so the exceptional set only
shrinks when `c` does.  This is the formal reason the ledger is absorbed by
the existential quantifier of Proposition 4.2. -/

/-- The exceptional set of (34) for one monomial pair. -/
def badPairs (R : ℕ) (w w' : Fin (2 * R) → ℕ) (m m' : ℤ × ℤ) (C c ρ : ℝ) (n : ℕ) :
    Set (ℕ × ℕ) :=
  {p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
    ¬ ‖(∫ α in Ioo (0 : ℝ) 1,
            Prop42.monoAt R w m.1 m.2 α n p.1 * Prop42.monoAt R w' m'.1 m'.2 α n p.2)
          - Prop42.monoStationary R w m.1 m.2 * Prop42.monoStationary R w' m'.1 m'.2‖
        ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n))}

lemma badPairs_finite (R : ℕ) (w w' : Fin (2 * R) → ℕ) (m m' : ℤ × ℤ) (C c ρ : ℝ) (n : ℕ) :
    (badPairs R w w' m m' C c ρ n).Finite :=
  Set.Finite.subset (bulkPairs n).finite_toSet (Set.sep_subset _ _)

/-- **Monotonicity of the exceptional set in `c`.** -/
lemma badPairs_mono {R : ℕ} {w w' : Fin (2 * R) → ℕ} {m m' : ℤ × ℤ} {C c c' ρ : ℝ} {n : ℕ}
    (hC : 0 < C) (hc'0 : 0 < c') (hc'c : c' ≤ c) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hL : 0 ≤ Lnorm n) (hH : 0 ≤ Hscale n) :
    badPairs R w w' m m' C c' ρ n ⊆ badPairs R w w' m m' C c ρ n := by
  rintro p ⟨hp1, hp2⟩
  refine ⟨hp1, fun hle => hp2 ?_⟩
  exact le_trans hle
    (MonomialCore.err_le hC le_rfl hc'0 hc'c hρ0 le_rfl hρ1 hL hH)

/-! ## 4. The remaining two cases: what is actually missing

`MonomialCore.laterMode_phase_bound` and `MonomialCore.earlierMode_phase_bound`
are consumed unchanged.  Their obstruction is, however, **not** the one
`MonomialCore.lean`'s docstring records, that docstring predates
`Display22.lean` and `BVMixing.lean`, and it is not display (33) either.
Re-auditing every input of Kwon's cases 2 and 3 against the current tree:

* (31), the window-character reduction, **proved**,
  `CharacterReduction.window_character_reduction`.
* (33), `e(rθ_{j−1} + sθ_j) = e((−1)^j Q_j(r,s) n α)`, which is what turns the
  two-block integrand into a pure phase times a cylinder amplitude, i.e. into
  the shape of display (22), **proved**, as
  `CharacterReduction.torusChar_monomial_frequency'`.  (The hypothesis-free
  form `Section4.torusChar_monomial_frequency` is *false* and is already
  refuted in-tree by `CharacterReduction.torusChar_monomial_frequency_false`;
  the corrected form carries the standing §2 hypotheses `α ∈ Ioo 0 1`,
  `Irrational α`, which hold a.e., so nothing is lost.)
* Lemma 3.3, the anti-concentration `|Q_k(r,s)| ≥ η q_k` off a set of mass
  `O(η + e^{−c₀ k})`, **proved**,
  `AntiConcentration.shrinking_anti_concentration`.
* "Fibonacci growth makes the later frequency dominate", giving
  `|Q| ≥ ½ e^{−cH} q_k`, **proved**, `Prop42.later_frequency_dominates`.
* "Since `2λt₋ = L + λk − 80λH + O(1)`, every retained descendant satisfies
  `q_{t₋}² ≤ e^{−cH} n|Q|`", **proved**,
  `Prop42.retained_descendant_exponent`, and at a ledger-compatible constant by
  `retained_descendant_at_compat` below.
* Lemma 3.4, converse half, display (23), **proved**,
  `CylinderPhase.descendant_phase_small`.
* Lemma 3.4, substantive half, display (22), **proved**,
  `Display22.descendant_cylinder_estimate`.
* Lemma 3.2, conditional multi-block mixing, needed for the
  `k > t₀ + 100H` branch of case 3, **proved** for BV observables,
  `BVMixing.lemma_3_2_BV`.
* **Display (20), the Lévy large-deviation bound for the continuants** -
  `e^{λj−δH} ≤ q_j ≤ e^{λj+δH}` outside a set of mass `O(e^{−c√L})` -
  **absent**.

**Finding (obstruction, corrected).**  Display (20) is the one analytic input
of cases 2 and 3 that this development does not contain in any form.  A grep
for a bound of the shape `exp (lyapunov * j ± δ * H)` on `denom` returns
nothing in `Kwon1002/`, and the 35-module Wang substrate has no continuant
large-deviation estimate either (`Erdos1002.LevyContinuity` is the
characteristic-function continuity theorem, unrelated).  Yet (20) is used
*four times* in the two cases: it supplies the hypotheses `hqt` and `hqk` of
`Prop42.retained_descendant_exponent` in both the `t₋` branches; it supplies
the lower bound `q_{t₊} ≥ e^{λt₊−δH}` of the `t₊` branch; and it is what makes
each "discarded union has mass `O(e^{−cL^{1/2}})`" true, i.e. it is the sole
source of the first summand of the error bracket of (34).  Removing the other
gaps therefore does not shorten the path: (20) is load-bearing and has to be
formalised before either phase bound can be attempted.

`Display20` below records it as a predicate, so the missing input is at least
machine-readable and can be quoted verbatim by a later pass.  It is a `def`,
not a sorried theorem: nothing is assumed here. -/

/-- **Display (20)** of the manuscript, as a predicate: outside a set of
Lebesgue measure `C e^{−c√L}`, every bulk continuant obeys the two-sided Lévy
bound at deviation `δH`.  Nothing in this file assumes it; it is stated so that
the gap identified in §4 has a name. -/
def Display20 (C δ c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
    volume.real {α ∈ Ioo (0 : ℝ) 1 |
        ¬ (Real.exp (lyapunov * (j : ℝ) - δ * Hscale n) ≤ (denom α j : ℝ)
            ∧ (denom α j : ℝ) ≤ Real.exp (lyapunov * (j : ℝ) + δ * Hscale n))}
      ≤ C * Real.exp (-c * Real.sqrt (Lnorm n))

/-- **The retained-descendant line of the manuscript, at a ledger constant.**
`Prop42.retained_descendant_exponent` produces the rate `80λ − 3δ − c`; Kwon
writes the conclusion with the *same* `c` as the anti-concentration constant.
Under the ledger entry `retainedMinus` (`2c + 3δ < 80λ`) that reuse is
legitimate, and this lemma is the manuscript's line verbatim:
`q_{t₋}² ≤ e^{−cH} n|Q|` up to the absolute factor `2e^A`. -/
lemma retained_descendant_at_compat
    {L H del cc A t k qt qk Q nn : ℝ} (hH : 0 ≤ H)
    (hled : 2 * cc + 3 * del < 80 * lyapunov)
    (hqt0 : 0 ≤ qt)
    (hqt : qt ≤ Real.exp (lyapunov * t + del * H))
    (hqk : Real.exp (lyapunov * k - del * H) ≤ qk)
    (hQ : (1 / 2) * Real.exp (-cc * H) * qk ≤ Q)
    (hnn : Real.exp L ≤ nn)
    (ht : 2 * (lyapunov * t) = L + lyapunov * k - 80 * lyapunov * H + A) :
    qt ^ 2 ≤ 2 * Real.exp A * Real.exp (-cc * H) * (nn * Q) := by
  have hbase := Prop42.retained_descendant_exponent hqt0 hqt hqk hQ hnn ht
  have hqk0 : 0 ≤ qk := le_trans (Real.exp_pos _).le hqk
  have hQ0 : 0 ≤ Q := le_trans (by positivity) hQ
  have hnn0 : 0 ≤ nn := le_trans (Real.exp_pos _).le hnn
  have hrate : cc ≤ 80 * lyapunov - 3 * del - cc := by linarith
  have hexp : Real.exp (-(80 * lyapunov - 3 * del - cc) * H) ≤ Real.exp (-cc * H) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hfac : (0 : ℝ) ≤ 2 * Real.exp A := by positivity
  refine le_trans hbase ?_
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hnn0 hQ0)
  exact mul_le_mul_of_nonneg_left hexp hfac

/-! ## 5. The monomial core -/

/-- **Monomial core of Proposition 4.2**, token-identical to
`Kwon1002.Prop42.two_block_monomial_core`, assembled from the reduced case 1
(`zeroMode_gauss_mixing'`, proved here from `zeroMode_cylinder_mixing`) and
cases 2-3. -/
theorem two_block_monomial_core'' (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ Prop42.modeBox K, ∀ w' ∈ Wv, ∀ m' ∈ Prop42.modeBox K,
        (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
            ¬ ‖(∫ α in Ioo (0 : ℝ) 1,
                    Prop42.monoAt R w m.1 m.2 α n p.1 * Prop42.monoAt R w' m'.1 m'.2 α n p.2)
                  - Prop42.monoStationary R w m.1 m.2 * Prop42.monoStationary R w' m'.1 m'.2‖
                ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                        + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n))}).ncard : ℝ)
          ≤ C * Lnorm n * Hscale n := by
  classical
  obtain ⟨CA, cA, ρA, hCA0, hcA0, hρA0, hρA1, hA⟩ := zeroMode_gauss_mixing' R Wu Wv
  obtain ⟨CB, cB, ρB, hCB0, hcB0, hρB0, hρB1, hB⟩ :=
    MonomialCore.laterMode_phase_bound R K Wu Wv
  obtain ⟨CD, cD, ρD, hCD0, hcD0, hρD0, hρD1, hD⟩ :=
    MonomialCore.earlierMode_phase_bound R K Wu Wv
  set C₁ : ℝ := max CA (max CB CD) with hC₁def
  set c₁ : ℝ := min cA (min cB cD) with hc₁def
  set ρ₁ : ℝ := max ρA (max ρB ρD) with hρ₁def
  set A : ℝ := 1 / lyapunov + 1 with hAdef
  have hA0 : 0 < A := by
    have h := one_div_pos.2 Prop42.lyapunov_pos
    rw [hAdef]; linarith
  set C : ℝ := max C₁ (A * (C₁ + 205)) with hCdef
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le hCA0 (le_max_left _ _)
  have hc₁0 : 0 < c₁ := lt_min hcA0 (lt_min hcB0 hcD0)
  have hρ₁0 : 0 < ρ₁ := lt_of_lt_of_le hρA0 (le_max_left _ _)
  have hρ₁1 : ρ₁ < 1 := max_lt hρA1 (max_lt hρB1 hρD1)
  have hC0 : 0 < C := lt_of_lt_of_le hC₁0 (le_max_left _ _)
  have hC₁C : C₁ ≤ C := le_max_left _ _
  refine ⟨C, c₁, ρ₁, hC0, hc₁0, hρ₁0, hρ₁1, ?_⟩
  have htend : Filter.Tendsto (fun n : ℕ => Lnorm n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hA, hB, hD, htend.eventually_ge_atTop 1] with n hAn hBn hDn hL1
  intro w hw m hm w' hw' m' hm'
  have hL0 : (0 : ℝ) ≤ Lnorm n := by linarith
  have hH1 : (1 : ℝ) ≤ Hscale n := MonomialCore.one_le_Hscale hL1
  have hH0 : (0 : ℝ) ≤ Hscale n := by linarith
  set Exc : Finset (ℕ × ℕ) :=
    MonomialCore.nearDiag n (C₁ * Hscale n) ∪ MonomialCore.nearRes n (100 * Hscale n)
    with hExcdef
  have hsub : {p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
      ¬ ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w m.1 m.2 α n p.1 * Prop42.monoAt R w' m'.1 m'.2 α n p.2)
            - Prop42.monoStationary R w m.1 m.2 * Prop42.monoStationary R w' m'.1 m'.2‖
          ≤ C * (Real.exp (-c₁ * Real.sqrt (Lnorm n))
                  + Real.exp (-c₁ * Hscale n) + ρ₁ ^ (c₁ * Hscale n))} ⊆ ↑Exc := by
    rintro p ⟨hp1, hp2⟩
    by_contra hcon
    apply hp2
    have hpb : p ∈ bulkPairs n := Finset.mem_coe.mp hp1
    have hnd : p ∉ MonomialCore.nearDiag n (C₁ * Hscale n) := fun h =>
      hcon (Finset.mem_coe.2 (Finset.mem_union_left _ h))
    have hnr : p ∉ MonomialCore.nearRes n (100 * Hscale n) := fun h =>
      hcon (Finset.mem_coe.2 (Finset.mem_union_right _ h))
    have hgap : C₁ * Hscale n < (p.2 : ℝ) - (p.1 : ℝ) := by
      by_contra hg
      push_neg at hg
      exact hnd (Finset.mem_filter.2 ⟨hpb, hg⟩)
    have hres : 100 * Hscale n < |(p.2 : ℝ) - ((mIndex n : ℝ) + (p.1 : ℝ)) / 2| := by
      by_contra hg
      push_neg at hg
      exact hnr (Finset.mem_filter.2 ⟨hpb, hg⟩)
    by_cases hm'0 : m' = (0, 0)
    · have hm'1 : m'.1 = 0 := by rw [hm'0]
      have hm'2 : m'.2 = 0 := by rw [hm'0]
      by_cases hm0 : m = (0, 0)
      · have hm1 : m.1 = 0 := by rw [hm0]
        have hm2 : m.2 = 0 := by rw [hm0]
        rw [hm1, hm2, hm'1, hm'2]
        refine le_trans (hAn w hw w' hw' p hpb ?_) ?_
        · calc CA * Hscale n ≤ C₁ * Hscale n :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) hH0
            _ < _ := hgap
        · exact MonomialCore.err_le hCA0 (le_trans (le_max_left _ _) hC₁C) hc₁0
            (min_le_left _ _) hρA0 (le_max_left _ _) hρ₁1 hL0 hH0
      · have hstat : Prop42.monoStationary R w m.1 m.2 = 0 :=
          MonomialCore.monoStationary_eq_zero R w (by rw [Prod.mk.eta]; exact hm0)
        rw [hm'1, hm'2, hstat, zero_mul, sub_zero]
        refine le_trans (hDn w hw m hm hm0 w' hw' p hpb hres) ?_
        exact MonomialCore.err_le hCD0
          (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC₁C)
          hc₁0 (le_trans (min_le_right _ _) (min_le_right _ _))
          hρD0 (le_trans (le_max_right _ _) (le_max_right _ _)) hρ₁1 hL0 hH0
    · have hstat : Prop42.monoStationary R w' m'.1 m'.2 = 0 :=
        MonomialCore.monoStationary_eq_zero R w' (by rw [Prod.mk.eta]; exact hm'0)
      rw [hstat, mul_zero, sub_zero]
      refine le_trans (hBn w hw m hm w' hw' m' hm' hm'0 p hpb ?_) ?_
      · calc CB * Hscale n ≤ C₁ * Hscale n :=
              mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _)) hH0
          _ < _ := hgap
      · exact MonomialCore.err_le hCB0
          (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC₁C)
          hc₁0 (le_trans (min_le_right _ _) (min_le_left _ _))
          hρB0 (le_trans (le_max_left _ _) (le_max_right _ _)) hρ₁1 hL0 hH0
  have hfin := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hfin
  have hcount : ((Exc.card : ℕ) : ℝ) ≤ C * Lnorm n * Hscale n := by
    have h1 : ((Exc.card : ℕ) : ℝ) ≤ (A * (C₁ + 205)) * Lnorm n * Hscale n := by
      rw [hExcdef, hAdef]
      exact MonomialCore.exc_card_bound n C₁ hC₁0.le hL1
    have h2 : A * (C₁ + 205) ≤ C := le_max_right _ _
    calc ((Exc.card : ℕ) : ℝ) ≤ (A * (C₁ + 205)) * Lnorm n * Hscale n := h1
      _ = (A * (C₁ + 205)) * (Lnorm n * Hscale n) := by ring
      _ ≤ C * (Lnorm n * Hscale n) := mul_le_mul_of_nonneg_right h2 (mul_nonneg hL0 hH0)
      _ = C * Lnorm n * Hscale n := by ring
  refine le_trans ?_ hcount
  exact_mod_cast hfin

/-- **The ledger costs nothing.**  The monomial core holds with a constant `c`
satisfying the *entire* compatibility ledger of §3, for any denominator
deviation `δ ≤ 1` and any positive Lemma 3.3 decay constant `c₀`. -/
theorem two_block_monomial_core_compat (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ))
    {δ c₀ : ℝ} (hδ : δ ≤ 1) (hc₀ : 0 < c₀) :
    ∃ C c ρ : ℝ, 0 < C ∧ Compat c δ c₀ ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ Prop42.modeBox K, ∀ w' ∈ Wv, ∀ m' ∈ Prop42.modeBox K,
        ((badPairs R w w' m m' C c ρ n).ncard : ℝ) ≤ C * Lnorm n * Hscale n := by
  obtain ⟨C, c, ρ, hC, hc, hρ0, hρ1, hcore⟩ := two_block_monomial_core'' R K Wu Wv
  set c' : ℝ := min c (min 1 (200 * c₀)) with hc'def
  have hc'0 : 0 < c' := lt_min hc (lt_min one_pos (by linarith))
  have hc'c : c' ≤ c := min_le_left _ _
  have hc'1 : c' ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hc'₀ : c' ≤ 200 * c₀ := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨C, c', ρ, hC, compat_of_le_one hc'0 hc'1 hδ hc'₀, hρ0, hρ1, ?_⟩
  filter_upwards [hcore, eventually_ge_atTop 1] with n hn hn1
  intro w hw m hm w' hw' m' hm'
  have hL0 : (0 : ℝ) ≤ Lnorm n := Real.log_nonneg (by exact_mod_cast hn1)
  have hH0 : (0 : ℝ) ≤ Hscale n := Real.rpow_nonneg hL0 _
  refine le_trans ?_ (hn w hw m hm w' hw' m' hm')
  have hsub : badPairs R w w' m m' C c' ρ n ⊆ badPairs R w w' m m' C c ρ n :=
    badPairs_mono hC hc'0 hc'c hρ0 hρ1 hL0 hH0
  have := Set.ncard_le_ncard hsub (badPairs_finite R w w' m m' C c ρ n)
  exact_mod_cast this

end

end P42Cases

/-! ## 6. Token-identical restatements

`two_block_monomial_core''` below is a byte-for-byte copy of
`Kwon1002.Prop42.two_block_monomial_core` (Prop42.lean lines 582-591) with only
the name primed (double-primed: `MonomialCore.lean` already claims the single
prime), and `prop_4_2_two_block_factorization'` is a byte-for-byte
copy of the canonical `Kwon1002.prop_4_2_two_block_factorization`
(Section4.lean lines 263-270), likewise only renamed. -/

namespace Prop42

noncomputable section

theorem two_block_monomial_core'' (R K : ℕ) (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ modeBox K, ∀ w' ∈ Wv, ∀ m' ∈ modeBox K,
        (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
            ¬ ‖(∫ α in Ioo (0 : ℝ) 1,
                    monoAt R w m.1 m.2 α n p.1 * monoAt R w' m'.1 m'.2 α n p.2)
                  - monoStationary R w m.1 m.2 * monoStationary R w' m'.1 m'.2‖
                ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                        + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n))}).ncard : ℝ)
          ≤ C * Lnorm n * Hscale n :=
  P42Cases.two_block_monomial_core'' R K Wu Wv

end

end Prop42

noncomputable section

/-- **Proposition 4.2** (Two-block factorization), display (34), token-identical
to `Kwon1002.prop_4_2_two_block_factorization`, proved from the monomial core
of §5 by the bilinear bookkeeping of `Prop42`. -/
theorem prop_4_2_two_block_factorization' {R K : ℕ} (U V : WindowSymbol R K) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
          ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
                - U.stationaryIntegral * V.stationaryIntegral‖
              ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                      + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n))}).ncard : ℝ)
        ≤ C * Lnorm n * Hscale n := by
  classical
  obtain ⟨C₀, c, ρ, hC₀, hc, hρ0, hρ1, hcore⟩ :=
    Prop42.two_block_monomial_core'' R K U.words V.words
  set C : ℝ := max 1 (max
      ((∑ t ∈ Prop42.symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
        * (∑ t' ∈ Prop42.symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * C₀)
      ((((Prop42.symIdx U).card * (Prop42.symIdx V).card : ℕ) : ℝ) * C₀)) with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hCA : (∑ t ∈ Prop42.symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
      * (∑ t' ∈ Prop42.symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * C₀ ≤ C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hCN : (((Prop42.symIdx U).card * (Prop42.symIdx V).card : ℕ) : ℝ) * C₀ ≤ C :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, c, ρ, by linarith, hc, hρ0, hρ1, ?_⟩
  filter_upwards [hcore, eventually_ge_atTop 1] with n hn hn1
  have hL : (0 : ℝ) ≤ Lnorm n := Real.log_nonneg (by exact_mod_cast hn1)
  have hH : (0 : ℝ) ≤ Hscale n := Real.rpow_nonneg hL _
  set E : ℝ := Real.exp (-c * Real.sqrt (Lnorm n)) + Real.exp (-c * Hscale n)
      + ρ ^ (c * Hscale n) with hEdef
  have hEpos : 0 < E := by
    have h1 := Real.exp_pos (-c * Real.sqrt (Lnorm n))
    have h2 := Real.exp_pos (-c * Hscale n)
    have h3 := Real.rpow_pos_of_pos hρ0 (c * Hscale n)
    rw [hEdef]; linarith
  set Bad : (((Fin (2 * R) → ℕ) × ℤ × ℤ) × ((Fin (2 * R) → ℕ) × ℤ × ℤ)) → Finset (ℕ × ℕ) :=
    fun q => (bulkPairs n).filter (fun p =>
      ¬ ‖(∫ α in Ioo (0 : ℝ) 1,
            Prop42.monoAt R q.1.1 q.1.2.1 q.1.2.2 α n p.1
              * Prop42.monoAt R q.2.1 q.2.2.1 q.2.2.2 α n p.2)
          - Prop42.monoStationary R q.1.1 q.1.2.1 q.1.2.2
            * Prop42.monoStationary R q.2.1 q.2.2.1 q.2.2.2‖
        ≤ C₀ * E) with hBad
  have hIdx : ∀ q ∈ Prop42.symIdx U ×ˢ Prop42.symIdx V,
      ((Bad q).card : ℝ) ≤ C₀ * Lnorm n * Hscale n := by
    intro q hq
    rw [Finset.mem_product] at hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [Prop42.symIdx, Finset.mem_product] at hq1 hq2
    have hcore' := hn q.1.1 hq1.1 q.1.2 hq1.2 q.2.1 hq2.1 q.2.2 hq2.2
    rw [hBad]
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    exact hcore'
  have hsub : {p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
      ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
            - U.stationaryIntegral * V.stationaryIntegral‖ ≤ C * E}
      ⊆ ↑((Prop42.symIdx U ×ˢ Prop42.symIdx V).biUnion Bad) := by
    rintro p ⟨hp1, hp2⟩
    rw [Finset.mem_coe, Finset.mem_biUnion]
    by_contra hcon
    push_neg at hcon
    apply hp2
    have hmono : ∀ t ∈ Prop42.symIdx U, ∀ t' ∈ Prop42.symIdx V,
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R t.1 t.2.1 t.2.2 α n p.1
                * Prop42.monoAt R t'.1 t'.2.1 t'.2.2 α n p.2)
            - Prop42.monoStationary R t.1 t.2.1 t.2.2
              * Prop42.monoStationary R t'.1 t'.2.1 t'.2.2‖
          ≤ C₀ * E := by
      intro t ht t' ht'
      have hq := hcon (t, t') (Finset.mem_product.mpr ⟨ht, ht'⟩)
      simp only [hBad, Finset.mem_filter, not_and, not_not] at hq
      exact hq (Finset.mem_coe.mp hp1)
    calc ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
            - U.stationaryIntegral * V.stationaryIntegral‖
        ≤ (∑ t ∈ Prop42.symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
            * (∑ t' ∈ Prop42.symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * (C₀ * E) :=
          Prop42.two_block_bound_of_mono U V n p.1 p.2 (C₀ * E) hmono
      _ = ((∑ t ∈ Prop42.symIdx U, ‖U.coeff t.1 t.2.1 t.2.2‖)
            * (∑ t' ∈ Prop42.symIdx V, ‖V.coeff t'.1 t'.2.1 t'.2.2‖) * C₀) * E := by ring
      _ ≤ C * E := mul_le_mul_of_nonneg_right hCA hEpos.le
  calc (({p ∈ (bulkPairs n : Set (ℕ × ℕ)) |
          ¬ ‖(∫ α in Ioo (0 : ℝ) 1, U.at α n p.1 * V.at α n p.2)
                - U.stationaryIntegral * V.stationaryIntegral‖ ≤ C * E}).ncard : ℝ)
      ≤ ((((Prop42.symIdx U ×ˢ Prop42.symIdx V).biUnion Bad).card : ℕ) : ℝ) := by
        have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        rw [Set.ncard_coe_finset] at h
        exact_mod_cast h
    _ ≤ ∑ q ∈ Prop42.symIdx U ×ˢ Prop42.symIdx V, ((Bad q).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ Prop42.symIdx U ×ˢ Prop42.symIdx V, C₀ * Lnorm n * Hscale n :=
        Finset.sum_le_sum hIdx
    _ = (((Prop42.symIdx U).card * (Prop42.symIdx V).card : ℕ) : ℝ) * C₀
          * (Lnorm n * Hscale n) := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ C * (Lnorm n * Hscale n) :=
        mul_le_mul_of_nonneg_right hCN (mul_nonneg hL hH)
    _ = C * Lnorm n * Hscale n := by ring

end

end Kwon1002

