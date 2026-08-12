import Kwon1002.TransferIdentity
import Kwon1002.MixingBV
import Kwon1002.LDObservable

/-!
# Large deviations, stage A4: relative decoupling of digit past and orbit future

The Bernstein block argument needs *relative* (ψ-mixing–type) factorization
against **arbitrary** bounded nonnegative future observables — no BV or
Lipschitz condition on the future — because block observables
`exp(2s Σ g_u(x̂_i))` have unbounded variation as functions of `α`.

Route: the in-tree conditional density of a positive cylinder is
`kwonDensity a b` (`TransferIdentity.exists_cylinder_condDensity'`), with
`0 ≤ φ ≤ 8`, Lipschitz constant `24`, `∫ φ dν = 1`.  Then for any gap `M`
and nonnegative bounded measurable `Φ`:

`∫_{I_w} Φ(T^{|w|+M} α) dν = ν(I_w) ∫ (L^M φ_w) Φ dν
   ≤ (1 + 24 ρ₀^M) ν(I_w) ∫ Φ dν`, `ρ₀ = 527/540`,

by the adjoint identity and the sup-norm contraction
`|L^M φ_w − 1| ≤ 24 ρ₀^M`.  Summing over the countable depth-`D`
partition (`gaussPrefixPartitionCell`) lifts this to arbitrary
nonnegative bounded digit-determined pasts, and induction along a list of
separated digit-window blocks gives the product factorization.
-/

open Set MeasureTheory

namespace Kwon1002

namespace LargeDeviation

noncomputable section

/-- A function of the first `D` digits (on the full-measure set of
irrationals of `(0,1)`). -/
def DigitDetermined (D : ℕ) (P : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, x ∈ Ioo (0 : ℝ) 1 → Irrational x →
    y ∈ Ioo (0 : ℝ) 1 → Irrational y →
    (∀ i, i < D → digit x i = digit y i) → P x = P y

/-! ### Private helpers -/

/-- Any positive-word half-open cylinder sits in `(0,1]` up to the single
point `0` (only the empty word's cylinder `[0,1)` contains it). -/
private theorem halfOpen_diff_Ioc_subset (v : List ℕ) (hv : ∀ q ∈ v, 0 < q) :
    Erdos1002.gaussHalfOpenPrefixCylinder v \ Ioc (0 : ℝ) 1 ⊆ ({0} : Set ℝ) := by
  cases v with
  | nil =>
      intro x hx
      have h1 : x ∈ Ico (0 : ℝ) 1 := hx.1
      have h2 : x ∉ Ioc (0 : ℝ) 1 := hx.2
      have hx0 : x ≤ 0 := by
        by_contra h
        exact h2 ⟨lt_of_not_ge h, h1.2.le⟩
      have hx0' : x = 0 := le_antisymm hx0 h1.1
      simp [hx0']
  | cons q qs =>
      intro x hx
      exfalso
      have hq : 0 < q := hv q (List.mem_cons_self ..)
      have hcyl : Erdos1002.gaussHalfOpenPrefixCylinder (q :: qs)
          = Erdos1002.firstDigitCylinder q ∩
            Erdos1002.gaussMap ⁻¹' Erdos1002.gaussHalfOpenPrefixCylinder qs := rfl
      rw [hcyl] at hx
      have h1 : x ∈ Erdos1002.firstDigitCylinder q := hx.1.1
      have hfd : Erdos1002.firstDigitCylinder q
          = Ioc (1 / ((q + 1 : ℕ) : ℝ)) (1 / (q : ℝ)) := rfl
      rw [hfd] at h1
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have hlow : (0 : ℝ) < 1 / ((q + 1 : ℕ) : ℝ) := by positivity
      have hup : 1 / (q : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      exact hx.2 ⟨lt_trans hlow h1.1, le_trans h1.2 hup⟩

/-- The `some w` partition cell agrees `γ`-a.e. with the raw half-open
cylinder of `w` (they differ at most at the volume-null point `0`). -/
private theorem cell_some_ae_eq (D : ℕ) (w : Erdos1002.PositiveDigitWord D) :
    Erdos1002.gaussPrefixPartitionCell D (some w)
      =ᵐ[Erdos1002.gaussMeasure] Erdos1002.gaussHalfOpenPrefixCylinder w.1 := by
  have hcell : Erdos1002.gaussPrefixPartitionCell D (some w)
      = Ioc (0 : ℝ) 1 ∩ Erdos1002.gaussHalfOpenPrefixCylinder w.1 := rfl
  have hnull : Erdos1002.gaussMeasure ({0} : Set ℝ) = 0 :=
    gaussMeasure_absCont Real.volume_singleton
  rw [hcell, ae_eq_set]
  constructor
  · exact measure_mono_null (fun x hx => absurd hx.1.2 hx.2) measure_empty
  · refine measure_mono_null (fun x hx => ?_) hnull
    exact halfOpen_diff_Ioc_subset w.1 w.2.2 ⟨hx.1, fun hI => hx.2 ⟨hI, hx.1⟩⟩

/-- An integrable observable's Gauss integral is the countable sum of its
integrals over the depth-`D` prefix-partition cells. -/
private theorem integral_eq_tsum_partition (D : ℕ) {g : ℝ → ℝ}
    (hg : Integrable g Erdos1002.gaussMeasure) :
    ∫ x, g x ∂Erdos1002.gaussMeasure
      = ∑' i : Erdos1002.GaussPrefixPartitionIndex D,
          ∫ x in Erdos1002.gaussPrefixPartitionCell D i, g x
            ∂Erdos1002.gaussMeasure := by
  have hcompl : Erdos1002.gaussMeasure (Ioc (0 : ℝ) 1)ᶜ = 0 := by
    have h : Erdos1002.gaussMeasure {x : ℝ | x ∈ Ioc (0 : ℝ) 1}ᶜ = 0 :=
      mem_ae_iff.mp Erdos1002.gaussMeasure_unit_ae
    exact h
  have h1 : ∫ x, g x ∂Erdos1002.gaussMeasure
      = ∫ x in Ioc (0 : ℝ) 1, g x ∂Erdos1002.gaussMeasure := by
    have h2 := integral_add_compl
      (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1)) hg
    rw [setIntegral_measure_zero _ hcompl, add_zero] at h2
    exact h2.symm
  rw [h1, ← Erdos1002.iUnion_gaussPrefixPartitionCell D]
  exact integral_iUnion
    (fun i => Erdos1002.measurableSet_gaussPrefixPartitionCell D i)
    (Erdos1002.pairwise_disjoint_gaussPrefixPartitionCell D)
    hg.integrableOn

/-- Iterating the Gauss map composes additively. -/
private theorem gaussIter_comp (x : ℝ) (n i : ℕ) :
    gaussIter (gaussIter x n) i = gaussIter x (n + i) := by
  show gaussMap^[i] (gaussMap^[n] x) = gaussMap^[n + i] x
  rw [← Function.iterate_add_apply, Nat.add_comm i n]

/-- Digits of the shifted orbit are shifted digits. -/
private theorem digit_shift (x : ℝ) (n i : ℕ) :
    digit (Erdos1002.gaussOrbit n x) i = digit x (n + i) := by
  have h : gaussIter (Erdos1002.gaussOrbit n x) i = gaussIter x (n + i) := by
    rw [← gaussIter_eq_gaussOrbit x n]
    exact gaussIter_comp x n i
  simp only [digit, h]

/-- In a `(V+M)`-separated chain, every later offset clears the head's
window. -/
private theorem isChain_head_le (V M : ℕ) :
    ∀ (l : List (ℕ × (ℝ → ℝ))) (a : ℕ × (ℝ → ℝ)),
      List.IsChain (fun p q : ℕ × (ℝ → ℝ) => p.1 + V + M ≤ q.1) (a :: l) →
      ∀ b ∈ l, a.1 + V + M ≤ b.1 := by
  intro l
  induction l with
  | nil => intro a _ b hb; simp at hb
  | cons c l ih =>
      intro a h b hb
      have hac : a.1 + V + M ≤ c.1 := h.rel_head
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hac
      · have hcb := ih c h.of_cons b hb'
        omega

/-- Measurability of a shifted block product. -/
private theorem measurable_orbitProd (τ : ℕ × (ℝ → ℝ) → ℕ) :
    ∀ l : List (ℕ × (ℝ → ℝ)), (∀ r ∈ l, Measurable r.2) →
      Measurable fun y =>
        (l.map (fun r => r.2 (Erdos1002.gaussOrbit (τ r) y))).prod := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons r l ih =>
      intro h
      simp only [List.map_cons, List.prod_cons]
      exact ((h r (List.mem_cons_self ..)).comp
        (Erdos1002.measurable_gaussOrbit (τ r))).mul
        (ih fun s hs => h s (List.mem_cons_of_mem _ hs))

/-- Nonnegativity of a shifted block product. -/
private theorem orbitProd_nonneg (τ : ℕ × (ℝ → ℝ) → ℕ)
    (l : List (ℕ × (ℝ → ℝ))) (h0 : ∀ r ∈ l, ∀ x, 0 ≤ r.2 x) (y : ℝ) :
    0 ≤ (l.map (fun r => r.2 (Erdos1002.gaussOrbit (τ r) y))).prod := by
  apply List.prod_nonneg
  intro a ha
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
  exact h0 r hr _

/-- Uniform bound `B ^ length` on a shifted block product. -/
private theorem orbitProd_le (τ : ℕ × (ℝ → ℝ) → ℕ) {B : ℝ} (hB : 1 ≤ B) :
    ∀ l : List (ℕ × (ℝ → ℝ)), (∀ r ∈ l, ∀ x, 0 ≤ r.2 x) →
      (∀ r ∈ l, ∀ x, r.2 x ≤ B) → ∀ y : ℝ,
      (l.map (fun r => r.2 (Erdos1002.gaussOrbit (τ r) y))).prod
        ≤ B ^ l.length := by
  intro l
  induction l with
  | nil => intro _ _ y; simp
  | cons r l ih =>
      intro h0 hbd y
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      have h1 : r.2 (Erdos1002.gaussOrbit (τ r) y) ≤ B :=
        hbd r (List.mem_cons_self ..) _
      have h2 := ih (fun s hs => h0 s (List.mem_cons_of_mem _ hs))
        (fun s hs => hbd s (List.mem_cons_of_mem _ hs)) y
      have h20 : 0 ≤ (l.map (fun r =>
          r.2 (Erdos1002.gaussOrbit (τ r) y))).prod :=
        orbitProd_nonneg τ l (fun s hs => h0 s (List.mem_cons_of_mem _ hs)) y
      have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB
      rw [pow_succ']
      exact mul_le_mul h1 h2 h20 hB0

/-- **Per-cylinder relative decoupling.**  Conditionally on a positive
cylinder, a bounded nonnegative future observable beyond gap `M` has
conditional mean at most `(1 + 24 ρ₀^M)` times its stationary mean. -/
theorem cylinder_future_decouple (w : List ℕ) (hw : ∀ q ∈ w, 0 < q)
    (hpos : 0 < (Erdos1002.gaussMeasure
      (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal)
    (M : ℕ) {Φ : ℝ → ℝ} (hΦm : Measurable Φ) (hΦ0 : ∀ x, 0 ≤ Φ x)
    {B : ℝ} (hΦB : ∀ x, Φ x ≤ B) :
    ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
        Φ (Erdos1002.gaussOrbit (w.length + M) α) ∂Erdos1002.gaussMeasure
      ≤ (1 + 24 * (527 / 540 : ℝ) ^ M)
          * (Erdos1002.gaussMeasure
              (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
          * ∫ x, Φ x ∂Erdos1002.gaussMeasure := by
  obtain ⟨a, b, ha, hb, hrep⟩ :=
    TransferIdentity.exists_cylinder_condDensity' w hw hpos
  have hFm : Measurable fun y => Φ (Erdos1002.gaussOrbit M y) :=
    hΦm.comp (Erdos1002.measurable_gaussOrbit M)
  have hkey := hrep (fun y => Φ (Erdos1002.gaussOrbit M y)) hFm
  simp only [Transfer.condMean] at hkey
  have hnum := (div_eq_iff (ne_of_gt hpos)).mp hkey
  have hswap : ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
        Φ (Erdos1002.gaussOrbit (w.length + M) α) ∂Erdos1002.gaussMeasure
      = ∫ x in Erdos1002.gaussHalfOpenPrefixCylinder w,
          Φ (Erdos1002.gaussOrbit M (Erdos1002.gaussOrbit w.length x))
            ∂Erdos1002.gaussMeasure :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      show Φ (Erdos1002.gaussOrbit (w.length + M) x)
        = Φ (Erdos1002.gaussOrbit M (Erdos1002.gaussOrbit w.length x))
      rw [Nat.add_comm w.length M, gaussOrbit_add])
  have hadj : ∫ y, Transfer.kwonDensity a b y * Φ (Erdos1002.gaussOrbit M y)
        ∂Erdos1002.gaussMeasure
      = ∫ y, (Erdos1002.gaussTransfer^[M]) (Transfer.kwonDensity a b) y * Φ y
          ∂Erdos1002.gaussMeasure :=
    Erdos1002.integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate
      (Transfer.measurable_kwonDensity a b) hΦm
      (Transfer.kwonDensity_nonneg ha hb) (Transfer.kwonDensity_le ha hb) M
  have hb8 := Erdos1002.gaussTransfer_iterate_unit_bounds
    (Transfer.kwonDensity_nonneg ha hb) (Transfer.kwonDensity_le ha hb) M
  have hIntT : Integrable
      ((Erdos1002.gaussTransfer^[M]) (Transfer.kwonDensity a b))
      Erdos1002.gaussMeasure :=
    Erdos1002.integrable_gaussTransfer_iterate_of_unit_bounds
      (Transfer.measurable_kwonDensity a b)
      (Transfer.kwonDensity_nonneg ha hb) (Transfer.kwonDensity_le ha hb) M
  have hΦint : Integrable Φ Erdos1002.gaussMeasure :=
    Integrable.of_bound hΦm.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hΦ0 x)]; exact hΦB x)
  have hprodint : Integrable (fun y =>
      (Erdos1002.gaussTransfer^[M]) (Transfer.kwonDensity a b) y * Φ y)
      Erdos1002.gaussMeasure := by
    refine Integrable.of_bound
      (hIntT.aestronglyMeasurable.mul hΦm.aestronglyMeasurable) (8 * B) ?_
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with y hy
    have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb8.1 hycc),
      abs_of_nonneg (hΦ0 y)]
    exact mul_le_mul (hb8.2 hycc) (hΦB y) (hΦ0 y) (by norm_num)
  have hptwise : ∀ᵐ y ∂Erdos1002.gaussMeasure,
      (Erdos1002.gaussTransfer^[M]) (Transfer.kwonDensity a b) y * Φ y
        ≤ (1 + 24 * (527 / 540 : ℝ) ^ M) * Φ y := by
    filter_upwards [Erdos1002.gaussMeasure_unit_ae] with y hy
    have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
    have h1 := Erdos1002.abs_gaussTransfer_iterate_sub_integral_le
      (K := 24) (by norm_num) (Transfer.measurable_kwonDensity a b)
      (Transfer.kwonDensity_nonneg ha hb) (Transfer.kwonDensity_le ha hb)
      (Transfer.kwonDensity_lipschitz ha hb) M hycc
    rw [Transfer.kwonDensity_integral_eq_one ha hb] at h1
    have h2 := (abs_le.mp h1).2
    have h3 : (Erdos1002.gaussTransfer^[M]) (Transfer.kwonDensity a b) y
        ≤ 1 + 24 * (527 / 540 : ℝ) ^ M := by linarith
    exact mul_le_mul_of_nonneg_right h3 (hΦ0 y)
  have hmono : ∫ y,
        (Erdos1002.gaussTransfer^[M]) (Transfer.kwonDensity a b) y * Φ y
          ∂Erdos1002.gaussMeasure
      ≤ (1 + 24 * (527 / 540 : ℝ) ^ M)
          * ∫ x, Φ x ∂Erdos1002.gaussMeasure := by
    have h1 := integral_mono_ae hprodint (hΦint.const_mul _) hptwise
    rwa [integral_const_mul] at h1
  calc ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder w,
        Φ (Erdos1002.gaussOrbit (w.length + M) α) ∂Erdos1002.gaussMeasure
      = (∫ y, Transfer.kwonDensity a b y * Φ (Erdos1002.gaussOrbit M y)
            ∂Erdos1002.gaussMeasure)
          * (Erdos1002.gaussMeasure
              (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal := by
        rw [hswap]; exact hnum
    _ = (∫ y, (Erdos1002.gaussTransfer^[M]) (Transfer.kwonDensity a b) y * Φ y
            ∂Erdos1002.gaussMeasure)
          * (Erdos1002.gaussMeasure
              (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal := by
        rw [hadj]
    _ ≤ ((1 + 24 * (527 / 540 : ℝ) ^ M) * ∫ x, Φ x ∂Erdos1002.gaussMeasure)
          * (Erdos1002.gaussMeasure
              (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal :=
        mul_le_mul_of_nonneg_right hmono ENNReal.toReal_nonneg
    _ = (1 + 24 * (527 / 540 : ℝ) ^ M)
          * (Erdos1002.gaussMeasure
              (Erdos1002.gaussHalfOpenPrefixCylinder w)).toReal
          * ∫ x, Φ x ∂Erdos1002.gaussMeasure := by ring

/-- **Past–future relative decoupling.**  A bounded nonnegative depth-`D`
digit-determined past decouples from any bounded nonnegative future beyond
gap `M`, with relative error `24 ρ₀^M`. -/
theorem past_future_decouple (D M : ℕ) {P Φ : ℝ → ℝ}
    (hPm : Measurable P) (hP0 : ∀ x, 0 ≤ P x) {BP : ℝ} (hPB : ∀ x, P x ≤ BP)
    (hPdet : DigitDetermined D P)
    (hΦm : Measurable Φ) (hΦ0 : ∀ x, 0 ≤ Φ x) {BΦ : ℝ} (hΦB : ∀ x, Φ x ≤ BΦ) :
    ∫ α, P α * Φ (Erdos1002.gaussOrbit (D + M) α) ∂Erdos1002.gaussMeasure
      ≤ (1 + 24 * (527 / 540 : ℝ) ^ M)
          * (∫ x, P x ∂Erdos1002.gaussMeasure)
          * ∫ x, Φ x ∂Erdos1002.gaussMeasure := by
  classical
  have hBP0 : (0 : ℝ) ≤ BP := le_trans (hP0 0) (hPB 0)
  have hfm : Measurable fun α => P α * Φ (Erdos1002.gaussOrbit (D + M) α) :=
    hPm.mul (hΦm.comp (Erdos1002.measurable_gaussOrbit (D + M)))
  have hfint : Integrable
      (fun α => P α * Φ (Erdos1002.gaussOrbit (D + M) α))
      Erdos1002.gaussMeasure :=
    Integrable.of_bound hfm.aestronglyMeasurable (BP * BΦ)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hP0 x) (hΦ0 _))]
        exact mul_le_mul (hPB x) (hΦB _) (hΦ0 _) hBP0)
  have hPint : Integrable P Erdos1002.gaussMeasure :=
    Integrable.of_bound hPm.aestronglyMeasurable BP
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hP0 x)]; exact hPB x)
  have hC0 : (0 : ℝ) ≤ 1 + 24 * (527 / 540 : ℝ) ^ M := by positivity
  -- per-cell bound
  have hcell : ∀ i : Erdos1002.GaussPrefixPartitionIndex D,
      ∫ x in Erdos1002.gaussPrefixPartitionCell D i,
          P x * Φ (Erdos1002.gaussOrbit (D + M) x) ∂Erdos1002.gaussMeasure
        ≤ ((1 + 24 * (527 / 540 : ℝ) ^ M)
              * ∫ x, Φ x ∂Erdos1002.gaussMeasure)
            * ∫ x in Erdos1002.gaussPrefixPartitionCell D i, P x
                ∂Erdos1002.gaussMeasure := by
    intro i
    cases i with
    | none =>
        have h0cell : Erdos1002.gaussMeasure
            (Erdos1002.gaussPrefixPartitionCell D none) = 0 :=
          gaussMeasure_absCont
            (Erdos1002.volume_gaussPrefixPartitionCell_none D)
        rw [setIntegral_measure_zero _ h0cell,
          setIntegral_measure_zero _ h0cell, mul_zero]
    | some w =>
        have hae := cell_some_ae_eq D w
        rw [setIntegral_congr_set hae, setIntegral_congr_set hae]
        by_cases hH0 : Erdos1002.gaussMeasure
            (Erdos1002.gaussHalfOpenPrefixCylinder w.1) = 0
        · rw [setIntegral_measure_zero _ hH0,
            setIntegral_measure_zero _ hH0, mul_zero]
        · have hposH : 0 < (Erdos1002.gaussMeasure
              (Erdos1002.gaussHalfOpenPrefixCylinder w.1)).toReal :=
            ENNReal.toReal_pos hH0 (measure_ne_top _ _)
          have hthm1 := cylinder_future_decouple w.1 w.2.2 hposH M hΦm hΦ0 hΦB
          rw [w.2.1] at hthm1
          -- a good point of the cylinder
          have hGnull : Erdos1002.gaussMeasure
              {x : ℝ | ¬(x ∈ Ioo (0 : ℝ) 1 ∧ Irrational x)} = 0 :=
            ae_iff.mp ae_gauss_unit_irrational
          have hHG : Erdos1002.gaussMeasure
              (Erdos1002.gaussHalfOpenPrefixCylinder w.1 ∩
                {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ Irrational x}) ≠ 0 := by
            intro hzero
            apply hH0
            have hsub : Erdos1002.gaussHalfOpenPrefixCylinder w.1 ⊆
                (Erdos1002.gaussHalfOpenPrefixCylinder w.1 ∩
                  {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ Irrational x}) ∪
                {x : ℝ | ¬(x ∈ Ioo (0 : ℝ) 1 ∧ Irrational x)} := by
              intro x hx
              by_cases hg : x ∈ Ioo (0 : ℝ) 1 ∧ Irrational x
              · exact Set.mem_union_left _ ⟨hx, hg⟩
              · exact Set.mem_union_right _ hg
            have hle : Erdos1002.gaussMeasure
                  (Erdos1002.gaussHalfOpenPrefixCylinder w.1)
                ≤ Erdos1002.gaussMeasure
                    (Erdos1002.gaussHalfOpenPrefixCylinder w.1 ∩
                      {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ Irrational x})
                  + Erdos1002.gaussMeasure
                      {x : ℝ | ¬(x ∈ Ioo (0 : ℝ) 1 ∧ Irrational x)} :=
              (measure_mono hsub).trans (measure_union_le _ _)
            rw [hzero, hGnull, add_zero] at hle
            exact le_antisymm hle (zero_le _)
          obtain ⟨α₀, hα₀⟩ := nonempty_of_measure_ne_zero hHG
          have horb : ∀ z : ℝ, z ∈ Ioo (0 : ℝ) 1 → Irrational z →
              ∀ k, Erdos1002.gaussOrbit k z ∈ Ioo (0 : ℝ) 1 := by
            intro z hz hirr k
            rw [← gaussIter_eq_gaussOrbit]
            exact gaussIter_mem_Ioo hz hirr k
          have hconst : ∀ x, x ∈ Erdos1002.gaussHalfOpenPrefixCylinder w.1 →
              x ∈ Ioo (0 : ℝ) 1 ∧ Irrational x → P x = P α₀ := by
            intro x hxH hxG
            apply hPdet x α₀ hxG.1 hxG.2 hα₀.2.1 hα₀.2.2
            intro i hiD
            have hxd := (MixingBV.mem_halfOpen_iff w.1 x
              (horb x hxG.1 hxG.2)).mp hxH
            have hαd := (MixingBV.mem_halfOpen_iff w.1 α₀
              (horb α₀ hα₀.2.1 hα₀.2.2)).mp hα₀.1
            have hlen : i < w.1.length := by rw [w.2.1]; exact hiD
            rw [MixingBV.digit_eq_gaussDigitAt, MixingBV.digit_eq_gaussDigitAt,
              hxd i hlen, hαd i hlen]
          have hfH : ∫ x in Erdos1002.gaussHalfOpenPrefixCylinder w.1,
                P x * Φ (Erdos1002.gaussOrbit (D + M) x)
                  ∂Erdos1002.gaussMeasure
              = P α₀ * ∫ x in Erdos1002.gaussHalfOpenPrefixCylinder w.1,
                  Φ (Erdos1002.gaussOrbit (D + M) x)
                    ∂Erdos1002.gaussMeasure := by
            rw [← integral_const_mul]
            refine setIntegral_congr_ae
              (Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w.1) ?_
            filter_upwards [ae_gauss_unit_irrational] with x hxG hxH
            rw [hconst x hxH hxG]
          have hPH : ∫ x in Erdos1002.gaussHalfOpenPrefixCylinder w.1, P x
                ∂Erdos1002.gaussMeasure
              = P α₀ * (Erdos1002.gaussMeasure
                  (Erdos1002.gaussHalfOpenPrefixCylinder w.1)).toReal := by
            have h1 : ∫ x in Erdos1002.gaussHalfOpenPrefixCylinder w.1, P x
                  ∂Erdos1002.gaussMeasure
                = ∫ _ in Erdos1002.gaussHalfOpenPrefixCylinder w.1, P α₀
                    ∂Erdos1002.gaussMeasure := by
              refine setIntegral_congr_ae
                (Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder w.1) ?_
              filter_upwards [ae_gauss_unit_irrational] with x hxG hxH
              rw [hconst x hxH hxG]
            rw [h1, setIntegral_const, smul_eq_mul, measureReal_def]
            ring
          calc ∫ x in Erdos1002.gaussHalfOpenPrefixCylinder w.1,
                P x * Φ (Erdos1002.gaussOrbit (D + M) x)
                  ∂Erdos1002.gaussMeasure
              = P α₀ * ∫ x in Erdos1002.gaussHalfOpenPrefixCylinder w.1,
                  Φ (Erdos1002.gaussOrbit (D + M) x)
                    ∂Erdos1002.gaussMeasure := hfH
            _ ≤ P α₀ * ((1 + 24 * (527 / 540 : ℝ) ^ M)
                  * (Erdos1002.gaussMeasure
                      (Erdos1002.gaussHalfOpenPrefixCylinder w.1)).toReal
                  * ∫ x, Φ x ∂Erdos1002.gaussMeasure) :=
                mul_le_mul_of_nonneg_left hthm1 (hP0 α₀)
            _ = ((1 + 24 * (527 / 540 : ℝ) ^ M)
                  * ∫ x, Φ x ∂Erdos1002.gaussMeasure)
                  * (P α₀ * (Erdos1002.gaussMeasure
                      (Erdos1002.gaussHalfOpenPrefixCylinder w.1)).toReal) := by
                ring
            _ = ((1 + 24 * (527 / 540 : ℝ) ^ M)
                  * ∫ x, Φ x ∂Erdos1002.gaussMeasure)
                  * ∫ x in Erdos1002.gaussHalfOpenPrefixCylinder w.1, P x
                      ∂Erdos1002.gaussMeasure := by
                rw [← hPH]
  -- summability of the two cell families
  have hm := fun i => Erdos1002.measurableSet_gaussPrefixPartitionCell D i
  have hd := Erdos1002.pairwise_disjoint_gaussPrefixPartitionCell D
  have hSf : Summable fun i : Erdos1002.GaussPrefixPartitionIndex D =>
      ∫ x in Erdos1002.gaussPrefixPartitionCell D i,
        P x * Φ (Erdos1002.gaussOrbit (D + M) x) ∂Erdos1002.gaussMeasure :=
    (hasSum_integral_iUnion hm hd hfint.integrableOn).summable
  have hSP : Summable fun i : Erdos1002.GaussPrefixPartitionIndex D =>
      ∫ x in Erdos1002.gaussPrefixPartitionCell D i, P x
        ∂Erdos1002.gaussMeasure :=
    (hasSum_integral_iUnion hm hd hPint.integrableOn).summable
  calc ∫ α, P α * Φ (Erdos1002.gaussOrbit (D + M) α) ∂Erdos1002.gaussMeasure
      = ∑' i : Erdos1002.GaussPrefixPartitionIndex D,
          ∫ x in Erdos1002.gaussPrefixPartitionCell D i,
            P x * Φ (Erdos1002.gaussOrbit (D + M) x)
              ∂Erdos1002.gaussMeasure :=
        integral_eq_tsum_partition D hfint
    _ ≤ ∑' i : Erdos1002.GaussPrefixPartitionIndex D,
          ((1 + 24 * (527 / 540 : ℝ) ^ M)
              * ∫ x, Φ x ∂Erdos1002.gaussMeasure)
            * ∫ x in Erdos1002.gaussPrefixPartitionCell D i, P x
                ∂Erdos1002.gaussMeasure :=
        Summable.tsum_le_tsum hcell hSf (hSP.mul_left _)
    _ = ((1 + 24 * (527 / 540 : ℝ) ^ M)
            * ∫ x, Φ x ∂Erdos1002.gaussMeasure)
          * ∑' i : Erdos1002.GaussPrefixPartitionIndex D,
              ∫ x in Erdos1002.gaussPrefixPartitionCell D i, P x
                ∂Erdos1002.gaussMeasure := tsum_mul_left
    _ = ((1 + 24 * (527 / 540 : ℝ) ^ M)
            * ∫ x, Φ x ∂Erdos1002.gaussMeasure)
          * ∫ x, P x ∂Erdos1002.gaussMeasure := by
        rw [← integral_eq_tsum_partition D hPint]
    _ = (1 + 24 * (527 / 540 : ℝ) ^ M)
          * (∫ x, P x ∂Erdos1002.gaussMeasure)
          * ∫ x, Φ x ∂Erdos1002.gaussMeasure := by ring

/-- **Separated-block product factorization.**  For a list of blocks
`(tᵢ, Ψᵢ)` with nonnegative measurable observables bounded by `B ≥ 1`,
each determined by `V` digits, whose offsets satisfy
`tᵢ + V + M ≤ tᵢ₊₁`, the product decouples up to
`(1 + 24 ρ₀^M)` per block:

`∫ Π Ψᵢ(T^{tᵢ} α) dν ≤ (1 + 24 ρ₀^M)^{len} · Π ∫ Ψᵢ dν`. -/
theorem separated_product_decouple (V M : ℕ)
    (bl : List (ℕ × (ℝ → ℝ)))
    (hmeas : ∀ p ∈ bl, Measurable p.2)
    (h0 : ∀ p ∈ bl, ∀ x, 0 ≤ p.2 x)
    {B : ℝ} (hB : 1 ≤ B) (hbd : ∀ p ∈ bl, ∀ x, p.2 x ≤ B)
    (hdet : ∀ p ∈ bl, DigitDetermined V p.2)
    (hsep : List.IsChain (fun p q : ℕ × (ℝ → ℝ) => p.1 + V + M ≤ q.1) bl) :
    ∫ α, (bl.map (fun p => p.2 (Erdos1002.gaussOrbit p.1 α))).prod
        ∂Erdos1002.gaussMeasure
      ≤ (1 + 24 * (527 / 540 : ℝ) ^ M) ^ bl.length
          * (bl.map (fun p => ∫ x, p.2 x ∂Erdos1002.gaussMeasure)).prod := by
  revert hmeas h0 hbd hdet hsep
  induction bl with
  | nil =>
      intro _ _ _ _ _
      simp
  | cons p rest ih =>
      intro hmeas h0 hbd hdet hsep
      have hpmem : p ∈ p :: rest := List.mem_cons_self ..
      have hmeas' : ∀ r ∈ rest, Measurable r.2 :=
        fun r hr => hmeas r (List.mem_cons_of_mem _ hr)
      have h0' : ∀ r ∈ rest, ∀ x, 0 ≤ r.2 x :=
        fun r hr => h0 r (List.mem_cons_of_mem _ hr)
      have hbd' : ∀ r ∈ rest, ∀ x, r.2 x ≤ B :=
        fun r hr => hbd r (List.mem_cons_of_mem _ hr)
      have hdet' : ∀ r ∈ rest, DigitDetermined V r.2 :=
        fun r hr => hdet r (List.mem_cons_of_mem _ hr)
      have hIH := ih hmeas' h0' hbd' hdet' hsep.of_cons
      have hS : ∀ r ∈ rest, p.1 + V + M ≤ r.1 :=
        isChain_head_le V M rest p hsep
      -- the shifted tail observable Ψ
      have hΨm : Measurable fun y => (rest.map (fun r =>
          r.2 (Erdos1002.gaussOrbit (r.1 - (p.1 + V + M)) y))).prod :=
        measurable_orbitProd (fun r => r.1 - (p.1 + V + M)) rest hmeas'
      have hΨ0 : ∀ y, 0 ≤ (rest.map (fun r =>
          r.2 (Erdos1002.gaussOrbit (r.1 - (p.1 + V + M)) y))).prod :=
        orbitProd_nonneg (fun r => r.1 - (p.1 + V + M)) rest h0'
      have hΨB : ∀ y, (rest.map (fun r =>
          r.2 (Erdos1002.gaussOrbit (r.1 - (p.1 + V + M)) y))).prod
            ≤ B ^ rest.length :=
        orbitProd_le (fun r => r.1 - (p.1 + V + M)) hB rest h0' hbd'
      -- the head observable
      have hPbm : Measurable fun α => p.2 (Erdos1002.gaussOrbit p.1 α) :=
        (hmeas p hpmem).comp (Erdos1002.measurable_gaussOrbit p.1)
      have hPb0 : ∀ x, 0 ≤ p.2 (Erdos1002.gaussOrbit p.1 x) :=
        fun x => h0 p hpmem _
      have hPbB : ∀ x, p.2 (Erdos1002.gaussOrbit p.1 x) ≤ B :=
        fun x => hbd p hpmem _
      have hPbdet : DigitDetermined (p.1 + V)
          fun α => p.2 (Erdos1002.gaussOrbit p.1 α) := by
        intro x y hx hxirr hy hyirr hdig
        have hox : Erdos1002.gaussOrbit p.1 x ∈ Ioo (0 : ℝ) 1 := by
          rw [← gaussIter_eq_gaussOrbit]; exact gaussIter_mem_Ioo hx hxirr p.1
        have hoy : Erdos1002.gaussOrbit p.1 y ∈ Ioo (0 : ℝ) 1 := by
          rw [← gaussIter_eq_gaussOrbit]; exact gaussIter_mem_Ioo hy hyirr p.1
        have hix : Irrational (Erdos1002.gaussOrbit p.1 x) := by
          rw [← gaussIter_eq_gaussOrbit]; exact gaussIter_irrational hxirr p.1
        have hiy : Irrational (Erdos1002.gaussOrbit p.1 y) := by
          rw [← gaussIter_eq_gaussOrbit]; exact gaussIter_irrational hyirr p.1
        refine hdet p hpmem _ _ hox hix hoy hiy fun i hi => ?_
        rw [digit_shift, digit_shift]
        exact hdig (p.1 + i) (by omega)
      -- pointwise: the tail product is Ψ read at the shifted orbit
      have hΨR : ∀ α, (rest.map (fun r =>
            r.2 (Erdos1002.gaussOrbit (r.1 - (p.1 + V + M))
              (Erdos1002.gaussOrbit (p.1 + V + M) α)))).prod
          = (rest.map (fun r =>
              r.2 (Erdos1002.gaussOrbit r.1 α))).prod := by
        intro α
        congr 1
        refine List.map_congr_left fun r hr => ?_
        rw [← gaussOrbit_add, Nat.sub_add_cancel (hS r hr)]
      have hintPb : ∫ x, p.2 (Erdos1002.gaussOrbit p.1 x)
            ∂Erdos1002.gaussMeasure
          = ∫ x, p.2 x ∂Erdos1002.gaussMeasure :=
        integral_comp_gaussOrbit p.1 p.2 (hmeas p hpmem).aestronglyMeasurable
      have hintΨ : ∫ y, (rest.map (fun r =>
            r.2 (Erdos1002.gaussOrbit (r.1 - (p.1 + V + M)) y))).prod
              ∂Erdos1002.gaussMeasure
          = ∫ α, (rest.map (fun r =>
              r.2 (Erdos1002.gaussOrbit r.1 α))).prod
                ∂Erdos1002.gaussMeasure := by
        rw [← integral_comp_gaussOrbit (p.1 + V + M) _
          hΨm.aestronglyMeasurable]
        exact integral_congr_ae (Filter.Eventually.of_forall fun α => hΨR α)
      have hmain := past_future_decouple (p.1 + V) M hPbm hPb0 hPbB hPbdet
        hΨm hΨ0 hΨB
      have hgoal_lhs : ∫ α, ((p :: rest).map (fun q =>
            q.2 (Erdos1002.gaussOrbit q.1 α))).prod ∂Erdos1002.gaussMeasure
          = ∫ α, p.2 (Erdos1002.gaussOrbit p.1 α) *
              (rest.map (fun r =>
                r.2 (Erdos1002.gaussOrbit (r.1 - (p.1 + V + M))
                  (Erdos1002.gaussOrbit (p.1 + V + M) α)))).prod
                ∂Erdos1002.gaussMeasure := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
        simp only [List.map_cons, List.prod_cons]
        rw [← hΨR α]
      have hintp0 : 0 ≤ ∫ x, p.2 x ∂Erdos1002.gaussMeasure :=
        integral_nonneg fun x => h0 p hpmem x
      have hC0 : (0 : ℝ) ≤ 1 + 24 * (527 / 540 : ℝ) ^ M := by positivity
      calc ∫ α, ((p :: rest).map (fun q =>
            q.2 (Erdos1002.gaussOrbit q.1 α))).prod ∂Erdos1002.gaussMeasure
          = ∫ α, p.2 (Erdos1002.gaussOrbit p.1 α) *
              (rest.map (fun r =>
                r.2 (Erdos1002.gaussOrbit (r.1 - (p.1 + V + M))
                  (Erdos1002.gaussOrbit (p.1 + V + M) α)))).prod
                ∂Erdos1002.gaussMeasure := hgoal_lhs
        _ ≤ (1 + 24 * (527 / 540 : ℝ) ^ M)
              * (∫ x, p.2 (Erdos1002.gaussOrbit p.1 x)
                  ∂Erdos1002.gaussMeasure)
              * ∫ y, (rest.map (fun r =>
                  r.2 (Erdos1002.gaussOrbit (r.1 - (p.1 + V + M)) y))).prod
                    ∂Erdos1002.gaussMeasure := hmain
        _ = (1 + 24 * (527 / 540 : ℝ) ^ M)
              * (∫ x, p.2 x ∂Erdos1002.gaussMeasure)
              * ∫ α, (rest.map (fun r =>
                  r.2 (Erdos1002.gaussOrbit r.1 α))).prod
                    ∂Erdos1002.gaussMeasure := by
            rw [hintPb, hintΨ]
        _ ≤ (1 + 24 * (527 / 540 : ℝ) ^ M)
              * (∫ x, p.2 x ∂Erdos1002.gaussMeasure)
              * ((1 + 24 * (527 / 540 : ℝ) ^ M) ^ rest.length
                  * (rest.map (fun q =>
                      ∫ x, q.2 x ∂Erdos1002.gaussMeasure)).prod) :=
            mul_le_mul_of_nonneg_left hIH (mul_nonneg hC0 hintp0)
        _ = (1 + 24 * (527 / 540 : ℝ) ^ M) ^ (rest.length + 1)
              * ((∫ x, p.2 x ∂Erdos1002.gaussMeasure)
                  * (rest.map (fun q =>
                      ∫ x, q.2 x ∂Erdos1002.gaussMeasure)).prod) := by
            ring
        _ = (1 + 24 * (527 / 540 : ℝ) ^ M) ^ (p :: rest).length
              * ((p :: rest).map (fun q =>
                  ∫ x, q.2 x ∂Erdos1002.gaussMeasure)).prod := by
            simp [List.map_cons, List.prod_cons, List.length_cons]

end

end LargeDeviation

end Kwon1002
