import Kwon1002.SymbolIntensity
import Kwon1002.CompoundCauchy

/-!
# `hp1`: the one-level limit at the complex symbol
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Kwon1002

namespace SymbolLimit

noncomputable section

open LevyExponent TupleMeasure FactorialRoute

/-! ## The tuple bound with its constant exhibited -/

/-- `FactorialRoute.exists_tupleBigEvent_bound` with the `ε`-dependence of the
constant made explicit: one `C₀`, good for **every** truncation level. -/
theorem exists_tupleBigEvent_bound_uniform (c : ℝ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ,
      unifIoo.real (tupleBigEvent c ε n S) ≤ (C₀ / (8 * ε) / Lnorm n) ^ S.card := by
  classical
  obtain ⟨C₀, hC₀, hC⟩ := digit_tail_product
  refine ⟨C₀, hC₀, ?_⟩
  intro ε hε
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 8 * ε * Lnorm n := by
    have h : Tendsto (fun n : ℕ => 8 * ε * Lnorm n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) TupleMeasure.tendsto_Lnorm_atTop
    exact h.eventually_ge_atTop 1
  have h2 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < Lnorm n :=
    TupleMeasure.tendsto_Lnorm_atTop.eventually_gt_atTop 0
  have hB0 : ∀ x ∈ PoissonRoute.truncSet ε, ε ≤ |x| := fun _ hx => le_of_lt hx
  filter_upwards [h1, h2] with n hn1 hn2 S
  set k : ℕ := S.card with hk
  set js : Fin k → ℕ := fun i => S.orderEmbOfFin hk.symm i with hjs
  set big : Set ℝ := {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin k, (fun _ : Fin k => 8 * ε * Lnorm n) i ≤ (digit α (js i) : ℝ)} with hbig
  have hinj : Function.Injective js := (S.orderEmbOfFin hk.symm).injective
  have hbound : (volume big).toReal ≤ C₀ ^ k * ∏ _i : Fin k, (8 * ε * Lnorm n)⁻¹ :=
    hC k js (fun _ => 8 * ε * Lnorm n) hinj (fun _ => hn1)
  have hsub : tupleBigEvent c ε n S ∩ Ioo (0 : ℝ) 1 ⊆ big := by
    rintro α ⟨hα, hαI⟩
    refine ⟨hαI, fun i => ?_⟩
    have hmem : α ∈ bigEvent c ε n (js i) :=
      Set.mem_iInter₂.mp hα (js i) (S.orderEmbOfFin_mem hk.symm i)
    exact TupleMeasure.digit_ge_of_mem_bulkMarkEvent c (PoissonRoute.truncSet ε) hB0 hn2 hmem
  have hfin : volume big ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmeas : unifIoo.real (tupleBigEvent c ε n S) ≤ (volume big).toReal := by
    rw [Measure.real, unifIoo, Measure.restrict_apply' measurableSet_Ioo]
    exact ENNReal.toReal_mono hfin (measure_mono hsub)
  refine le_trans hmeas (le_trans hbound (le_of_eq ?_))
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow, div_div,
    ← div_eq_mul_inv]


/-! ## The mass bound at a truncation level, with an explicit constant -/

/-- The total large-jump mass at truncation level `ε`, bounded by `C₀/(2ε)`
eventually in `n` — the same estimate as `SymbolIntensity.sum_bigEvent_mass_le`
with the `ε`-dependence of the constant exhibited.  It is what makes the
`R → ∞` tail of `hp1` quantitative. -/
theorem eventually_sum_bigEvent_mass (c : ℝ) {C₀ : ℝ}
    (hb : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ,
      unifIoo.real (tupleBigEvent c ε n S) ≤ (C₀ / (8 * ε) / Lnorm n) ^ S.card)
    (hC₀ : 0 < C₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (∑ j ∈ Finset.range (n + 1), unifIoo.real (bigEvent c ε n j)) ≤ C₀ / (2 * ε) := by
  have hL3 : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ Lnorm n :=
    TupleMeasure.tendsto_Lnorm_atTop.eventually_ge_atTop 3
  filter_upwards [hb ε hε, hL3, eventually_ge_atTop 1] with n hn hL hn1
  have h := SymbolIntensity.sum_bigEvent_mass_le c ε (C := C₀ / (8 * ε))
    (by positivity) hn1 hL hn
  refine le_trans h (le_of_eq ?_)
  field_simp
  ring

/-! ## The complex symbol and its Lipschitz bound -/

/-- The symbol `x ↦ (e^{itx} − 1)·1{|x| > ε}` of `LayerAssembly.mu`. -/
def psi (t ε : ℝ) : ℝ → ℂ := fun x =>
  Set.indicator (PoissonRoute.truncSet ε)
    (fun y : ℝ => Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) - 1) x

lemma mu_eq_levelSymbol_psi (t c ε : ℝ) (n j : ℕ) :
    LayerAssembly.mu t c ε n j = SymbolIntensity.levelSymbol (psi t ε) c n j :=
  SymbolIntensity.mu_eq_levelSymbol t c ε n j

lemma measurable_psi (t ε : ℝ) : Measurable (psi t ε) := by
  refine Measurable.indicator ?_ (PoissonRoute.measurableSet_truncSet ε)
  exact (Complex.continuous_exp.comp
    (by continuity)).measurable.sub measurable_const

lemma norm_expSymbol_le (t x : ℝ) :
    ‖Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1‖ ≤ 2 := by
  have h1 : ‖Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)‖ = 1 := by
    have : (t : ℂ) * (x : ℂ) * Complex.I = ((t * x : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  calc ‖Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1‖
      ≤ ‖Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [h1]; norm_num

lemma norm_psi_le (t ε x : ℝ) : ‖psi t ε x‖ ≤ 2 := by
  unfold psi
  by_cases h : x ∈ PoissonRoute.truncSet ε
  · rw [Set.indicator_of_mem h]; exact norm_expSymbol_le t x
  · rw [Set.indicator_of_notMem h]; simp

/-- `x ↦ e^{itx} − 1` is `2|t|`-Lipschitz.  (The constant `2` comes from
`Complex.norm_exp_sub_one_le`; the bound is unconditional because for
`|t||x−y| > 1` the left side is at most `2` anyway.) -/
lemma norm_expSymbol_sub_le (t x y : ℝ) :
    ‖(Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
        - (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) - 1)‖ ≤ 2 * |t| * |x - y| := by
  have hxy : (t : ℂ) * (x : ℂ) * Complex.I
      = (t : ℂ) * (y : ℂ) * Complex.I + ((t * (x - y) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hone : ‖Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)‖ = 1 := by
    have h : (t : ℂ) * (y : ℂ) * Complex.I = ((t * y : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have hsub : (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
        - (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) - 1)
      = Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
          * (Complex.exp (((t * (x - y) : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [hxy, Complex.exp_add]; ring
  have hz : ‖((t * (x - y) : ℝ) : ℂ) * Complex.I‖ = |t| * |x - y| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  rw [hsub, norm_mul, hone, one_mul]
  by_cases hle : ‖((t * (x - y) : ℝ) : ℂ) * Complex.I‖ ≤ 1
  · refine le_trans (Complex.norm_exp_sub_one_le hle) (le_of_eq ?_)
    rw [hz]; ring
  · push_neg at hle
    rw [hz] at hle
    have h2 : ‖Complex.exp (((t * (x - y) : ℝ) : ℂ) * Complex.I) - 1‖ ≤ 2 := by
      have h1 : ‖Complex.exp (((t * (x - y) : ℝ) : ℂ) * Complex.I)‖ = 1 :=
        Complex.norm_exp_ofReal_mul_I _
      calc ‖Complex.exp (((t * (x - y) : ℝ) : ℂ) * Complex.I) - 1‖
          ≤ ‖Complex.exp (((t * (x - y) : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
        _ = 2 := by rw [h1]; norm_num
    nlinarith

/-! ## The step-symbol approximation of the complex symbol -/

/-- **The window approximation.**  For every truncation level `R > ε` and every
tolerance `η > 0` the symbol `x ↦ (e^{itx}−1)1{|x|>ε}` is within `η` of a step
symbol supported on the annulus `{ε < |x| ≤ R}` and built from the interval
class, the error off the annulus being at most `2` on `{|x| > R}` and `0` on
`{|x| ≤ ε}`.

The cells are the `Ioc` cells of a uniform grid of mesh `η/(2(|t|+1))` cut to
the annulus; each is a union of at most two intervals by
`IntervalClass.isUnionOfIntervals_truncation`, and the weight of a cell is the
symbol at its right endpoint, so the error inside a cell is at most `2|t|` times
the mesh by `norm_expSymbol_sub_le`. -/
theorem exists_step_approx (t : ℝ) {ε R η : ℝ} (_hε : 0 < ε) (_hεR : ε < R) (hη : 0 < η) :
    ∃ (M : ℕ) (w : Fin M → ℂ) (E : Fin M → Set ℝ),
      (∀ i, MeasurableSet (E i)) ∧
      (∀ i, E i ⊆ {x : ℝ | ε < |x| ∧ |x| ≤ R}) ∧
      (∀ i, IntervalClass.IsFiniteUnionOfIntervals (E i)) ∧
      (∀ x : ℝ, ‖psi t ε x - ∑ i, w i * Set.indicator (E i) (fun _ => (1 : ℂ)) x‖
          ≤ η * Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1 : ℝ)) x
            + 2 * Set.indicator (PoissonRoute.truncSet R) (fun _ => (1 : ℝ)) x) := by
  classical
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  set st : ℝ := η / (2 * (|t| + 1)) with hstdef
  have hs0 : 0 < st := by rw [hstdef]; positivity
  have hLip : 2 * |t| * st ≤ η := by
    rw [hstdef, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  set N : ℕ := ⌈R / st⌉₊ + 1 with hNdef
  have hRN : R ≤ (N : ℝ) * st := by
    have h1 : R / st ≤ (⌈R / st⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hs0] at h1
    have h2 : (⌈R / st⌉₊ : ℝ) ≤ (N : ℝ) := by rw [hNdef]; push_cast; linarith
    nlinarith
  set M : ℕ := 2 * N + 2 with hMdef
  set A : Set ℝ := {x : ℝ | ε < |x| ∧ |x| ≤ R} with hAdef
  have hAmeas : MeasurableSet A := by
    rw [hAdef]
    exact (PoissonRoute.measurableSet_truncSet ε).inter
      (measurableSet_le continuous_abs.measurable measurable_const)
  set lft : Fin M → ℝ := fun i => (((i : ℕ) : ℝ) - ((N : ℝ) + 1)) * st with hlftdef
  set rgt : Fin M → ℝ := fun i => (((i : ℕ) : ℝ) + 1 - ((N : ℝ) + 1)) * st with hrgtdef
  refine ⟨M, fun i => Complex.exp ((t : ℂ) * ((rgt i : ℝ) : ℂ) * Complex.I) - 1,
    fun i => Set.Ioc (lft i) (rgt i) ∩ A, fun i => measurableSet_Ioc.inter hAmeas,
    fun i x hx => hx.2, ?_, ?_⟩
  · intro i
    have h := (IntervalClass.isUnionOfIntervals_truncation ε R).inter
      (J := Set.Ioc (lft i) (rgt i)) ordConnected_Ioc
    rw [hAdef]
    exact h.finite
  · intro x
    have hnn : (0 : ℝ) ≤ η * Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1 : ℝ)) x
        + 2 * Set.indicator (PoissonRoute.truncSet R) (fun _ => (1 : ℝ)) x := by
      have h1 : (0 : ℝ) ≤ Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1 : ℝ)) x :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
      have h2 : (0 : ℝ) ≤ Set.indicator (PoissonRoute.truncSet R) (fun _ => (1 : ℝ)) x :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
      positivity
    by_cases hxA : x ∈ A
    · -- inside the annulus: exactly one cell contains `x`
      obtain ⟨hxε, hxR⟩ := hxA
      have hxεm : x ∈ PoissonRoute.truncSet ε := hxε
      have hxsub : ∀ b : Fin M, x ∈ Set.Ioc (lft b) (rgt b) ∩ A →
          ((b : ℕ) : ℤ) = ⌈x / st⌉ + (N : ℤ) := by
        intro b hb
        obtain ⟨hb1, hb2⟩ := hb.1
        have h1 : ((((b : ℕ) : ℤ) - (N : ℤ) : ℤ) : ℝ) - 1 < x / st := by
          rw [lt_div_iff₀ hs0]
          push_cast
          rw [hlftdef] at hb1
          simp only at hb1
          linarith
        have h2 : x / st ≤ ((((b : ℕ) : ℤ) - (N : ℤ) : ℤ) : ℝ) := by
          rw [div_le_iff₀ hs0]
          push_cast
          rw [hrgtdef] at hb2
          simp only at hb2
          linarith
        have := Int.ceil_eq_iff.mpr ⟨h1, h2⟩
        omega
      have hceil_lb : -(N : ℤ) ≤ ⌈x / st⌉ := by
        have hxge : -R ≤ x := neg_le_of_abs_le hxR
        have hxdiv : -((N : ℝ)) ≤ x / st := by
          rw [le_div_iff₀ hs0]
          nlinarith
        have hlt : ((-(N : ℤ) - 1 : ℤ) : ℝ) < x / st := by push_cast; linarith
        have := Int.lt_ceil.mpr hlt
        omega
      have hceil_ub : ⌈x / st⌉ ≤ (N : ℤ) := by
        have hxle : x ≤ R := le_of_abs_le hxR
        have hxdiv : x / st ≤ (N : ℝ) := by
          rw [div_le_iff₀ hs0]; nlinarith
        exact Int.ceil_le.mpr (by push_cast; exact hxdiv)
      have hlt : (⌈x / st⌉ + (N : ℤ)).toNat < M := by rw [hMdef]; omega
      set i0 : Fin M := ⟨(⌈x / st⌉ + (N : ℤ)).toNat, hlt⟩ with hi0def
      have hi0val : ((i0 : ℕ) : ℤ) = ⌈x / st⌉ + (N : ℤ) := by
        rw [hi0def]
        simp only
        omega
      have hi0R : ((i0 : ℕ) : ℝ) = (⌈x / st⌉ : ℝ) + (N : ℝ) := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hi0val
        push_cast at this
        exact this
      have hrgt0 : rgt i0 = (⌈x / st⌉ : ℝ) * st := by
        rw [hrgtdef]; simp only [hi0R]; ring
      have hlft0 : lft i0 = ((⌈x / st⌉ : ℝ) - 1) * st := by
        rw [hlftdef]; simp only [hi0R]; ring
      have hmem0 : x ∈ Set.Ioc (lft i0) (rgt i0) ∩ A := by
        refine ⟨⟨?_, ?_⟩, hxε, hxR⟩
        · rw [hlft0]
          have h : (⌈x / st⌉ : ℝ) - 1 < x / st := by
            have := Int.ceil_lt_add_one (x / st); linarith
          calc ((⌈x / st⌉ : ℝ) - 1) * st < (x / st) * st :=
                mul_lt_mul_of_pos_right h hs0
            _ = x := by field_simp
        · rw [hrgt0]
          have h : x / st ≤ (⌈x / st⌉ : ℝ) := Int.le_ceil _
          calc x = (x / st) * st := by field_simp
            _ ≤ (⌈x / st⌉ : ℝ) * st := mul_le_mul_of_nonneg_right h hs0.le
      have hsum : (∑ i, (Complex.exp ((t : ℂ) * ((rgt i : ℝ) : ℂ) * Complex.I) - 1)
            * Set.indicator (Set.Ioc (lft i) (rgt i) ∩ A) (fun _ => (1 : ℂ)) x)
          = Complex.exp ((t : ℂ) * ((rgt i0 : ℝ) : ℂ) * Complex.I) - 1 := by
        rw [Finset.sum_eq_single i0]
        · rw [Set.indicator_of_mem hmem0, mul_one]
        · intro b _ hb
          have hnot : x ∉ Set.Ioc (lft b) (rgt b) ∩ A := by
            intro hmem
            have h1 := hxsub b hmem
            have : (b : ℕ) = (i0 : ℕ) := by omega
            exact hb (Fin.ext this)
          rw [Set.indicator_of_notMem hnot, mul_zero]
        · intro hb; exact absurd (Finset.mem_univ i0) hb
      have hpsi : psi t ε x = Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1 := by
        rw [psi, Set.indicator_of_mem hxεm]
      have hdist : |x - rgt i0| ≤ st := by
        have h1 := hmem0.1.1
        have h2 := hmem0.1.2
        have hwidth : rgt i0 - lft i0 = st := by rw [hrgt0, hlft0]; ring
        rw [abs_le]; constructor <;> linarith
      have hbnd : ‖psi t ε x
          - (Complex.exp ((t : ℂ) * ((rgt i0 : ℝ) : ℂ) * Complex.I) - 1)‖ ≤ η := by
        rw [hpsi]
        refine le_trans (norm_expSymbol_sub_le t x (rgt i0)) ?_
        calc 2 * |t| * |x - rgt i0| ≤ 2 * |t| * st := by
              exact mul_le_mul_of_nonneg_left hdist (by positivity)
          _ ≤ η := hLip
      rw [hsum]
      refine le_trans hbnd ?_
      have h1 : Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1 : ℝ)) x = 1 :=
        Set.indicator_of_mem hxεm _
      have h2 : (0 : ℝ) ≤ Set.indicator (PoissonRoute.truncSet R) (fun _ => (1 : ℝ)) x :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
      rw [h1, mul_one]
      linarith
    · -- outside the annulus: every cell misses `x`
      have hsum : (∑ i, (Complex.exp ((t : ℂ) * ((rgt i : ℝ) : ℂ) * Complex.I) - 1)
            * Set.indicator (Set.Ioc (lft i) (rgt i) ∩ A) (fun _ => (1 : ℂ)) x) = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        rw [Set.indicator_of_notMem (fun hmem => hxA hmem.2), mul_zero]
      rw [hsum, sub_zero]
      by_cases hxε : x ∈ PoissonRoute.truncSet ε
      · -- `|x| > ε` but not in the annulus, so `|x| > R`
        have hxR : x ∈ PoissonRoute.truncSet R := by
          rw [PoissonRoute.truncSet, Set.mem_setOf_eq]
          by_contra hc
          push_neg at hc
          exact hxA ⟨hxε, hc⟩
        have h1 : Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1 : ℝ)) x = 1 :=
          Set.indicator_of_mem hxε _
        have h2 : Set.indicator (PoissonRoute.truncSet R) (fun _ => (1 : ℝ)) x = 1 :=
          Set.indicator_of_mem hxR _
        rw [h1, h2, mul_one, mul_one]
        have := norm_psi_le t ε x
        linarith
      · rw [psi, Set.indicator_of_notMem hxε, norm_zero]
        exact hnn

/-! ## Transferring the pointwise error to the level sums -/

lemma setIntegral_indicator_unifIoo {S : Set ℝ} (hS : MeasurableSet S) :
    (∫ α in Ioo (0:ℝ) 1, Set.indicator S (fun _ => (1:ℝ)) α) = unifIoo.real S := by
  rw [setIntegral_indicator hS, setIntegral_const, smul_eq_mul, mul_one]
  simp [Measure.real, unifIoo, Measure.restrict_apply hS, Set.inter_comm]

lemma integrableOn_indicator_unifIoo {S : Set ℝ} (hS : MeasurableSet S) :
    IntegrableOn (fun α : ℝ => Set.indicator S (fun _ => (1:ℝ)) α) (Ioo (0:ℝ) 1) volume :=
  (integrable_const (1:ℝ)).indicator hS

/-- The level-`j` integrand of a bounded measurable symbol is integrable on the
unit interval. -/
lemma integrableOn_levelIntegrand (c : ℝ) {f : ℝ → ℂ} (hf : Measurable f) {K : ℝ}
    (hfb : ∀ x, ‖f x‖ ≤ K) (n j : ℕ) :
    IntegrableOn (fun α : ℝ => Set.indicator {β : ℝ | j ∈ bulkIndices c β n}
        (fun β => f (signedMark β n j)) α) (Ioo (0:ℝ) 1) volume := by
  have hmeas : Measurable (fun α : ℝ => Set.indicator {β : ℝ | j ∈ bulkIndices c β n}
      (fun β => f (signedMark β n j)) α) :=
    Measurable.indicator (hf.comp (measurable_signedMark n j))
      (measurableSet_mem_bulkIndices c n j)
  refine Measure.integrableOn_of_bounded (M := K) (by simp [Real.volume_Ioo])
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun α => ?_)
  rw [Set.indicator_apply]
  split_ifs with h
  · exact hfb _
  · rw [norm_zero]
    exact le_trans (norm_nonneg (f 0)) (hfb 0)

/-- **The approximation error at one level.**  A pointwise error bound on the
symbol, of the shape `exists_step_approx` produces, is paid at level `j` by the
window mass at `ε` and the tail mass at `R`. -/
theorem norm_levelSymbol_sub_le (c t : ℝ) {ε R η : ℝ} {M : ℕ} (w : Fin M → ℂ)
    (E : Fin M → Set ℝ) (hEm : ∀ i, MeasurableSet (E i))
    (hpt : ∀ x : ℝ, ‖psi t ε x - ∑ i, w i * Set.indicator (E i) (fun _ => (1 : ℂ)) x‖
        ≤ η * Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1 : ℝ)) x
          + 2 * Set.indicator (PoissonRoute.truncSet R) (fun _ => (1 : ℝ)) x)
    (n j : ℕ) :
    ‖SymbolIntensity.levelSymbol (psi t ε) c n j
        - SymbolIntensity.levelSymbol
            (fun x => ∑ i, w i * Set.indicator (E i) (fun _ => (1 : ℂ)) x) c n j‖
      ≤ η * unifIoo.real (bigEvent c ε n j) + 2 * unifIoo.real (bigEvent c R n j) := by
  classical
  set σ : ℝ → ℂ := fun x => ∑ i, w i * Set.indicator (E i) (fun _ => (1 : ℂ)) x with hσ
  have hσm : Measurable σ := by
    rw [hσ]
    exact Finset.univ.measurable_sum (fun i _ =>
      measurable_const.mul ((measurable_const : Measurable (fun _ : ℝ => (1:ℂ))).indicator (hEm i)))
  have hσb : ∀ x, ‖σ x‖ ≤ ∑ i, ‖w i‖ := by
    intro x
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_mul]
    have : ‖Set.indicator (E i) (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
      rw [Set.indicator_apply]; split_ifs <;> simp
    nlinarith [norm_nonneg (w i), norm_nonneg (Set.indicator (E i) (fun _ => (1 : ℂ)) x)]
  have hI1 := integrableOn_levelIntegrand c (measurable_psi t ε) (norm_psi_le t ε) n j
  have hI2 := integrableOn_levelIntegrand c hσm hσb n j
  have hdiff : SymbolIntensity.levelSymbol (psi t ε) c n j
      - SymbolIntensity.levelSymbol σ c n j
      = ∫ α in Ioo (0:ℝ) 1, (Set.indicator {β : ℝ | j ∈ bulkIndices c β n}
            (fun β => psi t ε (signedMark β n j)) α
          - Set.indicator {β : ℝ | j ∈ bulkIndices c β n}
            (fun β => σ (signedMark β n j)) α) := by
    rw [SymbolIntensity.levelSymbol, SymbolIntensity.levelSymbol, ← integral_sub hI1 hI2]
  set G : ℝ → ℝ := fun α =>
    η * Set.indicator (bigEvent c ε n j) (fun _ => (1:ℝ)) α
      + 2 * Set.indicator (bigEvent c R n j) (fun _ => (1:ℝ)) α with hG
  have hGint : IntegrableOn G (Ioo (0:ℝ) 1) volume := by
    rw [hG]
    exact ((integrableOn_indicator_unifIoo (measurableSet_bigEvent c ε n j)).const_mul η).add
      ((integrableOn_indicator_unifIoo (measurableSet_bigEvent c R n j)).const_mul 2)
  have hptG : ∀ α : ℝ, ‖Set.indicator {β : ℝ | j ∈ bulkIndices c β n}
        (fun β => psi t ε (signedMark β n j)) α
      - Set.indicator {β : ℝ | j ∈ bulkIndices c β n}
        (fun β => σ (signedMark β n j)) α‖ ≤ G α := by
    intro α
    by_cases hb : α ∈ {β : ℝ | j ∈ bulkIndices c β n}
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]
      refine le_trans (hpt (signedMark α n j)) (le_of_eq ?_)
      rw [hG]
      congr 1
      · congr 1
        by_cases hs : signedMark α n j ∈ PoissonRoute.truncSet ε
        · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show α ∈ bigEvent c ε n j from ⟨hb, hs⟩)]
        · rw [Set.indicator_of_notMem hs,
            Set.indicator_of_notMem (show α ∉ bigEvent c ε n j from fun h => hs h.2)]
      · congr 1
        by_cases hs : signedMark α n j ∈ PoissonRoute.truncSet R
        · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show α ∈ bigEvent c R n j from ⟨hb, hs⟩)]
        · rw [Set.indicator_of_notMem hs,
            Set.indicator_of_notMem (show α ∉ bigEvent c R n j from fun h => hs h.2)]
    · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb, sub_zero, norm_zero]
      have h1 : Set.indicator (bigEvent c ε n j) (fun _ => (1:ℝ)) α = 0 :=
        Set.indicator_of_notMem (fun h => hb h.1) _
      have h2 : Set.indicator (bigEvent c R n j) (fun _ => (1:ℝ)) α = 0 :=
        Set.indicator_of_notMem (fun h => hb h.1) _
      simp only [hG, h1, h2]
      norm_num
  rw [hdiff]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hmono : (∫ α in Ioo (0:ℝ) 1, ‖Set.indicator {β : ℝ | j ∈ bulkIndices c β n}
        (fun β => psi t ε (signedMark β n j)) α
      - Set.indicator {β : ℝ | j ∈ bulkIndices c β n}
        (fun β => σ (signedMark β n j)) α‖)
      ≤ ∫ α in Ioo (0:ℝ) 1, G α :=
    integral_mono (hI1.sub hI2).norm hGint hptG
  refine le_trans hmono (le_of_eq ?_)
  rw [hG]
  rw [integral_add ((integrableOn_indicator_unifIoo (measurableSet_bigEvent c ε n j)).const_mul η)
      ((integrableOn_indicator_unifIoo (measurableSet_bigEvent c R n j)).const_mul 2),
    integral_const_mul, integral_const_mul,
    setIntegral_indicator_unifIoo (measurableSet_bigEvent c ε n j),
    setIntegral_indicator_unifIoo (measurableSet_bigEvent c R n j)]

/-! ## The Lévy side: the step symbol against the intensity -/

open CompoundCauchy in
/-- Off a neighbourhood of the origin the Lévy intensity of a set is the
integral of its density. -/
lemma levyIntensity_toReal_eq_setIntegral {ε : ℝ} (hε : 0 < ε) {S : Set ℝ}
    (hS : MeasurableSet S) (hsub : S ⊆ {x : ℝ | ε < |x|}) :
    (levyIntensity S).toReal = ∫ x in S, levyIntensityDensity x := by
  have hint : IntegrableOn levyIntensityDensity S volume :=
    (integrableOn_levyIntensityDensity_trunc hε).mono_set hsub
  rw [levyIntensity, withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => levyIntensityDensity_nonneg x),
    ENNReal.toReal_ofReal (integral_nonneg fun x => levyIntensityDensity_nonneg x)]

open CompoundCauchy in
/-- The step symbol integrates against `Λ` to the weighted sum of the masses of
its cells — the limit `SymbolIntensity.sum_levelSymbol_step_tendsto` produces. -/
lemma setIntegral_step_mul_density {ε : ℝ} (hε : 0 < ε) {M : ℕ} (w : Fin M → ℂ)
    (E : Fin M → Set ℝ) (hEm : ∀ i, MeasurableSet (E i))
    (hEsub : ∀ i, E i ⊆ {x : ℝ | ε < |x|}) :
    (∫ x in {x : ℝ | ε < |x|},
        (∑ i, w i * Set.indicator (E i) (fun _ => (1 : ℂ)) x)
          * (levyIntensityDensity x : ℂ))
      = ∑ i, w i * (((levyIntensity (E i)).toReal : ℝ) : ℂ) := by
  classical
  set T : Set ℝ := {x : ℝ | ε < |x|} with hT
  have hTm : MeasurableSet T := CompoundCauchy.measurableSet_trunc ε
  have hdint : IntegrableOn (fun x : ℝ => ((levyIntensityDensity x : ℝ) : ℂ)) T volume := by
    exact (integrableOn_levyIntensityDensity_trunc hε).ofReal
  have hcongr : ∀ x : ℝ, (∑ i, w i * Set.indicator (E i) (fun _ => (1 : ℂ)) x)
        * (levyIntensityDensity x : ℂ)
      = ∑ i, w i * Set.indicator (E i) (fun y : ℝ => ((levyIntensityDensity y : ℝ) : ℂ)) x := by
    intro x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : x ∈ E i
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring
  rw [setIntegral_congr_fun hTm (fun x _ => hcongr x)]
  rw [integral_finset_sum _ (fun i _ => (hdint.indicator (hEm i)).const_mul _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul, setIntegral_indicator (hEm i),
    Set.inter_eq_self_of_subset_right (hEsub i), integral_complex_ofReal,
    levyIntensity_toReal_eq_setIntegral hε (hEm i) (hEsub i)]

open CompoundCauchy in
/-- The truncation set splits into the window and its tail. -/
lemma integral_far_density {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    (∫ x in {x : ℝ | R < |x|}, levyIntensityDensity x)
      = (∫ x in {x : ℝ | ε < |x|}, levyIntensityDensity x)
        - ∫ x in {x : ℝ | ε < |x| ∧ |x| ≤ R}, levyIntensityDensity x := by
  have hAm : MeasurableSet {x : ℝ | ε < |x| ∧ |x| ≤ R} :=
    (measurableSet_trunc ε).inter
      (measurableSet_le continuous_abs.measurable measurable_const)
  have hFm : MeasurableSet {x : ℝ | R < |x|} := measurableSet_trunc R
  have hsplit : {x : ℝ | ε < |x|}
      = {x : ℝ | ε < |x| ∧ |x| ≤ R} ∪ {x : ℝ | R < |x|} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hx
      rcases le_or_gt |x| R with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (⟨hx, -⟩ | hx)
      · exact hx
      · linarith
  have hdisj : Disjoint {x : ℝ | ε < |x| ∧ |x| ≤ R} {x : ℝ | R < |x|} := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx2⟩ hx3
    exact absurd hx3 (not_lt.mpr hx2)
  have hint := integrableOn_levyIntensityDensity_trunc hε
  have h1 : IntegrableOn levyIntensityDensity {x : ℝ | ε < |x| ∧ |x| ≤ R} volume :=
    hint.mono_set (fun x hx => hx.1)
  have h2 : IntegrableOn levyIntensityDensity {x : ℝ | R < |x|} volume :=
    hint.mono_set (fun x hx => lt_of_le_of_lt hεR hx)
  rw [hsplit, setIntegral_union hdisj hFm h1 h2]
  ring

open CompoundCauchy in
/-- The tail mass of `Λ` vanishes as the truncation level grows. -/
lemma tendsto_integral_far_density {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m : ℕ => ∫ x in {x : ℝ | ε + m < |x|}, levyIntensityDensity x)
      atTop (𝓝 0) := by
  set s : ℕ → Set ℝ := fun m => {x : ℝ | ε < |x| ∧ |x| ≤ ε + m} with hs
  have hsm : ∀ m, MeasurableSet (s m) := fun m =>
    (measurableSet_trunc ε).inter
      (measurableSet_le continuous_abs.measurable measurable_const)
  have hmono : Monotone s := by
    intro a b hab x hx
    refine ⟨hx.1, le_trans hx.2 ?_⟩
    have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
    linarith
  have hunion : (⋃ m, s m) = {x : ℝ | ε < |x|} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, hs]
    constructor
    · rintro ⟨m, hm, -⟩; exact hm
    · intro hx
      obtain ⟨m, hm⟩ := exists_nat_ge (|x| - ε)
      exact ⟨m, hx, by linarith⟩
  have hint : IntegrableOn levyIntensityDensity (⋃ m, s m) volume := by
    rw [hunion]; exact integrableOn_levyIntensityDensity_trunc hε
  have h := tendsto_setIntegral_of_monotone hsm hmono hint
  rw [hunion] at h
  have heq : ∀ m : ℕ, (∫ x in {x : ℝ | ε + m < |x|}, levyIntensityDensity x)
      = (∫ x in {x : ℝ | ε < |x|}, levyIntensityDensity x) - ∫ x in s m, levyIntensityDensity x := by
    intro m
    have hεm : ε ≤ ε + m := by
      have h0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      linarith
    exact integral_far_density hε hεm
  refine Filter.Tendsto.congr (fun m => (heq m).symm) ?_
  have := (tendsto_const_nhds (x := (∫ x in {x : ℝ | ε < |x|}, levyIntensityDensity x))
    (f := (atTop : Filter ℕ))).sub h
  simpa using this

open CompoundCauchy in
/-- **The approximation error on the Lévy side.**  The same pointwise error
bound is paid against `Λ` by the total window mass and the tail mass. -/
theorem norm_step_levy_sub_le (t : ℝ) {ε R η : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) {M : ℕ}
    (w : Fin M → ℂ) (E : Fin M → Set ℝ) (hEm : ∀ i, MeasurableSet (E i))
    (hEsub : ∀ i, E i ⊆ {x : ℝ | ε < |x|}) (hη : 0 ≤ η)
    (hpt : ∀ x : ℝ, ‖psi t ε x - ∑ i, w i * Set.indicator (E i) (fun _ => (1 : ℂ)) x‖
        ≤ η * Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1 : ℝ)) x
          + 2 * Set.indicator (PoissonRoute.truncSet R) (fun _ => (1 : ℝ)) x) :
    ‖(∑ i, w i * (((levyIntensity (E i)).toReal : ℝ) : ℂ))
        - ∫ x in {x : ℝ | ε < |x|},
            (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
              * (levyIntensityDensity x : ℂ)‖
      ≤ η * (∫ x in {x : ℝ | ε < |x|}, levyIntensityDensity x)
        + 2 * (∫ x in {x : ℝ | R < |x|}, levyIntensityDensity x) := by
  classical
  have hpsiT : (∫ x in {x : ℝ | ε < |x|},
        (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1) * (levyIntensityDensity x : ℂ))
      = ∫ x in {x : ℝ | ε < |x|}, psi t ε x * (levyIntensityDensity x : ℂ) := by
    refine setIntegral_congr_fun (measurableSet_trunc ε) (fun x hx => ?_)
    rw [psi, Set.indicator_of_mem (show x ∈ PoissonRoute.truncSet ε from hx)]
  rw [hpsiT, ← setIntegral_step_mul_density hε w E hEm hEsub]
  set T : Set ℝ := {x : ℝ | ε < |x|} with hT
  set F : Set ℝ := {x : ℝ | R < |x|} with hF
  have hTm : MeasurableSet T := measurableSet_trunc ε
  have hFm : MeasurableSet F := measurableSet_trunc R
  have hFT : F ⊆ T := fun x hx => lt_of_le_of_lt hεR hx
  have hdens : IntegrableOn levyIntensityDensity T volume :=
    integrableOn_levyIntensityDensity_trunc hε
  set σ : ℝ → ℂ := fun x => ∑ i, w i * Set.indicator (E i) (fun _ => (1 : ℂ)) x with hσ
  -- the dominating function
  set g : ℝ → ℝ := fun x =>
    η * levyIntensityDensity x
      + 2 * Set.indicator F (fun y => levyIntensityDensity y) x with hg
  have hgint : IntegrableOn g T volume := by
    rw [hg]
    exact (hdens.const_mul η).add
      (((hdens.indicator hFm)).const_mul 2)
  have hfint : IntegrableOn (fun x => σ x * (levyIntensityDensity x : ℂ)
      - psi t ε x * (levyIntensityDensity x : ℂ)) T volume := by
    refine Integrable.mono' (hgint.const_mul 1 |>.congr (Filter.Eventually.of_forall
        (fun x => one_mul (g x)))) ?_ ?_
    · have hσm : Measurable σ := by
        rw [hσ]
        exact Finset.univ.measurable_sum (fun i _ =>
          measurable_const.mul
            ((measurable_const : Measurable (fun _ : ℝ => (1:ℂ))).indicator (hEm i)))
      have md : Measurable (fun x : ℝ => ((levyIntensityDensity x : ℝ) : ℂ)) :=
        Complex.measurable_ofReal.comp measurable_levyIntensityDensity
      exact ((hσm.mul md).sub
        ((measurable_psi t ε).mul md)).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem hTm] with x hx
      rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (levyIntensityDensity_nonneg x)]
      have h1 : ‖σ x - psi t ε x‖ ≤ η + 2 * Set.indicator F (fun _ => (1:ℝ)) x := by
        rw [← norm_neg]
        have := hpt x
        have he : Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1 : ℝ)) x = 1 :=
          Set.indicator_of_mem (show x ∈ PoissonRoute.truncSet ε from hx) _
        rw [he, mul_one] at this
        have hFeq : Set.indicator (PoissonRoute.truncSet R) (fun _ => (1 : ℝ)) x
            = Set.indicator F (fun _ => (1:ℝ)) x := rfl
        rw [hFeq] at this
        simpa using this
      have hd : 0 ≤ levyIntensityDensity x := levyIntensityDensity_nonneg x
      have hgx : g x = (η + 2 * Set.indicator F (fun _ => (1:ℝ)) x) * levyIntensityDensity x := by
        simp only [hg]
        by_cases hxF : x ∈ F
        · rw [Set.indicator_of_mem hxF, Set.indicator_of_mem hxF]; ring
        · rw [Set.indicator_of_notMem hxF, Set.indicator_of_notMem hxF]; ring
      rw [hgx]
      exact mul_le_mul_of_nonneg_right h1 hd
  have hsub : (∫ x in T, σ x * (levyIntensityDensity x : ℂ))
      - ∫ x in T, psi t ε x * (levyIntensityDensity x : ℂ)
      = ∫ x in T, (σ x * (levyIntensityDensity x : ℂ)
          - psi t ε x * (levyIntensityDensity x : ℂ)) := by
    have hI1 : IntegrableOn (fun x => psi t ε x * (levyIntensityDensity x : ℂ)) T volume := by
      refine Integrable.mono' (hdens.const_mul 2) ?_ ?_
      · exact ((measurable_psi t ε).mul (Complex.measurable_ofReal.comp
          measurable_levyIntensityDensity)).aestronglyMeasurable.restrict
      · filter_upwards with x
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (levyIntensityDensity_nonneg x)]
        exact mul_le_mul_of_nonneg_right (norm_psi_le t ε x) (levyIntensityDensity_nonneg x)
    have hI2 : IntegrableOn (fun x => σ x * (levyIntensityDensity x : ℂ)) T volume := by
      have hadd := hfint.add hI1
      exact hadd.congr (Filter.Eventually.of_forall
        (fun x => by simp only [Pi.add_apply]; ring))
    exact (integral_sub hI2 hI1).symm
  rw [hsub]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hmono : (∫ x in T, ‖σ x * (levyIntensityDensity x : ℂ)
      - psi t ε x * (levyIntensityDensity x : ℂ)‖) ≤ ∫ x in T, g x := by
    refine integral_mono hfint.norm hgint ?_
    intro x
    show ‖σ x * (levyIntensityDensity x : ℂ) - psi t ε x * (levyIntensityDensity x : ℂ)‖ ≤ g x
    by_cases hx : x ∈ T
    · rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (levyIntensityDensity_nonneg x)]
      have h1 : ‖σ x - psi t ε x‖ ≤ η + 2 * Set.indicator F (fun _ => (1:ℝ)) x := by
        rw [← norm_neg]
        have hh := hpt x
        have he : Set.indicator (PoissonRoute.truncSet ε) (fun _ => (1 : ℝ)) x = 1 :=
          Set.indicator_of_mem (show x ∈ PoissonRoute.truncSet ε from hx) _
        rw [he, mul_one] at hh
        simpa using hh
      have hgx : g x = (η + 2 * Set.indicator F (fun _ => (1:ℝ)) x) * levyIntensityDensity x := by
        simp only [hg]
        by_cases hxF : x ∈ F
        · rw [Set.indicator_of_mem hxF, Set.indicator_of_mem hxF]; ring
        · rw [Set.indicator_of_notMem hxF, Set.indicator_of_notMem hxF]; ring
      rw [hgx]
      exact mul_le_mul_of_nonneg_right h1 (levyIntensityDensity_nonneg x)
    · have h0 : σ x = 0 := by
        rw [hσ]
        refine Finset.sum_eq_zero (fun i _ => ?_)
        rw [Set.indicator_of_notMem (fun hmem => hx (hEsub i hmem)), mul_zero]
      have hp0 : psi t ε x = 0 := by
        rw [psi, Set.indicator_of_notMem (show x ∉ PoissonRoute.truncSet ε from hx)]
      have hd : 0 ≤ levyIntensityDensity x := levyIntensityDensity_nonneg x
      have h2 : (0:ℝ) ≤ Set.indicator F (fun y => levyIntensityDensity y) x :=
        Set.indicator_nonneg (fun y _ => levyIntensityDensity_nonneg y) x
      have h3 : (0:ℝ) ≤ η * levyIntensityDensity x := mul_nonneg hη hd
      simp only [h0, hp0, zero_mul, sub_zero, norm_zero, hg]
      linarith
  refine le_trans hmono (le_of_eq ?_)
  rw [hg, integral_add (hdens.const_mul η) ((hdens.indicator hFm).const_mul 2),
    integral_const_mul, integral_const_mul, setIntegral_indicator hFm,
    Set.inter_eq_self_of_subset_right hFT]

/-! ## `hp1`, the one-level limit at the complex symbol -/

open CompoundCauchy in
/-- **`hp1`.**  The one-level sums of the complex symbol `x ↦ (e^{itx}−1)1{|x|>ε}`
converge to the compound-Poisson exponent

  `∑_{j ≤ n} ∫₀¹ h_j  →  ∫_{|x|>ε} (e^{itx} − 1) dΛ(x)`.

Proved by an `ε/3` between three estimates, none of which needs a further §4
input:

* `SymbolIntensity.sum_levelSymbol_step_tendsto`, the limit at a step symbol from
  the interval class (this is the §4-dependent half, already unconditional);
* `exists_step_approx` together with `norm_levelSymbol_sub_le` and
  `SymbolIntensity.sum_bigEvent_mass_le`, the window approximation, whose cost is
  the tolerance times the uniformly bounded total window mass;
* `eventually_sum_bigEvent_mass` and `tendsto_integral_far_density`, the two
  `R → ∞` tails, one on the random side with the explicit constant `C₀/(2R)` of
  `exists_tupleBigEvent_bound_uniform`, one on the Lévy side. -/
theorem sum_mu_tendsto (c : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), LayerAssembly.mu t c ε n j) atTop
      (𝓝 (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ))) := by
  classical
  obtain ⟨C₀, hC₀, hbnd⟩ := exists_tupleBigEvent_bound_uniform c
  set Lam : ℝ := ∫ x in {x : ℝ | ε < |x|}, levyIntensityDensity x with hLam
  have hLam0 : 0 ≤ Lam := integral_nonneg fun x => levyIntensityDensity_nonneg x
  have hmu : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1), LayerAssembly.mu t c ε n j)
      = ∑ j ∈ Finset.range (n + 1), SymbolIntensity.levelSymbol (psi t ε) c n j := by
    intro n
    exact Finset.sum_congr rfl (fun j _ => mu_eq_levelSymbol_psi t c ε n j)
  refine Filter.Tendsto.congr (fun n => (hmu n).symm) ?_
  refine Metric.tendsto_atTop.mpr (fun γ hγ => ?_)
  -- choose the truncation level `R = ε + m`
  have hfar : ∀ᶠ m : ℕ in atTop,
      2 * (∫ x in {x : ℝ | ε + m < |x|}, levyIntensityDensity x) ≤ γ / 6 := by
    have h := (tendsto_integral_far_density hε).const_mul (2 : ℝ)
    rw [mul_zero] at h
    exact h.eventually_le_const (by linarith)
  have hCR : ∀ᶠ m : ℕ in atTop, C₀ / (ε + m) ≤ γ / 6 := by
    have hdiv : Tendsto (fun m : ℕ => C₀ / (ε + m)) atTop (𝓝 0) := by
      refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
      exact Filter.tendsto_atTop_add_const_left _ ε tendsto_natCast_atTop_atTop
    exact hdiv.eventually_le_const (by linarith)
  obtain ⟨m, ⟨hm1, hm2⟩, hm3⟩ := ((hfar.and hCR).and (eventually_ge_atTop 1)).exists
  set R : ℝ := ε + m with hR
  have hεR : ε < R := by
    rw [hR]
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
    linarith
  have hR0 : 0 < R := lt_trans hε hεR
  -- choose the tolerance
  set D : ℝ := 4 * (C₀ / (8 * ε)) + Lam + 1 with hD
  have hD0 : 0 < D := by rw [hD]; have : 0 < C₀ / (8 * ε) := by positivity
                         linarith
  set η : ℝ := (γ / 6) / D with hη
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηmass : η * (4 * (C₀ / (8 * ε))) ≤ γ / 6 := by
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ hD0]
    have h1 : 4 * (C₀ / (8 * ε)) ≤ D := by rw [hD]; linarith
    nlinarith [le_of_lt hγ, div_nonneg (le_of_lt hγ) (by norm_num : (0:ℝ) ≤ 6)]
  have hηLam : η * Lam ≤ γ / 6 := by
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ hD0]
    have h1 : Lam ≤ D := by rw [hD]; have : 0 < C₀ / (8 * ε) := by positivity
                            linarith
    nlinarith [div_nonneg (le_of_lt hγ) (by norm_num : (0:ℝ) ≤ 6)]
  -- the step symbol
  obtain ⟨M, w, E, hEm, hEsub, hEi, hpt⟩ := exists_step_approx t hε hεR hη0
  have hE0 : ∀ i, ∃ δ > 0, ∀ x ∈ E i, δ ≤ |x| :=
    fun i => ⟨ε, hε, fun x hx => le_of_lt (hEsub i hx).1⟩
  have hEb : ∀ i, ∃ S : ℝ, ∀ x ∈ E i, |x| ≤ S := fun i => ⟨R, fun x hx => (hEsub i hx).2⟩
  have hEsubT : ∀ i, E i ⊆ {x : ℝ | ε < |x|} := fun i x hx => (hEsub i hx).1
  -- the Lévy side
  have hlevy : ‖(∑ i, w i * (((levyIntensity (E i)).toReal : ℝ) : ℂ))
      - ∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ)‖ ≤ γ / 6 + γ / 6 := by
    refine le_trans (norm_step_levy_sub_le t hε (le_of_lt hεR) w E hEm hEsubT hη0.le hpt) ?_
    have h1 : η * Lam ≤ γ / 6 := hηLam
    have h2 : 2 * (∫ x in {x : ℝ | R < |x|}, levyIntensityDensity x) ≤ γ / 6 := hm1
    linarith
  -- the level-sum error
  have hsumerr : ∀ n : ℕ, ‖(∑ j ∈ Finset.range (n + 1),
        SymbolIntensity.levelSymbol (psi t ε) c n j)
      - ∑ j ∈ Finset.range (n + 1), SymbolIntensity.levelSymbol
          (fun x => ∑ i, w i * Set.indicator (E i) (fun _ => (1 : ℂ)) x) c n j‖
      ≤ η * (∑ j ∈ Finset.range (n + 1), unifIoo.real (bigEvent c ε n j))
        + 2 * (∑ j ∈ Finset.range (n + 1), unifIoo.real (bigEvent c R n j)) := by
    intro n
    rw [← Finset.sum_sub_distrib]
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => norm_levelSymbol_sub_le c t w E hEm hpt n j)
  -- the three eventual facts
  have hstep := SymbolIntensity.sum_levelSymbol_step_tendsto c w E hEm hE0 hEb hEi
  have hev1 : ∀ᶠ n : ℕ in atTop, ‖(∑ j ∈ Finset.range (n + 1),
      SymbolIntensity.levelSymbol
        (fun x => ∑ i, w i * Set.indicator (E i) (fun _ => (1 : ℂ)) x) c n j)
      - ∑ i, w i * (((levyIntensity (E i)).toReal : ℝ) : ℂ)‖ ≤ γ / 6 := by
    have := Metric.tendsto_atTop.mp hstep (γ / 6) (by linarith)
    obtain ⟨N, hN⟩ := this
    filter_upwards [eventually_ge_atTop N] with n hn
    have := hN n hn
    rw [dist_eq_norm] at this
    exact le_of_lt this
  have hev2 : ∀ᶠ n : ℕ in atTop,
      (∑ j ∈ Finset.range (n + 1), unifIoo.real (bigEvent c ε n j)) ≤ 4 * (C₀ / (8 * ε)) := by
    have hL3 : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ Lnorm n :=
      TupleMeasure.tendsto_Lnorm_atTop.eventually_ge_atTop 3
    filter_upwards [hbnd ε hε, hL3, eventually_ge_atTop 1] with n hn hL hn1
    exact SymbolIntensity.sum_bigEvent_mass_le c ε (C := C₀ / (8 * ε)) (by positivity) hn1 hL hn
  have hev3 : ∀ᶠ n : ℕ in atTop,
      (∑ j ∈ Finset.range (n + 1), unifIoo.real (bigEvent c R n j)) ≤ C₀ / (2 * R) :=
    eventually_sum_bigEvent_mass c hbnd hC₀ hR0
  rw [Filter.eventually_atTop] at hev1 hev2 hev3
  obtain ⟨N1, hN1⟩ := hev1
  obtain ⟨N2, hN2⟩ := hev2
  obtain ⟨N3, hN3⟩ := hev3
  refine ⟨max N1 (max N2 N3), fun n hn => ?_⟩
  have hn1 := hN1 n (le_trans (le_max_left _ _) hn)
  have hn2 := hN2 n (le_trans (le_trans (le_max_left _ _) (le_max_right N1 _)) hn)
  have hn3 := hN3 n (le_trans (le_trans (le_max_right _ _) (le_max_right N1 _)) hn)
  have htail : 2 * (C₀ / (2 * R)) ≤ γ / 6 := by
    have : 2 * (C₀ / (2 * R)) = C₀ / R := by field_simp
    rw [this]; exact hm2
  have herr : ‖(∑ j ∈ Finset.range (n + 1),
        SymbolIntensity.levelSymbol (psi t ε) c n j)
      - ∑ j ∈ Finset.range (n + 1), SymbolIntensity.levelSymbol
          (fun x => ∑ i, w i * Set.indicator (E i) (fun _ => (1 : ℂ)) x) c n j‖
      ≤ γ / 6 + γ / 6 := by
    refine le_trans (hsumerr n) ?_
    have hA : η * (∑ j ∈ Finset.range (n + 1), unifIoo.real (bigEvent c ε n j))
        ≤ η * (4 * (C₀ / (8 * ε))) := mul_le_mul_of_nonneg_left hn2 hη0.le
    have hB : 2 * (∑ j ∈ Finset.range (n + 1), unifIoo.real (bigEvent c R n j))
        ≤ 2 * (C₀ / (2 * R)) := by linarith
    linarith
  rw [dist_eq_norm]
  have hsplit : (∑ j ∈ Finset.range (n + 1), SymbolIntensity.levelSymbol (psi t ε) c n j)
      - (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1) * (levyIntensityDensity x : ℂ))
      = ((∑ j ∈ Finset.range (n + 1), SymbolIntensity.levelSymbol (psi t ε) c n j)
          - ∑ j ∈ Finset.range (n + 1), SymbolIntensity.levelSymbol
              (fun x => ∑ i, w i * Set.indicator (E i) (fun _ => (1 : ℂ)) x) c n j)
        + ((∑ j ∈ Finset.range (n + 1), SymbolIntensity.levelSymbol
              (fun x => ∑ i, w i * Set.indicator (E i) (fun _ => (1 : ℂ)) x) c n j)
          - ∑ i, w i * (((levyIntensity (E i)).toReal : ℝ) : ℂ))
        + ((∑ i, w i * (((levyIntensity (E i)).toReal : ℝ) : ℂ))
          - ∫ x in {x : ℝ | ε < |x|},
              (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
                * (levyIntensityDensity x : ℂ)) := by ring
  rw [hsplit]
  refine lt_of_le_of_lt (norm_add₃_le) ?_
  linarith

/-! ## `hp1` discharged inside the layer assembly

`LayerAssembly.largeSum_charFun_limit_of_two_inputs` reduces
`CorFinal.largeSum_charFun_limit` to `hp1` and `hqi`.  `sum_mu_tendsto` is `hp1`,
so what follows records, inside Lean, that `hqi` is now the **only** remaining
input on this route: the statement below is the conclusion of
`CorFinal.largeSum_charFun_limit` with `hqi` as its single hypothesis. -/

/-- **`CorFinal.largeSum_charFun_limit` from `hqi` alone.**  The `hp1` input of
`LayerAssembly.largeSum_charFun_limit_of_two_inputs` is supplied by
`sum_mu_tendsto`; nothing else is assumed. -/
theorem largeSum_charFun_limit_of_hqi (c ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (t : ℝ)
    (hqi : ∀ k : ℕ, Tendsto (fun n : ℕ =>
        ∑ S ∈ Finset.powersetCard k (Finset.range (n + 1)),
          ‖(∫ α in Ioo (0:ℝ) 1, ∏ j ∈ S, jumpFactor t c ε n j α)
              - ∏ j ∈ S, LayerAssembly.mu t c ε n j‖) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ α in Ioo (0 : ℝ) 1,
        Complex.exp ((t : ℂ) * (Assembly5.largeSum c ε α n : ℂ) * Complex.I)) atTop
      (𝓝 (Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ)))) :=
  LayerAssembly.largeSum_charFun_limit_of_two_inputs c ε hε0 hε1 t
    (sum_mu_tendsto c hε0 t) hqi

/-- Statement guard: the conclusion above is the statement of
`Kwon1002.CorFinal.largeSum_charFun_limit`, token for token.  The `example`
mentions a sorried declaration, so it is anonymous. -/
example : ∀ (c ε : ℝ), 0 < ε → ε < 1 → ∀ t : ℝ,
    Filter.Tendsto (fun n : ℕ => ∫ α in Set.Ioo (0 : ℝ) 1,
        Complex.exp ((t : ℂ) * (Kwon1002.Assembly5.largeSum c ε α n : ℂ) * Complex.I)) Filter.atTop
      (nhds (Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (Kwon1002.levyIntensityDensity x : ℂ)))) :=
  @Kwon1002.CorFinal.largeSum_charFun_limit

end

end SymbolLimit

end Kwon1002
