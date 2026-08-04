/-
Scratch file (transfer agent): Kwon §3, Lemma 3.1(i) and Lemma 3.2.

We state and prove Kwon's transfer-operator spectral gap (Lemma 3.1(i)) and
his conditional multi-block mixing estimate (Lemma 3.2, display (17)) on top
of Shouqiao Wang's vendored substrate.
-/
import Erdos1002.GaussTransferCorrelation
import Erdos1002.GaussPrefixCylinderPartition

open MeasureTheory Set
open scoped ENNReal

namespace Kwon1002.Transfer

open Erdos1002

noncomputable section

/-! ## 0. Preliminaries on the Gauss orbit -/

theorem gaussMap_mem_Icc (x : ℝ) : gaussMap x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · simp [gaussMap, Int.fract_nonneg]
  · simpa [gaussMap] using (Int.fract_lt_one x⁻¹).le

theorem gaussOrbit_mem_Icc (m : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    gaussOrbit m x ∈ Icc (0 : ℝ) 1 := by
  induction m with
  | zero => simpa [gaussOrbit] using hx
  | succ m _ =>
      have h : gaussOrbit (m + 1) x = gaussMap (gaussOrbit m x) := by
        simp [gaussOrbit, Function.iterate_succ_apply']
      rw [h]
      exact gaussMap_mem_Icc _

/-! ## 0'. Monotonicity of the two substrate norms -/

theorem gaussUnitUpperBound_mono {A A' : ℝ} {f : ℝ → ℝ}
    (hf : GaussUnitUpperBound A f) (h : A ≤ A') : GaussUnitUpperBound A' f :=
  fun _ hx => (hf hx).trans h

theorem gaussUnitLipschitzBound_mono {K K' : ℝ} {f : ℝ → ℝ}
    (hf : GaussUnitLipschitzBound K f) (h : K ≤ K') :
    GaussUnitLipschitzBound K' f := by
  intro x hx y hy
  exact (hf hx hy).trans (mul_le_mul_of_nonneg_right h (abs_nonneg _))

/-! ## 1. Lemma 3.1(i): the transfer-operator spectral gap

Kwon's display is `‖L^r f - h ∫ f‖₁ ≤ C ρ^r ‖f‖_BV`, with `L` the transfer
operator normalized against **Lebesgue** measure and `h` the Gauss invariant
density.  The substrate works with `gaussTransfer`, the transfer operator
normalized against the **Gauss** measure `ν`.  The two are conjugate,
`L^r (h · g) = h · (gaussTransfer^[r]) g`, so Kwon's display for `f = h · g`
is literally the `L¹(ν)` statement below.  The class `BV(0,1)` is replaced by
Wang's Lipschitz class; the sup-norm form is stronger than Kwon's `L¹` form.
Kwon's `C` is `1` and his `ρ` is Wang's explicit `527/540`. -/

/-- **Lemma 3.1(i)**, uniform (sup-norm) form: the iterated Gauss transfer
operator converges to the mean at the explicit geometric rate. -/
theorem lemma_3_1_i_sup {A K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K)
    (hfM : Measurable f) (hf0 : GaussUnitNonnegative f)
    (hfA : GaussUnitUpperBound A f) (hfLip : GaussUnitLipschitzBound K f)
    (r : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    |(gaussTransfer^[r]) f y - ∫ x, f x ∂gaussMeasure| ≤ (527 / 540 : ℝ) ^ r * K :=
  abs_gaussTransfer_iterate_sub_integral_le hK hfM hf0 hfA hfLip r hy

/-- **Lemma 3.1(i)**, `L¹` form (Kwon's display, transported to `ν`). -/
theorem lemma_3_1_i_L1 {A K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K)
    (hfM : Measurable f) (hf0 : GaussUnitNonnegative f)
    (hfA : GaussUnitUpperBound A f) (hfLip : GaussUnitLipschitzBound K f)
    (r : ℕ) :
    (∫ y, |(gaussTransfer^[r]) f y - ∫ x, f x ∂gaussMeasure| ∂gaussMeasure)
      ≤ (527 / 540 : ℝ) ^ r * K := by
  have hInt : Integrable ((gaussTransfer^[r]) f) gaussMeasure :=
    integrable_gaussTransfer_iterate_of_unit_bounds hfM hf0 hfA r
  have hd : Integrable
      (fun y => |(gaussTransfer^[r]) f y - ∫ x, f x ∂gaussMeasure|) gaussMeasure :=
    (hInt.sub (integrable_const _)).abs
  have hb : ∀ᵐ y ∂gaussMeasure,
      |(gaussTransfer^[r]) f y - ∫ x, f x ∂gaussMeasure| ≤ (527 / 540 : ℝ) ^ r * K := by
    filter_upwards [gaussMeasure_unit_ae] with y hy
    exact lemma_3_1_i_sup hK hfM hf0 hfA hfLip r ⟨hy.1.le, hy.2⟩
  simpa using integral_mono_ae hd (integrable_const _) hb

/-- **Lemma 3.1(i)** in Kwon's existential shape: there are `C > 0` and
`0 < ρ < 1` such that `‖L^r f - h ∫ f‖₁ ≤ C ρ^r ‖f‖`. -/
theorem lemma_3_1_i :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ {A K : ℝ} {f : ℝ → ℝ}, 0 ≤ K → Measurable f → GaussUnitNonnegative f →
        GaussUnitUpperBound A f → GaussUnitLipschitzBound K f → ∀ r : ℕ,
        (∫ y, |(gaussTransfer^[r]) f y - ∫ x, f x ∂gaussMeasure| ∂gaussMeasure)
          ≤ C * ρ ^ r * K := by
  refine ⟨1, 527 / 540, by norm_num, by norm_num, by norm_num, ?_⟩
  intro A K f hK hfM hf0 hfA hfLip r
  simpa using lemma_3_1_i_L1 hK hfM hf0 hfA hfLip r

/-! ## 2. Multi-block products

A block list `[(m₁,g₁), …, (m_s,g_s)]` records the observables together with
the **gaps** `mᵢ = tᵢ - t_{i-1}`; so `tᵢ = m₁ + ⋯ + mᵢ` and
`blockProduct blocks α = ∏ᵢ gᵢ (T^{tᵢ} α)`. -/

def blockProduct : List (ℕ × (ℝ → ℝ)) → ℝ → ℝ
  | [], _ => 1
  | p :: rest, x => p.2 (gaussOrbit p.1 x) * blockProduct rest (gaussOrbit p.1 x)

@[simp] theorem blockProduct_nil (x : ℝ) : blockProduct [] x = 1 := rfl

@[simp] theorem blockProduct_cons (p : ℕ × (ℝ → ℝ)) (rest : List (ℕ × (ℝ → ℝ)))
    (x : ℝ) :
    blockProduct (p :: rest) x =
      p.2 (gaussOrbit p.1 x) * blockProduct rest (gaussOrbit p.1 x) := rfl

/-- `∏ᵢ ∫ gᵢ dν`. -/
def blockMean (blocks : List (ℕ × (ℝ → ℝ))) : ℝ :=
  (blocks.map (fun p => ∫ x, p.2 x ∂gaussMeasure)).prod

@[simp] theorem blockMean_nil : blockMean [] = 1 := rfl

@[simp] theorem blockMean_cons (p : ℕ × (ℝ → ℝ)) (rest : List (ℕ × (ℝ → ℝ))) :
    blockMean (p :: rest) = (∫ x, p.2 x ∂gaussMeasure) * blockMean rest := rfl

theorem measurable_blockProduct (blocks : List (ℕ × (ℝ → ℝ)))
    (h : ∀ p ∈ blocks, Measurable p.2) : Measurable (blockProduct blocks) := by
  induction blocks with
  | nil => exact measurable_const
  | cons p rest ih =>
      have hp : Measurable p.2 := h p (by simp)
      have hr : Measurable (blockProduct rest) :=
        ih (fun q hq => h q (by simp [hq]))
      show Measurable fun x =>
        p.2 (gaussOrbit p.1 x) * blockProduct rest (gaussOrbit p.1 x)
      exact (hp.comp (measurable_gaussOrbit p.1)).mul
        (hr.comp (measurable_gaussOrbit p.1))

theorem blockProduct_nonneg (blocks : List (ℕ × (ℝ → ℝ)))
    (h0 : ∀ p ∈ blocks, GaussUnitNonnegative p.2) :
    GaussUnitNonnegative (blockProduct blocks) := by
  induction blocks with
  | nil => intro x _; simp
  | cons p rest ih =>
      intro x hx
      have hy : gaussOrbit p.1 x ∈ Icc (0 : ℝ) 1 := gaussOrbit_mem_Icc _ hx
      exact mul_nonneg (h0 p (by simp) hy) (ih (fun q hq => h0 q (by simp [hq])) hy)

theorem blockProduct_le (blocks : List (ℕ × (ℝ → ℝ))) {A : ℝ}
    (h0 : ∀ p ∈ blocks, GaussUnitNonnegative p.2)
    (hA : ∀ p ∈ blocks, GaussUnitUpperBound A p.2) :
    GaussUnitUpperBound (A ^ blocks.length) (blockProduct blocks) := by
  induction blocks with
  | nil => intro x _; simp
  | cons p rest ih =>
      intro x hx
      have hy : gaussOrbit p.1 x ∈ Icc (0 : ℝ) 1 := gaussOrbit_mem_Icc _ hx
      have h1 : p.2 (gaussOrbit p.1 x) ≤ A := hA p (by simp) hy
      have h4 : 0 ≤ p.2 (gaussOrbit p.1 x) := h0 p (by simp) hy
      have h2 : blockProduct rest (gaussOrbit p.1 x) ≤ A ^ rest.length :=
        ih (fun q hq => h0 q (by simp [hq])) (fun q hq => hA q (by simp [hq])) hy
      have h3 : 0 ≤ blockProduct rest (gaussOrbit p.1 x) :=
        blockProduct_nonneg rest (fun q hq => h0 q (by simp [hq])) hy
      have hfin : p.2 (gaussOrbit p.1 x) * blockProduct rest (gaussOrbit p.1 x)
          ≤ A ^ (rest.length + 1) := by
        calc p.2 (gaussOrbit p.1 x) * blockProduct rest (gaussOrbit p.1 x)
            ≤ A * A ^ rest.length := mul_le_mul h1 h2 h3 (h4.trans h1)
          _ = A ^ (rest.length + 1) := by ring
      simpa using hfin

/-! ## 3. The multi-block mixing estimate (heart of Lemma 3.2)

This is the induction that Kwon summarizes as "apply Lemma 3.1(i) across the
first gap, multiply by the next BV observable, and iterate".  The initial
density `φ` is arbitrary in the same bounded-Lipschitz class, which is what
makes the constants **uniform in the conditioning event**. -/

theorem multiblock_mixing {A K : ℝ} (hK : 0 ≤ K) (M : ℕ) :
    ∀ blocks : List (ℕ × (ℝ → ℝ)),
      (∀ p ∈ blocks, Measurable p.2) →
      (∀ p ∈ blocks, GaussUnitNonnegative p.2) →
      (∀ p ∈ blocks, GaussUnitUpperBound A p.2) →
      (∀ p ∈ blocks, GaussUnitLipschitzBound K p.2) →
      (∀ p ∈ blocks, M ≤ p.1) →
      ∀ φ : ℝ → ℝ, Measurable φ → GaussUnitNonnegative φ →
        GaussUnitUpperBound A φ → GaussUnitLipschitzBound K φ →
        |(∫ x, φ x * blockProduct blocks x ∂gaussMeasure) -
            (∫ x, φ x ∂gaussMeasure) * blockMean blocks| ≤
          (blocks.length : ℝ) * ((527 / 540 : ℝ) ^ M * K * A ^ blocks.length) := by
  intro blocks
  induction blocks with
  | nil =>
      intro _ _ _ _ _ φ _ _ _ _
      simp
  | cons p rest ih =>
    intro hM h0 hAb hKb hgap φ hφM hφ0 hφA hφK
    -- tail hypotheses
    have hrestM : ∀ q ∈ rest, Measurable q.2 := fun q hq => hM q (by simp [hq])
    have hrest0 : ∀ q ∈ rest, GaussUnitNonnegative q.2 := fun q hq => h0 q (by simp [hq])
    have hrestA : ∀ q ∈ rest, GaussUnitUpperBound A q.2 := fun q hq => hAb q (by simp [hq])
    have hrestK : ∀ q ∈ rest, GaussUnitLipschitzBound K q.2 := fun q hq => hKb q (by simp [hq])
    have hrestgap : ∀ q ∈ rest, M ≤ q.1 := fun q hq => hgap q (by simp [hq])
    have hgM : Measurable p.2 := hM p (by simp)
    have hg0 : GaussUnitNonnegative p.2 := h0 p (by simp)
    have hgA : GaussUnitUpperBound A p.2 := hAb p (by simp)
    have hgK : GaussUnitLipschitzBound K p.2 := hKb p (by simp)
    have hmM : M ≤ p.1 := hgap p (by simp)
    have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have hA0 : 0 ≤ A := (hg0 hzero).trans (hgA hzero)
    have hE : (0 : ℝ) ≤ (527 / 540 : ℝ) ^ M * K := mul_nonneg (by positivity) hK
    have hpowA : (0 : ℝ) ≤ A ^ rest.length := pow_nonneg hA0 _
    -- the merged observable `G y = g y * blockProduct rest y`
    obtain ⟨G, hGfun⟩ : ∃ G : ℝ → ℝ, G = fun y => p.2 y * blockProduct rest y := ⟨_, rfl⟩
    have hGdef : ∀ y, G y = p.2 y * blockProduct rest y := fun y => by rw [hGfun]
    have hGM : Measurable G := by
      rw [hGfun]; exact hgM.mul (measurable_blockProduct rest hrestM)
    have hG0 : GaussUnitNonnegative G := by
      intro y hy
      rw [hGdef]
      exact mul_nonneg (hg0 hy) (blockProduct_nonneg rest hrest0 hy)
    have hGA : GaussUnitUpperBound (A ^ (rest.length + 1)) G := by
      intro y hy
      rw [hGdef]
      calc p.2 y * blockProduct rest y
          ≤ A * A ^ rest.length :=
            mul_le_mul (hgA hy) (blockProduct_le rest hrest0 hrestA hy)
              (blockProduct_nonneg rest hrest0 hy) hA0
        _ = A ^ (rest.length + 1) := by ring
    -- step 1 : push the first gap through the transfer operator
    have hbp : ∀ x : ℝ, blockProduct (p :: rest) x = G (gaussOrbit p.1 x) := by
      intro x; rw [hGdef]; rfl
    have hstep : (∫ x, φ x * blockProduct (p :: rest) x ∂gaussMeasure)
        = ∫ y, ((gaussTransfer^[p.1]) φ y) * G y ∂gaussMeasure := by
      simp_rw [hbp]
      exact integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate hφM hGM hφ0 hφA p.1
    -- integrability bookkeeping
    have hφInt : Integrable φ gaussMeasure := by
      refine Integrable.of_bound hφM.aestronglyMeasurable A ?_
      filter_upwards [gaussMeasure_unit_ae] with x hx
      have hxcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 hxcc)]
      exact hφA hxcc
    have hc0 : 0 ≤ ∫ x, φ x ∂gaussMeasure := by
      apply integral_nonneg_of_ae
      filter_upwards [gaussMeasure_unit_ae] with x hx
      exact hφ0 ⟨hx.1.le, hx.2⟩
    have hcAae : ∀ᵐ x ∂gaussMeasure, φ x ≤ A := by
      filter_upwards [gaussMeasure_unit_ae] with x hx
      exact hφA ⟨hx.1.le, hx.2⟩
    have hcA : (∫ x, φ x ∂gaussMeasure) ≤ A := by
      simpa using integral_mono_ae hφInt (integrable_const A) hcAae
    have hGint : Integrable G gaussMeasure := by
      refine Integrable.of_bound hGM.aestronglyMeasurable (A ^ (rest.length + 1)) ?_
      filter_upwards [gaussMeasure_unit_ae] with y hy
      have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 hycc)]
      exact hGA hycc
    have hPint : Integrable ((gaussTransfer^[p.1]) φ) gaussMeasure :=
      integrable_gaussTransfer_iterate_of_unit_bounds hφM hφ0 hφA p.1
    have hPb := gaussTransfer_iterate_unit_bounds hφ0 hφA p.1
    have hprodInt :
        Integrable (fun y => ((gaussTransfer^[p.1]) φ y) * G y) gaussMeasure := by
      refine Integrable.of_bound
        (hPint.aestronglyMeasurable.mul hGM.aestronglyMeasurable)
        (A * A ^ (rest.length + 1)) ?_
      filter_upwards [gaussMeasure_unit_ae] with y hy
      have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hPb.1 hycc),
        abs_of_nonneg (hG0 hycc)]
      exact mul_le_mul (hPb.2 hycc) (hGA hycc) (hG0 hycc) hA0
    have hcGint : Integrable (fun y => (∫ x, φ x ∂gaussMeasure) * G y) gaussMeasure :=
      hGint.const_mul _
    -- the spectral-gap step
    have hsplit :
        (∫ y, ((gaussTransfer^[p.1]) φ y) * G y ∂gaussMeasure)
            - (∫ x, φ x ∂gaussMeasure) * (∫ y, G y ∂gaussMeasure)
          = ∫ y, (((gaussTransfer^[p.1]) φ y) - (∫ x, φ x ∂gaussMeasure)) * G y
              ∂gaussMeasure := by
      rw [← integral_const_mul, ← integral_sub hprodInt hcGint]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    have hbound1 :
        |∫ y, (((gaussTransfer^[p.1]) φ y) - (∫ x, φ x ∂gaussMeasure)) * G y
            ∂gaussMeasure|
          ≤ (527 / 540 : ℝ) ^ M * K * A ^ (rest.length + 1) := by
      have hb : ∀ᵐ y ∂gaussMeasure,
          ‖(((gaussTransfer^[p.1]) φ y) - (∫ x, φ x ∂gaussMeasure)) * G y‖
            ≤ (527 / 540 : ℝ) ^ M * K * A ^ (rest.length + 1) := by
        filter_upwards [gaussMeasure_unit_ae] with y hy
        have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
        have h1 : |((gaussTransfer^[p.1]) φ y) - (∫ x, φ x ∂gaussMeasure)|
            ≤ (527 / 540 : ℝ) ^ p.1 * K :=
          abs_gaussTransfer_iterate_sub_integral_le hK hφM hφ0 hφA hφK p.1 hycc
        have h2 : (527 / 540 : ℝ) ^ p.1 ≤ (527 / 540 : ℝ) ^ M :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hmM
        have h3 : |((gaussTransfer^[p.1]) φ y) - (∫ x, φ x ∂gaussMeasure)|
            ≤ (527 / 540 : ℝ) ^ M * K :=
          h1.trans (mul_le_mul_of_nonneg_right h2 hK)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hG0 hycc)]
        exact mul_le_mul h3 (hGA hycc) (hG0 hycc) hE
      simpa using norm_integral_le_of_norm_le_const hb
    -- the induction hypothesis, applied with `φ := gᵢ`
    have hIH := ih hrestM hrest0 hrestA hrestK hrestgap p.2 hgM hg0 hgA hgK
    have hGeq : (∫ y, G y ∂gaussMeasure)
        = ∫ x, p.2 x * blockProduct rest x ∂gaussMeasure := by
      simp only [hGdef]
    -- assemble
    have hsum :
        (∫ x, φ x * blockProduct (p :: rest) x ∂gaussMeasure)
            - (∫ x, φ x ∂gaussMeasure) * blockMean (p :: rest)
          = ((∫ y, ((gaussTransfer^[p.1]) φ y) * G y ∂gaussMeasure)
              - (∫ x, φ x ∂gaussMeasure) * (∫ y, G y ∂gaussMeasure))
            + (∫ x, φ x ∂gaussMeasure) *
                ((∫ y, G y ∂gaussMeasure)
                  - (∫ x, p.2 x ∂gaussMeasure) * blockMean rest) := by
      rw [hstep, blockMean_cons]; ring
    have habs :
        |(∫ x, φ x * blockProduct (p :: rest) x ∂gaussMeasure)
            - (∫ x, φ x ∂gaussMeasure) * blockMean (p :: rest)|
          ≤ ((527 / 540 : ℝ) ^ M * K * A ^ (rest.length + 1))
            + (∫ x, φ x ∂gaussMeasure) *
              ((rest.length : ℝ) * ((527 / 540 : ℝ) ^ M * K * A ^ rest.length)) := by
      rw [hsum]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [hsplit]
        exact hbound1
      · rw [abs_mul, abs_of_nonneg hc0]
        refine mul_le_mul_of_nonneg_left ?_ hc0
        rw [hGeq]
        exact hIH
    refine habs.trans ?_
    have hstep2 : (∫ x, φ x ∂gaussMeasure) *
          ((rest.length : ℝ) * ((527 / 540 : ℝ) ^ M * K * A ^ rest.length))
        ≤ A * ((rest.length : ℝ) * ((527 / 540 : ℝ) ^ M * K * A ^ rest.length)) :=
      mul_le_mul_of_nonneg_right hcA
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hE hpowA))
    have hfinal :
        ((527 / 540 : ℝ) ^ M * K * A ^ (rest.length + 1))
          + A * ((rest.length : ℝ) * ((527 / 540 : ℝ) ^ M * K * A ^ rest.length))
        = ((rest.length : ℝ) + 1) *
            ((527 / 540 : ℝ) ^ M * K * A ^ (rest.length + 1)) := by ring
    have : ((527 / 540 : ℝ) ^ M * K * A ^ (rest.length + 1))
        + (∫ x, φ x ∂gaussMeasure) *
            ((rest.length : ℝ) * ((527 / 540 : ℝ) ^ M * K * A ^ rest.length))
        ≤ ((rest.length : ℝ) + 1) *
            ((527 / 540 : ℝ) ^ M * K * A ^ (rest.length + 1)) := by
      rw [← hfinal]; linarith
    simpa using this

/-! ## 4. Conditioning

`condMean S F = E[F | S]` for the Gauss measure. -/

def condMean (S : Set ℝ) (F : ℝ → ℝ) : ℝ :=
  (∫ x in S, F x ∂gaussMeasure) / (gaussMeasure S).toReal

/-- `φ` is a version of the conditional density of `T^d α` given `α ∈ S`
(with respect to the Gauss measure). -/
def IsCondDensity (S : Set ℝ) (d : ℕ) (φ : ℝ → ℝ) : Prop :=
  ∀ F : ℝ → ℝ, Measurable F →
    condMean S (fun α => F (gaussOrbit d α)) = ∫ y, φ y * F y ∂gaussMeasure

/-- **Conditional multi-block mixing**, abstract form.  Given any conditioning
event `S` whose depth-`d` conditional density lies in the bounded-Lipschitz
class `(A, K)`, the block observables decouple at rate `ρ^M`, with constants
depending only on `(A, K, s)`, **not** on `S`. -/
theorem conditional_multiblock_mixing
    {S : Set ℝ} {d : ℕ} {A K : ℝ} (hK : 0 ≤ K) (M : ℕ)
    {φ : ℝ → ℝ} (hφM : Measurable φ) (hφ0 : GaussUnitNonnegative φ)
    (hφA : GaussUnitUpperBound A φ) (hφK : GaussUnitLipschitzBound K φ)
    (hφmean : (∫ x, φ x ∂gaussMeasure) = 1)
    (hrep : IsCondDensity S d φ)
    (blocks : List (ℕ × (ℝ → ℝ)))
    (hM : ∀ p ∈ blocks, Measurable p.2)
    (h0 : ∀ p ∈ blocks, GaussUnitNonnegative p.2)
    (hAb : ∀ p ∈ blocks, GaussUnitUpperBound A p.2)
    (hKb : ∀ p ∈ blocks, GaussUnitLipschitzBound K p.2)
    (hgap : ∀ p ∈ blocks, M ≤ p.1) :
    |condMean S (fun α => blockProduct blocks (gaussOrbit d α)) - blockMean blocks|
      ≤ (blocks.length : ℝ) *
          ((527 / 540 : ℝ) ^ M * K * A ^ blocks.length) := by
  have hrw := hrep (blockProduct blocks) (measurable_blockProduct blocks hM)
  rw [hrw]
  have := multiblock_mixing (A := A) (K := K) hK M blocks hM h0 hAb hKb hgap
    φ hφM hφ0 hφA hφK
  rwa [hφmean, one_mul] at this

/-! ## 5. Kwon's display (14): the explicit cylinder conditional density

For a word `w = (a₁,…,a_d)` with convergents `p_j/q_j`, the inverse branch is
`h_w(y) = (p_d + p_{d-1} y)/(q_d + q_{d-1} y)`, `|h_w'(y)| = (q_d+q_{d-1}y)^{-2}`,
and Kwon's `ρ_w(y) = q_d(q_d+q_{d-1})/(q_d+q_{d-1}y)^2` is the **Lebesgue**
conditional density of `T^d α` given `α ∈ I_w`.

Since the substrate normalizes everything against the Gauss measure `ν`, we
need `ρ_w` re-expressed as a `ν`-density.  Dividing by the Gauss density and
using `1 + h_w(y) = (q_d+p_d + (q_{d-1}+p_{d-1})y)/(q_d+q_{d-1}y)` gives

  `ρ_w^ν(y) = c_w · (1+y) / ((1 + a y)(1 + b y))`,
  `a = q_{d-1}/q_d ∈ [0,1]`,  `b = (q_{d-1}+p_{d-1})/(q_d+p_d) ∈ [0,1]`,

with `c_w` fixed by `∫ ρ_w^ν dν = 1`.  (Sanity checks: `d = 0` gives
`a = 0, b = 1` and `ρ ≡ 1`; `d = 1`, `w = [q]` gives
`(1+y)q(q+1)/((q+y)(q+1+y)) = q(q+1)·gaussBranchRatio q y`, i.e. Wang's
`finiteGaussDigitTailDensity` for a single digit.)

Everything about this two-parameter family is proved below.  In particular
Kwon's `sup_w ‖ρ_w‖_BV < ∞` becomes the *explicit* uniform pair `(8, 24)`. -/

/-- The unnormalized Gauss-measure cylinder weight in Kwon's normalized
Möbius coordinates. -/
def kwonWeight (a b y : ℝ) : ℝ := (1 + y) / ((1 + a * y) * (1 + b * y))

theorem measurable_kwonWeight (a b : ℝ) : Measurable (kwonWeight a b) := by
  unfold kwonWeight
  fun_prop

theorem kwonWeight_bounds {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    1 / 4 ≤ kwonWeight a b y ∧ kwonWeight a b y ≤ 2 := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨hy0, hy1⟩ := hy
  have hay0 : (0 : ℝ) ≤ a * y := mul_nonneg ha0 hy0
  have hby0 : (0 : ℝ) ≤ b * y := mul_nonneg hb0 hy0
  have hay1 : a * y ≤ 1 := by nlinarith
  have hby1 : b * y ≤ 1 := by nlinarith
  have hd : (0 : ℝ) < (1 + a * y) * (1 + b * y) := by nlinarith
  have hd4 : (1 + a * y) * (1 + b * y) ≤ 4 := by
    nlinarith [mul_nonneg hay0 (sub_nonneg.mpr hby1)]
  constructor
  · rw [kwonWeight, le_div_iff₀ hd]; nlinarith
  · rw [kwonWeight, div_le_iff₀ hd]; nlinarith

theorem kwonWeight_lipschitz {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) : GaussUnitLipschitzBound 6 (kwonWeight a b) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  intro y hy z hz
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hz0, hz1⟩ := hz
  have hay0 : (0 : ℝ) ≤ a * y := mul_nonneg ha0 hy0
  have hby0 : (0 : ℝ) ≤ b * y := mul_nonneg hb0 hy0
  have haz0 : (0 : ℝ) ≤ a * z := mul_nonneg ha0 hz0
  have hbz0 : (0 : ℝ) ≤ b * z := mul_nonneg hb0 hz0
  have p1 : (0 : ℝ) < 1 + a * y := by linarith
  have p2 : (0 : ℝ) < 1 + b * y := by linarith
  have p3 : (0 : ℝ) < 1 + a * z := by linarith
  have p4 : (0 : ℝ) < 1 + b * z := by linarith
  have key : kwonWeight a b y - kwonWeight a b z
      = ((y - z) * (1 - (a + b) - a * b * (y + z) - a * b * y * z))
        / (((1 + a * y) * (1 + b * y)) * ((1 + a * z) * (1 + b * z))) := by
    unfold kwonWeight
    field_simp
    ring
  have hD : (1 : ℝ) ≤ ((1 + a * y) * (1 + b * y)) * ((1 + a * z) * (1 + b * z)) := by
    nlinarith [mul_nonneg hay0 hby0, mul_nonneg haz0 hbz0,
      mul_nonneg (mul_nonneg hay0 hby0) (mul_nonneg haz0 hbz0)]
  have hDpos : (0 : ℝ) < ((1 + a * y) * (1 + b * y)) * ((1 + a * z) * (1 + b * z)) :=
    lt_of_lt_of_le zero_lt_one hD
  have hE : |1 - (a + b) - a * b * (y + z) - a * b * y * z| ≤ 4 := by
    have hab0 : (0 : ℝ) ≤ a * b := mul_nonneg ha0 hb0
    have hab1 : a * b ≤ 1 := by nlinarith
    have hyz0 : (0 : ℝ) ≤ y * z := mul_nonneg hy0 hz0
    have hyz1 : y * z ≤ 1 := by nlinarith
    have h1 : a * b * (y + z) ≤ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hab1 (add_nonneg hy0 hz0)]
    have h2 : a * b * y * z ≤ 1 := by
      nlinarith [mul_le_mul hab1 hyz1 hyz0 zero_le_one]
    have h1' : (0 : ℝ) ≤ a * b * (y + z) := mul_nonneg hab0 (add_nonneg hy0 hz0)
    have h2' : (0 : ℝ) ≤ a * b * y * z := mul_nonneg (mul_nonneg hab0 hy0) hz0
    rw [abs_le]
    constructor <;> linarith
  rw [key, abs_div, abs_mul, abs_of_pos hDpos, div_le_iff₀ hDpos]
  nlinarith [mul_le_mul_of_nonneg_left hE (abs_nonneg (y - z)), abs_nonneg (y - z),
    mul_nonneg (abs_nonneg (y - z)) (sub_nonneg.mpr hD)]

theorem integrable_kwonWeight {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) : Integrable (kwonWeight a b) gaussMeasure := by
  refine Integrable.of_bound (measurable_kwonWeight a b).aestronglyMeasurable 2 ?_
  filter_upwards [gaussMeasure_unit_ae] with y hy
  have h := kwonWeight_bounds ha hb (⟨hy.1.le, hy.2⟩ : y ∈ Icc (0 : ℝ) 1)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [h.1])]
  exact h.2

/-- The normalizing constant `∫ kwonWeight a b dν`. -/
def kwonNorm (a b : ℝ) : ℝ := ∫ z, kwonWeight a b z ∂gaussMeasure

theorem kwonNorm_bounds {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    1 / 4 ≤ kwonNorm a b ∧ kwonNorm a b ≤ 2 := by
  have hint := integrable_kwonWeight ha hb
  constructor
  · have hb' : ∀ᵐ y ∂gaussMeasure, (1 / 4 : ℝ) ≤ kwonWeight a b y := by
      filter_upwards [gaussMeasure_unit_ae] with y hy
      exact (kwonWeight_bounds ha hb (⟨hy.1.le, hy.2⟩ : y ∈ Icc (0 : ℝ) 1)).1
    simpa [kwonNorm] using integral_mono_ae (integrable_const (1 / 4 : ℝ)) hint hb'
  · have hb' : ∀ᵐ y ∂gaussMeasure, kwonWeight a b y ≤ (2 : ℝ) := by
      filter_upwards [gaussMeasure_unit_ae] with y hy
      exact (kwonWeight_bounds ha hb (⟨hy.1.le, hy.2⟩ : y ∈ Icc (0 : ℝ) 1)).2
    simpa [kwonNorm] using integral_mono_ae hint (integrable_const (2 : ℝ)) hb'

/-- **Kwon's `ρ_w`**, expressed as a density against the Gauss measure. -/
def kwonDensity (a b : ℝ) : ℝ → ℝ := fun y => kwonWeight a b y / kwonNorm a b

theorem measurable_kwonDensity (a b : ℝ) : Measurable (kwonDensity a b) :=
  (measurable_kwonWeight a b).div_const _

theorem kwonDensity_nonneg {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) : GaussUnitNonnegative (kwonDensity a b) := by
  intro y hy
  have h := kwonWeight_bounds ha hb hy
  have hZ := kwonNorm_bounds ha hb
  exact div_nonneg (by linarith [h.1]) (by linarith [hZ.1])

/-- Uniform sup bound: `‖ρ_w‖_∞ ≤ 8`, independently of the word. -/
theorem kwonDensity_le {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    GaussUnitUpperBound 8 (kwonDensity a b) := by
  intro y hy
  have h := kwonWeight_bounds ha hb hy
  have hZ := kwonNorm_bounds ha hb
  have hZ0 : (0 : ℝ) < kwonNorm a b := by linarith [hZ.1]
  rw [kwonDensity, div_le_iff₀ hZ0]
  nlinarith [h.2, hZ.1]

/-- Uniform Lipschitz bound: `ρ_w` is `24`-Lipschitz, independently of the
word.  This is Kwon's `sup_w ‖ρ_w‖_BV < ∞`, made explicit. -/
theorem kwonDensity_lipschitz {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) : GaussUnitLipschitzBound 24 (kwonDensity a b) := by
  intro y hy z hz
  have hZ := kwonNorm_bounds ha hb
  have hZ0 : (0 : ℝ) < kwonNorm a b := by linarith [hZ.1]
  have hlip := kwonWeight_lipschitz ha hb hy hz
  have hrw : kwonDensity a b y - kwonDensity a b z
      = (kwonWeight a b y - kwonWeight a b z) / kwonNorm a b := by
    simp only [kwonDensity]; ring
  rw [hrw, abs_div, abs_of_pos hZ0, div_le_iff₀ hZ0]
  nlinarith [abs_nonneg (y - z), hZ.1, hlip]

theorem kwonDensity_integral_eq_one {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) : (∫ y, kwonDensity a b y ∂gaussMeasure) = 1 := by
  have hZ := kwonNorm_bounds ha hb
  have hZ0 : kwonNorm a b ≠ 0 := ne_of_gt (by linarith [hZ.1])
  simp only [kwonDensity]
  rw [integral_div]
  exact div_self hZ0

/-! ## 6. Lemma 3.2 for continued-fraction cylinders

Everything quantitative is now proved.  The single remaining input is a pure
*identity*, no estimate is hidden in it: the depth-`d` transfer of the
indicator of a cylinder is `ν(I_w)` times the explicit Möbius density.  In
Kwon's notation this is exactly display (14) together with the formula for
`ρ_w` printed just after it, rewritten as a `ν`-density.  Wang's substrate
discharges the case `d = 1` (`finiteGaussDigitTailDensity`, whose value is
`gaussBranchRatio q y`, i.e. `kwonWeight (1/q) (1/(q+1)) y / (q(q+1))`) but
has no depth-`d` version, so this is where we stop. -/

/-- **Kwon (14), identification step** (sorried).  With `p_j/q_j` the
convergents of `w`, the parameters are `a = q_{d-1}/q_d ∈ [0,1]` and
`b = (q_{d-1}+p_{d-1})/(q_d+p_d) ∈ [0,1]`.  Content: change of variables
through the inverse branch `h_w(y) = (p_d+p_{d-1}y)/(q_d+q_{d-1}y)`, whose
Gauss-measure Jacobian is `(1+y)/((q_d+p_d+(q_{d-1}+p_{d-1})y)(q_d+q_{d-1}y))`,
combined with `|I_w|` from (14).

DOMAIN NOTE (corrected 2026-08-03): this identity holds on `Ioo 0 1`, NOT on
`Icc 0 1`. At `y = 1` the surviving branch index shifts (Wang's cylinders are
`Ioc (1/(q+1)) (1/q)`, so `1/(n+2)` is a right endpoint), and the identity is
FALSE there, see `TransferIdentity.cylinder_transfer_eq_kwonDensity_Icc_false`
for a machine-checked refutation. Nothing downstream weakens: every consumer
uses the identity `ν`-a.e., and `ν{1} = 0`. Proved in
`TransferIdentity.cylinder_transfer_eq_kwonDensity_Ioo`. -/
theorem cylinder_transfer_eq_kwonDensity (w : List ℕ) (hw : ∀ q ∈ w, 0 < q) :
    ∃ a b : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧
      ∀ y ∈ Ioo (0 : ℝ) 1,
        (gaussTransfer^[w.length])
            ((gaussHalfOpenPrefixCylinder w).indicator (fun _ => (1 : ℝ))) y
          = (gaussMeasure (gaussHalfOpenPrefixCylinder w)).toReal *
              kwonDensity a b y := by
  sorry

/-- `ν`-a.e. point lies in the OPEN unit interval: `ν{1} = 0` because `ν`
has a density with respect to Lebesgue measure. This is what lets every
consumer of the (corrected) `Ioo`-form identity work `ν`-a.e. -/
theorem gaussMeasure_ae_Ioo : ∀ᵐ y ∂gaussMeasure, y ∈ Ioo (0 : ℝ) 1 := by
  have h1 : gaussMeasure {(1 : ℝ)} = 0 := by
    rw [gaussMeasure_eq_volume_withDensity]
    exact withDensity_absolutelyContinuous volume gaussDensity (by simp)
  have h2 : ∀ᵐ y ∂gaussMeasure, y ≠ (1 : ℝ) := by
    rw [ae_iff]; simpa using h1
  filter_upwards [gaussMeasure_unit_ae, h2] with y hy hy1
  exact ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩

/-- If the depth-`d` transfer of `1_S` is `ν(S)` times the explicit Möbius
density, then that density *is* the conditional density of `T^d α` given
`α ∈ S`.  (Fully proved from the substrate's Perron-Frobenius identity.) -/
theorem isCondDensity_of_transfer_eq {S : Set ℝ} (hS : MeasurableSet S) {d : ℕ}
    (hSpos : 0 < (gaussMeasure S).toReal) {a b : ℝ}
    (hid : ∀ y ∈ Ioo (0 : ℝ) 1,
      (gaussTransfer^[d]) (S.indicator (fun _ => (1 : ℝ))) y
        = (gaussMeasure S).toReal * kwonDensity a b y) :
    IsCondDensity S d (kwonDensity a b) := by
  intro F hF
  set f : ℝ → ℝ := S.indicator (fun _ => (1 : ℝ)) with hf
  have hfM : Measurable f := measurable_const.indicator hS
  have hf0 : GaussUnitNonnegative f := fun x _ =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hf1 : GaussUnitUpperBound 1 f := by
    intro x _
    by_cases hx : x ∈ S
    · simp [hf, Set.indicator_of_mem hx]
    · simp [hf, Set.indicator_of_notMem hx]
  have hind : ∀ x : ℝ,
      f x * F (gaussOrbit d x) = S.indicator (fun z => F (gaussOrbit d z)) x := by
    intro x
    by_cases hx : x ∈ S
    · simp [hf, Set.indicator_of_mem hx]
    · simp [hf, Set.indicator_of_notMem hx]
  have h1 : (∫ x in S, F (gaussOrbit d x) ∂gaussMeasure)
      = ∫ x, f x * F (gaussOrbit d x) ∂gaussMeasure := by
    simp_rw [hind]
    exact (integral_indicator hS).symm
  have h2 : (∫ x, f x * F (gaussOrbit d x) ∂gaussMeasure)
      = ∫ y, ((gaussTransfer^[d]) f y) * F y ∂gaussMeasure :=
    integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate hfM hF hf0 hf1 d
  have h3 : (∫ y, ((gaussTransfer^[d]) f y) * F y ∂gaussMeasure)
      = (gaussMeasure S).toReal * ∫ y, kwonDensity a b y * F y ∂gaussMeasure := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [gaussMeasure_ae_Ioo] with y hy
    rw [hid y hy]
    ring
  rw [condMean, h1, h2, h3, mul_comm, mul_div_assoc, div_self (ne_of_gt hSpos),
    mul_one]

theorem exists_cylinder_condDensity (w : List ℕ) (hw : ∀ q ∈ w, 0 < q)
    (hpos : 0 < (gaussMeasure (gaussHalfOpenPrefixCylinder w)).toReal) :
    ∃ a b : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧
      IsCondDensity (gaussHalfOpenPrefixCylinder w) w.length (kwonDensity a b) := by
  obtain ⟨a, b, ha, hb, hid⟩ := cylinder_transfer_eq_kwonDensity w hw
  exact ⟨a, b, ha, hb, isCondDensity_of_transfer_eq
    (measurableSet_gaussHalfOpenPrefixCylinder w) hpos hid⟩

/-- **Lemma 3.2** (conditional multi-block mixing, display (17)), with the
constants `A₀ = 8`, `K₀ = 24`, `ρ = 527/540` and `C_s = s` **uniform in the
cylinder `I_w`**, the uniformity is exactly what §4 needs. -/
theorem lemma_3_2 (w : List ℕ) (hw : ∀ q ∈ w, 0 < q)
    (hpos : 0 < (gaussMeasure (gaussHalfOpenPrefixCylinder w)).toReal)
    (A K : ℝ) (hAA : 8 ≤ A) (hKK : 24 ≤ K) (M : ℕ)
    (blocks : List (ℕ × (ℝ → ℝ)))
    (hM : ∀ p ∈ blocks, Measurable p.2)
    (h0 : ∀ p ∈ blocks, GaussUnitNonnegative p.2)
    (hAb : ∀ p ∈ blocks, GaussUnitUpperBound A p.2)
    (hKb : ∀ p ∈ blocks, GaussUnitLipschitzBound K p.2)
    (hgap : ∀ p ∈ blocks, M ≤ p.1) :
    |condMean (gaussHalfOpenPrefixCylinder w)
        (fun α => blockProduct blocks (gaussOrbit w.length α)) - blockMean blocks|
      ≤ (blocks.length : ℝ) *
          ((527 / 540 : ℝ) ^ M * K * A ^ blocks.length) := by
  obtain ⟨a, b, ha, hb, hrep⟩ := exists_cylinder_condDensity w hw hpos
  exact conditional_multiblock_mixing (by linarith) M
    (measurable_kwonDensity a b) (kwonDensity_nonneg ha hb)
    (gaussUnitUpperBound_mono (kwonDensity_le ha hb) hAA)
    (gaussUnitLipschitzBound_mono (kwonDensity_lipschitz ha hb) hKK)
    (kwonDensity_integral_eq_one ha hb) hrep blocks hM h0 hAb hKb hgap

/-! ## 7. Findings about the manuscript

**(a) BV versus Lipschitz, a real gap, not a cosmetic one.**  Kwon states
Lemma 3.1(i) and Lemma 3.2 for `f, g_i ∈ BV(0,1)`.  Wang's Lasota-Yorke
contraction (`gaussTransfer_strict_lipschitz_contraction`, coefficient
`527/540`) is proved for the *Lipschitz* seminorm on `[0,1]`, and every
result above inherits that class.  This is not merely a weaker hypothesis
class: at manuscript lines 334 and 369, §4 applies Lemma 3.2 to *digit
functions*, indicators of first-digit cylinders, which are BV but not
Lipschitz.  So `lemma_3_2` as proved here does **not** cover §4's actual use.
Two honest ways to close it: extend the substrate's contraction to BV
(genuine work: the Lasota-Yorke inequality `Var(L²f) ≤ ρ₀ Var f + C‖f‖₁` plus
Helly compactness, which Wang does not formalize), or route §4's digit-event
applications through Wang's `ψ`-mixing chain
(`gaussDigitPsiMixing_exponential`,
`gaussMeasureReal_iInter_oneDigitEvents_factorization_error_le`), which does
handle one-digit indicators, but only *unconditionally*, not conditioned on
a depth-`d` cylinder.  The conditional-on-a-cylinder version at BV generality
is exactly what is missing from both sources.

**(b) Shape of the constant.**  Kwon's (17) reads `C_s ρ^M ∏ ‖g_i‖_BV`.  Our
bound is `s · ρ^M · K · A^s`, i.e. `C_s = s`, `ρ = 527/540`, and one extra
norm factor `K` beyond the `s` factors `A^s`.  The extra factor is the
Lipschitz constant of the conditional density, which Kwon absorbs into `C_s`
via `sup_w ‖ρ_w‖_BV < ∞`; here that supremum is the explicit pair `(8, 24)`
(`kwonDensity_le`, `kwonDensity_lipschitz`), so the two forms agree after
renaming constants.

**(c) Display (14) is correct and is the only sorried input.**  Kwon's
`ρ_w(y) = q_d(q_d+q_{d-1})/(q_d+q_{d-1}y)²` is the *Lebesgue* conditional
density.  Against the Gauss measure it becomes
`c_w (1+y)/((1+ay)(1+by))` with `a = q_{d-1}/q_d`,
`b = (q_{d-1}+p_{d-1})/(q_d+p_d)`, both in `[0,1]`; this is `kwonDensity`.
Sanity checks are recorded in §5.  Every bound Kwon asserts about this family
is proved above; only the change-of-variables identification
(`cylinder_transfer_eq_kwonDensity`) is sorried. -/

end

end Kwon1002.Transfer
