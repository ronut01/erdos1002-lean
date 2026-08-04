import Kwon1002.GaussBasics
import Erdos1002.GaussDigitQuasiBernoulli
import Erdos1002.GaussLebesgueTransfer

/-!
# §3, Lemma 3.1(ii), unconditional form, display (15)

Target: `Kwon1002.digit_tail_product` of `Kwon1002/GaussEstimates.lean`,
reproduced verbatim here as `digit_tail_product` and proved.

The argument follows the manuscript: `{a₁ ≥ A} = (0, 1/A]` up to endpoints
gives the one-level Gauss tail `ν_G(a₁ ≥ A) ≤ 2/A`, and the substrate's
uniform (quasi-Bernoulli) bounded-distortion bound

  `ν_G(E ∩ T⁻¹B) ≤ 6 · ν_G(E) · ν_G(B)`     (`E` a one-digit event)

iterates it across distinct levels. Peeling the *smallest* level and using
`ν_G ∘ T⁻¹ = ν_G` turns the multi-level event into a one-digit event
intersected with a `T`-preimage, which is exactly the substrate's shape.
Finally `dLeb/dν_G = log 2 · (1+x) ≤ 2` on `(0,1]` transfers the Gauss bound
back to Lebesgue measure.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Kwon1002

noncomputable section

/-! ## Digits: level shift, measurability -/

/-- Our level-0 digit is the substrate's first digit. -/
lemma digit_zero_eq (x : ℝ) : digit x 0 = Erdos1002.gaussFirstDigitNat x := rfl

lemma gaussIter_succ' (x : ℝ) (j : ℕ) :
    gaussIter x (j + 1) = gaussIter (Erdos1002.gaussMap x) j :=
  Function.iterate_succ_apply gaussMap j x

/-- Shifting the level by one is applying the Gauss map. -/
lemma digit_succ' (x : ℝ) (j : ℕ) :
    digit x (j + 1) = digit (Erdos1002.gaussMap x) j := by
  unfold digit
  rw [gaussIter_succ']

lemma measurable_digit_real (j : ℕ) :
    Measurable (fun x : ℝ => (digit x j : ℝ)) := by
  have h1 : Measurable (fun x : ℝ => gaussIter x j) :=
    Erdos1002.measurable_gaussMap.iterate j
  have h2 : Measurable (fun x : ℝ => ⌊(gaussIter x j)⁻¹⌋) := h1.inv.floor
  exact (measurable_of_countable (fun n : ℤ => (n.toNat : ℝ))).comp h2

/-! ## The multi-level digit event -/

/-- `{x : a_{j+1}(x) ≥ f j for every level j ∈ J}`. -/
def digitEvent (f : ℕ → ℝ) (J : Finset ℕ) : Set ℝ :=
  {x : ℝ | ∀ j ∈ J, f j ≤ (digit x j : ℝ)}

lemma measurableSet_digitEvent (f : ℕ → ℝ) (J : Finset ℕ) :
    MeasurableSet (digitEvent f J) := by
  have h : digitEvent f J = ⋂ j ∈ (J : Set ℕ), {x : ℝ | f j ≤ (digit x j : ℝ)} := by
    ext x; simp [digitEvent]
  rw [h]
  exact MeasurableSet.biInter J.countable_toSet
    (fun j _ => measurableSet_le measurable_const (measurable_digit_real j))

/-! ## One level: the Gauss digit tail `≤ 2/c` -/

lemma gaussMeasure_firstDigit_ge_le {c : ℝ} (hc : 1 ≤ c) :
    Erdos1002.gaussMeasure
        (Ioc (0 : ℝ) 1 ∩ Erdos1002.gaussFirstDigitNat ⁻¹' {m : ℕ | c ≤ (m : ℝ)})
      ≤ ENNReal.ofReal (2 * c⁻¹) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hcinv_pos : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc0
  have hcinv_le : c⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact hc
  -- the event sits inside `(0, 1/c]`
  have hsub :
      Ioc (0 : ℝ) 1 ∩ Erdos1002.gaussFirstDigitNat ⁻¹' {m : ℕ | c ≤ (m : ℝ)}
        ⊆ Ioc (0 : ℝ) c⁻¹ := by
    rintro x ⟨hx, hdx⟩
    have hdx' : c ≤ ((Erdos1002.gaussFirstDigitNat x : ℕ) : ℝ) := hdx
    have hnat : 1 ≤ Erdos1002.gaussFirstDigitNat x := by
      by_contra hcon
      have h0 : Erdos1002.gaussFirstDigitNat x = 0 := by omega
      rw [h0] at hdx'
      simp at hdx'
      linarith
    have hint : (1 : ℤ) ≤ ⌊x⁻¹⌋ := by
      have : Erdos1002.gaussFirstDigitNat x = (⌊x⁻¹⌋).toNat := rfl
      omega
    have hcast : ((Erdos1002.gaussFirstDigitNat x : ℕ) : ℝ) = ((⌊x⁻¹⌋ : ℤ) : ℝ) := by
      have h : ((Erdos1002.gaussFirstDigitNat x : ℕ) : ℤ) = ⌊x⁻¹⌋ := by
        have : Erdos1002.gaussFirstDigitNat x = (⌊x⁻¹⌋).toNat := rfl
        omega
      exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) h
    have hle : c ≤ x⁻¹ := by
      rw [hcast] at hdx'
      exact hdx'.trans (Int.floor_le _)
    exact ⟨hx.1, (le_inv_comm₀ hc0 hx.1).mp hle⟩
  refine le_trans (measure_mono hsub) ?_
  have hfin : Erdos1002.gaussMeasure (Ioc (0 : ℝ) c⁻¹) ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  have hval : (Erdos1002.gaussMeasure (Ioc (0 : ℝ) c⁻¹)).toReal
      = (Real.log (1 + c⁻¹) - Real.log (1 + 0)) / Real.log 2 :=
    Erdos1002.gaussMeasure_real_Ioc le_rfl hcinv_pos.le hcinv_le
  rw [hval]
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogle : Real.log (1 + c⁻¹) ≤ c⁻¹ := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + c⁻¹)
    linarith
  rw [show (1 : ℝ) + 0 = 1 by ring, Real.log_one, sub_zero,
    div_le_iff₀ (by linarith : (0 : ℝ) < Real.log 2)]
  nlinarith [hcinv_pos]

/-! ## The induction: peeling the smallest level -/

lemma gaussMeasure_preimage (A : Set ℝ) (hA : MeasurableSet A) :
    Erdos1002.gaussMeasure (Erdos1002.gaussMap ⁻¹' A)
      = Erdos1002.gaussMeasure A := by
  conv_rhs => rw [← Erdos1002.map_gaussMap_gaussMeasure]
  rw [Measure.map_apply Erdos1002.measurable_gaussMap hA]

lemma gaussMeasure_compl_unit : Erdos1002.gaussMeasure ((Ioc (0 : ℝ) 1)ᶜ) = 0 := by
  rw [measure_compl measurableSet_Ioc (measure_ne_top _ _), Erdos1002.gaussMeasure_unit,
    measure_univ, tsub_self]

/-- Main estimate, in Gauss measure: over any finite set of levels below `n`,
the digit-threshold event has measure at most `∏ 12/f j`. -/
lemma gaussMeasure_digitEvent_le :
    ∀ (n : ℕ) (J : Finset ℕ) (f : ℕ → ℝ), (∀ j ∈ J, j < n) → (∀ j, 1 ≤ f j) →
      Erdos1002.gaussMeasure (digitEvent f J)
        ≤ ∏ j ∈ J, ENNReal.ofReal (12 * (f j)⁻¹) := by
  intro n
  induction n with
  | zero =>
    intro J f hJ _
    have hempty : J = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun j hj => ?_)
      exact absurd (hJ j hj) (by omega)
    subst hempty
    have huniv : digitEvent f ∅ = univ := by ext x; simp [digitEvent]
    rw [huniv, Finset.prod_empty, measure_univ]
  | succ n ih =>
    intro J f hJ hf
    set J₁ : Finset ℕ := (J.erase 0).image (fun j => j - 1) with hJ₁def
    set f₁ : ℕ → ℝ := fun k => f (k + 1) with hf₁def
    set B : Set ℝ := digitEvent f₁ J₁ with hBdef
    have hBM : MeasurableSet B := measurableSet_digitEvent _ _
    have hJ₁lt : ∀ k ∈ J₁, k < n := by
      intro k hk
      rw [hJ₁def, Finset.mem_image] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      have hjJ : j ∈ J := Finset.mem_of_mem_erase hj
      have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
      have := hJ j hjJ
      omega
    have hIH := ih J₁ f₁ hJ₁lt (fun k => hf (k + 1))
    -- the shift identity
    have hshift : digitEvent f (J.erase 0) = Erdos1002.gaussMap ⁻¹' B := by
      ext x
      simp only [hBdef, digitEvent, mem_setOf_eq, mem_preimage, hJ₁def, hf₁def,
        Finset.mem_image]
      constructor
      · rintro h k ⟨j, hj, rfl⟩
        have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
        have hjj : j - 1 + 1 = j := by omega
        rw [← digit_succ' x (j - 1), hjj]
        exact h j hj
      · intro h j hj
        have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
        have hjj : j - 1 + 1 = j := by omega
        have hmem : ∃ a ∈ J.erase 0, a - 1 = j - 1 := ⟨j, hj, rfl⟩
        have := h (j - 1) hmem
        rw [← digit_succ' x (j - 1), hjj] at this
        exact this
    -- the product over shifted levels
    have hprodshift : ∏ k ∈ J₁, ENNReal.ofReal (12 * (f₁ k)⁻¹)
        = ∏ j ∈ J.erase 0, ENNReal.ofReal (12 * (f j)⁻¹) := by
      rw [hJ₁def, Finset.prod_image ?inj]
      case inj =>
        intro a ha b hb hab
        have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
        have hb0 : b ≠ 0 := Finset.ne_of_mem_erase hb
        have hab' : a - 1 = b - 1 := hab
        omega
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
      have hjj : j - 1 + 1 = j := by omega
      rw [hf₁def]
      simp only [hjj]
    by_cases h0 : (0 : ℕ) ∈ J
    · -- peel level 0
      set digits : Set ℕ := {m : ℕ | f 0 ≤ (m : ℝ)} with hdigitsdef
      set G : Set ℝ := Ioc (0 : ℝ) 1 ∩ Erdos1002.gaussFirstDigitNat ⁻¹' digits with hGdef
      have hsub : digitEvent f J ⊆ (G ∩ Erdos1002.gaussMap ⁻¹' B) ∪ (Ioc (0 : ℝ) 1)ᶜ := by
        intro x hx
        by_cases hxu : x ∈ Ioc (0 : ℝ) 1
        · left
          refine ⟨⟨hxu, ?_⟩, ?_⟩
          · show f 0 ≤ ((Erdos1002.gaussFirstDigitNat x : ℕ) : ℝ)
            exact hx 0 h0
          · have hx' : x ∈ digitEvent f (J.erase 0) :=
              fun j hj => hx j (Finset.mem_of_mem_erase hj)
            rw [hshift] at hx'
            exact hx'
        · right; exact hxu
      have hGle : Erdos1002.gaussMeasure G ≤ ENNReal.ofReal (2 * (f 0)⁻¹) :=
        gaussMeasure_firstDigit_ge_le (hf 0)
      calc Erdos1002.gaussMeasure (digitEvent f J)
          ≤ Erdos1002.gaussMeasure
              ((G ∩ Erdos1002.gaussMap ⁻¹' B) ∪ (Ioc (0 : ℝ) 1)ᶜ) := measure_mono hsub
        _ ≤ Erdos1002.gaussMeasure (G ∩ Erdos1002.gaussMap ⁻¹' B)
              + Erdos1002.gaussMeasure ((Ioc (0 : ℝ) 1)ᶜ) := measure_union_le _ _
        _ = Erdos1002.gaussMeasure (G ∩ Erdos1002.gaussMap ⁻¹' B) := by
              rw [gaussMeasure_compl_unit, add_zero]
        _ ≤ 6 * Erdos1002.gaussMeasure G * Erdos1002.gaussMeasure B :=
              Erdos1002.gaussMeasure_oneDigitEvent_inter_preimage_le digits hBM
        _ ≤ 6 * ENNReal.ofReal (2 * (f 0)⁻¹)
              * ∏ k ∈ J₁, ENNReal.ofReal (12 * (f₁ k)⁻¹) :=
              mul_le_mul' (mul_le_mul' le_rfl hGle) hIH
        _ = ENNReal.ofReal (12 * (f 0)⁻¹)
              * ∏ j ∈ J.erase 0, ENNReal.ofReal (12 * (f j)⁻¹) := by
              rw [hprodshift]
              congr 1
              rw [show (6 : ℝ≥0∞) = ENNReal.ofReal 6 by simp,
                ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
              congr 1
              ring
        _ = ∏ j ∈ J, ENNReal.ofReal (12 * (f j)⁻¹) :=
              Finset.mul_prod_erase J (fun j => ENNReal.ofReal (12 * (f j)⁻¹)) h0
    · -- level 0 absent: pure shift
      have herase : J.erase 0 = J := Finset.erase_eq_of_notMem h0
      have heq : digitEvent f J = Erdos1002.gaussMap ⁻¹' B := by
        rw [← herase]; exact hshift
      rw [heq, gaussMeasure_preimage B hBM, hBdef]
      calc Erdos1002.gaussMeasure (digitEvent f₁ J₁)
          ≤ ∏ k ∈ J₁, ENNReal.ofReal (12 * (f₁ k)⁻¹) := hIH
        _ = ∏ j ∈ J.erase 0, ENNReal.ofReal (12 * (f j)⁻¹) := hprodshift
        _ = ∏ j ∈ J, ENNReal.ofReal (12 * (f j)⁻¹) := by rw [herase]

/-! ## Lebesgue transfer and the target -/

/-- **Lemma 3.1(ii)**, in the unconditional form (15) the proof consumes:
for distinct levels, the joint probability that the digits exceed
thresholds `A i` factorizes up to a constant per level. -/
theorem digit_tail_product :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℕ) (js : Fin s → ℕ) (A : Fin s → ℝ),
      Function.Injective js → (∀ i, 1 ≤ A i) →
      (MeasureTheory.volume {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∀ i, A i ≤ (digit α (js i) : ℝ)}).toReal
        ≤ C ^ s * ∏ i, (A i)⁻¹ := by
  refine ⟨24, by norm_num, ?_⟩
  intro s js A hinj hA
  have hApos : ∀ i, (0 : ℝ) < A i := fun i => lt_of_lt_of_le zero_lt_one (hA i)
  have hprodnn : (0 : ℝ) ≤ ∏ i, (A i)⁻¹ :=
    Finset.prod_nonneg (fun i _ => (inv_pos.mpr (hApos i)).le)
  set S : Set ℝ := {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i, A i ≤ (digit α (js i) : ℝ)} with hSdef
  rcases Nat.eq_zero_or_pos s with hs | hs
  · -- no constraints: the ambient interval already has measure 1
    subst hs
    have hsub : S ⊆ Ioo (0 : ℝ) 1 := fun x hx => hx.1
    have : volume S ≤ 1 := by
      refine le_trans (measure_mono hsub) ?_
      rw [Real.volume_Ioo]
      simp
    calc (volume S).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono (by simp) this
      _ = 1 := by simp
      _ ≤ (24 : ℝ) ^ 0 * ∏ i : Fin 0, (A i)⁻¹ := by simp
  -- the general case
  set J : Finset ℕ := Finset.image js Finset.univ with hJdef
  set f : ℕ → ℝ := Function.extend js A (fun _ => 1) with hfdef
  have hfjs : ∀ i, f (js i) = A i := fun i => hinj.extend_apply A (fun _ => 1) i
  have hf1 : ∀ j, 1 ≤ f j := by
    intro j
    by_cases h : ∃ i, js i = j
    · obtain ⟨i, rfl⟩ := h
      rw [hfjs i]; exact hA i
    · rw [hfdef, Function.extend_apply' _ _ _ h]
  set E : Set ℝ := Ioc (0 : ℝ) 1 ∩ digitEvent f J with hEdef
  have hEM : MeasurableSet E := measurableSet_Ioc.inter (measurableSet_digitEvent _ _)
  have hEsub : E ⊆ Ioc (0 : ℝ) 1 := inter_subset_left
  have hSE : S ⊆ E := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨⟨hx1.1, hx1.2.le⟩, ?_⟩
    intro j hj
    rw [hJdef, Finset.mem_image] at hj
    obtain ⟨i, -, rfl⟩ := hj
    rw [hfjs i]
    exact hx2 i
  -- Gauss bound for `E`
  have hgauss : Erdos1002.gaussMeasure E ≤ ∏ j ∈ J, ENNReal.ofReal (12 * (f j)⁻¹) := by
    refine le_trans (measure_mono inter_subset_right) ?_
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ j ∈ J, j < n := by
      refine ⟨(J.sup id) + 1, fun j hj => ?_⟩
      have h := Finset.le_sup (f := id) hj
      simp only [id_eq] at h
      omega
    exact gaussMeasure_digitEvent_le n J f hn hf1
  -- transfer Gauss → Lebesgue on the unit interval
  have hae : ∀ᵐ x ∂(Erdos1002.gaussMeasure.restrict E),
      Erdos1002.lebesgueOverGaussDensity x ≤ 2 := by
    refine (ae_restrict_iff' hEM).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
    have hx1 : x ∈ Icc (0 : ℝ) 1 := ⟨(hEsub hx).1.le, (hEsub hx).2⟩
    have hb := (Erdos1002.lebesgueOverGaussDensityReal_bounds hx1).2
    have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    calc Erdos1002.lebesgueOverGaussDensity x
        = ENNReal.ofReal (Erdos1002.lebesgueOverGaussDensityReal x) := rfl
      _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by linarith)
      _ = 2 := by simp
  have hleb : volume E ≤ 2 * Erdos1002.gaussMeasure E := by
    have h1 : volume E = (volume.restrict (Ioc (0 : ℝ) 1)) E := by
      rw [Measure.restrict_apply hEM, inter_eq_self_of_subset_left hEsub]
    rw [h1, ← Erdos1002.gaussMeasure_withDensity_lebesgueOverGaussDensity,
      withDensity_apply _ hEM]
    calc ∫⁻ x in E, Erdos1002.lebesgueOverGaussDensity x ∂Erdos1002.gaussMeasure
        ≤ ∫⁻ _ in E, 2 ∂Erdos1002.gaussMeasure := lintegral_mono_ae hae
      _ = 2 * Erdos1002.gaussMeasure E := setLIntegral_const _ _
  -- assemble
  have hprodJ : ∏ j ∈ J, ENNReal.ofReal (12 * (f j)⁻¹)
      = ∏ i, ENNReal.ofReal (12 * (A i)⁻¹) := by
    rw [hJdef, Finset.prod_image (fun a _ b _ hab => hinj hab)]
    exact Finset.prod_congr rfl (fun i _ => by rw [hfjs i])
  have hprodReal : ∏ i, ENNReal.ofReal (12 * (A i)⁻¹)
      = ENNReal.ofReal (12 ^ s * ∏ i, (A i)⁻¹) := by
    rw [← ENNReal.ofReal_prod_of_nonneg
      (fun i _ => by have := hApos i; positivity), Finset.prod_mul_distrib,
      Finset.prod_const]
    simp
  have hfinal : volume S ≤ ENNReal.ofReal (2 * (12 ^ s * ∏ i, (A i)⁻¹)) := by
    calc volume S ≤ volume E := measure_mono hSE
      _ ≤ 2 * Erdos1002.gaussMeasure E := hleb
      _ ≤ 2 * ∏ j ∈ J, ENNReal.ofReal (12 * (f j)⁻¹) := by
            exact mul_le_mul' le_rfl hgauss
      _ = 2 * ENNReal.ofReal (12 ^ s * ∏ i, (A i)⁻¹) := by rw [hprodJ, hprodReal]
      _ = ENNReal.ofReal (2 * (12 ^ s * ∏ i, (A i)⁻¹)) := by
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
              ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have htoReal : (volume S).toReal ≤ 2 * (12 ^ s * ∏ i, (A i)⁻¹) := by
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hfinal) ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
  refine le_trans htoReal ?_
  have h2 : (2 : ℝ) ≤ 2 ^ s := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) hs
  have hpow : (2 : ℝ) * 12 ^ s ≤ 24 ^ s := by
    have h12 : (0 : ℝ) < 12 ^ s := by positivity
    calc (2 : ℝ) * 12 ^ s ≤ 2 ^ s * 12 ^ s := by nlinarith
      _ = 24 ^ s := by rw [← mul_pow]; norm_num
  calc 2 * (12 ^ s * ∏ i, (A i)⁻¹) = (2 * 12 ^ s) * ∏ i, (A i)⁻¹ := by ring
    _ ≤ 24 ^ s * ∏ i, (A i)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hpow hprodnn

end

end Kwon1002
