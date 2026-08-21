import Kwon1002.P42Later

/-!
# P42Super: the super-resonance branch of case 3 of Proposition 4.2

"If `k > t₀ + 100H`", the remaining branch of case 3 of the manuscript's
proof of Proposition 4.2 (v9, lines ≈ 798-833).  The earlier mode
`(r₁,s₁)` is nonzero and the later mode is zero, and the later block sits
*above* the descendant cut `t₋` of the earlier index, so the two-block
amplitude is no longer measurable before `t₋` and the sub-resonance route of
`Kwon1002/P42Later.lean` does not apply.  The manuscript's extra step is
carried out here:

* **§1** the earlier monomial alone is `oscillatory_prefix_bound` at the
  degenerate pair `(j, j)` — the zero mode at the same depth and word is
  idempotent (`monoAt_mul_self_zeroMode`), so no new engine is needed;
* **§2** the later zero-mode block is the shifted digit-cylinder observable
  `PhaseBounds.cylObs` (`monoAt_zeroMode_eq_cylObs`);
* **§3** on each retained depth-`t₊` cylinder the earlier phase is frozen
  (`NonzeroMode.phase_freeze_on_cylinder`) at the margin
  `q_{t₊}² ≥ e^{γ₊H/2}·n|Q_j|` of
  `PhaseBounds.ascended_descendant_bound_at_cut`, the later block is
  replaced by its stationary Gauss mean
  (`StationaryReplace.leb_halfOpen_multiblock_mixing`, block gap from
  `P42Cases.mixingGap_ground`), and the discarded depth-`t₊` cylinders are
  restored, giving `mean_replacement_bound`;
* **§4** the two are combined and wrapped in `∀ᶠ n`, giving
  `earlierMode_superResonance_bound'`, token-identical to the residual of
  `Kwon1002/Prop42Unconditional.lean`.
-/

open MeasureTheory Set Filter

open scoped BigOperators Topology ENNReal

namespace Kwon1002

namespace P42Super

open RetainedCut StationaryReplace CylinderSum P42Later

noncomputable section

/-! ## 1. The earlier monomial alone -/

/-- The zero mode at the same depth and the same word is idempotent against
a monomial: `μ_{w,r,s}(j)·μ_{w,0,0}(j) = μ_{w,r,s}(j)`.  This is what lets
the single-monomial integral be read as a *pair* integral at the degenerate
pair `(j, j)`, and so be estimated by the engine of `P42Later`. -/
lemma monoAt_mul_self_zeroMode (R : ℕ) (w : Fin (2 * R) → ℕ) (r s : ℤ) (α : ℝ)
    (n j : ℕ) :
    Prop42.monoAt R w r s α n j * Prop42.monoAt R w 0 0 α n j
      = Prop42.monoAt R w r s α n j := by
  have hz : Prop42.monoAt R w 0 0 α n j
      = (if windowWord R α j = w then (1 : ℂ) else 0) := by
    unfold Prop42.monoAt
    norm_num [P42Cases.torusChar_zero]
  rw [hz]
  unfold Prop42.monoAt
  by_cases h : windowWord R α j = w
  · rw [if_pos h]; ring
  · rw [if_neg h]; ring

/-- **The earlier monomial alone**, at a fixed `n`.  The combined frequency
of the degenerate pair `(j, j)` with the zero mode is `±Q_j(r,s)`, so
`hdom` is free and `P42Later.oscillatory_prefix_bound` applies verbatim at
prefix depth `j + R` and descendant depth `t₋ = ⌊(m_n+j)/2 − 40H⌋`. -/
theorem oscillatory_single_bound {n : ℕ} (hn1 : 1 ≤ n) {R j : ℕ}
    (hjb : j ∈ bulkJ n) (hj1 : 1 ≤ j) (hRj : R ≤ j)
    (w : Fin (2 * R) → ℕ) {r s : ℤ}
    (hdt : j + R < (Prop41.kMinus n j).toNat)
    {C₀ c₀ : ℝ}
    (h20 : ∀ i : ℕ, i ≤ 2 * mIndex n →
      volume.real {α ∈ Ioo (0 : ℝ) 1 |
          ¬ (Real.exp (lyapunov * (i : ℝ) - 1 * Hscale n) ≤ (denom α i : ℝ)
              ∧ (denom α i : ℝ) ≤ Real.exp (lyapunov * (i : ℝ) + 1 * Hscale n))}
        ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)))
    {Cac : ℝ}
    (hac : (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧
        |(s : ℝ) * (denom α j : ℝ) - (r : ℝ) * (denom α (j - 1) : ℝ)|
          < Real.exp (-Hscale n) * (denom α j : ℝ)}).toReal ≤ Cac) :
    ‖∫ α in Ioo (0 : ℝ) 1, Prop42.monoAt R w r s α n j‖
      ≤ 3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) + Cac
          + 28 * Real.exp (-Hscale n) := by
  have hdom : ∀ u : List ℕ, u.length = (Prop41.kMinus n j).toNat → (∀ x ∈ u, 0 < x) →
      ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder u, Irrational α →
      Real.exp (-Hscale n) * (denom α j : ℝ) ≤ |((Qfreq α j r s : ℤ) : ℝ)| →
      (1 / 2) * Real.exp (-Hscale n) * (denom α j : ℝ)
        ≤ |((PhaseBounds.Qpair α j j r s 0 0 : ℤ) : ℝ)| := by
    intro u _ _ α _ _ hlow
    have hz : Qfreq α j (0 : ℤ) (0 : ℤ) = 0 := by unfold Qfreq; ring
    have hQ : PhaseBounds.Qpair α j j r s 0 0 = (-1) ^ j * Qfreq α j r s := by
      unfold PhaseBounds.Qpair
      rw [hz]
      ring
    rw [hQ]
    push_cast
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hq0 : (0 : ℝ) ≤ (denom α j : ℝ) := Nat.cast_nonneg _
    have hexp : (0 : ℝ) < Real.exp (-Hscale n) := Real.exp_pos _
    nlinarith
  have h := P42Later.oscillatory_prefix_bound hn1 hjb hj1 hRj (le_refl j)
    (Nat.le_add_right j R) w w hdt hdom (C₀ := C₀) (c₀ := c₀) h20 (Cac := Cac) hac
  simpa only [monoAt_mul_self_zeroMode] using h

/-! ## 2. The later zero-mode block as a shifted digit observable -/

/-- The zero-mode monomial at depth `k` is the indicator of the depth-`2R`
digit cylinder of `w'`, read along the orbit at time `k - R`. -/
lemma monoAt_zeroMode_eq_cylObs {R k : ℕ} (hRk : R ≤ k) (w' : Fin (2 * R) → ℕ)
    (α : ℝ) (n : ℕ) :
    Prop42.monoAt R w' 0 0 α n k
      = ((PhaseBounds.cylObs R w' (gaussIter α (k - R)) : ℝ) : ℂ) := by
  classical
  rw [PhaseBounds.cylObs_windowWord R k hRk w' α]
  unfold Prop42.monoAt
  rw [Set.indicator_apply]
  by_cases h : α ∈ P42Cases.cyl R w' k
  · have h' : windowWord R α k = w' := h
    rw [if_pos h', if_pos h]
    norm_num [P42Cases.torusChar_zero]
  · have h' : ¬ windowWord R α k = w' := h
    rw [if_neg h', if_neg h]
    norm_num

/-! ## 3. Freezing the earlier phase and replacing the later block -/

set_option maxHeartbeats 1600000 in
/-- **The mean replacement, at a fixed `n`.**  On the retained depth-`t₊`
cylinders the earlier phase is frozen (`NonzeroMode.phase_freeze_on_cylinder`
at the margin `hasc`, which is
`PhaseBounds.ascended_descendant_bound_at_cut`), the later zero-mode block is
replaced by its stationary Gauss mean (`hmix`, which is
`StationaryReplace.leb_halfOpen_multiblock_mixing 1`), and the discarded
cylinders are restored on both sides.  What is left of the two-block
amplitude is the earlier amplitude alone, times a constant of modulus at
most one. -/
theorem mean_replacement_bound {n R j k : ℕ} {r s : ℤ}
    (hj1 : 1 ≤ j) (hRj : R ≤ j) (hRk : R ≤ k)
    (w w' : Fin (2 * R) → ℕ)
    {C₀ c₀ : ℝ}
    (h20 : ∀ i : ℕ, i ≤ 2 * mIndex n →
      volume.real {α ∈ Ioo (0 : ℝ) 1 |
          ¬ (Real.exp (lyapunov * (i : ℝ) - 1 * Hscale n) ≤ (denom α i : ℝ)
              ∧ (denom α i : ℝ) ≤ Real.exp (lyapunov * (i : ℝ) + 1 * Hscale n))}
        ≤ C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)))
    {Kc gam : ℝ}
    (hmode : |(r : ℝ)| + |(s : ℝ)| ≤ Kc)
    (hasc : ∀ qt qj Q nn : ℝ, 0 ≤ Q →
      Real.exp (lyapunov * (((Prop41.kPlus n j).toNat : ℕ) : ℝ) - 1 * Hscale n) ≤ qt →
      qj ≤ Real.exp (lyapunov * (j : ℝ) + 1 * Hscale n) →
      Q ≤ Kc * qj → nn ≤ Real.exp (Lnorm n) →
      Real.exp (gam * Hscale n) * (nn * Q) ≤ qt ^ 2)
    (hnn : (n : ℝ) ≤ Real.exp (Lnorm n))
    (hjRkp : j + R ≤ (Prop41.kPlus n j).toNat)
    (hkp0 : 0 < (Prop41.kPlus n j).toNat)
    (hkp2m : (Prop41.kPlus n j).toNat ≤ 2 * mIndex n)
    (hDel : Real.exp (2 * Hscale n
        - 2 * lyapunov * (((Prop41.kPlus n j).toNat : ℕ) : ℝ)) ≤ Real.exp (-Hscale n))
    {Cmix ρmix : ℝ} {M : ℕ} (hCmix : 0 < Cmix) (hρmix : 0 < ρmix)
    (hmix : ∀ (d Mm : ℕ) (u : List ℕ), u.length = d → (∀ a ∈ u, 0 < a) → 0 < d →
      ∀ Δ : ℝ,
      (∀ x ∈ Erdos1002.gaussHalfOpenPrefixCylinder u,
        ∀ y ∈ Erdos1002.gaussHalfOpenPrefixCylinder u,
          Irrational x → Irrational y → |x - y| ≤ Δ) →
      ∀ (t : ℕ → ℕ) (gg : ℕ → ℝ → ℝ) (K : ℝ), 0 ≤ K →
        (∀ i, i < 1 → Prop41.BVBoundedBy K (gg i)) →
        (∀ i, i < 1 → Measurable (gg i)) →
        d + Mm ≤ t 0 → (∀ i, i + 1 < 1 → t i + Mm ≤ t (i + 1)) →
        |(∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u,
              ∏ i ∈ Finset.range 1, gg i (gaussIter α (t i)))
            - (volume (Erdos1002.gaussHalfOpenPrefixCylinder u)).toReal
                * ∏ i ∈ Finset.range 1, ∫ x, gg i x ∂Erdos1002.gaussMeasure|
          ≤ (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder u)).toReal
              * (2 * Real.log 2) * (Cmix * ρmix ^ Mm + Δ) * K ^ 1)
    (hgap : (Prop41.kPlus n j).toNat + M + R ≤ k) :
    ‖∫ α in Ioo (0 : ℝ) 1,
        Prop42.monoAt R w r s α n j * Prop42.monoAt R w' 0 0 α n k‖
      ≤ ‖∫ α in Ioo (0 : ℝ) 1, Prop42.monoAt R w r s α n j‖
        + 6 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)))
        + 4 * Real.pi * Real.exp (-gam * Hscale n)
        + 4 * Real.log 2 * (Cmix * ρmix ^ M + Real.exp (-Hscale n)) := by
  classical
  set H : ℝ := Hscale n with hHdef
  set kp : ℕ := (Prop41.kPlus n j).toNat with hkpdef
  set Δ : ℝ := Real.exp (2 * H - 2 * lyapunov * (kp : ℝ)) with hΔdef
  have hΔ0 : (0 : ℝ) < Δ := Real.exp_pos _
  set W : Finset (List ℕ) := StationaryReplace.retainedWords n j (j + R) kp 1 with hWdef
  have hWshape : ∀ u ∈ W, u.length = kp ∧ ∀ a ∈ u, 0 < a :=
    StationaryReplace.retainedWords_shape
  have hWne : ∀ u ∈ W, u ≠ [] := by
    intro u hu hnil
    have hl := (hWshape u hu).1
    rw [hnil] at hl
    simp at hl
    omega
  set gfun : ℝ → ℂ := fun α => Prop42.monoAt R w r s α n j with hgdef
  set hfun : ℝ → ℂ := fun α => Prop42.monoAt R w' 0 0 α n k with hhdef
  have hgm : Measurable gfun := Prop42.measurable_monoAt R w r s n j
  have hhm : Measurable hfun := Prop42.measurable_monoAt R w' 0 0 n k
  have hg1 : ∀ α, ‖gfun α‖ ≤ 1 := fun α => Prop42.norm_monoAt_le R w r s α n j
  have hh1 : ∀ α, ‖hfun α‖ ≤ 1 := fun α => Prop42.norm_monoAt_le R w' 0 0 α n k
  have hgh1 : ∀ α, ‖gfun α * hfun α‖ ≤ 1 := by
    intro α
    rw [norm_mul]
    nlinarith [hg1 α, hh1 α, norm_nonneg (gfun α), norm_nonneg (hfun α)]
  -- the stationary mean of the later block
  set Preal : ℝ := ∫ x, PhaseBounds.cylObs R w' x ∂Erdos1002.gaussMeasure with hPdef
  have hPval : Preal
      = (Erdos1002.gaussMeasure (Prop41.cylinder (2 * R) (PhaseBounds.wordFn R w'))).toReal :=
    PhaseBounds.integral_cylObs_gauss R w'
  have hP0 : (0 : ℝ) ≤ Preal := by rw [hPval]; exact ENNReal.toReal_nonneg
  have hP1 : |Preal| ≤ 1 := by
    rw [hPval, abs_of_nonneg ENNReal.toReal_nonneg]
    have hsub : Prop41.cylinder (2 * R) (PhaseBounds.wordFn R w') ⊆ Ioo (0 : ℝ) 1 :=
      fun x hx => hx.1
    have hle := measure_mono (μ := Erdos1002.gaussMeasure) hsub
    have hone : (Erdos1002.gaussMeasure (Ioo (0 : ℝ) 1)).toReal = 1 :=
      Prop41Final.gaussMeasure_Ioo_eq_one
    have hfin : Erdos1002.gaussMeasure (Ioo (0 : ℝ) 1) ≠ ⊤ := by
      intro hc
      rw [hc] at hone
      simp at hone
    have hmono := ENNReal.toReal_mono hfin hle
    rw [hone] at hmono
    exact hmono
  -- ### step 1: the complete prefix partition at depth `t₊`, both sides
  have hdisc : (volume (Ioo (0 : ℝ) 1 \
      ⋃ u ∈ W, Erdos1002.gaussHalfOpenPrefixCylinder u)).toReal
      ≤ 3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) := by
    rw [hWdef]
    exact StationaryReplace.volume_discarded_retainedWords_le n h20
      (Nat.le_add_right _ _) hjRkp hkp2m
  have hA1 : ‖(∫ α in Ioo (0 : ℝ) 1, gfun α * hfun α)
        - ∑ u ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, gfun α * hfun α‖
      ≤ 3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) :=
    le_trans (CylinderSum.norm_integral_sub_sum_le hkp0 W hWshape (hgm.mul hhm) hgh1) hdisc
  have hB1 : ‖(∫ α in Ioo (0 : ℝ) 1, gfun α)
        - ∑ u ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, gfun α‖
      ≤ 3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) :=
    le_trans (CylinderSum.norm_integral_sub_sum_le hkp0 W hWshape hgm hg1) hdisc
  -- ### the frozen data on a retained cylinder
  set Qw : List ℕ → ℤ := fun u => QpairWord u j j r s 0 0 with hQwdef
  set Ku : List ℕ → ℝ := fun u => (n : ℝ) * ((Qw u : ℤ) : ℝ) with hKudef
  set cu : List ℕ → ℂ := fun u => if windowOfWord R u j = w then (1 : ℂ) else 0 with hcudef
  have hcu1 : ∀ u, ‖cu u‖ ≤ 1 := by
    intro u
    rw [hcudef]
    by_cases hc : windowOfWord R u j = w <;> simp [hc]
  have hgcyl : ∀ u ∈ W, ∀ α ∈ Erdos1002.gaussHalfOpenPrefixCylinder u, Irrational α →
      gfun α = cu u * torusChar (Ku u * α) := by
    intro u hu α hα hirr
    have hlen := (hWshape u hu).1
    have hpos := (hWshape u hu).2
    have hid := P42Later.integrand_eq_on_cylinder hRj hRj hj1 hj1 hlen hpos
      (by omega) (by omega) w w r s 0 0 n hα hirr
    rw [monoAt_mul_self_zeroMode] at hid
    rw [hgdef]
    simp only at hid ⊢
    rw [hid]
    simp only [and_self]
    congr 1
    rw [hKudef, hQwdef]
    exact (P42Later.torusChar_eq_oscillatoryPhase _ _).symm
  -- ### the uniform diameter of the retained cylinders
  have hdiam : ∀ u ∈ W, ∀ x ∈ Erdos1002.gaussHalfOpenPrefixCylinder u,
      ∀ y ∈ Erdos1002.gaussHalfOpenPrefixCylinder u,
      Irrational x → Irrational y → |x - y| ≤ Δ := by
    intro u hu x hx y hy hix hiy
    have hlen := (hWshape u hu).1
    have hpos := (hWshape u hu).2
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 :=
      ZeroMode.mem_Ioo_of_mem_halfOpen (hWne u hu) hpos hx hix
    have hyIoo : y ∈ Ioo (0 : ℝ) 1 :=
      ZeroMode.mem_Ioo_of_mem_halfOpen (hWne u hu) hpos hy hiy
    have hdig : ∀ i, i < kp → digit x i = digit y i := by
      intro i hi
      have hi' : i < u.length := by rw [hlen]; exact hi
      rw [ZeroMode.digit_eq_of_mem_halfOpen hxIoo hix hx i hi',
        ZeroMode.digit_eq_of_mem_halfOpen hyIoo hiy hy i hi']
    have hqlow : Real.exp (lyapunov * (kp : ℝ) - 1 * H) ≤ (denom x kp : ℝ) := by
      have := StationaryReplace.retainedWords_windows (n := n) (δ := 1) hkp0
        (Nat.le_add_right _ _) hjRkp u hu x hx hix
      exact this.2.2.1
    have hprod := Kwon1002.abs_sub_mul_denom_sq_le_one hxIoo hyIoo hix hiy kp hdig
    have hq0 : (0 : ℝ) < Real.exp (lyapunov * (kp : ℝ) - 1 * H) := Real.exp_pos _
    have hq1 : (0 : ℝ) < (denom x kp : ℝ) := lt_of_lt_of_le hq0 hqlow
    have hsq : Real.exp (lyapunov * (kp : ℝ) - 1 * H) ^ 2 ≤ (denom x kp : ℝ) ^ 2 :=
      pow_le_pow_left₀ hq0.le hqlow 2
    have hsqval : Real.exp (lyapunov * (kp : ℝ) - 1 * H) ^ 2
        = Real.exp (2 * lyapunov * (kp : ℝ) - 2 * H) := by
      rw [sq, ← Real.exp_add]; ring_nf
    have hΔinv : Δ = (Real.exp (2 * lyapunov * (kp : ℝ) - 2 * H))⁻¹ := by
      rw [hΔdef, ← Real.exp_neg]
      congr 1
      ring
    calc |x - y| ≤ 1 / (denom x kp : ℝ) ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          exact hprod
      _ ≤ 1 / Real.exp (2 * lyapunov * (kp : ℝ) - 2 * H) := by
          refine one_div_le_one_div_of_le (by positivity) ?_
          rw [← hsqval]
          exact hsq
      _ = Δ := by rw [hΔinv, one_div]
  -- ### the frozen frequency is small against the diameter
  have hfreq : ∀ u ∈ W, |Ku u| * Δ ≤ Real.exp (-gam * H) := by
    intro u hu
    have hlen := (hWshape u hu).1
    have hpos := (hWshape u hu).2
    obtain ⟨α, hα, hirr⟩ := StationaryReplace.exists_irrational_mem_halfOpen hpos
    have hαIoo : α ∈ Ioo (0 : ℝ) 1 :=
      ZeroMode.mem_Ioo_of_mem_halfOpen (hWne u hu) hpos hα hirr
    have hwin := StationaryReplace.retainedWords_windows (n := n) (δ := 1) hkp0
      (Nat.le_add_right _ _) hjRkp u hu α hα hirr
    have hqjup : (denom α j : ℝ) ≤ Real.exp (lyapunov * (j : ℝ) + 1 * H) := hwin.1.2
    have hzero : QwordAt u j (0 : ℤ) (0 : ℤ) = 0 := by unfold QwordAt; ring
    have hQval : Qw u = (-1) ^ j * QwordAt u j r s := by
      rw [hQwdef]
      show QpairWord u j j r s 0 0 = _
      unfold QpairWord
      rw [hzero]
      ring
    have hQeq : Qfreq α j r s = QwordAt u j r s :=
      P42Later.Qfreq_eq_QwordAt hlen hpos hα hirr hkp0 (by omega) r s
    have habsQ : |((Qw u : ℤ) : ℝ)| = |((Qfreq α j r s : ℤ) : ℝ)| := by
      rw [hQval, hQeq]
      push_cast
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hQle : |((Qw u : ℤ) : ℝ)| ≤ Kc * (denom α j : ℝ) := by
      rw [habsQ]
      refine le_trans (Prop42.abs_Qfreq_le hαIoo hirr j hj1 r s) ?_
      exact mul_le_mul_of_nonneg_right hmode (Nat.cast_nonneg _)
    have hasc' := hasc (Real.exp (lyapunov * (kp : ℝ) - 1 * H))
      (denom α j : ℝ) |((Qw u : ℤ) : ℝ)| (n : ℝ) (abs_nonneg _) (le_refl _)
      hqjup hQle hnn
    have hsqval : Real.exp (lyapunov * (kp : ℝ) - 1 * H) ^ 2
        = Real.exp (2 * lyapunov * (kp : ℝ) - 2 * H) := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [hsqval] at hasc'
    have hKuabs : |Ku u| = (n : ℝ) * |((Qw u : ℤ) : ℝ)| := by
      rw [hKudef]
      simp only
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
    have hinv : Δ * Real.exp (2 * lyapunov * (kp : ℝ) - 2 * H) = 1 := by
      rw [hΔdef, ← Real.exp_add]
      rw [show 2 * H - 2 * lyapunov * (kp : ℝ) + (2 * lyapunov * (kp : ℝ) - 2 * H)
        = 0 by ring, Real.exp_zero]
    have hgexp : Real.exp (gam * H) * Real.exp (-gam * H) = 1 := by
      rw [← Real.exp_add, show gam * H + -gam * H = 0 by ring, Real.exp_zero]
    have hgpos : (0 : ℝ) < Real.exp (gam * H) := Real.exp_pos _
    rw [hKuabs]
    have hmain : Real.exp (gam * H) * ((n : ℝ) * |((Qw u : ℤ) : ℝ)|) * Δ ≤ 1 := by
      calc Real.exp (gam * H) * ((n : ℝ) * |((Qw u : ℤ) : ℝ)|) * Δ
          ≤ Real.exp (2 * lyapunov * (kp : ℝ) - 2 * H) * Δ :=
            mul_le_mul_of_nonneg_right hasc' hΔ0.le
        _ = 1 := by rw [mul_comm]; exact hinv
    have hnq0 : (0 : ℝ) ≤ (n : ℝ) * |((Qw u : ℤ) : ℝ)| :=
      mul_nonneg (Nat.cast_nonneg n) (abs_nonneg _)
    nlinarith [hmain, hgexp, hgpos, hΔ0, hnq0]
  -- ### the per-cylinder estimate
  have hkey : ∀ u ∈ W,
      ‖(∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, gfun α * hfun α)
          - (Preal : ℂ) * ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, gfun α‖
        ≤ 4 * Real.pi * Real.exp (-gam * H)
              * (volume (Erdos1002.gaussHalfOpenPrefixCylinder u)).toReal
          + 4 * Real.log 2 * (Cmix * ρmix ^ M + Real.exp (-H))
              * (Erdos1002.gaussMeasure
                  (Erdos1002.gaussHalfOpenPrefixCylinder u)).toReal := by
    intro u hu
    have hlen := (hWshape u hu).1
    have hpos := (hWshape u hu).2
    have hune := hWne u hu
    obtain ⟨β, hβ, hβirr⟩ := StationaryReplace.exists_irrational_mem_halfOpen hpos
    have hfr1 := NonzeroMode.phase_freeze_on_cylinder hune hpos hfun hhm 1 zero_le_one
      (fun α _ _ => hh1 α) (Ku u) hβ hβirr Δ
      (fun α hα hirr => hdiam u hu α hα β hβ hirr hβirr)
    have hfr2 := NonzeroMode.phase_freeze_on_cylinder hune hpos (fun _ => (1 : ℂ))
      measurable_const 1 zero_le_one (fun α _ _ => by simp) (Ku u) hβ hβirr Δ
      (fun α hα hirr => hdiam u hu α hα β hβ hirr hβirr)
    have hmixu := hmix kp M u hlen hpos hkp0 Δ (hdiam u hu) (fun _ => k - R)
      (fun _ => PhaseBounds.cylObs R w') 2 (by norm_num)
      (fun i _ => PhaseBounds.cylObs_bv R w')
      (fun i _ => PhaseBounds.measurable_cylObs R w')
      (by show kp + M ≤ k - R; omega) (fun i hi => absurd hi (by omega))
    simp only [Finset.prod_range_one, pow_one] at hmixu
    rw [← hPdef] at hmixu
    set S : Set ℝ := Erdos1002.gaussHalfOpenPrefixCylinder u with hSdef
    set V : ℝ := (volume S).toReal with hVdef
    set ν : ℝ := (Erdos1002.gaussMeasure S).toReal with hνdef
    have hV0 : (0 : ℝ) ≤ V := ENNReal.toReal_nonneg
    have hν0 : (0 : ℝ) ≤ ν := ENNReal.toReal_nonneg
    have hSm : MeasurableSet S := Erdos1002.measurableSet_gaussHalfOpenPrefixCylinder u
    set τ : ℂ := torusChar (Ku u * β) with hτdef
    have hτ1 : ‖τ‖ = 1 := Prop42.norm_torusChar _
    -- the two cylinder integrals in frozen form
    have hIA : (∫ α in S, gfun α * hfun α)
        = cu u * ∫ α in S, hfun α * torusChar (Ku u * α) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_ae hSm ?_
      filter_upwards [LargeDeviation.ae_irrational_volume] with α hirr hαS
      rw [hgcyl u hu α hαS hirr]
      ring
    have hIB : (∫ α in S, gfun α) = cu u * ∫ α in S, torusChar (Ku u * α) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_ae hSm ?_
      filter_upwards [LargeDeviation.ae_irrational_volume] with α hirr hαS
      exact hgcyl u hu α hαS hirr
    -- the two phase freezes
    have hfrbd : 2 * Real.pi * |Ku u| * Δ * 1 * V
        ≤ 2 * Real.pi * Real.exp (-gam * H) * V := by
      have h1 : |Ku u| * Δ ≤ Real.exp (-gam * H) := hfreq u hu
      have hc : (0 : ℝ) ≤ 2 * Real.pi * V :=
        mul_nonneg (by positivity) hV0
      calc 2 * Real.pi * |Ku u| * Δ * 1 * V = (2 * Real.pi * V) * (|Ku u| * Δ) := by ring
        _ ≤ (2 * Real.pi * V) * Real.exp (-gam * H) := mul_le_mul_of_nonneg_left h1 hc
        _ = 2 * Real.pi * Real.exp (-gam * H) * V := by ring
    have hconst : (∫ _α in S, (1 : ℂ)) = (V : ℂ) := by
      rw [setIntegral_const, hVdef]
      simp [measureReal_def]
    have hfr1' : ‖(∫ α in S, hfun α * torusChar (Ku u * α)) - τ * ∫ α in S, hfun α‖
        ≤ 2 * Real.pi * Real.exp (-gam * H) * V := le_trans hfr1 hfrbd
    have hfr2' : ‖(∫ α in S, torusChar (Ku u * α)) - (V : ℂ) * τ‖
        ≤ 2 * Real.pi * Real.exp (-gam * H) * V := by
      have heq : (∫ α in S, (fun _ : ℝ => (1 : ℂ)) α * torusChar (Ku u * α))
            - torusChar (Ku u * β) * (∫ α in S, (fun _ : ℝ => (1 : ℂ)) α)
          = (∫ α in S, torusChar (Ku u * α)) - (V : ℂ) * τ := by
        simp only [one_mul]
        rw [hconst, hτdef]
        ring
      rw [← heq]
      exact le_trans hfr2 hfrbd
    -- the mean replacement
    have hJh : (∫ α in S, hfun α)
        = ((∫ α in S, PhaseBounds.cylObs R w' (gaussIter α (k - R)) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun hSm ?_
      intro α _
      exact monoAt_zeroMode_eq_cylObs hRk w' α n
    have hmix' : ‖(∫ α in S, hfun α) - (V : ℂ) * (Preal : ℂ)‖
        ≤ 4 * Real.log 2 * (Cmix * ρmix ^ M + Real.exp (-H)) * ν := by
      have hcast : (∫ α in S, hfun α) - (V : ℂ) * (Preal : ℂ)
          = (((∫ α in S, PhaseBounds.cylObs R w' (gaussIter α (k - R))) - V * Preal : ℝ) : ℂ) := by
        rw [hJh]
        push_cast
        ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      refine le_trans hmixu ?_
      have hstep : Cmix * ρmix ^ M + Δ ≤ Cmix * ρmix ^ M + Real.exp (-H) := by
        have hd : Δ ≤ Real.exp (-Hscale n) := hDel
        rw [hHdef]
        linarith
      have hlog0 : (0 : ℝ) ≤ 4 * Real.log 2 * ν := by
        have h3 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have : (0 : ℝ) ≤ 4 * Real.log 2 := by linarith
        exact mul_nonneg this hν0
      calc ν * (2 * Real.log 2) * (Cmix * ρmix ^ M + Δ) * 2
          = (4 * Real.log 2 * ν) * (Cmix * ρmix ^ M + Δ) := by ring
        _ ≤ (4 * Real.log 2 * ν) * (Cmix * ρmix ^ M + Real.exp (-H)) :=
            mul_le_mul_of_nonneg_left hstep hlog0
        _ = 4 * Real.log 2 * (Cmix * ρmix ^ M + Real.exp (-H)) * ν := by ring
    -- assemble on the cylinder
    have hPnorm : ‖(Preal : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hP1
    have hinner : ‖(∫ α in S, hfun α * torusChar (Ku u * α))
          - (Preal : ℂ) * (∫ α in S, torusChar (Ku u * α))‖
        ≤ 4 * Real.pi * Real.exp (-gam * H) * V
          + 4 * Real.log 2 * (Cmix * ρmix ^ M + Real.exp (-H)) * ν := by
      have hsplit : (∫ α in S, hfun α * torusChar (Ku u * α))
            - (Preal : ℂ) * (∫ α in S, torusChar (Ku u * α))
          = ((∫ α in S, hfun α * torusChar (Ku u * α)) - τ * ∫ α in S, hfun α)
            + τ * ((∫ α in S, hfun α) - (V : ℂ) * (Preal : ℂ))
            - (Preal : ℂ) * ((∫ α in S, torusChar (Ku u * α)) - (V : ℂ) * τ) := by
        ring
      rw [hsplit]
      refine le_trans (norm_sub_le _ _) ?_
      refine le_trans (add_le_add (norm_add_le _ _) (le_refl _)) ?_
      have e2 : ‖τ * ((∫ α in S, hfun α) - (V : ℂ) * (Preal : ℂ))‖
          ≤ 4 * Real.log 2 * (Cmix * ρmix ^ M + Real.exp (-H)) * ν := by
        rw [norm_mul, hτ1, one_mul]
        exact hmix'
      have e3 : ‖(Preal : ℂ) * ((∫ α in S, torusChar (Ku u * α)) - (V : ℂ) * τ)‖
          ≤ 2 * Real.pi * Real.exp (-gam * H) * V := by
        rw [norm_mul]
        refine le_trans (mul_le_mul_of_nonneg_right hPnorm (norm_nonneg _)) ?_
        rw [one_mul]
        exact hfr2'
      linarith [hfr1', e2, e3]
    rw [hIA, hIB]
    rw [show (cu u * ∫ α in S, hfun α * torusChar (Ku u * α))
          - (Preal : ℂ) * (cu u * ∫ α in S, torusChar (Ku u * α))
        = cu u * ((∫ α in S, hfun α * torusChar (Ku u * α))
          - (Preal : ℂ) * ∫ α in S, torusChar (Ku u * α)) from by ring, norm_mul]
    refine le_trans (mul_le_mul_of_nonneg_right (hcu1 u) (norm_nonneg _)) ?_
    rw [one_mul]
    exact hinner
  -- ### summation over the retained family
  have hsumV : ∑ u ∈ W, (volume (Erdos1002.gaussHalfOpenPrefixCylinder u)).toReal ≤ 1 :=
    NonzeroMode.sum_vol_halfOpen_le_one W kp hkp0 hWshape
  have hsumν : ∑ u ∈ W,
      (Erdos1002.gaussMeasure (Erdos1002.gaussHalfOpenPrefixCylinder u)).toReal ≤ 1 :=
    NonzeroMode.sum_gauss_halfOpen_le_one W kp hWshape
  have hmixnn : (0 : ℝ) ≤ 4 * Real.log 2 * (Cmix * ρmix ^ M + Real.exp (-H)) := by
    have h1 : (0 : ℝ) ≤ Cmix * ρmix ^ M := by positivity
    have h2 : (0 : ℝ) < Real.exp (-H) := Real.exp_pos _
    have h3 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  have hfrnn : (0 : ℝ) ≤ 4 * Real.pi * Real.exp (-gam * H) := by positivity
  have hSum : ‖(∑ u ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, gfun α * hfun α)
        - (Preal : ℂ) * ∑ u ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, gfun α‖
      ≤ 4 * Real.pi * Real.exp (-gam * H)
        + 4 * Real.log 2 * (Cmix * ρmix ^ M + Real.exp (-H)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum hkey) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 : 4 * Real.pi * Real.exp (-gam * H)
        * ∑ u ∈ W, (volume (Erdos1002.gaussHalfOpenPrefixCylinder u)).toReal
        ≤ 4 * Real.pi * Real.exp (-gam * H) :=
      mul_le_of_le_one_right hfrnn hsumV
    have h2 : 4 * Real.log 2 * (Cmix * ρmix ^ M + Real.exp (-H))
        * ∑ u ∈ W, (Erdos1002.gaussMeasure
            (Erdos1002.gaussHalfOpenPrefixCylinder u)).toReal
        ≤ 4 * Real.log 2 * (Cmix * ρmix ^ M + Real.exp (-H)) :=
      mul_le_of_le_one_right hmixnn hsumν
    linarith
  -- ### restore the discarded cylinders on both sides
  have hPn : ‖(Preal : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hP1
  have hfinal : ‖(∫ α in Ioo (0 : ℝ) 1, gfun α * hfun α)
        - (Preal : ℂ) * ∫ α in Ioo (0 : ℝ) 1, gfun α‖
      ≤ 6 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n)))
        + 4 * Real.pi * Real.exp (-gam * H)
        + 4 * Real.log 2 * (Cmix * ρmix ^ M + Real.exp (-H)) := by
    have hid : (∫ α in Ioo (0 : ℝ) 1, gfun α * hfun α)
          - (Preal : ℂ) * ∫ α in Ioo (0 : ℝ) 1, gfun α
        = ((∫ α in Ioo (0 : ℝ) 1, gfun α * hfun α)
            - ∑ u ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, gfun α * hfun α)
          + ((∑ u ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, gfun α * hfun α)
            - (Preal : ℂ) * ∑ u ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, gfun α)
          - (Preal : ℂ) * ((∫ α in Ioo (0 : ℝ) 1, gfun α)
            - ∑ u ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, gfun α) := by
      ring
    rw [hid]
    refine le_trans (norm_sub_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) (le_refl _)) ?_
    have e3 : ‖(Preal : ℂ) * ((∫ α in Ioo (0 : ℝ) 1, gfun α)
          - ∑ u ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, gfun α)‖
        ≤ 3 * (C₀ * Real.exp (-c₀ * Real.sqrt (Lnorm n))) := by
      rw [norm_mul]
      have h0 : (0 : ℝ) ≤ ‖(∫ α in Ioo (0 : ℝ) 1, gfun α)
          - ∑ u ∈ W, ∫ α in Erdos1002.gaussHalfOpenPrefixCylinder u, gfun α‖ := norm_nonneg _
      nlinarith [hPn, hB1, h0, norm_nonneg ((Preal : ℂ))]
    linarith [hA1, hSum, e3]
  -- ### and drop the constant
  have hlast : ‖(Preal : ℂ) * ∫ α in Ioo (0 : ℝ) 1, gfun α‖
      ≤ ‖∫ α in Ioo (0 : ℝ) 1, gfun α‖ := by
    rw [norm_mul]
    have h0 : (0 : ℝ) ≤ ‖∫ α in Ioo (0 : ℝ) 1, gfun α‖ := norm_nonneg _
    nlinarith [hPn, h0]
  have htri : ‖∫ α in Ioo (0 : ℝ) 1, gfun α * hfun α‖
      ≤ ‖(∫ α in Ioo (0 : ℝ) 1, gfun α * hfun α)
          - (Preal : ℂ) * ∫ α in Ioo (0 : ℝ) 1, gfun α‖
        + ‖(Preal : ℂ) * ∫ α in Ioo (0 : ℝ) 1, gfun α‖ := by
    have := norm_add_le ((∫ α in Ioo (0 : ℝ) 1, gfun α * hfun α)
      - (Preal : ℂ) * ∫ α in Ioo (0 : ℝ) 1, gfun α)
      ((Preal : ℂ) * ∫ α in Ioo (0 : ℝ) 1, gfun α)
    simpa using this
  linarith [htri, hfinal, hlast]

/-! ## 4. The `∀ᶠ n` wrapper -/

set_option maxHeartbeats 6400000 in
/-- **The super-resonance branch of case 3 of the proof of Proposition 4.2.**
"If `k > t₀ + 100H`."  The later mode is zero, so the combined frequency of
(33) is `±Q_j`; but the later window sits above the descendant cut `t₋` of
the earlier index, so it is first removed by the mean replacement of §3, and
what is left is the earlier monomial alone, killed by §1. -/
theorem earlierMode_superResonance_bound' (R K : ℕ)
    (Wu Wv : Finset (Fin (2 * R) → ℕ)) :
    ∃ C c ρ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ Wu, ∀ m ∈ Prop42.modeBox K, m ≠ (0, 0) → ∀ w' ∈ Wv,
      ∀ p ∈ bulkPairs n,
        Prop41.resonanceTime n p.1 + 100 * Hscale n < (p.2 : ℝ) →
        ‖(∫ α in Ioo (0 : ℝ) 1,
              Prop42.monoAt R w m.1 m.2 α n p.1 * Prop42.monoAt R w' 0 0 α n p.2)‖
          ≤ C * (Real.exp (-c * Real.sqrt (Lnorm n))
                  + Real.exp (-c * Hscale n) + ρ ^ (c * Hscale n)) := by
  classical
  obtain ⟨C20, c20, hC20, hc20, h20⟩ := LargeDeviation.display20_of_pos 1 one_pos
  obtain ⟨C3, c3, hc3, hAC⟩ := Kwon1002.shrinking_anti_concentration
  obtain ⟨Cmix, ρmix, hCmix, hρmix0, hρmix1, hmix⟩ :=
    StationaryReplace.leb_halfOpen_multiblock_mixing 1
  set C3' : ℝ := max C3 0 with hC3'def
  have hC3'0 : (0 : ℝ) ≤ C3' := le_max_right _ _
  have hC3C3' : C3 ≤ C3' := le_max_left _ _
  set Kc : ℝ := 2 * (K : ℝ) + 1 with hKcdef
  have hKc1 : (1 : ℝ) ≤ Kc := by
    have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    rw [hKcdef]; linarith
  have h80 := Prop42.eighty_lyapunov_bounds
  have hlyap : (0 : ℝ) < lyapunov := Prop42.lyapunov_pos
  set gam : ℝ := 40 * lyapunov - 3 / 2 * 1 with hgamdef
  have hgam1 : (1 : ℝ) ≤ gam := by rw [hgamdef]; linarith [h80.1]
  set c : ℝ := min 1 (min c20 (200 * c3)) with hcdef
  have hc0 : 0 < c := lt_min one_pos (lt_min hc20 (by linarith))
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcc20 : c ≤ c20 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hcc3 : c ≤ 200 * c3 := le_trans (min_le_right _ _) (min_le_right _ _)
  set ρ : ℝ := max (1 / 2) ρmix with hρdef
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hρ1 : ρ < 1 := max_lt (by norm_num) hρmix1
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set C : ℝ := max (9 * C20)
    (max (2 * C3' + 28 + 4 * Real.pi + 4 * Real.log 2)
      (max (4 * Real.log 2 * Cmix / ρmix) 1)) with hCdef
  have hCA : 9 * C20 ≤ C := le_max_left _ _
  have hCB : 2 * C3' + 28 + 4 * Real.pi + 4 * Real.log 2 ≤ C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hCC : 4 * Real.log 2 * Cmix / ρmix ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hC1 : (1 : ℝ) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC1
  refine ⟨C, c, ρ, hC0, hc0, hρ0, hρ1, ?_⟩
  filter_upwards [h20,
    PhaseBounds.ascended_descendant_bound_at_cut (Kc := Kc) (del := 1) hKc1
      (by linarith [h80.1]),
    P42Cases.tendsto_Hscale.eventually_ge_atTop
      (max 1 (max ((R : ℝ)) (((R : ℝ) + 1) / 60))),
    eventually_ge_atTop 1] with n h20n hascn hHM hn1
  intro w hw m hm hm0 w' hw' p hp hres
  set H : ℝ := Hscale n with hHdef
  have hH1 : (1 : ℝ) ≤ H := le_trans (le_max_left _ _) hHM
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hHR : (R : ℝ) ≤ H := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hHM
  have hHR60 : (R : ℝ) + 1 ≤ 60 * H := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hHM
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 60)] at this
    linarith
  -- the pair
  have hjb : p.1 ∈ bulkJ n := MonomialCore.mem_bulkPairs_fst hp
  have hkb : p.2 ∈ bulkJ n := PhaseBounds.mem_bulkPairs_snd hp
  have hjk : p.1 < p.2 := MonomialCore.mem_bulkPairs_lt hp
  have hjlo : 200 * H ≤ (p.1 : ℝ) := ((Finset.mem_filter.1 hjb).2).1
  have hklo : 200 * H ≤ (p.2 : ℝ) := ((Finset.mem_filter.1 hkb).2).1
  have hjm : p.1 ≤ mIndex n :=
    Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_filter.1 hjb).1)
  have hjmR : (p.1 : ℝ) ≤ (mIndex n : ℝ) := by exact_mod_cast hjm
  have hRj : R ≤ p.1 := by
    have : (R : ℝ) ≤ (p.1 : ℝ) := by linarith
    exact_mod_cast this
  have hRk : R ≤ p.2 := by
    have : (R : ℝ) ≤ (p.2 : ℝ) := by linarith
    exact_mod_cast this
  have hj1 : 1 ≤ p.1 := by
    have : (1 : ℝ) ≤ (p.1 : ℝ) := by linarith
    exact_mod_cast this
  -- the ascended cut
  set kp : ℕ := (Prop41.kPlus n p.1).toNat with hkpdef
  have hresge : (p.1 : ℝ) ≤ Prop41.resonanceTime n p.1 := by
    show (p.1 : ℝ) ≤ ((mIndex n : ℝ) + (p.1 : ℝ)) / 2
    linarith
  have hkpZ : (0 : ℝ) < ((Prop41.kPlus n p.1 : ℤ) : ℝ) := by
    have h1 : Prop41.resonanceTime n p.1 + 40 * Hscale n - 1
        < ((Prop41.kPlus n p.1 : ℤ) : ℝ) := Int.sub_one_lt_floor _
    rw [← hHdef] at h1
    linarith
  have hkp_cast : ((kp : ℕ) : ℝ) = ((Prop41.kPlus n p.1 : ℤ) : ℝ) := by
    rw [hkpdef]
    have h0 : (0 : ℤ) ≤ Prop41.kPlus n p.1 := by exact_mod_cast hkpZ.le
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg h0)
  have hkp_lb : Prop41.resonanceTime n p.1 + 40 * H - 1 < (kp : ℝ) := by
    rw [hkp_cast]
    have h1 : Prop41.resonanceTime n p.1 + 40 * Hscale n - 1
        < ((Prop41.kPlus n p.1 : ℤ) : ℝ) := Int.sub_one_lt_floor _
    rw [← hHdef] at h1
    exact h1
  have hkp_ub : (kp : ℝ) ≤ Prop41.resonanceTime n p.1 + 40 * H := by
    rw [hkp_cast, hHdef]
    exact PhaseBounds.kPlus_le_add n p.1
  have hkp_lb2 : 240 * H - 1 < (kp : ℝ) := by linarith
  have hkp0 : 0 < kp := by
    have : (0 : ℝ) < (kp : ℝ) := by linarith
    exact_mod_cast this
  have hjRkp : p.1 + R ≤ kp := by
    have : ((p.1 + R : ℕ) : ℝ) ≤ (kp : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hkp2m : kp ≤ 2 * mIndex n := PhaseBounds.kPlus_toNat_le_two_mIndex_of_bulk hjb
  have hDel : Real.exp (2 * Hscale n - 2 * lyapunov * ((kp : ℕ) : ℝ))
      ≤ Real.exp (-Hscale n) := by
    refine Real.exp_le_exp.2 ?_
    rw [← hHdef]
    nlinarith [h80.1, hkp_lb2, hH1]
  -- the mixing gap
  set M : ℕ := ⌊H⌋₊ with hMdef
  have hM_le : (M : ℝ) ≤ H := Nat.floor_le hH0
  have hM_ge : H - 1 ≤ (M : ℝ) := by
    have := Nat.lt_floor_add_one H
    linarith
  have hgap : kp + M + R ≤ p.2 := by
    have : ((kp + M + R : ℕ) : ℝ) ≤ (p.2 : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hnn : (n : ℝ) ≤ Real.exp (Lnorm n) := by
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    rw [Lnorm, Real.exp_log hn0]
  -- the mode bound
  have hmode : |((m.1 : ℤ) : ℝ)| + |((m.2 : ℤ) : ℝ)| ≤ Kc := by
    rw [Prop42.modeBox, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hm
    have h1 : |((m.1 : ℤ) : ℝ)| ≤ (K : ℝ) := by
      rw [abs_le]
      exact ⟨by exact_mod_cast hm.1.1, by exact_mod_cast hm.1.2⟩
    have h2 : |((m.2 : ℤ) : ℝ)| ≤ (K : ℝ) := by
      rw [abs_le]
      exact ⟨by exact_mod_cast hm.2.1, by exact_mod_cast hm.2.2⟩
    rw [hKcdef]; linarith
  -- §3: remove the later block
  have hstep3 := mean_replacement_bound (n := n) (R := R) (j := p.1) (k := p.2)
    (r := m.1) (s := m.2) hj1 hRj hRk w w' h20n (Kc := Kc) (gam := gam) hmode
    (hascn p.1 hjb) hnn hjRkp hkp0 hkp2m hDel hCmix hρmix0 hmix hgap
  -- §1: the earlier monomial alone
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
  have hdt : p.1 + R < (Prop41.kMinus n p.1).toNat :=
    PhaseBounds.prefix_lt_kMinus_toNat_of_bulk hjb (by rw [hHdef] at hHR60; exact hHR60)
  have hstep1 := oscillatory_single_bound hn1 hjb hj1 hRj w hdt
    (C₀ := C20) (c₀ := c20) h20n
    (Cac := C3 * (Real.exp (-H) + Real.exp (-c3 * (p.1 : ℝ)))) hacn
  -- ### the error shape
  have hLsq : (0 : ℝ) ≤ Real.sqrt (Lnorm n) := Real.sqrt_nonneg _
  set E1 : ℝ := Real.exp (-c * Real.sqrt (Lnorm n)) with hE1
  set E2 : ℝ := Real.exp (-c * H) with hE2
  set E3 : ℝ := ρ ^ (c * H) with hE3
  have hE10 : (0 : ℝ) < E1 := Real.exp_pos _
  have hE20 : (0 : ℝ) < E2 := Real.exp_pos _
  have hE30 : (0 : ℝ) < E3 := Real.rpow_pos_of_pos hρ0 _
  have e1 : Real.exp (-c20 * Real.sqrt (Lnorm n)) ≤ E1 := Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-H) ≤ E2 := Real.exp_le_exp.2 (by nlinarith)
  have e3 : Real.exp (-c3 * (p.1 : ℝ)) ≤ E2 := by
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have e4 : Real.exp (-gam * H) ≤ E2 := Real.exp_le_exp.2 (by nlinarith)
  -- the mixing tail
  have hmixtail : Cmix * ρmix ^ M ≤ (Cmix / ρmix) * E3 := by
    have hrw : ρmix ^ M = ρmix ^ ((M : ℕ) : ℝ) := (Real.rpow_natCast ρmix M).symm
    have hs1 : ρmix ^ ((M : ℕ) : ℝ) ≤ ρmix ^ (H - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hρmix0 hρmix1.le hM_ge
    have hs2 : ρmix ^ (H - 1) = ρmix ^ H / ρmix := by
      rw [Real.rpow_sub hρmix0, Real.rpow_one]
    have hs3 : ρmix ^ H ≤ ρmix ^ (c * H) :=
      Real.rpow_le_rpow_of_exponent_ge hρmix0 hρmix1.le (by nlinarith)
    have hs4 : ρmix ^ (c * H) ≤ E3 := by
      rw [hE3]
      exact Real.rpow_le_rpow hρmix0.le (le_max_right _ _) (by positivity)
    have hchain : ρmix ^ M ≤ E3 / ρmix := by
      rw [hrw]
      refine le_trans hs1 ?_
      rw [hs2]
      exact div_le_div_of_nonneg_right (le_trans hs3 hs4) hρmix0.le
    calc Cmix * ρmix ^ M ≤ Cmix * (E3 / ρmix) :=
          mul_le_mul_of_nonneg_left hchain hCmix.le
      _ = (Cmix / ρmix) * E3 := by field_simp
  -- collect
  have hT1 : 9 * (C20 * Real.exp (-c20 * Real.sqrt (Lnorm n))) ≤ C * E1 := by
    have h1 : 9 * (C20 * Real.exp (-c20 * Real.sqrt (Lnorm n))) ≤ 9 * (C20 * E1) := by
      nlinarith [hC20, e1, hE10]
    nlinarith [hCA, hE10]
  have hT2 : C3 * (Real.exp (-H) + Real.exp (-c3 * (p.1 : ℝ)))
      + 28 * Real.exp (-H) + 4 * Real.pi * Real.exp (-gam * H)
      + 4 * Real.log 2 * Real.exp (-H)
      ≤ (2 * C3' + 28 + 4 * Real.pi + 4 * Real.log 2) * E2 := by
    have hb1 : C3 * (Real.exp (-H) + Real.exp (-c3 * (p.1 : ℝ))) ≤ 2 * C3' * E2 := by
      have hstep1' : C3 * (Real.exp (-H) + Real.exp (-c3 * (p.1 : ℝ)))
          ≤ C3' * (Real.exp (-H) + Real.exp (-c3 * (p.1 : ℝ))) :=
        mul_le_mul_of_nonneg_right hC3C3' (by positivity)
      have hstep2' : C3' * (Real.exp (-H) + Real.exp (-c3 * (p.1 : ℝ)))
          ≤ C3' * (2 * E2) :=
        mul_le_mul_of_nonneg_left (by linarith) hC3'0
      linarith
    have hpi : (0 : ℝ) ≤ 4 * Real.pi := by positivity
    nlinarith [hb1, e2, e4, hpi, hlog2, hE20]
  have hT2' : C3 * (Real.exp (-H) + Real.exp (-c3 * (p.1 : ℝ)))
      + 28 * Real.exp (-H) + 4 * Real.pi * Real.exp (-gam * H)
      + 4 * Real.log 2 * Real.exp (-H) ≤ C * E2 := by
    have := hT2
    nlinarith [hCB, hE20]
  have hT3 : 4 * Real.log 2 * (Cmix * ρmix ^ M) ≤ C * E3 := by
    have h1 : 4 * Real.log 2 * (Cmix * ρmix ^ M)
        ≤ 4 * Real.log 2 * ((Cmix / ρmix) * E3) := by
      nlinarith [hmixtail, hlog2]
    have h2 : 4 * Real.log 2 * ((Cmix / ρmix) * E3)
        = (4 * Real.log 2 * Cmix / ρmix) * E3 := by field_simp
    rw [h2] at h1
    nlinarith [h1, hCC, hE30]
  have hfin : ‖∫ α in Ioo (0 : ℝ) 1, Prop42.monoAt R w m.1 m.2 α n p.1‖
      ≤ 3 * (C20 * Real.exp (-c20 * Real.sqrt (Lnorm n)))
        + C3 * (Real.exp (-H) + Real.exp (-c3 * (p.1 : ℝ)))
        + 28 * Real.exp (-H) := by
    rw [hHdef]
    exact hstep1
  have hcombined := le_trans hstep3 (by linarith [hfin] :
    ‖∫ α in Ioo (0 : ℝ) 1, Prop42.monoAt R w m.1 m.2 α n p.1‖
      + 6 * (C20 * Real.exp (-c20 * Real.sqrt (Lnorm n)))
      + 4 * Real.pi * Real.exp (-gam * Hscale n)
      + 4 * Real.log 2 * (Cmix * ρmix ^ M + Real.exp (-Hscale n))
    ≤ 9 * (C20 * Real.exp (-c20 * Real.sqrt (Lnorm n)))
      + (C3 * (Real.exp (-H) + Real.exp (-c3 * (p.1 : ℝ)))
        + 28 * Real.exp (-H) + 4 * Real.pi * Real.exp (-gam * H)
        + 4 * Real.log 2 * Real.exp (-H))
      + 4 * Real.log 2 * (Cmix * ρmix ^ M))
  refine le_trans hcombined ?_
  have : C * (E1 + E2 + E3) = C * E1 + C * E2 + C * E3 := by ring
  rw [hE1, hE2, hE3] at this ⊢
  linarith [hT1, hT2', hT3]

end

end P42Super

end Kwon1002
