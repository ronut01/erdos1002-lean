import Kwon1002.Prop64FullState
import Kwon1002.Prop64Carry
import Kwon1002.Prop64SquaredError
import Kwon1002.Section6Continuity
import Mathlib.Util.AssertNoSorry

open MeasureTheory Set Filter Metric
open scoped BigOperators Topology ENNReal BoundedContinuousFunction

namespace Kwon1002.Prop64SpecialTransfers

noncomputable section

open Prop64

local instance propDecidable (P : Prop) : Decidable P := Classical.propDecidable P

private def xIndex (R : ℕ) (t : Fin R) : Fin (2 * R + 1) :=
  ⟨t, by omega⟩

private def thetaIndex (R : ℕ) (t : Fin R) : Fin (2 * R + 2) :=
  ⟨t + 1, by omega⟩

private lemma wX_index (R : ℕ) (w : WindowSpace R) (t : Fin R) :
    wX w (-(R : ℤ) + (t : ℤ)) = w.2.1 (xIndex R t) := by
  unfold wX
  rw [dif_pos (by constructor <;> omega)]
  apply congrArg
  apply Fin.ext
  simp [xIndex]

private lemma wTh_index (R : ℕ) (w : WindowSpace R) (t : Fin R) :
    wTh w (-(R : ℤ) + (t : ℤ)) = w.2.2 (thetaIndex R t) := by
  unfold wTh
  rw [dif_pos (by constructor <;> omega)]
  apply congrArg
  apply Fin.ext
  simp [thetaIndex]

/-- The open reset arc `(1/2,3/4)` on the genuine unit torus.  Writing it
as the ball of centre `5/8` and radius `1/8` keeps the seam at zero out of
its frontier. -/
def resetArc9 : Set UnitAddCircle :=
  ball ((5 / 8 : ℝ) : UnitAddCircle) (1 / 8 : ℝ)

def qResetAt9 (R : ℕ) (q : QWindow R) (t : Fin R) : Prop :=
  q.2.1 (xIndex R t) < 1 / 40 ∧ q.2.2 (thetaIndex R t) ∈ resetArc9

/-- The radius-`R`, `D=9` no-reset event on the quotient window. -/
def qNoResetSet9 (R : ℕ) : Set (QWindow R) :=
  {q | ∀ t : Fin R, ¬ qResetAt9 R q t}

def windowResetAt9 (R : ℕ) (w : WindowSpace R) (t : Fin R) : Prop :=
  wX w (-(R : ℤ) + (t : ℤ)) < 1 / 40 ∧
    1 / 2 < wTh w (-(R : ℤ) + (t : ℤ)) ∧
    wTh w (-(R : ℤ) + (t : ℤ)) < 3 / 4

def windowNoResetSet9 (R : ℕ) : Set (WindowSpace R) :=
  {w | ∀ t : Fin R, ¬ windowResetAt9 R w t}

private lemma mem_resetArc9_coe_iff {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    (s : UnitAddCircle) ∈ resetArc9 ↔ 1 / 2 < s ∧ s < 3 / 4 := by
  rw [resetArc9, mem_ball, dist_eq_norm, ← QuotientAddGroup.mk_sub,
    AddCircle.norm_eq]
  norm_num only [inv_one, one_mul]
  by_cases hlo : s < 1 / 8
  · have hr : round (s - 5 / 8) = -1 := by
      rw [round_eq, Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith [hs.1]
    rw [hr]
    norm_num
    constructor
    · intro h
      rw [abs_lt] at h
      linarith [hs.1]
    · rintro ⟨h, _⟩
      linarith
  · have hr : round (s - 5 / 8) = 0 := by
      rw [round_eq_zero_iff]
      constructor <;> linarith [hs.2]
    rw [hr, Int.cast_zero, zero_mul, sub_zero]
    constructor
    · intro h
      rw [abs_lt] at h
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      rw [abs_lt]
      constructor <;> linarith

lemma quotientWindow_preimage_qNoResetSet9_on_support (R : ℕ) :
    quotientWindow R ⁻¹' qNoResetSet9 R ∩ WindowSupport R =
      windowNoResetSet9 R ∩ WindowSupport R := by
  ext w
  simp only [mem_inter_iff, mem_preimage, qNoResetSet9, mem_setOf_eq,
    windowNoResetSet9]
  constructor
  · rintro ⟨hq, hw⟩
    refine ⟨?_, hw⟩
    intro t hreset
    apply hq t
    rcases hreset with ⟨hx, hth⟩
    constructor
    · simpa [qResetAt9, quotientWindow, wX_index] using hx
    · rw [wTh_index] at hth
      exact (mem_resetArc9_coe_iff (hw.2 (thetaIndex R t))).2 hth
  · rintro ⟨hwno, hw⟩
    refine ⟨?_, hw⟩
    intro t hreset
    apply hwno t
    rcases hreset with ⟨hx, hth⟩
    constructor
    · simpa [qResetAt9, quotientWindow, wX_index] using hx
    · rw [wTh_index]
      exact (mem_resetArc9_coe_iff (hw.2 (thetaIndex R t))).1 hth

lemma measurableSet_qNoResetSet9 (R : ℕ) : MeasurableSet (qNoResetSet9 R) := by
  rw [show qNoResetSet9 R = ⋂ t : Fin R,
      ({q : QWindow R | q.2.1 (xIndex R t) < 1 / 40} ∩
        (fun q : QWindow R ↦ q.2.2 (thetaIndex R t)) ⁻¹' resetArc9)ᶜ by
    ext q
    simp [qNoResetSet9, qResetAt9]]
  exact MeasurableSet.iInter fun t =>
    (MeasurableSet.inter
      (measurableSet_lt
        (((measurable_pi_apply (xIndex R t)).comp measurable_fst).comp measurable_snd)
        measurable_const)
      ((((measurable_pi_apply (thetaIndex R t)).comp measurable_snd).comp measurable_snd)
        measurableSet_ball)).compl

lemma qActualWindowLaw_qNoResetSet9 (R n j : ℕ) :
    Prop64.qActualWindowLaw R n j (qNoResetSet9 R) =
      actualWindowLaw R n j (quotientWindow R ⁻¹' qNoResetSet9 R) := by
  rw [Prop64.qActualWindowLaw, Measure.map_apply (measurable_quotientWindow R)
    (measurableSet_qNoResetSet9 R)]

lemma qWindowLaw_qNoResetSet9 (R : ℕ) :
    qWindowLaw R (qNoResetSet9 R) =
      windowLaw R (quotientWindow R ⁻¹' qNoResetSet9 R) := by
  rw [qWindowLaw, Measure.map_apply (measurable_quotientWindow R)
    (measurableSet_qNoResetSet9 R)]

lemma qWindowLaw_qNoResetSet9_eq_window (R : ℕ) :
    qWindowLaw R (qNoResetSet9 R) = windowLaw R (windowNoResetSet9 R) := by
  rw [qWindowLaw_qNoResetSet9]
  apply measure_congr
  filter_upwards [windowLaw_ae_mem_windowSupport R] with w hw
  have hsets := Set.ext_iff.mp (quotientWindow_preimage_qNoResetSet9_on_support R) w
  simpa [hw] using hsets

private lemma actualWindowLaw_ae_mem_windowSupport (R n j : ℕ) :
    ∀ᵐ w ∂(actualWindowLaw R n j), w ∈ WindowSupport R := by
  rw [actualWindowLaw]
  apply (ae_map_iff (measurable_actualWindow R n j).aemeasurable
    (measurableSet_windowSupport R)).2
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
    with α hα hirr
  constructor
  · intro i
    change gaussIter α (j + (i : ℕ) - R) ∈ Ioo (0 : ℝ) 1
    exact gaussIter_mem_Ioo hα hirr _
  · intro i
    change theta α n (j + (i : ℕ) - R - 1) ∈ Ico (0 : ℝ) 1
    exact theta_mem_Ico α n _

lemma qActualWindowLaw_qNoResetSet9_eq_window (R n j : ℕ) :
    Prop64.qActualWindowLaw R n j (qNoResetSet9 R) =
      actualWindowLaw R n j (windowNoResetSet9 R) := by
  rw [qActualWindowLaw_qNoResetSet9]
  apply measure_congr
  filter_upwards [actualWindowLaw_ae_mem_windowSupport R n j] with w hw
  have hsets := Set.ext_iff.mp (quotientWindow_preimage_qNoResetSet9_on_support R) w
  simpa [hw] using hsets

private lemma gaussMarginal_singleton (c : ℝ) : gaussMarginal ({c} : Set ℝ) = 0 := by
  exact NatExtMixing.gaussMarginal_ac (by simp)

private lemma qWindowLaw_x_singleton (R : ℕ) (i : Fin (2 * R + 1)) (c : ℝ) :
    qWindowLaw R {q | q.2.1 i = c} = 0 := by
  rw [qWindowLaw]
  change (Measure.map (quotientWindow R) (windowLaw R))
    ((fun q : QWindow R ↦ q.2.1 i) ⁻¹' {c}) = 0
  have hset : MeasurableSet ((fun q : QWindow R ↦ q.2.1 i) ⁻¹' {c}) :=
    (((measurable_pi_apply i).comp measurable_fst).comp measurable_snd)
      (measurableSet_singleton c)
  rw [Measure.map_apply (measurable_quotientWindow R) hset]
  rw [windowLaw, Measure.map_apply (measurable_stationaryWindow R)
    ((measurable_quotientWindow R) hset)]
  let t : ℤ := (i : ℤ) - (R : ℤ)
  have ht1 : -(R : ℤ) ≤ t := by dsimp [t]; omega
  have ht2 : t ≤ (R : ℤ) := by dsimp [t]; omega
  have hpre : stationaryWindow R ⁻¹'
        (quotientWindow R ⁻¹' ((fun q : QWindow R ↦ q.2.1 i) ⁻¹' {c})) =
      (fun z : NatExtTorus ↦ (hatSzpow t z).1.1) ⁻¹' {c} := by
    ext z
    simp only [mem_preimage, mem_setOf_eq, mem_singleton_iff, quotientWindow]
    change (stationaryWindow R z).2.1 i = c ↔ _
    have hi : i = ⟨(t + (R : ℤ)).toNat, by omega⟩ := by
      apply Fin.ext
      dsimp [t]
      omega
    rw [hi, ← wX_stationaryWindow R z ht1 ht2]
    have hc : 0 ≤ t + (R : ℤ) ∧ t + (R : ℤ) < 2 * (R : ℤ) + 1 := by
      constructor <;> omega
    simp only [wX, dif_pos hc]
  rw [hpre, ← Measure.map_apply (measurable_hatSzpow t).fst.fst (measurableSet_singleton c),
    hatMu0_map_hatSzpow_future, gaussMarginal_singleton]

private lemma hatMu0_theta_singleton_zero_noreset (c : ℝ) :
    hatMu0 {z : NatExtTorus | z.2.2 = c} = 0 := by
  rw [hatMu0_eq_prod]
  apply (Measure.measure_prod_null
    (measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const)).2
  filter_upwards with p
  change (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))
    {q : ℝ × ℝ | q.2 = c} = 0
  rw [NatExtMeasure.restrict_unitSq_eq_prod,
    Measure.measure_prod_null
      (measurableSet_eq_fun measurable_snd measurable_const)]
  filter_upwards with r
  exact measure_singleton c

private lemma qWindowLaw_theta_singleton_noreset (R : ℕ) (i : Fin (2 * R + 2))
    (c : UnitAddCircle) : qWindowLaw R {q | q.2.2 i = c} = 0 := by
  rw [qWindowLaw]
  change (Measure.map (quotientWindow R) (windowLaw R))
    ((fun q : QWindow R ↦ q.2.2 i) ⁻¹' {c}) = 0
  have hset : MeasurableSet ((fun q : QWindow R ↦ q.2.2 i) ⁻¹' {c}) :=
    (((measurable_pi_apply i).comp measurable_snd).comp measurable_snd)
      (measurableSet_singleton c)
  rw [Measure.map_apply (measurable_quotientWindow R) hset]
  rw [windowLaw, Measure.map_apply (measurable_stationaryWindow R)
    ((measurable_quotientWindow R) hset)]
  let t : ℤ := (i : ℤ) - (R : ℤ) - 1
  have ht1 : -(R : ℤ) - 1 ≤ t := by dsimp [t]; omega
  have ht2 : t ≤ (R : ℤ) := by dsimp [t]; omega
  let r : ℝ := ((AddCircle.equivIco 1 0) c).1
  have hstate : hatMu0 {z : NatExtTorus | (hatSzpow t z).2.2 = r} = 0 := by
    have hm := (hatSzpow_measurePreserving t).measure_preimage
      (measurableSet_eq_fun (measurable_snd.comp measurable_snd)
        (measurable_const : Measurable fun _ : NatExtTorus => r)).nullMeasurableSet
    change hatMu0 ((hatSzpow t) ⁻¹' {z : NatExtTorus | z.2.2 = r}) = 0
    simpa only [Function.comp_apply] using
      hm.trans (hatMu0_theta_singleton_zero_noreset r)
  apply bot_unique
  calc
    hatMu0 (stationaryWindow R ⁻¹' (quotientWindow R ⁻¹' {q | q.2.2 i = c}))
        ≤ hatMu0 {z : NatExtTorus | (hatSzpow t z).2.2 = r} := by
          apply measure_mono_ae
          filter_upwards [CarryGraph.hatMu0_ae_goodT] with z hz hzc
          change ((stationaryWindow R z).2.2 i : UnitAddCircle) = c at hzc
          have hi : i = ⟨(t + (R : ℤ) + 1).toNat, by omega⟩ := by
            apply Fin.ext
            dsimp [t]
            omega
          have hread : (stationaryWindow R z).2.2 i = (hatSzpow t z).2.2 := by
            rw [hi, ← wTh_stationaryWindow R z ht1 ht2]
            have hc : 0 ≤ t + (R : ℤ) + 1 ∧
                t + (R : ℤ) + 1 < 2 * (R : ℤ) + 2 := by
              constructor <;> omega
            simp only [wTh, dif_pos hc]
          rw [hread] at hzc
          have hgood : hatSzpow t z ∈ CarryGraph.GoodT := by
            by_cases ht : (0 : ℤ) ≤ t
            · rw [hatSzpow, if_pos ht]
              exact CarryGraph.hatS_iterate_mem_goodT hz _
            · rw [hatSzpow, if_neg ht]
              exact CarryGraph.hatSinv_iterate_mem_goodT hz _
          have hgood' : (hatSzpow t z).2.2 ∈ Ico (0 : ℝ) (0 + 1) := by
            simpa only [zero_add] using hgood.2.2
          have hc' : ((AddCircle.equivIco 1 0) c).1 ∈ Ico (0 : ℝ) (0 + 1) :=
            (AddCircle.equivIco 1 0 c).2
          have heqrep : c = (((AddCircle.equivIco 1 0) c).1 : UnitAddCircle) :=
            ((AddCircle.equivIco 1 0).symm_apply_apply c).symm
          exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
            (p := (1 : ℝ)) (a := (0 : ℝ)) hgood' hc').mp
              (hzc.trans heqrep)
    _ = 0 := hstate

private lemma resetArc9_sphere_subset :
    sphere ((5 / 8 : ℝ) : UnitAddCircle) (1 / 8 : ℝ) ⊆
      ({((1 / 2 : ℝ) : UnitAddCircle), ((3 / 4 : ℝ) : UnitAddCircle)} :
        Set UnitAddCircle) := by
  intro y hy
  let s : ℝ := ((AddCircle.equivIco 1 0) y).1
  have hs : s ∈ Ico (0 : ℝ) 1 := by
    simpa [s] using (AddCircle.equivIco 1 0 y).2
  have hcoe : (s : UnitAddCircle) = y := (AddCircle.equivIco 1 0).symm_apply_apply y
  rw [mem_sphere, ← hcoe, dist_eq_norm, ← QuotientAddGroup.mk_sub,
    AddCircle.norm_eq] at hy
  norm_num only [inv_one, one_mul] at hy
  by_cases hlo : s < 1 / 8
  · have hr : round (s - 5 / 8) = -1 := by
      rw [round_eq, Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith [hs.1]
    rw [hr] at hy
    norm_num at hy
    rw [abs_eq (by positivity)] at hy
    rcases hy with hy | hy <;> linarith [hs.1]
  · have hr : round (s - 5 / 8) = 0 := by
      rw [round_eq_zero_iff]
      constructor <;> linarith [hs.2]
    rw [hr, Int.cast_zero, zero_mul, sub_zero, abs_eq (by positivity)] at hy
    simp only [mem_insert_iff, mem_singleton_iff]
    rcases hy with hy | hy
    · right
      rw [← hcoe]
      congr 1
      linarith
    · left
      rw [← hcoe]
      congr 1
      linarith

private lemma qWindowLaw_frontier_xCut_null (R : ℕ) (t : Fin R) :
    qWindowLaw R (frontier {q : QWindow R | q.2.1 (xIndex R t) < 1 / 40}) = 0 := by
  apply measure_mono_null
    (frontier_lt_subset_eq
      ((((continuous_apply (xIndex R t)).comp continuous_fst).comp continuous_snd))
      continuous_const)
  exact qWindowLaw_x_singleton R (xIndex R t) (1 / 40)

private lemma qWindowLaw_frontier_thetaArc_null (R : ℕ) (t : Fin R) :
    qWindowLaw R
      (frontier ((fun q : QWindow R ↦ q.2.2 (thetaIndex R t)) ⁻¹' resetArc9)) = 0 := by
  let f : QWindow R → UnitAddCircle := fun q ↦ q.2.2 (thetaIndex R t)
  have hf : Continuous f :=
    (((continuous_apply (thetaIndex R t)).comp continuous_snd).comp continuous_snd)
  have hsub : frontier (f ⁻¹' resetArc9) ⊆
      {q : QWindow R | f q = ((1 / 2 : ℝ) : UnitAddCircle)} ∪
      {q : QWindow R | f q = ((3 / 4 : ℝ) : UnitAddCircle)} :=
    (hf.frontier_preimage_subset resetArc9).trans (by
      intro q hq
      have hsphere := frontier_ball_subset_sphere hq
      rcases resetArc9_sphere_subset hsphere with h | h
      · left
        exact h
      · right
        exact h)
  apply measure_mono_null hsub
  rw [measure_union_null]
  · exact qWindowLaw_theta_singleton_noreset R (thetaIndex R t) _
  · exact qWindowLaw_theta_singleton_noreset R (thetaIndex R t) _

private lemma qWindowLaw_frontier_qResetAt9_null (R : ℕ) (t : Fin R) :
    qWindowLaw R (frontier {q : QWindow R | qResetAt9 R q t}) = 0 := by
  change qWindowLaw R (frontier
    ({q : QWindow R | q.2.1 (xIndex R t) < 1 / 40} ∩
      (fun q : QWindow R ↦ q.2.2 (thetaIndex R t)) ⁻¹' resetArc9)) = 0
  exact null_frontier_inter (qWindowLaw_frontier_xCut_null R t)
    (qWindowLaw_frontier_thetaArc_null R t)

private lemma null_frontier_finset_iInter {R : ℕ} (s : Finset (Fin R)) :
    qWindowLaw R (frontier (⋂ t ∈ s, {q : QWindow R | ¬ qResetAt9 R q t})) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [show (⋂ t ∈ insert a s, {q : QWindow R | ¬ qResetAt9 R q t}) =
          {q : QWindow R | ¬ qResetAt9 R q a} ∩
            ⋂ t ∈ s, {q : QWindow R | ¬ qResetAt9 R q t} by
        ext q
        simp [ha]]
      apply null_frontier_inter
      · rw [show {q : QWindow R | ¬ qResetAt9 R q a} =
            {q : QWindow R | qResetAt9 R q a}ᶜ by ext; simp,
          frontier_compl]
        exact qWindowLaw_frontier_qResetAt9_null R a
      · exact ih

/-- The Portmanteau input: the stationary quotient-window law gives zero
mass to the frontier of the `D=9` no-reset event. -/
theorem qWindowLaw_frontier_qNoResetSet9_null (R : ℕ) :
    qWindowLaw R (frontier (qNoResetSet9 R)) = 0 := by
  rw [show qNoResetSet9 R =
      ⋂ t ∈ (Finset.univ : Finset (Fin R)), {q : QWindow R | ¬ qResetAt9 R q t} by
    ext q
    simp [qNoResetSet9]]
  exact null_frontier_finset_iInter Finset.univ

lemma windowNoResetSet9_eq_canonical (R : ℕ) :
    windowNoResetSet9 R = Prop64Carry.windowNoResetSet9 R := by
  ext w
  simp only [windowNoResetSet9, Prop64Carry.windowNoResetSet9, mem_setOf_eq]
  constructor
  · intro h t ht hreset
    apply h ⟨t, ht⟩
    norm_num [windowResetAt9, Prop64Carry.windowResetAt9, resetSet,
      div_eq_mul_inv] at hreset ⊢
    exact hreset
  · intro h t hreset
    apply h t t.isLt
    norm_num [windowResetAt9, Prop64Carry.windowResetAt9, resetSet,
      div_eq_mul_inv] at hreset ⊢
    exact hreset




/-- The quotient-coordinate version of the window projection. -/
def qWindowProj {R' R : ℕ} (h : R ≤ R') (q : QWindow R') : QWindow R :=
  (fun i => q.1 ⟨(i : ℕ) + (R' - R), by have := i.isLt; omega⟩,
   fun i => q.2.1 ⟨(i : ℕ) + (R' - R), by have := i.isLt; omega⟩,
   fun i => q.2.2 ⟨(i : ℕ) + (R' - R), by have := i.isLt; omega⟩)

lemma continuous_qWindowProj {R' R : ℕ} (h : R ≤ R') :
    Continuous (qWindowProj h) := by
  unfold qWindowProj
  fun_prop

lemma qWindowProj_quotientWindow {R' R : ℕ} (h : R ≤ R') (w : WindowSpace R') :
    qWindowProj h (quotientWindow R' w) = quotientWindow R (windowProj h w) := by
  rfl

/-- A `WindowSymbol` evaluated directly on quotient coordinates.  In particular,
this definition has no choice of representatives and hence no torus seam. -/
def qSymbolEval {R K : ℕ} (P : WindowSymbol R K) (q : QWindow R) : ℂ :=
  ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
    P.coeff (fun i => q.1 ⟨i, by have := i.isLt; omega⟩) r s *
      (fourier r (q.2.2 ⟨R, by omega⟩) * fourier s (q.2.2 ⟨R + 1, by omega⟩))

lemma continuous_qSymbolEval {R K : ℕ} (P : WindowSymbol R K) :
    Continuous (qSymbolEval P) := by
  unfold qSymbolEval
  refine continuous_finset_sum _ fun r _ => continuous_finset_sum _ fun s _ => ?_
  have hd0 : Continuous (fun a : Fin (2 * R + 1) → ℕ =>
      P.coeff (fun i => a ⟨i, by have := i.isLt; omega⟩) r s) :=
    continuous_of_discreteTopology
  have hd : Continuous (fun q : QWindow R =>
      P.coeff (fun i => q.1 ⟨i, by have := i.isLt; omega⟩) r s) :=
    hd0.comp continuous_fst
  have ht0 : Continuous (fun q : QWindow R => q.2.2 ⟨R, by omega⟩) := by fun_prop
  have ht1 : Continuous (fun q : QWindow R => q.2.2 ⟨R + 1, by omega⟩) := by fun_prop
  exact hd.mul
    (((fourier r).continuous.comp
      ht0).mul
    ((fourier s).continuous.comp
      ht1))

lemma qSymbolEval_quotientWindow {R K : ℕ} (P : WindowSymbol R K)
    (w : WindowSpace R) : qSymbolEval P (quotientWindow R w) = P.evalWindow w := by
  unfold qSymbolEval WindowSymbol.evalWindow quotientWindow
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  · apply congrArg (fun v => P.coeff v r s)
    funext i
    have hi : 0 ≤ (i : ℤ) - (R : ℤ) + (R : ℤ) ∧
        (i : ℤ) - (R : ℤ) + (R : ℤ) < 2 * (R : ℤ) + 1 := by omega
    simp only [windowWordOf, wA, dif_pos hi]
    apply congrArg w.1
    apply Fin.ext
    simp
  · rw [fourier_coe_apply, fourier_coe_apply]
    have hm1 : 0 ≤ (-1 : ℤ) + (R : ℤ) + 1 ∧
        (-1 : ℤ) + (R : ℤ) + 1 < 2 * (R : ℤ) + 2 := by omega
    have h0 : 0 ≤ (0 : ℤ) + (R : ℤ) + 1 ∧
        (0 : ℤ) + (R : ℤ) + 1 < 2 * (R : ℤ) + 2 := by omega
    simp only [wTh, dif_pos hm1, dif_pos h0]
    simp only [torusChar, ← Complex.exp_add]
    congr 1
    norm_num
    push_cast
    ring

/-- Display (56)'s nonnegative squared-error observable on the corrected
quotient window. -/
def qSquaredError (R M K : ℕ) (P : WindowSymbol (R + M) K)
    (q : QWindow (R + M)) : ℝ :=
  ‖qBwindowRep R (qWindowProj (Nat.le_add_right R M) q) - qSymbolEval P q‖ ^ 2

lemma qSquaredError_nonneg (R M K : ℕ) (P : WindowSymbol (R + M) K) (q) :
    0 ≤ qSquaredError R M K P q := sq_nonneg _

lemma measurable_qSquaredError (R M K : ℕ) (P : WindowSymbol (R + M) K) :
    Measurable (qSquaredError R M K P) := by
  unfold qSquaredError
  exact ((((measurable_qBwindowRep R).comp
    (continuous_qWindowProj (Nat.le_add_right R M)).measurable).sub
      (continuous_qSymbolEval P).measurable).norm.pow_const 2)

private lemma norm_qSymbolEval_le {R K : ℕ} (P : WindowSymbol R K) (q : QWindow R) :
    ‖qSymbolEval P q‖
      ≤ ∑ w ∈ P.words, ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖P.coeff w r s‖ := by
  classical
  have hstep : ‖qSymbolEval P q‖
      ≤ ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          ‖P.coeff (fun i => q.1 ⟨i, by have := i.isLt; omega⟩) r s‖ := by
    unfold qSymbolEval
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [norm_mul, norm_mul, fourier_apply, fourier_apply,
      Circle.norm_coe, Circle.norm_coe, mul_one, mul_one]
  refine hstep.trans ?_
  let word : Fin (2 * R) → ℕ := fun i => q.1 ⟨i, by have := i.isLt; omega⟩
  by_cases hw : word ∈ P.words
  · exact Finset.single_le_sum
      (f := fun w => ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖P.coeff w r s‖)
      (fun w _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hw
  · have hz : ∀ r s, P.coeff word r s = 0 := fun r s => P.coeff_support word r s hw
    have hzero : (∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          ‖P.coeff (fun i => q.1 ⟨i, by have := i.isLt; omega⟩) r s‖) = 0 := by
      simpa only [word, hz, norm_zero, Finset.sum_const_zero]
    rw [hzero]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- A uniform bound, stated in the exact shape needed by bounded
Portmanteau integration. -/
lemma qSquaredError_le (R M K : ℕ) (P : WindowSymbol (R + M) K) (q) :
    qSquaredError R M K P q ≤
      (45 / 8 + ∑ w ∈ P.words, ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖P.coeff w r s‖) ^ 2 := by
  let C := ∑ w ∈ P.words, ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖P.coeff w r s‖
  have hB : ‖qBwindowRep R (qWindowProj (Nat.le_add_right R M) q)‖ ≤ 45 / 8 := by
    simpa [qBwindowRep, Complex.norm_real] using
      abs_BwindowRep_le R (liftQWindow R (qWindowProj (Nat.le_add_right R M) q))
  have hP : ‖qSymbolEval P q‖ ≤ C := norm_qSymbolEval_le P q
  have hn : ‖qBwindowRep R (qWindowProj (Nat.le_add_right R M) q) - qSymbolEval P q‖
      ≤ 45 / 8 + C := (norm_sub_le _ _).trans (add_le_add hB hP)
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- The original real-valued display-(56) integrand. -/
def windowSquaredError (R M K : ℕ) (P : WindowSymbol (R + M) K)
    (w : WindowSpace (R + M)) : ℝ :=
  ‖(BwindowRep R (windowProj (Nat.le_add_right R M) w) : ℂ) - P.evalWindow w‖ ^ 2

lemma qSquaredError_comp_quotientWindow_ae (R M K : ℕ)
    (P : WindowSymbol (R + M) K) :
    (fun w => qSquaredError R M K P (quotientWindow (R + M) w))
      =ᵐ[windowLaw (R + M)] windowSquaredError R M K P := by
  let h := Nat.le_add_right R M
  have hlift0 := ae_liftQWindow_quotientWindow R
  rw [← windowProj_map_windowLaw h] at hlift0
  have hlift := (ae_map_iff (measurable_windowProj h).aemeasurable
    (measurableSet_eq_fun
      ((measurable_liftQWindow R).comp (measurable_quotientWindow R)) measurable_id)).mp hlift0
  filter_upwards [hlift] with w hw
  change liftQWindow R (quotientWindow R (windowProj h w)) = windowProj h w at hw
  simp only [qSquaredError, qWindowProj_quotientWindow, qBwindowRep, hw,
    qSymbolEval_quotientWindow, windowSquaredError]

theorem integral_qSquaredError_qWindowLaw (R M K : ℕ)
    (P : WindowSymbol (R + M) K) :
    ∫ q, qSquaredError R M K P q ∂qWindowLaw (R + M) =
      ∫ w, windowSquaredError R M K P w ∂windowLaw (R + M) := by
  rw [qWindowLaw, integral_map (measurable_quotientWindow (R + M)).aemeasurable
    (measurable_qSquaredError R M K P).aestronglyMeasurable]
  exact integral_congr_ae (qSquaredError_comp_quotientWindow_ae R M K P)

private lemma actualWindow_mem_windowSupport (R n j : ℕ) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) :
    actualWindow R α n j ∈ WindowSupport R := by
  constructor
  · intro i
    exact gaussIter_mem_Ioo hα hirr _
  · intro i
    exact theta_mem_Ico α n _

/-- The quotient actual-window integral is exactly the display-(56)
Lebesgue integral. -/
theorem integral_qSquaredError_qActualWindowLaw (R M K n j : ℕ)
    (P : WindowSymbol (R + M) K) (hj : R + M + 1 ≤ j) :
    ∫ q, qSquaredError R M K P q ∂qActualWindowLaw (R + M) n j =
      ∫ α in Ioo (0 : ℝ) 1,
        ‖(BremainderTrunc α n R j : ℂ) - P.at α n j‖ ^ 2 := by
  rw [qActualWindowLaw,
    integral_map (measurable_quotientWindow (R + M)).aemeasurable
      (measurable_qSquaredError R M K P).aestronglyMeasurable,
    actualWindowLaw]
  change (∫ w, (qSquaredError R M K P ∘ quotientWindow (R + M)) w
      ∂Measure.map (fun α => actualWindow (R + M) α n j)
        (volume.restrict (Ioo (0 : ℝ) 1))) = _
  rw [integral_map (measurable_actualWindow (R + M) n j).aemeasurable
    (((measurable_qSquaredError R M K P).comp
      (measurable_quotientWindow (R + M))).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_irrational_restrict]
    with α hα hirr
  simp only [Function.comp_apply]
  have hs := actualWindow_mem_windowSupport R n j hα hirr
  have hlift : liftQWindow R (quotientWindow R (actualWindow R α n j)) =
      actualWindow R α n j := liftQWindow_quotientWindow_of_mem_support hs
  rw [qSquaredError, qWindowProj_quotientWindow,
    windowProj_actualWindow (Nat.le_add_right R M) α n j hj,
    qBwindowRep, hlift, qSymbolEval_quotientWindow,
    BwindowRep_actualWindow R α n j (by omega) hα hirr,
    WindowSymbol.evalWindow_actualWindow P α n j hj]

private lemma hatMu0_theta_singleton_zero (c : ℝ) :
    hatMu0 {z : NatExtTorus | z.2.2 = c} = 0 :=
  hatMu0_theta_singleton_zero_noreset c

/-- The canonical `[0,1)` lift seam is null for every quotient-window torus
coordinate.  This is kept separate from the carry discontinuity null set. -/
private lemma qWindowLaw_theta_singleton (R : ℕ) (i : Fin (2 * R + 2))
    (c : UnitAddCircle) : qWindowLaw R {q | q.2.2 i = c} = 0 :=
  qWindowLaw_theta_singleton_noreset R i c

lemma qWindowLaw_torus_seam_null (R : ℕ) (i : Fin (2 * R + 2)) :
    qWindowLaw R {q | q.2.2 i = 0} = 0 :=
  qWindowLaw_theta_singleton R i 0

lemma qWindowLaw_ae_off_torus_seam (R : ℕ) :
    ∀ᵐ q ∂qWindowLaw R, ∀ i, q.2.2 i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  exact measure_eq_zero_iff_ae_notMem.mp (qWindowLaw_torus_seam_null R i)

lemma continuousAt_liftQWindow_of_off_seam {R : ℕ} {q : QWindow R}
    (hq : ∀ i, q.2.2 i ≠ 0) : ContinuousAt (liftQWindow R) q := by
  unfold liftQWindow
  refine continuousAt_fst.prodMk
    ((continuousAt_fst.comp continuousAt_snd).prodMk ?_)
  rw [continuousAt_pi]
  intro i
  have hc : ContinuousAt (fun y : QWindow R => y.2.2 i) q := by fun_prop
  have he : ContinuousAt
      (fun y : QWindow R => AddCircle.equivIco 1 0 (y.2.2 i)) q :=
    ContinuousAt.comp' (f := fun y : QWindow R => y.2.2 i)
      (AddCircle.continuousAt_equivIco 1 0 (hq i)) hc
  exact ContinuousAt.comp'
    (f := fun y : QWindow R => AddCircle.equivIco 1 0 (y.2.2 i))
    continuousAt_subtype_val he

lemma qBwindowRep_ae_continuous (R : ℕ) :
    ∀ᵐ q ∂qWindowLaw R, ContinuousAt (qBwindowRep R) q := by
  have hB : ∀ᵐ w ∂windowLaw R, ContinuousAt (BwindowRep R) w := by
    simpa only [mem_setOf_eq, not_not] using
      measure_eq_zero_iff_ae_notMem.mp (BwindowRep_ae_continuous_clean R)
  have hBlift : ∀ᵐ q ∂qWindowLaw R,
      ContinuousAt (BwindowRep R) (liftQWindow R q) := by
    rw [qWindowLaw]
    apply (ae_map_iff (measurable_quotientWindow R).aemeasurable
      ((measurableSet_of_continuousAt (BwindowRep R)).preimage
        (measurable_liftQWindow R))).mpr
    filter_upwards [ae_liftQWindow_quotientWindow R, hB] with w hw hcont
    simpa only [hw] using hcont
  filter_upwards [qWindowLaw_ae_off_torus_seam R, hBlift] with q hseam hcont
  unfold qBwindowRep
  exact Complex.continuous_ofReal.continuousAt.comp
    (hcont.comp (continuousAt_liftQWindow_of_off_seam hseam))

lemma qWindowProj_map_qWindowLaw {R' R : ℕ} (h : R ≤ R') :
    (qWindowLaw R').map (qWindowProj h) = qWindowLaw R := by
  rw [qWindowLaw, qWindowLaw,
    Measure.map_map (continuous_qWindowProj h).measurable (measurable_quotientWindow R'),
    ← windowProj_map_windowLaw h,
    Measure.map_map (measurable_quotientWindow R) (measurable_windowProj h)]
  congr 1

theorem qSquaredError_ae_continuous (R M K : ℕ)
    (P : WindowSymbol (R + M) K) :
    ∀ᵐ q ∂qWindowLaw (R + M), ContinuousAt (qSquaredError R M K P) q := by
  let h := Nat.le_add_right R M
  have hB := qBwindowRep_ae_continuous R
  rw [← qWindowProj_map_qWindowLaw h] at hB
  rw [ae_map_iff (continuous_qWindowProj h).aemeasurable
    (measurableSet_of_continuousAt (qBwindowRep R))] at hB
  filter_upwards [hB] with q hq
  unfold qSquaredError
  exact (((hq.comp (continuous_qWindowProj h).continuousAt).sub
    (continuous_qSymbolEval P).continuousAt).norm.pow 2)

private instance qWindowLaw_isProbabilityMeasure (R : ℕ) :
    IsProbabilityMeasure (qWindowLaw R) := by
  constructor
  rw [qWindowLaw, Measure.map_apply_of_aemeasurable
    (measurable_quotientWindow R).aemeasurable MeasurableSet.univ]
  simp

private instance qActualWindowLaw_isProbabilityMeasure (R n j : ℕ) :
    IsProbabilityMeasure (qActualWindowLaw R n j) := by
  constructor
  rw [qActualWindowLaw, Measure.map_apply_of_aemeasurable
    (measurable_quotientWindow R).aemeasurable MeasurableSet.univ]
  simp only [preimage_univ]
  rw [
    actualWindowLaw, Measure.map_apply_of_aemeasurable
      (measurable_actualWindow R n j).aemeasurable MeasurableSet.univ]
  simp [Real.volume_Ioo]

private def qWindowProbability (R : ℕ) : ProbabilityMeasure (QWindow R) :=
  ⟨qWindowLaw R, inferInstance⟩

private def qActualWindowProbability (R n j : ℕ) : ProbabilityMeasure (QWindow R) :=
  ⟨qActualWindowLaw R n j, inferInstance⟩

private lemma real_boundedContinuous_transfer (R : ℕ)
    (g : QWindow R →ᵇ ℝ) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      |(∫ q, g q ∂qActualWindowLaw R n j) - ∫ q, g q ∂qWindowLaw R| < ε := by
  intro ε hε
  let gc : QWindow R →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun q ↦ (g q : ℂ))
    (Complex.continuous_ofReal.comp g.continuous) ‖g‖
    (fun q ↦ by simpa [Complex.norm_real] using g.norm_coe_le_norm q)
  have hbulk := Prop64.boundedContinuous_transfer_clean R gc ε hε
  filter_upwards [hbulk] with n hn
  intro j hj
  have hact :
      (∫ q, g q ∂qActualWindowLaw R n j) =
        ∫ α in Ioo (0 : ℝ) 1, g (actualQWindow R α n j) := by
    rw [qActualWindowLaw, actualWindowLaw,
      Measure.map_map (measurable_quotientWindow R) (measurable_actualWindow R n j),
      integral_map
        ((measurable_quotientWindow R).comp (measurable_actualWindow R n j)).aemeasurable
        g.continuous.measurable.aestronglyMeasurable]
    rfl
  have hc := hn j hj
  have hactC : (∫ α in Ioo (0 : ℝ) 1, gc (actualQWindow R α n j)) =
      Complex.ofReal (∫ α in Ioo (0 : ℝ) 1, g (actualQWindow R α n j)) := by
    change (∫ α in Ioo (0 : ℝ) 1,
      ((g (actualQWindow R α n j) : ℝ) : ℂ)) = _
    exact integral_complex_ofReal
  have hstatC : (∫ q, gc q ∂qWindowLaw R) =
      Complex.ofReal (∫ q, g q ∂qWindowLaw R) := by
    change (∫ q, ((g q : ℝ) : ℂ) ∂qWindowLaw R) = _
    exact integral_complex_ofReal
  rw [hactC, hstatC, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at hc
  simpa only [hact] using hc

private lemma eLpNorm_two_eq_integral_norm_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℂ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 2
  simp only [ENNReal.toReal_ofNat]
  rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  norm_num

/-- The display-(56) squared-error transfer, obtained from the proved
full-state convergence and bounded a.e.-continuous Portmanteau. -/
theorem squaredErrorBulkTransferProvider :
    Prop64SquaredError.SquaredErrorBulkTransferProvider := by
  intro R M K P δRM hδ hnorm
  let R' := R + M
  let μ : ProbabilityMeasure (QWindow R') := qWindowProbability R'
  let μs : ℕ → ℕ → ProbabilityMeasure (QWindow R') :=
    fun n j ↦ qActualWindowProbability R' n j
  have hbulk : ∀ g : QWindow R' →ᵇ ℝ, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ j ∈ (bulkJ n : Set ℕ),
        |(∫ q, g q ∂(μs n j : Measure (QWindow R'))) -
          ∫ q, g q ∂(μ : Measure (QWindow R'))| < ε := by
    intro g ε hε
    simpa only [μs, μ, qActualWindowProbability, qWindowProbability,
      ProbabilityMeasure.coe_mk] using real_boundedContinuous_transfer R' g ε hε
  have hport := ProbabilityMeasure.bulk_uniform_integral_of_ae_continuous
    μ μs (fun n ↦ (bulkJ n : Set ℕ)) hbulk
    (measurable_qSquaredError R M K P)
    (qSquaredError_ae_continuous R M K P)
    (fun q ↦ qSquaredError_nonneg R M K P q)
    (fun q ↦ qSquaredError_le R M K P q)
  let F : WindowSpace R' → ℂ := fun w ↦
    ((BwindowRep R (windowProj (Nat.le_add_right R M) w) : ℂ) - P.evalWindow w)
  have hFmeas : Measurable F :=
    (Complex.measurable_ofReal.comp
      ((measurable_BwindowRep R).comp
        (measurable_windowProj (Nat.le_add_right R M)))).sub
      (measurable_evalWindow P)
  have hFmem : MemLp F 2 (windowLaw R') := by
    refine ⟨hFmeas.aestronglyMeasurable, ?_⟩
    rw [hnorm]
    exact ENNReal.ofReal_lt_top
  have hsqrt : Real.sqrt (∫ w, ‖F w‖ ^ 2 ∂windowLaw R') = δRM := by
    have heq := (eLpNorm_two_eq_integral_norm_sq hFmem).symm.trans hnorm
    have hre := congrArg ENNReal.toReal heq
    simpa [ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ENNReal.toReal_ofReal hδ] using hre
  have hint_nonneg : 0 ≤ ∫ w, ‖F w‖ ^ 2 ∂windowLaw R' :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hint : ∫ w, ‖F w‖ ^ 2 ∂windowLaw R' = δRM ^ 2 := by
    calc
      (∫ w, ‖F w‖ ^ 2 ∂windowLaw R') =
          (Real.sqrt (∫ w, ‖F w‖ ^ 2 ∂windowLaw R')) ^ 2 :=
        (Real.sq_sqrt hint_nonneg).symm
      _ = δRM ^ 2 := by rw [hsqrt]
  intro η hη
  have hp := hport η hη
  filter_upwards [hp, Prop64.eventually_bulk_radius R'] with n hn hroom
  intro j hj
  have hn' := hn j hj
  rw [show (μs n j : Measure (QWindow R')) = qActualWindowLaw R' n j by rfl,
    show (μ : Measure (QWindow R')) = qWindowLaw R' by rfl,
    integral_qSquaredError_qActualWindowLaw R M K n j P
      (hroom j hj),
    integral_qSquaredError_qWindowLaw R M K P] at hn'
  simpa only [windowSquaredError, F, R', hint] using hn'

/-- The finite-boundary no-reset specialization of Lemma 6.3. -/
theorem noResetIndicatorTransfer9 (R : ℕ) :
    Prop64Carry.NoResetIndicatorTransfer9 R := by
  let μ : ProbabilityMeasure (QWindow R) := qWindowProbability R
  let μs : ℕ → ℕ → ProbabilityMeasure (QWindow R) :=
    fun n j ↦ qActualWindowProbability R n j
  have hbulk : ∀ g : QWindow R →ᵇ ℝ, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ j ∈ (bulkJ n : Set ℕ),
        |(∫ q, g q ∂(μs n j : Measure (QWindow R))) -
          ∫ q, g q ∂(μ : Measure (QWindow R))| < ε := by
    intro g ε hε
    simpa only [μs, μ, qActualWindowProbability, qWindowProbability,
      ProbabilityMeasure.coe_mk] using real_boundedContinuous_transfer R g ε hε
  have hmeasure := ProbabilityMeasure.bulk_uniform_measure_of_nullFrontier
    μ μs (fun n ↦ (bulkJ n : Set ℕ)) hbulk
    (qWindowLaw_frontier_qNoResetSet9_null R)
  intro ε hε
  have hevent := hmeasure ε hε
  filter_upwards [hevent] with n hn
  intro j hj
  have hm := hn j hj
  have hactual :
      (qActualWindowLaw R n j).real (qNoResetSet9 R) =
        (volume.restrict (Ioo (0 : ℝ) 1)).real
          ((fun α ↦ actualWindow R α n j) ⁻¹'
            Prop64Carry.windowNoResetSet9 R) := by
    rw [Measure.real, qActualWindowLaw_qNoResetSet9_eq_window,
      windowNoResetSet9_eq_canonical, actualWindowLaw,
      Measure.map_apply (measurable_actualWindow R n j)
        (Prop64Carry.measurableSet_windowNoResetSet9 R)]
    rfl
  have hstationary :
      (qWindowLaw R).real (qNoResetSet9 R) =
        (windowLaw R).real (Prop64Carry.windowNoResetSet9 R) := by
    rw [Measure.real, qWindowLaw_qNoResetSet9_eq_window,
      windowNoResetSet9_eq_canonical]
    rfl
  change |(qActualWindowLaw R n j).real (qNoResetSet9 R) -
    (qWindowLaw R).real (qNoResetSet9 R)| < ε at hm
  rw [hactual, hstationary] at hm
  rw [Prop64Carry.integral_noResetIndicator9_actual,
    show (∫ w, Prop64Carry.noResetIndicator9 R w ∂windowLaw R) =
      (((windowLaw R).real (Prop64Carry.windowNoResetSet9 R) : ℝ) : ℂ) by
        have hi := integral_indicator_const (μ := windowLaw R) (1 : ℂ)
          (Prop64Carry.measurableSet_windowNoResetSet9 R)
        simpa [Prop64Carry.noResetIndicator9] using hi,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hm

assert_no_sorry qSquaredError_nonneg
assert_no_sorry measurable_qSquaredError
assert_no_sorry qSquaredError_le
assert_no_sorry integral_qSquaredError_qWindowLaw
assert_no_sorry integral_qSquaredError_qActualWindowLaw
assert_no_sorry qWindowLaw_torus_seam_null
assert_no_sorry qSquaredError_ae_continuous
assert_no_sorry squaredErrorBulkTransferProvider
assert_no_sorry noResetIndicatorTransfer9

end

end Kwon1002.Prop64SpecialTransfers
