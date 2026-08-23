import Kwon1002.DigitLaw
import Kwon1002.StationaryIdentity31
import Mathlib.Util.AssertNoSorry

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace Kwon1002

noncomputable section

def NonIntegral (x : ℝ) : Prop := ∀ n : ℤ, x ≠ (n : ℝ)

lemma continuousAt_ceil_of_nonIntegral {x : ℝ} (hx : NonIntegral x) :
    ContinuousAt (fun y : ℝ => (⌈y⌉ : ℝ)) x := by
  have hlt : x < (⌈x⌉ : ℝ) := lt_of_le_of_ne (Int.le_ceil x) (hx ⌈x⌉)
  have hlo : (⌈x⌉ : ℝ) - 1 < x := by
    rw [sub_lt_iff_lt_add]
    exact Int.ceil_lt_add_one x
  exact (continuousOn_ceil ⌈x⌉).continuousAt (Ioc_mem_nhds hlo hlt)

lemma continuousAt_fract_of_nonIntegral {x : ℝ} (hx : NonIntegral x) :
    ContinuousAt Int.fract x := continuousAt_fract (hx ⌊x⌋)

lemma continuous_W : Continuous W := by
  unfold W
  let f : ℝ → ℝ := fun u => u * (1 - u) / 2
  have hf : Continuous f := by fun_prop
  simpa [Function.comp_def, f] using
    hf.continuousOn.comp_fract'' (by simp [f] : f 0 = f 1)

lemma continuous_wA {R : ℕ} (t : ℤ) : Continuous (fun w : WindowSpace R => wA w t) := by
  unfold wA
  split <;> fun_prop

lemma continuous_wX {R : ℕ} (t : ℤ) : Continuous (fun w : WindowSpace R => wX w t) := by
  unfold wX
  split <;> fun_prop

lemma continuous_wTh {R : ℕ} (t : ℤ) : Continuous (fun w : WindowSpace R => wTh w t) := by
  unfold wTh
  split <;> fun_prop

def CarryRegular (R : ℕ) (w : WindowSpace R) : Prop :=
  wX w 0 ≠ 0 ∧
  (∀ k < R, ∀ d : ℤ,
    NonIntegral (wX w (-(R : ℤ) + k) * ((d : ℝ) + wTh w (-(R : ℤ) + k - 1))
      - wTh w (-(R : ℤ) + k))) ∧
  (∀ d : ℤ, NonIntegral
    (wTh w 0 - wX w 0 * ((d : ℝ) + wTh w (-1))))

lemma continuousAt_windowCarryCast_of_regular {R : ℕ} {w : WindowSpace R}
    (hw : CarryRegular R w) :
    ∀ k, k ≤ R → ContinuousAt (fun v => ((windowCarry R v k : ℤ) : ℝ)) w := by
  intro k
  induction k with
  | zero => intro _; simp only [windowCarry]; exact continuousAt_const
  | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hinner : ContinuousAt
          (fun v : WindowSpace R =>
            wX v (-(R : ℤ) + k) * (((windowCarry R v k : ℤ) : ℝ)
              + wTh v (-(R : ℤ) + k - 1)) - wTh v (-(R : ℤ) + k)) w :=
        (((continuous_wX _).continuousAt.mul
          (hprev.add (continuous_wTh _).continuousAt)).sub
          (continuous_wTh _).continuousAt)
      simpa only [windowCarry, carryMap] using
        (continuousAt_ceil_of_nonIntegral
          (hw.2.1 k (by omega) (windowCarry R w k))).comp_of_eq hinner rfl

lemma continuousAt_BwindowRep_of_regular {R : ℕ} {w : WindowSpace R}
    (hw : CarryRegular R w) : ContinuousAt (BwindowRep R) w := by
  have hcarry := continuousAt_windowCarryCast_of_regular hw R le_rfl
  have harg : ContinuousAt
      (fun v : WindowSpace R =>
        wTh v 0 - wX v 0 * (((windowCarry R v R : ℤ) : ℝ) + wTh v (-1))) w :=
    (continuous_wTh 0).continuousAt.sub
      ((continuous_wX 0).continuousAt.mul
        (hcarry.add (continuous_wTh (-1)).continuousAt))
  have hfract := (continuousAt_fract_of_nonIntegral
    (hw.2.2 (windowCarry R w R))).comp_of_eq harg rfl
  have hden : ContinuousAt (fun v : WindowSpace R => 2 * wX v 0) w :=
    continuousAt_const.mul (continuous_wX 0).continuousAt
  have hraw : ContinuousAt (Bwindow R) w := by
    unfold Bwindow carryU Phi
    exact (((hfract.mul
        ((continuousAt_const : ContinuousAt (fun _ : WindowSpace R => (1 : ℝ)) w).sub hfract)).div₀
          hden (mul_ne_zero (by norm_num) hw.1)).sub (hfract.div_const 2)).sub
      ((((continuous_of_discreteTopology : Continuous fun n : ℕ => (n : ℝ)).comp
          (continuous_wA 0)).continuousAt.mul
        (continuous_W.continuousAt.comp (continuous_wTh 0).continuousAt)))
  unfold BwindowRep
  exact continuousAt_const.max (continuousAt_const.min hraw)

def StationaryCarryRegular (R : ℕ) : Prop :=
  ∀ᵐ z ∂hatMu0, CarryRegular R (stationaryWindow R z)

lemma BwindowRep_ae_continuous_of_stationaryCarryRegular (R : ℕ)
    (hreg : StationaryCarryRegular R) :
    windowLaw R {w | ¬ ContinuousAt (BwindowRep R) w} = 0 := by
  rw [windowLaw]
  change (Measure.map (stationaryWindow R) hatMu0)
    ({w | ContinuousAt (BwindowRep R) w}ᶜ) = 0
  rw [Measure.map_apply (measurable_stationaryWindow R)
    (measurableSet_of_continuousAt (BwindowRep R)).compl,
    measure_eq_zero_iff_ae_notMem]
  filter_upwards [hreg] with z hz
  simpa only [mem_preimage, mem_compl_iff, mem_setOf_eq, not_not] using
    continuousAt_BwindowRep_of_regular hz

def torusBoundary (x : ℝ) (d n : ℤ) : Set (ℝ × ℝ) :=
  {q | x * ((d : ℝ) + q.1) - q.2 = (n : ℝ)}

lemma measurableSet_torusBoundary (x : ℝ) (d n : ℤ) :
    MeasurableSet (torusBoundary x d n) := by
  exact measurableSet_eq_fun
    ((measurable_const.mul (measurable_const.add measurable_fst)).sub measurable_snd)
    measurable_const

lemma torusBoundary_null (x : ℝ) (d n : ℤ) :
    (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) (torusBoundary x d n) = 0 := by
  rw [NatExtMeasure.restrict_unitSq_eq_prod]
  rw [Measure.measure_prod_null (measurableSet_torusBoundary x d n)]
  filter_upwards with r
  have hpre : Prod.mk r ⁻¹' torusBoundary x d n = {x * ((d : ℝ) + r) - (n : ℝ)} := by
    ext s
    simp only [mem_preimage, torusBoundary, mem_setOf_eq, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  rw [hpre]
  exact measure_singleton _

def stateBoundary (d n : ℤ) : Set NatExtTorus :=
  {z | z.1.1 * ((d : ℝ) + z.2.1) - z.2.2 = (n : ℝ)}

lemma measurableSet_stateBoundary (d n : ℤ) : MeasurableSet (stateBoundary d n) := by
  exact measurableSet_eq_fun
    (((measurable_fst.comp measurable_fst).mul
      (measurable_const.add (measurable_fst.comp measurable_snd))).sub
        (measurable_snd.comp measurable_snd)) measurable_const

lemma stateBoundary_null (d n : ℤ) : hatMu0 (stateBoundary d n) = 0 := by
  rw [hatMu0_eq_prod]
  rw [Measure.measure_prod_null (measurableSet_stateBoundary d n)]
  filter_upwards with p
  simpa only [stateBoundary, torusBoundary, preimage_setOf_eq] using
    torusBoundary_null p.1 d n

lemma ae_state_nonIntegral :
    ∀ᵐ z ∂hatMu0, ∀ d : ℤ,
      NonIntegral (z.1.1 * ((d : ℝ) + z.2.1) - z.2.2) := by
  simp only [NonIntegral]
  rw [ae_all_iff]
  intro d
  rw [ae_all_iff]
  intro n
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (stateBoundary_null d n)] with z hz
  simpa only [stateBoundary, mem_setOf_eq] using hz

lemma ae_state_nonIntegral_zpow (t : ℤ) :
    ∀ᵐ z ∂hatMu0, ∀ d : ℤ,
      NonIntegral ((hatSzpow t z).1.1 * ((d : ℝ) + (hatSzpow t z).2.1)
        - (hatSzpow t z).2.2) := by
  exact (hatSzpow_measurePreserving t).quasiMeasurePreserving.ae ae_state_nonIntegral

lemma stationaryCarryRegular (R : ℕ) :
    StationaryCarryRegular R := by
  have hx : ∀ᵐ z ∂hatMu0, (hatSzpow 0 z).1.1 ≠ 0 := by
    filter_upwards [CarryGraph.hatMu0_ae_goodT] with z hz
    simpa [hatSzpow] using ne_of_gt hz.1.1.1
  have hsteps : ∀ k : ℕ, k < R →
      ∀ᵐ z ∂hatMu0, ∀ d : ℤ,
        NonIntegral
          (wX (stationaryWindow R z) (-(R : ℤ) + k) *
              ((d : ℝ) + wTh (stationaryWindow R z) (-(R : ℤ) + k - 1)) -
            wTh (stationaryWindow R z) (-(R : ℤ) + k)) := by
    intro k hk
    have hreg := ae_state_nonIntegral_zpow (-(R : ℤ) + k)
    filter_upwards [CarryGraph.hatMu0_ae_goodT, hreg] with z hz hzreg
    intro d
    rw [wX_stationaryWindow R z (by omega) (by omega),
      wTh_stationaryWindow R z (by omega) (by omega),
      wTh_stationaryWindow R z (by omega) (by omega),
      ← StationaryIdentity31.hatSzpow_fst_torus hz (-(R : ℤ) + k)]
    exact hzreg d
  have hfinal : ∀ᵐ z ∂hatMu0, ∀ d : ℤ,
      NonIntegral
        (wTh (stationaryWindow R z) 0 - wX (stationaryWindow R z) 0 *
          ((d : ℝ) + wTh (stationaryWindow R z) (-1))) := by
    have hreg := ae_state_nonIntegral_zpow 0
    filter_upwards [CarryGraph.hatMu0_ae_goodT, hreg] with z hz hzreg
    intro d n
    have htor : (hatSzpow (-1) z).2.2 = (hatSzpow 0 z).2.1 := by
      simpa using (StationaryIdentity31.hatSzpow_fst_torus hz 0).symm
    rw [wX_stationaryWindow R z (by omega) (by omega),
      wTh_stationaryWindow R z (by omega) (by omega),
      wTh_stationaryWindow R z (by omega) (by omega),
      htor]
    intro heq
    exact hzreg d (-n) (by push_cast; linarith)
  have hstepsAll : ∀ᵐ z ∂hatMu0, ∀ k : ℕ, k < R → ∀ d : ℤ,
      NonIntegral
        (wX (stationaryWindow R z) (-(R : ℤ) + k) *
            ((d : ℝ) + wTh (stationaryWindow R z) (-(R : ℤ) + k - 1)) -
          wTh (stationaryWindow R z) (-(R : ℤ) + k)) := by
    rw [ae_all_iff]
    intro k
    by_cases hk : k < R
    · exact (hsteps k hk).mono fun _ hz _ => hz
    · exact Eventually.of_forall fun _ hk' => (hk hk').elim
  filter_upwards [hx, hfinal, hstepsAll] with z hx hfinal hsteps
  refine ⟨?_, ?_, hfinal⟩
  · simpa [wX_stationaryWindow, hatSzpow] using hx
  · intro k hk d
    exact hsteps k hk d

theorem BwindowRep_ae_continuous_clean (R : ℕ) :
    windowLaw R {w | ¬ ContinuousAt (BwindowRep R) w} = 0 :=
  BwindowRep_ae_continuous_of_stationaryCarryRegular R (stationaryCarryRegular R)

assert_no_sorry BwindowRep_ae_continuous_clean

end

end Kwon1002
