import Kwon1002.Prop42
import Kwon1002.Section6Skeleton

/-!
# S6W, the v5 window laws `μ_R` and the projections `π_{R',R}`

Working file for the window bookkeeping of §6 of v5
(`manuscript/erdos1002_cauchy_limit_revision_v5.tex`, lines 1152-1165):
the window space `X_R` of (51), the actual window (52), the stationary
window `stationaryWindow`, the laws `μ_R = windowLaw R` and
`η^{(R)}_{n,j} = actualWindowLaw R n j`, the coordinate projections
`π_{R',R} = windowProj`, and the consistency
`(π_{R',R})_* μ_{R'} = μ_R`.

The targets of `Kwon1002/Section6Skeleton.lean` reproduced here
token-identically (definitions and theorem statements copied verbatim and
diffed) are

* the definitions `NatExtTorus`, `natExtMap`, `natExtInv`, `hatS`,
  `hatSinv`, `WindowSpace`, `wA`, `wX`, `wTh`, `actualWindow`,
  `hatSzpow`, `stationaryWindow`, `windowLaw`, `actualWindowLaw`,
  `windowProj`;
* `measurable_windowProj`, `windowProj_actualWindow`,
  `windowProj_stationaryWindow`, `measurable_stationaryWindow`,
  `windowProj_map_windowLaw`.

All five theorems are proved outright here, with no `sorry` and no
appeal to a sorried result.  The skeleton had `measurable_stationaryWindow`
open and the other four written but never compiled.

The only input beyond `Kwon1002.Section4` is the measurability layer
already in the tree: `Kwon1002.measurable_gaussIter`,
`Kwon1002.measurable_digitCast`, `Kwon1002.measurable_theta` of
`SmallJumps.lean` and `Kwon1002.Prop42.measurable_digitNat` of
`Prop42.lean`.  Merging the contents of this file into
`Section6Skeleton.lean` therefore means adding `import Kwon1002.Prop42`
there; that creates no cycle, since `Prop42` imports only `Section4` and
`SmallJumps`.

## What is proved beyond the five targets

The same bookkeeping for the actual windows and for the window
coordinate readers, which §6 needs downstream and which is not stated in
the skeleton:

* `measurable_wA`, `measurable_wX`, `measurable_wTh`, so that any
  function built from the window coordinates is measurable;
* `measurable_actualWindow`, which is what makes `actualWindowLaw` a
  pushforward of Lebesgue measure along a measurable map rather than
  along an arbitrary one;
* `windowProj_map_actualWindowLaw`, the actual-window analogue of
  `windowProj_map_windowLaw`, valid on the range `R' + 1 ≤ j` where the
  radius-`R'` window is genuinely defined;
* `measurable_hatS`, `measurable_hatSinv`, `measurable_hatSzpow`, the
  measurability of the cocycle (49) and of its integer powers;
* `measurable_windowCarry`, the measurability of the truncated carry
  read off a window.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Kwon1002

noncomputable section

/-! ## The Gauss-torus system

Definitions copied verbatim from `Section6Skeleton.lean`. -/




/-! ### Measurability of the cocycle -/

/-- The Gauss map is measurable.  `gaussMap x = Int.fract x⁻¹` by
definition, so this is `Measurable.inv` followed by `Measurable.fract`. -/
lemma measurable_gaussMap' : Measurable gaussMap := by
  unfold gaussMap
  exact measurable_id.inv.fract

lemma measurable_natExtMap : Measurable natExtMap := by
  unfold natExtMap
  refine Measurable.prodMk (measurable_gaussMap'.comp measurable_fst) ?_
  exact (((measurable_digitCast 0).comp measurable_fst).add measurable_snd).inv

lemma measurable_natExtInv : Measurable natExtInv := by
  unfold natExtInv
  refine Measurable.prodMk ?_ (measurable_gaussMap'.comp measurable_snd)
  exact (((measurable_digitCast 0).comp measurable_snd).add measurable_fst).inv

lemma measurable_hatS : Measurable hatS := by
  unfold hatS
  refine Measurable.prodMk (measurable_natExtMap.comp measurable_fst) ?_
  refine Measurable.prodMk (measurable_snd.comp measurable_snd) ?_
  exact ((measurable_fst.comp measurable_snd).sub
    (((measurable_digitCast 0).comp (measurable_fst.comp measurable_fst)).mul
      (measurable_snd.comp measurable_snd))).fract

lemma measurable_hatSinv : Measurable hatSinv := by
  unfold hatSinv
  refine Measurable.prodMk (measurable_natExtInv.comp measurable_fst) ?_
  refine Measurable.prodMk ?_ (measurable_fst.comp measurable_snd)
  exact ((measurable_snd.comp measurable_snd).add
    (((measurable_digitCast 0).comp (measurable_snd.comp measurable_fst)).mul
      (measurable_fst.comp measurable_snd))).fract

/-! ## The window space -/



theorem measurable_windowProj {R' R : ℕ} (h : R ≤ R') :
    Measurable (windowProj (R' := R') (R := R) h) := by
  unfold windowProj
  apply Measurable.prodMk
  · exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_fst
  · apply Measurable.prodMk
    · exact measurable_pi_lambda _ fun i =>
        (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
    · exact measurable_pi_lambda _ fun i =>
        (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)

/-- The projection is compatible with the actual windows: whenever both
are defined, `π_{R',R}(W^{(R')}_{n,j}) = W^{(R)}_{n,j}` (v5 line 1165). -/
theorem windowProj_actualWindow {R' R : ℕ} (h : R ≤ R') (α : ℝ) (n j : ℕ)
    (hj : R' + 1 ≤ j) :
    windowProj h (actualWindow R' α n j) = actualWindow R α n j := by
  have hd : ∀ i : ℕ, i < 2 * R + 1 → j + (i + (R' - R)) - R' = j + i - R := by
    intro i hi; omega
  have ht : ∀ i : ℕ, i < 2 * R + 2 → j + (i + (R' - R)) - R' - 1 = j + i - R - 1 := by
    intro i hi; omega
  simp only [windowProj, actualWindow, Prod.mk.injEq, Fin.val_mk]
  refine ⟨funext fun i => ?_, funext fun i => ?_, funext fun i => ?_⟩
  · rw [hd i i.isLt]
  · rw [hd i i.isLt]
  · rw [ht i i.isLt]

/-- The projection is compatible with the stationary windows. -/
theorem windowProj_stationaryWindow {R' R : ℕ} (h : R ≤ R') (z : NatExtTorus) :
    windowProj h (stationaryWindow R' z) = stationaryWindow R z := by
  have hd : ∀ i : ℕ, ((i + (R' - R) : ℕ) : ℤ) - (R' : ℤ) = (i : ℤ) - (R : ℤ) := by
    intro i; omega
  have ht : ∀ i : ℕ,
      ((i + (R' - R) : ℕ) : ℤ) - (R' : ℤ) - 1 = (i : ℤ) - (R : ℤ) - 1 := by
    intro i; omega
  simp only [windowProj, stationaryWindow, Prod.mk.injEq, Fin.val_mk]
  refine ⟨funext fun i => ?_, funext fun i => ?_, funext fun i => ?_⟩
  · rw [hd i]
  · rw [hd i]
  · rw [ht i]

/-- Every integer power of the cocycle is measurable.  The sign test in
`hatSzpow` does not involve the point, so the two branches are separate
iterates of `hatS` and of `hatSinv`. -/
lemma measurable_hatSzpow (t : ℤ) : Measurable (hatSzpow t) := by
  by_cases h : (0 : ℤ) ≤ t
  · have he : hatSzpow t = hatS^[t.toNat] := by
      funext z; simp [hatSzpow, h]
    rw [he]
    exact measurable_hatS.iterate _
  · have he : hatSzpow t = hatSinv^[(-t).toNat] := by
      funext z; simp [hatSzpow, h]
    rw [he]
    exact measurable_hatSinv.iterate _

theorem measurable_stationaryWindow (R : ℕ) : Measurable (stationaryWindow R) := by
  unfold stationaryWindow
  apply Measurable.prodMk
  · exact measurable_pi_lambda _ fun i =>
      (Prop42.measurable_digitNat 0).comp
        (measurable_fst.comp (measurable_fst.comp (measurable_hatSzpow _)))
  · apply Measurable.prodMk
    · exact measurable_pi_lambda _ fun i =>
        measurable_fst.comp (measurable_fst.comp (measurable_hatSzpow _))
    · exact measurable_pi_lambda _ fun i =>
        measurable_snd.comp (measurable_snd.comp (measurable_hatSzpow _))

/-- `μ_R` is a probability measure: the pushforward of the probability
measure `μ̂₀` (`isProbabilityMeasure_hatMu0`) along the measurable
stationary window. -/
instance isProbabilityMeasure_windowLaw (R : ℕ) :
    IsProbabilityMeasure (windowLaw R) := by
  show IsProbabilityMeasure (hatMu0.map (stationaryWindow R))
  exact Measure.isProbabilityMeasure_map (measurable_stationaryWindow R).aemeasurable

/-- **(`(π_{R',R})_* μ_{R'} = μ_R`)**, v5 line 1165. -/
theorem windowProj_map_windowLaw {R' R : ℕ} (h : R ≤ R') :
    (windowLaw R').map (windowProj h) = windowLaw R := by
  rw [windowLaw, windowLaw, Measure.map_map (measurable_windowProj h)
    (measurable_stationaryWindow R')]
  congr 1
  exact funext fun z => windowProj_stationaryWindow h z

/-! ## The window coordinate readers and the actual window law

Not part of the skeleton, but needed by everything downstream that reads
a window coordinate (`Bwindow`, `windowWordOf`, `WindowSymbol.evalWindow`)
or that pushes the actual window law forward. -/

lemma measurable_wA (R : ℕ) (t : ℤ) : Measurable fun w : WindowSpace R => wA w t := by
  by_cases h : 0 ≤ t + (R : ℤ) ∧ t + (R : ℤ) < 2 * (R : ℤ) + 1
  · simp only [wA, dif_pos h]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [wA, dif_neg h]
    exact measurable_const

lemma measurable_wX (R : ℕ) (t : ℤ) : Measurable fun w : WindowSpace R => wX w t := by
  by_cases h : 0 ≤ t + (R : ℤ) ∧ t + (R : ℤ) < 2 * (R : ℤ) + 1
  · simp only [wX, dif_pos h]
    exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
  · simp only [wX, dif_neg h]
    exact measurable_const

lemma measurable_wTh (R : ℕ) (t : ℤ) : Measurable fun w : WindowSpace R => wTh w t := by
  by_cases h : 0 ≤ t + (R : ℤ) + 1 ∧ t + (R : ℤ) + 1 < 2 * (R : ℤ) + 2
  · simp only [wTh, dif_pos h]
    exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)
  · simp only [wTh, dif_neg h]
    exact measurable_const

/-- The actual window is a measurable function of `α`, so `η^{(R)}_{n,j}`
is an honest pushforward of Lebesgue measure on `(0,1)`. -/
theorem measurable_actualWindow (R n j : ℕ) :
    Measurable fun α : ℝ => actualWindow R α n j := by
  unfold actualWindow
  apply Measurable.prodMk
  · exact measurable_pi_lambda _ fun i => Prop42.measurable_digitNat _
  · apply Measurable.prodMk
    · exact measurable_pi_lambda _ fun i => measurable_gaussIter _
    · exact measurable_pi_lambda _ fun i => measurable_theta n _

/-- The actual-window analogue of `windowProj_map_windowLaw`, on the
range `R' + 1 ≤ j` where the radius-`R'` window is defined. -/
theorem windowProj_map_actualWindowLaw {R' R : ℕ} (h : R ≤ R') (n j : ℕ)
    (hj : R' + 1 ≤ j) :
    (actualWindowLaw R' n j).map (windowProj h) = actualWindowLaw R n j := by
  rw [actualWindowLaw, actualWindowLaw, Measure.map_map (measurable_windowProj h)
    (measurable_actualWindow R' n j)]
  congr 1
  exact funext fun α => windowProj_actualWindow h α n j hj

/-! ## The truncated carry as a window observable -/



/-- Each step of the truncated carry is a measurable function of the
window: `φ` is a ceiling of a polynomial in the window coordinates and in
the previous carry, and the `ℤ`-valued previous carry enters through the
countable-domain cast `ℤ → ℝ`. -/
theorem measurable_windowCarry (R : ℕ) (k : ℕ) :
    Measurable fun w : WindowSpace R => windowCarry R w k := by
  induction k with
  | zero =>
      simp only [windowCarry]
      exact measurable_const
  | succ k ih =>
      have hcast : Measurable fun w : WindowSpace R => ((windowCarry R w k : ℤ) : ℝ) :=
        (measurable_from_top (f := fun m : ℤ => (m : ℝ))).comp ih
      have : Measurable fun w : WindowSpace R =>
          wX w (-(R : ℤ) + k) * (((windowCarry R w k : ℤ) : ℝ) + wTh w (-(R : ℤ) + k - 1))
            - wTh w (-(R : ℤ) + k) :=
        ((measurable_wX R _).mul (hcast.add (measurable_wTh R _))).sub (measurable_wTh R _)
      simpa [windowCarry, carryMap] using this.ceil

end

end Kwon1002
