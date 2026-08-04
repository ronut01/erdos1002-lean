import Mathlib

/-!
# Erdős Problem 1002: the statement to be proved

This is the target of the Kwon formalization. The statement is fixed by
the problem and is independent of the ongoing manuscript revision, so it
can be settled now.

Two forms are given:

* `Erdos1002Conclusion`, the concrete Cauchy limit, the form Kwon's
  Theorem 1.1 asserts;
* `Erdos1002Official`, the existential distribution-function form as
  posed by Erdős and as rendered in
  `google-deepmind/formal-conjectures`, `ErdosProblems/1002.lean`.

The second is what the problem literally asks; the first implies it, and
that implication is proved here (it is the only content in this file
that is not a definition).
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Kwon1002

noncomputable section

/-- The centered sawtooth `1/2 - {x}`. -/
def sawtooth (x : ℝ) : ℝ := (1 : ℝ) / 2 - Int.fract x

/-- `S_N(α) = ∑_{k=1}^{N} (1/2 - {kα})`. -/
def rotationSum (N : ℕ) (α : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, sawtooth ((k : ℝ) * α)

/-- `S_N(α) / log N`, the normalized statistic of the problem. -/
def normalizedRotationSum (N : ℕ) (α : ℝ) : ℝ :=
  rotationSum N α / Real.log (N : ℝ)

/-- The finite-`N` distribution function under Lebesgue measure on `(0,1)`. -/
def distributionValue (N : ℕ) (c : ℝ) : ℝ :=
  (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ normalizedRotationSum N α ≤ c}).toReal

/-- CDF of the centered Cauchy law of scale `1/(2π)`. -/
def cauchyLimitCDF (c : ℝ) : ℝ :=
  (1 : ℝ) / 2 + (1 / Real.pi) * Real.arctan (2 * Real.pi * c)

/-- Kwon, Theorem 1.1: pointwise convergence of the distribution
functions to the Cauchy CDF of scale `1/(2π)`. -/
def Erdos1002Conclusion : Prop :=
  ∀ c : ℝ, Tendsto (fun N : ℕ => distributionValue N c) atTop (𝓝 (cauchyLimitCDF c))

/-- The form Erdős asked: some nondecreasing `g` with limits `0` and `1`
is the limiting distribution function. -/
def Erdos1002Official : Prop :=
  ∃ g : ℝ → ℝ, Monotone g ∧ Tendsto g atBot (𝓝 0) ∧ Tendsto g atTop (𝓝 1) ∧
    ∀ c : ℝ, Tendsto (fun N : ℕ => distributionValue N c) atTop (𝓝 (g c))

/-! ## The Cauchy CDF is a distribution function

Elementary, and independent of the analytic content of the proof. Proved
here so that the reduction of the official form to the concrete one is
available from the start.
-/

lemma monotone_cauchyLimitCDF : Monotone cauchyLimitCDF := by
  intro a b hab
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have : Real.arctan (2 * Real.pi * a) ≤ Real.arctan (2 * Real.pi * b) :=
    Real.arctan_mono (by nlinarith)
  have hinv : (0 : ℝ) < 1 / Real.pi := by positivity
  unfold cauchyLimitCDF
  nlinarith [this, hinv]

lemma tendsto_cauchyLimitCDF_atBot : Tendsto cauchyLimitCDF atBot (𝓝 0) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h : Tendsto (fun c : ℝ => 2 * Real.pi * c) atBot atBot :=
    Filter.Tendsto.const_mul_atBot (by positivity) Filter.tendsto_id
  have harc : Tendsto (fun c : ℝ => Real.arctan (2 * Real.pi * c)) atBot (𝓝 (-(Real.pi / 2))) :=
    (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp h
  have hlim := (tendsto_const_nhds (x := (1 : ℝ) / 2) (f := atBot)).add
    (harc.const_mul (1 / Real.pi))
  have hval : (1 : ℝ) / 2 + (1 / Real.pi) * (-(Real.pi / 2)) = 0 := by
    field_simp; ring
  rw [hval] at hlim
  exact hlim

lemma tendsto_cauchyLimitCDF_atTop : Tendsto cauchyLimitCDF atTop (𝓝 1) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h : Tendsto (fun c : ℝ => 2 * Real.pi * c) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) Filter.tendsto_id
  have harc : Tendsto (fun c : ℝ => Real.arctan (2 * Real.pi * c)) atTop (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h
  have hlim := (tendsto_const_nhds (x := (1 : ℝ) / 2) (f := atTop)).add
    (harc.const_mul (1 / Real.pi))
  have hval : (1 : ℝ) / 2 + (1 / Real.pi) * (Real.pi / 2) = 1 := by
    field_simp; ring
  rw [hval] at hlim
  exact hlim

/-- The concrete Cauchy limit implies the form Erdős asked for. -/
theorem official_of_conclusion (h : Erdos1002Conclusion) : Erdos1002Official :=
  ⟨cauchyLimitCDF, monotone_cauchyLimitCDF,
    tendsto_cauchyLimitCDF_atBot, tendsto_cauchyLimitCDF_atTop, h⟩

end

end Kwon1002
