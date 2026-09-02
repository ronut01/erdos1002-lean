import Kwon1002.QuasiIndep
import Kwon1002.Section7Bridge

/-!
# The join module: §5's Corollary 5.3 and the master theorem, above the proof of DEBT 1

`Kwon1002/QuasiIndep.lean` **proves** the fixed-`ε` large-jump
characteristic-function limit (DEBT 1) outright:
`Kwon1002.QuasiIndep.largeSum_charFun_limit` carries the statement of
`Kwon1002.CorFinal.largeSum_charFun_limit` token for token (two anonymous
`example`s at the foot of that file close one and the same statement text, one
by the canonical sorried declaration and one by the theorem proved there), and
`#print axioms` on it reports exactly `[propext, Classical.choice, Quot.sound]`.

That proof cannot be installed where the canonical declaration stands.  The
factorial route runs

  `CorFinal → FactorialRoute → … → StepQuasi → QuasiIndep`,

so `QuasiIndep` sits strictly **above** `CorFinal`, and the `sorry` at
`Kwon1002.CorFinal.largeSum_charFun_limit` therefore survives in the import
closure of everything that consumes that name — including
`CorFinal.principal_cauchy_law_F` and, through it,
`Master.erdos1002Conclusion_of_section7`.  This is the sixth instance of the
import-direction pathology in this tree, and it is handled the same way as the
previous five: the affected chain is **restated and re-proved here**, in a
module that imports both sides, with a `rfl` guard against every canonical
name so that no statement can drift.

## What is re-proved here, and against what

The five-step chain of `Kwon1002/CorFinal.lean` Part I, re-run with
`QuasiIndep.largeSum_charFun_limit` in place of the sorried
`CorFinal.largeSum_charFun_limit`:

  `xi_charFun_limit_J` → `xi_largeIntegral_weak_limit_J`
    → `largeJump_tendsto_compoundPoisson_J` → `largeJump_weak_limit_J`
    → `principal_cauchy_law_J`,

together with `compound_tendsto_cauchy_J`, which `principal_cauchy_law_J` also
consumes.  Every proof body is the author's, transcribed unchanged apart from
the names of its inputs; the statements are byte-identical to `CorFinal`'s and
are checked against the canonical names by the anonymous `example`s at the foot
of this file.

`principal_cauchy_law_J` additionally consumes
`CorFinal.signed_small_jumps_variance_F`, which is used **as it stands**: its
only sorry-leaf is `CorFinal.bulk_offdiagonal_abs_far_sharp`, so nothing is
gained by restating it here.

## The effect on the closure

`CorFinal.principal_cauchy_law_F` has sorry-leaves
`{bulk_offdiagonal_abs_far_sharp, largeSum_charFun_limit}`.
`principal_cauchy_law_J` has sorry-leaves `{bulk_offdiagonal_abs_far_sharp}`.

`Master.erdos1002Conclusion_of_section7` has the two historical §5 leaves
`{bulk_offdiagonal_abs_far_sharp, largeSum_charFun_limit}`;
`erdos1002Conclusion_of_section7_J` below, and the unconditional
`erdos1002Conclusion_final`, retain only
`{bulk_offdiagonal_abs_far_sharp}`.  Proposition 6.4 is now supplied by its
completed canonical root declaration.

`Kwon1002/CorFinal.lean` is deliberately **not** edited: its `sorry` stays where
it is, as with the five earlier instances, and this module is the machine-checked
record that the statement it carries is proved elsewhere.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal Real

namespace Kwon1002

namespace CauchyJoin

open Assembly5

noncomputable section

/-! ## Part I, the five-step chain, on the proved DEBT 1 -/

/-- `Kwon1002.xi_charFun_limit` (the residual of `Kwon1002/FiveFinal.lean`),
reproduced token for token and **proved** from
`QuasiIndep.largeSum_charFun_limit`. -/
theorem xi_charFun_limit_J (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1) (t : ℝ)
    (μs : ℕ → ProbabilityMeasure ℝ)
    (_hμs : ∀ n, (μs n : Measure ℝ)
      = unifIoo.map (fun α => ∫ x in PoissonRoute.truncSet ε, x ∂(PoissonRoute.xiMeasure c α n))) :
    Tendsto (fun n => charFun (μs n : Measure ℝ) t) atTop
      (𝓝 (Complex.exp (∫ x in {x : ℝ | ε < |x|},
          (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) - 1)
            * (levyIntensityDensity x : ℂ)))) := by
  have h : ∀ n : ℕ, charFun (μs n : Measure ℝ) t
      = ∫ α in Ioo (0 : ℝ) 1,
          Complex.exp ((t : ℂ) * (largeSum c ε α n : ℂ) * Complex.I) :=
    fun n => CorFinal.charFun_largeSum_law c ε _hε0.le n t (μs n) (_hμs n)
  simp only [h]
  exact QuasiIndep.largeSum_charFun_limit c ε _hε0 _hε1 t

/-- `Kwon1002.PoissonRoute.xi_largeIntegral_weak_limit`, reproduced token for
token and **proved** from `xi_charFun_limit_J`, by Lévy continuity
(`Erdos1002.levy_continuity_real`) and the compound-Poisson exponent identity
(`CompoundCauchy.charFun_compoundPoisson_levy`). -/
theorem xi_largeIntegral_weak_limit_J (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1)
    (r : ℝ≥0) (ν : ProbabilityMeasure ℝ)
    (_hrate : (r : ℝ≥0∞) = levyIntensity (PoissonRoute.truncSet ε))
    (_hjump : (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict (PoissonRoute.truncSet ε))
    (μs : ℕ → ProbabilityMeasure ℝ)
    (_hμs : ∀ n, (μs n : Measure ℝ)
      = unifIoo.map (fun α => ∫ x in PoissonRoute.truncSet ε, x ∂(PoissonRoute.xiMeasure c α n))) :
    Tendsto μs atTop (𝓝 (Erdos1002.continuousCompoundPoissonProbability r ν)) := by
  refine Erdos1002.levy_continuity_real μs _ (fun t => ?_)
  have hjump' : (r : ℝ≥0∞) • (ν : Measure ℝ)
      = levyIntensity.restrict {x : ℝ | ε < |x|} := _hjump
  have hcp : ((Erdos1002.continuousCompoundPoissonProbability r ν :
        ProbabilityMeasure ℝ) : Measure ℝ)
      = Erdos1002.continuousCompoundPoissonMeasure r ν :=
    Erdos1002.continuousCompoundPoissonProbability_toMeasure r ν
  rw [CompoundCauchy.charFun_compoundPoisson_levy _hε0 t
    (Erdos1002.continuousCompoundPoissonProbability r ν) r ν hjump' hcp]
  exact xi_charFun_limit_J c ε _hε0 _hε1 t μs _hμs

/-- The fixed-`ε` large-jump limit with the limit law **exhibited**;
`CorFinal.largeJump_tendsto_compoundPoisson_F` re-proved. -/
theorem largeJump_tendsto_compoundPoisson_J (c ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (r : ℝ≥0) (ν : ProbabilityMeasure ℝ),
      (r : ℝ≥0∞) = levyIntensity (PoissonRoute.truncSet ε) ∧
      (r : ℝ≥0∞) • (ν : Measure ℝ) = levyIntensity.restrict (PoissonRoute.truncSet ε) ∧
      Tendsto (fun n => largeProb c ε n) atTop
        (𝓝 (Erdos1002.continuousCompoundPoissonProbability r ν)) := by
  obtain ⟨r, ν, hrate, hjump⟩ := PoissonRoute.exists_levy_truncation_data hε0
  exact ⟨r, ν, hrate, hjump,
    xi_largeIntegral_weak_limit_J c ε hε0 hε1 r ν hrate hjump (fun n => largeProb c ε n)
      (fun n => PoissonRoute.largeProb_eq_xi_law c ε hε0.le n)⟩

/-- `Kwon1002.Assembly5.largeJump_weak_limit`, reproduced token for token. -/
theorem largeJump_weak_limit_J (c ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1) :
    ∃ ρ : ProbabilityMeasure ℝ,
      Tendsto (fun n => largeProb c ε n) atTop (𝓝 ρ) := by
  obtain ⟨r, ν, -, -, hconv⟩ := largeJump_tendsto_compoundPoisson_J c ε _hε0 _hε1
  exact ⟨Erdos1002.continuousCompoundPoissonProbability r ν, hconv⟩

/-- `Kwon1002.Assembly5.compound_tendsto_cauchy`, reproduced token for token;
proved from `largeJump_tendsto_compoundPoisson_J` and the *proved*
`Finale.compound_tendsto_cauchy_of_identification`. -/
theorem compound_tendsto_cauchy_J (c : ℝ) (e : ℕ → ℝ)
    (_he0 : ∀ k, 0 < e k) (_he1 : ∀ k, e k < 1) (_he : Tendsto e atTop (𝓝 0))
    (ρ : ℕ → ProbabilityMeasure ℝ)
    (_hρ : ∀ k, Tendsto (fun n => largeProb c (e k) n) atTop (𝓝 (ρ k))) :
    Tendsto ρ atTop (𝓝 cauchyProb) := by
  refine Finale.compound_tendsto_cauchy_of_identification e _he0 _he ρ fun k => ?_
  obtain ⟨r, ν, -, hjump, hconv⟩ :=
    largeJump_tendsto_compoundPoisson_J c (e k) (_he0 k) (_he1 k)
  have heq : ρ k = Erdos1002.continuousCompoundPoissonProbability r ν :=
    tendsto_nhds_unique (_hρ k) hconv
  refine ⟨r, ν, hjump, ?_⟩
  rw [heq, Erdos1002.continuousCompoundPoissonProbability_toMeasure]

/-! ## Part II, Corollary 5.3

The author's ε/3 assembly of `Assembly5`/`Finale`, re-run against the proved
DEBT 1.  The only sorried input left in it is
`CorFinal.bulk_offdiagonal_abs_far_sharp`, reached through
`CorFinal.signed_small_jumps_variance_F`. -/

/-- **Corollary 5.3**, `Kwon1002.principal_cauchy_law`
(`Kwon1002/PoissonLimit.lean` line 46), display (43), reproduced token for
token.

Proved from exactly **one** sorried statement,
`CorFinal.bulk_offdiagonal_abs_far_sharp`. -/
theorem principal_cauchy_law_J (c : ℝ) :
    ∃ b : ℕ → ℝ, ∀ x : ℝ,
      Tendsto
        (fun n : ℕ =>
          (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ bulkSum c α n - b n ≤ x}).toReal)
        atTop (𝓝 (cauchyLimitCDF x)) := by
  classical
  obtain ⟨C, hC, hvar⟩ := CorFinal.signed_small_jumps_variance_F c
  -- the truncation scale, tuned so that `C · e k ≤ (dseq k)³`
  set dseq : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 2) with hdseq
  set e : ℕ → ℝ := fun k => dseq k ^ 3 / (C + 1) with he
  have hd0 : ∀ k, 0 < dseq k := fun k => by
    simp only [hdseq]; positivity
  have hd1 : ∀ k, dseq k ≤ 1 / 2 := fun k => by
    simp only [hdseq]
    refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have he0 : ∀ k, 0 < e k := fun k => by
    simp only [he]
    have := hd0 k
    positivity
  have he1 : ∀ k, e k < 1 := fun k => by
    have h1 : dseq k ^ 3 ≤ 1 := by
      have h2 := hd1 k
      have h3 := (hd0 k).le
      calc dseq k ^ 3 ≤ (1 / 2 : ℝ) ^ 3 := by gcongr
        _ ≤ 1 := by norm_num
    have : e k ≤ 1 / (C + 1) := by
      simp only [he]
      exact div_le_div_of_nonneg_right h1 (by linarith)
    have hlt : 1 / (C + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    linarith
  have hdlim : Tendsto dseq atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h.comp (tendsto_add_atTop_nat 1)
    refine h2.congr fun k => ?_
    simp only [Function.comp_apply, hdseq]
    push_cast
    ring_nf
  have helim : Tendsto e atTop (𝓝 0) := by
    have h3 : Tendsto (fun k => dseq k ^ 3) atTop (𝓝 0) := by
      simpa using hdlim.pow 3
    simpa [he] using h3.div_const (C + 1)
  -- the limit laws of the large-jump parts, and their Cauchy limit
  have hlarge : ∀ k : ℕ, ∃ ρ : ProbabilityMeasure ℝ,
      Tendsto (fun n => largeProb c (e k) n) atTop (𝓝 ρ) := fun k =>
    largeJump_weak_limit_J c (e k) (he0 k) (he1 k)
  choose ρ hρ using hlarge
  have hcauchy : Tendsto ρ atTop (𝓝 cauchyProb) :=
    compound_tendsto_cauchy_J c e he0 he1 helim ρ hρ
  -- pass to the Lévy-Prokhorov metric, which metrizes convergence in distribution
  set Φ : ProbabilityMeasure ℝ → LevyProkhorov (ProbabilityMeasure ℝ) :=
    LevyProkhorov.ofMeasure with hΦ
  have hΦcont : Continuous Φ := LevyProkhorov.continuous_ofMeasure_probabilityMeasure
  set z : LevyProkhorov (ProbabilityMeasure ℝ) := Φ cauchyProb with hz
  set Pk : ℕ → ℕ → LevyProkhorov (ProbabilityMeasure ℝ) :=
    fun k n => Φ (centeredBulkProb c (e k) n) with hPk
  set η : ℕ → ℝ := fun k => dseq k + dseq k + dist (Φ (ρ k)) z with hη
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have hdist : Tendsto (fun k => dist (Φ (ρ k)) z) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => Φ (ρ k)) atTop (𝓝 z) := by
        simpa [hz] using (hΦcont.tendsto cauchyProb).comp hcauchy
      have h2 := h1.dist (tendsto_const_nhds (x := z) (f := atTop))
      simpa using h2
    have := (hdlim.add hdlim).add hdist
    simpa [hη] using this
  have hPkclose : ∀ k, ∀ᶠ n in atTop, dist (Pk k n) z ≤ η k := by
    intro k
    obtain ⟨N, hN⟩ := hvar (e k) (he0 k) (he1 k)
    have hlp : Tendsto (fun n => Φ (largeProb c (e k) n)) atTop (𝓝 (Φ (ρ k))) :=
      (hΦcont.tendsto (ρ k)).comp (hρ k)
    have hev := Metric.tendsto_nhds.mp hlp (dseq k) (hd0 k)
    filter_upwards [eventually_ge_atTop N, hev] with n hn hnd
    have h1 : dist (Pk k n) (Φ (largeProb c (e k) n)) ≤ dseq k := by
      refine dist_centeredBulk_largeProb_le c (e k) (he0 k).le n (hd0 k).le ?_
      refine (hN n hn).trans ?_
      have hpos : (0 : ℝ) < C + 1 := by linarith
      have hcube : (0 : ℝ) ≤ dseq k ^ 3 := pow_nonneg (hd0 k).le 3
      simp only [he]
      rw [← mul_div_assoc, div_le_iff₀ hpos]
      nlinarith [hcube]
    calc dist (Pk k n) z
        ≤ dist (Pk k n) (Φ (largeProb c (e k) n)) + dist (Φ (largeProb c (e k) n)) z :=
          dist_triangle _ _ _
      _ ≤ dist (Pk k n) (Φ (largeProb c (e k) n))
            + (dist (Φ (largeProb c (e k) n)) (Φ (ρ k)) + dist (Φ (ρ k)) z) := by
          gcongr
          exact dist_triangle _ _ _
      _ ≤ dseq k + (dseq k + dist (Φ (ρ k)) z) :=
          add_le_add h1 (add_le_add hnd.le le_rfl)
      _ = η k := by simp only [hη]; ring
  obtain ⟨κ, hκ⟩ := exists_diagonal_tendsto Pk z η hηlim hPkclose
  -- transfer back to convergence in distribution
  have hweak : Tendsto (fun n => centeredBulkProb c (e (κ n)) n) atTop (𝓝 cauchyProb) := by
    have hcont : Continuous
        (LevyProkhorov.toMeasure (α := ProbabilityMeasure ℝ)) :=
      LevyProkhorov.continuous_toMeasure_probabilityMeasure
    have h := (hcont.tendsto z).comp hκ
    simpa [hPk, hΦ, hz, Function.comp_def] using h
  refine ⟨fun n => smallCenter c (e (κ n)) n, fun x => ?_⟩
  exact cdf_tendsto_of_weak_convergence c (fun n => smallCenter c (e (κ n)) n)
    (fun n => centeredBulkProb c (e (κ n)) n) (fun n => rfl) hweak x

/-! ## Part III, the master theorem

`Kwon1002/Master.lean` proves Kwon's Theorem 1.1 from three hypotheses and
`Kwon1002/Section7Bridge.lean` discharges the third outright.  Corollary 5.3 is
supplied by Part II above, and Proposition 6.4 now comes from the completed
canonical declaration in `Kwon1002.Prop64Final`. -/

/-- `Kwon1002.Master.erdos1002Conclusion_of_section7`, reproduced token for
token, with hypothesis 1 fed from `principal_cauchy_law_J` rather than from
`CorFinal.principal_cauchy_law_F`.  Its only historical leaf is
`CorFinal.bulk_offdiagonal_abs_far_sharp`. -/
theorem erdos1002Conclusion_of_section7_J (c : ℝ) (hstop : Master.Section7EndTerms c) :
    Erdos1002Conclusion :=
  Master.erdos1002Conclusion_of c (principal_cauchy_law_J c)
    prop_6_4_bounded_remainder_weak_law hstop

/-- **Kwon's Theorem 1.1 from Proposition 6.4 alone.**  §7 is proved
(`Section7.section7EndTerms_holds`), Corollary 5.3 is `principal_cauchy_law_J`,
so Proposition 6.4 is the single remaining hypothesis. -/
theorem erdos1002Conclusion_of_prop64 (hprop64 : Master.Prop64Statement) :
    Erdos1002Conclusion :=
  Section7.erdos1002Conclusion_of_principal_and_prop64 0 le_rfl
    (principal_cauchy_law_J 0) hprop64

/-- The official (existential) form Erdős asked for, from Proposition 6.4
alone. -/
theorem erdos1002Official_of_prop64 (hprop64 : Master.Prop64Statement) :
    Erdos1002Official :=
  Section7.erdos1002Official_of_principal_and_prop64 0 le_rfl
    (principal_cauchy_law_J 0) hprop64

/-- **The endgame.**  Kwon's Theorem 1.1, with the completed Proposition 6.4
fed from its canonical name.  The only historical leaf here is
`Kwon1002.CorFinal.bulk_offdiagonal_abs_far_sharp`. -/
theorem erdos1002Conclusion_final : Erdos1002Conclusion :=
  erdos1002Conclusion_of_prop64 prop_6_4_bounded_remainder_weak_law

/-- The official form, same two leaves. -/
theorem erdos1002Official_final : Erdos1002Official :=
  erdos1002Official_of_prop64 prop_6_4_bounded_remainder_weak_law

end

end CauchyJoin

end Kwon1002

/- **Token-identity checks.**  Each `example` forces the statement above to be
the *same type* as its canonical target (`rfl` then closes it by proof
irrelevance).  They mention sorried declarations, so they are anonymous and
nothing proved above depends on them. -/
example : @Kwon1002.xi_charFun_limit
    = @Kwon1002.CauchyJoin.xi_charFun_limit_J := rfl

example : @Kwon1002.CorFinal.xi_charFun_limit_F
    = @Kwon1002.CauchyJoin.xi_charFun_limit_J := rfl

example : @Kwon1002.PoissonRoute.xi_largeIntegral_weak_limit
    = @Kwon1002.CauchyJoin.xi_largeIntegral_weak_limit_J := rfl

example : @Kwon1002.CorFinal.xi_largeIntegral_weak_limit_F
    = @Kwon1002.CauchyJoin.xi_largeIntegral_weak_limit_J := rfl

example : @Kwon1002.CorFinal.largeJump_tendsto_compoundPoisson_F
    = @Kwon1002.CauchyJoin.largeJump_tendsto_compoundPoisson_J := rfl

example : @Kwon1002.Assembly5.largeJump_weak_limit
    = @Kwon1002.CauchyJoin.largeJump_weak_limit_J := rfl

example : @Kwon1002.CorFinal.largeJump_weak_limit_F
    = @Kwon1002.CauchyJoin.largeJump_weak_limit_J := rfl

example : @Kwon1002.Assembly5.compound_tendsto_cauchy
    = @Kwon1002.CauchyJoin.compound_tendsto_cauchy_J := rfl

example : @Kwon1002.CorFinal.compound_tendsto_cauchy_F
    = @Kwon1002.CauchyJoin.compound_tendsto_cauchy_J := rfl

example : @Kwon1002.principal_cauchy_law
    = @Kwon1002.CauchyJoin.principal_cauchy_law_J := rfl

example : @Kwon1002.Assembly5.principal_cauchy_law
    = @Kwon1002.CauchyJoin.principal_cauchy_law_J := rfl

example : @Kwon1002.CorFinal.principal_cauchy_law_F
    = @Kwon1002.CauchyJoin.principal_cauchy_law_J := rfl

example : @Kwon1002.Master.erdos1002Conclusion_of_section7
    = @Kwon1002.CauchyJoin.erdos1002Conclusion_of_section7_J := rfl
