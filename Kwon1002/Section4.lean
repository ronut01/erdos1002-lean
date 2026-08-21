import Kwon1002.GaussEstimates
import Kwon1002.Marks
import Kwon1002.SubstrateBridge

/-!
# §4, Marked factorization and resonances (Kwon, Props 4.1 and 4.2)

Faithful **statements** for §4 of the manuscript, displays (18)-(19) and
(24)-(34).  Everything here is `sorry`-proved on purpose: the deliverable
of this pass is the vocabulary and the two propositions, stated against
the existing `Kwon1002` §2-§3 objects (`digit`, `theta`, `thetaPred`,
`denom`, `Lnorm`, `Hscale`) and the vendored Wang substrate
(`Erdos1002.gaussMeasure` is Gauss's `ν`, see `SubstrateBridge`).

Index conventions carried over from §2, and used without further comment:

* `digit α j = a_{j+1}` (so `F(a_{j+1}, θ_j)` is `F (digit α j) (theta α n j)`);
* `denom α j = q_j` (continuant recursion of `GaussEstimates`);
* `theta α n j = θ_j`, `thetaPred α n j = θ_{j-1}` with `θ_{-1} = 0`;
* `Lnorm n = L = log n`, `Hscale n = H = L^{3/4}` (18).

Readings that the manuscript leaves implicit are flagged at each
definition; see the module docstring items marked **Reading**.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Kwon1002

noncomputable section

/-! ## The additive character on the torus -/

/-- `e(t) = e^{2πit}`, the character used throughout §4. -/
def torusChar (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))

/-! ## (13), (18), (19): the Lévy constant, the scales, and the bulk `J_n` -/

/-- `λ = π²/(12 log 2)` of (13).  (The manuscript calls it the Lyapunov
exponent; it is the Lévy constant, cosmetic note 1 of our referee
report.  The *value* is the one every downstream display uses, so the
value is what is fixed here.) -/
def lyapunov : ℝ := Real.pi ^ 2 / (12 * Real.log 2)

/-- `m_n = ⌊L/λ⌋` of (18). -/
def mIndex (n : ℕ) : ℕ := ⌊Lnorm n / lyapunov⌋₊

/-- **(19)** The bulk index set `J_n = {j : 200H ≤ j ≤ m_n - 200H}`,
as a `Finset ℕ`.  (`Marks.bulkIndices` is the *different*, §7 index set
built from the stopping time; §4's `J_n` is this deterministic one.) -/
def bulkJ (n : ℕ) : Finset ℕ :=
  (Finset.range (mIndex n + 1)).filter
    (fun j => 200 * Hscale n ≤ (j : ℝ) ∧ (j : ℝ) ≤ (mIndex n : ℝ) - 200 * Hscale n)

/-- The pairs `j < k` in `J_n` over which Proposition 4.2 quantifies. -/
def bulkPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (bulkJ n ×ˢ bulkJ n).filter (fun p => p.1 < p.2)

/-! ## (24): the symbol class `P_D(L)`

`F(a,θ) = Σ_{|v| ≤ L^D} c(a,v) e^{2πivθ}`, with `c(a,v) = 0` for `a > L^D`
and `Σ_{a,v} |c(a,v)| ≤ L^D`.

**Reading.** The manuscript writes the Fourier sum over `|v| ≤ L^D`
only; that is recorded here as a second vanishing hypothesis on `c`,
which makes the coefficient family finitely supported and the two `tsum`s
below honest finite sums.  Coefficients are complex (the class is closed
under the Fourier expansion the proof of 4.1 performs, which is the point
of introducing it). -/
def IsInPD (D L : ℝ) (F : ℕ → ℝ → ℂ) : Prop :=
  ∃ c : ℕ → ℤ → ℂ,
    (∀ a : ℕ, ∀ v : ℤ, L ^ D < (a : ℝ) → c a v = 0) ∧
    (∀ a : ℕ, ∀ v : ℤ, L ^ D < |(v : ℝ)| → c a v = 0) ∧
    (∑' p : ℕ × ℤ, ‖c p.1 p.2‖) ≤ L ^ D ∧
    (∀ a : ℕ, ∀ θ : ℝ, F a θ = ∑' v : ℤ, c a v * torusChar ((v : ℝ) * θ))

/-! ## (25)-(26): good tuples

**Reading (26).**  The text extraction of the manuscript drops the
absolute-value bars of display (26); the PDF has them, and they are
essential: the condition is `|j_ℓ - (m_n + j_i)/2| ≥ 200H`, i.e. `j_ℓ`
must avoid a *two-sided* window around the nominal resonance time
`R_i = (m_n + j_i)/2`, not merely lie above it.  The proof of 4.1 uses
exactly the two-sided form ("each lies either at least `100H` before
`k_-` or at least `100H` after `k_+`").

**Reading (indices).**  The manuscript's `j_1 < ⋯ < j_r` is 1-based; here
tuples are `j : ℕ → ℕ` read on `ℓ < r` and normalised to `0` above `r`
(this makes the set of tuples finite for the counting statement, and is
harmless because `0 ∉ J_n`). -/
def IsAdmissibleTuple (n r : ℕ) (j : ℕ → ℕ) : Prop :=
  (∀ ℓ, r ≤ ℓ → j ℓ = 0) ∧
  (∀ ℓ ℓ', ℓ < ℓ' → ℓ' < r → j ℓ < j ℓ') ∧
  (∀ ℓ, ℓ < r → j ℓ ∈ bulkJ n)

/-- **(25)-(26)** A tuple `j_1 < ⋯ < j_r` in `J_n` is *good* when the
consecutive gaps are at least `200H` and every `j_ℓ` avoids the `200H`
window around the resonance time of every earlier `j_i`. -/
def GoodTuple (n r : ℕ) (j : ℕ → ℕ) : Prop :=
  IsAdmissibleTuple n r j ∧
  (∀ ℓ, ℓ + 1 < r → 200 * Hscale n ≤ (j (ℓ + 1) : ℝ) - (j ℓ : ℝ)) ∧
  (∀ i ℓ, i < ℓ → ℓ < r →
    200 * Hscale n ≤ |(j ℓ : ℝ) - ((mIndex n : ℝ) + (j i : ℝ)) / 2|)

/-- The count of non-good `r`-tuples in `J_n` is `O_r(L^{r-1} H)`
(the sentence between (26) and Proposition 4.1). -/
theorem nonGood_tuple_count (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (({j : ℕ → ℕ | IsAdmissibleTuple n r j} \ {j : ℕ → ℕ | GoodTuple n r j}).ncard : ℝ)
        ≤ C * (Lnorm n) ^ (r - 1) * Hscale n := by
  sorry

/-! ## Proposition 4.1 (Marked factorization), display (27) -/

/-- The stationary one-block mean `∫₀¹ ∫₀¹ F(a₁(x), θ) dθ dν(x)` on the
right of (27).  `a₁(x) = ⌊1/x⌋ = digit x 0`, `dν` is Gauss measure
(`Erdos1002.gaussMeasure`, which is a probability measure carried by
`[0,1]`), and `dθ` is Haar measure on `T`, i.e. Lebesgue on `(0,1)`. -/
def stationaryMean (F : ℕ → ℝ → ℂ) : ℂ :=
  ∫ x, (∫ θ in Ioo (0 : ℝ) 1, F (digit x 0) θ) ∂Erdos1002.gaussMeasure

/-! ### Proposition 4.1 (Marked factorization), display (27)

`Kwon1002.prop_4_1_marked_factorization` is **declared in
`Kwon1002/Prop41Unconditional.lean`**, not here.  Its proof consumes the
`v_s ≠ 0` branch of §4, discharged in `Kwon1002/NonzeroMode.lean`, and every
module able to prove it sits above this one.  A declaration placed here could
therefore never shed its `sorry` by mathematics alone, so the name is put
where the proof lives instead.  The statement is unchanged; see the docstring
at its declaration site. -/

/-! ## (31): reduction of a radius-`R` window character to the central pair -/

/-- The radius-`R` digit word at time `j`: `(a_{j-R+1}, …, a_{j+R})`,
i.e. `(digit α (j-R), …, digit α (j+R-1))`, of length `2R`. -/
def windowWord (R : ℕ) (α : ℝ) (j : ℕ) : Fin (2 * R) → ℕ :=
  fun t => digit α (j + (t : ℕ) - R)

/-- **(31)** On its digit cylinder, every radius-`R` window character
reduces mod 1 to a character in the two central coordinates `θ_j`,
`θ_{j-1}`, with integer coefficients `A_w`, `B_w` depending only on the
radius-`R` word `w`.

**Reading.**  "Depending only on `w`" is rendered by quantifying `A`, `B`
as functions of the word *before* `α`, `n`, `j` are introduced; the
`(mod 1)` of (31) is the existential integer `m`.

**Range.**  The manuscript sums `t = -R-1, …, R`, so the window reaches
`θ_{j-R-1}` and the identity requires `j ≥ R+1`.  An earlier form of this
statement summed only `t = -R, …, R` under `R ≤ j`, one coordinate short of
the manuscript; it is widened here to the manuscript's own window.  Proved
at that range as `V5Identity31.window_character_reduction_v5`. -/
theorem window_character_reduction (R : ℕ) (c : Fin (2 * R + 2) → ℤ) :
    ∃ A B : (Fin (2 * R) → ℕ) → ℤ,
      ∀ α : ℝ, Irrational α → α ∈ Ioo (0 : ℝ) 1 → ∀ n j : ℕ, R + 1 ≤ j →
        ∃ m : ℤ,
          (∑ i : Fin (2 * R + 2), (c i : ℝ) * theta α n (j + (i : ℕ) - (R + 1)))
            = (A (windowWord R α j) : ℝ) * theta α n j
              + (B (windowWord R α j) : ℝ) * thetaPred α n j + (m : ℝ) := by
  sorry

/-! ## (32)-(33): cylinder-torus monomials and their frequencies -/

/-- **(33)** `Q_j(r,s) = s q_j - r q_{j-1}`.  (`q_{-1} = 0`; the value at
`j = 0` is never used, every `j` in play lying in `J_n`.) -/
def Qfreq (α : ℝ) (j : ℕ) (r s : ℤ) : ℤ :=
  s * (denom α j : ℤ) - r * (denom α (j - 1) : ℤ)

/-- **(33)**, the sentence "Its frequency is `(-1)^j Q_j(r,s)`": by (8)
the torus part of a monomial at time `j` is the pure phase
`e^{2πi n (-1)^j Q_j(r,s) α}`.  Needs `j ≥ 1`, since `Qfreq` reads
`q_{j-1}` through truncated subtraction.

**The standing §2 hypotheses on `α` are required.**  Without them the
statement is false: `CharacterReduction.torusChar_monomial_frequency_false`
refutes it at `α = 1/2`, `n = 1`, `j = 2`, `(r,s) = (0,1)`, where (8) fails
because `α` is rational.  The manuscript carries `α` irrational in `(0,1)`
throughout §2-§4, so this restores a hypothesis the prose assumes rather
than changing the claim.

Proved as `CharacterReduction.torusChar_monomial_frequency'`.  It cannot be
discharged here, since its proof runs through `theta_eq_mod`, which lives
downstream of this module; `CharacterReduction` carries a type-check guard
tying that proof to this statement. -/
theorem torusChar_monomial_frequency {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n j : ℕ) (hj : 1 ≤ j) (r s : ℤ) :
    torusChar ((r : ℝ) * thetaPred α n j + (s : ℝ) * theta α n j)
      = torusChar ((-1 : ℝ) ^ j * (Qfreq α j r s : ℝ) * (n : ℝ) * α) := by
  sorry

/-- **(32)** A *window symbol* of radius `R` and mode cap `K`: the data of
a finite linear combination of cylinder-torus monomials

`U_j(α) = u(a_{j-R+1}, …, a_{j+R}) e^{2πi(r θ_{j-1} + s θ_j)}`,   `|r| + |s| ≤ K`,

with `u` supported on finitely many words.  A single monomial is the case
where `coeff` is supported on one `(w, r, s)`; a finite linear combination
of monomials of a common radius and cap is exactly a general `coeff` with
these two support restrictions, because `Σ_w c_w 1[word = w]` collapses to
`c_{word}`.

**Reading (radius/cap).**  The manuscript fixes `R` and `K` once and lets
`U`, `V` be *fixed* finite combinations.  A common radius and cap for the
two blocks is no loss (pad the smaller), and it is what makes the
`O_{U,V}` bookkeeping of (34) meaningful. -/
structure WindowSymbol (R K : ℕ) where
  /-- Coefficient of the word `w` and the torus mode `(r,s)`. -/
  coeff : (Fin (2 * R) → ℕ) → ℤ → ℤ → ℂ
  /-- The finitely many words the symbol is supported on. -/
  words : Finset (Fin (2 * R) → ℕ)
  coeff_support : ∀ w r s, w ∉ words → coeff w r s = 0
  mode_cap : ∀ w r s, K < r.natAbs + s.natAbs → coeff w r s = 0

/-- The symbol `U` placed at time `j`: `U_j(α)` of (32). -/
def WindowSymbol.at {R K : ℕ} (U : WindowSymbol R K) (α : ℝ) (n j : ℕ) : ℂ :=
  ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
    U.coeff (windowWord R α j) r s *
      torusChar ((r : ℝ) * thetaPred α n j + (s : ℝ) * theta α n j)

/-! ## `μ̂₀`: the stationary Gauss natural-extension measure times Haar on `T²`

Coordinates: `((x, y), (θ', θ))` with `(x,y) ∈ (0,1)²` the natural-extension
pair at the reference time, `x = [0; a_{j+1}, a_{j+2}, …]` the future,
`y = [0; a_j, a_{j-1}, …]` the past, and `(θ', θ) ∈ T²` the pair
`(θ_{j-1}, θ_j)`.  The invariant density of the natural extension is
`1/(log 2 (1+xy)²)` (§3, in the proof of Lemma 3.3); Haar on `T²` is
Lebesgue on `(0,1)²`. -/
def hatMu0 : Measure ((ℝ × ℝ) × ℝ × ℝ) :=
  (volume.restrict
      ((Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))).withDensity
    (fun z => ENNReal.ofReal (1 / (Real.log 2 * (1 + z.1.1 * z.1.2) ^ 2)))

/-- The radius-`R` word read off a natural-extension point `(x, y)`:
the past half `(a_{j-R+1}, …, a_j)` comes from `y` in reversed order, the
future half `(a_{j+1}, …, a_{j+R})` from `x`. -/
def natExtWord (R : ℕ) (p : ℝ × ℝ) : Fin (2 * R) → ℕ :=
  fun t => if (t : ℕ) < R then digit p.2 (R - 1 - (t : ℕ)) else digit p.1 ((t : ℕ) - R)

/-- A window symbol evaluated on the natural extension times `T²`. -/
def WindowSymbol.eval {R K : ℕ} (U : WindowSymbol R K) (z : (ℝ × ℝ) × ℝ × ℝ) : ℂ :=
  ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
    U.coeff (natExtWord R z.1) r s * torusChar ((r : ℝ) * z.2.1 + (s : ℝ) * z.2.2)

/-- `∫ U dμ̂₀`, the stationary mean appearing on the right of (34). -/
def WindowSymbol.stationaryIntegral {R K : ℕ} (U : WindowSymbol R K) : ℂ :=
  ∫ z, U.eval z ∂hatMu0

/-! ## Proposition 4.2 (Two-block factorization), display (34) -/

/-! ### Proposition 4.2 (Two-block factorization), display (34)

`Kwon1002.prop_4_2_two_block_factorization` is **declared in
`Kwon1002/Prop42Unconditional.lean`**, not here, for the same reason as
Proposition 4.1: the three cases of its monomial core are discharged in
`Kwon1002/PhaseBounds.lean`, `Kwon1002/P42Later.lean` and
`Kwon1002/P42Super.lean`, all of which sit above this module.  The statement
is unchanged; see the docstring at its declaration site. -/

end

end Kwon1002
