import Kwon1002.Section4
import Kwon1002.Lemma61

/-!
# §6 of v5, the carry graph and the bounded remainder: skeleton

Faithful **statements** for Section 6 of the settled v5 manuscript
(`manuscript/erdos1002_cauchy_limit_revision_v5.tex`), together with the
window bookkeeping the section rests on.  Nothing in §6 had been
formalized before; this file supplies the vocabulary and the four
headline statements, proving outright only what falls out for free.

Line numbers below refer to the v5 TeX source.

* Lemma 6.1, endpoint-controlled continuant recurrence, lines 1060-1076.
* Lemma 6.2, Gauss-torus mixing, lines 1112-1150.
* The window space `X_R` (51), the actual window (52), the stationary
  window law `μ_R` and the projections `π_{R',R}`, lines 1152-1165.
* Lemma 6.3, uniform full-state transfer, lines 1166-1179.
* The carry map (53), the reset set (54), the invariant carry graph,
  and the coupling bound (57), lines 1246-1293.
* Proposition 6.4, bounded-remainder weak law, lines 1295-1463, stated
  against the corrected display (55) at lines 1307-1408.

Everything is phrased in the §2-§4 vocabulary already in the tree:
`gaussIter`, `digit`, `denom`, `theta`, `thetaPred`, `betaProd`, `Phi`,
`W`, `carry`, `Lnorm`, `Hscale`, `bulkJ`, `lyapunov`, `torusChar`,
`hatMu0`, `Qfreq`, `windowWord`, `WindowSymbol`.

## Readings flagged

1. **Lemma 6.1, "not identically zero" (line 1063).**  Read as: the
   solution is not identically zero *on the range the recurrence
   controls*, `0 ≤ i ≤ m+1`.  The literal reading "the sequence
   `z : ℕ → ℤ` is not the zero sequence" makes the lemma false: take
   `z 0 = z 1 = 0`, so that `z i = 0` for all `i ≤ m+1` no matter how
   large `m` is, and let `z` be nonzero somewhere beyond `m+1`, which
   the recurrence never sees.  Equivalently the hypothesis is
   `(z 0, z 1) ≠ (0,0)`.  No hypothesis `K ≥ 1` is needed: if `K < 1`
   the endpoint bounds force `z 0 = z 1 = 0` and the statement is
   vacuous.

2. **Uniformity in `j` (Lemma 6.3, (57), (56)).**  `sup_{j ∈ J_n} … → 0`
   is rendered as `∀ ε > 0, ∀ᶠ n, ∀ j ∈ bulkJ n, … < ε`.  For each `n`
   the index set is finite, so this is equivalent to convergence of the
   supremum, and it avoids a `⨆` over a possibly empty index set at
   small `n`.

3. **Window indexing.**  `X_R = ℕ^{2R+1} × [0,1]^{2R+1} × T^{2R+2}` is
   carried as a triple of `Fin`-indexed functions.  The digit and real
   blocks are indexed by `i ↦ t = i - R`, the torus block by
   `i ↦ t = i - R - 1`, matching the ranges `-R ≤ t ≤ R` and
   `-R-1 ≤ t ≤ R` of (52).  The `ℤ`-indexed accessors `wA`, `wX`, `wTh`
   read a window at an offset `t` directly and return a junk value off
   range; every statement below is used only in range.

4. **Torus representatives.**  As in v5 (lines 1035-1037), a torus
   coordinate is always its representative in `[0,1)`.  Where that
   matters (the reset computation) it appears as an explicit
   hypothesis rather than being built into the type.

5. **Lemma 6.3's `κ, δ` (lines 1189-1191).**  These are internal to the
   proof; v5 separates them and imposes `κ + 3δ < 80λ`.  They are
   surfaced here in `lemma_6_3_good_cylinder_selection`, the step that
   actually uses them, and the compatibility constraint is recorded and
   discharged in `exists_admissible_kappa_delta`.

6. **Display (55) (lines 1400-1408).**  The corrected chain is
   `B^{(R)} → G → G_M → G_M 1_E → P_{R,M}`, and the approximant lives at
   radius `R + M`, not `R`; see `manuscript/proposition_6_4_revision_note.pdf`.
   `display_55_monomial_approximation` states exactly that: the
   fixed-radius remainder is lifted along `π_{R+M,R}` and compared, in
   `L²(μ_{R+M})`, with a real-valued finite combination of the
   monomials (32) at radius `R + M`.

## Current status

This historical skeleton is machine-checked, but several early declarations
remain explicit proof obligations and therefore still use `sorry`.  The three
final declarations most likely to be mistaken for the completed result are
intentionally **not** declared here: display (55) is proved canonically in
`Kwon1002.Prop64`, while display (56) and Proposition 6.4 are installed under
their root-namespace names only after their proved providers are available in
`Kwon1002.Prop64Final`.  The completed Theorem 1.1 path is
`Kwon1002.ProofComplete`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Kwon1002

noncomputable section

/-! ## Lemma 6.1: endpoint-controlled continuant recurrence

**Lemma 6.1** (v5 lines 1060-1068).  Let `a_i ≥ 1` and let an integer
sequence, not identically zero on `0 ≤ i ≤ m+1`, satisfy
`z_{i+2} = a_{i+1} z_{i+1} + z_i` for `0 ≤ i < m`.  If
`max(|z_0|,|z_1|,|z_m|,|z_{m+1}|) ≤ K` then `m ≤ C log(2K)` for an
absolute constant `C`.

See reading 1 of the module docstring for the non-vanishing hypothesis.

**Proved in `Kwon1002.Lemma61`, and declared there only.**  This file used
to carry a second, sorried declaration of the same fully-qualified name
`Kwon1002.lemma_6_1_endpoint_recurrence`.  Since neither module imports the
other, the clash was invisible until `Kwon1002.lean` pulled both in, where
Lean silently kept whichever arrived later — the proved one, but only
because of the order of two adjacent import lines.  Reordering them would
have substituted this file's `sorry` and tainted every consumer, starting
with `Lemma62.resonance_bounded`.  The duplicate is removed and this module
imports the proof instead, so the name has exactly one declaration and the
hazard cannot recur. -/

/-! ## The Gauss-torus system and Lemma 6.2 -/

/-- The state space of the two-sided Gauss system times `T²`, in the
coordinates already fixed by `hatMu0` in `Section4`: `((x, y), (θ', θ))`
with `x` the future `[0; a_{j+1}, a_{j+2}, …]`, `y` the past
`[0; a_j, a_{j-1}, …]`, and `(θ', θ) = (θ_{j-1}, θ_j)`. -/
abbrev NatExtTorus : Type := (ℝ × ℝ) × ℝ × ℝ

/-- The natural-extension map `σ`: the future advances by the Gauss map,
the past absorbs the digit just consumed. -/
def natExtMap (p : ℝ × ℝ) : ℝ × ℝ :=
  (gaussMap p.1, ((digit p.1 0 : ℝ) + p.2)⁻¹)

/-- The inverse of `natExtMap`: the past retreats by the Gauss map, the
future gives back the digit `a_j = ⌊1/y⌋`. -/
def natExtInv (p : ℝ × ℝ) : ℝ × ℝ :=
  (((digit p.2 0 : ℝ) + p.1)⁻¹, gaussMap p.2)

/-- **(49)** The torus cocycle
`S(ω, r, s) = (σω, s, r - a_1(ω) s mod 1)`. -/
def hatS (z : NatExtTorus) : NatExtTorus :=
  (natExtMap z.1, z.2.2, Int.fract (z.2.1 - (digit z.1.1 0 : ℝ) * z.2.2))

/-- The inverse cocycle.  On the torus it undoes `θ_{j+1} = {θ_{j-1} - a_{j+1}θ_j}`
using the digit `a_j = ⌊1/y⌋` read off the past coordinate. -/
def hatSinv (z : NatExtTorus) : NatExtTorus :=
  (natExtInv z.1, Int.fract (z.2.2 + (digit z.1.2 0 : ℝ) * z.2.1), z.2.1)

/-- The fibre matrix `A_a = ((0,1),(1,-a))` of v5 lines 1052-1056.  It
lies in `GL₂(ℤ)`, which is why `μ̂₀ = ν̂ ⊗ m_{T²}` is invariant. -/
def fibreMatrix (a : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; 1, -(a : ℤ)]

/-- `A_{a_m} ⋯ A_{a_1}`, with `a i` read as `a_i`. -/
def fibreProd (a : ℕ → ℕ) : ℕ → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => 1
  | m + 1 => fibreMatrix (a (m + 1)) * fibreProd a m

/-- `det A_a = -1`, so `A_a ∈ GL₂(ℤ)` (v5 lines 1052-1056). -/
theorem fibreMatrix_det (a : ℕ) : (fibreMatrix a).det = -1 := by
  rw [fibreMatrix, Matrix.det_fin_two_of]
  ring

/-- The cocycle preserves `μ̂₀`. -/
theorem hatS_measurePreserving : MeasurePreserving hatS hatMu0 hatMu0 := by
  sorry

/-- **(50)**, the character-resonance obstruction.  For fixed nonzero
integer vectors `k, ℓ`, the resonance `k + (A_{a_m} ⋯ A_{a_1})ᵀ ℓ = 0`
is impossible for all sufficiently large `m`, uniformly in the digit
sequence.  This is exactly what Lemma 6.1 buys: the transposed products
turn into the recurrence `z_{i+2} = a_{m-i} z_{i+1} + z_i` whose two
endpoint pairs are, up to signs, the coordinate pairs of `ℓ` and `k`
(v5 lines 1121-1147). -/
theorem resonance_bounded (k l : Fin 2 → ℤ) (hk : k ≠ 0) (hl : l ≠ 0) :
    ∃ M : ℕ, ∀ (m : ℕ), M ≤ m → ∀ a : ℕ → ℕ, (∀ i, 1 ≤ a i) →
      k + (fibreProd a m).transpose.mulVec l ≠ 0 := by
  sorry

/-- **Lemma 6.2** (Gauss-torus mixing), v5 lines 1112-1114.  The system
`(Ω̂ × T², μ̂₀, S)` is mixing.

**Reading.**  Mathlib has no `IsMixing` predicate, so mixing is written
out: correlations of indicators of measurable sets converge to the
product of the masses. -/
theorem lemma_6_2_gauss_torus_mixing (A B : Set NatExtTorus)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun m : ℕ => hatMu0.real (A ∩ hatS^[m] ⁻¹' B)) atTop
      (𝓝 (hatMu0.real A * hatMu0.real B)) := by
  sorry

/-! ## The window space, the actual window, and the window law -/

/-- **(51)** `X_R = ℕ^{2R+1} × [0,1]^{2R+1} × T^{2R+2}` with the product
topology, `ℕ` discrete.  See reading 3 for the index convention. -/
abbrev WindowSpace (R : ℕ) : Type :=
  (Fin (2 * R + 1) → ℕ) × (Fin (2 * R + 1) → ℝ) × (Fin (2 * R + 2) → ℝ)

/-- The digit coordinate of a window at offset `t`, i.e. `a_{j+t+1}`,
for `-R ≤ t ≤ R`. -/
def wA {R : ℕ} (w : WindowSpace R) (t : ℤ) : ℕ :=
  if h : 0 ≤ t + (R : ℤ) ∧ t + (R : ℤ) < 2 * (R : ℤ) + 1 then
    w.1 ⟨(t + (R : ℤ)).toNat, by omega⟩ else 0

/-- The real coordinate of a window at offset `t`, i.e. `x_{j+t}`,
for `-R ≤ t ≤ R`. -/
def wX {R : ℕ} (w : WindowSpace R) (t : ℤ) : ℝ :=
  if h : 0 ≤ t + (R : ℤ) ∧ t + (R : ℤ) < 2 * (R : ℤ) + 1 then
    w.2.1 ⟨(t + (R : ℤ)).toNat, by omega⟩ else 0

/-- The torus coordinate of a window at offset `t`, i.e. `θ_{j+t}`,
for `-R-1 ≤ t ≤ R`. -/
def wTh {R : ℕ} (w : WindowSpace R) (t : ℤ) : ℝ :=
  if h : 0 ≤ t + (R : ℤ) + 1 ∧ t + (R : ℤ) + 1 < 2 * (R : ℤ) + 2 then
    w.2.2 ⟨(t + (R : ℤ) + 1).toNat, by omega⟩ else 0

/-- **(52)** The actual window
`W^{(R)}_{n,j} = ((a_{j+t+1})_{t=-R}^{R}, (x_{j+t})_{t=-R}^{R}, (θ_{j+t})_{t=-R-1}^{R})`.

Requires `R + 1 ≤ j` for every coordinate to exist; the truncated
subtraction below is never exercised at the intended `j ∈ J_n`, which
satisfies `j ≥ 200H`. -/
def actualWindow (R : ℕ) (α : ℝ) (n j : ℕ) : WindowSpace R :=
  (fun i => digit α (j + (i : ℕ) - R),
   fun i => gaussIter α (j + (i : ℕ) - R),
   fun i => theta α n (j + (i : ℕ) - R - 1))

/-- `S^t` for `t ∈ ℤ`, used to read the stationary window at negative
offsets. -/
def hatSzpow (t : ℤ) (z : NatExtTorus) : NatExtTorus :=
  if 0 ≤ t then hatS^[t.toNat] z else hatSinv^[(-t).toNat] z

/-- The stationary window, defined from the two-sided Gauss-torus system
exactly as (52) is defined from the actual process (v5 lines 1161-1163). -/
def stationaryWindow (R : ℕ) (z : NatExtTorus) : WindowSpace R :=
  (fun i => digit (hatSzpow ((i : ℤ) - (R : ℤ)) z).1.1 0,
   fun i => (hatSzpow ((i : ℤ) - (R : ℤ)) z).1.1,
   fun i => (hatSzpow ((i : ℤ) - (R : ℤ) - 1) z).2.2)

/-- The stationary window law `μ_R`. -/
def windowLaw (R : ℕ) : Measure (WindowSpace R) :=
  hatMu0.map (stationaryWindow R)

/-- The law `η^{(R)}_{n,j}` of the actual window (52) for Lebesgue `α`
on `(0,1)`. -/
def actualWindowLaw (R n j : ℕ) : Measure (WindowSpace R) :=
  (volume.restrict (Ioo (0 : ℝ) 1)).map (fun α => actualWindow R α n j)

/-- The coordinate projection `π_{R',R} : X_{R'} → X_R` of v5 lines
1164-1165: retain the digit and real coordinates with `-R ≤ t ≤ R` and
the torus coordinates with `-R-1 ≤ t ≤ R`.  In index terms every block
is shifted by `R' - R`. -/
def windowProj {R' R : ℕ} (h : R ≤ R') (w : WindowSpace R') : WindowSpace R :=
  (fun i => w.1 ⟨(i : ℕ) + (R' - R), by have := i.isLt; omega⟩,
   fun i => w.2.1 ⟨(i : ℕ) + (R' - R), by have := i.isLt; omega⟩,
   fun i => w.2.2 ⟨(i : ℕ) + (R' - R), by have := i.isLt; omega⟩)




/-! ## Lemma 6.3: uniform full-state transfer -/

/-- A digit-cylinder amplitude supported on finitely many local words,
times a torus character `exp(2πi Σ_{t=-R-1}^{R} c_t θ_{j+t})`: the test
class the proof of Lemma 6.3 starts from (v5 lines 1180-1183). -/
structure CylinderCharacterTest (R : ℕ) where
  /-- The digit amplitude, a function of the full window word
  `(a_{j-R+1}, …, a_{j+R+1})`. -/
  amp : (Fin (2 * R + 1) → ℕ) → ℂ
  /-- The finitely many local words the amplitude is supported on. -/
  words : Finset (Fin (2 * R + 1) → ℕ)
  amp_support : ∀ w ∉ words, amp w = 0
  /-- The character exponents `c_{-R-1}, …, c_R`. -/
  c : Fin (2 * R + 2) → ℤ

/-- The test as a function on `X_R`. -/
def CylinderCharacterTest.eval {R : ℕ} (T : CylinderCharacterTest R)
    (w : WindowSpace R) : ℂ :=
  T.amp w.1 * torusChar (∑ i : Fin (2 * R + 2), (T.c i : ℝ) * w.2.2 i)

/-- The compatibility constraint `κ + 3δ < 80λ` of v5 line 1190 is
satisfiable.  (`80λ ≈ 94.9`, so there is a great deal of room; the
constraint only becomes binding through the constants of Lemma 3.3 and
of the local `q`-estimate, which are not part of this statement.) -/
theorem exists_admissible_kappa_delta :
    ∃ κ δ : ℝ, 0 < κ ∧ 0 < δ ∧ κ + 3 * δ < 80 * lyapunov := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlam : 0 < lyapunov := by
    unfold lyapunov
    have hp : 0 < Real.pi ^ 2 := by positivity
    exact div_pos hp (by linarith)
  exact ⟨lyapunov, lyapunov, hlam, hlam, by linarith⟩

/-- The anti-concentration selection inside the proof of Lemma 6.3
(v5 lines 1186-1196), with `κ` and `δ` separated as v5 separates them.
On each complete depth-`d` cylinder the pair `(A_w, B_w)` of (31) is
fixed; if it is nonzero, Lemma 3.3 applied with `η = e^{-κH}` removes a
set of measure `O(e^{-cH})` and leaves `|Q_j| ≥ e^{-κH} q_j`, while the
local `q`-estimate leaves `q_j ≥ e^{λj - δH}`.

**Reading.**  `Qfreq α j B A = A q_j - B q_{j-1}` is the manuscript's
`Q_j` for the pair `(A_w, B_w)`, since `Qfreq α j r s = s q_j - r q_{j-1}`.
The bound is uniform in the nonzero pair, which is what makes the sum
over the finitely many words in `words` harmless.

**Order of quantifiers.**  The exceptional set must be chosen *after* the
pair `(A,B)`, not before it.  With `∃ E` outermost the statement is false
for every `κ` and `δ`, and `Lemma63.not_goodCylinderSelection` proves it so:
a single `E` cannot serve all pairs at once, since `(A,B) = (q_{j-1}, q_j)`
makes `Q_j` vanish at every irrational `α`.  The manuscript's Lemma 3.3 is
uniform in the nonzero pair, which is exactly the form below.  The
anti-concentration half is proved at this order as
`Lemma63.good_cylinder_selection_antiConc`; the continuant half is display
(20). -/
theorem lemma_6_3_good_cylinder_selection (κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ)
    (hκδ : κ + 3 * δ < 80 * lyapunov) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ∀ A B : ℤ, (A, B) ≠ (0, 0) →
      ∃ E : Set ℝ, MeasurableSet E ∧
        (volume.restrict (Ioo (0 : ℝ) 1)).real E ≤ C * Real.exp (-c * Hscale n) ∧
        ∀ α ∈ Ioo (0 : ℝ) 1 \ E, Irrational α →
          Real.exp (lyapunov * j - δ * Hscale n) ≤ (denom α j : ℝ) ∧
          Real.exp (-κ * Hscale n) * (denom α j : ℝ) ≤ |(Qfreq α j B A : ℝ)| := by
  sorry

/-- The one-block step of Lemma 6.3 (v5 lines 1180-1216): the required
convergence, uniformly in `j`, for finite sums of cylinder-character
tests with finitely supported local digit amplitudes. -/
theorem lemma_6_3_cylinder_character_step (R : ℕ) (T : CylinderCharacterTest R) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ‖(∫ w, T.eval w ∂(actualWindowLaw R n j)) - ∫ w, T.eval w ∂(windowLaw R)‖ < ε := by
  sorry

/-- **Lemma 6.3** (uniform full-state transfer), v5 lines 1166-1179.
If `G : X_R → ℂ` is bounded and its discontinuity set has `μ_R`-measure
zero, then `sup_{j ∈ J_n} |∫ G dη^{(R)}_{n,j} - ∫ G dμ_R| → 0`.

See reading 2 for the rendering of the supremum. -/
theorem lemma_6_3_full_state_transfer (R : ℕ) (G : WindowSpace R → ℂ) (C : ℝ)
    (hGmeas : Measurable G) (hGbdd : ∀ w, ‖G w‖ ≤ C)
    (hGcont : windowLaw R {w | ¬ ContinuousAt G w} = 0) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      ‖(∫ w, G w ∂(actualWindowLaw R n j)) - ∫ w, G w ∂(windowLaw R)‖ < ε := by
  sorry

/-! ## The carry graph -/

/-- **(53)** `φ_z(d) = ⌈x(d + r) - s⌉` for `z = (x, r, s)`.

Kept `ℤ`-valued: the manuscript's carries are nonnegative, but that is a
theorem about the trajectories, not part of the definition. -/
def carryMap (x r s : ℝ) (d : ℤ) : ℤ := ⌈x * ((d : ℝ) + r) - s⌉

/-- **(9)** `u_j = {θ_j - x_j (d_j + θ_{j-1})}`, the carry read off the
integer part `d_j` of the height error. -/
def carryU (x r s : ℝ) (d : ℤ) : ℝ := Int.fract (s - x * ((d : ℝ) + r))

/-- `d_j = ⌊E_j⌋`, the integer part of the height error. -/
def actualCarry (α : ℝ) (n j : ℕ) : ℤ := ⌊heightError α n j⌋

/-- **The state split behind (9) and (53)**: the height error splits into
its integer part, the actual carry `d_j = ⌊E_j⌋`, and its fractional
part, which is the previous torus coordinate `θ_{j-1}`.  Indeed for
`j ≥ 1` one has `E_j = n β_{j-1} - N_j` with `N_j ∈ ℕ`, so
`{E_j} = {n β_{j-1}} = θ_{j-1}`; at `j = 0` all three terms vanish. -/
theorem heightError_eq_actualCarry_add_thetaPred (α : ℝ) (n j : ℕ) :
    heightError α n j = (actualCarry α n j : ℝ) + thetaPred α n j := by
  cases j with
  | zero =>
      have h0 : heightError α n 0 = 0 := heightError_zero_eqD α n
      show heightError α n 0 = ((⌊heightError α n 0⌋ : ℤ) : ℝ) + (0 : ℝ)
      rw [h0]
      norm_num
  | succ m =>
      have hfr : Int.fract (heightError α n (m + 1)) = thetaPred α n (m + 1) := by
        rw [heightError_succ_eqD,
          show ((heightSeq α n (m + 1) : ℕ) : ℝ)
              = ((heightSeq α n (m + 1) : ℤ) : ℝ) from by rfl,
          Int.fract_sub_intCast]
        rfl
      show heightError α n (m + 1)
          = ((⌊heightError α n (m + 1)⌋ : ℤ) : ℝ) + thetaPred α n (m + 1)
      rw [← hfr]
      exact (Int.floor_add_fract _).symm

/-- **(9)** in the present notation: the actual carry `u_j` of §2 is
`carryU` evaluated at the actual state.  The proof combines the split
`E_j = d_j + θ_{j-1}` with display (10), `θ_j = {u_j + x_j E_j}`. -/
theorem carry_eq_carryU (α : ℝ) (n j : ℕ) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) :
    carry α n j
      = carryU (gaussIter α j) (thetaPred α n j) (theta α n j) (actualCarry α n j) := by
  show carry α n j
      = Int.fract (theta α n j
          - gaussIter α j * ((actualCarry α n j : ℝ) + thetaPred α n j))
  rw [← heightError_eq_actualCarry_add_thetaPred α n j, theta_eq α hα hirr n j]
  have hkey : Int.fract (carry α n j + gaussIter α j * heightError α n j)
      - gaussIter α j * heightError α n j
      = carry α n j
        + ((-⌊carry α n j + gaussIter α j * heightError α n j⌋ : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [hkey, Int.fract_add_intCast]
  show Int.fract ((heightSeq α n j : ℝ) * gaussIter α j)
      = Int.fract (Int.fract ((heightSeq α n j : ℝ) * gaussIter α j))
  exact (Int.fract_fract _).symm

/-- v5 lines 1251-1252: the actual carries satisfy
`d_{j+1} = φ_{(x_j, θ_{j-1}, θ_j)}(d_j)`.  From the error recursion (5),
`E_{j+1} = x_j E_j + u_j`, so `⌊E_{j+1}⌋ = ⌊x_j E_j + u_j⌋`, while the
ceiling on the right unwinds through `θ_j = {u_j + x_j E_j}` and
`⌈-u_j⌉ = 0`. -/
theorem actualCarry_succ (α : ℝ) (n j : ℕ) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) :
    actualCarry α n (j + 1)
      = carryMap (gaussIter α j) (thetaPred α n j) (theta α n j) (actualCarry α n j) := by
  show ⌊heightError α n (j + 1)⌋
      = ⌈gaussIter α j * ((actualCarry α n j : ℝ) + thetaPred α n j) - theta α n j⌉
  rw [← heightError_eq_actualCarry_add_thetaPred α n j,
    heightError_recD α hα hirr n j, theta_eq α hα hirr n j]
  have hkey : gaussIter α j * heightError α n j
      - Int.fract (carry α n j + gaussIter α j * heightError α n j)
      = -(carry α n j)
        + ((⌊carry α n j + gaussIter α j * heightError α n j⌋ : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [hkey, Int.ceil_add_intCast, Int.ceil_neg,
    Int.floor_eq_zero_iff.mpr ⟨carry_nonneg α n j, carry_lt_one α n j⟩,
    show gaussIter α j * heightError α n j + carry α n j
        = carry α n j + gaussIter α j * heightError α n j from by ring]
  simp

/-- `E* ≤ 9/2`: the reciprocal-Fibonacci series is dominated termwise by
the geometric series `(3/2)(2/3)^ℓ`, whose sum is `9/2`. -/
theorem Estar_le_nine_halves : Estar ≤ 9 / 2 := by
  have hE : Estar = ∑' ℓ : ℕ, ((Nat.fib (ℓ + 1) : ℝ))⁻¹ := rfl
  have hsum : Summable (fun ℓ : ℕ => (3 / 2 : ℝ) * ((2 : ℝ) / 3) ^ ℓ) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have h1 : ∑' ℓ : ℕ, ((Nat.fib (ℓ + 1) : ℝ))⁻¹
      ≤ ∑' ℓ : ℕ, (3 / 2 : ℝ) * ((2 : ℝ) / 3) ^ ℓ :=
    Summable.tsum_le_tsum (fun ℓ => inv_fib_le_geomD ℓ) summable_inv_fibD hsum
  have h2 : ∑' ℓ : ℕ, (3 / 2 : ℝ) * ((2 : ℝ) / 3) ^ ℓ = (3 / 2 : ℝ) * (1 - 2 / 3)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  rw [hE]
  rw [h2] at h1
  norm_num at h1
  linarith

/-- v5 lines 1253-1258: combining the contraction `xe ≤ e' < xe + 1` with
the Fibonacci product bound (6), all actual trajectories and all pullback
trajectories started from zero stay in `[0, D]` for an absolute integer
`D`.  Here `D = 9`, matching the carry-graph bound of
`Kwon1002.CarryGraph`; the actual carries in fact satisfy the sharper
`d_j = ⌊E_j⌋ ∈ [0, ⌊E*⌋] ⊆ [0, 4]` by display (7). -/
theorem exists_absolute_carry_bound :
    ∃ D : ℕ, ∀ (α : ℝ), α ∈ Ioo (0 : ℝ) 1 → Irrational α → ∀ n j : ℕ,
      0 ≤ actualCarry α n j ∧ actualCarry α n j ≤ (D : ℤ) := by
  refine ⟨9, fun α hα hirr n j => ?_⟩
  have hE := heightError_mem_Icc α hα hirr n j
  constructor
  · exact Int.floor_nonneg.mpr hE.1
  · have h1 : heightError α n j ≤ 9 :=
      le_trans hE.2 (le_trans Estar_le_nine_halves (by norm_num))
    have h2 : ((⌊heightError α n j⌋ : ℤ) : ℝ) ≤ 9 := le_trans (Int.floor_le _) h1
    exact_mod_cast h2

/-- **(54)** The reset set
`R = {(x,r,s) : x < 1/(4(D+1)), 1/2 < s < 3/4}`. -/
def resetSet (D : ℕ) : Set NatExtTorus :=
  {z | z.1.1 < 1 / (4 * ((D : ℝ) + 1)) ∧ 1 / 2 < z.2.2 ∧ z.2.2 < 3 / 4}

/-- v5 lines 1264-1268: for `0 ≤ d ≤ D` and `z ∈ R` one has
`-3/4 < x(d+r) - s < -1/4`, hence `φ_z(d) = 0`.

The hypotheses `0 ≤ x` and `0 ≤ r < 1` are the canonical-representative
convention of v5 lines 1035-1037 (reading 4). -/
theorem carryMap_eq_zero_of_mem_resetSet (D : ℕ) (z : NatExtTorus)
    (hz : z ∈ resetSet D) (hx : 0 ≤ z.1.1) (hr0 : 0 ≤ z.2.1) (hr1 : z.2.1 < 1)
    (d : ℤ) (hd0 : 0 ≤ d) (hdD : d ≤ (D : ℤ)) :
    carryMap z.1.1 z.2.1 z.2.2 d = 0 := by
  obtain ⟨hx4, hs1, hs2⟩ := hz
  have hD : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  have hd0' : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd0
  have hdD' : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hdD
  have h1 : 0 ≤ z.1.1 * ((d : ℝ) + z.2.1) := mul_nonneg hx (by linarith)
  have h2 : z.1.1 * ((d : ℝ) + z.2.1) < 1 / 4 := by
    have hstep : z.1.1 * ((d : ℝ) + z.2.1) ≤ z.1.1 * ((D : ℝ) + 1) := by
      have : (d : ℝ) + z.2.1 ≤ (D : ℝ) + 1 := by linarith
      exact mul_le_mul_of_nonneg_left this hx
    have hlt : z.1.1 * ((D : ℝ) + 1) < (1 / (4 * ((D : ℝ) + 1))) * ((D : ℝ) + 1) :=
      mul_lt_mul_of_pos_right hx4 hD
    have heq : (1 / (4 * ((D : ℝ) + 1))) * ((D : ℝ) + 1) = 1 / 4 := by
      field_simp
    linarith
  simp only [carryMap, Int.ceil_eq_zero_iff, Set.mem_Ioc]
  constructor <;> linarith

/-- The `μ̂₀`-measure of the reset set is positive (v5 line 1269).

No dynamics is involved.  `μ̂₀` is Lebesgue measure on the box
`(0,1)⁴` weighted by `1/(log 2 (1+xy)²)`, a density that on that box lies
strictly between `1/(4 log 2)` and `1/log 2`.  The explicit sub-box
`(0, 1/(4(D+1))) × (0,1) × (0,1) × (1/2, 3/4)` is contained in the reset
set, so the lower bound on the density times its positive Lebesgue volume
bounds `μ̂₀(R)` from below; the upper bound on the density gives
`μ̂₀(R) ≤ μ̂₀(X) ≤ 1/log 2 < ∞`, which is what makes the real-valued
`Measure.real` positive rather than merely nonzero. -/
theorem resetSet_measure_pos (D : ℕ) : 0 < hatMu0.real (resetSet D) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hdens : Measurable (fun z : NatExtTorus =>
      ENNReal.ofReal (1 / (Real.log 2 * (1 + z.1.1 * z.1.2) ^ 2))) := by
    refine Measurable.ennreal_ofReal ?_
    fun_prop
  set c : ℝ := 1 / (4 * ((D : ℝ) + 1)) with hc
  have hDpos : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcle : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]
    have hD : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
    linarith
  set Box : Set NatExtTorus :=
    (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) with hBox
  set S : Set NatExtTorus :=
    (Ioo (0 : ℝ) c ×ˢ Ioo (0 : ℝ) 1) ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (1 / 2 : ℝ) (3 / 4)) with hS
  have hBoxMeas : MeasurableSet Box :=
    (measurableSet_Ioo.prod measurableSet_Ioo).prod
      (measurableSet_Ioo.prod measurableSet_Ioo)
  have hSMeas : MeasurableSet S :=
    (measurableSet_Ioo.prod measurableSet_Ioo).prod
      (measurableSet_Ioo.prod measurableSet_Ioo)
  have hvolBox : volume Box = 1 := by
    simp only [hBox, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
    norm_num
  have hvolS : volume S ≠ 0 := by
    simp only [hS, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
    have h1 : ENNReal.ofReal (c - 0) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
    have h2 : ENNReal.ofReal ((1 : ℝ) - 0) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; norm_num
    have h3 : ENNReal.ofReal ((3 / 4 : ℝ) - 1 / 2) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; norm_num
    exact mul_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero h2 h3)
  -- `S` sits inside the ambient box and inside the reset set
  have hSsubBox : S ⊆ Box := by
    intro z hz
    rw [hS] at hz
    rw [hBox]
    simp only [Set.mem_prod, Set.mem_Ioo] at hz ⊢
    obtain ⟨⟨⟨hx0, hx1⟩, hy⟩, ht1, ht20, ht21⟩ := hz
    exact ⟨⟨⟨hx0, lt_of_lt_of_le hx1 hcle⟩, hy⟩, ht1, by linarith, by linarith⟩
  have hSsubReset : S ⊆ resetSet D := by
    intro z hz
    rw [hS] at hz
    simp only [Set.mem_prod, Set.mem_Ioo] at hz
    obtain ⟨⟨⟨_, hx1⟩, _⟩, _, ht20, ht21⟩ := hz
    refine ⟨?_, ht20, ht21⟩
    rw [← hc]
    exact hx1
  -- the measure is finite: the density is at most `1 / log 2` on the box
  have hupper : hatMu0 Set.univ ≤ ENNReal.ofReal (1 / Real.log 2) := by
    rw [show hatMu0 = (volume.restrict Box).withDensity
        (fun z => ENNReal.ofReal (1 / (Real.log 2 * (1 + z.1.1 * z.1.2) ^ 2))) from rfl,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hle : ∀ z ∈ Box, ENNReal.ofReal (1 / (Real.log 2 * (1 + z.1.1 * z.1.2) ^ 2))
        ≤ ENNReal.ofReal (1 / Real.log 2) := by
      intro z hz
      rw [hBox] at hz
      simp only [Set.mem_prod, Set.mem_Ioo] at hz
      obtain ⟨⟨⟨hx0, _⟩, hy0, _⟩, _⟩ := hz
      refine ENNReal.ofReal_le_ofReal ?_
      have hxy : 0 < z.1.1 * z.1.2 := mul_pos hx0 hy0
      have h1 : (1 : ℝ) ≤ (1 + z.1.1 * z.1.2) ^ 2 := by nlinarith
      have h2 : Real.log 2 ≤ Real.log 2 * (1 + z.1.1 * z.1.2) ^ 2 := by nlinarith
      exact one_div_le_one_div_of_le hlog2 h2
    calc ∫⁻ z in Box, ENNReal.ofReal (1 / (Real.log 2 * (1 + z.1.1 * z.1.2) ^ 2))
        ≤ ∫⁻ _ in Box, ENNReal.ofReal (1 / Real.log 2) :=
          setLIntegral_mono measurable_const hle
      _ = ENNReal.ofReal (1 / Real.log 2) * volume Box := setLIntegral_const _ _
      _ = ENNReal.ofReal (1 / Real.log 2) := by rw [hvolBox, mul_one]
  have hfin : hatMu0 (resetSet D) ≠ ⊤ := by
    have h1 : hatMu0 (resetSet D) ≤ ENNReal.ofReal (1 / Real.log 2) :=
      le_trans (measure_mono (subset_univ _)) hupper
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  -- the measure is positive: the density is at least `1 / (4 log 2)` on `S`
  have hSpos : 0 < hatMu0 S := by
    rw [show hatMu0 = (volume.restrict Box).withDensity
        (fun z => ENNReal.ofReal (1 / (Real.log 2 * (1 + z.1.1 * z.1.2) ^ 2))) from rfl,
      withDensity_apply _ hSMeas, Measure.restrict_restrict hSMeas,
      Set.inter_eq_self_of_subset_left hSsubBox]
    have hge : ∀ z ∈ S, ENNReal.ofReal (1 / (4 * Real.log 2))
        ≤ ENNReal.ofReal (1 / (Real.log 2 * (1 + z.1.1 * z.1.2) ^ 2)) := by
      intro z hz
      rw [hS] at hz
      simp only [Set.mem_prod, Set.mem_Ioo] at hz
      obtain ⟨⟨⟨hx0, hx1⟩, hy0, hy1⟩, _⟩ := hz
      refine ENNReal.ofReal_le_ofReal ?_
      have hx1' : z.1.1 < 1 := lt_of_lt_of_le hx1 hcle
      have hxy0 : 0 < z.1.1 * z.1.2 := mul_pos hx0 hy0
      have hxy1 : z.1.1 * z.1.2 < 1 := by nlinarith
      have hden : 0 < Real.log 2 * (1 + z.1.1 * z.1.2) ^ 2 := by positivity
      have hsq : (1 + z.1.1 * z.1.2) ^ 2 ≤ 4 := by nlinarith
      have h2 : Real.log 2 * (1 + z.1.1 * z.1.2) ^ 2 ≤ 4 * Real.log 2 := by
        have hmul := mul_le_mul_of_nonneg_left hsq hlog2.le
        linarith
      exact one_div_le_one_div_of_le hden h2
    have hlow : ENNReal.ofReal (1 / (4 * Real.log 2)) * volume S
        ≤ ∫⁻ z in S, ENNReal.ofReal (1 / (Real.log 2 * (1 + z.1.1 * z.1.2) ^ 2)) := by
      calc ENNReal.ofReal (1 / (4 * Real.log 2)) * volume S
          = ∫⁻ _ in S, ENNReal.ofReal (1 / (4 * Real.log 2)) := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ z in S, ENNReal.ofReal (1 / (Real.log 2 * (1 + z.1.1 * z.1.2) ^ 2)) :=
            setLIntegral_mono hdens hge
    refine lt_of_lt_of_le ?_ hlow
    refine ENNReal.mul_pos ?_ hvolS
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hpos : 0 < hatMu0 (resetSet D) := lt_of_lt_of_le hSpos (measure_mono hSsubReset)
  exact ENNReal.toReal_pos (ne_of_gt hpos) hfin

/-- **(56)** The stationary carry extension is a measurable invariant
graph `d_*` with `d_*(Sz) = φ_z(d_*(z))` (v5 lines 1269-1279). -/
theorem exists_carry_graph :
    ∃ D : ℕ, ∃ dstar : NatExtTorus → ℤ, Measurable dstar ∧
      (∀ z, 0 ≤ dstar z ∧ dstar z ≤ (D : ℤ)) ∧
      (∀ᵐ z ∂hatMu0, dstar (hatS z) = carryMap z.1.1 z.2.1 z.2.2 (dstar z)) := by
  sorry

/-- The carry obtained by setting the carry to zero at time `i` and
iterating `k` steps of `φ` along the actual orbit. -/
def carryFrom (α : ℝ) (n i : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 =>
      carryMap (gaussIter α (i + k)) (thetaPred α n (i + k)) (theta α n (i + k))
        (carryFrom α n i k)

/-- `d_j^{(R)}`: carry zero at time `j - R`, then `R` steps (v5 lines
1281-1283). -/
def carryTrunc (α : ℝ) (n R j : ℕ) : ℤ := carryFrom α n (j - R) R

/-- The no-reset set of v5 line 1284: no visit to `R` during the last
`R` steps. -/
def noResetSet (D R : ℕ) : Set NatExtTorus :=
  {z | ∀ t < R, hatS^[t] z ∉ resetSet D}

/-- `p_R = μ̂₀(⋂_{t<R} S^{-t} Rᶜ)`. -/
def noResetProb (D R : ℕ) : ℝ := hatMu0.real (noResetSet D R)

/-- Ergodicity and `μ̂₀(R) > 0` give `p_R → 0` (v5 lines 1286-1287). -/
theorem noResetProb_tendsto_zero (D : ℕ) :
    Tendsto (fun R => noResetProb D R) atTop (𝓝 0) := by
  sorry

/-- **(57)** `sup_{j ∈ J_n} P(d_j ≠ d_j^{(R)}) ≤ p_R + o_n(1)`
(v5 lines 1288-1293).  Whenever the actual orbit has a reset during
`[j-R, j)` the two carries agree; the no-reset indicator has
stationary-null boundary, so Lemma 6.3 applies to it. -/
theorem carry_coupling (D R : ℕ) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ∈ bulkJ n,
      (volume.restrict (Ioo (0 : ℝ) 1)).real
          {α | actualCarry α n j ≠ carryTrunc α n R j}
        ≤ noResetProb D R + ε := by
  sorry

/-! ## The bounded remainder and Proposition 6.4 -/

/-- **(11)** `B_j = Φ(x_j, u_j) - a_{j+1} W(θ_j)`, the bounded remainder
of the principal split. -/
def Bremainder (α : ℝ) (n j : ℕ) : ℝ :=
  Phi (gaussIter α j) (carry α n j) - (digit α j : ℝ) * W (theta α n j)

/-- `B_j^{(R)}`: the bounded remainder with `d_j` replaced by `d_j^{(R)}`
(v5 lines 1298-1300). -/
def BremainderTrunc (α : ℝ) (n R j : ℕ) : ℝ :=
  Phi (gaussIter α j)
      (carryU (gaussIter α j) (thetaPred α n j) (theta α n j) (carryTrunc α n R j))
    - (digit α j : ℝ) * W (theta α n j)

/-- The truncated carry as a function of the window: start from zero at
offset `-R` and iterate `φ` using the coordinates `(x_t, θ_{t-1}, θ_t)`
for `t = -R, …, -1`. -/
def windowCarry (R : ℕ) (w : WindowSpace R) : ℕ → ℤ
  | 0 => 0
  | k + 1 =>
      carryMap (wX w (-(R : ℤ) + k)) (wTh w (-(R : ℤ) + k - 1)) (wTh w (-(R : ℤ) + k))
        (windowCarry R w k)

/-- **The function `B^{(R)} : X_R → ℝ`** of v5 lines 1298-1305: a Borel
function whose restriction to the orbit-consistent support represents
`B_j^{(R)}` (`Bwindow_actualWindow`).  It is written out here rather than
merely asserted to exist, which makes the almost-everywhere claims
checkable — but note that, unlike the bounded representative whose
existence v5 asserts, this explicit choice is **not** globally bounded:
see `bwindow_unbounded` below. -/
def Bwindow (R : ℕ) (w : WindowSpace R) : ℝ :=
  Phi (wX w 0) (carryU (wX w 0) (wTh w (-1)) (wTh w 0) (windowCarry R w R))
    - (wA w 0 : ℝ) * W (wTh w 0)

/-- `BwindowRep` is a concrete bounded Borel representative compatible with
the v9 manuscript's existential choice (lines 1417-1425): the clamp of the
raw `Bwindow` to `[-45/8, 45/8]`, used in downstream
`display_55_monomial_approximation` and `actual_L2_transfer`. -/
def BwindowRep (R : ℕ) (w : WindowSpace R) : ℝ :=
  max (-(45 / 8 : ℝ)) (min (45 / 8 : ℝ) (Bwindow R w))

/-- The digit reader on an actual window: `wA` at offset `t` reads
`digit α (j + t)`, whenever the offset is in range and `j ≥ R` keeps the
truncated subtraction honest. -/
theorem wA_actualWindow (R : ℕ) (α : ℝ) (n j : ℕ) (hj : R ≤ j) {t : ℤ}
    (h1 : -(R : ℤ) ≤ t) (h2 : t ≤ (R : ℤ)) :
    wA (actualWindow R α n j) t = digit α ((j : ℤ) + t).toNat := by
  have hc : 0 ≤ t + (R : ℤ) ∧ t + (R : ℤ) < 2 * (R : ℤ) + 1 := ⟨by omega, by omega⟩
  simp only [wA, actualWindow, dif_pos hc]
  congr 1
  omega

/-- The real reader on an actual window. -/
theorem wX_actualWindow (R : ℕ) (α : ℝ) (n j : ℕ) (hj : R ≤ j) {t : ℤ}
    (h1 : -(R : ℤ) ≤ t) (h2 : t ≤ (R : ℤ)) :
    wX (actualWindow R α n j) t = gaussIter α ((j : ℤ) + t).toNat := by
  have hc : 0 ≤ t + (R : ℤ) ∧ t + (R : ℤ) < 2 * (R : ℤ) + 1 := ⟨by omega, by omega⟩
  simp only [wX, actualWindow, dif_pos hc]
  congr 1
  omega

/-- The torus reader on an actual window: `wTh` at offset `t` reads
`θ_{j+t}`. -/
theorem wTh_actualWindow (R : ℕ) (α : ℝ) (n j : ℕ) (hj : R + 1 ≤ j) {t : ℤ}
    (h1 : -(R : ℤ) - 1 ≤ t) (h2 : t ≤ (R : ℤ)) :
    wTh (actualWindow R α n j) t = theta α n ((j : ℤ) + t).toNat := by
  have hc : 0 ≤ t + (R : ℤ) + 1 ∧ t + (R : ℤ) + 1 < 2 * (R : ℤ) + 2 := ⟨by omega, by omega⟩
  simp only [wTh, actualWindow, dif_pos hc]
  congr 1
  omega

/-- Iterating the window carry along an actual window reads exactly the
actual coordinates `(x_{j-R+k}, θ_{j-R+k-1}, θ_{j-R+k})`, so it computes
`carryFrom` restarted at time `j - R`. -/
theorem windowCarry_actualWindow (R : ℕ) (α : ℝ) (n j : ℕ) (hj : R + 1 ≤ j) :
    ∀ k, k ≤ R → windowCarry R (actualWindow R α n j) k = carryFrom α n (j - R) k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hk' : k ≤ R := by omega
      show carryMap (wX (actualWindow R α n j) (-(R : ℤ) + k))
          (wTh (actualWindow R α n j) (-(R : ℤ) + k - 1))
          (wTh (actualWindow R α n j) (-(R : ℤ) + k))
          (windowCarry R (actualWindow R α n j) k)
        = carryMap (gaussIter α (j - R + k)) (thetaPred α n (j - R + k))
            (theta α n (j - R + k)) (carryFrom α n (j - R) k)
      have hpred : thetaPred α n (j - R + k) = theta α n (j - R + k - 1) := by
        obtain ⟨m, hm⟩ : ∃ m, j - R + k = m + 1 := ⟨j - R + k - 1, by omega⟩
        rw [hm]
        rfl
      rw [wX_actualWindow R α n j (by omega) (t := -(R : ℤ) + k) (by omega) (by omega),
        wTh_actualWindow R α n j hj (t := -(R : ℤ) + k - 1) (by omega) (by omega),
        wTh_actualWindow R α n j hj (t := -(R : ℤ) + k) (by omega) (by omega),
        ih hk', hpred,
        show ((j : ℤ) + (-(R : ℤ) + k)).toNat = j - R + k from by omega,
        show ((j : ℤ) + (-(R : ℤ) + k - 1)).toNat = j - R + k - 1 from by omega]

/-- `B_j^{(R)} = B^{(R)}(W^{(R)}_{n,j})` (v5 lines 1300-1302). -/
theorem Bwindow_actualWindow (R : ℕ) (α : ℝ) (n j : ℕ) (hj : R + 1 ≤ j) :
    Bwindow R (actualWindow R α n j) = BremainderTrunc α n R j := by
  have hX0 : wX (actualWindow R α n j) 0 = gaussIter α j := by
    rw [wX_actualWindow R α n j (by omega) (by omega) (by omega)]
    congr 1
  have hT0 : wTh (actualWindow R α n j) 0 = theta α n j := by
    rw [wTh_actualWindow R α n j hj (by omega) (by omega)]
    congr 1
  have hTm : wTh (actualWindow R α n j) (-1) = thetaPred α n j := by
    rw [wTh_actualWindow R α n j hj (by omega) (by omega)]
    have hpred : thetaPred α n j = theta α n (j - 1) := by
      obtain ⟨m, hm⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      rw [hm]
      rfl
    rw [hpred]
    congr 1
    omega
  have hA0 : wA (actualWindow R α n j) 0 = digit α j := by
    rw [wA_actualWindow R α n j (by omega) (by omega) (by omega)]
    congr 1
  have hWC : windowCarry R (actualWindow R α n j) R = carryTrunc α n R j :=
    windowCarry_actualWindow R α n j hj R le_rfl
  show Phi (wX (actualWindow R α n j) 0)
      (carryU (wX (actualWindow R α n j) 0) (wTh (actualWindow R α n j) (-1))
        (wTh (actualWindow R α n j) 0) (windowCarry R (actualWindow R α n j) R))
    - (wA (actualWindow R α n j) 0 : ℝ) * W (wTh (actualWindow R α n j) 0)
    = BremainderTrunc α n R j
  rw [hX0, hTm, hT0, hA0, hWC]
  rfl

/-- **`B^{(R)}` as written is *not* globally bounded on `WindowSpace R`.**
The digit block of `WindowSpace R` is an unconstrained copy of `ℕ` and the
type does not couple it to the real block, so the term
`a_{j+1} W(θ_j)` grows without bound along windows whose central digit is
large while `W(θ_j) = 1/8` stays put; nothing in `Φ` can compensate,
because the real coordinate is pinned at `1` where `Φ` is bounded.  This
refutes global boundedness of the raw `Bwindow` for every `R`; the
downstream argument instead uses the bounded-representative contract
`BwindowRep_ae_continuous` below. -/
theorem bwindow_unbounded (R : ℕ) :
    ¬ ∃ C : ℝ, ∀ w : WindowSpace R, |Bwindow R w| ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (8 * (C + 1))
  set w : WindowSpace R :=
    (fun _ => m, fun _ => (1 : ℝ), fun _ => (1 / 2 : ℝ)) with hw
  have hcA : 0 ≤ (0 : ℤ) + (R : ℤ) ∧ (0 : ℤ) + (R : ℤ) < 2 * (R : ℤ) + 1 :=
    ⟨by omega, by omega⟩
  have hcT : 0 ≤ (0 : ℤ) + (R : ℤ) + 1 ∧ (0 : ℤ) + (R : ℤ) + 1 < 2 * (R : ℤ) + 2 :=
    ⟨by omega, by omega⟩
  have hA : wA w 0 = m := by
    simp only [hw, wA, dif_pos hcA]
  have hX : wX w 0 = 1 := by
    simp only [hw, wX, dif_pos hcA]
  have hT : wTh w 0 = 1 / 2 := by
    simp only [hw, wTh, dif_pos hcT]
  set u : ℝ := carryU (wX w 0) (wTh w (-1)) (wTh w 0) (windowCarry R w R) with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    simp only [carryU]
    exact Int.fract_nonneg _
  have hu1 : u < 1 := by
    rw [hu]
    simp only [carryU]
    exact Int.fract_lt_one _
  have hW : W (1 / 2 : ℝ) = 1 / 8 := by
    unfold W
    rw [Int.fract_eq_self.mpr (by norm_num)]
    norm_num
  have hB : Bwindow R w = Phi 1 u - (m : ℝ) * (1 / 8) := by
    show Phi (wX w 0) u - (wA w 0 : ℝ) * W (wTh w 0) = Phi 1 u - (m : ℝ) * (1 / 8)
    rw [hX, hA, hT, hW]
  have hPhi : |Phi 1 u| ≤ 1 / 2 := by
    unfold Phi
    rw [abs_le]
    constructor <;> nlinarith
  have hkey := hC w
  rw [hB] at hkey
  have hlow : (m : ℝ) / 8 - 1 / 2 ≤ |Phi 1 u - (m : ℝ) * (1 / 8)| := by
    have h1 : (m : ℝ) * (1 / 8) - Phi 1 u ≤ |Phi 1 u - (m : ℝ) * (1 / 8)| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    have h2 : Phi 1 u ≤ 1 / 2 := (abs_le.mp hPhi).2
    linarith
  linarith

/-- `display_55_monomial_approximation` now uses `BwindowRep`, so this file
only requires the a.e.-continuity half from the bounded representative.

**Corrected bounded-representative contract (v9 lines 1417-1425).**
`BwindowRep` is bounded globally by construction, with the bound and
measurability proved downstream in `Prop64`.  What remains here is continuity:
`windowLaw R`-a.e. continuous at `BwindowRep`. -/
theorem BwindowRep_ae_continuous (R : ℕ) :
    windowLaw R {w | ¬ ContinuousAt (BwindowRep R) w} = 0 := by
  sorry

/-! ### The corrected display (55) -/

/-- The radius-`R'` word `(a_{j-R'+1}, …, a_{j+R'})` of (31) read off a
window in `X_{R'}`.  Compare `windowWord` of `Section4`, which reads the
same word off `α` directly. -/
def windowWordOf (R' : ℕ) (w : WindowSpace R') : Fin (2 * R') → ℕ :=
  fun i => wA w ((i : ℤ) - (R' : ℤ))

/-- A monomial (32) evaluated on the window space of its own radius. -/
def WindowSymbol.evalWindow {R' K : ℕ} (U : WindowSymbol R' K)
    (w : WindowSpace R') : ℂ :=
  ∑ r ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ∑ s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
    U.coeff (windowWordOf R' w) r s *
      torusChar ((r : ℝ) * wTh w (-1) + (s : ℝ) * wTh w 0)

/-- Placing a monomial at time `j` agrees with evaluating it on the
actual window: `U_j(α) = U(W^{(R')}_{n,j})`. -/
theorem WindowSymbol.evalWindow_actualWindow {R' K : ℕ} (U : WindowSymbol R' K)
    (α : ℝ) (n j : ℕ) (hj : R' + 1 ≤ j) :
    U.evalWindow (actualWindow R' α n j) = U.at α n j := by
  have hword : windowWordOf R' (actualWindow R' α n j) = windowWord R' α j := by
    funext i
    change wA (actualWindow R' α n j) ((i : ℤ) - (R' : ℤ)) = digit α (j + (i : ℕ) - R')
    rw [wA_actualWindow (R := R') (α := α) (n := n) (j := j) (t := (i : ℤ) - (R' : ℤ))
      (by omega) (by omega) (by omega)]
    have hnat : ((j : ℤ) + ((i : ℤ) - (R' : ℤ))).toNat = j + (i : ℕ) - R' := by
      omega
    simpa [hnat]
  have hT0 : wTh (actualWindow R' α n j) 0 = theta α n j := by
    rw [wTh_actualWindow R' α n j hj (by omega) (by omega)]
    have hnat : ((j : ℤ) + 0).toNat = j := by omega
    simpa [hnat]
  have hTm : wTh (actualWindow R' α n j) (-1) = thetaPred α n j := by
    rw [wTh_actualWindow R' α n j hj (by omega) (by omega)]
    have hpred : thetaPred α n j = theta α n (j - 1) := by
      obtain ⟨m, hm⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      rw [hm]
      rfl
    rw [show ((j : ℤ) + (-1)).toNat = j - 1 by omega, ← hpred]
  unfold WindowSymbol.evalWindow WindowSymbol.at
  simp [hword, hTm, hT0]

/-!
## Completed display (55), display (56), and Proposition 6.4

Their full statements and proofs live downstream, where all analytic providers
are available without an import cycle:

* `Kwon1002.display_55_monomial_approximation` is installed in `Prop64`;
* `Kwon1002.actual_L2_transfer` is installed in `Prop64Final` from the proved
  squared-error bulk-transfer provider;
* `Kwon1002.prop_6_4_bounded_remainder_weak_law` is installed in
  `Prop64Final` from the completed centered-`L²` assembly.

Keeping those canonical names out of this upstream skeleton prevents a reader
from finding a stale `sorry` when searching for the completed theorem.
-/

end

end Kwon1002
