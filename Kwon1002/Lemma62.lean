import Kwon1002.Section6Skeleton
import Kwon1002.NatExtMeasure
import Kwon1002.NatExtInvariance
import Kwon1002.NatExtMixing
import Kwon1002.CylinderCharDense
import Kwon1002.CharacterReduction

/-!
# Scratch, §6 of v5: the fibre matrices, the character cocycle, and (50)

Work file for the `lem62` slice of §6: the four statements
`fibreMatrix_det`, `hatS_measurePreserving`, `resonance_bounded` and
`lemma_6_2_gauss_torus_mixing` of `Kwon1002/Section6Skeleton.lean`.

Every target below is reproduced token-identically from the skeleton; the
supporting definitions (`fibreMatrix`, `fibreProd`, `hatS`, `hatMu0`,
`NatExtTorus`, `natExtMap`) are the skeleton's own, imported rather than
copied, so the statements are literally about the same objects.

## What is proved here

* `fibreMatrix_det`, `fibreMatrix_transpose`, and the forward form
  `fibreProdT` of the transposed product
  `(A_{a_m} ⋯ A_{a_1})ᵀ = A_{a_1} ⋯ A_{a_m}` (the transpose reversal the
  proof of Lemma 6.2 performs at v5 lines 1121-1127).
* `torusChar_comp_hatS`: one step of the torus cocycle (49) acts on
  characters by the fibre matrix, `χ_k ∘ S = χ_{A_{a_1} k}`.
* `torusChar_hatS_iterate`: the iterate, `χ_k ∘ S^m = χ_{(A_{a_m} ⋯ A_{a_1})ᵀ k}`
  with the digits read along the Gauss orbit of the future coordinate.
  This is the identity that turns an `m`-step correlation into a single
  character in the torus variables, so that the fibre integral vanishes
  unless the resonance (50) holds.
* `resonance_bounded`, **(50)**, proved in full from Lemma 6.1.  The
  transposed product is unwound into the recurrence
  `ξ_{i+2} = ξ_i - a_{m-i} ξ_{i+1}`, the alternating renormalisation
  `z_i = (-1)^i ξ_i` puts it in the form Lemma 6.1 expects, and the two
  endpoint pairs are the coordinate pairs of `ℓ` and of `k`.  The
  hypothesis here is manuscript v8's, `k ≠ 0 ∨ ℓ ≠ 0`, which is weaker
  than the skeleton's pair `k ≠ 0`, `ℓ ≠ 0`; `resonance_zero_iff` records
  v8's reason, namely that under a resonance the invertibility of
  `(A_{a_m} ⋯ A_{a_1})ᵀ` over `ℤ` forces `k = 0` exactly when `ℓ = 0`.
* `fibreProd_det`, `isUnit_det_fibreProd_transpose`,
  `fibreProd_transpose_mulVec_eq_zero_iff`: determinant multiplicativity
  applied to `fibreMatrix_det`, and the resulting injectivity of `mulVec`
  by the transposed product on `ℤ²`.
* `resonance_bounded_along_orbit`, the form in which (50) is consumed by
  the proof of Lemma 6.2: the character produced by
  `torusChar_hatS_iterate` at time `m` never cancels a fixed nonzero
  character once `m` is large.

## The measure-theoretic substrate

Everything below is proved; this file carries no `sorry`.

* `natExtMap_measurePreserving` is **proved**, in
  `Kwon1002/NatExtInvariance.lean`: the natural extension preserves
  `ν̂ = hatNu` (density `1/(log 2 (1+xy)²)` on `(0,1)²`).  Restricted to a
  Gauss branch `σ` is a product map, so the change of variables is two
  one-dimensional antitone Jacobians and Fubini, and the density cocycle
  `1 + uv = (1+xy)/(x(a+y))` makes them cancel exactly;
* `natExtInv_measurePreserving` is **proved**, by conjugating the forward
  statement with the coordinate swap, under which both `ν̂` and the unit
  square are symmetric;
* `torusFibre_measurePreserving` is **proved**: the fibre map
  `(r,s) ↦ (s, {r - a s})` is a swap followed by a skew product over the
  identity, and the fibre rotation `r ↦ {r - a s}` preserves Lebesgue
  measure on `(0,1)` by an elementary two-piece translation argument in
  the `Int.fract` representation.  No `AddCircle` bridge was needed;
* `hatS_measurePreserving` is **proved**, by assembling the two through
  `MeasureTheory.MeasurePreserving.skew_product` on the product shape
  `hatMu0_eq_prod : μ̂₀ = ν̂ ⊗ m`.

`natExt_zero_mode_mixing` is now **proved**: it delegates to
`Kwon1002.NatExtMixing.natExt_zero_mode_mixing`, where the lifting of the
one-sided transfer-operator contraction to the two-sided natural
extension is built by hand (conditional-expectation collapse onto the
Gauss marginal, the `2 (1/2)^m` contraction of the past coordinate, and a
closed-set/thickening approximation of indicators by Lipschitz
observables).  See the module docstring of `Kwon1002/NatExtMixing.lean`
for the architecture.

`cylinderChar_dense_L2` (the `L²(μ̂₀)` density of finite digit-cylinder
functions times torus characters, v5 line 1149) is now **proved**, by
delegation to `Kwon1002.CylinderCharDense.cylinderChar_dense_L2_core`;
see that module's docstring for the architecture (product-measure Dynkin
argument, Fourier density on `AddCircle 1` through the null seam, cylinder
shrinking plus outer regularity on the Gauss factor, and the digit-cap
refinement to a common radius).

`lemma_6_2_gauss_torus_mixing` is now **proved**, in the `Assembly62`
section: `monoInd_corrTo` computes the `m`-step correlation of a single
pair of monomials exactly (Fubini over `μ̂₀ = ν̂ ⊗ m`, the cocycle
identity `torusChar_hatS_iterate`, and either `natExt_zero_mode_mixing`
for the zero modes or `resonance_bounded` plus the mean-zero character
integral for the rest), `span_corrTo` extends the limit bilinearly over
`Submodule.span ℂ monoSet`, and the final proof trades the indicators of
two arbitrary measurable sets for span members at an `L²`-controlled
`L¹` cost that is uniform in `m` by `hatS_measurePreserving`.

-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Kwon1002

namespace Lemma62

noncomputable section

/-! ## The fibre matrices -/

/-- `det A_a = -1`, so `A_a ∈ GL₂(ℤ)` (v5 lines 1052-1056). -/
theorem fibreMatrix_det (a : ℕ) : (fibreMatrix a).det = -1 := by
  rw [fibreMatrix, Matrix.det_fin_two_of]
  ring

/-- `A_a` is symmetric; this is what lets the proof of Lemma 6.2 replace
the transposes of v5 line 1125 by the matrices themselves. -/
theorem fibreMatrix_transpose (a : ℕ) : (fibreMatrix a).transpose = fibreMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fibreMatrix]

/-- The forward product `A_{a_1} A_{a_2} ⋯ A_{a_m}`.  Since each `A_a` is
symmetric this is `(A_{a_m} ⋯ A_{a_1})ᵀ`, i.e. exactly the matrix that
occurs in the resonance relation (50). -/
def fibreProdT (a : ℕ → ℕ) : ℕ → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => 1
  | m + 1 => fibreProdT a m * fibreMatrix (a (m + 1))

theorem fibreProd_transpose (a : ℕ → ℕ) (m : ℕ) :
    (fibreProd a m).transpose = fibreProdT a m := by
  induction m with
  | zero => simp [fibreProd, fibreProdT]
  | succ m ih =>
      simp only [fibreProd, fibreProdT, Matrix.transpose_mul, ih, fibreMatrix_transpose]

/-- The action of a fibre matrix on a column vector, written out. -/
theorem fibreMatrix_mulVec (a : ℕ) (v : Fin 2 → ℤ) :
    Matrix.mulVec (fibreMatrix a) v = ![v 1, v 0 - (a : ℤ) * v 1] := by
  funext i
  have hi : Matrix.mulVec (fibreMatrix a) v i = ∑ j, fibreMatrix a i j * v j := by
    simp [Matrix.mulVec, dotProduct]
  rw [hi, Fin.sum_univ_two]
  fin_cases i
  · simp [fibreMatrix]
  · simp [fibreMatrix]
    ring

/-! ## The character cocycle

One application of `hatS` moves the torus pair `(θ_{j-1}, θ_j)` by the
fibre matrix, so a character `χ_k` is carried to `χ_{A_a k}`.  Iterating
gives `χ_k ∘ S^m = χ_{(A_{a_m} ⋯ A_{a_1})ᵀ k}`, which is the identity
behind the fibre-integral computation at v5 lines 1118-1121. -/

/-- The future coordinate of the natural extension advances by the Gauss
map, so its `m`-th iterate is `gaussIter`. -/
theorem natExtMap_iterate_fst (m : ℕ) (p : ℝ × ℝ) :
    (natExtMap^[m] p).1 = gaussIter p.1 m := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, ih, natExtMap]
      simp [gaussIter, Function.iterate_succ_apply]

/-- `hatS` acts on the Gauss pair by `natExtMap`. -/
theorem hatS_iterate_fst (m : ℕ) (z : NatExtTorus) :
    (hatS^[m] z).1 = natExtMap^[m] z.1 := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, ih, hatS, Function.iterate_succ_apply]

/-- `hatSinv` acts on the Gauss pair by `natExtInv`; the backward
counterpart of `hatS_iterate_fst`, and what lets the stationary window be
read at negative offsets. -/
theorem hatSinv_iterate_fst (m : ℕ) (z : NatExtTorus) :
    (hatSinv^[m] z).1 = natExtInv^[m] z.1 := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, ih, hatSinv, Function.iterate_succ_apply]

/-- The digit consumed at time `m` along the `hatS` orbit is the `m`-th
Gauss digit of the future coordinate. -/
theorem digit_hatS_iterate (m : ℕ) (z : NatExtTorus) :
    digit (hatS^[m] z).1.1 0 = digit z.1.1 m := by
  rw [hatS_iterate_fst, natExtMap_iterate_fst]
  simp [digit, gaussIter]

/-- One step of the cocycle (49) on characters: `χ_k ∘ S = χ_{A_{a_1} k}`. -/
theorem torusChar_comp_hatS (z : NatExtTorus) (k : Fin 2 → ℤ) :
    torusChar ((k 0 : ℝ) * (hatS z).2.1 + (k 1 : ℝ) * (hatS z).2.2)
      = torusChar
          (((Matrix.mulVec (fibreMatrix (digit z.1.1 0)) k) 0 : ℝ) * z.2.1
            + ((Matrix.mulVec (fibreMatrix (digit z.1.1 0)) k) 1 : ℝ) * z.2.2) := by
  rw [fibreMatrix_mulVec]
  simp only [hatS, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hfr : ∀ t : ℝ, Int.fract t = t - (⌊t⌋ : ℝ) := fun _ => rfl
  have key :
      (k 0 : ℝ) * z.2.2
          + (k 1 : ℝ) * Int.fract (z.2.1 - ((digit z.1.1 0 : ℕ) : ℝ) * z.2.2)
        = ((k 1 : ℤ) : ℝ) * z.2.1 + ((k 0 - (digit z.1.1 0 : ℤ) * k 1 : ℤ) : ℝ) * z.2.2
            + ((-(k 1 * ⌊z.2.1 - ((digit z.1.1 0 : ℕ) : ℝ) * z.2.2⌋) : ℤ) : ℝ) := by
    rw [hfr]
    push_cast
    ring
  rw [key, torusChar_add_int]

/-- The iterated cocycle: `χ_k ∘ S^m = χ_{(A_{a_m} ⋯ A_{a_1})ᵀ k}`, with
the digits `a_i` read along the Gauss orbit of the future coordinate.
This is the step at v5 lines 1118-1127 that reduces an `m`-step
correlation of two cylinder-character test functions to a single
character, whose fibre integral vanishes unless (50) holds. -/
theorem torusChar_hatS_iterate' (m : ℕ) (z : NatExtTorus) (k : Fin 2 → ℤ) :
    torusChar ((k 0 : ℝ) * (hatS^[m] z).2.1 + (k 1 : ℝ) * (hatS^[m] z).2.2)
      = torusChar
          (((Matrix.mulVec (fibreProdT (fun i => digit z.1.1 (i - 1)) m) k) 0 : ℝ) * z.2.1
            + ((Matrix.mulVec (fibreProdT (fun i => digit z.1.1 (i - 1)) m) k) 1 : ℝ) * z.2.2) := by
  induction m generalizing k with
  | zero => simp [fibreProdT]
  | succ m ih =>
      rw [Function.iterate_succ_apply', torusChar_comp_hatS, digit_hatS_iterate, ih]
      have hstep : fibreProdT (fun i => digit z.1.1 (i - 1)) (m + 1)
          = fibreProdT (fun i => digit z.1.1 (i - 1)) m * fibreMatrix (digit z.1.1 m) := by
        simp [fibreProdT]
      rw [hstep, ← Matrix.mulVec_mulVec]

theorem torusChar_hatS_iterate (m : ℕ) (z : NatExtTorus) (k : Fin 2 → ℤ) :
    torusChar ((k 0 : ℝ) * (hatS^[m] z).2.1 + (k 1 : ℝ) * (hatS^[m] z).2.2)
      = torusChar
          (((Matrix.mulVec (fibreProd (fun i => digit z.1.1 (i - 1)) m).transpose k) 0 : ℝ)
              * z.2.1
            + ((Matrix.mulVec (fibreProd (fun i => digit z.1.1 (i - 1)) m).transpose k) 1 : ℝ)
              * z.2.2) := by
  rw [fibreProd_transpose]
  exact torusChar_hatS_iterate' m z k

/-! ## Lemma 6.1 unwound: the transposed product as a recurrence -/

/-- The scalar sequence of v5 lines 1128-1137: `ξ_0 = ℓ_0`, `ξ_1 = ℓ_1`,
`ξ_{i+2} = ξ_i - a_{m-i} ξ_{i+1}`. -/
def xiSeq (a : ℕ → ℕ) (m : ℕ) (l : Fin 2 → ℤ) : ℕ → ℤ
  | 0 => l 0
  | 1 => l 1
  | i + 2 => xiSeq a m l i - (a (m - i) : ℤ) * xiSeq a m l (i + 1)

theorem xiSeq_zero (a : ℕ → ℕ) (m : ℕ) (l : Fin 2 → ℤ) : xiSeq a m l 0 = l 0 := by
  simp [xiSeq]

theorem xiSeq_one (a : ℕ → ℕ) (m : ℕ) (l : Fin 2 → ℤ) : xiSeq a m l 1 = l 1 := by
  simp [xiSeq]

theorem xiSeq_add_two (a : ℕ → ℕ) (m : ℕ) (l : Fin 2 → ℤ) (i : ℕ) :
    xiSeq a m l (i + 2) = xiSeq a m l i - (a (m - i) : ℤ) * xiSeq a m l (i + 1) := by
  simp [xiSeq]

/-- The partial-product form of the unwinding: after `j ≤ m` steps the
vector `(A_{a_1} ⋯ A_{a_m}) ℓ` has been rewritten as
`(A_{a_1} ⋯ A_{a_{m-j}}) (ξ_j, ξ_{j+1})`. -/
theorem fibreProdT_mulVec_step (a : ℕ → ℕ) (m : ℕ) (l : Fin 2 → ℤ) :
    ∀ j, j ≤ m →
      Matrix.mulVec (fibreProdT a m) l
        = Matrix.mulVec (fibreProdT a (m - j)) ![xiSeq a m l j, xiSeq a m l (j + 1)] := by
  intro j
  induction j with
  | zero =>
      intro _
      simp only [Nat.sub_zero]
      congr 1
      funext i
      fin_cases i <;> simp [xiSeq_zero, xiSeq_one]
  | succ j ih =>
      intro hj
      rw [ih (Nat.le_of_succ_le hj)]
      have hms : m - j = (m - (j + 1)) + 1 := by omega
      have hidx : m - (j + 1) + 1 = m - j := by omega
      rw [hms]
      simp only [fibreProdT]
      rw [← Matrix.mulVec_mulVec, hidx]
      congr 1
      rw [fibreMatrix_mulVec]
      funext i
      fin_cases i <;> simp [xiSeq_add_two]

/-- The full unwinding: `(A_{a_m} ⋯ A_{a_1})ᵀ ℓ = (ξ_m, ξ_{m+1})`. -/
theorem fibreProdT_mulVec (a : ℕ → ℕ) (m : ℕ) (l : Fin 2 → ℤ) :
    Matrix.mulVec (fibreProdT a m) l = ![xiSeq a m l m, xiSeq a m l (m + 1)] := by
  have h := fibreProdT_mulVec_step a m l m le_rfl
  simpa [fibreProdT] using h

/-! ## `GL₂(ℤ)`: the transposed product is injective on `ℤ²`

Manuscript v8 justifies the resonance hypothesis by observing that in the
relation (50) the vector `ℓ` vanishes exactly when `k` does, because the
product of fibre matrices is invertible over `ℤ`.  That is recorded here:
determinant multiplicativity turns `fibreMatrix_det` into
`det (A_{a_m} ⋯ A_{a_1}) = (-1)^m`, a unit of `ℤ`, so the transposed product
has a two-sided inverse over `ℤ` and `mulVec` by it is injective. -/

/-- `det (A_{a_m} ⋯ A_{a_1}) = (-1)^m`, by determinant multiplicativity on
top of `fibreMatrix_det`. -/
theorem fibreProd_det (a : ℕ → ℕ) (m : ℕ) : (fibreProd a m).det = (-1) ^ m := by
  induction m with
  | zero => simp [fibreProd]
  | succ m ih =>
      rw [fibreProd, Matrix.det_mul, fibreMatrix_det, ih]
      ring

/-- The transposed product lies in `GL₂(ℤ)` (v5 lines 1052-1056). -/
theorem isUnit_det_fibreProd_transpose (a : ℕ → ℕ) (m : ℕ) :
    IsUnit ((fibreProd a m).transpose.det) := by
  rw [Matrix.det_transpose, fibreProd_det]
  exact IsUnit.pow m isUnit_one.neg

/-- `(A_{a_m} ⋯ A_{a_1})ᵀ` kills only the zero vector of `ℤ²`. -/
theorem fibreProd_transpose_mulVec_eq_zero_iff (a : ℕ → ℕ) (m : ℕ) (v : Fin 2 → ℤ) :
    (fibreProd a m).transpose.mulVec v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hinv := Matrix.nonsing_inv_mul _ (isUnit_det_fibreProd_transpose a m)
    calc v = (1 : Matrix (Fin 2) (Fin 2) ℤ).mulVec v := (Matrix.one_mulVec v).symm
      _ = ((fibreProd a m).transpose⁻¹ * (fibreProd a m).transpose).mulVec v := by rw [hinv]
      _ = (fibreProd a m).transpose⁻¹.mulVec ((fibreProd a m).transpose.mulVec v) := by
          rw [← Matrix.mulVec_mulVec]
      _ = 0 := by rw [h, Matrix.mulVec_zero]
  · rintro rfl
    exact Matrix.mulVec_zero _

/-- **v8's justification for the hypothesis of (50).**  Whenever the
resonance `k + (A_{a_m} ⋯ A_{a_1})ᵀ ℓ = 0` holds, `k = 0` if and only if
`ℓ = 0`.  So the two vectors are nonzero together, and asking that *one* of
them be nonzero, `k ≠ 0 ∨ ℓ ≠ 0`, is the hypothesis under which (50) is a
genuine obstruction. -/
theorem resonance_zero_iff (a : ℕ → ℕ) (m : ℕ) (k l : Fin 2 → ℤ)
    (h : k + (fibreProd a m).transpose.mulVec l = 0) : k = 0 ↔ l = 0 := by
  constructor
  · intro h0
    rw [h0, zero_add] at h
    exact (fibreProd_transpose_mulVec_eq_zero_iff a m l).mp h
  · intro h0
    rw [h0, Matrix.mulVec_zero, add_zero] at h
    exact h

/-! ## (50): the resonance is impossible for large `m` -/

/-- **(50)**, the character-resonance obstruction.  For fixed nonzero
integer vectors `k, ℓ`, the resonance `k + (A_{a_m} ⋯ A_{a_1})ᵀ ℓ = 0`
is impossible for all sufficiently large `m`, uniformly in the digit
sequence.  This is exactly what Lemma 6.1 buys: the transposed products
turn into the recurrence `z_{i+2} = a_{m-i} z_{i+1} + z_i` whose two
endpoint pairs are, up to signs, the coordinate pairs of `ℓ` and `k`
(v5 lines 1121-1147).

Consumes `Kwon1002.lemma_6_1_endpoint_recurrence`, which is sorried in
`Section6Skeleton.lean` and is proved in `Kwon1002/Lemma61.lean`.

**Hypothesis.**  This tracks manuscript v8, which asks only that `k` and
`ℓ` not both vanish.  The earlier rendering (still the one in
`Section6Skeleton.lean`) assumed both `k ≠ 0` and `ℓ ≠ 0`, and the proof
below shows that `ℓ ≠ 0` alone suffices for the Lemma 6.1 route: with
`k = 0` the two right-hand endpoints `z_m, z_{m+1}` are `0`, which the
endpoint bound `≤ K` accommodates, and the non-vanishing hypothesis of
Lemma 6.1 is supplied by `(z_0, z_1) = (ℓ_0, -ℓ_1) ≠ (0,0)` alone.  The
remaining case `ℓ = 0` is immediate, the left-hand side being `k`.  That
the two cases are exhaustive under `k ≠ 0 ∨ ℓ ≠ 0`, and that this is the
right hypothesis rather than an artificially weak one, is v8's
observation `resonance_zero_iff` above: under a resonance, invertibility
of `(A_{a_m} ⋯ A_{a_1})ᵀ` over `ℤ` forces `k = 0 ↔ ℓ = 0`. -/
theorem resonance_bounded (k l : Fin 2 → ℤ) (hkl : k ≠ 0 ∨ l ≠ 0) :
    ∃ M : ℕ, ∀ (m : ℕ), M ≤ m → ∀ a : ℕ → ℕ, (∀ i, 1 ≤ a i) →
      k + (fibreProd a m).transpose.mulVec l ≠ 0 := by
  rcases eq_or_ne l 0 with rfl | hl
  · refine ⟨0, fun m _ a _ => ?_⟩
    rw [Matrix.mulVec_zero, add_zero]
    exact hkl.resolve_right fun h => h rfl
  obtain ⟨C, _hC, hrec⟩ := lemma_6_1_endpoint_recurrence
  set K : ℝ := max (max |(k 0 : ℝ)| |(k 1 : ℝ)|) (max |(l 0 : ℝ)| |(l 1 : ℝ)|) with hK
  refine ⟨⌈C * Real.log (2 * K)⌉₊ + 1, ?_⟩
  intro m hm a ha hres
  -- the resonance says the transposed product sends `ℓ` to `-k`
  have h1 : Matrix.mulVec (fibreProd a m).transpose l = -k := by
    funext i
    have h := congrFun hres i
    simp only [Pi.add_apply, Pi.zero_apply] at h
    simp only [Pi.neg_apply]
    omega
  have h2 : ![xiSeq a m l m, xiSeq a m l (m + 1)] = -k := by
    rw [← fibreProdT_mulVec a m l, ← fibreProd_transpose]
    exact h1
  have hxm : xiSeq a m l m = -k 0 := by
    have := congrFun h2 0
    simpa using this
  have hxm1 : xiSeq a m l (m + 1) = -k 1 := by
    have := congrFun h2 1
    simpa using this
  -- the alternating renormalisation and the reversed digit sequence
  obtain ⟨z, hzdef⟩ : ∃ z : ℕ → ℤ, ∀ i, z i = (-1 : ℤ) ^ i * xiSeq a m l i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨a', ha'def⟩ : ∃ a' : ℕ → ℕ, ∀ i, a' i = a (m + 1 - i) := ⟨_, fun _ => rfl⟩
  have hA : ∀ i, 1 ≤ a' i := by intro i; rw [ha'def]; exact ha _
  have habs : ∀ (i : ℕ) (t : ℤ), |(((-1 : ℤ) ^ i * t : ℤ) : ℝ)| = |((t : ℤ) : ℝ)| := by
    intro i t
    push_cast
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  -- the recurrence in the form Lemma 6.1 expects
  have hrecur : ∀ i < m, z (i + 2) = (a' (i + 1) : ℤ) * z (i + 1) + z i := by
    intro i _
    rw [hzdef, hzdef, hzdef, ha'def, xiSeq_add_two]
    have hidx : m + 1 - (i + 1) = m - i := by omega
    rw [hidx]
    ring
  -- non-vanishing on `0 ≤ i ≤ m + 1`
  have hl' : l 0 ≠ 0 ∨ l 1 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hl (funext fun i => ?_)
    fin_cases i <;> simp [hcon.1, hcon.2]
  have hnz : ∃ i ≤ m + 1, z i ≠ 0 := by
    rcases hl' with h | h
    · exact ⟨0, by omega, by rw [hzdef, xiSeq_zero]; simpa using h⟩
    · exact ⟨1, by omega, by rw [hzdef, xiSeq_one]; simpa using h⟩
  -- the four endpoint bounds
  have b0 : |((z 0 : ℤ) : ℝ)| ≤ K := by
    rw [hzdef, xiSeq_zero, habs, hK]
    exact le_max_of_le_right (le_max_left _ _)
  have b1 : |((z 1 : ℤ) : ℝ)| ≤ K := by
    rw [hzdef, xiSeq_one, habs, hK]
    exact le_max_of_le_right (le_max_right _ _)
  have bm : |((z m : ℤ) : ℝ)| ≤ K := by
    rw [hzdef, hxm, habs, hK]
    push_cast
    rw [abs_neg]
    exact le_max_of_le_left (le_max_left _ _)
  have bm1 : |((z (m + 1) : ℤ) : ℝ)| ≤ K := by
    rw [hzdef, hxm1, habs, hK]
    push_cast
    rw [abs_neg]
    exact le_max_of_le_left (le_max_right _ _)
  have hfin : (m : ℝ) ≤ C * Real.log (2 * K) := hrec m a' z K hA hnz hrecur b0 b1 bm bm1
  have hceil : (m : ℝ) ≤ (⌈C * Real.log (2 * K)⌉₊ : ℝ) := hfin.trans (Nat.le_ceil _)
  have : m ≤ ⌈C * Real.log (2 * K)⌉₊ := by exact_mod_cast hceil
  omega

/-- Statement identity, type check only: the skeleton's `resonance_bounded`,
which still carries the pair of hypotheses `k ≠ 0` and `ℓ ≠ 0`, is the
specialisation of the version above.  The skeleton cannot delegate to this
file, since this file imports the skeleton; this `example` is what detects
drift between the two statements. -/
example : ∀ (k l : Fin 2 → ℤ), k ≠ 0 → l ≠ 0 →
    ∃ M : ℕ, ∀ (m : ℕ), M ≤ m → ∀ a : ℕ → ℕ, (∀ i, 1 ≤ a i) →
      k + (fibreProd a m).transpose.mulVec l ≠ 0 :=
  fun k l hk _hl => resonance_bounded k l (Or.inl hk)

/-- (50) in the form the proof of Lemma 6.2 consumes it: the character
produced by `torusChar_hatS_iterate` at time `m` cannot cancel a fixed
nonzero character `χ_ℓ` once `m` is large, uniformly over orbits whose
digits are all at least `1` (which by `GaussBasics.one_le_digit` is every
irrational future coordinate in `(0,1)`). -/
theorem resonance_bounded_along_orbit (k l : Fin 2 → ℤ) (hk : k ≠ 0) (hl : l ≠ 0) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ z : NatExtTorus, (∀ i, 1 ≤ digit z.1.1 i) →
      Matrix.mulVec (fibreProd (fun i => digit z.1.1 (i - 1)) m).transpose k + l ≠ 0 := by
  obtain ⟨M, hM⟩ := resonance_bounded l k (Or.inl hl)
  refine ⟨M, fun m hm z hz hcon => hM m hm (fun i => digit z.1.1 (i - 1)) (fun i => hz _) ?_⟩
  rw [add_comm]
  exact hcon

/-! ## The measure-theoretic inputs that this tree does not have -/

/-- **Proved.**  The Gauss natural extension preserves `ν̂ = hatNu`, the
measure with density `1/(log 2 (1+xy)²)` on `(0,1)²`
(`Kwon1002/NatExtMeasure.lean`).

This is manuscript v8's "the displayed density `ν̂` is `σ`-invariant by
branchwise change of variables" (line 1144), carried out in
`Kwon1002/NatExtInvariance.lean`.  The point that makes it elementary is
that *on a single branch* `σ` is a product map: for
`x ∈ (1/(a+1), 1/a)` the digit is constantly `a` and
`σ(x,y) = (1/x - a, 1/(a+y))`, whose first coordinate depends only on `x`
and second only on `y`.  So the Jacobian is diagonal and the
one-dimensional change of variables
`MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn`
applies twice, with no `HasFDerivWithinAt` on `ℝ × ℝ` anywhere.  The
density cocycle `1 + uv = (1+xy)/(x(a+y))` then makes the two Jacobians
cancel against the density exactly.

An earlier revision of this docstring recorded the whole statement as an
open obstruction, on the ground that the BV chain in this tree only ever
handles the one-sided Gauss map.  That was true of the BV chain and
irrelevant to this statement: nothing about the two-sided extension is
needed beyond the branch partition. -/
theorem natExtMap_measurePreserving :
    MeasurePreserving natExtMap hatNu hatNu :=
  NatExtInvariance.natExtMap_measurePreserving

/-- **Proved.**  For each digit `a`, the fibre map `(r,s) ↦ (s, {r - a s})`
of (49) preserves Haar on `T²`, this being the `GL₂(ℤ)`-invariance of v5
lines 1052-1056 (`fibreMatrix_det` above is the determinant half of it).

The map factors as a swap followed by a skew product over the identity,
which is literally the shape of
`MeasureTheory.MeasurePreserving.skew_product`: the base coordinate `s` is
untouched and the fibre map `r ↦ {r - a s}` is a rotation of the circle.
No `AddCircle` bridge is needed.  An earlier revision of this docstring
recorded the missing bridge as the obstruction; the obstruction was softer
than that, because the rotation is elementary in the `Int.fract`
representation itself: it cuts `[0,1)` at `1 - {a s}` and translates the
two pieces, and translations preserve Lebesgue measure
(`NatExtMeasure.map_fract_add_Ico`).  The `Ioo`/`Ico` mismatch is a null
set (`NatExtMeasure.restrict_Ioo_eq_Ico`).

Note that the fibre coordinate of the image can be `0`, which is outside
`(0,1)`; that costs nothing, since `MeasurePreserving` constrains the
pushforward measure and the discrepancy is a null set. -/
theorem torusFibre_measurePreserving (a : ℕ) :
    MeasurePreserving (fun q : ℝ × ℝ => (q.2, Int.fract (q.1 - (a : ℝ) * q.2)))
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
  rw [NatExtMeasure.restrict_unitSq_eq_prod]
  set μ := (volume : Measure ℝ).restrict (Ioo (0:ℝ) 1) with hμ
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) (μ.prod μ) (μ.prod μ) :=
    MeasureTheory.Measure.measurePreserving_swap
  have hskew : MeasurePreserving
      (fun p : ℝ × ℝ => (id p.1, Int.fract (p.2 - (a : ℝ) * p.1))) (μ.prod μ) (μ.prod μ) := by
    refine (MeasurePreserving.id μ).skew_product
      (g := fun s r : ℝ => Int.fract (r - (a : ℝ) * s)) ?_ ?_
    · exact (measurable_snd.sub (measurable_fst.const_mul _)).fract
    · filter_upwards with s
      exact NatExtMeasure.map_fract_sub_Ioo ((a : ℝ) * s)
  simpa [Function.comp] using hskew.comp hswap

/-- **Proved.**  The backward natural-extension map also preserves `ν̂`.
`natExtInv` is `natExtMap` conjugated by the coordinate swap
(`NatExtInvariance.natExtInv_eq_swap`), and both `ν̂` and the unit square
are symmetric in the two coordinates, so no second branch analysis is
needed.  This is what the negative powers `hatSzpow` at negative exponents
need in order to be measure preserving. -/
theorem natExtInv_measurePreserving :
    MeasurePreserving natExtInv hatNu hatNu :=
  NatExtInvariance.natExtInv_measurePreserving

/-- **Proved.**  The cocycle (49) preserves `μ̂₀`.

With `natExtMap_measurePreserving` in hand this is the mechanical skew
product the earlier revision of this docstring predicted:
`hatMu0_eq_prod` puts `μ̂₀` in the shape `ν̂ ⊗ m` that
`MeasureTheory.MeasurePreserving.skew_product` consumes, the base half is
`natExtMap_measurePreserving`, and the fibre half is
`torusFibre_measurePreserving` at the digit `a₁` read off the base point.
The predicted wrinkle about the torus coordinates being swapped relative
to `torusFibre_measurePreserving` did not materialise: `hatS` writes the
torus block as `(θ, {θ' - a θ})` and the fibre lemma is stated in exactly
that shape, so the two match on the nose. -/
theorem hatS_measurePreserving : MeasurePreserving hatS hatMu0 hatMu0 := by
  rw [hatMu0_eq_prod]
  have hgm : Measurable (Function.uncurry
      (fun (p : ℝ × ℝ) (q : ℝ × ℝ) => (q.2, Int.fract (q.1 - (digit p.1 0 : ℝ) * q.2)))) := by
    refine Measurable.prodMk (measurable_snd.comp measurable_snd) ?_
    exact ((measurable_fst.comp measurable_snd).sub
      (((measurable_digitCast 0).comp (measurable_fst.comp measurable_fst)).mul
        (measurable_snd.comp measurable_snd))).fract
  have hg : ∀ᵐ p ∂hatNu, Measure.map
      (fun q : ℝ × ℝ => (q.2, Int.fract (q.1 - (digit p.1 0 : ℝ) * q.2)))
      ((volume : Measure (ℝ × ℝ)).restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))
      = (volume : Measure (ℝ × ℝ)).restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    Filter.Eventually.of_forall
      (fun p => (torusFibre_measurePreserving (digit p.1 0)).map_eq)
  exact natExtMap_measurePreserving.skew_product hgm hg

/-- The zero-mode half of Lemma 6.2 (v5 line 1148): on characters with
`k = ℓ = 0` the correlation is a correlation of the Gauss natural
extension alone — the two-sided system `((0,1)², ν̂, σ)` is mixing.

**Proved**, by delegation to
`Kwon1002.NatExtMixing.natExt_zero_mode_mixing`.  An earlier revision of
this docstring recorded the absence of a lifting from the one-sided BV
chain to the two-sided extension as the obstruction; the lifting is now
built by hand in `Kwon1002/NatExtMixing.lean`: the future coordinate of
`σ^m` is `T^m x` exactly, the past coordinate is a `2 (1/2)^m`-contraction
in its initial condition, so freezing the past and collapsing the
conditional expectation onto the Gauss marginal turns the two-sided
correlation into a one-sided one against the frozen-past observable, and
Wang's transfer contraction closes it at rate `(527/540)^(m/2)` for
coordinate-Lipschitz observables; indicators follow by inner regularity
and thickened-indicator approximation. -/
theorem natExt_zero_mode_mixing (A B : Set (ℝ × ℝ))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun m : ℕ => hatNu.real (A ∩ natExtMap^[m] ⁻¹' B))
      atTop (𝓝 (hatNu.real A * hatNu.real B)) :=
  NatExtMixing.natExt_zero_mode_mixing A B hA hB

/-- Finite digit-cylinder functions times torus characters are dense in
`L²(μ̂₀)` (v5 line 1149, "density of cylinder functions times characters
in `L²` completes the proof").

**Proved**, by delegation to
`Kwon1002.CylinderCharDense.cylinderChar_dense_L2_core`; the direct term
application doubles as the drift guard tying the two statements together.
An earlier revision of this docstring recorded the missing cylinder
sigma-algebra and the missing `L²` density lemma as the obstruction; both
are now built in `Kwon1002/CylinderCharDense.lean`: `μ̂₀ = ν̂ ⊗ m` reduces
density to the two factors through a Dynkin argument over rectangles, the
torus factor is Fourier density on `AddCircle 1` transported through the
null seam of the `[0,1)` representation, the Gauss factor is the shrinking
of closed prefix cylinders (`(1/4)^(d/2)` diameter) plus outer regularity,
and a digit-cap refinement (`digit_tail_product`) rewrites the resulting
mixed-depth combination as one `WindowSymbol` of a common radius. -/
theorem cylinderChar_dense_L2 (f : NatExtTorus → ℂ) (hf : MemLp f 2 hatMu0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (R K : ℕ) (U : WindowSymbol R K),
      eLpNorm (fun z => f z - U.eval z) 2 hatMu0 < ENNReal.ofReal ε :=
  CylinderCharDense.cylinderChar_dense_L2_core f hf ε hε

/-! ## The assembly: from monomials to arbitrary indicators

The proof of Lemma 6.2 runs over the test class
`CylinderCharDense.monoSet`, the base-set indicators times two-mode torus
characters whose span is dense in `L²(μ̂₀)` (`monoSet_span_dense`).  For a
single pair of monomials the `m`-step correlation is computed exactly:
the cocycle identity `torusChar_hatS_iterate` collapses the two torus
characters into one of mode `k + (A_{a_m} ⋯ A_{a_1})ᵀ ℓ`, Fubini over
`μ̂₀ = ν̂ ⊗ m` (`hatMu0_eq_prod`) integrates that character out to an
indicator of the resonance (50), and then either all modes vanish — the
zero-mode case, closed by `natExt_zero_mode_mixing` — or
`resonance_bounded` kills the fibre integral outright for all large `m`
while `integral_torusChar_pair_eq_zero` kills the limit.  Bilinearity
extends the limit over the span, and an `L²`-approximation argument
extends it from the span to indicators of arbitrary measurable sets. -/

section Assembly62

open CylinderCharDense

/-- A single Gauss-torus monomial: the indicator of a base set times a
two-mode torus character.  Every generator of `monoSet` has this shape
(`monoSet_repr`), and it is the shape the §6 cocycle computation
consumes. -/
def monoInd (D : Set (ℝ × ℝ)) (r s : ℤ) : NatExtTorus → ℂ := fun z =>
  indC D z.1 * torusChar ((r : ℝ) * z.2.1 + (s : ℝ) * z.2.2)

theorem norm_indC_le {X : Type*} (D : Set X) (x : X) : ‖indC D x‖ ≤ 1 := by
  by_cases h : x ∈ D <;> simp [indC, Set.indicator_apply, h]

theorem indC_eq_ofReal {X : Type*} (D : Set X) (x : X) :
    indC D x = ((D.indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) := by
  by_cases h : x ∈ D <;> simp [indC, Set.indicator_apply, h]

theorem integral_indC {X : Type*} [MeasurableSpace X] (μ : Measure X) {D : Set X}
    (hD : MeasurableSet D) : ∫ x, indC D x ∂μ = ((μ.real D : ℝ) : ℂ) := by
  rw [indC, integral_indicator_const (1 : ℂ) hD, Complex.real_smul, mul_one]

theorem norm_monoInd_le (D : Set (ℝ × ℝ)) (r s : ℤ) (z : NatExtTorus) :
    ‖monoInd D r s z‖ ≤ 1 := by
  simp only [monoInd, norm_mul, Prop42.norm_torusChar, mul_one]
  exact norm_indC_le D z.1

theorem measurable_monoInd {D : Set (ℝ × ℝ)} (hD : MeasurableSet D) (r s : ℤ) :
    Measurable (monoInd D r s) := by
  refine ((measurable_indC hD).comp measurable_fst).mul ?_
  exact Prop42.continuous_torusChar.measurable.comp
    (((measurable_fst.comp measurable_snd).const_mul _).add
      ((measurable_snd.comp measurable_snd).const_mul _))

/-- Every generator of `monoSet` is a `monoInd` at a measurable base
rectangle: the two cylinder indicators merge into the indicator of their
product, and the two one-mode characters merge into one two-mode
character. -/
theorem monoSet_repr {g : NatExtTorus → ℂ} (hg : g ∈ monoSet) :
    ∃ (D : Set (ℝ × ℝ)) (r s : ℤ), MeasurableSet D ∧ g = monoInd D r s := by
  obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hg
  obtain ⟨i₁, hi₁, i₂, hi₂, rfl⟩ := hg₁
  obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := hg₂
  obtain ⟨d₁, w₁, rfl⟩ := hi₁
  obtain ⟨d₂, w₂, rfl⟩ := hi₂
  obtain ⟨r, rfl⟩ := hc₁
  obtain ⟨s, rfl⟩ := hc₂
  refine ⟨Prop41.cylinder d₁ w₁ ×ˢ Prop41.cylinder d₂ w₂, r, s,
    (measurableSet_cylinder d₁ w₁).prod (measurableSet_cylinder d₂ w₂), ?_⟩
  funext z
  simp only [monoInd]
  rw [MonomialCore.torusChar_add]
  have hind : indC (Prop41.cylinder d₁ w₁) z.1.1 * indC (Prop41.cylinder d₂ w₂) z.1.2
      = indC (Prop41.cylinder d₁ w₁ ×ˢ Prop41.cylinder d₂ w₂) z.1 := by
    by_cases h1 : z.1.1 ∈ Prop41.cylinder d₁ w₁ <;>
      by_cases h2 : z.1.2 ∈ Prop41.cylinder d₂ w₂ <;>
        simp [indC, Set.indicator_apply, h1, h2, Set.mem_prod]
  rw [← hind]

theorem vecPair_eq_zero_iff {r s : ℤ} : (![r, s] : Fin 2 → ℤ) = 0 ↔ r = 0 ∧ s = 0 := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩
    funext i
    fin_cases i <;> rfl

theorem pair_ne_of_ne_zero {u : Fin 2 → ℤ} (hu : u ≠ 0) : (u 0, u 1) ≠ (0, 0) := by
  intro h
  apply hu
  funext i
  fin_cases i
  · simpa using congrArg Prod.fst h
  · simpa using congrArg Prod.snd h

/-- The Haar integral of a two-mode character: `1` at the trivial mode,
`0` otherwise (`MonomialCore.integral_torusChar_pair_eq_zero`). -/
theorem integral_torusChar_vec (u : Fin 2 → ℤ) :
    (∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
        torusChar ((u 0 : ℝ) * q.1 + (u 1 : ℝ) * q.2))
      = if u = 0 then 1 else 0 := by
  by_cases hu : u = 0
  · subst hu
    simp only [Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, torusChar_zero, if_pos]
    simp
  · rw [if_neg hu]
    exact MonomialCore.integral_torusChar_pair_eq_zero (pair_ne_of_ne_zero hu)

/-- The pointwise collapse of an `m`-step monomial correlation: the two
torus characters merge into a single character whose mode is the
resonance combination `k + (A_{a_m} ⋯ A_{a_1})ᵀ ℓ` of (50). -/
theorem monoInd_mul_comp (D₁ D₂ : Set (ℝ × ℝ)) (r₁ s₁ r₂ s₂ : ℤ) (m : ℕ)
    (z : NatExtTorus) :
    monoInd D₁ r₁ s₁ z * monoInd D₂ r₂ s₂ (hatS^[m] z)
      = (indC D₁ z.1 * indC D₂ (natExtMap^[m] z.1)) *
          torusChar
            ((((![r₁, s₁] + (fibreProd (fun i => digit z.1.1 (i - 1)) m).transpose.mulVec
                ![r₂, s₂]) 0 : ℤ) : ℝ) * z.2.1
              + (((![r₁, s₁] + (fibreProd (fun i => digit z.1.1 (i - 1)) m).transpose.mulVec
                ![r₂, s₂]) 1 : ℤ) : ℝ) * z.2.2) := by
  have hχ := torusChar_hatS_iterate m z ![r₂, s₂]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hχ
  have hmerge : torusChar ((r₁ : ℝ) * z.2.1 + (s₁ : ℝ) * z.2.2)
      * torusChar
          ((((fibreProd (fun i => digit z.1.1 (i - 1)) m).transpose.mulVec ![r₂, s₂]) 0 : ℝ)
              * z.2.1
            + (((fibreProd (fun i => digit z.1.1 (i - 1)) m).transpose.mulVec ![r₂, s₂]) 1 : ℝ)
              * z.2.2)
      = torusChar
          ((((![r₁, s₁] + (fibreProd (fun i => digit z.1.1 (i - 1)) m).transpose.mulVec
              ![r₂, s₂]) 0 : ℤ) : ℝ) * z.2.1
            + (((![r₁, s₁] + (fibreProd (fun i => digit z.1.1 (i - 1)) m).transpose.mulVec
              ![r₂, s₂]) 1 : ℤ) : ℝ) * z.2.2) := by
    rw [← MonomialCore.torusChar_add]
    congr 1
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    ring
  simp only [monoInd, hatS_iterate_fst, hχ]
  rw [mul_mul_mul_comm, hmerge]

/-- The `m`-step monomial correlation, Fubini'd: the torus factor
integrates to the indicator of the resonance (50). -/
theorem monoInd_corr_eq {D₁ D₂ : Set (ℝ × ℝ)} (hD₁ : MeasurableSet D₁)
    (hD₂ : MeasurableSet D₂) (r₁ s₁ r₂ s₂ : ℤ) (m : ℕ) :
    ∫ z, monoInd D₁ r₁ s₁ z * monoInd D₂ r₂ s₂ (hatS^[m] z) ∂hatMu0
      = ∫ p, (indC D₁ p * indC D₂ (natExtMap^[m] p)) *
          (if ![r₁, s₁] + (fibreProd (fun i => digit p.1 (i - 1)) m).transpose.mulVec ![r₂, s₂]
              = 0 then 1 else 0) ∂hatNu := by
  have hint : Integrable
      (fun z : NatExtTorus => monoInd D₁ r₁ s₁ z * monoInd D₂ r₂ s₂ (hatS^[m] z)) hatMu0 := by
    refine (integrable_const (1 : ℝ)).mono'
      ((measurable_monoInd hD₁ r₁ s₁).mul ((measurable_monoInd hD₂ r₂ s₂).comp
        (hatS_measurePreserving.measurable.iterate m))).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_one₀ (norm_monoInd_le _ _ _ _) (norm_nonneg _) (norm_monoInd_le _ _ _ _)
  rw [funext (monoInd_mul_comp D₁ D₂ r₁ s₁ r₂ s₂ m)] at hint ⊢
  rw [hatMu0_eq_prod] at hint ⊢
  rw [MeasureTheory.integral_prod _ hint]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact integral_torusChar_vec _

/-- The stationary integral of a monomial: the base mass times the
indicator of the trivial mode. -/
theorem monoInd_integral {D : Set (ℝ × ℝ)} (hD : MeasurableSet D) (r s : ℤ) :
    ∫ z, monoInd D r s z ∂hatMu0
      = ((hatNu.real D : ℝ) : ℂ) * (if r = 0 ∧ s = 0 then 1 else 0) := by
  have hsplit := MeasureTheory.integral_prod_mul (μ := hatNu)
      (ν := (volume : Measure (ℝ × ℝ)).restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))
      (f := indC D) (g := fun q : ℝ × ℝ => torusChar ((r : ℝ) * q.1 + (s : ℝ) * q.2))
  rw [hatMu0_eq_prod]
  rw [show (fun z : NatExtTorus => monoInd D r s z)
      = fun z : (ℝ × ℝ) × ℝ × ℝ => indC D z.1
          * (fun q : ℝ × ℝ => torusChar ((r : ℝ) * q.1 + (s : ℝ) * q.2)) z.2 from rfl]
  rw [hsplit, integral_indC hatNu hD]
  congr 1
  have hv := integral_torusChar_vec ![r, s]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hv
  rw [hv]
  simp [vecPair_eq_zero_iff]

/-- The two-sided correlation property against `hatS`: the `m`-step
correlation converges to the product of the stationary means. -/
def CorrTo (f g : NatExtTorus → ℂ) : Prop :=
  Tendsto (fun m : ℕ => ∫ z, f z * g (hatS^[m] z) ∂hatMu0) atTop
    (𝓝 ((∫ z, f z ∂hatMu0) * ∫ z, g z ∂hatMu0))

/-- **The generator case of Lemma 6.2**: the correlation limit for a
single pair of monomials.  Zero modes reduce to the mixing of the Gauss
natural extension; a nonzero mode pair makes the correlation *equal* to
zero for all large `m` by (50), while the limit is zero because a
nontrivial character has mean zero. -/
theorem monoInd_corrTo {D₁ D₂ : Set (ℝ × ℝ)} (hD₁ : MeasurableSet D₁)
    (hD₂ : MeasurableSet D₂) (r₁ s₁ r₂ s₂ : ℤ) :
    CorrTo (monoInd D₁ r₁ s₁) (monoInd D₂ r₂ s₂) := by
  by_cases hzero : r₁ = 0 ∧ s₁ = 0 ∧ r₂ = 0 ∧ s₂ = 0
  · obtain ⟨h1, h2, h3, h4⟩ := hzero
    subst h1; subst h2; subst h3; subst h4
    have hv : (![(0 : ℤ), 0] : Fin 2 → ℤ) = 0 := vecPair_eq_zero_iff.mpr ⟨rfl, rfl⟩
    have hseq : ∀ m : ℕ, ∫ z, monoInd D₁ 0 0 z * monoInd D₂ 0 0 (hatS^[m] z) ∂hatMu0
        = ((hatNu.real (D₁ ∩ natExtMap^[m] ⁻¹' D₂) : ℝ) : ℂ) := by
      intro m
      rw [monoInd_corr_eq hD₁ hD₂ 0 0 0 0 m]
      rw [show (fun p : ℝ × ℝ => (indC D₁ p * indC D₂ (natExtMap^[m] p)) *
            (if ![(0 : ℤ), 0] + (fibreProd (fun i => digit p.1 (i - 1)) m).transpose.mulVec
                ![(0 : ℤ), 0] = 0 then (1 : ℂ) else 0))
          = fun p : ℝ × ℝ =>
              (((D₁.indicator (fun _ => (1 : ℝ)) p
                  * D₂.indicator (fun _ => (1 : ℝ)) (natExtMap^[m] p) : ℝ)) : ℂ) by
        funext p
        rw [if_pos (by rw [hv, Matrix.mulVec_zero, add_zero]), mul_one,
          indC_eq_ofReal, indC_eq_ofReal, Complex.ofReal_mul]]
      rw [integral_complex_ofReal, ← NatExtMixing.hatNuReal_inter_eq D₁ D₂ hD₁ hD₂ m]
    have hlim : Tendsto (fun m => ((hatNu.real (D₁ ∩ natExtMap^[m] ⁻¹' D₂) : ℝ) : ℂ)) atTop
        (𝓝 ((hatNu.real D₁ * hatNu.real D₂ : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp
        (NatExtMixing.natExt_zero_mode_mixing D₁ D₂ hD₁ hD₂)
    unfold CorrTo
    rw [monoInd_integral hD₁ 0 0, monoInd_integral hD₂ 0 0, if_pos ⟨rfl, rfl⟩, mul_one, mul_one,
      show ((hatNu.real D₁ : ℝ) : ℂ) * ((hatNu.real D₂ : ℝ) : ℂ)
        = ((hatNu.real D₁ * hatNu.real D₂ : ℝ) : ℂ) by push_cast; ring]
    exact Tendsto.congr (fun m => (hseq m).symm) hlim
  · have hor : (![r₁, s₁] : Fin 2 → ℤ) ≠ 0 ∨ (![r₂, s₂] : Fin 2 → ℤ) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hzero ⟨(vecPair_eq_zero_iff.mp hcon.1).1, (vecPair_eq_zero_iff.mp hcon.1).2,
        (vecPair_eq_zero_iff.mp hcon.2).1, (vecPair_eq_zero_iff.mp hcon.2).2⟩
    obtain ⟨M₀, hM₀⟩ := resonance_bounded ![r₁, s₁] ![r₂, s₂] hor
    have hev : (fun m : ℕ => ∫ z, monoInd D₁ r₁ s₁ z * monoInd D₂ r₂ s₂ (hatS^[m] z) ∂hatMu0)
        =ᶠ[atTop] fun _ => (0 : ℂ) := by
      filter_upwards [eventually_ge_atTop M₀] with m hm
      rw [monoInd_corr_eq hD₁ hD₂ r₁ s₁ r₂ s₂ m]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [NatExtMixing.hatNu_ae_good] with p hp
      rw [if_neg (hM₀ m hm (fun i => digit p.1 (i - 1))
        (fun i => one_le_digit hp.1 hp.2.2 (i - 1))), mul_zero]
      rfl
    have hzero_lim : (∫ z, monoInd D₁ r₁ s₁ z ∂hatMu0) * ∫ z, monoInd D₂ r₂ s₂ z ∂hatMu0
        = 0 := by
      rcases hor with hk | hl
      · rw [monoInd_integral hD₁ r₁ s₁,
          if_neg (fun hc => hk (vecPair_eq_zero_iff.mpr hc)), mul_zero, zero_mul]
      · rw [monoInd_integral hD₂ r₂ s₂,
          if_neg (fun hc => hl (vecPair_eq_zero_iff.mpr hc)), mul_zero, mul_zero]
    unfold CorrTo
    rw [hzero_lim]
    exact Tendsto.congr' hev.symm tendsto_const_nhds

/-! ### The correlation calculus over the span -/

/-- Bounded measurable observables: the closure properties the bilinear
extension of the correlation limit needs. -/
structure Tame (f : NatExtTorus → ℂ) : Prop where
  meas : Measurable f
  bdd : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C

theorem tame_of_mem_monoSet {f : NatExtTorus → ℂ} (hf : f ∈ monoSet) : Tame f := by
  obtain ⟨D, r, s, hD, rfl⟩ := monoSet_repr hf
  exact ⟨measurable_monoInd hD r s, 1, norm_monoInd_le D r s⟩

theorem tame_of_mem_span {f : NatExtTorus → ℂ}
    (hf : f ∈ Submodule.span ℂ monoSet) : Tame f := by
  induction hf using Submodule.span_induction with
  | mem g hg => exact tame_of_mem_monoSet hg
  | zero => exact ⟨measurable_const, 0, fun z => by simp⟩
  | add f₁ f₂ _ _ h₁ h₂ =>
      obtain ⟨C₁, hC₁⟩ := h₁.bdd
      obtain ⟨C₂, hC₂⟩ := h₂.bdd
      exact ⟨h₁.meas.add h₂.meas, C₁ + C₂,
        fun z => (norm_add_le _ _).trans (add_le_add (hC₁ z) (hC₂ z))⟩
  | smul c f₁ _ h =>
      obtain ⟨C, hC⟩ := h.bdd
      refine ⟨h.meas.const_smul c, ‖c‖ * C, fun z => ?_⟩
      rw [Pi.smul_apply, norm_smul]
      exact mul_le_mul_of_nonneg_left (hC z) (norm_nonneg c)

theorem Tame.integrable {f : NatExtTorus → ℂ} (hf : Tame f) : Integrable f hatMu0 := by
  obtain ⟨C, hC⟩ := hf.bdd
  exact (integrable_const C).mono' hf.meas.aestronglyMeasurable (Eventually.of_forall hC)

theorem integrable_corr {f g : NatExtTorus → ℂ} (hf : Tame f) (hg : Tame g) (m : ℕ) :
    Integrable (fun z => f z * g (hatS^[m] z)) hatMu0 := by
  obtain ⟨C₁, hC₁⟩ := hf.bdd
  obtain ⟨C₂, hC₂⟩ := hg.bdd
  refine (integrable_const (C₁ * C₂)).mono'
    (hf.meas.mul (hg.meas.comp (hatS_measurePreserving.measurable.iterate m))).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [norm_mul]
  exact mul_le_mul (hC₁ z) (hC₂ _) (norm_nonneg _) ((norm_nonneg _).trans (hC₁ z))

theorem corrTo_zero_right (f : NatExtTorus → ℂ) : CorrTo f 0 := by
  unfold CorrTo
  simp only [Pi.zero_apply, mul_zero, integral_zero]
  exact tendsto_const_nhds

theorem corrTo_zero_left (g : NatExtTorus → ℂ) : CorrTo 0 g := by
  unfold CorrTo
  simp only [Pi.zero_apply, zero_mul, integral_zero]
  exact tendsto_const_nhds

theorem corrTo_add_right {f g₁ g₂ : NatExtTorus → ℂ} (hf : Tame f) (hg₁ : Tame g₁)
    (hg₂ : Tame g₂) (h₁ : CorrTo f g₁) (h₂ : CorrTo f g₂) : CorrTo f (g₁ + g₂) := by
  unfold CorrTo at h₁ h₂ ⊢
  have hseq : ∀ m : ℕ, ∫ z, f z * (g₁ + g₂) (hatS^[m] z) ∂hatMu0
      = (∫ z, f z * g₁ (hatS^[m] z) ∂hatMu0) + ∫ z, f z * g₂ (hatS^[m] z) ∂hatMu0 := by
    intro m
    rw [← integral_add (integrable_corr hf hg₁ m) (integrable_corr hf hg₂ m)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    ring
  have htarget : (∫ z, f z ∂hatMu0) * ∫ z, (g₁ + g₂) z ∂hatMu0
      = (∫ z, f z ∂hatMu0) * ∫ z, g₁ z ∂hatMu0
        + (∫ z, f z ∂hatMu0) * ∫ z, g₂ z ∂hatMu0 := by
    simp only [Pi.add_apply]
    rw [integral_add hg₁.integrable hg₂.integrable]
    ring
  rw [htarget]
  exact Tendsto.congr (fun m => (hseq m).symm) (h₁.add h₂)

theorem corrTo_add_left {f₁ f₂ g : NatExtTorus → ℂ} (hf₁ : Tame f₁) (hf₂ : Tame f₂)
    (hg : Tame g) (h₁ : CorrTo f₁ g) (h₂ : CorrTo f₂ g) : CorrTo (f₁ + f₂) g := by
  unfold CorrTo at h₁ h₂ ⊢
  have hseq : ∀ m : ℕ, ∫ z, (f₁ + f₂) z * g (hatS^[m] z) ∂hatMu0
      = (∫ z, f₁ z * g (hatS^[m] z) ∂hatMu0) + ∫ z, f₂ z * g (hatS^[m] z) ∂hatMu0 := by
    intro m
    rw [← integral_add (integrable_corr hf₁ hg m) (integrable_corr hf₂ hg m)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    ring
  have htarget : (∫ z, (f₁ + f₂) z ∂hatMu0) * ∫ z, g z ∂hatMu0
      = (∫ z, f₁ z ∂hatMu0) * ∫ z, g z ∂hatMu0
        + (∫ z, f₂ z ∂hatMu0) * ∫ z, g z ∂hatMu0 := by
    simp only [Pi.add_apply]
    rw [integral_add hf₁.integrable hf₂.integrable]
    ring
  rw [htarget]
  exact Tendsto.congr (fun m => (hseq m).symm) (h₁.add h₂)

theorem corrTo_smul_right {f g : NatExtTorus → ℂ} (c : ℂ) (h : CorrTo f g) :
    CorrTo f (c • g) := by
  unfold CorrTo at h ⊢
  have hseq : ∀ m : ℕ, ∫ z, f z * (c • g) (hatS^[m] z) ∂hatMu0
      = c * ∫ z, f z * g (hatS^[m] z) ∂hatMu0 := by
    intro m
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have htarget : (∫ z, f z ∂hatMu0) * ∫ z, (c • g) z ∂hatMu0
      = c * ((∫ z, f z ∂hatMu0) * ∫ z, g z ∂hatMu0) := by
    simp only [Pi.smul_apply]
    rw [integral_smul, smul_eq_mul]
    ring
  rw [htarget]
  exact Tendsto.congr (fun m => (hseq m).symm) (h.const_mul c)

theorem corrTo_smul_left {f g : NatExtTorus → ℂ} (c : ℂ) (h : CorrTo f g) :
    CorrTo (c • f) g := by
  unfold CorrTo at h ⊢
  have hseq : ∀ m : ℕ, ∫ z, (c • f) z * g (hatS^[m] z) ∂hatMu0
      = c * ∫ z, f z * g (hatS^[m] z) ∂hatMu0 := by
    intro m
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have htarget : (∫ z, (c • f) z ∂hatMu0) * ∫ z, g z ∂hatMu0
      = c * ((∫ z, f z ∂hatMu0) * ∫ z, g z ∂hatMu0) := by
    simp only [Pi.smul_apply]
    rw [integral_smul, smul_eq_mul]
    ring
  rw [htarget]
  exact Tendsto.congr (fun m => (hseq m).symm) (h.const_mul c)

theorem corrTo_of_mem {f g : NatExtTorus → ℂ} (hf : f ∈ monoSet) (hg : g ∈ monoSet) :
    CorrTo f g := by
  obtain ⟨D₁, r₁, s₁, hD₁, rfl⟩ := monoSet_repr hf
  obtain ⟨D₂, r₂, s₂, hD₂, rfl⟩ := monoSet_repr hg
  exact monoInd_corrTo hD₁ hD₂ r₁ s₁ r₂ s₂

/-- The correlation limit holds across the whole span of the monomials. -/
theorem span_corrTo {f g : NatExtTorus → ℂ}
    (hf : f ∈ Submodule.span ℂ monoSet)
    (hg : g ∈ Submodule.span ℂ monoSet) : CorrTo f g := by
  induction hf using Submodule.span_induction with
  | mem f₀ hf₀ =>
      induction hg using Submodule.span_induction with
      | mem g₀ hg₀ => exact corrTo_of_mem hf₀ hg₀
      | zero => exact corrTo_zero_right _
      | add g₁ g₂ hg₁ hg₂ h₁ h₂ =>
          exact corrTo_add_right (tame_of_mem_monoSet hf₀)
            (tame_of_mem_span hg₁) (tame_of_mem_span hg₂) h₁ h₂
      | smul c g₁ _ h => exact corrTo_smul_right c h
  | zero => exact corrTo_zero_left _
  | add f₁ f₂ hf₁ hf₂ h₁ h₂ =>
      exact corrTo_add_left (tame_of_mem_span hf₁) (tame_of_mem_span hf₂)
        (tame_of_mem_span hg) h₁ h₂
  | smul c f₁ _ h => exact corrTo_smul_left c h

/-! ### The `L²` approximation step -/

/-- Push-forward invariance of `μ̂₀`-integrals along the iterated cocycle. -/
theorem integral_comp_hatS_iterate (h : NatExtTorus → ℝ) (hm : Measurable h) (m : ℕ) :
    ∫ z, h (hatS^[m] z) ∂hatMu0 = ∫ z, h z ∂hatMu0 := by
  have hmp : MeasurePreserving (hatS^[m]) hatMu0 hatMu0 := hatS_measurePreserving.iterate m
  calc ∫ z, h (hatS^[m] z) ∂hatMu0
      = ∫ y, h y ∂(hatMu0.map (hatS^[m])) :=
        (integral_map hmp.measurable.aemeasurable hm.aestronglyMeasurable).symm
    _ = ∫ z, h z ∂hatMu0 := by rw [hmp.map_eq]

/-- `L¹(μ̂₀)` control from `L²(μ̂₀)` control, on the probability space. -/
theorem integral_norm_le_of_L2 {u : NatExtTorus → ℂ} (hu : Measurable u) {ε : ℝ}
    (hε : 0 < ε) (h2 : eLpNorm u 2 hatMu0 < ENNReal.ofReal ε) :
    ∫ z, ‖u z‖ ∂hatMu0 ≤ ε := by
  have h1 : eLpNorm u 1 hatMu0 ≤ eLpNorm u 2 hatMu0 :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hu.aestronglyMeasurable
  have hnorm : ∫ z, ‖u z‖ ∂hatMu0 = (eLpNorm u 1 hatMu0).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact integral_norm_eq_lintegral_enorm hu.aestronglyMeasurable
  rw [hnorm]
  exact ENNReal.toReal_le_of_le_ofReal hε.le (h1.trans h2.le)

/-- Replacing the left factor of a correlation costs at most the `L¹`
distance, when the right factor is bounded by `1`. -/
theorem corr_replace_left {f₁ f₂ g : NatExtTorus → ℂ} (h₁ : Tame f₁) (h₂ : Tame f₂)
    (hg : Tame g) (hgb : ∀ z, ‖g z‖ ≤ 1) (m : ℕ) :
    ‖(∫ z, f₁ z * g (hatS^[m] z) ∂hatMu0) - ∫ z, f₂ z * g (hatS^[m] z) ∂hatMu0‖
      ≤ ∫ z, ‖(f₁ - f₂) z‖ ∂hatMu0 := by
  rw [← integral_sub (integrable_corr h₁ hg m) (integrable_corr h₂ hg m)]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono ((integrable_corr h₁ hg m).sub (integrable_corr h₂ hg m)).norm
    (h₁.integrable.sub h₂.integrable).norm fun z => ?_
  rw [show f₁ z * g (hatS^[m] z) - f₂ z * g (hatS^[m] z)
      = (f₁ z - f₂ z) * g (hatS^[m] z) by ring, norm_mul, Pi.sub_apply]
  exact mul_le_of_le_one_right (norm_nonneg _) (hgb _)

/-- Replacing the right factor of a correlation costs at most the sup
bound of the left factor times the `L¹` distance, by stationarity. -/
theorem corr_replace_right {f g₁ g₂ : NatExtTorus → ℂ} (hf : Tame f) {Cf : ℝ}
    (hfb : ∀ z, ‖f z‖ ≤ Cf) (h₁ : Tame g₁) (h₂ : Tame g₂) (m : ℕ) :
    ‖(∫ z, f z * g₁ (hatS^[m] z) ∂hatMu0) - ∫ z, f z * g₂ (hatS^[m] z) ∂hatMu0‖
      ≤ Cf * ∫ z, ‖(g₁ - g₂) z‖ ∂hatMu0 := by
  have hdint : Integrable (fun z => ‖(g₁ - g₂) (hatS^[m] z)‖) hatMu0 := by
    obtain ⟨C₁, hC₁⟩ := h₁.bdd
    obtain ⟨C₂, hC₂⟩ := h₂.bdd
    refine (integrable_const (C₁ + C₂)).mono'
      (((h₁.meas.sub h₂.meas).norm).comp
        (hatS_measurePreserving.measurable.iterate m)).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Pi.sub_apply]
    exact (norm_sub_le _ _).trans (add_le_add (hC₁ _) (hC₂ _))
  rw [← integral_sub (integrable_corr hf h₁ m) (integrable_corr hf h₂ m)]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hcomp : ∫ z, ‖(g₁ - g₂) (hatS^[m] z)‖ ∂hatMu0 = ∫ z, ‖(g₁ - g₂) z‖ ∂hatMu0 :=
    integral_comp_hatS_iterate _ ((h₁.meas.sub h₂.meas).norm) m
  calc ∫ z, ‖f z * g₁ (hatS^[m] z) - f z * g₂ (hatS^[m] z)‖ ∂hatMu0
      ≤ ∫ z, Cf * ‖(g₁ - g₂) (hatS^[m] z)‖ ∂hatMu0 := by
        refine integral_mono
          ((integrable_corr hf h₁ m).sub (integrable_corr hf h₂ m)).norm
          (hdint.const_mul Cf) fun z => ?_
        rw [show f z * g₁ (hatS^[m] z) - f z * g₂ (hatS^[m] z)
            = f z * ((g₁ - g₂) (hatS^[m] z)) by rw [Pi.sub_apply]; ring, norm_mul]
        exact mul_le_mul_of_nonneg_right (hfb z) (norm_nonneg _)
    _ = Cf * ∫ z, ‖(g₁ - g₂) (hatS^[m] z)‖ ∂hatMu0 := MeasureTheory.integral_const_mul _ _
    _ = Cf * ∫ z, ‖(g₁ - g₂) z‖ ∂hatMu0 := by rw [hcomp]

theorem norm_integral_sub_le {f g : NatExtTorus → ℂ} (hf : Tame f) (hg : Tame g) :
    ‖(∫ z, f z ∂hatMu0) - ∫ z, g z ∂hatMu0‖ ≤ ∫ z, ‖(f - g) z‖ ∂hatMu0 := by
  rw [← integral_sub hf.integrable hg.integrable]
  exact norm_integral_le_integral_norm _

theorem norm_integral_le_one {h : NatExtTorus → ℂ} (hb : ∀ z, ‖h z‖ ≤ 1) :
    ‖∫ z, h z ∂hatMu0‖ ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := hatMu0) (C := 1)
    (Eventually.of_forall hb)
  simpa using this

/-- The `m`-step indicator correlation as an integral, complex form. -/
theorem corr_indicator_eq {A B : Set NatExtTorus} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (m : ℕ) :
    ((hatMu0.real (A ∩ hatS^[m] ⁻¹' B) : ℝ) : ℂ)
      = ∫ z, indC A z * indC B (hatS^[m] z) ∂hatMu0 := by
  have hmeas : MeasurableSet (A ∩ hatS^[m] ⁻¹' B) :=
    hA.inter ((hatS_measurePreserving.measurable.iterate m) hB)
  rw [← integral_indC hatMu0 hmeas]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases h1 : z ∈ A <;> by_cases h2 : hatS^[m] z ∈ B <;>
    simp [indC, Set.indicator_apply, h1, h2, Set.mem_inter_iff, Set.mem_preimage]

end Assembly62

/-- **Lemma 6.2** (Gauss-torus mixing), v5 lines 1112-1114.  The system
`(Ω̂ × T², μ̂₀, S)` is mixing.

**Reading.**  Mathlib has no `IsMixing` predicate, so mixing is written
out: correlations of indicators of measurable sets converge to the
product of the masses.

**Proof.**  The §6 combinatorics are `torusChar_hatS_iterate` and
`resonance_bounded` above; the measure theory is `hatS_measurePreserving`,
`natExt_zero_mode_mixing`, and the density of the monomial span
(`CylinderCharDense.monoSet_span_dense`).  The assembly is the section
`Assembly62`: `monoInd_corrTo` settles a single pair of monomials by the
Fubini/resonance computation, `span_corrTo` extends bilinearly over the
span, and here the indicators of `A` and `B` are traded for span members
at an `L²` (hence `L¹`) cost that is uniform in `m` because `hatS`
preserves `μ̂₀`. -/
theorem lemma_6_2_gauss_torus_mixing (A B : Set NatExtTorus)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun m : ℕ => hatMu0.real (A ∩ hatS^[m] ⁻¹' B)) atTop
      (𝓝 (hatMu0.real A * hatMu0.real B)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := min ε 1 / 8 with hηdef
  have hη0 : 0 < η := div_pos (lt_min hε one_pos) (by norm_num)
  have hη1 : η ≤ 1 / 8 := by
    rw [hηdef]
    have := min_le_right ε 1
    linarith
  have hη8 : 8 * η ≤ ε := by
    rw [hηdef]
    have := min_le_left ε 1
    linarith
  have htIA : Tame (CylinderCharDense.indC A) :=
    ⟨CylinderCharDense.measurable_indC hA, 1, norm_indC_le A⟩
  have htIB : Tame (CylinderCharDense.indC B) :=
    ⟨CylinderCharDense.measurable_indC hB, 1, norm_indC_le B⟩
  have hMemA : MemLp (CylinderCharDense.indC A) 2 hatMu0 :=
    memLp_indicator_const 2 hA (1 : ℂ) (Or.inr (measure_ne_top _ _))
  have hMemB : MemLp (CylinderCharDense.indC B) 2 hatMu0 :=
    memLp_indicator_const 2 hB (1 : ℂ) (Or.inr (measure_ne_top _ _))
  obtain ⟨f', hf'span, hf'close⟩ := CylinderCharDense.monoSet_span_dense hMemA hη0
  have htf : Tame f' := tame_of_mem_span hf'span
  obtain ⟨C₀, hC₀⟩ := htf.bdd
  set Cf : ℝ := max C₀ 1 with hCfdef
  have hCf1 : (1 : ℝ) ≤ Cf := le_max_right _ _
  have hCf0 : (0 : ℝ) < Cf := lt_of_lt_of_le one_pos hCf1
  have hCfb : ∀ z, ‖f' z‖ ≤ Cf := fun z => (hC₀ z).trans (le_max_left _ _)
  have hη20 : 0 < η / Cf := div_pos hη0 hCf0
  obtain ⟨g', hg'span, hg'close⟩ := CylinderCharDense.monoSet_span_dense hMemB hη20
  have htg : Tame g' := tame_of_mem_span hg'span
  have hL1A : ∫ z, ‖(CylinderCharDense.indC A - f') z‖ ∂hatMu0 ≤ η :=
    integral_norm_le_of_L2 (htIA.meas.sub htf.meas) hη0 hf'close
  have hL1B : ∫ z, ‖(CylinderCharDense.indC B - g') z‖ ∂hatMu0 ≤ η / Cf :=
    integral_norm_le_of_L2 (htIB.meas.sub htg.meas) hη20 hg'close
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (span_corrTo hf'span hg'span) η hη0
  refine ⟨N, fun m hm => ?_⟩
  have hT3 : ‖(∫ z, f' z * g' (hatS^[m] z) ∂hatMu0)
      - (∫ z, f' z ∂hatMu0) * ∫ z, g' z ∂hatMu0‖ < η := by
    have := hN m hm
    rwa [dist_eq_norm] at this
  have hT1 : ‖(∫ z, CylinderCharDense.indC A z * CylinderCharDense.indC B (hatS^[m] z) ∂hatMu0)
      - ∫ z, f' z * CylinderCharDense.indC B (hatS^[m] z) ∂hatMu0‖ ≤ η :=
    (corr_replace_left htIA htf htIB (norm_indC_le B) m).trans hL1A
  have hT2 : ‖(∫ z, f' z * CylinderCharDense.indC B (hatS^[m] z) ∂hatMu0)
      - ∫ z, f' z * g' (hatS^[m] z) ∂hatMu0‖ ≤ η := by
    refine (corr_replace_right htf hCfb htIB htg m).trans ?_
    calc Cf * ∫ z, ‖(CylinderCharDense.indC B - g') z‖ ∂hatMu0
        ≤ Cf * (η / Cf) := mul_le_mul_of_nonneg_left hL1B hCf0.le
      _ = η := by field_simp
  have hmA : ‖(∫ z, CylinderCharDense.indC A z ∂hatMu0) - ∫ z, f' z ∂hatMu0‖ ≤ η :=
    (norm_integral_sub_le htIA htf).trans hL1A
  have hmB : ‖(∫ z, CylinderCharDense.indC B z ∂hatMu0) - ∫ z, g' z ∂hatMu0‖ ≤ η := by
    refine (norm_integral_sub_le htIB htg).trans (hL1B.trans ?_)
    calc η / Cf ≤ η / 1 := by
          apply div_le_div_of_nonneg_left hη0.le one_pos hCf1
      _ = η := div_one η
  have hbA : ‖∫ z, CylinderCharDense.indC A z ∂hatMu0‖ ≤ 1 :=
    norm_integral_le_one (norm_indC_le A)
  have hbB : ‖∫ z, CylinderCharDense.indC B z ∂hatMu0‖ ≤ 1 :=
    norm_integral_le_one (norm_indC_le B)
  have hbg : ‖∫ z, g' z ∂hatMu0‖ ≤ 1 + η := by
    calc ‖∫ z, g' z ∂hatMu0‖
        = ‖(∫ z, CylinderCharDense.indC B z ∂hatMu0)
            - ((∫ z, CylinderCharDense.indC B z ∂hatMu0) - ∫ z, g' z ∂hatMu0)‖ := by
          congr 1
          ring
      _ ≤ ‖∫ z, CylinderCharDense.indC B z ∂hatMu0‖
            + ‖(∫ z, CylinderCharDense.indC B z ∂hatMu0) - ∫ z, g' z ∂hatMu0‖ :=
          norm_sub_le _ _
      _ ≤ 1 + η := add_le_add hbB hmB
  have hT4 : ‖((∫ z, f' z ∂hatMu0) * ∫ z, g' z ∂hatMu0)
      - (∫ z, CylinderCharDense.indC A z ∂hatMu0)
          * ∫ z, CylinderCharDense.indC B z ∂hatMu0‖ ≤ η * (1 + η) + η := by
    rw [show ((∫ z, f' z ∂hatMu0) * ∫ z, g' z ∂hatMu0)
        - (∫ z, CylinderCharDense.indC A z ∂hatMu0)
            * ∫ z, CylinderCharDense.indC B z ∂hatMu0
      = ((∫ z, f' z ∂hatMu0) - ∫ z, CylinderCharDense.indC A z ∂hatMu0)
            * (∫ z, g' z ∂hatMu0)
        + (∫ z, CylinderCharDense.indC A z ∂hatMu0)
            * ((∫ z, g' z ∂hatMu0) - ∫ z, CylinderCharDense.indC B z ∂hatMu0) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hpart1 : ‖(∫ z, f' z ∂hatMu0) - ∫ z, CylinderCharDense.indC A z ∂hatMu0‖
        * ‖∫ z, g' z ∂hatMu0‖ ≤ η * (1 + η) := by
      refine mul_le_mul ?_ hbg (norm_nonneg _) hη0.le
      rw [norm_sub_rev]
      exact hmA
    have hpart2 : ‖∫ z, CylinderCharDense.indC A z ∂hatMu0‖
        * ‖(∫ z, g' z ∂hatMu0) - ∫ z, CylinderCharDense.indC B z ∂hatMu0‖ ≤ η := by
      calc ‖∫ z, CylinderCharDense.indC A z ∂hatMu0‖
          * ‖(∫ z, g' z ∂hatMu0) - ∫ z, CylinderCharDense.indC B z ∂hatMu0‖
          ≤ 1 * η := by
            refine mul_le_mul hbA ?_ (norm_nonneg _) zero_le_one
            rw [norm_sub_rev]
            exact hmB
        _ = η := one_mul η
    linarith
  -- assemble the chain in `ℂ` and read it back in `ℝ`
  have hchain : ∀ a b c d e : ℂ, ‖a - e‖ ≤ ‖a - b‖ + ‖b - c‖ + ‖c - d‖ + ‖d - e‖ := by
    intro a b c d e
    have h1 : a - e = (a - b) + (b - c) + (c - d) + (d - e) := by ring
    calc ‖a - e‖ = ‖(a - b) + (b - c) + (c - d) + (d - e)‖ := by rw [← h1]
      _ ≤ ‖(a - b) + (b - c) + (c - d)‖ + ‖d - e‖ := norm_add_le _ _
      _ ≤ ‖a - b‖ + ‖b - c‖ + ‖c - d‖ + ‖d - e‖ := by
          have h2 := norm_add_le ((a - b) + (b - c)) (c - d)
          have h3 := norm_add_le (a - b) (b - c)
          linarith
  have hkey : ‖((hatMu0.real (A ∩ hatS^[m] ⁻¹' B) : ℝ) : ℂ)
      - ((hatMu0.real A * hatMu0.real B : ℝ) : ℂ)‖ < ε := by
    have hIA : ((hatMu0.real A : ℝ) : ℂ) = ∫ z, CylinderCharDense.indC A z ∂hatMu0 :=
      (integral_indC hatMu0 hA).symm
    have hIB : ((hatMu0.real B : ℝ) : ℂ) = ∫ z, CylinderCharDense.indC B z ∂hatMu0 :=
      (integral_indC hatMu0 hB).symm
    rw [corr_indicator_eq hA hB m, Complex.ofReal_mul, hIA, hIB]
    have hηsq : η * η ≤ η := by nlinarith
    calc ‖(∫ z, CylinderCharDense.indC A z * CylinderCharDense.indC B (hatS^[m] z) ∂hatMu0)
        - (∫ z, CylinderCharDense.indC A z ∂hatMu0)
            * ∫ z, CylinderCharDense.indC B z ∂hatMu0‖
        ≤ ‖(∫ z, CylinderCharDense.indC A z * CylinderCharDense.indC B (hatS^[m] z) ∂hatMu0)
              - ∫ z, f' z * CylinderCharDense.indC B (hatS^[m] z) ∂hatMu0‖
          + ‖(∫ z, f' z * CylinderCharDense.indC B (hatS^[m] z) ∂hatMu0)
              - ∫ z, f' z * g' (hatS^[m] z) ∂hatMu0‖
          + ‖(∫ z, f' z * g' (hatS^[m] z) ∂hatMu0)
              - (∫ z, f' z ∂hatMu0) * ∫ z, g' z ∂hatMu0‖
          + ‖((∫ z, f' z ∂hatMu0) * ∫ z, g' z ∂hatMu0)
              - (∫ z, CylinderCharDense.indC A z ∂hatMu0)
                  * ∫ z, CylinderCharDense.indC B z ∂hatMu0‖ := hchain _ _ _ _ _
      _ < ε := by
          have h4 : ‖((∫ z, f' z ∂hatMu0) * ∫ z, g' z ∂hatMu0)
              - (∫ z, CylinderCharDense.indC A z ∂hatMu0)
                  * ∫ z, CylinderCharDense.indC B z ∂hatMu0‖ ≤ 2 * η + η * η := by
            refine hT4.trans (le_of_eq ?_)
            ring
          linarith
  rw [Real.dist_eq, ← Real.norm_eq_abs,
    show hatMu0.real (A ∩ hatS^[m] ⁻¹' B) - hatMu0.real A * hatMu0.real B
      = hatMu0.real (A ∩ hatS^[m] ⁻¹' B) - (hatMu0.real A * hatMu0.real B) from rfl]
  calc ‖hatMu0.real (A ∩ hatS^[m] ⁻¹' B) - hatMu0.real A * hatMu0.real B‖
      = ‖((hatMu0.real (A ∩ hatS^[m] ⁻¹' B) : ℝ) : ℂ)
          - ((hatMu0.real A * hatMu0.real B : ℝ) : ℂ)‖ := by
        rw [← Complex.ofReal_sub, Complex.norm_real]
    _ < ε := hkey

end

end Lemma62

end Kwon1002
