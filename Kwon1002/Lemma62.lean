import Kwon1002.Section6Skeleton
import Kwon1002.NatExtMeasure
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

## What is not proved here, and why

`hatS_measurePreserving` and `lemma_6_2_gauss_torus_mixing` are left
sorried.  The obstruction is not §6 combinatorics; it is that the
measure-theoretic substrate they need does not exist anywhere in this
development or in `wang_substrate/`.  Concretely:

* there is no statement, let alone proof, that the Gauss natural
  extension map preserves `ν̂` (density `1/(log 2 (1+xy)²)` on `(0,1)²`);
  `grep MeasurePreserving` over both trees returns only the skeleton line
  itself;
* there is no torus-automorphism input either: that
  `(r,s) ↦ (s, {r - a s})` preserves Haar on `T²` for `a ∈ ℕ` is the
  `GL₂(ℤ)`-invariance quoted at v5 lines 1052-1056, and Mathlib's
  `AddCircle` Haar machinery is not connected to the `Int.fract`-on-`[0,1)`
  representation used throughout this development;
* the two must then be assembled as a skew product over a `withDensity`
  measure, which is a Fubini argument in its own right.

`lemma_6_2_gauss_torus_mixing` needs, on top of `hatS_measurePreserving`,
the `L²(μ̂₀)` density of finite digit-cylinder functions times torus
characters and the mixing of the Gauss natural extension itself (the
"zero modes" of v5 line 1148).  The BV chain in this tree
(`BVMixing.lemma_3_2_BV`, `MixingBV.lem_3_2_conditional_multiblock_mixing'`)
gives quantitative multi-block mixing for the *one-sided* Gauss system
against BV observables; it does not give the two-sided natural extension
as a measure-preserving system, which is what `hatS` is built on, and no
lifting statement exists in the tree.  Those are named below as the four
inputs `natExtMap_measurePreserving`, `torusFibre_measurePreserving`,
`natExt_zero_mode_mixing` and `cylinderChar_dense_L2`; they are exactly
the sorries this file cannot discharge.
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

/-- The Gauss natural extension preserves `ν̂ = hatNu`, the measure with
density `1/(log 2 (1+xy)²)` on `(0,1)²` (`Kwon1002/NatExtMeasure.lean`).

**Obstruction.**  Nothing of the kind exists in `Kwon1002/` or in
`wang_substrate/Erdos1002/`: the BV chain in this tree works with the
transfer operator of the *one-sided* Gauss map and never constructs the
two-sided extension as a measure-preserving system.  What Layer 0 does
supply is that `ν̂` is a probability measure (`hatNu_univ`), so the
statement below is now a statement about two probability measures. -/
theorem natExtMap_measurePreserving :
    MeasurePreserving natExtMap hatNu hatNu := by
  sorry

/-- For each digit `a`, the fibre map `(r,s) ↦ (s, {r - a s})` of (49)
preserves Haar on `T²`, this being the `GL₂(ℤ)`-invariance of v5 lines
1052-1056 (`fibreMatrix_det` above is the determinant half of it).

**Obstruction.**  Haar on `T²` is carried in this development as Lebesgue
restricted to `(0,1)²` with `Int.fract` doing the reduction, and Mathlib's
invariance results live on `AddCircle`; the translation between the two
representations is missing, and there is no `Int.fract`-level change of
variables for an integer unimodular map in the tree. -/
theorem torusFibre_measurePreserving (a : ℕ) :
    MeasurePreserving (fun q : ℝ × ℝ => (q.2, Int.fract (q.1 - (a : ℝ) * q.2)))
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1))
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
  sorry

/-- The cocycle preserves `μ̂₀`.

**Obstruction.**  Two missing inputs, `natExtMap_measurePreserving` and
`torusFibre_measurePreserving`, plus the skew-product assembly: `hatS` is
not a product map, since the fibre matrix depends on the base point
through `digit z.1.1 0`, so the assembly is a Fubini argument over the
`withDensity` base measure and not a `MeasurePreserving.prod`. -/
theorem hatS_measurePreserving : MeasurePreserving hatS hatMu0 hatMu0 := by
  sorry

/-- The zero-mode half of Lemma 6.2 (v5 line 1148): on characters with
`k = ℓ = 0` the correlation is a correlation of the Gauss natural
extension alone, and mixing there is the classical statement.

**Obstruction.**  The BV mixing available here
(`BVMixing.lemma_3_2_BV`, `MixingBV.lem_3_2_conditional_multiblock_mixing'`)
is for the one-sided Gauss map against BV observables on `(0,1)`; lifting
it to the two-sided natural extension requires
`natExtMap_measurePreserving` and the identification of `natExtMap`-invariant
sets with `gaussMap`-invariant sets, neither of which is in the tree. -/
theorem natExt_zero_mode_mixing (A B : Set (ℝ × ℝ))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun m : ℕ => hatNu.real (A ∩ natExtMap^[m] ⁻¹' B))
      atTop (𝓝 (hatNu.real A * hatNu.real B)) := by
  sorry

/-- Finite digit-cylinder functions times torus characters are dense in
`L²(μ̂₀)` (v5 line 1149, "density of cylinder functions times characters
in `L²` completes the proof").

**Obstruction.**  Stated here only as the approximation property that the
proof uses; a proof needs the generated sigma-algebra of the cylinder
partition together with Stone-Weierstrass on `T²`, and neither the
cylinder sigma-algebra of the two-sided extension nor an `L²` density
lemma for it exists in this tree. -/
theorem cylinderChar_dense_L2 (f : NatExtTorus → ℂ) (hf : MemLp f 2 hatMu0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (R K : ℕ) (U : WindowSymbol R K),
      eLpNorm (fun z => f z - U.eval z) 2 hatMu0 < ENNReal.ofReal ε := by
  sorry

/-- **Lemma 6.2** (Gauss-torus mixing), v5 lines 1112-1114.  The system
`(Ω̂ × T², μ̂₀, S)` is mixing.

**Reading.**  Mathlib has no `IsMixing` predicate, so mixing is written
out: correlations of indicators of measurable sets converge to the
product of the masses.

**Obstruction.**  The §6 combinatorics of the proof are complete above:
`torusChar_hatS_iterate` turns an `m`-step correlation of cylinder times
character into a single character with mode
`(A_{a_m} ⋯ A_{a_1})ᵀ k + ℓ`, and `resonance_bounded_along_orbit` says
that mode is nonzero for all large `m`, so the fibre integral vanishes.
What is missing is entirely measure-theoretic: `hatS_measurePreserving`
(to have a dynamical system at all), the vanishing of the `μ̂₀`-integral
of a nonzero torus character (Fubini against Haar on the fibre),
`natExt_zero_mode_mixing` for the zero modes, and `cylinderChar_dense_L2`
to pass from the test class to indicators of arbitrary measurable sets. -/
theorem lemma_6_2_gauss_torus_mixing (A B : Set NatExtTorus)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun m : ℕ => hatMu0.real (A ∩ hatS^[m] ⁻¹' B)) atTop
      (𝓝 (hatMu0.real A * hatMu0.real B)) := by
  sorry

end

end Lemma62

end Kwon1002
