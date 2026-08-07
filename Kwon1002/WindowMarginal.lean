import Kwon1002.WindowLaws
import Kwon1002.Lemma62

/-!
# The marginal description of the stationary window law `μ_R`

`Kwon1002.windowLaw R` is `hatMu0` pushed forward along
`stationaryWindow R` (v5 lines 1161-1165).  Nothing in the *type*
`WindowSpace R` ties the digit block `a_t` to the real block `x_t`: at an
arbitrary `w : WindowSpace R` the two are unrelated.  What ties them is
the law.  This file supplies the missing description.

## The content

On the image of `stationaryWindow R` the real coordinates are the Gauss
orbit of the future coordinate,

`x_{t+1} = T x_t`  and  `a_t = ⌊1/x_t⌋`,   hence   `1/x_t = a_t + x_{t+1}`,

which is exactly the recursion `Prop64.cfFinite` unwinds.  That is
`OrbitConsistent`, and `ae_orbitConsistent` says `μ_R`-almost every window
satisfies it.

The forward half of the orbit (`t ≥ 0`) needs no hypothesis at all: the
first coordinate of `hatS^[m]` is `gaussIter`.  The backward half does.
`hatSzpow` at a negative exponent iterates `hatSinv`, and
`natExtInv p = ((a_1(y) + x)⁻¹, T y)` returns the *previous* real
coordinate only when the current one already lies in `[0,1)`; otherwise
`gaussMap ((natExtInv p).1) = {a_1(y) + x} ≠ x`.  The invariant region on
which that holds is `natExtGood`, both coordinates irrational in `(0,1)`,
and `natExtMap_mem_good` / `natExtInv_mem_good` show it is preserved in
both time directions.  `hatMu0_ae_natExtGood` shows it carries full
`μ̂₀`-measure: `μ̂₀` is absolutely continuous with respect to Lebesgue on
the box, which pins the two coordinates in `(0,1)`, and the rationals are
Lebesgue-null.

## What this unblocks, and what it does not

`Prop64.digit_truncation` and `Prop64.event_truncation` both name this
statement as their missing structural input; their docstrings are updated
to point here.

It is *not* by itself the digit-block marginal.  Orbit consistency ties
the digits of one window to each other; identifying the law of the digit
at offset `t` with the Gauss digit law needs the stationarity of `μ̂₀`
under `hatS` (`Lemma62.hatS_measurePreserving`), which is still open.  See
the note on `Prop64.event_truncation`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace Kwon1002

noncomputable section

/-! ## The invariant region of the two-sided Gauss system -/

/-- The region on which the two-sided Gauss recursion is exact in both
time directions: both coordinates irrational and in `(0,1)`.  It carries
full `μ̂₀`-measure (`hatMu0_ae_natExtGood`) and is invariant under
`natExtMap` and `natExtInv`. -/
def natExtGood : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1 ∧ Irrational p.1 ∧ Irrational p.2}

/-- The defining split `1/x = a_1(x) + Tx` at a single point of `(0,1)`.
Unlike `inv_gaussIter_eq` this needs no irrationality: `x ∈ (0,1)` already
forces `⌊1/x⌋ ≥ 1 ≥ 0`, which is all the `Int.toNat` in `digit` needs. -/
theorem inv_eq_digit_add_gaussMap {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    x⁻¹ = (digit x 0 : ℝ) + gaussMap x := by
  have h1 : (1:ℝ) < x⁻¹ := by
    rw [lt_inv_comm₀ one_pos hx.1]; simpa using hx.2
  have hfl : (0:ℤ) ≤ ⌊x⁻¹⌋ := Int.floor_nonneg.mpr (by linarith)
  have hcast : ((⌊x⁻¹⌋.toNat : ℕ) : ℝ) = ((⌊x⁻¹⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hfl
  have hd : digit x 0 = ⌊x⁻¹⌋.toNat := by simp [digit, gaussIter]
  rw [hd, hcast]
  unfold gaussMap Int.fract
  ring

/-- `1/(a + u) ∈ (0,1)` for `a ≥ 1` a digit and `u ∈ (0,1)`; the step that
keeps both natural-extension maps inside the unit square. -/
theorem inv_natCast_add_mem_Ioo {a : ℕ} {u : ℝ} (ha : 1 ≤ a) (hu : 0 < u) :
    ((a : ℝ) + u)⁻¹ ∈ Ioo (0:ℝ) 1 := by
  have ha' : (1:ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hsum : (1:ℝ) < (a : ℝ) + u := by linarith
  exact ⟨inv_pos.mpr (by linarith), by
    rw [inv_lt_one_iff₀]; right; exact hsum⟩

/-- `natExtGood` is forward invariant. -/
theorem natExtMap_mem_good {p : ℝ × ℝ} (hp : p ∈ natExtGood) : natExtMap p ∈ natExtGood := by
  obtain ⟨h1, h2, hi1, hi2⟩ := hp
  refine ⟨gaussMap_mem_Ioo hi1, ?_, gaussMap_irrational hi1, (hi2.natCast_add _).inv⟩
  exact inv_natCast_add_mem_Ioo (one_le_digit h1 hi1 0) h2.1

/-- `natExtGood` is backward invariant. -/
theorem natExtInv_mem_good {p : ℝ × ℝ} (hp : p ∈ natExtGood) : natExtInv p ∈ natExtGood := by
  obtain ⟨h1, h2, hi1, hi2⟩ := hp
  refine ⟨?_, gaussMap_mem_Ioo hi2, (hi1.natCast_add _).inv, gaussMap_irrational hi2⟩
  exact inv_natCast_add_mem_Ioo (one_le_digit h2 hi2 0) h1.1

/-- Forward invariance along the whole orbit. -/
theorem natExtMap_iterate_mem_good {p : ℝ × ℝ} (hp : p ∈ natExtGood) (m : ℕ) :
    natExtMap^[m] p ∈ natExtGood := by
  induction m with
  | zero => simpa using hp
  | succ m ih => rw [Function.iterate_succ_apply']; exact natExtMap_mem_good ih

/-- Backward invariance along the whole orbit. -/
theorem natExtInv_iterate_mem_good {p : ℝ × ℝ} (hp : p ∈ natExtGood) (m : ℕ) :
    natExtInv^[m] p ∈ natExtGood := by
  induction m with
  | zero => simpa using hp
  | succ m ih => rw [Function.iterate_succ_apply']; exact natExtInv_mem_good ih

/-- At a nonnegative exponent the Gauss block of `S^t` is a forward
iterate of `natExtMap`. -/
theorem hatSzpow_fst_of_nonneg {t : ℤ} (ht : 0 ≤ t) (z : NatExtTorus) :
    (hatSzpow t z).1 = natExtMap^[t.toNat] z.1 := by
  rw [hatSzpow, if_pos ht]
  exact Lemma62.hatS_iterate_fst _ _

/-- At a nonpositive exponent the Gauss block of `S^t` is a backward
iterate of `natExtInv`.  The exponent `0` is in both statements, and they
agree there. -/
theorem hatSzpow_fst_of_nonpos {t : ℤ} (ht : t ≤ 0) (z : NatExtTorus) :
    (hatSzpow t z).1 = natExtInv^[(-t).toNat] z.1 := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h; simp [hatSzpow]
  · rw [hatSzpow, if_neg (by omega)]
    exact Lemma62.hatSinv_iterate_fst _ _

/-- Every point of the two-sided orbit of a good point is good. -/
theorem hatSzpow_fst_mem_good {z : NatExtTorus} (hz : z.1 ∈ natExtGood) (t : ℤ) :
    (hatSzpow t z).1 ∈ natExtGood := by
  rcases le_or_gt 0 t with h | h
  · rw [hatSzpow_fst_of_nonneg h]; exact natExtMap_iterate_mem_good hz _
  · rw [hatSzpow_fst_of_nonpos h.le]; exact natExtInv_iterate_mem_good hz _

/-- **The backward step.**  `T((a_1(y) + x)⁻¹) = {a_1(y) + x} = x` when
`x ∈ [0,1)`.  This is the identity that fails off `natExtGood`, and it is
the only place the invariant region is used. -/
theorem gaussMap_natExtInv_fst {q : ℝ × ℝ} (hq : q.1 ∈ Ico (0:ℝ) 1) :
    gaussMap (natExtInv q).1 = q.1 := by
  simp only [natExtInv, gaussMap, inv_inv]
  rw [Int.fract_natCast_add]
  exact Int.fract_eq_self.mpr ⟨hq.1, hq.2⟩

/-! ### The two natural-extension maps are mutually inverse on the good region

`natExtMap` and `natExtInv` are **not** pointwise inverse on all of `ℝ²`:
`gaussMap ((natExtInv p).1) = Int.fract (a₁(y) + x)`, which is `x` only
when `x` already lies in `[0,1)`.  On `natExtGood`, which carries full
`ν̂`- and `μ̂₀`-measure, they are.  This is what `hatSzpow` needs at negative
exponents, and it is the pointwise content behind
`Lemma62.natExtInv_measurePreserving`. -/

theorem floor_natCast_add_of_mem_Ico {a : ℕ} {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    ⌊(a : ℝ) + x⌋ = (a : ℤ) := by
  rw [Int.floor_eq_iff]
  constructor
  · push_cast
    linarith [hx.1]
  · push_cast
    linarith [hx.2]

/-- The digit of `1/(a + x)` is `a`, for `x ∈ [0,1)`. -/
theorem digit_inv_natCast_add {a : ℕ} {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    digit (((a : ℝ) + x)⁻¹) 0 = a := by
  simp only [digit, gaussIter_zero, inv_inv]
  rw [floor_natCast_add_of_mem_Ico hx]
  exact Int.toNat_natCast a

/-- The Gauss map of `1/(a + x)` is `x`, for `x ∈ [0,1)`. -/
theorem gaussMap_inv_natCast_add {a : ℕ} {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    gaussMap (((a : ℝ) + x)⁻¹) = x := by
  simp only [gaussMap, inv_inv]
  rw [Int.fract_natCast_add]
  exact Int.fract_eq_self.mpr ⟨hx.1, hx.2⟩

/-- `σ⁻¹ ∘ σ = id` wherever the future coordinate is in `(0,1)` and the
past coordinate in `[0,1)`. -/
theorem natExtInv_natExtMap {p : ℝ × ℝ} (h1 : p.1 ∈ Ioo (0 : ℝ) 1)
    (h2 : p.2 ∈ Ico (0 : ℝ) 1) : natExtInv (natExtMap p) = p := by
  obtain ⟨x, y⟩ := p
  simp only [natExtMap, natExtInv] at *
  rw [digit_inv_natCast_add h2, gaussMap_inv_natCast_add h2,
    ← inv_eq_digit_add_gaussMap h1, inv_inv]

/-- `σ ∘ σ⁻¹ = id` wherever the future coordinate is in `[0,1)` and the
past coordinate in `(0,1)`. -/
theorem natExtMap_natExtInv {p : ℝ × ℝ} (h1 : p.1 ∈ Ico (0 : ℝ) 1)
    (h2 : p.2 ∈ Ioo (0 : ℝ) 1) : natExtMap (natExtInv p) = p := by
  obtain ⟨x, y⟩ := p
  simp only [natExtMap, natExtInv] at *
  rw [gaussMap_inv_natCast_add h1, digit_inv_natCast_add h1,
    ← inv_eq_digit_add_gaussMap h2, inv_inv]

theorem natExtInv_natExtMap_of_good {p : ℝ × ℝ} (hp : p ∈ natExtGood) :
    natExtInv (natExtMap p) = p :=
  natExtInv_natExtMap hp.1 (Ioo_subset_Ico_self hp.2.1)

theorem natExtMap_natExtInv_of_good {p : ℝ × ℝ} (hp : p ∈ natExtGood) :
    natExtMap (natExtInv p) = p :=
  natExtMap_natExtInv (Ioo_subset_Ico_self hp.1) hp.2.1

/-- **The good region carries full `ν̂`-measure.**  `ν̂` is a `withDensity`
of Lebesgue restricted to the square, hence absolutely continuous with
respect to it; the square supplies `(0,1)` in both coordinates and the
rationals are Lebesgue-null.  The `μ̂₀` counterpart is
`hatMu0_ae_natExtGood` below. -/
theorem hatNu_ae_natExtGood : ∀ᵐ p ∂hatNu, p ∈ natExtGood := by
  have hQ : volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
    (Set.countable_range _).measure_zero volume
  have h1 : ∀ᵐ p : ℝ × ℝ ∂volume, Irrational p.1 := by
    have hsub : {p : ℝ × ℝ | ¬ Irrational p.1}
        = (Set.range ((↑) : ℚ → ℝ) ×ˢ (Set.univ : Set ℝ)) := by
      ext p; simp [Irrational]
    rw [ae_iff, hsub]
    simp [Measure.volume_eq_prod, Measure.prod_prod, hQ]
  have h2 : ∀ᵐ p : ℝ × ℝ ∂volume, Irrational p.2 := by
    have hsub : {p : ℝ × ℝ | ¬ Irrational p.2}
        = ((Set.univ : Set ℝ) ×ˢ Set.range ((↑) : ℚ → ℝ)) := by
      ext p; simp [Irrational]
    rw [ae_iff, hsub]
    simp [Measure.volume_eq_prod, Measure.prod_prod, hQ]
  have hac : hatNu ≪ volume.restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) := by
    rw [hatNu]; exact withDensity_absolutelyContinuous _ _
  have key : ∀ᵐ p ∂(volume.restrict (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)), p ∈ natExtGood := by
    rw [ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)]
    filter_upwards [h1, h2] with p hp1 hp2 hpB
    exact ⟨hpB.1, hpB.2, hp1, hp2⟩
  exact hac.ae_le key

/-- **C5, the a.e. inverse identity.**  `σ ∘ σ⁻¹ = id` `ν̂`-almost
everywhere.  It is *not* a pointwise identity in this representation, and
saying so is the point: off `natExtGood` the composite returns
`Int.fract (a₁(y) + x)` in the first coordinate instead of `x`. -/
theorem natExtMap_natExtInv_ae : ∀ᵐ p ∂hatNu, natExtMap (natExtInv p) = p := by
  filter_upwards [hatNu_ae_natExtGood] with p hp
  exact natExtMap_natExtInv_of_good hp

/-- **C5, the a.e. inverse identity, other direction.** -/
theorem natExtInv_natExtMap_ae : ∀ᵐ p ∂hatNu, natExtInv (natExtMap p) = p := by
  filter_upwards [hatNu_ae_natExtGood] with p hp
  exact natExtInv_natExtMap_of_good hp

/-- **The orbit recursion.**  Along the stationary orbit of a good point
the real coordinate advances by the Gauss map, at every integer time,
forward and backward. -/
theorem hatSzpow_fst_fst_succ {z : NatExtTorus} (hz : z.1 ∈ natExtGood) (t : ℤ) :
    (hatSzpow (t + 1) z).1.1 = gaussMap ((hatSzpow t z).1.1) := by
  rcases le_or_gt 0 t with h | h
  · rw [hatSzpow_fst_of_nonneg (by omega : (0:ℤ) ≤ t + 1), hatSzpow_fst_of_nonneg h]
    have hn : (t + 1).toNat = t.toNat + 1 := by omega
    rw [hn, Function.iterate_succ_apply']
    rfl
  · have ht1 : t + 1 ≤ 0 := by omega
    rw [hatSzpow_fst_of_nonpos ht1, hatSzpow_fst_of_nonpos h.le]
    have hn : (-t).toNat = (-(t + 1)).toNat + 1 := by omega
    rw [hn, Function.iterate_succ_apply']
    have hq := natExtInv_iterate_mem_good hz (-(t + 1)).toNat
    exact (gaussMap_natExtInv_fst (Ioo_subset_Ico_self hq.1)).symm

/-! ## readers -/

/-- The real coordinate at offset `t` of a stationary window is the Gauss
coordinate of `S^t z`. -/
theorem wX_stationaryWindow (R : ℕ) (z : NatExtTorus) {t : ℤ}
    (h1 : -(R:ℤ) ≤ t) (h2 : t ≤ (R:ℤ)) :
    wX (stationaryWindow R z) t = (hatSzpow t z).1.1 := by
  have hc : 0 ≤ t + (R:ℤ) ∧ t + (R:ℤ) < 2 * (R:ℤ) + 1 := ⟨by omega, by omega⟩
  simp only [wX, dif_pos hc, stationaryWindow]
  have hidx : (((t + (R:ℤ)).toNat : ℕ) : ℤ) - (R:ℤ) = t := by omega
  rw [hidx]

/-- The digit at offset `t` of a stationary window is the leading Gauss
digit of the real coordinate at offset `t`; true for every `z`, with no
hypothesis, since `stationaryWindow` builds it that way. -/
theorem wA_stationaryWindow (R : ℕ) (z : NatExtTorus) {t : ℤ}
    (h1 : -(R:ℤ) ≤ t) (h2 : t ≤ (R:ℤ)) :
    wA (stationaryWindow R z) t = digit ((hatSzpow t z).1.1) 0 := by
  have hc : 0 ≤ t + (R:ℤ) ∧ t + (R:ℤ) < 2 * (R:ℤ) + 1 := ⟨by omega, by omega⟩
  simp only [wA, dif_pos hc, stationaryWindow]
  have hidx : (((t + (R:ℤ)).toNat : ℕ) : ℤ) - (R:ℤ) = t := by omega
  rw [hidx]

/-- The torus coordinate at offset `t` of a stationary window. -/
theorem wTh_stationaryWindow (R : ℕ) (z : NatExtTorus) {t : ℤ}
    (h1 : -(R:ℤ) - 1 ≤ t) (h2 : t ≤ (R:ℤ)) :
    wTh (stationaryWindow R z) t = (hatSzpow t z).2.2 := by
  have hc : 0 ≤ t + (R:ℤ) + 1 ∧ t + (R:ℤ) + 1 < 2 * (R:ℤ) + 2 := ⟨by omega, by omega⟩
  simp only [wTh, dif_pos hc, stationaryWindow]
  have hidx : (((t + (R:ℤ) + 1).toNat : ℕ) : ℤ) - (R:ℤ) - 1 = t := by omega
  rw [hidx]

/-! ## orbit consistency -/

/-- **Orbit consistency**, the marginal description of `μ_R`.  A window
is orbit-consistent when its real coordinates are an irrational Gauss
orbit in `(0,1)` and its digits are the digits of that orbit.  This is
precisely what `stationaryWindow` produces and what an arbitrary point of
`WindowSpace R` does not satisfy. -/
def OrbitConsistent (R : ℕ) (w : WindowSpace R) : Prop :=
  (∀ t : ℤ, -(R:ℤ) ≤ t → t ≤ (R:ℤ) →
      wX w t ∈ Ioo (0:ℝ) 1 ∧ Irrational (wX w t) ∧ wA w t = digit (wX w t) 0) ∧
  (∀ t : ℤ, -(R:ℤ) ≤ t → t + 1 ≤ (R:ℤ) → wX w (t + 1) = gaussMap (wX w t))

/-- **Every stationary window over a good point is orbit-consistent.** -/
theorem stationaryWindow_orbitConsistent (R : ℕ) {z : NatExtTorus} (hz : z.1 ∈ natExtGood) :
    OrbitConsistent R (stationaryWindow R z) := by
  constructor
  · intro t h1 h2
    rw [wX_stationaryWindow R z h1 h2, wA_stationaryWindow R z h1 h2]
    obtain ⟨hI, -, hi, -⟩ := hatSzpow_fst_mem_good hz t
    exact ⟨hI, hi, rfl⟩
  · intro t h1 h2
    rw [wX_stationaryWindow R z (by omega) h2, wX_stationaryWindow R z h1 (by omega)]
    exact hatSzpow_fst_fst_succ hz t

/-- **The split the truncation argument consumes**, `1/x_t = a_t + x_{t+1}`
for `-R ≤ t < R`.  Unwinding it `M` times is exactly `Prop64.cfFinite`. -/
theorem OrbitConsistent.inv_wX {R : ℕ} {w : WindowSpace R} (h : OrbitConsistent R w)
    {t : ℤ} (h1 : -(R:ℤ) ≤ t) (h2 : t + 1 ≤ (R:ℤ)) :
    (wX w t)⁻¹ = (wA w t : ℝ) + wX w (t + 1) := by
  obtain ⟨hA, hG⟩ := h
  obtain ⟨hI, -, hd⟩ := hA t h1 (by omega)
  rw [hd, hG t h1 h2]
  exact inv_eq_digit_add_gaussMap hI

/-- The irrationals are a measurable subset of `ℝ`: the complement of the
countable range of `ℚ → ℝ`. -/
theorem measurableSet_irrational : MeasurableSet {x : ℝ | Irrational x} :=
  (Set.countable_range ((↑) : ℚ → ℝ)).measurableSet.compl

/-- Orbit consistency is a measurable condition.  Both clauses are
countable (indeed finite) intersections over `t : ℤ` of preimages under
the window coordinate readers. -/
theorem measurableSet_orbitConsistent (R : ℕ) :
    MeasurableSet {w : WindowSpace R | OrbitConsistent R w} := by
  have hset : {w : WindowSpace R | OrbitConsistent R w}
      = (⋂ t : ℤ, {w : WindowSpace R | -(R:ℤ) ≤ t → t ≤ (R:ℤ) →
            wX w t ∈ Ioo (0:ℝ) 1 ∧ Irrational (wX w t) ∧ wA w t = digit (wX w t) 0})
        ∩ (⋂ t : ℤ, {w : WindowSpace R | -(R:ℤ) ≤ t → t + 1 ≤ (R:ℤ) →
            wX w (t + 1) = gaussMap (wX w t)}) := by
    ext w
    simp only [OrbitConsistent, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.iInter fun t => ?_) (MeasurableSet.iInter fun t => ?_)
  · by_cases hc : -(R:ℤ) ≤ t ∧ t ≤ (R:ℤ)
    · have hrw : {w : WindowSpace R | -(R:ℤ) ≤ t → t ≤ (R:ℤ) →
            wX w t ∈ Ioo (0:ℝ) 1 ∧ Irrational (wX w t) ∧ wA w t = digit (wX w t) 0}
          = {w : WindowSpace R | wX w t ∈ Ioo (0:ℝ) 1} ∩
            ({w : WindowSpace R | Irrational (wX w t)} ∩
              {w : WindowSpace R | wA w t = digit (wX w t) 0}) := by
        ext w; simp [hc.1, hc.2, and_assoc]
      rw [hrw]
      refine MeasurableSet.inter ((measurable_wX R t) measurableSet_Ioo)
        (MeasurableSet.inter ((measurable_wX R t) measurableSet_irrational) ?_)
      exact measurableSet_eq_fun (measurable_wA R t)
        ((Prop42.measurable_digitNat 0).comp (measurable_wX R t))
    · have hrw : {w : WindowSpace R | -(R:ℤ) ≤ t → t ≤ (R:ℤ) →
            wX w t ∈ Ioo (0:ℝ) 1 ∧ Irrational (wX w t) ∧ wA w t = digit (wX w t) 0}
          = Set.univ := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro ha hb; exact absurd ⟨ha, hb⟩ hc
      rw [hrw]; exact MeasurableSet.univ
  · by_cases hc : -(R:ℤ) ≤ t ∧ t + 1 ≤ (R:ℤ)
    · have hrw : {w : WindowSpace R | -(R:ℤ) ≤ t → t + 1 ≤ (R:ℤ) →
            wX w (t + 1) = gaussMap (wX w t)}
          = {w : WindowSpace R | wX w (t + 1) = gaussMap (wX w t)} := by
        ext w; simp [hc.1, hc.2]
      rw [hrw]
      exact measurableSet_eq_fun (measurable_wX R (t + 1))
        (measurable_gaussMap'.comp (measurable_wX R t))
    · have hrw : {w : WindowSpace R | -(R:ℤ) ≤ t → t + 1 ≤ (R:ℤ) →
            wX w (t + 1) = gaussMap (wX w t)} = Set.univ := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro ha hb; exact absurd ⟨ha, hb⟩ hc
      rw [hrw]; exact MeasurableSet.univ

/-- **`μ̂₀` lives on the good region.**  `μ̂₀` is a `withDensity` of
Lebesgue restricted to the box, hence absolutely continuous with respect
to it; the box supplies `(0,1)` and the rationals are Lebesgue-null. -/
theorem hatMu0_ae_natExtGood : ∀ᵐ z ∂hatMu0, z.1 ∈ natExtGood := by
  have hQ : volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
    (Set.countable_range _).measure_zero volume
  have h1 : ∀ᵐ z : (ℝ × ℝ) × ℝ × ℝ ∂volume, Irrational z.1.1 := by
    have hsub : {z : (ℝ × ℝ) × ℝ × ℝ | ¬ Irrational z.1.1}
        = ((Set.range ((↑) : ℚ → ℝ) ×ˢ (Set.univ : Set ℝ)) ×ˢ
            (Set.univ : Set (ℝ × ℝ))) := by
      ext z; simp [Irrational]
    rw [ae_iff, hsub]
    simp [Measure.volume_eq_prod, Measure.prod_prod, hQ]
  have h2 : ∀ᵐ z : (ℝ × ℝ) × ℝ × ℝ ∂volume, Irrational z.1.2 := by
    have hsub : {z : (ℝ × ℝ) × ℝ × ℝ | ¬ Irrational z.1.2}
        = (((Set.univ : Set ℝ) ×ˢ Set.range ((↑) : ℚ → ℝ)) ×ˢ
            (Set.univ : Set (ℝ × ℝ))) := by
      ext z; simp [Irrational]
    rw [ae_iff, hsub]
    simp [Measure.volume_eq_prod, Measure.prod_prod, hQ]
  have hac : hatMu0 ≪ volume.restrict
      (((Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) ×ˢ (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)) :
        Set ((ℝ × ℝ) × ℝ × ℝ)) := by
    rw [hatMu0]; exact withDensity_absolutelyContinuous _ _
  have key : ∀ᵐ z ∂(volume.restrict
      (((Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) ×ˢ (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)) :
        Set ((ℝ × ℝ) × ℝ × ℝ))), z.1 ∈ natExtGood := by
    rw [ae_restrict_iff' Prop42.measurableSet_hatBox]
    filter_upwards [h1, h2] with z hz1 hz2 hzB
    exact ⟨hzB.1.1, hzB.1.2, hz1, hz2⟩
  exact hac.ae_le key

/-- **The marginal description of `μ_R`.**  `μ_R`-almost every window is
orbit-consistent.  This is the single fact behind both
`Prop64.digit_truncation` and `Prop64.event_truncation`; it is false
pointwise on `WindowSpace R`, which is why those two statements are not
pointwise statements. -/
theorem ae_orbitConsistent (R : ℕ) : ∀ᵐ w ∂(windowLaw R), OrbitConsistent R w := by
  rw [windowLaw, ae_map_iff (measurable_stationaryWindow R).aemeasurable
    (measurableSet_orbitConsistent R)]
  filter_upwards [hatMu0_ae_natExtGood] with z hz
  exact stationaryWindow_orbitConsistent R hz


end

end Kwon1002
