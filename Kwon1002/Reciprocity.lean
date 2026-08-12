import Kwon1002.GaussBasics

/-!
# §2, Reciprocity and the principal term (Kwon, Props 2.1-2.2)

Faithful skeleton of the manuscript's §2, displays (1)-(11), against the
current draft (referee-verified formulas; this section is not under
revision). Statements are sorried; the definitions are the content here
and are fixed by the manuscript:

* the Gauss map `T x = {1/x}` and its iterates `x_j`;
* the height recursion (2): `N_{j+1} = ⌊N_j x_j⌋`, `u_j = {N_j x_j}`;
* `Φ(x,u) = u(1-u)/(2x) - u/2` (Prop 2.1's remainder);
* `β_j = x_0 ⋯ x_j` (4), `θ_j = {n β_j}` (8), `E_j = n β_{j-1} - N_j`
  with `E_0 = 0` (5), `E* = ∑_{ℓ≥1} 1/F_ℓ` (7);
* `W(t) = {t}(1-{t})/2` and `C₀ = E*/2 + 5/8` (the constant the audit
  pinned for (11); the manuscript asserts only that some absolute `C₀`
  works, so the sorried statement uses this concrete one).
-/

open Filter Set

namespace Kwon1002

noncomputable section

/-- The height sequence (2): `N_0 = n`, `N_{j+1} = ⌊N_j x_j⌋`. -/
def heightSeq (α : ℝ) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | j + 1 => ⌊(heightSeq α n j : ℝ) * gaussIter α j⌋.toNat

/-- `u_j = {N_j x_j}` from (2). -/
def carry (α : ℝ) (n : ℕ) (j : ℕ) : ℝ :=
  Int.fract ((heightSeq α n j : ℝ) * gaussIter α j)

/-- `τ_n = min { j | N_j = 0 }` (3). -/
def stoppingTime (α : ℝ) (n : ℕ) : ℕ := sInf {j | heightSeq α n j = 0}

/-- `Φ(x,u) = u(1-u)/(2x) - u/2`, the exact remainder of Prop 2.1. -/
def Phi (x u : ℝ) : ℝ := u * (1 - u) / (2 * x) - u / 2

/-- `β_j = x_0 x_1 ⋯ x_j` (4). -/
def betaProd (α : ℝ) (j : ℕ) : ℝ := ∏ i ∈ Finset.range (j + 1), gaussIter α i

/-- `θ_j = {n β_j}` (8); the convention `θ_{-1} = 0` is handled at use
sites via `thetaPred`. -/
def theta (α : ℝ) (n : ℕ) (j : ℕ) : ℝ := Int.fract ((n : ℝ) * betaProd α j)

/-- `θ_{j-1}` with the `θ_{-1} = 0` convention of (8). -/
def thetaPred (α : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => theta α n j

/-- `E_j = n β_{j-1} - N_j` (heights and their errors), `E_0 = 0`. -/
def heightError (α : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => (n : ℝ) * betaProd α j - (heightSeq α n (j + 1) : ℝ)

/-- `E* = ∑_{ℓ≥1} 1/F_ℓ` (7), the reciprocal-Fibonacci bound. -/
def Estar : ℝ := ∑' ℓ : ℕ, ((Nat.fib (ℓ + 1) : ℝ))⁻¹

/-- `W(t) = {t}(1-{t})/2`, `1/2`-Lipschitz on the torus, `0 ≤ W ≤ 1/8`. -/
def W (t : ℝ) : ℝ := Int.fract t * (1 - Int.fract t) / 2

/-- The audit-pinned constant for (11): `C₀ = E*/2 + 5/8 ≈ 2.305`. -/
def Czero : ℝ := Estar / 2 + 5 / 8

/-! ### Helper lemmas for Proposition 2.1 -/

/-- Gauss sum over `Icc 1 m`, in `ℝ`. -/
lemma sum_Icc_id_real (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, (j : ℝ) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
  induction m with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    push_cast
    ring

/-- Expansion of the sawtooth sum through `{t} = t - ⌊t⌋`. -/
lemma rotationSum_eq_floor_sum (n : ℕ) (y : ℝ) :
    rotationSum n y
      = (n : ℝ) / 2 - y * ((n : ℝ) * ((n : ℝ) + 1)) / 2
        + ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * y⌋ : ℝ) := by
  have hterm : ∀ k ∈ Finset.Icc 1 n,
      sawtooth ((k : ℝ) * y) = ((1 : ℝ) / 2 - (k : ℝ) * y) + (⌊(k : ℝ) * y⌋ : ℝ) := by
    intro k _
    unfold sawtooth Int.fract
    ring
  unfold rotationSum
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, sum_Icc_id_real]
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  ring

/-- The per-`j` digit split: `⌊j/x⌋ = j·⌊1/x⌋ + ⌊j·Tx⌋` (as reals). -/
lemma floor_div_split (x : ℝ) (j : ℕ) :
    (⌊(j : ℝ) / x⌋ : ℝ) = (j : ℝ) * ((⌊x⁻¹⌋ : ℤ) : ℝ) + (⌊(j : ℝ) * gaussMap x⌋ : ℝ) := by
  have key : (j : ℝ) / x = (j : ℝ) * gaussMap x + ((j * ⌊x⁻¹⌋ : ℤ) : ℝ) := by
    unfold gaussMap Int.fract
    push_cast
    ring
  rw [key, Int.floor_add_intCast]
  push_cast
  ring

/-- Summing the digit split over `j = 1, …, m`. -/
lemma sum_floor_div_split (x : ℝ) (m N : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, ((N : ℝ) - (⌊(j : ℝ) / x⌋ : ℝ))
      = (m : ℝ) * (N : ℝ)
        - (((⌊x⁻¹⌋ : ℤ) : ℝ) * ((m : ℝ) * ((m : ℝ) + 1) / 2)
          + ∑ j ∈ Finset.Icc 1 m, (⌊(j : ℝ) * gaussMap x⌋ : ℝ)) := by
  have hdiv : ∀ j ∈ Finset.Icc 1 m, (⌊(j : ℝ) / x⌋ : ℝ)
      = (j : ℝ) * ((⌊x⁻¹⌋ : ℤ) : ℝ) + (⌊(j : ℝ) * gaussMap x⌋ : ℝ) :=
    fun j _ => floor_div_split x j
  rw [Finset.sum_sub_distrib, Finset.sum_congr rfl hdiv, Finset.sum_add_distrib,
    ← Finset.sum_mul, sum_Icc_id_real]
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  ring

/-- For `1 ≤ k ≤ N`, the lattice points `1 ≤ j < kx` with `j ≤ ⌊Nx⌋`
number exactly `⌊kx⌋`. -/
lemma count_j (x : ℝ) (hx0 : 0 < x) (hirr : Irrational x) (N k : ℕ)
    (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    ∑ j ∈ Finset.Icc 1 (⌊(N : ℝ) * x⌋.toNat),
        (if (j : ℝ) < (k : ℝ) * x then (1 : ℝ) else 0)
      = (⌊(k : ℝ) * x⌋ : ℝ) := by
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hkx_pos : 0 < (k : ℝ) * x := mul_pos hkR hx0
  have hfl_nonneg : (0 : ℤ) ≤ ⌊(k : ℝ) * x⌋ := Int.floor_nonneg.mpr hkx_pos.le
  have hmono : ⌊(k : ℝ) * x⌋ ≤ ⌊(N : ℝ) * x⌋ :=
    Int.floor_le_floor (mul_le_mul_of_nonneg_right (by exact_mod_cast hkN) hx0.le)
  have hirr_kx : Irrational ((k : ℝ) * x) := hirr.natCast_mul (by omega)
  have hset : (Finset.Icc 1 (⌊(N : ℝ) * x⌋.toNat)).filter
        (fun j : ℕ => (j : ℝ) < (k : ℝ) * x)
      = Finset.Icc 1 (⌊(k : ℝ) * x⌋.toNat) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hj1, _⟩, hjlt⟩
      have h1 : (j : ℤ) ≤ ⌊(k : ℝ) * x⌋ := Int.le_floor.mpr (by exact_mod_cast hjlt.le)
      exact ⟨hj1, by omega⟩
    · rintro ⟨hj1, hjK⟩
      have h1 : (j : ℤ) ≤ ⌊(k : ℝ) * x⌋ := by omega
      have h2 : (j : ℝ) ≤ ((⌊(k : ℝ) * x⌋ : ℤ) : ℝ) := by exact_mod_cast h1
      have h3 : (j : ℝ) ≤ (k : ℝ) * x := h2.trans (Int.floor_le _)
      have h4 : (j : ℝ) ≠ (k : ℝ) * x := fun h => hirr_kx.ne_nat j h.symm
      exact ⟨⟨hj1, by omega⟩, lt_of_le_of_ne h3 h4⟩
  rw [← Finset.sum_filter, hset]
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  exact_mod_cast Int.toNat_of_nonneg hfl_nonneg

/-- For `1 ≤ j ≤ ⌊Nx⌋`, the `k ∈ [1, N]` with `kx > j` number exactly
`N - ⌊j/x⌋`. -/
lemma count_k (x : ℝ) (hx0 : 0 < x) (N j : ℕ)
    (hj1 : 1 ≤ j) (hjm : j ≤ ⌊(N : ℝ) * x⌋.toNat) :
    ∑ k ∈ Finset.Icc 1 N, (if (j : ℝ) < (k : ℝ) * x then (1 : ℝ) else 0)
      = (N : ℝ) - (⌊(j : ℝ) / x⌋ : ℝ) := by
  have hj0 : 0 < j := by omega
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj0
  have ha_nonneg : (0 : ℤ) ≤ ⌊(j : ℝ) / x⌋ := Int.floor_nonneg.mpr (div_pos hjR hx0).le
  have hNx_nonneg : (0 : ℤ) ≤ ⌊(N : ℝ) * x⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg N) hx0.le)
  have hjNx : (j : ℝ) ≤ (N : ℝ) * x := by
    have h1 : (j : ℤ) ≤ ⌊(N : ℝ) * x⌋ := by omega
    have h2 : (j : ℝ) ≤ ((⌊(N : ℝ) * x⌋ : ℤ) : ℝ) := by exact_mod_cast h1
    exact h2.trans (Int.floor_le _)
  have haN : ⌊(j : ℝ) / x⌋ ≤ (N : ℤ) := by
    have h := Int.floor_le_floor ((div_le_iff₀ hx0).mpr hjNx)
    rwa [Int.floor_natCast] at h
  have hkey : ∀ k : ℕ, ((j : ℝ) < (k : ℝ) * x ↔ ⌊(j : ℝ) / x⌋ < (k : ℤ)) := by
    intro k
    rw [Int.floor_lt, div_lt_iff₀ hx0]
    norm_cast
  have hset : (Finset.Icc 1 N).filter (fun k : ℕ => (j : ℝ) < (k : ℝ) * x)
      = Finset.Icc (⌊(j : ℝ) / x⌋.toNat + 1) N := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, hkey k]
    omega
  rw [← Finset.sum_filter, hset]
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  have e1 : N + 1 - (⌊(j : ℝ) / x⌋.toNat + 1) = N - ⌊(j : ℝ) / x⌋.toNat := by omega
  have hcast : ((⌊(j : ℝ) / x⌋.toNat : ℕ) : ℝ) = ((⌊(j : ℝ) / x⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg ha_nonneg
  rw [e1, Nat.cast_sub (by omega), hcast]

/-- The lattice-point swap: `∑_{k=1}^{N} ⌊kx⌋ = ∑_{j=1}^{⌊Nx⌋} (N - ⌊j/x⌋)`. -/
lemma floor_sum_swap (x : ℝ) (hx0 : 0 < x) (hirr : Irrational x) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (⌊(k : ℝ) * x⌋ : ℝ)
      = ∑ j ∈ Finset.Icc 1 (⌊(N : ℝ) * x⌋.toNat), ((N : ℝ) - (⌊(j : ℝ) / x⌋ : ℝ)) := by
  calc ∑ k ∈ Finset.Icc 1 N, (⌊(k : ℝ) * x⌋ : ℝ)
      = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 (⌊(N : ℝ) * x⌋.toNat),
          (if (j : ℝ) < (k : ℝ) * x then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_Icc] at hk
        exact (count_j x hx0 hirr N k hk.1 hk.2).symm
    _ = ∑ j ∈ Finset.Icc 1 (⌊(N : ℝ) * x⌋.toNat), ∑ k ∈ Finset.Icc 1 N,
          (if (j : ℝ) < (k : ℝ) * x then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ j ∈ Finset.Icc 1 (⌊(N : ℝ) * x⌋.toNat), ((N : ℝ) - (⌊(j : ℝ) / x⌋ : ℝ)) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_Icc] at hj
        exact count_k x hx0 N j hj.1 hj.2

/-- The final polynomial bookkeeping: substituting `m = Nx - u` and
`⌊1/x⌋ = 1/x - Tx` reduces the assembled sums to `Φ(x,u)`. -/
lemma reciprocity_assembly (x u Nr mr A T S' SN ST : ℝ) (hx : x ≠ 0)
    (hA : A = x⁻¹ - T) (hm : mr = Nr * x - u)
    (h1 : SN = Nr / 2 - x * (Nr * (Nr + 1)) / 2
        + (mr * Nr - (A * (mr * (mr + 1) / 2) + ST)))
    (h2 : S' = mr / 2 - T * (mr * (mr + 1)) / 2 + ST) :
    SN = -S' + (u * (1 - u) / (2 * x) - u / 2) := by
  subst hA hm h1 h2
  field_simp
  ring

set_option linter.unusedVariables false in
/-- **Proposition 2.1** (Reciprocity). For irrational `x ∈ (0,1)` and
`N ≥ 1`, with `m = ⌊Nx⌋` and `u = {Nx}`:
`S_N(x) = -S_m(Tx) + Φ(x,u)`. -/
theorem reciprocity (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hirr : Irrational x)
    (N : ℕ) (hN : 1 ≤ N) :
    rotationSum N x =
      -rotationSum (⌊(N : ℝ) * x⌋.toNat) (gaussMap x)
        + Phi x (Int.fract ((N : ℝ) * x)) := by
  obtain ⟨hx0, -⟩ := hx
  have hNx_nonneg : (0 : ℝ) ≤ (N : ℝ) * x := mul_nonneg (Nat.cast_nonneg N) hx0.le
  have hfl_nonneg : (0 : ℤ) ≤ ⌊(N : ℝ) * x⌋ := Int.floor_nonneg.mpr hNx_nonneg
  have hmr : ((⌊(N : ℝ) * x⌋.toNat : ℕ) : ℝ) = ((⌊(N : ℝ) * x⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hfl_nonneg
  have hmu : ((⌊(N : ℝ) * x⌋.toNat : ℕ) : ℝ) = (N : ℝ) * x - Int.fract ((N : ℝ) * x) := by
    rw [hmr, Int.self_sub_fract]
  have hA : ((⌊x⁻¹⌋ : ℤ) : ℝ) = x⁻¹ - gaussMap x := by
    unfold gaussMap
    rw [Int.self_sub_fract]
  have h1 : rotationSum N x
      = (N : ℝ) / 2 - x * ((N : ℝ) * ((N : ℝ) + 1)) / 2
        + (((⌊(N : ℝ) * x⌋.toNat : ℕ) : ℝ) * (N : ℝ)
          - (((⌊x⁻¹⌋ : ℤ) : ℝ)
              * (((⌊(N : ℝ) * x⌋.toNat : ℕ) : ℝ) * (((⌊(N : ℝ) * x⌋.toNat : ℕ) : ℝ) + 1) / 2)
            + ∑ j ∈ Finset.Icc 1 (⌊(N : ℝ) * x⌋.toNat), (⌊(j : ℝ) * gaussMap x⌋ : ℝ))) := by
    rw [rotationSum_eq_floor_sum N x, floor_sum_swap x hx0 hirr N,
      sum_floor_div_split x (⌊(N : ℝ) * x⌋.toNat) N]
  have h2 := rotationSum_eq_floor_sum (⌊(N : ℝ) * x⌋.toNat) (gaussMap x)
  unfold Phi
  exact reciprocity_assembly x (Int.fract ((N : ℝ) * x)) (N : ℝ)
    ((⌊(N : ℝ) * x⌋.toNat : ℕ) : ℝ) ((⌊x⁻¹⌋ : ℤ) : ℝ) (gaussMap x)
    (rotationSum (⌊(N : ℝ) * x⌋.toNat) (gaussMap x)) (rotationSum N x)
    (∑ j ∈ Finset.Icc 1 (⌊(N : ℝ) * x⌋.toNat), (⌊(j : ℝ) * gaussMap x⌋ : ℝ))
    hx0.ne' hA hmu h1 h2


/-! ### Helper lemmas for display (3) -/

/-! ### Equation lemmas for `heightSeq` -/

lemma heightSeq_zero_eq (α : ℝ) (n : ℕ) : heightSeq α n 0 = n := rfl

lemma heightSeq_succ_eq (α : ℝ) (n j : ℕ) :
    heightSeq α n (j + 1) = ⌊(heightSeq α n j : ℝ) * gaussIter α j⌋.toNat := rfl

/-- Shifting the Gauss iteration by one step. -/
lemma gaussIter_shift (α : ℝ) (j : ℕ) :
    gaussIter α (j + 1) = gaussIter (gaussMap α) j := by
  unfold gaussIter
  rw [Function.iterate_succ_apply]

/-- The height sequence of `(α, n)` shifted by one step is the height
sequence of the renormalized data `(Tα, N₁)`. -/
lemma heightSeq_shift (α : ℝ) (n : ℕ) (j : ℕ) :
    heightSeq α n (j + 1) = heightSeq (gaussMap α) (heightSeq α n 1) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [heightSeq_succ_eq α n (j + 1), heightSeq_succ_eq (gaussMap α) (heightSeq α n 1) j,
      ih, gaussIter_shift]

/-- The carries shift the same way. -/
lemma carry_shift (α : ℝ) (n : ℕ) (j : ℕ) :
    carry α n (j + 1) = carry (gaussMap α) (heightSeq α n 1) j := by
  unfold carry
  rw [heightSeq_shift, gaussIter_shift]

/-- Once the height sequence hits `0` it stays `0`. -/
lemma heightSeq_succ_of_eq_zero (α : ℝ) (n j : ℕ) (h : heightSeq α n j = 0) :
    heightSeq α n (j + 1) = 0 := by
  rw [heightSeq_succ_eq, h]
  simp

/-- While nonzero, the heights strictly decrease. -/
lemma heightSeq_succ_lt (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (n j : ℕ) (h : heightSeq α n j ≠ 0) :
    heightSeq α n (j + 1) < heightSeq α n j := by
  have hx := gaussIter_mem_Ioo hα hirr j
  have hNpos : (0 : ℝ) < (heightSeq α n j : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
  have hlt : (heightSeq α n j : ℝ) * gaussIter α j < (heightSeq α n j : ℝ) :=
    mul_lt_of_lt_one_right hNpos hx.2
  have hfl : ⌊(heightSeq α n j : ℝ) * gaussIter α j⌋ < (heightSeq α n j : ℤ) :=
    Int.floor_lt.mpr (by exact_mod_cast hlt)
  have hnn : (0 : ℤ) ≤ ⌊(heightSeq α n j : ℝ) * gaussIter α j⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) hx.1.le)
  rw [heightSeq_succ_eq]
  omega

/-- Either the height is already `0`, or it has dropped by at least `j`. -/
lemma heightSeq_eq_zero_or_le (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n j : ℕ) :
    heightSeq α n j = 0 ∨ heightSeq α n j + j ≤ n := by
  induction j with
  | zero => right; simp [heightSeq_zero_eq]
  | succ j ih =>
    by_cases h : heightSeq α n j = 0
    · exact Or.inl (heightSeq_succ_of_eq_zero α n j h)
    · rcases ih with h0 | h2
      · exact absurd h0 h
      · have h1 := heightSeq_succ_lt α hα hirr n j h
        right
        omega

/-- The height sequence reaches `0` by time `n`. -/
lemma heightSeq_self_eq_zero (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n : ℕ) : heightSeq α n n = 0 := by
  rcases heightSeq_eq_zero_or_le α hα hirr n n with h | h
  · exact h
  · omega

/-! ### The stopping time -/

lemma stoppingTime_zero (α : ℝ) : stoppingTime α 0 = 0 := by
  have h0 : (0 : ℕ) ∈ {j | heightSeq α 0 j = 0} := heightSeq_zero_eq α 0
  exact Nat.sInf_eq_zero.mpr (Or.inl h0)

/-- For `n ≥ 1` the stopping time is one more than the stopping time of the
renormalized data `(Tα, N₁)`. -/
lemma stoppingTime_succ_eq (α : ℝ) (_hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n : ℕ) (hn : 1 ≤ n) :
    stoppingTime α n = stoppingTime (gaussMap α) (heightSeq α n 1) + 1 := by
  have hαg : gaussMap α ∈ Ioo (0 : ℝ) 1 := gaussMap_mem_Ioo hirr
  have hirrg : Irrational (gaussMap α) := gaussMap_irrational hirr
  have hne : {j | heightSeq (gaussMap α) (heightSeq α n 1) j = 0}.Nonempty :=
    ⟨heightSeq α n 1, heightSeq_self_eq_zero (gaussMap α) hαg hirrg _⟩
  have hkmem : heightSeq (gaussMap α) (heightSeq α n 1)
      (stoppingTime (gaussMap α) (heightSeq α n 1)) = 0 := Nat.sInf_mem hne
  have hmem : (stoppingTime (gaussMap α) (heightSeq α n 1) + 1) ∈
      {j | heightSeq α n j = 0} := by
    show heightSeq α n _ = 0
    rw [heightSeq_shift]
    exact hkmem
  have hne2 : {j | heightSeq α n j = 0}.Nonempty := ⟨_, hmem⟩
  have h2 : heightSeq α n (sInf {j | heightSeq α n j = 0}) = 0 := Nat.sInf_mem hne2
  have hlt : ∀ i, i < stoppingTime (gaussMap α) (heightSeq α n 1) + 1 →
      heightSeq α n i ≠ 0 := by
    intro i hi
    cases i with
    | zero =>
      rw [heightSeq_zero_eq]
      omega
    | succ i =>
      have hi' : i < stoppingTime (gaussMap α) (heightSeq α n 1) := by omega
      have hnotmem : i ∉ {j | heightSeq (gaussMap α) (heightSeq α n 1) j = 0} :=
        Nat.notMem_of_lt_sInf hi'
      rw [heightSeq_shift]
      exact hnotmem
  have h1 : sInf {j | heightSeq α n j = 0}
      ≤ stoppingTime (gaussMap α) (heightSeq α n 1) + 1 := Nat.sInf_le hmem
  have h3 : stoppingTime (gaussMap α) (heightSeq α n 1) + 1
      ≤ sInf {j | heightSeq α n j = 0} := by
    by_contra hc
    push_neg at hc
    exact hlt _ hc h2
  exact le_antisymm h1 h3

/-! ### Display (3) -/

/-- Display (3), generalized (it also holds for `n = 0`), in the form
suitable for strong induction on `n`. -/
lemma rotationSum_eq_alternating_sum_aux (n : ℕ) :
    ∀ α : ℝ, α ∈ Ioo (0 : ℝ) 1 → Irrational α →
      rotationSum n α =
        ∑ j ∈ Finset.range (stoppingTime α n),
          (-1 : ℝ) ^ j * Phi (gaussIter α j) (carry α n j) := by
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro α hα hirr
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- base case `n = 0`: both sides are empty sums
      rw [stoppingTime_zero]
      unfold rotationSum
      rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by omega)]
      simp
    · -- inductive step: one application of Prop 2.1, then the IH at `(Tα, N₁)`
      have hn1 : 1 ≤ n := hn
      have hαg : gaussMap α ∈ Ioo (0 : ℝ) 1 := gaussMap_mem_Ioo hirr
      have hirrg : Irrational (gaussMap α) := gaussMap_irrational hirr
      have hm1 : heightSeq α n 1 = ⌊(n : ℝ) * α⌋.toNat := rfl
      have hmlt : heightSeq α n 1 < n := by
        have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
        have hlt : (n : ℝ) * α < (n : ℝ) := mul_lt_of_lt_one_right hnpos hα.2
        have hfl : ⌊(n : ℝ) * α⌋ < (n : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hlt)
        have hnn : (0 : ℤ) ≤ ⌊(n : ℝ) * α⌋ :=
          Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n) hα.1.le)
        rw [hm1]
        omega
      have hIH := IH (heightSeq α n 1) hmlt (gaussMap α) hαg hirrg
      have hrec := reciprocity α hα hirr n hn1
      rw [← hm1] at hrec
      have hpt : ∀ j : ℕ,
          (-1 : ℝ) ^ (j + 1) * Phi (gaussIter α (j + 1)) (carry α n (j + 1))
            = -((-1 : ℝ) ^ j * Phi (gaussIter (gaussMap α) j)
                (carry (gaussMap α) (heightSeq α n 1) j)) := by
        intro j
        rw [gaussIter_shift, carry_shift, pow_succ]
        ring
      have hs : ∑ j ∈ Finset.range (stoppingTime (gaussMap α) (heightSeq α n 1)),
            (-1 : ℝ) ^ (j + 1) * Phi (gaussIter α (j + 1)) (carry α n (j + 1))
          = ∑ j ∈ Finset.range (stoppingTime (gaussMap α) (heightSeq α n 1)),
            -((-1 : ℝ) ^ j * Phi (gaussIter (gaussMap α) j)
              (carry (gaussMap α) (heightSeq α n 1) j)) :=
        Finset.sum_congr rfl fun j _ => hpt j
      rw [stoppingTime_succ_eq α hα hirr n hn1]
      simp only [Finset.sum_range_succ']
      rw [hs, Finset.sum_neg_distrib, ← hIH, hrec]
      simp [carry, heightSeq_zero_eq]

set_option linter.unusedVariables false in
/-- **Display (3)**: iterating Prop 2.1 to the stopping time gives the
exact alternating identity for `S_n(α)`. -/
theorem rotationSum_eq_alternating_sum (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n : ℕ) (hn : 1 ≤ n) :
    rotationSum n α =
      ∑ j ∈ Finset.range (stoppingTime α n),
        (-1 : ℝ) ^ j * Phi (gaussIter α j) (carry α n j) :=
  rotationSum_eq_alternating_sum_aux n α hα hirr


/-! ### Helper lemmas for display (7) -/

/-! ### Equation lemmas -/

lemma heightError_zero_eqD (α : ℝ) (n : ℕ) : heightError α n 0 = 0 := rfl

lemma heightError_succ_eqD (α : ℝ) (n j : ℕ) :
    heightError α n (j + 1) = (n : ℝ) * betaProd α j - (heightSeq α n (j + 1) : ℝ) := rfl

lemma betaProd_zero_eqD (α : ℝ) : betaProd α 0 = gaussIter α 0 := by
  unfold betaProd
  rw [Finset.prod_range_one]

lemma betaProd_succD (α : ℝ) (j : ℕ) :
    betaProd α (j + 1) = betaProd α j * gaussIter α (j + 1) := by
  unfold betaProd
  rw [Finset.prod_range_succ]

/-- The real-valued form of the height recursion `N_{j+1} = N_j x_j - u_j`. -/
lemma heightSeq_cast_succD (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (n j : ℕ) :
    ((heightSeq α n (j + 1) : ℕ) : ℝ)
      = (heightSeq α n j : ℝ) * gaussIter α j - carry α n j := by
  have hx := gaussIter_mem_Ioo hα hirr j
  have hnn : (0 : ℤ) ≤ ⌊(heightSeq α n j : ℝ) * gaussIter α j⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) hx.1.le)
  rw [heightSeq_succ_eq]
  have hc : ((⌊(heightSeq α n j : ℝ) * gaussIter α j⌋.toNat : ℕ) : ℝ)
      = ((⌊(heightSeq α n j : ℝ) * gaussIter α j⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnn
  rw [hc]
  unfold carry Int.fract
  ring

/-! ### Display (5): the error recursion -/

/-- **(5)**: `E_{j+1} = x_j E_j + u_j`. -/
lemma heightError_recD (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (n j : ℕ) :
    heightError α n (j + 1) = gaussIter α j * heightError α n j + carry α n j := by
  cases j with
  | zero =>
    rw [heightError_succ_eqD α n 0, heightError_zero_eqD,
      heightSeq_cast_succD α hα hirr n 0, heightSeq_zero_eq, betaProd_zero_eqD]
    ring
  | succ k =>
    rw [heightError_succ_eqD α n (k + 1), heightError_succ_eqD α n k,
      heightSeq_cast_succD α hα hirr n (k + 1), betaProd_succD α k]
    ring

/-! ### The lower bound -/

lemma heightError_nonnegD (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (n j : ℕ) :
    0 ≤ heightError α n j := by
  induction j with
  | zero => simp [heightError_zero_eqD]
  | succ j ih =>
    rw [heightError_recD α hα hirr n j]
    have hx := gaussIter_mem_Ioo hα hirr j
    have hu : 0 ≤ carry α n j := by
      unfold carry
      exact Int.fract_nonneg _
    have := mul_nonneg hx.1.le ih
    linarith

/-! ### Display (6): the product bound -/

/-- `x_r x_{r+1} ⋯ x_{r+ℓ-1}`, a product of `ℓ` consecutive Gauss iterates. -/
def consecProdD (α : ℝ) (r ℓ : ℕ) : ℝ := ∏ k ∈ Finset.range ℓ, gaussIter α (r + k)

lemma consecProdD_zeroD (α : ℝ) (r : ℕ) : consecProdD α r 0 = 1 := by
  unfold consecProdD
  rw [Finset.range_zero, Finset.prod_empty]

lemma consecProdD_succD (α : ℝ) (r ℓ : ℕ) :
    consecProdD α r (ℓ + 1) = consecProdD α r ℓ * gaussIter α (r + ℓ) := by
  unfold consecProdD
  rw [Finset.prod_range_succ]

lemma consecProdD_nonnegD (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (r ℓ : ℕ) :
    0 ≤ consecProdD α r ℓ := by
  unfold consecProdD
  exact Finset.prod_nonneg fun k _ => (gaussIter_mem_Ioo hα hirr _).1.le

/-- `x_k (1 + x_{k+1}) ≤ 1`, from `1/x_k = a_{k+1} + x_{k+1}` and `a_{k+1} ≥ 1`. -/
lemma gauss_step_leD (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (k : ℕ) :
    gaussIter α k * (1 + gaussIter α (k + 1)) ≤ 1 := by
  have hx := gaussIter_mem_Ioo hα hirr k
  have hd : (1 : ℝ) ≤ (digit α k : ℝ) := by
    exact_mod_cast one_le_digit hα hirr k
  have hinv := inv_gaussIter_eq hα hirr k
  have h1 : (1 : ℝ) + gaussIter α (k + 1) ≤ (gaussIter α k)⁻¹ := by
    rw [hinv]; linarith
  calc gaussIter α k * (1 + gaussIter α (k + 1))
      ≤ gaussIter α k * (gaussIter α k)⁻¹ := mul_le_mul_of_nonneg_left h1 hx.1.le
    _ = 1 := mul_inv_cancel₀ hx.1.ne'

/-- The strengthened form of (6): `F_{ℓ+1} P_ℓ + F_ℓ P_{ℓ+1} ≤ 1`. -/
lemma fib_consecProdD (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (r ℓ : ℕ) :
    (Nat.fib (ℓ + 1) : ℝ) * consecProdD α r ℓ
      + (Nat.fib ℓ : ℝ) * consecProdD α r (ℓ + 1) ≤ 1 := by
  induction ℓ with
  | zero =>
    rw [consecProdD_zeroD]
    norm_num
  | succ ℓ ih =>
    have hA : 0 ≤ consecProdD α r ℓ := consecProdD_nonnegD α hα hirr r ℓ
    have hfib1 : (0 : ℝ) ≤ (Nat.fib (ℓ + 1) : ℝ) := Nat.cast_nonneg _
    have hkey : gaussIter α (r + ℓ) * (1 + gaussIter α (r + ℓ + 1)) ≤ 1 :=
      gauss_step_leD α hα hirr (r + ℓ)
    have h1 : (Nat.fib (ℓ + 1) : ℝ)
          * (consecProdD α r ℓ * (gaussIter α (r + ℓ) * (1 + gaussIter α (r + ℓ + 1))))
        ≤ (Nat.fib (ℓ + 1) : ℝ) * (consecProdD α r ℓ * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey hA) hfib1
    have hcast : ((Nat.fib (ℓ + 1 + 1) : ℕ) : ℝ)
        = (Nat.fib ℓ : ℝ) + (Nat.fib (ℓ + 1) : ℝ) := by
      have h2 : Nat.fib (ℓ + 1 + 1) = Nat.fib ℓ + Nat.fib (ℓ + 1) := Nat.fib_add_two
      rw [h2]
      push_cast
      ring
    rw [consecProdD_succD α r ℓ] at ih
    rw [consecProdD_succD α r (ℓ + 1), consecProdD_succD α r ℓ, ← Nat.add_assoc r ℓ 1, hcast]
    linarith

/-- **(6)**: `x_r ⋯ x_{r+ℓ-1} ≤ 1 / F_{ℓ+1}`. -/
lemma consecProdD_le_inv_fibD (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (r ℓ : ℕ) :
    consecProdD α r ℓ ≤ ((Nat.fib (ℓ + 1) : ℝ))⁻¹ := by
  have h := fib_consecProdD α hα hirr r ℓ
  have h2 : 0 ≤ (Nat.fib ℓ : ℝ) * consecProdD α r (ℓ + 1) :=
    mul_nonneg (Nat.cast_nonneg _) (consecProdD_nonnegD α hα hirr r (ℓ + 1))
  have hpos : (0 : ℝ) < (Nat.fib (ℓ + 1) : ℝ) := by
    have : 0 < Nat.fib (ℓ + 1) := Nat.fib_pos.mpr (Nat.succ_pos ℓ)
    exact_mod_cast this
  rw [← one_div, le_div_iff₀ hpos]
  linarith

/-! ### Summability of `∑ 1/F_{ℓ+1}` -/

lemma fib_ge_powD (ℓ : ℕ) :
    ((3 : ℝ) / 2) ^ ℓ ≤ (Nat.fib (ℓ + 2) : ℝ)
      ∧ ((3 : ℝ) / 2) ^ (ℓ + 1) ≤ (Nat.fib (ℓ + 3) : ℝ) := by
  induction ℓ with
  | zero =>
    have h3 : Nat.fib 3 = 2 := rfl
    refine ⟨by norm_num, by norm_num [h3]⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hcast : ((Nat.fib (k + 1 + 3) : ℕ) : ℝ)
        = ((Nat.fib (k + 2) : ℕ) : ℝ) + ((Nat.fib (k + 3) : ℕ) : ℝ) := by
      have hf : Nat.fib (k + 1 + 3) = Nat.fib (k + 2) + Nat.fib (k + 3) := Nat.fib_add_two
      rw [hf]
      push_cast
      ring
    have hp : (0 : ℝ) < ((3 : ℝ) / 2) ^ k := by positivity
    have e1 : ((3 : ℝ) / 2) ^ (k + 1) = ((3 : ℝ) / 2) ^ k * (3 / 2) := by rw [pow_succ]
    have e2 : ((3 : ℝ) / 2) ^ (k + 1 + 1) = ((3 : ℝ) / 2) ^ k * (3 / 2) * (3 / 2) := by
      rw [pow_succ, pow_succ]
    rw [e1] at h2
    rw [hcast, e2]
    linarith

lemma fib_succ_geD (ℓ : ℕ) : (2 / 3 : ℝ) * ((3 : ℝ) / 2) ^ ℓ ≤ (Nat.fib (ℓ + 1) : ℝ) := by
  cases ℓ with
  | zero => norm_num
  | succ k =>
    have h := (fib_ge_powD k).1
    have e : ((Nat.fib (k + 1 + 1) : ℕ) : ℝ) = ((Nat.fib (k + 2) : ℕ) : ℝ) := rfl
    have e2 : (2 / 3 : ℝ) * ((3 : ℝ) / 2) ^ (k + 1) = ((3 : ℝ) / 2) ^ k := by
      rw [pow_succ]; ring
    rw [e, e2]
    exact h

lemma inv_fib_le_geomD (ℓ : ℕ) :
    ((Nat.fib (ℓ + 1) : ℝ))⁻¹ ≤ (3 / 2 : ℝ) * ((2 : ℝ) / 3) ^ ℓ := by
  have hpos : (0 : ℝ) < (Nat.fib (ℓ + 1) : ℝ) := by
    have : 0 < Nat.fib (ℓ + 1) := Nat.fib_pos.mpr (Nat.succ_pos ℓ)
    exact_mod_cast this
  have hg : (0 : ℝ) < (3 / 2 : ℝ) * ((2 : ℝ) / 3) ^ ℓ := by positivity
  have hlb := fib_succ_geD ℓ
  have hmul := mul_le_mul_of_nonneg_right hlb hg.le
  have hone : ((2 : ℝ) / 3 * ((3 : ℝ) / 2) ^ ℓ) * ((3 / 2 : ℝ) * ((2 : ℝ) / 3) ^ ℓ) = 1 := by
    rw [show ((2 : ℝ) / 3 * ((3 : ℝ) / 2) ^ ℓ) * ((3 / 2 : ℝ) * ((2 : ℝ) / 3) ^ ℓ)
        = ((2 : ℝ) / 3 * (3 / 2 : ℝ)) * (((3 : ℝ) / 2) ^ ℓ * ((2 : ℝ) / 3) ^ ℓ) from by ring,
      ← mul_pow]
    norm_num
  rw [← one_div, div_le_iff₀ hpos]
  nlinarith [hmul, hone]

lemma summable_inv_fibD : Summable (fun ℓ : ℕ => ((Nat.fib (ℓ + 1) : ℝ))⁻¹) := by
  refine Summable.of_nonneg_of_le (f := fun ℓ : ℕ => (3 / 2 : ℝ) * ((2 : ℝ) / 3) ^ ℓ)
    (fun b => ?_) (fun b => inv_fib_le_geomD b) ?_
  · positivity
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

lemma partial_le_EstarD (m : ℕ) :
    ∑ ℓ ∈ Finset.range m, ((Nat.fib (ℓ + 1) : ℝ))⁻¹ ≤ Estar := by
  unfold Estar
  exact Summable.sum_le_tsum (Finset.range m) (fun i _ => by positivity) summable_inv_fibD

/-! ### Unfolding the recursion and the upper bound -/

lemma heightError_eq_sumD (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (n m : ℕ) :
    heightError α n m
      = ∑ i ∈ Finset.range m,
          (∏ k ∈ Finset.Ico (i + 1) m, gaussIter α k) * carry α n i := by
  induction m with
  | zero => simp [heightError_zero_eqD]
  | succ m ih =>
    rw [heightError_recD α hα hirr n m, ih, Finset.sum_range_succ, Finset.mul_sum]
    have hlast : (∏ k ∈ Finset.Ico (m + 1) (m + 1), gaussIter α k) * carry α n m
        = carry α n m := by simp
    rw [hlast]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Finset.prod_Ico_succ_top (show i + 1 ≤ m by omega)]
    ring

lemma heightError_le_partialD (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α) (n m : ℕ) :
    heightError α n m ≤ ∑ ℓ ∈ Finset.range m, ((Nat.fib (ℓ + 1) : ℝ))⁻¹ := by
  rw [heightError_eq_sumD α hα hirr n m]
  have step : ∀ i ∈ Finset.range m,
      (∏ k ∈ Finset.Ico (i + 1) m, gaussIter α k) * carry α n i
        ≤ ((Nat.fib (m - i) : ℝ))⁻¹ := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hprod_eq : (∏ k ∈ Finset.Ico (i + 1) m, gaussIter α k)
        = consecProdD α (i + 1) (m - (i + 1)) := by
      rw [Finset.prod_Ico_eq_prod_range]
      rfl
    have hb : consecProdD α (i + 1) (m - (i + 1))
        ≤ ((Nat.fib (m - (i + 1) + 1) : ℝ))⁻¹ :=
      consecProdD_le_inv_fibD α hα hirr (i + 1) (m - (i + 1))
    have hidx : m - (i + 1) + 1 = m - i := by omega
    rw [hidx] at hb
    have hnn : 0 ≤ (∏ k ∈ Finset.Ico (i + 1) m, gaussIter α k) :=
      Finset.prod_nonneg fun k _ => (gaussIter_mem_Ioo hα hirr k).1.le
    have hu1 : carry α n i ≤ 1 := by
      unfold carry
      exact (Int.fract_lt_one _).le
    calc (∏ k ∈ Finset.Ico (i + 1) m, gaussIter α k) * carry α n i
        ≤ (∏ k ∈ Finset.Ico (i + 1) m, gaussIter α k) * 1 :=
          mul_le_mul_of_nonneg_left hu1 hnn
      _ = consecProdD α (i + 1) (m - (i + 1)) := by rw [mul_one, hprod_eq]
      _ ≤ ((Nat.fib (m - i) : ℝ))⁻¹ := hb
  calc ∑ i ∈ Finset.range m, (∏ k ∈ Finset.Ico (i + 1) m, gaussIter α k) * carry α n i
      ≤ ∑ i ∈ Finset.range m, ((Nat.fib (m - i) : ℝ))⁻¹ := Finset.sum_le_sum step
    _ = ∑ i ∈ Finset.range m, ((Nat.fib (m - 1 - i + 1) : ℝ))⁻¹ := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        have h : m - i = m - 1 - i + 1 := by omega
        rw [h]
    _ = ∑ ℓ ∈ Finset.range m, ((Nat.fib (ℓ + 1) : ℝ))⁻¹ :=
        Finset.sum_range_reflect (fun ℓ => ((Nat.fib (ℓ + 1) : ℝ))⁻¹) m

/-! ### Display (7) -/

/-- **(7)**: the height errors are uniformly bounded: `0 ≤ E_j ≤ E*`. -/
theorem heightError_mem_Icc (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n j : ℕ) :
    heightError α n j ∈ Icc (0 : ℝ) Estar :=
  Set.mem_Icc.mpr
    ⟨heightError_nonnegD α hα hirr n j,
      le_trans (heightError_le_partialD α hα hirr n j) (partial_le_EstarD j)⟩


/-! ### Helper lemmas for Proposition 2.2 -/

/-! ### Elementary properties of `W` -/

lemma W_nonneg (t : ℝ) : 0 ≤ W t := by
  have h1 := Int.fract_nonneg t
  have h2 := Int.fract_lt_one t
  have h3 : 0 ≤ Int.fract t * (1 - Int.fract t) := mul_nonneg h1 (by linarith)
  unfold W
  linarith

lemma W_le_eighth (t : ℝ) : W t ≤ 1 / 8 := by
  have h1 := Int.fract_nonneg t
  have h2 := Int.fract_lt_one t
  unfold W
  nlinarith [sq_nonneg (Int.fract t - 1 / 2)]

/-- (W2) `W` is `1`-periodic. -/
lemma W_add_int (t : ℝ) (k : ℤ) : W (t + (k : ℝ)) = W t := by
  unfold W
  rw [Int.fract_add_intCast]

lemma W_eq_of_mem {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) : W s = s * (1 - s) / 2 := by
  unfold W
  rw [Int.fract_eq_self.mpr ⟨h0, h1⟩]

/-- The torus-Lipschitz estimate on a strip: the case `|d| < 1/4`,
`s ∈ [0,1)`. -/
lemma W_shift_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {d : ℝ} (hd : |d| < 1 / 4) :
    |W (s + d) - W s| ≤ |d| / 2 := by
  have hd1 : -(1 / 4 : ℝ) < d := (abs_lt.mp hd).1
  have hd2 : d < 1 / 4 := (abs_lt.mp hd).2
  have hWs : W s = s * (1 - s) / 2 := W_eq_of_mem hs0 hs1
  rcases lt_or_ge (s + d) 0 with hneg | hnn'
  · -- wrap through the integer below: both values are small
    have hd0 : d < 0 := by linarith
    have he0 : (0 : ℝ) ≤ s + d + 1 := by linarith
    have he1 : s + d + 1 < 1 := by linarith
    have h2 : W (s + d) = W (s + d + 1) := by
      have h3 : s + d + 1 = (s + d) + ((1 : ℤ) : ℝ) := by push_cast; ring
      rw [h3, W_add_int]
    have hW : W (s + d) = (s + d + 1) * (1 - (s + d + 1)) / 2 := by
      rw [h2]; exact W_eq_of_mem he0 he1
    have hA1 : 0 ≤ W (s + d) := W_nonneg _
    have hA2 : W (s + d) ≤ -d / 2 := by rw [hW]; nlinarith [sq_nonneg (s + d)]
    have hB1 : 0 ≤ W s := W_nonneg _
    have hB2 : W s ≤ -d / 2 := by rw [hWs]; nlinarith [sq_nonneg s]
    rw [abs_of_neg hd0, abs_le]
    constructor <;> linarith
  · have hnn : (0 : ℝ) ≤ s + d := hnn'
    rcases lt_or_ge (s + d) 1 with hlt | hge
    · -- no wrap: the exact secant identity
      have hW : W (s + d) = (s + d) * (1 - (s + d)) / 2 := W_eq_of_mem hnn hlt
      rw [hW, hWs]
      rcases lt_or_ge d 0 with hd0 | hd0'
      · have hdn : (0 : ℝ) ≤ -d := by linarith
        rw [abs_of_neg hd0, abs_le]
        refine ⟨?_, ?_⟩
        · nlinarith [mul_nonneg hdn (show (0:ℝ) ≤ 2 * s + d by linarith)]
        · nlinarith [mul_nonneg hdn (show (0:ℝ) ≤ 2 - 2 * s - d by linarith)]
      · have hd0 : (0 : ℝ) ≤ d := hd0'
        rw [abs_of_nonneg hd0, abs_le]
        refine ⟨?_, ?_⟩
        · nlinarith [mul_nonneg hd0 (show (0:ℝ) ≤ 2 - 2 * s - d by linarith)]
        · nlinarith [mul_nonneg hd0 (show (0:ℝ) ≤ 2 * s + d by linarith)]
    · -- wrap through the integer above: both values are small
      have hd0 : 0 < d := by linarith
      have he0 : (0 : ℝ) ≤ s + d - 1 := by linarith
      have he1 : s + d - 1 < 1 := by linarith
      have h2 : W (s + d) = W (s + d - 1) := by
        have h3 : s + d - 1 = (s + d) + ((-1 : ℤ) : ℝ) := by push_cast; ring
        rw [h3, W_add_int]
      have hW : W (s + d) = (s + d - 1) * (1 - (s + d - 1)) / 2 := by
        rw [h2]; exact W_eq_of_mem he0 he1
      have hA1 : 0 ≤ W (s + d) := W_nonneg _
      have hA2 : W (s + d) ≤ d / 2 := by rw [hW]; nlinarith [sq_nonneg (s + d - 1)]
      have hB1 : 0 ≤ W s := W_nonneg _
      have hB2 : W s ≤ d / 2 := by rw [hWs]; nlinarith [sq_nonneg (1 - s)]
      rw [abs_of_pos hd0, abs_le]
      constructor <;> linarith

/-- (W3) `W` is `1/2`-Lipschitz on the torus, in the form used below. -/
lemma W_sub_le (b d : ℝ) : |W (b + d) - W b| ≤ |d| / 2 := by
  rcases lt_or_ge |d| (1 / 4 : ℝ) with hd | hd
  · have hs0 : 0 ≤ Int.fract b := Int.fract_nonneg b
    have hs1 : Int.fract b < 1 := Int.fract_lt_one b
    have hb : W b = W (Int.fract b) := by
      unfold W
      rw [Int.fract_fract]
    have hbd : W (b + d) = W (Int.fract b + d) := by
      have h : Int.fract b + d = (b + d) + ((-⌊b⌋ : ℤ) : ℝ) := by
        unfold Int.fract
        push_cast
        ring
      rw [h, W_add_int]
    rw [hb, hbd]
    exact W_shift_le hs0 hs1 hd
  · have h1 := W_nonneg (b + d)
    have h2 := W_le_eighth (b + d)
    have h3 := W_nonneg b
    have h4 := W_le_eighth b
    have hd' : (1 / 4 : ℝ) ≤ |d| := hd
    rw [abs_le]
    constructor <;> linarith

/-! ### Bookkeeping for display (10) -/

lemma carry_nonneg (α : ℝ) (n j : ℕ) : 0 ≤ carry α n j := Int.fract_nonneg _

lemma carry_lt_one (α : ℝ) (n j : ℕ) : carry α n j < 1 := Int.fract_lt_one _

lemma nat_floor_fract (y : ℝ) (hy : 0 ≤ y) :
    ((⌊y⌋.toNat : ℕ) : ℝ) + Int.fract y = y := by
  have h : (0 : ℤ) ≤ ⌊y⌋ := Int.floor_nonneg.mpr hy
  have hc : ((⌊y⌋.toNat : ℕ) : ℝ) = ((⌊y⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg h
  rw [hc]
  exact Int.floor_add_fract y

lemma betaProd_zero (α : ℝ) : betaProd α 0 = gaussIter α 0 := by
  unfold betaProd
  simp

lemma betaProd_succ (α : ℝ) (j : ℕ) :
    betaProd α (j + 1) = betaProd α j * gaussIter α (j + 1) := by
  unfold betaProd
  rw [Finset.prod_range_succ]

lemma heightError_zero_eq (α : ℝ) (n : ℕ) : heightError α n 0 = 0 := rfl

lemma heightError_succ_eq (α : ℝ) (n j : ℕ) :
    heightError α n (j + 1)
      = (n : ℝ) * betaProd α j - (heightSeq α n (j + 1) : ℝ) := rfl

/-- One step of (2): `N_j x_j = N_{j+1} + u_j`. -/
lemma height_step (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (n j : ℕ) :
    (heightSeq α n j : ℝ) * gaussIter α j
      = (heightSeq α n (j + 1) : ℝ) + carry α n j := by
  have hx := gaussIter_mem_Ioo hα hirr j
  have hy : (0 : ℝ) ≤ (heightSeq α n j : ℝ) * gaussIter α j :=
    mul_nonneg (Nat.cast_nonneg _) hx.1.le
  unfold carry
  rw [heightSeq_succ_eq]
  exact (nat_floor_fract _ hy).symm

/-- `C_{j+1} = N_{j+1} + u_j + x_j E_j`, the identity behind (10). -/
lemma key_ten (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (n j : ℕ) :
    (n : ℝ) * betaProd α j
      = (heightSeq α n (j + 1) : ℝ) + carry α n j
        + gaussIter α j * heightError α n j := by
  cases j with
  | zero =>
    have h := height_step α hα hirr n 0
    rw [heightSeq_zero_eq] at h
    rw [betaProd_zero, heightError_zero_eq]
    linear_combination h
  | succ j =>
    have h := height_step α hα hirr n (j + 1)
    rw [betaProd_succ, heightError_succ_eq]
    linear_combination h

/-- `θ_j = {u_j + x_j E_j}`, display (10). -/
lemma theta_eq (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (n j : ℕ) :
    theta α n j = Int.fract (carry α n j + gaussIter α j * heightError α n j) := by
  unfold theta
  refine Int.fract_eq_fract.mpr ⟨(heightSeq α n (j + 1) : ℤ), ?_⟩
  rw [key_ten α hα hirr n j]
  push_cast
  ring

/-- (10) in torus form: `u_j` and `θ_j - x_j E_j` differ by an integer. -/
lemma carry_sub_theta (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (n j : ℕ) :
    ∃ k : ℤ, carry α n j
      = theta α n j + -(gaussIter α j * heightError α n j) + (k : ℝ) := by
  refine ⟨⌊carry α n j + gaussIter α j * heightError α n j⌋, ?_⟩
  rw [theta_eq α hα hirr n j]
  unfold Int.fract
  ring

/-- The consequence of (10) and (7) used in Prop 2.2. -/
lemma W_carry_sub_W_theta (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n j : ℕ) :
    |W (carry α n j) - W (theta α n j)|
      ≤ |gaussIter α j * heightError α n j| / 2 := by
  obtain ⟨k, hk⟩ := carry_sub_theta α hα hirr n j
  have h1 : W (carry α n j)
      = W (theta α n j + -(gaussIter α j * heightError α n j)) := by
    rw [hk, W_add_int]
  rw [h1]
  have h2 := W_sub_le (theta α n j) (-(gaussIter α j * heightError α n j))
  rwa [abs_neg] at h2

/-! ### The analytic core of Proposition 2.2 -/

/-- The purely algebraic content of (11): with `1/x = a + x'`,
`Φ(x,u) - a W(θ) = a (W u - W θ) + x' W u - u/2`, and each term is
bounded. -/
lemma principal_bound (x x' u θ a E Es : ℝ)
    (hx : 0 < x) (hx'0 : 0 < x') (hx'1 : x' < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (ha : 0 ≤ a)
    (hinv : x⁻¹ = a + x')
    (hE0 : 0 ≤ E) (hEs : E ≤ Es)
    (hWu : W u = u * (1 - u) / 2)
    (hd : |W u - W θ| ≤ x * E / 2) :
    |Phi x u - a * W θ| ≤ Es / 2 + 5 / 8 := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have ha' : a = x⁻¹ - x' := by linarith
  have hax_eq : a * x = 1 - x' * x := by
    rw [ha', sub_mul, inv_mul_cancel₀ hxne]
  have hax : a * x ≤ 1 := by linarith [mul_pos hx'0 hx]
  have h1 : u * (1 - u) / (2 * x) = u * (1 - u) / 2 * x⁻¹ := by
    rw [← div_div, div_eq_mul_inv]
  have hPhi : Phi x u = W u * (a + x') - u / 2 := by
    unfold Phi
    rw [h1, hWu, ← hinv]
  have hdec : Phi x u - a * W θ = a * (W u - W θ) + x' * W u - u / 2 := by
    rw [hPhi]; ring
  have hWu0 : 0 ≤ W u := W_nonneg u
  have hWu8 : W u ≤ 1 / 8 := W_le_eighth u
  have hA : |a * (W u - W θ)| ≤ Es / 2 := by
    rw [abs_mul, abs_of_nonneg ha]
    have s1 : a * |W u - W θ| ≤ a * (x * E / 2) := mul_le_mul_of_nonneg_left hd ha
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 - a * x by linarith) hE0]
  have hB : |x' * W u| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_nonneg hx'0.le, abs_of_nonneg hWu0]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 - x' by linarith) hWu0]
  have hC : |u / 2| ≤ 1 / 2 := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u / 2)]
    linarith
  obtain ⟨ha1, ha2⟩ := abs_le.mp hA
  obtain ⟨hb1, hb2⟩ := abs_le.mp hB
  obtain ⟨hc1, hc2⟩ := abs_le.mp hC
  rw [hdec, abs_le]
  constructor <;> linarith

/-- **Proposition 2.2** (Principal term), with the audit-pinned constant:
`|Φ(x_j, u_j) - a_{j+1} W(θ_j)| ≤ C₀` for every `j`. -/
theorem principal_term (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (n j : ℕ) :
    |Phi (gaussIter α j) (carry α n j) - (digit α j : ℝ) * W (theta α n j)|
      ≤ Czero := by
  have hx := gaussIter_mem_Ioo hα hirr j
  have hx' := gaussIter_mem_Ioo hα hirr (j + 1)
  have hu0 := carry_nonneg α n j
  have hu1 := carry_lt_one α n j
  have hE := heightError_mem_Icc α hα hirr n j
  have hd : |W (carry α n j) - W (theta α n j)|
      ≤ gaussIter α j * heightError α n j / 2 := by
    have h := W_carry_sub_W_theta α hα hirr n j
    rwa [abs_of_nonneg (mul_nonneg hx.1.le hE.1)] at h
  have hmain := principal_bound (gaussIter α j) (gaussIter α (j + 1))
    (carry α n j) (theta α n j) (digit α j : ℝ) (heightError α n j) Estar
    hx.1 hx'.1 hx'.2 hu0 hu1 (Nat.cast_nonneg _)
    (inv_gaussIter_eq hα hirr j) hE.1 hE.2 (W_eq_of_mem hu0 hu1) hd
  have hCz : Czero = Estar / 2 + 5 / 8 := rfl
  rw [hCz]
  exact hmain



end

end Kwon1002
