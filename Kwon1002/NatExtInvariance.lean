import Kwon1002.NatExtMeasure
import Kwon1002.WindowLaws

/-!
# Layer 2 of the natural extension: `σ` preserves `ν̂`

Manuscript v8, §6 (lines 1119-1145) fixes the two-sided Gauss system as

`Ω̂ = (0,1)²`,  `dν̂ = dx dy / (log 2 (1+xy)²)`,  `σ(x,y) = (Tx, 1/(a₁(x)+y))`,

and asserts that `ν̂` is `σ`-invariant "by branchwise change of variables".
This file carries out that change of variables.

## The cocycle identity and its exact domain

Writing `(u,v) = σ(x,y)`, so `u = 1/x - a` and `v = 1/(a+y)` with
`a = a₁(x)`, the density transforms through

`1 + u v = (1 + x y) / (x (a + y))`,        (`one_add_natExt_mul`)

which is an identity of real numbers valid **exactly when `x ≠ 0` and
`a + y ≠ 0`**, and for no other reason: `one_add_natExt_mul` is stated with
those two hypotheses and they are both used.  Both fail only outside the
region the argument runs in.  Concretely, on the `a`-th branch
`x ∈ (1/(a+1), 1/a)` with `a ≥ 1` and `y ∈ (0,1)` one has `x ≥ 1/(a+1) > 0`
and `a + y > 1`, so the identity holds on the closed branch as well: at
`x = 1/(a+1)`, at `x = 1/a`, at `y = 0` and at `y = 1` alike.  It is *not*
an artefact of the open interval.  Where it does fail is `x = 0`, and there
it fails for Lean's reason as well as the mathematical one: `(0 : ℝ)⁻¹ = 0`
makes the right-hand side `1/0 = 0` while the left-hand side is
`1 - a/(a+y) ≠ 0`.  This is the same convention that broke the `hatSzpow`
recursion (see `natExtGood` in `Kwon1002/WindowMarginal.lean`), and it is
why every lemma below carries the branch hypothesis rather than working on
all of `ℝ²`.

`Int.fract` does not bite here.  On `branch a` one has `1/x ∈ (a, a+1)`, so
`⌊1/x⌋ = a` and `T x = Int.fract (1/x) = 1/x - a` exactly
(`gaussMap_eq_of_mem_branch`); the `Int.toNat` inside `digit` is faithful
because `⌊1/x⌋ ≥ 1 ≥ 0`.  The only point of `(0,1)` at which the branch
description of `σ` is not exact is a left endpoint `x = 1/(a+1)`, where the
digit jumps to `a+1`; those are countably many points, hence null, and
`iUnion_branch_ae_eq` is what discards them.

## The route

* `branch a = (1/(a+1), 1/a)`; on it `digit x 0 = a` and
  `σ (x,y) = (ψ x, χ y)` with `ψ x = 1/x - a`, `χ y = 1/(a+y)`
  (`natExtMap_eq_of_mem_branch`).  Restricted to a branch `σ` is therefore
  a **product** map, with diagonal derivative, and the two-dimensional
  Jacobian machinery is not needed.
* `psi_image` and `chi_image`: `ψ '' branch a = (0,1)` and
  `χ '' (0,1) = branch a`, both exactly, not merely up to null sets.
* `branch_lintegral`: the change of variables on one branch, obtained from
  the one-dimensional
  `MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn`
  applied twice (both `ψ` and `χ` are antitone, which is what lets the
  injectivity side condition be dropped) and `MeasureTheory.lintegral_prod`.
* `natExtMap_measurePreserving`: the branches are pairwise disjoint and
  cover `(0,1)` up to the countable set `{1/m}`, so the two sides of the
  invariance are equal termwise as `tsum`s.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace Kwon1002

noncomputable section

namespace NatExtInvariance

/-! ## Elementary comparisons of inverses -/

/-- Strict antitonicity of `x ↦ x⁻¹` on the positive reals, in the form
used below. -/
theorem inv_lt_inv_of_lt' {u v : ℝ} (hu : 0 < u) (h : u < v) : v⁻¹ < u⁻¹ := by
  by_contra hc
  push_neg at hc
  have h2 := inv_anti₀ (inv_pos.mpr hu) hc
  rw [inv_inv, inv_inv] at h2
  linarith

/-! ## The branches of the Gauss map -/

/-- The `a`-th Gauss branch `(1/(a+1), 1/a)`, on which the first digit is
constantly `a`. -/
def branch (a : ℕ) : Set ℝ := Ioo (((a : ℝ) + 1)⁻¹) (((a : ℝ))⁻¹)

theorem measurableSet_branch (a : ℕ) : MeasurableSet (branch a) := measurableSet_Ioo

theorem one_le_cast {a : ℕ} (ha : 1 ≤ a) : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha

theorem branch_pos {a : ℕ} {x : ℝ} (hx : x ∈ branch a) : 0 < x :=
  lt_trans (by positivity) hx.1

/-- On the `a`-th branch, `1/x > a`. -/
theorem branch_lt_inv {a : ℕ} {x : ℝ} (hx : x ∈ branch a) : (a : ℝ) < x⁻¹ := by
  have h := inv_lt_inv_of_lt' (branch_pos hx) hx.2
  rwa [inv_inv] at h

/-- On the `a`-th branch, `1/x < a + 1`. -/
theorem branch_inv_lt {a : ℕ} {x : ℝ} (hx : x ∈ branch a) : x⁻¹ < (a : ℝ) + 1 := by
  have hpos : (0 : ℝ) < ((a : ℝ) + 1)⁻¹ := by positivity
  have h := inv_lt_inv_of_lt' hpos hx.1
  rwa [inv_inv] at h

theorem branch_subset {a : ℕ} (ha : 1 ≤ a) : branch a ⊆ Ioo (0 : ℝ) 1 := by
  intro x hx
  refine ⟨branch_pos hx, lt_of_lt_of_le hx.2 (inv_le_one_of_one_le₀ (one_le_cast ha))⟩

/-- The floor of `1/x` on the `a`-th branch is `a`. -/
theorem floor_inv_eq_of_mem_branch {a : ℕ} {x : ℝ} (hx : x ∈ branch a) :
    ⌊x⁻¹⌋ = (a : ℤ) := by
  rw [Int.floor_eq_iff]
  refine ⟨le_of_lt ?_, ?_⟩
  · exact_mod_cast branch_lt_inv hx
  · push_cast
    exact branch_inv_lt hx

/-- **C1.**  On the `a`-th branch the first Gauss digit is constantly `a`. -/
theorem digit_eq_of_mem_branch {a : ℕ} {x : ℝ} (hx : x ∈ branch a) : digit x 0 = a := by
  have h : ⌊x⁻¹⌋ = (a : ℤ) := floor_inv_eq_of_mem_branch hx
  simp only [digit, gaussIter_zero, h]
  exact Int.toNat_natCast a

/-- **C1.**  On the `a`-th branch the Gauss map is the affine branch
`x ↦ 1/x - a`; no `Int.fract` survives. -/
theorem gaussMap_eq_of_mem_branch {a : ℕ} {x : ℝ} (hx : x ∈ branch a) :
    gaussMap x = x⁻¹ - (a : ℝ) := by
  simp [gaussMap, Int.fract, floor_inv_eq_of_mem_branch hx]

/-- Distinct branches are disjoint: the digit reads the branch index off
any of its points. -/
theorem branch_disjoint {a b : ℕ} (hab : a ≠ b) : Disjoint (branch a) (branch b) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  exact hab (by rw [← digit_eq_of_mem_branch hxa, ← digit_eq_of_mem_branch hxb])

/-! ## The two coordinate maps of a branch -/

/-- The future half of `σ` on the `a`-th branch, `x ↦ 1/x - a`. -/
def psi (a : ℕ) (x : ℝ) : ℝ := x⁻¹ - (a : ℝ)

/-- The past half of `σ` on the `a`-th branch, `y ↦ 1/(a+y)`. -/
def chi (a : ℕ) (y : ℝ) : ℝ := ((a : ℝ) + y)⁻¹

/-- **C1/C3.**  On a branch, `σ` is the product map `ψ × χ`.  This is the
simplification that removes the need for `HasFDerivWithinAt` on `ℝ × ℝ`. -/
theorem natExtMap_eq_of_mem_branch {a : ℕ} {x : ℝ} (hx : x ∈ branch a) (y : ℝ) :
    natExtMap (x, y) = (psi a x, chi a y) := by
  simp only [natExtMap, psi, chi]
  rw [gaussMap_eq_of_mem_branch hx, digit_eq_of_mem_branch hx]

theorem chi_mem_branch {a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    chi a y ∈ branch a := by
  have hA : (1 : ℝ) ≤ (a : ℝ) := one_le_cast ha
  have h0 : (0 : ℝ) < (a : ℝ) := by linarith
  have h1 : (0 : ℝ) < (a : ℝ) + y := by linarith [hy.1]
  exact ⟨inv_lt_inv_of_lt' h1 (by linarith [hy.2]), inv_lt_inv_of_lt' h0 (by linarith [hy.1])⟩

theorem psi_mem_Ioo {a : ℕ} {x : ℝ} (hx : x ∈ branch a) : psi a x ∈ Ioo (0 : ℝ) 1 := by
  have h1 := branch_lt_inv hx
  have h2 := branch_inv_lt hx
  exact ⟨by simp only [psi]; linarith, by simp only [psi]; linarith⟩

/-- `ψ` maps the `a`-th branch **onto** `(0,1)`, exactly. -/
theorem psi_image {a : ℕ} (ha : 1 ≤ a) : psi a '' branch a = Ioo (0 : ℝ) 1 := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact psi_mem_Ioo hx
  · intro hu
    refine ⟨chi a u, chi_mem_branch ha hu, ?_⟩
    simp only [psi, chi, inv_inv]
    ring

/-- `χ` maps `(0,1)` **onto** the `a`-th branch, exactly. -/
theorem chi_image {a : ℕ} (ha : 1 ≤ a) : chi a '' Ioo (0 : ℝ) 1 = branch a := by
  ext v
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact chi_mem_branch ha hy
  · intro hv
    refine ⟨psi a v, psi_mem_Ioo hv, ?_⟩
    simp only [psi, chi]
    rw [show (a : ℝ) + (v⁻¹ - (a : ℝ)) = v⁻¹ by ring, inv_inv]

theorem psi_antitoneOn (a : ℕ) : AntitoneOn (psi a) (branch a) := by
  intro x hx y _ hxy
  simp only [psi]
  have := inv_anti₀ (branch_pos hx) hxy
  linarith

theorem chi_antitoneOn (a : ℕ) : AntitoneOn (chi a) (Ioo (0 : ℝ) 1) := by
  intro x hx y _ hxy
  simp only [chi]
  exact inv_anti₀ (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]) (by linarith)

theorem psi_hasDerivAt {a : ℕ} {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (psi a) (-((x ^ 2)⁻¹)) x := by
  have h : HasDerivAt (fun t : ℝ => t⁻¹ - (a : ℝ)) (-((x ^ 2)⁻¹)) x :=
    (hasDerivAt_inv hx).sub_const ((a : ℝ))
  exact h

theorem chi_hasDerivAt {a : ℕ} {y : ℝ} (hy : (a : ℝ) + y ≠ 0) :
    HasDerivAt (chi a) (-((((a : ℝ) + y) ^ 2)⁻¹)) y := by
  have h1 : HasDerivAt (fun t : ℝ => (a : ℝ) + t) 1 y := by
    simpa using (hasDerivAt_id y).const_add ((a : ℝ))
  have h2 : HasDerivAt (fun t : ℝ => ((a : ℝ) + t)⁻¹) (-1 / ((a : ℝ) + y) ^ 2) y := h1.inv hy
  have h3 : HasDerivAt (fun t : ℝ => ((a : ℝ) + t)⁻¹) (-((((a : ℝ) + y) ^ 2)⁻¹)) y := by
    rw [show -((((a : ℝ) + y) ^ 2)⁻¹) = -1 / ((a : ℝ) + y) ^ 2 by rw [neg_div, one_div]]
    exact h2
  exact h3

/-! ## Step 0: the density cocycle identity -/

/-- **The density cocycle identity, with its exact domain.**  With
`u = 1/x - a` and `v = 1/(a+y)`,

`1 + u v = (1 + x y) / (x (a + y))`.

The two hypotheses are sharp for this formulation: `x ≠ 0` is needed
because the right-hand side divides by `x` (and because Lean's `0⁻¹ = 0`
makes both sides disagree at `x = 0`), and `a + y ≠ 0` because both sides
divide by `a + y`.  Nothing else is required — in particular the identity
holds at the branch endpoints `x = 1/(a+1)` and `x = 1/a` and at `y = 0`
and `y = 1`. -/
theorem one_add_natExt_mul {a x y : ℝ} (hx : x ≠ 0) (hay : a + y ≠ 0) :
    1 + (x⁻¹ - a) * (a + y)⁻¹ = (1 + x * y) / (x * (a + y)) := by
  field_simp
  ring

/-- The density `1/(log 2 (1+xy)²)` of `ν̂` against Lebesgue on `(0,1)²`. -/
def dens (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (Real.log 2 * (1 + p.1 * p.2) ^ 2))

theorem measurable_dens : Measurable dens :=
  NatExtMeasure.measurable_hatNuDensity

/-- Statement identity, type check only: `dens` is the density of
`Kwon1002.hatNu` on the nose. -/
example : hatNu = (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)).withDensity dens := rfl

/-- **C2.**  The density cocycle in the form the change of variables
consumes: the product of the two one-dimensional Jacobians times the
density at the image point is the density at the source point.  Valid on
the branch, which is where `one_add_natExt_mul` applies. -/
theorem dens_cocycle {a : ℕ} (ha : 1 ≤ a) {x y : ℝ} (hx : x ∈ branch a)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    ENNReal.ofReal ((x ^ 2)⁻¹) * ENNReal.ofReal ((((a : ℝ) + y) ^ 2)⁻¹)
        * dens (psi a x, chi a y)
      = dens (x, y) := by
  have hA : (1 : ℝ) ≤ (a : ℝ) := one_le_cast ha
  have hx0 : 0 < x := branch_pos hx
  have hxne : x ≠ 0 := hx0.ne'
  have hay : (0 : ℝ) < (a : ℝ) + y := by linarith [hy.1]
  have hayne : (a : ℝ) + y ≠ 0 := hay.ne'
  have hlog : (0 : ℝ) < Real.log 2 := NatExtMeasure.log_two_pos
  have hlogne : Real.log 2 ≠ 0 := hlog.ne'
  have hxy : (0 : ℝ) < 1 + x * y := by nlinarith [hy.1, hy.2, hx0]
  have hxyne : (1 : ℝ) + x * y ≠ 0 := hxy.ne'
  simp only [dens, psi, chi]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [one_add_natExt_mul hxne hayne]
  have hprod : x * ((a : ℝ) + y) ≠ 0 := mul_ne_zero hxne hayne
  field_simp

/-! ## C3: measure preservation on one branch -/

theorem restrict_prod_eq (A B : Set ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (A ×ˢ B)
      = ((volume : Measure ℝ).restrict A).prod ((volume : Measure ℝ).restrict B) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]

/-- **C3.**  The branchwise change of variables of manuscript v8 line 1144.
On the `a`-th branch `σ` is the product map `ψ × χ`, so the two
one-dimensional antitone Jacobian formulas plus Fubini give
`∫_{branch a × (0,1)} h · (F ∘ σ) = ∫_{(0,1) × branch a} h · F`. -/
theorem branch_lintegral {a : ℕ} (ha : 1 ≤ a) {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p in branch a ×ˢ Ioo (0 : ℝ) 1, dens p * F (natExtMap p)
      = ∫⁻ q in Ioo (0 : ℝ) 1 ×ˢ branch a, dens q * F q := by
  have hA : (1 : ℝ) ≤ (a : ℝ) := one_le_cast ha
  -- the two sides as iterated integrals
  have hL : ∫⁻ p in branch a ×ˢ Ioo (0 : ℝ) 1, dens p * F (natExtMap p)
      = ∫⁻ x in branch a, ∫⁻ y in Ioo (0 : ℝ) 1, dens (x, y) * F (natExtMap (x, y)) := by
    rw [restrict_prod_eq]
    exact lintegral_prod _ ((measurable_dens.mul (hF.comp measurable_natExtMap)).aemeasurable)
  have hR : ∫⁻ q in Ioo (0 : ℝ) 1 ×ˢ branch a, dens q * F q
      = ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in branch a, dens (u, v) * F (u, v) := by
    rw [restrict_prod_eq]
    exact lintegral_prod _ ((measurable_dens.mul hF).aemeasurable)
  -- the outer change of variables, `u = ψ x`
  have houter : ∀ H : ℝ → ℝ≥0∞, (∫⁻ u in Ioo (0 : ℝ) 1, H u)
      = ∫⁻ x in branch a, ENNReal.ofReal ((x ^ 2)⁻¹) * H (psi a x) := by
    intro H
    have key := lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn
      (s := branch a) (f := psi a) (f' := fun x => -((x ^ 2)⁻¹))
      (measurableSet_branch a)
      (fun x hx => (psi_hasDerivAt (a := a) (branch_pos hx).ne').hasDerivWithinAt)
      (psi_antitoneOn a) H
    rw [psi_image ha] at key
    rw [key]
    simp only [neg_neg]
  -- the inner change of variables, `v = χ y`
  have hinner : ∀ u : ℝ, (∫⁻ v in branch a, dens (u, v) * F (u, v))
      = ∫⁻ y in Ioo (0 : ℝ) 1,
          ENNReal.ofReal ((((a : ℝ) + y) ^ 2)⁻¹) * (dens (u, chi a y) * F (u, chi a y)) := by
    intro u
    have hd : ∀ y ∈ Ioo (0 : ℝ) 1,
        HasDerivWithinAt (chi a) ((fun t : ℝ => -((((a : ℝ) + t) ^ 2)⁻¹)) y)
          (Ioo (0 : ℝ) 1) y := by
      intro y hy
      exact (chi_hasDerivAt (a := a) (by
        have : (0 : ℝ) < (a : ℝ) + y := by linarith [hy.1]
        exact this.ne')).hasDerivWithinAt
    have key := lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn
      (s := Ioo (0 : ℝ) 1) (f := chi a) (f' := fun t : ℝ => -((((a : ℝ) + t) ^ 2)⁻¹))
      measurableSet_Ioo hd (chi_antitoneOn a) (fun v => dens (u, v) * F (u, v))
    rw [chi_image ha] at key
    rw [key]
    simp only [neg_neg]
  rw [hL, hR, houter (fun u => ∫⁻ v in branch a, dens (u, v) * F (u, v))]
  refine setLIntegral_congr_fun (measurableSet_branch a) (fun x hx => ?_)
  rw [hinner (psi a x), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun y hy => ?_)
  rw [natExtMap_eq_of_mem_branch hx y, ← mul_assoc, ← mul_assoc, dens_cocycle ha hx hy]

/-! ## C4: assembling the branches -/

/-- The branches cover `(0,1)` up to the countable set of reciprocals of
the positive integers. -/
theorem iUnion_branch_ae_eq :
    (⋃ n : ℕ, branch (n + 1)) =ᵐ[volume] Ioo (0 : ℝ) 1 := by
  have hsub : (⋃ n : ℕ, branch (n + 1)) ⊆ Ioo (0 : ℝ) 1 :=
    Set.iUnion_subset (fun n => branch_subset (by omega))
  have hcount : Ioo (0 : ℝ) 1 \ (⋃ n : ℕ, branch (n + 1))
      ⊆ Set.range (fun m : ℕ => ((m : ℝ))⁻¹) := by
    rintro x ⟨hx, hxn⟩
    have hx0 : (0 : ℝ) < x := hx.1
    have hxinv : (1 : ℝ) < x⁻¹ := by
      have := inv_lt_inv_of_lt' hx0 hx.2
      rwa [inv_one] at this
    have hfl1 : (1 : ℤ) ≤ ⌊x⁻¹⌋ := Int.le_floor.mpr (by exact_mod_cast hxinv.le)
    set m : ℕ := ⌊x⁻¹⌋.toNat with hm
    have hmcast : ((m : ℕ) : ℝ) = ((⌊x⁻¹⌋ : ℤ) : ℝ) := by
      rw [hm]; exact_mod_cast Int.toNat_of_nonneg (by omega)
    have hm1 : 1 ≤ m := by omega
    have hlow : ((m : ℕ) : ℝ) ≤ x⁻¹ := by rw [hmcast]; exact Int.floor_le _
    have hhigh : x⁻¹ < ((m : ℕ) : ℝ) + 1 := by
      rw [hmcast]; exact Int.lt_floor_add_one _
    have hm0 : (0 : ℝ) < (m : ℝ) := by
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      linarith
    have hxle : x ≤ ((m : ℝ))⁻¹ := by
      have := inv_anti₀ hm0 hlow
      rwa [inv_inv] at this
    have hxgt : (((m : ℝ)) + 1)⁻¹ < x := by
      have := inv_lt_inv_of_lt' (inv_pos.mpr hx0) hhigh
      rwa [inv_inv] at this
    rcases lt_or_eq_of_le hxle with hlt | heq
    · exfalso
      refine hxn (Set.mem_iUnion.mpr ⟨m - 1, ?_⟩)
      have hidx : m - 1 + 1 = m := by omega
      rw [hidx]
      exact ⟨hxgt, hlt⟩
    · exact ⟨m, heq.symm⟩
  refine ae_eq_set.mpr ⟨?_, ?_⟩
  · rw [Set.diff_eq_empty.mpr hsub, measure_empty]
  · exact measure_mono_null hcount ((Set.countable_range _).measure_zero _)

/-! ## C4: `ν̂` is `σ`-invariant -/

/-- A product of an a.e. equality on the left factor. -/
theorem prod_ae_eq_left {A B C : Set ℝ} (h : A =ᵐ[volume] B) :
    (A ×ˢ C) =ᵐ[volume] (B ×ˢ C) := by
  rw [ae_eq_set] at h ⊢
  constructor
  · refine measure_mono_null (?_ : (A ×ˢ C) \ (B ×ˢ C) ⊆ (A \ B) ×ˢ C) ?_
    · rintro ⟨x, y⟩ ⟨⟨hx, hy⟩, hnot⟩
      exact ⟨⟨hx, fun hb => hnot ⟨hb, hy⟩⟩, hy⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod, h.1, zero_mul]
  · refine measure_mono_null (?_ : (B ×ˢ C) \ (A ×ˢ C) ⊆ (B \ A) ×ˢ C) ?_
    · rintro ⟨x, y⟩ ⟨⟨hx, hy⟩, hnot⟩
      exact ⟨⟨hx, fun hb => hnot ⟨hb, hy⟩⟩, hy⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod, h.2, zero_mul]

/-- A product of an a.e. equality on the right factor. -/
theorem prod_ae_eq_right {A B C : Set ℝ} (h : A =ᵐ[volume] B) :
    (C ×ˢ A) =ᵐ[volume] (C ×ˢ B) := by
  rw [ae_eq_set] at h ⊢
  constructor
  · refine measure_mono_null (?_ : (C ×ˢ A) \ (C ×ˢ B) ⊆ C ×ˢ (A \ B)) ?_
    · rintro ⟨x, y⟩ ⟨⟨hx, hy⟩, hnot⟩
      exact ⟨hx, ⟨hy, fun hb => hnot ⟨hx, hb⟩⟩⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod, h.1, mul_zero]
  · refine measure_mono_null (?_ : (C ×ˢ B) \ (C ×ˢ A) ⊆ C ×ˢ (B \ A)) ?_
    · rintro ⟨x, y⟩ ⟨⟨hx, hy⟩, hnot⟩
      exact ⟨hx, ⟨hy, fun hb => hnot ⟨hx, hb⟩⟩⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod, h.2, mul_zero]

/-- `ν̂` evaluated on a measurable set, as a Lebesgue integral of `dens`. -/
theorem hatNu_apply {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    hatNu A = ∫⁻ p in A ∩ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1), dens p := by
  simp only [hatNu]
  rw [withDensity_apply _ hA, Measure.restrict_restrict hA]
  rfl

/-- Cutting a set integral down to an indicator factor. -/
theorem setLIntegral_inter_eq {T A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (g : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ p in T ∩ A, g p = ∫⁻ p in T, g p * A.indicator (fun _ => 1) p := by
  have hpt : ∀ p, g p * A.indicator (fun _ => (1 : ℝ≥0∞)) p = A.indicator g p := by
    intro p
    by_cases h : p ∈ A
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  simp_rw [hpt]
  rw [lintegral_indicator hA, Measure.restrict_restrict hA, Set.inter_comm]

/-- **C4.  The natural-extension map preserves `ν̂`.**  Manuscript v8,
line 1144: "the displayed density `ν̂` is `σ`-invariant by branchwise change
of variables".

The branches `(1/(a+1), 1/a)`, `a ≥ 1`, are pairwise disjoint and cover
`(0,1)` up to the countable set `{1/m}` (`iUnion_branch_ae_eq`), so both
`ν̂ (σ⁻¹ S)` and `ν̂ S` split as sums over branches — the source splitting by
the *first* coordinate and the target by the *second*, since `σ` sends
`branch a × (0,1)` onto `(0,1) × branch a`.  `branch_lintegral` matches the
two sums term by term. -/
theorem natExtMap_measurePreserving : MeasurePreserving natExtMap hatNu hatNu := by
  refine ⟨measurable_natExtMap, ?_⟩
  refine Measure.ext (fun S hS => ?_)
  rw [Measure.map_apply measurable_natExtMap hS]
  have hpre : MeasurableSet (natExtMap ⁻¹' S) := measurable_natExtMap hS
  rw [hatNu_apply hpre, hatNu_apply hS]
  -- the two branch decompositions
  have hmL : ∀ n : ℕ, MeasurableSet ((branch (n + 1) ×ˢ Ioo (0 : ℝ) 1) ∩ natExtMap ⁻¹' S) :=
    fun n => ((measurableSet_branch _).prod measurableSet_Ioo).inter hpre
  have hmR : ∀ n : ℕ, MeasurableSet ((Ioo (0 : ℝ) 1 ×ˢ branch (n + 1)) ∩ S) :=
    fun n => (measurableSet_Ioo.prod (measurableSet_branch _)).inter hS
  have hdL : Pairwise (Function.onFun Disjoint
      (fun n : ℕ => (branch (n + 1) ×ˢ Ioo (0 : ℝ) 1) ∩ natExtMap ⁻¹' S)) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨⟨hx, _⟩, _⟩ ⟨⟨hx', _⟩, _⟩
    exact (Set.disjoint_left.mp (branch_disjoint (by omega : m + 1 ≠ n + 1))) hx hx'
  have hdR : Pairwise (Function.onFun Disjoint
      (fun n : ℕ => (Ioo (0 : ℝ) 1 ×ˢ branch (n + 1)) ∩ S)) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨⟨_, hy⟩, _⟩ ⟨⟨_, hy'⟩, _⟩
    exact (Set.disjoint_left.mp (branch_disjoint (by omega : m + 1 ≠ n + 1))) hy hy'
  have heL : (((natExtMap ⁻¹' S) ∩ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) : Set (ℝ × ℝ))
      =ᵐ[volume] ((⋃ n : ℕ, (branch (n + 1) ×ˢ Ioo (0 : ℝ) 1) ∩ natExtMap ⁻¹' S) :
        Set (ℝ × ℝ)) := by
    have h1 : (((natExtMap ⁻¹' S) ∩ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) : Set (ℝ × ℝ))
        =ᵐ[volume] (((natExtMap ⁻¹' S) ∩ ((⋃ n : ℕ, branch (n + 1)) ×ˢ Ioo (0 : ℝ) 1)) :
          Set (ℝ × ℝ)) :=
      (Filter.EventuallyEq.refl _ (natExtMap ⁻¹' S)).inter (prod_ae_eq_left iUnion_branch_ae_eq).symm
    refine h1.trans (Filter.EventuallyEq.of_eq ?_)
    rw [Set.iUnion_prod_const, Set.inter_iUnion]
    exact Set.iUnion_congr (fun n => Set.inter_comm _ _)
  have heR : ((S ∩ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) : Set (ℝ × ℝ))
      =ᵐ[volume] ((⋃ n : ℕ, (Ioo (0 : ℝ) 1 ×ˢ branch (n + 1)) ∩ S) : Set (ℝ × ℝ)) := by
    have h1 : ((S ∩ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) : Set (ℝ × ℝ))
        =ᵐ[volume] ((S ∩ (Ioo (0 : ℝ) 1 ×ˢ (⋃ n : ℕ, branch (n + 1)))) : Set (ℝ × ℝ)) :=
      (Filter.EventuallyEq.refl _ S).inter (prod_ae_eq_right iUnion_branch_ae_eq).symm
    refine h1.trans (Filter.EventuallyEq.of_eq ?_)
    rw [Set.prod_iUnion, Set.inter_iUnion]
    exact Set.iUnion_congr (fun n => Set.inter_comm _ _)
  rw [setLIntegral_congr heL, setLIntegral_congr heR,
    lintegral_iUnion hmL hdL, lintegral_iUnion hmR hdR]
  refine tsum_congr (fun n => ?_)
  rw [setLIntegral_inter_eq hpre, setLIntegral_inter_eq hS]
  have hind : ∀ p : ℝ × ℝ, (natExtMap ⁻¹' S).indicator (fun _ => (1 : ℝ≥0∞)) p
      = S.indicator (fun _ => (1 : ℝ≥0∞)) (natExtMap p) := by
    intro p
    by_cases h : natExtMap p ∈ S
    · simp [Set.indicator_of_mem, h, Set.mem_preimage]
    · simp [Set.indicator_of_notMem, h, Set.mem_preimage]
  simp_rw [hind]
  exact branch_lintegral (by omega) (measurable_const.indicator hS)

/-! ## C5: the backward map

`natExtInv` is `natExtMap` conjugated by the coordinate swap, and both `ν̂`
and the unit square are swap-symmetric, so no second branch analysis is
needed. -/

/-- The density is symmetric in its two arguments. -/
theorem dens_swap (p : ℝ × ℝ) : dens (Prod.swap p) = dens p := by
  simp only [dens, Prod.fst_swap, Prod.snd_swap]
  rw [mul_comm p.2 p.1]

theorem preimage_swap_unitSq :
    (Prod.swap : ℝ × ℝ → ℝ × ℝ) ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)
      = Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  ext ⟨x, y⟩
  simp only [Set.mem_preimage, Prod.swap_prod_mk, Set.mem_prod]
  exact and_comm

theorem setLIntegral_dens_swap {T : Set (ℝ × ℝ)} (hT : MeasurableSet T) :
    ∫⁻ p in (Prod.swap : ℝ × ℝ → ℝ × ℝ) ⁻¹' T, dens p = ∫⁻ q in T, dens q := by
  have hmp : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  have hpt : ∀ p : ℝ × ℝ,
      (T.indicator dens) (Prod.swap p) = ((Prod.swap : ℝ × ℝ → ℝ × ℝ) ⁻¹' T).indicator dens p := by
    intro p
    by_cases h : Prod.swap p ∈ T
    · have h' : p ∈ (Prod.swap : ℝ × ℝ → ℝ × ℝ) ⁻¹' T := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h', dens_swap]
    · have h' : p ∉ (Prod.swap : ℝ × ℝ → ℝ × ℝ) ⁻¹' T := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  calc ∫⁻ p in (Prod.swap : ℝ × ℝ → ℝ × ℝ) ⁻¹' T, dens p
      = ∫⁻ p, ((Prod.swap : ℝ × ℝ → ℝ × ℝ) ⁻¹' T).indicator dens p :=
        (lintegral_indicator (measurable_swap hT) _).symm
    _ = ∫⁻ p, (T.indicator dens) (Prod.swap p) := by simp_rw [hpt]
    _ = ∫⁻ q, T.indicator dens q := hmp.lintegral_comp (measurable_dens.indicator hT)
    _ = ∫⁻ q in T, dens q := lintegral_indicator hT _

/-- The coordinate swap preserves `ν̂`. -/
theorem measurePreserving_swap_hatNu :
    MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) hatNu hatNu := by
  refine ⟨measurable_swap, Measure.ext (fun S hS => ?_)⟩
  rw [Measure.map_apply measurable_swap hS, hatNu_apply (measurable_swap hS), hatNu_apply hS]
  rw [show ((Prod.swap : ℝ × ℝ → ℝ × ℝ) ⁻¹' S) ∩ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)
      = (Prod.swap : ℝ × ℝ → ℝ × ℝ) ⁻¹' (S ∩ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) by
    rw [Set.preimage_inter, preimage_swap_unitSq]]
  exact setLIntegral_dens_swap (hS.inter (measurableSet_Ioo.prod measurableSet_Ioo))

/-- `σ⁻¹` is `σ` conjugated by the coordinate swap. -/
theorem natExtInv_eq_swap :
    natExtInv = (Prod.swap : ℝ × ℝ → ℝ × ℝ) ∘ natExtMap ∘ (Prod.swap : ℝ × ℝ → ℝ × ℝ) := by
  funext p
  simp [natExtInv, natExtMap, Function.comp]

/-- **C5.**  The backward natural-extension map preserves `ν̂` as well. -/
theorem natExtInv_measurePreserving : MeasurePreserving natExtInv hatNu hatNu := by
  rw [natExtInv_eq_swap]
  exact measurePreserving_swap_hatNu.comp
    (natExtMap_measurePreserving.comp measurePreserving_swap_hatNu)

end NatExtInvariance

end

end Kwon1002
