module

public import LowDimensionalTopology.Geometry.Teichmuller.EllipticFiniteOrder
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalTeichmullerStraightLineGeometry
public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The midpoint and iterate proof for an invariant straight line

The original full QC modular group acts on the original marked quotient with
its genuine full-log metric. The sole unproved input is the concrete
straight-line geometry. Infinite order excludes fixed points by the proved
finiteness of point stabilizers.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers

open Set Surfaces LiZhongQC
open LowDimensionalTopology.Unproved.Teichmuller

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

local notation "QCPointR" => @TeichSpace X _ R.toRiemannAtlas.toChartedSpace
local notation "ModularR" =>
  @SourceQCModular.ModularGroup X _ R.toRiemannAtlas.toChartedSpace R.toRiemannAtlas.isManifold

/-- A positive attained displacement gives an invariant line through the original point. -/
theorem exists_invariantLine_of_minimizingPoint_of_pos
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hgeometry : OriginalTeichmullerStraightLineGeometry R hg hgenus)
    (γ : ModularR) (p : QCPointR) (hp : IsMinimizingPoint R γ p)
    (hpos : 0 < displacement R γ p) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    letI := R.compactSpace
    letI := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
    ∃ ℓ : ℝ → QCPointR, Isometry ℓ ∧ p ∈ range ℓ ∧
      (fun q : QCPointR => γ • q) '' range ℓ = range ℓ := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
  obtain ⟨hline, hunique, hbetween⟩ := hgeometry
  have hiso (δ : ModularR) : Isometry (fun q : QCPointR => δ • q) :=
    SourceQCModular.bookMetric_isometry hg (R.hasSourceGenus hgenus) δ
  have hmin : ∀ q : QCPointR, dist p (γ • p) ≤ dist q (γ • q) :=
    (isMinimizingPoint_iff R γ p).mp hp
  let a : ℝ := dist p (γ • p)
  have ha : 0 < a := hpos
  have hpne : p ≠ γ • p := dist_pos.mp ha
  obtain ⟨ℓ, hℓ, hzero, haℓ⟩ := hline p (γ • p) hpne
  let m : QCPointR := ℓ (a / 2)
  let n : QCPointR := γ • m
  have hpm : dist p m = a / 2 := by
    rw [← hzero, hℓ.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg (by linarith : 0 ≤ a / 2)]
  have hmp : dist m (γ • p) = a / 2 := by
    rw [← haℓ, hℓ.dist_eq, Real.dist_eq,
      abs_of_nonpos (by linarith : a / 2 - a ≤ 0)]
    ring
  have hpn : dist (γ • p) n = a / 2 := by
    rw [(hiso γ).dist_eq]
    exact hpm
  have hmn : dist m n = a := by
    apply le_antisymm
    · calc
        dist m n ≤ dist m (γ • p) + dist (γ • p) n := dist_triangle _ _ _
        _ = a := by rw [hmp, hpn]; ring
    · exact hmin m
  have hmne : m ≠ n := by
    apply dist_pos.mp
    rw [hmn]
    exact ha
  obtain ⟨k, hk, hkzero, hka⟩ := hline m n hmne
  have hpk : γ • p ∈ range k := by
    apply hbetween k hk 0 (dist m n) (γ • p)
    rw [hkzero, hka, hmp, hpn, hmn]
    ring
  have hmℓ : m ∈ range ℓ := ⟨a / 2, rfl⟩
  have hpℓ : γ • p ∈ range ℓ := ⟨a, haℓ⟩
  have hmk : m ∈ range k := ⟨0, hkzero⟩
  have hmpne : m ≠ γ • p := by
    apply dist_pos.mp
    rw [hmp]
    linarith
  have hranges : range k = range ℓ :=
    hunique k ℓ hk hℓ m (γ • p) hmpne hmk hpk hmℓ hpℓ
  have hnℓ : n ∈ range ℓ := hranges ▸ (show n ∈ range k from ⟨dist m n, hka⟩)
  have hγℓ : Isometry (fun t : ℝ => γ • ℓ t) := (hiso γ).comp hℓ
  have hγranges : range (fun t : ℝ => γ • ℓ t) = range ℓ := by
    apply hunique _ ℓ hγℓ hℓ (γ • p) n
    · apply dist_pos.mp
      rw [hpn]
      linarith
    · exact ⟨0, congrArg (fun q : QCPointR => γ • q) hzero⟩
    · exact ⟨a / 2, rfl⟩
    · exact hpℓ
    · exact hnℓ
  refine ⟨ℓ, hℓ, ⟨0, hzero⟩, ?_⟩
  simpa only [range_comp'] using hγranges

/-- On an invariant original line, the action is a reflection or has exact
linear orbit distances and attains its original displacement infimum. -/
theorem invariantLine_reflection_or_orbit_minimum
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (γ : ModularR) (p : QCPointR) (ℓ : ℝ → QCPointR) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    letI := R.compactSpace
    letI := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
    Isometry ℓ → p ∈ range ℓ →
      (fun q : QCPointR => γ • q) '' range ℓ = range ℓ →
        (∃ c : ℝ, ∀ t : ℝ, γ • ℓ t = ℓ (c - t)) ∨
          ((∀ n : ℕ, dist p (γ ^ n • p) = (n : ℝ) * dist p (γ • p)) ∧
            IsMinimizingPoint R γ p) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
  have hiso (δ : ModularR) : Isometry (fun q : QCPointR => δ • q) :=
    SourceQCModular.bookMetric_isometry hg (R.hasSourceGenus hgenus) δ
  exact fun hℓ hpℓ hinvariant => by
    obtain ⟨r, hr⟩ := hpℓ
    have hmap (t : ℝ) : ∃ s : ℝ, ℓ s = γ • ℓ t := by
      have hm : γ • ℓ t ∈ range ℓ := hinvariant ▸ ⟨ℓ t, ⟨t, rfl⟩, rfl⟩
      exact hm
    let φ : ℝ → ℝ := fun t => Classical.choose (hmap t)
    have hφ (t : ℝ) : ℓ (φ t) = γ • ℓ t := Classical.choose_spec (hmap t)
    have hφiso : Isometry φ := by
      apply Isometry.of_dist_eq
      intro s t
      rw [← hℓ.dist_eq, hφ, hφ, (hiso γ).dist_eq, hℓ.dist_eq]
    have hφsurj : Function.Surjective φ := by
      intro s
      have hm : ℓ s ∈ (fun q : QCPointR => γ • q) '' range ℓ :=
        hinvariant.symm ▸ (show ℓ s ∈ range ℓ from ⟨s, rfl⟩)
      obtain ⟨q, ⟨t, rfl⟩, hq⟩ := hm
      exact ⟨t, hℓ.injective ((hφ t).trans hq)⟩
    let e : ℝ ≃ᵢ ℝ :=
      { Equiv.ofBijective φ ⟨hφiso.injective, hφsurj⟩ with isometry_toFun := hφiso }
    let L := e.toRealLinearIsometryEquiv
    have hlinear (t : ℝ) : L t = t * L 1 := by
      simpa only [smul_eq_mul, mul_one] using L.map_smul t (1 : ℝ)
    have hunit : |L 1| = |(1 : ℝ)| := by
      simpa only [Real.norm_eq_abs] using L.norm_map (1 : ℝ)
    rcases abs_eq_abs.mp hunit with hpositive | hnegative
    · have htranslation (t : ℝ) : φ t = t + φ 0 := by
        have ht := hlinear t
        rw [IsometryEquiv.toRealLinearIsometryEquiv_apply] at ht
        change φ t - φ 0 = t * L 1 at ht
        rw [hpositive, mul_one] at ht
        linarith
      have haction (t : ℝ) : γ • ℓ t = ℓ (t + φ 0) := by
        rw [← hφ, htranslation]
      have hpow (n : ℕ) (t : ℝ) :
          γ ^ n • ℓ t = ℓ (t + (n : ℝ) * φ 0) := by
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', mul_smul, ih, haction]
          congr 1
          push_cast
          ring
      have horbit (n : ℕ) : dist p (γ ^ n • p) = (n : ℝ) * dist p (γ • p) := by
        rw [← hr, hpow, haction, hℓ.dist_eq, hℓ.dist_eq, Real.dist_eq, Real.dist_eq]
        rw [show r - (r + (n : ℝ) * φ 0) = -((n : ℝ) * φ 0) by ring,
          show r - (r + φ 0) = -(φ 0) by ring, abs_neg, abs_neg, abs_mul,
          abs_of_nonneg (Nat.cast_nonneg n)]
      refine Or.inr ⟨horbit, ?_⟩
      have hupper (q : QCPointR) (n : ℕ) :
          dist q (γ ^ n • q) ≤ (n : ℝ) * dist q (γ • q) := by
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', mul_smul]
          calc
            dist q (γ • (γ ^ n • q)) ≤
                dist q (γ • q) + dist (γ • q) (γ • (γ ^ n • q)) := dist_triangle _ _ _
            _ = dist q (γ • q) + dist q (γ ^ n • q) := by rw [(hiso γ).dist_eq]
            _ ≤ dist q (γ • q) + (n : ℝ) * dist q (γ • q) := by linarith [ih]
            _ = ((n + 1 : ℕ) : ℝ) * dist q (γ • q) := by push_cast; ring
      apply (isMinimizingPoint_iff R γ p).mpr
      intro q
      change dist p (γ • p) ≤ dist q (γ • q)
      have hbound (n : ℕ) :
          (n : ℝ) * dist p (γ • p) ≤
            2 * dist p q + (n : ℝ) * dist q (γ • q) := by
        rw [← horbit]
        calc
          dist p (γ ^ n • p) ≤ dist p q + dist q (γ ^ n • q) +
              dist (γ ^ n • q) (γ ^ n • p) := dist_triangle4 _ _ _ _
          _ = dist p q + dist q (γ ^ n • q) + dist p q := by
            rw [(hiso (γ ^ n)).dist_eq, dist_comm q p]
          _ ≤ 2 * dist p q + (n : ℝ) * dist q (γ • q) := by
            linarith [hupper q n]
      by_contra hnot
      have hpos : 0 < dist p (γ • p) - dist q (γ • q) := sub_pos.mpr (lt_of_not_ge hnot)
      obtain ⟨n, hn⟩ := exists_nat_gt
        (2 * dist p q / (dist p (γ • p) - dist q (γ • q)))
      have hlarge := (div_lt_iff₀ hpos).mp hn
      nlinarith [hbound n]
    · refine Or.inl ⟨φ 0, ?_⟩
      intro t
      have ht := hlinear t
      rw [IsometryEquiv.toRealLinearIsometryEquiv_apply] at ht
      change φ t - φ 0 = t * L 1 at ht
      rw [hnegative] at ht
      have hreflect : φ t = φ 0 - t := by linarith
      rw [← hφ, hreflect]

/-- The minimizing-point equivalence, with the precise missing straight-line bridge explicit. -/
theorem isMinimizingPoint_iff_exists_invariantLine_of_straightLineGeometry
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hgeometry : OriginalTeichmullerStraightLineGeometry R hg hgenus)
    (γ : ModularR) (hγ : ¬ IsOfFinOrder γ) (p : QCPointR) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    letI := R.compactSpace
    letI := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
    IsMinimizingPoint R γ p ↔
      ∃ ℓ : ℝ → QCPointR, Isometry ℓ ∧ p ∈ range ℓ ∧
        (fun q : QCPointR => γ • q) '' range ℓ = range ℓ := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
  have hnofix (q : QCPointR) : γ • q ≠ q := by
    intro hfix
    let S := MulAction.stabilizer ModularR q
    have hfinite : (S : Set ModularR).Finite := modular_stabilizer_finite R hg hgenus q
    let : Fintype S := hfinite.fintype
    let γS : S := ⟨γ, hfix⟩
    exact hγ (S.subtype.isOfFinOrder (isOfFinOrder_of_finite γS))
  constructor
  · intro hp
    exact exists_invariantLine_of_minimizingPoint_of_pos
      R hg hgenus hgeometry γ p hp (dist_pos.mpr (hnofix p).symm)
  · rintro ⟨ℓ, hℓ, hpℓ, hinvariant⟩
    rcases invariantLine_reflection_or_orbit_minimum
        R hg hgenus γ p ℓ hℓ hpℓ hinvariant with ⟨c, hc⟩ | ⟨_, hp⟩
    · have hfixed : γ • ℓ (c / 2) = ℓ (c / 2) := by
        rw [hc]
        congr 1
        ring
      exact False.elim (hnofix (ℓ (c / 2)) hfixed)
    · exact hp

end LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers
