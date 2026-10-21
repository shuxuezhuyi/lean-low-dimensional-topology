/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The subgroup maximum-height argument adapts `ModularGroup.exists_max_im`
from Mathlib/NumberTheory/Modular.lean, by Alex Kontorovich, Heather Macbeth
and Marc Masdeu. The remaining concrete polygon proofs are original here.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ConvexBoundaryMateCriterion
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
public import LowDimensionalTopology.Geometry.Fuchsian.Examples.PrimitiveSimpleHyperbolicExample
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.PingPong
public import LowDimensionalTopology.Geometry.Fuchsian.GeometricFiniteness.SplitLimitPolygons
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeMultiplicityPunctures

/-!
# Infinitely many sides in one polygon edge

Explicit integral matrices pair a locally finite family of semicircles. Their
ping-pong domains give a discrete group and a fundamental base region. A window
reassembly produces a convex locally finite polygon with infinitely many distinct
closed-tile intersections along one boundary geodesic.

The final distinction concerns actual sides and edges of this same polygon.
Its group is non-elementary and is not finitely generated.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Explicit real matrices for the paired semicircles. -/
def infiniteSideSL (c : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![-c,c^2-1;1,-c], by
    norm_num [Matrix.det_fin_two]
    ring⟩

def infiniteSideCenter (n : ℕ) : ℝ := 4*n+2

def infiniteSideCircleQ (a : ℝ) (z : ℍ) : ℝ :=
  Complex.normSq ((z : ℂ)-(a : ℂ))

theorem infiniteSideCircleQ_coordinates (a : ℝ) (z : ℍ) :
    infiniteSideCircleQ a z = (z.re-a)^2+z.im^2 := by
  simp only [infiniteSideCircleQ, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

theorem infiniteSideSL_coe (c : ℝ) (z : ℍ) :
    ((infiniteSideSL c • z : ℍ) : ℂ) = -(c : ℂ)-1/((z : ℂ)-(c : ℂ)) := by
  have hd : (z : ℂ)-(c : ℂ) ≠ 0 := by
    intro he
    have h := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero,
      UpperHalfPlane.coe_im, Complex.zero_im] at h
    exact z.im_ne_zero h
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [infiniteSideSL, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Algebra.algebraMap_self_apply,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_sub, Complex.ofReal_pow,
    one_mul, ←sub_eq_add_neg]
  field_simp
  ring

theorem infiniteSideSL_circle_identity (c : ℝ) (z : ℍ) :
    infiniteSideCircleQ (-c) (infiniteSideSL c • z) * infiniteSideCircleQ c z = 1 := by
  have hd : Complex.normSq ((z : ℂ)-(c : ℂ)) ≠ 0 := by
    apply ne_of_gt
    apply Complex.normSq_pos.mpr
    intro he
    have h := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero,
      UpperHalfPlane.coe_im, Complex.zero_im] at h
    exact z.im_ne_zero h
  rw [infiniteSideCircleQ, infiniteSideSL_coe]
  have he : -(c : ℂ)-1/((z : ℂ)-(c : ℂ))-((-c : ℝ) : ℂ) =
      -(1/((z : ℂ)-(c : ℂ))) := by push_cast; ring
  rw [he, Complex.normSq_neg, Complex.normSq_div, Complex.normSq_one]
  change (1/Complex.normSq ((z : ℂ)-(c : ℂ))) *
    Complex.normSq ((z : ℂ)-(c : ℂ)) = 1
  exact one_div_mul_cancel hd

theorem infiniteSideCircleQ_small_re (a : ℝ) (z : ℍ)
    (h : infiniteSideCircleQ a z ≤ 1) : a-1 < z.re ∧ z.re < a+1 := by
  rw [infiniteSideCircleQ_coordinates] at h
  have hy := sq_pos_of_pos z.im_pos
  constructor
  · nlinarith [sq_nonneg (z.re-a+1)]
  · nlinarith [sq_nonneg (z.re-a-1)]

theorem infiniteSideCircleQ_large_of_re (a : ℝ) (z : ℍ)
    (h : z.re ≤ a-1 ∨ a+1 ≤ z.re) : 1 < infiniteSideCircleQ a z := by
  rw [infiniteSideCircleQ_coordinates]
  have hy := sq_pos_of_pos z.im_pos
  rcases h with h | h
  · have hh := sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 0 ≤ a-z.re)
    have hs : (1 : ℝ)^2 ≤ (a-z.re)^2 := hh.mpr (by linarith)
    nlinarith
  · have hh := sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 0 ≤ z.re-a)
    have hs : (1 : ℝ)^2 ≤ (z.re-a)^2 := hh.mpr (by linarith)
    nlinarith

def infiniteSideSector (c : ℝ) : Set ℍ :=
  {z | 1 < infiniteSideCircleQ c z ∧ 1 < infiniteSideCircleQ (-c) z}

theorem infiniteSideSector_wandering (c : ℝ) (hc : 2 ≤ c) (g : ℍ ≃ᵢ ℍ)
    (hg : g ∈ Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL c))) (hne
      : g ≠ 1) :
    Disjoint (g • infiniteSideSector c) (infiniteSideSector c) := by
  apply torus_cyclic_sector_wandering (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL
    c)) (infiniteSideSector c)
    {z | infiniteSideCircleQ (-c) z < 1} {z | 1 < infiniteSideCircleQ c z}
    {z | infiniteSideCircleQ c z < 1} {z | 1 < infiniteSideCircleQ (-c) z}
    (fun _ hz => hz.1) _ _ (fun _ hz => hz.2) _ _ _ _ g hg hne
  · intro z hz
    have hx := infiniteSideCircleQ_small_re (-c) z hz.le
    exact infiniteSideCircleQ_large_of_re c z (Or.inl (by linarith))
  · intro z hz
    have hi := infiniteSideSL_circle_identity c z
    have hnonneg := Complex.normSq_nonneg (((infiniteSideSL c • z : ℍ) : ℂ)-((-c : ℝ) : ℂ))
    change 1 < infiniteSideCircleQ c z at hz
    change infiniteSideCircleQ (-c) (infiniteSideSL c • z) < 1
    by_contra! h
    nlinarith
  · intro z hz
    have hx := infiniteSideCircleQ_small_re c z hz.le
    exact infiniteSideCircleQ_large_of_re (-c) z (Or.inr (by linarith))
  · intro z hz
    let w := ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL c))⁻¹ : ℍ ≃ᵢ ℍ) z
    have hw : infiniteSideSL c • w = z := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL
      c)).apply_inv_self z
    have hi := infiniteSideSL_circle_identity c w
    rw [hw] at hi
    have hnonneg := Complex.normSq_nonneg ((w : ℂ)-(c : ℂ))
    change 1 < infiniteSideCircleQ (-c) z at hz
    change infiniteSideCircleQ c w < 1
    by_contra! h
    nlinarith
  · exact disjoint_left.mpr (fun z hz hd => (not_lt_of_ge hz.le) hd.2)
  · exact disjoint_left.mpr (fun z hz hd => (not_lt_of_ge hz.le) hd.1)

/-- Separated actual paired circles give the factor-cover condition. -/
theorem infiniteSideSector_cover_of_gap (a b : ℝ) (ha : 2 ≤ a) (hab : a+4 ≤ b) :
    infiniteSideSector a ∪ infiniteSideSector b = univ := by
  apply eq_univ_of_forall
  intro z
  by_cases hp : 1 < infiniteSideCircleQ a z
  · by_cases hn : 1 < infiniteSideCircleQ (-a) z
    · exact Or.inl ⟨hp,hn⟩
    · right
      have hx := infiniteSideCircleQ_small_re (-a) z (le_of_not_gt hn)
      exact ⟨infiniteSideCircleQ_large_of_re b z (Or.inl (by linarith)),
        infiniteSideCircleQ_large_of_re (-b) z (Or.inr (by linarith))⟩
  · right
    have hx := infiniteSideCircleQ_small_re a z (le_of_not_gt hp)
    exact ⟨infiniteSideCircleQ_large_of_re b z (Or.inl (by linarith)),
      infiniteSideCircleQ_large_of_re (-b) z (Or.inr (by linarith))⟩

theorem infiniteSideCenter_two_le (n : ℕ) : 2 ≤ infiniteSideCenter n := by
  dsimp only [infiniteSideCenter]
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem infiniteSideSector_cover (n m : ℕ) (hne : n ≠ m) :
    infiniteSideSector (infiniteSideCenter n) ∪
      infiniteSideSector (infiniteSideCenter m) = univ := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hh : (n : ℝ)+1 ≤ m := by exact_mod_cast h
    exact infiniteSideSector_cover_of_gap _ _ (infiniteSideCenter_two_le n)
      (by dsimp only [infiniteSideCenter]; linarith)
  · have hh : (m : ℝ)+1 ≤ n := by exact_mod_cast h
    rw [union_comm]
    exact infiniteSideSector_cover_of_gap _ _ (infiniteSideCenter_two_le m)
      (by dsimp only [infiniteSideCenter]; linarith)

/-- The existing free-product ping-pong theorem gives actual wandering for
the present infinite family; the conclusion concerns the whole generated group. -/
theorem native_packing_family_wandering {ι : Type*}
    (G : ι → Subgroup (ℍ ≃ᵢ ℍ)) (D : ι → Set ℍ)
    (hpack : ∀ i g, g ∈ G i → g ≠ 1 → Disjoint (g • D i) (D i))
    (hcover : ∀ i j, i ≠ j → D i ∪ D j = univ)
    (U : Set ℍ) (hU : ∀ i, U ⊆ D i)
    (g : ℍ ≃ᵢ ℍ) (hg : g ∈ ⨆ i, G i) (hne : g ≠ 1) :
    Disjoint (g • U) U := by
  classical
  let f : ∀ i, G i →* (ℍ ≃ᵢ ℍ) := fun i => (G i).subtype
  let A : ι → Set ℍ := fun i => (D i)ᶜ
  have hmove (i : ι) (k : G i) (hk : k ≠ 1) (x : ℍ) (hx : x ∈ D i) :
      (f i k) x ∉ D i := by
    have hk' : k.val ≠ 1 := fun he => hk (Subtype.ext he)
    exact fun hy => disjoint_left.mp (hpack i k.val k.property hk') ⟨x,hx,rfl⟩ hy
  have hpp : Pairwise fun i j => ∀ k : G i, k ≠ 1 → f i k • A j ⊆ A i := by
    intro i j hij k hk y hy
    obtain ⟨x,hx,rfl⟩ := hy
    have hxD : x ∈ D i := by
      have hh : x ∈ D i ∪ D j := by rw [hcover i j hij]; trivial
      exact hh.resolve_right hx
    exact hmove i k hk x hxD
  have hstart : ∀ i (k : G i), k ≠ 1 → f i k • U ⊆ A i := by
    rintro i k hk y ⟨x,hx,rfl⟩
    exact hmove i k hk x (hU i hx)
  have hgap : ∀ i, Disjoint (A i) U := fun i =>
    disjoint_left.mpr (fun _ hx hy => hx (hU i hy))
  have hgr : g ∈ (Monoid.CoprodI.lift f).range := by
    rw [Monoid.CoprodI.range_eq_iSup]
    simpa only [f,Subgroup.range_subtype] using hg
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.pingPong_range_wandering f A U hpp hstart hgap g hgr hne

def infiniteSideNativeGroup : Subgroup (ℍ ≃ᵢ ℍ) :=
  ⨆ n : ℕ, Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL
    (infiniteSideCenter n)))

def infiniteSideBase : Set ℍ := ⋂ n : ℕ, infiniteSideSector (infiniteSideCenter n)

theorem infiniteSideBase_wandering (g : ℍ ≃ᵢ ℍ) (hg : g ∈ infiniteSideNativeGroup)
    (hne : g ≠ 1) : Disjoint (g • infiniteSideBase) infiniteSideBase := by
  exact native_packing_family_wandering _ _
    (fun n => infiniteSideSector_wandering _ (infiniteSideCenter_two_le n))
    infiniteSideSector_cover infiniteSideBase (fun n => iInter_subset _ n) g hg hne

theorem infiniteSide_high_mem (a : ℝ) (z : ℍ) (hz : 2 < z.im) :
    1 < infiniteSideCircleQ a z := by
  rw [infiniteSideCircleQ_coordinates]
  nlinarith [sq_nonneg (z.re-a)]

theorem infiniteSideNativeGroup_discrete : DiscreteTopology infiniteSideNativeGroup := by
  let U : Set ℍ := {z | 2 < z.im}
  have hU : ∀ n, U ⊆ infiniteSideSector (infiniteSideCenter n) := by
    intro n z hz
    exact ⟨infiniteSide_high_mem _ z hz, infiniteSide_high_mem _ z hz⟩
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteTopology_of_wandering_open U
    (isOpen_lt continuous_const UpperHalfPlane.continuous_im)
    ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 3 (by norm_num), by change 2 < (3 : ℝ); norm_num⟩
  intro g hg
  exact native_packing_family_wandering _ _
    (fun n => infiniteSideSector_wandering _ (infiniteSideCenter_two_le n))
    infiniteSideSector_cover U hU g.val g.property (fun he => hg (Subtype.ext he))

theorem infiniteSideNativeGroup_conformal : infiniteSideNativeGroup ≤
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  apply iSup_le
  intro n
  exact Subgroup.zpowers_le.mpr ⟨infiniteSideSL (infiniteSideCenter n),rfl⟩

theorem infiniteSideNativeGroup_discontinuous : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous infiniteSideNativeGroup ℍ := by
  let : DiscreteTopology infiniteSideNativeGroup := infiniteSideNativeGroup_discrete
  exact nativeConformalSubgroup_discontinuous _ infiniteSideNativeGroup_conformal

end LowDimensionalTopology.Geometry.Fuchsian

open scoped MatrixGroups

namespace LowDimensionalTopology.Geometry.Fuchsian

/--
The actual orbit of any integral matrix subgroup contains a highest point.
This is the subgroup-restricted bottom-row argument for,
adapted from Mathlib's `ModularGroup.exists_max_im`.
-/
theorem integralSubgroup_exists_max_im (J : Subgroup SL(2, ℤ)) (z : ℍ) :
    ∃ g : J, ∀ g' : J, (g'.val • z).im ≤ (g.val • z).im := by
  let s : Set (Fin 2 → ℤ) := Set.range (fun g : J => g.val 1)
  have hs : s.Nonempty := ⟨(1 : SL(2, ℤ)) 1, ⟨1, rfl⟩⟩
  obtain ⟨p, hp, hmin⟩ := Filter.Tendsto.exists_within_forall_le hs
    (ModularGroup.tendsto_normSq_coprime_pair z)
  obtain ⟨g, hg⟩ := hp
  refine ⟨g, fun g' => ?_⟩
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.im_smul_eq_div_normSq,
    div_le_div_iff_of_pos_left]
  · simpa [← hg] using! hmin (g'.val 1) ⟨g', rfl⟩
  · exact z.im_pos
  · exact UpperHalfPlane.normSq_denom_pos g'.val z.im_ne_zero
  · exact UpperHalfPlane.normSq_denom_pos g.val z.im_ne_zero

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian

open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The displayed paired-circle matrices are genuine integral matrices. -/
def infiniteSideIntegralSL (c : ℤ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![-c, c ^ 2 - 1; 1, -c], by
    norm_num [Matrix.det_fin_two]
    ring⟩

theorem infiniteSideIntegralSL_map (c : ℤ) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (infiniteSideIntegralSL c) =
      infiniteSideSL (c : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [infiniteSideIntegralSL, infiniteSideSL, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply]

theorem infiniteSideIntegralSL_native (c : ℤ) :
    modularNativeHom (infiniteSideIntegralSL c) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (c : ℝ)) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (Matrix.SpecialLinearGroup.map (Int.castRingHom
    ℝ)
    (infiniteSideIntegralSL c)) = _
  rw [infiniteSideIntegralSL_map]

theorem infiniteSideNativeGroup_le_integral :
    infiniteSideNativeGroup ≤ modularNativeHom.range := by
  apply iSup_le
  intro n
  apply Subgroup.zpowers_le.mpr
  refine ⟨infiniteSideIntegralSL (4 * (n : ℤ) + 2), ?_⟩
  rw [infiniteSideIntegralSL_native]
  congr 2
  simp [infiniteSideCenter]

theorem infiniteSideNativeGroup_exists_max_im (z : ℍ) :
    ∃ g : infiniteSideNativeGroup, ∀ h : infiniteSideNativeGroup,
      (h.val z).im ≤ (g.val z).im := by
  let J := infiniteSideNativeGroup.comap modularNativeHom
  obtain ⟨a, ha⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.integralSubgroup_exists_max_im J z
  refine ⟨⟨modularNativeHom a.val, a.property⟩, fun h => ?_⟩
  obtain ⟨b, hb⟩ := infiniteSideNativeGroup_le_integral h.property
  let b' : J := ⟨b, by
    change modularNativeHom b ∈ infiniteSideNativeGroup
    rw [hb]
    exact h.property⟩
  change (h.val z).im ≤ (modularNativeHom a.val z).im
  rw [← hb, modularNativeHom_apply, modularNativeHom_apply]
  exact ha b'

theorem infiniteSideCircleQ_pos (c : ℝ) (z : ℍ) : 0 < infiniteSideCircleQ c z := by
  rw [infiniteSideCircleQ_coordinates]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos z.im_pos)

theorem infiniteSideSL_im (c : ℝ) (z : ℍ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL c) z).im = z.im / infiniteSideCircleQ c z := by
  change (((infiniteSideSL c • z : ℍ) : ℂ)).im = _
  rw [infiniteSideSL_coe]
  simp [infiniteSideCircleQ]
  ring

theorem infiniteSideSL_inv_im (c : ℝ) (z : ℍ) :
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL c))⁻¹ z).im =
      z.im / infiniteSideCircleQ (-c) z := by
  let w := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL c))⁻¹ z
  have hw : infiniteSideSL c • w = z :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL c)).apply_inv_self z
  have him := infiniteSideSL_im c w
  change (infiniteSideSL c • w).im = _ at him
  rw [hw] at him
  have hc := infiniteSideSL_circle_identity c w
  rw [hw] at hc
  have he : w.im = z.im * infiniteSideCircleQ c w :=
    ((div_eq_iff (infiniteSideCircleQ_pos c w).ne').mp him.symm)
  change w.im = _
  apply (eq_div_iff (infiniteSideCircleQ_pos (-c) z).ne').mpr
  rw [he]
  calc
    (z.im * infiniteSideCircleQ c w) * infiniteSideCircleQ (-c) z =
        z.im * (infiniteSideCircleQ (-c) z * infiniteSideCircleQ c w) := by ring
    _ = z.im := by rw [hc, mul_one]

/-- Each genuine group orbit reaches the simultaneous closed exterior of all paired circles. -/
theorem infiniteSide_closed_base_meets_every_orbit (z : ℍ) :
    ∃ g : infiniteSideNativeGroup, ∀ n : ℕ,
      1 ≤ infiniteSideCircleQ (infiniteSideCenter n) (g.val z) ∧
        1 ≤ infiniteSideCircleQ (-infiniteSideCenter n) (g.val z) := by
  obtain ⟨g, hg⟩ := infiniteSideNativeGroup_exists_max_im z
  refine ⟨g, fun n => ?_⟩
  let k := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n))
  have hk : k ∈ infiniteSideNativeGroup :=
    (le_iSup (fun m : ℕ => Subgroup.zpowers
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
        m)))) n) (Subgroup.mem_zpowers k)
  have hf := hg (⟨k, hk⟩ * g)
  have hi := hg (⟨k⁻¹, infiniteSideNativeGroup.inv_mem hk⟩ * g)
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)) (g.val
    z)).im ≤
    (g.val z).im at hf
  change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)))⁻¹
    (g.val z)).im ≤
    (g.val z).im at hi
  rw [infiniteSideSL_im] at hf
  rw [infiniteSideSL_inv_im] at hi
  have hf' := (div_le_iff₀ (infiniteSideCircleQ_pos (infiniteSideCenter n) (g.val z))).mp hf
  have hi' := (div_le_iff₀ (infiniteSideCircleQ_pos (-infiniteSideCenter n) (g.val z))).mp hi
  constructor <;> nlinarith [(g.val z).im_pos]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian

open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open Filter MeasureTheory

theorem infiniteSideBase_mem_iff (z : ℍ) : z ∈ infiniteSideBase ↔
    ∀ n : ℕ, 1 < infiniteSideCircleQ (infiniteSideCenter n) z ∧
      1 < infiniteSideCircleQ (-infiniteSideCenter n) z := by
  simp only [infiniteSideBase, mem_iInter, infiniteSideSector, mem_ofPred_eq]

theorem infiniteSideCircleQ_continuous (c : ℝ) : Continuous (infiniteSideCircleQ c) := by
  unfold infiniteSideCircleQ
  fun_prop

/-- The actual family of circles escapes every bounded real-coordinate strip. -/
theorem infiniteSideBase_isOpen : IsOpen infiniteSideBase := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hz' := (infiniteSideBase_mem_iff z).mp hz
  obtain ⟨N, hN⟩ := exists_nat_gt (|z.re| + 2)
  have hB : {w : ℍ | -(N : ℝ) < w.re ∧ w.re < N} ∈ 𝓝 z := by
    have hl : -(N : ℝ) < z.re := by linarith [neg_abs_le z.re]
    have hr : z.re < N := by linarith [le_abs_self z.re]
    exact Filter.inter_mem
      ((isOpen_lt continuous_const UpperHalfPlane.continuous_re).mem_nhds hl)
      ((isOpen_lt UpperHalfPlane.continuous_re continuous_const).mem_nhds hr)
  have hF : ∀ᶠ w in 𝓝 z, ∀ n : Fin N,
      1 < infiniteSideCircleQ (infiniteSideCenter n.val) w ∧
        1 < infiniteSideCircleQ (-infiniteSideCenter n.val) w := by
    apply Filter.eventually_all.mpr
    intro n
    exact ((isOpen_lt continuous_const (infiniteSideCircleQ_continuous _)).inter
      (isOpen_lt continuous_const (infiniteSideCircleQ_continuous _))).mem_nhds (hz' n.val)
  filter_upwards [hB, hF] with w hw hf
  rw [infiniteSideBase_mem_iff]
  intro n
  by_cases hn : n < N
  · exact hf ⟨n, hn⟩
  · have hnr : (N : ℝ) ≤ n := by exact_mod_cast Nat.le_of_not_gt hn
    constructor
    · exact infiniteSideCircleQ_large_of_re _ w (Or.inl (by
        dsimp only [infiniteSideCenter]
        linarith [Nat.cast_nonneg (α := ℝ) n]))
    · exact infiniteSideCircleQ_large_of_re _ w (Or.inr (by
        dsimp only [infiniteSideCenter]
        linarith [Nat.cast_nonneg (α := ℝ) n]))

def infiniteSideSignedCenter (i : ℕ × Bool) : ℝ :=
  if i.2 then infiniteSideCenter i.1 else -infiniteSideCenter i.1

def infiniteSideNormals (i : ℕ × Bool) : ℂ :=
  torusCircleNormal (infiniteSideSignedCenter i - 1) (infiniteSideSignedCenter i + 1)

def infiniteSideThresholds (i : ℕ × Bool) : ℝ :=
  torusCircleThreshold (infiniteSideSignedCenter i - 1) (infiniteSideSignedCenter i + 1)

theorem infiniteSideCircleQ_slack (c : ℝ) (z : ℍ) :
    torusCircleQ (c - 1) (c + 1) z = infiniteSideCircleQ c z - 1 := by
  rw [infiniteSideCircleQ_coordinates]
  simp only [torusCircleQ, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

theorem infiniteSideBase_klein : infiniteSideBase =
    torusKleinCutRegion infiniteSideNormals infiniteSideThresholds := by
  ext z
  rw [infiniteSideBase_mem_iff]
  constructor
  · intro hz i
    apply (torusCircleQ_klein_pos_iff _ _ z).mp
    rw [infiniteSideCircleQ_slack]
    have hp : 1 < infiniteSideCircleQ (infiniteSideSignedCenter i) z := by
      rcases i with ⟨n, b⟩
      cases b
      · exact (hz n).2
      · exact (hz n).1
    linarith
  · intro hz n
    have hp := (torusCircleQ_klein_pos_iff _ _ z).mpr (hz (n, true))
    have hm := (torusCircleQ_klein_pos_iff _ _ z).mpr (hz (n, false))
    rw [infiniteSideCircleQ_slack] at hp hm
    change 0 < infiniteSideCircleQ (infiniteSideCenter n) z - 1 at hp
    change 0 < infiniteSideCircleQ (-infiniteSideCenter n) z - 1 at hm
    exact ⟨by linarith, by linarith⟩

theorem infiniteSideBase_hConvex : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex infiniteSideBase := by
  rw [infiniteSideBase_klein]
  exact torusKleinCutRegion_hConvex _ _

theorem infiniteSideBase_high_mem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 3 (by norm_num) ∈ infiniteSideBase := by
  rw [infiniteSideBase_mem_iff]
  intro n
  exact ⟨infiniteSide_high_mem _ _ (by norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]),
    infiniteSide_high_mem _ _ (by norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe])⟩

theorem infiniteSideBase_isConnected : IsConnected infiniteSideBase :=
  ⟨⟨_, infiniteSideBase_high_mem⟩, infiniteSideBase_hConvex.isPreconnected⟩

theorem infiniteSideBase_closure : closure infiniteSideBase =
    {z : ℍ | ∀ n : ℕ, 1 ≤ infiniteSideCircleQ (infiniteSideCenter n) z ∧
      1 ≤ infiniteSideCircleQ (-infiniteSideCenter n) z} := by
  have he : closure infiniteSideBase =
      torusKleinClosedRegion infiniteSideNormals infiniteSideThresholds := by
    rw [infiniteSideBase_klein]
    exact torusKleinCutRegion_closure _ _ _
      (infiniteSideBase_klein ▸ infiniteSideBase_high_mem)
  rw [he]
  ext z
  constructor
  · intro hz n
    have hp := (torusCircleQ_klein_nonneg_iff _ _ z).mpr (hz (n, true))
    have hm := (torusCircleQ_klein_nonneg_iff _ _ z).mpr (hz (n, false))
    rw [infiniteSideCircleQ_slack] at hp hm
    change 0 ≤ infiniteSideCircleQ (infiniteSideCenter n) z - 1 at hp
    change 0 ≤ infiniteSideCircleQ (-infiniteSideCenter n) z - 1 at hm
    exact ⟨by linarith, by linarith⟩
  · intro hz i
    apply (torusCircleQ_klein_nonneg_iff _ _ z).mp
    rw [infiniteSideCircleQ_slack]
    have hp : 1 ≤ infiniteSideCircleQ (infiniteSideSignedCenter i) z := by
      rcases i with ⟨n, b⟩
      cases b
      · exact (hz n).2
      · exact (hz n).1
    linarith

theorem infiniteSideBase_frontier_null : volume (frontier infiniteSideBase) = 0 := by
  have hnull (c : ℝ) : volume {z : ℍ | infiniteSideCircleQ c z = 1} = 0 := by
    have he : {z : ℍ | infiniteSideCircleQ c z = 1} =
        {z : ℍ | torusCircleQ (c - 1) (c + 1) z = 0} := by
      ext z
      change infiniteSideCircleQ c z = 1 ↔ torusCircleQ (c - 1) (c + 1) z = 0
      rw [infiniteSideCircleQ_slack]
      constructor <;> intro h <;> linarith
    rw [he]
    exact torusCircleQ_zero_null _ _ (by linarith)
  apply measure_mono_null (t := ⋃ n : ℕ,
    ({z : ℍ | infiniteSideCircleQ (infiniteSideCenter n) z = 1} ∪
      {z : ℍ | infiniteSideCircleQ (-infiniteSideCenter n) z = 1}))
  · intro z hz
    have hc := hz.1
    rw [infiniteSideBase_closure] at hc
    have hn : z ∉ infiniteSideBase := by
      simpa only [infiniteSideBase_isOpen.interior_eq] using hz.2
    have hex : ∃ n : ℕ, infiniteSideCircleQ (infiniteSideCenter n) z = 1 ∨
        infiniteSideCircleQ (-infiniteSideCenter n) z = 1 := by
      by_contra hh
      apply hn
      rw [infiniteSideBase_mem_iff]
      intro n
      constructor
      · exact lt_of_le_of_ne (hc n).1 (fun h => hh ⟨n, Or.inl h.symm⟩)
      · exact lt_of_le_of_ne (hc n).2 (fun h => hh ⟨n, Or.inr h.symm⟩)
    obtain ⟨n, hn⟩ := hex
    exact mem_iUnion.mpr ⟨n, hn⟩
  · exact measure_iUnion_null (fun n => measure_union_null (hnull _) (hnull _))

theorem infiniteSideBase_closure_meetsEveryOrbit :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit infiniteSideNativeGroup ℍ (closure infiniteSideBase) := by
  intro z
  obtain ⟨g, hg⟩ := infiniteSide_closed_base_meets_every_orbit z
  refine ⟨g, ?_⟩
  rw [infiniteSideBase_closure]
  exact hg

/-- The genuine infinite paired-circle base is a fundamental domain for the whole group. -/
theorem infiniteSideBase_fundamental :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain infiniteSideNativeGroup ℍ volume infiniteSideBase := by
  refine ⟨infiniteSideBase_isOpen, infiniteSideBase_isConnected, ?_, infiniteSideBase_frontier_null⟩
  apply exists_fundamentalSet_between _ _ subset_closure infiniteSideBase_closure_meetsEveryOrbit
  intro x hx y hy hxy
  obtain ⟨g, hg⟩ := (Quotient.exact hxy : MulAction.orbitRel infiniteSideNativeGroup ℍ x y)
  change g.val y = x at hg
  by_cases he : g.val = 1
  · rw [he] at hg
    exact hg.symm
  · exact False.elim (Set.disjoint_left.mp (infiniteSideBase_wandering g.val g.property he)
      ⟨y, hy, hg⟩ hx)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian

open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open Filter MeasureTheory

/-- The distinct displayed signed circle centers are separated by at least four. -/
theorem infiniteSideSignedCenter_gap (i j : ℕ × Bool) (hne : i ≠ j) :
    infiniteSideSignedCenter i + 4 ≤ infiniteSideSignedCenter j ∨
      infiniteSideSignedCenter j + 4 ≤ infiniteSideSignedCenter i := by
  rcases i with ⟨n, b⟩
  rcases j with ⟨m, d⟩
  have hcN := infiniteSideCenter_two_le n
  have hcM := infiniteSideCenter_two_le m
  cases b <;> cases d
  · have hnm : n ≠ m := by intro h; subst m; exact hne rfl
    rcases lt_or_gt_of_ne hnm with h | h
    · right
      have hh : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
      change -infiniteSideCenter m + 4 ≤ -infiniteSideCenter n
      dsimp only [infiniteSideCenter]
      linarith
    · left
      have hh : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
      change -infiniteSideCenter n + 4 ≤ -infiniteSideCenter m
      dsimp only [infiniteSideCenter]
      linarith
  · left
    change -infiniteSideCenter n + 4 ≤ infiniteSideCenter m
    linarith
  · right
    change -infiniteSideCenter m + 4 ≤ infiniteSideCenter n
    linarith
  · have hnm : n ≠ m := by intro h; subst m; exact hne rfl
    rcases lt_or_gt_of_ne hnm with h | h
    · left
      have hh : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
      change infiniteSideCenter n + 4 ≤ infiniteSideCenter m
      dsimp only [infiniteSideCenter]
      linarith
    · right
      have hh : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
      change infiniteSideCenter m + 4 ≤ infiniteSideCenter n
      dsimp only [infiniteSideCenter]
      linarith

theorem infiniteSide_circle_boundary_other (i j : ℕ × Bool) (hne : i ≠ j)
    (z : ℍ) (hz : infiniteSideCircleQ (infiniteSideSignedCenter i) z = 1) :
    1 < infiniteSideCircleQ (infiniteSideSignedCenter j) z := by
  have hx := infiniteSideCircleQ_small_re _ z hz.le
  rcases infiniteSideSignedCenter_gap i j hne with h | h
  · exact infiniteSideCircleQ_large_of_re _ z (Or.inl (by linarith))
  · exact infiniteSideCircleQ_large_of_re _ z (Or.inr (by linarith))

theorem infiniteSide_circle_boundary_frontier (i : ℕ × Bool) (z : ℍ)
    (hz : infiniteSideCircleQ (infiniteSideSignedCenter i) z = 1) :
    z ∈ frontier infiniteSideBase := by
  have hw (j : ℕ × Bool) : 1 ≤ infiniteSideCircleQ (infiniteSideSignedCenter j) z := by
    by_cases he : i = j
    · simpa only [← he, hz] using (le_rfl : (1 : ℝ) ≤ 1)
    · exact (infiniteSide_circle_boundary_other i j he z hz).le
  refine ⟨?_, ?_⟩
  · rw [infiniteSideBase_closure]
    intro n
    exact ⟨hw (n, true), hw (n, false)⟩
  · rw [infiniteSideBase_isOpen.interior_eq]
    intro hm
    have h := (infiniteSideBase_mem_iff z).mp hm i.1
    have hh : 1 < infiniteSideCircleQ (infiniteSideSignedCenter i) z := by
      rcases i with ⟨n, b⟩
      cases b
      · exact h.2
      · exact h.1
    rw [hz] at hh
    exact hh.false

theorem infiniteSideBase_frontier_circle (x : ℍ) (hx : x ∈ frontier infiniteSideBase) :
    ∃ i : ℕ × Bool, infiniteSideCircleQ (infiniteSideSignedCenter i) x = 1 := by
  have hc := hx.1
  rw [infiniteSideBase_closure] at hc
  have hn : x ∉ infiniteSideBase := by
    simpa only [infiniteSideBase_isOpen.interior_eq] using hx.2
  by_contra he
  apply hn
  rw [infiniteSideBase_mem_iff]
  intro n
  constructor
  · exact lt_of_le_of_ne (hc n).1 (fun h => he ⟨(n, true), h.symm⟩)
  · exact lt_of_le_of_ne (hc n).2 (fun h => he ⟨(n, false), h.symm⟩)

theorem infiniteSide_generator_ne_one (n : ℕ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)) ≠ 1 := by
  intro he
  have h := infiniteSideSL_circle_identity (infiniteSideCenter n) UpperHalfPlane.I
  change infiniteSideCircleQ (-infiniteSideCenter n)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n))
      UpperHalfPlane.I) *
      infiniteSideCircleQ (infiniteSideCenter n) UpperHalfPlane.I = 1 at h
  rw [he] at h
  norm_num [infiniteSideCircleQ_coordinates, UpperHalfPlane.I] at h
  nlinarith [infiniteSideCenter_two_le n]

/-- Every true base boundary point has a genuine paired point on the same full base boundary. -/
theorem infiniteSideBase_boundary_mates_native (x : ℍ) (hx : x ∈ frontier infiniteSideBase) :
    ∃ g : infiniteSideNativeGroup, g ≠ 1 ∧ g.val x ∈ frontier infiniteSideBase := by
  obtain ⟨⟨n, b⟩, hb⟩ := infiniteSideBase_frontier_circle x hx
  let k := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n))
  have hk : k ∈ infiniteSideNativeGroup :=
    (le_iSup (fun m : ℕ => Subgroup.zpowers
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
        m)))) n) (Subgroup.mem_zpowers k)
  have hk1 : k ≠ 1 := infiniteSide_generator_ne_one n
  cases b
  · refine ⟨⟨k⁻¹, infiniteSideNativeGroup.inv_mem hk⟩, ?_, ?_⟩
    · exact fun he => (inv_ne_one.mpr hk1) (congrArg Subtype.val he)
    · apply infiniteSide_circle_boundary_frontier (n, true)
      have h := infiniteSideSL_circle_identity (infiniteSideCenter n) (k⁻¹ x)
      have hback : infiniteSideSL (infiniteSideCenter n) • (k⁻¹ x) = x := k.apply_inv_self x
      rw [hback] at h
      change infiniteSideCircleQ (-infiniteSideCenter n) x = 1 at hb
      rw [hb, one_mul] at h
      exact h
  · refine ⟨⟨k, hk⟩, ?_, ?_⟩
    · exact fun he => hk1 (congrArg Subtype.val he)
    · apply infiniteSide_circle_boundary_frontier (n, false)
      have h := infiniteSideSL_circle_identity (infiniteSideCenter n) x
      change infiniteSideCircleQ (infiniteSideCenter n) x = 1 at hb
      rw [hb, mul_one] at h
      exact h

/-- The actual whole original Mobius group, obtained from the entire generated native group. -/
def infiniteSideGroup : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  (nativeConformalSubgroupMobiusHom infiniteSideNativeGroup infiniteSideNativeGroup_conformal).range

theorem infiniteSideData : HalfPlaneFuchsianGroup infiniteSideGroup := by
  let : DiscreteTopology infiniteSideNativeGroup := infiniteSideNativeGroup_discrete
  exact nativeConformalSubgroup_halfPlaneData _ infiniteSideNativeGroup_conformal

def infiniteSideNativeOriginalEquiv : infiniteSideNativeGroup ≃* infiniteSideGroup :=
  MonoidHom.ofInjective (nativeConformalSubgroupMobiusHom_isometry infiniteSideNativeGroup
    infiniteSideNativeGroup_conformal).injective

theorem infiniteSideNativeOriginalEquiv_action (g : infiniteSideNativeGroup) (z : ℍ) :
    let := infiniteSideData.nativeAction
    infiniteSideNativeOriginalEquiv g • z = g.val z := by
  let := infiniteSideData.nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  rw [← infiniteSideData.nativeAction_boundary]
  exact nativeConformalSubgroupMobiusHom_action infiniteSideNativeGroup infiniteSideNativeGroup_conformal g z

theorem infiniteSideBase_original_fundamental :
    let := infiniteSideData.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain infiniteSideGroup ℍ volume infiniteSideBase := by
  let := infiniteSideData.nativeAction
  have he (g : infiniteSideGroup) (z : ℍ) :
      (Homeomorph.refl ℍ) (g • z) =
        infiniteSideNativeOriginalEquiv.symm g • (Homeomorph.refl ℍ) z := by
    change g • z = (infiniteSideNativeOriginalEquiv.symm g).val z
    have h := infiniteSideNativeOriginalEquiv_action (infiniteSideNativeOriginalEquiv.symm g) z
    rwa [infiniteSideNativeOriginalEquiv.apply_symm_apply] at h
  simpa using _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage infiniteSideNativeOriginalEquiv.symm
    (Homeomorph.refl ℍ) he infiniteSideBase_fundamental

def infiniteSideCayleyGroupEquiv : infiniteSideNativeGroup ≃*
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius infiniteSideGroup :=
  infiniteSideNativeOriginalEquiv.trans (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius infiniteSideGroup)

theorem infiniteSideCayley_equivariant (g : infiniteSideNativeGroup) (z : ℍ) :
    infiniteSideData.cayleyCoordinate (g.val z) =
      infiniteSideCayleyGroupEquiv g • infiniteSideData.cayleyCoordinate z := by
  have h := infiniteSideData.cayleyCoordinate_equivariant (infiniteSideNativeOriginalEquiv g) z
  rw [infiniteSideNativeOriginalEquiv_action] at h
  exact h

theorem infiniteSideBase_cayley_locallyFinite :
    IsLocallyFiniteFuchsianDomain infiniteSideData.cayleyData
      (infiniteSideData.cayleyCoordinate '' infiniteSideBase) := by
  apply (convex_fundamentalDomain_locallyFinite_iff_boundary_mates _ _
    (infiniteSideData.cayley_fundamental infiniteSideBase_original_fundamental)
    (infiniteSideData.cayley_convex infiniteSideBase_hConvex)).mpr
  intro x hx
  let F := infiniteSideData.cayleyCoordinate
  have hx' : F.symm x ∈ frontier infiniteSideBase := by
    rw [← F.image_frontier] at hx
    obtain ⟨z, hz, he⟩ := hx
    rwa [← he, F.symm_apply_apply]
  obtain ⟨g, hg1, hgm⟩ := infiniteSideBase_boundary_mates_native (F.symm x) hx'
  refine ⟨infiniteSideCayleyGroupEquiv g, ?_, ?_⟩
  · exact fun he => hg1 (infiniteSideCayleyGroupEquiv.injective
      (he.trans infiniteSideCayleyGroupEquiv.map_one.symm))
  · rw [← F.apply_symm_apply x, ← infiniteSideCayley_equivariant]
    rw [← F.image_frontier]
    exact mem_image_of_mem F hgm

theorem infiniteSideBase_native_compact_hits (K : Set ℍ) (hK : IsCompact K) :
    {g : infiniteSideNativeGroup | (g.val '' closure infiniteSideBase ∩ K).Nonempty}.Finite := by
  let F := infiniteSideData.cayleyCoordinate
  let E := infiniteSideCayleyGroupEquiv
  have hf := infiniteSideBase_cayley_locallyFinite.compact_hits_finite (F '' K)
    (hK.image F.continuous)
  apply (hf.preimage E.injective.injOn).subset
  rintro g ⟨x, ⟨y, hy, hgy⟩, hx⟩
  refine ⟨F x, ?_, mem_image_of_mem F hx⟩
  refine ⟨F y, ?_, ?_⟩
  · rw [← F.image_closure]
    exact mem_image_of_mem F hy
  · change infiniteSideCayleyGroupEquiv g • infiniteSideData.cayleyCoordinate y =
      infiniteSideData.cayleyCoordinate x
    rw [← infiniteSideCayley_equivariant, hgy]

theorem infiniteSideBase_native_locallyFinite :
    LocallyFinite (fun g : infiniteSideNativeGroup => g.val '' closure infiniteSideBase) := by
  intro x
  obtain ⟨K, hK, hx⟩ := exists_compact_mem_nhds x
  exact ⟨K, hx, infiniteSideBase_native_compact_hits K hK⟩

theorem infiniteSideBase_original_locallyFinite :
    let := infiniteSideData.nativeAction
    LocallyFinite (fun g : infiniteSideGroup => g • closure infiniteSideBase) := by
  let := infiniteSideData.nativeAction
  apply infiniteSideNativeOriginalEquiv.toEquiv.locallyFinite_comp_iff.mp
  change LocallyFinite (fun g : infiniteSideNativeGroup =>
    infiniteSideNativeOriginalEquiv g • closure infiniteSideBase)
  have he (g : infiniteSideNativeGroup) :
      infiniteSideNativeOriginalEquiv g • closure infiniteSideBase =
        g.val '' closure infiniteSideBase := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, (infiniteSideNativeOriginalEquiv_action g y).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, infiniteSideNativeOriginalEquiv_action g y⟩
  simpa only [he] using infiniteSideBase_native_locallyFinite

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
/-- Packing for the actual infinite reassembly. -/
local instance infiniteSideGenericEvaluationAction {X : Type*} [MetricSpace X] :
    MulAction (X ≃ᵢ X) X where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem indexed_reassembly_wandering {X κ : Type*} [MetricSpace X]
    (H : Subgroup (X ≃ᵢ X)) (D : Set X) (P : κ → Set X) (L : κ → X ≃ᵢ X)
    (hPD : ∀ j, P j ⊆ D) (hunique : ∀ j k x, x ∈ P j → x ∈ P k → j = k)
    (hL : ∀ j, L j ∈ H) (hpack : ∀ h ∈ H, h ≠ 1 → Disjoint (h • D) D)
    (h : X ≃ᵢ X) (hh : h ∈ H) (hne : h ≠ 1) :
    Disjoint (h • ⋃ j, L j '' P j) (⋃ j, L j '' P j) := by
  have huniq (k : X ≃ᵢ X) (hk : k ∈ H) (x y : X)
      (hx : x ∈ D) (hy : y ∈ D) (hxy : k x = y) : k = 1 ∧ x = y := by
    by_cases he : k = 1
    · refine ⟨he, ?_⟩
      subst k
      exact hxy
    · exact False.elim (disjoint_left.mp (hpack k hk he) ⟨x, hx, hxy⟩ hy)
  apply disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ hy
  obtain ⟨j, a, ha, rfl⟩ := mem_iUnion.mp hx
  obtain ⟨k, b, hb, he⟩ := mem_iUnion.mp hy
  let l := L k
  let r := L j
  have hkl : (l⁻¹ * h * r) a = b := by
    change l.symm (h (r a)) = b
    change l b = h (r a) at he
    exact (congrArg l.symm he).symm.trans (l.symm_apply_apply b)
  have hu := huniq (l⁻¹ * h * r) (H.mul_mem (H.mul_mem (H.inv_mem (hL k)) hh) (hL j))
    a b (hPD j ha) (hPD k hb) hkl
  have hjk := hunique j k a ha (hu.2.symm ▸ hb)
  subst k
  apply hne
  calc
    h = r * (l⁻¹ * h * r) * r⁻¹ := by change h = r * (r⁻¹ * h * r) * r⁻¹; group
    _ = 1 := by rw [hu.1]; group


end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
/-- The actual open right-hand annular pieces. -/
def infiniteSideRightWindow (c : ℝ) : Set ℍ :=
  {z | 0 < z.re ∧ (c-2)^2 < Complex.normSq (z:ℂ) ∧
    Complex.normSq (z:ℂ) < (c+2)^2}

def infiniteSideWindowNormals (c : ℝ) : Fin 3 → ℂ :=
  ![-torusVerticalNormal 0, torusCircleNormal (-(c-2)) (c-2),
    -torusCircleNormal (-(c+2)) (c+2)]

def infiniteSideWindowThresholds (c : ℝ) : Fin 3 → ℝ :=
  ![0, torusCircleThreshold (-(c-2)) (c-2),
    -torusCircleThreshold (-(c+2)) (c+2)]

theorem infiniteSide_circleQ_origin (r : ℝ) (z : ℍ) :
    torusCircleQ (-r) r z = Complex.normSq (z:ℂ)-r^2 := by
  unfold torusCircleQ
  ring

theorem infiniteSideRightWindow_klein (c : ℝ) :
    infiniteSideRightWindow c =
      torusKleinCutRegion (infiniteSideWindowNormals c)
        (infiniteSideWindowThresholds c) := by
  ext z
  change (0 < z.re ∧ (c-2)^2 < Complex.normSq (z:ℂ) ∧
    Complex.normSq (z:ℂ) < (c+2)^2) ↔ _
  constructor
  · rintro ⟨hx,hi,ho⟩ i
    fin_cases i
    · change inner ℝ (-torusVerticalNormal
      0) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) < 0
      simpa using (torusVertical_klein_gt 0 z).mp hx
    · exact (torusCircleQ_klein_pos_iff _ _ z).mp (by
        rw [infiniteSide_circleQ_origin]
        linarith)
    · exact (torusCircleQ_klein_neg_iff _ _ z).mp (by
        rw [infiniteSide_circleQ_origin]
        linarith)
  · intro h
    have h0 := h (0:Fin 3)
    have h1 := h (1:Fin 3)
    have h2 := h (2:Fin 3)
    change inner ℝ (-torusVerticalNormal 0) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
      z) < 0 at h0
    have hx : 0 < z.re := (torusVertical_klein_gt 0 z).mpr (by simpa using h0)
    have hi := (torusCircleQ_klein_pos_iff (-(c-2)) (c-2) z).mpr h1
    have ho := (torusCircleQ_klein_neg_iff (-(c+2)) (c+2) z).mpr h2
    rw [infiniteSide_circleQ_origin] at hi ho
    exact ⟨hx,by linarith,by linarith⟩

theorem infiniteSideRightWindow_isOpen (c : ℝ) : IsOpen (infiniteSideRightWindow c) := by
  rw [infiniteSideRightWindow_klein]
  exact torusKleinCutRegion_isOpen _ _

theorem infiniteSideRightWindow_hConvex (c : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (infiniteSideRightWindow c) := by
  rw [infiniteSideRightWindow_klein]
  exact torusKleinCutRegion_hConvex _ _

/-- The modified polygon is an intersection of literal geodesic half-planes
in the original upper half-plane. -/
def infiniteSidePolygon : Set ℍ :=
  {z | z.re < 0 ∧ ∀ n : ℕ,
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)))⁻¹ z) ∈
      infiniteSideRightWindow (infiniteSideCenter n)}

theorem infiniteSidePolygon_hConvex : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex infiniteSidePolygon := by
  intro z hz w hw u hu
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hReCutLt_hConvex 0 z hz.1 w hw.1 hu,?_⟩
  intro n
  exact ((infiniteSideRightWindow_hConvex (infiniteSideCenter n)).isometry_preimage
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
      n)))⁻¹).isometry)
    z (hz.2 n) w (hw.2 n) hu

/-- A point in the paired positive disc lies strictly between the two
annular cutting geodesics. -/
theorem infiniteSideRightWindow_of_circle (c : ℝ) (hc : 2 ≤ c) (z : ℍ)
    (hz : infiniteSideCircleQ c z ≤ 1) : z ∈ infiniteSideRightWindow c := by
  have hx := infiniteSideCircleQ_small_re c z hz
  have hq := infiniteSideCircleQ_coordinates c z
  have hn : Complex.normSq (z:ℂ) = z.re^2+z.im^2 := by
    simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  refine ⟨by linarith,?_,?_⟩
  · rw [hn]
    have hp : 0 < (z.re-(c-2))*(z.re+(c-2)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [sq_pos_of_pos z.im_pos]
  · rw [hn]
    have hp : 0 < c*(c+1-z.re) := mul_pos (by linarith) (by linarith)
    nlinarith

theorem infiniteSide_inverse_window_of_exterior (c : ℝ) (hc : 2 ≤ c) (z : ℍ)
    (hz : 1 ≤ infiniteSideCircleQ (-c) z) :
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL c))⁻¹ z) ∈ infiniteSideRightWindow c := by
  let w := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL c))⁻¹ z
  have he : infiniteSideSL c • w = z :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL c)).apply_inv_self z
  have hi := infiniteSideSL_circle_identity c w
  rw [he] at hi
  apply infiniteSideRightWindow_of_circle c hc w
  have hn : 0 ≤ infiniteSideCircleQ c w := Complex.normSq_nonneg _
  nlinarith

theorem infiniteSidePolygon_isOpen : IsOpen infiniteSidePolygon := by
  apply isOpen_iff_forall_mem_open.mpr
  intro z hz
  obtain ⟨N,hN⟩ := exists_nat_gt (-z.re+3)
  let V : Set ℍ := {w | w.re < 0 ∧ z.re-1 < w.re} ∩
    ⋂ n : Fin N, (fun w : ℍ =>
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)))⁻¹) w) ⁻¹'
      infiniteSideRightWindow (infiniteSideCenter n)
  have hV : IsOpen V := by
    apply IsOpen.inter
    · exact (isOpen_lt UpperHalfPlane.continuous_re continuous_const).inter
        (isOpen_lt continuous_const UpperHalfPlane.continuous_re)
    · exact isOpen_iInter_of_finite (fun n =>
        (infiniteSideRightWindow_isOpen _).preimage
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
            n)))⁻¹).continuous)
  refine ⟨V,?_,hV,?_⟩
  · rintro w ⟨⟨hw,hclose⟩,hwindow⟩
    refine ⟨hw,fun n => ?_⟩
    by_cases hn : n < N
    · exact mem_iInter.mp hwindow ⟨n,hn⟩
    · have hnr : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast (Nat.le_of_not_gt hn)
      apply infiniteSide_inverse_window_of_exterior _ (infiniteSideCenter_two_le n)
      exact (infiniteSideCircleQ_large_of_re (-infiniteSideCenter n) w
        (Or.inr (by dsimp only [infiniteSideCenter]; linarith [Nat.cast_nonneg (α := ℝ) n]))).le
  · refine ⟨⟨hz.1,by linarith⟩,mem_iInter.mpr (fun n => hz.2 n)⟩

theorem infiniteSidePolygon_contains_closed_left (z : ℍ) (hz : z.re < 0)
    (hc : ∀n:ℕ,1 ≤ infiniteSideCircleQ (-infiniteSideCenter n) z) :
    z ∈ infiniteSidePolygon :=
  ⟨hz,fun n => infiniteSide_inverse_window_of_exterior _
    (infiniteSideCenter_two_le n) z (hc n)⟩

theorem infiniteSidePolygon_nonempty : infiniteSidePolygon.Nonempty := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-1/2) 1 (by norm_num),
    infiniteSidePolygon_contains_closed_left _ (by change (-1/2:ℝ)<0; norm_num) ?_⟩
  intro n
  exact (infiniteSideCircleQ_large_of_re (-infiniteSideCenter n) _ (Or.inr (by
    change -infiniteSideCenter n+1 ≤ (-1/2:ℝ)
    linarith [infiniteSideCenter_two_le n]))).le

theorem infiniteSideRightWindow_disjoint (n m : ℕ) (hne : n ≠ m) :
    Disjoint (infiniteSideRightWindow (infiniteSideCenter n))
      (infiniteSideRightWindow (infiniteSideCenter m)) := by
  apply disjoint_left.mpr
  intro z hn hm
  rcases lt_or_gt_of_ne hne with h | h
  · have hnm : (n:ℝ)+1 ≤ m := by exact_mod_cast h
    have he : 0 ≤ infiniteSideCenter m-2 := by linarith [infiniteSideCenter_two_le m]
    have hsq : (infiniteSideCenter n+2)^2 ≤ (infiniteSideCenter m-2)^2 := by
      apply (sq_le_sq₀ (by linarith [infiniteSideCenter_two_le n]) he).mpr
      dsimp only [infiniteSideCenter]
      linarith
    exact (not_lt_of_ge (hsq.trans hm.2.1.le)) hn.2.2
  · have hmn : (m:ℝ)+1 ≤ n := by exact_mod_cast h
    have he : 0 ≤ infiniteSideCenter n-2 := by linarith [infiniteSideCenter_two_le n]
    have hsq : (infiniteSideCenter m+2)^2 ≤ (infiniteSideCenter n-2)^2 := by
      apply (sq_le_sq₀ (by linarith [infiniteSideCenter_two_le m]) he).mpr
      dsimp only [infiniteSideCenter]
      linarith
    exact (not_lt_of_ge (hsq.trans hn.2.1.le)) hm.2.2

theorem infiniteSideRightWindow_other_circle (n m : ℕ) (hne : n ≠ m)
    (z : ℍ) (hz : z ∈ infiniteSideRightWindow (infiniteSideCenter n)) :
    1 < infiniteSideCircleQ (infiniteSideCenter m) z := by
  by_contra hn
  have hm := infiniteSideRightWindow_of_circle _ (infiniteSideCenter_two_le m) z
    (le_of_not_gt hn)
  exact disjoint_left.mp (infiniteSideRightWindow_disjoint n m hne) hz hm

def infiniteSidePieces : Option ℕ → Set ℍ
  | none => infiniteSideBase ∩ {z | z.re < 0}
  | some n => infiniteSideBase ∩ infiniteSideRightWindow (infiniteSideCenter n)

def infiniteSideLabels : Option ℕ → (ℍ ≃ᵢ ℍ)
  | none => 1
  | some n => _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n))

def infiniteSideAssembly : Set ℍ :=
  ⋃ j : Option ℕ, infiniteSideLabels j '' infiniteSidePieces j

theorem infiniteSidePieces_subset (j : Option ℕ) :
    infiniteSidePieces j ⊆ infiniteSideBase := by
  cases j <;> exact inter_subset_left

theorem infiniteSidePieces_unique (j k : Option ℕ) (z : ℍ)
    (hj : z ∈ infiniteSidePieces j) (hk : z ∈ infiniteSidePieces k) : j=k := by
  cases j with
  | none =>
    cases k with
    | none => rfl
    | some n => exact False.elim (by
        have h1 : z.re < 0 := hj.2
        have h2 : 0 < z.re := hk.2.1
        linarith)
  | some n =>
    cases k with
    | none => exact False.elim (by
        have h1 : z.re < 0 := hk.2
        have h2 : 0 < z.re := hj.2.1
        linarith)
    | some m =>
      congr 1
      by_contra hne
      exact disjoint_left.mp (infiniteSideRightWindow_disjoint n m hne) hj.2 hk.2

theorem infiniteSideLabels_mem (j : Option ℕ) :
    infiniteSideLabels j ∈ infiniteSideNativeGroup := by
  cases j with
  | none => exact Subgroup.one_mem _
  | some n =>
    exact (le_iSup (fun m : ℕ =>
      Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL
        (infiniteSideCenter m)))) n)
      (Subgroup.mem_zpowers _)

theorem infiniteSideAssembly_isOpen : IsOpen infiniteSideAssembly := by
  apply isOpen_iUnion
  intro j
  apply (infiniteSideLabels j).toHomeomorph.isOpenMap
  cases j with
  | none =>
    exact infiniteSideBase_isOpen.inter
      (isOpen_lt UpperHalfPlane.continuous_re continuous_const)
  | some n => exact infiniteSideBase_isOpen.inter (infiniteSideRightWindow_isOpen _)

theorem infiniteSideAssembly_wandering (g : ℍ ≃ᵢ ℍ)
    (hg : g ∈ infiniteSideNativeGroup) (hne : g ≠ 1) :
    Disjoint (g • infiniteSideAssembly) infiniteSideAssembly :=
  indexed_reassembly_wandering infiniteSideNativeGroup infiniteSideBase
    infiniteSidePieces infiniteSideLabels infiniteSidePieces_subset infiniteSidePieces_unique
    infiniteSideLabels_mem infiniteSideBase_wandering g hg hne

theorem infiniteSideAssembly_subset : infiniteSideAssembly ⊆ infiniteSidePolygon := by
  intro z hz
  obtain ⟨j,w,hw,rfl⟩ := mem_iUnion.mp hz
  cases j with
  | none =>
    change w ∈ infiniteSidePolygon
    exact infiniteSidePolygon_contains_closed_left w hw.2
      (fun n => ((infiniteSideBase_mem_iff w).mp hw.1 n).2.le)
  | some n =>
    let z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)) w
    change z ∈ infiniteSidePolygon
    have hq := ((infiniteSideBase_mem_iff w).mp hw.1 n).1
    have hi := infiniteSideSL_circle_identity (infiniteSideCenter n) w
    have hnonneg : 0 ≤ infiniteSideCircleQ (-infiniteSideCenter n) z :=
      Complex.normSq_nonneg _
    have hzq : infiniteSideCircleQ (-infiniteSideCenter n) z < 1 := by
      change infiniteSideCircleQ (-infiniteSideCenter n) z *
        infiniteSideCircleQ (infiniteSideCenter n) w = 1 at hi
      nlinarith
    have hx := infiniteSideCircleQ_small_re (-infiniteSideCenter n) z hzq.le
    refine ⟨by linarith [infiniteSideCenter_two_le n],fun m => ?_⟩
    by_cases hmn : m=n
    · subst m
      simpa only [z, IsometryEquiv.inv_apply_self] using hw.2
    · have hu : z ∈ infiniteSideSector (infiniteSideCenter n) ∪
          infiniteSideSector (infiniteSideCenter m) := by
        rw [infiniteSideSector_cover n m (Ne.symm hmn)]
        trivial
      have hm : 1 < infiniteSideCircleQ (-infiniteSideCenter m) z := by
        rcases hu with hn | hm
        · exact False.elim ((not_lt_of_ge hzq.le) hn.2)
        · exact hm.2
      exact infiniteSide_inverse_window_of_exterior _
        (infiniteSideCenter_two_le m) z hm.le

open MeasureTheory Filter

def infiniteSideSeams : Set ℍ :=
  ⋃ n : ℕ, {z | infiniteSideCircleQ (-infiniteSideCenter n) z = 1}

theorem infiniteSideSeams_null : volume infiniteSideSeams = 0 := by
  apply measure_iUnion_null
  intro n
  have he : {z : ℍ | infiniteSideCircleQ (-infiniteSideCenter n) z = 1} =
      {z : ℍ | torusCircleQ (-infiniteSideCenter n-1) (-infiniteSideCenter n+1) z = 0} := by
    ext z
    change infiniteSideCircleQ (-infiniteSideCenter n) z = 1 ↔
      torusCircleQ (-infiniteSideCenter n-1) (-infiniteSideCenter n+1) z = 0
    rw [infiniteSideCircleQ_slack]
    constructor <;> intro h <;> linarith
  rw [he]
  exact torusCircleQ_zero_null _ _ (by linarith)

theorem infiniteSidePolygon_outside_seams :
    infiniteSidePolygon ∩ infiniteSideSeamsᶜ ⊆ infiniteSideAssembly := by
  intro z ⟨hz,hseam⟩
  by_cases hall : ∀ n : ℕ, 1 < infiniteSideCircleQ (-infiniteSideCenter n) z
  · have hb : z ∈ infiniteSideBase := by
      rw [infiniteSideBase_mem_iff]
      intro n
      exact ⟨infiniteSideCircleQ_large_of_re _ z
        (Or.inl (by linarith [infiniteSideCenter_two_le n,hz.1])),hall n⟩
    exact mem_iUnion.mpr ⟨none,z,⟨hb,hz.1⟩,rfl⟩
  · push Not at hall
    obtain ⟨n,hn⟩ := hall
    have hne : infiniteSideCircleQ (-infiniteSideCenter n) z ≠ 1 := by
      intro he
      exact hseam (mem_iUnion.mpr ⟨n,he⟩)
    have hlt : infiniteSideCircleQ (-infiniteSideCenter n) z < 1 :=
      lt_of_le_of_ne hn hne
    let w := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)))⁻¹ z
    have he : infiniteSideSL (infiniteSideCenter n) • w = z :=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
        n))).apply_inv_self z
    have hwin : w ∈ infiniteSideRightWindow (infiniteSideCenter n) := hz.2 n
    have hi := infiniteSideSL_circle_identity (infiniteSideCenter n) w
    rw [he] at hi
    have hqw : 1 < infiniteSideCircleQ (infiniteSideCenter n) w := by
      have hp := infiniteSideCircleQ_pos (infiniteSideCenter n) w
      have hnonneg : 0 ≤ infiniteSideCircleQ (-infiniteSideCenter n) z :=
        Complex.normSq_nonneg _
      by_contra hh
      have hle := le_of_not_gt hh
      nlinarith
    have hb : w ∈ infiniteSideBase := by
      rw [infiniteSideBase_mem_iff]
      intro m
      constructor
      · by_cases hmn : m=n
        · simpa only [hmn] using hqw
        · exact infiniteSideRightWindow_other_circle n m (Ne.symm hmn) w hwin
      · exact infiniteSideCircleQ_large_of_re _ w
          (Or.inr (by linarith [infiniteSideCenter_two_le m,hwin.1]))
    exact mem_iUnion.mpr ⟨some n,w,⟨hb,hwin⟩,he⟩

theorem infiniteSidePolygon_subset_closure_assembly :
    infiniteSidePolygon ⊆ closure infiniteSideAssembly := by
  let : Measure.IsOpenPosMeasure (volume : Measure ℍ) :=
    ⟨fun U hU hn => ne_of_gt (_root_.LowDimensionalTopology.Geometry.Polygon.native_open_volume_pos hU hn)⟩
  have hd : Dense infiniteSideSeamsᶜ :=
    (volume : Measure ℍ).dense_of_ae
      (measure_eq_zero_iff_ae_notMem.mp infiniteSideSeams_null)
  exact (hd.open_subset_closure_inter infiniteSidePolygon_isOpen).trans
    (closure_mono infiniteSidePolygon_outside_seams)

theorem infiniteSidePolygon_wandering (g : ℍ ≃ᵢ ℍ)
    (hg : g ∈ infiniteSideNativeGroup) (hne : g ≠ 1) :
    Disjoint (g • infiniteSidePolygon) infiniteSidePolygon :=
  open_closure_wandering infiniteSideNativeGroup infiniteSideAssembly infiniteSidePolygon
    infiniteSideAssembly_isOpen infiniteSidePolygon_isOpen
    infiniteSidePolygon_subset_closure_assembly infiniteSideAssembly_wandering g hg hne

theorem infiniteSidePolygon_frontier_null : volume (frontier infiniteSidePolygon) = 0 :=
  parabolicFord_hConvex_frontier_volume_zero infiniteSidePolygon_hConvex

theorem infiniteSidePieces_locallyFinite : LocallyFinite infiniteSidePieces := by
  intro z
  obtain ⟨N,hN⟩ := exists_nat_gt ‖(z:ℂ)‖
  let U : Set ℍ := {w | ‖(w:ℂ)‖ < N}
  have hU : U ∈ 𝓝 z :=
    (isOpen_lt UpperHalfPlane.continuous_coe.norm continuous_const).mem_nhds hN
  refine ⟨U,hU,?_⟩
  have hf : ({none} ∪ Option.some '' Iio N : Set (Option ℕ)).Finite :=
    (finite_singleton none).union ((finite_Iio N).image Option.some)
  apply hf.subset
  intro j hj
  cases j with
  | none => exact Or.inl (mem_singleton _)
  | some n =>
    apply Or.inr
    refine ⟨n,?_,rfl⟩
    obtain ⟨w,hw,hwn⟩ := hj
    have hlow : (4*(n:ℝ))^2 < ‖(w:ℂ)‖^2 := by
      have h := hw.2.2.1
      change (infiniteSideCenter n-2)^2 < Complex.normSq (w:ℂ) at h
      simpa only [infiniteSideCenter,add_sub_cancel_right,Complex.normSq_eq_norm_sq] using h
    have hbound : 4*(n:ℝ) < ‖(w:ℂ)‖ := by
      nlinarith [norm_nonneg (w:ℂ),Nat.cast_nonneg (α := ℝ) n]
    have hwn' : ‖(w:ℂ)‖ < N := hwn
    have hnN : (n:ℝ) < N := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact_mod_cast hnN

def infiniteSideSourceCuts : Set ℍ :=
  {z | z.re = 0} ∪ ⋃ n : ℕ, {z | Complex.normSq (z:ℂ) = (4*(n:ℝ))^2}

theorem infiniteSideSourceCuts_null : volume infiniteSideSourceCuts = 0 := by
  apply measure_union_null (torusVertical_zero_null 0)
  apply measure_iUnion_null
  intro n
  by_cases hn : n=0
  · subst n
    have he : {z : ℍ | Complex.normSq (z:ℂ) = (4*(0:ℝ))^2} = ∅ := by
      ext z
      have hp : 0 < Complex.normSq (z:ℂ) := by
        simpa only [infiniteSideCircleQ,Complex.ofReal_zero,sub_zero] using
          infiniteSideCircleQ_pos 0 z
      simp only [mul_zero,zero_pow (by norm_num : 2≠0),mem_ofPred_eq,mem_empty_iff_false,
        iff_false]
      exact ne_of_gt hp
    simpa only [Nat.cast_zero,he] using (measure_empty : volume (∅ : Set ℍ) = 0)
  · have hr : (0:ℝ) < 4*(n:ℝ) := by
      have hn' : (0:ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      positivity
    have he : {z : ℍ | Complex.normSq (z:ℂ) = (4*(n:ℝ))^2} =
        {z : ℍ | torusCircleQ (-(4*(n:ℝ))) (4*(n:ℝ)) z = 0} := by
      ext z
      change Complex.normSq (z:ℂ) = (4*(n:ℝ))^2 ↔
        torusCircleQ (-(4*(n:ℝ))) (4*(n:ℝ)) z = 0
      rw [infiniteSide_circleQ_origin]
      constructor <;> intro h <;> linarith
    rw [he]
    exact torusCircleQ_zero_null _ _ (by linarith)

theorem infiniteSide_exists_right_window (z : ℍ) (hx : 0 < z.re)
    (hcut : ∀n:ℕ, Complex.normSq (z:ℂ) ≠ (4*(n:ℝ))^2) :
    ∃n:ℕ,z ∈ infiniteSideRightWindow (infiniteSideCenter n) := by
  let n := Nat.floor (‖(z:ℂ)‖/4)
  have hl := Nat.floor_le (show 0 ≤ ‖(z:ℂ)‖/4 by positivity)
  have hu := Nat.lt_floor_add_one (‖(z:ℂ)‖/4)
  have hlow : 4*(n:ℝ) ≤ ‖(z:ℂ)‖ := by
    dsimp only [n]
    linarith
  have hupp : ‖(z:ℂ)‖ < 4*(n:ℝ)+4 := by
    dsimp only [n]
    linarith
  refine ⟨n,hx,?_,?_⟩
  · have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 4*(n:ℝ))
      (norm_nonneg (z:ℂ))).mpr hlow
    have hne := Ne.symm (hcut n)
    rw [Complex.normSq_eq_norm_sq] at hne
    have hh := lt_of_le_of_ne hsq hne
    simpa only [infiniteSideCenter,add_sub_cancel_right,Complex.normSq_eq_norm_sq] using hh
  · have hh := (sq_lt_sq₀ (norm_nonneg (z:ℂ))
      (by positivity : 0 ≤ 4*(n:ℝ)+4)).mpr hupp
    change Complex.normSq (z:ℂ) < (4*(n:ℝ)+2+2)^2
    rw [Complex.normSq_eq_norm_sq]
    convert hh using 1; ring

theorem infiniteSideBase_outside_cuts :
    infiniteSideBase ∩ infiniteSideSourceCutsᶜ ⊆ ⋃ j, infiniteSidePieces j := by
  intro z ⟨hz,hcut⟩
  have hx : z.re ≠ 0 := fun h => hcut (Or.inl h)
  rcases lt_or_gt_of_ne hx with hn | hp
  · exact mem_iUnion.mpr ⟨none,⟨hz,hn⟩⟩
  · obtain ⟨n,hn⟩ := infiniteSide_exists_right_window z hp (fun n he =>
      hcut (Or.inr (mem_iUnion.mpr ⟨n,he⟩)))
    exact mem_iUnion.mpr ⟨some n,⟨hz,hn⟩⟩

theorem infiniteSideBase_subset_closure_pieces :
    infiniteSideBase ⊆ closure (⋃ j, infiniteSidePieces j) := by
  let : Measure.IsOpenPosMeasure (volume : Measure ℍ) :=
    ⟨fun U hU hn => ne_of_gt (_root_.LowDimensionalTopology.Geometry.Polygon.native_open_volume_pos hU hn)⟩
  have hd : Dense infiniteSideSourceCutsᶜ :=
    (volume : Measure ℍ).dense_of_ae
      (measure_eq_zero_iff_ae_notMem.mp infiniteSideSourceCuts_null)
  exact (hd.open_subset_closure_inter infiniteSideBase_isOpen).trans
    (closure_mono infiniteSideBase_outside_cuts)

theorem infiniteSidePolygon_closure_meetsEveryOrbit :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit infiniteSideNativeGroup ℍ (closure infiniteSidePolygon) := by
  intro z
  obtain ⟨g,hg⟩ := infiniteSideBase_closure_meetsEveryOrbit z
  have hc : closure infiniteSideBase ⊆ ⋃j,closure (infiniteSidePieces j) := by
    rw [← infiniteSidePieces_locallyFinite.closure_iUnion]
    exact (closure_mono infiniteSideBase_subset_closure_pieces).trans_eq closure_closure
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hc hg)
  let k : infiniteSideNativeGroup :=
    ⟨infiniteSideLabels j,infiniteSideLabels_mem j⟩ * g
  refine ⟨k,?_⟩
  have him : infiniteSideLabels j (g.val z) ∈
      closure (infiniteSideLabels j '' infiniteSidePieces j) := by
    have he : infiniteSideLabels j '' closure (infiniteSidePieces j) =
        closure (infiniteSideLabels j '' infiniteSidePieces j) :=
      (infiniteSideLabels j).toHomeomorph.image_closure _
    rw [← he]
    exact mem_image_of_mem _ hj
  apply closure_mono infiniteSideAssembly_subset
  exact closure_mono (subset_iUnion (fun j => infiniteSideLabels j '' infiniteSidePieces j) j) him

theorem infiniteSidePolygon_fundamental :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain infiniteSideNativeGroup ℍ volume infiniteSidePolygon := by
  refine ⟨infiniteSidePolygon_isOpen,
    ⟨infiniteSidePolygon_nonempty,infiniteSidePolygon_hConvex.isPreconnected⟩,?_,
    infiniteSidePolygon_frontier_null⟩
  apply exists_fundamentalSet_between _ _ subset_closure infiniteSidePolygon_closure_meetsEveryOrbit
  intro x hx y hy hxy
  obtain ⟨g,hg⟩ := (Quotient.exact hxy : MulAction.orbitRel infiniteSideNativeGroup ℍ x y)
  change g.val y=x at hg
  by_cases he : g.val=1
  · rw [he] at hg
    exact hg.symm
  · exact False.elim (disjoint_left.mp (infiniteSidePolygon_wandering g.val g.property he)
      ⟨y,hy,hg⟩ hx)

theorem infiniteSide_label_image_circle (n : ℕ) (w : ℍ) (hw : w ∈ infiniteSideBase) :
    infiniteSideCircleQ (-infiniteSideCenter n)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)) w) < 1 := by
  have hq := ((infiniteSideBase_mem_iff w).mp hw n).1
  have hi := infiniteSideSL_circle_identity (infiniteSideCenter n) w
  have hn : 0 ≤ infiniteSideCircleQ (-infiniteSideCenter n)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)) w) :=
    Complex.normSq_nonneg _
  change infiniteSideCircleQ (-infiniteSideCenter n)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)) w) *
      infiniteSideCircleQ (infiniteSideCenter n) w = 1 at hi
  nlinarith

theorem infiniteSide_imagePieces_locallyFinite :
    LocallyFinite (fun j => infiniteSideLabels j '' infiniteSidePieces j) := by
  intro z
  obtain ⟨N,hN⟩ := exists_nat_gt (-z.re+3)
  let U : Set ℍ := {w | z.re-1 < w.re}
  have hzU : z ∈ U := by change z.re-1 < z.re; linarith
  have hoU : IsOpen U := isOpen_lt continuous_const UpperHalfPlane.continuous_re
  have hU : U ∈ 𝓝 z := hoU.mem_nhds hzU
  refine ⟨U,hU,?_⟩
  have hf : ({none} ∪ Option.some '' Iio N : Set (Option ℕ)).Finite :=
    (finite_singleton none).union ((finite_Iio N).image Option.some)
  apply hf.subset
  intro j hj
  cases j with
  | none => exact Or.inl (mem_singleton _)
  | some n =>
    apply Or.inr
    refine ⟨n,?_,rfl⟩
    obtain ⟨v,⟨w,hw,rfl⟩,hv⟩ := hj
    have hq := infiniteSide_label_image_circle n w hw.1
    have hx := infiniteSideCircleQ_small_re _ _ hq.le
    have hv' : z.re-1 < (infiniteSideLabels (some n) w).re := hv
    have hnN : (n:ℝ) < N := by
      change z.re-1 < (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
        n)) w).re at hv'
      have hh : infiniteSideCenter n < 2-z.re := by linarith [hx.2,hv']
      dsimp only [infiniteSideCenter] at hh
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact_mod_cast hnN

theorem infiniteSidePolygon_closure_pieces :
    closure infiniteSidePolygon =
      ⋃ j,closure (infiniteSideLabels j '' infiniteSidePieces j) := by
  calc
    closure infiniteSidePolygon = closure infiniteSideAssembly := by
      apply subset_antisymm
      · exact (closure_mono infiniteSidePolygon_subset_closure_assembly).trans_eq closure_closure
      · exact closure_mono infiniteSideAssembly_subset
    _ = _ := infiniteSide_imagePieces_locallyFinite.closure_iUnion

theorem infiniteSidePolygon_native_compact_hits (K : Set ℍ) (hK : IsCompact K) :
    {g : infiniteSideNativeGroup |
      (g.val '' closure infiniteSidePolygon ∩ K).Nonempty}.Finite := by
  let A : Set infiniteSideNativeGroup :=
    {h | (h.val '' closure infiniteSideBase ∩ K).Nonempty}
  let C (h : infiniteSideNativeGroup) : Set ℍ := h.val.symm '' K
  let J (h : infiniteSideNativeGroup) : Set (Option ℕ) :=
    {j | (closure (infiniteSidePieces j) ∩ C h).Nonempty}
  let L (j : Option ℕ) : infiniteSideNativeGroup :=
    ⟨infiniteSideLabels j,infiniteSideLabels_mem j⟩
  have hA : A.Finite := infiniteSideBase_native_compact_hits K hK
  have hJ (h : infiniteSideNativeGroup) : (J h).Finite :=
    infiniteSidePieces_locallyFinite.closure.finite_nonempty_inter_compact
      (hK.image h.val.symm.continuous)
  have hf : (⋃ h ∈ A, (fun j => h * (L j)⁻¹) '' J h).Finite :=
    hA.biUnion (fun h _ => (hJ h).image _)
  apply hf.subset
  rintro g ⟨x,⟨y,hy,hgy⟩,hxK⟩
  rw [infiniteSidePolygon_closure_pieces] at hy
  obtain ⟨j,hj⟩ := mem_iUnion.mp hy
  have he : infiniteSideLabels j '' closure (infiniteSidePieces j) =
      closure (infiniteSideLabels j '' infiniteSidePieces j) :=
    (infiniteSideLabels j).toHomeomorph.image_closure _
  rw [← he] at hj
  obtain ⟨w,hw,hwL⟩ := hj
  let h := g * L j
  have hhw : h.val w = x := by
    change g.val (infiniteSideLabels j w)=x
    rw [hwL]
    exact hgy
  have hhA : h ∈ A :=
    ⟨x,⟨w,closure_mono (infiniteSidePieces_subset j) hw,hhw⟩,hxK⟩
  have hjJ : j ∈ J h := by
    refine ⟨w,hw,x,hxK,?_⟩
    rw [← hhw,h.val.symm_apply_apply]
  refine mem_iUnion.mpr ⟨h,mem_iUnion.mpr ⟨hhA,j,hjJ,?_⟩⟩
  dsimp only [h]
  group

theorem infiniteSidePolygon_native_locallyFinite :
    LocallyFinite (fun g : infiniteSideNativeGroup =>
      g.val '' closure infiniteSidePolygon) := by
  intro x
  obtain ⟨K,hK,hx⟩ := exists_compact_mem_nhds x
  exact ⟨K,hx,infiniteSidePolygon_native_compact_hits K hK⟩

def infiniteSideWindowProbe (c : ℝ) : ℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe c 2 (by norm_num)

theorem infiniteSideWindowProbe_mem (c : ℝ) (hc : 2 ≤ c) :
    infiniteSideWindowProbe c ∈ infiniteSideRightWindow c := by
  change 0<c ∧ (c-2)^2 < Complex.normSq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe c 2 (by norm_num):ℂ) ∧
    Complex.normSq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe c 2 (by norm_num):ℂ) < (c+2)^2
  simp only [Complex.normSq_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
  constructor
  · linarith
  · constructor <;> nlinarith

theorem infiniteSideRightWindow_closure (c : ℝ) (hc : 2 ≤ c) :
    closure (infiniteSideRightWindow c) =
      {z : ℍ | 0 ≤ z.re ∧ (c-2)^2 ≤ Complex.normSq (z:ℂ) ∧
        Complex.normSq (z:ℂ) ≤ (c+2)^2} := by
  have hk : closure (infiniteSideRightWindow c) =
      torusKleinClosedRegion (infiniteSideWindowNormals c) (infiniteSideWindowThresholds c) := by
    rw [infiniteSideRightWindow_klein]
    exact torusKleinCutRegion_closure _ _ _ (infiniteSideRightWindow_klein c ▸
      infiniteSideWindowProbe_mem c hc)
  rw [hk]
  ext z
  have h0 : 0 ≤ z.re ↔ inner ℝ (-torusVerticalNormal 0) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) ≤ 0 := by
    rw [inner_neg_left,neg_nonpos]
    simpa only [zero_div,not_lt] using not_congr (torusVertical_klein_lt 0 z)
  constructor
  · intro hz
    have hz0 := hz (0:Fin 3)
    have hz1 := (torusCircleQ_klein_nonneg_iff (-(c-2)) (c-2) z).mpr (hz 1)
    have hz2 := (torusCircleQ_klein_nonpos_iff (-(c+2)) (c+2) z).mpr (hz 2)
    rw [infiniteSide_circleQ_origin] at hz1 hz2
    exact ⟨h0.mpr hz0,by linarith,by linarith⟩
  · rintro ⟨hz0,hz1,hz2⟩ i
    fin_cases i
    · exact h0.mp hz0
    · exact (torusCircleQ_klein_nonneg_iff _ _ z).mp (by
        rw [infiniteSide_circleQ_origin]
        linarith)
    · exact (torusCircleQ_klein_nonpos_iff _ _ z).mp (by
        rw [infiniteSide_circleQ_origin]
        linarith)

theorem infiniteSideWindowProbe_base (n : ℕ) :
    infiniteSideWindowProbe (infiniteSideCenter n) ∈ infiniteSideBase := by
  rw [infiniteSideBase_mem_iff]
  intro m
  have hw := infiniteSideWindowProbe_mem _ (infiniteSideCenter_two_le n)
  constructor
  · by_cases hmn : m=n
    · subst m
      norm_num [infiniteSideCircleQ_coordinates,infiniteSideWindowProbe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
    · exact infiniteSideRightWindow_other_circle n m (Ne.symm hmn) _ hw
  · exact infiniteSideCircleQ_large_of_re _ _
      (Or.inr (by
        change -infiniteSideCenter m+1 ≤ infiniteSideCenter n
        linarith [infiniteSideCenter_two_le m,infiniteSideCenter_two_le n]))

theorem infiniteSidePolygon_closure_re (z : ℍ) (hz : z ∈ closure infiniteSidePolygon) :
    z.re ≤ 0 :=
  closure_minimal (fun _ h => h.1.le)
    (isClosed_le UpperHalfPlane.continuous_re continuous_const) hz

theorem infiniteSidePolygon_closure_window (z : ℍ)
    (hz : z ∈ closure infiniteSidePolygon) (n : ℕ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)))⁻¹ z ∈
      closure (infiniteSideRightWindow (infiniteSideCenter n)) := by
  have hclosed : IsClosed ((fun w : ℍ =>
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)))⁻¹ w) ⁻¹'
      closure (infiniteSideRightWindow (infiniteSideCenter n))) :=
    isClosed_closure.preimage ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL
      (infiniteSideCenter n)))⁻¹).continuous
  have hsub : infiniteSidePolygon ⊆ (fun w : ℍ =>
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)))⁻¹ w) ⁻¹'
      closure (infiniteSideRightWindow (infiniteSideCenter n)) :=
    fun _ h => subset_closure (h.2 n)
  exact closure_minimal hsub hclosed hz

theorem infiniteSidePolygon_axis_closure (z : ℍ) (hz : z.re=0) :
    z ∈ closure infiniteSidePolygon := by
  have hs : UpperHalfPlane.re ⁻¹' Ioo (-1:ℝ) 0 ⊆ infiniteSidePolygon := by
    intro w hw
    apply infiniteSidePolygon_contains_closed_left w hw.2
    intro n
    exact (infiniteSideCircleQ_large_of_re _ w
      (Or.inr (by linarith [infiniteSideCenter_two_le n,hw.1]))).le
  apply closure_mono hs
  rw [← UpperHalfPlane.isOpenMap_re.preimage_closure_eq_closure_preimage UpperHalfPlane.continuous_re,
    closure_Ioo (by norm_num : (-1:ℝ)≠0)]
  change -1 ≤ z.re ∧ z.re ≤ 0
  simp only [hz]
  norm_num

theorem infiniteSidePolygon_axis_frontier (z : ℍ) (hz : z.re=0) :
    z ∈ frontier infiniteSidePolygon := by
  refine ⟨infiniteSidePolygon_axis_closure z hz,?_⟩
  rw [infiniteSidePolygon_isOpen.interior_eq]
  exact fun h => (not_lt_of_ge (by linarith : 0≤z.re)) h.1

theorem infiniteSide_closed_piece_image (j : Option ℕ) (z : ℍ)
    (hz : z ∈ closure (infiniteSidePieces j)) :
    infiniteSideLabels j z ∈ closure infiniteSidePolygon := by
  rw [infiniteSidePolygon_closure_pieces]
  apply mem_iUnion.mpr
  refine ⟨j,?_⟩
  have he : infiniteSideLabels j '' closure (infiniteSidePieces j) =
      closure (infiniteSideLabels j '' infiniteSidePieces j) :=
    (infiniteSideLabels j).toHomeomorph.image_closure _
  rw [←he]
  exact mem_image_of_mem _ hz

def infiniteSideAxisInterval (n : ℕ) : Set ℍ :=
  {z | z.re=0 ∧ 4*(n:ℝ) ≤ z.im ∧ z.im ≤ 4*(n:ℝ)+4}

theorem infiniteSidePolygon_paired_intersection (n : ℕ) :
    closure infiniteSidePolygon ∩
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)))⁻¹ : ℍ ≃ᵢ
        ℍ) ''
        closure infiniteSidePolygon = infiniteSideAxisInterval n := by
  ext z
  constructor
  · rintro ⟨hz,⟨w,hw,hwz⟩⟩
    let L := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n))
    have hLz : L z ∈ closure infiniteSidePolygon := by
      rw [←hwz]
      simpa only [L,IsometryEquiv.apply_inv_self] using hw
    have hwin := infiniteSidePolygon_closure_window (L z) hLz n
    have hzwin : z ∈ closure (infiniteSideRightWindow (infiniteSideCenter n)) := by
      simpa only [L,IsometryEquiv.inv_apply_self] using hwin
    rw [infiniteSideRightWindow_closure _ (infiniteSideCenter_two_le n)] at hzwin
    have hre : z.re=0 := le_antisymm (infiniteSidePolygon_closure_re z hz) hzwin.1
    have hn : Complex.normSq (z:ℂ)=z.im^2 := by
      simp only [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,hre]
      ring
    refine ⟨hre,?_,?_⟩
    · have hlow : (4*(n:ℝ))^2 ≤ z.im^2 := by
        simpa only [infiniteSideCenter,add_sub_cancel_right,hn] using hzwin.2.1
      exact (sq_le_sq₀ (by positivity) z.im_pos.le).mp hlow
    · have hupp : z.im^2 ≤ (4*(n:ℝ)+4)^2 := by
        convert hzwin.2.2 using 1
        · exact hn.symm
        · dsimp only [infiniteSideCenter]
          ring
      exact (sq_le_sq₀ z.im_pos.le (by positivity)).mp hupp
  · rintro ⟨hre,hlo,hhi⟩
    have hn : Complex.normSq (z:ℂ)=z.im^2 := by
      simp only [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,hre]
      ring
    have hzB : z ∈ infiniteSideBase := by
      rw [infiniteSideBase_mem_iff]
      intro m
      constructor
      all_goals rw [infiniteSideCircleQ_coordinates,hre]
      all_goals nlinarith [infiniteSideCenter_two_le m,sq_pos_of_pos z.im_pos]
    have hzW : z ∈ closure (infiniteSideRightWindow (infiniteSideCenter n)) := by
      rw [infiniteSideRightWindow_closure _ (infiniteSideCenter_two_le n)]
      refine ⟨by linarith,?_,?_⟩
      · have hs := (sq_le_sq₀ (by positivity) z.im_pos.le).mpr hlo
        simpa only [infiniteSideCenter,add_sub_cancel_right,hn] using hs
      · have hs := (sq_le_sq₀ z.im_pos.le (by positivity)).mpr hhi
        rw [hn]
        convert hs using 1
        dsimp only [infiniteSideCenter]
        ring
    have hzPiece : z ∈ closure (infiniteSidePieces (some n)) := by
      change z ∈ closure (infiniteSideBase ∩ infiniteSideRightWindow (infiniteSideCenter n))
      rw [hConvex_open_closure_inter infiniteSideBase_hConvex
        (infiniteSideRightWindow_hConvex _) infiniteSideBase_isOpen
        (infiniteSideRightWindow_isOpen _) ⟨infiniteSideWindowProbe (infiniteSideCenter n),
          infiniteSideWindowProbe_base n,
          infiniteSideWindowProbe_mem _ (infiniteSideCenter_two_le n)⟩]
      exact ⟨subset_closure hzB,hzW⟩
    refine ⟨infiniteSidePolygon_axis_closure z hre,?_⟩
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)) z,
      infiniteSide_closed_piece_image (some n) z hzPiece,?_⟩
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
      n))).inv_apply_self z

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace MeasureTheory

def infiniteSideGenerator (n : ℕ) : infiniteSideNativeGroup :=
  ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
    n)),infiniteSideLabels_mem (some n)⟩

theorem infiniteSidePolygon_original_fundamental :
    let := infiniteSideData.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain infiniteSideGroup ℍ volume infiniteSidePolygon := by
  let := infiniteSideData.nativeAction
  have he (g : infiniteSideGroup) (z : ℍ) :
      (Homeomorph.refl ℍ) (g • z) =
        infiniteSideNativeOriginalEquiv.symm g • (Homeomorph.refl ℍ) z := by
    change g • z = (infiniteSideNativeOriginalEquiv.symm g).val z
    have h := infiniteSideNativeOriginalEquiv_action (infiniteSideNativeOriginalEquiv.symm g) z
    rwa [infiniteSideNativeOriginalEquiv.apply_symm_apply] at h
  simpa using _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage infiniteSideNativeOriginalEquiv.symm
    (Homeomorph.refl ℍ) he infiniteSidePolygon_fundamental

theorem infiniteSidePolygon_original_compact_hits (K : Set ℍ) (hK : IsCompact K) :
    let := infiniteSideData.nativeAction
    {g : infiniteSideGroup | (g • closure infiniteSidePolygon ∩ K).Nonempty}.Finite := by
  let := infiniteSideData.nativeAction
  have hf := (infiniteSidePolygon_native_compact_hits K hK).image infiniteSideNativeOriginalEquiv
  apply hf.subset
  rintro g ⟨x,⟨z,hz,hgz⟩,hx⟩
  refine ⟨infiniteSideNativeOriginalEquiv.symm g,?_,infiniteSideNativeOriginalEquiv.apply_symm_apply g⟩
  refine ⟨x,⟨z,hz,?_⟩,hx⟩
  have he := infiniteSideNativeOriginalEquiv_action (infiniteSideNativeOriginalEquiv.symm g) z
  rw [infiniteSideNativeOriginalEquiv.apply_symm_apply] at he
  exact he.symm.trans hgz

def infiniteSideOriginalPolygon : Set infiniteSideData.cayleyData.domain.carrier :=
  infiniteSideData.cayleyCoordinate '' infiniteSidePolygon

theorem infiniteSideOriginalPolygon_convexPolygon :
    IsConvexFuchsianPolygon infiniteSideData.cayleyData infiniteSideOriginalPolygon :=
  infiniteSideData.cayley_polygon infiniteSidePolygon_original_fundamental
    infiniteSidePolygon_hConvex infiniteSidePolygon_original_compact_hits

def infiniteSideOriginalSide (n : ℕ) : Set infiniteSideData.cayleyData.domain.carrier :=
  infiniteSideData.cayleyCoordinate '' infiniteSideAxisInterval n

theorem infiniteSide_cayley_closed_tile (g : infiniteSideNativeGroup) :
    infiniteSideData.cayleyCoordinate '' (g.val '' closure infiniteSidePolygon) =
      fuchsianDomainTile infiniteSideData.cayleyData infiniteSideOriginalPolygon
        (infiniteSideCayleyGroupEquiv g) := by
  let F := infiniteSideData.cayleyCoordinate
  rw [fuchsianDomainTile,show infiniteSideOriginalPolygon=F '' infiniteSidePolygon from rfl,
    ←F.image_closure]
  ext x
  constructor
  · rintro ⟨z,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨F w,mem_image_of_mem F hw,(infiniteSideCayley_equivariant g w).symm⟩
  · rintro ⟨y,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨g.val w,mem_image_of_mem g.val hw,infiniteSideCayley_equivariant g w⟩

theorem infiniteSideOriginalSide_intersection (n : ℕ) :
    infiniteSideOriginalSide n = closure infiniteSideOriginalPolygon ∩
      fuchsianDomainTile infiniteSideData.cayleyData infiniteSideOriginalPolygon
        (infiniteSideCayleyGroupEquiv (infiniteSideGenerator n)⁻¹) := by
  rw [←infiniteSide_cayley_closed_tile,show infiniteSideOriginalPolygon=
    infiniteSideData.cayleyCoordinate '' infiniteSidePolygon from rfl,
    ←infiniteSideData.cayleyCoordinate.image_closure,
    ←image_inter infiniteSideData.cayleyCoordinate.injective]
  change infiniteSideOriginalSide n = infiniteSideData.cayleyCoordinate ''
    (closure infiniteSidePolygon ∩
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)))⁻¹ : ℍ ≃ᵢ
        ℍ) ''
        closure infiniteSidePolygon)
  rw [infiniteSidePolygon_paired_intersection]
  rfl

theorem infiniteSideAxisInterval_nontrivial (n : ℕ) : (infiniteSideAxisInterval n).Nontrivial := by
  let a := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (4*(n:ℝ)+1) (by positivity)
  let b := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (4*(n:ℝ)+2) (by positivity)
  refine ⟨a,?_,b,?_,?_⟩
  · change 0=0 ∧ 4*(n:ℝ)≤4*(n:ℝ)+1 ∧ 4*(n:ℝ)+1≤4*(n:ℝ)+4
    exact ⟨rfl,by linarith,by linarith⟩
  · change 0=0 ∧ 4*(n:ℝ)≤4*(n:ℝ)+2 ∧ 4*(n:ℝ)+2≤4*(n:ℝ)+4
    exact ⟨rfl,by linarith,by linarith⟩
  · intro he
    have hi := congrArg UpperHalfPlane.im he
    change 4*(n:ℝ)+1=4*(n:ℝ)+2 at hi
    linarith

theorem infiniteSideOriginalSide_isSide (n : ℕ) :
    IsFuchsianPolygonSide infiniteSideData.cayleyData infiniteSideOriginalPolygon
      (infiniteSideOriginalSide n) := by
  rw [infiniteSideOriginalSide_intersection]
  apply infiniteSideOriginalPolygon_convexPolygon.side_of_nontrivial_intersection
  · intro he
    have hk : (infiniteSideGenerator n)⁻¹=1 := infiniteSideCayleyGroupEquiv.injective
      (he.trans infiniteSideCayleyGroupEquiv.map_one.symm)
    exact (inv_ne_one.mpr (infiniteSide_generator_ne_one n)) (congrArg Subtype.val hk)
  · rw [←infiniteSideOriginalSide_intersection]
    exact (infiniteSideAxisInterval_nontrivial n).image infiniteSideData.cayleyCoordinate.injective

theorem infiniteSideOriginalSide_injective : Function.Injective infiniteSideOriginalSide := by
  intro n m he
  have he' : infiniteSideAxisInterval n=infiniteSideAxisInterval m :=
    Set.image_injective.mpr infiniteSideData.cayleyCoordinate.injective he
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (4*(n:ℝ)+1) (by positivity) ∈ infiniteSideAxisInterval n :=
    ⟨rfl,by change 4*(n:ℝ)≤4*(n:ℝ)+1;linarith,
      by change 4*(n:ℝ)+1≤4*(n:ℝ)+4;linarith⟩
  have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (4*(m:ℝ)+1) (by positivity) ∈ infiniteSideAxisInterval m :=
    ⟨rfl,by change 4*(m:ℝ)≤4*(m:ℝ)+1;linarith,
      by change 4*(m:ℝ)+1≤4*(m:ℝ)+4;linarith⟩
  have hnm := he' ▸ hn
  have hmn := he'.symm ▸ hm
  change _=0 ∧ 4*(m:ℝ)≤4*(n:ℝ)+1 ∧ 4*(n:ℝ)+1≤4*(m:ℝ)+4 at hnm
  change _=0 ∧ 4*(n:ℝ)≤4*(m:ℝ)+1 ∧ 4*(m:ℝ)+1≤4*(n:ℝ)+4 at hmn
  have hlo : m≤n := Nat.lt_succ_iff.mp (by exact_mod_cast (by linarith [hnm.2.1] : (m:ℝ)<n+1))
  have hhi : n≤m := Nat.lt_succ_iff.mp (by exact_mod_cast (by linarith [hmn.2.1] : (n:ℝ)<m+1))
  exact le_antisymm hhi hlo

def infiniteSideOriginalEdge : Set infiniteSideData.cayleyData.domain.carrier :=
  infiniteSideData.cayleyCoordinate '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
    0).carrier

theorem infiniteSideOriginalSide_subset_edge (n : ℕ) :
    infiniteSideOriginalSide n⊆infiniteSideOriginalEdge := by
  rintro z ⟨w,hw,rfl⟩
  exact ⟨w,hw.1,rfl⟩

theorem infiniteSideOriginalEdge_isEdge :
    IsFuchsianPolygonEdge infiniteSideData.cayleyData infiniteSideOriginalPolygon
      infiniteSideOriginalEdge := by
  let P := infiniteSideData.cayleyData
  let F := infiniteSideData.cayleyCoordinate
  let L := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).toDiscLine
  have he : P.finiteCoordinate '' infiniteSideOriginalEdge=L.carrier := by
    rw [show infiniteSideOriginalEdge=F '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
      0).carrier from rfl,
      image_image]
    dsimp only [L]
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_carrier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.discCarrier_eq_cayley_image]
    exact image_congr (fun z _=>infiniteSideData.cayleyCoordinate_finite z)
  have hnt : infiniteSideOriginalEdge.Nontrivial := by
    apply ((infiniteSideAxisInterval_nontrivial 0).image F.injective).mono
    exact infiniteSideOriginalSide_subset_edge 0
  refine ⟨⟨?_,L,?_⟩,hnt,?_,?_⟩
  · rw [he]
    exact L.hConvex
  · rw [he]
  · rintro z ⟨w,hw,rfl⟩
    rw [show infiniteSideOriginalPolygon=F '' infiniteSidePolygon from rfl,←F.image_frontier]
    exact mem_image_of_mem F (infiniteSidePolygon_axis_frontier w hw)
  · intro T hT _hTF hET z hzT
    obtain ⟨M,hM⟩:=hT.2
    obtain ⟨a,ha,b,hb,hab⟩:=hnt
    have hLM : L=M := L.eq_of_two_points M (P.finiteCoordinate.injective.ne hab)
      (he ▸ mem_image_of_mem P.finiteCoordinate ha)
      (he ▸ mem_image_of_mem P.finiteCoordinate hb)
      (hM (mem_image_of_mem P.finiteCoordinate (hET ha)))
      (hM (mem_image_of_mem P.finiteCoordinate (hET hb)))
    have hzL : P.finiteCoordinate z∈P.finiteCoordinate '' infiniteSideOriginalEdge := by
      rw [he,hLM]
      exact hM (mem_image_of_mem P.finiteCoordinate hzT)
    exact P.finiteCoordinate.injective.mem_set_image.mp hzL

theorem infiniteSideOriginalEdge_infinitely_many_sides :
    {S | IsFuchsianPolygonSide infiniteSideData.cayleyData infiniteSideOriginalPolygon S ∧
      S⊆infiniteSideOriginalEdge}.Infinite := by
  apply Set.infinite_range_of_injective infiniteSideOriginalSide_injective |>.mono
  rintro S ⟨n,rfl⟩
  exact ⟨infiniteSideOriginalSide_isSide n,infiniteSideOriginalSide_subset_edge n⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open scoped OnePoint

/-- The first two actual generators of have no common fixed point on the entire extended complex plane. -/
theorem infiniteSideSL_zero_one_no_common_fixed (p:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    ¬ ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (infiniteSideSL (infiniteSideCenter 0))).val p=p
      ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (infiniteSideSL (infiniteSideCenter 1))).val p=p) := by
  intro h
  induction p using OnePoint.rec with
  | infty =>
    have hz:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff _).mp h.1
    norm_num [infiniteSideSL] at hz
  | coe z =>
    have hquad (c:ℝ)
        (hc:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (infiniteSideSL c)).val (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
        z*z=((c^2-1:ℝ):ℂ) := by
      change _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map Complex.ofRealHom (infiniteSideSL c))) z=z at hc
      have hf:=(_root_.LowDimensionalTopology.Geometry.Mobius.Classification.fractionalLinear_fixed_coe_iff _ z).mp hc
      change (((infiniteSideSL c) 1 0:ℝ):ℂ)*(z*z)+
        ((((infiniteSideSL c) 1 1:ℝ):ℂ)-(((infiniteSideSL c) 0 0:ℝ):ℂ))*z+
        (-(((infiniteSideSL c) 0 1:ℝ):ℂ))=0 at hf
      norm_num [infiniteSideSL] at hf
      push_cast
      linear_combination hf
    have h0:=hquad (infiniteSideCenter 0) h.1
    have h1:=hquad (infiniteSideCenter 1) h.2
    norm_num [infiniteSideCenter] at h0 h1
    have hh:=h0.symm.trans h1
    norm_num at hh

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem infiniteSideSL_mem_group (n:ℕ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (infiniteSideSL (infiniteSideCenter n))∈infiniteSideGroup := by
  have hn:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
    n))∈infiniteSideNativeGroup:=
    (le_iSup (fun m:ℕ=>Subgroup.zpowers
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter
        m)))) n) (Subgroup.mem_zpowers _)
  refine ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)),hn⟩,?_⟩
  exact nativeConformalSubgroupMobiusHom_matrix _ _ _ _

theorem infiniteSideSL_hyperbolic (c:ℝ) (hc:2≤c) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (infiniteSideSL c)) := by
  have ht:4<(Matrix.trace (infiniteSideSL c).val)^2:=by
    norm_num [Matrix.trace_fin_two,infiniteSideSL]
    nlinarith
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
    (realSLMobius_ne_one_of_trace_sq_gt_four _ ht)).mpr ht

/-- The actual complete generated group is non-elementary. -/
theorem infiniteSideGroup_nonElementary : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary infiniteSideGroup := by
  have h0:=infiniteSideSL_hyperbolic (infiniteSideCenter 0) (infiniteSideCenter_two_le 0)
  have h1:=infiniteSideSL_hyperbolic (infiniteSideCenter 1) (infiniteSideCenter_two_le 1)
  intro hE
  obtain ⟨p,q,_hpq,hp,_hq,hpair⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elementary_loxodromic_fixed_pair infiniteSideGroup
    infiniteSideData.discrete hE _ (infiniteSideSL_mem_group 0) h0.1
  have hp1:=(elementary_invariant_pair_fixed_by_loxodromic infiniteSideGroup p q hpair
    ⟨_,infiniteSideSL_mem_group 1⟩ h1.1).1
  exact infiniteSideSL_zero_one_no_common_fixed p ⟨hp,hp1⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The literal left-hand region. -/
def infiniteSideSourceHalfDomain : Set ℍ :=
  {z | z.re<0 ∧ ∀n:ℕ,1 < infiniteSideCircleQ (-infiniteSideCenter n) z}

/-- The literal right-hand annular region. -/
def infiniteSideSourceAnnularPiece (n:ℕ) : Set ℍ :=
  infiniteSideRightWindow (infiniteSideCenter n) ∩
    {z | 1 ≤ infiniteSideCircleQ (infiniteSideCenter n) z}

def infiniteSideSourceCircle (n:ℕ) : Set ℍ :=
  {z | infiniteSideCircleQ (infiniteSideCenter n) z=1}

theorem infiniteSideSourceCircle_subset_annular (n:ℕ) :
    infiniteSideSourceCircle n⊆infiniteSideSourceAnnularPiece n := by
  intro z hz
  exact ⟨infiniteSideRightWindow_of_circle _ (infiniteSideCenter_two_le n) z hz.le,hz.ge⟩

/-- The concrete intersection of geodesic cuts equals the geometric actual countable reassembly, including its circle seams. -/
theorem infiniteSidePolygon_source_formula :
    infiniteSidePolygon = infiniteSideSourceHalfDomain ∪
      ⋃n:ℕ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)) ''
        (infiniteSideSourceAnnularPiece n ∪ infiniteSideSourceCircle n) := by
  ext z
  constructor
  · intro hz
    by_cases hall:∀n:ℕ,1 < infiniteSideCircleQ (-infiniteSideCenter n) z
    · exact Or.inl ⟨hz.1,hall⟩
    · push Not at hall
      obtain ⟨n,hn⟩:=hall
      right
      apply mem_iUnion.mpr
      let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n))
      let w:=L⁻¹ z
      have he:infiniteSideSL (infiniteSideCenter n) • w=z:=L.apply_inv_self z
      have hi:=infiniteSideSL_circle_identity (infiniteSideCenter n) w
      rw [he] at hi
      have hq:1 ≤ infiniteSideCircleQ (infiniteSideCenter n) w:=by
        have hnon:0 ≤ infiniteSideCircleQ (infiniteSideCenter n) w:=Complex.normSq_nonneg _
        nlinarith
      exact ⟨n,w,Or.inl ⟨hz.2 n,hq⟩,he⟩
  · rintro (hz|hz)
    · exact infiniteSidePolygon_contains_closed_left z hz.1 (fun n=>(hz.2 n).le)
    · obtain ⟨n,w,hw,rfl⟩:=mem_iUnion.mp hz
      have hw: w∈infiniteSideSourceAnnularPiece n:=
        hw.elim id (fun h=>infiniteSideSourceCircle_subset_annular n h)
      let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (infiniteSideSL (infiniteSideCenter n)) w
      have hi:=infiniteSideSL_circle_identity (infiniteSideCenter n) w
      change infiniteSideCircleQ (-infiniteSideCenter n) z *
        infiniteSideCircleQ (infiniteSideCenter n) w=1 at hi
      have hn:0 ≤ infiniteSideCircleQ (-infiniteSideCenter n) z:=Complex.normSq_nonneg _
      have hzq:infiniteSideCircleQ (-infiniteSideCenter n) z≤1:=by
        have hwq:1 ≤ infiniteSideCircleQ (infiniteSideCenter n) w:=hw.2
        have hp:=mul_le_mul_of_nonneg_left hwq hn
        simpa only [mul_one,hi] using hp
      have hx:=infiniteSideCircleQ_small_re (-infiniteSideCenter n) z hzq
      refine ⟨by linarith [infiniteSideCenter_two_le n],fun m=>?_⟩
      by_cases hmn:m=n
      · subst m
        simpa only [z,IsometryEquiv.inv_apply_self] using hw.1
      · have hu:z∈infiniteSideSector (infiniteSideCenter n)∪infiniteSideSector (infiniteSideCenter m):=by
          rw [infiniteSideSector_cover n m (Ne.symm hmn)]
          trivial
        have hm:1 < infiniteSideCircleQ (-infiniteSideCenter m) z:=by
          rcases hu with hn|hm
          · exact False.elim ((not_lt_of_ge hzq) hn.2)
          · exact hm.2
        exact infiniteSide_inverse_window_of_exterior _ (infiniteSideCenter_two_le m) z hm.le

theorem infiniteSideOriginalPolygon_infinitely_many_sides :
    {S | IsFuchsianPolygonSide infiniteSideData.cayleyData infiniteSideOriginalPolygon S}.Infinite :=
  infiniteSideOriginalEdge_infinitely_many_sides.mono (fun _ h=>h.1)

theorem infiniteSideGroup_not_finitelyGenerated : ¬infiniteSideGroup.FG := by
  intro hFG
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius infiniteSideGroup
  let : Group.FG infiniteSideGroup:=(Group.fg_iff_subgroup_fg _).mpr hFG
  let : Group.FG (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius infiniteSideGroup):=
    Group.fg_of_surjective (f:=e.toMonoidHom) e.surjective
  have hcFG:(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius infiniteSideGroup).FG:=
    (Group.fg_iff_subgroup_fg _).mp inferInstance
  let := finitelyGenerated_every_convexPolygon_sides_finite infiniteSideData.cayleyData
    (infiniteSideGroup_nonElementary.conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) hcFG
    infiniteSideOriginalPolygon_convexPolygon
  have hf:{S | IsFuchsianPolygonSide infiniteSideData.cayleyData infiniteSideOriginalPolygon S}.Finite:=
    Set.finite_coe_iff.mp (show Finite (FuchsianPolygonSides infiniteSideData.cayleyData infiniteSideOriginalPolygon)
      from inferInstance)
  exact infiniteSideOriginalPolygon_infinitely_many_sides hf

/-- For the explicit original whole group and the actual hyperbolic polygon. -/
theorem infiniteSideGroup_not_fg_convex_polygon_with_distinct_sides_in_one_edge :
    IsConvexFuchsianPolygon infiniteSideData.cayleyData infiniteSideOriginalPolygon ∧
    ¬infiniteSideGroup.FG ∧
    IsFuchsianPolygonEdge infiniteSideData.cayleyData infiniteSideOriginalPolygon infiniteSideOriginalEdge ∧
    (∀n:ℕ,IsFuchsianPolygonSide infiniteSideData.cayleyData infiniteSideOriginalPolygon (infiniteSideOriginalSide n)) ∧
    Function.Injective infiniteSideOriginalSide ∧
    (∀n:ℕ,infiniteSideOriginalSide n⊆infiniteSideOriginalEdge) :=
  ⟨infiniteSideOriginalPolygon_convexPolygon,infiniteSideGroup_not_finitelyGenerated,
    infiniteSideOriginalEdge_isEdge,infiniteSideOriginalSide_isSide,
    infiniteSideOriginalSide_injective,infiniteSideOriginalSide_subset_edge⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic

/-- The genuine edge/side distinction, realized by the actual group. -/
theorem infiniteSidePolygon_has_edge_with_infinitely_many_sides :
    IsConvexFuchsianPolygon infiniteSideData.cayleyData infiniteSideOriginalPolygon ∧
    IsFuchsianPolygonEdge infiniteSideData.cayleyData infiniteSideOriginalPolygon infiniteSideOriginalEdge ∧
    {S | IsFuchsianPolygonSide infiniteSideData.cayleyData infiniteSideOriginalPolygon S ∧
      S⊆infiniteSideOriginalEdge}.Infinite :=
  ⟨infiniteSideOriginalPolygon_convexPolygon,infiniteSideOriginalEdge_isEdge,
    infiniteSideOriginalEdge_infinitely_many_sides⟩

end LowDimensionalTopology.Geometry.Fuchsian
