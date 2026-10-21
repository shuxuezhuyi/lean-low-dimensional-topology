/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetFibreRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
open Set
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- At a point on one genuine polygon side, every other incident side is
its original predecessor or successor, at the corresponding actual vertex. -/
theorem generalSignature_cut_side_incidence
    {n : ℕ}
    (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (i : Fin n)
    (z : ℍ) (hz : z ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q (finRotate n i))
    (a : (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).Side) (ha : z ∈ a.val) :
    a = _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q (finRotate n i) ∨
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) = Q.vertices (finRotate n i) ∧
        a = _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q i) ∨
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) = Q.vertices (finRotate n (finRotate n i)) ∧
        a = _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q (finRotate n (finRotate n i))) := by
  let k := finRotate n i
  let j := finRotate n k
  let E := _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q
  by_cases hcut : a = E k
  · exact Or.inl hcut
  obtain ⟨r, rfl⟩ := E.surjective a
  have hrk : r ≠ k := fun h => hcut (congrArg E h)
  have hv := _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_common_sides_vertex Q hrk.symm hz ha
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈ range Q.vertices at hv
  obtain ⟨v, hv⟩ := hv
  have hlabels (b : (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q).Side) (hb : z ∈ b.val) :
      b = E ((finRotate n).symm v) ∨ b = E v :=
    cofiniteJordan_vertex_side_labels Q v (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) hv b
      (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using hb)
  rcases hlabels (E k) hz with hprev | hnext
  · have hkv : k = (finRotate n).symm v := E.injective hprev
    have hvj : v = j := by
      change v = finRotate n k
      rw [hkv, Equiv.apply_symm_apply]
    rcases hlabels (E r) ha with hr | hr
    · have hrk' : r = k := E.injective (hr.trans hprev.symm)
      exact (hrk hrk').elim
    · exact Or.inr (Or.inr ⟨hv.symm.trans (congrArg Q.vertices hvj), by rw [hr, hvj]⟩)
  · have hkv : k = v := E.injective hnext
    rcases hlabels (E r) ha with hr | hr
    · refine Or.inr (Or.inl ⟨hv.symm.trans (congrArg Q.vertices hkv.symm), ?_⟩)
      rw [hr, ← hkv]
      exact congrArg E ((finRotate n).symm_apply_apply i)
    · exact (hcut (hr.trans hnext.symm)).elim

/-- A genuine isometry preserving a nondegenerate actual polygon side
also preserves its complete native geodesic support. -/
theorem generalSignature_side_image_support
    {n : ℕ}
    (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (i : Fin n)
    (F : ℍ ≃ᵢ ℍ) (hF : F '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i = _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i) :
    F '' (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier = (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier := by
  obtain ⟨A, hA⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.isometry_exists_realGL F.isometry
  obtain ⟨x, hx, y, hy, hxy⟩ := _root_.LowDimensionalTopology.Geometry.Polygon.nativeCompactifiedSide_nontrivial (Q.vertices i)
    (Q.vertices (finRotate n i)) (Q.vertices_injective.ne (Q.next_ne_self i).symm)
  have he (z : ℍ) : F z = A • z := congrFun hA z
  have hline : (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).realGLMap A = _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.eq_of_two_points _ _ (F.injective.ne hxy)
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
      exact ⟨x, _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i hx, (he x).symm⟩
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
      exact ⟨y, _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i hy, (he y).symm⟩
    · exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i (hF ▸ mem_image_of_mem F hx)
    · exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i (hF ▸ mem_image_of_mem F hy)
  calc
    F '' (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier =
        (fun z : ℍ => A • z) '' (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier := by rw [hA]
    _ = ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).realGLMap A).carrier :=
      ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).realGLMap_carrier A).symm
    _ = (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier := congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier hline

/-- The actual integer-power saturation of a set is invariant under its
actual generator, with both inclusions witnessed by consecutive powers. -/
theorem generalSignature_zpow_saturation_image (F : ℍ ≃ᵢ ℍ) (C : Set ℍ) :
    F '' (⋃ m : ℤ, (F ^ m) '' C) = ⋃ m : ℤ, (F ^ m) '' C := by
  apply subset_antisymm
  · rintro _ ⟨_, hy, rfl⟩
    obtain ⟨m, z, hz, rfl⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨1 + m, z, hz, by rw [zpow_one_add]; rfl⟩
  · intro y hy
    obtain ⟨m, z, hz, rfl⟩ := mem_iUnion.mp hy
    refine ⟨(F ^ (m - 1)) z, mem_iUnion.mpr ⟨m - 1, z, hz, rfl⟩, ?_⟩
    change (F * F ^ (m - 1)) z = (F ^ m) z
    rw [← zpow_one_add, show (1 : ℤ) + (m - 1) = m by omega]

variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
  (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
  (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)

local notation "Qcore" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
  (generalCoreTheta_mem g orders s t ho hdef) hd hb
local notation "Pcore" => _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Qcore
local notation "Saux" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb
local notation "Ecore" => _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Qcore
local notation "idx" => generalCoreBoundarySideIndex g orders s t
local notation "Ccut" => generalCoreCutSegment g orders s t ho hdef d hd hb

/-- The third actual side in a boundary block is paired with its first side. -/
theorem generalCoreBoundarySideIndex_pair_two (j : Fin t) :
    generalCoreAuxPairing g orders s t (idx j 2) = idx j 0 := by
  have h := generalCoreAuxPairing_involutive g orders s t (idx j 0)
  rwa [generalCoreBoundarySideIndex_pair_zero] at h

/-- Every actual original gluing step at one of the two right corners or
on the cut keeps its point on that same original cut segment. -/
theorem generalCoreCutSegment_side_step (j : Fin t) (z : ℍ) (hz : z ∈ Ccut j)
    (a : (Pcore).Side) (ha : z ∈ a.val) : (Saux).element a z ∈ Ccut j := by
  let θ := generalCoreTheta g orders s t
  let hθ := generalCoreTheta_mem g orders s t ho hdef
  let ρ := generalCoreAuxPairing g orders s t
  have hn0 := generalCoreBoundarySideIndex_next_zero g orders s t j
  have hn1 := generalCoreBoundarySideIndex_next_one g orders s t j
  have hinc := generalSignature_cut_side_incidence Qcore (idx j 0) z
    (by simpa only [hn0, generalCoreCutSegment] using hz) a ha
  simp only [hn0, hn1] at hinc
  have he (r : Fin 3) : (Saux).element (Ecore (idx j r)) =
      cofiniteTangentPairingElement θ d hθ hd hb (idx j r) (ρ (idx j r)) :=
    cofiniteTangentialJordanSidePairing_element_index θ d hθ hd hb ρ
      (generalCoreAuxPairing_involutive g orders s t)
      (generalCoreAuxPairing_angle_profile g orders s t) _
  rcases hinc with hcut | ⟨hv, rfl⟩ | ⟨hv, rfl⟩
  · have hpaired : (Saux).paired a = a := by
      rw [hcut]
      change Ecore (ρ ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Qcore).symm (Ecore (idx j 1)))) = Ecore (idx j 1)
      rw [Equiv.symm_apply_apply, generalCoreBoundarySideIndex_pair_one]
    have hside := (Saux).side_image a
    have hm : (Saux).element a z ∈ ((Saux).paired a).val := by
      rw [← hside]
      exact ⟨z, ha, rfl⟩
    rw [hpaired, hcut] at hm
    rw [hcut]
    exact hm
  · rw [he, generalCoreBoundarySideIndex_pair_zero]
    have hr : θ (finRotate _ (idx j 0)) = θ (idx j 2) := by
      dsimp only [θ]
      rw [hn0, generalCoreBoundarySideIndex_angle, generalCoreBoundarySideIndex_angle]
      norm_num
    have hright := cofiniteTangentPairingClosedIsometry_vertex_right θ d hθ hd hb
      (idx j 0) (idx j 2) hr
    rw [hn0, ← hv, _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry.finite_commutes,
      cofiniteTangentPairingClosedIsometry_finite, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] at hright
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc _) ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment ((Qcore).vertices (idx j 1))
        ((Qcore).vertices (finRotate _ (idx j 1)))
    rw [hright, hn1]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_right_mem _ _
  · rw [he, generalCoreBoundarySideIndex_pair_two]
    have hl : θ (idx j 2) = θ (finRotate _ (idx j 0)) := by
      dsimp only [θ]
      rw [hn0, generalCoreBoundarySideIndex_angle, generalCoreBoundarySideIndex_angle]
      norm_num
    have hleft := cofiniteTangentPairingElement_vertex θ d hθ hd hb
      (idx j 2) (idx j 0) hl (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) hv.symm
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc, hn0] at hleft
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc _) ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment ((Qcore).vertices (idx j 1))
        ((Qcore).vertices (finRotate _ (idx j 1)))
    rw [← hleft]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem _ _

/-- The actual full original gluing relation retains each boundary-cut
label, including all four copies at either finite right corner. -/
theorem generalCoreCutSegment_gluing_iff (j : Fin t) (a b : (Saux).Copy)
    (hab : Relation.EqvGen (Saux).Step a b) :
    a.2.val ∈ Ccut j ↔ b.2.val ∈ Ccut j := by
  have hstep (a b : (Saux).Copy) (hab : (Saux).Step a b)
      (ha : a.2.val ∈ Ccut j) : b.2.val ∈ Ccut j := by
    rcases hab with rfl | ⟨side, hside, hpoint, _⟩
    · exact ha
    · rw [hpoint]
      exact generalCoreCutSegment_side_step g orders s t ho hdef d hd hb j a.2.val ha side hside
  induction hab with
  | rel a b hab => exact ⟨hstep a b hab, hstep b a ((Saux).step_symm hab)⟩
  | refl a => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ihab ihbc => exact ihab.trans ihbc

/-- A point of the original closed auxiliary polygon lies on an actual
wall precisely when it lies on one of its own finitely many actual cuts.
The global implication follows from developing injectivity and the genuine
original gluing chain, rather than from an assumed wall-incidence census. -/
theorem generalCoreAux_carrier_wall_iff (x : ℍ) (hx : x ∈ (Pcore).carrier) :
    x ∈ generalCoreCutWallUnion g orders s t ho hdef d hd hb ↔
      x ∈ ⋃ j : Fin t, Ccut j := by
  constructor
  · intro hxW
    obtain ⟨γ, z, hz, he⟩ := mem_iUnion.mp hxW
    obtain ⟨j, hz⟩ := mem_iUnion.mp hz
    let side := Ecore (idx j 1)
    let a : (Saux).Copy := (γ, ⟨z, (Pcore).side_subset_carrier side hz⟩)
    let b : (Saux).Copy := (1, ⟨x, hx⟩)
    have hproject : (Saux).project a = (Saux).project b := by
      apply generalCoreAux_evaluation_injective g orders s t ho hdef d hd hb
      exact he
    have hchain := ((Saux).project_eq_iff a b).mp hproject
    exact mem_iUnion.mpr ⟨j,
      (generalCoreCutSegment_gluing_iff g orders s t ho hdef d hd hb j a b hchain).mp hz⟩
  · intro hxC
    exact mem_iUnion.mpr ⟨1, x, hxC, rfl⟩

/-- The original closed-polygon wall incidence has an actual finite support
cover. This is the boundary input for the actual target-core argument. -/
theorem generalCoreAux_carrier_wall_subset_axes :
    (Pcore).carrier ∩ generalCoreCutWallUnion g orders s t ho hdef d hd hb ⊆
      ⋃ j : Fin t, (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Qcore (idx j 1)).carrier := by
  rintro x ⟨hxQ, hxW⟩
  obtain ⟨j, hxj⟩ := mem_iUnion.mp
    ((generalCoreAux_carrier_wall_iff g orders s t ho hdef d hd hb x hxQ).mp hxW)
  exact mem_iUnion.mpr ⟨j, _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Qcore (idx j 1) hxj⟩

end LowDimensionalTopology.Geometry.Fuchsian
