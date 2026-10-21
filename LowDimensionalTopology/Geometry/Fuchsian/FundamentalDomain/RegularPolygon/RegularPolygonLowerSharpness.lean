/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.RegularPolygon.RegularPolygonCycles
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CompactPolygonTranslates
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaActualSignature
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaFirstKind
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.CompactSignatureFiniteGeneration
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleSupergroups
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.OriginalPolygonSideCounts
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.FirstKindShortSignatures
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ParabolicFundamentalBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.Geodesic.ClosedCurveLengthBounds
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleWindings
public import LowDimensionalTopology.Geometry.Polygon.Area.PolygonArea
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
open Set MeasureTheory Topology
open scoped UpperHalfPlane Pointwise Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance regularSharpSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance regularSharpSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

theorem regularPolygon_original_native_compact_tiles (k : ℕ) (hk : 2 ≤ k) :
    letI := (regularPolygonHalfPlaneData k hk).nativeAction
    ∀ K : Set ℍ, IsCompact K →
      {g : regularPolygonMobiusGroup k hk |
        (g • closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (regularCyclePolygon (4*k) (by omega)).interior) ∩ K).Nonempty}.Finite := by
  let regularSharpNativeAction := (regularPolygonHalfPlaneData k hk).nativeAction
  let regularSharpNativeDiscrete : DiscreteTopology (regularPolygonSidePairing k hk).Generated :=
    (regularPolygon_native_fundamental k hk).1
  let Q := regularCyclePolygon (4*k) (show 4 < 4*k by omega)
  let hf := regularCyclePolygon_vertices_finite (show 4 < 4*k by omega)
  let e := regularPolygonGroupEquiv k hk
  intro K hK
  have hcomp : IsCompact (closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior)) := by
    change IsCompact (closure (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior)
    rw [← _root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q hf]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf
  have hfin := (native_compact_translate_hits_finite (regularPolygonSidePairing k hk).Generated hcomp hK).image e
  apply hfin.subset
  rintro g ⟨x, ⟨y, hy, hgy⟩, hxK⟩
  refine ⟨e.symm g, ⟨x, ⟨y, hy, ?_⟩, hxK⟩, e.apply_symm_apply g⟩
  have he := regularPolygonGroupEquiv_action k hk (e.symm g) y
  change e (e.symm g) • y = (e.symm g).val y at he
  rw [e.apply_symm_apply] at he
  exact he.symm.trans hgy

theorem regularPolygonDisc_convex (k : ℕ) (hk : 2 ≤ k) :
    IsConvexFuchsianPolygon (regularPolygonDiscData k hk) (regularPolygonDiscDomain k hk) := by
  apply (regularPolygonHalfPlaneData k hk).cayley_polygon
    (regularPolygon_original_native_fundamental k hk) ?_
    (regularPolygon_original_native_compact_tiles k hk)
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex _).mpr
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph ⁻¹'
    (regularCyclePolygon (4*k) (by omega)).interior)
  rw [image_preimage_eq _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.surjective]
  exact regularCyclePolygon_isConvex (by omega)

theorem regularPolygonDisc_closure_compact (k : ℕ) (hk : 2 ≤ k) :
    IsCompact (closure (regularPolygonDiscDomain k hk)) := by
  let Q := regularCyclePolygon (4*k) (show 4 < 4*k by omega)
  let hf := regularCyclePolygon_vertices_finite (show 4 < 4*k by omega)
  let e := (regularPolygonHalfPlaneData k hk).cayleyCoordinate
  change IsCompact (closure (e '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior)))
  rw [← e.image_closure]
  change IsCompact (e '' closure (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q
    hf).interior)
  rw [← _root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q hf]
  exact (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf).image e.continuous

theorem regularPolygonDisc_area_exact (k : ℕ) (hk : 2 ≤ k) :
    (regularPolygonDiscData k hk).area (regularPolygonDiscDomain k hk) =
      ENNReal.ofReal ((4*(k:ℝ)-4)*Real.pi) := by
  let Q := regularCyclePolygon (4*k) (show 4 < 4*k by omega)
  have hopen := (regularPolygonDisc_fundamental k hk).isOpen
  rw [(regularPolygonDiscData k hk).area_apply _ hopen.measurableSet,
    regularPolygonDiscDomain_finite]
  change Q.area = _
  rw [Q.area_eq_original_angle_defect]
  have hang : ∀ i : Fin (4*k), Q.angle i = Real.pi / (2*k) :=
    regularCyclePolygon_angle_fourk k hk
  simp_rw [hang]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  have hk0 : (k:ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

private theorem finitePolygon_pairing_nonvertex {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon
  n)
    (hf : ∀i, ‖(Q.vertices i : ℂ)‖ < 1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ ≃ᵢ ℍ)
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (s : (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).Side) (x : ℍ)
    (hx : x ∈ s.val) (hv : x ∉ range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf)) :
    S.generator s • x ∉ range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf) := by
  rintro ⟨i, hi⟩
  have hm : S.generator s • x ∈ (S.paired s).val := by
    rw [← S.generator_side_image]
    exact ⟨x, hx, rfl⟩
  obtain ⟨j, hj⟩ := _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPairing_preserves_vertices Q hf S i (S.paired s) (hi ▸ hm)
  apply hv
  refine ⟨j, ?_⟩
  rw [hj]
  change S.generator (S.paired s) • _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i = x
  rw [S.generator_paired, hi]
  exact inv_smul_smul _ _

theorem regularPolygon_native_closed_point_free (k : ℕ) (hk : 2 ≤ k)
    (x : ℍ)
    (hx : x ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega))).carrier)
    (g : (regularPolygonSidePairing k hk).Generated) (hg : g.val x = x) : g = 1 := by
  let Q := regularCyclePolygon (4*k) (show 4 < 4*k by omega)
  let hf := regularCyclePolygon_vertices_finite (show 4 < 4*k by omega)
  let P := _root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S := regularPolygonSidePairing k hk
  let p : P.Point := ⟨x, hx⟩
  by_cases hv : x ∈ range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf)
  · obtain ⟨i, rfl⟩ := hv
    let e := (regularPolygonHalfPlaneData k hk).cayleyCoordinate
    let E := regularPolygonDiscGroupEquiv k hk
    have hfix : E g • regularPolygonDiscVertex k hk i = regularPolygonDiscVertex k hk i := by
      change E g • e (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf
        i) = e (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)
      rw [← regularPolygonDiscCoordinate_equivariant, hg]
    have he := (isAccidentalFuchsianPoint_iff_no_stabilizer _ _).mp
      (regularPolygonDisc_all_vertices_accidental k hk i) (E g) hfix
    exact E.injective (he.trans E.map_one.symm)
  let regularSharpGeneratedIsometric : IsIsometricSMul S.Generated ℍ := ⟨fun h => h.val.isometry⟩
  have hA := _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_local_tessellation Q hf S
    (regularPolygon_opposite_side_neighborhoods k hk) (regularPolygon_canonical_cycle_conditions k hk)
  have hEval : Function.Injective S.evaluation :=
    (hA.covering_homeomorph_of_compact S
      (S.native_metric_assumptions
        (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isOpen Q hf)
        (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isConnected Q hf))
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q
        hf).le (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf)).2.injective
  have hproj : S.project (g,p) = S.project (1,p) := by
    apply hEval
    change g.val x = x
    exact hg
  by_cases hI : x ∈ P.interior
  · have hm : (g,p) ∈ S.project ⁻¹' {S.project (1,p)} := hproj
    rw [S.project_fiber_eq_singleton_of_interior (1,p) hI] at hm
    exact congrArg Prod.fst hm
  have hB : x ∈ P.boundary := hx.resolve_left hI
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := mem_sUnion.mp hB
  let s := _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i
  have hs : x ∈ s.val := hi
  have hmate := finitePolygon_pairing_nonvertex Q hf S s x hs hv
  have hu : ∀t : P.Side, x ∈ t.val → t = s := by
    intro t ht
    obtain ⟨j, rfl⟩ := (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).surjective t
    by_cases he : i = j
    · exact congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf) he.symm
    · exact (hv (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_common_sides_vertex Q hf he hi ht)).elim
  have hw : ∀t : P.Side, (S.sideMateCopy (1,p) s hs).2.val ∈ t.val → t = S.paired s := by
    intro t ht
    let y := S.generator s • x
    have hy : y ∈ (S.paired s).val := by
      rw [← S.generator_side_image]
      exact ⟨x, hs, rfl⟩
    obtain ⟨j, hj⟩ := (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).surjective (S.paired
      s)
    obtain ⟨l, rfl⟩ := (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).surjective t
    by_cases he : j = l
    · exact (congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf) he.symm).trans hj
    · have hyj : y ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q j := by
        change y ∈ ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf) j).val
        rw [hj]
        exact hy
      exact (hmate (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_common_sides_vertex Q hf he hyj
        ht)).elim
  have hm : (g,p) ∈ S.project ⁻¹' {S.project (1,p)} := hproj
  rw [S.project_fiber_eq_side_pair (1,p) s hs hu hw] at hm
  rcases hm with he | he
  · exact congrArg Prod.fst he
  · have hcoord : x = S.generator s • x := congrArg (fun a : S.Copy => a.2.val) he
    have hother : x ∈ (S.paired s).val := by
      rw [hcoord, ← S.generator_side_image]
      exact ⟨x, hs, rfl⟩
    rw [regularPolygonSidePairing_paired_index] at hother
    exact (hv (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_common_sides_vertex Q hf
      (regularOppositeIndex_ne k hk i).symm hi hother)).elim

theorem regularPolygonDisc_closed_points_accidental (k : ℕ) (hk : 2 ≤ k)
    (x : (regularPolygonDiscData k hk).domain.carrier)
    (hx : x ∈ closure (regularPolygonDiscDomain k hk)) :
    IsAccidentalFuchsianPoint (regularPolygonDiscData k hk) x := by
  let Q := regularCyclePolygon (4*k) (show 4 < 4*k by omega)
  let hf := regularCyclePolygon_vertices_finite (show 4 < 4*k by omega)
  let e := (regularPolygonHalfPlaneData k hk).cayleyCoordinate
  let E := regularPolygonDiscGroupEquiv k hk
  change x ∈ closure (e '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior)) at hx
  rw [← e.image_closure] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hzP : z ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier := by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier]
    exact hz
  rw [isAccidentalFuchsianPoint_iff_no_stabilizer]
  intro g hg
  have hfix : (E.symm g).val z = z := by
    apply e.injective
    rw [regularPolygonDiscCoordinate_equivariant, E.apply_symm_apply]
    exact hg
  have hh := regularPolygon_native_closed_point_free k hk z hzP (E.symm g) hfix
  have he := congrArg E hh
  simpa only [E.apply_symm_apply, E.map_one] using he

theorem regularPolygonDisc_points_accidental (k : ℕ) (hk : 2 ≤ k)
    (x : (regularPolygonDiscData k hk).domain.carrier) :
    IsAccidentalFuchsianPoint (regularPolygonDiscData k hk) x := by
  let P := regularPolygonDiscData k hk
  let D := regularPolygonDiscDomain k hk
  have hx : x ∈ ⋃g : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (regularPolygonMobiusGroup k hk),
      (fun y : P.domain.carrier => g • y) '' closure D := by
    rw [(regularPolygonDisc_fundamental k hk).closure_cover]
    trivial
  obtain ⟨g, y, hy, hgy⟩ := mem_iUnion.mp hx
  change g • y = x at hgy
  have hacc := regularPolygonDisc_closed_points_accidental k hk y hy
  rw [isAccidentalFuchsianPoint_iff_no_stabilizer] at hacc ⊢
  intro h hh
  have hconj : (g⁻¹*h*g) • y = y := by
    rw [mul_smul, mul_smul, hgy, hh, ← hgy, inv_smul_smul]
  have he := hacc (g⁻¹*h*g) hconj
  have hback := congrArg (fun a => g*a*g⁻¹) he
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_one,
    inv_mul_cancel, mul_inv_cancel] using hback

theorem regularPolygonDisc_no_elliptic (k : ℕ) (hk : 2 ≤ k)
    (f : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (regularPolygonMobiusGroup k hk)) :
    ¬ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val := by
  intro hf
  obtain ⟨w, hw, _⟩ := elliptic_unitDisc_existsUnique_fixed f.val hf
    ((regularPolygonDiscData k hk).image_eq f)
  exact regularPolygonDisc_points_accidental k hk w ⟨f, hf, Subtype.ext hw⟩

theorem regularPolygonDisc_no_self_paired (k : ℕ) (hk : 2 ≤ k)
    (s : FuchsianPolygonSides (regularPolygonDiscData k hk) (regularPolygonDiscDomain k hk)) :
    fuchsianPairedSide (regularPolygonDisc_convex k hk) s ≠ s := by
  intro hs
  obtain ⟨x, _hx, hfix, _hi⟩ :=
    (fuchsianPairedSide_eq_self_iff_fixed_interior (regularPolygonDisc_convex k hk) s).mp hs
  have he := (isAccidentalFuchsianPoint_iff_no_stabilizer _ _).mp
    (regularPolygonDisc_points_accidental k hk x) _ hfix
  exact (fuchsianSideElement_spec (regularPolygonDisc_convex k hk) s).1 he

theorem regularPolygonDisc_no_parabolic (k : ℕ) (hk : 2 ≤ k)
    (f : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (regularPolygonMobiusGroup k hk)) :
    ¬ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val := by
  intro hf
  let P := regularPolygonDiscData k hk
  let D := regularPolygonDiscDomain k hk
  obtain ⟨ξ, hξ⟩ := hf.2
  have hfix : f.val.val ξ = ξ := (hξ ξ).mpr rfl
  have hfront := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_fixed_mem_disc_frontier f.val hf _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc
    (P.image_eq f) hfix
  obtain ⟨g, hg⟩ := (regularPolygonDisc_convex k hk).locallyFinite.parabolic_fixedPoint_orbit_mem_closure
    f hf ξ hfix
  have hcompact : IsCompact ((Subtype.val : P.domain.carrier →
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' closure D) :=
    (regularPolygonDisc_closure_compact k hk).image continuous_subtype_val
  have hsub : closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    '' D) ⊆
      (Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' closure D :=
    closure_minimal (image_mono subset_closure) hcompact.isClosed
  obtain ⟨x, _hx, hxe⟩ := hsub hg
  have hin : ξ ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
    have hx' := P.invariant g⁻¹ x.val x.property
    change g⁻¹.val.val x.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc at hx'
    have he : g⁻¹.val.val x.val = ξ := by
      rw [hxe]
      exact g.val.val.symm_apply_apply ξ
    rwa [he] at hx'
  exact hfront.2 (by rwa [_root_.LowDimensionalTopology.Geometry.Mobius.isOpen_extendedUnitDisc.interior_eq])

theorem regularPolygonDisc_actual_signature (k : ℕ) (hk : 2 ≤ k) :
    HasCofiniteFuchsianSignature (regularPolygonDiscData k hk).asFuchsianDisc k [] 0 := by
  let P := regularPolygonDiscData k hk
  let D := regularPolygonDiscDomain k hk
  have ha : P.area D ≠ ⊤ := by
    rw [regularPolygonDisc_area_exact]
    exact ENNReal.ofReal_ne_top
  obtain ⟨s, hb, hSig, harea⟩ := finite_area_unitDisc_signature_area P D
    (regularPolygonDisc_fundamental k hk) ha
  have hE : IsEmpty (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic) :=
    (fuchsianCyclicConjugacyClasses_isEmpty_iff P.asFuchsianDisc .elliptic).mpr
      (fun f hf => regularPolygonDisc_no_elliptic k hk ⟨f, hf⟩)
  have hP : IsEmpty (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) :=
    (fuchsianCyclicConjugacyClasses_isEmpty_iff P.asFuchsianDisc .parabolic).mpr
      (fun f hf => regularPolygonDisc_no_parabolic k hk ⟨f, hf⟩)
  have ho : s.ellipticOrders = [] := by
    apply List.length_eq_zero_iff.mp
    rw [hSig.orders_length, @Nat.card_of_isEmpty _ hE]
  have hp : s.parabolicEnds = 0 := hSig.cuspCount.trans (@Nat.card_of_isEmpty _ hP)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hnonneg : 0 ≤ (4*(k:ℝ)-4)*Real.pi :=
    mul_nonneg (by linarith) Real.pi_pos.le
  rw [regularPolygonDisc_area_exact, ENNReal.toReal_ofReal hnonneg] at harea
  simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit, ho, hp, hb, List.map_nil,
    List.sum_nil,
    Nat.cast_zero, add_zero] at harea
  have hgR : (s.genus : ℝ) = k := by nlinarith [Real.pi_pos]
  have hg : s.genus = k := by exact_mod_cast hgR
  simpa only [hg, ho, hp] using hSig

theorem regularPolygonDisc_finitelyGenerated (k : ℕ) (hk : 2 ≤ k) :
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (regularPolygonMobiusGroup k hk)).FG :=
  (regularPolygonDisc_actual_signature k hk).finitelyGenerated

theorem regularPolygonDisc_nonElementary (k : ℕ) (hk : 2 ≤ k) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (regularPolygonMobiusGroup k hk)) := by
  intro he
  let H := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (regularPolygonMobiusGroup k hk)
  let P := regularPolygonDiscData k hk
  let D := P.asFuchsianDisc
  let regularSharpCyclic : IsCyclic H := D.elementary_ellipticFree_isCyclic
    (regularPolygonDisc_no_elliptic k hk) he
  let regularSharpCommGroup : CommGroup H := IsCyclic.commGroup
  let regularSharpOppCyclic : IsCyclic Hᵐᵒᵖ :=
    (MulOpposite.opMulEquiv (M := H)).isCyclic.mp regularSharpCyclic
  have hsurj : Function.Surjective (fuchsianCuspCompletionOld D) := by
    intro x
    rcases fuchsianCuspCompletion_old_or_cusp D x with hx | ⟨c, _hc⟩
    · exact hx
    · have hP : IsEmpty (FuchsianCyclicConjugacyClasses D .parabolic) :=
        (fuchsianCyclicConjugacyClasses_isEmpty_iff D .parabolic).mpr
          (fun f hf => regularPolygonDisc_no_parabolic k hk ⟨f, hf⟩)
      exact (hP.false c).elim
  let eOld := (fuchsianCuspCompletionOld_isOpenEmbedding D).isEmbedding.toHomeomorphOfSurjective hsurj
  obtain ⟨eGenus⟩ := (regularPolygonDisc_actual_signature k hk).topologicalGenus
  let eHandle : _root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleSurface k ≃ₜ Quot (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent k) := by
    cases k with
    | zero => omega
    | succ n => exact Homeomorph.refl _
  let e := eOld.trans (eGenus.trans eHandle)
  let v := _root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleVertex k 0
  let x := e.symm v
  obtain ⟨z, hz⟩ := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection_surjective D.domain x
  let regularSharpDiscSimplyConnected : SimplyConnectedSpace D.domain.carrier :=
    _root_.LowDimensionalTopology.Geometry.Surfaces.discRiemannSurface_simplyConnected
  let E := (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomain_noElliptic_covering D.domain D.discontinuous
    (fun f hf _hn => regularPolygonDisc_no_elliptic k hk ⟨f, hf⟩)).fundamentalGroupEquiv
      (x := x) ⟨z, hz⟩
  let regularSharpQuotientCyclic : IsCyclic (FundamentalGroup
    (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain) x) :=
    E.isCyclic.mpr regularSharpOppCyclic
  let F := _root_.LowDimensionalTopology.Geometry.Surfaces.fundamentalGroupHomeomorphMulEquiv e.symm v
  let regularSharpHandleCyclic : IsCyclic (FundamentalGroup (Quot
    (_root_.LowDimensionalTopology.Geometry.Surfaces.CanonicalHandleIdent k)) v) :=
    F.isCyclic.mpr regularSharpQuotientCyclic
  let regularSharpThreeCyclic : IsCyclic (Fin 3 → Multiplicative ℤ) :=
    isCyclic_of_surjective (_root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleThreeWindingHom k hk)
      (_root_.LowDimensionalTopology.Geometry.Surfaces.canonicalHandleThreeWindingHom_surjective hk)
  let π : (Fin 3 → Multiplicative ℤ) →* Multiplicative ℤ × Multiplicative ℤ := {
    toFun := fun w => (w 0, w 1)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hπ : Function.Surjective π := fun ⟨a,b⟩ => ⟨![a,b,1], rfl⟩
  exact not_isCyclic_prod_of_infinite_nontrivial (Multiplicative ℤ) (Multiplicative ℤ)
    (isCyclic_of_surjective π hπ)

theorem regularPolygonDisc_firstKind (k : ℕ) (hk : 2 ≤ k) :
    (regularPolygonDiscData k hk).asFuchsianDisc.IsFirstKind := by
  let P := regularPolygonDiscData k hk
  let D := regularPolygonDiscDomain k hk
  have hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (regularPolygonMobiusGroup k hk))
      (fuchsianGeometricDomain P.asFuchsianDisc).carrier (geometricModelArea P.asFuchsianDisc) D := by
    rw [geometricModelArea_asUnitDisc]
    exact regularPolygonDisc_fundamental k hk
  apply fuchsian_finite_area_firstKind P.asFuchsianDisc (regularPolygonDisc_nonElementary k hk) hD
  rw [geometricModelArea_asUnitDisc]
  change (regularPolygonDiscData k hk).area (regularPolygonDiscDomain k hk) ≠ ⊤
  rw [regularPolygonDisc_area_exact]
  exact ENNReal.ofReal_ne_top

private theorem regularPolygon_evaluation_injective (k : ℕ) (hk : 2 ≤ k) :
    Function.Injective (regularPolygonSidePairing k hk).evaluation := by
  let Q := regularCyclePolygon (4*k) (show 4 < 4*k by omega)
  let hf := regularCyclePolygon_vertices_finite (show 4 < 4*k by omega)
  let S := regularPolygonSidePairing k hk
  let regularSharpEvaluationIsometric : IsIsometricSMul S.Generated ℍ := ⟨fun h => h.val.isometry⟩
  have hA := _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_local_tessellation Q hf S
    (regularPolygon_opposite_side_neighborhoods k hk) (regularPolygon_canonical_cycle_conditions k hk)
  exact (hA.covering_homeomorph_of_compact S
    (S.native_metric_assumptions
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isOpen Q hf)
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isConnected Q hf))
    (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q
      hf).le (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf)).2.injective

theorem regularPolygon_native_nonvertex_incident (k : ℕ) (hk : 2 ≤ k)
    (x : ℍ)
    (hx : x ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega))).carrier)
    (hv : x ∉ range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega)))) :
    ∃ b : (regularPolygonSidePairing k hk).Generated,
      ∀ g : (regularPolygonSidePairing k hk).Generated,
        x ∈ g • (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (regularCyclePolygon (4*k) (by omega))
          (regularCyclePolygon_vertices_finite (by omega))).carrier → g = 1 ∨ g = b := by
  let Q := regularCyclePolygon (4*k) (show 4 < 4*k by omega)
  let hf := regularCyclePolygon_vertices_finite (show 4 < 4*k by omega)
  let P := _root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S := regularPolygonSidePairing k hk
  let p : P.Point := ⟨x, hx⟩
  have hproj (g : S.Generated) (y : ℍ) (hy : y ∈ P.carrier) (he : g • y = x) :
      S.project (g,⟨y,hy⟩) = S.project (1,p) := by
    apply regularPolygon_evaluation_injective k hk
    exact he
  by_cases hI : x ∈ P.interior
  · refine ⟨1, ?_⟩
    rintro g ⟨y, hy, hgy⟩
    have hm : (g,⟨y,hy⟩) ∈ S.project ⁻¹' {S.project (1,p)} := hproj g y hy hgy
    rw [S.project_fiber_eq_singleton_of_interior (1,p) hI] at hm
    exact Or.inl (congrArg Prod.fst hm)
  have hB : x ∈ P.boundary := hx.resolve_left hI
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := mem_sUnion.mp hB
  let s := _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i
  have hs : x ∈ s.val := hi
  have hmate := finitePolygon_pairing_nonvertex Q hf S s x hs hv
  have hu : ∀t : P.Side, x ∈ t.val → t = s := by
    intro t ht
    obtain ⟨j, rfl⟩ := (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).surjective t
    by_cases he : i = j
    · exact congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf) he.symm
    · exact (hv (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_common_sides_vertex Q hf he hi ht)).elim
  have hw : ∀t : P.Side, (S.sideMateCopy (1,p) s hs).2.val ∈ t.val → t = S.paired s := by
    intro t ht
    let y := S.generator s • x
    have hy : y ∈ (S.paired s).val := by
      rw [← S.generator_side_image]
      exact ⟨x, hs, rfl⟩
    obtain ⟨j, hj⟩ := (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).surjective (S.paired
      s)
    obtain ⟨l, rfl⟩ := (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).surjective t
    by_cases he : j = l
    · exact (congrArg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf) he.symm).trans hj
    · have hyj : y ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q j := by
        change y ∈ ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf) j).val
        rw [hj]
        exact hy
      exact (hmate (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_common_sides_vertex Q hf he hyj
        ht)).elim
  refine ⟨(S.generator s)⁻¹, ?_⟩
  rintro g ⟨y, hy, hgy⟩
  have hm : (g,⟨y,hy⟩) ∈ S.project ⁻¹' {S.project (1,p)} := hproj g y hy hgy
  rw [S.project_fiber_eq_side_pair (1,p) s hs hu hw] at hm
  rcases hm with he | he
  · exact Or.inl (congrArg Prod.fst he)
  · exact Or.inr (congrArg Prod.fst he)

theorem regularPolygonDisc_original_vertex_mem_range (k : ℕ) (hk : 2 ≤ k)
    (x : (regularPolygonDiscData k hk).domain.carrier)
    (hx : IsFuchsianPolygonVertex (regularPolygonDiscData k hk) (regularPolygonDiscDomain k hk) x) :
    x ∈ range (regularPolygonDiscVertex k hk) := by
  let Q := regularCyclePolygon (4*k) (show 4 < 4*k by omega)
  let hf := regularCyclePolygon_vertices_finite (show 4 < 4*k by omega)
  let C := _root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let P := regularPolygonDiscData k hk
  let D := regularPolygonDiscDomain k hk
  let e := (regularPolygonHalfPlaneData k hk).cayleyCoordinate
  let E := regularPolygonDiscGroupEquiv k hk
  obtain ⟨z, rfl⟩ := e.surjective x
  have hclosed (w : ℍ) : e w ∈ closure D ↔ w ∈ C.carrier := by
    change e w ∈ closure (e '' C.interior) ↔ _
    rw [← e.image_closure, e.injective.mem_set_image, ←
      _root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier]
  obtain ⟨f, h, hf1, hh1, hfh, htriple⟩ := hx
  have hmem : e z ∈ closure D ∩ fuchsianDomainTile P D f ∩ fuchsianDomainTile P D h := by
    rw [htriple]
    exact mem_singleton _
  have hz := (hclosed z).mp hmem.1.1
  by_contra hn
  have hv : z ∉ range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf) := by
    rintro ⟨i, rfl⟩
    exact hn ⟨i,rfl⟩
  obtain ⟨b, hb⟩ := regularPolygon_native_nonvertex_incident k hk z hz hv
  have htile (g : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (regularPolygonMobiusGroup k hk))
      (hg : e z ∈ fuchsianDomainTile P D g) : z ∈ E.symm g • C.carrier := by
    obtain ⟨y, hy, hgy⟩ := hg
    obtain ⟨w, rfl⟩ := e.surjective y
    refine ⟨w, (hclosed w).mp hy, ?_⟩
    apply e.injective
    change e ((E.symm g).val w) = e z
    rw [regularPolygonDiscCoordinate_equivariant, E.apply_symm_apply]
    exact hgy
  have hfN : E.symm f ≠ 1 := by
    intro he
    apply hf1
    simpa only [E.apply_symm_apply, E.map_one] using congrArg E he
  have hhN : E.symm h ≠ 1 := by
    intro he
    apply hh1
    simpa only [E.apply_symm_apply, E.map_one] using congrArg E he
  have hfb := (hb (E.symm f) (htile f hmem.1.2)).resolve_left hfN
  have hhb := (hb (E.symm h) (htile h hmem.2)).resolve_left hhN
  exact hfh (E.symm.injective (hfb.trans hhb.symm))

theorem regularPolygonDisc_refined_endpoints_mem_range (k : ℕ) (hk : 2 ≤ k) :
    originalRefinedEndpointSet (regularPolygonDisc_convex k hk) ⊆
      range (regularCyclePolygon (4*k) (by omega)).vertices := by
  let regularSharpClosedDiscT2 : T2Space 𝕔𝔻 := Complex.UnitClosedDisc.isEmbedding_coe.t2Space
  let P := regularPolygonDiscData k hk
  let D := regularPolygonDiscDomain k hk
  let Q := regularCyclePolygon (4*k) (show 4 < 4*k by omega)
  let hf := regularCyclePolygon_vertices_finite (show 4 < 4*k by omega)
  let F : P.domain.carrier → 𝕔𝔻 := fun x => _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)
  have hcomp : IsCompact (F '' closure D) :=
    (regularPolygonDisc_closure_compact k hk).image
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.continuous.comp
        P.finiteCoordinate.continuous)
  have hside (s : FuchsianPolygonSides P D) : fuchsianSideClosedModel s ⊆ F '' closure D := by
    unfold fuchsianSideClosedModel _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure
    rw [image_image]
    apply closure_minimal _ hcomp.isClosed
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, _hg, he⟩ := s.property.1
    exact ⟨x, (he ▸ hx).1, rfl⟩
  have hmodel (i : Fin (4*k)) : F (regularPolygonDiscVertex k hk i) = Q.vertices i := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate
      ((regularPolygonHalfPlaneData k hk).cayleyCoordinate
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i))) = _
    rw [(regularPolygonHalfPlaneData k hk).cayleyCoordinate_finite]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_coordinate Q hf i
  have hpoint (v : OriginalRefinedSide (regularPolygonDisc_convex k hk))
      (p : 𝕔𝔻) (hp : p = v.leftEndpoint ∨ p = v.rightEndpoint) : p ∈ range Q.vertices := by
    have hcp : p ∈ fuchsianSideClosedModel v.val.1 := by
      apply v.carrier_subset_original
      rcases hp with rfl | rfl
      · exact v.endpoints_mem_carrier.1
      · exact v.endpoints_mem_carrier.2
    obtain ⟨x, _hx, hxp⟩ := hside v.val.1 hcp
    have heq : fuchsianSideClosedModel v.val.1 = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment v.leftEndpoint v.rightEndpoint := by
      have hv := v.carrier_eq_endpoints
      simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.OriginalRefinedSide.carrier,
        regularPolygonDisc_no_self_paired k hk,
        dite_false] using hv
    have hvertex : IsFuchsianPolygonVertex P D x := by
      rcases hp with hp | hp
      · exact (original_finite_side_endpoint_vertices (regularPolygonDisc_convex k hk) v.val.1
          _ _ v.endpoints_ne heq).1 x (hxp.trans hp)
      · exact (original_finite_side_endpoint_vertices (regularPolygonDisc_convex k hk) v.val.1
          _ _ v.endpoints_ne heq).2 x (hxp.trans hp)
    obtain ⟨i, hi⟩ := regularPolygonDisc_original_vertex_mem_range k hk x hvertex
    refine ⟨i, ?_⟩
    rw [← hmodel, hi]
    exact hxp
  rintro p (⟨v, rfl⟩ | ⟨v, rfl⟩)
  · exact hpoint v _ (Or.inl rfl)
  · exact hpoint v _ (Or.inr rfl)

theorem regularPolygonDisc_original_side_count (k : ℕ) (hk : 2 ≤ k) :
    Nat.card (FuchsianPolygonSides (regularPolygonDiscData k hk) (regularPolygonDiscDomain k hk)) = 4*k := by
  classical
  let P := regularPolygonDiscData k hk
  let D := regularPolygonDiscDomain k hk
  let hD := regularPolygonDisc_convex k hk
  let Q := regularCyclePolygon (4*k) (show 4 < 4*k by omega)
  have ha : P.area D ≠ ⊤ := by
    change (regularPolygonDiscData k hk).area (regularPolygonDiscDomain k hk) ≠ ⊤
    rw [regularPolygonDisc_area_exact]
    exact ENNReal.ofReal_ne_top
  obtain ⟨J, e, _hc, hv, _hs⟩ := finite_area_original_cyclic_side_model hD ha
  have hsub : range (originalCyclicVertex hD J hv) ⊆ range Q.vertices := by
    rw [range_originalCyclicVertex]
    exact regularPolygonDisc_refined_endpoints_mem_range k hk
  have hJn : (range (originalCyclicVertex hD J hv)).ncard = J.n := by
    rw [ncard_range_of_injective (originalCyclicVertex_injective hD J hv)]
    simp only [Nat.card_eq_fintype_card, ZMod.card]
  have hQn : (range Q.vertices).ncard = 4*k := by
    rw [ncard_range_of_injective Q.vertices_injective]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  have hle : J.n ≤ 4*k := by
    rw [← hJn, ← hQn]
    exact ncard_le_ncard hsub (finite_range _)
  have hcount := originalCyclic_sideCount hD ha J e
  have hself : Nat.card {s : FuchsianPolygonSides P D // fuchsianPairedSide hD s = s} = 0 := by
    let regularSharpSelfEmpty : IsEmpty {s : FuchsianPolygonSides P D // fuchsianPairedSide hD s = s} :=
      ⟨fun s => regularPolygonDisc_no_self_paired k hk s.val s.property⟩
    exact Nat.card_of_isEmpty
  rw [hself, add_zero] at hcount
  have hlower := (convexPolygon_sideCard_bounds_of_cofinite_signature P (regularPolygonDisc_finitelyGenerated k hk)
    (regularPolygonDisc_firstKind k hk) k [] 0 (regularPolygonDisc_actual_signature k hk)
    hD (regularPolygonDisc_no_self_paired k hk)).2.1 rfl
  omega

theorem regularPolygon_lower_side_bound_attained (k : ℕ) (hk : 2 ≤ k) :
    HasCofiniteFuchsianSignature (regularPolygonDiscData k hk).asFuchsianDisc k [] 0 ∧
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (regularPolygonMobiusGroup k hk)).FG ∧
      (regularPolygonDiscData k hk).asFuchsianDisc.IsFirstKind ∧
      ∃hD : IsConvexFuchsianPolygon (regularPolygonDiscData k hk) (regularPolygonDiscDomain k hk),
        (∀s, fuchsianPairedSide hD s ≠ s) ∧
        Nat.card (FuchsianPolygonSides (regularPolygonDiscData k hk) (regularPolygonDiscDomain k hk)) = 4*k := by
  exact ⟨regularPolygonDisc_actual_signature k hk, regularPolygonDisc_finitelyGenerated k hk,
    regularPolygonDisc_firstKind k hk, regularPolygonDisc_convex k hk,
    regularPolygonDisc_no_self_paired k hk, regularPolygonDisc_original_side_count k hk⟩

end LowDimensionalTopology.Geometry.Fuchsian
