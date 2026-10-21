/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureSidePairingProfile
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.SignatureBoundaryAxisTiling
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureBoundaryTranslation
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureBoundaryLabels
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.SignatureCutWallChamber
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
open Set
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The actual auxiliary cofinite polygon has a locally finite family of
original native closed tiles. Its projective coordinate is a genuine faithful
equivariant homeomorphism, so no native local-finiteness premise is inserted. -/
theorem generalCoreAux_native_closed_tiles_locallyFinite
    (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi) :
    let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
      (generalCoreTheta_mem g orders s t ho hdef) hd hb
    let S := generalCoreAuxSidePairing g orders s t ho hdef d hd hb
    LocallyFinite (fun γ : S.Generated =>
      γ.val '' closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior)) := by
  let θ := generalCoreTheta g orders s t
  let hθ := generalCoreTheta_mem g orders s t ho hdef
  let ρ := generalCoreAuxPairing g orders s t
  let hρ := generalCoreAuxPairing_involutive g orders s t
  let hθρ := generalCoreAuxPairing_angle_profile g orders s t
  let hPeriod := generalCoreAux_positive_angular_periods g orders s t ho hdef
  let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let S := generalCoreAuxSidePairing g orders s t ho hdef d hd hb
  let P := cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
  let f := P.cayleyCoordinate
  let U : Set ℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior
  let R := f '' U
  let E := (cofiniteMixedTangentialGroupEquiv θ d hθ hd hb ρ hρ hθρ).trans
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
      (cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ))
  have hR : IsConvexFuchsianPolygon P.cayleyData R :=
    cofiniteMixedTangential_projective_disc_convex θ d hθ hd hb ρ hρ hθρ hPeriod
  have hLF : LocallyFinite (fun γ : S.Generated =>
      f ⁻¹' fuchsianDomainTile P.cayleyData R (E γ)) :=
    (hR.locallyFinite.locallyFinite.comp_injective E.injective).preimage_continuous
      f.continuous
  have hclosure : closure R = f '' closure U := (f.image_closure U).symm
  have he : (fun γ : S.Generated =>
      f ⁻¹' fuchsianDomainTile P.cayleyData R (E γ)) =
      (fun γ : S.Generated => γ.val '' closure U) := by
    funext γ
    ext z
    change f z ∈ (E γ) • closure R ↔ z ∈ γ.val '' closure U
    rw [hclosure]
    change f z ∈ (fun w => (E γ) • w) '' (f '' closure U) ↔ _
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, he⟩
      refine ⟨y, hy, f.injective ?_⟩
      exact (cofiniteMixedTangential_coordinate_action θ d hθ hd hb ρ hρ hθρ hPeriod γ y).trans he
    · rintro ⟨y, hy, rfl⟩
      refine ⟨f y, ⟨y, hy, rfl⟩, ?_⟩
      exact (cofiniteMixedTangential_coordinate_action θ d hθ hd hb ρ hρ hθρ hPeriod γ y).symm
  rw [he] at hLF
  exact hLF

/-- The actual side between two consecutive right corners is extended to
its whole actual support by powers of its actual boundary-pairing generator.
All endpoint, translation and axis data come from the original polygon. -/
theorem generalSignature_boundary_cut_zpow_cover {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (i : Fin n)
    (hk : θ (finRotate n i) = Real.pi / 2)
    (hj : θ (finRotate n (finRotate n i)) = Real.pi / 2) :
    let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let k := finRotate n i
    let j := finRotate n k
    let F := cofiniteTangentPairingElement θ d hθ hd hb i j
    (⋃ m : ℤ, (F ^ m) '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q k) = (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q k).carrier := by
  let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let k := finRotate n i
  let j := finRotate n k
  let F := cofiniteTangentPairingElement θ d hθ hd hb i j
  obtain ⟨u, v, q, l, hu, hv, _huv, hl, hqu, hqv, hK, ht⟩ :=
    generalSignature_boundary_triple_translation θ d hθ hd hb i hk hj
  let e := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry q
  have he0 : e u = _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam 0 := by
    change q • u = _
    rw [hqu]
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam, UpperHalfPlane.I]
  have heF : F = e⁻¹ * signatureBoundaryShift l * e := by
    apply IsometryEquiv.ext
    intro z
    apply e.injective
    change e (F z) = e (e.symm (signatureBoundaryShift l (e z)))
    rw [IsometryEquiv.apply_symm_apply]
    change q • cofiniteTangentPairingElement θ d hθ hd hb i
      (finRotate n (finRotate n i)) z = signatureBoundaryShift l (q • z)
    exact ht z
  have heFm (m : ℤ) : F ^ m = e⁻¹ * (signatureBoundaryShift l ^ m) * e := by
    rw [heF]
    simpa only [inv_inv] using (conj_zpow (a := e⁻¹) (b := signatureBoundaryShift l) (i := m))
  have hseg : _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q k = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment u v := by
    ext z
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (Q.vertices k) (Q.vertices j) ↔ _
    rw [← hu, ← hv, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_interior,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective.mem_set_image]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc u)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc v)) ↔ _
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  have hcar : e '' (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q k).carrier = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
    rw [← hK, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  calc
    (⋃ m : ℤ, (F ^ m) '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q k) =
        ⋃ m : ℤ, (e⁻¹ * (signatureBoundaryShift l ^ m) * e) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment u v := by
      simp only [heFm, hseg]
    _ = (e⁻¹ : ℍ ≃ᵢ ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier :=
      signatureBoundaryAxisCut_conjugate_cover e u v l hl he0 hqv
    _ = (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q k).carrier := by
      rw [← hcar]
      exact e.toEquiv.symm_image_image _

section ActualCutWalls
variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)

local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
  (generalCoreTheta_mem g orders s t ho hdef) hd hb
local notation "S₀" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb
local notation "k₀" j => generalCoreBoundarySideIndex g orders s t j 1

/-- The literal finite cut in each actual boundary triple of the prescribed core. -/
def generalCoreCutSegment
    (j : Fin t) : Set ℍ := _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ (k₀ j)

/-- The actual auxiliary-group wall set, built from finitely many physical cuts. -/
def generalCoreCutWallUnion : Set ℍ :=
  ⋃ γ : (S₀).Generated, γ.val '' (⋃ j : Fin t, generalCoreCutSegment g orders s t ho hdef d hd hb j)

/-- The complete support axes of the same actual translated cut sides. -/
def generalCoreCutFullAxisUnion : Set ℍ :=
  ⋃ γ : (S₀).Generated, γ.val '' (⋃ j : Fin t, (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q₀ (k₀ j)).carrier)

theorem generalCoreCutSegment_isClosed (j : Fin t) :
    IsClosed (generalCoreCutSegment g orders s t ho hdef d hd hb j) :=
  _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_isClosed Q₀ (k₀ j)

/-- These are genuine original boundary segments of the auxiliary polygon. -/
theorem generalCoreCutSegment_subset_closed_polygon (j : Fin t) :
    generalCoreCutSegment g orders s t ho hdef d hd hb j ⊆
      closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (Q₀).interior) := by
  change _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ (k₀ j) ⊆ closure (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).interior
  rw [← _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_carrier Q₀]
  intro z hz
  exact Or.inr (mem_sUnion.mpr ⟨_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ (k₀ j), ⟨k₀ j, rfl⟩, hz⟩)

/-- Closedness of the actual infinite wall set follows from the actual
closed-tile local finiteness and finitely many actual closed cuts. -/
theorem generalCoreCutWallUnion_isClosed :
    IsClosed (generalCoreCutWallUnion g orders s t ho hdef d hd hb) := by
  have hcuts : (⋃ j : Fin t, generalCoreCutSegment g orders s t ho hdef d hd hb j) ⊆
      closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (Q₀).interior) :=
    iUnion_subset (fun j => generalCoreCutSegment_subset_closed_polygon g orders s t ho hdef d hd hb j)
  have hLF := (generalCoreAux_native_closed_tiles_locallyFinite g orders s t ho hdef d hd hb).subset
    (fun γ : (S₀).Generated => image_mono hcuts)
  apply hLF.isClosed_iUnion
  intro γ
  exact γ.val.toHomeomorph.isClosedMap _
    ((locallyFinite_of_finite _).isClosed_iUnion
      (fun j => generalCoreCutSegment_isClosed g orders s t ho hdef d hd hb j))

/-- Powers of the actual retained boundary generator fill the whole support
of its actual cut, including both finite right corners. -/
theorem generalCoreCutSegment_zpow_cover (j : Fin t) :
    (⋃ m : ℤ,
      (generalCoreTargetGenerator g orders s t ho hdef d hd hb
        (generalCoreBoundarySideIndex g orders s t j 0) ^ m) ''
        generalCoreCutSegment g orders s t ho hdef d hd hb j) =
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q₀ (k₀ j)).carrier := by
  have hk : generalCoreTheta g orders s t
      (finRotate _ (generalCoreBoundarySideIndex g orders s t j 0)) = Real.pi / 2 := by
    rw [generalCoreBoundarySideIndex_next_zero, generalCoreBoundarySideIndex_angle]
    norm_num
  have hj : generalCoreTheta g orders s t
      (finRotate _ (finRotate _ (generalCoreBoundarySideIndex g orders s t j 0))) = Real.pi / 2 := by
    rw [generalCoreBoundarySideIndex_next_zero, generalCoreBoundarySideIndex_next_one,
      generalCoreBoundarySideIndex_angle]
    norm_num
  have h := generalSignature_boundary_cut_zpow_cover (generalCoreTheta g orders s t) d
    (generalCoreTheta_mem g orders s t ho hdef) hd hb
    (generalCoreBoundarySideIndex g orders s t j 0) hk hj
  simpa only [generalCoreBoundarySideIndex_next_zero, generalCoreBoundarySideIndex_next_one,
    generalCoreCutSegment, generalCoreTargetGenerator, generalCoreBoundarySideIndex_pair_zero] using h

/-- No wall closedness or whole-axis hypothesis is supplied: the actual
boundary-translation powers and subgroup multiplication identify the two sets. -/
theorem generalCoreCutWallUnion_eq_fullAxes :
    generalCoreCutWallUnion g orders s t ho hdef d hd hb =
      generalCoreCutFullAxisUnion g orders s t ho hdef d hd hb := by
  apply subset_antisymm
  · exact iUnion_mono (fun _ => image_mono
      (iUnion_mono (fun j => _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q₀ (k₀ j))))
  · intro z hz
    obtain ⟨γ, y, hy, rfl⟩ := mem_iUnion.mp hz
    obtain ⟨j, hy⟩ := mem_iUnion.mp hy
    rw [← generalCoreCutSegment_zpow_cover g orders s t ho hdef d hd hb j] at hy
    obtain ⟨m, w, hw, he⟩ := mem_iUnion.mp hy
    let F : (S₀).Generated := ⟨generalCoreTargetGenerator g orders s t ho hdef d hd hb
      (generalCoreBoundarySideIndex g orders s t j 0),
      generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb
        (generalCoreBoundarySideIndex_generator_mem g orders s t ho hdef d hd hb j)⟩
    apply mem_iUnion.mpr
    refine ⟨γ * F ^ m, w, mem_iUnion.mpr ⟨j, hw⟩, ?_⟩
    have hpow : (F ^ m).val = F.val ^ m := map_zpow (S₀).Generated.subtype F m
    have hw' : (F ^ m).val w = y := by rw [hpow]; exact he
    change γ.val ((F ^ m).val w) = γ.val y
    exact congrArg γ.val hw'

theorem generalCoreCutFullAxisUnion_isClosed :
    IsClosed (generalCoreCutFullAxisUnion g orders s t ho hdef d hd hb) := by
  rw [← generalCoreCutWallUnion_eq_fullAxes]
  exact generalCoreCutWallUnion_isClosed g orders s t ho hdef d hd hb

/-- A family of genuine native geodesics realizing exactly these actual walls. -/
def generalCoreCutAxisFamily : Set _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine :=
  {L | ∃ γ : (S₀).Generated, ∃ j : Fin t,
    L.carrier = γ.val '' (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q₀ (k₀ j)).carrier}

theorem generalCoreCutAxisFamily_carriers :
    (⋃ L ∈ generalCoreCutAxisFamily g orders s t ho hdef d hd hb, L.carrier) =
      generalCoreCutWallUnion g orders s t ho hdef d hd hb := by
  rw [generalCoreCutWallUnion_eq_fullAxes]
  apply subset_antisymm
  · intro z hz
    obtain ⟨L, hL, hz⟩ := mem_iUnion₂.mp hz
    obtain ⟨γ, j, hL⟩ := hL
    rw [hL] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact mem_iUnion.mpr ⟨γ, y, mem_iUnion.mpr ⟨j, hy⟩, rfl⟩
  · intro z hz
    obtain ⟨γ, y, hy, rfl⟩ := mem_iUnion.mp hz
    obtain ⟨j, hy⟩ := mem_iUnion.mp hy
    obtain ⟨A, hA⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.isometry_exists_realGL γ.val.isometry
    let L := (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q₀ (k₀ j)).realGLMap A
    have hL : L.carrier = γ.val '' (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q₀ (k₀ j)).carrier := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
      change (fun z : ℍ => A • z) '' _ = (γ.val : ℍ → ℍ) '' _
      rw [← hA]
    refine mem_iUnion₂.mpr ⟨L, ⟨γ, j, hL⟩, ?_⟩
    rw [hL]
    exact mem_image_of_mem γ.val hy

/-- The actual complementary component of the complete cut-axis walls. -/
def generalCoreCutChamber (x : ℍ) : Set ℍ :=
  connectedComponentIn (generalCoreCutWallUnion g orders s t ho hdef d hd hb)ᶜ x

/-- True wall geometry gives convexity of the actual chamber; pairwise wall
disjointness and a desired convexity hypothesis are unnecessary. -/
theorem generalCoreCutChamber_hConvex (x : ℍ)
    (hx : x ∉ generalCoreCutWallUnion g orders s t ho hdef d hd hb) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (generalCoreCutChamber g orders s t ho hdef d hd hb x) := by
  have he := generalCoreCutAxisFamily_carriers g orders s t ho hdef d hd hb
  have h := signatureCutWallChamber_hConvex
    (generalCoreCutAxisFamily g orders s t ho hdef d hd hb) x (by rwa [he])
  simpa only [he, generalCoreCutChamber] using h

/-- Openness is a conclusion of the actual closed-wall proof, not an
unjustified assertion about an infinite intersection of open half-planes. -/
theorem generalCoreCutChamber_isOpen (x : ℍ) :
    IsOpen (generalCoreCutChamber g orders s t ho hdef d hd hb x) :=
  (generalCoreCutWallUnion_isClosed g orders s t ho hdef d hd hb).isOpen_compl.connectedComponentIn

end ActualCutWalls

end LowDimensionalTopology.Geometry.Fuchsian
