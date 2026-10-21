module
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Germs
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.ProperSectorAngularMeasure
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonCornerAngles
public import LowDimensionalTopology.Geometry.Polygon.Triangulation.PolygonMeshCornerSums

/-! Genuine minor and reflex polygon corners are recovered from their actual incident mesh angles. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped Complex.UnitDisc Classical ENNReal UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

theorem discRadialDirections_iUnion {ι : Type*} (S : ι → Set 𝔻) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (⋃ i, S i) = ⋃ i, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (S i) := by
  ext u
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections, Set.mem_ofPred_eq, mem_iUnion]
  exact exists_comm

/-- An actual union of convex sectors through the origin has local angular directions. -/
theorem discRadialDirections_iUnion_eq_of_germ {ι : Type*} (S : ι → Set 𝔻)
    (hS : ∀ i, _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (S i)) (h0 : ∀ i, (0 : 𝔻) ∈ S i)
    {A : Set 𝔻} (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex A) (h0A : (0 : 𝔻) ∈ A)
    (h : ∀ᶠ w in 𝓝 (0 : 𝔻), w ∈ (⋃ i, S i) ↔ w ∈ A) :
    (⋃ i, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (S i)) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections A := by
  let N : Set 𝔻 := {w | w ∈ (⋃ i, S i) ↔ w ∈ A}
  have hN : N ∈ 𝓝 (0 : 𝔻) := h
  have he : (⋃ i, S i) ∩ N = A ∩ N := by
    ext w
    simp only [Set.mem_inter_iff, N, Set.mem_ofPred_eq]
    tauto
  rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_inter_nhds hA h0A hN, ← he, iUnion_inter,
    discRadialDirections_iUnion]
  congr 1
  funext i
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_inter_nhds (hS i) (h0 i) hN).symm

/-- Open convex planar regions based at a common closure point cannot first meet far away. -/
theorem convex_open_disjoint_of_eventually {U V : Set ℂ}
    (hUc : Convex ℝ U) (hUo : IsOpen U) (hVc : Convex ℝ V) (hVo : IsOpen V)
    (h0U : (0 : ℂ) ∈ closure U) (h0V : (0 : ℂ) ∈ closure V)
    (h : ∀ᶠ w in 𝓝 (0 : ℂ), w ∉ U ∩ V) : Disjoint U V := by
  refine Set.disjoint_left.mpr ?_
  intro x hxU hxV
  have hseg : openSegment ℝ (0 : ℂ) x ⊆ U ∩ V := by
    intro y hy
    exact ⟨interior_subset (hUc.openSegment_closure_interior_subset_interior h0U
      (hUo.interior_eq.symm ▸ hxU) hy),
      interior_subset (hVc.openSegment_closure_interior_subset_interior h0V
        (hVo.interior_eq.symm ▸ hxV) hy)⟩
  have hcl : (0 : ℂ) ∈ closure (U ∩ V) := closure_mono hseg
    (segment_subset_closure_openSegment (left_mem_segment ℝ (0 : ℂ) x))
  obtain ⟨w, hw, hn⟩ := ((mem_closure_iff_frequently.mp hcl).and_eventually h).exists
  exact hn hw

/-- The same local-to-global disjointness holds for the actual native hyperbolic convex regions. -/
theorem discHConvex_open_disjoint_of_eventually {U V : Set 𝔻}
    (hUc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex U) (hUo : IsOpen U) (hVc :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex V) (hVo : IsOpen V)
    (h0U : (0 : 𝔻) ∈ closure U) (h0V : (0 : 𝔻) ∈ closure V)
    (h : ∀ᶠ w in 𝓝 (0 : 𝔻), w ∉ U ∩ V) : Disjoint U V := by
  have hK0 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (0 : 𝔻) = 0 := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula 0 = 0
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
  let N : Set 𝔻 := {w | w ∉ U ∩ V}
  have hN : N ∈ 𝓝 (0 : 𝔻) := h
  have hKN := _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap.image_mem_nhds hN
  rw [hK0] at hKN
  have hnot : ∀ᶠ y in 𝓝 (0 : ℂ), y ∉ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' U) ∩ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' V) := by
    filter_upwards [hKN] with y hy
    obtain ⟨w, hw, hwK⟩ := hy
    rintro ⟨⟨u,hu,huK⟩,⟨v,hv,hvK⟩⟩
    have huW : u = w := _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective (huK.trans hwK.symm)
    have hvW : v = w := _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective (hvK.trans hwK.symm)
    exact hw ⟨huW ▸ hu,hvW ▸ hv⟩
  have h0KU : (0 : ℂ) ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' U) := by
    rw [← hK0]
    exact (image_closure_subset_closure_image
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_kleinCoordinate)
      (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate h0U)
  have h0KV : (0 : ℂ) ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' V) := by
    rw [← hK0]
    exact (image_closure_subset_closure_image
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_kleinCoordinate)
      (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate h0V)
  have hdis := convex_open_disjoint_of_eventually
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex U).mp hUc)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap U hUo)
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex V).mp hVc)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap V hVo) h0KU h0KV hnot
  exact Set.disjoint_left.mpr (fun x hxU hxV =>
    Set.disjoint_left.mp hdis (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      hxU) (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate hxV))

def DiscPolygon.finiteCarrier {n : ℕ} (P : DiscPolygon n) : Set 𝔻 :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ⁻¹' P.closedCarrier

theorem DiscPolygon.finiteCarrier_eq_closure {n : ℕ} (P : DiscPolygon n) :
    P.finiteCarrier = closure P.interior := by
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRelativeClosure_eq_preimage P.interior).symm

/-- The actual incident closed faces reproduce the full actual polygon germ at every finite point. -/
theorem DiscPolygon.meshTriangle_incident_germ {n : ℕ} (P : DiscPolygon n) (z : 𝔻) :
    ∀ᶠ w in 𝓝 z,
      w ∈ (⋃ t ∈ {t : P.kleinTriangleMesh.Triangle | z ∈ (P.meshTriangle t).finiteCarrier},
        (P.meshTriangle t).finiteCarrier) ↔ w ∈ P.finiteCarrier := by
  filter_upwards [P.meshTriangle_nonincident_eventually z] with w hw
  constructor
  · intro hw
    obtain ⟨t,hzt,hwt⟩ := mem_iUnion₂.mp hw
    exact P.meshTriangle_subset_closedCarrier t hwt
  · intro hwP
    have hc : w ∈ ⋃ t : P.kleinTriangleMesh.Triangle, (P.meshTriangle t).finiteCarrier := by
      rw [P.meshTriangle_finiteCarrier_cover]
      exact hwP
    obtain ⟨t,hwt⟩ := mem_iUnion.mp hc
    have hzt : z ∈ (P.meshTriangle t).finiteCarrier := by
      by_contra hn
      exact hw t hn hwt
    exact mem_iUnion₂.mpr ⟨t,hzt,hwt⟩

/-- Genuine angular additivity compares an actual polygon corner germ with any actual convex region. -/
theorem DiscPolygon.meshTriangle_angularFraction_sum_of_convex_germ {n : ℕ}
    (P : DiscPolygon n) (z : 𝔻) {A : Set 𝔻}
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex A) (hzA : z ∈ A)
    (hG : ∀ᶠ w in 𝓝 z, w ∈ P.finiteCarrier ↔ w ∈ A) :
    ∑ t : {t : P.kleinTriangleMesh.Triangle | z ∈ (P.meshTriangle t).finiteCarrier},
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction (P.meshTriangle
        t.1).finiteCarrier z =
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction A z := by
  let F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z
  let I := {t : P.kleinTriangleMesh.Triangle | z ∈ (P.meshTriangle t).finiteCarrier}
  let S : I → Set 𝔻 := fun t => F '' (P.meshTriangle t.1).finiteCarrier
  have hS : ∀ t, _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (S t) := fun t =>
    (P.meshTriangle t.1).finiteCarrier_hConvex.isometry_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry z)
  have h0S : ∀ t, (0 :
    𝔻) ∈ S t := fun t => ⟨z,t.2,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self z⟩
  have hUnion : (⋃ t : I, S t) = F ''
      (⋃ t ∈ {t : P.kleinTriangleMesh.Triangle | z ∈ (P.meshTriangle t).finiteCarrier},
        (P.meshTriangle t).finiteCarrier) := by
    ext w
    constructor
    · intro hw
      obtain ⟨t,ht⟩ := mem_iUnion.mp hw
      obtain ⟨x,hxt,hxw⟩ := ht
      exact ⟨x,mem_iUnion₂.mpr ⟨t.1,t.2,hxt⟩,hxw⟩
    · rintro ⟨x,hx,hxw⟩
      obtain ⟨t,hzt,hxt⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨⟨t,hzt⟩,⟨x,hxt,hxw⟩⟩
  have hg : ∀ᶠ w in 𝓝 z,
      w ∈ (⋃ t ∈ {t : P.kleinTriangleMesh.Triangle | z ∈ (P.meshTriangle t).finiteCarrier},
        (P.meshTriangle t).finiteCarrier) ↔ w ∈ A := by
    filter_upwards [P.meshTriangle_incident_germ z,hG] with w hw₁ hw₂
    exact hw₁.trans hw₂
  have hgF := _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_homeomorph_germ F hg
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self, ← hUnion] at hgF
  have hdirs := discRadialDirections_iUnion_eq_of_germ S hS h0S
    (hA.isometry_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry z))
    ⟨z,hzA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self z⟩ hgF
  have hm := measure_biUnion_finset₀ (μ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure)
    (s := (Finset.univ : Finset I)) (f := fun t =>
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (S t))
    (fun t _ u _ htu => P.meshTriangle_directions_pairwise_null z t.2 u.2
      (fun he => htu (Subtype.ext he)))
    (fun t _ => (_root_.LowDimensionalTopology.Geometry.Hyperbolic.measurableSet_discRadialDirections (hS t)
      (F.isClosedMap _ (P.meshTriangle t.1).finiteCarrier_isClosed) (h0S t)).nullMeasurableSet)
  simp only [Finset.mem_univ, iUnion_true] at hm
  rw [hdirs] at hm
  exact hm.symm

theorem DiscPolygon.meshTriangle_subtendedAngle_sum_of_convex_germ {n : ℕ}
    (P : DiscPolygon n) (z : 𝔻) {A : Set 𝔻}
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex A) (hzA : z ∈ A)
    (hG : ∀ᶠ w in 𝓝 z, w ∈ P.finiteCarrier ↔ w ∈ A) :
    ∑ t : {t : P.kleinTriangleMesh.Triangle | z ∈ (P.meshTriangle t).finiteCarrier},
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (P.meshTriangle t.1).finiteCarrier z = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle A z := by
  have hs := congrArg ENNReal.toReal (P.meshTriangle_angularFraction_sum_of_convex_germ z hA hzA hG)
  rw [ENNReal.toReal_sum (fun t ht => by
    unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction
    exact measure_ne_top _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure _)] at hs
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle, ← Finset.mul_sum, hs]

/-- At a true finite minor corner, the incident mesh's original angles recover the original polygon angle. -/
theorem DiscPolygon.meshTriangle_subtendedAngle_sum_at_minor {n : ℕ}
    (P : DiscPolygon n) (i : Fin n) (z : 𝔻) (hz : P.vertices i =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hne : (P.cornerRayPrev i z hz).supportLine ≠ (P.cornerRayNext i z hz).supportLine)
    (hminor : P.HasMinorInteriorAt i z hz) :
    ∑ t : {t : P.kleinTriangleMesh.Triangle | z ∈ (P.meshTriangle t).finiteCarrier},
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (P.meshTriangle t.1).finiteCarrier z = P.angle i := by
  let T := P.properCornerTriangle i z hz hne
  have hTa : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := hz
  have hp : P.cornerRayPrev i z hz = T.cornerRayABAtA z hTa := by
    change discRayTowardClosed z T.b _ = _
    exact T.rayToward_b z hTa _
  have hn : P.cornerRayNext i z hz = T.cornerRayACAtA z hTa := by
    change discRayTowardClosed z T.c _ = _
    exact T.rayToward_c z hTa _
  have hP : ∀ᶠ w in 𝓝 z, w ∈ P.interior ↔ w ∈ T.interior := by
    have hh : ∀ᶠ w in 𝓝 z, w ∈ P.interior ↔
        w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior (T.cornerRayABAtA z hTa) (T.cornerRayACAtA z hTa) := by
      simpa only [DiscPolygon.HasMinorInteriorAt,hp,hn] using hminor
    filter_upwards [hh,T.interior_corner_germ z hTa] with w hwP hwT
    exact hwP.trans hwT.symm
  have hClosed := _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_closure_germ hP
  rw [← P.finiteCarrier_eq_closure, ← T.finiteCarrier_eq_closure] at hClosed
  have hzT : z ∈ T.finiteCarrier := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ T.closedCarrier
    rw [← hTa]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.subset_closedDiscHConvexHull {T.a,T.b,T.c} (by simp)
  have hs := P.meshTriangle_subtendedAngle_sum_of_convex_germ z T.finiteCarrier_hConvex hzT hClosed
  rw [T.subtendedAngle_at_finite z hTa] at hs
  have hAlpha : T.alpha = P.angle i := by
    rw [P.angle_of_minor i z hz hminor,T.alpha_of_finite z hTa,← hp,← hn]
  exact hs.trans hAlpha

/-- The two actual proper components leave no open angular gap. -/
theorem closure_properHAngle_components {z : ℍ} (R S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S ∪ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleExterior R S) = univ := by
  have hd : Dense (({(0 : ℝ)}ᶜ) ×ˢ ({(0 : ℝ)}ᶜ)) :=
    (dense_compl_singleton (0 : ℝ)).prod (dense_compl_singleton (0 : ℝ))
  have hp := hd.preimage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleCoordinate_isOpenEmbedding R S
    hne).isOpenMap
  apply (hp.mono ?_).closure_eq
  intro w hw
  have h₁ : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleCoordinate R S hne w).1 ≠ 0 := hw.1
  have h₂ : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleCoordinate R S hne w).2 ≠ 0 := hw.2
  have hImage : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleCoordinate R S hne w ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleCoordinate R S hne '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S ∪ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleExterior R S) := by
    rw [image_union,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleCoordinate_image_interior R S
      hne,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleCoordinate_image_exterior R S hne]
    have hDom : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleCoordinate R S hne w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleCoordinateDomain R S hne := by
      rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleCoordinate_range]
      exact mem_range_self w
    rcases lt_or_gt_of_ne h₁ with h₁ | h₁
    · exact Or.inr ⟨hDom,Or.inl h₁⟩
    · rcases lt_or_gt_of_ne h₂ with h₂ | h₂
      · exact Or.inr ⟨hDom,Or.inr h₂⟩
      · exact Or.inl ⟨hDom,h₁,h₂⟩
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAngleCoordinate_isOpenEmbedding R S
    hne).injective.mem_set_image.mp hImage

theorem closure_properDiscAngle_components {z : 𝔻} (R S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior R S ∪ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleExterior R S) = univ := by
  have hH := closure_properHAngle_components R.toHalfPlane S.toHalfPlane
    ((R.different_supports_iff S).mp hne)
  have hImage : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R.toHalfPlane S.toHalfPlane ∪
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleExterior R.toHalfPlane S.toHalfPlane) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior R S ∪ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleExterior R S := image_union _ _ _
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' closure
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R.toHalfPlane S.toHalfPlane ∪
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleExterior R.toHalfPlane S.toHalfPlane) =
      closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ''
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R.toHalfPlane S.toHalfPlane ∪
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleExterior R.toHalfPlane S.toHalfPlane)) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.image_closure _
  have hr : range _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc = univ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.surjective.range_eq
  rw [hH, hImage, image_univ, hr] at he
  exact he.symm

theorem DiscPolygon.interior_finiteCarrier {n : ℕ} (P : DiscPolygon n) :
    _root_.interior P.finiteCarrier = P.interior := by
  have he : Topology.IsOpenEmbedding ((↑) : 𝔻 → ℂ) := by
    refine ⟨Complex.UnitDisc.isEmbedding_coe, ?_⟩
    have hr : range ((↑) : 𝔻 → ℂ) = {z : ℂ | ‖z‖ < 1} := by
      ext w
      constructor
      · rintro ⟨z,rfl⟩
        exact z.norm_lt_one
      · exact fun hw => ⟨Complex.UnitDisc.mk w hw,rfl⟩
    rw [hr]
    exact isOpen_lt continuous_norm continuous_const
  rw [P.finiteCarrier_eq_closure]
  change _root_.interior (closure (((↑) : 𝔻 → ℂ) ⁻¹' P.complexInterior)) = _
  rw [← he.isOpenMap.preimage_closure_eq_closure_preimage Complex.UnitDisc.continuous_coe,
    ← he.isOpenMap.preimage_interior_eq_interior_preimage
      Complex.UnitDisc.continuous_coe, P.interior_closure_complexInterior]
  rfl

theorem DiscPolygon.meshTriangle_interior_subset {n : ℕ} (P : DiscPolygon n)
    (t : P.kleinTriangleMesh.Triangle) : (P.meshTriangle t).interior ⊆ P.interior := by
  rw [← P.interior_finiteCarrier]
  apply interior_maximal _ (P.meshTriangle t).interior_isOpen
  intro z hz
  apply P.meshTriangle_subset_closedCarrier t
  have hc : z ∈ (P.meshTriangle t).finiteCarrier := by
    rw [(P.meshTriangle t).finiteCarrier_eq_closure]
    exact subset_closure hz
  exact hc

theorem DiscPolygon.meshAngleSumAt_eq_incident_subtendedAngle {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (z : 𝔻) (hz : P.meshNativeVertex v =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    P.meshAngleSumAt v =
      ∑ t : {t : P.kleinTriangleMesh.Triangle | z ∈ (P.meshTriangle t).finiteCarrier},
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (P.meshTriangle t.1).finiteCarrier z := by
  have hSub := Finset.sum_subtype (F := inferInstance)
    (p := fun t : P.kleinTriangleMesh.Triangle => z ∈ (P.meshTriangle t).finiteCarrier)
    (Finset.univ.filter (fun t : P.kleinTriangleMesh.Triangle => z ∈ (P.meshTriangle t).finiteCarrier))
    (by intro t; simp only [Finset.mem_filter,Finset.mem_univ,true_and])
    (fun t : P.kleinTriangleMesh.Triangle => _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle
      (P.meshTriangle t).finiteCarrier z)
  refine Eq.trans ?_ hSub
  rw [Finset.sum_filter]
  unfold DiscPolygon.meshAngleSumAt
  apply Finset.sum_congr rfl
  intro t ht
  have he : z ∈ (P.meshTriangle t).finiteCarrier ↔ v.1 ∈ t.1 := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ (P.meshTriangle t).closedCarrier ↔ _
    rw [← hz]
    exact P.usedMeshVertex_mem_triangle_iff v.1 v.2 t
  by_cases hvt : v.1 ∈ t.1
  · rw [ite_eq_left (he.mpr hvt)]
    exact P.meshTriangle_angleAtPoint_eq_subtendedAngle v.1 v.2 z hz t hvt
  · rw [ite_eq_right (fun h => hvt (he.mp h))]
    exact (P.meshTriangle t).angleAtPoint_eq_zero_of_not_mem
      (fun h => hvt ((P.usedMeshVertex_mem_triangle_iff v.1 v.2 t).mp h))

theorem DiscPolygon.meshAngleSumAt_of_minor {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (i : Fin n) (z : 𝔻)
    (hv : P.meshNativeVertex v = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (hz : P.vertices
      i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hne : (P.cornerRayPrev i z hz).supportLine ≠ (P.cornerRayNext i z hz).supportLine)
    (hminor : P.HasMinorInteriorAt i z hz) : P.meshAngleSumAt v = P.angle i := by
  rw [P.meshAngleSumAt_eq_incident_subtendedAngle v z hv]
  exact P.meshTriangle_subtendedAngle_sum_at_minor i z hz hne hminor

/-- A genuine finite convex open star filling a neighborhood has total angular measure two pi. -/
theorem discSubtendedAngle_sum_of_open_star {ι : Type*} [Fintype ι]
    (U : ι → Set 𝔻) (hc : ∀ i, _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (U i)) (ho : ∀ i, IsOpen (U
      i))
    (hn : ∀ i, (U i).Nonempty) (h0 : ∀ i, (0 : 𝔻) ∈ closure (U i))
    (hd : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcov : (⋃ i, closure (U i)) ∈ 𝓝 (0 : 𝔻)) :
    ∑ i, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure (U i)) 0 = 2 * Real.pi := by
  have hCover := discRadialDirections_incident_cover_of_mem_nhds
    (fun i => closure (U i)) (locallyFinite_of_finite _) (fun _ => isClosed_closure) hcov
  simp only [h0,Set.mem_ofPred_eq,iUnion_true] at hCover
  have hm := measure_biUnion_finset₀ (μ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure)
    (s := (Finset.univ : Finset ι)) (f := fun i =>
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (closure (U i)))
    (fun i _ j _ hij => (_root_.LowDimensionalTopology.Geometry.Hyperbolic.finite_discRadialDirections_common_closures
      (hc i) (ho i) (hn i) (hc j) (ho j) (hn j) (hd hij) (h0 i) (h0 j)).measure_zero _)
    (fun i _ => (_root_.LowDimensionalTopology.Geometry.Hyperbolic.measurableSet_discRadialDirections (hc i).closure
      isClosed_closure (h0 i)).nullMeasurableSet)
  simp only [Finset.mem_univ,iUnion_true] at hm
  rw [hCover,_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure_univ] at hm
  have hs := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_sum (fun i hi => measure_ne_top
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure _),ENNReal.toReal_one] at hs
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction_zero,← Finset.mul_sum,← hs,mul_one]

/-- An actual complementary triangle closes a reflex star, with no global-complement hypothesis. -/
theorem DiscPolygon.meshTriangle_subtendedAngle_sum_add_complement {n : ℕ}
    (P : DiscPolygon n) (z : 𝔻) (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (hzT : T.a =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hsep : ∀ᶠ w in 𝓝 z, w ∉ P.interior ∩ T.interior)
    (hcov : P.finiteCarrier ∪ T.finiteCarrier ∈ 𝓝 z) :
    (∑ t : {t : P.kleinTriangleMesh.Triangle | z ∈ (P.meshTriangle t).finiteCarrier},
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (P.meshTriangle t.1).finiteCarrier z) + T.alpha = 2 * Real.pi := by
  let F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z
  let I := {t : P.kleinTriangleMesh.Triangle | z ∈ (P.meshTriangle t).finiteCarrier}
  let U : Option I → Set 𝔻 := fun t => match t with
    | none => F '' T.interior
    | some t => F '' (P.meshTriangle t.1).interior
  have hc : ∀ i, _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (U i) := by
    rintro (_ | i)
    · exact T.interior_discHConvex.isometry_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry z)
    · exact (P.meshTriangle i.1).interior_discHConvex.isometry_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry z)
  have ho : ∀ i, IsOpen (U i) := by
    rintro (_ | i)
    · exact F.isOpenMap _ T.interior_isOpen
    · exact F.isOpenMap _ (P.meshTriangle i.1).interior_isOpen
  have hn : ∀ i, (U i).Nonempty := by
    rintro (_ | i)
    · exact T.interior_nonempty.image F
    · exact (P.meshTriangle i.1).interior_nonempty.image F
  have hEq (B : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) : F '' B.finiteCarrier = closure (F '' B.interior) := by
    rw [B.finiteCarrier_eq_closure,F.image_closure]
  have h0T : (0 : 𝔻) ∈ closure (F '' T.interior) := by
    rw [← hEq]
    refine ⟨z, ?_,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self z⟩
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ T.closedCarrier
    rw [← hzT]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.subset_closedDiscHConvexHull {T.a,T.b,T.c} (by simp)
  have h0 : ∀ i, (0 : 𝔻) ∈ closure (U i) := by
    rintro (_ | i)
    · exact h0T
    · change (0 : 𝔻) ∈ closure (F '' (P.meshTriangle i.1).interior)
      rw [← hEq]
      exact ⟨z,i.2,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self z⟩
  have hDis (i : I) : Disjoint (U (some i)) (U none) := by
    have hh : ∀ᶠ w in 𝓝 z,
        w ∈ (P.meshTriangle i.1).interior ∩ T.interior ↔ w ∈ (∅ : Set 𝔻) := by
      filter_upwards [hsep] with w hw
      simp only [mem_empty_iff_false,iff_false]
      exact fun h => hw ⟨P.meshTriangle_interior_subset i.1 h.1,h.2⟩
    have hF := _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_homeomorph_germ F hh
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self,image_inter
      F.injective,image_empty] at hF
    simp only [mem_empty_iff_false,iff_false] at hF
    exact discHConvex_open_disjoint_of_eventually
      (hc (some i)) (ho (some i)) (hc none) (ho none) (h0 (some i)) (h0 none) hF
  have hd : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    rintro (_ | i) (_ | j) hij
    · exact (hij rfl).elim
    · exact (hDis j).symm
    · exact hDis i
    · exact (P.meshTriangle_interior_pairwise_disjoint
        (fun he => hij (congrArg some (Subtype.ext he)))).image F.injective.injOn
          (subset_univ _) (subset_univ _)
  have hLocal : (⋃ i : Option I, closure (U i)) ∈ 𝓝 (0 : 𝔻) := by
    have hOld : (⋃ i : Option I, match i with
        | none => T.finiteCarrier
        | some t => (P.meshTriangle t.1).finiteCarrier) ∈ 𝓝 z := by
      filter_upwards [hcov,P.meshTriangle_incident_germ z] with w hw hG
      rcases hw with hw | hw
      · obtain ⟨t,hzt,hwt⟩ := mem_iUnion₂.mp (hG.mpr hw)
        exact mem_iUnion.mpr ⟨some ⟨t,hzt⟩,hwt⟩
      · exact mem_iUnion.mpr ⟨none,hw⟩
    have hMap := F.isOpenMap.image_mem_nhds hOld
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self,image_iUnion] at hMap
    have he : (fun i : Option I => F '' (match i with
        | none => T.finiteCarrier
        | some t => (P.meshTriangle t.1).finiteCarrier)) = fun i => closure (U i) := by
      funext i
      cases i <;> exact hEq _
    rw [he] at hMap
    exact hMap
  have hs := discSubtendedAngle_sum_of_open_star U hc ho hn h0 hd hLocal
  have hAngle (B : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (closure (F '' B.interior)) 0 = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle B.finiteCarrier z := by
    rw [← hEq]
    have hh := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_isometry F (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry z) B.finiteCarrier z
    rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self] at hh
  simp only [Fintype.sum_option,U] at hs
  simp_rw [hAngle] at hs
  rw [T.subtendedAngle_at_finite z hzT] at hs
  linarith

/-- A true reflex corner is accounted for by adjoining its actual complementary triangle star. -/
theorem DiscPolygon.meshTriangle_subtendedAngle_sum_at_reflex {n : ℕ}
    (P : DiscPolygon n) (i : Fin n) (z : 𝔻) (hz : P.vertices i =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hne : (P.cornerRayPrev i z hz).supportLine ≠ (P.cornerRayNext i z hz).supportLine)
    (hnot : ¬ P.HasMinorInteriorAt i z hz) :
    ∑ t : {t : P.kleinTriangleMesh.Triangle | z ∈ (P.meshTriangle t).finiteCarrier},
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (P.meshTriangle t.1).finiteCarrier z = P.angle i := by
  let T := P.properCornerTriangle i z hz hne
  have hTa : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := hz
  have hp : P.cornerRayPrev i z hz = T.cornerRayABAtA z hTa := by
    change discRayTowardClosed z T.b _ = _
    exact T.rayToward_b z hTa _
  have hn : P.cornerRayNext i z hz = T.cornerRayACAtA z hTa := by
    change discRayTowardClosed z T.c _ = _
    exact T.rayToward_c z hTa _
  have hneT := T.cornerAtA_proper z hTa
  have hMajor : ∀ᶠ w in 𝓝 z, w ∈ P.interior ↔
      w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleExterior (T.cornerRayABAtA z hTa) (T.cornerRayACAtA z hTa) := by
    simpa only [hp,hn] using (P.corner_interior_germ_cases i z hz hne).resolve_left hnot
  have hT := T.interior_corner_germ z hTa
  have hsep : ∀ᶠ w in 𝓝 z, w ∉ P.interior ∩ T.interior := by
    filter_upwards [hMajor,hT] with w hwP hwT
    exact fun h => Set.disjoint_left.mp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngle_interior_exterior_disjoint _ _)
      (hwT.mp h.2) (hwP.mp h.1)
  have hG : ∀ᶠ w in 𝓝 z, w ∈ P.interior ∪ T.interior ↔
      w ∈ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior (T.cornerRayABAtA z hTa)
        (T.cornerRayACAtA z hTa) ∪
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleExterior (T.cornerRayABAtA z hTa) (T.cornerRayACAtA z hTa)) := by
    filter_upwards [hMajor,hT] with w hwP hwT
    simp only [mem_union,hwP,hwT]
    exact or_comm
  have hC := _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_closure_germ hG
  have hL : closure (P.interior ∪ T.interior) = P.finiteCarrier ∪ T.finiteCarrier := by
    rw [closure_union,← P.finiteCarrier_eq_closure,← T.finiteCarrier_eq_closure]
  rw [hL,closure_properDiscAngle_components _ _ hneT] at hC
  have hcov : P.finiteCarrier ∪ T.finiteCarrier ∈ 𝓝 z := by
    filter_upwards [hC] with w hw
    exact hw.mpr (mem_univ w)
  have hs := P.meshTriangle_subtendedAngle_sum_add_complement z T hTa hsep hcov
  have hAlpha : T.alpha = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure (P.cornerRayPrev i z hz) (P.cornerRayNext i z hz) := by
    rw [T.alpha_of_finite z hTa,← hp,← hn]
  rw [hAlpha] at hs
  rw [P.angle_of_not_minor i z hz hnot]
  linarith

theorem DiscPolygon.meshAngleSumAt_of_proper_finite_corner {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (i : Fin n) (z : 𝔻)
    (hv : P.meshNativeVertex v = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (hz : P.vertices
      i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hne : (P.cornerRayPrev i z hz).supportLine ≠ (P.cornerRayNext i z hz).supportLine) :
    P.meshAngleSumAt v = P.angle i := by
  rw [P.meshAngleSumAt_eq_incident_subtendedAngle v z hv]
  by_cases hminor : P.HasMinorInteriorAt i z hz
  · exact P.meshTriangle_subtendedAngle_sum_at_minor i z hz hne hminor
  · exact P.meshTriangle_subtendedAngle_sum_at_reflex i z hz hne hminor

end
end LowDimensionalTopology.Geometry.Polygon
