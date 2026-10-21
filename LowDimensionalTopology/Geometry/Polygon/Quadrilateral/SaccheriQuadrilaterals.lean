module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.LambertExistence
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.GeodesicReflections
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.IdealTriangleIsometries
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.CommonOrthogonals
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonAngles
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- An actual h-line reflection fixes its own entire finite carrier pointwise. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflection_image_self (N : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) : N.reflection '' N.carrier = N.carrier := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    rw [(N.reflection_fixed_iff w).mpr hw]
    exact hw
  · intro hz
    exact ⟨z,hz,(N.reflection_fixed_iff z).mpr hz⟩

/-- The genuine reflection preserves every genuine h-line perpendicular to its mirror. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflection_image_of_orthogonalAt (N K :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a : ℍ)
    (ha : N.OrthogonalAt K a) : N.reflection '' K.carrier = K.carrier := by
  obtain ⟨M,hM⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine N.reflection_isometry K
  have hNM := N.orthogonalAt_isometry_image K N M N.reflection N.reflection_isometry
    N.reflection_image_self hM ha
  rw [(N.reflection_fixed_iff a).mpr ha.1] at hNM
  obtain ⟨P,_,huniq⟩ := N.existsUnique_perpendicular a
  have hMP : M = P := huniq M ⟨hNM.2.1,⟨a,hNM⟩⟩
  have hKP : K = P := huniq K ⟨ha.2.1,⟨a,ha⟩⟩
  exact hM.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier (hMP.trans hKP.symm))

/-- The actual mirror extends to the genuine finite and ideal compactification. -/
def _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.closedReflectionHomeomorph (N :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel ≃ₜ _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isometry_exists_closedHalfPlaneHomeomorph
    N.reflection_isometry).choose

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.closedReflectionHomeomorph_finite (N :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (z : ℍ) :
    N.closedReflectionHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel
      z) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (N.reflection z) :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isometry_exists_closedHalfPlaneHomeomorph
    N.reflection_isometry).choose_spec z

/-- Whole finite/ideal side closures are preserved when the finite side is perpendicular to the mirror. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.closedReflection_image_of_orthogonalAt (N K :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (a : ℍ)
    (ha : N.OrthogonalAt K a) : N.closedReflectionHomeomorph '' K.closedCarrier = K.closedCarrier := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.closedCarrier,N.closedReflectionHomeomorph.image_closure,image_image]
  change closure ((fun z : ℍ => N.closedReflectionHomeomorph
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel z)) '' K.carrier) = _
  rw [show (fun z : ℍ => N.closedReflectionHomeomorph
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel z)) =
    (fun z : ℍ => _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (N.reflection z)) by
      funext z
      exact N.closedReflectionHomeomorph_finite z]
  rw [← image_image,N.reflection_image_of_orthogonalAt K a ha]

/-- Two genuine perpendicular lines are distinct. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.ne_of_orthogonalAt (N M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (d : ℍ)
    (hd : N.OrthogonalAt M d) : N ≠ M := by
  intro he
  have hz := N.normalPairing_orthogonal M d hd
  rw [← he] at hz
  change inner ℝ N.incenterNormal N.incenterNormal - N.incenterOffset * N.incenterOffset = 0 at hz
  rw [real_inner_self_eq_norm_sq] at hz
  have hunit := N.incenterNormal_lorentz_unit
  nlinarith only [hunit,hz]

/-- A point on the perpendicular line, away from the foot, is moved by the genuine mirror. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflection_ne_of_perpendicular (N M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (d c : ℍ)
    (hd : N.OrthogonalAt M d) (hc : c ∈ M.carrier) (hcd : c ≠ d) : N.reflection c ≠ c := by
  intro he
  have hcN := (N.reflection_fixed_iff c).mp he
  exact (N.ne_of_orthogonalAt M d hd) (N.eq_of_two_points M hcd hcN hd.1 hc hd.2.1)

/-- The mirror foot is the genuine metric midpoint on a perpendicular h-line. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflection_perpendicular_midpoint (N M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (d c : ℍ)
    (hd : N.OrthogonalAt M d) (hc : c ∈ M.carrier) (hcd : c ≠ d) :
    d ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment c (N.reflection c) ∧ dist c (N.reflection c) = 2 * dist c d := by
  have hcr : N.reflection c ∈ M.carrier :=
    N.reflection_image_of_orthogonalAt M d hd ▸ mem_image_of_mem N.reflection hc
  obtain ⟨γ,hγ,hr⟩ := M.exists_isometric_param
  obtain ⟨u,hu⟩ := hr ▸ hc
  obtain ⟨v,hv⟩ := hr ▸ hd.2.1
  obtain ⟨w,hw⟩ := hr ▸ hcr
  have huw : u ≠ w := by
    intro he
    exact N.reflection_ne_of_perpendicular M d c hd hc hcd (hw.symm.trans (congrArg γ he.symm) |>.trans hu)
  have he : dist (γ u) (γ v) = dist (γ w) (γ v) := by
    rw [hu,hv,hw]
    have hfix := (N.reflection_fixed_iff d).mpr hd.1
    calc
      dist c d = dist (N.reflection c) (N.reflection d) := (N.reflection_isometry.dist_eq c d).symm
      _ = dist (N.reflection c) d := by rw [hfix]
  rw [hγ.dist_eq,hγ.dist_eq,Real.dist_eq,Real.dist_eq,abs_eq_abs] at he
  have hsum : u+w=2*v := by
    rcases he with he | he
    · exact (huw (by linarith)).elim
    · linarith
  have hlen : dist c (N.reflection c) = 2 * dist c d := by
    rw [← hw,← hv,← hu,hγ.dist_eq,hγ.dist_eq,Real.dist_eq,Real.dist_eq,
      show u-w=2*(u-v) by linarith,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hsame : dist c d = dist d (N.reflection c) := by
    rw [← hw,← hv,← hu,hγ.dist_eq,hγ.dist_eq,Real.dist_eq,Real.dist_eq]
    congr 1
    linarith
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.mem_closedHSegment_of_dist_triangle_eq
    (N.reflection_ne_of_perpendicular M d c hd hc hcd).symm ?_,hlen⟩
  rw [hlen,← hsame]
  ring

/-- The extension is the genuine ambient geometric reflection, also at all ideal points. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.closedReflectionHomeomorph_ambient (N :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel) :
    (N.closedReflectionHomeomorph p).val = _root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom N.realReflection p.val := by
  have hc : Continuous (fun p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel => _root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom N.realReflection p.val) := by
    change Continuous (fun p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel =>
      _root_.LowDimensionalTopology.Geometry.Mobius.extendedComplexEuclideanHomeomorph.symm
      (N.realReflection (_root_.LowDimensionalTopology.Geometry.Mobius.extendedComplexEuclideanHomeomorph p.val)))
    fun_prop
  have he := _root_.LowDimensionalTopology.Geometry.Hyperbolic.denseRange_halfPlaneToClosedModel.equalizer
    (continuous_subtype_val.comp N.closedReflectionHomeomorph.continuous) hc (by
      funext z
      change (N.closedReflectionHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel
        z)).val =
        _root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom N.realReflection ((z : ℂ) :
          _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      rw [N.closedReflectionHomeomorph_finite,N.realReflection_coe]
      rfl)
  exact congrFun he p

/-- The actual reflection on the whole finite/ideal compactification is involutive. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.closedReflectionHomeomorph_involutive (N :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    Function.Involutive N.closedReflectionHomeomorph := by
  have he := _root_.LowDimensionalTopology.Geometry.Hyperbolic.denseRange_halfPlaneToClosedModel.equalizer
    (N.closedReflectionHomeomorph.continuous.comp N.closedReflectionHomeomorph.continuous)
    continuous_id (by
      funext z
      change N.closedReflectionHomeomorph (N.closedReflectionHomeomorph
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel z)) = _
      rw [N.closedReflectionHomeomorph_finite,N.closedReflectionHomeomorph_finite,N.reflection_involutive z]
      rfl)
  exact congrFun he

/-- Ideal ends are exactly the boundary points lying on the genuine full generalized circle. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.idealEndpoint_iff_extendedCircle (N :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (p :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hp : p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary) : p ∈ N.idealEndpoints ↔ p ∈ N.extendedCircle.val := by
  induction p using OnePoint.rec with
  | infty => cases N <;> simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.vertical_idealEndpoints,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circle_idealEndpoints,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.extendedCircle]
  | coe z =>
    have hz := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary z).mp hp
    have hzr : z=(z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hz
    rw [hzr]
    cases N with
    | vertical x => simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.vertical_idealEndpoints,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.extendedCircle,Complex.inner]
    | circle c r hr =>
      simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circle_idealEndpoints,mem_insert_iff,mem_singleton_iff,OnePoint.coe_eq_coe,
        Complex.ofReal_inj,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.extendedCircle,_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe]
      rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_eq (le_of_lt hr)]
      constructor <;> rintro (h|h) <;> first | (left; linarith) | (right; linarith)

/-- The genuine whole-line closure is precisely its full generalized circle in the closed model. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.closedCarrier_iff_extendedCircle (N :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (p :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel) :
    p ∈ N.closedCarrier ↔ p.val ∈ N.extendedCircle.val := by
  by_cases hp : p.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary
  · exact (N.closedCarrier_mem_ideal_iff p hp).trans (N.idealEndpoint_iff_extendedCircle p.val hp)
  · obtain ⟨z,hz⟩ : ∃ z : ℍ,p=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel z := by
      rcases p with ⟨p,hpC⟩
      induction p using OnePoint.rec with
      | infty => exact (hp (by simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary])).elim
      | coe z =>
        have hz0 := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_closedHalfPlaneSet z).mp hpC
        have hz1 : z.im ≠ 0 := by
          intro he
          exact hp ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary z).mpr he)
        exact ⟨⟨z,lt_of_le_of_ne hz0 (Ne.symm hz1)⟩,rfl⟩
    rw [hz,N.closedCarrier_mem_interior_iff]
    exact (N.mem_extendedCircle z).symm

/-- Its whole fixed set is the actual compactified mirror, with no extra ideal fixed point. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.closedReflectionHomeomorph_fixed_iff (N :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (p :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel) :
    N.closedReflectionHomeomorph p = p ↔ p ∈ N.closedCarrier := by
  rw [Subtype.ext_iff,N.closedReflectionHomeomorph_ambient,N.closedCarrier_iff_extendedCircle,
    ← N.realReflection_fixedPoints]
  rfl

/-- Every finite or ideal point off the foot on a perpendicular h-line is moved by the mirror. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.closedReflection_ne_of_perpendicular (N M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (d : ℍ)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel) (hd : N.OrthogonalAt M d) (hp : p ∈
      M.closedCarrier)
    (hpd : p ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel d) : N.closedReflectionHomeomorph p ≠ p := by
  intro he
  have hpN := (N.closedReflectionHomeomorph_fixed_iff p).mp he
  exact (N.ne_of_orthogonalAt M d hd) (N.eq_of_two_closed_points M hpd hpN
    ((N.closedCarrier_mem_interior_iff d).mpr hd.1) hp
    ((M.closedCarrier_mem_interior_iff d).mpr hd.2.1))

/-- The genuine disc mirror, with its actual finite/ideal extension and actual path-distance isometry. -/
def _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedReflectionIsometry (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscIsometry where
  finiteMap := L.reflection
  distance_eq := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIsometry_native_distance L.toHalfPlane.reflection_isometry
  closedMap := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm.trans
    (L.toHalfPlane.closedReflectionHomeomorph.trans
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph)
  finite_commutes z := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph
      (L.toHalfPlane.closedReflectionHomeomorph
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z))) = _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_inverse_finite,L.toHalfPlane.closedReflectionHomeomorph_finite,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior]
    rfl

/-- The compactified disc mirror has exactly its genuine compactified h-line as fixed set. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedReflectionIsometry_fixed_iff (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (p : 𝕔𝔻) :
    L.closedReflectionIsometry.closedMap p = p ↔ p ∈ L.closedCarrier := by
  have he : L.closedReflectionIsometry.closedMap p = p ↔
      L.toHalfPlane.closedReflectionHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p) =
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p := by
    constructor
    · intro h
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph
        (L.toHalfPlane.closedReflectionHomeomorph
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p)) = p at h
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.injective (by simpa only
        [Homeomorph.apply_symm_apply] using h)
    · intro h
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph
        (L.toHalfPlane.closedReflectionHomeomorph
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p)) = p
      rw [h,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.apply_symm_apply]
  rw [he,L.toHalfPlane.closedReflectionHomeomorph_fixed_iff]
  exact (L.closedCarrier_cayley_mem (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm
    p)).symm.trans
    (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.apply_symm_apply])

/-- The native finite mirror fixes precisely the genuine finite h-line. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.reflection_fixed_iff (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (z : 𝔻) :
    L.reflection z = z ↔ z ∈ L.carrier := by
  have he := L.closedReflectionIsometry_fixed_iff (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    z)
  rw [L.closedReflectionIsometry.finite_commutes,L.closedCarrier_mem_interior_iff] at he
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective.eq_iff).symm.trans he

/-- The native closed mirror is involutive, including both ideal ends. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedReflectionIsometry_involutive (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) :
    Function.Involutive L.closedReflectionIsometry.closedMap := by
  intro p
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph
    (L.toHalfPlane.closedReflectionHomeomorph
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph
        (L.toHalfPlane.closedReflectionHomeomorph
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p))))) = p
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm_apply_apply,L.toHalfPlane.closedReflectionHomeomorph_involutive,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.apply_symm_apply]

/-- Genuine disc mirror images preserve perpendicular complete finite/ideal sides. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedReflection_image_of_orthogonalAt (N M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (d : 𝔻)
    (hd : N.OrthogonalAt M d) :
    N.closedReflectionIsometry.closedMap '' M.closedCarrier = M.closedCarrier := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph (N.toHalfPlane.closedReflectionHomeomorph
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm q)) ∈ M.closedCarrier
    apply (M.closedCarrier_cayley_mem _).mpr
    rw [← N.toHalfPlane.closedReflection_image_of_orthogonalAt M.toHalfPlane
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane d) ((N.orthogonalAt_iff_halfPlane M d).mp hd)]
    exact mem_image_of_mem _ ((M.closedCarrier_cayley_mem _).mp
      (by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.apply_symm_apply]))
  · intro hp
    refine ⟨N.closedReflectionIsometry.closedMap p,?_,N.closedReflectionIsometry_involutive p⟩
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph (N.toHalfPlane.closedReflectionHomeomorph
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p)) ∈ M.closedCarrier
    apply (M.closedCarrier_cayley_mem _).mpr
    rw [← N.toHalfPlane.closedReflection_image_of_orthogonalAt M.toHalfPlane
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane d) ((N.orthogonalAt_iff_halfPlane M d).mp hd)]
    exact mem_image_of_mem _ ((M.closedCarrier_cayley_mem _).mp
      (by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.apply_symm_apply]))

/-- A genuine mirror moves every other finite or ideal point on a perpendicular side. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedReflection_ne_of_perpendicular (N M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (d : 𝔻)
    (p : 𝕔𝔻) (hd : N.OrthogonalAt M d) (hp : p ∈ M.closedCarrier)
    (hpd : p ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel d) : N.closedReflectionIsometry.closedMap p ≠ p := by
  intro he
  have hpN := (N.closedReflectionIsometry_fixed_iff p).mp he
  have hNM := N.toHalfPlane.ne_of_orthogonalAt M.toHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane d)
    ((N.orthogonalAt_iff_halfPlane M d).mp hd)
  apply hNM
  apply congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane
  apply N.eq_of_two_closed_points M hpd hpN
    ((N.closedCarrier_mem_interior_iff d).mpr hd.1) hp
    ((M.closedCarrier_mem_interior_iff d).mpr hd.2.1)

/-- The actual finite foot lies between a point and its genuine mirror, with the exact doubled distance. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.reflection_perpendicular_midpoint (N M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (d c : 𝔻)
    (hd : N.OrthogonalAt M d) (hc : c ∈ M.carrier) (hcd : c ≠ d) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel d ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel c)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (N.reflection c)) ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist c (N.reflection c) = 2 * _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist c d := by
  have hh := N.toHalfPlane.reflection_perpendicular_midpoint M.toHalfPlane
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      d) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane c) ((N.orthogonalAt_iff_halfPlane M d).mp
      hd)
    ((M.mem_carrier c).mp hc) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective.ne hcd)
  constructor
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_interior]
    apply mem_image_of_mem
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHSegment_eq_cayley_image]
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      d,?_,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane d⟩
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.reflection,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using hh.1
  · simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.reflection,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using hh.2

/-- Moving one endpoint farther out along its genuine corner ray leaves the actual angle unchanged. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.alpha_eq_of_sideC_subdivision (T U :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (d : 𝔻)
    (ha : U.a=T.a) (hc : U.c=T.c) (hd : T.b=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel d)
    (hdU : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel d ∈ U.sideC) : U.alpha=T.alpha := by
  rcases _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDisc_interior_or_ideal T.a with ⟨z,hz⟩ | hz
  · have hT : T.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := hz.symm
    have hU : U.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := ha.trans hT
    have hzd : z ≠ d := by
      intro he
      exact T.a_ne_b (hT.trans ((congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel he).trans
        hd.symm))
    have hR : U.cornerRayABAtA z hU=T.cornerRayABAtA z hT := by
      apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.eq_of_shared_point _ _ hzd
      · exact U.cornerAtA_sideC_finite_subset z hU hdU
      · apply T.cornerAtA_sideC_finite_subset z hT
        change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel d ∈ T.sideC
        rw [← hd,T.mem_sideC_iff_coordinate,T.coordinate_b]
        norm_num
    have hzc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ≠ T.c := hT ▸ T.c_ne_a.symm
    have hzcU : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ≠ U.c := hc ▸ hzc
    have hS : U.cornerRayACAtA z hU=T.cornerRayACAtA z hT := by
      rw [← U.rayToward_c z hU hzcU,← T.rayToward_c z hT hzc]
      simp only [hc]
    rw [U.alpha_of_finite z hU,T.alpha_of_finite z hT]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure _ _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure _ _
    rw [hR,hS]
  · rw [U.alpha_of_ideal (by rw [ha];exact hz),T.alpha_of_ideal hz]

/-- True perpendicular adjacent supports give the actual right triangle angle. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.alpha_eq_pi_div_two_of_normalPairing_zero (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle)
    (hpair : T.sideLineB.toHalfPlane.normalPairing T.sideLineC.toHalfPlane=0) :
    T.alpha=Real.pi/2 := by
  obtain ⟨q,hq⟩ := T.interior_nonempty
  have hp := T.discCoordinate_image_interior ▸ mem_image_of_mem T.discCoordinate hq
  change 0<(T.discCoordinate q).1 ∧ 0<(T.discCoordinate q).2 ∧ _ at hp
  have hn := T.positive_coordinates_not_adjacent_sides q ⟨hp.1,hp.2.1⟩
  let F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q)
  let G := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q)
  have hF : F ≠ 0 := by
    intro h
    exact hn.1 ((T.sideLineB.closedCarrier_mem_interior_iff q).mp
      ((T.sideLineB.closed_incenter_affine_zero_iff _).mp h))
  have hG : G ≠ 0 := by
    intro h
    exact hn.2 ((T.sideLineC.closedCarrier_mem_interior_iff q).mp
      ((T.sideLineC.closed_incenter_affine_zero_iff _).mp h))
  have he := T.cosine_alpha_side_normals q hq
  change Real.cos T.alpha * |F| * |G|= -(T.sideLineB.toHalfPlane.normalPairing
    T.sideLineC.toHalfPlane*F*G) at he
  rw [hpair,zero_mul,zero_mul,neg_zero] at he
  have hc : Real.cos T.alpha=0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (abs_ne_zero.mpr hG))).resolve_right (abs_ne_zero.mpr hF)
  have hb := T.alpha_mem_Ico
  apply Real.injOn_cos ⟨hb.1,hb.2.le⟩ ⟨by positivity,by linarith [Real.pi_pos]⟩
  rw [hc,Real.cos_pi_div_two]

/-- The reflected summit is distinct even when the original fourth vertex is ideal. -/
theorem LambertQuadrilateral.reflected_summit_ne (Q : LambertQuadrilateral) :
    Q.left.closedReflectionIsometry.closedMap Q.corner.a ≠ Q.corner.a := by
  apply Q.left.closedReflection_ne_of_perpendicular Q.corner.sideLineC Q.d Q.corner.a
    Q.angle_d Q.corner.a_mem_sideLineC
  rw [← Q.vertex_d]
  exact Q.corner.a_ne_b

/-- The reflected summit remains on the genuine whole upper side. -/
theorem LambertQuadrilateral.reflected_summit_mem (Q : LambertQuadrilateral) :
    Q.left.closedReflectionIsometry.closedMap Q.corner.a ∈ Q.corner.sideLineC.closedCarrier := by
  rw [← Q.left.closedReflection_image_of_orthogonalAt Q.corner.sideLineC Q.d Q.angle_d]
  exact mem_image_of_mem _ Q.corner.a_mem_sideLineC

/-- The genuine summit corner after reflection, with a finite or ideal summit. -/
def LambertQuadrilateral.saccheriSummitCorner (Q :
  LambertQuadrilateral) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle where
  a := Q.corner.a
  b := Q.left.closedReflectionIsometry.closedMap Q.corner.a
  c := Q.corner.c
  noncollinear := by
    rintro ⟨L,hC,hC',hB⟩
    have hLM : L=Q.corner.sideLineC := L.eq_of_two_closed_points Q.corner.sideLineC
      Q.reflected_summit_ne.symm hC hC' Q.corner.a_mem_sideLineC Q.reflected_summit_mem
    exact Q.corner.noncollinear ⟨Q.corner.sideLineC,Q.corner.a_mem_sideLineC,
      Q.corner.b_mem_sideLineC,hLM ▸ hB⟩

/-- The original upper midpoint lies on the genuine closed summit edge. -/
theorem LambertQuadrilateral.saccheriSummitCorner_midpoint (Q : LambertQuadrilateral)
    (z : 𝔻) (hz : Q.corner.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.d ∈ Q.saccheriSummitCorner.sideC := by
  have hm := Q.left.reflection_perpendicular_midpoint Q.corner.sideLineC Q.d z Q.angle_d
    ((Q.corner.sideLineC.closedCarrier_mem_interior_iff z).mp (hz ▸ Q.corner.a_mem_sideLineC))
    (by intro he; exact Q.corner.a_ne_b (hz.trans ((congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel he).trans Q.vertex_d.symm)))
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.d ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment Q.corner.a
    (Q.left.closedReflectionIsometry.closedMap Q.corner.a)
  rw [hz,Q.left.closedReflectionIsometry.finite_commutes]
  exact hm.1

/-- The actual angle at either finite or ideal summit is the original Lambert angle. -/
theorem LambertQuadrilateral.saccheriSummitCorner_angle (Q : LambertQuadrilateral) :
    Q.saccheriSummitCorner.alpha=Q.angle := by
  rcases _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDisc_interior_or_ideal Q.corner.a with ⟨z,hz⟩ | hz
  · exact Q.corner.alpha_eq_of_sideC_subdivision Q.saccheriSummitCorner Q.d rfl rfl Q.vertex_d
      (Q.saccheriSummitCorner_midpoint z hz.symm)
  · change Q.saccheriSummitCorner.alpha=Q.corner.alpha
    rw [Q.saccheriSummitCorner.alpha_of_ideal hz,Q.corner.alpha_of_ideal hz]

/-- The genuine base vertex is moved by reflection in the adjacent side. -/
theorem LambertQuadrilateral.reflected_base_ne (Q : LambertQuadrilateral) :
    Q.left.reflection Q.b ≠ Q.b := by
  have hsym : Q.left.OrthogonalAt Q.bottom Q.a :=
    ⟨Q.angle_a.2.1,Q.angle_a.1,by rw [real_inner_comm];exact Q.angle_a.2.2⟩
  have he := Q.left.closedReflection_ne_of_perpendicular Q.bottom Q.a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.b)
    hsym ((Q.bottom.closedCarrier_mem_interior_iff Q.b).mpr Q.angle_b.1)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective.ne Q.a_ne_b.symm)
  rw [Q.left.closedReflectionIsometry.finite_commutes] at he
  exact fun h => he (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel h)

/-- Its genuine reflected base endpoint remains on the same complete base h-line. -/
theorem LambertQuadrilateral.reflected_base_mem (Q : LambertQuadrilateral) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (Q.left.reflection Q.b) ∈ Q.bottom.closedCarrier := by
  have hsym : Q.left.OrthogonalAt Q.bottom Q.a :=
    ⟨Q.angle_a.2.1,Q.angle_a.1,by rw [real_inner_comm];exact Q.angle_a.2.2⟩
  rw [← Q.left.closedReflection_image_of_orthogonalAt Q.bottom Q.a hsym]
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    Q.b,(Q.bottom.closedCarrier_mem_interior_iff Q.b).mpr Q.angle_b.1,?_⟩
  exact Q.left.closedReflectionIsometry.finite_commutes Q.b

/-- The finite or ideal summit cannot belong to the base h-line. -/
theorem LambertQuadrilateral.summit_not_mem_base (Q : LambertQuadrilateral) :
    Q.corner.a ∉ Q.bottom.closedCarrier := by
  intro hp
  have hCB : Q.corner.a ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.b := Q.vertex_b ▸ Q.corner.c_ne_a.symm
  have he := Q.bottom.eq_of_two_closed_points Q.corner.sideLineB hCB hp
    ((Q.bottom.closedCarrier_mem_interior_iff Q.b).mpr Q.angle_b.1) Q.corner.a_mem_sideLineB
    (Q.vertex_b ▸ Q.corner.c_mem_sideLineB)
  exact (Q.bottom.toHalfPlane.ne_of_orthogonalAt Q.corner.sideLineB.toHalfPlane
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.b)
    ((Q.bottom.orthogonalAt_iff_halfPlane Q.corner.sideLineB Q.b).mp Q.angle_b))
    (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane he)

/-- The genuine lower corner has the full reflected base ray, rather than a subdivided auxiliary ray. -/
def LambertQuadrilateral.saccheriBaseCorner (Q :
  LambertQuadrilateral) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle where
  a := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.b
  b := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (Q.left.reflection Q.b)
  c := Q.corner.a
  noncollinear := by
    rintro ⟨L,hB,hB',hC⟩
    have he := L.eq_of_two_closed_points Q.bottom
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective.ne
        Q.reflected_base_ne.symm) hB hB'
      ((Q.bottom.closedCarrier_mem_interior_iff Q.b).mpr Q.angle_b.1) Q.reflected_base_mem
    exact Q.summit_not_mem_base (he ▸ hC)

/-- The actual summit leg is the original right side of the Lambert quadrilateral. -/
theorem LambertQuadrilateral.saccheriBaseCorner_sideLineB (Q : LambertQuadrilateral) :
    Q.saccheriBaseCorner.sideLineB=Q.corner.sideLineB := by
  apply Q.saccheriBaseCorner.sideLineB.eq_of_two_closed_points Q.corner.sideLineB
    Q.saccheriBaseCorner.c_ne_a
    Q.saccheriBaseCorner.c_mem_sideLineB Q.saccheriBaseCorner.a_mem_sideLineB
    Q.corner.a_mem_sideLineB
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.b ∈ Q.corner.sideLineB.closedCarrier
  exact Q.vertex_b ▸ Q.corner.c_mem_sideLineB

/-- The genuine reflected base determines the same actual base support. -/
theorem LambertQuadrilateral.saccheriBaseCorner_sideLineC (Q : LambertQuadrilateral) :
    Q.saccheriBaseCorner.sideLineC=Q.bottom := by
  exact Q.saccheriBaseCorner.sideLineC.eq_of_two_closed_points Q.bottom
    Q.saccheriBaseCorner.a_ne_b Q.saccheriBaseCorner.a_mem_sideLineC
    Q.saccheriBaseCorner.b_mem_sideLineC
    ((Q.bottom.closedCarrier_mem_interior_iff Q.b).mpr Q.angle_b.1) Q.reflected_base_mem

/-- The actual lower corner of the reflected quadrilateral is a right angle. -/
theorem LambertQuadrilateral.saccheriBaseCorner_angle (Q : LambertQuadrilateral) :
    Q.saccheriBaseCorner.alpha=Real.pi/2 := by
  apply Q.saccheriBaseCorner.alpha_eq_pi_div_two_of_normalPairing_zero
  rw [Q.saccheriBaseCorner_sideLineB,Q.saccheriBaseCorner_sideLineC]
  apply Q.corner.sideLineB.toHalfPlane.normalPairing_orthogonal Q.bottom.toHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane Q.b)
  have hb := (Q.bottom.orthogonalAt_iff_halfPlane Q.corner.sideLineB Q.b).mp Q.angle_b
  exact ⟨hb.2.1,hb.1,by rw [real_inner_comm];exact hb.2.2⟩

/-- All four genuine corner angles in the mirror construction, including ideal summits. -/
theorem LambertQuadrilateral.saccheri_corner_angles (Q : LambertQuadrilateral) :
    Q.saccheriBaseCorner.alpha=Real.pi/2 ∧
    (Q.saccheriBaseCorner.mapClosedIsometry Q.left.closedReflectionIsometry).alpha=Real.pi/2 ∧
    Q.saccheriSummitCorner.alpha=Q.angle ∧
    (Q.saccheriSummitCorner.mapClosedIsometry Q.left.closedReflectionIsometry).alpha=Q.angle := by
  exact ⟨Q.saccheriBaseCorner_angle,
    (Q.saccheriBaseCorner.mapClosedIsometry_alpha _).trans Q.saccheriBaseCorner_angle,
    Q.saccheriSummitCorner_angle,
    (Q.saccheriSummitCorner.mapClosedIsometry_alpha _).trans Q.saccheriSummitCorner_angle⟩

/-- The actual four successive vertices of the reflected quadrilateral. -/
def LambertQuadrilateral.saccheriVertices (Q : LambertQuadrilateral) : Fin 4 → 𝕔𝔻 :=
  ![_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    Q.b,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (Q.left.reflection Q.b),
    Q.left.closedReflectionIsometry.closedMap Q.corner.a,Q.corner.a]

/-- All four successive vertices are distinct, including in the ideal-summit case. -/
theorem LambertQuadrilateral.saccheriVertices_injective (Q : LambertQuadrilateral) :
    Function.Injective Q.saccheriVertices := by
  have hBC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.b ≠ Q.corner.a := Q.vertex_b ▸ Q.corner.c_ne_a
  have hBB' := _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective.ne Q.reflected_base_ne.symm
  have hCC' := Q.reflected_summit_ne.symm
  have hB'C : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (Q.left.reflection Q.b) ≠ Q.corner.a := by
    intro h
    exact Q.summit_not_mem_base (h ▸ Q.reflected_base_mem)
  have hBC' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.b ≠ Q.left.closedReflectionIsometry.closedMap Q.corner.a := by
    intro h
    exact Q.corner.c_not_mem_sideLineC (Q.vertex_b.symm ▸ (h.symm ▸ Q.reflected_summit_mem))
  have hB'C' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (Q.left.reflection Q.b) ≠
      Q.left.closedReflectionIsometry.closedMap Q.corner.a := by
    have hmap := Q.left.closedReflectionIsometry.finite_commutes Q.b
    change Q.left.closedReflectionIsometry.closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.b) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (Q.left.reflection Q.b) at hmap
    rw [← hmap]
    exact Q.left.closedReflectionIsometry.closedMap.injective.ne hBC
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [LambertQuadrilateral.saccheriVertices]

/-- The four actual corner triangles use the full adjacent rays of the reflected quadrilateral. -/
def LambertQuadrilateral.saccheriCorner (Q :
  LambertQuadrilateral) : Fin 4 → _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle :=
  ![Q.saccheriBaseCorner,Q.saccheriBaseCorner.mapClosedIsometry Q.left.closedReflectionIsometry,
    Q.saccheriSummitCorner.mapClosedIsometry Q.left.closedReflectionIsometry,Q.saccheriSummitCorner]

theorem LambertQuadrilateral.saccheriCorner_vertices (Q : LambertQuadrilateral) (i : Fin 4) :
    (Q.saccheriCorner i).a=Q.saccheriVertices i ∧
    ({(Q.saccheriCorner i).b,(Q.saccheriCorner i).c} : Set 𝕔𝔻)=
      {Q.saccheriVertices (i-1),Q.saccheriVertices (i+1)} := by
  have hB := Q.left.closedReflectionIsometry.finite_commutes Q.b
  change Q.left.closedReflectionIsometry.closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    Q.b) =
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (Q.left.reflection Q.b) at hB
  have hC := Q.left.closedReflectionIsometry_involutive Q.corner.a
  have hB' : Q.left.closedReflectionIsometry.closedMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (Q.left.reflection Q.b)) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.b := by
    rw [← hB,Q.left.closedReflectionIsometry_involutive]
  fin_cases i <;> simp [LambertQuadrilateral.saccheriCorner,LambertQuadrilateral.saccheriVertices,LambertQuadrilateral.saccheriBaseCorner,LambertQuadrilateral.saccheriSummitCorner,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.mapClosedIsometry,hB,hB',hC,Q.vertex_b,Set.pair_comm]

/-- The exact two right base angles and two original summit angles. -/
theorem LambertQuadrilateral.saccheriCorner_angles (Q : LambertQuadrilateral) (i : Fin 4) :
    (Q.saccheriCorner i).alpha=if i=0 ∨ i=1 then Real.pi/2 else Q.angle := by
  fin_cases i <;> simp [LambertQuadrilateral.saccheriCorner,Q.saccheriBaseCorner_angle,Q.saccheriSummitCorner_angle,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.mapClosedIsometry_alpha]

/-- The two genuine legs have equal finite or infinite side length. -/
theorem LambertQuadrilateral.saccheri_legs_equal (Q : LambertQuadrilateral) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (Q.saccheriVertices 0) (Q.saccheriVertices
      3) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscSideLength (Q.saccheriVertices 1) (Q.saccheriVertices 2) := by
  have he := Q.left.closedReflectionIsometry.extendedSideLength_eq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel Q.b) Q.corner.a
  rw [Q.left.closedReflectionIsometry.finite_commutes] at he
  exact he.symm

end
end LowDimensionalTopology.Geometry.Polygon
