module
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.LocalAngularMeasure
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CompactPolygonTranslates
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.Measure.PolygonMultiplicityArea
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- The actual native isometry in the genuine conformal disc coordinate. -/
def nativeDiscIsometry (f : ℍ≃ᵢℍ) : Complex.UnitDisc≃ₜComplex.UnitDisc :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm.trans
    f.toHomeomorph).trans _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph

theorem nativeDiscIsometry_isometry (f : ℍ≃ᵢℍ) :
    let :=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric; Isometry (nativeDiscIsometry f) := by
  let :=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  apply Isometry.of_dist_eq
  intro z w
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (f (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (f
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      w)))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z w
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIsometry_native_distance f.isometry z w

def nativeLocalAngularFraction (P : Set ℍ) (z : ℍ) : ℝ≥0∞ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngularFraction (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' P) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)

def nativeLocalAngle (P : Set ℍ) (z : ℍ) : ℝ :=
  2*Real.pi*(nativeLocalAngularFraction P z).toReal

theorem nativeLocalAngularFraction_isometry (f : ℍ≃ᵢℍ) (P : Set ℍ) (z : ℍ) :
    nativeLocalAngularFraction (f '' P) (f z)=nativeLocalAngularFraction P z := by
  have he : nativeDiscIsometry f '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' P)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' (f '' P) := by
    simp only [image_image]
    congr 1
    funext w
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (f
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w)))=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  have hz : nativeDiscIsometry f (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (f z) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (f
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)))=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  unfold nativeLocalAngularFraction
  rw [←he,←hz]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngularFraction_isometry _ (nativeDiscIsometry_isometry f) _ _

theorem nativeLocalAngularFraction_of_interior {P : Set ℍ} {z : ℍ}
    (hz : z∈interior P) : nativeLocalAngularFraction P z=1 := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngularFraction_of_interior
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph z∈interior (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph '' P)
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.image_interior]
  exact mem_image_of_mem _ hz

theorem nativeLocalAngularFraction_of_not_mem_closure {P : Set ℍ} {z : ℍ}
    (hz : z∉closure P) : nativeLocalAngularFraction P z=0 := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngularFraction_of_not_mem_closure
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph z∉closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph '' P)
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.image_closure,_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective.mem_set_image]
  exact hz

theorem nativeLocalAngularFraction_le_one (P : Set ℍ) (z : ℍ) :
    nativeLocalAngularFraction P z≤1 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngularFraction_le_one _ _

theorem nativeLocalAngularFraction_eq_indicator_off_frontier (P : Set ℍ) (z : ℍ)
    (hz : z∉frontier P) :
    nativeLocalAngularFraction P z=P.indicator (fun _ : ℍ=>(1 : ℝ≥0∞)) z := by
  by_cases hm : z∈P
  · rw [indicator_of_mem hm]
    exact nativeLocalAngularFraction_of_interior ((mem_interior_iff_notMem_frontier hm).mpr hz)
  · rw [indicator_of_notMem hm]
    apply nativeLocalAngularFraction_of_not_mem_closure
    intro hc
    exact hz ⟨hc,fun hi=>hm (interior_subset hi)⟩

/-- The actual sum of the original polygon's local angular fractions over every
literal translate label. Each term is a genuine local angle rather than a prescribed weight. -/
def nativePolygonAngularMultiplicity (H : Subgroup (ℍ≃ᵢℍ)) (P : Set ℍ) (z : ℍ) : ℝ≥0∞ :=
  ∑' g : H,nativeLocalAngularFraction P (g⁻¹ • z)

/-- The source angular multiplicity in radians. -/
def nativePolygonAngularMultiplicityRadians (H : Subgroup (ℍ≃ᵢℍ)) (P : Set ℍ) (z : ℍ) : ℝ :=
  2*Real.pi*(nativePolygonAngularMultiplicity H P z).toReal

/-- The inverse-point expression is exactly the sum of the actual angles of every
original translated polygon at the original specified point. -/
theorem nativePolygonAngularMultiplicity_eq_translated (H : Subgroup (ℍ≃ᵢℍ))
    (P : Set ℍ) (z : ℍ) :
    nativePolygonAngularMultiplicity H P z=∑'g : H,nativeLocalAngularFraction (g • P) z := by
  apply tsum_congr
  intro g
  have he:=nativeLocalAngularFraction_isometry g.val P (g⁻¹ • z)
  change nativeLocalAngularFraction ((fun w : ℍ=>g • w) '' P) (g • (g⁻¹ • z))=
    nativeLocalAngularFraction P (g⁻¹ • z) at he
  simpa only [smul_inv_smul,image_smul] using he.symm

/-- The literal angular multiplicity is invariant under every element of its actual group. -/
theorem nativePolygonAngularMultiplicity_smul (H : Subgroup (ℍ≃ᵢℍ))
    (P : Set ℍ) (h : H) (z : ℍ) :
    nativePolygonAngularMultiplicity H P (h • z)=nativePolygonAngularMultiplicity H P z := by
  unfold nativePolygonAngularMultiplicity
  calc
    (∑'g : H,nativeLocalAngularFraction P (g⁻¹ • (h • z)))=
      ∑'k : H,nativeLocalAngularFraction P ((h*k)⁻¹ • (h • z)):=
        ((Equiv.mulLeft h).tsum_eq _).symm
    _=_:=tsum_congr (fun _=>by simp [mul_smul])

/-- Away from every actual translated boundary, the actual angular fraction sum is
exactly the genuine integer count of original translates containing the point. -/
theorem nativePolygonAngularMultiplicity_eq_orbital_off_frontiers
    (H : Subgroup (ℍ≃ᵢℍ)) (P : Set ℍ) (z : ℍ)
    (hz : ∀g : H,z∉frontier (g • P)) :
    nativePolygonAngularMultiplicity H P z=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitalCoverMultiplicity H P z := by
  rw [nativePolygonAngularMultiplicity_eq_translated]
  apply tsum_congr
  intro g
  rw [nativeLocalAngularFraction_eq_indicator_off_frontier _ _ (hz g)]
  by_cases hm : z∈g • P
  · rw [indicator_of_mem hm,indicator_of_mem (mem_smul_set_iff_inv_smul_mem.mp hm)]
  · rw [indicator_of_notMem hm,
      indicator_of_notMem (fun h=>hm (mem_smul_set_iff_inv_smul_mem.mpr h))]

theorem nativeLocalAngle_of_interior {P : Set ℍ} {z : ℍ} (hz : z∈interior P) :
    nativeLocalAngle P z=2*Real.pi := by
  rw [nativeLocalAngle,nativeLocalAngularFraction_of_interior hz,ENNReal.toReal_one,mul_one]

theorem nativeLocalAngle_of_not_mem_closure {P : Set ℍ} {z : ℍ} (hz : z∉closure P) :
    nativeLocalAngle P z=0 := by
  rw [nativeLocalAngle,nativeLocalAngularFraction_of_not_mem_closure hz,ENNReal.toReal_zero,mul_zero]

/-- Compactness and the actual discreteness theorem reduce the infinite original sum
to its genuine finite set of incident original translate labels. -/
theorem nativePolygonAngularMultiplicity_eq_sum_incident (H : Subgroup (ℍ≃ᵢℍ))
    [DiscreteTopology H] (P : Set ℍ) (hP : IsCompact P) (z : ℍ) :
    nativePolygonAngularMultiplicity H P z=
      ∑g∈((_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite H hP).point_finite
        z).toFinset,
        nativeLocalAngularFraction P (g⁻¹ • z) := by
  classical
  unfold nativePolygonAngularMultiplicity
  apply tsum_eq_sum
  intro g hg
  apply nativeLocalAngularFraction_of_not_mem_closure
  rw [hP.isClosed.closure_eq]
  intro hm
  apply hg
  rw [Set.Finite.mem_toFinset]
  change z∈g • P
  exact mem_smul_set_iff_inv_smul_mem.mpr hm

theorem nativePolygonAngularMultiplicity_le_incident_card (H : Subgroup (ℍ≃ᵢℍ))
    [DiscreteTopology H] (P : Set ℍ) (hP : IsCompact P) (z : ℍ) :
    nativePolygonAngularMultiplicity H P z≤
      (((_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite H hP).point_finite z).toFinset.card : ℝ≥0∞) := by
  classical
  rw [nativePolygonAngularMultiplicity_eq_sum_incident H P hP z]
  calc
    _≤∑g∈((_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite H hP).point_finite
      z).toFinset,
      (1 : ℝ≥0∞):=Finset.sum_le_sum (fun _ _=>nativeLocalAngularFraction_le_one _ _)
    _=_:=by simp

theorem nativePolygonAngularMultiplicity_lt_top (H : Subgroup (ℍ≃ᵢℍ))
    [DiscreteTopology H] (P : Set ℍ) (hP : IsCompact P) (z : ℍ) :
    nativePolygonAngularMultiplicity H P z<⊤ := by
  exact lt_of_le_of_lt (nativePolygonAngularMultiplicity_le_incident_card H P hP z) (by simp)

/-- The source theta is literally the finite sum of the genuine local angles of all
actual incident polygon images, in radians. -/
theorem nativePolygonAngularMultiplicityRadians_eq_sum (H : Subgroup (ℍ≃ᵢℍ))
    [DiscreteTopology H] (P : Set ℍ) (hP : IsCompact P) (z : ℍ) :
    nativePolygonAngularMultiplicityRadians H P z=
      ∑g∈((_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite H hP).point_finite
        z).toFinset,
        nativeLocalAngle (g • P) z := by
  classical
  unfold nativePolygonAngularMultiplicityRadians
  rw [nativePolygonAngularMultiplicity_eq_sum_incident H P hP z,ENNReal.toReal_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    unfold nativeLocalAngle
    congr 2
    have he:=nativeLocalAngularFraction_isometry g.val P (g⁻¹ • z)
    change nativeLocalAngularFraction ((fun w : ℍ=>g • w) '' P) (g • (g⁻¹ • z))=
      nativeLocalAngularFraction P (g⁻¹ • z) at he
    simpa only [smul_inv_smul,image_smul] using he.symm
  · intro g _
    exact ne_top_of_le_ne_top (by simp) (nativeLocalAngularFraction_le_one _ _)

/-- The actual angular multiplicity is a genuine finite integer off all original
translated polygon boundaries. -/
theorem nativePolygonAngularMultiplicity_exists_nat_off_frontiers
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] (P : Set ℍ) (hP : IsCompact P) (z : ℍ)
    (hz : ∀g : H,z∉frontier (g • P)) :
    ∃k : ℕ,nativePolygonAngularMultiplicity H P z=k := by
  have hf : {g : H | g⁻¹ • z∈P}.Finite:=
    ((_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite H hP).point_finite
      z).subset
      (fun _ hg=>mem_smul_set_iff_inv_smul_mem.mpr hg)
  exact ⟨hf.toFinset.card,(nativePolygonAngularMultiplicity_eq_orbital_off_frontiers H P z hz).trans
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitalCoverMultiplicity_eq_card P z hf)⟩

/-- The source angular sum is locally constant on the actual open complement of all
translated polygon boundaries, with no assumed global constant or pairing conclusion. -/
theorem nativePolygonAngularMultiplicity_locally_constant_off_frontiers
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] (P : Set ℍ) (hP : IsCompact P) (z : ℍ)
    (hz : ∀g : H,z∉frontier (g • P)) :
    ∀ᶠw in 𝓝 z,nativePolygonAngularMultiplicity H P w=nativePolygonAngularMultiplicity H P z := by
  have hLF:=_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite H hP
  have hN : (⋃g : H,frontier (g • P))ᶜ∈𝓝 z:=
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_compl_translated_frontiers_isOpen H hP).mem_nhds (by simpa using hz)
  filter_upwards [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitalCoverMultiplicity_locally_constant_off_boundaries P hLF z hz,hN]
    with w hw hwb
  have hwF : ∀g : H,w∉frontier (g • P):=by simpa using hwb
  rw [nativePolygonAngularMultiplicity_eq_orbital_off_frontiers H P w hwF,
    nativePolygonAngularMultiplicity_eq_orbital_off_frontiers H P z hz]
  exact hw

/-- The original polygon may be open: compactness is required only of its actual
closure, and incident labels are selected by that actual closure. -/
theorem nativePolygonAngularMultiplicity_eq_sum_closure_incident (H : Subgroup (ℍ≃ᵢℍ))
    [DiscreteTopology H] (P : Set ℍ) (hP : IsCompact (closure P)) (z : ℍ) :
    nativePolygonAngularMultiplicity H P z=
      ∑g∈((_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite H hP).point_finite
        z).toFinset,
        nativeLocalAngularFraction P (g⁻¹ • z) := by
  classical
  unfold nativePolygonAngularMultiplicity
  apply tsum_eq_sum
  intro g hg
  apply nativeLocalAngularFraction_of_not_mem_closure
  intro hm
  apply hg
  rw [Set.Finite.mem_toFinset]
  change z∈g • closure P
  exact mem_smul_set_iff_inv_smul_mem.mpr hm

theorem nativePolygonAngularMultiplicity_le_closure_incident_card (H : Subgroup (ℍ≃ᵢℍ))
    [DiscreteTopology H] (P : Set ℍ) (hP : IsCompact (closure P)) (z : ℍ) :
    nativePolygonAngularMultiplicity H P z≤
      (((_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite H hP).point_finite z).toFinset.card : ℝ≥0∞) := by
  classical
  rw [nativePolygonAngularMultiplicity_eq_sum_closure_incident H P hP z]
  calc
    _≤∑g∈((_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite H hP).point_finite
      z).toFinset,
      (1 : ℝ≥0∞):=Finset.sum_le_sum (fun _ _=>nativeLocalAngularFraction_le_one _ _)
    _=_:=by simp

theorem nativePolygonAngularMultiplicity_lt_top_of_compact_closure (H : Subgroup (ℍ≃ᵢℍ))
    [DiscreteTopology H] (P : Set ℍ) (hP : IsCompact (closure P)) (z : ℍ) :
    nativePolygonAngularMultiplicity H P z<⊤ :=
  lt_of_le_of_lt (nativePolygonAngularMultiplicity_le_closure_incident_card H P hP z) (by simp)

/-- For the source open polygon with compact closure, theta is exactly the sum of all
its genuine incident translated angles in radians; no infinity-to-real convention is used. -/
theorem nativePolygonAngularMultiplicityRadians_eq_sum_of_compact_closure
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] (P : Set ℍ)
    (hP : IsCompact (closure P)) (z : ℍ) :
    nativePolygonAngularMultiplicityRadians H P z=
      ∑g∈((_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite H hP).point_finite
        z).toFinset,
        nativeLocalAngle (g • P) z := by
  classical
  unfold nativePolygonAngularMultiplicityRadians
  rw [nativePolygonAngularMultiplicity_eq_sum_closure_incident H P hP z,ENNReal.toReal_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    unfold nativeLocalAngle
    congr 2
    have he:=nativeLocalAngularFraction_isometry g.val P (g⁻¹ • z)
    change nativeLocalAngularFraction ((fun w : ℍ=>g • w) '' P) (g • (g⁻¹ • z))=
      nativeLocalAngularFraction P (g⁻¹ • z) at he
    simpa only [smul_inv_smul,image_smul] using he.symm
  · intro g _
    exact ne_top_of_le_ne_top (by simp) (nativeLocalAngularFraction_le_one _ _)

end LowDimensionalTopology.Geometry.Polygon
