module
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Germs
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.AngularMeasure
public import LowDimensionalTopology.Geometry.Polygon.Triangulation.PolygonMeshBoundaryAngles
public import Mathlib.Analysis.Normed.Operator.Banach

/-! Actual straight boundary points and all original finite-or-ideal corner angles in the derived mesh. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory InnerProductGeometry
open scoped Complex.UnitDisc Classical ENNReal UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- Any genuine closed Euclidean tangent hemisphere has half the normalized angular measure. -/
theorem polygonDirectionMeasure_hemisphere (n : ℂ) (hn : n ≠ 0) :
    2 * Real.pi * (_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure {u : Circle | 0 ≤ inner ℝ (u : ℂ) n}).toReal = Real.pi := by
  let H : Set Circle := {u | 0 ≤ inner ℝ (u : ℂ) n}
  let N : Set Circle := {u | inner ℝ (u : ℂ) n ≤ 0}
  have hN : MeasurableSet N := (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hp : (fun u : Circle => (-1 : Circle) * u) ⁻¹' H = N := by
    ext u
    change 0 ≤ inner ℝ (((-1 : Circle) * u : Circle) : ℂ) n ↔ inner ℝ (u : ℂ) n ≤ 0
    have he : (((-1 : Circle) * u : Circle) : ℂ) = -(u : ℂ) := by
      simp
    rw [he,inner_neg_left,neg_nonneg]
  have hμ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure N = _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure H := by
    rw [← hp]
    exact measure_preimage_mul _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure (-1) H
  have hU : H ∪ N = univ := by
    ext u
    simp only [mem_union,H,N,mem_ofPred_eq,mem_univ,iff_true]
    exact le_total 0 _
  have hI : H ∩ N = {u : Circle | inner ℝ (u : ℂ) n = 0} := by
    ext u
    simp only [mem_inter_iff,H,N,mem_ofPred_eq]
    exact ⟨fun h => le_antisymm h.2 h.1,fun h => ⟨h.symm.le,h.le⟩⟩
  have hd : AEDisjoint _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure H N := by
    rw [AEDisjoint,hI]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.finite_circle_orthogonal n hn).measure_zero _
  have hm := measure_union₀ hN.nullMeasurableSet hd
  rw [hU,_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure_univ,hμ] at hm
  have hr := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_one,ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hr
  change 2 * Real.pi * (_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure H).toReal = Real.pi
  calc
    2 * Real.pi * (_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure H).toReal =
        Real.pi * ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure H).toReal + (_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure H).toReal) := by ring
    _ = Real.pi * 1 := congrArg (fun x : ℝ => Real.pi * x) hr.symm
    _ = Real.pi := mul_one _

theorem discRadialDirections_closed_halfPlane (n : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections {z : 𝔻 | 0 ≤ inner ℝ (z : ℂ) n} =
      {u : Circle | 0 ≤ inner ℝ (u : ℂ) n} := by
  ext u
  constructor
  · rintro ⟨r,hr⟩
    change 0 ≤ inner ℝ (r.val • (u : ℂ)) n at hr
    rw [real_inner_smul_left] at hr
    exact nonneg_of_mul_nonneg_right hr r.property.1
  · intro hu
    refine ⟨⟨(1/2 : ℝ),by norm_num⟩, ?_⟩
    change 0 ≤ inner ℝ ((1/2 : ℝ) • (u : ℂ)) n
    rw [real_inner_smul_left]
    exact mul_nonneg (by norm_num) hu

/-- A genuine tangent half-plane at the native origin subtends precisely a straight angle. -/
theorem discSubtendedAngle_closed_halfPlane (n : ℂ) (hn : n ≠ 0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle {z : 𝔻 | 0 ≤ inner ℝ (z : ℂ) n} 0 = Real.pi := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction_zero,discRadialDirections_closed_halfPlane]
  exact polygonDirectionMeasure_hemisphere n hn

/-- The actual inside of a two-sided local Jordan line is one of its genuine open half-planes. -/
theorem complex_jordan_linear_boundary_halfplane_germ {I O B : Set ℂ} {x : ℂ}
    (hI : IsOpen I) (hO : IsOpen O) (hd : Disjoint I O) (hu : ∀ᶠ y in 𝓝 x, (y ∈ I ∨ y ∈ O) ↔ y ∉ B)
    (hxI : x ∈ frontier I) (hxO : x ∈ frontier O) (f : ℂ →ᵃ[ℝ] ℝ)
    (he : ∀ᶠ y in 𝓝 x, y ∈ B ↔ f y = 0) :
    (∀ᶠ y in 𝓝 x, y ∈ I ↔ 0 < f y) ∨
      (∀ᶠ y in 𝓝 x, y ∈ I ↔ f y < 0) := by
  obtain ⟨r,hr,hre⟩ := Metric.mem_nhds_iff.mp (he.and hu)
  let A : Set ℂ := Metric.ball x r ∩ {y | 0 < f y}
  let C : Set ℂ := Metric.ball x r ∩ {y | f y < 0}
  have hAc : IsPreconnected A :=
    ((convex_ball x r).inter ((convex_Ioi (0 : ℝ)).affine_preimage f)).isPreconnected
  have hCc : IsPreconnected C :=
    ((convex_ball x r).inter ((convex_Iio (0 : ℝ)).affine_preimage f)).isPreconnected
  have hmem (y : ℂ) (hy : y ∈ Metric.ball x r) :
      (y ∈ I ∨ y ∈ O) ↔ f y ≠ 0 := by
    exact ((hre hy).2).trans (not_congr (hre hy).1)
  have hAsub : A ⊆ I ∪ O := by
    intro y hy
    exact (hmem y hy.1).mpr (ne_of_gt hy.2)
  have hCsub : C ⊆ I ∪ O := by
    intro y hy
    exact (hmem y hy.1).mpr (ne_of_lt hy.2)
  have hexI : ∃ y ∈ Metric.ball x r, y ∈ I := by
    exact mem_closure_iff.mp (frontier_subset_closure hxI) (Metric.ball x r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hexO : ∃ y ∈ Metric.ball x r, y ∈ O := by
    exact mem_closure_iff.mp (frontier_subset_closure hxO) (Metric.ball x r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hnotBothI : ¬ (A ⊆ I ∧ C ⊆ I) := by
    rintro ⟨ha,hc⟩
    obtain ⟨y,hy,hyo⟩ := hexO
    have hn := (hmem y hy).mp (Or.inr hyo)
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · exact Set.disjoint_left.mp hd (hc ⟨hy,hneg⟩) hyo
    · exact Set.disjoint_left.mp hd (ha ⟨hy,hpos⟩) hyo
  have hnotBothO : ¬ (A ⊆ O ∧ C ⊆ O) := by
    rintro ⟨ha,hc⟩
    obtain ⟨y,hy,hyi⟩ := hexI
    have hn := (hmem y hy).mp (Or.inl hyi)
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · exact Set.disjoint_left.mp hd hyi (hc ⟨hy,hneg⟩)
    · exact Set.disjoint_left.mp hd hyi (ha ⟨hy,hpos⟩)
  rcases hAc.subset_or_subset hI hO hd hAsub with ha | ha
  · have hc : C ⊆ O := (hCc.subset_or_subset hI hO hd hCsub).resolve_left
      (fun hi => hnotBothI ⟨ha,hi⟩)
    left
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    constructor
    · intro hi
      have hn := (hmem y hy).mp (Or.inl hi)
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · exact (Set.disjoint_left.mp hd hi (hc ⟨hy,hneg⟩)).elim
      · exact hpos
    · intro hypos
      exact ha ⟨hy,hypos⟩
  · have hc : C ⊆ I := (hCc.subset_or_subset hI hO hd hCsub).resolve_right
      (fun ho => hnotBothO ⟨ha,ho⟩)
    right
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    constructor
    · intro hi
      have hn := (hmem y hy).mp (Or.inl hi)
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · exact hneg
      · exact (Set.disjoint_left.mp hd hi (ha ⟨hy,hpos⟩)).elim
    · intro hyneg
      exact hc ⟨hy,hyneg⟩


/-- An open embedding transports genuine set germs to genuine ambient germs. -/
theorem angular_openEmbedding_germ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Topology.IsOpenEmbedding f) {A B : Set X} {x : X}
    (h : ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ B) :
    ∀ᶠ y in 𝓝 (f x), y ∈ f '' A ↔ y ∈ f '' B := by
  have hm : ∀ᶠ y in Filter.map f (𝓝 x), y ∈ f '' A ↔ y ∈ f '' B := by
    change ∀ᶠ y in 𝓝 x, f y ∈ f '' A ↔ f y ∈ f '' B
    simpa only [hf.injective.mem_set_image] using h
  rwa [hf.map_nhds_eq] at hm

theorem discHConvex_closed_halfPlane (n : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex {z : 𝔻 | 0 ≤ inner ℝ (z : ℂ) n} := by
  have he : {z : 𝔻 | 0 ≤ inner ℝ (z : ℂ) n} =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ⁻¹' {p : ℂ | 0 ≤ inner ℝ n p} := by
    ext z
    obtain ⟨c,hc,hK⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_positive_smul z
    change 0 ≤ inner ℝ (z : ℂ) n ↔ 0 ≤ inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z)
    rw [hK,real_inner_smul_right,real_inner_comm n (z : ℂ)]
    exact ⟨mul_nonneg hc.le, fun h => nonneg_of_mul_nonneg_right h hc⟩
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mpr
  rw [he,image_preimage_eq_inter_range,_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
  exact ((convex_Ici (0 : ℝ)).linear_preimage (innerSL ℝ n).toLinearMap).inter (convex_ball _ _)

theorem unitDisc_coe_isOpenEmbedding : Topology.IsOpenEmbedding ((↑) : 𝔻 → ℂ) := by
  refine ⟨Complex.UnitDisc.isEmbedding_coe, ?_⟩
  have hr : range ((↑) : 𝔻 → ℂ) = {z : ℂ | ‖z‖ < 1} := by
    ext w
    exact ⟨fun ⟨z,hz⟩ => hz ▸ z.norm_lt_one,fun hw => ⟨Complex.UnitDisc.mk w hw,rfl⟩⟩
  rw [hr]
  exact isOpen_lt continuous_norm continuous_const

/-- The actual two-sided native Jordan regions at a diameter select a true open tangent half-plane. -/
theorem disc_jordan_linear_boundary_halfplane_germ {I O B : Set 𝔻}
    (hI : IsOpen I) (hO : IsOpen O) (hd : Disjoint I O) (hu : I ∪ O = Bᶜ)
    (h0I : (0 : 𝔻) ∈ frontier I) (h0O : (0 : 𝔻) ∈ frontier O) (n : ℂ)
    (hB : ∀ᶠ w in 𝓝 (0 : 𝔻), w ∈ B ↔ inner ℝ (w : ℂ) n = 0) :
    (∀ᶠ w in 𝓝 (0 : 𝔻), w ∈ I ↔ 0 < inner ℝ (w : ℂ) n) ∨
      (∀ᶠ w in 𝓝 (0 : 𝔻), w ∈ I ↔ inner ℝ (w : ℂ) n < 0) := by
  let e : 𝔻 → ℂ := (↑)
  have he : Topology.IsOpenEmbedding e := unitDisc_coe_isOpenEmbedding
  have he0 : e 0 = 0 := rfl
  have hi : IsOpen (e '' I) := he.isOpenMap _ hI
  have ho : IsOpen (e '' O) := he.isOpenMap _ hO
  have hRange : range e ∈ 𝓝 (0 : ℂ) := by
    rw [← he0]
    exact he.isOpen_range.mem_nhds (mem_range_self 0)
  have hdis : Disjoint (e '' I) (e '' O) :=
    hd.image he.injective.injOn (subset_univ _) (subset_univ _)
  have hfI : (0 : ℂ) ∈ frontier (e '' I) := by
    rw [frontier,hi.interior_eq]
    refine ⟨?_,?_⟩
    · rw [← he0]
      exact (image_closure_subset_closure_image he.continuous)
        (mem_image_of_mem e (frontier_subset_closure h0I))
    · rw [← he0,he.injective.mem_set_image]
      exact fun h => (show (0 : 𝔻) ∉ _root_.interior I from h0I.2) (hI.interior_eq.symm ▸ h)
  have hfO : (0 : ℂ) ∈ frontier (e '' O) := by
    rw [frontier,ho.interior_eq]
    refine ⟨?_,?_⟩
    · rw [← he0]
      exact (image_closure_subset_closure_image he.continuous)
        (mem_image_of_mem e (frontier_subset_closure h0O))
    · rw [← he0,he.injective.mem_set_image]
      exact fun h => (show (0 : 𝔻) ∉ _root_.interior O from h0O.2) (hO.interior_eq.symm ▸ h)
  have hUnion : ∀ᶠ y in 𝓝 (0 : ℂ), (y ∈ e '' I ∨ y ∈ e '' O) ↔ y ∉ e '' B := by
    filter_upwards [hRange] with y hy
    obtain ⟨w,rfl⟩ := hy
    simp only [he.injective.mem_set_image]
    change w ∈ I ∪ O ↔ w ∈ Bᶜ
    rw [hu]
  have hLine : ∀ᶠ y in 𝓝 (0 : ℂ), y ∈ e '' B ↔ inner ℝ n y = 0 := by
    have hm := angular_openEmbedding_germ e he hB
    rw [he0] at hm
    filter_upwards [hm,hRange] with y hy hr
    obtain ⟨w,rfl⟩ := hr
    have hcut : e w ∈ e '' {u : 𝔻 | inner ℝ (u : ℂ) n = 0} ↔ inner ℝ (w : ℂ) n = 0 :=
      he.injective.mem_set_image
    exact hy.trans (hcut.trans (by
      change inner ℝ (w : ℂ) n = 0 ↔ inner ℝ n (w : ℂ) = 0
      rw [real_inner_comm]))
  let f : ℂ →ᵃ[ℝ] ℝ := (innerSL ℝ n).toLinearMap.toAffineMap
  have hf (x : ℂ) : f x = inner ℝ n x := rfl
  have h := complex_jordan_linear_boundary_halfplane_germ hi ho hdis hUnion hfI hfO f hLine
  have ht : Filter.Tendsto e (𝓝 (0 : 𝔻)) (𝓝 (0 : ℂ)) := by
    rw [← he0]
    exact he.continuous.tendsto 0
  rcases h with hp | hn
  · left
    filter_upwards [ht.eventually hp] with w hw
    have hwi : e w ∈ e '' I ↔ w ∈ I := he.injective.mem_set_image
    rw [hf,real_inner_comm (e w) n] at hw
    exact hwi.symm.trans hw
  · right
    filter_upwards [ht.eventually hn] with w hw
    have hwi : e w ∈ e '' I ↔ w ∈ I := he.injective.mem_set_image
    rw [hf,real_inner_comm (e w) n] at hw
    exact hwi.symm.trans hw

def DiscPolygon.finiteBoundary {n : ℕ} (P : DiscPolygon n) : Set 𝔻 :=
  ((↑) : 𝔻 → ℂ) ⁻¹' P.complexBoundary

def DiscPolygon.finiteOutside {n : ℕ} (P : DiscPolygon n) : Set 𝔻 :=
  ((↑) : 𝔻 → ℂ) ⁻¹' P.complexOutside

theorem DiscPolygon.frontier_finiteInterior {n : ℕ} (P : DiscPolygon n) :
    frontier P.interior = P.finiteBoundary := by
  change frontier (((↑) : 𝔻 → ℂ) ⁻¹' P.complexInterior) = _
  rw [← unitDisc_coe_isOpenEmbedding.isOpenMap.preimage_frontier_eq_frontier_preimage
    Complex.UnitDisc.continuous_coe,P.frontier_complexInterior]
  rfl

theorem DiscPolygon.frontier_finiteOutside {n : ℕ} (P : DiscPolygon n) :
    frontier P.finiteOutside = P.finiteBoundary := by
  change frontier (((↑) : 𝔻 → ℂ) ⁻¹' P.complexOutside) = _
  rw [← unitDisc_coe_isOpenEmbedding.isOpenMap.preimage_frontier_eq_frontier_preimage
    Complex.UnitDisc.continuous_coe,P.frontier_complexOutside]
  rfl

theorem DiscPolygon.finite_jordan_partition {n : ℕ} (P : DiscPolygon n) :
    P.interior ∪ P.finiteOutside = P.finiteBoundaryᶜ := by
  ext w
  change ((w : ℂ) ∈ P.complexInterior ∨ (w : ℂ) ∈ P.complexOutside) ↔
    (w : ℂ) ∉ P.complexBoundary
  constructor
  · rintro (hw | hw)
    · exact hw.1
    · exact connectedComponentIn_subset _ _ hw
  · intro hw
    by_cases ho : (w : ℂ) ∈ P.complexOutside
    · exact Or.inr ho
    · exact Or.inl ⟨hw,ho⟩

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.carrier_eq_tangent_line_of_zero (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (h0 : (0 : 𝔻) ∈ L.carrier) :
    ∃ n : ℂ, n ≠ 0 ∧ L.carrier = {w : 𝔻 | inner ℝ (w : ℂ) n = 0} := by
  obtain ⟨n,t,hn,he⟩ := L.closedKlein_affine_equation
  have hK0 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (0 : 𝔻) = 0 := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula 0 = 0
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
  have ht : t = 0 := by
    have hh := (he (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      0)).mp ((L.closedCarrier_mem_interior_iff 0).mpr h0)
    change inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate 0) = t at hh
    rw [hK0,inner_zero_right] at hh
    exact hh.symm
  refine ⟨n,hn,?_⟩
  ext w
  have hh := (L.closedCarrier_mem_interior_iff w).symm.trans (he
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w))
  change w ∈ L.carrier ↔ inner ℝ (w : ℂ) n = 0
  rw [ht] at hh
  obtain ⟨c,hc,hK⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_positive_smul w
  change w ∈ L.carrier ↔ inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate w) = 0 at hh
  rw [hK,real_inner_smul_right,mul_eq_zero,or_iff_right hc.ne',real_inner_comm] at hh
  exact hh

theorem closure_disc_open_halfPlane (n : ℂ) (hn : n ≠ 0) :
    closure {w : 𝔻 | 0 < inner ℝ (w : ℂ) n} = {w : 𝔻 | 0 ≤ inner ℝ (w : ℂ) n} := by
  let f : ℂ →L[ℝ] ℝ := innerSL ℝ n
  have hf : Function.Surjective f := by
    intro r
    refine ⟨(r / ‖n‖ ^ 2) • n, ?_⟩
    change inner ℝ n ((r / ‖n‖ ^ 2) • n) = r
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq]
    exact div_mul_cancel₀ r (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))
  have hOpen : {w : 𝔻 | 0 < inner ℝ (w : ℂ) n} =
      ((↑) : 𝔻 → ℂ) ⁻¹' (f ⁻¹' Ioi 0) := by
    ext w
    change 0 < inner ℝ (w : ℂ) n ↔ 0 < inner ℝ n (w : ℂ)
    rw [real_inner_comm]
  have hClosed : {w : 𝔻 | 0 ≤ inner ℝ (w : ℂ) n} =
      ((↑) : 𝔻 → ℂ) ⁻¹' (f ⁻¹' Ici 0) := by
    ext w
    change 0 ≤ inner ℝ (w : ℂ) n ↔ 0 ≤ inner ℝ n (w : ℂ)
    rw [real_inner_comm]
  rw [hOpen,hClosed,
    ← unitDisc_coe_isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      Complex.UnitDisc.continuous_coe,
    ← (f.isOpenMap hf).preimage_closure_eq_closure_preimage f.continuous,closure_Ioi]

/-- Normalization of a genuine local boundary line yields one true open Euclidean tangent half-plane. -/
theorem DiscPolygon.normalized_interior_halfPlane_germ {n : ℕ} (P : DiscPolygon n) (z : 𝔻)
    (hzB : z ∈ P.finiteBoundary) (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (hzL : z ∈ L.carrier)
    (hB : ∀ᶠ w in 𝓝 z, w ∈ P.finiteBoundary ↔ w ∈ L.carrier) :
    ∃ m : ℂ, m ≠ 0 ∧ ∀ᶠ w in 𝓝 (0 : 𝔻),
      w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z '' P.interior ↔ 0 < inner ℝ (w : ℂ) m := by
  let F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z
  have hFz : F z = 0 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self z
  have hdF : ∀ u v, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (F u) (F v) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist u v := by
    let lineGermNormalizerMetricSpace : MetricSpace 𝔻 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
    intro u v
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] using (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry z).dist_eq u v
  obtain ⟨M,hM⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathIsometry_image_discLine F hdF L
  have h0M : (0 : 𝔻) ∈ M.carrier := by
    rw [← hM]
    exact ⟨z,hzL,hFz⟩
  obtain ⟨m,hm,hLine⟩ := M.carrier_eq_tangent_line_of_zero h0M
  have hBoundary := _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_homeomorph_germ F hB
  rw [hFz,hM,hLine] at hBoundary
  have hUopen : IsOpen (F '' P.interior) := F.isOpenMap _ P.interior_isOpen
  have hOopen : IsOpen (F '' P.finiteOutside) :=
    F.isOpenMap _ (P.complexOutside_isOpen.preimage Complex.UnitDisc.continuous_coe)
  have hdis : Disjoint (F '' P.interior) (F '' P.finiteOutside) := by
    apply (Set.disjoint_left.mpr (fun w hwI hwO => hwI.2 hwO)).image
      F.injective.injOn (subset_univ _) (subset_univ _)
  have hUnion : F '' P.interior ∪ F '' P.finiteOutside = (F '' P.finiteBoundary)ᶜ := by
    rw [← image_union,P.finite_jordan_partition,image_compl_eq F.bijective]
  have h0I : (0 : 𝔻) ∈ frontier (F '' P.interior) := by
    rw [← F.image_frontier,P.frontier_finiteInterior]
    exact ⟨z,hzB,hFz⟩
  have h0O : (0 : 𝔻) ∈ frontier (F '' P.finiteOutside) := by
    rw [← F.image_frontier,P.frontier_finiteOutside]
    exact ⟨z,hzB,hFz⟩
  rcases disc_jordan_linear_boundary_halfplane_germ hUopen hOopen hdis hUnion h0I h0O m hBoundary with hp | hn
  · exact ⟨m,hm,hp⟩
  · refine ⟨-m,neg_ne_zero.mpr hm,?_⟩
    simpa only [inner_neg_right,neg_pos] using hn

/-- An actual straight boundary germ contributes exactly pi to the actual incident native mesh angle sum. -/
theorem DiscPolygon.meshAngleSumAt_of_boundary_line_germ {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (z : 𝔻) (hz : P.meshNativeVertex v =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hzB : z ∈ P.finiteBoundary) (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (hzL : z ∈ L.carrier)
    (hB : ∀ᶠ w in 𝓝 z, w ∈ P.finiteBoundary ↔ w ∈ L.carrier) :
    P.meshAngleSumAt v = Real.pi := by
  let F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z
  have hFz : F z = 0 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self z
  have hSz : F.symm 0 = z := by
    apply F.injective
    rw [F.apply_symm_apply,hFz]
  obtain ⟨m,hm,hG⟩ := P.normalized_interior_halfPlane_germ z hzB L hzL hB
  have hC := _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_closure_germ hG
  have hEq : F '' P.finiteCarrier = closure (F '' P.interior) := by
    rw [P.finiteCarrier_eq_closure,F.image_closure]
  rw [← hEq] at hC
  let H : Set 𝔻 := {w | 0 ≤ inner ℝ (w : ℂ) m}
  have hC0 : ∀ᶠ w in 𝓝 (0 : 𝔻), w ∈ F '' P.finiteCarrier ↔ w ∈ H := by
    filter_upwards [hC] with w hw
    exact hw.trans (Set.ext_iff.mp (closure_disc_open_halfPlane m hm) w)
  have hBack := _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_homeomorph_germ F.symm hC0
  have hInv : F.symm '' (F '' P.finiteCarrier) = P.finiteCarrier := by
    ext w
    constructor
    · rintro ⟨y,⟨x,hx,hxy⟩,hyw⟩
      have he : x = w := (F.symm_apply_apply x).symm.trans
        ((congrArg F.symm hxy).trans hyw)
      exact he ▸ hx
    · exact fun hw => ⟨F w,⟨w,hw,rfl⟩,F.symm_apply_apply w⟩
  rw [hSz,hInv] at hBack
  have hzH : z ∈ F.symm '' H := by
    refine ⟨0, ?_,hSz⟩
    simp [H]
  have hs := P.meshTriangle_subtendedAngle_sum_of_convex_germ z
    ((discHConvex_closed_halfPlane m).isometry_image
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_symm_isometry z)) hzH hBack
  rw [P.meshAngleSumAt_eq_incident_subtendedAngle v z hz]
  refine hs.trans ?_
  have he := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_isometry F.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_symm_isometry z) H 0
  rw [hSz] at he
  exact he.trans (discSubtendedAngle_closed_halfPlane m hm)

/-- Two distinct points determine the very same real-affine line equation as a true planar hyperplane. -/
theorem complex_lineEquation_eq_zero_iff {a b z m : ℂ} {t : ℝ}
    (hab : a ≠ b) (hm : m ≠ 0) (ha : inner ℝ m a = t) (hb : inner ℝ m b = t) :
    inner ℝ m z = t ↔ polygonComplexLineEquation a b z = 0 := by
  have hv : b-a ≠ 0 := sub_ne_zero.mpr hab.symm
  rw [polygonComplexLineEquation_apply]
  constructor
  · intro hz
    have hc : Collinear ℝ ({a,b,z} : Set ℂ) := by
      apply polygonComplex_hyperplane_collinear m a hm (by simp)
      intro x hx
      rcases hx with rfl | rfl | rfl <;> simp only [ha,hb,hz]
    have hline := hc.mem_affineSpan_of_mem_of_ne (p₁ := a) (p₂ := b) (p₃ := z)
      (by simp) (by simp) (by simp) hab
    obtain ⟨r,rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hline
    have he : ((AffineMap.lineMap a b r-a)/(b-a)) = (r : ℂ) := by
      rw [AffineMap.lineMap_apply,Complex.real_smul]
      change (((r : ℂ)*(b-a)+a)-a)/(b-a) = (r : ℂ)
      field_simp [hv]
      ring
    rw [he]
    exact Complex.ofReal_im r
  · intro hz
    let r := ((z-a)/(b-a)).re
    have he : (r : ℂ) = (z-a)/(b-a) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using hz.symm
    have hsub : z-a = r • (b-a) := by
      rw [Complex.real_smul,he]
      exact (div_mul_cancel₀ (z-a) hv).symm
    have hi : inner ℝ m (z-a) = 0 := by
      rw [hsub,real_inner_smul_right,inner_sub_right,ha,hb,sub_self,mul_zero]
    rw [inner_sub_right,ha] at hi
    linarith

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.mem_carrier_iff_complexLineEquation (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (p q : 𝕔𝔻)
    (hpq : p ≠ q) (hp : p ∈ L.closedCarrier) (hq : q ∈ L.closedCarrier) (w : 𝔻) :
    w ∈ L.carrier ↔ polygonComplexLineEquation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      p)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate w) = 0 := by
  obtain ⟨m,t,hm,he⟩ := L.closedKlein_affine_equation
  have hh := (L.closedCarrier_mem_interior_iff w).symm.trans (he
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w))
  exact hh.trans (complex_lineEquation_eq_zero_iff
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hpq)
    hm ((he p).mp hp) ((he q).mp hq))

theorem DiscPolygon.finiteBoundary_mem_iff {n : ℕ} (P : DiscPolygon n) (z : 𝔻) :
    z ∈ P.finiteBoundary ↔ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ P.boundary := by
  constructor
  · rintro ⟨p,hp,he⟩
    have hpc : p = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := Complex.UnitClosedDisc.coe_injective he
    exact hpc ▸ hp
  · exact fun hz => ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z,hz,rfl⟩

theorem DiscPolygon.klein_mem_boundary_iff {n : ℕ} (P : DiscPolygon n) (z : 𝔻) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.boundary ↔ z ∈ P.finiteBoundary := by
  rw [P.finiteBoundary_mem_iff,← _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion
    z]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image

/-- Every actual relative-interior side point contributes precisely the genuine straight angle. -/
theorem DiscPolygon.meshAngleSumAt_of_edge_interior {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (i : Fin n) (z : 𝔻) (hz : P.meshNativeVertex v =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) ∈ openSegment ℝ
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
        i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i)))) :
    P.meshAngleSumAt v = Real.pi := by
  let L := P.edgeSupport i
  have hp := (P.edgeSupport_incident i).1
  have hq := (P.edgeSupport_incident i).2
  have hpq : P.vertices i ≠ P.vertices (finRotate n i) :=
    P.vertices_injective.ne (P.next_ne_self i).symm
  have hzEdge : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ discPolygonEdge P.vertices i := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp
    rw [discPolygonEdge,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact openSegment_subset_segment ℝ _ _ he
  have hzB : z ∈ P.finiteBoundary := (P.finiteBoundary_mem_iff z).mpr
    (mem_iUnion.mpr ⟨i,hzEdge⟩)
  have hzL : z ∈ L.carrier := (L.closedCarrier_mem_interior_iff z).mp
    (P.edge_subset_support i hzEdge)
  have hK := P.klein_boundary_line_germ_edge i he
  have hNative := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_kleinCoordinate.tendsto z).eventually hK
  have hB : ∀ᶠ w in 𝓝 z, w ∈ P.finiteBoundary ↔ w ∈ L.carrier := by
    filter_upwards [hNative] with w hw
    exact (P.klein_mem_boundary_iff w).symm.trans
      (hw.trans (L.mem_carrier_iff_complexLineEquation _ _ hpq hp hq w).symm)
  exact P.meshAngleSumAt_of_boundary_line_germ v z hz hzB L hzL hB

/-- Every actual straight original corner has exactly its original angle in the true mesh sum. -/
theorem DiscPolygon.meshAngleSumAt_of_straight_corner {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (i : Fin n) (z : 𝔻) (hv : P.meshNativeVertex v =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hL : (P.cornerRayPrev i z hz).supportLine = (P.cornerRayNext i z hz).supportLine) :
    P.meshAngleSumAt v = P.angle i := by
  let R := P.cornerRayPrev i z hz
  let S := P.cornerRayNext i z hz
  let L := R.supportLine
  have hp : P.vertices ((finRotate n).symm i) ∈ L.closedCarrier := by
    have h := discRayTowardClosed_endpoint_mem z (P.vertices ((finRotate n).symm i))
      (show _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ≠ P.vertices ((finRotate n).symm i) from by
        rw [← hz]; exact fun he => P.prev_ne_self i (P.vertices_injective he).symm)
    exact closure_mono (image_mono R.subset_support) h
  have hq : P.vertices (finRotate n i) ∈ L.closedCarrier := by
    have h := discRayTowardClosed_endpoint_mem z (P.vertices (finRotate n i))
      (show _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ≠ P.vertices (finRotate n i) from by
        rw [← hz]; exact fun he => P.next_ne_self i (P.vertices_injective he).symm)
    have hh : P.vertices (finRotate n i) ∈ S.supportLine.closedCarrier :=
      closure_mono (image_mono S.subset_support) h
    change P.vertices (finRotate n i) ∈ R.supportLine.closedCarrier
    rwa [hL]
  have hpq : P.vertices ((finRotate n).symm i) ≠ P.vertices (finRotate n i) :=
    P.vertices_injective.ne (polygonSupport_prev_ne_next P.three_le i)
  have hzB : z ∈ P.finiteBoundary := (P.finiteBoundary_mem_iff z).mpr (by
    rw [← hz]
    exact mem_iUnion.mpr ⟨i,closedModelDiscHSegment_left_mem _ _⟩)
  have hK := P.klein_boundary_straight_germ i z hz hL
  rw [hz,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion] at hK
  have hNative := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_kleinCoordinate.tendsto z).eventually hK
  have hB : ∀ᶠ w in 𝓝 z, w ∈ P.finiteBoundary ↔ w ∈ L.carrier := by
    filter_upwards [hNative] with w hw
    exact (P.klein_mem_boundary_iff w).symm.trans
      (hw.trans (L.mem_carrier_iff_complexLineEquation _ _ hpq hp hq w).symm)
  rw [P.angle_eq_pi_of_same_support i z hz hL]
  exact P.meshAngleSumAt_of_boundary_line_germ v z hv hzB L (R.subset_support R.start_mem) hB

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.angleAtPoint_of_ideal (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle)
    (p : 𝕔𝔻) (hp : ‖(p : ℂ)‖ = 1) : T.angleAtPoint p = 0 := by
  by_cases ha : p = T.a
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.angleAtPoint,ite_eq_left ha]
    exact T.alpha_of_ideal (ha ▸ hp)
  by_cases hb : p = T.b
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.angleAtPoint,ite_eq_right ha,ite_eq_left
    hb]
    have hpb : ‖(T.b : ℂ)‖ = 1 := hb ▸ hp
    exact T.cycle.alpha_of_ideal hpb
  by_cases hc : p = T.c
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.angleAtPoint,ite_eq_right ha,ite_eq_right
    hb,ite_eq_left hc]
    have hpc : ‖(T.c : ℂ)‖ = 1 := hc ▸ hp
    exact T.cycle.cycle.alpha_of_ideal hpc
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.angleAtPoint,ite_eq_right
    ha,ite_eq_right hb,ite_eq_right hc]

theorem DiscPolygon.meshAngleSumAt_of_ideal {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (hv : ‖(P.meshNativeVertex v : ℂ)‖ = 1) : P.meshAngleSumAt v = 0 := by
  apply Finset.sum_eq_zero
  exact fun t _ => (P.meshTriangle t).angleAtPoint_of_ideal (P.meshNativeVertex v) hv

theorem DiscPolygon.meshAngleSumAt_of_finite_corner {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (i : Fin n) (z : 𝔻) (hv : P.meshNativeVertex v =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)
    (hz : P.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) : P.meshAngleSumAt v = P.angle i := by
  by_cases hL : (P.cornerRayPrev i z hz).supportLine = (P.cornerRayNext i z hz).supportLine
  · exact P.meshAngleSumAt_of_straight_corner v i z hv hz hL
  · exact P.meshAngleSumAt_of_proper_finite_corner v i z hv hz hL

/-- All actual original corners, finite, straight, reflex or ideal, retain their original angle in the derived mesh. -/
theorem DiscPolygon.meshAngleSumAt_of_original_corner {n : ℕ} (P : DiscPolygon n)
    (v : P.UsedMeshVertex) (i : Fin n) (hv : P.meshNativeVertex v = P.vertices i) :
    P.meshAngleSumAt v = P.angle i := by
  rcases _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDisc_interior_or_ideal (P.vertices i) with ⟨z,hz⟩ | hi
  · exact P.meshAngleSumAt_of_finite_corner v i z (hv.trans hz.symm) hz.symm
  · rw [P.meshAngleSumAt_of_ideal v (by rw [hv]; exact hi),P.angle_of_ideal i hi]

end
end LowDimensionalTopology.Geometry.Polygon
