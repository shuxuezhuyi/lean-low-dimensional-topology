module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.PolygonCompactCircleCores
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletCoreBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSideInteriors
public import LowDimensionalTopology.Geometry.Polygon.Tangential.PolygonTangentialTriangle
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped Complex.UnitDisc Pointwise RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
local instance kleinCircleSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance kleinCircleSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- The actual center-normalized Klein radius detects the true original hyperbolic metric radius. -/
theorem normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w z : P.domain.carrier) :
    ‖normalizedPolygonKleinCoordinate P w z‖ = Real.tanh (P.hyperbolicDist w z) := by
  rw [P.hyperbolicDist_eq_discPathDist]
  change ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate w) (P.finiteCoordinate z))‖ = _
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.kleinCoordinate_norm_eq_tanh_distance]
  apply congrArg Real.tanh
  let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  have hd := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry (P.finiteCoordinate
    w)).dist_eq
    (P.finiteCoordinate w) (P.finiteCoordinate z)
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self] using hd

/-- The true metric circle becomes the complete actual Euclidean circle in the center-normalized Klein chart. -/
theorem normalizedPolygonKleinCoordinate_image_metric_circle
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (R : ℝ) :
    normalizedPolygonKleinCoordinate P w '' {x | P.hyperbolicDist w x = R} =
      Metric.sphere (0 : ℂ) (Real.tanh R) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [Metric.mem_sphere,dist_zero_right,normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist,hx]
  · intro hz
    have hn : ‖z‖ = Real.tanh R := by simpa only [Metric.mem_sphere,dist_zero_right] using hz
    let k : 𝔻 := Complex.UnitDisc.mk z (hn ▸ Real.tanh_lt_one R)
    let x := (polygonPointCoordinate P w).symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinHomeomorph.symm
      k)
    have he : normalizedPolygonKleinCoordinate P w x = z := by
      change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinHomeomorph (polygonPointCoordinate P w x) : ℂ) = z
      rw [(polygonPointCoordinate P w).apply_symm_apply]
      exact congrArg (fun u : 𝔻 => (u :
        ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinHomeomorph.apply_symm_apply k)
    refine ⟨x,?_,he⟩
    apply Real.tanh_injective
    rw [←normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist,he]
    exact hn

/-- Any genuine open convex tile chart centered at the actual point gives the true finite local supporting cone. -/
theorem fuchsian_polygon_chart_local_finite_cone
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (x : P.domain.carrier) (hx : x ∈ closure D)
    (F : P.domain.carrier → ℂ) (hF : Topology.IsOpenEmbedding F) (hFx : F x = 0)
    (hconv : ∀ g : H, Convex ℝ (F '' (g • D))) :
    ∃ (s : Finset H) (n : {g // g ∈ s ∧ g ≠ 1} → ℂ) (N : Set ℂ),
      IsOpen N ∧ (0 : ℂ) ∈ N ∧
      (∀ i, n i ≠ 0) ∧
      (∀ i, ∀ a ∈ F '' D, inner ℝ (n i) a < 0) ∧
      (∀ i, ∀ a ∈ F '' (i.val • D), 0 < inner ℝ (n i) a) ∧
      (F '' closure D ∩ N = {z | ∀ i, inner ℝ (n i) z ≤ 0} ∩ N) ∧
      (∀ g : H, g ∈ s ↔ x ∈ fuchsianDomainTile P D g) := by
  classical
  let U : H → Set ℂ := fun g => F '' (g • D)
  let s := (hD.locallyFinite.incident_finite x).toFinset
  have hs (g : H) : g ∈ s ↔ x ∈ fuchsianDomainTile P D g := Set.Finite.mem_toFinset _
  have hi₀ : (1 : H) ∈ s := (hs 1).mpr (by simpa only [fuchsianDomainTile, one_smul] using hx)
  have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hDn := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hUc (g : H) : Convex ℝ (U g) := hconv g
  have hUo (g : H) : IsOpen (U g) := hF.isOpenMap _ ((Homeomorph.smul g).isOpenMap D hDo)
  have hUn (g : H) : (U g).Nonempty := (hDn.image (fun y => g • y)).image F
  have him (g : H) : F '' fuchsianDomainTile P D g ⊆ closure (U g) := by
    have he : fuchsianDomainTile P D g = closure (g • D) := (Homeomorph.smul g).image_closure D
    rw [he]
    exact image_closure_subset_closure_image hF.continuous
  have hUz (g : H) (hg : g ∈ s) : (0 : ℂ) ∈ closure (U g) :=
    him g ⟨x, (hs g).mp hg, hFx⟩
  have hUd (g : H) (_hg : g ∈ s) (hg : g ≠ 1) : Disjoint (U 1) (U g) := by
    change Disjoint (F '' (1 • D)) (F '' (g • D))
    rw [one_smul]
    exact (hD.locallyFinite.fundamental.disjoint_image hg).symm.image hF.injective.injOn
      (subset_univ _) (subset_univ _)
  obtain ⟨K, _hK, hKx, _hI, hcoverK, _havoid⟩ := hD.locallyFinite.finite_neighborhood_star x
  obtain ⟨O, hOK, hOo, hxO⟩ := mem_nhds_iff.mp hKx
  let N := F '' O
  have hN : IsOpen N := hF.isOpenMap O hOo
  have h0N : (0 : ℂ) ∈ N := ⟨x, hxO, hFx⟩
  have hcover : N ⊆ ⋃ g ∈ s, closure (U g) := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨g, hg, hgy⟩ := mem_iUnion₂.mp (hcoverK (hOK hy))
    exact mem_iUnion₂.mpr ⟨g, (hs g).mpr hg, him g (mem_image_of_mem F hgy)⟩
  obtain ⟨n, hn, _h0, he⟩ := finite_convex_cover_germ s 1 hi₀ U (fun g _ => hUc g)
    (fun g _ => hUo g) (fun g _ => hUn g) hUd hUz N hN h0N hcover
  refine ⟨s, n, N, hN, h0N, fun i => (hn i).1, ?_, (fun i => (hn i).2.2), ?_, hs⟩
  · intro i a ha
    apply (hn i).2.1 a
    simpa only [U, one_smul] using ha
  · have hU₁ : U 1 = F '' D := by simp only [U, one_smul]
    rw [hU₁] at he
    calc
      (F '' closure D) ∩ N = closure (F '' D) ∩ N := by
        apply subset_antisymm
        · exact inter_subset_inter_left N (image_closure_subset_closure_image hF.continuous)
        · rintro z ⟨hzcl, hzN⟩
          obtain ⟨y, hyO, hyz⟩ := hzN
          refine ⟨⟨y, ?_, hyz⟩, ⟨y, hyO, hyz⟩⟩
          rw [hF.isEmbedding.closure_eq_preimage_closure_image]
          change F y ∈ closure (F '' D)
          exact hyz.symm ▸ hzcl
      _ = _ := he


/-- A genuine Klein chart with arbitrary geometric center, translated to the specified local point. -/
def centeredPolygonKleinCoordinate {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w x y : P.domain.carrier) : ℂ :=
  -normalizedPolygonKleinCoordinate P w x + normalizedPolygonKleinCoordinate P w y

theorem centeredPolygonKleinCoordinate_isOpenEmbedding {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w x : P.domain.carrier) :
    Topology.IsOpenEmbedding (centeredPolygonKleinCoordinate P w x) :=
  (Homeomorph.addLeft (-normalizedPolygonKleinCoordinate P w x)).isOpenEmbedding.comp
    (normalizedPolygonKleinCoordinate_isOpenEmbedding P w)

theorem fuchsian_polygon_centered_klein_tile_convex
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w x : P.domain.carrier) (g : H) :
    Convex ℝ (centeredPolygonKleinCoordinate P w x '' (g • D)) := by
  have hc : Convex ℝ (normalizedPolygonKleinCoordinate P w '' (g • D)) := by
    have he : normalizedPolygonKleinCoordinate P w '' (g • D) =
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (polygonPointCoordinate P w '' (g • D)) := by rw [image_image]; rfl
    rw [he]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex
      _).mp (hD.pointCoordinate_smul_convex w g)
  have he : centeredPolygonKleinCoordinate P w x '' (g • D) =
      (fun z : ℂ => -normalizedPolygonKleinCoordinate P w x + z) ''
        (normalizedPolygonKleinCoordinate P w '' (g • D)) := by rw [image_image]; rfl
  rw [he]
  exact hc.translate _

/-- In any center-normalized Klein chart a genuine nonvertex polygon boundary has its
actual affine half-plane germ, and its entire actual side lies in the genuine supporting line. -/
theorem fuchsian_nonvertex_Klein_affine_halfplane_germ
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w x : P.domain.carrier)
    (hx : x ∈ frontier D) (hnv : ¬ IsFuchsianPolygonVertex P D x) :
    ∃ (n : ℂ) (N : Set ℂ), n ≠ 0 ∧ IsOpen N ∧ normalizedPolygonKleinCoordinate P w x ∈ N ∧
      (∀ z ∈ normalizedPolygonKleinCoordinate P w '' D,
        inner ℝ n z < inner ℝ n (normalizedPolygonKleinCoordinate P w x)) ∧
      (normalizedPolygonKleinCoordinate P w '' closure D ∩ N =
        {z | inner ℝ n z ≤ inner ℝ n (normalizedPolygonKleinCoordinate P w x)} ∩ N) ∧
      ∀ S : Set P.domain.carrier, IsFuchsianPolygonSide P D S → x ∈ S →
        normalizedPolygonKleinCoordinate P w '' S ⊆
          {z | inner ℝ n z = inner ℝ n (normalizedPolygonKleinCoordinate P w x)} := by
  let F := normalizedPolygonKleinCoordinate P w
  let K := centeredPolygonKleinCoordinate P w x
  have hK := centeredPolygonKleinCoordinate_isOpenEmbedding P w x
  have hKx : K x = 0 := neg_add_cancel (F x)
  obtain ⟨g,⟨hg,_hxg⟩,hunique⟩ := hD.nonvertex_incident_unique hx hnv
  obtain ⟨s,n,N,hNo,h0N,hn,hneg,hpos,heK,hincident⟩ :=
    fuchsian_polygon_chart_local_finite_cone hD x (frontier_subset_closure hx) K hK hKx
      (fuchsian_polygon_centered_klein_tile_convex hD w x)
  let i₀ : {g : H // g ∈ s ∧ g ≠ 1} := ⟨g,(hincident g).mpr _hxg,hg⟩
  have hi (i : {g : H // g ∈ s ∧ g ≠ 1}) : i = i₀ := by
    apply Subtype.ext
    exact hunique i.val ⟨i.property.2,(hincident i.val).mp i.property.1⟩
  have hQ : {z : ℂ | ∀ i, inner ℝ (n i) z ≤ 0} = {z | inner ℝ (n i₀) z ≤ 0} := by
    ext z
    constructor
    · exact fun hz => hz i₀
    · intro hz i
      rw [hi i]
      exact hz
  rw [hQ] at heK
  let N' : Set ℂ := (fun z => -F x + z) ⁻¹' N
  have hN'o : IsOpen N' := hNo.preimage (continuous_const.add continuous_id)
  have hxN' : F x ∈ N' := by change -F x + F x ∈ N; simpa only [neg_add_cancel] using h0N
  have hmem (z : ℂ) : z ∈ F '' closure D ↔ -F x + z ∈ K '' closure D := by
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,hy,rfl⟩
    · rintro ⟨y,hy,he⟩
      exact ⟨y,hy,add_left_cancel he⟩
  refine ⟨n i₀,N',hn i₀,hN'o,hxN',?_,?_,?_⟩
  · rintro z ⟨y,hy,rfl⟩
    have hh := hneg i₀ (K y) ⟨y,hy,rfl⟩
    change inner ℝ (n i₀) (-F x + F y) < 0 at hh
    rw [inner_add_right,inner_neg_right] at hh
    linarith
  · ext z
    change (z ∈ F '' closure D ∧ -F x + z ∈ N) ↔
      (inner ℝ (n i₀) z ≤ inner ℝ (n i₀) (F x) ∧ -F x + z ∈ N)
    rw [hmem]
    have hepoint := Set.ext_iff.mp heK (-F x + z)
    change (-F x + z ∈ K '' closure D ∧ -F x + z ∈ N) ↔
      (inner ℝ (n i₀) (-F x + z) ≤ 0 ∧ -F x + z ∈ N) at hepoint
    apply hepoint.trans
    apply and_congr_left'
    rw [inner_add_right,inner_neg_right]
    constructor <;> intro hh <;> linarith
  · intro S hS hxS
    obtain ⟨j,hj,heS,_hSnt⟩ := hD.side_iff.mp hS
    have hxj : x ∈ fuchsianDomainTile P D j := (heS ▸ hxS).2
    have hjg : j = g := hunique j ⟨hj,hxj⟩
    rw [hjg] at heS
    have hleft : closure (K '' D) ⊆ {z : ℂ | inner ℝ (n i₀) z ≤ 0} :=
      closure_minimal (fun z hz => (hneg i₀ z hz).le)
        (isClosed_le (continuous_const.inner continuous_id) continuous_const)
    have hright : closure (K '' (g • D)) ⊆ {z : ℂ | 0 ≤ inner ℝ (n i₀) z} :=
      closure_minimal (fun z hz => (hpos i₀ z hz).le)
        (isClosed_le continuous_const (continuous_const.inner continuous_id))
    rintro z ⟨y,hy,rfl⟩
    have hyS : y ∈ closure D ∩ fuchsianDomainTile P D g := heS ▸ hy
    have hy0 := image_closure_subset_closure_image hK.continuous (mem_image_of_mem K hyS.1)
    have hyt : y ∈ closure (g • D) := by
      change y ∈ closure ((Homeomorph.smul g) '' D)
      rw [←(Homeomorph.smul g).image_closure D]
      exact hyS.2
    have hy1 := image_closure_subset_closure_image hK.continuous (mem_image_of_mem K hyt)
    have hl : inner ℝ (n i₀) (K y) ≤ 0 := hleft hy0
    have hr : 0 ≤ inner ℝ (n i₀) (K y) := hright hy1
    have he0 := le_antisymm hl hr
    change inner ℝ (n i₀) (-F x + F y) = 0 at he0
    rw [inner_add_right,inner_neg_right] at he0
    change inner ℝ (n i₀) (F y) = inner ℝ (n i₀) (F x)
    linarith


/-- Every genuine native side support has its actual affine-line equation in any center-normalized Klein chart. -/
theorem normalizedPolygonKleinCoordinate_discLine_equation
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) :
    ∃ (m : ℂ) (t : ℝ), m ≠ 0 ∧ ∀ z : P.domain.carrier,
      P.finiteCoordinate z ∈ L.carrier ↔ inner ℝ m (normalizedPolygonKleinCoordinate P w z) = t := by
  let e := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate w)
  obtain ⟨M,hM⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_isometry_image_hLine
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry (P.finiteCoordinate w)) L
  obtain ⟨m,t,hm,hline⟩ := M.exists_klein_linear_equation
  refine ⟨m,t,hm,?_⟩
  intro z
  have he : e (P.finiteCoordinate z) ∈ M.carrier ↔ P.finiteCoordinate z ∈ L.carrier := by
    rw [←hM,e.injective.mem_set_image]
  exact he.symm.trans (hline (e (P.finiteCoordinate z)))

/-- A genuine affine support equation on a positive-length actual side holds on its entire genuine native support line. -/
theorem fuchsian_side_Klein_equation_of_support
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (w :
      P.domain.carrier)
    {D S : Set P.domain.carrier} (hS : IsFuchsianPolygonSide P D S)
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (hLS : P.finiteCoordinate '' S ⊆ L.carrier)
    (n : ℂ) (t : ℝ) (hn : n ≠ 0)
    (hSupp : normalizedPolygonKleinCoordinate P w '' S ⊆ {z | inner ℝ n z = t}) :
    ∀ z : P.domain.carrier, P.finiteCoordinate z ∈ L.carrier ↔
      inner ℝ n (normalizedPolygonKleinCoordinate P w z) = t := by
  obtain ⟨a,ha,b,hb,hab⟩ := hS.2.2
  obtain ⟨m,u,hm,hline⟩ := normalizedPolygonKleinCoordinate_discLine_equation P w L
  have hma := (hline a).mp (hLS ⟨a,ha,rfl⟩)
  have hmb := (hline b).mp (hLS ⟨b,hb,rfl⟩)
  have hna : inner ℝ n (normalizedPolygonKleinCoordinate P w a) = t := hSupp ⟨a,ha,rfl⟩
  have hnb : inner ℝ n (normalizedPolygonKleinCoordinate P w b) = t := hSupp ⟨b,hb,rfl⟩
  have hab' := (normalizedPolygonKleinCoordinate_isOpenEmbedding P w).injective.ne hab
  intro z
  exact (hline z).trans (_root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_equations_iff_of_two_points hn
    hm hab' hna hnb hma hmb).symm

/-- A genuine circle cut by a nontrivial affine line at two distinct actual points has nonzero angular derivative there. -/
theorem complex_circle_affine_angle_derivative_ne (n x y : ℂ) (hn : n ≠ 0)
    (hyx : y ≠ x) (hnorm : ‖x‖ = ‖y‖) (hline : inner ℝ n x = inner ℝ n y) :
    inner ℝ n (Complex.I*x) ≠ 0 := by
  intro hz
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx,norm_zero] at hnorm
    exact hyx (by rw [hx]; exact norm_eq_zero.mp hnorm.symm)
  have horth : inner ℝ (Complex.I*x) n = 0 := (real_inner_comm _ _).trans hz
  obtain ⟨r,hr⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_orthogonal_eq_real_smul (Complex.I*x) n
    (mul_ne_zero Complex.I_ne_zero hx0) horth
  have hr' : n = r • (-x) := by simpa only [←mul_assoc,Complex.I_mul_I,neg_one_mul] using hr
  have hr0 : r ≠ 0 := by intro he; exact hn (by rw [hr',he,zero_smul])
  have hchord : inner ℝ n (y-x) = 0 := by rw [inner_sub_right,←hline,sub_self]
  rw [hr',real_inner_smul_left,inner_neg_left] at hchord
  have he0 : inner ℝ x (y-x) = 0 := neg_eq_zero.mp ((mul_eq_zero.mp hchord).resolve_left hr0)
  exact complex_circle_radial_inner_chord_ne 0 x y (by simpa only [sub_zero] using hnorm) hyx
    (by simpa only [sub_zero] using he0)


/-- True noncritical side-circle cuts have nonzero derivative of the genuine supporting
line equation along the actual center-normalized circle. -/
theorem fuchsian_side_Klein_circle_angle_derivative_ne
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (w x :
      P.domain.carrier)
    {D S : Set P.domain.carrier} (hS : IsFuchsianPolygonSide P D S) (hxS : x ∈ S)
    (R : ℝ) (hxR : P.hyperbolicDist w x = R)
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (hLS : P.finiteCoordinate '' S ⊆ L.carrier)
    (hcrit : R ≠ L.toHalfPlane.pointDist (P.halfPlaneCoordinate w))
    (n : ℂ) (t : ℝ) (hn : n ≠ 0)
    (hSupp : normalizedPolygonKleinCoordinate P w '' S ⊆ {z | inner ℝ n z = t}) :
    inner ℝ n (Complex.I*normalizedPolygonKleinCoordinate P w x) ≠ 0 := by
  have hxL : P.halfPlaneCoordinate x ∈ L.toHalfPlane.carrier :=
    (L.mem_carrier _).mp (hLS ⟨x,hxS,rfl⟩)
  obtain ⟨y,hy,hyR,hyx⟩ := halfPlaneLine_circle_other_intersection L.toHalfPlane
    (P.halfPlaneCoordinate w) (P.halfPlaneCoordinate x) R hxL hxR hcrit
  let z := P.halfPlaneCoordinate.symm y
  have hzL : P.finiteCoordinate z ∈ L.carrier := by
    apply (L.mem_carrier _).mpr
    change P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm y) ∈ L.toHalfPlane.carrier
    rwa [P.halfPlaneCoordinate.apply_symm_apply]
  have hzR : P.hyperbolicDist w z = R := by
    change dist (P.halfPlaneCoordinate w) (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm y)) = R
    rwa [P.halfPlaneCoordinate.apply_symm_apply]
  have hne : normalizedPolygonKleinCoordinate P w z ≠ normalizedPolygonKleinCoordinate P w x := by
    intro he
    have hzx := (normalizedPolygonKleinCoordinate_isOpenEmbedding P w).injective he
    apply hyx
    calc
      y = P.halfPlaneCoordinate z := (P.halfPlaneCoordinate.apply_symm_apply y).symm
      _ = P.halfPlaneCoordinate x := congrArg P.halfPlaneCoordinate hzx
  have hEq := fuchsian_side_Klein_equation_of_support P w hS L hLS n t hn hSupp
  apply complex_circle_affine_angle_derivative_ne n _ _ hn hne
  · rw [normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist,
      normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist,hxR,hzR]
  · exact ((hEq x).mp (hLS ⟨x,hxS,rfl⟩)).trans ((hEq z).mp hzL).symm

/-- An actual point on a nontrivial affine supporting line is a genuine frontier point. -/
theorem mem_frontier_of_affine_supporting_halfplane {C : Set ℂ} {n z : ℂ} {c : ℝ}
    (hn : n ≠ 0) (hC : C ⊆ {u | inner ℝ n u ≤ c}) (hz : z ∈ C)
    (hnz : inner ℝ n z = c) : z ∈ frontier C := by
  refine ⟨subset_closure hz,?_⟩
  intro hi
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hi)
  let a := r/(2*‖n‖)
  have ha : 0 < a := div_pos hr (mul_pos (by norm_num) (norm_pos_iff.mpr hn))
  have hm : a*‖n‖ = r/2 := by dsimp [a]; field_simp
  have hd : dist (z+a • n) z < r := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ha,hm]
    linarith
  have hh : inner ℝ n (z+a • n) ≤ c := hC (interior_subset (hball hd))
  rw [inner_add_right,real_inner_smul_right,hnz,real_inner_self_eq_norm_sq] at hh
  have hp := mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hn))
  linarith

theorem interior_closed_complex_affine_halfplane (n : ℂ) (c : ℝ) (hn : n ≠ 0) :
    interior {z | inner ℝ n z ≤ c} = {z | inner ℝ n z < c} := by
  ext z
  constructor
  · intro hz
    have hmem : z ∈ {u : ℂ | inner ℝ n u ≤ c} := interior_subset hz
    have hle : inner ℝ n z ≤ c := hmem
    by_contra hlt
    have he := le_antisymm hle (le_of_not_gt hlt)
    exact (mem_frontier_of_affine_supporting_halfplane hn (subset_refl _) hmem he).2 hz
  · intro hz
    have hsub : {u : ℂ | inner ℝ n u < c} ⊆ {u | inner ℝ n u ≤ c} := by
      intro u hu
      have hh : inner ℝ n u < c := hu
      exact hh.le
    exact mem_interior.mpr ⟨{u | inner ℝ n u < c},hsub,
      isOpen_lt (continuous_const.inner continuous_id) continuous_const,hz⟩

/-- A genuine nonvertex polygon boundary in any actual center-normalized Klein chart
has the strict affine half-plane as its original polygon germ. -/
theorem fuchsian_nonvertex_Klein_open_affine_halfplane_germ
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w x : P.domain.carrier)
    (hx : x ∈ frontier D) (hnv : ¬ IsFuchsianPolygonVertex P D x) :
    ∃ (n : ℂ) (N : Set ℂ), n ≠ 0 ∧ IsOpen N ∧ normalizedPolygonKleinCoordinate P w x ∈ N ∧
      (∀ y : P.domain.carrier, normalizedPolygonKleinCoordinate P w y ∈ N →
        (y ∈ D ↔ inner ℝ n (normalizedPolygonKleinCoordinate P w y) <
          inner ℝ n (normalizedPolygonKleinCoordinate P w x))) ∧
      ∀ S : Set P.domain.carrier, IsFuchsianPolygonSide P D S → x ∈ S →
        normalizedPolygonKleinCoordinate P w '' S ⊆
          {z | inner ℝ n z = inner ℝ n (normalizedPolygonKleinCoordinate P w x)} := by
  let F := normalizedPolygonKleinCoordinate P w
  have hF := normalizedPolygonKleinCoordinate_isOpenEmbedding P w
  obtain ⟨n,N,hn,hN,hxN,_hstrict,hclosed,hside⟩ :=
    fuchsian_nonvertex_Klein_affine_halfplane_germ hD w x hx hnv
  have heInt := congrArg interior hclosed
  rw [interior_inter,interior_inter,hN.interior_eq,interior_closed_complex_affine_halfplane n _ hn] at heInt
  have hpre := hF.isOpenMap.preimage_interior_eq_interior_preimage hF.continuous (F '' closure D)
  rw [hF.injective.preimage_image,hD.interior_closure] at hpre
  refine ⟨n,N,hn,hN,hxN,?_,hside⟩
  intro y hyN
  have hp := Set.ext_iff.mp heInt (F y)
  have hpy := Set.ext_iff.mp hpre y
  change (F y ∈ interior (F '' closure D) ∧ F y ∈ N) ↔
    (inner ℝ n (F y) < inner ℝ n (F x) ∧ F y ∈ N) at hp
  have hEq : F y ∈ interior (F '' closure D) ↔ inner ℝ n (F y) < inner ℝ n (F x) := by
    constructor
    · intro hh; exact (hp.mp ⟨hh,hyN⟩).1
    · intro hh; exact (hp.mpr ⟨hh,hyN⟩).1
  exact hpy.symm.trans hEq


/-- At a genuine nonzero scalar derivative, the strict local side is determined by
its sign. This uses only the defining limit of the difference quotients. -/
theorem hasDerivAt_nonzero_local_strict_side {f : ℝ → ℝ} {d x : ℝ}
    (hf : HasDerivAt f d x) (hd : d ≠ 0) :
    ∀ᶠ y in 𝓝 x, (f y < f x ↔ d*(y-x) < 0) := by
  rcases lt_or_gt_of_ne hd with hd | hd
  · have he : ∀ᶠ y in 𝓝[≠] x, slope f x y < 0 :=
      hf.tendsto_slope.eventually (gt_mem_nhds hd)
    filter_upwards [eventually_nhdsWithin_iff.mp he] with y hy
    by_cases hyx : y = x
    · simp [hyx]
    · have hs := hy hyx
      rw [slope_def_field] at hs
      rcases lt_or_gt_of_ne hyx with hlt | hgt
      · have hv : 0 < f y-f x := by rcases div_neg_iff.mp hs with h | h <;> linarith [h.1,h.2]
        have hp := mul_pos_of_neg_of_neg hd (sub_neg.mpr hlt)
        constructor <;> intro hh <;> linarith
      · have hv : f y-f x < 0 := by rcases div_neg_iff.mp hs with h | h <;> linarith [h.1,h.2]
        have hp := mul_neg_of_neg_of_pos hd (sub_pos.mpr hgt)
        exact iff_of_true (by linarith) hp
  · have he : ∀ᶠ y in 𝓝[≠] x, 0 < slope f x y :=
      hf.tendsto_slope.eventually (lt_mem_nhds hd)
    filter_upwards [eventually_nhdsWithin_iff.mp he] with y hy
    by_cases hyx : y = x
    · simp [hyx]
    · have hs := hy hyx
      rw [slope_def_field] at hs
      rcases lt_or_gt_of_ne hyx with hlt | hgt
      · have hv : f y-f x < 0 := (div_pos_iff.mp hs).resolve_left (by intro h; linarith [h.2]) |>.1
        have hp := mul_neg_of_pos_of_neg hd (sub_neg.mpr hlt)
        exact iff_of_true (by linarith) hp
      · have hv : 0 < f y-f x := (div_pos_iff.mp hs).resolve_right (by intro h; linarith [h.2]) |>.1
        have hp := mul_pos hd (sub_pos.mpr hgt)
        constructor <;> intro hh <;> linarith

/-- The affine supporting functional has its actual angular derivative along the genuine Euclidean circle. -/
theorem hasDerivAt_circle_support_functional (n : ℂ) (r θ : ℝ) :
    HasDerivAt (fun t => inner ℝ n (circleMap 0 r t))
      (inner ℝ n (Complex.I*circleMap 0 r θ)) θ := by
  simpa only [circleMap, zero_add, inner_zero_left, add_zero, mul_comm] using
    (hasDerivAt_const θ n).inner ℝ (hasDerivAt_circleMap 0 r θ)


/-- The genuine center-normalized Klein angular parametrization, returned to the original domain. -/
def fuchsianKleinCircleParam {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R θ : ℝ) : P.domain.carrier :=
  (polygonPointCoordinate P w).symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinHomeomorph.symm
    (Complex.UnitDisc.mk (circleMap 0 (Real.tanh R) θ) (by
      rw [norm_circleMap_zero]
      exact abs_lt.mpr ⟨Real.neg_one_lt_tanh R,Real.tanh_lt_one R⟩)))

theorem fuchsianKleinCircleParam_coordinate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R θ : ℝ) :
    normalizedPolygonKleinCoordinate P w (fuchsianKleinCircleParam P w R θ) =
      circleMap 0 (Real.tanh R) θ := by
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinHomeomorph (polygonPointCoordinate P w
    ((polygonPointCoordinate P w).symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinHomeomorph.symm
      _))) : ℂ) = _
  rw [(polygonPointCoordinate P w).apply_symm_apply]
  exact congrArg (fun z : 𝔻 => (z :
    ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinHomeomorph.apply_symm_apply _)

theorem continuous_fuchsianKleinCircleParam {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ) :
    Continuous (fuchsianKleinCircleParam P w R) := by
  apply (polygonPointCoordinate P w).symm.continuous.comp
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinHomeomorph.symm.continuous.comp
  exact Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr (continuous_circleMap 0 (Real.tanh R))

theorem fuchsianKleinCircleParam_radius {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ) (hR : 0 < R) (θ : ℝ) :
    P.hyperbolicDist w (fuchsianKleinCircleParam P w R θ) = R := by
  apply Real.tanh_injective
  rw [←normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist,
    fuchsianKleinCircleParam_coordinate,norm_circleMap_zero,abs_of_pos (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangential_tanh_pos hR)]

/-- Every original point of the actual positive metric circle has a genuine Klein angular parameter. -/
theorem fuchsianKleinCircleParam_exists {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w x : P.domain.carrier) (R : ℝ)
    (hR : 0 < R) (hxR : P.hyperbolicDist w x = R) :
    ∃ θ : ℝ, fuchsianKleinCircleParam P w R θ = x := by
  have hx : normalizedPolygonKleinCoordinate P w x ∈ range (circleMap 0 (Real.tanh R)) := by
    rw [range_circleMap,abs_of_pos (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangential_tanh_pos
      hR),Metric.mem_sphere,dist_zero_right,
      normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist,hxR]
  obtain ⟨θ,hθ⟩ := hx
  refine ⟨θ,(normalizedPolygonKleinCoordinate_isOpenEmbedding P w).injective ?_⟩
  rw [fuchsianKleinCircleParam_coordinate,hθ]

/-- At every genuine nonvertex noncritical side cut, the actual original metric-circle
curve has precisely one polygon-interior direction. -/
theorem fuchsian_polygon_circle_cut_one_sided
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w x : P.domain.carrier)
    (hx : x ∈ frontier D) (hnv : ¬IsFuchsianPolygonVertex P D x)
    (R : ℝ) (hR : 0 < R) (hxR : P.hyperbolicDist w x = R)
    {S : Set P.domain.carrier} (hS : IsFuchsianPolygonSide P D S) (hxS : x ∈ S)
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (hLS : P.finiteCoordinate '' S ⊆ L.carrier)
    (hcrit : R ≠ L.toHalfPlane.pointDist (P.halfPlaneCoordinate w)) :
    ∃ θ d : ℝ, d ≠ 0 ∧ fuchsianKleinCircleParam P w R θ = x ∧
      ∀ᶠ t in 𝓝 θ, (fuchsianKleinCircleParam P w R t ∈ D ↔ d*(t-θ) < 0) := by
  obtain ⟨n,N,hn,hN,hxN,hgerm,hside⟩ :=
    fuchsian_nonvertex_Klein_open_affine_halfplane_germ hD w x hx hnv
  obtain ⟨θ,hθ⟩ := fuchsianKleinCircleParam_exists P w x R hR hxR
  have hcoord : circleMap 0 (Real.tanh R) θ = normalizedPolygonKleinCoordinate P w x := by
    rw [←fuchsianKleinCircleParam_coordinate,hθ]
  let d := inner ℝ n (Complex.I*normalizedPolygonKleinCoordinate P w x)
  have hd : d ≠ 0 := fuchsian_side_Klein_circle_angle_derivative_ne P w x hS hxS R hxR
    L hLS hcrit n _ hn (hside S hS hxS)
  have hder : HasDerivAt (fun t => inner ℝ n (circleMap 0 (Real.tanh R) t)) d θ := by
    simpa only [hcoord] using hasDerivAt_circle_support_functional n (Real.tanh R) θ
  have he := hasDerivAt_nonzero_local_strict_side hder hd
  have hnear : ∀ᶠ t in 𝓝 θ, circleMap 0 (Real.tanh R) t ∈ N :=
    (continuous_circleMap 0 (Real.tanh R)).continuousAt.eventually (hN.mem_nhds (hcoord ▸ hxN))
  refine ⟨θ,d,hd,hθ,?_⟩
  filter_upwards [he,hnear] with t ht htN
  have hh := hgerm (fuchsianKleinCircleParam P w R t)
    ((fuchsianKleinCircleParam_coordinate P w R t).symm ▸ htN)
  rw [fuchsianKleinCircleParam_coordinate,←hcoord] at hh
  exact hh.trans ht


/-- The actual one-sided angular branch places its original cut point in the closure
of genuine polygon-interior points on the same actual metric circle. -/
theorem fuchsian_circle_cut_mem_closure_of_one_sided
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    {D : Set P.domain.carrier} (w x : P.domain.carrier) (R : ℝ) (hR : 0 < R)
    (hside : ∃ θ d : ℝ, d ≠ 0 ∧ fuchsianKleinCircleParam P w R θ = x ∧
      ∀ᶠ t in 𝓝 θ, (fuchsianKleinCircleParam P w R t ∈ D ↔ d*(t-θ) < 0)) :
    x ∈ closure (D ∩ {z | P.hyperbolicDist w z = R}) := by
  obtain ⟨θ,d,hd,hθ,he⟩ := hside
  rcases lt_or_gt_of_ne hd with hd | hd
  · have hl : Tendsto (fuchsianKleinCircleParam P w R) (𝓝[>] θ) (𝓝 x) := by
      rw [←hθ]
      exact (continuous_fuchsianKleinCircleParam P w R).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto hl
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht htθ
    exact ⟨ht.mpr (mul_neg_of_neg_of_pos hd (sub_pos.mpr htθ)),fuchsianKleinCircleParam_radius P w R hR t⟩
  · have hl : Tendsto (fuchsianKleinCircleParam P w R) (𝓝[<] θ) (𝓝 x) := by
      rw [←hθ]
      exact (continuous_fuchsianKleinCircleParam P w R).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto hl
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht htθ
    exact ⟨ht.mpr (mul_neg_of_pos_of_neg hd (sub_neg.mpr htθ)),fuchsianKleinCircleParam_radius P w R hR t⟩

/-- Actual one-sidedness at all actual cuts removes the possible isolated point
pieces from the closed polygon-circle intersection. -/
theorem fuchsian_polygon_circle_closure_inter_eq
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w : P.domain.carrier) (R : ℝ) (hR : 0 < R)
    (hside : ∀ x : P.domain.carrier, x ∈ frontier D → P.hyperbolicDist w x = R →
      ∃ θ d : ℝ, d ≠ 0 ∧ fuchsianKleinCircleParam P w R θ = x ∧
        ∀ᶠ t in 𝓝 θ, (fuchsianKleinCircleParam P w R t ∈ D ↔ d*(t-θ) < 0)) :
    closure (D ∩ {x | P.hyperbolicDist w x = R}) =
      closure D ∩ {x | P.hyperbolicDist w x = R} := by
  have hc : IsClosed {x | P.hyperbolicDist w x = R} := by
    change IsClosed {x | dist (P.halfPlaneCoordinate w) (P.halfPlaneCoordinate x) = R}
    exact isClosed_eq (continuous_const.dist P.halfPlaneCoordinate.continuous) continuous_const
  refine subset_antisymm ?_ ?_
  · simpa only [hc.closure_eq] using closure_inter_subset_inter_closure D {x | P.hyperbolicDist w x = R}
  · intro x hx
    by_cases hxD : x ∈ D
    · exact subset_closure ⟨hxD,hx.2⟩
    · have hxfront : x ∈ frontier D := ⟨hx.1,by simpa only [hD.locallyFinite.fundamental.isOpen.interior_eq] using hxD⟩
      exact fuchsian_circle_cut_mem_closure_of_one_sided P w x R hR (hside x hxfront hx.2)

/-- Beyond every bound, the actual original polygon-circle intersection has genuine
one-sided branches at every cut, and its complete closed intersection is a finite
union of actual compact arcs with genuine polygon-interior open arcs. -/
theorem exists_polygon_circle_finite_transverse_arc_boundary
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w : P.domain.carrier) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ ∃ hR : 0 < R,
      (∀ x : P.domain.carrier, P.hyperbolicDist w x = R →
        ¬IsFuchsianPolygonVertex P D x ∧ IsDirichletCenter P x) ∧
      (∀ x : P.domain.carrier, x ∈ frontier D → P.hyperbolicDist w x = R →
        ∃ θ d : ℝ, d ≠ 0 ∧ fuchsianKleinCircleParam P w R θ = x ∧
          ∀ᶠ t in 𝓝 θ, (fuchsianKleinCircleParam P w R t ∈ D ↔ d*(t-θ) < 0)) ∧
      closure (D ∩ {x | P.hyperbolicDist w x = R}) = closure D ∩ {x | P.hyperbolicDist w x = R} ∧
      ∃ a : Circle, ∃ F : Set (Set P.domain.carrier), F.Finite ∧
        closure D ∩ {x | P.hyperbolicDist w x = R} = ⋃ A ∈ F, A ∧
        ∀ A ∈ F, ∃ l r : ℝ, -Real.pi ≤ l ∧ l < r ∧ r ≤ Real.pi ∧
          A = fuchsianCircleArcParam P w R hR a '' Icc l r ∧
          fuchsianCircleArcParam P w R hR a '' Ioo l r ⊆ D := by
  obtain ⟨R,hR₀,hR,havoid,hsides⟩ := exists_polygon_circle_radius_with_two_point_side_cuts P D w R₀
  have hside (x : P.domain.carrier) (hx : x ∈ frontier D) (hxR : P.hyperbolicDist w x = R) :
      ∃ θ d : ℝ, d ≠ 0 ∧ fuchsianKleinCircleParam P w R θ = x ∧
        ∀ᶠ t in 𝓝 θ, (fuchsianKleinCircleParam P w R t ∈ D ↔ d*(t-θ) < 0) := by
    obtain ⟨S,hS,hxS⟩ := hD.boundary_mem_side hx
    obtain ⟨L,hLS,hcrit,_⟩ := hsides S hS
    exact fuchsian_polygon_circle_cut_one_sided hD w x hx (havoid x hxR).1 R hR hxR hS hxS L hLS hcrit
  have he := fuchsian_polygon_circle_closure_inter_eq hD w R hR hside
  obtain ⟨a,F,hfin,hcov,hint⟩ := fuchsian_polygon_circle_closed_arc_cover hD w R hR
  exact ⟨R,hR₀,hR,havoid,hside,he,a,F,hfin,he.symm.trans hcov,hint⟩

end LowDimensionalTopology.Geometry.Fuchsian
