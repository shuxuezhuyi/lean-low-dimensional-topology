module
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.Separation
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonLocalGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonBoundarySides
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonAccidentalCycles
public import Mathlib.Tactic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped Complex.UnitDisc Pointwise
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

theorem linear_form_endpoints_eq_of_openSegment {n a b x : ℂ} {t : ℝ}
    (ha : inner ℝ n a ≤ t) (hb : inner ℝ n b ≤ t)
    (hx : x ∈ openSegment ℝ a b) (he : inner ℝ n x = t) :
    inner ℝ n a = t ∧ inner ℝ n b = t := by
  obtain ⟨r,s,hr,hs,hrs,hx⟩ := hx
  have hcomb := congrArg (fun z : ℂ => inner ℝ n z) hx
  rw [inner_add_right,real_inner_smul_right,real_inner_smul_right,he] at hcomb
  have hz : r*(t-inner ℝ n a)+s*(t-inner ℝ n b) = 0 := by
    calc
      _ = (r+s)*t-(r*inner ℝ n a+s*inner ℝ n b) := by ring
      _ = 0 := by rw [hrs,hcomb]; ring
  constructor
  · by_contra hh
    have hh' : inner ℝ n a < t := lt_of_le_of_ne ha hh
    have hp := mul_pos hr (sub_pos.mpr hh')
    have hq := mul_nonneg hs.le (sub_nonneg.mpr hb)
    linarith
  · by_contra hh
    have hh' : inner ℝ n b < t := lt_of_le_of_ne hb hh
    have hp := mul_pos hs (sub_pos.mpr hh')
    have hq := mul_nonneg hr.le (sub_nonneg.mpr ha)
    linarith

/-- A third genuine open convex tile cannot touch the relative interior of a common closed side. -/
theorem three_disjoint_open_convex_not_touch_side_interior {U V W : Set ℂ}
    (hUc : Convex ℝ U) (hUo : IsOpen U) (hUn : U.Nonempty)
    (hVc : Convex ℝ V) (hVo : IsOpen V) (hVn : V.Nonempty)
    (hWc : Convex ℝ W) (hWo : IsOpen W) (hWn : W.Nonempty)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W)
    {a b x : ℂ} (hab : a ≠ b) (ha : a ∈ closure U ∩ closure V)
    (hb : b ∈ closure U ∩ closure V) (hx : x ∈ openSegment ℝ a b)
    (hxW : x ∈ closure W) : False := by
  obtain ⟨n,t,hn,hlU,hrV⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.convex_open_disjoint_strict_separator hUc hUo hUn hVc hVo hVn hUV
  obtain ⟨m,s,hm,hlU',hrW⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.convex_open_disjoint_strict_separator hUc hUo hUn hWc hWo hWn hUW
  obtain ⟨l,r,hl,hlV,hrW'⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.convex_open_disjoint_strict_separator hVc hVo hVn hWc hWo hWn hVW
  have hna := _root_.LowDimensionalTopology.Geometry.Euclidean.inner_eq_of_common_closures hlU hrV ha
  have hnb := _root_.LowDimensionalTopology.Geometry.Euclidean.inner_eq_of_common_closures hlU hrV hb
  have hxU : x ∈ closure U := hUc.closure.segment_subset ha.1 hb.1 (openSegment_subset_segment _ _ _ hx)
  have hxV : x ∈ closure V := hVc.closure.segment_subset ha.2 hb.2 (openSegment_subset_segment _ _ _ hx)
  have hmx := _root_.LowDimensionalTopology.Geometry.Euclidean.inner_eq_of_common_closures hlU' hrW ⟨hxU,hxW⟩
  have hlx := _root_.LowDimensionalTopology.Geometry.Euclidean.inner_eq_of_common_closures hlV hrW' ⟨hxV,hxW⟩
  have hmU : closure U ⊆ {z | inner ℝ m z ≤ s} := closure_minimal
    (fun z hz => (hlU' z hz).le) (isClosed_le (continuous_const.inner continuous_id) continuous_const)
  have hlV' : closure V ⊆ {z | inner ℝ l z ≤ r} := closure_minimal
    (fun z hz => (hlV z hz).le) (isClosed_le (continuous_const.inner continuous_id) continuous_const)
  obtain ⟨hma,hmb⟩ := linear_form_endpoints_eq_of_openSegment (hmU ha.1) (hmU hb.1) hx hmx
  obtain ⟨hla,hlb⟩ := linear_form_endpoints_eq_of_openSegment (hlV' ha.2) (hlV' hb.2) hx hlx
  obtain ⟨u,hu⟩ := hUn
  obtain ⟨v,hv⟩ := hVn
  obtain ⟨w,hw⟩ := hWn
  have hcross := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_difference_cross (x := w) (u := u) hn hm hab hna hnb hma hmb
  have hcross' := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_difference_cross (x := w) (u := v) hn hl hab hna hnb hla hlb
  have hFw : t < inner ℝ n w := by
    by_contra h
    have h1 := mul_neg_of_pos_of_neg (sub_pos.mpr (hrW w hw)) (sub_neg.mpr (hlU u hu))
    have h2 := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (le_of_not_gt h))
      (sub_nonpos.mpr (hlU' u hu).le)
    linarith
  have h1 := mul_pos (sub_pos.mpr (hrW' w hw)) (sub_pos.mpr (hrV v hv))
  have h2 := mul_neg_of_pos_of_neg (sub_pos.mpr hFw) (sub_neg.mpr (hlV v hv))
  linarith

/-- A genuine interval interior, expressed by two distinct actual side points and their true geodesic segment. -/
def IsFuchsianPolygonSideInterior {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (x : P.domain.carrier) : Prop :=
  ∃ S : Set P.domain.carrier, IsFuchsianPolygonSide P D S ∧
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
      normalizedPolygonKleinCoordinate P x x ∈ openSegment ℝ
        (normalizedPolygonKleinCoordinate P x a) (normalizedPolygonKleinCoordinate P x b)

theorem IsConvexFuchsianPolygon.vertex_not_side_interior
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    {x : P.domain.carrier} (hx : IsFuchsianPolygonVertex P D x) :
    ¬ IsFuchsianPolygonSideInterior P D x := by
  rintro ⟨S,hS,a,ha,b,hb,hab,hseg⟩
  obtain ⟨g,hg,heS,_hnontriv⟩ := hD.side_iff.mp hS
  obtain ⟨j,k,hj,hk,hjk,he⟩ := hx
  have hxjk : x ∈ closure D ∩ fuchsianDomainTile P D j ∩ fuchsianDomainTile P D k :=
    he.symm ▸ mem_singleton x
  have hother : ∃ h : H, h ≠ 1 ∧ g ≠ h ∧ x ∈ fuchsianDomainTile P D h := by
    by_cases hjg : j = g
    · exact ⟨k,hk,by simpa only [← hjg] using hjk,hxjk.2⟩
    · exact ⟨j,hj,Ne.symm hjg,hxjk.1.2⟩
  obtain ⟨h,hh,hgh,hxh⟩ := hother
  let F := normalizedPolygonKleinCoordinate P x
  let U : H → Set ℂ := fun g => F '' (g • D)
  have hF := normalizedPolygonKleinCoordinate_isOpenEmbedding P x
  have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hDn := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hUc (g : H) : Convex ℝ (U g) := by
    have heU : U g = _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (polygonPointCoordinate P x '' (g • D)) := by
      rw [image_image]; rfl
    rw [heU]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp (hD.pointCoordinate_smul_convex x g)
  have hUo (g : H) : IsOpen (U g) := hF.isOpenMap _ ((Homeomorph.smul g).isOpenMap D hDo)
  have hUn (g : H) : (U g).Nonempty := (hDn.image (fun y => g • y)).image F
  have hUd (g h : H) (hne : g ≠ h) : Disjoint (U g) (U h) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨a,ha,haz⟩ ⟨b,hb,hbz⟩
    have hab' := hF.injective (haz.trans hbz.symm)
    exact hne (hD.locallyFinite.fundamental.tile_intersection_eq ha (hab'.symm ▸ hb))
  have hclosed (g : H) : F '' fuchsianDomainTile P D g ⊆ closure (U g) := by
    change F '' (g • closure D) ⊆ _
    have hgc : g • closure D = closure (g • D) := (Homeomorph.smul g).image_closure D
    rw [hgc]
    exact image_closure_subset_closure_image hF.continuous
  have ha' : F a ∈ closure (U 1) ∩ closure (U g) := by
    rw [heS] at ha
    exact ⟨hclosed 1 ⟨a,by simpa only [fuchsianDomainTile,one_smul] using ha.1,rfl⟩,
      hclosed g ⟨a,ha.2,rfl⟩⟩
  have hb' : F b ∈ closure (U 1) ∩ closure (U g) := by
    rw [heS] at hb
    exact ⟨hclosed 1 ⟨b,by simpa only [fuchsianDomainTile,one_smul] using hb.1,rfl⟩,
      hclosed g ⟨b,hb.2,rfl⟩⟩
  exact three_disjoint_open_convex_not_touch_side_interior
    (hUc 1) (hUo 1) (hUn 1) (hUc g) (hUo g) (hUn g) (hUc h) (hUo h) (hUn h)
    (hUd 1 g (Ne.symm hg)) (hUd 1 h (Ne.symm hh)) (hUd g h hgh)
    (hF.injective.ne hab) ha' hb' hseg (hclosed h ⟨x,hxh,rfl⟩)

theorem IsFuchsianPolygonSideInterior.mem_frontier
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} {x : P.domain.carrier}
    (hx : IsFuchsianPolygonSideInterior P D x) (hD : IsFuchsianFundamentalDomain P D) :
    x ∈ frontier D := by
  obtain ⟨S,hS,a,ha,b,hb,_hab,hseg⟩ := hx
  let F := normalizedPolygonKleinCoordinate P x
  have hconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (polygonPointCoordinate P x '' S) := by
    have he : polygonPointCoordinate P x '' S =
        discOriginNormalizer (P.finiteCoordinate x) '' (P.finiteCoordinate '' S) := by
      rw [image_image]; rfl
    rw [he]
    exact hS.2.1.1.isometry_image (discOriginNormalizer_isometry _)
  have hCF : Convex ℝ (F '' S) := by
    have heF : F '' S = _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (polygonPointCoordinate P x '' S) := by
      rw [image_image]; rfl
    rw [heF]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp hconv
  have hFx : F x ∈ F '' S := hCF.segment_subset ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    (openSegment_subset_segment _ _ _ hseg)
  obtain ⟨y,hy,hey⟩ := hFx
  have hyx : y = x := (normalizedPolygonKleinCoordinate_isOpenEmbedding P x).injective hey
  exact hS.subset_frontier hD (hyx ▸ hy)

theorem IsConvexFuchsianPolygon.nonvertex_local_halfplane
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    {x : P.domain.carrier} (hx : x ∈ frontier D) (hnv : ¬ IsFuchsianPolygonVertex P D x) :
    ∃ (q : ℂ) (N : Set ℂ), q ≠ 0 ∧ IsOpen N ∧ (0 : ℂ) ∈ N ∧
      ((normalizedPolygonKleinCoordinate P x '' closure D) ∩ N = {z | inner ℝ q z ≤ 0} ∩ N) := by
  classical
  obtain ⟨g,⟨hg,hxg⟩,hgUnique⟩ := hD.nonvertex_incident_unique hx hnv
  obtain ⟨s,n,N,hN,h0N,hn,_hnstrict,he,hincident⟩ := hD.local_finite_cone x (frontier_subset_closure hx)
  let i₀ : {g // g ∈ s ∧ g ≠ 1} := ⟨g,(hincident g).mpr hxg,hg⟩
  have hi (i : {g // g ∈ s ∧ g ≠ 1}) : i = i₀ := by
    apply Subtype.ext
    exact hgUnique i.val ⟨i.property.2,(hincident i.val).mp i.property.1⟩
  have hQ : {z : ℂ | ∀ i, inner ℝ (n i) z ≤ 0} = {z | inner ℝ (n i₀) z ≤ 0} := by
    ext z
    constructor
    · exact fun hz => hz i₀
    · intro hz i; rw [hi i]; exact hz
  exact ⟨n i₀,N,hn i₀,hN,h0N,by rw [hQ] at he; exact he⟩

theorem IsConvexFuchsianPolygon.nonvertex_boundary_near_unique_tile
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    {x : P.domain.carrier} (hx : x ∈ frontier D) (hnv : ¬ IsFuchsianPolygonVertex P D x) :
    ∃ (g : H) (O : Set P.domain.carrier), g ≠ 1 ∧ IsOpen O ∧ x ∈ O ∧
      ∀ y ∈ frontier D ∩ O, y ∈ closure D ∩ fuchsianDomainTile P D g := by
  obtain ⟨g,⟨hg,_hxg⟩,hunique⟩ := hD.nonvertex_incident_unique hx hnv
  obtain ⟨N,_hNc,hNx,_hf,_hcover,hd⟩ := hD.locallyFinite.finite_neighborhood_star x
  obtain ⟨O,hON,hOo,hxO⟩ := mem_nhds_iff.mp hNx
  refine ⟨g,O,hg,hOo,hxO, ?_⟩
  rintro y ⟨hyfront,hyO⟩
  obtain ⟨k,hk,hky⟩ := hD.boundary_mate hyfront
  have hyt : y ∈ fuchsianDomainTile P D k⁻¹ :=
    ⟨k • y,frontier_subset_closure hky,inv_smul_smul k y⟩
  have hxt : x ∈ fuchsianDomainTile P D k⁻¹ := by
    by_contra hnot
    exact Set.disjoint_left.mp (hd k⁻¹ hnot) (hON hyO) hyt
  have he := hunique k⁻¹ ⟨inv_ne_one.mpr hk,hxt⟩
  exact ⟨frontier_subset_closure hyfront,he ▸ hyt⟩

/-- A true nonvertex boundary point lies strictly between two actual points of one actual side. -/
theorem IsConvexFuchsianPolygon.nonvertex_is_side_interior
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    {x : P.domain.carrier} (hx : x ∈ frontier D) (hnv : ¬ IsFuchsianPolygonVertex P D x) :
    IsFuchsianPolygonSideInterior P D x := by
  obtain ⟨q,N,hq,hN,h0N,he⟩ := hD.nonvertex_local_halfplane hx hnv
  obtain ⟨g,O,hg,hOo,hxO,hnear⟩ := hD.nonvertex_boundary_near_unique_tile hx hnv
  let F := normalizedPolygonKleinCoordinate P x
  have hF := normalizedPolygonKleinCoordinate_isOpenEmbedding P x
  have h0FO : (0 : ℂ) ∈ F '' O := ⟨x,hxO,normalizedPolygonKleinCoordinate_self P x⟩
  have hW : N ∩ (F '' O) ∈ 𝓝 (0 : ℂ) := (hN.inter (hF.isOpenMap O hOo)).mem_nhds ⟨h0N,h0FO⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hW
  let v := Complex.I*q
  have hv : v ≠ 0 := mul_ne_zero Complex.I_ne_zero hq
  have hqv : inner ℝ q v = 0 := by simp [v,Complex.inner]; ring
  let t := r/(2*‖v‖)
  have ht : 0 < t := div_pos hr (mul_pos (by norm_num) (norm_pos_iff.mpr hv))
  have hnorm : ‖t • v‖ = r/2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    dsimp [t]; field_simp
  have hpa : t • v ∈ N ∩ (F '' O) := hball (by
    rw [Metric.mem_ball,dist_zero_right,hnorm]; linarith)
  have hpb : -(t • v) ∈ N ∩ (F '' O) := hball (by
    rw [Metric.mem_ball,dist_zero_right,norm_neg,hnorm]; linarith)
  obtain ⟨a,haO,haF⟩ := hpa.2
  obtain ⟨b,hbO,hbF⟩ := hpb.2
  have hline (z : ℂ) (hz : inner ℝ q z = 0) (hzN : z ∈ N) :
      z ∈ frontier (F '' closure D) := by
    have hzH : z ∈ frontier {w : ℂ | inner ℝ q w ≤ 0} :=
      mem_frontier_of_supporting_halfplane hq (subset_refl _) hz.le hz
    have hfront := frontiers_equal_on_open_germ hN he
    exact (hfront.symm ▸ (show z ∈ frontier {w : ℂ | inner ℝ q w ≤ 0} ∩ N from ⟨hzH,hzN⟩)).1
  have haFront : a ∈ frontier D := (hD.normalizedKlein_frontier_iff x a).mp (by
    change F a ∈ _
    rw [haF]
    apply hline _ _ hpa.1
    rw [real_inner_smul_right,hqv,mul_zero])
  have hbFront : b ∈ frontier D := (hD.normalizedKlein_frontier_iff x b).mp (by
    change F b ∈ _
    rw [hbF]
    apply hline _ _ hpb.1
    rw [inner_neg_right,real_inner_smul_right,hqv,mul_zero,neg_zero])
  have hneq : t • v ≠ -(t • v) := by
    intro heq
    have hre := congrArg Complex.re heq
    have him := congrArg Complex.im heq
    simp only [Complex.neg_re] at hre
    simp only [Complex.neg_im] at him
    have hz : t • v = (0 : ℂ) := Complex.ext (by simp only [Complex.zero_re]; linarith)
      (by simp only [Complex.zero_im]; linarith)
    exact (smul_ne_zero ht.ne' hv) hz
  have hab : a ≠ b := by intro heq; exact hneq (haF.symm.trans ((congrArg F heq).trans hbF))
  let S := closure D ∩ fuchsianDomainTile P D g
  have haS : a ∈ S := hnear a ⟨haFront,haO⟩
  have hbS : b ∈ S := hnear b ⟨hbFront,hbO⟩
  have hside : IsFuchsianPolygonSide P D S := hD.side_iff.mpr ⟨g,hg,rfl,a,haS,b,hbS,hab⟩
  refine ⟨S,hside,a,haS,b,hbS,hab, ?_⟩
  rw [normalizedPolygonKleinCoordinate_self]
  change (0 : ℂ) ∈ openSegment ℝ (F a) (F b)
  rw [haF,hbF]
  exact ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,by simp⟩

theorem IsConvexFuchsianPolygon.side_interior_iff_boundary_nonvertex
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (x : P.domain.carrier) :
    IsFuchsianPolygonSideInterior P D x ↔ x ∈ frontier D ∧ ¬ IsFuchsianPolygonVertex P D x := by
  constructor
  · intro hi
    exact ⟨hi.mem_frontier hD.locallyFinite.fundamental,fun hv => hD.vertex_not_side_interior hv hi⟩
  · rintro ⟨hx,hnv⟩
    exact hD.nonvertex_is_side_interior hx hnv

theorem IsConvexFuchsianPolygon.distinct_sides_meet_vertex
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S T : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hS : IsFuchsianPolygonSide P D S) (hT : IsFuchsianPolygonSide P D T) (hST : S ≠ T)
    {x : P.domain.carrier} (hx : x ∈ S ∩ T) : IsFuchsianPolygonVertex P D x := by
  obtain ⟨g,hg,rfl,_⟩ := hD.side_iff.mp hS
  obtain ⟨h,hh,rfl,_⟩ := hD.side_iff.mp hT
  have hgh : g ≠ h := by rintro rfl; exact hST rfl
  exact ⟨g,h,hg,hh,hgh,(hD.closed_tile_triple_subsingleton hg hh hgh).eq_singleton_of_mem
    ⟨hx.1,hx.2.2⟩⟩


theorem IsFuchsianFundamentalDomain.interior_point_accidental
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) {x : P.domain.carrier} (hx : x ∈ D) :
    IsAccidentalFuchsianPoint P x := by
  rw [isAccidentalFuchsianPoint_iff_no_stabilizer]
  intro g hg
  by_contra hne
  exact Set.disjoint_left.mp (hD.disjoint_image hne) ⟨x,hx,hg⟩ hx

theorem IsFuchsianFundamentalDomain.interior_cycle_eq_singleton
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) {x : P.domain.carrier} (hx : x ∈ D) :
    fuchsianPolygonCycle P D x = {x} := by
  ext y
  constructor
  · intro hy
    have he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier y =
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H P.domain.carrier x := by
      obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hy.2
      rw [← hg]
      exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul H P.domain.carrier g x
    exact hD.interior_closure_orbit_unique hx hy.1 he
  · intro hy
    have hyx := mem_singleton_iff.mp hy
    subst y
    exact ⟨subset_closure hx,MulAction.mem_orbit_self x⟩

theorem IsConvexFuchsianPolygon.interior_iff_order_one_and_cycle_length_one
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) {x : P.domain.carrier} (hx : x ∈ closure D) :
    x ∈ D ↔ fuchsianPointOrder P x = 1 ∧
      fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x) = 1 := by
  classical
  constructor
  · intro hxD
    refine ⟨(isAccidentalFuchsianPoint_iff_pointOrder_one P x).mp
      (hD.locallyFinite.fundamental.interior_point_accidental hxD), ?_⟩
    rw [hD.locallyFinite.fundamental.interior_cycle_eq_singleton hxD]
    exact Set.ncard_singleton x
  · rintro ⟨ho,hc⟩
    have hi := hD.locallyFinite.incident_card_eq_order_mul_cycleLength x
    rw [ho,hc,mul_one] at hi
    let s := (hD.locallyFinite.incident_finite x).toFinset
    have h1 : (1 : H) ∈ s := by
      apply (Set.Finite.mem_toFinset _).mpr
      change x ∈ (1 : H) • closure D
      simpa only [one_smul] using hx
    have hs : s = {1} := by
      obtain ⟨g,hg⟩ := Finset.card_eq_one.mp hi
      change s = {g} at hg
      have hg1 : g = 1 := by
        rw [hg,Finset.mem_singleton] at h1
        exact h1.symm
      simpa only [hg1] using hg
    by_contra hn
    have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
    have hfront : x ∈ frontier D := by
      rw [hDo.frontier_eq]
      exact ⟨hx,hn⟩
    obtain ⟨g,hg,hgx⟩ := hD.boundary_mate hfront
    have hxi : x ∈ fuchsianDomainTile P D g⁻¹ :=
      ⟨g • x,frontier_subset_closure hgx,inv_smul_smul g x⟩
    have hgi : g⁻¹ ∈ s := (Set.Finite.mem_toFinset _).mpr hxi
    rw [hs,Finset.mem_singleton] at hgi
    exact (inv_ne_one.mpr hg) hgi

theorem IsConvexFuchsianPolygon.accidental_singleton_iff_interior
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) {x : P.domain.carrier}
    (hx : x ∈ closure D) (ha : IsAccidentalFuchsianPoint P x) :
    fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x) = 1 ↔ x ∈ D := by
  constructor
  · intro hc
    exact (hD.interior_iff_order_one_and_cycle_length_one hx).mpr
      ⟨(isAccidentalFuchsianPoint_iff_pointOrder_one P x).mp ha,hc⟩
  · intro hxD
    exact ((hD.interior_iff_order_one_and_cycle_length_one hx).mp hxD).2

/-- Exact two-point cycles are the nonvertex boundary case; the relative-side-interior bridge is separate. -/
theorem IsConvexFuchsianPolygon.accidental_two_cycle_iff_boundary_nonvertex
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) {x : P.domain.carrier}
    (hx : x ∈ closure D) (ha : IsAccidentalFuchsianPoint P x) :
    fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x) = 2 ↔
      x ∈ frontier D ∧ ¬ IsFuchsianPolygonVertex P D x := by
  classical
  constructor
  · intro hc
    have hn : x ∉ D := by
      intro hxD
      have he := (hD.interior_iff_order_one_and_cycle_length_one hx).mp hxD |>.2
      omega
    have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
    refine ⟨by rw [hDo.frontier_eq]; exact ⟨hx,hn⟩, ?_⟩
    intro hvertex
    have he := hD.accidental_vertex_cycle_length_ge_three x hvertex ha
    omega
  · rintro ⟨hfront,hnv⟩
    obtain ⟨g,⟨hg,hxg⟩,hunique⟩ := hD.nonvertex_incident_unique hfront hnv
    let s := (hD.locallyFinite.incident_finite x).toFinset
    have hs : s = {1,g} := by
      ext h
      constructor
      · intro hh
        by_cases he : h = 1
        · simp [he]
        · have hxh : h ∈ {g : H | x ∈ fuchsianDomainTile P D g} :=
            (Set.Finite.mem_toFinset (hD.locallyFinite.incident_finite x)).mp hh
          have hhe : h = g := hunique h ⟨he,hxh⟩
          simp [hhe]
      · intro hh
        simp only [Finset.mem_insert,Finset.mem_singleton] at hh
        rcases hh with rfl | rfl
        · apply (Set.Finite.mem_toFinset _).mpr
          change x ∈ (1 : H) • closure D
          simpa only [one_smul] using hx
        · exact (Set.Finite.mem_toFinset _).mpr hxg
    have hc : s.card = 2 := by simp [hs,Ne.symm hg]
    have he := hD.locallyFinite.incident_card_eq_order_mul_cycleLength x
    rw [(isAccidentalFuchsianPoint_iff_pointOrder_one P x).mp ha,one_mul] at he
    exact he.symm.trans hc

/-- A genuine endpoint of a geodesic segment, rather than a convention imposed by polygon vertices. -/
def IsFuchsianPolygonSideEndpoint {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (S : Set P.domain.carrier) (x : P.domain.carrier) : Prop :=
  x ∈ S ∧ ¬ ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
    normalizedPolygonKleinCoordinate P x x ∈ openSegment ℝ
      (normalizedPolygonKleinCoordinate P x a) (normalizedPolygonKleinCoordinate P x b)

theorem IsConvexFuchsianPolygon.vertex_side_endpoint
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    {x : P.domain.carrier} (hx : IsFuchsianPolygonVertex P D x)
    (hS : IsFuchsianPolygonSide P D S) (hxS : x ∈ S) :
    IsFuchsianPolygonSideEndpoint P S x := by
  refine ⟨hxS, ?_⟩
  rintro ⟨a,ha,b,hb,hab,hseg⟩
  exact hD.vertex_not_side_interior hx ⟨S,hS,a,ha,b,hb,hab,hseg⟩

theorem IsConvexFuchsianPolygon.distinct_sides_meet_common_endpoint
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S T : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hS : IsFuchsianPolygonSide P D S) (hT : IsFuchsianPolygonSide P D T) (hST : S ≠ T)
    {x : P.domain.carrier} (hx : x ∈ S ∩ T) :
    IsFuchsianPolygonVertex P D x ∧ IsFuchsianPolygonSideEndpoint P S x ∧
      IsFuchsianPolygonSideEndpoint P T x := by
  have hv := hD.distinct_sides_meet_vertex hS hT hST hx
  exact ⟨hv,hD.vertex_side_endpoint hv hS hx.1,hD.vertex_side_endpoint hv hT hx.2⟩

/-- The source's two-point accidental cycles consist precisely of genuine side-interior points. -/
theorem IsConvexFuchsianPolygon.accidental_two_cycle_iff_side_interior
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) {x : P.domain.carrier}
    (hx : x ∈ closure D) (ha : IsAccidentalFuchsianPoint P x) :
    fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x) = 2 ↔
      IsFuchsianPolygonSideInterior P D x :=
  (hD.accidental_two_cycle_iff_boundary_nonvertex hx ha).trans
    (hD.side_interior_iff_boundary_nonvertex x).symm

end LowDimensionalTopology.Geometry.Fuchsian
